"""Verify the lattice store and put it into a Zenodo DRAFT deposition. Never publishes.

The data release --

    "Entroptics lattice gauge-theory action-density ensembles (U(1), SU(2), SU(3))"

-- is about 24.7 GB of tarballs on an operator's local disk. It is not in this repository and never
will be, so the thing that uploads it has to run where the disk is. This module is the one
implementation of that procedure: an operator runs it directly, and
``.github/workflows/publish.yml`` shells out to it, so both paths execute the same code.

What it enforces, in order:

  1. every tarball's SHA-256 matches ``SHA256SUMS.tarballs`` as shipped;
  2. the tarballs between them contain exactly the shards ``SHA256SUMS`` lists -- a tarball can
     verify as a blob and still be missing files inside it;
  3. the store's own README, licence, generation notes, manifest and reader are present and go up
     WITH the data. They are in neither checksum list and inside none of the tarballs, so staging
     the tarballs alone published seven opaque 1-11 GB blobs that nobody could read or cite;
  4. the staged total fits the record quota, stated rather than assumed.

Publishing is deliberately not here. Uploading is reversible -- a draft can be discarded, a file
replaced -- and minting a DOI is not: it fixes the public record date and the metadata the world
cites. That step is a human in the Zenodo UI, which is also where the record's access conditions
and the not-yet-existing paper identifier get their final read.

Usage::

    python research/code/zenodo_deposit.py verify
    python research/code/zenodo_deposit.py upload --api sandbox
    python research/code/zenodo_deposit.py upload --api production --deposition 1234567

``upload`` re-checks the manifest it was given, skips any file the deposition already holds with a
matching checksum -- so an interrupted 24.7 GB run is resumed by re-running it -- and confirms
Zenodo's own checksum for every file it sends before reporting success.

The API token is read from the ``ZENODO_TOKEN`` environment variable, else from ``ZENODO_TOKEN`` in
the git-ignored ``research.local.env`` beside ``CONFIGS``. It is never logged and never written to
the manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import sys
import tarfile
import time
import urllib.error
import urllib.request

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import store_path                                                          # noqa: E402

#: Zenodo's default per-record allowance. Overridable because it is a quota, not a law: Zenodo will
#: raise it on request, and a raised quota that the script still refuses on is a false refusal.
QUOTA_BYTES = int(os.environ.get("ZENODO_RECORD_QUOTA_BYTES", "53687091200"))       # 50 GB

#: The two halves, used only if a single record is refused for size. Each half is a whole record and
#: therefore carries the metadata below in full.
REDUCED = {"configs_betasweep.tar", "configs_densebeta.tar", "configs_ladder.tar",
           "configs_paper83.tar", "configs_phase1.tar"}
LINKS = {"configs_links_su2.tar", "configs_links_su2_lscan.tar"}

#: The store's own release metadata and reader -- in no checksum list, inside no tarball, and the
#: difference between a citable dataset and 24.7 GB of undocumented binary.
COMPANIONS = ["README.md", "GENERATION.md", "CITATION.cff", "LICENSE.txt", ".zenodo.json",
              "SHA256SUMS", "SHA256SUMS.tarballs", "manifest.csv", "read_example.py",
              "make_manifest.py",
              # GENERATION.md tells a reader this file is "in this directory" and rests the
              # release's central claim on it -- that every ensemble is an equilibrium sample,
              # verified by measurement. Without it the record ships that claim with its evidence
              # missing, and the sentence pointing at it dangles.
              "store_dat_thermalisation.csv"]

SANDBOX = "https://sandbox.zenodo.org/api"
PRODUCTION = "https://zenodo.org/api"


# ------------------------------------------------------------------------------------------------
# reading the store
# ------------------------------------------------------------------------------------------------

def read_sums(p: pathlib.Path) -> dict[str, str]:
    """``{filename: sha256}`` from a ``sha256sum``-format list."""
    out = {}
    for line in p.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        digest, _, name = line.partition("  ")
        out[name.strip()] = digest.strip().lower()
    return out


def digest(p: pathlib.Path, algo: str = "sha256") -> str:
    """Streaming digest, 16 MiB at a time -- these files do not fit in memory."""
    h = hashlib.new(algo)
    with p.open("rb") as fh:
        for chunk in iter(lambda: fh.read(16 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def store() -> pathlib.Path:
    """The store root, by the same rule every reader in ``research/`` uses."""
    return pathlib.Path(store_path.store_root())


def load_manifest(path: pathlib.Path, root: pathlib.Path) -> list[dict]:
    """A staged set from an earlier ``verify``, re-checked cheaply against the disk.

    Hashing 24.7 GB twice -- once to verify, then again minutes later immediately before sending
    the same bytes -- costs the better part of an hour and buys nothing that the upload's own
    per-file checksum confirmation does not already give: every file's md5 is compared against
    Zenodo's response before the run is called a success. So this is opt-in, and it still refuses
    on any file whose size has moved since the manifest was written.
    """
    try:
        staged = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        raise SystemExit(f"{path} is not there. Run `verify` first, or drop --use-manifest to "
                         f"verify as part of this run.")
    # Read before any refresh below rewrites the file, or the age reported is the age of this run.
    age = (time.time() - path.stat().st_mtime) / 60
    drift, refreshed = [], []
    for e in staged:
        p = root / e["name"]
        if not p.exists():
            drift.append(f"{e['name']}: in the manifest, absent on disk")
            continue
        size = p.stat().st_size
        if size == e["bytes"]:
            continue
        if e["kind"] == "tarball":
            # A tarball's SHA-256 is in SHA256SUMS.tarballs. If the bytes moved, the shipped
            # checksum list no longer describes this store, and no amount of re-hashing here makes
            # that safe to publish -- the release itself has to be rebuilt.
            drift.append(f"{e['name']}: {size:,} B on disk, {e['bytes']:,} B in the manifest -- a "
                         f"tarball changed, so SHA256SUMS.tarballs no longer describes the store")
            continue
        # Metadata is in no checksum list, and is EXPECTED to change right up to deposit time and
        # again afterwards, when the minted DOI is written back into CITATION.cff and .zenodo.json.
        # Re-hash the few kilobytes that moved rather than the 24.7 GB that did not.
        e["bytes"], e["sha256"] = size, digest(p)
        refreshed.append(e["name"])
    if drift:
        print("REFUSING: the store has moved since the manifest was written:\n")
        for d in drift:
            print(f"  * {d}")
        raise SystemExit(1)
    total = sum(e["bytes"] for e in staged)
    n_tar = sum(1 for e in staged if e["kind"] == "tarball")
    print(f"store: {root}")
    print(f"reusing {path}, written {age:.0f} min ago: {len(staged)} file(s), "
          f"{total:,} B ({total / 1e9:.2f} GB)")
    if refreshed:
        path.write_text(json.dumps(staged, indent=2), encoding="utf-8")
        print(f"  {len(refreshed)} metadata file(s) changed since and were re-hashed: "
              f"{', '.join(refreshed)}")
    print(f"  all {n_tar} tarball(s) unchanged in size, so their SHA-256 gate from that run still "
          f"stands; Zenodo's own checksum is confirmed per file as each upload completes\n")
    return staged


# ------------------------------------------------------------------------------------------------
# verify
# ------------------------------------------------------------------------------------------------

def verify(root: pathlib.Path, split: str) -> list[dict]:
    """The staged set, or raise. Prints what it checked, because a silent pass proves nothing."""
    tar_list = read_sums(root / "SHA256SUMS.tarballs")
    shard_list = read_sums(root / "SHA256SUMS")
    print(f"store: {root}")
    print(f"checksum lists: {len(tar_list)} tarballs, {len(shard_list)} shards\n", flush=True)

    if split == "single":
        want = set(tar_list)
    elif split == "reduced":
        want = REDUCED
    else:
        want = LINKS

    missing_from_list = want - set(tar_list)
    if missing_from_list:
        raise SystemExit(f"REFUSING: {sorted(missing_from_list)} are staged but not in "
                         f"SHA256SUMS.tarballs -- the checksum list is not describing this release")
    if split != "single" and (REDUCED | LINKS) != set(tar_list):
        raise SystemExit(f"REFUSING: the split partition {sorted(REDUCED | LINKS)} does not cover "
                         f"SHA256SUMS.tarballs {sorted(tar_list)}; publishing it would drop data "
                         f"while the record metadata still claims the whole release")

    failures: list[str] = []
    staged: list[dict] = []
    total = 0

    for name in sorted(want):
        p = root / name
        if not p.exists():
            failures.append(f"{name}: listed in SHA256SUMS.tarballs, absent on disk")
            continue
        got = digest(p)
        if got != tar_list[name]:
            failures.append(f"{name}: sha256 {got} != listed {tar_list[name]}")
            continue
        size = p.stat().st_size
        total += size
        staged.append({"name": name, "sha256": got, "bytes": size, "kind": "tarball"})
        print(f"  OK  {name}  {size:,} B", flush=True)

    for name in COMPANIONS:
        p = root / name
        if not p.exists():
            failures.append(f"{name}: release metadata missing from the store, so the record would "
                            f"publish without it")
            continue
        size = p.stat().st_size
        total += size
        staged.append({"name": name, "sha256": digest(p), "bytes": size, "kind": "metadata"})
        print(f"  OK  {name}  {size:,} B  (metadata)", flush=True)

    # Members, not just blobs: the per-shard list must be exactly what the tarballs hold.
    seen: set[str] = set()
    for entry in [e for e in staged if e["kind"] == "tarball"]:
        with tarfile.open(root / entry["name"]) as tf:
            seen |= {m.name.replace("\\", "/").lstrip("./") for m in tf.getmembers() if m.isfile()}
    if split == "single":
        absent = set(shard_list) - seen
        extra = seen - set(shard_list)
        if absent:
            failures.append(f"{len(absent)} shard(s) in SHA256SUMS are in no tarball, "
                            f"e.g. {sorted(absent)[:3]}")
        if extra:
            failures.append(f"{len(extra)} file(s) inside the tarballs are in no checksum list, "
                            f"e.g. {sorted(extra)[:3]}")

    if failures:
        print("\nREFUSING TO PUBLISH -- verification failed:\n")
        for f in failures:
            print(f"  * {f}")
        raise SystemExit(1)

    n_tar = sum(1 for e in staged if e["kind"] == "tarball")
    n_meta = len(staged) - n_tar
    print(f"\nstaged {len(staged)} file(s) -- {n_tar} tarball(s) + {n_meta} metadata -- "
          f"{total:,} B ({total / 1e9:.2f} GB)")
    print(f"record quota {QUOTA_BYTES:,} B ({QUOTA_BYTES / 1e9:.2f} GB); "
          f"headroom {QUOTA_BYTES - total:,} B ({(QUOTA_BYTES - total) / 1e9:.2f} GB)")
    largest = max(staged, key=lambda e: e["bytes"])
    print(f"largest single file: {largest['name']} {largest['bytes']:,} B "
          f"({largest['bytes'] / 1e9:.2f} GB) -- REST API upload only, not the browser")
    if total > QUOTA_BYTES:
        raise SystemExit("REFUSING: the staged set exceeds the record quota. Request an increase, "
                         "or re-run with --split reduced / --split links. Do NOT drop files to fit.")
    print(f"\nverified: every one of the {n_tar} tarball(s) matches the shipped checksum list, and "
          f"the {n_meta} metadata file(s) the record needs to be readable are present")
    return staged


# ------------------------------------------------------------------------------------------------
# upload
# ------------------------------------------------------------------------------------------------

def token() -> str:
    """The API token, from the environment or the git-ignored local config. Never printed."""
    value = os.environ.get("ZENODO_TOKEN", "").strip() or store_path.local_value("ZENODO_TOKEN")
    if not value:
        raise SystemExit(
            "No Zenodo API token.\n\n"
            "Create one at https://zenodo.org/account/settings/applications/tokens/new/ with the\n"
            "scopes deposit:write and deposit:actions, then either\n\n"
            f"  1. add it to {store_path.local_config_path()} (git-ignored, beside CONFIGS):\n"
            "         ZENODO_TOKEN=...\n\n"
            "  2. or set it for one run:\n"
            "         ZENODO_TOKEN=... python research/code/zenodo_deposit.py upload\n\n"
            "Sandbox and production are separate sites with separate tokens -- a sandbox token\n"
            "returns 401 against the production API and vice versa.")
    return value


class _Progress:
    """A file wrapper that reports as it is read.

    ``urllib`` streams the file object straight to the socket, so without this an 11 GB PUT is a
    silent hour with no way to tell a slow upload from a hung one.
    """

    def __init__(self, fh, total: int, label: str):
        self.fh, self.total, self.label = fh, total, label
        self.sent = 0
        self.started = time.monotonic()
        self.last = 0.0

    def read(self, size: int = -1) -> bytes:
        chunk = self.fh.read(size)
        self.sent += len(chunk)
        now = time.monotonic()
        if chunk and (now - self.last > 5 or self.sent == self.total):
            self.last = now
            elapsed = max(now - self.started, 1e-9)
            pct = 100 * self.sent / self.total if self.total else 100.0
            rate = self.sent / elapsed / 1e6
            eta = (self.total - self.sent) / (self.sent / elapsed) if self.sent else 0
            print(f"    {self.label}: {pct:5.1f}%  {self.sent / 1e9:.2f}/{self.total / 1e9:.2f} GB  "
                  f"{rate:.1f} MB/s  ETA {eta / 60:.0f} min", flush=True)
        return chunk

    def __len__(self) -> int:
        return self.total


def call(api_token: str, method: str, url: str, data=None, headers=None, length: int | None = None):
    """One authenticated request. Returns parsed JSON, or {} for an empty body."""
    hdrs = {"Authorization": f"Bearer {api_token}", **(headers or {})}
    if length is not None:
        hdrs["Content-Length"] = str(length)
    req = urllib.request.Request(url, data=data, method=method, headers=hdrs)
    try:
        with urllib.request.urlopen(req) as r:
            body = r.read()
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")[:2000]
        hint = ""
        if exc.code in (401, 403):
            site = "sandbox.zenodo.org" if "sandbox" in url else "zenodo.org"
            other = "zenodo.org" if "sandbox" in url else "sandbox.zenodo.org"
            hint = (f"\n\nThis is almost always the token, and almost always one of two things:\n\n"
                    f"  * IT IS FROM THE OTHER SITE. {site} and {other} are separate services with\n"
                    f"    separate accounts, separate logins and separate tokens. A token minted on\n"
                    f"    {other} is not a weaker credential here, it is not a credential at all.\n"
                    f"    This request went to {site}, so the token has to have been created at\n"
                    f"        https://{site}/account/settings/applications/tokens/new/\n"
                    f"    on an account registered at {site}.\n\n"
                    f"  * IT IS MISSING A SCOPE. Creating and writing a deposition needs\n"
                    f"    deposit:write; publishing needs deposit:actions. Scopes are fixed when\n"
                    f"    the token is created -- check the token, and make a new one if it is\n"
                    f"    short. The old one cannot be widened.\n\n"
                    f"Nothing was uploaded and no deposition was created.")
        raise SystemExit(f"Zenodo {method} {url} -> HTTP {exc.code}\n{detail}{hint}") from None
    return json.loads(body) if body else {}


def upload(staged: list[dict], root: pathlib.Path, api: str, deposition_id: str | None,
           set_metadata: bool, metadata_only: bool = False) -> None:
    """Put the staged files into a draft. Skips what is already there and verified.

    ``metadata_only`` creates the draft and sets its metadata but uploads nothing. That is the
    rehearsal worth doing: almost everything that can go wrong before the bytes move is a metadata
    or credential problem -- a licence identifier Zenodo does not recognise, ``restricted`` access
    without ``access_conditions``, a malformed related identifier, a token with the wrong scope or
    from the wrong site -- and none of that needs 24.7 GB to find out about. Sending the whole
    store to the sandbox to learn the licence string is wrong costs hours and proves little.
    """
    api_token = token()
    api = api.rstrip("/")
    print(f"\nZenodo API: {api}")
    if "sandbox" in api:
        print("(SANDBOX -- nothing here is a real DOI; use --api production for the real deposit)")

    if deposition_id:
        dep = call(api_token, "GET", f"{api}/deposit/depositions/{deposition_id}")
    else:
        dep = call(api_token, "POST", f"{api}/deposit/depositions", data=b"{}",
                   headers={"Content-Type": "application/json"})
        print(f"created draft deposition {dep['id']}")
        print(f"  re-run with --deposition {dep['id']} to resume into this same draft")

    if dep.get("submitted") or dep.get("state") == "done":
        raise SystemExit(f"deposition {dep['id']} is already published. Publishing is irreversible "
                         f"and is not undone from here; create a new version in the Zenodo UI.")

    if set_metadata:
        meta = json.loads((root / ".zenodo.json").read_text(encoding="utf-8"))
        call(api_token, "PUT", f"{api}/deposit/depositions/{dep['id']}",
             data=json.dumps({"metadata": meta}).encode("utf-8"),
             headers={"Content-Type": "application/json"})
        print(f"metadata set from {root / '.zenodo.json'}")

    if metadata_only:
        print(f"\nmetadata-only: draft {dep['id']} exists and Zenodo accepted its metadata. "
              f"NOTHING was uploaded.")
        print(f"  {api.replace('/api', '')}/deposit/{dep['id']}")
        print(f"\nThe credentials and the record metadata are good. To send the data:")
        print(f"    python research/code/zenodo_deposit.py upload --api "
              f"{'sandbox' if 'sandbox' in api else 'production'} --deposition {dep['id']} "
              f"--use-manifest")
        print("(drop --use-manifest to re-hash the store first; the manifest's SHA-256 gate has "
              "already run)")
        return

    bucket = dep["links"]["bucket"]
    already = {f.get("filename") or f.get("key"): str(f.get("checksum", "")).split(":")[-1]
               for f in dep.get("files", [])}

    # Only re-hash what the draft claims to hold already: on a fresh run that is nothing, and
    # hashing 24.7 GB to decide there is nothing to skip would double the cost of every run.
    todo = []
    for e in staged:
        remote = already.get(e["name"])
        if remote is None or remote != digest(root / e["name"], "md5"):
            todo.append(e)
    skipped = len(staged) - len(todo)
    if skipped:
        print(f"{skipped} file(s) already in the draft with a matching checksum -- not re-uploading")

    for i, entry in enumerate(todo, 1):
        src = root / entry["name"]
        want_md5 = digest(src, "md5")
        print(f"\n[{i}/{len(todo)}] {entry['name']}  {entry['bytes']:,} B", flush=True)
        for attempt in (1, 2, 3):
            try:
                with src.open("rb") as fh:
                    got = call(api_token, "PUT", f"{bucket}/{entry['name']}",
                               data=_Progress(fh, entry["bytes"], entry["name"]),
                               headers={"Content-Type": "application/octet-stream"},
                               length=entry["bytes"])
                break
            except (urllib.error.URLError, OSError) as exc:
                if attempt == 3:
                    raise SystemExit(f"{entry['name']}: upload failed after 3 attempts: {exc}")
                print(f"    attempt {attempt} failed ({exc}); retrying", flush=True)
                time.sleep(5 * attempt)
        remote = str(got.get("checksum", "")).split(":")[-1]
        if remote != want_md5:
            raise SystemExit(f"REFUSING: {entry['name']} stored as {remote}, local md5 {want_md5} "
                             f"-- the archived copy is not the verified file")
        print(f"    confirmed md5 {remote}")

    print(f"\nDRAFT deposition {dep['id']} now holds {len(staged)} verified file(s).")
    print(f"  {api.replace('/api', '')}/deposit/{dep['id']}")
    print("\nNOT PUBLISHED. Review the draft, confirm the metadata, and publish by hand. Then write")
    print("the minted DOI into the store's CITATION.cff and .zenodo.json, and into this repository's")
    print(".zenodo.json related_identifiers as a resource_type 'dataset' entry -- the readiness gate")
    print("fails until you do.")


# ------------------------------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("command", choices=["verify", "upload"])
    ap.add_argument("--split", choices=["single", "reduced", "links"], default="single",
                    help="single = one record, everything. reduced/links = one half each, only if "
                         "a single record is refused for size.")
    ap.add_argument("--api", choices=["sandbox", "production"], default="sandbox",
                    help="default sandbox: rehearse before minting anything permanent")
    ap.add_argument("--deposition", default=os.environ.get("ZENODO_DEPOSITION_ID") or None,
                    help="resume into an existing draft instead of creating one")
    ap.add_argument("--manifest", default="staged.json",
                    help="where verify writes, and upload reads, the staged set")
    ap.add_argument("--set-metadata", action="store_true",
                    help="also PUT the store's .zenodo.json as the draft's metadata")
    ap.add_argument("--metadata-only", action="store_true",
                    help="create the draft and set its metadata, upload nothing -- the cheap "
                         "rehearsal for credentials and metadata schema")
    ap.add_argument("--use-manifest", action="store_true",
                    help="trust an earlier verify's staged.json instead of re-hashing the store; "
                         "sizes are still re-checked against disk")
    args = ap.parse_args()

    root = store()

    if args.command == "upload" and args.metadata_only:
        # Nothing is staged, so there is nothing to check. Hashing 24.7 GB to create an empty draft
        # is exactly the cost this rehearsal exists to avoid.
        staged = []
        print(f"store: {root}")
        print("--metadata-only: no files are staged, so the checksum gate is not run\n")
    elif args.command == "upload" and args.use_manifest:
        staged = load_manifest(pathlib.Path(args.manifest), root)
    else:
        staged = verify(root, args.split)
        pathlib.Path(args.manifest).write_text(json.dumps(staged, indent=2), encoding="utf-8")
        print(f"\nstaged set written to {args.manifest}")

    if args.command == "upload":
        # A draft with no metadata is not a rehearsal of anything, so the flag implies it.
        upload(staged, root, SANDBOX if args.api == "sandbox" else PRODUCTION,
               args.deposition, args.set_metadata or args.metadata_only, args.metadata_only)


if __name__ == "__main__":
    main()
