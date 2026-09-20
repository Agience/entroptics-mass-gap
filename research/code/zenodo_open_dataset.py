"""Flip the published lattice dataset record from `restricted` to `open`, and fix its source.

WHY THIS EXISTS. v0.2.0 of the action-density ensembles (record 22850110, DOI
10.5281/zenodo.22850110) was published carrying `access_right: "restricted"`, so the public record
serves ZERO of its 25 files while the paper, CITATION.cff and the repository's .zenodo.json all cite
it. v0.1.0 (22650079) is `open` with its 19 files public, so v0.2.0 was a REGRESSION -- and the
record ships CC-BY-4.0, which grants redistribution over files the record refuses to hand out. The
two cannot both be intended.

The restriction came from the store's own `.zenodo.json`, which the uploader pushes with
`--set-metadata`. Fixing the record without fixing that file would put it straight back on the next
version, so this changes the source first and the record second.

Authorised by John, 2026-09-19, in answer to a direct question about this record.

WHAT THIS DOES NOT DO. It does not touch the files, the DOI, the version or any other field, and it
publishes no new version -- the cited DOI keeps resolving to the same 25 files. It edits one
metadata key on an already-published record and submits that edit.
"""
import io
import json
import os
import sys
import urllib.error
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import store_path                                     # noqa: E402  (needs the path above first)

#: DERIVED: the version DOI minted for v0.2.0 on 2026-09-19; the record this repository cites.
DEPOSITION = 22850110
API = "https://zenodo.org/api/deposit/depositions/%d" % DEPOSITION


def token() -> str:
    """The Zenodo token, from the git-ignored local env file. Never named in source."""
    p = os.path.join(os.path.dirname(REPO), "research.local.env")
    if not os.path.exists(p):
        p = os.path.join(REPO, "..", "research.local.env")
    for line in io.open(p, encoding="utf-8"):
        if line.startswith("ZENODO_TOKEN="):
            return line.split("=", 1)[1].strip()
    raise SystemExit("no ZENODO_TOKEN in research.local.env")


def call(url, tok, method="GET", body=None):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method, headers={
        "Authorization": "Bearer " + tok, "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req) as fh:
            raw = fh.read()
        return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as e:
        raise SystemExit("%s %s -> %d\n%s" % (method, url, e.code, e.read().decode()[:1200]))


def main():
    tok = token()

    # 1. The SOURCE, so the next version does not reintroduce it.
    src = os.path.join(store_path.store_root(), ".zenodo.json")
    meta = json.load(io.open(src, encoding="utf-8"))
    if meta.get("access_right") != "open":
        was = meta.get("access_right")
        meta["access_right"] = "open"
        io.open(src, "w", encoding="utf-8").write(json.dumps(meta, indent=2, ensure_ascii=False) + "\n")
        print("store .zenodo.json: access_right %r -> 'open'" % was)
    else:
        print("store .zenodo.json: already open")

    # 2. The RECORD. Read what is live before writing, and change exactly one key.
    dep = call(API, tok)
    live = dict(dep["metadata"])
    print("record %d: state=%s submitted=%s access_right=%s files=%d"
          % (DEPOSITION, dep.get("state"), dep.get("submitted"),
             live.get("access_right"), len(dep.get("files", []))))
    if live.get("access_right") == "open" and dep.get("state") == "done":
        print("already open and published; nothing to do")
        return 0

    if dep.get("state") == "done":
        # No edit draft open yet -- open one.
        call(API + "/actions/edit", tok, method="POST")
        print("opened an edit draft")
        live = dict(call(API, tok)["metadata"])

    live["access_right"] = "open"
    call(API, tok, method="PUT", body={"metadata": live})
    print("metadata updated: access_right -> open")

    pub = call(API + "/actions/publish", tok, method="POST")
    print("PUBLISHED  state=%s  doi=%s" % (pub.get("state"), pub.get("doi")))

    # 3. Verify against the PUBLIC record, not against our own request.
    with urllib.request.urlopen("https://zenodo.org/api/records/%d" % DEPOSITION) as fh:
        rec = json.load(fh)
    n = len(rec.get("files", []))
    print("public record: access_right=%s  files served=%d"
          % (rec.get("metadata", {}).get("access_right"), n))
    # DERIVED: the file count is the deposit's own, read back from the API rather than written here,
    # so this checks the PUBLIC record against what the deposit holds instead of against a numeral.
    assert rec.get("metadata", {}).get("access_right") == "open", "the public record is still closed"
    held = len(dep.get("files", []))
    assert n == held, "public record serves %d of the deposit's %d files" % (n, held)
    print("OK: all %d files are publicly downloadable at https://doi.org/%s" % (n, rec.get("doi")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
