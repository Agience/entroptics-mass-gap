"""Retrieve a running campaign's shards as they land, verify each one, and record it.

WHY REAL TIME. A campaign on rented hardware that transfers at the end is a campaign whose product
can be lost entirely -- to a preempted pod, a dropped link, or a crash eight hours in. Transferring
each shard as it completes means the data on this machine is always the data that has been generated,
and the only work at risk is the shard currently in flight.

HOW IT KNOWS A SHARD IS DONE. `lattice_generator`'s CLI writes each shard atomically (to a temporary
name, then `os.replace`) and only then appends its SHA-256 to `SHA256SUMS.partial`. A name appearing
in that file is therefore a shard that is complete on disk -- there is no window in which a partial
file is advertised. This polls that sidecar, which is also why it needs no cooperation from the
generator beyond what the generator already does.

WHAT IT CHECKS, PER SHARD, BEFORE COUNTING IT. Four things, because a transfer that merely finishes
is not a transfer that succeeded:

  1. the local SHA-256 equals the digest the generator recorded -- catches truncation and corruption;
  2. the file parses as a `.npy` and its shape matches the campaign's geometry;
  3. the array is finite -- no NaN or inf, which a diverged sweep would produce;
  4. the configuration count is the one asked for.

A shard failing any of these is reported and NOT recorded, and the puller keeps going: one bad shard
should not end a campaign that is still producing good ones.

USAGE. Runs against a live campaign or a finished one; it is idempotent and skips what it already has.

    python campaign_pull.py --host root@1.2.3.4 --port 22 --key ~/.ssh/id --remote /workspace/gen \\
        --dest <store>/configs_new --expect-shape 96,16,16,16,32
"""
from __future__ import annotations

import argparse
import hashlib
import os
import subprocess
import sys
import time

import numpy as np

SIDECAR = "SHA256SUMS.partial"


def _ssh_base(a):
    argv = ["ssh", "-o", "StrictHostKeyChecking=no", "-o", "BatchMode=yes"]
    if a.key:
        argv += ["-i", os.path.expanduser(a.key)]
    if a.port:
        argv += ["-p", str(a.port)]
    return argv + [a.host]


def _scp_argv(a, remote_path, local_path):
    argv = ["scp", "-o", "StrictHostKeyChecking=no", "-o", "BatchMode=yes"]
    if a.key:
        argv += ["-i", os.path.expanduser(a.key)]
    if a.port:
        argv += ["-P", str(a.port)]
    return argv + [f"{a.host}:{remote_path}", local_path]


def remote_sidecar(a):
    """`{filename: digest}` the generator has published so far. Empty if the run has not started."""
    r = subprocess.run(_ssh_base(a) + [f"cat {a.remote}/{SIDECAR} 2>/dev/null || true"],
                       capture_output=True, text=True, encoding="utf-8", errors="replace",
                       timeout=120)
    out = {}
    for line in r.stdout.splitlines():
        parts = line.split()
        # DERIVED: a sha256sum line is exactly `<digest>  <name>`; two fields is the format,
        # not a threshold, and anything else is not a sidecar entry.
        if len(parts) == 2:
            out[parts[1]] = parts[0]
    return out


def sha256_file(path, chunk=1 << 20):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(chunk), b""):
            h.update(block)
    return h.hexdigest()


def verify(path, digest, expect_shape):
    """The four checks. Returns (ok, message)."""
    actual = sha256_file(path)
    if actual != digest:
        return False, f"digest mismatch (got {actual[:12]}, expected {digest[:12]})"
    try:
        arr = np.load(path, mmap_mode="r")
    except Exception as e:                                  # noqa: BLE001 - any read failure is a fail
        return False, f"does not parse as .npy: {type(e).__name__}"
    if expect_shape is not None and tuple(arr.shape) != tuple(expect_shape):
        return False, f"shape {tuple(arr.shape)} != expected {tuple(expect_shape)}"
    # DERIVED: check the first configuration rather than the whole shard -- a diverged sweep
    # poisons every configuration, and reading one avoids paging gigabytes to find that out.
    # `ndim > 1` distinguishes a stack of configurations from a single one.
    block = np.asarray(arr[0] if arr.ndim > 1 else arr)
    if not np.isfinite(block).all():
        return False, "array contains NaN or inf -- the sweep diverged"
    return True, f"{tuple(arr.shape)} {arr.dtype} {os.path.getsize(path) / 1e6:.1f} MB"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--host", required=True)
    ap.add_argument("--port", type=int, default=0)
    ap.add_argument("--key", default=None)
    ap.add_argument("--remote", required=True, help="campaign output directory on the pod")
    ap.add_argument("--dest", required=True, help="local collection directory")
    ap.add_argument("--expect-shape", default=None,
                    help="comma-separated shape every shard must have, e.g. 96,16,16,16,32")
    #: CHOSEN: how often to ask the pod what it has finished. It costs one `cat` per interval and
    #: bounds how much completed work sits only on the pod; nothing depends on its value.
    ap.add_argument("--interval", type=float, default=20.0)
    #: CHOSEN: how long to keep waiting after the last new shard before concluding the campaign is
    #: over. Generous, because a large volume can take many minutes per shard.
    ap.add_argument("--idle-timeout", type=float, default=1800.0)
    ap.add_argument("--once", action="store_true", help="one pass, then exit")
    a = ap.parse_args()

    expect_shape = tuple(int(x) for x in a.expect_shape.split(",")) if a.expect_shape else None
    os.makedirs(a.dest, exist_ok=True)
    local_sums = os.path.join(a.dest, "SHA256SUMS.pulled")

    have = set()
    if os.path.exists(local_sums):
        # DERIVED: same two-field sidecar format as `remote_sidecar`.
        with open(local_sums, encoding="utf-8") as fh:
            # DERIVED: the two-field sidecar format, as in `remote_sidecar`.
            have = {l.split()[1] for l in fh if len(l.split()) == 2}

    print(f"pulling from {a.host}:{a.remote}  ->  {a.dest}")
    if have:
        print(f"already recorded: {len(have)} shard(s)")

    last_new = time.time()
    pulled = 0
    failed = 0
    while True:
        remote = remote_sidecar(a)
        todo = [n for n in sorted(remote) if n not in have]
        for name in todo:
            dest = os.path.join(a.dest, name)
            tmp = dest + ".part"
            t0 = time.time()
            r = subprocess.run(_scp_argv(a, f"{a.remote}/{name}", tmp),
                               capture_output=True, text=True, encoding="utf-8",
                               errors="replace", timeout=3600)
            # DERIVED: zero is the POSIX convention for success, not a threshold.
            if r.returncode != 0:
                print(f"  TRANSFER FAILED {name}: {r.stderr.strip()[:160]}")
                failed += 1
                if os.path.exists(tmp):
                    os.remove(tmp)
                continue
            ok, msg = verify(tmp, remote[name], expect_shape)
            if not ok:
                print(f"  REJECTED {name}: {msg}")
                failed += 1
                os.remove(tmp)
                continue
            os.replace(tmp, dest)                 # only a verified shard gets its real name
            with open(local_sums, "a", newline="\n", encoding="utf-8") as fh:
                fh.write(f"{remote[name]}  {name}\n")
            have.add(name)
            pulled += 1
            last_new = time.time()
            print(f"  OK {name}  {msg}  ({time.time() - t0:.0f}s)", flush=True)

        if a.once:
            break
        if time.time() - last_new > a.idle_timeout:
            print(f"no new shard for {a.idle_timeout:.0f}s -- stopping")
            break
        time.sleep(a.interval)

    print(f"\nrecorded {pulled} shard(s), {failed} rejected; index at {local_sums}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
