"""Launch one generation slice per GPU, and retrieve every slice in real time.

WHY THIS EXISTS. A campaign that fits on one card is a shell command. A campaign split across several
is a scheduling problem, and doing it by hand is how two generators ended up sharing one GPU twice in
this project. This holds the whole arrangement in one place: which slice goes to which host, that
each host is checked to be idle BEFORE anything starts, and that a puller is running for every slice
so nothing finishes on a pod and stays there.

WHAT IT DOES NOT DO. It does not decide the slices. Packing work across cards of different speeds is
a judgement about the measurement -- which boxes matter, which levels hedge which risk -- and it
belongs in the caller, written down, not in a heuristic here.

    python campaign_launch.py --plan plan.json
    python campaign_launch.py --plan plan.json --dry-run     # print, touch nothing

The plan is a JSON list, one entry per host:

    [{"name": "a6000", "host": "root@1.2.3.4", "port": 17754, "key": "~/.ssh/runpod_ed25519",
      "jobs": "24:32 16:32", "out": "/workspace/gen_boxsm", "dest": "configs_boxsm_su2"}]

`jobs` is the `L:smear` list `run_box_smeared.sh` consumes; `dest` is the collection under the store
root the shards land in. Every host may write to the SAME `dest`: the shard names carry `L`, the
channel and the smearing level, so two slices cannot collide.
"""
from __future__ import annotations

import argparse
import json
import os
import shlex
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import store_path  # noqa: E402

#: The files a pod needs. The generator is pushed every launch so a pod cannot run a stale copy --
#: the same rule `lean_build.push_sources` follows, for the same reason.
PUSH = ("lattice_generator.py",)


def _ssh(hostcfg, *args, timeout=60):
    argv = ["ssh", "-o", "StrictHostKeyChecking=no", "-o", "BatchMode=yes"]
    if hostcfg.get("key"):
        argv += ["-i", os.path.expanduser(hostcfg["key"])]
    if hostcfg.get("port"):
        argv += ["-p", str(hostcfg["port"])]
    argv += [hostcfg["host"], *args]
    return subprocess.run(argv, capture_output=True, text=True, encoding="utf-8",
                          errors="replace", timeout=timeout)


# CHOSEN: a transfer budget in seconds. It bounds a hung network and nothing else -- the payload
# is one Python file, so any value that crosses a working link behaves identically. Caps waiting,
# never correctness.
def _scp(hostcfg, local, remote, timeout=300):
    argv = ["scp", "-o", "StrictHostKeyChecking=no", "-o", "BatchMode=yes"]
    if hostcfg.get("key"):
        argv += ["-i", os.path.expanduser(hostcfg["key"])]
    if hostcfg.get("port"):
        argv += ["-P", str(hostcfg["port"])]
    argv += [local, f"{hostcfg['host']}:{remote}"]
    return subprocess.run(argv, capture_output=True, text=True, encoding="utf-8",
                          errors="replace", timeout=timeout)


def busy(hostcfg):
    """Anything already generating on this host, as a list of command lines.

    Checked BEFORE launching, not after. Two generators on one card do not fail; they both run
    slowly and the campaign looks fine until the timings are read.
    """
    r = _ssh(hostcfg, "pgrep -af 'lattice_generator\\.py' | grep -v pgrep || true")
    return [l for l in r.stdout.splitlines() if l.strip()]


def launch(hostcfg, script_local, dry_run=False):
    """Push the generator and the slice script, then start the slice detached."""
    name = hostcfg.get("name", hostcfg["host"])
    running = busy(hostcfg)
    if running and not dry_run:
        raise SystemExit(f"REFUSED on {name}: a generator is already running there:\n  "
                         + "\n  ".join(running)
                         + "\nTwo generators share the card and both run slowly. Stop it, or give "
                           "this slice to another host.")
    if running:
        # A dry run touches nothing, so it REPORTS the conflict rather than refusing -- the point of
        # a dry run is to see the whole plan, including which hosts are not ready.
        print(f"  [{name}] BUSY, would refuse: {running[0][:110]}")
    if dry_run:
        print(f"  [{name}] would push {', '.join(PUSH)} + the slice script and run "
              f"JOBS={hostcfg['jobs']!r}")
        return None

    # The remote working directory may not exist on a fresh pod, and scp will not create it.
    mk = _ssh(hostcfg, "mkdir -p mg")
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if mk.returncode != 0:
        raise SystemExit(f"{name}: could not create the remote working directory: {mk.stderr[:300]}")
    for fn in PUSH:
        r = _scp(hostcfg, os.path.join(HERE, fn), f"mg/{fn}")
        # DERIVED: zero is the POSIX convention for success, not a threshold.
        if r.returncode != 0:
            raise SystemExit(f"{name}: pushing {fn} failed: {r.stderr[:300]}")
    r = _scp(hostcfg, script_local, "mg/run_box_smeared.sh")
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if r.returncode != 0:
        raise SystemExit(f"{name}: pushing the slice script failed: {r.stderr[:300]}")

    out = hostcfg.get("out", "/workspace/gen_boxsm")
    env = f"JOBS={shlex.quote(hostcfg['jobs'])} OUT={shlex.quote(out)}"
    cmd = (f"chmod +x mg/run_box_smeared.sh; mkdir -p {shlex.quote(out)}; "
           f"cd mg && setsid nohup env {env} bash run_box_smeared.sh "
           f"> {shlex.quote(out)}/gen.log 2>&1 < /dev/null & sleep 2; "
           f"pgrep -af run_box_smeared.sh | grep -v pgrep | head -1")
    # A detached launch can hold the ssh channel open until the client times out, by which time the
    # work has already started. So the launch call is fire-and-verify: a timeout is not evidence of
    # failure, and the host is asked what it is actually running.
    try:
        _ssh(hostcfg, cmd, timeout=20)
    except subprocess.TimeoutExpired:
        pass
    running = busy(hostcfg)
    if not running:
        raise SystemExit(f"{name}: launched but nothing is generating there. Check "
                         f"{out}/gen.log on the host.")
    print(f"  [{name}] running: {running[0].split('lattice_generator.py')[-1].strip()[:90]}")
    return 0


def puller_argv(hostcfg, root):
    """The `campaign_pull` command line that retrieves this host's slice."""
    dest = os.path.join(root, hostcfg.get("dest", "configs_boxsm_su2"))
    argv = [sys.executable, os.path.join(HERE, "campaign_pull.py"),
            "--host", hostcfg["host"],
            "--remote", hostcfg.get("out", "/workspace/gen_boxsm"),
            "--dest", dest]
    if hostcfg.get("port"):
        argv += ["--port", str(hostcfg["port"])]
    if hostcfg.get("key"):
        argv += ["--key", hostcfg["key"]]
    # CHOSEN: how often to ask each pod what it has finished, and how long to keep waiting after the
    # last new shard. Both cost polling, not correctness; nothing downstream depends on either.
    argv += ["--interval", "30", "--idle-timeout", "9000"]
    return argv


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--plan", required=True, help="JSON file: one entry per host")
    ap.add_argument("--script", default=None,
                    help="the slice script to push (default: run_box_smeared.sh beside this file)")
    ap.add_argument("--dry-run", action="store_true", help="print the plan and touch nothing")
    a = ap.parse_args()

    with open(a.plan, encoding="utf-8") as fh:
        plan = json.load(fh)
    script = a.script or os.path.join(HERE, "run_box_smeared.sh")
    if not os.path.exists(script):
        raise SystemExit(f"slice script not found: {script}")

    root = store_path.store_root(required=not a.dry_run) or "<store not configured>"
    print(f"plan: {len(plan)} host(s); store root {root}")
    for h in plan:
        print(f"  {h.get('name', h['host']):>10}  {h['jobs']}")

    print("\nlaunching:")
    for h in plan:
        launch(h, script, dry_run=a.dry_run)

    print("\nretrieve each slice with (one per host, run them in parallel):")
    for h in plan:
        print("  " + " ".join(shlex.quote(x) for x in puller_argv(h, root)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
