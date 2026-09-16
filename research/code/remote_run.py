"""The one place that knows where heavy Python runs.

WHY A WRAPPER. `lean_build.py` already holds this decision for Lean: which machine compiles belongs
to the person running the program, not to the source. The same is true of the reads. A certificate
that reseeds a 4-block ensemble, or a mass sweep across three window widths, is minutes of CPU, and
minutes of CPU on the workstation is minutes the workstation is not usable. Every caller that spelled
out `python some_certificate.py` was hard-coding one answer to that question. This module holds it
once; callers ask for a run and read the output.

CONFIGURATION, and the default is deliberate. With nothing configured this runs LOCALLY, because a
researcher who clones this repository must be able to reproduce every artifact without access to any
particular machine. A compute host is an optimisation for whoever has one, declared in the same
machine-local, git-ignored file that already carries the store root and the Lean builder:

    COMPUTE_HOST=builder@192.168.4.45          # ssh destination
    COMPUTE_PORT=2222                          # optional, default 22
    COMPUTE_KEY=~/.ssh/some_key                # optional
    COMPUTE_DIR=research                       # remote working tree, relative to $HOME
    COMPUTE_PY=$HOME/research-venv/bin/python  # the interpreter there

ITS OWN KEYS, not the Lean builder's. The two roles happen to be the same machine here, and reading
one set of keys for both would bake that coincidence into the source: moving the reads to a bigger
box would then move the Lean build with them. They are separate questions and get separate answers.
There is no fallback from one to the other, for the same reason.

WHAT A REMOTE RUN DOES. It ships the Python SOURCES and runs them there, so what runs is what is on
this machine, not whatever the remote checkout drifted to. It does NOT ship the ensemble store: the
store is tens of gigabytes and lives where `store_path` says it lives. So a script that reads the
store runs locally and a script that generates its own data runs anywhere -- `needs_store` is the
caller's declaration of which it is, and asking for a remote run of a store-reading script fails
loudly rather than producing a read of an empty directory.

WHAT IT DOES NOT DO. It does not decide what to run, parse output, or write artifacts. Callers do
that; this returns the completed process.

    python remote_run.py --describe
    python remote_run.py certify/gap_of_maximal_correlation.py
"""
from __future__ import annotations

import argparse
import glob
import os
import shlex
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import store_path  # noqa: E402  (needs HERE on sys.path first)

#: The research tree root -- the parent of `code/`.
RESEARCH = os.path.dirname(HERE)

#: The sources a run needs, relative to `RESEARCH`. Data artifacts are NOT shipped: a run either
#: produces them or reads the store, and the store does not travel.
SOURCE_GLOBS = ("requirements.txt", "code/*.py", "code/certify/*.py", "code/tests/*.py",
                "data/*.py")


def _cfg(key, default=None):
    return (os.environ.get(key, "").strip()
            or store_path.local_value(key)
            or default)


def target():
    """Where heavy runs go, in words. `None` means locally."""
    host = _cfg("COMPUTE_HOST")
    if not host:
        return None
    return f"{host}:{_cfg('COMPUTE_PORT', '22')}"


def _ssh_argv():
    argv = ["ssh", "-o", "StrictHostKeyChecking=no", "-o", "BatchMode=yes"]
    key = _cfg("COMPUTE_KEY")
    if key:
        argv += ["-i", os.path.expanduser(key)]
    port = _cfg("COMPUTE_PORT")
    if port:
        argv += ["-p", str(port)]
    return argv + [_cfg("COMPUTE_HOST")]


def _remote_dir():
    return _cfg("COMPUTE_DIR", "research")


def _remote_prelude():
    """`cd` into the remote tree, as one shell prefix."""
    return f"cd {shlex.quote(_remote_dir())} && "


# CHOSEN: a transfer budget in seconds. It bounds a hung network and nothing else -- the payload is
# well under a megabyte of Python sources, so any value that crosses a working link behaves
# identically. It caps waiting, never correctness.
def push_sources(timeout=600):
    """Ship this tree's Python sources to the remote working tree. No-op when running locally.

    Sent as a tar stream rather than file-by-file: one round trip, and the transfer either lands
    whole or not at all.
    """
    if target() is None:
        return None
    files = []
    for g in SOURCE_GLOBS:
        files += [os.path.relpath(f, RESEARCH).replace("\\", "/")
                  for f in glob.glob(os.path.join(RESEARCH, *g.split("/")))]
    if not files:
        raise SystemExit(f"no Python sources found under {RESEARCH}; refusing to push an empty tree")
    tar = subprocess.run(["tar", "czf", "-"] + sorted(files), cwd=RESEARCH,
                         capture_output=True, timeout=timeout)
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if tar.returncode != 0:
        raise SystemExit(f"tar failed: {tar.stderr.decode('utf-8', 'replace')[:400]}")
    r = subprocess.run(
        _ssh_argv() + [f"mkdir -p {shlex.quote(_remote_dir())} && " + _remote_prelude() + "tar xzf -"],
        input=tar.stdout, capture_output=True, timeout=timeout)
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if r.returncode != 0:
        raise SystemExit(f"pushing sources failed: {r.stderr.decode('utf-8', 'replace')[:400]}")
    return len(files)


def sources_only_on_remote():
    """Python sources present on the remote but not here, as a sorted list of relative paths.

    A push adds and overwrites; it does not delete. So a file retired here survives there and would
    be run by the next remote invocation, which is how a compute host starts disagreeing with the
    tree it is supposed to be running. Reported rather than deleted: removing a file from someone
    else's machine is not a thing a run wrapper should do silently.
    """
    if target() is None:
        return []
    r = subprocess.run(
        _ssh_argv() + [_remote_prelude() + "ls code/*.py code/certify/*.py code/tests/*.py "
                                           "data/*.py 2>/dev/null"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120)
    remote = {x.strip() for x in r.stdout.split() if x.strip().endswith(".py")}
    here = set()
    for g in SOURCE_GLOBS:
        if g.endswith(".py"):
            here |= {os.path.relpath(f, RESEARCH).replace("\\", "/")
                     for f in glob.glob(os.path.join(RESEARCH, *g.split("/")))}
    return sorted(remote - here)


# CHOSEN: one hour. Long enough for the heaviest reseeded certificate, short enough that a wedged
# run is noticed in one sitting. Caps waiting, never correctness.
def run(script, args=(), *, needs_store=False, timeout=3600, push=True, unbuffered=True):
    """Run `python <script> <args>` where heavy work belongs; return the CompletedProcess.

    `script` is relative to the research tree (e.g. `certify/gap_of_maximal_correlation.py` or
    `code/certify/...`; both spellings resolve, since certificates live under `code/` and figure
    scripts under `data/`).

    `needs_store=True` says the script reads the ensemble store, which does not travel -- such a
    script runs locally even when a compute host is configured, because running it there would read
    an empty directory and report a measurement on nothing.

    `unbuffered` passes `-u`, so a long run's progress is visible while it runs instead of arriving
    in one block at the end. Learned the expensive way: a buffered background run produced hours of
    GPU work and no output to show for it.
    """
    rel = script.replace("\\", "/")
    if not os.path.exists(os.path.join(RESEARCH, *rel.split("/"))):
        for prefix in ("code", "data"):
            cand = f"{prefix}/{rel}"
            if os.path.exists(os.path.join(RESEARCH, *cand.split("/"))):
                rel = cand
                break
        else:
            raise SystemExit(f"no such script under {RESEARCH}: {script}")

    py_args = (["-u"] if unbuffered else []) + [rel, *map(str, args)]

    if target() is None or needs_store:
        return subprocess.run([sys.executable, *py_args], cwd=RESEARCH, capture_output=True,
                              text=True, encoding="utf-8", errors="replace", timeout=timeout)
    if push:
        push_sources()
    py = _cfg("COMPUTE_PY", "python3")
    cmd = _remote_prelude() + " ".join([py] + [shlex.quote(a) for a in py_args])
    return subprocess.run(_ssh_argv() + [cmd], capture_output=True, text=True,
                          encoding="utf-8", errors="replace", timeout=timeout)


def describe():
    """One line naming where heavy runs go, for a caller that wants to say so."""
    t = target()
    if t is None:
        return "compute target: local"
    return f"compute target: {t} ({_remote_dir()}, {_cfg('COMPUTE_PY', 'python3')})"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("script", nargs="?", help="script path relative to the research tree")
    ap.add_argument("args", nargs="*", help="arguments passed through to the script")
    ap.add_argument("--describe", action="store_true", help="print the target and exit")
    ap.add_argument("--needs-store", action="store_true",
                    help="the script reads the ensemble store, so run it locally")
    ap.add_argument("--drift", action="store_true",
                    help="list sources present on the remote but not here, and exit")
    a = ap.parse_args()

    print(describe(), file=sys.stderr)
    if a.describe:
        return 0
    if a.drift:
        for f in sources_only_on_remote():
            print(f)
        return 0
    if not a.script:
        ap.error("a script is required unless --describe or --drift is given")
    r = run(a.script, a.args, needs_store=a.needs_store)
    sys.stdout.write(r.stdout)
    sys.stderr.write(r.stderr)
    return r.returncode


if __name__ == "__main__":
    raise SystemExit(main())
