"""The one place that knows how to build the Lean development.

WHY A WRAPPER. Building Mathlib is expensive enough that it happens on a machine chosen for it, and
which machine that is belongs to the person running the program, not to the source. Every caller that
spelled out `subprocess.run(["lake", "build"], cwd=...)` was therefore hard-coding one answer, and a
second caller with a different answer would have been a second answer rather than a corrected one.
This module holds the decision once; callers ask for a build and read the output.

CONFIGURATION, and the default is deliberate. With nothing configured this builds LOCALLY, because a
researcher who clones this repository must be able to reproduce every artifact without access to any
particular machine. A remote builder is an optimisation for whoever has one, declared in the same
machine-local, git-ignored file that already carries the store root:

    LEAN_BUILD_HOST=builder@192.168.4.45          # ssh destination
    LEAN_BUILD_PORT=2222                          # optional, default 22
    LEAN_BUILD_KEY=~/.ssh/some_key                # optional
    LEAN_BUILD_DIR=massgap-lean                   # remote checkout, relative to $HOME
    LEAN_BUILD_PATH=$HOME/.elan/bin               # optional, prepended to remote PATH

WHAT A REMOTE BUILD DOES. It ships the Lean SOURCES and builds them there, so what is built is what is
on this machine, not whatever the remote checkout drifted to. It never ships or deletes `.lake`: that
directory holds the Mathlib build the remote host exists for, and re-transferring or clearing it would
cost hours. The consequence is worth stating plainly -- a remote build leaves any file that exists only
on the remote in place, so `sources_only_on_remote` reports them rather than letting them accumulate
unseen.

WHAT IT DOES NOT DO. It does not decide what to build, parse output, or write artifacts. Callers do
that; this returns the completed process.
"""
from __future__ import annotations

import os
import shlex
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import store_path  # noqa: E402  (needs HERE on sys.path first)

#: The Lean package root in this working tree.
LEAN = os.path.join(os.path.dirname(HERE), "lean")

#: The source files a build needs. `.lake` is excluded by construction, not by a filter: it is build
#: output, it is what the remote host is keeping for us, and it is measured in gigabytes.
SOURCE_GLOBS = ("MassGap.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json",
                "MassGap/*.lean")


def _cfg(key, default=None):
    return (os.environ.get(key, "").strip()
            or store_path.local_value(key)
            or default)


def target():
    """Where builds run, in words. `None` means locally."""
    host = _cfg("LEAN_BUILD_HOST")
    if not host:
        return None
    port = _cfg("LEAN_BUILD_PORT", "22")
    return f"{host}:{port}"


def _ssh_argv():
    argv = ["ssh", "-o", "StrictHostKeyChecking=no", "-o", "BatchMode=yes"]
    key = _cfg("LEAN_BUILD_KEY")
    if key:
        argv += ["-i", os.path.expanduser(key)]
    port = _cfg("LEAN_BUILD_PORT")
    if port:
        argv += ["-p", str(port)]
    return argv + [_cfg("LEAN_BUILD_HOST")]


def _remote_prelude():
    """`cd` into the remote checkout with the toolchain on PATH, as one shell prefix."""
    d = shlex.quote(_cfg("LEAN_BUILD_DIR", "massgap-lean"))
    extra = _cfg("LEAN_BUILD_PATH", "$HOME/.elan/bin")
    return f'export PATH="{extra}:$PATH"; cd {d} && '


# CHOSEN: a transfer budget in seconds. It bounds a hung network and nothing else -- the
# payload is under a megabyte of Lean sources, so any value that crosses a working link
# behaves identically. It caps waiting, never correctness.
def push_sources(timeout=600):
    """Ship this tree's Lean sources to the remote checkout. No-op when building locally.

    Sent as a tar stream rather than file-by-file: one round trip, and the transfer either lands
    whole or not at all. `.lake` is never included -- see the module docstring.
    """
    if target() is None:
        return None
    files = []
    import glob
    for g in SOURCE_GLOBS:
        files += [os.path.relpath(f, LEAN) for f in glob.glob(os.path.join(LEAN, g))]
    if not files:
        raise SystemExit(f"no Lean sources found under {LEAN}; refusing to push an empty tree")
    tar = subprocess.run(["tar", "czf", "-"] + sorted(files), cwd=LEAN,
                         capture_output=True, timeout=timeout)
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if tar.returncode != 0:
        raise SystemExit(f"tar failed: {tar.stderr.decode('utf-8', 'replace')[:400]}")
    r = subprocess.run(_ssh_argv() + [_remote_prelude() + "tar xzf -"],
                       input=tar.stdout, capture_output=True, timeout=timeout)
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if r.returncode != 0:
        raise SystemExit(f"pushing sources failed: {r.stderr.decode('utf-8', 'replace')[:400]}")
    return len(files)


def sources_only_on_remote():
    """Lean sources present on the remote but not here, as a sorted list.

    A push adds and overwrites; it does not delete. So a file retired here survives there and will be
    compiled into the next remote build, which is how a remote builder starts disagreeing with the
    tree it is supposed to be building. Reported rather than deleted: removing a file from someone
    else's machine is not a thing a build wrapper should do silently.
    """
    if target() is None:
        return []
    r = subprocess.run(_ssh_argv() + [_remote_prelude() + "ls MassGap/*.lean 2>/dev/null"],
                       capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120)
    remote = {os.path.basename(x.strip()) for x in r.stdout.split() if x.strip().endswith(".lean")}
    import glob
    here = {os.path.basename(f) for f in glob.glob(os.path.join(LEAN, "MassGap", "*.lean"))}
    return sorted(remote - here)


#: The ONLY directory a clear is ever allowed to touch, relative to the Lean package root. Written
#: out rather than assembled, so that reading this line tells you the whole blast radius. Mathlib's
#: build lives under `.lake/packages`, which this path does not contain and cannot reach.
BUILD_OUTPUT_DIR = ".lake/build/lib/lean"


def clear_project_build(dry_run=False):
    """Remove MassGap's own build products so the next build RE-ELABORATES.

    `#print axioms` is an info message emitted during elaboration, so a warm build replays nothing
    and reports an empty axiom table. Clearing the project's outputs is what makes the footprints
    reappear; clearing more than that would rebuild Mathlib, which is hours.

    Only `BUILD_OUTPUT_DIR/MassGap*` is touched, locally or remotely. The remote form is a `find`
    pinned to that directory with `-maxdepth 1`, so a name that is not a MassGap output cannot be
    reached however the glob is expanded, and `.lake/packages` is not under the search root at all.

    Returns the names removed.
    """
    if target() is None:
        root = os.path.join(LEAN, *BUILD_OUTPUT_DIR.split("/"))
        if not os.path.isdir(root):
            return []
        import shutil
        removed = []
        for name in sorted(os.listdir(root)):
            if not name.startswith("MassGap"):
                continue
            path = os.path.join(root, name)
            real = os.path.realpath(path)
            # belt and braces: the resolved path must still be inside the build tree, so a symlink
            # planted in the output directory cannot redirect a delete somewhere else
            assert os.path.join(".lake", "packages") not in real, real
            assert real.startswith(os.path.realpath(os.path.join(LEAN, ".lake", "build"))), real
            removed.append(name)
            if not dry_run:
                shutil.rmtree(path) if os.path.isdir(path) else os.remove(path)
        return removed

    listing = subprocess.run(
        _ssh_argv() + [_remote_prelude()
                       + f"test -d {BUILD_OUTPUT_DIR} && "
                         f"find {BUILD_OUTPUT_DIR} -maxdepth 1 -name 'MassGap*' -printf '%f\\n'"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300)
    names = sorted(x.strip() for x in listing.stdout.splitlines() if x.strip())
    if not names or dry_run:
        return names
    r = subprocess.run(
        _ssh_argv() + [_remote_prelude()
                       + f"find {BUILD_OUTPUT_DIR} -maxdepth 1 -name 'MassGap*' -exec rm -rf {{}} +"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300)
    # DERIVED: zero is the POSIX convention for success, not a threshold.
    if r.returncode != 0:
        raise SystemExit(f"remote clear failed: {r.stderr[:400]}")
    return names


# CHOSEN: two hours. Long enough for a cold MassGap elaboration against a warm Mathlib, short
# enough that a wedged build is noticed in one sitting. Caps waiting, never correctness.
def build(args=("build",), timeout=7200, push=True):
    """Run `lake <args>` where builds belong, and return the CompletedProcess.

    stdout and stderr come back as text either way, so a caller parsing `#print axioms` lines does
    not need to know where the build happened.
    """
    if target() is None:
        return subprocess.run(["lake", *args], cwd=LEAN, capture_output=True, text=True, encoding="utf-8", errors="replace",
                              timeout=timeout)
    if push:
        push_sources()
    cmd = _remote_prelude() + " ".join(["lake", *[shlex.quote(a) for a in args]])
    return subprocess.run(_ssh_argv() + [cmd], capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=timeout)


def describe():
    """One line naming where a build would run, for a script to print before it starts one."""
    t = target()
    return f"lean build target: {t} ({_cfg('LEAN_BUILD_DIR', 'massgap-lean')})" if t else \
        f"lean build target: local ({LEAN})"


if __name__ == "__main__":
    print(describe())
    extra = sources_only_on_remote()
    if extra:
        print(f"sources present ONLY on the remote ({len(extra)}): {', '.join(extra)}")
        print("these will be compiled by a remote build though nothing here defines them.")
    if sys.argv[1:2] == ["--clear-dry-run"]:
        names = clear_project_build(dry_run=True)
        print(f"a clear would remove {len(names)} product(s): {', '.join(names) or '(none)'}")
        raise SystemExit(0)
    r = build(tuple(sys.argv[1:]) or ("build",))
    # Lean writes UTF-8 (check marks, crosses, unicode identifiers). On a console whose encoding is
    # not UTF-8 a plain write raises, turning a successful build into a traceback -- so the streams
    # are reconfigured rather than the output sanitised, and what Lean said is what gets printed.
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding='utf-8', errors='replace')
        except (AttributeError, OSError):
            pass
    sys.stdout.write(r.stdout)
    sys.stderr.write(r.stderr)
    raise SystemExit(r.returncode)
