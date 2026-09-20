"""Capture the axiom footprint of every `#print axioms` in MassGap as a committed artifact.

PAPER Sec 13 states the footprint of the flagship theorems -- "the three foundational axioms plus
`wilson_reflection_positive`", "foundation-only", "the four named axioms". Lean already checks those
claims: the sources carry `#print axioms` commands, and every build prints what each declaration
really depends on. But that output lives in the build log and nothing keeps it, so the paper's
footprint table can only be compared against a build someone happens to have run. This writes it
down, and `test_paper_matches_lean.py` compares the table to the paper.

Runs `lake build` in research/lean and parses the info messages, which take the two forms

    'MassGap.CellEnclosure.gap_uniform_of_cell' depends on axioms: [propext, Classical.choice]
    'MassGap.FreeField.muInf_lt_floor' does not depend on any axioms

Emits 13_dat_axiom_footprints.csv (declaration, axioms, n_axioms), sorted, one row per printed
declaration. Refuses to write a partial table: a build that fails, or that surfaces fewer
declarations than the sources ask to print, leaves the committed artifact alone.

This is a BUILD, not a read: it needs the Lean toolchain and a warm .lake. It builds WARM --
Lean caches each module's `#print axioms` output and replays it, MEASURED 2026-09-19 -- so a run
costs minutes rather than the fifty-five a cold re-elaboration took. If the shortfall guard fires,
it clears and re-elaborates cold once, automatically.
Builds run on a dedicated node rather than the workstation, so `--from-log PATH` parses a log
that build produced instead of running one here. Both paths share the parser and the shortfall
guard, so a log from a warm build -- which replays no info messages -- is refused exactly as a
short local build is.
"""
from __future__ import annotations

import csv
import os
import re
import subprocess

import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
LEAN = os.path.join(REPO, "research", "lean")

sys.path.insert(0, os.path.dirname(_HERE))          # research/code, for the build wrapper
import lean_build as LB                             # noqa: E402  (needs the path above first)
OUT_CSV = os.path.join(REPO, "research", "data", "13_dat_axiom_footprints.csv")

# 'name' depends on axioms: [a, b, c]   |   'name' does not depend on any axioms
#
# GREEDY, and that is the whole point. Lean wraps the name in single quotes, so a declaration whose
# name ENDS IN A PRIME prints as `'MassGap.HaarVariance.haar_variance_reTr_pos'' depends on ...` --
# two quotes in a row. A `'([^']+)'` pattern cannot cross that prime: it matches up to `...pos`, then
# needs ` depends` and finds `' depends`, and no backtracking rescues it because the class excludes
# the quote. The line is dropped SILENTLY, and a primed declaration vanishes from the table.
# `.+` backtracks to the last `' depends on axioms:` instead, which captures the prime.
# Caught 2026-09-19 by this script's own shortfall guard refusing to write a partial table.
_DEPENDS = re.compile(r"'(.+)' depends on axioms: \[([^\]]*)\]")
_CLEAN = re.compile(r"'(.+)' does not depend on any axioms")


def parse(text: str) -> dict[str, list[str]]:
    """Declaration -> its axiom list, from `lake build` output. [] means axiom-free."""
    out: dict[str, list[str]] = {}
    for m in _DEPENDS.finditer(text):
        out[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in _CLEAN.finditer(text):
        out.setdefault(m.group(1), [])
    return out


def requested() -> set[str]:
    """Every declaration the sources ask to print, so a short build cannot pass as a full one."""
    want = set()
    src = os.path.join(LEAN, "MassGap")
    if not os.path.isdir(src):
        raise SystemExit(
            f"{src}: no Lean sources here. The footprint table is read out of a build of\n"
            "  this tree, so there is nothing to capture -- refusing rather than writing an\n"
            "  empty table. Builds run on the Lean node; bring its log back and pass\n"
            "  --from-log <log>.")
    for fn in sorted(os.listdir(src)):
        if not fn.endswith(".lean"):
            continue
        with open(os.path.join(src, fn), encoding="utf-8", errors="replace") as fh:
            for line in fh:
                # Lean identifiers are UNICODE. An ASCII-only class silently truncates a name at its
                # first non-ASCII character -- `exp_κ₀YM` was read as `exp_`, which then matched
                # nothing in the build output and made a complete table look like a partial one.
                # The shortfall guard refused to write, correctly, for a reason that was not the real
                # one. Anything that is not whitespace is part of the name.
                m = re.match(r"\s*#print axioms\s+(\S+)", line)
                if m:
                    want.add(m.group(1).split(".")[-1])
    return want



def requested_by_module() -> dict:
    """{module basename: {declaration basenames it asks to print}}.

    Separate from `requested()` because the guard below asks a different question: not "is this name
    anywhere in the build" but "did THIS module contribute anything at all". A module that asks for
    footprints and yields none was never elaborated, and its declarations' axiom claims are unchecked.
    """
    out: dict = {}
    src = os.path.join(LEAN, "MassGap")
    for fn in sorted(os.listdir(src)):
        if not fn.endswith(".lean"):
            continue
        names = set()
        with open(os.path.join(src, fn), encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = re.match(r"\s*#print axioms\s+(\S+)", line)
                if m:
                    names.add(m.group(1).split(".")[-1])
        if names:
            out[fn[:-len(".lean")]] = names
    return out

def build_here(*, cold: bool = False) -> str:
    """Re-elaborate MassGap where builds belong, and return the build output.

    "Here" is whatever `lean_build` resolves to: local by default, or a configured build host. The
    footprint table is a property of the SOURCES, not of the machine that compiled them, so a build
    host changes how long this takes and nothing else -- and the sources are pushed before the build,
    so a remote host cannot report footprints for a tree other than this one.
    """
    print(LB.describe())
    orphans = LB.sources_only_on_remote()
    if orphans:
        # A remote build compiles what is THERE. A source that exists only on the build host is
        # still elaborated, so its declarations would enter this artifact while nothing in this
        # repository defines them -- a footprint for a theorem the paper cannot cite.
        raise SystemExit(
            f"REFUSED: the build host carries {len(orphans)} Lean source(s) this tree does not: "
            f"{', '.join(orphans)}. They would be compiled into the footprint table while nothing "
            f"here defines them. Remove them there, or add them here, then re-run.")
    return _build(cold=cold)


def _build(*, cold: bool) -> str:
    """One build, warm by default.

    MEASURED 2026-09-19: a warm build replays the `#print axioms` output. `lean_build.py build
    MassGap.Floor` on a fully warm tree prints `Replayed MassGap.Floor` and both of that module's
    footprint lines. Lean caches info messages alongside the module. The cold path cost fifty
    minutes a run and bought nothing the shortfall guard does not already check.
    """
    if cold:
        cleared = LB.clear_project_build()
        print(f"cleared {len(cleared)} project build product(s); Mathlib's cache is untouched.")
    print("Building..." if cold else "Building (warm; the shortfall guard checks the result)...")
    r = LB.build()
    blob = (r.stdout or "") + "\n" + (r.stderr or "")
    if r.returncode != 0:
        sys.stderr.write(blob[-4000:])
        raise SystemExit(f"lake build failed (exit {r.returncode}): leaving the artifact alone")
    return blob


def read_log(path: str) -> str:
    """The output of a build run elsewhere, on the sources this repo currently holds."""
    if not os.path.exists(path):
        raise SystemExit(f"{path}: no such log")
    with open(path, encoding="utf-8", errors="replace") as fh:
        blob = fh.read()
    if re.search(r"^\s*error", blob, re.M) or "Build completed successfully" not in blob:
        raise SystemExit(f"{path} is not a clean successful build: leaving the artifact alone")
    return blob


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    log_path = None
    if "--from-log" in argv:
        i = argv.index("--from-log")
        if i + 1 >= len(argv):
            raise SystemExit("--from-log needs a path")
        log_path = argv[i + 1]

    want = requested()
    if not want:
        raise SystemExit("no `#print axioms` found in MassGap: refusing to write an empty table")
    print(f"MassGap asks to print {len(want)} footprints.")
    blob = read_log(log_path) if log_path else build_here()

    found = parse(blob)
    short = sorted(n for n in want if not any(k.split(".")[-1] == n for k in found))

    # A module that asks for footprints and contributes NONE was never elaborated. The basename
    # check above cannot see this: a name satisfied from any module satisfies a request from every
    # module, which is how eight whole namespaces -- 203 `#print axioms`, the entire live front --
    # went missing from this artifact on 2026-09-19 while the gate stayed green. Matching is by the
    # names a module asks for rather than by its file name, because several files here declare a
    # namespace that differs from the file (CellCouple.lean declares MassGap.CellEnclosure).
    found_bases = {k.split(".")[-1] for k in found}
    silent = sorted(mod for mod, names in requested_by_module().items()
                    if not (names & found_bases))
    if silent and not short:
        short = ["<module %s contributed no footprint>" % m for m in silent]

    if short and log_path is None:
        # The warm build did not surface everything. Clear and re-elaborate ONCE, automatically:
        # one route, no operator flag, and the slow path is spent only when it is actually needed.
        print(f"{len(short)} requested footprint(s) missing from the warm build; "
              "clearing and re-elaborating cold.")
        blob = build_here(cold=True)
        found = parse(blob)
        found_bases = {k.split(".")[-1] for k in found}
        short = sorted(n for n in want if n not in found_bases)
        short += ["<module %s contributed no footprint>" % m
                  for m, names in requested_by_module().items() if not (names & found_bases)]
        short = sorted(short)
    if short:
        raise SystemExit(
            f"the build surfaced {len(found)} footprints but {len(short)} of the requested ones are "
            f"missing ({short[:6]}...): a module that does not re-elaborate replays no info "
            "message. A cold re-elaboration has already been tried and did not recover them "
            "(a --from-log run does not try, so there the usual cause is a truncated or piped "
            "log). Otherwise a declaration was renamed, or a `#print axioms` names something no "
            "longer reachable. Refusing to write a partial table.")

    rows = [{"declaration": k, "axioms": " ".join(sorted(v)), "n_axioms": len(v)}
            for k, v in sorted(found.items())]
    with open(OUT_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["declaration", "axioms", "n_axioms"])
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {OUT_CSV} ({len(rows)} declarations)")
    axiom_free = sum(1 for r_ in rows if r_["n_axioms"] == 0)
    print(f"  {axiom_free} axiom-free; {len(rows) - axiom_free} carry at least one axiom")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
