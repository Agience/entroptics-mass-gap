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

This is a BUILD, not a read: it needs the Lean toolchain and a warm .lake, and it is not cheap.
Builds run on a dedicated node rather than the workstation, so `--from-log PATH` parses a log
that build produced instead of running one here. Both paths share the parser and the shortfall
guard, so a log from a warm build -- which replays no info messages -- is refused exactly as a
short local build is.
"""
from __future__ import annotations

import csv
import os
import re
import shutil
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
LEAN = os.path.join(REPO, "research", "lean")
OUT_CSV = os.path.join(REPO, "research", "data", "13_dat_axiom_footprints.csv")

# 'name' depends on axioms: [a, b, c]   |   'name' does not depend on any axioms
_DEPENDS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
_CLEAN = re.compile(r"'([^']+)' does not depend on any axioms")


def project_build_outputs():
    """MassGap's own build products, and nothing else.

    `#print axioms` output is an info message emitted while a module ELABORATES. A warm .lake
    replays nothing for modules it does not rebuild, so a second `lake build` produces an empty
    table -- which is why this exists. Clearing the project's own outputs makes MassGap re-elaborate
    while Mathlib stays cached; `lake build --no-cache` would rebuild Mathlib too, for hours.

    Returns paths under .lake/build/lib/lean named MassGap*. Anything under .lake/packages is a
    dependency's build and is never returned, so a bad glob cannot cost a Mathlib rebuild.
    """
    root = os.path.join(LEAN, ".lake", "build", "lib", "lean")
    if not os.path.isdir(root):
        return []
    out = []
    for name in sorted(os.listdir(root)):
        if not name.startswith("MassGap"):
            continue
        path = os.path.join(root, name)
        real = os.path.realpath(path)
        assert os.path.join(".lake", "packages") not in real, real
        assert real.startswith(os.path.realpath(os.path.join(LEAN, ".lake", "build"))), real
        out.append(path)
    return out


def clear_project_build(dry_run=False):
    """Remove MassGap's build products so the next build re-elaborates and replays its info messages."""
    targets = project_build_outputs()
    for t in targets:
        print("  clearing %s" % os.path.relpath(t, LEAN))
        if not dry_run:
            shutil.rmtree(t) if os.path.isdir(t) else os.remove(t)
    return targets


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
                m = re.match(r"\s*#print axioms\s+([A-Za-z_][A-Za-z0-9_.']*)", line)
                if m:
                    want.add(m.group(1).split(".")[-1])
    return want


def build_here() -> str:
    """Re-elaborate MassGap locally and return the build output."""
    cleared = clear_project_build()
    print(f"cleared {len(cleared)} project build product(s); Mathlib's cache is untouched. Building...")
    r = subprocess.run(["lake", "build"], cwd=LEAN, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
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
    if short:
        raise SystemExit(
            f"the build surfaced {len(found)} footprints but {len(short)} of the requested ones are "
            f"missing ({short[:6]}...): a module that does not re-elaborate replays no info "
            "message. A local build clears the project's build products first so this cannot "
            "happen; a --from-log run cannot, so the usual cause there is a log from a warm "
            "build. Otherwise a declaration was renamed, or a `#print axioms` names something no "
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
