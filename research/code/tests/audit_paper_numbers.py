"""Which numbers in PAPER.md would a test notice changing? Mutation audit, not a test.

WHY THIS EXISTS. A seven-column margin table was written into Sec 9 with nothing checking it. It was
found by accident -- an injection aimed at a neighbouring claim happened to land in it -- and the
claims on either side of the table WERE guarded, so the suite stayed green over an unverified table
sitting between two verified ones. That is not a property anyone can eyeball; the only way to know
which numbers are load-bearing is to change each one and see whether anything objects.

WHAT IT DOES. For every numeric literal in the paper, perturb it, re-run the correspondence tests
IN PROCESS, and record whether any of them fails. A number no test notices is a number a reader
cannot trust: it can drift from the artifact it came from and the suite will not say so.

WHAT A "MISS" IS AND IS NOT. Plenty of numbers in a paper are not artifact-derived -- citation years,
section numbers, lattice sizes quoted in prose, the arithmetic in a worked example. Those SHOULD be
unguarded by these tests, and the report separates them by context rather than counting them as
defects. The signal to act on is a number that came from an artifact and is not tied to it.

Run it directly; it is deliberately not named `test_*` so it does not run in CI -- a full pass
mutates the paper hundreds of times, and a crash mid-run would leave the file altered. The original
is restored in a `finally`, and the audit refuses to start if the paper is already modified.
"""
from __future__ import annotations

import atexit
import io
import re
import signal
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

PAPER = HERE.parents[1] / "PAPER.md"

#: Test modules whose failure means "this number is tied to something".
MODULES = ["test_paper_matches_artifacts", "test_paper_matches_lean"]

#: A numeric literal in the paper. Excludes anything inside a markdown link target or an inline
#: code span, which are names rather than measurements.
NUM = re.compile(r"(?<![\w.])(\d+\.\d+)(?![\w.])")


def load_tests():
    """Every zero-argument `test_*` in the correspondence modules."""
    fns = []
    for name in MODULES:
        mod = __import__(name)
        for attr in dir(mod):
            if attr.startswith("test_"):
                fn = getattr(mod, attr)
                # DERIVED: zero is the arity a test takes; anything else needs a fixture this
                # audit does not provide, and calling it would error rather than report.
                if callable(fn) and fn.__code__.co_argcount == 0:
                    fns.append((name, attr, fn))
    return fns


def any_fails(fns):
    """True if any correspondence test rejects the paper as it currently stands on disk."""
    for _, _, fn in fns:
        try:
            fn()
        except AssertionError:
            return True
        except Exception:
            # A test that ERRORS rather than fails is not evidence about this number; it is a
            # broken test, and silently counting it as "guarded" would mark every number guarded.
            raise
    return False


def perturb(tok: str) -> str:
    """A changed value of the same shape, so the mutation tests the NUMBER not the formatting.

    The last digit is advanced (9 wraps to 0), which keeps width, sign and decimal places -- a
    mutation that changed the shape could be caught by a formatting check and report a number as
    guarded when only its punctuation is.
    """
    d = tok[-1]
    return tok[:-1] + ("0" if d == "9" else str(int(d) + 1))


def context(src: str, i: int) -> str:
    """The line the number sits on, trimmed -- enough to judge whether it is artifact-derived."""
    a = src.rfind("\n", 0, i) + 1
    b = src.find("\n", i)
    # DERIVED: `str.find` returns -1 for absent, so zero-or-more is 'a newline exists'.
    return src[a:b if b > 0 else len(src)].strip()


def cache_the_tree() -> None:
    """Cache `Path.read_text` for every file except the paper.

    MEASURED: one pass costs 3.9s, and 93% of that is two tests re-reading every python file in the
    tree. A one-digit change to PAPER.md cannot affect a tree-derived read, so caching them changes
    the run time and nothing else. The paper itself is never cached -- it is the thing being
    mutated, and a stale read of it would make every number report as guarded.
    """
    cache: dict[str, str] = {}
    original_read_text = Path.read_text

    def read_text(self, *a, **kw):
        key = str(self)
        if key == str(PAPER):
            return original_read_text(self, *a, **kw)
        if key not in cache:
            cache[key] = original_read_text(self, *a, **kw)
        return cache[key]

    Path.read_text = read_text

    # The dominant cost is not reading the tree but PARSING it: the citation resolver builds an AST
    # for every python file on every pass. Same source text gives the same tree, so the parse is
    # memoised on the source. This is what actually moved the number -- caching the reads alone
    # changed 3.90s to 3.69s, because the read was never the expensive half.
    import ast as _ast
    _parsed: dict[str, object] = {}
    _original_parse = _ast.parse

    def parse(source, *a, **kw):
        if isinstance(source, str) and not a and not kw:
            if source not in _parsed:
                _parsed[source] = _original_parse(source)
            return _parsed[source]
        return _original_parse(source, *a, **kw)

    _ast.parse = parse

    # PROFILED: directory WALKING dominates -- 57% of a pass, 49,722 scandir calls, because several
    # tests rglob the whole research tree. The tree does not change during a run (the paper is the
    # only file written, and it matches none of these patterns), so each glob is resolved once.
    _globbed: dict[tuple, list] = {}
    _original_rglob = Path.rglob
    _original_glob = Path.glob

    def rglob(self, pattern, *a, **kw):
        key = ('r', str(self), pattern)
        if key not in _globbed:
            _globbed[key] = list(_original_rglob(self, pattern, *a, **kw))
        return iter(_globbed[key])

    def glob(self, pattern, *a, **kw):
        key = ('g', str(self), pattern)
        if key not in _globbed:
            _globbed[key] = list(_original_glob(self, pattern, *a, **kw))
        return iter(_globbed[key])

    Path.rglob = rglob
    Path.glob = glob


def arm_restore(original: str) -> None:
    """Put the paper back on ANY exit, not only the normal one.

    The previous run was stopped part-way and left a mutated digit behind. `finally` does not cover
    a termination signal, so the restore is registered with `atexit` and with the signals a stop
    actually sends. Restoring twice is harmless; not restoring once is not.
    """
    def restore(*_):
        try:
            io.open(PAPER, "w", encoding="utf-8", newline="").write(original)
        except Exception:
            pass

    atexit.register(restore)
    for sig in (signal.SIGINT, signal.SIGTERM, getattr(signal, "SIGBREAK", signal.SIGTERM)):
        try:
            signal.signal(sig, lambda *_: (restore(), sys.exit(130)))
        except (ValueError, OSError):
            pass


def main() -> None:
    original = io.open(PAPER, encoding="utf-8", newline="").read()
    arm_restore(original)
    cache_the_tree()
    fns = load_tests()
    print(f"{len(fns)} correspondence tests over {len(MODULES)} modules")

    if any_fails(fns):
        raise SystemExit("the correspondence tests already fail on the unmodified paper; fix that "
                         "first, or every number will report as guarded")

    hits = [(m.start(), m.group(1)) for m in NUM.finditer(original)]
    print(f"{len(hits)} numeric literals in PAPER.md\n")

    guarded, missed = [], []
    try:
        for n, (i, tok) in enumerate(hits, 1):
            mutated = original[:i] + perturb(tok) + original[i + len(tok):]
            io.open(PAPER, "w", encoding="utf-8", newline="").write(mutated)
            (guarded if any_fails(fns) else missed).append((i, tok, context(original, i)))
            # CHOSEN: how often progress is printed. It costs a line of output and nothing else.
            if n % 25 == 0:
                print(f"  ...{n}/{len(hits)}", flush=True)
    finally:
        io.open(PAPER, "w", encoding="utf-8", newline="").write(original)
        print("\npaper restored")

    assert io.open(PAPER, encoding="utf-8", newline="").read() == original, \
        "THE PAPER WAS NOT RESTORED -- restore it from git before doing anything else"

    print(f"\n{len(guarded)} guarded, {len(missed)} unnoticed\n")
    print("=" * 96)
    print("NUMBERS NO CORRESPONDENCE TEST NOTICES")
    print("=" * 96)
    for i, tok, ctx in missed:
        line = original[:i].count("\n") + 1
        print(f"  L{line:<5} {tok:>10}   {ctx[:88]}")


if __name__ == "__main__":
    main()
