"""A function must not be shadowed by a local of the same name in a function that calls it.

WHAT THIS CATCHES, and it is not hypothetical. `certify/string_tension_eq_centre.py` defined a
module-level predicate `resolved(mean, spread)` -- the resolution guard -- and later, inside `main()`,
bound a list to the same name:

    resolved = [r for r in rows if r["Z_over_full"] != ""]

Python decides scope per function at compile time, so binding the name ANYWHERE in `main()` made it
local throughout `main()`, and the earlier call `ok = resolved(sf, sf_spread)` became an
`UnboundLocalError`. The guard could not run at all.

WHY NOTHING ELSE SAW IT. The module imports cleanly, every test passes, and the script's own docstring
describes the guard correctly. The failure appears only when execution reaches the call -- on a GPU
host, minutes into a run, after the ensemble has been generated. It cost a full launch to discover.

The check is static and costs milliseconds, which is the point: this class of defect is invisible to
import, to linting that does not track scope, and to any suite that does not run the script end to
end against real data.
"""
from __future__ import annotations

import ast
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
CODE = REPO / "research" / "code"


def _assigned_names(fn: ast.AST) -> set[str]:
    """Every name this function binds -- assignment, for-target, with-target, comprehension, etc.

    Nested function and class definitions are NOT descended into: they have their own scope, and a
    name bound inside one does not make the outer function's name local.
    """
    out: set[str] = set()

    def walk(node, top=False):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if not top:
                    continue
                out.add(child.name)          # a nested def DOES bind its own name in this scope
                continue
            if isinstance(child, ast.Lambda):
                continue
            if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Store):
                out.add(child.id)
            elif isinstance(child, ast.arg):
                out.add(child.arg)
            elif isinstance(child, (ast.Global, ast.Nonlocal)):
                out.difference_update(child.names)
            walk(child)

    walk(fn, top=True)
    for name in getattr(fn, "_globals", ()):  # pragma: no cover - defensive
        out.discard(name)
    return out


def _declared_global(fn: ast.AST) -> set[str]:
    out: set[str] = set()
    for node in ast.walk(fn):
        if isinstance(node, ast.Global):
            out.update(node.names)
    return out


def _called_names(fn: ast.AST) -> set[str]:
    out: set[str] = set()
    for node in ast.walk(fn):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            out.add(node.func.id)
    return out


def test_no_local_shadows_a_module_function_it_calls():
    offenders = []
    for path in sorted(CODE.rglob("*.py")):
        if any(part in path.parts for part in (".lake", "__pycache__", "tests")):
            continue
        try:
            tree = ast.parse(path.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        module_fns = {n.name for n in tree.body
                      if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))}
        if not module_fns:
            continue
        for node in tree.body:
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            bound = _assigned_names(node) - _declared_global(node)
            # a name it CALLS, that the module defines, and that it also binds locally
            clash = (bound & module_fns & _called_names(node)) - {node.name}
            for name in sorted(clash):
                offenders.append(
                    f"{path.relative_to(REPO)}: {node.name}() calls `{name}()` but also binds "
                    f"`{name}` locally -- the call is an UnboundLocalError")
    assert not offenders, (
        "a local binding shadows a module-level function the same function calls:\n  "
        + "\n  ".join(offenders)
        + "\n\nRename the local. Python decides scope per function, so binding the name anywhere in "
          "the function makes every use of it local, including uses that come earlier.")
