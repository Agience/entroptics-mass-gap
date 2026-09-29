"""Shared fixtures for the mass-gap code suite.

Puts ``research/code`` on the path so ``import entroptics`` resolves to the wrapper; the wrapper's
shim then imports the installed ``entroptics`` package (``pip install -r research/requirements.txt``). Small,
fast fixtures: the free scalar (a known gap) and tiny gauge lattices (validity, not physics).
"""
import sys
from pathlib import Path

import pytest

_CODE = Path(__file__).resolve().parent.parent          # research/code
sys.path.insert(0, str(_CODE))                          # `import entroptics` -> the wrapper (code first)

import lattice_generator as generator   # noqa: E402
import entroptics_adapter as entroptics   # noqa: E402  -- the wrapper (research/code is first on the path)

# Verifiability: the reads are pinned to one Entroptics release or commit. The pin is set once, in
# research/requirements.txt, and reaches here through the wrapper that already enforces the call
# surface at import -- no second copy of it. That check is a floor; this one warns on ANY mismatch,
# because the committed reads were verified against exactly the pin. A commit pin is compared with
# the commit pip recorded for the install (direct_url.json); an install from a directory or a wheel
# records none, and is reported as unconfirmed rather than passed.
_PIN = entroptics.REQUIRED_VERSION
try:
    import json as _json
    import warnings
    from importlib.metadata import distribution as _dist
    _d = _dist("entroptics")
    if entroptics.PIN_IS_COMMIT:
        _du = _json.loads(_d.read_text("direct_url.json") or "{}")
        _got = (_du.get("vcs_info") or {}).get("commit_id", "")
        if not (_got and (_got.startswith(_PIN) or _PIN.startswith(_got))):
            warnings.warn(f"entroptics installed from {_du.get('url', 'an index')} "
                          f"(commit {_got or 'not recorded'}); reads verified against commit "
                          f"{_PIN} (pip install -r research/requirements.txt)", stacklevel=2)
    elif _d.version != _PIN:
        warnings.warn(f"entroptics {_d.version} installed; reads verified against "
                      f"{_PIN} (pip install entroptics=={_PIN})", stacklevel=2)
except Exception:
    pass


@pytest.fixture
def free_configs():
    """A handful of free-scalar fields of mass 0.6 (exact gap E0 = arccosh(1 + m^2/2))."""
    return [generator.free_scalar((8, 8, 49), 0.6, seed=s) for s in range(12)]


@pytest.fixture
def su2_configs():
    """A few thermalised SU(2) action-density fields on a small coprime lattice."""
    return list(generator.stream((5, 5, 5, 16), 2.0, group="su2", n=3, therm=20, gap=3))


# ── pinned null-reference: the wrapper REQUIRES one for every floor read (K_signal / contrast /
#    certificate) -- it never falls back to the library's i.i.d. mp edge (see pin_reference).  A
#    certificate test must therefore pin a signal-free reference whose planes have the same
#    feature-count as the configs it reads.  These fixtures pin a SEPARATE same-type, same-shape
#    ensemble and unpin afterward. ──

@pytest.fixture
def pin_su2():
    """Pin a separate confined SU(2) reference (matching the (5,5,5,16) su2 configs' F=5 planes)."""
    entroptics.pin_reference(list(generator.stream((5, 5, 5, 16), 2.0, group="su2",
                                                    n=4, therm=20, gap=3, seed=99)))
    yield
    entroptics.unpin_reference()


@pytest.fixture
def pin_free():
    """Pin a separate free-scalar reference (matching the (8,8,49) free configs' F=8 planes)."""
    entroptics.pin_reference([generator.free_scalar((8, 8, 49), 0.6, seed=100 + s) for s in range(6)])
    yield
    entroptics.unpin_reference()
