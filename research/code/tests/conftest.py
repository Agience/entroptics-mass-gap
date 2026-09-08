"""Shared fixtures for the mass-gap code suite.

Puts ``research/code`` on the path so ``import entroptics`` resolves to the wrapper; the wrapper's
shim then imports the public PyPI ``entroptics`` package (``pip install entroptics==<pin>``). Small,
fast fixtures: the free scalar (a known gap) and tiny gauge lattices (validity, not physics).
"""
import sys
from pathlib import Path

import pytest

_CODE = Path(__file__).resolve().parent.parent          # research/code
sys.path.insert(0, str(_CODE))                          # `import entroptics` -> the wrapper (code first)

import lattice_generator as generator   # noqa: E402
import entroptics_adapter as entroptics   # noqa: E402  -- the wrapper (research/code is first on the path)

# Verifiability: the reads are pinned to a published Entroptics release. The version is set once,
# in research/requirements.txt, and reaches here through the wrapper that already enforces the
# floor at import -- no second copy of the number. That check is ">=" (the call surface); this one
# warns on ANY mismatch, because the committed reads were verified against exactly the pin.
_PIN = entroptics.REQUIRED_VERSION
try:
    from importlib.metadata import version as _pkgver
    if _pkgver("entroptics") != _PIN:
        import warnings
        warnings.warn(f"entroptics {_pkgver('entroptics')} installed; reads verified against "
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
