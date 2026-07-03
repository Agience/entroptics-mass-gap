"""
entroptics.py -- the reader: a strongly-typed wrapper over the entroptics library.

The library does ALL the processing. You feed it RAW configurations and read a
named, typed value. ``run(configs)`` returns a ``Reads`` object whose every
property maps DIRECTLY to a library read, with the only two choices -- axis
orientation and splicing -- baked in here, once.

    from entroptics import run
    r = run(configs)             # configs: an iterable of raw N-D fields, last axis = time
    r.mass_gap                   # float  -- slowest DMD decay rate (spliced), moves WITH the gap
    r.temporal.dominance_lo      # float  -- certified lower bound on the leading temporal mode
    r.optics.a_delta             # float  -- any intrinsic optical read, averaged over configs

NEVER build a correlator / effective mass / fit / bias correction / projection
before a read. That is reverting to classic (see ../CLAUDE.md). Feed raw configs;
the mass gap is ``rates().long_range``; the spectral ``attenuation`` is coherence,
not the gap.

Named ``entroptics.py``, so it loads the real library through a shim to avoid
shadowing it.
"""
from __future__ import annotations

import importlib
import math
import os
import sys
from dataclasses import dataclass, fields
from typing import Iterable

_HERE = os.path.dirname(os.path.abspath(__file__))
_self = sys.modules.pop(__name__, None)
_saved = sys.path[:]
sys.path = [p for p in sys.path if os.path.abspath(p or os.getcwd()) != _HERE]
_lib = importlib.import_module("entroptics")          # the installed library
sys.path = _saved
if _self is not None:
    sys.modules[__name__] = _self

Aperture = _lib.Aperture

import numpy as np                                     # noqa: E402


# ══════════════════════════════════════════════════════════════════════════════
# Typed read records
# ══════════════════════════════════════════════════════════════════════════════
@dataclass(frozen=True)
class Optics:
    """The full intrinsic optical read of one screen (the library's canonical
    schema), averaged over configs; count fields become fractional averages."""
    H_T: float; n_T: float; delta_T: float; phi_T: float; sigma_T: float          # noqa: E702
    H_F: float; n_F: float; delta_F: float; phi_F: float; sigma_F: float          # noqa: E702
    phi: float; magnification: float; etendue: float; space_bandwidth: float; strehl: float  # noqa: E702
    contrast: float; top_share: float; resolved_modes: float; noise_floor: float  # noqa: E702
    attenuation: float; phase: float; dispersion: float; resolved_power: float; dominance: float  # noqa: E702
    focus: float; intensity: float                                               # noqa: E702
    a_delta: float; a_delta_abbe: float; correlation_length: float; decay_entropy: float  # noqa: E702
    gabor_product: float; shape_factor: float; at_diffraction_limit: float        # noqa: E702


@dataclass(frozen=True)
class Dynamics:
    """Exact per-mode decay rates from the DMD/Koopman operator (spliced over all
    raw configs). ``mass_gap`` is the slowest rate and moves WITH the gap."""
    mass_gap: float                       # long_range: the slowest decay rate = the gap
    fast_rate: float                      # short_range: the fastest decay rate
    decay_rates: tuple[float, ...]        # every alpha_k = -log|mu_k|
    frequencies: tuple[float, ...]        # every beta_k = arg(mu_k)


@dataclass(frozen=True)
class Temporal:
    """The leading temporal mode's contrast, read with time as the feature axis.
    It moves OPPOSITE the gap (high when coherent/gapless, low when gapped)."""
    dominance: float                      # attenuation alpha ([E, Sec 6])
    dominance_lo: float                   # Weyl-certified lower bound ([E, Lem 6.2])
    dominance_hi: float                   # Weyl-certified upper bound
    certified: float                      # fraction of configs with dominance_lo > 0


# ══════════════════════════════════════════════════════════════════════════════
# Orientations of a raw config (the sole "decision", made here once)
# ══════════════════════════════════════════════════════════════════════════════
def _time_ordered(f: np.ndarray, ta: int) -> np.ndarray:
    """(T=time, F=space): time is the ordered axis (dynamics / the gap)."""
    f = np.asarray(f, dtype=float)
    return np.moveaxis(f, ta, 0).reshape(f.shape[ta], -1)


def _time_feature(f: np.ndarray, ta: int) -> np.ndarray:
    """(samples=space, F=time): time is the feature axis (the temporal spectrum)."""
    f = np.asarray(f, dtype=float)
    return np.moveaxis(f, ta, -1).reshape(-1, f.shape[ta])


# ══════════════════════════════════════════════════════════════════════════════
# The reader
# ══════════════════════════════════════════════════════════════════════════════
class Reads:
    """Named, typed physics reads of raw configurations. Feed an iterable of raw
    N-D fields (last axis = time); every property is a direct library read on raw
    data. Axis orientation and splicing are decided here, once."""

    def __init__(self, configs: Iterable[np.ndarray], *, time_axis: int = -1) -> None:
        self._cfgs: list[np.ndarray] = [np.asarray(c, dtype=float) for c in configs]
        if not self._cfgs:
            raise ValueError("run() needs at least one configuration")
        self._ta: int = time_axis
        self._dyn = None

    # ---- internals ----
    def _spliced(self):
        """The DMD/Koopman operator accumulated over ALL raw configs (time-ordered)."""
        if self._dyn is None:
            aps = [Aperture(_time_ordered(f, self._ta)) for f in self._cfgs]
            whole = aps[0]
            for a in aps[1:]:
                whole = whole.splice(a, adjacent=False)
            self._dyn = whole
        return self._dyn

    def _temporal_ci(self, f: np.ndarray):
        a = Aperture(_time_feature(f, self._ta))
        n, F = int(a.W.shape[0]), int(a.W.shape[1])     # samples=space, features=time
        band = 2.0 * (math.sqrt(F / n) + F / n)          # Vershynin sample-count band
        return a.attenuation_interval(band)

    # ---- DYNAMICS (moves WITH the gap) ----
    @property
    def dynamics(self) -> Dynamics:
        r = self._spliced().rates()
        return Dynamics(mass_gap=float(r.long_range), fast_rate=float(r.short_range),
                        decay_rates=tuple(float(x) for x in np.asarray(r.alpha)),
                        frequencies=tuple(float(x) for x in np.asarray(r.beta)))

    @property
    def mass_gap(self) -> float:
        """Delta = the slowest DMD/Koopman decay rate, spliced over all raw configs."""
        return self.dynamics.mass_gap

    # ---- TEMPORAL SPECTRUM (moves OPPOSITE the gap) ----
    @property
    def temporal(self) -> Temporal:
        cis = [self._temporal_ci(f) for f in self._cfgs]
        return Temporal(
            dominance=float(np.mean([c.attenuation for c in cis])),
            dominance_lo=float(np.mean([c.attenuation_lo for c in cis])),
            dominance_hi=float(np.mean([c.attenuation_hi for c in cis])),
            certified=float(np.mean([1.0 if c.certified else 0.0 for c in cis])))

    @property
    def temporal_dominance(self) -> float:
        return self.temporal.dominance

    # ---- SPATIAL SCREEN ----
    @property
    def confinement(self) -> float:
        """K_signal: resolved spatial modes above the Marchenko-Pastur noise floor."""
        return float(np.mean([Aperture(_time_ordered(f, self._ta)).screen().K_signal
                             for f in self._cfgs]))

    @property
    def coherence(self) -> float:
        """Ordered-axis coherence z-score (closed-form permutation null)."""
        return float(np.mean([Aperture(_time_ordered(f, self._ta)).screen().coherence
                             for f in self._cfgs]))

    # ---- full intrinsic optics (averaged over configs, time-ordered) ----
    @property
    def optics(self) -> Optics:
        names = [fld.name for fld in fields(Optics)]
        acc = {k: 0.0 for k in names}
        for f in self._cfgs:
            o = Aperture(_time_ordered(f, self._ta)).optics()
            for k in names:
                acc[k] += float(o[k])
        n = len(self._cfgs)
        return Optics(**{k: acc[k] / n for k in names})


def run(configs: Iterable[np.ndarray], *, time_axis: int = -1) -> Reads:
    """Wrap raw configurations and read named, typed physics values (see Reads)."""
    return Reads(configs, time_axis=time_axis)


def aperture(field: np.ndarray, time_axis: int = -1):
    """The Aperture of a single raw config (time-ordered). Low-level; prefer run()."""
    return Aperture(_time_ordered(field, time_axis))
