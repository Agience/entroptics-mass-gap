"""
entroptics_adapter.py -- the reader: a strongly-typed domain adapter over the entroptics library.

The library does ALL the processing. You feed it RAW N-D configurations and read a
named, typed value. The ONE job of this wrapper is to hand each library read the
reduction that PRESERVES the structure that read needs, so nothing is destroyed by a
bare reshape. The library is strictly 2-D, so an N-D field must be reduced first; the
reduction is chosen PER READ (entroptics.fields):

  * ORDERED reads (the gap Delta, decay a_delta, the DMD rates, phi_T, Strehl): the
    ordered axis is time and every off-axis site is POOLED as the feature/state vector
    of the one ordered process (fields.pool). The spatial field IS the DMD state, so
    pooling it is correct, not destructive.
  * TEMPORAL-SPECTRUM read (the leading temporal mode's coherence / attenuation,
    [E Sec 6]): time is the FEATURE axis and spatial sites are exchangeable SAMPLES of
    the time vector.
  * SPATIAL / FEATURE reads (the confinement K_signal, contrast, phi_F, focus): each
    2-D spatial plane is kept INTACT (fields.slabs) and the read is averaged over
    planes ([E Sec 8], PAPER Sec 8.1). A bare flatten of the spatial volume into one
    feature axis destroys the within-plane correlation and inverts the order
    parameter, so it is never used for a spatial read.

    from entroptics_adapter import run, confinement, aperture
    r = run(configs)             # configs: an iterable of raw N-D fields, last axis = time
    r.mass_gap                   # ORDERED: the gap = dominant Koopman/DMD mode rate -log|mu_1| (forward operator read)
    r.temporal.attenuation_lo    # TEMPORAL: certified lower bound on the leading temporal mode
    confinement(config)          # SPATIAL: plane-averaged K_signal of one raw config

Optics-to-gap dictionary (each wrapper read maps to a named library read [E] and the
gap quantity it carries in PAPER Sec 3):
    r.mass_gap             <- Aperture.connected_decay_rate    [E Sec 9]  = Delta = -log|mu_1|, connected (forward operator read)
    r.temporal.attenuation <- attenuation_interval.attenuation[E Sec 6]  = leading-temporal-mode coherence
    r.temporal.*_lo/_hi    <- attenuation_interval (Weyl)     [E Lem 6.2]= certified coherence interval
    confinement()          <- Aperture.projection().K_signal  [E Sec 8]  = confinement order parameter
    r.contrast             <- Aperture.contrast               [E Sec 6]  = leading feature-mode coherence
    r.a_delta              <- Aperture.a_delta                [E Sec 4]  = diffraction-limit aperture (bore)
    r.optics.phi_T, ...    <- Aperture.optics()               [E Sec 3]  = fill / reach (band-limit)

"""
from __future__ import annotations

import importlib
import math
import os
import sys
from dataclasses import dataclass, fields
from pathlib import Path
from typing import Callable, Iterable

# The module is named `entroptics_adapter` so that it does not shadow the
# installed `entroptics` package — a plain import resolves the library directly, no sys.path shim.
_lib = importlib.import_module("entroptics")          # the installed public PyPI entroptics package
_lib_nulls = importlib.import_module("entroptics.null_providers")   # caller-suppliable floor nulls

# The reader version is set in one place -- the ``entroptics==`` line of research/requirements.txt,
# the file pip actually installs from -- and carries from there: this import check reads it, and so
# does the test suite (conftest imports REQUIRED_VERSION rather than writing the number again).
# The check is ">=", because what the pin protects is the CALL SURFACE: 0.2.1 renamed the per-frame
# projection (Screen -> Projection, Aperture.screen() -> Aperture.projection(), the "screen" floor
# cut -> "projection"), so an older reader has no Aperture.projection() at all and must fail here,
# at import and with a reason, rather than mid-read with a bare AttributeError. Read VALUES are
# unchanged across that rename; the suite warns separately when the installed version is not the
# pinned one, since that is the version the committed numbers were verified against.
_REQUIREMENTS = Path(__file__).resolve().parent.parent / "requirements.txt"


def _pinned_version() -> str:
    """The ``entroptics==X.Y.Z`` pin from research/requirements.txt -- the single source."""
    for line in _REQUIREMENTS.read_text(encoding="utf-8").splitlines():
        stmt = line.split("#", 1)[0].strip()
        if stmt.startswith("entroptics=="):
            return stmt[len("entroptics=="):].strip()
    raise ImportError(f"no 'entroptics==' pin found in {_REQUIREMENTS}")


def _version_tuple(v: str) -> tuple:
    return tuple(int(x) for x in v.split(".")[:3])


REQUIRED_VERSION = _pinned_version()        # e.g. "0.2.1" -- set in requirements.txt, not here

if _version_tuple(_lib.__version__) < _version_tuple(REQUIRED_VERSION):
    raise ImportError(
        f"entroptics {_lib.__version__} installed; this adapter needs >= {REQUIRED_VERSION} "
        f"(pinned in research/requirements.txt). The 0.2.1 release renamed Screen -> "
        "Projection: an older reader has no Aperture.projection() and no 'projection' floor "
        "cut.")

null_providers = _lib_nulls           # mp (default) / robust / reference_null / permutation() + plumbing
reference_null = _lib_nulls.reference_null                 # O(1) closed-form null from a signal-free reference
self_calibrating_null = _lib_nulls.self_calibrating_null   # reference_null calibrated LOCALLY on a region's own noise
by_kind = _lib.by_kind                # per-cut-point null routing: {projection|spectral|bulk: provider}
Aperture = _lib.Aperture              # the single front door: every read goes through it
slabs = _lib.slabs                    # geometry-preserving N-D reduction: keep each plane intact
over_planes = _lib.over_planes        # library-side fold of a 2-D read over intact planes
read_batch = _lib.read_batch          # batched monitor: fold+svdvals+floor over a plane STACK (bit-identical)
spectral_batch = _lib.spectral_batch  # batched correlation-eigvalsh over a plane STACK (bit-identical)
pool = _lib.pool                      # ordered reduction: off-axis sites as feature samples
SpectralAccumulator = _lib.SpectralAccumulator            # pool the feature correlation over planes
resolved_dimension_interval = _lib.resolved_dimension_interval  # certified resolved-mode count
attenuation_interval = _lib.attenuation_interval          # certified attenuation interval (Lem 6.2)
concentration_band = _lib.concentration_band              # Vershynin sample band for the interval
hankel_spectrum = _lib.hankel_spectrum    # reflection-positive MOMENT PENCIL: transfer spectrum of a corr. sequence
jackknife = _lib.jackknife                # generic delete-one(-bin) jackknife SE for reads w/o a closed-form interval
HankelSpectrum = _lib.HankelSpectrum      # the pencil result: .evals/.isolation/.psd/.leading/.rate

import numpy as np                                     # noqa: E402``


# ── backend helpers: a torch config stays ON its device (GPU) through the reductions;
# only the numpy-only certified accumulator materialises to numpy ─────────────────────
def _is_torch(x) -> bool:
    return type(x).__module__.split(".", 1)[0] == "torch"


def _asfloat(f):
    """A torch tensor stays on its device as float; anything else becomes a numpy float array."""
    if _is_torch(f):
        return f if f.dtype.is_floating_point else f.double()
    return np.asarray(f, dtype=float)


def _movedim(f, src, dst):
    return f.movedim(src, dst) if _is_torch(f) else np.moveaxis(f, src, dst)


def _to_np(f):
    return f.detach().cpu().numpy() if _is_torch(f) else np.asarray(f)


# ══════════════════════════════════════════════════════════════════════════════
# Typed read records
# ══════════════════════════════════════════════════════════════════════════════
@dataclass(frozen=True)
class Optics:
    """The full intrinsic optical read of one config (the library's canonical schema),
    averaged over configs. Each field is read through its CORRECT reduction: the
    ordered/decay fields (T axis) from the time-pooled projection, the feature/spectral/
    concentration fields (F axis) plane-averaged over intact spatial planes."""
    H_T: float; n_T: float; delta_T: float; phi_T: float; sigma_T: float
    H_F: float; n_F: float; delta_F: float; phi_F: float; sigma_F: float
    phi: float; magnification: float; etendue: float; space_bandwidth: float; strehl: float
    contrast: float; top_share: float; resolved_modes: float; noise_floor: float
    attenuation: float; phase: float; dispersion: float; resolved_power: float; dominance: float
    focus: float; intensity: float
    a_delta: float; a_delta_abbe: float; correlation_length: float; decay_entropy: float
    rayleigh_shape_factor: float; shape_factor: float; at_diffraction_limit: float

@dataclass(frozen=True)
class Dynamics:
    """Decay rates from the DMD/Koopman operator (spliced over all raw configs).
    ``mass_gap`` is read on the CONNECTED (mean-subtracted) spectrum: the slowest
    FLUCTUATION mode (the gap) of field data with a nonzero mean. ``decay_rates`` /
    ``frequencies`` are the full RAW operator spectrum (dominant-first)."""
    mass_gap: float                       # -log|mu_1| of the dominant (slowest) CONNECTED mode = the gap
    fast_rate: float                      # short_range: the fastest RAW decay rate
    decay_rates: tuple[float, ...]        # RAW spectrum: every alpha_k = -log|mu_k| (dominant-first)
    frequencies: tuple[float, ...]        # RAW spectrum: every beta_k = arg(mu_k)


@dataclass(frozen=True)
class Temporal:
    """The leading temporal mode's ATTENUATION alpha ([E Sec 6], Def 6.1), read with
    time as the feature axis and spatial sites as samples. It is the mass-gap paper's
    "coherence (leading temporal mode)" and moves OPPOSITE the gap (high when
    coherent/gapless, low when gapped). Fields mirror the library CertifiedInterval;
    this is the ATTENUATION, not the [E] SpectralOptics.dominance (lambda1-1)/(N-1)."""
    attenuation: float                    # attenuation alpha ([E, Sec 6])
    attenuation_lo: float                 # Weyl-certified lower bound ([E, Lem 6.2])
    attenuation_hi: float                 # Weyl-certified upper bound
    certified: float                      # fraction of configs with attenuation_lo > 0


@dataclass(frozen=True)
class ConfinementCertificate:
    """The pooled, Weyl-certified DISORDER read over the whole configuration ensemble (the
    confinement side; the ensemble-level Aperture bound). Built by pooling the feature
    correlation over INTACT spatial planes (``SpectralAccumulator`` fed by ``fields.slabs``,
    never a flatten), so the certified band tightens with the ensemble.

    ``attenuation`` is the mass-gap paper's vortex tension mu ([E, Sec 6], PAPER Sec 12): its
    Weyl-certified UPPER endpoint below the floor kappa_0 = (1/4)ln3 is the certified
    confinement inequality mu < kappa_0. The resolved-mode interval is the phase discriminator
    ([E, Def 8.2] analogue). Both read off ONE pooled spectrum. The kappa_0 comparison is
    PHYSICS, done by the caller (the run script), not by the read layer."""
    attenuation:    float   # mu = disorder attenuation alpha, nats (point read)
    attenuation_lo: float   # Weyl-certified lower endpoint
    attenuation_hi: float   # Weyl-certified upper endpoint (mu < kappa_0  <=>  this < kappa_0)
    resolved_modes: int     # resolved count above the reference-null floor (point)
    resolved_lo:    int     # certified minimum resolved count
    resolved_hi:    int     # certified maximum resolved count
    band:           float   # the Vershynin certified band (shrinks as the pooled N grows)
    n_samples:      int     # pooled sample count (rows) over the ensemble
    n_features:     int     # feature count (columns)


@dataclass(frozen=True)
class KSignalCertificate:
    """Concentration-certified ensemble mean of the confinement order parameter K_signal
    ([E, Def 8.2]), the read that separates the phases (confined low, Coulomb high). The
    per-config plane-averaged K_signal values are the independent samples; the certified
    interval is an empirical-Bernstein bound (Maurer-Pontil) on the ensemble mean, so its
    width shrinks as 1/sqrt(n_configs). A certified phase SEPARATION is two such intervals
    (confined vs a reference) that do not overlap; that is the ensemble-size-limited step."""
    mean:   float   # ensemble-mean K_signal over configs
    std:    float   # sample standard deviation across configs
    n:      int     # number of independent configs
    lo:     float   # certified lower endpoint (1 - delta)
    hi:     float   # certified upper endpoint
    delta:  float   # failure probability


# The optics fields grouped by which reduction reads them correctly. Ordered/decay
# fields are read on the time-pooled projection; feature/spectral/concentration fields are
# plane-averaged over intact spatial planes. etendue / space_bandwidth / shape_factor
# CROSS the two axes and are recomposed from the correctly-reduced pieces.
_ORDERED_FIELDS = ("H_T", "n_T", "delta_T", "phi_T", "sigma_T", "phi", "magnification",
                   "strehl", "a_delta", "a_delta_abbe", "correlation_length",
                   "decay_entropy", "rayleigh_shape_factor", "at_diffraction_limit")
_FEATURE_FIELDS = ("H_F", "n_F", "delta_F", "phi_F", "sigma_F", "contrast", "top_share",
                   "resolved_modes", "noise_floor", "attenuation", "phase", "dispersion",
                   "resolved_power", "dominance", "focus", "intensity")


# ══════════════════════════════════════════════════════════════════════════════
# Reductions of a raw N-D config -- one per read family (the library is strictly
# 2-D; each read gets the reduction that keeps its own structure intact)
# ══════════════════════════════════════════════════════════════════════════════
def _ordered(f: np.ndarray, ta: int) -> np.ndarray:
    """ORDERED reads (dynamics / decay / gap): time first, every off-axis site pooled
    as the feature/state vector of the one ordered process (== entroptics.fields.pool)."""
    return pool(_asfloat(f), ta)


def _temporal(f: np.ndarray, ta: int) -> np.ndarray:
    """TEMPORAL-SPECTRUM read: time as the FEATURE axis, off-axis sites as SAMPLES of
    the time vector (the leading temporal mode's coherence, [E Sec 6])."""
    f = _asfloat(f)
    return _movedim(f, ta, -1).reshape(-1, f.shape[ta])


def _plane_axes(ndim: int, ta: int):
    """The two axes that form each intact SPATIAL plane: the first two non-time axes
    (None if fewer than two exist, e.g. an already-2-D field)."""
    t = ta % ndim
    spatial = [ax for ax in range(ndim) if ax != t]
    return (spatial[0], spatial[1]) if len(spatial) >= 2 else None


def _spatial_planes(f: np.ndarray, ta: int):
    """Yield each intact 2-D spatial plane of a raw config (entroptics.fields.slabs),
    iterating the remaining spatial axes and time. Geometry-preserving: the within-
    plane spatial correlation the confinement read lives on is never flattened away.
    For an already-2-D field the field itself is the single plane."""
    f = _asfloat(f)
    pa = _plane_axes(f.ndim, ta)
    if pa is None:
        yield _movedim(f, ta % f.ndim, 0)
        return
    yield from slabs(f, pa)


def _plane_mean(f: np.ndarray, ta: int, read: Callable) -> float:
    """A scalar 2-D ``read`` folded over the intact spatial planes of ``f`` by the
    LIBRARY's geometry-preserving reduction (entroptics.fields.over_planes; [E Sec 8],
    PAPER Sec 8.1). The library keeps each plane intact and reduces -- we build no
    aggregation by hand. For an already-2-D field the field itself is the single plane."""
    f = _asfloat(f)
    pa = _plane_axes(f.ndim, ta)
    if pa is None:
        return float(read(_movedim(f, ta % f.ndim, 0)))
    return float(over_planes(f, pa, read=read, reduce="mean"))


_APERTURE_WINDOW = 128   # Aperture's default window minimum: a plane with <= this many rows is
                         # never window-truncated, so read_batch(full plane) == Aperture(p).projection().


def _plane_mean_batched(f, ta, *, batched_read, pick, orig) -> float:
    """Plane-mean of a 2-D read done in one batched pass over the intact spatial planes --
    BIT-IDENTICAL to ``_plane_mean(f, ta, orig)`` whenever each plane fits the Aperture window
    (no truncation).  ``batched_read(planes) -> per-plane records``; ``pick`` pulls the scalar
    (e.g. ``r.K_signal`` for ``read_batch``, ``r.contrast`` for ``spectral_batch``).  Falls back
    to the exact per-plane ``orig`` read for a single plane or tall planes (which ``Aperture``
    would window), so it can never diverge from the un-batched read."""
    f = _asfloat(f)
    pa = _plane_axes(f.ndim, ta)
    if pa is None:
        return float(orig(_movedim(f, ta % f.ndim, 0)))          # single plane -> keep windowed read
    planes = [np.asarray(_to_np(p), dtype=float) for p in slabs(f, pa)]
    if not planes:
        return float("nan")
    if any(int(p.shape[0]) > _APERTURE_WINDOW for p in planes):  # tall -> Aperture windows -> per-plane
        return float(over_planes(f, pa, read=orig, reduce="mean"))
    return float(np.mean([float(pick(r)) for r in batched_read(planes)]))


# ══════════════════════════════════════════════════════════════════════════════
# The pinned null reference
# ══════════════════════════════════════════════════════════════════════════════
# Every K_signal, contrast, resolved-mode and certified-mu floor here is measured against the
# calibrated null reference ([E] Def 8.2): an analytic, O(1), machine-precision null built from a
# signal-free, deeply-confined ensemble. It is a detection null, so deconfinement reads as the
# coherent mode standing above the confined floor. The library's own default is the
# i.i.d.-Gaussian ``mp`` edge; the wrapper uses the reference instead, because a physics floor
# measured against a Gaussian edge is measuring a different quantity.
#
# Pin once with ``pin_reference(confined_ensemble)``. A floor read with nothing pinned and no
# explicit ``null=`` raises at the point of measurement.
_PINNED_REFERENCE = None       # the signal-free reference planes (introspection)
_PINNED_PROVIDER = None        # the cached by_kind reference-null provider (projection+spectral+bulk)


def pin_reference(confined_configs: "Iterable | None" = None, *,
                  realisations: "Iterable | None" = None, far: float | None = None,
                  time_axis: int = -1, kboot: int = 40, seed: int = 0):
    """PIN the calibrated null-reference for every floor read of this wrapper (K_signal,
    contrast, resolved modes, the certified mu), from a deeply-confined reference ensemble
    ([E] Def 8.2). The reference is calibrated PER CUT POINT at the SAME granularity as the read
    it thresholds -- this is what makes the floor correct:

      * projection (per-plane K_signal): the whitened-projection top singular value of each
                   reference plane -> ``confined_reference_null`` (per-plane distribution).
      * spectral   (per-plane contrast / resolved_modes): each plane's top correlation eigenvalue
                   -> ``reference_null`` (per-plane distribution).
      * bulk       (the POOLED ensemble certificate): the POOLED top correlation eigenvalue's
                   SAMPLING band -> bootstrap-resample the reference planes, pool, take the pooled
                   top eigenvalue (``kboot`` draws) -> ``reference_null``. A per-plane value here
                   would inflate the floor (per-plane variance >> pooled variance) and bury every
                   signal; the pooled bootstrap is the matched detection floor (the certificate
                   read itself pools over the ensemble).

    All are the analytic O(1) reference null (``center + z(far)*scale``), sharpening to any ``far``.
    After this the wrapper uses only the reference null -- never the i.i.d.-Gaussian ``mp`` edge.
    Returns the pinned ``by_kind`` provider. ``seed`` makes the bulk bootstrap deterministic."""
    global _PINNED_REFERENCE, _PINNED_PROVIDER
    if realisations is not None:
        planes = [np.asarray(_to_np(r), dtype=float) for r in realisations]
        planes = [p for p in planes if p.ndim == 2 and int(p.shape[1]) >= 2]
    elif confined_configs is not None:
        planes = []
        for c in confined_configs:
            for p in _spatial_planes(_asfloat(c), time_axis):
                p = np.asarray(_to_np(p), dtype=float)
                if p.ndim == 2 and int(p.shape[1]) >= 2:
                    planes.append(p)
    else:
        raise ValueError("pin_reference needs confined_configs=... or realisations=...")
    if not planes:
        raise ValueError("pin_reference: no 2-D reference planes found in the reference ensemble")
    F = int(planes[0].shape[1])
    planes = [p for p in planes if int(p.shape[1]) == F]        # one feature count for the pooled bulk
    # projection + spectral cuts: PER-PLANE reference (the read is per-plane)
    projection_svs = np.asarray([float(Aperture(p).projection().S[0]) for p in planes], dtype=float)
    corr_vals = np.asarray([null_providers.top_spectrum_value(p, "spectral") for p in planes], dtype=float)
    # bulk cut: the POOLED top eigenvalue's SAMPLING band -- bootstrap over the reference planes
    rng = np.random.default_rng(seed); n = len(planes)
    bulk_tops = np.empty(int(kboot), dtype=float)
    for b in range(int(kboot)):
        acc = SpectralAccumulator(F)
        for i in rng.choice(n, size=n, replace=True):
            acc.add(planes[i])
        bulk_tops[b] = float(np.asarray(acc.spectral().eigenvalues)[0])
    _PINNED_REFERENCE = planes
    _PINNED_PROVIDER = by_kind(
        projection=confined_reference_null(projection_svs, far=far),
        spectral=null_providers.reference_null(corr_vals, far=far),
        bulk=null_providers.reference_null(bulk_tops, far=far))
    return _PINNED_PROVIDER


def unpin_reference() -> None:
    """Clear the pinned reference; floor reads then RAISE until one is pinned again."""
    global _PINNED_REFERENCE, _PINNED_PROVIDER
    _PINNED_REFERENCE = None
    _PINNED_PROVIDER = None


def pinned_reference():
    """The currently pinned reference planes, or ``None``."""
    return _PINNED_REFERENCE


def _provider_or_raise(null):
    """The provider to hand a FLOOR read: an explicit ``null`` overrides; else the pinned
    reference null; else RAISE -- this wrapper never silently falls back to the library's
    i.i.d.-Gaussian ``mp`` floor."""
    if null is not None:
        return null
    if _PINNED_PROVIDER is not None:
        return _PINNED_PROVIDER
    raise RuntimeError(
        "entroptics wrapper: no null-reference pinned. This wrapper NEVER defaults to the "
        "library's i.i.d.-Gaussian 'mp' floor for a physics read. Call "
        "entroptics.pin_reference(confined_ensemble) once (or pass an explicit null=) before "
        "any confinement / K_signal / contrast / optics read.")


# ══════════════════════════════════════════════════════════════════════════════
# The reader
# ══════════════════════════════════════════════════════════════════════════════
class Reads:
    """Named, typed physics reads of raw configurations. Feed an iterable of raw
    N-D fields (last axis = time); every property is a direct library read on raw
    data, each through the reduction that preserves its structure (see module docstring)."""

    def __init__(self, configs: Iterable[np.ndarray], *, time_axis: int = -1) -> None:
        self._cfgs: list = [_asfloat(c) for c in configs]
        if not self._cfgs:
            raise ValueError("run() needs at least one configuration")
        self._ta: int = time_axis
        self._dyn = None

    # ---- internals ----
    def _spliced(self):
        """The DMD/Koopman operator accumulated over ALL raw configs (time-ordered;
        the spatial field is the state vector, pooled -- NOT flattened away).

        The ensemble is streamed into one accumulator, each configuration ingested as its own run
        (``adjacent=False``: no transition pair spans two configurations, because the system never
        made that transition). One accumulator holds a single dense ``F x F`` pair; splicing one
        Aperture per configuration pairwise builds the same operator, bit-identical, but holds three
        such pairs at every merge.

        That distinction decides whether a read runs at all. ``F`` is the pooled spatial width and
        grows as ``L^3``: at L=32 it is 32768, so one operator is 24 GB (Pxx, Pyx, Pinv) and the
        pairwise splice peaked near 72 GB -- past the host, which is where two certifications were
        being OOM-killed. Streaming holds one.
        """
        if self._dyn is None:
            frames = [_ordered(f, self._ta) for f in self._cfgs]
            F = int(np.asarray(frames[0]).shape[1]) if not hasattr(frames[0], "device")                 else int(frames[0].shape[1])
            gib = F * F * 8 / 1024 ** 3
            try:
                whole = Aperture(frames[0])
                dyn = whole.dynamics()
                for c in frames[1:]:
                    dyn.update_block(c, adjacent=False)
            except MemoryError as e:
                raise MemoryError(
                    f'accumulating the Koopman operator over {len(frames)} configs needs a dense '
                    f'{F}x{F} state matrix -- {gib:.2f} GiB each, and the operator carries three '
                    f'(Pxx, Pyx, Pinv), so ~{3 * gib:.1f} GiB. F is the pooled spatial width of the '
                    f'configurations, fixed by the lattice size: read a smaller L, or run on a host '
                    f'with the memory. Reducing the config count does NOT help.'
                ) from e
            self._dyn = whole
        return self._dyn

    def _temporal_ci(self, f: np.ndarray):
        a = Aperture(_temporal(f, self._ta))
        n, F = int(a.W.shape[0]), int(a.W.shape[1])     # samples=space, features=time
        band = concentration_band(n, F)                  # Vershynin sample-count band (library primitive, no inline copy)
        return a.attenuation_interval(band)

    # ---- DYNAMICS (ORDERED; moves WITH the gap) ----
    @property
    def dynamics(self) -> Dynamics:
        sp = self._spliced()
        r = sp.rates()
        return Dynamics(mass_gap=float(sp.connected_decay_rate), fast_rate=float(r.short_range),
                        decay_rates=tuple(float(x) for x in np.asarray(r.alpha)),
                        frequencies=tuple(float(x) for x in np.asarray(r.beta)))

    @property
    def mass_gap(self) -> float:
        """Delta = the mass gap (PAPER Sec 3): the decay rate of the DOMINANT (slowest) mode of
        the ordered-axis Koopman/DMD operator, -log|mu_1|, spliced over all configs and read on
        the CONNECTED (mean-subtracted) dynamics -- the slowest FLUCTUATION mode about the vacuum.
        The FORWARD operator read -- identify the linear propagator from the trajectory and read
        its dominant rate, borrowing the classical dynamical-systems machinery and walking it
        forward, isolating the gap of a multi-mode signal. Deterministic in the operator
        eigenvalues. See [E] Sec 9, library ``Aperture.connected_decay_rate``."""
        return float(self._spliced().connected_decay_rate)

    # ---- TEMPORAL SPECTRUM (moves OPPOSITE the gap) ----
    @property
    def temporal(self) -> Temporal:
        cis = [self._temporal_ci(f) for f in self._cfgs]
        return Temporal(
            attenuation=float(np.mean([c.attenuation for c in cis])),
            attenuation_lo=float(np.mean([c.attenuation_lo for c in cis])),
            attenuation_hi=float(np.mean([c.attenuation_hi for c in cis])),
            certified=float(np.mean([1.0 if c.certified else 0.0 for c in cis])))

    @property
    def temporal_attenuation(self) -> float:
        return self.temporal.attenuation

    # ---- Spatial screen: each plane is read intact ----
    @property
    def confinement(self) -> float:
        """K_signal: resolved spatial modes above the pinned reference-null floor, read on each
        intact spatial plane and averaged over planes and configurations."""
        return float(np.mean([confinement(f, self._ta) for f in self._cfgs]))

    def _spectral_mean(self, attr: str) -> float:
        """Plane- and ensemble-mean of one feature-correlation-spectrum field (any
        ``SpectralOptics`` attribute).  Each config's intact spatial planes are read in a SINGLE
        batched ``spectral_batch`` pass -- BIT-IDENTICAL to the per-plane
        ``Aperture(p, null=prov).<attr>`` (``spectral_batch`` reuses the library's
        ``_spectral_from_cov``, so every field matches, not just ``contrast``) -- plane-averaged,
        then averaged over configs.  Floor = the PINNED reference null (never mp); raises if
        nothing is pinned.  The one place the correlation eigenspectrum is formed, shared by
        ``contrast`` / ``resolved_modes`` / ``attenuation`` / ``top_share`` / ``dispersion``."""
        prov = _provider_or_raise(None)
        return float(np.mean([_plane_mean_batched(
            f, self._ta,
            batched_read=lambda planes: spectral_batch(planes, null=prov),
            pick=lambda r: getattr(r, attr),
            orig=lambda p: getattr(Aperture(p, null=prov), attr)) for f in self._cfgs]))

    @property
    def contrast(self) -> float:
        """Dominant feature-mode COHERENCE lambda_1 / reference-null floor (>1 => structure
        above the confined vacuum). A coherence / correlation read, NOT the string tension:
        sigma is a nonlocal Wilson-loop quantity, absent from the local action-density
        spectrum. Use it for the confinement PATTERN, not as sqrt(sigma). Plane-averaged
        (feature read), then averaged over configs. Floor = the PINNED reference null (never
        mp); raises if no reference is pinned."""
        return self._spectral_mean("contrast")

    @property
    def resolved_modes(self) -> float:
        """Feature-correlation modes above the reference-null floor, plane- and ensemble-averaged
        -- the spatial resolved count from the CORRELATION spectrum (companion to ``confinement``,
        the K_signal from the projection SVD).  Free from the same batched spectral pass as ``contrast``."""
        return self._spectral_mean("resolved_modes")

    @property
    def attenuation(self) -> float:
        """Attenuation constant alpha = log(lambda_1 / max(lambda_2, floor)) of the dominant
        feature-correlation mode: the spectral gap of the leading mode above the next mode / floor,
        plane- and ensemble-averaged.  ~0 when gapless; grows as a coherent mode isolates."""
        return self._spectral_mean("attenuation")

    @property
    def top_share(self) -> float:
        """Fraction of the total correlation-eigenvalue mass in the dominant mode
        (lambda_1 / sum lambda), plane- and ensemble-averaged -- how concentrated the feature
        spectrum is."""
        return self._spectral_mean("top_share")

    @property
    def dispersion(self) -> float:
        """Spread (std) of the per-mode attenuation across the resolved feature modes, plane- and
        ensemble-averaged -- how the propagation constant varies mode-to-mode."""
        return self._spectral_mean("dispersion")

    # ---- SPATIAL SCREEN, certified over the ensemble (confinement) ----
    @property
    def confinement_certificate(self) -> ConfinementCertificate:
        """The disorder attenuation mu and the resolved count, with Weyl-certified intervals,
        POOLED over the whole ensemble on INTACT spatial planes (``SpectralAccumulator`` +
        ``fields.slabs``, no flatten). Confinement mu < kappa_0 is certified when
        ``attenuation_hi < kappa_0 = (1/4)ln3`` (the caller does the kappa_0 comparison). The
        pooling is the ensemble-level Aperture bound: the band shrinks as the ensemble grows."""
        prov = _provider_or_raise(None)
        acc = None
        for f in self._cfgs:
            for p in _spatial_planes(f, self._ta):
                p = np.asarray(_to_np(p), dtype=float)
                if p.ndim != 2 or int(p.shape[1]) < 2:
                    continue
                if acc is None:
                    acc = SpectralAccumulator(int(p.shape[1]))
                acc.add(p)
        if acc is None or acc.T < 3:
            raise ValueError("confinement_certificate needs at least one 2-D plane with >= 3 rows")
        sg = acc.spectral(null=prov)
        band = concentration_band(acc.T, acc.F)
        a = attenuation_interval(None, band=band, sg=sg)
        k = resolved_dimension_interval(None, band=band, sg=sg)
        return ConfinementCertificate(
            attenuation=float(a.attenuation), attenuation_lo=float(a.attenuation_lo),
            attenuation_hi=float(a.attenuation_hi), resolved_modes=int(k.resolved_modes),
            resolved_lo=int(k.resolved_lo), resolved_hi=int(k.resolved_hi),
            band=float(band), n_samples=int(acc.T), n_features=int(acc.F))

    def k_signal_certificate(self, delta: float = 0.05) -> KSignalCertificate:
        """Concentration-certified ensemble mean of the confinement order parameter K_signal
        ([E, Def 8.2]), the read that discriminates the phase. The per-config plane-averaged
        K_signal values are the independent samples; the interval is an empirical-Bernstein
        bound on the ensemble mean at confidence 1 - ``delta``. Its width scales as
        1/sqrt(n_configs), so a certified phase separation is an ensemble-size question."""
        vals = [confinement(f, self._ta) for f in self._cfgs]
        n = len(vals)
        m = float(np.mean(vals))
        if n < 2:
            return KSignalCertificate(m, 0.0, n, m, m, float(delta))
        v = float(np.var(vals, ddof=1))
        rng = float(max(vals) - min(vals))
        L = math.log(2.0 / float(delta))
        t = math.sqrt(2.0 * v * L / n) + 7.0 * rng * L / (3.0 * (n - 1))   # empirical Bernstein
        return KSignalCertificate(m, float(np.std(vals, ddof=1)), n, m - t, m + t, float(delta))

    # ---- ORDERED decay aperture ----
    @property
    def a_delta(self) -> float:
        """The diffraction-limit APERTURE the paper aligns the gap to ([E, Def 4.4],
        PAPER Sec 4): a_delta = 2^{-H} of the signal's own decay, the reciprocal
        aperture width, so Delta ~ a_delta. Read along the ORDERED axis (time pooled),
        so run(cfgs, time_axis=k) reads the aperture ACROSS axis k -- a spatial axis
        gives the TRANSVERSE (bore) aperture. Recovers the free-scalar gap (moves with
        mass); on the vacuum gauge action density it sits at the white value (the
        confinement aperture is not locally exposed; the gauge gap is the bore).
        Averaged over configs."""
        return float(np.mean([Aperture(_ordered(f, self._ta)).a_delta for f in self._cfgs]))

    # ---- ORDERED coherence (is there ordered structure along the time axis?) ----
    @property
    def coherence(self) -> float:
        """Ordered-axis (time) coherence z-score (closed-form permutation null, [E Sec 5])."""
        return float(np.mean([Aperture(_ordered(f, self._ta)).projection().coherence
                             for f in self._cfgs]))

    # ---- full intrinsic optics (EACH field via its correct reduction) ----
    @property
    def optics(self) -> Optics:
        names = [fld.name for fld in fields(Optics)]
        acc = {k: 0.0 for k in names}
        for f in self._cfgs:
            o = self._config_optics(f)
            for k in names:
                acc[k] += float(o[k])
        n = len(self._cfgs)
        return Optics(**{k: acc[k] / n for k in names})

    def _config_optics(self, f: np.ndarray) -> dict:
        """One config's optics, each field read through its correct reduction: the
        ordered/decay fields from the time-pooled projection, the feature/spectral/
        concentration fields plane-averaged over intact spatial planes, and the two
        cross-axis areas (etendue, space-bandwidth) plus shape_factor recomposed."""
        prov = _provider_or_raise(None)
        ordered = Aperture(_ordered(f, self._ta), null=prov).optics()
        planes = [Aperture(pl, null=prov).optics() for pl in _spatial_planes(f, self._ta)]

        def pmean(k):
            return float(np.mean([p[k] for p in planes])) if planes else float(ordered[k])

        out = {k: float(ordered[k]) for k in _ORDERED_FIELDS}
        for k in _FEATURE_FIELDS:
            out[k] = pmean(k)
        out["etendue"] = out["phi_F"] * out["phi_T"]                         # phi_F phi_T (cross axes)
        out["space_bandwidth"] = out["n_F"] * out["n_T"]                     # n_F n_T   (cross axes)
        out["shape_factor"] = (out["a_delta"] / out["phi_F"]) if out["phi_F"] > 0 else float("nan")
        return out


def run(configs: Iterable[np.ndarray], *, time_axis: int = -1) -> Reads:
    """Wrap raw configurations and read named, typed physics values (see Reads)."""
    return Reads(configs, time_axis=time_axis)


def aperture(field: np.ndarray, time_axis: int = -1):
    """The ORDERED (time-pooled) Aperture of one raw config -- for ordered / decay /
    dynamics reads (a_delta, rates, strehl, phi_T), where the spatial field is the
    state vector. For SPATIAL / feature reads (K_signal, contrast, phi_F) use
    confinement() / run(), which keep each spatial plane intact. Low-level; prefer run()."""
    return Aperture(_ordered(field, time_axis))


def confinement(field: np.ndarray, time_axis: int = -1, *, null=None, seed: int = 0) -> float:
    """Plane-averaged K_signal of one raw config: the resolved-mode count read on each
    INTACT 2-D spatial plane (entroptics.fields.slabs) and averaged over planes ([E Sec 8],
    PAPER Sec 8.1). The geometry-preserving spatial order parameter -- a bare flatten of
    the spatial volume would destroy the within-plane correlation and invert it.

    ``null`` overrides the floor provider for this read. With ``null=None`` the wrapper uses
    the PINNED reference null (``pin_reference(...)``): the confined-vacuum detection null
    ([E] Def 8.2), so deconfinement reads as the coherent mode above the confined floor. The
    wrapper does not fall back to the library's i.i.d.-Gaussian ``mp`` edge: a read with
    nothing pinned and ``null=None`` raises. Resampling nulls are deterministic per ``seed``."""
    prov = _provider_or_raise(null)
    return _plane_mean_batched(
        _asfloat(field), time_axis,
        batched_read=lambda planes: read_batch(planes, null=prov, seed=seed),
        pick=lambda r: r.K_signal,
        orig=lambda p: Aperture(p).projection(null=prov, seed=seed).K_signal)


def confined_top_singular_values(confined_configs, time_axis: int = -1) -> np.ndarray:
    """The top singular value of each confined-phase spatial-plane projection: the reference
    distribution the confined-reference null thresholds against. Same projection construction
    (whiten + fold) as the confinement read, so the floor is in the read's own units."""
    svs = []
    for c in confined_configs:
        for p in _spatial_planes(_asfloat(c), time_axis):
            p = np.asarray(_to_np(p), dtype=float)
            if p.ndim == 2 and int(p.shape[1]) >= 2:
                svs.append(float(Aperture(p).projection().S[0]))
    return np.asarray(svs, dtype=float)


def _norm_ppf(p: float) -> float:
    """Inverse standard-normal CDF (Acklam rational approximation): O(1), deterministic,
    |abs error| < 1.2e-9. Returns z with P(Z <= z) = p."""
    if p <= 0.0:
        return -math.inf
    if p >= 1.0:
        return math.inf
    a = (-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00)
    b = (-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01)
    c = (-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00)
    d = (7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
         3.754408661907416e+00)
    plow, phigh = 0.02425, 1.0 - 0.02425
    if p < plow:
        q = math.sqrt(-2.0 * math.log(p))
        return ((((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])
                / (((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1.0)))
    if p > phigh:
        q = math.sqrt(-2.0 * math.log(1.0 - p))
        return -((((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])
                 / (((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1.0)))
    q = p - 0.5; r = q * q
    return ((((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5]) * q
            / ((((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1.0)))


def _norm_isf(p: float) -> float:
    """Inverse survival: z with P(Z > z) = p (= -_norm_ppf(p)). O(1), deterministic."""
    return -_norm_ppf(p)


def confined_reference_null(confined_top_svs, *, far: float | None = None):
    """DETERMINISTIC O(1) confined-reference null: the physics null the mass-gap read OWNS
    ([E] Def 8.2, 'prewhiten from a signal-free window'). The confined vacuum's
    top-singular-value distribution is moment-matched to a closed form, so the floor is
    ``center + z(far)*scale`` -- a pure O(1) function of ``ctx.far`` with NO stored samples and
    NO resampling, sharpening ANALYTICALLY to any far (the normal quantile inverts to 1e-5+;
    no 1/far sample requirement). ``(center, scale)`` = mean/std of
    ``confined_top_singular_values(confined_ensemble)`` at the target (N,F) shape, calibrated
    ONCE offline. Detection null = the confined phase, so deconfinement reads as the coherent
    mode standing above it. The confined analogue of the ``mp`` edge (same closed form, the
    noise model calibrated on the confined vacuum instead of an i.i.d. bulk)."""
    sv = np.asarray(confined_top_svs, dtype=float)
    center = float(sv.mean()); scale = float(sv.std() + 1e-30)

    def _provider(ctx) -> float:
        f = ctx.far if far is None else far
        return center + _norm_isf(f) * scale
    _provider.__name__ = "confined_reference_null"
    _provider.center = center
    _provider.scale = scale
    return _provider


class ConfinedReferenceNull:
    """Stateful DETERMINISTIC O(1) sharpening confined-reference null. Maintains the running
    mean/variance of the confined vacuum's top singular value by Welford (O(1) per update),
    and floors at ``mean + z(far)*std`` (O(1) per call), sharpening ANALYTICALLY to any far via
    the normal quantile -- no 1/far sample-size requirement, unlike an empirical quantile.
    ``update(*confined_configs)`` grows the estimate in the dynamical (the streaming aperture
    calls it per frame, so the null tracks a drifting confined level online); ``far=None`` uses
    the read's ``ctx.far``, a value pins a target level. Memory and per-call cost are O(1)
    regardless of how much reference has been accumulated.

    ``forgetting`` (in (0, 1], default 1.0 = perfect memory / stationary) gives the reference a
    FADING memory: each update decays the accumulated weight first, so the floor tracks a DRIFTING
    confined level (effective sample ~1/(1-forgetting) recent values). Keep 1.0 for a globally
    homogeneous vacuum (the maximally-stable, most-sensitive floor -- the mass-gap regime); use
    < 1 to follow a slow drift. Mirrors the library's ``ReferenceNull(forgetting=...)``."""

    def __init__(self, confined_configs=None, *, far: float | None = None, time_axis: int = -1,
                 forgetting: float = 1.0):
        if not (0.0 < forgetting <= 1.0):
            raise ValueError(f"forgetting must be in (0, 1]; got {forgetting}")
        self._ta = time_axis
        self._far = far
        self._forget = float(forgetting)
        self._n = 0.0                                 # float: effective (possibly faded) sample weight
        self._mean = 0.0
        self._M2 = 0.0
        if confined_configs is not None:
            self.update(*confined_configs)

    def _push(self, x: float) -> None:                # fading-memory Welford, O(1) per sample + memory
        f = self._forget
        self._n = f * self._n + 1.0
        d = x - self._mean
        self._mean += d / self._n
        self._M2 = f * self._M2 + d * (x - self._mean)

    def update(self, *confined_configs) -> "ConfinedReferenceNull":
        for c in confined_configs:
            for s in confined_top_singular_values([c], self._ta):
                self._push(float(s))
        return self

    @property
    def n_reference(self) -> float:
        return self._n

    @property
    def center(self) -> float:
        return self._mean

    @property
    def scale(self) -> float:
        return (self._M2 / (self._n - 1.0)) ** 0.5 if self._n > 1.0 else float("inf")

    def __call__(self, ctx) -> float:
        if self._n < 2:
            return float("inf")                       # not enough reference yet -> resolve nothing
        f = ctx.far if self._far is None else self._far
        return self._mean + _norm_isf(f) * self.scale


def marginal_entropy(field: np.ndarray, time_axis: int = -1) -> float:
    """Plane-averaged Shannon entropy H = H_T + H_F of one raw config's power marginals
    ([E Sec 2]), read on each intact spatial plane and averaged. Its coupling derivative
    -dH/dbeta is the disorder response (free-energy curvature; PAPER Sec 8.4): the
    marginals concentrate as a coherent mode orders the field, so H drops sharply at a
    deconfinement transition and stays flat across a smooth crossover."""
    return _plane_mean(_asfloat(field), time_axis,
                       lambda p: float(Aperture(p).H_T + Aperture(p).H_F))
