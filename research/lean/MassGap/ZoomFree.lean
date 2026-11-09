import Mathlib
import MassGap.ScaleLightCone

/-!
# MassGap.ZoomFree — a single observer zoomed in sees a field that runs free

`ScaleLightCone` reads observers at different zooms, whose light cones are disjoint: it reaches every
reading of separated factors. A reading at coincident points sits inside one light cone common to all its
insertions, so scale separation says nothing about it. This module states the single-observer mechanism for
those readings: an observer zoomed in on one point sees, inside its own light cone, a field whose coupling
at the observer's scale `s` runs to zero (asymptotic freedom), so its readings are the free (Gaussian, Wick)
readings at the canonical size `s^{−d}`, dressed by powers of the running coupling `ḡ²(s)`. It is stated
twice: `ZoomInFree` (§3, by coincident-point cumulants) and the author's aperture form `ApertureSettles` (§6: a
number of connected modes per aperture, each with noise set by the running coupling), the mechanism of the
root `clayStatementOf_of_aperture`. Declarations are in the namespace `MassGap.ZoomFree`.

The templates are Bałaban's ultraviolet stability of four-dimensional Yang–Mills in finite volume (at each
scale an effective action that is the free one plus a perturbation small in the running coupling of that
scale) and the Gawędzki–Kupiainen and Feldman–Magnen–Rivasseau–Sénéor constructions of the Gross–Neveu
model, where the same scale-by-scale smallness of the running coupling, from `b₀ > 0`, controls every
coincident-point reading.

## 1. The running coupling at the observer's scale (proved)

* `runG b₀ u s = u / (1 + 2 b₀ u |log s|)`: the one-loop solution `1/ḡ²(s) = 1/u + 2 b₀ log(1/s)` of
  `μ dḡ²/dμ = −2 b₀ ḡ⁴` (`μ = 1/s`) with `ḡ²(1) = u`, read through `|log s|` as
  `MultiScaleAll.afLog` is.
* `runsFree_iff`: for `u > 0`, `RunsFree b₀ u` (positive on `(0, 1]` and `→ 0` as `s → 0⁺`) holds iff
  `b₀ > 0`. At `b₀ = 0` the coupling is constant; at `b₀ < 0` it has a pole at `s = e^{1/(2 b₀ u)} < 1`
  (the Landau pole).
* `tendsto_runG_mul_absLog`: at `b₀ > 0`, `ḡ²(s) |log s| → (2 b₀)⁻¹`, independent of `u`.
* `runG_rpow_neg_le`: `ḡ²(s)^{−a} ≤ Q (1 + |log s|)^{max(a, 0)}`: a power of the running coupling is a power
  of the logarithm, the factor `afLog` of the core. `le_inv_runG` is the lower comparison at `b₀ > 0`,
  `min(u⁻¹, 2 b₀)(1 + |log s|) ≤ 1/ḡ²(s)`: at `b₀ > 0` the dressing `ḡ²(s)^{−a}` and `afLog a s` bound
  each other.

## 2. Moments from cumulants at coincident points (proved)

* `abs_mom_le_of_cum_pow`: cumulants within `((|B| − 1)!)^r c^{|B|}` give moments within `(|B|!)^r c^{|B|}`
  (`r ≥ 1`; `ClusterRoute.abs_mom_le_of_cum` at `r = 1`, with `∑ xᵢ^r ≤ (∑ xᵢ)^r`). At coincident points:
  `abs_state_pow_le`, `|ν(Yⁿ)| ≤ (n!)^r cⁿ`.
* `state_coshC_le_of`: `ν(Y^{2m}) ≤ (2m)! σ^{2m}` at every `m` gives `ν(cosh(λY)) ≤ 1/(1 − λ²σ²)` at every
  rate `0 ≤ λ < 1/σ` (the partial sums of the cosh series increase to it uniformly by Dini's theorem, and the
  state is norm-continuous). `state_coshC_le` is the instance `λ = (2σ)⁻¹`, bound `4/3`: a choice; any
  `λσ < 1` serves, and the choice stays inside the proofs that use it.

## 3. The mechanism

`anom γ γP j` is the anomalous exponent of the channel `j` (`γᵢ` per monomial, `γP` for the plaquette
class); `wickIx j = ⌈d_j / 4⌉` is the free Wick index of a channel of dimension `d_j`: a composite of
dimension `d` is of degree at most `d/2` in the free field strength (dimension `2`), and a Wick monomial of
degree `m` in a Gaussian field has cumulants of order `n` growing as `(n!)^{m/2}` (argued, Isserlis).

**`ZoomInFreeAt b₀ z b Wf`**: one `u > 0` (the running coupling at `s = 1`) and anomalous exponents `γ`, `γP`
with

* (chan, every zoom) every channel `j` has one `σⱼ > 0` such that at every scale `0 < s ≤ b` and every order
  `n`, eventually in the step, the coincident-point cumulant of `n` copies of the flowed channel obeys the
  free Wick count at the canonical size dressed by the running coupling:
  `|κ_k(B)| ≤ ((|B| − 1)!)^{wickIx j} (σⱼ ḡ²(s)^{−aⱼ} / s^{d_j})^{|B|}`;
* (obs, the observer's own scale `b`) one `σP > 0`, `E`: eventually in the step, at every plaquette, the
  flowed plaquette mean is `|ν_k(O ∘ V_b)| ≤ E a_k⁴` (its physical value is finite: the free value times
  `ḡ²(b)`, Lüscher's `t²⟨E(t)⟩`, argued), and the cumulants of every order obey the Wick count of the
  degree-two density, `|κ_k(B)| ≤ (|B| − 1)! σP^{|B|}`;
* (af, the zoom into a pair) a two-point kernel `G` of the trace at `z` whose reading settles onto the free
  (tree) value times the square of the running coupling: `r⁸ G(r) / (trTree N · ḡ²(r)²) → 1` as `r → 0⁺`,
  with `trTree N = 48 (N² − 1)/π⁴` the tree value of `r⁸⟨g²F²(x) g²F²(0)⟩/g⁴`.

**`ZoomInFree z b Wf = ZoomInFreeAt (b0 N) z b Wf`**, at the one-loop coefficient of `SU(N)`.

## 4. The derivations (proved)

* `scaleControlChan_of_zoomFree`: `ZoomInFreeAt b₀ z b Wf`, `b₀ ≥ 0`, `b > 0` give
  `ClusterRoute.ScaleControlChan b Wf`, at the exponents `max(γᵢ, 0)`, `max(γP, 0)`, the index
  `max(wickIx j, 1)` per channel and `K = 1`; the plaquette class at `b` from the obs clause with rate
  `μ = (2σP)⁻¹` and constant `e^{μE} · 2 · 4/3` (both a choice inside the proof: `ScaleControlChan` asks for
  some rate and constant).
* `afCoefficient_of_settles`: at `N ≥ 2`, the settling kernel has `ClayStatement.AFCoefficient N G`:
  `r⁸ G(r) log² r = [r⁸ G / (trTree ḡ⁴)] · trTree · (ḡ² |log r|)² → trTree / (4 b₀²) = afConst N`.
  The coupling `u` drops out of the limit; the coefficient is the one-loop factor of the free value.
  `afSettles_iff_afCoefficient` is the converse: at `N ≥ 2` and `u > 0` the af clause is equivalent to
  `AFCoefficient N G`.
* `substrateCoreCL_of_zoomFree`: `ZoomInFree z b Wf`, `b > 0` and `Wf b = W` give
  `ClusterRoute.SubstrateCoreCL W z b Wf`: every field of the coincident-point core.

## 5. The tests

* No gap (proved shape, argued content). Every clause reads a single point, or a pair as `r → 0⁺`:
  `afSettles_congr` shows that the af clause depends only on the germ of `G` at `0⁺`, so it fixes no decay
  at large `r`; the gapless kernel `trTree N · ḡ²(r)² / r⁸` meets it with ratio `1` at every `r > 0`. The
  free massless field meets the chan and obs clauses with no mass (Gaussian Wick composites of a field of
  covariance `≍ s^{−2}` at flow scale `s`; argued), so the mechanism is ultraviolet only and holds without a
  gap.
* Asymptotic freedom is used. `runsFree_iff`: the observer's coupling runs to zero with no pole iff
  `b₀ > 0`; `afCoefficient_of_settles` reads the limit `(2 b₀)⁻¹` of `ḡ² |log r|`, and
  `runG_rpow_neg_le` (`b₀ ≥ 0`) turns the running-coupling dressing into the logarithms of the core. At
  `b₀ < 0` (`φ⁴₄`, QED: the coupling grows on zoom-in) the coupling has a pole at a finite zoom, the dressing
  `ḡ²(s)^{−a}` is not a power of `|log s|`, and the deviations from the canonical size are powers of `s`
  (argued); the mechanism is then the cautionary case of triviality, not a free ultraviolet limit.
* The rough tail. The chan clause has the order fixed before the step limit, where the floor of
  `BlFamCore.RoughTail` vanishes (`ObserverTowerPM.tendsto_roughFloor`); the obs clause gives an exponential
  moment only on the dimension-`4` plaquette class at `s = b`, which `RoughTail` (channels of dimension
  `4(n + 1) ≥ 8`) does not reach. So `RoughTail` refutes no clause (argued, as for `ScaleControlChan`,
  `ObserverTowerCL` §5); `ZoomInFree` does not give `ScaleControlAll`.
* What is new against the core. The af clause is equivalent to `AFCoefficient N G`
  (`afSettles_iff_afCoefficient`, at `N ≥ 2`, `u > 0`). The size dressing `ḡ²(s)^{−a}` is equivalent at
  `b₀ > 0` to the core's `afLog a s` up to constants (`runG_rpow_neg_le`, `le_inv_runG`). The obs clause is
  the cumulant (Wick) form of the plaquette exponential moment, near it in strength (argued). The one new
  content is the index pin: the chan clause fixes the Gevrey index to the free Wick index `⌈d/4⌉`, where the
  core lets every channel choose its index. The pin is argued: Isserlis gives `⌈d/4⌉` for a Wick monomial
  in a linear field `F`; at `g ≠ 0` the field strength has `A²` terms, so the composite is not a Wick
  monomial in a Gaussian field and the pin is an input, not a consequence of the free theory.

## 6. The aperture mechanism (the author's statement)

"The aperture and light cone block out what isn't visible, and the diffraction limit gives us what is
outside the aperture to 2x the wave length … as we zoom in, aperture shrinks relative, and fields settle with
less noise. But we can infer what's outside, so we can tell if what we're looking at is a thing or not."

**`ApertureSettlesAt b₀ z b Wf`** (and `ApertureSettles = ApertureSettlesAt (b0 N)`), on the real objects:

* (band limit) at aperture `s ∈ (0, b]` and every step, the connected flowed reading of channel `j` is the
  sum of `Mⱼ` modes, each connected: the modes longer than the aperture act as a constant offset across it
  and cancel in the connected reading. Lean has no long-wavelength shift on `Cfg N`; the lattice form of
  the invariance is that the reading and every mode are connected (`msFlow` subtracts the mean).
* (finite information) `Mⱼ ≥ 1` is one number, independent of the step and of the aperture: the intended
  reading is the Slepian–Landau–Pollak count `≍ (A W)^d` of an aperture `A` with band `W ≍ 1/A`
  (Nyquist–Shannon, Landau density), the same count at every zoom.
* (noise per mode) every mode's even moment of order `2p`, eventually in the step, is within the free Wick
  count at the canonical size times `ḡ²(s)^{κⱼ}`, the noise per mode at the aperture's running coupling;
  at the observer's aperture `b` the plaquette modes (fixed count `MP`) have every even moment within
  `(2m)! σP^{2m}` and the flowed plaquette mean is `O(a_k⁴)`.
* (af) the trace kernel settles onto the tree value times `ḡ²(r)²` (as in `ZoomInFreeAt`).

Proved: `state_pow_sum_le` (`ν((∑ᵢ eᵢ)^{2p}) ≤ M^{2p} maxᵢ ν(eᵢ^{2p})`, power mean);
`scaleControlChan_of_aperture` (per-channel moments at the index `wickIx j`, `K = 1`, rate
`(Mⱼ σⱼ Q)⁻¹`; the plaquette exponential moment at `b` by Jensen over the `MP` modes and `state_coshC_le` per
mode); `substrateCoreCL_of_aperture` (all of `SubstrateCoreCL`); `clayStatementOf_of_aperture`: the root
from `StrongEnd N`, `ZoomSettlesUV` and `CoreInputsAlongWAP` (the bundle with the copy of
`ApertureSettles`). Asymptotic freedom enters only as the noise per mode `ḡ²(s)^{κ}`
(`runG_rpow_neg_le`, `runsFree_iff`) and in the af clause.

The mode clauses as stated are equivalent to `M = 1` (`apertureSettlesAt_iff_one`): `M = 1` with
`e = msFlow` meets them (`msFlow` is centred, `state_msFlow`), and an `M`-mode witness at noise `σ` gives the
`M = 1` witness at noise `Mσ` (`state_pow_sum_le`); the same holds for `MP`. The modes are existential, so
the count is not a constraint, and `ApertureSettles` restates `SubstrateCoreCL` (through the moment form
`ApertureOneAt`) together with the argued Gevrey-index pin `⌈d/4⌉` (§5). A count that constrains has to be
read from the field, not chosen: `ApertureModes` measures it.

The rough tail (argued). `BlFamCore.not_scaleControlAll_of_roughTail` reads the exponential moment of a
channel of dimension `4(n + 1) ≥ 8` at rate `a_k^{−4(n+1)}`: one reading over every lattice mode of the read
set at once, the reading the fixed count excludes. `ApertureSettles` asks only fixed-order moments of those
channels, where the floor of `RoughTail` tends to `0` (`ObserverTowerPM.tendsto_roughFloor`), and one
exponential moment, of the dimension-`4` plaquette class at `b`. `RoughTail` at `n ≥ 1` refutes no clause;
at `n = 0` it would refute the obs clause, and the argued charge rate of a rough configuration,
`exp(−c (b/a_k)⁴ log(b/a_k))`, lies below every `exp(−L a_k^{−4})`, so it does not hold there
(`BlFamCore` §2). The escape is the fixed order; it is not proved that no observer has a rough tail at
`n = 0`.

Inference outside the aperture (not derived). The prolate-spheroidal extrapolation decides from in-band
data whether a localized object is present: a lower bound (a non-zero, non-Gaussian reading). `ProxyNondeg`,
`ProxyGenLimGerm` and `ThreePointAtScale` are such lower bounds; every clause of `ApertureSettles` is an
upper bound, and an upper bound cannot witness non-triviality, so these stay inputs. Their statement in
aperture terms (an in-band reading bounded below at the aperture) is the next single-observer step (argued).

## 7. The root and what remains, by kind

`clayStatementOf_of_zoomFree` reads `StrongEnd N`, `ScaleLightCone.ZoomSettlesUV` and the bundle
`CoreInputsAlongWZF`: `0 < b`, `Wf b = W`, the copy of `ZoomInFree`, `ExpandStrong`, `ZoomSettles`,
`FlowCovLim`, `FlowWard`, `ProxyNondeg`, the germ `ProxyGenLimGerm` and the three-point clause.

* Zoom-out: `StrongEnd N`; the base clause of `ZoomSettles` (the coarse observer at the first step).
* Zoom-in, separated observers: the suppression rates of `ZoomSettles`, `ZoomSettlesUV`; the rate clause of
  `ExpandStrong` (its `(s/d)^ε` compares the flow scale with the separation: two light cones).
* Zoom-in, single observer: `ZoomInFree` (this module): the per-channel moments, the plaquette exponential
  moment at `b` and `af` are derived from it. The coefficient matching inside `ExpandStrong` (the free OPE
  is exact, corrections in `ḡ²(s)`) is a single-observer reading not derived here (argued).
* Normalization and symmetry: `0 < b`, `Wf b = W`, the membership clause of `ExpandStrong` (a range
  condition), `FlowCovLim`, `FlowWard`.
* Inference outside the aperture (single observer, lower bounds): `ProxyNondeg`, the germ
  `ProxyGenLimGerm`, the three-point clause (§6).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower ends, the limit `0⁺` and the point approached; `1` the
coupling's reference scale `s = 1`, the least index, the limit of the settling ratio and the top of the
pole's scale; `2` the one-loop factor in `−2 b₀ ḡ⁴`, the square of the coupling, the even powers, the cosh
bound `e^{|y|} ≤ 2 cosh y` and the least colour count; `4` the plaquette dimension, the dimension of `F²` in
`⌈d/4⌉` (with `3` the ceiling offset), and `π⁴`; `8` the dimension pair `r⁸`; `48` the tree value; `1/2`,
`1/4`, `4/3` in `state_coshC_le` and in the proofs that use it: the chosen rate `λσ = 1/2` and its geometric
sum (a choice; `state_coshC_le_of` takes any `λσ < 1`); `1` the least mode count; `Mⱼ`, `MP` (the mode
counts), `u`, `γ`, `γP`, `σⱼ`, `σP`, `E`, `Q` existential; `b₀ = b0 N = 11N/(48π²)` the theory's one-loop
coefficient.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ZoomFree

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ScalePC MassGap.ScalePM
  MassGap.ClusterRoute MassGap.MeasuredSpacing
open MassGap.ScaleControlFull (zOne)

/-! ## 1. The running coupling at the observer's scale -/

section Running

/-- **The one-loop running coupling at scale `s`**: `ḡ²(s) = u / (1 + 2 b₀ u |log s|)`, `ḡ²(1) = u`.
DERIVED: `1` the reference scale; `2` the one-loop factor in `μ dḡ²/dμ = −2 b₀ ḡ⁴`. -/
def runG (b₀ u s : ℝ) : ℝ := u / (1 + 2 * b₀ * u * |Real.log s|)

/-- DERIVED: `0` the signs; `1`, `2` as in `runG`. -/
theorem runG_den_pos {b₀ u : ℝ} (hb : 0 ≤ b₀) (hu : 0 ≤ u) (s : ℝ) :
    0 < 1 + 2 * b₀ * u * |Real.log s| := by
  have := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hb) hu) (abs_nonneg (Real.log s))
  linarith

/-- DERIVED: `0` the signs. -/
theorem runG_pos {b₀ u : ℝ} (hb : 0 ≤ b₀) (hu : 0 < u) (s : ℝ) : 0 < runG b₀ u s :=
  div_pos hu (runG_den_pos hb hu.le s)

/-- **The coupling only decreases on zoom-in from its reference value**: `ḡ²(s) ≤ u`. DERIVED: `0` the
signs. -/
theorem runG_le {b₀ u : ℝ} (hb : 0 ≤ b₀) (hu : 0 < u) (s : ℝ) : runG b₀ u s ≤ u :=
  div_le_self hu.le (le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hb) hu.le) (abs_nonneg (Real.log s))))

/-- `1/ḡ²(s) ≤ (1/u + 2 b₀)(1 + |log s|)`. DERIVED: `1`, `2` as in `runG`; `0` the signs. -/
theorem inv_runG_le {b₀ u : ℝ} (hb : 0 ≤ b₀) (hu : 0 < u) (s : ℝ) :
    (runG b₀ u s)⁻¹ ≤ (u⁻¹ + 2 * b₀) * (1 + |Real.log s|) := by
  have hL := abs_nonneg (Real.log s)
  have hu' := hu.ne'
  have e : (runG b₀ u s)⁻¹ = u⁻¹ + 2 * b₀ * |Real.log s| := by
    unfold runG
    rw [inv_div]
    field_simp
  rw [e]
  have h1 : 0 ≤ u⁻¹ * |Real.log s| := mul_nonneg (inv_nonneg.2 hu.le) hL
  nlinarith

/-- **The lower comparison**: `min(u⁻¹, 2 b₀)(1 + |log s|) ≤ 1/ḡ²(s)` at `b₀ ≥ 0`, so at `b₀ > 0` a
power of the running coupling and a power of `1 + |log s|` bound each other. DERIVED: `1`, `2` as in `runG`; `0` the
signs. -/
theorem le_inv_runG {b₀ u : ℝ} (hb : 0 ≤ b₀) (hu : 0 < u) (s : ℝ) :
    min u⁻¹ (2 * b₀) * (1 + |Real.log s|) ≤ (runG b₀ u s)⁻¹ := by
  have hL := abs_nonneg (Real.log s)
  have e : (runG b₀ u s)⁻¹ = u⁻¹ + 2 * b₀ * |Real.log s| := by
    have hu' := hu.ne'
    unfold runG
    rw [inv_div]
    field_simp
  rw [e, mul_add, mul_one]
  have h1 := min_le_left u⁻¹ (2 * b₀)
  have h2 := min_le_right u⁻¹ (2 * b₀)
  have h3 : min u⁻¹ (2 * b₀) * |Real.log s| ≤ 2 * b₀ * |Real.log s| := mul_le_mul_of_nonneg_right h2 hL
  linarith

/-- **A power of the running coupling is a power of the logarithm**: for every `a` there is `Q > 0` with
`ḡ²(s)^{−a} ≤ Q (1 + |log s|)^{max(a, 0)}` at every `s`. DERIVED: `0` the signs and the floor of the
exponent. -/
theorem runG_rpow_neg_le {b₀ u : ℝ} (hb : 0 ≤ b₀) (hu : 0 < u) (a : ℝ) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ s : ℝ, runG b₀ u s ^ (-a) ≤ Q * afLog (max a 0) s := by
  rcases le_or_gt 0 a with ha | ha
  · have hU : 0 < u⁻¹ + 2 * b₀ := by have := inv_pos.2 hu; linarith
    refine ⟨(u⁻¹ + 2 * b₀) ^ a, Real.rpow_pos_of_pos hU a, fun s => ?_⟩
    have hg := runG_pos hb hu s
    have h1 : (0 : ℝ) ≤ 1 + |Real.log s| := by positivity
    rw [max_eq_left ha, afLog, Real.rpow_neg hg.le, ← Real.inv_rpow hg.le,
      ← Real.mul_rpow hU.le h1]
    exact Real.rpow_le_rpow (inv_nonneg.2 hg.le) (inv_runG_le hb hu s) ha
  · refine ⟨u ^ (-a), Real.rpow_pos_of_pos hu _, fun s => ?_⟩
    rw [max_eq_right ha.le, afLog, Real.rpow_zero, mul_one]
    exact Real.rpow_le_rpow (runG_pos hb hu s).le (runG_le hb hu s) (by linarith)

/-- `|log s| → ∞` as `s → 0⁺`. DERIVED: `0` the point approached. -/
theorem tendsto_absLog : Tendsto (fun s : ℝ => |Real.log s|) (𝓝[>] 0) atTop :=
  tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

/-- **The coupling runs to zero on zoom-in** at `b₀ > 0`. DERIVED: `0` the point approached and the limit;
`1`, `2` as in `runG`. -/
theorem tendsto_runG_zero {b₀ u : ℝ} (hb : 0 < b₀) (hu : 0 < u) :
    Tendsto (runG b₀ u) (𝓝[>] 0) (𝓝 0) := by
  have hD : Tendsto (fun s : ℝ => 1 + 2 * b₀ * u * |Real.log s|) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_absLog.const_mul_atTop (mul_pos (mul_pos two_pos hb) hu))
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => u) (𝓝[>] 0) (𝓝 u)).div_atTop hD

/-- **`ḡ²(s) |log s| → (2 b₀)⁻¹`** at `b₀ > 0`, whatever `u > 0`. DERIVED: `0` the point approached;
`2` the one-loop factor. -/
theorem tendsto_runG_mul_absLog {b₀ u : ℝ} (hb : 0 < b₀) (hu : 0 < u) :
    Tendsto (fun s => runG b₀ u s * |Real.log s|) (𝓝[>] 0) (𝓝 (2 * b₀)⁻¹) := by
  have h1 : Tendsto (fun s : ℝ => ((u * |Real.log s|)⁻¹ + 2 * b₀)⁻¹) (𝓝[>] 0) (𝓝 (0 + 2 * b₀)⁻¹) :=
    ((tendsto_inv_atTop_zero.comp (tendsto_absLog.const_mul_atTop hu)).add_const (2 * b₀)).inv₀
      (by linarith)
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [tendsto_absLog.eventually_gt_atTop 0] with s hs
  have hD := (runG_den_pos hb.le hu.le s).ne'
  have hs' := hs.ne'
  have hu' := hu.ne'
  unfold runG
  field_simp

/-- **The observer's coupling runs free**: positive on `(0, 1]` and `→ 0` as `s → 0⁺`. DERIVED: `0` the
signs and the limit; `1` the reference scale. -/
def RunsFree (b₀ u : ℝ) : Prop :=
  0 < u ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → 0 < runG b₀ u s) ∧ Tendsto (runG b₀ u) (𝓝[>] 0) (𝓝 0)

/-- **Asymptotic freedom is exactly what makes the zoom-in run free**: for `u > 0`, `RunsFree b₀ u ↔ 0 < b₀`.
At `b₀ = 0` the coupling is constant; at `b₀ < 0` it has a pole at `s = e^{1/(2 b₀ u)} ∈ (0, 1)`.
DERIVED: `0` the signs; `1`, `2` as in `runG`. -/
theorem runsFree_iff {b₀ u : ℝ} (hu : 0 < u) : RunsFree b₀ u ↔ 0 < b₀ := by
  constructor
  · rintro ⟨-, hpos, hlim⟩
    refine lt_of_not_ge fun hb => ?_
    rcases hb.lt_or_eq with hb | hb
    · have hbu : 2 * b₀ * u < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg two_pos hb) hu
      have hneg : 1 / (2 * b₀ * u) < 0 := one_div_neg.2 hbu
      have h1 : Real.exp (1 / (2 * b₀ * u)) ≤ 1 :=
        (Real.exp_le_exp.2 hneg.le).trans_eq Real.exp_zero
      have h0 := hpos _ (Real.exp_pos _) h1
      have hden : 1 + 2 * b₀ * u * |Real.log (Real.exp (1 / (2 * b₀ * u)))| = 0 := by
        rw [Real.log_exp, abs_of_neg hneg, mul_neg, mul_one_div_cancel hbu.ne]
        norm_num
      unfold runG at h0
      rw [hden, div_zero] at h0
      exact lt_irrefl _ h0
    · subst hb
      have hc : runG 0 u = fun _ => u := by
        funext s
        simp [runG]
      rw [hc] at hlim
      exact hu.ne' (tendsto_nhds_unique tendsto_const_nhds hlim)
  · intro hb
    exact ⟨hu, fun s _ _ => runG_pos hb.le hu s, tendsto_runG_zero hb hu⟩

end Running

/-! ## 2. Moments from cumulants at coincident points -/

section Moments

/-- `∑ xᵢ^r ≤ (∑ xᵢ)^r` for `xᵢ ≥ 0`, `r ≥ 1`. DERIVED: `1` the least power; `0` the signs. -/
theorem zf_sum_pow_le {α : Type*} (E : Finset α) (x : α → ℝ) (hx : ∀ a, 0 ≤ x a) {r : ℕ} (hr : 1 ≤ r) :
    ∑ a ∈ E, x a ^ r ≤ (∑ a ∈ E, x a) ^ r := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  calc ∑ a ∈ E, x a ^ (q + 1) = ∑ a ∈ E, x a ^ q * x a := by simp only [pow_succ]
    _ ≤ ∑ a ∈ E, (∑ b ∈ E, x b) ^ q * x a := Finset.sum_le_sum fun a ha =>
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx a)
          (Finset.single_le_sum (fun b _ => hx b) ha) q) (hx a)
    _ = (∑ b ∈ E, x b) ^ (q + 1) := by rw [← Finset.mul_sum, pow_succ]

/-- **Cumulants with `((|B| − 1)!)^r` growth give moments with `(|B|!)^r` growth**, `r ≥ 1`
(`ClusterRoute.abs_mom_le_of_cum` at `r = 1`). DERIVED: `1` the empty moment, the block offset and the least
index; `0` the signs. -/
theorem abs_mom_le_of_cum_pow {ι : Type*} [LinearOrder ι] (m : Finset ι → ℝ) (h0 : m ∅ = 1) {r : ℕ}
    (hr : 1 ≤ r) {c : ℝ} (hc : 0 ≤ c)
    (hcum : ∀ B : Finset ι, B.Nonempty → |cum m B| ≤ ((B.card - 1).factorial : ℝ) ^ r * c ^ B.card) :
    ∀ B : Finset ι, |m B| ≤ (B.card.factorial : ℝ) ^ r * c ^ B.card := by
  intro B
  induction B using Finset.strongInduction with
  | H B ih =>
    rcases B.eq_empty_or_nonempty with rfl | h
    · simp [h0]
    · rw [mom_eq_sum_cum m h0 h]
      have hi0B : B.min' h ∈ B := Finset.min'_mem B h
      have hcardB : (B.erase (B.min' h)).card + 1 = B.card := Finset.card_erase_add_one hi0B
      have hterm : ∀ A ∈ (B.erase (B.min' h)).powerset,
          |cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A)|
            ≤ c ^ B.card
              * ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) ^ r := by
        intro A hA
        rw [Finset.mem_powerset] at hA
        have hi0A : B.min' h ∉ A := fun hm => Finset.notMem_erase (B.min' h) B (hA hm)
        have hAc : A.card ≤ (B.erase (B.min' h)).card := Finset.card_le_card hA
        have hsdc : (B.erase (B.min' h) \ A).card = (B.erase (B.min' h)).card - A.card := by
          have := Finset.card_sdiff_add_card_eq_card hA
          omega
        have hss : B.erase (B.min' h) \ A ⊂ B := by
          refine (Finset.ssubset_iff_of_subset
            ((Finset.sdiff_subset).trans (Finset.erase_subset _ _))).2 ⟨B.min' h, hi0B, ?_⟩
          intro hm
          exact Finset.notMem_erase (B.min' h) B (Finset.sdiff_subset hm)
        have hc1 := hcum (insert (B.min' h) A) (Finset.insert_nonempty _ _)
        rw [Finset.card_insert_of_notMem hi0A, Nat.add_sub_cancel] at hc1
        have hm1 := ih _ hss
        rw [hsdc] at hm1
        have hC : c ^ (A.card + 1) * c ^ ((B.erase (B.min' h)).card - A.card) = c ^ B.card := by
          rw [← pow_add]
          congr 1
          omega
        have hR0 : 0 ≤ (A.card.factorial : ℝ) ^ r * c ^ (A.card + 1) :=
          mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hc _)
        rw [abs_mul]
        calc |cum m (insert (B.min' h) A)| * |m (B.erase (B.min' h) \ A)|
            ≤ ((A.card.factorial : ℝ) ^ r * c ^ (A.card + 1))
              * ((((B.erase (B.min' h)).card - A.card).factorial : ℝ) ^ r
                * c ^ ((B.erase (B.min' h)).card - A.card)) :=
              mul_le_mul hc1 hm1 (abs_nonneg _) hR0
          _ = c ^ B.card
              * ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) ^ r := by
              rw [← hC, mul_pow]
              ring
      have hx : ∀ A : Finset ι,
          0 ≤ (A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ) :=
        fun A => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      calc |∑ A ∈ (B.erase (B.min' h)).powerset,
            cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A)|
          ≤ ∑ A ∈ (B.erase (B.min' h)).powerset,
            |cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ A ∈ (B.erase (B.min' h)).powerset, c ^ B.card
              * ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) ^ r :=
            Finset.sum_le_sum hterm
        _ = c ^ B.card * ∑ A ∈ (B.erase (B.min' h)).powerset,
              ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) ^ r :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ c ^ B.card * (∑ A ∈ (B.erase (B.min' h)).powerset,
              ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ))) ^ r :=
            mul_le_mul_of_nonneg_left (zf_sum_pow_le _ _ hx hr) (pow_nonneg hc _)
        _ = (B.card.factorial : ℝ) ^ r * c ^ B.card := by
            rw [sum_powerset_fact, hcardB]
            ring

/-- The moments of `n` copies of one observable: `B = univ` is `ν(Yⁿ)`. DERIVED: no numeral. -/
theorem stMom_const_univ {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    (Y : C(X, ℝ)) (n : ℕ) : stMom ν (fun _ : Fin n => Y) Finset.univ = ν (Y ^ n) := by
  rw [stMom, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **A coincident-point moment from the cumulants of its copies**: `|ν(Yⁿ)| ≤ (n!)^r cⁿ`. DERIVED: `1` the
least index; `0` the sign. -/
theorem abs_state_pow_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    (Y : C(X, ℝ)) {r : ℕ} (hr : 1 ≤ r) {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (hcum : ∀ B : Finset (Fin n), B.Nonempty →
      |cum (stMom ν (fun _ : Fin n => Y)) B| ≤ ((B.card - 1).factorial : ℝ) ^ r * c ^ B.card) :
    |ν (Y ^ n)| ≤ (n.factorial : ℝ) ^ r * c ^ n := by
  have h := abs_mom_le_of_cum_pow (stMom ν (fun _ : Fin n => Y)) (stMom_empty ν _) hr hc hcum Finset.univ
  rwa [stMom_const_univ, Finset.card_univ, Fintype.card_fin] at h

/-- The pointwise `cosh` of a continuous function. DERIVED: no numeral. -/
def coshC {X : Type*} [TopologicalSpace X] (G : C(X, ℝ)) : C(X, ℝ) :=
  (⟨Real.cosh, Real.continuous_cosh⟩ : C(ℝ, ℝ)).comp G

/-- **The cosh moment from the even moments, at every rate below `1/σ`**: `ν(Y^{2m}) ≤ (2m)! σ^{2m}` at
every `m` gives `ν(cosh(λY)) ≤ 1/(1 − (λσ)²)` for `0 ≤ λ`, `λσ < 1`. The partial sums of the cosh series
increase to it, uniformly by Dini's theorem, and the state is norm-continuous. DERIVED: `2` the even powers;
`1` the geometric sum `∑ q^m ≤ 1/(1 − q)`; `0` the signs. -/
theorem state_coshC_le_of {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    (Y : C(X, ℝ)) {σ l : ℝ} (hσ : 0 ≤ σ) (hl0 : 0 ≤ l) (hlσ1 : l * σ < 1)
    (hmom : ∀ m : ℕ, ν (Y ^ (2 * m)) ≤ ((2 * m).factorial : ℝ) * σ ^ (2 * m)) :
    ν (coshC (l • Y)) ≤ 1 / (1 - (l * σ) ^ 2) := by
  have hq0 : 0 ≤ (l * σ) ^ 2 := sq_nonneg _
  have hq1 : (l * σ) ^ 2 < 1 := by
    have := mul_nonneg hl0 hσ
    nlinarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → C(X, ℝ),
      S = fun M => ∑ m ∈ Finset.range M, (l ^ (2 * m) / ((2 * m).factorial : ℝ)) • Y ^ (2 * m) :=
    ⟨_, rfl⟩
  have hSapp : ∀ M x, S M x = ∑ m ∈ Finset.range M, (l * Y x) ^ (2 * m) / ((2 * m).factorial : ℝ) := by
    intro M x
    rw [hSdef]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.pow_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]
    ring
  have hmono : Monotone S := by
    refine monotone_nat_of_le_succ fun M => ContinuousMap.le_def.2 fun x => ?_
    rw [hSapp, hSapp, Finset.sum_range_succ]
    have : 0 ≤ (l * Y x) ^ (2 * M) / ((2 * M).factorial : ℝ) :=
      div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (Nat.cast_nonneg _)
    linarith
  have hpt : ∀ x, Tendsto (fun M => S M x) atTop (𝓝 (coshC (l • Y) x)) := by
    intro x
    have e1 : coshC (l • Y) x = Real.cosh (l * Y x) := rfl
    rw [e1]
    exact (Real.hasSum_cosh (l * Y x)).tendsto_sum_nat.congr fun M => (hSapp M x).symm
  have hS := ContinuousMap.tendsto_of_monotone_of_pointwise hmono hpt
  have hν := (ν.continuous.tendsto (coshC (l • Y))).comp hS
  refine le_of_tendsto' hν fun M => ?_
  show ν (S M) ≤ 1 / (1 - (l * σ) ^ 2)
  have hlin : ν (S M)
      = ∑ m ∈ Finset.range M, (l ^ (2 * m) / ((2 * m).factorial : ℝ)) * ν (Y ^ (2 * m)) := by
    rw [hSdef]
    simp only [ν.map_sum, ν.map_smul]
  rw [hlin]
  have hterm : ∀ m ∈ Finset.range M,
      (l ^ (2 * m) / ((2 * m).factorial : ℝ)) * ν (Y ^ (2 * m)) ≤ ((l * σ) ^ 2) ^ m := by
    intro m _
    have hf : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc (l ^ (2 * m) / ((2 * m).factorial : ℝ)) * ν (Y ^ (2 * m))
        ≤ (l ^ (2 * m) / ((2 * m).factorial : ℝ)) * (((2 * m).factorial : ℝ) * σ ^ (2 * m)) :=
          mul_le_mul_of_nonneg_left (hmom m) (div_nonneg (pow_nonneg hl0 _) hf.le)
      _ = (l * σ) ^ (2 * m) := by
          rw [mul_pow, div_mul_eq_mul_div, mul_comm (((2 * m).factorial : ℝ)), ← mul_assoc,
            mul_div_assoc, div_self hf.ne', mul_one]
      _ = ((l * σ) ^ 2) ^ m := by rw [pow_mul]
  calc ∑ m ∈ Finset.range M, (l ^ (2 * m) / ((2 * m).factorial : ℝ)) * ν (Y ^ (2 * m))
      ≤ ∑ m ∈ Finset.range M, ((l * σ) ^ 2) ^ m := Finset.sum_le_sum hterm
    _ ≤ ((l * σ) ^ 2) ^ 0 / (1 - (l * σ) ^ 2) := by
        rw [Finset.range_eq_Ico]
        exact geom_sum_Ico_le_of_lt_one hq0 hq1
    _ = 1 / (1 - (l * σ) ^ 2) := by rw [pow_zero]

/-- **The cosh moment at the rate `(2σ)⁻¹`**: `ν(Y^{2m}) ≤ (2m)! σ^{2m}` at every `m` gives
`ν(cosh(Y/(2σ))) ≤ 4/3` (`state_coshC_le_of` at `λσ = 1/2`). DERIVED: `2`, `1/4`, `4/3` a choice of rate and
its geometric sum (any `λσ < 1` serves, `state_coshC_le_of`); the proofs that use it keep the choice inside
an existential constant. -/
theorem state_coshC_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    (Y : C(X, ℝ)) {σ : ℝ} (hσ : 0 < σ)
    (hmom : ∀ m : ℕ, ν (Y ^ (2 * m)) ≤ ((2 * m).factorial : ℝ) * σ ^ (2 * m)) :
    ν (coshC ((2 * σ)⁻¹ • Y)) ≤ 4 / 3 := by
  have hlσ : (2 * σ)⁻¹ * σ = 1 / 2 := by
    field_simp
  have h := state_coshC_le_of ν Y hσ.le (inv_pos.2 (mul_pos two_pos hσ)).le
    (by rw [hlσ]; norm_num) hmom
  rw [hlσ] at h
  exact h.trans_eq (by norm_num)

/-- `e^{|y|} ≤ 2 cosh y`. DERIVED: `2` the two exponentials. -/
theorem exp_abs_le_two_cosh (y : ℝ) : Real.exp |y| ≤ 2 * Real.cosh y := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_pos y
  have h2 := Real.exp_pos (-y)
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

end Moments

/-! ## 3. The mechanism -/

variable {N : ℕ}

/-- **The anomalous exponent of a channel**: `γᵢ` for a monomial, `γP` for the plaquette class.
DERIVED: no numeral. -/
def anom (γ : Ix0 → ℝ) (γP : ℝ) : MIx → ℝ
  | Sum.inl i => γ i
  | Sum.inr _ => γP

/-- **The free Wick index of a channel**: `⌈d_j / 4⌉`, `d_j` its canonical dimension (module docstring, §3).
DERIVED: `4` the dimension of `F²`; `3` the ceiling offset. -/
def wickIx (j : MIx) : ℕ := (mDim j + 3) / 4

/-- **The tree value of the trace two-point function**: `48 (N² − 1)/π⁴`, the value of
`r⁸⟨g²F²(x) g²F²(0)⟩/g⁴` in the free theory. DERIVED: `48` the tree count; `2` the square; `4` the power of
`π`. -/
def trTree (N : ℕ) : ℝ := 48 * ((N : ℝ) ^ 2 - 1) / Real.pi ^ 4

/-- **The zoom-in runs free, at one-loop coefficient `b₀`** (module docstring, §3): one `u > 0`, anomalous
exponents `γ`, `γP`; (chan) every channel's coincident-point cumulants within the free Wick count at the
canonical size dressed by `ḡ²(s)^{−aⱼ}`, at every scale `0 < s ≤ b` and order, eventually in the step;
(obs) at the observer's scale `b`, the flowed plaquette mean within `E a_k⁴` and its cumulants of every order
within the Wick count of a degree-two density; (af) a two-point kernel of the trace at `z` settling onto the
tree value times `ḡ²(r)²`. DERIVED: `1` the block offset and the limit of the ratio; `4` the plaquette
dimension; `8` the dimension pair; `2` the square of the coupling; `0` the signs and the point approached. -/
def ZoomInFreeAt [NeZero N] (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∀ j : MIx, ∃ σ : ℝ, 0 < σ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ n : ℕ, ∀ᶠ k in atTop,
      ∀ B : Finset (Fin n), B.Nonempty →
        |cum (stMom (stateK (NeZero.ne N) k) (fun _ : Fin n => msFlow Wf k s j)) B|
          ≤ ((B.card - 1).factorial : ℝ) ^ wickIx j
            * (σ * runG b₀ u s ^ (-anom γ γP j) / s ^ mDim j) ^ B.card)
    ∧ (∃ σP E : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
        |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
        ∧ ∀ (n : ℕ) (B : Finset (Fin n)), B.Nonempty →
          |cum (stMom (stateK (NeZero.ne N) k) (fun _ : Fin n => msFlow Wf k b (Sum.inr q))) B|
            ≤ ((B.card - 1).factorial : ℝ) * σP ^ B.card)
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

/-- **The zoom-in runs free** at the one-loop coefficient of `SU(N)`, `b0 N = 11N/(48π²)`.
DERIVED: no numeral beyond `b0`'s. -/
def ZoomInFree [NeZero N] (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ZoomInFreeAt (MassGap.ClayStatement.b0 N) z b Wf

/-! ## 4. The derivations -/

/-- The strength `μ_j(s)` at the clipped exponents is `t s^{d_j} / afLog(max(aⱼ, 0), s)`.
DERIVED: `0` the floor of the exponent. -/
theorem msMu_anom (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (j : MIx) (s : ℝ) :
    msMu t (fun i => max (γ i) 0) (max γP 0) j s = t * s ^ mDim j / afLog (max (anom γ γP j) 0) s := by
  cases j <;> rfl

/-- **The coincident-point core from the zoom**: `ZoomInFreeAt b₀ z b Wf`, `b₀ ≥ 0`, `b > 0` give
`ScaleControlChan b Wf` (module docstring, §4). DERIVED: `1` the least index and `K`; `2` the even powers;
`4` the plaquette dimension; `0` the signs. Inside the proof only (the conclusion's rate and constant are
existential): the rate `(2σP)⁻¹` and the cosh sum `4/3`, a choice (`state_coshC_le`). -/
theorem scaleControlChan_of_zoomFree [NeZero N] {b₀ : ℝ} (hb₀ : 0 ≤ b₀) {z : Chan → ℕ → ℝ} {b : ℝ}
    (hb : 0 < b) {Wf : ℝ → ConfFlow N} (h : ZoomInFreeAt b₀ z b Wf) : ScaleControlChan b Wf := by
  obtain ⟨u, γ, γP, hu, hchan, ⟨σP, E, hσP, hobs⟩, -⟩ := h
  refine ⟨fun i => max (γ i) 0, max γP 0, ⟨fun j => ?_, ?_⟩⟩
  · obtain ⟨σ, hσ, hj⟩ := hchan j
    obtain ⟨Q, hQ, hQb⟩ := runG_rpow_neg_le hb₀ hu (anom γ γP j)
    have ht : 0 < (σ * Q)⁻¹ := inv_pos.2 (mul_pos hσ hQ)
    refine ⟨max (wickIx j) 1, (σ * Q)⁻¹, 1, ht, fun s hs hsb p => ?_⟩
    filter_upwards [hj s hs hsb (2 * p)] with k hk
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ * runG b₀ u s ^ (-anom γ γP j) / s ^ mDim j := ⟨_, rfl⟩
    rw [← hc] at hk
    have hsd : 0 < s ^ mDim j := pow_pos hs _
    have hc0 : 0 ≤ c := by
      rw [hc]
      exact div_nonneg (mul_nonneg hσ.le (Real.rpow_nonneg (runG_pos hb₀ hu s).le _)) hsd.le
    have hmom := abs_state_pow_le (stateK (NeZero.ne N) k) (msFlow Wf k s j) (le_max_right _ 1) hc0 (2 * p)
      (fun B hB => (hk B hB).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
          (le_max_left _ _)) (pow_nonneg hc0 _)))
    have hmu := msMu_pos ht (fun i => max (γ i) 0) (max γP 0) hs j
    have hcmu : c ≤ (msMu (σ * Q)⁻¹ (fun i => max (γ i) 0) (max γP 0) j s)⁻¹ := by
      rw [msMu_anom, inv_div, hc, div_le_div_iff₀ hsd (mul_pos ht hsd)]
      have hg : runG b₀ u s ^ (-anom γ γP j) / Q ≤ afLog (max (anom γ γP j) 0) s :=
        (div_le_iff₀ hQ).2 (by linarith [hQb s])
      have e : σ * runG b₀ u s ^ (-anom γ γP j) * ((σ * Q)⁻¹ * s ^ mDim j)
          = runG b₀ u s ^ (-anom γ γP j) / Q * s ^ mDim j := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hg hsd.le
    unfold ScaleChanPM
    calc stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ |stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))| := le_abs_self _
      _ ≤ ((2 * p).factorial : ℝ) ^ max (wickIx j) 1 * c ^ (2 * p) := hmom
      _ ≤ ((2 * p).factorial : ℝ) ^ max (wickIx j) 1
            * ((msMu (σ * Q)⁻¹ (fun i => max (γ i) 0) (max γP 0) j s)⁻¹) ^ (2 * p) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hcmu _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = ((2 * p).factorial : ℝ) ^ max (wickIx j) 1
            / msMu (σ * Q)⁻¹ (fun i => max (γ i) 0) (max γP 0) j s ^ (2 * p) * 1 := by
          rw [inv_pow, mul_one, div_eq_mul_inv]
  · have hb4 : 0 < 2 * σP * b ^ 4 := mul_pos (mul_pos two_pos hσP) (pow_pos hb 4)
    have hl : 0 < (2 * σP)⁻¹ := inv_pos.2 (mul_pos two_pos hσP)
    refine ⟨afLog (max γP 0) b / (2 * σP * b ^ 4), Real.exp ((2 * σP)⁻¹ * E) * 2 * (4 / 3),
      div_pos (afLog_pos _ _) hb4, ?_⟩
    filter_upwards [hobs] with k hk q
    obtain ⟨hmean, hcum⟩ := hk q
    have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
    have ha4 : 0 < dySpacing N k ^ 4 := pow_pos ha 4
    have hmom : ∀ m : ℕ, stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ (2 * m))
        ≤ ((2 * m).factorial : ℝ) * σP ^ (2 * m) := by
      intro m
      have h := abs_state_pow_le (stateK (NeZero.ne N) k) (msFlow Wf k b (Sum.inr q)) le_rfl hσP.le (2 * m)
        (fun B hB => by rw [pow_one]; exact hcum (2 * m) B hB)
      rw [pow_one] at h
      exact (le_abs_self _).trans h
    have hcosh := state_coshC_le (stateK (NeZero.ne N) k) (msFlow Wf k b (Sum.inr q)) hσP hmom
    have hmu : msMu (afLog (max γP 0) b / (2 * σP * b ^ 4)) (fun i => max (γ i) 0) (max γP 0)
        (Sum.inr q) b = (2 * σP)⁻¹ := by
      have hA := (afLog_pos (max γP 0) b).ne'
      have hb' := hb.ne'
      have hσ' := hσP.ne'
      rw [msMu_inr]
      field_simp
    unfold ScaleChan
    rw [hmu, mDim_inr]
    have hpt : ∀ U, expC (((2 * σP)⁻¹ / dySpacing N k ^ 4)
          • msAbs ((Wf b).fieldMap k (mField (Sum.inr q))).1) U
        ≤ ((Real.exp ((2 * σP)⁻¹ * E) * 2) • coshC ((2 * σP)⁻¹ • msFlow Wf k b (Sum.inr q))) U := by
      intro U
      have hXU : msFlow Wf k b (Sum.inr q) U = (dySpacing N k ^ 4)⁻¹
          * (((Wf b).fieldMap k (mField (Sum.inr q))).1 U
            - stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 * 1) := rfl
      have hY : ((Wf b).fieldMap k (mField (Sum.inr q))).1 U
          = dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U
            + stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 := by
        rw [hXU, ← mul_assoc, mul_inv_cancel₀ ha4.ne', one_mul]
        ring
      have hYU : |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
          ≤ dySpacing N k ^ 4 * |msFlow Wf k b (Sum.inr q) U| + E * dySpacing N k ^ 4 := by
        rw [hY]
        calc |dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U
              + stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1|
            ≤ |dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U|
              + |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| := abs_add_le _ _
          _ ≤ dySpacing N k ^ 4 * |msFlow Wf k b (Sum.inr q) U| + E * dySpacing N k ^ 4 := by
              rw [abs_mul, abs_of_pos ha4]
              linarith
      show Real.exp ((2 * σP)⁻¹ / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|)
        ≤ Real.exp ((2 * σP)⁻¹ * E) * 2 * Real.cosh ((2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U)
      have hexp : (2 * σP)⁻¹ / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
          ≤ |(2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U| + (2 * σP)⁻¹ * E := by
        calc (2 * σP)⁻¹ / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
            ≤ (2 * σP)⁻¹ / dySpacing N k ^ 4
              * (dySpacing N k ^ 4 * |msFlow Wf k b (Sum.inr q) U| + E * dySpacing N k ^ 4) :=
              mul_le_mul_of_nonneg_left hYU (div_nonneg hl.le ha4.le)
          _ = |(2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U| + (2 * σP)⁻¹ * E := by
              rw [abs_mul, abs_of_pos hl]
              field_simp
      calc Real.exp ((2 * σP)⁻¹ / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|)
          ≤ Real.exp (|(2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U| + (2 * σP)⁻¹ * E) :=
            Real.exp_le_exp.2 hexp
        _ = Real.exp ((2 * σP)⁻¹ * E) * Real.exp |(2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U| := by
            rw [Real.exp_add, mul_comm]
        _ ≤ Real.exp ((2 * σP)⁻¹ * E) * (2 * Real.cosh ((2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U)) :=
            mul_le_mul_of_nonneg_left (exp_abs_le_two_cosh _) (Real.exp_pos _).le
        _ = Real.exp ((2 * σP)⁻¹ * E) * 2 * Real.cosh ((2 * σP)⁻¹ * msFlow Wf k b (Sum.inr q) U) := by
            ring
    calc stateK (NeZero.ne N) k (expC (((2 * σP)⁻¹ / dySpacing N k ^ 4)
          • msAbs ((Wf b).fieldMap k (mField (Sum.inr q))).1))
        ≤ stateK (NeZero.ne N) k
            ((Real.exp ((2 * σP)⁻¹ * E) * 2) • coshC ((2 * σP)⁻¹ • msFlow Wf k b (Sum.inr q))) :=
          (stateK (NeZero.ne N) k).mono hpt
      _ = Real.exp ((2 * σP)⁻¹ * E) * 2
            * stateK (NeZero.ne N) k (coshC ((2 * σP)⁻¹ • msFlow Wf k b (Sum.inr q))) :=
          (stateK (NeZero.ne N) k).map_smul _ _
      _ ≤ Real.exp ((2 * σP)⁻¹ * E) * 2 * (4 / 3) :=
          mul_le_mul_of_nonneg_left hcosh (by positivity)

/-- `b0 N > 0` for `N ≥ 1`. DERIVED: `0` the sign. -/
theorem b0_pos [NeZero N] : 0 < MassGap.ClayStatement.b0 N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold MassGap.ClayStatement.b0
  exact div_pos (by linarith) (by positivity)

/-- The tree value is positive at `N ≥ 2`. DERIVED: `2` the least colour count; `0` the sign. -/
theorem trTree_pos (hN2 : 2 ≤ N) : 0 < trTree N := by
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hn : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by nlinarith
  unfold trTree
  exact div_pos (by linarith) (by positivity)

/-- **The leading-log constant is the tree value times the one-loop factor**:
`trTree N · (2 b₀)⁻² = afConst N`. DERIVED: `2`, `4 = 2²`, `12 = 48/4` as in `afConst`. -/
theorem trTree_mul_eq_afConst [NeZero N] :
    trTree N * ((2 * MassGap.ClayStatement.b0 N)⁻¹) ^ 2 = afConst N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hπ := Real.pi_ne_zero
  unfold trTree afConst MassGap.ClayStatement.b0
  field_simp
  ring

/-- **`af` from the settling kernel**: at `N ≥ 2`, `r⁸ G(r) / (trTree N · ḡ²(r)²) → 1` gives
`AFCoefficient N G`, whatever `u > 0`. DERIVED: `8` the dimension pair; `2` the squares; `1` the limit of
the ratio; `0` the point approached. -/
theorem afCoefficient_of_settles (hN2 : 2 ≤ N) [NeZero N] {u : ℝ} (hu : 0 < u) {G : ℝ → ℝ}
    (h : Tendsto (fun r => r ^ 8 * G r / (trTree N * runG (MassGap.ClayStatement.b0 N) u r ^ 2))
      (𝓝[>] 0) (𝓝 1)) :
    AFCoefficient N G := by
  have hb : 0 < MassGap.ClayStatement.b0 N := b0_pos
  have hT := trTree_pos hN2
  have hP := (h.mul_const (trTree N)).mul ((tendsto_runG_mul_absLog hb hu).pow 2)
  rw [one_mul, trTree_mul_eq_afConst] at hP
  unfold AFCoefficient
  refine hP.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r _
  have hg := runG_pos hb.le hu r
  have hTg : trTree N * runG (MassGap.ClayStatement.b0 N) u r ^ 2 ≠ 0 := (mul_pos hT (pow_pos hg 2)).ne'
  rw [mul_pow, sq_abs]
  calc r ^ 8 * G r / (trTree N * runG (MassGap.ClayStatement.b0 N) u r ^ 2) * trTree N
        * (runG (MassGap.ClayStatement.b0 N) u r ^ 2 * Real.log r ^ 2)
      = r ^ 8 * G r / (trTree N * runG (MassGap.ClayStatement.b0 N) u r ^ 2)
          * (trTree N * runG (MassGap.ClayStatement.b0 N) u r ^ 2) * Real.log r ^ 2 := by ring
    _ = r ^ 8 * G r * Real.log r ^ 2 := by rw [div_mul_cancel₀ _ hTg]

/-- **The coincident-point core from the zoom**: `ZoomInFree z b Wf`, `b > 0` and `Wf b = W` give
`SubstrateCoreCL W z b Wf` (`scaleControlChan_of_zoomFree`, `afCoefficient_of_settles`).
DERIVED: `2` the least colour count; `0` the signs. -/
theorem substrateCoreCL_of_zoomFree (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (hb : 0 < b) (htop : Wf b = W) (h : ZoomInFree z b Wf) :
    SubstrateCoreCL W z b Wf := by
  have hsc := scaleControlChan_of_zoomFree b0_pos.le hb h
  obtain ⟨u, -, -, hu, -, -, G, hG, hset⟩ := h
  exact ⟨hb, htop, hsc, ⟨G, hG, afCoefficient_of_settles hN2 hu hset⟩⟩

/-! ## 5. The tests -/

/-- **The af clause reads only the germ at `0⁺`**: two kernels equal near `0⁺` settle together, so the
clause fixes no decay at large `r` (no gap). DERIVED: `8` the dimension pair; `2` the square; `1` the limit;
`0` the point approached. -/
theorem afSettles_congr {b₀ u : ℝ} {G G' : ℝ → ℝ} (hGG : G =ᶠ[𝓝[>] (0 : ℝ)] G') :
    Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)
      ↔ Tendsto (fun r => r ^ 8 * G' r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1) :=
  tendsto_congr' (hGG.mono fun r h => by simp only [h])

/-- **The af clause is `AFCoefficient`**: at `N ≥ 2` and `u > 0`, the settling of `r⁸ G / (trTree ḡ⁴)` onto
`1` is equivalent to `r⁸ G log² r → afConst N` (`ḡ² |log r| → (2 b₀)⁻¹`). DERIVED: `8` the dimension pair;
`2` the squares and the least colour count; `1` the limit of the ratio and the top of the window `(0, 1)`
where `log r ≠ 0`; `0` the point approached. -/
theorem afSettles_iff_afCoefficient (hN2 : 2 ≤ N) [NeZero N] {u : ℝ} (hu : 0 < u) {G : ℝ → ℝ} :
    Tendsto (fun r => r ^ 8 * G r / (trTree N * runG (MassGap.ClayStatement.b0 N) u r ^ 2)) (𝓝[>] 0) (𝓝 1)
      ↔ AFCoefficient N G := by
  refine ⟨afCoefficient_of_settles hN2 hu, fun h => ?_⟩
  have hb : 0 < MassGap.ClayStatement.b0 N := b0_pos
  have hA := (afConst_pos hN2).ne'
  have hD : Tendsto (fun r => trTree N * (runG (MassGap.ClayStatement.b0 N) u r * |Real.log r|) ^ 2)
      (𝓝[>] 0) (𝓝 (afConst N)) := by
    rw [← trTree_mul_eq_afConst]
    exact ((tendsto_runG_mul_absLog hb hu).pow 2).const_mul _
  have hq := (show Tendsto (fun r => r ^ 8 * G r * Real.log r ^ 2) (𝓝[>] 0) (𝓝 (afConst N)) from h).div hD hA
  rw [div_self hA] at hq
  refine hq.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r hr
  have hl : Real.log r ≠ 0 := (Real.log_neg hr.1 hr.2).ne
  have hg := (runG_pos hb.le hu r).ne'
  have hT := (trTree_pos hN2).ne'
  rw [Pi.div_apply, mul_pow, sq_abs, div_eq_div_iff (mul_ne_zero hT (mul_ne_zero (pow_ne_zero 2 hg) (pow_ne_zero 2 hl)))
    (mul_ne_zero hT (pow_ne_zero 2 hg))]
  ring

/-! ## 6. The aperture mechanism (the author's single-observer statement) -/

section Aperture

/-- **A reading through `M` in-band modes, by an even moment**: if `ν(eᵢⁿ) ≤ D` at every mode, `n` even,
then `ν((∑ᵢ eᵢ)ⁿ) ≤ Mⁿ D` (power mean). DERIVED: `1` the least mode count; `0` the signs. -/
theorem state_pow_sum_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    {M : ℕ} (hM : 1 ≤ M) (e : Fin M → C(X, ℝ)) {n : ℕ} (hn : Even n) {D : ℝ}
    (hD : ∀ i, ν (e i ^ n) ≤ D) : ν ((∑ i, e i) ^ n) ≤ (M : ℝ) ^ n * D := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM' := hM0.ne'
  have hw : ∑ _i : Fin M, (1 / (M : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hM0.ne']
  have hc0 : 0 ≤ 1 / (M : ℝ) * (M : ℝ) ^ n := by positivity
  have hpt : ∀ U, ((∑ i, e i) ^ n) U ≤ (∑ i, (1 / (M : ℝ) * (M : ℝ) ^ n) • e i ^ n) U := by
    intro U
    simp only [ContinuousMap.pow_apply, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    have e1 : ∑ i, e i U = ∑ i, 1 / (M : ℝ) * ((M : ℝ) * e i U) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [e1]
    refine (Real.pow_arith_mean_le_arith_mean_pow_of_even Finset.univ (fun _ => 1 / (M : ℝ))
      (fun i => (M : ℝ) * e i U) (fun _ _ => by positivity) hw hn).trans_eq ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  calc ν ((∑ i, e i) ^ n) ≤ ν (∑ i, (1 / (M : ℝ) * (M : ℝ) ^ n) • e i ^ n) := ν.mono hpt
    _ = ∑ i, (1 / (M : ℝ) * (M : ℝ) ^ n) * ν (e i ^ n) := by rw [ν.map_sum]; simp only [ν.map_smul]
    _ ≤ ∑ _i : Fin M, (1 / (M : ℝ) * (M : ℝ) ^ n) * D :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hD i) hc0
    _ = (M : ℝ) ^ n * D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          mul_one_div_cancel hM', one_mul]

/-- **The aperture settles, at one-loop coefficient `b₀`** (the author's mechanism; module docstring, §6). One
`u > 0` and noise exponents `γ`, `γP`:

* (band) every channel `j` is read at every aperture `s ∈ (0, b]` and step `k` through one fixed number
  `Mⱼ ≥ 1` of in-band modes `e_{k,s,i}`: the connected flowed reading is their sum, each mode is connected
  (constant offsets, the modes longer than the aperture, cancel), and `Mⱼ` does not depend on `k` or `s`
  (finite information per aperture);
* (noise) at every aperture and every order `2p`, eventually in the step, every mode has its even moment
  within the free Wick count at the canonical size times the noise per mode `ḡ²(s)^{κⱼ}`:
  `ν_k(e^{2p}) ≤ ((2p)!)^{wickIx j} (σⱼ ḡ²(s)^{κⱼ} / s^{d_j})^{2p}`;
* (obs) at the observer's own aperture `b`, every plaquette reading through one fixed number `MP ≥ 1` of
  connected modes, the flowed plaquette mean within `E a_k⁴`, and every mode's even moments of every order
  within `(2m)! σP^{2m}`;
* (af) a two-point kernel of the trace at `z` settling onto the tree value times `ḡ²(r)²`.

DERIVED: `1` the least mode count, the limit of the ratio; `2` the even powers and the square; `4` the
plaquette dimension; `8` the dimension pair; `0` the signs, the connected modes and the point approached. -/
def ApertureSettlesAt [NeZero N] (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∀ j : MIx, ∃ (M : ℕ) (σ : ℝ) (e : ℕ → ℝ → Fin M → C(Cfg N, ℝ)), 1 ≤ M ∧ 0 < σ ∧
      (∀ k s, msFlow Wf k s j = ∑ i, e k s i)
      ∧ (∀ k s i, stateK (NeZero.ne N) k (e k s i) = 0)
      ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ, ∀ᶠ k in atTop, ∀ i,
        stateK (NeZero.ne N) k (e k s i ^ (2 * p))
          ≤ ((2 * p).factorial : ℝ) ^ wickIx j * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p))
    ∧ (∃ (MP : ℕ) (eP : ℕ → MassGap.GibbsSpec.IPlaq → Fin MP → C(Cfg N, ℝ)) (σP E : ℝ),
        1 ≤ MP ∧ 0 < σP ∧
        (∀ k q, msFlow Wf k b (Sum.inr q) = ∑ i, eP k q i)
        ∧ (∀ k q i, stateK (NeZero.ne N) k (eP k q i) = 0)
        ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
          |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
          ∧ ∀ i m, stateK (NeZero.ne N) k (eP k q i ^ (2 * m)) ≤ ((2 * m).factorial : ℝ) * σP ^ (2 * m))
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

/-- **The aperture settles** at the one-loop coefficient of `SU(N)`. DERIVED: no numeral beyond `b0`'s. -/
def ApertureSettles [NeZero N] (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ApertureSettlesAt (MassGap.ClayStatement.b0 N) z b Wf

/-- The strength at the exponents `max(−κ, 0)`. DERIVED: `0` the floor of the exponent. -/
theorem msMu_anom_neg (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (j : MIx) (s : ℝ) :
    msMu t (fun i => max (-γ i) 0) (max (-γP) 0) j s
      = t * s ^ mDim j / afLog (max (-anom γ γP j) 0) s := by
  cases j <;> rfl

/-- **The per-channel moments and the plaquette exponential moment from the aperture**:
`ApertureSettlesAt b₀ z b Wf`, `b₀ ≥ 0`, `b > 0` give `ScaleControlChan b Wf`, at the exponents
`max(−κ, 0)`, the free Wick index per channel and `K = 1`; the plaquette class at `b` with rate
`(2 σP MP)⁻¹` and constant `e^{E/(2σP MP)} · 2 · 4/3` (Jensen over the `MP` modes, then
`state_coshC_le` per mode). DERIVED: `1` `K`; `2` the even powers; `4` the plaquette dimension; `0` the
signs. Inside the proof only (the conclusion's rate and constant are existential): the rate's `2` and the
cosh sum `4/3`, a choice (`state_coshC_le`). -/
theorem scaleControlChan_of_aperture [NeZero N] {b₀ : ℝ} (hb₀ : 0 ≤ b₀) {z : Chan → ℕ → ℝ} {b : ℝ}
    (hb : 0 < b) {Wf : ℝ → ConfFlow N} (h : ApertureSettlesAt b₀ z b Wf) : ScaleControlChan b Wf := by
  obtain ⟨u, γ, γP, hu, hchan, ⟨MP, eP, σP, E, hMP, hσP, hdecP, -, hobs⟩, -⟩ := h
  refine ⟨fun i => max (-γ i) 0, max (-γP) 0, ⟨fun j => ?_, ?_⟩⟩
  · obtain ⟨M, σ, e, hM, hσ, hdec, -, hj⟩ := hchan j
    obtain ⟨Q, hQ, hQb⟩ := runG_rpow_neg_le hb₀ hu (-anom γ γP j)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have ht : 0 < ((M : ℝ) * σ * Q)⁻¹ := inv_pos.2 (mul_pos (mul_pos hM0 hσ) hQ)
    refine ⟨wickIx j, ((M : ℝ) * σ * Q)⁻¹, 1, ht, fun s hs hsb p => ?_⟩
    filter_upwards [hj s hs hsb p] with k hk
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j := ⟨_, rfl⟩
    rw [← hc] at hk
    have hsd : 0 < s ^ mDim j := pow_pos hs _
    have hc0 : 0 ≤ c := by
      rw [hc]
      exact div_nonneg (mul_nonneg hσ.le (Real.rpow_nonneg (runG_pos hb₀ hu s).le _)) hsd.le
    have hmom := state_pow_sum_le (stateK (NeZero.ne N) k) hM (e k s) (even_two_mul p) hk
    rw [← hdec] at hmom
    have hmu := msMu_pos ht (fun i => max (-γ i) 0) (max (-γP) 0) hs j
    have hcmu :
        (M : ℝ) * c ≤ (msMu ((M : ℝ) * σ * Q)⁻¹ (fun i => max (-γ i) 0) (max (-γP) 0) j s)⁻¹ := by
      rw [msMu_anom_neg, inv_div, hc, mul_div_assoc', div_le_div_iff₀ hsd (mul_pos ht hsd)]
      have hQs := hQb s
      rw [neg_neg] at hQs
      have hg : runG b₀ u s ^ anom γ γP j / Q ≤ afLog (max (-anom γ γP j) 0) s :=
        (div_le_iff₀ hQ).2 (by linarith)
      have e2 : (M : ℝ) * (σ * runG b₀ u s ^ anom γ γP j) * (((M : ℝ) * σ * Q)⁻¹ * s ^ mDim j)
          = runG b₀ u s ^ anom γ γP j / Q * s ^ mDim j := by
        field_simp
      rw [e2]
      exact mul_le_mul_of_nonneg_right hg hsd.le
    unfold ScaleChanPM
    calc stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ (M : ℝ) ^ (2 * p) * (((2 * p).factorial : ℝ) ^ wickIx j * c ^ (2 * p)) := hmom
      _ = ((2 * p).factorial : ℝ) ^ wickIx j * ((M : ℝ) * c) ^ (2 * p) := by ring
      _ ≤ ((2 * p).factorial : ℝ) ^ wickIx j
            * ((msMu ((M : ℝ) * σ * Q)⁻¹ (fun i => max (-γ i) 0) (max (-γP) 0) j s)⁻¹) ^ (2 * p) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hM0.le hc0) hcmu _)
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ = ((2 * p).factorial : ℝ) ^ wickIx j
            / msMu ((M : ℝ) * σ * Q)⁻¹ (fun i => max (-γ i) 0) (max (-γP) 0) j s ^ (2 * p) * 1 := by
          rw [inv_pow, mul_one, div_eq_mul_inv]
  · have hM0 : (0 : ℝ) < MP := by exact_mod_cast hMP
    have hM' := hM0.ne'
    have hσ' := hσP.ne'
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (2 * σP * MP)⁻¹ := ⟨_, rfl⟩
    have hl0 : 0 < l := by
      rw [hl]
      exact inv_pos.2 (mul_pos (mul_pos two_pos hσP) hM0)
    have hlM : l * MP = (2 * σP)⁻¹ := by
      rw [hl]
      field_simp
    have hb4 : 0 < 2 * σP * MP * b ^ 4 := mul_pos (mul_pos (mul_pos two_pos hσP) hM0) (pow_pos hb 4)
    refine ⟨afLog (max (-γP) 0) b / (2 * σP * MP * b ^ 4), Real.exp (l * E) * 2 * (4 / 3),
      div_pos (afLog_pos _ _) hb4, ?_⟩
    filter_upwards [hobs] with k hk q
    obtain ⟨hmean, hmode⟩ := hk q
    have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
    have ha4 : 0 < dySpacing N k ^ 4 := pow_pos ha 4
    have hcosh : ∀ i, stateK (NeZero.ne N) k (coshC ((2 * σP)⁻¹ • eP k q i)) ≤ 4 / 3 :=
      fun i => state_coshC_le (stateK (NeZero.ne N) k) (eP k q i) hσP (hmode i)
    have hmu : msMu (afLog (max (-γP) 0) b / (2 * σP * MP * b ^ 4)) (fun i => max (-γ i) 0) (max (-γP) 0)
        (Sum.inr q) b = l := by
      have hA := (afLog_pos (max (-γP) 0) b).ne'
      have hb' := hb.ne'
      rw [msMu_inr, hl]
      field_simp
    unfold ScaleChan
    rw [hmu, mDim_inr]
    have hpt : ∀ U, expC ((l / dySpacing N k ^ 4) • msAbs ((Wf b).fieldMap k (mField (Sum.inr q))).1) U
        ≤ ((Real.exp (l * E) * 2 / MP) • ∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) U := by
      intro U
      have hXU : msFlow Wf k b (Sum.inr q) U = (dySpacing N k ^ 4)⁻¹
          * (((Wf b).fieldMap k (mField (Sum.inr q))).1 U
            - stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 * 1) := rfl
      have hY : ((Wf b).fieldMap k (mField (Sum.inr q))).1 U
          = dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U
            + stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 := by
        rw [hXU, ← mul_assoc, mul_inv_cancel₀ ha4.ne', one_mul]
        ring
      have hsumU : msFlow Wf k b (Sum.inr q) U = ∑ i, eP k q i U := by
        rw [hdecP k q]
        simp only [ContinuousMap.coe_sum, Finset.sum_apply]
      have hYU : |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
          ≤ dySpacing N k ^ 4 * ∑ i, |eP k q i U| + E * dySpacing N k ^ 4 := by
        rw [hY]
        have h1 := abs_add_le (dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U)
          (stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1)
        have h2 : |msFlow Wf k b (Sum.inr q) U| ≤ ∑ i, |eP k q i U| := by
          rw [hsumU]
          exact Finset.abs_sum_le_sum_abs _ _
        rw [abs_mul, abs_of_pos ha4] at h1
        linarith [mul_le_mul_of_nonneg_left h2 ha4.le]
      simp only [expC_apply, ContinuousMap.smul_apply, msAbs_apply, smul_eq_mul, ContinuousMap.coe_sum,
        Finset.sum_apply]
      show Real.exp (l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|)
        ≤ Real.exp (l * E) * 2 / MP * ∑ i, Real.cosh ((2 * σP)⁻¹ * eP k q i U)
      have hexp : l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
          ≤ l * ∑ i, 1 * |eP k q i U| + l * E := by
        calc l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
            ≤ l / dySpacing N k ^ 4 * (dySpacing N k ^ 4 * ∑ i, |eP k q i U| + E * dySpacing N k ^ 4) :=
              mul_le_mul_of_nonneg_left hYU (div_nonneg hl0.le ha4.le)
          _ = l * ∑ i, 1 * |eP k q i U| + l * E := by
              simp only [one_mul]
              field_simp
      have hJ := MassGap.FlowUV.exp_mul_wsum_le Finset.univ (fun _ : Fin MP => (1 : ℝ))
        (fun i => |eP k q i U|) (fun _ _ => zero_le_one) hM0 (by simp) l
      calc Real.exp (l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|)
          ≤ Real.exp (l * ∑ i, 1 * |eP k q i U| + l * E) := Real.exp_le_exp.2 hexp
        _ = Real.exp (l * E) * Real.exp (l * ∑ i, 1 * |eP k q i U|) := by
            rw [Real.exp_add, mul_comm]
        _ ≤ Real.exp (l * E) * ∑ i, (1 / (MP : ℝ)) * Real.exp (l * MP * |eP k q i U|) :=
            mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le
        _ ≤ Real.exp (l * E) * ∑ i, (1 / (MP : ℝ)) * (2 * Real.cosh ((2 * σP)⁻¹ * eP k q i U)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hab : l * MP * |eP k q i U| = |(2 * σP)⁻¹ * eP k q i U| := by
              rw [hlM, abs_mul, abs_of_pos (inv_pos.2 (mul_pos two_pos hσP))]
            rw [hab]
            exact exp_abs_le_two_cosh _
        _ = Real.exp (l * E) * 2 / MP * ∑ i, Real.cosh ((2 * σP)⁻¹ * eP k q i U) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    have hsum : stateK (NeZero.ne N) k (∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) ≤ MP * (4 / 3) := by
      rw [(stateK (NeZero.ne N) k).map_sum]
      calc ∑ i, stateK (NeZero.ne N) k (coshC ((2 * σP)⁻¹ • eP k q i)) ≤ ∑ _i : Fin MP, (4 / 3 : ℝ) :=
            Finset.sum_le_sum fun i _ => hcosh i
        _ = MP * (4 / 3) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc stateK (NeZero.ne N) k (expC ((l / dySpacing N k ^ 4)
          • msAbs ((Wf b).fieldMap k (mField (Sum.inr q))).1))
        ≤ stateK (NeZero.ne N) k ((Real.exp (l * E) * 2 / MP) • ∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) :=
          (stateK (NeZero.ne N) k).mono hpt
      _ = Real.exp (l * E) * 2 / MP * stateK (NeZero.ne N) k (∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) :=
          (stateK (NeZero.ne N) k).map_smul _ _
      _ ≤ Real.exp (l * E) * 2 / MP * (MP * (4 / 3)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp (l * E) * 2 * (4 / 3) := by field_simp

/-- **The coincident-point core from the aperture**: `ApertureSettles z b Wf`, `b > 0` and `Wf b = W` give
`SubstrateCoreCL W z b Wf`. DERIVED: `2` the least colour count; `0` the signs. -/
theorem substrateCoreCL_of_aperture (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (hb : 0 < b) (htop : Wf b = W) (h : ApertureSettles z b Wf) :
    SubstrateCoreCL W z b Wf := by
  have hsc := scaleControlChan_of_aperture b0_pos.le hb h
  obtain ⟨u, -, -, hu, -, -, G, hG, hset⟩ := h
  exact ⟨hb, htop, hsc, ⟨G, hG, afCoefficient_of_settles hN2 hu hset⟩⟩

/-- **The flowed reading is connected**: `ν_k(msFlow) = 0` (`msFlow` subtracts the state mean).
DERIVED: `0` the mean; `1` the unit observable. -/
theorem state_msFlow [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    stateK (NeZero.ne N) k (msFlow Wf k s j) = 0 := by
  unfold msFlow
  rw [MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_smul,
    MassGap.DLRLimit.State.map_one, mul_one, sub_self, mul_zero]

/-- **The aperture's mode clauses at one mode**: `ApertureSettlesAt` with every channel read through the one
mode `msFlow` itself: the even moments of the reading within the free Wick count dressed by `ḡ²(s)^{κⱼ}`,
the plaquette mean `O(a_k⁴)` and the plaquette moments within `(2m)! σP^{2m}` at `b`, and the af clause.
DERIVED: `1` the limit of the ratio; `2` the even powers and the square; `4` the plaquette dimension; `8` the
dimension pair; `0` the signs and the point approached. -/
def ApertureOneAt [NeZero N] (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∀ j : MIx, ∃ σ : ℝ, 0 < σ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ, ∀ᶠ k in atTop,
      stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickIx j * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p))
    ∧ (∃ σP E : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
        |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
        ∧ ∀ m : ℕ, stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ (2 * m))
          ≤ ((2 * m).factorial : ℝ) * σP ^ (2 * m))
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

/-- **The mode clauses are equivalent to one mode**: an `M`-mode witness at noise `σ` gives the one-mode
witness at noise `Mσ` (`state_pow_sum_le`), and one mode, `e = msFlow`, is a witness (`state_msFlow`);
likewise for the plaquette count `MP`. So the count in `ApertureSettlesAt` is not a constraint.
DERIVED: `1` the one mode; `2` the even powers. -/
theorem apertureSettlesAt_iff_one [NeZero N] {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N} :
    ApertureSettlesAt b₀ z b Wf ↔ ApertureOneAt b₀ z b Wf := by
  constructor
  · rintro ⟨u, γ, γP, hu, hchan, ⟨MP, eP, σP, E, hMP, hσP, hdecP, -, hobs⟩, haf⟩
    have hMP0 : (0 : ℝ) < MP := by exact_mod_cast hMP
    refine ⟨u, γ, γP, hu, fun j => ?_, ⟨MP * σP, E, mul_pos hMP0 hσP, ?_⟩, haf⟩
    · obtain ⟨M, σ, e, hM, hσ, hdec, -, hj⟩ := hchan j
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
      refine ⟨M * σ, mul_pos hM0 hσ, fun s hs hsb p => ?_⟩
      filter_upwards [hj s hs hsb p] with k hk
      have h := state_pow_sum_le (stateK (NeZero.ne N) k) hM (e k s) (even_two_mul p) hk
      rw [← hdec] at h
      refine h.trans_eq ?_
      ring
    · filter_upwards [hobs] with k hk q
      refine ⟨(hk q).1, fun m => ?_⟩
      have h := state_pow_sum_le (stateK (NeZero.ne N) k) hMP (eP k q) (even_two_mul m)
        (fun i => (hk q).2 i m)
      rw [← hdecP] at h
      refine h.trans_eq ?_
      ring
  · rintro ⟨u, γ, γP, hu, hchan, ⟨σP, E, hσP, hobs⟩, haf⟩
    refine ⟨u, γ, γP, hu, fun j => ?_, ⟨1, fun k q _ => msFlow Wf k b (Sum.inr q), σP, E, le_rfl, hσP,
      fun k q => by rw [Fin.sum_univ_one], fun k q _ => state_msFlow Wf k b _, ?_⟩, haf⟩
    · obtain ⟨σ, hσ, hj⟩ := hchan j
      refine ⟨1, σ, fun k s _ => msFlow Wf k s j, le_rfl, hσ, fun k s => by rw [Fin.sum_univ_one],
        fun k s _ => state_msFlow Wf k s j, fun s hs hsb p => ?_⟩
      filter_upwards [hj s hs hsb p] with k hk _
      exact hk
    · filter_upwards [hobs] with k hk q
      exact ⟨(hk q).1, fun _ m => (hk q).2 m⟩

end Aperture

end MassGap.ZoomFree

end

/-! ### The copy over a coupling family -/

namespace MassGap.ZoomFree

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ZoomFree.substrateCoreCL_of_zoomFree
  MassGap.ZoomFree.substrateCoreCL_of_aperture

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ZoomFree

/-! ## 7. The root -/

noncomputable section

namespace MassGap.ZoomFree

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ScaleLightCone (CoreInputsAlongWSL ZoomSettlesUV clayStatementOf_of_zoomSettles)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` with both zoom mechanisms**: `ScaleLightCone.CoreInputsAlongWSL` with
`0 < b`, `Wf b = W` and the copy of `ZoomInFree z b Wf` in place of the copy of `SubstrateCoreCL W z b Wf`,
every other field unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWZF (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.ZoomFree.ZoomInFree (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **The zoom bundle gives the separated-zoom bundle** (the copy of `substrateCoreCL_of_zoomFree` at
`cpl βs`). DERIVED: `2` the least colour count. -/
theorem coreWSL_of_coreWZF {βs : ℕ → ℝ} (h : CoreInputsAlongWZF N βs) : CoreInputsAlongWSL N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf,
    CouplingGen.Along.ZoomFree.substrateCoreCL_of_zoomFree (cpl βs) (Fact.out : 2 ≤ N) hb htop hZ, hE, F⟩

/-- **The root at `SU(N)` from the strong end and the two zoom mechanisms**: `StrongEnd N`, the settling
window reading along the towers near `0⁺` and `CoreInputsAlongWZF` along the towers near `0⁺` give
`ClayStatementOf (SU N)` (`ScaleLightCone.clayStatementOf_of_zoomSettles`, `coreWSL_of_coreWZF`).
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_zoomFree (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWZF N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_zoomSettles hS hUV (hF.mono fun _ h βs hT => coreWSL_of_coreWZF (h βs hT))

variable (N) in
/-- **The flow-side bundle along `βs` with the aperture**: `CoreInputsAlongWZF` with the copy of
`ApertureSettles z b Wf` in place of the copy of `ZoomInFree z b Wf`. DERIVED: `0` the signs. -/
def CoreInputsAlongWAP (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.ZoomFree.ApertureSettles (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **The aperture bundle gives the separated-zoom bundle** (the copy of `substrateCoreCL_of_aperture` at
`cpl βs`). DERIVED: `2` the least colour count. -/
theorem coreWSL_of_coreWAP {βs : ℕ → ℝ} (h : CoreInputsAlongWAP N βs) : CoreInputsAlongWSL N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf,
    CouplingGen.Along.ZoomFree.substrateCoreCL_of_aperture (cpl βs) (Fact.out : 2 ≤ N) hb htop hZ, hE, F⟩

/-- **The root at `SU(N)` from the strong end, the separated zoom and the aperture**: `StrongEnd N`, the
settling window reading and `CoreInputsAlongWAP` along the towers near `0⁺` give `ClayStatementOf (SU N)`
(`ScaleLightCone.clayStatementOf_of_zoomSettles`, `coreWSL_of_coreWAP`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_aperture (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWAP N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_zoomSettles hS hUV (hF.mono fun _ h βs hT => coreWSL_of_coreWAP (h βs hT))

end MassGap.ZoomFree

end

#print axioms MassGap.ZoomFree.runG_den_pos
#print axioms MassGap.ZoomFree.runG_pos
#print axioms MassGap.ZoomFree.runG_le
#print axioms MassGap.ZoomFree.inv_runG_le
#print axioms MassGap.ZoomFree.runG_rpow_neg_le
#print axioms MassGap.ZoomFree.tendsto_absLog
#print axioms MassGap.ZoomFree.tendsto_runG_zero
#print axioms MassGap.ZoomFree.tendsto_runG_mul_absLog
#print axioms MassGap.ZoomFree.runsFree_iff
#print axioms MassGap.ZoomFree.zf_sum_pow_le
#print axioms MassGap.ZoomFree.abs_mom_le_of_cum_pow
#print axioms MassGap.ZoomFree.stMom_const_univ
#print axioms MassGap.ZoomFree.abs_state_pow_le
#print axioms MassGap.ZoomFree.state_coshC_le
#print axioms MassGap.ZoomFree.exp_abs_le_two_cosh
#print axioms MassGap.ZoomFree.msMu_anom
#print axioms MassGap.ZoomFree.scaleControlChan_of_zoomFree
#print axioms MassGap.ZoomFree.b0_pos
#print axioms MassGap.ZoomFree.trTree_pos
#print axioms MassGap.ZoomFree.trTree_mul_eq_afConst
#print axioms MassGap.ZoomFree.afCoefficient_of_settles
#print axioms MassGap.ZoomFree.substrateCoreCL_of_zoomFree
#print axioms MassGap.CouplingGen.Along.ZoomFree.substrateCoreCL_of_zoomFree
#print axioms MassGap.ZoomFree.afSettles_congr
#print axioms MassGap.ZoomFree.coreWSL_of_coreWZF
#print axioms MassGap.ZoomFree.clayStatementOf_of_zoomFree
#print axioms MassGap.ZoomFree.state_pow_sum_le
#print axioms MassGap.ZoomFree.msMu_anom_neg
#print axioms MassGap.ZoomFree.scaleControlChan_of_aperture
#print axioms MassGap.ZoomFree.substrateCoreCL_of_aperture
#print axioms MassGap.CouplingGen.Along.ZoomFree.substrateCoreCL_of_aperture
#print axioms MassGap.ZoomFree.coreWSL_of_coreWAP
#print axioms MassGap.ZoomFree.clayStatementOf_of_aperture
#print axioms MassGap.ZoomFree.le_inv_runG
#print axioms MassGap.ZoomFree.state_coshC_le_of
#print axioms MassGap.ZoomFree.afSettles_iff_afCoefficient
#print axioms MassGap.ZoomFree.state_msFlow
#print axioms MassGap.ZoomFree.apertureSettlesAt_iff_one
