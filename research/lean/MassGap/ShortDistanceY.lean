import Mathlib
import MassGap.ThreePointN
import MassGap.WeakCouplingWindow

/-!
# MassGap.ShortDistanceY — requirement Y as the asymptotic-freedom form of the `tr F²` two-point function

## The statement

Jaffe–Witten ask that the continuum theory be Yang–Mills: its local fields are gauge-invariant
polynomials in the curvature, and their correlation functions agree at short distances with the
predictions of asymptotic freedom and perturbative renormalisation theory. For the lowest composite
`tr F²` the prediction is a statement about its connected two-point function `G(r)` at separation
`r → 0⁺`:

    r⁸ · G(r) · (log r)²  →  C > 0.                                        (`AFShortDistance G`)

`8 = 2·4` is twice the canonical dimension of `tr F²` in four dimensions. The renormalisation-group
invariant composite is the trace anomaly `(β(g)/2g)·F^aF^a`, which at leading order is
`−(b₀/2)·g²F^aF^a`, so each insertion carries one running coupling `ḡ²(r)`, and the Callan–Symanzik
equation gives
`r⁸ G(r) = Φ(ḡ(r))` with `Φ(g) = C₀ g⁴ (1 + O(g²))`. At one loop `ḡ²(r) ∼ 1/(2 b₀ log(1/r))`: the
power `1` of the logarithm is the one-loop start `β(g) ∼ −b₀ g³` of the beta function (its sign: `beta_neg` in `Running`),
and two insertions square it, which is the exponent `2`. The two-loop coefficient `b₁` changes `ḡ²` by a
factor `1 + O(log log(1/r) / log(1/r)) → 1` and leaves the exponent and the existence of `C` alone:
`coupling_mul_neg_log_aRun_tendsto` proves this for the tree's two-loop spacing `aRun N`, whose `b₁`
term `(51/121)·log u` drops out of `(2N/β)·log(1/aRun N β) → 24π²/(11N) = 1/(2b₀)` (`inv_two_b0`).
`(log r)² = (log (1/r))²` (`log_inv_sq`). A constant rescaling of the composite, the only freedom of a
renormalisation-group invariant operator, rescales `C` and keeps the form (`af_of_const_mul`); an
additive renormalisation does not enter a connected function.

The exponent `2` holds for every normalisation of the composite that is a fixed multiple of
`(β(g)/2g)·F^aF^a`. The minimally subtracted `[F^aF^a]_μ` at a fixed scale `μ` is
`(2g(μ)/β(g(μ)))·(β(g)/2g)F^aF^a`, a constant multiple, so it carries the same `(log r)²`: the one-loop
anomalous dimension of the canonically normalised `F^aF^a` is what turns its tree-level `r⁻⁸` into
`r⁻⁸ ḡ⁴(r)/g⁴(μ)`. A normalisation tied to the separation itself (`μ = 1/r`) has no logarithm, and the
bare canonical `F^aF^a` on the lattice has no continuum limit; neither is a fixed operator.
`latticeTwoPoint` uses the bare `g₀²·tr F²`, a fixed multiple of the invariant composite in the limit.

`af_along_aRun`: along the two-loop spacing, `AFShortDistance G` gives
`a⁸ G(a) / (g²)² → C·(2b₀)² > 0` at `a = aRun N β`, `g² = 2N/β` — the square of the running coupling at
the scale of the separation.

## What it separates

* `ShortDistanceSuppressed G`, `r⁸G(r) → 0`, separates from every free composite
  (`not_suppressed_of_free`); `AFShortDistance` implies it (`scaled_tendsto_zero_of_af`).
* `not_af_of_scaled_tendsto_ne_zero`: if `r⁸ G(r) → C₀ ≠ 0` then `G` is not asymptotically free. So the
  class `FreeShortDistance G` (`r⁸G → C > 0`) is disjoint from Y (`af_and_free_false`).
* The free massless composite `freeMassless C r = C / r⁸` has `r⁸G = C` exactly and is in that class
  (`freeShortDistance_freeMassless`, `not_af_freeMassless`).
* `FreeScalingForm G`: `G(r) = Φ(m r)/r⁸` for a mass `m ≥ 0` and a profile `Φ` continuous from the
  right at `0` with `Φ(0) > 0`. Dimensional analysis puts the tree-level composite two-point function of
  a free field of mass `m` in this form, `Φ(0)` being the massless value; identifying `Φ` with the
  Bessel-function expression of the free massive vector field is physics and is not formalised (Mathlib
  carries no modified Bessel function `K_ν`). Every such `G` is in the free class
  (`freeShortDistance_of_scalingForm`) and so fails Y (`not_af_of_scalingForm`), massless (`m = 0`,
  `scalingForm_freeMassless`) and massive alike.
* `not_af_of_isBigO_rpow`: `r⁸G = O(r^ε)` for some `ε > 0` fails Y; `not_af_of_conformal`: no pure power
  law `G(r) = K r^{−2Δ}`, `K ≠ 0`, of any scaling dimension `Δ` satisfies Y. So Y excludes every
  scale-invariant two-point function, which `ShortDistanceSuppressed` does not:
  `suppressed_strictly_weaker` exhibits `r ↦ r/r⁸` (dimension `7/2`), suppressed and not asymptotically
  free.
* `af_satisfiable`: `afWitness C r = C·(r⁸)⁻¹·((log r)²)⁻¹` satisfies Y, so Y is not vacuous.

## On the lattice family

`latticeTwoPoint N hN β r` is the connected two-point function, under
`PeriodicState.periodicState hN β`, of the lattice `tr F²` density at the origin and at
`⌈r / aRun N β⌉·e₀` (`ThreePointN.blockObs` with side `1`, summed over the six planes), divided by
`aRun N β ⁸`: the separation is held at physical length `r` while the spacing runs with the two-loop
`SU(N)` law. `ContinuumTwoPoint L G` says the family converges to `G(r)` at every fixed `r > 0`;
`FamilyAF L` is the asymptotic-freedom form with one constant `C`: for every `ε > 0` a `δ > 0` such that at
each separation `0 < r < δ` the family lies within `ε` of the form at every large `β`, the threshold in `β`
depending on `r` — the analogue of `WeakCouplingWindow.FixedWindowDecay` at a fixed physical separation. Under `ContinuumTwoPoint L G`,
`FamilyAF L ↔ AFShortDistance G` (`familyAF_iff`): the lattice form is the continuum statement, neither
weaker nor stronger.

`wilson_yang_mills_separated`: from `WilsonContinuumTwoPoint N hN G`, `WilsonLatticeAF N hN` and
`ThreePointN.WilsonThreePointSeparation N hN`, the continuum two-point function satisfies Y, it is not the
two-point function of any free composite (massless or massive), it is no pure power law, it falls like
the square of the running coupling along `aRun N`, and along every `β → ∞` the normalised three-point
statistic `ThreePointN.sepRatio` of the lattice block composites is eventually at least a fixed `c > 0`,
where `0` is the value of every Gaussian law and of the free massless gauge field. Y separates the
continuum two-point function from every free composite, massless or massive; N separates the lattice
family's block composites from Gaussian laws and from the free massless value. At `N = 1` the group
`SU(1)` is trivial, `latticeTwoPoint` is `0` and `WilsonLatticeAF` fails, so the theorem carries its
content at `2 ≤ N`.

## Open

`WilsonContinuumTwoPoint N hN G` (for some `G`), `WilsonLatticeAF N hN` and
`ThreePointN.WilsonThreePointSeparation N hN` are not proved at any `β`. The converse of
`af_along_aRun` (from the `aRun` form back to `AFShortDistance`) is not built. The requirement that every
local field be a gauge-invariant polynomial in the curvature is not addressed beyond the choice of the
composite.
-/

namespace MassGap.ShortDistanceY

open Filter Topology Asymptotics
open MassGap.AsymptoticScaling (aRun aRun_pos)

/-! ## 1. The continuum statements -/

/-- **Requirement Y at the lowest composite.** `r⁸ · G(r) · (log r)² → C` as `r → 0⁺` for some
`C > 0`: the connected two-point function of `tr F²`, normalised as a fixed multiple of the
renormalisation-group invariant `(β(g)/2g)·F^aF^a`, falls, after the canonical `r⁻⁸`, like the square of
the one-loop running coupling `ḡ²(r) ∼ 1/(2b₀ log(1/r))`.

DERIVED: `8 = 2·4`, twice the canonical dimension `4` of `tr F²` in four dimensions; `2` on the
logarithm is the two insertions, each carrying one `ḡ²`, whose one-loop form carries `log` to the power
`1` because the beta function starts at `g³`; `0` is the point approached and the sign of `C`, which the
reflection-positive two-point function fixes. -/
def AFShortDistance (G : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ Tendsto (fun r => r ^ 8 * G r * Real.log r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 C)

#print axioms AFShortDistance

/-- **The suppressed form.** `r⁸ · G(r) → 0` as `r → 0⁺`. No free composite satisfies it
(`not_suppressed_of_free`).

DERIVED: `8` as in `AFShortDistance`; `0` is the point approached and the limit. -/
def ShortDistanceSuppressed (G : ℝ → ℝ) : Prop :=
  Tendsto (fun r => r ^ 8 * G r) (𝓝[>] (0 : ℝ)) (𝓝 0)

#print axioms ShortDistanceSuppressed

/-- **The free class.** `r⁸ · G(r) → C` as `r → 0⁺` for some `C > 0`: the short-distance form of the
composite two-point function of a free field, massless or massive.

DERIVED: `8` as in `AFShortDistance`; `0` is the point approached and the sign of `C`. -/
def FreeShortDistance (G : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ Tendsto (fun r => r ^ 8 * G r) (𝓝[>] (0 : ℝ)) (𝓝 C)

#print axioms FreeShortDistance

/-- `(log r⁻¹)² = (log r)²`, by `Real.log_inv` and `neg_sq`: the form may be read with `log (1/r)`.

DERIVED: `2` is the square. -/
theorem log_inv_sq (r : ℝ) : Real.log r⁻¹ ^ 2 = Real.log r ^ 2 := by
  rw [Real.log_inv, neg_sq]

#print axioms log_inv_sq

/-- `(log r)² → ∞` as `r → 0⁺`: `−log r → ∞` (`Real.tendsto_log_nhdsGT_zero`) and the square of a
quantity tending to `∞` does.

DERIVED: `2` is the square; `0` is the point approached. -/
theorem tendsto_log_sq_nhdsGT_zero :
    Tendsto (fun r : ℝ => Real.log r ^ 2) (𝓝[>] (0 : ℝ)) atTop := by
  have h : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h2 := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp h
  exact h2.congr (fun r => neg_sq (Real.log r))

#print axioms tendsto_log_sq_nhdsGT_zero

/-- **Y implies the suppressed form.** `AFShortDistance G` gives `r⁸ G(r) → 0`: on `(0, 1)` the logarithm is
non-zero, so `r⁸G = (r⁸G·(log r)²)·((log r)²)⁻¹ → C·0`.

DERIVED: `8` and `2` as in `AFShortDistance`; `0` is the point approached and the limit; `1` is where
`log` changes sign, so `(0, 1)` is where `(log r)² ≠ 0` is read off `Real.log_neg`. -/
theorem scaled_tendsto_zero_of_af {G : ℝ → ℝ} (h : AFShortDistance G) :
    ShortDistanceSuppressed G := by
  show Tendsto (fun r => r ^ 8 * G r) (𝓝[>] (0 : ℝ)) (𝓝 0)
  obtain ⟨C, -, hlim⟩ := h
  have hinv : Tendsto (fun r : ℝ => (Real.log r ^ 2)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_log_sq_nhdsGT_zero.inv_tendsto_atTop
  have hprod : Tendsto (fun r : ℝ => r ^ 8 * G r * Real.log r ^ 2 * (Real.log r ^ 2)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (C * 0)) := hlim.mul hinv
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  have hL : Real.log r ^ 2 ≠ 0 := pow_ne_zero 2 (Real.log_neg hr.1 hr.2).ne
  exact mul_inv_cancel_right₀ hL _

#print axioms scaled_tendsto_zero_of_af

/-! ## 2. Every free composite fails Y -/

/-- **The target.** If `r⁸ G(r) → C₀` with `C₀ ≠ 0`, then `G` does not satisfy Y: Y forces the limit to
be `0` (`scaled_tendsto_zero_of_af`), and limits in `ℝ` are unique.

DERIVED: `8` as in `AFShortDistance`; `0` is the point approached and the excluded limit. -/
theorem not_af_of_scaled_tendsto_ne_zero {G : ℝ → ℝ} {C₀ : ℝ} (hC₀ : C₀ ≠ 0)
    (h : Tendsto (fun r => r ^ 8 * G r) (𝓝[>] (0 : ℝ)) (𝓝 C₀)) : ¬ AFShortDistance G :=
  fun hY => hC₀ (tendsto_nhds_unique h
    (show Tendsto (fun r => r ^ 8 * G r) (𝓝[>] (0 : ℝ)) (𝓝 0) from scaled_tendsto_zero_of_af hY))

#print axioms not_af_of_scaled_tendsto_ne_zero

/-- **The free class fails Y.**

DERIVED: no numeral beyond the definitions'. -/
theorem not_af_of_free {G : ℝ → ℝ} (hfree : FreeShortDistance G) : ¬ AFShortDistance G := by
  obtain ⟨C, hC, hlim⟩ := hfree
  exact not_af_of_scaled_tendsto_ne_zero hC.ne' hlim

#print axioms not_af_of_free

/-- **Y and the free form together are false.**

DERIVED: no numeral beyond the definitions'. -/
theorem af_and_free_false {G : ℝ → ℝ} (h : AFShortDistance G ∧ FreeShortDistance G) : False :=
  not_af_of_free h.2 h.1

#print axioms af_and_free_false

/-- **The free class fails the suppressed form.** `FreeShortDistance G → ¬ ShortDistanceSuppressed G`.

DERIVED: no numeral beyond the definitions'. -/
theorem not_suppressed_of_free {G : ℝ → ℝ} (hfree : FreeShortDistance G) :
    ¬ ShortDistanceSuppressed G := by
  obtain ⟨C, hC, hlim⟩ := hfree
  exact fun hs => hC.ne' (tendsto_nhds_unique hlim hs)

#print axioms not_suppressed_of_free

/-- **The free massless composite.** `C / r⁸`, the exact two-point function of `tr F²` in the free
massless gauge theory at separated points, `C > 0` a normalisation.

DERIVED: `8` as in `AFShortDistance`: the free massless composite has no scale besides `r`, so its
two-point function is `r` to the power `−2·4`. -/
noncomputable def freeMassless (C : ℝ) (r : ℝ) : ℝ := C / r ^ 8

#print axioms freeMassless

/-- `r⁸ · freeMassless C r = C` at every `r ≠ 0` (`mul_div_cancel₀`).

DERIVED: `8` is `freeMassless`'s; `0` is the excluded separation. -/
theorem scaled_freeMassless (C : ℝ) {r : ℝ} (hr : r ≠ 0) : r ^ 8 * freeMassless C r = C := by
  rw [freeMassless, mul_div_cancel₀ C (pow_ne_zero 8 hr)]

#print axioms scaled_freeMassless

/-- **The free massless composite is in the free class**, at `C > 0`.

DERIVED: `0` is the sign of `C` and the point approached; `8` is `freeMassless`'s. -/
theorem freeShortDistance_freeMassless {C : ℝ} (hC : 0 < C) :
    FreeShortDistance (freeMassless C) := by
  refine ⟨C, hC, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  exact (scaled_freeMassless C hr0.ne').symm

#print axioms freeShortDistance_freeMassless

/-- **The free massless composite fails Y**, at every `C ≠ 0`: `r⁸G` is the constant `C`.

DERIVED: `0` is the excluded normalisation and the point approached. -/
theorem not_af_freeMassless {C : ℝ} (hC : C ≠ 0) : ¬ AFShortDistance (freeMassless C) := by
  refine not_af_of_scaled_tendsto_ne_zero hC (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  exact (scaled_freeMassless C hr0.ne').symm

#print axioms not_af_freeMassless

/-- **The free scaling form.** `G(r) = Φ(m r) / r⁸` at every `r > 0`, for a mass `m ≥ 0` and a profile
`Φ` continuous at `0` from the right with `Φ(0) > 0`. A free field of mass `m` has no scale besides `m`
and `r`, so the two-point function of its `tr F²` composite is `r⁻⁸` times a function of `m r`. For a
free massive vector field the longitudinal mode does not enter `F = dA`, so that function tends, as
`m r → 0`, to the free massless value, which is positive: this is the continuity and the sign the
definition asks for. Several masses `m₁, …, m_k` fit the same form with `m = max mᵢ`, since every
`mᵢ r` is a fixed multiple of `m r`.

DERIVED: `8` as in `AFShortDistance`; `0` is the least mass, the base point of `Φ`, the sign of `Φ(0)`
and of `r`. -/
def FreeScalingForm (G : ℝ → ℝ) : Prop :=
  ∃ m : ℝ, ∃ Φ : ℝ → ℝ, 0 ≤ m ∧ ContinuousWithinAt Φ (Set.Ici 0) 0 ∧ 0 < Φ 0 ∧
    ∀ r : ℝ, 0 < r → G r = Φ (m * r) / r ^ 8

#print axioms FreeScalingForm

/-- **The free scaling form is in the free class**, with limit `Φ(0)`: `m r → 0` from the right as
`r → 0⁺`, so `r⁸G(r) = Φ(m r) → Φ(0)`.

DERIVED: `0` is the point approached and `Φ`'s base point; `8` is the scaling form's. -/
theorem freeShortDistance_of_scalingForm {G : ℝ → ℝ} (h : FreeScalingForm G) :
    FreeShortDistance G := by
  obtain ⟨m, Φ, hm, hΦc, hΦ0, hG⟩ := h
  refine ⟨Φ 0, hΦ0, ?_⟩
  have hmr : Tendsto (fun r : ℝ => m * r) (𝓝[>] (0 : ℝ)) (𝓝[Set.Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun r : ℝ => m * r) (𝓝 0) (𝓝 (m * 0)) :=
        (continuous_const_mul m).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      exact mul_nonneg hm hr0.le
  have hlim : Tendsto (fun r : ℝ => Φ (m * r)) (𝓝[>] (0 : ℝ)) (𝓝 (Φ 0)) :=
    hΦc.tendsto.comp hmr
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  rw [hG r hr0, mul_div_cancel₀ _ (pow_ne_zero 8 hr0.ne')]

#print axioms freeShortDistance_of_scalingForm

/-- **Every free composite, massless or massive, fails Y.**

DERIVED: no numeral beyond the definitions'. -/
theorem not_af_of_scalingForm {G : ℝ → ℝ} (h : FreeScalingForm G) : ¬ AFShortDistance G :=
  not_af_of_free (freeShortDistance_of_scalingForm h)

#print axioms not_af_of_scalingForm

/-- **The massless composite is the case `m = 0`** of the free scaling form, with the constant profile.

DERIVED: `0` is the mass and the sign of `C`; `8` is `freeMassless`'s. -/
theorem scalingForm_freeMassless {C : ℝ} (hC : 0 < C) : FreeScalingForm (freeMassless C) :=
  ⟨0, fun _ => C, le_refl 0, continuousWithinAt_const, hC, fun _ _ => rfl⟩

#print axioms scalingForm_freeMassless

/-! ## 3. Y excludes every power law -/

/-- **A power-suppressed `r⁸G` fails Y.** If `r⁸G(r) = O(r^ε)` as `r → 0⁺` for some `ε > 0`, then
`r⁸G(r)(log r)² = O(r^ε (log r)²)`, and `r^ε (log r)² = (log r · r^{ε/2})² → 0`
(`tendsto_log_mul_rpow_nhdsGT_zero`), so the limit `C` of Y is `0`.

DERIVED: `8` and `2` as in `AFShortDistance`; `0` is the sign of `ε`, the point approached and the
forced limit; `2` in `ε/2` splits `r^ε` into the two factors of the square (`add_halves`). -/
theorem not_af_of_isBigO_rpow {G : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hO : (fun r : ℝ => r ^ 8 * G r) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ ε)) :
    ¬ AFShortDistance G := by
  rintro ⟨C, hC, hlim⟩
  have hsq : Tendsto (fun r : ℝ => r ^ ε * Real.log r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (half_pos hε)).pow 2
    rw [zero_pow two_ne_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hsplit : r ^ ε = r ^ (ε / 2) * r ^ (ε / 2) := by
      rw [← Real.rpow_add hr0, add_halves]
    rw [hsplit]
    ring
  have hO2 : (fun r : ℝ => r ^ 8 * G r * Real.log r ^ 2) =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => r ^ ε * Real.log r ^ 2) :=
    hO.mul (isBigO_refl (fun r : ℝ => Real.log r ^ 2) _)
  exact hC.ne' (tendsto_nhds_unique hlim (hO2.trans_tendsto hsq))

#print axioms not_af_of_isBigO_rpow

/-- **No scale-invariant two-point function satisfies Y.** If `G(r) = K · r^{−2Δ}` on `r > 0` with
`K ≠ 0`, for any real scaling dimension `Δ`, then `r⁸G(r) = K r^{8−2Δ}` and:

* `8 − 2Δ < 0`: `r^{8−2Δ} → ∞` (`tendsto_rpow_neg_nhdsGT_zero`), against the limit `0` Y forces;
* `8 − 2Δ = 0`: `r⁸G = K ≠ 0` (`not_af_of_scaled_tendsto_ne_zero`);
* `8 − 2Δ > 0`: `r⁸G = O(r^{8−2Δ})` (`not_af_of_isBigO_rpow`).

DERIVED: `8` as in `AFShortDistance`; `2` in `2Δ` is the two insertions of a field of dimension `Δ`;
`0` is the excluded amplitude, the split of the three cases and the point approached. -/
theorem not_af_of_conformal {G : ℝ → ℝ} {K : ℝ} (hK : K ≠ 0) (Δ : ℝ)
    (hG : ∀ r : ℝ, 0 < r → G r = K * r ^ (-(2 * Δ))) : ¬ AFShortDistance G := by
  intro hY
  have hscaled : ∀ r : ℝ, 0 < r → r ^ 8 * G r = K * r ^ (8 - 2 * Δ) := by
    intro r hr
    rw [hG r hr, show (8 : ℝ) - 2 * Δ = ((8 : ℕ) : ℝ) + -(2 * Δ) by push_cast; ring,
      Real.rpow_add hr, Real.rpow_natCast]
    ring
  have hev : (fun r : ℝ => r ^ 8 * G r) =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => K * r ^ (8 - 2 * Δ)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    exact hscaled r hr0
  have hs : Tendsto (fun r : ℝ => r ^ 8 * G r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    scaled_tendsto_zero_of_af hY
  have hsup : Tendsto (fun r : ℝ => K * r ^ (8 - 2 * Δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hs.congr' hev
  rcases lt_trichotomy (8 - 2 * Δ) 0 with hneg | hzero | hpos
  · have h := hsup.const_mul K⁻¹
    rw [mul_zero] at h
    have hpow : Tendsto (fun r : ℝ => r ^ (8 - 2 * Δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      h.congr (fun r => inv_mul_cancel_left₀ hK _)
    exact not_tendsto_nhds_of_tendsto_atTop (tendsto_rpow_neg_nhdsGT_zero hneg) 0 hpow
  · have hconst : Tendsto (fun r : ℝ => K * r ^ (8 - 2 * Δ)) (𝓝[>] (0 : ℝ)) (𝓝 K) :=
      tendsto_const_nhds.congr (fun r => by simp only [hzero, Real.rpow_zero, mul_one])
    exact hK (tendsto_nhds_unique hconst hsup)
  · have hO : (fun r : ℝ => r ^ 8 * G r) =O[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ (8 - 2 * Δ)) :=
      hev.trans_isBigO ((isBigO_refl (fun r : ℝ => r ^ (8 - 2 * Δ)) _).const_mul_left K)
    exact not_af_of_isBigO_rpow hpos hO hY

#print axioms not_af_of_conformal

/-- The two-point function `r / r⁸ = r⁻⁷` of a scale-invariant composite of dimension `7/2`.

DERIVED: `8` as in `AFShortDistance`; the numerator `r` makes the exponent `8 − 1 = 7 = 2·(7/2)`.
CHOSEN: dimension `7/2`, any dimension below `4` serves. -/
noncomputable def powerSeven (r : ℝ) : ℝ := r / r ^ 8

#print axioms powerSeven

/-- **Y is strictly stronger than the suppressed form.** `powerSeven` has `r⁸G(r) = r → 0` and
does not satisfy Y (`not_af_of_isBigO_rpow` at `ε = 1`).

DERIVED: `8` is `powerSeven`'s; `0` is the point approached; `1` is the exponent of `r⁸·powerSeven r = r`. -/
theorem suppressed_strictly_weaker :
    ShortDistanceSuppressed powerSeven ∧ ¬ AFShortDistance powerSeven := by
  have hev : (fun r : ℝ => r ^ 8 * powerSeven r) =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => r ^ (1 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    rw [powerSeven, mul_div_cancel₀ r (pow_ne_zero 8 hr0.ne'), Real.rpow_one]
  refine ⟨?_, not_af_of_isBigO_rpow one_pos (hev.trans_isBigO (isBigO_refl _ _))⟩
  have hid : Tendsto (fun r : ℝ => r ^ (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact h.congr (fun r => (Real.rpow_one r).symm)
  exact hid.congr' hev.symm

#print axioms suppressed_strictly_weaker

/-- A two-point function of the asymptotic-freedom form: `C · (r⁸)⁻¹ · ((log r)²)⁻¹`.

DERIVED: `8` and `2` as in `AFShortDistance`. -/
noncomputable def afWitness (C : ℝ) (r : ℝ) : ℝ := C * (r ^ 8)⁻¹ * (Real.log r ^ 2)⁻¹

#print axioms afWitness

/-- **Y is satisfiable.** `afWitness C` satisfies it at `C > 0`: on `(0, 1)`, `r⁸·afWitness C r·(log r)² = C`.

DERIVED: `0` is the sign of `C` and the point approached; `1` is where `log` vanishes; `8` and `2` are
`afWitness`'s. -/
theorem af_satisfiable {C : ℝ} (hC : 0 < C) : AFShortDistance (afWitness C) := by
  refine ⟨C, hC, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  have hp : r ^ 8 ≠ 0 := pow_ne_zero 8 hr.1.ne'
  have hL : Real.log r ^ 2 ≠ 0 := pow_ne_zero 2 (Real.log_neg hr.1 hr.2).ne
  show C = r ^ 8 * (C * (r ^ 8)⁻¹ * (Real.log r ^ 2)⁻¹) * Real.log r ^ 2
  calc C = C * (r ^ 8 * (r ^ 8)⁻¹) * ((Real.log r ^ 2)⁻¹ * Real.log r ^ 2) := by
        rw [mul_inv_cancel₀ hp, inv_mul_cancel₀ hL, mul_one, mul_one]
    _ = r ^ 8 * (C * (r ^ 8)⁻¹ * (Real.log r ^ 2)⁻¹) * Real.log r ^ 2 := by ring

#print axioms af_satisfiable

/-- **Y is invariant under a positive rescaling of the composite.** If `G' = Z·G` on `r > 0` with
`Z > 0`, Y for `G` gives Y for `G'` with the constant `Z·C`.

DERIVED: `0` is the sign of `Z` and of `r`; `8` and `2` are `AFShortDistance`'s. -/
theorem af_of_const_mul {G G' : ℝ → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hG' : ∀ r : ℝ, 0 < r → G' r = Z * G r) (h : AFShortDistance G) : AFShortDistance G' := by
  obtain ⟨C, hC, hlim⟩ := h
  refine ⟨Z * C, mul_pos hZ hC, (hlim.const_mul Z).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  rw [hG' r hr0]
  ring

#print axioms af_of_const_mul

/-! ## 4. The running coupling of the two-loop spacing -/

/-- `1/(2·(11N/(3·16π²))) = 24π²/(11N)` for `N ≠ 0`: `24π²/(11N)` is `1/(2b₀)` at the gauge-coupling
normalisation `b₀ = 11N/(3·16π²)` of `AsymptoticScaling.aRun`.

DERIVED: `1` and `2` are `1/(2b₀)`; `11`, `3`, `16` and the `2` of `π ^ 2` are `b₀`; the quotient is
`3·16π²/(2·11N)`, so `24 = 3·16/2` and `11` on the right; `0` in `hN` is what `field_simp` needs. -/
theorem inv_two_b0 {N : ℝ} (hN : N ≠ 0) :
    1 / (2 * (11 * N / (3 * (16 * Real.pi ^ 2)))) = 24 * Real.pi ^ 2 / (11 * N) := by
  field_simp
  ring

#print axioms inv_two_b0

/-- `(2N/β)·(12π²β/(11N²)) = 24π²/(11N)` for `N ≠ 0`, `β ≠ 0`: the coupling `g² = 2N/β` times the
exponential's argument of `aRun`.

DERIVED: `2` in `2N` is `g² = 2N/β`; `12`, `11` and the `2`s of `π ^ 2` and `N ^ 2` are `aRun`'s
exponential argument (`AsymptoticScaling.one_over_four_N_b0`); `24 = 2·12` and `11` on the right are
the product; `0` in the hypotheses is what `field_simp` needs. -/
theorem coupling_mul_exponent {N β : ℝ} (hN : N ≠ 0) (hβ : β ≠ 0) :
    2 * N / β * (12 * Real.pi ^ 2 * β / (11 * N ^ 2)) = 24 * Real.pi ^ 2 / (11 * N) := by
  field_simp
  ring

#print axioms coupling_mul_exponent

/-- **The two-loop spacing tends to `0` from above.** For `1 ≤ N`, `aRun N β → 0⁺` as `β → ∞`:
positive at `β > 0` (`aRun_pos`) and eventually below every positive bound
(`WeakCouplingWindow.eventually_aRun_le`).

DERIVED: `1` is the least colour count; `0` is the limit and the sign; `2` halves the target so the
bound is strict. -/
theorem tendsto_aRun_nhdsGT_zero {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (aRun N) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
      exact hb.trans (aRun_pos hN hβ)
    · filter_upwards [MassGap.WeakCouplingWindow.eventually_aRun_le hN (half_pos hb)] with β hβ
      linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact Set.mem_Ioi.mpr (aRun_pos hN hβ)

#print axioms tendsto_aRun_nhdsGT_zero

/-- **The coupling times the logarithm of the spacing tends to `1/(2b₀)`.** For `1 ≤ N`,

    (2N/β) · (−log aRun N β)  →  24π²/(11N)  =  1/(2b₀)        as β → ∞.

With `u = 24π²β/(11N²)`, `log aRun N β = (51/121)·log u − 12π²β/(11N²)` (`Real.log_mul`,
`Real.log_rpow`, `Real.log_exp`), so the product is `24π²/(11N) − (102N/121)·(log u)/β`, and
`(log u)/β → 0` (`Real.isLittleO_log_id_atTop`). The two-loop term `51/121 = b₁/(2b₀²)` enters only
through `(log u)/β` and drops out: `ḡ²(a) ∼ 1/(2b₀ log(1/a))` at the tree's two-loop spacing.

DERIVED: `2` in `2N` is `g² = 2N/β`; `24`, `11`, `12` and the `2`s of `π ^ 2` and `N ^ 2` are `aRun`'s
constants (`inv_two_b0`, `coupling_mul_exponent`); `51/121` is `aRun`'s exponent and
`102/121 = 2·51/121` its product with the `2` of `2N`; `1` is the least colour count; `0` is the sign of
`β` and the limit of `(log u)/β`. -/
theorem coupling_mul_neg_log_aRun_tendsto {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun β : ℝ => 2 * (N : ℝ) / β * -Real.log (aRun N β)) atTop
      (𝓝 (24 * Real.pi ^ 2 / (11 * (N : ℝ)))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 24 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) := ⟨_, rfl⟩
  have hkpos : 0 < k := by
    rw [hk]
    exact div_pos (mul_pos (by norm_num) (pow_pos Real.pi_pos 2))
      (mul_pos (by norm_num) (pow_pos hN0 2))
  have hlogβ : Tendsto (fun β : ℝ => Real.log β / β) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconst : Tendsto (fun β : ℝ => Real.log k / β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlogkβ : Tendsto (fun β : ℝ => Real.log (k * β) / β) atTop (𝓝 0) := by
    have hsum : Tendsto (fun β : ℝ => Real.log k / β + Real.log β / β) atTop (𝓝 (0 + 0)) :=
      hconst.add hlogβ
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    rw [Real.log_mul hkpos.ne' hβ.ne', add_div]
  have hlim : Tendsto (fun β : ℝ => 24 * Real.pi ^ 2 / (11 * (N : ℝ))
      - 102 * (N : ℝ) / 121 * (Real.log (k * β) / β)) atTop
      (𝓝 (24 * Real.pi ^ 2 / (11 * (N : ℝ)) - 102 * (N : ℝ) / 121 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hlogkβ)
  rw [mul_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  have hu : 0 < k * β := mul_pos hkpos hβ
  have hbase : (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) = k * β := by
    rw [hk]
    ring
  have hA : aRun N β = (k * β) ^ (51 / 121 : ℝ)
      * Real.exp (-(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) := by
    unfold MassGap.AsymptoticScaling.aRun
    rw [hbase]
  have hlogA : Real.log (aRun N β)
      = 51 / 121 * Real.log (k * β) + -(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by
    rw [hA, Real.log_mul (Real.rpow_pos_of_pos hu _).ne' (Real.exp_pos _).ne',
      Real.log_rpow hu, Real.log_exp]
  have key := coupling_mul_exponent hN0.ne' hβ.ne'
  rw [hlogA]
  linear_combination (-1 : ℝ) * key

#print axioms coupling_mul_neg_log_aRun_tendsto

/-- **Y read along the two-loop spacing: the square of the running coupling.** For `1 ≤ N`,
`AFShortDistance G` gives a `C' > 0` with

    aRun N β ⁸ · G(aRun N β) / (2N/β)²  →  C'        as β → ∞,

`C' = C·(2b₀)²`, `2b₀ = 11N/(24π²)`: at the separation `a = aRun N β`, `a⁸G(a)` is `C'` times the square
of the running coupling `g² = 2N/β` at that scale. The proof composes Y with `aRun N β → 0⁺`
(`tendsto_aRun_nhdsGT_zero`) and divides by the square of `(2N/β)·(−log a) → 1/(2b₀)`
(`coupling_mul_neg_log_aRun_tendsto`).

DERIVED: `8` and the square are `AFShortDistance`'s and the square of `g²`; `2` in `2N` is `g² = 2N/β`;
`24`, `11` and the `2` of `π ^ 2` are `1/(2b₀)` (`inv_two_b0`); `1` is the least colour count and the
level `aRun N β < 1` below which `log` is negative; `0` is the sign of `C'` and of `β`. CHOSEN: `1/2`,
a level below `1` that `aRun N β` eventually stays under; any level in `(0, 1)` serves. -/
theorem af_along_aRun {N : ℕ} (hN : 1 ≤ N) {G : ℝ → ℝ} (hY : AFShortDistance G) :
    ∃ C' : ℝ, 0 < C' ∧
      Tendsto (fun β : ℝ => aRun N β ^ 8 * G (aRun N β) / (2 * (N : ℝ) / β) ^ 2) atTop (𝓝 C') := by
  obtain ⟨C, hC, hlim⟩ := hY
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc0 : (0 : ℝ) < 24 * Real.pi ^ 2 / (11 * (N : ℝ)) :=
    div_pos (mul_pos (by norm_num) (pow_pos Real.pi_pos 2)) (mul_pos (by norm_num) hN0)
  have h1 : Tendsto (fun β : ℝ => aRun N β ^ 8 * G (aRun N β) * Real.log (aRun N β) ^ 2) atTop
      (𝓝 C) := hlim.comp (tendsto_aRun_nhdsGT_zero hN)
  have h2 : Tendsto (fun β : ℝ => (2 * (N : ℝ) / β * -Real.log (aRun N β)) ^ 2) atTop
      (𝓝 ((24 * Real.pi ^ 2 / (11 * (N : ℝ))) ^ 2)) :=
    (coupling_mul_neg_log_aRun_tendsto hN).pow 2
  have h3 : Tendsto (fun β : ℝ => aRun N β ^ 8 * G (aRun N β) * Real.log (aRun N β) ^ 2
      / (2 * (N : ℝ) / β * -Real.log (aRun N β)) ^ 2) atTop
      (𝓝 (C / (24 * Real.pi ^ 2 / (11 * (N : ℝ))) ^ 2)) :=
    h1.div h2 (pow_pos hc0 2).ne'
  refine ⟨C / (24 * Real.pi ^ 2 / (11 * (N : ℝ))) ^ 2, div_pos hC (pow_pos hc0 2), h3.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    MassGap.WeakCouplingWindow.eventually_aRun_le hN (by norm_num : (0 : ℝ) < 1 / 2)]
    with β hβ hsmall
  have hApos : 0 < aRun N β := aRun_pos hN hβ
  have hL : Real.log (aRun N β) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Real.log_neg hApos (by linarith)).ne
  rw [mul_pow, neg_sq]
  exact mul_div_mul_right _ _ hL

#print axioms af_along_aRun

/-! ## 5. The lattice family at a fixed physical separation -/

/-- **Continuum limit at fixed separation.** `L β r → G r` as `β → ∞` at every `r > 0`.

DERIVED: `0` is the sign of the separation. -/
def ContinuumTwoPoint (L : ℝ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → Tendsto (fun β => L β r) atTop (𝓝 (G r))

#print axioms ContinuumTwoPoint

/-- **Y along a family.** One `C > 0` such that for every `ε > 0` there is `δ > 0` with, at every
separation `0 < r < δ`, `|r⁸ · L β r · (log r)² − C| ≤ ε` for every large `β` (the threshold in `β` may
depend on `r`): the asymptotic-freedom form at fixed physical separation, reached as the spacing runs to
zero, the analogue of `WeakCouplingWindow.FixedWindowDecay` for Y.

DERIVED: `8` and `2` as in `AFShortDistance`; `0` is the sign of `C`, `ε`, `δ` and `r`. -/
def FamilyAF (L : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
    ∀ᶠ β in atTop, |r ^ 8 * L β r * Real.log r ^ 2 - C| ≤ ε

#print axioms FamilyAF

/-- **The family form passes to the continuum.** Under `ContinuumTwoPoint L G`, `FamilyAF L` gives
`AFShortDistance G`: at each `0 < r < δ` the bound `≤ ε/2` passes to the limit in `β`
(`le_of_tendsto`).

DERIVED: `0` is the sign of `r`, `ε` and the base point; `2` in `ε/2` leaves room for the strict
inequality of the metric criterion; `8` and the square are `AFShortDistance`'s. -/
theorem af_of_familyAF {L : ℝ → ℝ → ℝ} {G : ℝ → ℝ} (hconv : ContinuumTwoPoint L G)
    (hL : FamilyAF L) : AFShortDistance G := by
  obtain ⟨C, hC, hunif⟩ := hL
  refine ⟨C, hC, Metric.tendsto_nhdsWithin_nhds.mpr (fun ε hε => ?_)⟩
  obtain ⟨δ, hδ, hr⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro r hrpos hrd
  have hr0 : (0 : ℝ) < r := hrpos
  have hrδ : r < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr0] at hrd
    exact hrd
  have hT : Tendsto (fun β => |r ^ 8 * L β r * Real.log r ^ 2 - C|) atTop
      (𝓝 |r ^ 8 * G r * Real.log r ^ 2 - C|) :=
    ((((hconv r hr0).const_mul (r ^ 8)).mul_const (Real.log r ^ 2)).sub_const C).abs
  have hle : |r ^ 8 * G r * Real.log r ^ 2 - C| ≤ ε / 2 := le_of_tendsto hT (hr r hr0 hrδ)
  show dist (r ^ 8 * G r * Real.log r ^ 2) C < ε
  rw [Real.dist_eq]
  linarith

#print axioms af_of_familyAF

/-- **The continuum form gives the family form.** Under `ContinuumTwoPoint L G`, `AFShortDistance G`
gives `FamilyAF L`: at `0 < r < δ` the continuum value is within `ε/2` of `C`, and the family value is
within `ε/2` of the continuum value for every large `β`.

DERIVED: `0` is the sign of `r`, `ε` and the base point; `2` in `ε/2` splits the triangle inequality;
`8` and the square are `AFShortDistance`'s. -/
theorem familyAF_of_af {L : ℝ → ℝ → ℝ} {G : ℝ → ℝ} (hconv : ContinuumTwoPoint L G)
    (hY : AFShortDistance G) : FamilyAF L := by
  obtain ⟨C, hC, hlim⟩ := hY
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun r hr0 hrδ => ?_⟩
  have hmem : r ∈ Set.Ioi (0 : ℝ) := hr0
  have hdist : dist r 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr0]
    exact hrδ
  have hG : dist (r ^ 8 * G r * Real.log r ^ 2) C < ε / 2 := hball hmem hdist
  have hT : Tendsto (fun β => r ^ 8 * L β r * Real.log r ^ 2) atTop
      (𝓝 (r ^ 8 * G r * Real.log r ^ 2)) :=
    ((hconv r hr0).const_mul (r ^ 8)).mul_const (Real.log r ^ 2)
  filter_upwards [Metric.tendsto_nhds.mp hT (ε / 2) (half_pos hε)] with β hβ
  have htri := dist_triangle (r ^ 8 * L β r * Real.log r ^ 2) (r ^ 8 * G r * Real.log r ^ 2) C
  rw [← Real.dist_eq]
  linarith

#print axioms familyAF_of_af

/-- **The family form is the continuum statement.** Under `ContinuumTwoPoint L G`,
`FamilyAF L ↔ AFShortDistance G`.

DERIVED: no numeral beyond the definitions'. -/
theorem familyAF_iff {L : ℝ → ℝ → ℝ} {G : ℝ → ℝ} (hconv : ContinuumTwoPoint L G) :
    FamilyAF L ↔ AFShortDistance G :=
  ⟨af_of_familyAF hconv, familyAF_of_af hconv⟩

#print axioms familyAF_iff

/-- **The lattice `tr F²` density at a site.** `ThreePointN.blockObs` with side `1` at
`ThreePointN.tripleBase n 1 = n·e₀`: the plaquette energies of the six planes `μ < ν` based at `n·e₀`.

DERIVED: the side `1` is one lattice site; the block index `1` selects the base `n·e₀` among
`tripleBase`'s three. -/
noncomputable def siteObs (N n : ℕ) : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) :=
  MassGap.ThreePointN.blockObs N (MassGap.ThreePointN.tripleBase n 1) 1

#print axioms siteObs

/-- **The lattice two-point function at physical separation `r`.** The connected two-point function,
under `PeriodicState.periodicState hN β`, of `siteObs N 0` (the origin) and
`siteObs N ⌈r / aRun N β⌉₊` (at `⌈r / aRun N β⌉₊·e₀`), divided by `aRun N β ⁸`.

At weak coupling each plaquette energy is `a⁴·g₀²·tr F²/(2N)` plus operators of higher dimension
(`ThreePointN.blockObs`), so `aRun N β ⁻⁴ · siteObs` is the lattice form of the bare `g₀²·tr F²/(2N)`.
The renormalisation-group invariant composite is `(β(g₀)/2g₀)·F^aF^a = −(b₀/2)·g₀²F^aF^a·(1 + O(g₀²))`;
the constant is absorbed by `af_of_const_mul`, and the factor `1 + O(g₀²)` tends to `1` as `β → ∞` at
fixed `r`. The limit `G`, where it exists, is therefore a constant multiple of the invariant composite's
two-point function, the normalisation in which `AFShortDistance` carries `(log r)²`. The identity
mixing drops out of `cov2`.

DERIVED: `8 = 2·4`: each of the two insertions carries `a⁴`; `0` is the origin. -/
noncomputable def latticeTwoPoint (N : ℕ) (hN : N ≠ 0) (β r : ℝ) : ℝ :=
  MassGap.ThreePointN.cov2 (MassGap.PeriodicState.periodicState hN β) (siteObs N 0)
      (siteObs N (MassGap.ThreePointN.latUnits r (aRun N β)))
    / aRun N β ^ 8

#print axioms latticeTwoPoint

/-- **The continuum two-point function of the Wilson family (part of E).** `latticeTwoPoint N hN β r`
converges to `G r` as `β → ∞` at every fixed physical separation `r > 0`. Open.

DERIVED: `0` is the excluded rank in `hN`. -/
def WilsonContinuumTwoPoint (N : ℕ) (hN : N ≠ 0) (G : ℝ → ℝ) : Prop :=
  ContinuumTwoPoint (latticeTwoPoint N hN) G

#print axioms WilsonContinuumTwoPoint

/-- **Requirement Y on the Wilson family.** `FamilyAF` of `latticeTwoPoint N hN`. Open.

DERIVED: `0` is the excluded rank in `hN`. -/
def WilsonLatticeAF (N : ℕ) (hN : N ≠ 0) : Prop :=
  FamilyAF (latticeTwoPoint N hN)

#print axioms WilsonLatticeAF

/-- **On the Wilson family, the lattice form is the continuum statement.** Under
`WilsonContinuumTwoPoint N hN G`, `WilsonLatticeAF N hN ↔ AFShortDistance G`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem wilson_af_iff {N : ℕ} (hN : N ≠ 0) {G : ℝ → ℝ} (hconv : WilsonContinuumTwoPoint N hN G) :
    WilsonLatticeAF N hN ↔ AFShortDistance G :=
  familyAF_iff hconv

#print axioms wilson_af_iff

/-- **N and Y on the Wilson family.** Y separates the continuum two-point function from every free
composite, massless or massive; N separates the lattice block composites from Gaussian laws and from
the free massless value. At `N ≠ 0`, from `WilsonContinuumTwoPoint N hN G`, `WilsonLatticeAF N hN` and
`ThreePointN.WilsonThreePointSeparation N hN`:

1. `G` satisfies Y;
2. `G` is not in the free class (`r⁸G → C > 0`);
3. `G` has no free scaling form `Φ(m r)/r⁸`, massless or massive;
4. `G` is no pure power law `K r^{−2Δ}`, `K ≠ 0`, on `r > 0`;
5. along `aRun N`, `a⁸G(a)/(2N/β)² → C' > 0`;
6. there are `0 < ℓ < D` such that along every `β i → ∞` the three block composites of physical size
   `ℓ` and separation `D` are `ThreePointN.ThreePointSeparated` under the periodic state — the
   normalised statistic `ThreePointN.sepRatio = cum3²/|cov2·cov2·cov2|` is eventually at least one
   `c > 0`, so the connected three-point function is eventually non-zero, and `0` is the statistic's
   value for every Gaussian law and for the free massless gauge field in the duality matrix model
   (`ThreePointN.freeSepRatio_of_duality`).

At `N = 1` the group is trivial, `latticeTwoPoint` is `0` and `WilsonLatticeAF` fails, so the
hypotheses carry content at `2 ≤ N`.

DERIVED: `8` and the square on the logarithm as in `AFShortDistance`; `2` in `2Δ` is the two
insertions of a field of dimension `Δ` (`not_af_of_conformal`); `2` in `2N/β` is `g² = 2N/β` and the
square on it is `af_along_aRun`'s; `0` is the excluded amplitude, colour count and sign; `0`, `1`, `2`
index the three blocks; `1` is the least colour count, from `hN`. -/
theorem wilson_yang_mills_separated {N : ℕ} (hN : N ≠ 0) {G : ℝ → ℝ}
    (hconv : WilsonContinuumTwoPoint N hN G) (hY : WilsonLatticeAF N hN)
    (hsep : MassGap.ThreePointN.WilsonThreePointSeparation N hN) :
    AFShortDistance G ∧ ¬ FreeShortDistance G ∧ ¬ FreeScalingForm G ∧
      (∀ K Δ : ℝ, K ≠ 0 → ¬ ∀ r : ℝ, 0 < r → G r = K * r ^ (-(2 * Δ))) ∧
      (∃ C' : ℝ, 0 < C' ∧ Tendsto (fun β : ℝ => aRun N β ^ 8 * G (aRun N β) / (2 * (N : ℝ) / β) ^ 2)
        atTop (𝓝 C')) ∧
      ∃ ℓ D : ℝ, 0 < ℓ ∧ ℓ < D ∧ ∀ β : ℕ → ℝ, Tendsto β atTop atTop →
        MassGap.ThreePointN.ThreePointSeparated
          (fun i => MassGap.PeriodicState.periodicState hN (β i))
          (fun i => MassGap.ThreePointN.tripleObs N ℓ D (β i) 0)
          (fun i => MassGap.ThreePointN.tripleObs N ℓ D (β i) 1)
          (fun i => MassGap.ThreePointN.tripleObs N ℓ D (β i) 2) := by
  have hAF : AFShortDistance G := (wilson_af_iff hN hconv).mp hY
  refine ⟨hAF, fun hf => not_af_of_free hf hAF, fun hs => not_af_of_scalingForm hs hAF,
    fun K Δ hK hG => not_af_of_conformal hK Δ hG hAF,
    af_along_aRun (Nat.one_le_iff_ne_zero.mpr hN) hAF,
    MassGap.ThreePointN.wilson_threePointSeparated hN hsep⟩

#print axioms wilson_yang_mills_separated

end MassGap.ShortDistanceY
