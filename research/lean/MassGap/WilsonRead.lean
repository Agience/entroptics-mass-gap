import MassGap.WilsonReal
import MassGap.Moment

/-!
# MassGap.WilsonRead — a `Moment.Read` built from the `SU(2)` two-plaquette Wilson Gibbs measure

`wilsonCorrReal β d` is the Gibbs expectation `⟨φ_{p₀} · φ_{p_d}⟩_β` of the `SU(2)` system `sysReal`
built in `MassGap.WilsonReal`: eight links, two plaquettes, each plaquette a four-link ordered
holonomy `U₀U₁U₂⁻¹U₃⁻¹`, the Wilson density `φ_W(g) = 1 - ½ Re tr g`, integrated against normalised
Haar measure. `wilsonReadReal β` is the `Moment.Read 1` it supports.

Both `Moment.Read` obligations are theorems here rather than hypotheses. Nonnegativity at every lag
(`wilsonCorrReal_nonneg`) is the Gibbs average of a product of two nonnegative densities
(`WilsonAction.wilsonDensity_nonneg`) under a positive state (`WilsonReal.sysReal_expect_nonneg`).
Positive total mass (`sum_wilsonCorrReal_pos`) is reached in four steps:

1. `expect_ge_haar_of_nonneg` — `⟨O⟩_β ≥ e^{-8|β|} ∫ O dHaar` for a bounded nonnegative observable.
   `sysReal`'s action lies in `[0, 4]`, so its Boltzmann weight lies in `[e^{-4|β|}, e^{4|β|}]`; the
   coupling enters only through that constant, so positivity at every `β` follows from positivity
   under plain Haar.
2. `integral_re_trace_hol_zero` — `∫ Re tr(hol p₀) dvol = 0`, from the centre of `SU(2)`. Translating
   link `0` by `z = -1` preserves the product Haar measure (`linkTranslate_measurePreserving`) and
   sends `hol` to `-hol` (`hol_linkTranslate`), so the integral equals its own negative.
3. `integral_plaqObs_eq_one` — `∫ φ₀ dvol = 1`, since `φ_W = 1 - ½ Re tr`.
4. `integral_plaqObs_sq_pos` — `0 < ∫ φ₀² dvol`, from the pointwise `(φ₀ - 1)² ≥ 0` and
   `integral_mono`; the proof reaches `≥ 1` and exports positivity only.

The last two declarations concern the finite-aperture condition. `wilson_tension_lt_floor` puts the
read's tension below `(1/4)·log 3` given a bounded lag second moment `hB` and the scaling condition
`hscale`. `two_plaquette_aperture_forces_tiny_B` computes what `hscale` demands at this aperture.

## Scope

`sysReal` is two plaquettes on eight links — one gauge cell, with no time direction and no transfer
operator. Nothing here identifies the read's tension with a transfer eigenvalue.

The read has `N = 1`, so `hscale` reduces to `B < 2(1 - 3^{-1/4})/π²`. The system's own lag moment is
larger: the two plaquettes share no link, so `ρ(1) = ⟨φ₀⟩⟨φ₁⟩` at every coupling
(`WilsonReal.expect_plaqObs_factor`), and at `β = 0` that is `1` against `ρ(0) = ∫ φ₀² = 5/4`, giving
a second moment of `4/9`. So `hB` and `hscale` are jointly unsatisfiable on `sysReal`, and
`wilson_tension_lt_floor` has no instance there. `Complete.confinement_of_growth_bound` states the
condition at every sufficiently large aperture; the aperture factor scales as `1/(N+1)²`.

Footprint: the three foundational axioms only, for every declaration in this file. In particular not
`Complete.wilson_reflection_positive_at`, which the rest of the development uses for the opaque
`Complete.wilsonCorr` and which does not appear here.
-/

namespace MassGap.WilsonRead

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonReal MassGap.WilsonAction
open MassGap.CompactGauge
open MeasureTheory

/-! The plaquette action-density observable is `WilsonReal.plaqObs`, defined there with its
nonnegativity (`plaqObs_nonneg`), its bound (`plaqObs_le_two`), its measurability
(`measurable_plaqObs`) and its gauge invariance (`plaqObs_gauge_invariant`). Nothing is redefined
here. -/

/-- The two-plaquette correlation at lag `d`: `⟨φ_{p₀} · φ_{p_d}⟩_β`, the Gibbs expectation of the
product of the two plaquette densities against normalised Haar with the Wilson Boltzmann weight.

This is the profile `wilsonReadReal` is built from.

DERIVED: `2` is the number of plaquettes of `sysReal`, so the lag index ranges over `Fin 2`. It is
the only numeral in the statement. -/
noncomputable def wilsonCorrReal (β : ℝ) (d : Fin 2) : ℝ :=
  sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs d U)

/-- `0 ≤ wilsonCorrReal β d` at every real coupling and every lag.

The integrand is a product of two nonnegative densities (`plaqObs_nonneg`) and the Gibbs state is
positive (`sysReal_expect_nonneg`), so no reflection-positivity input enters. This is the property
`Complete.wilson_reflection_positive_at` asserts for the opaque correlation.

DERIVED: `2` is the number of plaquettes of `sysReal`, the range of the lag index; `0` is the lower
bound concluded. -/
theorem wilsonCorrReal_nonneg (β : ℝ) (d : Fin 2) : 0 ≤ wilsonCorrReal β d :=
  sysReal_expect_nonneg β _ (fun U => mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg d U))

/-- `wilsonCorrReal β d ≤ 4` at every real coupling and every lag.

Each density is at most `2` (`plaqObs_le_two`) and the Gibbs state does not increase a uniform bound
(`sysReal_expect_abs_le`), so the product is bounded by `4`.

DERIVED: `4` is the product of the two density bounds, `2` each, from
`WilsonReal.plaqObs_le_two`. `2` is also the number of plaquettes, the range of the lag index. -/
theorem wilsonCorrReal_le_four (β : ℝ) (d : Fin 2) : wilsonCorrReal β d ≤ 4 := by
  have hmeas : Measurable (fun U => plaqObs 0 U * plaqObs d U) :=
    (measurable_plaqObs 0).mul (measurable_plaqObs d)
  have habs : |wilsonCorrReal β d| ≤ 4 :=
    sysReal_expect_abs_le β _ hmeas 4 (fun U => by
      rw [abs_of_nonneg (mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg d U))]
      calc plaqObs 0 U * plaqObs d U
          ≤ 2 * 2 := mul_le_mul (plaqObs_le_two 0 U) (plaqObs_le_two d U)
              (plaqObs_nonneg d U) (by norm_num)
        _ = 4 := by norm_num)
  exact le_trans (le_abs_self _) habs

/-! ### Reducing `hpos` at every coupling to one Haar fact

The Gibbs state is sandwiched by the Haar integral, because `sysReal`'s action is bounded in `[0,4]`
(`sysReal_action_nonneg`, `sysReal_action_le`) so its Boltzmann weight is bounded in
`[e^{−4|β|}, e^{4|β|}]`. For a nonnegative observable that gives `⟨O⟩_β ≥ e^{−8|β|} ∫ O dHaar`, so
positivity at EVERY coupling follows from positivity under plain Haar — one measure, no `β`. -/

/-- `Real.exp (-(4 * |β|)) ≤ sysReal.boltz β U` at every configuration and every real coupling.

The action lies in `[0, 4]` (`sysReal_action_nonneg`, `sysReal_action_le`), so `β * action` is at
most `|β| * 4`. The mirror of `sysReal_boltz_le`.

DERIVED: `4` is the upper bound on `sysReal`'s action — two plaquettes at density at most `2`
each. -/
theorem sysReal_boltz_ge (β : ℝ) (U : sysReal.Config) :
    Real.exp (-(4 * |β|)) ≤ sysReal.boltz β U := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : β * sysReal.action U ≤ |β| * sysReal.action U :=
    mul_le_mul_of_nonneg_right (le_abs_self β) (sysReal_action_nonneg U)
  have h2 : |β| * sysReal.action U ≤ |β| * 4 :=
    mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg β)
  linarith

/-- `sysReal.partition (probHaar G2) β ≤ Real.exp (4 * |β|)`.

The Boltzmann weight is bounded above by that constant (`sysReal_boltz_le`) and the configuration
measure is a probability measure, so the integral inherits the bound.

DERIVED: `4` is the upper bound on `sysReal`'s action, which is what caps the exponent. -/
theorem sysReal_partition_le (β : ℝ) : sysReal.partition (probHaar G2) β ≤ Real.exp (4 * |β|) := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  unfold System.partition
  have hint : Integrable (sysReal.boltz β) (sysReal.vol (probHaar G2)) :=
    (integrable_const (Real.exp (4 * |β|))).mono'
      (measurable_sysReal_boltz β).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => by
        rw [Real.norm_of_nonneg (sysReal_boltz_pos β U).le]; exact sysReal_boltz_le β U))
  calc ∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2))
      ≤ ∫ _U, Real.exp (4 * |β|) ∂(sysReal.vol (probHaar G2)) :=
        integral_mono hint (integrable_const _) (fun U => sysReal_boltz_le β U)
    _ = Real.exp (4 * |β|) := by simp

/-- `Real.exp (-(8 * |β|)) * ∫ O dvol ≤ sysReal.expect (probHaar G2) β O`, for a measurable `O` that
is bounded by some `M` and pointwise nonnegative.

The numerator is bounded below by `e^{-4|β|} ∫ O` from `sysReal_boltz_ge`, and the denominator above
by `e^{4|β|}` from `sysReal_partition_le`; the two exponents add.

Scope: the coupling enters the conclusion only through the constant, so a strictly positive Haar
integral gives a strictly positive Gibbs expectation at every `β`. The bound `M` is a parameter and
is used only for integrability, not in the conclusion.

DERIVED: `8` is the sum of the two exponents `4` and `4` — the upper bound on `sysReal`'s action,
entering once through the weight's lower bound and once through the partition function's upper
bound. `0` is the lower bound in the nonnegativity hypothesis `hO`. -/
theorem expect_ge_haar_of_nonneg (β : ℝ) (O : sysReal.Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) (hO : ∀ U, 0 ≤ O U) :
    Real.exp (-(8 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2)))
      ≤ sysReal.expect (probHaar G2) β O := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  have hZpos := sysReal_partition_pos β
  have hZle := sysReal_partition_le β
  have hOint : Integrable O (sysReal.vol (probHaar G2)) :=
    (integrable_const M).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => by rw [Real.norm_eq_abs]; exact hbound U))
  have hprod : Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)) :=
    sysReal_mul_boltz_integrable β O hmeas M hbound
  have hIO : 0 ≤ ∫ U, O U ∂(sysReal.vol (probHaar G2)) := integral_nonneg hO
  -- numerator: ∫ O·boltz ≥ e^{−4|β|} ∫ O
  have hnum : Real.exp (-(4 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2)))
      ≤ ∫ U, O U * sysReal.boltz β U ∂(sysReal.vol (probHaar G2)) := by
    rw [← integral_const_mul]
    refine integral_mono (hOint.const_mul _) hprod (fun U => ?_)
    calc Real.exp (-(4 * |β|)) * O U
        ≤ sysReal.boltz β U * O U := mul_le_mul_of_nonneg_right (sysReal_boltz_ge β U) (hO U)
      _ = O U * sysReal.boltz β U := mul_comm _ _
  have hXnn : 0 ≤ Real.exp (-(8 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2))) :=
    mul_nonneg (Real.exp_pos _).le hIO
  unfold System.expect System.corrNum
  rw [le_div_iff₀ hZpos]
  calc Real.exp (-(8 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2)))
        * sysReal.partition (probHaar G2) β
      ≤ Real.exp (-(8 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2))) * Real.exp (4 * |β|) :=
        mul_le_mul_of_nonneg_left hZle hXnn
    _ = Real.exp (-(4 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2))) := by
        rw [mul_comm (Real.exp (-(8 * |β|)) * (∫ U, O U ∂(sysReal.vol (probHaar G2))))
              (Real.exp (4 * |β|)), ← mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ ∫ U, O U * sysReal.boltz β U ∂(sysReal.vol (probHaar G2)) := hnum

/-- `0 < ∑ d, wilsonCorrReal β d` at every real coupling, given that the zero-lag Haar integral
`∫ φ₀ * φ₀ dvol` is positive.

`expect_ge_haar_of_nonneg` turns the Haar positivity into positivity of `wilsonCorrReal β 0`, and the
remaining lag is nonnegative by `wilsonCorrReal_nonneg`.

Scope: the hypothesis is about the zero-lag integral under plain product Haar, not about the total
mass, and it carries no coupling — the coupling enters the conclusion only through the constant
`e^{-8|β|}`.

DERIVED: `0` is the lag the hypothesis is taken at and the lower bound in both the hypothesis and the
conclusion. It is the only numeral in the statement. -/
theorem sum_wilsonCorrReal_pos_of_haar (β : ℝ)
    (hhaar : 0 < ∫ U, plaqObs 0 U * plaqObs 0 U ∂(sysReal.vol (probHaar G2))) :
    0 < ∑ d, wilsonCorrReal β d := by
  have hmeas : Measurable (fun U => plaqObs 0 U * plaqObs 0 U) :=
    (measurable_plaqObs 0).mul (measurable_plaqObs 0)
  have hnn : ∀ U, 0 ≤ plaqObs 0 U * plaqObs 0 U :=
    fun U => mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg 0 U)
  have hb : ∀ U, |plaqObs 0 U * plaqObs 0 U| ≤ 4 := fun U => by
    rw [abs_of_nonneg (hnn U)]
    calc plaqObs 0 U * plaqObs 0 U
        ≤ 2 * 2 := mul_le_mul (plaqObs_le_two 0 U) (plaqObs_le_two 0 U)
            (plaqObs_nonneg 0 U) (by norm_num)
      _ = 4 := by norm_num
  have h0 : 0 < wilsonCorrReal β 0 :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hhaar)
      (expect_ge_haar_of_nonneg β _ hmeas 4 hb hnn)
  have hall : ∀ d ∈ Finset.univ, 0 ≤ wilsonCorrReal β d :=
    fun d _ => wilsonCorrReal_nonneg β d
  exact lt_of_lt_of_le h0 (Finset.single_le_sum hall (Finset.mem_univ 0))

/-! ### The single-link translation, and how the plaquette holonomy transports under it

The remaining Haar integral (`∫ φ₀ dvol = 1`, equivalently `∫ Re tr(hol p₀) dvol = 0`) is reached by
translating ONE link. Link `0` occurs exactly once in `bd2 0`, first and forward, so left-multiplying
it by `g` left-multiplies the whole plaquette holonomy by `g`; and translating one coordinate preserves
the product Haar measure by left-invariance in that factor and the identity elsewhere.

Both facts are proved here. What remains for `∫ Re tr(hol p₀) dvol = 0` is one averaging step: the
value is independent of `g` by `integral_comp_linkTranslate`, so it equals its own average over `g`,
and swapping that average inside (Fubini on two probability measures, bounded measurable integrand)
leaves `∫_g tr(g · X) dHaar(g) = 0` pointwise by `HaarMoments.haar_su2_trace_mul_zero`. -/

/-- Left-multiply the link at index `i₀` by `g`, leaving every other link alone.

Typed on `Fin 8 → G2`, which is definitionally `sysReal.Config`, so that the coordinate comparison
`l = i₀` has a `DecidableEq` instance.

DERIVED: `8` is the number of links of `sysReal`, the index range of a configuration. It is the only
numeral in the statement. -/
noncomputable def linkTranslate (g : G2) (i₀ : Fin 8) (U : Fin 8 → G2) : Fin 8 → G2 :=
  fun l => if l = i₀ then g * U l else U l

/-- The coordinate map that `linkTranslate` applies at index `l` preserves Haar measure on `G2`:
left multiplication by `g` when `l = i₀`, the identity otherwise.

Left-invariance of Haar in the first case, `MeasurePreserving.id` in the second.

DERIVED: `8` is the number of links of `sysReal`, the range of the two indices. It is the only
numeral in the statement. -/
theorem linkTranslate_coord_mp (g : G2) (i₀ l : Fin 8) :
    MeasurePreserving (fun u : G2 => if l = i₀ then g * u else u) (probHaar G2) (probHaar G2) := by
  by_cases h : l = i₀
  · simp only [h]
    exact measurePreserving_mul_left (probHaar G2) g
  · simp only [if_neg h]
    exact MeasurePreserving.id (probHaar G2)

/-- `linkTranslate g i₀` preserves the product Haar measure on `Fin 8 → G2`.

The map is coordinatewise, each coordinate map preserves Haar (`linkTranslate_coord_mp`), and
`Measure.pi_map_pi` assembles them. No property of `g` is needed beyond membership in the group.

DERIVED: `8` is the number of links of `sysReal`, the index of the product. It is the only numeral in
the statement. -/
theorem linkTranslate_measurePreserving (g : G2) (i₀ : Fin 8) :
    MeasurePreserving (linkTranslate g i₀)
      (Measure.pi fun _ : Fin 8 => probHaar G2) (Measure.pi fun _ : Fin 8 => probHaar G2) := by
  have hmeas : Measurable (linkTranslate g i₀) := by
    refine measurable_pi_lambda _ (fun l => ?_)
    by_cases h : l = i₀
    · simp only [linkTranslate, h]
      exact measurable_const.mul (measurable_pi_apply i₀)
    · simp only [linkTranslate, if_neg h]
      exact measurable_pi_apply l
  refine ⟨hmeas, ?_⟩
  have hform : linkTranslate g i₀
      = (fun (U : Fin 8 → G2) (l : Fin 8) =>
          (fun u : G2 => if l = i₀ then g * u else u) (U l)) := by
    funext U l; simp only [linkTranslate]
  rw [hform, Measure.pi_map_pi (fun l => (linkTranslate_coord_mp g i₀ l).aemeasurable)]
  simp only [(linkTranslate_coord_mp g i₀ _).map_eq]

/-- `wilsonHol bd2 0 (linkTranslate g 0 U) = g * wilsonHol bd2 0 U`.

Link `0` appears exactly once in the boundary word `bd2 0`, first and forward, so translating it left
multiplies the whole ordered product on the left. A finite computation on the concrete word; it does
not hold for a link appearing elsewhere in the word or inverted.

DERIVED: `8` is the number of links of `sysReal`; `0` is the index of the translated link and of the
plaquette, which must be the same for the computation to close. -/
theorem hol_linkTranslate (g : G2) (U : Fin 8 → G2) :
    wilsonHol bd2 0 (linkTranslate g 0 U) = g * wilsonHol bd2 0 U := by
  simp [wilsonHol, bd2, linkTranslate, mul_assoc]

/-- The single-link translation as a measurable equivalence of `Fin 8 → G2`, with inverse the
translation by `g⁻¹`.

`MeasurePreserving.integral_comp'` transports an integral along an `≃ᵐ` and not along a bare
function, which is why this packaging exists; stated with `linkTranslate` directly the elaborator
does not unify the function against the equivalence's coercion within its heartbeat budget. It
mirrors `CompactGauge.confConjEquiv`.

DERIVED: `8` is the number of links of `sysReal`, the index of the configuration type. It is the only
numeral in the statement. -/
noncomputable def linkTranslateEquiv (g : G2) (i₀ : Fin 8) : (Fin 8 → G2) ≃ᵐ (Fin 8 → G2) where
  toFun := linkTranslate g i₀
  invFun := linkTranslate g⁻¹ i₀
  left_inv := fun U => by
    funext l; by_cases h : l = i₀ <;> simp [linkTranslate, h]
  right_inv := fun U => by
    funext l; by_cases h : l = i₀ <;> simp [linkTranslate, h]
  measurable_toFun := (linkTranslate_measurePreserving g i₀).measurable
  measurable_invFun := (linkTranslate_measurePreserving g⁻¹ i₀).measurable

/-- `linkTranslateEquiv g i₀` preserves the product Haar measure — it is `linkTranslate g i₀` under
the coercion, so `linkTranslate_measurePreserving` applies directly.

DERIVED: `8` is the number of links of `sysReal`, the index of the product. It is the only numeral in
the statement. -/
theorem linkTranslateEquiv_measurePreserving (g : G2) (i₀ : Fin 8) :
    MeasurePreserving (linkTranslateEquiv g i₀)
      (Measure.pi fun _ : Fin 8 => probHaar G2) (Measure.pi fun _ : Fin 8 => probHaar G2) :=
  linkTranslate_measurePreserving g i₀

/-- `∫ f (g * wilsonHol bd2 0 U) dvol = ∫ f (wilsonHol bd2 0 U) dvol`, for every `g : G2` and every
`f : G2 → ℝ`.

Transporting along `linkTranslateEquiv g 0` preserves the measure, and `hol_linkTranslate` turns the
transported holonomy into `g * hol`. So the value is independent of the left shift.

Scope: `f` is an arbitrary real-valued function, with no measurability or boundedness hypothesis —
Mathlib's integral is zero on non-integrable functions, and the two sides are equal either way. The
statement is about the plaquette at index `0` and the link at index `0`.

DERIVED: `8` is the number of links of `sysReal`; `0` is the index of the plaquette whose holonomy is
read and of the link that is translated. -/
theorem integral_comp_linkTranslate (g : G2) (f : G2 → ℝ) :
    (∫ U, f (g * wilsonHol bd2 0 U) ∂(Measure.pi fun _ : Fin 8 => probHaar G2))
      = ∫ U, f (wilsonHol bd2 0 U) ∂(Measure.pi fun _ : Fin 8 => probHaar G2) := by
  have hmp := linkTranslateEquiv_measurePreserving g 0
  have hstep := hmp.integral_comp' (fun U : Fin 8 → G2 => f (wilsonHol bd2 0 U))
  calc (∫ U, f (g * wilsonHol bd2 0 U) ∂(Measure.pi fun _ : Fin 8 => probHaar G2))
      = ∫ U, f (wilsonHol bd2 0 (linkTranslateEquiv g 0 U))
          ∂(Measure.pi fun _ : Fin 8 => probHaar G2) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun U => by
          show f (g * wilsonHol bd2 0 U) = f (wilsonHol bd2 0 (linkTranslate g 0 U))
          rw [hol_linkTranslate]))
    _ = ∫ U, f (wilsonHol bd2 0 U) ∂(Measure.pi fun _ : Fin 8 => probHaar G2) := hstep

/-! ### Closing the Haar integral with the `Z₂` centre

No Fubini is needed. `−1` lies in `SU(2)` (determinant `(−1)² = 1`, unitary), and it is central, so
translating link `0` by it negates the plaquette holonomy and hence its trace. The integral therefore
equals minus itself. -/

/-- `-1` lies in `Matrix.specialUnitaryGroup (Fin 2) ℂ`: it is unitary and its determinant is
`(-1)² = 1`.

DERIVED: `1` is the matrix scalar being negated, and `2` is the matrix size — `SU(2)` is the gauge
group of `sysReal`. -/
theorem negOne_mem_SU2 : (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · simp
  · simp [Matrix.det_fin_two]

/-- `-1` as an element of `G2`, the nontrivial element of the centre of `SU(2)`.

DERIVED: the statement carries no numeral — `zCentre` is a constant of type `G2`, and the matrix it
bundles is supplied in the body. -/
noncomputable def zCentre : G2 := ⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), negOne_mem_SU2⟩

@[simp] theorem zCentre_coe : (zCentre : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

/-- `∫ (Re tr (wilsonHol bd2 0 U)) dvol = 0` under the product Haar measure.

Translating link `0` by `zCentre` leaves the integral unchanged (`integral_comp_linkTranslate`) and
sends the holonomy to its negative, so the trace changes sign and the integral equals its own
negative. Only centrality and `z = -1` are used; no Fubini swap and no character orthogonality
enters.

DERIVED: `8` is the number of links of `sysReal`; `2` is the matrix size of the gauge group `SU(2)`;
`0` is the index of the plaquette read and the value of the integral. -/
theorem integral_re_trace_hol_zero :
    (∫ U, (Matrix.trace ((wilsonHol bd2 0 U : G2) : Matrix (Fin 2) (Fin 2) ℂ)).re
      ∂(Measure.pi fun _ : Fin 8 => probHaar G2)) = 0 := by
  set F : G2 → ℝ := fun x => (Matrix.trace ((x : Matrix (Fin 2) (Fin 2) ℂ))).re with hF
  have hshift := integral_comp_linkTranslate zCentre F
  have hneg : ∀ x : G2, F (zCentre * x) = -F x := by
    intro x
    show (Matrix.trace (((zCentre * x : G2) : Matrix (Fin 2) (Fin 2) ℂ))).re = -_
    have hmul : ((zCentre * x : G2) : Matrix (Fin 2) (Fin 2) ℂ)
        = (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (x : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [hmul, neg_one_mul, Matrix.trace_neg, Complex.neg_re]
  have : (∫ U, F (zCentre * wilsonHol bd2 0 U) ∂(Measure.pi fun _ : Fin 8 => probHaar G2))
      = -∫ U, F (wilsonHol bd2 0 U) ∂(Measure.pi fun _ : Fin 8 => probHaar G2) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun U => hneg _))
  rw [this] at hshift
  linarith [hshift]

/-- `∫ φ₀ dvol = 1` under the product Haar measure.

`φ_W(g) = 1 - ½ Re tr g`, and the character averages to zero by `integral_re_trace_hol_zero`, so the
value is `1`. The measure is a probability measure, which is what makes the constant term integrate
to `1`.

DERIVED: `8` is the number of links of `sysReal`; `0` is the index of the plaquette read; `1` is the
value of the integral, which is the constant term of the Wilson density `1 - ½ Re tr`. -/
theorem integral_plaqObs_eq_one :
    (∫ U, plaqObs 0 U ∂(Measure.pi fun _ : Fin 8 => probHaar G2)) = 1 := by
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin 8 => probHaar G2) := inferInstance
  have hre : Integrable
      (fun U : Fin 8 → G2 =>
        (Matrix.trace ((wilsonHol bd2 0 U : G2) : Matrix (Fin 2) (Fin 2) ℂ)).re)
      (Measure.pi fun _ : Fin 8 => probHaar G2) := by
    have hm : Measurable (fun U : Fin 8 → G2 =>
        (Matrix.trace ((wilsonHol bd2 0 U : G2) : Matrix (Fin 2) (Fin 2) ℂ)).re) := by
      have heq : (fun U : Fin 8 → G2 =>
          (Matrix.trace ((wilsonHol bd2 0 U : G2) : Matrix (Fin 2) (Fin 2) ℂ)).re)
          = fun U : Fin 8 → G2 => 2 * (1 - plaqObs 0 U) := by
        funext U; simp only [plaqObs, wilsonDensity]; ring
      rw [heq]
      exact (measurable_const.sub (measurable_plaqObs 0)).const_mul 2
    refine (integrable_const (2 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => ?_))
    have h := abs_re_trace_le (N := 2) (wilsonHol bd2 0 U)
    rw [Real.norm_eq_abs]
    simpa using h
  have hpt : ∀ U : Fin 8 → G2, plaqObs 0 U
      = 1 - (1 / 2 : ℝ) * (Matrix.trace ((wilsonHol bd2 0 U : G2) : Matrix (Fin 2) (Fin 2) ℂ)).re := by
    intro U; simp [plaqObs, wilsonDensity]
  simp only [hpt]
  rw [integral_sub (integrable_const _) (hre.const_mul _), integral_const_mul,
      integral_re_trace_hol_zero]
  simp

/-- `0 < ∫ φ₀ * φ₀ dvol` under the product Haar measure.

The pointwise inequality `(φ₀ - 1)² ≥ 0` gives `φ₀² ≥ 2φ₀ - 1`, and `integral_mono` with
`integral_plaqObs_eq_one` puts the integral at least `1`. No Cauchy–Schwarz is used.

Scope: the proof reaches `≥ 1` but the conclusion exported is positivity, so a caller cannot use the
value.

DERIVED: `8` is the number of links of `sysReal`; `0` is the index of the plaquette read and the
lower bound concluded. -/
theorem integral_plaqObs_sq_pos :
    0 < ∫ U, plaqObs 0 U * plaqObs 0 U ∂(Measure.pi fun _ : Fin 8 => probHaar G2) := by
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin 8 => probHaar G2) := inferInstance
  have hmsq : Measurable (fun U : Fin 8 → G2 => plaqObs 0 U * plaqObs 0 U) :=
    (measurable_plaqObs 0).mul (measurable_plaqObs 0)
  have hsq : Integrable (fun U : Fin 8 → G2 => plaqObs 0 U * plaqObs 0 U)
      (Measure.pi fun _ : Fin 8 => probHaar G2) := by
    refine (integrable_const (4 : ℝ)).mono' hmsq.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg 0 U))]
    calc plaqObs 0 U * plaqObs 0 U
        ≤ 2 * 2 := mul_le_mul (plaqObs_le_two 0 U) (plaqObs_le_two 0 U)
            (plaqObs_nonneg 0 U) (by norm_num)
      _ = 4 := by norm_num
  have hlin : Integrable (fun U : Fin 8 → G2 => 2 * plaqObs 0 U - 1)
      (Measure.pi fun _ : Fin 8 => probHaar G2) := by
    refine (integrable_const (5 : ℝ)).mono'
      (((measurable_plaqObs 0).const_mul 2).sub measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => ?_))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> [linarith [plaqObs_nonneg 0 U]; linarith [plaqObs_le_two 0 U]]
  have hmono : (∫ U, (2 * plaqObs 0 U - 1) ∂(Measure.pi fun _ : Fin 8 => probHaar G2))
      ≤ ∫ U, plaqObs 0 U * plaqObs 0 U ∂(Measure.pi fun _ : Fin 8 => probHaar G2) :=
    integral_mono hlin hsq (fun U => by nlinarith [sq_nonneg (plaqObs 0 U - 1)])
  have hval : (∫ U, (2 * plaqObs 0 U - 1) ∂(Measure.pi fun _ : Fin 8 => probHaar G2)) = 1 := by
    have hint : Integrable (fun U : Fin 8 → G2 => plaqObs 0 U)
        (Measure.pi fun _ : Fin 8 => probHaar G2) := by
      refine (integrable_const (2 : ℝ)).mono'
        (measurable_plaqObs 0).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun U => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (plaqObs_nonneg 0 U)]
      exact plaqObs_le_two 0 U
    rw [integral_sub (hint.const_mul 2) (integrable_const _), integral_const_mul,
        integral_plaqObs_eq_one]
    simp
    norm_num
  linarith [hmono, hval]

/-- `0 < ∑ d, wilsonCorrReal β d` at every real coupling, with no hypothesis.

`sum_wilsonCorrReal_pos_of_haar` with its Haar hypothesis supplied by `integral_plaqObs_sq_pos`. This
is the `hpos` field `Moment.Read` requires.

DERIVED: `0` is the lower bound concluded, and is the only numeral in the statement. -/
theorem sum_wilsonCorrReal_pos (β : ℝ) : 0 < ∑ d, wilsonCorrReal β d :=
  sum_wilsonCorrReal_pos_of_haar β integral_plaqObs_sq_pos

/-- The `Moment.Read 1` whose profile is `wilsonCorrReal β`.

Both `Moment.Read` obligations are filled by theorems rather than hypotheses: `hρ` by
`wilsonCorrReal_nonneg` and `hpos` by `sum_wilsonCorrReal_pos`. The construction takes the coupling
and nothing else.

Scope: `sysReal` has two plaquettes, so the aperture index is `1` and the lags are `0` and `1`. Every
aperture-scaled statement about this read is at that aperture.

DERIVED: `1` is the aperture index `N` of `Moment.Read`, one less than the two plaquettes of
`sysReal`. It is the only numeral in the statement. -/
noncomputable def wilsonReadReal (β : ℝ) : Moment.Read 1 :=
  { ρ := wilsonCorrReal β
    hρ := wilsonCorrReal_nonneg β
    hpos := sum_wilsonCorrReal_pos β }

/-- `(wilsonReadReal β).ρ d = sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs d U)`, by
`rfl`.

The read's profile is the Gibbs expectation itself, not a name standing in for one.

DERIVED: `2` is the number of plaquettes of `sysReal`, the range of the lag index; `0` is the base
plaquette the correlation is read from. -/
theorem wilsonReadReal_rho (β : ℝ) (d : Fin 2) :
    (wilsonReadReal β).ρ d
      = sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs d U) := rfl

/-- `(wilsonReadReal β).tension < (1 / 4) * Real.log 3`, given a lag second moment bounded by `B`
(`hB`) and the aperture scaling condition `hscale`.

`Moment.Read.tension_lt_floor_of_circ_moment` applied to this read: `cos x ≥ 1 - x²/2` together with
the `1/(N+1)²` aperture factor. Nonnegativity and positive total mass are already theorems here, so
`hB` and `hscale` are the only inputs.

Scope. The aperture is `N = 1`, so the factor in `hscale` is `(2π/2)²/2 = π²/2` and
`two_plaquette_aperture_forces_tiny_B` reduces the condition to `B < 2(1 - 3^{-1/4})/π²`, about
`0.0487`. The system's own lag second moment is larger: the two plaquettes share no link, so
`ρ(1) = ⟨φ₀⟩⟨φ₁⟩` at every coupling (`WilsonReal.expect_plaqObs_factor`), and at `β = 0` that is `1`
against `ρ(0) = ∫ φ₀² = 5/4`, giving `4/9`. So `hB` and `hscale` cannot both hold for `sysReal`, and
this theorem has no instance on that system. `Complete.confinement_of_growth_bound` states the
condition at every sufficiently large aperture, where the `1/(N+1)²` factor makes it weaker.

DERIVED: `2` is the numerator `2 * Real.pi` of one turn in the aperture factor, its denominator's
divisor, and the exponent of the circle distance in the lag second moment. `1` is the aperture index
`N` of this read, the offset in `N + 1`, the value the floor margin is measured from in
`1 - 3 ^ (-(1)/4)`, and the numerator of `1 / 4`. `3` and `4` are the entropy floor
`(1 / 4) * Real.log 3` and the constant `3 ^ (-(1 : ℝ) / 4)` the margin is taken against; both come
from `Moment.Read.tension_lt_floor_of_circ_moment`. -/
-- At `N = 1` the circle distance is the raw lag, since `min 1 (2 - 1) = 1`, so the circle-moment and
-- raw-lag forms of the hypothesis coincide at this extent. The raw-lag form is not used because its
-- hypothesis is unsatisfiable for a periodic correlation at large extent.
theorem wilson_tension_lt_floor {β B : ℝ}
    (hB : ∑ d, (wilsonReadReal β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ B)
    (hscale : (2 * Real.pi / ((1 : ℕ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (wilsonReadReal β).tension < (1 / 4) * Real.log 3 :=
  (wilsonReadReal β).tension_lt_floor_of_circ_moment hB hscale

/-- `hscale` at aperture `N = 1` is exactly `B < 2 * (1 - 3 ^ (-(1 : ℝ) / 4)) / π ^ 2`.

At that aperture the scaling factor is `(2π/2)²/2 = π²/2`, so dividing through gives the stated
bound. No rounding is introduced: the right-hand side is the aperture condition rearranged.

Scope: this is an implication out of `hscale`, not an assertion that any `B` satisfies it. Its value
is about `0.0487`, against `sysReal`'s own lag second moment of `4/9` at `β = 0`, so `hB` and
`hscale` are jointly unsatisfiable on that system.

DERIVED: `2` is the numerator `2 * Real.pi` of one turn, the divisor in the aperture factor, the
coefficient on the right, and the exponent of `Real.pi`. `1` is the aperture index `N`, the offset in
`N + 1`, and the value the floor margin is measured from. `3` and `4` are the base and root of
`3 ^ (-(1 : ℝ) / 4)`, carried unchanged from `hscale`. -/
theorem two_plaquette_aperture_forces_tiny_B {B : ℝ}
    (hscale : (2 * Real.pi / ((1 : ℕ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    B < 2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / Real.pi ^ 2 := by
  have hN : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
  rw [hN] at hscale
  have hpi2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hrw : (2 * Real.pi / 2) ^ 2 * B / 2 = Real.pi ^ 2 * B / 2 := by ring_nf
  rw [hrw] at hscale
  rw [lt_div_iff₀ hpi2]
  linarith

#print axioms two_plaquette_aperture_forces_tiny_B

#print axioms linkTranslate_measurePreserving
#print axioms integral_comp_linkTranslate
#print axioms integral_re_trace_hol_zero
#print axioms integral_plaqObs_eq_one
#print axioms integral_plaqObs_sq_pos
#print axioms sum_wilsonCorrReal_pos
#print axioms hol_linkTranslate
#print axioms sysReal_boltz_ge
#print axioms expect_ge_haar_of_nonneg
#print axioms sum_wilsonCorrReal_pos_of_haar
#print axioms wilsonCorrReal_nonneg
#print axioms wilsonReadReal_rho
#print axioms wilson_tension_lt_floor

end MassGap.WilsonRead
