import MassGap.WilsonReal
import MassGap.Moment

/-!
# MassGap.WilsonRead — the entropy-matched read of a GENUINE Wilson Gibbs measure

Everywhere else in this development the read's input is `Complete.wilsonCorr`, an `opaque` function whose
one load-bearing property — nonnegativity at every lag — is the NAMED AXIOM
`Complete.wilson_reflection_positive_at`. The review's §4 asks for the identification of the read with the
actual Wilson theory to stop being a modelling statement. This file does that at the one volume where it is
currently reachable, and derives what was assumed.

## What is genuine here

The correlation below is a Gibbs expectation of the REAL SU(2) Wilson system already built in
`WilsonReal`: eight links, two plaquettes, each plaquette a genuine four-link ordered holonomy
`U₀U₁U₂⁻¹U₃⁻¹`, the real Wilson action density `φ_W(g) = 1 − ½ Re tr g`, integrated against normalised
Haar measure. No `opaque`, no ensemble stand-in.

* **Nonnegativity is a THEOREM, not the RP axiom.** `wilsonCorrReal β d = ⟨φ_p · φ_q⟩_β` is the Gibbs
  average of a product of two nonnegative quantities (`WilsonAction.wilsonDensity_nonneg`), and the Gibbs
  state is positive (`WilsonReal.sysReal_expect_nonneg`). So `Moment.Read`'s `hρ` is discharged by
  computation. For this system, `wilson_reflection_positive_at` is not needed and does not appear.
* **Positivity of the total mass is a THEOREM too.** `Moment.Read` also needs `0 < Σ_d ρ_d`, and
  `sum_wilsonCorrReal_pos` proves it at every coupling. So `wilsonReadReal β` is UNCONDITIONAL: a
  `Moment.Read` built from a genuine Wilson Gibbs measure with no hypothesis and no axiom beyond the
  foundational three.

  How the coupling drops out, and how the integral closes:

  1. **`⟨O⟩_β ≥ e^{−8|β|} ∫ O dHaar`** (`expect_ge_haar_of_nonneg`). `sysReal`'s action is bounded in
     `[0,4]`, so its Boltzmann weight is bounded in `[e^{−4|β|}, e^{4|β|}]` and the Gibbs state
     dominates the Haar integral. A statement over the whole half-line becomes one integral against
     one fixed measure.
  2. **`∫ Re tr(hol p₀) dvol = 0`** (`integral_re_trace_hol_zero`), by the `Z₂` **centre** of `SU(2)`.
     Translating link `0` by `z = −1` preserves product Haar (`linkTranslate_measurePreserving`) and
     sends `hol ↦ z·hol = −hol` (`hol_linkTranslate`), so the integral equals minus itself. This is
     what replaces a Fubini swap against Haar — the centre does the work in three lines.
  3. **`∫ φ₀ dvol = 1`** (`integral_plaqObs_eq_one`), since `φ_W = 1 − ½ Re tr`.
  4. **`∫ φ₀² dvol ≥ 1 > 0`** (`integral_plaqObs_sq_pos`), from the pointwise `(φ₀−1)² ≥ 0`, i.e.
     `φ₀² ≥ 2φ₀ − 1`, and `integral_mono`. No Cauchy–Schwarz needed.

  The one remaining measured input anywhere in this file is `hB`, the bounded lag second moment of
  `wilson_tension_lt_floor` — the finite-correlation-length content, which is the measured input
  everywhere in this program.

## What this is NOT

Two plaquettes on eight links is a single gauge cell, not a finite-volume lattice with a time direction.
There is no transfer operator here yet, so nothing below identifies the read's tension with a transfer
eigenvalue — the reviewer's §5/§16-T1 in full. What it does establish is the first link of that chain on a
real Wilson measure: the entropy-matched read is applied to a genuine Wilson Gibbs correlation, and the
property the read needs of it is proved rather than assumed.

Footprint: the three foundational axioms only, for every declaration in this file. In particular
NOT `wilson_reflection_positive_at`, and no hypothesis on the read itself.
-/

namespace MassGap.WilsonRead

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonReal MassGap.WilsonAction
open MassGap.CompactGauge
open MeasureTheory

/-! The plaquette action-density observable is `WilsonReal.plaqObs` — already defined there, with its
nonnegativity (`plaqObs_nonneg`), its bound (`plaqObs_le_two`), its measurability (`measurable_plaqObs`)
and its gauge invariance (`plaqObs_gauge_invariant`) proved. Nothing is redefined here. -/

/-- **The two-plaquette correlation of the genuine Wilson Gibbs measure**, indexed by the lag `d`:
`ρ_β(d) = ⟨φ_{p₀} · φ_{p_d}⟩_β`, a real expectation against normalised Haar with the real Wilson
Boltzmann weight. This is the object the entropy-matched read consumes — with no `opaque` in it. -/
noncomputable def wilsonCorrReal (β : ℝ) (d : Fin 2) : ℝ :=
  sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs d U)

/-- **The correlation is nonnegative — a THEOREM.** The integrand is a product of two nonnegative
densities and the Gibbs state is positive, so no reflection-positivity input is required. This is what
`Complete.wilson_reflection_positive_at` asserts for the opaque ensemble; here it is proved. -/
theorem wilsonCorrReal_nonneg (β : ℝ) (d : Fin 2) : 0 ≤ wilsonCorrReal β d :=
  sysReal_expect_nonneg β _ (fun U => mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg d U))

/-- **The correlation is bounded by 4** (each density is `≤ 2`, and the state is contractive). Recorded
because the read's downstream moment bounds are statements about a bounded correlation. -/
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

/-- **Lower bound on the Boltzmann weight, `e^{−4|β|} ≤ e^{−βS}`** — the mirror of the existing
`sysReal_boltz_le`, from `S ∈ [0,4]`. -/
theorem sysReal_boltz_ge (β : ℝ) (U : sysReal.Config) :
    Real.exp (-(4 * |β|)) ≤ sysReal.boltz β U := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : β * sysReal.action U ≤ |β| * sysReal.action U :=
    mul_le_mul_of_nonneg_right (le_abs_self β) (sysReal_action_nonneg U)
  have h2 : |β| * sysReal.action U ≤ |β| * 4 :=
    mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg β)
  linarith

/-- **The partition function is at most `e^{4|β|}`** (weight bounded, `vol` a probability measure). -/
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

/-- **The Gibbs state dominates the Haar integral up to `e^{−8|β|}`, for a bounded nonnegative
observable.** `⟨O⟩_β ≥ e^{−8|β|} ∫ O dHaar`. The coupling enters only through that constant, so a
strictly positive Haar integral gives a strictly positive Gibbs expectation at EVERY `β`. -/
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

/-- **`hpos` at every coupling from one Haar fact.** If the correlation's total mass is positive under
plain product Haar, it is positive at every `β` — the coupling enters only through the constant
`e^{−8|β|}` of `expect_ge_haar_of_nonneg`. This is the reduction that makes P2 step 2 a single
`β`-free integral rather than a statement over the whole half-line. -/
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

/-- Left-translate a single link by `g`, leaving every other link alone. Typed on `Fin 8 → G2`
(definitionally `sysReal.Config`) so that the coordinate comparison `l = i₀` has its `DecidableEq`. -/
noncomputable def linkTranslate (g : G2) (i₀ : Fin 8) (U : Fin 8 → G2) : Fin 8 → G2 :=
  fun l => if l = i₀ then g * U l else U l

/-- The per-coordinate map `linkTranslate` applies: left multiplication by `g` at `i₀`, identity
elsewhere. Left-invariance of Haar in the first case, nothing to do in the second. -/
theorem linkTranslate_coord_mp (g : G2) (i₀ l : Fin 8) :
    MeasurePreserving (fun u : G2 => if l = i₀ then g * u else u) (probHaar G2) (probHaar G2) := by
  by_cases h : l = i₀
  · simp only [h]
    exact measurePreserving_mul_left (probHaar G2) g
  · simp only [if_neg h]
    exact MeasurePreserving.id (probHaar G2)

/-- **Translating one link preserves the product Haar measure** — left-invariance in that factor,
the identity in the others, assembled coordinatewise by `Measure.pi_map_pi`. -/
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

/-- **The plaquette-0 holonomy transports by left multiplication.** Link `0` appears exactly once in
`bd2 0`, first and forward, so `hol p₀ (linkTranslate g 0 U) = g · hol p₀ U`. A finite computation on
the concrete boundary word. -/
theorem hol_linkTranslate (g : G2) (U : Fin 8 → G2) :
    wilsonHol bd2 0 (linkTranslate g 0 U) = g * wilsonHol bd2 0 U := by
  simp [wilsonHol, bd2, linkTranslate, mul_assoc]

/-- **The single-link translation as a MEASURABLE EQUIVALENCE** (inverse: translate by `g⁻¹`).
`MeasurePreserving.integral_comp'` transports an integral only along an `≃ᵐ`, so the bare function
will not do: stated with `linkTranslate` directly the elaborator burns a million heartbeats at `whnf`
trying to unify a function against the equivalence's coercion. Mirrors `CompactGauge.confConjEquiv`. -/
noncomputable def linkTranslateEquiv (g : G2) (i₀ : Fin 8) : (Fin 8 → G2) ≃ᵐ (Fin 8 → G2) where
  toFun := linkTranslate g i₀
  invFun := linkTranslate g⁻¹ i₀
  left_inv := fun U => by
    funext l; by_cases h : l = i₀ <;> simp [linkTranslate, h]
  right_inv := fun U => by
    funext l; by_cases h : l = i₀ <;> simp [linkTranslate, h]
  measurable_toFun := (linkTranslate_measurePreserving g i₀).measurable
  measurable_invFun := (linkTranslate_measurePreserving g⁻¹ i₀).measurable

/-- `linkTranslateEquiv` preserves the product Haar measure (it is the same map). -/
theorem linkTranslateEquiv_measurePreserving (g : G2) (i₀ : Fin 8) :
    MeasurePreserving (linkTranslateEquiv g i₀)
      (Measure.pi fun _ : Fin 8 => probHaar G2) (Measure.pi fun _ : Fin 8 => probHaar G2) :=
  linkTranslate_measurePreserving g i₀

/-- **The Haar integral of any function of the plaquette-0 holonomy is independent of a left shift.**
Transporting by `linkTranslateEquiv` is measure-preserving and shifts the holonomy by `g`
(`hol_linkTranslate`), so `∫ f(g · hol p₀ U) = ∫ f(hol p₀ U)` for every `g`.

This is the input the averaging step consumes: the value is its own `g`-average, and the inner
`g`-integral `∫ tr(g · X) dHaar(g)` vanishes for every fixed `X`
(`HaarMoments.haar_su2_trace_mul_zero`). Applying it at `f = Re ∘ tr` and averaging gives
`∫ Re tr(hol p₀) dvol = 0`, hence `∫ φ₀ dvol = 1`, which is the last input `hpos` needs. -/
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

/-- The centre element `−1 ∈ SU(2)`. -/
theorem negOne_mem_SU2 : (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · simp
  · simp [Matrix.det_fin_two]

/-- `−1` as an element of `SU(2)` — the nontrivial element of the centre `Z₂`. -/
noncomputable def zCentre : G2 := ⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), negOne_mem_SU2⟩

@[simp] theorem zCentre_coe : (zCentre : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

/-- **The Haar average of the plaquette-0 Wilson character vanishes: `∫ Re tr(hol p₀) dvol = 0`.**

Translating link `0` by the centre element `z = −1` leaves the Haar integral unchanged
(`integral_comp_linkTranslate`) while sending `hol ↦ z · hol = −hol`, so the trace changes sign. The
integral is therefore equal to its own negative, hence zero. This is the `Z₂` centre of `SU(2)` doing
the work that would otherwise need a Fubini swap against Haar.

Foundational axioms only. -/
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

/-- **The Haar mean plaquette energy is exactly 1: `∫ φ₀ dvol = 1`.** `φ_W(g) = 1 − ½ Re tr g` and the
character averages to zero (`integral_re_trace_hol_zero`), so the free value is `1 − ½·0 = 1`. -/
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

/-- **The Haar mean square plaquette energy is at least 1, hence positive.** Pointwise
`(φ₀ − 1)² ≥ 0` gives `φ₀² ≥ 2φ₀ − 1`, and integrating with `∫ φ₀ = 1` gives `∫ φ₀² ≥ 1`. No
Cauchy–Schwarz: one pointwise inequality and `integral_mono`. -/
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

/-- **`hpos` is DISCHARGED — the read needs no hypothesis.** Combining
`sum_wilsonCorrReal_pos_of_haar` with `integral_plaqObs_sq_pos`: the genuine Wilson correlation has
strictly positive total mass at EVERY coupling, proved, with no axiom and no assumption. -/
theorem sum_wilsonCorrReal_pos (β : ℝ) : 0 < ∑ d, wilsonCorrReal β d :=
  sum_wilsonCorrReal_pos_of_haar β integral_plaqObs_sq_pos

/-- **The entropy-matched read of the genuine Wilson measure — UNCONDITIONAL.** Both of
`Moment.Read`'s obligations are discharged by theorems: `hρ` (nonnegativity at every lag) by
`wilsonCorrReal_nonneg`, and `hpos` (positive total mass) by `sum_wilsonCorrReal_pos`. There is no
hypothesis and no axiom beyond the foundational three. `sysReal` has two plaquettes, so the read has
`N = 1` (lags `d ∈ {0,1}`). -/
noncomputable def wilsonReadReal (β : ℝ) : Moment.Read 1 :=
  { ρ := wilsonCorrReal β
    hρ := wilsonCorrReal_nonneg β
    hpos := sum_wilsonCorrReal_pos β }

/-- **The read's correlation IS the Wilson Gibbs correlation — by construction (`rfl`).** Unlike
a `rfl` relating two names for the same OPAQUE function, this
identifies the read's input with a genuine expectation against Haar and the real Wilson action. -/
theorem wilsonReadReal_rho (β : ℝ) (d : Fin 2) :
    (wilsonReadReal β).ρ d
      = sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs d U) := rfl

/-- **The tension of the GENUINE Wilson read is below the entropy floor when its lag moment is bounded.**
The same analytic step the rest of the development uses (`Moment.Read.tension_lt_floor_of_circ_moment`:
`cos x ≥ 1 − x²/2` plus the `1/(N+1)²` aperture scaling), but applied to a read whose correlation is a
real Wilson Gibbs expectation and whose nonnegativity is proved.

The ONE input is `hB`, the bounded lag second moment — the finite-correlation-length content, which
remains the measured input everywhere in this program. Positivity and nonnegativity of the correlation
are now theorems, so nothing else is assumed.

SCOPE — THIS BAR IS NOT INSTANTIABLE ON `sysReal`, AND THAT IS A PROPERTY OF THE SYSTEM, NOT A GAP IN
THE PROOF. `sysReal` has two plaquettes, so the read has `N = 1` and the aperture factor is
`(2π/2)² / 2 = π²/2 ≈ 4.93`. `two_plaquette_aperture_forces_tiny_B` below shows `hscale` then forces
`B < 1/10` (the true threshold is `≈ 0.0487`). But the system's actual lag moment is far larger: the
two plaquettes share no link, so `ρ(1) = ⟨φ₀⟩⟨φ₁⟩` at every `β` (`WilsonReal.expect_plaqObs_factor`),
and at `β = 0` that is `1·1 = 1` while `ρ(0) = ∫φ₀² = 5/4`, giving `⟨d²⟩ = 1/(5/4+1) = 4/9 ≈ 0.444`
— over the threshold by a factor of `9.1`.

So `hB` and `hscale` cannot both hold here. This is the `1/L²` aperture scaling working as designed:
`Complete.confinement_of_growth_bound` gives the condition at every large enough aperture, and the physical read uses
`N = 16` (threshold `≈ 3.52`). A two-plaquette cell is nine apertures too small. The theorem is stated
because it is the correct general statement over this read; it is NOT evidence about `sysReal`, and no
instantiation of it on `sysReal` should be quoted.

Footprint: the three foundational axioms. NOT `wilson_reflection_positive_at`. -/
-- DERIVED: at `N = 1` the circle distance IS the raw lag -- `min 1 (2-1) = 1` -- so switching this
-- to `tension_lt_floor_of_circ_moment` changes the statement not at all. The raw-lag route it used
-- to take was retired because its hypothesis is unsatisfiable for a periodic correlation at large
-- extent; at this extent the two coincide.
theorem wilson_tension_lt_floor {β B : ℝ}
    (hB : ∑ d, (wilsonReadReal β).p d * (Moment.circLag d : ℝ) ^ 2 ≤ B)
    (hscale : (2 * Real.pi / ((1 : ℕ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (wilsonReadReal β).tension < (1 / 4) * Real.log 3 :=
  (wilsonReadReal β).tension_lt_floor_of_circ_moment hB hscale

/-- **The two-plaquette aperture is too small for the finite-aperture condition — machine-checked.**
At `N = 1` the scaling factor is `(2π/2)²/2 = π²/2`, so `hscale` is exactly the statement
`B < 2(1 − 3^{-1/4})/π²`. That is the SHARP consequence — no rounded threshold is introduced here, the
bound is whatever the aperture condition itself says. Numerically it is `≈ 0.0487`, against the
system's own lag moment `4/9 ≈ 0.444` at `β = 0` (see the scope note on `wilson_tension_lt_floor`), so
the two hypotheses are jointly unsatisfiable here.

This is the anti-vacuity check applied to this file's own bar: a theorem whose hypotheses no instance
of the system can meet would be exactly the defect the constant-witness theorems in `Complete` were
carrying, and it is recorded rather than left to be discovered. -/
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
