import Mathlib
import MassGap.StrongCouplingGap
import MassGap.HaarVariance

/-!
# A plaquette's variance: the Haar floor and its ingredients

At `SU N`, `2 ≤ N`, the Haar variance of the real trace is positive (`varReTr_pos`), and every
centred second moment of `wilsonDensity` under Haar is at least `varReTr N / N²`
(`integral_wilsonDensity_centred_ge`).

The floor conditions on every link but the plaquette's first, `l₀`. The observable is then
`g ↦ wilsonDensity(g · W)` with `W` fixed by the other links (`ihol_eq_head_mul`), whose Haar integral
does not depend on `W` by right-invariance (`integral_shift_factor`). A state evaluates a centred
square as the variance (`state_centred_sq`), and a plaquette in the reflection plane is fixed by the
reflection (`ireflPlaq_plane`).
-/

namespace MassGap.PlaneVariance

open MeasureTheory

/-! ## One link against the rest -/

section OneLink

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G]

open scoped Classical in
/-- **A factor reading one coordinate through a right translation by the others integrates out.**
For `K` and `B` bounded and measurable, and `W`, `B` not reading coordinate `i₀`,

    ∫ K(u i₀ · W u) · B u  =  (∫ K dμ) · ∫ B.

`ActionSplit.integral_cvol_split_iterated_symm` integrates coordinate `i₀` innermost with the rest
fixed; there `W` and `B` are constants, `ActionSplit.integral_eval_cvol` reduces the inner integral to
one over the group, and right-invariance of `μ` removes `W` (`integral_mul_right_eq_self`).

DERIVED: the `1` is the identity used to fill coordinate `i₀`. -/
theorem integral_shift_factor (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (i₀ : ι) {K : G → ℝ} (hK : Measurable K) {CK : ℝ} (hKb : ∀ g, |K g| ≤ CK)
    {W : (ι → G) → G} (hW : Measurable W) (hWi : ∀ u g, W (Function.update u i₀ g) = W u)
    {B : (ι → G) → ℝ} (hB : Measurable B) {CB : ℝ} (hBb : ∀ u, |B u| ≤ CB)
    (hBi : ∀ u g, B (Function.update u i₀ g) = B u) :
    ∫ u, K (u i₀ * W u) * B u ∂(MassGap.ActionSplit.cvol ι μ)
      = (∫ g, K g ∂μ) * ∫ u, B u ∂(MassGap.ActionSplit.cvol ι μ) := by
  classical
  set p : ι → Prop := fun i => i = i₀ with hp
  have hupd : ∀ (x : Subtype p → G) (y : {i // ¬ p i} → G),
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm (x, y)
        = Function.update ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm
            (fun _ => 1, y)) i₀ (x ⟨i₀, rfl⟩) := by
    intro x y
    funext i
    by_cases h : i = i₀
    · subst h
      simp [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, hp]
    · have h' : ¬ p i := h
      simp [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, Function.update_of_ne h, h']
  have hev : ∀ (x : Subtype p → G) (y : {i // ¬ p i} → G),
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm (x, y) i₀ = x ⟨i₀, rfl⟩ := by
    intro x y; rw [hupd]; simp
  have hsm := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm.measurable
  rw [MassGap.ActionSplit.integral_cvol_split_iterated_symm μ p
      (fun u => K (u i₀ * W u) * B u)
      ((integrable_const (CK * CB)).mono'
        ((hK.comp (((measurable_pi_apply i₀).comp hsm).mul (hW.comp hsm))).mul
          (hB.comp hsm)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hKb _) (hBb _) (abs_nonneg _) ((abs_nonneg _).trans (hKb 1))))),
    MassGap.ActionSplit.integral_cvol_split_iterated_symm μ p B
      ((integrable_const CB).mono' (hB.comp hsm).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hBb _)))]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  have h2 : ∀ x : Subtype p → G,
      W ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm (x, y))
        = W ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm (fun _ => 1, y)) := by
    intro x; rw [hupd, hWi]
  have h3 : ∀ x : Subtype p → G,
      B ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm (x, y))
        = B ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm (fun _ => 1, y)) := by
    intro x; rw [hupd, hBi]
  simp only [hev, h2, h3]
  rw [integral_mul_const, integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1
  convert (MassGap.ActionSplit.integral_eval_cvol μ (⟨i₀, rfl⟩ : Subtype p)
      (fun g => K (g * W ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p).symm
        (fun _ => 1, y)))) (hK.comp (measurable_mul_const _))).trans
    (integral_mul_right_eq_self (fun g => K g) _)
  all_goals rfl

#print axioms integral_shift_factor

end OneLink

/-! ## The Haar floor -/

variable {N : ℕ}

/-- The Haar variance of the real trace, `∫ reTr² − (∫ reTr)²`.

DERIVED: the `2` is the second moment's exponent. -/
noncomputable def varReTr (N : ℕ) : ℝ :=
  (∫ g, MassGap.HaarVariance.reTr (N := N) g ^ 2 ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))
    - (∫ g, MassGap.HaarVariance.reTr (N := N) g ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ^ 2

/-- **`varReTr N > 0` at `2 ≤ N`.** `HaarVariance.haar_variance_reTr_pos` in the second-moment form
(`ActionSplit.integral_centred_eq`).

DERIVED: the `2` is the rank bound and the second moment's exponent; the `0` is the strict floor. -/
theorem varReTr_pos (hN2 : 2 ≤ N) : 0 < varReTr N := by
  obtain ⟨Ch, hCh⟩ := MassGap.ActionSplit.exists_bound_of_continuous
    (MassGap.HaarVariance.continuous_reTr (N := N))
  have hm : Measurable (MassGap.HaarVariance.reTr (N := N)) :=
    MassGap.HaarVariance.continuous_reTr.measurable
  have hint : Integrable (MassGap.HaarVariance.reTr (N := N))
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
    MassGap.GibbsSpec.integrable_of_bounded _ hm hCh
  have hint2 : Integrable (fun g => MassGap.HaarVariance.reTr (N := N) g ^ 2)
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
    MassGap.GibbsSpec.integrable_of_bounded _ (hm.pow_const 2) (fun g => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (MassGap.HaarVariance.reTr g)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hCh g) 2)
  have hbridge : varReTr N = ProbabilityTheory.variance (MassGap.HaarVariance.reTr (N := N))
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) := by
    unfold varReTr
    rw [ProbabilityTheory.variance_eq_integral hm.aemeasurable,
      MassGap.ActionSplit.integral_centred_eq _ _ hint hint2
        (∫ g, MassGap.HaarVariance.reTr (N := N) g
          ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))]
    ring
  rw [hbridge]
  exact MassGap.HaarVariance.haar_variance_reTr_pos hN2

#print axioms varReTr_pos

/-- **Every centred second moment of `wilsonDensity` under Haar is at least `varReTr N / N²`.**
`wilsonDensity g − c = −(1/N)(reTr g − N(1 − c))`, and the centred second moment of `reTr` about any
point is at least its variance (`ActionSplit.variance_le_integral_centred`).

DERIVED: the `2` is the square; the `1` is `wilsonDensity`'s constant term; the `0` is `hN`. -/
theorem integral_wilsonDensity_centred_ge (hN : N ≠ 0) (c : ℝ) :
    varReTr N / (N : ℝ) ^ 2
      ≤ ∫ g, (MassGap.WilsonAction.wilsonDensity g - c) ^ 2
          ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) := by
  obtain ⟨Ch, hCh⟩ := MassGap.ActionSplit.exists_bound_of_continuous
    (MassGap.HaarVariance.continuous_reTr (N := N))
  have hm : Measurable (MassGap.HaarVariance.reTr (N := N)) :=
    MassGap.HaarVariance.continuous_reTr.measurable
  have hint : Integrable (MassGap.HaarVariance.reTr (N := N))
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
    MassGap.GibbsSpec.integrable_of_bounded _ hm hCh
  have hint2 : Integrable (fun g => MassGap.HaarVariance.reTr (N := N) g ^ 2)
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
    MassGap.GibbsSpec.integrable_of_bounded _ (hm.pow_const 2) (fun g => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (MassGap.HaarVariance.reTr g)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hCh g) 2)
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hpt : ∀ g : MassGap.SUN.SU N, (MassGap.WilsonAction.wilsonDensity g - c) ^ 2
      = (1 / (N : ℝ) ^ 2) * (MassGap.HaarVariance.reTr g - (N : ℝ) * (1 - c)) ^ 2 := by
    intro g
    unfold MassGap.WilsonAction.wilsonDensity MassGap.HaarVariance.reTr
    field_simp
    ring
  simp only [hpt]
  rw [integral_const_mul]
  have hv := MassGap.ActionSplit.variance_le_integral_centred _ _ hint hint2 ((N : ℝ) * (1 - c))
  unfold varReTr
  rw [div_eq_mul_inv, one_div, mul_comm ((N : ℝ) ^ 2)⁻¹]
  exact mul_le_mul_of_nonneg_right hv (by positivity)

#print axioms integral_wilsonDensity_centred_ge

/-! ## The floor in a free box -/

/-- **A plaquette's holonomy is its first link times the product of the other three.**

DERIVED: no numeral. -/
theorem ihol_eq_head_mul (q : MassGap.GibbsSpec.IPlaq) (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    MassGap.GibbsSpec.ihol q U
      = U (q.1.1, q.2) * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
          * ((U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹)) := by
  unfold MassGap.GibbsSpec.ihol MassGap.WilsonLattice.wilsonHol MassGap.GibbsSpec.ibd
  simp [List.prod_cons]

#print axioms ihol_eq_head_mul

/-- A state evaluates a centred square as the variance: `ν((f − c)²) = ν(f²) − 2c ν(f) + c²`.

DERIVED: the `2` is the square's cross term; the `1` is the constant observable. -/
theorem state_centred_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (c : ℝ) :
    ν ((f - c • 1) * (f - c • 1)) = ν (f * f) - 2 * c * ν f + c ^ 2 := by
  have he : (f - c • 1) * (f - c • 1) = f * f - (2 * c) • f + (c ^ 2) • (1 : C(X, ℝ)) := by
    ext x; simp; ring
  rw [he, MassGap.DLRLimit.State.map_add, MassGap.DLRLimit.State.map_sub,
    MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_smul, ν.map_one]
  ring

#print axioms state_centred_sq

/-! ## A non-zero vector orthogonal to the vacuum -/

/-- **A plaquette in the reflection plane, with neither direction `τ`, is fixed by the reflection at
`2p`**: `ireflPlaq` keeps its directions and reflects its base site, which the plane fixes.

DERIVED: `2` is the plane-to-constant doubling; `4` is the dimension. -/
theorem ireflPlaq_plane (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (h1 : q.1.1 ≠ τ) (h2 : q.1.2 ≠ τ) (hq : q.2 τ = p) :
    MassGap.LatticeReflection.ireflPlaq τ (2 * p) q = q := by
  unfold MassGap.LatticeReflection.ireflPlaq
  rw [if_neg h1, if_neg h2]
  obtain ⟨⟨a, b⟩, x⟩ := q
  simp only at hq ⊢
  congr 1
  unfold MassGap.LatticeReflection.ireflSite
  rw [Function.update_eq_self_iff, hq]
  ring

#print axioms ireflPlaq_plane

end MassGap.PlaneVariance
