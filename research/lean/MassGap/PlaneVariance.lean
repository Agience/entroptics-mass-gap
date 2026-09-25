import Mathlib
import MassGap.FreeLimit
import MassGap.StrongCouplingGap

/-!
# A plaquette's variance, bounded below uniformly in the volume

At `SU N`, `2 ≤ N`, `0 ≤ β`, the variance of a plaquette observable in every free box state is at least
`e^{−32β} · Var_Haar(reTr) / N²` (`stateFree_var_iplaqObs_ge`), so it stays positive in the limit
state `ν` (`nu_var_iplaqObs_ge`). A plaquette in the reflection plane is fixed by the reflection, so
its mean-subtracted class in the gauge-invariant GNS space has squared norm equal to that variance,
and it is a non-zero vector orthogonal to the vacuum (`exists_ne_zero_orth_vacuum`).

The floor conditions on every link but the plaquette's first, `l₀`. The observable is then
`g ↦ wilsonDensity(g · W)` with `W` fixed by the other links, whose Haar integral does not depend on `W`
by right-invariance (`integral_shift_factor`); the free weight's factor at `l₀` lies in
`[e^{−32β}, 1]`, since at most `16` box plaquettes carry `l₀` (`ReflectionHalfSpace.card_touching_le`),
and the rest of the weight does not read `l₀`. `SpecVarianceFloor.spec_variance_floor` is the same
argument for a single-link observable and the fixed-boundary kernel.
-/

namespace MassGap.PlaneVariance

open MeasureTheory MassGap.ReflectionHalfSpace

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
(`ActionSplit.integral_centred_eq`), as in `SpecVarianceFloor.wilson_eventual_variance_floor`.

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

/-- A lattice step moves the site: `ishift μ x ≠ x`. The plaquette's first link and its other three
are distinct because of it.

DERIVED: the `4` is the dimension. -/
theorem ishift_ne (μ : Fin 4) (x : MassGap.GibbsSpec.ISite) : MassGap.GibbsSpec.ishift μ x ≠ x := by
  intro h
  have := congrFun h μ
  simp [MassGap.GibbsSpec.ishift] at this

#print axioms ishift_ne

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

open scoped Classical in
/-- **The plaquette variance in a free box is at least `e^{−32β} · varReTr N / N²`.** For `q` in the
box `Λ`, at `0 ≤ β`, every boundary configuration.

The free weight splits into the plaquettes carrying the first link `l₀` — at most `16`
(`ReflectionHalfSpace.card_touching_le`), so their factor lies in `[e^{−32β}, 1]` — and the rest, which
does not read `l₀`. The centred square reads `l₀` through `g ↦ wilsonDensity(g · W)` with `W` built from
the other three links (`ihol_eq_head_mul`), so `integral_shift_factor` integrates it out against the
rest to `(∫ (wilsonDensity − c)²) · ∫ rest`, which `integral_wilsonDensity_centred_ge` bounds; the
partition function is at most `∫ rest`.

DERIVED: `32 = 2 · 16`, the density's ceiling times the plaquettes carrying one link; `0` and `2` are
the density's range and the sign of `β`; `2` is also the square's exponent. -/
theorem stateFree_var_iplaqObs_ge (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (q : MassGap.GibbsSpec.IPlaq) (hq : q ∈ iplqAll Λ) :
    Real.exp (-(β * 32)) * (varReTr N / (N : ℝ) ^ 2)
      ≤ stateFree MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
          β Λ ω (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
            * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
        - (stateFree MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
          β Λ ω (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)) ^ 2 := by
  classical
  set ν := stateFree MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
    β Λ ω with hν
  set φ := MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q with hφ
  set m := ν φ with hm
  have hvar : ν (φ * φ) - m ^ 2 = ν ((φ - m • 1) * (φ - m • 1)) := by
    rw [state_centred_sq]; ring
  rw [hvar]
  -- the plaquette's links
  obtain ⟨hqin, hqnd⟩ := mem_iplqAll.mp hq
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp hqin
  have hl0 : ((q.1.1, q.2) : MassGap.InfiniteLattice.ILink) ∈ Λ :=
    hlinks _ (MassGap.BoxCube.head_link_mem q)
  set l₀ : ↥Λ := ⟨(q.1.1, q.2), hl0⟩ with hl₀
  -- the split of the free weight
  set Aset : Finset MassGap.GibbsSpec.IPlaq :=
    (iplqAll Λ).filter (fun r => ((q.1.1, q.2) : MassGap.InfiniteLattice.ILink)
      ∈ MassGap.GibbsSpec.ilinks r) with hAset
  set Bset : Finset MassGap.GibbsSpec.IPlaq :=
    (iplqAll Λ).filter (fun r => ((q.1.1, q.2) : MassGap.InfiniteLattice.ILink)
      ∉ MassGap.GibbsSpec.ilinks r) with hBset
  have hAcard : Aset.card ≤ 16 := by
    refine le_trans (Finset.card_le_card (fun r hr => ?_))
      (card_touching_le ((q.1.1, q.2) : MassGap.InfiniteLattice.ILink))
    exact MassGap.GibbsSpec.mem_touching (Finset.mem_filter.mp hr).2
  set B : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ := fun u =>
    Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity Bset
      (MassGap.GibbsSpec.splice Λ u ω)) with hB
  have hwt : ∀ u, wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u
      = Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity Aset
          (MassGap.GibbsSpec.splice Λ u ω)) * B u := by
    intro u
    rw [hB]
    simp only [wtFree, MassGap.GibbsSpec.actionOn, hAset, hBset]
    rw [← Real.exp_add, ← mul_add, Finset.sum_filter_add_sum_filter_not]
  -- the update at l₀ leaves the other links alone
  have hsplice_upd : ∀ (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) (g : MassGap.SUN.SU N)
      (l : MassGap.InfiniteLattice.ILink), l ≠ (q.1.1, q.2) →
      MassGap.GibbsSpec.splice Λ (Function.update u l₀ g) ω l = MassGap.GibbsSpec.splice Λ u ω l := by
    intro u g l hl
    by_cases hlΛ : l ∈ Λ
    · rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ,
        Function.update_of_ne (fun h => hl (congrArg Subtype.val h))]
    · rw [MassGap.GibbsSpec.splice_not_mem hlΛ, MassGap.GibbsSpec.splice_not_mem hlΛ]
  have hBi : ∀ u g, B (Function.update u l₀ g) = B u := by
    intro u g
    simp only [hB]
    rw [MassGap.GibbsSpec.actionOn_congr _ Bset _ _ (fun r hr l hl => hsplice_upd u g l (fun h =>
      (Finset.mem_filter.mp hr).2 (h ▸ hl)))]
  -- the observable as a function of the first link
  set W : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → MassGap.SUN.SU N := fun u =>
    MassGap.GibbsSpec.splice Λ u ω (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
      * ((MassGap.GibbsSpec.splice Λ u ω (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹
        * (MassGap.GibbsSpec.splice Λ u ω (q.1.2, q.2))⁻¹) with hW
  have hne1 : ((q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2) : MassGap.InfiniteLattice.ILink)
      ≠ (q.1.1, q.2) := fun h => hqnd (congrArg Prod.fst h).symm
  have hne2 : ((q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2) : MassGap.InfiniteLattice.ILink)
      ≠ (q.1.1, q.2) := fun h => ishift_ne q.1.2 q.2 (congrArg Prod.snd h)
  have hne3 : ((q.1.2, q.2) : MassGap.InfiniteLattice.ILink) ≠ (q.1.1, q.2) :=
    fun h => hqnd (congrArg Prod.fst h).symm
  have hWi : ∀ u g, W (Function.update u l₀ g) = W u := by
    intro u g
    simp only [hW, hsplice_upd u g _ hne1, hsplice_upd u g _ hne2, hsplice_upd u g _ hne3]
  have hobs : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      φ (MassGap.GibbsSpec.splice Λ u ω) = MassGap.WilsonAction.wilsonDensity (u l₀ * W u) := by
    intro u
    have h := ihol_eq_head_mul q (MassGap.GibbsSpec.splice Λ u ω)
    rw [MassGap.GibbsSpec.splice_mem hl0] at h
    show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q (MassGap.GibbsSpec.splice Λ u ω)) = _
    exact congrArg MassGap.WilsonAction.wilsonDensity h
  -- measurability and bounds
  have hsm : Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      MassGap.GibbsSpec.splice Λ u ω) := MassGap.GibbsSpec.measurable_splice_left Λ ω
  have hWm : Measurable W := by
    simp only [hW]
    exact ((measurable_pi_apply _).comp hsm).mul
      (((measurable_pi_apply _).comp hsm).inv.mul ((measurable_pi_apply _).comp hsm).inv)
  have hBm : Measurable B := by
    simp only [hB]
    exact Real.continuous_exp.measurable.comp
      (((MassGap.GibbsSpec.measurable_actionOn MassGap.WilsonAction.measurable_wilsonDensity _).comp
        hsm).const_mul (-β))
  have hBb : ∀ u, |B u| ≤ Real.exp (|β| * ((Bset.card : ℝ) * 2)) := fun u =>
    abs_exp_neg_actionOn_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β _ _
  have hB0 : ∀ u, 0 ≤ B u := fun u => (Real.exp_pos _).le
  have hKm : Measurable (fun g : MassGap.SUN.SU N => (MassGap.WilsonAction.wilsonDensity g - m) ^ 2) :=
    (MassGap.WilsonAction.measurable_wilsonDensity.sub_const m).pow_const 2
  have hKb : ∀ g : MassGap.SUN.SU N,
      |(MassGap.WilsonAction.wilsonDensity g - m) ^ 2| ≤ (2 + |m|) ^ 2 := by
    intro g
    have h0 := MassGap.WilsonAction.wilsonDensity_nonneg hN g
    have h2 := MassGap.WilsonAction.wilsonDensity_le_two hN g
    rw [abs_of_nonneg (sq_nonneg _)]
    have := neg_abs_le m
    have := le_abs_self m
    nlinarith
  -- the factor at l₀
  have hA : ∀ u, Real.exp (-(β * 32)) ≤ Real.exp (-β * MassGap.GibbsSpec.actionOn
      MassGap.WilsonAction.wilsonDensity Aset (MassGap.GibbsSpec.splice Λ u ω)) := by
    intro u
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_actionOn_ge
      (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
      β Aset (MassGap.GibbsSpec.splice Λ u ω))
    rw [abs_of_nonneg hβ]
    have : (Aset.card : ℝ) ≤ 16 := by exact_mod_cast hAcard
    nlinarith
  -- the specification as a ratio
  have hZpos := partFree_pos MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω
  have hspec : ν ((φ - m • 1) * (φ - m • 1))
      = (∫ u, (MassGap.WilsonAction.wilsonDensity (u l₀ * W u) - m) ^ 2
          * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u
          ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))))
        / partFree (φ := MassGap.WilsonAction.wilsonDensity) β Λ ω := by
    show specFree β Λ ω (fun u => ((φ - m • 1) * (φ - m • 1)) (MassGap.GibbsSpec.splice Λ u ω)) = _
    unfold specFree
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    rw [hobs u]
    ring
  rw [hspec, le_div_iff₀ hZpos]
  -- numerator ≥ e^{−32β} · (∫ (wD − m)²) · ∫ B
  have hfac := integral_shift_factor (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) l₀
    hKm hKb hWm hWi hBm hBb hBi
  beta_reduce at hfac
  have hlow := integral_wilsonDensity_centred_ge hN m
  have hZle : partFree (φ := MassGap.WilsonAction.wilsonDensity) β Λ ω
      ≤ ∫ u, B u ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) := by
    unfold partFree
    refine integral_mono (MassGap.GibbsSpec.integrable_of_bounded _
      (measurable_wtFree MassGap.WilsonAction.measurable_wilsonDensity β Λ ω)
      (wtFree_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω))
      (MassGap.GibbsSpec.integrable_of_bounded _ hBm hBb) (fun u => ?_)
    rw [hwt u]
    have h1 := MassGap.GibbsSpec.exp_neg_actionOn_le_one
      (MassGap.WilsonAction.wilsonDensity_nonneg hN) hβ Aset (MassGap.GibbsSpec.splice Λ u ω)
    exact mul_le_of_le_one_left (hB0 u) h1
  have hnum : Real.exp (-(β * 32))
        * ((∫ g, (MassGap.WilsonAction.wilsonDensity g - m) ^ 2
            ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))
          * ∫ u, B u ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))))
      ≤ ∫ u, (MassGap.WilsonAction.wilsonDensity (u l₀ * W u) - m) ^ 2
          * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u
          ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) := by
    rw [← hfac, ← integral_const_mul]
    refine integral_mono ((MassGap.GibbsSpec.integrable_of_bounded _
        ((hKm.comp ((measurable_pi_apply l₀).mul hWm)).mul hBm)
        (fun u => by
          rw [abs_mul]
          exact mul_le_mul (hKb _) (hBb u) (abs_nonneg _) ((abs_nonneg _).trans (hKb 1)))).const_mul _)
      (MassGap.GibbsSpec.integrable_of_bounded _
        ((hKm.comp ((measurable_pi_apply l₀).mul hWm)).mul
          (measurable_wtFree MassGap.WilsonAction.measurable_wilsonDensity β Λ ω))
        (fun u => by
          rw [abs_mul]
          exact mul_le_mul (hKb _) (wtFree_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω u) (abs_nonneg _)
            ((abs_nonneg _).trans (hKb 1)))) (fun u => ?_)
    rw [hwt u]
    have hsq : 0 ≤ (MassGap.WilsonAction.wilsonDensity (u l₀ * W u) - m) ^ 2 := sq_nonneg _
    calc Real.exp (-(β * 32)) * ((MassGap.WilsonAction.wilsonDensity (u l₀ * W u) - m) ^ 2 * B u)
        = (MassGap.WilsonAction.wilsonDensity (u l₀ * W u) - m) ^ 2 * (Real.exp (-(β * 32)) * B u) := by
          ring
      _ ≤ (MassGap.WilsonAction.wilsonDensity (u l₀ * W u) - m) ^ 2
          * (Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity Aset
              (MassGap.GibbsSpec.splice Λ u ω)) * B u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hA u) (hB0 u)) hsq
  have hBint0 : 0 ≤ ∫ u, B u ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) :=
    integral_nonneg hB0
  have hV0 : 0 ≤ varReTr N / (N : ℝ) ^ 2 :=
    (div_pos (varReTr_pos hN2) (pow_pos (Nat.cast_pos.mpr (by omega)) 2)).le
  calc Real.exp (-(β * 32)) * (varReTr N / (N : ℝ) ^ 2) * partFree (φ := MassGap.WilsonAction.wilsonDensity) β Λ ω
      ≤ Real.exp (-(β * 32)) * (varReTr N / (N : ℝ) ^ 2)
          * ∫ u, B u ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) :=
        mul_le_mul_of_nonneg_left hZle (mul_nonneg (Real.exp_pos _).le hV0)
    _ ≤ Real.exp (-(β * 32))
          * ((∫ g, (MassGap.WilsonAction.wilsonDensity g - m) ^ 2
              ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))
            * ∫ u, B u ∂(MassGap.ActionSplit.cvol ↥Λ (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlow hBint0) (Real.exp_pos _).le
    _ ≤ _ := hnum

#print axioms stateFree_var_iplaqObs_ge

/-! ## The floor in the limit state -/

/-- **The plaquette variance stays at least `e^{−32β} · varReTr N / N²` in the limit state.** Along
`mixCube` the box eventually holds the plaquette (`ReflectionHalfSpace.eventually_mem_iplqAll`), where
`stateFree_var_iplaqObs_ge` holds, and both moments converge by `htend`.

DERIVED: `32` is the box floor's constant; `2` is the rank bound and the square; `0` is the sign of
`β` and the excluded rank; `1` is the identity boundary configuration; `4` is the dimension. -/
theorem nu_var_iplaqObs_ge (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) :
    Real.exp (-(β * 32)) * (varReTr N / (N : ℝ) ^ 2)
      ≤ ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
            * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
        - (ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)) ^ 2 := by
  have hlim := (htend (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
      * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)).sub
    ((htend (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)).pow 2)
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_mem_iplqAll τ p q hq] with n hn
  exact stateFree_var_iplaqObs_ge hN2 hN hβ (mixCube τ p n) 1 q hn

#print axioms nu_var_iplaqObs_ge

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

/-- **The class of a mean-subtracted plane plaquette is a non-zero vector orthogonal to the vacuum.**
At `2 ≤ N`, `0 ≤ β` and the limit state `ν`, the plaquette `q` with directions `τ + 1`, `τ + 2` at a
site on the plane `x_τ = p` is in the gauge-invariant algebra, and so is `x = φ_q − ν(φ_q)`. The vacuum
pairs with `[x]` as `ν(x) = 0` (`StrongCouplingGap.inner_vacGNS_mk_gaugeInv`), and `‖[x]‖² = ν(θx · x)`
(`GaugeInvariantAlgebra.gaugeInv_form_pow` at `0`), with `θx = x` since the reflection fixes `q`
(`ireflPlaq_plane`); that is the variance of `φ_q` in `ν`, positive by `nu_var_iplaqObs_ge`.

DERIVED: `1` and `2` are the plaquette's directions `τ + 1`, `τ + 2` and the identity boundary
configuration; `2` is also the rank bound and the doubling of the plane; `0` is the excluded rank,
the sign of `β`, the vacuum pairing and the site's other coordinates; `4` is the dimension. -/
theorem exists_ne_zero_orth_vacuum (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    ∃ y : MassGap.Transfer.GNS
        (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
      y ≠ 0 ∧ (inner ℝ (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0 := by
  classical
  have hinv := wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
  have hpos := wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
  have hnu := wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
    (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)
  -- the plane plaquette
  set x₀ : MassGap.GibbsSpec.ISite := fun i => if i = τ then p else 0 with hx₀
  set q : MassGap.GibbsSpec.IPlaq := ((τ + 1, τ + 2), x₀) with hqdef
  have h1 : q.1.1 ≠ τ := by simp [hqdef]
  have h2 : q.1.2 ≠ τ := by
    simp only [hqdef]
    intro h
    have := congrArg (fun i : Fin 4 => (i : ℕ)) h
    fin_cases τ <;> simp_all
  have hnd : q.1.1 ≠ q.1.2 := by
    simp only [hqdef]
    fin_cases τ <;> decide
  have hq2 : q.2 τ = p := by simp [hqdef, hx₀]
  set φ := MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q with hφ
  have hφmem : φ ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
    MassGap.GaugeInvariantAlgebra.iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le q τ p hq2.symm.le
  set c := ν φ with hc
  have hxmem : φ - c • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
    Submodule.sub_mem _ hφmem
      (Submodule.smul_mem _ c (MassGap.GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg τ p))
  set x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
    ⟨φ - c • 1, hxmem⟩ with hxdef
  refine ⟨MassGap.Transfer.GNS.mk
    (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm x, ?_, ?_⟩
  · -- non-zero: its squared norm is the variance
    intro h0
    have hθφ : MassGap.LatticeReflection.ireflObs τ (2 * p) φ = φ := by
      rw [hφ, MassGap.GaugeInvariantAlgebra.ireflObs_iplaqObs, ireflPlaq_plane τ p q h1 h2 hq2]
    have hθ1 : MassGap.LatticeReflection.ireflObs τ (2 * p)
        (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 := by
      ext U; rfl
    have hθx : MassGap.LatticeReflection.ireflObs τ (2 * p) (φ - c • 1) = φ - c • 1 := by
      rw [map_sub, map_smul, hθφ, hθ1]
    have hform := MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu x 0
    have hin := MassGap.Transfer.GNS.inner_mk
      (P := (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm) x x
    rw [h0, inner_zero_left] at hin
    have hvar := nu_var_iplaqObs_ge hN2 hN hβ τ p ν htend q hnd
    have hcent := state_centred_sq ν φ c
    have hpos' : 0 < Real.exp (-(β * 32)) * (varReTr N / (N : ℝ) ^ 2) :=
      mul_pos (Real.exp_pos _) (div_pos (varReTr_pos hN2) (pow_pos (Nat.cast_pos.mpr (by omega)) 2))
    have e1 : (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm.form x x
        = (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).form x
            (((MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).T ^ 0) x) := by
      first
        | rfl
        | (rw [pow_zero]; rfl)
        | rw [pow_zero]
    have hform' : (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm.form x x
        = ν ((φ - c • 1) * (φ - c • 1)) := by
      rw [e1, hform]
      show ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (φ - c • 1) * (φ - c • 1)) = _
      rw [hθx]
    rw [hform', hcent] at hin
    nlinarith
  · -- orthogonal to the vacuum
    rw [show (inner ℝ (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS
        (MassGap.Transfer.GNS.mk
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm x) : ℝ)
        = ν (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) from
      MassGap.StrongCouplingGap.inner_vacGNS_mk_gaugeInv τ p ν hinv hpos hnu x]
    show ν (φ - c • 1) = 0
    rw [MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one]
    ring

#print axioms exists_ne_zero_orth_vacuum

/-- **M on the lattice with content.** At `SU N`, `2 ≤ N`, for every `0 < β` with `coreRate 64 β < 1`,
there is an infinite-volume state `ν`, the `atTop` limit of the free box states, at which the
transfer operator of the gauge-invariant theory is self-adjoint with spectrum in `{1} ∪ [0, ρ]`,
`ρ = coreRate 64 β`, `1` at the top; every vector orthogonal to the vacuum is contracted by `ρ`,
`‖Tq y‖ ≤ ρ ‖y‖` (`StrongCouplingGap.norm_Tq_le_of_orth`), a gap `Δ = −log ρ > 0`; and there is such a
vector that is not zero (`exists_ne_zero_orth_vacuum`), so the contraction acts on a non-zero space.
`FreeLimit.wilson_gaugeInv_mass_gap_lattice` supplies the rest.

DERIVED: `16 * 4` is the box touch-degree bound; `4` is the dimension; `2` is the rank bound and the
density's ceiling; `0` is the coupling's lower end, the spectrum's bottom and the vacuum pairing; `1`
is the vacuum eigenvalue, the geometric threshold and the identity boundary configuration. -/
theorem wilson_gaugeInv_mass_gap_lattice_nontrivial (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) {β : ℝ}
    (hβ : 0 < β) (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) :
    ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
      (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg (by omega : N ≠ 0))
            (MassGap.WilsonAction.wilsonDensity_le_two (by omega : N ≠ 0)) β (mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f))),
      (IsSelfAdjoint (MassGap.GNSHilbert.opT
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend))
      ∧ 0 < -Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β)
      ∧ spectrum ℝ (MassGap.GNSHilbert.opT
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β))))
      ∧ IsGreatest (spectrum ℝ (MassGap.GNSHilbert.opT
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend))) 1)
      ∧ (∀ y : MassGap.Transfer.GNS
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend).toReflForm,
          (inner ℝ (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend).vacGNS y
            : ℝ) = 0 →
          ‖(MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend).Tq y‖
            ≤ MassGap.StrongCoupling.coreRate (16 * 4) β * ‖y‖)
      ∧ ∃ y : MassGap.Transfer.GNS
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend).toReflForm,
          y ≠ 0 ∧ (inner ℝ (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) β ν htend).vacGNS y
            : ℝ) = 0 := by
  have hN : N ≠ 0 := by omega
  obtain ⟨ν, htend⟩ := MassGap.FreeLimit.exists_tendsto_stateFree hN hβ.le hr τ p
  exact ⟨ν, htend,
    MassGap.StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling τ p hN hβ hr ν htend,
    fun y hy => MassGap.StrongCouplingGap.norm_Tq_le_of_orth τ p hN hβ hr ν htend y hy,
    exists_ne_zero_orth_vacuum τ p hN2 hN hβ.le ν htend⟩

#print axioms wilson_gaugeInv_mass_gap_lattice_nontrivial

end MassGap.PlaneVariance
