import Mathlib
import MassGap.BoxCompare
import MassGap.BoxCube
import MassGap.GeneralDecay
import MassGap.StrongCouplingGap

/-!
# The free box states converge

The free-boundary box states along `ReflectionHalfSpace.mixCube` are Cauchy on every continuous
observable at `0 ≤ β` with `coreRate 64 β < 1`, so the subsequential limit of
`ClayCapstone.exists_dlr_limit_of_free_family` is their `atTop` limit.

A sub-box's state is a restriction of an ambient box's Wilson system: the links outside the sub-box
integrate out (`integral_restrict_marginal`), so `stateFree Λ f` is `BoxCompare.meanR` over the
sub-box's plaquettes (`stateFree_eq_meanR`). `BoxCompare.meanR_sub_abs_le` then compares two sub-boxes
inside their union.
-/

namespace MassGap.FreeLimit

open MeasureTheory MassGap.ReflectionHalfSpace

/-! ## Links outside a sub-box integrate out -/

section Marginal

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

open scoped Classical in
/-- **A function of a sub-box's links integrates against the box measure as against the sub-box's.**
For `V ⊆ Λ` and `F` bounded and measurable on `V`'s configurations,
`∫ F (u|_V) d(Haar^Λ) = ∫ F d(Haar^V)`. `ActionSplit.integral_cvol_split_iterated` splits the box's
links into those in `V` and the rest; the integrand does not read the rest, which integrates to one;
`ReflectionHalfSpace.integral_vblock` reindexes the block in `V` to `V`'s own links.

DERIVED: no numeral. -/
theorem integral_restrict_marginal (μ : Measure G) [IsProbabilityMeasure μ]
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (F : MassGap.GibbsSpec.VConf G V → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ v, |F v| ≤ C) :
    ∫ u, F (fun w : ↥V => u ⟨(w : MassGap.InfiniteLattice.ILink), hVΛ w.2⟩)
        ∂(MassGap.ActionSplit.cvol ↥Λ μ)
      = ∫ v, F v ∂(MassGap.GibbsSpec.vol μ V) := by
  classical
  set p : ↥Λ → Prop := fun i => (i : MassGap.InfiniteLattice.ILink) ∈ V with hp
  have hres : Measurable (fun u : ↥Λ → G =>
      fun w : ↥V => u ⟨(w : MassGap.InfiniteLattice.ILink), hVΛ w.2⟩) :=
    measurable_pi_lambda _ (fun w => measurable_pi_apply _)
  have hint : Integrable
      (fun z : ((Subtype p → G) × ({i : ↥Λ // ¬ p i} → G)) =>
        F (fun w : ↥V => ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ => G) p).symm z)
          ⟨(w : MassGap.InfiniteLattice.ILink), hVΛ w.2⟩))
      ((Measure.pi fun _ : Subtype p => μ).prod (Measure.pi fun _ : {i : ↥Λ // ¬ p i} => μ)) :=
    (integrable_const C).mono'
      ((hF.comp (hres.comp (MeasurableEquiv.measurable _))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hFb _))
  rw [MassGap.ActionSplit.integral_cvol_split_iterated μ p _ hint]
  have hpt : ∀ (x : Subtype p → G) (y : {i : ↥Λ // ¬ p i} → G),
      (fun w : ↥V => ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ => G) p).symm (x, y))
          ⟨(w : MassGap.InfiniteLattice.ILink), hVΛ w.2⟩)
        = fun w : ↥V => x ((MassGap.GibbsSpec.linkSubEquiv hVΛ).symm w) := by
    intro x y
    funext w
    have hw : p ⟨(w : MassGap.InfiniteLattice.ILink), hVΛ w.2⟩ := w.2
    simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, dif_pos hw]
    rfl
  simp_rw [hpt]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact integral_vblock μ hVΛ F

#print axioms integral_restrict_marginal

end Marginal

/-! ## A sub-box's state as a restriction of an ambient box -/

variable {N : ℕ}

open scoped Classical in
/-- The ambient box's plaquettes that lie in the sub-box `Λ`.

DERIVED: no numeral. -/
noncomputable def subPlaq (Λ'' Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥(iplqAll Λ'') :=
  Finset.univ.filter (fun q => (q : MassGap.GibbsSpec.IPlaq) ∈ iplqAll Λ)

open scoped Classical in
/-- The sub-box's plaquettes, as ambient plaquettes, are exactly `iplqAll Λ`.

DERIVED: no numeral. -/
theorem subPlaq_map (Λ'' Λ : Finset MassGap.InfiniteLattice.ILink) (hsub : Λ ⊆ Λ'') :
    (subPlaq Λ'' Λ).map (Function.Embedding.subtype _) = iplqAll Λ := by
  ext q
  simp only [subPlaq, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨q', hq', rfl⟩; exact hq'
  · intro hq
    refine ⟨⟨q, ?_⟩, hq, rfl⟩
    obtain ⟨hin, hnd⟩ := mem_iplqAll.mp hq
    refine mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr (fun l hl => hsub
      (MassGap.GibbsSpec.mem_plaqsIn.mp hin l hl)), hnd⟩

#print axioms subPlaq_map

/-- The restriction of an ambient configuration to the sub-box.

DERIVED: no numeral. -/
def restr {G : Type} {Λ'' Λ : Finset MassGap.InfiniteLattice.ILink} (hsub : Λ ⊆ Λ'')
    (u : MassGap.GibbsSpec.VConf G Λ'') : MassGap.GibbsSpec.VConf G Λ :=
  fun w => u ⟨(w : MassGap.InfiniteLattice.ILink), hsub w.2⟩

/-- On the sub-box's links the two splices agree.

DERIVED: no numeral. -/
theorem splice_restr_eq {G : Type} {Λ'' Λ : Finset MassGap.InfiniteLattice.ILink} (hsub : Λ ⊆ Λ'')
    (u : MassGap.GibbsSpec.VConf G Λ'') (ω : MassGap.GibbsSpec.IConf G)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ Λ) :
    MassGap.GibbsSpec.splice Λ'' u ω l = MassGap.GibbsSpec.splice Λ (restr hsub u) ω l := by
  rw [MassGap.GibbsSpec.splice_mem (hsub hl), MassGap.GibbsSpec.splice_mem hl]
  rfl

#print axioms splice_restr_eq

open scoped Classical in
/-- **The restricted Boltzmann weight of the ambient box is the sub-box's free weight**:
`subBoltz (boxBd Λ'') β (subPlaq Λ'' Λ) u = wtFree Λ ω (u|_Λ)`, for any boundary `ω`. Each plaquette's
box holonomy is its lattice holonomy on the splice (`ReflectionHalfSpace.wilsonHol_boxBd`), which
reads only the sub-box's links; the product over the ambient copies of the sub-box's plaquettes is the
product over `iplqAll Λ` (`subPlaq_map`), and that is the exponential of the action.

DERIVED: no numeral. -/
theorem subBoltz_subPlaq (β : ℝ) {Λ'' Λ : Finset MassGap.InfiniteLattice.ILink} (hsub : Λ ⊆ Λ'')
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ'') :
    MassGap.StrongCoupling.subBoltz (Nc := N) (boxBd Λ'') β (subPlaq Λ'' Λ) u
      = wtFree MassGap.WilsonAction.wilsonDensity β Λ ω (restr hsub u) := by
  classical
  unfold MassGap.StrongCoupling.subBoltz wtFree MassGap.GibbsSpec.actionOn
  rw [Finset.mul_sum, Real.exp_sum, ← subPlaq_map Λ'' Λ hsub, Finset.prod_map]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hqΛ : (q : MassGap.GibbsSpec.IPlaq) ∈ iplqAll Λ := (Finset.mem_filter.mp hq).2
  simp only [Function.Embedding.coe_subtype]
  rw [wilsonHol_boxBd Λ'' q u ω,
    MassGap.GibbsSpec.ihol_congr (q : MassGap.GibbsSpec.IPlaq) _ _ (fun l hl =>
      splice_restr_eq hsub u ω (MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqΛ).1 l hl))]
  congr 1
  ring

#print axioms subBoltz_subPlaq

/-- **A sub-box's free state is the restricted mean of the ambient box.** For `Λ ⊆ Λ''` and `f`
continuous and local on `S ⊆ Λ`, `stateFree Λ ω f = meanR (boxBd Λ'') β (subPlaq Λ'' Λ) (f ∘ splice)`.
Both numerator and denominator are integrals of a function of the sub-box's links
(`subBoltz_subPlaq`, locality of `f`), which `integral_restrict_marginal` carries to the sub-box.

DERIVED: the `0` and `2` are the density's range, as `stateFree` takes them. -/
theorem stateFree_eq_meanR (hN : N ≠ 0)
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2) (β : ℝ)
    {Λ'' Λ : Finset MassGap.InfiniteLattice.ILink} (hsub : Λ ⊆ Λ'')
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) {S : Finset MassGap.InfiniteLattice.ILink}
    (hS : S ⊆ Λ)
    (hf : MassGap.InfiniteLattice.IsLocalOn S (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)) :
    stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω f
      = MassGap.BoxCompare.meanR (Nc := N) (boxBd Λ'') β (subPlaq Λ'' Λ)
          (fun u => f (MassGap.GibbsSpec.splice Λ'' u ω)) := by
  classical
  rw [MassGap.BoxCompare.meanR_eq_integral hN _ β _
    (O := fun u => f (MassGap.GibbsSpec.splice Λ'' u ω))
    (f.continuous.comp (continuous_splice_left Λ'' ω)).measurable (MassGap.BoxCube.abs_splice_le Λ'' ω f)]
  have hfloc : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ'',
      f (MassGap.GibbsSpec.splice Λ'' u ω) = f (MassGap.GibbsSpec.splice Λ (restr hsub u) ω) :=
    fun u => hf _ _ (fun l hl => splice_restr_eq hsub u ω (hS hl))
  obtain ⟨Cw, hCw⟩ : ∃ Cw : ℝ, ∀ v, |wtFree MassGap.WilsonAction.wilsonDensity β Λ ω v| ≤ Cw :=
    ⟨_, wtFree_le hφ0 hφ2 β Λ ω⟩
  have hwm := measurable_wtFree (G := MassGap.SUN.SU N) MassGap.WilsonAction.measurable_wilsonDensity β Λ ω
  have hfm : Measurable (fun v : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ v ω)) :=
    (f.continuous.comp (continuous_splice_left Λ ω)).measurable
  have hnum : (∫ u, f (MassGap.GibbsSpec.splice Λ'' u ω)
        * MassGap.StrongCoupling.subBoltz (Nc := N) (boxBd Λ'') β (subPlaq Λ'' Λ) u
        ∂(Measure.pi (fun _ : ↥Λ'' => MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))))
      = ∫ v, f (MassGap.GibbsSpec.splice Λ v ω) * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω v
        ∂(MassGap.GibbsSpec.vol (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) Λ) := by
    have h := integral_restrict_marginal (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) hsub
      (fun v => f (MassGap.GibbsSpec.splice Λ v ω) * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω v)
      (hfm.mul hwm) (C := ‖f‖ * Cw) (fun v => by
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _) (hCw v)
          (abs_nonneg _) (norm_nonneg _))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [hfloc u, subBoltz_subPlaq β hsub ω u]
    rfl
  have hden : (∫ u, MassGap.StrongCoupling.subBoltz (Nc := N) (boxBd Λ'') β (subPlaq Λ'' Λ) u
        ∂(Measure.pi (fun _ : ↥Λ'' => MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))))
      = ∫ v, wtFree MassGap.WilsonAction.wilsonDensity β Λ ω v
        ∂(MassGap.GibbsSpec.vol (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) Λ) := by
    have h := integral_restrict_marginal (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) hsub
      (fun v => wtFree MassGap.WilsonAction.wilsonDensity β Λ ω v) hwm hCw
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [subBoltz_subPlaq β hsub ω u]
    rfl
  rw [hnum, hden]
  rfl

#print axioms stateFree_eq_meanR

/-! ## Geometry: cubes and balls -/

/-- **Every finite link set lies strictly inside a cube.** Each coordinate of each link is bounded by
`M`, the largest coordinate sum; the cube starts at `−M − 1` on every axis with side `2M + 1`.

DERIVED: the `1`s are the strict-inside margin and the lower bound on the side; `2M` covers
`[−M, M]`; the `4` is the dimension. -/
theorem exists_cube (S : Finset MassGap.InfiniteLattice.ILink) :
    ∃ (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ), 1 ≤ R ∧
      ∀ l ∈ S, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R := by
  classical
  let M : ℕ := S.sup (fun l => ∑ i : Fin 4, (l.2 i).natAbs)
  have hM : ∀ l ∈ S, ∀ i : Fin 4, (l.2 i).natAbs ≤ M := by
    intro l hl i
    exact le_trans (Finset.single_le_sum (f := fun j : Fin 4 => (l.2 j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      (Finset.le_sup (f := fun l : MassGap.InfiniteLattice.ILink => ∑ i : Fin 4, (l.2 i).natAbs) hl)
  refine ⟨fun _ => -(M : ℤ) - 1, 2 * M + 1, by omega, fun l hl i => ?_⟩
  have hb := hM l hl i
  dsimp only
  constructor <;> omega

#print axioms exists_cube

open scoped Classical in
/-- The links with every coordinate in `[x₀ i − r, x₀ i + r + 1]`.

DERIVED: the `1` is the step from a plaquette's base to its farthest link; the `4` is the dimension. -/
noncomputable def linkCube (x₀ : MassGap.GibbsSpec.ISite) (r : ℕ) :
    Finset MassGap.InfiniteLattice.ILink :=
  (Finset.univ : Finset (Fin 4)) ×ˢ
    Fintype.piFinset (fun i : Fin 4 => Finset.Icc (x₀ i - r) (x₀ i + r + 1))

open scoped Classical in
/-- Membership in `linkCube`, unfolded.

DERIVED: the `1` and `4` are `linkCube`'s. -/
theorem mem_linkCube {x₀ : MassGap.GibbsSpec.ISite} {r : ℕ} {l : MassGap.InfiniteLattice.ILink} :
    l ∈ linkCube x₀ r ↔ ∀ i : Fin 4, x₀ i - r ≤ l.2 i ∧ l.2 i ≤ x₀ i + r + 1 := by
  unfold linkCube
  simp [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]

#print axioms mem_linkCube

/-- **A plaquette within `k` touch-steps of `a` is within `k` of it on every axis.**
`ReflectionHalfSpace.not_mem_ball_of_axis_gt`, contraposed.

DERIVED: the `4` is the dimension. -/
theorem coord_le_of_mem_ball (Λ : Finset MassGap.InfiniteLattice.ILink) (a q : ↥(iplqAll Λ))
    (k : ℕ) (hq : q ∈ MassGap.StrongCoupling.ball (boxBd Λ) a k) (i : Fin 4) :
    ((q : MassGap.GibbsSpec.IPlaq).2 i - (a : MassGap.GibbsSpec.IPlaq).2 i).natAbs ≤ k := by
  by_contra h
  push_neg at h
  exact not_mem_ball_of_axis_gt Λ i a q k h hq

#print axioms coord_le_of_mem_ball

/-- **A plaquette within `k` touch-steps of `a` lies in any box holding the link cube of radius `k`
around `a`'s base**: its links sit at its base or one step above on each axis
(`ReflectionHalfSpace.ilink_site_coord`).

DERIVED: the `4` is the dimension. -/
theorem mem_iplqAll_of_mem_ball {Λ'' Λ : Finset MassGap.InfiniteLattice.ILink}
    (a q : ↥(iplqAll Λ'')) (k : ℕ) (hq : q ∈ MassGap.StrongCoupling.ball (boxBd Λ'') a k)
    (hcube : linkCube (a : MassGap.GibbsSpec.IPlaq).2 k ⊆ Λ) :
    (q : MassGap.GibbsSpec.IPlaq) ∈ iplqAll Λ := by
  refine mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr (fun l hl =>
    hcube (mem_linkCube.mpr (fun i => ?_))), (mem_iplqAll.mp q.2).2⟩
  have hc := ilink_site_coord i (q : MassGap.GibbsSpec.IPlaq) l hl
  have hb := coord_le_of_mem_ball Λ'' a q k hq i
  omega

#print axioms mem_iplqAll_of_mem_ball

/-! ## The free box states are Cauchy -/

open scoped Classical in
/-- **The free box states along `mixCube` are Cauchy on a local observable.** For `f` continuous and
local on a finite `S`, at `0 ≤ β` with `coreRate 64 β < 1`, every `ε > 0` has an `N₀` past which any
two box states of `f` differ by at most `ε`.

`S` lies strictly inside a cube of side `R` at `x₀` (`exists_cube`); its plaquettes, in the ambient
box `Λₙ ∪ Λₘ`, are the anchor (`BoxCube.cubePlaq`: it contains the halo, is touch-connected, has at
most `U = 16 (R + 1)⁴` members). Pick `k` with `coreConstG · coreRate^(k + 2 − U) ≤ ε`; the boxes
eventually hold the link cube of radius `k` around `x₀` (`ReflectionHalfSpace.mixCube_exhausts`), so the
`k`-ball of the anchor's base lies in both (`mem_iplqAll_of_mem_ball`). Both states are restricted
means of the ambient box (`stateFree_eq_meanR`), and `BoxCompare.meanR_sub_abs_le` bounds their
difference; `coreConstG_mono`, `BoxCube.coreConstG_le_of_le` and `coreRate_mono` carry the bound to
touch degree `64` and anchor size `U`.

DERIVED: `16 * 4` is the box touch-degree bound; `16` and the exponent `4` in `U` are
`card_cubePlaq_le`'s; `2` is `diffTerm`'s two products and the two base plaquettes in `k + 2`; `0`
and `1` are the directions of the two base plaquettes, the sign hypotheses and the geometric
threshold, and the identity boundary configuration. -/
theorem stateFree_cauchy (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) (τ : Fin 4) (p : ℤ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) {S : Finset MassGap.InfiniteLattice.ILink}
    (hf : MassGap.InfiniteLattice.IsLocalOn S (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ m ≥ N₀,
      |stateFree MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
          β (mixCube τ p n) 1 f
        - stateFree MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
          β (mixCube τ p m) 1 f| ≤ ε := by
  classical
  obtain ⟨x₀, R, hR, hin⟩ := exists_cube S
  have hr0 : 0 ≤ MassGap.StrongCoupling.coreRate (16 * 4) β :=
    MassGap.StrongCoupling.coreRate_nonneg _ hβ
  have hC2 : (0 : ℝ) ≤ 2 * ‖f‖ := by positivity
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ,
      Cst = MassGap.StrongCoupling.coreConstG (2 * ‖f‖) (16 * 4) β (16 * (R + 1) ^ 4) := ⟨_, rfl⟩
  have hC0 : 0 ≤ Cst := by
    rw [hCst]
    unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
    have : (0 : ℝ) < 1 - MassGap.StrongCoupling.coreRate (16 * 4) β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC2 (by positivity)) (by positivity)) this.le
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Cst * MassGap.StrongCoupling.coreRate (16 * 4) β ^ j ≤ ε := by
    rcases eq_or_lt_of_le hC0 with h | h
    · exact ⟨0, by rw [← h, zero_mul]; exact hε.le⟩
    · obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hε h) hr
      refine ⟨j, ?_⟩
      have := (lt_div_iff₀ h).mp hj
      linarith
  set U : ℕ := 16 * (R + 1) ^ 4 with hU
  set k : ℕ := j + U + R with hk
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (mixCube_exhausts τ p (linkCube x₀ k))
  refine ⟨N₀, fun n hn m hm => ?_⟩
  set Λn := mixCube τ p n with hΛn
  set Λm := mixCube τ p m with hΛm
  have hcn : linkCube x₀ k ⊆ Λn := hN₀ n hn
  have hcm : linkCube x₀ k ⊆ Λm := hN₀ m hm
  have hsubn : Λn ⊆ Λn ∪ Λm := Finset.subset_union_left
  have hsubm : Λm ⊆ Λn ∪ Λm := Finset.subset_union_right
  have hSk : S ⊆ linkCube x₀ k := fun l hl => mem_linkCube.mpr (fun i => by
    have := hin l hl i; constructor <;> omega)
  have hbox : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → MassGap.BoxCube.InCube x₀ R q.2 →
      q ∈ iplqAll (Λn ∪ Λm) := by
    intro q hnd hq
    refine mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr (fun l hl =>
      hsubn (hcn (mem_linkCube.mpr (fun i => ?_)))), hnd⟩
    have hc := ilink_site_coord i q l hl
    have := hq i
    constructor <;> omega
  have hx₀ : MassGap.BoxCube.InCube x₀ R x₀ := fun i => ⟨le_rfl, by omega⟩
  let a : ↥(iplqAll (Λn ∪ Λm)) := MassGap.BoxCube.mkPlaq hbox 0 1 (by decide) x₀ hx₀
  let b : ↥(iplqAll (Λn ∪ Λm)) := MassGap.BoxCube.mkPlaq hbox 1 0 (by decide) x₀ hx₀
  have ha : a ∈ MassGap.BoxCube.cubePlaq (Λn ∪ Λm) x₀ R := MassGap.BoxCube.mem_cubePlaq.mpr hx₀
  have hb : b ∈ MassGap.BoxCube.cubePlaq (Λn ∪ Λm) x₀ R := MassGap.BoxCube.mem_cubePlaq.mpr hx₀
  have hne : a ≠ b := by
    intro h
    have h1 := congrArg (fun q : ↥(iplqAll (Λn ∪ Λm)) => (q : MassGap.GibbsSpec.IPlaq).1.1) h
    simp [a, b, MassGap.BoxCube.mkPlaq] at h1
  have hball : ∀ q ∈ MassGap.StrongCoupling.ball (boxBd (Λn ∪ Λm)) a k,
      q ∈ subPlaq (Λn ∪ Λm) Λm ∩ subPlaq (Λn ∪ Λm) Λn := by
    intro q hq
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_iplqAll_of_mem_ball a q k hq hcm⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_iplqAll_of_mem_ball a q k hq hcn⟩⟩
  rw [stateFree_eq_meanR hN _ _ β hsubn 1 f (hSk.trans hcn) hf,
    stateFree_eq_meanR hN _ _ β hsubm 1 f (hSk.trans hcm) hf]
  have hO := MassGap.BoxCube.localOnLinks_splice (Λn ∪ Λm) 1 f (hSk.trans (hcn.trans hsubn)) hf
  have hAo := MassGap.BoxCube.linkHalo_subset_cubePlaq (Λn ∪ Λm) x₀ R
    (MassGap.BoxCube.boxLinks (Λn ∪ Λm) S)
    (fun l hl i => hin l (MassGap.BoxCube.mem_boxLinks.mp hl) i)
  have hconnA := MassGap.BoxCube.reach_cubePlaq hbox ha
  have hrle := MassGap.StrongCoupling.coreRate_mono hβ (touchDeg_boxBd_le (Λn ∪ Λm))
  have hrK : MassGap.StrongCoupling.coreRate (MassGap.StrongCoupling.touchDeg (boxBd (Λn ∪ Λm))) β < 1 :=
    lt_of_le_of_lt hrle hr
  have hcard := MassGap.BoxCube.card_cubePlaq_le (Λn ∪ Λm) x₀ R
  have hu : (MassGap.BoxCube.cubePlaq (Λn ∪ Λm) x₀ R).card ≤ k + 2 := by omega
  have key := MassGap.BoxCompare.meanR_sub_abs_le hN (boxBd (Λn ∪ Λm)) hβ
    (subPlaq (Λn ∪ Λm) Λn) (subPlaq (Λn ∪ Λm) Λm) hO (MassGap.BoxCube.abs_splice_le (Λn ∪ Λm) 1 f)
    hAo ha hb hne hconnA hrK k hu hball
  refine le_trans key ?_
  -- carry the bound to touch degree 64 and anchor size U
  have hCC : MassGap.StrongCoupling.coreConstG (2 * ‖f‖)
        (MassGap.StrongCoupling.touchDeg (boxBd (Λn ∪ Λm))) β
        (MassGap.BoxCube.cubePlaq (Λn ∪ Λm) x₀ R).card ≤ Cst := by
    rw [hCst]
    exact le_trans (MassGap.StrongCoupling.coreConstG_mono hC2 hβ (touchDeg_boxBd_le _) hr _)
      (MassGap.BoxCube.coreConstG_le_of_le hC2 hβ hr hcard)
  have hpow : MassGap.StrongCoupling.coreRate (MassGap.StrongCoupling.touchDeg (boxBd (Λn ∪ Λm))) β
        ^ (k + 2 - (MassGap.BoxCube.cubePlaq (Λn ∪ Λm) x₀ R).card)
      ≤ MassGap.StrongCoupling.coreRate (16 * 4) β ^ j := by
    refine le_trans (pow_le_pow_left₀ (MassGap.StrongCoupling.coreRate_nonneg _ hβ) hrle _) ?_
    exact MassGap.StrongCoupling.pow_le_pow_of_le_one_asm hr0 hr.le (by omega)
  have hK0 : 0 ≤ MassGap.StrongCoupling.coreConstG (2 * ‖f‖)
      (MassGap.StrongCoupling.touchDeg (boxBd (Λn ∪ Λm))) β
      (MassGap.BoxCube.cubePlaq (Λn ∪ Λm) x₀ R).card := by
    unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
    have : (0 : ℝ) < 1 - MassGap.StrongCoupling.coreRate
        (MassGap.StrongCoupling.touchDeg (boxBd (Λn ∪ Λm))) β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC2 (by positivity)) (by positivity)) this.le
  calc _ ≤ Cst * MassGap.StrongCoupling.coreRate (16 * 4) β ^ j :=
        mul_le_mul hCC hpow (pow_nonneg (MassGap.StrongCoupling.coreRate_nonneg _ hβ) _) hC0
    _ ≤ ε := hj

#print axioms stateFree_cauchy

/-! ## The limit -/

open scoped Classical in
/-- **L1: the free box states converge.** At `0 ≤ β` with `coreRate 64 β < 1` there is a state `ν`
with `stateFree (mixCube τ p n) 1 f → ν f` along `atTop` for every continuous `f`.

`ClayCapstone.exists_dlr_limit_of_free_family` gives `ν` as a limit along an ultrafilter finer than
`atTop`. For `f`, take a local `g` within `ε/4` (the local observables are dense by
Stone–Weierstrass, `DLRLimit.localObsAlg_separatesPoints`); past `stateFree_cauchy`'s `N₀` the
states of `g` are within `ε/4` of one another, and the ultrafilter meets that tail, so they are within
`ε/2` of `ν g`; states are `1`-Lipschitz in the sup norm (`DLRLimit.State.abs_le_norm`).

DERIVED: `16 * 4` is the box touch-degree bound; `0` is the sign hypothesis; `1` is the geometric
threshold and the identity boundary configuration; `4` and `2` are the splitting of `ε`. -/
theorem exists_tendsto_stateFree (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) (τ : Fin 4) (p : ℤ) :
    ∃ ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f)) := by
  classical
  obtain ⟨u, ν, hu, htu, -⟩ := MassGap.ClayCapstone.exists_dlr_limit_of_free_family τ p hN β 1
  refine ⟨ν, fun f => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a local observable near `f`
  have hsep := MassGap.DLRLimit.localObsAlg_separatesPoints (G := MassGap.SUN.SU N)
    (fun a b hab => MassGap.DLRLimit.continuousMap_separatesPoints_of_t2 _ a b hab)
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hcl : f ∈ closure ((MassGap.DLRLimit.localObsAlg (MassGap.SUN.SU N)) :
      Set C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, htop]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hcl (ε / 4) (by linarith)
  rw [dist_eq_norm] at hfg
  obtain ⟨S, hS⟩ := MassGap.DLRLimit.mem_localObsAlg.mp hg
  obtain ⟨N₀, hN₀⟩ := stateFree_cauchy hN hβ hr τ p g
    (MassGap.WilsonDLR.isLocalOn_of_isLocalOnC hS) (ε := ε / 4) (by linarith)
  set s : ℕ → MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) := fun n =>
    stateFree MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
      β (mixCube τ p n) 1 with hs
  have hνg : ∀ n ≥ N₀, |s n g - ν g| ≤ ε / 2 := by
    intro n hn
    have hev : ∀ᶠ m in (u : Filter ℕ), dist (s m g) (ν g) < ε / 4 ∧ N₀ ≤ m :=
      ((Metric.tendsto_nhds.mp (htu g)) (ε / 4) (by linarith)).and
        (hu (Filter.eventually_ge_atTop N₀))
    obtain ⟨m, hm1, hm2⟩ := hev.exists
    rw [Real.dist_eq] at hm1
    have h := hN₀ n hn m hm2
    calc |s n g - ν g| ≤ |s n g - s m g| + |s m g - ν g| := abs_sub_le _ _ _
      _ ≤ ε / 2 := by linarith
  refine ⟨N₀, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have h1 : |s n f - s n g| ≤ ‖f - g‖ := by
    rw [← MassGap.DLRLimit.State.map_sub]; exact MassGap.DLRLimit.State.abs_le_norm _ _
  have h2 : |ν g - ν f| ≤ ‖f - g‖ := by
    rw [← MassGap.DLRLimit.State.map_sub]
    exact le_trans (MassGap.DLRLimit.State.abs_le_norm _ _) (le_of_eq (norm_sub_rev _ _))
  have h3 := hνg n hn
  calc |s n f - ν f| ≤ |s n f - s n g| + |s n g - ν g| + |ν g - ν f| := by
        have := abs_sub_le (s n f) (s n g) (ν f)
        have := abs_sub_le (s n g) (ν g) (ν f)
        linarith
    _ < ε := by linarith

#print axioms exists_tendsto_stateFree

/-- **M on the lattice, unconditional at strong coupling.** At every `0 < β` with
`coreRate 64 β < 1` there is an infinite-volume state `ν`, the `atTop` limit of the free box states
along `mixCube` (`exists_tendsto_stateFree`), at which the transfer operator of the gauge-invariant
theory is self-adjoint with spectrum in `{1} ∪ [0, ρ]`, `ρ = coreRate 64 β`, and `1` at the top: a gap
`Δ = −log ρ > 0` (`StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling`).

DERIVED: `16 * 4` is the box touch-degree bound; `4` is the dimension; `0` is the coupling's lower
end and the spectrum's bottom; `1` is the vacuum eigenvalue, the geometric threshold and the identity
boundary configuration; `2` is the density's ceiling. -/
theorem wilson_gaugeInv_mass_gap_lattice (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) :
    ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
      (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f))),
      IsSelfAdjoint (MassGap.GNSHilbert.opT (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β)
      ∧ spectrum ℝ (MassGap.GNSHilbert.opT (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β))))
      ∧ IsGreatest (spectrum ℝ (MassGap.GNSHilbert.opT
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend))) 1 := by
  obtain ⟨ν, htend⟩ := exists_tendsto_stateFree hN hβ.le hr τ p
  exact ⟨ν, htend, MassGap.StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling τ p hN hβ hr ν htend⟩

#print axioms wilson_gaugeInv_mass_gap_lattice

/-- **The strong-coupling region is not empty.** There is a `b > 0` with `coreRate 64 β < 1` for every
`0 < β < b` (`StrongCoupling.core_rate_lt_one_of_small`), so `wilson_gaugeInv_mass_gap_lattice` holds
on the interval `(0, b)`.

DERIVED: `16 * 4` is the box touch-degree bound; `0` is the interval's lower end; `1` is the
geometric threshold. -/
theorem exists_strong_coupling_region :
    ∃ b > 0, ∀ β : ℝ, 0 < β → β < b → MassGap.StrongCoupling.coreRate (16 * 4) β < 1 := by
  obtain ⟨b, hb, h⟩ := MassGap.StrongCoupling.core_rate_lt_one_of_small (16 * 4)
  exact ⟨b, hb, fun β hβ hβb => h β hβ.le hβb⟩

#print axioms exists_strong_coupling_region

end MassGap.FreeLimit
