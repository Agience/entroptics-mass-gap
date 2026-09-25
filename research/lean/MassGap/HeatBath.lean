import Mathlib
import MassGap.KnabeCriterion
import MassGap.LocalGauge
import MassGap.PlaqVariance

noncomputable section

/-!
# MassGap.HeatBath — the heat-bath conditional expectations of the periodic Wilson measures

## What it gives

1. **One coordinate of a product measure.** `measurePreserving_update`: the map
   `(W, g) ↦ Function.update W i g` carries `(Π μ) ⊗ μ` to `Π μ` for a probability measure `μ`;
   `integral_eq_integral_update` is the resulting identity
   `∫ F d(Π μ) = ∫ W, ∫ g, F (update W i g) dμ d(Π μ)` for bounded measurable `F`.
2. **The heat bath of a finite `SU(N)` Wilson system.** For a boundary word `bd`, a coupling `β` and
   a link `l`, `heatAvg bd β l f W` is the average of `f` over the variable at `l` with the Wilson
   Boltzmann weight `wt bd β`, the other links held at `W`:
   `heatAvg bd β l f W = (∫ g, f (W[l ↦ g]) wt (W[l ↦ g]) dg) / ∫ g, wt (W[l ↦ g]) dg`, with `dg`
   the probability Haar measure. It does not read `l` (`heatAvg_update`), fixes every function not
   reading `l` (`heatAvg_of_readsNot`), pulls out factors not reading `l` (`heatAvg_mul_left`,
   `heatAvg_mul_right`), is linear on continuous functions (`heatAvg_add`, `heatAvg_const_mul`) and
   carries continuous functions to continuous functions (`continuous_heatAvg`).
3. **The DLR identity and detailed balance.** `expect_heatAvg`: the Gibbs expectation of
   `heatAvg bd β l f` is that of `f`, for continuous `f`. `expect_heatAvg_mul`: the Gibbs expectation
   of `heatAvg f · g` equals that of `f · heatAvg g`, through that of `heatAvg f · heatAvg g`.
4. **Commutation.** `SharePlaq bd l l'`: some plaquette's boundary word visits both links.
   `heatAvg_eq_loc`: the heat bath at `l` reads only the weight of the plaquettes through `l`.
   `heatAvg_comm`: for `l ≠ l'` sharing no plaquette, the heat baths at `l` and `l'` commute on
   continuous functions (Fubini on `SU(N) × SU(N)`).
5. **The periodic lattice.** `liftSite`, `liftLink`: a torus site or link read as the `ℤ⁴` one with
   coordinates in `[0, M]`; `restrictConf M U` reads a `ℤ⁴` configuration on those links, and
   `restrictConf_pullback` makes it a left inverse of `InfiniteLattice.pullback M`.
   `heatLift β M l F` is the heat bath at the torus link `l` of the torus reading of `F`, composed
   with `restrictConf M`: `torusObs M (heatLift β M l F) = heatAvg (bdT M) β l (torusObs M F)`
   (`torusObs_heatLift`). It keeps periodic gauge invariance (`heatLift_mem`), through
   `pullback_gaugeTransform`, `restrictConf_igauge` and the two-sided invariance of Haar measure
   (`heatAvg_gauge`).
6. **The conditional expectations.** `torusCondExp β M l` is `heatLift β M l` as a linear map of
   `periodicGaugeInvSubmodule M`. At `M = 2j + 1` it is `torusForm`-self-adjoint
   (`torusCondExp_selfAdj`), idempotent (`torusCondExp_idem`), its values do not read `l`
   (`torusCondExp_readsNot`), it keeps the torus reading of every observable not reading `l`
   (`torusCondExp_keeps`), and two of them at links sharing no plaquette commute
   (`torusCondExp_comm`). These are the analytic fields of `KnabeCriterion.WilsonHeatBath`;
   `MassGap.BoxPatch` supplies the patch data and builds the structure.

## Scope

Everything is exact at every finite extent, every real `β` and every `N`: no bound, limit or
uniqueness enters. The heat bath is defined with the full Boltzmann weight; `heatAvg_eq_loc`
identifies it with the weight of the plaquettes through the link.
-/

namespace MassGap.HeatBath

open MeasureTheory
open MassGap.LatticeGauge
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.KnabeCriterion
open MassGap.PeriodicState (torusObs torusState)
open MassGap.InfiniteLattice (siteMod linkMod pullback finMod)

/-! ## 1. One coordinate of a product measure -/

section Measure

/-- A continuous real function on a compact space is bounded in absolute value.

DERIVED: no numeral. -/
theorem exists_abs_le {X : Type*} [TopologicalSpace X] [CompactSpace X] {F : X → ℝ}
    (hF : Continuous F) : ∃ C : ℝ, ∀ x, |F x| ≤ C := by
  obtain ⟨b, hb⟩ := (isCompact_range hF).bddAbove
  obtain ⟨a, ha⟩ := (isCompact_range hF).bddBelow
  refine ⟨|a| + |b|, fun x => ?_⟩
  have h1 : F x ≤ b := hb (Set.mem_range_self x)
  have h2 : a ≤ F x := ha (Set.mem_range_self x)
  have h3 : -|a| ≤ a := neg_abs_le a
  have h4 : b ≤ |b| := le_abs_self b
  have h5 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h6 : (0 : ℝ) ≤ |b| := abs_nonneg b
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms exists_abs_le

/-- A measurable real function bounded in absolute value is integrable against a finite measure.

DERIVED: no numeral. -/
theorem integrable_of_abs_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {F : X → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) : Integrable F ν :=
  (integrable_const C).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC x))

#print axioms integrable_of_abs_le

/-- **Updating one coordinate preserves the product measure.** For a probability measure `μ`, the
map `(W, g) ↦ Function.update W i g` carries `(Π μ) ⊗ μ` to `Π μ`: on a box `Π s_j` its preimage is
the box with `univ` at `i`, times `s i`, of measure `(Π_{j ≠ i} μ(s_j)) · μ(s_i)`
(`Measure.pi_eq`).

DERIVED: no numeral. -/
theorem measurePreserving_update {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i : ι) :
    MeasurePreserving (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
      ((Measure.pi fun _ : ι => μ).prod μ) (Measure.pi fun _ : ι => μ) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · rw [hj, Function.update_self]
          exact Set.mem_univ _
        · rw [Function.update_of_ne hj]
          have h' := h j
          rwa [Function.update_of_ne hj] at h'
      · have h' := h i
        rwa [Function.update_self] at h'
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        exact h2
      · rw [Function.update_of_ne hj]
        have h' := h1 j
        rwa [Function.update_of_ne hj] at h'
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, measure_univ, mul_one,
    ← Finset.prod_erase_mul _ (fun j => μ (s j)) (Finset.mem_univ i)]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

#print axioms measurePreserving_update

/-- **Integrating out one coordinate.** For a probability measure `μ` and a bounded measurable `F`
on `ι → Ω`: `∫ F d(Π μ) = ∫ W, ∫ g, F (update W i g) dμ d(Π μ)` (`measurePreserving_update`,
`integral_map`, Fubini).

DERIVED: no numeral. -/
theorem integral_eq_integral_update {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i : ι) (F : (ι → Ω) → ℝ) (hF : Measurable F)
    {C : ℝ} (hC : ∀ W, |F W| ≤ C) :
    ∫ W, F W ∂(Measure.pi fun _ : ι => μ)
      = ∫ W, ∫ g, F (Function.update W i g) ∂μ ∂(Measure.pi fun _ : ι => μ) := by
  have hmp := measurePreserving_update μ i
  have hint : Integrable (fun p : (ι → Ω) × Ω => F (Function.update p.1 i p.2))
      ((Measure.pi fun _ : ι => μ).prod μ) :=
    integrable_of_abs_le _ (hF.comp measurable_update') (fun p => hC _)
  calc ∫ W, F W ∂(Measure.pi fun _ : ι => μ)
      = ∫ W, F W ∂(Measure.map (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
          ((Measure.pi fun _ : ι => μ).prod μ)) := by rw [hmp.map_eq]
    _ = ∫ p, F (Function.update p.1 i p.2) ∂((Measure.pi fun _ : ι => μ).prod μ) :=
        integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable
    _ = ∫ W, ∫ g, F (Function.update W i g) ∂μ ∂(Measure.pi fun _ : ι => μ) :=
        integral_prod _ hint

#print axioms integral_eq_integral_update

/-- **Haar measure on `SU(N)` is invariant under two-sided translation**:
`∫ F(a h b) dh = ∫ F(h) dh` (`integral_mul_left_eq_self`, `integral_mul_right_eq_self`, with
`CompactGauge.isMulRightInvariant_probHaar`).

DERIVED: no numeral. -/
theorem integral_twoSided {N : ℕ} (F : SU N → ℝ) (a b : SU N) :
    ∫ h, F (a * h * b) ∂(probHaar (SU N)) = ∫ h, F h ∂(probHaar (SU N)) :=
  calc ∫ h, F (a * h * b) ∂(probHaar (SU N)) = ∫ h, F (h * b) ∂(probHaar (SU N)) :=
        integral_mul_left_eq_self (fun y => F (y * b)) a
    _ = ∫ h, F h ∂(probHaar (SU N)) := integral_mul_right_eq_self F b

#print axioms integral_twoSided

end Measure

/-! ## 2. The heat bath of a finite Wilson system -/

section HeatBathAvg

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- The Wilson system's link type is `Lk`; its decidable equality is `Lk`'s. -/
local instance decEqSystemLink (bd : Pq → List (Lk × Bool)) :
    DecidableEq (wilsonSystem bd (wilsonDensity (N := N))).Link :=
  inferInstanceAs (DecidableEq Lk)

/-- The Wilson Boltzmann weight `e^{−β S(W)}` of the system `wilsonSystem bd wilsonDensity`.

DERIVED: no numeral. -/
def wt (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Lk → SU N) : ℝ :=
  (wilsonSystem bd (wilsonDensity (N := N))).boltz β W

/-- The weight is positive (`WilsonReal.wilsonSystem_boltz_pos`).

DERIVED: `0` is the sign asserted. -/
theorem wt_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Lk → SU N) : 0 < wt bd β W :=
  MassGap.WilsonReal.wilsonSystem_boltz_pos bd β W

#print axioms wt_pos

/-- The weight is continuous (`PlaqVariance.continuous_wilsonSystem_boltz`).

DERIVED: no numeral. -/
theorem continuous_wt (bd : Pq → List (Lk × Bool)) (β : ℝ) : Continuous (wt (N := N) bd β) :=
  MassGap.PlaqVariance.continuous_wilsonSystem_boltz bd β

#print axioms continuous_wt

/-- The heat-bath numerator at the link `l`: `∫ g, f (W[l ↦ g]) wt (W[l ↦ g]) dg`.

DERIVED: no numeral. -/
def heatNum (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : ℝ :=
  ∫ g, f (Function.update W l g) * wt bd β (Function.update W l g) ∂(probHaar (SU N))

/-- The heat-bath normalisation at the link `l`: `∫ g, wt (W[l ↦ g]) dg`.

DERIVED: no numeral. -/
def heatPart (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (W : Lk → SU N) : ℝ :=
  ∫ g, wt bd β (Function.update W l g) ∂(probHaar (SU N))

/-- **The heat bath at the link `l`**: the average of `f` over the variable at `l` with the Wilson
weight, the other links held at `W`: `heatNum / heatPart`.

DERIVED: no numeral. -/
def heatAvg (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : ℝ :=
  heatNum bd β l f W / heatPart bd β l W

/-- The normalisation is positive: the weight is positive and continuous on the compact group.

DERIVED: `0` is the sign asserted. -/
theorem heatPart_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (W : Lk → SU N) :
    0 < heatPart bd β l W := by
  have hc : Continuous (fun g : SU N => wt bd β (Function.update W l g)) :=
    (continuous_wt bd β).comp (continuous_const.update l continuous_id)
  obtain ⟨C, hC⟩ := exists_abs_le hc
  have hint : Integrable (fun g : SU N => wt bd β (Function.update W l g)) (probHaar (SU N)) :=
    integrable_of_abs_le _ hc.measurable hC
  unfold heatPart
  rw [integral_pos_iff_support_of_nonneg (fun g => (wt_pos bd β _).le) hint]
  have hsupp : Function.support (fun g : SU N => wt bd β (Function.update W l g)) = Set.univ :=
    Set.eq_univ_of_forall (fun g => Function.mem_support.mpr (wt_pos bd β _).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms heatPart_pos

/-- The integrand of the numerator is integrable for continuous `f`.

DERIVED: no numeral. -/
theorem integrable_upd (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) {f : (Lk → SU N) → ℝ}
    (hf : Continuous f) (W : Lk → SU N) :
    Integrable (fun g => f (Function.update W l g) * wt bd β (Function.update W l g))
      (probHaar (SU N)) := by
  have hF : Continuous (fun V => f V * wt bd β V) := hf.mul (continuous_wt bd β)
  obtain ⟨C, hC⟩ := exists_abs_le hF
  exact integrable_of_abs_le _ (hF.comp (continuous_const.update l continuous_id)).measurable
    (fun g => hC _)

#print axioms integrable_upd

/-- The heat bath does not read the variable at `l` (`Function.update_idem`).

DERIVED: no numeral. -/
theorem heatAvg_update (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) (h : SU N) :
    heatAvg bd β l f (Function.update W l h) = heatAvg bd β l f W := by
  simp only [heatAvg, heatNum, heatPart, Function.update_idem]

#print axioms heatAvg_update

/-- **The heat bath fixes every function not reading `l`.**

DERIVED: no numeral. -/
theorem heatAvg_of_readsNot (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {f : (Lk → SU N) → ℝ} (hf : ∀ W g, f (Function.update W l g) = f W) (W : Lk → SU N) :
    heatAvg bd β l f W = f W := by
  unfold heatAvg heatNum
  simp only [hf, integral_const_mul]
  exact mul_div_cancel_right₀ _ (heatPart_pos bd β l W).ne'

#print axioms heatAvg_of_readsNot

/-- **A factor not reading `l` comes out on the left.**

DERIVED: no numeral. -/
theorem heatAvg_mul_left (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {a f : (Lk → SU N) → ℝ} (ha : ∀ W g, a (Function.update W l g) = a W) (W : Lk → SU N) :
    heatAvg bd β l (fun V => a V * f V) W = a W * heatAvg bd β l f W := by
  unfold heatAvg heatNum
  simp only [ha, mul_assoc, integral_const_mul]
  exact mul_div_assoc _ _ _

#print axioms heatAvg_mul_left

/-- **A factor not reading `l` comes out on the right.**

DERIVED: no numeral. -/
theorem heatAvg_mul_right (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {a f : (Lk → SU N) → ℝ} (ha : ∀ W g, a (Function.update W l g) = a W) (W : Lk → SU N) :
    heatAvg bd β l (fun V => f V * a V) W = heatAvg bd β l f W * a W := by
  have hfun : (fun V => f V * a V) = (fun V => a V * f V) := funext fun V => mul_comm _ _
  rw [hfun, heatAvg_mul_left bd β l ha W, mul_comm]

#print axioms heatAvg_mul_right

/-- The heat bath is homogeneous (`heatAvg_mul_left` at a constant).

DERIVED: no numeral. -/
theorem heatAvg_const_mul (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (c : ℝ)
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    heatAvg bd β l (fun V => c * f V) W = c * heatAvg bd β l f W :=
  heatAvg_mul_left bd β l (a := fun _ => c) (fun _ _ => rfl) W

#print axioms heatAvg_const_mul

/-- The heat bath is additive on continuous functions (`integral_add`).

DERIVED: no numeral. -/
theorem heatAvg_add (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) {f g : (Lk → SU N) → ℝ}
    (hf : Continuous f) (hg : Continuous g) (W : Lk → SU N) :
    heatAvg bd β l (fun V => f V + g V) W = heatAvg bd β l f W + heatAvg bd β l g W := by
  unfold heatAvg heatNum
  rw [← add_div]
  congr 1
  simp only [add_mul]
  exact integral_add (integrable_upd bd β l hf W) (integrable_upd bd β l hg W)

#print axioms heatAvg_add

/-- The numerator is continuous in the frozen links, for continuous `f`
(`continuous_of_dominated`, the bound a constant by compactness).

DERIVED: no numeral. -/
theorem continuous_heatNum (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (heatNum bd β l f) := by
  have hF : Continuous (fun V => f V * wt bd β V) := hf.mul (continuous_wt bd β)
  obtain ⟨C, hC⟩ := exists_abs_le hF
  show Continuous (fun W => ∫ g, f (Function.update W l g) * wt bd β (Function.update W l g)
    ∂(probHaar (SU N)))
  refine continuous_of_dominated (bound := fun _ => C) (fun W => ?_) (fun W => ?_)
    (integrable_const C) ?_
  · exact (hF.comp (continuous_const.update l continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun g => by rw [Real.norm_eq_abs]; exact hC _)
  · exact Filter.Eventually.of_forall (fun g => hF.comp (continuous_id.update l continuous_const))

#print axioms continuous_heatNum

/-- The normalisation is the numerator of the constant `1`.

DERIVED: `1` is the constant function. -/
theorem heatPart_eq (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) :
    heatPart (N := N) bd β l = heatNum bd β l (fun _ => 1) := by
  funext W
  unfold heatPart heatNum
  simp only [one_mul]

#print axioms heatPart_eq

/-- The heat bath of a continuous function is continuous.

DERIVED: no numeral. -/
theorem continuous_heatAvg (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (heatAvg bd β l f) := by
  have hP : Continuous (heatPart (N := N) bd β l) := by
    rw [heatPart_eq]
    exact continuous_heatNum bd β l continuous_const
  exact (continuous_heatNum bd β l hf).div hP (fun W => (heatPart_pos bd β l W).ne')

#print axioms continuous_heatAvg

/-- **The DLR identity at one link, integrated.** For continuous `f`:
`∫ heatAvg f · wt = ∫ f · wt` against the product Haar measure (`integral_eq_integral_update`,
`heatAvg_update`).

DERIVED: no numeral. -/
theorem integral_heatAvg_mul_wt (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) :
    ∫ W, heatAvg bd β l f W * wt bd β W ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, f W * wt bd β W ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
  have hc1 : Continuous (fun W => heatAvg bd β l f W * wt bd β W) :=
    (continuous_heatAvg bd β l hf).mul (continuous_wt bd β)
  have hc2 : Continuous (fun W => f W * wt bd β W) := hf.mul (continuous_wt bd β)
  obtain ⟨C1, hC1⟩ := exists_abs_le hc1
  obtain ⟨C2, hC2⟩ := exists_abs_le hc2
  rw [integral_eq_integral_update (probHaar (SU N)) l _ hc1.measurable hC1,
    integral_eq_integral_update (probHaar (SU N)) l _ hc2.measurable hC2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show ∫ g, heatAvg bd β l f (Function.update W l g) * wt bd β (Function.update W l g)
      ∂(probHaar (SU N))
    = ∫ g, f (Function.update W l g) * wt bd β (Function.update W l g) ∂(probHaar (SU N))
  simp only [heatAvg_update, integral_const_mul]
  show heatAvg bd β l f W * heatPart bd β l W = heatNum bd β l f W
  unfold heatAvg
  exact div_mul_cancel₀ _ (heatPart_pos bd β l W).ne'

#print axioms integral_heatAvg_mul_wt

/-- **The DLR identity at one link.** The Gibbs expectation of `heatAvg bd β l f` is that of `f`,
for continuous `f`.

DERIVED: no numeral. -/
theorem expect_heatAvg (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) {f : (Lk → SU N) → ℝ}
    (hf : Continuous f) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β (heatAvg bd β l f)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β f := by
  unfold System.expect System.corrNum
  exact congrArg
    (fun t => t / (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (SU N)) β)
    (integral_heatAvg_mul_wt bd β l hf)

#print axioms expect_heatAvg

/-- **Detailed balance.** For continuous `f`, `g`, the Gibbs expectations of `heatAvg f · g` and of
`f · heatAvg g` agree. The proof passes through the expectation of `heatAvg f · heatAvg g`
(`expect_heatAvg`, `heatAvg_mul_left`, `heatAvg_mul_right`).

DERIVED: no numeral. -/
theorem expect_heatAvg_mul (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk)
    {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => heatAvg bd β l f W * g W)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => f W * heatAvg bd β l g W) :=
  calc (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => heatAvg bd β l f W * g W)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (heatAvg bd β l (fun W => heatAvg bd β l f W * g W)) :=
        (expect_heatAvg bd β l ((continuous_heatAvg bd β l hf).mul hg)).symm
    _ = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (fun W => heatAvg bd β l f W * heatAvg bd β l g W) := by
        congr 1
        funext W
        exact heatAvg_mul_left bd β l (fun V h => heatAvg_update bd β l f V h) W
    _ = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (heatAvg bd β l (fun W => f W * heatAvg bd β l g W)) := by
        congr 1
        funext W
        exact (heatAvg_mul_right bd β l (fun V h => heatAvg_update bd β l g V h) W).symm
    _ = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (fun W => f W * heatAvg bd β l g W) :=
        expect_heatAvg bd β l (hf.mul (continuous_heatAvg bd β l hg))

#print axioms expect_heatAvg_mul

end HeatBathAvg

/-! ## 3. Locality and commutation -/

section Commute

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- **Two links share a plaquette**: some plaquette's boundary word visits both. At `bdT` the plaquettes
run over every ordered pair of directions, the diagonal `μ = ν` included, so two consecutive links in
one direction share the diagonal plaquette, whose holonomy is the identity: `SharePlaq` also holds at
pairs whose conditional laws do not couple, and sharing none is a sufficient condition for the heat
baths to commute (`heatAvg_comm`).

DERIVED: no numeral. -/
def SharePlaq (bd : Pq → List (Lk × Bool)) (l l' : Lk) : Prop :=
  ∃ p, l ∈ (bd p).map Prod.fst ∧ l' ∈ (bd p).map Prod.fst

/-- Sharing a plaquette is symmetric.

DERIVED: no numeral. -/
theorem not_sharePlaq_symm {bd : Pq → List (Lk × Bool)} {l l' : Lk} (h : ¬ SharePlaq bd l l') :
    ¬ SharePlaq bd l' l :=
  fun ⟨p, h1, h2⟩ => h ⟨p, h2, h1⟩

#print axioms not_sharePlaq_symm

/-- A holonomy whose boundary word does not visit `l` does not read the variable at `l`.

DERIVED: no numeral. -/
theorem wilsonHol_update_of_not_mem (bd : Pq → List (Lk × Bool)) (p : Pq) {l : Lk}
    (hl : l ∉ (bd p).map Prod.fst) (W : Lk → SU N) (g : SU N) :
    wilsonHol bd p (Function.update W l g) = wilsonHol bd p W := by
  unfold wilsonHol
  congr 1
  apply List.map_congr_left
  intro lo hlo
  have hne : lo.1 ≠ l := fun h => hl (List.mem_map.mpr ⟨lo, hlo, h⟩)
  simp only [Function.update_of_ne hne]

#print axioms wilsonHol_update_of_not_mem

/-- The action of the plaquettes whose boundary word visits `l`.

DERIVED: no numeral. -/
def locSum (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => l ∈ (bd p).map Prod.fst), wilsonDensity (wilsonHol bd p W)

/-- The action of the plaquettes whose boundary word does not visit `l`.

DERIVED: no numeral. -/
def restSum (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => l ∉ (bd p).map Prod.fst), wilsonDensity (wilsonHol bd p W)

/-- The local weight `e^{−β · locSum}` at `l`.

DERIVED: no numeral. -/
def locW (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (W : Lk → SU N) : ℝ :=
  Real.exp (-β * locSum bd l W)

/-- The action splits at `l` (`Finset.sum_filter_add_sum_filter_not`).

DERIVED: no numeral. -/
theorem action_split (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) :
    (wilsonSystem bd (wilsonDensity (N := N))).action W = locSum bd l W + restSum bd l W := by
  show ∑ p, wilsonDensity (wilsonHol bd p W) = _
  unfold locSum restSum
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm

#print axioms action_split

/-- The weight factors at `l`: `wt = locW · e^{−β · restSum}`.

DERIVED: no numeral. -/
theorem wt_split (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (W : Lk → SU N) :
    wt bd β W = locW bd β l W * Real.exp (-β * restSum bd l W) := by
  unfold wt locW
  show Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action W) = _
  rw [action_split bd l W, mul_add, Real.exp_add]

#print axioms wt_split

/-- The rest of the action does not read `l`.

DERIVED: no numeral. -/
theorem restSum_update (bd : Pq → List (Lk × Bool)) (l : Lk) (W : Lk → SU N) (g : SU N) :
    restSum bd l (Function.update W l g) = restSum bd l W := by
  unfold restSum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [wilsonHol_update_of_not_mem bd p (Finset.mem_filter.mp hp).2]

#print axioms restSum_update

/-- The local action at `l` does not read a link `l'` sharing no plaquette with `l`.

DERIVED: no numeral. -/
theorem locSum_update_other (bd : Pq → List (Lk × Bool)) {l l' : Lk} (hs : ¬ SharePlaq bd l l')
    (W : Lk → SU N) (h : SU N) :
    locSum bd l (Function.update W l' h) = locSum bd l W := by
  unfold locSum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hl : l ∈ (bd p).map Prod.fst := (Finset.mem_filter.mp hp).2
  have hl' : l' ∉ (bd p).map Prod.fst := fun h' => hs ⟨p, hl, h'⟩
  rw [wilsonHol_update_of_not_mem bd p hl']

#print axioms locSum_update_other

/-- The local weight at `l` does not read a link sharing no plaquette with `l`.

DERIVED: no numeral. -/
theorem locW_update_other (bd : Pq → List (Lk × Bool)) (β : ℝ) {l l' : Lk}
    (hs : ¬ SharePlaq bd l l') (W : Lk → SU N) (h : SU N) :
    locW bd β l (Function.update W l' h) = locW bd β l W := by
  unfold locW
  rw [locSum_update_other bd hs W h]

#print axioms locW_update_other

/-- The local weight is continuous.

DERIVED: no numeral. -/
theorem continuous_locW (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) :
    Continuous (locW (N := N) bd β l) := by
  have hS : Continuous (fun W : Lk → SU N =>
      ∑ p ∈ Finset.univ.filter (fun p => l ∈ (bd p).map Prod.fst),
        wilsonDensity (wilsonHol bd p W)) :=
    continuous_finsetSum _ (fun p _ => MassGap.WilsonAction.continuous_wilsonDensity.comp
      (MassGap.PlaqVariance.continuous_wilsonHol bd p))
  exact Real.continuous_exp.comp (continuous_const.mul hS)

#print axioms continuous_locW

/-- **The heat bath reads only the plaquettes through `l`**: the factor `e^{−β · restSum}` does not
read `l` and cancels between numerator and normalisation.

DERIVED: no numeral. -/
theorem heatAvg_eq_loc (bd : Pq → List (Lk × Bool)) (β : ℝ) (l : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) :
    heatAvg bd β l f W
      = (∫ g, f (Function.update W l g) * locW bd β l (Function.update W l g) ∂(probHaar (SU N)))
        / ∫ g, locW bd β l (Function.update W l g) ∂(probHaar (SU N)) := by
  have hw : ∀ g, wt bd β (Function.update W l g)
      = locW bd β l (Function.update W l g) * Real.exp (-β * restSum bd l W) := by
    intro g
    rw [wt_split bd β l, restSum_update]
  unfold heatAvg heatNum heatPart
  simp only [hw, ← mul_assoc, integral_mul_const]
  exact mul_div_mul_right _ _ (Real.exp_pos _).ne'

#print axioms heatAvg_eq_loc

/-- **The two heat baths as one double integral.** For `l ≠ l'` sharing no plaquette,
`heatAvg l (heatAvg l' f) W` is the double integral of `f (W[l ↦ g][l' ↦ h])` against the two local
weights, over the product of the two local normalisations.

DERIVED: no numeral. -/
theorem heatAvg_heatAvg_eq (bd : Pq → List (Lk × Bool)) (β : ℝ) {l l' : Lk} (hll : l ≠ l')
    (hs : ¬ SharePlaq bd l l') (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    heatAvg bd β l (heatAvg bd β l' f) W
      = (∫ g, ∫ h, f (Function.update (Function.update W l g) l' h)
            * (locW bd β l' (Function.update W l' h) * locW bd β l (Function.update W l g))
            ∂(probHaar (SU N)) ∂(probHaar (SU N)))
        / ((∫ h, locW bd β l' (Function.update W l' h) ∂(probHaar (SU N)))
            * ∫ g, locW bd β l (Function.update W l g) ∂(probHaar (SU N))) := by
  have hE' : ∀ (V : Lk → SU N) (g : SU N),
      locW bd β l' (Function.update V l g) = locW bd β l' V :=
    fun V g => locW_update_other bd β (not_sharePlaq_symm hs) V g
  have hinner : ∀ g, heatAvg bd β l' f (Function.update W l g)
      = (∫ h, f (Function.update (Function.update W l g) l' h)
            * locW bd β l' (Function.update W l' h) ∂(probHaar (SU N)))
        / ∫ h, locW bd β l' (Function.update W l' h) ∂(probHaar (SU N)) := by
    intro g
    rw [heatAvg_eq_loc bd β l' f (Function.update W l g)]
    have hc : ∀ h, locW bd β l' (Function.update (Function.update W l g) l' h)
        = locW bd β l' (Function.update W l' h) := by
      intro h
      rw [Function.update_comm hll g h W, hE']
    simp only [hc]
  have hnum : ∀ g, heatAvg bd β l' f (Function.update W l g) * locW bd β l (Function.update W l g)
      = (∫ h, f (Function.update (Function.update W l g) l' h)
            * (locW bd β l' (Function.update W l' h) * locW bd β l (Function.update W l g))
            ∂(probHaar (SU N)))
        / ∫ h, locW bd β l' (Function.update W l' h) ∂(probHaar (SU N)) := by
    intro g
    rw [hinner g, div_mul_eq_mul_div, ← integral_mul_const]
    simp only [mul_assoc]
  rw [heatAvg_eq_loc bd β l (heatAvg bd β l' f) W]
  simp only [hnum]
  rw [integral_div, div_div]

#print axioms heatAvg_heatAvg_eq

/-- **Heat baths at links sharing no plaquette commute** on continuous functions: the double
integral of `heatAvg_heatAvg_eq` is symmetric by `Function.update_comm` and
`integral_integral_swap`.

DERIVED: no numeral. -/
theorem heatAvg_comm (bd : Pq → List (Lk × Bool)) (β : ℝ) {l l' : Lk} (hll : l ≠ l')
    (hs : ¬ SharePlaq bd l l') {f : (Lk → SU N) → ℝ} (hf : Continuous f) (W : Lk → SU N) :
    heatAvg bd β l (heatAvg bd β l' f) W = heatAvg bd β l' (heatAvg bd β l f) W := by
  rw [heatAvg_heatAvg_eq bd β hll hs f W,
    heatAvg_heatAvg_eq bd β (Ne.symm hll) (not_sharePlaq_symm hs) f W,
    mul_comm (∫ h, locW bd β l (Function.update W l h) ∂(probHaar (SU N)))]
  congr 1
  have hu2 : Continuous (fun p : SU N × SU N =>
      Function.update (Function.update W l p.1) l' p.2) :=
    ((continuous_const : Continuous fun _ : SU N × SU N => W).update l continuous_fst).update l'
      continuous_snd
  have hu1 : Continuous (fun p : SU N × SU N => Function.update W l p.1) :=
    continuous_const.update l continuous_fst
  have hu1' : Continuous (fun p : SU N × SU N => Function.update W l' p.2) :=
    continuous_const.update l' continuous_snd
  have hcont : Continuous (fun p : SU N × SU N =>
      f (Function.update (Function.update W l p.1) l' p.2)
        * (locW bd β l' (Function.update W l' p.2) * locW bd β l (Function.update W l p.1))) :=
    (hf.comp hu2).mul (((continuous_locW bd β l').comp hu1').mul
      ((continuous_locW bd β l).comp hu1))
  obtain ⟨C, hC⟩ := exists_abs_le hcont
  have hint : Integrable (Function.uncurry fun g h =>
      f (Function.update (Function.update W l g) l' h)
        * (locW bd β l' (Function.update W l' h) * locW bd β l (Function.update W l g)))
      ((probHaar (SU N)).prod (probHaar (SU N))) :=
    integrable_of_abs_le _ hcont.measurable hC
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  show f (Function.update (Function.update W l g) l' h)
      * (locW bd β l' (Function.update W l' h) * locW bd β l (Function.update W l g))
    = f (Function.update (Function.update W l' h) l g)
      * (locW bd β l (Function.update W l g) * locW bd β l' (Function.update W l' h))
  rw [Function.update_comm hll g h W, mul_comm (locW bd β l' (Function.update W l' h))]

#print axioms heatAvg_comm

end Commute

/-! ## 4. The periodic lattice -/

section Torus

variable {N : ℕ}

/-- The Wilson boundary word of the periodic four-dimensional lattice of extent `M + 1`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
abbrev bdT (M : ℕ) := WilsonHypercubic.bd (d := 4) (n := M + 1)

/-- `finMod M` inverts the embedding of `Fin (M + 1)` into `ℤ`.

DERIVED: `1` is the successor writing the extent; `0` is the lower end of the residue range. -/
theorem finMod_natCast (M : ℕ) (a : Fin (M + 1)) : finMod M ((a : ℕ) : ℤ) = a := by
  apply Fin.ext
  show ((((a : ℕ) : ℤ) % ((M : ℤ) + 1)).toNat) = (a : ℕ)
  have h0 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by omega
  have h1 : ((a : ℕ) : ℤ) < (M : ℤ) + 1 := by have := a.isLt; omega
  rw [Int.emod_eq_of_lt h0 h1, Int.toNat_natCast]

#print axioms finMod_natCast

/-- A torus site read as the `ℤ⁴` site with coordinates in `[0, M]`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def liftSite (M : ℕ) (x : WilsonHypercubic.Site 4 (M + 1)) : InfiniteLattice.ISite :=
  fun i => ((x i : ℕ) : ℤ)

/-- A torus link read as the `ℤ⁴` link at the lifted base site.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def liftLink (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) : InfiniteLattice.ILink :=
  (l.1, liftSite M l.2)

/-- `siteMod M ∘ liftSite M` is the identity.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem siteMod_liftSite (M : ℕ) (x : WilsonHypercubic.Site 4 (M + 1)) :
    siteMod M (liftSite M x) = x :=
  funext fun i => finMod_natCast M (x i)

#print axioms siteMod_liftSite

/-- `linkMod M ∘ liftLink M` is the identity.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem linkMod_liftLink (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    linkMod M (liftLink M l) = l :=
  Prod.ext rfl (siteMod_liftSite M l.2)

#print axioms linkMod_liftLink

/-- **The restriction to one period**: a `ℤ⁴` configuration read on the lifted torus links.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def restrictConf (M : ℕ) (U : GibbsSpec.IConf (SU N)) : WilsonHypercubic.Link 4 (M + 1) → SU N :=
  fun l => U (liftLink M l)

/-- `restrictConf M` is continuous.

DERIVED: no numeral. -/
theorem continuous_restrictConf (M : ℕ) : Continuous (restrictConf (N := N) M) :=
  continuous_pi fun l => continuous_apply (liftLink M l)

#print axioms continuous_restrictConf

/-- `restrictConf M` is a left inverse of `pullback M` (`linkMod_liftLink`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem restrictConf_pullback (M : ℕ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    restrictConf M (pullback M W) = W := by
  funext l
  show W (linkMod M (liftLink M l)) = W l
  rw [linkMod_liftLink]

#print axioms restrictConf_pullback

/-- The torus reading of a continuous observable is continuous.

DERIVED: no numeral. -/
theorem continuous_torusObs (M : ℕ) (F : C(GibbsSpec.IConf (SU N), ℝ)) :
    Continuous (torusObs M F) :=
  F.continuous.comp (InfiniteLattice.continuous_pullback (m := M))

#print axioms continuous_torusObs

/-- **The pullback intertwines the gauge actions**: a torus gauge transformation pulled back is the
`ℤ⁴` gauge transformation by the periodic gauge function (`InfiniteLattice.siteMod_ishift`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem pullback_gaugeTransform (M : ℕ) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    pullback M (LocalGauge.gaugeTransform g W)
      = GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) (pullback M W) := by
  funext l
  show g (siteMod M l.2) * W (linkMod M l) * (g (WilsonHypercubic.shift l.1 (siteMod M l.2)))⁻¹
    = g (siteMod M l.2) * W (linkMod M l)
      * (g (siteMod M (InfiniteLattice.ishift l.1 l.2)))⁻¹
  rw [InfiniteLattice.siteMod_ishift]

#print axioms pullback_gaugeTransform

/-- **The restriction intertwines the gauge actions**: restricting a `ℤ⁴` configuration transformed
by a periodic gauge function is transforming its restriction on the torus.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem restrictConf_igauge (M : ℕ) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (U : GibbsSpec.IConf (SU N)) :
    restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = LocalGauge.gaugeTransform g (restrictConf M U) := by
  funext l
  show g (siteMod M (liftSite M l.2)) * U (liftLink M l)
      * (g (siteMod M (InfiniteLattice.ishift l.1 (liftSite M l.2))))⁻¹
    = g l.2 * U (liftLink M l) * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
  rw [InfiniteLattice.siteMod_ishift, siteMod_liftSite]

#print axioms restrictConf_igauge

/-- The torus reading of a periodic gauge-invariant observable is invariant under every torus gauge
transformation.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_gauge {M : ℕ} {F : C(GibbsSpec.IConf (SU N), ℝ)}
    (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    torusObs M F (LocalGauge.gaugeTransform g W) = torusObs M F W := by
  have hF' : PeriodicGaugeInv M F := hF
  show F (pullback M (LocalGauge.gaugeTransform g W)) = F (pullback M W)
  rw [pullback_gaugeTransform]
  exact hF' g (pullback M W)

#print axioms torusObs_gauge

/-- **The heat bath keeps torus gauge invariance.** The gauge transformation at the updated link is
a two-sided translation of the integration variable (`integral_twoSided`), and the weight is gauge
invariant (`LocalGauge.boltz_gauge_invariant_local`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem heatAvg_gauge (β : ℝ) {M : ℕ} (l : WilsonHypercubic.Link 4 (M + 1))
    {φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hφ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), φ (LocalGauge.gaugeTransform g W) = φ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    heatAvg (bdT M) β l φ (LocalGauge.gaugeTransform g W) = heatAvg (bdT M) β l φ W := by
  have hupd : ∀ h : SU N, Function.update (LocalGauge.gaugeTransform g W) l h
      = LocalGauge.gaugeTransform g
          (Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2))) := by
    intro h
    funext l'
    by_cases hl : l' = l
    · rw [hl, Function.update_self]
      show h = g l.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l
        * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
      rw [Function.update_self]
      group
    · rw [Function.update_of_ne hl]
      show g l'.2 * W l' * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
        = g l'.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l'
          * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
      rw [Function.update_of_ne hl]
  have hwt : ∀ V : WilsonHypercubic.Link 4 (M + 1) → SU N,
      wt (bdT M) β (LocalGauge.gaugeTransform g V) = wt (bdT M) β V :=
    fun V => LocalGauge.boltz_gauge_invariant_local g β V
  unfold heatAvg heatNum heatPart
  simp only [hupd, hφ, hwt]
  rw [integral_twoSided (fun y => φ (Function.update W l y) * wt (bdT M) β (Function.update W l y)),
    integral_twoSided (fun y => wt (bdT M) β (Function.update W l y))]

#print axioms heatAvg_gauge

/-- **The heat bath lifted to `ℤ⁴` observables**: the heat bath at the torus link `l` of the torus
reading of `F`, composed with the restriction to one period.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def heatLift (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) : C(GibbsSpec.IConf (SU N), ℝ) :=
  ⟨fun U => heatAvg (bdT M) β l (torusObs M F) (restrictConf M U),
    (continuous_heatAvg (bdT M) β l (continuous_torusObs M F)).comp (continuous_restrictConf M)⟩

/-- The torus reading of the lifted heat bath is the heat bath of the torus reading
(`restrictConf_pullback`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_heatLift (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) :
    torusObs M (heatLift β M l F) = heatAvg (bdT M) β l (torusObs M F) := by
  funext W
  show heatAvg (bdT M) β l (torusObs M F) (restrictConf M (pullback M W))
    = heatAvg (bdT M) β l (torusObs M F) W
  rw [restrictConf_pullback]

#print axioms torusObs_heatLift

/-- **The lifted heat bath keeps periodic gauge invariance** (`restrictConf_igauge`,
`heatAvg_gauge`, `torusObs_gauge`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem heatLift_mem (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) :
    heatLift β M l F ∈ periodicGaugeInvSubmodule (N := N) M := by
  show ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : GibbsSpec.IConf (SU N)),
    heatLift β M l F (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = heatLift β M l F U
  intro g U
  show heatAvg (bdT M) β l (torusObs M F)
      (restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U))
    = heatAvg (bdT M) β l (torusObs M F) (restrictConf M U)
  rw [restrictConf_igauge]
  exact heatAvg_gauge β l (fun g' W => torusObs_gauge hF g' W) g (restrictConf M U)

#print axioms heatLift_mem

/-- **The heat-bath conditional expectation at the torus link `l`** as a linear map of the
periodic gauge-invariant observables at extent `M + 1` (`heatAvg_add`, `heatAvg_const_mul`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def torusCondExp (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) M) →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) M) where
  toFun x := ⟨heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ)), heatLift_mem β M l x.2⟩
  map_add' x y := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show heatAvg (bdT M) β l
        (torusObs M ((x : C(GibbsSpec.IConf (SU N), ℝ)) + (y : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
        + heatAvg (bdT M) β l (torusObs M (y : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact heatAvg_add (bdT M) β l (continuous_torusObs M _) (continuous_torusObs M _)
      (restrictConf M U)
  map_smul' c x := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show heatAvg (bdT M) β l (torusObs M (c • (x : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = c * heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact heatAvg_const_mul (bdT M) β l c _ (restrictConf M U)

/-- The underlying observable of `torusCondExp β M l x` is `heatLift β M l x`, by definition.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_coe (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    ((torusCondExp β M l x : ↥(periodicGaugeInvSubmodule (N := N) M))
      : C(GibbsSpec.IConf (SU N), ℝ)) = heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ)) := rfl

#print axioms torusCondExp_coe

/-- **Self-adjointness for `torusForm`** (detailed balance, `expect_heatAvg_mul`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN`. -/
theorem torusCondExp_selfAdj (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (torusCondExp β (2 * j + 1) l x) y
      = torusForm hN β j x (torusCondExp β (2 * j + 1) l y) := by
  rw [torusForm_apply, torusForm_apply]
  show ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ))) W
        * torusObs (2 * j + 1) (y : C(GibbsSpec.IConf (SU N), ℝ)) W)
    = ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W
        * torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (y : C(GibbsSpec.IConf (SU N), ℝ))) W)
  rw [torusObs_heatLift, torusObs_heatLift]
  exact expect_heatAvg_mul (bdT (2 * j + 1)) β l (continuous_torusObs _ _)
    (continuous_torusObs _ _)

#print axioms torusCondExp_selfAdj

/-- **Idempotence** (`heatAvg_of_readsNot`, `heatAvg_update`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_idem (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp β M l (torusCondExp β M l x) = torusCondExp β M l x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) β l (torusObs M (heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_heatLift]
  exact heatAvg_of_readsNot (bdT M) β l (fun W g => heatAvg_update (bdT M) β l _ W g) _

#print axioms torusCondExp_idem

/-- **The values do not read `l`** (`heatAvg_update`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem torusCondExp_readsNot (β : ℝ) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    ReadsNot j l ((torusCondExp β (2 * j + 1) l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
      : C(GibbsSpec.IConf (SU N), ℝ)) := by
  unfold ReadsNot
  intro W g
  show torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ)))
      (Function.update W l g)
    = torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ))) W
  rw [torusObs_heatLift]
  exact heatAvg_update (bdT (2 * j + 1)) β l _ W g

#print axioms torusCondExp_readsNot

/-- **The torus reading of an observable not reading `l` is kept** (`heatAvg_of_readsNot`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem torusCondExp_keeps (β : ℝ) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hx : ReadsNot j l (x : C(GibbsSpec.IConf (SU N), ℝ))) :
    torusObs (2 * j + 1)
        ((torusCondExp β (2 * j + 1) l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ))
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) := by
  show torusObs (2 * j + 1) (heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ)))
    = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))
  rw [torusObs_heatLift]
  funext W
  exact heatAvg_of_readsNot (bdT (2 * j + 1)) β l hx W

#print axioms torusCondExp_keeps

/-- **Conditional expectations at links sharing no plaquette commute** (`heatAvg_comm`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_comm (β : ℝ) (M : ℕ) {l l' : WilsonHypercubic.Link 4 (M + 1)} (hll : l ≠ l')
    (hs : ¬ SharePlaq (bdT M) l l') (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp β M l (torusCondExp β M l' x) = torusCondExp β M l' (torusCondExp β M l x) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) β l (torusObs M (heatLift β M l' (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg (bdT M) β l' (torusObs M (heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
  rw [torusObs_heatLift, torusObs_heatLift]
  exact heatAvg_comm (bdT M) β hll hs (continuous_torusObs M _) _

#print axioms torusCondExp_comm

end Torus

end MassGap.HeatBath
