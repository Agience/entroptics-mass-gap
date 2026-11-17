import Mathlib
import MassGap.PurityKernelPositive
import MassGap.SliceKernelDefinite

/-!
# MassGap.SliceKernelDefiniteG — the slice transfer kernel is definite on gauge-invariant functions, every gauge group

`SliceKernelDefinite` for a general compact gauge group `G` (`GaugeGroup`, defining representation
`ρ = repM G` of dimension `d`, injective). The axis links `A : TT μ T → G` act on a slice by
`PurityKernelPositive.gaugeAct`; `GaugeInvG u` says `u (gaugeAct A V) = u V`.

* `sp_gaugeAct`, `measurePreserving_gaugeAct`: the spatial action is gauge invariant; the gauge
  action preserves the product Haar measure.
* `entryCoord_sep`, `planeCoordG`, `planeCoordG_sep`: the coordinates
  `PurityKernelPositive.entryCoord` separate the points of `G` (`repM_injective`), and of a slice.
* `crossEnergy_planeCoord`: `E(V, W) = |SpT| − (1/d) coordKernel planeCoordG V W`
  (`PurityKernelPositive.wilsonDensityG_mul_inv`).
* `gkG_eq_axis`: `gkG = C₀ ∫ e^{(2β/d) coordKernel planeCoordG V (A · V')} dA`,
  `C₀ = e^{−2β |SpT|}`.
* `sliceKernelG_form_eq`: for continuous gauge-invariant `u`,
  `∫∫ u(V) u(V') kTG(V, V') = C₀ · crossForm (Haar) planeCoordG (2β/d) (w · u)`,
  `w(V) = e^{−β spTG(V)/2}`.
* `sliceKernelG_form_eq_zero_iff`: at `β > 0` the form vanishes on a continuous gauge-invariant `u`
  exactly at `u = 0`. Nonnegativity on every integrable `u` is
  `PurityKernelPositive.kTG_quad_nonneg`.

DERIVED (module-wide): `2` the count of each time-like plaquette in both orders (`gkG`).
-/

noncomputable section

namespace MassGap.SliceKernelDefiniteG

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG
  MassGap.RectTransferG MassGap.KernelInjective MassGap.GaugeGroup MassGap.PurityKernelPositive

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-! ## 1. The gauge action on one slice -/

/-- A function of one slice is gauge invariant. -/
def GaugeInvG (u : (SpT μ T → G) → ℝ) : Prop :=
  ∀ (A : TT μ T → G) (V : SpT μ T → G), u (gaugeAct A V) = u V

theorem sp_gaugeAct (A : TT μ T → G) (V : SpT μ T → G) :
    spTG G μ T (gaugeAct A V) = spTG G μ T V := by
  unfold spTG
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ν' _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp only [gaugeAct]
  rw [SliceKernelDefinite.tsh_comm ν' ν y]
  set a := A y
  set b := A (tsh μ T ν y)
  set c := A (tsh μ T ν' y)
  set d := A (tsh μ T ν (tsh μ T ν' y))
  set p := V (ν, y)
  set q := V (ν', tsh μ T ν y)
  set r := V (ν, tsh μ T ν' y)
  set s := V (ν', y)
  have e : a * p * b⁻¹ * (b * q * d⁻¹) * (c * r * d⁻¹)⁻¹ * (a * s * c⁻¹)⁻¹
      = a * (p * q * r⁻¹ * s⁻¹) * a⁻¹ := by group
  rw [e, wilsonDensityG_conj]

theorem measurePreserving_gaugeAct (A : TT μ T → G) :
    MeasurePreserving (gaugeAct A) (hSG G μ T) (hSG G μ T) :=
  measurePreserving_pi (fun _ : SpT μ T => probHaar G) (fun _ : SpT μ T => probHaar G)
    (f := fun l (x : G) => A l.2 * x * (A (tsh μ T l.1 l.2))⁻¹)
    (fun l => (measurePreserving_mul_left (probHaar G) (A l.2)).mul_right (probHaar G)
      (A (tsh μ T l.1 l.2))⁻¹)

/-! ## 2. Coordinates -/

theorem entryCoord_sep (g h : G) (hp : ∀ q, entryCoord q g = entryCoord q h) : g = h := by
  apply repM_injective
  ext i j
  apply Complex.ext
  · simpa [entryCoord] using hp (i, j, true)
  · simpa [entryCoord] using hp (i, j, false)

/-- The coordinates of a slice: `entryCoord q (V l)`. -/
def planeCoordG (i : SpT μ T × (Fin (dim G) × Fin (dim G) × Bool)) (V : SpT μ T → G) : ℝ :=
  entryCoord i.2 (V i.1)

theorem continuous_planeCoordG (i : SpT μ T × (Fin (dim G) × Fin (dim G) × Bool)) :
    Continuous (planeCoordG (G := G) i) :=
  (continuous_entryCoord i.2).comp (continuous_apply i.1)

theorem planeCoordG_sep (V W : SpT μ T → G) (h : ∀ i, planeCoordG i V = planeCoordG i W) :
    V = W :=
  funext fun l => entryCoord_sep (V l) (W l) (fun q => h (l, q))

theorem crossEnergy_planeCoord (V W : SpT μ T → G) :
    crossEnergy V W = Fintype.card (SpT μ T) - (1 / (dim G : ℝ)) * coordKernel planeCoordG V W := by
  have h : coordKernel planeCoordG V W = ∑ l, ∑ q, entryCoord q (V l) * entryCoord q (W l) :=
    Fintype.sum_prod_type _
  rw [h]
  unfold crossEnergy
  simp only [wilsonDensityG_mul_inv]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-! ## 3. The time-like factor -/

/-- `gkG` as the axis average of the link-plane kernel at `V` and `A · V'`. -/
theorem gkG_eq_axis (β : ℝ) (V V' : SpT μ T → G) :
    gkG G μ T β V V' = Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
      ∫ A, Real.exp (2 * β / dim G * coordKernel planeCoordG V (gaugeAct A V')) ∂(hAG G μ T) := by
  rw [← integral_const_mul]
  unfold gkG
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  dsimp only
  rw [tpTG_eq, crossEnergy_planeCoord, ← Real.exp_add]
  congr 1
  ring

/-! ## 4. The identity -/

/-- `w(V) = e^{−β spTG(V)/2}`. -/
def wtG (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (β : ℝ) (V : SpT μ T → G) : ℝ :=
  Real.exp (-β * spTG G μ T V / 2)

theorem continuous_wtG (β : ℝ) : Continuous (wtG (G := G) μ T β) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_spG continuous_id)).div_const _)

theorem wtG_gaugeAct (β : ℝ) (A : TT μ T → G) (V : SpT μ T → G) :
    wtG μ T β (gaugeAct A V) = wtG μ T β V := by
  unfold wtG; rw [sp_gaugeAct]

theorem integral_gaugeAct_snd (A : TT μ T → G) {F : (SpT μ T → G) × (SpT μ T → G) → ℝ}
    (hF : Continuous F) :
    ∫ z, F (z.1, gaugeAct A z.2) ∂((hSG G μ T).prod (hSG G μ T))
      = ∫ z, F z ∂((hSG G μ T).prod (hSG G μ T)) := by
  have hmp : MeasurePreserving (Prod.map id (gaugeAct A)) ((hSG G μ T).prod (hSG G μ T))
      ((hSG G μ T).prod (hSG G μ T)) :=
    (MeasurePreserving.id (hSG G μ T)).prod (measurePreserving_gaugeAct A)
  have h := integral_map (μ := (hSG G μ T).prod (hSG G μ T)) hmp.measurable.aemeasurable
    (hF.aestronglyMeasurable
      (μ := Measure.map (Prod.map id (gaugeAct A)) ((hSG G μ T).prod (hSG G μ T))))
  rw [hmp.map_eq] at h
  exact h.symm

theorem integral_swap_gaugeAct {F : (SpT μ T → G) × (SpT μ T → G) → ℝ} (hF : Continuous F) :
    ∫ z, ∫ A, F (z.1, gaugeAct A z.2) ∂(hAG G μ T) ∂((hSG G μ T).prod (hSG G μ T))
      = ∫ z, F z ∂((hSG G μ T).prod (hSG G μ T)) := by
  have hφ : Continuous fun p : ((SpT μ T → G) × (SpT μ T → G)) × (TT μ T → G) =>
      ((p.1.1, gaugeAct p.2 p.1.2) : (SpT μ T → G) × (SpT μ T → G)) := by
    refine continuous_fst.fst.prodMk (continuous_pi fun l => ?_)
    unfold gaugeAct
    fun_prop
  have hG : Integrable (Function.uncurry fun (z : (SpT μ T → G) × (SpT μ T → G))
      (A : TT μ T → G) => F (z.1, gaugeAct A z.2))
      (((hSG G μ T).prod (hSG G μ T)).prod (hAG G μ T)) :=
    integrable_of_continuous (hF.comp hφ)
  refine (integral_integral_swap hG).trans ?_
  refine (integral_congr_ae (Filter.Eventually.of_forall fun A => integral_gaugeAct_snd A hF)).trans ?_
  rw [integral_const, probReal_univ, one_smul]

/-- The integrand of the link-plane crossing form at `w · u`. -/
def ffunG (β : ℝ) (u : (SpT μ T → G) → ℝ) (z : (SpT μ T → G) × (SpT μ T → G)) : ℝ :=
  (wtG μ T β z.1 * u z.1) * (wtG μ T β z.2 * u z.2)
    * Real.exp (2 * β / dim G * coordKernel planeCoordG z.1 z.2)

theorem continuous_ffunG (β : ℝ) {u : (SpT μ T → G) → ℝ} (hu : Continuous u) :
    Continuous (ffunG (μ := μ) (T := T) β u) :=
  ((((continuous_wtG β).comp continuous_fst).mul (hu.comp continuous_fst)).mul
    (((continuous_wtG β).comp continuous_snd).mul (hu.comp continuous_snd))).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_coordKernel continuous_planeCoordG)))

theorem form_integrandG_eq (β : ℝ) {u : (SpT μ T → G) → ℝ} (hinv : GaugeInvG u)
    (z : (SpT μ T → G) × (SpT μ T → G)) :
    u z.1 * u z.2 * kTG G μ T β z.1 z.2
      = Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
          ∫ A, ffunG β u (z.1, gaugeAct A z.2) ∂(hAG G μ T) := by
  have hF : ∀ A : TT μ T → G, ffunG β u (z.1, gaugeAct A z.2)
      = (wtG μ T β z.1 * u z.1) * (wtG μ T β z.2 * u z.2)
        * Real.exp (2 * β / dim G * coordKernel planeCoordG z.1 (gaugeAct A z.2)) := by
    intro A
    simp only [ffunG, wtG_gaugeAct, hinv A z.2]
  rw [integral_congr_ae (Filter.Eventually.of_forall hF), integral_const_mul]
  unfold kTG
  rw [gkG_eq_axis]
  simp only [wtG]
  ring

/-- **The slice-kernel form is a positive multiple of a link-plane crossing form**, every gauge
group: `∫∫ u(V) u(V') kTG(V,V') = C₀ · crossForm (Haar) planeCoordG (2β/d) (w · u)`. -/
theorem sliceKernelG_form_eq (β : ℝ) {u : (SpT μ T → G) → ℝ} (hu : Continuous u)
    (hinv : GaugeInvG u) :
    ∫ z, u z.1 * u z.2 * kTG G μ T β z.1 z.2 ∂((hSG G μ T).prod (hSG G μ T))
      = Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
          crossForm (hSG G μ T) planeCoordG (2 * β / dim G) (fun V => wtG μ T β V * u V) := by
  calc ∫ z, u z.1 * u z.2 * kTG G μ T β z.1 z.2 ∂((hSG G μ T).prod (hSG G μ T))
      = ∫ z, Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
          ∫ A, ffunG β u (z.1, gaugeAct A z.2) ∂(hAG G μ T) ∂((hSG G μ T).prod (hSG G μ T)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => form_integrandG_eq β hinv z)
    _ = Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
          ∫ z, ffunG β u z ∂((hSG G μ T).prod (hSG G μ T)) := by
        rw [integral_const_mul, integral_swap_gaugeAct (continuous_ffunG β hu)]
    _ = _ := rfl

/-! ## 5. Definiteness -/

/-- **The slice-kernel form is definite** on continuous gauge-invariant functions, every gauge
group, `β > 0`. -/
theorem sliceKernelG_form_eq_zero_iff {β : ℝ} (hβ : 0 < β) (u : C(SpT μ T → G, ℝ))
    (hinv : GaugeInvG (⇑u)) :
    ∫ z, u z.1 * u z.2 * kTG G μ T β z.1 z.2 ∂((hSG G μ T).prod (hSG G μ T)) = 0 ↔ u = 0 := by
  rw [sliceKernelG_form_eq β u.continuous hinv, mul_eq_zero, or_iff_right (Real.exp_pos _).ne']
  have hc : 0 < 2 * β / (dim G : ℝ) :=
    div_pos (mul_pos two_pos hβ) (Nat.cast_pos.mpr dim_pos)
  exact weighted_crossForm_eq_zero_iff (hSG G μ T) continuous_planeCoordG planeCoordG_sep hc
    ⟨wtG μ T β, continuous_wtG β⟩ (fun _ => (Real.exp_pos _).ne') u

end MassGap.SliceKernelDefiniteG

end

#print axioms MassGap.SliceKernelDefiniteG.sp_gaugeAct
#print axioms MassGap.SliceKernelDefiniteG.measurePreserving_gaugeAct
#print axioms MassGap.SliceKernelDefiniteG.entryCoord_sep
#print axioms MassGap.SliceKernelDefiniteG.crossEnergy_planeCoord
#print axioms MassGap.SliceKernelDefiniteG.gkG_eq_axis
#print axioms MassGap.SliceKernelDefiniteG.sliceKernelG_form_eq
#print axioms MassGap.SliceKernelDefiniteG.sliceKernelG_form_eq_zero_iff
