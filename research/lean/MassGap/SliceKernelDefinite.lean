import Mathlib
import MassGap.ElectricStep
import MassGap.KernelInjective
import MassGap.CrossingIntegration

/-!
# MassGap.SliceKernelDefinite — the slice transfer kernel is definite on gauge-invariant functions

Direction `μ`, transverse extents `T`, as in `RectTransfer`. A slice carries spatial links
`V : SpT μ T → SU(N)`; the axis links `g : TT μ T → SU(N)` act on it by the gauge transformation
`gact g V (ν, y) = g_y V_{(ν,y)} g_{y+ν}⁻¹`. A function `u` of one slice is gauge invariant
(`GaugeInv u`) when `u (gact g V) = u V` for every `g` and `V`.

## What is proved

* `sliceKernel_form_eq` (**the identity**). For continuous gauge-invariant `u` and every real `β`,

      ∫∫ u(V) u(V') kT(V, V') dV dV' = C₀ · crossForm (Haar) planeCoord (2β/N) (w · u),

  with `kT = RectTransfer.kT μ T N β`, `w(V) = e^{−β sp(V)/2}` and `C₀ = ∏_l e^{−2β} > 0`. The route:
  `ElectricStep.gk_eq_gkW` writes `gk` as the axis average of `∏_l e^{−2β·wilsonDensity}` of the
  time-like plaquettes `(gact A V')_l V_l⁻¹`; `wilsonDensity` splits each factor as
  `e^{−2β} · e^{(2β/N) Re tr ((gact A V')_l V_l⁻¹)}` and `CrossingIntegration.hsRe_coe_eq` makes the
  trace `hsRe (V_l) ((gact A V')_l)` (`elecWeight_eq`, `prod_elecWeight`). The axis integral and the
  slice integrals swap (`integral_integral_swap`, continuous integrand on a compact space). At fixed
  `A`, the change of variables `V' ↦ gact A V'` preserves the product Haar measure
  (`measurePreserving_gact`, left and right invariance on each link) and `w · u` is gauge invariant
  (`sp_gact`: each spatial plaquette is conjugated, the two transverse steps commuting by `tsh_comm`),
  so the `A`-average leaves the link-plane crossing form of `KernelInjective`.
* `sliceKernel_form_nonneg`: at `0 ≤ β`, the form is `≥ 0` (`KernelInjective.crossForm_nonneg`).
* `sliceKernel_form_eq_zero_iff`: at `N ≠ 0` and `0 < β`, the form vanishes on a continuous
  gauge-invariant `u` exactly at `u = 0` (`KernelInjective.weighted_crossForm_eq_zero_iff`, with
  weight `w > 0` and coupling `2β/N > 0`).

## Place in the ledger

A component of `TorusCapstone.TorusRefPos`, not of the pinned `ExistencePos.LagOnePos`, and not a
discharge. The torus-side positivity rests on three lemmas: this definiteness
(`sliceKernel_form_eq_zero_iff`, which makes the kernel powers injective in `SliceKernelPower`); the
strict diagonal term `SliceRPStrict.torusState_refl_Qr_pos`; and nonnegativity of every slice pair
`TorusRefPosPlane.torusState_refl_Qr_pair_nonneg`, whose odd–odd case
(`TorusRefPosPlane.odd_pair_nonneg`) is the change of variables of `sliceKernel_form_eq` applied to
two kernels at once, on pairs of slices. They combine in `TorusRefPosPlane.torusState_refl_sum_pos`. What `TorusRefPos`
at `planePlaq` still needs is the slice form of the reference vector (`TorusRefPosPlane.SliceForm`),
which needs `0 < ℓ`: at `ℓ = 0` the cube misses the lattice for non-dyadic `t`.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.SliceKernelDefinite`.
-/

noncomputable section

namespace MassGap.SliceKernelDefinite

open MeasureTheory MassGap.CompactGauge MassGap.RectWilson MassGap.CharacterExpansion
  MassGap.KernelInjective MassGap.ElectricStep MassGap.RectTransfer

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-! ## 1. The gauge action on one slice -/

/-- **The gauge action of axis links on the spatial links of one slice**:
`(gact g V)_{(ν,y)} = g_y V_{(ν,y)} g_{y+ν}⁻¹`. -/
def gact (g : TT μ T → SUN.SU N) (V : SpT μ T → SUN.SU N) : SpT μ T → SUN.SU N :=
  fun l => g l.2 * V l * (g (tsh μ T l.1 l.2))⁻¹

/-- A function of one slice is gauge invariant. -/
def GaugeInv (u : (SpT μ T → SUN.SU N) → ℝ) : Prop :=
  ∀ (g : TT μ T → SUN.SU N) (V : SpT μ T → SUN.SU N), u (gact g V) = u V

/-- Two transverse steps commute. -/
theorem tsh_comm (ν ν' : {j : Fin 4 // j ≠ μ}) (y : TT μ T) :
    tsh μ T ν (tsh μ T ν' y) = tsh μ T ν' (tsh μ T ν y) := by
  by_cases h : ν = ν'
  · subst h; rfl
  · unfold tsh
    rw [Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
    exact Function.update_comm (Ne.symm h) _ _ _

/-- The spatial plaquette action is gauge invariant: each plaquette is conjugated by `g_y`. -/
theorem sp_gact (g : TT μ T → SUN.SU N) (V : SpT μ T → SUN.SU N) :
    spT μ T (gact g V) = spT μ T V := by
  unfold spT
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ν' _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp only [gact]
  rw [tsh_comm ν' ν y]
  set a := g y
  set b := g (tsh μ T ν y)
  set c := g (tsh μ T ν' y)
  set d := g (tsh μ T ν (tsh μ T ν' y))
  set p := V (ν, y)
  set q := V (ν', tsh μ T ν y)
  set r := V (ν, tsh μ T ν' y)
  set s := V (ν', y)
  have e : a * p * b⁻¹ * (b * q * d⁻¹) * (c * r * d⁻¹)⁻¹ * (a * s * c⁻¹)⁻¹
      = a * (p * q * r⁻¹ * s⁻¹) * a⁻¹ := by group
  rw [e, WilsonAction.wilsonDensity_conj]

theorem continuous_gact_uncurry :
    Continuous fun p : (TT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) => gact p.1 p.2 := by
  refine continuous_pi fun l => ?_
  unfold gact
  fun_prop

/-- Two-sided multiplication preserves Haar measure on one link. -/
theorem measurePreserving_link (a b : SUN.SU N) :
    MeasurePreserving (fun x : SUN.SU N => a * x * b⁻¹) (probHaar (SUN.SU N)) (probHaar (SUN.SU N)) :=
  (measurePreserving_mul_left (probHaar (SUN.SU N)) a).mul_right (probHaar (SUN.SU N)) b⁻¹

/-- The gauge action preserves the product Haar measure on one slice. -/
theorem measurePreserving_gact (g : TT μ T → SUN.SU N) :
    MeasurePreserving (gact g) (hS μ T N) (hS μ T N) := by
  have h := measurePreserving_pi (fun _ : SpT μ T => probHaar (SUN.SU N))
    (fun _ : SpT μ T => probHaar (SUN.SU N))
    (f := fun l (x : SUN.SU N) => g l.2 * x * (g (tsh μ T l.1 l.2))⁻¹)
    (fun l => measurePreserving_link (g l.2) (g (tsh μ T l.1 l.2)))
  exact h

/-! ## 2. The time-like factor as a product of link crossing weights -/

theorem hsRe_symm (A B : Matrix (Fin N) (Fin N) ℂ) : hsRe A B = hsRe B A := by
  rw [hsRe_eq_sum, hsRe_eq_sum]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- One time-like plaquette: `e^{−2β·wilsonDensity(a b⁻¹)} = e^{−2β} e^{(2β/N) Re tr (b aᴴ)}`. -/
theorem elecWeight_eq (β : ℝ) (a b : SUN.SU N) :
    elecWeight N β (a * b⁻¹)
      = Real.exp (-(2 * β)) * Real.exp (2 * β / N * hsRe (b : Matrix (Fin N) (Fin N) ℂ) a) := by
  unfold elecWeight WilsonAction.wilsonDensity
  rw [hsRe_symm, CrossingIntegration.hsRe_coe_eq a b, ← Real.exp_add]
  congr 1
  ring

/-- The constant `C₀ = ∏_l e^{−2β}`. -/
def cZero (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (β : ℝ) : ℝ :=
  ∏ _l : SpT μ T, Real.exp (-(2 * β))

theorem cZero_pos (β : ℝ) : 0 < cZero μ T β :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-- The weight `w(V) = e^{−β sp(V)/2}`. -/
def wt (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) (β : ℝ) (V : SpT μ T → SUN.SU N) : ℝ :=
  Real.exp (-β * spT μ T V / 2)

theorem continuous_wt (β : ℝ) : Continuous (wt μ T N β) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_sp continuous_id)).div_const _)

theorem wt_gact (β : ℝ) (g : TT μ T → SUN.SU N) (V : SpT μ T → SUN.SU N) :
    wt μ T N β (gact g V) = wt μ T N β V := by
  unfold wt; rw [sp_gact]

/-- The product of the time-like weights is `C₀` times the link-plane kernel at `V` and `gact A V'`. -/
theorem prod_elecWeight (β : ℝ) (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    ∏ l, elecWeight N β (tplaq A V V' l)
      = cZero μ T β * Real.exp (2 * β / N * coordKernel planeCoord V (gact A V')) := by
  rw [exp_coordKernel_planeCoord, cZero, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => elecWeight_eq β (gact A V' l) (V l)

/-! ## 3. The identity -/

/-- `gk` as the axis average of the link-plane kernel at `V` and `gact A V'`. -/
theorem gk_eq_axis (β : ℝ) (V V' : SpT μ T → SUN.SU N) :
    gk μ T N β V V' = cZero μ T β *
      ∫ A, Real.exp (2 * β / N * coordKernel planeCoord V (gact A V')) ∂(hA μ T N) := by
  rw [gk_eq_gkW, ← integral_const_mul]
  unfold gkW
  exact integral_congr_ae (Filter.Eventually.of_forall fun A => prod_elecWeight β A V V')

/-- At fixed axis links, the change of variables `V' ↦ gact A V'` on the second slice. -/
theorem integral_gact_snd (A : TT μ T → SUN.SU N)
    {F : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) → ℝ} (hF : Continuous F) :
    ∫ z, F (z.1, gact A z.2) ∂((hS μ T N).prod (hS μ T N))
      = ∫ z, F z ∂((hS μ T N).prod (hS μ T N)) := by
  have hmp : MeasurePreserving (Prod.map id (gact A)) ((hS μ T N).prod (hS μ T N))
      ((hS μ T N).prod (hS μ T N)) :=
    (MeasurePreserving.id (hS μ T N)).prod (measurePreserving_gact A)
  have h := integral_map (μ := (hS μ T N).prod (hS μ T N)) hmp.measurable.aemeasurable
    (hF.aestronglyMeasurable (μ := Measure.map (Prod.map id (gact A)) ((hS μ T N).prod (hS μ T N))))
  rw [hmp.map_eq] at h
  exact h.symm

/-- The axis average and the slice integrals swap, and the change of variables removes the axis
average. -/
theorem integral_swap_gact {F : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) → ℝ}
    (hF : Continuous F) :
    ∫ z, ∫ A, F (z.1, gact A z.2) ∂(hA μ T N) ∂((hS μ T N).prod (hS μ T N))
      = ∫ z, F z ∂((hS μ T N).prod (hS μ T N)) := by
  have hφ : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) × (TT μ T → SUN.SU N) =>
      ((p.1.1, gact p.2 p.1.2) : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) := by
    refine continuous_fst.fst.prodMk (continuous_pi fun l => ?_)
    unfold gact
    fun_prop
  have hG : Integrable (Function.uncurry fun (z : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      (A : TT μ T → SUN.SU N) => F (z.1, gact A z.2)) (((hS μ T N).prod (hS μ T N)).prod (hA μ T N)) :=
    integrable_of_continuous (hF.comp hφ)
  refine (integral_integral_swap hG).trans ?_
  refine (integral_congr_ae (Filter.Eventually.of_forall fun A => integral_gact_snd A hF)).trans ?_
  rw [integral_const, probReal_univ, one_smul]

variable (μ T N) in
/-- The integrand of the link-plane crossing form at `w · u`. -/
def ffun (β : ℝ) (u : (SpT μ T → SUN.SU N) → ℝ) (z : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) : ℝ :=
  (wt μ T N β z.1 * u z.1) * (wt μ T N β z.2 * u z.2)
    * Real.exp (2 * β / N * coordKernel planeCoord z.1 z.2)

theorem continuous_ffun (β : ℝ) {u : (SpT μ T → SUN.SU N) → ℝ} (hu : Continuous u) :
    Continuous (ffun μ T N β u) :=
  ((((continuous_wt β).comp continuous_fst).mul (hu.comp continuous_fst)).mul
    (((continuous_wt β).comp continuous_snd).mul (hu.comp continuous_snd))).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_coordKernel continuous_planeCoord)))

/-- Pointwise: the form integrand is `C₀` times the axis average of the crossing integrand at
`(V, gact A V')`. -/
theorem form_integrand_eq (β : ℝ) {u : (SpT μ T → SUN.SU N) → ℝ} (hinv : GaugeInv u)
    (z : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) :
    u z.1 * u z.2 * kT μ T N β z.1 z.2
      = cZero μ T β * ∫ A, ffun μ T N β u (z.1, gact A z.2) ∂(hA μ T N) := by
  have hF : ∀ A : TT μ T → SUN.SU N, ffun μ T N β u (z.1, gact A z.2)
      = (wt μ T N β z.1 * u z.1) * (wt μ T N β z.2 * u z.2)
        * Real.exp (2 * β / N * coordKernel planeCoord z.1 (gact A z.2)) := by
    intro A
    simp only [ffun, wt_gact, hinv A z.2]
  rw [integral_congr_ae (Filter.Eventually.of_forall hF), integral_const_mul]
  unfold kT
  rw [gk_eq_axis]
  simp only [wt]
  ring

/-- **The slice-kernel form is a positive multiple of a link-plane crossing form.** For continuous
gauge-invariant `u` and every real `β`:
`∫∫ u(V) u(V') kT(V,V') = C₀ · crossForm (Haar) planeCoord (2β/N) (w · u)`. -/
theorem sliceKernel_form_eq (β : ℝ) {u : (SpT μ T → SUN.SU N) → ℝ} (hu : Continuous u)
    (hinv : GaugeInv u) :
    ∫ z, u z.1 * u z.2 * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N))
      = cZero μ T β * crossForm (hS μ T N) planeCoord (2 * β / N)
          (fun V => wt μ T N β V * u V) := by
  calc ∫ z, u z.1 * u z.2 * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N))
      = ∫ z, cZero μ T β * ∫ A, ffun μ T N β u (z.1, gact A z.2) ∂(hA μ T N)
          ∂((hS μ T N).prod (hS μ T N)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => form_integrand_eq β hinv z)
    _ = cZero μ T β * ∫ z, ffun μ T N β u z ∂((hS μ T N).prod (hS μ T N)) := by
        rw [integral_const_mul, integral_swap_gact (continuous_ffun β hu)]
    _ = cZero μ T β * crossForm (hS μ T N) planeCoord (2 * β / N)
          (fun V => wt μ T N β V * u V) := rfl

/-! ## 4. Nonnegativity and definiteness -/

/-- **The slice-kernel form is nonnegative** on continuous gauge-invariant functions, at `0 ≤ β`. -/
theorem sliceKernel_form_nonneg {β : ℝ} (hβ : 0 ≤ β) {u : (SpT μ T → SUN.SU N) → ℝ}
    (hu : Continuous u) (hinv : GaugeInv u) :
    0 ≤ ∫ z, u z.1 * u z.2 * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N)) := by
  rw [sliceKernel_form_eq β hu hinv]
  exact mul_nonneg (cZero_pos β).le
    (crossForm_nonneg (hS μ T N) continuous_planeCoord ((continuous_wt β).mul hu)
      (div_nonneg (mul_nonneg zero_le_two hβ) (Nat.cast_nonneg N)))

/-- **The slice-kernel form is definite** on continuous gauge-invariant functions: at `N ≠ 0` and
`0 < β` it vanishes exactly at `u = 0`. -/
theorem sliceKernel_form_eq_zero_iff (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (u : C(SpT μ T → SUN.SU N, ℝ)) (hinv : GaugeInv (⇑u)) :
    ∫ z, u z.1 * u z.2 * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N)) = 0 ↔ u = 0 := by
  rw [sliceKernel_form_eq β u.continuous hinv, mul_eq_zero, or_iff_right (cZero_pos β).ne']
  have hc : 0 < 2 * β / N :=
    div_pos (mul_pos two_pos hβ) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
  exact weighted_crossForm_eq_zero_iff (hS μ T N) continuous_planeCoord planeCoord_sep hc
    ⟨wt μ T N β, continuous_wt β⟩ (fun _ => (Real.exp_pos _).ne') u

end MassGap.SliceKernelDefinite

end

#print axioms MassGap.SliceKernelDefinite.tsh_comm
#print axioms MassGap.SliceKernelDefinite.sp_gact
#print axioms MassGap.SliceKernelDefinite.measurePreserving_gact
#print axioms MassGap.SliceKernelDefinite.elecWeight_eq
#print axioms MassGap.SliceKernelDefinite.prod_elecWeight
#print axioms MassGap.SliceKernelDefinite.sliceKernel_form_eq
#print axioms MassGap.SliceKernelDefinite.sliceKernel_form_nonneg
#print axioms MassGap.SliceKernelDefinite.sliceKernel_form_eq_zero_iff
