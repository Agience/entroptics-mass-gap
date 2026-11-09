import Mathlib
import MassGap.SliceKernelDefinite
import MassGap.HiddenChain

/-!
# MassGap.SliceKernelPower — powers of the slice transfer kernel: injectivity and the square formula

Direction `μ`, transverse extents `T`, as in `RectTransfer`. The slice transfer kernel
`kT = RectTransfer.kT μ T N β` acts on functions of one slice by

    K h (V) = ∫ kT(V, V') h(V') dV'          (`Kf`, Haar measure `hS` on the spatial links),

and on continuous functions as `Kc : C(Sl, ℝ) → C(Sl, ℝ)`.

## What is proved

* `kT_gact_right`, `kT_gact_left` (**gauge invariance of the kernel in each argument**). For every
  axis configuration `a`, `kT V (gact a V') = kT V V'` and `kT (gact a V) V' = kT V V'`. Second
  argument: each time-like plaquette of `(A, V, gact a V')` is the one of `(A·a, V, V')`
  (`tp_gact`), right translation `A ↦ A·a` preserves the product Haar measure on the axis links
  (`measurePreserving_mulAx`), so `gk` is unchanged (`gk_gact`), and the spatial weight is unchanged
  by `SliceKernelDefinite.sp_gact`. First argument by `RectTransfer.kT_symm`.
* `Kf_gaugeInv`: `K h` is gauge invariant for every function `h`, with no regularity on `h`.
* `continuous_Kf`: `K h` is continuous for continuous `h` (`RectTransfer.continuous_kT`, joint, on
  a compact space, through `continuous_parametric_integral_of_continuous`); `Kc` packages it.
* `form_eq_inner`: for continuous `u`, `∫∫ u(V) u(V') kT(V,V') = ∫ u · K u` (Fubini on a continuous
  integrand of a compact space).
* `eq_zero_of_Kc_eq_zero`: at `N ≠ 0`, `0 < β`, a continuous gauge-invariant `u` with `K u = 0` is
  `0` (the form above vanishes, then `SliceKernelDefinite.sliceKernel_form_eq_zero_iff`).
* `iterate_Kc_eq_zero` (**injectivity of the powers**). At `N ≠ 0`, `0 < β`, for every `j` and every
  continuous gauge-invariant `u`, `Kc^[j] u = 0 → u = 0`. Induction: `Kc^[j+1] u = Kc^[j] (Kc u)`,
  and `Kc u` is continuous and gauge invariant.
* `iterate_Kc_succ_eq_zero`: for every continuous `u` (gauge invariant or not),
  `Kc^[j+1] u = 0 → Kc u = 0`.
* `iterate_Kc_gaugeInv`, `iterate_Kc_one_pos`: the powers carry gauge invariance, and at `N ≠ 0`,
  `0 ≤ β`, `Kc^[j] 1 > 0` everywhere (`RectTransfer.kT_lower`: `kT ≥ kTmin > 0`; `Kf_pos`).
* `eq_zero_of_iterate_Kc_mul` (**the kernel end of strict site positivity**). At `N ≠ 0`, `0 < β`,
  for continuous gauge-invariant `q` and every `r`, `j`: `Kc^[r] (q · Kc^[j] 1) = 0 → q = 0`
  (`q · Kc^[j] 1` is continuous and gauge invariant, the powers are injective on it, and
  `Kc^[j] 1 > 0`).

Kernel powers as functions of two slices, `P_j = KernelPower.iter hS kT j = kT^{∗(j+1)}`:

* `continuous_iter`: `P_j` is jointly continuous. `integral_iter_mul`: for continuous `f`,
  `∫ P_j(x, z) f(z) dz = Kc^[j+1] f (x)` (at `N ≠ 0`, `0 ≤ β`).
* `eq_zero_of_sandwich_eq_zero`: at `N ≠ 0`, `0 < β`, for continuous gauge-invariant `q`, if the
  sandwich kernel `sand r m q (z, z') = ∫ P_r(z, x) q(x) P_m(x, z') dx` vanishes everywhere, then
  `q = 0` (integrate in `z'`: `Kc^[r+1] (q · Kc^[m+1] 1) = 0`).
* `sand_square` (**the square formula**). At `N ≠ 0`, `0 ≤ β`, for continuous `q`,

      ∫∫ q(x) q(y) P_{2r+1}(x, y) P_{2m+1}(y, x) dx dy = ∫∫ sand r m q (z, z')² dz dz',

  through `KernelPower.iter_add`, `CyclicKernel.iter_symm` (from `kT_symm`) and Fubini on the four
  slices `(x, y, z, z')` (`sandPhi`, `integral_sandPhi_snd`, `integral_sandPhi_fst`).
* `sand_square_pos` (**strict positivity of the two-insertion closed chain, kernel level**). At
  `N ≠ 0`, `0 < β`, for continuous gauge-invariant `q ≠ 0` and every `r`, `m`,
  `0 < ∫∫ q(x) q(y) kT^{∗(2r+2)}(x, y) kT^{∗(2m+2)}(y, x)`: the right side of the square formula is
  `≥ 0`, and if it vanished the continuous nonnegative row integrals would vanish
  (`eq_zero_of_integral_eq_zero`, Haar measure open-positive), so `sand ≡ 0` and `q = 0`.

## Place in the ledger

A component of `TorusCapstone.TorusRefPos` (finite-torus content), not of the pinned
`ExistencePos.LagOnePos`, and not a discharge. It is strict site reflection positivity for one slice
(M2) at the level of the slice kernel: `sand_square_pos` is the statement for the reflected
two-slice correlation once that correlation is written as the closed chain with insertions `q` at
two slices `2r + 2` apart on a cycle of length `2(r + m + 2)`. That rewriting, and M2 on the torus
for `q` gauge invariant on the slice, is `SliceRPStrict.torusState_refl_Qr_pos`. `GaugeInv` is a
property of the slice function `q` itself; for `q` built from the plaquettes of one slice (the case
of `planePlaq`) it holds plaquette by plaquette, each being conjugated as in
`SliceKernelDefinite.sp_gact`, and no four-dimensional gauge transformation is needed.

M1, nonnegativity of the slice-pair terms: at even–even powers it is `sand_square` here (for every
continuous `q`); at odd–odd powers it is `TorusRefPosPlane.odd_pair_nonneg`. The torus statement for
every pair is `TorusRefPosPlane.torusState_refl_Qr_pair_nonneg`, and the sum of slices
`TorusRefPosPlane.torusState_refl_sum_pos`. What `hpos` still needs: the slice form of the
reference vector at `planePlaq` (`TorusRefPosPlane.SliceForm`, finite-torus bookkeeping, at
`0 < ℓ`) and the volume-uniform passage `RefPassage`.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.SliceKernelPower`.
-/

noncomputable section

namespace MassGap.SliceKernelPower

open MeasureTheory MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.SliceKernelDefinite

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-! ## 1. Gauge invariance of the kernel -/

/-- The time-like plaquettes of `(A, V, gact a V')` are those of `(A·a, V, V')`. -/
theorem tp_gact (A a : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    tpT μ T A V (gact a V') = tpT μ T (fun y => A y * a y) V V' := by
  unfold tpT
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [gact]
  congr 1
  group

/-- Right translation of the axis links preserves the product Haar measure. -/
theorem measurePreserving_mulAx (a : TT μ T → SUN.SU N) :
    MeasurePreserving (fun (A : TT μ T → SUN.SU N) y => A y * a y) (hA μ T N) (hA μ T N) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU N)) (fun _ => probHaar (SUN.SU N))
    (fun y => measurePreserving_mul_right (probHaar (SUN.SU N)) (a y))

/-- The axis-integrated factor is invariant under the gauge action on its second slice. -/
theorem gk_gact (β : ℝ) (a : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    gk μ T N β V (gact a V') = gk μ T N β V V' := by
  set e := MeasurableEquiv.piCongrRight
    (fun y : TT μ T => MeasurableEquiv.mulRight (a y))
  have hmp : MeasurePreserving e (hA μ T N) (hA μ T N) := measurePreserving_mulAx a
  unfold gk
  rw [← hmp.integral_comp' (fun A => Real.exp (-β * (2 * tpT μ T A V V')))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  have hA' : (e A) = fun y => A y * a y := rfl
  show Real.exp (-β * (2 * tpT μ T A V (gact a V'))) = Real.exp (-β * (2 * tpT μ T (e A) V V'))
  rw [hA', tp_gact]

/-- **The slice kernel is gauge invariant in its second argument.** -/
theorem kT_gact_right (β : ℝ) (a : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    kT μ T N β V (gact a V') = kT μ T N β V V' := by
  unfold kT
  rw [gk_gact, sp_gact]

/-- **The slice kernel is gauge invariant in its first argument.** -/
theorem kT_gact_left (β : ℝ) (a : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    kT μ T N β (gact a V) V' = kT μ T N β V V' := by
  rw [kT_symm, kT_gact_right, kT_symm]

/-! ## 2. The kernel operator -/

variable (μ T N) in
/-- The slice kernel acting on a function of one slice: `K h (V) = ∫ kT(V,V') h(V') dV'`. -/
def Kf (β : ℝ) (h : (SpT μ T → SUN.SU N) → ℝ) (V : SpT μ T → SUN.SU N) : ℝ :=
  ∫ V', kT μ T N β V V' * h V' ∂(hS μ T N)

/-- `K h` is gauge invariant for every `h`. -/
theorem Kf_gaugeInv (β : ℝ) (h : (SpT μ T → SUN.SU N) → ℝ) : GaugeInv (Kf μ T N β h) := by
  intro g V
  unfold Kf
  refine integral_congr_ae (Filter.Eventually.of_forall fun V' => ?_)
  show kT μ T N β (gact g V) V' * h V' = kT μ T N β V V' * h V'
  rw [kT_gact_left]

/-- `K h` is continuous for continuous `h`. -/
theorem continuous_Kf (β : ℝ) {h : (SpT μ T → SUN.SU N) → ℝ} (hh : Continuous h) :
    Continuous (Kf μ T N β h) := by
  have hF : Continuous (Function.uncurry fun (V V' : SpT μ T → SUN.SU N) =>
      kT μ T N β V V' * h V') :=
    (continuous_kT β).mul (hh.comp continuous_snd)
  have hc := continuous_parametric_integral_of_continuous (μ := hS μ T N) hF isCompact_univ
  simp only [Measure.restrict_univ] at hc
  exact hc

variable (μ T N) in
/-- The slice kernel on continuous functions. -/
def Kc (β : ℝ) (h : C(SpT μ T → SUN.SU N, ℝ)) : C(SpT μ T → SUN.SU N, ℝ) :=
  ⟨Kf μ T N β h, continuous_Kf β h.continuous⟩

theorem Kc_apply (β : ℝ) (h : C(SpT μ T → SUN.SU N, ℝ)) (V : SpT μ T → SUN.SU N) :
    Kc μ T N β h V = ∫ V', kT μ T N β V V' * h V' ∂(hS μ T N) := rfl

theorem Kc_gaugeInv (β : ℝ) (h : C(SpT μ T → SUN.SU N, ℝ)) : GaugeInv ⇑(Kc μ T N β h) :=
  Kf_gaugeInv β h

/-! ## 3. The form as an inner product, and injectivity of the powers -/

/-- `∫∫ u(V) u(V') kT(V,V') = ∫ u · K u`. -/
theorem form_eq_inner (β : ℝ) (u : C(SpT μ T → SUN.SU N, ℝ)) :
    ∫ z, u z.1 * u z.2 * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N))
      = ∫ V, u V * Kc μ T N β u V ∂(hS μ T N) := by
  have hc : Continuous fun z : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      u z.1 * u z.2 * kT μ T N β z.1 z.2 :=
    ((u.continuous.comp continuous_fst).mul (u.continuous.comp continuous_snd)).mul
      (continuous_kT β)
  rw [integral_prod _ (KernelInjective.integrable_of_continuous hc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  show ∫ V', u V * u V' * kT μ T N β V V' ∂(hS μ T N)
    = u V * ∫ V', kT μ T N β V V' * u V' ∂(hS μ T N)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V' => ?_)
  show u V * u V' * kT μ T N β V V' = u V * (kT μ T N β V V' * u V')
  ring

/-- **A gauge-invariant function annihilated by the kernel is zero**, at `N ≠ 0` and `0 < β`. -/
theorem eq_zero_of_Kc_eq_zero (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (u : C(SpT μ T → SUN.SU N, ℝ)) (hinv : GaugeInv ⇑u) (h : Kc μ T N β u = 0) : u = 0 := by
  refine (sliceKernel_form_eq_zero_iff hN hβ u hinv).mp ?_
  rw [form_eq_inner, h]
  simp

/-- **The powers of the slice kernel are injective on continuous gauge-invariant functions**, at
`N ≠ 0` and `0 < β`. -/
theorem iterate_Kc_eq_zero (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (j : ℕ) :
    ∀ u : C(SpT μ T → SUN.SU N, ℝ), GaugeInv ⇑u → (Kc μ T N β)^[j] u = 0 → u = 0 := by
  induction j with
  | zero => intro u _ h; exact h
  | succ j ih =>
    intro u hinv h
    rw [Function.iterate_succ_apply] at h
    exact eq_zero_of_Kc_eq_zero hN hβ u hinv (ih (Kc μ T N β u) (Kc_gaugeInv β u) h)

/-- For every continuous `u`, `Kc^[j+1] u = 0` forces `Kc u = 0`, at `N ≠ 0` and `0 < β`. -/
theorem iterate_Kc_succ_eq_zero (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (j : ℕ)
    (u : C(SpT μ T → SUN.SU N, ℝ)) (h : (Kc μ T N β)^[j + 1] u = 0) : Kc μ T N β u = 0 := by
  rw [Function.iterate_succ_apply] at h
  exact iterate_Kc_eq_zero hN hβ j (Kc μ T N β u) (Kc_gaugeInv β u) h

/-! ## 4. The kernel end of strict site positivity -/

/-- The powers of the kernel carry gauge invariance. -/
theorem iterate_Kc_gaugeInv (β : ℝ) (j : ℕ) :
    ∀ u : C(SpT μ T → SUN.SU N, ℝ), GaugeInv ⇑u → GaugeInv ⇑((Kc μ T N β)^[j] u) := by
  induction j with
  | zero => intro u hu; exact hu
  | succ j _ =>
    intro u _
    rw [Function.iterate_succ_apply']
    exact Kc_gaugeInv β _

/-- `K h > 0` for continuous `h > 0`, at `N ≠ 0` and `0 ≤ β` (`kT ≥ kTmin > 0`). -/
theorem Kf_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {h : (SpT μ T → SUN.SU N) → ℝ}
    (hh : Continuous h) (hpos : ∀ V, 0 < h V) (V : SpT μ T → SUN.SU N) :
    0 < Kf μ T N β h V := by
  have hf : ∀ V', 0 < kT μ T N β V V' * h V' := fun V' =>
    mul_pos ((kTmin_pos β).trans_le (kT_lower hN hβ V V')) (hpos V')
  have hc : Continuous fun V' => kT μ T N β V V' * h V' :=
    ((continuous_kT β).comp (continuous_const.prodMk continuous_id)).mul hh
  unfold Kf
  rw [integral_pos_iff_support_of_nonneg (fun V' => (hf V').le)
    (KernelInjective.integrable_of_continuous hc)]
  have hs : Function.support (fun V' => kT μ T N β V V' * h V') = Set.univ :=
    Set.eq_univ_of_forall fun V' => Function.mem_support.mpr (hf V').ne'
  rw [hs, measure_univ]
  exact zero_lt_one

/-- `Kc^[j] 1 > 0` everywhere, at `N ≠ 0` and `0 ≤ β`. -/
theorem iterate_Kc_one_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (V : SpT μ T → SUN.SU N) :
    0 < (Kc μ T N β)^[j] 1 V := by
  induction j generalizing V with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact Kf_pos hN hβ ((Kc μ T N β)^[j] 1).continuous ih V

/-- **The kernel end of strict site positivity.** At `N ≠ 0` and `0 < β`, for a continuous
gauge-invariant `q` and every `r`, `j`: `Kc^[r] (q · Kc^[j] 1) = 0 → q = 0`. -/
theorem eq_zero_of_iterate_Kc_mul (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (r j : ℕ)
    (q : C(SpT μ T → SUN.SU N, ℝ)) (hq : GaugeInv ⇑q)
    (h : (Kc μ T N β)^[r] (q * (Kc μ T N β)^[j] 1) = 0) : q = 0 := by
  have hinv1 : GaugeInv ⇑(1 : C(SpT μ T → SUN.SU N, ℝ)) := fun _ _ => rfl
  have hh := iterate_Kc_gaugeInv (μ := μ) (T := T) (N := N) β j 1 hinv1
  have hprod : GaugeInv ⇑(q * (Kc μ T N β)^[j] 1) := fun g V => by
    simp only [ContinuousMap.mul_apply]
    rw [hq g V, hh g V]
  have h0 := iterate_Kc_eq_zero hN hβ r _ hprod h
  ext V
  have hV : q V * (Kc μ T N β)^[j] 1 V = 0 := by
    have := DFunLike.congr_fun h0 V
    simpa only [ContinuousMap.mul_apply, ContinuousMap.zero_apply] using this
  have hp := iterate_Kc_one_pos hN hβ.le j V
  rw [ContinuousMap.zero_apply]
  exact (mul_eq_zero.mp hV).resolve_right hp.ne'

/-! ## 5. Kernel powers as functions of two slices -/

open MassGap.KernelPower in
/-- The kernel powers `iter hS kT j = kT^{∗(j+1)}` are jointly continuous. -/
theorem continuous_iter (β : ℝ) :
    ∀ j, Continuous (Function.uncurry (iter (hS μ T N) (kT μ T N β) j))
  | 0 => continuous_kT β
  | j + 1 => by
    have ih := continuous_iter β j
    have hF : Continuous (Function.uncurry
        fun (p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) (y : SpT μ T → SUN.SU N) =>
          kT μ T N β p.1 y * iter (hS μ T N) (kT μ T N β) j y p.2) :=
      ((continuous_kT β).comp (continuous_fst.fst.prodMk continuous_snd)).mul
        (ih.comp (continuous_snd.prodMk continuous_fst.snd))
    have hc := continuous_parametric_integral_of_continuous (μ := hS μ T N) hF isCompact_univ
    simp only [Measure.restrict_univ] at hc
    exact hc

open MassGap.KernelPower in
/-- The kernel power `kT^{∗(j+1)}` acting on a continuous function is `Kc^[j+1]`. -/
theorem integral_iter_mul (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (f : C(SpT μ T → SUN.SU N, ℝ)) :
    ∀ (j : ℕ) (x : SpT μ T → SUN.SU N),
      ∫ z, iter (hS μ T N) (kT μ T N β) j x z * f z ∂(hS μ T N) = (Kc μ T N β)^[j + 1] f x
  | 0, x => rfl
  | j + 1, x => by
    rw [Function.iterate_succ_apply']
    have hk := bdd_kT (μ := μ) (T := T) hN hβ
    have hki := hk.iter (μ := hS μ T N) j
    obtain ⟨C, hC⟩ := hk.bdd
    obtain ⟨Ci, hCi⟩ := hki.bdd
    obtain ⟨Bf, hBf⟩ : ∃ B, ∀ z, |f z| ≤ B :=
      ⟨‖f‖, fun z => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm z⟩
    have hF : Measurable (Function.uncurry fun (y z : SpT μ T → SUN.SU N) =>
        kT μ T N β x y * (iter (hS μ T N) (kT μ T N β) j y z * f z)) :=
      ((hk.row x).comp measurable_fst).mul
        (hki.meas.mul (f.continuous.measurable.comp measurable_snd))
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x x)
    have hFb : ∀ y z, |kT μ T N β x y * (iter (hS μ T N) (kT μ T N β) j y z * f z)|
        ≤ C * (Ci * Bf) := by
      intro y z
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hC x y) (mul_le_mul (hCi y z) (hBf z) (abs_nonneg _)
        ((abs_nonneg _).trans (hCi y z))) (by positivity) hC0
    rw [Kc_apply]
    calc ∫ z, iter (hS μ T N) (kT μ T N β) (j + 1) x z * f z ∂(hS μ T N)
        = ∫ z, ∫ y, kT μ T N β x y * (iter (hS μ T N) (kT μ T N β) j y z * f z)
            ∂(hS μ T N) ∂(hS μ T N) := by
          congr 1; funext z
          show (∫ y, kT μ T N β x y * iter (hS μ T N) (kT μ T N β) j y z ∂(hS μ T N)) * f z = _
          rw [← integral_mul_const]; congr 1; funext y; ring
      _ = ∫ y, ∫ z, kT μ T N β x y * (iter (hS μ T N) (kT μ T N β) j y z * f z)
            ∂(hS μ T N) ∂(hS μ T N) := (swap_bdd hF hFb).symm
      _ = ∫ y, kT μ T N β x y * (Kc μ T N β)^[j + 1] f y ∂(hS μ T N) := by
          congr 1; funext y
          rw [integral_const_mul, integral_iter_mul hN hβ f j y]

open MassGap.KernelPower in
/-- **A vanishing sandwich kernel forces the insertion to vanish.** At `N ≠ 0` and `0 < β`, for a
continuous gauge-invariant `q` and every `r`, `m`: if
`H(z, z') = ∫ kT^{∗(r+1)}(z, x) q(x) kT^{∗(m+1)}(x, z') dx` vanishes for all `z`, `z'`, then
`q = 0` (integrate in `z'`: `Kc^[r+1] (q · Kc^[m+1] 1) = 0`). -/
theorem eq_zero_of_sandwich_eq_zero (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (r m : ℕ)
    (q : C(SpT μ T → SUN.SU N, ℝ)) (hq : GaugeInv ⇑q)
    (hH : ∀ z z', ∫ x, iter (hS μ T N) (kT μ T N β) r z x
      * (q x * iter (hS μ T N) (kT μ T N β) m x z') ∂(hS μ T N) = 0) :
    q = 0 := by
  refine eq_zero_of_iterate_Kc_mul hN hβ (r + 1) (m + 1) q hq ?_
  ext z
  rw [ContinuousMap.zero_apply, ← integral_iter_mul hN hβ.le (q * (Kc μ T N β)^[m + 1] 1) r z]
  have hk := bdd_kT (μ := μ) (T := T) hN hβ.le
  have hr := hk.iter (μ := hS μ T N) r
  have hm := hk.iter (μ := hS μ T N) m
  obtain ⟨Cr, hCr⟩ := hr.bdd
  obtain ⟨Cm, hCm⟩ := hm.bdd
  obtain ⟨Bq, hBq⟩ : ∃ B, ∀ x, |q x| ≤ B :=
    ⟨‖q‖, fun x => by simpa [Real.norm_eq_abs] using q.norm_coe_le_norm x⟩
  have hF : Measurable (Function.uncurry fun (x z' : SpT μ T → SUN.SU N) =>
      iter (hS μ T N) (kT μ T N β) r z x * (q x * iter (hS μ T N) (kT μ T N β) m x z')) :=
    ((hr.row z).comp measurable_fst).mul ((q.continuous.measurable.comp measurable_fst).mul hm.meas)
  have hFb : ∀ x z', |iter (hS μ T N) (kT μ T N β) r z x
      * (q x * iter (hS μ T N) (kT μ T N β) m x z')| ≤ Cr * (Bq * Cm) := by
    intro x z'
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hCr z x) (mul_le_mul (hBq x) (hCm x z') (abs_nonneg _)
      ((abs_nonneg _).trans (hBq x))) (by positivity) ((abs_nonneg _).trans (hCr z x))
  have hg : ∀ x, (Kc μ T N β)^[m + 1] 1 x
      = ∫ z', iter (hS μ T N) (kT μ T N β) m x z' ∂(hS μ T N) := by
    intro x
    rw [← integral_iter_mul hN hβ.le 1 m x]
    simp only [ContinuousMap.one_apply, mul_one]
  calc ∫ x, iter (hS μ T N) (kT μ T N β) r z x * (q * (Kc μ T N β)^[m + 1] 1) x ∂(hS μ T N)
      = ∫ x, ∫ z', iter (hS μ T N) (kT μ T N β) r z x
          * (q x * iter (hS μ T N) (kT μ T N β) m x z') ∂(hS μ T N) ∂(hS μ T N) := by
        congr 1; funext x
        rw [ContinuousMap.mul_apply, hg x, ← integral_const_mul, ← integral_const_mul]
    _ = ∫ z', ∫ x, iter (hS μ T N) (kT μ T N β) r z x
          * (q x * iter (hS μ T N) (kT μ T N β) m x z') ∂(hS μ T N) ∂(hS μ T N) :=
        swap_bdd hF hFb
    _ = 0 := by simp only [hH, integral_zero]

/-! ## 6. The square formula and strict positivity at the kernel level -/

section Sandwich

open MassGap.KernelPower

variable (μ T N) in
/-- The sandwich kernel `H(z, z') = ∫ kT^{∗(r+1)}(z, x) q(x) kT^{∗(m+1)}(x, z') dx`. -/
def sand (β : ℝ) (r m : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ) (z z' : SpT μ T → SUN.SU N) : ℝ :=
  ∫ x, iter (hS μ T N) (kT μ T N β) r z x * (q x * iter (hS μ T N) (kT μ T N β) m x z')
    ∂(hS μ T N)

theorem continuous_sand (β : ℝ) (r m : ℕ) {q : (SpT μ T → SUN.SU N) → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (sand μ T N β r m q)) := by
  have hF : Continuous (Function.uncurry
      fun (p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) (x : SpT μ T → SUN.SU N) =>
        iter (hS μ T N) (kT μ T N β) r p.1 x * (q x * iter (hS μ T N) (kT μ T N β) m x p.2)) :=
    ((continuous_iter β r).comp (continuous_fst.fst.prodMk continuous_snd)).mul
      ((hq.comp continuous_snd).mul
        ((continuous_iter β m).comp (continuous_snd.prodMk continuous_fst.snd)))
  have hc := continuous_parametric_integral_of_continuous (μ := hS μ T N) hF isCompact_univ
  simp only [Measure.restrict_univ] at hc
  exact hc

variable (μ T N) in
/-- The integrand of `H(z,z')²` on the four slices `((x, y), (z, z'))`. -/
def sandPhi (β : ℝ) (r m : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) : ℝ :=
  (iter (hS μ T N) (kT μ T N β) r p.2.1 p.1.1
      * (q p.1.1 * iter (hS μ T N) (kT μ T N β) m p.1.1 p.2.2))
    * (iter (hS μ T N) (kT μ T N β) r p.2.1 p.1.2
      * (q p.1.2 * iter (hS μ T N) (kT μ T N β) m p.1.2 p.2.2))

/-- `|a b| ≤ B D` from `|a| ≤ B` and `|b| ≤ D`. An alias of `HiddenChain.abs_mul_le_of`. -/
alias abs_mul_le_of_le := MassGap.HiddenChain.abs_mul_le_of

/-- The four-slice integrand is integrable (bounded and measurable). -/
theorem integrable_sandPhi (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (r m : ℕ)
    (q : C(SpT μ T → SUN.SU N, ℝ)) :
    Integrable (sandPhi μ T N β r m q)
      (((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) := by
  have hk := bdd_kT (μ := μ) (T := T) hN hβ
  have hr := hk.iter (μ := hS μ T N) r
  have hm := hk.iter (μ := hS μ T N) m
  obtain ⟨Cr, hCr⟩ := hr.bdd
  obtain ⟨Cm, hCm⟩ := hm.bdd
  obtain ⟨Bq, hBq⟩ : ∃ B, ∀ x, |q x| ≤ B :=
    ⟨‖q‖, fun x => by simpa [Real.norm_eq_abs] using q.norm_coe_le_norm x⟩
  have hqm : Measurable q := q.continuous.measurable
  have hmeas : Measurable (sandPhi μ T N β r m q) :=
    ((hr.meas.comp (measurable_snd.fst.prodMk measurable_fst.fst)).mul
      ((hqm.comp measurable_fst.fst).mul
        (hm.meas.comp (measurable_fst.fst.prodMk measurable_snd.snd)))).mul
    ((hr.meas.comp (measurable_snd.fst.prodMk measurable_fst.snd)).mul
      ((hqm.comp measurable_fst.snd).mul
        (hm.meas.comp (measurable_fst.snd.prodMk measurable_snd.snd))))
  exact KernelPower.integrable_of_bdd hmeas (C := (Cr * (Bq * Cm)) * (Cr * (Bq * Cm))) fun p =>
    abs_mul_le_of_le (abs_mul_le_of_le (hCr _ _) (abs_mul_le_of_le (hBq _) (hCm _ _)))
      (abs_mul_le_of_le (hCr _ _) (abs_mul_le_of_le (hBq _) (hCm _ _)))

/-- Integrating `(z, z')` out of the four-slice integrand leaves the two-insertion kernel. -/
theorem integral_sandPhi_snd (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (r m : ℕ)
    (q : (SpT μ T → SUN.SU N) → ℝ) (x y : SpT μ T → SUN.SU N) :
    ∫ w, sandPhi μ T N β r m q ((x, y), w) ∂((hS μ T N).prod (hS μ T N))
      = q x * q y * (iter (hS μ T N) (kT μ T N β) (r + r + 1) x y
        * iter (hS μ T N) (kT μ T N β) (m + m + 1) y x) := by
    have hk := bdd_kT (μ := μ) (T := T) hN hβ
    have hsym := CyclicKernel.iter_symm (μ := hS μ T N) hk (kT_symm β)
    have e1 : iter (hS μ T N) (kT μ T N β) (r + r + 1) x y
        = ∫ z, iter (hS μ T N) (kT μ T N β) r z x * iter (hS μ T N) (kT μ T N β) r z y
          ∂(hS μ T N) := by
      rw [iter_add (μ := hS μ T N) hk r r]
      show ∫ z, iter (hS μ T N) (kT μ T N β) r x z * iter (hS μ T N) (kT μ T N β) r z y
        ∂(hS μ T N) = _
      congr 1; funext z; rw [hsym r x z]
    have e2 : iter (hS μ T N) (kT μ T N β) (m + m + 1) y x
        = ∫ z', iter (hS μ T N) (kT μ T N β) m x z' * iter (hS μ T N) (kT μ T N β) m y z'
          ∂(hS μ T N) := by
      rw [iter_add (μ := hS μ T N) hk m m]
      show ∫ z', iter (hS μ T N) (kT μ T N β) m y z' * iter (hS μ T N) (kT μ T N β) m z' x
        ∂(hS μ T N) = _
      congr 1; funext z'; rw [hsym m z' x, mul_comm]
    rw [e1, e2, ← integral_prod_mul, ← integral_const_mul]
    congr 1; funext w
    simp only [sandPhi]
    ring

/-- Integrating `(x, y)` out of the four-slice integrand leaves `H(z,z')²`. -/
theorem integral_sandPhi_fst (β : ℝ) (r m : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (w : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) :
    ∫ v, sandPhi μ T N β r m q (v, w) ∂((hS μ T N).prod (hS μ T N))
      = sand μ T N β r m q w.1 w.2 ^ 2 := by
  rw [sq]
  unfold sand
  rw [← integral_prod_mul]
  rfl

/-- **The square formula.** For continuous `q`, at `N ≠ 0` and `0 ≤ β`,
`∫∫ q(x) q(y) kT^{∗(2r+2)}(x,y) kT^{∗(2m+2)}(y,x) = ∫∫ H(z,z')²`, `H = sand r m q`. Through
`KernelPower.iter_add`, `CyclicKernel.iter_symm` (from `kT_symm`) and Fubini on the four slices
`(x, y, z, z')`. -/
theorem sand_square (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (r m : ℕ) (q : C(SpT μ T → SUN.SU N, ℝ)) :
    ∫ x, ∫ y, q x * q y * (iter (hS μ T N) (kT μ T N β) (r + r + 1) x y
        * iter (hS μ T N) (kT μ T N β) (m + m + 1) y x) ∂(hS μ T N) ∂(hS μ T N)
      = ∫ z, ∫ z', sand μ T N β r m q z z' ^ 2 ∂(hS μ T N) ∂(hS μ T N) := by
  have hpt1 := integral_sandPhi_snd (μ := μ) (T := T) hN hβ r m q
  have hpt2 := integral_sandPhi_fst (μ := μ) (T := T) (N := N) β r m q
  have c1 := continuous_iter (μ := μ) (T := T) (N := N) β (r + r + 1)
  have c2 := continuous_iter (μ := μ) (T := T) (N := N) β (m + m + 1)
  generalize r + r + 1 = a at hpt1 c1 ⊢
  generalize m + m + 1 = b at hpt1 c2 ⊢
  have c2' : Continuous fun v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      iter (hS μ T N) (kT μ T N β) b v.2 v.1 :=
    c2.comp continuous_swap
  have hGc : Continuous fun v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      q v.1 * q v.2 * (iter (hS μ T N) (kT μ T N β) a v.1 v.2
        * iter (hS μ T N) (kT μ T N β) b v.2 v.1) :=
    ((q.continuous.comp continuous_fst).mul (q.continuous.comp continuous_snd)).mul
      (c1.mul c2')
  have hsc : Continuous fun w : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      sand μ T N β r m q w.1 w.2 ^ 2 :=
    (continuous_sand β r m q.continuous).pow 2
  calc ∫ x, ∫ y, q x * q y * (iter (hS μ T N) (kT μ T N β) a x y
        * iter (hS μ T N) (kT μ T N β) b y x) ∂(hS μ T N) ∂(hS μ T N)
      = ∫ v, q v.1 * q v.2 * (iter (hS μ T N) (kT μ T N β) a v.1 v.2
          * iter (hS μ T N) (kT μ T N β) b v.2 v.1) ∂((hS μ T N).prod (hS μ T N)) :=
        (integral_prod (fun v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
          q v.1 * q v.2 * (iter (hS μ T N) (kT μ T N β) a v.1 v.2
            * iter (hS μ T N) (kT μ T N β) b v.2 v.1))
          (KernelInjective.integrable_of_continuous hGc)).symm
    _ = ∫ v, ∫ w, sandPhi μ T N β r m q (v, w) ∂((hS μ T N).prod (hS μ T N))
          ∂((hS μ T N).prod (hS μ T N)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun v => (hpt1 v.1 v.2).symm)
    _ = ∫ w, ∫ v, sandPhi μ T N β r m q (v, w) ∂((hS μ T N).prod (hS μ T N))
          ∂((hS μ T N).prod (hS μ T N)) :=
        integral_integral_swap (f := fun v w => sandPhi μ T N β r m q (v, w))
          (integrable_sandPhi hN hβ r m q)
    _ = ∫ w, sand μ T N β r m q w.1 w.2 ^ 2 ∂((hS μ T N).prod (hS μ T N)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt2)
    _ = ∫ z, ∫ z', sand μ T N β r m q z z' ^ 2 ∂(hS μ T N) ∂(hS μ T N) :=
        integral_prod (fun w : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
          sand μ T N β r m q w.1 w.2 ^ 2) (KernelInjective.integrable_of_continuous hsc)

/-- A continuous nonnegative function of one slice with zero Haar integral is zero. -/
theorem eq_zero_of_integral_eq_zero {f : (SpT μ T → SUN.SU N) → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) (hi : ∫ x, f x ∂(hS μ T N) = 0) (x : SpT μ T → SUN.SU N) : f x = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg h0
    (KernelInjective.integrable_of_continuous (ν := hS μ T N) hf)).mp hi
  have hpt : f = 0 := Measure.eq_of_ae_eq hae hf continuous_zero
  exact congrFun hpt x

/-- **Strict positivity of the two-insertion closed chain at the kernel level.** At `N ≠ 0` and
`0 < β`, for a continuous gauge-invariant `q ≠ 0` and every `r`, `m`,
`0 < ∫∫ q(x) q(y) kT^{∗(2r+2)}(x,y) kT^{∗(2m+2)}(y,x)`. -/
theorem sand_square_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (r m : ℕ)
    (q : C(SpT μ T → SUN.SU N, ℝ)) (hq : GaugeInv ⇑q) (hq0 : q ≠ 0) :
    0 < ∫ x, ∫ y, q x * q y * (iter (hS μ T N) (kT μ T N β) (r + r + 1) x y
        * iter (hS μ T N) (kT μ T N β) (m + m + 1) y x) ∂(hS μ T N) ∂(hS μ T N) := by
  rw [sand_square hN hβ.le r m q]
  have hsc := continuous_sand (μ := μ) (T := T) (N := N) β r m q.continuous
  have hrow : ∀ z, Continuous fun z' => sand μ T N β r m q z z' ^ 2 := fun z =>
    (hsc.comp (continuous_const.prodMk continuous_id)).pow 2
  have hG : Continuous fun z => ∫ z', sand μ T N β r m q z z' ^ 2 ∂(hS μ T N) := by
    have hc := continuous_parametric_integral_of_continuous (μ := hS μ T N)
      (f := fun z z' => sand μ T N β r m q z z' ^ 2) (hsc.pow 2) isCompact_univ
    simp only [Measure.restrict_univ] at hc
    exact hc
  have hG0 : ∀ z, 0 ≤ ∫ z', sand μ T N β r m q z z' ^ 2 ∂(hS μ T N) :=
    fun z => integral_nonneg fun z' => sq_nonneg _
  refine lt_of_le_of_ne (integral_nonneg hG0) (fun h => hq0 ?_)
  have h1 := eq_zero_of_integral_eq_zero hG hG0 h.symm
  refine eq_zero_of_sandwich_eq_zero hN hβ r m q hq fun z z' => ?_
  have h2 := eq_zero_of_integral_eq_zero (hrow z) (fun z' => sq_nonneg _) (h1 z) z'
  exact (pow_eq_zero_iff two_ne_zero).mp h2

end Sandwich

end MassGap.SliceKernelPower

end

#print axioms MassGap.SliceKernelPower.tp_gact
#print axioms MassGap.SliceKernelPower.gk_gact
#print axioms MassGap.SliceKernelPower.kT_gact_right
#print axioms MassGap.SliceKernelPower.kT_gact_left
#print axioms MassGap.SliceKernelPower.Kf_gaugeInv
#print axioms MassGap.SliceKernelPower.continuous_Kf
#print axioms MassGap.SliceKernelPower.form_eq_inner
#print axioms MassGap.SliceKernelPower.eq_zero_of_Kc_eq_zero
#print axioms MassGap.SliceKernelPower.iterate_Kc_eq_zero
#print axioms MassGap.SliceKernelPower.iterate_Kc_succ_eq_zero
#print axioms MassGap.SliceKernelPower.iterate_Kc_gaugeInv
#print axioms MassGap.SliceKernelPower.Kf_pos
#print axioms MassGap.SliceKernelPower.iterate_Kc_one_pos
#print axioms MassGap.SliceKernelPower.eq_zero_of_iterate_Kc_mul
#print axioms MassGap.SliceKernelPower.continuous_iter
#print axioms MassGap.SliceKernelPower.integral_iter_mul
#print axioms MassGap.SliceKernelPower.eq_zero_of_sandwich_eq_zero
#print axioms MassGap.SliceKernelPower.continuous_sand
#print axioms MassGap.SliceKernelPower.integrable_sandPhi
#print axioms MassGap.SliceKernelPower.integral_sandPhi_snd
#print axioms MassGap.SliceKernelPower.integral_sandPhi_fst
#print axioms MassGap.SliceKernelPower.sand_square
#print axioms MassGap.SliceKernelPower.eq_zero_of_integral_eq_zero
#print axioms MassGap.SliceKernelPower.sand_square_pos
