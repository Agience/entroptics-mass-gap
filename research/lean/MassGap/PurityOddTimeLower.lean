import Mathlib
import MassGap.PurityOddTime
import MassGap.KernelGap
import MassGap.FluxSectorBound
import MassGap.PurityKernelPositive

/-!
# MassGap.PurityOddTimeLower — `Ψ_T ≥ 0` at odd times

The lower bound `ψ_T = 2 log cyc(T) − log cyc(2T) ≥ 0` of D. Bhattacharjee, U. Bhattacharya,
J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills
Theory at Weak Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>,
commit 8e01510, `Paper-2/Paper-2.pdf`), at the time `T = 2j + 1`, `j ≥ 1`, for a positive
semidefinite kernel operator.

`k` is a bounded, jointly measurable, symmetric kernel on a probability space whose operator `K` on
`L²` is positive semidefinite, with a bounded eigenfunction `φ`, `∫ φ² = 1`, eigenvalue `c > 0`;
`r = rem k c φ = k − c φ ⊗ φ` and `R` is its operator, with `‖R‖ ≤ c`.

* `inner_pow_succ_le`, `inner_pow_nonneg`: for a symmetric positive semidefinite operator `A` on a
  real inner product space, `a_n = ⟪A^n v, v⟫` has `a_n ≥ 0` and `a_{n+1} ≤ ‖A‖ a_n`; hence
  `a_{n+l} ≤ ‖A‖^l a_n` (`inner_pow_add_le`).
* `form_sub_nonneg`: `⟪u, A u⟫ − c ⟪e, u⟫² ≥ 0` for a unit eigenvector `A e = c e`.
* `rem_apply`, `rem_form_nonneg`: `R u = K u − c ⟪u, φ⟫ φ`, so `R` is positive semidefinite.
* `iter_diag_eq`: `r^{∗(i+3)}(x, x) = ⟪R^{i+1} r(·, x), r(·, x)⟫`.
* `trace_rem_nonneg_and_hs_le`: `t = ∫ r^{∗(2j+1)}(x, x) dx ≥ 0` and
  `‖r^{∗(2j+1)}‖²_HS ≤ ‖R‖^{2j+1} t`.
* `defect_odd_nonneg`: `ψ_{2j+1} ≥ 0`, from `cyc(T) = c^T + t`, `cyc(2T) = c^{2T} + ‖r^{∗T}‖²_HS`.
* `kTG_form_nonneg`, `defect_odd_nonneg_kTG`, `ZRG_defect_odd_nonneg`: the Wilson transfer operator is
  positive semidefinite, so `ψ_{2j+1} ≥ 0` for it and `log Z(L') ≤ 2 log Z(L)`.
-/

namespace MassGap.PurityOddTimeLower

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower MassGap.CyclicKernel

/-! ## Positive semidefinite operators -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E →L[ℝ] E}
  (hA : ∀ u w, inner ℝ (A u) w = inner ℝ u (A w)) (hpsd : ∀ u, 0 ≤ inner ℝ u (A u))

include hA in
/-- `⟪A^{p+q} v, v⟫ = ⟪A^p v, A^q v⟫`. -/
theorem inner_pow_add (p q : ℕ) (v : E) :
    inner ℝ ((A ^ (p + q)) v) v = inner ℝ ((A ^ p) v) ((A ^ q) v) := by
  rw [pow_add, ContinuousLinearMap.mul_apply, KernelGap.pow_symm hA p, real_inner_comm]

theorem pow_succ_apply (m : ℕ) (v : E) : (A ^ (m + 1)) v = A ((A ^ m) v) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]

include hA hpsd in
/-- `‖A u‖² ≤ ‖A‖ ⟪A u, u⟫`. -/
theorem norm_sq_le_form (u : E) : ‖A u‖ ^ 2 ≤ ‖A‖ * inner ℝ (A u) u := by
  rcases (norm_nonneg A).eq_or_lt with h0 | hpos
  · have hz : ‖A u‖ = 0 := le_antisymm
      (by have h := A.le_opNorm u; rw [← h0, zero_mul] at h; exact h) (norm_nonneg _)
    rw [hz, ← h0]; simp
  · have hs0 : 0 < ‖A‖⁻¹ := inv_pos.mpr hpos
    have h := hpsd (u - ‖A‖⁻¹ • A u)
    rw [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right] at h
    have e1 : inner ℝ u (A (A u)) = ‖A u‖ ^ 2 := by
      rw [← hA u (A u), real_inner_self_eq_norm_sq]
    have e2 : inner ℝ (A u) (A u) = ‖A u‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hY : inner ℝ (A u) (A (A u)) ≤ ‖A‖ * ‖A u‖ ^ 2 := by
      calc inner ℝ (A u) (A (A u)) ≤ ‖A u‖ * ‖A (A u)‖ := real_inner_le_norm _ _
        _ ≤ ‖A u‖ * (‖A‖ * ‖A u‖) :=
            mul_le_mul_of_nonneg_left (A.le_opNorm (A u)) (norm_nonneg _)
        _ = ‖A‖ * ‖A u‖ ^ 2 := by ring
    rw [e1, e2] at h
    have hY' : ‖A‖⁻¹ * (‖A‖⁻¹ * inner ℝ (A u) (A (A u))) ≤
        ‖A‖⁻¹ * (‖A‖⁻¹ * (‖A‖ * ‖A u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hs0.le) hs0.le
    rw [inv_mul_cancel_left₀ hpos.ne'] at hY'
    have h1 : ‖A‖⁻¹ * ‖A u‖ ^ 2 ≤ inner ℝ u (A u) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
    rw [real_inner_comm]; exact h2

include hA hpsd in
/-- `a_{n+1} ≤ ‖A‖ a_n` and `a_n ≥ 0` for `a_n = ⟪A^n v, v⟫`. -/
theorem inner_pow_succ_le_and_nonneg (n : ℕ) (v : E) :
    inner ℝ ((A ^ (n + 1)) v) v ≤ ‖A‖ * inner ℝ ((A ^ n) v) v ∧
      0 ≤ inner ℝ ((A ^ n) v) v := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · set u := (A ^ m) v
    have e1 : inner ℝ ((A ^ (2 * m + 1)) v) v = inner ℝ (A u) u := by
      rw [show 2 * m + 1 = (m + 1) + m by ring, inner_pow_add hA, pow_succ_apply]
    have e0 : inner ℝ ((A ^ (2 * m)) v) v = ‖u‖ ^ 2 := by
      rw [two_mul, inner_pow_add hA, real_inner_self_eq_norm_sq]
    rw [e1, e0]
    refine ⟨?_, sq_nonneg _⟩
    calc inner ℝ (A u) u ≤ ‖A u‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖u‖ * ‖u‖ := mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg _)
      _ = ‖A‖ * ‖u‖ ^ 2 := by ring
  · set u := (A ^ m) v
    have e2 : inner ℝ ((A ^ (2 * m + 1 + 1)) v) v = ‖A u‖ ^ 2 := by
      rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring, inner_pow_add hA, pow_succ_apply,
        real_inner_self_eq_norm_sq]
    have e1 : inner ℝ ((A ^ (2 * m + 1)) v) v = inner ℝ (A u) u := by
      rw [show 2 * m + 1 = (m + 1) + m by ring, inner_pow_add hA, pow_succ_apply]
    rw [e2, e1]
    refine ⟨norm_sq_le_form hA hpsd u, ?_⟩
    rw [real_inner_comm]; exact hpsd u

include hA hpsd in
theorem inner_pow_nonneg (n : ℕ) (v : E) : 0 ≤ inner ℝ ((A ^ n) v) v :=
  (inner_pow_succ_le_and_nonneg hA hpsd n v).2

include hA hpsd in
/-- `a_{n+l} ≤ ‖A‖^l a_n`. -/
theorem inner_pow_add_le (n : ℕ) (v : E) :
    ∀ l : ℕ, inner ℝ ((A ^ (n + l)) v) v ≤ ‖A‖ ^ l * inner ℝ ((A ^ n) v) v
  | 0 => by simp
  | l + 1 => by
    have h := (inner_pow_succ_le_and_nonneg hA hpsd (n + l) v).1
    have IH := inner_pow_add_le n v l
    calc inner ℝ ((A ^ (n + (l + 1))) v) v ≤ ‖A‖ * inner ℝ ((A ^ (n + l)) v) v := h
      _ ≤ ‖A‖ * (‖A‖ ^ l * inner ℝ ((A ^ n) v) v) :=
          mul_le_mul_of_nonneg_left IH (norm_nonneg _)
      _ = ‖A‖ ^ (l + 1) * inner ℝ ((A ^ n) v) v := by ring

include hA hpsd in
/-- `⟪u, A u⟫ − c ⟪e, u⟫² ≥ 0` for a unit eigenvector `A e = c e`. -/
theorem form_sub_nonneg {e : E} {c : ℝ} (he : A e = c • e) (he1 : ‖e‖ = 1) (u : E) :
    0 ≤ inner ℝ u (A u) - c * inner ℝ e u ^ 2 := by
  set a := inner ℝ e u with ha
  have h := hpsd (u - a • e)
  rw [map_sub, map_smul, he, smul_smul, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right] at h
  have e1 : inner ℝ e (A u) = c * a := by rw [← hA e u, he, real_inner_smul_left]
  have e2 : inner ℝ u e = a := real_inner_comm e u
  have e3 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he1, one_pow]
  rw [e1, e2, e3] at h
  nlinarith [h]

end Abstract

/-! ## The remainder operator -/

section Kernel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
  (hrb : ∀ x y, |rem k c φ x y| ≤ Cr)

include hkm hkb hφm hφb in
/-- `R u = K u − c ⟪u, φ⟫ φ`. -/
theorem rem_apply (u : Lp ℝ 2 μ) :
    kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ u =
      kernelCLM k C hkm hC0 hkb μ μ u -
        (c * inner ℝ u (KernelGap.vac (μ := μ) hφm hφb)) • KernelGap.vac (μ := μ) hφm hφb := by
  have hu1 : Integrable (u : X → ℝ) μ := (Lp.memLp u).integrable one_le_two
  apply Lp.ext
  filter_upwards [coeFn_kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ u,
    coeFn_kernelCLM k C hkm hC0 hkb μ μ u,
    Lp.coeFn_sub (kernelCLM k C hkm hC0 hkb μ μ u)
      ((c * inner ℝ u (KernelGap.vac (μ := μ) hφm hφb)) • KernelGap.vac (μ := μ) hφm hφb),
    Lp.coeFn_smul (c * inner ℝ u (KernelGap.vac (μ := μ) hφm hφb))
      (KernelGap.vac (μ := μ) hφm hφb),
    (KernelGap.memLp_φ (μ := μ) hφm hφb).coeFn_toLp] with x h1 h2 h3 h4 h5
  rw [h1, h3, Pi.sub_apply, h2, h4, Pi.smul_apply, smul_eq_mul, KernelGap.inner_vac hφm hφb]
  change kernelFun (rem k c φ) μ (u : X → ℝ) x = kernelFun k μ (u : X → ℝ) x -
    c * (∫ y, φ y * (u : X → ℝ) y ∂μ) *
      (((KernelGap.memLp_φ (μ := μ) hφm hφb).toLp φ : Lp ℝ 2 μ) : X → ℝ) x
  rw [h5]
  unfold kernelFun rem
  have hφu : Integrable (fun y => φ y * (u : X → ℝ) y) μ :=
    integrable_row_mul (K := fun (_ : X) y => φ y) (hφm.comp measurable_snd)
      (fun _ y => hφb y) hu1 x
  have e : (fun y => (k x y - c * φ x * φ y) * (u : X → ℝ) y) =
      fun y => k x y * (u : X → ℝ) y - (c * φ x) * (φ y * (u : X → ℝ) y) := by
    funext y; ring
  rw [e, integral_sub (integrable_row_mul hkm hkb hu1 x) (hφu.const_mul _), integral_const_mul]
  ring

include hkm hkb hsym hφm hφb hφ1 heig in
/-- `R` is positive semidefinite when `K` is. -/
theorem rem_form_nonneg (hKpsd : ∀ u : Lp ℝ 2 μ, 0 ≤ inner ℝ u (kernelCLM k C hkm hC0 hkb μ μ u))
    (u : Lp ℝ 2 μ) : 0 ≤ inner ℝ u (kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ u) := by
  have hK := (SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm k C hkm hC0 hkb μ hsym).isSymmetric
  have h := form_sub_nonneg (A := kernelCLM k C hkm hC0 hkb μ μ) (fun u w => hK u w) hKpsd
    (KernelGap.K_vac hkm hC0 hkb hφm hφb heig) (KernelGap.norm_vac hφm hφb hφ1) u
  rw [rem_apply hkm hC0 hkb hφm hφb hrm hCr0 hrb u, inner_sub_right, real_inner_smul_right,
    real_inner_comm (KernelGap.vac (μ := μ) hφm hφb) u] at *
  nlinarith [h]

include hrm hrb in
/-- The column `y ↦ r(y, x)` in `L²`. -/
noncomputable def col (x : X) : Lp ℝ 2 μ :=
  (MemLp.of_bound (f := fun y => rem k c φ y x)
    (hrm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable Cr
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hrb y x)).toLp _

include hrm hrb in
theorem coeFn_col (x : X) :
    ((col (μ := μ) hrm hrb x : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] fun y => rem k c φ y x :=
  MemLp.coeFn_toLp _

include hrm hrb in
/-- `r^{∗(i+3)}(x, x) = ⟪R^{i+1} r(·, x), r(·, x)⟫` for symmetric `r`. -/
theorem iter_diag_eq (hrs : ∀ x y, rem k c φ x y = rem k c φ y x) (i : ℕ) (x : X) :
    iter μ (rem k c φ) (i + 2) x x =
      inner ℝ (((kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ) ^ (i + 1))
          (col (μ := μ) hrm hrb x)) (col (μ := μ) hrm hrb x) := by
  have hr : Bdd (rem k c φ) := ⟨hrm, Cr, hrb⟩
  rw [SlabTransferAdjoint.real_inner_Lp]
  have hpow := KernelGap.opPow_coe hrm hCr0 hrb (col (μ := μ) hrm hrb x) i
  have hcol := coeFn_col (μ := μ) hrm hrb x
  have e : ∀ y, kernelFun (iter μ (rem k c φ) i) μ
      ((col (μ := μ) hrm hrb x : Lp ℝ 2 μ) : X → ℝ) y =
      iter μ (rem k c φ) (i + 1) y x := by
    intro y
    rw [kernelFun_congr hcol y]
    have ea := iter_add (μ := μ) hr i 0
    simp only [Nat.add_zero] at ea
    rw [ea]
    rfl
  calc iter μ (rem k c φ) (i + 2) x x
      = ∫ y, iter μ (rem k c φ) (i + 1) y x * rem k c φ y x ∂μ := by
        change ∫ y, rem k c φ x y * iter μ (rem k c φ) (i + 1) y x ∂μ = _
        congr 1; funext y; rw [hrs x y, mul_comm]
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hpow, hcol] with y h1 h2
        rw [h1, h2, e y]

include hkm hkb hsym hφm hφb hφ1 heig in
/-- `t = ∫ r^{∗(2j+1)}(x, x) dx ≥ 0` and `‖r^{∗(2j+1)}‖²_HS ≤ ‖R‖^{2j+1} t`. -/
theorem trace_rem_nonneg_and_hs_le
    (hKpsd : ∀ u : Lp ℝ 2 μ, 0 ≤ inner ℝ u (kernelCLM k C hkm hC0 hkb μ μ u)) (j : ℕ)
    (hj : 1 ≤ j) :
    0 ≤ ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ ∧
      hs μ (iter μ (rem k c φ) (2 * j)) ≤
        ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ^ (2 * j + 1) *
          ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ := by
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hr : Bdd (rem k c φ) := ⟨hrm, Cr, hrb⟩
  have hRA := (SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm (rem k c φ) Cr hrm hCr0 hrb μ
    hrs).isSymmetric
  have hRpsd := rem_form_nonneg hkm hC0 hkb hsym hφm hφb hφ1 heig hrm hCr0 hrb hKpsd
  have d2 : ∀ x, iter μ (rem k c φ) (2 * j) x x =
      inner ℝ (((kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ) ^ (2 * j - 1))
        (col (μ := μ) hrm hrb x)) (col (μ := μ) hrm hrb x) := by
    intro x
    have h := iter_diag_eq (μ := μ) hrm hCr0 hrb hrs (2 * j - 2) x
    rwa [show 2 * j - 2 + 2 = 2 * j by omega, show 2 * j - 2 + 1 = 2 * j - 1 by omega] at h
  have d4 : ∀ x, iter μ (rem k c φ) (4 * j + 1) x x =
      inner ℝ (((kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ) ^ (2 * j - 1 + (2 * j + 1)))
        (col (μ := μ) hrm hrb x)) (col (μ := μ) hrm hrb x) := by
    intro x
    have h := iter_diag_eq (μ := μ) hrm hCr0 hrb hrs (4 * j - 1) x
    rwa [show 4 * j - 1 + 2 = 4 * j + 1 by omega,
      show 4 * j - 1 + 1 = 2 * j - 1 + (2 * j + 1) by omega] at h
  have ht : 0 ≤ ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ :=
    integral_nonneg fun x => by rw [d2 x]; exact inner_pow_nonneg (fun u w => hRA u w) hRpsd _ _
  refine ⟨ht, ?_⟩
  have hhs : hs μ (iter μ (rem k c φ) (2 * j)) = ∫ x, iter μ (rem k c φ) (4 * j + 1) x x ∂μ := by
    have ea := iter_add (μ := μ) hr (2 * j) (2 * j)
    rw [show 2 * j + 2 * j + 1 = 4 * j + 1 by ring] at ea
    rw [ea]
    unfold hs conv
    congr 1; funext x; congr 1; funext z
    rw [iter_symm hr hrs (2 * j) z x, sq]
  rw [hhs, ← integral_const_mul]
  refine integral_mono (FluxSectorBound.idiag (hr.iter (μ := μ) (4 * j + 1)))
    ((FluxSectorBound.idiag (hr.iter (μ := μ) (2 * j))).const_mul _) fun x => ?_
  dsimp only
  rw [d4 x, d2 x]
  exact inner_pow_add_le (fun u w => hRA u w) hRpsd (2 * j - 1) _ (2 * j + 1)

include hkm hkb hsym hφm hφb hφ1 heig in
/-- **`ψ_{2j+1} ≥ 0`** for a positive semidefinite kernel operator with `‖R‖ ≤ c`. -/
theorem defect_odd_nonneg
    (hKpsd : ∀ u : Lp ℝ 2 μ, 0 ≤ inner ℝ u (kernelCLM k C hkm hC0 hkb μ μ u)) (hcpos : 0 < c)
    (hRc : ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ c) (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ DoublingPower.defect (cyc μ k) (2 * j + 1) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  obtain ⟨ht, hhs⟩ :=
    trace_rem_nonneg_and_hs_le hkm hC0 hkb hsym hφm hφb hφ1 heig hrm hCr0 hrb hKpsd j hj
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hRc (2 * j + 1)
  have hhs' := hhs.trans (mul_le_mul_of_nonneg_right hpow ht)
  have h1 := PurityOddTime.cyc_odd hk hsym hφm hφb hφ1 heig j
  have h2 := cyc_even (μ := μ) hk hsym (2 * j + 1) (by omega)
  have h3 := hs_iter_decomp hk hsym hφm hφb hφ1 heig (2 * j)
  unfold traceSeq at h2
  rw [show 2 * (2 * j + 1) / 2 - 1 = 2 * j by omega, h3] at h2
  have hcT : 0 < c ^ (2 * j + 1) := pow_pos hcpos _
  have hh0 := hs_nonneg (μ := μ) (iter μ (rem k c φ) (2 * j))
  have eY : c ^ (2 * (2 * j + 1)) = (c ^ (2 * j + 1)) ^ 2 := by
    rw [show 2 * (2 * j + 1) = (2 * j + 1) * 2 by ring, pow_mul]
  unfold DoublingPower.defect
  rw [h2, h1, eY]
  have hX : 0 < c ^ (2 * j + 1) + ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ := by linarith
  have hY : 0 < (c ^ (2 * j + 1)) ^ 2 + hs μ (iter μ (rem k c φ) (2 * j)) := by positivity
  have hle : (c ^ (2 * j + 1)) ^ 2 + hs μ (iter μ (rem k c φ) (2 * j)) ≤
      (c ^ (2 * j + 1) + ∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ) ^ 2 := by
    nlinarith [mul_nonneg hcT.le ht, sq_nonneg (∫ x, iter μ (rem k c φ) (2 * j) x x ∂μ)]
  have hl := log_le_log hY hle
  rw [log_pow] at hl
  push_cast at hl
  linarith

end Kernel

/-! ## The Wilson transfer kernel -/

section Wilson

open MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.GaugeGroup MassGap.PurityHaarProjection

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- The Wilson transfer operator is positive semidefinite on `L²`. -/
theorem kTG_form_nonneg {β : ℝ} (hβ : 0 ≤ β) (u : Lp ℝ 2 (hSG G μ T)) :
    0 ≤ inner ℝ u (kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
      (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T) u) := by
  have hu1 : Integrable (u : (SpT μ T → G) → ℝ) (hSG G μ T) :=
    (Lp.memLp u).integrable one_le_two
  rw [SlabTransferAdjoint.real_inner_Lp]
  refine (PurityKernelPositive.kTG_quad_nonneg (G := G) (μ := μ) (T := T) hβ hu1).trans_eq
    (integral_congr_ae ?_)
  filter_upwards [coeFn_kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (hSG G μ T) (hSG G μ T) u] with x hx
  rw [hx, mul_comm]
  rfl

/-- **`ψ_{2j+1} ≥ 0` for the Wilson transfer kernel**, `j ≥ 1`. -/
theorem defect_odd_nonneg_kTG [Nontrivial G] {β : ℝ} (hβ : 0 < β) (hT : ∀ j, 2 ≤ T j) (j : ℕ)
    (hj : 1 ≤ j) : 0 ≤ DoublingPower.defect (cyc (hSG G μ T) (kTG G μ T β)) (2 * j + 1) := by
  obtain ⟨hpos, φ, hφc, -, hφb, hφ1, heig, hR⟩ :=
    PurityRectWilsonFixed.norm_rem_le (G := G) (μ := μ) (T := T) hβ hT
  have hk : Bdd (kTG G μ T β) := bdd_kTG hβ.le
  have hφm := hφc.measurable
  have hr := hk.rem (c := ‖kernelCLM (kTG G μ T β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ.le) (hSG G μ T) (hSG G μ T)‖) hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hCr (fun _ => 1) (fun _ => 1))
  have hRc := (hR Cr hr.meas hCr0 hCr).trans
    (mul_le_of_le_one_left (norm_nonneg _) (PurityWilson.tanh_lt_one _).le)
  exact defect_odd_nonneg (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ.le)
    (kTG_symm β) hφm hφb hφ1 heig hr.meas hCr0 hCr (kTG_form_nonneg hβ.le) hpos hRc j hj

/-- **`ψ_{2j+1} ≥ 0` for the Wilson partition function.** For a nontrivial gauge group, time
extents `L μ = 2j + 1` and `L' μ = 2(2j + 1)`, `j ≥ 1`, the same spatial extents, each at least
`2`, and `β > 0`, `log Z(L') ≤ 2 log Z(L)`. -/
theorem ZRG_defect_odd_nonneg [Nontrivial G] {β : ℝ} (hβ : 0 < β) {L L' : Fin 4 → ℕ}
    (hT : ∀ ν : {j : Fin 4 // j ≠ μ}, 2 ≤ L ν.1) (htr : tr L' μ = tr L μ) (j : ℕ) (hj : 1 ≤ j)
    (hL : L μ = 2 * j + 1) (hL' : L' μ = 2 * (2 * j + 1)) :
    log (ZRG G L' β) ≤ 2 * log (ZRG G L β) := by
  have h := defect_odd_nonneg_kTG (G := G) (T := tr L μ) hβ hT j hj
  have h1 := ZRG_eq_cyc (G := G) (μ := μ) (L := L) β
  have h2 := ZRG_eq_cyc (G := G) (μ := μ) (L := L') β
  rw [htr, hL'] at h2
  rw [hL] at h1
  unfold DoublingPower.defect at h
  rw [h1, h2]
  linarith

end Wilson

end MassGap.PurityOddTimeLower

#print axioms MassGap.PurityOddTimeLower.inner_pow_add
#print axioms MassGap.PurityOddTimeLower.norm_sq_le_form
#print axioms MassGap.PurityOddTimeLower.inner_pow_succ_le_and_nonneg
#print axioms MassGap.PurityOddTimeLower.inner_pow_add_le
#print axioms MassGap.PurityOddTimeLower.form_sub_nonneg
#print axioms MassGap.PurityOddTimeLower.rem_apply
#print axioms MassGap.PurityOddTimeLower.rem_form_nonneg
#print axioms MassGap.PurityOddTimeLower.iter_diag_eq
#print axioms MassGap.PurityOddTimeLower.trace_rem_nonneg_and_hs_le
#print axioms MassGap.PurityOddTimeLower.defect_odd_nonneg
#print axioms MassGap.PurityOddTimeLower.kTG_form_nonneg
#print axioms MassGap.PurityOddTimeLower.defect_odd_nonneg_kTG
#print axioms MassGap.PurityOddTimeLower.ZRG_defect_odd_nonneg
