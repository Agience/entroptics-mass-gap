import Mathlib
import MassGap.KernelPower
import MassGap.TransferGap

/-!
# MassGap.KernelGap — the transfer gap of a symmetric kernel operator from its trace facts

`K` is the `L²(μ)` operator of a bounded measurable symmetric kernel `k`, and `φ` a normalised
eigenfunction, `∫ k(z,y)φ(y) = c φ(z)` with `|c| = ‖K‖ > 0`. `vac = φ` in `L²`.

* `opPow_coe` — `K^(i+1) f` is the iterated kernel `k^{∗(i+1)}` applied to `f`, a.e.
* `norm_opPow_sq_le` — for `f ⊥ vac` and `j ≥ 1`: `‖K^j f‖² ≤ hs(r^{∗j}) ‖f‖²`, with `r = k − cφ⊗φ`.
* `root_extract` — on a real inner product space, for `T` self-adjoint with `T v = c v` and
  `‖T^h g‖² ≤ S‖g‖²` on `v⊥`: `‖T^n f‖^(2^k) ≤ S ‖f‖^(2^k)` on `v⊥` whenever `2h = 2^k n`.
* `gap_of_excited` — if the relative excited weight at `m = 2^k n` (`n` even) is at most
  `(1/2)^(2^k)`, then `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` for every `f ⊥ vac`.
* `transferData`, `gapAt_half` — the normalised `n`-step transfer `‖K‖^{-n} K^n` with vacuum `vac`
  as a `Transfer.TransferData` on `L²`, and `TransferGap.GapAt` at `r = 1/2` for it.
-/

namespace MassGap.KernelGap

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-! ## Root extraction on an inner product space -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pow_symm {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w)) :
    ∀ (p : ℕ) (u w : E), inner ℝ ((T ^ p) u) w = inner ℝ u ((T ^ p) w)
  | 0, u, w => by simp
  | p + 1, u, w => by
    rw [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, pow_symm hT p, hT]
    congr 1
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← pow_succ', ← pow_succ]

theorem norm_pow_sq_le {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    (p : ℕ) (f : E) : ‖(T ^ p) f‖ ^ 2 ≤ ‖f‖ * ‖(T ^ (2 * p)) f‖ := by
  rw [← real_inner_self_eq_norm_sq ((T ^ p) f), pow_symm hT, ← ContinuousLinearMap.mul_apply, ← pow_add,
    show p + p = 2 * p by ring]
  exact real_inner_le_norm f ((T ^ (2 * p)) f)

theorem norm_pow_chain {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    (n : ℕ) (f : E) : ∀ i : ℕ, ‖(T ^ n) f‖ ^ (2 ^ i) ≤ ‖f‖ ^ (2 ^ i - 1) * ‖(T ^ (2 ^ i * n)) f‖
  | 0 => by simp
  | i + 1 => by
    have IH := norm_pow_chain hT n f i
    have h1 := norm_pow_sq_le hT (2 ^ i * n) f
    have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    calc ‖(T ^ n) f‖ ^ (2 ^ (i + 1)) = (‖(T ^ n) f‖ ^ (2 ^ i)) ^ 2 := by
          rw [← pow_mul, pow_succ]
      _ ≤ (‖f‖ ^ (2 ^ i - 1) * ‖(T ^ (2 ^ i * n)) f‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) IH 2
      _ = ‖f‖ ^ (2 * (2 ^ i - 1)) * ‖(T ^ (2 ^ i * n)) f‖ ^ 2 := by rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ ‖f‖ ^ (2 * (2 ^ i - 1)) * (‖f‖ * ‖(T ^ (2 * (2 ^ i * n))) f‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖f‖ ^ (2 ^ (i + 1) - 1) * ‖(T ^ (2 ^ (i + 1) * n)) f‖ := by
          have e1 : 2 * (2 ^ i * n) = 2 ^ (i + 1) * n := by ring
          have e2 : 2 ^ (i + 1) - 1 = 2 * (2 ^ i - 1) + 1 := by
            rw [pow_succ]; omega
          rw [e1, e2, pow_succ]; ring

theorem norm_pow_apply_le (T : E →L[ℝ] E) (u : E) : ∀ n : ℕ, ‖(T ^ n) u‖ ≤ ‖T‖ ^ n * ‖u‖
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ', ContinuousLinearMap.mul_apply, pow_succ']
    calc ‖T ((T ^ n) u)‖ ≤ ‖T‖ * ‖(T ^ n) u‖ := T.le_opNorm _
      _ ≤ ‖T‖ * (‖T‖ ^ n * ‖u‖) := mul_le_mul_of_nonneg_left (norm_pow_apply_le T u n) (norm_nonneg _)
      _ = ‖T‖ * ‖T‖ ^ n * ‖u‖ := by ring

theorem orth_pow {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w)) {v : E} {c : ℝ}
    (hv : T v = c • v) (p : ℕ) {f : E} (hf : inner ℝ f v = 0) : inner ℝ ((T ^ p) f) v = 0 := by
  have hvp : (T ^ p) v = c ^ p • v := by
    induction p with
    | zero => simp
    | succ p ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hv, smul_smul,
        pow_succ]
  rw [pow_symm hT, hvp, inner_smul_right, hf, mul_zero]

theorem root_extract {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w)) {v : E}
    {c : ℝ} (hv : T v = c • v) {h : ℕ} {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ g : E, inner ℝ g v = 0 → ‖(T ^ h) g‖ ^ 2 ≤ S * ‖g‖ ^ 2) {k n : ℕ}
    (hkn : 2 * h = 2 ^ k * n) {f : E} (hf : inner ℝ f v = 0) :
    ‖(T ^ n) f‖ ^ (2 ^ k) ≤ S * ‖f‖ ^ (2 ^ k) := by
  have hchain := norm_pow_chain hT n f k
  have h2 : ‖(T ^ (2 * h)) f‖ ≤ S * ‖f‖ := by
    have hf' := orth_pow hT hv h hf
    have a1 := hS _ hf'
    have a2 := hS f hf
    rw [two_mul, pow_add, ContinuousLinearMap.mul_apply] at *
    have : ‖(T ^ h) ((T ^ h) f)‖ ^ 2 ≤ (S * ‖f‖) ^ 2 := by
      calc _ ≤ S * ‖(T ^ h) f‖ ^ 2 := a1
        _ ≤ S * (S * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left a2 hS0
        _ = (S * ‖f‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  rw [hkn] at h2
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  calc ‖(T ^ n) f‖ ^ (2 ^ k) ≤ ‖f‖ ^ (2 ^ k - 1) * ‖(T ^ (2 ^ k * n)) f‖ := hchain
    _ ≤ ‖f‖ ^ (2 ^ k - 1) * (S * ‖f‖) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = S * ‖f‖ ^ (2 ^ k - 1 + 1) := by rw [pow_succ]; ring
    _ = S * ‖f‖ ^ (2 ^ k) := by rw [Nat.sub_add_cancel hpos]

end Abstract

/-! ## The kernel operator -/

section Kernel

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C)

include hkm hC0 hkb in
/-- `K^(i+1) f` is `k^{∗(i+1)}` applied to `f`. -/
theorem opPow_coe (f : Lp ℝ 2 μ) : ∀ i : ℕ,
    (((kernelCLM k C hkm hC0 hkb μ μ) ^ (i + 1)) f : X → ℝ) =ᵐ[μ] kernelFun (iter μ k i) μ f
  | 0 => by simpa [iter] using coeFn_kernelCLM k C hkm hC0 hkb μ μ f
  | i + 1 => by
    have IH := opPow_coe f i
    have hk : Bdd k := ⟨hkm, C, hkb⟩
    have hki := hk.iter (μ := μ) i
    obtain ⟨Ci, hCi⟩ := hki.bdd
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    filter_upwards [coeFn_kernelCLM k C hkm hC0 hkb μ μ (((kernelCLM k C hkm hC0 hkb μ μ) ^ (i + 1)) f)]
      with x hx
    rw [hx, kernelFun_congr IH x]
    -- Fubini
    have hf1 : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
    have hfm : Measurable (f : X → ℝ) := (Lp.stronglyMeasurable f).measurable
    have hF : Integrable (Function.uncurry (fun y z => k x y * (iter μ k i y z * (f : X → ℝ) z)))
        (μ.prod μ) := by
      refine Integrable.mono' ((hf1.norm.comp_snd μ).const_mul (C * Ci)) ?_ ?_
      · exact (((hk.row x).comp measurable_fst).mul
          (hki.meas.mul (hfm.comp measurable_snd))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun p => ?_
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        have h0 : 0 ≤ C := hC0
        have h1 : 0 ≤ Ci := (abs_nonneg _).trans (hCi p.1 p.2)
        calc |k x p.1| * (|iter μ k i p.1 p.2| * |(f : X → ℝ) p.2|)
            ≤ C * (Ci * |(f : X → ℝ) p.2|) :=
              mul_le_mul (hkb x p.1) (mul_le_mul_of_nonneg_right (hCi p.1 p.2) (abs_nonneg _))
                (by positivity) h0
          _ = C * Ci * |(f : X → ℝ) p.2| := by ring
    unfold kernelFun
    calc ∫ y, k x y * (∫ z, iter μ k i y z * (f : X → ℝ) z ∂μ) ∂μ
        = ∫ y, ∫ z, k x y * (iter μ k i y z * (f : X → ℝ) z) ∂μ ∂μ := by
          congr 1; funext y; rw [integral_const_mul]
      _ = ∫ z, ∫ y, k x y * (iter μ k i y z * (f : X → ℝ) z) ∂μ ∂μ :=
          integral_integral_swap hF
      _ = ∫ z, iter μ k (i + 1) x z * (f : X → ℝ) z ∂μ := by
          congr 1; funext z
          change _ = (∫ y, k x y * iter μ k i y z ∂μ) * (f : X → ℝ) z
          rw [← integral_mul_const]; congr 1; funext y; ring

/-- `∫ (∫ h(x,y) f(y))² ≤ hs h · ‖f‖²`. -/
theorem integral_kernelFun_sq_le {h : X → X → ℝ} (hh : Bdd h) (f : Lp ℝ 2 μ) :
    ∫ x, kernelFun h μ (f : X → ℝ) x ^ 2 ∂μ ≤ hs μ h * ‖f‖ ^ 2 := by
  obtain ⟨Ch, hCh⟩ := hh.bdd
  have hCh0 : ∀ x y, |h x y| ^ 2 ≤ Ch ^ 2 := fun x y => pow_le_pow_left₀ (abs_nonneg _) (hCh x y) 2
  have hf2 : Integrable (fun y => (f : X → ℝ) y ^ 2) μ := (Lp.memLp f).integrable_sq
  have hf1 : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
  have hnf : ‖f‖ ^ 2 = ∫ y, (f : X → ℝ) y ^ 2 ∂μ := norm_sq_eq_integral f
  have hpt : ∀ x, kernelFun h μ (f : X → ℝ) x ^ 2 ≤ (∫ y, h x y ^ 2 ∂μ) * ‖f‖ ^ 2 := by
    intro x
    rw [hnf]
    exact sq_integral_mul_le
      (integrable_of_bdd ((hh.row x).pow_const 2) (fun y => by rw [abs_pow]; exact hCh0 x y))
      hf2 (integrable_row_mul hh.meas hCh hf1 x)
  rw [hs, ← integral_mul_const]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_
    (Filter.Eventually.of_forall hpt)
  exact (integrable_of_bdd (measurable_integral_right (hh.meas.pow_const 2)) (C := Ch ^ 2)
    (fun x => abs_integral_le fun y => by rw [abs_pow]; exact hCh0 x y)).mul_const _

end Kernel

section Eigen

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hφm hφb in
theorem memLp_φ : MemLp φ 2 μ :=
  MemLp.of_bound hφm.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hφb x)

/-- The vacuum: `φ` as an `L²` vector. -/
noncomputable def vac (hφm : Measurable φ) (hφb : ∀ x, |φ x| ≤ B) : Lp ℝ 2 μ :=
  (memLp_φ (μ := μ) hφm hφb).toLp φ

include hφ1 in
theorem norm_vac : ‖vac (μ := μ) hφm hφb‖ = 1 := by
  have h := norm_sq_eq_integral (vac (μ := μ) hφm hφb)
  have : ∫ x, ((vac (μ := μ) hφm hφb : Lp ℝ 2 μ) : X → ℝ) x ^ 2 ∂μ = 1 := by
    rw [← hφ1]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_φ (μ := μ) hφm hφb).coeFn_toLp] with x hx
    unfold vac; rw [hx]
  rw [this] at h
  nlinarith [norm_nonneg (vac (μ := μ) hφm hφb), sq_nonneg (‖vac (μ := μ) hφm hφb‖ - 1)]

theorem inner_vac (f : Lp ℝ 2 μ) :
    inner ℝ f (vac (μ := μ) hφm hφb) = ∫ y, φ y * (f : X → ℝ) y ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_φ (μ := μ) hφm hφb).coeFn_toLp] with y hy
  unfold vac; rw [hy]; simp [mul_comm]

include heig in
theorem K_vac : kernelCLM k C hkm hC0 hkb μ μ (vac (μ := μ) hφm hφb) = c • vac (μ := μ) hφm hφb := by
  apply Lp.ext
  filter_upwards [coeFn_kernelCLM k C hkm hC0 hkb μ μ (vac (μ := μ) hφm hφb),
    Lp.coeFn_smul c (vac (μ := μ) hφm hφb), (memLp_φ (μ := μ) hφm hφb).coeFn_toLp] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, smul_eq_mul]
  change kernelFun k μ (((memLp_φ (μ := μ) hφm hφb).toLp φ : Lp ℝ 2 μ) : X → ℝ) z
    = c * (((memLp_φ (μ := μ) hφm hφb).toLp φ : Lp ℝ 2 μ) : X → ℝ) z
  rw [h3, kernelFun_congr (memLp_φ (μ := μ) hφm hφb).coeFn_toLp z]
  exact heig z

include hkm hC0 hkb hsym hφ1 heig in
/-- `‖K^j f‖² ≤ hs(r^{∗j}) ‖f‖²` for `f ⊥ vac`, `j ≥ 1`. -/
theorem norm_opPow_sq_le (j : ℕ) (hj : 1 ≤ j) (f : Lp ℝ 2 μ)
    (hf : inner ℝ f (vac (μ := μ) hφm hφb) = 0) :
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ j) f‖ ^ 2
      ≤ hs μ (iter μ (rem k c φ) (j - 1)) * ‖f‖ ^ 2 := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hcoe := opPow_coe hkm hC0 hkb f (j - 1)
  rw [hj'] at hcoe
  have hf0 : ∫ y, φ y * (f : X → ℝ) y ∂μ = 0 := by rw [← inner_vac hφm hφb f]; exact hf
  have hf1 : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
  have hrj := hr.iter (μ := μ) (j - 1)
  obtain ⟨Cr, hCr⟩ := hrj.bdd
  have hpt : ∀ x, kernelFun (iter μ k (j - 1)) μ (f : X → ℝ) x
      = kernelFun (iter μ (rem k c φ) (j - 1)) μ (f : X → ℝ) x := by
    intro x
    unfold kernelFun
    have e : (fun y => iter μ k (j - 1) x y * (f : X → ℝ) y)
        = fun y => (c ^ (j - 1 + 1) * φ x) * (φ y * (f : X → ℝ) y)
          + iter μ (rem k c φ) (j - 1) x y * (f : X → ℝ) y := by
      funext y; rw [iter_decomp hk hsym hφm hφb hφ1 heig (j - 1) x y]; ring
    have i1 : Integrable (fun y => φ y * (f : X → ℝ) y) μ := by
      have := hf1.bdd_mul (c := B) hφm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hφb y)
      simpa using this
    have i2 : Integrable (fun y => iter μ (rem k c φ) (j - 1) x y * (f : X → ℝ) y) μ :=
      integrable_row_mul hrj.meas hCr hf1 x
    have j1 : Integrable (fun y => (c ^ (j - 1 + 1) * φ x) * (φ y * (f : X → ℝ) y)) μ :=
      i1.const_mul _
    rw [e, integral_add j1 i2, integral_const_mul, hf0, mul_zero, zero_add]
  rw [norm_sq_eq_integral]
  calc ∫ x, ((((kernelCLM k C hkm hC0 hkb μ μ) ^ j) f : Lp ℝ 2 μ) : X → ℝ) x ^ 2 ∂μ
      = ∫ x, kernelFun (iter μ (rem k c φ) (j - 1)) μ (f : X → ℝ) x ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx, hpt]
    _ ≤ _ := integral_kernelFun_sq_le hrj f

variable (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) (hc0 : c ≠ 0)

include hkm hC0 hkb hsym hφ1 heig hnorm hc0 in
/-- The gap. If at `m = 2^k n` (`n` even, positive) the relative excited weight is at most
`(1/2)^(2^k)`, then `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` on the vacuum complement. -/
theorem gap_of_excited (q n : ℕ) (hn : 0 < n) (hne : Even n)
    (hexc : excited μ k c φ (2 ^ q * n / 2) ≤ (1 / 2) ^ (2 ^ q)) (f : Lp ℝ 2 μ)
    (hf : inner ℝ f (vac (μ := μ) hφm hφb) = 0) :
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖ ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖ := by
  set K := kernelCLM k C hkm hC0 hkb μ μ
  set lam := ‖K‖
  have hl : 0 < lam := by rw [← hnorm]; exact abs_pos.mpr hc0
  obtain ⟨n', rfl⟩ := hne
  set h := 2 ^ q * (n' + n') / 2 with hh
  have hh2 : 2 * h = 2 ^ q * (n' + n') := by
    rw [hh]; have : 2 ^ q * (n' + n') = 2 * (2 ^ q * n') := by ring
    rw [this]; omega
  have hh1 : 1 ≤ h := by
    have : 1 ≤ n' := by omega
    have : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    rw [hh]; have e : 2 ^ q * (n' + n') = 2 * (2 ^ q * n') := by ring
    rw [e]; simp only [Nat.mul_div_cancel_left _ two_pos]; nlinarith
  have hsym' : ∀ u w, inner ℝ (K u) w = inner ℝ u (K w) := fun u w =>
    (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm k C hkm hC0 hkb μ hsym).isSymmetric u w
  have hv := K_vac hkm hC0 hkb hφm hφb heig
  set S := hs μ (iter μ (rem k c φ) (h - 1)) with hSdef
  have hS0 : 0 ≤ S := hs_nonneg _
  have hS : ∀ g : Lp ℝ 2 μ, inner ℝ g (vac (μ := μ) hφm hφb) = 0 → ‖(K ^ h) g‖ ^ 2 ≤ S * ‖g‖ ^ 2 :=
    fun g hg => norm_opPow_sq_le hkm hC0 hkb hsym hφm hφb hφ1 heig h hh1 g hg
  have hroot := root_extract hsym' hv hS0 hS hh2 hf
  -- `S = excited · λ^{2h}`
  have hSe : S = excited μ k c φ h * lam ^ (2 * h) := by
    rw [hSdef]; unfold excited; rw [hnorm]; field_simp
  have hpowq : 0 < 2 ^ q := Nat.two_pow_pos q
  have hlam_pow : lam ^ (2 * h) = (lam ^ (n' + n')) ^ (2 ^ q) := by
    rw [← pow_mul, hh2, mul_comm]
  have key : ‖(K ^ (n' + n')) f‖ ^ (2 ^ q) ≤ (1 / 2 * lam ^ (n' + n') * ‖f‖) ^ (2 ^ q) := by
    calc ‖(K ^ (n' + n')) f‖ ^ (2 ^ q) ≤ S * ‖f‖ ^ (2 ^ q) := hroot
      _ = excited μ k c φ h * (lam ^ (n' + n')) ^ (2 ^ q) * ‖f‖ ^ (2 ^ q) := by
          rw [hSe, hlam_pow]
      _ ≤ (1 / 2) ^ (2 ^ q) * (lam ^ (n' + n')) ^ (2 ^ q) * ‖f‖ ^ (2 ^ q) := by
          gcongr
      _ = (1 / 2 * lam ^ (n' + n') * ‖f‖) ^ (2 ^ q) := by rw [mul_pow, mul_pow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hpowq.ne').mp key


include hkm hC0 hkb hsym hφ1 heig hnorm hc0 in
/-- The normalised `n`-step transfer `‖K‖^{-n} K^n` on `L²`, with vacuum `vac`, as a
`Transfer.TransferData` (`n` even). -/
noncomputable def transferData (n : ℕ) (hne : Even n) :
    MassGap.Transfer.TransferData (Lp ℝ 2 μ) where
  form u w := inner ℝ u w
  form_symm u w := real_inner_comm w u
  form_add_left u w z := inner_add_left u w z
  form_smul_left r u w := real_inner_smul_left u w r
  form_nonneg u := real_inner_self_nonneg
  T := ((‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n)⁻¹ • (kernelCLM k C hkm hC0 hkb μ μ) ^ n :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ).toLinearMap
  vac := vac (μ := μ) hφm hφb
  T_symm u w := by
    have hsym' : ∀ u w, inner ℝ (kernelCLM k C hkm hC0 hkb μ μ u) w
        = inner ℝ u (kernelCLM k C hkm hC0 hkb μ μ w) := fun u w =>
      (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm k C hkm hC0 hkb μ hsym).isSymmetric u w
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_smul_right]
    rw [pow_symm hsym']
  T_contract u := by
    set K := kernelCLM k C hkm hC0 hkb μ μ
    have hl : 0 < ‖K‖ := by rw [← hnorm]; exact abs_pos.mpr hc0
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h1 : ‖(K ^ n) u‖ ≤ ‖K‖ ^ n * ‖u‖ := norm_pow_apply_le K u n
    have hp : 0 < ‖K‖ ^ n := pow_pos hl n
    have h2 : ‖(K ^ n) u‖ ^ 2 ≤ (‖K‖ ^ n) ^ 2 * ‖u‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hp, inv_pow,
      inv_mul_le_iff₀ (by positivity)]
    exact h2
  T_vac := by
    set K := kernelCLM k C hkm hC0 hkb μ μ
    have hl : 0 < ‖K‖ := by rw [← hnorm]; exact abs_pos.mpr hc0
    have hv := K_vac hkm hC0 hkb hφm hφb heig
    have hvp : (K ^ n) (vac (μ := μ) hφm hφb) = c ^ n • vac (μ := μ) hφm hφb := by
      clear hne
      induction n with
      | zero => simp
      | succ p ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hv, smul_smul,
          pow_succ]
    have hcn : c ^ n = ‖K‖ ^ n := by
      rw [← hnorm]; exact (Even.pow_abs hne c).symm
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, hvp, hcn, smul_smul,
      inv_mul_cancel₀ (pow_pos hl n).ne', one_smul]
  vac_norm := by
    change inner ℝ (vac (μ := μ) hφm hφb) (vac (μ := μ) hφm hφb) = 1
    rw [real_inner_self_eq_norm_sq, norm_vac hφm hφb hφ1, one_pow]

include hkm hC0 hkb hsym hφ1 heig hnorm hc0 in
/-- `TransferGap.GapAt` at `r = 1/2` for the normalised `n`-step transfer. -/
theorem gapAt_half (q n : ℕ) (hn : 0 < n) (hne : Even n)
    (hexc : excited μ k c φ (2 ^ q * n / 2) ≤ (1 / 2) ^ (2 ^ q)) :
    MassGap.TransferGap.GapAt
      (transferData hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 n hne) (1 / 2) := by
  intro f hf
  set K := kernelCLM k C hkm hC0 hkb μ μ
  have hl : 0 < ‖K‖ := by rw [← hnorm]; exact abs_pos.mpr hc0
  have hg := gap_of_excited hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 q n hn hne hexc f hf
  change inner ℝ ((‖K‖ ^ n)⁻¹ • (K ^ n) f) ((‖K‖ ^ n)⁻¹ • (K ^ n) f) ≤ (1 / 2) ^ 2 * inner ℝ f f
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, ← mul_assoc, ← mul_inv, ← sq]
  have hp : 0 < ‖K‖ ^ n := pow_pos hl n
  rw [inv_mul_le_iff₀ (by positivity)]
  have h2 : ‖(K ^ n) f‖ ^ 2 ≤ (1 / 2 * ‖K‖ ^ n * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg 2
  nlinarith [h2]

end Eigen

#print axioms opPow_coe
#print axioms norm_opPow_sq_le
#print axioms root_extract
#print axioms gap_of_excited
#print axioms gapAt_half

end MassGap.KernelGap
