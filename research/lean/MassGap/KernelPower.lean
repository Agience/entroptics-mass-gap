import Mathlib
import MassGap.SlabTransferAdjoint
import MassGap.DoublingPower

/-!
# MassGap.KernelPower — iterated kernels, Hilbert–Schmidt bounds, and the four trace facts

For a bounded measurable kernel `k` on a probability space `(X, μ)`:

* `conv μ a c x z = ∫ a x y · c y z dμ(y)` and `iter μ k i = k^{∗(i+1)}` (`iter 0 = k`).
* `hs μ h = ∫∫ h(x,z)² dμ dμ`, the squared Hilbert–Schmidt norm of the kernel `h`.

Proved here, with no trace-class or spectral theory:

* `conv_assoc`, `iter_add` — `k^{∗(i+l+2)} = k^{∗(i+1)} ∗ k^{∗(l+1)}` (Fubini on bounded kernels).
* `hs_conv_le_mul` — `hs (a ∗ c) ≤ hs a · hs c` (Cauchy–Schwarz pointwise).
* `hs_conv_le_norm` — `hs (k ∗ c) ≤ ‖K‖² · hs c`, `K` the `L²` operator of `k`.
* `iter_decomp`, `hs_iter_decomp` — given a normalised eigenfunction `φ` of a symmetric `k` with
  eigenvalue `c`, and `r = k − c φ⊗φ`: `k^{∗(i+1)} = c^{i+1} φ⊗φ + r^{∗(i+1)}` pointwise, and
  `hs(k^{∗(i+1)}) = c^{2(i+1)} + hs(r^{∗(i+1)})`.
* `powerFacts` — with `|c| = ‖K‖ > 0` and `a m = hs(k^{∗(m/2)})`, the four trace facts
  `DoublingPower.PowerFacts a |c| s m` hold at every even `m ≥ 2`.
* `opPow_coe`, `norm_opPow_sq_le` — `(K^(i+1) f)` is `k^{∗(i+1)}` applied to `f`, and for `f ⊥ φ`,
  `‖K^j f‖² ≤ hs(r^{∗j}) ‖f‖²`.

`a m` is the cyclic integral of `m` copies of `k` when `m` is even: `∫∫ k^{∗j}(x,z) k^{∗j}(z,x)` is
`hs(k^{∗j})` for symmetric `k`. That identification is made where the lattice supplies `k`.
-/

namespace MassGap.KernelPower

open MeasureTheory Real MassGap.SlabKernelOperator

variable {X : Type*} [MeasurableSpace X]

/-- Kernel composition. -/
noncomputable def conv (μ : Measure X) (a c : X → X → ℝ) : X → X → ℝ :=
  fun x z => ∫ y, a x y * c y z ∂μ

/-- `iter μ k i = k^{∗(i+1)}`. -/
noncomputable def iter (μ : Measure X) (k : X → X → ℝ) : ℕ → X → X → ℝ
  | 0 => k
  | i + 1 => conv μ k (iter μ k i)

/-- Squared Hilbert–Schmidt norm of a kernel. -/
noncomputable def hs (μ : Measure X) (h : X → X → ℝ) : ℝ := ∫ x, ∫ z, h x z ^ 2 ∂μ ∂μ

/-- A bounded jointly measurable kernel. -/
structure Bdd (h : X → X → ℝ) : Prop where
  meas : Measurable (Function.uncurry h)
  bdd : ∃ C, ∀ x y, |h x y| ≤ C

variable {μ : Measure X} [IsProbabilityMeasure μ]

/-! ## Integrability bookkeeping -/

theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {f : α → ℝ} (hm : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) : Integrable f ν :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

theorem measurable_integral_right {F : X → X → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => ∫ y, F x y ∂μ) :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem abs_integral_le {f : X → ℝ} {C : ℝ} (hb : ∀ y, |f y| ≤ C) : |∫ y, f y ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb y)
  simpa [Real.norm_eq_abs] using h

theorem Bdd.row {h : X → X → ℝ} (hh : Bdd h) (x : X) : Measurable (h x) :=
  hh.meas.comp measurable_prodMk_left

theorem Bdd.col {h : X → X → ℝ} (hh : Bdd h) (z : X) : Measurable (fun y => h y z) :=
  hh.meas.comp measurable_prodMk_right

theorem Bdd.add {a c : X → X → ℝ} (ha : Bdd a) (hc : Bdd c) : Bdd (fun x y => a x y + c x y) := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  obtain ⟨Cc, hCc⟩ := hc.bdd
  refine ⟨ha.meas.add hc.meas, Ca + Cc, fun x y => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hCa x y) (hCc x y))

theorem Bdd.conv {a c : X → X → ℝ} (ha : Bdd a) (hc : Bdd c) : Bdd (conv μ a c) := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  obtain ⟨Cc, hCc⟩ := hc.bdd
  refine ⟨?_, Ca * Cc, fun x z => ?_⟩
  · have hm : Measurable (fun p : (X × X) × X => a p.1.1 p.2 * c p.2 p.1.2) :=
      (ha.meas.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hc.meas.comp (measurable_snd.prodMk measurable_fst.snd))
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  · apply abs_integral_le
    intro y
    rw [abs_mul]
    exact mul_le_mul (hCa x y) (hCc y z) (abs_nonneg _) ((abs_nonneg _).trans (hCa x y))

theorem Bdd.iter {k : X → X → ℝ} (hk : Bdd k) : ∀ i, Bdd (iter μ k i)
  | 0 => hk
  | i + 1 => hk.conv (Bdd.iter hk i)

theorem Bdd.mul_swap_integrable {F : X → X → ℝ} (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hb : ∀ x y, |F x y| ≤ C) : Integrable (Function.uncurry F) (μ.prod μ) :=
  integrable_of_bdd hF (fun p => hb p.1 p.2)

theorem swap_bdd {F : X → X → ℝ} (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hb : ∀ x y, |F x y| ≤ C) :
    ∫ x, ∫ y, F x y ∂μ ∂μ = ∫ y, ∫ x, F x y ∂μ ∂μ :=
  integral_integral_swap (Bdd.mul_swap_integrable hF hb)

/-! ## Associativity and powers -/

theorem conv_assoc {a b c : X → X → ℝ} (ha : Bdd a) (hb : Bdd b) (hc : Bdd c) :
    conv μ a (conv μ b c) = conv μ (conv μ a b) c := by
  funext x w
  obtain ⟨Ca, hCa⟩ := ha.bdd
  obtain ⟨Cb, hCb⟩ := hb.bdd
  obtain ⟨Cc, hCc⟩ := hc.bdd
  have hF : Measurable (Function.uncurry (fun y z => a x y * (b y z * c z w))) :=
    ((ha.row x).comp measurable_fst).mul
      (hb.meas.mul ((hc.col w).comp measurable_snd))
  have hFb : ∀ y z, |a x y * (b y z * c z w)| ≤ Ca * (Cb * Cc) := by
    intro y z
    rw [abs_mul, abs_mul]
    have h0a : 0 ≤ Ca := (abs_nonneg _).trans (hCa x y)
    have h0b : 0 ≤ Cb := (abs_nonneg _).trans (hCb y z)
    exact mul_le_mul (hCa x y) (mul_le_mul (hCb y z) (hCc z w) (abs_nonneg _) h0b)
      (by positivity) h0a
  unfold conv
  calc ∫ y, a x y * (∫ z, b y z * c z w ∂μ) ∂μ
      = ∫ y, ∫ z, a x y * (b y z * c z w) ∂μ ∂μ := by
        congr 1; funext y; rw [integral_const_mul]
    _ = ∫ z, ∫ y, a x y * (b y z * c z w) ∂μ ∂μ := swap_bdd hF hFb
    _ = ∫ z, (∫ y, a x y * b y z ∂μ) * c z w ∂μ := by
        congr 1; funext z; rw [← integral_mul_const]; congr 1; funext y; ring

theorem iter_add {k : X → X → ℝ} (hk : Bdd k) (i l : ℕ) :
    iter μ k (i + l + 1) = conv μ (iter μ k i) (iter μ k l) := by
  induction i with
  | zero => simp [iter]
  | succ i ih =>
    have e : i + 1 + l + 1 = (i + l + 1) + 1 := by omega
    rw [e]
    change conv μ k (iter μ k (i + l + 1)) = conv μ (conv μ k (iter μ k i)) (iter μ k l)
    rw [ih, conv_assoc hk (hk.iter i) (hk.iter l)]

/-! ## Hilbert–Schmidt inequalities -/

/-- Cauchy–Schwarz for integrals, by the discriminant. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) ν) (hg : Integrable (fun x => g x ^ 2) ν)
    (hfg : Integrable (fun x => f x * g x) ν) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * (∫ x, g x ^ 2 ∂ν) := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂ν) * (t * t) + (-2 * ∫ x, f x * g x ∂ν) * t
      + ∫ x, f x ^ 2 ∂ν := by
    intro t
    have i1 : Integrable (fun x => f x ^ 2 - 2 * t * (f x * g x)) ν := hf.sub (hfg.const_mul (2 * t))
    have i2 : Integrable (fun x => 2 * t * (f x * g x)) ν := hfg.const_mul (2 * t)
    have i3 : Integrable (fun x => t ^ 2 * g x ^ 2) ν := hg.const_mul (t ^ 2)
    have h0 : 0 ≤ ∫ x, (f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * g x ^ 2) ∂ν := by
      apply integral_nonneg
      intro x
      have : f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * g x ^ 2 = (f x - t * g x) ^ 2 := by ring
      simp only [this]; positivity
    rw [integral_add i1 i3, integral_sub hf i2, integral_const_mul, integral_const_mul] at h0
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

omit [IsProbabilityMeasure μ] in
theorem hs_nonneg (h : X → X → ℝ) : 0 ≤ hs μ h :=
  integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

theorem hs_conv_le_mul {a c : X → X → ℝ} (ha : Bdd a) (hc : Bdd c) :
    hs μ (conv μ a c) ≤ hs μ a * hs μ c := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  obtain ⟨Cc, hCc⟩ := hc.bdd
  have hCa0 : ∀ x y, |a x y| ^ 2 ≤ Ca ^ 2 := fun x y =>
    pow_le_pow_left₀ (abs_nonneg _) (hCa x y) 2
  have hCc0 : ∀ x y, |c x y| ^ 2 ≤ Cc ^ 2 := fun x y =>
    pow_le_pow_left₀ (abs_nonneg _) (hCc x y) 2
  set A : X → ℝ := fun x => ∫ y, a x y ^ 2 ∂μ with hA
  set B : X → ℝ := fun z => ∫ y, c y z ^ 2 ∂μ with hB
  have hAm : Measurable A := measurable_integral_right (F := fun x y => a x y ^ 2) (ha.meas.pow_const 2)
  have hBm : Measurable B :=
    measurable_integral_right (F := fun z y => c y z ^ 2)
      ((hc.meas.comp measurable_swap).pow_const 2)
  have hAb : ∀ x, |A x| ≤ Ca ^ 2 := fun x => abs_integral_le fun y => by
    rw [abs_pow]; exact hCa0 x y
  have hBb : ∀ z, |B z| ≤ Cc ^ 2 := fun z => abs_integral_le fun y => by
    rw [abs_pow]; exact hCc0 y z
  have hpt : ∀ x z, conv μ a c x z ^ 2 ≤ A x * B z := by
    intro x z
    apply sq_integral_mul_le
    · exact integrable_of_bdd ((ha.row x).pow_const 2) (fun y => by rw [abs_pow]; exact hCa0 x y)
    · exact integrable_of_bdd ((hc.col z).pow_const 2) (fun y => by rw [abs_pow]; exact hCc0 y z)
    · refine integrable_of_bdd ((ha.row x).mul (hc.col z)) (C := Ca * Cc) (fun y => ?_)
      rw [abs_mul]
      exact mul_le_mul (hCa x y) (hCc y z) (abs_nonneg _) ((abs_nonneg _).trans (hCa x y))
  have hconv := (ha.conv (μ := μ) hc)
  obtain ⟨Cv, hCv⟩ := hconv.bdd
  have hinner : ∀ x, ∫ z, conv μ a c x z ^ 2 ∂μ ≤ ∫ z, A x * B z ∂μ := by
    intro x
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) ?_
      (Filter.Eventually.of_forall fun z => hpt x z)
    exact integrable_of_bdd (measurable_const.mul hBm) (C := Ca ^ 2 * Cc ^ 2) (fun z => by
      rw [abs_mul]; exact mul_le_mul (hAb x) (hBb z) (abs_nonneg _) (by positivity))
  have hB_int : ∫ z, B z ∂μ = hs μ c := by
    have hm : Measurable (Function.uncurry (fun z y => c y z ^ 2)) :=
      (hc.meas.comp measurable_swap).pow_const 2
    rw [hB, swap_bdd hm (C := Cc ^ 2) (fun z y => by rw [abs_pow]; exact hCc0 y z)]
    rfl
  calc hs μ (conv μ a c) = ∫ x, ∫ z, conv μ a c x z ^ 2 ∂μ ∂μ := rfl
    _ ≤ ∫ x, ∫ z, A x * B z ∂μ ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => integral_nonneg fun z => sq_nonneg _) ?_
          (Filter.Eventually.of_forall hinner)
        refine integrable_of_bdd ?_ (C := Ca ^ 2 * Cc ^ 2) (fun x => ?_)
        · simp_rw [integral_const_mul]; exact hAm.mul measurable_const
        · rw [integral_const_mul, abs_mul]
          exact mul_le_mul (hAb x) (abs_integral_le hBb) (abs_nonneg _) (by positivity)
    _ = (∫ x, A x ∂μ) * ∫ z, B z ∂μ := by
        simp_rw [integral_const_mul]; rw [integral_mul_const]
    _ = hs μ a * hs μ c := by rw [hB_int]; rfl

omit [IsProbabilityMeasure μ] in
/-- `‖g‖² = ∫ g²` in `L²`. -/
theorem norm_sq_eq_integral (g : Lp ℝ 2 μ) : ‖g‖ ^ 2 = ∫ x, (g : X → ℝ) x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

section Operator

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C)

omit [IsProbabilityMeasure μ] in
/-- `kernelFun` depends on `f` only through its a.e. class. -/
theorem kernelFun_congr {h : X → X → ℝ} {f g : X → ℝ} (hfg : f =ᵐ[μ] g) (x : X) :
    kernelFun h μ f x = kernelFun h μ g x := by
  unfold kernelFun
  refine integral_congr_ae ?_
  filter_upwards [hfg] with y hy
  rw [hy]

include hkm hC0 hkb in
/-- `hs (k ∗ c) ≤ ‖K‖² · hs c`. -/
theorem hs_conv_le_norm {c : X → X → ℝ} (hc : Bdd c) :
    hs μ (conv μ k c) ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 * hs μ c := by
  obtain ⟨Cc, hCc⟩ := hc.bdd
  set K := kernelCLM k C hkm hC0 hkb μ μ
  have hcol : ∀ z, MemLp (fun y => c y z) 2 μ := fun z =>
    MemLp.of_bound (hc.col z).aestronglyMeasurable Cc
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hCc y z)
  have hz : ∀ z, ∫ x, conv μ k c x z ^ 2 ∂μ ≤ ‖K‖ ^ 2 * ∫ y, c y z ^ 2 ∂μ := by
    intro z
    set g : Lp ℝ 2 μ := (hcol z).toLp _
    have hgc : (g : X → ℝ) =ᵐ[μ] fun y => c y z := (hcol z).coeFn_toLp
    have h1 : ‖K g‖ ^ 2 = ∫ x, conv μ k c x z ^ 2 ∂μ := by
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_kernelCLM k C hkm hC0 hkb μ μ g] with x hx
      rw [hx, kernelFun_congr hgc x]
      rfl
    have h2 : ‖g‖ ^ 2 = ∫ y, c y z ^ 2 ∂μ := by
      rw [norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hgc] with y hy
      rw [hy]
    have h3 : ‖K g‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖g‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (K.le_opNorm g) 2
    rw [← h1, ← h2]; exact h3
  have hconv := (Bdd.conv (μ := μ) ⟨hkm, C, hkb⟩ hc)
  obtain ⟨Cv, hCv⟩ := hconv.bdd
  have hm1 : Measurable (Function.uncurry (fun x z => conv μ k c x z ^ 2)) := hconv.meas.pow_const 2
  have hm2 : Measurable (Function.uncurry (fun z y => c y z ^ 2)) :=
    (hc.meas.comp measurable_swap).pow_const 2
  calc hs μ (conv μ k c) = ∫ x, ∫ z, conv μ k c x z ^ 2 ∂μ ∂μ := rfl
    _ = ∫ z, ∫ x, conv μ k c x z ^ 2 ∂μ ∂μ :=
        swap_bdd hm1 (C := Cv ^ 2) (fun x z => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCv x z) 2)
    _ ≤ ∫ z, ‖K‖ ^ 2 * ∫ y, c y z ^ 2 ∂μ ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => integral_nonneg fun x => sq_nonneg _) ?_
          (Filter.Eventually.of_forall hz)
        refine integrable_of_bdd (measurable_const.mul (measurable_integral_right hm2))
          (C := ‖K‖ ^ 2 * Cc ^ 2) (fun z => ?_)
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖K‖ ^ 2)]
        exact mul_le_mul_of_nonneg_left (abs_integral_le fun y => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCc y z) 2) (by positivity)
    _ = ‖K‖ ^ 2 * ∫ z, ∫ y, c y z ^ 2 ∂μ ∂μ := integral_const_mul _ _
    _ = ‖K‖ ^ 2 * hs μ c := by
        rw [swap_bdd hm2 (C := Cc ^ 2) (fun z y => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCc y z) 2)]
        rfl

include hkm hC0 hkb in
/-- `hs(k^{∗(i+l+1)}) ≤ ‖K‖^{2l} hs(k^{∗(i+1)})`. -/
theorem hs_iter_le (i l : ℕ) :
    hs μ (iter μ k (i + l)) ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * l) * hs μ (iter μ k i) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  induction l with
  | zero => simp
  | succ l ih =>
    have e : i + (l + 1) = (i + l) + 1 := by omega
    rw [e]
    change hs μ (conv μ k (iter μ k (i + l))) ≤ _
    calc hs μ (conv μ k (iter μ k (i + l)))
        ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 * hs μ (iter μ k (i + l)) :=
          hs_conv_le_norm hkm hC0 hkb (hk.iter (i + l))
      _ ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 *
            (‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * l) * hs μ (iter μ k i)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by ring

end Operator

/-! ## The eigen-decomposition -/

section Eigen

variable {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

/-- The remainder kernel `k − c φ⊗φ`. -/
def rem (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) : X → X → ℝ := fun x y => k x y - c * φ x * φ y

include hk hφm hφb in
theorem Bdd.rem : Bdd (rem k c φ) := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  refine ⟨hk.meas.sub ((measurable_const.mul (hφm.comp measurable_fst)).mul
    (hφm.comp measurable_snd)), Ck + |c| * B * B, fun x y => ?_⟩
  unfold MassGap.KernelPower.rem
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hφb x)
  calc |k x y - c * φ x * φ y| ≤ |k x y| + |c * φ x * φ y| := abs_sub _ _
    _ ≤ Ck + |c| * B * B := by
        rw [abs_mul, abs_mul]
        exact add_le_add (hCk x y) (mul_le_mul (mul_le_mul_of_nonneg_left (hφb x) (abs_nonneg _))
          (hφb y) (abs_nonneg _) (by positivity))

theorem integrable_mul_of_bdd {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg) : Integrable (fun x => f x * g x) μ :=
  integrable_of_bdd (hf.mul hg) (C := Cf * Cg) (fun x => by
    rw [abs_mul]; exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) ((abs_nonneg _).trans (hfb x)))

include hk hφm hφb hφ1 heig in
theorem rem_row_orth (z : X) : ∫ y, rem k c φ z y * φ y ∂μ = 0 := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  unfold MassGap.KernelPower.rem
  have e : (fun y => (k z y - c * φ z * φ y) * φ y)
      = fun y => k z y * φ y - (c * φ z) * φ y ^ 2 := by funext y; ring
  rw [e, integral_sub (integrable_mul_of_bdd (hk.row z) hφm (hCk z) hφb)
    ((integrable_of_bdd (hφm.pow_const 2) (C := B ^ 2) (fun y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb y) 2)).const_mul _),
    integral_const_mul, hφ1, heig z]
  ring

include hk hsym hφm hφb hφ1 heig in
theorem rem_col_orth (z : X) : ∫ y, φ y * rem k c φ y z ∂μ = 0 := by
  have e : (fun y => φ y * rem k c φ y z) = fun y => rem k c φ z y * φ y := by
    funext y; unfold MassGap.KernelPower.rem; rw [hsym y z]; ring
  rw [e]; exact rem_row_orth hk hφm hφb hφ1 heig z

include hk hsym hφm hφb hφ1 heig in
theorem iter_rem_col_orth : ∀ (i : ℕ) (z : X), ∫ y, φ y * iter μ (rem k c φ) i y z ∂μ = 0
  | 0, z => rem_col_orth hk hsym hφm hφb hφ1 heig z
  | i + 1, z => by
    have hr := Bdd.rem hk hφm hφb (c := c)
    have hri := hr.iter (μ := μ) i
    obtain ⟨Cr, hCr⟩ := hr.bdd
    obtain ⟨Ci, hCi⟩ := hri.bdd
    have hF : Measurable (Function.uncurry
        (fun y w => φ y * (rem k c φ y w * iter μ (rem k c φ) i w z))) :=
      (hφm.comp measurable_fst).mul (hr.meas.mul ((hri.col z).comp measurable_snd))
    have hFb : ∀ y w, |φ y * (rem k c φ y w * iter μ (rem k c φ) i w z)| ≤ B * (Cr * Ci) := by
      intro y w
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hφb y) (mul_le_mul (hCr y w) (hCi w z) (abs_nonneg _)
        ((abs_nonneg _).trans (hCr y w))) (by positivity) ((abs_nonneg _).trans (hφb y))
    change ∫ y, φ y * (∫ w, rem k c φ y w * iter μ (rem k c φ) i w z ∂μ) ∂μ = 0
    calc ∫ y, φ y * (∫ w, rem k c φ y w * iter μ (rem k c φ) i w z ∂μ) ∂μ
        = ∫ y, ∫ w, φ y * (rem k c φ y w * iter μ (rem k c φ) i w z) ∂μ ∂μ := by
          congr 1; funext y; rw [integral_const_mul]
      _ = ∫ w, ∫ y, φ y * (rem k c φ y w * iter μ (rem k c φ) i w z) ∂μ ∂μ := swap_bdd hF hFb
      _ = ∫ w, (∫ y, φ y * rem k c φ y w ∂μ) * iter μ (rem k c φ) i w z ∂μ := by
          congr 1; funext w; rw [← integral_mul_const]; congr 1; funext y; ring
      _ = 0 := by simp [rem_col_orth hk hsym hφm hφb hφ1 heig]

include hk hφm hφb hφ1 heig in
theorem iter_rem_row_orth : ∀ (i : ℕ) (x : X), ∫ z, iter μ (rem k c φ) i x z * φ z ∂μ = 0
  | 0, x => rem_row_orth hk hφm hφb hφ1 heig x
  | i + 1, x => by
    have hr := Bdd.rem hk hφm hφb (c := c)
    have hri := hr.iter (μ := μ) i
    obtain ⟨Cr, hCr⟩ := hr.bdd
    obtain ⟨Ci, hCi⟩ := hri.bdd
    have hF : Measurable (Function.uncurry
        (fun z w => rem k c φ x w * (iter μ (rem k c φ) i w z * φ z))) :=
      ((hr.row x).comp measurable_snd).mul
        ((hri.meas.comp measurable_swap).mul (hφm.comp measurable_fst))
    have hFb : ∀ z w, |rem k c φ x w * (iter μ (rem k c φ) i w z * φ z)| ≤ Cr * (Ci * B) := by
      intro z w
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hCr x w) (mul_le_mul (hCi w z) (hφb z) (abs_nonneg _)
        ((abs_nonneg _).trans (hCi w z))) (by positivity) ((abs_nonneg _).trans (hCr x w))
    change ∫ z, (∫ w, rem k c φ x w * iter μ (rem k c φ) i w z ∂μ) * φ z ∂μ = 0
    calc ∫ z, (∫ w, rem k c φ x w * iter μ (rem k c φ) i w z ∂μ) * φ z ∂μ
        = ∫ z, ∫ w, rem k c φ x w * (iter μ (rem k c φ) i w z * φ z) ∂μ ∂μ := by
          congr 1; funext z; rw [← integral_mul_const]; congr 1; funext w; ring
      _ = ∫ w, ∫ z, rem k c φ x w * (iter μ (rem k c φ) i w z * φ z) ∂μ ∂μ := swap_bdd hF hFb
      _ = ∫ w, rem k c φ x w * (∫ z, iter μ (rem k c φ) i w z * φ z ∂μ) ∂μ := by
          congr 1; funext w; rw [integral_const_mul]
      _ = 0 := by simp [iter_rem_row_orth i]

include hk hsym hφm hφb hφ1 heig in
/-- `k^{∗(i+1)} = c^{i+1} φ⊗φ + r^{∗(i+1)}` pointwise. -/
theorem iter_decomp : ∀ (i : ℕ) (x z : X),
    iter μ k i x z = c ^ (i + 1) * φ x * φ z + iter μ (rem k c φ) i x z
  | 0, x, z => by simp [iter, rem]
  | i + 1, x, z => by
    have hr := Bdd.rem hk hφm hφb (c := c)
    have hri := hr.iter (μ := μ) i
    obtain ⟨Cr, hCr⟩ := hr.bdd
    obtain ⟨Ci, hCi⟩ := hri.bdd
    have IH := iter_decomp i
    change ∫ y, k x y * iter μ k i y z ∂μ = _
    have e1 : (fun y => k x y * iter μ k i y z)
        = fun y => (c * φ x * c ^ (i + 1) * φ z) * φ y ^ 2
          + ((c * φ x) * (φ y * iter μ (rem k c φ) i y z)
          + ((c ^ (i + 1) * φ z) * (rem k c φ x y * φ y)
          + rem k c φ x y * iter μ (rem k c φ) i y z)) := by
      funext y; rw [IH y z]; unfold MassGap.KernelPower.rem; ring
    have hφ2 : Integrable (fun y => φ y ^ 2) μ := integrable_of_bdd (hφm.pow_const 2) (C := B ^ 2)
      (fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb y) 2)
    have i2 : Integrable (fun y => φ y * iter μ (rem k c φ) i y z) μ :=
      integrable_mul_of_bdd hφm (hri.col z) hφb (fun y => hCi y z)
    have i3 : Integrable (fun y => rem k c φ x y * φ y) μ :=
      integrable_mul_of_bdd (hr.row x) hφm (fun y => hCr x y) hφb
    have i4 : Integrable (fun y => rem k c φ x y * iter μ (rem k c φ) i y z) μ :=
      integrable_mul_of_bdd (hr.row x) (hri.col z) (fun y => hCr x y) (fun y => hCi y z)
    have j1 : Integrable (fun y => (c * φ x * c ^ (i + 1) * φ z) * φ y ^ 2) μ := hφ2.const_mul _
    have j2 : Integrable (fun y => (c * φ x) * (φ y * iter μ (rem k c φ) i y z)) μ := i2.const_mul _
    have j3 : Integrable (fun y => (c ^ (i + 1) * φ z) * (rem k c φ x y * φ y)) μ := i3.const_mul _
    have j34 : Integrable (fun y => (c ^ (i + 1) * φ z) * (rem k c φ x y * φ y)
        + rem k c φ x y * iter μ (rem k c φ) i y z) μ := j3.add i4
    have j234 : Integrable (fun y => (c * φ x) * (φ y * iter μ (rem k c φ) i y z)
        + ((c ^ (i + 1) * φ z) * (rem k c φ x y * φ y)
        + rem k c φ x y * iter μ (rem k c φ) i y z)) μ := j2.add j34
    rw [e1, integral_add j1 j234, integral_add j2 j34, integral_add j3 i4,
      integral_const_mul, integral_const_mul, integral_const_mul, hφ1, iter_rem_col_orth hk hsym hφm hφb hφ1 heig i z,
      rem_row_orth hk hφm hφb hφ1 heig x]
    change _ = _ + conv μ (rem k c φ) (iter μ (rem k c φ) i) x z
    unfold conv
    ring

include hk hsym hφm hφb hφ1 heig in
/-- `hs(k^{∗(i+1)}) = c^{2(i+1)} + hs(r^{∗(i+1)})`. -/
theorem hs_iter_decomp (i : ℕ) :
    hs μ (iter μ k i) = c ^ (2 * (i + 1)) + hs μ (iter μ (rem k c φ) i) := by
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hri := hr.iter (μ := μ) i
  obtain ⟨Ci, hCi⟩ := hri.bdd
  have hφ2 : Integrable (fun y => φ y ^ 2) μ := integrable_of_bdd (hφm.pow_const 2) (C := B ^ 2)
    (fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb y) 2)
  have hpt : ∀ x, ∫ z, iter μ k i x z ^ 2 ∂μ
      = c ^ (2 * (i + 1)) * φ x ^ 2 + ∫ z, iter μ (rem k c φ) i x z ^ 2 ∂μ := by
    intro x
    have e : (fun z => iter μ k i x z ^ 2)
        = fun z => (c ^ (2 * (i + 1)) * φ x ^ 2) * φ z ^ 2
          + ((2 * c ^ (i + 1) * φ x) * (iter μ (rem k c φ) i x z * φ z)
          + iter μ (rem k c φ) i x z ^ 2) := by
      funext z; rw [iter_decomp hk hsym hφm hφb hφ1 heig i x z]; ring
    have i2 : Integrable (fun z => iter μ (rem k c φ) i x z * φ z) μ :=
      integrable_mul_of_bdd (hri.row x) hφm (fun z => hCi x z) hφb
    have i3 : Integrable (fun z => iter μ (rem k c φ) i x z ^ 2) μ :=
      integrable_of_bdd ((hri.row x).pow_const 2) (C := Ci ^ 2) (fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCi x z) 2)
    have j1 : Integrable (fun z => (c ^ (2 * (i + 1)) * φ x ^ 2) * φ z ^ 2) μ := hφ2.const_mul _
    have j2 : Integrable (fun z => (2 * c ^ (i + 1) * φ x) * (iter μ (rem k c φ) i x z * φ z)) μ :=
      i2.const_mul _
    have j23 : Integrable (fun z => (2 * c ^ (i + 1) * φ x) * (iter μ (rem k c φ) i x z * φ z)
        + iter μ (rem k c φ) i x z ^ 2) μ := j2.add i3
    rw [e, integral_add j1 j23, integral_add j2 i3, integral_const_mul, integral_const_mul, hφ1,
      iter_rem_row_orth hk hφm hφb hφ1 heig i x]
    ring
  unfold hs
  simp_rw [hpt]
  have i4 : Integrable (fun x => ∫ z, iter μ (rem k c φ) i x z ^ 2 ∂μ) μ :=
    integrable_of_bdd (measurable_integral_right (hri.meas.pow_const 2)) (C := Ci ^ 2)
      (fun x => abs_integral_le fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCi x z) 2)
  have j1 : Integrable (fun x => c ^ (2 * (i + 1)) * φ x ^ 2) μ := hφ2.const_mul _
  rw [integral_add j1 i4, integral_const_mul, hφ1, mul_one]

end Eigen

/-! ## The four trace facts -/

section Facts

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) (hc0 : c ≠ 0)

/-- The trace sequence: `a m = hs(k^{∗(m/2)})`, the cyclic integral of `m` copies of `k` for even
`m ≥ 2`. -/
noncomputable def traceSeq (μ : Measure X) (k : X → X → ℝ) (m : ℕ) : ℝ := hs μ (iter μ k (m / 2 - 1))

/-- The relative excited weight at `m = 2j`. -/
noncomputable def excited (μ : Measure X) (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (j : ℕ) : ℝ :=
  hs μ (iter μ (rem k c φ) (j - 1)) / |c| ^ (2 * j)

include hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hc0 in
theorem powerFacts (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.PowerFacts (traceSeq μ k) |c| (excited μ k c φ j) (2 * j) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hl : 0 < |c| := abs_pos.mpr hc0
  have hpow : ∀ n : ℕ, c ^ (2 * n) = |c| ^ (2 * n) := fun n => by
    rw [pow_mul, pow_mul, ← sq_abs]
  have hr := Bdd.rem hk hφm hφb (c := c)
  have e1 : 2 * j / 2 - 1 = j - 1 := by omega
  have e2 : 2 * (2 * j) / 2 - 1 = (j - 1) + j := by omega
  have e3 : 2 * (2 * (2 * j)) / 2 - 1 = (j - 1) + 3 * j := by omega
  have f1 : j - 1 + 1 = j := by omega
  have f2 : j - 1 + j + 1 = 2 * j := by omega
  have f3 : j - 1 + 3 * j + 1 = 2 * (2 * j) := by omega
  have hR0 : 0 ≤ hs μ (iter μ (rem k c φ) (j - 1)) := hs_nonneg _
  have hcl : 0 < |c| ^ (2 * j) := pow_pos hl _
  have hsdef : excited μ k c φ j * |c| ^ (2 * j) = hs μ (iter μ (rem k c φ) (j - 1)) := by
    unfold excited; field_simp
  have hbase : traceSeq μ k (2 * j) = |c| ^ (2 * j) + hs μ (iter μ (rem k c φ) (j - 1)) := by
    unfold traceSeq
    rw [e1, hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig (j - 1), hpow, f1]
  have hdbl : traceSeq μ k (2 * (2 * j)) = |c| ^ (2 * (2 * j))
      + hs μ (iter μ (rem k c φ) ((j - 1) + j)) := by
    unfold traceSeq
    rw [e2, hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig (j - 1 + j), hpow, f2]
  have hquad : traceSeq μ k (2 * (2 * (2 * j))) = |c| ^ (2 * (2 * (2 * j)))
      + hs μ (iter μ (rem k c φ) ((j - 1) + 3 * j)) := by
    unfold traceSeq
    rw [e3, hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig (j - 1 + 3 * j), hpow, f3]
  refine ⟨hl, div_nonneg hR0 hcl.le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbase, ← hsdef]; ring
  · have h := hs_iter_le (μ := μ) hkm hC0 hkb (j - 1) j
    rw [← hnorm] at h
    unfold traceSeq
    rw [e1, e2]
    exact h
  · rw [hdbl]
    have e4 : (j - 1) + j = (j - 1) + (j - 1) + 1 := by omega
    have hsq : hs μ (iter μ (rem k c φ) ((j - 1) + j))
        ≤ hs μ (iter μ (rem k c φ) (j - 1)) ^ 2 := by
      rw [e4, iter_add hr (j - 1) (j - 1), sq]
      exact hs_conv_le_mul (hr.iter (j - 1)) (hr.iter (j - 1))
    have hp2 : |c| ^ (2 * (2 * j)) = (|c| ^ (2 * j)) ^ 2 := by rw [← pow_mul]; ring_nf
    have hR2 : hs μ (iter μ (rem k c φ) (j - 1)) ^ 2
        = |c| ^ (2 * (2 * j)) * excited μ k c φ j ^ 2 := by
      rw [← hsdef, hp2]; ring
    rw [hR2] at hsq
    nlinarith
  · rw [hdbl]; linarith [hs_nonneg (μ := μ) (iter μ (rem k c φ) ((j - 1) + j))]
  · rw [hquad]; linarith [hs_nonneg (μ := μ) (iter μ (rem k c φ) ((j - 1) + 3 * j))]

end Facts

#print axioms iter_add
#print axioms hs_conv_le_mul
#print axioms hs_conv_le_norm
#print axioms hs_iter_decomp
#print axioms powerFacts

end MassGap.KernelPower
