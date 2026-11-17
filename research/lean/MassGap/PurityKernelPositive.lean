import Mathlib
import MassGap.KernelInjective
import MassGap.RectTransferG

/-!
# MassGap.PurityKernelPositive — the Wilson transfer kernel is a positive operator

The step from Theorem 5.2 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov,
I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling*
(research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`) to the lattice gap `Δ_lat` uses `K ≥ 0`. This module proves it for the
gauge-projected transfer kernel `RectTransferG.kTG` of the rectangular torus over any gauge group
`G`, at `β ≥ 0`, on every integrable function of one slice:

    ∫∫ u(x) kTG(x, y) u(y) dx dy ≥ 0.

## Averaged crossing kernels

For finite coordinates `φ : P → X × Y → ℝ` with `|φ| ≤ 1`, a probability measure `ν` on `Y` and
`c ≥ 0`, the kernel

    avgKern ν φ c x y = ∫∫ exp (c ∑ₚ φₚ(x, b) φₚ(y, a)) dν(a) dν(b)

has a nonnegative quadratic form on every integrable `W` (`quad_nonneg`). The truncated exponential
`expTrunc N` expands by `KernelInjective.coordKernel_pow` into
`∑_{n<N} cⁿ/n! ∑_s ampl_s(x) ampl_s(y)` with `ampl_s(x) = ∫ pmono φ s (x, b) dν(b)`
(`avgKernTrunc_eq`), so its form is `∑_{n<N} cⁿ/n! ∑_s (∫ ampl_s W)² ≥ 0` (`quadTrunc_nonneg`).
Dominated convergence, with bounds built from `exp (c · |P|)`, passes to `N → ∞` four times
(`tendsto_avgKernTrunc`, `tendsto_quadTrunc`).

## The Wilson kernel

* `wilsonDensityG_mul_inv`: `wilsonDensityG (g h⁻¹) = 1 − (1/d) ∑_q c_q(h) c_q(g)`, with `c_q` the
  real and imaginary parts of the entries of the representation (`entryCoord`), from
  `repM h⁻¹ = (repM h)ᴴ`.
* `tpTG_eq`, `crossEnergy_act`, `gkG_eq_avg`: `tp(A, x, y)` is the crossing energy of `x` and
  `A · y` (`gaugeAct`); the energy is invariant under a common gauge transformation, and the
  left-invariant axis measure turns `gkG` into the average over two independent axis
  configurations `B`, `A` of `exp (−2β E(B · x, A · y))`.
* `gkG_eq_avgKern`: `gkG = e^{−2β |SpT|} · avgKern hAG actCoord (2β/d)`.
* `kTG_quad_nonneg`: the form of `kTG` on integrable `u` is `e^{−2β |SpT|}` times the form of
  `avgKern` on `W = e^{−β sp/2} u`.
-/

namespace MassGap.PurityKernelPositive

open MeasureTheory Filter Topology MassGap.KernelInjective

/-! ## 1. Averaged crossing kernels -/

section Abstract

variable {X Y P : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype P]

/-- The exponential series truncated at order `N`. -/
noncomputable def expTrunc (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, z ^ n / (n.factorial : ℝ)

/-- The amplitude `ampl_s(x) = ∫ pmono φ s (x, b) dν(b)`. -/
noncomputable def ampl (ν : Measure Y) (φ : P → X × Y → ℝ) {n : ℕ} (s : Fin n → P) (x : X) : ℝ :=
  ∫ b, pmono φ s (x, b) ∂ν

/-- The averaged crossing kernel at truncation order `N`. -/
noncomputable def avgKernTrunc (ν : Measure Y) (φ : P → X × Y → ℝ) (c : ℝ) (N : ℕ) (x y : X) :
    ℝ :=
  ∫ b, ∫ a, expTrunc N (c * coordKernel φ (x, b) (y, a)) ∂ν ∂ν

/-- The averaged crossing kernel `∫∫ exp (c ∑ₚ φₚ(x, b) φₚ(y, a)) dν(a) dν(b)`. -/
noncomputable def avgKern (ν : Measure Y) (φ : P → X × Y → ℝ) (c : ℝ) (x y : X) : ℝ :=
  ∫ b, ∫ a, Real.exp (c * coordKernel φ (x, b) (y, a)) ∂ν ∂ν

theorem abs_expTrunc_le (N : ℕ) (z : ℝ) : |expTrunc N z| ≤ Real.exp |z| := by
  calc |expTrunc N z| ≤ ∑ n ∈ Finset.range N, |z ^ n / (n.factorial : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.range N, |z| ^ n / (n.factorial : ℝ) :=
        Finset.sum_congr rfl fun n _ => by rw [abs_div, abs_pow, Nat.abs_cast]
    _ ≤ Real.exp |z| := Real.sum_le_exp_of_nonneg (abs_nonneg z) N

theorem tendsto_expTrunc (z : ℝ) :
    Tendsto (fun N => expTrunc N z) atTop (𝓝 (Real.exp z)) := by
  have h : HasSum (fun n => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  exact h.tendsto_sum_nat

theorem continuous_expTrunc (N : ℕ) : Continuous (expTrunc N) :=
  continuous_finsetSum _ fun n _ => (continuous_pow n).div_const _

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem expTrunc_coordKernel (φ : P → X × Y → ℝ) (c : ℝ) (N : ℕ) (p q : X × Y) :
    expTrunc N (c * coordKernel φ p q) =
      ∑ n ∈ Finset.range N, ∑ s : Fin n → P,
        c ^ n / (n.factorial : ℝ) * pmono φ s p * pmono φ s q := by
  unfold expTrunc
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_pow, coordKernel_pow, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem integrable_of_abs_bound {Z : Type*} [MeasurableSpace Z] {m : Measure Z}
    [IsFiniteMeasure m] {f : Z → ℝ} (hf : Measurable f) {C : ℝ} (h : ∀ a, |f a| ≤ C) :
    Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact h a)

theorem abs_integral_le_bound {Z : Type*} [MeasurableSpace Z] {m : Measure Z}
    [IsProbabilityMeasure m] {f : Z → ℝ} {C : ℝ} (h : ∀ a, |f a| ≤ C) :
    |∫ a, f a ∂m| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := m) (f := f) (C := C)
    (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact h a)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

variable {φ : P → X × Y → ℝ}

omit [MeasurableSpace X] [MeasurableSpace Y] [Fintype P] in
theorem abs_pmono_le (hb : ∀ p z, |φ p z| ≤ 1) {n : ℕ} (s : Fin n → P) (z : X × Y) :
    |pmono φ s z| ≤ 1 := by
  rw [pmono, Finset.abs_prod]
  exact Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => hb (s k) z

omit [Fintype P] in
theorem measurable_pmono (hφ : ∀ p, Measurable (φ p)) {n : ℕ} (s : Fin n → P) :
    Measurable (pmono φ s) := by
  unfold pmono
  exact Finset.measurable_prod _ fun k _ => hφ (s k)

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem abs_coordKernel_le (hb : ∀ p z, |φ p z| ≤ 1) (z w : X × Y) :
    |coordKernel φ z w| ≤ Fintype.card P := by
  unfold coordKernel
  calc |∑ i, φ i z * φ i w| ≤ ∑ i, |φ i z * φ i w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : P, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_one₀ (hb i z) (abs_nonneg _) (hb i w)
    _ = Fintype.card P := by simp

theorem measurable_coordKernel (hφ : ∀ p, Measurable (φ p)) (x : X) (b : Y) (y : X) :
    Measurable fun a => coordKernel φ (x, b) (y, a) := by
  unfold coordKernel
  exact Finset.measurable_sum _ fun i _ => ((hφ i).comp measurable_prodMk_left).const_mul _

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem abs_expTrunc_coord (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ} (hc : 0 ≤ c) (N : ℕ)
    (z w : X × Y) :
    |expTrunc N (c * coordKernel φ z w)| ≤ Real.exp (c * Fintype.card P) :=
  (abs_expTrunc_le N _).trans (Real.exp_le_exp.2 (by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (abs_coordKernel_le hb z w) hc))

variable {ν : Measure Y} [IsProbabilityMeasure ν]

omit [Fintype P] in
theorem integrable_pmono_right (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1)
    {n : ℕ} (s : Fin n → P) (x : X) : Integrable (fun b => pmono φ s (x, b)) ν :=
  integrable_of_abs_bound ((measurable_pmono hφ s).comp measurable_prodMk_left)
    fun _ => abs_pmono_le hb s _

omit [Fintype P] in
theorem measurable_ampl (hφ : ∀ p, Measurable (φ p)) {n : ℕ} (s : Fin n → P) :
    Measurable (ampl ν φ s) := by
  have h : StronglyMeasurable fun x => ∫ b, pmono φ s (x, b) ∂ν :=
    (measurable_pmono hφ s).stronglyMeasurable.integral_prod_right'
  exact h.measurable

omit [MeasurableSpace X] [Fintype P] in
theorem abs_ampl_le (hb : ∀ p z, |φ p z| ≤ 1) {n : ℕ} (s : Fin n → P) (x : X) :
    |ampl ν φ s x| ≤ 1 :=
  abs_integral_le_bound fun _ => abs_pmono_le hb s _

theorem integral_inner (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) (c : ℝ)
    (N : ℕ) (x : X) (b : Y) (y : X) :
    ∫ a, expTrunc N (c * coordKernel φ (x, b) (y, a)) ∂ν =
      ∑ n ∈ Finset.range N, ∑ s : Fin n → P,
        c ^ n / (n.factorial : ℝ) * pmono φ s (x, b) * ampl ν φ s y := by
  simp_rw [expTrunc_coordKernel]
  rw [integral_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun s _ => (integrable_pmono_right hφ hb s y).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun s _ => (integrable_pmono_right hφ hb s y).const_mul _]
  exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _

theorem measurable_inner (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) (c : ℝ)
    (N : ℕ) (x y : X) :
    Measurable fun b => ∫ a, expTrunc N (c * coordKernel φ (x, b) (y, a)) ∂ν := by
  simp_rw [integral_inner hφ hb]
  exact Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun s _ =>
    (((measurable_pmono hφ s).comp measurable_prodMk_left).const_mul _).mul_const _

theorem avgKernTrunc_eq (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) (c : ℝ)
    (N : ℕ) (x y : X) :
    avgKernTrunc ν φ c N x y = ∑ n ∈ Finset.range N, ∑ s : Fin n → P,
      c ^ n / (n.factorial : ℝ) * ampl ν φ s x * ampl ν φ s y := by
  unfold avgKernTrunc
  simp_rw [integral_inner hφ hb]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun s _ =>
    ((integrable_pmono_right hφ hb s x).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun s _ =>
    ((integrable_pmono_right hφ hb s x).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun s _ => ?_
  show _ = c ^ n / (n.factorial : ℝ) * (∫ b, pmono φ s (x, b) ∂ν) * ∫ a, pmono φ s (y, a) ∂ν
  rw [integral_mul_const, integral_const_mul]
  rfl

theorem measurable_avgKernTrunc (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1)
    (c : ℝ) (N : ℕ) (x : X) : Measurable fun y => avgKernTrunc ν φ c N x y := by
  simp_rw [avgKernTrunc_eq hφ hb]
  exact Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun s _ =>
    (measurable_ampl hφ s).const_mul _

omit [MeasurableSpace X] in
theorem abs_avgKernTrunc_le (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) (x y : X) :
    |avgKernTrunc ν φ c N x y| ≤ Real.exp (c * Fintype.card P) :=
  abs_integral_le_bound fun _ => abs_integral_le_bound fun _ => abs_expTrunc_coord hb hc N _ _

theorem tendsto_avgKernTrunc (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (x y : X) :
    Tendsto (fun N => avgKernTrunc ν φ c N x y) atTop (𝓝 (avgKern ν φ c x y)) := by
  unfold avgKernTrunc avgKern
  refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (c * Fintype.card P))
    (fun N => (measurable_inner hφ hb c N x y).aestronglyMeasurable) (integrable_const _)
    (fun N => Eventually.of_forall fun b => ?_) (Eventually.of_forall fun b => ?_)
  · rw [Real.norm_eq_abs]
    exact abs_integral_le_bound fun a => abs_expTrunc_coord hb hc N _ _
  · refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (c * Fintype.card P))
      (fun N => ?_) (integrable_const _) (fun N => Eventually.of_forall fun a => ?_)
      (Eventually.of_forall fun a => tendsto_expTrunc _)
    · exact ((continuous_expTrunc N).measurable.comp
        ((measurable_coordKernel hφ x b y).const_mul c)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_expTrunc_coord hb hc N _ _

variable {μ : Measure X} {W : X → ℝ}

omit [Fintype P] in
theorem integrable_ampl_mul (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1)
    (hW : Integrable W μ) {n : ℕ} (s : Fin n → P) :
    Integrable (fun y => ampl ν φ s y * W y) μ :=
  hW.bdd_mul (measurable_ampl hφ s).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_ampl_le hb s y)

theorem integral_avgKernTrunc_mul (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1)
    (hW : Integrable W μ) (c : ℝ) (N : ℕ) (x : X) :
    ∫ y, avgKernTrunc ν φ c N x y * W y ∂μ = ∑ n ∈ Finset.range N, ∑ s : Fin n → P,
      c ^ n / (n.factorial : ℝ) * ampl ν φ s x * ∫ y, ampl ν φ s y * W y ∂μ := by
  have h : (fun y => avgKernTrunc ν φ c N x y * W y) = fun y => ∑ n ∈ Finset.range N,
      ∑ s : Fin n → P, c ^ n / (n.factorial : ℝ) * ampl ν φ s x * (ampl ν φ s y * W y) := by
    funext y
    rw [avgKernTrunc_eq hφ hb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h, integral_finsetSum _ fun n _ => integrable_finsetSum _ fun s _ =>
    (integrable_ampl_mul hφ hb hW s).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun s _ => (integrable_ampl_mul hφ hb hW s).const_mul _]
  exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _

theorem measurable_integral_avgKernTrunc_mul (hφ : ∀ p, Measurable (φ p))
    (hb : ∀ p z, |φ p z| ≤ 1) (hW : Integrable W μ) (c : ℝ) (N : ℕ) :
    Measurable fun x => ∫ y, avgKernTrunc ν φ c N x y * W y ∂μ := by
  simp_rw [integral_avgKernTrunc_mul hφ hb hW]
  exact Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun s _ =>
    ((measurable_ampl hφ s).const_mul _).mul_const _

/-- The truncated form is `∑_{n<N} cⁿ/n! ∑_s (∫ ampl_s W)² ≥ 0`. -/
theorem quadTrunc_nonneg (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (hW : Integrable W μ) (N : ℕ) :
    0 ≤ ∫ x, (∫ y, avgKernTrunc ν φ c N x y * W y ∂μ) * W x ∂μ := by
  have h : (fun x => (∫ y, avgKernTrunc ν φ c N x y * W y ∂μ) * W x) = fun x =>
      ∑ n ∈ Finset.range N, ∑ s : Fin n → P,
        (c ^ n / (n.factorial : ℝ) * ∫ y, ampl ν φ s y * W y ∂μ) * (ampl ν φ s x * W x) := by
    funext x
    rw [integral_avgKernTrunc_mul hφ hb hW, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h, integral_finsetSum _ fun n _ => integrable_finsetSum _ fun s _ =>
    (integrable_ampl_mul hφ hb hW s).const_mul _]
  refine Finset.sum_nonneg fun n _ => ?_
  rw [integral_finsetSum _ fun s _ => (integrable_ampl_mul hφ hb hW s).const_mul _]
  refine Finset.sum_nonneg fun s _ => ?_
  rw [integral_const_mul, mul_assoc]
  exact mul_nonneg (div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg _)) (mul_self_nonneg _)

theorem tendsto_integral_avgKernTrunc_mul (hφ : ∀ p, Measurable (φ p))
    (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ} (hc : 0 ≤ c) (hW : Integrable W μ) (x : X) :
    Tendsto (fun N => ∫ y, avgKernTrunc ν φ c N x y * W y ∂μ) atTop
      (𝓝 (∫ y, avgKern ν φ c x y * W y ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun y => Real.exp (c * Fintype.card P) * |W y|)
    (fun N => (measurable_avgKernTrunc hφ hb c N x).aestronglyMeasurable.mul
      hW.aestronglyMeasurable)
    (hW.abs.const_mul _)
    (fun N => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_avgKernTrunc_le hb hc N x y) (abs_nonneg _))
    (Eventually.of_forall fun y => (tendsto_avgKernTrunc hφ hb hc x y).mul_const (W y))

theorem tendsto_quadTrunc (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (hW : Integrable W μ) :
    Tendsto (fun N => ∫ x, (∫ y, avgKernTrunc ν φ c N x y * W y ∂μ) * W x ∂μ) atTop
      (𝓝 (∫ x, (∫ y, avgKern ν φ c x y * W y ∂μ) * W x ∂μ)) :=
  tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (c * Fintype.card P) * (∫ y, |W y| ∂μ) * |W x|)
    (fun N => (measurable_integral_avgKernTrunc_mul hφ hb hW c N).aestronglyMeasurable.mul
      hW.aestronglyMeasurable)
    (hW.abs.const_mul _)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h := norm_integral_le_of_norm_le (μ := μ)
        (f := fun y => avgKernTrunc ν φ c N x y * W y) (hW.abs.const_mul (Real.exp (c * Fintype.card P)))
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_avgKernTrunc_le hb hc N x y) (abs_nonneg _))
      rwa [Real.norm_eq_abs, integral_const_mul] at h)
    (Eventually.of_forall fun x =>
      (tendsto_integral_avgKernTrunc_mul hφ hb hc hW x).mul_const (W x))

/-- **The averaged crossing kernel has a nonnegative form** on every integrable `W`, for
coordinates bounded by `1`, a probability measure `ν` and `c ≥ 0`. -/
theorem quad_nonneg (hφ : ∀ p, Measurable (φ p)) (hb : ∀ p z, |φ p z| ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) (hW : Integrable W μ) :
    0 ≤ ∫ x, (∫ y, avgKern ν φ c x y * W y ∂μ) * W x ∂μ :=
  ge_of_tendsto' (tendsto_quadTrunc hφ hb hc hW) fun N => quadTrunc_nonneg hφ hb hc hW N

end Abstract

/-! ## 2. The Wilson transfer kernel -/

section Wilson

open MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.GaugeGroup

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The real (`true`) and imaginary (`false`) parts of the entries of `repM g`. -/
noncomputable def entryCoord (q : Fin (dim G) × Fin (dim G) × Bool) (g : G) : ℝ :=
  cond q.2.2 (repM G g q.1 q.2.1).re (repM G g q.1 q.2.1).im

theorem repM_inv (h : G) : repM G h⁻¹ = star (repM G h) := by
  have h1 : repM G h⁻¹ * repM G h = 1 := by rw [← repM_mul, inv_mul_cancel, repM_one]
  have h2 : repM G h * star (repM G h) = 1 := Matrix.mem_unitaryGroup_iff.1 (repM_mem h)
  calc repM G h⁻¹ = repM G h⁻¹ * (repM G h * star (repM G h)) := by rw [h2, mul_one]
    _ = star (repM G h) := by rw [← mul_assoc, h1, one_mul]

/-- `wilsonDensityG (g h⁻¹) = 1 − (1/d) ∑_q c_q(h) c_q(g)`. -/
theorem wilsonDensityG_mul_inv (g h : G) :
    wilsonDensityG G (g * h⁻¹) = 1 - (1 / (dim G : ℝ)) * ∑ q, entryCoord q h * entryCoord q g := by
  have key : (Matrix.trace (repM G (g * h⁻¹))).re = ∑ q, entryCoord q h * entryCoord q g := by
    rw [repM_mul, repM_inv, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply,
      Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    simp only [entryCoord, cond_true, cond_false]
    ring
  unfold wilsonDensityG
  rw [key]

theorem abs_entryCoord_le (q : Fin (dim G) × Fin (dim G) × Bool) (g : G) :
    |entryCoord q g| ≤ 1 := by
  rcases q with ⟨i, j, _ | _⟩
  · exact (Complex.abs_im_le_norm _).trans (entry_norm_bound_of_unitary (repM_mem g) i j)
  · exact (Complex.abs_re_le_norm _).trans (entry_norm_bound_of_unitary (repM_mem g) i j)

theorem continuous_entryCoord (q : Fin (dim G) × Fin (dim G) × Bool) :
    Continuous (entryCoord (G := G) q) := by
  rcases q with ⟨i, j, _ | _⟩
  · show Continuous fun g => (repM G g i j).im
    exact Complex.continuous_im.comp (continuous_repM.matrix_elem i j)
  · show Continuous fun g => (repM G g i j).re
    exact Complex.continuous_re.comp (continuous_repM.matrix_elem i j)

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- The gauge transformation of a slice by an axis configuration:
`(A · V)_{(ν, y)} = A_y V_{(ν, y)} A_{y+ν}⁻¹`. -/
def gaugeAct (A : TT μ T → G) (V : SpT μ T → G) : SpT μ T → G :=
  fun l => A l.2 * V l * (A (tsh μ T l.1 l.2))⁻¹

/-- The crossing energy `E(V, V') = ∑_l wilsonDensityG (V'_l V_l⁻¹)`. -/
noncomputable def crossEnergy (V V' : SpT μ T → G) : ℝ :=
  ∑ l, wilsonDensityG G (V' l * (V l)⁻¹)

theorem tpTG_eq (A : TT μ T → G) (V V' : SpT μ T → G) :
    tpTG G μ T A V V' = crossEnergy V (gaugeAct A V') := by
  unfold tpTG crossEnergy gaugeAct
  rw [Fintype.sum_prod_type]

theorem crossEnergy_act (B : TT μ T → G) (V V' : SpT μ T → G) :
    crossEnergy (gaugeAct B V) (gaugeAct B V') = crossEnergy V V' := by
  unfold crossEnergy
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : gaugeAct B V' l * (gaugeAct B V l)⁻¹ = B l.2 * (V' l * (V l)⁻¹) * (B l.2)⁻¹ := by
    simp only [gaugeAct]
    group
  rw [h, wilsonDensityG_conj]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem gaugeAct_gaugeAct (A B : TT μ T → G) (V : SpT μ T → G) :
    gaugeAct B (gaugeAct A V) = gaugeAct (B * A) V := by
  funext l
  simp only [gaugeAct, Pi.mul_apply]
  group

theorem integral_mul_left_hAG (B : TT μ T → G) (f : (TT μ T → G) → ℝ) :
    ∫ A, f (B * A) ∂(hAG G μ T) = ∫ A, f A ∂(hAG G μ T) :=
  integral_mul_left_eq_self f B

/-- `gkG` is the average over two independent axis configurations of the crossing weight. -/
theorem gkG_eq_avg (β : ℝ) (x y : SpT μ T → G) :
    gkG G μ T β x y = ∫ B, ∫ A, Real.exp (-β * (2 * crossEnergy (gaugeAct B x) (gaugeAct A y)))
      ∂(hAG G μ T) ∂(hAG G μ T) := by
  have h : ∀ B, gkG G μ T β x y =
      ∫ A, Real.exp (-β * (2 * crossEnergy (gaugeAct B x) (gaugeAct A y))) ∂(hAG G μ T) := by
    intro B
    unfold gkG
    refine Eq.trans ?_ (integral_mul_left_hAG B
      fun A => Real.exp (-β * (2 * crossEnergy (gaugeAct B x) (gaugeAct A y))))
    refine integral_congr_ae (Eventually.of_forall fun A => ?_)
    show Real.exp (-β * (2 * tpTG G μ T A x y)) =
      Real.exp (-β * (2 * crossEnergy (gaugeAct B x) (gaugeAct (B * A) y)))
    rw [tpTG_eq, ← gaugeAct_gaugeAct, crossEnergy_act]
  calc gkG G μ T β x y = ∫ _B : TT μ T → G, gkG G μ T β x y ∂(hAG G μ T) := by
        rw [integral_const, probReal_univ, one_smul]
    _ = _ := integral_congr_ae (Eventually.of_forall h)

/-- The coordinates of the crossing kernel: `φ_{(l, q)}(x, B) = c_q((B · x)_l)`. -/
noncomputable def actCoord (i : SpT μ T × (Fin (dim G) × Fin (dim G) × Bool))
    (p : (SpT μ T → G) × (TT μ T → G)) : ℝ :=
  entryCoord i.2 (gaugeAct p.2 p.1 i.1)

theorem coordKernel_actCoord (x y : SpT μ T → G) (B A : TT μ T → G) :
    coordKernel (actCoord (G := G) (μ := μ) (T := T)) (x, B) (y, A) =
      ∑ l, ∑ q, entryCoord q (gaugeAct B x l) * entryCoord q (gaugeAct A y l) :=
  Fintype.sum_prod_type _

theorem crossEnergy_eq (x y : SpT μ T → G) (B A : TT μ T → G) :
    crossEnergy (gaugeAct B x) (gaugeAct A y) =
      Fintype.card (SpT μ T) - (1 / (dim G : ℝ)) * coordKernel actCoord (x, B) (y, A) := by
  rw [coordKernel_actCoord]
  unfold crossEnergy
  simp only [wilsonDensityG_mul_inv]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

theorem exp_crossEnergy (β : ℝ) (x y : SpT μ T → G) (B A : TT μ T → G) :
    Real.exp (-β * (2 * crossEnergy (gaugeAct B x) (gaugeAct A y))) =
      Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
        Real.exp (2 * β / (dim G : ℝ) * coordKernel actCoord (x, B) (y, A)) := by
  rw [crossEnergy_eq, ← Real.exp_add]
  congr 1
  ring

/-- `gkG = e^{−2β |SpT|} · avgKern hAG actCoord (2β/d)`. -/
theorem gkG_eq_avgKern (β : ℝ) (x y : SpT μ T → G) :
    gkG G μ T β x y = Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
      avgKern (hAG G μ T) actCoord (2 * β / (dim G : ℝ)) x y := by
  rw [gkG_eq_avg]
  unfold avgKern
  simp_rw [exp_crossEnergy, integral_const_mul]

theorem continuous_actCoord (i : SpT μ T × (Fin (dim G) × Fin (dim G) × Bool)) :
    Continuous (actCoord (G := G) (μ := μ) (T := T) i) := by
  obtain ⟨l, q⟩ := i
  have e1 : Continuous fun p : (SpT μ T → G) × (TT μ T → G) => p.2 l.2 :=
    (continuous_apply _).comp continuous_snd
  have e2 : Continuous fun p : (SpT μ T → G) × (TT μ T → G) => p.1 l :=
    (continuous_apply _).comp continuous_fst
  have e3 : Continuous fun p : (SpT μ T → G) × (TT μ T → G) => p.2 (tsh μ T l.1 l.2) :=
    (continuous_apply _).comp continuous_snd
  exact (continuous_entryCoord q).comp ((e1.mul e2).mul e3.inv)

/-- **The Wilson transfer kernel is a positive operator.** For `β ≥ 0` and every integrable
function `u` of one slice, `∫∫ u(x) kTG(x, y) u(y) dx dy ≥ 0`. -/
theorem kTG_quad_nonneg {β : ℝ} (hβ : 0 ≤ β) {u : (SpT μ T → G) → ℝ}
    (hu : Integrable u (hSG G μ T)) :
    0 ≤ ∫ x, (∫ y, kTG G μ T β x y * u y ∂(hSG G μ T)) * u x ∂(hSG G μ T) := by
  have hwm : Measurable fun x : SpT μ T → G => Real.exp (-β * spTG G μ T x / 2) :=
    (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_spG continuous_id)).div_const _)).measurable
  have hW : Integrable (fun x => Real.exp (-β * spTG G μ T x / 2) * u x) (hSG G μ T) :=
    hu.bdd_mul hwm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.2 ?_
      have := spG_nonneg (G := G) (μ := μ) (T := T) x
      nlinarith [mul_nonneg hβ this])
  have hc : 0 ≤ 2 * β / (dim G : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have key := quad_nonneg (ν := hAG G μ T) (φ := actCoord)
    (fun i => (continuous_actCoord i).measurable) (fun i p => abs_entryCoord_le _ _) hc hW
  have h : ∀ x, (∫ y, kTG G μ T β x y * u y ∂(hSG G μ T)) * u x =
      Real.exp (-β * (2 * Fintype.card (SpT μ T))) *
        ((∫ y, avgKern (hAG G μ T) actCoord (2 * β / (dim G : ℝ)) x y *
          (Real.exp (-β * spTG G μ T y / 2) * u y) ∂(hSG G μ T)) *
          (Real.exp (-β * spTG G μ T x / 2) * u x)) := by
    intro x
    have hf : (fun y => kTG G μ T β x y * u y) = fun y =>
        (Real.exp (-β * spTG G μ T x / 2) * Real.exp (-β * (2 * Fintype.card (SpT μ T)))) *
          (avgKern (hAG G μ T) actCoord (2 * β / (dim G : ℝ)) x y *
            (Real.exp (-β * spTG G μ T y / 2) * u y)) := by
      funext y
      unfold kTG
      rw [gkG_eq_avgKern]
      ring
    rw [hf, integral_const_mul]
    ring
  rw [integral_congr_ae (Eventually.of_forall h), integral_const_mul]
  exact mul_nonneg (Real.exp_pos _).le key

end Wilson

end MassGap.PurityKernelPositive

#print axioms MassGap.PurityKernelPositive.abs_expTrunc_le
#print axioms MassGap.PurityKernelPositive.tendsto_expTrunc
#print axioms MassGap.PurityKernelPositive.expTrunc_coordKernel
#print axioms MassGap.PurityKernelPositive.avgKernTrunc_eq
#print axioms MassGap.PurityKernelPositive.tendsto_avgKernTrunc
#print axioms MassGap.PurityKernelPositive.quadTrunc_nonneg
#print axioms MassGap.PurityKernelPositive.tendsto_quadTrunc
#print axioms MassGap.PurityKernelPositive.quad_nonneg
#print axioms MassGap.PurityKernelPositive.wilsonDensityG_mul_inv
#print axioms MassGap.PurityKernelPositive.tpTG_eq
#print axioms MassGap.PurityKernelPositive.crossEnergy_act
#print axioms MassGap.PurityKernelPositive.gkG_eq_avg
#print axioms MassGap.PurityKernelPositive.gkG_eq_avgKern
#print axioms MassGap.PurityKernelPositive.kTG_quad_nonneg
