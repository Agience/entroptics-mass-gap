import Mathlib
import MassGap.JentzschKT
import MassGap.KernelPower
import MassGap.PurityTrace

/-!
# MassGap.PurityRayleigh — the bound (6.1) of Proposition 6.1 for a `DAD` kernel

Proposition 6.1, (6.1), of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit
8e01510, `Paper-2/Paper-2.pdf`).

Setting: a probability measure `μ`, a bounded measurable `D`, a jointly measurable `A` with values
in `[a, b]`, `0 < a`, the kernel `k x y = D x · A x y · D y` acting on `L²(μ)` as `kernelCLM`, and
`S = ∫ D² > 0`. With `dint w = ∫∫ D(x)² w(x, y) D(y)² dμ dμ`:

* `rayleigh`: `∫ (∫ k x y g y) g x ≤ ‖K‖ ∫ g²` for every bounded measurable `g`.
* `rayleigh_dad`: `dint A ≤ ‖K‖ S` (the trial function `D`; paper: `λ₀ ≥ Sµ`,
  `µ = ∫ A d(σ ⊗ σ) = dint A / S²`).
* `hs_dad`: `‖K‖²_HS = KernelPower.hs μ k = ∫∫ k² = dint (A²)`; `traceSeq_two`:
  `traceSeq μ k 2 = hs μ k`. For symmetric `A` this is the paper's `Tr K² = S² ∫ A² d(σ ⊗ σ)`.
* `dint_lin`, `dint_nonneg`, `dint_one` (`dint 1 = S²`); `dint_bounds`: `a S² ≤ dint A ≤ b S²`;
  `bhatia_davis`: `dint (A²) ≤ (a + b) dint A − a b S²`.
* `trace_ratio_var`: `‖K‖²_HS/‖K‖² − 1 ≤ S² dint (A²)/(dint A)² − 1`, the first relation of (6.1);
  the right side is `Var_{σ⊗σ}(A)/µ²`.
* `trace_ratio_le`: `‖K‖²_HS/‖K‖² − 1 ≤ (b − a)²/(4ab)`, the first and second relations of (6.1)
  combined, through Bhatia–Davis.
* Helpers: `weighted`, `abs_A_le`, `abs_A_sq_le`.

For symmetric `A`, `‖K‖²_HS = Tr K²`, and with `R = K/‖K‖` the left sides are `Tr R² − 1`.

DERIVED (module-wide): `2` the `L²` exponent and the square; `1` the constant weight; `4` from
`PurityTrace.ratio_le`.
-/

namespace MassGap.PurityRayleigh

open MeasureTheory Real MassGap.SlabKernelOperator MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **Rayleigh bound.** For a bounded measurable `g`, `∫ (K g) g ≤ ‖K‖ ∫ g²`. -/
theorem rayleigh {k : X → X → ℝ} {C : ℝ} (hk : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |k x y| ≤ C) {g : X → ℝ} (hg : Measurable g) {M : ℝ} (hgb : ∀ x, |g x| ≤ M) :
    ∫ x, (∫ y, k x y * g y ∂μ) * g x ∂μ
      ≤ ‖kernelCLM k C hk hC0 hkb μ μ‖ * ∫ x, g x ^ 2 ∂μ := by
  have hm : MemLp g 2 μ := MemLp.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgb x)
  set f := hm.toLp g
  have hf : (f : X → ℝ) =ᵐ[μ] g := hm.coeFn_toLp
  have hK : ∀ x, kernelFun k μ (f : X → ℝ) x = ∫ y, k x y * g y ∂μ := by
    intro x
    unfold kernelFun
    refine integral_congr_ae ?_
    filter_upwards [hf] with y hy
    rw [hy]
  have hin : (inner ℝ (kernelCLM k C hk hC0 hkb μ μ f) f : ℝ)
      = ∫ x, (∫ y, k x y * g y ∂μ) * g x ∂μ := by
    rw [MassGap.JentzschKT.inner_kernelCLM_eq hk hC0 hkb f f]
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hK x, hx]
  have hn : ‖f‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [SlabTransferAdjoint.norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
  rw [← hin, ← hn]
  calc (inner ℝ (kernelCLM k C hk hC0 hkb μ μ f) f : ℝ)
      ≤ ‖kernelCLM k C hk hC0 hkb μ μ f‖ * ‖f‖ := real_inner_le_norm _ _
    _ ≤ ‖kernelCLM k C hk hC0 hkb μ μ‖ * ‖f‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖kernelCLM k C hk hC0 hkb μ μ‖ * ‖f‖ ^ 2 := by ring

/-- The `D²`-weighted double integral `dint w = ∫∫ D(x)² w(x, y) D(y)²`. -/
noncomputable def dint (μ : Measure X) (D : X → ℝ) (w : X → X → ℝ) : ℝ :=
  ∫ x, ∫ y, D x ^ 2 * w x y * D y ^ 2 ∂μ ∂μ

omit [IsProbabilityMeasure μ] in
theorem dint_nonneg (D : X → ℝ) {w : X → X → ℝ} (hw : ∀ x y, 0 ≤ w x y) : 0 ≤ dint μ D w :=
  integral_nonneg fun x => integral_nonneg fun y =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (hw x y)) (sq_nonneg _)

omit [IsProbabilityMeasure μ] in
/-- `dint 1 = S²`. -/
theorem dint_one (D : X → ℝ) : dint μ D (fun _ _ => 1) = (∫ x, D x ^ 2 ∂μ) ^ 2 := by
  unfold dint
  simp only [mul_one, integral_const_mul, integral_mul_const]
  ring

/-- A weighted bounded kernel is bounded and jointly measurable. -/
theorem weighted {D : X → ℝ} (hD : Measurable D) {M : ℝ} (hDb : ∀ x, |D x| ≤ M)
    {w : X → X → ℝ} (hw : Measurable (Function.uncurry w)) {c : ℝ} (hb : ∀ x y, |w x y| ≤ c) :
    Measurable (Function.uncurry fun x y => D x ^ 2 * w x y * D y ^ 2) ∧
      ∀ x y, |D x ^ 2 * w x y * D y ^ 2| ≤ M ^ 2 * c * M ^ 2 := by
  have hD2 : ∀ x, D x ^ 2 ≤ M ^ 2 := fun x => by
    have := hDb x
    nlinarith [abs_nonneg (D x), sq_abs (D x)]
  refine ⟨(((hD.comp measurable_fst).pow_const 2).mul hw).mul
    ((hD.comp measurable_snd).pow_const 2), fun x y => ?_⟩
  have hc : 0 ≤ c := (abs_nonneg _).trans (hb x y)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (D x)), abs_of_nonneg (sq_nonneg (D y))]
  exact mul_le_mul (mul_le_mul (hD2 x) (hb x y) (abs_nonneg _) (sq_nonneg _)) (hD2 y)
    (sq_nonneg _) (mul_nonneg (sq_nonneg _) hc)

/-- `dint` is linear on bounded measurable weights. -/
theorem dint_lin {D : X → ℝ} (hD : Measurable D) {M : ℝ} (hDb : ∀ x, |D x| ≤ M)
    {w₁ w₂ : X → X → ℝ} (h₁ : Measurable (Function.uncurry w₁))
    (h₂ : Measurable (Function.uncurry w₂)) {c₁ c₂ : ℝ} (hb₁ : ∀ x y, |w₁ x y| ≤ c₁)
    (hb₂ : ∀ x y, |w₂ x y| ≤ c₂) (α β : ℝ) :
    dint μ D (fun x y => α * w₁ x y + β * w₂ x y) = α * dint μ D w₁ + β * dint μ D w₂ := by
  obtain ⟨m₁, b₁⟩ := weighted hD hDb h₁ hb₁
  obtain ⟨m₂, b₂⟩ := weighted hD hDb h₂ hb₂
  have i₁ : ∀ x, Integrable (fun y => D x ^ 2 * w₁ x y * D y ^ 2) μ := fun x =>
    integrable_of_bdd (m₁.comp measurable_prodMk_left) (b₁ x)
  have i₂ : ∀ x, Integrable (fun y => D x ^ 2 * w₂ x y * D y ^ 2) μ := fun x =>
    integrable_of_bdd (m₂.comp measurable_prodMk_left) (b₂ x)
  have o₁ : Integrable (fun x => ∫ y, D x ^ 2 * w₁ x y * D y ^ 2 ∂μ) μ :=
    integrable_of_bdd (measurable_integral_right m₁) (fun x => abs_integral_le (b₁ x))
  have o₂ : Integrable (fun x => ∫ y, D x ^ 2 * w₂ x y * D y ^ 2 ∂μ) μ :=
    integrable_of_bdd (measurable_integral_right m₂) (fun x => abs_integral_le (b₂ x))
  have hx : ∀ x, ∫ y, D x ^ 2 * (α * w₁ x y + β * w₂ x y) * D y ^ 2 ∂μ
      = α * (∫ y, D x ^ 2 * w₁ x y * D y ^ 2 ∂μ) + β * ∫ y, D x ^ 2 * w₂ x y * D y ^ 2 ∂μ := by
    intro x
    calc ∫ y, D x ^ 2 * (α * w₁ x y + β * w₂ x y) * D y ^ 2 ∂μ
        = ∫ y, (α * (D x ^ 2 * w₁ x y * D y ^ 2) + β * (D x ^ 2 * w₂ x y * D y ^ 2)) ∂μ := by
          congr 1
          funext y
          ring
      _ = _ := by
          rw [integral_add ((i₁ x).const_mul α) ((i₂ x).const_mul β), integral_const_mul,
            integral_const_mul]
  unfold dint
  calc ∫ x, ∫ y, D x ^ 2 * (α * w₁ x y + β * w₂ x y) * D y ^ 2 ∂μ ∂μ
      = ∫ x, (α * (∫ y, D x ^ 2 * w₁ x y * D y ^ 2 ∂μ)
          + β * ∫ y, D x ^ 2 * w₂ x y * D y ^ 2 ∂μ) ∂μ := by
        congr 1
        funext x
        exact hx x
    _ = _ := by
        rw [integral_add (o₁.const_mul α) (o₂.const_mul β), integral_const_mul,
          integral_const_mul]

omit [MeasurableSpace X] in
theorem abs_A_le {A : X → X → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : ∀ x y, A x y ∈ Set.Icc a b) (x y : X) : |A x y| ≤ b :=
  abs_le.mpr ⟨by linarith [(hab x y).1, (hab x y).2], (hab x y).2⟩

omit [MeasurableSpace X] in
theorem abs_A_sq_le {A : X → X → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : ∀ x y, A x y ∈ Set.Icc a b) (x y : X) : |A x y ^ 2| ≤ b ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h1 := (hab x y).1
  have h2 := (hab x y).2
  nlinarith

section DAD

variable {D : X → ℝ} (hD : Measurable D) {M : ℝ} (hDb : ∀ x, |D x| ≤ M)
  {A : X → X → ℝ} (hA : Measurable (Function.uncurry A)) {a b : ℝ} (ha : 0 < a)
  (hab : ∀ x y, A x y ∈ Set.Icc a b)
include hD hDb hA ha hab

/-- `a S² ≤ dint A ≤ b S²`. -/
theorem dint_bounds :
    a * (∫ x, D x ^ 2 ∂μ) ^ 2 ≤ dint μ D A ∧ dint μ D A ≤ b * (∫ x, D x ^ 2 ∂μ) ^ 2 := by
  have h1 : Measurable (Function.uncurry fun (_ : X) (_ : X) => (1 : ℝ)) := measurable_const
  have hb1 : ∀ x y : X, |(fun (_ : X) (_ : X) => (1 : ℝ)) x y| ≤ 1 := fun _ _ => by simp
  have hA' := abs_A_le ha hab
  constructor
  · have hn := dint_nonneg (μ := μ) D (w := fun x y => 1 * A x y + (-a) * 1)
      (fun x y => by linarith [(hab x y).1])
    rw [dint_lin hD hDb hA h1 hA' hb1, dint_one] at hn
    linarith
  · have hn := dint_nonneg (μ := μ) D (w := fun x y => (-1) * A x y + b * 1)
      (fun x y => by linarith [(hab x y).2])
    rw [dint_lin hD hDb hA h1 hA' hb1, dint_one] at hn
    linarith

/-- **Bhatia–Davis, integrated.** `dint (A²) ≤ (a + b) dint A − a b S²`. -/
theorem bhatia_davis :
    dint μ D (fun x y => A x y ^ 2)
      ≤ (a + b) * dint μ D A - a * b * (∫ x, D x ^ 2 ∂μ) ^ 2 := by
  have h1 : Measurable (Function.uncurry fun (_ : X) (_ : X) => (1 : ℝ)) := measurable_const
  have hb1 : ∀ x y : X, |(fun (_ : X) (_ : X) => (1 : ℝ)) x y| ≤ 1 := fun _ _ => by simp
  have hA' := abs_A_le ha hab
  have hA2 : Measurable (Function.uncurry fun x y => A x y ^ 2) := hA.pow_const 2
  have hA2' := abs_A_sq_le ha hab
  have hc : Measurable (Function.uncurry fun x y => (-1) * A x y ^ 2 + (-(a * b)) * 1) :=
    (measurable_const.mul hA2).add (measurable_const.mul measurable_const)
  have hcb : ∀ x y, |(-1) * A x y ^ 2 + (-(a * b)) * 1| ≤ b ^ 2 + a * b := fun x y => by
    have e1 := (hab x y).1
    have e2 := (hab x y).2
    rw [abs_le]
    constructor <;> nlinarith
  have hn := dint_nonneg (μ := μ) D (w := fun x y => (A x y - a) * (b - A x y))
    (fun x y => mul_nonneg (by linarith [(hab x y).1]) (by linarith [(hab x y).2]))
  have e : dint μ D (fun x y => (A x y - a) * (b - A x y))
      = dint μ D (fun x y => (a + b) * A x y + 1 * ((-1) * A x y ^ 2 + (-(a * b)) * 1)) := by
    congr 1
    funext x y
    ring
  rw [e, dint_lin hD hDb hA hc hA' hcb, dint_lin hD hDb hA2 h1 hA2' hb1, dint_one] at hn
  linarith

variable {k : X → X → ℝ} (hkdef : ∀ x y, k x y = D x * A x y * D y) {C : ℝ}
  (hk : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C)
include hkdef

omit hA ha hab in
/-- **Rayleigh with the trial function `D`**: `dint A ≤ ‖K‖ S` (paper: `λ₀ ≥ Sµ`). -/
theorem rayleigh_dad :
    dint μ D A ≤ ‖kernelCLM k C hk hC0 hkb μ μ‖ * ∫ x, D x ^ 2 ∂μ := by
  have h := rayleigh (μ := μ) hk hC0 hkb hD hDb
  have e : ∫ x, (∫ y, k x y * D y ∂μ) * D x ∂μ = dint μ D A := by
    unfold dint
    congr 1
    funext x
    rw [← integral_mul_const]
    congr 1
    funext y
    rw [hkdef]
    ring
  rwa [e] at h

omit [IsProbabilityMeasure μ] hD hDb hA ha hab in
/-- `‖K‖²_HS = ∫∫ k² = dint (A²)`; for symmetric `A` this is `Tr K² = S² ∫ A² d(σ ⊗ σ)`. -/
theorem hs_dad : hs μ k = dint μ D (fun x y => A x y ^ 2) := by
  unfold hs dint
  congr 1
  funext x
  congr 1
  funext z
  rw [hkdef]
  ring

omit [IsProbabilityMeasure μ] in
omit hD hDb hA ha hab hkdef in
theorem traceSeq_two : traceSeq μ k 2 = hs μ k := rfl

/-- **Proposition 6.1, first relation of (6.1).** `‖K‖²_HS/‖K‖² − 1 ≤ S² dint (A²)/(dint A)² − 1`,
the right side being `Var_{σ⊗σ}(A)/µ²`. -/
theorem trace_ratio_var (hS : 0 < ∫ x, D x ^ 2 ∂μ) :
    traceSeq μ k 2 / ‖kernelCLM k C hk hC0 hkb μ μ‖ ^ 2 - 1
      ≤ (∫ x, D x ^ 2 ∂μ) ^ 2 * dint μ D (fun x y => A x y ^ 2) / dint μ D A ^ 2 - 1 := by
  set S := ∫ x, D x ^ 2 ∂μ
  set N := ‖kernelCLM k C hk hC0 hkb μ μ‖
  have hR := rayleigh_dad (μ := μ) hD hDb hkdef hk hC0 hkb
  obtain ⟨hlo, -⟩ := dint_bounds (μ := μ) hD hDb hA ha hab
  have hP : 0 < dint μ D A := lt_of_lt_of_le (by positivity) hlo
  have hq : 0 < dint μ D A / S := div_pos hP hS
  have hN : dint μ D A / S ≤ N := (div_le_iff₀ hS).mpr hR
  have hs0 : 0 ≤ hs μ k := hs_nonneg k
  rw [traceSeq_two, ← hs_dad (μ := μ) hkdef]
  have h1 : hs μ k / N ^ 2 ≤ hs μ k / (dint μ D A / S) ^ 2 :=
    div_le_div_of_nonneg_left hs0 (pow_pos hq 2) (pow_le_pow_left₀ hq.le hN 2)
  have e : hs μ k / (dint μ D A / S) ^ 2 = S ^ 2 * hs μ k / dint μ D A ^ 2 := by
    rw [div_pow, div_div_eq_mul_div]
    ring
  linarith

/-- **Proposition 6.1, (6.1), first and second relations combined.**
`‖K‖²_HS/‖K‖² − 1 ≤ (b − a)²/(4ab)`; for symmetric `A`, with `R = K/‖K‖`, this is
`Tr R² − 1 ≤ (b − a)²/(4ab)`. -/
theorem trace_ratio_le (hS : 0 < ∫ x, D x ^ 2 ∂μ) :
    traceSeq μ k 2 / ‖kernelCLM k C hk hC0 hkb μ μ‖ ^ 2 - 1 ≤ (b - a) ^ 2 / (4 * a * b) := by
  set S := ∫ x, D x ^ 2 ∂μ with hSdef
  set N := ‖kernelCLM k C hk hC0 hkb μ μ‖
  have hR := rayleigh_dad (μ := μ) hD hDb hkdef hk hC0 hkb
  obtain ⟨hlo, hhi⟩ := dint_bounds (μ := μ) hD hDb hA ha hab
  have hBD := bhatia_davis (μ := μ) hD hDb hA ha hab
  have hHS := hs_dad (μ := μ) hkdef
  have hS2 : 0 < S ^ 2 := pow_pos hS 2
  set m := dint μ D A / S ^ 2 with hm
  have hN1 : dint μ D A = m * S ^ 2 := by rw [hm]; field_simp
  rw [hN1] at hR hlo hhi hBD
  have hma : a ≤ m := le_of_mul_le_mul_right hlo hS2
  have hmb : m ≤ b := le_of_mul_le_mul_right hhi hS2
  have hm0 : 0 < m := lt_of_lt_of_le ha hma
  have hmS : m * S ≤ N := le_of_mul_le_mul_right (by nlinarith) hS
  have hmS0 : 0 < m * S := mul_pos hm0 hS
  have hN0 : 0 < N := lt_of_lt_of_le hmS0 hmS
  have hs0 : 0 ≤ hs μ k := by
    rw [hHS]
    exact dint_nonneg D (fun x y => sq_nonneg _)
  have hK2 : (m * S) ^ 2 ≤ N ^ 2 := by nlinarith
  rw [traceSeq_two]
  have h1 : hs μ k / N ^ 2 ≤ hs μ k / (m * S) ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hN0 2) (pow_pos hmS0 2)]
    exact mul_le_mul_of_nonneg_left hK2 hs0
  have h2 : hs μ k / (m * S) ^ 2 ≤ ((a + b) * m - a * b) / m ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hmS0 2) (pow_pos hm0 2), hHS]
    have hBD' : dint μ D (fun x y => A x y ^ 2) ≤ ((a + b) * m - a * b) * S ^ 2 := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hBD' (sq_nonneg m)]
  calc hs μ k / N ^ 2 - 1 ≤ ((a + b) * m - a * b) / m ^ 2 - 1 := by linarith
    _ = (b - m) * (m - a) / m ^ 2 := by
        rw [div_sub_one (pow_ne_zero 2 hm0.ne')]
        congr 1
        ring
    _ ≤ (b - a) ^ 2 / (4 * a * b) := MassGap.PurityTrace.ratio_le ha hma hmb

end DAD

end MassGap.PurityRayleigh

#print axioms MassGap.PurityRayleigh.rayleigh
#print axioms MassGap.PurityRayleigh.dint_nonneg
#print axioms MassGap.PurityRayleigh.dint_one
#print axioms MassGap.PurityRayleigh.weighted
#print axioms MassGap.PurityRayleigh.dint_lin
#print axioms MassGap.PurityRayleigh.abs_A_le
#print axioms MassGap.PurityRayleigh.abs_A_sq_le
#print axioms MassGap.PurityRayleigh.dint_bounds
#print axioms MassGap.PurityRayleigh.bhatia_davis
#print axioms MassGap.PurityRayleigh.rayleigh_dad
#print axioms MassGap.PurityRayleigh.hs_dad
#print axioms MassGap.PurityRayleigh.traceSeq_two
#print axioms MassGap.PurityRayleigh.trace_ratio_var
#print axioms MassGap.PurityRayleigh.trace_ratio_le
