import Mathlib
import MassGap.KernelPower

/-!
# MassGap.PurityTailIdentity — the finite-rank matrix certificate

(D.2) and (D.3) of Appendix D of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov,
I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling*
(research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510,
`Paper-2/Paper-2.pdf`).

For a bounded measurable kernel `k` on a probability space and an orthonormal family
`φ₀, …, φ_{m−1}` of bounded measurable functions, `gram μ k φ i j = ⟨φᵢ, K φⱼ⟩` is the matrix
`G` and `proj μ k φ x z = ∑ᵢⱼ Gᵢⱼ φᵢ(x) φⱼ(z)` is the kernel of `P_m K P_m`.

* `sq_lin`: `∫ (∑ⱼ aⱼ φⱼ)² = ∑ⱼ aⱼ²`. `res_sq`: `∫ (k(x,·) − ∑ⱼ aⱼ φⱼ)² = ∫ k(x,·)² − 2 ∑ⱼ aⱼ (K φⱼ)(x)
  + ∑ⱼ aⱼ²`.
* `tail` (D.2), the matrix certificate: `hs (k − proj) = hs k − ∑ᵢⱼ Gᵢⱼ²`.
* `bessel`: `∑ᵢⱼ Gᵢⱼ² ≤ hs k`.
* `tail_right`: `hs (k − K P_m) = hs k − ∑ᵢ ‖K φᵢ‖²`. `tail_left` (symmetric `k`), the tail
  identity: `‖(I − P_m) K‖²_HS = hs k − ∑ᵢ ‖K φᵢ‖²`; with `Kᵀ = K`, `∑ᵢ ‖K φᵢ‖² = Tr(P_m K²)`.
  `res_bdd` and `KernelPower.hs_swap` (`‖Kᵀ‖²_HS = ‖K‖²_HS`) are the supporting lemmas.
* `tail_le`: an upper bound `U` on `hs k` and a lower bound `L` on `∑ᵢⱼ Gᵢⱼ²` give
  `hs (k − proj) ≤ U − L`.
* `window` (D.3): `0 ≤ d ≤ exp(V/(322 (48T)³)) − 1` gives `2 log(1 + d) ≤ V/(161 (48T)³)`.
-/

namespace MassGap.PurityTailIdentity

open MeasureTheory Real MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- `row μ k φ j x = (K φⱼ)(x) = ∫ k(x,z) φⱼ(z) dμ(z)`. -/
noncomputable def row (μ : Measure X) (k : X → X → ℝ) {m : ℕ} (φ : Fin m → X → ℝ) (j : Fin m) :
    X → ℝ :=
  fun x => ∫ z, k x z * φ j z ∂μ

/-- The matrix `Gᵢⱼ = ⟨φᵢ, K φⱼ⟩`. -/
noncomputable def gram (μ : Measure X) (k : X → X → ℝ) {m : ℕ} (φ : Fin m → X → ℝ)
    (i j : Fin m) : ℝ :=
  ∫ x, φ i x * row μ k φ j x ∂μ

/-- `coef μ k φ j x = ∑ᵢ Gᵢⱼ φᵢ(x)`. -/
noncomputable def coef (μ : Measure X) (k : X → X → ℝ) {m : ℕ} (φ : Fin m → X → ℝ) (j : Fin m) :
    X → ℝ :=
  fun x => ∑ i, gram μ k φ i j * φ i x

/-- The kernel of `P_m K P_m`. -/
noncomputable def proj (μ : Measure X) (k : X → X → ℝ) {m : ℕ} (φ : Fin m → X → ℝ) :
    X → X → ℝ :=
  fun x z => ∑ j, coef μ k φ j x * φ j z

omit [IsProbabilityMeasure μ] in
theorem proj_eq (k : X → X → ℝ) {m : ℕ} (φ : Fin m → X → ℝ) (x z : X) :
    proj μ k φ x z = ∑ i, ∑ j, gram μ k φ i j * φ i x * φ j z := by
  simp only [proj, coef, Finset.sum_mul]
  exact Finset.sum_comm

section Family

variable {m : ℕ} {φ : Fin m → X → ℝ}

theorem lin_meas (hφm : ∀ i, Measurable (φ i)) (a : Fin m → ℝ) :
    Measurable (fun x => ∑ j, a j * φ j x) :=
  Finset.measurable_sum (f := fun j x => a j * φ j x) Finset.univ
    (fun j _ => (hφm j).const_mul (a j))

omit [MeasurableSpace X] in
theorem lin_bdd {B : ℝ} (hφb : ∀ i x, |φ i x| ≤ B) (a : Fin m → ℝ) (x : X) :
    |∑ j, a j * φ j x| ≤ ∑ j, |a j| * B :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb j x) (abs_nonneg _))

/-- **Parseval on a finite orthonormal family**: `∫ (∑ⱼ aⱼ φⱼ)² = ∑ⱼ aⱼ²`. -/
theorem sq_lin (hφm : ∀ i, Measurable (φ i)) {B : ℝ} (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) (a : Fin m → ℝ) :
    ∫ z, (∑ j, a j * φ j z) ^ 2 ∂μ = ∑ j, a j ^ 2 := by
  have e : (fun z => (∑ j, a j * φ j z) ^ 2)
      = fun z => ∑ i, ∑ j, a i * a j * (φ i z * φ j z) := by
    funext z
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint : ∀ i j, Integrable (fun z => a i * a j * (φ i z * φ j z)) μ := fun i j =>
    (integrable_mul_of_bdd (hφm i) (hφm j) (hφb i) (hφb j)).const_mul _
  rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  simp only [integral_const_mul, hon]
  simp [sq]

theorem row_meas {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) (j : Fin m) :
    Measurable (row μ k φ j) :=
  measurable_integral_right (μ := μ) (F := fun x z => k x z * φ j z)
    (hk.meas.mul ((hφm j).comp measurable_snd))

theorem row_bdd {k : X → X → ℝ} {C : ℝ} (hC : ∀ x z, |k x z| ≤ C) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B) (j : Fin m) (x : X) : |row μ k φ j x| ≤ C * B :=
  abs_integral_le fun z => by
    rw [abs_mul]; exact mul_le_mul (hC x z) (hφb j z) (abs_nonneg _) ((abs_nonneg _).trans (hC x z))

/-- **The residual of a row**: `∫ (k(x,·) − ∑ⱼ aⱼ φⱼ)² = ∫ k(x,·)² − 2 ∑ⱼ aⱼ (K φⱼ)(x) + ∑ⱼ aⱼ²`. -/
theorem res_sq {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) (x : X) (a : Fin m → ℝ) :
    ∫ z, (k x z - ∑ j, a j * φ j z) ^ 2 ∂μ
      = ∫ z, k x z ^ 2 ∂μ - 2 * ∑ j, a j * row μ k φ j x + ∑ j, a j ^ 2 := by
  obtain ⟨C, hC⟩ := hk.bdd
  have e : (fun z => (k x z - ∑ j, a j * φ j z) ^ 2) = fun z =>
      k x z ^ 2 - 2 * ∑ j, a j * (k x z * φ j z) + (∑ j, a j * φ j z) ^ 2 := by
    funext z
    have hm : k x z * ∑ j, a j * φ j z = ∑ j, a j * (k x z * φ j z) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [sub_sq, ← hm]; ring
  have i1 : Integrable (fun z => k x z ^ 2) μ :=
    integrable_of_bdd ((hk.row x).pow_const 2) (C := C ^ 2) (fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x z) 2)
  have i2j : ∀ j, Integrable (fun z => a j * (k x z * φ j z)) μ := fun j =>
    (integrable_mul_of_bdd (hk.row x) (hφm j) (hC x) (hφb j)).const_mul _
  have i2 : Integrable (fun z => 2 * ∑ j, a j * (k x z * φ j z)) μ :=
    (integrable_finsetSum _ fun j _ => i2j j).const_mul 2
  have i3 : Integrable (fun z => (∑ j, a j * φ j z) ^ 2) μ :=
    integrable_of_bdd ((lin_meas hφm _).pow_const 2) (C := (∑ j, |a j| * B) ^ 2) (fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (lin_bdd hφb _ z) 2)
  rw [e, integral_add (f := fun z => k x z ^ 2 - 2 * ∑ j, a j * (k x z * φ j z)) (i1.sub i2) i3,
    integral_sub i1 i2, integral_const_mul, integral_finsetSum _ fun j _ => i2j j,
    sq_lin hφm hφb hon a]
  simp only [integral_const_mul, row]

/-- **(D.2), the matrix certificate**: `‖K − P_m K P_m‖²_HS = ∫∫ k² − ∑ᵢⱼ Gᵢⱼ²`. -/
theorem tail {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) :
    hs μ (fun x z => k x z - proj μ k φ x z) = hs μ k - ∑ i, ∑ j, gram μ k φ i j ^ 2 := by
  obtain ⟨C, hC⟩ := hk.bdd
  have hrm := row_meas (μ := μ) hk hφm
  have hrb : ∀ j x, |row μ k φ j x| ≤ C * B := row_bdd hC hφb
  have hcm : ∀ j, Measurable (coef μ k φ j) := fun j => lin_meas hφm (fun i => gram μ k φ i j)
  have hcb : ∀ j x, |coef μ k φ j x| ≤ ∑ i, |gram μ k φ i j| * B := fun j x =>
    lin_bdd hφb (fun i => gram μ k φ i j) x
  have hpt : ∀ x, ∫ z, (k x z - proj μ k φ x z) ^ 2 ∂μ
      = ∫ z, k x z ^ 2 ∂μ - 2 * ∑ j, coef μ k φ j x * row μ k φ j x
        + ∑ j, coef μ k φ j x ^ 2 := fun x =>
    res_sq hk hφm hφb hon x (fun j => coef μ k φ j x)
  unfold hs
  simp_rw [hpt]
  have o1 : Integrable (fun x => ∫ z, k x z ^ 2 ∂μ) μ := integrable_rowsq hk
  have o2j : ∀ j, Integrable (fun x => coef μ k φ j x * row μ k φ j x) μ := fun j =>
    integrable_mul_of_bdd (hcm j) (hrm j) (hcb j) (hrb j)
  have o2 : Integrable (fun x => 2 * ∑ j, coef μ k φ j x * row μ k φ j x) μ :=
    (integrable_finsetSum _ fun j _ => o2j j).const_mul 2
  have o3j : ∀ j, Integrable (fun x => coef μ k φ j x ^ 2) μ := fun j =>
    integrable_of_bdd ((hcm j).pow_const 2) (C := (∑ i, |gram μ k φ i j| * B) ^ 2) (fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb j x) 2)
  have o3 : Integrable (fun x => ∑ j, coef μ k φ j x ^ 2) μ :=
    integrable_finsetSum _ fun j _ => o3j j
  have hc : ∀ j, ∫ x, coef μ k φ j x * row μ k φ j x ∂μ = ∑ i, gram μ k φ i j * gram μ k φ i j := by
    intro j
    simp only [coef, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_mul_of_bdd (hφm i) (hrm j) (hφb i) (hrb j)).const_mul _]
    simp only [integral_const_mul]
    rfl
  have hq2 : ∀ j, ∫ x, coef μ k φ j x ^ 2 ∂μ = ∑ i, gram μ k φ i j ^ 2 := fun j => by
    simp only [coef]; exact sq_lin hφm hφb hon _
  rw [integral_add (f := fun x => ∫ z, k x z ^ 2 ∂μ - 2 * ∑ j, coef μ k φ j x * row μ k φ j x)
    (o1.sub o2) o3, integral_sub o1 o2, integral_const_mul,
    integral_finsetSum _ fun j _ => o2j j, integral_finsetSum _ fun j _ => o3j j]
  simp only [hc, hq2]
  have s1 : ∑ j, ∑ i, gram μ k φ i j * gram μ k φ i j = ∑ i, ∑ j, gram μ k φ i j ^ 2 := by
    simp only [sq]; exact Finset.sum_comm
  have s2 : ∑ j, ∑ i, gram μ k φ i j ^ 2 = ∑ i, ∑ j, gram μ k φ i j ^ 2 := Finset.sum_comm
  rw [s1, s2]; ring

/-- **Bessel**: `∑ᵢⱼ Gᵢⱼ² ≤ ∫∫ k²`. -/
theorem bessel {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) :
    ∑ i, ∑ j, gram μ k φ i j ^ 2 ≤ hs μ k := by
  have h := hs_nonneg (μ := μ) (fun x z => k x z - proj μ k φ x z)
  rw [tail hk hφm hφb hon] at h
  linarith

/-- **The certified tail bound**: an upper bound on `∫∫ k²` and a lower bound on `∑ᵢⱼ Gᵢⱼ²`
bound `‖K − P_m K P_m‖²_HS`. -/
theorem tail_le {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) {U L : ℝ}
    (hU : hs μ k ≤ U) (hL : L ≤ ∑ i, ∑ j, gram μ k φ i j ^ 2) :
    hs μ (fun x z => k x z - proj μ k φ x z) ≤ U - L := by
  rw [tail hk hφm hφb hon]; linarith

/-- The kernel `k − ∑ᵢ (K φᵢ)(x) φᵢ(z)` of `K − K P_m` is bounded and jointly measurable. -/
theorem res_bdd {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B) :
    Bdd (fun x z => k x z - ∑ i, row μ k φ i x * φ i z) := by
  obtain ⟨C, hC⟩ := hk.bdd
  refine ⟨hk.meas.sub (Finset.measurable_sum (f := fun i (p : X × X) => row μ k φ i p.1 * φ i p.2)
    Finset.univ fun i _ => ((row_meas hk hφm i).comp measurable_fst).mul
      ((hφm i).comp measurable_snd)), C + ∑ _i : Fin m, C * B * B, fun x z => ?_⟩
  refine (abs_sub _ _).trans (add_le_add (hC x z) ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)))
  rw [abs_mul]
  exact mul_le_mul (row_bdd (μ := μ) hC hφb i x) (hφb i z) (abs_nonneg _)
    ((abs_nonneg _).trans (row_bdd (μ := μ) hC hφb i x))

/-- **The tail identity, right form**: `‖K − K P_m‖²_HS = ∫∫ k² − ∑ᵢ ‖K φᵢ‖²`. -/
theorem tail_right {k : X → X → ℝ} (hk : Bdd k) (hφm : ∀ i, Measurable (φ i)) {B : ℝ}
    (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) :
    hs μ (fun x z => k x z - ∑ i, row μ k φ i x * φ i z)
      = hs μ k - ∑ i, ∫ x, row μ k φ i x ^ 2 ∂μ := by
  obtain ⟨C, hC⟩ := hk.bdd
  have hpt : ∀ x, ∫ z, (k x z - ∑ i, row μ k φ i x * φ i z) ^ 2 ∂μ
      = ∫ z, k x z ^ 2 ∂μ - ∑ i, row μ k φ i x ^ 2 := fun x => by
    rw [res_sq hk hφm hφb hon x (fun i => row μ k φ i x)]; simp only [sq]; ring
  unfold hs
  simp_rw [hpt]
  have o1 : Integrable (fun x => ∫ z, k x z ^ 2 ∂μ) μ := integrable_rowsq hk
  have oj : ∀ i, Integrable (fun x => row μ k φ i x ^ 2) μ := fun i =>
    integrable_of_bdd ((row_meas hk hφm i).pow_const 2) (C := (C * B) ^ 2) (fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (row_bdd hC hφb i x) 2)
  rw [integral_sub o1 (integrable_finsetSum _ fun i _ => oj i),
    integral_finsetSum _ fun i _ => oj i]

/-- **The tail identity**: for symmetric `k`, `‖(I − P_m) K‖²_HS = ∫∫ k² − ∑ᵢ ‖K φᵢ‖²`, that is
`Tr K² − Tr(P_m K²)` since `∑ᵢ ‖K φᵢ‖² = ∑ᵢ ⟨φᵢ, Kᵀ K φᵢ⟩`; the kernel of `P_m K` is `∑ᵢ φᵢ(x) (K φᵢ)(z)`. -/
theorem tail_left {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x z, k x z = k z x)
    (hφm : ∀ i, Measurable (φ i)) {B : ℝ} (hφb : ∀ i x, |φ i x| ≤ B)
    (hon : ∀ i j, ∫ x, φ i x * φ j x ∂μ = if i = j then 1 else 0) :
    hs μ (fun x z => k x z - ∑ i, φ i x * row μ k φ i z)
      = hs μ k - ∑ i, ∫ x, row μ k φ i x ^ 2 ∂μ := by
  have e : (fun x z => k x z - ∑ i, φ i x * row μ k φ i z)
      = fun x z => (fun x z => k x z - ∑ i, row μ k φ i x * φ i z) z x := by
    funext x z; rw [hsym x z]; simp only [mul_comm]
  rw [e, hs_swap (res_bdd hk hφm hφb), tail_right hk hφm hφb hon]

end Family

/-- **(D.3), the window test**: `0 ≤ d ≤ exp(V/(322 (48T)³)) − 1` gives
`2 log(1 + d) ≤ V/(161 (48T)³)`. `322`, `161`, `48` are the constants of (D.3). -/
theorem window {d V T : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ exp (V / (322 * (48 * T) ^ 3)) - 1) :
    2 * log (1 + d) ≤ V / (161 * (48 * T) ^ 3) := by
  have h1 : log (1 + d) ≤ V / (322 * (48 * T) ^ 3) := by
    rw [Real.log_le_iff_le_exp (by linarith)]; linarith
  have h2 : V / (161 * (48 * T) ^ 3) = 2 * (V / (322 * (48 * T) ^ 3)) := by ring
  rw [h2]; linarith

end MassGap.PurityTailIdentity

#print axioms MassGap.PurityTailIdentity.proj_eq
#print axioms MassGap.PurityTailIdentity.lin_meas
#print axioms MassGap.PurityTailIdentity.lin_bdd
#print axioms MassGap.PurityTailIdentity.sq_lin
#print axioms MassGap.PurityTailIdentity.row_meas
#print axioms MassGap.PurityTailIdentity.row_bdd
#print axioms MassGap.PurityTailIdentity.res_sq
#print axioms MassGap.PurityTailIdentity.tail
#print axioms MassGap.PurityTailIdentity.bessel
#print axioms MassGap.PurityTailIdentity.tail_le
#print axioms MassGap.PurityTailIdentity.res_bdd
#print axioms MassGap.PurityTailIdentity.tail_right
#print axioms MassGap.PurityTailIdentity.tail_left
#print axioms MassGap.PurityTailIdentity.window
