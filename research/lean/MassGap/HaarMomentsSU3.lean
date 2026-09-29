import Mathlib
import MassGap.SUN
import MassGap.ContactValue
import MassGap.PairInterface

noncomputable section

/-!
# MassGap.HaarMomentsSU3 — the Haar constants of the `SU(3)` link feature

The feature theorems read `PairInterface.inner_realFeature` and
`PairInterface.frob_featDual`.

## What it gives

`haarConsts_su3 : HaarConsts (probHaar (SU 3)) (realFeature 3)` with `D = 18`, `q4 = 1/96`,
`t3 = 1/108`.

## The route (substitution into the Haar integral, at rank 3)

Tools: invariance of `probHaar` under `U ↦ gU` and `U ↦ Ug` (`integral_mul_left_eq_self`,
`integral_mul_right_eq_self`) at explicit elements `g` of `SU(3)`; unitarity
`Σⱼ Uᵢⱼ Ū_kⱼ = δᵢₖ` and `Σᵢ Ūᵢₐ Uᵢ_b = δₐ_b`; and `det U = 1`. Reused from `MassGap.ContactValue`:
`om`, `Zg`, `phase_zero`, `coe_Zg_mul`, `om_primitive`, `om_conj`, `diag_mem`, `entry_cont`, and the
entry moments `msq`.

The elements:
* `Zg = ωI` multiplies a monomial with `p` factors `U` and `q` factors `Ū` by `ω^{p−q}`; every
  moment with `3 ∤ p − q` vanishes (`integral_omega_kill`).
* The diagonal phases `diag(i, 1, −i)` and `diag(1, i, −i)`, on either side: a monomial survives
  both only if its row (column) indices balance. Which index patterns balance is decided on `Fin 3`.
* The signed permutation matrices `sgn σ · P_σ` (determinant `sgn(σ)⁴ = 1`), on either side,
  relabel rows or columns.
* The rotation `[[3/5, −4/5, 0], [4/5, 3/5, 0], [0, 0, 1]]`, on the left.

1. Second moments (`haar_su3_second`): phases kill `i ≠ k` and `j ≠ l`; `ContactValue.msq` gives
   `E|Uᵢⱼ|² = 1/3`.
2. Fourth moments (`haar_su3_fourth`): phases leave the index patterns `{i₁,i₂} = {k₁,k₂}`,
   `{j₁,j₂} = {l₁,l₂}`; relabelling reduces every index tuple to nine canonical ones, which carry
   five values `A = E|U₁₁|⁴`, `B = E|U₁₁|²|U₁₂|²`, `C = E|U₁₁|²|U₂₁|²`, `D = E|U₁₁|²|U₂₂|²`,
   `X = E U₁₁U₂₂Ū₁₂Ū₂₁`. The first row sum gives `A + 2B = 1/3`, the first column sum
   `A + 2C = 1/3`, the second row sum `C + 2D = 1/3`, row orthogonality `C + 2X = 0`, and the rotation
   `625A = 337A + 576C`, i.e. `A = 2C`. So `A = 1/6`, `B = C = 1/12`, `D = 1/8`, `X = −1/24`: the
   values of `wg4`.
3. The quartic (`haar_su3_trace_fourth_le`): contracting `wg4`,
   `E|tr(UA)|⁴ = (1/4)‖A‖⁴_F − (1/12) Σ_{pq} |Σⱼ A_{jp} Ā_{jq}|² ≤ (1/4)‖A‖⁴_F`.
4. Third moments (`haar_su3_trace_cube`): with `M = UA`, left phases leave in `(tr M)³` only the
   six products `M₁₁M₂₂M₃₃`, and relabelling rows gives `E M_{1σ1}M_{2σ2}M_{3σ3} = sgn σ ·
   E M₁₁M₂₂M₃₃`; `E det M = det A` (`det U = 1`) then gives `E tr(UA)³ = det A`. The polarisation
   `(a+b)³ − (a−b)³ = 6a²b + 2b³` gives `haar_su3_trace_sq_mul`.
5. `adjugate_frob_le`: `2‖adj A‖²_F = ‖A‖⁴_F − Σ_{pq}|(A†A)_{pq}|²` and
   `Σ_{pq}|(A†A)_{pq}|² ≥ Σ_p (A†A)_{pp}² ≥ ‖A‖⁴_F/3`.
6. The feature: `⟪w, X⟫ = Re z/√3`, `z = tr(U featDual w)`. `(Re z)² = (|z|² + Re z²)/2` gives
   `E⟪w,X⟫² = ‖w‖²/18`; `(Re z)⁴ = (3/8)|z|⁴ + (1/8)Re z⁴ + (1/2)Re(z³z̄)` gives
   `E⟪w,X⟫⁴ = (1/24)E|z|⁴ ≤ ‖w‖⁴/96`; `(Re a)² Re b = (Re(a²b) + Re(a²b̄) + 2 Re(aāb))/4` gives
   `E⟪u,X⟫²⟪w,X⟫ = Re tr(adj F_u F_w)/(36√3)`, bounded by `‖u‖²‖w‖/108` through Cauchy–Schwarz and
   step 5.
-/

namespace MassGap.HaarMomentsSU3

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.PairInterface
open MassGap.ContactValue (om Zg phase_zero)

/-! ## 0. Integrability, continuity, invariance -/

/-- A continuous complex function on `SU(3)` is Haar-integrable: on a compact group every function
has compact support.

DERIVED: `3` is the rank. -/
private theorem intC {f : SU 3 → ℂ} (hf : Continuous f) : Integrable f (probHaar (SU 3)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The real-valued form of `intC`.

DERIVED: `3` is the rank. -/
private theorem intR {f : SU 3 → ℝ} (hf : Continuous f) : Integrable f (probHaar (SU 3)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- An entry is continuous.

DERIVED: `3` is the rank. -/
private theorem ec (i j : Fin 3) :
    Continuous (fun U : SU 3 => (U : Matrix (Fin 3) (Fin 3) ℂ) i j) :=
  MassGap.ContactValue.entry_cont i j

/-- A conjugated entry is continuous.

DERIVED: `3` is the rank. -/
private theorem ecs (i j : Fin 3) :
    Continuous (fun U : SU 3 => star ((U : Matrix (Fin 3) (Fin 3) ℂ) i j)) :=
  continuous_star.comp (ec i j)

/-- The monomial with two factors `U` and two factors `Ū` is continuous.

DERIVED: `3` is the rank. -/
private theorem mono4_cont (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    Continuous (fun U : SU 3 => (U : Matrix (Fin 3) (Fin 3) ℂ) i1 j1
      * (U : Matrix (Fin 3) (Fin 3) ℂ) i2 j2 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k1 l1)
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k2 l2)) :=
  (((ec i1 j1).mul (ec i2 j2)).mul (ecs k1 l1)).mul (ecs k2 l2)

/-- An entry of `UA` is continuous.

DERIVED: `3` is the rank. -/
private theorem mcont (A : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3) :
    Continuous (fun U : SU 3 => ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a b) :=
  (continuous_subtype_val.matrix_mul continuous_const).matrix_elem a b

/-- A product of three entries of `UA` is continuous.

DERIVED: `3` is the rank and the number of factors. -/
private theorem cont3 (A : Matrix (Fin 3) (Fin 3) ℂ) (a0 b0 a1 b1 a2 b2 : Fin 3) :
    Continuous (fun U : SU 3 => ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a0 b0
      * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a1 b1 * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a2 b2) :=
  ((mcont A a0 b0).mul (mcont A a1 b1)).mul (mcont A a2 b2)

/-- `tr(UA)` is continuous.

DERIVED: `3` is the rank. -/
private theorem trc (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Continuous (fun U : SU 3 => Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)) :=
  (continuous_subtype_val.matrix_mul continuous_const).matrix_trace

/-- `conj tr(UA)` is continuous.

DERIVED: `3` is the rank. -/
private theorem ccs (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Continuous (fun U : SU 3 => (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A))) :=
  Complex.continuous_conj.comp (trc A)

/-- Left translation by `g` multiplying the integrand by `lam` multiplies the integral by `lam`.

DERIVED: `3` is the rank. -/
private theorem inv_left {F : SU 3 → ℂ} (g : SU 3) (lam : ℂ) (h : ∀ U, F (g * U) = lam * F U) :
    ∫ U, F U ∂(probHaar (SU 3)) = lam * ∫ U, F U ∂(probHaar (SU 3)) := by
  haveI := MassGap.CompactGauge.isMulLeftInvariant_probHaar (SU 3)
  calc ∫ U, F U ∂(probHaar (SU 3)) = ∫ U, F (g * U) ∂(probHaar (SU 3)) :=
        (integral_mul_left_eq_self F g).symm
    _ = ∫ U, lam * F U ∂(probHaar (SU 3)) := integral_congr_ae (Filter.Eventually.of_forall h)
    _ = lam * ∫ U, F U ∂(probHaar (SU 3)) := integral_const_mul _ _

/-- The right-translation form of `inv_left`.

DERIVED: `3` is the rank. -/
private theorem inv_right {F : SU 3 → ℂ} (g : SU 3) (lam : ℂ) (h : ∀ U, F (U * g) = lam * F U) :
    ∫ U, F U ∂(probHaar (SU 3)) = lam * ∫ U, F U ∂(probHaar (SU 3)) := by
  haveI := MassGap.CompactGauge.isMulRightInvariant_probHaar (SU 3)
  calc ∫ U, F U ∂(probHaar (SU 3)) = ∫ U, F (U * g) ∂(probHaar (SU 3)) :=
        (integral_mul_right_eq_self F g).symm
    _ = ∫ U, lam * F U ∂(probHaar (SU 3)) := integral_congr_ae (Filter.Eventually.of_forall h)
    _ = lam * ∫ U, F U ∂(probHaar (SU 3)) := integral_const_mul _ _

/-- If `F(gU) = G(U)` then `∫ G = ∫ F`.

DERIVED: `3` is the rank. -/
private theorem eq_left {F G : SU 3 → ℂ} (g : SU 3) (h : ∀ U, F (g * U) = G U) :
    ∫ U, G U ∂(probHaar (SU 3)) = ∫ U, F U ∂(probHaar (SU 3)) := by
  haveI := MassGap.CompactGauge.isMulLeftInvariant_probHaar (SU 3)
  calc ∫ U, G U ∂(probHaar (SU 3)) = ∫ U, F (g * U) ∂(probHaar (SU 3)) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun U => (h U).symm))
    _ = ∫ U, F U ∂(probHaar (SU 3)) := integral_mul_left_eq_self F g

/-- If `F(Ug) = G(U)` then `∫ G = ∫ F`.

DERIVED: `3` is the rank. -/
private theorem eq_right {F G : SU 3 → ℂ} (g : SU 3) (h : ∀ U, F (U * g) = G U) :
    ∫ U, G U ∂(probHaar (SU 3)) = ∫ U, F U ∂(probHaar (SU 3)) := by
  haveI := MassGap.CompactGauge.isMulRightInvariant_probHaar (SU 3)
  calc ∫ U, G U ∂(probHaar (SU 3)) = ∫ U, F (U * g) ∂(probHaar (SU 3)) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun U => (h U).symm))
    _ = ∫ U, F U ∂(probHaar (SU 3)) := integral_mul_right_eq_self F g

/-- `x = λx` with `λ ≠ 1` forces `x = 0`.

DERIVED: `1` is the excluded phase; `0` is the value. -/
private theorem kill {x lam : ℂ} (h : x = lam * x) (hl : lam ≠ 1) : x = 0 := by
  have h1 : (1 - lam) * x = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm hl))

/-- `x = λx` with `x ≠ 0` forces `λ = 1`.

DERIVED: `1` is the forced phase; `0` is the excluded value. -/
private theorem lam_one {x lam : ℂ} (h : x = lam * x) (hx : x ≠ 0) : lam = 1 := by
  by_contra hl
  exact hx (kill h hl)

/-- The integral of a sum over `Fin 3` splits into its three terms.

DERIVED: `3` is the rank; `0`, `1`, `2` are the three indices. -/
private theorem int_sum3 (F : Fin 3 → SU 3 → ℂ) (hF : ∀ j, Continuous (F j)) :
    ∫ U, ∑ j, F j U ∂(probHaar (SU 3))
      = ∫ U, F 0 U ∂(probHaar (SU 3)) + ∫ U, F 1 U ∂(probHaar (SU 3))
        + ∫ U, F 2 U ∂(probHaar (SU 3)) := by
  rw [integral_finsetSum _ (fun j _ => intC (hF j)), Fin.sum_univ_three]

/-- The integral of a triple sum over `Fin 3` is the triple sum of the integrals.

DERIVED: `3` is the rank. -/
private theorem int_sum3n (F : Fin 3 → Fin 3 → Fin 3 → SU 3 → ℂ)
    (hF : ∀ a b c, Continuous (F a b c)) :
    ∫ U, ∑ a, ∑ b, ∑ c, F a b c U ∂(probHaar (SU 3))
      = ∑ a, ∑ b, ∑ c, ∫ U, F a b c U ∂(probHaar (SU 3)) := by
  have h1 : ∀ a b, Continuous (fun U => ∑ c, F a b c U) := fun a b =>
    continuous_finsetSum _ (fun c _ => hF a b c)
  have h2 : ∀ a, Continuous (fun U => ∑ b, ∑ c, F a b c U) := fun a =>
    continuous_finsetSum _ (fun b _ => h1 a b)
  rw [integral_finsetSum _ (fun a _ => intC (h2 a))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_finsetSum _ (fun b _ => intC (h1 a b))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact integral_finsetSum _ (fun c _ => intC (hF a b c))

/-- The integral of a fourfold sum over `Fin 3` is the fourfold sum of the integrals.

DERIVED: `3` is the rank. -/
private theorem int_sum4 (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → SU 3 → ℂ)
    (hF : ∀ a b c d, Continuous (F a b c d)) :
    ∫ U, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d U ∂(probHaar (SU 3))
      = ∑ a, ∑ b, ∑ c, ∑ d, ∫ U, F a b c d U ∂(probHaar (SU 3)) := by
  have h1 : ∀ a b c, Continuous (fun U => ∑ d, F a b c d U) := fun a b c =>
    continuous_finsetSum _ (fun d _ => hF a b c d)
  have h2 : ∀ a b, Continuous (fun U => ∑ c, ∑ d, F a b c d U) := fun a b =>
    continuous_finsetSum _ (fun c _ => h1 a b c)
  have h3 : ∀ a, Continuous (fun U => ∑ b, ∑ c, ∑ d, F a b c d U) := fun a =>
    continuous_finsetSum _ (fun b _ => h2 a b)
  rw [integral_finsetSum _ (fun a _ => intC (h3 a))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_finsetSum _ (fun b _ => intC (h2 a b))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [integral_finsetSum _ (fun c _ => intC (h1 a b c))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  exact integral_finsetSum _ (fun d _ => intC (hF a b c d))

/-- Termwise equality of fourfold sums over `Fin 3`.

DERIVED: `3` is the rank. -/
private theorem sum4_congr {f g : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ}
    (h : ∀ a b c d, f a b c d = g a b c d) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d :=
  Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => h a b c d))))

/-- A product of two double sums over `Fin 3` is a fourfold sum.

DERIVED: `3` is the rank. -/
private theorem mul_sum22 (f g : Fin 3 → Fin 3 → ℂ) :
    (∑ a, ∑ b, f a b) * (∑ c, ∑ d, g c d) = ∑ a, ∑ b, ∑ c, ∑ d, f a b * g c d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]

/-- A product of two fourfold sums over `Fin 3` is an eightfold sum.

DERIVED: `3` is the rank. -/
private theorem mul_sum44 (f g : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) * (∑ e, ∑ p, ∑ q, ∑ r, g e p q r)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ q, ∑ r, f a b c d * g e p q r := by
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.mul_sum]

/-! ## 1. Diagonal phases -/

/-- `conj(iⁿ) = i^{3n}`.

DERIVED: `3`: `conj i = −i = i³`. -/
private theorem star_Ipow (n : ℕ) : star (Complex.I ^ n) = Complex.I ^ (3 * n) := by
  rw [star_pow, pow_mul, Complex.I_pow_three]
  congr 1
  rw [← starRingEnd_apply]
  exact Complex.conj_I

/-- `iⁿ = 1` forces `4 ∣ n`.

DERIVED: `4` is the order of `i`; `0, 1, 2, 3` are the residues. -/
private theorem I_pow_eq_one {n : ℕ} (h : Complex.I ^ n = 1) : n % 4 = 0 := by
  have hmod : Complex.I ^ n = Complex.I ^ (n % 4) := by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hmod] at h
  have hc : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hc with h0 | h1 | h2 | h3
  · exact h0
  · exfalso
    rw [h1, pow_one] at h
    have hre := congrArg Complex.re h
    simp at hre
  · exfalso
    rw [h2, Complex.I_sq] at h
    have hre := congrArg Complex.re h
    norm_num at hre
  · exfalso
    rw [h3, Complex.I_pow_three] at h
    have hre := congrArg Complex.re h
    simp at hre

/-- The exponents of `diag(i, 1, −i) = diag(i¹, i⁰, i³)`.

CHOSEN: the powers `1, 0, 3` of `i`; their sum `4` puts the matrix in `SU(3)`. -/
private def exA : Fin 3 → ℕ := ![1, 0, 3]

/-- The exponents of `diag(1, i, −i) = diag(i⁰, i¹, i³)`.

CHOSEN: the powers `0, 1, 3` of `i`; their sum `4` puts the matrix in `SU(3)`. -/
private def exB : Fin 3 → ℕ := ![0, 1, 3]

/-- The entries of `diag(i, 1, −i)`.

DERIVED: `3` is the rank. -/
private def phA : Fin 3 → ℂ := fun a => Complex.I ^ exA a

/-- The entries of `diag(1, i, −i)`.

DERIVED: `3` is the rank. -/
private def phB : Fin 3 → ℂ := fun a => Complex.I ^ exB a

/-- `iⁿ` has unit modulus.

DERIVED: `4 = 1 + 3`; `1` is the modulus. -/
private theorem ipow_unit (n : ℕ) : Complex.I ^ n * (starRingEnd ℂ) (Complex.I ^ n) = 1 := by
  rw [starRingEnd_apply, star_Ipow, ← pow_add, show n + 3 * n = 4 * n by ring, pow_mul,
    Complex.I_pow_four, one_pow]

/-- `diag(i, 1, −i) ∈ SU(3)`.

DERIVED: `4 = 1 + 0 + 3`; `0, 1, 2` are the diagonal positions. -/
private theorem phA_mem : Matrix.diagonal phA ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  refine MassGap.ContactValue.diag_mem phA (fun i => ipow_unit (exA i)) ?_
  show Complex.I ^ exA 0 * Complex.I ^ exA 1 * Complex.I ^ exA 2 = 1
  rw [← pow_add, ← pow_add, show exA 0 + exA 1 + exA 2 = 4 by decide, Complex.I_pow_four]

/-- `diag(1, i, −i) ∈ SU(3)`.

DERIVED: `4 = 0 + 1 + 3`; `0, 1, 2` are the diagonal positions. -/
private theorem phB_mem : Matrix.diagonal phB ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  refine MassGap.ContactValue.diag_mem phB (fun i => ipow_unit (exB i)) ?_
  show Complex.I ^ exB 0 * Complex.I ^ exB 1 * Complex.I ^ exB 2 = 1
  rw [← pow_add, ← pow_add, show exB 0 + exB 1 + exB 2 = 4 by decide, Complex.I_pow_four]

/-- Left multiplication by a diagonal element scales row `i` by `vᵢ`.

DERIVED: `3` is the rank. -/
private theorem coe_diag_mul (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (U : SU 3) (i j : Fin 3) :
    (((⟨Matrix.diagonal v, hv⟩ : SU 3) * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
      = v i * (U : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  rw [Submonoid.coe_mul]
  show (Matrix.diagonal v * (U : Matrix (Fin 3) (Fin 3) ℂ)) i j = _
  rw [Matrix.diagonal_mul]

/-- Right multiplication by a diagonal element scales column `j` by `vⱼ`.

DERIVED: `3` is the rank. -/
private theorem coe_mul_diag (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (U : SU 3) (i j : Fin 3) :
    ((U * (⟨Matrix.diagonal v, hv⟩ : SU 3) : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
      = (U : Matrix (Fin 3) (Fin 3) ℂ) i j * v j := by
  rw [Submonoid.coe_mul]
  show ((U : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.diagonal v) i j = _
  rw [Matrix.mul_diagonal]

/-- Left multiplication by a diagonal element scales row `a` of `UA` by `vₐ`.

DERIVED: `3` is the rank. -/
private theorem coe_diag_mul_mat (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (U : SU 3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3) :
    ((((⟨Matrix.diagonal v, hv⟩ : SU 3) * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) * A) a b
      = v a * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a b := by
  rw [Submonoid.coe_mul, Matrix.mul_assoc]
  show (Matrix.diagonal v * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)) a b = _
  rw [Matrix.diagonal_mul]

/-- The phase of a degree-`(1,1)` monomial.

DERIVED: `3`: `conj(iᵉ) = i^{3e}`. -/
private theorem phase2 (e : Fin 3 → ℕ) (a c : Fin 3) :
    Complex.I ^ e a * star (Complex.I ^ e c) = Complex.I ^ (e a + 3 * e c) := by
  rw [star_Ipow, pow_add]

/-- The phase of a degree-`(3,0)` monomial.

DERIVED: `3` is the rank, the range of the index positions. -/
private theorem phase3 (e : Fin 3 → ℕ) (a b c : Fin 3) :
    Complex.I ^ e a * Complex.I ^ e b * Complex.I ^ e c = Complex.I ^ (e a + e b + e c) := by
  rw [pow_add, pow_add]

/-- The phase of a degree-`(2,2)` monomial.

DERIVED: `3`: `conj(iᵉ) = i^{3e}`. -/
private theorem phase4 (e : Fin 3 → ℕ) (a b c d : Fin 3) :
    Complex.I ^ e a * Complex.I ^ e b * star (Complex.I ^ e c) * star (Complex.I ^ e d)
      = Complex.I ^ (e a + e b + 3 * e c + 3 * e d) := by
  rw [star_Ipow, star_Ipow, pow_add, pow_add, pow_add]

/-- DERIVED: `3` is the rank; `4` the order of `i`; `0` the residue. -/
private theorem dec2 : ∀ a c : Fin 3, (exA a + 3 * exA c) % 4 = 0 → a = c := by
  decide

/-- DERIVED: `3` is the rank; `4` the order of `i`; `0` the residue. -/
private theorem dec3 : ∀ a b c : Fin 3, (exA a + exA b + exA c) % 4 = 0 →
    (exB a + exB b + exB c) % 4 = 0 → a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  decide

/-- DERIVED: `3` is the rank and `conj(iᵉ) = i^{3e}`; `4` the order of `i`; `0` the residue. -/
private theorem dec4 : ∀ a b c d : Fin 3, (exA a + exA b + 3 * exA c + 3 * exA d) % 4 = 0 →
    (exB a + exB b + 3 * exB c + 3 * exB d) % 4 = 0 → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  decide

/-- DERIVED: `3` is the rank; `0, 1, 2` are its values. -/
private theorem fin3_cases : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by
  decide

/-- DERIVED: `3` is the rank; `0, 1, 2` are its values. -/
private theorem pair_cases : ∀ a b : Fin 3, a ≠ b →
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0)
      ∨ (a = 2 ∧ b = 1) := by
  decide

/-- DERIVED: `3` is the rank; `0, 1, 2` are its values. -/
private theorem perm3_cases : ∀ a0 a1 a2 : Fin 3, a0 ≠ a1 → a1 ≠ a2 → a0 ≠ a2 →
    (a0 = 0 ∧ a1 = 1 ∧ a2 = 2) ∨ (a0 = 0 ∧ a1 = 2 ∧ a2 = 1) ∨ (a0 = 1 ∧ a1 = 0 ∧ a2 = 2)
      ∨ (a0 = 1 ∧ a1 = 2 ∧ a2 = 0) ∨ (a0 = 2 ∧ a1 = 0 ∧ a2 = 1) ∨ (a0 = 2 ∧ a1 = 1 ∧ a2 = 0) := by
  decide

/-! ## 2. Signed permutation matrices -/

/-- The sign of a permutation, as a complex number.

DERIVED: `3` is the rank. -/
private def sg (σ : Equiv.Perm (Fin 3)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

/-- DERIVED: `1`, `−1` are the two signs; `3` is the rank. -/
private theorem sg_cases (σ : Equiv.Perm (Fin 3)) : sg σ = 1 ∨ sg σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · left; unfold sg; rw [h]; simp
  · right; unfold sg; rw [h]; simp

/-- DERIVED: `1` is the square of a sign; `3` is the rank. -/
private theorem sg_mul_self (σ : Equiv.Perm (Fin 3)) : sg σ * sg σ = 1 := by
  rcases sg_cases σ with h | h <;> rw [h] <;> norm_num

/-- DERIVED: `3` is the rank. -/
private theorem star_sg (σ : Equiv.Perm (Fin 3)) : star (sg σ) = sg σ := by
  unfold sg; exact star_intCast _

/-- DERIVED: `−1` is the sign of a transposition; `3` is the rank. -/
private theorem sg_swap (a b : Fin 3) (h : a ≠ b) : sg (Equiv.swap a b) = -1 := by
  unfold sg; rw [Equiv.Perm.sign_swap h]; simp

/-- DERIVED: `3` is the rank. -/
private theorem sg_mul (σ τ : Equiv.Perm (Fin 3)) : sg (σ * τ) = sg σ * sg τ := by
  unfold sg; rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]

/-- The signed permutation matrix relabelling rows: `(P_σ M)ₐ_c = sgn σ · M_{σa, c}`.

DERIVED: `3` is the rank; `0` is the off-support entry. -/
private def Pm (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun a b => if σ a = b then sg σ else 0

/-- The signed permutation matrix relabelling columns: `(M Q_σ)ₐ_b = M_{a, σb} · sgn σ`.

DERIVED: `3` is the rank; `0` is the off-support entry. -/
private def Qm (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun c b => if c = σ b then sg σ else 0

/-- DERIVED: `3` is the rank. -/
private theorem Pm_mul (σ : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) ℂ) (a c : Fin 3) :
    (Pm σ * M) a c = sg σ * M (σ a) c := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (σ a)]
  · simp [Pm]
  · intro b hb
    simp [Pm, Ne.symm hb]

/-- DERIVED: `3` is the rank. -/
private theorem mul_Qm (σ : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3) :
    (M * Qm σ) a b = M a (σ b) * sg σ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (σ b)]
  · simp [Qm]
  · intro c hc
    simp [Qm, hc]

/-- `sgn σ · P_σ ∈ SU(3)`: unitary, with determinant `sgn(σ)³ · sgn σ = 1`.

DERIVED: `3` is the rank and the power of the scalar in the determinant; `1` is the determinant. -/
private theorem Pm_mem (σ : Equiv.Perm (Fin 3)) : Pm σ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext a c
    rw [Pm_mul, Matrix.star_apply, Matrix.one_apply]
    by_cases h : a = c
    · subst h
      simp [Pm, star_sg, sg_mul_self]
    · have h' : σ c ≠ σ a := fun e => h (σ.injective e).symm
      simp [Pm, h, h']
  · have hP : Pm σ = sg σ • (1 : Matrix (Fin 3) (Fin 3) ℂ).submatrix σ id := by
      ext a b
      simp [Pm, Matrix.one_apply]
    rw [hP, Matrix.det_smul, Matrix.det_permute, Matrix.det_one, Fintype.card_fin]
    show sg σ ^ 3 * (sg σ * 1) = 1
    rcases sg_cases σ with hs | hs <;> rw [hs] <;> norm_num

/-- `sgn σ · Q_σ ∈ SU(3)`.

DERIVED: `3` is the rank and the power of the scalar in the determinant; `1` is the determinant. -/
private theorem Qm_mem (σ : Equiv.Perm (Fin 3)) : Qm σ ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff'.mpr ?_, ?_⟩
  · ext a b
    rw [mul_Qm, Matrix.star_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h
      simp [Qm, star_sg, sg_mul_self]
    · have h' : σ b ≠ σ a := fun e => h (σ.injective e).symm
      simp [Qm, h, h']
  · have hQ : Qm σ = sg σ • (1 : Matrix (Fin 3) (Fin 3) ℂ).submatrix id σ := by
      ext a b
      simp [Qm, Matrix.one_apply]
    rw [hQ, Matrix.det_smul, Matrix.det_permute', Matrix.det_one, Fintype.card_fin]
    show sg σ ^ 3 * (sg σ * 1) = 1
    rcases sg_cases σ with hs | hs <;> rw [hs] <;> norm_num

/-- `sgn σ · P_σ` as an element of `SU(3)`.

DERIVED: `3` is the rank. -/
private def PgS (σ : Equiv.Perm (Fin 3)) : SU 3 := ⟨Pm σ, Pm_mem σ⟩

/-- `sgn σ · Q_σ` as an element of `SU(3)`.

DERIVED: `3` is the rank. -/
private def QgS (σ : Equiv.Perm (Fin 3)) : SU 3 := ⟨Qm σ, Qm_mem σ⟩

/-- DERIVED: `3` is the rank. -/
private theorem coe_PgS_mul (σ : Equiv.Perm (Fin 3)) (U : SU 3) (a c : Fin 3) :
    ((PgS σ * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) a c
      = sg σ * (U : Matrix (Fin 3) (Fin 3) ℂ) (σ a) c := by
  rw [Submonoid.coe_mul]
  exact Pm_mul σ _ a c

/-- DERIVED: `3` is the rank. -/
private theorem coe_mul_QgS (σ : Equiv.Perm (Fin 3)) (U : SU 3) (a b : Fin 3) :
    ((U * QgS σ : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) a b
      = (U : Matrix (Fin 3) (Fin 3) ℂ) a (σ b) * sg σ := by
  rw [Submonoid.coe_mul]
  exact mul_Qm σ _ a b

/-- DERIVED: `3` is the rank. -/
private theorem coe_PgS_mul_mat (σ : Equiv.Perm (Fin 3)) (U : SU 3) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (a b : Fin 3) :
    (((PgS σ * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) * A) a b
      = sg σ * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) (σ a) b := by
  rw [Submonoid.coe_mul, Matrix.mul_assoc]
  exact Pm_mul σ _ a b

/-- DERIVED: `0` goes to some `σ 0`; `3` is the rank. -/
private theorem exists_perm1 (a : Fin 3) : ∃ σ : Equiv.Perm (Fin 3), σ 0 = a :=
  ⟨Equiv.swap 0 a, Equiv.swap_apply_left 0 a⟩

/-- Two distinct indices are the images of `0` and `1` under some permutation.

DERIVED: `0, 1, 2` are the values of `Fin 3`. -/
private theorem exists_perm2 (a b : Fin 3) (h : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b := by
  rcases pair_cases a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2 * Equiv.swap 1 2, by decide, by decide⟩
  · exact ⟨Equiv.swap 0 2, by decide, by decide⟩

/-! ### Values of the transpositions used below

DERIVED: `0, 1, 2` are the values of `Fin 3`. -/

private theorem sw01_0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := Equiv.swap_apply_left 0 1
private theorem sw01_1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := Equiv.swap_apply_right 0 1
private theorem sw01_2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
private theorem sw12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
private theorem sw12_1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := Equiv.swap_apply_left 1 2
private theorem sw12_2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := Equiv.swap_apply_right 1 2
private theorem sw02_0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := Equiv.swap_apply_left 0 2
private theorem sw02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
private theorem sw02_2 : Equiv.swap (0 : Fin 3) 2 2 = 0 := Equiv.swap_apply_right 0 2
private theorem cy1_0 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 0 = 1 := by decide
private theorem cy1_1 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 1 = 2 := by decide
private theorem cy1_2 : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 2 = 0 := by decide
private theorem cy2_0 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 0 = 2 := by decide
private theorem cy2_1 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 1 = 0 := by decide
private theorem cy2_2 : ((Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) 2 = 1 := by decide

/-! ## 3. Unitarity -/

/-- Rows of a unitary matrix: `Σⱼ Uₐⱼ Ū_bⱼ = δₐ_b`.

DERIVED: `3` is the rank; `1` is the identity. -/
private theorem row_mul (U : SU 3) (a b : Fin 3) :
    ∑ j, (U : Matrix (Fin 3) (Fin 3) ℂ) a j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) b j)
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) a b := by
  have huni : (U : Matrix (Fin 3) (Fin 3) ℂ) * star (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have h := congrFun (congrFun huni a) b
  rw [Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.star_apply]

/-- Columns of a unitary matrix: `Σᵢ Ūᵢₐ Uᵢ_b = δₐ_b`.

DERIVED: `3` is the rank; `1` is the identity. -/
private theorem col_mul (U : SU 3) (a b : Fin 3) :
    ∑ i, star ((U : Matrix (Fin 3) (Fin 3) ℂ) i a) * (U : Matrix (Fin 3) (Fin 3) ℂ) i b
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) a b := by
  have huni : star (U : Matrix (Fin 3) (Fin 3) ℂ) * (U : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have h := congrFun (congrFun huni a) b
  rw [Matrix.mul_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.star_apply]

/-- DERIVED: `3` is the rank; `1` is the diagonal of the identity. -/
private theorem row_self (U : SU 3) (a : Fin 3) :
    ∑ j, (U : Matrix (Fin 3) (Fin 3) ℂ) a j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) a j) = 1 :=
  (row_mul U a a).trans (Matrix.one_apply_eq a)

/-- DERIVED: `3` is the rank; `0` is the off-diagonal of the identity. -/
private theorem row_orth (U : SU 3) (a b : Fin 3) (h : a ≠ b) :
    ∑ j, (U : Matrix (Fin 3) (Fin 3) ℂ) a j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) b j) = 0 :=
  (row_mul U a b).trans (Matrix.one_apply_ne h)

/-- DERIVED: `3` is the rank; `1` is the diagonal of the identity. -/
private theorem col_self (U : SU 3) (a : Fin 3) :
    ∑ i, star ((U : Matrix (Fin 3) (Fin 3) ℂ) i a) * (U : Matrix (Fin 3) (Fin 3) ℂ) i a = 1 :=
  (col_mul U a a).trans (Matrix.one_apply_eq a)

/-! ## 4. The centre, and second moments -/

/-- **The centre kills unbalanced moments**: if `f(ωI · U) = ω^k f(U)` and `3 ∤ k`, then `E f = 0`
(`ContactValue.phase_zero` at `h = Zg`, `λ = ωᵏ ≠ 1`).

DERIVED: `3` is the rank and the order of `ω`; `0` is the value. -/
theorem integral_omega_kill (f : SU 3 → ℂ) (k : ℕ) (hk : ¬ 3 ∣ k)
    (hf : ∀ U, f (Zg * U) = om ^ k * f U) :
    ∫ U, f U ∂(probHaar (SU 3)) = 0 := by
  refine phase_zero Zg (om ^ k) ?_ hf
  intro h
  exact hk ((MassGap.ContactValue.om_primitive.pow_eq_one_iff_dvd k).mp h)

#print axioms integral_omega_kill

/-- DERIVED: `3` is the rank. -/
private theorem T2_lphase (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (i j k l : Fin 3) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l)
        ∂(probHaar (SU 3))
      = (v i * star (v k)) * ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j
          * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l) ∂(probHaar (SU 3)) := by
  refine inv_left (⟨Matrix.diagonal v, hv⟩ : SU 3) _ (fun U => ?_)
  simp only [coe_diag_mul, star_mul']
  ring

/-- DERIVED: `3` is the rank. -/
private theorem T2_rphase (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (i j k l : Fin 3) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l)
        ∂(probHaar (SU 3))
      = (v j * star (v l)) * ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j
          * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l) ∂(probHaar (SU 3)) := by
  refine inv_right (⟨Matrix.diagonal v, hv⟩ : SU 3) _ (fun U => ?_)
  simp only [coe_mul_diag, star_mul']
  ring

/-- DERIVED: `3` is the rank; `0` is the value. -/
private theorem T2_zero_row {i k : Fin 3} (j l : Fin 3) (h : i ≠ k) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l)
      ∂(probHaar (SU 3)) = 0 := by
  by_contra hne
  have hA := T2_lphase phA phA_mem i j k l
  rw [show phA i * star (phA k) = Complex.I ^ (exA i + 3 * exA k) from phase2 exA i k] at hA
  exact h (dec2 i k (I_pow_eq_one (lam_one hA hne)))

/-- DERIVED: `3` is the rank; `0` is the value. -/
private theorem T2_zero_col (i k : Fin 3) {j l : Fin 3} (h : j ≠ l) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l)
      ∂(probHaar (SU 3)) = 0 := by
  by_contra hne
  have hA := T2_rphase phA phA_mem i j k l
  rw [show phA j * star (phA l) = Complex.I ^ (exA j + 3 * exA l) from phase2 exA j l] at hA
  exact h (dec2 j l (I_pow_eq_one (lam_one hA hne)))

/-- `ContactValue.msq a 0 = 1/3` for every row `a`.

DERIVED: `1/3 = 1/N`; `0` is the column. -/
private theorem msq_col0 (a : Fin 3) : MassGap.ContactValue.msq a 0 = 1 / 3 := by
  rcases fin3_cases a with rfl | rfl | rfl
  · exact MassGap.ContactValue.msq_zero_zero
  · exact (MassGap.ContactValue.msq_row_01 0).symm.trans MassGap.ContactValue.msq_zero_zero
  · exact ((MassGap.ContactValue.msq_row_12 0).symm.trans
      (MassGap.ContactValue.msq_row_01 0).symm).trans MassGap.ContactValue.msq_zero_zero

/-- `ContactValue.msq a b = 1/3` for every entry.

DERIVED: `1/3 = 1/N`. -/
private theorem msq_all (a b : Fin 3) : MassGap.ContactValue.msq a b = 1 / 3 := by
  rcases fin3_cases b with rfl | rfl | rfl
  · exact msq_col0 a
  · exact (MassGap.ContactValue.msq_col_01 a).trans (msq_col0 a)
  · exact ((MassGap.ContactValue.msq_col_12 a).trans (MassGap.ContactValue.msq_col_01 a)).trans
      (msq_col0 a)

/-- `E|Uₐ_b|² = 1/3`.

DERIVED: `1/3 = 1/N`. -/
private theorem T2_diag (a b : Fin 3) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) a b * star ((U : Matrix (Fin 3) (Fin 3) ℂ) a b)
      ∂(probHaar (SU 3)) = 1 / 3 := by
  have h := msq_all a b
  unfold MassGap.ContactValue.msq at h
  simpa only [starRingEnd_apply] using h

/-- **Second moments**: `E Uᵢⱼ Ū_kl = δᵢₖ δⱼₗ / 3`.

DERIVED: `3` is the rank; `1/3 = 1/N`; `0` is the value off the diagonal. -/
theorem haar_su3_second (i j k l : Fin 3) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l)
      ∂(probHaar (SU 3)) = if i = k ∧ j = l then 1 / 3 else 0 := by
  by_cases h : i = k ∧ j = l
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact T2_diag i j
  · rw [if_neg h]
    by_cases hik : i = k
    · exact T2_zero_col i k (fun hjl => h ⟨hik, hjl⟩)
    · exact T2_zero_row j l hik

#print axioms haar_su3_second

/-- `E Uᵢⱼ U_kl = 0` (`integral_omega_kill`, `k = 2`).

DERIVED: `3` is the rank; `0` is the value. -/
theorem haar_su3_second_noconj (i j k l : Fin 3) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * (U : Matrix (Fin 3) (Fin 3) ℂ) k l
      ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 2 (by decide) (fun U => ?_)
  simp only [MassGap.ContactValue.coe_Zg_mul]
  ring

#print axioms haar_su3_second_noconj

/-- **The fourth-moment Weingarten values** at rank `3`:
`Wg(e) = 1/(N² − 1) = 1/8`, `Wg((12)) = −1/(N(N² − 1)) = −1/24`.

DERIVED: `8 = 3² − 1`; `24 = 3(3² − 1)`; `1`, `0` are the Kronecker values. -/
def wg4 (i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ : Fin 3) : ℂ :=
  (1 / 8) * ((if i₁ = k₁ ∧ i₂ = k₂ ∧ j₁ = l₁ ∧ j₂ = l₂ then 1 else 0)
      + (if i₁ = k₂ ∧ i₂ = k₁ ∧ j₁ = l₂ ∧ j₂ = l₁ then 1 else 0))
    - (1 / 24) * ((if i₁ = k₁ ∧ i₂ = k₂ ∧ j₁ = l₂ ∧ j₂ = l₁ then 1 else 0)
      + (if i₁ = k₂ ∧ i₂ = k₁ ∧ j₁ = l₁ ∧ j₂ = l₂ then 1 else 0))

/-! ## 5. Fourth moments -/

/-- The fourth-moment integral, the left side of `haar_su3_fourth`.

DERIVED: `3` is the rank. -/
private def T4 (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) : ℂ :=
  ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i1 j1 * (U : Matrix (Fin 3) (Fin 3) ℂ) i2 j2
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k1 l1) * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k2 l2)
    ∂(probHaar (SU 3))

/-- DERIVED: `3` is the rank. -/
private theorem T4_lphase (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 i1 j1 i2 j2 k1 l1 k2 l2
      = (v i1 * v i2 * star (v k1) * star (v k2)) * T4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  unfold T4
  refine inv_left (⟨Matrix.diagonal v, hv⟩ : SU 3) _ (fun U => ?_)
  simp only [coe_diag_mul, star_mul']
  ring

/-- DERIVED: `3` is the rank. -/
private theorem T4_rphase (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 i1 j1 i2 j2 k1 l1 k2 l2
      = (v j1 * v j2 * star (v l1) * star (v l2)) * T4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  unfold T4
  refine inv_right (⟨Matrix.diagonal v, hv⟩ : SU 3) _ (fun U => ?_)
  simp only [coe_mul_diag, star_mul']
  ring

/-- Unbalanced rows kill the fourth moment.

DERIVED: `3` is the rank; `0` is the value. -/
private theorem T4_row_zero (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3)
    (h : ¬((i1 = k1 ∧ i2 = k2) ∨ (i1 = k2 ∧ i2 = k1))) : T4 i1 j1 i2 j2 k1 l1 k2 l2 = 0 := by
  by_contra hne
  have hA := T4_lphase phA phA_mem i1 j1 i2 j2 k1 l1 k2 l2
  have hB := T4_lphase phB phB_mem i1 j1 i2 j2 k1 l1 k2 l2
  rw [show phA i1 * phA i2 * star (phA k1) * star (phA k2)
      = Complex.I ^ (exA i1 + exA i2 + 3 * exA k1 + 3 * exA k2) from phase4 exA i1 i2 k1 k2] at hA
  rw [show phB i1 * phB i2 * star (phB k1) * star (phB k2)
      = Complex.I ^ (exB i1 + exB i2 + 3 * exB k1 + 3 * exB k2) from phase4 exB i1 i2 k1 k2] at hB
  exact h (dec4 i1 i2 k1 k2 (I_pow_eq_one (lam_one hA hne)) (I_pow_eq_one (lam_one hB hne)))

/-- Unbalanced columns kill the fourth moment.

DERIVED: `3` is the rank; `0` is the value. -/
private theorem T4_col_zero (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3)
    (h : ¬((j1 = l1 ∧ j2 = l2) ∨ (j1 = l2 ∧ j2 = l1))) : T4 i1 j1 i2 j2 k1 l1 k2 l2 = 0 := by
  by_contra hne
  have hA := T4_rphase phA phA_mem i1 j1 i2 j2 k1 l1 k2 l2
  have hB := T4_rphase phB phB_mem i1 j1 i2 j2 k1 l1 k2 l2
  rw [show phA j1 * phA j2 * star (phA l1) * star (phA l2)
      = Complex.I ^ (exA j1 + exA j2 + 3 * exA l1 + 3 * exA l2) from phase4 exA j1 j2 l1 l2] at hA
  rw [show phB j1 * phB j2 * star (phB l1) * star (phB l2)
      = Complex.I ^ (exB j1 + exB j2 + 3 * exB l1 + 3 * exB l2) from phase4 exB j1 j2 l1 l2] at hB
  exact h (dec4 j1 j2 l1 l2 (I_pow_eq_one (lam_one hA hne)) (I_pow_eq_one (lam_one hB hne)))

/-- Relabelling rows leaves the fourth moment unchanged (the sign enters four times).

DERIVED: `3` is the rank. -/
private theorem T4_rowperm (σ : Equiv.Perm (Fin 3)) (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 (σ i1) j1 (σ i2) j2 (σ k1) l1 (σ k2) l2 = T4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  unfold T4
  refine eq_left (PgS σ) (fun U => ?_)
  simp only [coe_PgS_mul, star_mul', star_sg]
  rcases sg_cases σ with hs | hs <;> rw [hs] <;> ring

/-- Relabelling columns leaves the fourth moment unchanged.

DERIVED: `3` is the rank. -/
private theorem T4_colperm (σ : Equiv.Perm (Fin 3)) (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 i1 (σ j1) i2 (σ j2) k1 (σ l1) k2 (σ l2) = T4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  unfold T4
  refine eq_right (QgS σ) (fun U => ?_)
  simp only [coe_mul_QgS, star_mul', star_sg]
  rcases sg_cases σ with hs | hs <;> rw [hs] <;> ring

/-- The two conjugated factors commute.

DERIVED: `3` is the rank. -/
private theorem T4_swapc (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 i1 j1 i2 j2 k1 l1 k2 l2 = T4 i1 j1 i2 j2 k2 l2 k1 l1 := by
  unfold T4
  congr 1
  funext U
  ring

/-- DERIVED: `3` is the rank. -/
private theorem wg4_rowperm (σ : Equiv.Perm (Fin 3)) (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    wg4 (σ i1) j1 (σ i2) j2 (σ k1) l1 (σ k2) l2 = wg4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  simp only [wg4, Equiv.apply_eq_iff_eq]

/-- DERIVED: `3` is the rank. -/
private theorem wg4_colperm (σ : Equiv.Perm (Fin 3)) (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    wg4 i1 (σ j1) i2 (σ j2) k1 (σ l1) k2 (σ l2) = wg4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  simp only [wg4, Equiv.apply_eq_iff_eq]

/-- DERIVED: `0` is the value; `3` is the rank. -/
private theorem wg4_row_zero (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3)
    (h : ¬((i1 = k1 ∧ i2 = k2) ∨ (i1 = k2 ∧ i2 = k1))) : wg4 i1 j1 i2 j2 k1 l1 k2 l2 = 0 := by
  have e1 : ¬(i1 = k1 ∧ i2 = k2 ∧ j1 = l1 ∧ j2 = l2) := fun h' => h (Or.inl ⟨h'.1, h'.2.1⟩)
  have e2 : ¬(i1 = k2 ∧ i2 = k1 ∧ j1 = l2 ∧ j2 = l1) := fun h' => h (Or.inr ⟨h'.1, h'.2.1⟩)
  have e3 : ¬(i1 = k1 ∧ i2 = k2 ∧ j1 = l2 ∧ j2 = l1) := fun h' => h (Or.inl ⟨h'.1, h'.2.1⟩)
  have e4 : ¬(i1 = k2 ∧ i2 = k1 ∧ j1 = l1 ∧ j2 = l2) := fun h' => h (Or.inr ⟨h'.1, h'.2.1⟩)
  unfold wg4
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4]
  ring

/-- DERIVED: `0` is the value; `3` is the rank. -/
private theorem wg4_col_zero (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3)
    (h : ¬((j1 = l1 ∧ j2 = l2) ∨ (j1 = l2 ∧ j2 = l1))) : wg4 i1 j1 i2 j2 k1 l1 k2 l2 = 0 := by
  have e1 : ¬(i1 = k1 ∧ i2 = k2 ∧ j1 = l1 ∧ j2 = l2) :=
    fun h' => h (Or.inl ⟨h'.2.2.1, h'.2.2.2⟩)
  have e2 : ¬(i1 = k2 ∧ i2 = k1 ∧ j1 = l2 ∧ j2 = l1) :=
    fun h' => h (Or.inr ⟨h'.2.2.1, h'.2.2.2⟩)
  have e3 : ¬(i1 = k1 ∧ i2 = k2 ∧ j1 = l2 ∧ j2 = l1) :=
    fun h' => h (Or.inr ⟨h'.2.2.1, h'.2.2.2⟩)
  have e4 : ¬(i1 = k2 ∧ i2 = k1 ∧ j1 = l1 ∧ j2 = l2) :=
    fun h' => h (Or.inl ⟨h'.2.2.1, h'.2.2.2⟩)
  unfold wg4
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4]
  ring

/-- Three terms of a sum over `Fin 3`, from a pointwise identity and the integral of its value.

DERIVED: `3` is the rank; `0, 1, 2` are the indices. -/
private theorem R_helper (F : Fin 3 → SU 3 → ℂ) (hF : ∀ j, Continuous (F j)) (G : SU 3 → ℂ)
    (c : ℂ) (hpt : ∀ U, ∑ j, F j U = G U) (hG : ∫ U, G U ∂(probHaar (SU 3)) = c) :
    ∫ U, F 0 U ∂(probHaar (SU 3)) + ∫ U, F 1 U ∂(probHaar (SU 3))
      + ∫ U, F 2 U ∂(probHaar (SU 3)) = c := by
  rw [← int_sum3 F hF, integral_congr_ae (Filter.Eventually.of_forall hpt), hG]

/-- Left invariance, expanded: `T4 = Σ g g ḡ ḡ · T4`.

DERIVED: `3` is the rank. -/
private theorem T4_left_expand (g : SU 3) (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 i1 j1 i2 j2 k1 l1 k2 l2 = ∑ a1 : Fin 3, ∑ a2 : Fin 3, ∑ b1 : Fin 3, ∑ b2 : Fin 3,
      ((g : Matrix (Fin 3) (Fin 3) ℂ) i1 a1 * (g : Matrix (Fin 3) (Fin 3) ℂ) i2 a2
        * star ((g : Matrix (Fin 3) (Fin 3) ℂ) k1 b1) * star ((g : Matrix (Fin 3) (Fin 3) ℂ) k2 b2))
        * T4 a1 j1 a2 j2 b1 l1 b2 l2 := by
  have step1 : T4 i1 j1 i2 j2 k1 l1 k2 l2 = ∫ U : SU 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3,
      ∑ b1 : Fin 3, ∑ b2 : Fin 3,
        ((g : Matrix (Fin 3) (Fin 3) ℂ) i1 a1 * (g : Matrix (Fin 3) (Fin 3) ℂ) i2 a2
          * star ((g : Matrix (Fin 3) (Fin 3) ℂ) k1 b1)
          * star ((g : Matrix (Fin 3) (Fin 3) ℂ) k2 b2))
        * ((U : Matrix (Fin 3) (Fin 3) ℂ) a1 j1 * (U : Matrix (Fin 3) (Fin 3) ℂ) a2 j2
          * star ((U : Matrix (Fin 3) (Fin 3) ℂ) b1 l1)
          * star ((U : Matrix (Fin 3) (Fin 3) ℂ) b2 l2)) ∂(probHaar (SU 3)) := by
    unfold T4
    symm
    refine eq_left g (fun U => ?_)
    simp only [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, star_add, star_mul']
    ring
  rw [step1, int_sum4]
  · refine sum4_congr (fun a1 a2 b1 b2 => ?_)
    exact integral_const_mul _ _
  · intro a1 a2 b1 b2
    exact continuous_const.mul (mono4_cont a1 j1 a2 j2 b1 l1 b2 l2)

/-- The rotation by `(3/5, 4/5)` in the plane of the first two rows.

CHOSEN: the Pythagorean pair `(3, 4, 5)` makes a rational element of `SO(2) ⊂ SU(3)` with both
entries nonzero; any such rotation serves. -/
private def rmat : Matrix (Fin 3) (Fin 3) ℂ := !![3 / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1]

/-- DERIVED: `3/5` is a rotation entry. -/
private theorem star_35 : star ((3 : ℂ) / 5) = 3 / 5 := by
  rw [← starRingEnd_apply, map_div₀, map_ofNat, map_ofNat]

/-- DERIVED: `4/5` is a rotation entry. -/
private theorem star_45 : star ((4 : ℂ) / 5) = 4 / 5 := by
  rw [← starRingEnd_apply, map_div₀, map_ofNat, map_ofNat]

/-- DERIVED: `3` is the rank; `9/25 + 16/25 = 1`. -/
private theorem rmat_mem : rmat ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, map_ofNat] <;>
      norm_num
  · simp [rmat, Matrix.det_fin_three] <;> norm_num

/-- The rotation as an element of `SU(3)`.

DERIVED: `3` is the rank. -/
private def RotG : SU 3 := ⟨rmat, rmat_mem⟩

/-- DERIVED: `3/5` is the `(0, 0)` entry of `rmat`; the `3` of `SU 3` is the rank. -/
private theorem rot00 : ((RotG : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) 0 0 = 3 / 5 := by
  show rmat 0 0 = 3 / 5
  simp [rmat]

/-- DERIVED: `−(4/5)` is the `(0, 1)` entry of `rmat`; `3` is the rank. -/
private theorem rot01 : ((RotG : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) 0 1 = -(4 / 5) := by
  show rmat 0 1 = -(4 / 5)
  simp [rmat]

/-- DERIVED: the `(0, 2)` entry of `rmat`, off the rotation plane; `3` is the rank. -/
private theorem rot02 : ((RotG : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) 0 2 = 0 := by
  show rmat 0 2 = 0
  simp [rmat]

/-- **The five fourth-moment values** `A = 1/6`, `B = 1/12`, `C = 1/12`, `D = 1/8`, `X = −1/24`.

DERIVED: `1/3` is `E|U₁₁|²`; `625 = 5⁴`, `337 = 3⁴ + 4⁴`, `576 = 4 · 3² · 4²` are the rotation's
coefficients; `1/6`, `1/12`, `1/12`, `1/8`, `−1/24` are the solution of the linear system, the last
two agreeing with `wg4`; `0`, `1` are the row and column indices of the five entries. -/
private theorem T4_vals :
    T4 0 0 0 0 0 0 0 0 = 1 / 6 ∧ T4 0 0 0 1 0 0 0 1 = 1 / 12 ∧ T4 0 0 1 0 0 0 1 0 = 1 / 12
      ∧ T4 0 0 1 1 0 0 1 1 = 1 / 8 ∧ T4 0 0 1 1 0 1 1 0 = -1 / 24 := by
  -- the first row sum
  have p1 : ∀ U : SU 3, ∑ j : Fin 3, (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * (U : Matrix (Fin 3) (Fin 3) ℂ) 0 j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0)
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 j)
      = (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0) := by
    intro U
    have hr := row_self U 0
    rw [Fin.sum_univ_three] at hr ⊢
    linear_combination ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0)) * hr
  have R1 : T4 0 0 0 0 0 0 0 0 + T4 0 0 0 1 0 0 0 1 + T4 0 0 0 2 0 0 0 2 = 1 / 3 :=
    R_helper (fun j U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * (U : Matrix (Fin 3) (Fin 3) ℂ) 0 j
        * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0) * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 j))
      (fun j => mono4_cont 0 0 0 j 0 0 0 j)
      (fun U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0))
      (1 / 3) p1 (T2_diag 0 0)
  -- the first column sum
  have p2 : ∀ U : SU 3, ∑ i : Fin 3, (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * (U : Matrix (Fin 3) (Fin 3) ℂ) i 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0)
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) i 0)
      = (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0) := by
    intro U
    have hc := col_self U 0
    rw [Fin.sum_univ_three] at hc ⊢
    linear_combination ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0)) * hc
  have R2 : T4 0 0 0 0 0 0 0 0 + T4 0 0 1 0 0 0 1 0 + T4 0 0 2 0 0 0 2 0 = 1 / 3 :=
    R_helper (fun i U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * (U : Matrix (Fin 3) (Fin 3) ℂ) i 0
        * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0) * star ((U : Matrix (Fin 3) (Fin 3) ℂ) i 0))
      (fun i => mono4_cont 0 0 i 0 0 0 i 0)
      (fun U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0))
      (1 / 3) p2 (T2_diag 0 0)
  -- the second row sum
  have p3 : ∀ U : SU 3, ∑ j : Fin 3, (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * (U : Matrix (Fin 3) (Fin 3) ℂ) 1 j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0)
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 1 j)
      = (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0) := by
    intro U
    have hr := row_self U 1
    rw [Fin.sum_univ_three] at hr ⊢
    linear_combination ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0)) * hr
  have R3 : T4 0 0 1 0 0 0 1 0 + T4 0 0 1 1 0 0 1 1 + T4 0 0 1 2 0 0 1 2 = 1 / 3 :=
    R_helper (fun j U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * (U : Matrix (Fin 3) (Fin 3) ℂ) 1 j
        * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0) * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 1 j))
      (fun j => mono4_cont 0 0 1 j 0 0 1 j)
      (fun U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0))
      (1 / 3) p3 (T2_diag 0 0)
  -- orthogonality of rows 0 and 1
  have p4 : ∀ U : SU 3, ∑ j : Fin 3, (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * (U : Matrix (Fin 3) (Fin 3) ℂ) 1 j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 1 0)
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 j) = 0 := by
    intro U
    have ho := row_orth U 1 0 (by decide)
    rw [Fin.sum_univ_three] at ho ⊢
    linear_combination ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 1 0)) * ho
  have R4 : T4 0 0 1 0 1 0 0 0 + T4 0 0 1 1 1 0 0 1 + T4 0 0 1 2 1 0 0 2 = 0 :=
    R_helper (fun j U => (U : Matrix (Fin 3) (Fin 3) ℂ) 0 0 * (U : Matrix (Fin 3) (Fin 3) ℂ) 1 j
        * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 1 0) * star ((U : Matrix (Fin 3) (Fin 3) ℂ) 0 j))
      (fun j => mono4_cont 0 0 1 j 1 0 0 j) (fun _ => 0) 0 p4 (by simp)
  -- the rotation
  have z0001 : T4 0 0 0 0 0 0 1 0 = 0 := T4_row_zero 0 0 0 0 0 0 1 0 (by decide)
  have z0010 : T4 0 0 0 0 1 0 0 0 = 0 := T4_row_zero 0 0 0 0 1 0 0 0 (by decide)
  have z0011 : T4 0 0 0 0 1 0 1 0 = 0 := T4_row_zero 0 0 0 0 1 0 1 0 (by decide)
  have z0100 : T4 0 0 1 0 0 0 0 0 = 0 := T4_row_zero 0 0 1 0 0 0 0 0 (by decide)
  have z0111 : T4 0 0 1 0 1 0 1 0 = 0 := T4_row_zero 0 0 1 0 1 0 1 0 (by decide)
  have z1000 : T4 1 0 0 0 0 0 0 0 = 0 := T4_row_zero 1 0 0 0 0 0 0 0 (by decide)
  have z1011 : T4 1 0 0 0 1 0 1 0 = 0 := T4_row_zero 1 0 0 0 1 0 1 0 (by decide)
  have z1100 : T4 1 0 1 0 0 0 0 0 = 0 := T4_row_zero 1 0 1 0 0 0 0 0 (by decide)
  have z1101 : T4 1 0 1 0 0 0 1 0 = 0 := T4_row_zero 1 0 1 0 0 0 1 0 (by decide)
  have z1110 : T4 1 0 1 0 1 0 0 0 = 0 := T4_row_zero 1 0 1 0 1 0 0 0 (by decide)
  have e0110 : T4 0 0 1 0 1 0 0 0 = T4 0 0 1 0 0 0 1 0 := T4_swapc 0 0 1 0 1 0 0 0
  have e1010 : T4 1 0 0 0 1 0 0 0 = T4 0 0 1 0 0 0 1 0 := by
    have h := T4_rowperm (Equiv.swap (0 : Fin 3) 1) 0 0 1 0 0 0 1 0
    rwa [sw01_0, sw01_1] at h
  have e1001 : T4 1 0 0 0 0 0 1 0 = T4 0 0 1 0 0 0 1 0 := by
    have h := T4_rowperm (Equiv.swap (0 : Fin 3) 1) 0 0 1 0 1 0 0 0
    rw [sw01_0, sw01_1] at h
    rw [h, e0110]
  have e1111 : T4 1 0 1 0 1 0 1 0 = T4 0 0 0 0 0 0 0 0 := by
    have h := T4_rowperm (Equiv.swap (0 : Fin 3) 1) 0 0 0 0 0 0 0 0
    rwa [sw01_0] at h
  have R5 : T4 0 0 0 0 0 0 0 0 = 2 * T4 0 0 1 0 0 0 1 0 := by
    have h := T4_left_expand RotG 0 0 0 0 0 0 0 0
    simp only [Fin.sum_univ_three, rot00, rot01, rot02, star_35, star_45, star_neg, star_zero,
      mul_zero, zero_mul, add_zero, zero_add] at h
    rw [z0001, z0010, z0011, z0100, e0110, z0111, z1000, e1001, e1010, z1011, z1100, z1101,
      z1110, e1111] at h
    linear_combination (625 / 288 : ℂ) * h
  -- identifications by relabelling
  have iB2 : T4 0 0 0 2 0 0 0 2 = T4 0 0 0 1 0 0 0 1 := by
    have h := T4_colperm (Equiv.swap (1 : Fin 3) 2) 0 0 0 1 0 0 0 1
    rwa [sw12_0, sw12_1] at h
  have iC2 : T4 0 0 2 0 0 0 2 0 = T4 0 0 1 0 0 0 1 0 := by
    have h := T4_rowperm (Equiv.swap (1 : Fin 3) 2) 0 0 1 0 0 0 1 0
    rwa [sw12_0, sw12_1] at h
  have iD2 : T4 0 0 1 2 0 0 1 2 = T4 0 0 1 1 0 0 1 1 := by
    have h := T4_colperm (Equiv.swap (1 : Fin 3) 2) 0 0 1 1 0 0 1 1
    rwa [sw12_0, sw12_1] at h
  have iX2 : T4 0 0 1 2 1 0 0 2 = T4 0 0 1 1 1 0 0 1 := by
    have h := T4_colperm (Equiv.swap (1 : Fin 3) 2) 0 0 1 1 1 0 0 1
    rwa [sw12_0, sw12_1] at h
  have iX' : T4 0 0 1 1 1 0 0 1 = T4 0 0 1 1 0 1 1 0 := T4_swapc 0 0 1 1 1 0 0 1
  rw [iB2] at R1
  rw [iC2] at R2
  rw [iD2] at R3
  rw [iX2, iX', e0110] at R4
  have hC : T4 0 0 1 0 0 0 1 0 = 1 / 12 := by linear_combination (R2 - R5) / 4
  have hA : T4 0 0 0 0 0 0 0 0 = 1 / 6 := by linear_combination R5 + 2 * hC
  have hB : T4 0 0 0 1 0 0 0 1 = 1 / 12 := by linear_combination (R1 - hA) / 2
  have hD : T4 0 0 1 1 0 0 1 1 = 1 / 8 := by linear_combination (R3 - hC) / 2
  have hX : T4 0 0 1 1 0 1 1 0 = -1 / 24 := by linear_combination (R4 - hC) / 2
  exact ⟨hA, hB, hC, hD, hX⟩

/-! ### The nine canonical index patterns

Rows `(i₁, i₂, k₁, k₂) ∈ {(0,0,0,0), (0,1,0,1), (0,1,1,0)}`, columns likewise.
DERIVED: the values are `T4_vals`; `wg4` is evaluated at the literal indices. -/

private theorem cR0C0 : T4 0 0 0 0 0 0 0 0 = wg4 0 0 0 0 0 0 0 0 := by
  rw [T4_vals.1]; norm_num [wg4]
private theorem cR0C1 : T4 0 0 0 1 0 0 0 1 = wg4 0 0 0 1 0 0 0 1 := by
  rw [T4_vals.2.1]; norm_num [wg4]
private theorem cR0C2 : T4 0 0 0 1 0 1 0 0 = wg4 0 0 0 1 0 1 0 0 := by
  rw [T4_swapc 0 0 0 1 0 1 0 0, T4_vals.2.1]; norm_num [wg4]
private theorem cR1C0 : T4 0 0 1 0 0 0 1 0 = wg4 0 0 1 0 0 0 1 0 := by
  rw [T4_vals.2.2.1]; norm_num [wg4]
private theorem cR1C1 : T4 0 0 1 1 0 0 1 1 = wg4 0 0 1 1 0 0 1 1 := by
  rw [T4_vals.2.2.2.1]; norm_num [wg4]
private theorem cR1C2 : T4 0 0 1 1 0 1 1 0 = wg4 0 0 1 1 0 1 1 0 := by
  rw [T4_vals.2.2.2.2]; norm_num [wg4]
private theorem cR2C0 : T4 0 0 1 0 1 0 0 0 = wg4 0 0 1 0 1 0 0 0 := by
  rw [T4_swapc 0 0 1 0 1 0 0 0, T4_vals.2.2.1]; norm_num [wg4]
private theorem cR2C1 : T4 0 0 1 1 1 0 0 1 = wg4 0 0 1 1 1 0 0 1 := by
  rw [T4_swapc 0 0 1 1 1 0 0 1, T4_vals.2.2.2.2]; norm_num [wg4]
private theorem cR2C2 : T4 0 0 1 1 1 1 0 0 = wg4 0 0 1 1 1 1 0 0 := by
  rw [T4_swapc 0 0 1 1 1 1 0 0, T4_vals.2.2.2.1]; norm_num [wg4]

/-- Fixed rows, arbitrary columns: phases or a column relabelling reduce to three canonical
column patterns.

DERIVED: `0`, `1` are the canonical column indices; `3` is the rank. -/
private theorem cols_stage (a b c d : Fin 3)
    (h0 : T4 a 0 b 0 c 0 d 0 = wg4 a 0 b 0 c 0 d 0)
    (h1 : T4 a 0 b 1 c 0 d 1 = wg4 a 0 b 1 c 0 d 1)
    (h2 : T4 a 0 b 1 c 1 d 0 = wg4 a 0 b 1 c 1 d 0) (j1 j2 l1 l2 : Fin 3) :
    T4 a j1 b j2 c l1 d l2 = wg4 a j1 b j2 c l1 d l2 := by
  have same : ∀ j : Fin 3, T4 a j b j c j d j = wg4 a j b j c j d j := by
    intro j
    obtain ⟨σ, hσ⟩ := exists_perm1 j
    rw [← hσ, T4_colperm σ a 0 b 0 c 0 d 0, wg4_colperm σ a 0 b 0 c 0 d 0]
    exact h0
  by_cases hc : (j1 = l1 ∧ j2 = l2) ∨ (j1 = l2 ∧ j2 = l1)
  · rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]
      by_cases hj : j1 = j2
      · rw [← hj]
        exact same j1
      · obtain ⟨σ, hσ0, hσ1⟩ := exists_perm2 j1 j2 hj
        rw [← hσ0, ← hσ1, T4_colperm σ a 0 b 1 c 0 d 1, wg4_colperm σ a 0 b 1 c 0 d 1]
        exact h1
    · rw [← e1, ← e2]
      by_cases hj : j1 = j2
      · rw [← hj]
        exact same j1
      · obtain ⟨σ, hσ0, hσ1⟩ := exists_perm2 j1 j2 hj
        rw [← hσ0, ← hσ1, T4_colperm σ a 0 b 1 c 1 d 0, wg4_colperm σ a 0 b 1 c 1 d 0]
        exact h2
  · rw [T4_col_zero a j1 b j2 c l1 d l2 hc, wg4_col_zero a j1 b j2 c l1 d l2 hc]

/-- Rows `(a, b, a, b)`.

DERIVED: `3` is the rank; the proof reduces to the canonical row indices `0`, `1`. -/
private theorem T4_R_same (a b j1 j2 l1 l2 : Fin 3) :
    T4 a j1 b j2 a l1 b l2 = wg4 a j1 b j2 a l1 b l2 := by
  by_cases hab : a = b
  · rw [← hab]
    obtain ⟨σ, hσ⟩ := exists_perm1 a
    rw [← hσ, T4_rowperm σ 0 j1 0 j2 0 l1 0 l2, wg4_rowperm σ 0 j1 0 j2 0 l1 0 l2]
    exact cols_stage 0 0 0 0 cR0C0 cR0C1 cR0C2 j1 j2 l1 l2
  · obtain ⟨σ, hσ0, hσ1⟩ := exists_perm2 a b hab
    rw [← hσ0, ← hσ1, T4_rowperm σ 0 j1 1 j2 0 l1 1 l2, wg4_rowperm σ 0 j1 1 j2 0 l1 1 l2]
    exact cols_stage 0 1 0 1 cR1C0 cR1C1 cR1C2 j1 j2 l1 l2

/-- Rows `(a, b, b, a)`.

DERIVED: `3` is the rank; the proof reduces to the canonical row indices `0`, `1`. -/
private theorem T4_R_cross (a b j1 j2 l1 l2 : Fin 3) :
    T4 a j1 b j2 b l1 a l2 = wg4 a j1 b j2 b l1 a l2 := by
  by_cases hab : a = b
  · rw [← hab]
    exact T4_R_same a a j1 j2 l1 l2
  · obtain ⟨σ, hσ0, hσ1⟩ := exists_perm2 a b hab
    rw [← hσ0, ← hσ1, T4_rowperm σ 0 j1 1 j2 1 l1 0 l2, wg4_rowperm σ 0 j1 1 j2 1 l1 0 l2]
    exact cols_stage 0 1 1 0 cR2C0 cR2C1 cR2C2 j1 j2 l1 l2

/-- DERIVED: `3` is the rank. -/
private theorem T4_eq_wg4 (i1 j1 i2 j2 k1 l1 k2 l2 : Fin 3) :
    T4 i1 j1 i2 j2 k1 l1 k2 l2 = wg4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  by_cases hr : (i1 = k1 ∧ i2 = k2) ∨ (i1 = k2 ∧ i2 = k1)
  · rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]
      exact T4_R_same i1 i2 j1 j2 l1 l2
    · rw [← e1, ← e2]
      exact T4_R_cross i1 i2 j1 j2 l1 l2
  · rw [T4_row_zero i1 j1 i2 j2 k1 l1 k2 l2 hr, wg4_row_zero i1 j1 i2 j2 k1 l1 k2 l2 hr]

/-- **Fourth moments**: `E Uᵢ₁ⱼ₁ Uᵢ₂ⱼ₂ Ū_k₁l₁ Ū_k₂l₂ = wg4` (step 2 of the module docstring).

DERIVED: `3` is the rank. -/
theorem haar_su3_fourth (i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ : Fin 3) :
    ∫ U : SU 3, (U : Matrix (Fin 3) (Fin 3) ℂ) i₁ j₁ * (U : Matrix (Fin 3) (Fin 3) ℂ) i₂ j₂
        * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k₁ l₁) * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k₂ l₂)
      ∂(probHaar (SU 3)) = wg4 i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ :=
  T4_eq_wg4 i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂

#print axioms haar_su3_fourth

/-! ## 6. The quartic -/

/-- `tr(UF) = Σᵢⱼ Uᵢⱼ Fⱼᵢ`.

DERIVED: `3` is the rank. -/
private theorem trace_expand (U : SU 3) (F : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F)
      = ∑ i, ∑ j, (U : Matrix (Fin 3) (Fin 3) ℂ) i j * F j i := by
  rw [Matrix.trace_fin_three]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]

/-- `conj tr(UF) = Σₖₗ Ūₖₗ F̄ₗₖ`.

DERIVED: `3` is the rank. -/
private theorem trace_star_expand (U : SU 3) (F : Matrix (Fin 3) (Fin 3) ℂ) :
    star (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F))
      = ∑ k, ∑ l, star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l) * star (F l k) := by
  rw [trace_expand, star_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [star_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [star_mul']

/-- `|tr(UA)|⁴` as an eightfold sum of monomials.

DERIVED: `2` is the square of `normSq`; `3` is the rank. -/
private theorem quartic_expand (A : Matrix (Fin 3) (Fin 3) ℂ) (U : SU 3) :
    ((Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)) ^ 2 : ℝ) : ℂ)
      = ∑ i1 : Fin 3, ∑ j1 : Fin 3, ∑ i2 : Fin 3, ∑ j2 : Fin 3, ∑ k1 : Fin 3, ∑ l1 : Fin 3,
          ∑ k2 : Fin 3, ∑ l2 : Fin 3,
            (A j1 i1 * A j2 i2 * star (A l1 k1) * star (A l2 k2))
              * ((U : Matrix (Fin 3) (Fin 3) ℂ) i1 j1 * (U : Matrix (Fin 3) (Fin 3) ℂ) i2 j2
                * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k1 l1)
                * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k2 l2)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj, starRingEnd_apply,
    show ∀ x y : ℂ, (x * y) ^ 2 = (x * x) * (y * y) from fun x y => by ring,
    trace_star_expand, trace_expand, mul_sum22, mul_sum22, mul_sum44]
  exact sum4_congr (fun i1 j1 i2 j2 => sum4_congr (fun k1 l1 k2 l2 => by ring))

/-- `E|tr(UA)|⁴` as an eightfold sum of fourth moments.

DERIVED: `2` is the square of `normSq`; `3` is the rank. -/
private theorem quartic_int (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, ((Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)) ^ 2 : ℝ) : ℂ)
        ∂(probHaar (SU 3))
      = ∑ i1 : Fin 3, ∑ j1 : Fin 3, ∑ i2 : Fin 3, ∑ j2 : Fin 3, ∑ k1 : Fin 3, ∑ l1 : Fin 3,
          ∑ k2 : Fin 3, ∑ l2 : Fin 3,
            (A j1 i1 * A j2 i2 * star (A l1 k1) * star (A l2 k2))
              * T4 i1 j1 i2 j2 k1 l1 k2 l2 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (quartic_expand A)), int_sum4]
  · refine sum4_congr (fun i1 j1 i2 j2 => ?_)
    rw [int_sum4]
    · refine sum4_congr (fun k1 l1 k2 l2 => ?_)
      exact integral_const_mul _ _
    · intro k1 l1 k2 l2
      exact continuous_const.mul (mono4_cont i1 j1 i2 j2 k1 l1 k2 l2)
  · intro i1 j1 i2 j2
    exact continuous_finsetSum _ (fun k1 _ => continuous_finsetSum _ (fun l1 _ =>
      continuous_finsetSum _ (fun k2 _ => continuous_finsetSum _ (fun l2 _ =>
        continuous_const.mul (mono4_cont i1 j1 i2 j2 k1 l1 k2 l2)))))

/-- A Kronecker indicator collapses a fourfold sum.

DERIVED: `1`, `0` are the indicator values; `3` is the rank. -/
private theorem collapse (X : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (a b c d : Fin 3) :
    ∑ k1, ∑ l1, ∑ k2, ∑ l2,
        X k1 l1 k2 l2 * (if k1 = a ∧ l1 = b ∧ k2 = c ∧ l2 = d then (1 : ℂ) else 0)
      = X a b c d := by
  rw [Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single b]
    · rw [Fintype.sum_eq_single c]
      · rw [Fintype.sum_eq_single d]
        · rw [if_pos ⟨rfl, rfl, rfl, rfl⟩, mul_one]
        · intro x hx
          rw [if_neg (fun (h : a = a ∧ b = b ∧ c = c ∧ x = d) => hx h.2.2.2), mul_zero]
      · intro x hx
        refine Finset.sum_eq_zero (fun y _ => ?_)
        rw [if_neg (fun (h : a = a ∧ b = b ∧ x = c ∧ y = d) => hx h.2.2.1), mul_zero]
    · intro x hx
      refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun z _ => ?_))
      rw [if_neg (fun (h : a = a ∧ x = b ∧ y = c ∧ z = d) => hx h.2.1), mul_zero]
  · intro x hx
    refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun z _ =>
      Finset.sum_eq_zero (fun t _ => ?_)))
    rw [if_neg (fun (h : x = a ∧ y = b ∧ z = c ∧ t = d) => hx h.1), mul_zero]

/-- **Contracting `wg4`** against the conjugated pair of indices.

DERIVED: `1/8`, `1/24` are `wg4`'s coefficients; `3` is the rank. -/
private theorem wg4_contract (i1 j1 i2 j2 : Fin 3) (X : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ k1, ∑ l1, ∑ k2, ∑ l2, X k1 l1 k2 l2 * wg4 i1 j1 i2 j2 k1 l1 k2 l2
      = (1 / 8) * (X i1 j1 i2 j2 + X i2 j2 i1 j1) - (1 / 24) * (X i1 j2 i2 j1 + X i2 j1 i1 j2) := by
  have hpt : ∀ k1 l1 k2 l2 : Fin 3, X k1 l1 k2 l2 * wg4 i1 j1 i2 j2 k1 l1 k2 l2
      = (1 / 8) * (X k1 l1 k2 l2 * (if k1 = i1 ∧ l1 = j1 ∧ k2 = i2 ∧ l2 = j2 then (1 : ℂ) else 0))
        + (1 / 8) * (X k1 l1 k2 l2 * (if k1 = i2 ∧ l1 = j2 ∧ k2 = i1 ∧ l2 = j1 then (1 : ℂ) else 0))
        + (-(1 / 24)) * (X k1 l1 k2 l2
            * (if k1 = i1 ∧ l1 = j2 ∧ k2 = i2 ∧ l2 = j1 then (1 : ℂ) else 0))
        + (-(1 / 24)) * (X k1 l1 k2 l2
            * (if k1 = i2 ∧ l1 = j1 ∧ k2 = i1 ∧ l2 = j2 then (1 : ℂ) else 0)) := by
    intro k1 l1 k2 l2
    have e1 : (if i1 = k1 ∧ i2 = k2 ∧ j1 = l1 ∧ j2 = l2 then (1 : ℂ) else 0)
        = (if k1 = i1 ∧ l1 = j1 ∧ k2 = i2 ∧ l2 = j2 then (1 : ℂ) else 0) :=
      if_congr ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3.symm, h2.symm, h4.symm⟩⟩ rfl rfl
    have e2 : (if i1 = k2 ∧ i2 = k1 ∧ j1 = l2 ∧ j2 = l1 then (1 : ℂ) else 0)
        = (if k1 = i2 ∧ l1 = j2 ∧ k2 = i1 ∧ l2 = j1 then (1 : ℂ) else 0) :=
      if_congr ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2.symm, h4.symm, h1.symm, h3.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h1.symm, h4.symm, h2.symm⟩⟩ rfl rfl
    have e3 : (if i1 = k1 ∧ i2 = k2 ∧ j1 = l2 ∧ j2 = l1 then (1 : ℂ) else 0)
        = (if k1 = i1 ∧ l1 = j2 ∧ k2 = i2 ∧ l2 = j1 then (1 : ℂ) else 0) :=
      if_congr ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h4.symm, h2.symm, h3.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3.symm, h4.symm, h2.symm⟩⟩ rfl rfl
    have e4 : (if i1 = k2 ∧ i2 = k1 ∧ j1 = l1 ∧ j2 = l2 then (1 : ℂ) else 0)
        = (if k1 = i2 ∧ l1 = j1 ∧ k2 = i1 ∧ l2 = j2 then (1 : ℂ) else 0) :=
      if_congr ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2.symm, h3.symm, h1.symm, h4.symm⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨h3.symm, h1.symm, h2.symm, h4.symm⟩⟩ rfl rfl
    unfold wg4
    rw [e1, e2, e3, e4]
    ring
  rw [sum4_congr hpt]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [collapse, collapse, collapse, collapse]
  ring

/-- **The contracted quartic**:
`Σ P · E(UUŪŪ) = (1/4)(Σ|Aᵢⱼ|²)² − (1/12) Σ_{pq} |Σⱼ A_{jp} Ā_{jq}|²`.

DERIVED: `1/4 = 2 · 1/8`, `1/12 = 2 · 1/24`; `2` is the square; `3` is the rank. -/
private theorem quartic_value (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ i1 : Fin 3, ∑ j1 : Fin 3, ∑ i2 : Fin 3, ∑ j2 : Fin 3, ∑ k1 : Fin 3, ∑ l1 : Fin 3,
      ∑ k2 : Fin 3, ∑ l2 : Fin 3,
        (A j1 i1 * A j2 i2 * star (A l1 k1) * star (A l2 k2)) * T4 i1 j1 i2 j2 k1 l1 k2 l2
      = (1 / 4) * (∑ i : Fin 3, ∑ j : Fin 3, A i j * star (A i j)) ^ 2
        - (1 / 12) * ∑ p : Fin 3, ∑ q : Fin 3,
          (∑ j : Fin 3, A j p * star (A j q)) * star (∑ j : Fin 3, A j p * star (A j q)) := by
  simp only [T4_eq_wg4]
  rw [sum4_congr (fun i1 j1 i2 j2 => wg4_contract i1 j1 i2 j2
    (fun k1 l1 k2 l2 => A j1 i1 * A j2 i2 * star (A l1 k1) * star (A l2 k2)))]
  simp only [Fin.sum_univ_three, star_add, star_mul', star_star]
  ring

/-- **The quartic bound**: `E|tr(UA)|⁴ ≤ ‖A‖⁴_F/4`.

DERIVED: `3` is the rank; `2` is the square of `normSq` (fourth power of the modulus) and of the
Frobenius norm; `4`: `E|tr(UA)|⁴ = (2 · 1/8)(tr B)² − (2 · 1/24) tr B² ≤ (1/4)(tr B)²`. -/
theorem haar_su3_trace_fourth_le (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)) ^ 2
      ∂(probHaar (SU 3)) ≤ (∑ i, ∑ j, Complex.normSq (A i j)) ^ 2 / 4 := by
  have hC := quartic_int A
  rw [quartic_value, integral_complex_ofReal] at hC
  have hN : (∑ i : Fin 3, ∑ j : Fin 3, A i j * star (A i j))
      = ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← Complex.mul_conj, starRingEnd_apply]
  have hT : (∑ p : Fin 3, ∑ q : Fin 3,
      (∑ j : Fin 3, A j p * star (A j q)) * star (∑ j : Fin 3, A j p * star (A j q)))
      = ((∑ p : Fin 3, ∑ q : Fin 3, Complex.normSq (∑ j : Fin 3, A j p * star (A j q)) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [← Complex.mul_conj, starRingEnd_apply]
  rw [hN, hT] at hC
  have hre : ∫ U : SU 3, Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)) ^ 2
        ∂(probHaar (SU 3))
      = (∑ i, ∑ j, Complex.normSq (A i j)) ^ 2 / 4
        - 1 / 12 * ∑ p : Fin 3, ∑ q : Fin 3, Complex.normSq (∑ j : Fin 3, A j p * star (A j q)) := by
    apply Complex.ofReal_injective
    rw [hC]
    push_cast
    ring
  have hnn : 0 ≤ ∑ p : Fin 3, ∑ q : Fin 3, Complex.normSq (∑ j : Fin 3, A j p * star (A j q)) :=
    Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ => Complex.normSq_nonneg _))
  rw [hre]
  linarith

#print axioms haar_su3_trace_fourth_le

/-! ## 7. Third moments -/

/-- The third-moment integral `E (UA)_{a₀b₀} (UA)_{a₁b₁} (UA)_{a₂b₂}`.

DERIVED: `3` is the rank and the number of factors. -/
private def Q3 (A : Matrix (Fin 3) (Fin 3) ℂ) (a0 b0 a1 b1 a2 b2 : Fin 3) : ℂ :=
  ∫ U : SU 3, ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a0 b0 * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a1 b1
      * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a2 b2 ∂(probHaar (SU 3))

/-- DERIVED: `3` is the rank. -/
private theorem Q3_lphase (v : Fin 3 → ℂ)
    (hv : Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (a0 b0 a1 b1 a2 b2 : Fin 3) :
    Q3 A a0 b0 a1 b1 a2 b2 = (v a0 * v a1 * v a2) * Q3 A a0 b0 a1 b1 a2 b2 := by
  unfold Q3
  refine inv_left (⟨Matrix.diagonal v, hv⟩ : SU 3) _ (fun U => ?_)
  simp only [coe_diag_mul_mat]
  ring

/-- Rows of `UA` that are not a permutation of `(0, 1, 2)` kill the third moment.

DERIVED: `3` is the rank; `0` is the value. -/
private theorem Q3_zero (A : Matrix (Fin 3) (Fin 3) ℂ) (a0 b0 a1 b1 a2 b2 : Fin 3)
    (h : ¬(a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2)) : Q3 A a0 b0 a1 b1 a2 b2 = 0 := by
  by_contra hne
  have hA := Q3_lphase phA phA_mem A a0 b0 a1 b1 a2 b2
  have hB := Q3_lphase phB phB_mem A a0 b0 a1 b1 a2 b2
  rw [show phA a0 * phA a1 * phA a2 = Complex.I ^ (exA a0 + exA a1 + exA a2)
    from phase3 exA a0 a1 a2] at hA
  rw [show phB a0 * phB a1 * phB a2 = Complex.I ^ (exB a0 + exB a1 + exB a2)
    from phase3 exB a0 a1 a2] at hB
  exact h (dec3 a0 a1 a2 (I_pow_eq_one (lam_one hA hne)) (I_pow_eq_one (lam_one hB hne)))

/-- Relabelling rows of `UA` multiplies the third moment by the sign (it enters three times).

DERIVED: `3` is the rank. -/
private theorem Q3_perm (A : Matrix (Fin 3) (Fin 3) ℂ) (σ : Equiv.Perm (Fin 3))
    (a0 b0 a1 b1 a2 b2 : Fin 3) :
    Q3 A a0 b0 a1 b1 a2 b2 = sg σ * Q3 A (σ a0) b0 (σ a1) b1 (σ a2) b2 := by
  unfold Q3
  rw [← integral_const_mul]
  symm
  refine eq_left (PgS σ) (fun U => ?_)
  simp only [coe_PgS_mul_mat]
  rcases sg_cases σ with hs | hs <;> rw [hs] <;> ring

/-- Three distinct factors of a product over `Fin 3` are the three factors.

DERIVED: `0, 1, 2` are the values of `Fin 3`. -/
private theorem prod_perm3 (f : Fin 3 → ℂ) (a0 a1 a2 : Fin 3) (h : a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2) :
    f a0 * f a1 * f a2 = f 0 * f 1 * f 2 := by
  rcases perm3_cases a0 a1 a2 h.1 h.2.1 h.2.2 with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      | ⟨rfl, rfl, rfl⟩ <;> ring

/-- The diagonal third moments of `UA`.

DERIVED: `0, 1, 2` are the diagonal positions; `0` is the value off the permutations; `3` is the
rank. -/
private theorem Q3_diag (A : Matrix (Fin 3) (Fin 3) ℂ) (a0 a1 a2 : Fin 3) :
    Q3 A a0 a0 a1 a1 a2 a2 = if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2 then Q3 A 0 0 1 1 2 2 else 0 := by
  by_cases h : a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2
  · rw [if_pos h]
    unfold Q3
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    exact prod_perm3 (fun a => ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a a) a0 a1 a2 h
  · rw [if_neg h]
    exact Q3_zero A a0 a0 a1 a1 a2 a2 h

/-- `6 E M₁₁M₂₂M₃₃ = E det M = det A`, `M = UA`.

DERIVED: `6 = 3!` terms of `det_fin_three`, each `sgn σ · sgn σ = 1` times the diagonal moment;
`0, 1, 2` are the diagonal positions; `3` is the rank. -/
private theorem Q3_det (A : Matrix (Fin 3) (Fin 3) ℂ) : 6 * Q3 A 0 0 1 1 2 2 = A.det := by
  haveI := MassGap.CompactGauge.isProbabilityMeasure_probHaar (SU 3)
  have hconst : ∫ U : SU 3, ((U : Matrix (Fin 3) (Fin 3) ℂ) * A).det ∂(probHaar (SU 3))
      = A.det := by
    have hpt : ∀ U : SU 3, ((U : Matrix (Fin 3) (Fin 3) ℂ) * A).det = A.det := by
      intro U
      rw [Matrix.det_mul, (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2, one_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const]
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun U : SU 3 => Matrix.det_fin_three ((U : Matrix (Fin 3) (Fin 3) ℂ) * A)))] at hconst
  have k1 := cont3 A 0 0 1 1 2 2
  have k2 := cont3 A 0 0 1 2 2 1
  have k3 := cont3 A 0 1 1 0 2 2
  have k4 := cont3 A 0 1 1 2 2 0
  have k5 := cont3 A 0 2 1 0 2 1
  have k6 := cont3 A 0 2 1 1 2 0
  rw [integral_sub, integral_add, integral_add, integral_sub, integral_sub] at hconst
  rotate_left
  all_goals first
    | exact intC k1 | exact intC k2 | exact intC k3 | exact intC k4 | exact intC k5
    | exact intC k6 | exact intC (k1.sub k2) | exact intC ((k1.sub k2).sub k3)
    | exact intC (((k1.sub k2).sub k3).add k4)
    | exact intC ((((k1.sub k2).sub k3).add k4).add k5)
    | skip
  have hc : Q3 A 0 0 1 1 2 2 - Q3 A 0 0 1 2 2 1 - Q3 A 0 1 1 0 2 2 + Q3 A 0 1 1 2 2 0
      + Q3 A 0 2 1 0 2 1 - Q3 A 0 2 1 1 2 0 = A.det := hconst
  have r1 : Q3 A 0 0 2 2 1 1 = Q3 A 0 0 1 1 2 2 := by
    unfold Q3; congr 1; funext U; ring
  have r2 : Q3 A 1 1 0 0 2 2 = Q3 A 0 0 1 1 2 2 := by
    unfold Q3; congr 1; funext U; ring
  have r3 : Q3 A 1 1 2 2 0 0 = Q3 A 0 0 1 1 2 2 := by
    unfold Q3; congr 1; funext U; ring
  have r4 : Q3 A 2 2 0 0 1 1 = Q3 A 0 0 1 1 2 2 := by
    unfold Q3; congr 1; funext U; ring
  have r5 : Q3 A 2 2 1 1 0 0 = Q3 A 0 0 1 1 2 2 := by
    unfold Q3; congr 1; funext U; ring
  have p2 : Q3 A 0 0 1 2 2 1 = -Q3 A 0 0 1 1 2 2 := by
    have h := Q3_perm A (Equiv.swap (1 : Fin 3) 2) 0 0 1 2 2 1
    rw [sw12_0, sw12_1, sw12_2, sg_swap 1 2 (by decide)] at h
    rw [h, r1]; ring
  have p3 : Q3 A 0 1 1 0 2 2 = -Q3 A 0 0 1 1 2 2 := by
    have h := Q3_perm A (Equiv.swap (0 : Fin 3) 1) 0 1 1 0 2 2
    rw [sw01_0, sw01_1, sw01_2, sg_swap 0 1 (by decide)] at h
    rw [h, r2]; ring
  have p4 : Q3 A 0 1 1 2 2 0 = Q3 A 0 0 1 1 2 2 := by
    have h := Q3_perm A (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) 0 1 1 2 2 0
    rw [cy1_0, cy1_1, cy1_2, sg_mul, sg_swap 0 1 (by decide), sg_swap 1 2 (by decide)] at h
    rw [h, r3]; ring
  have p5 : Q3 A 0 2 1 0 2 1 = Q3 A 0 0 1 1 2 2 := by
    have h := Q3_perm A (Equiv.swap (0 : Fin 3) 2 * Equiv.swap 1 2) 0 2 1 0 2 1
    rw [cy2_0, cy2_1, cy2_2, sg_mul, sg_swap 0 2 (by decide), sg_swap 1 2 (by decide)] at h
    rw [h, r4]; ring
  have p6 : Q3 A 0 2 1 1 2 0 = -Q3 A 0 0 1 1 2 2 := by
    have h := Q3_perm A (Equiv.swap (0 : Fin 3) 2) 0 2 1 1 2 0
    rw [sw02_0, sw02_1, sw02_2, sg_swap 0 2 (by decide)] at h
    rw [h, r5]; ring
  rw [p2, p3, p4, p5, p6] at hc
  linear_combination hc

/-- **The trace cube is the determinant**: `E tr(UA)³ = det A` (step 4).

DERIVED: `3` is the rank and the power. -/
theorem haar_su3_trace_cube (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) ^ 3 ∂(probHaar (SU 3)) = A.det := by
  have hpt : ∀ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) ^ 3
      = ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3, ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a0 a0
        * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a1 a1 * ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) a2 a2 := by
    intro U
    rw [Matrix.trace_fin_three]
    simp only [Fin.sum_univ_three]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), int_sum3n]
  · show ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3, Q3 A a0 a0 a1 a1 a2 a2 = A.det
    have hdiag : ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3, Q3 A a0 a0 a1 a1 a2 a2
        = ∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3,
          (if a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2 then Q3 A 0 0 1 1 2 2 else 0) :=
      Finset.sum_congr rfl (fun a0 _ => Finset.sum_congr rfl (fun a1 _ =>
        Finset.sum_congr rfl (fun a2 _ => Q3_diag A a0 a1 a2)))
    rw [hdiag, ← Q3_det A]
    generalize Q3 A 0 0 1 1 2 2 = Q
    simp [Fin.sum_univ_three]
    ring
  · intro a0 a1 a2
    exact cont3 A a0 a0 a1 a1 a2 a2

#print axioms haar_su3_trace_cube

/-- **The mixed third moment**: `E tr(UA)² tr(UB) = tr(adj A · B)/3` (polarisation of
`haar_su3_trace_cube`: `det(A + tB) = det A + t tr(adj A · B) + O(t²)`).

DERIVED: `3` is the rank and the `3` of the polarisation `D(A, A, B) = tr(adj A · B)/3`; `2` is the
power of `tr(UA)`. -/
theorem haar_su3_trace_sq_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) ^ 2
        * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * B) ∂(probHaar (SU 3))
      = Matrix.trace (A.adjugate * B) / 3 := by
  have hpt : ∀ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * A) ^ 2
      * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * B)
      = (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * (A + B)) ^ 3
        - Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * (A - B)) ^ 3
        - 2 * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * B) ^ 3) / 6 := by
    intro U
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  have cX : Continuous (fun U : SU 3 => Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * (A + B)) ^ 3) :=
    (trc (A + B)).pow 3
  have cY : Continuous (fun U : SU 3 => Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * (A - B)) ^ 3) :=
    (trc (A - B)).pow 3
  have cZ : Continuous (fun U : SU 3 => 2 * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * B) ^ 3) :=
    continuous_const.mul ((trc B).pow 3)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_sub (intC (cX.sub cY)) (intC cZ), integral_sub (intC cX) (intC cY),
    integral_const_mul, haar_su3_trace_cube, haar_su3_trace_cube, haar_su3_trace_cube]
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace_fin_three]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

#print axioms haar_su3_trace_sq_mul

/-! ## 8. The adjugate -/

/-- `2‖adj A‖²_F = ‖A‖⁴_F − Σ_{pq}|(A†A)_{pq}|²` (Cauchy–Binet on the `2 × 2` minors).

DERIVED: `2` is the double count of `Σ_{p<q}`; `2` as exponent is the square; `3` is the rank. -/
private theorem adj_identity (A : Matrix (Fin 3) (Fin 3) ℂ) :
    2 * (∑ i, ∑ j, Complex.normSq (A.adjugate i j))
      = (∑ i, ∑ j, Complex.normSq (A i j)) ^ 2
        - ∑ p : Fin 3, ∑ q : Fin 3, Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k q) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_sum,
    Complex.ofReal_ofNat, ← Complex.mul_conj]
  rw [Matrix.adjugate_fin_three]
  simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub,
    map_mul, map_neg, map_sum, Complex.conj_conj]
  ring

/-- **The adjugate bound**: `‖adj A‖²_F ≤ ‖A‖⁴_F/3` (step 5).

DERIVED: `3` is the rank and the `1/3` of `Σᵢ Bᵢᵢ² ≥ (Σᵢ Bᵢᵢ)²/3`; `2` is the square. -/
theorem adjugate_frob_le (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ i, ∑ j, Complex.normSq (A.adjugate i j) ≤ (∑ i, ∑ j, Complex.normSq (A i j)) ^ 2 / 3 := by
  have hid := adj_identity A
  have hdiag : ∀ p : Fin 3, Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k p)
      = (∑ k : Fin 3, Complex.normSq (A k p)) ^ 2 := by
    intro p
    have h1 : (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k p)
        = ((∑ k : Fin 3, Complex.normSq (A k p) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_comm, Complex.mul_conj]
    rw [h1, Complex.normSq_ofReal, sq]
  have hdrop : ∑ p : Fin 3, Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k p)
      ≤ ∑ p : Fin 3, ∑ q : Fin 3, Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k q) :=
    Finset.sum_le_sum (fun p _ => Finset.single_le_sum
      (f := fun q => Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k q))
      (fun q _ => Complex.normSq_nonneg _) (Finset.mem_univ p))
  have hswap : ∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (A i j)
      = ∑ p : Fin 3, ∑ k : Fin 3, Complex.normSq (A k p) := Finset.sum_comm
  have hcs : ∀ d : Fin 3 → ℝ, (∑ p, d p) ^ 2 / 3 ≤ ∑ p, d p ^ 2 := by
    intro d
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    nlinarith [sq_nonneg (d 0 - d 1), sq_nonneg (d 1 - d 2), sq_nonneg (d 0 - d 2)]
  have hcs' : (∑ p : Fin 3, ∑ k : Fin 3, Complex.normSq (A k p)) ^ 2 / 3
      ≤ ∑ p : Fin 3, (∑ k : Fin 3, Complex.normSq (A k p)) ^ 2 :=
    hcs (fun p => ∑ k : Fin 3, Complex.normSq (A k p))
  have hB : (∑ i : Fin 3, ∑ j : Fin 3, Complex.normSq (A i j)) ^ 2 / 3
      ≤ ∑ p : Fin 3, ∑ q : Fin 3, Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k q) := by
    rw [hswap]
    calc (∑ p : Fin 3, ∑ k : Fin 3, Complex.normSq (A k p)) ^ 2 / 3
        ≤ ∑ p : Fin 3, (∑ k : Fin 3, Complex.normSq (A k p)) ^ 2 := hcs'
      _ = ∑ p : Fin 3, Complex.normSq (∑ k : Fin 3, (starRingEnd ℂ) (A k p) * A k p) :=
          (Finset.sum_congr rfl (fun p _ => hdiag p)).symm
      _ ≤ _ := hdrop
  linarith

#print axioms adjugate_frob_le

/-! ## 9. The feature -/

/-- The real part commutes with the Haar integral.

DERIVED: `3` is the rank. -/
private theorem int_re {f : SU 3 → ℂ} (hf : Integrable f (probHaar (SU 3))) :
    ∫ U, (f U).re ∂(probHaar (SU 3)) = (∫ U, f U ∂(probHaar (SU 3))).re := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
  simpa only [Complex.reCLM_apply] using h

/-- `√3`, the normalisation of the feature.

DERIVED: `3` is the rank. -/
private def s3 : ℝ := Real.sqrt ((3 : ℕ) : ℝ)

/-- DERIVED: `3` is the rank; `2` the square. -/
private theorem s3_sq : s3 ^ 2 = 3 := by
  unfold s3
  rw [Real.sq_sqrt (Nat.cast_nonneg 3)]
  norm_num

/-- DERIVED: `0` is the bound. -/
private theorem s3_pos : 0 < s3 := by
  unfold s3
  exact Real.sqrt_pos.mpr (by norm_num)

/-- `⟪w, X U⟫ = Re tr(U featDual w)/√3` (`PairInterface.inner_realFeature` at `N = 3`).

DERIVED: `3` is the rank. -/
private theorem feat_eq (w : FE 3) (U : SU 3) :
    inner ℝ w (realFeature 3 U)
      = (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re / s3 :=
  inner_realFeature 3 w U

/-- `tr((ωI · U) F) = ω tr(UF)`.

DERIVED: `3` is the rank. -/
private theorem tr_Zg (U : SU 3) (F : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (((Zg * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) * F)
      = om * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F) := by
  have h : ((Zg * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) = om • (U : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    rw [MassGap.ContactValue.coe_Zg_mul, Matrix.smul_apply, smul_eq_mul]
  rw [h, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- `E tr(UF) = 0` (`ω¹`).

DERIVED: `1` is the power of `ω`; `0` the value; `3` is the rank. -/
private theorem tr1_zero (F : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F) ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 1 (by decide) (fun U => ?_)
  simp only [tr_Zg]
  ring

/-- `E tr(UF)² = 0` (`ω²`).

DERIVED: `2` is the power; `0` the value; `3` is the rank. -/
private theorem tr2_zero (F : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F) ^ 2 ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 2 (by decide) (fun U => ?_)
  simp only [tr_Zg]
  ring

/-- `E tr(UF)⁴ = 0` (`ω⁴ = ω`).

DERIVED: `4` is the power; `0` the value; `3` is the rank. -/
private theorem tr4_zero (F : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F) ^ 4 ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 4 (by decide) (fun U => ?_)
  simp only [tr_Zg]
  ring

/-- `E tr(UF)³ conj tr(UF) = 0` (`ω³ ω² = ω⁵`).

DERIVED: `3` is the power; `5 = 3 + 2`; `0` the value. -/
private theorem tr31_zero (F : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F) ^ 3
      * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F)) ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 5 (by decide) (fun U => ?_)
  simp only [tr_Zg, map_mul, MassGap.ContactValue.om_conj]
  ring

/-- `E tr(UF)² conj tr(UG) = 0` (`ω² ω² = ω⁴`).

DERIVED: `2` is the power; `4 = 2 + 2`; `0` the value; `3` is the rank. -/
private theorem tr21c_zero (F G : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F) ^ 2
      * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * G)) ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 4 (by decide) (fun U => ?_)
  simp only [tr_Zg, map_mul, MassGap.ContactValue.om_conj]
  ring

/-- `E tr(UF) conj tr(UF) tr(UG) = 0` (`ω ω² ω = ω⁴`).

DERIVED: `4 = 1 + 2 + 1`; `0` the value; `3` is the rank. -/
private theorem tr11c1_zero (F G : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F)
      * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F))
      * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * G) ∂(probHaar (SU 3)) = 0 := by
  refine integral_omega_kill _ 4 (by decide) (fun U => ?_)
  simp only [tr_Zg, map_mul, MassGap.ContactValue.om_conj]
  ring

/-- `|tr(UF)|²` as a fourfold sum of second-moment monomials.

DERIVED: `3` is the rank. -/
private theorem normSq_expand (F : Matrix (Fin 3) (Fin 3) ℂ) (U : SU 3) :
    ((Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F)) : ℝ) : ℂ)
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, (F j i * star (F l k))
          * ((U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l)) := by
  rw [← Complex.mul_conj, starRingEnd_apply, trace_star_expand, trace_expand, mul_sum22]
  exact sum4_congr (fun i j k l => by ring)

/-- A Kronecker indicator of weight `1/3` collapses a double sum.

DERIVED: `1/3` is the second-moment value; `3` the rank; `0` is the indicator's value off the
diagonal pair. -/
private theorem collapse2 (X : Fin 3 → Fin 3 → ℂ) (i j : Fin 3) :
    ∑ k, ∑ l, X k l * (if i = k ∧ j = l then (1 / 3 : ℂ) else 0) = X i j / 3 := by
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · rw [if_pos ⟨rfl, rfl⟩]
      ring
    · intro x hx
      rw [if_neg (fun (h : i = i ∧ j = x) => hx h.2.symm), mul_zero]
  · intro x hx
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_neg (fun (h : i = x ∧ j = y) => hx h.1.symm), mul_zero]

/-- `E|tr(UF)|² = ‖F‖²_F/3`.

DERIVED: `1/3` is `E|Uᵢⱼ|²`; `3` the rank. -/
private theorem normSq_int (F : Matrix (Fin 3) (Fin 3) ℂ) :
    ∫ U : SU 3, Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * F)) ∂(probHaar (SU 3))
      = (∑ i, ∑ j, Complex.normSq (F i j)) / 3 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, integral_congr_ae (Filter.Eventually.of_forall (normSq_expand F)),
    int_sum4]
  · have step : ∀ i j k l : Fin 3, ∫ U : SU 3, (F j i * star (F l k))
          * ((U : Matrix (Fin 3) (Fin 3) ℂ) i j * star ((U : Matrix (Fin 3) (Fin 3) ℂ) k l))
          ∂(probHaar (SU 3))
        = (F j i * star (F l k)) * (if i = k ∧ j = l then (1 / 3 : ℂ) else 0) := by
      intro i j k l
      rw [integral_const_mul, haar_su3_second]
    have hcol : ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          (F j i * star (F l k)) * (if i = k ∧ j = l then (1 / 3 : ℂ) else 0)
        = ∑ i : Fin 3, ∑ j : Fin 3, F j i * star (F j i) / 3 :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        collapse2 (fun k l => F j i * star (F l k)) i j))
    rw [sum4_congr step, hcol]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_one,
      Complex.ofReal_sum]
    simp only [← Complex.mul_conj, starRingEnd_apply]
    simp only [Fin.sum_univ_three]
    ring
  · intro i j k l
    exact continuous_const.mul ((ec i j).mul (ecs k l))

/-- `(Re z)⁴ = (3/8)|z|⁴ + (1/8) Re z⁴ + (1/2) Re(z³ z̄)`.

DERIVED: the coefficients of `x⁴ = ((z + z̄)/2)⁴` after pairing conjugate terms: the binomial
coefficients `1, 4, 6, 4, 1` over `2⁴ = 16` give `3/8 = 6/16` on `|z|⁴`, `1/8 = 2/16` on `Re z⁴` and
`1/2 = 8/16` on `Re(z³ z̄)`; `4` is the power; `2` in `normSq z ^ 2` is the square giving `|z|⁴`;
`3` is the power of `z` in `z³ z̄`. -/
private theorem re4_id (z : ℂ) :
    z.re ^ 4 = 3 / 8 * Complex.normSq z ^ 2 + 1 / 8 * (z ^ 4).re
      + 1 / 2 * (z ^ 3 * (starRingEnd ℂ) z).re := by
  rw [show z ^ 4 = z * z * z * z by ring, show z ^ 3 = z * z * z by ring]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `(Re a/s)² (Re b/s) = (Re(a²b) + Re(a² b̄) + 2 Re(a ā b))/(4 s³)`.

DERIVED: `4 = 2²` from `Re a = (a + ā)/2`; `3` the power of `s`; `2` the multiplicity of `aāb`
and the exponent of `a`; `1/(4 s³)` is the common factor; `0` in `s ≠ 0` keeps the division by
`s` defined. -/
private theorem re3_id (a b : ℂ) (s : ℝ) (hs : s ≠ 0) :
    (a.re / s) ^ 2 * (b.re / s)
      = 1 / (4 * s ^ 3) * ((a ^ 2 * b).re + (a ^ 2 * (starRingEnd ℂ) b).re
        + 2 * (a * (starRingEnd ℂ) a * b).re) := by
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- `|tr(GH)|² ≤ ‖G‖²_F ‖H‖²_F`.

DERIVED: `2` is the square; `3` is the rank. -/
private theorem trace_cs (G H : Matrix (Fin 3) (Fin 3) ℂ) :
    ‖Matrix.trace (G * H)‖ ^ 2
      ≤ (∑ i, ∑ j, Complex.normSq (G i j)) * (∑ i, ∑ j, Complex.normSq (H i j)) := by
  have h1 : Matrix.trace (G * H) = ∑ p : Fin 3 × Fin 3, G p.1 p.2 * H p.2 p.1 := by
    rw [Fintype.sum_prod_type, Matrix.trace_fin_three]
    simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have h2 : ‖∑ p : Fin 3 × Fin 3, G p.1 p.2 * H p.2 p.1‖
      ≤ ∑ p : Fin 3 × Fin 3, ‖G p.1 p.2‖ * ‖H p.2 p.1‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun p _ => norm_mul _ _)
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : Fin 3 × Fin 3 => ‖G p.1 p.2‖) (fun p : Fin 3 × Fin 3 => ‖H p.2 p.1‖)
  have hG : ∑ p : Fin 3 × Fin 3, ‖G p.1 p.2‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (G i j) := by
    rw [Fintype.sum_prod_type]
    simp only [Complex.sq_norm]
  have hH : ∑ p : Fin 3 × Fin 3, ‖H p.2 p.1‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (H i j) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Complex.sq_norm]
  rw [h1]
  calc ‖∑ p : Fin 3 × Fin 3, G p.1 p.2 * H p.2 p.1‖ ^ 2
      ≤ (∑ p : Fin 3 × Fin 3, ‖G p.1 p.2‖ * ‖H p.2 p.1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ (∑ p : Fin 3 × Fin 3, ‖G p.1 p.2‖ ^ 2) * (∑ p : Fin 3 × Fin 3, ‖H p.2 p.1‖ ^ 2) := h3
    _ = (∑ i, ∑ j, Complex.normSq (G i j)) * (∑ i, ∑ j, Complex.normSq (H i j)) := by
        rw [hG, hH]

/-- The feature has mean `0` (`integral_omega_kill`, `k = 1`).

DERIVED: `3` is the rank; `0` is the mean. -/
theorem feature_mean_su3 (w : FE 3) :
    ∫ U : SU 3, inner ℝ w (realFeature 3 U) ∂(probHaar (SU 3)) = 0 := by
  have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM (intC (trc (featDual 3 w)))
  simp only [Complex.reCLM_apply] at hre
  rw [integral_congr_ae (Filter.Eventually.of_forall (feat_eq w)), integral_div, hre,
    tr1_zero, Complex.zero_re, zero_div]

#print axioms feature_mean_su3

/-- **Second moments**: `E⟪w, X⟫² ≤ ‖w‖²/18` (equality holds).

DERIVED: `3` is the rank; `2` is the moment order; `18 = 2 · 3²`: `E(Re Uᵢⱼ)²/3 = (1/2)(1/3)/3`. -/
theorem feature_second_su3 (w : FE 3) :
    ∫ U : SU 3, inner ℝ w (realFeature 3 U) ^ 2 ∂(probHaar (SU 3)) ≤ ‖w‖ ^ 2 / 18 := by
  apply le_of_eq
  have hpt : ∀ U : SU 3, inner ℝ w (realFeature 3 U) ^ 2
      = 1 / 6 * (Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))
        + (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 2).re) := by
    intro U
    rw [feat_eq, div_pow, s3_sq]
    simp only [sq, Complex.mul_re, Complex.normSq_apply]
    ring
  have c1 : Continuous (fun U : SU 3 =>
      Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))) :=
    Complex.continuous_normSq.comp (trc _)
  have c2 : Continuous (fun U : SU 3 =>
      (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 2).re) :=
    Complex.continuous_re.comp ((trc _).pow 2)
  have h2 : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 2).re
      ∂(probHaar (SU 3)) = 0 := by
    have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM
      (intC ((trc (featDual 3 w)).pow 2))
    simp only [Complex.reCLM_apply] at hre
    rw [hre, tr2_zero, Complex.zero_re]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add (intR c1) (intR c2), h2, normSq_int, frob_featDual]
  ring

#print axioms feature_second_su3

/-- **Fourth moments**: `E⟪w, X⟫⁴ ≤ ‖w‖⁴/96` (step 6).

DERIVED: `3` is the rank; `4` is the moment order; `1/96 = (3/8)(1/3²)(1/4)`, `= 3/(4N²(N² − 1))`
at `N = 3`. -/
theorem feature_fourth_su3 (w : FE 3) :
    ∫ U : SU 3, inner ℝ w (realFeature 3 U) ^ 4 ∂(probHaar (SU 3)) ≤ 1 / 96 * ‖w‖ ^ 4 := by
  have hpt : ∀ U : SU 3, inner ℝ w (realFeature 3 U) ^ 4
      = 1 / 9 * (3 / 8 * Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)) ^ 2
        + 1 / 8 * (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 4).re
        + 1 / 2 * (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 3
          * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))).re) := by
    intro U
    rw [feat_eq, div_pow, show s3 ^ 4 = (s3 ^ 2) ^ 2 by ring, s3_sq, re4_id]
    ring
  have ca : Continuous (fun U : SU 3 =>
      3 / 8 * Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)) ^ 2) :=
    continuous_const.mul ((Complex.continuous_normSq.comp (trc _)).pow 2)
  have cb : Continuous (fun U : SU 3 =>
      1 / 8 * (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 4).re) :=
    continuous_const.mul (Complex.continuous_re.comp ((trc _).pow 4))
  have cc : Continuous (fun U : SU 3 =>
      1 / 2 * (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 3
        * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))).re) :=
    continuous_const.mul (Complex.continuous_re.comp (((trc _).pow 3).mul (ccs _)))
  have h4 : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 4).re
      ∂(probHaar (SU 3)) = 0 := by
    have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM
      (intC ((trc (featDual 3 w)).pow 4))
    simp only [Complex.reCLM_apply] at hre
    rw [hre, tr4_zero, Complex.zero_re]
  have h31 : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 3
      * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))).re
      ∂(probHaar (SU 3)) = 0 := by
    rw [int_re, tr31_zero, Complex.zero_re]
    exact intC (((trc (featDual 3 w)).pow 3).mul (ccs (featDual 3 w)))
  have hint : ∫ U : SU 3, inner ℝ w (realFeature 3 U) ^ 4 ∂(probHaar (SU 3))
      = 1 / 24 * ∫ U : SU 3,
          Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)) ^ 2
          ∂(probHaar (SU 3)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul, h4, h31]
    all_goals first
      | exact intR ca | exact intR cb | exact intR cc | exact intR (ca.add cb) | ring1
  rw [hint]
  have hq := haar_su3_trace_fourth_le (featDual 3 w)
  rw [frob_featDual] at hq
  calc 1 / 24 * ∫ U : SU 3,
        Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)) ^ 2
        ∂(probHaar (SU 3))
      ≤ 1 / 24 * ((‖w‖ ^ 2) ^ 2 / 4) := mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = 1 / 96 * ‖w‖ ^ 4 := by ring

#print axioms feature_fourth_su3

/-- **Mixed third moments**: `|E⟪u, X⟫²⟪w, X⟫| ≤ ‖u‖²‖w‖/108` (step 6).

DERIVED: `3` is the rank; `2` is the square; `1/108 = (1/(3√3))(1/4)(1/3)(1/√3)`. -/
theorem feature_third_su3 (u w : FE 3) :
    |∫ U : SU 3, inner ℝ u (realFeature 3 U) ^ 2 * inner ℝ w (realFeature 3 U) ∂(probHaar (SU 3))|
      ≤ 1 / 108 * ‖u‖ ^ 2 * ‖w‖ := by
  have hs0 : s3 ≠ 0 := s3_pos.ne'
  have hpt : ∀ U : SU 3, inner ℝ u (realFeature 3 U) ^ 2 * inner ℝ w (realFeature 3 U)
      = 1 / (4 * s3 ^ 3)
        * ((Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u) ^ 2
              * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re
          + (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u) ^ 2
              * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))).re
          + 2 * (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u)
              * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u))
              * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re) := by
    intro U
    rw [feat_eq, feat_eq]
    exact re3_id _ _ _ hs0
  have cP : Continuous (fun U : SU 3 =>
      (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u) ^ 2
        * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re) :=
    Complex.continuous_re.comp (((trc _).pow 2).mul (trc _))
  have cQ : Continuous (fun U : SU 3 =>
      (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u) ^ 2
        * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))).re) :=
    Complex.continuous_re.comp (((trc _).pow 2).mul (ccs _))
  have cR : Continuous (fun U : SU 3 =>
      2 * (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u)
        * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u))
        * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re) :=
    continuous_const.mul (Complex.continuous_re.comp (((trc _).mul (ccs _)).mul (trc _)))
  have hP : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u) ^ 2
        * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re ∂(probHaar (SU 3))
      = (Matrix.trace ((featDual 3 u).adjugate * featDual 3 w) / 3).re := by
    rw [int_re, haar_su3_trace_sq_mul]
    exact intC (((trc (featDual 3 u)).pow 2).mul (trc (featDual 3 w)))
  have hQ : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u) ^ 2
        * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))).re
        ∂(probHaar (SU 3)) = 0 := by
    rw [int_re, tr21c_zero, Complex.zero_re]
    exact intC (((trc (featDual 3 u)).pow 2).mul (ccs (featDual 3 w)))
  have hR : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u)
        * (starRingEnd ℂ) (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 u))
        * Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w)).re ∂(probHaar (SU 3)) = 0 := by
    rw [int_re, tr11c1_zero, Complex.zero_re]
    exact intC (((trc (featDual 3 u)).mul (ccs (featDual 3 u))).mul (trc (featDual 3 w)))
  have hV : ∫ U : SU 3, inner ℝ u (realFeature 3 U) ^ 2 * inner ℝ w (realFeature 3 U)
        ∂(probHaar (SU 3))
      = 1 / (4 * s3 ^ 3) * (Matrix.trace ((featDual 3 u).adjugate * featDual 3 w) / 3).re := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_add, integral_add, integral_const_mul, hP, hQ, hR]
    all_goals first
      | exact intR cP | exact intR cQ | exact intR cR | exact intR (cP.add cQ) | ring1
  have ht : ‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ * s3 ≤ ‖u‖ ^ 2 * ‖w‖ := by
    have hcs := trace_cs (featDual 3 u).adjugate (featDual 3 w)
    have hadj := adjugate_frob_le (featDual 3 u)
    rw [frob_featDual] at hadj
    rw [frob_featDual] at hcs
    have h2 : (‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ * s3) ^ 2
        ≤ (‖u‖ ^ 2 * ‖w‖) ^ 2 := by
      calc (‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ * s3) ^ 2
          = 3 * ‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ ^ 2 := by
            rw [mul_pow, s3_sq]; ring
        _ ≤ 3 * ((∑ i, ∑ j, Complex.normSq ((featDual 3 u).adjugate i j)) * ‖w‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (by norm_num)
        _ ≤ 3 * ((‖u‖ ^ 2) ^ 2 / 3 * ‖w‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hadj (sq_nonneg _)) (by norm_num)
        _ = (‖u‖ ^ 2 * ‖w‖) ^ 2 := by ring
    have h3 := abs_le_of_sq_le_sq h2 (mul_nonneg (sq_nonneg _) (norm_nonneg _))
    rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) s3_pos.le)] at h3
  have hinv : 1 / (4 * s3 ^ 3) = s3 / 36 := by
    have h1 : (4 * s3 ^ 3 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hs0)
    rw [div_eq_div_iff h1 (by norm_num)]
    have e : s3 * (4 * s3 ^ 3) = 4 * (s3 ^ 2) ^ 2 := by ring
    rw [e, s3_sq]
    norm_num
  have hre : |(Matrix.trace ((featDual 3 u).adjugate * featDual 3 w) / 3).re|
      ≤ ‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ / 3 := by
    calc |(Matrix.trace ((featDual 3 u).adjugate * featDual 3 w) / 3).re|
        ≤ ‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w) / 3‖ := Complex.abs_re_le_norm _
      _ = ‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ / 3 := by
          rw [norm_div, Complex.norm_ofNat]
  have h5 : s3 * |(Matrix.trace ((featDual 3 u).adjugate * featDual 3 w) / 3).re|
      ≤ s3 * (‖Matrix.trace ((featDual 3 u).adjugate * featDual 3 w)‖ / 3) :=
    mul_le_mul_of_nonneg_left hre s3_pos.le
  rw [hV, hinv, abs_mul, abs_of_pos (div_pos s3_pos (by norm_num))]
  linarith

#print axioms feature_third_su3

/-- **The Haar constants of the `SU(3)` feature**: `D = 18`, `q4 = 1/96`, `t3 = 1/108`.

DERIVED: `18`, `1/96`, `1/108` are `feature_second_su3`'s, `feature_fourth_su3`'s and
`feature_third_su3`'s constants; `3` is the rank. -/
def haarConsts_su3 : HaarConsts (probHaar (SU 3)) (realFeature 3) where
  D := 18
  q4 := 1 / 96
  t3 := 1 / 108
  D_pos := by norm_num
  q4_nonneg := by norm_num
  t3_nonneg := by norm_num
  mean := feature_mean_su3
  second := feature_second_su3
  fourth := feature_fourth_su3
  third := feature_third_su3

#print axioms haarConsts_su3

end MassGap.HaarMomentsSU3
