import Mathlib
import MassGap.Schwinger

/-!
# MassGap.MomentMeasure — the bounded moment sequence as a MEASURE on the lag variable

## What the object is, and what it is not

`Schwinger.exists_infinite_volume_bounded_moment_data` produces `L : ℕ → ℝ` — one real number per
natural-number lag — together with both Hankel conditions of a compactly supported moment sequence.
That is a SEQUENCE OF NUMBERS. This file turns it into a MEASURE: a `MeasureTheory.Measure ℝ` whose
`k`-th moment is `L k` and which gives no mass to the complement of `[−R, R]`.

The variable of that measure is the LAG. It is a measure on `ℝ`, one real dimension, and `ℝ` here is
the spectral variable conjugate to a lattice separation along direction `2`. It is NOT a measure on
`ℝ⁴`, NOT a measure on a space of distributions, and NOT an Osterwalder–Schrader measure. A Schwinger
function needs a limit indexed by `Fin 4 → ℤ`; `corrClay`'s lag runs along one direction only, and
that gap is untouched here.

## The route

The classical bounded Hamburger construction, with every step taken from Mathlib:

1. `lam` — the linear functional `Λ_s : ℂ[X] →ₗ[ℂ] ℂ` sending `X^k ↦ L (k + s)`.
2. `sform` — the sesquilinear form `⟨p, q⟩ = Λ_s(p⋆ q)`, with `p⋆` the coefficientwise conjugate.
3. `re_sform_self_nonneg` — positive semidefiniteness of `⟨·,·⟩ = ⟨·,·⟩_0`. This is
   `Schwinger.limit_hankel_psd` applied twice, to the real and to the imaginary parts of the
   coefficient family; the cross terms cancel because `L (i+j)` is symmetric under `i ↔ j`.
4. `Pre D` — `ℂ[X]` carrying that form as a SEMI-inner product, so no quotient by the null space is
   needed: `PreInnerProductSpace.Core` asks only for semidefiniteness, and `UniformSpace.Completion`
   Hausdorffifies and completes in one step.
5. `opX` — multiplication by `X`, extended to the completion. Its norm is at most `R`, and that is
   exactly `Schwinger.shiftForm_one_le`: the shifted Hankel bound says multiplication by `X` is a
   bounded operator, which bare positive semidefiniteness never gives.
6. `isSelfAdjoint_opX`, `spectrum_opX_subset` — self-adjointness is immediate from the definition of
   the form, and `spectrum.subset_closedBall_norm_mul` puts the real spectrum inside `[−R, R]`.
7. The continuous functional calculus and Riesz–Markov–Kakutani turn the vector state
   `f ↦ ⟨1, f(A) 1⟩` into the measure.

The Hilbert space is COMPLEX rather than real because Mathlib's continuous functional calculus for
self-adjoint elements is an instance on complex C⋆-algebras (`CStarAlgebra` is complex by
definition, `Mathlib/Analysis/CStarAlgebra/Classes.lean`), and `E →L[ℂ] E` is one exactly when `E` is
a complex Hilbert space.
-/

namespace MassGap.MomentMeasure

open Polynomial Finset
open scoped ComplexConjugate CompactlySupported

noncomputable section

/-! ## Part 1 — the data

Everything below is a function of one bundled record. Its fields are exactly the conclusions of
`Schwinger.exists_infinite_volume_bounded_moment_data`: the sequence, the rate, full Hankel
positivity at every finite family of lags, and the shifted Hankel bound at that rate. Nothing else
about `L` is used — not the contact floor, not summability, not the geometric bound itself (the
geometric bound enters only through `shift`, which `Schwinger.shift_two_le` derives from it). -/

/-- **The hypothesis of the bounded Hamburger moment problem**, as a record.

`psd` is `Schwinger.limit_hankel_psd`; `shift` is `Schwinger.shift_two_le`. The record is in `Type 1`
because `psd` quantifies over the index type. -/
structure MomentData where
  /-- The moment sequence: one real number per lag. -/
  L : ℕ → ℝ
  /-- The rate. The measure this file builds lives on `[−R, R]`. -/
  R : ℝ
  /-- The rate is positive. -/
  R_pos : 0 < R
  /-- **Full Hankel positivity**, at every finite family of lags and coefficients. -/
  psd : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i')
  /-- **The shifted Hankel bound** — multiplication by `X` is bounded by `R`. -/
  shift : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      ∑ i, ∑ i', c i * c i' * L (a i + a i' + 2)
        ≤ R ^ 2 * ∑ i, ∑ i', c i * c i' * L (a i + a i')

variable (D : MomentData)

/-! ## Part 2 — the functional and the form -/

/-- The coefficient sequence of a polynomial, as a finitely supported function. `Polynomial.toFinsupp`
lands in `AddMonoidAlgebra`, which is the same type read with the convolution product; this names the
additive reading, which is the one a linear functional needs. -/
def coeffs (p : ℂ[X]) : ℕ →₀ ℂ := p.toFinsupp

theorem coeffs_add (p q : ℂ[X]) : coeffs (p + q) = coeffs p + coeffs q :=
  Polynomial.toFinsupp_add p q

theorem coeffs_smul (c : ℂ) (p : ℂ[X]) : coeffs (c • p) = c • coeffs p :=
  Polynomial.toFinsupp_smul c p

theorem coeffs_monomial (i : ℕ) (a : ℂ) : coeffs (monomial i a) = Finsupp.single i a :=
  Polynomial.toFinsupp_monomial i a

/-- **The moment functional at shift `s`**: the `ℂ`-linear map sending `X^k` to `L (k + s)`.

DERIVED: nothing numeric; `s` is a formal shift of the index, used to express the `X²`-shifted form
without a second definition. -/
def lam (s : ℕ) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun p := Finsupp.linearCombination ℂ (fun k : ℕ => ((D.L (k + s) : ℝ) : ℂ)) (coeffs p)
  map_add' p q := by rw [coeffs_add]; exact map_add _ _ _
  map_smul' c p := by rw [coeffs_smul, map_smul]; rfl

@[simp] theorem lam_monomial (s i : ℕ) (a : ℂ) :
    lam D s (monomial i a) = a * ((D.L (i + s) : ℝ) : ℂ) := by
  simp [lam, coeffs_monomial, Finsupp.linearCombination_single, smul_eq_mul]

/-- The coefficientwise conjugate of a complex polynomial. -/
def pstar (p : ℂ[X]) : ℂ[X] := p.map (starRingEnd ℂ)

@[simp] theorem pstar_coeff (p : ℂ[X]) (n : ℕ) : (pstar p).coeff n = conj (p.coeff n) := by
  simp [pstar, Polynomial.coeff_map]

@[simp] theorem pstar_add (p q : ℂ[X]) : pstar (p + q) = pstar p + pstar q := by
  ext n; simp

@[simp] theorem pstar_mul (p q : ℂ[X]) : pstar (p * q) = pstar p * pstar q := by
  simp [pstar, Polynomial.map_mul]

@[simp] theorem pstar_pstar (p : ℂ[X]) : pstar (pstar p) = p := by
  ext n; simp

@[simp] theorem pstar_X : pstar (X : ℂ[X]) = X := by simp [pstar]

@[simp] theorem pstar_one : pstar (1 : ℂ[X]) = 1 := by simp [pstar]

@[simp] theorem pstar_smul (c : ℂ) (p : ℂ[X]) : pstar (c • p) = conj c • pstar p := by
  ext n; simp [Polynomial.coeff_smul, smul_eq_mul]

@[simp] theorem pstar_monomial (i : ℕ) (a : ℂ) :
    pstar (monomial i a) = monomial i (conj a) := by
  ext n
  simp [Polynomial.coeff_monomial, apply_ite (starRingEnd ℂ)]

/-- **The form.** `⟨p, q⟩_s = Λ_s(p⋆ q)`, conjugate-linear in the first slot. -/
def sform (s : ℕ) (p q : ℂ[X]) : ℂ := lam D s (pstar p * q)

@[simp] theorem sform_zero_right (s : ℕ) (p : ℂ[X]) : sform D s p 0 = 0 := by simp [sform]

@[simp] theorem sform_zero_left (s : ℕ) (q : ℂ[X]) : sform D s 0 q = 0 := by simp [sform, pstar]

theorem sform_add_right (s : ℕ) (p q r : ℂ[X]) :
    sform D s p (q + r) = sform D s p q + sform D s p r := by
  simp [sform, mul_add]

theorem sform_add_left (s : ℕ) (p q r : ℂ[X]) :
    sform D s (p + q) r = sform D s p r + sform D s q r := by
  simp [sform, add_mul]

theorem sform_smul_right (s : ℕ) (c : ℂ) (p q : ℂ[X]) :
    sform D s p (c • q) = c * sform D s p q := by
  simp [sform, smul_eq_mul]

theorem sform_smul_left (s : ℕ) (c : ℂ) (p q : ℂ[X]) :
    sform D s (c • p) q = conj c * sform D s p q := by
  simp [sform]

@[simp] theorem sform_monomial (s i j : ℕ) (a b : ℂ) :
    sform D s (monomial i a) (monomial j b) = conj a * b * ((D.L (i + j + s) : ℝ) : ℂ) := by
  rw [sform, pstar_monomial, monomial_mul_monomial, lam_monomial]

/-- The functional commutes with conjugation because `L` is real-valued. -/
theorem lam_conj (s : ℕ) (p : ℂ[X]) : conj (lam D s p) = lam D s (pstar p) := by
  refine Polynomial.induction_on' p (fun q r hq hr => ?_) (fun n a => ?_)
  · simp [hq, hr]
  · simp [Complex.conj_ofReal]

/-- **The form is Hermitian.** -/
theorem sform_conj_symm (s : ℕ) (p q : ℂ[X]) : conj (sform D s q p) = sform D s p q := by
  rw [sform, lam_conj, pstar_mul, pstar_pstar, mul_comm, sform]

/-- The shift is multiplication by `X^m`, on the nose. -/
theorem lam_shift (s m : ℕ) (p : ℂ[X]) : lam D s ((X : ℂ[X]) ^ m * p) = lam D (m + s) p := by
  refine Polynomial.induction_on' p (fun q r hq hr => ?_) (fun n a => ?_)
  · simp [mul_add, hq, hr]
  · have hX : (X : ℂ[X]) ^ m = monomial m 1 := Polynomial.X_pow_eq_monomial m
    have hidx : m + n + s = n + (m + s) := by omega
    rw [hX, monomial_mul_monomial, lam_monomial, lam_monomial, one_mul, hidx]

/-- **Multiplication by `X` is symmetric for the form** — immediate from the definition, since
`(Xp)⋆ q = p⋆ (Xq)` as polynomials. -/
theorem sform_mulX (s : ℕ) (p q : ℂ[X]) :
    sform D s ((X : ℂ[X]) * p) q = sform D s p ((X : ℂ[X]) * q) := by
  unfold sform
  congr 1
  rw [pstar_mul, pstar_X]
  ring

/-- **The `X`-shifted form is the form at shift `2`.** This is where the `2` of the shifted Hankel
bound comes from: multiplying both slots by `X` moves the index by `1` on each side.

DERIVED: the `2` is the Hankel index's own arithmetic, as in `Schwinger.shiftForm`. -/
theorem sform_mulX_self (p : ℂ[X]) :
    sform D 0 ((X : ℂ[X]) * p) ((X : ℂ[X]) * p) = sform D 2 p p := by
  have h : pstar ((X : ℂ[X]) * p) * ((X : ℂ[X]) * p)
      = (X : ℂ[X]) ^ 2 * (pstar p * p) := by
    rw [pstar_mul, pstar_X]; ring
  rw [sform, h, lam_shift, sform]

/-! ## Part 3 — positive semidefiniteness, from `limit_hankel_psd` -/

/-- A double sum over `Fin N` is a double sum over `range N`. -/
theorem sum_fin_eq_sum_range (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, g i j = ∑ i ∈ range N, ∑ j ∈ range N, g i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, g i j) N]
  exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (fun j => g i j) N

/-- Hankel positivity, read on a range of lags. -/
theorem double_sum_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range N, ∑ j ∈ range N, c i * c j * D.L (i + j) := by
  rw [← sum_fin_eq_sum_range N (fun i j => c i * c j * D.L (i + j))]
  exact D.psd (Fin N) (fun i => (i : ℕ)) (fun i => c (i : ℕ))

/-- The shifted Hankel bound, read on a range of lags. -/
theorem double_sum_shift_le (N : ℕ) (c : ℕ → ℝ) :
    ∑ i ∈ range N, ∑ j ∈ range N, c i * c j * D.L (i + j + 2)
      ≤ D.R ^ 2 * ∑ i ∈ range N, ∑ j ∈ range N, c i * c j * D.L (i + j) := by
  rw [← sum_fin_eq_sum_range N (fun i j => c i * c j * D.L (i + j + 2)),
    ← sum_fin_eq_sum_range N (fun i j => c i * c j * D.L (i + j))]
  exact D.shift (Fin N) (fun i => (i : ℕ)) (fun i => c (i : ℕ))

/-- The form on the diagonal, expanded over the coefficients. -/
theorem sform_eq_double_sum (s N : ℕ) (p : ℂ[X]) (hN : p.natDegree < N) :
    sform D s p p
      = ∑ i ∈ range N, ∑ j ∈ range N,
          conj (p.coeff i) * p.coeff j * ((D.L (i + j + s) : ℝ) : ℂ) := by
  have hsum_right : ∀ (q : ℂ[X]) (t : Finset ℕ) (f : ℕ → ℂ[X]),
      sform D s q (∑ i ∈ t, f i) = ∑ i ∈ t, sform D s q (f i) := by
    intro q t f
    classical
    refine Finset.induction_on t (by simp) (fun i t hi ih => ?_)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, sform_add_right, ih]
  have hsum_left : ∀ (q : ℂ[X]) (t : Finset ℕ) (f : ℕ → ℂ[X]),
      sform D s (∑ i ∈ t, f i) q = ∑ i ∈ t, sform D s (f i) q := by
    intro q t f
    classical
    refine Finset.induction_on t (by simp) (fun i t hi ih => ?_)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, sform_add_left, ih]
  conv_lhs => rw [Polynomial.as_sum_range' p N hN]
  rw [hsum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hsum_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sform_monomial]

/-- **The real part of the diagonal form splits into two real Hankel forms.** The cross terms cancel
because `L (i+j)` does not see the order of `i` and `j`; what is left is the real-part family and
the imaginary-part family, each a real coefficient family of the kind `limit_hankel_psd` accepts. -/
theorem re_sform_self (s N : ℕ) (p : ℂ[X]) (hN : p.natDegree < N) :
    (sform D s p p).re
      = (∑ i ∈ range N, ∑ j ∈ range N, (p.coeff i).re * (p.coeff j).re * D.L (i + j + s))
        + ∑ i ∈ range N, ∑ j ∈ range N, (p.coeff i).im * (p.coeff j).im * D.L (i + j + s) := by
  have hterm : ∀ (z w : ℂ) (r : ℝ),
      (conj z * w * ((r : ℝ) : ℂ)).re = z.re * w.re * r + z.im * w.im * r := by
    intro z w r
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [sform_eq_double_sum D s N p hN, Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => hterm _ _ _)

/-- **THE FORM IS POSITIVE SEMIDEFINITE.** -/
theorem re_sform_self_nonneg (p : ℂ[X]) : 0 ≤ (sform D 0 p p).re := by
  rw [re_sform_self D 0 (p.natDegree + 1) p (lt_add_one _)]
  have h1 := double_sum_nonneg D (p.natDegree + 1) (fun i => (p.coeff i).re)
  have h2 := double_sum_nonneg D (p.natDegree + 1) (fun i => (p.coeff i).im)
  simp only [Nat.add_zero]
  linarith

/-- **THE SHIFTED FORM IS BOUNDED BY `R²` TIMES THE FORM.** This is the whole of the geometric decay,
transported to the pre-Hilbert space: it says multiplication by `X` has norm at most `R`. -/
theorem re_sform_two_le (p : ℂ[X]) :
    (sform D 2 p p).re ≤ D.R ^ 2 * (sform D 0 p p).re := by
  rw [re_sform_self D 2 (p.natDegree + 1) p (lt_add_one _),
    re_sform_self D 0 (p.natDegree + 1) p (lt_add_one _)]
  have h1 := double_sum_shift_le D (p.natDegree + 1) (fun i => (p.coeff i).re)
  have h2 := double_sum_shift_le D (p.natDegree + 1) (fun i => (p.coeff i).im)
  simp only [Nat.add_zero]
  linarith

/-! ## Part 4 — the pre-Hilbert space and its completion

No quotient is taken. `PreInnerProductSpace.Core` asks for semidefiniteness only, and the completion
of the resulting seminormed space is a genuine Hilbert space: `UniformSpace.Completion` collapses the
null vectors and completes in one step. -/

set_option linter.unusedVariables false in
/-- `ℂ[X]` carrying the moment form as a semi-inner product. The record is a parameter so that the
seminorm below is attached to a type that remembers which moment sequence produced it. -/
def Pre (D : MomentData) : Type := ℂ[X]

instance instAddCommGroupPre : AddCommGroup (Pre D) := inferInstanceAs (AddCommGroup ℂ[X])

instance instModulePre : Module ℂ (Pre D) := inferInstanceAs (Module ℂ ℂ[X])

/-- A polynomial, read as a vector of the pre-Hilbert space. -/
def ofPoly (D : MomentData) (p : ℂ[X]) : Pre D := p

/-- A vector of the pre-Hilbert space, read as a polynomial. -/
def toPoly (D : MomentData) (p : Pre D) : ℂ[X] := p

@[simp] theorem toPoly_ofPoly (p : ℂ[X]) : toPoly D (ofPoly D p) = p := rfl

@[simp] theorem ofPoly_toPoly (p : Pre D) : ofPoly D (toPoly D p) = p := rfl

@[simp] theorem toPoly_add (p q : Pre D) : toPoly D (p + q) = toPoly D p + toPoly D q := rfl

@[simp] theorem toPoly_smul (c : ℂ) (p : Pre D) : toPoly D (c • p) = c • toPoly D p := rfl

/-- **The semi-inner product.** Hermitian by `sform_conj_symm`, semidefinite by
`re_sform_self_nonneg`, sesquilinear by construction. Definiteness is NOT claimed and is not needed:
the completion quotients the null vectors out. -/
@[reducible] def core (D : MomentData) : PreInnerProductSpace.Core ℂ (Pre D) where
  inner p q := sform D 0 (toPoly D p) (toPoly D q)
  conj_inner_symm p q := sform_conj_symm D 0 (toPoly D p) (toPoly D q)
  re_inner_nonneg p := by
    simpa using re_sform_self_nonneg D (toPoly D p)
  add_left p q r := sform_add_left D 0 (toPoly D p) (toPoly D q) (toPoly D r)
  smul_left p q c := sform_smul_left D 0 c (toPoly D p) (toPoly D q)

instance instSeminormedPre : SeminormedAddCommGroup (Pre D) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (Pre D) _ _ _ (core D)

instance instInnerProductSpacePre : InnerProductSpace ℂ (Pre D) :=
  InnerProductSpace.ofCore (core D)

@[simp] theorem inner_ofPoly (p q : ℂ[X]) :
    inner ℂ (ofPoly D p) (ofPoly D q) = sform D 0 p q := rfl

theorem norm_ofPoly (p : ℂ[X]) : ‖ofPoly D p‖ = Real.sqrt ((sform D 0 p p).re) := by
  have h : ‖ofPoly D p‖ ^ 2 = RCLike.re (inner ℂ (ofPoly D p) (ofPoly D p)) :=
    InnerProductSpace.norm_sq_eq_re_inner _
  rw [inner_ofPoly] at h
  rw [show ((sform D 0 p p).re) = ‖ofPoly D p‖ ^ 2 by rw [h]; simp,
    Real.sqrt_sq (norm_nonneg _)]

/-- Multiplication by `X` on the pre-Hilbert space. -/
def mulXₗ (D : MomentData) : Pre D →ₗ[ℂ] Pre D where
  toFun p := ofPoly D ((X : ℂ[X]) * toPoly D p)
  map_add' p q := by
    show ofPoly D ((X : ℂ[X]) * (toPoly D p + toPoly D q)) = _
    rw [mul_add]; rfl
  map_smul' c p := by
    show ofPoly D ((X : ℂ[X]) * (c • toPoly D p)) = _
    rw [mul_smul_comm]; rfl

@[simp] theorem mulXₗ_ofPoly (p : ℂ[X]) :
    mulXₗ D (ofPoly D p) = ofPoly D ((X : ℂ[X]) * p) := rfl

/-- **Multiplication by `X` is bounded by `R`.** This is `re_sform_two_le`, i.e. the shifted Hankel
bound, and nothing else. -/
theorem norm_mulXₗ_le (p : Pre D) : ‖mulXₗ D p‖ ≤ D.R * ‖p‖ := by
  set q : ℂ[X] := toPoly D p with hq
  have hp : p = ofPoly D q := rfl
  have h1 : ‖mulXₗ D p‖ = Real.sqrt ((sform D 2 q q).re) := by
    rw [hp, mulXₗ_ofPoly, norm_ofPoly, sform_mulX_self]
  have h2 : ‖p‖ = Real.sqrt ((sform D 0 q q).re) := by rw [hp, norm_ofPoly]
  rw [h1, h2]
  have h3 : (sform D 2 q q).re ≤ D.R ^ 2 * (sform D 0 q q).re := re_sform_two_le D q
  calc Real.sqrt ((sform D 2 q q).re)
      ≤ Real.sqrt (D.R ^ 2 * (sform D 0 q q).re) := Real.sqrt_le_sqrt h3
    _ = D.R * Real.sqrt ((sform D 0 q q).re) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq D.R_pos.le]

/-- Multiplication by `X`, bundled as a continuous linear map of norm at most `R`. -/
def mulXL (D : MomentData) : Pre D →L[ℂ] Pre D :=
  LinearMap.mkContinuous (mulXₗ D) D.R (norm_mulXₗ_le D)

@[simp] theorem mulXL_ofPoly (p : ℂ[X]) :
    mulXL D (ofPoly D p) = ofPoly D ((X : ℂ[X]) * p) := rfl

/-- **The Hilbert space**: the completion of the moment pre-Hilbert space. -/
abbrev H (D : MomentData) : Type := UniformSpace.Completion (Pre D)

/-- **Multiplication by `X` as a bounded operator on the Hilbert space.** -/
def opX (D : MomentData) : H D →L[ℂ] H D := (mulXL D).completion

@[simp] theorem opX_coe (p : Pre D) : opX D (p : H D) = ((mulXL D p : Pre D) : H D) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- **The operator norm is at most `R`.** -/
theorem norm_opX_le : ‖opX D‖ ≤ D.R := by
  refine ContinuousLinearMap.opNorm_le_bound _ D.R_pos.le (fun x => ?_)
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_le (continuous_norm.comp (opX D).continuous)
        (continuous_const.mul continuous_norm)
  | ih p =>
      simpa [mulXL, UniformSpace.Completion.norm_coe] using norm_mulXₗ_le D p

/-- **The operator is self-adjoint.** Immediate from `sform_mulX`: the form cannot tell whether `X`
was applied on the left or on the right. -/
theorem isSelfAdjoint_opX : IsSelfAdjoint (opX D) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact Continuous.inner ((opX D).continuous.comp continuous_fst) continuous_snd
      · exact Continuous.inner continuous_fst ((opX D).continuous.comp continuous_snd)
  | ih p q =>
      simp only [ContinuousLinearMap.coe_coe, opX_coe, UniformSpace.Completion.inner_coe]
      exact sform_mulX D 0 (toPoly D p) (toPoly D q)

/-- **The real spectrum lies in `[−R, R]`.** -/
theorem spectrum_opX_subset : spectrum ℝ (opX D) ⊆ Set.Icc (-D.R) D.R := by
  intro k hk
  have h1 : |k| ≤ ‖opX D‖ * ‖(1 : H D →L[ℂ] H D)‖ := by
    have hmem : k ∈ Metric.closedBall (0 : ℝ) (‖opX D‖ * ‖(1 : H D →L[ℂ] H D)‖) :=
      spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) (opX D) hk
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
    exact hmem
  have h2 : ‖(1 : H D →L[ℂ] H D)‖ ≤ 1 := by
    simpa [ContinuousLinearMap.one_def] using
      ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H D)
  have h4 : |k| ≤ D.R := by
    calc |k| ≤ ‖opX D‖ * ‖(1 : H D →L[ℂ] H D)‖ := h1
      _ ≤ D.R * 1 :=
          mul_le_mul (norm_opX_le D) h2 (norm_nonneg (1 : H D →L[ℂ] H D)) D.R_pos.le
      _ = D.R := mul_one _
  exact Set.mem_Icc.mpr ⟨(abs_le.mp h4).1, (abs_le.mp h4).2⟩

/-! ## Part 5 — the vacuum vector and the vector state

`cfcHom` is Mathlib's continuous functional calculus for a self-adjoint element: a star-algebra
homomorphism `C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H)` sending the restricted identity to `A`.
Composing it with the vector state at the vacuum gives a POSITIVE linear functional on the
continuous functions on the spectrum, and positivity is the only thing that needs proving: a
nonnegative `f` is `g·g` for `g = √f`, whose image is self-adjoint, so the value is `‖g(A)1‖²`. -/

/-- **The vacuum**: the constant polynomial `1`, as a vector of the Hilbert space. -/
def vac (D : MomentData) : H D := ((ofPoly D 1 : Pre D) : H D)

/-- **`A^k` applied to the vacuum is the class of `X^k`.** -/
theorem opX_pow_vac (k : ℕ) :
    (opX D ^ k) (vac D) = ((ofPoly D ((X : ℂ[X]) ^ k) : Pre D) : H D) := by
  induction k with
  | zero => simp [vac]
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, opX_coe, mulXL_ofPoly, pow_succ']

/-- **The moments of the vacuum state ARE the moment sequence.** -/
theorem inner_vac_opX_pow (k : ℕ) :
    inner ℂ (vac D) ((opX D ^ k) (vac D)) = ((D.L k : ℝ) : ℂ) := by
  rw [opX_pow_vac, vac, UniformSpace.Completion.inner_coe, inner_ofPoly, sform, pstar_one, one_mul,
    Polynomial.X_pow_eq_monomial k, lam_monomial, one_mul, Nat.add_zero]

/-- **The vector state** `f ↦ ⟨1, f(A) 1⟩`, as a real linear functional on the continuous functions
on the spectrum. -/
def state (D : MomentData) : C(spectrum ℝ (opX D), ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ (vac D) (cfcHom (isSelfAdjoint_opX D) f (vac D))).re
  map_add' f g := by
    simp [map_add, inner_add_right, Complex.add_re]
  map_smul' r f := by
    have h1 : cfcHom (isSelfAdjoint_opX D) (r • f)
        = r • cfcHom (isSelfAdjoint_opX D) f := map_smul _ _ _
    simp only [h1, ContinuousLinearMap.smul_apply', RingHom.id_apply, smul_eq_mul]
    rw [← IsScalarTower.algebraMap_smul ℂ r, inner_smul_right]
    simp [Complex.mul_re]

@[simp] theorem state_apply (f : C(spectrum ℝ (opX D), ℝ)) :
    state D f = (inner ℂ (vac D) (cfcHom (isSelfAdjoint_opX D) f (vac D))).re := rfl

/-- **THE STATE IS POSITIVE.** A nonnegative continuous function on the spectrum is `g·g` with
`g = √f` continuous, and the functional calculus sends `g` to a self-adjoint operator, so the value
is a squared norm. -/
theorem state_nonneg (f : C(spectrum ℝ (opX D), ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ state D f := by
  set ha := isSelfAdjoint_opX D with hha
  set g : C(spectrum ℝ (opX D), ℝ) :=
    ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩ with hg
  have hgf : g * g = f := by
    ext x
    exact Real.mul_self_sqrt (hf x)
  have hsa : IsSelfAdjoint (cfcHom ha g) := cfcHom_predicate ha g
  have hsym := hsa.isSymmetric
  have hval : inner ℂ (vac D) (cfcHom ha f (vac D))
      = inner ℂ (cfcHom ha g (vac D)) (cfcHom ha g (vac D)) := by
    rw [← hgf, map_mul, mul_apply_eq_comp]
    simpa using (hsym (vac D) (cfcHom ha g (vac D))).symm
  rw [state_apply, hval]
  have hnorm : ‖cfcHom ha g (vac D)‖ ^ 2
      = RCLike.re (inner ℂ (cfcHom ha g (vac D)) (cfcHom ha g (vac D))) :=
    InnerProductSpace.norm_sq_eq_re_inner _
  have h2 : (inner ℂ (cfcHom ha g (vac D)) (cfcHom ha g (vac D))).re
      = ‖cfcHom ha g (vac D)‖ ^ 2 := by simpa using hnorm.symm
  rw [h2]
  positivity

/-- **The positive linear functional** on the compactly supported continuous functions on the
spectrum — the input Riesz–Markov–Kakutani asks for. Every continuous function on the spectrum is
compactly supported, because the spectrum is compact. -/
def stateCc (D : MomentData) : C_c(spectrum ℝ (opX D), ℝ) →ₚ[ℝ] ℝ where
  toFun f := state D f.toContinuousMap
  map_add' f g := by
    show state D (f + g).toContinuousMap = state D f.toContinuousMap + state D g.toContinuousMap
    rw [← map_add]
    rfl
  map_smul' r f := by
    show state D (r • f).toContinuousMap = (RingHom.id ℝ) r • state D f.toContinuousMap
    rw [RingHom.id_apply, ← map_smul]
    rfl
  monotone' := by
    intro f g hfg
    have hsub : 0 ≤ state D (g.toContinuousMap - f.toContinuousMap) := by
      refine state_nonneg D _ (fun x => ?_)
      have := CompactlySupportedContinuousMap.le_def.mp hfg x
      simpa using this
    rw [map_sub] at hsub
    show state D f.toContinuousMap ≤ state D g.toContinuousMap
    linarith

/-! ## Part 6 — the measure -/

/-- The Riesz–Markov–Kakutani measure of the vacuum state, on the spectrum. -/
def spectralMeasure (D : MomentData) : MeasureTheory.Measure (spectrum ℝ (opX D)) :=
  RealRMK.rieszMeasure (stateCc D)

/-- **THE REPRESENTING MEASURE**, on `ℝ`: the spectral measure of the vacuum state, pushed forward
along the inclusion of the spectrum.

The variable is the LAG's spectral parameter — one real dimension. This is not a measure on `ℝ⁴`. -/
def rieszMeasure (D : MomentData) : MeasureTheory.Measure ℝ :=
  (spectralMeasure D).map Subtype.val

/-- **THE MEASURE LIVES ON `[−R, R]`.** -/
theorem rieszMeasure_compl_Icc : rieszMeasure D ((Set.Icc (-D.R) D.R)ᶜ) = 0 := by
  have hmeas : MeasurableSet ((Set.Icc (-D.R) D.R)ᶜ) := measurableSet_Icc.compl
  rw [rieszMeasure, MeasureTheory.Measure.map_apply measurable_subtype_coe hmeas]
  have hempty : (Subtype.val ⁻¹' (Set.Icc (-D.R) D.R)ᶜ : Set (spectrum ℝ (opX D))) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hx (spectrum_opX_subset D x.2))
  rw [hempty, MeasureTheory.measure_empty]

set_option maxHeartbeats 1000000 in
/-- **THE MOMENTS OF THE MEASURE ARE THE MOMENT SEQUENCE.**

`∫ x^k dμ = ⟨1, A^k 1⟩ = Λ(X^k) = L k`: Riesz–Markov–Kakutani for the middle equality, the functional
calculus for the first, and the definition of the form for the last. -/
theorem integral_pow_rieszMeasure (k : ℕ) :
    ∫ x, x ^ k ∂(rieszMeasure D) = D.L k := by
  have hae : AEMeasurable (Subtype.val : spectrum ℝ (opX D) → ℝ) (spectralMeasure D) :=
    measurable_subtype_coe.aemeasurable
  have hsm : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ k)
      ((spectralMeasure D).map Subtype.val) := (continuous_pow k).aestronglyMeasurable
  set F : C_c(spectrum ℝ (opX D), ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv
      (((ContinuousMap.id ℝ).restrict (spectrum ℝ (opX D))) ^ k) with hF
  have hFval : ∀ x : spectrum ℝ (opX D), F x = (x : ℝ) ^ k := by
    intro x; simp [hF]
  have hfin : stateCc D F = D.L k := by
    show state D (((ContinuousMap.id ℝ).restrict (spectrum ℝ (opX D))) ^ k) = D.L k
    rw [state_apply, map_pow, cfcHom_id, inner_vac_opX_pow]
    simp
  rw [rieszMeasure, MeasureTheory.integral_map hae hsm, spectralMeasure]
  calc ∫ x : spectrum ℝ (opX D), ((x : ℝ)) ^ k ∂(RealRMK.rieszMeasure (stateCc D))
      = ∫ x : spectrum ℝ (opX D), F x ∂(RealRMK.rieszMeasure (stateCc D)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => (hFval x).symm)
    _ = stateCc D F := RealRMK.integral_rieszMeasure (stateCc D) F
    _ = D.L k := hfin

/-- **THE BOUNDED HAMBURGER CONCLUSION**, as one statement: a sequence carrying both Hankel
conditions IS the moment sequence of a positive measure supported in `[−R, R]`. -/
theorem exists_representing_measure (D : MomentData) :
    ∃ μ : MeasureTheory.Measure ℝ,
      (∀ k : ℕ, ∫ x, x ^ k ∂μ = D.L k) ∧ μ ((Set.Icc (-D.R) D.R)ᶜ) = 0 :=
  ⟨rieszMeasure D, integral_pow_rieszMeasure D, rieszMeasure_compl_Icc D⟩

/-- **THE MEASURE IS NOT THE ZERO MEASURE** when the contact term is positive: its total mass is
`L 0`. This is the `k = 0` case of `integral_pow_rieszMeasure`, recorded because it is what makes the
construction non-vacuous at every coupling `Schwinger`'s contact floor covers. -/
theorem rieszMeasure_ne_zero (h : 0 < D.L 0) : rieszMeasure D ≠ 0 := by
  intro hzero
  have h0 := integral_pow_rieszMeasure D 0
  rw [hzero, MeasureTheory.integral_zero_measure] at h0
  linarith

/-! ## Part 7 — the infinite-volume two-point function, as a measure

`Schwinger.exists_infinite_volume_bounded_moment_data` supplies exactly the two fields of
`MomentData` at every rate the geometric clustering allows. Feeding it in turns `L` from a sequence
of numbers into the moments of a measure.

What this is NOT: the measure's variable is the spectral parameter of ONE lag direction. It is not a
measure on `ℝ⁴`, not a measure on a space of distributions, and not an Osterwalder–Schrader
measure. -/

/-- **THE INFINITE-VOLUME TWO-POINT FUNCTION IS THE MOMENT SEQUENCE OF A MEASURE ON `[−R, R]`.**

On the derived coupling interval `[0,b)`, at every rate `R` the clustering allows, the limit `L` of
the Clay correlation along the even-extent apertures is `∫ x^k dμ` for a positive measure `μ` on `ℝ`
that gives no mass outside `[−R, R]`. The contact floor is carried through unchanged, so `μ` is not
the zero measure at any `β` in the interval.

DERIVED: `2·φ j + 1`, `128` and `16·4` are `Schwinger`'s; nothing here is chosen. -/
theorem exists_infinite_volume_representing_measure :
    ∃ b : ℝ, 0 < b ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ β : ℝ, 0 ≤ β → β < b →
        ∀ R : ℝ, MassGap.StrongCoupling.coreRate (16 * 4) β ≤ R → 0 < R → R < 1 →
          ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ) (μ : MeasureTheory.Measure ℝ),
            StrictMono φ ∧
            (∀ k : ℕ, Filter.Tendsto
              (fun j => MassGap.InfiniteVolume.corrLag k β (2 * φ j + 1))
              Filter.atTop (nhds (L k))) ∧
            Real.exp (-(128 * β)) * δ₀ ≤ L 0 ∧
            (∀ k : ℕ, ∫ x, x ^ k ∂μ = L k) ∧
            μ ((Set.Icc (-R) R)ᶜ) = 0 := by
  obtain ⟨b, hb, δ₀, hδ₀, hmain⟩ :=
    MassGap.Schwinger.exists_infinite_volume_bounded_moment_data
  refine ⟨b, hb, δ₀, hδ₀, fun β hβ0 hβb R hrateR hR0 hR1 => ?_⟩
  obtain ⟨-, L, φ, hφ, htend, hfloor, hpsd, hrest⟩ := hmain β hβ0 hβb
  obtain ⟨-, hshift, -⟩ := hrest R hrateR hR0 hR1
  refine ⟨L, φ, rieszMeasure ⟨L, R, hR0, hpsd, hshift⟩, hφ, htend, hfloor,
    integral_pow_rieszMeasure ⟨L, R, hR0, hpsd, hshift⟩,
    rieszMeasure_compl_Icc ⟨L, R, hR0, hpsd, hshift⟩⟩

end

/-! ## Axiom footprints

Every declaration of this file, printed. The expected footprint is foundational-only —
`propext`, `Classical.choice`, `Quot.sound` — for all of them; `exists_infinite_volume_representing_measure`
inherits whatever `Schwinger.exists_infinite_volume_bounded_moment_data` carries. -/

#print axioms MomentData
#print axioms coeffs
#print axioms coeffs_add
#print axioms coeffs_smul
#print axioms coeffs_monomial
#print axioms lam
#print axioms lam_monomial
#print axioms pstar
#print axioms pstar_coeff
#print axioms pstar_add
#print axioms pstar_mul
#print axioms pstar_pstar
#print axioms pstar_X
#print axioms pstar_one
#print axioms pstar_smul
#print axioms pstar_monomial
#print axioms sform
#print axioms sform_zero_right
#print axioms sform_zero_left
#print axioms sform_add_right
#print axioms sform_add_left
#print axioms sform_smul_right
#print axioms sform_smul_left
#print axioms sform_monomial
#print axioms lam_conj
#print axioms sform_conj_symm
#print axioms lam_shift
#print axioms sform_mulX
#print axioms sform_mulX_self
#print axioms sum_fin_eq_sum_range
#print axioms double_sum_nonneg
#print axioms double_sum_shift_le
#print axioms sform_eq_double_sum
#print axioms re_sform_self
#print axioms re_sform_self_nonneg
#print axioms re_sform_two_le
#print axioms Pre
#print axioms instAddCommGroupPre
#print axioms instModulePre
#print axioms ofPoly
#print axioms toPoly
#print axioms toPoly_ofPoly
#print axioms ofPoly_toPoly
#print axioms toPoly_add
#print axioms toPoly_smul
#print axioms core
#print axioms instSeminormedPre
#print axioms instInnerProductSpacePre
#print axioms inner_ofPoly
#print axioms norm_ofPoly
#print axioms mulXₗ
#print axioms mulXₗ_ofPoly
#print axioms norm_mulXₗ_le
#print axioms mulXL
#print axioms mulXL_ofPoly
#print axioms H
#print axioms opX
#print axioms opX_coe
#print axioms norm_opX_le
#print axioms isSelfAdjoint_opX
#print axioms spectrum_opX_subset
#print axioms vac
#print axioms opX_pow_vac
#print axioms inner_vac_opX_pow
#print axioms state
#print axioms state_apply
#print axioms state_nonneg
#print axioms stateCc
#print axioms spectralMeasure
#print axioms rieszMeasure
#print axioms rieszMeasure_compl_Icc
#print axioms integral_pow_rieszMeasure
#print axioms rieszMeasure_ne_zero
#print axioms exists_representing_measure
#print axioms exists_infinite_volume_representing_measure

end MassGap.MomentMeasure
