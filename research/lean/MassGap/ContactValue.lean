import Mathlib
import MassGap.ContactFloor

/-!
# MassGap.ContactValue — the zero-coupling contact value on `SU(3)`

`ContactFloor.corrClay_zero_at_zero_eq` reduces the zero-coupling, zero-lag connected plaquette
correlator, at every extent `n ≥ 2`, to `haarSecond − haarMean ^ 2`: two Haar integrals of the
Wilson density `φ(g) = 1 − (1/3)·Re tr g` on `SU(3)`. This file evaluates those two integrals.

## Method

Mathlib at this pin carries no Peter–Weyl theorem and no Schur orthogonality for compact groups, so
`∫ |χ|² = 1` is not available as a citation. `phase_zero` stands in for it: if left translation by a
single group element multiplies the integrand by a fixed scalar `lam ≠ 1`, the integral is zero.
Every moment below is that lemma applied at an explicit element of `SU(3)`, and the only property of
`probHaar` used is left (and once right) invariance.

Three elements are defined here, each with its membership proof:

* `Zg = ω·1`, with `ω` a primitive cube root of unity. It lies in `SU(3)` because
  `det(ω·1) = ω³ = 1`. Translation by it multiplies `χ` by `ω` and `χ²` by `ω²`, giving
  `haar_chi_zero` and `haar_chi_sq_zero`.
* `Dg = diag(1, ω, ω²)`. Translation by it attaches the phase `ω^(i−k)` to `g_ii · conj (g_kk)`,
  which is `1` only when `i = k`; `off_01` through `off_21` are the six vanishing off-diagonal
  moments.
* `Pg`, the three-cycle permutation matrix, which lies in `SU(3)` because a three-cycle is an even
  permutation. Translating on either side by it makes the nine entry moments `∫ |g_ij|²` equal, and
  one row of a unitary matrix then fixes each at `1/3` (`msq_row_zero_sum`, `msq_zero_zero`).

## What is proved

`haar_re_chi_zero` gives `∫ Re χ = 0`, `haar_chi_normsq` gives `∫ |χ|² = 1`, and `haar_re_chi_sq`
gives `∫ (Re χ)² = 1/2`. Those feed `haarMean_eq : haarMean = 1` and
`haarSecond_eq : haarSecond = 1 + 1/18`, and hence

    WilsonBridge.corrClay (m + 2) 0 0 = 1/18

at every `m` (`corrClay_zero_at_zero_value`), with `corrClay_four_zero_zero` the instance at
extent four.

## Where each numeral comes from

* `3` is the rank of the gauge group, carried in from `WilsonBridge.corrClay`, which is stated at
  `SU(3)`. Every `Fin 3`, the order of `ω`, and the `1/3` below are that one datum.
* `1/3` is `∫ |g_ij|²`: the nine are equal by `Pg`, and one row of a unitary matrix has three
  entries whose square moduli sum to `1`.
* `1` is `∫ |χ|² = 3 · (1/3)`, the three diagonal terms that survive `Dg`.
* `1/2` is `∫ (Re χ)² = (∫ Re(χ²) + ∫ |χ|²)/2 = (0 + 1)/2`, the dividing `2` belonging to the
  identity `(Re t)² = (Re(t²) + |t|²)/2`.
* `1/9` is `(1/3)²`, the square of the `1/N` normalising `WilsonAction.wilsonDensity`.
* `1/18` is `haarSecond − haarMean² = (1 + (1/9)·(1/2)) − 1²`.
* `4` is the extent at which the instance is stated; `4 = 2 + 2` reads
  `ContactFloor.corrClay_zero_at_zero_eq` at `m = 2`.
* The two `0`s in `corrClay 4 0 0` are the coupling `β = 0` and the lag `0 : Fin 4`. The second is
  what makes the correlator a variance rather than a separated two-point function.
* `2` as an exponent is the second moment, and the variance; `2` as the minimum extent in `m + 2`
  is `ContactFloor`'s own, the extent at which a plaquette's four links are distinct.

Foundational footprint only. Build: `python research/code/lean_build.py build MassGap.ContactValue`.
-/

namespace MassGap.ContactValue

open Matrix MeasureTheory
open MassGap.SUN MassGap.CompactGauge MassGap.WilsonAction

/-! ### A primitive cube root of unity

DERIVED: the order `3` is the rank of `SU(3)`. On a `3 × 3` matrix `det(ω·1) = ω^3`, so it is the
rank that selects which root of unity puts `ω·1` in the group. -/

/-- A primitive cube root of unity, `exp(2πi/3)`. `om_primitive`, `om_cube`, `om_ne_one` and
`om_sq_ne_one` are the facts about it used below; `om_conj` and `om_sq_conj` give its conjugate.

DERIVED: both numerals sit in the body rather than the signature. The `3` is the rank of `SU(3)`
and fixes the ORDER of the root, because `det(ω·1) = ω³` on a `3 × 3` matrix; the `2` is the `2π`
of one full turn, which that order divides. At rank `N` the expression reads `exp(2πi/N)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem om_primitive : IsPrimitiveRoot om 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem om_cube : om ^ 3 = 1 := om_primitive.pow_eq_one

theorem om_ne_one : om ≠ 1 := by
  have h := om_primitive.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num)
  simpa using h

theorem om_sq_ne_one : om ^ 2 ≠ 1 :=
  om_primitive.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)

theorem om_norm : ‖om‖ = 1 := Complex.norm_eq_one_of_pow_eq_one om_cube (by norm_num)

theorem om_inv : om⁻¹ = om ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [show om * om ^ 2 = om ^ 3 by ring, om_cube])

theorem om_conj : (starRingEnd ℂ) om = om ^ 2 := by
  rw [← Complex.inv_eq_conj om_norm, om_inv]

theorem om_sq_conj : (starRingEnd ℂ) (om ^ 2) = om := by
  rw [map_pow, om_conj, show (om ^ 2) ^ 2 = om ^ 3 * om by ring, om_cube, one_mul]

theorem om_mul_conj : om * (starRingEnd ℂ) om = 1 := by
  rw [om_conj, show om * om ^ 2 = om ^ 3 by ring, om_cube]

theorem om_sq_mul_conj : om ^ 2 * (starRingEnd ℂ) (om ^ 2) = 1 := by
  rw [om_sq_conj, show om ^ 2 * om = om ^ 3 by ring, om_cube]

/-! ### Three explicit elements of `SU(3)` -/

/-- The diagonal separator `diag(1, ω, ω²)`, given as its vector of entries.

DERIVED: the `3` of `Fin 3` is the rank, an index type. The entries are the successive powers
`ω⁰, ω¹, ω²`, one per row; their product is `ω^(0+1+2) = ω³ = 1`, which is what `dvec_mem` uses to
place the diagonal matrix in `SU(3)`. None of them is a magnitude. -/
noncomputable def dvec : Fin 3 → ℂ := ![1, om, om ^ 2]

/-- The central element `ω·1`, given as its vector of entries — `ω` in each diagonal place.

DERIVED: the `3` of `Fin 3` is the rank, an index type. `zvec_mem` places the matrix in `SU(3)`
because the product of the three entries is `ω³ = 1`. -/
noncomputable def zvec : Fin 3 → ℂ := ![om, om, om]

theorem dvec_zero : dvec 0 = 1 := by simp [dvec]
theorem dvec_one : dvec 1 = om := by simp [dvec]
theorem dvec_two : dvec 2 = om ^ 2 := by simp [dvec]

theorem zvec_apply (i : Fin 3) : zvec i = om := by fin_cases i <;> simp [zvec]

/-- A diagonal matrix over `Fin 3` whose entries each satisfy `v i * conj (v i) = 1` and whose
three entries multiply to `1` lies in `Matrix.specialUnitaryGroup (Fin 3) ℂ`. Used by `dvec_mem`
and `zvec_mem`.

DERIVED: `3` is the rank, an index type. The `1`s are the two conditions defining the special
unitary group: unit modulus of each entry, and unit determinant. The `0`, `1` and `2` in
`v 0 * v 1 * v 2` are the three diagonal positions, written out because `Fin.prod_univ_three`
expands the determinant that way. -/
theorem diag_mem (v : Fin 3 → ℂ) (hu : ∀ i, v i * (starRingEnd ℂ) (v i) = 1)
    (hd : v 0 * v 1 * v 2 = 1) :
    Matrix.diagonal v ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply]
    exact hu i
  · rw [Matrix.det_diagonal, Fin.prod_univ_three]
    exact hd

theorem dvec_mem : Matrix.diagonal dvec ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  have h0 : dvec 0 * (starRingEnd ℂ) (dvec 0) = 1 := by rw [dvec_zero, map_one, one_mul]
  have h1 : dvec 1 * (starRingEnd ℂ) (dvec 1) = 1 := by rw [dvec_one]; exact om_mul_conj
  have h2 : dvec 2 * (starRingEnd ℂ) (dvec 2) = 1 := by rw [dvec_two]; exact om_sq_mul_conj
  refine diag_mem dvec (fun i => ?_) ?_
  · fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rw [dvec_zero, dvec_one, dvec_two, one_mul,
      show om * om ^ 2 = om ^ 3 by ring, om_cube]

theorem zvec_mem : Matrix.diagonal zvec ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  refine diag_mem zvec (fun i => ?_) ?_
  · rw [zvec_apply]; exact om_mul_conj
  · rw [zvec_apply, zvec_apply, zvec_apply, show om * om * om = om ^ 3 by ring, om_cube]

/-- The three-cycle permutation matrix. `pmat_mem` places it in `SU(3)`: a three-cycle is an even
permutation, so the matrix is unitary with determinant `1`.

DERIVED: the `3` is the rank, an index type. The `0`s and `1`s of the literal matrix are a
permutation's incidence pattern — absent and present — and no entry is a magnitude. -/
noncomputable def pmat : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem pmat_mem : pmat ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [pmat, Matrix.det_fin_three]

/-- `diag(1, ω, ω²)` as an element of `SU 3`, pairing `dvec` with `dvec_mem`.

DERIVED: the `3` is the rank in the type `SU 3`. The entries are `dvec`'s and are derived there;
this declaration adds no numeral of its own. -/
noncomputable def Dg : SU 3 := ⟨Matrix.diagonal dvec, dvec_mem⟩

/-- `ω·1` as an element of `SU 3` — the central element — pairing `zvec` with `zvec_mem`.

DERIVED: the `3` is the rank in the type `SU 3`. The entries are `zvec`'s, derived there. -/
noncomputable def Zg : SU 3 := ⟨Matrix.diagonal zvec, zvec_mem⟩

/-- The three-cycle as an element of `SU 3`, pairing `pmat` with `pmat_mem`.

DERIVED: the `3` is the rank in the type `SU 3`; the entry pattern is `pmat`'s. -/
noncomputable def Pg : SU 3 := ⟨pmat, pmat_mem⟩

/-! ### How the three elements act -/

theorem coe_Dg_mul (g : SU 3) (i j : Fin 3) :
    ((Dg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
      = dvec i * (g : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  rw [Submonoid.coe_mul]
  show (Matrix.diagonal dvec * (g : Matrix (Fin 3) (Fin 3) ℂ)) i j = _
  simp [Matrix.diagonal_mul]

theorem coe_Zg_mul (g : SU 3) (i j : Fin 3) :
    ((Zg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
      = om * (g : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  rw [Submonoid.coe_mul]
  show (Matrix.diagonal zvec * (g : Matrix (Fin 3) (Fin 3) ℂ)) i j = _
  simp [Matrix.diagonal_mul, zvec_apply]

theorem coe_Pg_mul (g : SU 3) (i j : Fin 3) :
    ((Pg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
      = (pmat * (g : Matrix (Fin 3) (Fin 3) ℂ)) i j := by
  rw [Submonoid.coe_mul]; rfl

theorem coe_mul_Pg (g : SU 3) (i j : Fin 3) :
    ((g * Pg : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
      = ((g : Matrix (Fin 3) (Fin 3) ℂ) * pmat) i j := by
  rw [Submonoid.coe_mul]; rfl

theorem pmat_mul_row_one (M : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) :
    (pmat * M) 1 j = M 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]; simp [pmat]

theorem pmat_mul_row_two (M : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) :
    (pmat * M) 2 j = M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]; simp [pmat]

theorem mul_pmat_col_zero (M : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    (M * pmat) i 0 = M i 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]; simp [pmat]

theorem mul_pmat_col_one (M : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    (M * pmat) i 1 = M i 2 := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]; simp [pmat]

/-! ### The invariant-projection principle -/

/-- Invariant projection. If left translation by one group element `h` multiplies the integrand by
a fixed scalar `lam ≠ 1`, then `∫ f d(probHaar (SU 3)) = 0`. The proof uses left invariance of
`probHaar` and nothing else about it; every moment below is an instance.

DERIVED: `3` is the rank in `SU 3`. The `1` is the excluded value of `lam`: at `lam = 1` the
translation identity is vacuous and the conclusion does not follow. The `0` is the value of the
integral. -/
theorem phase_zero {f : SU 3 → ℂ} (h : SU 3) (lam : ℂ) (hlam : lam ≠ 1)
    (hpt : ∀ g : SU 3, f (h * g) = lam * f g) :
    ∫ g : SU 3, f g ∂(probHaar (SU 3)) = 0 := by
  haveI := isMulLeftInvariant_probHaar (SU 3)
  have step : (∫ g : SU 3, f g ∂(probHaar (SU 3)))
      = lam * ∫ g : SU 3, f g ∂(probHaar (SU 3)) := by
    calc (∫ g : SU 3, f g ∂(probHaar (SU 3)))
        = ∫ g : SU 3, f (h * g) ∂(probHaar (SU 3)) := (integral_mul_left_eq_self f h).symm
      _ = ∫ g : SU 3, lam * f g ∂(probHaar (SU 3)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = lam * ∫ g : SU 3, f g ∂(probHaar (SU 3)) := integral_const_mul _ _
  have hz : (1 - lam) * (∫ g : SU 3, f g ∂(probHaar (SU 3))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hlam))

/-! ### Continuity, bounds, integrability -/

theorem trace_eq_sum' (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.trace M = ∑ i, M i i := by
  rw [Matrix.trace]; rfl

theorem entry_cont (i j : Fin 3) :
    Continuous (fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem entry_norm_le (g : SU 3) (i j : Fin 3) :
    ‖(g : Matrix (Fin 3) (Fin 3) ℂ) i j‖ ≤ 1 :=
  unitary_entry_norm_le_one 3 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 i j

theorem integrableC {f : SU 3 → ℂ} (hc : Continuous f) (C : ℝ) (hb : ∀ g, ‖f g‖ ≤ C) :
    Integrable f (probHaar (SU 3)) := by
  haveI := isProbabilityMeasure_probHaar (SU 3)
  exact (integrable_const C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem integrableR {f : SU 3 → ℝ} (hc : Continuous f) (C : ℝ) (hb : ∀ g, ‖f g‖ ≤ C) :
    Integrable f (probHaar (SU 3)) := by
  haveI := isProbabilityMeasure_probHaar (SU 3)
  exact (integrable_const C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- The character of the defining representation: the trace of `g` read as a `3 × 3` complex
matrix. `chi_eq` writes it out as the sum of the three diagonal entries.

DERIVED: every `3` is the rank — the group in `SU 3` and its matrix index type `Fin 3`.
`Matrix.trace` sums the diagonal of whatever matrix it is given and carries no parameter of its
own. -/
noncomputable def chi (g : SU 3) : ℂ := Matrix.trace (g : Matrix (Fin 3) (Fin 3) ℂ)

theorem chi_eq (g : SU 3) :
    chi g = (g : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1
      + (g : Matrix (Fin 3) (Fin 3) ℂ) 2 2 := by
  rw [chi, trace_eq_sum', Fin.sum_univ_three]

theorem chi_cont : Continuous chi := by
  have h : chi = fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      + (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1 + (g : Matrix (Fin 3) (Fin 3) ℂ) 2 2 := by
    funext g; exact chi_eq g
  rw [h]
  exact ((entry_cont 0 0).add (entry_cont 1 1)).add (entry_cont 2 2)

/-- `‖chi g‖ ≤ 3` for every `g`.

DERIVED: `3` is the rank — the character is a sum of `3` diagonal entries, and `entry_norm_le`
bounds each of them by `1`. -/
theorem chi_norm_le (g : SU 3) : ‖chi g‖ ≤ 3 := by
  rw [chi_eq]
  calc ‖(g : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1
        + (g : Matrix (Fin 3) (Fin 3) ℂ) 2 2‖
      ≤ ‖(g : Matrix (Fin 3) (Fin 3) ℂ) 0 0 + (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1‖
        + ‖(g : Matrix (Fin 3) (Fin 3) ℂ) 2 2‖ := norm_add_le _ _
    _ ≤ (‖(g : Matrix (Fin 3) (Fin 3) ℂ) 0 0‖ + ‖(g : Matrix (Fin 3) (Fin 3) ℂ) 1 1‖)
        + ‖(g : Matrix (Fin 3) (Fin 3) ℂ) 2 2‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ (1 + 1) + 1 := by
          gcongr <;> exact entry_norm_le g _ _
    _ = 3 := by norm_num

theorem chi_integrable : Integrable chi (probHaar (SU 3)) :=
  integrableC chi_cont 3 (fun g => by simpa using chi_norm_le g)

theorem chi_sq_integrable : Integrable (fun g : SU 3 => chi g ^ 2) (probHaar (SU 3)) := by
  refine integrableC (chi_cont.pow 2) 9 (fun g => ?_)
  rw [norm_pow]
  nlinarith [chi_norm_le g, norm_nonneg (chi g)]

theorem chi_normsq_integrable :
    Integrable (fun g : SU 3 => chi g * (starRingEnd ℂ) (chi g)) (probHaar (SU 3)) := by
  refine integrableC (chi_cont.mul (Complex.continuous_conj.comp chi_cont)) 9 (fun g => ?_)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [chi_norm_le g, norm_nonneg (chi g)]

theorem re_chi_sq_term_integrable :
    Integrable (fun g : SU 3 => (chi g ^ 2).re) (probHaar (SU 3)) :=
  chi_sq_integrable.re

theorem re_chi_normsq_integrable :
    Integrable (fun g : SU 3 => (chi g * (starRingEnd ℂ) (chi g)).re) (probHaar (SU 3)) :=
  chi_normsq_integrable.re

theorem entry_prod_integrable (i j k l : Fin 3) :
    Integrable (fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) i j
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) k l)) (probHaar (SU 3)) := by
  refine integrableC ((entry_cont i j).mul (Complex.continuous_conj.comp (entry_cont k l)))
    1 (fun g => ?_)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [entry_norm_le g i j, entry_norm_le g k l,
    norm_nonneg ((g : Matrix (Fin 3) (Fin 3) ℂ) i j),
    norm_nonneg ((g : Matrix (Fin 3) (Fin 3) ℂ) k l)]

theorem re_chi_integrable : Integrable (fun g : SU 3 => (chi g).re) (probHaar (SU 3)) :=
  chi_integrable.re

theorem re_chi_sq_integrable : Integrable (fun g : SU 3 => ((chi g).re) ^ 2) (probHaar (SU 3)) := by
  refine integrableR ((Complex.continuous_re.comp chi_cont).pow 2) 9 (fun g => ?_)
  have h1 : |(chi g).re| ≤ ‖chi g‖ := Complex.abs_re_le_norm _
  have h2 := chi_norm_le g
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [abs_nonneg ((chi g).re)]

/-! ### The first moment: `∫ χ = 0` -/

/-- `∫ tr U d(probHaar (SU 3)) = 0`, by `phase_zero` at the central element `Zg = ω·1`: translation
by it multiplies the character by `ω`, and `om_ne_one` gives `ω ≠ 1`.

DERIVED: `3` is the rank in `SU 3`; `0` is the value of the integral. -/
theorem haar_chi_zero : ∫ g : SU 3, chi g ∂(probHaar (SU 3)) = 0 := by
  refine phase_zero Zg om om_ne_one (fun g => ?_)
  rw [chi_eq, chi_eq, coe_Zg_mul, coe_Zg_mul, coe_Zg_mul]
  ring

/-- `∫ Re tr U d(probHaar (SU 3)) = 0`. The real part is pulled through the integral by
`Complex.reCLM` and `chi_integrable`, and `haar_chi_zero` closes it.

DERIVED: `3` is the rank in `SU 3`; `0` is the value of the integral. -/
theorem haar_re_chi_zero : ∫ g : SU 3, (chi g).re ∂(probHaar (SU 3)) = 0 := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM chi_integrable
  simp only [Complex.reCLM_apply] at h
  rw [h, haar_chi_zero]
  simp

/-! ### The second character moment: `∫ χ² = 0` -/

/-- `∫ (tr U)² d(probHaar (SU 3)) = 0`, by `phase_zero` at `Zg`: translation by `ω·1` multiplies
`χ²` by `ω²`, and `om_sq_ne_one` gives `ω² ≠ 1` because `ω` has order `3`.

DERIVED: `3` is the rank in `SU 3` and the order of `ω`; the exponent `2` is the moment being
taken, and is also the power of `ω` the translation contributes; `0` is the value of the
integral. -/
theorem haar_chi_sq_zero : ∫ g : SU 3, chi g ^ 2 ∂(probHaar (SU 3)) = 0 := by
  refine phase_zero Zg (om ^ 2) om_sq_ne_one (fun g => ?_)
  have hc : chi (Zg * g) = om * chi g := by
    rw [chi_eq, chi_eq, coe_Zg_mul, coe_Zg_mul, coe_Zg_mul]; ring
  rw [hc]; ring

/-! ### The second moment `∫ |χ|² = 1` -/

/-- The nine entry second moments `∫ U_ij · conj (U_ij) d(probHaar (SU 3))`, as a function of the
two indices.

DERIVED: every `3` is the rank — `SU 3` and the matrix index type `Fin 3` — so `i` and `j` are
matrix INDICES rather than magnitudes, and there are `3 × 3` of these numbers. The `2` of a second
moment is written here as multiplication by the conjugate. -/
noncomputable def msq (i j : Fin 3) : ℂ :=
  ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) i j
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i j) ∂(probHaar (SU 3))

theorem msq_eq_left (i j i' j' : Fin 3)
    (hpt : ∀ g : SU 3, ((Pg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
        * (starRingEnd ℂ) (((Pg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j)
      = (g : Matrix (Fin 3) (Fin 3) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i' j')) :
    msq i' j' = msq i j := by
  haveI := isMulLeftInvariant_probHaar (SU 3)
  have key : (fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i' j'))
      = (fun g : SU 3 => ((Pg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
        * (starRingEnd ℂ) (((Pg * g : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j)) := by
    funext g; exact (hpt g).symm
  rw [msq, msq, key]
  exact integral_mul_left_eq_self (fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) i j
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i j)) Pg

theorem msq_eq_right (i j i' j' : Fin 3)
    (hpt : ∀ g : SU 3, ((g * Pg : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
        * (starRingEnd ℂ) (((g * Pg : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j)
      = (g : Matrix (Fin 3) (Fin 3) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i' j')) :
    msq i' j' = msq i j := by
  haveI := isMulRightInvariant_probHaar (SU 3)
  have key : (fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i' j'))
      = (fun g : SU 3 => ((g * Pg : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j
        * (starRingEnd ℂ) (((g * Pg : SU 3) : Matrix (Fin 3) (Fin 3) ℂ) i j)) := by
    funext g; exact (hpt g).symm
  rw [msq, msq, key]
  exact integral_mul_right_eq_self (fun g : SU 3 => (g : Matrix (Fin 3) (Fin 3) ℂ) i j
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) i j)) Pg

theorem msq_row_01 (j : Fin 3) : msq 0 j = msq 1 j := by
  refine msq_eq_left 1 j 0 j (fun g => ?_)
  rw [coe_Pg_mul, pmat_mul_row_one]

theorem msq_row_12 (j : Fin 3) : msq 1 j = msq 2 j := by
  refine msq_eq_left 2 j 1 j (fun g => ?_)
  rw [coe_Pg_mul, pmat_mul_row_two]

theorem msq_col_01 (i : Fin 3) : msq i 1 = msq i 0 := by
  refine msq_eq_right i 0 i 1 (fun g => ?_)
  rw [coe_mul_Pg, mul_pmat_col_zero]

theorem msq_col_12 (i : Fin 3) : msq i 2 = msq i 1 := by
  refine msq_eq_right i 1 i 2 (fun g => ?_)
  rw [coe_mul_Pg, mul_pmat_col_one]

/-- One row of a unitary matrix has square-modulus sum `1`:
`msq 0 0 + msq 0 1 + msq 0 2 = 1`.

DERIVED: `0`, `1` and `2` on the left are the three column indices of row zero, written out because
`Fin.sum_univ_three` expands the sum that way; the `1` on the right is the `(0, 0)` entry of the
identity matrix `U U* = 1`. -/
theorem msq_row_zero_sum : msq 0 0 + msq 0 1 + msq 0 2 = 1 := by
  haveI := isProbabilityMeasure_probHaar (SU 3)
  have hpt : ∀ g : SU 3, (∑ j : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 0 j
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 0 j)) = 1 := by
    intro g
    have huni : (g : Matrix (Fin 3) (Fin 3) ℂ) * star (g : Matrix (Fin 3) (Fin 3) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
    calc (∑ j : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 0 j
            * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 0 j))
        = ((g : Matrix (Fin 3) (Fin 3) ℂ) * star (g : Matrix (Fin 3) (Fin 3) ℂ)) 0 0 := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, starRingEnd_apply]
      _ = (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 := by rw [huni]
      _ = 1 := by simp
  have hint : (∫ g : SU 3, (∑ j : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 0 j
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 0 j)) ∂(probHaar (SU 3))) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp
  rw [integral_finsetSum _ (fun j _ => entry_prod_integrable 0 j 0 j), Fin.sum_univ_three] at hint
  exact hint

/-- `∫ |U_00|² d(probHaar (SU 3)) = 1 / 3`.

DERIVED: the two `0`s are the index of the entry. `1 / 3` is `1 / rank`: the nine entry moments are
equal (`msq_col_01`, `msq_col_12`, from the three-cycle) and the three in row zero sum to `1`
(`msq_row_zero_sum`). -/
theorem msq_zero_zero : msq 0 0 = 1 / 3 := by
  have h1 : msq 0 1 = msq 0 0 := msq_col_01 0
  have h2 : msq 0 2 = msq 0 0 := by rw [msq_col_12 0, h1]
  have h := msq_row_zero_sum
  rw [h1, h2] at h
  linear_combination h / 3

theorem msq_one_one : msq 1 1 = 1 / 3 := by
  have h1 : msq 1 1 = msq 1 0 := msq_col_01 1
  have h2 : msq 0 0 = msq 1 0 := msq_row_01 0
  rw [h1, ← h2, msq_zero_zero]

theorem msq_two_two : msq 2 2 = 1 / 3 := by
  have h1 : msq 2 2 = msq 2 1 := msq_col_12 2
  have h2 : msq 2 1 = msq 2 0 := msq_col_01 2
  have h3 : msq 1 0 = msq 2 0 := msq_row_12 0
  have h4 : msq 0 0 = msq 1 0 := msq_row_01 0
  rw [h1, h2, ← h3, ← h4, msq_zero_zero]

/-! ### The off-diagonal second moments vanish -/

/-- The separator `Dg = diag(1, ω, ω²)` kills `∫ U_ii · conj (U_kk)` whenever the phase
`dvec i * conj (dvec k)` it attaches is a `lam ≠ 1`. An instance of `phase_zero`; the six diagonal
pairs with `i ≠ k` are discharged below.

DERIVED: `3` is the rank, in `SU 3` and in the index type `Fin 3`; `1` is the excluded phase, which
is the case `i = k` the lemma says nothing about; `0` is the value of the integral. -/
theorem offdiag_zero (i k : Fin 3) (lam : ℂ) (hlam : lam ≠ 1)
    (hph : dvec i * (starRingEnd ℂ) (dvec k) = lam) :
    ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) i i
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) k k) ∂(probHaar (SU 3)) = 0 := by
  refine phase_zero Dg lam hlam (fun g => ?_)
  rw [coe_Dg_mul, coe_Dg_mul, map_mul, ← hph]
  ring

theorem off_01 : ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 0 0
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 1 1) ∂(probHaar (SU 3)) = 0 :=
  offdiag_zero 0 1 (om ^ 2) om_sq_ne_one (by rw [dvec_zero, dvec_one, om_conj, one_mul])

theorem off_02 : ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 0 0
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 2 2) ∂(probHaar (SU 3)) = 0 :=
  offdiag_zero 0 2 om om_ne_one (by rw [dvec_zero, dvec_two, om_sq_conj, one_mul])

theorem off_10 : ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 0 0) ∂(probHaar (SU 3)) = 0 :=
  offdiag_zero 1 0 om om_ne_one (by rw [dvec_one, dvec_zero, map_one, mul_one])

theorem off_12 : ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 2 2) ∂(probHaar (SU 3)) = 0 :=
  offdiag_zero 1 2 (om ^ 2) om_sq_ne_one (by rw [dvec_one, dvec_two, om_sq_conj]; ring)

theorem off_20 : ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 2 2
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 0 0) ∂(probHaar (SU 3)) = 0 :=
  offdiag_zero 2 0 (om ^ 2) om_sq_ne_one (by rw [dvec_two, dvec_zero, map_one, mul_one])

theorem off_21 : ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 2 2
    * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 1 1) ∂(probHaar (SU 3)) = 0 :=
  offdiag_zero 2 1 om om_ne_one
    (by rw [dvec_two, dvec_one, om_conj, show om ^ 2 * om ^ 2 = om ^ 3 * om by ring, om_cube,
      one_mul])

/-! ### `∫ |χ|² = 1` -/

/-- `∫ |tr U|² d(probHaar (SU 3)) = 1`. This is Schur orthogonality for the defining
representation, assembled from `msq_zero_zero`, `msq_one_one`, `msq_two_two` and the six `off_`
lemmas rather than cited.

DERIVED: `1 = 3 · (1/3)`, the three surviving diagonal terms at `1/3` each; `3` is the rank. -/
theorem haar_chi_normsq :
    ∫ g : SU 3, chi g * (starRingEnd ℂ) (chi g) ∂(probHaar (SU 3)) = 1 := by
  have hpt : ∀ g : SU 3, chi g * (starRingEnd ℂ) (chi g)
      = ∑ i : Fin 3, ∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℂ) i i
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) k k) := by
    intro g
    rw [chi, trace_eq_sum', map_sum, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun k _ => entry_prod_integrable i i k k))]
  have hinner : ∀ i : Fin 3,
      (∫ g : SU 3, ∑ k : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℂ) i i
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) k k) ∂(probHaar (SU 3)))
      = ∑ k : Fin 3, ∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) i i
        * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) k k) ∂(probHaar (SU 3)) :=
    fun i => integral_finsetSum _ (fun k _ => entry_prod_integrable i i k k)
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  rw [off_01, off_02, off_10, off_12, off_20, off_21]
  have d0 : (∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 0 0) ∂(probHaar (SU 3))) = 1 / 3 :=
    msq_zero_zero
  have d1 : (∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 1 1
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 1 1) ∂(probHaar (SU 3))) = 1 / 3 :=
    msq_one_one
  have d2 : (∫ g : SU 3, (g : Matrix (Fin 3) (Fin 3) ℂ) 2 2
      * (starRingEnd ℂ) ((g : Matrix (Fin 3) (Fin 3) ℂ) 2 2) ∂(probHaar (SU 3))) = 1 / 3 :=
    msq_two_two
  rw [d0, d1, d2]
  norm_num

/-! ### `∫ (Re χ)² = 1/2` -/

/-- `∫ (Re tr U)² d(probHaar (SU 3)) = 1 / 2`. Pointwise `(Re t)² = (Re(t²) + |t|²)/2`; the first
term integrates to `0` by `haar_chi_sq_zero` and the second to `1` by `haar_chi_normsq`.

DERIVED: `3` is the rank in `SU 3`. The exponent `2` is the moment; the dividing `2` is the
identity's own, an identity of `Re` and nothing else. `1 / 2` is `(0 + 1)/2`. -/
theorem haar_re_chi_sq :
    ∫ g : SU 3, ((chi g).re) ^ 2 ∂(probHaar (SU 3)) = 1 / 2 := by
  have hpt : ∀ g : SU 3, ((chi g).re) ^ 2
      = ((chi g ^ 2).re + (chi g * (starRingEnd ℂ) (chi g)).re) / 2 := by
    intro g
    rw [pow_two (chi g), Complex.mul_re, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_apply]
    ring
  have hre2 : (∫ g : SU 3, (chi g ^ 2).re ∂(probHaar (SU 3))) = 0 := by
    have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM chi_sq_integrable
    simp only [Complex.reCLM_apply] at h
    rw [h, haar_chi_sq_zero]
    simp
  have hre1 : (∫ g : SU 3, (chi g * (starRingEnd ℂ) (chi g)).re ∂(probHaar (SU 3))) = 1 := by
    have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM chi_normsq_integrable
    simp only [Complex.reCLM_apply] at h
    rw [h, haar_chi_normsq]
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_add re_chi_sq_term_integrable re_chi_normsq_integrable, hre2, hre1]
  norm_num

/-! ### The two Haar moments of the Wilson density -/

theorem wilsonDensity_eq (g : SU 3) :
    wilsonDensity (N := 3) g = 1 - (1 / 3 : ℝ) * (chi g).re := by
  unfold MassGap.WilsonAction.wilsonDensity
  rw [chi]
  norm_num

/-- The Haar mean of the Wilson density on `SU 3` is `1`: `ContactFloor.haarMean = 1`.

DERIVED: `1 − (1/3)·0`. The `1/3` is `1 / rank`, from `WilsonAction.wilsonDensity`; the `0` is
`∫ Re tr U`, from `haar_re_chi_zero`. -/
theorem haarMean_eq : MassGap.ContactFloor.haarMean = 1 := by
  haveI := isProbabilityMeasure_probHaar (SU 3)
  unfold MassGap.ContactFloor.haarMean
  rw [integral_congr_ae (Filter.Eventually.of_forall wilsonDensity_eq)]
  rw [integral_sub (integrable_const 1) (re_chi_integrable.const_mul _)]
  rw [integral_const_mul, haar_re_chi_zero, integral_const]
  simp

/-- The Haar second moment of the Wilson density on `SU 3` is `1 + 1 / 18`:
`ContactFloor.haarSecond = 1 + 1 / 18`.

DERIVED: expanding `(1 − r/3)²` against `∫ r = 0` (`haar_re_chi_zero`) and `∫ r² = 1/2`
(`haar_re_chi_sq`) gives `1 − (2/3)·0 + (1/9)·(1/2)`, where `1/9 = (1/3)²` and
`(1/9)·(1/2) = 1/18`. -/
theorem haarSecond_eq : MassGap.ContactFloor.haarSecond = 1 + 1 / 18 := by
  haveI := isProbabilityMeasure_probHaar (SU 3)
  have hA : Integrable (fun _ : SU 3 => (1 : ℝ)) (probHaar (SU 3)) := integrable_const 1
  have hB : Integrable (fun g : SU 3 => (2 / 3 : ℝ) * (chi g).re) (probHaar (SU 3)) :=
    re_chi_integrable.const_mul (2 / 3 : ℝ)
  have hC : Integrable (fun g : SU 3 => (1 / 9 : ℝ) * ((chi g).re) ^ 2) (probHaar (SU 3)) :=
    re_chi_sq_integrable.const_mul (1 / 9 : ℝ)
  have hAB : Integrable (fun g : SU 3 => (1 : ℝ) - (2 / 3 : ℝ) * (chi g).re)
      (probHaar (SU 3)) := hA.sub hB
  have hpt : ∀ g : SU 3, wilsonDensity (N := 3) g * wilsonDensity (N := 3) g
      = ((1 : ℝ) - (2 / 3 : ℝ) * (chi g).re) + (1 / 9 : ℝ) * ((chi g).re) ^ 2 := by
    intro g; rw [wilsonDensity_eq]; ring
  unfold MassGap.ContactFloor.haarSecond
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hAB hC,
    integral_sub hA hB, integral_const_mul, integral_const_mul, haar_re_chi_zero,
    haar_re_chi_sq, integral_const]
  simp
  all_goals norm_num

/-! ### The contact value -/

/-- The zero-coupling, zero-lag correlator is `1 / 18` at every extent of the form `m + 2`:
`WilsonBridge.corrClay (m + 2) 0 0 = 1 / 18`.

DERIVED: `1 / 18 = haarSecond − haarMean² = (1 + 1/18) − 1²`, by `haarSecond_eq` and `haarMean_eq`.
The two `0`s are the coupling and the lag. The `2` of `m + 2` is the minimum extent
`ContactFloor.corrClay_zero_at_zero_eq` is stated from; no extent appears on the right, which is
why one statement covers every `m`. -/
theorem corrClay_zero_at_zero_value (m : ℕ) :
    MassGap.WilsonBridge.corrClay (m + 2) 0 0 = 1 / 18 := by
  rw [MassGap.ContactFloor.corrClay_zero_at_zero_eq m, haarSecond_eq, haarMean_eq]
  norm_num

/-- The instance at extent four: `WilsonBridge.corrClay 4 0 0 = 1 / 18`, which is
`corrClay_zero_at_zero_value` read at `m = 2`.

DERIVED: `4 = 2 + 2` is the extent, and it selects a statement rather than a value. The two `0`s
are the coupling and the lag, and `1 / 18` is the value `corrClay_zero_at_zero_value` carries to
every extent `m + 2`. -/
theorem corrClay_four_zero_zero : MassGap.WilsonBridge.corrClay 4 0 0 = 1 / 18 :=
  corrClay_zero_at_zero_value 2

#print axioms om_primitive
#print axioms om_cube
#print axioms om_ne_one
#print axioms om_sq_ne_one
#print axioms om_norm
#print axioms om_inv
#print axioms om_conj
#print axioms om_sq_conj
#print axioms om_mul_conj
#print axioms om_sq_mul_conj
#print axioms dvec_zero
#print axioms dvec_one
#print axioms dvec_two
#print axioms zvec_apply
#print axioms diag_mem
#print axioms dvec_mem
#print axioms zvec_mem
#print axioms pmat_mem
#print axioms coe_Dg_mul
#print axioms coe_Zg_mul
#print axioms coe_Pg_mul
#print axioms coe_mul_Pg
#print axioms pmat_mul_row_one
#print axioms pmat_mul_row_two
#print axioms mul_pmat_col_zero
#print axioms mul_pmat_col_one
#print axioms phase_zero
#print axioms trace_eq_sum'
#print axioms entry_cont
#print axioms entry_norm_le
#print axioms integrableC
#print axioms integrableR
#print axioms chi_eq
#print axioms chi_cont
#print axioms chi_norm_le
#print axioms chi_integrable
#print axioms chi_sq_integrable
#print axioms chi_normsq_integrable
#print axioms re_chi_sq_term_integrable
#print axioms re_chi_normsq_integrable
#print axioms entry_prod_integrable
#print axioms re_chi_integrable
#print axioms re_chi_sq_integrable
#print axioms haar_chi_zero
#print axioms haar_re_chi_zero
#print axioms haar_chi_sq_zero
#print axioms msq_eq_left
#print axioms msq_eq_right
#print axioms msq_row_01
#print axioms msq_row_12
#print axioms msq_col_01
#print axioms msq_col_12
#print axioms msq_row_zero_sum
#print axioms msq_zero_zero
#print axioms msq_one_one
#print axioms msq_two_two
#print axioms offdiag_zero
#print axioms off_01
#print axioms off_02
#print axioms off_10
#print axioms off_12
#print axioms off_20
#print axioms off_21
#print axioms haar_chi_normsq
#print axioms haar_re_chi_sq
#print axioms wilsonDensity_eq
#print axioms haarMean_eq
#print axioms haarSecond_eq
#print axioms corrClay_four_zero_zero
#print axioms corrClay_zero_at_zero_value

end MassGap.ContactValue
