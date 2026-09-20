import Mathlib
import MassGap.ContactFloor

/-!
# MassGap.ContactValue — the exact zero-coupling contact value on `SU(3)`

`ContactFloor.corrClay_zero_at_zero_eq` reduces the zero-coupling, zero-lag connected plaquette
correlator at every extent `n ≥ 2` to ONE number, `haarSecond − haarMean ^ 2`: two Haar integrals of
the Wilson density `φ(g) = 1 − (1/3)·Re tr g` on `SU(3)`. It does not evaluate them, and
`ContactFloor.exists_haar_floor` only asserts the difference is positive. This file evaluates them.

## The obstruction and the way round it

Mathlib at this pin has no Peter–Weyl and no Schur orthogonality for compact groups, so `∫ |χ|² = 1`
is not available as a citation. `HaarMoments` solves the same problem for `SU(2)` by
**invariant projection on explicit group elements**: translating by a fixed `h` multiplies the
integrand by a fixed scalar `λ`, and `c = λ·c` with `λ ≠ 1` forces `c = 0`. That method is not
`SU(2)`-specific; only the elements are. `HaarMoments.haar_su2_second_moment` is stated for
`Fin 2` matrices throughout and does not generalise as written — it is re-derived here for `Fin 3`
with `SU(3)`'s own elements.

Three elements of `SU(3)` carry the whole file, and each is in `SU(3)` for a reason `SU(2)` cannot
copy:

* `Zg = ω·1` with `ω` a primitive cube root of unity — **central**, and in the group because
  `det(ω·1) = ω³ = 1`. It multiplies the character by `ω`, so `∫ χ = 0` and, crucially,
  `∫ χ² = ω²·∫ χ² ⇒ ∫ χ² = 0`. THE SECOND ONE IS FALSE FOR `SU(2)`: the central elements of `SU(2)`
  are `±1`, whose square is `1`, the projection is vacuous, and indeed `∫ χ² = 1` there. That is a
  factor of `2` of the `4.5` between the two answers — see the arithmetic below.
* `Dg = diag(1, ω, ω²)` — left translation attaches the phase `ω^{i−k}` to `g_{ii}·conj(g_{kk})`,
  which is `1` only when `i = k`, so every off-diagonal second moment vanishes.
* `Pg` — the three-cycle permutation matrix, in `SU(3)` because a three-cycle is EVEN. It makes the
  nine numbers `∫ |g_{ij}|²` equal; unitarity of one row then fixes each at `1/3`.

## What comes out

`∫ Re χ = 0`, `∫ (Re χ)² = 1/2`, hence `haarMean = 1`, `haarSecond = 1 + 1/18`, and

    WilsonBridge.corrClay 4 0 0 = 1/18.

## Where each numeral comes from

* DERIVED `3`: the rank of the gauge group, carried in from `WilsonBridge.corrClay`, which is the
  Clay problem's `SU(3)`. Every `Fin 3`, every `ω³`, and the `1/3` below are that one datum.
* DERIVED `1/3`: `∫ |g_{ij}|² `. The nine are equal (`Pg`) and one row of a unitary matrix has three
  entries summing in square modulus to `1`; `1/3 = 1/(rank)`.
* DERIVED `1`: `∫ |χ|² = 3 · (1/3)`, the three diagonal terms that survive `Dg`.
* DERIVED `1/2`: `∫ (Re χ)² = (∫ Re(χ²) + ∫ |χ|²)/2 = (0 + 1)/2`. The dividing `2` is the `2` of
  `(Re t)² = (Re(t²) + |t|²)/2`, an identity of `Re` and nothing else; the `0` is `Re(∫ χ²)` and the
  `1` is `∫ |χ|²`.
* DERIVED `1/9`: `(1/3)²`, the square of the `1/N` normalising `wilsonDensity`.
* DERIVED `1/18`: `haarSecond − haarMean² = (1 + (1/9)·(1/2)) − 1² = 1/18`. In general the contact
  value is `(1/N²)·∫ (Re χ)²`, so `SU(2)`'s `1/4` and `SU(3)`'s `1/18` differ by `4.5`, of which the
  centre argument above contributes `2` (`∫ (Re χ)²`: `1` against `1/2`) and the `1/N²` of
  `wilsonDensity` contributes `2.25` (`1/4` against `1/9`). Neither factor alone is the gap.
* DERIVED `4`: the extent at which the target is stated; `4 = 2 + 2` feeds
  `ContactFloor.corrClay_zero_at_zero_eq` at `m = 2`. `corrClay_zero_at_zero_value` below carries the
  same value to every extent `≥ 2`.
* DERIVED both `0`s in `corrClay 4 0 0`: the first is the COUPLING `β = 0` — this file is the
  zero-coupling contact term and nothing else — and the second is the LAG, `0 : Fin 4`, which is what
  makes the correlator a variance rather than a separated two-point function.
* DERIVED `2` as an exponent: the definition of a second moment, and of a variance. DERIVED `2` as
  the minimum extent in `m + 2`: `ContactFloor`'s own, the extent at which a plaquette's four links
  are distinct and the holonomy pushes Haar forward.

Foundational footprint only. Build: `python research/code/lean_build.py build MassGap.ContactValue`.
-/

namespace MassGap.ContactValue

open Matrix MeasureTheory
open MassGap.SUN MassGap.CompactGauge MassGap.WilsonAction

/-! ### A primitive cube root of unity

DERIVED: `3` is the rank of `SU(3)`; the cube root exists because `det(ω·1) = ω^3` on a `3 × 3`
matrix, so it is the rank that selects the order of the root. -/

/-- A primitive cube root of unity.

DERIVED: both numerals come from the gauge group. The `3` is the rank of `SU(3)` and fixes the ORDER
of the root, because `det(ω·1) = ω³` on a `3 × 3` matrix; the `2` is the `2π` of one full turn, which
that order divides. At rank `N` the same expression reads `exp(2πi/N)`, so neither is chosen here. -/
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

/-- The diagonal separator `diag(1, ω, ω²)`.

DERIVED: the entries are the three successive powers `ω⁰, ω¹, ω²` of the cube root, one per row, and
the `3` is `Fin 3`, the rank. Exponents and an index type, not magnitudes: the determinant is
`ω^(0+1+2) = ω³ = 1`, which is exactly what puts the element in `SU(3)`. -/
noncomputable def dvec : Fin 3 → ℂ := ![1, om, om ^ 2]

/-- The central element `ω·1`.

DERIVED: the `3` is `Fin 3`, the rank — an index type. The `1` is the identity matrix `ω` scales;
`ω·1` is the centre at whatever rank, so there is nothing here to choose. -/
noncomputable def zvec : Fin 3 → ℂ := ![om, om, om]

theorem dvec_zero : dvec 0 = 1 := by simp [dvec]
theorem dvec_one : dvec 1 = om := by simp [dvec]
theorem dvec_two : dvec 2 = om ^ 2 := by simp [dvec]

theorem zvec_apply (i : Fin 3) : zvec i = om := by fin_cases i <;> simp [zvec]

/-- A diagonal matrix whose entries have unit modulus and unit product is in `SU(3)`. -/
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

/-- The three-cycle permutation matrix. It is in `SU(3)` because a three-cycle is EVEN — the
corresponding transposition matrix of `SU(2)` has determinant `−1` and needs a sign, which is why
`HaarMoments.wmat` carries one and this does not.

DERIVED: the `0`s and `1`s are the incidence pattern of a permutation — absent and present — and the
`3` is the rank, an index type. The pattern is the three-cycle `1 ↦ 2 ↦ 3 ↦ 1` written out; no entry
is a magnitude and none is chosen. -/
noncomputable def pmat : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem pmat_mem : pmat ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [pmat, Matrix.det_fin_three]

/-- `diag(1, ω, ω²)` as an element of `SU(3)`.

DERIVED: the `3` is the rank in the type `SU 3`, and the `1` is the first entry of `dvec`, already
derived there. This declaration adds no number of its own — it pairs that matrix with its membership
proof. -/
noncomputable def Dg : SU 3 := ⟨Matrix.diagonal dvec, dvec_mem⟩

/-- `ω·1` as an element of `SU(3)` — the centre.

DERIVED: as `Dg` — the `3` is the rank in `SU 3` and the `1` is the identity `ω` scales, both from
`zvec`. This pairs that matrix with its membership proof. -/
noncomputable def Zg : SU 3 := ⟨Matrix.diagonal zvec, zvec_mem⟩

/-- The three-cycle as an element of `SU(3)`.

DERIVED: the `3` is the rank in the type `SU 3`; `pmat` carries the pattern. -/
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

/-- **Invariant projection.** If left translation by one group element multiplies the integrand by a
fixed scalar `λ ≠ 1`, the integral is zero. This is the whole method; Mathlib has no Schur
orthogonality to cite, and everything below is an instance of this line. -/
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

/-- The fundamental character, as a function on `SU(3)`.

DERIVED: every `3` is the rank — the group in `SU 3` and its matrix index type `Fin 3`. The trace
sums the diagonal of whatever matrix it is given and takes no parameter of its own. -/
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

/-- DERIVED: `3` is the rank — the character is a sum of `3` entries, each of modulus at most `1`. -/
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

/-- **`∫_{SU(3)} tr U dHaar = 0`** — by translation by the CENTRAL element `ω·1`, which multiplies
the character by `ω ≠ 1`. -/
theorem haar_chi_zero : ∫ g : SU 3, chi g ∂(probHaar (SU 3)) = 0 := by
  refine phase_zero Zg om om_ne_one (fun g => ?_)
  rw [chi_eq, chi_eq, coe_Zg_mul, coe_Zg_mul, coe_Zg_mul]
  ring

/-- `∫_{SU(3)} Re tr U dHaar = 0`. -/
theorem haar_re_chi_zero : ∫ g : SU 3, (chi g).re ∂(probHaar (SU 3)) = 0 := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM chi_integrable
  simp only [Complex.reCLM_apply] at h
  rw [h, haar_chi_zero]
  simp

/-! ### The moment that `SU(2)` does NOT share: `∫ χ² = 0` -/

/-- **`∫_{SU(3)} (tr U)² dHaar = 0`.** Translation by `ω·1` multiplies `χ²` by `ω²`, and `ω² ≠ 1`
because `ω` has order `3`. THE ANALOGUE FAILS AT `SU(2)`: its centre is `{±1}` and `(±1)² = 1`, so
no central element separates `χ²`; there `∫ χ² = ∫ |χ|² = 1`. That doubles `∫ (Re χ)²`, hence doubles
the contact value, at whatever rank; it is not by itself the `SU(2)`/`SU(3)` gap. -/
theorem haar_chi_sq_zero : ∫ g : SU 3, chi g ^ 2 ∂(probHaar (SU 3)) = 0 := by
  refine phase_zero Zg (om ^ 2) om_sq_ne_one (fun g => ?_)
  have hc : chi (Zg * g) = om * chi g := by
    rw [chi_eq, chi_eq, coe_Zg_mul, coe_Zg_mul, coe_Zg_mul]; ring
  rw [hc]; ring

/-! ### The second moment `∫ |χ|² = 1` -/

/-- The nine numbers `∫ |U_{ij}|²`.

DERIVED: every `3` is the rank — `SU 3` and the matrix index type `Fin 3`, so `i` and `j` are matrix
INDICES rather than magnitudes, and "nine" is `3 × 3` of them. The `2` of `|·|²` is the second moment
being defined. -/
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

/-- **One row of a unitary matrix has square-modulus sum `1`.** DERIVED: the `1` is `(U U*)_{00}`, an
entry of the identity. -/
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

/-- **`∫ |U_{00}|² = 1/3`.** DERIVED: `1/3 = 1/(rank)`; the nine entry moments are equal by the
three-cycle and one row's three of them sum to `1`. -/
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

/-- The separator `diag(1, ω, ω²)` kills `∫ U_{ii}·conj(U_{kk})` whenever the phase it attaches is
not `1`. -/
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

/-- **The character norm: `∫_{SU(3)} |tr U|² dHaar = 1`** — Schur orthogonality for the defining
representation, derived rather than cited. DERIVED: `1 = 3 · (1/3)`, the three surviving diagonal
terms at `1/3` each. -/
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

/-- **`∫_{SU(3)} (Re tr U)² dHaar = 1/2`.** The pointwise algebra is
`(Re t)² = (Re(t²) + |t|²)/2`; DERIVED: the `2` on the right is that identity's own, the `Re(t²)`
integrates to `0` by `haar_chi_sq_zero` and the `|t|²` to `1` by `haar_chi_normsq`, giving
`(0 + 1)/2`. At `SU(2)` the first term is `1`, not `0`, and the answer is `1`. -/
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

/-- **`haarMean = 1`.** DERIVED: `1 − (1/3)·0`; the `1/3` is `1/(rank)` from `wilsonDensity` and the
`0` is `∫ Re tr U`. -/
theorem haarMean_eq : MassGap.ContactFloor.haarMean = 1 := by
  haveI := isProbabilityMeasure_probHaar (SU 3)
  unfold MassGap.ContactFloor.haarMean
  rw [integral_congr_ae (Filter.Eventually.of_forall wilsonDensity_eq)]
  rw [integral_sub (integrable_const 1) (re_chi_integrable.const_mul _)]
  rw [integral_const_mul, haar_re_chi_zero, integral_const]
  simp

/-- **`haarSecond = 1 + 1/18`.** DERIVED: `1 − (2/3)·0 + (1/9)·(1/2)`, the expansion of
`(1 − r/3)²` against `∫ r = 0` and `∫ r² = 1/2`; `1/9 = (1/3)²` and `(1/9)·(1/2) = 1/18`. -/
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

/-- **The zero-coupling contact value at every extent at least two is `1/18`.**

DERIVED: `1/18 = haarSecond − haarMean² = (1 + 1/18) − 1²`. No extent appears on the right, which is
`ContactFloor.corrClay_zero_at_zero_eq`'s content and the reason one statement covers every `m`. -/
theorem corrClay_zero_at_zero_value (m : ℕ) :
    MassGap.WilsonBridge.corrClay (m + 2) 0 0 = 1 / 18 := by
  rw [MassGap.ContactFloor.corrClay_zero_at_zero_eq m, haarSecond_eq, haarMean_eq]
  norm_num

/-- **THE ZERO-COUPLING CONTACT VALUE AT THE CLAY EXTENT IS `1/18`.** The instance at `m = 2`; the
`4` selects a statement, not a value. -/
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
