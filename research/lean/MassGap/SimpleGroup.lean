import Mathlib
import MassGap.SUN

/-!
# MassGap.SimpleGroup — the centre of `SU(N)`, and `IsSimpleGroup` at `N = 1, 2`

Everything here is about `IsSimpleGroup` in the abstract-group sense: no proper nontrivial normal
subgroup. Simplicity of a Lie algebra is a different property and is neither stated nor used; `su n`
is not defined anywhere in this module.

## Contents

* `smul_one_comm`, `smul_one_mem`, `mem_center_of_coe_smul_one` — for every `n ≠ 0`, each `n`-th root
  of unity `ω` gives an element `ω • 1` of `SU(n)`, and it is central.
* `exists_mem_center_ne_one` — for `2 ≤ n` the centre of `SU(n)` contains an element other than `1`,
  witnessed by a primitive `n`-th root of unity.
* `jmat`, `kmat`, `j2`, `k2` and their entry lemmas — two explicit elements of `SU(2)`. Conjugating
  by `j2 = diag(i, -i)` forces the off-diagonal entries of a central element to vanish; conjugating
  by `k2 = [[0,1],[-1,0]]` equates its two diagonal entries.
* `coe_eq_one_or_neg_one_of_mem_center`, `mem_center_of_coe_eq_one_or_neg_one`,
  `mem_center_SU_two_iff` — the centre of `SU(2)` is exactly `{1, -1}`, both inclusions.
* `j2_k2_not_comm`, `negOne2`, `negOne2_ne_one`, `negOne2_mem_center`, `not_isSimpleGroup_SU_two` —
  the centre of `SU(2)` is neither `⊥` (it contains `-1 ≠ 1`) nor `⊤` (`j2` and `k2` do not commute),
  so `SU(2)` is not a simple group.
* `subsingleton_SU_one`, `not_isSimpleGroup_SU_one` — `SU(1)` is trivial, and `IsSimpleGroup` extends
  `Nontrivial`, so it is not simple either.
* `IsCompactSimpleGauge` — `CompactSpace G ∧ IsSimpleGroup G`, named as a `def`, with
  `not_isCompactSimpleGauge_SU_two` and `not_isCompactSimpleGauge_SU_one`.
* `expect_invariant_haar_of_not_isSimpleGroup` — `CompactGauge.expect_invariant_haar` restated with
  `¬ IsSimpleGroup G` among its hypotheses and unused in its proof term, together with
  `su_one_expect_invariant` and `su_two_expect_invariant`, which discharge that hypothesis at the two
  groups above.

## Scope

Only the inclusion `scalars ⊆ center (SU n)` is proved at general `n`
(`mem_center_of_coe_smul_one`). The reverse inclusion is proved at `n = 2` alone
(`coe_eq_one_or_neg_one_of_mem_center`), from two explicit commutators; there is no general-`n`
statement that the centre consists of scalars.
-/

namespace MassGap.SimpleGroup

open MassGap.SUN

/-! ## 1. Scalar matrices are central in `SU(N)`, for every `N` -/

section Scalars

variable {n : ℕ}

/-- `M * (ω • 1) = (ω • 1) * M` for every complex scalar `ω` and every square matrix `M`. By
`mul_smul_comm` and `smul_mul_assoc`; the scalar passes through the product and the identity
cancels on both sides.

DERIVED: `1` is the identity matrix the scalar multiplies; it is the only numeral, and `n` is the
section variable. -/
theorem smul_one_comm (ω : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M * (ω • (1 : Matrix (Fin n) (Fin n) ℂ)) = (ω • (1 : Matrix (Fin n) (Fin n) ℂ)) * M := by
  rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- For `n ≠ 0` and `ω ^ n = 1`, the matrix `ω • 1` lies in `Matrix.specialUnitaryGroup (Fin n) ℂ`.
`Complex.norm_eq_one_of_pow_eq_one` gives `‖ω‖ = 1`, hence `ω * star ω = 1`, which makes `ω • 1`
unitary; `Matrix.det_smul` gives `det (ω • 1) = ω ^ n = 1`.

`hn` is required twice over: for the norm argument, and because `det (ω • 1) = ω ^ n` uses
`Fintype.card_fin`.

DERIVED: `0` is the value `n` is required to differ from in `hn`. The two `1`s are the root-of-unity
condition `ω ^ n = 1` and the identity matrix being scaled; the determinant value `1` that puts the
matrix in `SU` rather than `U` is the former, not a third numeral. -/
theorem smul_one_mem (hn : n ≠ 0) {ω : ℂ} (hω : ω ^ n = 1) :
    (ω • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈ Matrix.specialUnitaryGroup (Fin n) ℂ := by
  have hconj : ω * star ω = 1 := by
    have hn1 : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hn
    have h : ω * (starRingEnd ℂ) ω = 1 := by
      rw [Complex.mul_conj', hn1]; norm_num
    exact h
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · have hs : star (ω • (1 : Matrix (Fin n) (Fin n) ℂ))
        = (star ω) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rw [hs, smul_mul_smul_comm, one_mul, hconj, one_smul]
  · rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, hω]

/-- An element `A : SU n` whose underlying matrix is a scalar `ω • 1` lies in
`Subgroup.center (SU n)`. `Subgroup.mem_center_iff` reduces to commuting with every `g`, and
`smul_one_comm` supplies that on the underlying matrices; `Subtype.val_injective` lifts it.

No condition on `ω` beyond what `A`'s membership already carries; the hypothesis is an equation of
matrices, so it is the caller's job to produce such an `A`.

DERIVED: `1` is the identity matrix in the scalar `ω • 1`; it is the only numeral. -/
theorem mem_center_of_coe_smul_one {A : SU n} {ω : ℂ}
    (hA : (A : Matrix (Fin n) (Fin n) ℂ) = ω • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    A ∈ Subgroup.center (SU n) := by
  refine Subgroup.mem_center_iff.mpr (fun g => Subtype.val_injective ?_)
  show (g : Matrix (Fin n) (Fin n) ℂ) * (A : Matrix (Fin n) (Fin n) ℂ)
      = (A : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)
  rw [hA]
  exact smul_one_comm ω _

/-- For `2 ≤ n` there is an `A : SU n` in `Subgroup.center (SU n)` with `A ≠ 1`. The witness is
`ζ • 1` for `ζ` a primitive `n`-th root of unity, from `Complex.isPrimitiveRoot_exp`; it is
special-unitary by `smul_one_mem`, central by `mem_center_of_coe_smul_one`, and distinct from `1`
because its `(0,0)` entry is `ζ ≠ 1`.

So the centre is a nontrivial normal subgroup at every `n ≥ 2`, which is what
`not_isSimpleGroup_SU_two` spends at `n = 2`. The statement asserts existence, not the size of the
centre.

DERIVED: `2` is the lower bound on `n` in `hn`, the least rank at which a primitive root of unity
differs from `1`; below it `SU(1)` is trivial. `1` is the group identity the witness is required to
differ from. -/
theorem exists_mem_center_ne_one (hn : 2 ≤ n) :
    ∃ A : SU n, A ∈ Subgroup.center (SU n) ∧ A ≠ 1 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hn0⟩
  have hpow : ζ ^ n = 1 := hζ.pow_eq_one
  refine ⟨⟨ζ • (1 : Matrix (Fin n) (Fin n) ℂ), smul_one_mem hn0 hpow⟩,
    mem_center_of_coe_smul_one rfl, ?_⟩
  intro hEq
  have hmat : ζ • (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := congrArg Subtype.val hEq
  have h00 := congr_fun (congr_fun hmat ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  exact hζ.ne_one (by omega) h00

end Scalars

/-! ## 2. The centre of `SU(2)`, computed exactly

Two explicit elements do the work. `jmat = diag(i, -i)` kills the off-diagonal entries of anything
that commutes with it, and `kmat = [[0,1],[-1,0]]` equates the two diagonal entries. Determinant one
then squares the common diagonal entry to `1`. -/

/-- `!![a, 0; 0, a] = a • (1 : Matrix (Fin 2) (Fin 2) ℂ)`. By `ext` and `fin_cases` on both indices.

DERIVED: `2` is the rank, the size of the matrix. The two `0`s are the off-diagonal entries, which is
what makes the matrix scalar, and `1` is the identity matrix being scaled. -/
theorem matrix_scalar_fin_two (a : ℂ) :
    !![a, 0; 0, a] = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul]

/-- The matrix `diag(Complex.I, -Complex.I)` of size two. `jmat_mem` shows it is special-unitary and
`j2` packages it as an element of `SU 2`.

Its role is in `coe_eq_one_or_neg_one_of_mem_center`: commuting with it forces both off-diagonal
entries of a central element to vanish, because the two diagonal entries are distinct.

DERIVED: `2` is the rank, the size of the matrix; `0` are the two off-diagonal entries, which make
it diagonal. `Complex.I` is a named constant, not a numeral. -/
noncomputable def jmat : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem jmat_mem : jmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [jmat, Matrix.det_fin_two]

/-- `jmat` as an element of `SU 2`, paired with `jmat_mem`.

DERIVED: `2` is the rank, carried from `jmat`; the definition introduces no numeral of its own. -/
noncomputable def j2 : SU 2 := ⟨jmat, jmat_mem⟩

theorem jmat_00 : jmat 0 0 = Complex.I := by simp [jmat]
theorem jmat_01 : jmat 0 1 = 0 := by simp [jmat]
theorem jmat_10 : jmat 1 0 = 0 := by simp [jmat]
theorem jmat_11 : jmat 1 1 = -Complex.I := by simp [jmat]

/-- The matrix `!![0, 1; -1, 0]` of size two. `kmat_mem` shows it is special-unitary and `k2`
packages it as an element of `SU 2`.

Its role is in `coe_eq_one_or_neg_one_of_mem_center`: commuting with it equates the two diagonal
entries of a central element, because it exchanges the two basis vectors up to sign.

DERIVED: `2` is the rank, the size of the matrix; `0` and `1` are its entries. The sign on the lower
`-1` is what makes the determinant `1` rather than `-1`, so it is what puts the matrix in `SU`
rather than only in `U`. -/
noncomputable def kmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem kmat_mem : kmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [kmat, Matrix.det_fin_two]

/-- `kmat` as an element of `SU 2`, paired with `kmat_mem`.

DERIVED: `2` is the rank, carried from `kmat`; the definition introduces no numeral of its own. -/
noncomputable def k2 : SU 2 := ⟨kmat, kmat_mem⟩

theorem kmat_00 : kmat 0 0 = 0 := by simp [kmat]
theorem kmat_01 : kmat 0 1 = 1 := by simp [kmat]
theorem kmat_11 : kmat 1 1 = 0 := by simp [kmat]

/-- `j2 * k2 ≠ k2 * j2`. If they were equal, the `(0,1)` entry of the underlying matrix identity
would give `2 * Complex.I = 0`, and neither factor vanishes.

So `SU 2` is not commutative, which is what rules out the centre being all of `SU 2` in
`not_isSimpleGroup_SU_two`.

DERIVED: no numeral of this declaration's. `2` is the rank, carried by the types of `j2` and `k2`;
the `(0,1)` entry and the factor `2` appearing in the proof are not part of the statement. -/
theorem j2_k2_not_comm : j2 * k2 ≠ k2 * j2 := by
  intro h
  have hm : jmat * kmat = kmat * jmat := congrArg Subtype.val h
  have h01 := congr_fun (congr_fun hm 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    jmat_00, jmat_01, jmat_11, kmat_00, kmat_01, kmat_11] at h01
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination h01
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact Complex.I_ne_zero h3

/-- Every `A : SU 2` in the centre has underlying matrix `1` or `-1`.

Three steps, each an entry of a commutator identity. The `(0,1)` and `(1,0)` entries of
`jmat * A = A * jmat` give `2·I·A₀₁ = 0` and `2·I·A₁₀ = 0`, so both off-diagonal entries vanish. The
`(0,1)` entry of `kmat * A = A * kmat` gives `A₁₁ = A₀₀`. Then `det A = 1` reads `A₀₀² = 1`, so
`(A₀₀ - 1)(A₀₀ + 1) = 0` and the matrix is `±1`.

This is the inclusion `center (SU 2) ⊆ scalars`, proved at rank two only; the argument uses the two
explicit matrices and does not generalise as written.

DERIVED: `2` is the rank throughout. `1` is the identity matrix, and `-1` its negation, the two
possible values; the determinant condition `det = 1` that forces them is `SU`'s own and is carried by
the type of `A`. -/
theorem coe_eq_one_or_neg_one_of_mem_center {A : SU 2} (hA : A ∈ Subgroup.center (SU 2)) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  have hc := Subgroup.mem_center_iff.mp hA
  have hj : jmat * (A : Matrix (Fin 2) (Fin 2) ℂ) = (A : Matrix (Fin 2) (Fin 2) ℂ) * jmat :=
    congrArg Subtype.val (hc j2)
  have hk : kmat * (A : Matrix (Fin 2) (Fin 2) ℂ) = (A : Matrix (Fin 2) (Fin 2) ℂ) * kmat :=
    congrArg Subtype.val (hc k2)
  -- the `(0,1)` entry of `jmat * A = A * jmat` reads `i·b = -i·b`
  have hb : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    have h := congr_fun (congr_fun hj 0) 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
      jmat_00, jmat_01, jmat_11] at h
    have h2 : (2 : ℂ) * (Complex.I * (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 Complex.I_ne_zero
      · exact h4
  -- the `(1,0)` entry reads `-i·c = i·c`
  have hcc : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    have h := congr_fun (congr_fun hj 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
      jmat_10, jmat_11, jmat_00] at h
    have h2 : (2 : ℂ) * (Complex.I * (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 Complex.I_ne_zero
      · exact h4
  -- the `(0,1)` entry of `kmat * A = A * kmat` reads `d = a`
  have hd : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    have h := congr_fun (congr_fun hk 0) 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
      kmat_00, kmat_01, kmat_11] at h
    linear_combination h
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp A.2).2
  rw [Matrix.det_fin_two, hb, hcc, hd] at hdet
  have hEta : (A : Matrix (Fin 2) (Fin 2) ℂ)
      = !![(A : Matrix (Fin 2) (Fin 2) ℂ) 0 0, 0; 0, (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0] := by
    conv_lhs => rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) ℂ)]
    rw [hb, hcc, hd]
  have hfac : ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - 1)
      * ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + 1) = 0 := by
    linear_combination hdet
  rcases mul_eq_zero.mp hfac with h | h
  · left
    have ha : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by linear_combination h
    rw [hEta, ha]
    exact Matrix.one_fin_two.symm
  · right
    have ha : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = -1 := by linear_combination h
    rw [hEta, ha, matrix_scalar_fin_two]
    simp

/-- An `A : SU 2` whose underlying matrix is `1` or `-1` is central. `Subgroup.mem_center_iff`
reduces to commuting with every `g`, and both cases are closed by `simp` once the matrix is
rewritten.

The converse inclusion to `coe_eq_one_or_neg_one_of_mem_center`.

DERIVED: `2` is the rank. `1` is the identity matrix and `-1` its negation, the two hypothesised
values. -/
theorem mem_center_of_coe_eq_one_or_neg_one {A : SU 2}
    (h : (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    A ∈ Subgroup.center (SU 2) := by
  refine Subgroup.mem_center_iff.mpr (fun g => Subtype.val_injective ?_)
  show (g : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ)
      = (A : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
  rcases h with h | h <;> rw [h] <;> simp

/-- `A ∈ Subgroup.center (SU 2)` if and only if its underlying matrix is `1` or `-1`. The two
inclusions, `coe_eq_one_or_neg_one_of_mem_center` and `mem_center_of_coe_eq_one_or_neg_one`, paired.

The centre of `SU 2` therefore has exactly two elements. Stated at rank two; no corresponding
equivalence is proved at other ranks.

DERIVED: `2` is the rank. `1` is the identity matrix and `-1` its negation — the square roots of
unity, which are the rank-two case of the `n`-th roots that `smul_one_mem` embeds. -/
theorem mem_center_SU_two_iff {A : SU 2} :
    A ∈ Subgroup.center (SU 2) ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1 :=
  ⟨coe_eq_one_or_neg_one_of_mem_center, mem_center_of_coe_eq_one_or_neg_one⟩

/-- `-1` as an element of `SU 2`: the negated identity matrix, with its membership proof inline —
unitary by `simp`, determinant `1` by `Matrix.det_fin_two`.

`negOne2_ne_one` and `negOne2_mem_center` are the two facts about it that
`not_isSimpleGroup_SU_two` consumes.

DERIVED: `2` is the rank; `1` is the identity matrix this negates. `-1` lies in `SU 2` because
`det (-I) = (-1)² = 1` at rank two, so the rank's evenness is what admits it. -/
noncomputable def negOne2 : SU 2 :=
  ⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
    · simp
    · simp [Matrix.det_fin_two]⟩

theorem negOne2_ne_one : negOne2 ≠ 1 := by
  intro h
  have hm : (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg Subtype.val h
  have h00 := congr_fun (congr_fun hm 0) 0
  norm_num [Matrix.neg_apply, Matrix.one_apply_eq] at h00

theorem negOne2_mem_center : negOne2 ∈ Subgroup.center (SU 2) :=
  mem_center_of_coe_eq_one_or_neg_one (A := negOne2) (Or.inr rfl)

/-! ## 3. `SU(2)` is not a simple group, and `SU(1)` is not even nontrivial -/

/-- `¬ IsSimpleGroup (SU 2)`. `IsSimpleGroup` forces every normal subgroup to be `⊥` or `⊤`, and the
centre is normal; it is not `⊥` because `negOne2` is in it and differs from `1`, and it is not `⊤`
because `j2` would then commute with `k2`, contradicting `j2_k2_not_comm`.

In the abstract-group sense only. Simplicity of a Lie algebra is a different property and is not
addressed.

DERIVED: `2` is the rank; it is the only numeral. -/
theorem not_isSimpleGroup_SU_two : ¬ IsSimpleGroup (SU 2) := by
  intro hs
  haveI := hs
  have hn : (Subgroup.center (SU 2)).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · have hmem := negOne2_mem_center
    rw [hbot] at hmem
    exact negOne2_ne_one (Subgroup.mem_bot.mp hmem)
  · have hj2 : j2 ∈ Subgroup.center (SU 2) := by
      rw [htop]; exact Subgroup.mem_top j2
    exact j2_k2_not_comm (Subgroup.mem_center_iff.mp hj2 k2).symm

/-- `Subsingleton (SU 1)`: every element of `SU 1` has underlying matrix `1`. The determinant of a
one-by-one matrix is its single entry, and `SU` requires that to be `1`; `Subsingleton` on `Fin 1`
then identifies the indices.

DERIVED: `1` is the rank, which makes the matrix one-by-one, and the value its single entry is
pinned to by the determinant condition; the two coincide because `det` of a `1 × 1` matrix is that
entry. -/
theorem subsingleton_SU_one : Subsingleton (SU 1) := by
  have key : ∀ a : SU 1, (a : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    intro a
    have ha : (a : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp a.2).2
      rwa [Matrix.det_fin_one] at h
    ext i j
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    rw [hi, hj, ha, Matrix.one_apply_eq]
  exact ⟨fun a b => Subtype.val_injective ((key a).trans (key b).symm)⟩

/-- `¬ IsSimpleGroup (SU 1)`. `IsSimpleGroup` extends `Nontrivial`, so it supplies a pair of distinct
elements; `subsingleton_SU_one` identifies them.

Fails for a different reason than `not_isSimpleGroup_SU_two`: there the centre is a proper nontrivial
normal subgroup, here the group has too few elements to be simple at all.

DERIVED: `1` is the rank; it is the only numeral. -/
theorem not_isSimpleGroup_SU_one : ¬ IsSimpleGroup (SU 1) := by
  intro hs
  haveI := hs
  haveI := subsingleton_SU_one
  obtain ⟨a, b, hab⟩ := exists_pair_ne (SU 1)
  exact hab (Subsingleton.elim a b)

/-! ## 4. The conjunction, named -/

/-- `CompactSpace G ∧ IsSimpleGroup G`, for a topological group `G`. Named as a `def` so that
`not_isCompactSimpleGauge_SU_two` and `not_isCompactSimpleGauge_SU_one` can state which conjunct
fails.

`IsSimpleGroup` here is the abstract-group property. Simplicity of a Lie algebra is a different
property; no Lie algebra of a matrix group is defined in this module, so the two cannot be compared
here.

DERIVED: no numeral. `G` is the caller's group. -/
def IsCompactSimpleGauge (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  CompactSpace G ∧ IsSimpleGroup G

theorem not_isCompactSimpleGauge_SU_two : ¬ IsCompactSimpleGauge (SU 2) :=
  fun h => not_isSimpleGroup_SU_two h.2

theorem not_isCompactSimpleGauge_SU_one : ¬ IsCompactSimpleGauge (SU 1) :=
  fun h => not_isSimpleGroup_SU_one h.2

/-- `CompactGauge.expect_invariant_haar` restated with an extra hypothesis `_hns : ¬ IsSimpleGroup G`.
The proof term is that theorem applied to the remaining arguments, and `_hns` is spelled with an
underscore because it is unused.

So the Haar invariance of the Gibbs expectation under a lattice symmetry is available on groups that
are not simple, and its derivation consumes compactness and Haar invariance rather than simplicity.

DERIVED: no numeral. `G`, `sys`, `sym`, `β` and `O` are the caller's. -/
theorem expect_invariant_haar_of_not_isSimpleGroup (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    (_hns : ¬ IsSimpleGroup G) {sys : MassGap.LatticeGauge.System G}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar G) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar G) β O :=
  MassGap.CompactGauge.expect_invariant_haar G sym β O

/-- `expect_invariant_haar_of_not_isSimpleGroup` at `G = SU 1`, with the non-simplicity hypothesis
discharged by `not_isSimpleGroup_SU_one`. So its hypothesis class is inhabited.

`SU 1` is the trivial group by `subsingleton_SU_one`, so the configuration space is a single point
and the invariance is degenerate there.

DERIVED: `1` is the rank of the gauge group instantiated; it is the only numeral. -/
theorem su_one_expect_invariant {sys : MassGap.LatticeGauge.System (SU 1)}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar (SU 1)) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar (SU 1)) β O :=
  expect_invariant_haar_of_not_isSimpleGroup (SU 1) not_isSimpleGroup_SU_one sym β O

/-- `expect_invariant_haar_of_not_isSimpleGroup` at `G = SU 2`, with the non-simplicity hypothesis
discharged by `not_isSimpleGroup_SU_two`. Unlike `su_one_expect_invariant` the group here is
nontrivial, so the configuration space is not a point.

DERIVED: `2` is the rank of the gauge group instantiated; it is the only numeral. -/
theorem su_two_expect_invariant {sys : MassGap.LatticeGauge.System (SU 2)}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar (SU 2)) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar (SU 2)) β O :=
  expect_invariant_haar_of_not_isSimpleGroup (SU 2) not_isSimpleGroup_SU_two sym β O

/-! ## Scope of the centre computation

Every `IsSimpleGroup` statement above is about the abstract group. No Lie algebra appears: this
module defines no `su n`, and `Matrix.specialUnitaryGroup` carries only `Group`, `StarMul`, `Inv`
and `mem_specialUnitaryGroup_iff`, so no Lie-algebra property of `SU(N)` is stated or used.

The two inclusions between the centre and the scalars are proved at different generality.
`mem_center_of_coe_smul_one` gives `scalars ⊆ center (SU n)` at every `n`.
`coe_eq_one_or_neg_one_of_mem_center` gives the reverse at `n = 2` alone, from the two explicit
commutators with `jmat` and `kmat`; there is no general-`n` statement that
`center (SU n) ⊆ scalars`. The `SU(2)` centre is computed here directly — Mathlib's
`SpecialLinearGroup.mem_center_iff` commutes with transvections, which are not special-unitary. -/

#print axioms smul_one_mem
#print axioms mem_center_of_coe_smul_one
#print axioms exists_mem_center_ne_one
#print axioms matrix_scalar_fin_two
#print axioms j2_k2_not_comm
#print axioms coe_eq_one_or_neg_one_of_mem_center
#print axioms mem_center_SU_two_iff
#print axioms negOne2_ne_one
#print axioms not_isSimpleGroup_SU_two
#print axioms subsingleton_SU_one
#print axioms not_isSimpleGroup_SU_one
#print axioms not_isCompactSimpleGauge_SU_two
#print axioms not_isCompactSimpleGauge_SU_one
#print axioms expect_invariant_haar_of_not_isSimpleGroup
#print axioms su_one_expect_invariant
#print axioms su_two_expect_invariant

end MassGap.SimpleGroup
