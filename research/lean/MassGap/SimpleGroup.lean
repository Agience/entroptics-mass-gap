import Mathlib
import MassGap.SUN

/-!
# MassGap.SimpleGroup — the simplicity clause of Clay row A1

Clay's row A1 asks for a Yang–Mills theory "for any compact **simple** gauge group `G`". `SUN.lean`
and `CompactGauge.lean` discharge *compact*: `SU(N)` is a compact Hausdorff Borel topological group
(`SUN.isCompact_coe`) carrying the canonical probability Haar measure `CompactGauge.probHaar`. This
file addresses the other word.

## What the word can mean, and which reading this file settles

"Simple" in "compact simple Lie group" is a statement about the **Lie algebra**: `su(N)` has no
proper nonzero ideals. That reading cannot even be stated against Mathlib v4.31 — see the module note
at the end of this file for exactly what is missing.

The other reading, `IsSimpleGroup G` (no proper nontrivial normal subgroup), is decidable here, and
the answer is **no**: `SU(N)` has a centre. This file computes that centre.

## Contents

* `smul_one_mem` / `mem_center_of_coe_smul_one` — for every `N`, each `N`-th root of unity `ω` gives
  a central element `ω • 1` of `SU(N)`;
* `exists_mem_center_ne_one` — hence for every `N ≥ 2` the centre of `SU(N)` is **nontrivial**;
* `mem_center_SU_two_iff` — **the centre of `SU(2)` is exactly `{1, -1}`**, both inclusions;
* `not_isSimpleGroup_SU_two` — `SU(2)` is **not** a simple group: its centre is a proper nontrivial
  normal subgroup;
* `subsingleton_SU_one` / `not_isSimpleGroup_SU_one` — `SU(1)` is the trivial group, so it is not
  simple either (it is not even nontrivial);
* `IsCompactSimpleGauge` — the Clay hypothesis named as a `def`, in the abstract-group reading;
* `expect_invariant_haar_of_not_isSimpleGroup` — **simplicity is orthogonal to the development**: the
  A1/A2a Haar invariance holds with `¬ IsSimpleGroup G` in hand, and `su_one_expect_invariant` /
  `su_two_expect_invariant` exhibit two gauge groups where that hypothesis is discharged. So nothing
  downstream of `CompactGauge.expect_invariant_haar` consumes simplicity.

Foundational footprint only (`#print axioms` at the end). Build: `lake build MassGap.SimpleGroup`.
-/

namespace MassGap.SimpleGroup

open MassGap.SUN

/-! ## 1. Scalar matrices are central in `SU(N)`, for every `N` -/

section Scalars

variable {n : ℕ}

/-- A scalar matrix commutes with every matrix. -/
theorem smul_one_comm (ω : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M * (ω • (1 : Matrix (Fin n) (Fin n) ℂ)) = (ω • (1 : Matrix (Fin n) (Fin n) ℂ)) * M := by
  rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- `ω • 1` is special-unitary whenever `ω` is an `N`-th root of unity: `ω ^ N = 1` forces `‖ω‖ = 1`,
which gives unitarity, and `det (ω • 1) = ω ^ N = 1`. -/
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

/-- A scalar element of `SU(N)` lies in the centre. -/
theorem mem_center_of_coe_smul_one {A : SU n} {ω : ℂ}
    (hA : (A : Matrix (Fin n) (Fin n) ℂ) = ω • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    A ∈ Subgroup.center (SU n) := by
  refine Subgroup.mem_center_iff.mpr (fun g => Subtype.val_injective ?_)
  show (g : Matrix (Fin n) (Fin n) ℂ) * (A : Matrix (Fin n) (Fin n) ℂ)
      = (A : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)
  rw [hA]
  exact smul_one_comm ω _

/-- **For `N ≥ 2` the centre of `SU(N)` is nontrivial.** A primitive `N`-th root of unity `ζ ≠ 1`
gives the central element `ζ • 1 ≠ 1`. This is the obstruction to `SU(N)` being a simple group: the
centre is a nontrivial normal subgroup. -/
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

/-- `!![a, 0; 0, a]` is the scalar matrix `a • 1`. -/
theorem matrix_scalar_fin_two (a : ℂ) :
    !![a, 0; 0, a] = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul]

/-- The diagonal element `diag(i, -i)` of `SU(2)`.

DERIVED: `2` is the rank; `0` are the off-diagonal entries that make it diagonal. The matrix
is written out because the centre computation needs an element whose conjugation action kills
the off-diagonals, and this is the standard one. -/
noncomputable def jmat : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem jmat_mem : jmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [jmat, Matrix.det_fin_two]

/-- `j2 = diag(i,-i)` as an element of `SU(2)`.

DERIVED: `2` is the rank, carried from `jmat`. -/
noncomputable def j2 : SU 2 := ⟨jmat, jmat_mem⟩

theorem jmat_00 : jmat 0 0 = Complex.I := by simp [jmat]
theorem jmat_01 : jmat 0 1 = 0 := by simp [jmat]
theorem jmat_10 : jmat 1 0 = 0 := by simp [jmat]
theorem jmat_11 : jmat 1 1 = -Complex.I := by simp [jmat]

/-- The swap element `[[0,1],[-1,0]]` of `SU(2)`.

DERIVED: `2` is the rank; `0` and `1` are the entries of the swap, which is the element whose
conjugation action exchanges the two diagonal entries and so equates them on a central
element. Determinant `1` is what puts it in `SU` rather than `U`. -/
noncomputable def kmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem kmat_mem : kmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [kmat, Matrix.det_fin_two]

/-- `k2 = [[0,1],[-1,0]]` as an element of `SU(2)`.

DERIVED: `2` is the rank and `0`, `1` the entries, both carried from `kmat`. -/
noncomputable def k2 : SU 2 := ⟨kmat, kmat_mem⟩

theorem kmat_00 : kmat 0 0 = 0 := by simp [kmat]
theorem kmat_01 : kmat 0 1 = 1 := by simp [kmat]
theorem kmat_11 : kmat 1 1 = 0 := by simp [kmat]

/-- `SU(2)` is not commutative: `j2` and `k2` do not commute. The `(0,1)` entry of `j2·k2 = k2·j2`
would read `i = -i`. -/
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

/-- **Every central element of `SU(2)` is `±1`.** Commuting with `jmat` kills both off-diagonal
entries; commuting with `kmat` equates the diagonal entries; `det = 1` then squares the common
entry to `1`. -/
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

/-- Conversely `±1` are central. -/
theorem mem_center_of_coe_eq_one_or_neg_one {A : SU 2}
    (h : (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    A ∈ Subgroup.center (SU 2) := by
  refine Subgroup.mem_center_iff.mpr (fun g => Subtype.val_injective ?_)
  show (g : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ)
      = (A : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
  rcases h with h | h <;> rw [h] <;> simp

/-- **The centre of `SU(2)` is exactly `{1, -1}` — the group `Z₂`.** This is the concrete case of the
general fact that the centre of `SU(N)` is the group of `N`-th roots of unity, scalar-embedded. -/
theorem mem_center_SU_two_iff {A : SU 2} :
    A ∈ Subgroup.center (SU 2) ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1 :=
  ⟨coe_eq_one_or_neg_one_of_mem_center, mem_center_of_coe_eq_one_or_neg_one⟩

/-- The nontrivial centre element `-1 ∈ SU(2)`.

DERIVED: `2` is the rank; `1` is the identity matrix this negates. `-1` is in `SU(2)` because
`det(-I) = (-1)^2 = 1`, which is exactly why the centre is nontrivial at even rank. -/
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

/-- **`SU(2)` is not simple as an abstract group.** Its centre is normal, contains `-1 ≠ 1` so it is
not `⊥`, and is not `⊤` because `j2` and `k2` do not commute. So formalising Clay's "simple" as
`IsSimpleGroup` would state something FALSE about the gauge group. -/
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

/-- `SU(1)` is the trivial group: the determinant condition pins its single entry to `1`. -/
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

/-- **`SU(1)` is not a simple group** — `IsSimpleGroup` extends `Nontrivial`, and `SU(1)` is
trivial. -/
theorem not_isSimpleGroup_SU_one : ¬ IsSimpleGroup (SU 1) := by
  intro hs
  haveI := hs
  haveI := subsingleton_SU_one
  obtain ⟨a, b, hab⟩ := exists_pair_ne (SU 1)
  exact hab (Subsingleton.elim a b)

/-! ## 4. The Clay hypothesis, named — and shown not to be consumed -/

/-- **The gauge-group hypothesis of Clay row A1, in the abstract-group reading**: `G` is a compact
topological group which is simple. Named so that the two facts below can say precisely what fails.

This is not the reading Clay intends — "simple" there is simplicity of the Lie algebra `su(N)` — but
it is the reading an `IsSimpleGroup` formalisation would commit to, and
`not_isCompactSimpleGauge_SU_two` shows that reading to be false for the gauge group this
development uses. -/
def IsCompactSimpleGauge (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  CompactSpace G ∧ IsSimpleGroup G

theorem not_isCompactSimpleGauge_SU_two : ¬ IsCompactSimpleGauge (SU 2) :=
  fun h => not_isSimpleGroup_SU_two h.2

theorem not_isCompactSimpleGauge_SU_one : ¬ IsCompactSimpleGauge (SU 1) :=
  fun h => not_isSimpleGroup_SU_one h.2

/-- **Simplicity is orthogonal to A1's Haar machinery.** The Osterwalder–Schrader invariance derived
in `CompactGauge.expect_invariant_haar` is available here with `¬ IsSimpleGroup G` in hand and
unused: the proof term is that invariance theorem applied unchanged. Whatever the Clay row's
simplicity clause is for, it is not feeding the compactness/Haar derivation. -/
theorem expect_invariant_haar_of_not_isSimpleGroup (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    (_hns : ¬ IsSimpleGroup G) {sys : MassGap.LatticeGauge.System G}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar G) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar G) β O :=
  MassGap.CompactGauge.expect_invariant_haar G sym β O

/-- The hypothesis class of `expect_invariant_haar_of_not_isSimpleGroup` is inhabited by the trivial
gauge group `SU(1)`: compact, Haar-carrying, and not simple. -/
theorem su_one_expect_invariant {sys : MassGap.LatticeGauge.System (SU 1)}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar (SU 1)) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar (SU 1)) β O :=
  expect_invariant_haar_of_not_isSimpleGroup (SU 1) not_isSimpleGroup_SU_one sym β O

/-- And by `SU(2)`, which carries a `Z₂` centre and is therefore not simple. -/
theorem su_two_expect_invariant {sys : MassGap.LatticeGauge.System (SU 2)}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar (SU 2)) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar (SU 2)) β O :=
  expect_invariant_haar_of_not_isSimpleGroup (SU 2) not_isSimpleGroup_SU_two sym β O

/-! ## What is missing for the Lie-simplicity reading

Mathlib v4.31 carries `LieAlgebra.IsSimple` (`Mathlib/Algebra/Lie/Semisimple/Defs.lean`) and the
classical matrix Lie algebras `sl`, `so`, `sp` (`Mathlib/Algebra/Lie/Classical.lean`), but

* it defines no compact real form `su n`, and
* it proves no classical Lie algebra simple — `Classical.lean` contains no occurrence of `IsSimple`
  at all, and the only concrete simple objects in the library are `alternatingGroup (Fin 5)` and the
  cyclic groups of prime order.

It also provides no Lie algebra of a matrix group: `Matrix.specialUnitaryGroup`
(`Mathlib/LinearAlgebra/UnitaryGroup.lean`) carries only `Group`, `StarMul`, `Inv` and
`mem_specialUnitaryGroup_iff`. So "the Lie algebra of `SU(N)` is simple" cannot be stated against the
library as it stands, let alone proved; it needs `su n` defined as a real Lie subalgebra of
`Matrix (Fin n) (Fin n) ℂ`, the correspondence to the group, and a simplicity proof by root data.

Mathlib does compute the centre of `SpecialLinearGroup` (`SpecialLinearGroup.mem_center_iff`), but by
commuting with transvections, which are not special-unitary — so that proof does not transfer, and
the `SU(2)` centre above is proved here from scratch. The general-`N` upper bound
`Subgroup.center (SU N) ≤ scalars` is not proved in this file; only the inclusion `⊇` is
(`mem_center_of_coe_smul_one`), which is what the non-simplicity argument needs. -/

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
