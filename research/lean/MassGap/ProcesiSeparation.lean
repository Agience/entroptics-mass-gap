import Mathlib
import MassGap.LoopsGenerateN

/-!
# MassGap.ProcesiSeparation — loop traces separate the gauge orbits of an `SU(N)` slice

`LoopsGenerateN.TracesSeparateN N n i` asks that two slice configurations with the same complex trace
`tr hol_C` on every loop be gauge related. This module proves it at every `N ≠ 0` and every `n`
(**`tracesSeparateN_all`**), so `LoopsGenerateN.excited_mem_closure_wordsN` holds with no separation
hypothesis (**`excited_mem_closure_words_all`**).

## 1. Spectral projections (proved)

For a Hermitian `H` and a real `t`, `eproj hH t = U D_t Uᴴ` with `U` the eigenvector unitary and `D_t` the
indicator of the eigenvalue `t`. `eproj_herm`, `eproj_idem`, `mul_eproj` (`H E = t E`), `eproj_mul_of`
(`H Y = t Y ⇒ E Y = Y`), `one_le_re_trace_eproj` (at an eigenvalue `t`, `Re tr E ≥ 1`), **`comm_eproj`**: a
matrix commuting with `H` commutes with `E`.

## 2. Trace-matched `*`-algebras of pairs (proved)

`TrStar V`: a subspace `V` of pairs of `N × N` matrices containing `1`, closed under products and adjoints,
on which `tr x₁ = tr x₂`. `Intw V T`: `x₂ T = T x₁` for every `x ∈ V`. `intw_adj` (`Tᴴ x₂ = x₁ Tᴴ`),
`faithful` (`x₁ = 0 ⇒ x₂ = 0`), the trace form `tf` (`tr (x₁ y₁)`) and `tf_nondeg`.

## 3. Intertwiners from the Casimir element (proved)

With a basis `e_j` of `V` and the `tf`-dual basis `f_j`, `cas Y = Σ_j (e_j)₂ Y (f_j)₁`. **`cas_intw`**: `cas Y`
intertwines for every `Y` (associativity of `tf`). `sum_trace_single`
(`Σ_{p,q} tr (X E_pq Y E_qp) = tr X tr Y`). **`exists_cas_ne`**: for Hermitian idempotent `P` and idempotent
`Q` commuting with the first and second components, with `tr (P x₁) = tr (Q x₂)` on `V` and `P ≠ 0`, some
`S = cas (Q E_pq P)` is a non-zero intertwiner with `Q S P = S` (the `tf`-Riesz vector `z` of `x ↦ tr (P x₁)`
is self-adjoint, so `Σ_{p,q} tr (S_pq E_qp) = tr (z₁ᴴ z₁) ≠ 0`).

## 4. A unitary intertwiner (proved)

`PIso W` (`WᴴW` idempotent), `piso_left`. **`step`**: an intertwining partial isometry `W` with `WᴴW ≠ 1`
extends to one with `Re tr (W'ᴴW')` at least one larger (`P = 1 − WᴴW`, `Q = 1 − WWᴴ`, `S` from
`exists_cas_ne`, `E` the spectral projection of `SᴴS` at a non-zero eigenvalue `t`, `W' = W + t^{-1/2} S E`).
**`exists_unitary_intw`**: on a `TrStar` subspace some `U` with `UᴴU = 1` intertwines.

## 5. `SU(N)` tuples (proved)

`word w A` (the ordered product of letters and inverses). **`su_conj_of_traces`**: families `A`, `B` in
`SU(N)` (`N ≠ 0`) with `tr word w A = tr word w B` for every word are simultaneously conjugate in `SU(N)`
(the star-algebra the pairs `(A_k, B_k)` generate is `TrStar`; the unitary intertwiner is rescaled by an
`N`-th root of `det⁻¹`).

## 6. The slice (proved)

`whN_append`, `whN_rev`, `pathHolN`, `holN_linkLoop` (the `SU(N)` form of `LoopsGenerate.linkLoop_hol`),
`stepsOf`, `wordLoop` (the loop at `y₀` that runs the link loops of a word), `holN_wordLoop`.
**`tracesSeparate_slice`**: on any slice, equal loop traces give `V' = gact h V` with
`h(z) = P_{V'}(z)⁻¹ G P_V(z)`. **`tracesSeparateN_all`**, **`excited_mem_closure_words_all`**.

DERIVED (module-wide): `1` the unit, the matrix-unit entry and the increment of `Re tr` per step; `0` the
zero matrix; `N + 1` the step count that exceeds `Re tr 1 = N`; `t^{-1/2}` makes `(t^{-1/2})² t = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ProcesiSeparation

open Matrix
open scoped ComplexOrder

/-- The `N × N` complex matrices. -/
abbrev Mat (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℂ

variable {N : ℕ}

/-! ## 1. Spectral projections of a Hermitian matrix -/

section Eigen

variable {H : Mat N} (hH : H.IsHermitian) (t : ℝ)

/-- The indicator of the eigenvalue `t` on the eigenvalue index. -/
def eind : Fin N → ℂ := fun i => if hH.eigenvalues i = t then 1 else 0

/-- **The spectral projection** of `H` at `t`: `U D_t Uᴴ`. -/
def eproj : Mat N :=
  (hH.eigenvectorUnitary : Mat N) * diagonal (eind hH t) * (hH.eigenvectorUnitary : Mat N)ᴴ

theorem eU_star_mul :
    (hH.eigenvectorUnitary : Mat N)ᴴ * (hH.eigenvectorUnitary : Mat N) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2

theorem eU_mul_star :
    (hH.eigenvectorUnitary : Mat N) * (hH.eigenvectorUnitary : Mat N)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2

theorem spec : H = (hH.eigenvectorUnitary : Mat N) * diagonal (fun i => (hH.eigenvalues i : ℂ))
    * (hH.eigenvectorUnitary : Mat N)ᴴ := by
  have h := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

theorem eind_mul_self (i : Fin N) : eind hH t i * eind hH t i = eind hH t i := by
  unfold eind; split_ifs <;> simp

theorem eproj_herm : (eproj hH t)ᴴ = eproj hH t := by
  unfold eproj
  have hd : star (eind hH t) = eind hH t := by
    funext i
    unfold eind
    split_ifs with h <;> simp [h]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, hd,
    ← mul_assoc]

theorem eproj_idem : eproj hH t * eproj hH t = eproj hH t := by
  unfold eproj
  have h := eU_star_mul hH
  calc (hH.eigenvectorUnitary : Mat N) * diagonal (eind hH t) * (hH.eigenvectorUnitary : Mat N)ᴴ
        * ((hH.eigenvectorUnitary : Mat N) * diagonal (eind hH t) * (hH.eigenvectorUnitary : Mat N)ᴴ)
      = (hH.eigenvectorUnitary : Mat N) * (diagonal (eind hH t)
          * ((hH.eigenvectorUnitary : Mat N)ᴴ * (hH.eigenvectorUnitary : Mat N))
          * diagonal (eind hH t)) * (hH.eigenvectorUnitary : Mat N)ᴴ := by simp only [mul_assoc]
    _ = _ := by
        rw [h, mul_one, diagonal_mul_diagonal,
          show (fun i => eind hH t i * eind hH t i) = eind hH t from funext (eind_mul_self hH t)]

/-- `H E = t E`. -/
theorem mul_eproj : H * eproj hH t = (t : ℂ) • eproj hH t := by
  have hs := spec hH
  have hd : diagonal (fun i => (hH.eigenvalues i : ℂ)) * diagonal (eind hH t)
      = (t : ℂ) • diagonal (eind hH t) := by
    rw [diagonal_mul_diagonal]
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      simp only [diagonal_apply_eq]
      unfold eind
      split_ifs with h
      · rw [h]
      · simp
    · rw [diagonal_apply_ne _ hab, diagonal_apply_ne _ hab, mul_zero]
  calc H * eproj hH t
      = (hH.eigenvectorUnitary : Mat N) * diagonal (fun i => (hH.eigenvalues i : ℂ))
          * (hH.eigenvectorUnitary : Mat N)ᴴ * eproj hH t := congrArg (· * eproj hH t) hs
    _ = (hH.eigenvectorUnitary : Mat N) * (diagonal (fun i => (hH.eigenvalues i : ℂ))
          * ((hH.eigenvectorUnitary : Mat N)ᴴ * (hH.eigenvectorUnitary : Mat N))
          * diagonal (eind hH t)) * (hH.eigenvectorUnitary : Mat N)ᴴ := by
        unfold eproj; simp only [mul_assoc]
    _ = (t : ℂ) • eproj hH t := by
        rw [eU_star_mul, mul_one, hd, Matrix.mul_smul, Matrix.smul_mul]
        rfl

/-- Every matrix whose columns lie in the `t`-eigenspace is fixed by `E`. -/
theorem eproj_mul_of (Y : Mat N) (hY : H * Y = (t : ℂ) • Y) : eproj hH t * Y = Y := by
  have hs := spec hH
  have h1 := eU_star_mul hH
  have h2 := eU_mul_star hH
  have hZ : diagonal (fun i => (hH.eigenvalues i : ℂ)) * ((hH.eigenvectorUnitary : Mat N)ᴴ * Y)
      = (t : ℂ) • ((hH.eigenvectorUnitary : Mat N)ᴴ * Y) := by
    have e : (hH.eigenvectorUnitary : Mat N)ᴴ * (H * Y)
        = (hH.eigenvectorUnitary : Mat N)ᴴ * ((t : ℂ) • Y) := by rw [hY]
    rw [Matrix.mul_smul] at e
    rw [← e]
    calc diagonal (fun i => (hH.eigenvalues i : ℂ)) * ((hH.eigenvectorUnitary : Mat N)ᴴ * Y)
        = (hH.eigenvectorUnitary : Mat N)ᴴ * ((hH.eigenvectorUnitary : Mat N)
            * diagonal (fun i => (hH.eigenvalues i : ℂ)) * (hH.eigenvectorUnitary : Mat N)ᴴ * Y) := by
          simp only [← mul_assoc, h1, one_mul]
      _ = (hH.eigenvectorUnitary : Mat N)ᴴ * (H * Y) := by rw [← hs]
  have hDZ : diagonal (eind hH t) * ((hH.eigenvectorUnitary : Mat N)ᴴ * Y)
      = (hH.eigenvectorUnitary : Mat N)ᴴ * Y := by
    ext a b
    have hab := congrFun (congrFun hZ a) b
    simp only [diagonal_mul, Matrix.smul_apply, smul_eq_mul] at hab ⊢
    unfold eind
    split_ifs with h
    · simp
    · have h0 : ((hH.eigenvalues a : ℂ) - t) * ((hH.eigenvectorUnitary : Mat N)ᴴ * Y) a b = 0 := by
        rw [sub_mul, hab, sub_self]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h') h
      · rw [h', mul_zero]
  calc eproj hH t * Y
      = (hH.eigenvectorUnitary : Mat N)
          * (diagonal (eind hH t) * ((hH.eigenvectorUnitary : Mat N)ᴴ * Y)) := by
        unfold eproj; simp only [mul_assoc]
    _ = Y := by rw [hDZ, ← mul_assoc, h2, one_mul]

theorem trace_eproj : trace (eproj hH t) = ∑ i, eind hH t i := by
  unfold eproj
  rw [trace_mul_comm, ← mul_assoc, eU_star_mul, one_mul, trace_diagonal]

/-- At an eigenvalue `t`, `Re tr E ≥ 1`. -/
theorem one_le_re_trace_eproj {i₀ : Fin N} (h : hH.eigenvalues i₀ = t) :
    1 ≤ (trace (eproj hH t)).re := by
  rw [trace_eproj, Complex.re_sum]
  have hnn : ∀ i, 0 ≤ (eind hH t i).re := fun i => by unfold eind; split_ifs <;> simp
  calc (1 : ℝ) = (eind hH t i₀).re := by simp [eind, h]
    _ ≤ ∑ i, (eind hH t i).re := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i₀)

/-- **A matrix commuting with `H` commutes with its spectral projections.** -/
theorem comm_eproj {X : Mat N} (hX : X * H = H * X) : X * eproj hH t = eproj hH t * X := by
  have hXa : Xᴴ * H = H * Xᴴ := by
    have e := congrArg conjTranspose hX
    rw [conjTranspose_mul, conjTranspose_mul, hH.eq] at e
    exact e.symm
  have k1 : eproj hH t * (X * eproj hH t) = X * eproj hH t :=
    eproj_mul_of hH t _ (by rw [← mul_assoc, ← hX, mul_assoc, mul_eproj, Matrix.mul_smul])
  have k2 : eproj hH t * (Xᴴ * eproj hH t) = Xᴴ * eproj hH t :=
    eproj_mul_of hH t _ (by rw [← mul_assoc, ← hXa, mul_assoc, mul_eproj, Matrix.mul_smul])
  have k3 := congrArg conjTranspose k2
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, eproj_herm] at k3
  rw [← k1, ← mul_assoc, k3]

end Eigen

/-! ## 2. Trace-matched `*`-algebras of pairs -/

section Alg

/-- A subspace of pairs of matrices containing `1`, closed under products and adjoints, on which the
two traces agree. -/
structure TrStar (V : Submodule ℂ (Mat N × Mat N)) : Prop where
  one_mem : (1 : Mat N × Mat N) ∈ V
  mul_mem : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V
  star_mem : ∀ x ∈ V, star x ∈ V
  tr : ∀ x ∈ V, trace x.1 = trace x.2

/-- `T` intertwines the two components of `V`: `x₂ T = T x₁`. -/
def Intw (V : Submodule ℂ (Mat N × Mat N)) (T : Mat N) : Prop := ∀ x ∈ V, x.2 * T = T * x.1

variable {V : Submodule ℂ (Mat N × Mat N)} (hV : TrStar V)
include hV

theorem intw_adj {T : Mat N} (hT : Intw V T) {x : Mat N × Mat N} (hx : x ∈ V) :
    Tᴴ * x.2 = x.1 * Tᴴ := by
  have h := congrArg conjTranspose (hT _ (hV.star_mem _ hx))
  simpa only [Prod.snd_star, Prod.fst_star, star_eq_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose] using h

/-- **The second component vanishes with the first.** -/
theorem faithful {x : Mat N × Mat N} (hx : x ∈ V) (h : x.1 = 0) : x.2 = 0 := by
  have h2 := hV.tr _ (hV.mul_mem _ hx _ (hV.star_mem _ hx))
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_star, Prod.snd_star, h, zero_mul, trace_zero,
    star_eq_conjTranspose] at h2
  exact trace_mul_conjTranspose_self_eq_zero_iff.mp h2.symm

omit hV in
variable (V) in
/-- The trace form `(x, y) ↦ tr (x₁ y₁)` on `V`. -/
def tf : LinearMap.BilinForm ℂ V :=
  LinearMap.mk₂ ℂ (fun x y => trace ((x : Mat N × Mat N).1 * (y : Mat N × Mat N).1))
    (fun a b c => by simp [Matrix.add_mul, trace_add])
    (fun r a b => by simp [trace_smul])
    (fun a b c => by simp [Matrix.mul_add, trace_add])
    (fun r a b => by simp [trace_smul])

omit hV in
theorem tf_apply (x y : V) : tf V x y = trace ((x : Mat N × Mat N).1 * (y : Mat N × Mat N).1) := rfl

theorem tf_nondeg : (tf V).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h := hx ⟨star (x : Mat N × Mat N), hV.star_mem _ x.2⟩
    rw [tf_apply] at h
    simp only [Prod.fst_star, star_eq_conjTranspose] at h
    have h1 : (x : Mat N × Mat N).1 = 0 := trace_mul_conjTranspose_self_eq_zero_iff.mp h
    have h2 := faithful hV x.2 h1
    apply Subtype.ext
    exact Prod.ext h1 h2
  · have h := hy ⟨star (y : Mat N × Mat N), hV.star_mem _ y.2⟩
    rw [tf_apply] at h
    simp only [Prod.fst_star, star_eq_conjTranspose] at h
    have h1 : (y : Mat N × Mat N).1 = 0 := trace_conjTranspose_mul_self_eq_zero_iff.mp h
    have h2 := faithful hV y.2 h1
    apply Subtype.ext
    exact Prod.ext h1 h2

end Alg

/-! ## 3. Intertwiners from the Casimir element -/

section Casimir

variable {V : Submodule ℂ (Mat N × Mat N)}

variable (V) in
/-- The basis vectors as pairs. -/
def eB (j : Fin (Module.finrank ℂ V)) : Mat N × Mat N := ((Module.finBasis ℂ V j : V) : Mat N × Mat N)

variable (V) in
theorem eB_mem (j : Fin (Module.finrank ℂ V)) : eB V j ∈ V := (Module.finBasis ℂ V j).2

/-- `Σ_{p,q} tr (X E_pq Y E_qp) = tr X tr Y`. -/
theorem sum_trace_single (X Y : Mat N) :
    ∑ p, ∑ q, trace (X * single p q (1 : ℂ) * Y * single q p 1) = trace X * trace Y := by
  have h : ∀ p q, trace (X * single p q (1 : ℂ) * Y * single q p 1) = X p p * Y q q := by
    intro p q
    rw [trace_mul_comm, ← mul_assoc, ← mul_assoc, single_mul_mul_single, trace_single_mul]
    simp
  simp only [h]
  rw [trace, trace, Finset.sum_mul_sum]
  rfl

variable (hV : TrStar V)
include hV

/-- The `tf`-dual basis of `Module.finBasis ℂ V`. -/
abbrev dB : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V :=
  (tf V).dualBasis (tf_nondeg hV) (Module.finBasis ℂ V)

/-- The dual basis vectors as pairs. -/
def fB (j : Fin (Module.finrank ℂ V)) : Mat N × Mat N := ((dB hV j : V) : Mat N × Mat N)

theorem fB_mem (j : Fin (Module.finrank ℂ V)) : fB hV j ∈ V := (dB hV j).2

theorem repr_eq (x : V) (j : Fin (Module.finrank ℂ V)) :
    (Module.finBasis ℂ V).repr x j = tf V (dB hV j) x := by
  conv_rhs => rw [← (Module.finBasis ℂ V).sum_repr x]
  simp only [map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Expansion in the basis, with `tf`-dual coefficients. -/
theorem coe_exp (x : V) :
    (x : Mat N × Mat N) = ∑ k, trace ((fB hV k).1 * (x : Mat N × Mat N).1) • eB V k := by
  conv_lhs => rw [← (Module.finBasis ℂ V).sum_repr x]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, repr_eq hV]
  rfl

/-- Expansion in the dual basis. -/
theorem coe_exp_d (y : V) :
    (y : Mat N × Mat N) = ∑ k, trace ((y : Mat N × Mat N).1 * (eB V k).1) • fB hV k := by
  conv_lhs => rw [← (dB hV).sum_repr y]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply]
  rfl

/-- **The Casimir map** `Y ↦ Σ_j (e_j)₂ Y (f_j)₁`. -/
def cas (Y : Mat N) : Mat N := ∑ j, (eB V j).2 * Y * (fB hV j).1

/-- **`cas Y` intertwines** for every `Y`. -/
theorem cas_intw (Y : Mat N) : Intw V (cas hV Y) := by
  intro x hx
  have hL : ∀ j, x * eB V j = ∑ k, trace ((fB hV k).1 * (x * eB V j).1) • eB V k := fun j =>
    coe_exp hV ⟨x * eB V j, hV.mul_mem _ hx _ (eB_mem V j)⟩
  have hR : ∀ k, fB hV k * x = ∑ j, trace ((fB hV k * x).1 * (eB V j).1) • fB hV j := fun k =>
    coe_exp_d hV ⟨fB hV k * x, hV.mul_mem _ (fB_mem hV k) _ hx⟩
  unfold cas
  rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ j, x.2 * ((eB V j).2 * Y * (fB hV j).1)
      = ∑ j, (x * eB V j).2 * Y * (fB hV j).1 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Prod.snd_mul, mul_assoc]
    _ = ∑ j, ∑ k, trace ((fB hV k).1 * (x * eB V j).1) • ((eB V k).2 * Y * (fB hV j).1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [hL j]
        simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_mul, Matrix.smul_mul]
    _ = ∑ k, ∑ j, trace ((fB hV k * x).1 * (eB V j).1) • ((eB V k).2 * Y * (fB hV j).1) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [Prod.fst_mul, mul_assoc]
    _ = ∑ k, (eB V k).2 * Y * (fB hV k * x).1 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_rhs => rw [hR k]
        simp only [Prod.fst_sum, Prod.smul_fst, Finset.mul_sum, Matrix.mul_smul]
    _ = ∑ k, (eB V k).2 * Y * (fB hV k).1 * x.1 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Prod.fst_mul, mul_assoc]

/-- **A non-zero intertwiner between the corners `P` and `Q`.** -/
theorem exists_cas_ne {P Q : Mat N} (hPh : Pᴴ = P) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hPc : ∀ x ∈ V, x.1 * P = P * x.1) (hQc : ∀ x ∈ V, x.2 * Q = Q * x.2)
    (hPQ : ∀ x ∈ V, trace (P * x.1) = trace (Q * x.2)) (hP0 : P ≠ 0) :
    ∃ S : Mat N, S ≠ 0 ∧ Intw V S ∧ Q * S * P = S := by
  set z : Mat N × Mat N := ∑ j, trace (P * (eB V j).1) • fB hV j with hz
  have hzV : z ∈ V := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (fB_mem hV j)
  have key : ∀ x ∈ V, trace (z.1 * x.1) = trace (P * x.1) := by
    intro x hx
    have hx' : x = ∑ k, trace ((fB hV k).1 * x.1) • eB V k := coe_exp hV ⟨x, hx⟩
    calc trace (z.1 * x.1) = ∑ j, trace (P * (eB V j).1) * trace ((fB hV j).1 * x.1) := by
          rw [hz, Prod.fst_sum, Finset.sum_mul, trace_sum]
          simp only [Prod.smul_fst, Matrix.smul_mul, trace_smul, smul_eq_mul]
      _ = trace (P * x.1) := by
          conv_rhs => rw [hx']
          rw [Prod.fst_sum, Finset.mul_sum, trace_sum]
          simp only [Prod.smul_fst, Matrix.mul_smul, trace_smul, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hsum : ∑ j, trace (P * (eB V j).1) * trace (P * (fB hV j).1) = trace (z.1 * z.1) := by
    rw [key z hzV, hz, Prod.fst_sum, Finset.mul_sum, trace_sum]
    simp only [Prod.smul_fst, Matrix.mul_smul, trace_smul, smul_eq_mul]
  have hzh : z.1ᴴ = z.1 := by
    have huV : star z - z ∈ V := Submodule.sub_mem _ (hV.star_mem _ hzV) hzV
    have hku : ∀ x ∈ V, trace ((star z - z).1 * x.1) = 0 := by
      intro x hx
      have h1 : trace (z.1ᴴ * x.1) = trace (P * x.1) := by
        have hsx := key (star x) (hV.star_mem _ hx)
        simp only [Prod.fst_star, star_eq_conjTranspose] at hsx
        calc trace (z.1ᴴ * x.1) = star (trace (z.1 * x.1ᴴ)) := by
              rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
              exact trace_mul_comm _ _
          _ = star (trace (P * x.1ᴴ)) := by rw [hsx]
          _ = trace (x.1 * P) := by
              rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, hPh]
          _ = trace (P * x.1) := trace_mul_comm _ _
      simp only [Prod.fst_sub, Prod.fst_star, star_eq_conjTranspose, Matrix.sub_mul, trace_sub, h1,
        key x hx, sub_self]
    have h0 := hku (star (star z - z)) (hV.star_mem _ huV)
    simp only [Prod.fst_star, star_eq_conjTranspose] at h0
    have hu0 : (star z - z).1 = 0 := trace_mul_conjTranspose_self_eq_zero_iff.mp h0
    simp only [Prod.fst_sub, Prod.fst_star, star_eq_conjTranspose] at hu0
    exact sub_eq_zero.mp hu0
  have hz0 : z.1 ≠ 0 := by
    intro h0
    have h1 := key 1 hV.one_mem
    rw [h0, zero_mul, trace_zero, Prod.fst_one, mul_one] at h1
    have h2 : trace (Pᴴ * P) = 0 := by rw [hPh, hPP]; exact h1.symm
    exact hP0 (trace_conjTranspose_mul_self_eq_zero_iff.mp h2)
  have hne : ∑ j, trace (P * (eB V j).1) * trace (P * (fB hV j).1) ≠ 0 := by
    rw [hsum]
    have e : trace (z.1 * z.1) = trace (z.1ᴴ * z.1) := by rw [hzh]
    rw [e]
    exact fun h => hz0 (trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  have hj : ∀ j, ∑ p, ∑ q, trace ((eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1
      * single q p 1) = trace (P * (eB V j).1) * trace (P * (fB hV j).1) := by
    intro j
    have e : ∀ p q, (eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1 * single q p 1
        = (eB V j).2 * Q * single p q 1 * (P * (fB hV j).1) * single q p 1 := by
      intro p q; simp only [mul_assoc]
    simp only [e]
    rw [sum_trace_single, trace_mul_comm, ← hPQ _ (eB_mem V j)]
  have hunits : ∑ p, ∑ q, trace (cas hV (Q * single p q (1 : ℂ) * P) * single q p 1)
      = ∑ j, trace (P * (eB V j).1) * trace (P * (fB hV j).1) := by
    unfold cas
    simp only [Finset.sum_mul, trace_sum]
    calc ∑ p, ∑ q, ∑ j, trace ((eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1
          * single q p 1)
        = ∑ p, ∑ j, ∑ q, trace ((eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1
          * single q p 1) := Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ j, ∑ p, ∑ q, trace ((eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1
          * single q p 1) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun j _ => hj j
  obtain ⟨p, q, hpq⟩ : ∃ p q, cas hV (Q * single p q (1 : ℂ) * P) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← hunits]
    simp [hcon]
  refine ⟨_, hpq, cas_intw hV _, ?_⟩
  unfold cas
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hQe : (eB V j).2 * Q = Q * (eB V j).2 := hQc _ (eB_mem V j)
  have hPf : (fB hV j).1 * P = P * (fB hV j).1 := hPc _ (fB_mem hV j)
  have h1 : Q * (eB V j).2 * Q = (eB V j).2 * Q := by rw [← hQe, mul_assoc, hQQ]
  have h2 : P * (fB hV j).1 * P = P * (fB hV j).1 := by rw [mul_assoc, hPf, ← mul_assoc, hPP]
  calc Q * ((eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1) * P
      = Q * (eB V j).2 * Q * single p q 1 * (P * (fB hV j).1 * P) := by simp only [mul_assoc]
    _ = (eB V j).2 * (Q * single p q (1 : ℂ) * P) * (fB hV j).1 := by
        rw [h1, h2]; simp only [mul_assoc]

end Casimir

/-! ## 4. A unitary intertwiner -/

section Unitary

/-- `W` is a partial isometry: `WᴴW` is idempotent. -/
def PIso (W : Mat N) : Prop := Wᴴ * W * (Wᴴ * W) = Wᴴ * W

theorem piso_left {W : Mat N} (h : PIso W) : W * (Wᴴ * W) = W := by
  unfold PIso at h
  have h0 : (W - W * (Wᴴ * W))ᴴ * (W - W * (Wᴴ * W)) = 0 := by
    have e : (W * (Wᴴ * W))ᴴ = Wᴴ * W * Wᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
    rw [conjTranspose_sub, e]
    simp only [sub_mul, mul_sub]
    have h1 : Wᴴ * (W * (Wᴴ * W)) = Wᴴ * W := by rw [← mul_assoc, h]
    have h2 : Wᴴ * W * Wᴴ * W = Wᴴ * W := by rw [mul_assoc (Wᴴ * W), h]
    have h3 : Wᴴ * W * Wᴴ * (W * (Wᴴ * W)) = Wᴴ * W := by rw [← mul_assoc, h2, h]
    rw [h1, h2, h3]
    abel
  exact (sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp h0)).symm

theorem piso_herm (W : Mat N) : (1 - Wᴴ * W)ᴴ = 1 - Wᴴ * W := by
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]

theorem piso_idem {W : Mat N} (h : PIso W) : (1 - Wᴴ * W) * (1 - Wᴴ * W) = 1 - Wᴴ * W := by
  unfold PIso at h
  simp only [sub_mul, mul_sub, one_mul, mul_one, h]
  abel

variable {V : Submodule ℂ (Mat N × Mat N)} (hV : TrStar V)
include hV

/-- **One step**: an intertwining partial isometry that is not unitary extends, with `Re tr (WᴴW)`
increased by at least one. -/
theorem step {W : Mat N} (hW : Intw V W) (hWp : PIso W) (h1 : Wᴴ * W ≠ 1) :
    ∃ W' : Mat N, Intw V W' ∧ PIso W' ∧ (trace (Wᴴ * W)).re + 1 ≤ (trace (W'ᴴ * W')).re := by
  have hl := piso_left hWp
  have hPh := piso_herm W
  have hPP := piso_idem hWp
  have hWW : W * Wᴴ * (W * Wᴴ) = W * Wᴴ := by rw [← mul_assoc, mul_assoc W Wᴴ W, hl]
  have hQQ : (1 - W * Wᴴ) * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hWW]
    abel
  have hWQ : Wᴴ * (1 - W * Wᴴ) = 0 := by
    have e : Wᴴ * (W * Wᴴ) = Wᴴ := by
      have := congrArg conjTranspose hl
      simpa only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc] using this
    rw [mul_sub, mul_one, e, sub_self]
  have hadj : ∀ x ∈ V, Wᴴ * x.2 = x.1 * Wᴴ := fun x hx => intw_adj hV hW hx
  have hPc : ∀ x ∈ V, x.1 * (1 - Wᴴ * W) = (1 - Wᴴ * W) * x.1 := by
    intro x hx
    have e : x.1 * (Wᴴ * W) = Wᴴ * W * x.1 := by
      rw [← mul_assoc, ← hadj x hx, mul_assoc, hW x hx, ← mul_assoc]
    rw [mul_sub, sub_mul, mul_one, one_mul, e]
  have hQc : ∀ x ∈ V, x.2 * (1 - W * Wᴴ) = (1 - W * Wᴴ) * x.2 := by
    intro x hx
    have e : x.2 * (W * Wᴴ) = W * Wᴴ * x.2 := by
      rw [← mul_assoc, hW x hx, mul_assoc, ← hadj x hx, ← mul_assoc]
    rw [mul_sub, sub_mul, mul_one, one_mul, e]
  have hPQ : ∀ x ∈ V, trace ((1 - Wᴴ * W) * x.1) = trace ((1 - W * Wᴴ) * x.2) := by
    intro x hx
    have e : trace (W * Wᴴ * x.2) = trace (Wᴴ * W * x.1) := by
      rw [mul_assoc, trace_mul_comm, hadj x hx, mul_assoc, trace_mul_comm]
    rw [sub_mul, sub_mul, one_mul, one_mul, trace_sub, trace_sub, hV.tr x hx, e]
  have hP0 : (1 - Wᴴ * W) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  obtain ⟨S, hS0, hSi, hQSP⟩ := exists_cas_ne hV hPh hPP hQQ hPc hQc hPQ hP0
  have hH : (Sᴴ * S).IsHermitian := isHermitian_conjTranspose_mul_self S
  have hH0 : Sᴴ * S ≠ 0 := fun h => hS0 (conjTranspose_mul_self_eq_zero.mp h)
  obtain ⟨i, hi⟩ : ∃ i, hH.eigenvalues i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hH0 (hH.eigenvalues_eq_zero_iff.mp (funext hall))
  set t := hH.eigenvalues i with ht
  have ht0 : 0 < t := lt_of_le_of_ne ((posSemidef_conjTranspose_mul_self S).eigenvalues_nonneg i)
    (Ne.symm hi)
  have hEc : ∀ x ∈ V, x.1 * eproj hH t = eproj hH t * x.1 := by
    intro x hx
    refine comm_eproj hH t ?_
    rw [← mul_assoc, ← intw_adj hV hSi hx, mul_assoc, hSi x hx, ← mul_assoc]
  have hSP : S * (1 - Wᴴ * W) = S := by
    conv_lhs => rw [← hQSP]
    rw [mul_assoc, hPP, hQSP]
  have hQS : (1 - W * Wᴴ) * S = S := by
    conv_lhs => rw [← hQSP]
    rw [← mul_assoc, ← mul_assoc, hQQ, hQSP]
  have hPS : (1 - Wᴴ * W) * Sᴴ = Sᴴ := by
    conv_rhs => rw [← hSP]
    rw [conjTranspose_mul, hPh]
  have hPE : (1 - Wᴴ * W) * eproj hH t = eproj hH t := by
    have k : (t : ℂ) • ((1 - Wᴴ * W) * eproj hH t) = (t : ℂ) • eproj hH t := by
      rw [← Matrix.mul_smul, ← mul_eproj hH t, ← mul_assoc, ← mul_assoc, hPS]
    exact smul_right_injective (Mat N) (by exact_mod_cast ht0.ne' : (t : ℂ) ≠ 0) k
  have hEP : eproj hH t * (1 - Wᴴ * W) = eproj hH t := by
    have := congrArg conjTranspose hPE
    rwa [conjTranspose_mul, hPh, eproj_herm] at this
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hcs : star c = c := by rw [hcdef]; exact Complex.conj_ofReal _
  have hct : star c * c * (t : ℂ) = 1 := by
    have hr : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt ht0.le, inv_mul_cancel₀ ht0.ne']
    rw [hcs, hcdef]
    exact_mod_cast hr
  set Vv : Mat N := c • (S * eproj hH t) with hVv
  have hVi : Intw V Vv := by
    intro x hx
    rw [hVv, Matrix.mul_smul, Matrix.smul_mul, ← mul_assoc, hSi x hx, mul_assoc, hEc x hx,
      mul_assoc]
  have hVV : Vvᴴ * Vv = eproj hH t := by
    have e : eproj hH t * Sᴴ * (S * eproj hH t) = (t : ℂ) • eproj hH t := by
      rw [mul_assoc, ← mul_assoc Sᴴ, mul_eproj, Matrix.mul_smul, eproj_idem]
    rw [hVv, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
      eproj_herm, e, smul_smul, hct, one_smul]
  have hWS : Wᴴ * S = 0 := by rw [← hQS, ← mul_assoc, hWQ, zero_mul]
  have hWV : Wᴴ * Vv = 0 := by
    rw [hVv, Matrix.mul_smul, ← mul_assoc, hWS, zero_mul, smul_zero]
  have hVW : Vvᴴ * W = 0 := by
    have := congrArg conjTranspose hWV
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
  have hRE : Wᴴ * W * eproj hH t = 0 := by
    have e : Wᴴ * W * eproj hH t = eproj hH t - (1 - Wᴴ * W) * eproj hH t := by
      rw [sub_mul, one_mul, sub_sub_cancel]
    rw [e, hPE, sub_self]
  have hER : eproj hH t * (Wᴴ * W) = 0 := by
    have e : eproj hH t * (Wᴴ * W) = eproj hH t - eproj hH t * (1 - Wᴴ * W) := by
      rw [mul_sub, mul_one, sub_sub_cancel]
    rw [e, hEP, sub_self]
  have hsum : (W + Vv)ᴴ * (W + Vv) = Wᴴ * W + eproj hH t := by
    rw [conjTranspose_add, add_mul, mul_add, mul_add, hWV, hVW, hVV, add_zero, zero_add]
  refine ⟨W + Vv, fun x hx => ?_, ?_, ?_⟩
  · rw [mul_add, add_mul, hW x hx, hVi x hx]
  · unfold PIso
    unfold PIso at hWp
    rw [hsum, add_mul, mul_add, mul_add, hWp, hRE, hER, eproj_idem, add_zero, zero_add]
  · rw [hsum, trace_add, Complex.add_re]
    linarith [one_le_re_trace_eproj hH t ht.symm]

/-- **A unitary intertwiner.** On a `TrStar` subspace some `U` with `UᴴU = 1` has `x₂ U = U x₁` for every
`x`. -/
theorem exists_unitary_intw : ∃ U : Mat N, Uᴴ * U = 1 ∧ Intw V U := by
  have key : ∀ k : ℕ, ∃ W : Mat N, Intw V W ∧ PIso W ∧
      (Wᴴ * W = 1 ∨ (k : ℝ) ≤ (trace (Wᴴ * W)).re) := by
    intro k
    induction k with
    | zero => exact ⟨0, fun x _ => by simp, by simp [PIso], Or.inr (by simp)⟩
    | succ k ih =>
        obtain ⟨W, hW, hWp, hk⟩ := ih
        by_cases h1 : Wᴴ * W = 1
        · exact ⟨W, hW, hWp, Or.inl h1⟩
        · obtain ⟨W', hW', hW'p, htr⟩ := step hV hW hWp h1
          refine ⟨W', hW', hW'p, Or.inr ?_⟩
          have := hk.resolve_left h1
          push_cast
          linarith
  obtain ⟨W, hW, hWp, hk⟩ := key (N + 1)
  refine ⟨W, ?_, hW⟩
  by_contra h1
  have hk' := hk.resolve_left h1
  have hnn : 0 ≤ (trace (1 - Wᴴ * W)).re := by
    have e : (1 - Wᴴ * W)ᴴ * (1 - Wᴴ * W) = 1 - Wᴴ * W := by rw [piso_herm, piso_idem hWp]
    have := (posSemidef_conjTranspose_mul_self (1 - Wᴴ * W)).trace_nonneg
    rw [e] at this
    exact (Complex.nonneg_iff.mp this).1
  rw [trace_sub, trace_one, Complex.sub_re] at hnn
  simp only [Fintype.card_fin, Complex.natCast_re] at hnn
  push_cast at hk'
  linarith

end Unitary

/-! ## 5. `SU(N)` tuples with equal word traces -/

section SU

/-- The ordered product of a word of letters (`true`) and inverse letters (`false`). -/
def word {κ : Type*} (w : List (κ × Bool)) (A : κ → SUN.SU N) : SUN.SU N :=
  (w.map fun c => if c.2 then A c.1 else (A c.1)⁻¹).prod

theorem word_append {κ : Type*} (w w' : List (κ × Bool)) (A : κ → SUN.SU N) :
    word (w ++ w') A = word w A * word w' A := by
  simp [word]

/-- **Procesi's separation for unitary tuples.** Families in `SU(N)` with the same complex trace on every
word are simultaneously conjugate in `SU(N)`. -/
theorem su_conj_of_traces [NeZero N] {κ : Type*} (A B : κ → SUN.SU N)
    (h : ∀ w : List (κ × Bool), trace (word w A : Mat N) = trace (word w B : Mat N)) :
    ∃ G : SUN.SU N, ∀ k, B k = G * A k * G⁻¹ := by
  classical
  set S : Set (Mat N × Mat N) := Set.range fun k => ((A k : Mat N), (B k : Mat N)) with hS
  set V : Submodule ℂ (Mat N × Mat N) :=
    Subalgebra.toSubmodule (StarAlgebra.adjoin ℂ S).toSubalgebra with hVdef
  have hwords : ∀ x ∈ Submonoid.closure (S ∪ star S),
      ∃ w : List (κ × Bool), x = ((word w A : Mat N), (word w B : Mat N)) := by
    intro x hx
    let M : Submonoid (Mat N × Mat N) :=
      { carrier := {x | ∃ w : List (κ × Bool), x = ((word w A : Mat N), (word w B : Mat N))}
        mul_mem' := by
          rintro a b ⟨w, rfl⟩ ⟨w', rfl⟩
          exact ⟨w ++ w', by simp [word_append]⟩
        one_mem' := ⟨[], Prod.ext (by simp [word]) (by simp [word])⟩ }
    refine (Submonoid.closure_le (S := M)).mpr ?_ hx
    rintro y (⟨k, rfl⟩ | hy)
    · exact ⟨[(k, true)], by simp [word]⟩
    · obtain ⟨k, hk⟩ := Set.mem_star.mp hy
      refine ⟨[(k, false)], ?_⟩
      have hk' : ((A k : Mat N), (B k : Mat N)) = star y := hk
      have e : y = star ((A k : Mat N), (B k : Mat N)) := by rw [hk', star_star]
      rw [e]
      simp [word]
      rfl
  have htr : ∀ x ∈ V, trace x.1 = trace x.2 := by
    intro x hx
    have hx' : x ∈ Submodule.span ℂ (Submonoid.closure (S ∪ star S) : Set (Mat N × Mat N)) := by
      rw [← Algebra.adjoin_eq_span, ← StarAlgebra.adjoin_toSubalgebra]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨w, rfl⟩ := hwords y hy
        exact h w
    | zero => simp
    | add y z _ _ hy hz => simp [trace_add, hy, hz]
    | smul a y _ hy => simp [trace_smul, hy]
  have hV : TrStar V :=
    ⟨Subalgebra.one_mem (StarAlgebra.adjoin ℂ S).toSubalgebra,
      fun x hx y hy => Subalgebra.mul_mem (StarAlgebra.adjoin ℂ S).toSubalgebra hx hy,
      fun x hx => (star_mem (hx : x ∈ StarAlgebra.adjoin ℂ S) : star x ∈ StarAlgebra.adjoin ℂ S), htr⟩
  obtain ⟨U, hU1, hUi⟩ := exists_unitary_intw hV
  have hUk : ∀ k, (B k : Mat N) * U = U * (A k : Mat N) := fun k =>
    hUi _ (StarAlgebra.subset_adjoin ℂ S ⟨k, rfl⟩)
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU1
  have hdet : star (det U) * det U = 1 := by
    have := congrArg det hU1
    rwa [det_mul, det_conjTranspose, det_one] at this
  have hn1 : ‖det U‖ = 1 := by
    have h2 : (Complex.normSq (det U) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact hdet
    have h3 : Complex.normSq (det U) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (det U)⁻¹ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hcn : ‖c‖ = 1 := by
    have : ‖c‖ ^ N = 1 := by rw [← norm_pow, hc, norm_inv, hn1, inv_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).mp this
  have hcc : c * star c = 1 := by
    have : (starRingEnd ℂ) c * c = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hcn]
      simp
    rw [mul_comm]
    exact this
  have hdet0 : det U ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  have hGmem : c • U ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_eq_conjTranspose, hU2, hcc,
        one_smul]
    · rw [det_smul, Fintype.card_fin, hc, inv_mul_cancel₀ hdet0]
  refine ⟨⟨c • U, hGmem⟩, fun k => Subtype.ext ?_⟩
  show (B k : Mat N) = c • U * (A k : Mat N) * star (c • U)
  calc (B k : Mat N) = B k * (U * Uᴴ) := by rw [hU2, mul_one]
    _ = U * A k * Uᴴ := by rw [← mul_assoc, hUk k]
    _ = c • U * (A k : Mat N) * star (c • U) := by
        rw [star_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc, one_smul,
          star_eq_conjTranspose]

end SU

/-! ## 6. The slice -/

section Lattice

open MassGap.ElectricLoops (Loop Dir Step walk endpt rev next letter walk_append endpt_append
  endpt_rev rev_cons)
open MassGap.RectWilson (SpT TT tsh)
open MassGap.RunSeedN (whN holN)
open MassGap.LoopsGenerate (path endpt_path linkLoop)

variable {i : Fin 4} {T : Dir i → ℕ}

theorem whN_append (w w' : List (SpT i T × Bool)) (V : SpT i T → SUN.SU N) :
    whN (w ++ w') V = whN w V * whN w' V := by
  simp [whN]

theorem whN_letter_flip (y : TT i T) (a : Step i) (V : SpT i T → SUN.SU N) :
    whN [letter (next y a) (ElectricLoops.flip a)] V = (whN [letter y a] V)⁻¹ := by
  rcases a with ⟨ν, b⟩
  cases b
  · simp [whN, letter, next, ElectricLoops.flip]
  · simp [whN, letter, next, ElectricLoops.flip, ElectricLoops.tshInv_tsh]

/-- **The reversed path has the inverse holonomy** (`SU(N)`). -/
theorem whN_rev (y : TT i T) (s : List (Step i)) (V : SpT i T → SUN.SU N) :
    whN (walk (endpt y s) (rev s)) V = (whN (walk y s) V)⁻¹ := by
  induction s generalizing y with
  | nil => simp [whN, walk, rev, endpt]
  | cons a ss ih =>
      rw [rev_cons, walk_append]
      simp only [endpt]
      rw [whN_append, ih, endpt_rev]
      rw [show walk (next y a) [ElectricLoops.flip a] = [letter (next y a) (ElectricLoops.flip a)] from rfl, whN_letter_flip,
        show walk y (a :: ss) = [letter y a] ++ walk (next y a) ss from rfl, whN_append, _root_.mul_inv_rev]

/-- The `SU(N)` holonomy along the chosen path from `y₀` to `z`. -/
def pathHolN (y₀ z : TT i T) (V : SpT i T → SUN.SU N) : SUN.SU N := whN (walk y₀ (path y₀ z)) V

theorem holN_linkLoop (y₀ : TT i T) (l : SpT i T) (V : SpT i T → SUN.SU N) :
    holN (linkLoop y₀ l) V = pathHolN y₀ l.2 V * V l * (pathHolN y₀ (tsh i T l.1 l.2) V)⁻¹ := by
  unfold holN linkLoop pathHolN
  simp only
  rw [walk_append, walk_append, whN_append, whN_append, endpt_append, endpt_path]
  have hr := whN_rev y₀ (path y₀ (tsh i T l.1 l.2)) V
  rw [endpt_path] at hr
  have hm : whN (walk l.2 [(l.1, true)]) V = V l := by simp [walk, letter, whN]
  have he : endpt l.2 [(l.1, true)] = tsh i T l.1 l.2 := by simp [endpt, next]
  rw [hm, he, hr]

/-- The steps of the loop at `y₀` that runs the link loops of a word (reversed for an inverse letter). -/
def stepsOf (y₀ : TT i T) : List (SpT i T × Bool) → List (Step i)
  | [] => []
  | c :: w => (if c.2 then (linkLoop y₀ c.1).steps else rev (linkLoop y₀ c.1).steps) ++ stepsOf y₀ w

theorem endpt_link (y₀ : TT i T) (c : SpT i T × Bool) :
    endpt y₀ (if c.2 then (linkLoop y₀ c.1).steps else rev (linkLoop y₀ c.1).steps) = y₀ := by
  have hc : endpt y₀ (linkLoop y₀ c.1).steps = y₀ := (linkLoop y₀ c.1).closed
  split_ifs
  · exact hc
  · have := endpt_rev y₀ (linkLoop y₀ c.1).steps
    rwa [hc] at this

theorem endpt_stepsOf (y₀ : TT i T) : ∀ w, endpt y₀ (stepsOf y₀ w) = y₀
  | [] => rfl
  | c :: w => by rw [stepsOf, endpt_append, endpt_link, endpt_stepsOf y₀ w]

theorem whN_link (y₀ : TT i T) (c : SpT i T × Bool) (V : SpT i T → SUN.SU N) :
    whN (walk y₀ (if c.2 then (linkLoop y₀ c.1).steps else rev (linkLoop y₀ c.1).steps)) V
      = if c.2 then holN (linkLoop y₀ c.1) V else (holN (linkLoop y₀ c.1) V)⁻¹ := by
  have hc : endpt y₀ (linkLoop y₀ c.1).steps = y₀ := (linkLoop y₀ c.1).closed
  split_ifs
  · rfl
  · have := whN_rev y₀ (linkLoop y₀ c.1).steps V
    rw [hc] at this
    exact this

theorem whN_stepsOf (y₀ : TT i T) (V : SpT i T → SUN.SU N) : ∀ w,
    whN (walk y₀ (stepsOf y₀ w)) V = word w (fun l => holN (linkLoop y₀ l) V)
  | [] => by simp [stepsOf, walk, whN, word]
  | c :: w => by
      rw [stepsOf, walk_append, whN_append, endpt_link, whN_stepsOf y₀ V w, whN_link]
      simp [word]

/-- **The loop at `y₀` of a word** in the link loops. -/
def wordLoop (y₀ : TT i T) (w : List (SpT i T × Bool)) : Loop i T :=
  ⟨y₀, stepsOf y₀ w, endpt_stepsOf y₀ w⟩

theorem holN_wordLoop (y₀ : TT i T) (w : List (SpT i T × Bool)) (V : SpT i T → SUN.SU N) :
    holN (wordLoop y₀ w) V = word w (fun l => holN (linkLoop y₀ l) V) :=
  whN_stepsOf y₀ V w

/-- **Loop traces separate the gauge orbits of a slice** (`SU(N)`, `N ≠ 0`). -/
theorem tracesSeparate_slice [NeZero N] (V V' : SpT i T → SUN.SU N)
    (h : ∀ C : Loop i T, trace (holN C V : Mat N) = trace (holN C V' : Mat N)) :
    ∃ g : TT i T → SUN.SU N, V' = SliceKernelDefinite.gact g V := by
  rcases isEmpty_or_nonempty (TT i T) with hE | hne
  · exact ⟨fun _ => 1, funext fun l => (hE.false l.2).elim⟩
  · obtain ⟨y₀⟩ := hne
    obtain ⟨G, hG⟩ := su_conj_of_traces (fun l => holN (linkLoop y₀ l) V)
      (fun l => holN (linkLoop y₀ l) V')
      (fun w => by rw [← holN_wordLoop, ← holN_wordLoop]; exact h _)
    refine ⟨fun z => (pathHolN y₀ z V')⁻¹ * G * pathHolN y₀ z V, funext fun l => ?_⟩
    have hGl : holN (linkLoop y₀ l) V' = G * holN (linkLoop y₀ l) V * G⁻¹ := hG l
    have e : V' l = (pathHolN y₀ l.2 V')⁻¹ * holN (linkLoop y₀ l) V'
        * pathHolN y₀ (tsh i T l.1 l.2) V' := by
      rw [holN_linkLoop]; group
    rw [e, hGl, holN_linkLoop]
    unfold SliceKernelDefinite.gact
    group

open MassGap.CentreSectorSeed (Tr) in
/-- **`TracesSeparateN` holds at every `N ≠ 0` and every `n`.** -/
theorem tracesSeparateN_all [NeZero N] (n : ℕ) (i : Fin 4) : LoopsGenerateN.TracesSeparateN N n i :=
  fun V V' h => tracesSeparate_slice V V' h

open MassGap.CentreSectorSeedN (hSN) in
open MassGap.RunSeedN (SliceN EigenLevelsN allLoopsN LoopFam) in
/-- **`gen` on words at every `N ≠ 0`**: at `β > 0`, for measurable zero-flux levels, every excited level is in
the `L²` closure of the span of the word states of `Ω = φ_{g₀}`. -/
theorem excited_mem_closure_words_all [NeZero N] {β : ℝ} (hβ : 0 < β) {n : ℕ} {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → SliceN N n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevelsN N β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j)) :
    ∀ j, j ≠ g₀ → ElectricLoops.vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoopsN (hSN N n i) (φ g₀) .words) :
        Set (MeasureTheory.Lp ℝ 2 (hSN N n i))) :=
  LoopsGenerateN.excited_mem_closure_wordsN hβ hL hm (tracesSeparateN_all n i)

end Lattice

end MassGap.ProcesiSeparation

end

#print axioms MassGap.ProcesiSeparation.comm_eproj
#print axioms MassGap.ProcesiSeparation.cas_intw
#print axioms MassGap.ProcesiSeparation.exists_cas_ne
#print axioms MassGap.ProcesiSeparation.step
#print axioms MassGap.ProcesiSeparation.exists_unitary_intw
#print axioms MassGap.ProcesiSeparation.su_conj_of_traces
#print axioms MassGap.ProcesiSeparation.holN_linkLoop
#print axioms MassGap.ProcesiSeparation.tracesSeparate_slice
#print axioms MassGap.ProcesiSeparation.tracesSeparateN_all
#print axioms MassGap.ProcesiSeparation.excited_mem_closure_words_all
