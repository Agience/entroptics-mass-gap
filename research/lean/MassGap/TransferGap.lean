import Mathlib
import MassGap.FiniteOrderTransfer

/-!
# MassGap.TransferGap — a contraction hypothesis on a bilinear form, and what follows from it

`Transfer.TransferData A` is a symmetric, nonnegative bilinear form on a real module together with a
self-adjoint contraction `T` fixing a normalised vacuum vector. This module states a gap as a
property of that form — `GapAt D r` — and derives exponential clustering, incompatibility with
finite order, and the non-triviality of `T`, entirely within the form's arithmetic: no Hilbert space
completion, no functional calculus and no logarithm appears in any statement here.

Contents:
* `GapAt D r` — `∀ x, D.form x D.vac = 0 → D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x`.
* `gapAt_of_one_le_sq` — every `TransferData` satisfies `GapAt D r` whenever `1 ≤ r ^ 2`, from the
  structure fields `T_contract` and `form_nonneg` alone.
* `gapAt_of_nondegenerate` — it suffices to check `GapAt` where `0 < D.form x x`.
* `orth_invariant`, `pow_vac`, `gap_pow` — the vacuum's orthogonal complement is `T`-invariant,
  every power fixes the vacuum, and the contraction iterates to `r ^ (2 * n)`.
* `vacProj`, `vacProj_orth`, `vacProj_add` — the vacuum component of `x`, removed and reassembled.
* `clustering_sq` — the squared connected correlation is bounded by
  `r ^ (2 * n) * (D.form y y * D.form (vacProj D x) (vacProj D x))`.
* `identity_fails_gap`, `finite_order_fails_gap` — with `r < 1`, an operator equal to the identity,
  or of finite order `m ≥ 1`, forces `D.form x x = 0` on the vacuum's complement. The finite-order
  route assumes no operator positivity.
* `gap_moves_something` — with `r < 1`, an `x` orthogonal to the vacuum with `D.form x x ≠ 0` has
  `D.form (D.T x - x) (D.T x - x) ≠ 0`, so `T` is not the identity.
* Section `Witness` — `diagStep`, `diagTransfer`, `gapAt_diagTransfer`, `exists_gapAt_lt_one`: a
  two-dimensional `TransferData` satisfying `GapAt` at any `lam` with `lam ^ 2 ≤ 1`, and hence an
  instance below rate one.

Scope. `GapAt` is a hypothesis everywhere it appears; no declaration here constructs a
`TransferData` from a gauge theory or derives a gap for one. Above rate one the predicate follows
from the structure fields (`gapAt_of_one_le_sq`), so only `r < 1` carries content. The witness in
section `Witness` is two-dimensional and has no gauge content; it establishes that `GapAt` is
satisfiable below rate one and nothing further. `clustering_sq` is stated squared, which is the form
Cauchy–Schwarz delivers and needs no square root or norm.
-/

namespace MassGap.TransferGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 1. The hypothesis -/

/-- The gap, stated on the form: `∀ x, D.form x D.vac = 0 → D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x`.
`T` contracts by `r` on the vacuum's orthogonal complement. A `Prop`-valued definition; it asserts
nothing on its own and carries no hypothesis that `r < 1`.

Written as a contraction of the form rather than as a spectral condition, so nothing downstream
needs `0 ∉ spectrum T` or a logarithm of an operator.

DERIVED: `0` is the value of `D.form x D.vac` that selects the vacuum's orthogonal complement — the
subspace the contraction is asserted on. `2` is the form's own degree: `form (T x) (T x)` is a
squared length, so a contraction by `r` on lengths reads as `r ^ 2` here. `r` is the caller's. -/
def GapAt (D : Transfer.TransferData A) (r : ℝ) : Prop :=
  ∀ x : A, D.form x D.vac = 0 → D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x

#print axioms GapAt

/-- At `1 ≤ r ^ 2`, `GapAt D r` holds for every `TransferData D`, with no further hypothesis. The
proof chains the structure field `T_contract` with `le_mul_of_one_le_left` on `form_nonneg`.

Scope: this fixes the range of `r` in which `GapAt` has content. A `GapAt D r` whose `r` is not
constrained below one asserts nothing beyond the structure fields.

DERIVED: `1` is the threshold on `r ^ 2` at or above which the property is automatic; `2` is
`GapAt`'s own exponent, the form's degree. -/
theorem gapAt_of_one_le_sq {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) {r : ℝ} (hr : 1 ≤ r ^ 2) : GapAt D r := by
  intro x _
  calc D.form (D.T x) (D.T x) ≤ D.form x x := D.T_contract x
    _ ≤ r ^ 2 * D.form x x := le_mul_of_one_le_left (D.form_nonneg x) hr

#print axioms gapAt_of_one_le_sq

/-- It suffices to check the gap inequality where the form is strictly positive: if the inequality
holds at every `x` with `D.form x D.vac = 0` and `0 < D.form x x`, then `GapAt D r` holds. The proof
splits on `form_nonneg`; in the degenerate branch `T_contract` puts `D.form (D.T x) (D.T x)` at or
below `0` and `form_nonneg` at or above, so both sides are `0` and the inequality holds at any `r`.

Scope: the content at a non-degenerate `x` is unchanged; this only removes the null space of the
form from what a caller must check. The reverse implication is immediate.

DERIVED: `0` is the value of `D.form x D.vac` selecting the vacuum's complement, and the strict
lower bound on `D.form x x` in the hypothesis; `2` is `GapAt`'s own exponent. -/
theorem gapAt_of_nondegenerate {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) {r : ℝ}
    (h : ∀ x : A, D.form x D.vac = 0 → 0 < D.form x x →
      D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x) :
    GapAt D r := by
  intro x hvac
  rcases lt_or_eq_of_le (D.form_nonneg x) with hpos | hzero
  · exact h x hvac hpos
  · have hxx : D.form x x = 0 := hzero.symm
    have hle : D.form (D.T x) (D.T x) ≤ 0 := by
      rw [← hxx]
      exact D.T_contract x
    have hTx : D.form (D.T x) (D.T x) = 0 := le_antisymm hle (D.form_nonneg _)
    rw [hTx, hxx, mul_zero]

#print axioms gapAt_of_nondegenerate

/-! ## 2. The complement is invariant, and the contraction iterates -/

/-- The vacuum's orthogonal complement is `T`-invariant: `D.form x D.vac = 0` gives
`D.form (D.T x) D.vac = 0`. Two structure fields: `T_symm` moves `T` across the form and `T_vac`
fixes the vacuum.

DERIVED: the one numeral is `0`, the value of the form against the vacuum, in both the hypothesis
and the conclusion. -/
theorem orth_invariant (D : Transfer.TransferData A) {x : A} (hx : D.form x D.vac = 0) :
    D.form (D.T x) D.vac = 0 := by
  rw [D.T_symm, D.T_vac]
  exact hx

#print axioms orth_invariant

/-- `(D.T ^ n) D.vac = D.vac` at every `n : ℕ`, by induction on `n` from the structure field
`T_vac`.

DERIVED: no numeral occurs in the statement; `n` is the caller's power. -/
theorem pow_vac (D : Transfer.TransferData A) (n : ℕ) : (D.T ^ n) D.vac = D.vac := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, D.T_vac, ih]

#print axioms pow_vac

/-- The contraction iterates: from `0 ≤ r` and `GapAt D r`, at every `n : ℕ` and every `x` with
`D.form x D.vac = 0`,
`D.form ((D.T ^ n) x) ((D.T ^ n) x) ≤ r ^ (2 * n) * D.form x x`. By induction on `n`, using
`orth_invariant` to keep the iterate in the complement.

DERIVED: `0` is the lower bound on `r`, needed so the accumulated factor `r ^ (2 * k)` stays
nonnegative when multiplying through, and the value of the form against the vacuum; `2 * n` is `n`
applications of `GapAt`'s exponent `2`, the form's degree. -/
theorem gap_pow (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    ∀ (n : ℕ) (x : A), D.form x D.vac = 0 →
      D.form ((D.T ^ n) x) ((D.T ^ n) x) ≤ r ^ (2 * n) * D.form x x := by
  intro n
  induction n with
  | zero =>
      intro x _
      simp only [pow_zero, Module.End.one_apply, Nat.mul_zero, one_mul]
      exact le_rfl
  | succ k ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply]
      have hrp : (0 : ℝ) ≤ r ^ (2 * k) := by positivity
      calc D.form ((D.T ^ k) (D.T x)) ((D.T ^ k) (D.T x))
          ≤ r ^ (2 * k) * D.form (D.T x) (D.T x) := ih (D.T x) (orth_invariant D hx)
        _ ≤ r ^ (2 * k) * (r ^ 2 * D.form x x) :=
            mul_le_mul_of_nonneg_left (hg x hx) hrp
        _ = r ^ (2 * (k + 1)) * D.form x x := by
            rw [Nat.mul_succ, pow_add]
            ring

#print axioms gap_pow

/-! ## 3. The vacuum component, removed -/

/-- `vacProj D x = x - (D.form x D.vac) • D.vac`, the part of `x` the vacuum does not account for.
The coefficient is `D.form x D.vac` rather than a ratio because the structure field `vac_norm`
normalises the vacuum.

DERIVED: no numeral occurs. -/
def vacProj (D : Transfer.TransferData A) (x : A) : A := x - (D.form x D.vac) • D.vac

#print axioms vacProj

/-- `D.form (vacProj D x) D.vac = 0`: the projection is orthogonal to the vacuum. Expands the
subtraction with `FiniteOrderTransfer.form_sub_left` and `form_smul_left`, then uses `vac_norm`.

DERIVED: the one numeral is `0`, the value of the form against the vacuum. -/
theorem vacProj_orth (D : Transfer.TransferData A) (x : A) :
    D.form (vacProj D x) D.vac = 0 := by
  unfold vacProj
  rw [MassGap.FiniteOrderTransfer.form_sub_left D.toPreForm, D.toPreForm.form_smul_left,
    D.vac_norm]
  ring

#print axioms vacProj_orth

/-- `(D.form x D.vac) • D.vac + vacProj D x = x`: the two pieces reassemble, by `abel` after
unfolding.

DERIVED: no numeral occurs. -/
theorem vacProj_add (D : Transfer.TransferData A) (x : A) :
    (D.form x D.vac) • D.vac + vacProj D x = x := by
  unfold vacProj
  abel

#print axioms vacProj_add

/-! ## 4. A gap is exponential clustering -/

/-- Exponential clustering of the connected correlation. From `0 ≤ r` and `GapAt D r`, at every
`n : ℕ` and all `x y : A`,

    (D.form y ((D.T ^ n) x) - D.form y D.vac * D.form D.vac x) ^ 2
      ≤ r ^ (2 * n) * (D.form y y * D.form (vacProj D x) (vacProj D x)).

Four steps: split `x` by `vacProj_add`, push `T ^ n` through using `pow_vac` so the vacuum term is
exactly the subtracted product, apply `ReflForm.cauchy_schwarz` once, and finish with `gap_pow`.

Scope: stated squared, so no square root or norm is required; the right-hand side involves the
form of the vacuum-orthogonal part of `x`, not of `x` itself. No spectral theorem, completion or
logarithm enters.

DERIVED: `0` is the lower bound on `r`; the exponent `2` on the left is the square Cauchy–Schwarz
produces, and the `2` in `r ^ (2 * n)` is `GapAt`'s exponent iterated `n` times. No numeral is a
magnitude. -/
theorem clustering_sq (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (n : ℕ) (x y : A) :
    (D.form y ((D.T ^ n) x) - D.form y D.vac * D.form D.vac x) ^ 2
      ≤ r ^ (2 * n) * (D.form y y * D.form (vacProj D x) (vacProj D x)) := by
  have hsplit : (D.T ^ n) x
      = (D.form x D.vac) • D.vac + (D.T ^ n) (vacProj D x) := by
    conv_lhs => rw [← vacProj_add D x]
    rw [map_add, map_smul, pow_vac D n]
  have hdiff : D.form y ((D.T ^ n) x) - D.form y D.vac * D.form D.vac x
      = D.form y ((D.T ^ n) (vacProj D x)) := by
    rw [hsplit, D.toPreForm.form_add_right, D.toPreForm.form_smul_right,
      D.toPreForm.form_symm D.vac x]
    ring
  rw [hdiff]
  have hyy : 0 ≤ D.form y y := D.form_nonneg y
  calc (D.form y ((D.T ^ n) (vacProj D x))) ^ 2
      ≤ D.form y y * D.form ((D.T ^ n) (vacProj D x)) ((D.T ^ n) (vacProj D x)) :=
        D.toReflForm.cauchy_schwarz y ((D.T ^ n) (vacProj D x))
    _ ≤ D.form y y * (r ^ (2 * n) * D.form (vacProj D x) (vacProj D x)) :=
        mul_le_mul_of_nonneg_left (gap_pow D hr hg n (vacProj D x) (vacProj_orth D x)) hyy
    _ = r ^ (2 * n) * (D.form y y * D.form (vacProj D x) (vacProj D x)) := by ring

#print axioms clustering_sq

/-! ## 5. What a gap rules out, and what it forces -/

/-- If `D.T` is the identity and `GapAt D r` holds with `0 ≤ r < 1`, then `D.form x x = 0` at every
`x` orthogonal to the vacuum: the form sees nothing off the vacuum. Substituting `hT` into the gap
inequality gives `D.form x x ≤ r ^ 2 * D.form x x` with `r ^ 2 < 1`, which `nlinarith` closes
against `form_nonneg`.

DERIVED: `0` is the lower bound on `r`, the value of the form against the vacuum in the hypothesis,
and the value of `D.form x x` in the conclusion; `1` is the strict upper bound on `r`, the point at
which the contraction stops contracting. -/
theorem identity_fails_gap (D : Transfer.TransferData A) (hT : ∀ z : A, D.T z = z)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hg : GapAt D r)
    (x : A) (hx : D.form x D.vac = 0) : D.form x x = 0 := by
  have h := hg x hx
  rw [hT x] at h
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  have hr2 : r ^ 2 < 1 := by nlinarith
  nlinarith

#print axioms identity_fails_gap

/-- The same conclusion for an operator of finite order. Given `1 ≤ m`, periodicity
`hper : ∀ y, (fun z => D.T z)^[m] y = y`, and `GapAt D r` with `0 ≤ r < 1`, every `x` orthogonal to
the vacuum has `D.form x x = 0`. The proof applies `gap_pow` at `n = m`, rewrites the iterate back
to `x` by `hper`, and uses `r ^ (2 * m) < 1`.

Scope: no operator positivity is assumed. `FiniteOrderTransfer.positive_finite_order_transfer_is_identity`
reaches a comparable conclusion instead through `0 ≤ D.form (D.T z) z`; the two hypotheses are
independent.

DERIVED: `1` is the least order that involves at least one step, `1 ≤ m`, and the strict upper bound
on `r`; `0` is the lower bound on `r`, the value of the form against the vacuum, and the value of
`D.form x x` concluded. -/
theorem finite_order_fails_gap (D : Transfer.TransferData A) (m : ℕ) (hm : 1 ≤ m)
    (hper : ∀ y : A, (fun z => D.T z)^[m] y = y)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hg : GapAt D r)
    (x : A) (hx : D.form x D.vac = 0) : D.form x x = 0 := by
  have hpow : (D.T ^ m) x = x := by
    rw [Module.End.pow_apply]
    exact hper x
  have h := gap_pow D hr0 hg m x hx
  rw [hpow] at h
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  have hrm : r ^ (2 * m) < 1 := pow_lt_one₀ hr0 hr (by omega)
  nlinarith

#print axioms finite_order_fails_gap

/-- A gap forces `T` to move something. Given `GapAt D r` with `0 ≤ r < 1`, an `x` with
`D.form x D.vac = 0` and `D.form x x ≠ 0` satisfies `D.form (D.T x - x) (D.T x - x) ≠ 0`. The proof
assumes the displacement null, derives from Cauchy–Schwarz that it is form-orthogonal to everything,
concludes `D.form (D.T x) (D.T x) = D.form x x`, and contradicts the gap inequality with
`r ^ 2 < 1`.

This is the shape of `ClayAssembly.TransferMovesSomething`, expressed through the form, so that
predicate follows from a gap rather than standing beside it.

DERIVED: `0` is the lower bound on `r` and the value of the form against the vacuum; the two `≠ 0`s
are the non-degeneracy hypothesis and the conclusion. `1` is the strict upper bound on `r`. -/
theorem gap_moves_something (D : Transfer.TransferData A) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hg : GapAt D r) (x : A) (hx : D.form x D.vac = 0) (hnz : D.form x x ≠ 0) :
    D.form (D.T x - x) (D.T x - x) ≠ 0 := by
  intro hz
  -- a null displacement is form-orthogonal to everything, by Cauchy–Schwarz
  have hzy : ∀ y : A, D.form (D.T x - x) y = 0 := by
    intro y
    have hcs := D.toReflForm.cauchy_schwarz (D.T x - x) y
    rw [hz, zero_mul] at hcs
    exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _))
  -- so `T x` has the same form-length as `x`
  have hTxe : D.T x = (D.T x - x) + x := by abel
  have hTx : D.form (D.T x) (D.T x) = D.form x x := by
    conv_lhs => rw [hTxe]
    rw [D.toPreForm.form_add_left, D.toPreForm.form_add_right, D.toPreForm.form_add_right,
      hz, hzy x, D.toPreForm.form_symm x (D.T x - x), hzy x]
    ring
  -- which the gap forbids
  have h := hg x hx
  rw [hTx] at h
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  have hr2 : r ^ 2 < 1 := by nlinarith
  exact hnz (by nlinarith)

#print axioms gap_moves_something

/-! ## A witness: `GapAt` is satisfiable below rate one

`GapAt` is a hypothesis wherever it appears, and above rate one it follows from the structure fields
(`gapAt_of_one_le_sq`). This section builds a two-dimensional `TransferData` satisfying it at any
`lam` with `lam ^ 2 ≤ 1`, including `lam < 1`, so the predicate and the theorems that consume it —
`GNSCompare`, `GapToOperator`, `B2Locality` — are about something inhabited.

The model is finite-dimensional and carries no gauge field; it settles satisfiability and nothing
about the Wilson transfer. -/

section Witness

/-- One time step on a two-dimensional model: the linear map on `Fin 2 → ℝ` fixing coordinate `0`
and scaling coordinate `1` by `lam`.

DERIVED: the `2` in `Fin 2` is the smallest dimension that has both a vacuum and a complement, which
is all a witness needs; `0` and `1` are those two coordinates, `0` carrying the vacuum. `lam` is the
caller's rate and no magnitude is chosen here. -/
def diagStep (lam : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := fun i => if i = 0 then x 0 else lam * x 1
  map_add' x y := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' c x := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring

/-- A `TransferData (Fin 2 → ℝ)` whose step contracts the vacuum's complement by `lam`: the standard
inner product as the form, the vacuum at coordinate `0`, and `diagStep lam` as `T`. `form_nonneg` is
a sum of two squares, `T_symm` holds because the map is diagonal, and `T_contract` is the
hypothesis `lam ^ 2 ≤ 1`.

DERIVED: the `2` in `Fin 2` is the model's dimension, as in `diagStep`, and the `2` in `lam ^ 2` is
the form's degree — `T_contract` compares `form (T x) (T x)` with `form x x`, so the rate enters
squared. The `1` bounding it is contractivity, `TransferData`'s own field. `0` and `1` index the two
coordinates, and the `1` in `vac_norm` is the normalisation `TransferData` requires. -/
noncomputable def diagTransfer (lam : ℝ) (hlam : lam ^ 2 ≤ 1) :
    MassGap.Transfer.TransferData (Fin 2 → ℝ) where
  form x y := x 0 * y 0 + x 1 * y 1
  form_symm x y := by ring
  form_add_left x y z := by simp [Pi.add_apply]; ring
  form_smul_left r x y := by simp [Pi.smul_apply]; ring
  form_nonneg x := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  T := diagStep lam
  vac := fun i => if i = 0 then 1 else 0
  T_symm x y := by simp [diagStep]; ring
  T_contract x := by
    simp only [diagStep, LinearMap.coe_mk, AddHom.coe_mk]
    norm_num
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  T_vac := by
    funext i
    by_cases h : i = 0 <;> simp [diagStep, h]
  vac_norm := by norm_num

/-- `GapAt (diagTransfer lam hlam) lam` for every `lam` with `lam ^ 2 ≤ 1`. Orthogonality to the
vacuum is `x 0 = 0`, and then both sides of the gap inequality read `lam ^ 2 * (x 1) ^ 2`, so the
rate is attained rather than merely bounded.

DERIVED: the `2` in `Fin 2` is the model's dimension and the `2` in `lam ^ 2` is the form's degree,
both as in `diagTransfer`; the `1` is that hypothesis's contractivity bound. The `0` is the vacuum
coordinate, where orthogonality puts `x`. -/
theorem gapAt_diagTransfer (lam : ℝ) (hlam : lam ^ 2 ≤ 1) :
    GapAt (diagTransfer lam hlam) lam := by
  intro x hx
  simp only [diagTransfer, diagStep, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [diagTransfer] at hx
  norm_num at hx ⊢
  nlinarith [hx]

#print axioms gapAt_diagTransfer

/-- There is a `TransferData (Fin 2 → ℝ)` and a rate `r` with `0 ≤ r`, `r < 1` and `GapAt D r`. The
witnesses are `diagTransfer (1 / 2) _` and `r = 1 / 2`, via `gapAt_diagTransfer`.

Scope: the model is two-dimensional and carries no gauge field, so this establishes that `GapAt`
below rate one is inhabited and nothing about the Wilson transfer.

DERIVED: `2` is the dimension `Fin 2` of the witness module, the least that has both a vacuum
coordinate and a complement; `0` and `1` bracket the rate, `1` being the boundary above which
`gapAt_of_one_le_sq` makes the predicate automatic. The rate `1 / 2` occurs in the proof term only,
chosen to sit strictly between those two bounds; any such value serves. -/
theorem exists_gapAt_lt_one :
    ∃ (D : MassGap.Transfer.TransferData (Fin 2 → ℝ)) (r : ℝ), 0 ≤ r ∧ r < 1 ∧ GapAt D r :=
  ⟨diagTransfer (1 / 2) (by norm_num), 1 / 2, by norm_num, by norm_num,
    gapAt_diagTransfer (1 / 2) (by norm_num)⟩

#print axioms exists_gapAt_lt_one

end Witness

end MassGap.TransferGap
