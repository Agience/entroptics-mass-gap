import Mathlib
import MassGap.FiniteOrderTransfer

/-!
# MassGap.TransferGap — what a gap buys, with no logarithm and no spectral theorem

`ClayAssembly` states C1's remaining operator input as `TransferMovesSomething` — a transfer operator
on `ymH` that is not the identity — and notes that the Hamiltonian itself wants more:

> `-log T` needs `0 ∉ spectrum T` rather than injectivity, so this predicate is necessary and not
> sufficient.

That is right about `-log T`, and it is worth being exact about what follows from it.

**`-log T` is already built in this tree.** `Reconstruction.hamiltonian` is
`cfc (fun x => -Real.log x) T`, and `Reconstruction.reconstruct_qm_core` gives the whole
operator-theoretic output — self-adjoint, `H ≥ 0`, vacuum at `0`, `spectrum H ⊆ {0} ∪ [Δ, ∞)` — from
`spectrum T ⊆ {1} ∪ [ε, e^{−Δ}]` with `0 < ε`, on foundational axioms alone. That spectral
hypothesis comes from DECAY via `MomentSupport.le_of_positive_weight_decay`.

**So this file is not a workaround for a missing construction.** What it adds is a route that reaches
exponential CLUSTERING — the physical content — without passing through the spectral theorem at all,
which is useful because `TransferData` is a bilinear form rather than a Hilbert-space operator and has
no functional calculus to call.

## What the mass gap actually says about correlations

The physical content of a gap `Δ` is that connected correlations decay like `e^{-Δ·n}`:

    ⟨y, Tⁿ x⟩ − ⟨y, Ω⟩⟨Ω, x⟩  →  0  exponentially.

Written that way it is a statement about the FORM, and it needs no Hilbert space completion, no
functional calculus and no logarithm. What it needs is one hypothesis — that `T` contracts by a
factor `r < 1` on the vacuum's orthogonal complement — and two facts already in `Transfer`:
`ReflForm.cauchy_schwarz` and `TransferData.T_vac`.

`clustering_sq` is that statement and its proof is four steps: split `x` into its vacuum component
and the rest, note the rest stays orthogonal under `T`, iterate the contraction, and apply
Cauchy–Schwarz once.

## Why this is not a detour around the open item

**A gap IMPLIES `TransferMovesSomething`.** `gap_moves_something`: if anything orthogonal to the
vacuum has nonzero form, an operator with a gap moves it. So the open item is not an extra obligation
alongside the gap — it is a consequence of it, and an attempt to exhibit motion first is an attempt
to prove something weaker on the way to something stronger.

**And a gap is incompatible with finite order, with NO positivity hypothesis.**
`FiniteOrderTransfer.positive_finite_order_transfer_is_identity` reaches that wall using operator
positivity `0 ≤ form (T z) z`. `finite_order_fails_gap` reaches it using the gap instead and assumes
no positivity at all. The two are independent routes to the same conclusion, which is why the
translation route stays closed however the operator is built.

## What is NOT claimed

Nothing here produces an operator, and nothing here produces a gap. `GapAt` is a hypothesis, stated
so that what it buys can be seen before anyone pays for it. The `TransferData` the tree can currently
build unconditionally — `ClayAssembly.trivialTransfer` — has `T = 1`, and `identity_fails_gap` says
exactly what that costs: the identity satisfies `GapAt D r` with `r < 1` only on a space where the
form sees nothing off the vacuum.
-/

namespace MassGap.TransferGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 1. The hypothesis -/

/-- **THE GAP, STATED ON THE FORM.** `T` contracts by `r` on the vacuum's orthogonal complement.

This is the transfer-operator form of a mass gap `Δ = −log r`, and it is stated as a contraction
rather than as a logarithm precisely so that `−log T` — which needs `0 ∉ spectrum T` — never has to
exist.

DERIVED: the `2` is the form's own degree. `form (T x) (T x)` is a squared length, so a contraction
by `r` on lengths is a contraction by `r²` on it. No magnitude is chosen here; `r` is the caller's. -/
def GapAt (D : Transfer.TransferData A) (r : ℝ) : Prop :=
  ∀ x : A, D.form x D.vac = 0 → D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x

#print axioms GapAt

/-- **⛔ AND AT `1 ≤ r²` IT IS FREE.** `T_contract` and `form_nonneg` give it for EVERY
`TransferData`, with no hypothesis at all.

Stated so that no statement downstream has to hedge about it: a `GapAt D r` carrying no `r < 1` says
nothing, and any reduction whose hypothesis forces `1 ≤ r²` has reduced nothing. Both mistakes are
easy to make, because the `r²` hides the sign and the contraction bound is already in the structure.

DERIVED: the `1` is the threshold above which the statement is empty; the `2` is `GapAt`'s own
exponent. -/
theorem gapAt_of_one_le_sq {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) {r : ℝ} (hr : 1 ≤ r ^ 2) : GapAt D r := by
  intro x _
  calc D.form (D.T x) (D.T x) ≤ D.form x x := D.T_contract x
    _ ≤ r ^ 2 * D.form x x := le_mul_of_one_le_left (D.form_nonneg x) hr

#print axioms gapAt_of_one_le_sq

/-- **⭐⭐ THE DEGENERATE OBSERVABLES ARE ALREADY DISCHARGED**, so `GapAt` need only be checked where
the form is positive.

At an `x` with `form x x = 0`, `T_contract` puts `form (T x) (T x)` at or below `0` and `form_nonneg`
at or above it, so both sides of the gap inequality are `0` and it holds at EVERY `r` — including
`r < 1`, where the statement is otherwise the whole content.

**THE CONVERSE IS ONE LINE**, by dropping the positivity argument, so this is an iff whose whole
content is the degenerate branch. What it buys a caller is the right to assume `0 < form x x`; that
is real and it is small.

**⛔ AND IT DOES NOT MAKE THE GAP EASIER.** `GapAt`'s content at a non-degenerate `x` is untouched.
`GNSCompare.gapAt_of_opT_contracts` and `gapAt_of_tq_contracts` handle the same null space more
strongly, by passing to the quotient where it is `0` outright.

The `x` the form annihilates are the ones the GNS quotient cannot see — the same null space that
separates `T ≠ 1` from `ClayAssembly.TransferMovesSomething`.

DERIVED: the `0` is the degenerate value of the form and the vacuum-orthogonality it is checked
against; the `2` is `GapAt`'s own degree, as there. -/
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

/-- **THE VACUUM'S ORTHOGONAL COMPLEMENT IS `T`-INVARIANT.** Two fields and nothing else:
self-adjointness moves `T` across the form, and `T` fixes the vacuum. -/
theorem orth_invariant (D : Transfer.TransferData A) {x : A} (hx : D.form x D.vac = 0) :
    D.form (D.T x) D.vac = 0 := by
  rw [D.T_symm, D.T_vac]
  exact hx

#print axioms orth_invariant

/-- Every power fixes the vacuum. -/
theorem pow_vac (D : Transfer.TransferData A) (n : ℕ) : (D.T ^ n) D.vac = D.vac := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, D.T_vac, ih]

#print axioms pow_vac

/-- **AND THE CONTRACTION ITERATES.** `n` steps contract the squared form by `r^{2n}`.

DERIVED: `2 * n` is `n` applications of the `2` in `GapAt`, which is the form's degree. -/
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

/-- The part of `x` the vacuum does not account for. `vac_norm` is what makes the coefficient simply
`form x vac` rather than a ratio. -/
def vacProj (D : Transfer.TransferData A) (x : A) : A := x - (D.form x D.vac) • D.vac

#print axioms vacProj

/-- It is orthogonal to the vacuum, which is the point of it. -/
theorem vacProj_orth (D : Transfer.TransferData A) (x : A) :
    D.form (vacProj D x) D.vac = 0 := by
  unfold vacProj
  rw [MassGap.FiniteOrderTransfer.form_sub_left D.toPreForm, D.toPreForm.form_smul_left,
    D.vac_norm]
  ring

#print axioms vacProj_orth

/-- and it reassembles. -/
theorem vacProj_add (D : Transfer.TransferData A) (x : A) :
    (D.form x D.vac) • D.vac + vacProj D x = x := by
  unfold vacProj
  abel

#print axioms vacProj_add

/-! ## 4. A gap is exponential clustering -/

/-- **A GAP IS EXPONENTIAL CLUSTERING.**

`(⟨y, Tⁿx⟩ − ⟨y,Ω⟩⟨Ω,x⟩)² ≤ r^{2n} · ⟨y,y⟩ · ⟨x⊥,x⊥⟩`. The connected correlation falls off like
`r^n`, which is `e^{−Δn}` for `Δ = −log r`.

Stated SQUARED, because that is the form Cauchy–Schwarz delivers and it needs no square root — the
statement is then an identity of the form's own arithmetic rather than a statement about a norm that
would have to be constructed.

**No spectral theorem, no completion, no logarithm.** Four steps: split `x`, note the complement is
`T`-invariant, iterate, apply `ReflForm.cauchy_schwarz` once.

DERIVED: the `2`s are the form's degree, as in `GapAt`; nothing is a magnitude. -/
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

/-- **THE IDENTITY FAILS THE GAP** — unless the form sees nothing off the vacuum.

This is the counterpart of `ClayAssembly.ym_target_discharged_trivially`: `trivialTransfer` satisfies
every clause of the transfer target with `T = 1`, and it satisfies `GapAt` too, but only by being
blind off the vacuum. On a space where something orthogonal to the vacuum has positive form, `T = 1`
is refuted outright.

DERIVED: `r < 1` is what a gap MEANS — `r = 1` is no decay — not a cut. -/
theorem identity_fails_gap (D : Transfer.TransferData A) (hT : ∀ z : A, D.T z = z)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hg : GapAt D r)
    (x : A) (hx : D.form x D.vac = 0) : D.form x x = 0 := by
  have h := hg x hx
  rw [hT x] at h
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  have hr2 : r ^ 2 < 1 := by nlinarith
  nlinarith

#print axioms identity_fails_gap

/-- **AND SO DOES ANY OPERATOR OF FINITE ORDER — with NO positivity hypothesis.**

`FiniteOrderTransfer.positive_finite_order_transfer_is_identity` reaches the same wall through
operator positivity `0 ≤ form (T z) z`. This route pays with the gap instead and assumes no
positivity at all, so the translation route to `I4` is closed twice over, by independent means.

A torus gives finite order exactly: translation by one step along a direction of extent `m` has
`T^m = 1`. So no lattice translation can carry a gap, whatever else is assumed of it.

DERIVED: `1 ≤ m` is the smallest order with a step; `r < 1` is what a gap means. -/
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

/-- **A GAP FORCES THE OPERATOR TO MOVE SOMETHING.**

`ClayAssembly.TransferMovesSomething` asks for `∃ x, T x ≠ x`, stated through the form as
`form (T x − x) (T x − x) ≠ 0`. This proves it is not an extra obligation alongside a gap but a
CONSEQUENCE of one: on any vector orthogonal to the vacuum that the form sees, an operator with a gap
must move it.

So exhibiting motion first is proving something weaker on the way to something stronger. The
displacement being null would make `T x` the same form-length as `x`, and a gap forbids that.

DERIVED: `r < 1` is what a gap means. -/
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

/-! ## ⭐ A witness: `GapAt` is satisfiable below rate one

Every occurrence of `GapAt` in this tree is a HYPOTHESIS, and above rate one it is free
(`bound_is_free_of_one_le`). Nothing exhibited one below rate one, so every theorem downstream of it
— `GNSCompare`, `GapToOperator`, `B2Locality` — ran on a predicate with no instance. This section
supplies one.

It is finite-dimensional and has no gauge content. It witnesses that the definitions are
satisfiable, nothing more, in the same spirit as `FlagshipScope.flagship_for_bogus`. -/

section Witness

/-- **One time step on a two-dimensional model: fix the vacuum, scale its complement by `lam`.**

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

/-- **⭐ A `TransferData` WHOSE STEP CONTRACTS THE VACUUM'S COMPLEMENT BY `lam`.**

The standard form on `Fin 2 → ℝ`, the vacuum at coordinate `0`, and `diagStep lam`. Reflection
positivity is the sum of two squares, self-adjointness is the diagonal, and contractivity is
`lam² ≤ 1`.

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

/-- **⭐⭐ AND IT SATISFIES `GapAt` AT `lam`, WITH EQUALITY.**

Orthogonality to the vacuum is `x 0 = 0`, and then both sides read `lam² * (x 1)²`. So the rate is
attained rather than merely bounded, and `GapAt` is satisfiable at every `lam` with `lam² ≤ 1` — in
particular below one, where the predicate has content.

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

/-- **⭐⭐⭐ SO A GAP BELOW RATE ONE EXISTS.** The predicate every theorem downstream of `GapAt`
assumes is satisfiable with room to spare, and not only in the free regime `1 ≤ r²`.

**⛔ IT IS A WITNESS, NOT A PHYSICAL RESULT.** The model is two-dimensional and carries no gauge
field. What it settles is that `GapAt`, `GNSCompare`'s equivalences and `GapToOperator`'s bounds are
not vacuously about nothing; what produces a gap for the WILSON transfer is untouched.

DERIVED: `1` is the free-regime boundary this rate sits strictly below; `1/2` is a witness value,
chosen only to be between `0` and `1`, and any other would do. -/
theorem exists_gapAt_lt_one :
    ∃ (D : MassGap.Transfer.TransferData (Fin 2 → ℝ)) (r : ℝ), 0 ≤ r ∧ r < 1 ∧ GapAt D r :=
  ⟨diagTransfer (1 / 2) (by norm_num), 1 / 2, by norm_num, by norm_num,
    gapAt_diagTransfer (1 / 2) (by norm_num)⟩

#print axioms exists_gapAt_lt_one

end Witness

end MassGap.TransferGap
