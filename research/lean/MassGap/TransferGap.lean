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

end MassGap.TransferGap
