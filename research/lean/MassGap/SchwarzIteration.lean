import Mathlib
import MassGap.Transfer
import MassGap.InfiniteReflection

/-!
# MassGap.SchwarzIteration — `T_contract` is a theorem, not a hypothesis

## What this closes, stated exactly

`Transfer.TransferData` has six fields. Two concern the time translation's relation to the form, and
this file is about those two:

| field | what it needs | this file |
|---|---|---|
| `T_symm` | `⟨Tx, y⟩ = ⟨x, Ty⟩` | `form_shift_symm` proves the corresponding identity ON `C(X, ℝ)`, from `ShiftCompat` |
| `T_contract` | `⟨Tx, Tx⟩ ≤ ⟨x, x⟩` | `contract_of_bounded_orbit` DERIVES it from `T_symm` plus a bounded orbit |

**`T_symm` is not eliminated — it is consumed.** `orbit_log_convex`,
`contract_of_bounded_orbit` and `null_is_preserved` each take it as the hypothesis `hsym`, which is
character-for-character `TransferData.T_symm`. What is shown is that `T_contract` need not be assumed
BESIDE it: symmetry plus a bounded orbit is enough.

**And boundedness is genuinely needed, not decoration.** On `A = ℝ` with `form x y = x·y` and
`T x = 2x`, the form is symmetric and positive semidefinite and `⟨Tx,Tx⟩ = 4x² > x²`. So "follows
from symmetry alone" would be false; `orbit_bounded_of_state` is what supplies the missing input in
the intended instance.

**Neither delivers `TransferData.T_symm` directly.** That field is about `form : A → A → ℝ` on a
carrier; `form_shift_symm` concludes an identity about `ν` on all of `C(X, ℝ)`. Restricting the shift
to a submodule and unfolding `stateReflForm` is `MassGap.TransferAssembly`'s work, not this file's.

## The Schwarz iteration

Write `aₙ = ⟨Tⁿx, Tⁿx⟩`. Moving one `T` across the form gives `aₙ₊₁ = ⟨Tⁿx, Tⁿ⁺²x⟩`, and
Cauchy–Schwarz on that turns into

    aₙ₊₁² ≤ aₙ · aₙ₊₂,

so `log a` is midpoint-convex. A convex sequence whose increments ever increase runs away: if
`a₁ > a₀` then the ratios `aₙ₊₁/aₙ` are non-decreasing, so `aₙ ≥ a₀·(a₁/a₀)ⁿ`, which is unbounded.
The orbit is bounded, so `a₁ ≤ a₀`. **That is `T_contract`.**

Every step is cross-multiplied rather than divided, so no positivity side condition is needed to
STATE the inequalities. Two case splits remain in the proof and are unavoidable: `aₙ₊₁ = 0` inside the
ratio induction, where the conclusion holds without the inductive hypothesis, and `a₀ = 0`, where the
assumption `a₀ < a₁` is contradicted outright.

## What this does NOT close

**The form.** `contract_of_bounded_orbit` takes a `Transfer.ReflForm`, so it consumes positivity
rather than supplying it; on the infinite lattice that is still
`InfiniteReflection.ReflPositiveOn` for a state nobody has exhibited.

**The carrier.** The theorems are about an abstract `A`. Instantiating them needs the shift and the
form on the same carrier, which `MassGap.TransferAssembly.restrictT` supplies, using
`HalfSpaceAlgebra.halfSpaceAlg_shift_stable`.

**The boundedness hypothesis is real.** `contract_of_bounded_orbit` needs a uniform `M` over the
WHOLE orbit. `orbit_bounded_of_state` supplies it for a form built from a state, and that is the only
place the state's boundedness is used — but a form not of that shape would have to supply it
separately, and nothing here proves every reflection form does.
-/

namespace MassGap.SchwarzIteration

open MassGap.Transfer

/-! ## 1. `T_symm`, from the reflection conjugating the shift -/

section Symm

open MassGap.InfiniteReflection MassGap.DLRLimit

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **WHAT A TIME TRANSLATION MUST SATISFY** for the reflection form to see it as symmetric.

`T` is the forward shift and `S` the backward one. The four conditions are the physics: a translation
of a product is the product of the translations, translating back then forward is nothing, the
reflection turns a forward translation into a backward one, and the state does not see a translation.

**`T_S` asks only `T ∘ S = id`, but it gets more than it asks.** Applying `θ` to `theta_T` and using
involutivity gives `T = θ ∘ S ∘ θ`, and chasing once more gives `S ∘ T = id` — proved as
`TransferAssembly.shift_inverse_is_two_sided`. **So `ShiftCompat` forces the translation to be
invertible**, which is satisfiable on `ℤ` (`InfiniteShift.ishiftConf` is a bijection) and NOT on a
half-line of `ℕ`. Writing the weaker-looking field buys nothing and the stronger consequence should
be visible.

DERIVED: no numeral. -/
structure ShiftCompat (R : Reflection X) (ν : State X) where
  /-- The forward time translation. -/
  T : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)
  /-- The backward time translation. -/
  S : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)
  /-- A translation of a product is the product of the translations. -/
  T_mul : ∀ f g : C(X, ℝ), T (f * g) = T f * T g
  /-- Translating back and then forward is doing nothing. -/
  T_S : ∀ f : C(X, ℝ), T (S f) = f
  /-- **The reflection conjugates the forward shift to the backward one.** -/
  theta_T : ∀ f : C(X, ℝ), R.θ (T f) = S (R.θ f)
  /-- The state is translation-invariant. -/
  nu_T : ∀ f : C(X, ℝ), ν (T f) = ν f

/-- **⭐ `T_symm`, PROVED.** Four rewrites:

    ν(θ(Tf)·g) = ν(S(θf)·g)          the reflection conjugates
               = ν(T(S(θf)·g))       the state is translation-invariant
               = ν(T(S(θf))·T g)     a translation is multiplicative
               = ν(θf·T g)           translating back then forward is nothing.

This is where reflection positivity earns its keep: the form is symmetric for the transfer operator
*because* the reflection reverses time, which is the whole reason Osterwalder–Schrader pairs a
reflection with a translation.

DERIVED: no numeral. -/
theorem form_shift_symm {R : Reflection X} {ν : State X} (C : ShiftCompat R ν)
    (f g : C(X, ℝ)) :
    ν (R.θ (C.T f) * g) = ν (R.θ f * C.T g) := by
  calc ν (R.θ (C.T f) * g)
      = ν (C.S (R.θ f) * g) := by rw [C.theta_T]
    _ = ν (C.T (C.S (R.θ f) * g)) := (C.nu_T _).symm
    _ = ν (C.T (C.S (R.θ f)) * C.T g) := by rw [C.T_mul]
    _ = ν (R.θ f * C.T g) := by rw [C.T_S]

#print axioms form_shift_symm

/-- A map that does not increase the supremum norm does not increase it after any number of steps.

DERIVED: no numeral. -/
theorem norm_iterate_le {T : C(X, ℝ) → C(X, ℝ)} (hT : ∀ f, ‖T f‖ ≤ ‖f‖) (f : C(X, ℝ)) (n : ℕ) :
    ‖T^[n] f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply' T k]
      exact le_trans (hT _) ih

#print axioms norm_iterate_le

/-- **⭐ AND THE ORBIT IS BOUNDED** — the other hypothesis `contract_of_bounded_orbit` needs, supplied
rather than assumed.

A state is bounded by the supremum norm (`State.le_norm`), the sup norm is submultiplicative on
`C(X, ℝ)`, and neither the reflection nor the translation increases it — both are precompositions by
a map of the configuration space, which cannot enlarge a supremum. So `‖f‖²` is a bound good for
every power at once, which is the form the contraction theorem consumes.

DERIVED: `‖f‖ * ‖f‖` is the two copies of `f` in the form, derived from `State.le_norm` and
submultiplicativity rather than chosen. No exponent appears in the statement. -/
theorem orbit_bounded_of_state (ν : State X) (R : Reflection X) {T : C(X, ℝ) → C(X, ℝ)}
    (hT : ∀ f, ‖T f‖ ≤ ‖f‖) (hθ : ∀ f, ‖R.θ f‖ ≤ ‖f‖) (f : C(X, ℝ)) (n : ℕ) :
    ν (R.θ (T^[n] f) * T^[n] f) ≤ ‖f‖ * ‖f‖ := by
  have hn : ‖T^[n] f‖ ≤ ‖f‖ := norm_iterate_le hT f n
  calc ν (R.θ (T^[n] f) * T^[n] f)
      ≤ ‖R.θ (T^[n] f) * T^[n] f‖ := ν.le_norm _
    _ ≤ ‖R.θ (T^[n] f)‖ * ‖T^[n] f‖ := norm_mul_le _ _
    _ ≤ ‖f‖ * ‖f‖ :=
        mul_le_mul (le_trans (hθ _) hn) hn (norm_nonneg _) (norm_nonneg _)

#print axioms orbit_bounded_of_state

end Symm

/-! ## 2. ⭐ `T_contract`, from Cauchy–Schwarz alone -/

section Contract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **ONE `T` MOVES ACROSS, AND CAUCHY–SCHWARZ CLOSES.** `aₙ₊₁² ≤ aₙ·aₙ₊₂` — midpoint log-convexity
of the orbit's diagonal.

`T` is a bare function: linearity is never used, only the symmetry of the form for it.

DERIVED: the exponent `2` is the square Cauchy–Schwarz produces; the `1` and `2` in the indices are
one and two translation steps. -/
theorem orbit_log_convex (P : ReflForm A) (T : A → A)
    (hsym : ∀ y z, P.form (T y) z = P.form y (T z)) (x : A) (n : ℕ) :
    P.form (T^[n + 1] x) (T^[n + 1] x) ^ 2
      ≤ P.form (T^[n] x) (T^[n] x) * P.form (T^[n + 2] x) (T^[n + 2] x) := by
  have h2 : T^[n + 2] x = T (T (T^[n] x)) := by
    rw [Function.iterate_succ_apply' T (n + 1), Function.iterate_succ_apply' T n]
  have hmid : P.form (T^[n + 1] x) (T^[n + 1] x) = P.form (T^[n] x) (T^[n + 2] x) := by
    rw [Function.iterate_succ_apply' T n, hsym, h2]
  rw [hmid]
  exact P.cauchy_schwarz _ _

#print axioms orbit_log_convex

/-- **⭐ `T_contract`, PROVED FROM SYMMETRY AND A BOUNDED ORBIT.**

`T_contract` reads like a second assumption about the operator and is not one. On a positive
semidefinite form, symmetry alone forces `aₙ₊₁² ≤ aₙ·aₙ₊₂`; if `a₁` ever exceeded `a₀` the ratios
would be non-decreasing from there on and `aₙ` would grow geometrically, which a bounded orbit
forbids.

**The boundedness hypothesis is where the state enters** — `|ν(g)| ≤ ‖g‖_∞`, and a translation does
not change a supremum. It is genuinely needed: the conclusion is false for an unbounded orbit, which
is why it is a hypothesis and not folded into the statement.

DERIVED: the `0` and `1` are the orbit's first two terms; the `2`s in `a (n+2)`, `a (k+2)` and the
squares are Cauchy–Schwarz's own and the two-step lag `orbit_log_convex` produces; `M` is the
caller's bound. Nothing is chosen. -/
theorem contract_of_bounded_orbit (P : ReflForm A) (T : A → A)
    (hsym : ∀ y z, P.form (T y) z = P.form y (T z)) (x : A) (M : ℝ)
    (hM : ∀ n, P.form (T^[n] x) (T^[n] x) ≤ M) :
    P.form (T x) (T x) ≤ P.form x x := by
  set a : ℕ → ℝ := fun n => P.form (T^[n] x) (T^[n] x) with hadef
  have ha0 : ∀ n, 0 ≤ a n := fun n => P.form_nonneg _
  have hstep : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2) := fun n =>
    orbit_log_convex P T hsym x n
  -- the ratios are non-decreasing, cross-multiplied so no division is needed
  have hmono : ∀ n, a 1 * a n ≤ a 0 * a (n + 1) := by
    intro n
    induction n with
    | zero => exact le_of_eq (by ring)
    | succ k ih =>
        rcases eq_or_lt_of_le (ha0 (k + 1)) with h | h
        · nlinarith [ha0 0, ha0 1, ha0 (k + 2), h.symm]
        · nlinarith [hstep k, ih, ha0 (k + 2), ha0 0, ha0 1, h]
  -- hence `a n` grows at least geometrically, again cross-multiplied
  have hpow : ∀ n, a 1 ^ n * a 0 ≤ a 0 ^ n * a n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hk : (0 : ℝ) ≤ a 0 ^ k := pow_nonneg (ha0 0) k
        calc a 1 ^ (k + 1) * a 0 = a 1 * (a 1 ^ k * a 0) := by ring
          _ ≤ a 1 * (a 0 ^ k * a k) := by nlinarith [ha0 1, ih]
          _ = a 0 ^ k * (a 1 * a k) := by ring
          _ ≤ a 0 ^ k * (a 0 * a (k + 1)) := by nlinarith [hmono k, hk]
          _ = a 0 ^ (k + 1) * a (k + 1) := by ring
  by_contra hcon
  rw [not_le] at hcon
  have hlt : a 0 < a 1 := by
    have h1 : a 1 = P.form (T x) (T x) := by simp [hadef]
    have h0 : a 0 = P.form x x := by simp [hadef]
    rw [h0, h1]
    exact hcon
  have h0pos : 0 < a 0 := by
    rcases eq_or_lt_of_le (ha0 0) with h | h
    · exfalso
      have hs := hstep 0
      nlinarith [ha0 1, ha0 2, h.symm, hlt]
    · exact h
  have key : ∀ n, (a 1 / a 0) ^ n ≤ M / a 0 := by
    intro n
    rw [div_pow, div_le_div_iff₀ (pow_pos h0pos n) h0pos]
    have h1 := hpow n
    have h2 := hM n
    nlinarith [pow_nonneg (ha0 0) n, h0pos]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / a 0) ((one_lt_div h0pos).mpr hlt)
  exact absurd (key n) (not_le.mpr hn)

#print axioms contract_of_bounded_orbit

/-- **THE DEGENERATE CASE IS NOT AN EXCEPTION.** A null vector stays null: if `⟨x,x⟩ = 0` then
`⟨Tx,Tx⟩ = 0` too, by Cauchy–Schwarz and symmetry, with no boundedness needed.

Worth separating because `contract_of_bounded_orbit`'s proof has to survive `a₀ = 0`, and this says
the conclusion there is not merely an inequality between zeros by accident.

DERIVED: the `0` is the null value; the exponent `2` is Cauchy–Schwarz's square. Nothing is chosen. -/
theorem null_is_preserved (P : ReflForm A) (T : A → A)
    (hsym : ∀ y z, P.form (T y) z = P.form y (T z)) {x : A} (hx : P.form x x = 0) :
    P.form (T x) (T x) = 0 := by
  have hcs := P.cauchy_schwarz x (T (T x))
  have hmid : P.form (T x) (T x) = P.form x (T (T x)) := hsym x (T x)
  rw [hx, zero_mul] at hcs
  have hsq : P.form x (T (T x)) ^ 2 ≤ 0 := hcs
  have : P.form x (T (T x)) = 0 := by nlinarith [sq_nonneg (P.form x (T (T x)))]
  rw [hmid, this]

#print axioms null_is_preserved

end Contract

end MassGap.SchwarzIteration
