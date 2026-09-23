import Mathlib
import MassGap.Transfer
import MassGap.InfiniteReflection

/-!
# MassGap.SchwarzIteration — form symmetry for a shift, and contraction from a bounded orbit

Two sections, on two different carriers.

## Section 1, on `C(X, ℝ)` for a compact `X`

`ShiftCompat R ν` bundles a forward shift `T`, a backward shift `S`, multiplicativity of `T`,
`T ∘ S = id`, the conjugation `θ ∘ T = S ∘ θ`, and invariance of the state `ν` under `T`. From it,
`form_shift_symm` proves `ν (θ (T f) · g) = ν (θ f · T g)` for all `f, g : C(X, ℝ)`: the identity in
the shape `Transfer.TransferData.T_symm` asks for, stated for `ν` on the whole of `C(X, ℝ)` rather
than for a `form` on a submodule carrier. Restricting to a carrier is `MassGap.TransferAssembly`'s
work.

`norm_iterate_le` and `orbit_bounded_of_state` supply the uniform orbit bound used in section 2:
if neither `T` nor `θ` increases the supremum norm, then `ν (θ (Tⁿf) · Tⁿf) ≤ ‖f‖²` for every `n`,
using `State.le_norm` and submultiplicativity of the sup norm.

## Section 2, on an abstract `ℝ`-module `A` with a `Transfer.ReflForm`

Writing `aₙ = P.form (Tⁿx) (Tⁿx)`, moving one `T` across the form by `hsym` turns
`aₙ₊₁ = P.form (Tⁿx) (Tⁿ⁺²x)`, and Cauchy–Schwarz gives `aₙ₊₁² ≤ aₙ aₙ₊₂` (`orbit_log_convex`).
`contract_of_bounded_orbit` runs that forward: with a uniform bound `M` on the whole orbit, `a₁ ≤ a₀`,
i.e. `P.form (Tx) (Tx) ≤ P.form x x`. The boundedness hypothesis is used, not decorative — on `A = ℝ`
with `form x y = x·y` and `T x = 2x` the form is symmetric and positive semidefinite while
`⟨Tx,Tx⟩ = 4x² > x²`.

`null_is_preserved` covers the degenerate case separately: `P.form x x = 0` gives
`P.form (Tx) (Tx) = 0`, from Cauchy–Schwarz and `hsym`, with no boundedness hypothesis.

`T` is a bare function throughout section 2; linearity is never used, only `hsym`. Positivity of the
form is consumed from the `ReflForm` structure, not established here.
-/

namespace MassGap.SchwarzIteration

open MassGap.Transfer

/-! ## 1. `T_symm`, from the reflection conjugating the shift -/

section Symm

open MassGap.InfiniteReflection MassGap.DLRLimit

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The compatibility a time translation needs for `form_shift_symm`, relative to a reflection `R`
and a state `ν` on `C(X, ℝ)`. It carries two `ℝ`-linear maps, the forward shift `T` and the backward
shift `S`, and four conditions: `T` is multiplicative (`T_mul`), `T ∘ S = id` (`T_S`), the reflection
conjugates forward to backward (`theta_T`), and `ν` is `T`-invariant (`nu_T`).

`T_S` states only the one-sided inverse, but the structure implies the other: applying `θ` to
`theta_T` and using involutivity gives `T = θ ∘ S ∘ θ`, hence `S ∘ T = id`, proved as
`TransferAssembly.shift_inverse_is_two_sided`. So the translation is invertible — satisfiable on `ℤ`,
where `InfiniteShift.ishiftConf` is a bijection, and not on a half-line of `ℕ`.

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

/-- `ν (θ (T f) · g) = ν (θ f · T g)` for all `f, g : C(X, ℝ)`, given a `ShiftCompat R ν`. Four
rewrites, one per field:

    ν(θ(Tf)·g) = ν(S(θf)·g)          theta_T
               = ν(T(S(θf)·g))       nu_T
               = ν(T(S(θf))·T g)     T_mul
               = ν(θf·T g)           T_S.

The conclusion is about `ν` on all of `C(X, ℝ)`, not about a `form` on a carrier; producing
`TransferData.T_symm` from it is a separate restriction step.

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

/-- `ν (θ (T^[n] f) · T^[n] f) ≤ ‖f‖ * ‖f‖`, for every `n`, given that neither `T` nor `R.θ`
increases the supremum norm. `State.le_norm` bounds the state by the norm, `norm_mul_le` splits the
product, and `norm_iterate_le` bounds each factor by `‖f‖`. The bound is uniform in `n`, which is the
shape `contract_of_bounded_orbit` consumes as its `M`.

DERIVED: `‖f‖ * ‖f‖` is the two copies of `f` in the form, from `State.le_norm` and
submultiplicativity. No numeral appears in the statement. -/
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

/-! ## 2. Contraction, from Cauchy–Schwarz and a bounded orbit -/

section Contract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- Midpoint log-convexity of the orbit diagonal: with `a n = P.form (T^[n] x) (T^[n] x)`,
`a (n+1) ^ 2 ≤ a n * a (n+2)`. One `T` moves across the form by `hsym`, turning `a (n+1)` into
`P.form (T^[n] x) (T^[n+2] x)`, and `P.cauchy_schwarz` closes it. `T` is a bare function; linearity
is never used, only `hsym`.

DERIVED: the exponent `2` is the square Cauchy–Schwarz produces; the `1` and the `2` in the iterate
indices are one and two translation steps, the spacing `hsym` creates. -/
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

/-- `P.form (T x) (T x) ≤ P.form x x`, from the form's symmetry for `T` and a uniform bound `M` on
the whole orbit diagonal. By contradiction: if `a 1 > a 0`, `orbit_log_convex` makes the ratios
non-decreasing, so `a n` grows at least like `(a 1 / a 0)^n`, and `pow_unbounded_of_one_lt`
contradicts `hM`. Every step is cross-multiplied rather than divided, so the intermediate inequalities
need no positivity side condition.

`hM` must hold at every `n`, not merely eventually. The hypothesis cannot be dropped: on `A = ℝ` with
`form x y = x·y` and `T x = 2x` the form is symmetric and positive semidefinite while
`⟨Tx,Tx⟩ = 4x² > x²`. Positivity of the form comes from the `ReflForm` structure, which this theorem
consumes rather than supplies.

DERIVED: no numeral. `M` is the caller's orbit bound, and the numerals in the proof's index arithmetic
do not reach the statement. -/
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

/-- A null vector stays null: `P.form x x = 0` gives `P.form (T x) (T x) = 0`. Cauchy–Schwarz at
`(x, T (T x))` has its right side killed by `hx`, so `P.form x (T (T x))` squares to at most zero and
vanishes; `hsym` identifies it with `P.form (T x) (T x)`. No boundedness hypothesis is needed, in
contrast to `contract_of_bounded_orbit`.

DERIVED: the `0` in the hypothesis is the null value of the form at `x`, and the `0` in the
conclusion is the same value one step along. -/
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
