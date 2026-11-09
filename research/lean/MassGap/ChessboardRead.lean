import Mathlib
import MassGap.GNSCompare
import MassGap.PeriodicContent

/-!
# MassGap.ChessboardRead — the read from one lag, by the Hankel step of reflection positivity

Reflection positivity and `GNSHilbert.PositiveTransfer` together make the transfer profile
`b(c) = D.form x (Tᶜ x)` of every observable log-convex, `b(c + 1)² ≤ b(c) · b(c + 2)`
(`lagProfile_log_convex`). When the outer lags `c`, `c + 2` are even this is Cauchy–Schwarz for the
reflection form itself; when they are odd it is Cauchy–Schwarz for the form
`(y, z) ↦ D.form y (T z)` (`tForm`), which is positive exactly by `PositiveTransfer` — at the Wilson
data, reflection positivity about a link plane
(`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive`). Iterated, it is the chessboard
step in the time direction, `b(1)ᵐ · b(0) ≤ b(0)ᵐ · b(m)` (`pow_mul_le_of_log_convex`): the number
of steps does not reach the rate.

## What it gives

1. `gapAt_iff_lag`: under `PositiveTransfer D` and `0 ≤ r`, `TransferGap.GapAt D r` holds exactly
   when, at one lag `m ≠ 0`, every observable orthogonal to the vacuum has
   `D.form x (Tᵐ x) ≤ rᵐ · D.form x x`. The rate is the same on both sides and the lag is
   immaterial: the single-lag inequality at any one lag `m ≠ 0` and rate `r` is `GapAt D r`
   restated, not a weaker input.
2. `opT_contracts_of_lag`: the same single-lag inequality contracts the vacuum complement of the
   completion by `r`.
3. On the periodic lattices: `TorusLagClear τ p hN β m r` is the single-lag inequality for the
   connected reflected-shifted pairing `PeriodicReduce.torusConn`, with slack, along
   `periodicUltra hN β`. On the lattices only the direction from `TorusLagClear` to `GapAt` at the
   periodic data is proved (`periodic_form_lag_of_torusLagClear`, then `gapAt_of_lag`).
   `periodic_clayGapAt_of_torusLag` gives, at `2 ≤ N`, `0 ≤ β`, a lag `m ≠ 0` and `0 < r < 1`,
   `PeriodicContent.PeriodicClayGapAt τ p hN β r` at the lag's own rate.
   `antipodal_rate_pow` computes that `r = e^{−20/(2(k + 1))}` has antipodal ratio `r^{k+1} = e^{−10}`.

## Scope

On the transfer form the single-lag inequality is `GapAt` at the same rate (`gapAt_iff_lag`): the
gap restated, not a weaker input, at any one lag. On the periodic lattices only
`TorusLagClear ⇒ GapAt` is proved. Nothing here proves either at any positive coupling.

The inputs the step consumes are positivity of the reflection form and `PositiveTransfer`. The
identity transfer has both and every profile log-convex, and there the single-lag bound at a rate
below one forces the vacuum complement to be null (`lag_forces_null_of_T_eq_id`): at `x` itself the
hypothesis already reads `D.form x x ≤ rᵐ · D.form x x`. So those inputs alone give no rate below
one, and the bound on a vacuum complement that is not null needs `T ≠ id`.
-/

namespace MassGap.ChessboardRead

open MassGap MassGap.Transfer MassGap.GNSHilbert

/-! ## 1. The chessboard step on a sequence -/

section Sequence

/-- **Iterated Schwarz on a log-convex sequence.** For `b` nonnegative with
`b (n + 1) ^ 2 ≤ b n * b (n + 2)` at every `n`: `b 1 ^ m * b 0 ≤ b 0 ^ m * b m` at every `m`. Every
ratio `b (n + 1) / b n` is at least the first one, `b 1 / b 0` (`hmono`, cross-multiplied so no
division occurs), so `b m` is at least `b 0` times the `m`-th power of the first ratio. The same argument sits inside
`SchwarzIteration.contract_of_bounded_orbit`; here it is stated on its own.

DERIVED: `0` is the lower bound on each term and the base index; `1` and `2` are the one- and
two-step index shifts of the Hankel minor, and `2` is also the exponent of the square Cauchy–Schwarz
produces. -/
theorem pow_mul_le_of_log_convex {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hlc : ∀ n, b (n + 1) ^ 2 ≤ b n * b (n + 2)) (m : ℕ) :
    b 1 ^ m * b 0 ≤ b 0 ^ m * b m := by
  have hmono : ∀ n, b 1 * b n ≤ b 0 * b (n + 1) := by
    intro n
    induction n with
    | zero =>
        show b 1 * b 0 ≤ b 0 * b 1
        exact le_of_eq (mul_comm _ _)
    | succ k ih =>
        show b 1 * b (k + 1) ≤ b 0 * b (k + 2)
        rcases eq_or_lt_of_le (hb (k + 1)) with h | h
        · nlinarith [hb 0, hb 1, hb (k + 2), h.symm]
        · nlinarith [hlc k, ih, hb (k + 2), hb 0, hb 1, h]
  induction m with
  | zero => simp
  | succ k ih =>
      have hk : (0 : ℝ) ≤ b 0 ^ k := pow_nonneg (hb 0) k
      calc b 1 ^ (k + 1) * b 0 = b 1 * (b 1 ^ k * b 0) := by ring
        _ ≤ b 1 * (b 0 ^ k * b k) := mul_le_mul_of_nonneg_left ih (hb 1)
        _ = b 0 ^ k * (b 1 * b k) := by ring
        _ ≤ b 0 ^ k * (b 0 * b (k + 1)) := mul_le_mul_of_nonneg_left (hmono k) hk
        _ = b 0 ^ (k + 1) * b (k + 1) := by ring

#print axioms pow_mul_le_of_log_convex

/-- **One lag bounds the first step.** For `b` nonnegative and log-convex (as in
`pow_mul_le_of_log_convex`), `m ≠ 0`, `0 ≤ r` and `b m ≤ r ^ m * b 0`: `b 1 ≤ r * b 0`. At `b 0 = 0`
the minor `b 1 ^ 2 ≤ b 0 * b 2` forces `b 1 = 0`; otherwise `b 1 ^ m ≤ (r * b 0) ^ m`, and the `m`-th
power is monotone on `[0, ∞)`.

DERIVED: `0` is the lower bound on each term and on `r`, the base index, and the excluded lag; `1`
and `2` are the Hankel minor's index shifts, and `2` is also the exponent of its square. -/
theorem le_mul_of_log_convex_lag {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hlc : ∀ n, b (n + 1) ^ 2 ≤ b n * b (n + 2)) {m : ℕ} (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (hlag : b m ≤ r ^ m * b 0) : b 1 ≤ r * b 0 := by
  rcases eq_or_lt_of_le (hb 0) with h0 | h0
  · have h1 : b 1 ^ 2 ≤ b 0 * b 2 := hlc 0
    rw [← h0, zero_mul] at h1
    rw [← h0, mul_zero]
    nlinarith [hb 1, h1]
  · have h2 : b 1 ^ m * b 0 ≤ (r * b 0) ^ m * b 0 := by
      calc b 1 ^ m * b 0 ≤ b 0 ^ m * b m := pow_mul_le_of_log_convex hb hlc m
        _ ≤ b 0 ^ m * (r ^ m * b 0) := mul_le_mul_of_nonneg_left hlag (pow_nonneg (hb 0) m)
        _ = (r * b 0) ^ m * b 0 := by rw [mul_pow]; ring
    have h3 : b 1 ^ m ≤ (r * b 0) ^ m := le_of_mul_le_mul_right h2 h0
    exact le_of_pow_le_pow_left₀ hm (mul_nonneg hr h0.le) h3

#print axioms le_mul_of_log_convex_lag

/-- **A limit inequality from slack.** If `u → a` and `v → b` along a non-trivial filter and, for
every `ε > 0`, eventually `u n ≤ v n + ε`, then `a ≤ b`: at `a > b` half the difference is a slack the
limit contradicts.

DERIVED: `0` is the sign of each slack `ε`. -/
theorem le_of_slack {u v : ℕ → ℝ} {l : Filter ℕ} [l.NeBot] {a b : ℝ}
    (hu : Filter.Tendsto u l (nhds a)) (hv : Filter.Tendsto v l (nhds b))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, u n ≤ v n + ε) : a ≤ b := by
  by_contra hneg
  have hlt : b < a := not_le.mp hneg
  have hε : 0 < (a - b) / 2 := by linarith
  have hv' : Filter.Tendsto (fun n => v n + (a - b) / 2) l (nhds (b + (a - b) / 2)) :=
    hv.add tendsto_const_nhds
  have hle : a ≤ b + (a - b) / 2 := le_of_tendsto_of_tendsto hu hv' (h _ hε)
  linarith

#print axioms le_of_slack

end Sequence

/-! ## 2. The profile of an observable, and the gap from one lag -/

section Profile

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The transfer profile of an observable: `lagProfile D x n = D.form x (Tⁿ x)`, the reflected
pairing of `x` with its `n`-th translate.

DERIVED: no numeral occurs. -/
noncomputable def lagProfile (D : TransferData A) (x : A) (n : ℕ) : ℝ :=
  D.form x ((D.T ^ n) x)

/-- The profile at `i + j` splits across the form: `D.form x (T^{i+j} x) = D.form (Tⁱ x) (Tʲ x)`.
`TransferGap.form_pow_symm` moves `Tⁱ` into the left slot.

DERIVED: no numeral occurs. -/
theorem lagProfile_add (D : TransferData A) (x : A) (i j : ℕ) :
    lagProfile D x (i + j) = D.form ((D.T ^ i) x) ((D.T ^ j) x) := by
  show D.form x ((D.T ^ (i + j)) x) = D.form ((D.T ^ i) x) ((D.T ^ j) x)
  rw [MassGap.TransferGap.form_pow_symm D i x ((D.T ^ j) x), pow_add, Module.End.mul_apply]

#print axioms lagProfile_add

/-- `T^{i+1} x = T (Tⁱ x)`.

DERIVED: `1` is one further step. -/
theorem T_pow_succ_apply (D : TransferData A) (i : ℕ) (x : A) :
    (D.T ^ (i + 1)) x = D.T ((D.T ^ i) x) := by
  rw [pow_succ', Module.End.mul_apply]

#print axioms T_pow_succ_apply

/-- **The form of the transfer operator**, `(y, z) ↦ D.form y (T z)`, as a `Transfer.ReflForm`. It is
symmetric by `T_symm` and the symmetry of `D.form`, additive and homogeneous because `D.form` is, and
nonnegative exactly by `GNSHilbert.PositiveTransfer D`.

DERIVED: no numeral occurs. -/
noncomputable def tForm (D : TransferData A) (hP : PositiveTransfer D) : ReflForm A where
  form y z := D.form y (D.T z)
  form_symm y z := (D.T_symm y z).symm.trans (D.form_symm (D.T y) z)
  form_add_left x y z := D.form_add_left x y (D.T z)
  form_smul_left c y z := D.form_smul_left c y (D.T z)
  form_nonneg y := hP y

/-- The profile at an even lag is a diagonal of the reflection form:
`D.form x (T^{2j} x) = D.form (Tʲ x) (Tʲ x)`.

DERIVED: `2` is the doubling of `j` steps, half in each slot. -/
theorem lagProfile_even (D : TransferData A) (x : A) (j : ℕ) :
    lagProfile D x (2 * j) = D.form ((D.T ^ j) x) ((D.T ^ j) x) :=
  (congrArg (lagProfile D x) (show 2 * j = j + j by omega)).trans (lagProfile_add D x j j)

#print axioms lagProfile_even

/-- The profile at an odd lag is a diagonal of `tForm`:
`D.form x (T^{2j+1} x) = D.form (Tʲ x) (T (Tʲ x))`.

DERIVED: `2` is the doubling of `j` steps and `1` the middle step `tForm` carries. -/
theorem lagProfile_odd (D : TransferData A) (x : A) (j : ℕ) :
    lagProfile D x (2 * j + 1) = D.form ((D.T ^ j) x) (D.T ((D.T ^ j) x)) := by
  rw [← T_pow_succ_apply D j x]
  exact (congrArg (lagProfile D x) (show 2 * j + 1 = j + (j + 1) by omega)).trans
    (lagProfile_add D x j (j + 1))

#print axioms lagProfile_odd

/-- **The profile is nonnegative.** At an even lag it is a diagonal of the reflection form
(`form_nonneg`); at an odd lag a diagonal of `tForm` (`PositiveTransfer`).

DERIVED: `0` is the lower bound asserted. -/
theorem lagProfile_nonneg (D : TransferData A) (hP : PositiveTransfer D) (x : A) (n : ℕ) :
    0 ≤ lagProfile D x n := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
  · subst hj
    rw [lagProfile_even]
    exact D.form_nonneg _
  · subst hj
    rw [lagProfile_odd]
    exact hP _

#print axioms lagProfile_nonneg

/-- **The profile is log-convex: the Hankel `2 × 2` minors are nonnegative.**
`b (n + 1) ^ 2 ≤ b n * b (n + 2)` for `b = lagProfile D x`. At `n = 2j` it is Cauchy–Schwarz for the
reflection form at `(Tʲ x, T^{j+1} x)`; at `n = 2j + 1` it is Cauchy–Schwarz for `tForm` at the same
pair, which is where `PositiveTransfer` enters.

DERIVED: `1` and `2` are the one- and two-step shifts of the minor; `2` is also the exponent of the
square. -/
theorem lagProfile_log_convex (D : TransferData A) (hP : PositiveTransfer D) (x : A) (n : ℕ) :
    lagProfile D x (n + 1) ^ 2 ≤ lagProfile D x n * lagProfile D x (n + 2) := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
  · subst hj
    have e0 : lagProfile D x (2 * j) = D.form ((D.T ^ j) x) ((D.T ^ j) x) :=
      lagProfile_even D x j
    have e1 : lagProfile D x (2 * j + 1) = D.form ((D.T ^ j) x) ((D.T ^ (j + 1)) x) :=
      (congrArg (lagProfile D x) (show 2 * j + 1 = j + (j + 1) by omega)).trans
        (lagProfile_add D x j (j + 1))
    have e2 : lagProfile D x (2 * j + 2)
        = D.form ((D.T ^ (j + 1)) x) ((D.T ^ (j + 1)) x) :=
      (congrArg (lagProfile D x) (show 2 * j + 2 = 2 * (j + 1) by omega)).trans
        (lagProfile_even D x (j + 1))
    rw [e1, e0, e2]
    exact D.toReflForm.cauchy_schwarz _ _
  · subst hj
    have e1 : lagProfile D x (2 * j + 1) = (tForm D hP).form ((D.T ^ j) x) ((D.T ^ j) x) :=
      lagProfile_odd D x j
    have e2 : lagProfile D x (2 * j + 1 + 1)
        = (tForm D hP).form ((D.T ^ j) x) ((D.T ^ (j + 1)) x) := by
      have h := lagProfile_add D x j (j + 1 + 1)
      rw [T_pow_succ_apply D (j + 1) x] at h
      exact (congrArg (lagProfile D x) (show 2 * j + 1 + 1 = j + (j + 1 + 1) by omega)).trans h
    have e3 : lagProfile D x (2 * j + 1 + 2)
        = (tForm D hP).form ((D.T ^ (j + 1)) x) ((D.T ^ (j + 1)) x) :=
      (congrArg (lagProfile D x) (show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega)).trans
        (lagProfile_odd D x (j + 1))
    rw [e2, e1, e3]
    exact (tForm D hP).cauchy_schwarz _ _

#print axioms lagProfile_log_convex

/-- **The Rayleigh quotient from one lag, for one observable.** Under `PositiveTransfer D`, `m ≠ 0`,
`0 ≤ r` and `D.form x (Tᵐ x) ≤ rᵐ · D.form x x`: `D.form x (T x) ≤ r · D.form x x`.
`le_mul_of_log_convex_lag` on `lagProfile D x`.

DERIVED: `0` is the excluded lag and the lower bound on `r`. -/
theorem rayleigh_of_lag (D : TransferData A) (hP : PositiveTransfer D) (x : A) {m : ℕ}
    (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r) (hlag : D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x) :
    D.form x (D.T x) ≤ r * D.form x x := by
  have h0 : lagProfile D x 0 = D.form x x := by
    show D.form x ((D.T ^ 0) x) = D.form x x
    rw [pow_zero, Module.End.one_apply]
  have h1 : lagProfile D x 1 = D.form x (D.T x) := by
    show D.form x ((D.T ^ 1) x) = D.form x (D.T x)
    rw [pow_one]
  have hlag' : lagProfile D x m ≤ r ^ m * lagProfile D x 0 := by
    rw [h0]
    exact hlag
  have h := le_mul_of_log_convex_lag (lagProfile_nonneg D hP x) (lagProfile_log_convex D hP x)
    hm hr hlag'
  rw [h1, h0] at h
  exact h

#print axioms rayleigh_of_lag

/-- **The gap from one lag.** Under `PositiveTransfer D`, `m ≠ 0` and `0 ≤ r`: if every `x` with
`D.form x D.vac = 0` has `D.form x (Tᵐ x) ≤ rᵐ · D.form x x`, then `TransferGap.GapAt D r`.
`rayleigh_of_lag` brings the lag down to one, `D.form x (T x) ≤ r · D.form x x`. From lag one to
`GapAt` is taken on the module: at `x`, `rayleigh_of_lag` at `x` and at `T x` (also orthogonal to the
vacuum, `TransferGap.orth_invariant`) give `⟨x, Tx⟩ ≤ r⟨x, x⟩` and `⟨Tx, T²x⟩ ≤ r⟨Tx, Tx⟩`;
Cauchy–Schwarz for `tForm` at `(x, T x)` is `⟨Tx, Tx⟩² ≤ ⟨x, Tx⟩ · ⟨Tx, T²x⟩`, so
`⟨Tx, Tx⟩ ≤ r⟨x, Tx⟩ ≤ r²⟨x, x⟩`.

DERIVED: `0` is the excluded lag, the lower bound on `r`, and the vacuum pairing. -/
theorem gapAt_of_lag (D : TransferData A) (hP : PositiveTransfer D) {m : ℕ} (hm : m ≠ 0)
    {r : ℝ} (hr : 0 ≤ r)
    (hlag : ∀ x : A, D.form x D.vac = 0 → D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x) :
    MassGap.TransferGap.GapAt D r := by
  intro x hx
  have hR0 : D.form x (D.T x) ≤ r * D.form x x := rayleigh_of_lag D hP x hm hr (hlag x hx)
  have hTx : D.form (D.T x) D.vac = 0 := MassGap.TransferGap.orth_invariant D hx
  have hR1 : D.form (D.T x) (D.T (D.T x)) ≤ r * D.form (D.T x) (D.T x) :=
    rayleigh_of_lag D hP (D.T x) hm hr (hlag (D.T x) hTx)
  have hcs := (tForm D hP).cauchy_schwarz x (D.T x)
  have e1 : (tForm D hP).form x (D.T x) = D.form (D.T x) (D.T x) := (D.T_symm x (D.T x)).symm
  have e2 : (tForm D hP).form x x = D.form x (D.T x) := rfl
  have e3 : (tForm D hP).form (D.T x) (D.T x) = D.form (D.T x) (D.T (D.T x)) := rfl
  rw [e1, e2, e3] at hcs
  have hb2 : 0 ≤ D.form (D.T x) (D.T x) := D.form_nonneg _
  have hb1 : 0 ≤ D.form x (D.T x) := hP x
  have hb0 : 0 ≤ D.form x x := D.form_nonneg x
  rcases eq_or_lt_of_le hb2 with h2 | h2
  · rw [← h2]
    exact mul_nonneg (sq_nonneg r) hb0
  · have h3 : D.form (D.T x) (D.T x) ^ 2 ≤ D.form x (D.T x) * (r * D.form (D.T x) (D.T x)) :=
      le_trans hcs (mul_le_mul_of_nonneg_left hR1 hb1)
    have h4 : D.form (D.T x) (D.T x) ≤ r * D.form x (D.T x) := by
      by_contra hc
      push_neg at hc
      have h5 := mul_lt_mul_of_pos_right hc h2
      nlinarith [h3, h5]
    nlinarith [mul_le_mul_of_nonneg_left hR0 hr, h4]

#print axioms gapAt_of_lag

/-- **One lag from the gap.** Under `TransferGap.GapAt D r` with `0 ≤ r`, every `x` with
`D.form x D.vac = 0` has `D.form x (Tᵐ x) ≤ rᵐ · D.form x x` at every `m`. At `m = 2j` it is
`TransferGap.gap_pow`; at `m = 2j + 1`, Cauchy–Schwarz for the reflection form at `(Tʲ x, T^{j+1} x)`
and `gap_pow` at `j` and `j + 1`. No positivity of `T` is used.

DERIVED: `0` is the lower bound on `r` and the vacuum pairing. -/
theorem lag_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (hg : MassGap.TransferGap.GapAt D r) (m : ℕ) (x : A) (hx : D.form x D.vac = 0) :
    D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x := by
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  · subst hj
    have e : D.form x ((D.T ^ (2 * j)) x) = D.form ((D.T ^ j) x) ((D.T ^ j) x) :=
      lagProfile_even D x j
    rw [e]
    exact MassGap.TransferGap.gap_pow D hr hg j x hx
  · subst hj
    have e : D.form x ((D.T ^ (2 * j + 1)) x) = D.form ((D.T ^ j) x) ((D.T ^ (j + 1)) x) :=
      (congrArg (lagProfile D x) (show 2 * j + 1 = j + (j + 1) by omega)).trans
        (lagProfile_add D x j (j + 1))
    have hcs := D.toReflForm.cauchy_schwarz ((D.T ^ j) x) ((D.T ^ (j + 1)) x)
    have ha := MassGap.TransferGap.gap_pow D hr hg j x hx
    have hb := MassGap.TransferGap.gap_pow D hr hg (j + 1) x hx
    have hsq : D.form ((D.T ^ j) x) ((D.T ^ (j + 1)) x) ^ 2
        ≤ (r ^ (2 * j + 1) * D.form x x) ^ 2 :=
      calc D.form ((D.T ^ j) x) ((D.T ^ (j + 1)) x) ^ 2
          ≤ D.form ((D.T ^ j) x) ((D.T ^ j) x)
              * D.form ((D.T ^ (j + 1)) x) ((D.T ^ (j + 1)) x) := hcs
        _ ≤ (r ^ (2 * j) * D.form x x) * (r ^ (2 * (j + 1)) * D.form x x) :=
            mul_le_mul ha hb (D.form_nonneg _) (mul_nonneg (pow_nonneg hr _) hxx)
        _ = (r ^ (2 * j + 1) * D.form x x) ^ 2 := by ring
    rw [e]
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (pow_nonneg hr _) hxx) hsq

#print axioms lag_of_gapAt

/-- **The gap is one lag.** Under `PositiveTransfer D`, `m ≠ 0` and `0 ≤ r`:
`TransferGap.GapAt D r` holds exactly when every `x` orthogonal to the vacuum has
`D.form x (Tᵐ x) ≤ rᵐ · D.form x x`. `lag_of_gapAt` and `gapAt_of_lag`; the rate is the same on both
sides and the lag is any one lag.

DERIVED: `0` is the excluded lag, the lower bound on `r`, and the vacuum pairing. -/
theorem gapAt_iff_lag (D : TransferData A) (hP : PositiveTransfer D) {m : ℕ} (hm : m ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    MassGap.TransferGap.GapAt D r ↔
      ∀ x : A, D.form x D.vac = 0 → D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x :=
  ⟨fun hg x hx => lag_of_gapAt D hr hg m x hx, gapAt_of_lag D hP hm hr⟩

#print axioms gapAt_iff_lag

/-- **At `T = id` the single-lag bound forces a null vacuum complement.** At `T = id` the reflection
form is positive, `T` is positive (`GNSHilbert.positiveTransfer_of_T_eq_id`) and every profile is
log-convex; there the single-lag bound at any rate `0 ≤ r < 1` forces every observable orthogonal to
the vacuum to be null. The hypothesis at `x` itself already reads `D.form x x ≤ rᵐ · D.form x x`,
since `Tᵐ x = x`; the proof goes through `gapAt_of_lag`, then `TransferGap.identity_fails_gap`. So
the Hankel step's inputs give no rate below one, and the bound on a vacuum complement that is not
null needs `T ≠ id`.

DERIVED: `0` is the excluded lag, the lower bound on `r`, the vacuum pairing, and the null value
concluded; `1` is the rate the bound must beat. -/
theorem lag_forces_null_of_T_eq_id (D : TransferData A) (hT : ∀ z : A, D.T z = z) {m : ℕ}
    (hm : m ≠ 0) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hlag : ∀ x : A, D.form x D.vac = 0 → D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x)
    (x : A) (hx : D.form x D.vac = 0) : D.form x x = 0 :=
  MassGap.TransferGap.identity_fails_gap D hT hr0 hr
    (gapAt_of_lag D (MassGap.GNSHilbert.positiveTransfer_of_T_eq_id D hT) hm hr0 hlag) x hx

#print axioms lag_forces_null_of_T_eq_id

end Profile

section Mixture

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end Mixture

/-! ## 3. The vacuum complement contracts from one lag -/

section Reads

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **One lag contracts the vacuum complement of the completion.** Under the hypotheses of
`gapAt_of_lag`, `‖opT D y‖ ≤ r ‖y‖` for every `y` orthogonal to the vacuum
(`GNSCompare.gapAt_iff_opT_contracts`).

DERIVED: `0` is the excluded lag, the lower bound on `r`, and the vacuum pairing. -/
theorem opT_contracts_of_lag (D : TransferData A) (hP : PositiveTransfer D) {m : ℕ} (hm : m ≠ 0)
    {r : ℝ} (hr : 0 ≤ r)
    (hlag : ∀ x : A, D.form x D.vac = 0 → D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x) :
    ∀ y : H D.toReflForm, inner ℂ (Omega D.toReflForm D.vac) y = (0 : ℂ) →
      ‖opT D y‖ ≤ r * ‖y‖ :=
  (MassGap.GNSCompare.gapAt_iff_opT_contracts D hr).mp (gapAt_of_lag D hP hm hr hlag)

#print axioms opT_contracts_of_lag

end Reads

/-! ## 4. On the periodic lattices -/

section Periodic

variable {N : ℕ}

/-- The gauge-invariant transfer form at the periodic state, on the diagonal:
`D.form x x = ν(θx · x)`, `D = periodicGaugeInvData τ p hN β`, `ν = periodicState hN β`. By
definition of the assembled form.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane. -/
theorem periodic_form_diag (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)) :
    (MassGap.PeriodicState.periodicGaugeInvData τ p hN β).form x x
      = MassGap.PeriodicState.periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
          (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := rfl

#print axioms periodic_form_diag

/-- **The single-lag input, on the periodic lattices.** At coupling `β`, lag `m` and rate `r`: for
every gauge-invariant half-space observable `x` and every slack `ε > 0`, the set of `j` with

    torusConn τ p hN β j x m  ≤  rᵐ · torusConn τ p hN β j x 0 + ε

belongs to `periodicUltra hN β` — the connected reflected-shifted pairing of `x` at lag `m`, in the
periodic Wilson state of extent `2(j + 1)`, at most `rᵐ` times its lag-zero value. One inequality per
observable, between two connected pairings of `x`. At `0 ≤ β`, `0 ≤ r` and any lag `m ≠ 0` it gives
`TransferGap.GapAt` at the periodic data at the same rate `r` (`periodic_form_lag_of_torusLagClear`,
then `gapAt_of_lag`); the converse on the lattices is
`WeakCouplingWindow.torusLagClear_of_gapAt`, and `WeakCouplingWindow.torusLagClear_iff_gapAt` states both. On the
transfer form the single-lag inequality is `GapAt` at the same rate (`gapAt_iff_lag`), so this is the gap
restated on the lattices, and every lag `m ≠ 0` at rate `r` gives the same conclusion. At
`torusLagClear_of_atTop` derives it from the same inequality for all large `j`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the sign of the slack, and
the contact lag. -/
def TorusLagClear (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (m : ℕ) (r : ℝ) : Prop :=
  ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in ((MassGap.PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
        MassGap.PeriodicReduce.torusConn τ p hN β j x m
          ≤ r ^ m * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε

/-- **The single-lag input from every large periodic lattice.** The same inequality for all large `j`
gives `TorusLagClear`: `periodicUltra hN β` is finer than `atTop`
(`PeriodicState.periodicUltra_le`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the sign of the slack, and
the contact lag. -/
theorem torusLagClear_of_atTop (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (m : ℕ) (r : ℝ)
    (h : ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in Filter.atTop,
        MassGap.PeriodicReduce.torusConn τ p hN β j x m
          ≤ r ^ m * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε) :
    TorusLagClear τ p hN β m r :=
  fun x hx ε hε => (h x hx ε hε).filter_mono (MassGap.PeriodicState.periodicUltra_le hN β)

#print axioms torusLagClear_of_atTop

/-- **The single-lag input at the periodic state.** Under `TorusLagClear τ p hN β m r`, every
gauge-invariant half-space observable `x` has, at `ν = periodicState hN β`,
`ν(θx · Sᵐx) − ν(θx)·ν(Sᵐx) ≤ rᵐ · (ν(θx · x) − ν(θx)·ν(x))`. Both connected pairings converge along
`periodicUltra hN β` (`PeriodicReduce.tendsto_torusConn`), and `le_of_slack` closes it.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane. -/
theorem periodic_conn_le_of_torusLagClear (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (m : ℕ)
    (r : ℝ) (h : TorusLagClear τ p hN β m r)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hx : x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p) :
    MassGap.PeriodicState.periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)
        - MassGap.PeriodicState.periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          * MassGap.PeriodicState.periodicState hN β
              ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)
      ≤ r ^ m * (MassGap.PeriodicState.periodicState hN β
            (MassGap.LatticeReflection.ireflObs τ (2 * p) x * x)
          - MassGap.PeriodicState.periodicState hN β
              (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
            * MassGap.PeriodicState.periodicState hN β x) := by
  haveI : ((MassGap.PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (MassGap.PeriodicState.periodicUltra hN β).neBot'
  exact le_of_slack (MassGap.PeriodicReduce.tendsto_torusConn τ p hN β x m)
    ((MassGap.PeriodicReduce.tendsto_torusConn τ p hN β x 0).const_mul (r ^ m)) (h x hx)

#print axioms periodic_conn_le_of_torusLagClear

/-- **The single-lag input on the transfer form.** Under `TorusLagClear τ p hN β m r`, every `x` of
the gauge-invariant algebra with `D.form x D.vac = 0` (`D = periodicGaugeInvData τ p hN β`) has
`D.form x (Tᵐ x) ≤ rᵐ · D.form x x`. `ν(θx) = D.form x D.vac = 0` (`PeriodicReduce.periodic_form_vac`)
removes the subtracted terms of `periodic_conn_le_of_torusLagClear`, and
`PeriodicReduce.periodic_form_pow`, `periodic_form_diag` name the rest.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the vacuum pairing. -/
theorem periodic_form_lag_of_torusLagClear (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (m : ℕ)
    (r : ℝ) (h : TorusLagClear τ p hN β m r)
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (hx : (MassGap.PeriodicState.periodicGaugeInvData τ p hN β).form x
      (MassGap.PeriodicState.periodicGaugeInvData τ p hN β).vac = 0) :
    (MassGap.PeriodicState.periodicGaugeInvData τ p hN β).form x
        (((MassGap.PeriodicState.periodicGaugeInvData τ p hN β).T ^ m) x)
      ≤ r ^ m * (MassGap.PeriodicState.periodicGaugeInvData τ p hN β).form x x := by
  have hθ : MassGap.PeriodicState.periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
      (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = 0 :=
    (MassGap.PeriodicReduce.periodic_form_vac τ p hN β x).symm.trans hx
  have hc := periodic_conn_le_of_torusLagClear τ p hN β m r h
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) x.2
  simp only [hθ, zero_mul, sub_zero] at hc
  rw [MassGap.PeriodicReduce.periodic_form_pow τ p hN β x m, periodic_form_diag τ p hN β x]
  exact hc

#print axioms periodic_form_lag_of_torusLagClear

/-- **The Clay statement at the periodic state from one lag, at the lag's own rate.** At `2 ≤ N`,
`0 ≤ β`, a lag `m ≠ 0`, `0 < r < 1` and `TorusLagClear τ p hN β m r`:
`PeriodicContent.PeriodicClayGapAt τ p hN β r`. `periodic_form_lag_of_torusLagClear` puts the
single-lag inequality on the transfer form, `gapAt_of_lag` with
`PeriodicState.periodic_positiveTransfer` gives `TransferGap.GapAt` at `r`,
`ClayCapstone.clay_gap_of_gapAt` gives the spectrum, `GNSCompare.gapAt_iff_opT_contracts` the
contraction of the vacuum complement, and `PeriodicContent.periodic_exists_ne_zero_orth_vacuum` a
non-zero vector orthogonal to the vacuum. No read and no single-mode condition enters: a single-lag
ratio `rᵐ < 1` at any one lag gives the gap at `r`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance of the
real trace; `0` is the excluded rank, the excluded lag, and the lower end of `β` and `r`; `1` is the
upper end of `r`, the rate the gap must beat. -/
theorem periodic_clayGapAt_of_torusLag (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) {m : ℕ} (hm : m ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (h : TorusLagClear τ p hN β m r) :
    MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β r := by
  have hP := MassGap.PeriodicState.periodic_positiveTransfer τ p hN hβ
  have hg : MassGap.TransferGap.GapAt (MassGap.PeriodicState.periodicGaugeInvData τ p hN β) r :=
    gapAt_of_lag (MassGap.PeriodicState.periodicGaugeInvData τ p hN β) hP hm hr0.le
      (fun x hx => periodic_form_lag_of_torusLagClear τ p hN β m r h x hx)
  obtain ⟨hsa, _, hspec, hgreat⟩ := MassGap.ClayCapstone.clay_gap_of_gapAt
    (MassGap.PeriodicState.periodicGaugeInvData τ p hN β) hr0 hr1 hP hg
  exact ⟨hr0, hr1, hsa, hspec, hgreat,
    (MassGap.GNSCompare.gapAt_iff_opT_contracts
      (MassGap.PeriodicState.periodicGaugeInvData τ p hN β) hr0.le).mp hg,
    MassGap.PeriodicContent.periodic_exists_ne_zero_orth_vacuum τ p hN2 hN hβ⟩

#print axioms periodic_clayGapAt_of_torusLag

/-- The rate `e^{−20/(2(k + 1))}` puts the antipodal ratio at `e^{−10}`:
`(e^{−20/(2(k + 1))})^{k+1} = e^{−20/2}`.

DERIVED: `20` is the window rate; `2` and `1` in `2 * (k + 1)` are the
number of lags of the aperture `2k + 1`, and `2` in `20 / 2` is the antipode at half of them; `1` is
also the `+ 1` of `k + 1`. -/
theorem antipodal_rate_pow (k : ℕ) :
    Real.exp (-((20 : ℝ) / (2 * ((k : ℝ) + 1)))) ^ (k + 1) = Real.exp (-((20 : ℝ) / 2)) := by
  have h2 : (2 : ℝ) * ((k : ℝ) + 1) ≠ 0 := by positivity
  have key : ((k : ℝ) + 1) * ((20 : ℝ) / (2 * ((k : ℝ) + 1))) = (20 : ℝ) / 2 := by
    rw [mul_div_assoc', div_eq_div_iff h2 two_ne_zero]
    ring
  rw [← Real.exp_nat_mul, Nat.cast_add_one, mul_neg, key]

#print axioms antipodal_rate_pow

end Periodic

end MassGap.ChessboardRead
