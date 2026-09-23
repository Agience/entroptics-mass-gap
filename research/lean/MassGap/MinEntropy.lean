import Mathlib

/-!
# MassGap.MinEntropy — the tension read rewritten as a min-entropy deficit

Three definitions over the reals and the logarithm identities relating them. With `ts` the
leading-mode power fraction, `f` the noise floor and `n` the mode count:

    Hmin ts        = -log ts
    HminDis f n    = log (n / f)
    tension ts f n = log (n * ts / f)

`tension_eq_min_entropy_deficit` proves `tension ts f n = HminDis f n - Hmin ts` for positive
`ts, f, n`, so the tension is the difference of the two entropies. `confinement_iff_min_entropy`
rewrites `tension ts f n < κ₀` as `HminDis f n - κ₀ < Hmin ts`, and `tension_zero_of_at_floor` gives
`tension ts f n = 0` when `n * ts = f`.

The second half replaces the single-mode read by a two-eigenvalue one:
`gapTension l1 l2 edge = log (l1 / max l2 edge)`. `gapTension_eq_edge_of_le` shows it collapses to
`log (l1 / edge)` when `l2 ≤ edge`, and `confinement_iff_gap` rewrites `gapTension l1 l2 edge < κ₀`
as `l1 < exp κ₀ * max l2 edge`.

Scope: every result here is a logarithm identity or a rearrangement of an inequality. `κ₀` is a free
real variable throughout; no theorem in this module fixes its value or asserts any inequality about
a physical read.
-/

namespace MassGap.MinEntropy

/-- The Rényi-∞ (min) entropy of a power spectrum with leading share `ts`: `-Real.log ts`. Defined
for every real `ts`; `Real.log` is `0` on non-positive arguments, so no positivity is required here.

DERIVED: no numeral occurs. -/
noncomputable def Hmin (ts : ℝ) : ℝ := -Real.log ts

/-- The min-entropy of a flat spectrum of `n` modes against noise floor `f`: `Real.log (n / f)`.
Defined for every pair of reals.

DERIVED: no numeral occurs. -/
noncomputable def HminDis (f n : ℝ) : ℝ := Real.log (n / f)

/-- The tension read as the log of a contrast: `Real.log (n * ts / f)`, where the contrast is the
leading share `ts` scaled by the mode count `n` and divided by the floor `f`. Defined for every
triple of reals.

DERIVED: no numeral occurs. -/
noncomputable def tension (ts f n : ℝ) : ℝ := Real.log (n * ts / f)

/-- `tension ts f n = HminDis f n - Hmin ts`, for `0 < ts`, `0 < f`, `0 < n`. The proof is three
applications of `Real.log_div` and `Real.log_mul`, closed by `ring`; the positivity hypotheses are
exactly what those lemmas need to split the logarithm.

DERIVED: the one numeral is the `0` in the three positivity hypotheses, which is where `Real.log`
turns a product and a quotient into a sum and a difference. -/
theorem tension_eq_min_entropy_deficit {ts f n : ℝ} (hts : 0 < ts) (hf : 0 < f) (hn : 0 < n) :
    tension ts f n = HminDis f n - Hmin ts := by
  unfold tension HminDis Hmin
  rw [Real.log_div (mul_pos hn hts).ne' hf.ne', Real.log_mul hn.ne' hts.ne',
      Real.log_div hn.ne' hf.ne']
  ring

/-- `tension ts f n < κ₀ ↔ HminDis f n - κ₀ < Hmin ts`, for `0 < ts`, `0 < f`, `0 < n`. Obtained by
rewriting with `tension_eq_min_entropy_deficit` and moving `κ₀` across, in both directions.

Scope: `κ₀` is a free real variable; the equivalence holds at any value and asserts neither side.

DERIVED: the one numeral is the `0` in the three positivity hypotheses, inherited from
`tension_eq_min_entropy_deficit`. -/
theorem confinement_iff_min_entropy {ts f n κ₀ : ℝ} (hts : 0 < ts) (hf : 0 < f) (hn : 0 < n) :
    tension ts f n < κ₀ ↔ HminDis f n - κ₀ < Hmin ts := by
  rw [tension_eq_min_entropy_deficit hts hf hn]
  constructor <;> intro h <;> linarith

/-- `tension ts f n = 0` when `n * ts = f`, that is, when the contrast is one. The proof rewrites by
`hfloor`, then `div_self` and `Real.log_one`.

Scope: only `hf : 0 < f` is used; the arguments `_hts` and `_hn` are named with a leading underscore
and play no part in the proof.

DERIVED: `0` appears twice — as the strict lower bound in the three positivity arguments and as the
value of the tension in the conclusion. The contrast value one is not written as a literal; it is
the content of `hfloor : n * ts = f`. -/
theorem tension_zero_of_at_floor {ts f n : ℝ} (_hts : 0 < ts) (hf : 0 < f) (_hn : 0 < n)
    (hfloor : n * ts = f) : tension ts f n = 0 := by
  unfold tension
  rw [hfloor, div_self hf.ne', Real.log_one]

/-- Chaining a character bound through the entropy form. Given `0 < ts`, `0 < f`, `0 < n`, a bound
`tension ts f n ≤ 2 * β * r` and `2 * β * r < κ₀`, the conclusion is `HminDis f n - κ₀ < Hmin ts`.
The proof is `lt_of_le_of_lt` on the two inequalities, passed through
`confinement_iff_min_entropy`.

Scope: both `hchar` and `hthr` are hypotheses. `β` and `r` are unconstrained reals, so the
expression `2 * β * r` carries no sign information of its own; the whole content is the transitive
step plus the rewrite.

DERIVED: `0` is the strict lower bound in the three positivity hypotheses; `2` is the coefficient in
the supplied bound `2 * β * r`, written as the caller states it and not computed here. -/
theorem confined_of_character_bound {ts f n β r κ₀ : ℝ} (hts : 0 < ts) (hf : 0 < f) (hn : 0 < n)
    (hchar : tension ts f n ≤ 2 * β * r) (hthr : 2 * β * r < κ₀) :
    HminDis f n - κ₀ < Hmin ts :=
  (confinement_iff_min_entropy hts hf hn).mp (lt_of_le_of_lt hchar hthr)

/-! ## The two-eigenvalue form

The library read (`reads.py`, `_spectral_from_cov`) computes a log-ratio of the top two correlation
eigenvalues with the noise floor as a backstop, `log (λ₁ / max (λ₂, edge))`, rather than
`log (λ₁ / edge)`. `gapTension` below is that expression. When `λ₂ ≤ edge` the `max` selects the
floor and the two forms agree (`gapTension_eq_edge_of_le`); otherwise the second eigenvalue is the
denominator. -/

/-- The two-eigenvalue tension `Real.log (l1 / max l2 edge)`: the log-ratio of the leading
correlation eigenvalue to the larger of the second eigenvalue and the noise floor. Defined for every
triple of reals.

DERIVED: no numeral occurs. -/
noncomputable def gapTension (l1 l2 edge : ℝ) : ℝ := Real.log (l1 / max l2 edge)

/-- `gapTension l1 l2 edge = Real.log (l1 / edge)` whenever `l2 ≤ edge`. One rewrite by
`max_eq_right` after unfolding. No positivity is assumed on any of the three arguments.

DERIVED: no numeral occurs. -/
theorem gapTension_eq_edge_of_le {l1 l2 edge : ℝ} (h : l2 ≤ edge) :
    gapTension l1 l2 edge = Real.log (l1 / edge) := by
  unfold gapTension; rw [max_eq_right h]

/-- `gapTension l1 l2 edge < κ₀ ↔ l1 < Real.exp κ₀ * max l2 edge`, given `0 < max l2 edge` and
`0 < l1`. The proof unfolds the definition, applies `Real.exp_lt_exp` and `Real.exp_log` to the
positive quotient, then `div_lt_iff₀` to clear the denominator.

Scope: `κ₀` is a free real variable and the equivalence holds at any value; positivity of the
denominator is required only as a `max`, so `l2` alone may be non-positive.

DERIVED: the one numeral is the `0` in the two positivity hypotheses, needed for `Real.exp_log` and
for the direction of `div_lt_iff₀`. -/
theorem confinement_iff_gap {l1 l2 edge κ₀ : ℝ} (hr : 0 < max l2 edge) (hl1 : 0 < l1) :
    gapTension l1 l2 edge < κ₀ ↔ l1 < Real.exp κ₀ * max l2 edge := by
  unfold gapTension
  rw [← Real.exp_lt_exp, Real.exp_log (div_pos hl1 hr), div_lt_iff₀ hr]

end MassGap.MinEntropy
