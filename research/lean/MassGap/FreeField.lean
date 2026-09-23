import Mathlib
import MassGap.MinEntropy

/-!
# MassGap.FreeField — the `gapTension` of a top-two ratio, and its limit

`gapTension l1 l2 edge` is defined in `MassGap.MinEntropy`; on the branch `edge ≤ l2` it equals
`log (l1 / l2)` (`gapTension_gap_branch`). Everything in this file is stated about arbitrary reals or
arbitrary real sequences `l1, l2, edge : ℕ → ℝ`. Nothing here constructs a free field, a structure
factor or a circulant; the reading of `l1 / l2` as a top-two structure-factor ratio and of `L` as a
lattice extent is supplied by the caller.

Proved here:

* `freeField_confined_of_ratio` — on the gap branch, with `l1, l2 > 0`, `l1 / l2 < exp κ₀` implies
  `gapTension l1 l2 edge < κ₀`. One direction only; the converse is not stated;
* `muInf_lt_floor` — the numeric fact `0.0326 < ¼ log 3`, proved from `Real.exp_one_lt_d9`;
* `ratio_tendsto_one_of_scaling` — `exp (c / L²) → 1` as `L → ∞`, for every real `c`;
* `tension_tendsto_zero` — eventual gap branch plus `l1 L / l2 L → 1` gives
  `gapTension (l1 L) (l2 L) (edge L) → 0`;
* `tension_tendsto_zero_of_inv_sq` — a sequence eventually bounded by `C / L²` in absolute value tends
  to `0`, for `C` bound outside the sequence;
* `structure_factor_peak_at_zero` — a finite-sum inequality: nonnegative `ρ` against weights `c d ≤ 1`
  gives `∑ ρ d · c d ≤ ∑ ρ d`;
* `A1_weak_of_freefield` — the same hypotheses as `tension_tendsto_zero` plus `0 < κ₀` give
  `gapTension < κ₀` eventually, by `Tendsto.eventually` on the open set `Iio κ₀`.

The numeric constant `0.0326` is the only measured value that enters a statement; the table it comes
from is produced by `code/certify/free_field_muinf.py`.
-/

namespace MassGap.FreeField

open MassGap.MinEntropy Filter Topology

/-- On the branch `edge ≤ l2`, `gapTension l1 l2 edge = Real.log (l1 / l2)`. By `max_eq_left`: the
definition takes `max l2 edge` as its denominator, and that is `l2` exactly when `edge ≤ l2`. No
positivity is required, so this is an unfolding identity, not an inequality.

DERIVED: no numeral. -/
theorem gapTension_gap_branch {l1 l2 edge : ℝ} (hle : edge ≤ l2) :
    gapTension l1 l2 edge = Real.log (l1 / l2) := by
  unfold gapTension; rw [max_eq_left hle]

/-- On the gap branch, with `l1` and `l2` positive, `l1 / l2 < exp κ₀` implies
`gapTension l1 l2 edge < κ₀`. Via `gapTension_gap_branch` and `Real.exp_log` on the positive quotient.
`κ₀` is an arbitrary real here — no floor value is fixed — and only this direction is proved.

DERIVED: the two `0`s are the positivity of `l2` and `l1` that `Real.exp_log` needs to undo the
logarithm on the quotient. -/
theorem freeField_confined_of_ratio {l1 l2 edge κ₀ : ℝ} (hle : edge ≤ l2) (hl2 : 0 < l2) (hl1 : 0 < l1)
    (hratio : l1 / l2 < Real.exp κ₀) : gapTension l1 l2 edge < κ₀ := by
  rw [gapTension_gap_branch hle, ← Real.exp_lt_exp, Real.exp_log (div_pos hl1 hl2)]
  exact hratio

/-- `(0.0326 : ℝ) < ¼ log 3`. From `Real.exp_one_lt_d9` one gets `e < 3`, hence `1 < log 3`, hence
`¼ log 3 > 1/4 > 0.0326`. A statement about two real numbers; nothing in it refers to a lattice extent
or to a measured tension.

DERIVED: `0.0326` is the measured `μ∞` value the inequality is about, from
`code/certify/free_field_muinf.py`; `1 / 4` and `3` are the floor `¼ log 3` it is compared against. -/
theorem muInf_lt_floor : (0.0326 : ℝ) < (1 / 4) * Real.log 3 := by
  have he : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
  have h3 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  linarith

/-- `exp (c / L²) → 1` as `L → ∞` over `ℕ`, for every real `c`. `L² → ∞`, so `c / L² → 0` by
`Tendsto.div_atTop`, and `Real.continuous_exp` carries that to `exp 0 = 1`. `c` is arbitrary,
including negative; the statement fixes only the `1/L²` shape of the argument.

DERIVED: `2` is the power of `L` in the denominator, which is what makes the quotient vanish; `1` is
`exp 0`, the limit that follows. -/
theorem ratio_tendsto_one_of_scaling (c : ℝ) :
    Tendsto (fun L : ℕ => Real.exp (c / (L : ℝ) ^ 2)) atTop (nhds 1) := by
  have hL2 : Tendsto (fun L : ℕ => ((L : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun L : ℕ => c / (L : ℝ) ^ 2) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hL2
  have := (Real.continuous_exp.tendsto 0).comp hz
  simpa [Real.exp_zero, Function.comp_def] using this

/-- Given sequences `l1, l2, edge : ℕ → ℝ` with `edge L ≤ l2 L` eventually and `l1 L / l2 L → 1`,
the sequence `gapTension (l1 L) (l2 L) (edge L)` tends to `0`. `Real.log` is continuous at `1`, so the
ratio's limit gives `log (l1 L / l2 L) → 0`, and `gapTension_gap_branch` identifies the two sequences
on the eventual gap branch. Neither positivity of `l1` and `l2` nor a rate of convergence is required
or concluded.

DERIVED: `1` is the ratio's limit, the point at which `Real.log` is evaluated; `0 = log 1` is the
resulting limit of the tension. -/
theorem tension_tendsto_zero {l1 l2 edge : ℕ → ℝ}
    (hgap : ∀ᶠ L in atTop, edge L ≤ l2 L)
    (hratio : Tendsto (fun L => l1 L / l2 L) atTop (nhds 1)) :
    Tendsto (fun L => gapTension (l1 L) (l2 L) (edge L)) atTop (nhds 0) := by
  have hlog : Tendsto (fun L => Real.log (l1 L / l2 L)) atTop (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa [Real.log_one, Function.comp_def] using h
  have heq : (fun L => Real.log (l1 L / l2 L)) =ᶠ[atTop]
      (fun L => gapTension (l1 L) (l2 L) (edge L)) := by
    filter_upwards [hgap] with L hL
    exact (gapTension_gap_branch hL).symm
  exact hlog.congr' heq

/-- A real sequence `μ : ℕ → ℝ` with `|μ L| ≤ C / L²` eventually tends to `0`. By `squeeze_zero_norm'`
against `C / L² → 0`. `C` is an implicit real bound outside the sequence: one constant must work for
all large `L`, and its value is unconstrained. The statement is about an arbitrary sequence named `μ`;
it does not mention a correlation, a structure factor or a second moment.

DERIVED: `2` is the power of `L` in the bound, which is what forces the bound to vanish; `0` is the
limit that follows. -/
theorem tension_tendsto_zero_of_inv_sq {μ : ℕ → ℝ} {C : ℝ}
    (hb : ∀ᶠ L in atTop, |μ L| ≤ C / (L : ℝ) ^ 2) :
    Tendsto μ atTop (nhds 0) := by
  have hL2 : Tendsto (fun L : ℕ => ((L : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun L : ℕ => C / (L : ℝ) ^ 2) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hL2
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [hb] with L hL
  simpa [Real.norm_eq_abs] using hL

/-- A weighted finite sum is at most the unweighted one when the weights are at most `1` and the
summands nonnegative: for `ρ c : Fin L → ℝ` with `0 ≤ ρ d` and `c d ≤ 1` for every `d`,
`∑ d, ρ d * c d ≤ ∑ d, ρ d`. Termwise by `mul_le_mul_of_nonneg_left`. The index type `Fin L` plays no
role beyond finiteness, and `c` is arbitrary below `1`; read against a structure factor, `c` is the
cosine weight and the right-hand side is the value at zero momentum.

DERIVED: `0` is the nonnegativity asked of each `ρ d`, without which the termwise multiplication
reverses; `1` is the ceiling on each weight `c d`, the value at which the two sides agree. -/
theorem structure_factor_peak_at_zero {L : ℕ} (ρ c : Fin L → ℝ)
    (hρ : ∀ d, 0 ≤ ρ d) (hc : ∀ d, c d ≤ 1) :
    ∑ d, ρ d * c d ≤ ∑ d, ρ d := by
  refine Finset.sum_le_sum (fun d _ => ?_)
  calc ρ d * c d ≤ ρ d * 1 := mul_le_mul_of_nonneg_left (hc d) (hρ d)
    _ = ρ d := mul_one _

/-- With `0 < κ₀`, the gap branch holding eventually, and `l1 L / l2 L → 1`, the gap tension is
eventually below `κ₀`: `∀ᶠ L in atTop, gapTension (l1 L) (l2 L) (edge L) < κ₀`. It is
`tension_tendsto_zero` composed with `Tendsto.eventually` on the open set `Set.Iio κ₀`, which contains
`0` exactly when `0 < κ₀`. `κ₀` is an arbitrary positive real; no floor value is fixed, and the
conclusion is eventual, with no threshold on `L` named.

DERIVED: `0` in `hκ` is what puts the limit `0` inside `Iio κ₀`, and is the only thing the hypothesis
is used for; `1` is the ratio limit inherited from `tension_tendsto_zero`. -/
theorem A1_weak_of_freefield {l1 l2 edge : ℕ → ℝ} {κ₀ : ℝ} (hκ : 0 < κ₀)
    (hgap : ∀ᶠ L in atTop, edge L ≤ l2 L)
    (hratio : Tendsto (fun L => l1 L / l2 L) atTop (nhds 1)) :
    ∀ᶠ L in atTop, gapTension (l1 L) (l2 L) (edge L) < κ₀ :=
  (tension_tendsto_zero hgap hratio).eventually (isOpen_Iio.mem_nhds hκ)

-- Reports the axiom footprint of the numeric floor fact on every build.
#print axioms muInf_lt_floor

end MassGap.FreeField
