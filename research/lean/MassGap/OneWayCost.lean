import Mathlib
import MassGap.NoTransitionFlow

/-!
# MassGap.OneWayCost — the chunk cost runs one way: which form, in which model, and what is left

The owner's route: "cost runs one way: each zoom-out doubling raises the chunk's edge cost by at
least a fixed amount (asymptotic freedom continued past `r*`: the coupling only grows outward)". In
`NoTransitionFlow` this is `RunsOneWay b s` (`s (k+1) ≥ s k + b (s k)²` at every doubling), consumed by
`uniform_steps_of_runsOneWay` and `matchAt_uniform_of_runsOneWay`. This module reads that predicate
against the flows it is meant to describe, replaces it by the form those flows can satisfy, and
reduces that form, in the Migdal–Kadanoff hierarchical model, to one inequality for one plaquette.

## 1. The uncapped form is not met by a flow with linear growth (`not_runsOneWay_of_linear`)

`not_runsOneWay_of_linear`: with `b > 0` and `s 0 > 0`, no sequence with `s (k+1) ≤ c s k + d` at
every step satisfies `RunsOneWay b s` (it would force `s → ∞`, `runsOneWay_tendsto`, while
`b s² ≤ (c − 1) s + d`). `not_runsOneWay_of_scales`: the same for an exact law `Scales c s`.
`tension_not_runsOneWay`: the tension read in chunk units, `σ f (2ᵏ ℓ₀)²` with `σ, f, ℓ₀ > 0` (the
confining reading, `Scales 4`), does not run one way in the uncapped sense for any `b > 0`.
`runsOneWay_family_unsat`: hence the hypothesis `∀ j, RunsOneWay b (s j)` of
`matchAt_uniform_of_runsOneWay` fails as soon as one zoom's cost grows at most linearly per doubling.
The Migdal–Kadanoff flow is such a flow at its strong end (`s' = 4 (s − log 4)` up to `O(e^{−s})`,
`no_transition_flow_checks.py`, `one_way_cost_checks.py`), as the units law `Scales 4` would be.

## 2. The capped form (`RunsOneWayTo`)

`RunsOneWayTo b T s`: `min (s k + b (s k)²) T ≤ s (k+1)` at every step — the cost rises by `b s²` while
it is below the target `T`, and once at `T` it does not fall below `T`.

* `runsOneWayTo_of_runsOneWay`: the uncapped form implies the capped one at every `T`.
* `runsOneWayTo_lower`: `min (s 0 + k b (s 0)²) T ≤ s k`.
* `uniform_steps_of_runsOneWayTo`, `matchAt_uniform_of_runsOneWayTo`: the conclusions of
  `uniform_steps_of_runsOneWay` and `matchAt_uniform_of_runsOneWay` from the capped form, with
  `T = kpCost z κ` for the match: one number of doublings `K` with `MatchAt` at every zoom and every
  step `k ≥ K`.
* `scales_runsOneWayTo`: an exact law `Scales c s`, `c ≥ 1`, `s 0 ≥ 0`, satisfies
  `RunsOneWayTo ((c − 1)/T) T`. `tension_runsOneWayTo`, `tension_capped_not_uncapped`: the confining
  reading meets the capped form with `b = 3/T` and fails the uncapped form for every `b > 0`.
* `not_runsOneWayTo_of_fixed`: a cost fixed at `c ∈ (0, T)` (a fixed point of the chunk law at a
  finite cost: the Coulomb phase of `U(1)` on the Wilson lattice, Guth 1980, Fröhlich–Spencer 1982,
  cited, not proved here) fails `RunsOneWayTo b T` for every `b > 0`.
* `exp_neg_div_le`: `e^{−a/s} ≤ 6 s³/a³`. `not_runsOneWayTo_of_nonpert`: a step whose increment is at
  most `C e^{−a/s}` (the nonperturbative size) at a cost `s` with `6 C s < b a³` and `s + b s² ≤ T`
  breaks `RunsOneWayTo b T`. So a flow whose increments are of that size at small cost runs one way
  with no `b > 0` near `s = 0`, though it may still pass every level eventually.

## 3. Eventual against rate (`uniform_of_monotone_step`)

`uniform_of_monotone_step`: an autonomous step `R` on a preordered state space, monotone, with a
monotone cost, a level `T` that the step does not leave (`T ≤ cost y → T ≤ cost (R y)`), and one start
`x₀` whose orbit reaches `T` at step `K`, give `T ≤ cost (Rᵏ (x j))` at every start `x j ≥ x₀` and
every `k ≥ K`. No rate enters: where the step is the same at every zoom and monotone, a qualitative
"the coefficients flow to the strong-coupling end" with a uniform start gives the uniform number of
doublings, and the rate `b` only sizes `K`.

## 4. The Migdal–Kadanoff model (`CostBound`, `BondMoveCost`, `mk_uniform_of_bondMoveCost`)

The MK step (Migdal 1975, Kadanoff 1976; `b = 2`, `d = 4`) on a plaquette weight `f = Σ d_j c_j χ_j`:
bond moving `f ↦ f^ζ / ∫ f^ζ`, `ζ = b^{d−2} = 4`, then decimation `c_j ↦ c_j^{b²}`, `b² = 4`, exact
in the character basis (2-dimensional integration, character orthogonality; `MKBound.mkUpper` with
`r = 1`). Here the state space `X`, the coefficient map `coef : X → J → ℝ` (`J` the nontrivial
representations), the bond-moving map `bm` and the decimation `dec` are abstract; the decimation is
assumed only through `coef (dec y) j = (coef y j)ⁿ`.

* `CostBound c s`: `0 ≤ c j ≤ e^{−s}` for every nontrivial `j` (the cost is at least `s`).
  `costBound_anti`: a bound at `s` is one at every `s' ≤ s`. `costBound_decim`, `decim_cost_eq`:
  decimation multiplies the cost by `n` exactly.
* `BondMoveCost S coef bm n b T`: for every weight `x` in the class `S` and every `s ≥ 0`, a cost
  bound `s` at `x` gives the cost bound `min (s + b s²) T / n` after bond moving. This is the one
  plaquette inequality "the moved plaquette costs at least `1/n` of the cost plus `b s²/n`".
* `cappedRun`, `cappedRun_runsOneWayTo`, `cappedRun_nonneg`: the extremal capped sequence.
* `mk_orbit_cost`: with `S` preserved by the step, `BondMoveCost` and a cost bound `s₀` at the start,
  the `k`-th MK iterate has the cost bound `cappedRun b T s₀ k`.
* `mk_uniform_of_bondMoveCost`: with `b > 0`, `s₀ > 0`, every start in `S` with cost at least `s₀`,
  there is one `K` such that after `k ≥ K` MK steps every nontrivial coefficient of every start is at
  most `e^{−T}`. That is the capped one-way running, with a rate, for the hierarchical model, under
  `BondMoveCost`.

What is proved for the MK model is the reduction: capped one-way running of the MK cost follows
from `BondMoveCost` on an invariant class. `BondMoveCost` itself is not proved here for any group.
What it carries, read on numbers (`one_way_cost_checks.py`, quadrature and exact sums, a model of the
RG, not a bound on it):

* `SU(2)`: on the heat-kernel weights the one-step running coefficient `(s' − s)/s²` lies between
  `0.167` (its value as `s → 0`, read at `s = 0.02`) and `0.334` on `s ∈ [0.02, kpCost]`; along Wilson
  starts `β = 1, 2.5, 4, 6` it is at least `0.263, 0.168, 0.156, 0.150` from step 1 on while
  `s < kpCost`, and negative at step 0 for `β = 2.5, 4, 6`. So the class `S` must exclude the Wilson
  weight itself. Above `kpCost` it follows `(3 s − 4 log 4)/s² → 0` (the uncapped form fails, §1).
* `U(1)`: on the Villain weights `c_n = e^{−τ n²}` the step is given exactly by Poisson summation over
  `{k ∈ ℤ⁴ : Σ k = 0}` (agreeing with direct convolution to `10⁻⁶` relative at `τ = 0.6, 1, 1.5`); its
  leading term is `s' − s = 32 e^{−3π²/(4s)}`, within `15 %` of the exact step at `τ ≤ 1`. The running coefficient is `3·10⁻¹⁰` at `s = 0.264` and `1.5·10⁻²²` at
  `s = 0.128`. Wilson starts `β = 1, 2` relax to a trajectory on which `s` rises by `0.52` and `0.19`
  of that leading term per step; at `β = 4` the increment is below double-precision resolution. Along
  the Villain family `s = 0.128 → 1` takes about `10²¹` steps (the integral of `ds/(s' − s)`, an
  estimate). This is the reading behind "`U(1)` stationary at `β ≥ 1` in 40 steps" of
  `match_checks.py`/`mk_bound_checks.py`: the flow is one way, its increment is nonperturbatively
  small, and `BondMoveCost` holds on it with no `b > 0` near `s = 0` (`not_runsOneWayTo_of_nonpert`).

## Ito's theorem and the `U(1)` defect of the hierarchical model

Ito, Phys. Rev. Lett. 55 (1985) 558, as stated in Ito–Seiler arXiv:0711.4930, Theorem 2.1: for the
MK recursion in `D ≤ 4` and `G = SU(N)` or `U(N)`, `lim c_j(n) = 0` for every `j ≠ 0` (cited, not
proved here). The statement is a limit with no rate, and `U(1)` (`U(N)` at `N = 1`) is included; Ito–Seiler note
that the MK recursions "cannot distinguish non-abelian groups from abelian ones". The MK model thus
confines 4D `U(1)` at every coupling, contrary to the Coulomb phase of the Wilson lattice (Guth,
Fröhlich–Spencer). With `uniform_of_monotone_step` an eventual limit already gives a uniform number of
doublings in the hierarchical model, for `U(1)` as for `SU(N)`, under three hypotheses not proved
here: monotonicity of the MK step in the coefficients, a level that the step does not leave (`habs`
of `uniform_of_monotone_step`), and decay of `sup_j c_j` along the orbit of the start `x₀`. Ito's
limit is per `j`; when `J` is infinite (`U(1)`, `j ∈ ℤ ∖ {0}`) it does not give the bound on
`sup_j c_j`, so it does not by itself give the level `T` at a finite step `K`. So in the hierarchical
model the route separates `SU(N)` from `U(1)` only through the rate: `b ≈ 0.17` against
`32 e^{−3π²/(4s)}/s²`, read numerically. `not_runsOneWayTo_of_fixed` excludes an exactly constant cost;
it does not cover an orbit that converges to a Coulomb fixed point without reaching it.

## The residual for the 4D Wilson lattice

To use `matchAt_uniform_of_runsOneWayTo` for 4D `SU(N)`:

* (W1) the capped one-way running of the block-spin chunk cost of the Wilson measure at every zoom past
  `r*`, with one `b > 0`; through the MK model this is (a) `BondMoveCost` for `SU(N)` on a class
  preserved by the MK step and containing the coarse weights at `r*`, and (b) a comparison giving
  the Wilson chunk cost at least the MK cost at every step — a `SandwichMatch`-type transfer
  (`MKBound.SandwichMatch`) at the level of costs, which `MKBound` leaves open and which must fail for
  `U(1)`: on the Wilson lattice the `U(1)` cost has a fixed point at a finite cost in the Coulomb
  phase, and `not_runsOneWayTo_of_fixed` excludes every `b > 0` there, while the MK cost of `U(1)`
  rises (Ito). Any proof of (b) uses a property `U(1)` lacks;
* (W2) the chunk activities obey the count at that cost (the count hypothesis of
  `matchAt_of_count`).

Nothing here proves (W1) or (W2), confinement, or a mass gap for the Wilson lattice.

DERIVED (module-wide): `1` the unit of the growth factor and of `max 1 _`; `3 = 4 − 1` the excess of
the units law `Scales 4` over the identity; `6 = 3!` from `x³/3! ≤ eˣ`; `0` the sign of a cost.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.OneWayCost

open Filter Topology Finset
open MassGap.MatchAt MassGap.NoTransitionFlow

/-! ## 1. The uncapped form against linear growth -/

/-- **One-way running in the uncapped form is not met by a flow with linear growth**: `b > 0`,
`s 0 > 0` and `s (k+1) ≤ c s k + d` at every step exclude `RunsOneWay b s`. -/
theorem not_runsOneWay_of_linear {b c d : ℝ} {s : ℕ → ℝ} (hb : 0 < b) (h0 : 0 < s 0)
    (hlin : ∀ k, s (k + 1) ≤ c * s k + d) : ¬ RunsOneWay b s := by
  intro h
  obtain ⟨k, hk⟩ := ((runsOneWay_tendsto hb h h0).eventually_ge_atTop
    (max 1 ((|c - 1| + |d| + 1) / b))).exists
  have hx1 : 1 ≤ s k := (le_max_left _ _).trans hk
  have hxM : (|c - 1| + |d| + 1) / b ≤ s k := (le_max_right _ _).trans hk
  have h1 : |c - 1| + |d| + 1 ≤ b * s k := by
    rw [div_le_iff₀ hb] at hxM
    linarith
  have h2 : (|c - 1| + |d| + 1) * s k ≤ b * s k * s k :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : (c - 1) * s k ≤ |c - 1| * s k :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have h4 : d ≤ |d| * s k := (le_abs_self d).trans (le_mul_of_one_le_right (abs_nonneg d) hx1)
  have h5 := h k
  have h6 := hlin k
  nlinarith

/-- **An exact doubling law does not run one way in the uncapped form.** -/
theorem not_runsOneWay_of_scales {b c : ℝ} {s : ℕ → ℝ} (hb : 0 < b) (h0 : 0 < s 0)
    (h : Scales c s) : ¬ RunsOneWay b s :=
  not_runsOneWay_of_linear (d := 0) hb h0 fun k => by rw [h k, add_zero]

/-- **The confining reading `σ f (2ᵏ ℓ₀)²` does not run one way in the uncapped form**, for any
`b > 0`. -/
theorem tension_not_runsOneWay {b σ f ℓ₀ : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hf : 0 < f)
    (hℓ₀ : 0 < ℓ₀) : ¬ RunsOneWay b (fun k => σ * f * side ℓ₀ k ^ 2) := by
  refine not_runsOneWay_of_scales hb ?_ (scales_tension σ f ℓ₀)
  simp only [side, pow_zero, one_mul]
  positivity

/-- **The hypothesis of `matchAt_uniform_of_runsOneWay` fails** as soon as one zoom's cost, started
at `≥ s₀ > 0`, grows at most linearly per doubling. -/
theorem runsOneWay_family_unsat {s : ℕ → ℕ → ℝ} {b c d s₀ : ℝ} (hb : 0 < b) (hs₀ : 0 < s₀)
    (hstart : ∀ j, s₀ ≤ s j 0) (j : ℕ) (hlin : ∀ k, s j (k + 1) ≤ c * s j k + d) :
    ¬ ∀ j, RunsOneWay b (s j) := fun h =>
  not_runsOneWay_of_linear hb (hs₀.trans_le (hstart j)) hlin (h j)

/-! ## 2. The capped form -/

/-- **One-way running up to a target**: the cost rises by at least `b s²` while below `T`, and does
not fall below `T` once there. -/
def RunsOneWayTo (b T : ℝ) (s : ℕ → ℝ) : Prop := ∀ k, min (s k + b * s k ^ 2) T ≤ s (k + 1)

theorem runsOneWayTo_of_runsOneWay {b : ℝ} {s : ℕ → ℝ} (h : RunsOneWay b s) (T : ℝ) :
    RunsOneWayTo b T s := fun k => (min_le_left _ _).trans (h k)

/-- **Linear lower bound up to the target**: `min (s 0 + k b (s 0)²) T ≤ s k`. -/
theorem runsOneWayTo_lower {b T : ℝ} {s : ℕ → ℝ} (hb : 0 ≤ b) (h : RunsOneWayTo b T s)
    (h0 : 0 ≤ s 0) (k : ℕ) : min (s 0 + k * (b * s 0 ^ 2)) T ≤ s k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases le_or_gt T (s k) with hT | hT
    · have hge : T ≤ s k + b * s k ^ 2 := by nlinarith [mul_nonneg hb (sq_nonneg (s k))]
      have hk1 : T ≤ s (k + 1) := by
        have := h k
        rwa [min_eq_right hge] at this
      exact (min_le_right _ _).trans hk1
    · have hA : s 0 + k * (b * s 0 ^ 2) ≤ s k := by
        rcases min_le_iff.1 ih with h' | h'
        · exact h'
        · linarith
      have hc : 0 ≤ (k : ℝ) * (b * s 0 ^ 2) :=
        mul_nonneg (Nat.cast_nonneg k) (mul_nonneg hb (sq_nonneg (s 0)))
      have hk0 : s 0 ≤ s k := by linarith
      have hsq : s 0 ^ 2 ≤ s k ^ 2 := pow_le_pow_left₀ h0 hk0 2
      have hb2 := mul_le_mul_of_nonneg_left hsq hb
      have hle : s 0 + ((k + 1 : ℕ) : ℝ) * (b * s 0 ^ 2) ≤ s k + b * s k ^ 2 := by
        push_cast
        nlinarith
      exact (min_le_min hle le_rfl).trans (h k)

/-- **One number of doublings for every zoom, from the capped form.** -/
theorem uniform_steps_of_runsOneWayTo {s : ℕ → ℕ → ℝ} {b s₀ T : ℝ} (hb : 0 ≤ b)
    (hbs : 0 < b * s₀ ^ 2) (hs₀ : 0 ≤ s₀) (hstart : ∀ j, s₀ ≤ s j 0)
    (hrun : ∀ j, RunsOneWayTo b T (s j)) : ∃ K : ℕ, ∀ j k, K ≤ k → T ≤ s j k := by
  obtain ⟨K, hK⟩ := exists_nat_ge ((T - s₀) / (b * s₀ ^ 2))
  refine ⟨K, fun j k hk => ?_⟩
  have h1 := runsOneWayTo_lower hb (hrun j) (hs₀.trans (hstart j)) k
  have hsq : s₀ ^ 2 ≤ s j 0 ^ 2 := pow_le_pow_left₀ hs₀ (hstart j) 2
  have hk' : (K : ℝ) ≤ k := Nat.cast_le.2 hk
  have h2 : T - s₀ ≤ K * (b * s₀ ^ 2) := (div_le_iff₀ hbs).1 hK
  have h3 : (K : ℝ) * (b * s₀ ^ 2) ≤ k * (b * s j 0 ^ 2) :=
    mul_le_mul hk' (mul_le_mul_of_nonneg_left hsq hb) hbs.le (Nat.cast_nonneg k)
  have hA : T ≤ s j 0 + k * (b * s j 0 ^ 2) := by linarith [hstart j]
  rwa [min_eq_right hA] at h1

/-- **The match at one number of doublings for every zoom, from the capped form**: chunk activities
obeying the count at cost `s j k`, the cost starting at `≥ s₀ > 0` and running one way up to
`kpCost z κ` with `b > 0` at every zoom, give one `K` with `MatchAt` at every zoom and every
`k ≥ K`. -/
theorem matchAt_uniform_of_runsOneWayTo {V : ℕ → ℕ → Type*} [∀ j k, Fintype (V j k)]
    [∀ j k, DecidableEq (V j k)] (w : ∀ j k, Finset (V j k) → ℝ) {s : ℕ → ℕ → ℝ} {z κ b s₀ : ℝ}
    (hz : 0 ≤ z) (hκ : 0 ≤ κ) (hb : 0 < b) (hs₀ : 0 < s₀) (hstart : ∀ j, s₀ ≤ s j 0)
    (hrun : ∀ j, RunsOneWayTo b (kpCost z κ) (s j)) (hw0 : ∀ j k, w j k ∅ = 0)
    (hcount : ∀ j k (v : V j k) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j k X|
      ≤ (z * Real.exp (-(s j k))) ^ n) :
    ∃ K : ℕ, ∀ j k, K ≤ k → MatchAt (w j k) 1 κ := by
  obtain ⟨K, hK⟩ := uniform_steps_of_runsOneWayTo hb.le (mul_pos hb (pow_pos hs₀ 2)) hs₀.le
    hstart hrun
  exact ⟨K, fun j k hk =>
    matchAt_of_count (hw0 j k) hz hκ (hcount j k) (count_cond_of_ge hz (hK j k hk))⟩

/-- **An exact doubling law runs one way up to every target**: `Scales c s`, `c ≥ 1`, `s 0 ≥ 0`
give `RunsOneWayTo ((c − 1)/T) T s`. -/
theorem scales_runsOneWayTo {c T : ℝ} {s : ℕ → ℝ} (hc : 1 ≤ c) (hT : 0 < T) (h : Scales c s)
    (h0 : 0 ≤ s 0) : RunsOneWayTo ((c - 1) / T) T s := by
  intro k
  have hc1 : 0 ≤ c - 1 := by linarith
  have hk : 0 ≤ s k := by
    rw [scales_iter h k]
    exact mul_nonneg (pow_nonneg (by linarith) k) h0
  rw [h k]
  rcases lt_or_ge (s k) T with hlt | hge
  · refine (min_le_left _ _).trans ?_
    have key : (c - 1) / T * s k ^ 2 ≤ (c - 1) * s k := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hT]
      nlinarith [mul_nonneg (mul_nonneg hc1 hk) (sub_nonneg.2 hlt.le)]
    linarith
  · exact (min_le_right _ _).trans (by nlinarith [mul_nonneg hc1 hk])

/-- **The confining reading runs one way up to every target**, with `b = 3/T`. -/
theorem tension_runsOneWayTo {σ f ℓ₀ T : ℝ} (hσ : 0 ≤ σ) (hf : 0 ≤ f) (hT : 0 < T) :
    RunsOneWayTo (3 / T) T (fun k => σ * f * side ℓ₀ k ^ 2) := by
  have h := scales_runsOneWayTo (c := 4) (by norm_num) hT (scales_tension σ f ℓ₀)
    (by simp only [side, pow_zero, one_mul]; positivity)
  convert h using 2
  norm_num

/-- **The confining reading: capped yes, uncapped no.** -/
theorem tension_capped_not_uncapped {b σ f ℓ₀ T : ℝ} (hb : 0 < b) (hσ : 0 < σ) (hf : 0 < f)
    (hℓ₀ : 0 < ℓ₀) (hT : 0 < T) :
    RunsOneWayTo (3 / T) T (fun k => σ * f * side ℓ₀ k ^ 2) ∧
      ¬ RunsOneWay b (fun k => σ * f * side ℓ₀ k ^ 2) :=
  ⟨tension_runsOneWayTo hσ.le hf.le hT, tension_not_runsOneWay hb hσ hf hℓ₀⟩

/-- **A cost fixed below the target does not run one way**, for any `b > 0`. -/
theorem not_runsOneWayTo_of_fixed {b T c : ℝ} (hb : 0 < b) (hc : 0 < c) (hcT : c < T) :
    ¬ RunsOneWayTo b T (fun _ => c) := by
  intro h
  have h0 : min (c + b * c ^ 2) T ≤ c := h 0
  have : c < min (c + b * c ^ 2) T := lt_min (by nlinarith [mul_pos hb (pow_pos hc 2)]) hcT
  linarith

/-- `e^{−a/s} ≤ 6 s³/a³` (from `x³/3! ≤ eˣ`). -/
theorem exp_neg_div_le {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    Real.exp (-(a / s)) ≤ 6 * s ^ 3 / a ^ 3 := by
  have hx : 0 < a / s := div_pos ha hs
  have h := Real.pow_div_factorial_le_exp (a / s) hx.le 3
  have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at h
  have hp : 0 < (a / s) ^ 3 / 6 := by positivity
  have ha' : a ≠ 0 := ha.ne'
  have hs' : s ≠ 0 := hs.ne'
  calc Real.exp (-(a / s)) = (Real.exp (a / s))⁻¹ := Real.exp_neg _
    _ ≤ ((a / s) ^ 3 / 6)⁻¹ := inv_anti₀ hp h
    _ = 6 * s ^ 3 / a ^ 3 := by field_simp

/-- **A nonperturbatively small step breaks the capped form**: at a cost `s k > 0` with
`6 C s k < b a³` and `s k + b (s k)² ≤ T`, an increment at most `C e^{−a/s k}` is below `b (s k)²`. -/
theorem not_runsOneWayTo_of_nonpert {a C b T : ℝ} {s : ℕ → ℝ} (ha : 0 < a) (hC : 0 ≤ C) (k : ℕ)
    (hs : 0 < s k) (hsmall : 6 * C * s k < b * a ^ 3) (hT : s k + b * s k ^ 2 ≤ T)
    (hstep : s (k + 1) ≤ s k + C * Real.exp (-(a / s k))) : ¬ RunsOneWayTo b T s := by
  intro h
  have h1 := h k
  rw [min_eq_left hT] at h1
  have he := mul_le_mul_of_nonneg_left (exp_neg_div_le ha hs) hC
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  have key : C * (6 * s k ^ 3 / a ^ 3) < b * s k ^ 2 := by
    rw [show C * (6 * s k ^ 3 / a ^ 3) = (6 * C * s k) * s k ^ 2 / a ^ 3 by ring,
      div_lt_iff₀ ha3]
    have := mul_lt_mul_of_pos_right hsmall (pow_pos hs 2)
    nlinarith
  linarith

/-! ## 3. Eventual against rate -/

/-- **Eventual suffices for an autonomous monotone step**: one start whose orbit reaches a level the
step does not leave gives that level after the same number of steps at every start above it. -/
theorem uniform_of_monotone_step {X : Type*} [Preorder X] {R : X → X} (hR : Monotone R)
    {cost : X → ℝ} (hcost : Monotone cost) {T : ℝ} (habs : ∀ y, T ≤ cost y → T ≤ cost (R y))
    {x₀ : X} {K : ℕ} (hK : T ≤ cost (R^[K] x₀)) {x : ℕ → X} (hx : ∀ j, x₀ ≤ x j) :
    ∀ j k, K ≤ k → T ≤ cost (R^[k] (x j)) := by
  have hstay : ∀ m, T ≤ cost (R^[K + m] x₀) := by
    intro m
    induction m with
    | zero => simpa using hK
    | succ m ih =>
      have e : R^[K + (m + 1)] x₀ = R (R^[K + m] x₀) := Function.iterate_succ_apply' R (K + m) x₀
      rw [e]
      exact habs _ ih
  intro j k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (hstay m).trans (hcost (hR.iterate (K + m) (hx j)))

/-! ## 4. The Migdal–Kadanoff model -/

section MK

variable {X J : Type*}

/-- **A cost bound on the nontrivial coefficients**: `0 ≤ c j ≤ e^{−s}` for every `j`. -/
def CostBound (c : J → ℝ) (s : ℝ) : Prop := ∀ j, 0 ≤ c j ∧ c j ≤ Real.exp (-s)

theorem costBound_anti {c : J → ℝ} {s s' : ℝ} (h : CostBound c s) (hs : s' ≤ s) :
    CostBound c s' :=
  fun j => ⟨(h j).1, (h j).2.trans (Real.exp_le_exp.2 (neg_le_neg hs))⟩

/-- **Decimation multiplies the cost by `n`**: `c j ↦ (c j)ⁿ` takes a cost bound `s` to `n s`. -/
theorem costBound_decim {c : J → ℝ} {s : ℝ} (n : ℕ) (h : CostBound c s) :
    CostBound (fun j => c j ^ n) (n * s) := fun j => by
  refine ⟨pow_nonneg (h j).1 n, ?_⟩
  calc c j ^ n ≤ Real.exp (-s) ^ n := pow_le_pow_left₀ (h j).1 (h j).2 n
    _ = Real.exp (-(n * s)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **The decimation's cost is exact**: a coefficient at `e^{−s}` goes to `e^{−n s}`. -/
theorem decim_cost_eq {c : J → ℝ} {s : ℝ} (n : ℕ) (j : J) (h : c j = Real.exp (-s)) :
    c j ^ n = Real.exp (-(n * s)) := by
  rw [h, ← Real.exp_nat_mul]; ring_nf

/-- **The one-plaquette inequality for bond moving**: on the class `S`, a cost bound `s ≥ 0` before
bond moving gives the cost bound `min (s + b s²) T / n` after it. -/
def BondMoveCost (S : X → Prop) (coef : X → J → ℝ) (bm : X → X) (n : ℕ) (b T : ℝ) : Prop :=
  ∀ x s, S x → 0 ≤ s → CostBound (coef x) s → CostBound (coef (bm x)) (min (s + b * s ^ 2) T / n)

/-- The extremal capped sequence `σ_{k+1} = min (σ_k + b σ_k²) T`, `σ_0 = s₀`. -/
def cappedRun (b T s₀ : ℝ) : ℕ → ℝ
  | 0 => s₀
  | k + 1 => min (cappedRun b T s₀ k + b * cappedRun b T s₀ k ^ 2) T

theorem cappedRun_runsOneWayTo (b T s₀ : ℝ) : RunsOneWayTo b T (cappedRun b T s₀) :=
  fun _ => le_rfl

theorem cappedRun_nonneg {b T s₀ : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (h0 : 0 ≤ s₀) (k : ℕ) :
    0 ≤ cappedRun b T s₀ k := by
  induction k with
  | zero => exact h0
  | succ k ih => exact le_min (add_nonneg ih (mul_nonneg hb (sq_nonneg _))) hT

/-- **The cost along the MK orbit**: with the class preserved by the step, the decimation exact on
the coefficients and `BondMoveCost`, the `k`-th iterate of `dec ∘ bm` has the cost bound
`cappedRun b T s₀ k`. -/
theorem mk_orbit_cost {S : X → Prop} {coef : X → J → ℝ} {bm dec : X → X} {n : ℕ} {b T s₀ : ℝ}
    (hn : 0 < n) (hb : 0 ≤ b) (hT : 0 ≤ T) (hdec : ∀ y j, coef (dec y) j = coef y j ^ n)
    (hS : ∀ x, S x → S (dec (bm x))) (hbm : BondMoveCost S coef bm n b T) {x : X} (hx : S x)
    (hs₀ : 0 ≤ s₀) (h0 : CostBound (coef x) s₀) (k : ℕ) :
    S ((dec ∘ bm)^[k] x) ∧ CostBound (coef ((dec ∘ bm)^[k] x)) (cappedRun b T s₀ k) := by
  induction k with
  | zero => exact ⟨hx, h0⟩
  | succ k ih =>
    have e : (dec ∘ bm)^[k + 1] x = dec (bm ((dec ∘ bm)^[k] x)) :=
      Function.iterate_succ_apply' _ k x
    rw [e]
    refine ⟨hS _ ih.1, ?_⟩
    have h1 := hbm _ _ ih.1 (cappedRun_nonneg hb hT hs₀ k) ih.2
    have h2 := costBound_decim n h1
    have hfun : coef (dec (bm ((dec ∘ bm)^[k] x)))
        = fun j => coef (bm ((dec ∘ bm)^[k] x)) j ^ n := funext (hdec _)
    rw [hfun]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm : (n : ℝ) * (min (cappedRun b T s₀ k + b * cappedRun b T s₀ k ^ 2) T / n)
        = cappedRun b T s₀ (k + 1) := by
      show _ = min (cappedRun b T s₀ k + b * cappedRun b T s₀ k ^ 2) T
      field_simp
    rwa [hm] at h2

/-- **Capped one-way running of the MK cost, uniformly in the start, under `BondMoveCost`**: with
`b > 0`, `s₀ > 0` and every start in the class with cost at least `s₀`, there is one `K` such that
after every `k ≥ K` MK steps every nontrivial coefficient of every start is at most `e^{−T}`. -/
theorem mk_uniform_of_bondMoveCost {S : X → Prop} {coef : X → J → ℝ} {bm dec : X → X} {n : ℕ}
    {b T s₀ : ℝ} (hn : 0 < n) (hb : 0 < b) (hT : 0 ≤ T) (hs₀ : 0 < s₀)
    (hdec : ∀ y j, coef (dec y) j = coef y j ^ n) (hS : ∀ x, S x → S (dec (bm x)))
    (hbm : BondMoveCost S coef bm n b T) (x : ℕ → X) (hx : ∀ j, S (x j))
    (h0 : ∀ j, CostBound (coef (x j)) s₀) :
    ∃ K : ℕ, ∀ j k, K ≤ k → CostBound (coef ((dec ∘ bm)^[k] (x j))) T := by
  obtain ⟨K, hK⟩ := uniform_steps_of_runsOneWayTo (s := fun _ k => cappedRun b T s₀ k) (T := T)
    hb.le (mul_pos hb (pow_pos hs₀ 2)) hs₀.le (fun _ => le_rfl)
    (fun _ => cappedRun_runsOneWayTo b T s₀)
  exact ⟨K, fun j k hk => costBound_anti
    (mk_orbit_cost hn hb.le hT hdec hS hbm (hx j) hs₀.le (h0 j) k).2 (hK j k hk)⟩

end MK

#print axioms not_runsOneWay_of_linear
#print axioms not_runsOneWay_of_scales
#print axioms tension_not_runsOneWay
#print axioms runsOneWay_family_unsat
#print axioms runsOneWayTo_of_runsOneWay
#print axioms runsOneWayTo_lower
#print axioms uniform_steps_of_runsOneWayTo
#print axioms matchAt_uniform_of_runsOneWayTo
#print axioms scales_runsOneWayTo
#print axioms tension_runsOneWayTo
#print axioms tension_capped_not_uncapped
#print axioms not_runsOneWayTo_of_fixed
#print axioms exp_neg_div_le
#print axioms not_runsOneWayTo_of_nonpert
#print axioms uniform_of_monotone_step
#print axioms costBound_anti
#print axioms costBound_decim
#print axioms decim_cost_eq
#print axioms cappedRun_runsOneWayTo
#print axioms cappedRun_nonneg
#print axioms mk_orbit_cost
#print axioms mk_uniform_of_bondMoveCost

end MassGap.OneWayCost
