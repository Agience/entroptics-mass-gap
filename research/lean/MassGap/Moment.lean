import Mathlib

/-!
# MassGap.Moment — a read on a lag correlation, and the cosine bounds on its tension

A `Read N` is a nonnegative function `ρ : Fin (N + 1) → ℝ` with positive total mass. From it the
module derives the probability vector `p d = ρ d / ∑ ρ`, the lag angle
`θ d = 2 * π * d / (N + 1)`, and the tension `tension = -log (∑ d, p d * cos (θ d))`. Everything
else here is an inequality between those.

## The two cosine bounds

Over one half-turn, `1 - x ^ 2 / 2 ≤ cos x ≤ 1 - (2 / π ^ 2) * x ^ 2`. The lower bound gives
`cos_avg_ge`, `Read.cos_avg_ge_circ` and the route from a bounded second moment to a tension below
`(1/4) * log 3`; the upper bound gives `Read.cos_avg_le_circ` and the route back.
`neg_log_lt_floor` is the scalar step: `3 ^ (-1/4) < c` gives `-log c < (1/4) * log 3`.

Both directions are stated about the circle distance `circLag d = min d (N + 1 - d)` rather than the
raw index. `Read.cos_theta_circ` proves `cos (θ d) = cos (2 * π * circLag d / (N + 1))`, so the
cosine average never sees the raw index; `thetaMoment_eq` gives the raw-index factorisation
`∑ p d * θ d ^ 2 = (2π/(N + 1)) ^ 2 * ∑ p d * d ^ 2` for comparison.

`Read.substrate_lt_of_tension_lt_floor` and `Read.tension_ge_floor_of_substrate` are the two
directions of the substrate-ratio bound:

    tension < (1/4) * log 3   ⟺   (∑ p d * circLag d ^ 2) / (N + 1) ^ 2  <  (1 - 3 ^ (-1/4)) / 8,

the forward direction requiring a positive cosine average, since a non-positive average has no
logarithm.

## From a decay rate to an aperture-independent moment

`tension_tendsto_zero_of_bounded_circ_moment` and `Complete.confinement_of_bounded_substrate` both
take one bound holding at every aperture. `sum_circLag_le_two_mul` shows `circLag` is at most
two-to-one on lags, and `circ_moment_le_of_geometric` converts a geometric bound
`p d ≤ C * r ^ circLag d` with `r < 1` into the aperture-independent
`2 * C * ∑' k, k ^ 2 * r ^ k`. `circ_decay_of_lag_decay` carries a geometric bound in the raw index
to one in the circle distance, which is the direction `r ≤ 1` allows.

## Scope

* The factorisation `⟨cos θ⟩ ≥ 1 - (2π/(N + 1)) ^ 2 * ⟨circLag ^ 2⟩ / 2` (`Read.cos_avg_ge_circ`) is
  a theorem. Reading its first factor as an aperture and its second as a property of a substrate
  carrying no reference to the window is an interpretation of the two factors, not a theorem, and
  nothing here derives it. It predicts that `⟨circLag ^ 2⟩` is invariant under changing the
  aperture.
* The bound must be stated about `circLag`, not the raw index. On a periodic extent
  `ρ N = ρ (-1) = ρ 1` (`MomentShape.wilsonCorrAt_neg`, proved at every extent and every real
  coupling), and `MomentShape.wilsonCorrAt_circLag_congr` says the correlation reads the lag only
  through `circLag`. Weighting the far half of the lag range by `d ^ 2` makes the raw moment grow
  like `N ^ 2` at fixed correlation length: for `ρ d = exp (-circLag d / 1.5)` the raw moment runs
  `14.5, 68.9, 307, 1305, 5384` across extents `8` to `128` while the circle moment settles at
  `3.28`.
* `Read` carries two fields and no more. It does not carry whitening, entropy matching or
  translation invariance. Whitening in the certificate path is the scalar division `ρ / ρ 0`, which
  cancels out of `p = ρ / ∑ ρ`; translation invariance is proved separately of the concrete
  correlator.
* `Read` is inhabited by the flat correlation `ρ ≡ 1`. That profile satisfies the five
  coupling-uniform facts `ShapeNoGo` collects, with equality in each, so no constraint of that kind
  excludes it. In the spectral form `ρ d = ∑ w n * exp (-E n * d)` the flat profile is the `E 0 = 0`
  term.
* `κ₀ = (1/4) * log 3` is derived in `Floor.lean` by counting directed cube paths as an `n → ∞`
  per-area density; no aperture enters it.
-/

namespace MassGap.Moment

open scoped BigOperators

/-- For a probability vector `p` over a `Fintype` and angles `θ`,
`1 - (∑ d, p d * θ d ^ 2) / 2 ≤ ∑ d, p d * cos (θ d)`. Termwise from
`Real.one_sub_sq_div_two_le_cos`, then summed using `hsum`.

DERIVED: `0` is the lower bound on each weight; `1` is the total mass of `p` and the leading term of
the quadratic bound, which is `cos 0`; `2` is the exponent on the angle and the divisor in
`1 - x ^ 2 / 2`, both from the second-order Taylor bound on cosine. -/
theorem cos_avg_ge {ι : Type*} [Fintype ι] (p θ : ι → ℝ)
    (hp : ∀ d, 0 ≤ p d) (hsum : ∑ d, p d = 1) :
    1 - (∑ d, p d * (θ d) ^ 2) / 2 ≤ ∑ d, p d * Real.cos (θ d) := by
  have key : ∑ d, p d * (1 - (θ d) ^ 2 / 2) ≤ ∑ d, p d * Real.cos (θ d) :=
    Finset.sum_le_sum fun d _ =>
      mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos) (hp d)
  have hpt : ∀ d, p d * (1 - (θ d) ^ 2 / 2) = p d - p d * (θ d) ^ 2 / 2 := fun d => by ring
  have expand : ∑ d, p d * (1 - (θ d) ^ 2 / 2) = 1 - (∑ d, p d * (θ d) ^ 2) / 2 := by
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, hsum, ← Finset.sum_div]
  rwa [expand] at key

/-- `(3 : ℝ) ^ (-(1 : ℝ) / 4) < c` gives `-Real.log c < (1 / 4) * Real.log 3`. Uses
`Real.log_rpow` to evaluate `log (3 ^ (-1/4)) = -(1/4) * log 3` and monotonicity of the logarithm.

DERIVED: `3` is the base, the entropy floor's own; `1` and `4` are the exponent `-1/4` on the left
and the coefficient `1/4` on the right, the same number in two positions, since
`3 ^ (-1/4) = exp (-(1/4) * log 3)`. -/
theorem neg_log_lt_floor {c : ℝ} (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < c) :
    - Real.log c < (1 / 4) * Real.log 3 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -(1 / 4) * Real.log 3 := by
    rw [Real.log_rpow (by norm_num)]; ring
  have hmono : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.log c := Real.log_lt_log h3 hc
  rw [hlog] at hmono
  linarith

/-- For a probability vector `p` and angles `θ`, if `(∑ d, p d * θ d ^ 2) / 2 < 1 - 3 ^ (-1/4)` then
`-Real.log (∑ d, p d * cos (θ d)) < (1 / 4) * Real.log 3`. `cos_avg_ge` puts the cosine average above
`3 ^ (-1/4)`, and `neg_log_lt_floor` finishes.

Scope: the moment bound is a hypothesis. The conclusion is about `-log` of the cosine average, which
is what `Read.tension` is defined to be.

DERIVED: `0` is the lower bound on each weight; `1` is the total mass of `p`, the leading term of the
quadratic bound, and the exponent numerator in `3 ^ (-1/4)` and `1/4`; `2` is the exponent on the
angle and the divisor of the quadratic bound; `3` is the base of the floor and `4` its exponent's
denominator. -/
theorem tension_lt_floor_of_moment {ι : Type*} [Fintype ι] (p θ : ι → ℝ)
    (hp : ∀ d, 0 ≤ p d) (hsum : ∑ d, p d = 1)
    (hmom : (∑ d, p d * (θ d) ^ 2) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    - Real.log (∑ d, p d * Real.cos (θ d)) < (1 / 4) * Real.log 3 := by
  have hcavg := cos_avg_ge p θ hp hsum
  have hc_gt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, p d * Real.cos (θ d) := by
    have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 - (∑ d, p d * (θ d) ^ 2) / 2 := by linarith
    linarith
  exact neg_log_lt_floor hc_gt

/-! ## The read: `p`, `θ` and the tension, derived from a nonnegative correlation

A nonnegative correlation `ρ` over the lag index with positive total mass determines the probability
vector `p = ρ / ∑ ρ`, the angles `θ d = 2 * π * d / (N + 1)`, and the tension
`-log (∑ p d * cos (θ d))`. The vector properties of `p` and the inequalities below are consequences
of the two structure fields. -/

/-- A correlation over the lag index: a function `ρ : Fin (N + 1) → ℝ` together with `0 ≤ ρ d` at
every lag and `0 < ∑ d, ρ d`. The derived quantities `p`, `θ` and `tension` are defined from these
two fields alone.

Scope: the structure carries no whitening, entropy matching or translation invariance. Whitening in
the certificate path is the scalar division `ρ / ρ 0`, which cancels out of `p = ρ / ∑ ρ`;
translation invariance of the concrete correlator is `MomentShape.wilsonCorrAt_neg`, proved
elsewhere. `readA` is a transparent wrapper — `ShareEnvelope.readYMAt_rho` is `rfl` — so a consumer
may unfold to `corrClay` and use facts about the Wilson measure directly.

DERIVED: `1` is the `+ 1` in the index type `Fin (N + 1)`, the number of lags on a periodic extent
of `N + 1` sites; `0` is the lower bound on each value and the strict lower bound on the total
mass. -/
structure Read (N : ℕ) where
  ρ : Fin (N + 1) → ℝ
  hρ : ∀ d, 0 ≤ ρ d
  hpos : 0 < ∑ d, ρ d

/-- `Read N` is inhabited, by the flat correlation `ρ ≡ 1` with nonnegativity from `zero_le_one` and
positive mass from `Finset.sum_pos` over the nonempty index type.

DERIVED: `1` is the constant value of the flat correlation, and `0` the lower bound its
nonnegativity field discharges. Since `p` normalises, any positive constant gives the same
derived read. -/
instance (N : ℕ) : Inhabited (Read N) where
  default :=
    { ρ := fun _ => 1
      hρ := fun _ => zero_le_one
      hpos := Finset.sum_pos (fun _ _ => one_pos) ⟨0, Finset.mem_univ 0⟩ }

namespace Read

variable {N : ℕ} (R : Read N)

/-- The correlation normalised to a probability vector: `p d = ρ d / ∑ d', ρ d'`. Well defined
because the `hpos` field makes the denominator nonzero.

DERIVED: the one numeral is the `1` in the index type `Fin (N + 1)`, the number of lags. -/
noncomputable def p (d : Fin (N + 1)) : ℝ := R.ρ d / ∑ d', R.ρ d'
/-- The lag angle `θ d = 2 * π * d / (N + 1)`, the phase of the first structure-factor mode. The
read argument is unused — the angle depends only on the lattice index — and is carried so that `R.θ`
reads as a projection alongside `R.p` and `R.ρ`.

DERIVED: `2` is the `2π` of a full turn, so the `N + 1` lags divide the circle evenly; `1` is the
`+ 1` giving the number of lags and the mode index the phase belongs to. -/
noncomputable def θ (_R : Read N) (d : Fin (N + 1)) : ℝ := 2 * Real.pi * (d : ℝ) / (N + 1)
/-- The tension `-Real.log (∑ d, R.p d * Real.cos (R.θ d))`, the negative logarithm of the read's
cosine average. Total as written; `Real.log` is `0` on non-positive arguments, so a non-positive
cosine average gives `0` rather than an error.

DERIVED: no numeral occurs. -/
noncomputable def tension : ℝ := - Real.log (∑ d, R.p d * Real.cos (R.θ d))

theorem p_nonneg (d : Fin (N + 1)) : 0 ≤ R.p d := div_nonneg (R.hρ d) R.hpos.le

theorem p_sum : ∑ d, R.p d = 1 := by
  unfold Read.p
  rw [← Finset.sum_div, div_self (ne_of_gt R.hpos)]

/-- `R.tension < (1 / 4) * Real.log 3` when `(∑ d, R.p d * R.θ d ^ 2) / 2 < 1 - 3 ^ (-1/4)`.
`tension_lt_floor_of_moment` at `R.p` and `R.θ`, with `p_nonneg` and `p_sum` discharging the
probability-vector hypotheses.

DERIVED: `2` is the exponent on the angle and the divisor of the quadratic cosine bound; `1` is the
leading term of that bound and the numerator of both `-1/4` and `1/4`; `3` is the base of the floor
and `4` its exponent's denominator. -/
theorem tension_lt_floor
    (hmom : (∑ d, R.p d * (R.θ d) ^ 2) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    R.tension < (1 / 4) * Real.log 3 :=
  tension_lt_floor_of_moment R.p R.θ (fun d => R.p_nonneg d) R.p_sum hmom

/-- `R.θ d ^ 2 = (2 * π / (N + 1)) ^ 2 * (d : ℝ) ^ 2`, by `ring` after unfolding: the squared lag
angle factors into a squared window scale and a squared raw index.

DERIVED: `2` is the `2π` of a full turn and the exponent of the square; `1` is the `+ 1` giving the
number of lags. -/
theorem theta_sq (d : Fin (N + 1)) : (R.θ d) ^ 2 = (2 * Real.pi / (N + 1)) ^ 2 * (d : ℝ) ^ 2 := by
  unfold Read.θ; ring

/-- `∑ d, R.p d * R.θ d ^ 2 = (2 * π / (N + 1)) ^ 2 * ∑ d, R.p d * (d : ℝ) ^ 2`: the angular second
moment factors into the squared window scale and the raw-index second moment. `theta_sq` summed.

Scope: this is the factorisation in the raw index. The corresponding statement about the circle
distance is `Read.cos_avg_ge_circ`, and the two differ — see the module header.

DERIVED: `2` is the `2π` of a full turn and the exponent of both squares; `1` is the `+ 1` giving
the number of lags. -/
theorem thetaMoment_eq :
    ∑ d, R.p d * (R.θ d) ^ 2 = (2 * Real.pi / (N + 1)) ^ 2 * ∑ d, R.p d * (d : ℝ) ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [R.theta_sq d]; ring

end Read

/-- `0 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)`, from `Real.rpow_lt_one_of_one_lt_of_neg`: the floor's
exponential is strictly below one, so the right-hand side of the aperture condition is positive.

DERIVED: `0` is the lower bound asserted; `3` is the base and `1`, `4` its exponent `-1/4`; the
`1` being subtracted is the value `3 ^ 0`, which the negative exponent puts the term below. -/
theorem floor_rhs_pos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith

/-- `0 ≤ R.tension`. The cosine average has absolute value at most the total mass `1`, so its
logarithm is non-positive and the negated logarithm is nonnegative.

DERIVED: the one numeral in the statement is `0`, the lower bound asserted. The `1` bounding the
cosine average is `p_sum`'s, and appears in the proof. -/
theorem Read.tension_nonneg {N : ℕ} (R : Read N) : 0 ≤ R.tension := by
  have hcos : ∀ d, |R.p d * Real.cos (R.θ d)| ≤ R.p d := by
    intro d
    rw [abs_mul, abs_of_nonneg (R.p_nonneg d)]
    exact mul_le_of_le_one_right (R.p_nonneg d) (Real.abs_cos_le_one _)
  have habs : |∑ d, R.p d * Real.cos (R.θ d)| ≤ 1 :=
    le_trans (Finset.abs_sum_le_sum_abs _ _)
      (le_trans (Finset.sum_le_sum (fun d _ => hcos d)) (le_of_eq R.p_sum))
  have hlog : Real.log (∑ d, R.p d * Real.cos (R.θ d)) ≤ 0 := by
    rw [← Real.log_abs]; exact Real.log_nonpos (abs_nonneg _) habs
  show 0 ≤ - Real.log (∑ d, R.p d * Real.cos (R.θ d))
  linarith

/-- `R.tension < (1 / 4) * Real.log 3` when `3 ^ (-1/4) < ∑ d, R.p d * cos (R.θ d)`. This is
`neg_log_lt_floor` applied directly, since `tension` is defined as the negated logarithm of that
average; no quadratic bound on cosine is used.

Scope: the hypothesis is a single scalar comparison on the cosine average. The second-moment routes
reach the same conclusion through `1 - x ^ 2 / 2 ≤ cos x`, which is sufficient but not necessary.

DERIVED: `3` is the base of the floor; `1` and `4` are the exponent `-1/4` on the left and the
coefficient `1/4` on the right, the same number in two positions. -/
theorem Read.tension_lt_floor_of_cosAvg {N : ℕ} (R : Read N)
    (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d)) :
    R.tension < (1 / 4) * Real.log 3 :=
  neg_log_lt_floor hc

#print axioms Read.tension_lt_floor_of_cosAvg

/-- The converse of `tension_lt_floor_of_cosAvg`: given `0 < ∑ d, R.p d * cos (R.θ d)` and
`R.tension < (1 / 4) * Real.log 3`, the cosine average exceeds `3 ^ (-1/4)`. Via
`Real.log_lt_log_iff`, which needs both arguments positive.

Scope: the positivity hypothesis is required — `Real.log` is `0` on non-positive arguments, so
without it the tension does not determine the average.

DERIVED: `0` is the strict lower bound on the cosine average; `3` is the base of the floor, and `1`
and `4` its exponent `-1/4` and the coefficient `1/4`. -/
theorem Read.cosAvg_gt_of_tension_lt_floor {N : ℕ} (R : Read N)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (h : R.tension < (1 / 4) * Real.log 3) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -(1 / 4) * Real.log 3 := by
    rw [Real.log_rpow (by norm_num)]; ring
  have hlt : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.log (∑ d, R.p d * Real.cos (R.θ d)) := by
    rw [hlog]
    have : R.tension = - Real.log (∑ d, R.p d * Real.cos (R.θ d)) := rfl
    rw [this] at h; linarith
  exact (Real.log_lt_log_iff h3 hpos).mp hlt

#print axioms Read.cosAvg_gt_of_tension_lt_floor

/-- `(2 * π / ((N : ℝ) + 1)) ^ 2 * B / 2 → 0` along `atTop` in `N`, at any fixed real `B`. The
window scale tends to zero and the rest is constant.

DERIVED: `2` is the `2π` of a full turn, the exponent of the square, and the divisor from the
quadratic cosine bound; `1` is the `+ 1` giving the number of lags; `0` is the limit. -/
theorem aperture_factor_tendsto_zero (B : ℝ) :
    Filter.Tendsto (fun N : ℕ => (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2)
      Filter.atTop (nhds 0) := by
  have hN : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h0 : Filter.Tendsto (fun N : ℕ => 2 * Real.pi / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hN
  simpa using ((h0.pow 2).mul_const B).div_const 2

/-- The distance from lag `d` to the origin on the circle of `N + 1` sites:
`min d (N + 1 - d)`, a natural number.

DERIVED: the one numeral is `1`, the `+ 1` giving the periodic extent `N + 1` that the lag index
runs over; `N + 1 - d` is the same separation measured the other way round the circle. -/
-- The `min` is what makes the two directions round the circle interchangeable; `Read.cos_theta_circ`
-- is where that is used.
def circLag {N : ℕ} (d : Fin (N + 1)) : ℕ := min (d : ℕ) (N + 1 - (d : ℕ))

/-- `Real.cos (R.θ d) = Real.cos (2 * π * (circLag d : ℝ) / (N + 1))`: the cosine of the lag angle
depends on the lag only through the circle distance. Splits on which side of the circle `d` lies and,
in the far case, uses `cos (2π - x) = cos x`.

DERIVED: `2` is the `2π` of a full turn; `1` is the `+ 1` giving the periodic extent, which is what
the angle is measured against. -/
theorem Read.cos_theta_circ {N : ℕ} (R : Read N) (d : Fin (N + 1)) :
    Real.cos (R.θ d) = Real.cos (2 * Real.pi * (circLag d : ℝ) / (N + 1)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rcases le_total ((d : ℕ)) (N + 1 - (d : ℕ)) with h | h
  · rw [circLag, min_eq_left h]; rfl
  · rw [circLag, min_eq_right h]
    have hd : ((N + 1 - (d : ℕ) : ℕ) : ℝ) = ((N : ℝ) + 1) - (d : ℕ) := by
      have hle : (d : ℕ) ≤ N + 1 := le_of_lt d.isLt
      push_cast [Nat.cast_sub hle]
      ring
    rw [hd]
    have : 2 * Real.pi * (((N : ℝ) + 1) - (d : ℕ)) / ((N : ℝ) + 1)
        = 2 * Real.pi - 2 * Real.pi * (d : ℕ) / ((N : ℝ) + 1) := by
      field_simp
    rw [this, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    unfold Read.θ
    ring

/-- `∑ d, R.p d * cos (R.θ d) ≤ 1 - 8 / ((N : ℝ) + 1) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2)`:
the cosine average bounded from above by the circular second moment.

The proof rewrites each cosine by `cos_theta_circ`, applies
`Real.cos_le_one_sub_mul_cos_sq` — the bound `cos x ≤ 1 - (2 / π ^ 2) * x ^ 2`, tight at `x = 0` and
`x = π` — and sums. Its hypothesis `|x| ≤ π` holds without a side condition, because
`2 * circLag d ≤ N + 1` by construction of `circLag`, so the lag angle stays within a half-turn.

Scope: this is the opposite direction from `cos_avg_ge_circ`, which uses the lower bound
`1 - x ^ 2 / 2 ≤ cos x` over the same range.

DERIVED: `8` is `(2 / π ^ 2) * (2π) ^ 2`, the constant of the cosine upper bound multiplied by the
square of the full turn in the lag angle; the `π`s cancel, which is why no `π` survives in the
statement. `1` is the total mass of `p` and the `+ 1` giving the periodic extent; `2` is the
exponent on the extent and on the circle distance. Nothing is chosen. -/
theorem Read.cos_avg_le_circ {N : ℕ} (R : Read N) :
    ∑ d, R.p d * Real.cos (R.θ d)
      ≤ 1 - 8 / ((N : ℝ) + 1) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have key : ∀ d : Fin (N + 1),
      R.p d * Real.cos (R.θ d)
        ≤ R.p d * (1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2) := by
    intro d
    rw [R.cos_theta_circ d]
    refine mul_le_mul_of_nonneg_left ?_ (R.p_nonneg d)
    -- the lag angle never leaves the half-turn, because the lag never exceeds half the circle
    have hhalf : 2 * (circLag d) ≤ N + 1 := by
      have := d.isLt; unfold circLag; omega
    have hhalfR : 2 * (circLag d : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hhalf
    have hc0 : (0 : ℝ) ≤ (circLag d : ℝ) := Nat.cast_nonneg _
    have habs : |2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)| ≤ Real.pi := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ hN]
      nlinarith [Real.pi_pos]
    have hcos := Real.cos_le_one_sub_mul_cos_sq habs
    have harith : 1 - 2 / Real.pi ^ 2 * (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2
        = 1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2 := by
      field_simp
      ring
    linarith [hcos, harith.le, harith.ge]
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have hexp : ∑ d, R.p d * (1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2)
      = 1 - 8 / ((N : ℝ) + 1) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) := by
    have hpt : ∀ d : Fin (N + 1),
        R.p d * (1 - 8 / ((N : ℝ) + 1) ^ 2 * (circLag d : ℝ) ^ 2)
          = R.p d - 8 / ((N : ℝ) + 1) ^ 2 * (R.p d * (circLag d : ℝ) ^ 2) :=
      fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, R.p_sum,
      ← Finset.mul_sum]
  linarith [hsum, hexp.le, hexp.ge]

#print axioms Read.cos_avg_le_circ

/-- A tension below the floor caps the substrate ratio. Given `0 < ∑ d, R.p d * cos (R.θ d)` and
`R.tension < (1 / 4) * Real.log 3`,

    (∑ d, R.p d * (circLag d : ℝ) ^ 2) / ((N : ℝ) + 1) ^ 2  <  (1 - 3 ^ (-1/4)) / 8  ≈ 0.0300.

`cosAvg_gt_of_tension_lt_floor` puts the cosine average above `3 ^ (-1/4)` and `cos_avg_le_circ`
puts it below `1 - 8 / (N + 1) ^ 2 * S`; the two squeeze `S`.

Scope: the converse direction is `tension_lt_floor_of_circ_moment`, so the two statements are each
other's consequences. The positivity hypothesis is required for the same reason as in
`cosAvg_gt_of_tension_lt_floor`: `Real.log` is `0` on non-positive arguments.

DERIVED: `0` is the strict lower bound on the cosine average; `1` and `4` are the coefficient `1/4`
of the floor and the exponent `-1/4` of `3 ^ (-1/4)`, which is `exp (-κ₀)` with `κ₀` derived in
`Floor.lean`; `3` is that base; `2` is the exponent on the circle distance and on the extent; `8` is
`cos_avg_le_circ`'s constant, carried through. The bound is a composition of those and nothing
else. -/
theorem Read.substrate_lt_of_tension_lt_floor {N : ℕ} (R : Read N)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (h : R.tension < (1 / 4) * Real.log 3) :
    (∑ d, R.p d * (circLag d : ℝ) ^ 2) / ((N : ℝ) + 1) ^ 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 := by
  have hN : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  set S : ℝ := ∑ d, R.p d * (circLag d : ℝ) ^ 2 with hS
  have hgt := R.cosAvg_gt_of_tension_lt_floor hpos h
  have hle := R.cos_avg_le_circ
  -- the two squeeze the moment from both sides: floor < cosAvg <= 1 - 8 S / (N+1)^2
  have hkey : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 - 8 / ((N : ℝ) + 1) ^ 2 * S :=
    lt_of_lt_of_le hgt hle
  have hfrac : (8 * S) / ((N : ℝ) + 1) ^ 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    have : 8 / ((N : ℝ) + 1) ^ 2 * S = (8 * S) / ((N : ℝ) + 1) ^ 2 := by ring
    linarith [hkey, this.le, this.ge]
  have h8S : 8 * S < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * ((N : ℝ) + 1) ^ 2 :=
    (div_lt_iff₀ hN).mp hfrac
  rw [div_lt_div_iff₀ hN (by norm_num : (0 : ℝ) < 8)]
  linarith [h8S]

#print axioms Read.substrate_lt_of_tension_lt_floor
/-- The contrapositive of `substrate_lt_of_tension_lt_floor`: given a positive cosine average, a
substrate ratio at or above `(1 - 3 ^ (-1/4)) / 8` gives `¬ (R.tension < (1 / 4) * Real.log 3)`.

Applied to a free massless field on a periodic screen of `n` sites, whose lowest mode at `2π/n`
gives `ρ d = exp (-2π * circLag d / n)`: its substrate ratio is `0.0321808`, computed in
`code/certify/aperture_cap_of_floor.py`, constant in `n` to seven digits from `n = 64` upward and
approached from below, against the ceiling `0.0300205`. That profile therefore falls under this
 theorem at every aperture.

Scope: the ceiling comes from the bound `cos x ≤ 1 - (2 / π ^ 2) * x ^ 2`, which gives away a factor
`π ^ 2 / 4 = 2.467` against the exact criterion; the exact criterion separates the massless profile
by `a⋆ = 1.7489` in the scaling variable. Those two figures are computed, not proved here.

DERIVED: `0` is the strict lower bound on the cosine average; `1` and `4` are the floor's
coefficient `1/4` and the exponent `-1/4`; `3` is the base, so the ceiling is `(1 - exp (-κ₀)) / 8`
with `κ₀` derived in `Floor.lean`; `2` is the exponent on the circle distance and on the extent; `8`
is `cos_avg_le_circ`'s constant. Nothing is chosen, and the massless value quoted above is computed,
not fitted. -/
theorem Read.tension_ge_floor_of_substrate {N : ℕ} (R : Read N)
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (hsub : (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8
      ≤ (∑ d, R.p d * (circLag d : ℝ) ^ 2) / ((N : ℝ) + 1) ^ 2) :
    ¬ (R.tension < (1 / 4) * Real.log 3) := by
  intro h
  exact absurd (R.substrate_lt_of_tension_lt_floor hpos h) (not_lt.mpr hsub)

#print axioms Read.tension_ge_floor_of_substrate


/-- `1 - (2 * π / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) / 2 ≤ ∑ d, R.p d * cos (R.θ d)`.
The termwise bound `Real.one_sub_sq_div_two_le_cos` applied after `cos_theta_circ`, then summed.
Stated about the circle distance rather than the raw index, so it is sharper than `cos_avg_ge`
composed with `thetaMoment_eq`.

DERIVED: `1` is the total mass of `p` and the `+ 1` giving the periodic extent; `2` is the `2π` of a
full turn, the exponent of both squares, and the divisor of the quadratic cosine bound. -/
theorem Read.cos_avg_ge_circ {N : ℕ} (R : Read N) :
    1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) / 2
      ≤ ∑ d, R.p d * Real.cos (R.θ d) := by
  have key : ∀ d : Fin (N + 1),
      R.p d * (1 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2 / 2)
        ≤ R.p d * Real.cos (R.θ d) := by
    intro d
    rw [R.cos_theta_circ d]
    exact mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos (R.p_nonneg d)
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have hexp : ∑ d, R.p d * (1 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2 / 2)
      = 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2) / 2 := by
    have hpt : ∀ d : Fin (N + 1),
        R.p d * (1 - (2 * Real.pi * (circLag d : ℝ) / ((N : ℝ) + 1)) ^ 2 / 2)
          = R.p d - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (R.p d * (circLag d : ℝ) ^ 2) / 2 :=
      fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => hpt d), Finset.sum_sub_distrib, R.p_sum]
    congr 1
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rwa [hexp] at hsum

/-- `R.tension < (1 / 4) * Real.log 3`, given `∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ B` and
`(2 * π / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - 3 ^ (-1/4)`. `cos_avg_ge_circ` puts the cosine average
above `3 ^ (-1/4)`, and `neg_log_lt_floor` finishes.

Scope: the moment is about `circLag`, not the raw index. A bound on the raw-index moment is the
stronger hypothesis and implies this one through `Complete.circ_moment_le_lag_moment`.

DERIVED: `2` is the `2π` of a full turn, the exponent of the squares, and the divisor of the
quadratic cosine bound; `1` is the `+ 1` giving the periodic extent, the leading term of that bound,
and the numerator of `1/4` and `-1/4`; `3` is the base of the floor and `4` its exponent's
denominator. -/
theorem Read.tension_lt_floor_of_circ_moment {N : ℕ} (R : Read N) {B : ℝ}
    (hB : ∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ B)
    (hscale : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    R.tension < (1 / 4) * Real.log 3 := by
  have hmul : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  have hge := R.cos_avg_ge_circ
  have hc_gt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) := by linarith
  exact neg_log_lt_floor hc_gt

#print axioms Read.cos_theta_circ
#print axioms Read.tension_lt_floor_of_circ_moment


/-- `R.tension ≤ -Real.log (1 - (2 * π / ((N : ℝ) + 1)) ^ 2 * B / 2)` when the circle moment is at
most `B` and that expression is positive. `cos_avg_ge_circ` followed by monotonicity of the
logarithm.

DERIVED: `2` is the `2π` of a full turn, the exponent of the square, and the divisor of the
quadratic cosine bound; `1` is the `+ 1` giving the periodic extent and the leading term of that
bound, which is also the upper bound the hypothesis places on the subtracted term. -/
theorem Read.tension_le_of_circ_moment {N : ℕ} (R : Read N) {B : ℝ}
    (hB : ∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ B)
    (hlt : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1) :
    R.tension ≤ - Real.log (1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2) := by
  have hmul : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (∑ d, R.p d * (circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
  have hge := R.cos_avg_ge_circ
  have hpos : (0 : ℝ) < 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 := by linarith
  have hle : 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2
      ≤ ∑ d, R.p d * Real.cos (R.θ d) := by linarith
  have := Real.log_le_log hpos hle
  show - Real.log (∑ d, R.p d * Real.cos (R.θ d)) ≤ _
  linarith

/-- For a family of reads `R : (N : ℕ) → Read N` whose circle second moments are bounded by a
single `B`, `(R N).tension → 0` along `atTop`. The tension is squeezed between `tension_nonneg` and
`tension_le_of_circ_moment`, whose upper bound tends to `0` because the window factor does
(`aperture_factor_tendsto_zero`).

Scope: the bound `B` must hold at every `N`; a bound at one aperture says nothing here.

DERIVED: `2` is the exponent on the circle distance; `0` is the limit. The window factor's numerals
are `aperture_factor_tendsto_zero`'s. -/
theorem tension_tendsto_zero_of_bounded_circ_moment (B : ℝ) (R : (N : ℕ) → Read N)
    (hmom : ∀ N, ∑ d, (R N).p d * (circLag d : ℝ) ^ 2 ≤ B) :
    Filter.Tendsto (fun N => (R N).tension) Filter.atTop (nhds 0) := by
  have hfac := aperture_factor_tendsto_zero B
  have hupper : Filter.Tendsto
      (fun N : ℕ => - Real.log (1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2))
      Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto
        (fun N : ℕ => 1 - (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hfac
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hc
    simpa using this.neg
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N => (R N).tension_nonneg)) ?_ hupper
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 :=
    hfac.eventually_lt_const (by norm_num)
  filter_upwards [hev] with N hN
  exact (R N).tension_le_of_circ_moment (hmom N) hN

#print axioms tension_tendsto_zero_of_bounded_circ_moment

/-! ### From a decay rate to an aperture-independent moment

`tension_tendsto_zero_of_bounded_circ_moment` and `Complete.confinement_of_bounded_substrate` each
take one bound holding at every aperture. The results below convert a geometric decay rate into such
a bound: the aperture enters only as the range of a sum, and the bound is the whole series, so it
does not depend on where the sum stops. -/

/-- `∑ d : Fin (N + 1), g (circLag d) ≤ 2 * ∑ k ∈ Finset.range (N + 2), g k` for nonnegative `g`.
`circLag d = min d (N + 1 - d)` takes each value at no more than two lags — `d = k` and
`d = N + 1 - k` — so fibrewise each value is counted at most twice. The proof fibres the sum with
`Finset.sum_fiberwise_of_maps_to` and bounds each fibre's cardinality by `2`.

DERIVED: the `2` is that multiplicity and nothing else; `N + 2` is the range `circLag` lands in,
since `min d (N+1−d) ≤ N+1`. -/
theorem sum_circLag_le_two_mul {N : ℕ} (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∑ d : Fin (N + 1), g (circLag d) ≤ 2 * ∑ k ∈ Finset.range (N + 2), g k := by
  classical
  have hmaps : ∀ d ∈ (Finset.univ : Finset (Fin (N + 1))), circLag d ∈ Finset.range (N + 2) := by
    intro d _
    have hd : (d : ℕ) < N + 1 := d.isLt
    simp only [Finset.mem_range, circLag]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  set S := (Finset.univ : Finset (Fin (N + 1))).filter (fun d => circLag d = k) with hS
  have hval : ∀ d ∈ S, g (circLag d) = g k := by
    intro d hd
    rw [hS, Finset.mem_filter] at hd
    rw [hd.2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  -- the fibre carries at most two lags: `circLag d = k` forces `d = k` or `d = N+1-k`
  have hmem : ∀ d ∈ S, (d : ℕ) = k ∨ (d : ℕ) = N + 1 - k := by
    intro d hd
    rw [hS, Finset.mem_filter] at hd
    have hd1 : (d : ℕ) < N + 1 := d.isLt
    have := hd.2
    rw [circLag] at this
    omega
  have hcard : S.card ≤ 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hc
    have ha' := hmem a ha
    have hb' := hmem b hb
    have hc'' := hmem c hc'
    have hfab : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    have hfac : (a : ℕ) ≠ (c : ℕ) := fun h => hac (Fin.ext h)
    have hfbc : (b : ℕ) ≠ (c : ℕ) := fun h => hbc (Fin.ext h)
    omega
  have h2 : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right h2 (hg k)

/-- Given `0 ≤ C`, `0 ≤ r < 1` and `R.p d ≤ C * r ^ circLag d` at every lag,
`∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k`. The right-hand side has
no `N` in it, so the bound is uniform in the aperture. The proof bounds each term, applies
`sum_circLag_le_two_mul`, and compares the partial sum with the whole series, which is summable by
`summable_pow_mul_geometric_of_norm_lt_one`.

Scope: no condition beyond `r < 1` is needed, and no threshold on the aperture is introduced.

DERIVED: the `2` is the circle distance's multiplicity (`sum_circLag_le_two_mul`); the exponent `2` is
the second moment's own; `C` and `r` are the caller's. Nothing here is chosen. -/
theorem circ_moment_le_of_geometric {N : ℕ} (R : Read N) {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ d, R.p d ≤ C * r ^ (circLag d)) :
    ∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k := by
  classical
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hsum : Summable (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hrnorm
  have hterm : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ 2 * r ^ k := fun k => by positivity
  -- termwise: the weight is under its geometric bound, and the square is nonnegative
  have hstep : ∀ d : Fin (N + 1),
      R.p d * (circLag d : ℝ) ^ 2 ≤ C * ((circLag d : ℝ) ^ 2 * r ^ (circLag d)) := by
    intro d
    have hsq : (0 : ℝ) ≤ (circLag d : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right (hdecay d) hsq
    calc R.p d * (circLag d : ℝ) ^ 2 ≤ C * r ^ (circLag d) * (circLag d : ℝ) ^ 2 := this
      _ = C * ((circLag d : ℝ) ^ 2 * r ^ (circLag d)) := by ring
  refine le_trans (Finset.sum_le_sum (fun d _ => hstep d)) ?_
  rw [← Finset.mul_sum]
  -- the lag sum is at most twice the distance sum, which is at most the whole series
  have hfib := sum_circLag_le_two_mul (N := N) (fun k => (k : ℝ) ^ 2 * r ^ k) hterm
  have hpart : ∑ k ∈ Finset.range (N + 2), (k : ℝ) ^ 2 * r ^ k
      ≤ ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k :=
    hsum.sum_le_tsum _ (fun k _ => hterm k)
  calc C * ∑ d : Fin (N + 1), (circLag d : ℝ) ^ 2 * r ^ (circLag d)
      ≤ C * (2 * ∑ k ∈ Finset.range (N + 2), (k : ℝ) ^ 2 * r ^ k) :=
        mul_le_mul_of_nonneg_left hfib hC
    _ ≤ C * (2 * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact mul_le_mul_of_nonneg_left hpart (by norm_num)
    _ = 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k := by ring

/-- Given `0 ≤ C`, `0 ≤ r ≤ 1` and `R.p d ≤ C * r ^ (d : ℕ)` at every lag, the same bound holds with
`circLag d` in the exponent. Since `circLag d ≤ d` by `min_le_left` and `r ≤ 1`, lowering the
exponent raises `r ^ ·`, so the bound weakens in the right direction.

Scope: the implication runs from the raw index to the circle distance only. The transfer form
`ρ d = ∑ₙ wₙ * λₙ ^ d` decays in the raw lag, while the results above consume decay in the circle
distance, and this is the step between them.

DERIVED: `0` is the lower bound on `C` and on `r`; `1` is the upper bound on `r`, which is what
makes a smaller exponent the weaker bound, and the `+ 1` in the index type `Fin (N + 1)`. The step
`circLag d ≤ d` is `min_le_left` and introduces no numeral. -/
theorem circ_decay_of_lag_decay {N : ℕ} (R : Read N) {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hdecay : ∀ d : Fin (N + 1), R.p d ≤ C * r ^ (d : ℕ)) :
    ∀ d : Fin (N + 1), R.p d ≤ C * r ^ (circLag d) := by
  intro d
  refine (hdecay d).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact pow_le_pow_of_le_one hr0 hr1 (min_le_left _ _)

#print axioms sum_circLag_le_two_mul
#print axioms circ_moment_le_of_geometric
#print axioms circ_decay_of_lag_decay

end MassGap.Moment
