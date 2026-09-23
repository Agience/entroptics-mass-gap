import Mathlib
import MassGap.Complete
import MassGap.ZeroMode
import MassGap.Spectral

/-!
# MassGap.Substrate — bounds on the circular second moment of a read, and reads that attain them

`MassGap.ym_mass_gap_of_substrate` takes the hypothesis `∃ B, ∀ N β, d2At N β ≤ B`, where
`d2At N β = ∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2` is the second moment of the read's
probability vector about the circle distance. This module bounds that moment for an arbitrary
`Moment.Read`, and constructs reads showing the bound is attained and the moment unbounded in the
aperture.

## The unconditional bound

`circ_moment_le_quarter_sq` gives `∑ d, R.p d * circLag d ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4` for every
`Moment.Read N`, from `Moment.Read.p_sum` and `circLag_le_half`. `d2At_le_quarter_sq` is that at the
Wilson read, and `substrateRatio_le_quarter` divides the aperture out to give
`substrateRatio N β ≤ 1 / 4`.

`quarter_ratio_fails_aperture_criterion` shows `1 / 4` does not satisfy
`ym_mass_gap_of_ratio`'s condition `(2 * π) ^ 2 * c / 2 < 1 - 3 ^ (-1/4)`: the left side exceeds
`4.9` and the right side is below `1`. `quarter_bound_grows_without_bound` shows
`((N : ℝ) + 1) ^ 2 / 4` admits no `N`-independent bound.

## Reads attaining and exceeding it

`antipodeRead k` puts all weight at the antipode of a circle of even period `2 * (k + 1)`. It
satisfies `ρ ≥ 0` and `∑ ρ > 0` — the two clauses `wilson_reflection_positive_at` asserts — and
`antipodeRead_moment_eq_quarter_sq` computes its moment as exactly `((N : ℝ) + 1) ^ 2 / 4`.
`rp_alone_leaves_moment_unbounded` uses it to exceed any `B`.

`flatRead k` is `ρ ≡ 1`. `flatSpectral` exhibits it as a `Spectral.PeriodicSpectralForm` with a
single mode at `lam = 1`, so it satisfies the periodic transfer form
`ρ d = ∑ₖ wₖ (λₖ ^ d + λₖ ^ (n - d))` with `wₖ ≥ 0` and `λₖ ∈ [0, 1]`. `flatRead_moment` computes
its moment as `(n ^ 2 + 2) / 12` at period `n = 2 * (k + 1)`, `flatRead_exceeds_ceiling` puts its
ratio above `(1 - 3 ^ (-1/4)) / 8`, and `spectral_form_alone_leaves_moment_unbounded` shows the
moment exceeds any `B`.

`substrate_bound_needs_more_than_positivity` states the two facts together: the read interface gives
`((N : ℝ) + 1) ^ 2 / 4`, and over all apertures the moment exceeds every constant.

## A bounded moment does not give a decay rate

`confinement_of_geometric_decay` consumes `p d ≤ C * r ^ circLag d` with one `r < 1` across all `N`
and `β`. `tailRead k` carries weight `1` at lag zero and `tailWeight k = 1 / (k + 1) ^ 3` at the
antipode. `tailRead_moment_le_one` bounds its moment by `1` at every aperture, and
`bounded_moment_does_not_give_geometric_decay` shows no such `(C, r)` exists for the family, since
`(k + 1) ^ 3 * r ^ (k + 1) → 0`.

## Scope

None of these results refutes `∃ B, ∀ N β, d2At N β ≤ B`, which is a statement about the constructed
correlation `wilsonCorrAt`. What the witness reads establish is that the bound does not follow from
the `Moment.Read` interface, nor from the two clauses of `wilson_reflection_positive_at`, nor from
`Spectral.PeriodicSpectralForm`. The bound `λ ≤ 1` in that form is contractivity, not a gap, which
is why the flat read satisfies it.
-/

namespace MassGap.Substrate

open MassGap.Moment

/-! ### The unconditional aperture bound -/

/-- `2 * Moment.circLag d ≤ N + 1` for every `d : Fin (N + 1)`: the circle lag, being
`min d (N + 1 - d)`, never exceeds half the period. By `omega`.

DERIVED: `1` is the `+ 1` giving the period `N + 1` from the index bound; `2` is the doubling that
turns the half-period bound into an integer inequality. -/
theorem two_mul_circLag_le {N : ℕ} (d : Fin (N + 1)) : 2 * Moment.circLag d ≤ N + 1 := by
  have h := d.isLt
  unfold Moment.circLag
  omega

/-- `(circLag d : ℝ) ≤ ((N : ℝ) + 1) / 2`, the previous inequality cast to the reals.

DERIVED: `1` is the `+ 1` giving the period; `2` is the halving of it. -/
theorem circLag_le_half {N : ℕ} (d : Fin (N + 1)) :
    ((Moment.circLag d : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
  have h : 2 * Moment.circLag d ≤ N + 1 := two_mul_circLag_le d
  have hR : (2 : ℝ) * ((Moment.circLag d : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  linarith

/-- `∑ d, R.p d * (circLag d : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4` for every `Moment.Read N`. Bounds
each term using `circLag_le_half` and nonnegativity of `p`, then sums using `Moment.Read.p_sum`.

Scope: no hypothesis beyond the `Moment.Read` interface. The bound carries the aperture `N`.

DERIVED: `2` is the moment's order and the square it induces on the half-period; `1` is the `+ 1`
giving the period `N + 1`; `4` is `2 ^ 2`, the square of the halving in `circLag_le_half`. Nothing
is chosen. -/
theorem circ_moment_le_quarter_sq {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4 := by
  have key : ∀ d : Fin (N + 1),
      R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 ≤ R.p d * (((N : ℝ) + 1) ^ 2 / 4) := by
    intro d
    refine mul_le_mul_of_nonneg_left ?_ (R.p_nonneg d)
    have h0 : (0 : ℝ) ≤ ((Moment.circLag d : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 := circLag_le_half d
    nlinarith
  calc ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
      ≤ ∑ d, R.p d * (((N : ℝ) + 1) ^ 2 / 4) := Finset.sum_le_sum (fun d _ => key d)
    _ = ((N : ℝ) + 1) ^ 2 / 4 := by rw [← Finset.sum_mul, R.p_sum, one_mul]

#print axioms circ_moment_le_quarter_sq

/-- `d2At N β ≤ ((N : ℝ) + 1) ^ 2 / 4` at every aperture and coupling: `circ_moment_le_quarter_sq`
at `readYMAt N β`.

Scope: the bound depends on `N`, so it is not of the form `∃ B, ∀ N β, d2At N β ≤ B` that
`ym_mass_gap_of_substrate` consumes; `quarter_bound_grows_without_bound` records that the right-hand
side has no `N`-independent bound.

DERIVED: `2` is the moment's order, `1` the `+ 1` giving the period, `4` the square of the halving,
all inherited from `circ_moment_le_quarter_sq`. -/
theorem d2At_le_quarter_sq (N : ℕ) (β : ℝ) : MassGap.d2At N β ≤ ((N : ℝ) + 1) ^ 2 / 4 := by
  unfold MassGap.d2At
  exact circ_moment_le_quarter_sq (MassGap.readYMAt N β)

#print axioms d2At_le_quarter_sq

/-- `substrateRatio N β ≤ 1 / 4` at every aperture and coupling: `d2At_le_quarter_sq` with the
aperture divided out, through `substrateRatio_le_iff`.

DERIVED: `1 / 4` is the previous bound's `((N : ℝ) + 1) ^ 2 / 4` divided by `((N : ℝ) + 1) ^ 2`, so
the `4` is still the square of the halving in `circLag_le_half` and the `1` its numerator. -/
theorem substrateRatio_le_quarter (N : ℕ) (β : ℝ) : MassGap.substrateRatio N β ≤ 1 / 4 := by
  rw [MassGap.substrateRatio_le_iff]
  have := d2At_le_quarter_sq N β
  linarith

#print axioms substrateRatio_le_quarter

/-- **The trivial bound cannot be fed to the flagship.** `ym_mass_gap_of_ratio` consumes
`substrateRatio ≤ c` provided `c` clears `(2π)²c/2 < 1 − 3^{-1/4}`. At `c = 1/4` — the best constant
the read interface supports (`substrateRatio_le_quarter`, `antipodeRead_moment_eq_quarter_sq`) — that
condition fails: the left side is `π²/2 > 4.9` and the right side is below `1`. So the unconditional
bound is not merely weaker than what is needed, it is on the wrong side of the criterion, and
`substrateRatio_le_quarter` discharges nothing.

DERIVED: nothing here is chosen. `(2π)²/2` is the aperture factor of
`Moment.Read.tension_lt_floor_of_circ_moment` with the window divided out; `3^{-1/4}` is `e^{-κ₀}`
with `κ₀` proved in `Floor`; `1/4` is the attained bound above. -/
theorem quarter_ratio_fails_aperture_criterion :
    ¬ ((2 * Real.pi) ^ 2 * (1 / 4 : ℝ) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  intro h
  nlinarith [hpi, h3]

#print axioms quarter_ratio_fails_aperture_criterion

/-- `¬ ∃ B, ∀ N, ((N : ℝ) + 1) ^ 2 / 4 ≤ B`: the right-hand side of `d2At_le_quarter_sq` has no
bound independent of the aperture. Given a candidate `B`, `exists_nat_gt` supplies `k > B` and the
 instance at `N = 4 * k` exceeds it.

DERIVED: `2` is the moment's order, `1` the `+ 1` giving the period, `4` the square of the halving —
all carried from `d2At_le_quarter_sq`'s right-hand side. The `4 * k` of the proof is a convenient
instance. -/
theorem quarter_bound_grows_without_bound :
    ¬ ∃ B : ℝ, ∀ N : ℕ, ((N : ℝ) + 1) ^ 2 / 4 ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_gt B
  have h := hB (4 * k)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hc : ((4 * k : ℕ) : ℝ) = 4 * (k : ℝ) := by push_cast; ring
  rw [hc] at h
  nlinarith

#print axioms quarter_bound_grows_without_bound

/-! ### The bound is attained, so the axiom supports no better constant -/

/-- The antipodal lag on a circle of period `2k+2`.

DERIVED: `2 * k + 1` is the aperture whose period `2k+2` is even, which is the only case in which an
antipode exists as a lag at all; `k + 1` is then half that period, and it is what `min d (n−d)`
returns there. Neither is a magnitude — both are forced by the requirement that the point be the
antipode. -/
def antipode (k : ℕ) : Fin (2 * k + 1 + 1) := ⟨k + 1, by omega⟩

/-- `Moment.circLag (antipode k) = k + 1`: the circle lag of the antipode is half the period
`2 * (k + 1)`, since `min (k + 1) ((2 * k + 2) - (k + 1))` is `k + 1`.

DERIVED: `1` is the `+ 1` in `k + 1`, half the even period `2 * k + 2`, which is what `min` returns
at the antipode. -/
theorem circLag_antipode (k : ℕ) : Moment.circLag (antipode k) = k + 1 := by
  have hv : ((antipode k : Fin (2 * k + 1 + 1)) : ℕ) = k + 1 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- **A read that puts all its weight at the antipode.** It satisfies exactly what
`wilson_reflection_positive_at` asserts — `ρ ≥ 0` and `∑ ρ > 0` — and nothing else.

DERIVED: the `1` and `0` are the two values of an indicator, so they are the definition of "all the
weight at one lag" rather than a magnitude; any positive value in place of the `1` gives the same
read, since `p` normalises. `2 * k + 1` is the even-period aperture `antipode` needs. -/
noncomputable def antipodeRead (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun d => if d = antipode k then 1 else 0
  hρ := fun d => by split <;> norm_num
  hpos := by simp

theorem antipodeRead_sum (k : ℕ) : ∑ d, (antipodeRead k).ρ d = 1 := by
  show ∑ d, (if d = antipode k then (1 : ℝ) else 0) = 1
  simp

/-- `∑ d, (antipodeRead k).p d * (circLag d : ℝ) ^ 2 = (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 / 4`: the
antipodal read attains the bound of `circ_moment_le_quarter_sq` exactly, at aperture `2 * k + 1`.
The sum collapses by `Finset.sum_ite_eq'` and `circLag_antipode` gives the lag.

Scope: attainment means no constant smaller than `1 / 4` follows from the `Moment.Read` interface
alone.

DERIVED: `2` is the moment's order and the doubling in the even aperture `2 * k + 1`; `1` is the
`+ 1` in that aperture and the `+ 1` giving the period; `4` is the square of the halving, as in
`circ_moment_le_quarter_sq`. -/
theorem antipodeRead_moment_eq_quarter_sq (k : ℕ) :
    ∑ d, (antipodeRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
      = (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 / 4 := by
  have hsum := antipodeRead_sum k
  have hp : ∀ d, (antipodeRead k).p d = (antipodeRead k).ρ d := by
    intro d; simp [Moment.Read.p, hsum]
  have hterm : ∀ d : Fin (2 * k + 1 + 1),
      (antipodeRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
        = if d = antipode k then ((Moment.circLag d : ℕ) : ℝ) ^ 2 else 0 := by
    intro d
    rw [hp d]
    show (if d = antipode k then (1 : ℝ) else 0) * _ = _
    split <;> ring
  rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_ite_eq' Finset.univ (antipode k)
    (fun d => ((Moment.circLag d : ℕ) : ℝ) ^ 2)]
  simp only [Finset.mem_univ, if_true]
  rw [circLag_antipode k]
  push_cast
  ring

#print axioms antipodeRead_moment_eq_quarter_sq

/-- For every `B : ℝ` there are an aperture `N` and a `Moment.Read N` whose circular second moment
exceeds `B`. The witness is `antipodeRead k` at `N = 2 * k + 1` for any `k > B`, whose moment is
`((k : ℝ) + 1) ^ 2` by `antipodeRead_moment_eq_quarter_sq`.

Scope: the witness satisfies exactly the two clauses `wilson_reflection_positive_at` asserts, so the
moment bound does not follow from those clauses. This says nothing about the moment of the
constructed `wilsonCorrAt`.

DERIVED: the one numeral in the statement is the exponent `2`, the moment's order. -/
theorem rp_alone_leaves_moment_unbounded (B : ℝ) :
    ∃ (N : ℕ) (R : Moment.Read N), B < ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨2 * k + 1, antipodeRead k, ?_⟩
  rw [antipodeRead_moment_eq_quarter_sq k]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcast : (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 / 4 = ((k : ℝ) + 1) ^ 2 := by push_cast; ring
  rw [hcast]
  nlinarith

#print axioms rp_alone_leaves_moment_unbounded

/-! ### Nor does the full periodic spectral form help -/

/-- **A read that is flat around the circle.** `ρ ≡ 1` — the correlation of a theory with no decay at
all.

DERIVED: the `1` is the constant value of a flat correlation, and `p` normalises it away, so no other
value gives a different read. `2 * k + 1` is the even-period aperture the exact moment
(`ZeroMode.sum_clag_sq`) is computed at. -/
noncomputable def flatRead (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun _ => 1
  hρ := fun _ => zero_le_one
  hpos := by simp; positivity

/-- **The flat read has the periodic transfer form reflection positivity is cited for**, with a
single mode at `λ = 1`. `λ ≤ 1` is contractivity of a probability measure's transfer operator, not a
gap, so nothing in `Spectral.PeriodicSpectralForm` excludes this.

DERIVED: `λ = 1` is the no-decay mode this read IS, and the weight `1/2` is then forced, not chosen —
the form sums `λ^d + λ^{n−d}`, which is `2` at `λ = 1`, so the weight reproducing `ρ ≡ 1` can only be
the reciprocal of that. `2 * k + 1 + 1` is the period of the aperture `flatRead` is built at. -/
noncomputable def flatSpectral (k : ℕ) :
    MassGap.Spectral.PeriodicSpectralForm (2 * k + 1 + 1) (fun _ => (1 : ℝ)) where
  Idx := Unit
  w := fun _ => 1 / 2
  lam := fun _ => 1
  hw := fun _ => by norm_num
  hlam0 := fun _ => by norm_num
  hlam1 := fun _ => le_refl 1
  hrep := by
    intro d
    have h1 : ∀ m : ℕ, (1 : ℝ) ^ m = 1 := fun m => one_pow m
    simp only [h1]
    norm_num

theorem flatRead_sum (k : ℕ) :
    ∑ d, (flatRead k).ρ d = ((2 * (k + 1) : ℕ) : ℝ) := by
  have hcard : ∑ _d : Fin (2 * k + 1 + 1), (1 : ℝ) = ((2 * k + 1 + 1 : ℕ) : ℝ) := by simp
  calc ∑ d, (flatRead k).ρ d = ∑ _d : Fin (2 * k + 1 + 1), (1 : ℝ) := rfl
    _ = ((2 * k + 1 + 1 : ℕ) : ℝ) := hcard
    _ = ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring

/-- `∑ d, (flatRead k).p d * (circLag d : ℝ) ^ 2 = (((2 * (k + 1) : ℕ) : ℝ) ^ 2 + 2) / 12` at period
`n = 2 * (k + 1)`. The uniform weight factors out, `ZeroMode.sum_circLag_eq_range` reindexes the sum,
and `ZeroMode.sum_clag_sq` evaluates it as `12 * ∑ clag ^ 2 = n ^ 3 + 2 * n`.

DERIVED: `2` is the moment's order, the doubling in the even period `2 * (k + 1)`, and the additive
term in `n ^ 2 + 2` that comes from `n ^ 3 + 2 * n` divided by `n`; `1` is the `+ 1` in `k + 1`;
`12` is the denominator `ZeroMode.sum_clag_sq` produces. All are computed. -/
theorem flatRead_moment (k : ℕ) :
    ∑ d, (flatRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
      = (((2 * (k + 1) : ℕ) : ℝ) ^ 2 + 2) / 12 := by
  have hn : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
  have hsum := flatRead_sum k
  have hp : ∀ d, (flatRead k).p d = 1 / ((2 * (k + 1) : ℕ) : ℝ) := by
    intro d
    show (1 : ℝ) / (∑ d', (flatRead k).ρ d') = _
    rw [hsum]
  have hterm : ∀ d : Fin (2 * k + 1 + 1),
      (flatRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
        = (1 / ((2 * (k + 1) : ℕ) : ℝ)) * ((Moment.circLag d : ℕ) : ℝ) ^ 2 := by
    intro d; rw [hp d]
  rw [Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.mul_sum]
  have hmom : ∑ d : Fin (2 * k + 1 + 1), ((Moment.circLag d : ℕ) : ℝ) ^ 2
      = ∑ d ∈ Finset.range (2 * (k + 1)),
          ((MassGap.ZeroMode.clag (2 * (k + 1)) d : ℕ) : ℝ) ^ 2 := by
    have h := MassGap.ZeroMode.sum_circLag_eq_range (N := 2 * k + 1) (fun c => ((c : ℕ) : ℝ) ^ 2)
    have he : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    rw [h, he]
  rw [hmom]
  have h12 := MassGap.ZeroMode.sum_clag_sq k
  have hval : ∑ d ∈ Finset.range (2 * (k + 1)),
      ((MassGap.ZeroMode.clag (2 * (k + 1)) d : ℕ) : ℝ) ^ 2
      = (((2 * (k + 1) : ℕ) : ℝ) ^ 3 + 2 * ((2 * (k + 1) : ℕ) : ℝ)) / 12 := by
    linarith
  rw [hval]
  field_simp

#print axioms flatRead_moment

/-- `(1 : ℝ) / 3 < (3 : ℝ) ^ (-(1 : ℝ) / 4)`. Since the base exceeds one, `Real.rpow` is increasing
in the exponent, and `-1/4 > -1` with `3 ^ (-1) = 1 / 3`.

DERIVED: `3` is the base, which is the entropy floor's own; `1` and `4` are the exponent `-1/4`, and
`1 / 3` is `3 ^ (-1)`, the value at the comparison exponent `-1`. -/
theorem one_third_lt_rpow : (1 : ℝ) / 3 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hbase : (1 : ℝ) < 3 := by norm_num
  have hlt : (3 : ℝ) ^ (-(1 : ℝ)) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    rw [Real.rpow_lt_rpow_left_iff hbase]
    norm_num
  have hone : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
    norm_num
  rw [hone] at hlt
  exact hlt

/-- `(1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 < 1 / 12`, by `linarith` from `one_third_lt_rpow`. The left
side is the ceiling `Moment.Read.substrate_lt_of_tension_lt_floor` places on the substrate ratio;
`1 / 12` is the value the flat read's ratio approaches from above.

DERIVED: `3`, `1` and `4` are the floor `3 ^ (-1/4)`, as above; `8` is the divisor
`substrate_lt_of_tension_lt_floor` carries; `12` is `flatRead_moment`'s denominator. -/
theorem ceiling_lt_twelfth : (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 < 1 / 12 := by
  have h := one_third_lt_rpow
  linarith

#print axioms ceiling_lt_twelfth

/-- At every `k`, `(1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8` is strictly below the flat read's substrate
ratio. Rewriting by `flatRead_moment`, that ratio is `1 / 12 + (2 / 12) / n ^ 2` with
`n = 2 * (k + 1)`, which exceeds `1 / 12`, which exceeds the left side by `ceiling_lt_twelfth`.

Scope: the flat read satisfies `Spectral.PeriodicSpectralForm` via `flatSpectral`, so that form does
not exclude a correlation whose ratio is above this ceiling.

DERIVED: `3`, `1` and `4` are the floor `3 ^ (-1/4)`; `8` is the ceiling's divisor; `2` is the
moment's order and the doubling in the aperture `2 * k + 1`; the `1`s are the `+ 1`s of the period
and the aperture. `12` appears in the proof, from `flatRead_moment`. -/
theorem flatRead_exceeds_ceiling (k : ℕ) :
    (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8
      < (∑ d, (flatRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2)
          / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
  have hcast : (((2 * k + 1 : ℕ) : ℝ) + 1) = ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring
  have hn : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
  rw [flatRead_moment k, hcast]
  have hratio : ((((2 * (k + 1) : ℕ) : ℝ) ^ 2 + 2) / 12) / ((2 * (k + 1) : ℕ) : ℝ) ^ 2
      = 1 / 12 + (2 / 12) / ((2 * (k + 1) : ℕ) : ℝ) ^ 2 := by
    field_simp
  rw [hratio]
  have hpos : (0 : ℝ) < (2 / 12) / ((2 * (k + 1) : ℕ) : ℝ) ^ 2 := by positivity
  linarith [ceiling_lt_twelfth]

#print axioms flatRead_exceeds_ceiling

/-- For every `B : ℝ` there is a `k`, a `Spectral.PeriodicSpectralForm (2 * k + 1 + 1) (fun _ => 1)`,
and the read `flatRead k` agreeing with that constant correlation, whose circular second moment
exceeds `B`. The witness is `flatSpectral k` for any `k > 12 * B`, using `flatRead_moment`.

Scope: the witness carries the full periodic transfer form — nonnegative weights and `λ ∈ [0, 1]` —
so that form does not bound the moment either. It has `λ = 1`; a bound `λ` strictly below one is not
part of the form.

DERIVED: `2` is the moment's order and the doubling in the period `2 * k + 1 + 1`; the `1`s are the
two `+ 1`s of that period and the constant value of the correlation. The `12 * B` of the proof comes
from `flatRead_moment`'s denominator. -/
theorem spectral_form_alone_leaves_moment_unbounded (B : ℝ) :
    ∃ (k : ℕ) (_S : MassGap.Spectral.PeriodicSpectralForm (2 * k + 1 + 1) (fun _ => (1 : ℝ))),
      (∀ d, (flatRead k).ρ d = (fun _ => (1 : ℝ)) d) ∧
        B < ∑ d, (flatRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (12 * B)
  refine ⟨k, flatSpectral k, fun _ => rfl, ?_⟩
  rw [flatRead_moment k]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcast : ((2 * (k + 1) : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  nlinarith

#print axioms spectral_form_alone_leaves_moment_unbounded

/-- The two facts together: every `Moment.Read N` has circular second moment at most
`((N : ℝ) + 1) ^ 2 / 4`, and for every `B` there is an aperture and a read whose moment exceeds `B`.
The conjunction of `circ_moment_le_quarter_sq` and `rp_alone_leaves_moment_unbounded`.

Scope: both quantify over arbitrary `Moment.Read`, not over `readYMAt`. The statement is about what
the interface alone yields; it leaves `∃ B, ∀ N β, d2At N β ≤ B` untouched, since that is a claim
about the constructed correlation.

DERIVED: `2` is the moment's order, `1` the `+ 1` giving the period, `4` the square of the halving,
all inherited from `circ_moment_le_quarter_sq`. -/
theorem substrate_bound_needs_more_than_positivity :
    (∀ (N : ℕ) (R : Moment.Read N),
        ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4) ∧
      (∀ B : ℝ, ∃ (N : ℕ) (R : Moment.Read N),
        B < ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2) :=
  ⟨fun _N R => circ_moment_le_quarter_sq R, rp_alone_leaves_moment_unbounded⟩

#print axioms substrate_bound_needs_more_than_positivity

/-! ### A bounded moment does not give a uniform decay rate

`confinement_of_geometric_decay` reaches its conclusion from `p d ≤ C * r ^ circLag d` with one
`r < 1`. The reads below have circular second moment at most `1` at every aperture and satisfy no
such bound: a far atom whose weight falls off polynomially in the aperture contributes a vanishing
amount to the moment while defeating every geometric bound. -/

/-- The far-tail weight: the reciprocal cube of the half-period.

DERIVED: the exponent `3` is the smallest integer for which the far atom's contribution to the
second moment, which carries a factor `(k+1)²`, still tends to zero — so it is fixed by the moment it
must not disturb, not chosen for size. The `1` is the numerator of a reciprocal. -/
noncomputable def tailWeight (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1) ^ 3

theorem tailWeight_pos (k : ℕ) : 0 < tailWeight k := by
  unfold tailWeight; positivity

theorem tailWeight_le_one (k : ℕ) : tailWeight k ≤ 1 := by
  unfold tailWeight
  rw [div_le_one (by positivity)]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
  have h3 : (0 : ℝ) ≤ (k : ℝ) ^ 3 := by positivity
  nlinarith [hk, h2, h3]

/-- **A read with a contact term and a polynomially faint far tail.** Weight `1` at lag zero and
`tailWeight k` at the antipode. It satisfies the two clauses of `wilson_reflection_positive_at`, its
circular second moment is at most `1` at every aperture, and it obeys no geometric decay bound.

DERIVED: the `1` at lag zero is the contact normalisation the far weight is measured against — `p`
divides by the total, so only the ratio of the two matters and the `1` fixes the scale of nothing.
The `0` is the absence of weight at every other lag. `2 * k + 1` is the even-period aperture the
antipode needs. -/
noncomputable def tailRead (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun d => (if d = 0 then 1 else 0) + (if d = antipode k then tailWeight k else 0)
  hρ := fun d => by
    have h1 : (0 : ℝ) ≤ if d = 0 then 1 else 0 := by split <;> norm_num
    have h2 : (0 : ℝ) ≤ if d = antipode k then tailWeight k else 0 := by
      split
      · exact (tailWeight_pos k).le
      · exact le_refl 0
    linarith
  hpos := by
    have hsplit : ∑ d : Fin (2 * k + 1 + 1),
        ((if d = 0 then (1 : ℝ) else 0) + (if d = antipode k then tailWeight k else 0))
        = (∑ d : Fin (2 * k + 1 + 1), (if d = 0 then (1 : ℝ) else 0))
          + ∑ d : Fin (2 * k + 1 + 1), (if d = antipode k then tailWeight k else 0) :=
      Finset.sum_add_distrib
    show (0 : ℝ) < ∑ d : Fin (2 * k + 1 + 1),
        ((if d = 0 then (1 : ℝ) else 0) + (if d = antipode k then tailWeight k else 0))
    rw [hsplit, Finset.sum_ite_eq' Finset.univ (0 : Fin (2 * k + 1 + 1)) (fun _ => (1 : ℝ)),
      Finset.sum_ite_eq' Finset.univ (antipode k) (fun _ => tailWeight k)]
    simp only [Finset.mem_univ, if_true]
    linarith [tailWeight_pos k]

theorem tailRead_sum (k : ℕ) : ∑ d, (tailRead k).ρ d = 1 + tailWeight k := by
  show ∑ d : Fin (2 * k + 1 + 1),
      ((if d = 0 then (1 : ℝ) else 0) + (if d = antipode k then tailWeight k else 0)) = _
  rw [Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (2 * k + 1 + 1)) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ (antipode k) (fun _ => tailWeight k)]
  simp

/-- `Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0`: the circle lag at the origin is zero, so the
contact term contributes nothing to a second moment.

DERIVED: `2` is the doubling in the period `2 * k + 1 + 1`; the `1`s are its two increments; `0` is
the index and the resulting lag. -/
theorem circLag_zero (k : ℕ) : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by
  have hv : ((0 : Fin (2 * k + 1 + 1)) : ℕ) = 0 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- `∑ d, (tailRead k).p d * (circLag d : ℝ) ^ 2 ≤ 1` at every `k`. The contact term sits at lag
zero and contributes nothing (`circLag_zero`); the far atom carries `tailWeight k = 1 / (k + 1) ^ 3`
at squared distance `(k + 1) ^ 2`, so the unnormalised moment is `1 / (k + 1)`, and dividing by the
total mass, which is at least `1`, keeps it at or below `1`.

DERIVED: `2` is the moment's order; `1` is the bound asserted, which is also the contact weight the
total mass is at least. The exponent `3` of `tailWeight` appears in the proof. -/
theorem tailRead_moment_le_one (k : ℕ) :
    ∑ d, (tailRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 ≤ 1 := by
  have hS := tailRead_sum k
  have hSpos : (0 : ℝ) < ∑ d, (tailRead k).ρ d := (tailRead k).hpos
  have hSge : (1 : ℝ) ≤ ∑ d, (tailRead k).ρ d := by
    rw [hS]; linarith [(tailWeight_pos k).le]
  -- the ρ-weighted moment, computed exactly
  have hterm : ∀ d : Fin (2 * k + 1 + 1),
      (tailRead k).ρ d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
        = (if d = 0 then (1 : ℝ) * ((Moment.circLag d : ℕ) : ℝ) ^ 2 else 0)
          + (if d = antipode k then tailWeight k * ((Moment.circLag d : ℕ) : ℝ) ^ 2 else 0) := by
    intro d
    show ((if d = 0 then (1 : ℝ) else 0) + (if d = antipode k then tailWeight k else 0))
        * ((Moment.circLag d : ℕ) : ℝ) ^ 2 = _
    split_ifs <;> ring
  have hnum : ∑ d, (tailRead k).ρ d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
      = tailWeight k * ((k : ℝ) + 1) ^ 2 := by
    rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (0 : Fin (2 * k + 1 + 1))
        (fun d => (1 : ℝ) * ((Moment.circLag d : ℕ) : ℝ) ^ 2),
      Finset.sum_ite_eq' Finset.univ (antipode k)
        (fun d => tailWeight k * ((Moment.circLag d : ℕ) : ℝ) ^ 2)]
    simp only [Finset.mem_univ, if_true]
    rw [circLag_zero k, circLag_antipode k]
    push_cast
    ring
  have hpeq : ∑ d, (tailRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2
      = (∑ d, (tailRead k).ρ d * ((Moment.circLag d : ℕ) : ℝ) ^ 2) / (∑ d, (tailRead k).ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  rw [hpeq, hnum, div_le_one hSpos]
  have hval : tailWeight k * ((k : ℝ) + 1) ^ 2 = 1 / ((k : ℝ) + 1) := by
    unfold tailWeight
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    field_simp
  rw [hval]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hk]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  linarith

#print axioms tailRead_moment_le_one

/-- `tailWeight k / 2 ≤ (tailRead k).p (antipode k)`. The unnormalised weight at the antipode is
exactly `tailWeight k`, and the total mass `1 + tailWeight k` is at most `2` by
`tailWeight_le_one`, so dividing loses at most a factor of two.

DERIVED: the one numeral is `2`, the upper bound on the total mass `1 + tailWeight k`, which is what
the division by that total can cost. -/
theorem tailRead_p_antipode (k : ℕ) : tailWeight k / 2 ≤ (tailRead k).p (antipode k) := by
  have hS := tailRead_sum k
  have hne : antipode k ≠ (0 : Fin (2 * k + 1 + 1)) := by
    intro h
    have : ((antipode k : Fin (2 * k + 1 + 1)) : ℕ) = ((0 : Fin (2 * k + 1 + 1)) : ℕ) := by rw [h]
    simp [antipode] at this
  have hrho : (tailRead k).ρ (antipode k) = tailWeight k := by
    show (if antipode k = (0 : Fin (2 * k + 1 + 1)) then (1 : ℝ) else 0)
        + (if antipode k = antipode k then tailWeight k else 0) = _
    rw [if_neg hne, if_pos rfl]
    ring
  have hSle : ∑ d, (tailRead k).ρ d ≤ 2 := by
    rw [hS]; linarith [tailWeight_le_one k]
  have hSpos : (0 : ℝ) < ∑ d, (tailRead k).ρ d := (tailRead k).hpos
  show tailWeight k / 2 ≤ (tailRead k).ρ (antipode k) / (∑ d, (tailRead k).ρ d)
  rw [hrho, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hSpos]
  nlinarith [(tailWeight_pos k).le]

/-- A conjunction: the `tailRead` family has circular second moment at most `1` at every `k`, and
there is no pair `(C, r)` with `0 ≤ r < 1` such that `(tailRead k).p d ≤ C * r ^ circLag d` holds at
every `k` and every `d`. The second part evaluates the candidate bound at the antipode, where
`tailRead_p_antipode` forces `1 / 2 ≤ C * ((k + 1) ^ 3 * r ^ (k + 1))`, and
`summable_pow_mul_geometric_of_norm_lt_one` sends the right-hand side to `0`.

Scope: the family satisfies `confinement_of_substrate_bound`'s hypothesis at `B = 1` while failing
`confinement_of_geometric_decay`'s, so the two hypotheses are not interchangeable. This is a
statement about these reads, not about `readYMAt`.

DERIVED: `2` is the moment's order; `1` is the moment bound asserted and the strict upper bound on
the geometric ratio `r`, which is what makes a geometric sequence decay; `0` is the lower bound on
`r`. The exponent `3` and the factor `1 / 2` are `tailWeight`'s and `tailRead_p_antipode`'s, and
appear in the proof. -/
theorem bounded_moment_does_not_give_geometric_decay :
    (∀ k : ℕ, ∑ d, (tailRead k).p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 ≤ 1) ∧
      ¬ ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧
          ∀ (k : ℕ) (d : Fin (2 * k + 1 + 1)),
            (tailRead k).p d ≤ C * r ^ (Moment.circLag d) := by
  refine ⟨tailRead_moment_le_one, ?_⟩
  rintro ⟨C, r, hr0, hr1, hbound⟩
  -- at the antipode the bound reads `(k+1)^{-3}/2 ≤ C·r^{k+1}`
  have hkey : ∀ k : ℕ, (1 : ℝ) / 2 ≤ C * (((k : ℝ) + 1) ^ 3 * r ^ (k + 1)) := by
    intro k
    have h := hbound k (antipode k)
    rw [circLag_antipode k] at h
    have hlow := tailRead_p_antipode k
    have hcube : (0 : ℝ) < ((k : ℝ) + 1) ^ 3 := by positivity
    have hw : tailWeight k * ((k : ℝ) + 1) ^ 3 = 1 := by
      unfold tailWeight
      field_simp
    nlinarith [hlow, h, hcube, pow_nonneg hr0 (k + 1)]
  -- but `n³rⁿ → 0`, so the left side is eventually beaten
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hnorm
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n) Filter.atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have htendC : Filter.Tendsto (fun n : ℕ => C * ((n : ℝ) ^ 3 * r ^ n)) Filter.atTop (nhds 0) := by
    simpa using htend.const_mul C
  have hev : ∀ᶠ n : ℕ in Filter.atTop, C * ((n : ℝ) ^ 3 * r ^ n) < 1 / 2 :=
    htendC.eventually_lt_const (by norm_num)
  obtain ⟨n, hn, hn1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hn
  linarith [hkey k, hn]

#print axioms bounded_moment_does_not_give_geometric_decay

end MassGap.Substrate
