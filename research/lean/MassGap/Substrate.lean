import Mathlib
import MassGap.Complete
import MassGap.ZeroMode
import MassGap.Spectral

/-!
# The substrate hypothesis: what bounds it, and what cannot

`MassGap.ym_mass_gap_of_substrate` reduces the Clay statement to one hypothesis,

    h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B

where `d2At N β = ∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ)^2` is the second moment of the
read's own probability vector about the CIRCLE distance. This file establishes what is true about
that hypothesis unconditionally, and closes the routes that cannot reach it.

## What is unconditionally true

`d2At N β ≤ ((N:ℝ)+1)^2/4` at every aperture and every coupling (`d2At_le_quarter_sq`), equivalently
`substrateRatio N β ≤ 1/4` (`substrateRatio_le_quarter`). This needs nothing beyond
`Moment.Read.p_sum` and `circLag d ≤ (N+1)/2`: a probability distribution on a circle of `N+1` sites
cannot have a second moment larger than the squared half-period.

## What this file does NOT claim

It does not refute `∃ B, ∀ N β, d2At N β ≤ B`. That statement is about the CONSTRUCTED correlation
`wilsonCorrAt`, and no family of other reads can refute it. What the reads below establish is the
weaker and different claim that the hypothesis is not DERIVABLE from what the tree assumes about
that correlation.

## Why the tree's assumptions cannot reach it

The aperture argument (`Moment.Read.tension_lt_floor_of_circ_moment`) needs the substrate ratio below
`(1 - 3^{-1/4})/(2π²) = 0.0121…`; its converse (`Moment.Read.substrate_lt_of_tension_lt_floor`) says
a tension below the floor forces it below `(1 - 3^{-1/4})/8 = 0.0300…`. The unconditional bound is
`1/4`, which is `8.3×` above even the necessary ceiling.

That gap cannot be closed by any argument reading only what `wilson_reflection_positive_at` asserts.
The axiom asserts exactly `0 ≤ ρ d` and `0 < ∑ ρ d`; `antipodeRead` is a `Moment.Read` meeting both
whose circular second moment is EXACTLY `((N:ℝ)+1)^2/4` (`antipodeRead_moment_eq_quarter_sq`), so
`1/4` is attained and is the best constant the axiom supports. Letting the aperture grow, the moment
is unbounded (`rp_alone_leaves_moment_unbounded`).

Nor can it be closed by the fuller content reflection positivity is cited for — the periodic transfer
form `ρ(d) = ∑ₖ wₖ(λₖ^d + λₖ^{n−d})` with `wₖ ≥ 0` and `λₖ ∈ [0,1]`
(`Spectral.PeriodicSpectralForm`). At `λ = 1` that form is the FLAT correlation, whose substrate
ratio is `1/12 + 1/(6n²)` (`flatRead_moment`), above the ceiling `(1 - 3^{-1/4})/8` at every aperture
(`flatRead_exceeds_ceiling`) and unbounded as a moment
(`spectral_form_alone_leaves_moment_unbounded`). `λ ≤ 1` is contractivity, not a gap, so the spectral
form on its own leaves the flat read in.

`substrate_bound_needs_more_than_positivity` states the closure: the moment bound is not a
consequence of the read interface, so any proof of `h` must evaluate `wilsonCorrAt` — a property of
the Wilson Gibbs measure that no theorem in this tree supplies.

## The hypothesis is strictly weaker than a uniform decay rate

`confinement_of_geometric_decay` consumes `p d ≤ C·r^{circLag d}` with ONE `r < 1` for all `N`, `β`.
`tailRead` is a family of reads whose circular second moment is at most `1` at every aperture and
which admits no such `(C, r)` (`bounded_moment_does_not_give_geometric_decay`): a far tail of
polynomially small weight costs the moment nothing and breaks every geometric bound. So the substrate
hypothesis is genuinely the weaker of the two, and a route that discharges it need not produce a
rate.
-/

namespace MassGap.Substrate

open MassGap.Moment

/-! ### The unconditional aperture bound -/

/-- The circle lag never exceeds half the period — the arithmetic of `min d (N+1−d)`. -/
theorem two_mul_circLag_le {N : ℕ} (d : Fin (N + 1)) : 2 * Moment.circLag d ≤ N + 1 := by
  have h := d.isLt
  unfold Moment.circLag
  omega

/-- The same, as a real inequality. -/
theorem circLag_le_half {N : ℕ} (d : Fin (N + 1)) :
    ((Moment.circLag d : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
  have h : 2 * Moment.circLag d ≤ N + 1 := two_mul_circLag_le d
  have hR : (2 : ℝ) * ((Moment.circLag d : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  linarith

/-- **Every read's circular second moment is at most the squared half-period.**

No hypothesis beyond the read interface: `p` is a probability vector (`Moment.Read.p_sum`) and the
circle lag is at most `(N+1)/2`, so the moment is at most `((N+1)/2)²`. This is the whole of what
reflection positivity, as axiomatised, can say about the substrate.

DERIVED: the `4` is `2²`, the square of the two halves of the period. Nothing is chosen. -/
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

/-- **The substrate moment of the Wilson read, bounded unconditionally.** At every aperture and every
coupling — no hypothesis, no measurement. The bound carries the aperture, which is exactly why it
does not discharge `ym_mass_gap_of_substrate`. -/
theorem d2At_le_quarter_sq (N : ℕ) (β : ℝ) : MassGap.d2At N β ≤ ((N : ℝ) + 1) ^ 2 / 4 := by
  unfold MassGap.d2At
  exact circ_moment_le_quarter_sq (MassGap.readYMAt N β)

#print axioms d2At_le_quarter_sq

/-- The same with the aperture divided out: the substrate ratio never exceeds `1/4`. -/
theorem substrateRatio_le_quarter (N : ℕ) (β : ℝ) : MassGap.substrateRatio N β ≤ 1 / 4 := by
  rw [MassGap.substrateRatio_le_iff]
  have := d2At_le_quarter_sq N β
  linarith

#print axioms substrateRatio_le_quarter

/-- **The trivial bound cannot be fed to the flagship.** `ym_mass_gap_of_ratio` consumes
`substrateRatio ≤ c` provided `c` clears `(2π)²c/2 < 1 − 3^{-1/4}`. At `c = 1/4` — the best constant
the read interface supports (`substrateRatio_le_quarter`, `antipodeRead_moment_eq_quarter_sq`) — that
condition FAILS: the left side is `π²/2 > 4.9` and the right side is below `1`. So the unconditional
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

/-- **And it cannot be fed to `confinement_of_substrate_bound` either**, because it is not a bound:
`((N:ℝ)+1)²/4` grows without limit in the aperture, and the hypothesis there is ONE `B` good at every
aperture. Stated so that `d2At_le_quarter_sq` cannot be mistaken for progress toward the flagship. -/
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

DERIVED: `2 * k + 1` is the aperture whose period `2k+2` is EVEN, which is the only case in which an
antipode exists as a lag at all; `k + 1` is then half that period, and it is what `min d (n−d)`
returns there. Neither is a magnitude — both are forced by the requirement that the point be the
antipode. -/
def antipode (k : ℕ) : Fin (2 * k + 1 + 1) := ⟨k + 1, by omega⟩

/-- The circle lag of the antipode is half the period. -/
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

/-- **The quarter bound is attained.** The antipodal read's circular second moment is exactly
`((N:ℝ)+1)²/4` at `N = 2k+1`, so no constant smaller than `1/4` follows from the read interface. -/
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

/-- **Reflection positivity alone leaves the substrate moment unbounded.**

For every `B` there is an aperture and a read meeting exactly the axiom's two clauses whose circular
second moment exceeds `B`. So `∃ B, ∀ N β, d2At N β ≤ B` is not a consequence of
`wilson_reflection_positive_at`: any proof of it must look at what `wilsonCorrAt` actually is. -/
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

/-- **The flat read's circular second moment is `(n² + 2)/12` at period `n = 2(k+1)`** — through
`ZeroMode.sum_clag_sq`, which computes `12·∑ clag² = n³ + 2n` exactly. -/
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

/-- `3^{-1/4} > 1/3`, because `3 > 1` and `-1/4 > -1`. -/
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

/-- **The ceiling a tension below the floor forces is below `1/12`.**

`Moment.Read.substrate_lt_of_tension_lt_floor` caps the substrate ratio at `(1 − 3^{-1/4})/8`. That
number is smaller than `1/12`, which is what the flat read's ratio approaches from above — so a flat
correlation is excluded, and so is every constant bound the read interface can prove. -/
theorem ceiling_lt_twelfth : (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 < 1 / 12 := by
  have h := one_third_lt_rpow
  linarith

#print axioms ceiling_lt_twelfth

/-- **The flat read is above the ceiling at every aperture.** Its substrate ratio is
`1/12 + 1/(6n²) > 1/12 > (1 − 3^{-1/4})/8`, so the correlation the periodic spectral form permits at
`λ = 1` is exactly one the entropy floor refuses — and the spectral form does not refuse it. -/
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

/-- **The periodic spectral form alone leaves the substrate moment unbounded too.**

For every `B` there is an aperture, a correlation of the exact shape `Spectral.PeriodicSpectralForm`
carries, and a read built from it, whose circular second moment exceeds `B`. So the fuller content
reflection positivity is cited for — nonnegative transfer weights and `λ ∈ [0,1]` — is also not
enough. What is missing is `λ` bounded away from `1`, which is the gap itself. -/
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

/-- **THE CLOSURE.** The substrate hypothesis is not a consequence of the read interface.

Stated as the two facts that together close the route: the unconditional bound the interface gives is
`1/4` and it is ATTAINED, and letting the aperture grow the moment exceeds any `B`. Both witnessing
reads satisfy exactly the two clauses `wilson_reflection_positive_at` asserts, and the flat one
additionally carries the periodic transfer form. So `∃ B, ∀ N β, d2At N β ≤ B` cannot be derived from
that axiom, however it is combined with the rest of this development: a proof must evaluate the
Wilson Gibbs measure at some lag, which no theorem in this tree does.

This is a statement about DERIVABILITY, not about truth. It leaves `∃ B, ∀ N β, d2At N β ≤ B` open. -/
theorem substrate_bound_needs_more_than_positivity :
    (∀ (N : ℕ) (R : Moment.Read N),
        ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 / 4) ∧
      (∀ B : ℝ, ∃ (N : ℕ) (R : Moment.Read N),
        B < ∑ d, R.p d * ((Moment.circLag d : ℕ) : ℝ) ^ 2) :=
  ⟨fun _N R => circ_moment_le_quarter_sq R, rp_alone_leaves_moment_unbounded⟩

#print axioms substrate_bound_needs_more_than_positivity

/-! ### The substrate bound is strictly weaker than a uniform decay rate

`confinement_of_geometric_decay` reaches the same conclusion from `p d ≤ C·r^{circLag d}` with ONE
`r < 1`. That is a STRICTLY stronger demand: the reads below have a circular second moment at most
`1` at every aperture and satisfy no geometric bound at all. A far tail whose weight falls off
polynomially in the aperture contributes nothing to the moment and defeats every `r < 1`.

Whoever plans to discharge the substrate hypothesis should therefore not route through a decay rate:
doing so asks for more than the flagship needs. -/

/-- The far-tail weight: the reciprocal cube of the half-period.

DERIVED: the exponent `3` is the smallest integer for which the far atom's contribution to the
SECOND moment, which carries a factor `(k+1)²`, still tends to zero — so it is fixed by the moment it
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
divides by the total, so only the RATIO of the two matters and the `1` fixes the scale of nothing.
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

/-- The circle lag at the origin is zero, so the contact term contributes nothing to the moment. -/
theorem circLag_zero (k : ℕ) : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by
  have hv : ((0 : Fin (2 * k + 1 + 1)) : ℕ) = 0 := rfl
  unfold Moment.circLag
  rw [hv]
  omega

/-- **The tail read's circular second moment is at most `1`, at every aperture.** The far atom
carries weight `(k+1)^{-3}` at squared distance `(k+1)²`, so it contributes `1/(k+1)` and the contact
term contributes nothing. -/
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

/-- The tail read's weight at the antipode is at least half the tail weight. -/
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

/-- **A BOUNDED SUBSTRATE MOMENT DOES NOT GIVE A DECAY RATE.**

The `tailRead` family has circular second moment at most `1` at every aperture — so it satisfies the
hypothesis of `confinement_of_substrate_bound` with `B = 1` — and there is no `(C, r)` with `r < 1`
for which `p d ≤ C·r^{circLag d}` holds across the family. The far atom's weight falls off like
`(k+1)^{-3}`, which no geometric sequence stays above.

So `confinement_of_geometric_decay` asks for strictly more than `confinement_of_substrate_bound`, and
the two open residuals are NOT the same residual. Discharging the substrate hypothesis does not
require producing a rate, and a route that produces one is solving a harder problem. -/
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
