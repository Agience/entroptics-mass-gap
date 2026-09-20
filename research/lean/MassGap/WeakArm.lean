import Mathlib
import MassGap.MomentShape

/-!
# MassGap.WeakArm — the contact bound at every lag, and what log-convexity cannot reach

Two things, one positive and one negative, both about the region of the coupling line that
`ContactFloor.contact_relative_unconditional` leaves open.

## Part 1 — the contact bound, at EVERY lag

    ρ(d) ≤ ρ(0)     for every lag `d`, at even extent `n = 2m` with `m ≥ 3`

`corrClay_le_at_zero`, which takes nonnegativity of `ρ` as its one hypothesis and is then good at
every REAL coupling. Even lags come from `MomentShape.corrClay_even_antitone` at `c₁ = 0`; the two
halves of the circle are exchanged by `MomentShape.corrClay_neg`, which is what lets `c` run all the
way to `m` rather than stopping at `m/2`; odd lags come from `MomentShape.corrClay_odd_le` squeezed
between two even lags that are already under `ρ(0)`.

`wilsonCorrAt_le_at_zero` discharges the nonnegativity from
`Complete.wilson_reflection_positive_at_even`, which is a THEOREM and not the named axiom — and which
requires `0 ≤ β`. So the two forms differ in scope and the difference matters: the CONDITIONAL form
`corrClay_le_at_zero` holds at every real coupling, the DISCHARGED form `wilsonCorrAt_le_at_zero`
holds on `0 ≤ β`. `[b, ∞)` is inside the latter.

The bound is scale-free — it survives `ρ ↦ t·ρ` — and it puts no floor under `ρ(0)`, so unlike
`ContactFloor.contactFloor_holds` nothing in it degrades as the coupling grows.

It is also OPTIMAL within the log-convex premise set: `no_strict_lag_bound_from_shape` proves no
factor below one is derivable there, at any lag or any extent, so the `1` in `ρ(d) ≤ ρ(0)` cannot be
improved by an argument running on nonnegativity, circle symmetry and log-convexity.

## Part 2 — log-convexity does not reach the contact-relative quartic law

`ShareEnvelope.substrate_of_contact_relative_decay` wants `ρ(d) ≤ C·ρ(0)/circLag(d)⁴` with ONE `C`
good at every aperture and every coupling. Three statements, all proved:

* `no_contact_relative_from_shape` — the CONSTANT profile satisfies `MomentShape.Shape` and also the
  two further facts the tree proves of the Wilson correlation with NO PREMISE DEPENDING ON THE
  COUPLING, `0 < ρ(0)` (`PlaqVariance.corrClay_zero_pos`, which is genuinely β-free) and `0 < ∑ ρ`
  (available at every `β ≥ 0`). It is scale-free and carries no floor, and at circle distance `k` it
  violates `ρ(d) ≤ C·ρ(0)/k⁴` as soon as `k⁴ > C`. So for every `C` and every cut `m₀` a conforming
  profile and a lag past the cut exist where the law fails.

* `no_strict_lag_bound_from_shape` — the same witness, against a constant factor: no `t < 1` gives
  `ρ(d) ≤ t·ρ(0)` at any lag or extent.

* `no_uniform_quartic_constant_of_vanishing_rate` — the obstruction one level up, where a decay RATE
  would live. Given any family of strictly positive rates whose infimum is zero, no single `C` makes
  `e^{−M·k} ≤ C/k⁴` hold across the family, at any cut. This is the exact complement of
  `StrongArm.exists_geom_quartic_bound`, which produces, for each rate `r < 1` SEPARATELY, one `S`
  with `L⁴·r^{L−1} ≤ S` at every `L ≥ 1`: a constant per rate, and no constant for all rates.

`corrClay_at_period` records the index fact that makes the first two unsurprising: on the even
sublattice parameter `c ∈ [0, m]` the profile `g(c) = ρ(2c)` has `g(m) = g(0)`, because `2m` is one
full period. A convex function with equal endpoints is under that horizontal chord, which is exactly
`ρ(d) ≤ ρ(0)` — Part 1 — and the chords that would carry a RATE all have an interior endpoint whose
value log-convexity does not supply.

## What this does and does not say

None of it says the quartic law is FALSE of the Wilson correlation; the tree PROVES it on `[0, b]`
(`ContactFloor.contact_relative_unconditional`). What is proved here is that the coupling-free,
scale-free premise set does not decide it, and what the missing quantity is: a decay rate bounded
away from one uniformly in the coupling AND the aperture.

Two caveats on scope, stated because they are easy to lose. First, `MomentShape.Shape` is a
COUPLING-FREE premise set — no premise in it mentions `β` or carries a `β`-dependent constant — and
not a coupling-UNCONDITIONAL one: `MomentShape.shape_wilsonCorrAt` requires `0 ≤ β`, because its
`nonneg` field is `Complete.wilson_reflection_positive_at_even`. Only `MomentShape.corrClay_neg` and
`LogConvex.corrClay_log_convex` hold at every real `β`. Nor is `Shape` everything the tree proves —
in particular the quartic law itself is available on `[0, b]`. Second, the geometric
envelope named in `no_uniform_quartic_constant_of_vanishing_rate` is a hypothesis about an abstract
family of rates: NO theorem in this tree derives `ρ(d)/ρ(0) ≤ e^{−M·d}` from
`LogConvex.corrClay_log_convex`, and `MomentShape.odd_scaling_admissible` shows the odd lags are not
bounded below by that premise set at all, so such an envelope is not merely unproved there.
-/

namespace MassGap.WeakArm

open MassGap.WilsonBridge MassGap.MomentShape

/-! ## Part 1 — `ρ(d) ≤ ρ(0)` at every lag -/

section ContactBound

variable {Nap m : ℕ}

/-- The zero even lag is the zero lag. -/
theorem ev_zero (Nap : ℕ) : ev Nap 0 = 0 := by
  apply Fin.ext
  rw [ev_eq, finOf_val]
  simp

#print axioms ev_zero

/-- **The circle complement of an even lag.** `ev (m − c) = −(ev c)` for `c ≤ m`, because doubling
`m` is one full period. This is what carries a statement proved on the first quarter, `2c ≤ m`, to
the whole half `c ≤ m`. -/
theorem ev_compl (hm : Nap + 1 = 2 * m) {c : ℕ} (hc : c ≤ m) :
    ev Nap (m - c) = -(ev Nap c) := by
  have h0 : ev Nap (m - c) + ev Nap c = 0 := by
    rw [ev_eq, ev_eq, finOf_add]
    have harith : 2 * (m - c) + 2 * c = Nap + 1 := by omega
    rw [harith, finOf_period]
  calc ev Nap (m - c) = ev Nap (m - c) + ev Nap c - ev Nap c := by abel
    _ = 0 - ev Nap c := by rw [h0]
    _ = -(ev Nap c) := by abel

#print axioms ev_compl

/-- **Every even lag is under the contact value.** `ρ(2c) ≤ ρ(0)` for every `c ≤ m`, not only for
`2c ≤ m`: past the quarter the circle symmetry reflects `c` to `m − c`. -/
theorem corrClay_ev_le_zero (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m) (β : ℝ)
    (hρ : ∀ d : Fin (Nap + 1), 0 ≤ corrClay (Nap + 1) β d)
    (c : ℕ) (hc : c ≤ m) :
    corrClay (Nap + 1) β (ev Nap c) ≤ corrClay (Nap + 1) β 0 := by
  by_cases h2 : 2 * c ≤ m
  · have h := corrClay_even_antitone hm hm3 β hρ 0 c (Nat.zero_le c) h2
    rwa [ev_zero] at h
  · have hc' : 2 * (m - c) ≤ m := by omega
    have heq : corrClay (Nap + 1) β (ev Nap c)
        = corrClay (Nap + 1) β (ev Nap (m - c)) := by
      rw [ev_compl hm hc, corrClay_neg]
    rw [heq]
    have h := corrClay_even_antitone hm hm3 β hρ 0 (m - c) (Nat.zero_le _) hc'
    rwa [ev_zero] at h

#print axioms corrClay_ev_le_zero

/-- **Every lag in the closed first half is under the contact value.** The even case is
`corrClay_ev_le_zero`; the odd case is `MomentShape.corrClay_odd_le`, whose two even neighbours are
both already under `ρ(0)`, so `ρ(2c+1)² ≤ ρ(0)²` and nonnegativity takes the square root.

`m ≥ 3` is exactly the threshold and not slack: the odd branch needs `c + 1 < m` from `2c + 1 ≤ m`,
which holds iff `m ≥ 3`. -/
theorem corrClay_finOf_le_zero (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m) (β : ℝ)
    (hρ : ∀ d : Fin (Nap + 1), 0 ≤ corrClay (Nap + 1) β d)
    (w : ℕ) (hw : w ≤ m) :
    corrClay (Nap + 1) β (finOf Nap w) ≤ corrClay (Nap + 1) β 0 := by
  rcases Nat.even_or_odd w with ⟨c, hcw⟩ | ⟨c, hcw⟩
  · have hev : finOf Nap w = ev Nap c := by
      rw [ev_eq]; congr 1; omega
    rw [hev]
    exact corrClay_ev_le_zero hm hm3 β hρ c (by omega)
  · have hd : finOf Nap w = finOf Nap c + finOf Nap (c + 1) := by
      rw [finOf_add]; congr 1; omega
    have hcm : c + 1 < m := by omega
    have hodd := corrClay_odd_le hm (by omega) β c hcm
    have h1 : corrClay (Nap + 1) β (ev Nap c) ≤ corrClay (Nap + 1) β 0 :=
      corrClay_ev_le_zero hm hm3 β hρ c (by omega)
    have h2 : corrClay (Nap + 1) β (ev Nap (c + 1)) ≤ corrClay (Nap + 1) β 0 :=
      corrClay_ev_le_zero hm hm3 β hρ (c + 1) (by omega)
    rw [hd]
    have hz : 0 ≤ corrClay (Nap + 1) β 0 := hρ 0
    have hx : 0 ≤ corrClay (Nap + 1) β (finOf Nap c + finOf Nap (c + 1)) := hρ _
    have hsq : corrClay (Nap + 1) β (finOf Nap c + finOf Nap (c + 1)) ^ 2
        ≤ corrClay (Nap + 1) β 0 ^ 2 := by
      calc corrClay (Nap + 1) β (finOf Nap c + finOf Nap (c + 1)) ^ 2
          ≤ corrClay (Nap + 1) β (ev Nap c) * corrClay (Nap + 1) β (ev Nap (c + 1)) := hodd
        _ ≤ corrClay (Nap + 1) β 0 * corrClay (Nap + 1) β 0 :=
            mul_le_mul h1 h2 (hρ _) hz
        _ = corrClay (Nap + 1) β 0 ^ 2 := by ring
    nlinarith [hsq, hx, hz]

#print axioms corrClay_finOf_le_zero

/-- **THE CONTACT BOUND, AT EVERY LAG.**

    ρ(d) ≤ ρ(0)

at even extent `Nap + 1 = 2m` with `m ≥ 3`, at EVERY real coupling, given only nonnegativity.

Every `d : Fin (Nap + 1)` is covered: the split is `d ≤ m`, where `d` is its own representative, and
`d > m`, where `corrClay_neg` replaces it by `−d`, whose value `2m − d` is then below `m`. The lag
`0` and the lag `2m − 1` are both inside, on the two branches respectively.

Nothing is assumed about `ρ(0)` beyond nonnegativity — no floor, so nothing degrades with the
coupling — and the statement is invariant under `ρ ↦ t·ρ`, so unlike a mass floor it is not refuted
by rescaling (`ShareEnvelope.mass_floor_is_not_scale_free` is what makes that distinction matter).

DERIVED: `m` is half the extent, the reflection geometry's own bound carried in from
`LogConvex.corrClay_log_convex`; `m ≥ 3` is where `MomentShape.corrClay_even_antitone` stops being
vacuous and is also exactly what the odd branch needs. No constant is introduced. -/
theorem corrClay_le_at_zero (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m) (β : ℝ)
    (hρ : ∀ d : Fin (Nap + 1), 0 ≤ corrClay (Nap + 1) β d) (d : Fin (Nap + 1)) :
    corrClay (Nap + 1) β d ≤ corrClay (Nap + 1) β 0 := by
  have hlt := d.isLt
  by_cases hle : (d : ℕ) ≤ m
  · have hd : finOf Nap (d : ℕ) = d := by
      apply Fin.ext
      rw [finOf_val]
      exact Nat.mod_eq_of_lt hlt
    rw [← hd]
    exact corrClay_finOf_le_zero hm hm3 β hρ _ hle
  · have hv : ((-d : Fin (Nap + 1)) : ℕ) = (Nap + 1 - (d : ℕ)) % (Nap + 1) := by
      simp [Fin.neg_def]
    have hneg : finOf Nap (Nap + 1 - (d : ℕ)) = -d := by
      apply Fin.ext
      rw [finOf_val, hv]
    rw [← corrClay_neg (Nap + 1) β d, ← hneg]
    exact corrClay_finOf_le_zero hm hm3 β hρ _ (by omega)

#print axioms corrClay_le_at_zero

/-- **The contact bound on the correlation the substrate read consumes**, with nonnegativity
discharged by `Complete.wilson_reflection_positive_at_even` — a theorem, not the named axiom, which
is why the footprint carries no reflection-positivity axiom.

The price of discharging it is `0 ≤ β`. `corrClay_le_at_zero` above is the form that holds at every
real coupling; this one holds on the nonnegative half, which contains `[b, ∞)`. -/
theorem wilsonCorrAt_le_at_zero (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) (d : Fin (Nap + 1)) :
    MassGap.wilsonCorrAt Nap β d ≤ MassGap.wilsonCorrAt Nap β 0 :=
  corrClay_le_at_zero hm hm3 β
    (fun d => (MassGap.wilson_reflection_positive_at_even Nap m hm (by omega) hβ).1 d) d

#print axioms wilsonCorrAt_le_at_zero

/-- **NON-VACUITY.** At extent six, the smallest even extent meeting `m ≥ 3`, the bound is a genuine
statement at the ODD lag `1` — which no antitone result in the tree reaches, because every right-hand
lag `LogConvex.corrClay_log_convex` produces is even. The right-hand side is not zero:
`PlaqVariance.corrClay_zero_pos` puts `0 < ρ(0)` at every aperture and every real coupling. -/
theorem wilsonCorrAt_le_at_zero_at_extent_six {β : ℝ} (hβ : 0 ≤ β) :
    MassGap.wilsonCorrAt 5 β 1 ≤ MassGap.wilsonCorrAt 5 β 0 :=
  wilsonCorrAt_le_at_zero 5 3 (by norm_num) (by norm_num) hβ 1

#print axioms wilsonCorrAt_le_at_zero_at_extent_six

end ContactBound

/-! ## Part 2 — the no-gos -/

section NoGo

variable {Nap m : ℕ}

/-- The even lag `2m` is one full period, hence the zero lag. -/
theorem ev_period (hm : Nap + 1 = 2 * m) : ev Nap m = 0 := by
  rw [ev_eq, hm.symm, finOf_period]

#print axioms ev_period

/-- **THE EVEN-SUBLATTICE PROFILE HAS EQUAL ENDPOINTS.**

    ρ(2m) = ρ(0)

Index arithmetic — `2m` is one period. It is the `c = 0` instance of the symmetry
`MomentShape.shape_antitone` consumes, `g(c) = g(m − c)` on the even-sublattice parameter
`g(c) = ρ(2c)`; the INTERIOR instances of that symmetry are the ones `MomentShape.shape_step` uses
and they come from `MomentShape.corrClay_neg`, not from period arithmetic. Endpoint equality alone
yields nothing, so this records a boundary condition and not the argument.

What it settles for Part 2 is narrow and worth having anyway: the OUTERMOST chord of the convex
profile, from `c = 0` to `c = m`, is horizontal, so the one chord whose endpoints are both free
carries no rate. It does not say no wide chord carries a rate — the antipodal chord to `c = m/2`, at
circle distance `m`, is an ordinary interior endpoint and would carry one. It says that every chord
which does carry a rate has an interior endpoint: a value of `ρ` strictly inside the half. And
log-convexity is a relation among lags — it can propagate such a value and cannot produce one. The
two numbers the tree does produce both move the wrong way with the coupling:
`StrongArm.coreRate_exceeds` proves the strong-coupling rate is unbounded above in `β` (for every `M`
there is a `β ≥ 0` with `M < coreRate K β`), and `ContactFloor.contactFloor_holds` produces the floor
`e^{−128b}·δ₀`. -/
theorem corrClay_at_period (hm : Nap + 1 = 2 * m) (β : ℝ) :
    corrClay (Nap + 1) β (ev Nap m) = corrClay (Nap + 1) β 0 := by
  rw [ev_period hm]

#print axioms corrClay_at_period

/-- **NO CONTACT-RELATIVE QUARTIC LAW FROM THE COUPLING-FREE PREMISE SET.**

For EVERY constant `C` and EVERY cut `m₀` there is an even extent and a profile `ρ` with

* `MomentShape.Shape` — nonnegative, circle-symmetric, log-convex with constant one, which
  `MomentShape.shape_wilsonCorrAt` proves of the Wilson correlation at every `β ≥ 0`, with no premise
  mentioning `β` and no `β`-dependent constant in any of them;
* `0 < ρ(0)`, matching `PlaqVariance.corrClay_zero_pos`, which holds at every aperture and every real
  coupling and is NOT a field of `Shape`;
* `0 < ∑ ρ`, matching the second conjunct of `Complete.wilson_reflection_positive_at_even`, also not
  a field of `Shape`;

and a lag past the cut at which `ρ(d) ≤ C·ρ(0)/circLag(d)⁴` FAILS. The two extra conjuncts are there
so the no-go is against the premises that are actually available and not only against `Shape` as
written.

The witness is the CONSTANT profile, and the two properties that make it the right witness are
positive ones: it is invariant under `ρ ↦ t·ρ`, and it puts no positive lower bound under `ρ(0)`
relative to the lag values. So it is a profile the coupling-free premises admit at every scale.

WHAT THIS DOES AND DOES NOT SAY. It does not say the quartic law fails for the Wilson correlation —
the tree PROVES the law on `[0, b]` in `ContactFloor.contact_relative_unconditional`, and this is no
evidence against that. It says no proof of the law AT EVERY COUPLING can run on the premises that
survive at every coupling, because those are satisfied by a profile that does not decay at all.

DERIVED: `k` is read off from `C` and `m₀` by the ceiling, the extent `4k+4` is an even one with
`k+1` inside the half, and the value `1` is any positive constant. Nothing is fitted. -/
theorem no_contact_relative_from_shape (C : ℝ) (m₀ : ℕ) :
    ∃ (Nap m : ℕ) (ρ : Fin (Nap + 1) → ℝ) (d : Fin (Nap + 1)),
      Nap + 1 = 2 * m ∧ 3 ≤ m ∧ Shape (Nap + 1) m ρ ∧
      0 < ρ 0 ∧ 0 < ∑ e, ρ e ∧
      m₀ ≤ Moment.circLag d ∧ 1 ≤ Moment.circLag d ∧
      ¬ (ρ d ≤ C * ρ 0 / (Moment.circLag d : ℝ) ^ 4) := by
  classical
  set k : ℕ := max (max m₀ 1) (⌈C⌉₊ + 1) with hkdef
  have hk1 : 1 ≤ k := le_trans (le_max_right m₀ 1) (le_max_left _ _)
  have hkm : m₀ ≤ k := le_trans (le_max_left m₀ 1) (le_max_left _ _)
  have hkceil : ⌈C⌉₊ + 1 ≤ k := le_max_right _ _
  have hkC : C < (k : ℝ) := by
    have h1 : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkceil
    push_cast at h1
    linarith [Nat.le_ceil C]
  have hlt : k + 1 < 4 * k + 3 + 1 := by omega
  have hcirc : Moment.circLag (⟨k + 1, hlt⟩ : Fin (4 * k + 3 + 1)) = k + 1 := by
    show min (k + 1) (4 * k + 3 + 1 - (k + 1)) = k + 1
    omega
  refine ⟨4 * k + 3, 2 * k + 2, fun _ => (1 : ℝ), ⟨k + 1, hlt⟩, by omega, by omega,
    ⟨fun _ => zero_le_one, fun _ => rfl, fun _ _ _ _ => by norm_num⟩,
    zero_lt_one, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_pos (fun _ _ => zero_lt_one) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  · rw [hcirc]; omega
  · rw [hcirc]; omega
  · rw [hcirc]
    intro hcon
    have hx : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hP : (0 : ℝ) < ((k : ℝ) + 1) ^ 4 := by positivity
    have hPne : ((k : ℝ) + 1) ^ 4 ≠ 0 := ne_of_gt hP
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hcon
    have hkey : ((k : ℝ) + 1) ^ 4 ≤ C * 1 := by
      calc ((k : ℝ) + 1) ^ 4 = 1 * ((k : ℝ) + 1) ^ 4 := by ring
        _ ≤ (C * 1 / ((k : ℝ) + 1) ^ 4) * ((k : ℝ) + 1) ^ 4 :=
            mul_le_mul_of_nonneg_right hcon hP.le
        _ = C * 1 := by field_simp
    have h4 : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 4 := by
      nlinarith [hx, mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx,
        mul_nonneg (mul_nonneg (mul_nonneg hx hx) hx) hx]
    linarith

#print axioms no_contact_relative_from_shape

/-- **PART 1 IS OPTIMAL: NO FACTOR BELOW ONE IS DERIVABLE, AT ANY LAG, AT ANY EXTENT.**

For every `t < 1`, every even extent with `m ≥ 3` and EVERY lag `d` — including `d` at the far side
of the circle — there is a profile satisfying `MomentShape.Shape` with `ρ(d) > t·ρ(0)`. The witness is
again the constant profile.

So `corrClay_le_at_zero` is not merely the best bound currently extracted from that premise set; the
constant `1` in it cannot be improved by any argument running on nonnegativity, circle symmetry and
log-convexity. `no_contact_relative_from_shape` is the same fact against the lag-dependent factor
`C/circLag(d)⁴`.

The witness carries `0 < ρ(0)` and `0 < ∑ ρ` here too, for the same reason it does in
`no_contact_relative_from_shape`: so the no-go is against the premises that are actually available
and not only against `Shape` as written.

The extent hypotheses are carried so the statement reads against Part 1's setting and are NOT
consumed — underscored because the witness needs neither, which makes the no-go strictly wider than
the theorem it is optimal against. -/
theorem no_strict_lag_bound_from_shape (Nap m : ℕ) (_hm : Nap + 1 = 2 * m) (_hm3 : 3 ≤ m)
    (t : ℝ) (ht : t < 1) (d : Fin (Nap + 1)) :
    ∃ ρ : Fin (Nap + 1) → ℝ, Shape (Nap + 1) m ρ ∧ 0 < ρ 0 ∧ 0 < ∑ e, ρ e ∧
      ¬ (ρ d ≤ t * ρ 0) := by
  refine ⟨fun _ => (1 : ℝ),
    ⟨fun _ => zero_le_one, fun _ => rfl, fun _ _ _ _ => by norm_num⟩, zero_lt_one,
    Finset.sum_pos (fun _ _ => zero_lt_one) ⟨0, Finset.mem_univ _⟩, ?_⟩
  intro h
  rw [mul_one] at h
  linarith

#print axioms no_strict_lag_bound_from_shape

/-! ### The rate, and why a constant per rate is not a constant for all rates -/

/-- **A lag past any cut where the quartic weight is under a half.** Pure arithmetic: `k⁴` grows, so
`C/k⁴` eventually clears any fixed positive level, and `1/2` is the level the exponential below is
pinned to exactly. `k` is read off from `C` and the cut by the ceiling. -/
theorem exists_lag_halving (C : ℝ) (m₀ : ℕ) :
    ∃ k : ℕ, m₀ ≤ k ∧ 1 ≤ k ∧ C / (k : ℝ) ^ 4 < 1 / 2 := by
  classical
  set k : ℕ := max (max m₀ 1) (⌈2 * C⌉₊ + 1) with hkdef
  have hk1 : 1 ≤ k := le_trans (le_max_right m₀ 1) (le_max_left _ _)
  have hkm : m₀ ≤ k := le_trans (le_max_left m₀ 1) (le_max_left _ _)
  have hkceil : ⌈2 * C⌉₊ + 1 ≤ k := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have h2C : 2 * C < (k : ℝ) := by
    have h1 : ((⌈2 * C⌉₊ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkceil
    push_cast at h1
    linarith [Nat.le_ceil (2 * C)]
  have h4 : (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    nlinarith [hx1, sq_nonneg ((k : ℝ) - 1), sq_nonneg ((k : ℝ) + 1),
      sq_nonneg ((k : ℝ) ^ 2 - 1), sq_nonneg ((k : ℝ) ^ 2 - (k : ℝ))]
  have hk4 : (0 : ℝ) < (k : ℝ) ^ 4 := by positivity
  have hk4ne : ((k : ℝ) ^ 4) ≠ 0 := ne_of_gt hk4
  refine ⟨k, hkm, hk1, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hmul := mul_le_mul_of_nonneg_right hcon hk4.le
  have hcalc : C / (k : ℝ) ^ 4 * (k : ℝ) ^ 4 = C := by field_simp
  rw [hcalc] at hmul
  linarith

#print axioms exists_lag_halving

/-- **NO SINGLE QUARTIC CONSTANT SERVES A FAMILY OF RATES WHOSE INFIMUM IS ZERO.**

Given rates `M i > 0` with `∀ ε > 0, ∃ i, M i < ε`, then for every `C` and every cut `m₀` there are
an index `i` and a lag `k` past the cut with

    C / k⁴  <  e^{−M i · k}

so no `C` makes the geometric envelope `e^{−M·d}` dominate `C/d⁴` across the family.

THIS IS THE EXACT COMPLEMENT OF `StrongArm.exists_geom_quartic_bound`, which produces, for each rate
`r < 1` SEPARATELY, one `S` with `L⁴·r^{L−1} ≤ S` at every `L ≥ 1`. That `S` is a function of `r`.
Together the two say: a constant per rate, and no constant for all rates. So a route to the law at
every coupling through a geometric envelope needs its rate bounded away from ZERO uniformly in the
coupling and the aperture — equivalently, in the `r = e^{−M}` parametrisation
`StrongArm.exists_geom_quartic_bound` uses, bounded away from ONE. A rate that is positive at each
coupling separately is not enough, and that is the quantity `[b, ∞)` still lacks.

WHAT IS HYPOTHESIS AND WHAT IS PROVED. The rate family is a HYPOTHESIS about an abstract `M : ι → ℝ`.
No theorem in this tree derives a geometric envelope `ρ(d)/ρ(0) ≤ e^{−M·d}` from
`LogConvex.corrClay_log_convex` — the log-convexity proved there is the three-point form
`ρ(e₁+e₂)² ≤ ρ(2e₁)·ρ(2e₂)` and nothing in the tree turns it into an envelope. Nor does this theorem
assert anything about how the Wilson rate behaves as `β` grows; it says only what a vanishing
infimum costs, whatever supplies one.

The rate exhibited against `k` is `M i < (log 2)/k`, which puts `e^{−M i·k}` above `1/2` exactly. -/
theorem no_uniform_quartic_constant_of_vanishing_rate {ι : Type*}
    (M : ι → ℝ) (hpos : ∀ i, 0 < M i) (hinf : ∀ ε : ℝ, 0 < ε → ∃ i, M i < ε)
    (C : ℝ) (m₀ : ℕ) :
    ∃ (i : ι) (k : ℕ), 0 < M i ∧ m₀ ≤ k ∧ 1 ≤ k ∧
      C / (k : ℝ) ^ 4 < Real.exp (-(M i * (k : ℝ))) := by
  obtain ⟨k, hkm, hk1, hhalf⟩ := exists_lag_halving C m₀
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkne : ((k : ℝ)) ≠ 0 := ne_of_gt hkR
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨i, hi⟩ := hinf (Real.log 2 / (k : ℝ)) (div_pos hlogpos hkR)
  refine ⟨i, k, hpos i, hkm, hk1, ?_⟩
  have heq : Real.log 2 / (k : ℝ) * (k : ℝ) = Real.log 2 := by field_simp
  have hMk : M i * (k : ℝ) < Real.log 2 := by
    have hltm := mul_lt_mul_of_pos_right hi hkR
    rw [heq] at hltm
    exact hltm
  have hhalfexp : (1 / 2 : ℝ) < Real.exp (-(M i * (k : ℝ))) := by
    have h2 : Real.exp (-(Real.log 2)) < Real.exp (-(M i * (k : ℝ))) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), ← one_div] at h2
  linarith

#print axioms no_uniform_quartic_constant_of_vanishing_rate

/-- A rate family that is strictly positive at every index, indexed so the infimum is zero.

DERIVED: nothing here is a magnitude. This exists only to witness the hypothesis of
`no_uniform_quartic_constant_of_vanishing_rate` — a family of strictly positive rates whose infimum
is zero — so the no-go is not vacuous. The `+ 1` is the shift that makes the reciprocal defined at
`n = 0` and the numerator `1` is what makes the family positive; any strictly positive null sequence
serves identically, and the theorem is stated over an arbitrary one. -/
noncomputable def invSucc (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem invSucc_pos (n : ℕ) : 0 < invSucc n := by
  unfold invSucc
  positivity

#print axioms invSucc_pos

/-- `invSucc` gets below every positive level, so its infimum is zero. -/
theorem invSucc_lt (ε : ℝ) (hε : 0 < ε) : ∃ i : ℕ, invSucc i < ε := by
  obtain ⟨i, hi⟩ := exists_nat_gt (1 / ε)
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) / ε * ε = 1 := by field_simp
  have hlt : (1 : ℝ) < ε * ((i : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_right hi hε
    rw [hone] at h
    nlinarith [h, hε]
  refine ⟨i, ?_⟩
  unfold invSucc
  by_contra hcon
  rw [not_lt] at hcon
  have hmul := mul_le_mul_of_nonneg_right hcon hi1.le
  have hcancel : (1 : ℝ) / ((i : ℝ) + 1) * ((i : ℝ) + 1) = 1 := by field_simp
  rw [hcancel] at hmul
  linarith

#print axioms invSucc_lt

/-- **NON-VACUITY OF THE RATE NO-GO.** The hypothesis pair of
`no_uniform_quartic_constant_of_vanishing_rate` is satisfiable, and the conclusion fires: `invSucc`
is strictly positive at every index and has infimum zero, so for every constant and every cut there
is an index and a lag past the cut where the quartic bound loses to the geometric one.

Stated so the no-go is not a statement about an empty hypothesis. It exhibits ONE family and claims
nothing about which family the Wilson correlation would supply — see the parent theorem's docstring
for what is hypothesis here and what is proved. -/
theorem no_uniform_quartic_constant_nonvacuous (C : ℝ) (m₀ : ℕ) :
    ∃ (i : ℕ) (k : ℕ), 0 < invSucc i ∧ m₀ ≤ k ∧ 1 ≤ k ∧
      C / (k : ℝ) ^ 4 < Real.exp (-(invSucc i * (k : ℝ))) :=
  no_uniform_quartic_constant_of_vanishing_rate invSucc invSucc_pos
    (fun ε hε => invSucc_lt ε hε) C m₀

#print axioms no_uniform_quartic_constant_nonvacuous

end NoGo

end MassGap.WeakArm
