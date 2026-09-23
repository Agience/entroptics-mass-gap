import Mathlib
import MassGap.MomentShape

/-!
# MassGap.WeakArm — the contact bound at every lag, and three limits of the shape premises

## Part 1 — `ρ(d) ≤ ρ(0)` at every lag

`corrClay_le_at_zero` is the bound at even extent `Nap + 1 = 2 * m` with `3 ≤ m`, at every real
coupling, taking nonnegativity of `ρ` as its one hypothesis. The even lags come from
`MomentShape.corrClay_even_antitone` at the left endpoint; `MomentShape.corrClay_neg` exchanges the
two halves of the circle, which is what lets the parameter run to `m` rather than stopping at half
that; the odd lags come from `MomentShape.corrClay_odd_le` squeezed between two even lags already
under `ρ(0)`.

`wilsonCorrAt_le_at_zero` is the same bound with nonnegativity discharged by
`Complete.wilson_reflection_positive_at_even`, which requires `0 ≤ β`. So the two forms differ in
scope: the conditional one holds at every real coupling, the discharged one on the nonnegative half.
`wilsonCorrAt_le_at_zero_at_extent_six` instantiates it at the smallest admissible extent and an odd
lag.

The bound is invariant under `ρ ↦ t·ρ` and puts no lower bound under `ρ(0)`, so no constant in it
depends on the coupling — unlike `ContactFloor.contactFloor_holds`, whose floor `e^{-128b}·δ₀`
decreases with the interval.

## Part 2 — three no-gos against the shape premises

`ShareEnvelope.substrate_of_contact_relative_decay` consumes `ρ(d) ≤ C·ρ(0)/circLag(d)⁴` with one `C`
good at every aperture and every coupling.

* `no_contact_relative_from_shape` — for every `C` and every cut there is an even extent, a profile
  satisfying `MomentShape.Shape` together with `0 < ρ 0` and `0 < ∑ ρ`, and a lag past the cut where
  that inequality fails. The witness is the constant profile.
* `no_strict_lag_bound_from_shape` — the same witness against a constant factor: for every `t < 1`,
  at every even extent and every lag, a conforming profile has `ρ(d) > t·ρ(0)`. So the `1` in Part 1
  is not improvable on these premises.
* `no_uniform_quartic_constant_of_vanishing_rate` — for any family of strictly positive rates whose
  infimum is zero, no single `C` makes `C/k⁴ ≤ e^{-M·k}` hold across the family at any cut.
  `exists_lag_halving` is its arithmetic core, and `invSucc` with
  `no_uniform_quartic_constant_nonvacuous` exhibits a family satisfying the hypotheses.

`StrongArm.exists_geom_quartic_bound` produces, for each rate `r < 1` separately, one `S` with
`L⁴·r^{L-1} ≤ S` at every `L ≥ 1`. That `S` depends on `r`.

`ev_period` and `corrClay_at_period` record the index fact behind the first two: on the even
sublattice parameter `c ∈ [0, m]` the profile `g(c) = ρ(2c)` has `g(m) = g(0)`, since `2m` is one
full period, so the outermost chord of the convex profile is horizontal.

## Scope

None of the Part 2 statements is about the Wilson correlation: each exhibits a profile satisfying the
named premises, and `ContactFloor.contact_relative_unconditional` states the quartic law on `[0, b]`
for the correlation itself.

`MomentShape.Shape` is a premise set in which no field mentions `β` or carries a `β`-dependent
constant, but it is not available at every coupling: `MomentShape.shape_wilsonCorrAt` requires
`0 ≤ β`, because its `nonneg` field is `Complete.wilson_reflection_positive_at_even`.
`MomentShape.corrClay_neg` and `LogConvex.corrClay_log_convex` do hold at every real `β`.

The geometric envelope in `no_uniform_quartic_constant_of_vanishing_rate` is a hypothesis about an
abstract family `M : ι → ℝ`. No theorem in this tree derives `ρ(d)/ρ(0) ≤ e^{-M·d}` from
`LogConvex.corrClay_log_convex`, whose conclusion is the three-point form
`ρ(e₁+e₂)² ≤ ρ(2e₁)·ρ(2e₂)`; and `MomentShape.odd_scaling_admissible` shows the odd lags are not
bounded below by that premise set.
-/

namespace MassGap.WeakArm

open MassGap.WilsonBridge MassGap.MomentShape

/-! ## Part 1 — `ρ(d) ≤ ρ(0)` at every lag -/

section ContactBound

variable {Nap m : ℕ}

/-- `ev Nap 0 = 0`: the even lag at parameter zero is the zero lag.

DERIVED: `0` is the even-sublattice parameter on the left and the lag it names on the right. It is
the only numeral in the statement. -/
theorem ev_zero (Nap : ℕ) : ev Nap 0 = 0 := by
  apply Fin.ext
  rw [ev_eq, finOf_val]
  simp

#print axioms ev_zero

/-- `ev Nap (m - c) = -(ev Nap c)` for `c ≤ m` at even extent `Nap + 1 = 2 * m`: the even lag at the
complementary parameter is the circle negation.

Doubling `m` is one full period, so `2(m - c) + 2c = Nap + 1`. This is what carries a statement
proved for `2 * c ≤ m` to the whole range `c ≤ m`. The subtraction `m - c` is in `ℕ`, and `hc`
keeps it faithful.

DERIVED: `2` is the doubling in the even extent `Nap + 1 = 2 * m` and in the even-lag map; `1` is the
offset in the aperture size `Nap + 1`. -/
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

/-- `corrClay (Nap + 1) β (ev Nap c) ≤ corrClay (Nap + 1) β 0` for every `c ≤ m`, at even extent
with `3 ≤ m`, given nonnegativity of the profile.

`MomentShape.corrClay_even_antitone` covers `2 * c ≤ m` directly; past that, `ev_compl` and
`MomentShape.corrClay_neg` replace `c` by `m - c`, which is in range. The coupling `β` is an
arbitrary real.

DERIVED: `2` is the doubling in the even extent `Nap + 1 = 2 * m`; `1` is the offset in the aperture
size; `3` is the lower bound on `m` that `MomentShape.corrClay_even_antitone` requires; `0` is the
contact lag and the lower bound in the nonnegativity hypothesis. -/
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

/-- `corrClay (Nap + 1) β (finOf Nap w) ≤ corrClay (Nap + 1) β 0` for every `w ≤ m`, at even extent
with `3 ≤ m`, given nonnegativity.

Even `w` is `corrClay_ev_le_zero`. Odd `w` is `MomentShape.corrClay_odd_le`, whose two even
neighbours are both already under `ρ(0)`, giving `ρ(w)² ≤ ρ(0)²`, from which nonnegativity takes the
square root.

Scope: `3 ≤ m` is what the odd branch needs — it requires `c + 1 < m` from `2 * c + 1 ≤ m`.

DERIVED: `2` is the doubling in the even extent; `1` is the offset in the aperture size; `3` is the
lower bound on `m`; `0` is the contact lag and the lower bound in the nonnegativity
hypothesis. -/
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

/-- `corrClay (Nap + 1) β d ≤ corrClay (Nap + 1) β 0` at every lag `d`, at even extent
`Nap + 1 = 2 * m` with `3 ≤ m`, at every real coupling, given nonnegativity of the profile.

Every `d : Fin (Nap + 1)` is covered by a split at `m`: below it `d` is its own representative and
`corrClay_finOf_le_zero` applies; above it `MomentShape.corrClay_neg` replaces `d` by `-d`, whose
value `2 * m - d` is then in range.

Scope. The only hypothesis on the profile is nonnegativity — no lower bound on `ρ 0` is assumed, so
no constant here depends on the coupling, and the statement is invariant under `ρ ↦ t·ρ`. The extent
must be even and `m` at least `3`.

DERIVED: `2` is the doubling in the even extent `Nap + 1 = 2 * m`; `1` is the offset in the aperture
size `Fin (Nap + 1)`; `3` is the lower bound on `m`, which is where
`MomentShape.corrClay_even_antitone` becomes available and is also what the odd branch needs; `0` is
the contact lag on the right and the lower bound in the nonnegativity hypothesis. -/
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

/-- `wilsonCorrAt Nap β d ≤ wilsonCorrAt Nap β 0` at every lag, at even extent with `3 ≤ m` and
`0 ≤ β`.

`corrClay_le_at_zero` with nonnegativity supplied by
`Complete.wilson_reflection_positive_at_even`, which is a theorem rather than a named axiom.

Scope: discharging the hypothesis costs the sign condition on `β`. `corrClay_le_at_zero` is the form
that holds at every real coupling; this one is restricted to the nonnegative half.

DERIVED: `2` is the doubling in the even extent `Nap + 1 = 2 * m`; `1` is the offset in the aperture
size; `3` is the lower bound on `m`; `0` is the contact lag and the lower bound on `β`. -/
theorem wilsonCorrAt_le_at_zero (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) (d : Fin (Nap + 1)) :
    MassGap.wilsonCorrAt Nap β d ≤ MassGap.wilsonCorrAt Nap β 0 :=
  corrClay_le_at_zero hm hm3 β
    (fun d => (MassGap.wilson_reflection_positive_at_even Nap m hm (by omega) hβ).1 d) d

#print axioms wilsonCorrAt_le_at_zero

/-- `wilsonCorrAt 5 β 1 ≤ wilsonCorrAt 5 β 0` at every `0 ≤ β`: `wilsonCorrAt_le_at_zero` at extent
six and lag one.

Extent six is the smallest even extent meeting `3 ≤ m`, and the lag is odd, which the antitone
results do not reach — every right-hand lag `LogConvex.corrClay_log_convex` produces is even. The
right-hand side is not zero: `PlaqVariance.corrClay_zero_pos` gives `0 < ρ(0)` at every aperture and
every real coupling.

DERIVED: `5` is the aperture index, so the extent is six, the smallest even one with `3 ≤ m`. `1` is
the lag, the smallest odd one. `0` is the contact lag and the lower bound on `β`. -/
theorem wilsonCorrAt_le_at_zero_at_extent_six {β : ℝ} (hβ : 0 ≤ β) :
    MassGap.wilsonCorrAt 5 β 1 ≤ MassGap.wilsonCorrAt 5 β 0 :=
  wilsonCorrAt_le_at_zero 5 3 (by norm_num) (by norm_num) hβ 1

#print axioms wilsonCorrAt_le_at_zero_at_extent_six

end ContactBound

/-! ## Part 2 — the no-gos -/

section NoGo

variable {Nap m : ℕ}

/-- `ev Nap m = 0` at even extent `Nap + 1 = 2 * m`: the even lag at parameter `m` is a full period,
hence the zero lag.

DERIVED: `2` is the doubling in `Nap + 1 = 2 * m` and in the even-lag map, which is why parameter `m`
is a full period; `1` is the offset in the aperture size; `0` is the lag it reduces to. -/
theorem ev_period (hm : Nap + 1 = 2 * m) : ev Nap m = 0 := by
  rw [ev_eq, hm.symm, finOf_period]

#print axioms ev_period

/-- `corrClay (Nap + 1) β (ev Nap m) = corrClay (Nap + 1) β 0` at even extent: the even-sublattice
profile `g(c) = ρ(2c)` has `g(m) = g(0)`.

Index arithmetic via `ev_period`; no property of `corrClay` is used and the coupling is arbitrary.
It is the endpoint instance of the symmetry `MomentShape.shape_antitone` consumes; the interior
instances come from `MomentShape.corrClay_neg` rather than from period arithmetic.

Scope. This is one equality between two values, not an argument. What it says about a convex profile
is that the outermost chord, from parameter `0` to parameter `m`, is horizontal; it says nothing
about interior chords, whose endpoints are ordinary values of `ρ`.

DERIVED: `2` is the doubling in `Nap + 1 = 2 * m` and in the even-lag map; `1` is the offset in the
aperture size; `0` is the lag on the right. -/
theorem corrClay_at_period (hm : Nap + 1 = 2 * m) (β : ℝ) :
    corrClay (Nap + 1) β (ev Nap m) = corrClay (Nap + 1) β 0 := by
  rw [ev_period hm]

#print axioms corrClay_at_period

/-- For every real `C` and every cut `m₀` there are an even extent `Nap + 1 = 2 * m` with `3 ≤ m`, a
profile `ρ` and a lag `d` such that `ρ` satisfies `MomentShape.Shape`, `0 < ρ 0` and `0 < ∑ ρ`, the
lag is past the cut and at least one, and `ρ d ≤ C * ρ 0 / (circLag d) ^ 4` fails.

The witness is the constant profile `fun _ => 1` at extent `4 * k + 4`, with `k` taken large enough
by a ceiling on `C` and `m₀`, and the lag at circle distance `k + 1`.

The three conjuncts on the profile are the premises available without a coupling hypothesis: `Shape`
is what `MomentShape.shape_wilsonCorrAt` gives, `0 < ρ 0` matches `PlaqVariance.corrClay_zero_pos`,
and `0 < ∑ ρ` matches the second conjunct of `Complete.wilson_reflection_positive_at_even`. The
latter two are not fields of `Shape`, and are included so the statement is against the whole
available set.

Scope: this is a statement about profiles satisfying those premises, not about the Wilson
correlation. `ContactFloor.contact_relative_unconditional` states the quartic law for the correlation
on a bounded coupling interval.

DERIVED: `2` is the doubling in the even extent `Nap + 1 = 2 * m`; `1` is the offset in the aperture
size, the lower bound on the circle distance, and the constant profile's value; `3` is the lower
bound on `m`, matching Part 1's setting; `0` is the contact lag and the lower bound in the two
positivity conjuncts; `4` is the exponent of the quartic the statement negates. The extent and the
lag are read off `C` and `m₀` by a ceiling. -/
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

/-- For every `t < 1`, every even extent with `3 ≤ m`, and every lag `d`, there is a profile `ρ`
satisfying `MomentShape.Shape`, `0 < ρ 0` and `0 < ∑ ρ` for which `ρ d ≤ t * ρ 0` fails.

The witness is the constant profile. So the factor `1` in `corrClay_le_at_zero` cannot be improved on
the premise set `Shape` records, at any lag or extent.

Scope: the two extent hypotheses are underscored and unused — the witness needs neither — so the
statement holds at any `Nap` and `m` whatever, and is carried in this form only to read against Part
1's setting. `no_contact_relative_from_shape` is the same witness against a lag-dependent factor.

DERIVED: `2` is the doubling in the unused hypothesis `Nap + 1 = 2 * m`; `1` is the offset in the
aperture size and the strict upper bound on `t`; `3` is the unused lower bound on `m`; `0` is the
contact lag and the lower bound in the two positivity conjuncts. -/
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

/-! ### A constant per rate is not a constant for all rates -/

/-- For every real `C` and every cut `m₀` there is a `k ≥ max m₀ 1` with `C / k ^ 4 < 1 / 2`.

Arithmetic: `k ^ 4` grows at least as fast as `k`, so the quotient clears any fixed positive level
once `k` passes a ceiling read off `C`.

Scope: the level `1 / 2` is not arbitrary here — it is the value
`no_uniform_quartic_constant_of_vanishing_rate` pins its exponential to, which is why this lemma is
stated at that level rather than at a general one.

DERIVED: `1` is the lower bound on `k` and the numerator of the level; `2` is its denominator, the
level the exponential in the consumer is pinned to; `4` is the quartic's exponent. -/
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

/-- Given a family of rates `M : ι → ℝ` with `0 < M i` at every index and infimum zero, then for
every real `C` and every cut `m₀` there are an index `i` and a `k ≥ max m₀ 1` with
`C / k ^ 4 < exp (-(M i * k))`.

`exists_lag_halving` puts `C / k ^ 4` below `1 / 2`, and the infimum hypothesis supplies an index
with `M i < (log 2) / k`, which puts the exponential above `1 / 2`.

Scope. The rate family is a hypothesis about an abstract `M`; no theorem in this tree derives a
geometric envelope `ρ(d)/ρ(0) ≤ exp (-M·d)` from `LogConvex.corrClay_log_convex`, whose conclusion is
the three-point form `ρ(e₁+e₂)² ≤ ρ(2e₁)·ρ(2e₂)`. Nothing here is a statement about the Wilson
correlation or about how any rate behaves as the coupling grows.

`StrongArm.exists_geom_quartic_bound` gives, for each rate `r < 1` separately, one `S` with
`L⁴·r^(L-1) ≤ S` at every `L ≥ 1`; that `S` is a function of `r`.

DERIVED: `0` is the lower bound in the positivity hypotheses on `M i` and on `ε`; `1` is the lower
bound on `k`; `4` is the quartic's exponent. The halving level and the logarithm appear in the proof,
not in the statement. -/
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

/-- `invSucc n = 1 / (n + 1)`: a family of strictly positive reals with infimum zero, indexed by
`ℕ`.

It exists to witness the hypotheses of `no_uniform_quartic_constant_of_vanishing_rate`. Any strictly
positive null sequence would serve, and that theorem is stated over an arbitrary one.

DERIVED: the statement carries no numeral — `invSucc` takes `n : ℕ` and returns `ℝ`, and the shift
and the numerator live in the body. -/
noncomputable def invSucc (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem invSucc_pos (n : ℕ) : 0 < invSucc n := by
  unfold invSucc
  positivity

#print axioms invSucc_pos

/-- For every `ε > 0` some index has `invSucc i < ε`: the family gets below every positive level,
so its infimum is zero.

DERIVED: `0` is the strict lower bound on `ε`, and is the only numeral in the statement. -/
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

/-- `no_uniform_quartic_constant_of_vanishing_rate` instantiated at `invSucc`: for every real `C` and
every cut `m₀` there are an index `i` and a `k ≥ max m₀ 1` with
`C / k ^ 4 < exp (-(invSucc i * k))`.

`invSucc_pos` and `invSucc_lt` discharge the two hypotheses, so the general statement is not about an
empty premise.

Scope: one family is exhibited. Nothing here says which family, if any, the Wilson correlation would
supply.

DERIVED: `0` is the lower bound in the positivity conjunct; `1` is the lower bound on `k`; `4` is the
quartic's exponent. -/
theorem no_uniform_quartic_constant_nonvacuous (C : ℝ) (m₀ : ℕ) :
    ∃ (i : ℕ) (k : ℕ), 0 < invSucc i ∧ m₀ ≤ k ∧ 1 ≤ k ∧
      C / (k : ℝ) ^ 4 < Real.exp (-(invSucc i * (k : ℝ))) :=
  no_uniform_quartic_constant_of_vanishing_rate invSucc invSucc_pos
    (fun ε hε => invSucc_lt ε hε) C m₀

#print axioms no_uniform_quartic_constant_nonvacuous

end NoGo

end MassGap.WeakArm
