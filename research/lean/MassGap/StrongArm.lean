import Mathlib
import MassGap.StrongCoupling
import MassGap.ShareEnvelope

/-!
# MassGap.StrongArm — a contact-relative quartic bound on a coupling interval `[0, b]`

The main statement, `contact_relative_on_strong_arm`, produces a cut `b > 0` at which
`coreRate (16 * 4) b < 1`, and, given a contact floor on `[0, b]`, one constant `C` with

    wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (circLag d) ^ 4

at every aperture `N`, every `β ∈ [0, b]`, and every lag with `1 ≤ circLag d`. That is the shape
`ShareEnvelope.substrate_of_contact_relative_decay` consumes, restricted to a bounded coupling
interval; that theorem quantifies over every coupling and is not invoked here.

## The pieces

* `exists_strong_arm_cut` — the cut, from
  `StrongCoupling.core_rate_lt_one_of_small_hypercubic`'s half-open interval, taken at its midpoint
  so the rate is below one at the endpoint itself. The lemma is existential, so the cut is not
  named.
* `coreRate_mono_beta`, `corePrefactor_mono_beta`, `coreConst_mono_beta` — the rate, the prefactor
  and the assembled constant are monotone in the coupling on `β ≥ 0`, read off the closed forms
  `coreRate K β = 4(K+1)²(e^{2β}-1)e^{4βK}` and `corePrefactor K β = 8(4(K+1)²)²(e^{4βK})²`. This is
  what lets one pair `(C, r)` serve a whole closed interval. `StrongCoupling`'s own `coreRate_mono`
  and `coreConst_mono` are monotonicity in the degree `K`, a different statement.
* `coreConst_nonneg_of_lt_one` — non-negativity of the assembled constant below the rate-one
  threshold.
* `exists_geom_quartic_bound`, `exists_contact_shape_bound` — at `0 ≤ r < 1` a single `S` bounds
  `L ^ 4 * r ^ (L - 1)` at every `L ≥ 1`, not merely eventually. The sequence converges to zero, so
  it is bounded; `(m+1)^4 ≤ 16m^4 + 16` reduces it to two Mathlib limits. The consequence is that the
  lag cut in the main statement is `1`, which excludes only `circLag d = 0`.
* `wilsonCorrAt_eq_corrClay` — `wilsonCorrAt N β d = WilsonBridge.corrClay (N + 1) β d`, by `rfl`,
  stated so the build checks it. It is what lets
  `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` be read as a bound on `wilsonCorrAt`.
* `coreRate_exceeds` — for every `M` there is a `β ≥ 0` with `M < coreRate K β`.

## Scope

`ContactFloor b` — one `δ > 0` with `δ ≤ wilsonCorrAt N β 0` at every aperture and every
`β ∈ [0, b]` — is a hypothesis of `contact_relative_on_strong_arm`, defined here and proved in
`MassGap.ContactFloor` by `contactFloor_holds`, whose floor is `e^{-128b}·δ₀` and therefore degrades
with `b`. `PlaqVariance.corrClay_zero_pos` gives strict positivity of the contact value at each
aperture and coupling but attaches no number, so it does not supply an aperture-uniform floor.

`coreRate_exceeds` says `coreRate` is unbounded in the coupling, so the condition
`coreRate (16 * 4) b < 1` that `exists_strong_arm_cut` supplies cannot hold at large `β`. That is a
statement about the reach of this estimate. Nothing here says the quartic bound fails at large
coupling.

The main statement carries `C` bound outside the quantifiers over `N`, `β` and `d`, and is silent
about `β > b`. `ShareEnvelope.mass_floor_is_not_scale_free` records that pairing an unnormalised
envelope with a positive floor is strictly stronger than the scale-free conclusion it yields, by one
degree of freedom; the hypothesis pair here is of that kind, since the strong-coupling estimate
bounds `|ρ(d)|` absolutely and the conclusion is a ratio.
-/

namespace MassGap.StrongArm

open MassGap.StrongCoupling

/-! ### The coupling cut

`StrongCoupling.core_rate_lt_one_of_small_hypercubic` gives a half-open interval on which the rate is
below one. The statements below need the rate below one at an endpoint, so that monotonicity in the
coupling can carry one constant across a closed interval. The endpoint comes out of that existential
rather than being named. -/

/-- There is a `b > 0` with `coreRate (16 * 4) b < 1`.

The interval `StrongCoupling.core_rate_lt_one_of_small_hypercubic` supplies is half-open, so its
right endpoint need not satisfy the bound; the witness taken is its midpoint. The statement is
existential, so no particular cut is named.

DERIVED: `16` and `4` are the degree argument `16 * 4` — `StrongCoupling.touchDeg_bd_le`'s cap of
`16` plaquettes per dimension meeting a given plaquette, times the lattice dimension `4`. `0` is the
strict lower bound on the cut and `1` the rate threshold the estimate carries. None is chosen
here. -/
theorem exists_strong_arm_cut : ∃ b : ℝ, 0 < b ∧ coreRate (16 * 4) b < 1 := by
  obtain ⟨b₀, hb₀, hlt⟩ := core_rate_lt_one_of_small_hypercubic 4
  exact ⟨b₀ / 2, by linarith, hlt (b₀ / 2) (by linarith) (by linarith)⟩

#print axioms exists_strong_arm_cut

/-! ### Monotonicity in the coupling

`coreRate` and `corePrefactor` are increasing on `β ≥ 0`, read off their closed forms. This is what
lets one constant serve a whole interval. `StrongCoupling.coreRate_mono` and
`StrongCoupling.coreConst_mono` are monotonicity in the degree `K` at fixed coupling, a different
statement. -/

/-- `coreRate K x ≤ coreRate K y` whenever `0 ≤ x ≤ y`, at every degree `K`.

Both factors of the closed form, `e^{2β} - 1` and `e^{4βK}`, are non-negative and increasing on
`β ≥ 0`. The hypothesis `0 ≤ x` is needed for the first factor's non-negativity.

DERIVED: `0` is the lower bound on the coupling in `hx : 0 ≤ x`, and is the only numeral in the
statement; the closed form's constants live inside `coreRate`. -/
theorem coreRate_mono_beta (K : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coreRate K x ≤ coreRate K y := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by positivity
  have hq : Real.exp (2 * x) - 1 ≤ Real.exp (2 * y) - 1 := by
    have h := Real.exp_le_exp.mpr (by linarith : 2 * x ≤ 2 * y)
    linarith
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * x) - 1 := by
    have := Real.one_le_exp (x := 2 * x) (by linarith)
    linarith
  have hprod : (0 : ℝ) ≤ (y - x) * (K : ℝ) := mul_nonneg (by linarith) hK
  have hw : Real.exp (4 * x * (K : ℝ)) ≤ Real.exp (4 * y * (K : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hw0 : (0 : ℝ) < Real.exp (4 * x * (K : ℝ)) := Real.exp_pos _
  have h1 : (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * x) - 1)
      ≤ (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * y) - 1) :=
    mul_le_mul_of_nonneg_left hq hA
  have h2 : (0 : ℝ) ≤ (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * x) - 1) := mul_nonneg hA hq0
  unfold coreRate
  exact mul_le_mul h1 hw hw0.le (le_trans h2 h1)

#print axioms coreRate_mono_beta

/-- `corePrefactor K x ≤ corePrefactor K y` whenever `x ≤ y`, at every degree `K`.

The closed form is a positive constant times `(e^{4βK})²`, which is increasing. The binder `_hx` is
present for symmetry with `coreRate_mono_beta` and is not used.

DERIVED: `0` is the lower bound in the unused binder `_hx : 0 ≤ x`, and is the only numeral in the
statement. -/
theorem corePrefactor_mono_beta (K : ℕ) {x y : ℝ} (_hx : 0 ≤ x) (hxy : x ≤ y) :
    corePrefactor K x ≤ corePrefactor K y := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hprod : (0 : ℝ) ≤ (y - x) * (K : ℝ) := mul_nonneg (by linarith) hK
  have hw : Real.exp (4 * x * (K : ℝ)) ≤ Real.exp (4 * y * (K : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hw0 : (0 : ℝ) < Real.exp (4 * x * (K : ℝ)) := Real.exp_pos _
  have hsq : Real.exp (4 * x * (K : ℝ)) ^ 2 ≤ Real.exp (4 * y * (K : ℝ)) ^ 2 := by nlinarith
  have hc : (0 : ℝ) ≤ 8 * (4 * ((K : ℝ) + 1) ^ 2) ^ 2 := by positivity
  unfold corePrefactor
  exact mul_le_mul_of_nonneg_left hsq hc

#print axioms corePrefactor_mono_beta

/-- `coreConst K x ≤ coreConst K y` whenever `0 ≤ x ≤ y` and `coreRate K y < 1`.

The numerator increases by `corePrefactor_mono_beta` and the denominator `1 - coreRate` decreases by
`coreRate_mono_beta`. The hypothesis at `y` is what keeps both denominators positive, so it is
required at the upper point rather than the lower.

DERIVED: `0` is the lower bound in `hx : 0 ≤ x`; `1` is the rate threshold in `hy : coreRate K y < 1`,
which is where the denominator `1 - coreRate` changes sign. -/
theorem coreConst_mono_beta (K : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : coreRate K y < 1) : coreConst K x ≤ coreConst K y := by
  have hrx : coreRate K x ≤ coreRate K y := coreRate_mono_beta K hx hxy
  have h1 : (0 : ℝ) < 1 - coreRate K y := by linarith
  have h2 : (0 : ℝ) < 1 - coreRate K x := by linarith
  have hs : 1 - coreRate K y ≤ 1 - coreRate K x := by linarith
  have hple : corePrefactor K x ≤ corePrefactor K y := corePrefactor_mono_beta K hx hxy
  have hPy0 : (0 : ℝ) ≤ corePrefactor K y := by
    have := one_le_corePrefactor K (hx.trans hxy); linarith
  have a1 : corePrefactor K x * (1 - coreRate K y) ≤ corePrefactor K y * (1 - coreRate K y) :=
    mul_le_mul_of_nonneg_right hple h1.le
  have a2 : corePrefactor K y * (1 - coreRate K y) ≤ corePrefactor K y * (1 - coreRate K x) :=
    mul_le_mul_of_nonneg_left hs hPy0
  have hnum : (0 : ℝ)
      ≤ corePrefactor K y * (1 - coreRate K x) - corePrefactor K x * (1 - coreRate K y) := by
    linarith
  have hden : (0 : ℝ) < (1 - coreRate K y) * (1 - coreRate K x) := mul_pos h1 h2
  have hd : corePrefactor K y / (1 - coreRate K y) - corePrefactor K x / (1 - coreRate K x)
      = (corePrefactor K y * (1 - coreRate K x) - corePrefactor K x * (1 - coreRate K y))
        / ((1 - coreRate K y) * (1 - coreRate K x)) := by
    field_simp
  have hpos := div_nonneg hnum hden.le
  rw [← hd] at hpos
  unfold coreConst
  linarith

#print axioms coreConst_mono_beta

/-- `0 ≤ coreConst K β` when `0 ≤ β` and `coreRate K β < 1`.

`StrongCoupling.one_le_corePrefactor` makes the numerator at least one and the rate hypothesis makes
the denominator positive.

DERIVED: `0` is the lower bound on the coupling and the bound concluded; `1` is the rate threshold in
`hr : coreRate K β < 1`. -/
theorem coreConst_nonneg_of_lt_one (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate K β < 1) :
    0 ≤ coreConst K β := by
  have hP : (1 : ℝ) ≤ corePrefactor K β := one_le_corePrefactor K hβ
  have hd : (0 : ℝ) < 1 - coreRate K β := by linarith
  unfold coreConst
  positivity

#print axioms coreConst_nonneg_of_lt_one

/-! ### A geometric sequence against a quartic

The conclusion carries `1 / L ^ 4` and the estimate carries `r ^ (L - 1)`. What is needed is one `S`
with `L ^ 4 * r ^ (L - 1) ≤ S` at every `L ≥ 1`, not merely eventually: an eventual statement would
leave a cut to be named. Boundedness of the whole sequence makes the cut `1`, whose only exclusion is
`circLag d = 0`, the contact term. -/

/-- At `0 ≤ r < 1` there is an `S ≥ 0` with `((m : ℝ) + 1) ^ 4 * r ^ m ≤ S` at every `m : ℕ`.

The sequence converges to zero, hence is bounded; `(m+1)^4 ≤ 16 m^4 + 16` reduces it to the two
Mathlib limits `m^4 r^m → 0` and `r^m → 0`. The witness is taken as `max S 0` so the non-negativity
clause holds.

Scope: the bound holds at every `m`, not only past a cut. `r < 1` is strict and required.

DERIVED: `0` is the lower bound on `r` and on `S`; `1` is the strict upper bound on `r` and the
offset in `(m : ℝ) + 1`; `4` is the quartic's exponent, the power the conclusion of the main theorem
divides by. The `16`s used to dominate `(m+1)^4` appear in the proof, not in the statement. -/
theorem exists_geom_quartic_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ m : ℕ, ((m : ℝ) + 1) ^ 4 * r ^ m ≤ S := by
  have h4 : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ 4 * r ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 4 hr0 hr1
  have h0 : Filter.Tendsto (fun m : ℕ => r ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hsum : Filter.Tendsto (fun m : ℕ => 16 * ((m : ℝ) ^ 4 * r ^ m) + 16 * r ^ m)
      Filter.atTop (nhds 0) := by
    have h := (h4.const_mul (16 : ℝ)).add (h0.const_mul (16 : ℝ))
    simpa using h
  obtain ⟨S, hS⟩ := hsum.bddAbove_range
  refine ⟨max S 0, le_max_right _ _, fun m => ?_⟩
  have hSm : 16 * ((m : ℝ) ^ 4 * r ^ m) + 16 * r ^ m ≤ S := hS (Set.mem_range_self m)
  have hrm : (0 : ℝ) ≤ r ^ m := pow_nonneg hr0 m
  have hpoly : ((m : ℝ) + 1) ^ 4 ≤ 16 * (m : ℝ) ^ 4 + 16 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h2t : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
      have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1) h2t 4
      nlinarith [hpow]
  have hstep : ((m : ℝ) + 1) ^ 4 * r ^ m ≤ (16 * (m : ℝ) ^ 4 + 16) * r ^ m :=
    mul_le_mul_of_nonneg_right hpoly hrm
  have hform : (16 * (m : ℝ) ^ 4 + 16) * r ^ m = 16 * ((m : ℝ) ^ 4 * r ^ m) + 16 * r ^ m := by ring
  have : ((m : ℝ) + 1) ^ 4 * r ^ m ≤ S := by rw [hform] at hstep; linarith
  exact le_trans this (le_max_left _ _)

#print axioms exists_geom_quartic_bound

/-- At `0 ≤ r < 1` there is an `S ≥ 0` with `(L : ℝ) ^ 4 * r ^ (L - 1) ≤ S` at every `L ≥ 1`.

`exists_geom_quartic_bound` reindexed by `m = L - 1`; the hypothesis `1 ≤ L` is what makes the
natural-number subtraction faithful.

DERIVED: `0` is the lower bound on `r` and on `S`; `1` is the strict upper bound on `r`, the lower
bound on `L`, and the offset in `L - 1`; `4` is the quartic's exponent. -/
theorem exists_contact_shape_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ L : ℕ, 1 ≤ L → (L : ℝ) ^ 4 * r ^ (L - 1) ≤ S := by
  obtain ⟨S, hS0, hS⟩ := exists_geom_quartic_bound hr0 hr1
  refine ⟨S, hS0, fun L hL => ?_⟩
  have hcast : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by
    rw [Nat.cast_sub hL, Nat.cast_one]; ring
  calc (L : ℝ) ^ 4 * r ^ (L - 1) = (((L - 1 : ℕ) : ℝ) + 1) ^ 4 * r ^ (L - 1) := by rw [hcast]
    _ ≤ S := hS (L - 1)

#print axioms exists_contact_shape_bound

/-! ### The identification of the two correlation names

`Complete.wilsonCorrAt N β` is `WilsonBridge.corrClay (N+1) β` by definition, and `corrClay` is
`corrHyper` at `d = 4`, `Nc = 3`, plane `(0,1)`, lag axis `2`, which unfolds to `wilsonCorrConn` on
`WilsonHypercubic.bd (d := 4) (n := N+1)`. The first link is stated as a theorem so the build checks
it; `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` is already in terms of `corrClay`. -/

/-- `wilsonCorrAt N β d = WilsonBridge.corrClay (N + 1) β d`, by `rfl`.

Stated as a theorem so the identification is checked by the build rather than asserted in prose.

DERIVED: `1` is the offset in the aperture size `N + 1`, which is how `corrClay` indexes the extent
that `wilsonCorrAt` indexes by `N`. It is the only numeral in the statement. -/
theorem wilsonCorrAt_eq_corrClay (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    MassGap.wilsonCorrAt N β d = MassGap.WilsonBridge.corrClay (N + 1) β d := rfl

#print axioms wilsonCorrAt_eq_corrClay

/-! ### The contact floor, as a named `Prop`

`ContactFloor b` asks for one `δ > 0` good at every aperture and every `β ∈ [0, b]`. Its two
quantifiers behave differently: at fixed aperture the coupling one is a minimum over a compact
interval, available from continuity and `PlaqVariance.corrClay_zero_pos`, while the aperture one asks
for a single number across all extents. -/

/-- `ContactFloor b` unfolds to: there is a `δ > 0` such that `δ ≤ wilsonCorrAt N β 0` at every
aperture `N` and every coupling `β` with `0 ≤ β ≤ b`.

One number, uniform in the aperture. `PlaqVariance.corrClay_zero_pos` gives strict positivity of the
contact value at each aperture and coupling separately but attaches no number, so it does not supply
this.

`MassGap.ContactFloor` proves it: `contactFloor_holds b` at every real `b`, with floor
`e^{-128b}·δ₀`. The aperture drops out at two places. The exponent counts only the plaquettes sharing
a link with the one being read, which `StrongCoupling.touchDeg_bd_le` caps at `16` per dimension,
hence `64` in four dimensions, with no extent in it; doubling that by
`WilsonAction.wilsonDensity_le_two`'s range bound gives `128`. And at `β = 0` the measure is Haar, so
the contact value is a single `SU(3)` number, the same at every extent at least `2`
(`corrClay_zero_at_zero_eq`, `corrClay_zero_at_zero_const`).

Scope: the floor obtained there depends on `b` and decreases with it, so the statement is per bounded
interval and does not extend to the half-line.

DERIVED: the statement carries no numeral. `ContactFloor` takes `b : ℝ` and everything else — the
positivity of `δ`, the coupling range and the contact lag — lives in the body rather than the
type. -/
def ContactFloor (b : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (β : ℝ), 0 ≤ β → β ≤ b → δ ≤ MassGap.wilsonCorrAt N β 0

#print axioms ContactFloor

/-! ### The strong arm -/

/-- There is a cut `b > 0` with `coreRate (16 * 4) b < 1` such that, given `ContactFloor b`, there is
one constant `C ≥ 0` with

    wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (circLag d : ℝ) ^ 4

at every aperture `N`, every coupling `β` with `0 ≤ β ≤ b`, and every lag with `1 ≤ circLag d`.

The cut comes from `exists_strong_arm_cut`. The constant produced is
`coreConst (16 * 4) b * S / δ`, with `S` from `exists_contact_shape_bound` at
`r = coreRate (16 * 4) b` and `δ` from the floor. Monotonicity in the coupling
(`coreRate_mono_beta`, `coreConst_mono_beta`) is what lets the endpoint values serve the whole
interval; `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` supplies the absolute bound and
`wilsonCorrAt_eq_corrClay` transfers it.

Scope. `C` is bound outside the quantifiers over `N`, `β` and `d`. `ContactFloor b` is a hypothesis,
and the statement is silent about `β > b`; `coreRate_exceeds` shows the cut condition cannot hold at
large coupling. `ShareEnvelope.substrate_of_contact_relative_decay` quantifies over every coupling and
is not invoked. The lag condition `1 ≤ circLag d` excludes only `circLag d = 0`.

DERIVED: `16` and `4` are the degree argument `16 * 4`, `StrongCoupling.touchDeg_bd_le`'s per-dimension
cap times the lattice dimension. `0` is the lower end of the coupling range, the lower bound on `b`
and on `C`, and the contact lag in `wilsonCorrAt N β 0`. `1` is the rate threshold in
`coreRate (16 * 4) b < 1`, the lag cut in `1 ≤ circLag d`, and the offset in the aperture size
`Fin (N + 1)`. `4` is also the exponent the conclusion divides by, from the target shape. -/
theorem contact_relative_on_strong_arm :
    ∃ b : ℝ, 0 < b ∧ coreRate (16 * 4) b < 1 ∧
      (ContactFloor b →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 0 ≤ β → β ≤ b →
          1 ≤ Moment.circLag d →
            MassGap.wilsonCorrAt N β d
              ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4) := by
  obtain ⟨b, hb, hrb⟩ := exists_strong_arm_cut
  refine ⟨b, hb, hrb, ?_⟩
  rintro ⟨δ, hδ, hfloor⟩
  have hr0 : (0 : ℝ) ≤ coreRate (16 * 4) b := coreRate_nonneg _ hb.le
  have hA0 : (0 : ℝ) ≤ coreConst (16 * 4) b := coreConst_nonneg_of_lt_one _ hb.le hrb
  obtain ⟨S, hS0, hS⟩ := exists_contact_shape_bound hr0 hrb
  refine ⟨coreConst (16 * 4) b * S / δ, by positivity, ?_⟩
  intro N β d hβ0 hβb hL
  set L := Moment.circLag d with hLdef
  -- the coupling-uniform rate and constant on `[0, b]`
  have hrβ : coreRate (16 * 4) β ≤ coreRate (16 * 4) b := coreRate_mono_beta _ hβ0 hβb
  have hrβ1 : coreRate (16 * 4) β < 1 := lt_of_le_of_lt hrβ hrb
  have hAβ : coreConst (16 * 4) β ≤ coreConst (16 * 4) b := coreConst_mono_beta _ hβ0 hβb hrb
  have hrβ0 : (0 : ℝ) ≤ coreRate (16 * 4) β := coreRate_nonneg _ hβ0
  -- the absolute exponential bound at the lag, on the genuine four-dimensional geometry
  have hbnd := corrClay_abs_le_coreConst_mul_rate_pow N hβ0 hrβ1 d (L - 1) (by omega)
  have hpow : coreRate (16 * 4) β ^ (L - 1) ≤ coreRate (16 * 4) b ^ (L - 1) :=
    pow_le_pow_left₀ hrβ0 hrβ (L - 1)
  have hmul : coreConst (16 * 4) β * coreRate (16 * 4) β ^ (L - 1)
      ≤ coreConst (16 * 4) b * coreRate (16 * 4) b ^ (L - 1) :=
    mul_le_mul hAβ hpow (pow_nonneg hrβ0 _) hA0
  have habs := le_abs_self (MassGap.WilsonBridge.corrClay (N + 1) β d)
  have hstep1 : MassGap.wilsonCorrAt N β d
      ≤ coreConst (16 * 4) b * coreRate (16 * 4) b ^ (L - 1) := by
    rw [wilsonCorrAt_eq_corrClay]; linarith
  -- the quartic, from the geometric bound
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := hL
    exact_mod_cast this
  have hLpos : (0 : ℝ) < (L : ℝ) ^ 4 := by positivity
  have hgeom : (L : ℝ) ^ 4 * coreRate (16 * 4) b ^ (L - 1) ≤ S := hS L hL
  have hstep2 : coreConst (16 * 4) b * coreRate (16 * 4) b ^ (L - 1) * (L : ℝ) ^ 4
      ≤ coreConst (16 * 4) b * S := by
    calc coreConst (16 * 4) b * coreRate (16 * 4) b ^ (L - 1) * (L : ℝ) ^ 4
        = coreConst (16 * 4) b * ((L : ℝ) ^ 4 * coreRate (16 * 4) b ^ (L - 1)) := by ring
      _ ≤ coreConst (16 * 4) b * S := mul_le_mul_of_nonneg_left hgeom hA0
  -- the floor, turning the absolute bound into a relative one
  have hCnn : (0 : ℝ) ≤ coreConst (16 * 4) b * S / δ := by positivity
  have hfl := hfloor N β hβ0 hβb
  have hstep3 : coreConst (16 * 4) b * S
      ≤ coreConst (16 * 4) b * S / δ * MassGap.wilsonCorrAt N β 0 := by
    have h3 : coreConst (16 * 4) b * S / δ * δ
        ≤ coreConst (16 * 4) b * S / δ * MassGap.wilsonCorrAt N β 0 :=
      mul_le_mul_of_nonneg_left hfl hCnn
    have h4 : coreConst (16 * 4) b * S / δ * δ = coreConst (16 * 4) b * S := by
      field_simp
    linarith
  have hfinal : coreConst (16 * 4) b * coreRate (16 * 4) b ^ (L - 1)
      ≤ coreConst (16 * 4) b * S / δ * MassGap.wilsonCorrAt N β 0 / (L : ℝ) ^ 4 := by
    rw [le_div_iff₀ hLpos]
    linarith
  linarith

#print axioms contact_relative_on_strong_arm

/-! ### The reach of the estimate in the coupling -/

/-- For every real `M` and every degree `K` there is a `β ≥ 0` with `M < coreRate K β`.

The witness is built inside the proof from `coreRate K β ≥ 8β`, which follows from `e^{2β} - 1 ≥ 2β`,
`4(K+1)² ≥ 4` and `e^{4βK} ≥ 1`. That inequality is not part of the conclusion, so a caller gets the
existential and not the linear lower bound.

Scope: this is a statement about `coreRate`, and so about the range of couplings on which the
`coreRate < 1` hypothesis of the `StrongCoupling` bounds is available. It says nothing about whether
the quartic bound itself holds at large coupling.

DERIVED: `0` is the lower bound on the witness coupling, and is the only numeral in the statement;
`M` and `K` are parameters and the rate's own constants live inside `coreRate`. -/
theorem coreRate_exceeds (K : ℕ) (M : ℝ) : ∃ β : ℝ, 0 ≤ β ∧ M < coreRate K β := by
  refine ⟨max 0 ((M + 1) / 8), le_max_left _ _, ?_⟩
  set β := max 0 ((M + 1) / 8) with hβdef
  have hβ0 : (0 : ℝ) ≤ β := le_max_left _ _
  have hβM : (M + 1) / 8 ≤ β := le_max_right _ _
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : (4 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by nlinarith
  have hq : 2 * β ≤ Real.exp (2 * β) - 1 := by
    have := Real.add_one_le_exp (2 * β); linarith
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by linarith
  have hw : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp (by positivity)
  have h1 : (4 : ℝ) * (2 * β) ≤ (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) := by
    have ha : (4 : ℝ) * (Real.exp (2 * β) - 1)
        ≤ (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) :=
      mul_le_mul_of_nonneg_right hA hq0
    nlinarith
  have hAq0 : (0 : ℝ) ≤ (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) := by
    apply mul_nonneg _ hq0; positivity
  have h3 : (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) * 1
      ≤ (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) * Real.exp (4 * β * (K : ℝ)) :=
    mul_le_mul_of_nonneg_left hw hAq0
  have hlow : 8 * β ≤ coreRate K β := by
    unfold coreRate
    nlinarith
  have hM8 : M + 1 ≤ 8 * β := by linarith
  linarith

#print axioms coreRate_exceeds

end MassGap.StrongArm
