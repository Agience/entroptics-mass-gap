import Mathlib
import MassGap.StrongCoupling
import MassGap.ShareEnvelope

/-!
# MassGap.StrongArm — the contact-relative power law on a DERIVED coupling interval `[0, b]`

`ShareEnvelope.substrate_of_contact_relative_decay` discharges the substrate hypothesis from

    ρ(d) ≤ C · ρ(0) / circLag(d)⁴      for circLag d ≥ m₀

with ONE `C`, ONE `m₀`, EVERY aperture and EVERY coupling. The coupling quantifier is the open part.
This file closes the STRONG-COUPLING ARM of that quantifier, and it does so CONDITIONALLY on one
named statement which it does NOT prove — see "What is open" below, which is the point of the file.

## What is proved here, unconditionally

* `exists_strong_arm_cut` — a coupling cut `b > 0` with `coreRate (16·4) b < 1`, obtained from
  `StrongCoupling.core_rate_lt_one_of_small_hypercubic`, which is an EXISTENTIAL carrying no numeral.
  Nothing is chosen: the cut is the estimate's own neighbourhood of `β = 0` and no literal appears in
  the statement.
* `coreRate_mono_beta`, `corePrefactor_mono_beta`, `coreConst_mono_beta` — the rate and the constant
  are monotone in the coupling on `β ≥ 0`, read off the closed forms
  `coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}` and `corePrefactor K β = 8(4(K+1)²)²(e^{4βK})²`. This is
  what makes ONE `(C, r)` serve the whole closed interval `[0, b]` rather than one pair per coupling.
* `exists_geom_quartic_bound`, `exists_contact_shape_bound` — a geometric sequence dominates a
  quartic OUTRIGHT, not merely eventually: for `0 ≤ r < 1` there is a single `S` with
  `L⁴·r^{L−1} ≤ S` at every `L ≥ 1`. The consequence is that the cut `m₀` in the target statement is
  `1`, DERIVED rather than chosen — no lag has to be excluded — and `S` comes from `r` alone, through
  `tendsto_pow_const_mul_const_pow_of_lt_one` and boundedness of a convergent sequence.
* `wilsonCorrAt_eq_corrClay` — the identification `wilsonCorrAt N β d = corrClay (N+1) β d`, by
  `rfl`, checked here rather than taken from a docstring. It is what lets the estimate on the
  constructed `SU(3)` four-dimensional correlation be read as a statement about the object
  `substrate_of_contact_relative_decay` consumes.
* `coreRate_exceeds` — the rate is unbounded above in the coupling, at every degree: `∀ M, ∃ β ≥ 0,
  M < coreRate K β`. That is the whole statement. `coreRate K β ≥ 8β`, which falls out of
  `e^x ≥ x + 1`, is how the witness is built inside the proof and is NOT a conclusion a caller gets.
  This is the arithmetic behind the reading "the rate diverges as `β → ∞`", made a theorem rather
  than a remark.

## What is open, and it is the whole crux

`contact_relative_on_strong_arm` is stated as an IMPLICATION out of `ContactFloor b`:

    ∃ δ > 0, ∀ N, ∀ β ∈ [0, b],  δ ≤ wilsonCorrAt N β 0

— one positive lower bound on the CONTACT value, uniform in the APERTURE. This file does not prove
it. **IT IS PROVED**, in `MassGap.ContactFloor`: `contactFloor_holds b : ContactFloor b` at
every real `b`, foundational only, with `contact_relative_unconditional` carrying nothing. The floor
is `e^{−128b}·δ₀`, and the section below says where the aperture leaves.

**⛔ WHAT REMAINS OPEN IS THE COUPLING RANGE, NOT THE FLOOR.** `b` is existential and comes from
`exists_strong_arm_cut`, whose only lever is `coreRate (16·4) b < 1`; `coreRate_exceeds` proves that
condition FAILS at large `β`. So this arm is closed on `[0, b]` and the crux is `β > b`.

`PlaqVariance.corrClay_zero_pos` gives `0 < corrClay (N+1) β 0` at every aperture and every coupling,
but it gives no number: its proof runs through `Continuous.ae_eq_iff_eq` against an
`IsOpenPosMeasure`, which yields strict positivity and no rate. Taking a minimum over a compact
coupling interval at FIXED aperture is immediate from that plus
`PlaqVariance.continuous_wilsonSystem_boltz`; the minimum so obtained depends on the aperture, and a
hypothesis that quantifies over every aperture cannot consume it. The only quantitative Gibbs-
versus-Haar domination in the tree, `WilsonRead.expect_ge_haar_of_nonneg`, carries the constant
`e^{−8|β|}` whose exponent is twice the plaquette count, so it degrades as the lattice grows; and
`WilsonReal.wilsonSystem_partition_pos` bounds the weight by `e^{|β|·2·card Pq}`, extensive in the
same way.

The ingredients a locality argument would need do exist — `ReflectionPositivity.hol_congr_on_support`
(a holonomy reads only its own links), `ReflectionPositivity.action_split` and
`action_on_congr_of_support` (the action splits along a plaquette subset), `StrongCoupling.touchDeg`
with `touchDeg_bd_le` (the number of plaquettes meeting one plaquette is `≤ 16·dim`, with no extent
in it), and `WilsonReal.block_integral_factor` — but every one of them is used in the tree in the
identity, vanishing or upper-bound direction, and none is applied to bound anything below.
`WilsonAnalytic.expect_lipschitz_local` produces exactly the extent-free Lipschitz constant such an
argument wants, and it takes as hypothesis that the connected correlation VANISHES outside a finite
plaquette set at every coupling, which is the clustering statement under proof.

So the arm is reduced to one statement, not discharged.

## Two things this file must not be read as saying

**It does not discharge the substrate hypothesis.** That hypothesis needs every coupling.
`substrate_of_contact_relative_decay` is not invoked here and cannot be: what is produced is a
`(C, m₀)` valid on `[0, b]` and silent on `[b, ∞)`. What changes is the shape of what is open — from
the whole coupling line to `[b, ∞)`, plus `ContactFloor b` on the arm itself.

**The route re-introduces a non-scale-free ingredient, and the tree already says why that costs
something.** `ShareEnvelope.mass_floor_is_not_scale_free` proves that pairing an unnormalised
envelope with a positive floor is strictly stronger than the scale-free conclusion it is used to
reach, by one whole degree of freedom. `ContactFloor` is a floor of exactly that kind. The strong-
coupling estimate bounds `|ρ(d)|` ABSOLUTELY, the target is a RATIO, and the only way across is a
floor on the denominator — so the composite hypothesis here is strictly stronger than the
contact-relative law it yields. That is a real cost and it is not hidden by the statement.

## Why the arm is unfinished rather than excluded

The reason on record for not pursuing this route is that the rate diverges as `β → ∞`.
`coreRate_exceeds` confirms the arithmetic: `coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}` is unbounded,
so `coreRate < 1` — the hypothesis every bound in `StrongCoupling` carries — cannot hold at large
coupling. That is a statement about the reach of THIS estimate. It is not a theorem that the
contact-relative law fails at large coupling, and no such theorem is in the tree. The estimate stops;
the arm it stops on is the one this file fills in.
-/

namespace MassGap.StrongArm

open MassGap.StrongCoupling

/-! ### The coupling cut, from the estimate's own neighbourhood

`core_rate_lt_one_of_small_hypercubic` gives a half-open interval on which the rate is below one. The
statements below need the rate below one AT an endpoint, so that monotonicity in the coupling can
carry one constant across the whole CLOSED interval. That endpoint is produced from the existential,
never named: no numeral occurs in `exists_strong_arm_cut`. -/

/-- **A CUT WITH THE RATE BELOW ONE AT THE ENDPOINT.** The interval `core_rate_lt_one_of_small_hypercubic`
supplies is half-open, so its right endpoint need not itself satisfy the bound. Any interior point
does, and the statement records only that one exists — the threshold is whatever `16·dim` makes it,
exactly as in the lemma this is derived from. -/
theorem exists_strong_arm_cut : ∃ b : ℝ, 0 < b ∧ coreRate (16 * 4) b < 1 := by
  obtain ⟨b₀, hb₀, hlt⟩ := core_rate_lt_one_of_small_hypercubic 4
  exact ⟨b₀ / 2, by linarith, hlt (b₀ / 2) (by linarith) (by linarith)⟩

#print axioms exists_strong_arm_cut

/-! ### Monotonicity in the coupling — what makes ONE constant serve a whole interval

Both `coreRate` and `corePrefactor` are increasing on `β ≥ 0`, read off their closed forms. Neither
monotonicity is in the tree: `coreRate_mono` and `coreConst_mono` are monotonicity in the DEGREE `K`
at fixed coupling, which is a different statement and does not give this one. -/

/-- The rate increases with the coupling on `β ≥ 0`: both `e^{2β} − 1` and `e^{4βK}` do, and both are
nonnegative there. -/
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

/-- The prefactor increases with the coupling on `β ≥ 0`: it is a positive constant times
`(e^{4βK})²`. -/
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

/-- **The assembled constant increases with the coupling**, below the rate-one threshold: the
numerator increases and the denominator `1 − rate` decreases. This is the step that lets the value at
the right endpoint bound the constant on the whole interval. -/
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

/-- The assembled constant is nonnegative below the rate-one threshold — `corePrefactor ≥ 1` and the
denominator is positive. -/
theorem coreConst_nonneg_of_lt_one (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate K β < 1) :
    0 ≤ coreConst K β := by
  have hP : (1 : ℝ) ≤ corePrefactor K β := one_le_corePrefactor K hβ
  have hd : (0 : ℝ) < 1 - coreRate K β := by linarith
  unfold coreConst
  positivity

#print axioms coreConst_nonneg_of_lt_one

/-! ### A geometric sequence dominates a quartic OUTRIGHT

The target carries `1/L⁴` and the estimate carries `r^{L−1}`. What is needed is one `S` with
`L⁴·r^{L−1} ≤ S` for EVERY `L ≥ 1` — not eventually, because an eventual statement would leave a cut
`m₀` to be named, and naming it would be choosing it. Boundedness of the whole sequence removes the
cut: `m₀ = 1`, and the only lag it excludes is `circLag d = 0`, which is `d = 0` — the contact term
itself, which the target statement does not speak about. -/

/-- **Boundedness of `(m+1)⁴·rᵐ` at `0 ≤ r < 1`.** The sequence converges to zero, hence is bounded;
`(m+1)⁴ ≤ 16m⁴ + 16` reduces it to the two Mathlib limits `(m)⁴rᵐ → 0` and `rᵐ → 0`. -/
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

/-- **The shape the contact-relative statement consumes.** One `S` with `L⁴·r^{L−1} ≤ S` at every
`L ≥ 1`. Reindexing `m = L − 1` is the whole content. -/
theorem exists_contact_shape_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ L : ℕ, 1 ≤ L → (L : ℝ) ^ 4 * r ^ (L - 1) ≤ S := by
  obtain ⟨S, hS0, hS⟩ := exists_geom_quartic_bound hr0 hr1
  refine ⟨S, hS0, fun L hL => ?_⟩
  have hcast : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by
    rw [Nat.cast_sub hL, Nat.cast_one]; ring
  calc (L : ℝ) ^ 4 * r ^ (L - 1) = (((L - 1 : ℕ) : ℝ) + 1) ^ 4 * r ^ (L - 1) := by rw [hcast]
    _ ≤ S := hS (L - 1)

#print axioms exists_contact_shape_bound

/-! ### The identification, checked rather than cited

`Complete.wilsonCorrAt N β` is `WilsonBridge.corrClay (N+1) β` by definition, and `corrClay` is
`corrHyper` at `d = 4`, `Nc = 3`, plane `(0,1)`, lag axis `2`, which unfolds to `wilsonCorrConn` on
`WilsonHypercubic.bd (d := 4) (n := N+1)`. The first link is `rfl` and is recorded as a theorem so
that the build checks it; the rest is `StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow`'s own
statement, which is already in terms of `corrClay`. -/

/-- `wilsonCorrAt` IS `corrClay`, definitionally. -/
theorem wilsonCorrAt_eq_corrClay (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    MassGap.wilsonCorrAt N β d = MassGap.WilsonBridge.corrClay (N + 1) β d := rfl

#print axioms wilsonCorrAt_eq_corrClay

/-! ### The open input, named

Everything below the cut `b` reduces to this one statement and nothing else. Its two quantifiers are
not symmetric: the coupling one is over a COMPACT interval and is discharged at each fixed aperture
by continuity and `PlaqVariance.corrClay_zero_pos`; the APERTURE one is the crux, and nothing in the
development bears on it. -/

/-- **THE CARRIED HYPOTHESIS: an APERTURE-UNIFORM floor on the contact value, on `[0, b]`.**

`PlaqVariance.corrClay_zero_pos` gives `0 < corrClay (N+1) β 0` at every aperture and every coupling,
with no number attached; this asks for ONE number good at every aperture at once.

**IT IS PROVED**, in `MassGap.ContactFloor`: `contactFloor_holds b : ContactFloor b` at every real `b`,
foundational only, and `contact_relative_unconditional` is the theorem below with this hypothesis
discharged and nothing carried. The floor is `e^{−128b}·δ₀`. The aperture leaves at two places and
both are worth naming: the exponent counts only the plaquettes SHARING A LINK with the one being read,
which `StrongCoupling.touchDeg_bd_le` caps at `16·dim = 64` with no extent in it (the `2` is
`WilsonAction.wilsonDensity_le_two`); and at `β = 0` the measure IS Haar, so the contact value is a
single `SU(3)` number, `haarSecond − haarMean²`, the same at every extent `≥ 2`
(`ContactFloor.corrClay_zero_at_zero_eq`, `corrClay_zero_at_zero_const`).

WHAT IT DOES NOT GIVE, and cannot: the floor DEGRADES like `e^{−128b}`, so this proves a floor on each
bounded coupling interval and never one number for the half-line. That is not slack in the proof — the
plaquette variance really does vanish as `β → ∞`. Any argument for `[b, ∞)` must therefore never bound
`ρ(0)` below at all.

DERIVED: every numeral above is read off an existing theorem, none is chosen. `16·dim` is
`StrongCoupling.touchDeg_bd_le`'s cap on the number of plaquettes sharing a link with the one being
read; `dim = 4` is the lattice's own dimension, so that cap is `64`. The `2` is
`WilsonAction.wilsonDensity_le_two`, and `2 · 64 = 128` is the exponent. `3` is `SU(3)`'s rank, carried
from the ensemble. The statement's own `0` is the lower end of the physical coupling domain and `1`
does not appear in it — `0 < δ` is positivity, not a magnitude, and `δ` is existentially bound rather
than named. -/
def ContactFloor (b : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (β : ℝ), 0 ≤ β → β ≤ b → δ ≤ MassGap.wilsonCorrAt N β 0

#print axioms ContactFloor

/-! ### The strong arm -/

/-- **THE CONTACT-RELATIVE POWER LAW ON A DERIVED COUPLING INTERVAL.**

There is a cut `b > 0`, coming from the strong-coupling estimate's own neighbourhood of zero and
named by no numeral, such that GIVEN an aperture-uniform contact floor on `[0, b]` there is ONE
constant `C` with

    ρ_N(β, d) ≤ C · ρ_N(β, 0) / circLag(d)⁴

at EVERY aperture `N`, EVERY coupling `β ∈ [0, b]` and EVERY lag with `circLag d ≥ 1`. The cut in the
lag is `1`, which excludes only the contact term itself, so it is not a threshold in any working
sense; `C` is `coreConst(16·4, b) · S / δ` with `S` the geometric-beats-quartic bound at
`r = coreRate(16·4, b)`, so every ingredient is read off the estimate and the floor.

WHAT IS NOT PROVED: `ContactFloor b`, and anything at all on `[b, ∞)`. This does not discharge
`ShareEnvelope.substrate_of_contact_relative_decay`'s hypothesis, which quantifies over every
coupling, and that theorem is deliberately not invoked. -/
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

/-! ### The reach of the estimate, and what it does and does not exclude -/

/-- **THE RATE IS UNBOUNDED IN THE COUPLING.** The statement is exactly that: for every `M` there is
a `β ≥ 0` with `M < coreRate K β`. The inequality `coreRate K β ≥ 8β` — from `e^{2β} − 1 ≥ 2β`,
`4(K+1)² ≥ 4` and `e^{4βK} ≥ 1` — is the WITNESS CONSTRUCTION inside the proof, which takes
`β = max 0 ((M+1)/8)`; it is not what the theorem asserts, and quoting it as the theorem overstates
what is available to a caller. This is the arithmetic
behind "the rate diverges as `β → ∞`", and it is a statement about `coreRate`, hence about the reach
of the estimate carrying it. It is NOT a statement that the contact-relative law fails at large
coupling: nothing in the tree says that. -/
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
