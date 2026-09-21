import MassGap.NonnegArm
import MassGap.OSFamily

/-!
# MassGap.ApertureRoute — the flagship from confinement at ONE aperture

`EvenAperture.existence_and_gap_of_substrate_even` consumes

    h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B

a moment bound quantified over EVERY even aperture. This file shows that the aperture quantifier is
not what the conclusion rests on, by rebuilding the flagship against the weaker hypothesis the
existing proof actually consumes.

## What `h` is used for, and it is less than it looks

Read `EvenAperture.fullModelEven`'s four fields:

    gap     := ymModelEven (apertureEven h)
    h1      := apertureEven_confines h
    h2      := A2_even (apertureEven h)
    measure := WilsonModel.ymFamilyTension

`apertureEven h` is `(exists_confining_even_aperture h).choose` and `apertureEven_confines h` is its
`.choose_spec`. `A2_even` takes no hypothesis. `ymFamilyTension` is a fixed object and the measure
side takes no hypothesis at all. So `h` enters the construction ONLY to produce an `EvenAp` together
with confinement at it, and is then discarded. Its load-bearing content is

    ∃ a : EvenAp, ∀ β : ℝ, 3^{−1/4} < ⟨cos θ⟩ of the read at (a, β)

— confinement at ONE even extent, for every coupling. That is `ConfinesAtAnAperture` below, and
`flagship_of_confinement_at_an_aperture` derives the whole flagship from it: the gap, non-triviality,
`SO(4)` invariance and the continuum measure.

**The condition is stated on the cosine average, NOT on the tension**, and that is not cosmetic:
`Real.log` is even, so `∀ β, μEven a β < κ₀YM` is satisfied by a read whose cosine average is `−1` —
no decay at all. `ConfinesAtAnAperture`'s docstring sets out the defect and
`unguarded_confinement_is_satisfiable_without_decay` machine-checks it on `Substrate.antipodeRead`.
The two spellings differ exactly by the positivity guard the tree already carries in
`Moment.Read.cosAvg_gt_of_tension_lt_floor`.

## THE APERTURE QUANTIFIER IS DROPPED, NOT SATISFIED

Nothing here proves confinement at any aperture. What is established is a strictly weaker HYPOTHESIS,
and the implication runs one way only:

* `confinement_at_an_aperture_of_substrate` — the old hypothesis gives the new one. It is
  `EvenAperture.exists_confining_even_aperture`, unchanged.
* **No converse is claimed, and none is available.** The old hypothesis bounds the moment at every
  even aperture simultaneously; the new one asks for confinement at a single extent of the prover's
  choosing. A witness for the second says nothing about any other extent.

So this does not discharge the reduction. It relocates the target from a statement uniform in the
aperture to a statement at one aperture, which is a different and smaller obligation.

## WHERE THE DIFFICULTY MOVES TO, AND WHAT CHOOSING THE EXTENT DOES NOT BUY

**Choosing the extent does not lower the bar.** `Moment.Read.tension_lt_floor_of_circ_moment`'s scale
hypothesis `(2π/(N+1))²·B/2 < 1 − 3^{−1/4}` does relax as the extent grows, but the quantity it
bounds grows at exactly the same rate, and the two cancel: substituting `d2At = substrateRatio·(N+1)²`
gives `(2π)²·substrateRatio/2 < 1 − 3^{−1/4}`, with no `N` in it. `Complete.surplus_ge`'s `hcancel`
step is that cancellation, proved as an EQUALITY by `field_simp` — "the aperture cancels EXACTLY: no
inequality is spent here, because the ratio is the read itself". So a larger extent admits a larger
absolute moment and demands a proportionally smaller ratio, and the criterion is the same at every
extent.

What choosing the extent DOES buy is the quantifier: the bar has to be met at ONE extent instead of at
all of them simultaneously.

**⚠ AND THAT IS NOT THE WHOLE OF THE WEAKENING — the cancellation above is a TAUTOLOGY, not a fact
about the correlation.** `substrateRatio` is DEFINED as `d2At/(N+1)²`, so substituting
`d2At = substrateRatio·(N+1)²` cannot fail; what it cannot do is tell you which of the two is stable
as the aperture grows. The paragraph above silently reads `substrateRatio` as the stable one. If
instead `d2At` is the stable one, the ceiling `substrateThreshold·(N+1)²` grows while the moment does
not, and **a bigger aperture IS easier** — which is exactly
`Complete.confinement_of_bounded_substrate`: from `∃ B, ∀ N β, d2At N β ≤ B` it concludes confinement
for all LARGE ENOUGH `N`. That theorem would be pointless if the criterion really were the same at
every extent.

**`Moment.lean` postulates that `⟨d²⟩` is the substrate-intrinsic one**, and says so in prose rather
than as an `axiom` precisely so it can be rejected. The tree's own SU(3) aperture scan
(`research/data/9_1_dat_d2_su3.csv`) measures it at the two couplings available at both extents:

    β = 5.50:  d2(L=6) = 0.23023 ± 0.02138,  d2(L=8) = 0.23089 ± 0.01545   (agree to 0.3%)
    β = 6.00:  d2(L=6) = 0.13835 ± 0.01765,  d2(L=8) = 0.14936 ± 0.00974   (0.55σ)

**At fixed coupling the moment is flat in the aperture**, so `substrateRatio = d2/(N+1)²` FALLS like
`(N+1)^{-2}` and a bigger aperture is easier IN FACT. That is what
`Complete.confinement_of_bounded_substrate` exploits, and it is why that theorem — confinement for all
LARGE ENOUGH `N` — is not vacuous.

⚠ **AN EARLIER VERSION OF THIS NOTE CLAIMED THE DATA REFUTES THE RATIO READING AT `11.5σ`. IT DOES
NOT, AND THE CLAIM IS WITHDRAWN.** The ratio form is an UPPER BOUND — `Complete.confinement_of_growth_bound`
is explicit that the moment "may grow like `c·(N+1)²`", and is "the weakest hypothesis the aperture
argument consumes". A FLAT moment satisfies that bound comfortably; it does not contradict it. The
`11.5σ` was computed against `d2(L=8) = d2(L=6)·64/36` read as a PREDICTION OF EQUALITY, which the
hypothesis never makes.

**And the ratio form is the weaker one for a reason the fixed-coupling data cannot see.** `PAPER.md`
§13: *"Measured in lattice units a correlation length diverges as the spacing goes to zero, so a
hypothesis demanding a strictly bounded lattice moment would ask for more than a continuum limit
supplies."* The growth the ratio form allows is for the CONTINUUM limit, where `β` and `L` move
together — not for the fixed-`β` aperture scan measured above.

**The bar, at every extent.** The unconditional bound is `substrateRatio ≤ 1/4`
(`Substrate.substrateRatio_le_quarter`, attained by `antipodeRead`, so it is the best constant the
read interface supports). The requirement is
`substrateRatio < Complete.substrateThreshold = arccos(3^{−1/4})²/(2π)² ≈ 0.0126877`
(`Complete.confinement_at_of_substrate_sharp`), which is SHARP — equality holds for the point mass at
`θ = arccos(3^{−1/4})`, so no argument reading only the second moment can do better. That is a factor
of about `19.7`, at every extent, and nothing here narrows it.

Use the sharp constant, not `2(1 − 3^{−1/4})/(2π)² ≈ 0.0121669`. The latter is what
`Moment.Read.tension_lt_floor_of_circ_moment` carries, because it goes through `1 − x²/2 ≤ cos x` —
the tangent to `t ↦ cos √t` AT THE ORIGIN, correct only for a read concentrated at zero lag.
`Complete.confinement_at_of_substrate_sharp` takes the tangent at the threshold itself and is 4.3%
more generous. Both are SUFFICIENT thresholds. Do not confuse either with the NECESSARY ceiling
`(1 − 3^{−1/4})/8 ≈ 0.0300` of `Moment.Read.substrate_lt_of_tension_lt_floor`, which runs the other
way — from a sub-floor tension TO a ratio bound — and which additionally requires
`0 < ∑ p_d cos θ_d`, a hypothesis that direction does not come without.

**The hard end is `β → ∞`.** The `∀ β` is unrestricted, and at fixed extent the large-coupling end is
where a correlator would flatten. The flat configuration is refused by the floor: the flat read's
substrate ratio is `1/12 + 1/(6n²)`, above the necessary ceiling `(1 − 3^{−1/4})/8` at every aperture
(`Substrate.flatRead_exceeds_ceiling`).

**But read that theorem's quantifiers before leaning on it.** `Substrate.flatRead` is indexed by
aperture ALONE — it has no coupling parameter — so `flatRead_exceeds_ceiling` is a `∀ k` statement
about a constructed read, and it is NOT a statement about `β → ∞`, at fixed extent or anywhere else.
It shows the floor refuses flatness; it does not show `wilsonCorrAt` becomes flat. `Substrate.lean` is
explicit that nothing of this kind can refute the hypothesis, because the hypothesis is about the
constructed correlation and no family of other reads bears on it. So this is an obstruction to clear,
not a refutation, and clearing it means a statement about the Wilson Gibbs measure at the chosen
extent that no theorem in this tree supplies.

## AN AUDIT OF `Aperture.lean`, BECAUSE ITS TITLE INVITES THE WRONG READING

The paper is titled for the finite aperture and `Aperture.lean` is named for it, so a reader will
assume that file carries the thesis. It does not, and the difference matters:

* **`wilsonCorrAt` and `WilsonBridge.corrClay` appear NOWHERE in that file.** Not in a statement, not
  in a proof. Every declaration there is one of three kinds, and none of them is about the Wilson
  ensemble: over a FREE mode family `{ι : Type*} (s : Finset ι) (P μ : ι → ℂ)` supplied by the caller
  (`finite_sum_margin_bound`, `finite_flow_decays`, `gap_at_finite_F`, `gap_uniform_in_F`,
  `gap_of_confinement`); over a free real family `μ₁ : ℕ → ℝ` or `Δ : ℝ → ℝ`
  (`UniformSpectralMargin`, `uniform_margin_of_intensive_radius`, `no_interior_transition`); or plain
  real analysis (`margin_iff_rate_pos`, `gap_refinement_invariant`). The one concrete theorem,
  `uniform_margin_solvable`, is about `Real.tanh b` at the exactly-solvable point — not Yang–Mills.
* `finite_flow_decays`, `gap_at_finite_F` and `gap_of_confinement` each take the spectral margin as a
  HYPOTHESIS, in three spellings of the same thing: `‖μ k‖ ≤ ρ` with `ρ < 1` supplied separately,
  `‖μ k‖ ≤ exp(-κ)` with `0 < κ`, and `‖m k‖ ≤ exp(-(κ₀ − μ))` with `μ < κ₀`. The margin IS the gap.
  The file's dichotomy — a mode on the unit circle, or a strict margin — is therefore not discharged
  there; there is no dichotomy theorem in the file at all, only the second horn, assumed.
* `no_interior_transition` has NO consumer anywhere in the tree. It is also stated for a single
  `Δ : ℝ → ℝ` with no aperture index, so applied at a fixed extent it yields a constant depending on
  that extent. Supplying the index is `CompactBeta.jointUniform_of_pointwise_of_equicontinuous`, which
  needs equicontinuity UNIFORM IN THE APERTURE — and `CompactBeta` measures what that costs
  (`clay_covariance_constant_not_aperture_uniform`, `profile_to_moment_not_uniformly_lipschitz`).
  Its own verdict on that equicontinuity is that it "is NOT available from anything proved": not that
  a route through clustering exists, but that none does.
* `margin_iff_rate_pos` and `uniform_margin_solvable` have no consumer either. Three of the file's
  eleven declarations are dead.
* `gap_refinement_invariant` is unconditional and used — it is `Real.log_rpow` plus `field_simp`, and
  it closes `a → 0` by an identity. It is not the only used declaration and not the most used:
  `gap_of_confinement` carries the file's traffic by a wide margin, and it is the one that takes the
  margin as a hypothesis.

What this file's construction DOES carry, and what it does not. It carries one EXTENT: the read
`μEven a β` is taken at a single `a : EvenAp`, and `ConfinesAtAnAperture` is the statement that one
extent suffices. It does NOT carry a derived finite MODE COUNT. `ymModelEven` has `Idx := Unit` and
`m β _ := exp(-(κ₀ − μEven a β))` — one mode, and a number defined equal to its own bound, so its
`hread` field is discharged by `le_of_eq`. `Complete.lean` says this of `ymModel` in the same terms,
and it is equally true here.

So the finite mode count is structural in the model rather than proved of the ensemble, and the open
statement that would make it a fact about Yang–Mills is `Complete.WilsonSpectral` — that
`wilsonCorrAt N β` admits a periodic transfer decomposition with nonnegative weights. **At the Clay
extent that is now PROVED**: `SlabQuadratic.wilsonSpectral (hβ : 0 ≤ β) : WilsonSpectral 3 β`,
foundational-only, from link- and site-reflection positivity through `SpectralFour.four_iff`. It
supplies the DECOMPOSITION, not a mode count and not a rate — `SpectralFour.fourRepresentable_const`
shows the constant triple is representable, so the property carries no gap. Neither `Aperture.lean`
nor this file supplies the finite mode count, which remains structural in the model.

## THE FLAGSHIP'S SECOND CLAUSE — A VOLUME LIMIT, NOT A CONTINUUM LIMIT

`fullModelOfConfinement`'s `measure` field is `OSFamily.osFamilyTension βFlag`, not
`WilsonModel.ymFamilyTension`. That one field is the whole content of the flagship's second clause,
so what it says — and what it still does not say — is written out here rather than left to the field
name.

**WHAT IT WAS.** `ymFamilyTension`'s reflected form is `WilsonGauge.QG`, which is

    min (max (sysYM.expect (probHaar G3) (a : ℝ) (O0 ∘ reindex …)) 0) 1

with `sysYM = WilsonHypercubic.sysWilson 3 4 nYM` and `WilsonGauge.nYM = 2`. Three consequences, each
readable off the declaration: the sequence index `a` reaches the object ONLY through `expect`'s
coupling slot, so the sequence was a sequence in the COUPLING; the lattice is the same `2⁴ = 16` sites
at every `a`, so neither the spacing nor the volume ever moved; and the value is clamped into `[0,1]`,
so the temperedness the limit is extracted by was definitional rather than a property of the measure.
`WilsonGauge.QG_eq` further proves `QG j a` does not depend on `j` at all.

**WHAT IT IS.** `OSFamily.osFamilyTension_Q_eq` states the new reflected form exactly:

    (osFamilyTension β).Q j a = WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)

with `OSFamily.extent a = 2a + 2` and `OSFamily.ext_strictMono`. The index is the EXTENT of a
four-dimensional periodic `SU(3)` lattice; the coupling is held fixed at `β` across the whole
sequence; and there is no clamp, because the value IS the connected Wilson plaquette correlation.
`0 ≤ q j` descends from `ReflectionStrong.corrClay_nonneg_even_lag`, a reflection-positivity theorem
at every real coupling on the even lags, and the bound's `B = 4` from
`InfiniteVolume.wilsonCorrConn_abs_le_four`, whose only hypothesis is `3 ≠ 0` and whose constant
carries no extent — which is what a sequence over extents needs. The infrared cutoff is unchanged:
`OSFamily.osFamilyTension_c` is `WilsonModel.cW`, so `WilsonModel.paramsTension` is reused verbatim
and `WilsonRealization.hc` discharges as before.

**SO THE CLAUSE NOW READS:** along a subsequence of extents `2φ(k) + 2 → ∞`, the connected `SU(3)`
Wilson plaquette correlation at FIXED coupling `βFlag` and fixed even separation converges; the limit
is nonnegative, bounded, and invariant under the two group actions.

### WHAT IT IS STILL NOT — read this before calling the clause a continuum limit

**IT IS NOT A CONTINUUM LIMIT, AND NEITHER WAS THE OLD ONE.** Nothing in the family sends the lattice
SPACING to zero. `β` is fixed at `βFlag` for the whole sequence, no asymptotic-scaling relation
`a(β)` appears anywhere in this tree, and the only thing the index moves is the periodic extent. This
is the INFINITE-VOLUME limit at fixed bare coupling — `InfiniteVolume.lean` uses exactly this object
and calls it that. Stated at the strength each actually has: the old clause was a limit in the
COUPLING at fixed volume, the new one is a limit in the VOLUME at fixed coupling, and neither is a
limit in the spacing. What the substitution buys is that the new sequence is a sequence of the genuine
correlation over a diverging volume; what it does not buy is the third limit.

**IT IS SUBSEQUENTIAL, AND IT IS A LIMIT OF NUMBERS.** `Measure.continuum_of_family` is
Bolzano–Weierstrass on a countable product: it extracts a subsequence `φ` and a pointwise limit
`q : J → ℝ`. There is no uniqueness, no measure on `ℝ⁴`, and no reconstruction — `q` is a real-valued
function on an index set, not a Schwinger function. Unchanged by the substitution.

**OS1 AND OS3 ARE STILL EMPTY, FOR THE SAME REASON AS BEFORE.** `OSFamily.actEOS` multiplies `j.1`
and `actPOS` multiplies `j.2.1`; NEITHER touches `j.2.2`, and
`OSFamily.Qos_depends_only_on_the_lag` proves the reflected form reads `j` through `j.2.2` alone. So
the Euclidean and permutation groups act on components the form is independent of, exactly as they do
for `QG`. `Qos` is not constant in `j` — it varies with the lag — but the lag is the one component
these two clauses never move. The repair is to the reflected form, not to the invariances.

**THE BOUND IS DOMINATED BY A CONSTANT WITH NO GAUGE CONTENT, AND IT IS FAR LOOSER THAN THE ONE IN
HAND.** The clause is `|q j| ≤ ⌈c⌉₊ · B`. Only `B = 4` comes from
`wilsonCorrConn_abs_le_four`; the factor `⌈cW⌉₊` comes from `OSFamily.hcount_wOne`, which counts the
FABRICATED single-mode spectrum `WilsonModel.wOne` against the FABRICATED circle read
`WilsonModel.readW` at the `Classical.choose`n aperture `WilsonModel.kW` — nothing in it is about
`SU(3)`, and `kW` is bounded above by nothing in this tree, so `⌈cW⌉₊` is not a nameable number.
Meanwhile `OSFamily.Qos_abs_le_four` already proves the sharp `|Q j a| ≤ 4` at every member of the
family. The published clause is therefore weaker than what the measure supports, and the excess is
carried entirely by the spectrum side. Note also that `B` went from `1` to `4`
(`WilsonModel.family_B` against `OSFamily.osFamilyTension_B`), so on that factor alone the clause is
four times looser than the one `EvenAperture` and `WilsonModel` publish; the `1` was the clamp's own
range, which is why it was smaller.

**`os_gap` IS NOT A STATEMENT ABOUT `SU(3)`.** `Measure.familyOfSortedCount` derives it from
`hsorted` and `hcount`, both facts about `wOne`. The `SU(3)` lattice contributes only `0 < Nmodes a`.
Unchanged from `ymFamilyTension`, and named here because the field sits beside three that ARE about
the measure.

**NON-DEGENERACY IS WEAKER THAN BEFORE — the one thing the substitution costs.**
`GibbsPositive.ymFamilyGauge_Q_pos` proves `0 < Q` at EVERY test configuration for the clamped family,
because a one-point plaquette expectation is strictly positive; a connected correlation at a general
lag is not, and no analogue is available. No consumer of `FullModel.measure` requires `0 < Q` —
`LatticeYMFamily` has no such field and `existence_and_gap_of_wilson` never asks for one — so nothing
breaks, but the family is no longer known to be positive everywhere. What is known is
`OSFamily.Qos_pos_at_lag_zero`: at lag zero the correlation is the plaquette-energy variance, strictly
positive at every real coupling (`PlaqVariance.corrClay_zero_pos`), so the family is not the
identically-zero one — which is what `GibbsPositive`'s positivity was guarding against.

**OS2 AND OS4 ARE ABSENT.** `q` carries OS0, the single-number nonnegativity that stands in for OS2,
and the two empty invariance clauses. It does not carry OS2 as positive semidefiniteness over the
half-space algebra — `Measure.LatticeYMFamily` has no field that could hold it, and the tree's Gram
statements (`OSPositivity`, `ReflectionStrong.wilson_expect_gram_nonneg`) are at finite volume on the
slab and are not composed with this family — and it does not carry OS4 clustering.

### WHY COMPACTNESS IS PERMITTED, AND WHAT THE FOOTNOTE ACTUALLY SAYS

Jaffe and Witten's problem description (`Quantum Yang–Mills Theory`, Clay Mathematics Institute
Millennium Prize problem statement, footnote 2) is explicit that this method is not on its own enough:

    "one cannot establish the existence of the limit by a weak compactness argument, unless one also
    uses other techniques to establish properties of the limit (such as the existence of a mass gap
    and the axioms)."

So a compactness-extracted limit is a legitimate ROUTE, provided the gap and the axioms are
established OF THE LIMIT. That is the standard the eventual construction has to meet, and it is
recorded here so the next reader does not read `continuum_of_family`'s Bolzano–Weierstrass as a defect
in itself.

READ THE SCOPE BEFORE LEANING ON IT, because the footnote is about a bigger object than this one. The
limit JW are discussing is the continuum quantum field theory; `q` is a pointwise limit of bounded
real sequences on an index set. The footnote therefore neither permits nor forbids anything about `q`
as such — what it does is name the two conditions (`the gap of the limit`, `the axioms of the limit`)
that any such extraction eventually has to be paired with. Measured against those: the flagship's
first clause establishes a gap of `ymModelEven`'s constructed one-mode spectrum, NOT of `q`, and the
two are nowhere composed — `FullModel`'s own docstring records that `Δ` is a rate at one spacing —
and of the axioms, the bullets above say which `q` carries and which it does not. The footnote's
proviso is NOT discharged here.

## Provenance

Every declaration below is `EvenAperture`'s, transcribed against `ConfinesAtAnAperture` in place of
the substrate bound. No proof is new and no numeral is introduced. `#print axioms` after every
declaration; the gap side reports the foundational three and no named axiom, exactly as
`EvenAperture`'s does, because `readEven` is built from the PROVED reflection positivity.
-/

namespace MassGap.ApertureRoute

open Filter
open MassGap.EvenAperture

/-! ## 1. The hypothesis, named

The whole point of this file is that this `Prop` — and not the substrate bound — is what the flagship
consumes. Stating it separately is what makes that visible. -/

/-- The cosine average of the clamped read — the scalar the tension is the negative logarithm of.
`Complete.cosAvgYMAt` with `readEven` in place of `readYMAt`. -/
noncomputable def cosAvgEven (a : EvenAp) (β : ℝ) : ℝ :=
  ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)

#print axioms cosAvgEven

/-- **CONFINEMENT AT ONE APERTURE.** There is an even extent of at least four at which the read's
cosine average stays STRICTLY ABOVE THE ENTROPY FLOOR `3^{−1/4} = e^{−κ₀}` at every coupling.

This is A1 (`Apriori.A1`) at a single aperture, with the aperture existentially quantified OUTSIDE the
coupling quantifier. The order is what makes it weaker than the substrate bound: one extent has to
work, not all of them.

**WHY THIS IS STATED ON `⟨cos θ⟩` AND NOT ON THE TENSION — READ THIS BEFORE "SIMPLIFYING" IT.**

The obvious spelling is `∀ β, μEven a β < κ₀YM`, and it is WRONG. `Moment.Read.tension` is
`- Real.log (∑ d, p d * cos (θ d))`, and Mathlib's `Real.log` is EVEN (`Real.log_abs`,
`Real.log_neg_eq_log`): it takes the logarithm of the ABSOLUTE VALUE, so `log (-1) = log 1 = 0`. A
read whose cosine average is `−1` — total anticorrelation, no decay whatever — therefore has tension
exactly `0`, which is below `κ₀YM`, and would SATISFY the bare form.

This is not hypothetical. `Substrate.antipodeRead k` puts all its mass at the antipode, where
`θ = π` and `⟨cos θ⟩ = −1` exactly. It is the very read the tree exhibits to show the `1/4` constant
cannot be improved (`Substrate.antipodeRead_moment_eq_quarter_sq`) and that reflection positivity
alone leaves the substrate moment unbounded (`Substrate.rp_alone_leaves_moment_unbounded`). So the
read that MAXIMALLY VIOLATES the sufficient moment condition would PASS an unguarded tension
condition. `unguarded_confinement_is_satisfiable_without_decay` below exhibits the phenomenon in this
file so that it cannot be re-weakened by accident; `ReadLayer` machine-checks it for `antipodeRead`
itself at every aperture.

The guard is the tree's own. `Moment.Read.cosAvg_gt_of_tension_lt_floor` carries the hypothesis
`0 < ∑ d, p d * cos (θ d)` with the comment that "a nonpositive average has no logarithm and the
tension is not a read". Dropping it was the defect; this definition restores it.

**WHY THE SHARP FORM RATHER THAN THE CONJUNCTION.** `0 < ⟨cos θ⟩ ∧ μ < κ₀` and `3^{−1/4} < ⟨cos θ⟩`
are EQUIVALENT (`confines_iff_pos_and_tension_lt_floor` below, from the tree's two bridging lemmas),
so nothing is strengthened by choosing the second. It is chosen because it is one inequality rather
than a conjunction, and because it is exactly the intermediate the substrate route already derives
on its way to the tension bound — so `confinement_at_an_aperture_of_substrate` proves it directly
instead of proving a weaker thing and then re-deriving the guard.

DERIVED: no numeral. `EvenAp` carries `4 ≤ N + 1` and `Even (N + 1)`, both read off
`Complete.wilson_reflection_positive_at_even`'s hypotheses; `3^{−1/4} = e^{−κ₀}` with `κ₀YM = ¼log3`
counted off directed cube paths in `Floor.lean`. -/
def ConfinesAtAnAperture : Prop :=
  ∃ a : EvenAp, ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β

#print axioms ConfinesAtAnAperture

/-- The aperture the hypothesis supplies. As in `EvenAperture.apertureEven`, no value is named — it
is `Classical.choose`n from the hypothesis's own witness. -/
noncomputable def apertureOf (hc : ConfinesAtAnAperture) : EvenAp := hc.choose

#print axioms apertureOf

/-- That aperture's read clears the floor at every coupling. -/
theorem apertureOf_cosAvg (hc : ConfinesAtAnAperture) :
    ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven (apertureOf hc) β := hc.choose_spec

#print axioms apertureOf_cosAvg

/-- **And therefore confines**: the tension at that aperture is below the counting floor at every
coupling. `Moment.Read.tension_lt_floor_of_cosAvg`, which is the guarded direction — it reads the
logarithm only where its argument is positive. This is the `A1_YM` field of the model below. -/
theorem apertureOf_confines (hc : ConfinesAtAnAperture) :
    ∀ β : ℝ, μEven (apertureOf hc) β < MassGap.κ₀YM :=
  fun β => (readEven (apertureOf hc) β).tension_lt_floor_of_cosAvg (hc.choose_spec β)

#print axioms apertureOf_confines

/-- **THE GUARD IS EXACTLY THE MISSING POSITIVITY.** Clearing the floor is equivalent to the
conjunction of the positivity `Moment.Read.cosAvg_gt_of_tension_lt_floor` requires and the tension
bound the flagship consumes. Both directions, so the choice of spelling is a statement rather than a
preference.

Forward is `tension_lt_floor_of_cosAvg` plus `0 < 3^{−1/4}`; backward is
`cosAvg_gt_of_tension_lt_floor`, whose positivity hypothesis is the conjunct. -/
theorem confines_iff_pos_and_tension_lt_floor (a : EvenAp) (β : ℝ) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β
      ↔ (0 < cosAvgEven a β ∧ μEven a β < MassGap.κ₀YM) := by
  constructor
  · intro h
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    exact ⟨lt_trans h3 h, (readEven a β).tension_lt_floor_of_cosAvg h⟩
  · rintro ⟨hpos, htens⟩
    exact (readEven a β).cosAvg_gt_of_tension_lt_floor hpos htens

#print axioms confines_iff_pos_and_tension_lt_floor

/-! ## 2. The model, the full model, and the realisation

`EvenAperture.fullModelEven` and `EvenAperture.wilsonEven`, with `apertureOf hc` in place of
`apertureEven h`. `ymModelEven` and `A2_even` are reused verbatim — neither ever mentioned the
substrate bound. -/

/-- **The coupling the flagship's measure family is read at.**

`OSFamily.osFamilyTension` holds ONE coupling fixed across the sequence of extents — that is the third
of its three repairs, that the index is the geometry and never `expect`'s coupling slot — and a
`FullModel` carries a single `LatticeYMFamily` with no coupling quantifier, so a value has to be
named.

CHOSEN: `1` decides nothing that is concluded. Every clause of the family is proved at EVERY real
coupling — `OSFamily.Qos_nonneg`, `Qos_abs_le_four`, `Qos_actE` and `Qos_actP` are each `∀ β` — and
`OSFamily.os_continuum_tension` states this file's entire continuum clause at an arbitrary `β`, so
nothing below depends on the value. What it does fix is WHICH coupling's correlation the limit `q` is
a limit of, and the one value the tree can rule out on a theorem is `0`:
`PowerTail.corrClay_at_zero_coupling` proves the connected correlation VANISHES at every nonzero lag
at `β = 0`, so at that value `q` would be the zero function except at lag zero. `1` is a value at
which no such collapse is proved; it is NOT claimed to be physically distinguished, and in particular
it is deep in the strong-coupling region rather than near the couplings a continuum study would use.
Nothing here depends on that, because nothing here depends on the value. -/
noncomputable def βFlag : ℝ := 1

#print axioms βFlag

/-- **A FULL MODEL FROM CONFINEMENT AT ONE APERTURE.** `EvenAperture.fullModelEven` with the
confinement witness supplying the aperture directly instead of the substrate bound supplying it
through `exists_confining_even_aperture`, and with `OSFamily.osFamilyTension βFlag` on the measure
side in place of `WilsonModel.ymFamilyTension`. The module docstring sets out what that second change
does to the continuum clause; the short form is that the sequence index becomes the lattice EXTENT
instead of the coupling, the volume diverges, and the clamp is gone.

DERIVED: no numeral of this declaration's; `βFlag` carries its own note and every other constant
belongs to the pieces assembled. -/
noncomputable def fullModelOfConfinement (hc : ConfinesAtAnAperture) : MassGap.FullModel where
  gap := ymModelEven (apertureOf hc)
  h1 := apertureOf_confines hc
  h2 := A2_even (apertureOf hc)
  measure := MassGap.OSFamily.osFamilyTension βFlag

#print axioms fullModelOfConfinement

/-- **The measure side takes no hypothesis**, as before: `fullModelOfConfinement`'s family is the
closed term `OSFamily.osFamilyTension βFlag`, by `rfl`. Weakening the gap-side hypothesis does not
restrict, weaken or re-derive the continuum half — `hc` does not reach this field. -/
theorem measure_is_osFamilyTension (hc : ConfinesAtAnAperture) :
    (fullModelOfConfinement hc).measure = MassGap.OSFamily.osFamilyTension βFlag := rfl

#print axioms measure_is_osFamilyTension

/-- **WHAT THE FLAGSHIP'S LIMIT IS TAKEN OF, at the declaration level.** The reflected form the
continuum clause converges is `WilsonBridge.corrClay` — the connected `SU(3)` Wilson plaquette
correlation on the four-dimensional periodic lattice — at extent `2a + 2` and coupling `βFlag`. No
clamp, and the index is the geometry.

DERIVED: no numeral of this declaration's; `OSFamily.extent` and `OSFamily.lagOf` carry their own. -/
theorem measure_Q_eq (hc : ConfinesAtAnAperture) (j : MassGap.OSFamily.JOS) (a : ℕ) :
    (fullModelOfConfinement hc).measure.Q j a
      = MassGap.WilsonBridge.corrClay (MassGap.OSFamily.extent a) βFlag
          (MassGap.OSFamily.lagOf a j.2.2) :=
  MassGap.OSFamily.osFamilyTension_Q_eq βFlag j a

#print axioms measure_Q_eq

/-- **The volume genuinely diverges along the flagship's sequence.** The family's mode count is the
extent-`(2a+2)` lattice's own plaquette count, and it tends to infinity.

READ THIS FOR WHAT IT IS. `Na` is INERT in the family's content — `WilsonModel.resolvedDim_wOne`
returns `1` at every positive count and `count_le_of_tension_uniform`'s bound contains no `Na`, so
substituting `WilsonGauge.NaG a = a + 1` here would give the identical family. What makes `a → ∞` the
infinite-volume limit is `OSFamily.extent` inside the reflected form (`measure_Q_eq`), not this field.
This theorem says the field is now the lattice's honest cardinality rather than a counter; it is not
evidence that the sequence is a volume sequence, and `measure_Q_eq` is.

DERIVED: no numeral of this declaration's. -/
theorem measure_Na_tendsto (hc : ConfinesAtAnAperture) :
    Tendsto (fun a : ℕ => (((fullModelOfConfinement hc).measure.Na a : ℕ) : ℝ)) atTop atTop :=
  MassGap.OSFamily.Nmodes_tendsto_volume

#print axioms measure_Na_tendsto

/-- **The cutoff `WilsonRealization.hc` matches against is still the tension's.** `paramsTension` is
reused unchanged below because this is `rfl`.

DERIVED: no numeral; `WilsonModel.cW` carries its own. -/
theorem measure_c (hc : ConfinesAtAnAperture) :
    (fullModelOfConfinement hc).measure.c = MassGap.WilsonModel.cW := rfl

#print axioms measure_c

/-- **AN `SU(3)` WILSON REALISATION FROM CONFINEMENT AT ONE APERTURE.**
`EvenAperture.wilsonEven`'s transcription. `WilsonModel.paramsTension` is reused unchanged: it reads
its infrared cutoff off the witness read. That cutoff does contain an aperture --
`kstar = 2π·cW` and `cW` carries `rW ^ (kW + 1)` with `kW` a `Classical.choose`n extent
(`WilsonModel.lean:261`) -- but it is a bare `ℕ` on the MEASURE side, fixed by the witness read and
unrelated to the `EvenAp` the gap side quantifies over. So the gap side's aperture, however it is
quantified, does not reach this field.

DERIVED: no numeral of this declaration's; `3` is `SU(3)`'s rank, carried from `paramsTension`. -/
noncomputable def wilsonOfConfinement (hc : ConfinesAtAnAperture) : MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelOfConfinement hc
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

#print axioms wilsonOfConfinement

/-! ## 3. The flagship -/

/-- The flagship's conclusion at the realisation this file builds: the mass gap (`C(τ) → 0`),
non-triviality (`μ − κ < 0`), `SO(4)` invariance (`R` direction-independent), and the tight
OS0–OS3 continuum limit.

Stated in the SHAPE `NonnegArm.Flagship` uses, so the conclusion can be named once and the theorem
below is faithful by type-checking rather than by assertion.

IT IS NO LONGER THE SAME CONCLUSION, and saying so would now be false. `NonnegArm.Flagship h` is
about `wilsonEven h`, whose measure is still `WilsonModel.ymFamilyTension`
(`NonnegArm.measure_is_ymFamilyTension`, by `rfl`). The four measure-half clauses here quantify over a
different `J`, a different `Q`, a different `B` (`4` against `WilsonModel.family_B`'s `1`) and a
different sequence (extents against couplings). The gap-half clauses are unchanged. See the module
docstring's second section for what the difference is.

DERIVED: no magnitude appears anywhere in this statement. Every `0` is a sign or a limit point:
`nhds 0` is the assertion that the correlation TENDS TO zero, which is the mass gap itself and not a
level it is compared against; `μ − κ < 0` is the SIGN of the tension deficit; and `0 ≤ q j` is
nonnegativity of the limit functional, not a floor on it. The `4` is not a numeral of the definition
at all — it is the dimension inside the NAME `SO(4)`, the rotation group of the four-dimensional
hypercubic lattice `WilsonBridge.corrClay` is stated on, carried in rather than chosen here. The
magnitudes that do appear — `c`, `B` — are the measure's own fields, quantified by it. -/
def FlagshipAt (hc : ConfinesAtAnAperture) : Prop :=
  ((∀ β, Tendsto (fun τ : ℕ => ‖∑ k ∈ (wilsonOfConfinement hc).model.gap.s β,
        (wilsonOfConfinement hc).model.gap.P β k
          * ((wilsonOfConfinement hc).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (wilsonOfConfinement hc).model.gap.μ β
          - (wilsonOfConfinement hc).model.gap.κ < 0) ∧
      (∀ d d', (wilsonOfConfinement hc).model.gap.R d
          = (wilsonOfConfinement hc).model.gap.R d')) ∧
    (∃ (q : (wilsonOfConfinement hc).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (wilsonOfConfinement hc).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(wilsonOfConfinement hc).model.measure.c⌉₊ : ℝ)
              * (wilsonOfConfinement hc).model.measure.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((wilsonOfConfinement hc).model.measure.actE g j) = q j) ∧
      (∀ σ j, q ((wilsonOfConfinement hc).model.measure.actP σ j) = q j))

#print axioms FlagshipAt

/-- **THE FLAGSHIP FROM CONFINEMENT AT ONE APERTURE.**

Existence, the mass gap, non-triviality, `SO(4)` invariance and the continuum measure, from
`∃ a : EvenAp, ∀ β, μEven a β < κ₀YM` alone. No moment bound, and no quantifier over apertures.

The proof term is `existence_and_gap_of_wilson` applied to this file's realisation and nothing else,
which is how the statement is known to be the flagship rather than asserted to be. -/
theorem flagship_of_confinement_at_an_aperture (hc : ConfinesAtAnAperture) : FlagshipAt hc :=
  MassGap.existence_and_gap_of_wilson (wilsonOfConfinement hc)

#print axioms flagship_of_confinement_at_an_aperture

/-- **The gap WITH ITS RATE, and the continuum measure.** `EvenAperture.mass_gap_rate_and_continuum_even`
from the same hypothesis: the rate is the entropy surplus `κ₀ − μ` at the chosen aperture. -/
theorem mass_gap_rate_and_continuum_at_an_aperture (hc : ConfinesAtAnAperture) (β : ℝ) :
    (0 < (fullModelOfConfinement hc).gap.κ₀ - (fullModelOfConfinement hc).gap.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ (fullModelOfConfinement hc).gap.s β,
          (fullModelOfConfinement hc).gap.P β k * ((fullModelOfConfinement hc).gap.m β k) ^ τ‖
        ≤ (∑ k ∈ (fullModelOfConfinement hc).gap.s β,
              ‖(fullModelOfConfinement hc).gap.P β k‖)
            * Real.exp (-((fullModelOfConfinement hc).gap.κ₀
                - (fullModelOfConfinement hc).gap.μ β)) ^ τ) ∧
      (∃ (q : (fullModelOfConfinement hc).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (fullModelOfConfinement hc).measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(fullModelOfConfinement hc).measure.c⌉₊ : ℝ)
                * (fullModelOfConfinement hc).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((fullModelOfConfinement hc).measure.actE g j) = q j) ∧
        (∀ σ j, q ((fullModelOfConfinement hc).measure.actP σ j) = q j)) :=
  MassGap.mass_gap_rate_and_continuum (fullModelOfConfinement hc) β

#print axioms mass_gap_rate_and_continuum_at_an_aperture

/-! ## 4. The new hypothesis is WEAKER than the old one

One direction, and only one. -/

/-- **THE OLD HYPOTHESIS GIVES THE NEW ONE.** `EvenAperture.exists_confining_even_aperture`, restated
as the implication between the two hypotheses so the ordering between them is a statement rather than
a remark. The substrate bound's aperture quantifier is spent here, choosing the aperture, and is not
used again.

**NO CONVERSE IS CLAIMED.** `ConfinesAtAnAperture` is about one extent; the substrate bound is about
all of them, and a witness for the first constrains no other extent.

**THE SUBSTRATE ROUTE SUPPLIES THE GUARD**, so restoring it costs nothing here. This is
`EvenAperture.exists_confining_even_aperture`'s proof with the conclusion taken one step earlier:
that proof reaches the tension bound through `Moment.Read.tension_lt_floor_of_circ_moment`, whose own
argument establishes `3^{−1/4} < ⟨cos θ⟩` as an INTERMEDIATE and then discards it. Here it is the
conclusion. The ingredients are `Moment.Read.cos_avg_ge_circ` (the quadratic lower bound on the
cosine average in terms of the circular second moment) and the aperture factor going to zero, exactly
as before — no new input, and in particular the positivity is not an extra assumption. -/
theorem confinement_at_an_aperture_of_substrate
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) : ConfinesAtAnAperture := by
  obtain ⟨B, hB⟩ := h
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  obtain ⟨a, ha⟩ := exists_evenAp_of_eventually hev
  refine ⟨a, fun β => ?_⟩
  have hd2 : d2Even a β
      = ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 := rfl
  have hmul : (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2
        * (∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2)
      ≤ (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2 * B := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← hd2]; exact hB a β
  have hge := (readEven a β).cos_avg_ge_circ
  show (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)
  linarith

#print axioms confinement_at_an_aperture_of_substrate

/-- **The flagship from the substrate bound, through the weaker hypothesis.** Composing the two
results above recovers `EvenAperture`'s conclusion, which is the check that nothing was lost in
weakening the hypothesis: everything the old route concluded is still concluded, from strictly less. -/
theorem flagship_of_substrate_even_via_aperture
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    FlagshipAt (confinement_at_an_aperture_of_substrate h) :=
  flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_substrate_even_via_aperture

/-! ### The guard costs the definitional identity with `NonnegArm.Flagship`, and that is benign

Before the guard, `FlagshipAt (confinement_at_an_aperture_of_substrate h)` was `NonnegArm.Flagship h`
by `Iff.rfl`: both realisations were built at `(exists_confining_even_aperture h).choose`, literally
the same term.

With the guard that is gone, and necessarily. `ConfinesAtAnAperture` is now a DIFFERENT existential —
over `3^{−1/4} < cosAvgEven a β` rather than over `μEven a β < κ₀YM` — so `apertureOf` draws its
witness by `Classical.choose` from a different proposition, and the two constructions need not pick
the same extent. Nothing is weakened by this: both are the flagship, each at its own chosen aperture.
It is the witness that differs, not the conclusion's content.

AND THERE IS NOW A SECOND, LARGER REASON, so this paragraph is not the whole account. The measure
field of `fullModelOfConfinement` is `OSFamily.osFamilyTension βFlag` while `NonnegArm.wilsonEven`'s
is still `WilsonModel.ymFamilyTension`, so the two propositions differ in the measure half's `J`, `Q`,
`B` and sequence — not only in which aperture `Classical.choose` picked. The earlier sentence "it is
the witness that differs, not the conclusion's content" was true before that change and is not true
now.

The substantive recovery therefore stands as `flagship_of_substrate_even_via_aperture` above — from
the substrate bound, the full flagship — and it is a theorem rather than an identity. What is NOT
claimed, and what would be false to claim, is that the two are the same proposition. -/

/-- **The guarded hypothesis implies the unguarded one.** The guard only restricts: any aperture
clearing the floor also has tension below it. Stated so the ordering between the two spellings is
machine-checked, and so the defect cannot be reintroduced by "generalising" back.

The converse fails, and `unguarded_confinement_is_satisfiable_without_decay` is why. -/
theorem unguarded_of_confinesAtAnAperture (hc : ConfinesAtAnAperture) :
    ∃ a : EvenAp, ∀ β : ℝ, μEven a β < MassGap.κ₀YM :=
  ⟨apertureOf hc, apertureOf_confines hc⟩

#print axioms unguarded_of_confinesAtAnAperture

/-! ## 5. The remaining obligation, stated at one aperture

`NonnegArm.existence_and_gap_of_law_above_cut` reduces the Clay statement to `LawAbove b` — the
contact-relative quartic law above a cut — by discharging the `[0, b]` arm from
`ContactFloor.contact_relative_unconditional`. That composition is reused verbatim here; the only
change is that it now lands on `ConfinesAtAnAperture`, so the reduction's target is visible at one
aperture. -/

/-- **THE OBLIGATION, AT ONE APERTURE.** There is a `b > 0` such that the contact-relative quartic law
on `(b, ∞)` alone yields confinement at a single even aperture, and with it the gap, non-triviality,
`SO(4)` invariance and the continuum measure.

The `[0, b]` arm is not assumed: it is discharged inside the proof by
`ContactFloor.contact_relative_unconditional`, carried out of `NonnegArm.lawBelow_holds`. `b` is not
named and not chosen; it is that theorem's own cut.

This proves nothing new about Yang–Mills. `LawAbove b` is still the sufficient input, unchanged. What
has changed is what it is sufficient FOR: the intermediate target is now confinement at one extent
rather than a moment bound at every extent, so a route that reaches the intermediate target without
going through the power law no longer has to be aperture-uniform. -/
theorem confinement_at_an_aperture_of_law_above_cut :
    ∃ b : ℝ, 0 < b ∧ (MassGap.NonnegArm.LawAbove b →
      ∃ hc : ConfinesAtAnAperture, FlagshipAt hc) := by
  obtain ⟨b, hbpos, hbelow⟩ := MassGap.NonnegArm.lawBelow_holds
  refine ⟨b, hbpos, fun habove => ?_⟩
  exact ⟨confinement_at_an_aperture_of_substrate
      (MassGap.NonnegArm.substrate_even_of_two_arm b hbelow habove),
    flagship_of_confinement_at_an_aperture _⟩

#print axioms confinement_at_an_aperture_of_law_above_cut

/-! ## 6. NON-VACUITY

`ConfinesAtAnAperture` quantifies over `EvenAp`, so it is not a quantification over nothing: the
extent-four aperture `EvenAperture.apFour` inhabits it. The hypothesis is therefore a statement about
a nonempty set of apertures, which is what makes the existential meaningful rather than trivially
unsatisfiable. -/

/-- `EvenAp` is inhabited, so `ConfinesAtAnAperture`'s existential ranges over a nonempty type.
`EvenAperture.evenAp_nonempty`, restated where the hypothesis is used. -/
theorem evenAp_nonempty : Nonempty EvenAp := MassGap.EvenAperture.evenAp_nonempty

#print axioms evenAp_nonempty

/-! ## 6b. THE NEGATIVE CONTROL: the guard is load-bearing, not decorative

`ConfinesAtAnAperture` is stated on `⟨cos θ⟩` rather than on the tension because `Real.log` is EVEN.
This section proves that the difference is real, on the tree's own read, so that nobody restates the
hypothesis in the "simpler" tension form without first seeing what it admits.

`Substrate.antipodeRead k` is the read the tree already exhibits to show that `1/4` is the best
constant the read interface supports (`antipodeRead_moment_eq_quarter_sq`) and that reflection
positivity alone leaves the substrate moment unbounded (`rp_alone_leaves_moment_unbounded`). All its
mass sits at the antipode, where `θ = π`, so its cosine average is exactly `−1`: total
anticorrelation, no decay of any kind. Its tension is `−log|−1| = 0`, which is below `κ₀YM`.

**So the read that maximally violates the sufficient moment condition passes the unguarded tension
condition, and fails the guarded one.** That is the whole content of the guard. -/

/-- The antipode sits at angle `π`: `θ = 2π(k+1)/(2k+2) = π`, half the period by construction. -/
theorem antipodeRead_theta_eq_pi (k : ℕ) :
    (MassGap.Substrate.antipodeRead k).θ (MassGap.Substrate.antipode k) = Real.pi := by
  have hv : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) = k + 1 := rfl
  show 2 * Real.pi * (((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) : ℝ)
      / (((2 * k + 1 : ℕ) : ℝ) + 1) = Real.pi
  rw [hv]
  have hne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  push_cast
  field_simp
  ring

#print axioms antipodeRead_theta_eq_pi

/-- **The antipodal read's cosine average is exactly `−1`.** A point mass at angle `π`. -/
theorem antipodeRead_cosAvg_eq_neg_one (k : ℕ) :
    ∑ d, (MassGap.Substrate.antipodeRead k).p d
        * Real.cos ((MassGap.Substrate.antipodeRead k).θ d) = -1 := by
  have hsum := MassGap.Substrate.antipodeRead_sum k
  have hp : ∀ d, (MassGap.Substrate.antipodeRead k).p d
      = (MassGap.Substrate.antipodeRead k).ρ d := by
    intro d
    show (MassGap.Substrate.antipodeRead k).ρ d
        / (∑ d', (MassGap.Substrate.antipodeRead k).ρ d') = _
    rw [hsum, div_one]
  have hterm : ∀ d : Fin (2 * k + 1 + 1),
      (MassGap.Substrate.antipodeRead k).p d
          * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)
        = if d = MassGap.Substrate.antipode k then
            Real.cos ((MassGap.Substrate.antipodeRead k).θ d) else 0 := by
    intro d
    rw [hp d]
    show (if d = MassGap.Substrate.antipode k then (1 : ℝ) else 0) * _ = _
    split <;> ring
  rw [Finset.sum_congr rfl (fun d _ => hterm d),
    Finset.sum_ite_eq' Finset.univ (MassGap.Substrate.antipode k)
      (fun d => Real.cos ((MassGap.Substrate.antipodeRead k).θ d))]
  simp only [Finset.mem_univ, if_true]
  rw [antipodeRead_theta_eq_pi k, Real.cos_pi]

#print axioms antipodeRead_cosAvg_eq_neg_one

/-- **THE TENSION CRITERION ALONE ADMITS A READ WITH NO DECAY.** At every aperture, the antipodal
read has tension `0 < κ₀YM` — so it satisfies the UNGUARDED form `μ < κ₀YM` — while its cosine
average is `−1`, so it fails `ConfinesAtAnAperture`'s guard.

The tension is `0` because `Real.log` is even: `−log(−1) = −log|−1| = −log 1 = 0`. Nothing about the
read decays; the criterion simply cannot see the sign through the logarithm.

**This is why `ConfinesAtAnAperture` is stated on `⟨cos θ⟩`.** If the hypothesis is ever restated as
`∀ β, μEven a β < κ₀YM`, this read is what it lets in. -/
theorem unguarded_confinement_is_satisfiable_without_decay (k : ℕ) :
    (MassGap.Substrate.antipodeRead k).tension < MassGap.κ₀YM
      ∧ ∑ d, (MassGap.Substrate.antipodeRead k).p d
          * Real.cos ((MassGap.Substrate.antipodeRead k).θ d) = -1
      ∧ ¬ ((3 : ℝ) ^ (-(1 : ℝ) / 4)
            < ∑ d, (MassGap.Substrate.antipodeRead k).p d
                * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)) := by
  have hcos := antipodeRead_cosAvg_eq_neg_one k
  have h0 : (MassGap.Substrate.antipodeRead k).tension = 0 := by
    show - Real.log (∑ d, (MassGap.Substrate.antipodeRead k).p d
      * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)) = 0
    rw [hcos, ← Real.log_abs]
    simp
  refine ⟨by rw [h0]; exact MassGap.κ₀YM_pos, hcos, ?_⟩
  rw [hcos]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  exact not_lt.mpr (by linarith)

#print axioms unguarded_confinement_is_satisfiable_without_decay

/-! ## 7. Footprints -/

section Audit
#print axioms ConfinesAtAnAperture
#print axioms apertureOf
#print axioms apertureOf_confines
#print axioms fullModelOfConfinement
#print axioms measure_is_osFamilyTension
#print axioms measure_Q_eq
#print axioms measure_Na_tendsto
#print axioms measure_c
#print axioms wilsonOfConfinement
#print axioms FlagshipAt
#print axioms flagship_of_confinement_at_an_aperture
#print axioms mass_gap_rate_and_continuum_at_an_aperture
#print axioms confinement_at_an_aperture_of_substrate
#print axioms flagship_of_substrate_even_via_aperture
#print axioms unguarded_of_confinesAtAnAperture
#print axioms confinement_at_an_aperture_of_law_above_cut
#print axioms evenAp_nonempty
#print axioms cosAvgEven
#print axioms confines_iff_pos_and_tension_lt_floor
#print axioms apertureOf_cosAvg
#print axioms antipodeRead_theta_eq_pi
#print axioms antipodeRead_cosAvg_eq_neg_one
#print axioms unguarded_confinement_is_satisfiable_without_decay
end Audit

end MassGap.ApertureRoute
