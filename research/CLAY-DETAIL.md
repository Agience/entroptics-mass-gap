# The Clay proof — detail behind the checklist

Companion to `CLAY-CHECKLIST.md`, which is the working file. This holds the worked-out sections:
the four parts as one statement, the coupling arms, the no-go results and what each one closes,
reconstruction, non-triviality, and the infinite-volume front on `ℤ⁴`.

---

## 0. The statement, and the four parts that deliver it

> Prove that for any compact simple gauge group `G`, a non-trivial quantum Yang–Mills theory exists
> on `ℝ⁴` and has a mass gap `Δ > 0`.

Four parts, each with its own chain:

| part | delivers | status |
|---|---|---|
| **I — the lattice gap** | `μYM β < κ₀YM` at every physical coupling, hence `0 < ΔYM β` | §1–§3: one lag-two ratio bound, at any of three extents |
| **II — the continuum limit** | a limit of the Schwinger functions over spacings, and a gap in physical units | §6: the physical gap follows from Part I's input, `SubstrateArms.exists_physical_gap_uniform_of_lawAbove`; the spacing link remains |
| **III — reconstruction** | a Wightman theory from the Euclidean data | §7: built on the Wilson data, `WilsonOS.wilson_reconstructed_nontrivial` |
| **IV — non-triviality** | an infinite-volume DLR state, normalised and not a point mass | §8: one input, an **eventual** variance floor |

**There are two open inputs, not one, and neither is a constant.**

- **Parts I and II** run from `ApertureRoute.ConfinesAtAnAperture` — confinement at *some* aperture.
  `ApertureRoute.flagship_of_confinement_at_an_aperture` carries it to `FlagshipAt`, and the whole
  chain is foundational-only.

  **Three lag-two obligations reduce to it**, each one real constant `K` below a closed-form
  threshold bounding `ρ(2)` by `K·ρ(0)` at every `β ≥ 0`, at a different extent:

  | extent | obligation | reduction | threshold |
  |---|---|---|---|
  | 4 | `ρ` at `wilsonCorrAt 3` | `LagTwoBound.confines_of_lag_two_ratio` | `lagTwoThreshold` |
  | 6 | `LagTwoSix.LagTwoRatioSix` | `LagTwoSix.confines_of_lagTwoRatioSix` | `lagTwoThresholdSix` |
  | 8 | `LagTwoEight.LagTwoRatioEight` | `LagTwoEight.confines_of_lagTwoRatioEight` | `lagTwoThresholdEight` |

  Every threshold is a closed form and every `K` is existential; nothing here is a chosen number.

  **The three are independent alternatives, not a chain, and they are not ordered by strength.**
  `wilsonCorrAt 3`, `wilsonCorrAt 5` and `wilsonCorrAt 7` are `WilsonBridge.corrClay` at periodic
  extent four, six and eight — three measures on three lattices. Nothing in the tree relates them:
  `LagTwoEight.admissible_at_eight_of_admissible_at_six` looks like a transport but is one
  `lt_trans` on constants, mentioning no correlation function, and
  `LagTwoEight.lagTwoThresholdSix_lt_lagTwoThresholdEight` compares two closed-form reals. A larger
  threshold is a weaker obligation only when the bounded object is held fixed, and it is not, so the
  larger threshold at extent eight does **not** make it the easier target. Discharging any one route
  gives the conclusion — `ConfinesAtAnAperture` is existential over apertures — and says nothing
  about the other two. That is why the capstone takes the interface they share.

  The structural difference behind the different thresholds: at extent four, lag two IS the antipode;
  at six the antipode is lag three and at eight lag four. So the extent-four criterion bounds the
  deepest point of the profile while extent eight bounds a lag a quarter of the way round, with lags
  beyond it. The criteria have different shapes because the lag sits differently in each.

  `ClayAssembly.flagship_of_clayRemaining` reaches the same place from `ClayRemaining`, but that
  structure carries a second field, `I2_clustering`, which the flagship route never reads —
  `lagTwoRatioSix_of_clayRemaining` destructures `I1_lagTwo` alone, and `I2_clustering`'s consumers
  are in `SubstrateArms`. So Parts I and II do **not** need a clustering constant.

  `SubstrateArms.clay_assembly_of_spectral_rate` reaches them from a geometric spectral rate instead.
  That is a **different and stronger** hypothesis standing beside the one the development is
  reducing, so it is not what the assembled claim is built on.
- **Part IV** runs from an **eventual variance floor** for the infinite-volume family — `hvar` in
  `VarianceBridge.clay_nontriviality_of_eventual_variance_floor` (§8). It mentions no torus
  quantity and no region size; the consistency relation it needs is already supplied by
  `WilsonDLR.hcons_specState`.
- **Part III needs neither.** It is unconditional.

Both inputs are statements the instrument can be pointed at, and both are open in the sense that
nothing in the tree yet produces them — not in the sense that some number is missing.

### The lag-two obligation is three coupling arms, and two of them are done

`LagTwoSix.LagTwoRatioSix` asks for one `K` below the threshold bounding `ρ(2)` by `K·ρ(0)` at
**every** `β ≥ 0`. The tree does not attack that half-line whole — it cuts it, and
`FreeFieldLagTwoSix.confines_of_arms_six` is the theorem that reassembles the pieces into
`ConfinesAtAnAperture`.

| range | status | what carries it |
|---|---|---|
| `[0, b]` — strong coupling | **proved** | `LagTwoSix.exists_cut_lag_two_ratio_six`, which produces a positive cut `b` for **every** `K > 0` |
| `(b, B)` — the intermediate window | **open** | nothing is aimed at it; `MiddleIntervalLagTwoSix K B` states the whole of `[0, B]` |
| `[B, ∞)` — weak coupling | **open, and not reduced** | `FreeFieldLagTwoSix.effective_lag_two_bound_six` derives it from `EffectiveGaussianLagTwoSix ε`, which asks for the conclusion and more — see below |

**The small-coupling arm is a real decay argument, not a shape fact.** It runs through
`StrongCoupling.coreRate` and `StrongArm.exists_strong_arm_cut` — it reads the measure. This matters
given the no-go results above: it is the one place in the chain where something already does the
thing those results say must be done.

**The weak-coupling arm is a restatement, not a reduction.** `lagTwoConstantSix ε` is by definition
`((1+ε)/(1−ε))·(fsCorr6 2 / fsCorr6 0)²`, and `FreeFieldLagTwo.two_lag_form_collapses` proves

> `(∃ R > 0, r₂ ≤ (1+ε)(R·s₂²) ∧ (1−ε)(R·s₀²) ≤ r₀)  ↔  r₂ ≤ ((1+ε)/(1−ε))·(s₂/s₀)²·r₀`

so at `s₂ = fsCorr6 2`, `s₀ = fsCorr6 0` the right-hand side **is** `ρ(2) ≤ lagTwoConstantSix ε · ρ(0)`,
verbatim the conclusion of `effective_lag_two_bound_six`. The band's lag-0 and lag-2 constraints,
with the free scale eliminated, are exactly the thing they are used to derive; the lag-1 and lag-3
constraints are surplus to that derivation, which reads only lag 2 and the lower bound at lag 0.

**So the Gaussian band does not make the far-field obligation smaller — it presents it, and asks for
more besides.** A prover should target `ρ(2) ≤ lagTwoConstantSix ε · ρ(0)` for `β ≥ B` directly.

This does not contradict the hazard recorded above. The surplus constraints are what stop the
hypothesis being *written* as its own conclusion — they make it an argument rather than an assumption.
They do not make it easier to establish.

**What the free-field computation does give is the margin.** `EffectiveGaussianLagTwoSix ε` posits that beyond
some coupling `B` the correlation is within a relative band `ε` of a free-field profile at one
positive scale. It is a hypothesis and **no declaration proves it.**

**Two of its six lag bounds are redundant.** Both sides of the band fold at extent six — `fsCorr6_fold`
gives `fsCorr6 4 = fsCorr6 2` and `fsCorr6 5 = fsCorr6 1`, and `circLag 4 = 2`, `circLag 5 = 1` in
`Fin 6`, so `MomentShape.wilsonCorrAt_circLag_congr` identifies the Wilson side too. So
`effectiveGaussianLagTwoSix_of_four_lags` derives the hypothesis from
`EffectiveGaussianLagTwoSixFour`, which asks for the band at lags `0, 1, 2, 3` only: a prover owes
**four** lag bounds, not six. The consumed form is unchanged.

**It cannot be reduced below four by dropping the lags the proof does not read.**
`effective_lag_two_bound_six` uses exactly two constraints — the upper bound at lag `2` and the lower
bound at lag `0`; lags `1` and `3` are never touched. But `FreeFieldLagTwo.two_lag_form_collapses`
proves that with only lags `0` and `2` the existential over the free scale `R` is **equivalent** to the
ratio bound it derives — the lower constraint caps `R`, and that cap is also the witness. Dropping the
unused lags would leave a hypothesis that assumes its own conclusion, and the theorem would still
compile. The lags the proof never reads are exactly what stop it being content-free. The reduction
above is safe for the opposite reason: lags `4` and `5` are not unused but *equal* to `2` and `1`, so
no constraint is lost. What is proved is that it
suffices, with room to spare: `freeRatioSix_eq` evaluates the free-field lag-two ratio exactly to
`34515625 / 67215229081`, `epsMaxSix = 24/25` admits a relative error of 96 %, `inflationSix_le`
bounds `(1+ε)/(1−ε)` by `49` there, and `lagTwoConstantSix_lt_threshold` puts the product below
`lagTwoThresholdSix`. So even a band that wide clears the bar.

**The two open arms are one statement, and `B` is an artifact of the split.**
`FreeFieldLagTwoSix.lagTwoRatioSix_of_above_strongCut` delivers `LagTwoSix.LagTwoRatioSix`
outright from a single hypothesis: the ratio bound on `[strongCutSix hK0, ∞)` — the single cut the
strong arm returns, named by `FreeFieldLagTwoSix.strongCutSix` so the obligation can be stated at
that one real number rather than at every positive one. No `B`, no second arm. Through
`LagTwoSix.confines_of_lagTwoRatioSix` that reaches `ApertureRoute.ConfinesAtAnAperture`, and so
Parts I and II of `VarianceBridge.clay_four_parts`.

**So the whole lattice-gap side of the Clay statement now rests on one inequality**, at one aperture,
above a proved cut: `ρ(2) ≤ K·ρ(0)` for `β ≥ b`, with `K` below the closed-form threshold.

Historically the split was between the window and the weak arm: — couplings too large for the
strong-coupling expansion and too small for the Gaussian band.

`FreeFieldLagTwoSix.lagTwoRatioSix_of_above_strongCut` makes that explicit: it derives
`MiddleIntervalLagTwoSix K B` from a bound on the window alone, handing the prover the
strong-coupling bound on `[0, b]` as a premise to bootstrap from. It is foundational-only and proves
nothing new about the Wilson correlation — it records where the remaining work is, so that whoever
attacks the middle interval does not re-prove the strong arm.

**The window is compact, and at a fixed aperture the correlation is Lipschitz in the coupling with no
hypothesis at all.** `ConfinesZero.wilsonSystem_expect_lipschitz` gives
`|⟨O⟩_x − ⟨O⟩_y| ≤ 4·M·#Plaq·|x − y|` at the general `SU(N)` Wilson system, from
`WilsonAnalytic.cov_bound_extensive` through `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` and the
mean value theorem. The other general Lipschitz bounds — `WilsonAnalytic.expect_lipschitz_local`,
`WilsonAnalytic.expect_lipschitz_summable` — each carry a **clustering hypothesis**, because each
chases a constant that does not grow with the volume; `WilsonAnalytic.expect_lipschitz` has the
extensive constant but only at `sysReal`, a two-plaquette system.

`CompactBeta.clay_covariance_constant_not_aperture_uniform` is why the extensive constant was not
used: it is unbounded over the aperture, so it cannot serve
`CompactBeta.equicontinuousInBeta_of_uniform_lipschitz`, whose constant must work at every aperture.
**That objection does not reach the lag-two window**, which is stated at one aperture, where `#Plaq`
is a number. So the window has a compact domain and an unconditional modulus of continuity, and what
remains missing is a bound on the ratio at the grid points — which no measurement may supply.

The same decomposition exists at extent four (`LagTwoBound.exists_cut_lag_two_ratio`,
`FreeFieldLagTwo`) and the strong arm exists at extent eight
(`LagTwoEight.exists_cut_lag_two_ratio_eight`).

### What the no-go results close, and what they do not

Four declarations in the tree read as refutations. **None of them closes any route.** Each rules out
a class of WITNESS or a class of PROOF, and each says so in its own scope note:

| declaration | what it rules out |
|---|---|
| `LagTwoEight.flat_profile_defeats_every_admissible_K` | a ratio equal to `1` meets no admissible `K` at extent eight — it quantifies over `K` alone and names no correlation function |
| `TailRatio.no_strict_lag_bound_with_contact` | the coupling-uniform shape facts alone (positivity, log-convexity, the bound `4`, contact dominance) imply no ratio bound with factor below `1`, at any of the three thresholds |
| `FlatProfileAllApertures.flat_profile_defeats_the_criterion_at_every_even_aperture` | the same, at **every** even aperture at once: a profile meeting seven shape conjuncts whose `cosAvgEven` still falls below `3^{−1/4}` |
| `ClayAssembly.flat_profile_admits_no_uniform_quartic_constant` | a uniform quartic constant for the `NonnegArm.LawAbove` route — a different route to the same conclusion |

**They are all the same result.** Every one is against an abstract profile satisfying named shape
facts, every one is discharged by the constant profile, and not one of them mentions `wilsonCorrAt`.
`wilsonCorrAt N` satisfies strictly more than any of those hypothesis sets, so none of these
refutes it.

What they establish jointly is the shape of the remaining work:

> **No route can be closed by shape facts alone.** Positivity, symmetry, log-convexity, contact
> dominance and a uniform bound are all satisfied by the constant profile, which fails the criterion
> at every aperture. Each route needs an argument that actually READS the decay of the Wilson
> correlation — and that missing argument is the same missing argument at extent four, six and eight.

This is why the three routes being independent alternatives does not help as much as it looks: they
are three instances of one gap, not three chances at it.

### The four parts as one statement

`VarianceBridge.clay_four_parts` conjoins all four from `ConfinesAtAnAperture` and the variance
floor, and nothing else. `VarianceBridge.clay_four_parts_of_lagTwoRatioEight` is the same statement
instantiated at the extent-eight obligation, so the capstone is reachable from a named lag-two
bound and not only from an abstract confinement.

**`VarianceBridge.clay_four_parts_of_lag_two_above_the_cut` is the smallest form.** It states all four
parts from exactly two hypotheses — the lag-two ratio bound on `[b, ∞)` above the strong cut, and the
eventual variance floor — plus Part III's own lattice data, which is unconditional. Its axiom set is
the three foundational ones plus `os_reconstruction_wightman`, entering through Part III alone.

Where `clay_four_parts` takes `ConfinesAtAnAperture` abstractly — correctly, since three independent
routes supply it — this one records what supplying it costs on the route the development is reducing. It compiles, and its axiom set is the three foundational axioms plus
`os_reconstruction_wightman`, which enters through Part III alone.

`wilson_reflection_positive_at` does **not** appear, although `flagship_of_clayRemaining` reports it.
That theorem's own docstring predicts this: the axiom is inherited from `ClayRemaining`, whose
`I2_clustering` field is stated on `d2At` and so runs through `readYMAt` — the development's only
application of it — while `LagTwoSix.confines_of_lagTwoRatioSix` is foundational-only, so a caller
reaches the conclusion without the axiom. Why applying the theorem drops what printing it reports is
open, and the difference is recorded rather than leaned on.

It proves no new mathematics. What it does is fix what "the whole thing" means, so that the claim has
a single referent the compiler reads: if any link is later weakened so that a part stops following
from those two hypotheses, `clay_four_parts` stops compiling.

A fifth body of work, §9, stands beside Part I: the infinite-volume `ℤ⁴` front, where a full
`Transfer.TransferData` on the half-space algebra is built with every field discharged and no named
axiom.

`Complete.gap_pos_iff_confinement` ties Part I to the gap: `0 < ΔYM β ↔ μYM β < κ₀YM`. The gap **is**
the centre-vortex tension sitting below the entropy floor `κ₀ = ¼·log 3`, and `Floor`, `CubeArea`
and `VortexCount.kappa0_is_the_surface_entropy_density` prove that floor from the directed-surface
count, both factors, with nothing measured.

---

## 1. Part I — the chain

```
NonnegArm.LawAbove b                              the input
NonnegArm.lawBelow_holds                          proved
  │
  ├─ SubstrateArms.substrate_bounded_of_two_arms
  │     ∃ B, ∀ N β, 0 ≤ β → d2At N β ≤ B          the substrate, bounded uniformly in the aperture
  │
  ├─ Complete.confinement_on_of_substrate_bound
  │     ∀ᶠ N in atTop, ∀ β ∈ S, μYMAt N β < κ₀YM  the aperture factor (2π/(N+1))² carries it
  │
  ├─ SubstrateArms.exists_aperture_A1_of_lawAbove
  │     ∃ N, ∀ β, 0 ≤ β → μYMAt N β < κ₀YM        A1's hypothesis, at a named aperture
  │
  ├─ WilsonInstance.gapModelOf_A1                 A1 from the nonnegative half-line
  ├─ WilsonInstance.gapModelOf_A2 = ym_A2_at      proved
  │
  └─ Model.mass_gap_of_model
        clustering at every coupling
        ∧ tension strictly below the entropy floor
        ∧ direction-independent read
```

Every constant in the chain is existential. The aperture is produced by the argument.

**The assembly is itself a theorem.** `SubstrateArms.clay_assembly_of_lawAbove` conjoins three
conclusions under the **same** hypothesis:

1. an aperture at which the model conjunction holds — clustering, tension below the entropy floor at
   every coupling, direction-independence;
2. one positive `c` below the surplus `κ₀YM − μYMAt` at every aperture past `N₀` and every `β ≥ 0`;
3. that same margin at a coupling realising any target the **running** spacing reaches, arbitrarily
   far out.

`SubstrateArms.lattice_gap_and_margin_of_lawAbove` is the same without the third conjunct, kept
because it needs no `AsymptoticScaling` import to state:

```lean
lattice_gap_and_margin_of_lawAbove
  (habove : ∀ b, NonnegArm.LawBelow b → NonnegArm.LawAbove b) … :
  (∃ N, … clustering ∧ tension below the floor ∧ direction-independence …)
  ∧ (∃ c > 0, ∃ N₀, ∀ i β, 0 ≤ β → c ≤ κ₀YM − μYMAt (N₀+i) β)
```

That the two parts share an input was prose before; Lean checks it now, and if a link is weakened so
they stop sharing one, the declaration stops compiling.

Part III is not conjoined there, because it does not depend on the input at all —
`WilsonOS.wilsonOSData` takes no `LawAbove`, no substrate bound and no coupling restriction.

**And the conjunction is not vacuous.** Its left conjunct reads `∃ N, ∀ hfe hgap, …` over a mode
family the caller supplies, so an empty `s β` would make the clustering conclusion a statement about
an empty sum, and a `cf` no aperture admits would leave the inner `∀` unreachable — `cf` is fixed
before `N` is produced, so that is not hypothetical.
`SubstrateArms.capstone_data_exists` exhibits data defeating both **at every aperture**: one mode of
magnitude `exp(−κ₀YM)`, which is below `1` by `Complete.κ₀YM_pos`, with `Δ` and `cf` the constant
`κ₀YM`. `hdom` and `hgap` hold with equality and `hfe` reduces to `0 ≤ μClampAt N β`, which is
`Complete.μYMAt_nonneg` on the physical branch.

---

## 2. What each link gives

| declaration | statement |
|---|---|
| `NonnegArm.lawBelow_holds` | `∃ b > 0, LawBelow b` — the quartic tail law on `[0, b]`, from `ContactFloor.contact_relative_unconditional` |
| `SubstrateArms.substrate_bounded_of_two_arms` | the two arms merged at general aperture: `∃ B, ∀ N β, 0 ≤ β → d2At N β ≤ B` |
| `Complete.confinement_on_of_substrate_bound` | an aperture-uniform substrate bound gives confinement at every sufficiently wide aperture; the aperture condition comes from `Moment.aperture_factor_tendsto_zero` |
| `SubstrateArms.exists_aperture_A1_of_lawAbove` | one aperture `N` with `∀ β ≥ 0, μYMAt N β < κ₀YM` |
| `WilsonInstance.gapModelOf_A1` | `A1_YM` at an arbitrary aperture from the nonnegative half-line; `μClampAt N β = if 0 ≤ β then μYMAt N β else 0` |
| `WilsonInstance.gapModelOf_A2` | `ym_A2_at N`, isotropy |
| `Model.mass_gap_of_model` | `A1_YM M → A2_YM M →` the conjunction, for any `M : LatticeYM` |
| `Complete.gap_pos_iff_confinement` | `0 < ΔYM β ↔ μYM β < κ₀YM` — the gap is the tension below the floor |
| `Moment.Read.tension_lt_floor_of_circ_moment` | a circle-moment bound plus the aperture condition gives `tension < ¼·log 3` |
| `Moment.Read.cos_avg_ge_circ` | `1 − (2π/(N+1))²·⟨d²⟩/2 ≤ ⟨cos θ⟩` |
| `Substrate.substrateRatio_le_quarter` | `substrateRatio ≤ 1/4`, unconditional, every aperture and coupling |
| `Substrate.antipodeRead_moment_eq_quarter_sq` | a `Moment.Read` attaining that bound |

---

## 3. The input

```lean
NonnegArm.LawAbove (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), b < β → 1 ≤ Moment.circLag d →
    wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4
```

A quartic tail on the whitened profile, relative to the contact term, with one constant above the
cut. `C` and `b` are existential; `b` is the cut `lawBelow_holds` supplies.

**The exponent is forced.** `∑ k²·C/kˢ` converges exactly when `s > 3`, and
`ShareEnvelope.cubic_contact_relative_gives_no_bound` settles `s = 3`.

**It is aperture-uniform**, which is the shape `confinement_on_of_substrate_bound` consumes.

**What yields it.** `SubstrateArms.lawAbove_of_geometric_tail`: a geometric lag-decay rate `r < 1`,
uniform in the aperture and in the coupling above the cut, gives `LawAbove` outright —
`StrongArm.exists_geom_quartic_bound` shows a geometric sequence dominates a quartic at every index.

**The input restated as a rate, which is what the instrument measures.** The quartic law is not the
only way in, and it is not the smallest. A periodic spectral representation of the connected read
with rates uniformly below one reaches the same place, through three lemmas that existed and had
never been composed:

| declaration | statement |
|---|---|
| `SubstrateArms.substrate_bound_of_uniform_spectral_rate` | a representation of `p` with all rates `≤ r < 1` and total weight `≤ W` gives `d2At N β ≤ 2(2W)·∑' k²rᵏ` — **a bound containing neither the aperture nor the coupling** |
| `SubstrateArms.confines_of_uniform_spectral_rate` | hence confinement at every sufficiently wide aperture, with no quartic law and no threshold |
| `SubstrateArms.substrate_bound_of_periodic_spectral_rate` | the same from the tree's own `Spectral.PeriodicSpectralForm`, whose representation is of the **unnormalised** correlation; the two differ by the total mass, which `Moment.Read.hpos` keeps positive |
| `SubstrateArms.confines_of_periodic_spectral_rate` | confinement from that form |
| `SubstrateArms.spectral_rate_representation_at_zero_coupling` | the shape is inhabited: at `β = 0` a single mode of rate `0` reproduces the read exactly |

Behind it: `GeometricProfile.profile_geometric_of_periodic_spectral` turns the representation into a
geometric profile and `Moment.circ_moment_le_of_geometric` turns that into a moment bound with no
`N` on the right-hand side.

**And the rate is only needed ABOVE the strong-coupling cut.**
`SubstrateArms.substrate_bound_on_of_uniform_spectral_rate` is relativised to a coupling set, so the
spectral route composes as an arm rather than all-or-nothing:

| declaration | statement |
|---|---|
| `SubstrateArms.substrate_bounded_of_below_arm_and_spectral_rate` | `NonnegArm.LawBelow b` — which `lawBelow_holds` **proves** — paired with a spectral rate on `(b, ∞)` gives `∃ B, ∀ N β ≥ 0, d2At N β ≤ B` |
| `SubstrateArms.confines_of_below_arm_and_spectral_rate` | hence confinement, with the strong arm supplied rather than assumed |

The two branches reach the moment by different routes — a quartic-weight sum below the cut, a
geometric sum above it — so unlike `substrate_bounded_of_two_arms` they are bounded separately and
the maximum serves both. `b ≈ 2.94e−5`, so this is what the open half actually asks for: a rate on
the couplings above that, not a law at every coupling.

**And only at large apertures.**

| declaration | statement |
|---|---|
| `SubstrateArms.substrate_bound_at_of_uniform_spectral_rate` | the reduction at ONE aperture and ONE coupling — its proof reads the representation only where it is bounding, so this is the real core |
| `SubstrateArms.confinement_on_of_eventual_substrate_bound` | `Complete.confinement_on_of_substrate_bound` with the hypothesis weakened to hold eventually: the conclusion was already eventual, because the aperture factor must shrink past the floor first, so the bound at small apertures was never read |
| `SubstrateArms.confines_of_eventual_spectral_rate` | confinement from a spectral rate supplied only at sufficiently wide apertures |

**So the open input carries three relaxations against `LawAbove`:** a spectral **rate** rather than a
quartic tail law; only **above** the strong-coupling cut; only at **sufficiently wide** apertures.
The last two matter because small apertures are where the read is coarsest and the strong arm is
already proved.

**And the assembly runs from that smaller input.**
`SubstrateArms.clay_assembly_of_spectral_rate` takes the rate above the cut and delivers all three:
confinement at every nonnegative coupling, the uniform margin, and the margin in screen units. The
cut is **not a parameter** — `lawBelow_holds` produces it, so the caller supplies only the rate and
never chooses `b`.

All three conclusions come from one substrate bound, and all three consumers already took it. That
is what routing the chain through the substrate bound rather than through `LawAbove` directly
bought: a smaller input reaches the same place with no new plumbing.

**The representation must be off the vacuum.** `Transfer.one_le_of_eigenvalues_le` proves that a
rate bound read over the *full* transfer spectrum forces `r ≥ 1`, because the vacuum is a unit
eigenvector at eigenvalue one, and `PeriodicSpectralForm` carries no field excluding it —
`Substrate.flatSpectral` exhibits the flat profile as a single mode at `lam = 1`. What makes the
hypothesis about something is that `wilsonCorrAt` is the **connected** correlation:
`WilsonBridge.wilsonCorrConn` subtracts the product of the one-plaquette expectations, which is the
vacuum's contribution. `TransferGap.GapAt` is stated on the vacuum complement for the same reason.

`Complete.WilsonSpectral N β` is exactly `Nonempty (PeriodicSpectralForm (N+1) (wilsonCorrAt N β))`,
so `SlabQuadratic.wilsonSpectral` (one aperture, every `β ≥ 0`) and
`Spectral2.wilsonSpectral_at_zero_coupling` (every aperture, `β = 0`) feed this once a rate is
supplied.

**Where it holds already.** `PowerTail.contact_relative_at_zero_coupling` gives the inequality at
`β = 0` with `C = 0`, at every aperture and lag.

**How far the proved arm reaches, as a number.**
`ClayAssembly.coreRate_lt_one_forces_small_beta {K β} (hβ : 0 ≤ β) (h : coreRate K β < 1) : β < 0.12`
holds at every `K`: `(e^{2β} − 1)` is a factor of `coreRate` and the other two factors are at least
`1`. Evaluating `coreRate (16*4)` puts the cut at `b ≈ 2.94e−5`
(`research/code/certify/lag_two_strong_arm_reach.py`), and the measured peak of the observable is at
`β = 2.8`. So `LawBelow` covers a neighbourhood of zero and `LawAbove` carries the rest of the line.

**What a proof of the input uses.** Two facts fix its shape.

*It uses the profile's decay.* `FreeFieldLagTwo.flat_profile_meets_every_uniform_fact` exhibits the
flat `r : Fin 4 → ℝ` satisfying seven coupling-uniform facts — nonnegativity, positive total, circle
symmetry, log-convexity, contact dominance, `LinkGram`'s `r 2 ≤ r 1`, `SlabQuadratic`'s quadratic —
so the argument reads the decay itself, not those seven.

*It is anchored away from `β = 0`.* `PowerTail.wilsonCorrAt_at_zero_coupling N d (1 ≤ circLag d) = 0`:
the zero-coupling read is a point mass at lag `0`. An argument carrying a bound out of `β = 0`
carries that zero with it — `LogDerivNoGo.per_lag_bound_from_zero_forces_vanishing` and
`PowerTail.haar_comparison_forces_vanishing` are the two statements of this, and
`SubstrateArms.exists_blo_ym_confines_on_Ico` is what the point *does* give: confinement,
unconditionally, on `[0, blo)`.

**Why the input is a uniform bound and not a ratio.** There are two ways to meet the aperture
criterion, and their arithmetic is different.

The *ratio* route asks for `substrateRatio N β ≤ c` at **every** aperture with
`(2π)²·c/2 < 1 − 3^{−1/4}`. Those numbers are fixed:

| quantity | what states it | evaluated |
|---|---|---|
| the criterion `(2π)²·c/2 < 1 − 3^{−1/4}` | `Complete.ym_mass_gap_of_ratio`, as its hypothesis | — |
| `0 < 1 − 3^{−1/4}` | `Moment.floor_rhs_pos` | 0.240164 |
| `3^{−1/4} = e^{−κ₀}` | `VolumeRate.cell_ceiling_eq_exp_neg_floor` | 0.759836 |
| the criterion fails at `c = 1/4` | `Substrate.quarter_ratio_fails_aperture_criterion` | threshold 0.012167 |
| `substrateRatio ≤ 1/4`, **sharp** | `Substrate.substrateRatio_le_quarter`, attained by `Substrate.antipodeRead_moment_eq_quarter_sq` | 0.25, 20.6× the threshold |
| the flat read, `(n²+2)/12` | `Substrate.flatRead_moment`, `Substrate.flatRead_exceeds_ceiling` | → 0.083333, 6.9× the threshold |

**The declarations state the conditions symbolically; none of them contains a decimal.**
`quarter_ratio_fails_aperture_criterion` closes by `nlinarith` from `π > 3`, so not even the
threshold appears there. The evaluated column is produced by
`research/code/certify/aperture_criterion_margin.py`, which asserts the two orderings it reports.

The interface's bound cannot be improved, because a read attains it. So no ratio bound available
from the interface meets the criterion, and
`Substrate.substrate_bound_needs_more_than_positivity` states that.

The *uniform* route asks instead for `∃ B, ∀ N β, d2At N β ≤ B` and lets the aperture factor
`(2π/(N+1))²` do the work: it shrinks, so `Moment.aperture_factor_tendsto_zero` clears any `B`
whatever its size, and `Complete.confinement_on_of_substrate_bound` carries no arithmetic side
condition at all. **This is the route the chain takes, and it is why no threshold appears anywhere
in §1.** `LawAbove` is the statement that supplies `B`;
`ContactFloor.contact_relative_unconditional` supplies it on `[0, b]`.

**But the ratio route asks for strictly less, and that is where to aim.** Since
`substrateRatio N β = d2At N β / (N+1)²`, a uniform bound on `d2At` sends the ratio to **zero**,
while the ratio route still admits `d2At` growing like `c·(N+1)²`.

| declaration | statement |
|---|---|
| `SubstrateArms.ratio_eventually_below_of_substrate_bound` | a uniform `d2At` bound clears **any** positive `c` eventually — so route (a) implies route (b) |
| `SubstrateArms.ratio_hypothesis_of_lawAbove` | from `LawAbove`: a `c > 0` that **already satisfies** `(2π)²·c/2 < 1 − 3^{−1/4}`, with `substrateRatio N β ≤ c` at every sufficiently wide aperture and every `β ≥ 0` |

The witness is `c = (1 − 3^{−1/4})/(2π)²`, which makes the condition's left side exactly half its
right, so the strict inequality is `Moment.floor_rhs_pos` and nothing is tuned. Anyone attacking the
open input should target the ratio: it asks for less than `LawAbove` does, and its side condition
now arrives discharged.

---

## 4. Supporting results in the tree

| result | declaration |
|---|---|
| the entropy floor `κ₀ = ¼·log 3`, both factors | `Floor`, `CubeArea`, `VortexCount.kappa0_is_the_surface_entropy_density` |
| the tension vanishes at zero coupling, every aperture | `ConfinesZero.confines_at_zero_coupling` |
| the cosine average is `1` at zero coupling | `ConfinesZero.cosAvgYMAt_at_zero_coupling` |
| the correlation is differentiable in the coupling | `ConfinesZero.differentiable_wilsonCorrAt` |
| the correlation is Lipschitz in the coupling | `ConfinesZero.lipschitz_wilsonCorrAt`, constant `48·card Plaq` |
| the profile sum has a positive floor on a compact range | `ConfinesZero.exists_profile_sum_floor` |
| a Lipschitz modulus for the lag moment | `SubstrateArms.exists_lipschitz_lag_moment` |
| the plaquette variance is positive at every coupling and extent | `PlaqVariance.corrClay_zero_pos` |
| the theory moves with the coupling | `AreaLaw.clay_mean_action_strictAnti`, `clay_not_free` |
| reflection positivity on the even lags at every real coupling | `ReflectionStrong.corrClay_nonneg_even_lag` |
| the infinite-volume DLR family and its consistency relation | `WilsonDLR.specState`, `hcons_specState` |
| non-triviality in the DLR sense from a variance floor | `VarianceBridge.clay_nontriviality_of_eventual_wilson_bridge` |
| a tight subsequential limit of the moment functionals | `Measure.continuum_of_family`, `OSFamily.os_continuum` |
| the two-loop running spacing, checked against `Running`'s coefficients | `AsymptoticScaling.aRun`, `b1_over_two_b0_sq` |
| the reconstructed Hamiltonian's spectrum | `Reconstruction.hamiltonian_mass_gap`, `Complete.ym_reconstructed_gap` |
| finiteness of the gap | `MassFinite.clayMass_eq` |

---

## 5. Scope of the conclusion

`Model.mass_gap_of_model` delivers, for the clamped lattice model:

* clustering — for every coupling the mode sum tends to zero in the separation;
* the tension strictly below the entropy floor at every coupling;
* the directional read independent of direction.

`Complete.gap_pos_iff_confinement` identifies the first two with a positive gap.

### Which gauge group, and in which dimension

The Clay statement asks for **any compact simple gauge group**. The assembled claim does not cover
that, and the three parts do not agree with one another on it:

| part | gauge group | dimension |
|---|---|---|
| I, II — the lattice gap | **`SU(3)` only** | **four**, fixed |
| III — reconstruction | `SU(N)` for any `N ≠ 0` | the slab's own `dsl`, the caller's |
| IV — non-triviality | any compact `G` with the stated instances | — |

Parts I and II are the narrow ones, and the narrowest part governs: `WilsonBridge.corrClay` is
`corrHyper (d := 4) 3 n 0 1 2`, so the colour rank `3` and the spacetime dimension `4` are written
into the definition every lag-two obligation is stated against, not supplied by a caller. Its own
`DERIVED` note records them as the problem's data.

**So `clay_four_parts` is an `SU(3)` statement in four dimensions.** That is the physically intended
case and the Clay problem's own example, so this is a limit of generality rather than a defect — but
the conjunction must not be read as more than it is. Generalising Parts I and II means generalising
`corrClay`, and nothing in the tree does.

## 6. The continuum direction

The objects in place:

| object | what it gives |
|---|---|
| `Measure.continuum_of_family` | a subsequential limit of the moment functionals over extents at fixed coupling, with the bound `|q j| ≤ ⌈c⌉₊·B`, nonnegativity, and invariance under both actions |
| `OSFamily.os_continuum` | that limit on the four-dimensional `SU(3)` correlation |
| `AsymptoticScaling.aRun` | the two-loop running spacing, exponents checked against `Running`'s `b₀`, `b₁` |
| `AsymptoticScaling.AsymptoticScalingAt` | the scaling predicate, proved satisfiable and proved refutable |
| `AsymptoticScaling.fixed_extent_pins_the_spacing` | a lattice mass bounded below forces the spacing bounded below |
| `ScreenedGap.uniform_physical_gap` | `S.κ / S.L ≤ (κ₀ − μ β) / S.spacing i`, a spacing-independent physical gap |
| `WightmanData.os_reconstruction_wightman` | `OSData → WightmanQFTData` |
| `PlaqVariance.corrClay_zero_pos` | a non-vanishing connected correlator on the genuine measure, with a separating witness and an `SU(1)` control |

**The physical gap comes from the same input as the lattice gap.**

```
SubstrateArms.exists_physical_gap_uniform_of_lawAbove
  (∀ b, LawBelow b → LawAbove b)
    → ∃ c > 0, ∃ N₀, ∀ L > 0, ∀ i β, 0 ≤ β →
        c / L ≤ (κ₀YM − μYMAt (N₀+i) β) / (L / (N₀+i+1))
```

The right-hand side is the lattice margin divided by the spacing a screen of fixed physical extent
`L` carries at aperture `N₀+i`, so the bound is the margin **in physical units** and it does not
degrade as the spacing shrinks.

| declaration | statement |
|---|---|
| `SubstrateArms.exists_uniform_cosAvg_floor_of_substrate` | an aperture-uniform bound on the lag moment gives one `γ` above `3^{−1/4}` and one `N₀` past which `γ ≤ cosAvgYMAt (N₀+i) β` — the modulus `Complete.ym_physical_gap_uniform_exact` and `RefinementLaw.confinesAtAnAperture_of_uniform_cosAvg` both consume |
| `SubstrateArms.exists_uniform_margin_of_substrate` | **the content**: one `c > 0` with `c ≤ κ₀YM − μYMAt (N₀+i) β` at every aperture past `N₀` and every `β ≥ 0`. `confinement_on_of_substrate_bound` gives the strict inequality at each aperture separately; a constant below every surplus is a different statement |
| `SubstrateArms.exists_physical_gap_uniform_of_substrate` | that margin divided through by the screen spacing, on `Set.Ici 0`, which is the form `ym_physical_gap_uniform_exact` and `ScreenedGap.uniform_physical_gap` are stated in |
| `SubstrateArms.exists_physical_gap_uniform_of_lawAbove` | the same from `LawAbove`, composing `lawBelow_holds` with `substrate_bounded_of_two_arms` exactly as `exists_aperture_A1_of_lawAbove` does |
| `Complete.surplus_eq_log_cosAvg` | `κ₀ − μYMAt N β = κ₀ + log (cosAvgYMAt N β)`, an identity |
| `ScreenedGap.uniform_physical_gap` | the same bound packaged from a `Screened`, whose `hrate` is the margin at each spacing |
| `ScreenedGap.uniform_physical_gap_pos` | that bound is positive |

The mechanism is the aperture factor. `Moment.Read.cos_avg_ge_circ` floors the cosine average by
`1 − (2π/(N+1))²·⟨d²⟩/2`; with `⟨d²⟩` bounded uniformly, `Moment.aperture_factor_tendsto_zero` sends
the subtracted term to zero, so the average tends to `1` and any `γ` below `1` is eventually a floor
for it. The entropy floor `3^{−1/4} = e^{−κ₀}` is itself below `1`, which is what leaves room for a
`γ` strictly between them.

**The running spacing attains every target, arbitrarily far out.** The screen spacing `L/(N+1)` is a
convention; reading the margin against the renormalisation-group spacing needs a coupling at which
`aRun N β` equals the target, and one now exists.

| declaration | statement |
|---|---|
| `AsymptoticScaling.exp_neg_le_four_div_sq` | `exp(−t) ≤ 4/t²` for `t > 0`, from `Real.add_one_le_exp` at `t/2`, squared |
| `AsymptoticScaling.aRun_le_of_base_ge_one` | the power factor is at most its base once the base passes `1`, since the exponent `51/121` is below `1`; the exponential factor by the line above |
| `AsymptoticScaling.aRun_le_inv_of_base_ge_one` | those collapse to `aRun N β ≤ 352·N²/(3β)` — a plain `1/β` decay at fixed aperture |
| `AsymptoticScaling.continuous_aRun` | `aRun N` is continuous, a nonnegative-exponent rpow of an affine map times an exponential of one |
| `AsymptoticScaling.exists_beta_aRun_lt` | past any coupling and below any positive target there is a coupling with `aRun N β < ε` |
| `AsymptoticScaling.exists_beta_aRun_eq` | **any target `0 < a < aRun N β₁` is attained at some `β ≥ β₁`**, by `intermediate_value_uIcc` |

`β₁` is arbitrary, so the coupling can be demanded as large as wanted — the branch asymptotic
freedom lives on. `AsymptoticScaling.fixed_extent_pins_the_spacing` is why the aperture must grow
too: it shows a lattice mass bounded below forces the spacing bounded below at a **fixed** extent.

All six carry the three foundational axioms and nothing else.

**The margin read against the running spacing.**
`SubstrateArms.physical_gap_at_the_running_spacing` composes the two:

```lean
physical_gap_at_the_running_spacing
  (habove : ∀ b, NonnegArm.LawBelow b → NonnegArm.LawAbove b) :
  ∃ c > 0, ∃ N₀ ≥ 1, ∀ i, ∀ a β₁, 0 ≤ β₁ → 0 < a → a < aRun (N₀+i) β₁ →
    ∃ β ≥ β₁, aRun (N₀+i) β = a ∧ c ≤ κ₀YM − μYMAt (N₀+i) β
```

At every aperture past `N₀`, for every target the running spacing reaches, there is a coupling
realising that target at which the margin is still at least `c` — and `c` depends on none of `i`,
`a` or `β`. Shrinking the spacing does not erode it. That is the continuum direction in
renormalisation-group units rather than in the screen convention.

What remains here is bookkeeping: a spacing field on `LatticeYMFamily` tied to `aRun`, carrying the
screen relation `((aperture i) + 1)·spacing i = L` onto it, so `ScreenedGap.Screened` can be built
from the Wilson data rather than reasoned about alongside it.

---

## 7. Part III — reconstruction

The Euclidean-to-quantum step, and the spectral facts on the quantum side:

| object | what it gives |
|---|---|
| `WightmanData.OSData` | the Euclidean datum: a normed test space, a reflection `theta` with `theta_invol`, a continuous bilinear form `S`, a translation `transl` with `transl_zero`/`transl_add`, and `os1`–`os3` with `os_nontriv` |
| `WightmanData.osData_test_nontrivial` | no subsingleton inhabits the hypothesis |
| `WilsonOS.osDataOfReflForm` | an `OSData` from any `Transfer.ReflForm` on a real module, evaluated on a finite family: `Test` is the coefficient space, `S` the Gram form `gramL`, `os2` the form's `form_nonneg`, `os3` its `form_symm` |
| `WilsonOS.wilsonOSData` | that construction at `ReflectionStrong.wilsonGibbsReflForm` — the Gibbs pairing of the `SU(N)` Wilson measure on the slab algebra, whose `form_nonneg` holds at every real coupling. Foundational axioms only |
| `WilsonOS.wilsonOSData_S` | its Schwinger form is that pairing on the combinations, by `rfl` |
| `WilsonOS.osDataOfReflForm_separates` | two family members with different self-pairings give two different values of `S` — a statement about the **form**, where `osData_test_nontrivial` is about the test space. The separating pair is the caller's |
| `WilsonOS.osDataOfReflForm_constant_of_no_separation` | the other case stated: on a family the form does not separate, `S` carries one number |
| `WilsonOS.wilson_reconstructed_nontrivial` | the Wilson datum through the reconstruction, with both spaces non-zero; footprint is the three foundational axioms plus `os_reconstruction_wightman` |
| `WightmanData.os_reconstruction_wightman` | `OSData → WightmanQFTData` |
| `WightmanData.reconstructed_space_nontrivial` | the reconstructed space is non-zero |
| `WightmanData.reconstructed_vacuum_energy_zero` | the reconstructed vacuum has energy zero |
| `Reconstruction.hamiltonian` | `H = cfc (fun x => −log x) T`, the continuous functional calculus |
| `Reconstruction.hamiltonian_mass_gap` | `spectrum ℝ T ⊆ {1} ∪ [ε, e^{−Δ}]` gives `spectrum ℝ H ⊆ {0} ∪ [Δ, ∞)` |
| `Reconstruction.reconstruct_qm_core` | the same with `H` self-adjoint, `0 ≤ H`, and `0 ∈ spectrum H` |
| `Complete.ym_reconstructed_gap` | that chain at the entropy-floor ceiling `3^{−1/4} = e^{−κ₀}` |
| `GappedTheory.reconstruct_gapped` | the conclusion packaged as a `GappedQuantumTheory` |
| `MassFinite.clayMass_eq` | `sup Δ` is attained and finite, from `Δ ∈ spectrum H` and the containment |
| `GapToOperator.spectrum_opT_subset` | `spectrum ℝ (opT D) ⊆ {1} ∪ [−r, r]` from `GapAt D r`, admitting `0` |
| `TransferGap.GapAt` | `∀ x, form x vac = 0 → form (T x) (T x) ≤ r²·form x x`, the contraction form |
| `GapToOperator.norm_opT_pow_le` | `‖(opT D)^n x‖ ≤ rⁿ·‖x‖` on the vacuum complement |
| `TransferInvertibility.isUnit_of_spectral_hypothesis` | `0 < ε` with the containment gives `IsUnit T` |

`LatticeTranslNoGo` records the arithmetic of the translation field: `transl_eq_id_of_finite_order`
(divisibility of `E4` with a finite-order action), `addHom_to_int_lattice_eq_zero` (an additive hom
`E4 →+ (Fin 4 → ℤ)` is zero), and `os1_holds_of_everything_when_transl_trivial`. An `OSData` carrying
invariance content has a translation group in which the lattice action embeds.

---

## 8. Part IV — non-triviality

| object | what it gives |
|---|---|
| `PlaqVariance.corrClay_zero_pos` | `0 < corrClay (N+1) β 0` at every real coupling and periodic extent, no hypotheses |
| `PlaqVariance.corrClay_zero_eq` | that value is `wilsonCorrConn` of the plaquette observable with itself on the four-dimensional `SU(3)` lattice |
| `PlaqVariance.wilsonCorrConn_self_pos` | the mechanism: two configurations where the observable differs |
| `PlaqVariance.wilsonCorrConn_self_eq_zero_of_trivial` | the `SU(1)` control, exactly zero |
| `InteractingTwoPoint.sysInt_shared_link_two_point` | `∫ tr(hol₀)·tr(hol₁) = ½·tr(C₀C₁)` against a product of marginals that is zero |
| `AreaLaw.clay_mean_action_strictAnti` | `β ↦ ⟨S⟩_β` strictly decreasing on all of `ℝ` |
| `AreaLaw.clay_not_free` | every `β ≠ 0` differs from product Haar |
| `AreaLaw.su_one_mean_action_deriv_zero` | the `SU(1)` control: the derivative is exactly zero |
| `DLRLimit.exists_infinite_volume_gibbs_state_nondegenerate` | a normalised DLR state that is not a point mass, from a variance floor |
| `InfiniteVolume.exists_uniform_contact_floor` | `e^{−128β}·δ₀ ≤ wilsonCorrAt N β 0` at every aperture and `β ≥ 0` |
| `VarianceBridge.clay_nontriviality_of_eventual_wilson_bridge` | the capstone at `WilsonDLR.specCM` / `specState` / `hcons_specState`. **This is Part IV's open input.** It takes `hbridge` at `atTop` — the torus contact value `wilsonCorrAt (ap Λ) β 0` bounded by the DLR state's variance at `Λ`, at large regions — and nothing produces it. `InfiniteVolume.exists_uniform_contact_floor` supplies the floor, so `hbridge` is the only hypothesis not instantiated from the tree |
| `VarianceBridge.clay_nontriviality_of_eventual_variance_floor` | the same without the torus: the caller hands over `c` and the eventual floor directly |
| `ClayNontriviality.clay_nontriviality_of_wilson_bridge` | the same shape with `hbridge` at **every** region. `VarianceBridge.wilson_bridge_hypothesis_unsatisfiable` refutes that hypothesis at the empty region, so this one is vacuously true and is not a route |
| `ClayNontriviality.clay_nontriviality_of_wilson_variance` | the generic form, taking the variance hypothesis directly at every region; conditional, and carrying the same empty-region defect |
| `ClayNontriviality.uniform_variance_floor_exists` | an aperture-uniform floor on `wilsonCorrAt N β 0` — the torus side of the bridge, proved. The `ℤ⁴` side of the comparison is what is absent |

**The size requirement in that input is free.** `hbridge` asks two things at once — that the
infinite-volume variance be *positive*, and that it be *large enough* to clear the torus side. The
second costs nothing:

| declaration | statement |
|---|---|
| `VarianceBridge.variance_smul` | a `DLRLimit.State` is homogeneous, so the variance of `c • f` is `c²` times the variance of `f` |
| `VarianceBridge.bridge_of_uniform_variance_floor` | a positive uniform variance floor `δ`, plus any region-indexed quantity bounded by `M`, gives an observable whose variance clears it everywhere — scale by `√(M/δ)`, which is the requirement `c²δ ≥ M` solved at equality, not a chosen constant |
| `VarianceBridge.wilson_bridge_of_uniform_variance_floor` | the torus side discharged: `InfiniteVolume.wilsonCorrAt_abs_le_four` bounds it by `4` with **no hypothesis at all**, so a positive uniform variance floor alone produces `hbridge`'s conclusion |

All three carry **the three foundational axioms and nothing else** — not even
`wilson_reflection_positive_at`.

So Part IV's open input is no longer a comparison between the torus and `ℤ⁴`. It is a statement about
the infinite-volume state alone: the variance of some observable is bounded below by a positive
constant, uniformly in the region. No size, and no torus quantity in it.

**And that uniform floor cannot hold, so the existing route is vacuous.**

| declaration | statement |
|---|---|
| `VarianceBridge.spec_empty` | at the empty region the specification kernel is a **point evaluation**: `splice ∅ u ω = ω`, so the numerator is `f ω` times the partition function |
| `VarianceBridge.variance_at_empty_eq_zero` | a point evaluation has variance **zero**, for every observable |
| `VarianceBridge.wilson_bridge_hypothesis_unsatisfiable` | `hbridge` is quantified over **every** region; at `∅` it demands a positive number be at most zero, since `PlaqVariance.corrClay_zero_pos` holds at every extent and coupling with no hypotheses |

`ClayNontriviality.clay_nontriviality_of_wilson_bridge` is therefore **vacuously true**. This refutes
the route, not non-triviality — the empty region has no observable to be non-trivial about.

**The repair, and it was one layer down.**
`DLRLimit.exists_infinite_volume_gibbs_state_nondegenerate` reaches its conclusion through
`not_isPointMass_of_uniform_variance`, which takes an `∀ᶠ` hypothesis — and then wraps the caller's
universal one with `Filter.Eventually.of_forall`. The universal quantifier is a strengthening
introduced at that layer and used nowhere. `exists_dlr_state` returns the ultrafilter with
`u ≤ atTop`, so an `atTop`-eventual floor transports by `Filter.Eventually.filter_mono`.

| declaration | statement |
|---|---|
| `VarianceBridge.nondegenerate_of_eventual_variance_floor` | the same conclusion from a floor holding only **eventually** in the region |
| `VarianceBridge.clay_nontriviality_of_eventual_variance_floor` | Part IV at the Wilson objects, with `WilsonDLR.hcons_specState` supplied, so the floor is the only hypothesis not instantiated from the tree |

All of these carry **the three foundational axioms and nothing else**. The conclusion is unchanged;
what changed is that the hypothesis stops mentioning the small regions and so is no longer refuted by
them.

Clay §4 asks for correlations distinguishable from a generalised free field. The object is the
truncated four-point function at separated points. `WilsonBridge.wilsonCorrConnF` gives the connected
form over finsets of plaquettes; `StrongCoupling.wilsonCorrConnObs` gives it for two arbitrary
observables; `ContactValue`'s `SU(3)` Haar moments (`haar_re_chi_zero`, `haar_re_chi_sq`,
`haar_chi_normsq`) are the evaluation method, and `ContactFloor.integral_hol_clay` is general in the
integrand. `PowerTail.integral_prod_hol_factor` gives the factorisation at zero coupling for
arbitrary bounded measurable factors, which fixes the free reference the interacting value is read
against.

---

## 9. The infinite-volume front on `ℤ⁴`

A second carrier of the same physics, on the infinite lattice
`GibbsSpec.IConf (SU N) = (ILink → SU N)` with `ILink = Fin 4 × (Fin 4 → ℤ)`. It is built, and it
carries **no named axiom** — `ReflectionHalfSpace`'s import closure does not reach `MassGap.Complete`.

| object | what it gives |
|---|---|
| `InfiniteReflection.stateReflForm R ν A hinv hpos` | a `Transfer.ReflForm` on any `A : Submodule ℝ C(X, ℝ)`; at `A := HalfSpaceAlgebra.halfSpaceAlg τ p` it is the `ℤ⁴` half-space form |
| `ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto` | its `form_nonneg`, for a limit of Wilson box states, at **every real coupling** |
| `ReflectionHalfSpace.wilson_reflPositive_limit_exists` | the same with no convergence hypothesis, through an ultrafilter |
| `ReflectionHalfSpace.wilson_reflInvariant_of_tendsto` | `IsReflectionInvariant` of the limit state, any coupling, any plane constant |
| `ReflectionHalfSpace.wilson_nu_T_of_tendsto` | translation invariance `∀ f, ν (ishiftObsL τ f) = ν f`, from reflection invariance at two adjacent constants |
| `WilsonTransferReduction.transferData_of_state_facts` | a full `Transfer.TransferData` on `halfSpaceAlg`, **all six own fields discharged** |
| `ReflectionHalfSpace.transferData_T_ne_id_of_rank_two` | its `T` moves an observable, so the shift is realised non-trivially |
| `WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive` | `PositiveTransfer` is exactly odd-plane reflection positivity |
| `ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit` | that positivity at `0 ≤ β` |
| `HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` | the shift has infinite order here, which is what makes a contraction rate meaningful on this carrier |
| `ReflectionHalfSpace.gapAt_of_finite_volume_connected` | a connected two-point bound on `ℤ⁴` boxes gives `TransferGap.GapAt` on the limit state |
| `TransferGap.clustering_sq` | `GapAt D r` gives exponential clustering in `n` |
| `WilsonDLR.specState`, `hcons_specState` | the DLR family and its consistency relation, at every real coupling |
| `WilsonDLR.exists_wilson_infinite_volume_gibbs_measure` | an infinite-volume Gibbs measure, every `N ≠ 0`, every `β` |

**The two links to build here.**

1. **One state.** `atTop` convergence of the interleaved box family `mixCube` to a single `ν`.
   Compactness gives ultrafilter subsequences (`DLRLimit.exists_limit_state`), and
   `ReflectionHalfSpace.eq_empty_of_stable_two_mirrors` shows no finite region is stable under two
   adjacent mirrors, so two families are needed and their limits are to be identified.
   `WilsonTransferReduction.wilson_transferData_of_common_limit` is the form that takes that
   identification as its hypothesis.
2. **Transport.** A statement relating the `ℤ⁴` objects to `wilsonCorrAt` / `WilsonBridge.corrClay`,
   which is what Part I consumes. `gapAt_of_finite_volume_connected` runs finite-`ℤ⁴`-box to
   infinite volume; the correspondence to the finite periodic torus is the piece that makes a rate
   proved here reach the chain in §1.

   **Both limit objects exist; identifying them is the step.** On the torus side,
   `InfiniteVolume.exists_subseq_tendsto_all_lags β` produces `L : ℕ → ℝ` with `|L k| ≤ 4` and a
   strictly monotone `φ` along which `corrLag k β (φ j) → L k` at **every** lag. On the `ℤ⁴` side,
   `DLRLimit.exists_limit_state` produces a state and `WilsonDLR.hcons_specState` its consistency.
   What is missing is the identification of `L` with that state's plaquette-pair correlations —
   boundary-condition independence between the periodic torus and `ℤ⁴` with free boundary.

   **A decay proved only in the limit does not give `LawAbove`.** `LawAbove` quantifies over every
   aperture `N` with ONE constant; a statement about `L` describes the `N → ∞` behaviour along one
   subsequence and carries no finite-`N` uniformity. Whatever is proved on the `ℤ⁴` side has to be
   transported at finite volume, not only in the limit.

The chessboard engine is in place and waiting on geometry: `Transfer.le_of_iterated_schwarz`
(`s k ≤ √(s (k+1))·√M` at every `k`, with `s` bounded, gives `s 0 ≤ M`) and
`Transfer.le_zero_of_halving`, over the single step `Transfer.ReflForm.abs_form_le_sqrt_mul`. What
they consume is the region-splitting that turns one reflection doubling into the next index of `s`.
