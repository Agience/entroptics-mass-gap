# Clay — declarations behind the route

Companion to [CLAY-CHECKLIST.md](CLAY-CHECKLIST.md). The previous pair is in [_archive/2026-09-24-entroptics-mass-gap/](../../_archive/2026-09-24-entroptics-mass-gap/).

## 1. The lattice gap

`ClayCapstone.clay_gap_of_absolute_decay` takes transfer data `D`, the vacuum complement `V`, a
nonempty Rayleigh set, `PositiveTransfer D`, a rate `0 < ρ < 1`, and

    ∀ y ∈ V, ∃ K, ∀ n,  ‖(D.Tq ^ n) y‖ ≤ K · ρⁿ

and returns `opT D` self-adjoint, `spectrum ⊆ {1} ∪ [0, e^(log ρ)]`, `1` the top.

It is built from:

* `SecondEigenvalue.norm_le_of_absolute_iterate_bound` — at a fixed `y ≠ 0`, absolute decay is the
  ratio form at `C = K/‖y‖`, and `SecondEigenvalue.norm_le_of_iterate_bound` washes the constant out
  by dyadic descent to `‖Tq y‖ ≤ ρ‖y‖`;
* `SecondEigenvalue.lambdaTwo_le_of_absolute_iterate_bound` — every vector at once, into `lambdaTwo`;
* `ClayCapstone.bddAbove_rayleighSet_Tq` — boundedness, unconditional;
* `ClayCapstone.clay_gap_of_lambdaTwo` — the spectral conclusion.

`SecondEigenvalue.decaySubmodule T ρ` is the set of vectors whose iterates decay at rate `ρ`, and it
is a submodule: constants add under sums and scale under scalars. So
`SecondEigenvalue.lambdaTwo_le_of_span_decay` needs decay only on a set whose span contains `V`.

## 2. The form is a state pairing

`GaugeInvariantAlgebra.gaugeInv_form_pow`: on the gauge-invariant transfer data,
`form x (Tⁿ x) = ν(θ_{2p} x · shiftⁿ x)`. `TransferGap.form_pow_diag` and
`ClayCapstone.norm_Tq_pow_mk_mul` convert that into `‖Tqⁿ [x]‖`, and
`ClayCapstone.absolute_decay_of_form_decay` completes the step: `form x (T²ⁿ x) ≤ K · r²ⁿ` gives
`‖Tqⁿ [x]‖ ≤ √(max K 0) · rⁿ`. So L3's pairing bound is the hypothesis of §1.

`HalfSpaceAlgebra.halfSpaceAlg` is every continuous function local on a finite set of links in
`HalfSpaceAlgebra.posHalf τ p = {l | p ≤ l.2 τ}`, and `GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg` its
gauge-invariant part. Every vector of the GNS space is the class of such an observable, so the decay
the capstone needs is decay for each of them, with its own constant.

The GNS step for an observable `x` uses:
* `GaugeInvariantAlgebra.iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le` — a plaquette with `p ≤ q.2 τ` is in
  the algebra, through `GaugeInvariantAlgebra.ilinks_mem_posHalf_of_le` and
  `GaugeInvariantAlgebra.le_ishift_apply`;
* `GaugeInvariantAlgebra.state_iterate_shift_eq` — `ν(Sⁿ f) = ν f` from one-step invariance;
* `GaugeInvariantAlgebra.iterate_shift_sub_smul_one` — `Sⁿ(f − c·1) = Sⁿ f − c·1`;
* `GaugeInvariantAlgebra.pairing_eq_connected` — the mean-subtracted pairing is the connected one;
* `TransferAssembly.inner_vacGNS_mk` — `⟪Ω, [x]⟫ = ν(x)`, so a mean-zero observable's class is in the
  vacuum complement.

## 3. The links

**L1 — the state.** `ClayCapstone.exists_dlr_limit_of_free_family` gives a limit of the free box
states along an ultrafilter at every coupling. The full `atTop` limit comes from the box comparison
below: the free box states along `mixCube` are Cauchy on local observables. At that state
`ReflectionHalfSpace.wilson_reflInvariant_of_tendsto`, `ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto`
and `ReflectionHalfSpace.wilson_nu_T_of_tendsto` supply reflection invariance, reflection positivity
and shift invariance, `ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit` supplies
`PositiveTransfer`, and
`ClayCapstone.wilsonGaugeInvMixCubeData` is the gauge-invariant data.

**L2 — the cluster bound.** `StrongCoupling.wilsonCorrConnObs_eq_bridging_sumObs` is the exact
expansion of the connected correlation of two observables local on disjoint link sets and bounded by
`c₁`, `c₂`: the bridging sum of `StrongCoupling.pairTermObs` over `Z²`. Locality gives measurability
(`StrongCoupling.measurable_of_localOnLinks`), the bound gives integrability against every activated
product (`StrongCoupling.integrable_obsFull_mul_wprod`), and each term obeys

    |pairTermObs bd O₁ O₂ β (E, F)|  ≤  2 · c₁ c₂ · (e^{2|β|} − 1)^(|E| + |F|)

(`StrongCoupling.zwFull_abs_le`, `StrongCoupling.pairTermObs_abs_le`).

An observable enters the resummation through an anchor set containing its halo
`StrongCoupling.linkHalo`, the plaquettes whose boundary uses a link of its support. A plaquette
outside a core containing both anchors uses no link of either support, so each term factors into its core times two outside weights
(`StrongCoupling.pairTermObs_eq_core_mul_outside`, `StrongCoupling.pairTermObs_fac_halo`). The
resummation and the core count are stated once for any summand with that factorisation and a per-term
bound `C·(e^{2β} − 1)^(|c.1| + |c.2|)` — `StrongCoupling.bridging_sum_eq_core_sum_of_fac`,
`StrongCoupling.corePairsF_sum_le_of_bound` — with the plaquette-family theorems as their instances.
With touch-connected anchors, a bridging configuration connects them
(`StrongCoupling.reach_halos_of_bridging`), and the remaining non-bridging configurations cancel under
the exchange (`StrongCoupling.nonbridging_sum_eq_zeroObs_of`,
`StrongCoupling.bridging_sumObs_eq_reach_sum`). The result is

    |wilsonCorrConnObs bd O₁ O₂ β|  ≤  coreConstG (2 c₁ c₂) K β u · coreRate K β ^ (k + 2 − u)

for base points more than `k` touch-steps apart (`b ∉ ball bd a k`), touch-connected anchors of total
size `u ≤ k + 2`, and `K ≥ touchDeg bd` with `coreRate K β < 1`
(`StrongCoupling.wilsonCorrConnObs_abs_le_coreConstG_mul_rate_pow`,
`StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball`). For plaquette products the same bound
reads: `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`,
`StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow`, with rate `coreRate K β` and constant
`coreConst K β`, uniform in the volume through the touch degree `K = 64`.

In the `ℤ⁴` box the anchor of an observable on links strictly inside a cube is the set of plaquettes
based in that cube, `BoxCube.cubePlaq`: it contains the halo (`BoxCube.linkHalo_subset_cubePlaq`), it
is touch-connected — plaquettes at one site with a common direction share that direction's link, and
`((i, j), x)` shares `(j, x + eᵢ)` with the plaquettes at `x + eᵢ` leaving along `j`
(`BoxCube.reach_cubePlaq`) — and it has at most `16 (R + 1)⁴` members whatever the box
(`BoxCube.card_cubePlaq_le`). The box state reads `f` through the splice,
`BoxCube.stateFree_connected_eq_wilsonCorrConnObs`, local by `BoxCube.localOnLinks_splice` and bounded
by `‖f‖`, and `BoxCube.stateFree_connected_abs_le_of_cubes` is the box bound:

    |⟨f g⟩ − ⟨f⟩⟨g⟩|_box  ≤  coreConstG (2 ‖f‖ ‖g‖) 64 β U · coreRate 64 β ^ (k + 2 − U),   U = 32 (R + 1)⁴,

for cube bases more than `k` apart along an axis. The right side is free of the box and the boundary
configuration; the hypotheses ask the box to hold both supports and every plaquette of both cubes.

**L1 — the free box states converge.** `FreeLimit.stateFree_eq_meanR`: inside an ambient box, a
sub-box's free state is `BoxCompare.meanR` over the sub-box's plaquettes, because the links outside
integrate out (`FreeLimit.integral_restrict_marginal`) and the restricted Boltzmann weight is the
sub-box's free weight (`FreeLimit.subBoltz_subPlaq`). `FreeLimit.stateFree_cauchy` compares two boxes
along `mixCube` inside their union: the anchor is the cube of plaquettes around the observable's
support (`FreeLimit.exists_cube`), the `k`-ball of its base lies in both boxes once they hold the link
cube of radius `k` (`FreeLimit.mem_iplqAll_of_mem_ball`), and `BoxCompare.meanR_sub_abs_le` bounds the
difference. `FreeLimit.exists_tendsto_stateFree` extends to every continuous observable by density
and identifies the limit with the subsequential one. `FreeLimit.wilson_gaugeInv_mass_gap_lattice`
composes it with `StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling`.

**L1 — two restrictions of one system agree near an observable.** Two restrictions `P`, `P'` of one
Wilson system give Gibbs means of a local `O` (`BoxCompare.meanR_eq_integral`) whose difference is `∑ BoxCompare.diffTerm / (Zr P' · Zr P)`
(`BoxCompare.meanR_sub_eq`), with
`diffTerm (E, F) = zw_{P'}(O, E) zw_P(1, F) − zw_P(O, F) zw_{P'}(1, E)`. Each term factors through the
anchor's component (`BoxCompare.diffTerm_fac`), the sum regroups by core with the two restricted
outside weights, cores inside `P ∩ P'` cancel in pairs under the copy swap
(`BoxCompare.sum_core_inside_eq_zero`), each restricted outside sum is at most
`exp (2β · touchDeg · |span|)` times its partition function (`BoxCompare.outside_div_le`), and the cores
that leave `P ∩ P'` span at least `k + 2` plaquettes (`BoxCompare.coreSpanF_card_ge_of_not_subset`).
`BoxCompare.meanR_sub_abs_le` is the result.

**L3 for every local observable.** `GeneralDecay.nu_connected_shift_abs_le_obs`: the support of `x`
lies strictly inside a cube based at `p − 1` along `τ` (`GeneralDecay.exists_cube_posHalf`); its
reflection at `2p` and its `m`-th translate lie strictly inside two cubes of one larger side, `m + R`
apart along `τ` (`GeneralDecay.ireflLink_coord`, `GeneralDecay.iterate_ishiftLink_coord`), local by
`HalfSpaceAlgebra.isLocalOn_ireflObs` and `GeneralDecay.isLocalOn_iterate_ishiftObsL`; the box holds
both cubes eventually along `mixCube` (`GeneralDecay.eventually_cube_mem_iplqAll`), so
`BoxCube.stateFree_connected_abs_le_of_cubes` bounds the box pairing and
`GaugeInvariantAlgebra.nu_pairing_abs_le_of_eventually` carries it to `ν`.

**The assembly.** `StrongCouplingGap.decay_of_orth`: a vector orthogonal to the vacuum is the class of
an invariant `a` with `ν(a) = 0` (`StrongCouplingGap.inner_vacGNS_mk_gaugeInv`); its form against
`T²ⁿ` is the connected pairing (`GaugeInvariantAlgebra.gaugeInv_form_pow`,
`GaugeInvariantAlgebra.state_iterate_shift_eq`), bounded by `(C/ρᵁ) ρ²ⁿ`
(`StrongCouplingGap.le_div_pow_mul_pow`), and `ClayCapstone.absolute_decay_of_form_decay` gives
`‖Tqⁿ y‖ ≤ K ρⁿ`. `StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling` turns that into
`‖Tq y‖ ≤ ρ‖y‖` (`SecondEigenvalue.norm_le_of_absolute_iterate_bound`), hence the Rayleigh ceiling
`⟪Tq y, y⟫ ≤ ρ‖y‖²` on the vacuum complement, and `ClayCapstone.clay_gap_of_rayleigh` gives the
spectrum. Its inputs are `0 < β`, `coreRate 64 β < 1` and `htend`.

**L3 — box to state.** `GaugeInvariantAlgebra.stateFree_pairing_shift_abs_le` and
`GaugeInvariantAlgebra.stateFree_pairing_shiftObs_abs_le` bound the reflected-shifted pairing in the
box state; `ReflectionHalfSpace.stateFree_symCube_reflection_invariant` gives the box reflection
invariance they take; `GaugeInvariantAlgebra.nu_pairing_abs_le_of_eventually` carries a bound eventually
uniform in the box to `ν`. `GaugeInvariantAlgebra.nu_connected_shift_abs_le` composes them for a
plaquette `q` with `p ≤ q.2 τ`, at the limit of the free boxes along `ReflectionHalfSpace.mixCube`:
along the even members `ReflectionHalfSpace.symCube` the box states are reflection invariant at the
identity boundary (`ReflectionHalfSpace.ireflConf_one`), the plaquette, its mirror and its translate
lie in the box eventually (`ReflectionHalfSpace.eventually_mem_iplqAll_refl_shift`), and the result is

    |ν(θ φ_q · Sᵐ φ_q) − ν(θ φ_q) ν(Sᵐ φ_q)|  ≤  coreConst (16·4) β · coreRate (16·4) βᵏ ,   k < m.


**The vacuum complement is non-zero at `2 ≤ N`.** `PlaneVariance.stateFree_var_iplaqObs_ge`: in every
free box the variance of a plaquette observable is at least `e^{−32β} · varReTr N / N²`. Condition on
every link but the plaquette's first `l₀`; the observable is `g ↦ wilsonDensity(g · W)` with `W` from the
other three links (`PlaneVariance.ihol_eq_head_mul`), and right-invariance of Haar removes `W`
(`PlaneVariance.integral_shift_factor`); the free weight's factor at `l₀` lies in `[e^{−32β}, 1]`, at most
`16` box plaquettes carrying `l₀`, and the rest does not read `l₀`. `PlaneVariance.nu_var_iplaqObs_ge`
carries it to `ν`; `PlaneVariance.exists_ne_zero_orth_vacuum` turns a plaquette in the reflection plane
into a non-zero vector orthogonal to the vacuum. `PlaneVariance.wilson_gaugeInv_mass_gap_lattice_nontrivial`
states the gap, the contraction of every vector orthogonal to the vacuum
(`StrongCouplingGap.norm_Tq_le_of_orth`), and that vector.

## 4. The continuum step

The entroptic step reads the transfer operator. For a vector `v` of the gauge-invariant GNS space at
`ν`, its correlation profile over the lags of an aperture of `N + 1` sites is `d ↦ ⟪v, Tqᵈ v⟫`, a
`Moment.Read`. Its tension below the floor `¼·log 3` bounds the spectral weight near `1`, and with the
aperture at fixed physical extent `L = (N + 1)·a` the rate is at least `κ*/L` at every spacing
(`ZeroMode.rate_gt_of_tension`, `ZeroMode.gap_phys_of_fixed_screen`,
`ScreenedGap.physical_gap_of_tension_at_screen`, `κ* = −2·log(12(1 − 3^(−1/4))/8) ≈ 2.04`).

What carries a read to the operator is the spectral representation `⟪v, Tqᵈ v⟫ = ∫ λᵈ dw_v(λ)`,
`w_v ≥ 0` on `[0, 1]`; `ZeroMode.correlation_gap_of_tension` is its finite-mode form, and
`SpectralRep.exists_moment_measure` is the general one: the functional `f ↦ re ⟪v, f(a) v⟫` of the
continuous functional calculus is positive (`SpectralRep.momentLinear_nonneg`), and its Riesz–Markov
measure has the moments `re ⟪v, aᵈ v⟫`.

The read reaches every vector orthogonal to the vacuum, not one observable. A single profile can
clear the floor while decaying only as a power, `r⁻⁸`, so the step reads all of them: a vector whose
spectral weight sits above `λ₀` has a read that clears the floor only when
`λ₀^{k+1} < 12(1 − 3^{−1/4})/8`, and a ramp `φ(opT)` isolates any weight above that level into such a
vector. The floor is
`exp(−κ₀YM)`, `κ₀YM = ¼·log 3`, from `VortexCount.kappa0_is_the_surface_entropy_density`.

**The chain from the read to the gap is built.** `SpectralGap.gap_of_reads` takes a self-adjoint
operator with spectrum in `[0, 1]` fixing the vacuum and `SpectralGap.ReadsClear` at aperture `2k + 1`,
and gives `‖aᵐ u‖ ≤ ρᵐ‖u‖` on the vacuum complement with `ρ^{k+1} = 12(1 − 3^{−1/4})/8`. The proof: the
spectral measure w_u of `u` (`SpectralRep.exists_spectral_measure`) can carry no mass above
`λ₁ = ρ` — a slice `[λ₁ + 2s, 1]` of positive mass, and the ramp `φ` rising from `0` at `λ₁ + s` to `1`
at `λ₁ + 2s`, make `v = φ(a)u` orthogonal to the vacuum (`SpectralRep.cfc_apply_of_fixed`) with
correlation `∫ φ² λ^c dw_u` (`SpectralRep.inner_cfc_cfc`), and its read below the floor puts
`(λ₁ + s)^{k+1}` under the cap (`SpectralRead.lam0_pow_lt_of_tension`), which `λ₁^{k+1}` already
reaches. With no mass above `λ₁`, `‖aᵐu‖² = ∫ λ^{2m} dw_u ≤ λ₁^{2m}‖u‖²`.
`WilsonReadGap.wilson_gap_of_reads` states it on the `SU(N)` Wilson transfer operator at every `β ≥ 0`,
and `SpectralGap.uniform_physical_gap_of_reads` in physical units at a fixed window: `κ*/L` with
`κ* = −2·log(12(1 − 3^{−1/4})/8) ≈ 2.04`: a lower bound on the physical gap that is one number at
every spacing.

`SpectralGap.ReadsClear` is the gap stated as a read. A vector's cosine average is the average, over
its spectral measure, of the single-mode average `f_k(λ)`, and `f_k(1) = 0`
(`ZeroMode.sum_cos_theta_eq_zero`); so at a fixed aperture the condition holds when the spectrum on
the vacuum complement avoids `{f_k ≤ 3^{−1/4}}`, a neighbourhood of `1`. The single-mode threshold at
fixed physical extent is `≈ 10.99/L` (computed, not proved); the chain returns `2.04/L`. What the read contributes is the
fixed physical window: a condition measured at a window of extent `L` becomes a bound in physical
units that reads no spacing.

**The gap at every coupling.** `ReadRoute.gapAt_of_reads` turns the reads into `TransferGap.GapAt` on any
transfer data with positive transfer; `ReadRoute.wilson_gaugeInv_clay_gap_of_reads` gives the Clay
spectral statement on the Wilson data at any `β ≥ 0`; `ReadRoute.wilson_gaugeInv_mass_gap_every_coupling`
joins it with the cluster expansion below the cut, with the single hypothesis `hweak` above it.
`ContinuumE.readsClear_iff`: the reads are one read per non-zero vector orthogonal to the vacuum,
`ContinuumE.transferRead`.

**The reads bracket the gap at one window.** `ReadConverse.modeCosAvg_antitone`: the single-mode cosine
average `modeCosAvg k t = Σ_d t^{c_d} cos θ_d / Σ_d t^{c_d}` is antitone on `[0, ∞)` — pairwise,
`(cos θ_d − cos θ_{d'})(t^{c_d} s^{c_{d'}} − s^{c_d} t^{c_{d'}}) ≥ 0` for `t ≤ s`
(`ReadConverse.cheb_sum`). A contraction of the vacuum complement at rate `r` confines every spectral
measure to `[0, r]` (`ReadConverse.ae_le_of_contraction`), so every read is a mixture of single-mode
averages at least `modeCosAvg k r`, and `ReadConverse.readsClear_of_contraction` gives the reads when
that exceeds `3^{−1/4}`. At one window of extent `L`, `ReadConverse.readsClear_brackets_physical_gap`
gives both halves: the reads give a physical gap of at least `κ*/L ≈ 2.04/L`, and a physical gap of at
least `20/L` gives the reads; between the two the reads are not decided.

**The reads from finite boxes.** A read's cosine average is at least `γ` exactly when the linear form
`Σ_d (cos θ_d − γ) ρ(d)` is non-negative (`ReadReduce.margin_nonneg_iff`); at a fixed `γ > 3^{−1/4}`
that condition, unlike the reads, is closed under limits, and it gives the reads
(`ReadReduce.readsClear_of_readsClearWith`). On the GNS completion it follows from the same inequality
on the classes of local observables, the vacuum component subtracted
(`ReadReduce.readsClearWith_of_local`); at the Wilson data the profile of a local `x` with `ν(θx) = 0`
is its connected reflected-shift pairing in `ν` (`ReadReduce.wilson_form_pow`,
`ReadReduce.wilson_form_vac`), the limit of the connected box pairings (`ReadReduce.tendsto_boxConn`).
`ReadReduce.wilson_clay_gap_of_boxReads`: under `htend` at `β ≥ 0`, the box inequality with slack, for
every gauge-invariant local observable, gives the reads and the Clay spectral statement; observable by
observable it is exactly the limit-state inequality (`ReadReduce.boxSlack_iff`). It is the reads at a
uniform margin, not a weaker input: at `β ≥ 0` it holds for some `γ > 3^{−1/4}` exactly when the
transfer operator contracts the vacuum complement below the root of `modeCosAvg k r = 3^{−1/4}`
(argued, not proved). The local step reverses exactly (`ReadReduce.boxReads_of_localReads`), and the
hypotheses hold together at `β = 0` (`ReadReduce.boxReadsClearWith_at_zero_coupling`, every `γ ≤ 1`).

**A state at every coupling, from periodic lattices.** A limit of free-boundary box states carries
reflection positivity about one plane only: an ultrafilter sees one parity of the mixed cubes, and a
finite link set stable under the mirrors at `a` and `a + 1` is empty
(`ReflectionHalfSpace.eq_empty_of_stable_two_mirrors`). The Wilson state on a periodic lattice is exactly
shift invariant and reflection invariant at every constant, reflection positive about the site planes
at every `β` (`ReflectionStrong.wilson_expect_nonneg_module`), and about the link planes at `β ≥ 0` and
half-extent at least `2` (`LinkGram.gram_refl_positive`). Read on `ℤ⁴` through
`InfiniteLattice.pullback` (`PeriodicState.pullback_ireflConf`, `PeriodicState.pullback_ishiftConf`),
one ultrafilter limit of the periodic states, `PeriodicState.periodicState`, carries all four facts the
transfer data needs (`PeriodicState.periodicState_reflInvariant`, `PeriodicState.periodicState_shift`,
`PeriodicState.periodicState_reflPositive`, `PeriodicState.periodicState_reflPositive_odd`), and
`PeriodicState.periodic_clay_gap_of_reads` gives the spectral statement from the reads at every
`β ≥ 0`; `periodicState` is not shown to satisfy the DLR equations. The non-zero vacuum complement comes
from a variance floor on every periodic lattice: `ContactFloor.wilsonCorrConn_self_ge_haar` bounds the
variance at `β` below by `e^{−2β·|touch|}` times the Haar variance, the touch count is at most `64`
(`StrongCoupling.touchDeg_bd_le`), and the Haar variance of a plaquette is at least `varReTr N/N²`
(`PeriodicContent.torus_haar_var_ge`); the floor passes to the limit
(`PeriodicContent.periodicState_var_iplaqObs_ge`) and a plane plaquette fixed by the reflection gives the
vector (`PeriodicContent.periodic_exists_ne_zero_orth_vacuum`). The floor holds at `β = 0` as well, so
it gives the non-zero complement and nothing more. With it,
`PeriodicContent.wilson_gaugeInv_mass_gap_every_coupling_periodic` states the gap at every `β > 0` from
the reads at the periodic state alone, and `PeriodicReduce.torusSlack_iff` states the reads, observable
by observable, as margin inequalities on the periodic lattices.

**The reads are a spectral bound, at any margin.** A read's correlation is the moment sequence of the
vector's spectral measure, so the margin sum is `∫ (modeCos k t − γ·modeMass k t) dw_v`. Since
`modeCosAvg k` is antitone with `modeCosAvg k 1 = 0` (`FloorRead.modeCosAvg_one`), the margin inequality
at `γ` holds when the vacuum complement contracts at a rate `r` with `γ ≤ modeCosAvg k r`
(`FloorRead.readsClearWith_of_contraction`) and gives a contraction at every `s` with
`modeCosAvg k s < γ` (`FloorRead.contraction_of_readsClearWith`); any `γ > 0` gives a gap
(`FloorRead.exists_contraction_lt_one_of_readsClearWith`), and
`FloorRead.wilson_gaugeInv_mass_gap_every_coupling_any_margin` is the periodic headline at any positive
margin; at `γ > 0` its input is the contraction itself, so the floor `3^{−1/4}` fixes the constant, not
the existence.

**The input at one lag.** Reflection positivity at the site plane and positivity of the transfer at the
link plane make every lag profile `b(c) = form x (Tᶜ x)` log-convex (`ChessboardRead.lagProfile_log_convex`),
so `b(1)^m b(0) ≤ b(0)^m b(m)` and `GapAt` holds at rate `r` exactly when one lag `m` does
(`ChessboardRead.gapAt_iff_lag`). On the periodic lattices the input is then one inequality per
gauge-invariant local observable at any one lag `m ≥ 1`, at any rate `0 < r < 1`, and it gives the
Clay gap at `r` (`ChessboardRead.periodic_clayGapAt_of_torusLag`). At `T = id` the bound forces a null
vacuum complement (`ChessboardRead.lag_forces_null_of_T_eq_id`), so it needs `T ≠ id`.

**The base at the periodic state.** The cluster expansion
(`StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball`) holds on any finite carrier of touch degree at
most `16·4`, and the periodic carrier has touch degree at most `16·4` at every extent
(`StrongCoupling.touchDeg_bd_le`).
`PeriodicStrongCoupling.torusCube` is the torus anchor set, holding the halo of every inner link
(`PeriodicStrongCoupling.linkHalo_subset_torusCube`), touch-connected
(`PeriodicStrongCoupling.torus_reach_from_base`) and of at most `16(R + 1)⁴` plaquettes
(`PeriodicStrongCoupling.card_torusCube_le`); the circular distance moves by at most one per touch
(`PeriodicStrongCoupling.circDist_sub_lipschitz`). So every periodic lattice of extent at least twice the
separation has the free-box cluster bound (`PeriodicStrongCoupling.torusState_connected_abs_le_of_cubes`),
and `PeriodicReduce.tendsto_torusConn` carries it to `periodicState`
(`PeriodicStrongCoupling.periodic_connected_shift_abs_le_obs`). Per-vector decay, the contraction and
`GapAt` follow as at the `mixCube` state (`PeriodicStrongCoupling.periodic_decay_of_orth`,
`PeriodicStrongCoupling.periodic_norm_Tq_le_of_orth`, `PeriodicStrongCoupling.periodic_gapAt_of_coreRate`),
giving `PeriodicStrongCoupling.periodic_gapAt_strong_coupling` on `(0, β₀)`, and
`PeriodicStrongCoupling.periodic_tower_base` carries it by `GapStep.gapAt_mono` to the tower's base rate
`e^{−M·aRun N β}` for every `M ≤ −log(coreRate 64 β) / aRun N β`.

**The interval, sharpened.** The per-plaquette count `4(K + 1)²` in `StrongCoupling.coreRate` has two
sources: a lazy walk with `K + 1` choices and two steps per plaquette (`StrongCoupling.card_connSets_le`),
and `4^m` ordered splits of a span. A tour — a depth-first traversal of a spanning tree
(`StrongCouplingSharp.IsTour`) — covers every touch-connected set (`StrongCouplingSharp.exists_tour_cover`);
there are at most `Kᵉ·catalan e ≤ (4K)ᵉ` tours with `e` branches (`StrongCouplingSharp.card_tourSet_le`),
so at most `(4K)^(m−1)` touch-connected sets of `m` plaquettes (`StrongCouplingSharp.card_connSets_le_four`).
The pair weights are summed rather than counted: at most `(1 + q)² − 1 = e^{4β} − 1` per non-anchor
plaquette of the span and `(1 + q)² = e^{4β}` per anchor plaquette, `q = e^{2β} − 1`
(`StrongCouplingSharp.pairCover_insert`, `StrongCouplingSharp.pairCover_le`). The resulting rate is
`StrongCouplingSharp.coreRate' K β = 4K(e^{4β} − 1)e^{4βK}`, the cluster bound
`StrongCouplingSharp.wilsonCorrConnObs_abs_le_of_not_mem_ball'` holds on it, and the periodic chain re-runs
to `StrongCouplingSharp.periodic_gapAt_of_coreRate'` and `StrongCouplingSharp.periodic_gapAt_strong_coupling'`,
at every `0 < β ≤ 1/1400`, where `coreRate' 64 β < 1` (`StrongCouplingSharp.coreRate'_lt_one_of_le`); that
interval is more than twenty times every interval on which `coreRate 64 β < 1`
(`StrongCouplingSharp.periodic_gap_interval_exceeds_old`).

**The line of constant physics.** For transfer data `D`, `ConstantPhysics.rateSet D` holds the rates `m > 0`
with `GapAt D (e^{−m})` and `ConstantPhysics.latMass D` is their supremum: `GapAt D (e^{−latMass D})`
always (`ConstantPhysics.gapAt_exp_neg_latMass`), it is positive exactly when the rate set is non-empty and
bounded (`ConstantPhysics.latMass_pos_iff`), and bounded exactly when `T` moves some vacuum-orthogonal vector
to one of positive form (`ConstantPhysics.bddAbove_rateSet_iff`). At the periodic state
`ConstantPhysics.latMassP` is that mass, and the spacing `ConstantPhysics.aPhys = latMassP/mphys` makes the
physical gap exactly `mphys` at every coupling where `latMassP` is positive
(`ConstantPhysics.constant_physics_gap`). Along any eventually positive spacing `a`, where `T` moves the
vacuum complement at large `β`, `ConstantPhysics.uniformPhysGapAlong_iff_massDominates` identifies the
uniform physical gap with the lattice mass dominating `a`, so `ConstantPhysics.fixedWindowDecay_iff_massDominates` makes `FixedWindowDecay` the
statement `κ·aRun N β ≤ aPhys β` at large `β` (`ConstantPhysics.fixedWindowDecay_iff_spacing_comparable`);
asymptotic scaling of the lattice mass is `aPhys/aRun → 1` (`ConstantPhysics.asymptoticScaling_iff_aPhys_ratio`)
and gives it (`ConstantPhysics.fixedWindowDecay_of_asymptoticScaling`). From continuity, positivity and
vanishing of the lattice mass, `ConstantPhysics.exists_physFamily` chooses couplings at which `aPhys` hits
the dyadic spacings, and `ConstantPhysics.contS_of_constantPhysics` makes `contS` of every separated family
the limit along `dyBeta`, under `ConstantPhysics.SignalConvergesSep` along those couplings and
`ConstantPhysics.StateShiftInvisibleSep` between them and `dyBeta`.

**The step between couplings.** The algebra and the shift are the same at every coupling; only
`periodicState hN β` moves, so a step compares two states on one algebra. `GapStep.PhysStep τ p hN β β' M`
carries `GapAt` at rate `e^{−M·aRun N β}` at `β` to rate `e^{−M·aRun N β'}` at `β'`, `aRun N` the two-loop
spacing of `SU(N)`, and `GapStep.phys_rate_le_iff` reads a rate `r` at spacing `a` as the physical rate
`−log r / a`. `GapStep.gapAt_sqrt_iff_lag_double`: under `PositiveTransfer D`, `m ≠ 0` and `0 ≤ r`,
`GapAt D (√r)` holds exactly when every vacuum-orthogonal `x` has `form x (T^{2m} x) ≤ rᵐ·form x x`, so at
`0 ≤ β'` and halved spacing the step is the lag-`2m` bound at `β'` with the lag-`m` ratio at `β`
(`GapStep.physStep_iff_lag`). `GapStep.periodic_clay_tower` composes the base and the step into
`PeriodicClayGapAt` at every `βⱼ` at one physical rate `M`. `GapStep.periodic_clay_tower_of_torus`
composes `ChessboardRead.TorusLagClear` at `β₀` and the lattice step into `PeriodicClayGapAt βⱼ rⱼ` at
every `j`; along `r_{j+1} = √r_j`, `m_{j+1} = 2m_j` and halved `aRun N`, the ratio `r_j^{m_j}` and
`−log r_j / aRun N β_j` are constant (`GapStep.sqrt_pow_double`, `GapStep.phys_rate_const`).

**The fixed physical window.** At `0 ≤ q` and `m ≠ 0`, one lag `m` at factor `q` gives
`ChessboardRead.TorusLagClear` at the per-step rate `stepRate q m = q^{1/m}`
(`WeakCouplingWindow.torusLagClear_stepRate`, `WeakCouplingWindow.stepRate_pow`), hence, at `0 ≤ β`,
`GapAt` at that rate, and `m·a ≤ L` gives the physical rate `−log q^{1/m} / a ≥ −log q / L`
(`WeakCouplingWindow.physical_rate_ge`). The converse runs through the centring of `PeriodicReduce`:
`GapAt` at `r` gives the torus inequality at every lag (`WeakCouplingWindow.torusLagClear_of_gapAt`), so
at `0 ≤ β` and `0 ≤ r`, `TorusLagClear` at any lag `m ≠ 0` is `GapAt`
(`WeakCouplingWindow.torusLagClear_iff_gapAt`). Since `aRun N β → 0`
(`WeakCouplingWindow.eventually_aRun_le`), a window lag with `L/2 ≤ m·aRun N β ≤ L` exists at every
large `β` (`WeakCouplingWindow.window_lag_exists`), and `WeakCouplingWindow.fixedWindowDecay_iff` makes
`FixedWindowDecay τ p hN L`, at `2 ≤ N` and `0 < L`, equivalent to the Clay gap at every large `β` with
physical rate `≥ c/L` for some `c > 0`. With `c` existential the condition is the same at every `L > 0`
(`WeakCouplingWindow.fixedWindowDecay_window_free`): the window sets no scale, and the input is the
uniform physical gap.

**The UV/IR split.** On any family of transfer data with spacing `a`, `UVIRSplit.LossStep D a βUV ε` carries
`GapAt` at `e^{−M·a β}` to `e^{−(M − ε(a β))·a β'}` whenever `a β/2 ≤ a β' ≤ a β`, and
`UVIRSplit.gapAt_chain` composes the steps with the losses added. `UVIRSplit.LossBudget ε a₀ E` bounds the
losses along the halvings of `a₀` by `E`, and `UVIRSplit.VanishingLoss ε` makes that budget small at small
`a₀`. At the periodic data, `UVIRSplit.gapAt_eventually_of_uv_ir` reaches every large `β` from `β₀` by
halvings and one partial step, and `UVIRSplit.fixedWindowDecay_of_uv_ir` gives `FixedWindowDecay` when
`E < M₀`; `UVIRSplit.irGapAt_of_fixedWindowDecay` and `UVIRSplit.fixedWindowDecay_iff_irGapAt` close the
equivalence under the UV step with vanishing loss. `UVIRSplit.uvLossStep_iff_long_lag` states the UV step as one lag of
physical length at least `ℓ` at the finer coupling (`UVIRSplit.le_longLag_mul`).
`UVIRSplit.lossStep_without_gap` and `UVIRSplit.lossStep_not_automatic` place the UV step strictly between
nothing and the gap, and `UVIRSplit.irGapAt_of_strong_coupling_chain` joins the proved base to the IR gap
through finitely many crossover steps. The UV step with a loss equal to the largest attainable physical
rate holds trivially, so its content is carried by `UVIRSplit.VanishingLoss` or a budget below the IR
rate; and since `UVIRSplit.IRGapAt` is proved at strong coupling at a rate unbounded as `β₀ → 0`, the split
carries IR content only with `β₀` past the strong-coupling region. Balaban (Commun. Math. Phys. 119
(1988) 243–285; 122 (1989) 355–392) bounds block-spin effective densities on a finite torus uniformly in
the number of steps at small running coupling and proves no correlation bound. Open: the UV step on
correlations in infinite volume with summable losses, and a gap at any single coupling outside strong
coupling.

**The zoom.** Under `PositiveTransfer` every lag profile is antitone (`ZoomStep.lagProfile_succ_le`) and
the even lags determine the gap (`ZoomStep.evenEnvelopeAt_iff_gapAt`). A fine profile that repeats the coarse
one exactly has lag-one ratio `1` at every non-null vacuum-orthogonal observable, which excludes every gap
below `1` (`ZoomStep.not_gapAt_of_ratio_one`,
`ZoomStep.literalRepeat_no_gap`); a fine profile matching the coarse one at even lags (`ZoomStep.EvenRepeat`)
carries the gap at the square-root rate (`ZoomStep.gapAt_sqrt_of_zoomRepeat`), which is the same physical
rate (`ZoomStep.zoom_keeps_physical_rate`), and gives `GapStep.PhysStep` (`ZoomStep.physStep_of_evenRepeat`).
`ZoomStep.ZoomInvariantWith` is that matching with a loss, equivalent to `UVIRSplit.UVLossStep`
(`ZoomStep.zoomInvariantWith_iff_uvLossStep`). On the spectral side `ZoomStep.outWeight` is a vector's
spectral weight past an edge `s`, the vacuum complement contracts at `s` exactly when that weight is zero
(`ZoomStep.contraction_iff_leftoverNull`), the reads clear the floor exactly when the weight past the read's
edge is zero (`ZoomStep.readsClearWith_iff_leftoverNull`), and `ZoomStep.LeftoverInvariant` — the leftover
null at the window's diffraction rate at every large `β` — is `FixedWindowDecay`
(`ZoomStep.leftoverInvariant_iff_fixedWindowDecay`).

**The same forest.** `ZoomForest.ObsClose μ ν ε` bounds every measurable observable of size one by `ε`,
closed under maps (`ZoomForest.ObsClose.map`) and composition (`ZoomForest.ObsClose.trans`).
`ZoomForest.ForestAt m ε` asks summable steps; then the laws are Cauchy (`ZoomForest.ForestAt.cauchy`) and
every bounded observable converges with the tail as its rate (`ZoomForest.ForestAt.tendsto`), connected
correlations included (`ZoomForest.ForestAt.abs_conn_sub_le`). A log-density bound gives a KL bound
(`ZoomForest.klDiv_le_of_abs_llr_le`); a geometric one gives the forest (`ZoomForest.ZoomGeometric.sameForestKL`,
then `ZoomForest.SameForestKL.sameForestAt` under the stated `ZoomForest.PinskerObs`). On the continuous path
a speed bound gives closeness by the path length (`ZoomForest.SpeedBound.obsClose`), proved on finite spaces
by Cauchy–Schwarz against the Fisher information (`ZoomForest.finitePath_abs_sub_le`), and
`ZoomForest.FiniteZoomLength.tendsto` gives the limit. `ZoomForest.tendsto_latSkR_of_sameForestAt` reads the
Schwinger functions through one bounded observer observable; over an arbitrary observer its hypotheses hold
exactly when the lattice sequence has summable increments, so its content is in exhibiting the Gibbs measures
and renormalised fields as that observer.

**Gap to decay.** On a patch system the lazy heat bath `T = id − K⁻¹H` (`HeatBathGapDecay.Tstep`) is a
contraction (`HeatBathGapDecay.nrm_Tstep_le`) and, under `GlobalGap c`, contracts the range of `H` by
`1 − c/(2K)` (`HeatBathGapDecay.range_gap`, `HeatBathGapDecay.nrm_Titer_H`). A link-resolved commutator
recursion bounds how far `T` spreads (`HeatBathGapDecay.lr_bound`), and the two combine into a covariance bound
whose volume factor cancels at `n = sK` steps (`HeatBathGapDecay.cov_bound_exp`). At the periodic state this
gives `GapAt` from per-vector torus clustering (`HeatBathGapDecay.gapAt_of_torusClusterAt`) and
`HeatBathDecay` from `HeatBathGapDecay.HeatBathLocality` (`HeatBathGapDecay.heatBathDecay_of_locality`),
whose one analytic field is fixed-volume ergodicity of the lazy heat bath (`HeatBathGapDecay.ErgodicLimit`).

**The box patch gap.** At `β = 0` each heat bath is the Haar average over its link and any two commute
(`BoxGap.heatAvg_zero`, `BoxGap.torusCondExp_comm_zero`), so every box patch has local gap `1`
(`BoxGap.boxLocalGap_zero`), and `BoxPatchGap hN 0 n 1` holds once the threshold `(40n − 36)/n²` is below `1`, that is for `n ≥ 40`
(`BoxGap.boxPatchGap_zero`). At a positive coupling the weight factors at a box `S` into a local weight on the
plaquettes meeting `S` and a boundary constant (`BoxGap.action_split_set`, `BoxGap.wt_glue`), so the local-gap
inequality on every fibre over a frozen boundary gives it on the torus (`BoxGap.fibre_iff_local`,
`BoxGap.boxLocalGap_of_fibreGap`). `BoxGap.BoxFibreGap` is that fibre statement, and
`BoxGap.boxPatchGap_of_fibreGap` returns `BoxPatchGap`. The pair route (`BoxGap.pairDefectAt_of_pairCorrAt`,
`BoxGap.boxPatchGap_of_pairCorrLinear`) supplies the local gap from two-link correlations; its witness
is the two-link conditional expectation, and pairs sharing no plaquette contribute nothing.

**The box gap is at most one.** The plaquette in the plane `(0, 1)` based one step back from a box corner reads
exactly one box link; every other box heat bath fixes it up to null vectors, so the box operator acts on it as
`id − E_l`, an idempotent, and the local-gap inequality reads `γ·v ≤ v` with
`v = ‖x − E_l x‖² > 0` (`BoxCeiling.torusForm_sub_condExp_pos`, the density moving when that one link moves, at
`2 ≤ N`). So `BoxCeiling.boxLocalGap_le_one`, and with the threshold `(40n − 36)/n² < γ ≤ 1`,
`BoxCeiling.boxPatchGap_side_ge_forty`: the box check needs side at least `40` at every coupling.

**The box check at small coupling.** For two links `l ≠ m` sharing a plaquette, the conditional expectation
given every other link (`PairCorr.twoCondExp`, built from the two-link heat bath `PairCorr.heatAvg2`) is fixed by
both single-link heat baths. On the `(l, m)` fibre the weight of the at most `512` plaquettes visiting `l` or `m`
lies in `[e^{−1024β}, 1]` times a boundary constant that cancels (`PairCorr.wt_pair_bounds`), and a product-measure
comparison bounds the correlation of `E_l f` and `E_m f` by `(κ² − 1)κ ≤ 5760β`, `κ = e^{1024β}`
(`PairCorr.fibre_corr_le`, `PairCorr.pairCorr_twoCond`). Links sharing no plaquette commute. With at most `21`
neighbours the defect matrix has sums `120960β` (`PairCorr.pairDelta_defect`), so
`PairCorr.pairCorrLinear_holds`, `PairCorr.boxPatchGap_at` (`BoxPatchGap` at `β = 1/241920`, side `80`, gap `1/2`)
and `PairCorr.irGapAt_small` (the IR gap there at `boxRate`). The constants are not optimised.

**The UV step at the box's rate.** `UVIRSplit.IRGapAt` is monotone in the rate (`TransferGap.gapAt_mono`): a
gap at `M₀` is a gap at every smaller positive rate, so a UV target is only usable at a named rate. The heat-bath
clustering proof computes its rate: at neighbour bound `z` and heat-bath gap `c` it is
`HeatBathGapDecay.clusterRate z c = √max(e/3, e^{−min(c,1)/(2(6z+1))})`
(`HeatBathGapDecay.torusClusterAt_of_localityAt`), and the Wilson heat bath has `z = 21`
(`HeatBathLocal.localityAt_holds`). A box of side `n` at local gap `γ` has heat-bath gap `boxKnabe n γ`
(`BoxPatch.boxFamily_check`), so it gives the IR gap at `β₀` at
`HeatBathLocal.boxRate N β₀ n γ = min(boxKnabe n γ, 1)/(508 · aRun N β₀)` (`HeatBathLocal.irGapAt_boxRate`,
`HeatBathLocal.boxRate_eq`), a physical mass at most `1/508` in lattice units at `β₀`.
`ClayRoutes.UVBelowIR τ p hN β₀ βUV M₀` is the UV step against one rate, with non-negative losses (a negative
loss would assert a gap outright) summing below `M₀`; `ClayRoutes.clay_continuum_of_boxPatchGap` asks it at
`boxRate`, with every coupling of the step past the peak `17N²/(88π²)` of `aRun N`, where the two-loop spacing
decreases, so each step of the tower refines the spacing. The peak lies deep in strong coupling (about `0.078`
at `N = 2`, `0.176` at `N = 3`); the physical crossover lies at larger `β` (standard `β ≈ 2.2` and
`5.7`, Lean `β ≈ 1.1` and `2.85`) and is inside the UV step unless
`β₀` is past it; and `ClayRoutes.clay_continuum_of_irGap` takes an IR gap at any stated
rate. The constant is `508 = 4(2zy + 1)`. `z = 21` bounds the links whose heat baths are not shown to commute
with a given link's: the link and the links sharing a plaquette with it, at most `1 + 2 + 3 · 6` in four dimensions,
the `2` being the link's neighbours along its own direction, which share a diagonal plaquette `μ = ν` with it
(`bdT` includes the diagonal; `HeatBathLocal.card_nbT_le`). `y = 3` is the least integer sweep parameter above
`e`. A diagonal plaquette's holonomy is the identity, so its two links' conditional laws do not couple; a
commutation lemma that skips the diagonal would give `z = 19` and the constant `4(6 · 19 + 1) = 460`.

**The UV step in entropy form.** For observer laws `obs β` (image measures of the periodic states under block
maps, `UVEntropy.PeriodicObserverLaws`), a χ² bound `√χ²(obs β' ‖ obs β) ≤ ε` moves a connected pairing by at
most `ε` times a variance coefficient (`UVEntropy.abs_obsConn_sub_le`), and a window factor `q` becomes `q + 4η`
after one step (`UVEntropy.factor_step`, `UVEntropy.factor_chain`). Along the dyadic tower from `β₀` the factor
stays below `q₀ + 4κE` (`UVEntropy.obsFactor_eventually_of_uvEntropy`). The physical-rate loss of an additive
step at `q = e^{−Mℓ}` is `4κε·e^{Mℓ}/ℓ` (`UVEntropy.neg_log_add_ge`), which grows with `M`, so this route does not
give `UVIRSplit.UVLossStep` for the whole lattice class; the class enters through `UVEntropy.ObsReadback` and
`UVEntropy.UVEntropyBridge`. On the constructive side, a density band `e^{±D}` gives `√χ² ≤ e^D − 1`
(`UVEntropy.chiStep_of_densityBand`), a power-law width `C a^γ` has a geometric budget
(`UVEntropy.lossBudget_rpow`) and a constant width has none (`UVEntropy.not_lossBudget_const`).
`UVEntropy.clay_continuum_of_boxPatchGap_entropy` takes `PeriodicObserverLaws`, `ObsReadback` at `β₀`,
`ClassKappaUV`, `UVEntropyBridge`, the peak restriction on `βUV` and `EntropyBelowIR` at `boxRate`,
`(e^{−boxRate · aRun N β₀})^{m₀} + 4κE < 1`. `PeriodicObserverLaws` does not tie `φ β` across couplings, so
observer laws frozen in `β` meet the step at zero loss and the bridge carries the content.

**Heat-bath locality.** Two `torusForm`-self-adjoint idempotents with values among the observables not reading a
link, each fixing them up to null vectors, agree up to null vectors (`HeatBathLocal.form_proj_unique`), so every
`WilsonHeatBath` is the heat bath up to null vectors (`HeatBathLocal.condExp_sub_null`) and commutes off shared
plaquettes (`HeatBathLocal.condExp_comm_null`, `HeatBathLocal.localCommute_wilson`, at most `21` neighbours). The
Wilson density lies between `e^{∓2|β||P|}` times the Haar density, the product-Haar variance is bounded by the
single-link defects through a sweep (`HeatBathErgodic.sweep_energy`), and the Haar average is the best
single-link approximation, giving a Poincaré inequality at each fixed volume, its constant growing with the
volume (`HeatBathErgodic.heat_poincare`,
`HeatBathLocal.torus_poincare`) and the ergodic limit (`HeatBathLocal.ergodicLimit_wilson`). A separation
potential gives the `Far` levels (`HeatBathLocal.far_of_potential`), and `HeatBathLocal.heatBathLocality_holds`
assembles `HeatBathGapDecay.HeatBathLocality` at every coupling. `HeatBathLocal.heatBathDecay_holds` then
gives `KnabeCriterion.HeatBathDecay`: a uniform heat-bath gap gives decay, the gap supplied on the finite-size
route by `BoxPatch.BoxPatchGap`.

**Entropy tools.** The pushed-forward density pulled back along a map is the conditional expectation of the
density, so conditional Jensen for `klFun` gives data processing (`EntropyTools.klDiv_map_le`); the pointwise
bound `3(x − 1)² ≤ (2x + 4)·klFun x` (`EntropyTools.three_mul_sq_le_klFun`) and a linear Cauchy–Schwarz give
Pinsker (`EntropyTools.abs_integral_sub_le_sqrt_two_mul_klDiv`). The χ² bound
`|∫h dP − ∫h dQ| ≤ √χ²(P‖Q)·√Var_Q(h)` (`ChiForest.abs_integral_sub_le_sqrt_chiSq_mul`) makes each zoom step
relative to the observable's own spread (`ChiForest.ChiForest.abs_step_le`), so the connected correlations
converge with a relative remainder (`ChiForest.ChiForest.abs_conn_sub_le`); the step to
`WeakCouplingWindow.FixedWindowDecay` then needs one constant bounding that remainder by the lag-zero value
across the observable class (`ChiForest.eventually_factor_of_relative`).

**The finite-size criterion.** With cover weight `a₁ = Σₖ cₖᵢ`, squared weight `a₂`, pair weights
`KnabeCriterion.pairWeight` at most `b` on commuting pairs and within `w` of `b` otherwise, and `w` of row
and column sums at most `e`, a patch gap `γ·B(Aₖx, x) ≤ B(Aₖx, Aₖx)` gives
`(γa₁ − a₂ + b − e)·B(Hx, x) ≤ b·B(Hx, Hx)` (`KnabeCriterion.knabe_bound`); commuting projections give the
gap one outright (`KnabeCriterion.knabe_commuting`). On the periodic lattices `KnabeCriterion.torusForm`
is the torus state's pairing on the periodic gauge-invariant observables
(`KnabeCriterion.periodicGaugeInvSubmodule`), `KnabeCriterion.WilsonHeatBath` carries the link conditional
expectations with the patch data, and `KnabeCriterion.WilsonHeatBath.toPatchSystem` its patch system.
`KnabeCriterion.gapAt_of_patchGapCheck`, `KnabeCriterion.periodicClayGapAt_of_patchGapCheck` and
`KnabeCriterion.irGapAt_of_patchGapCheck` give the gap at one coupling from `KnabeCriterion.HeatBathDecay`
and `KnabeCriterion.PatchGapCheck`, and `KnabeCriterion.fixedWindowDecay_of_patchGapCheck` joins it to the
UV step from that coupling on. At a one-patch witness `PatchGapCheck` is a uniform heat-bath gap; its
finite-size content is a box-patch witness, whose multiplicities in four dimensions put the needed patch
gap at `γ > (40n − 36)/n²` for boxes of side `n`.

**Flux sectors.** A neutral projection `P` (idempotent, form-symmetric, commuting with `T`, fixing the
vacuum) splits every lag profile, `form x (Tᵐ x) = form (Px) (Tᵐ Px) + form (x − Px) (Tᵐ (x − Px))`
(`CentreSector.form_pow_split`), and `GapAt` is the neutral bound on the vacuum complement together with
the charged bound (`CentreSector.gapAt_iff_sectors`). On `ℤ⁴` a central height twist is a gauge
transformation (`CentreTwist.heightTwist_eq_igaugeTransform`), so every gauge-invariant observable is
twist-invariant (`CentreTwist.isIGaugeInvariant_heightTwist`); at `SU(N)`, `2 ≤ N`, a central `z ≠ 1`
moves every configuration and fixes every member of `gaugeInvHalfSpaceAlg τ p`
(`CentreTwist.centre_invisible_SU`), and on each periodic lattice the torus observable of a
gauge-invariant observable is invariant under the torus centre twist (`CentreTwist.torusObs_torusTwist`).
The algebra of `periodicGaugeInvData` therefore contains no charged observable.
`CentreSector.charged_rate_does_not_reach_neutral` gives, for every `0 ≤ r < 1`, abstract positive
transfer data with a neutral projection, the charged sector killed in one step, a gap at some
`s ∈ (r, 1)`, and no gap at `r`: a bound on charged sectors fixes no neutral rate, and the input is a
bound on the gauge-invariant algebra itself.

**The surface count bounds the gap from above.** A counted surface sum below a correlator,
`C·3^c·e^{−μ(4c+6)} ≤ ν(θx·S^c x)` — the character-expansion shape, `e^{−μ}` the activity per
plaquette — forces `3e^{−4μ}` below every contraction rate, so `Δ ≤ 4(μ − κ₀)`: the floor is where
the surface series stops converging. The vortex hypotheses of `VortexCount`, `VortexFamily` and
`Capacity` have no Wilson producer; the reads at weak coupling need input past that radius.

## 5. Reconstruction and non-triviality

**E at the periodic state.** The couplings `ContinuumSchwinger.dyBeta hN k` halve the spacing at each
step (`ContinuumSchwinger.aRun_dyBeta`) and tend to infinity (`ContinuumSchwinger.tendsto_dyBeta`). A
field is a continuous local gauge-invariant observable (`ContinuumField.LField`); translation by `ℤ⁴`
(`ContinuumField.transObs`) preserves the periodic state (`ContinuumField.state_transObs`) and commutes
with the reflection (`ContinuumField.ireflObs_transObs`), and the smeared field
`ContinuumField.smear a F f = Σₓ a⁴ f(a x) · transObs x F` is bounded uniformly in `a ≤ 1`
(`ContinuumField.norm_smear_le`), covariant under translation and reflection
(`ContinuumField.smear_translate`, `ContinuumField.ireflObs_smear`), and in the half-space algebra for
positive-time test functions (`ContinuumField.smear_mem_halfSpaceAlg`). `ContinuumSchwinger.contS` is `limUnder`
of the renormalised products along one non-principal ultrafilter: under `ContinuumSchwinger.UniformBound`
it is their limit (`ContinuumSchwinger.tendsto_contS`), and where the sequence diverges it is an
unspecified real, so the identities that hold with no hypothesis (`ContinuumSchwinger.contS_comp_equiv`,
`ContinuumSchwinger.contS_translate`, `ContinuumSchwinger.kern_symm`) carry content where `contS` is a
limit. Under the bound it carries OS0, OS1 on the dyadic subgroup, reflection invariance
(`ContinuumSchwinger.contS_reflect`), OS2 and OS3. `ContinuumReconstruction.contReflForm` and
`ContinuumReconstruction.contTransfer` are the reflection form and the dyadic transfer semigroup
(`T_m = T_{m+1}²`), and `ContinuumReconstruction.continuum_reconstruction` the reconstructed Hilbert space
with `⟪vecOf P, vecOf Q⟫` equal to the Schwinger kernel. `ContinuumCluster.lattice_cluster` reads
`TransferGap.clustering_sq` at every step, and `ContinuumCluster.contS_cluster_of_fixedWindowDecay` passes
it to the limit as OS4 in reflected form at physical rate `c/L`.

**The same forest, by probes.** Two states that agree on a point-separating subalgebra are equal
(`Beacon.state_eq_of_sameSignal`, through `DLRLimit.State.eq_of_eqOn_subalgebra`), so a family whose probe
responses converge has one limit, reached along the filter (`Beacon.exists_unique_limit_of_beacon`,
`Beacon.beacon_iff_tendsto`); on measures the same holds in the weak topology
(`Beacon.exists_unique_tendsto_probabilityMeasure_of_beacon`,
`Beacon.measure_eq_of_integral_eqOn_subalgebra`). At the lattice, `Beacon.VolumeBeacon` makes every
periodic limit equal `periodicState` (`Beacon.eq_periodicState_of_volumeBeacon`), `Beacon.ObserverBeacon`
gives a unique observer-level limit (`Beacon.observer_limit_unique`), and `Beacon.SchwingerBeacon` makes
`contS` independent of the ultrafilter and a limit along the couplings
(`Beacon.contSAlong_eq_contS_of_schwingerBeacon`, `Beacon.tendsto_contS_atTop_of_schwingerBeacon`).
`Beacon.SchwingerBeacon` quantifies over every family, coincident supports included, where a growing
field-strength factor is expected to diverge; the form expected to hold is the separated one,
`ConstantPhysics.SignalConvergesSep` at `(dyBeta, dySpacing)`.

**Flowed probes.** A `ContinuumFlow.ConfFlow` is a continuous, gauge- and reflection-covariant configuration
map of finite range; `ContinuumFlow.Flow.ofConfScaled` composes fields with it and renormalises. The flowed
lattice functions obey the smearing bound (`ContinuumFlow.eventually_abs_latSF_le`), their ultrafilter limit
`ContinuumFlow.contSF` is symmetric, dyadically translation invariant and reflection invariant with no
hypothesis (`ContinuumFlow.contSF_comp_equiv`, `ContinuumFlow.contSF_translate`, `ContinuumFlow.contSF_reflect`),
a finite physical range keeps positive-time fields in the half-space algebra beyond the margin
(`ContinuumFlow.Flow.posPreserving_of_physRange`), which gives OS2 there, and a generic reconstruction from any
symmetric Gram-positive kernel with bounded orbits (`ContinuumFlow.reconstructed_of_positive`) gives
`ContinuumFlow.flow_reconstruction`. `ContinuumFlow.latKernelF_zeroFlow_connected` identifies the flowed kernel
at zero flow time with `ContinuumNontrivial.latKernel`. The localised gradient flow is not constructed; the
one configuration flow in the tree is `ContinuumFlow.ConfFlow.identity`, where the flowed functions are
`ContinuumSchwinger`'s (`ContinuumFlow.contSF_zeroFlow`), so the margin and the positive-flow-time inputs (`ContinuumFlow.UniformBoundF`,
`ContinuumFlow.FlowBeacon` over coincident supports at the canonical factor) are read at a flow still to be built.

**The continuum gap, on separated supports.** `ContinuumSep.sepBy d f g` puts the supports of `f` and `g`
at sup-distance at least `d`, kept by translation and reflection (`ContinuumSep.sepBy_translate`,
`ContinuumSep.sepBy_reflect`); `ContinuumSep.UniformBoundSep` is the uniform bound over separated families
only. A separated positive-time monomial (`ContinuumSep.SepMono`) pairs with its reflection as a separated
family (`ContinuumSep.famSep_pairFam`), so the reflection form, the transfer and the reconstruction rebuild
on them (`ContinuumSep.contTransferSep`, `ContinuumSep.continuum_reconstruction_sep`). The reflected
clustering bound (`ContinuumSep.contS_cluster_of_fixedWindowDecay_sep`) gives every vacuum-orthogonal
vector a per-vector form decay (`ContinuumSep.form_pow_le_of_cluster_sep`), hence `GapAt`
(`ContinuumSep.gapAt_of_per_vector_form_decay`, `ContinuumSep.gapAt_sep_of_cluster`), and
`ContinuumSep.continuum_gap_sep` assembles the spectral gap at every dyadic step, the vacuum complement contracted
by `e^{−(c/L)·tₘ}` with `c/L` fixed: a physical gap of at least `c/L`. `ContinuumSep.exists_orth_ne_zero` and `ContinuumSep.exists_orth_ne_zero_sep` turn a
non-zero connected two-point function into a vacuum-orthogonal vector outside the span of the vacuum.

**Non-triviality from Y.** For a one-factor monomial the reflected pair is a Riemann double sum of the
lattice kernel against the reflected and the plain test function
(`ContinuumNontrivial.latSkR_mono1_pair`); at the connected renormalisation the kernel is `Z²` times the
connected two-point function (`ContinuumNontrivial.latKernel_connected`), at `ContinuumNontrivial.rhoA`
that function over `a⁸` (`ContinuumNontrivial.latKernel_rhoA`), and the vacuum term vanishes
(`ContinuumNontrivial.kern_empty_mono1`). With the cube test function the Riemann sums are at least
`(ℓ/2)⁴` (`ContinuumNontrivial.riemann_cube_ge`), the pair region sits at separation at least `2t`
(`ContinuumNontrivial.pairRegion_subset`), and a kernel limit bounded below there bounds the pair below
by `g₀/2·(ℓ/2)⁸` (`ContinuumNontrivial.kern_mono1_ge`). `ShortDistanceY.AFShortDistance` bounds `G` below on a
short interval (`ContinuumNontrivial.af_bounds_on_interval`), and
`ContinuumNontrivial.connectedTwoPointNonzero_of_af` assembles `ContinuumSep.ConnectedTwoPointNonzero`
from `ContinuumNontrivial.KernelConvergesSep` and Y (at `ContinuumNontrivial.rhoA`,
`ContinuumNontrivial.connectedTwoPointNonzero_rhoA`), and `ContinuumNontrivial.exists_orth_ne_zero_of_af`
gives the vacuum-orthogonal vector under `ContinuumSep.UniformBoundSep`. `ContinuumClay.continuum_gap_nontrivial`
joins it to `ContinuumSep.continuum_gap_sep` on one reconstructed space.

**Hypercubic and ℝ⁴ invariance.** Axis permutations of `ℤ⁴` act on links, configurations and
observables (`ContinuumHypercubic.iaxisObs`), commute with translation
(`ContinuumHypercubic.iaxisObs_transObs`) and preserve gauge invariance
(`ContinuumHypercubic.isIGaugeInvariant_iaxisObs`); every periodic-lattice Wilson state is invariant
(`ContinuumHypercubic.torusState_axis`), hence the periodic state (`ContinuumHypercubic.periodicState_axis`),
and with the reflections the continuum Schwinger functions are invariant under every signed permutation
of the test functions at hypercubic-scalar fields (`ContinuumHypercubic.contS_signed`). The smeared field is
Lipschitz in the test function uniformly in the spacing (`ContinuumHypercubic.norm_smear_sub_le`); under
`ContinuumHypercubic.SupContinuousSep` translation invariance extends from the dyadic subgroup to all of
`ℝ⁴` for uniformly continuous test functions (`ContinuumHypercubic.contS_translate_real`). The rotations off
the hypercubic group are `ContinuumHypercubic.RotationOpen`. At `N = 1` the configuration space is a point
and every connected statistic vanishes (`NOneVacuity.not_wilsonLatticeAF_one`,
`NOneVacuity.not_wilsonThreePointSeparation_one`).

**Y.** `ShortDistanceY.AFShortDistance G` asks `r⁸·G(r)·(log r)² → C > 0` as `r → 0⁺`; `8` is twice the
canonical dimension of `tr F²` and the square of the log is two insertions of `ḡ²(r) ∼ 1/(2b₀ log(1/r))`.
`ShortDistanceY.af_and_free_false` and `ShortDistanceY.not_af_of_scalingForm` exclude the free massless and
massive forms, `ShortDistanceY.not_af_of_conformal` every power law, and `ShortDistanceY.af_of_const_mul`
keeps Y under a constant renormalisation. `ShortDistanceY.coupling_mul_neg_log_aRun_tendsto` gives
`(N/β)·(−log aRun N β) → 24π²/(11N) = 1/(2b₀)` at the Lean coupling, `g² = N/β`, the two-loop term entering only through `(log u)/β → 0`,
and `ShortDistanceY.af_along_aRun` reads Y at the running spacing. `ShortDistanceY.familyAF_iff` makes the
lattice form equivalent to Y under convergence of the two-point function, and
`ShortDistanceY.wilson_yang_mills_separated` joins it with N.

**N is a separated three-point statement.** A Gaussian is fixed by its covariance and exists for every
admissible covariance, so the read, a variance floor and the gap — two-point quantities — are met by a
Gaussian with the same two-point function; N needs a connected function of order three or more. The
cumulants of one smeared composite carry its contact terms, so the carrier is the connected three-point
function of three disjoint composites. `ThreePointN.sepRatio ν A B C = cum3² / |cov2 A B · cov2 B C ·
cov2 C A|` is unchanged under `X ↦ Z·X + b` in each argument (`ThreePointN.sepRatio_affine`), so it
survives every multiplicative and additive renormalisation. Its value in the free gauge field is `0` by
duality; Lean proves the matrix statement:
`ThreePointN.trace_three_eq_zero_of_duality` gives `tr(P₁W₁₂P₂W₂₃P₃W₃₁) = 0` when a duality `J, K` flips
each composite and fixes each propagator, and `ThreePointN.freeSepRatio_of_duality` reads it as the free
ratio; `ThreePointN.dual_example` is a named instance. Tying `freeCum3` to the free Maxwell field's Wick
contraction is physics. `ThreePointN.ThreePointSeparated` is the ratio
bounded below along a family; `ThreePointN.WilsonThreePointSeparation N hN`, open at every `β > 0`, is it
at the periodic state
for three plaquette blocks (`ThreePointN.tripleObs`) of physical size `ℓ` at base offsets `D` along two
axes, at spacing
`aRun N β`. From it, `ThreePointN.wilson_separated_from_free` keeps the Wilson ratio at least `c` from the
free one, and `ThreePointN.wilson_continuum_threePoint`, along every `β i → ∞` and every renormalisation
with converging cumulants and non-zero limiting two-point product, gives `c ≤ K₃²/|K₀₁K₁₂K₂₀|` and
`K₃ ≠ 0`. A bounded-below ratio makes `tr F²` non-Gaussian and separates it from the free massless gauge
field; a free massive field's quadratic composite also has a non-zero three-point function, and Y's
short-distance behaviour (asymptotic freedom) separates Yang–Mills from it. The lattice plaquette's law is not Gaussian under every `mixCube` limit state at `β ≥ 0`
(`NonGaussian.nu_iplaqObs_law_not_gaussian`), and `NonGaussian.ContinuumNonGaussian` is the order-four
ratio of one composite along a family, invariant under `O ↦ aO + b` (`NonGaussian.kurtRatio_affine`).

`WilsonOS.wilson_reconstructed_nontrivial` — Osterwalder–Schrader data from the Wilson reflected form,
through `WightmanData.os_reconstruction_wightman`.

`SpecVarianceFloor.spec_variance_floor` — `exp(−(|β|·card(boundaryPlaqs {l₀})·2)) · Var_μ(h)` bounds
the kernel's variance at every region containing `l₀`. `SpecVarianceFloor.wilson_eventual_variance_floor`
is its eventual form at `SU N`, `2 ≤ N`, for the fixed-boundary kernel `WilsonDLR.specState` and a
single-link observable, and `VarianceBridge.clay_nontriviality_of_eventual_variance_floor` turns it
into a DLR state that is not a point mass. The state of M, `ν` of `FreeLimit.exists_tendsto_stateFree`,
has its own floor at a gauge-invariant plaquette, `PlaneVariance.nu_var_iplaqObs_ge`.

## 6. Verification

```
python research/code/lean_build.py build MassGap
python research/code/certify/lean_axiom_footprints.py scan
python research/code/certify/lean_derived_literals.py scan
python research/code/certify/doc_cites_live_declarations.py scan
python -m pytest research/code/tests -q
```
