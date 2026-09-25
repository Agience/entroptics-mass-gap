# Clay — the route

[CLAY-DETAIL.md](CLAY-DETAIL.md) carries the declarations. The previous pair is in
[_archive/2026-09-24-entroptics-mass-gap/](../../_archive/2026-09-24-entroptics-mass-gap/).

## The goal — the Clay Millennium Problem

> **Yang–Mills Existence and Mass Gap.** Prove that for any compact simple gauge group `G`, a
> non-trivial quantum Yang–Mills theory exists on `ℝ⁴` and has a mass gap `Δ > 0`. Existence includes
> establishing axiomatic properties at least as strong as those cited in Streater–Wightman and
> Osterwalder–Schrader.
>
> — A. Jaffe and E. Witten, *Quantum Yang–Mills Theory*, the Clay Mathematics Institute's official
> problem description.

The statement asks for all of the following, together, for every compact simple `G`:

| # | requirement | meaning |
| --- | --- | --- |
| **E** | **existence** | a quantum field theory on `ℝ⁴` satisfying the Wightman axioms (equivalently the Osterwalder–Schrader axioms for its Euclidean Schwinger functions): a Hilbert space with a unitary representation of the Poincaré group, a unique vacuum, local field operators, positivity of the energy |
| **Y** | **it is Yang–Mills** | the continuum limit of the Yang–Mills theory with gauge group `G`: its local fields correspond to gauge-invariant polynomials in the curvature, with the short-distance behaviour asymptotic freedom prescribes |
| **N** | **non-trivial** | not a free field: the interaction is present in the limit |
| **M** | **mass gap** | the Hamiltonian `H` has spectrum `{0} ∪ [Δ, ∞)` with `Δ > 0`: every state orthogonal to the vacuum carries energy at least `Δ` |

## How the lattice meets it

On a reflection-positive lattice the Hamiltonian is `−log T`, `T` the transfer operator, so **M** on
the lattice is: **`T` has spectrum in `{1} ∪ [0, ρ]` with `ρ < 1`, in infinite volume**, `Δ = −log ρ`.
**E** is a Euclidean field theory on `ℝ⁴` satisfying the Osterwalder–Schrader axioms, obtained as the
limit of lattice Schwinger functions and reconstructed; **Y** is that limit of vanishing lattice
spacing with the gap held in physical units; **N** is a connected function of order three or more
that stays away from zero in the limit — the continuum theory is not a generalised free field.

## How we get there

**1. M on the lattice — the transfer gap on ℤ⁴ from cluster decay.**

    StrongCouplingGap.decay_of_orth  +  ClayCapstone.clay_gap_of_rayleigh
      per-vector decay  ‖Tqⁿ y‖ ≤ K_y · ρⁿ  on the vacuum complement  →  ‖Tq y‖ ≤ ρ ‖y‖
        →  opT self-adjoint,  spectrum ⊆ {1} ∪ [0, ρ],  1 the top

The constant is chosen per vector, so an absolute cluster estimate feeds it directly
(`SecondEigenvalue.norm_le_of_absolute_iterate_bound`).
`GaugeInvariantAlgebra.gaugeInv_form_pow` writes `form x (Tⁿ x)` as the reflected-shifted pairing
`ν(θ x · shiftⁿ x)` in the infinite-volume state, so the decay to supply is of that pairing.

| link | content | tree |
| --- | --- | --- |
| L1 | the infinite-volume state `ν` as the `atTop` limit of the free box states along `mixCube` (`htend`) | **built**: `FreeLimit.exists_tendsto_stateFree` — at `0 ≤ β` with `coreRate 64 β < 1` the free box states are Cauchy on every local observable (`FreeLimit.stateFree_cauchy`, from `BoxCompare.meanR_sub_abs_le` inside the union of two boxes, `FreeLimit.stateFree_eq_meanR`), the local observables are dense, and the subsequential limit of `ClayCapstone.exists_dlr_limit_of_free_family` is the `atTop` limit |
| L2 | a cluster bound for every continuous gauge-invariant local observable, with its constant depending on the observable | **built, in the box**: `BoxCube.stateFree_connected_abs_le_of_cubes` — for `f`, `g` local on disjoint link sets strictly inside two cubes of side `R` whose bases are more than `k` apart along an axis, `|⟨fg⟩ − ⟨f⟩⟨g⟩|_box ≤ coreConstG (2‖f‖‖g‖) 64 β U · coreRate 64 βᵏ⁺²⁻ᵁ`, `U = 32 (R + 1)⁴ ≤ k + 2`, with a right side free of the box and the boundary, for every box holding both supports and both cubes. General form: `StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball` |
| L3 | the box bound carried to `ν` | **built for every local observable**: `GeneralDecay.nu_connected_shift_abs_le_obs` — for `x` continuous and local on a finite set in `posHalf τ p`, there is `U` fixed by the support with `|ν(θx·Sᵐx) − ν(θx)ν(Sᵐx)| ≤ coreConstG (2‖x‖²) 64 β U · coreRate 64 β^(m+2−U)` for every `m ≥ U − 2` |
| L4 | per-vector decay → spectrum | **built and assembled**: `StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling` — at `0 < β` with `coreRate 64 β < 1` and `ν` the `mixCube` limit (`htend`), the gauge-invariant transfer operator is self-adjoint with spectrum in `{1} ∪ [0, ρ]`, `ρ = coreRate 64 β`: every vector orthogonal to the vacuum decays at `ρ` (`StrongCouplingGap.decay_of_orth`), so `‖Tq y‖ ≤ ρ‖y‖` and `ClayCapstone.clay_gap_of_rayleigh` applies |

**M on the lattice, assembled:** `FreeLimit.wilson_gaugeInv_mass_gap_lattice` — at every `0 < β` with
`coreRate 64 β < 1` there is an infinite-volume state `ν`, the `atTop` limit of the free box states,
at which the gauge-invariant transfer operator is self-adjoint with spectrum in `{1} ∪ [0, ρ]`,
`ρ = coreRate 64 β`, `1` at the top: a gap `Δ = −log ρ > 0`. `FreeLimit.exists_strong_coupling_region`
gives the interval `(0, b)` of such `β`. Axiom-clean.

**Per state, with content, at `SU N`, `2 ≤ N`:** `PlaneVariance.wilson_gaugeInv_mass_gap_lattice_nontrivial`
adds that every vector orthogonal to the vacuum is contracted, `‖Tq y‖ ≤ ρ‖y‖`
(`StrongCouplingGap.norm_Tq_le_of_orth`), and that there is a non-zero such vector. A plaquette in the reflection plane is fixed by the reflection
(`PlaneVariance.ireflPlaq_plane`), so its mean-subtracted class has squared norm equal to its variance in
`ν`, and that variance is at least `e^{−32β} · Var_Haar(reTr) / N²` in every free box
(`PlaneVariance.stateFree_var_iplaqObs_ge`) and so in `ν` (`PlaneVariance.nu_var_iplaqObs_ge`).
Axiom-clean.

**2. Y and M in the continuum — the entroptic read of the transfer operator.**

The read is Entroptics' instrument: a correlation profile over the lags of an aperture, its tension
`−log Σ p cos θ` set against the floor `κ₀YM = ¼·log 3` (`Moment.Read`). Below the floor the profile
cannot carry the infinitely extended mode a massless theory needs, and that is what fixes the rate
in physical units across spacings (`ZeroMode.rate_gt_of_tension`, `ZeroMode.gap_phys_of_fixed_screen`).
The read is made of the transfer operator's spectrum, and the chain from the read to the physical gap
is built, axiom-clean:

1. **Spectral measure** — `SpectralRep.exists_spectral_measure`: a self-adjoint operator with spectrum
   in `[0, 1]` and a vector `v` give one finite measure w_v on `[0, 1]` with `re ⟪v, h(a) v⟫ = ∫ h dw_v`
   for every continuous `h`; `SpectralRep.exists_moment_measure` is its moment form.
   `SpectralRep.cfc_apply_of_fixed`: a fixed vector is an eigenvector of the whole functional calculus.
2. **The read of a spectral measure** — `SpectralRead.lam0_pow_lt_of_tension`: a read whose correlation
   is `∫ g λ^{circLag d} dw` with a continuous weight `g ≥ 0` vanishing below `λ₀`, at tension below
   the floor, has `λ₀^{k+1} < 12(1 − 3^{−1/4})/8`.
3. **The transfer gap from the reads** — `SpectralGap.gap_of_reads`: if every vector orthogonal to the
   vacuum reads below the floor at aperture `2k + 1` (`SpectralGap.ReadsClear`), the vacuum complement
   is contracted at rate `ρ < 1` with `ρ^{k+1} = 12(1 − 3^{−1/4})/8`. A ramp `φ(a)` isolates any
   spectral weight above that level into a vector orthogonal to the vacuum whose read step 2 excludes
   (`SpectralGap.measure_gt_eq_zero`).
4. **On the Wilson transfer operator, at every coupling** — `WilsonReadGap.wilson_gap_of_reads`: at any
   `β ≥ 0` with infinite-volume state `ν`, the reads give the gap; positivity of the transfer comes
   from `ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit` at every `β ≥ 0`.
5. **In physical units** — `SpectralGap.uniform_physical_gap_of_reads`: apertures held at one physical
   extent `L = 2(k + 1)·a` give a physical gap of at least `−2·log(12(1 − 3^{−1/4})/8)/L ≈ 2.04/L` at
   every spacing.
6. **The entroptic input** — `SpectralGap.ReadsClear` at each spacing, with the aperture at a fixed
   physical extent: every vector orthogonal to the vacuum reads below the floor. At a fixed aperture
   this is the gap stated as a read: a vector's cosine average is the spectral average of the
   single-mode average, which vanishes at `1` (`ZeroMode.sum_cos_theta_eq_zero`), so `ReadsClear` keeps
   the spectrum on the vacuum complement out of a neighbourhood of `1`; at fixed physical extent it
   asks for a physical gap of about `10.99/L` (computed, not proved) and `gap_of_reads` returns
   `2.04/L`. The converse is
   built at a faster rate: `ReadConverse.readsClear_of_contraction` (a contraction at rate `r` with
   `3^{−1/4} < modeCosAvg k r` gives the reads, `ReadConverse.modeCosAvg_antitone`), and
   `ReadConverse.readsClear_brackets_physical_gap` brackets the gap at one window — the reads give at
   least `κ*/L`, a physical gap of at least `20/L` gives the reads, a factor about `9.8` apart. Supplying the
   reads along `β → ∞` is the mass gap in the continuum.

**3. The gap at every coupling.** `ReadRoute.wilson_gaugeInv_mass_gap_every_coupling`, axiom-clean: for
`SU(N)`, `2 ≤ N`, at every `β > 0` there are an infinite-volume state and `ρ < 1` with the
gauge-invariant transfer operator's spectrum in `{1} ∪ [0, ρ]`, every vector orthogonal to the vacuum
contracted by `ρ` — so `1` is a simple eigenvalue — and a non-zero vacuum complement
(`ReadRoute.ClayGapAt`). Below the cut `coreRate 64 β < 1` the cluster expansion supplies it
(`ReadRoute.clayGapAt_of_strong`); above it the single hypothesis `hweak` supplies the state and an
aperture at which the reads clear (`ReadRoute.clayGapAt_of_reads`).

**4. E — the continuum theory and its axioms.** What each OS axiom needs, and what is built toward it:

| axiom | built | to build |
| --- | --- | --- |
| reflection positivity (OS2) | positivity on the half-space algebra at every `β` for an ultrafilter limit of the free states, `ContinuumE.exists_reflPositive_state`, and at strong coupling for the `atTop` limit, `ContinuumE.wilson_lattice_os`; the Gram condition with real coefficients is closed under limits, `ContinuumE.gram_nonneg_of_tendsto` | the continuum Schwinger functions |
| clustering (OS4) | contraction of the vacuum complement and clustering of local observables, `ContinuumE.wilson_lattice_os`; closed under limits, `ContinuumE.clustering_of_tendsto` | the continuum Schwinger functions |
| translations (OS1) | shift invariance along the transfer direction, `ContinuumE.wilson_lattice_os` | the other three directions; the continuum group |
| rotations (OS1) | the lattice's axis permutations | rotation invariance of the limit |
| regularity (OS0) | `‖ν f‖ ≤ ‖f‖` on the lattice | smeared, renormalised fields with bounds uniform in the spacing |
| unique vacuum and gap | `ReadRoute.ClayGapAt` at every `β > 0` from `hweak`; `SpectralGap.uniform_physical_gap_of_reads` in physical units | `hweak` along `β → ∞` |
| reconstruction | GNS and transfer on ℤ⁴ (`GNSHilbert`), axiom-free | a reconstruction that ties its output to the Schwinger functions |

A physical-unit lower bound on the rate alone does not certify a continuum limit: at a fixed coupling
the physical rate diverges as the spacing falls (`ContinuumE.not_bounded_physical_rate_of_fixed_rate`),
so E needs the coupling to run with the spacing.

**5. N — not a free field.** A Gaussian is fixed by its two-point function, so a two-point quantity —
the read, a variance floor, the gap — cannot witness N. A gauge-invariant observable is a composite,
and a composite of a free field is non-Gaussian too, so N is a separation, uniform along the continuum
family, of a renormalisation-invariant connected quantity of order four, `|κ₄/κ₂²|`, from its value in
the free theory for the same gauge-invariant observable smeared at a fixed physical scale. The
invariant form for one observable is `NonGaussian.ContinuumNonGaussian`,
invariant under field renormalisation (`NonGaussian.kurtRatio_affine`,
`NonGaussian.continuumNonGaussian_renormalize`) and satisfiable (`NonGaussian.coin_continuumNonGaussian`).
A variance floor with a non-Gaussian law does not reach it (`NonGaussian.flat_floor_nonGaussian_not_continuum`).
On the lattice the plaquette's law is not Gaussian under every `mixCube` limit state at `β ≥ 0`
(`NonGaussian.nu_iplaqObs_law_not_gaussian`) and the vacuum complement is non-zero
(`PlaneVariance.exists_ne_zero_orth_vacuum`); the continuum witness is the order-four bound along the
family.

## Next

**Being built now:** `β → ∞` assembled from the tree's pieces into `ChessboardRead.TorusLagClear` along the
`aRun 3` family with a uniform physical rate; **E** — lattice Schwinger functions of smeared
gauge-invariant observables at spacing `aRun 3 β` under `PeriodicState.periodicState`, bounds uniform in
the spacing, a limit along `β → ∞`, its OS axioms, and reconstruction through `GNSHilbert`; **N** — the
free gauge theory's value of a smeared composite's higher connected statistic and a uniform separation
from it.

1. **`hweak` along `β → ∞`** — the reads at a fixed physical window, and the state. The reads bracket
   the physical gap at the window, `κ*/L` from the reads and `20/L` to the reads (`ReadConverse`).
   The reads at a uniform margin `γ > 3^{−1/4}` follow, under `htend`, from one inequality per
   gauge-invariant local observable on the free Wilson boxes, holding with every slack for all large
   boxes (`ReadReduce.BoxReadsClearWith`, `ReadReduce.wilson_clay_gap_of_boxReads`); observable by
   observable that is exactly the limit-state inequality (`ReadReduce.boxSlack_iff`), and it is the
   same target as the reads, not a weaker one.
   **The tower.** `GapStep.periodic_clay_tower`: at `2 ≤ N`, `0 < M` and couplings `βⱼ > 0`, the gap at
   rate `e^{−M·aRun N β₀}` at `β₀` and the step `GapStep.PhysStep` from each `βⱼ` to `βⱼ₊₁` give
   `PeriodicClayGapAt` at every `βⱼ` with physical rate `M`, `aRun N` the two-loop spacing of `SU(N)`;
   `GapStep.physStep_iff_lag` states the step at halved spacing as the lag-`2m` bound at `βⱼ₊₁` with the
   ratio of lag `m` at `βⱼ`, the same decay over the same physical separation. Given the base,
   `GapStep.gapAt_tower` turns the step at every level into the gap at rate `M` at every level, and the
   gap at every level makes every step true.
   **The target is centre-invariant.** On `ℤ⁴` a central height twist is a gauge transformation
   (`CentreTwist.heightTwist_eq_igaugeTransform`), so every gauge-invariant observable is twist-invariant
   (`CentreTwist.isIGaugeInvariant_heightTwist`); `CentreTwist.centre_invisible_SU`: for `2 ≤ N` a central
   `z ≠ 1` moves every configuration and fixes every member of `gaugeInvHalfSpaceAlg τ p`;
   `CentreTwist.torusObs_torusTwist` makes every torus observable of a gauge-invariant observable
   invariant under the torus centre twist. `CentreSector.gapAt_iff_sectors` splits `GapAt`, for any
   neutral projection, into a neutral and a charged one-lag bound, and
   `CentreSector.charged_rate_does_not_reach_neutral` gives abstract transfer data whose charged rate is
   `0` and whose neutral rate is free. The one-lag input is a bound on the gauge-invariant algebra, which
   contains no charged observable.
   **The weak-coupling input: the uniform physical gap.** `WeakCouplingWindow.FixedWindowDecay τ p hN L`:
   one factor `q ∈ (0, 1)` such that at every large `β` some lag `m` with `m·aRun N β ≤ L` has the
   connected reflected pairing of every member of `gaugeInvHalfSpaceAlg τ p` on the periodic lattices at
   most `q` times its lag-zero value. `WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay`: at `2 ≤ N`
   and `0 < L` it gives, at every large `β`, `GapAt` and `PeriodicClayGapAt` at a rate `r` with
   `−log r / aRun N β ≥ c/L` for some `c > 0` (the proof takes `−log q`);
   `WeakCouplingWindow.fixedWindowDecay_iff`: it holds exactly when that uniform physical gap does, and
   `WeakCouplingWindow.fixedWindowDecay_window_free` makes it the same condition at every `L > 0`. On the
   lattices, at `0 ≤ β` and `0 ≤ r`, `TorusLagClear` at any lag `m ≠ 0` is `GapAt` at the periodic data
   (`WeakCouplingWindow.torusLagClear_iff_gapAt`).
   **The base, at the periodic state — built.** At `0 ≤ β` with `coreRate 64 β < 1` the
   strong-coupling cluster bound holds on every periodic lattice of extent at least twice the separation
   of the two cubes, with the right side of the free boxes, which does not depend on the extent
   (`PeriodicStrongCoupling.torusState_connected_abs_le_of_cubes`), and passes through the ultrafilter to
   `PeriodicState.periodicState` (`PeriodicStrongCoupling.periodic_connected_shift_abs_le_obs`).
   `PeriodicStrongCoupling.periodic_gapAt_strong_coupling`: there is `β₀ > 0` such that at every
   `0 < β < β₀` the periodic data has `GapAt` at rate `coreRate 64 β < 1`;
   `PeriodicStrongCoupling.periodic_clayGapAt_strong_coupling` gives `PeriodicClayGapAt` there at
   `2 ≤ N`, and `PeriodicStrongCoupling.periodic_torusLagClear_strong_coupling` gives `TorusLagClear` at
   every lag. On `(0, β₀)` the headline's conclusion holds without the reads, `β₀` existential.
   `PeriodicStrongCoupling.periodic_tower_base` is the base `GapStep.periodic_clay_tower` takes: at every
   `β ∈ (0, β₀)` and every `M ≤ −log(coreRate 64 β) / aRun N β`, `GapAt` at `e^{−M·aRun N β}`.
   **The interval, sharpened.** Counting touch-connected sets by spanning-tree tours, `(4K)^(m−1)` of
   them (`StrongCouplingSharp.card_connSets_le_four`), and summing the pair weights in place of counting
   the splits (`StrongCouplingSharp.pairCover_le`) gives the rate
   `StrongCouplingSharp.coreRate' K β = 4K(e^{4β} − 1)e^{4βK}`, below one at `K = 64` on `[0, 1/1400]`
   (`StrongCouplingSharp.coreRate'_lt_one_of_le`), and `StrongCouplingSharp.periodic_gapAt_strong_coupling'`
   the periodic `GapAt` on that interval; `StrongCouplingSharp.periodic_gap_interval_exceeds_old` proves it
   more than twenty times every interval on which `coreRate 64 β < 1` (`StrongCouplingSharp.old_interval_le`).
   On it `PeriodicStrongCouplingSharp.periodic_clayGapAt_strong_coupling'` gives `PeriodicClayGapAt`,
   `PeriodicStrongCouplingSharp.periodic_torusLagClear_strong_coupling'` gives `TorusLagClear` at every lag,
   and `PeriodicStrongCouplingSharp.periodic_tower_base'` gives the tower's base.
   **The UV/IR split.** `UVIRSplit.UVLossStep`: a step from `β` to a finer `β'` carrying `GapAt` at physical
   rate `M` to rate `M − ε(aRun N β)`; `UVIRSplit.IRGapAt`: the gap at one coupling.
   `UVIRSplit.fixedWindowDecay_of_uv_ir`: the UV step with a loss budget `E` below the IR rate `M₀` gives
   `FixedWindowDecay`, reaching every large `β` from `β₀` by halvings and one
   partial step; `UVIRSplit.fixedWindowDecay_iff_irGapAt`:
   given the UV step with vanishing loss, `FixedWindowDecay` holds exactly when the gap holds at one coupling.
   The step's shape, with zero loss, holds on a gapless family (`UVIRSplit.lossStep_without_gap`) and
   fails on another (`UVIRSplit.lossStep_not_automatic`); with a loss equal to the largest attainable
   physical rate it holds trivially, so its content is carried by the vanishing loss or the budget
   `E < M₀`. At strong coupling the IR gap is proved at a rate unbounded as `β₀ → 0`, so the open content
   is the UV step across the crossover, and the IR gap carries content only past the strong-coupling
   region. `UVIRSplit.irGapAt_of_strong_coupling_chain` reaches the IR gap
   from the proved base `PeriodicStrongCoupling.periodic_tower_base` through finitely many crossover steps.
   Balaban's ultraviolet stability (Commun. Math. Phys. 119 (1988) 243; 122 (1989) 355, Theorem 1)
   bounds the block-spin effective densities on a torus by `exp(±E|T_η|)` with `E` independent of the
   step, the torus and the configuration, provided every running coupling stays below a small `γ`; it
   motivates the UV step. Open: the UV step as a statement on correlations, in infinite volume, with
   losses summing below the IR rate; and the gap at any single coupling outside strong coupling.
   **Past the crossover by a finite-size criterion.** `KnabeCriterion.knabe_bound` is Knabe's argument in
   weighted form: on a symmetric nonnegative form, self-adjoint idempotents `hᵢ` covered by patches with a
   local gap `γ` above the overlap excess give the global gap `(γa₁ − a₂ + b − e)/b`
   (`KnabeCriterion.PatchSystem.globalGap_of_localGap`). `KnabeCriterion.WilsonHeatBath` is the heat-bath of
   the periodic Wilson measures, the complements of the link conditional expectations, and
   `KnabeCriterion.fixedWindowDecay_of_patchGapCheck` gives `FixedWindowDecay` from
   `KnabeCriterion.HeatBathDecay` and `KnabeCriterion.PatchGapCheck` at one coupling `β₀` — a patch gap
   on one box of links under every boundary configuration — with the UV step `UVIRSplit.UVLossStep` only
   from `β₀` on. The UV step then runs in the weak-coupling regime alone. Open: `HeatBathDecay` (a uniform
   heat-bath gap gives decay), `PatchGapCheck` at a coupling past the strong-coupling region, and the UV
   step at weak coupling. **The heat-bath, built:** `HeatBath.heatAvg` is the single-link conditional
   expectation of the Wilson measure, with the DLR identity (`HeatBath.expect_heatAvg`), detailed balance
   (`HeatBath.expect_heatAvg_mul`) and commutation at links sharing no plaquette
   (`HeatBath.heatAvg_comm`); `BoxPatch.boxHeatBath` is a `KnabeCriterion.WilsonHeatBath` with box
   patches of side `n`, multiplicities `n⁴`, `n²(n − 1)²`, `n²(38n − 35)`, Knabe constant
   `(γn² − 40n + 36)/(n − 1)²` (`BoxPatch.knabeConst_box`), and
   `BoxPatch.patchGapCheck_of_boxPatchGap` makes the finite-size input `BoxPatch.BoxPatchGap`: a local
   gap above `(40n − 36)/n²` for every box patch operator, uniformly in the extent.
   **Being attacked now:** `FixedWindowDecay` at weak coupling; `E`; `Y`.
2. **An infinite-volume state at every coupling — built.** `PeriodicState.periodicState`: an
   ultrafilter limit of the `SU(N)` Wilson states on periodic lattices, read on `ℤ⁴`, reflection
   invariant at every constant, shift invariant, reflection positive at the even constant and (at
   `β ≥ 0`, `LinkGram.gram_refl_positive`) the odd one, so `PeriodicState.periodic_positiveTransfer`
   holds at every `β ≥ 0` with no uniqueness input. `PeriodicState.periodic_clay_gap_of_reads`: the reads
   at that state give the spectral statement at every `β ≥ 0`.
   **The headline, from the reads alone:** `PeriodicContent.wilson_gaugeInv_mass_gap_every_coupling_periodic`
   — for `SU(N)`, `2 ≤ N`, at every `β > 0` the Clay gap: spectrum in `{1} ∪ [0, ρ]`, the vacuum
   complement contracted by `ρ < 1`, and that complement non-zero (`PeriodicContent.PeriodicClayGapAt`);
   the reads at the periodic state are its only hypothesis. At any margin `γ > 0` the torus
   inequality is the gap itself — the contraction of the vacuum complement at the edge `r_γ(k)` of
   `modeCosAvg k`, endpoint included (`FloorRead.contraction_of_readsClearWith`,
   `FloorRead.readsClearWith_of_contraction`, `FloorRead.wilson_gaugeInv_mass_gap_every_coupling_any_margin`).
   **It is one lag:** the connected reflected pairing at one lag `m ≥ 1` at most `rᵐ` times its
   lag-zero value, `0 < r < 1`, for every gauge-invariant local observable on the periodic lattices,
   gives the Clay gap at `r` (`ChessboardRead.periodic_clayGapAt_of_torusLag`), because reflection
   positivity and positivity of the transfer make every lag profile log-convex
   (`ChessboardRead.lagProfile_log_convex`) and on the form that inequality is `GapAt` at the same rate
   (`ChessboardRead.gapAt_iff_lag`): the gap restated, not a weaker input. At `T = id` the bound forces
   a null vacuum complement (`ChessboardRead.lag_forces_null_of_T_eq_id`); reflection-positive `U(1)`
   lattice gauge theory with the Villain action has a massless phase at large `β` (Guth 1980;
   Fröhlich–Spencer 1982), so the estimate needs input beyond positivity.
   The complement comes from a plaquette-variance floor `e^{−128β}·varReTr N/N²` on every periodic lattice
   (`PeriodicContent.periodicState_var_iplaqObs_ge`), and the reads reduce to one inequality per
   gauge-invariant local observable on the periodic lattices (`PeriodicReduce.TorusReadsClearWith`,
   `PeriodicReduce.torusSlack_iff`, `PeriodicContent.periodic_clayGapAt_of_torusReads`).
3. **E** — the continuum Schwinger functions, at the periodic state. `ContinuumSchwinger.dyBeta` runs the
   coupling so that `aRun N (dyBeta k) = aRun N 1 / 2^(k+1)`; `ContinuumField.smear` smears a gauge-invariant
   local field with a test function at that spacing, bounded uniformly in the spacing
   (`ContinuumField.norm_smear_le`); the renormalisation `Z, c` is carried as data (`ContinuumSchwinger.Renorm`).
   Under `ContinuumSchwinger.UniformBound` the renormalised lattice Schwinger functions converge along one
   ultrafilter to `ContinuumSchwinger.contS` (`ContinuumSchwinger.tendsto_contS`), with OS0
   (`ContinuumSchwinger.exists_abs_contS_le`), OS1 on the dense dyadic subgroup of `ℝ⁴`
   (`ContinuumSchwinger.contS_translate`), OS2 (`ContinuumSchwinger.contS_gram_nonneg`) and OS3
   (`ContinuumSchwinger.contS_comp_equiv`); `ContinuumReconstruction.continuum_reconstruction` builds the
   Hilbert space, vacuum and self-adjoint transfer contraction with inner products equal to the Schwinger
   functions (`ContinuumReconstruction.inner_vecOf`); `ContinuumCluster.contS_cluster_of_fixedWindowDecay`
   derives OS4 in reflected form at physical rate `c/L` from `FixedWindowDecay`. `UniformBound` is proved for
   bounded renormalisation (`ContinuumSchwinger.uniformBound_of_bounded`), where the limit is degenerate in
   expectation: constants for the bare fields (`ContinuumReconstruction.continuum_reconstruction_bare`), zero
   for the connected composites. A non-degenerate limit needs a growing `Z`, and there the target is a
   uniform bound over families with separated supports, since `UniformBound` also covers coincident points,
   where Y's `r⁻⁸(log r)⁻²` is not integrable. **On separated supports:**
   `ContinuumSep.UniformBoundSep` bounds only the dyadic translates whose test-function supports are
   pairwise `d`-separated, one constant per family and per `d > 0`; `UniformBound` implies it
   (`ContinuumSep.uniformBoundSep_of_uniformBound`), and the chain runs on it: the limit
   (`ContinuumSep.tendsto_contS_sep`), OS0 (`ContinuumSep.exists_abs_contS_le_sep`), OS2
   (`ContinuumSep.contS_gram_nonneg_sep`) and the reconstruction on separated positive-time monomials
   (`ContinuumSep.continuum_reconstruction_sep`). **M in the continuum:**
   `ContinuumSep.continuum_gap_sep` — at `2 ≤ N` and a window `L > 0`, from `FixedWindowDecay`,
   `UniformBoundSep` and reflection-compatible data, there is `c > 0` such that at every dyadic step `m`
   the reconstructed transfer operator (self-adjoint by `ContinuumSep.continuum_reconstruction_sep`) has
   `1` the top of its spectrum, spectrum in `{1} ∪ [0, e^{−(c/L)·tₘ}]` and the vacuum complement
   contracted at that rate, `tₘ` the step length: a physical gap of at least `c/L` at every step.
   `ContinuumSep.exists_orth_ne_zero_sep` gives the reconstructed space a non-zero vector orthogonal to
   the vacuum under `ContinuumSep.ConnectedTwoPointNonzero`, so the space is not spanned by the vacuum.
   **Non-triviality from Y:** `ContinuumNontrivial.connectedTwoPointNonzero_of_af` — for a field `O`
   whose renormalised connected lattice kernel converges to `G(|p − q|)` on separated points
   (`ContinuumNontrivial.KernelConvergesSep`) with `ShortDistanceY.AFShortDistance G`, the cube-smeared
   connected field has a positive connected two-point function, so
   `ContinuumSep.ConnectedTwoPointNonzero` holds; `ContinuumNontrivial.exists_orth_ne_zero_of_af` gives the
   non-zero vacuum-orthogonal vector. **The capstone:** `ContinuumClay.continuum_gap_nontrivial` — on one
   reconstructed Hilbert space, at every dyadic step, the spectral gap of physical rate at least `c/L`
   and a non-zero vector orthogonal to the vacuum, from `UniformBoundSep`, `FixedWindowDecay`,
   `KernelConvergesSep` and `AFShortDistance`. **Invariance:** `ContinuumHypercubic.periodicState_axis`
   and `ContinuumHypercubic.contS_signed` (the hypercubic group W(B₄)),
   `ContinuumHypercubic.contS_translate_real` (all of `ℝ⁴`, under `ContinuumHypercubic.SupContinuousSep`,
   uniformly continuous test functions); `N = 1` is vacuous (`NOneVacuity.not_wilsonLatticeAF_one`).
   Open with them: `KernelConvergesSep` at `ContinuumNontrivial.rhoA` for a local gauge-invariant
   `tr F²` density (`ShortDistanceY.siteObs`, to be packaged as a `ContinuumField.LField`) and the
   identification of its limit with that of `ShortDistanceY.latticeTwoPoint`; `SupContinuousSep` and
   `UniformBoundSep` at a growing `Z`; the rotations off the hypercubic group
   (`ContinuumHypercubic.RotationOpen`). Open with them: `UniformBoundSep` at a growing
   `Z`, `ConnectedTwoPointNonzero`, rotation invariance (`ContinuumSchwinger.RotationInvariant`) and
   translation invariance off the dyadic subgroup.
4. **N** — the separated three-point statistic. `ThreePointN.sepRatio ν A B C` is the square of the
   connected three-point function of three composites over the product of their connected two-point
   functions; it is invariant under `X ↦ Z·X + b` in each argument (`ThreePointN.sepRatio_affine`), and
   it is `0` in the duality matrix model (`ThreePointN.freeSepRatio_of_duality`: any `J, K` that flip each
   composite and fix each propagator zero the Wick trace), the value the free gauge field's composite takes.
   The input is `ThreePointN.WilsonThreePointSeparation`, open at every `β > 0`:
   three plaquette blocks of physical size `ℓ` at base offsets `D` along two axes, at spacing `aRun N β`, with
   `sepRatio` at the periodic state at least `c > 0` at every large `β`.
   `ThreePointN.wilson_separated_from_free` separates it from the free value, and
   `ThreePointN.wilson_continuum_threePoint` gives, under every renormalisation whose cumulants converge
   with non-zero limiting two-point product, a non-zero limiting three-point function. A bounded-below
   ratio makes `tr F²` non-Gaussian and separates it from the free massless gauge field; a free massive
   field's quadratic composite also has a non-zero three-point function, and Y's short-distance
   behaviour (asymptotic freedom) separates Yang–Mills from it.

5. **Y** — short-distance agreement with asymptotic freedom. `ShortDistanceY.AFShortDistance G`:
   `r⁸·G(r)·(log r)² → C > 0`, the running-coupling form of the composite's two-point function; it is
   satisfiable (`ShortDistanceY.af_satisfiable`), strictly stronger than `r⁸G → 0`
   (`ShortDistanceY.suppressed_strictly_weaker`), and excludes every free form: the massless `C/r⁸`
   (`ShortDistanceY.not_af_freeMassless`), every massive scaling form `Φ(mr)/r⁸` with `Φ(0) > 0`
   (`ShortDistanceY.not_af_of_scalingForm`) and every pure power law (`ShortDistanceY.not_af_of_conformal`).
   `ShortDistanceY.coupling_mul_neg_log_aRun_tendsto` derives the exponent from the running coefficients,
   and `ShortDistanceY.af_along_aRun` reads Y as `r⁸G` falling like the square of the running coupling at
   `aRun N β`. On the Wilson family `ShortDistanceY.wilson_af_iff` makes the lattice form
   `ShortDistanceY.WilsonLatticeAF` equivalent to Y for the continuum two-point function, and
   `ShortDistanceY.wilson_yang_mills_separated` composes it with `ThreePointN.WilsonThreePointSeparation`:
   Y separates the continuum two-point function from every free composite, massless or massive, and N
   separates the lattice block composites from Gaussian laws and the free massless value.
   Open: `WilsonLatticeAF` and the convergence `ShortDistanceY.WilsonContinuumTwoPoint`.

## How to check

```
python research/code/lean_build.py build MassGap
python research/code/certify/lean_axiom_footprints.py scan
python research/code/certify/lean_derived_literals.py scan
python research/code/certify/doc_cites_live_declarations.py scan
python -m pytest research/code/tests -q
```
