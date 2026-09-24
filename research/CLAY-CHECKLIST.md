# The Clay proof — the checklist

Every claim here is read from the declaration. Every declaration on the route carries only
`Classical.choice Quot.sound propext`.

The proof is one chain in two halves. **Supply** builds a self-adjoint operator and bounds its
subdominant eigenvalue `Λ`. **Delivery** turns that bound into the mass gap, and the bar it must
beat is the entropy floor.

```
  SUPPLY                                        DELIVERY
  a self-adjoint operator                       Λ < lambdaThreshold
  + a Rayleigh bound Λ on the                        |
    vacuum's complement                              v
        |                             SecondEigenvalue.spectralAt_of_vacuum_rayleigh
        |                                            |
        +------------------ Λ -------------------->  v
                                      SpectralBound.SpectralAt β Λ
                                             |  spectralAt_iff: ↔ ρ(2) ≤ Λ²·ρ(0)
                                             v
                                      SpectralBound.confines_of_subdominant_bound
                                             v
                                      ApertureRoute.ConfinesAtAnAperture
                                             v
                                      ApertureRoute.FlagshipAt   — the gap
```

**The bar is derived, not chosen — there is no pin on this chain.**
`SpectralBound.lambdaThreshold = (1 − 3^(−1/4)) / (1 + 3^(−1/4))` is a closed form, and
`lambdaThreshold_sq` proves `lambdaThreshold² = LagTwoBound.lagTwoThreshold` by `rfl`. Its only
ingredient is `3^(−1/4) = e^(−κ₀)`, and `VortexCount.kappa0_is_the_surface_entropy_density` proves
`κ₀ = ¼·log 3` from the directed-surface count, both factors, with nothing measured and nothing fitted.
The `3` is the colour rank and the `4` is the spacetime dimension: the problem's own data.

So the aperture converts a spectral gap into a mass gap, and the number `Λ` must beat descends from
counting surfaces. Every constant on the chain is of this kind — a closed form with a derivation, not
a threshold anyone selected, and `Λ`, `r`, `ε` and `Δ` are all existential.

## Supply — the two routes to Λ

**The moment pencil is already built.** `MomentMeasure.opX` **is** `M`: the `H₀^{−1/2}` whitening is
performed by the GNS/completion construction and `H₁` is multiplication by `X`, so no matrix and no
operator square root appears. `isSelfAdjoint_opX` and `spectrum_opX_subset ⊆ Icc (−R) R` are proved,
and `Hankel.corrClay_hankel_psd` gives `H₀` positive semidefinite at every even extent `n = 2m`, every
real `β`, arbitrary finite index and arbitrary shifts below `m`. Nothing imports `MomentMeasure`; its
declarations are an unconsumed leaf.

It does not yet produce `Λ`. `MomentData.shift` supplies `R` as an **input**, from
`Schwinger.shift_two_le`, whose hypothesis is the geometric decay `|L k| ≤ B·R^k` itself — so
`spectrum_opX_subset` restates the decay rather than deriving it.

**The nearest close is on the periodic spectral form.** `SlabQuadratic.wilsonSpectral (hβ : 0 ≤ β)`
proves `WilsonSpectral 3 β` at every nonnegative coupling, foundational-only, giving a
`Spectral.PeriodicSpectralForm` with weights `w ≥ 0` and rates `0 ≤ λ ≤ 1`. **The mode count is
derived and it is two**: `PeriodicSpectralForm.Idx` is an arbitrary `Fintype`, and the witness
`SpectralFour` builds inside `LagOneDominates.wilsonSpectral_of_pair_and_quadratic` takes
`Idx := Fin 2`, from the quadratic inequality `2ρ(1)² ≤ ρ(2)² + ρ(0)ρ(2)` — which
`SlabQuadratic.wilson_quadratic` proves at **every real** `β`, the coupling sign entering only
through link-reflection positivity. Those are exactly the
`w`, `lam`, `hw`, `hlam0` that `MomentSupport.le_of_positive_weight_decay` consumes, and the consumer
is written: `Complete.ym_wilson_decay_to_half_period`. The one missing hypothesis is an **all-`τ`**
bound `∀ τ, ∑ w λ^τ ≤ M·ρ^τ`, where `wilsonSpectral`'s representation ranges over `Fin 4`. Joining the
two needs a finite-mode representation of `Schwinger`'s `L`, which is defined at every `k : ℕ` — that
is Curto–Fialkow flatness, and nothing proves it. `MassGap.lean` claims `Hankel.lean` carries a
Curto–Fialkow refutation; no such declaration exists.

**The GNS transfer operator** on the `ℤ⁴` half-space algebra, via R0–R2 below.

`entroptics` is the instrument for `Λ` on both routes: `hankel_spectrum` builds exactly this pencil
and returns `λ₁`, and `connected_decay_rate` returns `−log|μ₁|` of the mean-subtracted operator.
`aperture_reads.pencil_rate` is the mass-gap side's single call into it.

## Delivery — what is already proved

| declaration | what it gives |
|---|---|
| `SecondEigenvalue.spectralAt_of_vacuum_rayleigh` | from `hpos` and `hray` on a `TransferData`, plus the identification of `ρ(0)`, `ρ(2)`: `SpectralAt β Λ` |
| `SpectralBound.spectralAt_iff` | `SpectralAt β Λ ↔ (0 ≤ Λ ∧ wilsonCorrAt 3 β 2 ≤ Λ² · wilsonCorrAt 3 β 0)`, every real coupling |
| `SpectralBound.confines_of_subdominant_bound` | `LagSpectralBound Λ` with `Λ < lambdaThreshold` → `ConfinesAtAnAperture` |
| `ApertureRoute.flagship_of_confinement_at_an_aperture` | → `FlagshipAt`: the mode sum tends to zero, the tension stays below the floor at every coupling, the read is direction-independent, and a subsequence of the Schwinger functions converges |
| `Complete.gap_pos_iff_confinement` | `0 < ΔYM β ↔ μYM β < κ₀YM` |

Delivery is built. What remains is `Λ`.

## The chain to Λ through the transfer operator

```
  an infinite-volume Wilson state                          exists unconditionally
        |   WilsonState.exists_wilson_infinite_volume_state   (N ≠ 0, every real β)
        v
  + htend, along atTop for the interleaved mixCube family            [ R0 ]
        v
  ReflectionHalfSpace.wilson_transferData_of_thermodynamic_limit
        |   TransferData on halfSpaceAlg from htend alone. The three state facts are proved.
        v
  + hfin  (finite-volume connected decay, rate r < 1)                [ R1 ]
        v
  ReflectionHalfSpace.gapAt_of_finite_volume_connected  →  TransferGap.GapAt D r
        v
  GapToOperator.spectrum_opT_subset  →  spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (−r) r
        |
        |   + 1 ∈ spectrum ℝ (opT D)        GNSHilbert.one_mem_spectrum_opT   — proved
        |   + Icc (−r) r → Icc ε (exp (−Δ))                               [ R2 ]
        v
  OpTBridge.reconstruct_from_opT
        → IsSelfAdjoint H ∧ 0 ≤ H ∧ 0 ∈ spectrum H ∧ spectrum H ⊆ {0} ∪ Set.Ici Δ
```

## R0 — the thermodynamic limit

Proved: `WilsonState.exists_wilson_infinite_volume_state` (a state and a representing probability
measure, every `N ≠ 0`, every real `β`); `WilsonDLR.exists_wilson_infinite_volume_gibbs_measure`;
`DLRLimit.exists_limit_state` (compactness, per observable);
`ReflectionHalfSpace.wilson_reflPositive_limit_exists` (supplies a limit state with `ReflPositiveOn`,
no convergence hypothesis); `WilsonDLR.tendsto_specState_at_zero` (an `atTop` limit at `β = 0`).

Remaining: `∀ f, Tendsto (fun n => stateFree … β (mixCube τ p n) 1 f) atTop (nhds (ν f))`.
`mixCube_ultrafilter_sees_one_parity` shows an ultrafilter meets one parity class, and
`eq_empty_of_stable_two_mirrors` shows two families are forced, so the upgrade is a parity argument.
`wilson_positiveTransfer_of_common_subsequential_limit` states the same content as: the two families'
limits can be chosen equal.

## R1 — the finite-volume connected decay

`hfin`: for every `F ∈ halfSpaceAlg τ p`, eventually along the box family, each box subtracting its
own mean, `⟨θ_{2p−2}F·F⟩ₙ − ⟨F⟩ₙ⟨θ_{2p−2}F⟩ₙ ≤ r²·(⟨θ_{2p}F·F⟩ₙ − ⟨F⟩ₙ⟨θ_{2p}F⟩ₙ)`, `r < 1`.
Proved at `β = 0` by `WilsonState.gapAt_zero_at_zero_coupling`, through
`WilsonState.refl_pairing_at_zero_eq_zero` — which quantifies over **every** `F ∈ halfSpaceAlg τ p`
and gives `= 0`, by disjoint-support factorisation
(`HalfSpaceAlgebra.disjoint_image_ireflLink_posHalf` at `2p−2`, with `WilsonDLR.dlr_mul_at_zero`).
That is the template a `β > 0` argument follows.

`WilsonState.stateFree_eq_spec_at_zero_coupling` identifies the free-boundary and fixed-boundary
measures at `β = 0`: `stateFree` sums the action over `iplqAll Λ` and `GibbsSpec.spec` over
`boundaryPlaqs Λ`, sets `GibbsSpec.boundaryPlaqs_ne_plaqsIn` shows differ, and at zero coupling both
collapse to the same Haar integral. That is what lets `WilsonDLR.dlr_unique_at_zero` — the tree's only
uniqueness — and `tendsto_specState_at_zero` — its only `atTop` limit — speak about the
free-boundary family.

The engine is `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`, carrier-free over
abstract `{Lk Pq : Type}`. `StrongCoupling.nonbridging_sum_eq_zero` and `wilsonCorrConn_eq_bridging_sum`
are exact finite identities at every `β`, by a sign-reversing involution.

`ContactFloor.contact_relative_unconditional` carries no hypothesis: `∃ b > 0`, `∃ C ≥ 0`, with
`wilsonCorrAt N β d ≤ C · wilsonCorrAt N β 0 / circLag d ^ 4` at every aperture for `β ∈ [0, b]`.
`ContactValue.corrClay_zero_at_zero_value` reads `corrClay (m+2) 0 0 = 1/18`.

Instantiating the engine at the `ℤ⁴` box:

| | obligation | status |
|---|---|---|
| 1 | `touchDeg (boxBd Λ) ≤ 16 * 4` | proved — `ReflectionHalfSpace.touchDeg_boxBd_le` |
| 2 | the ball condition `q ∉ ball (boxBd Λ) p₀ k` | proved — `ReflectionHalfSpace.not_mem_ball_of_axis_gt`, by the axis coordinate |
| 3 | plaquette observables → every `F ∈ halfSpaceAlg τ p` | remaining |

Obligation 3 is a coordinate gap: `corrClay` is one plaquette pair on the periodic lattice, `hfin`
quantifies over `halfSpaceAlg` on `ℤ⁴` against `stateFree`. No module names both.

It will not close by generation. `halfSpaceAlg τ c` is a locality predicate — `F` local on some finite
link set inside `posHalf τ c` — and it contains the gauge-non-invariant `halfLinkObs`, so plaquettes
provably cannot generate it. The reduction the tree already uses is per-observable support
extraction: `InfiniteReflection.reflPositive_of_eventually_pointwise`, whose pattern is
`obtain ⟨S, hS, hfloc⟩ := mem_halfSpaceAlg.mp hf` and then an eventual box hypothesis.

`LogConvex.corrHyper_log_convex` bounds connected correlators at two separations at every real `β`
with constant one, from reflection positivity and Cauchy–Schwarz; log-convexity makes `ρ(k+1)/ρ(k)`
non-decreasing, so the decay comes from the coupling.

## R2 — the spectral bridge

`GNSHilbert.one_mem_spectrum_opT : (1 : ℝ) ∈ spectrum ℝ (opT D)` — proved, unconditional on any
`TransferData`, from `opT_Omega` and `Omega_ne_zero`.

**Positivity already reaches the spectrum**, and the chain is composed:
`GNSCompare.spectrum_opT_subset_of_positiveTransfer_of_rayleigh` takes the two open inputs and
returns the containment.

```
  GNSHilbert.PositiveTransfer D
    → GNSCompare.inner_Tq_nonneg_of_positiveTransfer
    → SecondEigenvalue.norm_Tq_le_of_rayleigh            [+ the Rayleigh ceiling Λ]
    → GNSCompare.gapAt_of_positiveTransfer_of_rayleigh   ⇒ GapAt D Λ
    → GapToOperator.spectrum_opT_subset                  ⇒ spectrum ℝ (opT D) ⊆ {1} ∪ Icc (−Λ) Λ
```

**There are two open inputs on this chain, not one.** `Λ` is the Rayleigh ceiling.
`GNSHilbert.PositiveTransfer D` is the other, and it is open for every non-trivial `D`:
`positiveTransfer_trivial` discharges it only where `T = id`, and
`WilsonTransferReduction.positiveTransfer_of_state_facts` needs
`hposOdd : ReflPositiveOn (latticeReflection τ (2p−1)) (halfSpaceAlg τ p) ν` — reflection positivity
about the **odd** plane — which nothing supplies. `positiveTransfer_iff_odd_reflPositive` proves the
two **equivalent**, so that hypothesis cannot be weakened away. What
`wilson_positiveTransfer_of_mixCube_limit`, `…_of_odd_limit` and
`…_of_common_subsequential_limit` give is the same content behind a limit hypothesis, which is R0. `SecondEigenvalue.norm_le_of_rayleigh_le` uses no compactness, no completeness,
no finite dimension and no spectral theorem. So `Transfer.TransferData.eigenvalue_nonneg` does not
need carrying to the completion: nothing on this route consumes it.

What remains after `Λ` is a strictly positive lower bound `ε`, then `Δ = −log r` — the latter built,
`Reconstruction.hamiltonian T := cfc (fun x => −Real.log x) T`, applied inside `reconstruct_from_opT`,
with `hamiltonian_nonneg` and `hamiltonian_mass_gap` the pieces.

`Icc (−Λ) Λ` admits `0`, and `TransferInvertibility.isUnit_of_spectral_hypothesis` shows `ε` is
exactly `IsUnit (opT D)`. `TransferInvertibility.spectral_hypothesis_of_band` states that precisely:
given the band, `spectrum ⊆ Ici 0`, `0 ∉ spectrum` and compactness of the spectrum, it **produces**
`reconstruct_qm_core`'s `hsp` with `Δ = −log Λ`, the gap being the band's own width read
logarithmically. It is a **restatement, not progress**: `zero_not_mem_spectrum` runs the other
direction, so with the band in hand `hsp`, `0 ∉ spectrum` and `IsUnit (opT D)` are one fact in three
forms. What it buys is that the obligation is now a single non-membership rather than an existential
entangled with `Δ` — attackable by a lower bound `c‖x‖ ≤ ‖opT D x‖`, or by invertibility read off
the transfer structure, either of which must avoid routing back through `hsp`.
`exists_pos_lower_bound_of_compact` is the analytic half: a compact set inside `Ici 0` missing `0`
attains a positive minimum, so `ε` is a member of the spectrum and never a chosen constant.

**`spectrum ℝ (opT D) ⊆ Set.Ici 0` is proved.** It was an open input and it is now
`GNSHilbert.spectrum_opT_nonneg`, foundational-only, from `PositiveTransfer D`. The route is
`GNSHilbert.isPositive_opT` — Mathlib’s positivity predicate for an operator on an inner-product
space, whose two components are `isSelfAdjoint_opT` read as symmetry and `re_inner_opT_nonneg`, the
argument order reconciled by that same symmetry at `(x, x)` — then that class’s spectrumRestricts,
then nnreal_iff, whose right-hand side is literally the containment. Before this, no declaration in
the tree, for any operator, went from a nonnegative quadratic form to spectral nonnegativity;
`RefinementLaw` took it as a binder five times.

With `spectrum_opT_subset_unit_interval` the spectrum now sits in `[0, 1]`, and
`isGreatest_one_spectrum_opT` puts its maximum at the vacuum. **The only question left about the
spectrum is whether `0` belongs to it.**

**And `ε` is not an obligation — it was never the right requirement.**
`GNSCompare.spectrum_opT_gap_form` proves
`spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (exp (−Δ))` at `Δ = −log Λ > 0`, from the Rayleigh ceiling
and `PositiveTransfer` alone. That is Clay’s `spectrum ℝ H ⊆ {0} ∪ Ici Δ` transported through
`T = exp(−H)` — **with `0` admitted**, because a theory whose energies are unbounded has a transfer
spectrum accumulating at zero. `reconstruct_qm_core`’s `hsp` demands `Icc ε (exp (−Δ))` with
`0 < ε`, which by `energies_bounded_of_spectral_hypothesis` is a ceiling on the energies and by
`isUnit_of_spectral_hypothesis` is `IsUnit (opT D)`. No quantum field theory has that ceiling. The
Lean side says the same: `Reconstruction.hamiltonian` is `cfc (fun x => −Real.log x) T`, and
`−log` is not continuous at `0`, so `ε` is what buys the bounded-operator functional calculus its
continuity — not what buys the gap.

**So R2’s open inputs are `Λ` and `PositiveTransfer`, and the capstone states exactly that.**
`ClayCapstone.clay_gap_of_rayleigh` takes those two on any `TransferData` and returns the spectral
content of a mass gap: `opT D` self-adjoint, `0 < −log Λ`, `spectrum ⊆ {1} ∪ Icc 0 (exp (−Δ))`, and
`1` its greatest element. `ClayCapstone.wilson_clay_gap_of_rayleigh` is that at `SU(N)` on `ℤ⁴`,
with `PositiveTransfer` discharged by `ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit`
from convergence of the free-boundary states along one exhausting family of boxes — so its only
remaining hypothesis is the Rayleigh ceiling. Arbitrary `N ≠ 0`, four dimensions, no named axiom.
`ClayCapstone` is the first module to import both `GNSCompare` and `ReflectionHalfSpace`;
`GNSCompare` had no importers at all, which is why the join had never been made. What the ε route still buys is the statement
phrased on a bounded Hamiltonian; reaching `MassFinite.clayMass` from the containment above needs an
unbounded functional calculus instead, which is a separate development from the one
`Reconstruction` carries.
One side condition of the ε step is a library matter rather than a fact about Yang–Mills: spectrum
compactness and closedness both exist at this pin, but instance search for a normed algebra over the
reals on the operator algebra does not terminate here, so `spectral_hypothesis_of_band` keeps
compactness as a hypothesis. **The question that decides it is whether `opT D` is compact.**
`spectral_hypothesis_fails_for_compact` proves a compact operator on an infinite-dimensional space
satisfies the containment at no `ε`, `Δ`. `IsCompactOperator` occurs in that file alone and only as a
hypothesis; no operator in the tree is shown compact and no space is shown finite- or
infinite-dimensional. Settling that one fact decides whether `reconstruct_from_opT` is reachable as
stated. `SlabTransferAdjoint.zero_mem_spectrum_slabNormal_of_beta_zero` and
`WilsonState.gapAt_zero_at_zero_coupling` are the `β = 0` case, where the spectrum reads `{1} ∪ {0}`.

`GNSHilbert.spectrum_opT_subset_unit_interval` bounds the spectrum with no gap hypothesis at all
— contractivity is the whole input — and with `one_mem_spectrum_opT` gives
`GNSHilbert.isGreatest_one_spectrum_opT : IsGreatest (spectrum ℝ (opT D)) 1`: the vacuum eigenvalue
is the **maximum** of the spectrum on any `TransferData`. That fixes what the gap is measured below.
`RefinementLaw.isGreatest_refined` is the tree's only hypothesis-position consumer of that shape and
is not reachable from it: it also takes `∀ x ∈ spectrum ℝ T, 0 < x`, which is `0 ∉ spectrum`, which
`TransferInvertibility.isUnit_of_spectral_hypothesis` ties to `IsUnit (opT D)` — the `ε` obligation
itself.

What is still unwritten is a consumer taking `spectrum T ⊆ Icc (−ρ) ρ` on the vacuum complement with `ρ < 1` and returning gap
`−log ρ`, which is what a connected-correlator operator needs in place of `reconstruct_gapped`'s
`{1} ∪ Icc ε (exp (−Δ))`.

`GNSCompare.spectrum_opT_strict_band` is the same chain at `Λ < 1`, which is where it carries
content: at `1 ≤ Λ` the containment says nothing `spectrum_opT_subset_unit_interval` does not already
say with no hypothesis, and `TransferGap.gapAt_of_one_le_sq` makes `GapAt D Λ` automatic there. It
returns the containment, the maximum at the vacuum, and the gap `−log Λ` — stated at `0 < Λ`, since
`Real.log 0` is the junk value `0`.

`OpTBridge.reconstruct_from_opT` still has no consumer, and the reason is the `ε` obligation: its
`hsp` is `{1} ∪ Icc ε (exp (−Δ))` with `0 < ε`, while this chain delivers `{1} ∪ Icc (−Λ) Λ`, which
admits `0`.

## R3 — the continuum limit

Built: `Schwinger.exists_infinite_volume_bounded_moment_data`, with no hypotheses — a contact floor,
Hankel positive-semidefiniteness at every finite family of lags, a geometric bound and summability,
along a subsequence of odd apertures at every `β ∈ [0, b)`. And
`MomentMeasure.exists_infinite_volume_representing_measure` — a `MeasureTheory.Measure ℝ` with
`∫ x^k ∂μ = L k`, compactly supported and nonzero, with `opX`, `spectrum_opX_subset`,
`spectralMeasure`, `rieszMeasure` behind it.

The spacing-to-coupling tie is `AsymptoticScaling.aRun` with `AsymptoticScalingAt`.

Remaining: both limiting objects are volume limits at fixed coupling, on `ℝ`. What is needed is a
limit as the spacing tends to zero, carrying an object on `ℝ⁴`.
`ClayAssembly.scaling_as_stated_is_vacuous` and `AsymptoticScaling.free_spacing_scaling_is_also_vacuous`
show the existential spacing clause is met by `a := m`, `mphys := 1`, so the statement is the work.

## R4 — the Wightman end

Built: `WilsonOS.osDataOfReflForm` from any `Transfer.ReflForm`, and `WilsonOS.wilsonOSData` at
`ReflectionStrong.wilsonGibbsReflForm`, the `SU(N)` Wilson Gibbs reflected form on the slab algebra,
at any real `β`. `wilsonOSData_S` and `osDataOfReflForm_S` are `rfl` identities giving
`D.S c c' = P.form (combo v c) (combo v c')`, so the Schwinger form is the Wilson form.
`wilson_reconstructed_nontrivial` and `wilson_reconstructed_vacuum_energy_zero` carry it through.

Remaining: a clause relating `D.S` to the output of `os_reconstruction_wightman`, whose type mentions
`D` once; `reconstruction_type_is_inhabited = fun _ => trivialWightmanQFTData` sits at that type as
the tripwire. `theta` and `transl` are the identity in every `OSData`, and
`LatticeTranslNoGo.transl_eq_id_of_finite_order` shows that is forced on a lattice, `E4` being
divisible, so Euclidean invariance is a property of the limit.

Mathlib carries GNS (*Analysis/CStarAlgebra/GelfandNaimarkSegal.lean*). Osterwalder–Schrader is on
its thousand-theorems list with no declaration, so R4 is a citation with a linking clause or a
formalisation Mathlib does not have.

## R5 — the gauge group

The operator carrier is general `SU N`. The aperture carrier is `SU(3)`, fixed in
`WilsonBridge.corrClay := corrHyper (d := 4) 3 n 0 1 2`.

## The keystone — `Λ` itself

The one thing both halves meet at. `hray : ∀ y, ⟪vac, y⟫ = 0 → ⟪Tq y, y⟫ ≤ Λ‖y‖²` has eleven
consumers and no producer:
`SecondEigenvalue.{norm_Tq_le, Tq_pow_norm_le, tendsto_zero, inner_Tq_two_le, lag_two_ratio_of_vacuum,
spectralAt_of_vacuum}_of_rayleigh`, `PeriodicRayleigh.{inner_pow_le, periodicCorr_le,
periodic_decay}_of_rayleigh`, `GNSCompare.{gapAt_of_rayleigh, gapAt_of_positiveTransfer_of_rayleigh}`.
`PeriodicRayleigh.one_le_of_rayleigh_le` shows the vacuum guard is load-bearing.

## Built, and connected to nothing

| asset | what it is |
|---|---|
| `HaarMoments.transferOp` | `X ↦ ∫ g*Xg = ½·tr(X)·I` — fixes the vacuum and annihilates its complement, which is `GapAt`'s shape at `r = 0`. Referenced only in its own file. Lifting it to `A →ₗ[ℝ] A` with a `ReflForm` gives the cheapest non-trivial `TransferData` |
| `SliceTransferSelfAdjoint.transferCLM` | a self-adjoint `ContinuousLinearMap` on `L²` from the OS Boltzmann kernel, injective, not a translation. Four steps short of a `TransferData`: operator positivity on `L²`, temporal gauge, the `Fin n` Fubini regrouping, a carrier bridge |

## `Λ` — the one number, and everything that already surrounds it

A sweep of the whole workspace, by type shape rather than by name, settles where this stands.

**In Lean, `Λ < 1` on a reflection-positive transfer form is a binder everywhere.** `GNSCompare`,
`SecondEigenvalue`, `PeriodicRayleigh`, `GapToOperator`, `WilsonTransferReduction` and
`ReflectionHalfSpace` all consume it; none produces it. `TransferGap.gapAt_of_one_le_sq` concludes
`GapAt` but only where it has no content, and `TransferGap.exists_gapAt_lt_one` concludes it on a
hand-built two-dimensional diagonal witness with no gauge content. **The only `GapAt … r < 1` on
genuine Wilson data is `WilsonState.gapAt_zero_at_zero_coupling`, at `r = 0` and `β = 0`** — the
degenerate point, where the reflection pairing vanishes identically.

**Three assets surround the hole.**

| what | where | status |
|---|---|---|
| the named target | `B2Locality.ConnectedRadiusAtCellCeiling D` = `∀ F, GapAt (D F) (3^(−1/4))` | a `Prop`, unproved |
| a scaffold that concludes `< 1` | `Mixing.interior_mixing_of_analytic_grid` | proved; **never instantiated** |
| the grid it consumes | `research/data/9_4_dat_interior_mixing_grid.csv` | measured, committed |

**The scaffold is now joined to the chain.** `ClayCapstone.rhoOne D V β` defines `ρ₁` as
`SecondEigenvalue.lambdaTwo (D β).Tq (V β)` — the subdominant Rayleigh supremum of a
coupling-indexed family of transfer data, as a function `ℝ → ℝ`. The half-space algebra is a
locality predicate and carries no coupling, so the family sits over a fixed algebra and only the GNS
space varies. `ClayCapstone.clay_gap_on_interval` runs `Mixing.interior_mixing_of_analytic_grid`
into `clay_gap_of_lambdaTwo` and returns **the gap at every coupling in the interval**. The bridge
from the number to the vector bound, `SecondEigenvalue.rayleigh_le_of_lambdaTwo_le`, was already in
the tree with no consumers.

**The coupling interval is a route, not a requirement.** `ClayCapstone.clay_gap_of_gapAt` takes
`TransferGap.GapAt D r` with `r < 1` and `PositiveTransfer`, and returns the same four conjuncts —
no Rayleigh ceiling, no subdominant supremum, no Lipschitz modulus, no grid. It runs
`GapToOperator.spectrum_opT_subset` into `GNSHilbert.spectrum_opT_nonneg`. **That is the form the
rest of the tree already produces**: `ReflectionHalfSpace.gapAt_of_finite_volume_connected` builds
`GapAt` for the Wilson transfer data out of R1’s `hfin`, a finite-volume connected-correlator
inequality. So R1 reaches the gap without passing through any of the ρ₁ machinery.

**That wiring is done.** `ClayCapstone.wilson_clay_gap_of_gapAt` takes `GapAt` below one on the
Wilson data and returns the four conjuncts, with `PositiveTransfer` discharged from the
thermodynamic limit. The two producers build `transferData_of_state_facts τ p ν hinv hpos hnu` from
different proofs of the same three state facts; those are `Prop`s, so definitional proof irrelevance
makes the terms equal, and an `example` beside the theorem checks that by `rfl` rather than asserting
it.

So the short route is closed end to end: R1’s `hfin` → `gapAt_of_finite_volume_connected` → `GapAt`
→ `wilson_clay_gap_of_gapAt` → the gap. **Its one open input is `hfin` at some `r < 1`, and what that demands is now precise.**

`hfin` must hold for **every** `F ∈ halfSpaceAlg τ p`, and that algebra is strictly larger than the
gauge-invariant one: `HalfSpaceAlgebra.halfLinkObs l f` is an arbitrary continuous function of a
single link variable, and `halfLinkObs_mem` puts it in `halfSpaceAlg` for every link of the positive
half and every `f`. No gauge-invariant sub-predicate exists anywhere in the tree — `LocalGauge`
proves invariance of specific objects (`plaqObs`, `wilsonAction`, `corrClay`) on the periodic
lattice, and defines no invariant algebra.

**That is why the strong-coupling machinery does not reach `hfin`.**
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` is carrier-free over abstract link and
plaquette types, but its subject is `WilsonBridge.wilsonCorrConn bd p₀ β pd` — a **plaquette-pair**
connected correlator, `p₀ pd : Pq`. It bounds two plaquettes, not an arbitrary local observable, so
no instantiation of it discharges `hfin`. And `GapAt` is quadratic in `F`, so a bound on a
generating set does not extend by linearity either.

So closing `hfin` needs one of: a cluster expansion for arbitrary local observables; or a
`TransferData` built on a smaller, gauge-invariant local algebra, where the plaquette bounds do
apply and where the mass gap is the physically meaningful statement. The second changes what the
theorem is about and should be a deliberate choice rather than a convenience.
**The second route is structurally open, and that is checkable rather than a judgement call.**
`WilsonTransferReduction.transferData_of_state_facts` is not a bespoke construction — it is
`assembleTransferData` applied to `halfSpaceAlg`, and that builder **takes the algebra as an
argument**, together with reflection invariance of the state, reflection positivity ON that algebra,
shift compatibility, shift stability of the algebra, membership of `1`, and two norm bounds. A
gauge-invariant local subalgebra would supply every one of them cheaply: reflection positivity on a
SUBSET follows from it on the superset; gauge invariance survives lattice translation, so shift
stability is inherited; and the unit is invariant.

What is missing for it is the gauge action itself on the infinite lattice. `LocalGauge` defines
`gaugeTransform` and proves invariance of `plaqObs`, `wilsonAction` and `corrClay` on the PERIODIC
lattice, and nothing carries it to `ℤ⁴`. So the work is: an infinite-lattice gauge action, an
invariance predicate, the subalgebra, and its three closure facts.

**That is done.** `MassGap/GaugeInvariantAlgebra.lean` carries `LocalGauge`’s action to `ℤ⁴` as
`igaugeTransform g U l = g l.2 · U l · (g (ishift l.1 l.2))⁻¹`, with `IsIGaugeInvariant` quantified
over **every** gauge function — the local group, not the centre. `ishiftConf_igaugeTransform` is the
translation covariance, and its whole content is `InfiniteShift.ishift_comm`.

`igaugeInv` is a `Submodule` (the gauge action is applied to the argument, so linearity passes
through), `gaugeInvHalfSpaceAlg τ c = halfSpaceAlg τ c ⊓ igaugeInv`, and its three closure facts are
proved: `gaugeInvHalfSpaceAlg_le`, `one_mem_gaugeInvHalfSpaceAlg`,
`gaugeInvHalfSpaceAlg_shift_stable`. `reflPositiveOn_gaugeInv` **restricts** reflection positivity
from the larger algebra rather than re-proving it — the point of the route.

**And the transfer data is built.** `gaugeInvTransferData` is
`TransferAssembly.assembleTransferData` on the invariant algebra; six of its nine inputs are shared
with `transferData_of_state_facts` verbatim. `ClayCapstone.clay_gap_of_gapAt` is generic over any
`TransferData`, so it applies to this one with no new wrapper.

**What the route now needs**, and both are on the smaller algebra: `PositiveTransfer` and `GapAt`
below one. `hfin` there no longer has to hold for `halfLinkObs l f` — an arbitrary continuous
function of a single link variable — which is what put it out of reach of the plaquette-pair
strong-coupling bounds.

**And the algebra is not just the constants.** `ihol_igaugeTransform` proves the plaquette holonomy
conjugates — `ihol q (igaugeTransform g U) = g x · ihol q U · (g x)⁻¹` at the base site `x = q.2`.
The four boundary factors cancel in adjacent pairs; the step that is not formal is the far corner,
where the second and third factors agree only because `InfiniteShift.ishift_comm` makes their target
the same site. That is the loop closing. `isIGaugeInvariant_of_classFun` then makes any
conjugation-invariant function of the holonomy gauge invariant, and
`WilsonAction.wilsonDensity_conj` is one — so the invariant algebra contains genuine plaquette
observables and the route is not vacuous.

A trap worth recording: `ishift` is defined **twice**, in `InfiniteLattice` and in `GibbsSpec`.
`igaugeTransform` uses one and `GibbsSpec.ibd` the other, so a rewrite with `ishift_comm` was inert
on half the term. They are definitionally equal and a `rfl` bridge in the simp set fixes it.

**And membership is proved.** `mem_gaugeInvHalfSpaceAlg_of_classFun` puts a conjugation-invariant
function of the holonomy of a plaquette whose links lie in the positive half into
`gaugeInvHalfSpaceAlg`: locality is `GibbsSpec.ihol_congr`, invariance is
`isIGaugeInvariant_of_classFun`. The observable is taken as a `C(IConf G, ℝ)` named by a hypothesis,
so continuity of the holonomy — which nothing in the tree states — does not enter; a caller
exhibiting a concrete observable supplies it.

**Every hypothesis but one restricts for free.** `reflPositiveOn_gaugeInv`,
`positiveTransfer_gaugeInv` and `gapAt_gaugeInv_of_gapAt` all transport from the locality algebra to
the invariant one, because each predicate is universally quantified over the algebra and both
transfer data compute the form and the shift on the underlying continuous map. The last of those does
not help prove the gap — it says the demand on the smaller algebra is **weaker**, which is the point.

**What producing it would take.** `ReflectionHalfSpace.gapAt_of_finite_volume_connected` is two
pieces: `InfiniteReflection.connected_pairing_le_of_eventually`, which **takes the algebra as an
argument** and so already applies to the invariant one, and
`WilsonTransferReduction.gapAt_iff_subtracted_pairing`, which is stated at
`transferData_of_state_facts` on `halfSpaceAlg`. Generalising that iff over the algebra is the
concrete next task, and it is the same generalisation `TransferAssembly.assembleTransferData` already
has. With it, an `hfin` quantified over gauge-invariant observables would give `GapAt` directly.

**That generalisation is done.** `GaugeInvariantAlgebra.gaugeInv_gapAt_iff_subtracted_pairing`
states `GapAt` on the invariant transfer data as a pairing inequality, and
`ClayCapstone.gaugeInv_clay_gap_of_pairing` composes the whole route into one signature whose only
input is that inequality. **The gauge-invariant route is structurally complete end to end.**

Reading the remaining obligation: for every observable local in the positive half and invariant under
the local gauge group, moving the reflection plane out by two costs a factor `r²` in the
mean-subtracted pairing. That is the gap in the coordinates the box family works in, asked on an
algebra with no arbitrary single-link observables in it.

**Where that obligation has to be attacked.** `GapAt` is **quadratic** in the observable, so a bound
proved for plaquette observables does not extend to their span by linearity — which is what stopped
the plaquette-pair strong-coupling bounds from reaching it, independently of the algebra.
`GaugeInvariantAlgebra.forall_span_of_forall_finite_combination` and
`gaugeInv_pairing_of_spanning` change the quantifier: a bound on finite linear COMBINATIONS of a
spanning set gives the bound on the span, and for a quadratic form that is a **Gram-matrix
condition** — over any finite family of plaquette observables, the depth-`2p−2` Gram matrix
dominated by `r²` times the depth-`2p` one. Entry by entry those are two-observable connected
pairings, which is the shape `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds.

Two gaps remain before that is usable, and neither is proved: the invariant algebra is not shown to
be **spanned** by plaquette observables, and the Gram condition itself needs the matrix inequality,
not just entry-wise bounds — positivity of `r² B − A`, where the entry-wise bounds constrain the
entries but do not by themselves give the form inequality.

`DLRLimit.State.map_sum` had to be added for any of this to typecheck: `State` is a bare structure
with `map_add'` and `map_smul'`, not a bundled `LinearMap`, so Mathlib's `map_sum` never applied to
it and no argument could expand a state over a finite family.

### The two infinite-volume constructions never meet

This is the substantive obstruction, and it is not a missing inequality.

| construction | object | |
|---|---|---|
| `InfiniteVolume` → `Schwinger` → `MomentMeasure` | limits of **periodic** correlators `corrLag k β N`, the moments `L k`, a representing measure | the strong-coupling bounds live here |
| `ReflectionHalfSpace` → `WilsonState` → `GaugeInvariantAlgebra` | a DLR state `ν` on `ℤ⁴` and its reflected pairings | the gap obligation lives here |

`InfiniteVolume` never mentions `ν`, `IConf` or `ireflObs`; `StrongCoupling`'s subject is
`WilsonBridge.wilsonCorrConn`, a plaquette pair on the periodic lattice. `gapEntry` is built from
`ν`-pairings. **The only declaration linking the two families is
`WilsonState.stateFree_eq_spec_at_zero_coupling`, and it holds only at zero coupling.**

**Do not route this through the periodic lattice.** Identifying `corrLag`'s limit with a `ν`-pairing
would need the periodic and free-boundary limits to agree — boundary-condition independence, i.e.
uniqueness of the infinite-volume Gibbs state, which the tree has only at `β = 0`
(`WilsonDLR.dlr_unique_at_zero`) and which is hard at positive coupling.

**Go through the box carrier instead.** `WilsonBridge.wilsonCorrConn bd p₀ β p` takes its measure
entirely from `bd`, the plaquette boundary map, through `wilsonSystem bd wilsonDensity` against
`probHaar`; the link and plaquette types are abstract. So is
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`, which bounds it. Instantiating that
carrier at a **finite box of `ℤ⁴`** — links in `Λ`, plaquettes with every link in `Λ`, `bd` the
restriction of `GibbsSpec.ibd` — gives the strong-coupling bound for the free-boundary box state
directly. That state is `ReflectionHalfSpace.stateFree`, which is what `htend` converges to and
therefore what `ν` is. **No uniqueness is needed: the identification is with the state the
construction already uses.**

And `WilsonBridge.wilsonCorrConnF` generalises single plaquettes to `Finset`s of them — products of
plaquette observables — which is exactly the monomial family
`OSPositivity.wilson_gram_nonneg_monomials` ranges over, so the spanning set and the bounded objects
would be the same family.

### The strong-coupling bound now lands on the gap obligation's expression

`GaugeInvariantAlgebra.stateFree_pairing_abs_le` bounds the reflected, mean-subtracted pairing of two
plaquette observables by `coreConst · coreRate ^ k`, geometrically and uniformly in the box. Four
links, every one foundational-only, and every one joining pieces that already existed:

| link | content |
|---|---|
| `iplaqObs`, `iplaqObs_mem_gaugeInvHalfSpaceAlg` | the plaquette observable constructed, and in the invariant algebra — continuity from `PlaqVariance.continuous_wilsonHol`, carrier-free |
| `ireflObs_iplaqObs` | the reflection carries it to the observable at `ireflPlaq τ c q`, the conjugating element killed by `wilsonDensity_conj` |
| `pairing_iplaqObs_eq_connected` | the reflected pairing IS a connected correlator |
| `stateFree_connected_eq_wilsonCorrConn` | that correlator IS `wilsonCorrConn` at the box carrier |
| `ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` | bounded geometrically, uniformly in the box |

`ireflPlaq_maps_plus_to_minus` is why it has force: the reflected plaquette sits in the opposite half, so
the boundary-word separation the factor is raised to grows with the reflection depth.

**Scope, sharply.** Two SINGLE plaquettes. `gapEntry` is stated over a spanning family. The
`Finset` version — `WilsonBridge.wilsonCorrConnF`, products of plaquettes — now has its geometric
bound in `StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow`, so what remains at this
step is lifting that bound from `wilsonCorrConnF` to the `stateFree` pairing, the family counterpart
of `stateFree_connected_eq_wilsonCorrConn`. That identification is not written.

**The counting estimate is already done**: `StrongCoupling.corePairsF_sum_le` bounds the core-pair
sum by `coreConstF · coreRate ^ (k + 2 - |Ao ∪ Bo|)`, taking exactly the span lower bound
`coreSpanF_card_ge_of_not_mem_ball` supplies. That is the hard half of the cluster expansion and it
is proved.

**What the `Finset` bound still needs is two lemmas, both with their ingredients proved.** The
single-plaquette bound is
`wilsonCorrConn_abs_le_of_coreResummation … (corePairs bd p₀ pd) (coreSpan p₀ pd)
(coreResummation_holds …)`, so the `Finset` route needs:

* a resummation identity for the Finset case — the analogue of `coreResummation_holds`, assemblable from
  `wilsonCorrConnF_eq_bridging_sumF` and `nonbridging_sum_eq_zeroF`, both proved;
* the generic step that turns a supplied resummation into the bound — the analogue of
  `wilsonCorrConn_abs_le_of_coreResummation`, a triangle-inequality and integrability argument.

With those, `corePairsF_sum_le` closes it. Neither is written, and neither is the counting estimate
— that part of the cluster expansion is behind us.

**Sized precisely.** `StrongCoupling` carries eighteen `Finset`-suffixed declarations already.
`wilsonCorrConn_abs_le_of_coreResummation` is generic in the core family — it takes `cores` and
`core` as arguments — but its conclusion is fixed to the single-plaquette `wilsonCorrConn` and to
`pairTerm`, so the `Finset` route cannot reuse it. `CoreResummation` is a concrete equation: the
reach-filtered sum of `pairTerm` equals a sum over cores of `pairTerm` times the outside partition
functions squared. Three declarations are wanted:

1. the predicate, `pairTermF` and the `Finset` reach condition in place of their singletons — a
   transcription of the statement;
2. its witness, which redoes the resummation — the sign-reversing involution machinery
   (`exchangeF`, `exchangeF_exchangeF`, `nonbridging_sum_eq_zeroF`) is proved, so this is assembly
   rather than new mathematics, but it is the substantial one;
3. the generic bound step at `wilsonCorrConnF`, mirroring the single-plaquette one.

Then `corePairsF_sum_le` — already proved — supplies the geometric decay.

**This route is now closed.** Four declarations in `StrongCoupling.lean` carry it:

| declaration | what it does |
|---|---|
| `CoreResummationF` | states the resummation for families |
| `coreResummationF_holds` | witnesses it, one line over `bridging_sum_eq_core_sumF` |
| `wilsonCorrConnF_abs_le_of_coreResummationF` | turns a core-sum bound into a `wilsonCorrConnF` bound |
| `wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` | composes those with `corePairsF_sum_le` |

The step that took the work was a filter mismatch. `wilsonCorrConnF_eq_bridging_sumF` produces a sum
filtered on `∃ b ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b` — some plaquette of `Bo`
reachable from some plaquette of `Ao` — while `bridging_sum_eq_core_sumF` resums the sum filtered on
`∀ p ∈ Ao ∪ Bo, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p`, every plaquette reachable from one base
point. Different conditions, and the single-plaquette proof gives no hint of it: there `Ao ∪ Bo` is
two points and the two collapse.

`reach_filter_iff_of_connected` closes it. Reading `wilsonCorrConnF_eq_bridging_sumF`'s hypotheses
rather than only its conclusion: it already requires `∀ p ∈ Ao, Reach bd Ao a p`, so `Ao` is
internally touch-connected. Adding the mirror for `Bo` makes the filters equal, via the chain
`a → a' → b' → b → p` — whose last two links need `Reach` to be symmetric, which `reach_symm` proves
from `touch_symm`. Internal connectedness is what a Wilson loop is, so this asks nothing the
intended callers do not already satisfy.

All four are axiom-clean: `propext`, `Classical.choice`, `Quot.sound` and nothing else.

### The box-carrier route, and the three pieces left

`ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` puts the strong-coupling bound on the box carrier:
the connected correlator of two plaquette observables in the free-boundary box state decays
geometrically, **uniformly in the box**, since `touchDeg_boxBd_le` carries no box dependence. That is
the state `htend` converges to, so no boundary-condition independence is needed. It composes
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le` (carrier-free) with
`touchDeg_boxBd_le` (which had no consumers), and `stateFree_eq_expect_boxBd` is the identification
of `stateFree` with that system.

What stands between it and `GaugeInvariantAlgebra.gapEntry`:

| piece | status |
|---|---|
| `ireflObs τ c` applied to a plaquette observable equals the observable at `LatticeReflection.ireflPlaq τ c q` | **built** — `ireflObs_iplaqObs` |
| a geometric bound for `WilsonBridge.wilsonCorrConnF`, the `Finset` version — products of plaquette observables | **built** — `wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` |
| the Gram and diagonal-dominance assembly | **built** — `gaugeInv_pairing_of_diagDominant` |
| an off-diagonal `gapEntry` bounded by its two constituent pairings | **built** — `gapEntry_abs_le` |
| the family counterpart of `stateFree_connected_eq_wilsonCorrConn` | **built** — `stateFree_connectedF_eq_wilsonCorrConnF`, over `stateFree_iplaqObsF` and `stateFree_iplaqObsF_mul` |
| the reflected pairing of two products, as a connected correlator | **built** — `pairing_iplaqObsF_eq_connected`, over the observable-generic `pairing_eq_connected` and `ireflObs_prod_iplaqObs` |
| joining those two at a box | **built** — `ireflObs_prod_iplaqObs_box` and `stateFree_pairingF_eq_wilsonCorrConnF`, composed into the geometric bound `stateFree_pairingF_abs_le` |
| `hdom` itself, the diagonal dominating the off-diagonal sum | **missing** — needs the sum over the family to converge against the diagonal, which is a statement about how spread out the family is |

`hdom` was the remaining step, and investigating it produced a correction rather than a proof.

**Unweighted diagonal dominance is the wrong test.** Write `d i` for a family member's height above
the reflection plane. The depth-`2p` diagonal entry is a correlator at separation `2 · d i`, while
the off-diagonal against the member `j` nearest the plane sits at `d i + d j`. On saturated bounds
the off-diagonal is the larger, by a factor geometric in `d i − d j`, at every member above the
family's minimum height — and a spanning family of the half-space algebra contains members at
several heights. So `hdom` is not provable from the upper bounds strong coupling supplies, and is
not something such a family should be expected to satisfy.

The fix is that the quadratic form's sign is invariant under positive diagonal rescaling while the
unweighted test is not. `sum_sum_nonneg_of_weighted_diagDominant` and
`gaugeInv_pairing_of_weighted_diagDominant` carry the weighted test, which `w = 1` specialises back
to the old one; `gapEntry_diagDominant_of_bounds` and `gapEntry_weighted_diagDominant_of_bounds`
reduce both to numeric inputs `U`, `U'`, `Lo` taken as parameters, so no coupling regime is baked in.

**The named open estimate.** `Lo` — a volume-uniform positive LOWER bound on the reflected connected
two-point function at separation `2 · d`. Strong coupling supplies bounds on the modulus only.

Nothing in the development lower-bounds any correlator at nonzero separation. Every strictly
positive floor is a contact value: `ContactFloor.wilsonCorrConn_self_ge_haar` is the same plaquette
twice at lag zero, and `irefl_box_pairing_pos_witness` and
`BoxNumericFloor.box_reflection_form_ge_number` are both at a link of `boxR`, the links the
reflection fixes.

**The obvious repair is closed, and this is worth stating precisely because it looks open.**
`irefl_box_pairing_ge_variance` bounds a reflected box pairing below by a uniform weight floor times
a free-measure variance. Its floor carries `(iplqZero τ p Λ).card`, the whole reflection plane, so
it decays as the box grows. That factor is a crude sup bound on the plane Boltzmann weight entering
at a single step, and it could be localized the way `ContactFloor` localizes its own. Localizing it
gains nothing: `ActionSplit.pairing_eq_zero_of_indep_R` proves the subtracted reflection pairing is
**identically zero at every coupling** whenever the observable reads the open half alone and the
weight reads the plane alone, and `iplaneWeight_local` together with `iplaneWeight_nonneg` discharge
the weight side. Under product Haar the two open halves are independent, so any
weight-floor-times-free-variance argument returns `0 ≤`, which `irefl_box_pairing_nonneg` already
has.

**The escape, read off that theorem's hypotheses.** It closes only on observables reading the open
half alone. The observable that actually appears is `idressed` — the observable times `ihalfBoltz`,
which reads every plaquette of the positive half — so it fails that hypothesis, and the whole
nonzero value of the pairing sits in the dressing. A positive floor therefore needs an expansion
keeping the leading connected term **with its sign**; a bound on the modulus cannot be turned
around.

One further obstruction, independent of the above: `irefl_box_pairing_ge_variance` is stated on an
unnormalised integral against `cvol`, while `DLRLimit.le_of_eventually_le` and
`variance_ge_of_eventually` — which do transport non-strict bounds through the thermodynamic limit —
consume the normalised `stateFree`. Bridging the two needs a `partFree` ceiling of the same form as
the floor, and none exists in volume-free form.

### The absolute floor is the Gram route's requirement, not the obligation's

Worth stating, because it changes what to aim at. The obligation is
`TransferGap.GapAt D r := ∀ x, D.form x D.vac = 0 → D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x`
— a **relative** bound between two forms at the same `x`. It never asks for `D.form x x ≥ c > 0`.
The same is true of the other entry point: `SecondEigenvalue.rayleighSet` divides by `‖y‖ ^ 2` in the
**GNS space**, which is already the quotient by the null space, so a nonzero vector has positive norm
for free.

The requirement for a strictly positive diagonal `Lo i` enters only with the Gram and
diagonal-dominance reduction, which is a *sufficient* route and strictly stronger than the
obligation. That is the step the no-go above bites on. A route that stays relative does not incur it.

**The relative route is now built end to end, and it is axiom-clean.** In `SecondEigenvalue`:

| declaration | |
|---|---|
| `rayleigh_le_of_norm_le` | operator-norm bound gives a Rayleigh bound — needs neither symmetry nor non-negativity |
| `norm_map_sq_le` | `‖T y‖² ≤ ‖y‖ · ‖T (T y)‖`, log-convexity along the orbit |
| `norm_pow_sq_le` | the same at an arbitrary power, via `IsSymmetric.pow` |
| `norm_map_pow_le` | the dyadic iteration: a `2^k`-step bound controls the one-step norm |
| `le_of_pow_two_pow_le` | a fixed constant cannot hold a geometric comparison open — Archimedean descent, no limit |
| `norm_le_of_iterate_bound` | geometric decay of the iterates bounds the operator in one step |
| `lambdaTwo_le_of_norm_le`, `lambdaTwo_le_of_iterate_bound` | the interface `clay_gap_of_lambdaTwo` consumes |

So `∀ y ∈ V, ∀ n, ‖T ^ n y‖ ≤ C · ρ ^ n · ‖y‖` with `ρ < 1` now yields the Clay spectral statement.
**Every step is an upper bound.** No lower bound on the reflection form appears anywhere, so the
reflected-pairing no-go does not reach this route.

That obligation is now stated in the reflection form rather than in the GNS space.
`ClayCapstone.norm_Tq_pow_mk_mul` reads `‖Tq ^ n (mk x)‖ · ‖Tq ^ n (mk x)‖` as
`D.form ((D.T ^ n) x) ((D.T ^ n) x)`, over `HalfLineTransfer.Tq_pow_mk`, and
`ClayCapstone.clay_gap_of_form_decay` takes the whole route from

    ∀ x, mk x ∈ V → ∀ n, D.form ((D.T ^ n) x) ((D.T ^ n) x) ≤ (C · ρ ^ n) ^ 2 · D.form x x

with `ρ < 1` straight to the Clay spectral statement. So the obligation is now a statement about the
reflection form at a translated observable — the object a correlation estimate speaks about.

And that diagonal is not a diagonal. `TransferGap.form_pow_symm` moves any power of `T` across the
form, and at `y = (D.T ^ n) x` it collapses the diagonal at the `n`-th iterate to an off-diagonal at
the `2 * n`-th:

    D.form ((D.T ^ n) x) ((D.T ^ n) x) = D.form x ((D.T ^ (2 * n)) x)      -- `form_pow_diag`

an identity, carrying no hypothesis. So `ClayCapstone.clay_gap_of_two_point_decay` takes the route
from

    ∀ x, mk x ∈ V → ∀ n, D.form x ((D.T ^ (2 * n)) x) ≤ (C · ρ ^ n) ^ 2 · D.form x x

with `ρ < 1`, straight to the Clay spectral statement. **Read what that says**: the reflected pairing
of an observable with itself translated `2 * n` steps — a two-point function at a separation growing
with `n` — bounded by the same observable at separation zero, the contact value. It is a
contact-relative decay law, geometric in the separation, an upper bound throughout. That is the same
shape `NonnegArm.LawAbove` has, reached by a different chain.

That hypothesis is now concrete. `TransferAssembly.assembleTransferData_form_pow` unfolds it:
the assembled form is `ν (R.θ F * H)` and its `T` is `restrictT`, so

    D.form x ((D.T ^ n) x) = ν (R.θ x * (C.T)^[n] x)

read on the underlying continuous functions. So the whole relative route reduces to

    ν (R.θ x * (C.T)^[2n] x) ≤ (C · ρ ^ n) ^ 2 · ν (R.θ x * x)

— the state's reflected pairing of an observable with itself translated `2 * n` steps, against the
same pairing at separation zero. Every object in it is one a correlation estimate speaks about; none
belongs to the GNS construction.

And the route is now stated at the gauge-invariant Wilson data itself.
`GaugeInvariantAlgebra.gaugeInv_form_pow` specialises the identification, since
`gaugeInvTransferData` IS `assembleTransferData` at the lattice reflection and the lattice shift, and
`ClayCapstone.gaugeInv_clay_gap_of_state_decay` takes the whole chain from

    ν (ireflObs τ (2p) x · (ishiftObsL τ)^[2n] x) ≤ (C · ρ ^ n) ^ 2 · ν (ireflObs τ (2p) x · x)

over gauge-invariant half-space observables whose class lies in the vacuum complement, with `ρ < 1`,
to the Clay spectral statement. **No GNS construction and no transfer data appear in that
hypothesis** — only the limiting state, the reflection and the shift.

**What is still open** is a strong-coupling bound of that shape.
`GaugeInvariantAlgebra.stateFree_pairing_abs_le` bounds a pairing of this form for plaquette
observables, but two things differ and neither is cosmetic: it is stated at `stateFree` on a finite
box rather than at the limiting state `ν`, and it pairs an observable with the REFLECTED plaquette
rather than with a TRANSLATE of itself.

The **first** now has its tool. `DLRLimit.le_of_eventually_le` carried only a LOWER bound to the
limit; `ge_of_eventually_ge` and `abs_le_of_eventually_abs_le` add the other direction and the
modulus one. The modulus version is the shape every strong-coupling estimate has —
`|pairing| ≤ constant · rate ^ separation` — so a finite-volume decay bound now reaches `ν` provided
the constant does not depend on the box. `coreConst` and `coreRate` are volume-free, since
`touchDeg_boxBd_le` carries no box dependence, so that proviso is met on this route; what remains is
to assemble the eventual hypothesis over an exhausting family.

The **second** is geometric and is the harder of the two. `stateFree_pairing_abs_le` does not
restrict the two families, so taking the second to be a translate of the first is allowed; its
separation parameter is a ball radius centred at the reflected plaquette, so closing this means
showing that the touch distance from `ireflPlaq τ (2p) q` to the `2n`-translate of `q` grows with
`n`. That is a counting statement about the lattice, not an estimate about the measure.

`SecondEigenvalue.inner_map_cauchy_schwarz`, the reflection-positivity Cauchy–Schwarz, remains
available and unused; the chain above needs only ordinary Cauchy–Schwarz and symmetry.

`ClayCapstone.clay_gap_of_lambdaTwo` is the entry point that consumes a `lambdaTwo` bound, and
`clay_gap_on_interval` joins it to `Mixing.interior_mixing_of_analytic_grid`. Note what that grid
argument is and is not: it turns a **derived** Lipschitz modulus plus grid-point bounds into a bound
everywhere, and the measured grid under `research/data` is a failure to refute rather than a proof —
the tree already says so, and it must stay that way.

The box join did not need the box's symmetry as an unproved side condition. It takes a map `ρ` of
the box's plaquettes to themselves together with `hρ`, the proof that `ρ` IS the reflection — so a
symmetric box supplies it and nothing is assumed of a box that is not one.

Generalising `pairing_iplaqObs_eq_connected` to `pairing_eq_connected` showed the special case
carries a hypothesis it does not need: reflection invariance of the state was spent converting
`ν (ireflObs τ c f)` to `ν f`, and the generic statement simply keeps the former, since the two
`ν f` terms cancel in the expansion regardless.

### What the search for a matrix-inequality route found

**The `B` side is already Gram-form.** `ReflectionStrong.pairing_gram_nonneg` proves the depth-`a+a`
Gram matrix positive semidefinite over any finite family of slab observables, at every real coupling;
`OSPositivity.wilson_gram_nonneg_monomials` does it over **monomials in generators**, so the
inequality ranges over the unital subalgebra the generators generate rather than a subspace. Both are
on the periodic lattice. `ReflectionStrong.form_sum_sum` is the expansion step for a `PreForm`, the
same one `pairing_sum_sum` performs for the raw pairing.

**The Osterwalder–Seiler iteration is present and runs the other way.**
`SchwarzIteration.orbit_log_convex` gives `P(Tⁿ⁺¹x)² ≤ P(Tⁿx)·P(Tⁿ⁺²x)` from Cauchy–Schwarz and
symmetry, and `contract_of_bounded_orbit` turns a bounded orbit into contractivity — which is
`TransferData.T_contract`, the rate-one statement. Log-convexity makes the successive ratios
**non-decreasing**, so it bounds a rate from below along one orbit, not above. It is why `T_contract`
is free and why nothing here produces a rate below one.

**Knabe's criterion is in the tree, on a different carrier.** `LocalGap.knabe_chain_gap` is exactly
the right shape — a local check on windows giving a global gap — but it is stated for a
nearest-neighbour chain of Hermitian idempotents indexed by `ZMod L` acting on `Fin N → ℝ`, not for
a lattice gauge transfer operator. No declaration connects the two carriers.

**Nothing produces positive semidefiniteness from entry bounds.** `PosSemidef` occurs only in the
cell modules — `CellEnclosure`, `CellPerturb`, `CellSpectrum`, `LocalGap` — all about the model cell
Hamiltonian. There is no Gershgorin, no diagonal-dominance and no Schur-complement result anywhere in
the tree.

The generalisation was mechanical once read — the halfSpaceAlg chain is three lemmas and each touches
the algebra only through the quantifier and `1 ∈ A`:
`gapAt_iff_pairing_of_mean_zero` turns `GapAt` into a pairing inequality over mean-zero elements —
the computation that unfolds the assembled form, the vacuum and the shift — and
`gapAt_iff_subtracted_pairing` drops the mean-zero side condition by subtracting the mean, using
only `Submodule.sub_mem`, `Submodule.smul_mem` and membership of `1`. The second rests on the first,
so the first is where the generalisation has to start.

**So the gauge-invariant route is complete as far as structure goes**: the action, the invariant
submodule, its three closure facts, restricted reflection positivity, the transfer data, and a
non-trivial member. What it needs is what every route needs — `PositiveTransfer` and `GapAt` below
one — now asked on an algebra where the plaquette-pair strong-coupling bounds are the right shape.

`TransferGap.gapAt_mono` makes the rate-zero results usable: from `GapAt D r₁` and `r₁² ≤ r₂²`,
`GapAt D r₂`, with `ReflForm.form_nonneg` the whole input. `WilsonState.gapAt_zero_at_zero_coupling`
concludes `GapAt … 0`, and a consumer wanting a gap `−log r` needs `0 < r` because `Real.log 0` is a
junk value; monotonicity turns rate zero into every positive rate, so the gap at zero coupling is
unbounded — the right reading, since the connected pairing vanishes identically there.

**What still blocks a complete end-to-end instance at `β = 0`** is `PositiveTransfer`. Nothing proves
it at zero coupling: `WilsonState` and `WilsonDLR` never mention it, and
`WilsonTransferReduction.positiveTransfer_of_state_facts` needs reflection positivity about the odd
plane. That is produced — `ReflectionHalfSpace.wilson_reflPositive_odd_of_tendsto` — but only from
a convergence hypothesis, so positivity is available WITH a limit and unavailable without one, even
at the trivial coupling.

**The pieces for a complete β = 0 instance are now present.** `WilsonDLR.tendsto_specState_at_zero`
is a limit along ALL finite regions; `wilson_positiveTransfer_of_mixCube_limit` wants one along the
interleaved box sequence. `ReflectionHalfSpace.mixCube_exhausts` and `tendsto_mixCube` bridge the
two: `mixCube` interleaves boxes at two reflection planes so it is not monotone, and exhaustion
needs both `symCube_exhausts` instances rather than one. With `stateFree_eq_spec_at_zero_coupling`
identifying the free-boundary and fixed-boundary states at zero coupling, and `specState` being
`spec` wrapped, the remaining step is the assembly — rewrite `stateFree` to `specState`, compose the
limit along `tendsto_mixCube`, then `gapAt_zero_at_zero_coupling` with `gapAt_mono` into
`wilson_clay_gap_of_gapAt`. **That assembly is done.**

`ClayCapstone.wilson_clay_gap_at_zero_coupling` closes the chain at zero coupling with **no open
input**, foundational-only. `wilson_htend_at_zero_coupling` supplies the thermodynamic limit in the
form the positivity producer consumes; that gives `PositiveTransfer`;
`gapAt_zero_at_zero_coupling` with `gapAt_mono` gives `GapAt` at every rate; and
`wilson_clay_gap_of_gapAt` returns the gap.

**Its value is non-vacuity, and that is the whole of it.** The capstone takes hypotheses nothing had
ever produced together, and a capstone whose hypotheses are jointly unsatisfiable proves nothing.
This exhibits a case where all of them hold at once. `β = 0` is the free theory — the connected
pairing vanishes identically, which is why the rate is `0` and why `r` stays universally quantified
over `(0,1)`, the gap unbounded and no constant chosen. It says nothing about any positive coupling.

The gap at ONE coupling is what a lattice mass gap asks for; `clay_gap_on_interval` gives it
uniformly in `β`, which is what a continuum limit wants. The two hypotheses below belong to the
second, stronger statement.

**For the uniform-in-β route, the remaining work is two hypotheses, both about `rhoOne`:**

| hypothesis | content | status |
|---|---|---|
| `hlip` | a Lipschitz modulus for the subdominant ratio in the coupling | unproved |
| `hcover` | grid values below `(1 − ε) − Lδ` | unproved |

Everything downstream of them is discharged. The structural hypotheses — `PositiveTransfer`,
boundedness of the Rayleigh set, the vacuum complement, and `0 < rhoOne β` — carry no quantitative
content. `0 < rhoOne β` is needed because `Real.log` returns a junk value at zero; where the
supremum vanishes the gap is unbounded, the degenerate case
`WilsonState.gapAt_zero_at_zero_coupling` exhibits.

**The measured grid cannot close it, and must not be used as though it could.** Data may refute a
derived bound, never support one. `9_4_dat_interior_mixing_grid.csv` records SU(2) at thirteen
couplings with `rho1` from 0.0243 to 0.3197 and one-sided 99.9% upper bounds to 0.4535, every row
below `3^(−1/4)`. That is a **failure to refute** `Λ < 1` across the measured range, which is worth
recording as exactly that and as nothing more. `Mixing.interior_mixing_of_analytic_grid` instantiated
on those rows would be a fit, not a proof.

**Two other proved sub-one constants exist and neither is about the transfer form.**
`CellSpectrum.Hcell2_clears_floor` concludes the `3^(−1/4)` ceiling at every real `λ`, and
`CellCover.cell_gap_on_range` concludes an exact-rational eigenvalue gap on a coupling range — both
for a model **cell** Hamiltonian, and `CellSpectrum`'s own scope note says the coupled transfer's
difference from the product is not addressed. Nothing bridges a cell to a `TransferData`.

**And `SpectralAt` is proved below one at small coupling, on the correlator side.**
`LagTwoBound.exists_cut_lag_two_ratio` gives, for **every** `K > 0`, a cut `b > 0` with
`wilsonCorrAt 3 β 2 ≤ K · wilsonCorrAt 3 β 0` on `[0, b]`; with `SpectralBound.spectralAt_iff` that
is `SpectralAt β √K` there. But `SpectralAt` is provably equivalent to the ratio inequality, so it
carries no operator content, and the tree's arrow runs
`SpectralBound.spectralAt_of_vacuum_rayleigh` — Rayleigh **to** `SpectralAt`, the direction that does
not help. The converse is the missing link on that route, and `b` is an uncontrolled continuity cut
in any case.

## The order of work

Delivery is built; the work is `Λ`.

1. Settle whether `opT D` is compact. That one fact decides whether `reconstruct_from_opT` is
   reachable as stated, and it is cheap against everything else here.
2. The all-`τ` bound for `SlabQuadratic.wilsonSpectral`'s spectral form — the shortest route to `Λ`,
   with producer and consumer both already written, and no thermodynamic limit needed.
3. R1 obligation 3 — plaquette observables to `halfSpaceAlg`, by support extraction.
4. R0 — `atTop` convergence for `mixCube`, by a parity argument.
5. The `ε` lower bound.
6. With `Λ < lambdaThreshold`: the mass gap, at `SU(N)`, no named axiom.
7. R3 and R4 — the spacing limit and the Minkowski end.
