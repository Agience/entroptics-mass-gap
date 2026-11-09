import Mathlib
import MassGap.WindowRelay
import MassGap.MeasuredSpacing

/-!
# MassGap.ObserverSkeleton — what the target's gap consumer reads, and whether the window skeleton carries it

The frame: the observer reads the substrate only through its aperture. `WindowRelay` proves that an exact
decimation keeps every reading of the coarse skeleton (`integral_skeleton`, `expect_skeleton`) and names the
coarse-to-fine step it cannot make (L2: fine modes off the skeleton). This module traces what the gap clause of
the target consumes, proves the reduction from the skeleton to that consumer under an exact (or vanishing-error)
skeleton condition and under a uniform-angle condition, and argues why neither condition holds for the target's observer at a window of fixed physical side. Declarations are in the namespace `MassGap.ObserverSkeleton`.

## 1. The consumer (traced; file:line in `research/lean/MassGap`)

* `ClayStatementG.lean:726` `ClayStatementOf G`: `∃ βs, MeasTowerG G βs ∧ ∃ W D, … ClayStatementAtP (schedAlongG G
  βs) (constsG G) W D`; `:667` `ClayDataP` carries the gap in three clauses: `:672` `HamiltonianGap X.base`
  (`ClayFull.lean:181`: the generator of `X.time` has `X.gap ‖u‖² ≤ re⟪u, Hu⟫` on the vacuum complement of
  `X.base.H`), `:678` `SpectralGapOn X.base (HLsG X w)` and `:691` `SpectralGapOn X.base (HLCG X wC)`
  (`ClayStatement.lean:789`: the same bound and `‖e^{−tH}u‖ ≤ e^{−Δt}‖u‖` on a closed subspace of `X.base.H`).
* The Hilbert space is `X.base.H`. `:693` `ObsGenG S W D X` (`:455`) asks it to be the closed span
  (`ClayStatement.lean:730` `HLg`) of the observer's vectors `v P` of the compact margin monomials of every local
  field, with `⟪v P, v Q⟫ = S_W(θP ∪ Q)` (the flowed Schwinger function of `energyMapG S W D`) and the time
  translation by `a_m` acting as the shift of the test functions. The local sector `HLsG X w` (`:445`, linked by
  `LinkTSG`, `:432`) and the composites' sector are closed subspaces of the same `X.base.H`.
* The operator is `X.base.time t` (the observer's time translation), with `X.base.gap` its rate; the only field
  of `OSDataS` (`ObserverOSReconstructionS.lean:76`) that carries the contraction is `time_gap` (`:107`).
* At the observer `ClayGFinal.observerOSDataSLinkedGN` (`ClayGFinal.lean:308`), `base := observerOSDataSGN`
  (`:265`) has `H := FlowHG …`, `time := timeTG …`, `time_gap := hμ…` (`:301`), with `hμ` from
  `flowN_time_group_of_gapG_noNT` (`:68`), whose one gap input is `hg` (`:271`, `:316`):
  `TransferGap.GapAt (transferNG S hS (energy0G S W D hD) hB τ hphys m0) ρ`, `0 < ρ < 1`. Its first step
  (`:76`) is `TimeGroupG.flowClusterAbs_iff_gapAtG` (`TimeGroupG.lean:710`) read right to left.
* `transferNG` (`TimeGroupG.lean:728`) is `FlowG.flowTransferG` (`FlowG.lean:742`): the GNS transfer of the
  form `kernFG S Φ τ P Q` (`FlowG.lean:546`) on finitely supported combinations of margin monomials, `Φ` the
  observer's flow `energy0G S W D hD`. `kernFG = contSFG S Φ.map (pairFamG τ P Q)` (`ClayTreeG.lean:476`): the
  limit along `ultra` in the step `k` of `latSFG = ν_k(∏ smear a_k (Φ.map k Oᵢ) fᵢ)` (`ClayTreeG.lean:465`,
  `:320`; `smear a F f = Σ_x a⁴ f(a x) T_x F`, `ContinuumField.lean:697`).

So the needed statement is `FlowClusterAbsG S Φ τ r L` (`TimeGroupG.lean:516`): some `c > 0` with, at every step
`m` and every pair of margin monomials, `|S_W(θP ∪ T_{a_m n} Q) − S_W(θP) S_W(Q)| ≤ C e^{−(c/L) a_m n}`.
`observerGap_iff_cluster` (proved) restates the iff at the consumer's own `transferNG`; `observerGap_of_clusterAt`
(proved): decay along one grid `m₁` gives `hg` at every step `m₀`. The answer is (b): the consumer reads only
the decay of two-time correlations of the observer's flowed readings, in the continuum limit, on the observer's
reconstruction; no gap of the fine lattice's full `L²` is asked. `MeasuredSpacing.observerGap_of_sectorSeed`
supplies it through a per-step gap of the full gauge-invariant half-space transfer (`kernFG_cluster_of_stepGap`),
which is sufficient, not necessary.

## 2. The reduction (proved, under the observer-skeleton condition)

* Exact transport of a connected read (`conn_skeleton`): for a measure-preserving `glue` with `π ∘ glue = fst`,
  the connected two-point read of skeleton observables `F ∘ π`, `H ∘ π` under the fine density equals the
  connected read of `F`, `H` under the effective density (three uses of `WindowRelay.expect_skeleton`).
* The observer-skeleton condition at the tower. `SkeletonReads S Φ τ eff`: the observer's lattice read of every
  pair, `latSFG S Φ.map k (pairFamG τ X Y)`, minus `eff k X Y` tends to `0` along `ultra`. `skeletonReads_of_factor`
  (proved): if, along `ultra`, every lattice read is the normalized fine integral of a skeleton observable
  `A k X Y ∘ π k` for an exact decimation at step `k`, then `SkeletonReads` holds with `eff` the effective reads.
* `SkeletonCluster S τ r L m₁ eff`: the connected `eff` reads of margin monomials decay at a rate `c/L` in physical
  time, with a constant per pair, uniformly along `ultra`.
* `flowClusterAt_of_skeleton`, `observerGap_of_skeleton` (proved): `SkeletonReads` and `SkeletonCluster` give
  `FlowClusterAtG`, hence `hg` at every step: the observer's gap, from decay of effective (coarse) reads.
* The angle form (`gap_of_angle`, proved): on a real inner product space, a symmetric contraction `A` whose
  reads between vectors of a set `K` decay, `|⟪k, A^s k⟫| ≤ ρ^s ‖k‖²`, and such that every vector is within
  `δ‖f‖` of `K`, has `‖A^T f‖² ≤ (ρ^{2T}(1 + δ)² + 2δ + δ²)‖f‖²`, so `‖A‖ < 1` once that coefficient is below
  one at some `T` (the power step is `WindowRelay.norm_le_of_norm_pow_le`). The intended instance (argued; no theorem of the module connects `gap_of_angle` to `transferNG`): `A` the
observer's transfer on the vacuum complement of its space, `K` the skeleton vectors. The condition is an angle between the observer's
  space and the skeleton: `‖(1 − P_skel)‖ ≤ δ` on the observer's space. L2 asks something else, that the fine
  modes off the skeleton are forgotten within one hop (`‖R^{∗b}(1 − P_skel)‖ ≤ δ`).

## 3. The obstruction (argued; the floor proved)

The observer's readings are not measurable with respect to the window skeleton, for three reasons.

1. Smearing. `smear a_k F f = Σ_x a_k⁴ f(a_k x) T_x F` sums every fine translate in the support of `f`. A
   window skeleton of side `b` is covariant only under the sublattice `b ℤ⁴`; `T_x F` is measurable for the
   skeleton at offset `x mod b`. The target forces this: `ObsGenG` and `LinkTSG` ask the time translation by
   every `a_m → 0` to act on the observer's space, below the window side, while a fixed skeleton is kept only by
   shifts through whole blocks.
2. The flow. `Φ.map k O = a_k⁻⁴ (O ∘ V_k)` reads the fine links within `range k` of the support of `O`; the
   skeleton of `GapSideExactDecimation.glueStep` keeps only products of fine links along coarse lines and
   integrates everything else. A block-summed flowed energy (`ObserverBlockReading.blockRead`, a mean of fine
   flowed plaquettes) is a function of links the decimation removes.
3. An approximation error that does not vanish leaves a floor. `toy_read`, `toy_skeleton`, `toy_dist`,
   `no_decay_of_floor` (proved): a skeleton coordinate forgotten in one step and an off-skeleton coordinate kept
   at every time; a reading at form distance `δ ≠ 0` from the skeleton has two-time read `δ²` (not a connected read; the toy has no vacuum) at every `n ≥ 1`,
   and no `C e^{−cn}` bounds it. So skeleton decay with a fixed non-zero per-reading error, and no control of the off-skeleton part, does not give
decay: without a uniform angle (`gap_of_angle`), the per-reading error must tend to `0` along the tower (the form of
`SkeletonReads`); the read error is bounded by the form distances
   (`abs_inner_sub_le`: `|⟪u, Tv⟫ − ⟪u′, Tv′⟫| ≤ ‖u − u′‖ ‖v‖ + ‖u′‖ ‖v − v′‖`, `‖T‖ ≤ 1`).

Why the error does not vanish (argued). Along a measured tower the window has a fixed physical side:
`window_side_phys` (proved) gives `C/(2c) ≤ 2^j a_k ≤ 2C/c` from the window clause `C ≤ 2^j m′ ≤ 2C` and the band
`c a_k ≤ m′ ≤ 2c a_k`. At a fixed flow `W` of physical range `r`, the form distance of a flowed reading from the
skeleton, `‖u − E[u | skel]‖`, is a quantity of the continuum theory at the fixed ratio of the flow's smoothing
length to `2^j a_k`; it is small only when that ratio is large, and not zero. The uniform-angle form fails on the
observer's whole space: `LinkTSG` puts the local sector in `X.base.H`, and `AFShortDistance` asks its two-point
kernel at every distance `r → 0`; a local reading at resolution far below the window side has almost all of its
connected variance off the skeleton (the skeleton carries the coarse holonomies, not the intra-block
fluctuations), so `δ → 1` on those vectors.

What weaker condition suffices (proved as stated): either the per-reading error `‖u_k − E[u_k | skel_k]‖ → 0`
along `ultra` for every pair of margin monomials (`SkeletonReads` through `abs_inner_sub_le`), or a uniform angle
`‖(1 − P_skel)|_{H ⊖ Ω}‖ ≤ δ` with `2δ + δ² < 1` (`gap_of_angle`). Each replaces the coarse-to-fine part of L2 for this consumer, not its carrier part (a decimation of the target's
infinite-volume state over `G`; the exact decimation is on the cubic `SU(2)` torus). Neither is shown to hold at the
target, and both are argued to fail there.

## 4. The window route without L2

`WindowStrong ε₀ a C`, L1 (`PolymerCluster`, the cluster bound of the dressed plaquette weight, not defined in
Lean) and the relay layer of `WindowRelay` §1 give, on the coarse torus at the window, decay of effective reads
at a rate `ρ_w` per window hop (argued: L1 is not built). With the observer-skeleton condition, the route is:
effective reads decay per hop; `rate_of_hops` (proved) turns `ρ_w^h` with `t ≤ (h + 1) ℓ` into
`ρ_w⁻¹ e^{−(−log ρ_w / ℓ) t}`; `window_side_phys` bounds the hop's physical length `ℓ ≤ 2C/c`; so the physical
rate is at least `−log ρ_w · c/(2C)`, uniform along the tower: that is `SkeletonCluster`. Then
`observerGap_of_skeleton` gives `hg`. L3 (the anchor of `TransferGapMeasured`) is not read by this consumer: the
measured unit enters through the window clause and the band of `MeasTowerG`; the anchor serves the flux clause
of the centre-sector seed route (`SliceTransferGap`, `WindowRelay.transferGapMeasured_of_windowHop`). The route does not close the target: L1 is not built, the window input is on `SU(2)` only, and the observer-skeleton
condition is argued to fail there (§3).

## 5. Generation and the limit `s → 0`

The target has no free resolution parameter: `W` is fixed by the existential of `ClayStatementOf`, the step `k`
is inside each kernel value (the limit along `ultra`), and `ObsGenG` quantifies over every compact margin monomial
of every local field, so test functions of every support size, and asks their closed span to be all of
`X.base.H`. `FlowClusterAbsG` quantifies over the same monomials (`∀ P Q`), and the gap fields are on all of
`X.base.H`. A gap on the closed span of readings at physical resolution `s ≥ s₀` (with `s₀` a multiple of the
window side) does not give the gap on `X.base.H`: the readings at `s < s₀` and the local sector are in the space
(`ObsGenG`, `LinkTSG`), off the skeleton (§3), and a product-kernel completion of the skeleton's chain by slow
fine modes keeps every skeleton read while the space has no gap. So the reduction
holds at fixed `s` only, on a subspace the target does not single out; and if the span of readings at `s ≥ s₀` is
already dense (a Reeh–Schlieder-type density, argued), the uniform angle on it extends to the closure and fails.

## 6. Tests

1. Restatement versus reduction (proved). `consumer_iff_exists_eff`: `FlowClusterAtG` holds iff some `eff`
   satisfies `SkeletonReads` and `SkeletonCluster` (take `eff` the continuum kernel). With `eff` unrestricted the
   pair restates the consumer; the content is that `eff` be the effective-density reads of an exact decimation
   (`skeletonReads_of_factor`). As stated, `hfac` only equates numbers: a constant `A k X Y` equal to the lattice read
satisfies it for any decimation, and then `eff` is the lattice read, so the lemma alone does not separate the
reduction from the restatement. The separating content, that `A k X Y ∘ π k` is the observer's step-`k` observable
and that `S.ν k` is the normalized `w μf` integral, is not in the statement (the target's states are
infinite-volume, the decimation is on a torus). `skeletonReads_self`: the lattice reads themselves satisfy `SkeletonReads`.
2. `β = 0` (argued, with `WindowRelay.effIter_one`). The effective density is `1` at every step; skeleton
   observables on disjoint blocks are independent under Haar, so their connected reads vanish past one hop. The
   target's states are Wilson states along `βs k → ∞`; `β = 0` is not an instance.
3. Strong coupling (argued). With zero decimation steps the skeleton is the whole fine configuration and
   `SkeletonReads` is `skeletonReads_self`; `UniformRelayStrong` gives the full fine relay gap there, which is
   the (a)-type sufficient route. The window sits at `k = 0` only when `C ≤ m′ ≤ 2C`, which fails along `β → ∞`.
4. Vacuity (proved). `gap_of_angle` at `δ = 0` asks every vector to lie in `K` and returns the gap from skeleton
   decay alone; at `δ` with `2δ + δ² ≥ 1` no `T` meets the coefficient bound, so the angle form is void there.
   `no_decay_of_floor`: a fixed non-zero error with a non-decaying off-skeleton part is not absorbed by skeleton decay;
under a uniform angle it is (`gap_of_angle`).
5. Supercritical crossover (argued). The window is asked past `PastPeak`. The exact decimation needs no control
   through the crossover (`WindowRelay.window_Z_exact`), and `conn_skeleton` holds at any step. The
   observer-skeleton condition is about the window and the observer's readings, not about intermediate steps;
   placing the window before the peak would not help it, since the off-skeleton fraction of sub-window readings
   does not depend on the coupling's side of the crossover.

## 7. Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the identification of `A`, `K` in `gap_of_angle` with the observer's transfer and skeleton vectors (§2);
  the identification of WindowStrong's `m′` with the tower's measured unit (§4); the restatement-vs-reduction
  reading of `skeletonReads_of_factor` (test 1); the obstruction (§3, items 1 and 2, and why the error does not vanish), the window route's L1 step
  (§4), the generation and `s → 0` reading (§5), tests 2, 3 and 5.
* Assumed: `SkeletonReads`, `SkeletonCluster` in `flowClusterAt_of_skeleton`, `observerGap_of_skeleton`; the
  factorization `hfac` in `skeletonReads_of_factor`; the angle `hUA` and skeleton decay `hK` in `gap_of_angle`.

## 8. Parameters

| argument | where | status |
|---|---|---|
| `S` | every tower statement | the schedule; at the target `schedAlongG G βs` |
| `Φ` | the reads | the observer's flow; at the target `energy0G S W D hD` |
| `hB` | the limit of the reads | `UniformBoundFG S Φ.map`, as the consumer takes it |
| `τ`, `r` | margin monomials | the time direction and the margin, the consumer's |
| `L` | `FlowClusterAtG` | the rate's unit; `1` in `observerGap_of_skeleton` |
| `m₁`, `m₀` | the grids | `m₁` the grid of the decay asked, `m₀` the step of `hg`; free |
| `eff` | `SkeletonReads`, `SkeletonCluster` | the effective reads; existential in `consumer_iff_exists_eff` |
| `c`, `C` | `SkeletonCluster` | the rate (fixed) and the constant per pair |
| `Ωf`, `Ωc`, `Ωr`, `glue`, `π`, `w`, `A` | `skeletonReads_of_factor` | the decimation at step `k` and the skeleton observables |
| `A`, `K`, `δ`, `ρ`, `T`, `q` | `gap_of_angle` | the transfer, the skeleton set, the angle, the skeleton rate, the power, the coefficient |
| `ρ_w`, `ℓ`, `h`, `t` | `rate_of_hops` | the rate per window hop, the hop's physical length, the hops, the time |
| `a`, `m`, `c`, `C`, `j` | `window_side_phys` | the spacing, the measured mass, the band unit, the window length, the window depth |

DERIVED (module-wide): `0` the vacuum read, the lower ends and the vanishing error; `1` the contraction bound and
the hop offset; `2` the square, the band's and the window's doubling and the dimension of the toy; `4` the
dimension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ObserverSkeleton

open MeasureTheory Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayTreeG MassGap.FlowG MassGap.TimeGroupG

/-! ## 1. The consumer -/

section Consumer

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The consumer's gap input is the flowed clustering**: a rate `ρ ∈ (0, 1)` with `GapAt` of the observer's
transfer `transferNG` at step `m₀` exists iff `FlowClusterAbsG`. DERIVED: `0` and `1` bracket the rate. -/
theorem observerGap_iff_cluster (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) :
    (∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (transferNG S hS Φ hB τ hphys m0) ρ)
      ↔ FlowClusterAbsG S Φ τ r L :=
  (flowClusterAbs_iff_gapAtG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) m0 hL).symm

/-- **Decay along one grid gives the consumer's input at every step.** DERIVED: `1` the rate's unit. -/
theorem observerGap_of_clusterAt (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m1 m0 : ℕ)
    (h : FlowClusterAtG S Φ τ r 1 m1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (transferNG S hS Φ hB τ hphys m0) ρ :=
  (observerGap_iff_cluster S hS Φ hB τ hphys m0 one_pos).mpr (flowClusterAbs_of_atG S hS Φ τ m1 h)

end Consumer

/-! ## 2. Exact transport of a connected read through the skeleton -/

section Skeleton

variable {Ωf Ωc Ωr Bf Bc : Type*} [MeasurableSpace Ωf] [MeasurableSpace Ωc] [MeasurableSpace Ωr]
  {μf : Measure Ωf} {μc : Measure Ωc} {μr : Measure Ωr} [SFinite μc] [SFinite μr]
  {glue : Ωc × Ωr → Ωf}

/-- **The connected read of two skeleton observables is the effective one**: under a measure-preserving `glue`
with `π ∘ glue = fst`, `⟨(F∘π)(H∘π)⟩ − ⟨F∘π⟩⟨H∘π⟩` under the normalized fine density equals
`⟨F H⟩ − ⟨F⟩⟨H⟩` under the normalized effective density. DERIVED: no numeral. -/
theorem conn_skeleton (hg : MeasurePreserving glue (μc.prod μr) μf) {π : Ωf → Ωc}
    (hπ : ∀ V R, π (glue (V, R)) = V) (E : Bc → Bf) (ρ : Bf → Ωf → ℝ) (ζ : Bc) (F H : Ωc → ℝ)
    (hFH : Integrable (fun U => F (π U) * H (π U) * ρ (E ζ) U) μf)
    (hF : Integrable (fun U => F (π U) * ρ (E ζ) U) μf)
    (hH : Integrable (fun U => H (π U) * ρ (E ζ) U) μf) (hρ : Integrable (ρ (E ζ)) μf) :
    (∫ U, F (π U) * H (π U) * ρ (E ζ) U ∂μf) / (∫ U, ρ (E ζ) U ∂μf)
        - (∫ U, F (π U) * ρ (E ζ) U ∂μf) / (∫ U, ρ (E ζ) U ∂μf)
          * ((∫ U, H (π U) * ρ (E ζ) U ∂μf) / (∫ U, ρ (E ζ) U ∂μf))
      = (∫ V, F V * H V * GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)
            / (∫ V, GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)
        - (∫ V, F V * GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)
            / (∫ V, GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)
          * ((∫ V, H V * GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)
            / (∫ V, GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)) := by
  have h1 := WindowRelay.expect_skeleton hg hπ E ρ ζ (fun V => F V * H V) hFH hρ
  have h2 := WindowRelay.expect_skeleton hg hπ E ρ ζ F hF hρ
  have h3 := WindowRelay.expect_skeleton hg hπ E ρ ζ H hH hρ
  try simp only at h1
  rw [h1, h2, h3]

end Skeleton

/-! ## 3. The reduction at the tower -/

section Tower

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The observer-skeleton condition**: the observer's lattice read of every pair minus `eff k X Y` tends to
`0` along `ultra`. DERIVED: `0` the vanishing error. -/
def SkeletonReads (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (eff : ℕ → MonoG G → MonoG G → ℝ) : Prop :=
  ∀ X Y : MonoG G,
    Tendsto (fun k => latSFG S Φ.map k (pairFamG τ X Y) - eff k X Y) (ultra : Filter ℕ) (𝓝 0)

/-- **The effective reads cluster**: some `c > 0` with, for every pair of margin monomials, a constant `C` and,
at every `n`, along `ultra`, the connected `eff` read at time `a_{m₁} n` at most `C e^{−(c/L) a_{m₁} n}`.
DERIVED: `0` the lower end of `c`. -/
def SkeletonCluster (S : Sched G) (τ : Fin 4) (r L : ℝ) (m1 : ℕ)
    (eff : ℕ → MonoG G → MonoG G → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P Q : MarginMonoG G τ r, ∃ C : ℝ, ∀ n : ℕ, ∀ᶠ k in (ultra : Filter ℕ),
    |eff k P.1 (monoShiftG (timeVecG S m1 τ n) Q.1)
        - eff k P.1 (emptyMonoG G) * eff k (emptyMonoG G) Q.1|
      ≤ C * Real.exp (-(c / L) * (S.a m1 * n))

/-- **The effective reads converge to the observer's kernel** under `SkeletonReads`. DERIVED: `0` the error. -/
theorem tendsto_eff (S : Sched G) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map) (τ : Fin 4)
    {eff : ℕ → MonoG G → MonoG G → ℝ} (hR : SkeletonReads S Φ τ eff) (X Y : MonoG G) :
    Tendsto (fun k => eff k X Y) (ultra : Filter ℕ) (𝓝 (kernFG S Φ τ X Y)) := by
  have h2 := (tendsto_contSFG S Φ.map hB (pairFamG τ X Y)).sub (hR X Y)
  rw [sub_zero] at h2
  exact h2.congr (fun k => sub_sub_cancel _ _)

/-- **The reduction**: `SkeletonReads` and `SkeletonCluster` give the observer's clustering along the grid
`m₁`. DERIVED: no numeral. -/
theorem flowClusterAt_of_skeleton (S : Sched G) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r L : ℝ} (m1 : ℕ) {eff : ℕ → MonoG G → MonoG G → ℝ}
    (hR : SkeletonReads S Φ τ eff) (hC : SkeletonCluster S τ r L m1 eff) :
    FlowClusterAtG S Φ τ r L m1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨c, hc, hC⟩ := hC
  refine ⟨c, hc, fun P Q => ?_⟩
  obtain ⟨C, hCb⟩ := hC P Q
  refine ⟨C, fun n => ?_⟩
  have te := tendsto_eff S Φ hB τ hR
  have hlim := ((te P.1 (monoShiftG (timeVecG S m1 τ n) Q.1)).sub
    ((te P.1 (emptyMonoG G)).mul (te (emptyMonoG G) Q.1))).abs
  exact le_of_tendsto hlim (hCb n)

/-- **The observer's gap from the skeleton**: `SkeletonReads` and `SkeletonCluster` at unit `L = 1` along any
grid `m₁` give the consumer's input `hg` at every step `m₀`. DERIVED: `1` the rate's unit. -/
theorem observerGap_of_skeleton (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m1 m0 : ℕ)
    {eff : ℕ → MonoG G → MonoG G → ℝ} (hR : SkeletonReads S Φ τ eff)
    (hC : SkeletonCluster S τ r 1 m1 eff) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (transferNG S hS Φ hB τ hphys m0) ρ :=
  observerGap_of_clusterAt S hS Φ hB τ hphys m1 m0 (flowClusterAt_of_skeleton S Φ hB τ m1 hR hC)

/-- **Test: the lattice reads satisfy `SkeletonReads` with no input.** DERIVED: `0` the error. -/
theorem skeletonReads_self (S : Sched G) (Φ : GFlow G) (τ : Fin 4) :
    SkeletonReads S Φ τ (fun k X Y => latSFG S Φ.map k (pairFamG τ X Y)) := by
  intro X Y
  simp only [sub_self]
  exact tendsto_const_nhds

/-- **Test: with `eff` unrestricted the pair restates the consumer.** `FlowClusterAtG` holds iff some `eff`
satisfies `SkeletonReads` and `SkeletonCluster`. DERIVED: no numeral. -/
theorem consumer_iff_exists_eff (S : Sched G) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r L : ℝ} (m1 : ℕ) :
    FlowClusterAtG S Φ τ r L m1
      ↔ ∃ eff : ℕ → MonoG G → MonoG G → ℝ, SkeletonReads S Φ τ eff ∧ SkeletonCluster S τ r L m1 eff := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun _ X Y => contSFG S Φ.map (pairFamG τ X Y), fun X Y => ?_, c, hc, fun P Q => ?_⟩
    · have h1 := (tendsto_contSFG S Φ.map hB (pairFamG τ X Y)).sub_const
        (contSFG S Φ.map (pairFamG τ X Y))
      rw [sub_self] at h1
      exact h1
    · obtain ⟨C, hC⟩ := h P Q
      exact ⟨C, fun n => Filter.Eventually.of_forall (fun _ => hC n)⟩
  · rintro ⟨eff, hR, hC⟩
    exact flowClusterAt_of_skeleton S Φ hB τ m1 hR hC

/-- **The exact instance**: if along `ultra` every lattice read of the observer is the normalized fine integral
of a skeleton observable `A k X Y ∘ π k` for a measure-preserving `glue k` with `π k ∘ glue k = fst`, then
`SkeletonReads` holds with `eff` the normalized effective reads (`WindowRelay.expect_skeleton`). DERIVED: `0`
the error. -/
theorem skeletonReads_of_factor (S : Sched G) (Φ : GFlow G) (τ : Fin 4)
    {Ωf Ωc Ωr : ℕ → Type*} [∀ k, MeasurableSpace (Ωf k)] [∀ k, MeasurableSpace (Ωc k)]
    [∀ k, MeasurableSpace (Ωr k)] (μf : ∀ k, Measure (Ωf k)) (μc : ∀ k, Measure (Ωc k))
    (μr : ∀ k, Measure (Ωr k)) [∀ k, SFinite (μc k)] [∀ k, SFinite (μr k)]
    (glue : ∀ k, Ωc k × Ωr k → Ωf k)
    (hg : ∀ k, MeasurePreserving (glue k) ((μc k).prod (μr k)) (μf k))
    (π : ∀ k, Ωf k → Ωc k) (hπ : ∀ k V R, π k (glue k (V, R)) = V)
    (w : ∀ k, Ωf k → ℝ) (hw : ∀ k, Integrable (w k) (μf k))
    (A : ∀ k, MonoG G → MonoG G → Ωc k → ℝ)
    (hint : ∀ k X Y, Integrable (fun U => A k X Y (π k U) * w k U) (μf k))
    (hfac : ∀ᶠ k in (ultra : Filter ℕ), ∀ X Y : MonoG G,
      latSFG S Φ.map k (pairFamG τ X Y)
        = (∫ U, A k X Y (π k U) * w k U ∂(μf k)) / ∫ U, w k U ∂(μf k)) :
    SkeletonReads S Φ τ (fun k X Y =>
      (∫ V, A k X Y V * GapSideExactDecimation.effDens (μr k) (glue k) (id : Unit → Unit)
          (fun _ => w k) () V ∂(μc k))
        / ∫ V, GapSideExactDecimation.effDens (μr k) (glue k) (id : Unit → Unit)
          (fun _ => w k) () V ∂(μc k)) := by
  intro X Y
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hfac] with k hk
  have e := WindowRelay.expect_skeleton (hg k) (hπ k) (id : Unit → Unit) (fun _ => w k) ()
    (A k X Y) (hint k X Y) (hw k)
  try simp only [id_eq] at e
  simp only [hk X Y, e, sub_self]

end Tower

/-! ## 4. The form-norm error and the angle form -/

section Angle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A read changes by at most the form distances**: for `‖T‖ ≤ 1`,
`|⟪u, T v⟫ − ⟪u′, T v′⟫| ≤ ‖u − u′‖ ‖v‖ + ‖u′‖ ‖v − v′‖`. DERIVED: `1` the contraction bound. -/
theorem abs_inner_sub_le (T : E →L[ℝ] E) (hT : ‖T‖ ≤ 1) (u u' v v' : E) :
    |inner ℝ u (T v) - inner ℝ u' (T v')| ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
  have hc : ∀ x : E, ‖T x‖ ≤ ‖x‖ := fun x =>
    (T.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) hT)
  have e : inner ℝ u (T v) - inner ℝ u' (T v')
      = inner ℝ (u - u') (T v) + inner ℝ u' (T (v - v')) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [e]
  calc |inner ℝ (u - u') (T v) + inner ℝ u' (T (v - v'))|
      ≤ |inner ℝ (u - u') (T v)| + |inner ℝ u' (T (v - v'))| := abs_add_le _ _
    _ ≤ ‖u - u'‖ * ‖T v‖ + ‖u'‖ * ‖T (v - v')‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hc v) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hc _) (norm_nonneg _))

/-- Powers of a symmetric operator are symmetric. DERIVED: `0` the empty power; `1` the step. -/
theorem pow_symm {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) :
    ∀ (n : ℕ) (u v : E), inner ℝ ((A ^ n) u) v = inner ℝ u ((A ^ n) v)
  | 0, u, v => by simp
  | n + 1, u, v => by
    have e1 : (A ^ (n + 1)) u = (A ^ n) (A u) := by rw [pow_succ, mul_apply_eq_comp]
    have e2 : (A ^ (n + 1)) v = A ((A ^ n) v) := by rw [pow_succ', mul_apply_eq_comp]
    rw [e1, e2, pow_symm hA n, hA]

/-- **The angle form, one power**: a symmetric contraction whose reads between vectors of `K` decay at `ρ`, and
every vector within `δ‖f‖` of `K`, has `‖A^T f‖² ≤ (ρ^{2T}(1 + δ)² + 2δ + δ²) ‖f‖²`. DERIVED: `1` the
contraction bound; `2` the square and the doubled power. -/
theorem sq_norm_pow_le_of_angle {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hA1 : ‖A‖ ≤ 1) {K : Set E} {ρ δ : ℝ} (hδ : 0 ≤ δ)
    (hK : ∀ k ∈ K, ∀ s : ℕ, |inner ℝ k ((A ^ s) k)| ≤ ρ ^ s * ‖k‖ ^ 2)
    (hUA : ∀ f : E, ∃ k ∈ K, ‖f - k‖ ≤ δ * ‖f‖) (T : ℕ) (f : E) :
    ‖(A ^ T) f‖ ^ 2 ≤ (ρ ^ (2 * T) * (1 + δ) ^ 2 + (2 * δ + δ ^ 2)) * ‖f‖ ^ 2 := by
  obtain ⟨k, hkK, hkf⟩ := hUA f
  set B := A ^ (2 * T) with hBdef
  have hc : ∀ x : E, ‖B x‖ ≤ ‖x‖ := fun x =>
    (StrongTransferGap.norm_pow_apply_le A x (2 * T)).trans
      (mul_le_of_le_one_left (norm_nonneg x) (pow_le_one₀ (norm_nonneg A) hA1))
  have hsq : ‖(A ^ T) f‖ ^ 2 = inner ℝ f (B f) := by
    rw [← real_inner_self_eq_norm_sq, pow_symm hA T, ← mul_apply_eq_comp, ← pow_add,
      ← two_mul]
  set e := f - k with he
  have hfe : f = k + e := by rw [he]; abel
  have hk_le : ‖k‖ ≤ (1 + δ) * ‖f‖ := by
    have : ‖k‖ ≤ ‖f‖ + ‖e‖ := by
      have h := norm_sub_le f e
      rwa [show f - e = k by rw [he]; abel] at h
    nlinarith
  have hsplit : inner ℝ f (B f) = inner ℝ k (B k) + inner ℝ k (B e) + inner ℝ e (B f) := by
    calc inner ℝ f (B f) = inner ℝ (k + e) (B f) := by rw [← hfe]
      _ = inner ℝ k (B f) + inner ℝ e (B f) := inner_add_left _ _ _
      _ = inner ℝ k (B (k + e)) + inner ℝ e (B f) := by rw [← hfe]
      _ = inner ℝ k (B k) + inner ℝ k (B e) + inner ℝ e (B f) := by
          rw [map_add, inner_add_right]
  have t1 : inner ℝ k (B k) ≤ ρ ^ (2 * T) * ((1 + δ) ^ 2 * ‖f‖ ^ 2) := by
    have h := (le_abs_self _).trans (hK k hkK (2 * T))
    have hk2 : ‖k‖ ^ 2 ≤ (1 + δ) ^ 2 * ‖f‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hk_le 2
    have hρ : 0 ≤ ρ ^ (2 * T) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg ρ) T
    exact h.trans (mul_le_mul_of_nonneg_left hk2 hρ)
  have t2 : inner ℝ k (B e) ≤ (1 + δ) * δ * ‖f‖ ^ 2 := by
    calc inner ℝ k (B e) ≤ ‖k‖ * ‖B e‖ := real_inner_le_norm _ _
      _ ≤ ‖k‖ * ‖e‖ := mul_le_mul_of_nonneg_left (hc e) (norm_nonneg _)
      _ ≤ ((1 + δ) * ‖f‖) * (δ * ‖f‖) :=
          mul_le_mul hk_le hkf (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))
      _ = (1 + δ) * δ * ‖f‖ ^ 2 := by ring
  have t3 : inner ℝ e (B f) ≤ δ * ‖f‖ ^ 2 := by
    calc inner ℝ e (B f) ≤ ‖e‖ * ‖B f‖ := real_inner_le_norm _ _
      _ ≤ ‖e‖ * ‖f‖ := mul_le_mul_of_nonneg_left (hc f) (norm_nonneg _)
      _ ≤ (δ * ‖f‖) * ‖f‖ := mul_le_mul_of_nonneg_right hkf (norm_nonneg _)
      _ = δ * ‖f‖ ^ 2 := by ring
  rw [hsq, hsplit]
  calc inner ℝ k (B k) + inner ℝ k (B e) + inner ℝ e (B f)
      ≤ ρ ^ (2 * T) * ((1 + δ) ^ 2 * ‖f‖ ^ 2) + (1 + δ) * δ * ‖f‖ ^ 2 + δ * ‖f‖ ^ 2 :=
        add_le_add (add_le_add t1 t2) t3
    _ = (ρ ^ (2 * T) * (1 + δ) ^ 2 + (2 * δ + δ ^ 2)) * ‖f‖ ^ 2 := by ring

/-- **The angle form gives a gap**: under the hypotheses of `sq_norm_pow_le_of_angle`, if at some power
`T ≥ 1` the coefficient is at most `q ∈ (0, 1)`, then `‖A‖ ≤ λ` for some `λ ∈ (0, 1)` (`λ = q^{1/(2T)}`).
DERIVED: `1` the least power and the top of the rate; `2` the square root. -/
theorem gap_of_angle {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hA1 : ‖A‖ ≤ 1) {K : Set E} {ρ δ : ℝ} (hδ : 0 ≤ δ)
    (hK : ∀ k ∈ K, ∀ s : ℕ, |inner ℝ k ((A ^ s) k)| ≤ ρ ^ s * ‖k‖ ^ 2)
    (hUA : ∀ f : E, ∃ k ∈ K, ‖f - k‖ ≤ δ * ‖f‖) {T : ℕ} (hT : 1 ≤ T) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hqT : ρ ^ (2 * T) * (1 + δ) ^ 2 + (2 * δ + δ ^ 2) ≤ q) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ ‖A‖ ≤ lam := by
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq1 : Real.sqrt q < 1 := by
    have := Real.sqrt_lt_sqrt hq0.le hq1
    rwa [Real.sqrt_one] at this
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hpow : ‖A ^ T‖ ≤ Real.sqrt q := by
    refine ContinuousLinearMap.opNorm_le_bound _ hsq0.le fun f => ?_
    have h := sq_norm_pow_le_of_angle hA hA1 hδ hK hUA T f
    have h2 : ‖(A ^ T) f‖ ^ 2 ≤ (Real.sqrt q * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq0.le]
      exact h.trans (mul_le_mul_of_nonneg_right hqT (sq_nonneg _))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  refine ⟨Real.sqrt q ^ ((T : ℝ)⁻¹), Real.rpow_pos_of_pos hsq0 _,
    Real.rpow_lt_one hsq0.le hsq1 (inv_pos.mpr (by exact_mod_cast (show 0 < T by omega))), ?_⟩
  refine WindowRelay.norm_le_of_norm_pow_le hA hT (Real.rpow_pos_of_pos hsq0 _) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul hsq0.le, inv_mul_cancel₀ hT0, Real.rpow_one]
  exact hpow

end Angle

/-! ## 5. The floor of a fixed error -/

section Floor

/-- The toy transfer: the skeleton coordinate is forgotten after one step, the off-skeleton coordinate is kept.
DERIVED: `0` the skeleton coordinate and the time origin; `1` the off-skeleton coordinate. -/
def toyT (n : ℕ) (u : Fin 2 → ℝ) : Fin 2 → ℝ := ![if n = 0 then u 0 else 0, u 1]

/-- **A reading at form distance `δ` from the skeleton reads `δ²` at every positive time.**
DERIVED: `2` the toy's dimension and the square. -/
theorem toy_read {n : ℕ} (hn : n ≠ 0) (s δ : ℝ) :
    ∑ i, ![s, δ] i * toyT n ![s, δ] i = δ ^ 2 := by
  simp [toyT, Fin.sum_univ_two, hn, sq]

/-- **A skeleton reading reads `0` at every positive time.** DERIVED: `0` the read. -/
theorem toy_skeleton {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    ∑ i, ![s, 0] i * toyT n ![s, 0] i = 0 := by
  simp [toyT, Fin.sum_univ_two, hn]

/-- **The reading's squared form distance from the skeleton reading is `δ²`.** DERIVED: `2` the square. -/
theorem toy_dist (s δ : ℝ) : ∑ i, (![s, δ] i - ![s, 0] i) ^ 2 = δ ^ 2 := by
  simp [Fin.sum_univ_two]

/-- **A fixed non-zero floor is never an exponential decay.** DERIVED: `0` the floor and the rate's lower
end; `2` the square. -/
theorem no_decay_of_floor {δ : ℝ} (hδ : δ ≠ 0) :
    ¬ ∃ C c : ℝ, 0 < c ∧ ∀ n : ℕ, n ≠ 0 → δ ^ 2 ≤ C * Real.exp (-(c * n)) := by
  rintro ⟨C, c, hc, h⟩
  have hpos : 0 < δ ^ 2 := lt_of_le_of_ne (sq_nonneg δ) (Ne.symm (pow_ne_zero 2 hδ))
  have ht : Tendsto (fun n : ℕ => C * Real.exp (-(c * n))) atTop (𝓝 (C * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)).const_mul C
  rw [mul_zero] at ht
  obtain ⟨n, hn1, hn2⟩ := ((ht.eventually (gt_mem_nhds hpos)).and (eventually_ne_atTop 0)).exists
  exact absurd (h n hn2) (not_le.mpr hn1)

end Floor

/-! ## 6. The window's physical side and the hop rate -/

section Window

/-- **The window has a fixed physical side along a measured tower**: from the band `c a ≤ m′ ≤ 2c a` and the
window `C ≤ 2^j m′ ≤ 2C`, `C/(2c) ≤ 2^j a ≤ 2C/c`. DERIVED: `2` the band's and the window's doubling. -/
theorem window_side_phys {a m c C : ℝ} {j : ℕ} (hc : 0 < c) (hband : c * a ≤ m ∧ m ≤ 2 * c * a)
    (hwin : C ≤ 2 ^ j * m ∧ 2 ^ j * m ≤ 2 * C) :
    C / (2 * c) ≤ 2 ^ j * a ∧ 2 ^ j * a ≤ 2 * C / c := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  constructor
  · rw [div_le_iff₀ (by linarith)]
    calc C ≤ 2 ^ j * m := hwin.1
      _ ≤ 2 ^ j * (2 * c * a) := mul_le_mul_of_nonneg_left hband.2 hp.le
      _ = 2 ^ j * a * (2 * c) := by ring
  · rw [le_div_iff₀ hc]
    calc 2 ^ j * a * c = 2 ^ j * (c * a) := by ring
      _ ≤ 2 ^ j * m := mul_le_mul_of_nonneg_left hband.1 hp.le
      _ ≤ 2 * C := hwin.2

/-- **A rate per window hop is a physical rate**: `0 < ρ_w < 1`, a hop of physical length `ℓ > 0`, and
`t ≤ (h + 1) ℓ` give `ρ_w^h ≤ ρ_w⁻¹ e^{−(−log ρ_w / ℓ) t}`. DERIVED: `1` the hop offset. -/
theorem rate_of_hops {ρw ℓ t : ℝ} {h : ℕ} (h0 : 0 < ρw) (h1 : ρw < 1) (hℓ : 0 < ℓ)
    (ht : t ≤ (h + 1) * ℓ) :
    ρw ^ h ≤ ρw⁻¹ * Real.exp (-(-Real.log ρw / ℓ) * t) := by
  have hl : Real.log ρw < 0 := Real.log_neg h0 h1
  have e1 : ρw ^ h = ρw⁻¹ * ρw ^ (h + 1) := by
    rw [pow_succ, mul_comm (ρw ^ h), ← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
  have e2 : ρw ^ (h + 1) = Real.exp (((h + 1 : ℕ) : ℝ) * Real.log ρw) := by
    rw [Real.exp_nat_mul, Real.exp_log h0]
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr h0.le)
  rw [show -(-Real.log ρw / ℓ) * t = Real.log ρw * t / ℓ by ring, le_div_iff₀ hℓ]
  calc ((h + 1 : ℕ) : ℝ) * Real.log ρw * ℓ = Real.log ρw * ((h + 1) * ℓ) := by push_cast; ring
    _ ≤ Real.log ρw * t := mul_le_mul_of_nonpos_left ht hl.le

end Window

end MassGap.ObserverSkeleton

end

#print axioms MassGap.ObserverSkeleton.observerGap_iff_cluster
#print axioms MassGap.ObserverSkeleton.observerGap_of_clusterAt
#print axioms MassGap.ObserverSkeleton.conn_skeleton
#print axioms MassGap.ObserverSkeleton.tendsto_eff
#print axioms MassGap.ObserverSkeleton.flowClusterAt_of_skeleton
#print axioms MassGap.ObserverSkeleton.observerGap_of_skeleton
#print axioms MassGap.ObserverSkeleton.skeletonReads_self
#print axioms MassGap.ObserverSkeleton.consumer_iff_exists_eff
#print axioms MassGap.ObserverSkeleton.skeletonReads_of_factor
#print axioms MassGap.ObserverSkeleton.abs_inner_sub_le
#print axioms MassGap.ObserverSkeleton.pow_symm
#print axioms MassGap.ObserverSkeleton.sq_norm_pow_le_of_angle
#print axioms MassGap.ObserverSkeleton.gap_of_angle
#print axioms MassGap.ObserverSkeleton.toy_read
#print axioms MassGap.ObserverSkeleton.toy_skeleton
#print axioms MassGap.ObserverSkeleton.toy_dist
#print axioms MassGap.ObserverSkeleton.no_decay_of_floor
#print axioms MassGap.ObserverSkeleton.window_side_phys
#print axioms MassGap.ObserverSkeleton.rate_of_hops
