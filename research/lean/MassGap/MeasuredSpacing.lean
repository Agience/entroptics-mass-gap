import Mathlib
import MassGap.MeasuredSeed
import MassGap.FlowClusterG
import MassGap.ClayStatementG

/-!
# MassGap.MeasuredSpacing — the construction at a measured tower

The root `MassGap.ClayStatement` (`ClayStatementG`) builds its continuum, for every compact simple group `G` of
the tree, at the dyadic spacing `a_k = dySpacingG G k` with the coupling of step `k` selected by a measured read:
the measured mass `m′(β)` of the tensor reading of `G` (in lattice units, `1/ξ`) lies in `[c a_k, 2c a_k]` for one
unit `c > 0` (`MeasuredTower.MeasTowerG`). `ClayStatementDy` (`ClayStatement.lean`) is the same statement at the
frozen tower, the coupling `dyBeta k` chosen so that the two-loop spacing `aRun N (dyBeta k)` equals `a_k`. The
spacing sequence, every clause and every constant are the same in the two; only the state of each step differs.
This module classifies where the two-loop tower enters, proves the facts of the measured schedule that need more
than `ClayTreeG`, compares the two statements, and proves the per-step gap at `SU(N)` from the measured seed, which
needs nothing in `aRun`. Declarations are in the namespace `MassGap.MeasuredSpacing`; the measured read, the
band, the tower, `schedAlongG` and `AsymScalingG` are in `MassGap.MeasuredTower`.

## 1. Where the two-loop tower enters

File:line in `research/lean/MassGap`. Class (i): a length unit (smearing, time step, normalization by `a_k`);
class (ii): a short-distance clause; class (iii): other.

| where | what | class |
|---|---|---|
| `ContinuumSchwinger.lean:107` `dySpacing N k = aRun N 1 / 2^(k+1)`; `ClayTreeG.lean:167` `dySpacingG` | the spacing; `aRun` enters only as the constant `aRun N 1`, a choice of length unit ("any positive reference coupling serves") | (i) |
| `ContinuumSchwinger.lean:140,147,156` `exists_coupling`, `dyBeta`, `aRun_dyBeta`; `ClayTreeG.lean:204` `dyBetaG` | the coupling of step `k` solves `aRun β = a_k` (intermediate values of the continuous `aRun`): the only place the two-loop running selects anything | (iii), the state |
| `ContinuumSchwinger.lean:227,234` `stateK`, `latSk` | state `periodicState hN (dyBeta k)`, read at spacing `dySpacing N k` | (iii) state; (i) smearing |
| `ContinuumSchwinger.lean:1089` `timeVec`; `ClayTreeG.lean:331` `timeVecG` | the dyadic time vector | (i) |
| `ClayStatement.lean:15–19` | the construction's description at the frozen tower | (iii), text |
| `ClayStatement.lean:287,295` `IsClassCfg`, `ClassicalLead`; `ClayStatementG.lean:218` | `(L(U) − L(1))/a^d → P` as `a → 0⁺`, `a` a free variable | (ii); no schedule |
| `ClayStatement.lean:360,367` `locField`, `latT` | connected subtraction `stateK hN k (op b)`, reading `latSk` | (iii) state; (i) smearing |
| `ClayStatement.lean:459` `ChannelTie` | `ClassicalLead` of the bare basis at dimension `4` | (ii); no schedule |
| `ClayStatement.lean:469` `TopNorm`; `ClayStatementG.lean:286` | `zq k · a_k⁴ → 2` | (ii) renormalization factor per step, read against `a_k` only |
| `ClayStatement.lean:597` `ApertureConv` | `UniformBoundF`, `contSF`, `schwSFM` of `energy0` (on `latSk`; `ContinuumFlow.lean:384,460`, `ObserverOSEuclidS.lean:392`) | (iii) state; (i) smearing |
| `ClayStatement.lean:612` `ScalarTie`; `ClayStatementG.lean:383` | `Ztr k · a_k⁴ → N/8` | (ii) renormalization factor per step, read against `a_k` only |
| `ClayStatement.lean:549` `TwoPointKernel`; `ClayStatementG.lean` `TwoPointKernelG S ρ` | `G` the kernel of the continuum `contTr`: the clause reads the schedule through `contT` / `contTG S` (the limit of the lattice readings at `S`); its text contains no spacing and no coupling | (ii) |
| `ClayStatement.lean:620,626,631` `b0`, `afConst`, `AFCoefficient`; `ClayStatementG.lean:391` | `r⁸ G(r) (log r)² → 12 dim 𝔤/(π⁴ b₀²)` on the kernel `G` | (ii); `b₀` the one-loop coefficient; no spacing, no coupling, no schedule |
| `ClayStatement.lean:704` `shiftT`; `ClayStatementG.lean:404` `shiftTG` | translation by the dyadic time vector | (i) |
| `ClayStatement.lean:719` `mixLatT` | `latSk` | (iii) state; (i) smearing |
| `ClayStatement.lean:742` `LinkTS` (`:748`); `ClayStatementG.lean:432` | `w (shiftT m P) = X.base.time a_m (w P)` | (i) time step |
| `ClayStatement.lean:769` `ObsGen` (`:777–778`); `ClayStatementG.lean:455` | the shift by the time vector acts as `X.base.time a_m` | (i) time step |
| `ClayStatement.lean:887,893` `cField`, `latC`; `ClayStatementG.lean:542,546` | state; smearing | (iii); (i) |
| `ClayStatement.lean:1002` `LinkC` (`:1008`); `ClayStatementG.lean:633` | `X.base.time a_m` | (i) time step |
| `ClayStatement.lean:1039` `ClayData` (first conjunct) | `X.SM = schwSFM` | (iii) state; (i) smearing |
| `ClayStatement.lean:1091` `MassGap.ClayStatementDy` | the statement at the frozen tower | (iii) |
| `ClayStatement.lean:1103–1152, 1242–1392, 1498, 1589`; `ClayStatementG.lean:947–1042` | proofs reading `a_k > 0`, `a_k → 0`, the dyadic step | (i), proof side |
| `ObserverEnergyBox.lean:364`, `ContinuumFlow.lean:162,174,349` | the energy density `a_k⁻⁴ (O ∘ V_k)`, `PhysRange`, `PosPreserving`, `canonZ` | (i) |
| `ClayTreeG.lean:243,253` `canonSched`, `schedSU`; `ClayStatementG.lean:710` `ClayStatementAtG := ClayStatementAtP (canonSched G) …` | the schedule of the frozen tower | (iii) |
| `ClayStatementG.lean:726` `ClayStatementOf := ∃ βs, MeasTowerG G βs ∧ … ClayStatementAtP (schedAlongG G βs) …` | the schedule of the root, selected by the band | (iii) |

Reading of the table: the two-loop tower selects the state of each step (class (iii), through `dyBeta`,
`dyBetaG`), and nothing else. Every spacing in a clause is the dyadic length `a_k`, in which `aRun` is a constant.
No class (ii) clause text contains `aRun` or a coupling; `TopNorm` and `ScalarTie` contain `a_k⁴`;
`TwoPointKernel` reads the schedule through the continuum limit, as every clause on local fields does.
`ClayStatementAtP S K W D` (`ClayStatementG.lean:698`) is the full statement at any schedule `S`, clause for
clause (`clayDataP_SU_iff` is `Iff.rfl` at `schedSU`).

## 2. The measured schedule (defined in `MeasuredTower`; facts proved)

* The measured read over `G`. `DecaysAtG`, `measMassOfG`: the decay rate of a reading's connected correlation,
  the definitions of `SubstrateDecode` over `IConf G` (`snormG_eq`). `tensorEnergyG G x`: the `(0, 1)`-plaquette
  density minus the `(2, 3)`-plaquette density of `plaqFieldG`. At `SU(N)` they are `SubstrateDecode`'s
  (`tensorEnergyG_SU`, `mUG_SU`). `measLenG G ν` (the measured spacing `1/ξ` at unit physical mass) is `0` exactly
  at the two degenerate reads, `m′ = 0` (no lock) or `m′ = ⊤` (a vanishing correlation, `measLenG_point`), and
  positive exactly at a finite lock (`measLenG_pos_iff`, `measLenG_eq_zero_iff`).
* `UnitLockG G`: `m′(β) → 0` and eventually `0 < m′(β)`; at `SU(N)` from `LockPersists`
  (`unitLockG_of_lockPersists`). Under it `measSpacingG → 0` and is eventually positive.
* `BandG G c k β`: `ofReal (c a_k) ≤ m′(β) ≤ ofReal (2c a_k)`. `MeasTowerG G βs`: `βs → ∞`, and some unit
  `c > 0` has `BandG G c k (βs k)` eventually. The band is the lock (`BandG.pos`, `BandG.ne_top`). Along a tower:
  `c a_k ≤ measSpacingG(βs k) ≤ 2c a_k` (`BandG.spacing`); the tensor channel's physical mass
  `measSpacingG/a_k ∈ [c, 2c]` (`MeasTowerG.physMass`); `measSpacingG(βs k) → 0`; the unit tie with constant `c`
  in the step's own spacing (`MeasTowerG.unitTie`). No clause reads `c`.
* `schedAlongG G βs : Sched G`: spacing `dySpacingG G`, state `periodicStateG G (βs k)`;
  `canonSched G = schedAlongG G (dyBetaG G)` (`canonSched_eq_schedAlongG`, `rfl`). For every tower: `SchedOS`
  (`schedOS_alongG`), `SchedShiftInv`, `SchedAxisInv`, `SchedTransInv` (all in `SchedAlong`).
* Existence. `MeasSweepG G` (one unit `c` with every band reached by couplings beyond any `B`) gives a tower
  (`exists_measTowerG`). `measSweepG_of_continuous`: the unit lock and continuity of `β ↦ measSpacingG G β` on a
  half-line give `MeasSweepG` at `c = 1` (intermediate values at `3a_k/2`); the measured counterpart of
  `exists_coupling`, which takes intermediate values of the continuous `aRun`.
* Comparison with the frozen tower. `AsymScalingG G R`: `measSpacingG(dyBetaG k)/a_k → R ∈ (0, ∞)`, asymptotic
  scaling of the tensor mass along the frozen construction. `measTowerG_of_scaling`: it makes `dyBetaG` a measured
  tower (unit `2R/3`). `unitTracksAlong_dy_of_scaling`: at `SU(N)` it gives `MeasuredSeed.UnitTracksAlong` along
  `dyFilter`. The converse is not proved.

## 3. The clauses under the measured schedule

Class (i), argued. The spacing is `a_k` in both constructions, so every class (i) occurrence reads verbatim: the
smearing `smear a_k`, the time vectors, `X.base.time a_m`, the normalization `a_k⁻⁴`. What differs is the physical
unit: at a measured tower it is the length at which the tensor channel's mass is in `[c, 2c]`; at `dyBeta` it is
fixed by the two-loop formula. The proofs that read the schedule read `a_k > 0`, `a_k → 0`; the flowed
reconstruction reads `SchedOS` (`FlowG.lean:92`), proved here for every tower.

Class (ii), argued clause by clause.

* `ClassicalLead`, `ChannelTie`, `Composites.Tied`: `a` is a free variable tending to `0⁺` on classical
  configurations; no schedule enters. No perturbative tie.
* `TopNorm`, `ScalarTie`: `zq k · a_k⁴ → 2`, `Ztr k · a_k⁴ → N/8`, `Ztr`, `zq` existential. They count the
  dimension of the bare operator against the spacing of the smearing, and ask that the finite part of the
  renormalization tends to `1` as `g₀ → 0`. They read `a_k` and `β_k → ∞` (part of the tower). No rate of
  `g₀ → 0` against `a_k` is read: the trace channel and the topological density renormalize multiplicatively by
  `1 + O(g₀²)`. The perturbative tie does not enter these clauses.
* `TwoPointKernel`, `AFCoefficient`: `AFCoefficient` is a statement on the kernel `G`; `r⁸ G(r)` is unit-free and
  `(log λr)²/(log r)² → 1` for every fixed `λ > 0`, so it is independent of the physical unit, and of `c`. The
  statement keeps no tie to `aRun`. A proof of it by lattice perturbation theory along the tower needs `g₀²(β_k)`
  to be the running coupling at `a_k` at leading logarithm: `log a_k / log aRun(β_k) → 1`, equivalently (band)
  `log m′(β_k) / log aRun(β_k) → 1`. That is where the tie sits if that route is used. It is not
  `UnitTracksRun`: it is two-sided and logarithmic, where `UnitTracksRun` is one-sided at the leading power; neither
  implies the other. It is strictly weaker than asymptotic scaling. `AFCoefficient` is an open input of the
  existing capstones (`hAF`), so no proved module consumes this condition.

## 4. The gap consequence (proved)

* `gapAt_unit_of_sectorSeed`: `SectorSeedMeasured hN` gives `c₀ > 0` with, at every large `β`, a lattice rate
  `r ∈ (0, 1)`, `GapAt (periodicGaugeInvData 0 0 hN β) r`, `PeriodicClayGapAt`, and `c₀ · measSpacing ≤ −log r`:
  the gap per lattice step is at least `c₀` times the measured unit mass. The seed side `n` is the window itself
  (`dyadicTorusDecay` at `n`, `torusLagClear_stepRate`, `physical_rate_ge` with `n · m′ ≤ C`); `WDelta2`, `nP` and
  `FixedWindowDecay`, written in `aRun`, are not used.
* `gapAlong_of_sectorSeed`, `gapAlong_of_reads`: along a measured tower of `SU(N)`, eventually in `k`,
  `GapAt (periodicGaugeInvDataG (SU N) 0 0 (βs k)) r` with `c₀ c ≤ −log r / a_k`. The band's lower edge
  (`BandG.spacing`, first half) replaces `UnitTracksRun`; the tower's existence comes through `MeasSweepG`. This
  is the hypothesis `hevk` of `FlowCapstone.kernF_cluster_of_fixedWindowDecay` (`FlowCapstone.lean:328`) with
  `aRun N (dyBeta k)` replaced by the step's spacing, the only place that proof reads `aRun`.
* `lattice_clusterSched`, `kernFG_cluster_of_stepGap`, `flowClusterAbs_of_stepGap`, `flowGapAt_of_stepGap`: the
  analogues of `FlowClusterG.lattice_clusterG`, `kernFG_cluster_of_fixedWindowDecayG`,
  `flowClusterAbsG_of_fixedWindowDecayG`, `gapAt_of_runSeedG`, over any dyadic schedule whose states are Wilson
  states, with the per-step gap as the input.
* `observerGap_of_sectorSeed`, `observerGap_of_reads`: `SectorSeedMeasured` (or `CoarseReadsFine`, `LongChainRead`,
  `ZeroFluxReadsMass`) and a measured tower give, for every flow over `schedAlongG (SU N) βs` with the uniform bound
  and a physical range, at every step `m₀`, `GapAt (transferNG (schedAlongG (SU N) βs) … m₀) ρ`, `ρ ∈ (0, 1)`: the
  gap input `hg` of `ClayGFinal.observerOSDataSLinkedGN` at the measured schedule. `UnitTracksRun` is not a
  hypothesis.

Not built: the remaining inputs of the `SU(N)` chain (`InputMerge.NarrowInputsAtMin`, `ClaySUFinal`,
`CompositesRenAll`) are stated at `stateK`; at a measured tower they are the hypotheses of
`ClayWiringG.clayStatementAtP_of_inputsG` and `ClayStatementG.clayStatementAtP_of_link` at
`S = schedAlongG (SU N) βs`, with `DiagBoundSep` of the local route along the tower. The seed and the reads are
stated at `SU(N)` only; the per-step gap over another `G` is not built.

## 5. The two statements

* The root. `ClayStatementG.ClayStatementOf G := ∃ βs, MeasTowerG G βs ∧ ∃ W D, (∀ τ O, O.refl τ ∈ D ↔ O ∈ D) ∧
  ClayStatementAtP (schedAlongG G βs) (constsG G) W D`; `ClayStatementSU`, `ClayStatementSO`, `ClayStatementUSp`,
  `ClayStatementClassical` and `ClayStatementG2`, …, `ClayStatementE8` read it; `MassGap.ClayStatement` is
  `∀ N ≥ 2, ClayStatementSU N` (`clayStatement_iff_SU`, `Iff.rfl`).
* The frozen tower. `ClayStatementOfDy G := ∃ W D, (…) ∧ ClayStatementAtG G W D`, with `ClayStatementSUDy`,
  `ClayStatementSODy`, `ClayStatementUSpDy`, `ClayStatementClassicalDy`; `MassGap.ClayStatementDy` is
  `∀ N ≥ 2, ClayStatementSUDy N` (`clayStatementDy_iff_SU`). `ClayStatementAt` is the parametric statement at the
  frozen tower (`clayStatementAt_iff_frozenTower`).
* The capstones of the tree conclude the frozen form: the `SU(N)` capstones `ClayStatementDy`, the exceptional
  groups `ClayStatementOfDy GX` (`GaugeG2.clayStatementG2_of_atG`, …), and the producers of `ClayStatementAtG`
  the frozen tower at one witness. `clayStatementMeasOf_of_atG`, `clayStatementMeasOf_of_of`,
  `clayStatementMeas_of_dy` and `clayStatementMeasClassical_of_frozen` lift each to the root under asymptotic
  scaling of the tensor mass; each capstone lifts by one application of them. No capstone has hypotheses at a
  measured schedule.

## 6. No clause weakened (argued)

* Every clause is the same predicate of the schedule (`ClayDataP S K`) with the same spacing `a_k` and the same
  constants (`constsG`); class (i) and (ii) clauses read `a_k`, `β_k → ∞` and the limit along `ultra`, all present.
* The freedom of the factor `2` and of the unit `c` is not read by any clause. Each clause is a statement about the
  limit along `ultra` of readings at `a_k`; along `ultra`, `m′/a_k`, which lies in `[c, 2c]` eventually, converges
  to some `R′ ∈ [c, 2c]`, and each clause is invariant under a constant change of the physical unit.
* The band, not `AFCoefficient`, pins the scaling of the construction. Without the band, `∃ βs` would allow a tower
  too fast for its spacings (`m′/a_k → ∞`) and a trivial limit; the band's two edges exclude that and a massless
  channel (`m′/a_k → 0`), and both degenerate reads.
* Non-triviality (`TensorNondeg`, `NonGaussianT`, the non-zero vectors, `CompNondeg`) and `AFCoefficient` are
  the same clauses.
* Comparison. The only formal comparison runs frozen ⇒ root, under asymptotic scaling of the tensor mass
  (`clayStatementMeasOf_of_atG`, `clayStatementMeas_of_dy`). Otherwise the two statements are formally
  incomparable: `∃ βs` adds freedom, `MeasTowerG` adds an obligation. The converse is not proved.

## Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the classification of §1; the readings of §3; the no-weakening argument of §6; that no module wires the
  gap into the `SU(N)` capstones at a measured tower.
* Assumed: `SectorSeedMeasured` (or the three reads) in the gap theorems; `MeasTowerG` there and in the statement;
  `MeasSweepG`, or `UnitLockG` and continuity of `measSpacingG` on a half-line, for existence; `AsymScalingG` in the
  comparison. `MeasSweepG` gives a positive tensor-channel lattice mass at arbitrarily large `β` (a cofinal set);
  `UnitLockG`, `SectorSeedMeasured` and the three reads each give one at every large `β`: a weak-coupling lattice
  gap in one channel, which is open.

## Parameters

| argument | where | status |
|---|---|---|
| `G` | the measured read, the tower, the statement | every group of the tree; the gap theorems at `SU(N)` |
| `βs` (couplings) | `MeasTowerG`, `schedAlongG`, the statement | existential, selected by the band |
| `c` (unit) | `BandG`, `MeasTowerG`, `MeasSweepG` | existential; read by no clause |
| `k` (step) | `BandG`, `MeasTowerG` | the construction's step |
| `a_k = dySpacingG G k` | everywhere | the construction's dyadic length; `aRunG G 1` a constant |
| `m′ = mUG G β` | `BandG`, `UnitLockG` | measured: `measMassOfG G (periodicStateG G β) (tensorEnergyG G)` |
| `R` | `AsymScalingG` | the limit of `m′/a_k` along the frozen tower |
| `B`, `β₀` | `MeasSweepG`, `measSweepG_of_continuous` | swept; existential start of the half-line |
| `c₀` | gap theorems | existential, `log 2 / C` from the seed's `C` |
| `S` | §5 of the code | any dyadic schedule of Wilson states |

DERIVED (module-wide): `2` the dyadic ratio, the least rank, the least side, the square; `3/2` the centre of the
band; `2/3` the unit at a scaling limit (`R` in `(2R/3, 4R/3)`); `1/2` the ratio of `dyadicTorusDecay`; `1` the
unit of the continuous sweep, the window and the top of the rate; `0` the plane, the limits and the signs; `4` the
dimension; `5` the least `n` of `SO(n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.MeasuredSpacing

open Filter Topology
open scoped ENNReal NNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG
  MassGap.FlowClusterG
open MassGap.ContinuumCluster (isIGaugeInvariant_prod isIGaugeInvariant_smear scaleSite_axisVec)
open MassGap.SubstrateFluxRead (SectorSeedMeasured)
open MassGap.SubstrateDecode (measMassOf tensorEnergy LockPersists)
open MassGap.PeriodicState (periodicState)
open MassGap.DLRLimit (State)
open MassGap.MeasuredTower

/-! ## 1. The measured read over `G` -/

/-- **The sup-norm of `MeasuredTower` is that of `StrongFiniteSize`.** DERIVED: no numeral. -/
theorem snormG_eq : snormG = StrongFiniteSize.snorm :=
  rfl

section MeasuredG

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A point capture reads spacing `0`** (its mass is `⊤`). DERIVED: `0` the value. -/
theorem measLenG_point (U : MassGap.GibbsSpec.IConf G) : measLenG G (SubstrateDecode.twoPhase U U) = 0 :=
  (measLenG_eq_zero_iff G _).mpr (Or.inr (measMassOfG_top_of_cov_zero G fun x z => by
    rw [SubstrateDecode.stateCov_twoPhase, sub_self, zero_mul, zero_div]))

/-- **Under the unit lock the measured spacing tends to `0`.** DERIVED: `0` the limit. -/
theorem tendsto_measSpacingG (h : UnitLockG G) : Tendsto (measSpacingG G) atTop (𝓝 0) := by
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.1
  rw [ENNReal.toReal_zero] at h1
  exact h1

/-- **Under the unit lock the measured spacing is eventually positive.** DERIVED: `0` the sign; `1` a finite
bound. -/
theorem eventually_measSpacingG_pos (h : UnitLockG G) : ∀ᶠ β in atTop, 0 < measSpacingG G β := by
  filter_upwards [h.2, h.1.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))] with β h0 h1
  exact ENNReal.toReal_pos h0.ne' (ne_top_of_lt h1)

end MeasuredG

section MeasuredSU

variable {N : ℕ}

/-- **The unit read of `SU(N)`** in the form of `SubstrateDecode`. DERIVED: no numeral. -/
def mU (hN : N ≠ 0) (β : ℝ) : ℝ≥0∞ := measMassOf (periodicState hN β) tensorEnergy

/-- **The measured spacing of `SU(N)`.** DERIVED: no numeral. -/
def measSpacing (hN : N ≠ 0) (β : ℝ) : ℝ := (mU hN β).toReal

variable [NeZero N]

/-- **At `SU(N)` the tensor reading of `G` is `SubstrateDecode.tensorEnergy`.** DERIVED: no numeral. -/
theorem tensorEnergyG_SU : tensorEnergyG (MassGap.SUN.SU N) = tensorEnergy := by
  funext x
  simp only [tensorEnergyG, SubstrateDecode.tensorEnergy, SymPlaqG.plaqFieldG_SU]

/-- **At `SU(N)` the unit read of `G` is that of `SubstrateDecode`.** DERIVED: no numeral. -/
theorem mUG_SU (β : ℝ) : mUG (MassGap.SUN.SU N) β = mU (NeZero.ne N) β := by
  unfold mUG mU
  rw [tensorEnergyG_SU]
  rfl

/-- **`LockPersists` gives the unit lock of `SU(N)`.** DERIVED: no numeral. -/
theorem unitLockG_of_lockPersists (h : LockPersists (NeZero.ne N)) : UnitLockG (MassGap.SUN.SU N) := by
  have e : mUG (MassGap.SUN.SU N) = mU (NeZero.ne N) := funext mUG_SU
  obtain ⟨_, -, ht, hev⟩ := h
  unfold UnitLockG
  rw [e]
  exact ⟨ht, hev.mono fun _ hβ => hβ.1⟩

end MeasuredSU

/-! ## 2. The measured tower -/

section Tower

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-! ### Existence -/

/-- **A continuous measured spacing sweeps every band at unit `1`**: under the unit lock, continuity of
`β ↦ measSpacingG G β` on a half-line gives `MeasSweepG` (intermediate values at `t = 3a_k/2`).
DERIVED: `3/2` the centre of the band; `1` the unit and a finite bound. -/
theorem measSweepG_of_continuous (hU : UnitLockG G) {β₀ : ℝ}
    (hc : ContinuousOn (measSpacingG G) (Set.Ici β₀)) : MeasSweepG G := by
  refine ⟨1, one_pos, fun B => ?_⟩
  have hlt : ∀ᶠ β in atTop, 0 < mUG G β ∧ mUG G β < 1 :=
    hU.2.and (hU.1.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞)))
  obtain ⟨β₁, hβ₁⟩ := eventually_atTop.mp hlt
  have hB'1 : β₁ ≤ max B (max β₀ β₁) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB'0 : β₀ ≤ max B (max β₀ β₁) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hx0 : 0 < measSpacingG G (max B (max β₀ β₁)) := by
    obtain ⟨h0, h1⟩ := hβ₁ _ hB'1
    exact ENNReal.toReal_pos h0.ne' (ne_top_of_lt h1)
  have hd : Tendsto (fun k => 3 / 2 * dySpacingG G k) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacingG G).const_mul (3 / 2)
  filter_upwards [hd.eventually (gt_mem_nhds hx0)] with k hk
  have ha := dySpacingG_pos G k
  have ht0 : 0 < 3 / 2 * dySpacingG G k := by positivity
  obtain ⟨β'', hβ''t, hβ''B⟩ :=
    (((tendsto_measSpacingG G hU).eventually (gt_mem_nhds ht0)).and
      (eventually_ge_atTop (max B (max β₀ β₁)))).exists
  have hcont : ContinuousOn (measSpacingG G) (Set.Icc (max B (max β₀ β₁)) β'') :=
    hc.mono fun x hx => le_trans hB'0 hx.1
  obtain ⟨β, hβI, hβeq⟩ := intermediate_value_Icc' hβ''B hcont ⟨hβ''t.le, hk.le⟩
  refine ⟨β, le_trans (le_max_left _ _) hβI.1, ?_⟩
  have hne : mUG G β ≠ ⊤ := ne_top_of_lt (hβ₁ β (le_trans hB'1 hβI.1)).2
  have hmU : mUG G β = ENNReal.ofReal (3 / 2 * dySpacingG G k) := by
    rw [← hβeq, measSpacingG, ENNReal.ofReal_toReal hne]
  unfold BandG
  rw [hmU]
  exact ⟨ENNReal.ofReal_le_ofReal (by linarith), ENNReal.ofReal_le_ofReal (by linarith)⟩

/-! ### Comparison with the frozen tower -/

/-- **Under asymptotic scaling the frozen tower is a measured tower**, at unit `2R/3`.
DERIVED: `2/3`, `4/3` a neighbourhood of `R` of ratio `2`. -/
theorem measTowerG_of_scaling {R : ℝ} (h : AsymScalingG G R) : MeasTowerG G (dyBetaG G) := by
  obtain ⟨hR, ht⟩ := h
  refine ⟨WindowG.tendsto_dyBetaG G, 2 * R / 3, by positivity, ?_⟩
  filter_upwards [ht.eventually (Ioo_mem_nhds (by linarith : 2 * R / 3 < R) (by linarith : R < 4 * R / 3))]
    with k hk
  have hd := dySpacingG_pos G k
  have h1 : 2 * R / 3 * dySpacingG G k < measSpacingG G (dyBetaG G k) := (lt_div_iff₀ hd).mp hk.1
  have h2 : measSpacingG G (dyBetaG G k) < 4 * R / 3 * dySpacingG G k := (div_lt_iff₀ hd).mp hk.2
  have hx : 0 < measSpacingG G (dyBetaG G k) := lt_trans (by positivity) h1
  have hne : mUG G (dyBetaG G k) ≠ ⊤ := by
    intro htop
    rw [measSpacingG, htop, ENNReal.toReal_top] at hx
    exact lt_irrefl 0 hx
  have heq : mUG G (dyBetaG G k) = ENNReal.ofReal (measSpacingG G (dyBetaG G k)) :=
    (ENNReal.ofReal_toReal hne).symm
  unfold BandG
  rw [heq]
  exact ⟨ENNReal.ofReal_le_ofReal h1.le, ENNReal.ofReal_le_ofReal (by linarith)⟩

end Tower

section TowerSU

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **At `SU(N)` asymptotic scaling gives the unit tie of `MeasuredSeed` along the construction.**
DERIVED: no numeral. -/
theorem unitTracksAlong_dy_of_scaling {R : ℝ} (h : AsymScalingG (MassGap.SUN.SU N) R) :
    MeasuredSeed.UnitTracksAlong (NeZero.ne N) (MeasuredSeed.dyFilter (NeZero.ne N)) := by
  obtain ⟨c, hc, hb⟩ := (measTowerG_of_scaling _ h).2
  refine (MeasuredSeed.unitTracksAlong_dy_iff (NeZero.ne N)).mpr ⟨c, hc, ?_⟩
  filter_upwards [hb] with k hk
  have h1 := hk.1
  rw [dySpacingG_SU N, dyBetaG_SU N k, mUG_SU] at h1
  exact h1

end TowerSU

/-! ## 3. The schedule along a tower

`SchedOS`, `SchedShiftInv`, `SchedAxisInv` and `SchedTransInv` of `schedAlongG G βs` at every `βs` are in
`SchedAlong` (`schedOS_alongG`, `schedShiftInv_alongG`, `schedAxisInv_alongG`, `schedTransInv_alongG`, in this
namespace). -/

/-! ## 4. The per-step gap in measured units, at `SU(N)` -/

section Gap

variable {N : ℕ} [NeZero N]

/-- **The measured seed gives a lattice gap in measured units**: some `c > 0` has, at every large `β`, a rate
`r ∈ (0, 1)` with `GapAt` and `PeriodicClayGapAt` and `c · measSpacing ≤ −log r`. DERIVED: `2` the least rank,
the least side and the base; `0` the plane, the time axis and the signs; `1/2` the ratio of `dyadicTorusDecay`. -/
theorem gapAt_unit_of_sectorSeed (hN2 : 2 ≤ N) (hN : N ≠ 0) (hS : SectorSeedMeasured hN) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TransferGap.GapAt (PeriodicState.periodicGaugeInvData 0 0 hN β) r ∧
      PeriodicContent.PeriodicClayGapAt 0 0 hN β r ∧
      c * measSpacing hN β ≤ -Real.log r := by
  obtain ⟨C, hC, hev⟩ := hS
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨Real.log 2 / C, div_pos hl2 hC, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β hβS hβ
  obtain ⟨hpos, n, ⟨b, hb⟩, hn2, hnm, hsec⟩ := hβS
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [hb] at hn2
    norm_num at hn2
  have he : Even n := by rw [hb]; exact Nat.even_pow.mpr ⟨even_two, hb0⟩
  have hd := CentreSectorSeedN.defectW_le_of_sectorsN hβ.le hn2 he hsec
  have hm : n ≠ 0 := by omega
  have hdec := DoublingClay2.dyadicTorusDecay hN β hβ.le n ⟨b, hb⟩ hn2 hd
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hq1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hlag := WeakCouplingWindow.torusLagClear_stepRate 0 0 hN β hq0.le hm hdec
  have hr0 := WeakCouplingWindow.stepRate_pos hq0 n
  have hr1 := WeakCouplingWindow.stepRate_lt_one hq0.le hq1 hm
  have hg := (WeakCouplingWindow.torusLagClear_iff_gapAt 0 0 hN hβ.le hm hr0.le).mp hlag
  refine ⟨_, hr0, hr1, hg, GapStep.periodic_clayGapAt_of_gapAt 0 0 hN2 hN hβ.le hr0 hr1 hg, ?_⟩
  have hnm' : (n : ℝ≥0∞) * mU hN β ≤ ENNReal.ofReal C := hnm
  have hpos' : 0 < mU hN β := hpos
  have hne : mU hN β ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by exact_mod_cast hm)] at hnm'
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hnm')
  have ha : 0 < measSpacing hN β := ENNReal.toReal_pos hpos'.ne' hne
  have hwin : (n : ℝ) * measSpacing hN β ≤ C := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnm'
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hC.le] at h1
  have hphys := WeakCouplingWindow.physical_rate_ge hq0 hq1 hm ha hC hwin
  have hlog : -Real.log (1 / 2 : ℝ) = Real.log 2 := by rw [one_div, Real.log_inv, neg_neg]
  rw [hlog, div_le_div_iff₀ hC ha] at hphys
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  exact hphys

variable [Fact (2 ≤ N)]

/-- **Along a measured tower the per-step gap is at least a fixed multiple of the step's spacing**: the band's
lower edge replaces `UnitTracksRun`. DERIVED: `0` the plane and the signs; `1` the top of the rate. -/
theorem gapAlong_of_sectorSeed (hS : SectorSeedMeasured (NeZero.ne N)) {βs : ℕ → ℝ}
    (hT : MeasTowerG (MassGap.SUN.SU N) βs) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r
      ∧ c ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k := by
  obtain ⟨c₀, hc₀, hev⟩ := gapAt_unit_of_sectorSeed (Fact.out : 2 ≤ N) (NeZero.ne N) hS
  obtain ⟨c, hc, hband⟩ := hT.2
  refine ⟨c₀ * c, mul_pos hc₀ hc, ?_⟩
  filter_upwards [hT.1.eventually hev, hband] with k ⟨r, hr0, hr1, hg, _, hrate⟩ hb
  have ha := dySpacingG_pos (MassGap.SUN.SU N) k
  have hsp := (hb.spacing hc).1
  have e : measSpacingG (MassGap.SUN.SU N) (βs k) = measSpacing (NeZero.ne N) (βs k) := by
    unfold measSpacingG measSpacing
    rw [mUG_SU]
  rw [e] at hsp
  refine ⟨r, hr0, hr1, hg, ?_⟩
  rw [le_div_iff₀ ha, mul_assoc]
  exact le_trans (mul_le_mul_of_nonneg_left hsp hc₀.le) hrate

/-- **The three measured reads give the per-step gap along a measured tower**, without `UnitTracksRun`.
DERIVED: no numeral. -/
theorem gapAlong_of_reads (hF : RelayChain.CoarseReadsFine N (NeZero.ne N))
    (hL : GapFromReads.LongChainRead N (NeZero.ne N)) (hZ : ZeroFluxGap.ZeroFluxReadsMass N (NeZero.ne N))
    {βs : ℕ → ℝ} (hT : MeasTowerG (MassGap.SUN.SU N) βs) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r
      ∧ c ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k :=
  gapAlong_of_sectorSeed (GapFromReads.sectorSeedMeasured_of_reads (NeZero.ne N) hF hL hZ) hT

end Gap

/-! ## 5. The flowed clustering and the observer's gap at a schedule -/

section ClusterG

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- DERIVED: no numeral. -/
theorem gaugeInvDataG_T_pow (β : ℝ) (τ : Fin 4) (n : ℕ)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0)) :
    (((((periodicGaugeInvDataG G τ 0 β).T ^ n) x
        : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0))) : C(MassGap.GibbsSpec.IConf G, ℝ))
      = (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[n] (x : C(MassGap.GibbsSpec.IConf G, ℝ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

/-- The product of the smears of the flowed empty monomial is `1`. DERIVED: `1` the value. -/
theorem prodSmearG_empty (Φ : GFlow G) (a : ℝ) (k : ℕ) :
    prodSmearG a (Φ.mono k (emptyMonoG G)) = 1 := by
  unfold prodSmearG
  exact Fintype.prod_empty _

/-- Translating a flowed smeared product by a lattice vector translates every test function.
DERIVED: no numeral. -/
theorem transObs_prodSmearG' (Φ : GFlow G) {a : ℝ} (ha : 0 < a) (k : ℕ) (n : ISite) (Q : MonoG G) :
    transObs n (prodSmearG a (Φ.mono k Q)) = prodSmearG a (Φ.mono k (monoShiftG (site a n) Q)) := by
  unfold prodSmearG
  rw [transObs_prod]
  exact Finset.prod_congr rfl (fun i _ => (smear_translate ha _ _ n).symm)

/-- A flowed monomial whose smeared factors at `S.a k` lie in the half-space algebra is gauge-invariant there.
DERIVED: `0` the plane. -/
theorem prodSmearG_mem_sched (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P : MonoG G)
    (hk : ∀ i : Fin P.1, smear (S.a k) (Φ.map k (P.2 i).1).1 (P.2 i).2
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    prodSmearG (S.a k) (Φ.mono k P) ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0 := by
  have h1 : prodSmearG (S.a k) (Φ.mono k P) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 :=
    HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _ (fun i _ => hk i)
  have h2 : GaugeInvariantAlgebra.IsIGaugeInvariant (prodSmearG (S.a k) (Φ.mono k P)) :=
    isIGaugeInvariant_prod Finset.univ _ (fun i _ => isIGaugeInvariant_smear (S.a_pos k) _ _)
  exact Submodule.mem_inf.mpr ⟨h1, h2⟩

/-- A dyadic vector of step `m` is a lattice vector of every later step. DERIVED: `2` the halving. -/
theorem site_sched {S : Sched G} (hd : SchedDyadic S) {m k : ℕ} (hmk : m ≤ k) (v : ISite) :
    site (S.a m) v = site (S.a k) (scaleSite (2 ^ (k - m)) v) := by
  funext i
  simp only [site, scaleSite]
  push_cast
  rw [← hd m k hmk]
  ring

/-- **Clustering at step `k` of a schedule whose state is the Wilson state at `βs k`.** DERIVED: `2` the square;
`0` the plane. -/
theorem lattice_clusterSched (S : Sched G) (βs : ℕ → ℝ)
    (hν : ∀ k, S.ν k = GaugeWilson.periodicStateG G (βs k)) (Φ : GFlow G) (τ : Fin 4) (k : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hg : TransferGap.GapAt (periodicGaugeInvDataG G τ 0 (βs k)) r) (P Q : MonoG G)
    (hP : prodSmearG (S.a k) (Φ.mono k P) ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0)
    (hQ : prodSmearG (S.a k) (Φ.mono k Q) ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0)
    (n : ℕ) :
    (latSFG S Φ.map k (pairFamG τ P (monoShiftG (site (S.a k) (axisVec τ n)) Q))
        - latSFG S Φ.map k (pairFamG τ P (emptyMonoG G))
          * latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q)) ^ 2
      ≤ r ^ (2 * n) * (latSFG S Φ.map k (pairFamG τ P P)
          * (latSFG S Φ.map k (pairFamG τ Q Q) - latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q) ^ 2))
    ∧ 0 ≤ latSFG S Φ.map k (pairFamG τ P P)
          * (latSFG S Φ.map k (pairFamG τ Q Q) - latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q) ^ 2) := by
  have ha := S.a_pos k
  have hS : ∀ X Y : MonoG G, latSFG S Φ.map k (pairFamG τ X Y)
      = GaugeWilson.periodicStateG G (βs k)
          (LatticeReflection.ireflObs τ 0 (prodSmearG (S.a k) (Φ.mono k X))
            * prodSmearG (S.a k) (Φ.mono k Y)) := by
    intro X Y
    rw [latSFG_pairFamG, latSG_pairFamG, hν k]
  set D := periodicGaugeInvDataG G τ 0 (βs k) with hD
  set y : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0) := ⟨_, hP⟩ with hy
  set x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0) := ⟨_, hQ⟩ with hx
  have h := TransferGap.clustering_sq D hr hg n x y
  have hY := mul_nonneg (D.form_nonneg y) (D.form_nonneg (TransferGap.vacProj D x))
  have e1 : D.form y ((D.T ^ n) x)
      = latSFG S Φ.map k (pairFamG τ P (monoShiftG (site (S.a k) (axisVec τ n)) Q)) := by
    rw [hS, ← transObs_prodSmearG' Φ ha k _ Q]
    show GaugeWilson.periodicStateG G (βs k)
        (LatticeReflection.ireflObs τ (2 * 0) (y : C(MassGap.GibbsSpec.IConf G, ℝ))
          * ((((D.T ^ n) x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0))
            : C(MassGap.GibbsSpec.IConf G, ℝ)))) = _
    rw [hD, gaugeInvDataG_T_pow, ContinuumCluster.ishiftObsL_iterate]
    rfl
  have e2 : D.form y D.vac = latSFG S Φ.map k (pairFamG τ P (emptyMonoG G)) := by
    rw [hS, prodSmearG_empty, mul_one]
    show GaugeWilson.periodicStateG G (βs k)
        (LatticeReflection.ireflObs τ (2 * 0) (y : C(MassGap.GibbsSpec.IConf G, ℝ)) * 1) = _
    rw [mul_one]
    rfl
  have e3 : D.form D.vac x = latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q) := by
    rw [hS, prodSmearG_empty]
    rfl
  have e4 : D.form y y = latSFG S Φ.map k (pairFamG τ P P) := by
    rw [hS]
    rfl
  have e4' : D.form x x = latSFG S Φ.map k (pairFamG τ Q Q) := by
    rw [hS]
    rfl
  have e5 : D.form (TransferGap.vacProj D x) (TransferGap.vacProj D x)
      = latSFG S Φ.map k (pairFamG τ Q Q) - latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q) ^ 2 := by
    rw [ContinuumCluster.form_vacProj, D.toPreForm.form_symm _ D.vac, e3, e4']
  rw [e1, e2, e3, e4, e5] at h
  rw [e4, e5] at hY
  exact ⟨h, hY⟩

/-- **The flowed limit clusters at the rate of the per-step gap**, over a dyadic schedule whose states are Wilson
states: if eventually in `k` the transfer of `βs k` has a rate `r` with `c ≤ −log r / S.a k`, the flowed kernel
clusters at rate `c` in physical separation at every step. DERIVED: `2` the square and the halving; `0` the
plane. -/
theorem kernFG_cluster_of_stepGap (S : Sched G) (hd : SchedDyadic S) (βs : ℕ → ℝ)
    (hν : ∀ k, S.ν k = GaugeWilson.periodicStateG G (βs k)) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) {c : ℝ}
    (hgap : ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ TransferGap.GapAt (periodicGaugeInvDataG G τ 0 (βs k)) r
      ∧ c ≤ -Real.log r / S.a k) :
    ∀ (P Q : MarginMonoG G τ r) (m n : ℕ),
      (kernFG S Φ τ P.1 (monoShiftG (timeVecG S m τ n) Q.1)
          - kernFG S Φ τ P.1 (emptyMonoG G) * kernFG S Φ τ (emptyMonoG G) Q.1) ^ 2
        ≤ Real.exp (-(2 * c) * (S.a m * n))
          * (kernFG S Φ τ P.1 P.1 * (kernFG S Φ τ Q.1 Q.1 - kernFG S Φ τ (emptyMonoG G) Q.1 ^ 2))
      ∧ 0 ≤ kernFG S Φ τ P.1 P.1 * (kernFG S Φ τ Q.1 Q.1 - kernFG S Φ τ (emptyMonoG G) Q.1 ^ 2) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro P Q m n
  have hmem : ∀ X : MarginMonoG G τ r, ∀ᶠ k in atTop, ∀ i : Fin X.1.1,
      smear (S.a k) (Φ.map k (X.1.2 i).1).1 (X.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
    intro X
    obtain ⟨d, hd', hrd, hX⟩ := X.2
    exact Filter.eventually_all.mpr
      (fun i => hpos (X.1.2 i).1 (X.1.2 i).2 d hd' hrd (fun y hy => hX i y hy))
  have tl : ∀ X Y : MonoG G, Tendsto (fun k => latSFG S Φ.map k (pairFamG τ X Y))
      (ultra : Filter ℕ) (𝓝 (kernFG S Φ τ X Y)) :=
    fun X Y => tendsto_contSFG S Φ.map hB (pairFamG τ X Y)
  have hf := ((tl P.1 (monoShiftG (timeVecG S m τ n) Q.1)).sub
    ((tl P.1 (emptyMonoG G)).mul (tl (emptyMonoG G) Q.1))).pow 2
  have hY := (tl P.1 P.1).mul ((tl Q.1 Q.1).sub ((tl (emptyMonoG G) Q.1).pow 2))
  have hg := hY.const_mul (Real.exp (-(2 * c) * (S.a m * n)))
  have hevLE : ∀ᶠ k in atTop,
      (latSFG S Φ.map k (pairFamG τ P.1 (monoShiftG (timeVecG S m τ n) Q.1))
        - latSFG S Φ.map k (pairFamG τ P.1 (emptyMonoG G))
          * latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q.1)) ^ 2
      ≤ Real.exp (-(2 * c) * (S.a m * n))
        * (latSFG S Φ.map k (pairFamG τ P.1 P.1)
          * (latSFG S Φ.map k (pairFamG τ Q.1 Q.1)
            - latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q.1) ^ 2))
      ∧ 0 ≤ latSFG S Φ.map k (pairFamG τ P.1 P.1)
          * (latSFG S Φ.map k (pairFamG τ Q.1 Q.1)
            - latSFG S Φ.map k (pairFamG τ (emptyMonoG G) Q.1) ^ 2) := by
    filter_upwards [Filter.eventually_ge_atTop m, hgap, hmem P, hmem Q] with k hk hkr hkP hkQ
    obtain ⟨r', hr0, hg', hrate⟩ := hkr
    have ha := S.a_pos k
    have hvec : timeVecG S m τ n = site (S.a k) (axisVec τ ((2 ^ (k - m) * n : ℕ) : ℤ)) := by
      show site (S.a m) (axisVec τ n) = _
      rw [site_sched hd hk, scaleSite_axisVec]
      congr 2
    obtain ⟨hcl, hY0⟩ := lattice_clusterSched S βs hν Φ τ k hr0.le hg' P.1 Q.1
      (prodSmearG_mem_sched S Φ τ k _ hkP) (prodSmearG_mem_sched S Φ τ k _ hkQ) (2 ^ (k - m) * n)
    rw [← hvec] at hcl
    refine ⟨hcl.trans (mul_le_mul_of_nonneg_right ?_ hY0), hY0⟩
    have hlog : Real.log r' ≤ -c * S.a k := by
      have h1 := hrate
      rw [le_div_iff₀ ha] at h1
      linarith
    have hr_le : r' ≤ Real.exp (-c * S.a k) := by
      rw [← Real.exp_log hr0]
      exact Real.exp_le_exp.mpr hlog
    calc r' ^ (2 * (2 ^ (k - m) * n))
        ≤ Real.exp (-c * S.a k) ^ (2 * (2 ^ (k - m) * n)) :=
          pow_le_pow_left₀ hr0.le hr_le _
      _ = Real.exp (((2 * (2 ^ (k - m) * n) : ℕ) : ℝ) * (-c * S.a k)) :=
          (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(2 * c) * (S.a m * n)) := by
          rw [← hd m k hk]
          push_cast
          congr 1
          ring
  have hev1 := hevLE.mono (fun k hk => hk.1)
  have hev2 := hevLE.mono (fun k hk => hk.2)
  exact ⟨le_of_tendsto_of_tendsto hf hg (hev1.filter_mono ultra_le),
    ge_of_tendsto hY (hev2.filter_mono ultra_le)⟩

/-- **The absolute clustering at window `1`** from the per-step gap. DERIVED: `1` the window; `2` the square. -/
theorem flowClusterAbs_of_stepGap (S : Sched G) (hd : SchedDyadic S) (βs : ℕ → ℝ)
    (hν : ∀ k, S.ν k = GaugeWilson.periodicStateG G (βs k)) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) {c : ℝ}
    (hc : 0 < c)
    (hgap : ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ TransferGap.GapAt (periodicGaugeInvDataG G τ 0 (βs k)) r
      ∧ c ≤ -Real.log r / S.a k) :
    FlowClusterAbsG S Φ τ r 1 := by
  have hcl := kernFG_cluster_of_stepGap S hd βs hν Φ hB τ hpos hgap
  refine ⟨c, hc, fun m P Q => ⟨Real.sqrt (kernFG S Φ τ P.1 P.1
    * (kernFG S Φ τ Q.1 Q.1 - kernFG S Φ τ (emptyMonoG G) Q.1 ^ 2)), fun n => ?_⟩⟩
  rw [div_one]
  have hE : (0 : ℝ) ≤ Real.exp (-c * (S.a m * n)) := (Real.exp_pos _).le
  have hsq : Real.exp (-c * (S.a m * n)) ^ 2 = Real.exp (-(2 * c) * (S.a m * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 := (hcl P Q m n).1
  rw [← hsq] at h1
  have h2 := ContinuumSep.abs_le_mul_sqrt_of_sq_le_sep hE h1
  linarith [h2, mul_comm (Real.exp (-c * (S.a m * n)))
    (Real.sqrt (kernFG S Φ τ P.1 P.1 * (kernFG S Φ τ Q.1 Q.1 - kernFG S Φ τ (emptyMonoG G) Q.1 ^ 2)))]

/-- **The observer's transfer is gapped at every step from the per-step gap**, over a schedule with the four
schedule properties whose states are Wilson states. DERIVED: `0` the plane; `1` the window and the top of the
rate. -/
theorem flowGapAt_of_stepGap (S : Sched G) (hS : SchedOS S) (βs : ℕ → ℝ)
    (hν : ∀ k, S.ν k = GaugeWilson.periodicStateG G (βs k)) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) {r : ℝ} (hphys : Φ.PhysRange S r) (m0 : ℕ) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ TransferGap.GapAt (periodicGaugeInvDataG G 0 0 (βs k)) r
      ∧ c ≤ -Real.log r / S.a k) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (transferNG S hS Φ hB 0 hphys m0) ρ := by
  have hpos := posPreserving_of_physRangeG S Φ hphys 0
  exact (flowClusterAbs_iff_gapAtG S hS Φ hB 0 hpos m0 one_pos).mp
    (flowClusterAbs_of_stepGap S hS.dyadic βs hν Φ hB 0 hpos hc hgap)

end ClusterG

/-! ## 6. The gap consequence at `SU(N)` -/

section GapSU

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The measured seed and a measured tower give the observer's gap at the tower's schedule**, without
`UnitTracksRun`. DERIVED: `0` the plane. -/
theorem observerGap_of_sectorSeed (hS : SectorSeedMeasured (NeZero.ne N)) {βs : ℕ → ℝ}
    (hT : MeasTowerG (MassGap.SUN.SU N) βs) (Φ : GFlow (MassGap.SUN.SU N))
    (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ} (hphys : Φ.PhysRange (schedAlongG _ βs) r)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (transferNG (schedAlongG _ βs) (schedOS_alongG _ βs) Φ hB 0 hphys m0) ρ := by
  obtain ⟨c, hc, hev⟩ := gapAlong_of_sectorSeed hS hT
  refine flowGapAt_of_stepGap (schedAlongG _ βs) (schedOS_alongG _ βs) βs (fun _ => rfl) Φ hB hphys m0 hc ?_
  filter_upwards [hev] with k ⟨r, hr0, _, hg, hrate⟩
  exact ⟨r, hr0, hg, hrate⟩

/-- **The three measured reads and a measured tower give the observer's gap at the tower's schedule.**
DERIVED: `0` the plane. -/
theorem observerGap_of_reads (hF : RelayChain.CoarseReadsFine N (NeZero.ne N))
    (hL : GapFromReads.LongChainRead N (NeZero.ne N)) (hZ : ZeroFluxGap.ZeroFluxReadsMass N (NeZero.ne N))
    {βs : ℕ → ℝ} (hT : MeasTowerG (MassGap.SUN.SU N) βs) (Φ : GFlow (MassGap.SUN.SU N))
    (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ} (hphys : Φ.PhysRange (schedAlongG _ βs) r)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (transferNG (schedAlongG _ βs) (schedOS_alongG _ βs) Φ hB 0 hphys m0) ρ :=
  observerGap_of_sectorSeed (GapFromReads.sectorSeedMeasured_of_reads (NeZero.ne N) hF hL hZ) hT Φ hB hphys m0

end GapSU

/-! ## 7. The two statements -/

section Statement

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]
  [GaugeLie G]

/-- **Under asymptotic scaling the statement at the frozen tower gives the statement at a measured tower.**
DERIVED: no numeral. -/
theorem clayStatementMeasOf_of_atG {R : ℝ} (hs : AsymScalingG G R) (W : ConfFlowG G) (D : Set (LField G))
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) (h : ClayStatementG.ClayStatementAtG G W D) :
    ClayStatementG.ClayStatementOf G :=
  ⟨dyBetaG G, measTowerG_of_scaling G hs, W, D, hD, h⟩

/-- DERIVED: no numeral. -/
theorem clayStatementMeasOf_of_of {R : ℝ} (hs : AsymScalingG G R) (h : ClayStatementG.ClayStatementOfDy G) :
    ClayStatementG.ClayStatementOf G := by
  obtain ⟨W, D, hD, hW⟩ := h
  exact clayStatementMeasOf_of_atG hs W D hD hW

end Statement

/-- **`ClayStatementAt` is the parametric statement at the frozen tower.** DERIVED: `2` the least colour count;
`4` the dimension. -/
theorem clayStatementAt_iff_frozenTower {N : ℕ} [NeZero N] [Fact (2 ≤ N)] (hN2 : 2 ≤ N) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) :
    ClayStatementG.ClayStatementAtP (schedAlongG _ (dyBetaG (MassGap.SUN.SU N)))
        (ClayStatementG.constsG (MassGap.SUN.SU N)) W.toG D
      ↔ ClayStatement.ClayStatementAt hN2 W D hD :=
  ClayStatementG.clayStatementAtG_SU_iff hN2 W D hD

/-- **Asymptotic scaling at every `SU(N)`.** DERIVED: `2` the least colour count; `0` the excluded one. -/
def ScalingSU : Prop :=
  ∀ (N : ℕ) (hN2 : 2 ≤ N),
    haveI : NeZero N := ⟨by omega⟩
    haveI : Fact (2 ≤ N) := ⟨hN2⟩
    ∃ R : ℝ, AsymScalingG (MassGap.SUN.SU N) R

/-- **Frozen ⇒ root, under asymptotic scaling.** The converse is not proved. DERIVED: `2` the least colour
count. -/
theorem clayStatementMeas_of_dy (h : MassGap.ClayStatementDy) (hs : ScalingSU) : MassGap.ClayStatement := by
  intro N hN2
  have h1 : ClayStatementG.ClayStatementSUDy N hN2 := (ClayStatementG.clayStatementDy_iff_SU.mp h) N hN2
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (2 ≤ N) := ⟨hN2⟩
  obtain ⟨R, hR⟩ := hs N hN2
  exact clayStatementMeasOf_of_of hR h1

/-- **Frozen ⇒ root over the instantiated groups, under asymptotic scaling at each.** DERIVED: `5`, `3`, `0`
the ranges of the families. -/
theorem clayStatementMeasClassical_of_frozen (h : ClayStatementG.ClayStatementClassicalDy) (hsSU : ScalingSU)
    (hsSO : ∀ (n : ℕ) (h5 : 5 ≤ n),
      haveI : NeZero n := ⟨by omega⟩
      haveI : Fact (5 ≤ n) := ⟨h5⟩
      ∃ R : ℝ, AsymScalingG (MassGap.GaugeInstances.SO n) R)
    (hs3 : ∃ R : ℝ, AsymScalingG (MassGap.GaugeInstances.SO 3) R)
    (hsSp : ∀ (n : ℕ) (hn : n ≠ 0),
      haveI : NeZero n := ⟨hn⟩
      ∃ R : ℝ, AsymScalingG (MassGap.GaugeInstances.USp n) R) :
    ClayStatementG.ClayStatementClassical := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun N hN2 => ?_, fun n h5 => ?_, ?_, fun n hn => ?_⟩
  · haveI : NeZero N := ⟨by omega⟩
    haveI : Fact (2 ≤ N) := ⟨hN2⟩
    obtain ⟨R, hR⟩ := hsSU N hN2
    exact clayStatementMeasOf_of_of hR (h1 N hN2)
  · haveI : NeZero n := ⟨by omega⟩
    haveI : Fact (5 ≤ n) := ⟨h5⟩
    obtain ⟨R, hR⟩ := hsSO n h5
    exact clayStatementMeasOf_of_of hR (h2 n h5)
  · obtain ⟨R, hR⟩ := hs3
    exact clayStatementMeasOf_of_of hR h3
  · haveI : NeZero n := ⟨hn⟩
    obtain ⟨R, hR⟩ := hsSp n hn
    exact clayStatementMeasOf_of_of hR (h4 n hn)

end MassGap.MeasuredSpacing

end

#print axioms MassGap.MeasuredSpacing.snormG_eq
#print axioms MassGap.MeasuredSpacing.measLenG_point
#print axioms MassGap.MeasuredSpacing.tendsto_measSpacingG
#print axioms MassGap.MeasuredSpacing.eventually_measSpacingG_pos
#print axioms MassGap.MeasuredSpacing.tensorEnergyG_SU
#print axioms MassGap.MeasuredSpacing.mUG_SU
#print axioms MassGap.MeasuredSpacing.unitLockG_of_lockPersists
#print axioms MassGap.MeasuredSpacing.measSweepG_of_continuous
#print axioms MassGap.MeasuredSpacing.measTowerG_of_scaling
#print axioms MassGap.MeasuredSpacing.unitTracksAlong_dy_of_scaling
#print axioms MassGap.MeasuredSpacing.gapAt_unit_of_sectorSeed
#print axioms MassGap.MeasuredSpacing.gapAlong_of_sectorSeed
#print axioms MassGap.MeasuredSpacing.gapAlong_of_reads
#print axioms MassGap.MeasuredSpacing.lattice_clusterSched
#print axioms MassGap.MeasuredSpacing.kernFG_cluster_of_stepGap
#print axioms MassGap.MeasuredSpacing.flowClusterAbs_of_stepGap
#print axioms MassGap.MeasuredSpacing.flowGapAt_of_stepGap
#print axioms MassGap.MeasuredSpacing.observerGap_of_sectorSeed
#print axioms MassGap.MeasuredSpacing.observerGap_of_reads
#print axioms MassGap.MeasuredSpacing.clayStatementMeasOf_of_atG
#print axioms MassGap.MeasuredSpacing.clayStatementMeasOf_of_of
#print axioms MassGap.MeasuredSpacing.clayStatementAt_iff_frozenTower
#print axioms MassGap.MeasuredSpacing.clayStatementMeas_of_dy
#print axioms MassGap.MeasuredSpacing.clayStatementMeasClassical_of_frozen
