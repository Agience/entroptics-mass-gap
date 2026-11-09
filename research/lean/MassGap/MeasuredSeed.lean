import Mathlib
import MassGap.GapFromReads
import MassGap.ContinuumSchwinger

/-!
# MassGap.MeasuredSeed — why the unit tie of the run seed stays, and the weakest form of it

`GapFromReads.runSeed_of_reads` reaches `WDeltaRun.RunSeed N` from the measured seed
`SubstrateFluxRead.SectorSeedMeasured` and one more input, `SubstrateDecode.UnitTracksRun`: the measured mass
`m′ = measMassOf (periodicState hN β) tensorEnergy` is at least `c₁ · aRun N β`, eventually in `β`. This module
traces what the consumer of `RunSeed` reads, argues from the construction's spacing that the unit tie cannot be
removed from that consumer, proves that given the measured seed and a seed floor `RunSeed` is equivalent to it, and
states it along the construction's couplings. Declarations are in the namespace `MassGap.MeasuredSeed`.

## What the consumer of `RunSeed` reads

The path from `RunSeed N` to `ClayStatement` (file:line in `research/lean/MassGap`):

* `InputMerge.lean:441`: `clayInputsN_of_narrowAtMin` puts the last clause of `NarrowInputsAtMin` into the field
  `far` of `SUNBest.InputsAt`.
* `SUNBest.lean:136`: `clayStatementAt_N_best` passes `I.far` to `CompositesRenAll.clayStatementAt_SU_ren_low`,
  which passes it (`CompositesRenAll.lean:243`) to `ClaySUFinal.clayStatementAt_SU_final`.
* `ClaySUFinal.lean:139`: the only use, `LocalLink.observerGapAt_of_runSeed` (`LocalLink.lean:106`), which gives
  `∃ ρ, 0 < ρ ∧ ρ < 1 ∧ GapAt (transferN hN Φ hB 0 hphys 0) ρ`: the Hamiltonian gap of the observer's flowed
  transfer at the step `0`.
* `LocalLink.lean:92`: `observerGap_of_runSeed` goes `RunSeed → WDelta2` (`WDeltaRun.wDelta2_of_runSeed`)
  `→ FixedWindowDecay 0 0 hN (5C)` (`DoublingClay2.fixedWindowDecay_of_WDelta2`) `→` the flowed gap at rate
  `e^{−(c/5C) · dySpacing N m}` (`FlowCapstone.flow_continuum_gap`).
* `FlowCapstone.lean:625`: `flow_continuum_gap` calls `kernF_cluster_of_fixedWindowDecay`, which at `:328–332`
  reads that bound only along the couplings `dyBeta k` (`(tendsto_dyBeta hN1).eventually hev`), and at `:404` only
  at the steps of `ultra` (`hevLE.filter_mono ultra_le`, `ultra = Ultrafilter.of atTop`), where
  `aRun N (dyBeta k) = dySpacing N k` (`ContinuumSchwinger.aRun_dyBeta`).
* `WeakCouplingWindow.lean:345`, called from `FlowCapstone.lean:328`: `gapAt_physical_of_fixedWindowDecay` turns
  the window into a lattice gap `r` with `c/L ≤ −log r / aRun N β`, eventually in `β`: a gap in lattice units at
  least `(c/L) · aRun N β`.

So the consumer needs a gap per lattice step at least a fixed multiple of the spacing `aRun`, along the couplings
`dyBeta k`, at the steps `k` of `ultra`. The spacing is not a choice of `RunSeed`: `ClayStatement` builds its lattice at step `k` at coupling
`dyBeta k` and spacing `dySpacing N k = aRun N (dyBeta k)` (`ClayStatement.lean:16`), and every physical length of
the statement is a lattice length times that spacing. A gap read in the measured unit `m′` is a physical gap only
through `m′ / aRun`. This is case (b): the unit tie belongs to the target, not to the seed.

## The main theorems (proved)

* `unitTracksAlong_of_window` (the unit tie is forced by the window): if, eventually along a filter `F`, some side
  `n ≥ 2` has `D ≤ n m′` and `n · aRun ≤ C` (`D, C > 0`), then `UnitTracksAlong hN F` with `c₁ = D/C`.
* `unitTracksAlong_of_runSeedAlong`: `RunSeedAlong N F → SeedFloorAlong hN F → UnitTracksAlong hN F`.
* `runSeedAlong_of_sectorSeed`: for `F ≤ atTop`, `SectorSeedMeasured hN → UnitTracksAlong hN F → RunSeedAlong N F`.
* `runSeedAlong_iff_unitTracksAlong`: for `F ≤ atTop`, given `SectorSeedMeasured hN` and
  `SeedFloorAlong hN F`, `RunSeedAlong N F ↔ UnitTracksAlong hN F`.
* `runSeed_iff_unitTracksRun`: the case `F = atTop`: given the measured seed and the floor,
  `WDeltaRun.RunSeed N ↔ UnitTracksRun hN`. Under the floor, the unit tie is exactly what `RunSeed` asks beyond the
  measured seed: a proof of `RunSeed` together with the floor proves it. Without the floor the theorem says nothing
  (test 4 of the floor).
* `unitTracksAlong_dy_iff`, `runSeedAlong_dy_iff`: along the construction's couplings `dyFilter hN = map dyBeta atTop`
  the two Props read `∀ᶠ k, ofReal (c₁ · dySpacing N k) ≤ m′(dyBeta k)` and
  `∀ᶠ k, ∃ n, IsPow2 n ∧ 2 ≤ n ∧ n · dySpacing N k ≤ C ∧ defectW N (dyBeta k) n ≤ 1/1000`.
* `unitTracksAlong_dy_of_run`: `UnitTracksRun hN → UnitTracksAlong hN (dyFilter hN)`; the converse is not proved.
* `runSeedAlong_dy_of_reads`: the three measured reads of `GapFromReads` and `UnitTracksAlong hN (dyFilter hN)` give
  `RunSeedAlong N (dyFilter hN)`.
* `tracksAlong_of_ratio`, `unitTracksAlong_of_ratio` (case (c)): a measured ratio `ofReal c · m″ ≤ m′` and the unit
  tie of `m″` give the unit tie of `m′`. A second measured mass moves the tie to itself; it does not remove it.

## The weakest form of the unit input

* Direction. Only the lower bound `m′ ≥ c₁ · aRun` is used (`unitTracksAlong_of_window` and its converse
  `runSeedAlong_of_sectorSeed`). `UnitTracksRun` is already one-sided; an upper bound on `m′ / aRun` is not read.
* Couplings. The consumer reads the gap along `dyBeta k` only (`FlowCapstone.lean:328–332`). The consumer reads the
  unit input along `dyBeta k` at the steps of `ultra`; its cofinite form, the one stated here, is
  `UnitTracksAlong hN (dyFilter hN)`: the measured mass at the `k`-th lattice of the
  construction is at least `c₁` times that lattice's own spacing. In the construction's physical units this says the
  tensor channel's physical mass `m′(dyBeta k) / dySpacing N k` is bounded below by `c₁`. `RunSeedAlong N
  (dyFilter hN)` is reached from it (`runSeedAlong_dy_of_reads`). It does not reach `ClayStatement` with the
  existing modules: the chain from `RunSeed` to the flowed gap (`WDelta2`, `FixedWindowDecay`,
  `gapAt_physical_of_fixedWindowDecay`) is written with `∀ᶠ β in atTop`, and its sequence forms are not built.
* Measured remainder. Both sides of the remaining comparison are read off the construction: `m′` is measured on the
  capture, and `dySpacing N k` is the target's own length unit, fixed by the definition of `ClayStatement`. Nothing
  is supplied to the reads beyond what the target itself is written in. What cannot be read from the capture alone is
  the identification of the two, which is asymptotic scaling of the measured mass.

## Case (c): a second measured mass as the unit

Reading the spacing as `1/ξ` for a measured correlation length `ξ = 1/m″` makes the ratio `m′ / m″` a statement
between two measured quantities, with nothing supplied (`SubstrateDecode.LockPersists` is of this form). It does not
meet the consumer: the consumer's spacing is `dySpacing N k = aRun N (dyBeta k)` by definition, so the ratio must
still be joined to `aRun` through the unit tie of `m″` (`unitTracksAlong_of_ratio`). The tie is removed only by a
construction whose spacing at step `k` is a measured length; that is a different target from the frozen
`ClayStatement`, and no module builds it.

## Tests

`SeedFloorAlong hN F` (assumed, in the necessity theorems only): there is `D > 0` such that eventually along `F`
every power-of-two side `n ≥ 2` that meets the run-seed defect `defectW N β n ≤ 1/1000` has `D ≤ n m′`.

1. Degenerate case (argued): at `m′ = ⊤` (a point capture, `SubstrateDecode.measMassOf_point`) `toReal` gives `0`,
   and the floor forbids every seed side; at `β = 0` the seed holds at every side
   (`SeedZeroCoupling.seed_at_zero`), but the floor is eventual in `β` and is not asked there.
2. Vacuity: the floor is asked at a fixed lattice side `n = 2` exactly when `2 m′ < D`, that is at sides below a
   measured length. There it asks the defect to exceed `1/1000` on a torus small in measured units: the small-aperture
   region named in test 3 of `GapFromReads.LongChainRead` (`n m′ → 0`, sub-additive flux energy). At weak coupling,
   at a fixed side, the Gaussian count gives a defect growing like `log β` from the modes that are not Gaussian
   (argued). `D` is a measured length; no constant is in lattice units.
3. Restatement against reduction: the floor is not the unit tie. It is a statement in measured units only, with no
   `aRun`. The unit tie follows from it and `RunSeed` (`unitTracksAlong_of_runSeedAlong`), so under the floor the
   unit tie is a consequence of the consumer's own input, not an extra hypothesis of the route.
4. Without the floor: `RunSeed` may hold at a side small in measured units while `m′ / aRun → 0`; then `m′` is not
   the mass the consumer's gap measures, and the necessity theorems say nothing.

`UnitTracksAlong hN (dyFilter hN)`:

1. Free field (argued): for the massive free scalar at lattice mass `M a`, `m′ = 2Ma` and `c₁ = 2M` works; for the
   massless free field `m′ = 0` and the Prop fails. The test discriminates.
2. Vacuity: no side appears; `c₁` is fixed before `k` and is a physical mass (measured mass over the construction's
   spacing). Nothing grows against it except `k`, along which both sides scale together.
3. Restatement against reduction: it is a restatement. It is the lower bound of one measured channel's physical mass,
   and it reduces nothing; its content is the uniformity of `c₁` in `k`.

## Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the consumer trace and case (b), read from the definitions `stateK`, `latSk`, `aRun_dyBeta`; that the
  unit tie cannot be removed from `ClayStatementDy`, the statement at the two-loop tower (the root
`MassGap.ClayStatement`, at a measured tower, does not carry it: `MeasuredSpacing.observerGap_of_reads`); the readings of `SeedFloorAlong` and `UnitTracksAlong` in the tests above; that no measured mass equals the
  construction's spacing by definition (asymptotic scaling is a property of the theory, not of the read).
* Assumed: `SectorSeedMeasured` (or the three reads of `GapFromReads`), `UnitTracksAlong` in the sufficiency
  theorems, `SeedFloorAlong` in the necessity theorems.

## Parameters

| argument | where | status |
|---|---|---|
| `F` (filter on couplings) | every `…Along` Prop | swept: `atTop` or `dyFilter hN = map dyBeta atTop`; `F ≤ atTop` in the sufficiency theorems |
| `β` (coupling) | every Prop | shared, in the substrate; read along `F` |
| `k` (step) | `…_dy_iff` | the construction's step; `β = dyBeta k` |
| `n` (side) | `RunSeedAlong`, `SeedFloorAlong` | power of two `≥ 2`; existential in the seed, swept in the floor |
| `C` | `RunSeedAlong`, window lemma | existential, a length in the construction's unit (`n · aRun ≤ C`) |
| `D` | `SeedFloorAlong`, window lemma | existential, a measured length (`D ≤ n m′`) |
| `c₁` | `UnitTracksAlong` | existential; derived as `D/C` in the necessity theorems |
| `c`, `c₂` | ratio theorems | existential |
| `μ`, `μ′`, `u` | `TracksAlong`, `tracksAlong_of_ratio` | generic masses and unit |
| `m′` | every Prop | measured: `measMassOf (periodicState hN β) tensorEnergy` |
| `m″` (`E''`) | ratio theorems | measured: `measMassOf (periodicState hN β) E''` |
| `aRun N β`, `dySpacing N k` | `UnitTracksAlong`, `RunSeedAlong` | the target's spacing, fixed by `ClayStatement`'s construction |
| `N` | the type | shared with the substrate |

DERIVED (module-wide): `2` the least side; `1/1000` the run-seed threshold of `WDeltaRun.RunSeed`; `1` the least
colour count of `dyBeta`; `0` the signs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.MeasuredSeed

open Filter Topology
open scoped ENNReal NNReal
open MassGap.SubstrateFluxRead (SectorSeedMeasured)
open MassGap.SubstrateDecode (measMassOf tensorEnergy UnitTracksRun)
open MassGap.PeriodicState (periodicState)
open MassGap.GibbsSpec
open MassGap.ContinuumSchwinger (Cfg dyBeta dySpacing aRun_dyBeta tendsto_dyBeta)

/-! ## 1. Tracking a unit along a filter -/

/-- **A mass tracks a unit along a filter**: some `c > 0` has `ofReal (c · u β) ≤ μ β` eventually along `F`.
DERIVED: `0` the sign of `c`. -/
def TracksAlong (μ : ℝ → ℝ≥0∞) (u : ℝ → ℝ) (F : Filter ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in F, ENNReal.ofReal (c * u β) ≤ μ β

/-- **Tracking passes to a finer filter.** DERIVED: no numeral. -/
theorem TracksAlong.mono {μ : ℝ → ℝ≥0∞} {u : ℝ → ℝ} {F G : Filter ℝ} (h : F ≤ G)
    (hT : TracksAlong μ u G) : TracksAlong μ u F := by
  obtain ⟨c, hc, hev⟩ := hT
  exact ⟨c, hc, hev.filter_mono h⟩

/-- **A measured ratio moves the unit tie**: if `ofReal c · μ′ ≤ μ` eventually and `μ′` tracks `u`, then `μ` tracks
`u`, with constant `c · c₂`. DERIVED: `0` the signs. -/
theorem tracksAlong_of_ratio {μ μ' : ℝ → ℝ≥0∞} {u : ℝ → ℝ} {F : Filter ℝ}
    (hR : ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in F, ENNReal.ofReal c * μ' β ≤ μ β) (hT : TracksAlong μ' u F) :
    TracksAlong μ u F := by
  obtain ⟨c, hc, hRev⟩ := hR
  obtain ⟨c₂, hc₂, hTev⟩ := hT
  refine ⟨c * c₂, mul_pos hc hc₂, ?_⟩
  filter_upwards [hRev, hTev] with β h1 h2
  calc ENNReal.ofReal (c * c₂ * u β) = ENNReal.ofReal c * ENNReal.ofReal (c₂ * u β) := by
        rw [mul_assoc, ENNReal.ofReal_mul hc.le]
    _ ≤ ENNReal.ofReal c * μ' β := by gcongr
    _ ≤ μ β := h1

/-! ## 2. The unit tie and the run seed along a filter -/

section Lattice

variable {N : ℕ}

/-- **The unit tie along a filter**: the measured tensor-channel mass is at least `c₁ · aRun N β`, eventually along
`F`. DERIVED: no numeral. -/
def UnitTracksAlong (hN : N ≠ 0) (F : Filter ℝ) : Prop :=
  TracksAlong (fun β => measMassOf (periodicState hN β) tensorEnergy) (AsymptoticScaling.aRun N) F

/-- **At `atTop` the unit tie is `UnitTracksRun`.** DERIVED: no numeral. -/
theorem unitTracksAlong_atTop_iff (hN : N ≠ 0) : UnitTracksAlong hN atTop ↔ UnitTracksRun hN :=
  Iff.rfl

variable (N) in
/-- **The run seed along a filter**: there is `C > 0` such that, eventually along `F`, some power of two `n ≥ 2`
with `n · aRun N β ≤ C` has `defectW N β n ≤ 1/1000`. DERIVED: `2` the least side; `1/1000` the seed threshold. -/
def RunSeedAlong (F : Filter ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in F, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    (n : ℝ) * AsymptoticScaling.aRun N β ≤ C ∧ ZoomSelfScale.defectW N β n ≤ 1 / 1000

/-- **At `atTop` the run seed along the filter is `RunSeed`.** DERIVED: no numeral. -/
theorem runSeedAlong_atTop_iff : RunSeedAlong N atTop ↔ WDeltaRun.RunSeed N :=
  Iff.rfl

/-- **The seed floor along a filter** (assumed where used): there is a measured length `D > 0` such that,
eventually along `F`, every power-of-two side `n ≥ 2` meeting the run-seed defect has `D ≤ n m′`.
DERIVED: `2` the least side; `1/1000` the seed threshold. -/
def SeedFloorAlong (hN : N ≠ 0) (F : Filter ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ β in F, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    ZoomSelfScale.defectW N β n ≤ 1 / 1000 →
      D ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal

/-- **The window forces the unit tie**: a side bounded below in the measured unit (`D ≤ n m′`) and above in the
spacing (`n · aRun ≤ C`) gives `m′ ≥ (D/C) · aRun`. DERIVED: `2` the least side; `0` the signs. -/
theorem unitTracksAlong_of_window (hN : N ≠ 0) {F : Filter ℝ}
    (h : ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ᶠ β in F, ∃ n : ℕ, 2 ≤ n ∧
      D ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal ∧
      (n : ℝ) * AsymptoticScaling.aRun N β ≤ C) :
    UnitTracksAlong hN F := by
  obtain ⟨D, C, hD, hC, hev⟩ := h
  refine ⟨D / C, div_pos hD hC, ?_⟩
  filter_upwards [hev] with β ⟨n, hn2, hlo, hhi⟩
  have hn : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have ha : AsymptoticScaling.aRun N β ≤ C / n := by
    rw [le_div_iff₀ hn]; linarith
  have h1 : D / C * AsymptoticScaling.aRun N β ≤ D / C * (C / n) :=
    mul_le_mul_of_nonneg_left ha (div_pos hD hC).le
  have h2 : D / C * (C / n) = D / n := by
    rw [div_mul_div_comm, mul_comm D C, mul_div_mul_left _ _ hC.ne']
  have h3 : D / n ≤ (measMassOf (periodicState hN β) tensorEnergy).toReal := by
    rw [div_le_iff₀ hn]; linarith
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_toReal_le

/-- **Necessity: the run seed and the floor give the unit tie.** DERIVED: no numeral. -/
theorem unitTracksAlong_of_runSeedAlong (hN : N ≠ 0) {F : Filter ℝ} (hR : RunSeedAlong N F)
    (hFl : SeedFloorAlong hN F) : UnitTracksAlong hN F := by
  obtain ⟨C, hC, hRev⟩ := hR
  obtain ⟨D, hD, hFev⟩ := hFl
  refine unitTracksAlong_of_window hN ⟨D, C, hD, hC, ?_⟩
  filter_upwards [hRev, hFev] with β ⟨n, hp, hn2, hna, hd⟩ hfl
  exact ⟨n, hn2, hfl n hp hn2 hd, hna⟩

/-- **Sufficiency: the measured seed and the unit tie give the run seed** along any `F ≤ atTop`. At `F = atTop`
this is `SubstrateFluxRead.runSeed_of_sectorSeedMeasured`.
DERIVED: `0`, `2`; `1/1000` the seed of `defectW_le_of_sectorsN`. -/
theorem runSeedAlong_of_sectorSeed [NeZero N] (hN : N ≠ 0) {F : Filter ℝ} (hF : F ≤ atTop)
    (hS : SectorSeedMeasured hN) (hU : UnitTracksAlong hN F) : RunSeedAlong N F := by
  obtain ⟨C, hC, hev⟩ := hS
  obtain ⟨c₁, hc₁, hUev⟩ := hU
  refine ⟨C / c₁, div_pos hC hc₁, ?_⟩
  filter_upwards [hev.filter_mono hF, hUev, (eventually_gt_atTop (0 : ℝ)).filter_mono hF]
    with β hSβ hu hβ
  obtain ⟨-, n, hp, hn2, hnm, hsec⟩ := hSβ
  obtain ⟨b, hb⟩ := hp
  have hb0 : b ≠ 0 := by rintro rfl; rw [hb] at hn2; norm_num at hn2
  have he : Even n := by rw [hb]; exact Nat.even_pow.mpr ⟨even_two, hb0⟩
  refine ⟨n, ⟨b, hb⟩, hn2, ?_, CentreSectorSeedN.defectW_le_of_sectorsN hβ.le hn2 he hsec⟩
  have h1 : ENNReal.ofReal ((n : ℝ) * (c₁ * AsymptoticScaling.aRun N β)) ≤ ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    exact le_trans (by gcongr) hnm
  have h2 := (ENNReal.ofReal_le_ofReal_iff hC.le).mp h1
  rw [le_div_iff₀ hc₁]
  linarith

/-- **Given the measured seed and the floor, the run seed along `F` is the unit tie along `F`.**
DERIVED: no numeral. -/
theorem runSeedAlong_iff_unitTracksAlong [NeZero N] (hN : N ≠ 0) {F : Filter ℝ} (hF : F ≤ atTop)
    (hS : SectorSeedMeasured hN) (hFl : SeedFloorAlong hN F) :
    RunSeedAlong N F ↔ UnitTracksAlong hN F :=
  ⟨fun h => unitTracksAlong_of_runSeedAlong hN h hFl, runSeedAlong_of_sectorSeed hN hF hS⟩

/-- **Given the measured seed and the floor, `RunSeed N` is `UnitTracksRun`.** DERIVED: no numeral. -/
theorem runSeed_iff_unitTracksRun [NeZero N] (hN : N ≠ 0) (hS : SectorSeedMeasured hN)
    (hFl : SeedFloorAlong hN atTop) : WDeltaRun.RunSeed N ↔ UnitTracksRun hN :=
  runSeedAlong_iff_unitTracksAlong hN le_rfl hS hFl

/-! ## 3. Along the couplings of the construction -/

/-- **The couplings of the construction** as a filter on `β`: the image of `atTop` under `dyBeta`.
DERIVED: `1` the least colour count. -/
def dyFilter (hN : N ≠ 0) : Filter ℝ :=
  Filter.map (dyBeta (Nat.one_le_iff_ne_zero.mpr hN)) atTop

/-- **The construction's couplings tend to infinity.** DERIVED: no numeral. -/
theorem dyFilter_le (hN : N ≠ 0) : dyFilter hN ≤ atTop :=
  tendsto_dyBeta _

/-- **The unit tie along the construction**, in its own spacing: the measured mass at step `k` is at least
`c₁ · dySpacing N k`. DERIVED: `1` the least colour count. -/
theorem unitTracksAlong_dy_iff (hN : N ≠ 0) :
    UnitTracksAlong hN (dyFilter hN) ↔ ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (c₁ * dySpacing N k)
        ≤ measMassOf (periodicState hN (dyBeta (Nat.one_le_iff_ne_zero.mpr hN) k)) tensorEnergy := by
  unfold UnitTracksAlong TracksAlong dyFilter
  simp only [Filter.eventually_map, aRun_dyBeta]

/-- **The run seed along the construction**, in its own spacing. DERIVED: `2` the least side; `1/1000` the seed
threshold; `1` the least colour count. -/
theorem runSeedAlong_dy_iff (hN : N ≠ 0) :
    RunSeedAlong N (dyFilter hN) ↔ ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ) * dySpacing N k ≤ C ∧
        ZoomSelfScale.defectW N (dyBeta (Nat.one_le_iff_ne_zero.mpr hN) k) n ≤ 1 / 1000 := by
  unfold RunSeedAlong dyFilter
  simp only [Filter.eventually_map, aRun_dyBeta]

/-- **`UnitTracksRun` gives the unit tie along the construction.** DERIVED: no numeral. -/
theorem unitTracksAlong_dy_of_run (hN : N ≠ 0) (h : UnitTracksRun hN) : UnitTracksAlong hN (dyFilter hN) :=
  TracksAlong.mono (dyFilter_le hN) h

/-- **The measured reads and the unit tie along the construction give the run seed along the construction.**
DERIVED: no numeral. -/
theorem runSeedAlong_dy_of_reads [NeZero N] (hN : N ≠ 0) (hF : RelayChain.CoarseReadsFine N hN)
    (hL : GapFromReads.LongChainRead N hN) (hZ : ZeroFluxGap.ZeroFluxReadsMass N hN)
    (hU : UnitTracksAlong hN (dyFilter hN)) : RunSeedAlong N (dyFilter hN) :=
  runSeedAlong_of_sectorSeed hN (dyFilter_le hN) (GapFromReads.sectorSeedMeasured_of_reads hN hF hL hZ) hU

/-- **A second measured mass moves the unit tie to itself**: a measured ratio `ofReal c · m″ ≤ m′` and the unit tie
of `m″` along `F` give the unit tie of `m′` along `F`. DERIVED: no numeral. -/
theorem unitTracksAlong_of_ratio (hN : N ≠ 0) {F : Filter ℝ} (E'' : ISite → C(Cfg N, ℝ))
    (hR : ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in F,
      ENNReal.ofReal c * measMassOf (periodicState hN β) E'' ≤ measMassOf (periodicState hN β) tensorEnergy)
    (hT : TracksAlong (fun β => measMassOf (periodicState hN β) E'') (AsymptoticScaling.aRun N) F) :
    UnitTracksAlong hN F :=
  tracksAlong_of_ratio hR hT

end Lattice

end MassGap.MeasuredSeed

end

#print axioms MassGap.MeasuredSeed.TracksAlong.mono
#print axioms MassGap.MeasuredSeed.tracksAlong_of_ratio
#print axioms MassGap.MeasuredSeed.unitTracksAlong_atTop_iff
#print axioms MassGap.MeasuredSeed.runSeedAlong_atTop_iff
#print axioms MassGap.MeasuredSeed.unitTracksAlong_of_window
#print axioms MassGap.MeasuredSeed.unitTracksAlong_of_runSeedAlong
#print axioms MassGap.MeasuredSeed.runSeedAlong_of_sectorSeed
#print axioms MassGap.MeasuredSeed.runSeedAlong_iff_unitTracksAlong
#print axioms MassGap.MeasuredSeed.runSeed_iff_unitTracksRun
#print axioms MassGap.MeasuredSeed.dyFilter_le
#print axioms MassGap.MeasuredSeed.unitTracksAlong_dy_iff
#print axioms MassGap.MeasuredSeed.runSeedAlong_dy_iff
#print axioms MassGap.MeasuredSeed.unitTracksAlong_dy_of_run
#print axioms MassGap.MeasuredSeed.runSeedAlong_dy_of_reads
#print axioms MassGap.MeasuredSeed.unitTracksAlong_of_ratio
