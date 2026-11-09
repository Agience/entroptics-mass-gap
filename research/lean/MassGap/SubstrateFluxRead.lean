import Mathlib
import MassGap.SubstrateDecode
import MassGap.CentreSectorSeedN

/-!
# MassGap.SubstrateFluxRead — the centre/flux coordinate read from the capture

`SubstrateDecode` reads the substrate's local channels from a capture `ν` and nothing else. The run seed
`WDeltaRun.RunSeed` reads the torus free-energy defect `defectW`, and the torus partition function sums over the
centre electric-flux sectors, which no local reading sees. This module adds the flux coordinate to the decode:
the scale of the torus and a winding (Polyakov) reading, both read from the capture alone; it proves that a local lock does not give a flux lock, proves what the strong-coupling machinery gives for the
flux sectors, and states what remains between the two locks and the run seed. Declarations are in the namespace
`MassGap.SubstrateFluxRead`.

## 1. The scale of the torus, read from the capture (defined; proved)

* **`lineSite d x k`**: the site `x` moved `k` steps along direction `d`.
* **`linkGap L d l`**: `wilsonDensity ((U l)⁻¹ U l')`, `l'` the link `l` moved `L` steps along `d`. Continuous, in
  `[0, 2]`, `0` where the two links agree.
* **`IsPeriod ν L`**: `0 < L` and `ν (linkGap L d l) = 0` at every direction `d` and link `l`: the capture does not
  distinguish a link from its translate by `L`. **`measPeriod ν = sInf {L | IsPeriod ν L}`**: the least period, `0`
  when the capture has none. No side, extent or scale is supplied; the period is read from `ν`.
* Proved: `torusState_isPeriod`: the periodic Wilson state of extent `M + 1` has period `M + 1`, so
  `measPeriod_torusState_le`: `0 < measPeriod (torusState hN M β) ≤ M + 1`. `measPeriod_twoPhase_sheet`: the
  captures of §3 read exactly their period. `measPeriod_aperiodic`: the point capture at a configuration with a
  single `−1` link has no period and reads `0`.
* Proved downstream (N ≥ 2): `measPeriod (torusState hN M β) = M + 1` (`RectTorusState.measPeriod_torusState`).
  Argued: the infinite-volume
  `periodicState hN β` has no period (it is a limit along growing extents).

## 2. The winding read (defined)

* **`polyHol μ L x U`**: the ordered product of the `L` links of direction `μ` from `x`. **`polyakov μ L x`**:
  `wilsonDensity (polyHol μ L x U) = 1 − Re tr P / N`, the Polyakov reading. At `L` a period of the configuration
  the line closes around the torus and the reading is invariant under the periodic gauge transformations (a class
  function of a closed holonomy; argued, not used).
* **`FluxAdm L μ z`**: `z μ = 0` and `0 < ‖z‖∞ < L`, a transverse separation that is not a multiple of the period.
* **`fluxCov ν μ x z`**: the connected correlation of the Polyakov readings at `x` and `x + z`, at the measured
  period `L = measPeriod ν`. Read from `ν` alone.
* **`FluxLocksAlong ν μ`** for a family `ν : ℕ → State`: the measured period grows without bound, and there are
  `σ > 0` and `C` with `|fluxCov (ν k) μ x z| ≤ C e^{−σ L_k}` eventually in `k`, at every position and every
  admissible separation. `σ` is a rate per unit of the measured period (a string tension times the transverse
  distance `≥ 1`), measured as an existential inside the read.

## 3. A local lock does not give a flux lock (proved)

* **`centreSheet L`** (`N = 2`): the link `(0, y)` is `−1` when `L ∣ y₀`, every other link is `1`. `flatCfg`: every
  link `1`. `ihol_centreSheet`: every plaquette holonomy of `centreSheet L` is `1`; `polyakov_centreSheet`: every
  Polyakov reading of length `L` in direction `0` is `2` (exactly one link of each line is `−1`;
  `card_hits_eq_one`), against `0` on `flatCfg`.
* **`sheetFamily k = twoPhase flatCfg (centreSheet (k + 2))`**, the mixture of two flat connections with different
  holonomy around the torus. `measMass_sheetFamily`, `measMassOf_tensor_sheetFamily`: both local channels read
  mass `∞` (the action density is `0` in both phases, so the connected correlation vanishes), so the local decode
  locks on every capture of the family. `measPeriod_sheetFamily`: the period reads `k + 2`, which grows.
  `fluxCov_sheetFamily`: the flux correlation is `1` at every position and admissible separation, and
  **`not_fluxLocksAlong_sheetFamily`**: the flux read does not lock. **`local_locks_flux_not`**: on one family,
  the local read locks at every member and the flux read fails. The local lock here is the trivial one (rate `∞`, no fluctuation; `LockPersistsAlong` excludes it), so this
shows that the verdict `Locks` does not give a flux lock; the deconfined 4D `Z₂` objection, a finite-rate local
lock with nearly degenerate flux states, is argued (`SubstrateDecode` §4), not built.
* `fluxLocksAlong_pointSheet`: the point family `twoPhase (centreSheet (k + 2)) (centreSheet (k + 2))` satisfies
  `FluxLocksAlong` (`C = 0`), so the Prop is satisfiable; its witness is degenerate.
* Not proved: `FluxLocksAlong` on the Wilson torus family at small `|β|` (Polyakov correlations decaying in the
  period). Box conditioning (`StrongFiniteSize.torusState_sub_le`) reaches only observables local in a box with
  `2 (R + 1) < M + 1`, and a Polyakov line spans the extent; the classical proof is a polymer expansion of winding
  observables, which no module builds.

## 4. The torus capture defeats the local read (proved)

* `cov_lineSite_period`: in `torusState hN M β` the action correlation is periodic in the separation, period
  `M + 1` along each axis. **`cov_eq_zero_of_decaysAt_torus`**: a positive decay rate forces the action
  correlation to vanish at every position and separation. **`locksOf_torusState_iff`**: on a torus capture the
  local read locks exactly when that correlation vanishes identically, and then reads `∞`; otherwise it reads `0`
  (`measMass_torusState_cases`).
* So the decode that sweeps every separation is an infinite-volume read. The captures on which `defectW` is
  written (the torus states) are exactly those on which it is all-or-nothing, and the capture on which it locks
  (`periodicState`, `SubstrateDecode.measMass_strong`) carries no torus trace (argued, §1) and no winding reading. Argued (N ≥ 2): the torus action variance is positive at every `β` (the density is not constant under a measure with positive
  density against Haar), so the local read on a torus capture reads `0`.

## 5. The flux sectors at strong coupling, and the bridge (proved where named, assumed otherwise)

The flux sectors in the form `defectW` reads them are the twisted partition functions
`CentreSectorSeedN.fluxShareN N β n i = 1 − N⁻³ Σ_g Z_g/Z` (`fluxShareN_eq_mean`), and the rest of the defect is
the zero-flux defect `trivialDefectN`. Both are traces of the transfer kernel, which carries `β`: a twisted ratio
`Z_g/Z` is the expectation of `exp(−β ΔS_g)`, which reads `β`. Given the bridge `FluxDuality.TwoSliceLaw` (proved for the Wilson family in
`RectTorusState.twoSliceLaw_rectState`),
`Z_g/Z` is also a capture read: the Hellinger affinity of the two-slice law under a relative centre twist
(`FluxDuality.fluxShareN_isLeast`, `FluxDuality.fluxReadOf_iff`), and `trivialDefectN` is read from the two-slice
density (`FluxDuality.defectReadOf_iff`).

* **`sectors_strong`** (proved): at `0 ≤ β ≤ 2^{-16}`, even `n ≥ 2`, and `(4 + N⁶) β B(n) ≤ 2` with
  `B(n) = StrongFiniteSize.strongBound n = 16 n⁴ · 1024 e^{−(log 2/2) n}`:
  `fluxShareN N β n i ≤ N³ β B(n)/2` and `trivialDefectN N β n i ≤ 2 β B(n)` at every step `i`. From
  `StrongFiniteSize.abs_defectW_strong_le` and `CentreSectorSeedN.sectors_of_defectWN`. The flux share is small: their share of the trace falls like `n⁴ e^{−(log 2/2) n}` in the side (`tendsto_fluxBound`,
  `eventually_sector_condition`). This is the strong flux lock in the twisted form; it is not a reading of the
  capture, and the constants are those of the Dobrushin sweep, not a string tension.
* **`strong_consistency`** (proved): at `0 ≤ β ≤ 2^{-16}` the local read locks (`measMass ≥ log 2`), both sector
  bounds hold at every admissible side, and `|defectW N β n| ≤ β B(n)`. All three come from the one
  single-link Dobrushin input, so this is a consistency witness, not a bridge.
* **`SectorSeedMeasured hN`** (assumed; with `UnitTracksRun`, the inputs of `runSeed_of_sectorSeedMeasured`): there is `C > 0` such that, eventually in `β`, the
  unit channel locks (`0 < m' = measMassOf (periodicState hN β) tensorEnergy`) and some power of two `n ≥ 2` with
  `n · m' ≤ C` has `fluxShareN ≤ 1/80000` and `trivialDefectN ≤ 1/80000` at every step. The side is in the measured unit and `aRun` does not appear; the sector clauses read `β` through the transfer.
`FluxDuality.SectorSeedRead` restates the Prop with both clauses written as reads of the captures; the two are
equivalent under `FluxDuality.CapturesReadTorus` (`sectorSeedMeasured_of_read`, `sectorSeedRead_of_measured`, the
latter with the period tie).
* **`runSeed_of_sectorSeedMeasured`** (proved): `SectorSeedMeasured hN → SubstrateDecode.UnitTracksRun hN →
  RunSeed N` (`CentreSectorSeedN.defectW_le_of_sectorsN` at the measured side; `UnitTracksRun` converts the side to
  run units, the only place `aRun` enters, because the target is written in it).
* Tests of `SectorSeedMeasured` (argued except where named).
  1. Satisfiability of the sector clauses: at fixed `β ∈ [0, 2^{-16}]` they hold at every large even side
     (`sectors_strong`, `tendsto_fluxBound`); the Prop asks them along `β → ∞` at a side bounded in the measured
     unit, which is its content.
  2. Degenerate unit: the lock clause `0 < m'` excludes the vacuous case `m' = 0` (where `n · m' ≤ C` holds at every
     side); `m' = ∞` fails `n · m' ≤ C`.
  3. Restatement against reduction: the sector split is exact up to a fixed number of squarings (`defectW_le_of_sectorsN`; conversely
`sectors_of_defectWN` with `exists_squarings`, at side `2^k n`). With the measured unit tracking `aRun` from both
sides the Prop is equivalent to `RunSeed N` (argued); with `UnitTracksRun` alone it is sufficient. It replaces
`LockPersists` and `DecayGivesSeed` by two named sector clauses and discharges neither.
  4. Why two clauses remain: they are independent. The deconfined 4D `Z₂` theory has the zero-flux clause and not
     the flux clause; the endpoint of the first-order line of the fundamental–adjoint `SU(2)` action has the flux
     clause and not the zero-flux clause (argued in the `CentreSectorSeed` docstring; neither model is the `SU(N)` Wilson family, so this excludes a
general implication between the clauses, not their joint truth along it). The local lock bears on neither directly:
     §3 shows that the lock verdict does not give a flux lock, §4 that it does not read the torus at all.

## 6. What is missing between the reads and the seed

* Flux: the capture-only flux read is `FluxLocksAlong` (Polyakov). The seed reads `fluxShareN` (twisted traces).
  Their identification is the electric-flux duality (the Polyakov correlator at transverse separation `z` is a
  sum of non-zero-flux traces of the transfer in the transverse direction), not built: `FluxLocksAlong → fluxShareN`
  is open. `FluxDuality` reads the flux clause from the full two-slice law, not from `tr P` correlators, and so does
  not supply this implication. With it, a flux lock uniform along `β` at the measured window would give the flux
  clause.
* Zero-flux: a decay of local correlations on `periodicState` gives no torus statement (§4); the zero-flux clause
  needs a finite-volume gap of the transfer restricted to the zero-flux sector at the window side, uniformly in
  `β`. That is the finite-volume against infinite-volume gap; `tendsto_periodicState` is weak-* convergence of
  local readings only and carries no rate.

## 7. Parameters

| argument | where | status |
|---|---|---|
| `ν` (the capture) | every read | the input |
| `L` (period) | `IsPeriod`, `polyakov`, `FluxAdm` | measured: `measPeriod ν` in `fluxCov` and `FluxLocksAlong` |
| `d`, `l` (direction, link) | `IsPeriod` | swept over all |
| `μ` (winding direction) | `polyakov`, `fluxCov`, `FluxLocksAlong` | chosen: one axis; the axes are equivalent on rotation-invariant captures (the torus states), not in general: `sheetFamily` locks along axes 1–3 and fails along 0 |
| `x`, `z` (position, transverse separation) | `fluxCov`, `FluxLocksAlong` | swept over all admissible |
| `σ`, `C` (flux rate, prefactor) | `FluxLocksAlong` | measured: existential inside the read |
| `k` (family index) | `FluxLocksAlong` | the family's own index; the read uses `measPeriod (ν k)`, not `k` |
| `N` (colour count) | the type `State (Cfg N)` | measured downstream: `MeasureN.measN` (centre phases of the law of `tr P` at the measured period); exact on the torus states at every real `β`, `N ≥ 2` (`MeasureN.measN_torusState`); torus captures only; axis `0` and the origin chosen |
| `β` (coupling) | `torusState`, `periodicState`, sector quantities | shared, in the substrate; the Polyakov and period reads never read it; `fluxShareN`, `trivialDefectN` do |
| `n` (side) | `sectors_strong`, `SectorSeedMeasured` | the torus side of the seed; bounded in the measured unit `1/m'` in `SectorSeedMeasured` |
| `C` | `SectorSeedMeasured` | measured: existential, in units of the measured length `1/m'` |
| `1/80000` | `SectorSeedMeasured` | the threshold of `defectW_le_of_sectorsN` |
| `aRun`, `c₁` | `UnitTracksRun` only | supplied spacing; enters only to meet `RunSeed`, written in it |

`N` is measured downstream by `MeasureN.measN`, the number of unit `ω` leaving the law of `tr P` at
`measPeriod ν` invariant. It equals `N` on `torusState hN M β` for `N ≥ 2` at every real `β`, by a central twist
of one time slice and a trace gap on `SU(N)`, with no Haar moment computed; the vanishing half,
`ν((tr P)^k) = 0` for `N ∤ k` on the torus states, is `MeasureN.moments_vanish_torusState`. The least-`n` route
would still need `∫ (tr U)^N dU = 1`, which no module proves, and the count does not use it. On `periodicState`
the read is argued to give `1`, not `N`, since its measured period is argued to be `0`. The rank `N` itself is read by the empty loop (`tr 1 = N`), which is the type, not
the centre.

DERIVED (module-wide): `0` the origin, the winding axis of the sheet and the sign of rates; `1` the unit step,
the identity and the flux correlation `(0 − 2)²/4` of the sheet family; `2` the colour count of the sheet, the
density of `−1`, the least sheet period with an admissible separation (`k + 2`) and the two phases; `4` the
dimension and the `4` of `twoPhase`; `65536 = 2^{16}` the threshold of `StrongKernelNear`; `log 2` its rate;
`80000`, `1000`, `4 + N⁶`, `N³/2` the constants of `CentreSectorSeedN`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SubstrateFluxRead

open Filter Topology
open scoped ENNReal NNReal
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.FocusZoom (stateCov)
open MassGap.SUN (SU)
open MassGap.ContinuumSchwinger (Cfg)
open MassGap.ObserverEnergyMoments (plaqField negOne negOne_inv)
open MassGap.StrongFiniteSize (snorm snorm_le_iff strongBound)
open MassGap.PeriodicState (periodicState torusState torusObs)
open MassGap.ObserverBlockReading (planes blockPlaqs blockEnergy plaqField_apply blockEnergy_flat)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_one wilsonDensity_nonneg continuous_wilsonDensity)
open MassGap.SubstrateDecode

variable {N : ℕ}

/-! ## 1. The period of a capture -/

/-- **A site moved `k` steps along `d`.** DERIVED: no numeral. -/
def lineSite (d : Fin 4) (x : ISite) (k : ℤ) : ISite := Function.update x d (x d + k)

/-- DERIVED: no numeral. -/
theorem lineSite_self (d : Fin 4) (x : ISite) (k : ℤ) : lineSite d x k d = x d + k := by
  simp [lineSite]

/-- **The link gap**: the Wilson density of `(U l)⁻¹ U l'`, `l'` the link `l` moved `L` steps along `d`.
DERIVED: no numeral. -/
def linkGap (L : ℕ) (d : Fin 4) (l : ILink) : C(Cfg N, ℝ) :=
  ⟨fun U => wilsonDensity ((U l)⁻¹ * U (l.1, lineSite d l.2 L)),
    continuous_wilsonDensity.comp (((continuous_apply l).inv).mul (continuous_apply _))⟩

/-- DERIVED: no numeral. -/
theorem linkGap_apply (L : ℕ) (d : Fin 4) (l : ILink) (U : Cfg N) :
    linkGap L d l U = wilsonDensity ((U l)⁻¹ * U (l.1, lineSite d l.2 L)) := rfl

/-- **`L` is a period of the capture**: it does not distinguish any link from its translate by `L`.
DERIVED: `0` the threshold. -/
def IsPeriod (ν : State (Cfg N)) (L : ℕ) : Prop :=
  0 < L ∧ ∀ (d : Fin 4) (l : ILink), ν (linkGap L d l) = 0

/-- **The measured period**: the least period of the capture, `0` when it has none. DERIVED: no numeral. -/
def measPeriod (ν : State (Cfg N)) : ℕ := sInf {L | IsPeriod ν L}

/-- DERIVED: no numeral. -/
theorem measPeriod_le {ν : State (Cfg N)} {L : ℕ} (h : IsPeriod ν L) : measPeriod ν ≤ L :=
  Nat.sInf_le h

/-- DERIVED: no numeral. -/
theorem isPeriod_measPeriod {ν : State (Cfg N)} (h : ∃ L, IsPeriod ν L) : IsPeriod ν (measPeriod ν) :=
  Nat.sInf_mem h

/-- **The measured period is the period when no shorter one holds.** DERIVED: `0` the threshold. -/
theorem measPeriod_eq {ν : State (Cfg N)} {L : ℕ} (h : IsPeriod ν L)
    (hmin : ∀ L', 0 < L' → L' < L → ¬ IsPeriod ν L') : measPeriod ν = L := by
  refine le_antisymm (measPeriod_le h) (le_csInf ⟨L, h⟩ fun b hb => ?_)
  by_contra hlt
  exact hmin b hb.1 (not_le.mp hlt) hb

/-- **A capture with no period reads `0`.** DERIVED: `0` the empty infimum. -/
theorem measPeriod_eq_zero {ν : State (Cfg N)} (h : ∀ L, ¬ IsPeriod ν L) : measPeriod ν = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inr (Set.eq_empty_of_forall_notMem h))

/-- A state reads `0` on `0`. DERIVED: `0`. -/
theorem state_zero (ν : State (Cfg N)) : ν 0 = 0 := by
  have h := ν.map_sub 0 0
  rwa [sub_self, sub_self] at h

/-- Reduction modulo the extent forgets a multiple of the extent. DERIVED: `1` the successor of the extent. -/
theorem finMod_add_mul (M : ℕ) (s k : ℤ) :
    InfiniteLattice.finMod M (s + k * ((M : ℤ) + 1)) = InfiniteLattice.finMod M s := by
  apply Fin.ext
  show ((s + k * ((M : ℤ) + 1)) % ((M : ℤ) + 1)).toNat = (s % ((M : ℤ) + 1)).toNat
  rw [Int.add_mul_emod_self_right]

/-- **A periodic configuration does not see a translate by a multiple of the extent.** DERIVED: `1` the
successor of the extent. -/
theorem pullback_lineSite (M : ℕ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (a d : Fin 4) (s : ISite)
    (k : ℤ) :
    InfiniteLattice.pullback M W (a, lineSite d s (k * ((M : ℤ) + 1))) = InfiniteLattice.pullback M W (a, s) := by
  simp only [InfiniteLattice.pullback, InfiniteLattice.linkMod]
  congr 2
  funext j
  show InfiniteLattice.finMod M (lineSite d s (k * ((M : ℤ) + 1)) j) = InfiniteLattice.finMod M (s j)
  simp only [lineSite, Function.update_apply]
  split_ifs with h
  · subst h; exact finMod_add_mul M (s j) k
  · rfl

/-- **Two observables that agree on periodic configurations have the same torus reading.** DERIVED: no
numeral. -/
theorem torusState_congr (hN : N ≠ 0) (M : ℕ) (β : ℝ) {f g : C(Cfg N, ℝ)}
    (h : ∀ W, f (InfiniteLattice.pullback M W) = g (InfiniteLattice.pullback M W)) :
    torusState hN M β f = torusState hN M β g := by
  have e : torusObs M f = torusObs M g := funext h
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M f)
    = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M g)
  rw [e]

/-- **The torus state of extent `M + 1` has period `M + 1`.** DERIVED: `1` the successor of the extent. -/
theorem torusState_isPeriod (hN : N ≠ 0) (M : ℕ) (β : ℝ) : IsPeriod (torusState hN M β) (M + 1) := by
  refine ⟨Nat.succ_pos M, fun d l => ?_⟩
  rw [← state_zero (torusState hN M β)]
  refine torusState_congr hN M β fun W => ?_
  have e : (((M + 1 : ℕ) : ℤ)) = (1 : ℤ) * ((M : ℤ) + 1) := by push_cast; ring
  rw [linkGap_apply, e, pullback_lineSite, inv_mul_cancel, wilsonDensity_one hN]
  rfl

/-- **The torus state reads a period between `1` and its extent.** DERIVED: `0`, `1` the bounds. -/
theorem measPeriod_torusState_le (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    0 < measPeriod (torusState hN M β) ∧ measPeriod (torusState hN M β) ≤ M + 1 :=
  ⟨(isPeriod_measPeriod ⟨_, torusState_isPeriod hN M β⟩).1, measPeriod_le (torusState_isPeriod hN M β)⟩

/-- **The single-defect configuration**: the link `(0, 0)` is `−1`, every other link `1`. DERIVED: `0` the
link; `2` the colour count. -/
def oneDefect : Cfg 2 := fun l => if l = ((0 : Fin 4), (0 : ISite)) then negOne else 1

/-- DERIVED: `2` the density of `−1`. -/
theorem wilsonDensity_negOne_inv_mul_one : wilsonDensity ((negOne)⁻¹ * (1 : SU 2)) = 2 := by
  rw [mul_one, negOne_inv]; exact wilsonDensity_negOne

/-- **A capture with no period reads `0`**: the point capture at `oneDefect`. DERIVED: `0` the link and the
reading; `2` the colour count. -/
theorem measPeriod_aperiodic : measPeriod (twoPhase oneDefect oneDefect) = 0 := by
  refine measPeriod_eq_zero fun L ⟨hL, h⟩ => ?_
  have h0 := h 0 ((0 : Fin 4), (0 : ISite))
  rw [twoPhase_apply, linkGap_apply] at h0
  dsimp only at h0
  have hne : (((0 : Fin 4), lineSite 0 (0 : ISite) (L : ℤ)) : ILink) ≠ ((0 : Fin 4), (0 : ISite)) := by
    intro he
    have := congrFun (congrArg Prod.snd he) 0
    dsimp only at this
    rw [lineSite_self] at this
    simp only [Pi.zero_apply, zero_add, Nat.cast_eq_zero] at this
    omega
  have hv : wilsonDensity ((oneDefect ((0 : Fin 4), (0 : ISite)))⁻¹
      * oneDefect ((0 : Fin 4), lineSite 0 (0 : ISite) (L : ℤ))) = 2 := by
    simp only [oneDefect, if_neg hne, if_true]
    exact wilsonDensity_negOne_inv_mul_one
  rw [hv] at h0
  norm_num at h0

/-! ## 2. The winding read -/

/-- **The holonomy of the line of `L` links of direction `μ` from `x`.** DERIVED: `0`, `1` the empty line
and the identity. -/
def polyHol (μ : Fin 4) : ℕ → ISite → Cfg N → SU N
  | 0, _, _ => 1
  | L + 1, x, U => polyHol μ L x U * U (μ, lineSite μ x L)

/-- DERIVED: no numeral. -/
theorem continuous_polyHol (μ : Fin 4) (L : ℕ) (x : ISite) : Continuous (polyHol (N := N) μ L x) := by
  induction L with
  | zero => exact continuous_const
  | succ L ih =>
    show Continuous fun U : Cfg N => polyHol μ L x U * U (μ, lineSite μ x L)
    exact ih.mul (continuous_apply _)

/-- **The Polyakov reading**: `1 − Re tr P / N` of the line holonomy. DERIVED: no numeral. -/
def polyakov (μ : Fin 4) (L : ℕ) (x : ISite) : C(Cfg N, ℝ) :=
  ⟨fun U => wilsonDensity (polyHol μ L x U), continuous_wilsonDensity.comp (continuous_polyHol μ L x)⟩

/-- DERIVED: no numeral. -/
theorem polyakov_apply (μ : Fin 4) (L : ℕ) (x : ISite) (U : Cfg N) :
    polyakov μ L x U = wilsonDensity (polyHol μ L x U) := rfl

/-- **An admissible transverse separation**: transverse to the winding, non-zero, shorter than the period.
DERIVED: `0` the threshold. -/
def FluxAdm (L : ℕ) (μ : Fin 4) (z : ISite) : Prop := z μ = 0 ∧ 0 < snorm z ∧ snorm z < L

/-- **The flux correlation**: the connected correlation of two Polyakov readings at the measured period.
DERIVED: no numeral. -/
def fluxCov (ν : State (Cfg N)) (μ : Fin 4) (x z : ISite) : ℝ :=
  stateCov ν (polyakov μ (measPeriod ν) x) (polyakov μ (measPeriod ν) (x + z))

/-- **The flux read locks along a family**: the measured period grows, and the flux correlation falls at a fixed
rate per unit of the measured period. DERIVED: `0` the sign of the rate. -/
def FluxLocksAlong (ν : ℕ → State (Cfg N)) (μ : Fin 4) : Prop :=
  Tendsto (fun k => measPeriod (ν k)) atTop atTop ∧
    ∃ σ C : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ x z : ISite, FluxAdm (measPeriod (ν k)) μ z →
      |fluxCov (ν k) μ x z| ≤ C * Real.exp (-(σ * measPeriod (ν k)))

/-! ## 3. The two coordinates are independent -/

/-- **The centre sheet**: the link `(0, y)` is `−1` when `L ∣ y₀`, every other link `1`. DERIVED: `0` the
winding axis; `2` the colour count. -/
def centreSheet (L : ℕ) : Cfg 2 := fun l => if l.1 = 0 ∧ l.2 0 % (L : ℤ) = 0 then negOne else 1

/-- The flat configuration. DERIVED: `1` the identity; `2` the colour count. -/
def flatCfg : Cfg 2 := fun _ => 1

/-- **Every plaquette of the centre sheet is trivial.** DERIVED: `0` the winding axis. -/
theorem ihol_centreSheet (L : ℕ) (q : IPlaq) : ihol q (centreSheet L) = 1 := by
  obtain ⟨⟨a, b⟩, x⟩ := q
  rw [ihol_eq]
  dsimp only
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha; subst hb; group
  · subst ha
    have h1 : centreSheet L (b, ishift 0 x) = 1 := by simp [centreSheet, hb]
    have h2 : centreSheet L (b, x) = 1 := by simp [centreSheet, hb]
    have h3 : centreSheet L (0, ishift b x) = centreSheet L (0, x) := by
      simp only [centreSheet, ishift_apply_zero hb]
    rw [h1, h2, h3]; group
  · subst hb
    have h1 : centreSheet L (a, x) = 1 := by simp [centreSheet, ha]
    have h2 : centreSheet L (a, ishift 0 x) = 1 := by simp [centreSheet, ha]
    have h3 : centreSheet L (0, ishift a x) = centreSheet L (0, x) := by
      simp only [centreSheet, ishift_apply_zero ha]
    rw [h1, h2, h3]; group
  · simp [centreSheet, ha, hb]

/-- **A configuration with trivial plaquettes has zero action density.** DERIVED: `0`. -/
theorem siteEnergy_of_hol_one (hN : N ≠ 0) {U : Cfg N} (hU : ∀ q, ihol q U = 1) (x : ISite) :
    siteEnergy x U = 0 := by
  rw [siteEnergy_apply]
  unfold blockEnergy
  rw [Finset.sum_eq_zero fun q _ => ?_, mul_zero]
  rw [plaqField_apply, hU, wilsonDensity_one hN]

/-- DERIVED: `0`. -/
theorem tensorEnergy_of_hol_one (hN : N ≠ 0) {U : Cfg N} (hU : ∀ q, ihol q U = 1) (x : ISite) :
    tensorEnergy x U = 0 := by
  simp only [tensorEnergy, ContinuousMap.sub_apply, plaqField_apply, hU, wilsonDensity_one hN, sub_self]

/-- **Two phases that a reading does not separate read infinite mass.** DERIVED: `0`. -/
theorem measMassOf_twoPhase_top {A B : Cfg N} {E : ISite → C(Cfg N, ℝ)} (h : ∀ x, E x A = E x B) :
    measMassOf (twoPhase A B) E = ⊤ :=
  measMassOf_top_of_cov_zero fun x z => by rw [stateCov_twoPhase, h x, sub_self, zero_mul, zero_div]

/-- DERIVED: `1` the identity. -/
theorem ihol_flat (q : IPlaq) : ihol q flatCfg = 1 := by
  rw [ihol_eq]; simp [flatCfg]

/-- **Exactly one of `L` consecutive integers is divisible by `L`.** DERIVED: `0`, `1`. -/
theorem card_hits_eq_one (a : ℤ) {L : ℕ} (hL : 0 < L) :
    ((Finset.range L).filter (fun j : ℕ => (a + j) % (L : ℤ) = 0)).card = 1 := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  rw [Finset.card_eq_one]
  refine ⟨((-a) % (L : ℤ)).toNat, ?_⟩
  have h0 : 0 ≤ (-a) % (L : ℤ) := Int.emod_nonneg _ hL'.ne'
  have h1 : (-a) % (L : ℤ) < L := Int.emod_lt_of_pos _ hL'
  have hr : (-a) % (L : ℤ) + L * ((-a) / L) = -a := Int.emod_add_mul_ediv _ _
  have ht : (((-a) % (L : ℤ)).toNat : ℤ) = (-a) % (L : ℤ) := Int.toNat_of_nonneg h0
  set r := (-a) % (L : ℤ) with hrdef
  set q := (-a) / (L : ℤ) with hqdef
  clear_value r q
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hm⟩
    obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hm
    have hjL : (j : ℤ) < L := by exact_mod_cast hj
    have he : (j : ℤ) - r = L * c + L * q := by linarith
    have he' : (j : ℤ) - r = L * (c + q) := by rw [he]; ring
    have e1 : c + q < 1 := by
      by_contra hh
      have : L * 1 ≤ L * (c + q) := mul_le_mul_of_nonneg_left (not_lt.mp hh) hL'.le
      linarith
    have e2 : -1 < c + q := by
      by_contra hh
      have : L * (c + q) ≤ L * (-1) := mul_le_mul_of_nonneg_left (not_lt.mp hh) hL'.le
      have : (0 : ℤ) ≤ j := by positivity
      linarith
    have e3 : c + q = 0 := by omega
    rw [e3, mul_zero] at he'
    omega
  · intro hj
    have hjr : (j : ℤ) = r := by rw [hj, ht]
    refine ⟨by omega, ?_⟩
    rw [hjr]
    have : a + r = L * (-q) := by linarith
    rw [this]
    exact Int.mul_emod_right _ _

/-- **The line holonomy of the centre sheet counts the sheet links on the line.** DERIVED: `0` the winding
axis. -/
theorem polyHol_centreSheet (L : ℕ) (x : ISite) (k : ℕ) :
    polyHol 0 k x (centreSheet L)
      = negOne ^ ((Finset.range k).filter (fun j : ℕ => (x 0 + j) % (L : ℤ) = 0)).card := by
  induction k with
  | zero => simp [polyHol]
  | succ k ih =>
    show polyHol 0 k x (centreSheet L) * centreSheet L (0, lineSite 0 x k) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    have hl : lineSite 0 x (k : ℤ) 0 = x 0 + k := lineSite_self 0 x k
    by_cases hk : (x 0 + k) % (L : ℤ) = 0
    · rw [if_pos hk, Finset.card_insert_of_notMem (by simp), pow_succ]
      simp [centreSheet, hl, hk]
    · rw [if_neg hk]
      simp [centreSheet, hl, hk]

/-- DERIVED: `1` the identity. -/
theorem polyHol_flat (μ : Fin 4) (k : ℕ) (x : ISite) : polyHol μ k x flatCfg = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show polyHol μ k x flatCfg * flatCfg (μ, lineSite μ x k) = 1
    rw [ih]; simp [flatCfg]

/-- **Every Polyakov reading of length `L` along `0` reads `2` on the centre sheet.** DERIVED: `2` the density
of `−1`. -/
theorem polyakov_centreSheet {L : ℕ} (hL : 0 < L) (x : ISite) : polyakov 0 L x (centreSheet L) = 2 := by
  rw [polyakov_apply, polyHol_centreSheet, card_hits_eq_one _ hL, pow_one]
  exact wilsonDensity_negOne

/-- DERIVED: `0`. -/
theorem polyakov_flat (μ : Fin 4) (L : ℕ) (x : ISite) : polyakov μ L x flatCfg = 0 := by
  rw [polyakov_apply, polyHol_flat]; exact wilsonDensity_one two_ne_zero

/-- DERIVED: `0`. -/
theorem linkGap_flat (L : ℕ) (d : Fin 4) (l : ILink) : linkGap L d l flatCfg = 0 := by
  rw [linkGap_apply]; simp only [flatCfg, inv_one, mul_one]; exact wilsonDensity_one two_ne_zero

/-- **The centre sheet has period `L` in every direction.** DERIVED: `0`. -/
theorem linkGap_centreSheet {L : ℕ} (d : Fin 4) (l : ILink) : linkGap L d l (centreSheet L) = 0 := by
  rw [linkGap_apply]
  have e : centreSheet L (l.1, lineSite d l.2 L) = centreSheet L l := by
    simp only [centreSheet, lineSite, Function.update_apply]
    split_ifs <;> simp_all [Int.add_emod_right]
  rw [e, inv_mul_cancel]; exact wilsonDensity_one two_ne_zero

/-- **A shorter translate along the winding axis moves a sheet link off the sheet.** DERIVED: `2` the density
of `−1`; `0` the link. -/
theorem linkGap_centreSheet_short {L L' : ℕ} (h0 : 0 < L') (h1 : L' < L) :
    linkGap L' 0 ((0 : Fin 4), (0 : ISite)) (centreSheet L) = 2 := by
  rw [linkGap_apply]
  have hs : centreSheet L ((0 : Fin 4), (0 : ISite)) = negOne := by simp [centreSheet]
  have hm : ((L' : ℤ)) % (L : ℤ) ≠ 0 := by
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h1)]
    exact_mod_cast h0.ne'
  have ht : centreSheet L ((0 : Fin 4), lineSite 0 (0 : ISite) (L' : ℤ)) = 1 := by
    simp only [centreSheet, lineSite_self]
    simp [hm]
  rw [hs, ht]
  exact wilsonDensity_negOne_inv_mul_one

/-- **A two-phase capture with one phase the sheet reads the sheet's period.** DERIVED: `0`, `2`. -/
theorem measPeriod_twoPhase_sheet {L : ℕ} (hL : 0 < L) {A : Cfg 2} (hA : ∀ d l, linkGap L d l A = 0) :
    measPeriod (twoPhase A (centreSheet L)) = L := by
  refine measPeriod_eq ⟨hL, fun d l => ?_⟩ fun L' h0 h1 ⟨_, h⟩ => ?_
  · rw [twoPhase_apply, hA, linkGap_centreSheet]; norm_num
  · have h' := h 0 ((0 : Fin 4), (0 : ISite))
    rw [twoPhase_apply, linkGap_centreSheet_short h0 h1] at h'
    have hn := wilsonDensity_nonneg two_ne_zero
      ((A ((0 : Fin 4), (0 : ISite)))⁻¹ * A ((0 : Fin 4), lineSite 0 (0 : ISite) (L' : ℤ)))
    rw [linkGap_apply] at h'
    linarith

/-- **The sheet family**: the mixture of the flat configuration and the centre sheet of period `k + 2`.
DERIVED: `2` the least period with an admissible separation. -/
def sheetFamily (k : ℕ) : State (Cfg 2) := twoPhase flatCfg (centreSheet (k + 2))

/-- DERIVED: `2`. -/
theorem measPeriod_sheetFamily (k : ℕ) : measPeriod (sheetFamily k) = k + 2 :=
  measPeriod_twoPhase_sheet (by omega) fun d l => linkGap_flat _ d l

/-- **The action density reads infinite mass on every member.** DERIVED: `2` the colour count. -/
theorem measMass_sheetFamily (k : ℕ) : measMass (sheetFamily k) = ⊤ :=
  measMassOf_twoPhase_top fun x => by
    rw [siteEnergy_of_hol_one two_ne_zero ihol_flat, siteEnergy_of_hol_one two_ne_zero (ihol_centreSheet _)]

/-- **The tensor channel reads infinite mass on every member.** DERIVED: `2` the colour count. -/
theorem measMassOf_tensor_sheetFamily (k : ℕ) : measMassOf (sheetFamily k) tensorEnergy = ⊤ :=
  measMassOf_twoPhase_top fun x => by
    rw [tensorEnergy_of_hol_one two_ne_zero ihol_flat,
      tensorEnergy_of_hol_one two_ne_zero (ihol_centreSheet _)]

/-- **The flux correlation is `1` at every position and separation.** DERIVED: `1 = (0 − 2)²/4`. -/
theorem fluxCov_sheetFamily (k : ℕ) (x z : ISite) : fluxCov (sheetFamily k) 0 x z = 1 := by
  unfold fluxCov
  rw [measPeriod_sheetFamily]
  unfold sheetFamily
  rw [stateCov_twoPhase, polyakov_flat, polyakov_flat, polyakov_centreSheet (by omega),
    polyakov_centreSheet (by omega)]
  norm_num

/-- The unit separation along axis `1`. DERIVED: `1` the step. -/
def unitOne : ISite := ![0, 1, 0, 0]

/-- DERIVED: `0`, `1`, `2`. -/
theorem fluxAdm_unitOne {L : ℕ} (hL : 2 ≤ L) : FluxAdm L 0 unitOne := by
  have hle : snorm unitOne ≤ 1 := by
    rw [snorm_le_iff]; intro i; fin_cases i <;> simp [unitOne]
  refine ⟨rfl, Nat.pos_of_ne_zero fun h0 => ?_, by omega⟩
  have h := (snorm_le_iff (x := unitOne) (k := 0)).mp h0.le 1
  simp [unitOne] at h

/-- **The flux read does not lock on the sheet family.** DERIVED: `1` the flux correlation; `2` the period
offset. -/
theorem not_fluxLocksAlong_sheetFamily : ¬ FluxLocksAlong sheetFamily 0 := by
  rintro ⟨-, σ, C, hσ, hev⟩
  obtain ⟨k, hk, hkC⟩ := (hev.and (eventually_ge_atTop ⌈C / σ⌉₊)).exists
  have h := hk 0 unitOne (by rw [measPeriod_sheetFamily]; exact fluxAdm_unitOne (by omega))
  rw [fluxCov_sheetFamily, measPeriod_sheetFamily, abs_one] at h
  set t : ℝ := σ * ((k + 2 : ℕ) : ℝ) with ht
  have h1 : Real.exp t ≤ C := by
    have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos t).le
    rwa [one_mul, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h2
  have h3 := Real.add_one_le_exp t
  have hkr : C / σ ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hkC)
  have h4 : C ≤ σ * k := by rwa [div_le_iff₀ hσ, mul_comm] at hkr
  have h5 : σ * (k : ℝ) ≤ t := by
    rw [ht]; push_cast
    nlinarith
  linarith

/-- **The local read locks and the flux read does not, on one family.** DERIVED: `0` the winding axis. -/
theorem local_locks_flux_not :
    (∀ k, Locks (sheetFamily k) ∧ LocksOf (sheetFamily k) tensorEnergy) ∧
      Tendsto (fun k => measPeriod (sheetFamily k)) atTop atTop ∧ ¬ FluxLocksAlong sheetFamily 0 := by
  refine ⟨fun k => ⟨?_, ?_⟩, ?_, not_fluxLocksAlong_sheetFamily⟩
  · unfold Locks; rw [measMass_sheetFamily k]; exact ENNReal.zero_lt_top
  · unfold LocksOf; rw [measMassOf_tensor_sheetFamily k]; exact ENNReal.zero_lt_top
  · simp only [measPeriod_sheetFamily]
    exact tendsto_add_atTop_nat 2

/-- **The point sheet family satisfies the flux lock** (`C = 0`): the Prop is satisfiable. DERIVED: `0`, `1`,
`2`. -/
theorem fluxLocksAlong_pointSheet :
    FluxLocksAlong (fun k => twoPhase (centreSheet (k + 2)) (centreSheet (k + 2))) 0 := by
  have hp : ∀ k, measPeriod (twoPhase (centreSheet (k + 2)) (centreSheet (k + 2))) = k + 2 := fun k =>
    measPeriod_twoPhase_sheet (by omega) fun d l => linkGap_centreSheet d l
  refine ⟨?_, 1, 0, one_pos, Eventually.of_forall fun k x z _ => ?_⟩
  · simp only [hp]
    exact tendsto_add_atTop_nat 2
  · unfold fluxCov
    rw [stateCov_twoPhase, sub_self, zero_mul, zero_div, abs_zero, zero_mul]

/-! ## 4. The torus capture defeats the local read -/

/-- DERIVED: `1` the step. -/
theorem ishift_lineSite (a d : Fin 4) (y : ISite) (k : ℤ) :
    ishift a (lineSite d y k) = lineSite d (ishift a y) k := by
  funext j
  simp only [ishift, lineSite, Function.update_apply]
  split_ifs <;> subst_vars <;> omega

/-- DERIVED: `1` the successor of the extent. -/
theorem ihol_pullback_lineSite (M : ℕ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (p : Fin 4 × Fin 4)
    (y : ISite) (d : Fin 4) (k : ℤ) :
    ihol (p, lineSite d y (k * ((M : ℤ) + 1))) (InfiniteLattice.pullback M W)
      = ihol (p, y) (InfiniteLattice.pullback M W) := by
  rw [ihol_eq, ihol_eq]
  dsimp only
  rw [ishift_lineSite, ishift_lineSite, pullback_lineSite, pullback_lineSite, pullback_lineSite,
    pullback_lineSite]

/-- **The action density at a site is the mean over the six planes.** DERIVED: `1` the block side. -/
theorem siteEnergy_eq_planes (y : ISite) (U : Cfg N) :
    siteEnergy y U = ((planes.card : ℝ))⁻¹ * ∑ p ∈ planes, wilsonDensity (ihol (p, y) U) := by
  rw [siteEnergy_apply]
  unfold blockEnergy blockPlaqs
  rw [blockSites_one, Finset.card_product, Finset.card_singleton, mul_one, Finset.sum_product]
  simp only [Finset.sum_singleton, plaqField_apply]

/-- DERIVED: `1` the successor of the extent. -/
theorem siteEnergy_pullback_lineSite (M : ℕ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (y : ISite)
    (d : Fin 4) (k : ℤ) :
    siteEnergy (lineSite d y (k * ((M : ℤ) + 1))) (InfiniteLattice.pullback M W)
      = siteEnergy y (InfiniteLattice.pullback M W) := by
  rw [siteEnergy_eq_planes, siteEnergy_eq_planes]
  simp only [ihol_pullback_lineSite]

/-- **In a torus state the action correlation is periodic in the separation.** DERIVED: `1` the successor of
the extent. -/
theorem cov_lineSite_period (hN : N ≠ 0) (M : ℕ) (β : ℝ) (x y : ISite) (d : Fin 4) (k : ℤ) :
    stateCov (torusState hN M β) (siteEnergy x) (siteEnergy (lineSite d y (k * ((M : ℤ) + 1))))
      = stateCov (torusState hN M β) (siteEnergy x) (siteEnergy y) := by
  unfold stateCov
  rw [torusState_congr hN M β (f := siteEnergy x * siteEnergy (lineSite d y (k * ((M : ℤ) + 1))))
      (g := siteEnergy x * siteEnergy y) fun W => by
        simp only [ContinuousMap.mul_apply, siteEnergy_pullback_lineSite],
    torusState_congr hN M β (f := siteEnergy (lineSite d y (k * ((M : ℤ) + 1)))) (g := siteEnergy y)
      fun W => siteEnergy_pullback_lineSite M W y d k]

/-- **On a torus capture a positive decay rate forces the action correlation to vanish.** DERIVED: `0` the
winding axis of the translation; `1` the successor of the extent. -/
theorem cov_eq_zero_of_decaysAt_torus (hN : N ≠ 0) (M : ℕ) (β : ℝ) {m : ℝ} (hm : 0 < m)
    (h : DecaysAt (torusState hN M β) siteEnergy m) (x z : ISite) :
    stateCov (torusState hN M β) (siteEnergy x) (siteEnergy (x + z)) = 0 := by
  obtain ⟨C, hC⟩ := h
  set c := stateCov (torusState hN M β) (siteEnergy x) (siteEnergy (x + z)) with hc
  have hb : ∀ k : ℕ, |c| ≤ C * Real.exp (-(m * z 0)) * Real.exp (-(m * k)) := by
    intro k
    set z' : ISite := lineSite 0 z ((k : ℤ) * ((M : ℤ) + 1)) with hz'
    have hxz : x + z' = lineSite 0 (x + z) ((k : ℤ) * ((M : ℤ) + 1)) := by
      funext j
      simp only [hz', lineSite, Function.update_apply, Pi.add_apply]
      split_ifs with h
      · subst h; ring
      · rfl
    have hper := cov_lineSite_period hN M β x (x + z) 0 (k : ℤ)
    rw [← hxz, ← hc] at hper
    have hd := hC x z'
    rw [hper] at hd
    have hs1 : (z' 0).natAbs ≤ snorm z' :=
      Finset.le_sup (f := fun i : Fin 4 => (z' i).natAbs) (Finset.mem_univ 0)
    have hs2 : z 0 + (k : ℤ) ≤ ((snorm z' : ℕ) : ℤ) := by
      have e : z' 0 = z 0 + (k : ℤ) * ((M : ℤ) + 1) := lineSite_self 0 z _
      have hk : (k : ℤ) ≤ (k : ℤ) * ((M : ℤ) + 1) := by
        have : (0 : ℤ) ≤ (k : ℤ) * (M : ℤ) := by positivity
        linarith
      have := Int.le_natAbs (a := z' 0)
      omega
    have hs3 : (z 0 : ℝ) + k ≤ (snorm z' : ℝ) := by exact_mod_cast hs2
    have hC0 : 0 ≤ C := by
      by_contra hneg
      nlinarith [abs_nonneg c, Real.exp_pos (-(m * (snorm z' : ℝ)))]
    calc |c| ≤ C * Real.exp (-(m * (snorm z' : ℝ))) := hd
      _ ≤ C * Real.exp (-(m * ((z 0 : ℝ) + k))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC0
      _ = C * Real.exp (-(m * z 0)) * Real.exp (-(m * k)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have ht : Tendsto (fun k : ℕ => C * Real.exp (-(m * z 0)) * Real.exp (-(m * k))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hm)
    have := he.const_mul (C * Real.exp (-(m * z 0)))
    rw [mul_zero] at this
    exact this.congr fun k => by simp [Function.comp_apply]
  exact abs_nonpos_iff.mp (ge_of_tendsto' ht hb)

/-- **On a torus capture the local read locks exactly when the action correlation vanishes identically.**
DERIVED: `0` the threshold. -/
theorem locksOf_torusState_iff (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    Locks (torusState hN M β) ↔
      ∀ x z : ISite, stateCov (torusState hN M β) (siteEnergy x) (siteEnergy (x + z)) = 0 := by
  constructor
  · intro h
    obtain ⟨m, hm, hd⟩ := (locksOf_iff _ _).mp h
    exact cov_eq_zero_of_decaysAt_torus hN M β hm hd
  · intro h
    show 0 < measMassOf _ _
    rw [measMassOf_top_of_cov_zero h]
    exact ENNReal.zero_lt_top

/-- **The local read on a torus capture is all-or-nothing.** DERIVED: `0`. -/
theorem measMass_torusState_cases (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    measMass (torusState hN M β) = 0 ∨ measMass (torusState hN M β) = ⊤ := by
  by_cases h : Locks (torusState hN M β)
  · exact Or.inr (measMassOf_top_of_cov_zero ((locksOf_torusState_iff hN M β).mp h))
  · exact Or.inl ((measMassOf_eq_zero_iff _ _).mpr h)

/-! ## 5. The flux sectors at strong coupling, and the bridge -/

section Sectors

variable [NeZero N]

open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN sectors_of_defectWN defectW_le_of_sectorsN)

/-- DERIVED: `0`. -/
theorem strongBound_nonneg (n : ℕ) : 0 ≤ strongBound n := by
  unfold strongBound; positivity

/-- **The flux sectors are gapped at strong coupling**: the flux share and the zero-flux defect are bounded by
the strong defect bound at every step. DERIVED: `65536 = 2^{16}`; `4 + N⁶`, `N³/2`, `2` from
`sectors_of_defectWN`: `3` in `N^3 = |Z_N³|`, the spatial directions of a time slice, and `6 = 2 · 3` from
the square `(N^3 δ/2)^2`. -/
theorem sectors_strong {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (hδ : (4 + (N : ℝ) ^ 6) * (β * strongBound n) ≤ 2) (i : Fin 4) :
    fluxShareN N β n i ≤ (N : ℝ) ^ 3 * (β * strongBound n) / 2 ∧
      trivialDefectN N β n i ≤ 2 * (β * strongBound n) :=
  sectors_of_defectWN hβ0 hn he (mul_nonneg hβ0 (strongBound_nonneg n)) hδ
    ((le_abs_self _).trans (MassGap.StrongFiniteSize.abs_defectW_strong_le (NeZero.ne N) (by omega) hβ0 hβ)) i

omit [NeZero N] in
/-- **The flux bound falls to `0` with the side.** DERIVED: `3`, `2` from `sectors_strong`. -/
theorem tendsto_fluxBound (β : ℝ) :
    Tendsto (fun n : ℕ => (N : ℝ) ^ 3 * (β * strongBound n) / 2) atTop (𝓝 0) := by
  have h := (MassGap.StrongFiniteSize.tendsto_strongBound.const_mul β).const_mul ((N : ℝ) ^ 3)
  rw [mul_zero, mul_zero] at h
  simpa using h.div_const 2

omit [NeZero N] in
/-- **The condition of `sectors_strong` holds at every large side.** DERIVED: `2`, `4 + N⁶`; `6 = 2 · 3`
as in `sectors_strong`. -/
theorem eventually_sector_condition (β : ℝ) :
    ∀ᶠ n : ℕ in atTop, (4 + (N : ℝ) ^ 6) * (β * strongBound n) ≤ 2 := by
  have h := (MassGap.StrongFiniteSize.tendsto_strongBound.const_mul β).const_mul (4 + (N : ℝ) ^ 6)
  rw [mul_zero, mul_zero] at h
  exact (tendsto_order.mp h).2 2 (by norm_num) |>.mono fun _ hn => hn.le

/-- **Consistency at strong coupling**: the local read locks, both sector bounds hold, and the defect is
small. DERIVED: `65536 = 2^{16}`; `log 2` the contraction rate; `3` in `N^3` and `6 = 2 · 3` as in
`sectors_strong`. -/
theorem strong_consistency {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    ENNReal.ofReal (Real.log 2) ≤ measMass (periodicState (NeZero.ne N) β) ∧
      ∀ n : ℕ, 2 ≤ n → Even n → (4 + (N : ℝ) ^ 6) * (β * strongBound n) ≤ 2 →
        (∀ i : Fin 4, fluxShareN N β n i ≤ (N : ℝ) ^ 3 * (β * strongBound n) / 2 ∧
          trivialDefectN N β n i ≤ 2 * (β * strongBound n)) ∧
        |MassGap.ZoomSelfScale.defectW N β n| ≤ β * strongBound n := by
  refine ⟨measMass_strong (NeZero.ne N) (abs_le.mpr ⟨by linarith, hβ⟩), fun n hn he hδ => ⟨fun i =>
    sectors_strong hβ0 hβ hn he hδ i, ?_⟩⟩
  exact MassGap.StrongFiniteSize.abs_defectW_strong_le (NeZero.ne N) (by omega) hβ0 hβ

/-- **The sector seed in the measured unit** (assumed): eventually in `β`, the unit channel locks and some power
of two `n ≥ 2` with `n · m' ≤ C` has both sector clauses at every step. DERIVED: `2` the least side;
`1/80000` the threshold of `defectW_le_of_sectorsN`. -/
def SectorSeedMeasured (hN : N ≠ 0) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, 0 < measMassOf (periodicState hN β) tensorEnergy ∧
    ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C ∧
      ∀ i : Fin 4, fluxShareN N β n i ≤ 1 / 80000 ∧ trivialDefectN N β n i ≤ 1 / 80000

/-- **The sector seed in the measured unit, with the unit tracking the run, gives the run seed.**
DERIVED: `0`, `2`; `1/1000` the seed of `defectW_le_of_sectorsN`. -/
theorem runSeed_of_sectorSeedMeasured (hN : N ≠ 0) (hS : SectorSeedMeasured hN) (hU : UnitTracksRun hN) :
    WDeltaRun.RunSeed N := by
  obtain ⟨C, hC, hev⟩ := hS
  obtain ⟨c₁, hc₁, hUev⟩ := hU
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  refine ⟨C / c₁, div_pos hC hc₁, ?_⟩
  filter_upwards [hev, hUev, eventually_gt_atTop (0 : ℝ)] with β hSβ hu hβ
  obtain ⟨-, n, hp, hn2, hnm, hsec⟩ := hSβ
  have ha : 0 < AsymptoticScaling.aRun N β := AsymptoticScaling.aRun_pos hN1 hβ
  obtain ⟨b, hb⟩ := hp
  have hb0 : b ≠ 0 := by rintro rfl; rw [hb] at hn2; norm_num at hn2
  have he : Even n := by rw [hb]; exact Nat.even_pow.mpr ⟨even_two, hb0⟩
  refine ⟨n, ⟨b, hb⟩, hn2, ?_, defectW_le_of_sectorsN hβ.le hn2 he hsec⟩
  have h1 : ENNReal.ofReal ((n : ℝ) * (c₁ * AsymptoticScaling.aRun N β)) ≤ ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    exact le_trans (by gcongr) hnm
  have h2 := (ENNReal.ofReal_le_ofReal_iff hC.le).mp h1
  rw [le_div_iff₀ hc₁]
  linarith

end Sectors

end MassGap.SubstrateFluxRead

#print axioms MassGap.SubstrateFluxRead.lineSite_self
#print axioms MassGap.SubstrateFluxRead.measPeriod_eq
#print axioms MassGap.SubstrateFluxRead.measPeriod_eq_zero
#print axioms MassGap.SubstrateFluxRead.finMod_add_mul
#print axioms MassGap.SubstrateFluxRead.pullback_lineSite
#print axioms MassGap.SubstrateFluxRead.torusState_congr
#print axioms MassGap.SubstrateFluxRead.torusState_isPeriod
#print axioms MassGap.SubstrateFluxRead.measPeriod_torusState_le
#print axioms MassGap.SubstrateFluxRead.measPeriod_aperiodic
#print axioms MassGap.SubstrateFluxRead.continuous_polyHol
#print axioms MassGap.SubstrateFluxRead.ihol_centreSheet
#print axioms MassGap.SubstrateFluxRead.measMassOf_twoPhase_top
#print axioms MassGap.SubstrateFluxRead.card_hits_eq_one
#print axioms MassGap.SubstrateFluxRead.polyHol_centreSheet
#print axioms MassGap.SubstrateFluxRead.polyakov_centreSheet
#print axioms MassGap.SubstrateFluxRead.linkGap_centreSheet
#print axioms MassGap.SubstrateFluxRead.linkGap_centreSheet_short
#print axioms MassGap.SubstrateFluxRead.measPeriod_twoPhase_sheet
#print axioms MassGap.SubstrateFluxRead.measPeriod_sheetFamily
#print axioms MassGap.SubstrateFluxRead.measMass_sheetFamily
#print axioms MassGap.SubstrateFluxRead.measMassOf_tensor_sheetFamily
#print axioms MassGap.SubstrateFluxRead.fluxCov_sheetFamily
#print axioms MassGap.SubstrateFluxRead.fluxAdm_unitOne
#print axioms MassGap.SubstrateFluxRead.not_fluxLocksAlong_sheetFamily
#print axioms MassGap.SubstrateFluxRead.local_locks_flux_not
#print axioms MassGap.SubstrateFluxRead.fluxLocksAlong_pointSheet
#print axioms MassGap.SubstrateFluxRead.ishift_lineSite
#print axioms MassGap.SubstrateFluxRead.siteEnergy_eq_planes
#print axioms MassGap.SubstrateFluxRead.cov_lineSite_period
#print axioms MassGap.SubstrateFluxRead.cov_eq_zero_of_decaysAt_torus
#print axioms MassGap.SubstrateFluxRead.locksOf_torusState_iff
#print axioms MassGap.SubstrateFluxRead.measMass_torusState_cases
#print axioms MassGap.SubstrateFluxRead.sectors_strong
#print axioms MassGap.SubstrateFluxRead.tendsto_fluxBound
#print axioms MassGap.SubstrateFluxRead.eventually_sector_condition
#print axioms MassGap.SubstrateFluxRead.strong_consistency
#print axioms MassGap.SubstrateFluxRead.runSeed_of_sectorSeedMeasured
