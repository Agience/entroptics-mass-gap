import Mathlib
import MassGap.ObserverBlockReading
import MassGap.WDeltaRun

/-!
# MassGap.SubstrateDecode — the substrate decoded from a capture alone

The observer reads the substrate the way a receiver reads a capture: it is handed a state and nothing else, and
every coordinate it reports is measured from that state. A scale the decode must be told is a scale it failed
to measure. This module defines a decode of that kind, proves that it locks at strong coupling, exhibits a capture
on which it does not lock, states the one open input in measured quantities, and names the bridge from that input
to the run seed. Declarations are in the namespace `MassGap.SubstrateDecode`.

## 1. The decode (defined)

* The capture is a state `ν : State (Cfg N)` (a state on the continuous functions of infinite-volume `SU(N)`
  link configurations; `periodicState hN β` is one). On a torus capture the read is all-or-nothing
  (`SubstrateFluxRead.measMass_torusState_cases`): the decode is an infinite-volume read.
* **`siteEnergy x`**: the action density at site `x`, the mean of `wilsonDensity` of the six plaquette holonomies
  based at `x` (`ObserverBlockReading.blockEnergy 1 · x`, `siteEnergy_apply`). Gauge invariant, in `[0, 2]`,
  pinned: no coupling, spacing, block side or normalization constant enters it. **`tensorEnergy x`**: the
  `(0, 1)`-plaquette density minus the `(2, 3)`-plaquette density at `x`, a second pinned reading in a different channel (it changes sign under the exchange of the two planes; under
the rotations about a separation axis it is not a pure tensor (with axis 0 as time, `E₁² − B₁²` contains the
scalar `(E² − B²)/3`), so its rate is expected to be the scalar rate (argued)).
* **`DecaysAt ν E m`**: there is `C` with `|Cov_ν(E_x, E_{x+z})| ≤ C e^{−m ‖z‖∞}` for every position `x` and every
  separation `z ∈ ℤ⁴`. The read sweeps every position and every separation; no axis and no base point is chosen.
* **`measMassOf ν E = ⨆ {m ≥ 0 : DecaysAt ν E m} m`** in `[0, ∞]`; **`measMass ν = measMassOf ν siteEnergy`**.
  This is the decay rate of the reading's connected correlation, read from `ν` alone. A correlation that vanishes
  identically reads `∞` (`measMassOf_point`: a point capture has every rate), a correlation that does not decay
  reads `0`. Argued: for a reading bounded uniformly in `x` (both pinned readings are), with `log 0 = −∞` it is `liminf_{‖z‖∞→∞} inf_x (−log |Cov_ν(E_x, E_{x+z})|) / ‖z‖∞`, the
  standard identity between the exponential rate and the best constant-free bound.
* **`Locks ν := 0 < measMass ν`** (`LocksOf ν E` for a general reading): the detection verdict, "the correlation decays at some positive rate (a point capture, rate `∞`, also locks)". `locksOf_iff`: `LocksOf ν E ↔ ∃ m > 0, DecaysAt ν E m`.
  `measMassOf_eq_zero_iff`: the mass reads `0` exactly when the read does not lock.

## 2. The read detects, and is not always true (proved)

* **`decaysAt_strong`**, **`measMass_strong`**, **`locks_strong`**: at `|β| ≤ 2^{-16}`, every `N ≠ 0`,
  `|Cov(E_x, E_{x+z})| ≤ 5184 · 2^{−‖z‖∞}` in `periodicState hN β`, so `measMass (periodicState hN β) ≥ log 2` and
  the read locks. `5184 = strongQ 1 0 = 16 · 3⁴ · 4` (`strongQ_one_zero`), from
  `ObserverBlockReading.blockCov_strong` at the identity flow, block side `1`, range `0`.
* **`twoPhase A B`**: the capture that reads `A` or `B` with weight `1/2` each; `stateCov_twoPhase`:
  `Cov(F, H) = (F A − F B)(H A − H B)/4`. `measMassOf_point`: `twoPhase U U` (a point capture) has
  `measMassOf = ∞` for every reading, so zero covariance reads infinite mass: a point capture locks trivially (`Locks` holds at `⊤`), and it is
`LockPersistsAlong` that excludes it (`not_lockPersistsAlong_point`).
* **`piFlux`** (`N = 2`): the link `(1, y)` is `−1` when `y₀` is even, every other link is `1`. `ihol_piFlux`: every
  `(0, 1)`-plaquette has holonomy `−1` and every other plaquette `1`, so `siteEnergy_piFlux`: the action density is
  `1/3` at every site; the flat configuration reads `0`.
* **`twoPhase_not_decaysAt`**, **`measMass_twoPhase`**, **`not_locks_twoPhase`**: in the two-phase capture
  `twoPhase 1 piFlux` the connected action correlation is `1/36` at every position and separation, no rate
  `m > 0` holds, `measMass = 0`, and the read does not lock. The degenerate capture that defeats a detector is the
  mixture of two phases (long-range order), not a point capture (`measMassOf_point`; a product capture has finite-range correlation and also reads `∞`,
argued).

## 3. The open input, in measured units (defined; implications proved; tests argued)

* **`LockPersistsAlong ν E E'`** for a family `ν : ℝ → State (Cfg N)`: there is `c > 0` such that the unit
  channel's mass `measMassOf (ν β) E'` tends to `0` (the observer's unit length `1/m'` grows without bound in
  lattice units: the family reaches the continuum as read by the observer), and eventually in `β`,
  `0 < measMassOf (ν β) E'` and `c · measMassOf (ν β) E' ≤ measMassOf (ν β) E`. The mass of `E` is bounded below
  in the unit read from `E'` in the same capture. **`LockPersists hN`**: the instance on the coupling family
  `periodicState hN`, gap channel `siteEnergy`, unit channel `tensorEnergy`. The coupling `β` indexes the family;
  the decode never reads it, and the supplied spacing `aRun` does not appear.
* Proved: `locks_of_lockPersistsAlong`: the Prop gives the lock `LocksOf (ν β) E` eventually.
  `lockPersistsAlong_self_iff`: with the unit channel equal to the gap channel the Prop collapses to
  "eventually locks, and the mass tends to `0`"; the ratio has content only when the unit is read from a
  different channel. `not_lockPersistsAlong_twoPhase`: the constant two-phase family fails it for every unit
  channel. `not_lockPersistsAlong_point`: a constant point family fails it (its unit mass is `∞`, which does not
  tend to `0`). So the Prop is not met by either degenerate capture.
* Tests (argued).
  1. Free field. For the massive free scalar at lattice mass `μ = M a`, the two local quadratic channels
     (`:φ²:` and a traceless `:∂_μφ ∂_νφ:` combination) both decay at the two-particle threshold `2μ` (up to power
     prefactors), so `m'/m → 1`, `c = 1/2` works, and `m' → 0` as `a → 0`: the Prop holds. For the massless free field both channels decay by a power law (`:φ²:` like `‖z‖^{−4}`), so `m = m' = 0` at
every coupling and `0 < m'` fails. The test
     discriminates.
  2. A constant fixed before a growing quantity. `c` is fixed before `β` and is a ratio of two rates, so it is
     dimensionless; no constant of the Prop is in lattice units. The strong-coupling lock has `m ≥ log 2` fixed in
     lattice units; it gives no instance of the Prop: the Prop is read along `β → ∞`, and the strong-coupling bound holds only at
`|β| ≤ 2^{-16}` and bounds the action density, not the tensor channel.
  3. Restatement against reduction. The Prop is a restatement: it is the mass gap of the action-density channel,
     in units of the tensor channel's mass, written in measured coordinates. It reduces nothing. Its content is the
     uniformity of `c` in `β` together with the existence of a scaling window (`m' → 0` with `m' > 0`). It reads two
     local channels only: a massless excitation in a channel neither reading couples to (in particular a flux
     sector on a torus) is not seen.
  4. Degenerate case. Unit equal to the reading: `lockPersistsAlong_self_iff`. Point and two-phase captures:
     proved to fail.

## 4. What the Prop gives, and the bridge (proved where named, assumed otherwise)

* `LockPersists` gives the measured lock at every large coupling (`locks_of_lockPersistsAlong`) and the ratio
  bound. It does not by itself give `WDeltaRun.RunSeed` or `ObserverRunSeed.ObsRunSeedW`: both are written in the
  supplied spacing (`n · aRun N β ≤ C`), `RunSeed` in the torus free-energy defect `defectW` and `ObsRunSeedW`
  in its `β`-derivative read through `boxRead` (equivalent, `ObserverRunSeed.obsRunSeedW_iff`). Two inputs separate them.
* **`UnitTracksRun hN`** (assumed): `∃ c₁ > 0`, eventually `c₁ · aRun N β ≤ measMassOf (periodicState hN β)
  tensorEnergy`. The measured unit tracks the supplied spacing (asymptotic scaling of one measured mass). This is
  where the supplied spacing re-enters, and it enters only to meet a target written in it.
* **`DecayGivesSeed hN`** (assumed): a scalar-channel rate `≥ κ · aRun` eventually gives `RunSeed N`. It needs a
  finite-volume statement from an infinite-volume decay, which no module builds (`ObserverOneInput`).
  Argued: no proof of it can use local decay alone. In the deconfined phase of 4D `Z₂` local correlations decay
  at a rate bounded below while the odd electric-flux states on the torus are nearly degenerate with the vacuum
  (`WDeltaRun` docstring), and `defectW` reads them, so a local lock does not give the seed by a general route.
  For `SU(N)` the Prop holds whenever `RunSeed N` does (its conclusion), so the bridge reduces nothing until it is proved from content the local reading lacks: the centre/flux sector
(`SubstrateFluxRead`: the lock verdict does not give a flux lock, `local_locks_flux_not`; on a torus capture the
local read is all-or-nothing, `measMass_torusState_cases`; the seed in measured side units is
`SectorSeedMeasured`).
* **`runSeed_of_lockPersists`** (proved): `LockPersists hN → UnitTracksRun hN → DecayGivesSeed hN → RunSeed N`.
* The Clay gap clause in clustering form is `FlowCapstone.FlowClusterAbs`, written in `dySpacing N m · n`; the
  bridge to it needs the same unit conversion, every margin monomial instead of one channel, and the continuum
  limit along `kernF` (`ObserverBlockReading` §5). Not built.

## 5. Parameters

| argument | where | status |
|---|---|---|
| `ν` (the capture) | `DecaysAt`, `measMassOf`, `measMass`, `Locks` | the input; everything is read from it |
| `x`, `z` (position, separation) | `DecaysAt` | swept over all of `ℤ⁴`; not supplied |
| `C`, `m` (prefactor, rate) | `DecaysAt`, `measMassOf` | measured: existential and supremum inside the read |
| `E`, `E'` (the readings) | `measMassOf`, `LockPersistsAlong` | general in `measMassOf`; pinned (`siteEnergy`, `tensorEnergy`) in `measMass` and `LockPersists`; no parameter |
| `‖·‖∞` (the separation norm) | `DecaysAt` | chosen: the lattice's own sup norm |
| `N` (colour count) | the type `State (Cfg N)` | shared with the substrate; not measured |
| `β` (coupling) | `periodicState hN β`, the family index | shared, in the substrate only; the decode never reads it |
| `c` (ratio) | `LockPersistsAlong` | measured: existential, a ratio of two measured rates |
| `aRun`, `c₁`, `κ` | `UnitTracksRun`, `DecayGivesSeed` only | supplied spacing; appears only in the bridge to a target written in it |

No block side, window constant, flow step, renormalization constant or budget is an argument of the decode. `N` is
not measured: it is the type of the capture. A read of the centre `Z_N` from the law of the Polyakov trace is sketched in `SubstrateFluxRead` §7; it needs
Haar moments of `tr U`, which no module proves.

DERIVED (module-wide): `0` the origin and signs; `1` the block side of a single site and the identity; `2` the
colour count of the two-phase witness, the parity of `piFlux` and the weight `1/2`; `4` the dimension and the
`4` of `(F A − F B)(H A − H B)/4`; `6` the planes; `1/3 = 2/6` the action density of `piFlux`;
`1/36 = (1/3)²/4`; `36` its reciprocal; `65536 = 2^{16}` the strong-coupling threshold of `StrongKernelNear`;
`log 2` its contraction rate; `5184 = 16 · 3⁴ · 4` `strongQ 1 0`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SubstrateDecode

open Filter Topology
open scoped ENNReal NNReal
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.FocusZoom (stateCov)
open MassGap.SUN (SU)
open MassGap.ContinuumSchwinger (Cfg)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.ObserverEnergyMoments (plaqField negOne negOne_inv)
open MassGap.StrongFiniteSize (snorm)
open MassGap.PeriodicState (periodicState)
open MassGap.ObserverBlockReading (planes blockSites blockPlaqs blockEnergy strongQ plaqField_apply
  blockEnergy_flat)

/-! ## 1. The reading and the decode -/

variable {N : ℕ}

/-- **The action density at a site**: the mean plaquette holonomy-class reading over the six plaquettes based at
`x`. DERIVED: `1` the block side of a single site. -/
def siteEnergy (x : ISite) : C(Cfg N, ℝ) :=
  ((blockPlaqs 1 x).card : ℝ)⁻¹ • ∑ q ∈ blockPlaqs 1 x, (plaqField (N := N) q).1

/-- DERIVED: `1` the block side of a single site. -/
theorem siteEnergy_apply (x : ISite) (U : Cfg N) : siteEnergy x U = blockEnergy 1 U x := by
  simp only [siteEnergy, blockEnergy, ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    smul_eq_mul]

/-- **The tensor reading**: the `(0, 1)`-plaquette density minus the `(2, 3)`-plaquette density at `x`.
DERIVED: `0`, `1`, `2`, `3` the two planes. -/
def tensorEnergy (x : ISite) : C(Cfg N, ℝ) :=
  (plaqField (N := N) (((0 : Fin 4), (1 : Fin 4)), x)).1 - (plaqField (N := N) (((2 : Fin 4), (3 : Fin 4)), x)).1

/-- **Decay at rate `m`**: one prefactor bounds the connected correlation of the reading at every position and
separation by `e^{−m ‖z‖∞}`. DERIVED: no numeral. -/
def DecaysAt (ν : State (Cfg N)) (E : ISite → C(Cfg N, ℝ)) (m : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x z : ISite, |stateCov ν (E x) (E (x + z))| ≤ C * Real.exp (-(m * snorm z))

/-- **The measured mass of a reading**: the supremum of the rates at which its correlation decays, in `[0, ∞]`.
DERIVED: no numeral. -/
def measMassOf (ν : State (Cfg N)) (E : ISite → C(Cfg N, ℝ)) : ℝ≥0∞ :=
  ⨆ (m : ℝ≥0) (_ : DecaysAt ν E m), (m : ℝ≥0∞)

/-- **The measured mass**: that of the action density. DERIVED: no numeral. -/
def measMass (ν : State (Cfg N)) : ℝ≥0∞ := measMassOf ν siteEnergy

/-- **The detection verdict for a reading.** DERIVED: `0` the threshold of detection. -/
def LocksOf (ν : State (Cfg N)) (E : ISite → C(Cfg N, ℝ)) : Prop := 0 < measMassOf ν E

/-- **The detection verdict**: the read locks at a finite scale. DERIVED: `0` the threshold of detection. -/
def Locks (ν : State (Cfg N)) : Prop := 0 < measMass ν

/-- A decay rate is a lower bound of the measured mass. DERIVED: `0` the sign of a rate. -/
theorem le_measMassOf {ν : State (Cfg N)} {E : ISite → C(Cfg N, ℝ)} {m : ℝ} (hm : 0 ≤ m)
    (h : DecaysAt ν E m) : ENNReal.ofReal m ≤ measMassOf ν E := by
  rw [ENNReal.ofReal_eq_coe_nnreal hm]
  exact le_iSup₂ (f := fun (r : ℝ≥0) (_ : DecaysAt ν E r) => (r : ℝ≥0∞)) ⟨m, hm⟩ h

/-- **The read locks exactly when some positive rate holds.** DERIVED: `0` the threshold. -/
theorem locksOf_iff (ν : State (Cfg N)) (E : ISite → C(Cfg N, ℝ)) :
    LocksOf ν E ↔ ∃ m : ℝ, 0 < m ∧ DecaysAt ν E m := by
  constructor
  · intro h
    unfold LocksOf measMassOf at h
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp h
    obtain ⟨hd, hpos⟩ := lt_iSup_iff.mp hr
    exact ⟨r, NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hpos), hd⟩
  · rintro ⟨m, hm, hd⟩
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hm) (le_measMassOf hm.le hd)

/-- **The mass reads `0` exactly when the read does not lock.** DERIVED: `0` the threshold. -/
theorem measMassOf_eq_zero_iff (ν : State (Cfg N)) (E : ISite → C(Cfg N, ℝ)) :
    measMassOf ν E = 0 ↔ ¬ LocksOf ν E := by
  unfold LocksOf
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h; exact le_antisymm (not_lt.mp h) bot_le

/-- **A vanishing correlation reads infinite mass.** DERIVED: `0` the vanishing correlation. -/
theorem measMassOf_top_of_cov_zero {ν : State (Cfg N)} {E : ISite → C(Cfg N, ℝ)}
    (h : ∀ x z : ISite, stateCov ν (E x) (E (x + z)) = 0) : measMassOf ν E = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  have hd : DecaysAt ν E r := ⟨0, fun x z => by rw [h, abs_zero, zero_mul]⟩
  simpa using le_measMassOf r.2 hd

/-! ## 2. The strong-coupling lock -/

/-- DERIVED: `1/2` and `log 2` the contraction rate. -/
theorem half_pow_eq_exp (n : ℕ) : (1 / 2 : ℝ) ^ n = Real.exp (-(Real.log 2 * n)) := by
  rw [show -(Real.log 2 * n) = (n : ℝ) * (-Real.log 2) by ring, Real.exp_nat_mul, Real.exp_neg,
    Real.exp_log two_pos]
  norm_num

/-- `strongQ 1 0 = 5184`. DERIVED: `5184 = 16 · 3⁴ · 4`. -/
theorem strongQ_one_zero : strongQ 1 0 = 5184 := by
  unfold strongQ; norm_num

/-- **The action density decays at rate `log 2` at strong coupling**, with prefactor `strongQ 1 0 = 5184`.
DERIVED: `65536 = 2^{16}`; `log 2` the contraction rate; `1` the block side; `0` the range and the step. -/
theorem decaysAt_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) :
    DecaysAt (periodicState hN β) siteEnergy (Real.log 2) := by
  refine ⟨strongQ 1 0, fun x z => ?_⟩
  have h := ObserverBlockReading.blockCov_strong hN hβ (ConfFlow.identity N) 0 1 0 le_rfl x (x + z)
    (f := id) (h := id) zero_le_one zero_le_one (fun a b => by simp) (fun a b => by simp)
    (siteEnergy x) (siteEnergy (x + z)) (fun U => siteEnergy_apply x U) (fun U => siteEnergy_apply (x + z) U)
  rw [add_sub_cancel_left, pow_one, mul_one, mul_one, half_pow_eq_exp] at h
  exact h

/-- **The measured mass is at least `log 2` at strong coupling.** DERIVED: `65536 = 2^{16}`; `log 2` the
contraction rate. -/
theorem measMass_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) :
    ENNReal.ofReal (Real.log 2) ≤ measMass (periodicState hN β) :=
  le_measMassOf (Real.log_nonneg one_le_two) (decaysAt_strong hN hβ)

/-- **The read locks at strong coupling.** DERIVED: `65536 = 2^{16}`; `log 2` the contraction rate. -/
theorem locks_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) : Locks (periodicState hN β) :=
  (locksOf_iff _ _).mpr ⟨Real.log 2, Real.log_pos one_lt_two, decaysAt_strong hN hβ⟩

/-! ## 3. Captures on which the read does not lock -/

section TwoPhase

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The two-phase capture**: `A` and `B` with weight `1/2` each. DERIVED: `2` the two phases; `0` the sign. -/
def twoPhase (A B : X) : State X where
  toFun f := (f A + f B) / 2
  map_add' f g := by simp only [ContinuousMap.add_apply]; ring
  map_smul' c f := by simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring
  nonneg' f hf := div_nonneg (add_nonneg (hf A) (hf B)) zero_le_two
  one' := by simp only [ContinuousMap.one_apply]; norm_num

/-- DERIVED: `2` the two phases. -/
theorem twoPhase_apply (A B : X) (f : C(X, ℝ)) : twoPhase A B f = (f A + f B) / 2 := rfl

/-- **The two-phase covariance.** DERIVED: `4 = 2 · 2` the two weights. -/
theorem stateCov_twoPhase (A B : X) (F H : C(X, ℝ)) :
    stateCov (twoPhase A B) F H = (F A - F B) * (H A - H B) / 4 := by
  unfold stateCov
  rw [twoPhase_apply, twoPhase_apply, twoPhase_apply]
  simp only [ContinuousMap.mul_apply]
  ring

end TwoPhase

/-- **A point capture has infinite mass in every reading.** DERIVED: `0` the vanishing correlation. -/
theorem measMassOf_point (U : Cfg N) (E : ISite → C(Cfg N, ℝ)) : measMassOf (twoPhase U U) E = ⊤ :=
  measMassOf_top_of_cov_zero fun x z => by rw [stateCov_twoPhase, sub_self, zero_mul, zero_div]

/-- **The `π`-flux configuration**: the link `(1, y)` is `−1` when `y₀` is even, every other link is `1`.
DERIVED: `1` the direction; `0` the parity axis; `2` the parity. -/
def piFlux : Cfg 2 := fun l => if l.1 = 1 ∧ l.2 0 % 2 = 0 then negOne else 1

/-- The plaquette holonomy as a product of four links. DERIVED: no numeral. -/
theorem ihol_eq {G : Type} [Group G] (q : IPlaq) (U : IConf G) :
    ihol q U = U (q.1.1, q.2) * U (q.1.2, ishift q.1.1 q.2) * (U (q.1.1, ishift q.1.2 q.2))⁻¹ *
      (U (q.1.2, q.2))⁻¹ := by
  simp [ihol, MassGap.WilsonLattice.wilsonHol, ibd, mul_assoc]

/-- DERIVED: `0` the axis; `1` the step. -/
theorem ishift_zero_apply (x : ISite) : ishift 0 x 0 = x 0 + 1 := by
  simp [ishift]

/-- DERIVED: `0` the axis. -/
theorem ishift_apply_zero {μ : Fin 4} (h : μ ≠ 0) (x : ISite) : ishift μ x 0 = x 0 := by
  unfold ishift
  rw [Function.update_apply, if_neg (Ne.symm h)]

/-- **Every `(0, 1)`-plaquette of `piFlux` has holonomy `−1`, every other plaquette `1`.**
DERIVED: `0`, `1`, `2`, `3` the planes; `2` the parity. -/
theorem ihol_piFlux (p : Fin 4 × Fin 4) (hp : p ∈ planes) (x : ISite) :
    ihol (p, x) piFlux = if p = ((0 : Fin 4), (1 : Fin 4)) then negOne else 1 := by
  obtain ⟨a, b⟩ := p
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have hnn : negOne * negOne = 1 := by
    have h := mul_inv_cancel negOne
    rwa [negOne_inv] at h
  by_cases hx : x 0 % 2 = 0
  · have hx' : ¬ ((x 0 + 1) % 2 = 0) := by omega
    fin_cases a <;> fin_cases b <;> simp [planes] at hp <;>
      simp [ihol_eq, piFlux, ishift_zero_apply, ishift_apply_zero h10, ishift_apply_zero h20,
        ishift_apply_zero h30, hx, hx', negOne_inv, hnn]
  · have hx' : (x 0 + 1) % 2 = 0 := by omega
    fin_cases a <;> fin_cases b <;> simp [planes] at hp <;>
      simp [ihol_eq, piFlux, ishift_zero_apply, ishift_apply_zero h10, ishift_apply_zero h20,
        ishift_apply_zero h30, hx, hx']

/-- DERIVED: `2` the density of `−1`. -/
theorem wilsonDensity_negOne : MassGap.WilsonAction.wilsonDensity (N := 2) negOne = 2 := by
  unfold MassGap.WilsonAction.wilsonDensity
  have : ((negOne : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl
  rw [this, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin, Complex.neg_re, Complex.natCast_re]
  norm_num

/-- The single-site block is the site. DERIVED: `1` the side. -/
theorem blockSites_one (x : ISite) : blockSites 1 x = {x} := by
  ext y
  simp only [blockSites, Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_singleton, Nat.cast_one, one_mul]
  constructor
  · intro h; funext i; have := h i; omega
  · rintro rfl i; omega

/-- **The action density of `piFlux` is `1/3` at every site.** DERIVED: `1/3 = 2/6`; `6` the planes. -/
theorem siteEnergy_piFlux (x : ISite) : blockEnergy 1 piFlux x = 1 / 3 := by
  unfold blockEnergy blockPlaqs
  rw [blockSites_one, Finset.card_product, Finset.card_singleton, Finset.sum_product]
  have hcard : planes.card = 6 := by decide
  rw [hcard]
  have hs : ∑ p ∈ planes, ∑ y ∈ ({x} : Finset ISite), (plaqField (N := 2) (p, y)).1 piFlux
      = ∑ p ∈ planes, if p = ((0 : Fin 4), (1 : Fin 4)) then (2 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_singleton, plaqField_apply, ihol_piFlux p hp x]
    split_ifs
    · exact wilsonDensity_negOne
    · exact MassGap.WilsonAction.wilsonDensity_one two_ne_zero
  rw [hs, Finset.sum_ite_eq' planes ((0 : Fin 4), (1 : Fin 4)), if_pos (by decide)]
  norm_num

/-- **No positive rate holds in the two-phase capture.** The connected action correlation is `1/36` at every
position and separation. DERIVED: `1/36 = (1/3)²/4`; `36` its reciprocal; `1` the ceiling step; `2` the colour
count. -/
theorem twoPhase_not_decaysAt {m : ℝ} (hm : 0 < m) :
    ¬ DecaysAt (twoPhase (fun _ => (1 : SU 2)) piFlux) siteEnergy m := by
  rintro ⟨C, hC⟩
  have hcov : ∀ x z : ISite,
      stateCov (twoPhase (fun _ => (1 : SU 2)) piFlux) (siteEnergy x) (siteEnergy (x + z)) = 1 / 36 := by
    intro x z
    rw [stateCov_twoPhase, siteEnergy_apply, siteEnergy_apply, siteEnergy_apply, siteEnergy_apply,
      blockEnergy_flat two_ne_zero, blockEnergy_flat two_ne_zero, siteEnergy_piFlux, siteEnergy_piFlux]
    norm_num
  set d : ℕ := ⌈36 * C / m⌉₊ + 1 with hd
  have h := hC 0 (fun _ => (d : ℤ))
  rw [hcov, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 36)] at h
  have h1 : ((fun _ : Fin 4 => (d : ℤ)) 0).natAbs ≤ snorm (fun _ : Fin 4 => (d : ℤ)) :=
    Finset.le_sup (f := fun i : Fin 4 => ((fun _ : Fin 4 => (d : ℤ)) i).natAbs) (Finset.mem_univ 0)
  have h2 : d ≤ snorm (fun _ : Fin 4 => (d : ℤ)) := by simpa using h1
  have hsn : (d : ℝ) ≤ (snorm (fun _ : Fin 4 => (d : ℤ)) : ℝ) := by exact_mod_cast h2
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hneg' : C < 0 := not_le.mp hneg
    nlinarith [Real.exp_pos (-(m * (snorm (fun _ : Fin 4 => (d : ℤ)) : ℝ)))]
  have hexp : Real.exp (-(m * (snorm (fun _ : Fin 4 => (d : ℤ)) : ℝ))) ≤ Real.exp (-(m * d)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hsn hm.le))
  have h3 : 1 / 36 ≤ C * Real.exp (-(m * d)) := h.trans (mul_le_mul_of_nonneg_left hexp hC0)
  have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (m * d)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h4
  have h5 := Real.add_one_le_exp (m * d)
  have h6 : 36 * C / m < d := by
    rw [hd]; push_cast
    linarith [Nat.le_ceil (36 * C / m)]
  have h7 : 36 * C < m * d := by
    rw [div_lt_iff₀ hm] at h6; linarith
  nlinarith

/-- **The two-phase capture has measured mass `0`.** DERIVED: `2` the colour count. -/
theorem measMass_twoPhase : measMass (twoPhase (fun _ => (1 : SU 2)) piFlux) = 0 := by
  unfold measMass
  rw [measMassOf_eq_zero_iff, locksOf_iff]
  rintro ⟨m, hm, hd⟩
  exact twoPhase_not_decaysAt hm hd

/-- **The read does not lock on the two-phase capture.** DERIVED: `2` the colour count. -/
theorem not_locks_twoPhase : ¬ Locks (twoPhase (fun _ => (1 : SU 2)) piFlux) := by
  unfold Locks
  rw [measMass_twoPhase]
  exact lt_irrefl 0

/-! ## 4. The open input in measured units -/

/-- **The lock persists in measured units** along a family of captures: the unit channel's mass tends to `0`, is
eventually positive, and bounds the gap channel's mass from below by a fixed ratio `c`.
DERIVED: `0` the limit of the unit mass and the threshold. -/
def LockPersistsAlong (ν : ℝ → State (Cfg N)) (E E' : ISite → C(Cfg N, ℝ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun β => measMassOf (ν β) E') atTop (𝓝 0) ∧
    ∀ᶠ β in atTop, 0 < measMassOf (ν β) E' ∧ ENNReal.ofReal c * measMassOf (ν β) E' ≤ measMassOf (ν β) E

/-- **The open input**: along the coupling family, the action-density mass stays bounded below in the unit read
from the tensor channel of the same capture. DERIVED: no numeral. -/
def LockPersists (hN : N ≠ 0) : Prop :=
  LockPersistsAlong (periodicState hN) siteEnergy tensorEnergy

/-- **The Prop gives the lock eventually.** DERIVED: `0` the threshold. -/
theorem locks_of_lockPersistsAlong {ν : ℝ → State (Cfg N)} {E E' : ISite → C(Cfg N, ℝ)}
    (h : LockPersistsAlong ν E E') : ∀ᶠ β in atTop, LocksOf (ν β) E := by
  obtain ⟨c, hc, -, hev⟩ := h
  exact hev.mono fun β hβ =>
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc).ne' hβ.1.ne') hβ.2

/-- **The lock persists on the coupling family, read at every large coupling.** DERIVED: no numeral. -/
theorem locks_of_lockPersists (hN : N ≠ 0) (h : LockPersists hN) :
    ∀ᶠ β in atTop, Locks (periodicState hN β) :=
  locks_of_lockPersistsAlong h

/-- **With the unit read from the same channel the ratio carries nothing**: the Prop is the eventual lock with a
mass tending to `0`. DERIVED: `1` the ratio of a channel to itself. -/
theorem lockPersistsAlong_self_iff (ν : ℝ → State (Cfg N)) (E : ISite → C(Cfg N, ℝ)) :
    LockPersistsAlong ν E E ↔
      Tendsto (fun β => measMassOf (ν β) E) atTop (𝓝 0) ∧ ∀ᶠ β in atTop, 0 < measMassOf (ν β) E := by
  constructor
  · rintro ⟨c, -, ht, hev⟩
    exact ⟨ht, hev.mono fun _ hβ => hβ.1⟩
  · rintro ⟨ht, hev⟩
    refine ⟨1, one_pos, ht, hev.mono fun _ hβ => ⟨hβ, ?_⟩⟩
    rw [ENNReal.ofReal_one, one_mul]

/-- **The constant two-phase family fails the Prop for every unit channel.** DERIVED: `2` the colour count. -/
theorem not_lockPersistsAlong_twoPhase (E' : ISite → C(Cfg 2, ℝ)) :
    ¬ LockPersistsAlong (fun _ => twoPhase (fun _ => (1 : SU 2)) piFlux) siteEnergy E' := by
  intro h
  obtain ⟨β, hβ⟩ := (locks_of_lockPersistsAlong h).exists
  exact not_locks_twoPhase hβ

/-- **A constant point family fails the Prop**: its unit mass is `∞` and does not tend to `0`.
DERIVED: `0` the limit. -/
theorem not_lockPersistsAlong_point (U : Cfg N) (E E' : ISite → C(Cfg N, ℝ)) :
    ¬ LockPersistsAlong (fun _ => twoPhase U U) E E' := by
  rintro ⟨c, -, ht, -⟩
  have hf : (fun β : ℝ => measMassOf ((fun _ : ℝ => twoPhase U U) β) E') = fun _ => ⊤ :=
    funext fun _ => measMassOf_point U E'
  rw [hf, tendsto_const_nhds_iff] at ht
  exact ENNReal.top_ne_zero ht

/-! ## 5. The bridge to the run seed -/

/-- **The measured unit tracks the supplied spacing** (assumed): the tensor channel's mass is at least
`c₁ · aRun N β` eventually. DERIVED: `0` the sign of `c₁`. -/
def UnitTracksRun (hN : N ≠ 0) : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ β in atTop,
    ENNReal.ofReal (c₁ * AsymptoticScaling.aRun N β) ≤ measMassOf (periodicState hN β) tensorEnergy

/-- **A scalar-channel rate in run units gives the seed** (assumed): the finite-volume bridge.
DERIVED: `0` the sign of `κ`. -/
def DecayGivesSeed (hN : N ≠ 0) : Prop :=
  (∃ κ : ℝ, 0 < κ ∧ ∀ᶠ β in atTop,
    ENNReal.ofReal (κ * AsymptoticScaling.aRun N β) ≤ measMass (periodicState hN β)) → WDeltaRun.RunSeed N

/-- **The open input with the two bridges gives the run seed.** DERIVED: no numeral. -/
theorem runSeed_of_lockPersists (hN : N ≠ 0) (hL : LockPersists hN) (hU : UnitTracksRun hN)
    (hB : DecayGivesSeed hN) : WDeltaRun.RunSeed N := by
  obtain ⟨c, hc, -, hev⟩ := hL
  obtain ⟨c₁, hc₁, hU⟩ := hU
  refine hB ⟨c * c₁, mul_pos hc hc₁, ?_⟩
  filter_upwards [hev, hU] with β hβ hu
  calc ENNReal.ofReal (c * c₁ * AsymptoticScaling.aRun N β)
        = ENNReal.ofReal c * ENNReal.ofReal (c₁ * AsymptoticScaling.aRun N β) := by
          rw [mul_assoc, ENNReal.ofReal_mul hc.le]
    _ ≤ ENNReal.ofReal c * measMassOf (periodicState hN β) tensorEnergy := by gcongr
    _ ≤ measMass (periodicState hN β) := hβ.2

end MassGap.SubstrateDecode

#print axioms MassGap.SubstrateDecode.siteEnergy_apply
#print axioms MassGap.SubstrateDecode.le_measMassOf
#print axioms MassGap.SubstrateDecode.locksOf_iff
#print axioms MassGap.SubstrateDecode.measMassOf_eq_zero_iff
#print axioms MassGap.SubstrateDecode.measMassOf_top_of_cov_zero
#print axioms MassGap.SubstrateDecode.half_pow_eq_exp
#print axioms MassGap.SubstrateDecode.strongQ_one_zero
#print axioms MassGap.SubstrateDecode.decaysAt_strong
#print axioms MassGap.SubstrateDecode.measMass_strong
#print axioms MassGap.SubstrateDecode.locks_strong
#print axioms MassGap.SubstrateDecode.stateCov_twoPhase
#print axioms MassGap.SubstrateDecode.measMassOf_point
#print axioms MassGap.SubstrateDecode.ihol_piFlux
#print axioms MassGap.SubstrateDecode.siteEnergy_piFlux
#print axioms MassGap.SubstrateDecode.twoPhase_not_decaysAt
#print axioms MassGap.SubstrateDecode.measMass_twoPhase
#print axioms MassGap.SubstrateDecode.not_locks_twoPhase
#print axioms MassGap.SubstrateDecode.locks_of_lockPersistsAlong
#print axioms MassGap.SubstrateDecode.locks_of_lockPersists
#print axioms MassGap.SubstrateDecode.lockPersistsAlong_self_iff
#print axioms MassGap.SubstrateDecode.not_lockPersistsAlong_twoPhase
#print axioms MassGap.SubstrateDecode.not_lockPersistsAlong_point
#print axioms MassGap.SubstrateDecode.runSeed_of_lockPersists
