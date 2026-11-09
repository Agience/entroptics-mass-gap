import Mathlib
import MassGap.FinalBridge
import MassGap.FluxSplitCasimir
import MassGap.VortexCondense

/-!
# MassGap.FloorTension — the rubber band: what a positive string tension gives the floor under the lowest note

The question of `FinalBridge`: why does a floor remain under the lowest note when the window opens to infinity, at
every coupling? The bridge read is `FinalBridge.MassReadOpens N`: `0 < mU β` at every `β ≥ 0`
(`FinalBridge.readOpens_iff`). This module tries the string-tension answer: stretching the field between charges
costs energy proportional to length, and the least cost of anything is the mass. Declarations are in the namespace
`MassGap.FloorTension`.

## 0. What the tree has (the map)

* The measured tension read on the windows: `LineSeedsBasin.tensionArea N β w i`, the hop tension of the
  electric-flux relay odds summed over the window's chain, on the flux share's own aperture; it telescopes to
  `log o(0) − log o(J)` (`tensionArea_eq`). `LineSeedsBasin.TensionBelow N A` names a lower bound `A(β)` per unit
  sheet area. `LineSeedsBasin.fluxShareN_le_of_area`: the area bounds the flux share,
  `fluxShareN ≤ N³ e^{−tensionArea}`.
* The exact split of the floor: `CasimirStep.vanishing_iff_noCasimirAt` (the window coupling vanishes iff there is
  no Casimir term) and `FluxSplitCasimir.noCasimirAt_iff_sectors` (no Casimir term iff the flux share vanishes
  along the windows, `FluxConfinedAt`, and the zero-flux defect vanishes, `ZeroFluxVanishing`).
  `FluxSplitCasimir.fluxConfinedAt_of_tension`: a positive `TensionBelow` confines the flux.
* Wilson loops: `VortexCondense.wloopR` (the `SU(2)` rectangular torus), `VortexCondense.HasTension W σ`
  (`−log W(n,n)/n² → σ`), `VortexTwo.floor_of_vortexR_condensation_two` and `VortexStrong.floor_of_strong`
  (centre-vortex condensation and `ChessboardFlux` give an area law, Tomboulis–Yaffe; condensation proved at
  `0 < β ≤ 1/4000000`). `EdgeCost.StringScalingAt`, `CellLinks.tension_floor_of_stringScaling`,
  `NonAbelianForget.edge_mass`, `OneBridge.relFloorM_of_edgeCost`: a tension `σ` as a function argument, with no
  declaration defining it from the measure.
* The window floor along towers: `CouplingTower.ConfinedAt`, `CouplingTower.le_window_mass`,
  `GapReadsTensorProved.confinedAt`, `FinalBridge.windowReading_floor`.
* No declaration in the tree goes from a tension (any of the reads above) to `mU β > 0` without a second input on
  the neutral sector. Every tension-to-gap theorem in the tree (for example
  `FluxSplitCasimir.windowGap_of_tension_binding`, `LineSeedsVanishing.vanishing_of_tension_zeroFlux`,
  `LineSeedsBasin.observerGap_of_tension_zeroFlux`) carries the zero-flux or binding clause as a hypothesis.

## 1. Tension positive at a coupling (stated, parameter-free)

* `AreaLawAt N β`: some `σ > 0` (existential, the state's own rate) bounds the electric-flux share of the window
  `2^w` by `e^{−σ · 2^w (2^w − 2)}`, eventually along the windows, at every step `i`. This is 't Hooft's
  electric-flux area law read on the flux share itself, not on the logarithm of the odds: the share is a ratio of
  traces in `[0, 1]`, so a share `0` (infinite tension) reads as a tension, where `tensionArea` reads the odds-zero case as `0`
  through `log 0 = 0` (proved at β = 0: `tensionArea_zero_coupling`; see also `tensionBelow_zero_coupling`).
* `TensionEvery N`: `AreaLawAt N β` at every `β ≥ 0`. This is "tension positive at every coupling".
* `areaLawAt_of_tensionBelow`: the tree's `TensionBelow N A` with `A(β) > 0` gives `AreaLawAt N β` at the rate
  `A(β)/2` (the prefactor `N³` is absorbed on large windows).
* `areaLawAt_zero` (the strong-coupling end, proved): at `β = 0` the flux odds vanish
  (`RelayChain.relayOdds_zero_coupling`), so the share is `≤ 0` and the area law holds at every rate.
  `TensionBelow` cannot see this (`LineSeedsBasin.tensionBelow_zero_coupling`: it forces `A(0) ≤ 0`).
* `fluxConfinedAt_of_areaLawAt`: the area law confines the flux (`FluxSplitCasimir.FluxConfinedAt`). The converse
  does not hold in general: `FluxConfinedAt` asks only that the share fall below every level, at any rate, so a
  perimeter-like decay of the share confines the flux in this sense. For the floor, the area law is more than is
  used.

## 2. Tension to the floor at one coupling (proved; the second input named)

* `window_floor_at` (the `le_window_mass` mechanism at fixed `β`, no tower): at `β ≥ 0`, a window `w ≥ 1` in the
  basin (`windowCoupling N β w ≤ 1/1000`) gives `log 2 / 2^w ≤ mU β` (`GapReadsTensorProved.confinedAt` at
  `u₀ = windowCoupling N β w`). `apertureRead_floor_at`: the same as `log 2 ≤ 2^w · mU β`, the floor in window
  units.
* `vanishes_iff_flux_zeroFlux`: at `β ≥ 0`, the vanishing read `StrongAnchor.Vanishes N β` holds exactly when the
  flux is confined and the zero-flux defect vanishes (`CasimirStep` composed with `FluxSplitCasimir`).
* **`readOpens_of_tension_zeroFlux`**, `mU_pos_of_tension_zeroFlux`: at `β ≥ 0`, `AreaLawAt N β` and
  `ZeroFluxVanishing N β` give `ReadOpens N β` and `0 < mU β`.
* `apertureRead_floor_of_tension_zeroFlux`: under the same two, eventually along the windows
  `log 2 ≤ 2^w · mU β`: the floor `log 2` in window units, at one fixed coupling, on every large window.

The second input is the template, named plainly: `LineSeedsVanishing.ZeroFluxVanishing N β`, the doubling defect
of the zero-flux (neutral, glueball) sector vanishing along the windows. It is the finite-size read of the gap in
the sector that carries no flux. Tension does not reach it on the tree's reads: `FiniteReadingFlux.wilson_neutral` (proved in the
tree) tensors the Wilson slice with a neutral two-state factor, within the class of centre-invariant kernels the
sector machinery uses. Every twisted ratio and the flux share are unchanged, while the zero-flux defect rises by
`log(25/17)`. No inequality from the flux-sector reads to the zero-flux defect holds on that class, so no theorem
on these reads takes the tension alone to `NoCasimirAt`. This is the tree's example, not a statement about the
`SU(N)` lattice measure. Read physically (argued), it resembles confined centre flux beside a neutral gapless
sector.

## 3. Every coupling (proved)

* **`noStall_iff_flux_zeroFlux`**: `StrongAnchor.NoStall N` (the existing input, equivalent to the vanishing read
  at every `β ≥ 0`) holds exactly when the flux is confined at every `β ≥ 0` and the zero-flux defect vanishes at
  every `β ≥ 0`. The input factors exactly into the rubber band and the neutral half.
* **`massReadOpens_of_tension_zeroFlux`**: `TensionEvery N` and `ZeroFluxVanishing` at every `β ≥ 0` give the
  bridge `FinalBridge.MassReadOpens N`.
* `fluxConfined_of_noStall`: `NoStall N` gives the confined flux at every coupling. So, against the existing
  input, tension adds nothing: it is the half of `NoStall N` that `NoStall N` already contains.

## 4. Tests (proved)

* Strong-coupling anchor. `areaLawAt_zero`: the area law at `β = 0`. `anchor_flux_zeroFlux`: on an actual interval
  `[0, β₀)`, `β₀ > 0`, both the confined flux and the vanishing zero-flux defect hold
  (`StrongAnchor.strongAnchor` read through the split). The rate form `AreaLawAt N β` at `β > 0` is not proved
  here: the tree's strong-coupling bounds on the flux share are per window (`SubstrateFluxRead.sectors_strong`) or
  on the vortex free energy of the corner tori at `SU(2)` (`VortexStrong.condenses_vortexR_strong`), and the
  passage from the latter to the share of every large window at one rate is not built.
* Free field: tension `0`, mass `m > 0`. `free_tension_zero`, `free_tension_unique`: a carrier whose loops all read
  `1` (nothing between the charges to stretch; counterexample choice: `W ≡ 1`) has `HasTension W 0` and no other
  tension. `free_mass_without_tension`: with it, at `m > 0`, the free read `2^w m` opens
  (`FinalBridge.freeRead_opens_iff`). So in the free read a mass is present without a tension (an illustration; no theorem links the loop
  family to the mass). The tree's neutral example (§2) shows no implication on its reads in the other direction.

## 5. Is tension at every `β` easier than mass at every `β`? (plainly)

No; it is a different half of the same input, and not the hard half for the floor.

* Proved: `NoStall N ↔ (flux confined at every β) ∧ (zero-flux defect vanishes at every β)`
  (`noStall_iff_flux_zeroFlux`). `TensionEvery N` gives the first factor only (`fluxConfinedAt_of_areaLawAt`).
  The floor `mU β > 0` is obtained here only with the second factor added (`mU_pos_of_tension_zeroFlux`).
* The second factor is the finite-size read of the gap in the neutral sector: the glueball floor itself. It is the
  mass statement restricted to the sector the flux does not see, so "tension ⇒ mass" moves the problem into that
  sector rather than solving it. The neutral test shows that no theorem can take the tension alone to it on the
  tree's reads.
* "Tension at every `β`" is not easier on its own terms either (argued): at weak coupling it is confinement of 4D
  `SU(N)`, open in the same regime as the gap; the tree proves it only at the strong end (`β = 0`, and the
  vortex condensation at `0 < β ≤ 1/4000000` with `ChessboardFlux` as input). Known mathematics agrees: an area
  law at strong coupling is Osterwalder–Seiler; an area law does not imply a mass gap as a theorem, and the mass
  gap does not imply an area law (the `Z₂` Higgs phase is gapped and deconfined).
* What the route does make precise: the tension half is closed exactly where the strong anchor is
  (`anchor_flux_zeroFlux`), and the remaining content of the floor at every coupling is `ZeroFluxVanishing` at
  every coupling. That is the zero-flux (glueball) sector's own no-stall statement.

DERIVED (module-wide): `0` the signs, the lower end of the couplings and the limits; `1` the least window index and
the base of `log 2 ≥ 0`; `2` the window base `2^w`, the least rank of `SU(N)` and the least window with a hop in
`2^w (2^w − 2)` (the sheet: side `2^w` by time extent `2^w − 2`, `LineSeedsBasin.TensionBelow`); `3` the power
`|Z_N³| = N³`; `4` the corner steps `Fin 4`; `log 2` the window rate of `CouplingTower.windowGap`; `A(β)/2` the
half of a measured rate that absorbs the prefactor `N³`. Inherited, not derived here: `1/1000` the seed of
`DoublingSharp` (through `GapReadsTensorProved.confinedAt` and `StrongAnchor.vanishes_iff_seed`); `1/80000`,
`1/4000000` and `log(25/17)` appear only in cited tree statements. Witness choice: `1` the rate in
`areaLawAt_zero` (any positive rate works there). Counterexample choice: `W ≡ 1` in `free_tension_zero`.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FloorTension

open Filter Topology
open scoped ENNReal
open MassGap.CouplingTower (windowCoupling)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)
open MassGap.LineSeedsBasin (TensionBelow)
open MassGap.LineSeedsVanishing (ZeroFluxVanishing)
open MassGap.FluxSplitCasimir (FluxConfinedAt)
open MassGap.MeasuredSpacing (mU)

variable {N : ℕ} [NeZero N]

/-! ## 1. Tension positive at a coupling -/

/-- The sheet area `2^w (2^w − 2)` of the window `2^w`. DERIVED: `2` the base and the least hop. -/
def sheet (w : ℕ) : ℝ := (2 : ℝ) ^ w * ((2 : ℝ) ^ w - 2)

/-- DERIVED: `2` the base and the least hop. -/
theorem tendsto_sheet : Tendsto sheet atTop atTop := LineSeedsVanishing.tendsto_area

variable (N) in
/-- **The electric-flux area law at `β`**: some rate `σ > 0` bounds the flux share of the window `2^w` by
`e^{−σ · 2^w (2^w − 2)}`, eventually along the windows, at every step. DERIVED: `0` the sign; `2` the base and the
least hop; `4` the steps. -/
def AreaLawAt (β : ℝ) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ i : Fin 4, ∀ᶠ w in atTop, fluxShareN N β (2 ^ w) i ≤ Real.exp (-(σ * sheet w))

variable (N) in
/-- **Tension positive at every coupling.** DERIVED: `0` the lower end of the couplings. -/
def TensionEvery : Prop := ∀ β : ℝ, 0 ≤ β → AreaLawAt N β

/-- **The tree's measured tension gives the area law** at the rate `A(β)/2`. DERIVED: `2` the half that absorbs
`N³`; `3` the power `N³`; `0` the signs. -/
theorem areaLawAt_of_tensionBelow {A : ℝ → ℝ} (hT : TensionBelow N A) {β : ℝ} (hβ : 0 ≤ β) (hA : 0 < A β) :
    AreaLawAt N β := by
  refine ⟨A β / 2, half_pos hA, fun i => ?_⟩
  have hbig : ∀ᶠ w in atTop, (N : ℝ) ^ 3 ≤ Real.exp (A β / 2 * sheet w) :=
    (Real.tendsto_exp_atTop.comp (tendsto_sheet.const_mul_atTop (half_pos hA))).eventually_ge_atTop _
  filter_upwards [hbig, eventually_ge_atTop 2] with w hw hw2
  have h := LineSeedsBasin.fluxShareN_le_of_area hβ w i (hT β hβ w hw2 i)
  calc fluxShareN N β (2 ^ w) i ≤ (N : ℝ) ^ 3 * Real.exp (-(A β * sheet w)) := h
    _ ≤ Real.exp (A β / 2 * sheet w) * Real.exp (-(A β * sheet w)) :=
        mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
    _ = Real.exp (-(A β / 2 * sheet w)) := by rw [← Real.exp_add]; congr 1; ring

/-- **The area law at `β = 0`**: the flux odds vanish, so the share is `≤ 0`. Witness choice: the rate `1` (any
positive rate works). DERIVED: `0` the ultralocal coupling. -/
theorem areaLawAt_zero : AreaLawAt N 0 := by
  refine ⟨1, one_pos, fun i => Filter.Eventually.of_forall fun w => ?_⟩
  rw [RelayChain.fluxShareN_eq_relay]
  refine (RelayChain.relayShare_le_odds le_rfl _).trans ?_
  rw [RelayChain.relayOdds_zero_coupling]
  exact (Real.exp_pos _).le

/-- **The area law confines the flux.** DERIVED: `0` the signs and the limit. -/
theorem fluxConfinedAt_of_areaLawAt {β : ℝ} (h : AreaLawAt N β) : FluxConfinedAt N β := by
  obtain ⟨σ, hσ, hL⟩ := h
  intro i ε hε
  have hu : Tendsto (fun w : ℕ => Real.exp (-(σ * sheet w))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_sheet.const_mul_atTop hσ)
  filter_upwards [hL i, hu.eventually (gt_mem_nhds hε)] with w h1 h2
  exact h1.trans h2.le

/-- **Tension at every coupling confines the flux at every coupling.** DERIVED: `0` the lower end. -/
theorem fluxConfined_of_tensionEvery (hT : TensionEvery N) : ∀ β : ℝ, 0 ≤ β → FluxConfinedAt N β :=
  fun β hβ => fluxConfinedAt_of_areaLawAt (hT β hβ)

/-! ## 2. Tension to the floor at one coupling -/

/-- **The window floor at one coupling** (the `le_window_mass` mechanism without a tower): a window `w ≥ 1` in the
basin gives `log 2 / 2^w ≤ mU β`. DERIVED: `2` the least rank and the base; `1` the least window; `0` the sign.
Inherited: `1/1000` the seed of `DoublingSharp`. -/
theorem window_floor_at (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (hs : windowCoupling N β w ≤ 1 / 1000) :
    ENNReal.ofReal (Real.log 2 / 2 ^ w) ≤ mU (NeZero.ne N) β :=
  GapReadsTensorProved.confinedAt (N := N) hN2 hs β hβ w hw rfl

/-- **The window floor in window units**: `log 2 ≤ 2^w · mU β` at a window in the basin. DERIVED: as
`window_floor_at`. Inherited: `1/1000`. -/
theorem apertureRead_floor_at (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (hs : windowCoupling N β w ≤ 1 / 1000) :
    ENNReal.ofReal (Real.log 2) ≤ FinalBridge.apertureRead N β w := by
  have h := window_floor_at hN2 hβ hw hs
  have hp : (0 : ℝ) < 2 ^ w := by positivity
  have e : ENNReal.ofReal (Real.log 2) = (2 : ℝ≥0∞) ^ w * ENNReal.ofReal (Real.log 2 / 2 ^ w) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul hp.le]
    congr 1
    field_simp
  rw [e, FinalBridge.apertureRead]
  gcongr

/-- **The vanishing read is the confined flux with the vanishing zero-flux defect.** DERIVED: `0` the sign and the
limit. -/
theorem vanishes_iff_flux_zeroFlux {β : ℝ} (hβ : 0 ≤ β) :
    StrongAnchor.Vanishes N β ↔ FluxConfinedAt N β ∧ ZeroFluxVanishing N β :=
  (CasimirStep.vanishing_iff_noCasimirAt N β).trans (FluxSplitCasimir.noCasimirAt_iff_sectors hβ)

/-- **Tension and the zero-flux clause open the read at `β`.** DERIVED: `2` the least rank; `0` the sign. -/
theorem readOpens_of_tension_zeroFlux (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (hT : AreaLawAt N β)
    (hZ : ZeroFluxVanishing N β) : FinalBridge.ReadOpens N β :=
  FinalBridge.readOpens_of_vanishes hN2 hβ
    ((vanishes_iff_flux_zeroFlux hβ).mpr ⟨fluxConfinedAt_of_areaLawAt hT, hZ⟩)

/-- **Tension and the zero-flux clause give a positive mass at `β`.** DERIVED: `2` the least rank; `0` the sign. -/
theorem mU_pos_of_tension_zeroFlux (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (hT : AreaLawAt N β)
    (hZ : ZeroFluxVanishing N β) : 0 < mU (NeZero.ne N) β :=
  (FinalBridge.readOpens_iff β).mp (readOpens_of_tension_zeroFlux hN2 hβ hT hZ)

/-- **The floor `log 2` in window units on every large window, at one coupling**, from tension and the zero-flux
clause. DERIVED: `2` the least rank and the base; `1` the least window; `0` the sign. Inherited: `1/1000`. -/
theorem apertureRead_floor_of_tension_zeroFlux (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (hT : AreaLawAt N β)
    (hZ : ZeroFluxVanishing N β) :
    ∀ᶠ w in atTop, ENNReal.ofReal (Real.log 2) ≤ FinalBridge.apertureRead N β w := by
  have hV : StrongAnchor.Vanishes N β :=
    (vanishes_iff_flux_zeroFlux hβ).mpr ⟨fluxConfinedAt_of_areaLawAt hT, hZ⟩
  have hs : ∀ᶠ w in atTop, windowCoupling N β w ≤ 1 / 1000 :=
    hV.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hs, eventually_ge_atTop 1] with w h hw
  exact apertureRead_floor_at hN2 hβ hw h

/-! ## 3. Every coupling -/

/-- **The existing input factors into the rubber band and the neutral half.** DERIVED: `0` the lower end. -/
theorem noStall_iff_flux_zeroFlux :
    StrongAnchor.NoStall N ↔
      (∀ β : ℝ, 0 ≤ β → FluxConfinedAt N β) ∧ (∀ β : ℝ, 0 ≤ β → ZeroFluxVanishing N β) := by
  rw [StrongAnchor.noStall_iff (NeZero.ne N)]
  exact ⟨fun h => ⟨fun β hβ => ((vanishes_iff_flux_zeroFlux hβ).mp (h β hβ)).1,
      fun β hβ => ((vanishes_iff_flux_zeroFlux hβ).mp (h β hβ)).2⟩,
    fun h β hβ => (vanishes_iff_flux_zeroFlux hβ).mpr ⟨h.1 β hβ, h.2 β hβ⟩⟩

/-- **`NoStall` already contains the confined flux at every coupling.** DERIVED: `0` the lower end. -/
theorem fluxConfined_of_noStall (h : StrongAnchor.NoStall N) : ∀ β : ℝ, 0 ≤ β → FluxConfinedAt N β :=
  (noStall_iff_flux_zeroFlux.mp h).1

/-- **Tension at every coupling and the zero-flux clause at every coupling give the bridge.**
DERIVED: `2` the least rank; `0` the lower end. -/
theorem massReadOpens_of_tension_zeroFlux (hN2 : 2 ≤ N) (hT : TensionEvery N)
    (hZ : ∀ β : ℝ, 0 ≤ β → ZeroFluxVanishing N β) : FinalBridge.MassReadOpens N :=
  fun β hβ => readOpens_of_tension_zeroFlux hN2 hβ (hT β hβ) (hZ β hβ)

/-! ## 4. Tests -/

/-- **The strong anchor closes both halves on an interval** `[0, β₀)`, `β₀ > 0`. DERIVED: `0` the lower end. -/
theorem anchor_flux_zeroFlux :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → FluxConfinedAt N β ∧ ZeroFluxVanishing N β := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongAnchor.strongAnchor (NeZero.ne N)
  exact ⟨β₀, hβ₀, fun β hβ hlt => (vanishes_iff_flux_zeroFlux hβ).mp (h β hβ hlt)⟩

/-- **Free carrier: tension `0`.** Loops that all read `1` (counterexample choice `W ≡ 1`) have tension `0`.
DERIVED: `1` the loop read; `0` the tension. -/
theorem free_tension_zero : VortexCondense.HasTension (fun _ _ => (1 : ℝ)) 0 := by
  refine ⟨fun _ _ => one_pos, ?_⟩
  simp only [Real.log_one, neg_zero, zero_div]
  exact tendsto_const_nhds

/-- **Free carrier: no other tension.** DERIVED: `1` the loop read; `0` the tension. -/
theorem free_tension_unique {σ : ℝ} (h : VortexCondense.HasTension (fun _ _ => (1 : ℝ)) σ) : σ = 0 :=
  tendsto_nhds_unique h.2 free_tension_zero.2

/-- **Two facts about the free read**: the carrier whose loops all read `1` has tension `0` only, and at `m > 0`
the free read `2^w m` opens. No theorem ties the loop family to the field of mass `m`; this is an illustration
that a positive free mass carries no tension in this read, not a proof about a gauge field. DERIVED: `0` the tension and the sign; `2` the window base. -/
theorem free_mass_without_tension {m : ℝ} (hm : 0 < m) :
    (∀ σ : ℝ, VortexCondense.HasTension (fun _ _ => (1 : ℝ)) σ → σ = 0) ∧
      Tendsto (fun w : ℕ => (2 : ℝ) ^ w * m) atTop atTop :=
  ⟨fun _ h => free_tension_unique h, (FinalBridge.freeRead_opens_iff hm.le).mpr hm⟩

end MassGap.FloorTension

end

#print axioms MassGap.FloorTension.tendsto_sheet
#print axioms MassGap.FloorTension.areaLawAt_of_tensionBelow
#print axioms MassGap.FloorTension.areaLawAt_zero
#print axioms MassGap.FloorTension.fluxConfinedAt_of_areaLawAt
#print axioms MassGap.FloorTension.fluxConfined_of_tensionEvery
#print axioms MassGap.FloorTension.window_floor_at
#print axioms MassGap.FloorTension.apertureRead_floor_at
#print axioms MassGap.FloorTension.vanishes_iff_flux_zeroFlux
#print axioms MassGap.FloorTension.readOpens_of_tension_zeroFlux
#print axioms MassGap.FloorTension.mU_pos_of_tension_zeroFlux
#print axioms MassGap.FloorTension.apertureRead_floor_of_tension_zeroFlux
#print axioms MassGap.FloorTension.noStall_iff_flux_zeroFlux
#print axioms MassGap.FloorTension.fluxConfined_of_noStall
#print axioms MassGap.FloorTension.massReadOpens_of_tension_zeroFlux
#print axioms MassGap.FloorTension.anchor_flux_zeroFlux
#print axioms MassGap.FloorTension.free_tension_zero
#print axioms MassGap.FloorTension.free_tension_unique
#print axioms MassGap.FloorTension.free_mass_without_tension
