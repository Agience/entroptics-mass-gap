import Mathlib
import MassGap.CrossingUnify
import MassGap.WDeltaRun
import MassGap.DeltaLengthTower

/-!
# MassGap.PhysicalScaleSmall — the exact effective density read at the physical scale

`GapSideExactDecimation.vortexF_crossing_exact` is an identity at every step count `k`:
`vortexF C 0 P (2^{k+2}) = FE(effIter k 4 (fineDens (halfField (C.W 0) suTau)), sheet_P)`. This module picks `k`
from the two-loop spacing alone, `kPhys L β = log₂ ⌊L / aRun 2 β⌋ − 2`, so the fine side `2^{kPhys + 2}` is the
physical size `L` in lattice units, and reads the side-`4` exact effective density `physDens L β` there. No
Migdal–Kadanoff chain enters the step count; the chain enters only as `W₀`, the Wilson weight itself.

The two items read different parts of that density. `hW` reads its dependence on the background only through
the closed twist sheet (`PhysVortex`, `PhysRatio`). `hpos` (1b) reads only its per-link oscillation `cL`
(`PhysLinkOsc`); the per-plaquette background constant is left free at every `β`.

## What is proved

* **The physical side** (`kPhys`, `physSide_spec`, `eventually_physSide_le`). Where `4 aRun 2 β ≤ L`,
  `L/2 < 2^{kPhys L β + 2} · aRun 2 β ≤ L`; eventually in `β` the upper bound holds. This is `WDeltaRun.RunSeed`'s
  size clause, by construction.
* **The closed-sheet vortex free energy at the physical side** (`PhysVortex`, `physVortex_iff`, `PhysRatio`,
  `FE_sheet_le_of_ratio`, `physVortex_of_physRatio`). `PhysVortex L ε` is `vortexF (W₀, 2^{kPhys + 2}) ≤ ε` at
  every sheet plane, eventually in `β`; by `vortexF_crossing_exact` it is the same statement as
  `FE(physDens L β, sheet_P) ≤ ε` (`physVortex_iff`). `PhysRatio L η`, the pointwise closed-sheet ratio
  `|log ρ(sheet_P, V) − log ρ(1, V)| ≤ η` at every link configuration `V`, gives `PhysVortex L η`
  (`abs_log_integral_sub_le`, no sheet count).
* **The seed at the physical side** (`physSectorSeed_of_physVortex`, `defectW_phys_le`, `physSeed`,
  `runSeed_two_of_physSectorSeed`). With `PhysRest L` and `9 ε ≤ 1/80000`,
  `GapSideVortexAntiDiagonal.fluxShareN_zero_le_of_vortex` gives the step-`0` flux share,
  `CentreSectorSeedN.defectW_le_of_sectorsN` gives `defectW 2 β (2^{kPhys + 2}) ≤ 1/1000`, and the side clause
  gives `RunSeed 2` with `C = L`.
* **`hW` from the physical-scale vortex bound** (`wDelta2_two_of_physVortex`, `wDelta2_two_of_physRatio`):
  `PhysVortex L ε` (or `PhysRatio L ε`), `PhysRest L`, `0 ≤ ε`, `9 ε ≤ 1/80000`, `L > 0` give
  `DoublingClay2.WDelta2 2 ℓ₀` at every `ℓ₀ ≥ L/2`. No size clause and no first-crossing clause is an input.
* **The pinned path** (`clay_canonical_two_phys`): `ExistenceReduce.clay_canonical` at `N = 2` with `hW` replaced
  by `PhysVortex L ε`, `PhysRest L` and the scalar bound.
* **`hpos` (1b) from the link constant alone** (`LinkOsc`, `boundPixelT_of_linkOsc`, `boundOnePoint_of_linkOsc`,
  `clay_canonical_linkOsc_fac`). `MomentCompare.fac_ratio`, `effScreenRel_of_fac_torus` and
  `RelativeScreen.relScreen_of_effScreenRel` take `UnitOsc ρ cP cL` with `cP` arbitrary and read only `cL`. So the
  coarse family needs, at each `k`, some `cP` (depending on `k`) with `UnitOsc (ρs k) cP cL`, and banding.
* **`hpos` and `hW` at the same density** (`physDens_banded`, `physTower`, `PhysLinkOsc`, `linkOsc_physTower`,
  `clay_canonical_phys`, `clay_canonical_phys_small`). `physTower hN L k` is the physical-scale density of the
  chain from `2 · dyBeta k`. `PhysLinkOsc L δ` (eventually in `β`, some `cP` with
  `UnitOsc (physDens L β) cP δ`) gives `LinkOsc (physTower hN L) δ`. `PhysLinkOsc L δ` with the factorisations
  `FacPixelAt`, `FacOnePointAt` at `physTower`, `ReadingFloor`, `PhysVortex L ε`, `PhysRest L` and `hD` gives
  the pinned conclusion, with `hW` replaced by `PhysVortex` and `PhysRest`. `clay_canonical_phys_small` states the scalar conditions as two
  thresholds, `δ ≤ δ₀` on the link constant and `ε ≤ 1/720000` on the vortex free energy.

## Where the first crossing was used, and what replaces it

In `GapSideExactDecimation.sectorSeed_of_exactEffectiveSmall` and `CrossingUnify` / `ScreenBridge`, no proof step
reads `coarseDefect C k ≤ 1/1000` or the minimality `∀ i < k`. The two clauses only gate the hypotheses and the
conclusion `FirstCrossingSectorSeed`, and they are passed through. `vortexF_crossing_exact`,
`fluxShareN_zero_le_of_vortex` and `defectW_le_of_sectorsN` hold at every `k`. So the replacement is a re-gating,
proved here, at `k = kPhys L β`.

## Why the background enters only through the closed sheet (argued)

`UnitOsc ρ cP cL` bounds the change of `log ρ` when one background plaquette takes any `SU(2)` value. Through
`pullTw`, one coarse `(i, j)` plaquette at `y` of the side-`4` torus pulls back after `k` steps to the fine
`(i, j)` plaquettes at `x_i = 2^k (y_i + 1) − 1`, `x_j = 2^k (y_j + 1) − 1` and all `2^k × 2^k` positions in the
two orthogonal directions, each carrying that value; the patch is open, its boundary a thin flux loop of length
about `2^{k+2}` in lattice units, with action of order `β L / a` for a centre value
(for a non-central value the interior costs as well, of order the patch area). So no `cP` bounds `UnitOsc (physDens L β) cP _` uniformly in `β`,
and no theorem here takes a bound on `cP`. The closed sheet `sheet_P` (all plaquettes of one orientation at one
position, around the torus) has no boundary; its free energy is the 't Hooft vortex free energy of a torus of
physical side `2^{kPhys + 2} a ∈ (L/2, L]`, of order `e^{−σ L²/4}` under an area law. That is the content of
`PhysVortex L ε` for `L = L(ε)` large; the uniformity in `β` at fixed `L` is the existence of the continuum limit of
the vortex free energy (argued, asymptotic freedom).

## Why the link constant is not obstructed the same way (argued)

`glueStep` sets the coarse link `V_l = u₁ u₂`, the product of the two fine links on its line, with `u₂`
integrated; `unitOsc_effIter` carries `cL` unchanged through the flow because one coarse link change is one fine
link change. After `kPhys` steps a coarse link is the holonomy of a straight line of `2^{kPhys}` fine links, and
changing it forces no thin defect: the change can be spread along the line at classical cost of order
`β θ² / 2^{kPhys}`, which tends to `0`. The a priori bound (one fine link, six plaquettes, oscillation of order
`β`) is not uniform in `β`. The spread cost is a cost at the action's minimum, while `UnitOsc` is a supremum over
links and backgrounds (including non-central background patches that touch the line's last fine link); the
pointwise carrier `abs_log_integral_sub_le` gives only a first-order cost of order `β θ`. So a uniform small `cL`
must come from the integral, as the strong-coupling statement for the line holonomies at block size `L/4`
(argued), not refuted at the unit. The consumers read `UnitOsc.link` only at the background `EffScreenFac`
supplies.

## What is not proved

`PhysVortex L ε`, `PhysLinkOsc L δ` and `PhysRest L` themselves, and the factorisations `FacPixelAt` /
`FacOnePointAt` at `physTower`. `PhysRest` is seven of the eight sector-seed conjuncts, including the four
zero-flux defects `trivialDefectN`; it is target-strength content (see its docstring). With `PhysVortex` it is a
sector-resolved strengthening of `RunSeed 2` at the side `2^{kPhys + 2}`, so the `hW` side here is a reduction,
not a discharge.

DERIVED (module-wide): `2` the block factor; `4` the coarse side and `2^{k+2} = 2^k · 4`; `kPhys = log₂ ⌊L/a⌋ − 2`
so that `2^{kPhys + 2}` is the largest power of two at most `L/a`; `9` and `1/80000` from
`fluxShareN_zero_le_of_vortex` and `defectW_le_of_sectorsN`; `1/720000 = 1/(9 · 80000)`; `L/4` the bound on `aRun`
that makes `⌊L/a⌋ ≥ 4`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.PhysicalScaleSmall

open MeasureTheory Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing
  MassGap.ElectricStepChain MassGap.MovedTorusDecimation MassGap.ElectricExactProof
  MassGap.GapSideVortexAntiDiagonal MassGap.WilsonChainExists
  MassGap.GapSideExactDecimation MassGap.CoarseBoundary MassGap.EffectiveDensityBound
  MassGap.ScreenBridge MassGap.MomentCompare MassGap.CrossingUnify
open MassGap.TwistedTraceBound (negOne coe_negOne)

/-! ## 1. The physical step count -/

section Side

/-- **The physical step count** at physical size `L`: `log₂ ⌊L / aRun 2 β⌋ − 2`, so that the fine side
`2^{kPhys + 2}` is the largest power of two at most `L / aRun 2 β` (`physSide_spec`). -/
def kPhys (L β : ℝ) : ℕ := Nat.log 2 ⌊L / AsymptoticScaling.aRun 2 β⌋₊ - 2

/-- **The fine side is the physical size**: where `4 aRun 2 β ≤ L`,
`2^{kPhys + 2} · aRun 2 β ≤ L < 2 · 2^{kPhys + 2} · aRun 2 β`. -/
theorem physSide_spec {L β : ℝ} (hβ : 0 < β) (h4 : 4 * AsymptoticScaling.aRun 2 β ≤ L) :
    (2 : ℝ) ^ (kPhys L β + 2) * AsymptoticScaling.aRun 2 β ≤ L ∧
      L < 2 * ((2 : ℝ) ^ (kPhys L β + 2) * AsymptoticScaling.aRun 2 β) := by
  have ha : 0 < AsymptoticScaling.aRun 2 β := AsymptoticScaling.aRun_pos (by norm_num) hβ
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = ⌊L / AsymptoticScaling.aRun 2 β⌋₊ := ⟨_, rfl⟩
  have hx : (4 : ℝ) ≤ L / AsymptoticScaling.aRun 2 β := by
    rw [le_div_iff₀ ha]
    linarith
  have hm : 4 ≤ m := by
    rw [hm_def]
    exact Nat.le_floor (by exact_mod_cast hx)
  have hlog : 2 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) (le_trans (by norm_num) hm)
  have hk0 : kPhys L β = Nat.log 2 m - 2 := by
    rw [hm_def]
    rfl
  have hk : kPhys L β + 2 = Nat.log 2 m := by omega
  have hp : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hq : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hq' : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by omega
  have hpR : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast hp
  have hqR : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 m + 1) := by exact_mod_cast hq'
  have hfl : (m : ℝ) ≤ L / AsymptoticScaling.aRun 2 β := by
    rw [hm_def]
    exact Nat.floor_le (by linarith)
  have hlt : L / AsymptoticScaling.aRun 2 β < (m : ℝ) + 1 := by
    rw [hm_def]
    exact Nat.lt_floor_add_one _
  rw [hk]
  refine ⟨(le_div_iff₀ ha).mp (hpR.trans hfl), ?_⟩
  have h2 := (div_lt_iff₀ ha).mp (hlt.trans_le hqR)
  have e : (2 : ℝ) ^ (Nat.log 2 m + 1) * AsymptoticScaling.aRun 2 β
      = 2 * ((2 : ℝ) ^ Nat.log 2 m * AsymptoticScaling.aRun 2 β) := by ring
  rw [e] at h2
  exact h2

/-- **The size clause holds by construction**, eventually in `β`. -/
theorem eventually_physSide_le {L : ℝ} (hL : 0 < L) :
    ∀ᶠ β in atTop, (2 : ℝ) ^ (kPhys L β + 2) * AsymptoticScaling.aRun 2 β ≤ L := by
  filter_upwards [WeakCouplingWindow.eventually_aRun_le (N := 2) (by norm_num) (b := L / 4)
    (by positivity), eventually_gt_atTop (0 : ℝ)] with β ha hβ
  exact (physSide_spec hβ (by linarith)).1

end Side

/-! ## 2. The closed-sheet vortex free energy at the physical side -/

section Vortex

/-- A positive integrand on a probability space has a positive integral. -/
theorem integral_pos_of_forall_pos_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {u : Ω → ℝ} (hu : ∀ x, 0 < u x) (iu : Integrable u μ) :
    0 < ∫ x, u x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hu x).le) iu]
  rw [show Function.support u = Set.univ from Set.eq_univ_of_forall fun x => (hu x).ne',
    measure_univ]
  exact one_pos

/-- **The sheet free energy from the pointwise closed-sheet ratio**: a positive integrable side-`4` family whose
log changes by at most `η` at every link configuration when the closed sheet `sheet_P` is put in has
`FE(ρ, sheet_P) ≤ η`. -/
theorem FE_sheet_le_of_ratio {ρ : DensE 4} (hpos : ∀ ζ V, 0 < ρ ζ V)
    (hi : ∀ ζ, Integrable (ρ ζ) (piL 4)) {η : ℝ} (P : Plane)
    (hb : ∀ V, |Real.log (ρ (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) V)
      - Real.log (ρ (fun _ => 1) V)| ≤ η) :
    FE ρ (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) ≤ η := by
  have hI : |Real.log (ZE ρ (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne))
      - Real.log (ZE ρ (fun _ => 1))| ≤ η :=
    abs_log_integral_sub_le (piL 4) (hpos _) (hpos _) (hi _) (hi _) hb
  have hZ : ∀ ζ, 0 < ZE ρ ζ := fun ζ => integral_pos_of_forall_pos_prob (piL 4) (hpos ζ) (hi ζ)
  unfold FE
  rw [Real.log_div (hZ _).ne' (hZ _).ne']
  have := (abs_le.mp hI).1
  linarith

/-- The side-`4` exact effective density of `W₀` of the chain from `2β` after `kPhys L β` steps: the density at
the physical scale `L`. -/
def physDens (L β : ℝ) : DensE 4 :=
  effIter (kPhys L β) 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))

theorem physDens_pos (L β : ℝ) : ∀ ζ V, 0 < physDens L β ζ V :=
  effIter_fineDens_pos (continuous_halfField (wilsonChainOf (2 * β)) 0) _ 4

theorem physDens_integrable (L β : ℝ) : ∀ ζ, Integrable (physDens L β ζ) (piL 4) := fun ζ =>
  (effIter_spec _ 4 _
    (fun ζ' => integrable_fineDens (continuous_halfField (wilsonChainOf (2 * β)) 0) ζ') ζ).1

/-- **The closed-sheet vortex bound at the physical side**: eventually in `β`, at every sheet plane, the vortex
free energy of `W₀` of the chain from `2β` at side `2^{kPhys L β + 2}` (physical side in `(L/2, L]`) is at most
`ε`. -/
def PhysVortex (L ε : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ P : Plane, vortexF (wilsonChainOf (2 * β)) 0 P (2 ^ (kPhys L β + 2)) ≤ ε

/-- **`PhysVortex` is the closed-sheet free energy of the physical-scale density** (`vortexF_crossing_exact`). -/
theorem physVortex_iff {L ε : ℝ} :
    PhysVortex L ε ↔ ∀ᶠ β in atTop, ∀ P : Plane,
      FE (physDens L β) (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) ≤ ε := by
  have e : ∀ (β : ℝ) (P : Plane), vortexF (wilsonChainOf (2 * β)) 0 P (2 ^ (kPhys L β + 2))
      = FE (physDens L β) (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) :=
    fun β P => vortexF_crossing_exact _ 0 P _
  unfold PhysVortex
  simp only [e]

/-- **The pointwise closed-sheet ratio at the physical side**: eventually in `β`, for every sheet plane and every
link configuration of the side-`4` torus, the log of the physical-scale density changes by at most `η` when the
closed sheet is put in. -/
def PhysRatio (L η : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ (P : Plane) (V : TLink 4 4 → SU 2),
    |Real.log (physDens L β (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) V)
      - Real.log (physDens L β (fun _ => 1) V)| ≤ η

/-- **The pointwise closed-sheet ratio gives the vortex bound** with the same constant. -/
theorem physVortex_of_physRatio {L η : ℝ} (h : PhysRatio L η) : PhysVortex L η := by
  rw [physVortex_iff]
  filter_upwards [h] with β hβ
  intro P
  exact FE_sheet_le_of_ratio (physDens_pos L β) (physDens_integrable L β) P (hβ P)

end Vortex

/-! ## 3. The seed at the physical side, and `hW` -/

section Seed

/-- **The rest of the sectors at the physical side**: eventually in `β`, at side `2^{kPhys L β + 2}`, the flux
shares at `i ≠ 0` and the four zero-flux defects `trivialDefectN` are at most `1/80000`. This is seven of the
eight conjuncts of `PhysSectorSeed`; only the flux share at `i = 0` is left to `PhysVortex`. The four zero-flux
defects bound the defect within the trivial flux sector, which is the `RunSeed 2` defect bound itself in that
sector: target-strength content, not a consequence of the vortex bound.

DERIVED: `2` the rank and the block factor; `2^{k+2} = 2^k · 4`, `4` the coarse side. CHOSEN (in
`CentreSectorSeedN`): `1/80000` so that `15 · 5/80000 ≤ 1/1000`, the threshold of
`CentreSectorSeedN.defectW_le_of_sectorsN`. -/
def PhysRest (L : ℝ) : Prop :=
  ∀ᶠ β in atTop,
    (∀ i : Fin 4, i ≠ 0 → CentreSectorSeedN.fluxShareN 2 β (2 ^ (kPhys L β + 2)) i ≤ 1 / 80000) ∧
      ∀ i : Fin 4, CentreSectorSeedN.trivialDefectN 2 β (2 ^ (kPhys L β + 2)) i ≤ 1 / 80000

/-- **The sector seed at the physical side.**

DERIVED: `2` the rank and the block factor; `2^{k+2} = 2^k · 4`, `4` the coarse side. CHOSEN (in
`CentreSectorSeedN`): `1/80000` so that `15 · 5/80000 ≤ 1/1000`, the threshold of
`CentreSectorSeedN.defectW_le_of_sectorsN`. -/
def PhysSectorSeed (L : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ i : Fin 4,
    CentreSectorSeedN.fluxShareN 2 β (2 ^ (kPhys L β + 2)) i ≤ 1 / 80000 ∧
      CentreSectorSeedN.trivialDefectN 2 β (2 ^ (kPhys L β + 2)) i ≤ 1 / 80000

/-- **The sector seed from the closed-sheet vortex bound** and the rest of the sectors. -/
theorem physSectorSeed_of_physVortex {L ε : ℝ} (h : PhysVortex L ε) (hε : 0 ≤ ε)
    (hb : 9 * ε ≤ 1 / 80000) (hR : PhysRest L) : PhysSectorSeed L := by
  filter_upwards [h, hR, eventually_ge_atTop (0 : ℝ)] with β hV hR hβ
  obtain ⟨hR1, hR2⟩ := hR
  intro i
  refine ⟨?_, hR2 i⟩
  by_cases hi : i = 0
  · subst hi
    have hfl := fluxShareN_zero_le_of_vortex hβ (kPhys L β) hε (fun ν => hV (plane0 ν))
    linarith
  · exact hR1 i hi

/-- **The `SU(2)` seed at the physical side**: `defectW 2 β (2^{kPhys L β + 2}) ≤ 1/1000`, eventually in `β`. -/
theorem defectW_phys_le {L : ℝ} (h : PhysSectorSeed L) :
    ∀ᶠ β in atTop, ZoomSelfScale.defectW 2 β (2 ^ (kPhys L β + 2)) ≤ 1 / 1000 := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hS hβ
  exact CentreSectorSeedN.defectW_le_of_sectorsN (N := 2) hβ
    (DeltaLengthTower.two_le_two_pow (by omega : 1 ≤ kPhys L β + 2))
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) hS

/-- **The run-seed body at `C = L`**: a power of two `n ≥ 2` with `n · aRun 2 β ≤ L` and the seed at `n`. -/
theorem physSeed {L : ℝ} (hL : 0 < L) (h : PhysSectorSeed L) :
    ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ L ∧ ZoomSelfScale.defectW 2 β n ≤ 1 / 1000 := by
  filter_upwards [defectW_phys_le h, eventually_physSide_le hL] with β hD hS
  refine ⟨2 ^ (kPhys L β + 2), ⟨_, rfl⟩, DeltaLengthTower.two_le_two_pow (by omega), ?_, hD⟩
  push_cast
  exact hS

/-- **`RunSeed 2` from the physical-side sector seed**, with `C = L`. -/
theorem runSeed_two_of_physSectorSeed {L : ℝ} (hL : 0 < L) (h : PhysSectorSeed L) :
    WDeltaRun.RunSeed 2 :=
  ⟨L, hL, physSeed hL h⟩

/-- **`WDelta2 2` from the closed-sheet vortex bound and the rest of the sectors**, at every `ℓ₀ ≥ L/2`. -/
theorem wDelta2_two_of_physVortex {L ε : ℝ} (hL : 0 < L) (h : PhysVortex L ε) (hε : 0 ≤ ε)
    (hb : 9 * ε ≤ 1 / 80000) (hR : PhysRest L) :
    ∀ ℓ₀ : ℝ, L ≤ 2 * ℓ₀ → DoublingClay2.WDelta2 2 ℓ₀ :=
  fun _ hℓ => WDeltaRun.wDelta2_of_seed_le (by norm_num)
    (physSeed hL (physSectorSeed_of_physVortex h hε hb hR)) hℓ

/-- **`WDelta2 2` from the pointwise closed-sheet ratio and the rest of the sectors**, at every `ℓ₀ ≥ L/2`. -/
theorem wDelta2_two_of_physRatio {L η : ℝ} (hL : 0 < L) (h : PhysRatio L η) (hη : 0 ≤ η)
    (hb : 9 * η ≤ 1 / 80000) (hR : PhysRest L) :
    ∀ ℓ₀ : ℝ, L ≤ 2 * ℓ₀ → DoublingClay2.WDelta2 2 ℓ₀ :=
  wDelta2_two_of_physVortex hL (physVortex_of_physRatio h) hη hb hR

end Seed

/-! ## 4. `hpos` (1b) from the link constant alone -/

section Link

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone MassGap.LocalClosing

/-- **The link-oscillation Prop at the coarse scale**: eventually in `k`, the side-`n` density `ρs k` is banded
and has per-link oscillation `cL`, with some per-plaquette constant (depending on `k`) and `n`, `cL` fixed. -/
def LinkOsc {n : ℕ} (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, (∃ cP : ℝ, UnitOsc (ρs k) cP cL) ∧ Banded (ρs k)

/-- **The pixel bound from the link constant**: `fac_ratio` reads only `cL`. -/
theorem boundPixelT_of_linkOsc {N : ℕ} {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π : ℝ} {n : ℕ} {ρs : ℕ → DensE n} {cL : ℝ} (hU : LinkOsc ρs cL)
    (hS : EffScreenFacPixel hN c O t ℓ π ρs cL) :
    BoundPixelT hN c O t ℓ π (MassGap.RelativeScreen.LayerBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨⟨cP, hk1⟩, hk2⟩ := hk
  obtain ⟨m, hm, hπ⟩ := hs
  refine MassGap.RelativeScreen.layerBound_of_relScreen
    (MassGap.RelativeScreen.relScreen_of_effScreenRel hk1 hk2
      (effScreenRel_of_fac_torus hk1 hk2 hm 0 ?_))
  rw [refMomentS_eq (RelativeDecay.stateTD hN c) O t ℓ k]
  exact mul_le_mul_of_nonneg_right hπ (Real.sqrt_nonneg _)

/-- **The one-point bounds from the link constant.** -/
theorem boundOnePoint_of_linkOsc {N : ℕ} {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π : ℝ} {n : ℕ} {ρs : ℕ → DensE n} {cL : ℝ} (hU : LinkOsc ρs cL)
    (hS : EffScreenFacOnePoint hN c O t ℓ π ρs cL) :
    CoarseBoundary.BoundOnePoint hN c O t ℓ π (MassGap.RelativeScreen.LayerBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨⟨cP, hk1⟩, hk2⟩ := hk
  obtain ⟨Δ₀, Δ₁, s₀, s₁, m₀, m₁, h₀, h₁, e₀, e₁, hle⟩ := hs
  exact ⟨Δ₀, Δ₁,
    MassGap.RelativeScreen.layerBound_of_relScreen
      (MassGap.RelativeScreen.relScreen_of_effScreenRel hk1 hk2
        (effScreenRel_of_fac_torus hk1 hk2 h₀ s₀ e₀)),
    MassGap.RelativeScreen.layerBound_of_relScreen
      (MassGap.RelativeScreen.relScreen_of_effScreenRel hk1 hk2
        (effScreenRel_of_fac_torus hk1 hk2 h₁ s₁ e₁)), hle⟩

/-- **The pinned path with `hpos` read through the link constant alone**: `LinkOsc ρs cL`, the factored screens
at `cL` and the floor; `hD` and `hW` unchanged. -/
theorem clay_canonical_linkOsc_fac {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) {n : ℕ} {ρs : ℕ → DensE n} {cL : ℝ} (hU : LinkOsc ρs cL)
    (hSP : EffScreenFacPixel hN c O t ℓ π₁ ρs cL) (hS1 : EffScreenFacOnePoint hN c O t ℓ π₂ ρs cL)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_boundT hN2 hN O (B := MassGap.RelativeScreen.LayerBound hN)
    (fun _ _ _ _ h => h.closing) ht c hκ hπ₁ hπ₂ hπκ
    (boundPixelT_of_linkOsc hU hSP) (boundOnePoint_of_linkOsc hU hS1) hF hD hℓ hW

end Link

/-! ## 5. The pinned path: `hpos` and `hW` at the same density -/

section Pinned

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone MassGap.LocalClosing

theorem physDens_banded (L β : ℝ) : Banded (physDens L β) :=
  effIter_banded _ 4 _ (fineDens_banded (continuous_halfField (wilsonChainOf (2 * β)) 0))

/-- **The coarse family of (1b) at the physical scale**: at step `k`, the physical-scale density of the chain
from `2 · dyBeta k`. -/
def physTower {N : ℕ} (hN : N ≠ 0) (L : ℝ) (k : ℕ) : DensE 4 :=
  physDens L (dyBeta (one_le_of_ne_zero hN) k)

/-- **The physical-scale link constant**: eventually in `β`, the physical-scale density has per-link
log-oscillation at most `cL`, with some per-plaquette constant (free, depending on `β`). -/
def PhysLinkOsc (L cL : ℝ) : Prop := ∀ᶠ β in atTop, ∃ cP : ℝ, UnitOsc (physDens L β) cP cL

/-- **The physical-scale link constant gives the link Prop of (1b)** at the physical tower. -/
theorem linkOsc_physTower {N : ℕ} (hN : N ≠ 0) {L cL : ℝ} (h : PhysLinkOsc L cL) :
    LinkOsc (physTower hN L) cL :=
  ((tendsto_dyBeta (one_le_of_ne_zero hN)).eventually h).mono
    fun _ hk => ⟨hk, physDens_banded _ _⟩

/-- **`clay_canonical` at `N = 2` with `hW` replaced** by the closed-sheet vortex bound, the rest of the sectors
at the physical side and the scalar bound. -/
theorem clay_canonical_two_phys (hN : (2 : ℕ) ≠ 0) (O : LField (MassGap.SUN.SU 2)) {t ℓ : ℝ}
    (ht : 0 < t) (hpos : ∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {L ε : ℝ} (hL : 0 < L) (hV : PhysVortex L ε) (hε : 0 ≤ ε) (hbV : 9 * ε ≤ 1 / 80000)
    (hR : PhysRest L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  ⟨L / 2, by positivity, ExistenceReduce.clay_canonical le_rfl hN O ht hpos hD (by positivity)
    (wDelta2_two_of_physVortex hL hV hε hbV hR (L / 2) (by linarith))⟩

/-- **The pinned path at `N = 2` at the physical-scale density**: `hpos` through the link constant
`PhysLinkOsc L δ`, the factorisations at the physical tower, the one-point ratio clause and the floor; `hW`
through `PhysVortex L ε` and `PhysRest L`; `hD` unchanged. -/
theorem clay_canonical_phys (hN : (2 : ℕ) ≠ 0) (O : LField (MassGap.SUN.SU 2))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) {L δ : ℝ} (hL : 0 < L) (hX : PhysLinkOsc L δ) (hδ : 0 ≤ δ) {m₀ : ℕ} {R : ℝ}
    (h1 : (m₀ : ℝ) * δ ≤ 1) (hb₁ : 32 * ((m₀ : ℝ) * δ) ≤ π₁ ^ 2)
    (hb₂ : 32 * ((m₀ : ℝ) * δ) * R ≤ π₂)
    (hSP : FacPixelAt hN c O t ℓ (physTower hN L) m₀)
    (hS1 : FacOnePointAt hN c O t ℓ (physTower hN L) m₀ R)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    {ε : ℝ} (hV : PhysVortex L ε) (hε : 0 ≤ ε) (hbV : 9 * ε ≤ 1 / 80000) (hR : PhysRest L)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  ⟨L / 2, by positivity, clay_canonical_linkOsc_fac le_rfl hN O ht c hκ hπ₁ hπ₂ hπκ
    (linkOsc_physTower hN hX) (effScreenFacPixel_of_crossing hSP hδ h1 hπ₁ hb₁)
    (effScreenFacOnePoint_of_crossing hS1 hδ h1 hb₂) hF hD (by positivity)
    (wDelta2_two_of_physVortex hL hV hε hbV hR (L / 2) (by linarith))⟩

/-- **The scalar conditions as two thresholds**: for `m₀`, `π₁, π₂ > 0` with `π₁ + π₂ < κ` and `R`, some
`δ₀ > 0` such that at every link constant `δ ∈ [0, δ₀]`, every vortex bound `ε ∈ [0, 1/720000]` and every
`L > 0`, `PhysLinkOsc L δ` with the factorisations at the physical tower, the ratio clause, the floor,
`PhysVortex L ε`, `PhysRest L` and `hD` give the pinned conclusion. -/
theorem clay_canonical_phys_small (hN : (2 : ℕ) ≠ 0) (O : LField (MassGap.SUN.SU 2))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 < π₁) (hπ₂ : 0 < π₂)
    (hπκ : π₁ + π₂ < κ) (m₀ : ℕ) (R : ℝ) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 720000 →
      ∀ L : ℝ, 0 < L → PhysLinkOsc L δ →
      FacPixelAt hN c O t ℓ (physTower hN L) m₀ → FacOnePointAt hN c O t ℓ (physTower hN L) m₀ R →
      LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ →
      PhysVortex L ε → PhysRest L →
      ∀ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
        (ExistenceReduce.zCan_refl hN O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep hN
          (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
          (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
            (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) := by
  obtain ⟨δ₀, hδ₀, hth⟩ := crossing_threshold m₀ hπ₁ hπ₂ R
  refine ⟨δ₀, hδ₀, fun δ hδ hle ε hε hεle L hL hX hSP hS1 hF hV hR hD => ?_⟩
  obtain ⟨h1, hb₁, hb₂, -⟩ := hth δ hδ hle
  exact clay_canonical_phys hN O ht c hκ hπ₁.le hπ₂.le hπκ hL hX hδ h1 hb₁ hb₂ hSP hS1 hF hV hε
    (by linarith) hR hD

end Pinned

end MassGap.PhysicalScaleSmall

end

#print axioms MassGap.PhysicalScaleSmall.physSide_spec
#print axioms MassGap.PhysicalScaleSmall.eventually_physSide_le
#print axioms MassGap.PhysicalScaleSmall.integral_pos_of_forall_pos_prob
#print axioms MassGap.PhysicalScaleSmall.FE_sheet_le_of_ratio
#print axioms MassGap.PhysicalScaleSmall.physDens_pos
#print axioms MassGap.PhysicalScaleSmall.physDens_integrable
#print axioms MassGap.PhysicalScaleSmall.physVortex_iff
#print axioms MassGap.PhysicalScaleSmall.physVortex_of_physRatio
#print axioms MassGap.PhysicalScaleSmall.physSectorSeed_of_physVortex
#print axioms MassGap.PhysicalScaleSmall.defectW_phys_le
#print axioms MassGap.PhysicalScaleSmall.physSeed
#print axioms MassGap.PhysicalScaleSmall.runSeed_two_of_physSectorSeed
#print axioms MassGap.PhysicalScaleSmall.wDelta2_two_of_physVortex
#print axioms MassGap.PhysicalScaleSmall.wDelta2_two_of_physRatio
#print axioms MassGap.PhysicalScaleSmall.boundPixelT_of_linkOsc
#print axioms MassGap.PhysicalScaleSmall.boundOnePoint_of_linkOsc
#print axioms MassGap.PhysicalScaleSmall.clay_canonical_linkOsc_fac
#print axioms MassGap.PhysicalScaleSmall.physDens_banded
#print axioms MassGap.PhysicalScaleSmall.linkOsc_physTower
#print axioms MassGap.PhysicalScaleSmall.clay_canonical_two_phys
#print axioms MassGap.PhysicalScaleSmall.clay_canonical_phys
#print axioms MassGap.PhysicalScaleSmall.clay_canonical_phys_small
