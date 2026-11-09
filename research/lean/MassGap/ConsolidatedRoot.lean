import Mathlib
import MassGap.ConstantPhysicsLine
import MassGap.SUNFromScale

/-!
# MassGap.ConsolidatedRoot — the root statement at `SU(N)` with every proved existence clause discharged

`ConstantPhysicsLine.clayStatementOf_of_reads` derives `ClayStatementOf (SU N)` from `StrongEnd N`, (UV) along the
coupling towers near `0⁺`, and `ExistAlong N βs` along those towers: seventeen `Prop` clauses with free
witnesses, counting `0 < t` and the index clauses `he1`, `he2`. Five of them (`hphys`, `hRie`, `hTie`, `hCT`,
`hCD`) read the schedule only through its spacing `a_k = dySpacingG (SU N) k`, which is the same at every measured
tower `βs` (`schedAlongG` changes the state, never the spacing), or read no schedule at all. For those the proofs
of the `SU(N)` chain at the frozen tower (`CompositesRenAll.clayStatementAt_SU_ren_low`) hold along every `βs` at
the witnesses that chain uses. A sixth, `hCov`, reads the state; it is reduced to `CompOSG` of the composites
`hCO` (`CompReduceG.tensorCovG_of_comp`). This module fixes those witnesses, discharges the five and the index
clauses, and reduces `hCov` to `hCO`. Declarations are in the namespace `MassGap.ConsolidatedRoot`.

## The witnesses

* The observer `W = sunFam hN2 c hc0 hc s₀` (`ObserverFlowSUN`, the `SU(N)` block-step flow at scale `s₀`), the
  observer of `SUNFromScale.FlowInputsN`.
* The mixing `rhoZ N zri zwe = rhoD (fR N) (zFix N zri zwe)`: scalar and pseudoscalar factors `2/a_k⁴`
  (`ZCanon.zFix`), traceless-Ricci and Weyl factors `zri`, `zwe` free.
* The composites `csZ N zri zwe μ = CRen N (zFix N zri zwe) μ` (`CompositesRen`) with the tensor index map `eI`.

## What is proved along every `βs`

* `physRange_sunFam` (`hphys`): `sunFam` has physical range `r > s₀` (`ObserverFlowSUN.sunFam_physRange`).
* `riemann_rhoZ` (`hRie`): `ClayWiring.riemann_mixOfZ`, `ClayData.coefRiemann_mD`.
* `tie_rhoZ` (`hTie`): `ClayData.scalarTie_D` with `ZCanon.tendsto_zFix_sc`.
* `channel_rhoZ` (`hCT`): `ClayData.channelTie_D` with `ZCanon.tendsto_zFix_ps`, `ReflAvg.tiedB_R`.
* `compData_csZ` (`hCD`): `CompositesRen.buildRen_compData` with `ClayData.renTensor_D`.
* `tensorCov_rhoZ` (`hCov`): from `CompOSG` of the composites (`CompReduceG.tensorCovG_of_comp`, the
  representation `CompositesRen.buildRen_hrep`).
* The index clauses `he1`, `he2`: `CompositesRen.buildRen_he1`, `buildRen_he2`.

## The open statement and the capstones

* `OpenAlong N βs`: at the witnesses, the clauses of `ExistAlong` that read the state `periodicStateG (βs k)`:
  the class moments `hU`, the two-point kernel with its asymptotic-freedom coefficient `hK`, `hAF`,
  non-Gaussianity `hNG`, the Ward identity `hWard`, `CompOSG` of the composites `hCO`, and the link `wC`, `hLC`,
  `hX`. `existAlong_of_open`: `OpenAlong N βs ⇒ ExistAlong N βs`.
* `clayStatementOf_of_open`: `StrongEnd N`, (UV) and `OpenAlong` along the towers near `0⁺` give
  `ClayStatementOf (SU N)`. The transfer gap holds under `u₀ ≤ …` along a coupling tower, whose existence near
  `0⁺` still requires `StrongEnd N` (open).
* `clayStatementOf_of_flow`: at the frozen tower the whole existence side is the bundle
  `SUNFromScale.FlowInputsN N` already in the tree (a conjunction of five clauses); with asymptotic scaling
  `AsymScalingG (SU N) R` it gives `ClayStatementOf (SU N)` (`MeasuredSpacing.clayStatementMeasOf_of_of`).

DERIVED (module-wide): `0` the plane, the time axis and the signs; `2` the least rank; `4` the dimension;
`π` in `π/N`, the angle of the centre of `SU(N)` (from the group); `12` a sufficient bound on the construction
parameter `c` of the block step (`ObserverFlowSUN.det_blockMatN_mem_slitPlane`: six staples, `12 c < sin(π/N)`),
with `c` existential and `c = 0` allowed; `1` the least rank of the spacing, proof-internal.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ConsolidatedRoot

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.InputsG MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG MassGap.SUInputs
  MassGap.ClayGFinal Filter
open scoped Topology Matrix
open MassGap.MeasuredTower (schedAlongG MeasTowerG AsymScalingG)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.ObserverFlowSUN (sunFam)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

omit [NeZero N] in
private theorem one_le : 1 ≤ N := le_trans one_le_two (Fact.out : 2 ≤ N)

/-- The spacing of the schedule along any tower is the `SU(N)` dyadic spacing. DERIVED: no numeral. -/
private theorem a_along (βs : ℕ → ℝ) (k : ℕ) :
    (schedAlongG (MassGap.SUN.SU N) βs).a k = dySpacing N k :=
  congrFun (dySpacingG_SU N) k

variable (N) in
/-- **The mixing**: `rhoD (fR N)` at the channel factors `zFix N zri zwe`. DERIVED: no numeral. -/
abbrev rhoZ (zri zwe : ℕ → ℝ) : RenormMixG (MassGap.SUN.SU N) :=
  (ClayData.rhoD (ReflAvg.fR N) (ZCanon.zFix N zri zwe)).toG

variable (N) in
/-- **The composites**: `CRen N (zFix N zri zwe) μ`. DERIVED: no numeral. -/
abbrev csZ (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) : CompositesG (MassGap.SUN.SU N) :=
  (CompositesRen.CRen N (ZCanon.zFix N zri zwe) μ).toG

variable (N) in
/-- **The observer**: the `SU(N)` block-step flow at scale `s₀`. DERIVED: `0` the sign of `c`; `2` the least
rank; `π` in `π/N` the angle of the centre of `SU(N)`; `12` a sufficient bound on `c`. -/
abbrev obsW {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ : ℝ) :
    ConfFlowG (MassGap.SUN.SU N) :=
  (sunFam (Fact.out : 2 ≤ N) c hc0 hc s₀).toG

/-! ## 1. The clauses proved at every tower -/

/-- **`hphys` along every tower.** DERIVED: `0` the signs of `c` and `s₀`; `2` the least rank; `π` in `π/N` the
angle of the centre of `SU(N)`; `12` a sufficient bound on `c`. -/
theorem physRange_sunFam (βs : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    {s₀ r : ℝ} (hs0 : 0 ≤ s₀) (hr : s₀ < r) :
    (energy0G (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqClassG (MassGap.SUN.SU N))
      (symPlaqG_refl (MassGap.SUN.SU N))).PhysRange (schedAlongG _ βs) r := by
  have h := ObserverFlowSUN.sunFam_physRange (Fact.out : 2 ≤ N) hc0 hc hs0 hr
  filter_upwards [h] with k hk
  show (schedAlongG (MassGap.SUN.SU N) βs).a k * ((sunFam (Fact.out : 2 ≤ N) c hc0 hc s₀).range k : ℝ) ≤ r
  rw [a_along βs k]
  exact hk

omit [Fact (2 ≤ N)] in
/-- **`hRie`.** DERIVED: no numeral. -/
theorem riemann_rhoZ (zri zwe : ℕ → ℝ) : (rhoZ N zri zwe).Riemann :=
  ClayWiring.riemann_mixOfZ (ClayData.opD (ReflAvg.fR N)) (ClayData.mD N)
    (ClayData.ZD (ZCanon.zFix N zri zwe)) (ClayData.coefRiemann_mD N)

set_option maxRecDepth 100000 in
/-- **`hTie` along every tower.** DERIVED: `2` the least rank; `4` the dimension. -/
theorem tie_rhoZ (βs : ℕ → ℝ) (zri zwe : ℕ → ℝ) :
    ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG (rhoZ N zri zwe) k trC b • ((rhoZ N zri zwe).op b).1
        = Ztr k • (symG (plaqFieldG (G := MassGap.SUN.SU N) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (schedAlongG (MassGap.SUN.SU N) βs).a k ^ 4) atTop
          (𝓝 (constsG (MassGap.SUN.SU N)).cTr) := by
  obtain ⟨-, Ztr, h1, h2⟩ := ClayData.scalarTie_D (NeZero.ne N) (ReflAvg.fR N) (ZCanon.zFix N zri zwe)
    (ZCanon.tendsto_zFix_sc one_le zri zwe)
  refine ⟨Ztr, h1, ?_⟩
  rw [constsG_SU N]
  exact h2.congr fun k => by rw [a_along βs k]

set_option maxRecDepth 100000 in
/-- **`hCT` along every tower.** DERIVED: `2` the least rank; `4` the dimension. -/
theorem channel_rhoZ (βs : ℕ → ℝ) (zri zwe : ℕ → ℝ) :
    ∃ (Mb : Idx4 → (rhoZ N zri zwe).B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (rhoZ N zri zwe) Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (schedAlongG (MassGap.SUN.SU N) βs).a k ^ 4) atTop
          (𝓝 (constsG (MassGap.SUN.SU N)).cTop) := by
  obtain ⟨Mb, Zc, h1, h2⟩ := ClayData.channelTie_D (ReflAvg.fR N) (ReflAvg.bR N) (ZCanon.zFix N zri zwe)
    (ZCanon.tendsto_zFix_ps one_le zri zwe) (ReflAvg.tiedB_R (NeZero.ne N))
  refine ⟨Mb, Zc, h1, ?_⟩
  rw [constsG_SU N]
  exact h2.congr fun k => by rw [a_along βs k]

/-- **`hCD`.** DERIVED: `0` the excluded factor value; `2` the least rank. -/
theorem compData_csZ {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0)
    (μ : CompositesRen.OffMix) : CompDataG (csZ N zri zwe μ) :=
  CompositesRen.buildRen_compData _ _ μ one_le (ReflAvg.tiedB_R (NeZero.ne N))
    (ClayData.renTensor_D (NeZero.ne N) (ReflAvg.fR N) (ReflAvg.bR N) _ (ZCanon.zFix_ne one_le hri hwe))

omit [Fact (2 ≤ N)] in
/-- **`he1`.** DERIVED: `0`, `1`, `2`, `3` the slots of the index. -/
theorem he1_csZ (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) (α : Idx4) :
    (csZ N zri zwe μ).cl (CompositesBuild.eI α) = [([([], α 0, α 1), ([], α 2, α 3)], true)] :=
  CompositesRen.buildRen_he1 (ClayData.rhoD (ReflAvg.fR N) (ZCanon.zFix N zri zwe))
    (ClayData.bareD (ReflAvg.fR N) (ReflAvg.bR N)) μ α

omit [Fact (2 ≤ N)] in
/-- **`he2`.** DERIVED: no numeral. -/
theorem he2_csZ (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) (k : ℕ) (α : Idx4) :
    ((csZ N zri zwe μ).ren k (CompositesBuild.eI α)).1
      = ∑ b, (rhoZ N zri zwe).M k α b • ((rhoZ N zri zwe).op b).1 :=
  CompositesRen.buildRen_he2 (ClayData.rhoD (ReflAvg.fR N) (ZCanon.zFix N zri zwe))
    (ClayData.bareD (ReflAvg.fR N) (ReflAvg.bR N)) μ k α

/-- **`hCov` along every tower, from `CompOSG` of the composites.** `hCov` reads the state; this reduces it to
`hCO`. DERIVED: `2` the least rank; `4` the dimension. -/
theorem tensorCov_rhoZ (βs : ℕ → ℝ) (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix)
    (hCO : CompOSG (schedAlongG _ βs) (csZ N zri zwe μ)) :
    TensorCovG (schedAlongG _ βs) (rhoZ N zri zwe) :=
  CompReduceG.tensorCovG_of_comp _ _ (csZ N zri zwe μ) CompositesBuild.eI
    (CompReduceG.e_injectiveG _ _ (he1_csZ zri zwe μ)) (he2_csZ zri zwe μ) hCO.1 hCO.2.2.2.1
    (fun R _ α => CompositesRen.buildRen_hrep
      (ClayData.rhoD (ReflAvg.fR N) (ZCanon.zFix N zri zwe))
      (ClayData.bareD (ReflAvg.fR N) (ReflAvg.bR N)) μ R α)

/-! ## 2. The open statement -/

variable (N) in
/-- **The clauses that read the state along `βs`**, at the witnesses of §1: some block-step observer
`obsW N hc0 hc s₀` with range `r > s₀`, class moments, channel factors `zri`, `zwe` nowhere zero, an off-tensor
mixing `μ`, a two-point kernel with its asymptotic-freedom coefficient, non-Gaussianity, the Ward identity,
`CompOSG` of the composites, and the link of the composites to the pre-observer with the cross reading.

DERIVED: `0` the plane, the time axis and the signs; `2` the least rank; `π` in `π/N` the angle of the centre
of `SU(N)`; `12` a sufficient bound on `c`; `4` the dimension. -/
def OpenAlong (βs : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (hs0 : 0 ≤ s₀) (hr : s₀ < r)
    (t C₀ : ℝ) (_ : 0 < t)
    (hU : ClassMomentsG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqClassG (MassGap.SUN.SU N)) t C₀)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : CompositesRen.OffMix)
    (_ : ∃ Gk : ℝ → ℝ, TwoPointKernelG (schedAlongG _ βs) (rhoZ N zri zwe) Gk
      ∧ AFCoefficientG (constsG (MassGap.SUN.SU N)) Gk)
    (_ : NonGaussianTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : WardTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : CompOSG (schedAlongG _ βs) (csZ N zri zwe μ))
    (wC : TSepG (csZ N zri zwe μ).Ix 0 → preHGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr)),
    LinkCPreG (schedAlongG _ βs) 0 (preVacGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr))
        (preTimeGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr)) (csZ N zri zwe μ) wC
      ∧ ∀ (P : TSep 0) (Q : MarginMonoDG (MassGap.SUN.SU N) (SymPlaqClassG (MassGap.SUN.SU N)) 0 r),
        Tendsto (fun k => mixLatTG (schedAlongG _ βs) (rhoZ N zri zwe)
            (energyMapG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqClassG (MassGap.SUN.SU N))) 0 k P.1 Q.1.1)
            (ultra : Filter ℕ)
            (𝓝 (mixTG (schedAlongG _ βs) (rhoZ N zri zwe)
              (energyMapG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqClassG (MassGap.SUN.SU N))) 0 P.1 Q.1.1))
          ∧ inner ℂ (wOfC CompositesBuild.eI wC P)
              (preCvecGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr) Q)
            = (mixTG (schedAlongG _ βs) (rhoZ N zri zwe)
                (energyMapG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqClassG (MassGap.SUN.SU N)))
                0 P.1 Q.1.1 : ℂ)

/-- **`OpenAlong ⇒ ExistAlong`**: the five spacing clauses of §1 and the index clauses are discharged, and
`hCov` is reduced to `hCO`. DERIVED: `2` the least rank. -/
theorem existAlong_of_open {βs : ℕ → ℝ} (h : OpenAlong N βs) : ConstantPhysicsLine.ExistAlong N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, t, C₀, ht, hU, zri, zwe, hri, hwe, μ, ⟨Gk, hK, hAF⟩, hNG, hWard, hCO, wC,
    hLC, hX⟩ := h
  exact ⟨obsW N hc0 hc s₀, t, C₀, ht, hU, r, physRange_sunFam βs hc0 hc hs0 hr, rhoZ N zri zwe,
    riemann_rhoZ zri zwe, tie_rhoZ βs zri zwe, tensorCov_rhoZ βs zri zwe μ hCO, channel_rhoZ βs zri zwe,
    Gk, hK, hAF, hNG, hWard, csZ N zri zwe μ, wC, CompositesBuild.eI, he1_csZ zri zwe μ, he2_csZ zri zwe μ,
    compData_csZ hri hwe μ, hCO, hLC, hX⟩

/-! ## 3. The capstones -/

/-- **The root at `SU(N)` from the strong end, (UV) and the state-reading clauses along the towers near `0⁺`.**
The transfer gap holds under `u₀ ≤ …` along a coupling tower, whose existence near `0⁺` is the open input
`hS`. DERIVED: `2` the least rank; `0` the limit `0⁺`. -/
theorem clayStatementOf_of_open (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ)
    (hO : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → OpenAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  ConstantPhysicsLine.clayStatementOf_of_reads hS hUV
    (hO.mono fun _ h βs hT => existAlong_of_open (h βs hT))

/-- **The root at `SU(N)` from the flow-side inputs and asymptotic scaling at the frozen tower.** Every
existence clause is derived from the bundle `SUNFromScale.FlowInputsN N` (through
`SUNBest.clayStatementSU_of_inputs`); the frozen tower is a measured tower under `AsymScalingG`
(`MeasuredSpacing.measTowerG_of_scaling`). DERIVED: `2` the least rank. -/
theorem clayStatementOf_of_flow (hF : SUNFromScale.FlowInputsN N (Fact.out : 2 ≤ N)) {R : ℝ}
    (hR : AsymScalingG (MassGap.SUN.SU N) R) : ClayStatementOf (MassGap.SUN.SU N) :=
  MeasuredSpacing.clayStatementMeasOf_of_of hR
    (SUNBest.clayStatementSU_of_inputs (Fact.out : 2 ≤ N)
      (SUNFromScale.clayInputsN_of_flow (Fact.out : 2 ≤ N) hF))

end MassGap.ConsolidatedRoot

end

#print axioms MassGap.ConsolidatedRoot.physRange_sunFam
#print axioms MassGap.ConsolidatedRoot.riemann_rhoZ
#print axioms MassGap.ConsolidatedRoot.tie_rhoZ
#print axioms MassGap.ConsolidatedRoot.channel_rhoZ
#print axioms MassGap.ConsolidatedRoot.compData_csZ
#print axioms MassGap.ConsolidatedRoot.he1_csZ
#print axioms MassGap.ConsolidatedRoot.he2_csZ
#print axioms MassGap.ConsolidatedRoot.tensorCov_rhoZ
#print axioms MassGap.ConsolidatedRoot.existAlong_of_open
#print axioms MassGap.ConsolidatedRoot.clayStatementOf_of_open
#print axioms MassGap.ConsolidatedRoot.clayStatementOf_of_flow
