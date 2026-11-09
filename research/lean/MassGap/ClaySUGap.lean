import Mathlib
import MassGap.ClaySU
import MassGap.ApertureInvariance

/-!
# The SU(N) capstone with the transfer gap as its input, and from the aperture bridge

`ClaySU.clayStatementAt_SU` takes `hfar : WDeltaRun.RunSeed N` and uses it only through
`SUInputs.gapEx'`: a rate `ρ ∈ (0, 1)` with `GapAt (transferN hN Φ hB 0 hphys 0) ρ` for
`Φ = energy0 W (SymPlaqClass N) (symPlaq_refl N)`, `hB = uB hN W hU`, the plane `0` and the step `0`.
This module states the capstone at that gap and at the aperture bridge.

* `obsXg` — `SUInputs.obsX'` with the gap `(ρ, hρ0, hρ1, hg)` in place of the choice from `gapEx'`
  (`ObserverOSLinked.observerOSDataSLinked` at the same arguments). `obsXe` — `obsXg` at the choice
  from an existential gap. `obsX'_eq_obsXe`: `obsX' … hfar = obsXe … (gapEx' … hfar)` by `rfl`.
* `obsXg_SM`, `obsXg_gap`, `obsXg_obsGen` — the companions of `obsX'_SM`, `obsX'_gap`,
  `obsX'_obsGen`, with the same proofs.
* `clayStatementAt_SU_gap` — `ClaySU.clayStatementAt_SU` with `hfar` replaced by `(ρ, hρ0, hρ1, hg)`
  and the inputs `wC`, `hLC`, `hX` typed at `obsXg`.
* `clayStatementAt_SU_of_runSeed` — the statement of `ClaySU.clayStatementAt_SU`, proved from
  `clayStatementAt_SU_gap` at the gap of `gapEx'`.
* `gapE_of_aperture` — `ApertureInvariance.gapAt_of_apertureInvariant` at `Φ`, `hB`, plane `0`,
  step `0`: its conclusion is the existential gap of `gapEx'` (same `transferN` arguments).
* `clayStatementAt_SU_aperture` — the capstone with the gap input replaced by the hypotheses of
  `gapAt_of_apertureInvariant` (a mass `M > 0`; apertures `Ap m P Q`; references `ref m P Q`; factors
  `Ca m P Q`; `KernelReads`, `ApertureInvariant`, `ClusterAt` at `M`), the inputs `wC`, `hLC`, `hX`
  typed at `obsXe … (gapE_of_aperture …)`.

The aperture inputs are hypotheses: no declaration constructs the aperture chains from the Wilson
measure (`KernelReads`), and `ApertureInvariant` against a clustering reference is the statement
that nothing changes from the coarse to the fine end; together they imply `FlowClusterAbs`, so this
input is the gap, carried in the owner's terms.

DERIVED (module-wide): `2` the least colour count; `0` the plane and the step; `8`, `4` as in
`ScalarTie` and `ClayStatement`.
-/

noncomputable section

namespace MassGap.ClaySUGap

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The observer at a given gap -/

section Observer

/-- The uniform bound of the flow `energy0 W (SymPlaqClass N) (symPlaq_refl N)` from the class
moments. DERIVED: no numeral. -/
theorem uB (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) :
    UniformBoundF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) :=
  uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
    (SUInputs.symPlaq_cube_of_classMoments hN W hU)

/-- **The observer at the field `sym (plaqField q0)`** from the class moments and a transfer gap
`GapAt (transferN hN Φ (uB hN W hU) 0 hphys 0) ρ`, `0 < ρ < 1`.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXg (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB hN W hU) 0 hphys 0) ρ) :
    OSDataSLinked N (SymPlaqClass N) 0 r :=
  observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
    (SUInputs.symPlaq_cube_of_classMoments hN W hU) ht
    (zero_le_one.trans (SUInputs.one_le_of_classMoments hN W hU))
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) SUInputs.q0_mem
    (SUInputs.unitCubeExpBound_of_cubeMomentsAt hN W ht (hU _ SUInputs.q0_mem)) 0 hphys 0 one_pos
    hρ0 hρ1 hg hNT

/-- `obsXg` at the rate chosen from an existential gap. DERIVED: `0` the plane and the step. -/
def obsXe (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hE : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB hN W hU) 0 hphys 0) ρ) :
    OSDataSLinked N (SymPlaqClass N) 0 r :=
  obsXg hN W ht hU hphys hNT (Classical.choose_spec hE).1 (Classical.choose_spec hE).2.1
    (Classical.choose_spec hE).2.2

/-- **`obsX'` is `obsXe` at the gap of `gapEx'`**, by definition. -/
theorem obsX'_eq_obsXe (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar
      = obsXe hN W ht hU hphys hNT (SUInputs.gapEx' hN2 hN W hU hphys hfar) :=
  rfl

/-- **The Hamiltonian gap of `obsXg`**, from its self-adjoint generator.

DERIVED: `0` the plane. -/
theorem obsXg_gap (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB hN W hU) 0 hphys 0) ρ) :
    HamiltonianGap (obsXg hN W ht hU hphys hNT hρ0 hρ1 hg).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjoint hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0))

/-- **The functional of `obsXg` is `schwSFM`**, by definition. DERIVED: no numeral. -/
theorem obsXg_SM (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB hN W hU) 0 hphys 0) ρ) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      (obsXg hN W ht hU hphys hNT hρ0 hρ1 hg).SM O g
        = schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g :=
  fun _ _ _ _ => rfl

/-- **`obsXg` carries its Hilbert space** (`ClayStatement.obsGen_observer`).

DERIVED: `0` the plane and the step; `1` the window. -/
theorem obsXg_obsGen (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB hN W hU) 0 hphys 0) ρ) :
    ObsGen hN W (SymPlaqClass N) (symPlaq_refl N) (obsXg hN W ht hU hphys hNT hρ0 hρ1 hg) :=
  obsGen_observer hN W (symPlaq_refl N) (symPlaq_nonneg hN)
    (SUInputs.symPlaq_cube_of_classMoments hN W hU) ht
    (zero_le_one.trans (SUInputs.one_le_of_classMoments hN W hU))
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) SUInputs.q0_mem
    (SUInputs.unitCubeExpBound_of_cubeMomentsAt hN W ht (hU _ SUInputs.q0_mem)) 0 hphys 0 one_pos
    hρ0 hρ1 hg hNT

end Observer

/-! ## 2. The capstone at a given gap -/

section Gap

/-- **`ClayStatementAt` at `SymPlaqClass N` from the inputs of `ClaySU.clayStatementAt_SU` with
`hfar` replaced by a rate `ρg ∈ (0, 1)` and `GapAt (transferN hN Φ (uB hN W hU) 0 hphys 0) ρg`**;
`wC`, `hLC`, `hX` are typed at `obsXg`. -/
theorem clayStatementAt_SU_gap (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    {ρg : ℝ} (hρ0 : 0 < ρg) (hρ1 : ρg < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB (ne_zero_of_two_le hN2) W hU) 0 hphys 0) ρg)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0
      → (obsXg (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkC (ne_zero_of_two_le hN2)
      (obsXg (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            ((obsXg (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg).cvec Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hConv := CompReduce.sepConv_of_comp (ne_zero_of_two_le hN2) ρ Cs e he2 hCO.1
  have hHS := LinkReduce.linkHS_of_comp (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) _ ρ Cs wC hLC e he1 he2 hX
  obtain ⟨Mb, Zc, hCT1, hCT2⟩ := hCT
  exact clayStatementAt_of_link hN2 W (SymPlaqClass N) (symPlaq_refl N)
    (obsXg (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg) ρ G
    (LinkReduce.wOfC e wC)
    (obsXg_SM (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg)
    (obsXg_gap (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg)
    hRie ⟨rfl, hTie⟩ hConv
    (CompReduce.os0Sep_of_comp _ ρ Cs e he2 hCO.1 hCO.2.1)
    (CompReduce.os1Sep_of_comp _ ρ Cs e he2 hCO.1 hCO.2.2.1) hCov
    (linkTS_of_hs _ W (SymPlaqClass N) (symPlaq_refl N) _ ρ _ hConv hHS)
    (SUInputs.hnt_of_gram hN2 (ne_zero_of_two_le hN2) _ ρ _ hHS.1 hHS.2.2.1 G hK hAF)
    hK hAF hNG
    (CompReduce.tensorNondeg_of_comp _ hN2 ρ Cs e he1 he2 hCO.1 hCO.2.2.2.2)
    ⟨uB (ne_zero_of_two_le hN2) W hU,
      CutSU.cut_of_classMoments (ne_zero_of_two_le hN2) W ht
        (zero_le_one.trans (SUInputs.one_le_of_classMoments (ne_zero_of_two_le hN2) W hU)) hU⟩
    Cs wC ⟨Mb, Zc, hCT1, LinkReduce.topNorm_of_channelTie ρ Mb Zc hCT1 hCT2⟩ hWard hCD hCO hLC
    (LinkReduce.tIn_of_comp _ ρ Cs wC e he1 he2)
    (obsXg_obsGen (ne_zero_of_two_le hN2) W ht hU hphys hNT hρ0 hρ1 hg)

/-- **The statement of `ClaySU.clayStatementAt_SU`, from `clayStatementAt_SU_gap`** at the rate and
gap that `SUInputs.gapEx'` gives from `hfar`. -/
theorem clayStatementAt_SU_of_runSeed (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0
      → (SUInputs.obsX' hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkC (ne_zero_of_two_le hN2)
      (SUInputs.obsX' hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            ((SUInputs.obsX' hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar).cvec Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_gap hN2 W ht hU hphys hNT
    (Classical.choose_spec (SUInputs.gapEx' hN2 (ne_zero_of_two_le hN2) W hU hphys hfar)).1
    (Classical.choose_spec (SUInputs.gapEx' hN2 (ne_zero_of_two_le hN2) W hU hphys hfar)).2.1
    (Classical.choose_spec (SUInputs.gapEx' hN2 (ne_zero_of_two_le hN2) W hU hphys hfar)).2.2
    ρ hRie hTie hCov hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hLC hX

end Gap

/-! ## 3. The capstone from the aperture bridge -/

section Aperture

/-- **The transfer gap of this observer from the aperture bridge**:
`ApertureInvariance.gapAt_of_apertureInvariant` at `Φ = energy0 W (SymPlaqClass N) (symPlaq_refl N)`,
`hB = uB hN W hU`, the plane `0` and the step `0`.

DERIVED: `0` the plane and the step. -/
theorem gapE_of_aperture (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r M : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) (hM : 0 < M)
    (Ap : ℕ → MarginMono N 0 r → MarginMono N 0 r → ApertureFixed.ApertureReading)
    (ref : ∀ m P Q, ApertureFixed.ReadingChain (Fin (Ap m P Q).K → (Ap m P Q).Y))
    (Ca : ℕ → MarginMono N 0 r → MarginMono N 0 r → ℝ)
    (hrep : ∀ m P Q, ∃ D, ApertureInvariance.KernelReads hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 m P Q (Ap m P Q) D)
    (hinv : ∀ m P Q, ApertureInvariance.ApertureInvariant (Ap m P Q) (ref m P Q) (Ca m P Q))
    (hcl : ∀ m P Q, ApertureInvariance.ClusterAt (ref m P Q) M (Ap m P Q).slab) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (uB hN W hU) 0 hphys 0) ρ :=
  ApertureInvariance.gapAt_of_apertureInvariant hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
    (uB hN W hU) 0 hphys hM Ap ref Ca hrep hinv hcl 0

/-- **`ClayStatementAt` at `SymPlaqClass N` from the inputs of `clayStatementAt_SU_gap` with the gap
replaced by the hypotheses of `ApertureInvariance.gapAt_of_apertureInvariant` at the plane `0`**: a
mass `M > 0`, apertures `Ap m P Q` reading the connected flowed lattice kernels of `Φ`
(`KernelReads`), each `ApertureInvariant` against a reference `ref m P Q` at the factor `Ca m P Q`,
each reference `ClusterAt` at `M`. `wC`, `hLC`, `hX` are typed at `obsXe … (gapE_of_aperture …)`. -/
theorem clayStatementAt_SU_aperture (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    {M : ℝ} (hM : 0 < M)
    (Ap : ℕ → MarginMono N 0 r → MarginMono N 0 r → ApertureFixed.ApertureReading)
    (ref : ∀ m P Q, ApertureFixed.ReadingChain (Fin (Ap m P Q).K → (Ap m P Q).Y))
    (Ca : ℕ → MarginMono N 0 r → MarginMono N 0 r → ℝ)
    (hrep : ∀ m P Q, ∃ D, ApertureInvariance.KernelReads (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 m P Q (Ap m P Q) D)
    (hinv : ∀ m P Q, ApertureInvariance.ApertureInvariant (Ap m P Q) (ref m P Q) (Ca m P Q))
    (hcl : ∀ m P Q, ApertureInvariance.ClusterAt (ref m P Q) M (Ap m P Q).slab)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0
      → (obsXe (ne_zero_of_two_le hN2) W ht hU hphys hNT
          (gapE_of_aperture (ne_zero_of_two_le hN2) W hU hphys hM Ap ref Ca hrep hinv hcl)).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkC (ne_zero_of_two_le hN2)
      (obsXe (ne_zero_of_two_le hN2) W ht hU hphys hNT
        (gapE_of_aperture (ne_zero_of_two_le hN2) W hU hphys hM Ap ref Ca hrep hinv hcl)) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            ((obsXe (ne_zero_of_two_le hN2) W ht hU hphys hNT
              (gapE_of_aperture (ne_zero_of_two_le hN2) W hU hphys hM Ap ref Ca hrep hinv hcl)).cvec Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_gap hN2 W ht hU hphys hNT
    (Classical.choose_spec
      (gapE_of_aperture (ne_zero_of_two_le hN2) W hU hphys hM Ap ref Ca hrep hinv hcl)).1
    (Classical.choose_spec
      (gapE_of_aperture (ne_zero_of_two_le hN2) W hU hphys hM Ap ref Ca hrep hinv hcl)).2.1
    (Classical.choose_spec
      (gapE_of_aperture (ne_zero_of_two_le hN2) W hU hphys hM Ap ref Ca hrep hinv hcl)).2.2
    ρ hRie hTie hCov hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hLC hX

end Aperture

end MassGap.ClaySUGap

end

#print axioms MassGap.ClaySUGap.obsX'_eq_obsXe
#print axioms MassGap.ClaySUGap.obsXg_gap
#print axioms MassGap.ClaySUGap.gapE_of_aperture
#print axioms MassGap.ClaySUGap.clayStatementAt_SU_gap
#print axioms MassGap.ClaySUGap.clayStatementAt_SU_of_runSeed
#print axioms MassGap.ClaySUGap.clayStatementAt_SU_aperture
