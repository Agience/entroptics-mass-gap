import Mathlib
import MassGap.InputsG
import MassGap.LinkReduceG

/-!
# MassGap.ClayG — the `G` capstone at a general mixing

`clayStatementAtG_GS` is `ClayStatementG.clayStatementAtG_of_link` at

* `D := SymPlaqClassG G`, `τ := 0`, `X := InputsG.obsXG' …`, with `hSM`, `hH`, `hGen` from
  `obsXG'_SM`, `obsXG'_gap`, `obsXG'_obsGen`, and `ApertureConvG` from `ObserverOSG.uniformBoundFG_energy0G` and
  `ObserverLinkedG.tendsto_schwSFMG` under the class moments (`InputsG.cube_of_classMomentsG`,
  `InputsG.one_le_of_classMomentsG`);
* a general mixing `ρ`, with `hRie` on `ρ` and `hTie` the second conjunct of `ScalarTieG` (the
  first, `X.O = symG (plaqFieldG q0)`, holds by definition of `obsXG'`);
* `w := LinkReduce.wOfC e wC`, with `LinkHSG` from `LinkReduceG.linkHSG_of_comp`, `LinkTSG` from it
  and `SepConvG` (`ClayWiringG.linkTSG_of_hs`), `hnt` from `InputsG.hnt_of_gramG` at its Gram and
  vacuum conjuncts with `hK`, `hAF` and `schedShiftInv_canonSched`, `afConstG_pos`, and `TInG` from
  `LinkReduceG.tInG_of_comp`;
* `SepConvG`, `OS0SepG`, `OS1SepG` of `ρ` from `CompOSG` and the second clause of the index map
  `e`, and `TensorNondegG` from `CompOSG`, both clauses and an abelian generator `AbelianGenG G`
  (`CompReduceG.sepConvG_of_comp`, `os0SepG_of_comp`, `os1SepG_of_comp`, `tensorNondegG_of_comp`);
* `TopNormG` from `ChannelTieG` and the limit of the identity component
  (`LinkReduceG.topNormG_of_channelTie`).

The transfer gap of the observer at step `0` (`hρ0`, `hρ1`, `hg`) is an input.

DERIVED (module-wide): `0` the plane and the step; `4` the dimension.
-/

noncomputable section

namespace MassGap.ClayG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.InputsG MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- **`ClayStatementAtG G W (SymPlaqClassG G)` from the observer inputs over `G`, its transfer gap,
a general mixing `ρ` with its Riemann symmetries, trace tie, covariance and channel tie, the kernel
`Gk`, the three-point and Ward clauses of `ρ`, the composites `Cs` with their data, analytic clauses
and link `wC`, the two clauses of an index map `e`, the cross reading of `wOfC e wC`, and an abelian
generator `AbelianGenG G`.** The trace and channel ties reach `(constsG G).cTr`, `(constsG G).cTop`
at the spacings `(canonSched G).a k`. -/
theorem clayStatementAtG_GS (W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ₀)
    (ρ : RenormMixG G) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := G) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (canonSched G).a k ^ 4) atTop (𝓝 (constsG G).cTr))
    (hCov : TensorCovG (canonSched G) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (canonSched G).a k ^ 4) atTop
          (𝓝 (constsG G).cTop))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (canonSched G) ρ Gk) (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (canonSched G) ρ) (hWard : WardTG (canonSched G) ρ)
    (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → (obsXG' W ht hU hphys hNT hρ0 hρ1 hg).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompDataG Cs) (hCO : CompOSG (canonSched G) Cs)
    (hLC : LinkCG (canonSched G) (obsXG' W ht hU hphys hNT hρ0 hρ1 hg) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (canonSched G) ρ
          (energyMapG (canonSched G) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) ((obsXG' W ht hU hphys hNT hρ0 hρ1 hg).cvec Q)
          = (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ))
    (hab : AbelianGenG G) :
    ClayStatementAtG G W (SymPlaqClassG G) := by
  have hConv := sepConvG_of_comp (canonSched G) ρ Cs e he2 hCO.1
  have hHS := linkHSG_of_comp (canonSched G) W (SymPlaqClassG G) _ ρ Cs wC hLC e he1 he2 hX
  obtain ⟨Mb, Zc, hCT1, hCT2⟩ := hCT
  exact clayStatementAtG_of_link W (SymPlaqClassG G) (obsXG' W ht hU hphys hNT hρ0 hρ1 hg) ρ Gk
    (wOfC e wC)
    (obsXG'_SM W ht hU hphys hNT hρ0 hρ1 hg)
    (obsXG'_gap W ht hU hphys hNT hρ0 hρ1 hg)
    hRie ⟨rfl, hTie⟩ hConv
    (os0SepG_of_comp _ ρ Cs e he2 hCO.1 hCO.2.1)
    (os1SepG_of_comp _ ρ Cs e he2 hCO.1 hCO.2.2.1) hCov
    (linkTSG_of_hs _ W (SymPlaqClassG G) _ ρ _ hConv hHS)
    (hnt_of_gramG (canonSched G) schedShiftInv_canonSched (constsG G) (afConstG_pos G) _ ρ _
      hHS.1 hHS.2.2.1 Gk hK hAF)
    hK hAF hNG
    (tensorNondegG_of_comp _ ρ Cs e he1 he2 hCO.1 hCO.2.2.2.2 hab)
    ⟨uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU),
      fun ι _ O hO g => tendsto_schwSFMG (canonSched G) W symPlaqG_nonneg ht
        (zero_le_one.trans (one_le_of_classMomentsG (canonSched G) W symPlaqG_q0 hU)) hU O hO g⟩
    Cs wC ⟨Mb, Zc, hCT1, topNormG_of_channelTie _ _ ρ Mb Zc hCT1 hCT2⟩ hWard hCD hCO hLC
    (tInG_of_comp _ ρ Cs wC e he1 he2)
    (obsXG'_obsGen W ht hU hphys hNT hρ0 hρ1 hg)

end MassGap.ClayG

end

#print axioms MassGap.ClayG.clayStatementAtG_GS
