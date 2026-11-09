import Mathlib
import MassGap.CompReduce
import MassGap.LinkReduce

/-!
# The SU(N) capstone at a general mixing

`clayStatementAt_SU` is `ClayStatement.clayStatementAt_of_link` at

* `D := SymPlaqClass N`, `τ := 0`, `X := SUInputs.obsX' …`, with `hSM`, `hH`, `hGen` from
  `obsX'_SM`, `obsX'_gap`, `obsX'_obsGen` and `hAC` from `uniformBoundF_energy0` and
  `CutSU.cut_of_classMoments`;
* a general mixing `ρ`, with `hRie` on `ρ` and `hTie` the second conjunct of `ScalarTie ρ` (the first,
  `X.O = sym (plaqField q0)`, holds by definition of `obsX'`);
* `w := LinkReduce.wOfC e wC`, with `LinkHS` from `LinkReduce.linkHS_of_comp`, `LinkTS` from it and
  `SepConv` (`ClayWiring.linkTS_of_hs`), `hnt` from `SUInputs.hnt_of_gram` at its Gram and vacuum
  conjuncts with `hK`, `hAF`, and `TIn` from `LinkReduce.tIn_of_comp`;
* `SepConv`, `OS0Sep`, `OS1Sep` of `ρ` from `CompOS` and the second clause of the index map `e`, and
  `TensorNondeg` from `CompOS` and both clauses (`CompReduce.sepConv_of_comp`, `os0Sep_of_comp`,
  `os1Sep_of_comp`, `tensorNondeg_of_comp`);
* `TopNorm` from `ChannelTie` and the limit of the identity component
  (`LinkReduce.topNorm_of_channelTie`).

`N ≠ 0` is `ne_zero_of_two_le hN2`.

DERIVED (module-wide): `2` the least colour count and the limit of `TopNorm`; `0` the plane;
`8`, `4` as in `ScalarTie`.
-/

noncomputable section

namespace MassGap.ClaySU

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-- **`ClayStatementAt` at `SymPlaqClass N` from the observer inputs, a general mixing `ρ` with its
Riemann symmetries, trace tie, covariance and channel tie, the kernel `G`, the three-point and Ward
clauses of `ρ`, the composites `Cs` with their data, analytic clauses and link `wC`, the two clauses of
an index map `e`, and the cross reading of `wOfC e wC`.** -/
theorem clayStatementAt_SU (hN2 : 2 ≤ N) (W : ConfFlow N)
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
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hConv := CompReduce.sepConv_of_comp (ne_zero_of_two_le hN2) ρ Cs e he2 hCO.1
  have hHS := LinkReduce.linkHS_of_comp (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) _ ρ Cs wC hLC e he1 he2 hX
  obtain ⟨Mb, Zc, hCT1, hCT2⟩ := hCT
  exact clayStatementAt_of_link hN2 W (SymPlaqClass N) (symPlaq_refl N)
    (SUInputs.obsX' hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar) ρ G
    (LinkReduce.wOfC e wC)
    (SUInputs.obsX'_SM hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar)
    (SUInputs.obsX'_gap hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar)
    hRie ⟨rfl, hTie⟩ hConv
    (CompReduce.os0Sep_of_comp _ ρ Cs e he2 hCO.1 hCO.2.1)
    (CompReduce.os1Sep_of_comp _ ρ Cs e he2 hCO.1 hCO.2.2.1) hCov
    (linkTS_of_hs _ W (SymPlaqClass N) (symPlaq_refl N) _ ρ _ hConv hHS)
    (SUInputs.hnt_of_gram hN2 (ne_zero_of_two_le hN2) _ ρ _ hHS.1 hHS.2.2.1 G hK hAF)
    hK hAF hNG
    (CompReduce.tensorNondeg_of_comp _ hN2 ρ Cs e he1 he2 hCO.1 hCO.2.2.2.2)
    ⟨uniformBoundF_energy0 (ne_zero_of_two_le hN2) W (SymPlaqClass N) (symPlaq_refl N)
        (symPlaq_nonneg (ne_zero_of_two_le hN2))
        (SUInputs.symPlaq_cube_of_classMoments (ne_zero_of_two_le hN2) W hU),
      CutSU.cut_of_classMoments (ne_zero_of_two_le hN2) W ht
        (zero_le_one.trans (SUInputs.one_le_of_classMoments (ne_zero_of_two_le hN2) W hU)) hU⟩
    Cs wC ⟨Mb, Zc, hCT1, LinkReduce.topNorm_of_channelTie ρ Mb Zc hCT1 hCT2⟩ hWard hCD hCO hLC
    (LinkReduce.tIn_of_comp _ ρ Cs wC e he1 he2)
    (SUInputs.obsX'_obsGen hN2 (ne_zero_of_two_le hN2) W ht hU hphys hNT hfar)

end MassGap.ClaySU

end

#print axioms MassGap.ClaySU.clayStatementAt_SU
