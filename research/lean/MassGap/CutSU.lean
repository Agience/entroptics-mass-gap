import Mathlib
import MassGap.ClayWiring

/-!
# The SU(N) capstone without the cut-off input

`ClayWiring.clayStatementAt_of_inputs` takes `hCut`: for fields in `SymPlaqClass N` and decaying
`g`, `contSF (Oᵢ, cut gᵢ R) → schwSFM O g` as `R → ∞`. That convergence is
`ObserverOSEuclidS.tendsto_schwSFM` at `D = SymPlaqClass N`, from the class moments `hU`, the
reflection closure `symPlaq_refl N` and the non-negativity `symPlaq_nonneg hN`.

* `cut_of_classMoments` — the `hCut` statement from `ht`, `hC0`, `hU`.
* `clayStatementAt_of_inputs'` — `ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N)` from the
  hypotheses of `clayStatementAt_of_inputs` with `hCut` removed.
-/

noncomputable section

namespace MassGap.CutSU

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-- **The cut-off convergence on `SymPlaqClass N`** from the class moments: for fields in
`SymPlaqClass N` and decaying `g`, `contSF (Oᵢ, cut gᵢ R) → schwSFM O g` as `R → ∞`. -/
theorem cut_of_classMoments (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)),
      (∀ i, O i ∈ SymPlaqClass N) → ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g)) :=
  fun _ _ O hO g =>
    tendsto_schwSFM hN W (symPlaq_refl N) (symPlaq_nonneg hN) ht hC0 hU O hO g

/-- **`ClayStatementAt` from the inputs of `clayStatementAt_of_inputs` without `hCut`.** The cut-off
convergence is `cut_of_classMoments` from `ht`, `hC0`, `hU`. -/
theorem clayStatementAt_of_inputs' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z) (hTC : TransContT hN (mixOfZ B op m Z))
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (w : TSep 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hL : LinkHS hN W (SymPlaqClass N) (symPlaq_refl N)
      (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) (mixOfZ B op m Z) w)
    (hnt : ∃ u ∈ HLs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w,
      inner ℂ (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.vac u = 0 ∧ u ≠ 0)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) Cs wC)
    (hTI : TIn (mixOfZ B op m Z) Cs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_of_inputs hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar op m Z hZ hD hRie b0 κ
    htr hop hZtie h0 hTC hCov G hK hAF hNG hND (cut_of_classMoments hN W ht hC0 hU) w hL hnt Cs wC
    hCT hWard hCD hCO hLC hTI

end MassGap.CutSU

end

#print axioms MassGap.CutSU.cut_of_classMoments
#print axioms MassGap.CutSU.clayStatementAt_of_inputs'
