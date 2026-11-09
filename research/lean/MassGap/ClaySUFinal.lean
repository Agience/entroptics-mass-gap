import Mathlib
import MassGap.OneBridge
import MassGap.CompReduce
import MassGap.FlowUV
import MassGap.LocalLink

/-!
# MassGap.ClaySUFinal — the SU(N) capstone with the proved reductions wired in

`OneBridgeSU.clayStatementAt_SU_noNT_gap` takes a gap `hρ0`, `hρ1`, `hg` at step `0`, the tensor
covariance `hCov`, the class moments `hU`, and the Riemann and scalar ties `hRie`, `hTie` of the mixing
`ρ`. This module discharges the ones a proved reduction gives:

* `hρ0`, `hρ1`, `hg` from `RunSeed N` (`LocalLink.observerGapAt_of_runSeed` at `preB hN W hU`, step `0`);
* `hCov` from `hrep` (`CompReduce.tensorCov_of_comp`, with `ConvC = hCO.1`, `CovC = hCO.2.2.2.1` and
  `e` injective from `he1`, `CompReduce.e_injective`);
* `hU` from `SiteExp` on `SymPlaqClass N` at strength `625 t`
  (`FlowUV.classUnitExp_of_siteExp`, then `ObserverMoments.symMoments_of_classUnitExp`; the constant
  becomes `|C|`): `classMoments_of_siteExp`;
* `hRie`, `hTie` at `ρ = mixOfZ B op m Z` from `CoefRiemann m` and the trace data `b0`, `κ`, `htr`,
  `hop`, `hZtie` (`ClayWiring.riemann_mixOfZ`, `ClayWiring.scalarTie_mixOfZ`).

## The theorems

* `clayStatementAt_SU_final` — general `ρ`; `RunSeed N` for the gap, `hrep` for `hCov`; `hU` kept as
  `ClassMoments` (the weakest moment input; `SiteExp` implies it).
* `clayStatementAt_SU_final_siteExp` — the same with `hU` from `SiteExp`.
* `clayStatementAt_SU_final_mixOfZ` — the same with `ρ = mixOfZ B op m Z`, `hRie`, `hTie` from the
  coefficient data.
* `clayStatementAt_SU2_fixedDiffraction`, `clayStatementAt_SU2_fixedDiffraction_mixOfZ` — `N = 2` with
  `RunSeed 2` from `ApertureGap.FixedDiffraction mD CD d` (`ApertureGap.runSeed_of_fixedDiffraction`).

## Why `hRie`, `hTie` stay inputs of the general theorem

`mixOfZ B op m Z` has `M k α b = m α b · Z k (op b)`: every basis field carries one step factor, the
same in every index `α`. A `RenormMix` whose mixing at a basis field has different step dependence in
different `α` (for instance `ChannelTie`'s `M k α b = ∑_β Zc k α β · Mb β b` with `Zc k` not diagonal
in a basis where each field sits in one channel) is not of that form. So the `mixOfZ` theorem is a
specialisation of the general one, and the general theorem keeps `hRie`, `hTie`. The `mixOfZ` form of
`hTie` used here (`htr`: the trace coefficient vector is `κ` on one basis field `b0` and `0` elsewhere)
is also a sufficient condition, not the general tie at `mixOfZ`.

## Remaining inputs of `clayStatementAt_SU_final` (one line each)

* `hU : ClassMoments hN W (SymPlaqClass N) t C` with `0 < t` — moments of the flowed energy density.
* `hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r` — the physical range.
* `hfar : WDeltaRun.RunSeed N` — the far input; gives the transfer gap.
* `hRie : ρ.Riemann` — Riemann symmetries of the mixing.
* `hTie` — the scalar tie: trace mixing `= Ztr k • sym (plaqField q0)` with `Ztr k a_k⁴ → N/8`.
* `hCT` — `ChannelTie ρ Mb Zc` with the pseudoscalar normalisation `(zAct (Zc k) epsC) id · a_k⁴ → 2`.
* `hK : TwoPointKernel hN ρ G` — the trace two-point function has a kernel `G`.
* `hAF : AFCoefficient N G` — the asymptotic-freedom coefficient of `G`.
* `hNG : NonGaussianT hN ρ` — a non-zero connected three-point function of the trace.
* `hWard : WardT hN ρ` — the Ward identity of the stress tensor.
* `he1`, `he2` — the index map `e` of the composites: its classes and its renormalisation by `ρ`.
* `hCD : CompData Cs`, `hCO : CompOS hN Cs` — the composites' data and OS clauses.
* `hrep` — the rotation representation of `e α` is `∑_β tcoef R α β · single (e β) 1`.
* `hLC : LinkCPre …` — the composites' link at the pre-observer, through the map `wC`.
* `hX` — the cross reading of `wOfC e wC` against `preCvec` converges to `mixT`.

`clayStatementAt_SU_final_siteExp` replaces `hU` by
`hS : FlowUV.SiteExp hN W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C`.
`clayStatementAt_SU_final_mixOfZ` replaces `hRie` by `CoefRiemann m` and `hTie` by `htr`, `hop`,
`hZtie`. The `SU(2)` forms replace `hfar` by `FixedDiffraction mD CD d`.

DERIVED (module-wide): `2` the least colour count and the rank of `SU(2)`; `0` the plane and the step
of the gap; `2 * 1 + 3`, `4` the site count of `FlowUV.classUnitExp_of_siteExp`; `8`, `4` as in
`ScalarTie`.
-/

noncomputable section

namespace MassGap.ClaySUFinal

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
  MassGap.PreObserver
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The moment input from `SiteExp` -/

/-- **`ClassMoments t |C|` on `SymPlaqClass N` from `SiteExp` at `625 t`** on
`SymPlaqClass N` (`FlowUV.classUnitExp_of_siteExp`,
`ObserverMoments.symMoments_of_classUnitExp`).

DERIVED: `2 * 1 + 3`, `4` the site count; `0` the lower end of `t`. -/
theorem classMoments_of_siteExp (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hS : FlowUV.SiteExp hN W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C) :
    ClassMoments hN W (SymPlaqClass N) t |C| :=
  ObserverMoments.classMoments_of_classUnitExp hN W (symPlaq_nonneg hN) ht
    (FlowUV.classUnitExp_of_siteExp hN W (symPlaq_nonneg hN) ht.le hS)

/-! ## 2. The capstone, general mixing -/

/-- **`ClayStatementAt` at `SymPlaqClass N` from `RunSeed N` and `hrep`**: the inputs of
`OneBridgeSU.clayStatementAt_SU_noNT_gap` with the gap `hρ0`, `hρ1`, `hg` from `hfar`
(`LocalLink.observerGapAt_of_runSeed` at `preB`, step `0`) and `hCov` from `hrep`
(`CompReduce.tensorCov_of_comp`, `CompReduce.e_injective`).

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane and the step; `8`, `4`
as in `ScalarTie`; `3` the last slot of the four-index `α : Idx4` in `he1`. -/
theorem clayStatementAt_SU_final (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, Cs.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ))
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  obtain ⟨ρg, hρ0, hρ1, hg⟩ := LocalLink.observerGapAt_of_runSeed hN2 (ne_zero_of_two_le hN2) hfar
    (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) hphys 0
  exact OneBridgeSU.clayStatementAt_SU_noNT_gap hN2 W ht hU hphys hρ0 hρ1 hg ρ hRie hTie
    (CompReduce.tensorCov_of_comp _ ρ Cs e (CompReduce.e_injective Cs e he1) he2 hCO.1
      hCO.2.2.2.1 hrep)
    hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hLC hX

/-- **`clayStatementAt_SU_final` with the moment input from `SiteExp`** at `625 t` on
`SymPlaqClass N` (`classMoments_of_siteExp`; the moment constant is `|C|`).

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `2 * 1 + 3`, `4` the
site count; `8`, `4` as in `ScalarTie`. -/
theorem clayStatementAt_SU_final_siteExp (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hS : FlowUV.SiteExp (ne_zero_of_two_le hN2) W (SymPlaqClass N)
      (t * (2 * 1 + 3) ^ 4) C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W
      (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS) hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, Cs.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ))
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS)
        hphys)
      (preTime (ne_zero_of_two_le hN2) W (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS)
        hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            (preCvec (ne_zero_of_two_le hN2) W
              (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS) hphys Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_final hN2 W ht (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS)
    hphys hfar ρ hRie hTie hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hrep hLC hX

/-! ## 3. The capstone at `ρ = mixOfZ` -/

section Mix

variable {B : Type} [Fintype B] [DecidableEq B]

/-- **`clayStatementAt_SU_final_siteExp` at `ρ = mixOfZ B op m Z`**, with `hRie` from
`CoefRiemann m` (`ClayWiring.riemann_mixOfZ`) and `hTie` from the trace data: the trace coefficient
vector is `κ` on `b0` and `0` elsewhere, `op b0 = sym (plaqField q0)`, and
`κ Z_k(op b0) a_k⁴ → N/8` (`ClayWiring.scalarTie_mixOfZ`).

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane and the other
coefficients; `2 * 1 + 3`, `4` the site count; `8`, `4` as in `ScalarTie`. -/
theorem clayStatementAt_SU_final_mixOfZ (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hS : FlowUV.SiteExp (ne_zero_of_two_le hN2) W (SymPlaqClass N)
      (t * (2 * 1 + 3) ^ 4) C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ)
    (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (mixOfZ B op m Z) G)
    (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) (mixOfZ B op m Z))
    (hWard : WardT (ne_zero_of_two_le hN2) (mixOfZ B op m Z))
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W
      (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS) hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, (m α b * Z k (op b)) • (op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, Cs.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ))
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS)
        hphys)
      (preTime (ne_zero_of_two_le hN2) W (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS)
        hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (mixOfZ B op m Z)
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) (mixOfZ B op m Z)
            (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            (preCvec (ne_zero_of_two_le hN2) W
              (classMoments_of_siteExp (ne_zero_of_two_le hN2) W ht hS) hphys Q)
          = (mixT (ne_zero_of_two_le hN2) (mixOfZ B op m Z)
              (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_final_siteExp hN2 W ht hS hphys hfar (mixOfZ B op m Z)
    (riemann_mixOfZ op m Z hRie) (scalarTie_mixOfZ op m Z b0 κ htr hop hZtie).2
    hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hrep hLC hX

end Mix

/-! ## 4. `SU(2)` with the gap from a fixed diffraction length -/

/-- **`clayStatementAt_SU_final` at `N = 2`** with `RunSeed 2` from
`ApertureGap.FixedDiffraction mD CD d` (`ApertureGap.runSeed_of_fixedDiffraction`).

DERIVED: `2` the rank and the limit of `TopNorm`; `0` the plane; `8`, `4` as in `ScalarTie`; `3` the
last slot of the four-index `α : Idx4` in `he1`. -/
theorem clayStatementAt_SU2_fixedDiffraction (W : ConfFlow 2)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    {mD CD : ℝ} {d : ℕ} (hfd : ApertureGap.FixedDiffraction mD CD d)
    (ρ : RenormMix 2) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing 2 k ^ 4) atTop (𝓝 (((2 : ℕ) : ℝ) / 8)))
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing 2 k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le (le_refl 2)) ρ G)
    (hAF : AFCoefficient 2 G)
    (hNG : NonGaussianT (ne_zero_of_two_le (le_refl 2)) ρ)
    (hWard : WardT (ne_zero_of_two_le (le_refl 2)) ρ)
    (Cs : Composites 2)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le (le_refl 2)) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) Cs)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, Cs.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ))
    (hLC : LinkCPre (ne_zero_of_two_le (le_refl 2)) 0
      (preVac (ne_zero_of_two_le (le_refl 2)) W hU hphys)
      (preTime (ne_zero_of_two_le (le_refl 2)) W hU hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD 2 (SymPlaqClass 2) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le (le_refl 2)) ρ
          (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le (le_refl 2)) ρ (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
            0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P) (preCvec (ne_zero_of_two_le (le_refl 2)) W hU hphys Q)
          = (mixT (ne_zero_of_two_le (le_refl 2)) ρ (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
              0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2) :=
  clayStatementAt_SU_final (le_refl 2) W ht hU hphys (ApertureGap.runSeed_of_fixedDiffraction hfd)
    ρ hRie hTie hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hrep hLC hX

/-- **`clayStatementAt_SU_final_mixOfZ` at `N = 2`** with `RunSeed 2` from
`ApertureGap.FixedDiffraction mD CD d` (`ApertureGap.runSeed_of_fixedDiffraction`).

DERIVED: `2` the rank and the limit of `TopNorm`; `0` the plane and the other coefficients;
`2 * 1 + 3`, `4` the site count; `8`, `4` as in `ScalarTie`. -/
theorem clayStatementAt_SU2_fixedDiffraction_mixOfZ {B : Type} [Fintype B] [DecidableEq B]
    (W : ConfFlow 2) {t C : ℝ} (ht : 0 < t)
    (hS : FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2)
      (t * (2 * 1 + 3) ^ 4) C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    {mD CD : ℝ} {d : ℕ} (hfd : ApertureGap.FixedDiffraction mD CD d)
    (op : B → LField (MassGap.SUN.SU 2)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ)
    (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing 2 k ^ 4) atTop
      (𝓝 (((2 : ℕ) : ℝ) / 8)))
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing 2 k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (mixOfZ B op m Z) G)
    (hAF : AFCoefficient 2 G)
    (hNG : NonGaussianT (ne_zero_of_two_le (le_refl 2)) (mixOfZ B op m Z))
    (hWard : WardT (ne_zero_of_two_le (le_refl 2)) (mixOfZ B op m Z))
    (Cs : Composites 2)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le (le_refl 2)) W
      (classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS) hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, (m α b * Z k (op b)) • (op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) Cs)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, Cs.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ))
    (hLC : LinkCPre (ne_zero_of_two_le (le_refl 2)) 0
      (preVac (ne_zero_of_two_le (le_refl 2)) W
        (classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS) hphys)
      (preTime (ne_zero_of_two_le (le_refl 2)) W
        (classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS) hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD 2 (SymPlaqClass 2) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le (le_refl 2)) (mixOfZ B op m Z)
          (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le (le_refl 2)) (mixOfZ B op m Z)
            (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            (preCvec (ne_zero_of_two_le (le_refl 2)) W
              (classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS) hphys Q)
          = (mixT (ne_zero_of_two_le (le_refl 2)) (mixOfZ B op m Z)
              (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2) :=
  clayStatementAt_SU_final_mixOfZ (le_refl 2) W ht hS hphys
    (ApertureGap.runSeed_of_fixedDiffraction hfd) op m Z hRie b0 κ htr hop hZtie hCT G hK hAF hNG
    hWard Cs wC e he1 he2 hCD hCO hrep hLC hX

end MassGap.ClaySUFinal

end

#print axioms MassGap.ClaySUFinal.classMoments_of_siteExp
#print axioms MassGap.ClaySUFinal.clayStatementAt_SU_final
#print axioms MassGap.ClaySUFinal.clayStatementAt_SU_final_siteExp
#print axioms MassGap.ClaySUFinal.clayStatementAt_SU_final_mixOfZ
#print axioms MassGap.ClaySUFinal.clayStatementAt_SU2_fixedDiffraction
#print axioms MassGap.ClaySUFinal.clayStatementAt_SU2_fixedDiffraction_mixOfZ
