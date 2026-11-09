import Mathlib
import MassGap.ClayG
import MassGap.AbelianGen
import MassGap.AbelianGenX
import MassGap.AbelianGenE7
import MassGap.SchedAlong

/-!
# MassGap.ClayGFinal — the `G` capstone without `FlowConnectedNonzeroG`

`ClayG.clayStatementAtG_GS` takes `hNT : FlowConnectedNonzeroG (canonSched G) (energy0G …) 0 r`.
Its one consumer is the `nontrivial` field of the observer's `OSDataS`
(`ObserverOSG.observerOSDataSG`, through `TimeGroupG.flowN_time_group_of_gapG`). This module fills
that field from the composites' link instead, as `PreObserver` does at `SU(N)`.

| `PreObserver` (`SU(N)`) | here (any `G`) |
|---|---|
| `flowN_time_group_of_gap_noNT` | `flowN_time_group_of_gapG_noNT` (any schedule `S` with `SchedOS S`) |
| `preB`, `preH`, `preVac`, `preTime`, `preCvec` | `preBG`, `preHG`, `preVacG`, `preTimeG`, `preCvecG` |
| `LinkCPre`, `linkC_iff_pre` | `LinkCPreG`, `linkCG_iff_pre` |
| `exists_orth_ne_zero_of_gram` | `exists_orth_ne_zero_of_gramG` (`SchedShiftInv S`, `0 < K.cAF`) |
| `preNontrivial` | `preNontrivialG` (`LinkReduceG.gram_wOfCG`, `LinkReduce.wOfC_empty`) |
| `observerOSDataSN`, `observerOSDataSLinkedN`, `obsXN` | `observerOSDataSGN`, `observerOSDataSLinkedGN`, `obsXGN` |
| `obsXN_gap`, `obsXN_SM` | `obsXGN_gap`, `obsXGN_SM` |
| `obsX'_linkC_iff`, `obsXN_linkC_iff`, `obsX'_cvec`, `obsXN_cvec` | `obsXG'_linkC_iff`, `obsXGN_linkC_iff`, `obsXG'_cvec`, `obsXGN_cvec` |
| `clayStatementAt_SU_at`, `clayStatementAt_SU_noNT` | `clayStatementAtG_GS_at`, `clayStatementAtG_GS_noNT` |

`ClayAtGNoNT G` is the conclusion of `clayStatementAtG_GS_noNT` under all of its inputs except
`hab : AbelianGenG G`; `clayAtGNoNT_of_abelianGenG` gives it from `hab`, and it holds at `SU(N)`
(`N ≥ 2`), `SO(n)` (`n ≥ 5`), `SO(3)`, `USp(n)`, `G₂`, `F₄`, `E₆`, `E₇`, `E₈` from the abelian
generators of `AbelianGen`, `AbelianGenX`, `AbelianGenE7`.

The pre-observer, `preNontrivialG`, `obsXGN` and its facts, the two
capstones, `ClayAtGNoNT` and its group instances are each stated along a coupling tower `βs : ℕ → ℝ`, at the
schedule `MeasuredTower.schedAlongG G βs`, under the same name with the suffix `Along`
(`preBGAlong`, …, `clayStatementAtG_GS_noNTAlong`, `ClayAtGNoNTAlong`, `clayAtGNoNT_SUAlong`, …). The
schedule enters only through `SchedOS` and `SchedShiftInv`, which hold at every `βs`
(`MeasuredSpacing.schedOS_alongG`, `MeasuredSpacing.schedShiftInv_alongG`, in `SchedAlong`), and through the
conclusion `ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G)`
(`ClayStatementG.clayStatementAtP_of_link`). Each unsuffixed declaration is its `Along` form at
`βs = dyBetaG G`, since `canonSched G = schedAlongG G (dyBetaG G)` by `rfl`. `clayStatementOf_of_noNTAlong`
packs the conclusion along a measured tower (`MeasuredTower.MeasTowerG G βs`) into the root statement
`ClayStatementG.ClayStatementOf G`.

The transfer gap of the observer at step `0` (`hρ0`, `hρ1`, `hg`) is an input.

DERIVED (module-wide): `0` the plane, the step, the vanishing pairing and the zero vector; `1` the
window and the top of the rate; `4` the dimension; `2`, `8` as in `SUInputs.eDist_bounds_of_bump`.
CHOSEN: `16 = 2 · 8`, as in `InputsG.hnt_of_gramG`.
-/

noncomputable section

namespace MassGap.ClayGFinal

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.InputsG MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG MassGap.SUInputs
  Filter
open scoped Topology Matrix

/-! ## 1. The time group without `FlowConnectedNonzeroG` -/

section TimeGroup

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The continuous-time picture of the flowed reconstruction over `G` from one gap at one step**:
the inputs of `TimeGroupG.flowN_time_group_of_gapG` without `FlowConnectedNonzeroG` give a rate
`μ > 0` and `TimeGroupAtG` at `μ` (`flowClusterAbs_iff_gapAtG`, `flow_gap_of_abs_clusterG`,
`flow_time_groupG`).

DERIVED: `0` the sign of `μ`, `L`, `ρ` and the lower end of the rate; `1` the top of `ρ`; `4` the
dimension. -/
theorem flowN_time_group_of_gapG_noNT (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS Φ hB τ hphys m0) ρ) :
    ∃ μ : ℝ, 0 < μ
      ∧ TimeGroupAtG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) μ := by
  obtain ⟨c, hc, hga⟩ := flow_gap_of_abs_clusterG S hS Φ hB τ
    (posPreserving_of_physRangeG S Φ hphys τ)
    ((flowClusterAbs_iff_gapAtG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) m0 hL).mpr
      ⟨ρ, hρ0, hρ1, hg⟩)
  have hgap : ∀ m : ℕ, ContinuumClay.GappedAt
      (flowTransferG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) m)
      (Real.exp (-(c / L) * S.a m)) := by
    intro m
    have hr0 : 0 < Real.exp (-(c / L) * S.a m) := Real.exp_pos _
    have hr1 : Real.exp (-(c / L) * S.a m) < 1 := by
      rw [Real.exp_lt_one_iff, neg_mul]
      exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (S.a_pos m))
    refine ⟨hr0, hr1, hga m, fun u hu => GapToOperator.norm_opT_le_of_orth _ hr0.le (hga m) u hu,
      ?_, GNSHilbert.isGreatest_one_spectrum_opT _⟩
    intro x hx
    rcases GapToOperator.spectrum_opT_subset _ hr0.le (hga m) hx with h | h
    · exact Or.inl h
    · exact Or.inr ⟨Set.mem_Ici.mp (GNSHilbert.spectrum_opT_nonneg _
        (flowTransferG_positive S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) m) hx),
        h.2⟩
  exact ⟨c / L, div_pos hc hL, flow_time_groupG S hS Φ hB τ
    (posPreserving_of_physRangeG S Φ hphys τ) (div_pos hc hL).le hgap⟩

end TimeGroup

/-! ## 2. The pre-observer -/

section Pre

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedOS_alongG)

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- The uniform bound of `energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)` from the
class moments, along a coupling tower `βs`. DERIVED: no numeral. -/
abbrev preBGAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) :
    UniformBoundFG (schedAlongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).map :=
  uniformBoundFG_energy0G (schedAlongG G βs) (schedOS_alongG G βs) W (symPlaqG_refl G)
    symPlaqG_nonneg (cube_of_classMomentsG (schedAlongG G βs) W hU)

/-- `preBGAlong` at the canonical schedule. DERIVED: no numeral. -/
abbrev preBG (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) :
    UniformBoundFG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).map :=
  preBGAlong (dyBetaG G) W hU

/-- The pre-observer's Hilbert space along a coupling tower `βs`: `FlowHG` of
`energy0G (schedAlongG G βs) W (SymPlaqClassG G) _` at the plane `0`. DERIVED: `0` the plane. -/
abbrev preHGAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r) : Type :=
  FlowHG (schedAlongG G βs) (schedOS_alongG G βs)
    (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) (preBGAlong βs W hU) 0
    (posPreserving_of_physRangeG (schedAlongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0)

/-- `preHGAlong` at the canonical schedule. DERIVED: no numeral. -/
abbrev preHG (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r) : Type :=
  preHGAlong (dyBetaG G) W hU hphys

/-- The pre-observer's vacuum `vacTG` along a coupling tower `βs`. DERIVED: `0` the plane. -/
abbrev preVacGAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r) : preHGAlong βs W hU hphys :=
  vacTG (schedAlongG G βs) (schedOS_alongG G βs)
    (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) (preBGAlong βs W hU) 0
    (posPreserving_of_physRangeG (schedAlongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0)

/-- `preVacGAlong` at the canonical schedule. DERIVED: no numeral. -/
abbrev preVacG (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r) : preHG W hU hphys :=
  preVacGAlong (dyBetaG G) W hU hphys

/-- The pre-observer's time translations `timeTG` along a coupling tower `βs`. DERIVED: `0` the
plane. -/
abbrev preTimeGAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r) :
    ℝ → preHGAlong βs W hU hphys →L[ℂ] preHGAlong βs W hU hphys :=
  timeTG (schedAlongG G βs) (schedOS_alongG G βs)
    (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) (preBGAlong βs W hU) 0
    (posPreserving_of_physRangeG (schedAlongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0)

/-- `preTimeGAlong` at the canonical schedule. DERIVED: no numeral. -/
abbrev preTimeG (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r) :
    ℝ → preHG W hU hphys →L[ℂ] preHG W hU hphys :=
  preTimeGAlong (dyBetaG G) W hU hphys

/-- The pre-observer's compact vectors `gvecTG` along a coupling tower `βs`. DERIVED: `0` the
plane. -/
abbrev preCvecGAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    (Q : MarginMonoDG G (SymPlaqClassG G) 0 r) : preHGAlong βs W hU hphys :=
  gvecTG (schedAlongG G βs) (schedOS_alongG G βs)
    (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) (preBGAlong βs W hU) 0
    (posPreserving_of_physRangeG (schedAlongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0) Q.1

/-- `preCvecGAlong` at the canonical schedule. DERIVED: `0` the plane. -/
abbrev preCvecG (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (Q : MarginMonoDG G (SymPlaqClassG G) 0 r) : preHG W hU hphys :=
  preCvecGAlong (dyBetaG G) W hU hphys Q

end Pre

section LinkPre

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The three clauses of `LinkCG`** on a complex inner product space with a vacuum `vac` and time
translations `time`: the Gram identity with the convergence of the lattice sequence of `ΘP ∪ Q`,
the step `S.a m` as `time`, and `wC ∅ = vac`.

DERIVED: no numeral. -/
def LinkCPreG (S : Sched G) (τ : Fin 4) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (vac : H) (time : ℝ → H →L[ℂ] H) (C : CompositesG G) (wC : TSepG C.Ix τ → H) : Prop :=
  (∀ P Q : TSepG C.Ix τ,
      Tendsto (fun k => latCG S C k (pairCG C τ P.1 Q.1)) (ultra : Filter ℕ)
          (𝓝 (contCG S C (pairCG C τ P.1 Q.1)))
        ∧ inner ℂ (wC P) (wC Q) = (kernCG S C τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSepG C.Ix τ), wC (shiftTG S τ m P) = time (S.a m) (wC P))
    ∧ wC (emptyG C.Ix τ) = vac

/-- **`LinkCG` is `LinkCPreG` at the vacuum and time translations of `X.base`.**

DERIVED: no numeral. -/
theorem linkCG_iff_pre (S : Sched G) {D : Set (LField G)} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinkedG G D τ r) (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H) :
    LinkCG S X C wC ↔ LinkCPreG S τ X.base.vac X.base.time C wC :=
  Iff.rfl

end LinkPre

/-! ## 3. A non-zero vector orthogonal to the vacuum on the pre-observer -/

section Nontrivial

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A non-zero vector orthogonal to `vac`** in any complex inner product space carrying a family
`w` with the Gram identity `⟪w P, w Q⟫ = kernTG S ρ 0 P Q` and `w ∅ = vac`, over a schedule with
`SchedShiftInv S` and constants with `0 < K.cAF`, from `TwoPointKernelG` and `AFCoefficientG`:
`w` at one trace insertion smeared with the bump (`SUInputs.oneT`). The argument of
`InputsG.hnt_of_gramG` without the reconstruction.

DERIVED: `0` the time axis, the vanishing pairing and the zero vector; `8` as in
`SUInputs.eDist_bounds_of_bump`. CHOSEN: `16 = 2 · 8`, as in `InputsG.hnt_of_gramG`. -/
theorem exists_orth_ne_zero_of_gramG (S : Sched G) (hsh : SchedShiftInv S) (K : ClayConsts)
    (hKpos : 0 < K.cAF) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (vac : H)
    (ρ : RenormMixG G) (w : TSep 0 → H)
    (hin : ∀ P Q : TSep 0, inner ℂ (w P) (w Q) = (kernTG S ρ 0 P Q : ℂ))
    (hvac : w (emptyT 0) = vac) (Gk : ℝ → ℝ)
    (hK : TwoPointKernelG S ρ Gk) (hAF : AFCoefficientG K Gk) :
    ∃ u : H, inner ℂ vac u = 0 ∧ u ≠ 0 := by
  obtain ⟨δ, hδ, -, hb⟩ :=
    ContinuumNontrivial.af_bounds_on_interval (afShortDistance_of_coefficientG hKpos hAF)
  have hl : 0 < δ / 16 := div_pos hδ (by norm_num)
  obtain ⟨g₀, g₁, hg₀, hG⟩ := hb (δ / 16) (8 * (δ / 16)) hl (by linarith) (by linarith)
  have hcont_r : Continuous ((bumpT hl.le).reflect 0).1 :=
    (continuous_bumpF (δ / 16)).comp (continuous_id.update 0 (continuous_apply 0).neg)
  have hkk : kernTG S ρ 0 (oneT hl) (oneT hl) ≠ 0 := by
    rw [kernTG_oneT_eq S ρ hl,
      hK.2 _ _ hcont_r (continuous_bumpF (δ / 16)) ⟨δ / 16, hl, sepBy_bump hl⟩]
    exact (kernel_integral_pos hK.1 hl hg₀ (fun r h1 h2 => (hG r h1 h2).1)).ne'
  refine ⟨w (oneT hl), ?_, ?_⟩
  · rw [← hvac, hin, kernTG_empty_oneT S hsh ρ hl, Complex.ofReal_zero]
  · intro h0
    apply hkk
    have h := hin (oneT hl) (oneT hl)
    rw [h0, inner_zero_left] at h
    exact_mod_cast h.symm

variable [GaugeSimple G] [GaugeLie G]

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedShiftInv_alongG)

/-- **The pre-observer over `G` along a coupling tower `βs` has a non-zero vector orthogonal to its
vacuum**, from `LinkCPreG` of a family `wC` of composites' vectors in `preHGAlong`, the two clauses of an
index map `e`, `TwoPointKernelG` and `AFCoefficientG`: `exists_orth_ne_zero_of_gramG` at
`schedAlongG G βs` (`MeasuredSpacing.schedShiftInv_alongG`) and `w := wOfC e wC`, with the Gram identity
from `LinkReduceG.gram_wOfCG` and `w ∅ = preVacGAlong` from `LinkReduce.wOfC_empty`.

DERIVED: `0` the plane, the vanishing pairing and the zero vector; `0`–`3` the slots. -/
theorem preNontrivialGAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    (ρ : RenormMixG G) (Gk : ℝ → ℝ) (hK : TwoPointKernelG (schedAlongG G βs) ρ Gk)
    (hAF : AFCoefficientG (constsG G) Gk) (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → preHGAlong βs W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hLC : LinkCPreG (schedAlongG G βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
      Cs wC) :
    ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0 :=
  exists_orth_ne_zero_of_gramG (schedAlongG G βs) (schedShiftInv_alongG G βs) (constsG G)
    (afConstG_pos G) _ ρ (wOfC e wC)
    (gram_wOfCG (schedAlongG G βs) ρ Cs wC e he1 he2 hLC.1)
    (wOfC_empty e wC hLC.2.2) Gk hK hAF

/-- **The pre-observer over `G` has a non-zero vector orthogonal to its vacuum**: `preNontrivialGAlong`
at the canonical schedule.

DERIVED: `0` the plane, the vanishing pairing and the zero vector; `0`–`3` the slots. -/
theorem preNontrivialG (W : ConfFlowG G) {t C : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (ρ : RenormMixG G) (Gk : ℝ → ℝ) (hK : TwoPointKernelG (canonSched G) ρ Gk)
    (hAF : AFCoefficientG (constsG G) Gk) (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → preHG W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hLC : LinkCPreG (canonSched G) 0 (preVacG W hU hphys) (preTimeG W hU hphys) Cs wC) :
    ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0 :=
  preNontrivialGAlong (dyBetaG G) W hU hphys ρ Gk hK hAF Cs wC e he1 he2 hLC

end Nontrivial

/-! ## 4. The observer with the non-trivial vector as an input -/

section Observer

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **`ObserverOSG.observerOSDataSG` with the non-trivial vector as an input.** The inputs of
`observerOSDataSG` with `hNT` replaced by `hnt`, a non-zero vector of `FlowHG` orthogonal to
`vacTG`; the rate is that of `flowN_time_group_of_gapG_noNT`, and `nontrivial := hnt`.

DERIVED: `0` the signs, the reference step and the time origin; `1` the top of `ρ`; `4` the
dimension. -/
def observerOSDataSGN (S : Sched G) (hS : SchedOS S) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O)
    {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ hphys m0) ρ)
    (hnt : ∃ u : FlowHG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
        (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ),
      inner ℂ (vacTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
        (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ)) u = 0 ∧ u ≠ 0) :
    OSDataS :=
  let hB := uniformBoundFG_energy0G S hS W hD hpos hcube
  let hpp := posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ
  let hT := flowN_time_group_of_gapG_noNT S hS (energy0G S W D hD) hB τ hphys m0 hL hρ0 hρ1 hg
  let hgr := abs_schwCMLG_le S hsh W hpos hO h
  let μ := Classical.choose hT
  have hμ := Classical.choose_spec hT
  { S := schwCMLG S hsh W hpos hO h
    α := Classical.choose hgr
    γ := Classical.choose (Classical.choose_spec hgr)
    growth := Classical.choose_spec (Classical.choose_spec hgr)
    os3 := fun n σ φ => by
      show schwSFG S W D O (fun i => ofE4 ((φ ∘ σ) i)) = schwSFG S W D O (fun i => ofE4 (φ i))
      exact schwSFG_comp_perm S W D O σ (fun i => ofE4 (φ i))
    H := FlowHG S hS (energy0G S W D hD) hB τ hpp
    vac := vacTG S hS (energy0G S W D hD) hB τ hpp
    time := timeTG S hS (energy0G S W D hD) hB τ hpp
    gap := μ
    gap_pos := hμ.1
    time_zero := hμ.2.1
    time_add := hμ.2.2.1
    time_selfAdjoint := fun t ht => ⟨(hμ.2.2.2.2.1 t ht).2.1, (hμ.2.2.2.2.1 t ht).2.2⟩
    time_cont := hμ.2.2.2.2.2.1
    time_vac := hμ.2.2.2.2.2.2.1
    time_gap := hμ.2.2.2.2.2.2.2.1
    nontrivial := hnt }

/-- **`ObserverLinkedG.observerOSDataSLinkedG` over `observerOSDataSGN`**: the same `SM`, `O`,
`vec`, `cvec` and proofs, with `base := observerOSDataSGN … hnt`.

DERIVED: `0` the signs and the reference step; `1` the top of `ρ`; `4` the dimension. -/
def observerOSDataSLinkedGN (S : Sched G) (hS : SchedOS S) (hsh : SchedShiftInv S)
    (W : ConfFlowG G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMomentsG S W D t C)
    {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ hphys m0) ρ)
    (hnt : ∃ u : FlowHG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
        (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ),
      inner ℂ (vacTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
        (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ)) u = 0 ∧ u ≠ 0) :
    OSDataSLinkedG G D τ r where
  base := observerOSDataSGN S hS hsh W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hnt
  SM := fun O g => schwSFMG S W D O g
  O := O
  S_eq := fun n φ => by
    show schwCMLG S hsh W hpos hO h n φ
      = schwSFMG S W D (fun _ : Fin n => O) (fun i => ofE4 (φ i))
    rw [schwCMLG_apply]
    exact schwSFG_eq_schwSFMG S W hpos ht hC0 hU hO _
  vec := vecDG S hS W hD hpos hcube τ hphys
  inner_vec := inner_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys
  cvec := fun Q => gvecTG S hS (energy0G S W D hD) (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
    (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ) Q.1
  vec_compact := vecDG_ofMarginDG S hS W hD hpos hcube ht hC0 hU τ hphys
  closure_eq := closure_range_vecDG S hS W hD hpos hcube ht hC0 hU τ hphys

variable [GaugeSimple G]

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedOS_alongG schedShiftInv_alongG)

/-- **`InputsG.obsXG'` with the non-trivial vector as an input, along a coupling tower `βs`**:
`observerOSDataSLinkedGN` at `schedAlongG G βs` (`MeasuredSpacing.schedOS_alongG`,
`MeasuredSpacing.schedShiftInv_alongG`), the class `SymPlaqClassG G`, the plane `0` and the step `0`.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXGNAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0) :
    OSDataSLinkedG G (SymPlaqClassG G) 0 r :=
  observerOSDataSLinkedGN (schedAlongG G βs) (schedOS_alongG G βs) (schedShiftInv_alongG G βs) W
    (symPlaqG_refl G) symPlaqG_nonneg (cube_of_classMomentsG (schedAlongG G βs) W hU) ht
    (zero_le_one.trans (one_le_of_classMomentsG (schedAlongG G βs) W symPlaqG_q0 hU)) hU symPlaqG_q0
    (unitCubeExpBoundG_of_cubeMomentsAtG (schedAlongG G βs) W ht (hU _ symPlaqG_q0))
    0 hphys 0 one_pos hρ0 hρ1 hg hnt

/-- **`InputsG.obsXG'` with the non-trivial vector as an input**: `obsXGNAlong` at the canonical
schedule.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXGN (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0) :
    OSDataSLinkedG G (SymPlaqClassG G) 0 r :=
  obsXGNAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt

/-- **The Hamiltonian gap of `obsXGNAlong`**, from its self-adjoint generator
(`ObserverOSG.observer_generator_isSelfAdjointG`, `ClayFull.hamiltonianGap_of_selfAdjoint`).

DERIVED: `0` the plane. -/
theorem obsXGN_gapAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0) :
    HamiltonianGap (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjointG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) (preBGAlong βs W hU) 0
      (posPreserving_of_physRangeG (schedAlongG G βs)
        (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0))

/-- **The Hamiltonian gap of `obsXGN`**: `obsXGN_gapAlong` at the canonical schedule.

DERIVED: `0` the plane. -/
theorem obsXGN_gap (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0) :
    HamiltonianGap (obsXGN W ht hU hphys hρ0 hρ1 hg hnt).base :=
  obsXGN_gapAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt

/-- **The functional of `obsXGNAlong` is `schwSFMG`** at `schedAlongG G βs`, by definition.
DERIVED: `0` the plane and the step. -/
theorem obsXGN_SMAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt).SM O g
        = schwSFMG (schedAlongG G βs) W (SymPlaqClassG G) O g :=
  fun _ _ _ _ => rfl

/-- **The functional of `obsXGN` is `schwSFMG`**: `obsXGN_SMAlong` at the canonical schedule.
DERIVED: no numeral. -/
theorem obsXGN_SM (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      (obsXGN W ht hU hphys hρ0 hρ1 hg hnt).SM O g
        = schwSFMG (canonSched G) W (SymPlaqClassG G) O g :=
  obsXGN_SMAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt

/-- **`obsXGNAlong` carries its Hilbert space**: `v = gvecTG` of the pre-observer
(`ObserverLinkedG.obsGenG_flow`).

DERIVED: `0` the plane. -/
theorem obsXGN_obsGenAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0) :
    ObsGenG (schedAlongG G βs) W (SymPlaqClassG G) (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt) :=
  ⟨gvecTG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) (preBGAlong βs W hU) 0
      (posPreserving_of_physRangeG (schedAlongG G βs)
        (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0),
    fun _ => rfl, obsGenG_flow (schedAlongG G βs) (schedOS_alongG G βs) W (symPlaqG_refl G)
      (preBGAlong βs W hU) 0
      (posPreserving_of_physRangeG (schedAlongG G βs)
        (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0)⟩

/-- **`obsXGN` carries its Hilbert space**: `obsXGN_obsGenAlong` at the canonical schedule.

DERIVED: `0` the plane. -/
theorem obsXGN_obsGen (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0) :
    ObsGenG (canonSched G) W (SymPlaqClassG G) (obsXGN W ht hU hphys hρ0 hρ1 hg hnt) :=
  obsXGN_obsGenAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt

/-- **`LinkCG` at `InputsG.obsXG' … hNT …` is `LinkCPreG` at the pre-observer**, for every `hNT`.

DERIVED: `0` the plane. -/
theorem obsXG'_linkC_iff (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (Cs : CompositesG G) (wC : TSepG Cs.Ix 0 → preHG W hU hphys) :
    LinkCG (canonSched G) (obsXG' W ht hU hphys hNT hρ0 hρ1 hg) Cs wC
      ↔ LinkCPreG (canonSched G) 0 (preVacG W hU hphys) (preTimeG W hU hphys) Cs wC :=
  Iff.rfl

/-- **`LinkCG` at `obsXGNAlong … hnt` is `LinkCPreG` at the pre-observer along `βs`**, for every `hnt`.

DERIVED: `0` the plane. -/
theorem obsXGN_linkC_iffAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0)
    (Cs : CompositesG G) (wC : TSepG Cs.Ix 0 → preHGAlong βs W hU hphys) :
    LinkCG (schedAlongG G βs) (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt) Cs wC
      ↔ LinkCPreG (schedAlongG G βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
        Cs wC :=
  Iff.rfl

/-- **`LinkCG` at `obsXGN … hnt` is `LinkCPreG` at the pre-observer**, for every `hnt`:
`obsXGN_linkC_iffAlong` at the canonical schedule.

DERIVED: `0` the plane. -/
theorem obsXGN_linkC_iff (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0)
    (Cs : CompositesG G) (wC : TSepG Cs.Ix 0 → preHG W hU hphys) :
    LinkCG (canonSched G) (obsXGN W ht hU hphys hρ0 hρ1 hg hnt) Cs wC
      ↔ LinkCPreG (canonSched G) 0 (preVacG W hU hphys) (preTimeG W hU hphys) Cs wC :=
  obsXGN_linkC_iffAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt Cs wC

/-- **The compact vectors of `InputsG.obsXG' … hNT …` are `preCvecG`**, for every `hNT`.

DERIVED: `0` the plane. -/
theorem obsXG'_cvec (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (Q : MarginMonoDG G (SymPlaqClassG G) 0 r) :
    (obsXG' W ht hU hphys hNT hρ0 hρ1 hg).cvec Q = preCvecG W hU hphys Q :=
  rfl

/-- **The compact vectors of `obsXGNAlong … hnt` are `preCvecGAlong`**, for every `hnt`.

DERIVED: `0` the plane. -/
theorem obsXGN_cvecAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0)
    (Q : MarginMonoDG G (SymPlaqClassG G) 0 r) :
    (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt).cvec Q = preCvecGAlong βs W hU hphys Q :=
  rfl

/-- **The compact vectors of `obsXGN … hnt` are `preCvecG`**, for every `hnt`: `obsXGN_cvecAlong`
at the canonical schedule.

DERIVED: `0` the plane. -/
theorem obsXGN_cvec (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0)
    (Q : MarginMonoDG G (SymPlaqClassG G) 0 r) :
    (obsXGN W ht hU hphys hρ0 hρ1 hg hnt).cvec Q = preCvecG W hU hphys Q :=
  obsXGN_cvecAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt Q

end Observer

/-! ## 5. The capstone -/

section Capstone

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedOS_alongG schedShiftInv_alongG)

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- **`ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G)` along a coupling tower `βs`, from
the inputs of `ClayG.clayStatementAtG_GS` at the observer `obsXGNAlong βs … hnt`**, each read at
`schedAlongG G βs`: `hNT` replaced by `hnt`, and `wC`, `hLC`, `hX` typed at `obsXGNAlong βs … hnt`. The
schedule enters through `MeasuredSpacing.schedOS_alongG` and `MeasuredSpacing.schedShiftInv_alongG`; the
conclusion is `ClayStatementG.clayStatementAtP_of_link` at `schedAlongG G βs` and `constsG G`.

DERIVED: `0` the plane and the step; `4` the dimension; `3` the last slot of the four-index `α : Idx4` in
`he1`. -/
theorem clayStatementAtG_GS_atAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ₀)
    (hnt : ∃ u : preHGAlong βs W hU hphys, inner ℂ (preVacGAlong βs W hU hphys) u = 0 ∧ u ≠ 0)
    (ρ : RenormMixG G) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := G) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (schedAlongG G βs).a k ^ 4) atTop (𝓝 (constsG G).cTr))
    (hCov : TensorCovG (schedAlongG G βs) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (schedAlongG G βs).a k ^ 4) atTop
          (𝓝 (constsG G).cTop))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (schedAlongG G βs) ρ Gk) (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (schedAlongG G βs) ρ) (hWard : WardTG (schedAlongG G βs) ρ)
    (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompDataG Cs) (hCO : CompOSG (schedAlongG G βs) Cs)
    (hLC : LinkCG (schedAlongG G βs) (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (schedAlongG G βs) ρ
          (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) ((obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt).cvec Q)
          = (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ))
    (hab : AbelianGenG G) :
    ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G) := by
  have hConv := sepConvG_of_comp (schedAlongG G βs) ρ Cs e he2 hCO.1
  have hHS := linkHSG_of_comp (schedAlongG G βs) W (SymPlaqClassG G) _ ρ Cs wC hLC e he1 he2 hX
  obtain ⟨Mb, Zc, hCT1, hCT2⟩ := hCT
  exact clayStatementAtP_of_link (schedAlongG G βs) (constsG G) (afConstG_pos G) W
    (SymPlaqClassG G) (obsXGNAlong βs W ht hU hphys hρ0 hρ1 hg hnt) ρ Gk
    (wOfC e wC)
    (obsXGN_SMAlong βs W ht hU hphys hρ0 hρ1 hg hnt)
    (obsXGN_gapAlong βs W ht hU hphys hρ0 hρ1 hg hnt)
    hRie ⟨rfl, hTie⟩ hConv
    (os0SepG_of_comp _ ρ Cs e he2 hCO.1 hCO.2.1)
    (os1SepG_of_comp _ ρ Cs e he2 hCO.1 hCO.2.2.1) hCov
    (linkTSG_of_hs _ W (SymPlaqClassG G) _ ρ _ hConv hHS)
    (hnt_of_gramG (schedAlongG G βs) (schedShiftInv_alongG G βs) (constsG G) (afConstG_pos G) _ ρ _
      hHS.1 hHS.2.2.1 Gk hK hAF)
    hK hAF hNG
    (tensorNondegG_of_comp _ ρ Cs e he1 he2 hCO.1 hCO.2.2.2.2 hab)
    ⟨uniformBoundFG_energy0G (schedAlongG G βs) (schedOS_alongG G βs) W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (schedAlongG G βs) W hU),
      fun ι _ O hO g => tendsto_schwSFMG (schedAlongG G βs) W symPlaqG_nonneg ht
        (zero_le_one.trans (one_le_of_classMomentsG (schedAlongG G βs) W symPlaqG_q0 hU)) hU O hO g⟩
    Cs wC ⟨Mb, Zc, hCT1, topNormG_of_channelTie _ _ ρ Mb Zc hCT1 hCT2⟩ hWard hCD hCO hLC
    (tInG_of_comp _ ρ Cs wC e he1 he2)
    (obsXGN_obsGenAlong βs W ht hU hphys hρ0 hρ1 hg hnt)

/-- **`ClayStatementAtG G W (SymPlaqClassG G)` from the inputs of `ClayG.clayStatementAtG_GS` at
the observer `obsXGN … hnt`**: `clayStatementAtG_GS_atAlong` at the canonical schedule
(`canonSched G = schedAlongG G (dyBetaG G)`).

DERIVED: `0` the plane and the step; `4` the dimension; `3` the last slot of the four-index `α : Idx4` in
`he1`. -/
theorem clayStatementAtG_GS_at(W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ₀)
    (hnt : ∃ u : preHG W hU hphys, inner ℂ (preVacG W hU hphys) u = 0 ∧ u ≠ 0)
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
    (wC : TSepG Cs.Ix 0 → (obsXGN W ht hU hphys hρ0 hρ1 hg hnt).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompDataG Cs) (hCO : CompOSG (canonSched G) Cs)
    (hLC : LinkCG (canonSched G) (obsXGN W ht hU hphys hρ0 hρ1 hg hnt) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (canonSched G) ρ
          (energyMapG (canonSched G) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) ((obsXGN W ht hU hphys hρ0 hρ1 hg hnt).cvec Q)
          = (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ))
    (hab : AbelianGenG G) :
    ClayStatementAtG G W (SymPlaqClassG G) :=
  clayStatementAtG_GS_atAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg hnt ρ hRie hTie hCov hCT Gk hK hAF
    hNG hWard Cs wC e he1 he2 hCD hCO hLC hX hab

/-- **`ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G)` along a coupling tower `βs`, from
the inputs of `ClayG.clayStatementAtG_GS` without `FlowConnectedNonzeroG`**, each read at
`schedAlongG G βs`, with the composites' vectors `wC`, their link `hLC` and the cross reading `hX` stated at
the pre-observer (`preHGAlong`, `preVacGAlong`, `preTimeGAlong`, `preCvecGAlong`). The observer is
`obsXGNAlong βs … hnt`, with `hnt` from `preNontrivialGAlong`: `clayStatementAtG_GS_atAlong` at that `hnt`,
whose `wC`, `hLC`, `hX` are these inputs (`obsXGN_linkC_iffAlong`, `obsXGN_cvecAlong`).

DERIVED: `0` the plane and the step; `4` the dimension; `3` the last slot of the four-index `α : Idx4` in
`he1`. -/
theorem clayStatementAtG_GS_noNTAlong (βs : ℕ → ℝ) (W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ₀)
    (ρ : RenormMixG G) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := G) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (schedAlongG G βs).a k ^ 4) atTop (𝓝 (constsG G).cTr))
    (hCov : TensorCovG (schedAlongG G βs) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (schedAlongG G βs).a k ^ 4) atTop
          (𝓝 (constsG G).cTop))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (schedAlongG G βs) ρ Gk) (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (schedAlongG G βs) ρ) (hWard : WardTG (schedAlongG G βs) ρ)
    (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → preHGAlong βs W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompDataG Cs) (hCO : CompOSG (schedAlongG G βs) Cs)
    (hLC : LinkCPreG (schedAlongG G βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
      Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (schedAlongG G βs) ρ
          (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (preCvecGAlong βs W hU hphys Q)
          = (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ))
    (hab : AbelianGenG G) :
    ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G) :=
  clayStatementAtG_GS_atAlong βs W ht hU hphys hρ0 hρ1 hg
    (preNontrivialGAlong βs W hU hphys ρ Gk hK hAF Cs wC e he1 he2 hLC) ρ hRie hTie hCov hCT Gk hK hAF
    hNG hWard Cs wC e he1 he2 hCD hCO hLC hX hab

/-- **`ClayStatementAtG G W (SymPlaqClassG G)` from the inputs of `ClayG.clayStatementAtG_GS`
without `FlowConnectedNonzeroG`**: `clayStatementAtG_GS_noNTAlong` at the canonical schedule.

DERIVED: `0` the plane and the step; `4` the dimension; `3` the last slot of the four-index `α : Idx4` in
`he1`. -/
theorem clayStatementAtG_GS_noNT(W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBG W hU) 0 hphys 0) ρ₀)
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
    (wC : TSepG Cs.Ix 0 → preHG W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompDataG Cs) (hCO : CompOSG (canonSched G) Cs)
    (hLC : LinkCPreG (canonSched G) 0 (preVacG W hU hphys) (preTimeG W hU hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (canonSched G) ρ
          (energyMapG (canonSched G) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (preCvecG W hU hphys Q)
          = (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ))
    (hab : AbelianGenG G) :
    ClayStatementAtG G W (SymPlaqClassG G) :=
  clayStatementAtG_GS_noNTAlong (dyBetaG G) W ht hU hphys hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK hAF
    hNG hWard Cs wC e he1 he2 hCD hCO hLC hX hab

variable (G) in
/-- **The conclusion of `clayStatementAtG_GS_noNTAlong` under all of its inputs except `hab`**, along a
coupling tower `βs`: `ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G)` for every `W`, the
observer inputs and transfer gap, the mixing `ρ` with its clauses, the kernel `Gk`, the composites `Cs` with
their data and pre-observer link `wC`, the index map `e` with its two clauses, and the cross reading `hX` at
`preCvecGAlong`, each read at `schedAlongG G βs`. No `FlowConnectedNonzeroG` input.

DERIVED: `0` the plane and the step; `4` the dimension. -/
def ClayAtGNoNTAlong (βs : ℕ → ℝ) : Prop :=
  ∀ (W : ConfFlowG G) {t C₀ : ℝ} (_ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ₀ : ℝ} (_hρ0 : 0 < ρ₀) (_hρ1 : ρ₀ < 1)
    (_hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ₀)
    (ρ : RenormMixG G) (_hRie : ρ.Riemann)
    (_hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := G) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (schedAlongG G βs).a k ^ 4) atTop (𝓝 (constsG G).cTr))
    (_hCov : TensorCovG (schedAlongG G βs) ρ)
    (_hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (schedAlongG G βs).a k ^ 4) atTop
          (𝓝 (constsG G).cTop))
    (Gk : ℝ → ℝ) (_hK : TwoPointKernelG (schedAlongG G βs) ρ Gk)
    (_hAF : AFCoefficientG (constsG G) Gk)
    (_hNG : NonGaussianTG (schedAlongG G βs) ρ) (_hWard : WardTG (schedAlongG G βs) ρ)
    (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → preHGAlong βs W hU hphys)
    (e : Idx4 → Cs.Ix) (_he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (_he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (_hCD : CompDataG Cs) (_hCO : CompOSG (schedAlongG G βs) Cs)
    (_hLC : LinkCPreG (schedAlongG G βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
      Cs wC)
    (_hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (schedAlongG G βs) ρ
          (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (preCvecGAlong βs W hU hphys Q)
          = (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ)),
    ClayStatementAtP (schedAlongG G βs) (constsG G) W (SymPlaqClassG G)

variable (G) in
/-- **The conclusion of `clayStatementAtG_GS_noNT` under all of its inputs except `hab`**:
`ClayAtGNoNTAlong` at the canonical schedule, `ClayStatementAtG G W (SymPlaqClassG G)` under the inputs of
`clayStatementAtG_GS_noNT`. No `FlowConnectedNonzeroG` input.

DERIVED: no numeral. -/
def ClayAtGNoNT : Prop :=
  ClayAtGNoNTAlong G (dyBetaG G)

/-- **`ClayAtGNoNTAlong G βs` from `AbelianGenG G`**: `clayStatementAtG_GS_noNTAlong` at `hab`.

DERIVED: no numeral. -/
theorem clayAtGNoNT_of_abelianGenGAlong (βs : ℕ → ℝ) (hab : AbelianGenG G) :
    ClayAtGNoNTAlong G βs := by
  intro W t C₀ ht hU r hphys ρ₀ hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK hAF hNG hWard Cs wC e
    he1 he2 hCD hCO hLC hX
  exact clayStatementAtG_GS_noNTAlong βs W ht hU hphys hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK hAF hNG
    hWard Cs wC e he1 he2 hCD hCO hLC hX hab

/-- **`ClayAtGNoNT G` from `AbelianGenG G`**: `clayAtGNoNT_of_abelianGenGAlong` at the canonical
schedule.

DERIVED: no numeral. -/
theorem clayAtGNoNT_of_abelianGenG (hab : AbelianGenG G) : ClayAtGNoNT G :=
  clayAtGNoNT_of_abelianGenGAlong (dyBetaG G) hab

end Capstone

/-! ## 6. At each compact simple group -/

section Groups

open MassGap.ClayTreeG (dyBetaG)

/-- **`ClayAtGNoNTAlong` at `SU(N)`, `N ≥ 2`, along every coupling tower `βs`** (`AbelianGen.abelianGenG_SU`). DERIVED: `2` the least `N`. -/
theorem clayAtGNoNT_SUAlong (N : ℕ) [NeZero N] [Fact (2 ≤ N)] (βs : ℕ → ℝ) : ClayAtGNoNTAlong (MassGap.SUN.SU N) βs :=
  clayAtGNoNT_of_abelianGenGAlong βs (MassGap.AbelianGen.abelianGenG_SU N)

/-- **`ClayAtGNoNT` at `SU(N)`, `N ≥ 2`**: `clayAtGNoNT_SUAlong` at the canonical schedule. DERIVED: `2` the least `N`. -/
theorem clayAtGNoNT_SU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] : ClayAtGNoNT (MassGap.SUN.SU N) :=
  clayAtGNoNT_SUAlong N (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `SO(n)`, `n ≥ 5`, along every coupling tower `βs`** (`AbelianGen.abelianGenG_SO`). DERIVED: `5` the least `n`. -/
theorem clayAtGNoNT_SOAlong (n : ℕ) [NeZero n] [Fact (5 ≤ n)] (βs : ℕ → ℝ) : ClayAtGNoNTAlong (MassGap.GaugeInstances.SO n) βs :=
  clayAtGNoNT_of_abelianGenGAlong βs (MassGap.AbelianGen.abelianGenG_SO n)

/-- **`ClayAtGNoNT` at `SO(n)`, `n ≥ 5`**: `clayAtGNoNT_SOAlong` at the canonical schedule. DERIVED: `5` the least `n`. -/
theorem clayAtGNoNT_SO (n : ℕ) [NeZero n] [Fact (5 ≤ n)] : ClayAtGNoNT (MassGap.GaugeInstances.SO n) :=
  clayAtGNoNT_SOAlong n (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `SO(3)`, along every coupling tower `βs`** (`AbelianGen.abelianGenG_SO3`). DERIVED: `3` the dimension. -/
theorem clayAtGNoNT_SO3Along (βs : ℕ → ℝ) : ClayAtGNoNTAlong (MassGap.GaugeInstances.SO 3) βs :=
  clayAtGNoNT_of_abelianGenGAlong βs MassGap.AbelianGen.abelianGenG_SO3

/-- **`ClayAtGNoNT` at `SO(3)`**: `clayAtGNoNT_SO3Along` at the canonical schedule. DERIVED: `3` the dimension. -/
theorem clayAtGNoNT_SO3 : ClayAtGNoNT (MassGap.GaugeInstances.SO 3) :=
  clayAtGNoNT_SO3Along (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at compact `Sp(n)`, along every coupling tower `βs`** (`AbelianGen.abelianGenG_USp`). DERIVED: no numeral. -/
theorem clayAtGNoNT_USpAlong (n : ℕ) [NeZero n] (βs : ℕ → ℝ) : ClayAtGNoNTAlong (MassGap.GaugeInstances.USp n) βs :=
  clayAtGNoNT_of_abelianGenGAlong βs (MassGap.AbelianGen.abelianGenG_USp n)

/-- **`ClayAtGNoNT` at compact `Sp(n)`**: `clayAtGNoNT_USpAlong` at the canonical schedule. DERIVED: no numeral. -/
theorem clayAtGNoNT_USp (n : ℕ) [NeZero n] : ClayAtGNoNT (MassGap.GaugeInstances.USp n) :=
  clayAtGNoNT_USpAlong n (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `G₂`, along every coupling tower `βs`** (`AbelianGen.abelianGenG_G2`). DERIVED: no numeral. -/
theorem clayAtGNoNT_G2Along (βs : ℕ → ℝ) : ClayAtGNoNTAlong MassGap.GaugeG2.G2 βs :=
  clayAtGNoNT_of_abelianGenGAlong βs MassGap.AbelianGen.abelianGenG_G2

/-- **`ClayAtGNoNT` at `G₂`**: `clayAtGNoNT_G2Along` at the canonical schedule. DERIVED: no numeral. -/
theorem clayAtGNoNT_G2 : ClayAtGNoNT MassGap.GaugeG2.G2 :=
  clayAtGNoNT_G2Along (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `F₄`, along every coupling tower `βs`** (`AbelianGenX.abelianGenG_F4`). DERIVED: no numeral. -/
theorem clayAtGNoNT_F4Along (βs : ℕ → ℝ) : ClayAtGNoNTAlong MassGap.GaugeF4.F4 βs :=
  clayAtGNoNT_of_abelianGenGAlong βs MassGap.AbelianGenX.abelianGenG_F4

/-- **`ClayAtGNoNT` at `F₄`**: `clayAtGNoNT_F4Along` at the canonical schedule. DERIVED: no numeral. -/
theorem clayAtGNoNT_F4 : ClayAtGNoNT MassGap.GaugeF4.F4 :=
  clayAtGNoNT_F4Along (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `E₆`, along every coupling tower `βs`** (`AbelianGenX.abelianGenG_E6`). DERIVED: no numeral. -/
theorem clayAtGNoNT_E6Along (βs : ℕ → ℝ) : ClayAtGNoNTAlong MassGap.GaugeE6.E6 βs :=
  clayAtGNoNT_of_abelianGenGAlong βs MassGap.AbelianGenX.abelianGenG_E6

/-- **`ClayAtGNoNT` at `E₆`**: `clayAtGNoNT_E6Along` at the canonical schedule. DERIVED: no numeral. -/
theorem clayAtGNoNT_E6 : ClayAtGNoNT MassGap.GaugeE6.E6 :=
  clayAtGNoNT_E6Along (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `E₇`, along every coupling tower `βs`** (`AbelianGenE7.abelianGenG_E7`). DERIVED: no numeral. -/
theorem clayAtGNoNT_E7Along (βs : ℕ → ℝ) : ClayAtGNoNTAlong MassGap.GaugeE7.E7 βs :=
  clayAtGNoNT_of_abelianGenGAlong βs MassGap.AbelianGenE7.abelianGenG_E7

/-- **`ClayAtGNoNT` at `E₇`**: `clayAtGNoNT_E7Along` at the canonical schedule. DERIVED: no numeral. -/
theorem clayAtGNoNT_E7 : ClayAtGNoNT MassGap.GaugeE7.E7 :=
  clayAtGNoNT_E7Along (dyBetaG _)

/-- **`ClayAtGNoNTAlong` at `E₈`, along every coupling tower `βs`** (`AbelianGenX.abelianGenG_E8`). DERIVED: no numeral. -/
theorem clayAtGNoNT_E8Along (βs : ℕ → ℝ) : ClayAtGNoNTAlong MassGap.GaugeE8.E8 βs :=
  clayAtGNoNT_of_abelianGenGAlong βs MassGap.AbelianGenX.abelianGenG_E8

/-- **`ClayAtGNoNT` at `E₈`**: `clayAtGNoNT_E8Along` at the canonical schedule. DERIVED: no numeral. -/
theorem clayAtGNoNT_E8 : ClayAtGNoNT MassGap.GaugeE8.E8 :=
  clayAtGNoNT_E8Along (dyBetaG _)

end Groups

/-! ## 7. The root statement along a measured tower -/

section Root

open MassGap.MeasuredTower (schedAlongG MeasTowerG)
open MassGap.MeasuredSpacing (schedOS_alongG)

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- **The root statement `ClayStatementOf G` from a measured tower and the inputs of
`clayStatementAtG_GS_noNTAlong` along it.** A measured tower `βs` (`MeasTowerG G βs`), and at its schedule
`schedAlongG G βs`: the class moments `hU` of `SymPlaqClassG G`, the physical range `hphys`, the transfer gap
of the observer at step `0` (`hρ0`, `hρ1`, `hg`), the mixing `ρ` with `hRie`, `hTie`, `hCov`, `hCT`, the kernel
`Gk` with `hK`, `hAF`, `hNG`, `hWard`, the composites `Cs` with `hCD`, `hCO`, their pre-observer vectors `wC`
and link `hLC`, the index map `e` with `he1`, `he2`, the cross reading `hX`, and `AbelianGenG G`. The class is
`SymPlaqClassG G`, reflection-closed by `SymPlaqG.symPlaqG_refl`. No input relates `βs` to `dyBetaG`.

DERIVED: `0` the plane and the step; `4` the dimension; `3` the last slot of the four-index `α : Idx4` in
`he1`. -/
theorem clayStatementOf_of_noNTAlong (βs : ℕ → ℝ) (hT : MeasTowerG G βs)
    (W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (schedAlongG G βs) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (schedAlongG G βs) r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (schedAlongG G βs) (schedOS_alongG G βs)
      (energy0G (schedAlongG G βs) W (SymPlaqClassG G) (symPlaqG_refl G))
      (preBGAlong βs W hU) 0 hphys 0) ρ₀)
    (ρ : RenormMixG G) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := G) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (schedAlongG G βs).a k ^ 4) atTop (𝓝 (constsG G).cTr))
    (hCov : TensorCovG (schedAlongG G βs) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (schedAlongG G βs).a k ^ 4) atTop
          (𝓝 (constsG G).cTop))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (schedAlongG G βs) ρ Gk) (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (schedAlongG G βs) ρ) (hWard : WardTG (schedAlongG G βs) ρ)
    (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → preHGAlong βs W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompDataG Cs) (hCO : CompOSG (schedAlongG G βs) Cs)
    (hLC : LinkCPreG (schedAlongG G βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
      Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (schedAlongG G βs) ρ
          (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (preCvecGAlong βs W hU hphys Q)
          = (mixTG (schedAlongG G βs) ρ (energyMapG (schedAlongG G βs) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ))
    (hab : AbelianGenG G) :
    ClayStatementOf G :=
  ⟨βs, hT, W, SymPlaqClassG G, symPlaqG_refl G,
    clayStatementAtG_GS_noNTAlong βs W ht hU hphys hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK hAF hNG hWard
      Cs wC e he1 he2 hCD hCO hLC hX hab⟩

end Root

end MassGap.ClayGFinal

end

#print axioms MassGap.ClayGFinal.flowN_time_group_of_gapG_noNT
#print axioms MassGap.ClayGFinal.linkCG_iff_pre
#print axioms MassGap.ClayGFinal.exists_orth_ne_zero_of_gramG
#print axioms MassGap.ClayGFinal.preNontrivialG
#print axioms MassGap.ClayGFinal.observerOSDataSGN
#print axioms MassGap.ClayGFinal.obsXGN_gap
#print axioms MassGap.ClayGFinal.obsXGN_SM
#print axioms MassGap.ClayGFinal.obsXG'_linkC_iff
#print axioms MassGap.ClayGFinal.obsXGN_linkC_iff
#print axioms MassGap.ClayGFinal.obsXG'_cvec
#print axioms MassGap.ClayGFinal.obsXGN_cvec
#print axioms MassGap.ClayGFinal.clayStatementAtG_GS_at
#print axioms MassGap.ClayGFinal.clayStatementAtG_GS_noNT
#print axioms MassGap.ClayGFinal.clayAtGNoNT_of_abelianGenG
#print axioms MassGap.ClayGFinal.clayAtGNoNT_SU
#print axioms MassGap.ClayGFinal.clayAtGNoNT_SO
#print axioms MassGap.ClayGFinal.clayAtGNoNT_SO3
#print axioms MassGap.ClayGFinal.clayAtGNoNT_USp
#print axioms MassGap.ClayGFinal.clayAtGNoNT_G2
#print axioms MassGap.ClayGFinal.clayAtGNoNT_F4
#print axioms MassGap.ClayGFinal.clayAtGNoNT_E6
#print axioms MassGap.ClayGFinal.clayAtGNoNT_E7
#print axioms MassGap.ClayGFinal.clayAtGNoNT_E8
#print axioms MassGap.ClayGFinal.preNontrivialGAlong
#print axioms MassGap.ClayGFinal.obsXGN_gapAlong
#print axioms MassGap.ClayGFinal.obsXGN_SMAlong
#print axioms MassGap.ClayGFinal.obsXGN_obsGenAlong
#print axioms MassGap.ClayGFinal.obsXGN_linkC_iffAlong
#print axioms MassGap.ClayGFinal.obsXGN_cvecAlong
#print axioms MassGap.ClayGFinal.clayStatementAtG_GS_atAlong
#print axioms MassGap.ClayGFinal.clayStatementAtG_GS_noNTAlong
#print axioms MassGap.ClayGFinal.clayAtGNoNT_of_abelianGenGAlong
#print axioms MassGap.ClayGFinal.clayAtGNoNT_SUAlong
#print axioms MassGap.ClayGFinal.clayAtGNoNT_SOAlong
#print axioms MassGap.ClayGFinal.clayAtGNoNT_SO3Along
#print axioms MassGap.ClayGFinal.clayAtGNoNT_USpAlong
#print axioms MassGap.ClayGFinal.clayAtGNoNT_G2Along
#print axioms MassGap.ClayGFinal.clayAtGNoNT_F4Along
#print axioms MassGap.ClayGFinal.clayAtGNoNT_E6Along
#print axioms MassGap.ClayGFinal.clayAtGNoNT_E7Along
#print axioms MassGap.ClayGFinal.clayAtGNoNT_E8Along
#print axioms MassGap.ClayGFinal.clayStatementOf_of_noNTAlong
