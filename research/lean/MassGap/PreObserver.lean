import Mathlib
import MassGap.ClaySU

/-!
# The SU(N) capstone without `FlowConnectedNonzero`

`ClaySU.clayStatementAt_SU` takes `hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N)
(symPlaq_refl N)) 0 r`. Its one consumer is the `nontrivial` field of the observer's `OSDataS`
(through `ContinuumTimeGroup.flowN_time_group_of_gap`). This module fills that field from the
composites' link instead.

* `flowN_time_group_of_gap_noNT` — the rate `μ > 0` and `TimeGroupAt` at `μ` from the inputs of
  `flowN_time_group_of_gap` without `hNT` (`FlowCapstone.flow_gap_of_abs_cluster`,
  `ObserverGapScale.flowClusterAbs_iff_gapAt`, `flow_time_group`).
* `preH`, `preVac`, `preTime`, `preCvec` — the pre-observer: the flowed reconstruction's Hilbert
  space `FlowH`, vacuum `vacT`, time translations `timeT` and compact vectors `gvecT` of
  `energy0 W (SymPlaqClass N) (symPlaq_refl N)` at the plane `0`. None of them reads `hNT`.
* `LinkCPre` — the three clauses of `LinkC` on a Hilbert space with a vacuum and time translations;
  `linkC_iff_pre`: `LinkC hN X C wC ↔ LinkCPre hN τ X.base.vac X.base.time C wC` by `Iff.rfl`.
* `exists_orth_ne_zero_of_gram` — the argument of `SUInputs.hnt_of_gram` on any complex inner
  product space: a non-zero vector orthogonal to `vac` from the Gram identity, `w ∅ = vac`,
  `TwoPointKernel` and `AFCoefficient`. `preNontrivial` — it at `w := LinkReduce.wOfC e wC` on the
  pre-observer, from `LinkCPre` and the two clauses of `e` (`LinkReduce.gram_wOfC`, `wOfC_empty`).
* `observerOSDataSN`, `observerOSDataSLinkedN`, `obsXN` — `observerOSDataS`,
  `observerOSDataSLinked`, `SUInputs.obsX'` with the `nontrivial` field given as an input `hnt` in
  place of `hNT`; the rate from `flowN_time_group_of_gap_noNT`.
* `obsX'_linkC_iff`, `obsXN_linkC_iff`, `obsX'_cvec`, `obsXN_cvec` — `LinkC` at `obsX' … hNT …` and
  at `obsXN … hnt` are both `LinkCPre` at the pre-observer, and both `cvec` are `preCvec`, by `rfl`.
* `clayStatementAt_SU_at` — the proof of `ClaySU.clayStatementAt_SU` at `obsXN … hnt`, with `hnt`
  in place of `hNT` and `wC`, `hLC`, `hX` typed at `obsXN … hnt`.
* `clayStatementAt_SU_noNT` — the statement of `ClaySU.clayStatementAt_SU` without `hNT`, with
  `wC`, `hLC`, `hX` stated at the pre-observer; `hnt` is `preNontrivial`.

DERIVED (module-wide): `2` the least colour count; `0` the plane, the step, the vanishing pairing
and the zero vector; `1` the window and the top of the rate; `8`, `4` as in `ScalarTie`; `16`, `8`
as in `SUInputs.hnt_of_gram`.
-/

noncomputable section

namespace MassGap.PreObserver

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The time group without `FlowConnectedNonzero` -/

section TimeGroup

/-- **The continuous-time picture of the flowed reconstruction from one gap at one step**: the
inputs of `ContinuumTimeGroup.flowN_time_group_of_gap` without `FlowConnectedNonzero` give a rate
`μ > 0` and `TimeGroupAt` at `μ`.

DERIVED: `0` the sign of `μ`, `L`, `ρ` and the lower end of the rate; `1` the top of `ρ`; `4` in
`Fin 4` the spacetime dimension. -/
theorem flowN_time_group_of_gap_noNT (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ) :
    ∃ μ : ℝ, 0 < μ
      ∧ TimeGroupAt hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ) μ := by
  obtain ⟨c, hc, hga⟩ := FlowCapstone.flow_gap_of_abs_cluster hN Φ hB τ
    (Flow.posPreserving_of_physRange hN Φ hphys τ)
    ((ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB τ
      (Flow.posPreserving_of_physRange hN Φ hphys τ) m0 hL).mpr ⟨ρ, hρ0, hρ1, hg⟩)
  have hgap : ∀ m : ℕ, ContinuumClay.GappedAt
      (flowTransfer hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ) m)
      (Real.exp (-(c / L) * dySpacing N m)) := by
    intro m
    have hr0 : 0 < Real.exp (-(c / L) * dySpacing N m) := Real.exp_pos _
    have hr1 : Real.exp (-(c / L) * dySpacing N m) < 1 := by
      rw [Real.exp_lt_one_iff, neg_mul]
      exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (dySpacing_pos (one_le_of_ne_zero hN) m))
    refine ⟨hr0, hr1, hga m, fun u hu => GapToOperator.norm_opT_le_of_orth _ hr0.le (hga m) u hu,
      ?_, GNSHilbert.isGreatest_one_spectrum_opT _⟩
    intro x hx
    rcases GapToOperator.spectrum_opT_subset _ hr0.le (hga m) hx with h | h
    · exact Or.inl h
    · exact Or.inr ⟨Set.mem_Ici.mp (GNSHilbert.spectrum_opT_nonneg _
        (flowTransfer_positive hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ) m) hx),
        h.2⟩
  exact ⟨c / L, div_pos hc hL, flow_time_group hN Φ hB τ
    (Flow.posPreserving_of_physRange hN Φ hphys τ) (div_pos hc hL).le hgap⟩

end TimeGroup

/-! ## 2. The pre-observer -/

section Pre

/-- The uniform bound of `energy0 W (SymPlaqClass N) (symPlaq_refl N)` from the class moments.
DERIVED: no numeral. -/
abbrev preB (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) :
    UniformBoundF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) :=
  uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
    (SUInputs.symPlaq_cube_of_classMoments hN W hU)

/-- The pre-observer's Hilbert space: `FlowH` of `energy0 W (SymPlaqClass N) (symPlaq_refl N)` at
the plane `0`. DERIVED: `0` the plane. -/
abbrev preH (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) : Type :=
  FlowH hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
    (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0)

/-- The pre-observer's vacuum `vacT`. DERIVED: `0` the plane. -/
abbrev preVac (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) : preH hN W hU hphys :=
  vacT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
    (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0)

/-- The pre-observer's time translations `timeT`. DERIVED: `0` the plane. -/
abbrev preTime (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) :
    ℝ → preH hN W hU hphys →L[ℂ] preH hN W hU hphys :=
  timeT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
    (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0)

/-- The pre-observer's compact vectors `gvecT`. DERIVED: `0` the plane. -/
abbrev preCvec (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (Q : MarginMonoD N (SymPlaqClass N) 0 r) : preH hN W hU hphys :=
  gvecT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
    (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0) Q.1

/-- **The three clauses of `LinkC`** on a complex inner product space with a vacuum `vac` and time
translations `time`: the Gram identity with the convergence of the lattice sequence of `ΘP ∪ Q`, the
dyadic shift as `time`, and `wC ∅ = vac`.

DERIVED: no numeral. -/
def LinkCPre (hN : N ≠ 0) (τ : Fin 4) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (vac : H) (time : ℝ → H →L[ℂ] H) (C : Composites N) (wC : TSepG C.Ix τ → H) : Prop :=
  (∀ P Q : TSepG C.Ix τ,
      Tendsto (fun k => latC hN C k (pairC C τ P.1 Q.1)) (ultra : Filter ℕ)
          (𝓝 (contC hN C (pairC C τ P.1 Q.1)))
        ∧ inner ℂ (wC P) (wC Q) = (kernC hN C τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSepG C.Ix τ), wC (shiftT hN τ m P) = time (dySpacing N m) (wC P))
    ∧ wC (emptyG C.Ix τ) = vac

/-- **`LinkC` is `LinkCPre` at the vacuum and time translations of `X.base`.**

DERIVED: no numeral. -/
theorem linkC_iff_pre (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (C : Composites N) (wC : TSepG C.Ix τ → X.base.H) :
    LinkC hN X C wC ↔ LinkCPre hN τ X.base.vac X.base.time C wC :=
  Iff.rfl

end Pre

/-! ## 3. A non-zero vector orthogonal to the vacuum on the pre-observer -/

section Nontrivial

/-- **A non-zero vector orthogonal to `vac`** in any complex inner product space carrying a family
`w` with the Gram identity `⟪w P, w Q⟫ = kernT P Q` and `w ∅ = vac`, from `TwoPointKernel` and
`AFCoefficient`: `w` at one trace insertion smeared with the bump (`SUInputs.oneT`).

DERIVED: `2` the least colour count; `0` the time axis, the vanishing pairing and the zero vector;
`8` as in `SUInputs.eDist_bounds_of_bump`. CHOSEN: `16 = 2 · 8`, as in `SUInputs.hnt_of_gram`. -/
theorem exists_orth_ne_zero_of_gram (hN2 : 2 ≤ N) (hN : N ≠ 0) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (vac : H) (ρ : RenormMix N) (w : TSep 0 → H)
    (hin : ∀ P Q : TSep 0, inner ℂ (w P) (w Q) = (kernT hN ρ 0 P Q : ℂ))
    (hvac : w (emptyT 0) = vac) (G : ℝ → ℝ)
    (hK : TwoPointKernel hN ρ G) (hAF : AFCoefficient N G) :
    ∃ u : H, inner ℂ vac u = 0 ∧ u ≠ 0 := by
  obtain ⟨δ, hδ, -, hb⟩ :=
    ContinuumNontrivial.af_bounds_on_interval (afShortDistance_of_coefficient hN2 hAF)
  have hl : 0 < δ / 16 := div_pos hδ (by norm_num)
  obtain ⟨g₀, g₁, hg₀, hG⟩ := hb (δ / 16) (8 * (δ / 16)) hl (by linarith) (by linarith)
  have hcont_r : Continuous ((SUInputs.bumpT hl.le).reflect 0).1 :=
    (SUInputs.continuous_bumpF (δ / 16)).comp (continuous_id.update 0 (continuous_apply 0).neg)
  have hkk : kernT hN ρ 0 (SUInputs.oneT hl) (SUInputs.oneT hl) ≠ 0 := by
    rw [SUInputs.kernT_oneT_eq hN ρ hl,
      hK.2 _ _ hcont_r (SUInputs.continuous_bumpF (δ / 16)) ⟨δ / 16, hl, SUInputs.sepBy_bump hl⟩]
    exact (SUInputs.kernel_integral_pos hK.1 hl hg₀ (fun r h1 h2 => (hG r h1 h2).1)).ne'
  refine ⟨w (SUInputs.oneT hl), ?_, ?_⟩
  · rw [← hvac, hin, SUInputs.kernT_empty_oneT hN ρ hl, Complex.ofReal_zero]
  · intro h0
    apply hkk
    have h := hin (SUInputs.oneT hl) (SUInputs.oneT hl)
    rw [h0, inner_zero_left] at h
    exact_mod_cast h.symm

/-- **The pre-observer has a non-zero vector orthogonal to its vacuum**, from `LinkCPre` of a
family `wC` of composites' vectors in `preH`, the two clauses of an index map `e`, `TwoPointKernel`
and `AFCoefficient`: `exists_orth_ne_zero_of_gram` at `w := LinkReduce.wOfC e wC`, with the Gram
identity from `LinkReduce.gram_wOfC` and `w ∅ = preVac` from `LinkReduce.wOfC_empty`.

DERIVED: `2` the least colour count; `0` the plane, the vanishing pairing and the zero vector;
`1`–`3` the slots. -/
theorem preNontrivial (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (ρ : RenormMix N) (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G)
    (hAF : AFCoefficient N G) (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys) Cs wC) :
    ∃ u : preH (ne_zero_of_two_le hN2) W hU hphys,
      inner ℂ (preVac (ne_zero_of_two_le hN2) W hU hphys) u = 0 ∧ u ≠ 0 :=
  exists_orth_ne_zero_of_gram hN2 (ne_zero_of_two_le hN2) _ ρ (LinkReduce.wOfC e wC)
    (LinkReduce.gram_wOfC (ne_zero_of_two_le hN2) ρ Cs wC e he1 he2 hLC.1)
    (LinkReduce.wOfC_empty e wC hLC.2.2) G hK hAF

end Nontrivial

/-! ## 4. The observer with the non-trivial vector as an input -/

section Observer

/-- **`observerOSDataS` with the non-trivial vector as an input.** The inputs of `observerOSDataS`
with `hNT` replaced by `hnt`, a non-zero vector of `FlowH` orthogonal to `vacT`; the rate is that
of `flowN_time_group_of_gap_noNT`, and `nontrivial := hnt`.

DERIVED: `0` the excluded colour count, the signs, the reference step and the time origin; `1` the
top of `ρ`; `4` in `Fin 4` the spacetime dimension. -/
def observerOSDataSN (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hnt : ∃ u : FlowH hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
        (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ),
      inner ℂ (vacT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
        (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)) u = 0 ∧ u ≠ 0) :
    OSDataS :=
  let hB := uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ
  let hT := flowN_time_group_of_gap_noNT hN (energy0 W D hD) hB τ hphys m0 hL hρ0 hρ1 hg
  let hgr := abs_schwCML_le hN W hD hpos hO h
  let μ := Classical.choose hT
  have hμ := Classical.choose_spec hT
  { S := schwCML hN W hD hpos hO h
    α := Classical.choose hgr
    γ := Classical.choose (Classical.choose_spec hgr)
    growth := Classical.choose_spec (Classical.choose_spec hgr)
    os3 := fun n σ φ => by
      show schwSF hN W D hD O (fun i => ofE4 ((φ ∘ σ) i)) = schwSF hN W D hD O (fun i => ofE4 (φ i))
      exact schwSF_comp_perm hN W D hD O σ (fun i => ofE4 (φ i))
    H := FlowH hN (energy0 W D hD) hB τ hpp
    vac := vacT hN (energy0 W D hD) hB τ hpp
    time := timeT hN (energy0 W D hD) hB τ hpp
    gap := μ
    gap_pos := hμ.1
    time_zero := hμ.2.1
    time_add := hμ.2.2.1
    time_selfAdjoint := fun t ht => ⟨(hμ.2.2.2.2.1 t ht).2.1, (hμ.2.2.2.2.1 t ht).2.2⟩
    time_cont := hμ.2.2.2.2.2.1
    time_vac := hμ.2.2.2.2.2.2.1
    time_gap := hμ.2.2.2.2.2.2.2.1
    nontrivial := hnt }

/-- **`observerOSDataSLinked` over `observerOSDataSN`**: the same `SM`, `O`, `vec`, `cvec` and
proofs, with `base := observerOSDataSN … hnt`.

DERIVED: `0` the excluded colour count, the signs and the reference step; `1` the top of `ρ`; `4` in
`Fin 4` the spacetime dimension. -/
def observerOSDataSLinkedN (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hnt : ∃ u : FlowH hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
        (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ),
      inner ℂ (vacT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
        (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)) u = 0 ∧ u ≠ 0) :
    OSDataSLinked N D τ r where
  base := observerOSDataSN hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hnt
  SM := fun O g => schwSFM hN W D hD O g
  O := O
  S_eq := fun n φ => by
    show schwCML hN W hD hpos hO h n φ = schwSFM hN W D hD (fun _ : Fin n => O) (fun i => ofE4 (φ i))
    rw [schwCML_apply]
    exact schwSF_eq_schwSFM hN W hD hpos ht hC0 hU hO _
  vec := vecD hN W hD hpos hcube τ hphys
  inner_vec := inner_vecD hN W hD hpos hcube ht hC0 hU τ hphys
  cvec := fun Q => gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
    (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) Q.1
  vec_compact := vecD_ofMarginD hN W hD hpos hcube ht hC0 hU τ hphys
  closure_eq := closure_range_vecD hN W hD hpos hcube ht hC0 hU τ hphys

/-- **`SUInputs.obsX'` with the non-trivial vector as an input**: `observerOSDataSLinkedN` at the
arguments of `obsX'`, with `hnt` in place of `hNT`.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXN (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    OSDataSLinked N (SymPlaqClass N) 0 r :=
  observerOSDataSLinkedN hN W (symPlaq_refl N) (symPlaq_nonneg hN)
    (SUInputs.symPlaq_cube_of_classMoments hN W hU) ht
    (zero_le_one.trans (SUInputs.one_le_of_classMoments hN W hU))
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) SUInputs.q0_mem
    (SUInputs.unitCubeExpBound_of_cubeMomentsAt hN W ht (hU _ SUInputs.q0_mem)) 0 hphys 0 one_pos
    (Classical.choose_spec (SUInputs.gapEx' hN2 hN W hU hphys hfar)).1
    (Classical.choose_spec (SUInputs.gapEx' hN2 hN W hU hphys hfar)).2.1
    (Classical.choose_spec (SUInputs.gapEx' hN2 hN W hU hphys hfar)).2.2 hnt

/-- **The Hamiltonian gap of `obsXN`**, from its self-adjoint generator (as `SUInputs.obsX'_gap`).

DERIVED: `0` the plane. -/
theorem obsXN_gap (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    HamiltonianGap (obsXN hN2 hN W ht hU hphys hfar hnt).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjoint hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (preB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0))

/-- **The functional of `obsXN` is `schwSFM`**, by definition. DERIVED: no numeral. -/
theorem obsXN_SM (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      (obsXN hN2 hN W ht hU hphys hfar hnt).SM O g
        = schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g :=
  fun _ _ _ _ => rfl

/-- **`obsXN` carries its Hilbert space**: `v = gvecT` of the pre-observer
(`ClayStatement.obsGen_flow`).

DERIVED: `0` the plane. -/
theorem obsXN_obsGen (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    ObsGen hN W (SymPlaqClass N) (symPlaq_refl N) (obsXN hN2 hN W ht hU hphys hfar hnt) :=
  ⟨gvecT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0),
    fun _ => rfl, obsGen_flow hN W (SymPlaqClass N) (symPlaq_refl N) (preB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0)⟩

/-- **`LinkC` at `SUInputs.obsX' … hNT …` is `LinkCPre` at the pre-observer**, for every `hNT`.

DERIVED: `0` the plane. -/
theorem obsX'_linkC_iff (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH hN W hU hphys) :
    LinkC hN (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar) Cs wC
      ↔ LinkCPre hN 0 (preVac hN W hU hphys) (preTime hN W hU hphys) Cs wC :=
  Iff.rfl

/-- **`LinkC` at `obsXN … hnt` is `LinkCPre` at the pre-observer**, for every `hnt`.

DERIVED: `0` the plane. -/
theorem obsXN_linkC_iff (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0)
    (Cs : Composites N) (wC : TSepG Cs.Ix 0 → preH hN W hU hphys) :
    LinkC hN (obsXN hN2 hN W ht hU hphys hfar hnt) Cs wC
      ↔ LinkCPre hN 0 (preVac hN W hU hphys) (preTime hN W hU hphys) Cs wC :=
  Iff.rfl

/-- **The compact vectors of `SUInputs.obsX' … hNT …` are `preCvec`**, for every `hNT`.

DERIVED: `0` the plane. -/
theorem obsX'_cvec (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) (Q : MarginMonoD N (SymPlaqClass N) 0 r) :
    (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).cvec Q = preCvec hN W hU hphys Q :=
  rfl

/-- **The compact vectors of `obsXN … hnt` are `preCvec`**, for every `hnt`.

DERIVED: `0` the plane. -/
theorem obsXN_cvec (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0)
    (Q : MarginMonoD N (SymPlaqClass N) 0 r) :
    (obsXN hN2 hN W ht hU hphys hfar hnt).cvec Q = preCvec hN W hU hphys Q :=
  rfl

end Observer

/-! ## 5. The capstone -/

section Capstone

/-- **`ClayStatementAt` at `SymPlaqClass N` from the inputs of `ClaySU.clayStatementAt_SU` at the
observer `obsXN … hnt`**: `hNT` replaced by `hnt`, and `wC`, `hLC`, `hX` typed at `obsXN … hnt`.
The proof is that of `clayStatementAt_SU` with `obsX'` replaced by `obsXN`.

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `8`, `4` as in
`ScalarTie`; `0`, `1`, `2`, `3` the four slots of a rank-four component `Idx4`. -/
theorem clayStatementAt_SU_at (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (hnt : ∃ u : preH (ne_zero_of_two_le hN2) W hU hphys,
      inner ℂ (preVac (ne_zero_of_two_le hN2) W hU hphys) u = 0 ∧ u ≠ 0)
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
    (wC : TSepG Cs.Ix 0 → (obsXN hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkC (ne_zero_of_two_le hN2)
      (obsXN hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            ((obsXN hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt).cvec Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hConv := CompReduce.sepConv_of_comp (ne_zero_of_two_le hN2) ρ Cs e he2 hCO.1
  have hHS := LinkReduce.linkHS_of_comp (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) _ ρ Cs wC hLC e he1 he2 hX
  obtain ⟨Mb, Zc, hCT1, hCT2⟩ := hCT
  exact clayStatementAt_of_link hN2 W (SymPlaqClass N) (symPlaq_refl N)
    (obsXN hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt) ρ G
    (LinkReduce.wOfC e wC)
    (obsXN_SM hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt)
    (obsXN_gap hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt)
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
    (obsXN_obsGen hN2 (ne_zero_of_two_le hN2) W ht hU hphys hfar hnt)

/-- **`ClayStatementAt` at `SymPlaqClass N` from the inputs of `ClaySU.clayStatementAt_SU` without
`FlowConnectedNonzero`**, with the composites' vectors `wC`, their link `hLC` and the cross reading
`hX` stated at the pre-observer (`preH`, `preVac`, `preTime`, `preCvec`). The observer is
`obsXN … hnt`, with `hnt` from `preNontrivial`: `clayStatementAt_SU_at` at that `hnt`, whose `wC`,
`hLC`, `hX` are these inputs (`obsXN_linkC_iff`, `obsXN_cvec`).

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `8`, `4` as in
`ScalarTie`; `0`, `1`, `2`, `3` the four slots of a rank-four component `Idx4`. -/
theorem clayStatementAt_SU_noNT (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
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
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
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
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_at hN2 W ht hU hphys hfar
    (preNontrivial hN2 W hU hphys ρ G hK hAF Cs wC e he1 he2 hLC) ρ hRie hTie hCov hCT G hK hAF
    hNG hWard Cs wC e he1 he2 hCD hCO hLC hX

end Capstone

end MassGap.PreObserver

end

#print axioms MassGap.PreObserver.flowN_time_group_of_gap_noNT
#print axioms MassGap.PreObserver.linkC_iff_pre
#print axioms MassGap.PreObserver.exists_orth_ne_zero_of_gram
#print axioms MassGap.PreObserver.preNontrivial
#print axioms MassGap.PreObserver.obsXN_gap
#print axioms MassGap.PreObserver.obsXN_SM
#print axioms MassGap.PreObserver.obsX'_linkC_iff
#print axioms MassGap.PreObserver.obsXN_linkC_iff
#print axioms MassGap.PreObserver.obsX'_cvec
#print axioms MassGap.PreObserver.obsXN_cvec
#print axioms MassGap.PreObserver.clayStatementAt_SU_at
#print axioms MassGap.PreObserver.clayStatementAt_SU_noNT
