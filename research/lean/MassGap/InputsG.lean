import Mathlib
import MassGap.ObserverLinkedG
import MassGap.SUInputs

/-!
# MassGap.InputsG — the observer inputs over `G` from the class moments

The mirror of `SUInputs` over a schedule `S` of a `GaugeGroup G`:

| `SUInputs` (`SU(N)`) | here (any `G`, `S`) | input it reads |
|---|---|---|
| `symPlaq_cube_of_classMoments` | `cube_of_classMomentsG` | `ClassMomentsG S W D t C` |
| `one_le_of_classMoments` | `one_le_of_classMomentsG` | `ClassMomentsG` at a field of `D` |
| `unitCubeExpBound_of_cubeMomentsAt` | `unitCubeExpBoundG_of_cubeMomentsAtG` | `CubeMomentsAtG`, `0 < t` |
| `kernT_oneT_eq`, `latT_empty_oneT`, `kernT_empty_oneT` | `kernTG_oneT_eq`, `latTG_empty_oneT`, `kernTG_empty_oneT` | `SchedShiftInv S` (the last two) |
| `hnt_of_gram` | `hnt_of_gramG` | `SchedShiftInv S`, `0 < K.cAF` |
| `obsX'`, `obsX'_SM`, `obsX'_gap` | `obsXG'`, `obsXG'_SM`, `obsXG'_O`, `obsXG'_gap` | the transfer gap `hg` |

The group-free parts of `SUInputs` (the bump `bumpT`, the insertion `oneT`, `reflC_trC`,
`twoEquiv`, `pairT_oneT_comp`, `sepBy_bump`, `kernel_integral_pos`, `moment_term_eq`) are used as
they are.

`stateG_smear_connected`: on a schedule with `SchedShiftInv S`, `ν_k(smear a_k (O − ν_k O) f) = 0`
(`ContinuumField.state_transObs`).

`obsXG'` is `ObserverLinkedG.observerOSDataSLinkedG` at `canonSched G`, `D = SymPlaqClassG G`, the
field `symG (plaqFieldG q0)`, the plane `0`, the step `0`, the window `1`, with `hcube`, `hC0`, `hUE`
from the class moments. The transfer gap `hg` at a rate `0 < ρ < 1` is an input.

DERIVED (module-wide): `0` the plane, the step, the time axis and the vanishing values; `1` the
window and the unit observable; `2`, `8`, `16`, `81`, `162` as in `SUInputs`.
-/

noncomputable section

namespace MassGap.InputsG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz
  MassGap.ObserverOSTempered MassGap.ObserverEnergyBox MassGap.ObserverOSEuclidS
  MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked MassGap.ClayFull MassGap.ClayStatement
  MassGap.ClayTreeG MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.SUInputs Filter
open scoped Topology Matrix

/-! ## 1. The class moments give the cube bounds, `C ≥ 1` and the unit-cube exponential moment -/

section Moments

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **`CubeMomentBoundG` on the class from the class moments.** DERIVED: no numeral. -/
theorem cube_of_classMomentsG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)} {t C : ℝ}
    (hU : ClassMomentsG S W D t C) : ∀ O ∈ D, CubeMomentBoundG S W O :=
  fun _ hO R hR p => ⟨_, (hU _ hO).mono fun _ hk => hk R hR p⟩

/-- **The constant of the class moments is at least `1`**: the zeroth moment at `R = 0` is
`ν_k(1) = 1 ≤ C`.

DERIVED: `0` the moment and the cube; `1` the unit observable. -/
theorem one_le_of_classMomentsG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    {O : LField G} (hO : O ∈ D) {t C : ℝ} (hU : ClassMomentsG S W D t C) : 1 ≤ C := by
  obtain ⟨k, hk⟩ := (hU _ hO).exists
  have h := hk 0 le_rfl 0
  simpa [(S.ν k).map_one] using h

/-- **The unit-cube exponential moment from the cube moments**, over a schedule. At `R = 1`,
`ν_k(E_1^{2p}) ≤ 81^{2p} (2p)! t^{-2p} C`; with `s = t/162` and `e^x ≤ 2 cosh x`,
`ν_k(e^{s E_1}) ≤ 2 C ∑_p ((81 s/t)²)^p`.

DERIVED: `81 = (2·1 + 1)⁴` the volume factor at the unit cube; `2` the even power and
`e^x ≤ 2 cosh x`. CHOSEN: `162 = 2 · 81`, so `81 s/t = 1/2`; any factor above `81` serves. -/
theorem unitCubeExpBoundG_of_cubeMomentsAtG (S : Sched G) (W : ConfFlowG G) {O : LField G}
    {t C : ℝ} (ht : 0 < t) (h : CubeMomentsAtG S W O t C) : UnitCubeExpBoundG S W O := by
  refine ⟨t / 162, 2 * (C * (1 - (81 * (t / 162) / t) ^ 2)⁻¹), div_pos ht (by norm_num),
    h.mono fun k hk => ?_⟩
  have hs : (0 : ℝ) < t / 162 := div_pos ht (by norm_num)
  set s : ℝ := t / 162 with hs_def
  set E : C(IConf G, ℝ) := cubeSumG (S.a k) 1 (W.fieldMap k O).1 with hE
  set ν := S.ν k with hν
  let f : ℕ → C(IConf G, ℝ) := fun p => (((2 * p).factorial : ℝ)⁻¹) • (s • E) ^ (2 * p)
  have hfU : ∀ p U, f p U = (s * E U) ^ (2 * p) / ((2 * p).factorial : ℝ) := by
    intro p U
    simp only [f, ContinuousMap.smul_apply, ContinuousMap.pow_apply, smul_eq_mul]
    ring
  have hb : ∀ p, ‖f p‖ ≤ ‖s • E‖ ^ (2 * p) / ((2 * p).factorial : ℝ) := by
    intro p
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun U => ?_
    rw [hfU, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have hU := (s • E).norm_coe_le_norm U
    rw [ContinuousMap.smul_apply, smul_eq_mul, Real.norm_eq_abs] at hU
    gcongr
  have hsum : Summable f := Summable.of_norm_bounded (Real.hasSum_cosh ‖s • E‖).summable hb
  have hT := hsum.hasSum
  have hpt : ∀ U, Real.exp (s * E U) ≤ 2 * (∑' p, f p) U := by
    intro U
    have h1 := (ContinuousMap.evalCLM ℝ U).hasSum hT
    simp only [ContinuousMap.evalCLM_apply] at h1
    have h2 : HasSum (fun p => f p U) (Real.cosh (s * E U)) := by
      simpa only [hfU] using Real.hasSum_cosh (s * E U)
    rw [h1.unique h2, Real.cosh_eq]
    have := Real.exp_pos (-(s * E U))
    linarith
  have hmono : ν (expC (s • E)) ≤ ν ((2 : ℝ) • ∑' p, f p) := ν.mono fun U => by
    simp only [expC_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact hpt U
  let νh : C(IConf G, ℝ) →+ ℝ :=
    { toFun := fun F => ν F, map_zero' := ν.map_zero, map_add' := ν.map_add }
  have hνT : HasSum (fun p => ν (f p)) (ν (∑' p, f p)) := hT.map νh ν.continuous
  have h81 : ((2 * (1 : ℝ) + 1) ^ 4) = 81 := by norm_num
  have hterm : ∀ p, ν (f p) ≤ C * ((81 * s / t) ^ 2) ^ p := by
    intro p
    have hfac : ((2 * p).factorial : ℝ) ≠ 0 := by positivity
    have e1 : f p = ((((2 * p).factorial : ℝ)⁻¹) * s ^ (2 * p)) • E ^ (2 * p) := by
      simp only [f, smul_pow, smul_smul]
    have hm := hk 1 zero_le_one p
    rw [h81] at hm
    rw [e1, ν.map_smul]
    calc (((2 * p).factorial : ℝ)⁻¹ * s ^ (2 * p)) * ν (E ^ (2 * p))
        ≤ (((2 * p).factorial : ℝ)⁻¹ * s ^ (2 * p))
            * ((81 : ℝ) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C)) :=
          mul_le_mul_of_nonneg_left hm
            (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hs.le _))
      _ = C * ((81 * s / t) ^ 2) ^ p := moment_term_eq _ _ _ _ _ hfac
  have hr0 : (0 : ℝ) ≤ (81 * s / t) ^ 2 := sq_nonneg _
  have hhalf : 81 * s / t = 1 / 2 := by
    rw [hs_def]
    field_simp
    ring
  have hr1 : (81 * s / t) ^ 2 < 1 := by
    rw [hhalf]
    norm_num
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left C
  have hle := hasSum_le hterm hνT hgeo
  calc ν (expC (s • E)) ≤ ν ((2 : ℝ) • ∑' p, f p) := hmono
    _ = 2 * ν (∑' p, f p) := ν.map_smul _ _
    _ ≤ 2 * (C * (1 - (81 * s / t) ^ 2)⁻¹) := by linarith

end Moments

/-! ## 2. A non-zero vector orthogonal to the vacuum -/

section Nontrivial

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A connected smeared field has mean zero** on a schedule with `SchedShiftInv S`:
`ν_k(smear a_k (O − ν_k O) f) = 0`, term by term by translation invariance.

DERIVED: `0` the value. -/
theorem stateG_smear_connected (S : Sched G) (hsh : SchedShiftInv S) (k : ℕ) (O : LField G)
    (f : TestFn) : S.ν k (smear (S.a k) (O.sub (S.ν k O.1)).1 f) = 0 := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum (S.a_pos k) _ f hf (Finset.Subset.refl _), (S.ν k).map_sum]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [(S.ν k).map_smul, state_transObs (hsh k)]
  show _ * S.ν k (O.1 - S.ν k O.1 • (1 : C(IConf G, ℝ))) = 0
  rw [(S.ν k).map_sub, (S.ν k).map_smul, (S.ν k).map_one, mul_one, sub_self, mul_zero]

/-- **`S(Θ P ∪ P)` is the trace two-point function** of the reflected bump and the bump, over a
schedule.

DERIVED: `0` the time axis; `2` the length. -/
theorem kernTG_oneT_eq (S : Sched G) (ρ : RenormMixG G) {lam : ℝ} (hl : 0 < lam) :
    kernTG S ρ 0 (oneT hl) (oneT hl) = contTrG S ρ ![(bumpT hl.le).reflect 0, bumpT hl.le] := by
  unfold kernTG contTrG contTG
  congr 1
  funext k
  exact (os3TG S ρ _ (Fin 2) (twoEquiv : Fin 2 ≃ Fin (oneT hl).1.1 ⊕ Fin (oneT hl).1.1)
    (pairT 0 (oneT hl).1 (oneT hl).1) k).symm.trans
    (congrArg (fun F : Fin 2 → TDatum => latTG S ρ k F) (pairT_oneT_comp hl))

/-- The lattice reading of `Θ∅ ∪ P` vanishes at every step: one connected field.

DERIVED: `0` the time axis and the value. -/
theorem latTG_empty_oneT (S : Sched G) (hsh : SchedShiftInv S) (ρ : RenormMixG G) {lam : ℝ}
    (hl : 0 < lam) (k : ℕ) : latTG S ρ k (pairT 0 (emptyT 0).1 (oneT hl).1) = 0 := by
  haveI : IsEmpty (Fin (emptyT (0 : Fin 4)).1.1) := by
    show IsEmpty (Fin 0)
    infer_instance
  haveI : Unique (Fin (oneT hl).1.1) := by
    show Unique (Fin 1)
    infer_instance
  unfold latTG
  refine Finset.sum_eq_zero fun b _ => mul_eq_zero_of_right _ ?_
  show S.ν k (∏ i, smear (S.a k) _ _) = 0
  rw [Fintype.prod_sum_type, Fintype.prod_empty, one_mul, Fintype.prod_unique]
  exact stateG_smear_connected S hsh k _ _

/-- **`S(Θ∅ ∪ P) = 0`** over a schedule with `SchedShiftInv S`.

DERIVED: `0` the time axis and the value. -/
theorem kernTG_empty_oneT (S : Sched G) (hsh : SchedShiftInv S) (ρ : RenormMixG G) {lam : ℝ}
    (hl : 0 < lam) : kernTG S ρ 0 (emptyT 0) (oneT hl) = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold kernTG contTG
  have e : (fun k => latTG S ρ k (pairT 0 (emptyT 0).1 (oneT hl).1)) = fun _ => (0 : ℝ) :=
    funext (latTG_empty_oneT S hsh ρ hl)
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

/-- **A non-zero vector of `HLsG X w` orthogonal to the vacuum**, over a schedule with
`SchedShiftInv S` and constants with `0 < K.cAF`, from the Gram identity, `w ∅ = vac`,
`TwoPointKernelG` and `AFCoefficientG`. For `P` one trace insertion smeared with the bump at
`λ = δ/16`, `⟪vac, w P⟫ = S(Θ∅ ∪ P) = 0` and `‖w P‖² = S(Θ P ∪ P) > 0`.

DERIVED: `0` the time axis, the vanishing pairing and the zero vector; `8` as in
`SUInputs.eDist_bounds_of_bump`. CHOSEN: `16 = 2 · 8`, so `8λ = δ/2 < δ`; any factor above `8`
serves. -/
theorem hnt_of_gramG (S : Sched G) (hsh : SchedShiftInv S) (K : ClayConsts) (hKpos : 0 < K.cAF)
    {D : Set (LField G)} {r : ℝ} (X : OSDataSLinkedG G D 0 r) (ρ : RenormMixG G)
    (w : TSep 0 → X.base.H)
    (hin : ∀ P Q : TSep 0, inner ℂ (w P) (w Q) = (kernTG S ρ 0 P Q : ℂ))
    (hvac : w (emptyT 0) = X.base.vac) (Gk : ℝ → ℝ)
    (hK : TwoPointKernelG S ρ Gk) (hAF : AFCoefficientG K Gk) :
    ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0 := by
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
  refine ⟨w (oneT hl), Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨oneT hl, rfl⟩),
    ?_, ?_⟩
  · rw [← hvac, hin, kernTG_empty_oneT S hsh ρ hl, Complex.ofReal_zero]
  · intro h0
    apply hkk
    have h := hin (oneT hl) (oneT hl)
    rw [h0, inner_zero_left] at h
    exact_mod_cast h.symm

end Nontrivial

/-! ## 3. The observer from the class moments, at the canonical schedule -/

section Observer

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- **The observer over `G` at the field `symG (plaqFieldG q0)`** from the class moments, at
`canonSched G`, the plane `0` and the step `0`: `observerOSDataSLinkedG` with `hcube`, `hC0`, `hUE`
given by `cube_of_classMomentsG`, `one_le_of_classMomentsG`, `unitCubeExpBoundG_of_cubeMomentsAtG`.
The transfer gap `hg` at a rate `0 < ρ < 1` is an input.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXG' (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ) :
    OSDataSLinkedG G (SymPlaqClassG G) 0 r :=
  observerOSDataSLinkedG (canonSched G) schedOS_canonSched schedShiftInv_canonSched W
    (symPlaqG_refl G) symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU) ht
    (zero_le_one.trans (one_le_of_classMomentsG (canonSched G) W symPlaqG_q0 hU)) hU symPlaqG_q0
    (unitCubeExpBoundG_of_cubeMomentsAtG (canonSched G) W ht (hU _ symPlaqG_q0))
    0 hphys 0 one_pos hρ0 hρ1 hg hNT

/-- **The observer's functional is `schwSFMG`**, by definition. DERIVED: no numeral. -/
theorem obsXG'_SM (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      (obsXG' W ht hU hphys hNT hρ0 hρ1 hg).SM O g
        = schwSFMG (canonSched G) W (SymPlaqClassG G) O g :=
  fun _ _ _ _ => rfl

/-- **The observer carries its Hilbert space**: `v = gvecTG` (`ObserverLinkedG.obsGenG_flow`).

DERIVED: `0` the plane. -/
theorem obsXG'_obsGen (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ) :
    ObsGenG (canonSched G) W (SymPlaqClassG G) (obsXG' W ht hU hphys hNT hρ0 hρ1 hg) :=
  ⟨gvecTG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0
      (posPreserving_of_physRangeG (canonSched G)
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0),
    fun _ => rfl, obsGenG_flow (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0
      (posPreserving_of_physRangeG (canonSched G)
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) hphys 0)⟩

/-- **The observer's field is `symG (plaqFieldG q0)`**, by definition. DERIVED: no numeral. -/
theorem obsXG'_O (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ) :
    (obsXG' W ht hU hphys hNT hρ0 hρ1 hg).O = symG (plaqFieldG ObserverEnergyMoments.q0) :=
  rfl

/-- **The Hamiltonian gap of the observer**, from its self-adjoint generator
(`ObserverOSG.observerOSDataSG_isSelfAdjoint`, `ClayFull.hamiltonianGap_of_selfAdjoint`).

DERIVED: `0` the plane and the reference step. -/
theorem obsXG'_gap (W : ConfFlowG G) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ) :
    HamiltonianGap (obsXG' W ht hU hphys hNT hρ0 hρ1 hg).base :=
  hamiltonianGap_of_selfAdjoint _
    (observerOSDataSG_isSelfAdjoint (canonSched G) schedOS_canonSched schedShiftInv_canonSched W
      (symPlaqG_refl G) symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU) symPlaqG_q0
      (unitCubeExpBoundG_of_cubeMomentsAtG (canonSched G) W ht (hU _ symPlaqG_q0)) 0 hphys 0
      one_pos hρ0 hρ1 hg hNT)

end Observer

end MassGap.InputsG

end

#print axioms MassGap.InputsG.cube_of_classMomentsG
#print axioms MassGap.InputsG.one_le_of_classMomentsG
#print axioms MassGap.InputsG.unitCubeExpBoundG_of_cubeMomentsAtG
#print axioms MassGap.InputsG.stateG_smear_connected
#print axioms MassGap.InputsG.kernTG_oneT_eq
#print axioms MassGap.InputsG.kernTG_empty_oneT
#print axioms MassGap.InputsG.hnt_of_gramG
#print axioms MassGap.InputsG.obsXG'
#print axioms MassGap.InputsG.obsXG'_gap
