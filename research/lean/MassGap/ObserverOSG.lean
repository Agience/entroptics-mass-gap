import Mathlib
import MassGap.TimeGroupG
import MassGap.EnergyBoundG
import MassGap.ObserverOSLinked

/-!
# MassGap.ObserverOSG — the observer's Schwartz-indexed Euclidean data over a schedule of `G`

`ObserverOSReconstructionS.observerOSDataS` builds, for the `SU(N)` energy density, an `OSDataS`: the
Schwinger functions as continuous multilinear functionals on `𝓢(E4, ℝ)` with the linear-growth bound,
and the reconstructed Hilbert space with its time translations and gap. This module builds the same
object for every `GaugeGroup G` over a schedule `S : ClayTreeG.Sched G`, for the energy density
`FlowG.energy0G S W D hD` (map `ClayTreeG.energyMapG S W D`).

The schedule enters through two properties: `FlowG.SchedOS S` (the reconstruction and the uniform
bound) and `SchedShiftInv S`, the invariance of every state under the four unit shifts (the covering
of a cube by translates of the unit cube). `schedShiftInv_canonSched` proves the second at
`canonSched G` (`ShiftInvG.periodicStateG_shift`).

| `SU(N)` | here (any `G`, any `S`) | schedule input |
|---|---|---|
| `ObserverOSGrowth.boxSum`, `cubeSum_le_boxSum`, `boxSum_le_cubeSum`, `card_mul_boxSum_le` | `boxSumG`, `cubeSumG_le_boxSumG`, `boxSumG_le_cubeSumG`, `card_mul_boxSumG_le` | none |
| `ObserverOSGrowth.state_cubeSum_pow_le` | `state_cubeSumG_pow_le` (any translation-invariant state) | none |
| `ObserverOSGrowth.UnitCubeExpBound`, `cubeMoments_of_unitExp` | `UnitCubeExpBoundG`, `cubeMoments_of_unitExpG` | `SchedShiftInv` |
| `ObserverOSSchwartz.sum_cubeInd_le_cubeSum`, `abs_smear_energy0_le_shells`, `moment_smear_decay_le` | `sum_cubeInd_le_cubeSumG`, `abs_smear_energy_le_shellsG`, `moment_smear_decay_leG` | none |
| `CubeMomentsAt`, `abs_latSF_decay_le`, `tendsto_latSF_decay`, `abs_contSF_decay_le` | `CubeMomentsAtG`, `abs_latSFG_decay_le`, `tendsto_latSFG_decay`, `abs_contSFG_decay_le` | none |
| `smear_tail`, `abs_contSF_trunc_sub_le`, `schwSF`, `tendsto_schwSF`, `abs_schwSF_le` | `smear_tailG`, `abs_contSFG_trunc_sub_le`, `schwSFG`, `tendsto_schwSFG`, `abs_schwSFG_le` | `SchedShiftInv` (last three) |
| `ObserverOS.smear_testAdd`, `smear_testSmul`, `latSF_update` | `smear_testAddG`, `smear_testSmulG`, `latSFG_update` | none |
| `ObserverOSTempered.tendsto_latSF_test`, `contSF_update_add_test`, `contSF_update_smul_test` | `tendsto_latSFG_test`, `contSFG_update_add_test`, `contSFG_update_smul_test` | none |
| `schwSF_update_add`, `schwSF_update_smul`, `schwMulti`, `schwCML`, `abs_schwCML_le` | `schwSFG_update_add`, `schwSFG_update_smul`, `schwMultiG`, `schwCMLG`, `abs_schwCMLG_le` | `SchedShiftInv` |
| `ObserverOSReconstructionS.schwSF_comp_perm`, `observerOSDataS` | `schwSFG_comp_perm`, `observerOSDataSG` | `SchedOS`, `SchedShiftInv` |
| `ObserverOS.uniformBoundF_energy0` | `uniformBoundFG_energy0G` (`EnergyBoundG.uniformBoundFG_energy`) | `SchedOS.trans` |

Used as they are, with no group in their statements: `ObserverOSGrowth.mem_box_iff`, `box_mono`,
`mem_box_floor`, `site_le_of_mem_box_floor`, `box_ratio_le`, `growth_const_le`; the shells, weights,
`DecayBound`, `Decaying`, `trunc`, `decayBound_tail`, `abs_state_prod_sub_le` and
`le_of_forall_pos_continuous` of `ObserverOSSchwartz`; `decAdd`, `decSmul`, `trunc_decAdd`,
`trunc_decSmul`, `e4Norm`, `ofE4`, `decayBound_e4`, `continuous_of_bound_by` of
`ObserverOSTempered`; `ObserverOS.abs_state_prod_le`, `testAdd`, `testSmul`;
`ObserverEnergyCoarseN.state_pow_sum_le`; `ObserverEnergyBox.state_pow_le_exp`, `expC`, `cubeInd`;
the structure `ObserverOSReconstructionS.OSDataS`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and the cell-volume exponent; `0` the signs, the reference
step and the zero subtraction; `1` the unit cube, the unit weights and the weight's unit term; `2`
makes a power even and with `1` is the box side `2K + 1`; `5`, `6`, `32`, `8192` the orders, the
shell decay and the shell-weight sum of `ObserverOSSchwartz`.
-/

noncomputable section

namespace MassGap.ObserverOSG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz
  MassGap.ObserverOSTempered MassGap.ObserverEnergyBox MassGap.ObserverEnergyMoments
  MassGap.ObserverOSReconstructionS MassGap.ClayTreeG MassGap.ClayWiringG MassGap.FlowG
  MassGap.TimeGroupG MassGap.EnergyBoundG Filter
open scoped Topology

/-! ## 1. The shift invariance of a schedule -/

section Shift

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Every state of the schedule is invariant under the four unit shifts.**

DERIVED: `4` the dimension. -/
def SchedShiftInv (S : Sched G) : Prop :=
  ∀ (k : ℕ) (τ : Fin 4) (F : C(IConf G, ℝ)),
    S.ν k (MassGap.ReflectionShift.ishiftObsL τ F) = S.ν k F

/-- **The canonical schedule of `G` is shift invariant** (`ShiftInvG.periodicStateG_shift` at the
coupling `dyBetaG G k` of each step).

DERIVED: no numeral. -/
theorem schedShiftInv_canonSched [GaugeSimple G] : SchedShiftInv (canonSched G) :=
  fun k τ F => MassGap.ShiftInvG.periodicStateG_shift G (dyBetaG G k) τ F

end Shift

/-! ## 2. Lattice boxes and the covering inequality -/

section Boxes

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The energy of a lattice box** over `G`: `∑_{x ∈ [-K, K]⁴} F ∘ T_x`.

DERIVED: `4` the dimension. -/
def boxSumG (K : ℕ) (F : C(IConf G, ℝ)) : C(IConf G, ℝ) := ∑ x ∈ box K, transObs x F

/-- DERIVED: no numeral. -/
theorem boxSumG_apply (K : ℕ) (F : C(IConf G, ℝ)) (U : IConf G) :
    boxSumG K F U = ∑ x ∈ box K, F (transConf x U) := by
  unfold boxSumG
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, transObs_apply]

/-- DERIVED: `0` the sign. -/
theorem boxSumG_nonneg (K : ℕ) {F : C(IConf G, ℝ)} (hF : ∀ U, 0 ≤ F U) (U : IConf G) :
    0 ≤ boxSumG K F U := by
  rw [boxSumG_apply]
  exact Finset.sum_nonneg (fun x _ => hF _)

/-- **The cube energy is at most the energy of the box `[-⌊R/a⌋, ⌊R/a⌋]⁴`**, for `F ≥ 0`.

DERIVED: `0` the sign of `a`, `R`, `F`; `1` the indicator on the cube. -/
theorem cubeSumG_le_boxSumG {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (F : C(IConf G, ℝ))
    (hF : ∀ U, 0 ≤ F U) (U : IConf G) : cubeSumG a R F U ≤ boxSumG ⌊R / a⌋₊ F U := by
  classical
  rw [cubeSumG_apply, boxSumG_apply]
  have e : ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)
      = ∑ x ∈ (box ⌈R / a⌉₊).filter (fun x => ∀ i, |site a x i| ≤ R), F (transConf x U) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold cubeInd
    split_ifs <;> simp
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hF _)
  exact mem_box_floor ha hR (Finset.mem_filter.mp hx).2

/-- **The energy of the box `[-⌊R/a⌋, ⌊R/a⌋]⁴` is at most the cube energy**, for `F ≥ 0`.

DERIVED: `0` the sign of `a`, `R`, `F`; `1` the indicator on the cube. -/
theorem boxSumG_le_cubeSumG {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (F : C(IConf G, ℝ))
    (hF : ∀ U, 0 ≤ F U) (U : IConf G) : boxSumG ⌊R / a⌋₊ F U ≤ cubeSumG a R F U := by
  rw [cubeSumG_apply, boxSumG_apply]
  have e : ∑ x ∈ box ⌊R / a⌋₊, F (transConf x U)
      = ∑ x ∈ box ⌊R / a⌋₊, cubeInd R (site a x) * F (transConf x U) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have h1 : cubeInd R (site a x) = 1 := by
      unfold cubeInd
      rw [if_pos (fun i => site_le_of_mem_box_floor ha hR hx i)]
    rw [h1, one_mul]
  rw [e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (box_mono (Nat.floor_le_ceil _))
    (fun x _ _ => mul_nonneg (cubeInd_nonneg _ _) (hF _))

/-- **Covering a box by translates of a smaller box**, over `G`: for `F ≥ 0`,
`(2l + 1)⁴ · boxSumG L F ≤ ∑_{y ∈ [-(L+l), L+l]⁴} T_y (boxSumG l F)`.

DERIVED: `2`, `1`, `4` are `card_box`'s count `(2l + 1)⁴`; `0` the sign of `F`. -/
theorem card_mul_boxSumG_le (L l : ℕ) (F : C(IConf G, ℝ)) (hF : ∀ U, 0 ≤ F U) (U : IConf G) :
    ((2 * l + 1) ^ 4 : ℝ) * boxSumG L F U
      ≤ ∑ y ∈ box (L + l), boxSumG l F (transConf y U) := by
  classical
  have hshift : ∀ z ∈ box l,
      boxSumG L F U ≤ ∑ y ∈ box (L + l), F (transConf (y + z) U) := by
    intro z hz
    rw [boxSumG_apply]
    have hinj : Set.InjOn (fun x : ISite => x - z) (box L) := by
      intro x _ y _ h
      exact sub_left_injective h
    calc ∑ x ∈ box L, F (transConf x U)
        = ∑ y ∈ (box L).image (fun x : ISite => x - z), F (transConf (y + z) U) := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [sub_add_cancel]
      _ ≤ ∑ y ∈ box (L + l), F (transConf (y + z) U) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) (fun _ _ _ => hF _)
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          rw [mem_box_iff] at hx hz ⊢
          intro i
          have h1 := abs_sub (x i) (z i)
          have h2 := hx i
          have h3 := hz i
          simp only [Pi.sub_apply]
          push_cast
          linarith
  have hsum : ((2 * l + 1) ^ 4 : ℝ) * boxSumG L F U = ∑ _z ∈ box l, boxSumG L F U := by
    rw [Finset.sum_const, card_box, nsmul_eq_mul]
    norm_num
  rw [hsum]
  calc ∑ _z ∈ box l, boxSumG L F U
      ≤ ∑ z ∈ box l, ∑ y ∈ box (L + l), F (transConf (y + z) U) := Finset.sum_le_sum hshift
    _ = ∑ y ∈ box (L + l), ∑ z ∈ box l, F (transConf (y + z) U) := Finset.sum_comm
    _ = ∑ y ∈ box (L + l), boxSumG l F (transConf y U) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [boxSumG_apply]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        exact (congrArg (fun H : C(IConf G, ℝ) => H U) (transObs_transObs y z F)).symm

/-- Translation commutes with powers. DERIVED: `0` the empty power. -/
theorem transObs_powG (x : ISite) (F : C(IConf G, ℝ)) (q : ℕ) :
    transObs x (F ^ q) = transObs x F ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero]; exact transObs_one x
  | succ q ih => rw [pow_succ, pow_succ, transObs_mul, ih]

/-- **The moments of the energy in any cube from those of the unit cube**, in any state on
`IConf G` invariant under the lattice translations: for `F ≥ 0`, `R ≥ 0` and every `p`,
`ν(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} ν(E_1^{2p})`, `E_R = cubeSumG a R F`. The covering inequality,
Minkowski's inequality in `L^{2p}` and the covering ratio.

DERIVED: `0` the sign of `a`, `R`, `F` and the moment `p = 0`; `1` the unit cube and the unit
weights; `2` makes the power even and with `1` is the box side; `4` the dimension. -/
theorem state_cubeSumG_pow_le (ν : MassGap.DLRLimit.State (IConf G))
    (hT : ∀ (x : ISite) (F : C(IConf G, ℝ)), ν (transObs x F) = ν F) {a R : ℝ} (ha : 0 < a)
    (hR : 0 ≤ R) (F : C(IConf G, ℝ)) (hF : ∀ U, 0 ≤ F U) (p : ℕ) :
    ν (cubeSumG a R F ^ (2 * p)) ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * ν (cubeSumG a 1 F ^ (2 * p)) := by
  rcases p with _ | q
  · simp
  have hm : 2 * (q + 1) = 2 * q + 2 := by ring
  rw [hm]
  set L := ⌊R / a⌋₊ with hLdef
  set l := ⌊1 / a⌋₊ with hldef
  set X : C(IConf G, ℝ) := boxSumG l F with hXdef
  set c : ℝ := ((2 * l + 1) ^ 4 : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have hX0 : ∀ U, 0 ≤ X U := fun U => boxSumG_nonneg l hF U
  have hcov : ν ((c • cubeSumG a R F) ^ (2 * q + 2))
      ≤ ν ((∑ y ∈ box (L + l), transObs y X) ^ (2 * q + 2)) := by
    refine ν.mono (fun U => ?_)
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.coe_sum, Finset.sum_apply, transObs_apply]
    have h1 := cubeSumG_le_boxSumG ha hR F hF U
    have h2 := card_mul_boxSumG_le L l F hF U
    have h0 := cubeSumG_nonneg a R hF U
    refine pow_le_pow_left₀ (mul_nonneg hc.le h0) ?_ _
    calc c * cubeSumG a R F U ≤ c * boxSumG L F U := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ _ := h2
  rw [smul_pow, ν.map_smul] at hcov
  have hmink := MassGap.ObserverEnergyCoarseN.state_pow_sum_le ν (box (L + l))
    (fun y => transObs y X) (fun _ => (1 : ℝ)) (fun _ _ => one_pos) q
    (D := ν (X ^ (2 * q + 2)))
    (fun y _ => by rw [one_pow, mul_one, ← transObs_powG, hT])
  rw [Finset.sum_const, card_box, nsmul_eq_mul, mul_one] at hmink
  have hX1 : ν (X ^ (2 * q + 2)) ≤ ν (cubeSumG a 1 F ^ (2 * q + 2)) := by
    refine ν.mono (fun U => ?_)
    simp only [ContinuousMap.pow_apply]
    exact pow_le_pow_left₀ (hX0 U) (boxSumG_le_cubeSumG ha zero_le_one F hF U) _
  have hratio : (((2 * (L + l) + 1) ^ 4 : ℕ) : ℝ) ≤ (2 * R + 1) ^ 4 * c := by
    have h := box_ratio_le ha hR
    rw [← hLdef, ← hldef] at h
    have h0 : (0 : ℝ) ≤ 2 * ((L + l : ℕ) : ℝ) + 1 := by positivity
    calc (((2 * (L + l) + 1) ^ 4 : ℕ) : ℝ) = (2 * ((L + l : ℕ) : ℝ) + 1) ^ 4 := by push_cast; ring
      _ ≤ ((2 * R + 1) * (2 * (l : ℝ) + 1)) ^ 4 := pow_le_pow_left₀ h0 h 4
      _ = (2 * R + 1) ^ 4 * c := by rw [mul_pow, hcdef]
  have hB0 : 0 ≤ ν (cubeSumG a 1 F ^ (2 * q + 2)) :=
    ν.nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]; exact (even_two_mul (q + 1)).pow_nonneg _)
  have hcm : 0 < c ^ (2 * q + 2) := pow_pos hc _
  have hfin : c ^ (2 * q + 2) * ν (cubeSumG a R F ^ (2 * q + 2))
      ≤ c ^ (2 * q + 2) * (((2 * R + 1) ^ 4) ^ (2 * q + 2) * ν (cubeSumG a 1 F ^ (2 * q + 2))) := by
    calc c ^ (2 * q + 2) * ν (cubeSumG a R F ^ (2 * q + 2))
        ≤ ν (X ^ (2 * q + 2)) * (((2 * (L + l) + 1) ^ 4 : ℕ) : ℝ) ^ (2 * q + 2) :=
          hcov.trans hmink
      _ ≤ ν (cubeSumG a 1 F ^ (2 * q + 2)) * ((2 * R + 1) ^ 4 * c) ^ (2 * q + 2) :=
          mul_le_mul hX1 (pow_le_pow_left₀ (Nat.cast_nonneg _) hratio _)
            (pow_nonneg (Nat.cast_nonneg _) _) hB0
      _ = c ^ (2 * q + 2) * (((2 * R + 1) ^ 4) ^ (2 * q + 2)
            * ν (cubeSumG a 1 F ^ (2 * q + 2))) := by rw [mul_pow]; ring
  exact le_of_mul_le_mul_left hfin hcm

end Boxes

/-! ## 3. One exponential moment of the unit cube -/

section OneCube

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **One exponential moment of the unit-cube energy over a schedule**: some `t > 0` has
`ν_k(e^{t E_1})` bounded eventually, `E_1 = cubeSumG a_k 1 (O ∘ V_k)`; the body of
`ObserverOSGrowth.UnitCubeExpBound` with `stateK`, `dySpacing` replaced by `S.ν`, `S.a`.

DERIVED: `0` the lower end of `t`; `1` the unit cube. -/
def UnitCubeExpBoundG (S : Sched G) (W : ConfFlowG G) (O : LField G) : Prop :=
  ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop,
    S.ν k (expC (t • cubeSumG (S.a k) 1 (W.fieldMap k O).1)) ≤ C

/-- **Every cube moment from one exponential moment of the unit cube**, uniformly: on a
shift-invariant schedule there are `t > 0` and `C ≥ 0` with, eventually in the step, for every
`R ≥ 0` and `p`, `ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} (2p)! t^{-2p} C`.

DERIVED: `0` the lower end of `t`, `C`, `R` and the sign of the field; `1`, `2`, `4` as in
`state_cubeSumG_pow_le`. -/
theorem cubeMoments_of_unitExpG (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {O : LField G} (hO : ∀ U, 0 ≤ O.1 U) (h : UnitCubeExpBoundG S W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      S.ν k (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C) := by
  obtain ⟨t, C, ht, hC⟩ := h
  refine ⟨t, |C|, ht, abs_nonneg C, ?_⟩
  filter_upwards [hC] with k hk
  intro R hR p
  have ha := S.a_pos k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hO (W.V k U)
  refine (state_cubeSumG_pow_le (S.ν k) (state_transObs (hsh k)) ha hR _ hF p).trans
    (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (pow_nonneg (by linarith) 4) _))
  exact (state_pow_le_exp (S.ν k) _ (cubeSumG_nonneg _ _ hF) ht (2 * p)).trans
    (mul_le_mul_of_nonneg_left (hk.trans (le_abs_self C))
      (div_nonneg (by positivity) (pow_pos ht _).le))

end OneCube

/-! ## 4. The smeared energy density against a decaying test function -/

section Moments

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A sum of cube-indicator weights over any set of sites is at most the cube energy**, for `F ≥ 0`.

DERIVED: `0` the sign of `a`, `R`, `F`; `1` the indicator on the cube. -/
theorem sum_cubeInd_le_cubeSumG {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (F : C(IConf G, ℝ))
    (hF : ∀ U, 0 ≤ F U) (s : Finset ISite) (U : IConf G) :
    ∑ x ∈ s, cubeInd R (site a x) * F (transConf x U) ≤ cubeSumG a R F U := by
  classical
  have e : ∑ x ∈ s, cubeInd R (site a x) * F (transConf x U)
      = ∑ x ∈ s.filter (fun x => ∀ i, |site a x i| ≤ R), F (transConf x U) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold cubeInd
    split_ifs <;> simp
  rw [e]
  refine le_trans ?_ (boxSumG_le_cubeSumG ha hR F hF U)
  rw [boxSumG_apply]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hF _)
  exact mem_box_floor ha hR (Finset.mem_filter.mp hx).2

/-- **The canonical factor cancels in a smeared scaled field**:
`smear a (a⁻⁴ F) g = ∑_x g(a x) F ∘ T_x`.

DERIVED: `4` the cell-volume exponent and the canonical dimension; `0` the sign of `a`. -/
theorem smear_scaled_applyG {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (g : TestFn) {R M : ℝ}
    (hg : IsTest g.1 R M) (U : IConf G) :
    smear a ((a ^ 4)⁻¹ • F) g U = ∑ x ∈ box ⌈R / a⌉₊, g.1 (site a x) * F (transConf x U) := by
  rw [smear_eq_sum ha _ g hg (subset_refl _)]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha.ne'
  calc a ^ 4 * g.1 (site a x) * ((a ^ 4)⁻¹ * F (transConf x U))
      = (a ^ 4 * (a ^ 4)⁻¹) * (g.1 (site a x) * F (transConf x U)) := by ring
    _ = g.1 (site a x) * F (transConf x U) := by rw [mul_inv_cancel₀ h4, one_mul]

/-- **On the class `D` the energy density is `a_k⁻⁴ (O ∘ V_k)`.**

DERIVED: `4` the dimension. -/
theorem energyMapG_of_mem (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)} {O : LField G}
    (hO : O ∈ D) (k : ℕ) : (energyMapG S W D k O).1 = (S.a k ^ 4)⁻¹ • (W.fieldMap k O).1 := by
  have hz : zOnG S D k O = (S.a k ^ 4)⁻¹ := by
    unfold zOnG
    rw [if_pos hO]
  rw [energyMapG_val, hz]

/-- **The smeared energy density is dominated by the dyadic cube energies**: for `O ∈ D`
non-negative and a test function `g` supported in `[-R, R]⁴` with `‖g‖₅ ≤ A`, at every step,
`|smear a_k (a_k⁻⁴ O ∘ V_k) g| ≤ ∑_{j < ⌈R⌉ + 1} A 32^{-j} cubeSumG a_k 2^{j+1} (O ∘ V_k)`.

DERIVED: `5`, `32`, `2`, `1` are `abs_le_sum_shell`'s; `0` the vanishing value; `4` the
dimension. -/
theorem abs_smear_energy_le_shellsG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D) (k : ℕ)
    (f : TestFn) {R M A : ℝ} (hRM : IsTest f.1 R M) (hf : DecayBound 5 f.1 A) (U : IConf G) :
    |smear (S.a k) (energyMapG S W D k O).1 f U|
      ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1),
          A * (1 / 32) ^ j * cubeSumG (S.a k) ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1 U := by
  have ha := S.a_pos k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hA := hf.nonneg
  rw [energyMapG_of_mem S W hO k, smear_scaled_applyG ha (W.fieldMap k O).1 f hRM U]
  have hterm : ∀ x ∈ box ⌈R / S.a k⌉₊,
      |f.1 (site (S.a k) x) * (W.fieldMap k O).1 (transConf x U)|
        ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j
            * (cubeInd ((2 : ℝ) ^ (j + 1)) (site (S.a k) x)
              * (W.fieldMap k O).1 (transConf x U)) := by
    intro x _
    rw [abs_mul, abs_of_nonneg (hF _)]
    have hsh : |f.1 (site (S.a k) x)| ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1),
        A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) (site (S.a k) x) := by
      by_cases h0 : f.1 (site (S.a k) x) = 0
      · rw [h0, abs_zero]
        exact Finset.sum_nonneg
          (fun j _ => mul_nonneg (mul_nonneg hA (by positivity)) (cubeInd_nonneg _ _))
      · refine abs_le_sum_shell (hf _) ?_
        refine (pi_norm_le_iff_of_nonneg hRM.1).mpr (fun i => ?_)
        rw [Real.norm_eq_abs]
        exact hRM.2.2 _ h0 i
    calc |f.1 (site (S.a k) x)| * (W.fieldMap k O).1 (transConf x U)
        ≤ (∑ j ∈ Finset.range (⌈R⌉₊ + 1),
            A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) (site (S.a k) x))
            * (W.fieldMap k O).1 (transConf x U) := mul_le_mul_of_nonneg_right hsh (hF _)
      _ = _ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
  calc |∑ x ∈ box ⌈R / S.a k⌉₊, f.1 (site (S.a k) x) * (W.fieldMap k O).1 (transConf x U)|
      ≤ ∑ x ∈ box ⌈R / S.a k⌉₊,
          |f.1 (site (S.a k) x) * (W.fieldMap k O).1 (transConf x U)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ box ⌈R / S.a k⌉₊, ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j
            * (cubeInd ((2 : ℝ) ^ (j + 1)) (site (S.a k) x)
              * (W.fieldMap k O).1 (transConf x U)) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j
            * ∑ x ∈ box ⌈R / S.a k⌉₊, cubeInd ((2 : ℝ) ^ (j + 1)) (site (S.a k) x)
              * (W.fieldMap k O).1 (transConf x U) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (sum_cubeInd_le_cubeSumG ha (by positivity) _ hF _ U) (mul_nonneg hA (by positivity)))

/-- **The moments of the smeared energy density against a decaying test function**: if at step `k`
every cube has `ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} c`, `c ≥ 0`, `p ≥ 1`, then for every test function
with `‖g‖₅ ≤ A`, `ν_k((smear g)^{2p}) ≤ c (8192 A)^{2p}`.

DERIVED: `0` the sign of `c` and the excluded moment `p = 0`; `8192` is `sum_shellWeight_le`'s; `2`
makes the power even and with `1`, `4` is the volume factor; `5`, `32` are `abs_le_sum_shell`'s. -/
theorem moment_smear_decay_leG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D) (k : ℕ)
    (f : TestFn) {A c : ℝ} (hf : DecayBound 5 f.1 A) (hc0 : 0 ≤ c) (p : ℕ) (hp : p ≠ 0)
    (hc : ∀ R : ℝ, 0 ≤ R → S.ν k (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p))
      ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * c) :
    S.ν k (smear (S.a k) (energyMapG S W D k O).1 f ^ (2 * p)) ≤ c * (8192 * A) ^ (2 * p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hm : 2 * (q + 1) = 2 * q + 2 := by ring
  rw [hm] at hc ⊢
  obtain ⟨R, M, hRM⟩ := f.2
  have hA := hf.nonneg
  have hmono : S.ν k (smear (S.a k) (energyMapG S W D k O).1 f ^ (2 * q + 2))
      ≤ S.ν k ((∑ j ∈ Finset.range (⌈R⌉₊ + 1), (A * (1 / 32) ^ j)
          • cubeSumG (S.a k) ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1) ^ (2 * q + 2)) := by
    refine (S.ν k).mono (fun U => ?_)
    have hb := abs_smear_energy_le_shellsG S W hpos hO k f hRM hf U
    have hev : Even (2 * q + 2) := ⟨q + 1, by ring⟩
    simp only [ContinuousMap.pow_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [← hev.pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb _
  have hD' : ∀ j ∈ Finset.range (⌈R⌉₊ + 1),
      S.ν k (((A * (1 / 32) ^ j) • cubeSumG (S.a k) ((2 : ℝ) ^ (j + 1))
        (W.fieldMap k O).1) ^ (2 * q + 2)) ≤ (A ^ (2 * q + 2) * c) * shellWeight j ^ (2 * q + 2) := by
    intro j _
    rw [smul_pow, (S.ν k).map_smul]
    calc (A * (1 / 32) ^ j) ^ (2 * q + 2) * S.ν k (cubeSumG (S.a k)
          ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1 ^ (2 * q + 2))
        ≤ (A * (1 / 32) ^ j) ^ (2 * q + 2)
            * (((2 * (2 : ℝ) ^ (j + 1) + 1) ^ 4) ^ (2 * q + 2) * c) :=
          mul_le_mul_of_nonneg_left (hc _ (by positivity))
            (pow_nonneg (mul_nonneg hA (by positivity)) _)
      _ = (A ^ (2 * q + 2) * c) * shellWeight j ^ (2 * q + 2) := by
          unfold shellWeight
          rw [mul_pow, mul_pow]
          ring
  have hmink := MassGap.ObserverEnergyCoarseN.state_pow_sum_le (S.ν k)
    (Finset.range (⌈R⌉₊ + 1))
    (fun j => (A * (1 / 32) ^ j) • cubeSumG (S.a k) ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1)
    shellWeight (fun j _ => shellWeight_pos j) q hD'
  have hW0 : 0 ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1), shellWeight j :=
    Finset.sum_nonneg (fun j _ => (shellWeight_pos j).le)
  calc S.ν k (smear (S.a k) (energyMapG S W D k O).1 f ^ (2 * q + 2))
      ≤ _ := hmono
    _ ≤ (A ^ (2 * q + 2) * c) * (∑ j ∈ Finset.range (⌈R⌉₊ + 1), shellWeight j) ^ (2 * q + 2) :=
        hmink
    _ ≤ (A ^ (2 * q + 2) * c) * 8192 ^ (2 * q + 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 (sum_shellWeight_le _) _)
          (mul_nonneg (pow_nonneg hA _) hc0)
    _ = c * (8192 * A) ^ (2 * q + 2) := by rw [mul_pow]; ring

end Moments

/-! ## 5. The growth condition in the weighted sup norm -/

section Growth

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cube moments at one step, uniform in the cube and the order**, over a schedule.

DERIVED: `0` the lower end of `R`; `2`, `1`, `4` the volume factor and the even power. -/
def CubeMomentsAtG (S : Sched G) (W : ConfFlowG G) (O : LField G) (t C : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
    S.ν k (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p))
      ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C)

/-- **One step of the weighted growth bound**: `|latSFG| ≤ (1 + n c) ∏ᵢ 8192 (Aᵢ + ε)`,
`c = (2n)! t^{-2n} C`.

DERIVED: `0` the sign of `t`, `C`, `ε`; `8192` is `sum_shellWeight_le`'s; `1`, `2` are
`abs_state_prod_le`'s; `5 = 4 + 1` the decay order, the least integer above the dimension
(`ObserverOSSchwartz`). -/
theorem abs_latSFG_decay_le (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) {k : ℕ}
    (hk : ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      S.ν k (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C))
    (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i))
    {ε : ℝ} (hε : 0 < ε) :
    |latSFG S (energyMapG S W D) k (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * (A i + ε) := by
  have hc0 : 0 ≤ ((2 * n).factorial : ℝ) / t ^ (2 * n) * C :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0
  have hb := abs_state_prod_le (S.ν k)
    (fun i => smear (S.a k) (energyMapG S W D k O).1 (f i))
    (fun i => 8192 * (A i + ε))
    (fun i => mul_pos (by norm_num) (by linarith [(hA i).nonneg]))
    (c := ((2 * n).factorial : ℝ) / t ^ (2 * n) * C)
    (fun i => by
      rw [Fintype.card_fin]
      have hn : n ≠ 0 := by have := i.isLt; omega
      exact (moment_smear_decay_leG S W hpos hO k (f i) (hA i) hc0 n hn
        (fun R hR => hk R hR n)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (by norm_num) (hA i).nonneg) (by linarith) _) hc0))
  rw [Fintype.card_fin] at hb
  exact hb

/-- **The lattice functions of a decaying family converge along the ultrafilter to `contSFG`**.

DERIVED: `1` the choice `ε = 1` in the eventual bound; `5 = 4 + 1` the decay order, as in
`abs_latSFG_decay_le`. -/
theorem tendsto_latSFG_decay (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAtG S W O t C)
    (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) :
    Tendsto (fun k => latSFG S (energyMapG S W D) k (fun i => (O, f i))) (ultra : Filter ℕ)
      (𝓝 (contSFG S (energyMapG S W D) (fun i => (O, f i)))) := by
  have hstep : ∀ᶠ k in atTop, |latSFG S (energyMapG S W D) k (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * (A i + 1) :=
    hev.mono (fun k hk => abs_latSFG_decay_le S W hpos hO ht hC0 hk n f A hA one_pos)
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hstep
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **The weighted growth bound under the cube moments**: `|S_n| ≤ (1 + n c) ∏ᵢ 8192 Aᵢ`.

DERIVED: `0` the sign of `t`, `C`, `Aᵢ` and the limit point; `8192` is `sum_shellWeight_le`'s; `1`,
`2` are `abs_state_prod_le`'s; `5 = 4 + 1` the decay order, as in `abs_latSFG_decay_le`. -/
theorem abs_contSFG_decay_le (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAtG S W O t C)
    (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) :
    |contSFG S (energyMapG S W D) (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * A i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hT := tendsto_latSFG_decay S W hpos hO ht hC0 hev n f A hA
  have hcont : Continuous (fun ε : ℝ => (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
      * ∏ i, 8192 * (A i + ε)) :=
    continuous_const.mul (continuous_finsetProd _
      (fun i _ => continuous_const.mul (continuous_const.add continuous_id)))
  have h := le_of_forall_pos_continuous hcont (fun ε hε => by
    have hstep : ∀ᶠ k in atTop, |latSFG S (energyMapG S W D) k (fun i => (O, f i))|
        ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * (A i + ε) :=
      hev.mono (fun k hk => abs_latSFG_decay_le S W hpos hO ht hC0 hk n f A hA hε)
    exact le_of_tendsto hT.abs (hstep.filter_mono ultra_le))
  simpa only [add_zero] using h

end Growth

/-! ## 6. Linearity of smearing over `G` -/

section Linear

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Smearing is additive in the test function**, over `G`.

DERIVED: `0` the sign of `a`; `4` the cell-volume exponent. -/
theorem smear_testAddG {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (f g : TestFn) :
    smear a F (testAdd f g) = smear a F f + smear a F g := by
  obtain ⟨R, M, hf⟩ := f.2
  obtain ⟨R', M', hg⟩ := g.2
  obtain ⟨R'', M'', hfg⟩ := (testAdd f g).2
  rw [smear_eq_sum ha F (testAdd f g) hfg
      (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊ ∪ box ⌈R'' / a⌉₊) Finset.subset_union_right,
    smear_eq_sum ha F f hf (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊ ∪ box ⌈R'' / a⌉₊)
      (Finset.subset_union_left.trans Finset.subset_union_left),
    smear_eq_sum ha F g hg (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊ ∪ box ⌈R'' / a⌉₊)
      (Finset.subset_union_right.trans Finset.subset_union_left),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← add_smul]
  congr 1
  show a ^ 4 * (f.1 (site a x) + g.1 (site a x)) = a ^ 4 * f.1 (site a x) + a ^ 4 * g.1 (site a x)
  ring

/-- **Smearing is homogeneous in the test function**, over `G`.

DERIVED: `0` the sign of `a`; `4` the cell-volume exponent. -/
theorem smear_testSmulG {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (c : ℝ) (f : TestFn) :
    smear a F (testSmul c f) = c • smear a F f := by
  obtain ⟨R, M, hf⟩ := f.2
  obtain ⟨R', M', hcf⟩ := (testSmul c f).2
  rw [smear_eq_sum ha F (testSmul c f) hcf (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊)
      Finset.subset_union_right,
    smear_eq_sum ha F f hf (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊) Finset.subset_union_left,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_smul]
  congr 1
  show a ^ 4 * (c * f.1 (site a x)) = c * (a ^ 4 * f.1 (site a x))
  ring

/-- **Smearing the tail** is the difference of the smeared truncations.

DERIVED: `0` the sign of `a`; `-1` the coefficient of the subtracted test function. -/
theorem smear_tailG {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (f g : TestFn) :
    smear a F (testAdd f (testSmul (-1) g)) = smear a F f - smear a F g := by
  rw [smear_testAddG ha, smear_testSmulG ha, neg_one_smul, ← sub_eq_add_neg]

/-- **The lattice function of a family with one slot replaced** is the state of the replaced factor
times the product of the others.

DERIVED: no numeral. -/
theorem latSFG_update (S : Sched G) (Φ : ℕ → LField G → LField G) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (B : ι → SFieldG G) (j : ι) (x : SFieldG G) :
    latSFG S Φ k (Function.update B j x)
      = S.ν k (smear (S.a k) (Φ k x.1).1 x.2
          * ∏ i ∈ Finset.univ.erase j, smear (S.a k) (Φ k (B i).1).1 (B i).2) := by
  show S.ν k (∏ i, smear (S.a k) (Φ k (Function.update B j x i).1).1
    (Function.update B j x i).2) = _
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end Linear

/-! ## 7. The extension to decaying test functions -/

section Extension

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Two truncations are close**: under the cube moments, for `R ≤ R'` and `‖gᵢ‖₆ ≤ Bᵢ`,
`|S_n(trunc_{R'} g) − S_n(trunc_R g)| ≤ (1 + n c) ∑ₐ 8192 (Bₐ / (1 + R)) ∏_{i ≠ a} 8192 Bᵢ`.

DERIVED: `0` the sign of `t`, `C`, `ε` and the limit point; `8192`, `5`, `6` as in
`moment_smear_decay_leG` and `decayBound_tail`; `1`, `2` are `abs_state_prod_le`'s. -/
theorem abs_contSFG_trunc_sub_le (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAtG S W O t C)
    (n : ℕ) (g : Fin n → Decaying) (B : Fin n → ℝ) (hB : ∀ i, DecayBound 6 (g i).1 (B i))
    {R R' : ℕ} (hRR : R ≤ R') :
    |contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R'))
        - contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
        * ∑ a, 8192 * (B a / (1 + R)) * ∏ i ∈ Finset.univ \ {a}, 8192 * B i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  set c : ℝ := ((2 * n).factorial : ℝ) / t ^ (2 * n) * C with hcdef
  have hc0 : 0 ≤ c := mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0
  have hB0 : ∀ i, 0 ≤ B i := fun i => (hB i).nonneg
  have hR0 : (0 : ℝ) < 1 + R := by positivity
  have hB5 : ∀ (R₁ : ℕ) i, DecayBound 5 (trunc (g i) R₁).1 (B i) :=
    fun R₁ i => decayBound_trunc ((hB i).mono (by norm_num)) R₁
  have hT' := tendsto_latSFG_decay S W hpos hO ht hC0 hev n (fun i => trunc (g i) R') B
    (hB5 R')
  have hT := tendsto_latSFG_decay S W hpos hO ht hC0 hev n (fun i => trunc (g i) R) B (hB5 R)
  have hcont : Continuous (fun ε : ℝ => (1 + n * c)
      * ∑ a, 8192 * (B a / (1 + R) + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε)) :=
    continuous_const.mul (continuous_finsetSum _ (fun a _ =>
      (continuous_const.mul (continuous_const.add continuous_id)).mul
        (continuous_finsetProd _
          (fun i _ => continuous_const.mul (continuous_const.add continuous_id)))))
  have h := le_of_forall_pos_continuous hcont (fun ε hε => by
    have hstep : ∀ᶠ k in atTop,
        |latSFG S (energyMapG S W D) k (fun i => (O, trunc (g i) R'))
          - latSFG S (energyMapG S W D) k (fun i => (O, trunc (g i) R))|
        ≤ (1 + n * c)
          * ∑ a, 8192 * (B a / (1 + R) + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε) := by
      filter_upwards [hev] with k hk
      have ha := S.a_pos k
      have hmom : ∀ (f : TestFn) (A : ℝ), DecayBound 5 f.1 A → n ≠ 0 →
          S.ν k (smear (S.a k) (energyMapG S W D k O).1 f ^ (2 * n))
            ≤ c * (8192 * (A + ε)) ^ (2 * n) := fun f A hA hn =>
        (moment_smear_decay_leG S W hpos hO k f hA hc0 n hn (fun R₁ hR₁ => hk R₁ hR₁ n)).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg (by norm_num) hA.nonneg) (by linarith) _) hc0)
      have hb := abs_state_prod_sub_le (S.ν k)
        (fun i => smear (S.a k) (energyMapG S W D k O).1 (trunc (g i) R))
        (fun i => smear (S.a k) (energyMapG S W D k O).1 (trunc (g i) R'))
        (fun i => 8192 * (B i + ε)) (fun i => 8192 * (B i / (1 + R) + ε))
        (fun i => mul_pos (by norm_num) (by linarith [hB0 i]))
        (fun i => mul_pos (by norm_num) (by linarith [div_nonneg (hB0 i) hR0.le])) (c := c)
        (fun i => by
          rw [Fintype.card_fin]
          exact hmom _ _ (hB5 R i) (by have := i.isLt; omega))
        (fun i => by
          rw [Fintype.card_fin]
          exact hmom _ _ (hB5 R' i) (by have := i.isLt; omega))
        (fun i => by
          rw [Fintype.card_fin]
          show S.ν k ((smear (S.a k) (energyMapG S W D k O).1 (trunc (g i) R')
              - smear (S.a k) (energyMapG S W D k O).1 (trunc (g i) R)) ^ (2 * n)) ≤ _
          rw [← smear_tailG ha]
          exact hmom _ _ (decayBound_tail (hB i) hRR) (by have := i.isLt; omega))
      rw [Fintype.card_fin] at hb
      exact hb
    exact le_of_tendsto (hT'.sub hT).abs (hstep.filter_mono ultra_le))
  simpa only [add_zero] using h

/-- **The Schwinger functions of decaying test functions over a schedule**: the limit, as `R → ∞`,
of the Schwinger functions of the truncations `trunc_R gᵢ`.

DERIVED: `4` the dimension. -/
def schwSFG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (O : LField G) {n : ℕ}
    (g : Fin n → Decaying) : ℝ :=
  limUnder atTop (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R)))

/-- **The truncated Schwinger functions converge**, given `UnitCubeExpBoundG` on a shift-invariant
schedule: `S_n(trunc_R g) → schwSFG g`.

DERIVED: `0` the sign of `ε` and `K`; `1` the shift `1 + R`. -/
theorem tendsto_schwSFG (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) {n : ℕ} (g : Fin n → Decaying) :
    Tendsto (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R))) atTop
      (𝓝 (schwSFG S W D O g)) := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExpG S hsh W (hpos O hO) h
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
      * ∑ a, 8192 * B a * ∏ i ∈ Finset.univ \ {a}, 8192 * B i := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0)))
      (Finset.sum_nonneg (fun a _ => mul_nonneg (mul_nonneg (by norm_num) (hB a).nonneg)
        (Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hB i).nonneg))))
  have hdist : ∀ R R' : ℕ, R ≤ R' →
      dist (contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R')))
        (contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R))) ≤ K / (1 + R) := by
    intro R R' hRR
    rw [Real.dist_eq]
    refine (abs_contSFG_trunc_sub_le S W hpos hO ht hC0 hev n g B hB hRR).trans
      (le_of_eq ?_)
    rw [hKdef, mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hcs : CauchySeq
      (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O, trunc (g i) R))) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (K / ε)
    refine ⟨M, fun m hm => (hdist M m hm).trans_lt ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **The growth bound for the extended Schwinger functions**: given `UnitCubeExpBoundG` on a
shift-invariant schedule, there are `t > 0`, `C ≥ 0` with
`|schwSFG g| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 Aᵢ` whenever `‖gᵢ‖₅ ≤ Aᵢ`.

DERIVED: `0` the sign of `t`, `C`; `5`, `8192` as in `abs_contSFG_decay_le`; `2`, `1` the
factorial constant. -/
theorem abs_schwSFG_le (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (g : Fin n → Decaying) (A : Fin n → ℝ),
      (∀ i, DecayBound 5 (g i).1 (A i)) →
        |schwSFG S W D O g|
          ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * A i := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExpG S hsh W (hpos O hO) h
  refine ⟨t, C, ht, hC0, fun n g A hA => ?_⟩
  exact le_of_tendsto (tendsto_schwSFG S hsh W hpos hO h g).abs (Eventually.of_forall
    (fun R => abs_contSFG_decay_le S W hpos hO ht hC0 hev n (fun i => trunc (g i) R) A
      (fun i => decayBound_trunc (hA i) R)))

/-- **`schwSFG` is symmetric under permutations** (`FlowG.contSFG_comp_equiv` at each truncation).

DERIVED: no numeral. -/
theorem schwSFG_comp_perm (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (O : LField G)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : Fin n → Decaying) :
    schwSFG S W D O (g ∘ σ) = schwSFG S W D O g := by
  unfold schwSFG
  congr 1
  funext R
  exact contSFG_comp_equiv S (energyMapG S W D) σ (fun i => (O, trunc (g i) R))

end Extension

/-! ## 8. Multilinearity -/

section Multi

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Every family of test functions of one field converges along the ultrafilter**, under the cube
moments of that field.

DERIVED: `5` the order of the weighted norm. -/
theorem tendsto_latSFG_test (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAtG S W O t C)
    (n : ℕ) (f : Fin n → TestFn) :
    Tendsto (fun k => latSFG S (energyMapG S W D) k (fun i => (O, f i))) (ultra : Filter ℕ)
      (𝓝 (contSFG S (energyMapG S W D) (fun i => (O, f i)))) := by
  have hex : ∀ i, ∃ R M : ℝ, IsTest (f i).1 R M := fun i => (f i).2
  choose R M hRM using hex
  exact tendsto_latSFG_decay S W hpos hO ht hC0 hev n f _
    (fun i => decayBound_of_isTest (hRM i))

/-- Replacing one test function of a one-field family is replacing one entry of the family.

DERIVED: no numeral. -/
theorem family_updateG {n : ℕ} [DecidableEq (Fin n)] (O : LField G)
    (f : Fin n → TestFn) (j : Fin n) (x : TestFn) :
    (fun i => ((O, Function.update f j x i) : SFieldG G))
      = Function.update (fun i => ((O, f i) : SFieldG G)) j (O, x) := by
  funext i
  exact Function.apply_update (fun _ (g : TestFn) => ((O, g) : SFieldG G)) f j x i

/-- **The limit is additive in each test function**, for one field with the cube moments.

DERIVED: no numeral. -/
theorem contSFG_update_add_test (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAtG S W O t C)
    {n : ℕ} [DecidableEq (Fin n)] (f : Fin n → TestFn) (j : Fin n) (a b : TestFn) :
    contSFG S (energyMapG S W D) (fun i => (O, Function.update f j (testAdd a b) i))
      = contSFG S (energyMapG S W D) (fun i => (O, Function.update f j a i))
        + contSFG S (energyMapG S W D) (fun i => (O, Function.update f j b i)) := by
  have h1 := tendsto_latSFG_test S W hpos hO ht hC0 hev n (Function.update f j (testAdd a b))
  have h2 := tendsto_latSFG_test S W hpos hO ht hC0 hev n (Function.update f j a)
  have h3 := tendsto_latSFG_test S W hpos hO ht hC0 hev n (Function.update f j b)
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine tendsto_nhds_unique h1 ((h2.add h3).congr (fun k => ?_))
  rw [family_updateG, family_updateG, family_updateG, latSFG_update, latSFG_update, latSFG_update]
  show _ = S.ν k (smear (S.a k) (energyMapG S W D k O).1 (testAdd a b) * _)
  rw [smear_testAddG (S.a_pos k), add_mul, (S.ν k).map_add]

/-- **The limit is homogeneous in each test function**, for one field with the cube moments.

DERIVED: no numeral. -/
theorem contSFG_update_smul_test (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAtG S W O t C)
    {n : ℕ} [DecidableEq (Fin n)] (f : Fin n → TestFn) (j : Fin n) (c : ℝ) (a : TestFn) :
    contSFG S (energyMapG S W D) (fun i => (O, Function.update f j (testSmul c a) i))
      = c * contSFG S (energyMapG S W D) (fun i => (O, Function.update f j a i)) := by
  have h1 := tendsto_latSFG_test S W hpos hO ht hC0 hev n (Function.update f j (testSmul c a))
  have h2 := tendsto_latSFG_test S W hpos hO ht hC0 hev n (Function.update f j a)
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine tendsto_nhds_unique h1 ((h2.const_mul c).congr (fun k => ?_))
  rw [family_updateG, family_updateG, latSFG_update, latSFG_update]
  show _ = S.ν k (smear (S.a k) (energyMapG S W D k O).1 (testSmul c a) * _)
  rw [smear_testSmulG (S.a_pos k), smul_mul_assoc, (S.ν k).map_smul]

/-- Truncating a family with one entry replaced.

DERIVED: no numeral. -/
theorem trunc_family_updateG {n : ℕ} [DecidableEq (Fin n)] (O : LField G)
    (g : Fin n → Decaying) (j : Fin n) (z : Decaying) (R : ℕ) :
    (fun i => ((O, trunc (Function.update g j z i) R) : SFieldG G))
      = (fun i => ((O, Function.update (fun i => trunc (g i) R) j (trunc z R) i) : SFieldG G)) := by
  funext i
  congr 1
  exact Function.apply_update (fun _ (w : Decaying) => trunc w R) g j z i

/-- **`schwSFG` is additive in each decaying function**, given `UnitCubeExpBoundG` on a
shift-invariant schedule.

DERIVED: no numeral. -/
theorem schwSFG_update_add (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) {n : ℕ} [DecidableEq (Fin n)] (g : Fin n → Decaying)
    (j : Fin n) (x y : Decaying) :
    schwSFG S W D O (Function.update g j (decAdd x y))
      = schwSFG S W D O (Function.update g j x) + schwSFG S W D O (Function.update g j y) := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExpG S hsh W (hpos O hO) h
  have h1 := tendsto_schwSFG S hsh W hpos hO h (Function.update g j (decAdd x y))
  have h2 := tendsto_schwSFG S hsh W hpos hO h (Function.update g j x)
  have h3 := tendsto_schwSFG S hsh W hpos hO h (Function.update g j y)
  refine tendsto_nhds_unique h1 ((h2.add h3).congr (fun R => ?_))
  show contSFG S (energyMapG S W D) (fun i => (O, trunc (Function.update g j x i) R))
      + contSFG S (energyMapG S W D) (fun i => (O, trunc (Function.update g j y i) R))
    = contSFG S (energyMapG S W D) (fun i => (O, trunc (Function.update g j (decAdd x y) i) R))
  rw [trunc_family_updateG, trunc_family_updateG, trunc_family_updateG, trunc_decAdd]
  exact (contSFG_update_add_test S W hpos hO ht hC0 hev (fun i => trunc (g i) R) j
    (trunc x R) (trunc y R)).symm

/-- **`schwSFG` is homogeneous in each decaying function**, given `UnitCubeExpBoundG` on a
shift-invariant schedule.

DERIVED: no numeral. -/
theorem schwSFG_update_smul (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) {n : ℕ} [DecidableEq (Fin n)] (g : Fin n → Decaying)
    (j : Fin n) (c : ℝ) (x : Decaying) :
    schwSFG S W D O (Function.update g j (decSmul c x))
      = c * schwSFG S W D O (Function.update g j x) := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExpG S hsh W (hpos O hO) h
  have h1 := tendsto_schwSFG S hsh W hpos hO h (Function.update g j (decSmul c x))
  have h2 := tendsto_schwSFG S hsh W hpos hO h (Function.update g j x)
  refine tendsto_nhds_unique h1 ((h2.const_mul c).congr (fun R => ?_))
  show c * contSFG S (energyMapG S W D) (fun i => (O, trunc (Function.update g j x i) R))
    = contSFG S (energyMapG S W D) (fun i => (O, trunc (Function.update g j (decSmul c x) i) R))
  rw [trunc_family_updateG, trunc_family_updateG, trunc_decSmul]
  exact (contSFG_update_smul_test S W hpos hO ht hC0 hev (fun i => trunc (g i) R) j c
    (trunc x R)).symm

end Multi

/-! ## 9. The Schwinger functions on `𝓢(E4, ℝ)` -/

section Schwinger

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The Schwinger functions of the energy density over `G` on Euclidean Schwartz functions, as a
multilinear map**: `φ ↦ schwSFG (ofE4 ∘ φ)`.

DERIVED: `4` the dimension. -/
def schwMultiG (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O)
    (n : ℕ) : MultilinearMap ℝ (fun _ : Fin n => MassGap.WightmanData.TestFn) ℝ where
  toFun φ := schwSFG S W D O (fun i => ofE4 (φ i))
  map_update_add' φ j a b := by
    show schwSFG S W D O (fun i => ofE4 (Function.update φ j (a + b) i))
      = schwSFG S W D O (fun i => ofE4 (Function.update φ j a i))
        + schwSFG S W D O (fun i => ofE4 (Function.update φ j b i))
    rw [ofE4_update, ofE4_update, ofE4_update, ofE4_add]
    exact schwSFG_update_add S hsh W hpos hO h _ j _ _
  map_update_smul' φ j c a := by
    show schwSFG S W D O (fun i => ofE4 (Function.update φ j (c • a) i))
      = c • schwSFG S W D O (fun i => ofE4 (Function.update φ j a i))
    rw [ofE4_update, ofE4_update, ofE4_smul, smul_eq_mul]
    exact schwSFG_update_smul S hsh W hpos hO h _ j c _

/-- **The growth bound on Euclidean Schwartz functions**: there are `t > 0`, `C ≥ 0` with
`|S_n(φ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 e4Norm 5 (φᵢ)`.

DERIVED: `5`, `8192` are `abs_schwSFG_le`'s; `0` the sign of `t`, `C`; `2`, `1` the factorial
constant. -/
theorem abs_schwMultiG_le (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
      |schwMultiG S hsh W hpos hO h n φ|
        ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * e4Norm 5 (φ i) := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwSFG_le S hsh W hpos hO h
  exact ⟨t, C, ht, hC0, fun n φ => hb n _ _ (fun i => decayBound_e4 5 (φ i))⟩

/-- **OS0 in the Schwartz topology over `G`**: `schwMultiG` as a continuous multilinear functional on
`𝓢(E4, ℝ)ⁿ`, continuity from `continuous_of_bound_by` at the gauge `8192 · e4Norm 5`.

DERIVED: `8192`, `5` are `abs_schwMultiG_le`'s; `0` the gauge at the origin and the signs. -/
def schwCMLG (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O)
    (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => MassGap.WightmanData.TestFn) ℝ where
  toMultilinearMap := schwMultiG S hsh W hpos hO h n
  cont := by
    obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwMultiG_le S hsh W hpos hO h
    refine continuous_of_bound_by (schwMultiG S hsh W hpos hO h n) (fun φ => 8192 * e4Norm 5 φ)
      (continuous_const.mul (continuous_e4Norm 5))
      (fun φ => mul_nonneg (by norm_num) (e4Norm_nonneg 5 φ))
      (by rw [e4Norm_zero, mul_zero])
      (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
      (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0)))
      (fun φ => hb n φ)

/-- DERIVED: no numeral. -/
theorem schwCMLG_apply (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn) :
    schwCMLG S hsh W hpos hO h n φ = schwSFG S W D O (fun i => ofE4 (φ i)) := rfl

/-- **OS0 in the linear-growth form on `𝓢(E4, ℝ)` over `G`**: one `α = 1 + C`,
`γ = 8 (1 + t⁻¹)²` with `|S_n(φ)| ≤ α γⁿ (n!)² ∏ᵢ 8192 e4Norm 5 (φᵢ)`.

DERIVED: `8`, `2`, `1` are `growth_const_le`'s; `5`, `8192` as in `abs_schwMultiG_le`; `0` the
sign. -/
theorem abs_schwCMLG_le (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField G} (hO : O ∈ D)
    (h : UnitCubeExpBoundG S W O) :
    ∃ α γ : ℝ, ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
      |schwCMLG S hsh W hpos hO h n φ|
        ≤ α * γ ^ n * (n.factorial : ℝ) ^ 2 * ∏ i, 8192 * e4Norm 5 (φ i) := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwMultiG_le S hsh W hpos hO h
  refine ⟨1 + C, 8 * (1 + t⁻¹) ^ 2, fun n φ => ?_⟩
  have hP0 : 0 ≤ ∏ i, 8192 * e4Norm 5 (φ i) :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (e4Norm_nonneg 5 (φ i)))
  exact (hb n φ).trans (mul_le_mul_of_nonneg_right (growth_const_le ht hC0 n) hP0)

end Schwinger

/-! ## 10. The observer's Schwartz-indexed data over `G` -/

section Observer

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The uniform bound of the energy density as a bound of the flow `energy0G`**
(`EnergyBoundG.uniformBoundFG_energy` at `SchedOS.trans`).

DERIVED: no numeral. -/
theorem uniformBoundFG_energy0G (S : Sched G) (hS : SchedOS S) (W : ConfFlowG G)
    {D : Set (LField G)} (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) :
    UniformBoundFG S (energy0G S W D hD).map :=
  uniformBoundFG_energy S hS.trans W D hpos hcube

/-- **The observer's Schwartz-indexed Euclidean data over a schedule of `G`.** Inputs: `SchedOS S`,
`SchedShiftInv S`, (E) on the class `D` (`CubeMomentBoundG`), one exponential moment of the unit cube
for the field `O ∈ D` (`UnitCubeExpBoundG`), a physical range `r` for `energy0G`, (M) as the gap of
the transfer at one step `m0` at a rate `ρ < 1`, and (N) (`FlowConnectedNonzeroG`). The Schwinger
functions are `schwCMLG`, the constants from `abs_schwCMLG_le`; the Hilbert space, vacuum and time
translations are those of `TimeGroupG` in the direction `τ`, the gap the rate of
`TimeGroupG.flowN_time_group_of_gapG`.

DERIVED: `0` the sign of `L`, `ρ`, the reference step and the time origin; `1` the top of `ρ`; `4`
the dimension. -/
def observerOSDataSG (S : Sched G) (hS : SchedOS S) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O)
    {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG S (energy0G S W D hD) τ r) : OSDataS :=
  let hB := uniformBoundFG_energy0G S hS W hD hpos hcube
  let hpp := posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ
  let hT := flowN_time_group_of_gapG S hS (energy0G S W D hD) hB τ hphys m0 hL hρ0 hρ1 hg hNT
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
    time_zero := hμ.2.1.1
    time_add := hμ.2.1.2.1
    time_selfAdjoint := fun t ht => ⟨(hμ.2.1.2.2.2.1 t ht).2.1, (hμ.2.1.2.2.2.1 t ht).2.2⟩
    time_cont := hμ.2.1.2.2.2.2.1
    time_vac := hμ.2.1.2.2.2.2.2.1
    time_gap := hμ.2.1.2.2.2.2.2.2.1
    nontrivial := by
      obtain ⟨u, hu0, hu, _⟩ := hμ.2.2
      exact ⟨u, hu0, hu⟩ }

/-- **The observer's time translations over `G` have a self-adjoint generator.** `timeTG` is the
semigroup of real powers of `stepTG 0`, self-adjoint with spectrum in `[0, 1]` and trivial kernel
(`ClassHamiltonian.powSemigroup_generator_isSelfAdjoint`). The mirror of
`ClayFull.observer_generator_isSelfAdjoint`.

DERIVED: `0` the reference step. -/
theorem observer_generator_isSelfAdjointG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) :
    IsSelfAdjoint (ClassHamiltonian.generator (timeTG S hS Φ hB τ hpos)) :=
  ClassHamiltonian.powSemigroup_generator_isSelfAdjoint (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0)
    (spectrum_stepTG S hS Φ hB τ hpos 0) (stepTG_zero_injective S hS Φ hB τ hpos) (S.a_pos 0)

/-- **The observer's data over `G` have a self-adjoint generator**: `observer_generator_isSelfAdjointG`
read through `observerOSDataSG`'s time translations.

DERIVED: `0` the reference step. -/
theorem observerOSDataSG_isSelfAdjoint (S : Sched G) (hS : SchedOS S) (hsh : SchedShiftInv S)
    (W : ConfFlowG G) {D : Set (LField G)} (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O)
    {O : LField G} (hO : O ∈ D) (h : UnitCubeExpBoundG S W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0G S W D hD).PhysRange S r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS (energy0G S W D hD)
      (uniformBoundFG_energy0G S hS W hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG S (energy0G S W D hD) τ r) :
    IsSelfAdjoint (ClassHamiltonian.generator
      (observerOSDataSG S hS hsh W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT).time) :=
  observer_generator_isSelfAdjointG S hS (energy0G S W D hD)
    (uniformBoundFG_energy0G S hS W hD hpos hcube) τ
    (posPreserving_of_physRangeG S (energy0G S W D hD) hphys τ)

end Observer

end MassGap.ObserverOSG

end

#print axioms MassGap.ObserverOSG.schedShiftInv_canonSched
#print axioms MassGap.ObserverOSG.card_mul_boxSumG_le
#print axioms MassGap.ObserverOSG.state_cubeSumG_pow_le
#print axioms MassGap.ObserverOSG.cubeMoments_of_unitExpG
#print axioms MassGap.ObserverOSG.abs_smear_energy_le_shellsG
#print axioms MassGap.ObserverOSG.moment_smear_decay_leG
#print axioms MassGap.ObserverOSG.abs_contSFG_decay_le
#print axioms MassGap.ObserverOSG.latSFG_update
#print axioms MassGap.ObserverOSG.abs_contSFG_trunc_sub_le
#print axioms MassGap.ObserverOSG.tendsto_schwSFG
#print axioms MassGap.ObserverOSG.abs_schwSFG_le
#print axioms MassGap.ObserverOSG.schwSFG_comp_perm
#print axioms MassGap.ObserverOSG.schwSFG_update_add
#print axioms MassGap.ObserverOSG.schwSFG_update_smul
#print axioms MassGap.ObserverOSG.schwCMLG
#print axioms MassGap.ObserverOSG.abs_schwCMLG_le
#print axioms MassGap.ObserverOSG.uniformBoundFG_energy0G
#print axioms MassGap.ObserverOSG.observerOSDataSG
#print axioms MassGap.ObserverOSG.observer_generator_isSelfAdjointG
#print axioms MassGap.ObserverOSG.observerOSDataSG_isSelfAdjoint
