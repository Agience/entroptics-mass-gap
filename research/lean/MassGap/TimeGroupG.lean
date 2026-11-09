import Mathlib
import MassGap.FlowG

/-!
# MassGap.TimeGroupG — the continuous time translations of the flowed reconstruction, over `G`

`ContinuumTimeGroup` puts the dyadic transfers of `ContinuumFlow.flow_reconstruction` on one space and
extends the dyadic times to every real `t ≥ 0`; `ObserverGapScale` and `FlowCapstone` turn one gap at
one step into the gap at every step. This module states and proves the same for every `GaugeGroup G`
and every schedule `S` with `FlowG.SchedOS S`, for the flowed transfers `FlowG.flowTransferG`.

| `SU(N)` | here (any `G`, any `S`) |
|---|---|
| `ContinuumTimeGroup.FlowH`, `stepT`, `vacT`, `stepT_coe`, `stepT_sq` | `FlowHG`, `stepTG`, `vacTG`, `stepTG_coe`, `stepTG_sq` |
| `isSelfAdjoint_stepT`, `stepT_nonneg`, `spectrum_stepT`, `stepT_vacT` | `isSelfAdjoint_stepTG`, `stepTG_nonneg`, `spectrum_stepTG`, `stepTG_vacTG` |
| `stepT_eq_powT`, `stepT_commute` | `stepTG_eq_powT`, `stepTG_commute` |
| `gvecT`, `stepT_gvecT`, `exists_shift_preimage`, `stepT_succ_eq_zero` | `gvecTG`, `stepTG_gvecTG`, `exists_shift_preimageG`, `stepTG_succ_eq_zero` |
| `inner_pre_eq_zero`, `stepT_zero_injective` | `inner_pre_eq_zeroG`, `stepTG_zero_injective` |
| `timeT`, `dySpacing_eq_mul`, `timeT_dyadic` | `timeTG`, `FlowG.sched_a_eq_mul`, `timeTG_dyadic` |
| `timeT_zero`, `timeT_add`, `timeT_nonneg_norm`, `continuousOn_timeT`, `timeT_vacT` | `timeTG_zero`, `timeTG_add`, `timeTG_nonneg_norm`, `continuousOn_timeTG`, `timeTG_vacTG` |
| `timeT_gap`, `TimeGroupAt`, `flow_time_group` | `timeTG_gap`, `TimeGroupAtG`, `flow_time_groupG` |
| `ContinuumCluster.emptyMono`, `ObserverGapScale.mono_shift_empty`, `kernF_vac_shift` | `emptyMonoG`, `mono_shift_emptyG`, `kernFG_vac_shift` |
| `FlowCapstone.FlowClusterAbs`, `flow_gap_of_abs_cluster`, `flow_clay_of_abs_cluster` | `FlowClusterAbsG`, `flow_gap_of_abs_clusterG`, `flow_clay_of_abs_clusterG` |
| `ObserverGapScale.FlowClusterAt`, `flowClusterAbs_of_at`, `flowClusterAt_of_gapAt`, `flowClusterAbs_iff_gapAt` | `FlowClusterAtG`, `flowClusterAbs_of_atG`, `flowClusterAt_of_gapAtG`, `flowClusterAbs_iff_gapAtG` |
| `ObserverEnergyReductionsN.transferN`, `flowN_clay_of_gap` | `transferNG`, `flowN_clay_of_gapG` |
| `ContinuumTimeGroup.flowN_time_group_of_gap` | `flowN_time_group_of_gapG`; at `canonSched G`, `flowN_time_group_of_gap_canonG` |

The real powers of a positive contraction (`ContinuumTimeGroup.powT` and its lemmas `powT_zero`,
`powT_one`, `powT_add`, `powT_nat_mul`, `isSelfAdjoint_powT`, `powT_nonneg`, `norm_powT_le_one`,
`continuousOn_powT_apply`, `powT_apply_fixed`, `norm_powT_apply_le`, `spectrum_powT_subset`,
`eq_powT_of_sq`), the kernel-transfer gap `FlowCapstone.gapAt_gTransfer_of_abs_cluster`, and the
Hilbert-space facts of `GNSHilbert`, `GapToOperator`, `TransferGap` and `ContinuumSep` carry no group;
they are used here as they are.

Where `ContinuumTimeGroup` reads the spacing `dySpacing N m`, this module reads `S.a m`; where it
reads the halving `dySpacing_mul_pow`, this module reads `SchedOS.dyadic`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `0` the reference step, the time origin, the zero vector and
the signs; `1` the identity, the vacuum eigenvalue, the norm bound and the unit step; `1/2` the dyadic
ratio; `2` the square and the dyadic ratio of the grids.
-/

noncomputable section

namespace MassGap.TimeGroupG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumTimeGroup MassGap.FlowCapstone MassGap.ClayTreeG
  MassGap.ClayWiringG MassGap.FlowG Filter
open scoped Topology

/-! ## 1. The flowed reconstruction on one space -/

section Flow

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The one reconstructed Hilbert space** of the flowed transfers over `G`: every step has the
reflection form of step `0` (`flowTransferG` changes only the step).

DERIVED: `0` the step whose form names the space; `4` the dimension. -/
abbrev FlowHG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) : Type :=
  GNSHilbert.H (flowTransferG S hS Φ hB τ hpos 0).toReflForm

/-- The reflection form is the same at every step.

DERIVED: `0` the reference step; `4` the dimension. -/
theorem toReflForm_flowTransferG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m : ℕ) :
    (flowTransferG S hS Φ hB τ hpos m).toReflForm
      = (flowTransferG S hS Φ hB τ hpos 0).toReflForm := rfl

/-- **The step-`m` transfer on the one space**: the time translation by `S.a m`.

DERIVED: `4` the dimension. -/
def stepTG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m : ℕ) :
    FlowHG S hS Φ hB τ hpos →L[ℂ] FlowHG S hS Φ hB τ hpos :=
  GNSHilbert.opT (flowTransferG S hS Φ hB τ hpos m)

/-- **The one vacuum**: the vacuum of every step.

DERIVED: `0` the reference step; `4` the dimension. -/
def vacTG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) : FlowHG S hS Φ hB τ hpos :=
  GNSHilbert.Omega (flowTransferG S hS Φ hB τ hpos 0).toReflForm
    (flowTransferG S hS Φ hB τ hpos 0).vac

variable (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map) (τ : Fin 4)
  {r : ℝ} (hpos : Φ.PosPreserving S τ r)

/-- `stepTG` on a pre-Hilbert vector: the step applied to both components.

DERIVED: `0` the reference step; `4` the dimension. -/
theorem stepTG_coe (m : ℕ) (z : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm) :
    stepTG S hS Φ hB τ hpos m (z : FlowHG S hS Φ hB τ hpos)
      = ((GNSHilbert.Pre.ofPair (flowTransferG S hS Φ hB τ hpos 0).toReflForm
          ((flowTransferG S hS Φ hB τ hpos m).T (z : _ × _).1)
          ((flowTransferG S hS Φ hB τ hpos m).T (z : _ × _).2)
          : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm)
          : FlowHG S hS Φ hB τ hpos) :=
  GNSHilbert.opT_coe (flowTransferG S hS Φ hB τ hpos m) z

/-- **Two half steps are one step** on the one space: `stepTG (m+1)² = stepTG m`.

DERIVED: `1` the half-step offset; `4` the dimension. -/
theorem stepTG_sq (m : ℕ) :
    stepTG S hS Φ hB τ hpos (m + 1) * stepTG S hS Φ hB τ hpos (m + 1)
      = stepTG S hS Φ hB τ hpos m := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (stepTG S hS Φ hB τ hpos (m + 1) * stepTG S hS Φ hB τ hpos (m + 1)).continuous
      (stepTG S hS Φ hB τ hpos m).continuous) (fun z => ?_)
  rw [mul_apply_eq_comp, stepTG_coe, stepTG_coe, stepTG_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show (flowTransferG S hS Φ hB τ hpos (m + 1)).T ((flowTransferG S hS Φ hB τ hpos (m + 1)).T _)
      = (flowTransferG S hS Φ hB τ hpos m).T _
    exact (gT_half _ _ (fun P => marginShiftG_half S hS.dyadic τ m P) _).symm
  · show (flowTransferG S hS Φ hB τ hpos (m + 1)).T ((flowTransferG S hS Φ hB τ hpos (m + 1)).T _)
      = (flowTransferG S hS Φ hB τ hpos m).T _
    exact (gT_half _ _ (fun P => marginShiftG_half S hS.dyadic τ m P) _).symm

/-- DERIVED: `4` the dimension. -/
theorem isSelfAdjoint_stepTG (m : ℕ) : IsSelfAdjoint (stepTG S hS Φ hB τ hpos m) :=
  GNSHilbert.isSelfAdjoint_opT _

/-- **Every step is positive** (`FlowG.flowTransferG_positive`).

DERIVED: `0` the order's bottom; `4` the dimension. -/
theorem stepTG_nonneg (m : ℕ) : 0 ≤ stepTG S hS Φ hB τ hpos m :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (GNSHilbert.isPositive_opT _ (flowTransferG_positive S hS Φ hB τ hpos m))

/-- DERIVED: `0` and `1` bound the spectrum (`FlowG.flow_reconstructionG`); `4` the dimension. -/
theorem spectrum_stepTG (m : ℕ) : spectrum ℝ (stepTG S hS Φ hB τ hpos m) ⊆ Set.Icc 0 1 :=
  (flow_reconstructionG S hS Φ hB τ hpos m).1.2.2.2.2

/-- DERIVED: `4` the dimension. -/
theorem stepTG_vacTG (m : ℕ) :
    stepTG S hS Φ hB τ hpos m (vacTG S hS Φ hB τ hpos) = vacTG S hS Φ hB τ hpos :=
  GNSHilbert.opT_Omega (flowTransferG S hS Φ hB τ hpos m)

/-- **The steps are the dyadic roots of step `0`**: `stepTG m = (stepTG 0) ^ (1/2)^m`.

DERIVED: `1/2` the dyadic ratio; `0` the reference step; `4` the dimension. -/
theorem stepTG_eq_powT (m : ℕ) :
    stepTG S hS Φ hB τ hpos m = powT (stepTG S hS Φ hB τ hpos 0) ((1 / 2 : ℝ) ^ m) :=
  eq_powT_of_sq (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0) (spectrum_stepTG S hS Φ hB τ hpos 0)
    (stepTG S hS Φ hB τ hpos) rfl (stepTG_nonneg S hS Φ hB τ hpos) (stepTG_sq S hS Φ hB τ hpos) m

/-- **The steps commute.**

DERIVED: `1/2` the dyadic ratio; `4` the dimension. -/
theorem stepTG_commute (m m' : ℕ) :
    Commute (stepTG S hS Φ hB τ hpos m) (stepTG S hS Φ hB τ hpos m') := by
  rw [stepTG_eq_powT S hS Φ hB τ hpos m, stepTG_eq_powT S hS Φ hB τ hpos m']
  unfold powT
  exact cfc_commute_cfc (R := ℝ) (fun x : ℝ => x ^ ((1 / 2 : ℝ) ^ m))
    (fun x : ℝ => x ^ ((1 / 2 : ℝ) ^ m')) (stepTG S hS Φ hB τ hpos 0)

/-! ### The kernel of step `0` is trivial -/

/-- The reconstructed vector of a margin monomial.

DERIVED: `1` the coefficient; `0` the imaginary part and the reference step; `4` the dimension. -/
def gvecTG (Q : MarginMonoG G τ r) : FlowHG S hS Φ hB τ hpos :=
  ((GNSHilbert.Pre.ofPair (flowTransferG S hS Φ hB τ hpos 0).toReflForm (Finsupp.single Q 1) 0
    : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm) : FlowHG S hS Φ hB τ hpos)

/-- **The step moves a monomial forward**: `stepTG m (gvec Q) = gvec (shift_m Q)`.

DERIVED: `1` the coefficient; `0` the imaginary part; `4` the dimension. -/
theorem stepTG_gvecTG (m : ℕ) (Q : MarginMonoG G τ r) :
    stepTG S hS Φ hB τ hpos m (gvecTG S hS Φ hB τ hpos Q)
      = gvecTG S hS Φ hB τ hpos (marginShiftG S τ m Q) := by
  unfold gvecTG
  rw [stepTG_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show Finsupp.mapDomain (marginShiftG S τ m) (Finsupp.single Q 1)
      = Finsupp.single (marginShiftG S τ m Q) 1
    exact Finsupp.mapDomain_single
  · show (flowTransferG S hS Φ hB τ hpos m).T 0 = 0
    exact map_zero _

/-- **Every margin monomial is one step forward of a margin monomial**, at a step finer than its
margin: if every factor vanishes below `d > max r 0`, take `S.a m < min d (d − r)` and the monomial
shifted back by `S.a m`.

DERIVED: `0` the sign of the margin; `1` the unit step and its inverse `-1`; `4` the dimension. -/
theorem exists_shift_preimageG (Q : MarginMonoG G τ r) :
    ∃ (m : ℕ) (Q' : MarginMonoG G τ r), marginShiftG S τ m Q' = Q := by
  obtain ⟨P1, d, hd, hrd, hP⟩ := Q
  obtain ⟨m, hm⟩ := (S.a_lim.eventually (gt_mem_nhds (lt_min hd (sub_pos.mpr hrd)))).exists
  have hm1 : S.a m < d := lt_of_lt_of_le hm (min_le_left _ _)
  have hm2 : S.a m < d - r := lt_of_lt_of_le hm (min_le_right _ _)
  refine ⟨m, ⟨monoShiftG (timeVecG S m τ (-1)) P1, d - S.a m, by linarith, by linarith,
    fun i y hy => ?_⟩, ?_⟩
  · have h1 := hP i (y - timeVecG S m τ (-1)) hy
    have h2 : (y - timeVecG S m τ (-1)) τ = y τ - timeVecG S m τ (-1) τ := rfl
    rw [h2, timeVecG_self] at h1
    push_cast at h1
    linarith
  · apply Subtype.ext
    show monoShiftG (timeVecG S m τ 1) (monoShiftG (timeVecG S m τ (-1)) P1) = P1
    rw [monoShiftG_shift, timeVecG_add, neg_add_cancel, timeVecG_zero, monoShiftG_zero]

/-- A vector killed by step `m` is killed by step `m + 1`: `‖T x‖² = ⟪x, T² x⟫`.

DERIVED: `0` the zero vector; `1` the half-step offset; `4` the dimension. -/
theorem stepTG_succ_eq_zero {m : ℕ} {x : FlowHG S hS Φ hB τ hpos}
    (hx : stepTG S hS Φ hB τ hpos m x = 0) : stepTG S hS Φ hB τ hpos (m + 1) x = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_stepTG S hS Φ hB τ hpos (m + 1))
  have h1 : stepTG S hS Φ hB τ hpos (m + 1) (stepTG S hS Φ hB τ hpos (m + 1) x) = 0 := by
    rw [← mul_apply_eq_comp, stepTG_sq, hx]
  have h2 : inner ℂ (stepTG S hS Φ hB τ hpos (m + 1) x) (stepTG S hS Φ hB τ hpos (m + 1) x)
      = 0 := by
    have := hsym x (stepTG S hS Φ hB τ hpos (m + 1) x)
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h2

/-- **Orthogonal to the monomials is orthogonal to the pre-Hilbert space**.

DERIVED: `0` the zero combination and the imaginary part; `1` the coefficient; `4` the dimension. -/
theorem inner_pre_eq_zeroG (x : FlowHG S hS Φ hB τ hpos)
    (horth : ∀ Q : MarginMonoG G τ r, inner ℂ x (gvecTG S hS Φ hB τ hpos Q) = 0)
    (z : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm) :
    inner ℂ x (z : FlowHG S hS Φ hB τ hpos) = 0 := by
  have hlin : ∀ c : MarginMonoG G τ r →₀ ℝ,
      inner ℂ x ((GNSHilbert.Pre.ofPair (flowTransferG S hS Φ hB τ hpos 0).toReflForm c 0
        : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm)
          : FlowHG S hS Φ hB τ hpos) = 0 := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero =>
      have h0 : (GNSHilbert.Pre.ofPair (flowTransferG S hS Φ hB τ hpos 0).toReflForm
          (0 : MarginMonoG G τ r →₀ ℝ) 0
          : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm) = 0 :=
        GNSHilbert.Pre.ext rfl rfl
      rw [h0, UniformSpace.Completion.coe_zero, inner_zero_right]
    | add f g hf hg =>
      have h0 : (GNSHilbert.Pre.ofPair (flowTransferG S hS Φ hB τ hpos 0).toReflForm (f + g) 0
          : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm)
          = GNSHilbert.Pre.ofPair _ f 0 + GNSHilbert.Pre.ofPair _ g 0 :=
        GNSHilbert.Pre.ext rfl
          (show (0 : MarginMonoG G τ r →₀ ℝ) = 0 + 0 from (add_zero 0).symm)
      rw [h0, UniformSpace.Completion.coe_add, inner_add_right, hf, hg, add_zero]
    | single Q b =>
      have h0 : (GNSHilbert.Pre.ofPair (flowTransferG S hS Φ hB τ hpos 0).toReflForm
          (Finsupp.single Q b) 0 : GNSHilbert.Pre (flowTransferG S hS Φ hB τ hpos 0).toReflForm)
          = (b : ℂ) • GNSHilbert.Pre.ofPair _ (Finsupp.single Q 1) 0 := by
        refine GNSHilbert.Pre.ext ?_ ?_
        · show Finsupp.single Q b
            = (b : ℂ).re • Finsupp.single Q (1 : ℝ)
              + (-(b : ℂ).im) • (0 : MarginMonoG G τ r →₀ ℝ)
          simp only [Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_smul, add_zero,
            Finsupp.smul_single, smul_eq_mul, mul_one]
        · show (0 : MarginMonoG G τ r →₀ ℝ)
            = (b : ℂ).re • (0 : MarginMonoG G τ r →₀ ℝ) + (b : ℂ).im • Finsupp.single Q (1 : ℝ)
          simp only [Complex.ofReal_im, zero_smul, smul_zero, add_zero]
      rw [h0, UniformSpace.Completion.coe_smul, inner_smul_right]
      exact mul_eq_zero_of_right _ (horth Q)
  have hz : z = GNSHilbert.Pre.ofPair _ (z : _ × _).1 0
      + Complex.I • GNSHilbert.Pre.ofPair _ (z : _ × _).2 0 := by
    refine GNSHilbert.Pre.ext ?_ ?_
    · show (z : _ × _).1 = (z : _ × _).1 + (Complex.I.re • (z : _ × _).2
        + (-Complex.I.im) • (0 : MarginMonoG G τ r →₀ ℝ))
      simp only [Complex.I_re, Complex.I_im, zero_smul, smul_zero, add_zero]
    · show (z : _ × _).2 = (0 : MarginMonoG G τ r →₀ ℝ)
        + (Complex.I.re • (0 : MarginMonoG G τ r →₀ ℝ) + Complex.I.im • (z : _ × _).2)
      simp only [Complex.I_re, Complex.I_im, smul_zero, one_smul, zero_add]
  rw [hz, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul, inner_add_right,
    inner_smul_right, hlin, hlin, mul_zero, add_zero]

/-- **Step `0` has trivial kernel.** A vector killed by step `0` is killed by every step, hence
orthogonal to every reconstructed monomial, hence to every pre-Hilbert vector, which are dense.

DERIVED: `0` the reference step and the zero vector; `4` the dimension. -/
theorem stepTG_zero_injective (x : FlowHG S hS Φ hB τ hpos)
    (hx : stepTG S hS Φ hB τ hpos 0 x = 0) : x = 0 := by
  have hall : ∀ m, stepTG S hS Φ hB τ hpos m x = 0 := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih => exact stepTG_succ_eq_zero S hS Φ hB τ hpos ih
  have horth : ∀ Q : MarginMonoG G τ r, inner ℂ x (gvecTG S hS Φ hB τ hpos Q) = 0 := by
    intro Q
    obtain ⟨m, Q', hQ'⟩ := exists_shift_preimageG S τ Q
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_stepTG S hS Φ hB τ hpos m)
    rw [← hQ', ← stepTG_gvecTG]
    have := hsym x (gvecTG S hS Φ hB τ hpos Q')
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hall m, inner_zero_left]
  have hall' : ∀ y : FlowHG S hS Φ hB τ hpos, inner ℂ x y = 0 := fun y =>
    UniformSpace.Completion.induction_on y
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      (inner_pre_eq_zeroG S hS Φ hB τ hpos x horth)
  exact inner_self_eq_zero.mp (hall' x)

/-! ### The time translations -/

/-- **The time translation by `t`**: `(stepTG 0) ^ (t / S.a 0)`.

DERIVED: `0` the reference step; `4` the dimension. -/
def timeTG (t : ℝ) : FlowHG S hS Φ hB τ hpos →L[ℂ] FlowHG S hS Φ hB τ hpos :=
  powT (stepTG S hS Φ hB τ hpos 0) (t / S.a 0)

/-- **The time translations agree with the dyadic steps**: `timeTG (n · S.a m) = stepTG m ^ n`.

DERIVED: `0` the reference step; `1/2` the dyadic ratio; `4` the dimension. -/
theorem timeTG_dyadic (m n : ℕ) :
    timeTG S hS Φ hB τ hpos (n * S.a m) = stepTG S hS Φ hB τ hpos m ^ n := by
  have ha0 := S.a_pos 0
  unfold timeTG
  rw [sched_a_eq_mul S hS.dyadic m, stepTG_eq_powT S hS Φ hB τ hpos m,
    ← powT_nat_mul (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0) (spectrum_stepTG S hS Φ hB τ hpos 0)
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m) n]
  congr 1
  field_simp

/-- DERIVED: `0` the time origin; `1` the identity. -/
theorem timeTG_zero : timeTG S hS Φ hB τ hpos 0 = 1 := by
  unfold timeTG
  rw [zero_div, powT_zero (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0)]

/-- **The semigroup law** `T(s + t) = T(s) T(t)`, `s, t ≥ 0`.

DERIVED: `0` the sign of the times and the reference step. -/
theorem timeTG_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    timeTG S hS Φ hB τ hpos (s + t) = timeTG S hS Φ hB τ hpos s * timeTG S hS Φ hB τ hpos t := by
  have ha0 := S.a_pos 0
  unfold timeTG
  rw [add_div, powT_add (spectrum_stepTG S hS Φ hB τ hpos 0) (div_nonneg hs ha0.le)
    (div_nonneg ht ha0.le)]

/-- **Positive self-adjoint contractions.**

DERIVED: `0` the order's bottom and the sign of `t`; `1` the norm bound. -/
theorem timeTG_nonneg_norm (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ timeTG S hS Φ hB τ hpos t ∧ IsSelfAdjoint (timeTG S hS Φ hB τ hpos t)
      ∧ ‖timeTG S hS Φ hB τ hpos t‖ ≤ 1 :=
  ⟨powT_nonneg (spectrum_stepTG S hS Φ hB τ hpos 0) _, isSelfAdjoint_powT _,
    norm_powT_le_one (spectrum_stepTG S hS Φ hB τ hpos 0) (div_nonneg ht (S.a_pos 0).le)⟩

/-- **Strong continuity on `[0, ∞)`** (`continuousOn_powT_apply` with `stepTG_zero_injective`).

DERIVED: `0` the time origin and the reference step. -/
theorem continuousOn_timeTG (y : FlowHG S hS Φ hB τ hpos) :
    ContinuousOn (fun t => timeTG S hS Φ hB τ hpos t y) (Set.Ici 0) := by
  have ha0 := S.a_pos 0
  have hc := continuousOn_powT_apply (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0)
    (spectrum_stepTG S hS Φ hB τ hpos 0) (stepTG_zero_injective S hS Φ hB τ hpos) y
  have hd : ContinuousOn (fun t : ℝ => t / S.a 0) (Set.Ici 0) :=
    (continuous_id.div_const _).continuousOn
  exact hc.comp hd (fun t ht => div_nonneg ht ha0.le)

/-- **The vacuum is invariant at every time.**

DERIVED: `0` the sign of `t` and the reference step; `1/2` the dyadic ratio. -/
theorem timeTG_vacTG {t : ℝ} (ht : 0 ≤ t) :
    timeTG S hS Φ hB τ hpos t (vacTG S hS Φ hB τ hpos) = vacTG S hS Φ hB τ hpos := by
  have ha0 := S.a_pos 0
  refine powT_apply_fixed (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0)
    (spectrum_stepTG S hS Φ hB τ hpos 0) (fun m n => ?_) (div_nonneg ht ha0.le)
  rw [powT_nat_mul (isSelfAdjoint_stepTG S hS Φ hB τ hpos 0) (spectrum_stepTG S hS Φ hB τ hpos 0)
    (by positivity) n, ← stepTG_eq_powT]
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self]
  | succ n ih => rw [pow_succ, mul_apply_eq_comp, stepTG_vacTG, ih]

/-- **The dyadic gaps give the gap at every time.** If at every step the reconstructed transfer is
`GappedAt` the rate `e^{−μ S.a m}`, `μ ≥ 0` independent of `m`, then at every `t ≥ 0` the time
translation contracts the vacuum complement by `e^{−μ t}` and its spectrum lies in
`{1} ∪ [0, e^{−μ t}]`.

DERIVED: `0` the sign of `μ` and `t`, the vanishing vacuum pairing and the reference step; `1` the
vacuum eigenvalue; `1/2` the dyadic ratio; `4` the dimension. -/
theorem timeTG_gap {μ : ℝ} (hμ : 0 ≤ μ)
    (hgap : ∀ m : ℕ, ContinuumClay.GappedAt (flowTransferG S hS Φ hB τ hpos m)
      (Real.exp (-μ * S.a m))) {t : ℝ} (ht : 0 ≤ t) :
    (∀ u : FlowHG S hS Φ hB τ hpos, inner ℂ (vacTG S hS Φ hB τ hpos) u = 0 →
        ‖timeTG S hS Φ hB τ hpos t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
      ∧ spectrum ℝ (timeTG S hS Φ hB τ hpos t) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(μ * t))) := by
  have ha0 := S.a_pos 0
  have hsa := isSelfAdjoint_stepTG S hS Φ hB τ hpos 0
  have hsp := spectrum_stepTG S hS Φ hB τ hpos 0
  have htime : μ * S.a 0 * (t / S.a 0) = μ * t := by field_simp
  refine ⟨fun u hu => ?_, ?_⟩
  · have hd : ∀ m n : ℕ, ‖powT (stepTG S hS Φ hB τ hpos 0) (n * (1 / 2 : ℝ) ^ m) u‖
        ≤ Real.exp (-(μ * S.a 0 * (n * (1 / 2 : ℝ) ^ m))) * ‖u‖ := by
      intro m n
      rw [powT_nat_mul hsa hsp (by positivity) n, ← stepTG_eq_powT]
      have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (isSelfAdjoint_stepTG S hS Φ hB τ hpos m)
      have hstep : ∀ v : FlowHG S hS Φ hB τ hpos, inner ℂ (vacTG S hS Φ hB τ hpos) v = 0 →
          ‖stepTG S hS Φ hB τ hpos m v‖ ≤ Real.exp (-μ * S.a m) * ‖v‖ :=
        fun v hv => (hgap m).2.2.2.1 v hv
      have hinv : ∀ v : FlowHG S hS Φ hB τ hpos, inner ℂ (vacTG S hS Φ hB τ hpos) v = 0 →
          inner ℂ (vacTG S hS Φ hB τ hpos) (stepTG S hS Φ hB τ hpos m v) = 0 := by
        intro v hv
        have := hsym (vacTG S hS Φ hB τ hpos) v
        simp only [ContinuousLinearMap.coe_coe] at this
        rw [← this, stepTG_vacTG, hv]
      have hpow : ∀ k : ℕ,
          inner ℂ (vacTG S hS Φ hB τ hpos) ((stepTG S hS Φ hB τ hpos m ^ k) u) = 0
            ∧ ‖(stepTG S hS Φ hB τ hpos m ^ k) u‖ ≤ Real.exp (-μ * S.a m) ^ k * ‖u‖ := by
        intro k
        induction k with
        | zero =>
          rw [pow_zero, one_apply_eq_self, pow_zero, one_mul]
          exact ⟨hu, le_rfl⟩
        | succ k ih =>
          rw [pow_succ', mul_apply_eq_comp]
          refine ⟨hinv _ ih.1, (hstep _ ih.1).trans ?_⟩
          rw [pow_succ', mul_assoc]
          exact mul_le_mul_of_nonneg_left ih.2 (Real.exp_pos _).le
      refine (hpow n).2.trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul, sched_a_eq_mul S hS.dyadic m]
      congr 2
      ring
    have h := norm_powT_apply_le hsa hsp (mul_nonneg hμ ha0.le) hd (div_nonneg ht ha0.le)
    rw [htime] at h
    exact h
  · have hgap0 : spectrum ℝ (stepTG S hS Φ hB τ hpos 0)
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-μ * S.a 0)) := (hgap 0).2.2.2.2.1
    have h := spectrum_powT_subset hsa hsp hgap0 (div_nonneg ht ha0.le)
    rw [← Real.exp_mul] at h
    have e : -μ * S.a 0 * (t / S.a 0) = -(μ * t) := by field_simp
    rw [e] at h
    exact h

/-- **The continuous-time picture at rate `μ`** on the one reconstructed space over `G`: the time
translations `timeTG t`, `t ≥ 0`, form a strongly continuous semigroup of positive self-adjoint
contractions, `timeTG 0 = 1`, agreeing with the dyadic steps, fixing the vacuum, contracting its
complement by `e^{−μ t}`, with spectrum in `{1} ∪ [0, e^{−μ t}]`. The mirror of
`ContinuumTimeGroup.TimeGroupAt`.

DERIVED: `0` the time origin, the sign of `t`, `s`, the vanishing pairing; `1` the identity, the
vacuum eigenvalue and the norm bound; `4` the dimension. -/
def TimeGroupAtG (μ : ℝ) : Prop :=
  timeTG S hS Φ hB τ hpos 0 = 1
    ∧ (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        timeTG S hS Φ hB τ hpos (s + t) = timeTG S hS Φ hB τ hpos s * timeTG S hS Φ hB τ hpos t)
    ∧ (∀ m n : ℕ, timeTG S hS Φ hB τ hpos (n * S.a m) = stepTG S hS Φ hB τ hpos m ^ n)
    ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ timeTG S hS Φ hB τ hpos t ∧ IsSelfAdjoint (timeTG S hS Φ hB τ hpos t)
        ∧ ‖timeTG S hS Φ hB τ hpos t‖ ≤ 1)
    ∧ (∀ y : FlowHG S hS Φ hB τ hpos,
        ContinuousOn (fun t => timeTG S hS Φ hB τ hpos t y) (Set.Ici 0))
    ∧ (∀ t : ℝ, 0 ≤ t →
        timeTG S hS Φ hB τ hpos t (vacTG S hS Φ hB τ hpos) = vacTG S hS Φ hB τ hpos)
    ∧ (∀ t : ℝ, 0 ≤ t → ∀ u : FlowHG S hS Φ hB τ hpos, inner ℂ (vacTG S hS Φ hB τ hpos) u = 0 →
        ‖timeTG S hS Φ hB τ hpos t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
    ∧ (∀ t : ℝ, 0 ≤ t →
        spectrum ℝ (timeTG S hS Φ hB τ hpos t) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(μ * t))))

/-- **The continuous-time picture of the flowed reconstruction over `G`.** Under the dyadic gaps at a
rate `μ ≥ 0` independent of the step, `TimeGroupAtG` at rate `μ`. The mirror of
`ContinuumTimeGroup.flow_time_group`.

DERIVED: `0` the sign of `μ`; `4` the dimension. -/
theorem flow_time_groupG {μ : ℝ} (hμ : 0 ≤ μ)
    (hgap : ∀ m : ℕ, ContinuumClay.GappedAt (flowTransferG S hS Φ hB τ hpos m)
      (Real.exp (-μ * S.a m))) : TimeGroupAtG S hS Φ hB τ hpos μ :=
  ⟨timeTG_zero S hS Φ hB τ hpos, fun _ _ hs ht => timeTG_add S hS Φ hB τ hpos hs ht,
    timeTG_dyadic S hS Φ hB τ hpos, timeTG_nonneg_norm S hS Φ hB τ hpos,
    continuousOn_timeTG S hS Φ hB τ hpos, fun _ ht => timeTG_vacTG S hS Φ hB τ hpos ht,
    fun _ ht => (timeTG_gap S hS Φ hB τ hpos hμ hgap ht).1,
    fun _ ht => (timeTG_gap S hS Φ hB τ hpos hμ hgap ht).2⟩

end Flow

/-! ## 2. One gap at one step gives the gap at every step -/

section Gap

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The empty monomial. DERIVED: `0` factors. -/
abbrev emptyMonoG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] :
    MonoG G :=
  ⟨0, Fin.elim0⟩

/-- Translating the empty monomial leaves it unchanged.

DERIVED: `0` the number of factors; `4` the dimension. -/
theorem mono_shift_emptyG (v : Fin 4 → ℝ) : monoShiftG v (emptyMonoG G) = emptyMonoG G :=
  congrArg (Sigma.mk 0) (funext fun i => i.elim0)

/-- **The one-point function is translation invariant along the time grid**:
`S(θ∅ ∪ shift (S.a m · s) Q) = S(θ∅ ∪ Q)`.

DERIVED: `0` the base of the induction; `1` the unit step; `4` the dimension. -/
theorem kernFG_vac_shift (S : Sched G) (hT : SchedTransInv S) (Φ : GFlow G) (τ : Fin 4)
    (m s : ℕ) (Q : MonoG G) :
    kernFG S Φ τ (emptyMonoG G) (monoShiftG (timeVecG S m τ s) Q) = kernFG S Φ τ (emptyMonoG G) Q := by
  induction s with
  | zero => rw [Nat.cast_zero, timeVecG_zero, monoShiftG_zero]
  | succ s ih =>
    have h : monoShiftG (timeVecG S m τ ((s + 1 : ℕ) : ℤ)) Q
        = monoShiftG (timeVecG S m τ 1) (monoShiftG (timeVecG S m τ s) Q) := by
      rw [monoShiftG_shift, timeVecG_add, Nat.cast_succ]
    rw [h, ← kernFG_shift S hT Φ τ m, mono_shift_emptyG, ih]

/-- **The flowed clustering, absolute form**, over `G`: some `c > 0` such that at every step `m`
every pair of margin monomials has a constant `C` with the connected flowed kernel at time
`S.a m · n` at most `C e^{−(c/L) S.a m n}`. The mirror of `FlowCapstone.FlowClusterAbs`.

DERIVED: `0` the lower end of `c`; `4` the dimension. -/
def FlowClusterAbsG (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (r L : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (P Q : MarginMonoG G τ r), ∃ C : ℝ, ∀ n : ℕ,
    |kernFG S Φ τ P.1 (monoShiftG (timeVecG S m τ n) Q.1)
        - kernFG S Φ τ P.1 (emptyMonoG G) * kernFG S Φ τ (emptyMonoG G) Q.1|
      ≤ C * Real.exp (-(c / L) * (S.a m * n))

/-- **The flowed clustering along the grid of one step `m₀`**, over `G`. The mirror of
`ObserverGapScale.FlowClusterAt`.

DERIVED: `0` the lower end of `c`; `4` the dimension. -/
def FlowClusterAtG (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (r L : ℝ) (m0 : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P Q : MarginMonoG G τ r, ∃ C : ℝ, ∀ n : ℕ,
    |kernFG S Φ τ P.1 (monoShiftG (timeVecG S m0 τ n) Q.1)
        - kernFG S Φ τ P.1 (emptyMonoG G) * kernFG S Φ τ (emptyMonoG G) Q.1|
      ≤ C * Real.exp (-(c / L) * (S.a m0 * n))

/-- **The gap of the flowed transfer from the absolute clustering**, at every step
(`FlowCapstone.gapAt_gTransfer_of_abs_cluster`). The mirror of `FlowCapstone.flow_gap_of_abs_cluster`.

DERIVED: `0` the sign of the rate; `4` the dimension. -/
theorem flow_gap_of_abs_clusterG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) {L : ℝ}
    (hcl : FlowClusterAbsG S Φ τ r L) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      TransferGap.GapAt (flowTransferG S hS Φ hB τ hpos m) (Real.exp (-(c / L) * S.a m)) := by
  obtain ⟨c, hc, hcl⟩ := hcl
  refine ⟨c, hc, fun m => ?_⟩
  unfold flowTransferG
  refine gapAt_gTransfer_of_abs_cluster _ _ _ _ _ _ _ _ _ (Real.exp_pos _).le (fun P Q => ?_)
  obtain ⟨C, hC⟩ := hcl m P Q
  refine ⟨C, fun n => ?_⟩
  rw [marginShiftG_iterate]
  have hexp : Real.exp (-(c / L) * S.a m) ^ n = Real.exp (-(c / L) * (S.a m * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  exact hC n

/-- **The continuum statement from the absolute clustering**, over `G`: at every step the flowed
transfer is `GappedAt` the rate `e^{−(c/L) S.a m}` on a space with a non-zero vector orthogonal to
the vacuum. The mirror of `FlowCapstone.flow_clay_of_abs_cluster`.

DERIVED: `0` the lower end of `L` and `c`, and the spectral interval; `1` the vacuum eigenvalue;
`4` the dimension. -/
theorem flow_clay_of_abs_clusterG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) {L : ℝ}
    (hL : 0 < L) (hcl : FlowClusterAbsG S Φ τ r L) (hNT : FlowConnectedNonzeroG S Φ τ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt (flowTransferG S hS Φ hB τ hpos m) (Real.exp (-(c / L) * S.a m))
        ∧ ContinuumClay.NontrivialVacuum (flowTransferG S hS Φ hB τ hpos m) := by
  obtain ⟨c, hc, hg⟩ := flow_gap_of_abs_clusterG S hS Φ hB τ hpos hcl
  refine ⟨c, hc, fun m => ⟨?_, exists_orth_ne_zero_flowG S hS Φ hB τ hpos m hNT⟩⟩
  have hr0 : 0 < Real.exp (-(c / L) * S.a m) := Real.exp_pos _
  have hr1 : Real.exp (-(c / L) * S.a m) < 1 := by
    rw [Real.exp_lt_one_iff, neg_mul]
    exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (S.a_pos m))
  refine ⟨hr0, hr1, hg m, fun u hu => GapToOperator.norm_opT_le_of_orth _ hr0.le (hg m) u hu, ?_,
    GNSHilbert.isGreatest_one_spectrum_opT _⟩
  intro x hx
  rcases GapToOperator.spectrum_opT_subset _ hr0.le (hg m) hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Set.mem_Ici.mp
      (GNSHilbert.spectrum_opT_nonneg _ (flowTransferG_positive S hS Φ hB τ hpos m) hx), h.2⟩

/-- **Decay along one grid gives decay along every grid**, over `G`. The mirror of
`ObserverGapScale.flowClusterAbs_of_at`.

DERIVED: `2` the dyadic ratio of the grids; `0` the lower end of the remainder; `4` the dimension. -/
theorem flowClusterAbs_of_atG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (τ : Fin 4) {r L : ℝ}
    (m0 : ℕ) (h : FlowClusterAtG S Φ τ r L m0) : FlowClusterAbsG S Φ τ r L := by
  classical
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun m P Q => ?_⟩
  let Qs : ℕ → MarginMonoG G τ r := fun s =>
    ⟨monoShiftG (timeVecG S (m0 + m) τ s) Q.1, by
      obtain ⟨d, hd, hrd, hP⟩ := Q.2
      exact ⟨d, hd, hrd, posAtG_shift hP (timeVecG_nonneg_nat S (m0 + m) τ s)⟩⟩
  let Cf : ℕ → ℝ := fun s => Classical.choose (h P (Qs s))
  have hCf : ∀ s q : ℕ, |kernFG S Φ τ P.1 (monoShiftG (timeVecG S m0 τ q) (Qs s).1)
        - kernFG S Φ τ P.1 (emptyMonoG G) * kernFG S Φ τ (emptyMonoG G) (Qs s).1|
      ≤ Cf s * Real.exp (-(c / L) * (S.a m0 * q)) :=
    fun s => Classical.choose_spec (h P (Qs s))
  have haM : 0 < S.a (m0 + m) := S.a_pos (m0 + m)
  have hm : S.a (m0 + m) * 2 ^ m0 = S.a m := by
    have := hS.dyadic m (m0 + m) (show m ≤ m0 + m by omega)
    rwa [show m0 + m - m = m0 by omega] at this
  have hm0 : S.a (m0 + m) * 2 ^ m = S.a m0 := by
    have := hS.dyadic m0 (m0 + m) (show m0 ≤ m0 + m by omega)
    rwa [show m0 + m - m0 = m by omega] at this
  refine ⟨∑ s ∈ Finset.range (2 ^ m), |Cf s| * Real.exp (|c / L| * S.a m0), fun n => ?_⟩
  obtain ⟨q, s, hpqs, hslt⟩ : ∃ q s : ℕ, 2 ^ m * q + s = 2 ^ m0 * n ∧ s < 2 ^ m :=
    ⟨(2 ^ m0 * n) / 2 ^ m, (2 ^ m0 * n) % 2 ^ m, Nat.div_add_mod _ _,
      Nat.mod_lt _ (by positivity)⟩
  have hpqsR : (2 : ℝ) ^ m * q + s = 2 ^ m0 * n := by exact_mod_cast hpqs
  have hreal : S.a m * n = S.a m0 * q + S.a (m0 + m) * s := by
    rw [← hm, ← hm0]
    linear_combination (-(S.a (m0 + m))) * hpqsR
  have hvec : timeVecG S m τ (n : ℤ)
      = timeVecG S (m0 + m) τ (s : ℤ) + timeVecG S m0 τ (q : ℤ) := by
    funext i
    simp only [timeVecG, site, axisVec, Pi.add_apply]
    split_ifs
    · push_cast
      linarith [hreal]
    · simp
  have hshift : monoShiftG (timeVecG S m τ n) Q.1
      = monoShiftG (timeVecG S m0 τ q) (Qs s).1 := by
    show _ = monoShiftG (timeVecG S m0 τ q) (monoShiftG (timeVecG S (m0 + m) τ s) Q.1)
    rw [monoShiftG_shift, hvec]
  have hvac : kernFG S Φ τ (emptyMonoG G) (Qs s).1 = kernFG S Φ τ (emptyMonoG G) Q.1 :=
    kernFG_vac_shift S hS.trans Φ τ (m0 + m) s Q.1
  rw [hshift, ← hvac]
  refine (hCf s q).trans ?_
  have h1 : 0 ≤ S.a (m0 + m) * s := by positivity
  have h2 : S.a (m0 + m) * s ≤ S.a m0 := by
    rw [← hm0]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hslt.le) haM.le
  have h3 : c / L * (S.a (m0 + m) * s) ≤ |c / L| * S.a m0 :=
    calc c / L * (S.a (m0 + m) * s) ≤ |c / L| * (S.a (m0 + m) * s) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h1
      _ ≤ |c / L| * S.a m0 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hexp : Real.exp (-(c / L) * (S.a m0 * q))
      ≤ Real.exp (|c / L| * S.a m0) * Real.exp (-(c / L) * (S.a m * n)) := by
    rw [← Real.exp_add, hreal]
    apply Real.exp_le_exp.mpr
    nlinarith [h3]
  have hterm : |Cf s| * Real.exp (|c / L| * S.a m0)
      ≤ ∑ s' ∈ Finset.range (2 ^ m), |Cf s'| * Real.exp (|c / L| * S.a m0) :=
    Finset.single_le_sum (f := fun s' => |Cf s'| * Real.exp (|c / L| * S.a m0))
      (fun s' _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (Finset.mem_range.mpr hslt)
  calc Cf s * Real.exp (-(c / L) * (S.a m0 * q))
      ≤ |Cf s| * Real.exp (-(c / L) * (S.a m0 * q)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |Cf s| * (Real.exp (|c / L| * S.a m0) * Real.exp (-(c / L) * (S.a m * n))) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = (|Cf s| * Real.exp (|c / L| * S.a m0)) * Real.exp (-(c / L) * (S.a m * n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le

/-- **The gap at one step gives clustering along that step's grid**, over `G`
(`TransferGap.clustering_sq` on two basis vectors). The mirror of
`ObserverGapScale.flowClusterAt_of_gapAt`.

DERIVED: `0` and `1` bracket the rate; `2` the square; `4` the dimension. -/
theorem flowClusterAt_of_gapAtG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m0 : ℕ)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (flowTransferG S hS Φ hB τ hpos m0) ρ) {L : ℝ} (hL : 0 < L) :
    FlowClusterAtG S Φ τ r L m0 := by
  have ha := S.a_pos m0
  have hlog : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ0 hρ1)
  refine ⟨L * (-Real.log ρ) / S.a m0, by positivity, fun P Q => ?_⟩
  set D := flowTransferG S hS Φ hB τ hpos m0 with hD
  refine ⟨Real.sqrt (kernFG S Φ τ P.1 P.1
    * D.form (TransferGap.vacProj D (Finsupp.single Q 1))
        (TransferGap.vacProj D (Finsupp.single Q 1))), fun n => ?_⟩
  have hexpo : -(L * (-Real.log ρ) / S.a m0 / L) * (S.a m0 * n) = n * Real.log ρ := by
    field_simp
  have hexp : Real.exp (-(L * (-Real.log ρ) / S.a m0 / L) * (S.a m0 * n)) = ρ ^ n := by
    rw [hexpo, Real.exp_nat_mul, Real.exp_log hρ0]
  rw [hexp]
  have hcs := TransferGap.clustering_sq D hρ0.le hg n (Finsupp.single Q 1) (Finsupp.single P 1)
  have e1 : D.form (Finsupp.single P 1) ((D.T ^ n) (Finsupp.single Q 1))
      = kernFG S Φ τ P.1 (monoShiftG (timeVecG S m0 τ n) Q.1) := by
    rw [Module.End.pow_apply]
    show gForm (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1) (Finsupp.single P 1)
      ((⇑(gT (marginShiftG S τ m0)))^[n] (Finsupp.single Q 1)) = _
    rw [gT_iterate, Finsupp.mapDomain_single, gForm_single, one_mul, one_mul,
      marginShiftG_iterate]
  have e2 : D.form (Finsupp.single P 1) D.vac = kernFG S Φ τ P.1 (emptyMonoG G) := by
    show gForm (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1) (Finsupp.single P 1)
      (Finsupp.single (emptyMarginG G τ r) 1) = _
    rw [gForm_single, one_mul, one_mul]
    rfl
  have e3 : D.form D.vac (Finsupp.single Q 1) = kernFG S Φ τ (emptyMonoG G) Q.1 := by
    show gForm (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1)
      (Finsupp.single (emptyMarginG G τ r) 1) (Finsupp.single Q 1) = _
    rw [gForm_single, one_mul, one_mul]
    rfl
  have e4 : D.form (Finsupp.single P 1) (Finsupp.single P 1) = kernFG S Φ τ P.1 P.1 := by
    show gForm (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1) (Finsupp.single P 1)
      (Finsupp.single P 1) = _
    rw [gForm_single, one_mul, one_mul]
  rw [e1, e2, e3, e4, show ρ ^ (2 * n) = (ρ ^ n) ^ 2 by rw [← pow_mul, mul_comm]] at hcs
  have hfin := ContinuumSep.abs_le_mul_sqrt_of_sq_le_sep (pow_nonneg hρ0.le n) hcs
  linarith [hfin, mul_comm (ρ ^ n) (Real.sqrt (kernFG S Φ τ P.1 P.1
    * D.form (TransferGap.vacProj D (Finsupp.single Q 1))
        (TransferGap.vacProj D (Finsupp.single Q 1))))]

/-- **The absolute clustering is one gap at one step**, over `G`: `FlowClusterAbsG` holds if and only
if the flowed transfer at step `m₀` is `GapAt` some `ρ` with `0 < ρ < 1`. The mirror of
`ObserverGapScale.flowClusterAbs_iff_gapAt`.

DERIVED: `0` and `1` bracket the rate and `0` the lower end of `L`; `4` the dimension. -/
theorem flowClusterAbs_iff_gapAtG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m0 : ℕ)
    {L : ℝ} (hL : 0 < L) :
    FlowClusterAbsG S Φ τ r L
      ↔ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (flowTransferG S hS Φ hB τ hpos m0) ρ := by
  constructor
  · intro h
    obtain ⟨c, hc, hg⟩ := flow_gap_of_abs_clusterG S hS Φ hB τ hpos h
    refine ⟨Real.exp (-(c / L) * S.a m0), Real.exp_pos _, ?_, hg m0⟩
    rw [Real.exp_lt_one_iff, neg_mul]
    exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (S.a_pos m0))
  · rintro ⟨ρ, hρ0, hρ1, hg⟩
    exact flowClusterAbs_of_atG S hS Φ τ m0
      (flowClusterAt_of_gapAtG S hS Φ hB τ hpos m0 hρ0 hρ1 hg hL)

/-- The reconstructed transfer of a flow at step `m₀` under a physical range bound, over `G`.

DERIVED: `4` the dimension. -/
abbrev transferNG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m0 : ℕ) :
    Transfer.TransferData (MarginMonoG G τ r →₀ ℝ) :=
  flowTransferG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) m0

/-- **The continuum statement of any flow over `G` from one gap at one step.** The transfer at one
step `m₀` gapped at some `0 < ρ < 1` and `FlowConnectedNonzeroG` give, at every step, the gap at rate
`e^{−(c'/L) S.a m}` on a space with a non-zero vector orthogonal to the vacuum. The mirror of
`ObserverEnergyReductionsN.flowN_clay_of_gap`.

DERIVED: `0` and `1` bracket the rate, `0` the lower end of `L` and `c'`; `4` the dimension. -/
theorem flowN_clay_of_gapG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS Φ hB τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG S Φ τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt (transferNG S hS Φ hB τ hphys m) (Real.exp (-(c' / L) * S.a m))
        ∧ ContinuumClay.NontrivialVacuum (transferNG S hS Φ hB τ hphys m) :=
  flow_clay_of_abs_clusterG S hS Φ hB τ _ hL
    ((flowClusterAbs_iff_gapAtG S hS Φ hB τ _ m0 hL).mpr ⟨ρ, hρ0, hρ1, hg⟩) hNT

/-- **The continuous-time capstone for any flow over `G`**: the uniform bound, a physical range
bound, the transfer at one step gapped and `FlowConnectedNonzeroG` give a rate `μ > 0` and
`TimeGroupAtG` at that rate on the one reconstructed space, together with a non-zero vector
orthogonal to the vacuum. The mirror of `ContinuumTimeGroup.flowN_time_group_of_gap`.

DERIVED: `0` the sign of `μ`, `L`, `ρ` and the reference step; `1` the top of `ρ`; `4` the
dimension. -/
theorem flowN_time_group_of_gapG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hphys : Φ.PhysRange S r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG S hS Φ hB τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG S Φ τ r) :
    ∃ μ : ℝ, 0 < μ
      ∧ TimeGroupAtG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) μ
      ∧ ContinuumClay.NontrivialVacuum (transferNG S hS Φ hB τ hphys 0) := by
  obtain ⟨c', hc', h⟩ := flowN_clay_of_gapG S hS Φ hB τ hphys m0 hL hρ0 hρ1 hg hNT
  refine ⟨c' / L, div_pos hc' hL, ?_⟩
  have hgap : ∀ m : ℕ, ContinuumClay.GappedAt
      (flowTransferG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ) m)
      (Real.exp (-(c' / L) * S.a m)) := fun m => (h m).1
  exact ⟨flow_time_groupG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hphys τ)
    (div_pos hc' hL).le hgap, (h 0).2⟩

/-- **The continuous-time capstone at the canonical schedule of `G`**: `flowN_time_group_of_gapG` at
`canonSched G`, with `SchedOS` from `FlowG.schedOS_canonSched`.

DERIVED: `0` the sign of `μ`, `L`, `ρ` and the reference step; `1` the top of `ρ`; `4` the
dimension. -/
theorem flowN_time_group_of_gap_canonG [GaugeSimple G] (Φ : GFlow G)
    (hB : UniformBoundFG (canonSched G) Φ.map) (τ : Fin 4) {r : ℝ}
    (hphys : Φ.PhysRange (canonSched G) r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched Φ hB τ hphys m0) ρ)
    (hNT : FlowConnectedNonzeroG (canonSched G) Φ τ r) :
    ∃ μ : ℝ, 0 < μ
      ∧ TimeGroupAtG (canonSched G) schedOS_canonSched Φ hB τ
          (posPreserving_of_physRangeG (canonSched G) Φ hphys τ) μ
      ∧ ContinuumClay.NontrivialVacuum
          (transferNG (canonSched G) schedOS_canonSched Φ hB τ hphys 0) :=
  flowN_time_group_of_gapG (canonSched G) schedOS_canonSched Φ hB τ hphys m0 hL hρ0 hρ1 hg hNT

end Gap

end MassGap.TimeGroupG

end

#print axioms MassGap.TimeGroupG.toReflForm_flowTransferG
#print axioms MassGap.TimeGroupG.stepTG_coe
#print axioms MassGap.TimeGroupG.stepTG_sq
#print axioms MassGap.TimeGroupG.stepTG_nonneg
#print axioms MassGap.TimeGroupG.spectrum_stepTG
#print axioms MassGap.TimeGroupG.stepTG_eq_powT
#print axioms MassGap.TimeGroupG.stepTG_commute
#print axioms MassGap.TimeGroupG.stepTG_gvecTG
#print axioms MassGap.TimeGroupG.exists_shift_preimageG
#print axioms MassGap.TimeGroupG.stepTG_succ_eq_zero
#print axioms MassGap.TimeGroupG.inner_pre_eq_zeroG
#print axioms MassGap.TimeGroupG.stepTG_zero_injective
#print axioms MassGap.TimeGroupG.timeTG_dyadic
#print axioms MassGap.TimeGroupG.timeTG_zero
#print axioms MassGap.TimeGroupG.timeTG_add
#print axioms MassGap.TimeGroupG.timeTG_nonneg_norm
#print axioms MassGap.TimeGroupG.continuousOn_timeTG
#print axioms MassGap.TimeGroupG.timeTG_vacTG
#print axioms MassGap.TimeGroupG.timeTG_gap
#print axioms MassGap.TimeGroupG.flow_time_groupG
#print axioms MassGap.TimeGroupG.mono_shift_emptyG
#print axioms MassGap.TimeGroupG.kernFG_vac_shift
#print axioms MassGap.TimeGroupG.flow_gap_of_abs_clusterG
#print axioms MassGap.TimeGroupG.flow_clay_of_abs_clusterG
#print axioms MassGap.TimeGroupG.flowClusterAbs_of_atG
#print axioms MassGap.TimeGroupG.flowClusterAt_of_gapAtG
#print axioms MassGap.TimeGroupG.flowClusterAbs_iff_gapAtG
#print axioms MassGap.TimeGroupG.flowN_clay_of_gapG
#print axioms MassGap.TimeGroupG.flowN_time_group_of_gapG
#print axioms MassGap.TimeGroupG.flowN_time_group_of_gap_canonG
