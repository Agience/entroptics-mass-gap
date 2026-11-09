import Mathlib
import MassGap.ObserverEnergyMoments
import MassGap.ObserverResidual
import MassGap.ObserverNVariance
import MassGap.EdgeStep
import MassGap.ClayRoutes

noncomputable section

/-!
# MassGap.ObserverEnergyM — M for the observer's energy density

The clustering input `FlowCapstone.FlowClusterAbs` of `ObserverEnergyMoments.obsEnergyOn` (the smeared
`SU(2)` observer scaled by `a⁻⁴`, less `s`, on a reflection-closed class `D` of fields, unscaled off `D`).

1. **A trivial view clusters for free** (`flowClusterAbs_of_not_connectedNonzero`): for any flow with the
   uniform bound keeping the half-space beyond its margin, if no margin monomial has a non-zero connected
   pairing then every connected kernel vanishes (Cauchy–Schwarz against the null vector `Q − S(Q)Ω`), and
   `FlowClusterAbs` holds at every window. For the bounded observer `ObserverClay.obsFlowF`, vanishing
   single-site variances give M and the failure of N together (`obsFlow_M_and_not_N_of_var`): a gap
   proved for the bounded observer's transfer carries no information.
2. **The two theories share the pre-space and agree off `D`** (`kernF_energyOn_eq`): both transfers act
   on `MarginMono 2 τ r →₀ ℝ` with the same shift and vacuum; the kernels agree on monomials with no field
   in `D`, so the energy density's clustering restricts to the bounded observer's on those monomials
   (`ofConf_cluster_of_energyOn`), and at `D = ∅` the two statements M coincide
   (`flowClusterAbs_energyOn_empty_iff`). On `D` the kernel is the `ultra`-limit of `a_k⁻⁴`-scaled
   moments, a limit of a different sequence; no statement relates it to the bounded kernel.
3. **The M reductions for the energy density** (`energy_M_iff_gap`, `energy_M_of_finite_time`,
   `energy_M_of_near_coarse`, `energy_M_of_leak`, `energy_clay_of_gap`): the generic statements of
   `ObserverGapScale` and `ObserverResidual` on the energy density's own transfer, under any proof of the
   uniform bound.
4. **Physical-rate sources** (`energy_M_of_fixedWindowDecay`, `energy_M_floor_su2_of_edgeStep`,
   `energy_M_of_chiForest`, `energy_clay_floor_su2_of_edgeStep`): `FixedWindowDecay` gives the reflected
   clustering bound of every flow with the uniform bound (`FlowCapstone.flowCluster_of_fixedWindowDecay`;
   the bound is relative, so the `a⁻⁴` factors cancel), and the tree's producers of `FixedWindowDecay` at
   `SU(2)` carry over.
-/

namespace MassGap.ObserverEnergyM

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. A trivial view clusters for free -/

section Trivial

/-- **Without a non-zero connected pairing every connected kernel vanishes.** If no margin monomial has
`S(θQ ∪ Q) − S(Q)² ≠ 0`, then `S(θP ∪ Q) − S(P) S(Q) = 0` for all margin monomials: the vector
`Q − S(Q)Ω` is null in the reconstructed form, and Cauchy–Schwarz pairs it to `0` with `P`.

DERIVED: `0` is the vanishing value and the step at which the form is read (any step serves); `1` the
basis coefficient; `2` the square; `4` in `Fin 4` is the spacetime dimension. -/
theorem conn_eq_zero_of_not_connectedNonzero (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving τ r) (h : ¬ FlowConnectedNonzero hN Φ τ r)
    (P Q : MarginMono N τ r) :
    kernF hN Φ τ P.1 Q.1 - kernF hN Φ τ P.1 (emptyMono N) * kernF hN Φ τ (emptyMono N) Q.1 = 0 := by
  set D := flowTransfer hN Φ hB τ hpos 0 with hD
  have hQ : kernF hN Φ τ Q.1 Q.1 - kernF hN Φ τ (emptyMargin N τ r).1 Q.1 ^ 2 = 0 := by
    by_contra hne
    exact h ⟨Q, hne⟩
  have fXY : ∀ X Y : MarginMono N τ r,
      D.form (Finsupp.single X 1) (Finsupp.single Y 1) = kernF hN Φ τ X.1 Y.1 := by
    intro X Y
    show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (Finsupp.single X 1)
      (Finsupp.single Y 1) = _
    rw [gForm_single, one_mul, one_mul]
  have fXv : ∀ X : MarginMono N τ r,
      D.form (Finsupp.single X 1) D.vac = kernF hN Φ τ X.1 (emptyMono N) := fun X => fXY X _
  have fvX : ∀ X : MarginMono N τ r,
      D.form D.vac (Finsupp.single X 1) = kernF hN Φ τ (emptyMono N) X.1 := fun X => fXY _ X
  have hnull : D.form (TransferGap.vacProj D (Finsupp.single Q 1))
      (TransferGap.vacProj D (Finsupp.single Q 1)) = 0 := by
    rw [form_vacProj, fXY, fXv, kernF_symm hN Φ τ Q.1 (emptyMono N)]
    exact hQ
  have hz : D.form (TransferGap.vacProj D (Finsupp.single Q 1)) (Finsupp.single P 1) = 0 :=
    D.toReflForm.form_eq_zero_of_mem_null (D.toReflForm.mem_nullSpace.mpr hnull) _
  unfold TransferGap.vacProj at hz
  rw [FiniteOrderTransfer.form_sub_left D.toPreForm, D.toPreForm.form_smul_left, fXY, fXv,
    fvX] at hz
  rw [kernF_symm hN Φ τ Q.1 P.1, kernF_symm hN Φ τ Q.1 (emptyMono N)] at hz
  rw [kernF_symm hN Φ τ P.1 (emptyMono N)]
  linear_combination hz

#print axioms conn_eq_zero_of_not_connectedNonzero

/-- **A trivial view satisfies M at every window.** For a flow with the uniform bound keeping the
half-space beyond its margin, `¬ FlowConnectedNonzero` gives `FlowClusterAbs` at every `L`, with rate
`1/L` and constant `0`.

DERIVED: `1` is the rate numerator chosen (any positive value serves); `0` the constant and the
vanishing kernel; `4` in `Fin 4` is the spacetime dimension. -/
theorem flowClusterAbs_of_not_connectedNonzero (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving τ r) (h : ¬ FlowConnectedNonzero hN Φ τ r)
    (L : ℝ) : FlowClusterAbs hN Φ τ r L := by
  refine ⟨1, one_pos, fun m P Q => ⟨0, fun n => ?_⟩⟩
  have hc := conn_eq_zero_of_not_connectedNonzero hN Φ hB τ hpos h P
    ((MarginMono.shift hN τ m)^[n] Q)
  rw [MarginMono.shift_iterate, kernF_vac_shift] at hc
  rw [hc, abs_zero, zero_mul]

#print axioms flowClusterAbs_of_not_connectedNonzero

/-- **The bounded observer: M and the failure of N from vanishing variances.** For the smeared observer
`obsFlowF` with a physical range bound, if every flowed field's single-site variance tends to `0` along
`ultra`, its clustering `FlowClusterAbs` holds at every window and `FlowConnectedNonzero` fails. M for
the bounded observer is then a statement about a space with no vacuum-orthogonal vector of non-zero
norm.

DERIVED: `2` is the rank; `0` is the limit and the lower end of `c`; `1/6` the dominance bound; `4` in
`Fin 4` is the spacetime dimension. -/
theorem obsFlow_M_and_not_N_of_var {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (τ : Fin 4) {r : ℝ} (hphys : (obsFlowF c hc0 hc n R).PhysRange r)
    (hvar : ∀ O : LField (MassGap.SUN.SU 2),
      Tendsto (fun k => ObserverNVariance.var (stateK two_ne k) ((obsFlowF c hc0 hc n R).map k O).1)
        (ultra : Filter ℕ) (𝓝 0)) :
    (∀ L : ℝ, FlowClusterAbs two_ne (obsFlowF c hc0 hc n R) τ r L)
      ∧ ¬ FlowConnectedNonzero two_ne (obsFlowF c hc0 hc n R) τ r := by
  have hN := ObserverNVariance.not_flowConnectedNonzero_of_var two_ne _ (Flow.ofConf_bounded _) τ r
    hvar
  exact ⟨fun L => flowClusterAbs_of_not_connectedNonzero two_ne _
    (uniformBoundF_of_bounded two_ne _ (Flow.ofConf_bounded _)) τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) hN L, hN⟩

#print axioms obsFlow_M_and_not_N_of_var

end Trivial

/-! ## 2. The energy density and the bounded observer share the pre-space and agree off `D` -/

section Compare

/-- **Flowed functions depend only on the flowed fields of the family.**

DERIVED: `0` is the excluded colour count. -/
theorem contSF_congr (hN : N ≠ 0) (Φ Ψ : Flow N) {ι : Type} [Fintype ι] (F : ι → SField N)
    (h : ∀ k i, Φ.map k (F i).1 = Ψ.map k (F i).1) : contSF hN Φ F = contSF hN Ψ F := by
  unfold contSF latSF
  have hfun : (fun k => latSk hN k (fun i => Φ.field k (F i)))
      = (fun k => latSk hN k (fun i => Ψ.field k (F i))) := by
    funext k
    have hF : (fun i => Φ.field k (F i)) = (fun i => Ψ.field k (F i)) := by
      funext i
      show (Φ.map k (F i).1, (F i).2) = (Ψ.map k (F i).1, (F i).2)
      rw [h k i]
    rw [hF]
  rw [hfun]

#print axioms contSF_congr

/-- **No field of the monomial lies in the class `D`.**

DERIVED: no numeral. -/
def OffClass (D : Set (LField (MassGap.SUN.SU N))) (P : Mono N) : Prop := ∀ i, (P.2 i).1 ∉ D

/-- **Off the class the energy density is the bounded flow**: for `O ∉ D` the class-scaled field of
step `k` is `O ∘ V_k`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem energyOn_map_of_not_mem (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∉ D) (k : ℕ) :
    (energyOn W D hD s hs).map k O = (Flow.ofConf W).map k O := by
  show scaleField ((W.fieldMap k O).sub (sOn D s k O)) (zOn D k O)
    = scaleField ((W.fieldMap k O).sub 0) 1
  rw [zOn_of_not_mem hO, sOn_of_not_mem hO]

#print axioms energyOn_map_of_not_mem

/-- **The two kernels agree off the class.** For monomials `P`, `Q` with no field in `D`,
`S(θP ∪ Q)` of the class-scaled flow is that of the bounded flow `Flow.ofConf W`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem kernF_energyOn_eq (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (τ : Fin 4) {P Q : Mono N} (hP : OffClass D P) (hQ : OffClass D Q) :
    kernF hN (energyOn W D hD s hs) τ P Q = kernF hN (Flow.ofConf W) τ P Q := by
  unfold kernF
  refine contSF_congr hN _ _ _ (fun k x => ?_)
  cases x with
  | inl i =>
    show (energyOn W D hD s hs).map k ((P.2 i).1.refl τ) = (Flow.ofConf W).map k ((P.2 i).1.refl τ)
    exact energyOn_map_of_not_mem W D hD s hs (fun h => hP i ((hD τ _).mp h)) k
  | inr j =>
    show (energyOn W D hD s hs).map k (Q.2 j).1 = (Flow.ofConf W).map k (Q.2 j).1
    exact energyOn_map_of_not_mem W D hD s hs (hQ j) k

#print axioms kernF_energyOn_eq

/-- **The energy density's clustering restricts to the bounded flow off the class.** `FlowClusterAbs`
of the class-scaled flow gives the bounded flow's clustering, at the same rate, on every pair of margin
monomials with no field in `D`.

DERIVED: `0` is the excluded colour count, the lower end of `c` and the empty monomial's size; `4` in
`Fin 4` is the spacetime dimension. -/
theorem ofConf_cluster_of_energyOn (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (τ : Fin 4) {r L : ℝ} (h : FlowClusterAbs hN (energyOn W D hD s hs) τ r L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (P Q : MarginMono N τ r), OffClass D P.1 → OffClass D Q.1 →
      ∃ C : ℝ, ∀ n : ℕ,
        |kernF hN (Flow.ofConf W) τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
            - kernF hN (Flow.ofConf W) τ P.1 (emptyMono N)
              * kernF hN (Flow.ofConf W) τ (emptyMono N) Q.1|
          ≤ C * Real.exp (-(c / L) * (dySpacing N m * n)) := by
  obtain ⟨c, hc, hcl⟩ := h
  refine ⟨c, hc, fun m P Q hP hQ => ?_⟩
  obtain ⟨C, hC⟩ := hcl m P Q
  refine ⟨C, fun n => ?_⟩
  have h0 : OffClass D (emptyMono N) := fun i => Fin.elim0 i
  have hQs : OffClass D (Mono.shift (timeVec N m τ n) Q.1) := fun i => hQ i
  rw [← kernF_energyOn_eq hN W D hD s hs τ hP hQs, ← kernF_energyOn_eq hN W D hD s hs τ hP h0,
    ← kernF_energyOn_eq hN W D hD s hs τ h0 hQ]
  exact hC n

#print axioms ofConf_cluster_of_energyOn

/-- **At the empty class the two statements M coincide.**

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem flowClusterAbs_energyOn_empty_iff (hN : N ≠ 0) (W : ConfFlow N)
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ (∅ : Set _) ↔ O ∈ (∅ : Set _))
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (τ : Fin 4) (r L : ℝ) :
    FlowClusterAbs hN (energyOn W ∅ hD s hs) τ r L ↔ FlowClusterAbs hN (Flow.ofConf W) τ r L := by
  have hk : kernF hN (energyOn W ∅ hD s hs) τ = kernF hN (Flow.ofConf W) τ := by
    funext P Q
    exact kernF_energyOn_eq hN W ∅ hD s hs τ (fun i h => h) (fun i h => h)
  unfold FlowClusterAbs
  rw [hk]

#print axioms flowClusterAbs_energyOn_empty_iff

end Compare

/-! ## 3. The M reductions for the energy density -/

section Reductions

/-- The energy density's reconstructed transfer at step `m₀`, under a proof `hB` of the uniform bound.

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
noncomputable abbrev energyTransfer {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) :
    Transfer.TransferData (MarginMono 2 τ r →₀ ℝ) :=
  flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs) hB τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) m0

/-- **M for the energy density is one gap at one step.** Under the uniform bound and a physical range
bound, at any step `m₀` and window `L > 0`: `FlowClusterAbs` of `obsEnergyOn` holds iff its transfer at
step `m₀` is `GapAt` some `0 < ρ < 1`.

DERIVED: `2` is the rank; `0` and `1` bracket the rate, `0` the lower end of `L`; `1/6` the dominance
bound. -/
theorem energy_M_iff_gap {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L
      ↔ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
          TransferGap.GapAt (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) ρ :=
  flowClusterAbs_iff_gapAt two_ne _ hB τ _ m0 hL

#print axioms energy_M_iff_gap

/-- **M for the energy density from one finite time.** `k ≥ 1` steps of its transfer at step `m₀`
contracting every vacuum-orthogonal vector by `ρ < 1` give `FlowClusterAbs`.

DERIVED: `2` is the rank and the form's degree; `0` and `1` bracket the rate, `0` the lower end of `k`
and `L` and the vacuum value; `1/6` the dominance bound. -/
theorem energy_M_of_finite_time {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L)
    {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : ∀ x, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form x
        (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac = 0 →
      (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) x)
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) x)
        ≤ ρ ^ 2 * (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form x x) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hk' : (0 : ℝ) < 1 / (k : ℝ) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  exact (energy_M_iff_gap hc0 hc n R D hD s hs hB τ hphys m0 hL).mpr
    ⟨ρ ^ (1 / (k : ℝ)), Real.rpow_pos_of_pos hρ0 _, Real.rpow_lt_one hρ0.le hρ1 hk',
      ObserverGapSplit.gapAt_of_iterate _ hk hρ0 hρ1.le h⟩

#print axioms energy_M_of_finite_time

/-- **M for the energy density from a gapped coarse view and nearness of slow vectors**
(`ObserverResidual.gapAt_of_near_coarse` on its transfer).

DERIVED: `2` is the rank and the form's degree; `0` and `1` bracket the rates, `k`, `κ` and `L`; `1/6`
the dominance bound. -/
theorem energy_M_of_near_coarse {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L)
    (C : Set (MarginMono 2 τ r →₀ ℝ)) {k : ℕ} (hk : 0 < k) {ρc κ : ℝ}
    (hρc : ρc ^ 2 < 1) (hκ : 0 < κ)
    (hcoarse : ∀ y ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y
        (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac = 0 →
      (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) y)
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) y)
        ≤ ρc ^ 2 * (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y y)
    (hnear : ∀ x, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form x
        (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac = 0 →
      ∃ y ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y
          (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac = 0 ∧
        κ * (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form (x - y) (x - y)
          ≤ (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form x x
            - (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form
              (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) x)
              (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) x)) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  (energy_M_iff_gap hc0 hc n R D hD s hs hB τ hphys m0 hL).mpr
    (ObserverResidual.gapAt_of_near_coarse _ C hk hρc hκ hcoarse hnear)

#print axioms energy_M_of_near_coarse

/-- **M for the energy density from three numbers at one time** (`ObserverResidual.gapAt_of_leak` on
its transfer): a submodule `C` holding the vacuum with an orthogonal split, coarse rate `ρc`, residual
rate `ρr`, leakage `η` with `η² < (1 − ρc²)(1 − ρr²)`.

DERIVED: `2` is the rank and the form's degree; `0` and `1` bracket the rates, `k` and `L`; `1/6` the
dominance bound. -/
theorem energy_M_of_leak {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L)
    (C : Submodule ℝ (MarginMono 2 τ r →₀ ℝ))
    (hvac : (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac ∈ C)
    (hsplit : ∀ x, ∃ y ∈ C, ∃ z,
      (∀ w ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form w z = 0) ∧ x = y + z)
    {k : ℕ} (hk : 0 < k) {ρc ρr η : ℝ} (hρc : ρc ^ 2 < 1) (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ρc ^ 2) * (1 - ρr ^ 2))
    (hcoarse : ∀ y ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y
        (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac = 0 →
      (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) y)
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) y)
        ≤ ρc ^ 2 * (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y y)
    (hres : ∀ z, (∀ w ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form w z = 0) →
      (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) z)
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) z)
        ≤ ρr ^ 2 * (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form z z)
    (hleak : ∀ y ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y
        (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac = 0 →
      ∀ z, (∀ w ∈ C, (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form w z = 0) →
      (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) y)
          (((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).T ^ k) z) ^ 2
        ≤ η ^ 2 * ((energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form y y
          * (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).form z z)) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  (energy_M_iff_gap hc0 hc n R D hD s hs hB τ hphys m0 hL).mpr
    (ObserverResidual.gapAt_of_leak _ C hvac hsplit hk hρc hρr hη hcoarse hres hleak)

#print axioms energy_M_of_leak

/-- **The energy density's continuum statement from one gap at one step.** Smeared moments on `D` (E),
a physical range bound, the transfer at one step `m₀` gapped at some `ρ < 1` (M), and
`FlowConnectedNonzero` (N) give, at every dyadic step, the gap at physical rate `c'/L` on a space with a
non-zero vector orthogonal to the vacuum.

DERIVED: `2` is the rank and makes the power even; `0` and `1` bracket the rate, `0` the lower end of
`L` and `c'`; `1/6` the dominance bound. -/
theorem energy_clay_of_gap {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK two_ne k (smear (dySpacing 2 k)
        ((obsEnergyOn c hc0 hc n R D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (energyTransfer hc0 hc n R D hD s hs
      (uniformBoundF_of_smearedMomentBound two_ne _
        (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM))
      τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  observer_energyOn_clay_of_smearedMoments hc0 hc n R D hD s hs hM τ hphys hL
    ((energy_M_iff_gap hc0 hc n R D hD s hs
      (uniformBoundF_of_smearedMomentBound two_ne _
      (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ hphys m0 hL).mpr ⟨ρ, hρ0, hρ1, hg⟩) hNT

#print axioms energy_clay_of_gap

end Reductions

/-! ## 4. Physical-rate sources of M for the energy density -/

section Sources

/-- **`FixedWindowDecay` gives M for the energy density.** Under the uniform bound and a physical range
bound, `WeakCouplingWindow.FixedWindowDecay τ 0 two_ne L` gives `FlowClusterAbs` of `obsEnergyOn`
(`FlowCapstone.flowCluster_of_fixedWindowDecay`: the reflected clustering bound is relative to the
diagonal kernels, so the `a⁻⁴` factors of the scaled fields cancel at every step).

DERIVED: `2` is the rank and the least rank with a non-zero Haar variance; `0` is the reflection plane
and the lower end of `L`; `1/6` the dominance bound. -/
theorem energy_M_of_fixedWindowDecay {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 two_ne L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  flowClusterAbs_of_flowCluster two_ne _ τ
    (flowCluster_of_fixedWindowDecay le_rfl two_ne _ hB τ
      (Flow.posPreserving_of_physRange two_ne _ hphys τ) hL hW)

#print axioms energy_M_of_fixedWindowDecay

/-- **M for the energy density from the floor box and the edge step.** At `SU(2)`, the proved floor box
(`PairCorrSharp.boxPatchGap_floor_su2`) and the edge step above the inverse box rate from
`floorBeta 2`, with a finite budget `E` of non-negative losses `δ`, give `FlowClusterAbs` of
`obsEnergyOn` (`EdgeStep.fixedWindowDecay_floor_su2_of_edgeStep`, `energy_M_of_fixedWindowDecay`).

DERIVED: `2` is the rank; `0` is the reflection plane and the sign of `L` and `δ`; `1/6` the dominance
bound; `2606`, `307/10000` are `PairCorrSharp.boxPatchGap_floor_su2`'s side and gap. -/
theorem energy_M_floor_su2_of_edgeStep {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) {L : ℝ} (hL : 0 < L)
    {δ : ℝ → ℝ} {E : ℝ}
    (hbud : UVIRSplit.LossBudget δ (AsymptoticScaling.aRun 2 (PairCorrSharp.floorBeta 2)) E)
    (hδ : ∀ t : ℝ, 0 ≤ δ t)
    (hedge : EdgeStep.UVEdgeStepAbove τ 0 two_ne (PairCorrSharp.floorBeta 2) δ
      (HeatBathLocal.boxRate 2 (PairCorrSharp.floorBeta 2) 2606 (307 / 10000))⁻¹) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_fixedWindowDecay hc0 hc n R D hD s hs hB τ hphys hL
    (EdgeStep.fixedWindowDecay_floor_su2_of_edgeStep two_ne τ hL hbud hδ hedge)

#print axioms energy_M_floor_su2_of_edgeStep

/-- **M for the energy density from the `χ²` forest of an observer and the carrier bridge**
(`OneCubeShims.fixedWindowDecay_of_chiForest`, `energy_M_of_fixedWindowDecay`).

DERIVED: `2` is the rank; `0` is the reflection plane and the lower end of `L`; `1/6` the dominance
bound. -/
theorem energy_M_of_chiForest {Ω : Type} [MeasurableSpace Ω] {ι : Type*} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c < 1 / 6) (n R : ℕ → ℕ) (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) {L : ℝ} (hL : 0 < L)
    {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ} (h : ChiForest.ChiForest m δ)
    (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ}
    (hK : ClayRoutes.ClassKappa m S aw bw a0 b0 κ) (hq : ClayRoutes.LimitFactor m S aw bw a0 b0 q₀)
    (hbr : ClayRoutes.ChiCarrierBridge τ 0 two_ne L m S aw bw a0 b0) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_fixedWindowDecay hc0 hc n R D hD s hs hB τ hphys hL
    (ClayRoutes.fixedWindowDecay_of_chiForest τ 0 two_ne h hprob hK hq hbr)

#print axioms energy_M_of_chiForest

/-- **The energy density's continuum statement from E, the edge step and N.** Smeared moments on `D`, a
physical range bound, the floor-box edge step with a finite budget, and `FlowConnectedNonzero` give, at
every dyadic step, the gap at physical rate `c'/L` on a space with a non-zero vector orthogonal to the
vacuum.

DERIVED: `2` is the rank and makes the power even; `0` is the reflection plane and the sign of `L`,
`δ` and `c'`; `1/6` the dominance bound; `2606`, `307/10000` are `PairCorrSharp.boxPatchGap_floor_su2`'s
side and gap. -/
theorem energy_clay_floor_su2_of_edgeStep {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK two_ne k (smear (dySpacing 2 k)
        ((obsEnergyOn c hc0 hc n R D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r)
    {L : ℝ} (hL : 0 < L) {δ : ℝ → ℝ} {E : ℝ}
    (hbud : UVIRSplit.LossBudget δ (AsymptoticScaling.aRun 2 (PairCorrSharp.floorBeta 2)) E)
    (hδ : ∀ t : ℝ, 0 ≤ δ t)
    (hedge : EdgeStep.UVEdgeStepAbove τ 0 two_ne (PairCorrSharp.floorBeta 2) δ
      (HeatBathLocal.boxRate 2 (PairCorrSharp.floorBeta 2) 2606 (307 / 10000))⁻¹)
    (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  observer_energyOn_clay_of_smearedMoments hc0 hc n R D hD s hs hM τ hphys hL
    (energy_M_floor_su2_of_edgeStep hc0 hc n R D hD s hs
      (uniformBoundF_of_smearedMomentBound two_ne _
      (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ hphys hL hbud hδ hedge) hNT

#print axioms energy_clay_floor_su2_of_edgeStep

end Sources

end MassGap.ObserverEnergyM
