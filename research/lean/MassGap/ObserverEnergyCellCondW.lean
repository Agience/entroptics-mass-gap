import Mathlib
import MassGap.ObserverEnergyCellCond

noncomputable section

/-!
# MassGap.ObserverEnergyCellCondW — the law clause as one weighted-row inequality

`ObserverEnergyCellCond.CondW1Row` asks for the W1 row of the cell field's conditional laws and, in
addition, for an exact zero: no influence beyond one unit of the cell distance. This module removes
the zero. The influence may reach every cell; only the weighted row is asked,
`Σ_k C(l,k) θ^{-cd(l,k)} ≤ α < 1` for one `θ ∈ (0, 1]`, and covariances decay as `θ^d`.

1. **Dobrushin's covariance bound for a weighted row** (`mass_stepU`, `cost_leU`,
   `cov_le_weightedU`): for any weight `u ≥ 0` with `Σ_k C(l,k) u_k ≤ α u_l` and plain rows `≤ α < 1`,
   `|σ(fg) − σf σg| ≤ M V_g/(1 − α) · Σ_k u_k v_f(k)` when `v_g ≤ V_g u`.
2. **Spatial decay with no range clause** (`cov_spatialWW`): for a site distance `D` (zero on the
   diagonal, triangle inequality) and `Σ_k C(l,k)/θ^{D(l,k)} ≤ α`, the weight `θ^{D(·, B)}` satisfies
   the weighted row, and readings `D`-farther than `d` from the sites `g` reads have
   `|Cov| ≤ M V_g/(1 − α) · θ^{d+1} Σ v_f`.
3. **The weighted W1 law and the chain** (`W1LawW`, `w1LawW_cov_margin`, `w1LawW_cov`, `CellViewW1W`,
   `latClusterRateOn_of_cellViewW1W`, `cellViewW1W_of_law`): as `ObserverEnergyCellW1.W1Law` with the
   weighted row in place of the plain row and the range clause; the cell readings cluster at `θ^{lv}`.
4. **The canonical box for it** (`RowAtW`, `CondW1RowW`, `w1LawW_of_rows`, `w1LawW_of_condW1RowW`):
   the window box laws of `ObserverEnergyCellCond` with CDF-form conditional kernels whose weighted
   row is `≤ α`.
5. **M at class `0.95`, rate `0.92`** (`eta_demand_W_92`, `energy_M_of_condW1RowW`), and the
   arithmetic of the measured row (`weighted_row_measured`).

## Scope

`CondW1RowW` is a hypothesis about the conditional laws of the cell energies of the Wilson state.
-/

namespace MassGap.ObserverEnergyCellCondW

open MeasureTheory Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap MassGap.ObserverEnergyMClose MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyCellM
open MassGap.HeatBath (exists_abs_le)
open MassGap.BoxDobrushinCoupling (oscStep)
open MassGap.BoxDobrushinSpatial (oscCost rep oscStep_nonneg)
open MassGap.DobrushinGeneral (cmul csmul csubc ex ex_mk ex_sub ex_const_mul abs_ex_le)
open MassGap.DobrushinUnbounded (Spec Invariant Tsp sweepS continuous_sweepS sweepS_rep affF)
open MassGap.DobrushinW1 (LipLe W1Infl cov_runW sweep_to_stateW)
open MassGap.ObserverEnergyCellW1 (pullR fieldMap affR affR_field affR_local lipLe_affPull sqR)
open MassGap.ObserverEnergyCellCond (Window CdfKernel cellDist_self cellDist_le)
open MassGap.ObserverEnergyMDob (eta_of_margin)

/-! ## 1. Dobrushin's covariance bound for a weighted row -/

section Weighted

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **The `u`-mass drops at every kernel.** If `C ≥ 0`, `u ≥ 0` and `Σ_k C(l,k) u_k ≤ β u_l`, then for
`v ≥ 0` the kernel at `l` gives `Σ u · oscStep C l v ≤ Σ u v − (1 − β) u_l v_l`.

DERIVED: `0` the sign; `1` the mass removed at `l`. -/
theorem mass_stepU {C : Lk → Lk → ℝ} (hC0 : ∀ l k, 0 ≤ C l k) {β : ℝ} {u : Lk → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hwr : ∀ l, ∑ k, C l k * u k ≤ β * u l) {v : Lk → ℝ}
    (hv : ∀ k, 0 ≤ v k) (l : Lk) :
    ∑ k, u k * oscStep C l v k ≤ ∑ k, u k * v k - (1 - β) * (u l * v l) := by
  have hpt : ∀ k, u k * oscStep C l v k
      ≤ u k * v k + C l k * u k * v l - (if k = l then u l * v l else 0) := by
    intro k
    by_cases hk : k = l
    · rw [hk]
      simp only [oscStep, ↓reduceIte, mul_zero]
      have := mul_nonneg (mul_nonneg (hC0 l l) (hu l)) (hv l)
      linarith
    · simp only [oscStep, hk, ↓reduceIte]
      exact le_of_eq (by ring)
  have h := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt k
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ l (fun _ => u l * v l), if_pos (Finset.mem_univ l)] at h
  have h2 : ∑ k, C l k * u k * v l ≤ β * u l * v l := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hwr l) (hv l)
  linarith

#print axioms mass_stepU

/-- **The cost of every run is bounded by the initial `u`-mass**: if `w ≤ V_g u`, then
`(1 − β) · oscCost C w L v ≤ V_g Σ_k u_k v_k` (`mass_stepU`).

DERIVED: `0` the sign; `1` the bound on `β`. -/
theorem cost_leU {C : Lk → Lk → ℝ} (hC0 : ∀ l k, 0 ≤ C l k) {β : ℝ} (hβ1 : β ≤ 1)
    {u : Lk → ℝ} (hu : ∀ k, 0 ≤ u k) (hwr : ∀ l, ∑ k, C l k * u k ≤ β * u l) {w : Lk → ℝ}
    {Vg : ℝ} (hVg : 0 ≤ Vg) (hw : ∀ k, w k ≤ Vg * u k) :
    ∀ (L : List Lk) (v : Lk → ℝ), (∀ k, 0 ≤ v k) →
      (1 - β) * oscCost C w L v ≤ Vg * ∑ k, u k * v k
  | [], v, hv => by
      simp only [oscCost, mul_zero]
      exact mul_nonneg hVg (Finset.sum_nonneg fun k _ => mul_nonneg (hu k) (hv k))
  | l :: L, v, hv => by
      have ih := cost_leU hC0 hβ1 hu hwr hVg hw L (oscStep C l v) (oscStep_nonneg hC0 hv l)
      have hm := mass_stepU hC0 hu hwr hv l
      have h0 := mul_le_mul_of_nonneg_left (hw l) (hv l)
      have h1 := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ 1 - β)
      have h2 := mul_le_mul_of_nonneg_left hm hVg
      show (1 - β) * (v l * w l + oscCost C w L (oscStep C l v)) ≤ _
      linarith

#print axioms cost_leU

/-- **Dobrushin's covariance bound, W1 form, for a weighted row.** For an invariant state of a
specification with W1 influence `C ≥ 0`, plain rows `≤ α < 1`, a weight `u ≥ 0` with
`Σ_k C(l,k) u_k ≤ α u_l`, continuous `f, g` with Lipschitz vectors `v_f, v_g`, `v_g ≤ V_g u`, and
`σ(x_l²) ≤ M` wherever `v_g(l) ≠ 0`: `|σ(f g) − σ f σ g| ≤ M V_g/(1 − α) · Σ_k u_k v_f(k)`
(`cov_runW`, `cost_leU` along `n` sweeps; the remainder vanishes by `sweep_to_stateW`).

DERIVED: `0` the sign of `α`, `M` and the limit of `αⁿ`; `1` the bound on `α`; `2 |R|` the
diameter in the vanishing tail. -/
theorem cov_le_weightedU {R : ℝ} {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)}
    (hσ : Invariant S σ) {C : Lk → Lk → ℝ} (hC : W1Infl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1) {u : Lk → ℝ} (hu : ∀ k, 0 ≤ u k)
    (hwr : ∀ l, ∑ k, C l k * u k ≤ α * u l) {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f)
    (hg : Continuous g) {vf vg : Lk → ℝ} (hvf : LipLe f vf) (hvg : LipLe g vg) {Vg M : ℝ}
    (hVg : 0 ≤ Vg) (hM0 : 0 ≤ M) (hw : ∀ k, vg k ≤ Vg * u k)
    (hM : ∀ l, vg l ≠ 0 → ex σ (fun W => (W l : ℝ) ^ 2) ≤ M) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg / (1 - α) * ∑ k, u k * vf k := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  obtain ⟨B, hB⟩ := exists_abs_le hg
  have hα1' : 0 < 1 - α := by linarith
  have hvf0 : ∀ k, 0 ≤ vf k := hvf.1
  have hS0 : 0 ≤ ∑ k, vf k := Finset.sum_nonneg fun k _ => hvf0 k
  have hw' : ∀ k, vg k * M ≤ M * Vg * u k := fun k => by
    have := mul_le_mul_of_nonneg_right (hw k) hM0
    linarith
  have hn : ∀ n : ℕ, |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg / (1 - α) * ∑ k, u k * vf k
        + α ^ n * (∑ k, vf k) * (2 * |R|) * B := by
    intro n
    have h1 := cov_runW hσ hC hC0 hg hvg hM (rep L n) hf hvf
    have h2 := cost_leU hC0 hα1.le hu hwr (mul_nonneg hM0 hVg) hw' (rep L n) vf hvf0
    have h3 : oscCost C (fun l => vg l * M) (rep L n) vf
        ≤ M * Vg / (1 - α) * ∑ k, u k * vf k := by
      have e : M * Vg / (1 - α) * ∑ k, u k * vf k = M * Vg * (∑ k, u k * vf k) / (1 - α) := by
        ring
      rw [e, le_div_iff₀ hα1']
      linarith
    have hc : Continuous (sweepS S (rep L n) f) := continuous_sweepS S _ hf
    have hT : ∀ W, |(sweepS S (rep L n) f W - ex σ f) * g W|
        ≤ α ^ n * (∑ k, vf k) * (2 * |R|) * B := by
      intro W
      have h := sweep_to_stateW hσ hC hC0 hrow hα0 hα1.le hL n ⟨f, hf⟩ hvf W
      rw [sweepS_rep] at h
      rw [abs_mul, ex_mk σ hf]
      exact mul_le_mul h (hB W) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (pow_nonneg hα0 n) hS0) (by positivity))
    have e : ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g
        = ex σ (fun W => (sweepS S (rep L n) f W - ex σ f) * g W) := by
      have e1 : (fun W => (sweepS S (rep L n) f W - ex σ f) * g W)
          = fun W => sweepS S (rep L n) f W * g W - ex σ f * g W :=
        funext fun W => by ring
      rw [e1, ex_sub σ (F := fun W => sweepS S (rep L n) f W * g W)
        (G := fun W => ex σ f * g W) (cmul hc hg) (csmul _ hg),
        ex_const_mul σ _ hg]
    have h4 : |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g|
        ≤ α ^ n * (∑ k, vf k) * (2 * |R|) * B := by
      rw [e]
      exact abs_ex_le σ (cmul (csubc hc (ex σ f)) hg) hT
    calc |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
        ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S (rep L n) f W * g W)|
          + |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith [h1.trans h3]
  have ht : Tendsto (fun n : ℕ => M * Vg / (1 - α) * ∑ k, u k * vf k
      + α ^ n * (∑ k, vf k) * (2 * |R|) * B)
      atTop (𝓝 (M * Vg / (1 - α) * ∑ k, u k * vf k
        + 0 * (∑ k, vf k) * (2 * |R|) * B)) :=
    ((((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const _).mul_const _).mul_const
      _).const_add _
  have hle := ge_of_tendsto' ht hn
  simpa using hle

#print axioms cov_le_weightedU

/-- **Spatial decay under a weighted row, no range clause.** For a site distance `D` (zero on the
diagonal, triangle inequality), `0 < θ ≤ 1`, and `Σ_k C(l,k)/θ^{D(l,k)} ≤ α < 1`: if `g` has
Lipschitz vector `≤ V_g` on `B` and `0` off it, `σ(x_l²) ≤ M` on `B`, and `f` reads only sites
`D`-farther than `d` from every site of `B`, then
`|σ(f g) − σ f σ g| ≤ M V_g/(1 − α) · θ^{d+1} Σ_k v_f(k)`. The weight is `θ^{ψ}`, `ψ` the distance
to `B`; it moves by at most `D(l,k)` from `l` to `k`, so the weighted row gives
`Σ_k C(l,k) θ^{ψ k} ≤ α θ^{ψ l}` (`cov_le_weightedU`).

DERIVED: `0` the sign and the vectors off the supports; `1` the bound on `θ` and the step beyond
`d`. -/
theorem cov_spatialWW {R : ℝ} {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)}
    (hσ : Invariant S σ) {C : Lk → Lk → ℝ} (hC : W1Infl S C) (hC0 : ∀ l k, 0 ≤ C l k)
    (D : Lk → Lk → ℕ) (hD0 : ∀ l, D l l = 0) (hD : ∀ a b c, D a c ≤ D a b + D b c)
    {α θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwrow : ∀ l, ∑ k, C l k / θ ^ D l k ≤ α)
    {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipLe f vf) (hvg : LipLe g vg) (B : Finset Lk) {Vg M : ℝ} (hVg : 0 ≤ Vg) (hM0 : 0 ≤ M)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg)
    (hM : ∀ l ∈ B, ex σ (fun W => (W l : ℝ) ^ 2) ≤ M) (d : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → ∀ b ∈ B, d < D k b) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg / (1 - α) * (θ ^ (d + 1) * ∑ k, vf k) := by
  obtain ⟨ψ, hψd⟩ : ∃ ψ : Lk → ℕ, ∀ k,
      ψ k = if h : B.Nonempty then B.inf' h (fun b => D k b) else d + 1 := ⟨_, fun _ => rfl⟩
  have hψ : ∀ l k, ψ l ≤ ψ k + D l k := by
    intro l k
    rw [hψd l, hψd k]
    by_cases h : B.Nonempty
    · rw [dif_pos h, dif_pos h]
      obtain ⟨b, hb, hbk⟩ := Finset.exists_mem_eq_inf' h (fun b => D k b)
      rw [hbk]
      calc B.inf' h (fun b => D l b) ≤ D l b := Finset.inf'_le _ hb
        _ ≤ D l k + D k b := hD l k b
        _ = D k b + D l k := add_comm _ _
    · rw [dif_neg h, dif_neg h]
      omega
  have hψB : ∀ k ∈ B, ψ k = 0 := by
    intro k hk
    rw [hψd k, dif_pos ⟨k, hk⟩]
    have h := Finset.inf'_le (fun b => D k b) hk
    rw [hD0 k] at h
    omega
  have hψfar : ∀ k, vf k ≠ 0 → d + 1 ≤ ψ k := by
    intro k hk
    rw [hψd k]
    by_cases h : B.Nonempty
    · rw [dif_pos h]
      exact Finset.le_inf' h _ fun b hb => hfar k hk b hb
    · rw [dif_neg h]
  have hθ0' : 0 ≤ θ := hθ0.le
  have hterm : ∀ l k, C l k * θ ^ ψ k ≤ C l k / θ ^ D l k * θ ^ ψ l := by
    intro l k
    have hpow : θ ^ ψ k * θ ^ D l k ≤ θ ^ ψ l := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hθ0' hθ1 (hψ l k)
    have hp : 0 < θ ^ D l k := pow_pos hθ0 _
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]
    calc C l k * θ ^ ψ k * θ ^ D l k = C l k * (θ ^ ψ k * θ ^ D l k) := by ring
      _ ≤ C l k * θ ^ ψ l := mul_le_mul_of_nonneg_left hpow (hC0 l k)
  have hwr : ∀ l, ∑ k, C l k * θ ^ ψ k ≤ α * θ ^ ψ l := by
    intro l
    calc ∑ k, C l k * θ ^ ψ k ≤ ∑ k, C l k / θ ^ D l k * θ ^ ψ l :=
          Finset.sum_le_sum fun k _ => hterm l k
      _ = (∑ k, C l k / θ ^ D l k) * θ ^ ψ l := by rw [Finset.sum_mul]
      _ ≤ α * θ ^ ψ l := mul_le_mul_of_nonneg_right (hwrow l) (pow_nonneg hθ0' _)
  have hrow : ∀ l, ∑ k, C l k ≤ α := by
    intro l
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hwrow l)
    have hp : 0 < θ ^ D l k := pow_pos hθ0 _
    rw [le_div_iff₀ hp]
    exact mul_le_of_le_one_right (hC0 l k) (pow_le_one₀ hθ0' hθ1)
  have hw : ∀ k, vg k ≤ Vg * θ ^ ψ k := by
    intro k
    by_cases hk : k ∈ B
    · rw [hψB k hk, pow_zero, mul_one]
      exact hgV k
    · rw [hgB k hk]
      exact mul_nonneg hVg (pow_nonneg hθ0' _)
  have hM' : ∀ l, vg l ≠ 0 → ex σ (fun W => (W l : ℝ) ^ 2) ≤ M := fun l hl =>
    hM l (by by_contra h; exact hl (hgB l h))
  have h := cov_le_weightedU hσ hC hC0 hrow hα0 hα1 (fun k => pow_nonneg hθ0' (ψ k)) hwr hf hg
    hvf hvg hVg hM0 hw hM'
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg (mul_nonneg hM0 hVg) (by linarith)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : vf k = 0
  · rw [hk]; simp
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0' hθ1 (hψfar k hk)) (hvf.1 k)

#print axioms cov_spatialWW

end Weighted

/-! ## 2. The weighted W1 law and the chain to clustering -/

section Law

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **A Dobrushin law of weighted W1 class `α` at rate `θ`.** As `ObserverEnergyCellW1.W1Law`, with
cell labels `cl_j` of the box sites (eventually inverting `ι_j` on every finite set of cells), and
with the weighted row `Σ_k C_j(l,k)/θ^{cd(cl_j l, cl_j k)} ≤ α` in place of the plain row and the
range clause: influence may reach every cell.

DERIVED: `0` the sign of `C`. -/
def W1LawW (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (α θ : ℝ) (cd : Cl → Cl → ℕ) : Prop :=
  ∃ (𝒰 : Filter ℕ) (M : ℕ → ℕ) (ι : (j : ℕ) → Cl → Fin (M j)) (cl : (j : ℕ) → Fin (M j) → Cl)
    (R : ℕ → ℝ) (S : (j : ℕ) → Spec (Tsp (R j)) (Fin (M j)))
    (σ : (j : ℕ) → DLRLimit.State (Fin (M j) → Tsp (R j)))
    (Cm : (j : ℕ) → Fin (M j) → Fin (M j) → ℝ),
    𝒰.NeBot ∧ (∀ j, W1Infl (S j) (Cm j)) ∧ (∀ j l k, 0 ≤ Cm j l k) ∧
    (∀ j l, ∑ k, Cm j l k / θ ^ cd (cl j l) (cl j k) ≤ α) ∧ (∀ j, Invariant (S j) (σ j)) ∧
    (∀ A : Finset Cl, ∀ᶠ j in 𝒰, ∀ c ∈ A, cl j (ι j c) = c) ∧
    ∀ (A : Finset Cl) (H : C(Cl → ℝ, ℝ)),
      (∀ y y' : Cl → ℝ, (∀ c ∈ A, y c = y' c) → H y = H y') →
      Tendsto (fun j => σ j (H.comp (pullR (ι j)))) 𝒰 (𝓝 (ν (H.comp (fieldMap e))))

/-- **Covariance decay of affine cell readings under a weighted W1 law, at one moment margin**:
`|ν(F G) − ν F ν G| ≤ (μ₂ + δ) W_G/(1 − α) · θ^{d+1} W_F` for cells more than `d` apart
(`cov_spatialWW` on each box at the site distance `cd ∘ cl`).

DERIVED: `2` the power of the moment; `1` the bounds on `θ`, `α` and the step beyond `d`; `0` the
signs. -/
theorem w1LawW_cov_margin {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {α θ : ℝ}
    {cd : Cl → Cl → ℕ} (hv : W1LawW ν e α θ cd) (hcd0 : ∀ c, cd c c = 0)
    (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ) {WF WG μ2 δ : ℝ}
    (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG) (hμ0 : 0 ≤ μ2) (hδ : 0 < δ)
    (hμ2 : ∀ c ∈ AG, ν (e c * e c) ≤ μ2) (d : ℕ) (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
      ≤ (μ2 + δ) * WG / (1 - α) * (θ ^ (d + 1) * WF) := by
  obtain ⟨𝒰, M, ι, cl, R, S, σ, Cm, hU, hC, hC0, hrow, hinv, hid, hL⟩ := hv
  haveI := hU
  have hWF0 : 0 ≤ WF := (Finset.sum_nonneg fun c _ => abs_nonneg (wF c)).trans hWF
  have hWG0 : 0 ≤ WG := (Finset.sum_nonneg fun c _ => abs_nonneg (wG c)).trans hWG
  have hM0 : 0 ≤ μ2 + δ := by linarith
  have hlocFG : ∀ y y' : Cl → ℝ, (∀ c ∈ AF ∪ AG, y c = y' c) →
      (affR AF wF bF * affR AG wG bG) y = (affR AF wF bF * affR AG wG bG) y' :=
    fun y y' h => by
      simp only [ContinuousMap.mul_apply]
      rw [affR_local AF wF bF y y' fun c hc => h c (Finset.mem_union_left _ hc),
        affR_local AG wG bG y y' fun c hc => h c (Finset.mem_union_right _ hc)]
  have lFG := hL _ _ hlocFG
  have lF := hL AF _ (affR_local AF wF bF)
  have lG := hL AG _ (affR_local AG wG bG)
  rw [ContinuousMap.mul_comp, affR_field, affR_field] at lFG
  rw [affR_field] at lF lG
  have hmom : ∀ᶠ j in 𝒰, ∀ c ∈ AG, σ j ((sqR c).comp (pullR (ι j))) < μ2 + δ := by
    refine (Filter.eventually_all_finset AG).2 fun c hc => ?_
    have hlc : ∀ y y' : Cl → ℝ, (∀ c' ∈ ({c} : Finset Cl), y c' = y' c') → sqR c y = sqR c y' :=
      fun y y' h => by
        show y c ^ 2 = y' c ^ 2
        rw [h c (Finset.mem_singleton_self c)]
    have t := hL {c} (sqR c) hlc
    have e0 : (sqR c).comp (fieldMap e) = e c * e c := by
      ext U
      show e c U ^ 2 = e c U * e c U
      ring
    rw [e0] at t
    exact t.eventually (eventually_lt_nhds (lt_of_le_of_lt (hμ2 c hc) (by linarith)))
  refine le_of_tendsto ((lFG.sub (lF.mul lG)).abs) ?_
  filter_upwards [hid (AF ∪ AG), hmom] with j hj hmj
  set f : C(Fin (M j) → Tsp (R j), ℝ) := (affR AF wF bF).comp (pullR (ι j)) with hfdef
  set g : C(Fin (M j) → Tsp (R j), ℝ) := (affR AG wG bG).comp (pullR (ι j)) with hgdef
  have e0 : (affR AF wF bF * affR AG wG bG).comp (pullR (ι j)) = f * g := by
    rw [ContinuousMap.mul_comp]
  rw [e0]
  have e1 : σ j (f * g) = ex (σ j) (fun W => f W * g W) :=
    (ex_mk (σ j) (cmul f.continuous g.continuous)).symm
  have e2 : σ j f = ex (σ j) f := (ex_mk (σ j) f.continuous).symm
  have e3 : σ j g = ex (σ j) g := (ex_mk (σ j) g.continuous).symm
  rw [e1, e2, e3]
  have hvf := lipLe_affPull (R := R j) (ι j) AF wF bF
  have hvg := lipLe_affPull (R := R j) (ι j) AG wG bG
  have hgB : ∀ k, k ∉ AG.image (ι j) → (∑ c ∈ AG with ι j c = k, |wG c|) = 0 :=
    fun k hk => Finset.sum_eq_zero fun c hc => absurd
      (Finset.mem_image.2 ⟨c, (Finset.mem_filter.1 hc).1, (Finset.mem_filter.1 hc).2⟩) hk
  have hgV : ∀ k, (∑ c ∈ AG with ι j c = k, |wG c|) ≤ WG := fun k =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun c _ _ => abs_nonneg _).trans hWG
  have hM : ∀ l ∈ AG.image (ι j), ex (σ j) (fun W => (W l : ℝ) ^ 2) ≤ μ2 + δ := by
    intro l hl
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hl
    have hcont : Continuous (fun W : Fin (M j) → Tsp (R j) => (W (ι j c) : ℝ) ^ 2) :=
      (continuous_subtype_val.comp (continuous_apply _)).pow 2
    rw [ex_mk (σ j) hcont]
    exact (hmj c hc).le
  have hfar : ∀ k, (∑ c ∈ AF with ι j c = k, |wF c|) ≠ 0 →
      ∀ b ∈ AG.image (ι j), d < cd (cl j k) (cl j b) := by
    intro k hk b hb
    obtain ⟨c, hc, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have hc' := Finset.mem_filter.1 hc
    obtain ⟨c', hc'', rfl⟩ := Finset.mem_image.1 hb
    rw [← hc'.2, hj c (Finset.mem_union_left _ hc'.1), hj c' (Finset.mem_union_right _ hc'')]
    exact hsep c hc'.1 c' hc''
  have hc := cov_spatialWW (hinv j) (hC j) (hC0 j) (fun l k => cd (cl j l) (cl j k))
    (fun l => hcd0 _) (fun a b c => hcd _ _ _) hθ0 hθ1 hα0 hα1 (hrow j) f.continuous g.continuous
    hvf hvg (AG.image (ι j)) hWG0 hM0 hgB hgV hM d hfar
  refine hc.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0.le _))
    (div_nonneg (mul_nonneg hM0 hWG0) (by linarith)))
  rw [Finset.sum_fiberwise AF (ι j) (fun c => |wF c|)]
  exact hWF

#print axioms w1LawW_cov_margin

/-- **Covariance decay of affine cell readings under a weighted W1 law**:
`|ν(F G) − ν F ν G| ≤ μ₂ W_G/(1 − α) · θ^{d+1} W_F` (`w1LawW_cov_margin` at `δ = 1/(n+1)`, and the
limit).

DERIVED: `1/(n+1)` the vanishing margin; `1` the bounds on `θ`, `α`; `0` the signs. -/
theorem w1LawW_cov {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {α θ : ℝ}
    {cd : Cl → Cl → ℕ} (hv : W1LawW ν e α θ cd) (hcd0 : ∀ c, cd c c = 0)
    (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ) {WF WG μ2 : ℝ}
    (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG) (hμ0 : 0 ≤ μ2)
    (hμ2 : ∀ c ∈ AG, ν (e c * e c) ≤ μ2) (d : ℕ) (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
      ≤ μ2 * WG / (1 - α) * (θ ^ (d + 1) * WF) := by
  have hn : ∀ n : ℕ,
      |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
        ≤ (μ2 + 1 / ((n : ℝ) + 1)) * WG / (1 - α) * (θ ^ (d + 1) * WF) := fun n =>
    w1LawW_cov_margin hv hcd0 hcd hθ0 hθ1 hα0 hα1 AF AG wF wG bF bG hWF hWG hμ0 (by positivity)
      hμ2 d hsep
  have ht : Tendsto (fun n : ℕ => (μ2 + 1 / ((n : ℝ) + 1)) * WG / (1 - α) * (θ ^ (d + 1) * WF))
      atTop (𝓝 ((μ2 + 0) * WG / (1 - α) * (θ ^ (d + 1) * WF))) :=
    ((((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _).div_const
      _).mul_const _)
  have h := ge_of_tendsto' ht hn
  simpa using h

#print axioms w1LawW_cov

end Law

section Chain

/-- **The cell view in the weighted W1 class**: the weighted W1 law eventually in the step, and the
reader clause of `ObserverEnergyCellW1.CellViewW1`, verbatim.

DERIVED: `2` the rank; `0` the reflection plane; `4` in `Fin 4` the spacetime dimension. -/
def CellViewW1W (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 lv : ℕ) (α θ : ℝ)
    (S : Set (MarginMono 2 τ r)) {Cl : Type} [DecidableEq Cl] (cd : Cl → Cl → ℕ)
    (e : ℕ → Cl → C(Cfg 2, ℝ)) : Prop :=
  (∀ᶠ k in atTop, W1LawW (stateK two_ne k) (e k) α θ cd) ∧
  ∀ P ∈ S, ∀ Q ∈ S, ∃ Wb Bb : ℝ, ∀ n : ℕ, ∃ (AP AQ : Finset Cl) (wP wQ : Cl → ℝ) (bP bQ : ℝ),
    ∑ c ∈ AP, |wP c| ≤ Wb ∧ ∑ c ∈ AQ, |wQ c| ≤ Wb ∧ |bP| ≤ Bb ∧ |bQ| ≤ Bb ∧
    (∀ c ∈ AP, ∀ c' ∈ AQ, lv * n < cd c c') ∧
    ∀ᶠ k in atTop,
      LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1))
          = affF (e k) AP wP bP ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1))
          = affF (e k) AQ wQ bQ

/-- **The weighted cell view gives lattice clustering at `θ^{lv}`**, with constant
`μ₂ W_b/(1 − α) · θ W_b` (`w1LawW_cov` at `d = lv · n`).

DERIVED: `1` the moment order `2 · 1` and the extra power of `θ`; `0` the reflection plane and the
signs. -/
theorem latClusterRateOn_of_cellViewW1W {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 lv : ℕ} {α θ : ℝ}
    {S : Set (MarginMono 2 τ r)} {Cl : Type} [DecidableEq Cl] {cd : Cl → Cl → ℕ}
    {e : ℕ → Cl → C(Cfg 2, ℝ)} (hV : CellViewW1W Φ τ r m0 lv α θ S cd e)
    (hM : CellMoments e) (hcd0 : ∀ c, cd c c = 0) (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    LatClusterRateOn two_ne Φ τ r m0 (θ ^ lv) S := by
  obtain ⟨hlaw, hread⟩ := hV
  intro P hP Q hQ
  obtain ⟨Wb, Bb, h⟩ := hread P hP Q hQ
  obtain ⟨C2, hC2⟩ := hM 1
  refine ⟨max C2 0 * Wb / (1 - α) * (θ * Wb), fun n => ?_⟩
  obtain ⟨AP, AQ, wP, wQ, bP, bQ, hWP, hWQ, hBP, hBQ, hsep, hrd⟩ := h n
  filter_upwards [hlaw, hrd, hC2] with k hk hrk h2
  obtain ⟨hPk, hQk⟩ := hrk
  have e1 : latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1))
      = stateK two_ne k (affF (e k) AP wP bP * affF (e k) AQ wQ bQ) := by
    rw [latSF_pair_eq, hPk, hQk]
  have e2 : latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2))
      = stateK two_ne k (affF (e k) AP wP bP) := by
    rw [latSF_pair_eq, hPk, mono_empty, prodSmear_empty, mul_one]
  have e3 : latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))
      = stateK two_ne k (affF (e k) AQ wQ bQ) := by
    rw [latSF_pair_eq, hQk, mono_empty, prodSmear_empty, ireflObs_one, one_mul]
  rw [e1, e2, e3]
  have hb := w1LawW_cov hk hcd0 hcd hθ0 hθ1 hα0 hα1 AP AQ wP wQ bP bQ hWP hWQ (le_max_right C2 0)
    (fun c _ => by
      have := h2 c
      rw [show 2 * 1 = 2 from rfl, pow_two] at this
      exact this.trans (le_max_left _ _))
    (lv * n) hsep
  refine hb.trans (le_of_eq ?_)
  rw [← pow_mul, pow_succ]
  ring

#print axioms latClusterRateOn_of_cellViewW1W

/-- **The reader clause is supplied on the single-cell monomials** (`cellView_readers`).

DERIVED: `1` the level `lv`. -/
theorem cellViewW1W_of_law (Φ : Flow 2) {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4)
    (r : ℝ) (I : Set (Fin nb)) (ρ : Fin nb → Fin nb)
    (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i)) {α θ : ℝ}
    (hlaw : ∀ᶠ k in atTop, W1LawW (stateK two_ne k) (cellE Φ base m0 k) α θ (cellDist τ)) :
    CellViewW1W Φ τ r m0 1 α θ (cellSet base m0 τ r I) (cellDist τ) (fun k => cellE Φ base m0 k) :=
  ⟨hlaw, cellView_readers Φ base m0 τ r I ρ hρ⟩

#print axioms cellViewW1W_of_law

end Chain

/-! ## 3. The canonical box for the weighted law -/

section Row

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **The weighted conditional W1 row at window `j`.** The box law `σ_j` of the window's cell
energies has CDF-form conditional kernels (`CdfKernel`, `σ_j` invariant under them) whose weighted
row is at most `α`: `Σ_k C(l,k)/θ^{cd(l,k)} ≤ α`, the sum over every cell of the window.

DERIVED: no numeral. -/
def RowAtW (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (Wn : Window Cl) (α θ : ℝ)
    (cd : Cl → Cl → ℕ) (j : ℕ) : Prop :=
  ∃ K : CdfKernel (Wn.bnd e j) (Fin (Wn.M j)),
    Invariant K.toW1.spec (Wn.boxLaw ν e j) ∧
    ∀ l, ∑ k, K.C l k / θ ^ cd (Wn.cellOf j l) (Wn.cellOf j k) ≤ α

/-- **The weighted conditional W1 row of the cell field**: `RowAtW` eventually in the window.

DERIVED: no numeral. -/
def CondW1RowW (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (Wn : Window Cl) (α θ : ℝ)
    (cd : Cl → Cl → ℕ) : Prop :=
  ∀ᶠ j in atTop, RowAtW ν e Wn α θ cd j

/-- **The weighted W1 law from the row at every window** (box laws, kernels, window indices and
cell labels of `ObserverEnergyCellCond`; `Window.boxLaw_read` for the limit).

DERIVED: no numeral. -/
theorem w1LawW_of_rows {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {Wn : Window Cl} {α θ : ℝ}
    {cd : Cl → Cl → ℕ} (h : ∀ j, RowAtW ν e Wn α θ cd j) : W1LawW ν e α θ cd := by
  choose K hinv hrow using h
  refine ⟨atTop, Wn.M, Wn.idx, Wn.cellOf, Wn.bnd e, fun j => (K j).toW1.spec, Wn.boxLaw ν e,
    fun j => (K j).C, inferInstance, fun j => (K j).toW1.w1Infl, fun j => (K j).C0, hrow, hinv,
    ?_, ?_⟩
  · intro A
    filter_upwards [(eventually_all_finset A).2 fun c _ => Wn.ev c] with j hj c hc
    exact Wn.cellOf_idx (hj c hc)
  · intro A H hH
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finset A).2 fun c _ => Wn.ev c] with j hj
    exact (Wn.boxLaw_read ν e A H hH hj).symm

#print axioms w1LawW_of_rows

/-- **The weighted W1 law of the cell field from its weighted conditional row.**

DERIVED: no numeral. -/
theorem w1LawW_of_condW1RowW {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {Wn : Window Cl}
    {α θ : ℝ} {cd : Cl → Cl → ℕ} (h : CondW1RowW ν e Wn α θ cd) : W1LawW ν e α θ cd := by
  obtain ⟨j0, hj0⟩ := eventually_atTop.1 h
  exact w1LawW_of_rows (Wn := Wn.shift j0) fun j => hj0 (j + j0) (Nat.le_add_left _ _)

#print axioms w1LawW_of_condW1RowW

end Row

/-! ## 4. M at class `0.95`, rate `0.92` -/

section M

/-- **The η demand at rate `θ = 23/25`.** Every `η` with `η² ≤ (23/100)²` passes:
`0.0529 < (1 − 0.8464) · 0.35 = 0.05376`.

DERIVED: `23/25` the rate; `23/100` the largest `η` kept; `13/20`, `7/20` as in `eta_of_margin`;
`1` the least `lv · k`; `2` the degree. -/
theorem eta_demand_W_92 {lv k : ℕ} (hlk : 1 ≤ lv * k) {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hη : η ^ 2 ≤ (23 / 100) ^ 2) :
    η ^ 2 < (1 - (((23 / 25 : ℝ) ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) :=
  eta_of_margin (by norm_num) (by norm_num) hlk hρr (by linarith)

#print axioms eta_demand_W_92

/-- **The measured row at rate `23/25`.** If the influence at time separation `0` and `1` sums to
at most `0.80` and at separation `2` to at most `0.04` (nothing beyond), the weighted row is
`≤ 0.80/0.92 + 0.04/0.92² < 0.917 ≤ 0.95`.

DERIVED: `4/5` the worst-neighbourhood row; `1/25` twice the larger error bar at `|Δt| = 2`;
`23/25` the rate; `95/100` the class. -/
theorem weighted_row_measured {a c2 : ℝ} (ha : a ≤ 4 / 5)
    (hc : c2 ≤ 1 / 25) : a / (23 / 25) + c2 / (23 / 25) ^ 2 ≤ 95 / 100 := by
  have e1 : a / (23 / 25 : ℝ) = a * (25 / 23) := by ring
  have e2 : c2 / (23 / 25 : ℝ) ^ 2 = c2 * (625 / 529) := by ring
  rw [e1, e2]
  nlinarith

#print axioms weighted_row_measured

/-- **M from E and the weighted conditional W1 row of the cell field at class `0.95`, rate
`0.92`.** For the single-cell readings of a base family in `D` with a reflection map on `I`, windows
`Λ` of the cell grid: E on `D`, `CondW1RowW` of class `95/100` at rate `23/25` in the time
separation of the step-`k` cell energies eventually in `k`, and the leakage inputs on
`coarseSpan (cellSet …)` at `η = 0.093`, `ρr² ≤ 13/20`, give `FlowClusterAbs`. No range clause
enters, and the uniform bound is the one E gives (`uniformBoundF_energyOn_of_cubeMoments`).

DERIVED: `95/100` the class; `23/25` the rate; `93/1000` the measured leakage; `13/20` as in
`eta_demand_W_92`; `1` the level; `2` the rank; `1/6` the dominance bound; `0` the sign of `k` and
`L`. -/
theorem energy_M_of_condW1RowW {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D) (I : Set (Fin nb))
    (ρ : Fin nb → Fin nb) (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i))
    (Wn : Window (Cell nb))
    (hrow : ∀ᶠ k in atTop, CondW1RowW (stateK two_ne k)
      (cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k) Wn (95 / 100) (23 / 25)
      (cellDist τ))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs
      (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) D hD s hs hpos
        hsub hcube) τ hphys m0)
      (coarseSpan (cellSet base m0 τ r I)) k ρr (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hB := uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) D hD s hs
    hpos hsub hcube
  have hV := cellViewW1W_of_law (obsEnergyOn c hc0 hc n R D hD s hs) base m0 τ r I ρ hρ
    (hrow.mono fun _ h => w1LawW_of_condW1RowW h)
  have hcl := latClusterRateOn_of_cellViewW1W hV
    (cellMoments_of_cube (obsConfFlow c hc0 hc n R) D hD s hs hpos hsub hcube base hbase m0)
    (cellDist_self τ) (cellDist_le τ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact energy_M_of_rate_leak hc0 hc n R D hD s hs hB τ hphys m0 (cellSet base m0 τ r I)
    (emptyMargin_mem_cellSet base m0 τ r I) (pow_nonneg (by norm_num) 1)
    (pow_lt_one₀ (by norm_num) (by norm_num) one_ne_zero) hcl hk (by linarith)
    (eta_demand_W_92 (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero one_ne_zero hk.ne')) hρr
      (by norm_num)) hL hLw

#print axioms energy_M_of_condW1RowW

/-- **M from E (cube form), the conditional W1 row with one-step range, and the leakage inputs**:
`ObserverEnergyCellCond.energy_M_of_condW1Row` with its uniform bound supplied by E
(`uniformBoundF_energyOn_of_cubeMoments`).

DERIVED: `95/100` the class; `93/1000` the measured leakage; `13/20` as in `eta_demand_W1_95`; `2`
the rank; `1/6` the dominance bound; `0` the sign of `L`. -/
theorem energy_M_of_condW1Row_cube {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D) (I : Set (Fin nb))
    (ρ : Fin nb → Fin nb) (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i))
    (Wn : Window (Cell nb))
    (hrow : ∀ᶠ k in atTop, MassGap.ObserverEnergyCellCond.CondW1Row (stateK two_ne k)
      (cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k) Wn (95 / 100) (cellDist τ))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs
      (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) D hD s hs hpos
        hsub hcube) τ hphys m0)
      (coarseSpan (cellSet base m0 τ r I)) k ρr (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  MassGap.ObserverEnergyCellCond.energy_M_of_condW1Row hc0 hc n R D hD s hs hpos hsub hcube _ τ
    hphys m0 base hbase I ρ hρ Wn hrow hk hρr hL hLw

#print axioms energy_M_of_condW1Row_cube

end M

end MassGap.ObserverEnergyCellCondW
