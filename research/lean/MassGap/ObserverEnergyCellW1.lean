import Mathlib
import MassGap.DobrushinW1
import MassGap.ObserverEnergyCellWitness

noncomputable section

/-!
# MassGap.ObserverEnergyCellW1 — M for the energy density from the cell view in Dobrushin's W1 class

`ObserverEnergyCellM.CellViewDobrushin` asks the truncated cell-energy field to be in Dobrushin's
total-variation class at every truncation level. For cell energies that respond linearly to an
unbounded neighbour, the TV influence grows with the level. This module replaces the law clause by
Dobrushin's Kantorovich (W1) condition, which is scale-free, and runs the same chain to M.

1. **The W1 law** (`pullR`, `fieldMap`, `affR`, `W1Law`): a state read through the real-valued cell
   field is a limit of states on finite boxes, each invariant under a specification with spins in an
   interval `[-|R_j|, |R_j|]` whose W1 influence matrix has row sums `≤ α`; influence moves at most
   one unit of a cell distance `cd`. No truncation level enters.
2. **Covariance decay of affine cell readings** (`lipLe_affPull`, `w1Law_cov`): readings
   `b + Σ_{c ∈ A} w_c e_c` with `Σ|w| ≤ W`, cells more than `d` apart, and `ν(e_c²) ≤ μ₂` at the cells
   of the second reading have `|ν(F G) − ν F ν G| ≤ μ₂ W_G θ/(θ − α) · θ^{d+1} W_F`
   (`DobrushinW1.cov_spatialW` on each box, moments carried from the limit, passed to the limit).
3. **The hypothesis and the chain** (`CellViewW1`, `latClusterRateOn_of_cellViewW1`,
   `energy_M_of_cellViewW1`, `energy_M_of_cellViewW1_cube`): `CellViewW1` with the cell moments of
   E gives `LatClusterRateOn` at `θ^{lv}` for every `θ ∈ (α, 1]`, hence M. The rate is `θ`, not the
   `√θ` of the truncated TV chain, and only the second moment is used.
4. **The demand at the measured rows** (`eta_demand_W1_877`, `eta_demand_W1_95`,
   `energy_M_of_cellViewW1_877`, `energy_M_of_cellViewW1_95`, `energy_M_of_cellLawW1_877`): at
   `α = 0.877` every `η ≤ 0.28` passes, at `α = 0.95` every `η ≤ 0.18`; the measured `η = 0.093`
   passes both.
5. **Non-vacuity** (`pairSpec_w1`, `w1Law_pair`, `pair_w1_877`): the coupled `±1` pair of
   `ObserverEnergyCellWitness` is in W1 class `2κ` with covariance `2κ`; at `κ = 877/2000` the class
   and the covariance are both `0.877`.
6. **The W1 class is strictly wider than the TV class** (`shiftSpec`, `shiftSpec_w1`,
   `shiftSpec_not_tv`, `shift_877`): a specification whose spin is the other spin times `κ` plus a
   fair `±(1 − κ)` has W1 row sums `κ`, while for `κ > 1/2` every TV influence matrix of it has an
   entry `≥ 1`. A linear response with disjoint conditional supports is the mechanism the
   measurement reads in the cell energies.

## Scope

The W1 law of the cell-energy field is a hypothesis; nothing here derives it from the fine measure.
The reader clause is the one of `CellViewDobrushin`, proved for single-cell monomials by
`ObserverEnergyCellM.cellView_readers`.
-/

namespace MassGap.ObserverEnergyCellW1

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap MassGap.ObserverEnergyMClose MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyCellM Filter
open MassGap.DobrushinUnbounded (Spec SInfl Invariant Tsp clampL affF tspin continuous_tspin)
open MassGap.DobrushinGeneral (ex ex_mk cmul)
open MassGap.DobrushinW1 (LipLe W1Infl cov_spatialW)
open MassGap.BoxDobrushinSpatial (reach)
open MassGap.ObserverEnergyMDob (eta_of_margin)
open MassGap.ObserverEnergyCellWitness (oth oth_ne oth_eq pairSpec pairInfl pairStateOn pairOn wEq wNe
  invariant_pair pairCell pairDist pair_cov reach_empty)
open scoped Topology

/-! ## 1. The W1 law of a real-valued cell field -/

section Law

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **A box configuration read as a real cell configuration** through `ι`.

DERIVED: no numeral. -/
def pullR {R : ℝ} {M : ℕ} (ι : Cl → Fin M) : C(Fin M → Tsp R, Cl → ℝ) :=
  ⟨fun W c => (W (ι c) : ℝ),
    continuous_pi fun c => continuous_subtype_val.comp (continuous_apply (ι c))⟩

/-- **The cell field**: each cell reading, untruncated.

DERIVED: no numeral. -/
def fieldMap (e : Cl → C(X, ℝ)) : C(X, Cl → ℝ) :=
  ⟨fun U c => e c U, continuous_pi fun c => (e c).continuous⟩

/-- **An affine reading of a real cell configuration**: `b + Σ_{c ∈ A} w_c y_c`.

DERIVED: no numeral. -/
def affR (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) : C(Cl → ℝ, ℝ) :=
  ⟨fun y => b + ∑ c ∈ A, w c * y c,
    continuous_const.add (continuous_finset_sum _ fun c _ => continuous_const.mul (continuous_apply c))⟩

/-- **The square of one cell reading.**

DERIVED: `2` the power. -/
def sqR (c : Cl) : C(Cl → ℝ, ℝ) := ⟨fun y => y c ^ 2, (continuous_apply c).pow 2⟩

/-- The affine reading of the cell field is the affine cell reading.

DERIVED: no numeral. -/
theorem affR_field (e : Cl → C(X, ℝ)) (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) :
    (affR A w b).comp (fieldMap e) = affF e A w b := by
  ext U; rfl

#print axioms affR_field

/-- An affine reading reads only the cells of `A`.

DERIVED: no numeral. -/
theorem affR_local (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) (y y' : Cl → ℝ)
    (h : ∀ c ∈ A, y c = y' c) : affR A w b y = affR A w b y' := by
  show b + ∑ c ∈ A, w c * y c = b + ∑ c ∈ A, w c * y' c
  rw [Finset.sum_congr rfl fun c hc => by rw [h c hc]]

#print axioms affR_local

/-- **The Lipschitz vector of an affine reading on the box**: changing the box spin at `k` moves
`b + Σ_c w_c W(ι c)` by at most `Σ_{c ∈ A, ι c = k} |w_c| · |Δ|`.

DERIVED: no numeral. -/
theorem lipLe_affPull {R : ℝ} {M : ℕ} (ι : Cl → Fin M) (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) :
    LipLe (fun W : Fin M → Tsp R => (affR A w b).comp (pullR ι) W)
      (fun k => ∑ c ∈ A with ι c = k, |w c|) := by
  refine ⟨fun k => Finset.sum_nonneg fun c _ => abs_nonneg _, fun W k x => ?_⟩
  show |(b + ∑ c ∈ A, w c * (Function.update W k x (ι c) : ℝ))
      - (b + ∑ c ∈ A, w c * (W (ι c) : ℝ))|
    ≤ (∑ c ∈ A with ι c = k, |w c|) * |(x : ℝ) - (W k : ℝ)|
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not A (fun c => ι c = k)]
  have h0 : ∑ c ∈ A with ¬ ι c = k,
      (w c * (Function.update W k x (ι c) : ℝ) - w c * (W (ι c) : ℝ)) = 0 :=
    Finset.sum_eq_zero fun c hc => by
      rw [Function.update_of_ne (Finset.mem_filter.1 hc).2]
      ring
  rw [h0, add_zero, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c hc => ?_)
  rw [(Finset.mem_filter.1 hc).2, Function.update_self, ← mul_sub, abs_mul]

#print axioms lipLe_affPull

/-- **A Dobrushin law of W1 class `α`.** Read through the real cell field, the state `ν` is the
limit along a filter `𝒰` of states `σ_j` on finite boxes `Fin (M j)` of spins in `[-|R_j|, |R_j|]`,
read through cell maps `ι_j`; each `σ_j` is invariant under a specification `S_j` with a non-negative
W1 influence matrix `C_j` of row sums `≤ α`; and influence moves at most one unit of the cell
distance `cd`: cells of `A` more than `d` from every cell of `A'` lie, eventually along `𝒰`, outside
the `d`-step influence neighbourhood of the image of `A'`. The limit is asked only of readings of
finitely many cells. The interval of each box is free: no bound in the chain depends on it.

DERIVED: `0` the sign of `C`. -/
def W1Law (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (α : ℝ) (cd : Cl → Cl → ℕ) : Prop :=
  ∃ (𝒰 : Filter ℕ) (M : ℕ → ℕ) (ι : (j : ℕ) → Cl → Fin (M j)) (R : ℕ → ℝ)
    (S : (j : ℕ) → Spec (Tsp (R j)) (Fin (M j)))
    (σ : (j : ℕ) → DLRLimit.State (Fin (M j) → Tsp (R j)))
    (Cm : (j : ℕ) → Fin (M j) → Fin (M j) → ℝ),
    𝒰.NeBot ∧ (∀ j, W1Infl (S j) (Cm j)) ∧ (∀ j l k, 0 ≤ Cm j l k) ∧
    (∀ j l, ∑ k, Cm j l k ≤ α) ∧ (∀ j, Invariant (S j) (σ j)) ∧
    (∀ (A A' : Finset Cl) (d : ℕ), (∀ c ∈ A, ∀ c' ∈ A', d < cd c c') →
      ∀ᶠ j in 𝒰, ∀ c ∈ A, ι j c ∉ reach (Cm j) (A'.image (ι j)) d) ∧
    ∀ (A : Finset Cl) (H : C(Cl → ℝ, ℝ)),
      (∀ y y' : Cl → ℝ, (∀ c ∈ A, y c = y' c) → H y = H y') →
      Tendsto (fun j => σ j (H.comp (pullR (ι j)))) 𝒰 (𝓝 (ν (H.comp (fieldMap e))))

/-- **Covariance decay of affine cell readings at one moment margin.** Under a W1 law of class `α`,
`α < θ ≤ 1`, readings with `Σ|w_F| ≤ W_F`, `Σ|w_G| ≤ W_G`, cells more than `d` apart, and
`ν(e_c²) ≤ μ₂ < μ₂ + δ` at the cells of `G`: `|ν(F G) − ν F ν G| ≤ (μ₂ + δ) W_G θ/(θ − α) · θ^{d+1} W_F`.
Eventually along `𝒰` the box second moments at the image of `A_G` are below `μ₂ + δ`, and
`cov_spatialW` bounds the box covariance.

DERIVED: `2` the power of the moment; `1` the cap beyond `d` and the bound on `θ`; `0` the signs. -/
theorem w1Law_cov_margin {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {α : ℝ} {cd : Cl → Cl → ℕ}
    (hv : W1Law ν e α cd) {θ : ℝ} (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ) {WF WG μ2 δ : ℝ}
    (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG) (hμ0 : 0 ≤ μ2) (hδ : 0 < δ)
    (hμ2 : ∀ c ∈ AG, ν (e c * e c) ≤ μ2) (d : ℕ) (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
      ≤ (μ2 + δ) * WG * θ / (θ - α) * (θ ^ (d + 1) * WF) := by
  obtain ⟨𝒰, M, ι, R, S, σ, Cm, hU, hC, hC0, hrow, hinv, hrange, hL⟩ := hv
  haveI := hU
  have hθ0 : 0 ≤ θ := by linarith
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
  -- the box second moments at the cells of `G`
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
  filter_upwards [hrange AF AG d hsep, hmom] with j hj hmj
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
      k ∉ reach (Cm j) (AG.image (ι j)) d := by
    intro k hk
    obtain ⟨c, hc, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have hc' := Finset.mem_filter.1 hc
    rw [← hc'.2]
    exact hj c hc'.1
  have hc := cov_spatialW (hinv j) (hC j) (hC0 j) (hrow j) hα0 hαθ hθ1 f.continuous g.continuous
    hvf hvg (AG.image (ι j)) hWG0 hM0 hgB hgV hM d hfar
  refine hc.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 _))
    (div_nonneg (mul_nonneg (mul_nonneg hM0 hWG0) hθ0) (by linarith)))
  rw [Finset.sum_fiberwise AF (ι j) (fun c => |wF c|)]
  exact hWF

#print axioms w1Law_cov_margin

/-- **Covariance decay of affine cell readings under a W1 law.** Under a W1 law of class `α`,
`α < θ ≤ 1`, readings with `Σ|w_F| ≤ W_F`, `Σ|w_G| ≤ W_G`, cells more than `d` apart, and
`ν(e_c²) ≤ μ₂` at the cells of `G`: `|ν(F G) − ν F ν G| ≤ μ₂ W_G θ/(θ − α) · θ^{d+1} W_F`
(`w1Law_cov_margin` at `δ = 1/(n+1)`, and the limit). No truncation and no higher moment enters.

DERIVED: `1/(n+1)` the vanishing margin; `1` the cap beyond `d` and the bound on `θ`; `0` the signs. -/
theorem w1Law_cov {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {α : ℝ} {cd : Cl → Cl → ℕ}
    (hv : W1Law ν e α cd) {θ : ℝ} (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ) {WF WG μ2 : ℝ}
    (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG) (hμ0 : 0 ≤ μ2)
    (hμ2 : ∀ c ∈ AG, ν (e c * e c) ≤ μ2) (d : ℕ) (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
      ≤ μ2 * WG * θ / (θ - α) * (θ ^ (d + 1) * WF) := by
  have hn : ∀ n : ℕ,
      |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
        ≤ (μ2 + 1 / ((n : ℝ) + 1)) * WG * θ / (θ - α) * (θ ^ (d + 1) * WF) := fun n =>
    w1Law_cov_margin hv hα0 hαθ hθ1 AF AG wF wG bF bG hWF hWG hμ0 (by positivity) hμ2 d hsep
  have ht : Tendsto (fun n : ℕ => (μ2 + 1 / ((n : ℝ) + 1)) * WG * θ / (θ - α) * (θ ^ (d + 1) * WF))
      atTop (𝓝 ((μ2 + 0) * WG * θ / (θ - α) * (θ ^ (d + 1) * WF))) :=
    ((((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const _).mul_const
      _).div_const _).mul_const _
  have h := ge_of_tendsto' ht hn
  simpa using h

#print axioms w1Law_cov

end Law

/-! ## 2. The hypothesis and the chain to M -/

section Chain

/-- **The observer's cell-energy view is in Dobrushin's W1 class, on the readers of `S`.** For a
cell type `Cl` with a cell distance `cd` and cell energies `e k c`:

* eventually in the step `k`, the step-`k` state read through the cell-energy field has a Dobrushin
  law of W1 class `α` whose influence moves at most one unit of `cd` per step (`W1Law`);
* the reader clause of `ObserverEnergyCellM.CellViewDobrushin`: for every pair `P, Q ∈ S` there are
  bounds `W_b`, `B_b` such that at every time separation `n` the reflected reading of `P` and the
  reading of `Q` shifted by `aₘ₀ n` are, eventually in `k`, affine readings `b + Σ_{c ∈ A} w_c e_k c`
  with `Σ|w| ≤ W_b`, `|b| ≤ B_b`, and every cell of `A_P` more than `lv · n` from every cell of
  `A_Q`.

DERIVED: `2` the rank; `0` the reflection plane; `4` in `Fin 4` the spacetime dimension. -/
def CellViewW1 (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 lv : ℕ) (α : ℝ)
    (S : Set (MarginMono 2 τ r)) {Cl : Type} [DecidableEq Cl] (cd : Cl → Cl → ℕ)
    (e : ℕ → Cl → C(Cfg 2, ℝ)) : Prop :=
  (∀ᶠ k in atTop, W1Law (stateK two_ne k) (e k) α cd) ∧
  ∀ P ∈ S, ∀ Q ∈ S, ∃ Wb Bb : ℝ, ∀ n : ℕ, ∃ (AP AQ : Finset Cl) (wP wQ : Cl → ℝ) (bP bQ : ℝ),
    ∑ c ∈ AP, |wP c| ≤ Wb ∧ ∑ c ∈ AQ, |wQ c| ≤ Wb ∧ |bP| ≤ Bb ∧ |bQ| ≤ Bb ∧
    (∀ c ∈ AP, ∀ c' ∈ AQ, lv * n < cd c c') ∧
    ∀ᶠ k in atTop,
      LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1))
          = affF (e k) AP wP bP ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1))
          = affF (e k) AQ wQ bQ

/-- **The cell view in Dobrushin's W1 class gives lattice clustering at `θ^{lv}`** for every
`θ ∈ (α, 1]`, with constant `μ₂ W_b θ/(θ − α) · θ W_b`, `μ₂` the bound on the second cell moments
(`w1Law_cov` at `d = lv · n`; `latSF_pair_eq`, `prodSmear_empty`, `FlowCapstone.mono_empty`).

DERIVED: `1` the moment order `2 · 1` and the extra power of `θ`; `0` the reflection plane and the
signs. -/
theorem latClusterRateOn_of_cellViewW1 {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 lv : ℕ} {α : ℝ}
    {S : Set (MarginMono 2 τ r)} {Cl : Type} [DecidableEq Cl] {cd : Cl → Cl → ℕ}
    {e : ℕ → Cl → C(Cfg 2, ℝ)} (hV : CellViewW1 Φ τ r m0 lv α S cd e)
    (hM : CellMoments e) {θ : ℝ} (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) :
    LatClusterRateOn two_ne Φ τ r m0 (θ ^ lv) S := by
  obtain ⟨hlaw, hread⟩ := hV
  intro P hP Q hQ
  obtain ⟨Wb, Bb, h⟩ := hread P hP Q hQ
  obtain ⟨C2, hC2⟩ := hM 1
  refine ⟨max C2 0 * Wb * θ / (θ - α) * (θ * Wb), fun n => ?_⟩
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
  have hb := w1Law_cov hk hα0 hαθ hθ1 AP AQ wP wQ bP bQ hWP hWQ (le_max_right C2 0)
    (fun c _ => by
      have := h2 c
      rw [show 2 * 1 = 2 from rfl, pow_two] at this
      exact this.trans (le_max_left _ _))
    (lv * n) hsep
  refine hb.trans (le_of_eq ?_)
  rw [← pow_mul, pow_succ]
  ring

#print axioms latClusterRateOn_of_cellViewW1

/-- **M for the energy density from the cell view in Dobrushin's W1 class.** `CellViewW1` of class
`α` on a set `S ∋ ∅` with `lv ≥ 1`, uniform cell moments, any `θ ∈ (α, 1)`, and the leakage inputs
on `coarseSpan S` at time `k ≥ 1` with `ρr² < 1` and `η² < (1 − θ^{2 lv k})(1 − ρr²)` give
`FlowClusterAbs` (`latClusterRateOn_of_cellViewW1`, `ObserverEnergyMClose.energy_M_of_rate_leak`).

DERIVED: `2` the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `θ`,
`lv`, `k`, `L` and the rates. -/
theorem energy_M_of_cellViewW1 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv) {α θ : ℝ}
    {Cl : Type} [DecidableEq Cl] (cd : Cl → Cl → ℕ) (e : ℕ → Cl → C(Cfg 2, ℝ))
    (hV : CellViewW1 (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv α S cd e)
    (hM : CellMoments e) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ < 1)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ((θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hθ0 : 0 ≤ θ := by linarith
  exact energy_M_of_rate_leak hc0 hc n R D hD s hs hB τ hphys m0 S hS
    (pow_nonneg hθ0 lv) (pow_lt_one₀ hθ0 hθ1 hlv.ne')
    (latClusterRateOn_of_cellViewW1 hV hM hα0 hαθ hθ1.le) hk hρr hη hL hLw

#print axioms energy_M_of_cellViewW1

/-- **M from E and the cell view in Dobrushin's W1 class.** The cube moment bound E on a class `D`
of non-negative fields with subtraction of the order of the cell volume supplies the cell moments of
the grid of base data in `D` (`cellMoments_of_cube`); with `CellViewW1` on that grid, M follows as in
`energy_M_of_cellViewW1`.

DERIVED: `2` the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `θ`,
`lv`, `k`, `L` and the rates. -/
theorem energy_M_of_cellViewW1_cube {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv) {α θ : ℝ}
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D)
    (hV : CellViewW1 (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv α S (cellDist τ)
      (fun k => cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k))
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ < 1)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ((θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellViewW1 hc0 hc n R D hD s hs hB τ hphys m0 S hS hlv (cellDist τ) _ hV
    (cellMoments_of_cube (obsConfFlow c hc0 hc n R) D hD s hs hpos hsub hcube base hbase m0)
    hα0 hαθ hθ1 hk hρr hη hL hLw

#print axioms energy_M_of_cellViewW1_cube

/-- **The η demand at the measured W1 row `α = 0.877`.** At `θ = 88/100`, every `η` with
`η² ≤ (28/100)²` passes: `0.0784 < (1 − 0.7744) · 0.35 = 0.07896`.

DERIVED: `88/100` the rate, `877/1000 < 88/100`; `28/100` the largest `η` kept; `13/20`, `7/20` as
in `eta_of_margin`; `1` the least `lv · k`; `2` the degree. -/
theorem eta_demand_W1_877 {lv k : ℕ} (hlk : 1 ≤ lv * k) {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hη : η ^ 2 ≤ (28 / 100) ^ 2) :
    η ^ 2 < (1 - (((88 / 100 : ℝ) ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) :=
  eta_of_margin (by norm_num) (by norm_num) hlk hρr (by linarith)

#print axioms eta_demand_W1_877

/-- **The η demand at `α = 0.95`.** At `θ = 951/1000`, every `η` with `η² ≤ (18/100)²` passes:
`0.0324 < (1 − 0.904401) · 0.35 = 0.03346`.

DERIVED: `951/1000` the rate, `95/100 < 951/1000`; `18/100` the largest `η` kept; the rest as in
`eta_demand_W1_877`, `13/20` as in `eta_of_margin`. -/
theorem eta_demand_W1_95 {lv k : ℕ} (hlk : 1 ≤ lv * k) {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hη : η ^ 2 ≤ (18 / 100) ^ 2) :
    η ^ 2 < (1 - (((951 / 1000 : ℝ) ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) :=
  eta_of_margin (by norm_num) (by norm_num) hlk hρr (by linarith)

#print axioms eta_demand_W1_95

/-- **M from E and the cell view in W1 class `0.877`, at the measured leakage.** If the cell view is
in W1 class `877/1000` with `lv ≥ 1`, E holds on the class, and the leakage inputs hold at time
`k ≥ 1` with `η = 0.093` and `ρr² ≤ 13/20`, then `FlowClusterAbs` holds
(`energy_M_of_cellViewW1_cube` at `θ = 88/100`, `eta_demand_W1_877`).

DERIVED: `877/1000` the W1 row read at `1.31 r0` (extreme pair, largest level); `88/100`, `13/20`
as in `eta_demand_W1_877`; `93/1000` the leakage `η = 0.093` measured at one coarse step; `2` the
rank; `1/6` the dominance bound; `0` and `1` bracket `lv`, `k`, `L`. -/
theorem energy_M_of_cellViewW1_877 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv)
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D)
    (hV : CellViewW1 (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv (877 / 1000) S (cellDist τ)
      (fun k => cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr
      (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellViewW1_cube hc0 hc n R D hD s hs hpos hsub hcube hB τ hphys m0 S hS hlv base hbase
    hV (by norm_num) (by norm_num : (877 / 1000 : ℝ) < 88 / 100) (by norm_num) hk (by linarith)
    (eta_demand_W1_877 (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hlv.ne' hk.ne')) hρr
      (by norm_num)) hL hLw

#print axioms energy_M_of_cellViewW1_877

/-- **M from E and the cell view in W1 class `0.95`, at the measured leakage.** As
`energy_M_of_cellViewW1_877` at class `95/100` (`θ = 951/1000`, `eta_demand_W1_95`).

DERIVED: `95/100` the class; `951/1000`, `13/20` as in `eta_demand_W1_95`; `93/1000` the measured
leakage; `2` the rank; `1/6` the dominance bound; `0` and `1` bracket `lv`, `k`, `L`. -/
theorem energy_M_of_cellViewW1_95 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv)
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D)
    (hV : CellViewW1 (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv (95 / 100) S (cellDist τ)
      (fun k => cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr
      (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellViewW1_cube hc0 hc n R D hD s hs hpos hsub hcube hB τ hphys m0 S hS hlv base hbase
    hV (by norm_num) (by norm_num : (95 / 100 : ℝ) < 951 / 1000) (by norm_num) hk (by linarith)
    (eta_demand_W1_95 (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hlv.ne' hk.ne')) hρr
      (by norm_num)) hL hLw

#print axioms energy_M_of_cellViewW1_95

/-- **The reader clause is supplied on the single-cell monomials**: for a base family with a
reflection map on `I`, a W1 law of the cell grid eventually in the step gives the full `CellViewW1`
at `lv = 1` on `cellSet` (`ObserverEnergyCellM.cellView_readers`).

DERIVED: `1` the level `lv`. -/
theorem cellViewW1_of_law (Φ : Flow 2) {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4)
    (r : ℝ) (I : Set (Fin nb)) (ρ : Fin nb → Fin nb)
    (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i)) {α : ℝ}
    (hlaw : ∀ᶠ k in atTop, W1Law (stateK two_ne k) (cellE Φ base m0 k) α (cellDist τ)) :
    CellViewW1 Φ τ r m0 1 α (cellSet base m0 τ r I) (cellDist τ) (fun k => cellE Φ base m0 k) :=
  ⟨hlaw, cellView_readers Φ base m0 τ r I ρ hρ⟩

#print axioms cellViewW1_of_law

/-- **M from E and the W1 law of the cell grid at the measured row.** For the single-cell readings
of a base family in `D` with a reflection map on `I`: E on `D`, a W1 law of class `0.877` of the
step-`k` cell-energy field eventually in `k`, and the leakage inputs on `coarseSpan (cellSet …)` at
`η = 0.093`, `ρr² ≤ 13/20`, give `FlowClusterAbs` (`cellViewW1_of_law`,
`energy_M_of_cellViewW1_877` at `lv = 1`).

DERIVED: `877/1000`, `93/1000`, `13/20` as in `energy_M_of_cellViewW1_877`; `1` the level; `2` the
rank; `1/6` the dominance bound; `0` the sign of `k` and `L`. -/
theorem energy_M_of_cellLawW1_877 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D) (I : Set (Fin nb))
    (ρ : Fin nb → Fin nb) (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i))
    (hlaw : ∀ᶠ k in atTop, W1Law (stateK two_ne k)
      (cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k) (877 / 1000) (cellDist τ))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0)
      (coarseSpan (cellSet base m0 τ r I)) k ρr (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellViewW1_877 hc0 hc n R D hD s hs hpos hsub hcube hB τ hphys m0
    (cellSet base m0 τ r I) (emptyMargin_mem_cellSet base m0 τ r I) one_pos base hbase
    (cellViewW1_of_law _ base m0 τ r I ρ hρ hlaw) hk hρr hL hLw

#print axioms energy_M_of_cellLawW1_877

end Chain

/-! ## 3. Non-vacuity: the coupled pair is in W1 class `2κ` with covariance `2κ` -/

section Pair

/-- **The upper spin `1`** of the interval `[-1, 1]`.

DERIVED: `1` the spin and the level. -/
def p1 : Tsp 1 := ⟨1, by norm_num⟩

/-- **The lower spin `−1`** of the interval `[-1, 1]`.

DERIVED: `1` the spin and the level. -/
def q1 : Tsp 1 := ⟨-1, by norm_num⟩

/-- DERIVED: `0`, `1` the sign and the spin. -/
theorem p1_pos : 0 < ((p1 : Tsp 1) : ℝ) := by
  show (0 : ℝ) < 1
  norm_num

#print axioms p1_pos

/-- **The clamp at level `1` fixes the spins of `[-1, 1]`.**

DERIVED: `1` the level. -/
theorem clampL_one_tsp (y : Tsp 1) : clampL 1 (y : ℝ) = (y : ℝ) := by
  have hy := y.2
  unfold clampL
  rw [min_eq_left hy.2, max_eq_right hy.1]

#print axioms clampL_one_tsp

/-- **The pair specification has W1 influence `2κ`.** At spins `±1` the conditional probability of
the upper spin is `1/2 + κ y`; changing the other spin by `Δ` moves it by `κ |Δ|`, and a
`1`-Lipschitz test function differs by at most `2` between the spins.

DERIVED: `2κ` the influence (`pairInfl`); `1/2` the bound on `κ`; `1` the level. -/
theorem pairSpec_w1 {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    W1Infl (pairSpec κ hκ0 hκ1 p1 q1 p1_pos) (pairInfl κ) := by
  intro l k hlk W x φ _ hφL
  have hok := oth_eq l k hlk
  show |(MassGap.ObserverEnergyCellWitness.lam κ ((p1 : Tsp 1) : ℝ)
        (Function.update W k x (oth l) : ℝ)
        * φ (Function.update (Function.update W k x) l p1 l)
      + (1 - MassGap.ObserverEnergyCellWitness.lam κ ((p1 : Tsp 1) : ℝ)
        (Function.update W k x (oth l) : ℝ))
        * φ (Function.update (Function.update W k x) l q1 l))
      - (MassGap.ObserverEnergyCellWitness.lam κ ((p1 : Tsp 1) : ℝ) (W (oth l) : ℝ)
          * φ (Function.update W l p1 l)
        + (1 - MassGap.ObserverEnergyCellWitness.lam κ ((p1 : Tsp 1) : ℝ) (W (oth l) : ℝ))
          * φ (Function.update W l q1 l))| ≤ pairInfl κ l k * |(x : ℝ) - (W k : ℝ)|
  simp only [Function.update_self]
  rw [hok, Function.update_self]
  unfold pairInfl MassGap.ObserverEnergyCellWitness.lam
  rw [if_neg hlk]
  have hm : ((p1 : Tsp 1) : ℝ) = 1 := rfl
  rw [hm, clampL_one_tsp, clampL_one_tsp]
  have e : (1 / 2 + κ * (x : ℝ) / 1) * φ p1 + (1 - (1 / 2 + κ * (x : ℝ) / 1)) * φ q1
      - ((1 / 2 + κ * (W k : ℝ) / 1) * φ p1 + (1 - (1 / 2 + κ * (W k : ℝ) / 1)) * φ q1)
      = κ * ((x : ℝ) - (W k : ℝ)) * (φ p1 - φ q1) := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg hκ0]
  have hpq : |φ p1 - φ q1| ≤ 2 := by
    have := hφL p1 q1
    have e2 : |((p1 : Tsp 1) : ℝ) - ((q1 : Tsp 1) : ℝ)| = 2 := by
      show |(1 : ℝ) - (-1)| = 2
      norm_num
    rwa [e2] at this
  have hd := abs_nonneg ((x : ℝ) - (W k : ℝ))
  calc κ * |(x : ℝ) - (W k : ℝ)| * |φ p1 - φ q1| ≤ κ * |(x : ℝ) - (W k : ℝ)| * 2 :=
        mul_le_mul_of_nonneg_left hpq (mul_nonneg hκ0 hd)
    _ = 2 * κ * |(x : ℝ) - (W k : ℝ)| := by ring

#print axioms pairSpec_w1

/-- **The coupled pair satisfies the W1 law of class `2κ`.** The state `pairStateOn true false` of
the two `±1` cells, read through the real cell field, is exactly the box state `pairStateOn p1 q1`
of the pair specification at the spins `±1` of `[-1, 1]`; its W1 influence is `2κ`
(`pairSpec_w1`) with row sums `2κ`, and influence steps are one unit of `pairDist`.

DERIVED: `2κ` the class; `0`, `1` the sites and distances; `1/2` the bound on `κ`; `2` the number of
sites. -/
theorem w1Law_pair {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    W1Law (pairStateOn true false hκ0 hκ1) pairCell (2 * κ) pairDist := by
  have hq : ((q1 : Tsp 1) : ℝ) = -((p1 : Tsp 1) : ℝ) := by
    show (-1 : ℝ) = -1
    rfl
  refine ⟨atTop, fun _ => 2, fun _ c => c, fun _ => 1,
    fun _ => pairSpec κ hκ0 hκ1 p1 q1 p1_pos, fun _ => pairStateOn p1 q1 hκ0 hκ1,
    fun _ => pairInfl κ, inferInstance, fun _ => pairSpec_w1 hκ0 hκ1, fun _ l k => ?_,
    fun _ l => ?_, fun _ => invariant_pair hκ0 hκ1 p1 q1 p1_pos hq, ?_, ?_⟩
  · show 0 ≤ pairInfl κ l k
    unfold pairInfl
    split_ifs <;> linarith
  · rw [Fin.sum_univ_two]
    unfold pairInfl
    fin_cases l <;> simp
  · intro A A' d hsep
    refine Filter.Eventually.of_forall fun _ c hc hmem => ?_
    rcases A'.eq_empty_or_nonempty with h0 | ⟨c', hc'⟩
    · rw [h0, Finset.image_empty, reach_empty] at hmem
      exact Finset.notMem_empty c hmem
    · have hd : d < pairDist c c' := hsep c hc c' hc'
      have hd1 : pairDist c c' ≤ 1 := by unfold pairDist; split_ifs <;> omega
      have hd0 : d = 0 := by omega
      subst hd0
      have hmem' : c ∈ A'.image (fun c => c) := hmem
      obtain ⟨c'', hc'', hcc⟩ := Finset.mem_image.1 hmem'
      subst hcc
      have := hsep c'' hc c'' hc''
      simp [pairDist] at this
  · intro A H _
    have e : (pairStateOn true false hκ0 hκ1) (H.comp (fieldMap pairCell))
        = (pairStateOn p1 q1 hκ0 hκ1) (H.comp (pullR (R := 1) (fun c : Fin 2 => c))) := by
      show pairOn true false κ (fun U => H (fun c => pairCell c U))
        = pairOn p1 q1 κ (fun W => H (fun c => ((W c : Tsp 1) : ℝ)))
      unfold pairOn
      beta_reduce
      have h1 : (fun c => pairCell c ![true, true]) = fun c => ((![p1, p1] c : Tsp 1) : ℝ) := by
        funext c; fin_cases c <;> rfl
      have h2 : (fun c => pairCell c ![true, false]) = fun c => ((![p1, q1] c : Tsp 1) : ℝ) := by
        funext c; fin_cases c <;> rfl
      have h3 : (fun c => pairCell c ![false, true]) = fun c => ((![q1, p1] c : Tsp 1) : ℝ) := by
        funext c; fin_cases c <;> rfl
      have h4 : (fun c => pairCell c ![false, false]) = fun c => ((![q1, q1] c : Tsp 1) : ℝ) := by
        funext c; fin_cases c <;> rfl
      rw [h1, h2, h3, h4]
    show Tendsto (fun _ : ℕ => (pairStateOn p1 q1 hκ0 hκ1)
        (H.comp (pullR (R := 1) (fun c : Fin 2 => c)))) atTop
      (𝓝 ((pairStateOn true false hκ0 hκ1) (H.comp (fieldMap pairCell))))
    rw [e]
    exact tendsto_const_nhds

#print axioms w1Law_pair

/-- **At W1 class `0.877` the pair has covariance `0.877`.** At `κ = 877/2000` the coupled pair
satisfies the W1 law of class `877/1000` (the measured row of `energy_M_of_cellViewW1_877`), and the
covariance of its two cells is `877/1000`: the hypothesis leaves a non-trivial pairing at the nearest
separation.

DERIVED: `877/2000` the coupling; `877/1000 = 2 · 877/2000` the class and the covariance; `1/2` the
bound on `κ`. -/
theorem pair_w1_877 :
    W1Law (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 877 / 2000) (by norm_num)) pairCell
        (877 / 1000) pairDist ∧
      (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 877 / 2000) (by norm_num))
          (pairCell 0 * pairCell 1)
        - (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 877 / 2000) (by norm_num)) (pairCell 0)
          * (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 877 / 2000) (by norm_num))
            (pairCell 1)
        = 877 / 1000 := by
  have h := w1Law_pair (κ := 877 / 2000) (by norm_num) (by norm_num)
  have hc := pair_cov (κ := 877 / 2000) (by norm_num) (by norm_num)
  rw [show (2 : ℝ) * (877 / 2000) = 877 / 1000 by norm_num] at h hc
  exact ⟨h, hc⟩

#print axioms pair_w1_877

end Pair

/-! ## 4. The W1 class is strictly wider than the TV class -/

section Shift

/-- **The upper draw of the shift kernel**: `κ y + (1 − κ)`, clamped into `[-1, 1]`.

DERIVED: `1` the level and the noise scale `1 − κ`. -/
def shUp (κ y : ℝ) : Tsp 1 := tspin 1 (κ * y + (1 - κ))

/-- **The lower draw of the shift kernel**: `κ y − (1 − κ)`, clamped into `[-1, 1]`.

DERIVED: `1` the level and the noise scale `1 − κ`. -/
def shDn (κ y : ℝ) : Tsp 1 := tspin 1 (κ * y - (1 - κ))

/-- The clamp at level `1` fixes the points of `[-1, 1]`.

DERIVED: `1` the level. -/
theorem clampL_one_of_mem {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ 1) : clampL 1 t = t := by
  unfold clampL
  rw [abs_one, min_eq_left h1, max_eq_right h0]

#print axioms clampL_one_of_mem

/-- **The draws are unclamped on `[-1, 1]`** for `0 ≤ κ ≤ 1`.

DERIVED: `1` the level; `0` the sign of `κ`. -/
theorem sh_val {κ y : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    ((shUp κ y : Tsp 1) : ℝ) = κ * y + (1 - κ) ∧ ((shDn κ y : Tsp 1) : ℝ) = κ * y - (1 - κ) := by
  have a1 : -κ ≤ κ * y := by nlinarith
  have a2 : κ * y ≤ κ := by nlinarith
  exact ⟨clampL_one_of_mem (by linarith) (by linarith),
    clampL_one_of_mem (by linarith) (by linarith)⟩

#print axioms sh_val

/-- The spins of `[-1, 1]` lie between `−1` and `1`.

DERIVED: `1` the level. -/
theorem tsp_one_bounds (x : Tsp 1) : -1 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 := by
  have h1 := x.2.1
  have h2 := x.2.2
  have e : |(1 : ℝ)| = 1 := abs_one
  exact ⟨by linarith, by linarith⟩

#print axioms tsp_one_bounds

/-- The draw maps are continuous.

DERIVED: no numeral. -/
theorem continuous_sh (κ : ℝ) : Continuous (shUp κ) ∧ Continuous (shDn κ) :=
  ⟨(continuous_tspin 1).comp ((continuous_const.mul continuous_id).add continuous_const),
    (continuous_tspin 1).comp ((continuous_const.mul continuous_id).sub continuous_const)⟩

#print axioms continuous_sh

/-- **The shift specification** on two spins of `[-1, 1]`: the kernel at `l` sets the spin at `l` to
`κ y ± (1 − κ)` with probability `1/2` each, `y` the other spin.

DERIVED: `1/2` the fair noise; `1` the total probability. -/
def shiftSpec (κ : ℝ) : Spec (Tsp 1) (Fin 2) where
  P l f W := 1 / 2 * f (Function.update W l (shUp κ (W (oth l) : ℝ)))
    + 1 / 2 * f (Function.update W l (shDn κ (W (oth l) : ℝ)))
  cont l _ hf := by
    have hy : Continuous (fun W : Fin 2 → Tsp 1 => (W (oth l) : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply _)
    exact (continuous_const.mul (hf.comp (continuous_id.update l ((continuous_sh κ).1.comp hy)))).add
      (continuous_const.mul (hf.comp (continuous_id.update l ((continuous_sh κ).2.comp hy))))
  lin _ _ _ _ _ _ _ _ := by ring
  one _ _ := by ring
  mono l _ _ _ _ W h :=
    add_le_add (mul_le_mul_of_nonneg_left (h _) (by norm_num))
      (mul_le_mul_of_nonneg_left (h _) (by norm_num))
  upd l f W y := by
    show 1 / 2 * f (Function.update (Function.update W l y) l
          (shUp κ (Function.update W l y (oth l) : ℝ)))
        + 1 / 2 * f (Function.update (Function.update W l y) l
          (shDn κ (Function.update W l y (oth l) : ℝ)))
      = 1 / 2 * f (Function.update W l (shUp κ (W (oth l) : ℝ)))
        + 1 / 2 * f (Function.update W l (shDn κ (W (oth l) : ℝ)))
    rw [Function.update_of_ne (oth_ne l), Function.update_idem, Function.update_idem]

/-- **The influence matrix of the shift**: `κ` off the diagonal.

DERIVED: `0` the diagonal. -/
def shiftInfl (κ : ℝ) (l k : Fin 2) : ℝ := if l = k then 0 else κ

/-- **The shift specification has W1 influence `κ`**: changing the other spin by `Δ` moves both
draws by `κ Δ`, so the mean of a `1`-Lipschitz test function moves by at most `κ |Δ|`.

DERIVED: `1/2` the fair noise; `0`, `1` bracket `κ`. -/
theorem shiftSpec_w1 {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) : W1Infl (shiftSpec κ) (shiftInfl κ) := by
  intro l k hlk W x φ _ hφL
  show |(1 / 2 * φ (Function.update (Function.update W k x) l
          (shUp κ (Function.update W k x (oth l) : ℝ)) l)
        + 1 / 2 * φ (Function.update (Function.update W k x) l
          (shDn κ (Function.update W k x (oth l) : ℝ)) l))
      - (1 / 2 * φ (Function.update W l (shUp κ (W (oth l) : ℝ)) l)
        + 1 / 2 * φ (Function.update W l (shDn κ (W (oth l) : ℝ)) l))|
    ≤ shiftInfl κ l k * |(x : ℝ) - (W k : ℝ)|
  simp only [Function.update_self]
  rw [oth_eq l k hlk, Function.update_self]
  unfold shiftInfl
  rw [if_neg hlk]
  have bx := tsp_one_bounds x
  have bw := tsp_one_bounds (W k)
  have hx' := sh_val hκ0 hκ1 bx.1 bx.2
  have hw' := sh_val hκ0 hκ1 bw.1 bw.2
  have hu := hφL (shUp κ (x : ℝ)) (shUp κ (W k : ℝ))
  have hd := hφL (shDn κ (x : ℝ)) (shDn κ (W k : ℝ))
  rw [hx'.1, hw'.1] at hu
  rw [hx'.2, hw'.2] at hd
  have eu : κ * (x : ℝ) + (1 - κ) - (κ * (W k : ℝ) + (1 - κ)) = κ * ((x : ℝ) - (W k : ℝ)) := by
    ring
  have ed : κ * (x : ℝ) - (1 - κ) - (κ * (W k : ℝ) - (1 - κ)) = κ * ((x : ℝ) - (W k : ℝ)) := by
    ring
  rw [eu, abs_mul, abs_of_nonneg hκ0] at hu
  rw [ed, abs_mul, abs_of_nonneg hκ0] at hd
  rw [show 1 / 2 * φ (shUp κ (x : ℝ)) + 1 / 2 * φ (shDn κ (x : ℝ))
      - (1 / 2 * φ (shUp κ (W k : ℝ)) + 1 / 2 * φ (shDn κ (W k : ℝ)))
      = 1 / 2 * (φ (shUp κ (x : ℝ)) - φ (shUp κ (W k : ℝ)))
        + 1 / 2 * (φ (shDn κ (x : ℝ)) - φ (shDn κ (W k : ℝ))) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

#print axioms shiftSpec_w1

/-- **The W1 row sums of the shift are `κ`.**

DERIVED: `2` the number of sites. -/
theorem shiftInfl_row (κ : ℝ) (l : Fin 2) : ∑ k, shiftInfl κ l k = κ := by
  rw [Fin.sum_univ_two]
  unfold shiftInfl
  fin_cases l <;> simp

#print axioms shiftInfl_row

/-- **The separating test function**: `0` at and below `1 − 2κ`, `1` at and above `2κ − 1`, linear
between, cut to `[0, 1]`.

DERIVED: `1 − 2κ`, `2κ − 1` the two inner draws; `2 (2κ − 1)` their distance; `0`, `1` the cut. -/
def sepφ (κ : ℝ) (t : Tsp 1) : ℝ := min 1 (max 0 (((t : ℝ) - (1 - 2 * κ)) / (2 * (2 * κ - 1))))

/-- **For `κ ∈ (1/2, 1]` the shift is in no TV class below `1`**: every TV influence matrix `C` of
`shiftSpec κ` has `C 0 1 ≥ 1`. With the other spin at `1` the draws are `1` and `2κ − 1`; at `−1`
they are `1 − 2κ` and `−1`; the test function `sepφ κ` is `1` on the first pair and `0` on the
second, so the conditional mean moves by `1`.

DERIVED: `1/2` the fair noise and the lower bound on `κ`; `1` the bound and the spins; `0`, `1` the
sites. -/
theorem shiftSpec_not_tv {κ : ℝ} (hκ : 1 / 2 < κ) (hκ1 : κ ≤ 1) {C : Fin 2 → Fin 2 → ℝ}
    (hC : SInfl (shiftSpec κ) C) : 1 ≤ C 0 1 := by
  have hpos : 0 < 2 * (2 * κ - 1) := by linarith
  have hφc : Continuous (sepφ κ) :=
    continuous_const.min (continuous_const.max
      ((continuous_subtype_val.sub continuous_const).div_const _))
  have hφ0 : ∀ t, 0 ≤ sepφ κ t := fun t => le_min zero_le_one (le_max_left _ _)
  have hφ1 : ∀ t, sepφ κ t ≤ 1 := fun t => min_le_left _ _
  have hone : ∀ t : Tsp 1, 2 * (2 * κ - 1) ≤ (t : ℝ) - (1 - 2 * κ) → sepφ κ t = 1 := by
    intro t ht
    have hv : 1 ≤ ((t : ℝ) - (1 - 2 * κ)) / (2 * (2 * κ - 1)) := by
      rw [le_div_iff₀ hpos]; linarith
    unfold sepφ
    rw [max_eq_right (by linarith), min_eq_left hv]
  have hzero : ∀ t : Tsp 1, (t : ℝ) - (1 - 2 * κ) ≤ 0 → sepφ κ t = 0 := by
    intro t ht
    have hv : ((t : ℝ) - (1 - 2 * κ)) / (2 * (2 * κ - 1)) ≤ 0 := by
      rw [div_le_iff₀ hpos]; linarith
    unfold sepφ
    rw [max_eq_left hv, min_eq_right zero_le_one]
  have hκ0 : 0 ≤ κ := by linarith
  have h := hC 0 1 (by decide) (fun _ => q1) p1 (sepφ κ) hφc hφ0 hφ1
  have e1 : (shiftSpec κ).P 0 (fun V => sepφ κ (V 0)) (Function.update (fun _ => q1) 1 p1)
      = 1 / 2 * sepφ κ (shUp κ 1) + 1 / 2 * sepφ κ (shDn κ 1) := rfl
  have e2 : (shiftSpec κ).P 0 (fun V => sepφ κ (V 0)) (fun _ => q1)
      = 1 / 2 * sepφ κ (shUp κ (-1)) + 1 / 2 * sepφ κ (shDn κ (-1)) := rfl
  rw [e1, e2] at h
  have v1 := sh_val (y := 1) hκ0 hκ1 (by norm_num) le_rfl
  have v2 := sh_val (y := -1) hκ0 hκ1 le_rfl (by norm_num)
  rw [hone _ (by rw [v1.1]; linarith), hone _ (by rw [v1.2]; linarith),
    hzero _ (by rw [v2.1]; linarith), hzero _ (by rw [v2.2]; linarith)] at h
  norm_num at h
  exact h

#print axioms shiftSpec_not_tv

/-- **At `κ = 0.877` the shift is in W1 class `0.877` and in no TV class below `1`.** Its W1 row
sums are `877/1000` (the measured cell-energy row), while every TV influence matrix of it has the
entry `C 0 1 ≥ 1`: a W1 class below `1` does not give a TV class below `1`.

DERIVED: `877/1000` the measured W1 row; `1/2` the threshold of the separation; `1` the TV bound. -/
theorem shift_877 :
    W1Infl (shiftSpec (877 / 1000)) (shiftInfl (877 / 1000)) ∧
      (∀ l, ∑ k, shiftInfl (877 / 1000) l k = 877 / 1000) ∧
      ∀ C : Fin 2 → Fin 2 → ℝ, SInfl (shiftSpec (877 / 1000)) C → 1 ≤ C 0 1 :=
  ⟨shiftSpec_w1 (by norm_num) (by norm_num), shiftInfl_row _,
    fun _ hC => shiftSpec_not_tv (by norm_num) (by norm_num) hC⟩

#print axioms shift_877

end Shift

end MassGap.ObserverEnergyCellW1
