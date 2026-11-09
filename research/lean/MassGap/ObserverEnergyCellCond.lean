import Mathlib
import MassGap.ObserverEnergyCellW1
import MassGap.Beacon

noncomputable section

/-!
# MassGap.ObserverEnergyCellCond — the W1 law of the cell field from its own conditional laws

`ObserverEnergyCellW1.W1Law` is existential: box states `σ_j`, specifications `S_j`, influence
matrices, cell maps and a limit. This module fixes every one of them canonically and leaves one
statement about the cell field's own conditional laws.

1. **Conditional kernels with a W1 row** (`W1Kernel`, `W1Kernel.P`, `W1Kernel.lipLe_P`,
   `continuous_of_lipLe`, `W1Kernel.continuous_P`, `W1Kernel.spec`, `W1Kernel.w1Infl`): a family of
   probability laws `κ l W` on the spin interval, one per site, not reading the spin at `l`, with
   `|∫ φ dκ_l(W with x at k) − ∫ φ dκ_l(W)| ≤ C l k · |x − W k|` for every `1`-Lipschitz `φ`. Its
   kernels form a `DobrushinUnbounded.Spec` with W1 influence `C`. The Feller clause of `Spec` is
   not assumed: the W1 row makes `P_l` map Lipschitz observables to Lipschitz observables, those are
   dense (`DobrushinW1.lipSub`, Stone–Weierstrass), and a uniform limit of continuous functions is
   continuous.
2. **The canonical box** (`Window`, `Window.cellOf`, `Window.idx`, `Window.bnd`, `Window.boxMap`,
   `Window.boxLaw`, `Window.boxLaw_read`): for an exhaustion of the cells by finite windows `Λ_j`,
   `σ_j` is the joint law under `ν` of the cell energies of `Λ_j`, on the interval
   `[-Σ_{c ∈ Λ_j} ‖e_c‖, Σ_{c ∈ Λ_j} ‖e_c‖]` that holds them. A reading of the cells of `A` has the
   same value under `σ_j` and `ν` once `A ⊆ Λ_j`, so the limit clause of `W1Law` holds exactly.
3. **The range from the zero pattern** (`Window.reach_cd`, `Window.range_clause`): if `C l k ≠ 0`
   only for cells at most one unit of `cd` apart, the `d`-step influence neighbourhood of `A'` stays
   within `cd`-distance `d` of `A'`.
4. **The row and the reduction** (`RowAt`, `CondW1Row`, `w1Law_of_rows`, `w1Law_of_condW1Row`):
   `CondW1Row ν e Λ α cd` says that eventually in `j` the law `σ_j` has conditional kernels of the
   kind of 1 (an `Invariant` family: `σ_j` disintegrates along them, which is what makes them its
   conditional laws), with row sums `≤ α` and zero influence beyond one unit of `cd`. It implies
   `W1Law ν e α cd`.
5. **The chain to M** (`cellWin`, `cellDist_self`, `cellDist_le`, `energy_M_of_condW1Row`): on the
   observer's cell grid with the windows `cellWin`, `CondW1Row` of class `0.95` eventually in the
   step, E, and the leakage inputs at `η = 0.093` give `FlowClusterAbs`.

## Scope

`CondW1Row` is a hypothesis. It asks for a version of each conditional law that is W1-Lipschitz in
every other cell energy with the stated constants; regular conditional laws exist on these finite
products of intervals, and the content of the hypothesis is the Lipschitz bound and its row sum.
-/

namespace MassGap.ObserverEnergyCellCond

open MeasureTheory Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap MassGap.ObserverEnergyMClose MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyCellM
open MassGap.ObserverEnergyCellW1 (W1Law pullR fieldMap cellViewW1_of_law
  energy_M_of_cellViewW1_95)
open MassGap.DobrushinUnbounded (Spec Invariant Tsp clampL tspin continuous_tspin)
open MassGap.DobrushinW1 (LipLe W1Infl abs_sub_le_lip_finset lipSub lipSub_separatesPoints)
open MassGap.BoxDobrushinCoupling (oscStep)
open MassGap.BoxDobrushinSpatial (reach oscStep_nonneg)

/-! ## 1. Conditional kernels with a W1 row -/

section Kernel

variable {R : ℝ}

/-- The clamp fixes the points of its interval.

DERIVED: no numeral. -/
theorem clampL_of_abs_le {L t : ℝ} (h : |t| ≤ |L|) : clampL L t = t := by
  unfold clampL
  rw [min_eq_left (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

#print axioms clampL_of_abs_le

/-- **A continuous function of the spin is integrable** under a finite law on the interval.

DERIVED: no numeral. -/
theorem integrable_tsp {φ : Tsp R → ℝ} (hφ : Continuous φ) (μ : Measure (Tsp R))
    [IsFiniteMeasure μ] : Integrable φ μ :=
  BoundedContinuousFunction.integrable μ (BoundedContinuousFunction.mkOfCompact ⟨φ, hφ⟩)

#print axioms integrable_tsp

/-- **Two functions within `c` everywhere have means within `c`** under a probability law.

DERIVED: `1` the total mass. -/
theorem abs_integral_sub_le {φ ψ : Tsp R → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (μ : Measure (Tsp R)) [IsProbabilityMeasure μ] {c : ℝ} (h : ∀ g, |φ g - ψ g| ≤ c) :
    |∫ g, φ g ∂μ - ∫ g, ψ g ∂μ| ≤ c := by
  rw [← integral_sub (integrable_tsp hφ μ) (integrable_tsp hψ μ)]
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := fun g => φ g - ψ g) (C := c)
    (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact h g)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at hb

#print axioms abs_integral_sub_le

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **Conditional kernels with a W1 row.** For each site `l` and configuration `W`, a probability
law `κ l W` of the spin at `l`, not reading the spin at `l`, such that changing the spin at `k ≠ l`
from `W k` to `x` moves the mean of every continuous `1`-Lipschitz `φ` by at most
`C l k · |x − W k|`: the W1 distance of the two conditional laws, by Kantorovich–Rubinstein duality.
For laws on the line that distance is `∫ |F₁(t) − F₂(t)| dt`, the integrated CDF difference.

DERIVED: `1` the Lipschitz constant of the test functions; `0` the sign of `C`. -/
structure W1Kernel (R : ℝ) (Lk : Type) [DecidableEq Lk] where
  /-- The conditional law of the spin at `l` given the configuration `W`. -/
  κ : Lk → (Lk → Tsp R) → Measure (Tsp R)
  /-- Each conditional law is a probability law. DERIVED: no numeral. -/
  prob : ∀ l W, IsProbabilityMeasure (κ l W)
  /-- The law at `l` does not read the spin at `l`. DERIVED: no numeral. -/
  others : ∀ l (W : Lk → Tsp R) (x : Tsp R), κ l (Function.update W l x) = κ l W
  /-- The W1 influence matrix. -/
  C : Lk → Lk → ℝ
  /-- DERIVED: `0` the sign. -/
  C0 : ∀ l k, 0 ≤ C l k
  /-- The W1 bound. DERIVED: `1` the Lipschitz constant of the test functions. -/
  w1 : ∀ l k, l ≠ k → ∀ (W : Lk → Tsp R) (x : Tsp R) (φ : Tsp R → ℝ), Continuous φ →
    (∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)|) →
    |∫ g, φ g ∂(κ l (Function.update W k x)) - ∫ g, φ g ∂(κ l W)|
      ≤ C l k * |(x : ℝ) - (W k : ℝ)|

namespace W1Kernel

/-- **The kernel at `l`**: `f ↦ ∫ f(W with g at l) dκ_l(W)(g)`.

DERIVED: no numeral. -/
def P (K : W1Kernel R Lk) (l : Lk) (f : (Lk → Tsp R) → ℝ) (W : Lk → Tsp R) : ℝ :=
  ∫ g, f (Function.update W l g) ∂(K.κ l W)

omit [Fintype Lk] in
/-- **The W1 bound for an `a`-Lipschitz test function**: `≤ C l k · a · |x − W k|`.

DERIVED: `0` the case `a = 0`; `1` the rescaled Lipschitz constant. -/
theorem w1_scaled (K : W1Kernel R Lk) {l k : Lk} (hlk : l ≠ k) (W : Lk → Tsp R) (x : Tsp R)
    {ψ : Tsp R → ℝ} (hψ : Continuous ψ) {a : ℝ} (ha : 0 ≤ a)
    (hL : ∀ g g' : Tsp R, |ψ g - ψ g'| ≤ a * |(g : ℝ) - (g' : ℝ)|) :
    |∫ g, ψ g ∂(K.κ l (Function.update W k x)) - ∫ g, ψ g ∂(K.κ l W)|
      ≤ K.C l k * a * |(x : ℝ) - (W k : ℝ)| := by
  haveI := K.prob l (Function.update W k x)
  haveI := K.prob l W
  have hd0 : 0 ≤ |(x : ℝ) - (W k : ℝ)| := abs_nonneg _
  rcases ha.eq_or_lt with h0 | hpos
  · have hc : ∀ g, ψ g = ψ (W l) := fun g => by
      have h := hL g (W l)
      rw [← h0, zero_mul] at h
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
    have e : ∀ μ : Measure (Tsp R), IsProbabilityMeasure μ → ∫ g, ψ g ∂μ = ψ (W l) := by
      intro μ _
      rw [integral_congr_ae (ae_of_all _ hc), integral_const, probReal_univ, one_smul]
    rw [e _ inferInstance, e _ inferInstance, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (K.C0 l k) ha) hd0
  · have hφc : Continuous (fun g => ψ g / a) := hψ.div_const a
    have hφL : ∀ g g' : Tsp R, |ψ g / a - ψ g' / a| ≤ |(g : ℝ) - (g' : ℝ)| := fun g g' => by
      rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, mul_comm]
      exact hL g g'
    have h := K.w1 l k hlk W x _ hφc hφL
    have e : ∀ μ : Measure (Tsp R), ∫ g, ψ g ∂μ = a * ∫ g, ψ g / a ∂μ := by
      intro μ
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      show ψ g = a * (ψ g / a)
      field_simp
    rw [e, e, ← mul_sub, abs_mul, abs_of_pos hpos]
    calc a * |∫ g, ψ g / a ∂(K.κ l (Function.update W k x)) - ∫ g, ψ g / a ∂(K.κ l W)|
        ≤ a * (K.C l k * |(x : ℝ) - (W k : ℝ)|) := mul_le_mul_of_nonneg_left h hpos.le
      _ = K.C l k * a * |(x : ℝ) - (W k : ℝ)| := by ring

#print axioms w1_scaled

/-- **The kernel step on Lipschitz vectors.** For a continuous `f` with Lipschitz vector `v`, the
kernel at `l` has Lipschitz vector `oscStep C l v` (`v_k + C l k v_l` off `l`, `0` at `l`): on the
fibre `f` moves by `≤ v_k |Δ|`, and the fibre function is `v_l`-Lipschitz, so its mean moves by
`≤ C l k v_l |Δ|` (`w1_scaled`).

DERIVED: `0` the entry at `l`. -/
theorem lipLe_P (K : W1Kernel R Lk) {f : (Lk → Tsp R) → ℝ} (hf : Continuous f) {v : Lk → ℝ}
    (hv : LipLe f v) (l : Lk) : LipLe (K.P l f) (oscStep K.C l v) := by
  refine ⟨oscStep_nonneg K.C0 hv.1 l, fun W k x => ?_⟩
  unfold oscStep
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, zero_mul]
    unfold P
    simp only [Function.update_idem, K.others, sub_self, abs_zero, le_refl]
  rw [if_neg hkl]
  have hlk : l ≠ k := Ne.symm hkl
  haveI := K.prob l (Function.update W k x)
  haveI := K.prob l W
  have hu : ∀ W' : Lk → Tsp R, Continuous (fun g : Tsp R => Function.update W' l g) :=
    fun W' => continuous_const.update l continuous_id
  have hψc : Continuous (fun g => f (Function.update W l g)) := hf.comp (hu W)
  have hfx : Continuous (fun g => f (Function.update (Function.update W k x) l g)) :=
    hf.comp (hu _)
  have s1 : |K.P l f (Function.update W k x)
      - ∫ g, f (Function.update W l g) ∂(K.κ l (Function.update W k x))|
      ≤ v k * |(x : ℝ) - (W k : ℝ)| := by
    unfold P
    refine abs_integral_sub_le hfx hψc _ fun g => ?_
    show |f (Function.update (Function.update W k x) l g) - f (Function.update W l g)| ≤ _
    rw [Function.update_comm hkl x g W]
    have h := hv.2 (Function.update W l g) k x
    rwa [Function.update_of_ne hkl] at h
  have s2 : |∫ g, f (Function.update W l g) ∂(K.κ l (Function.update W k x)) - K.P l f W|
      ≤ K.C l k * v l * |(x : ℝ) - (W k : ℝ)| :=
    K.w1_scaled hlk W x hψc (hv.1 l) fun g g' => hv.fibre W l g g'
  calc |K.P l f (Function.update W k x) - K.P l f W|
      ≤ |K.P l f (Function.update W k x)
          - ∫ g, f (Function.update W l g) ∂(K.κ l (Function.update W k x))|
        + |∫ g, f (Function.update W l g) ∂(K.κ l (Function.update W k x)) - K.P l f W| :=
        abs_sub_le _ _ _
    _ ≤ v k * |(x : ℝ) - (W k : ℝ)| + K.C l k * v l * |(x : ℝ) - (W k : ℝ)| := add_le_add s1 s2
    _ = (v k + K.C l k * v l) * |(x : ℝ) - (W k : ℝ)| := by ring

#print axioms lipLe_P

end W1Kernel

/-- **An observable with a Lipschitz vector is continuous**: `|F W' − F W| ≤ Σ_k u_k |W'_k − W_k|`
(`DobrushinW1.abs_sub_le_lip_finset`), and the bound is continuous and vanishes at `W`.

DERIVED: `0` the limit of the bound. -/
theorem continuous_of_lipLe {F : (Lk → Tsp R) → ℝ} {u : Lk → ℝ} (hu : LipLe F u) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro W
  have hb : ∀ W', |F W' - F W| ≤ ∑ k, u k * |(W' k : ℝ) - (W k : ℝ)| := fun W' => by
    have h := abs_sub_le_lip_finset hu W W' Finset.univ
    simp only [Finset.mem_univ, if_true] at h
    rw [abs_sub_comm]
    exact h
  have hg : Continuous (fun W' : Lk → Tsp R => ∑ k, u k * |(W' k : ℝ) - (W k : ℝ)|) :=
    continuous_finsetSum _ fun k _ => continuous_const.mul
      ((continuous_subtype_val.comp (continuous_apply k)).sub continuous_const).abs
  have ht : Tendsto (fun W' : Lk → Tsp R => ∑ k, u k * |(W' k : ℝ) - (W k : ℝ)|) (𝓝 W) (𝓝 0) := by
    have h := hg.tendsto W
    simpa using h
  show Tendsto F (𝓝 W) (𝓝 (F W))
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun W' => by rw [Real.dist_eq]; exact hb W') ht

#print axioms continuous_of_lipLe

namespace W1Kernel

/-- **The Feller property from the W1 row.** For continuous `f` the kernel `P_l f` is continuous:
`f` is a uniform limit of observables with Lipschitz vectors (`lipSub` is dense by
Stone–Weierstrass, `lipSub_separatesPoints`), the kernel of each is continuous (`lipLe_P`,
`continuous_of_lipLe`), and the kernel moves uniform distances by at most themselves.

DERIVED: `2` halves the tolerance. -/
theorem continuous_P (K : W1Kernel R Lk) (l : Lk) {f : (Lk → Tsp R) → ℝ} (hf : Continuous f) :
    Continuous (K.P l f) := by
  have hcl : (lipSub (R := R) (Lk := Lk)).topologicalClosure = ⊤ :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ lipSub_separatesPoints
  have hmem : (⟨f, hf⟩ : C(Lk → Tsp R, ℝ))
      ∈ closure ((lipSub (R := R) (Lk := Lk) : Subalgebra ℝ C(Lk → Tsp R, ℝ)) :
        Set C(Lk → Tsp R, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, hcl]
    trivial
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hmem (ε / 2) (half_pos hε)
  obtain ⟨v, hv⟩ := hg
  refine ⟨K.P l g, continuous_of_lipLe (K.lipLe_P g.continuous hv l), fun W => hεu ?_⟩
  haveI := K.prob l W
  rw [Real.dist_eq]
  have hcu : Continuous (fun y : Tsp R => Function.update W l y) :=
    continuous_const.update l continuous_id
  have h := abs_integral_sub_le (hf.comp hcu) (g.continuous.comp hcu) (K.κ l W)
    (c := dist (⟨f, hf⟩ : C(Lk → Tsp R, ℝ)) g) fun y => by
      rw [← Real.dist_eq]
      exact ContinuousMap.dist_apply_le_dist (f := (⟨f, hf⟩ : C(Lk → Tsp R, ℝ))) (g := g)
        (Function.update W l y)
  exact lt_of_le_of_lt h (lt_of_lt_of_le hfg (by linarith))

#print axioms continuous_P

/-- **The specification of the kernels**: Feller (`continuous_P`), linear and monotone (the
integral), unital (probability laws), not reading the spin at `l` (`others`).

DERIVED: `1` the total mass. -/
def spec (K : W1Kernel R Lk) : Spec (Tsp R) Lk where
  P := K.P
  cont := fun l {_f} hf => K.continuous_P l hf
  lin := fun l {f f'} hf hf' a b W => by
    haveI := K.prob l W
    have hcu : Continuous (fun y : Tsp R => Function.update W l y) :=
      continuous_const.update l continuous_id
    have h1 : Integrable (fun g => f (Function.update W l g)) (K.κ l W) :=
      integrable_tsp (hf.comp hcu) (K.κ l W)
    have h2 : Integrable (fun g => f' (Function.update W l g)) (K.κ l W) :=
      integrable_tsp (hf'.comp hcu) (K.κ l W)
    show ∫ g, (a * f (Function.update W l g) + b * f' (Function.update W l g)) ∂(K.κ l W)
      = a * ∫ g, f (Function.update W l g) ∂(K.κ l W)
        + b * ∫ g, f' (Function.update W l g) ∂(K.κ l W)
    rw [integral_add (h1.const_mul a) (h2.const_mul b), integral_const_mul, integral_const_mul]
  one l W := by
    haveI := K.prob l W
    show ∫ _g, (1 : ℝ) ∂(K.κ l W) = 1
    rw [integral_const, probReal_univ, one_smul]
  mono := fun l {f f'} hf hf' W h => by
    haveI := K.prob l W
    have hcu : Continuous (fun y : Tsp R => Function.update W l y) :=
      continuous_const.update l continuous_id
    exact integral_mono (integrable_tsp (hf.comp hcu) (K.κ l W))
      (integrable_tsp (hf'.comp hcu) (K.κ l W)) fun g => h g
  upd l f W x := by
    show ∫ g, f (Function.update (Function.update W l x) l g) ∂(K.κ l (Function.update W l x))
      = ∫ g, f (Function.update W l g) ∂(K.κ l W)
    simp only [Function.update_idem, K.others]

/-- **The kernels have W1 influence `C`.**

DERIVED: no numeral. -/
theorem w1Infl (K : W1Kernel R Lk) : W1Infl K.spec K.C := by
  intro l k hlk W x φ hφ hφL
  show |∫ g, φ (Function.update (Function.update W k x) l g l) ∂(K.κ l (Function.update W k x))
      - ∫ g, φ (Function.update W l g l) ∂(K.κ l W)| ≤ _
  simp only [Function.update_self]
  exact K.w1 l k hlk W x φ hφ hφL

#print axioms w1Infl

end W1Kernel

end Kernel

/-! ## 1b. The CDF form of the W1 row -/

section Cdf

variable {R : ℝ}

/-- **The CDF of a law on the spin interval**: `F(t) = μ{g ≤ t}`.

DERIVED: no numeral. -/
def cdfT (μ : Measure (Tsp R)) (t : ℝ) : ℝ := μ.real {g : Tsp R | (g : ℝ) ≤ t}

/-- The CDF is monotone.

DERIVED: no numeral. -/
theorem cdfT_mono (μ : Measure (Tsp R)) [IsFiniteMeasure μ] : Monotone (cdfT μ) :=
  fun s t hst => measureReal_mono fun g (hg : (g : ℝ) ≤ s) => show (g : ℝ) ≤ t from hg.trans hst

#print axioms cdfT_mono

/-- The clamp is `1`-Lipschitz.

DERIVED: `0` the distance of the level to itself. -/
theorem abs_clampL_sub_le (L x y : ℝ) : |clampL L x - clampL L y| ≤ |x - y| := by
  unfold clampL
  rw [max_comm (-|L|) (min x |L|), max_comm (-|L|) (min y |L|)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h := abs_min_sub_min_le_max x |L| y |L|
  rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h

#print axioms abs_clampL_sub_le

/-- **A test function of the spin, extended to the line** through the clamp.

DERIVED: no numeral. -/
def extT (φ : Tsp R → ℝ) (x : ℝ) : ℝ := φ (tspin R x)

/-- The extension agrees with the test function on the interval.

DERIVED: no numeral. -/
theorem extT_tsp (φ : Tsp R → ℝ) (g : Tsp R) : extT φ (g : ℝ) = φ g := by
  unfold extT
  congr 1
  exact Subtype.ext (clampL_of_abs_le (abs_le.2 ⟨g.2.1, g.2.2⟩))

#print axioms extT_tsp

/-- The extension of a `1`-Lipschitz test function is `1`-Lipschitz on the line.

DERIVED: `1` the constant. -/
theorem lip_extT {φ : Tsp R → ℝ} (hL : ∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)|) :
    LipschitzWith 1 (extT φ) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact (hL _ _).trans (abs_clampL_sub_le R x y)

#print axioms lip_extT

/-- Its derivative is at most `1` in absolute value wherever it is taken.

DERIVED: `1` the constant. -/
theorem abs_deriv_extT_le {φ : Tsp R → ℝ}
    (hL : ∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)|) (t : ℝ) :
    |deriv (extT φ) t| ≤ 1 := by
  have h := norm_deriv_le_of_lipschitz (x₀ := t) (lip_extT hL)
  rwa [Real.norm_eq_abs, NNReal.coe_one] at h

#print axioms abs_deriv_extT_le

/-- **The layer representation**: on the interval,
`ψ(x) = ψ(−|R|) + ∫_{(−|R|, |R|]} 1{t < x} ψ'(t) dt`
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, the extension being Lipschitz).

DERIVED: no numeral. -/
theorem extT_eq_integral {φ : Tsp R → ℝ}
    (hL : ∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)|) {x : ℝ}
    (hx : x ∈ Set.Icc (-|R|) |R|) :
    extT φ x = extT φ (-|R|)
      + ∫ t in Set.Ioc (-|R|) |R|, (Set.Iio x).indicator (deriv (extT φ)) t := by
  rw [setIntegral_indicator measurableSet_Iio]
  have e : Set.Ioc (-|R|) |R| ∩ Set.Iio x = Set.Ioo (-|R|) x := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.le.trans hx.2⟩, h3⟩
  rw [e, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.1,
    (lip_extT hL).lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
  ring

#print axioms extT_eq_integral

/-- **The W1 bound from the CDF difference**: for probability laws on the interval and a
`1`-Lipschitz `φ`, `|∫ φ dμ − ∫ φ dν| ≤ ∫_{−|R|}^{|R|} |F_μ(t) − F_ν(t)| dt`. Each mean is
`ψ(−|R|) + ∫ (1 − F(t)) ψ'(t) dt` (`extT_eq_integral` and Fubini), and `|ψ'| ≤ 1`.

DERIVED: `1` the bound on the derivative and the total mass. -/
theorem abs_integral_sub_le_cdf (μ ν : Measure (Tsp R)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {φ : Tsp R → ℝ}
    (hL : ∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)|) :
    |∫ g, φ g ∂μ - ∫ g, φ g ∂ν| ≤ ∫ t in (-|R|)..|R|, |cdfT μ t - cdfT ν t| := by
  have hab : -|R| ≤ |R| := by linarith [abs_nonneg R]
  have hd1 : ∀ t, |deriv (extT φ) t| ≤ 1 := abs_deriv_extT_le hL
  have hdm : Measurable (deriv (extT φ)) := measurable_deriv _
  have hF : ∀ (g : Tsp R) (t : ℝ), (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t
      = if t < (g : ℝ) then deriv (extT φ) t else 0 := fun g t => by
    simp only [Set.indicator_apply, Set.mem_Iio]
  have hFm : Measurable (Function.uncurry
      fun (g : Tsp R) (t : ℝ) => (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t) := by
    have e : (Function.uncurry
        fun (g : Tsp R) (t : ℝ) => (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t)
        = fun p : Tsp R × ℝ => if p.2 < (p.1 : ℝ) then deriv (extT φ) p.2 else 0 := by
      funext p
      exact hF p.1 p.2
    rw [e]
    exact Measurable.ite
      (measurableSet_lt measurable_snd (measurable_subtype_coe.comp measurable_fst))
      (hdm.comp measurable_snd) measurable_const
  have hFb : ∀ (g : Tsp R) (t : ℝ), |(Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t| ≤ 1 :=
    fun g t => by
      rw [hF]
      split_ifs
      · exact hd1 t
      · simp
  have hcm : ∀ m : Measure (Tsp R), IsProbabilityMeasure m → Measurable (cdfT m) :=
    fun m _ => (cdfT_mono m).measurable
  have hcb : ∀ m : Measure (Tsp R), IsProbabilityMeasure m → ∀ t,
      0 ≤ cdfT m t ∧ cdfT m t ≤ 1 := fun m _ t => ⟨measureReal_nonneg, measureReal_le_one⟩
  have key : ∀ m : Measure (Tsp R), IsProbabilityMeasure m →
      ∫ g, φ g ∂m = extT φ (-|R|)
        + ∫ t in Set.Ioc (-|R|) |R|, (1 - cdfT m t) * deriv (extT φ) t := by
    intro m hm
    have hint : Integrable (Function.uncurry
        fun (g : Tsp R) (t : ℝ) => (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t)
        (m.prod (volume.restrict (Set.Ioc (-|R|) |R|))) :=
      Integrable.of_bound hFm.aestronglyMeasurable 1
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hFb p.1 p.2)
    have h1 : ∀ g : Tsp R, φ g = extT φ (-|R|)
        + ∫ t in Set.Ioc (-|R|) |R|, (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t :=
      fun g => by
        rw [← extT_tsp φ g]
        exact extT_eq_integral hL ⟨g.2.1, g.2.2⟩
    have h2 : ∀ t, ∫ g, (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t ∂m
        = (1 - cdfT m t) * deriv (extT φ) t := fun t => by
      have e : (fun g : Tsp R => (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t)
          = ({g : Tsp R | t < (g : ℝ)}).indicator (fun _ => deriv (extT φ) t) := by
        funext g
        simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_setOf_eq]
      rw [e, integral_indicator_const _ (measurableSet_lt measurable_const measurable_subtype_coe),
        smul_eq_mul]
      congr 1
      have ec : {g : Tsp R | t < (g : ℝ)} = {g : Tsp R | (g : ℝ) ≤ t}ᶜ := by
        ext g
        simp [not_le]
      rw [ec, probReal_compl_eq_one_sub (measurableSet_le measurable_subtype_coe measurable_const)]
      rfl
    calc ∫ g, φ g ∂m
        = ∫ g, (extT φ (-|R|)
            + ∫ t in Set.Ioc (-|R|) |R|, (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t) ∂m :=
          integral_congr_ae (ae_of_all _ h1)
      _ = extT φ (-|R|) + ∫ g, (∫ t in Set.Ioc (-|R|) |R|,
            (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t) ∂m := by
          have hI : Integrable (fun g : Tsp R => ∫ t in Set.Ioc (-|R|) |R|,
              (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t) m := hint.integral_prod_left
          rw [integral_add (integrable_const _) hI, integral_const,
            probReal_univ, one_smul]
      _ = extT φ (-|R|) + ∫ t in Set.Ioc (-|R|) |R|, ∫ g,
            (Set.Iio (g : ℝ)).indicator (deriv (extT φ)) t ∂m := by
          rw [integral_integral_swap hint]
      _ = extT φ (-|R|) + ∫ t in Set.Ioc (-|R|) |R|, (1 - cdfT m t) * deriv (extT φ) t := by
          simp only [h2]
  have hGi : ∀ m : Measure (Tsp R), IsProbabilityMeasure m →
      Integrable (fun t => (1 - cdfT m t) * deriv (extT φ) t)
        (volume.restrict (Set.Ioc (-|R|) |R|)) := fun m hm =>
    Integrable.of_bound (((measurable_const.sub (hcm m hm)).mul hdm).aestronglyMeasurable) 1
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_mul]
        have hc := hcb m hm t
        have h' : |1 - cdfT m t| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
        calc |1 - cdfT m t| * |deriv (extT φ) t| ≤ 1 * 1 :=
              mul_le_mul h' (hd1 t) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1)
  have hbi : Integrable (fun t => |cdfT μ t - cdfT ν t|)
      (volume.restrict (Set.Ioc (-|R|) |R|)) :=
    Integrable.of_bound
      ((continuous_abs.measurable.comp ((hcm μ inferInstance).sub
        (hcm ν inferInstance))).aestronglyMeasurable) 1
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_abs]
        have h1 := hcb μ inferInstance t
        have h2 := hcb ν inferInstance t
        exact abs_le.2 ⟨by linarith, by linarith⟩)
  rw [key μ inferInstance, key ν inferInstance, add_sub_add_left_eq_sub,
    ← integral_sub (hGi μ inferInstance) (hGi ν inferInstance),
    intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hbi (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs,
    show (1 - cdfT μ t) * deriv (extT φ) t - (1 - cdfT ν t) * deriv (extT φ) t
      = (cdfT ν t - cdfT μ t) * deriv (extT φ) t by ring, abs_mul, abs_sub_comm (cdfT ν t)]
  calc |cdfT μ t - cdfT ν t| * |deriv (extT φ) t| ≤ |cdfT μ t - cdfT ν t| * 1 :=
        mul_le_mul_of_nonneg_left (hd1 t) (abs_nonneg _)
    _ = |cdfT μ t - cdfT ν t| := mul_one _

#print axioms abs_integral_sub_le_cdf

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **Conditional kernels with a W1 row in CDF form**, the form the measurement reads: changing the
energy of cell `k ≠ l` from `W k` to `x` moves the conditional CDF of cell `l` by at most
`C l k · |x − W k|` in `L¹(dt)`: `∫ |F_l(t | W with x at k) − F_l(t | W)| dt ≤ C l k |x − W k|`.
The measured `∫ |∂F_l(t | ω)/∂ω_k| dt`, bounded along the segment from `W k` to `x`, bounds this
difference quotient.

DERIVED: `0` the sign of `C`. -/
structure CdfKernel (R : ℝ) (Lk : Type) [DecidableEq Lk] where
  /-- The conditional law of the spin at `l` given the configuration `W`. -/
  κ : Lk → (Lk → Tsp R) → Measure (Tsp R)
  /-- Each conditional law is a probability law. DERIVED: no numeral. -/
  prob : ∀ l W, IsProbabilityMeasure (κ l W)
  /-- The law at `l` does not read the spin at `l`. DERIVED: no numeral. -/
  others : ∀ l (W : Lk → Tsp R) (x : Tsp R), κ l (Function.update W l x) = κ l W
  /-- The influence matrix. -/
  C : Lk → Lk → ℝ
  /-- DERIVED: `0` the sign. -/
  C0 : ∀ l k, 0 ≤ C l k
  /-- The CDF bound. DERIVED: no numeral. -/
  cdf : ∀ l k, l ≠ k → ∀ (W : Lk → Tsp R) (x : Tsp R),
    ∫ t in (-|R|)..|R|, |cdfT (κ l (Function.update W k x)) t - cdfT (κ l W) t|
      ≤ C l k * |(x : ℝ) - (W k : ℝ)|

/-- **A CDF kernel is a W1 kernel** (`abs_integral_sub_le_cdf`).

DERIVED: no numeral. -/
def CdfKernel.toW1 (K : CdfKernel R Lk) : W1Kernel R Lk where
  κ := K.κ
  prob := K.prob
  others := K.others
  C := K.C
  C0 := K.C0
  w1 l k hlk W x φ _ hL := by
    haveI := K.prob l (Function.update W k x)
    haveI := K.prob l W
    exact (abs_integral_sub_le_cdf _ _ hL).trans (K.cdf l k hlk W x)

end Cdf

/-! ## 2. The canonical box -/

section Box

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **An exhaustion of the cells by finite windows**: each window is non-empty, and every cell lies
in the window eventually.

DERIVED: no numeral. -/
structure Window (Cl : Type) where
  /-- The window of index `j`. -/
  Λ : ℕ → Finset Cl
  /-- DERIVED: no numeral. -/
  ne : ∀ j, (Λ j).Nonempty
  /-- DERIVED: no numeral. -/
  ev : ∀ c, ∀ᶠ j in atTop, c ∈ Λ j

namespace Window

variable (Wn : Window Cl)

/-- The number of cells of the window `j`.

DERIVED: no numeral. -/
abbrev M (j : ℕ) : ℕ := (Wn.Λ j).card

/-- **The cell of a box site.**

DERIVED: no numeral. -/
def cellOf (j : ℕ) (m : Fin (Wn.M j)) : Cl := ((Wn.Λ j).equivFin.symm m).1

/-- **The box site of a cell**: its index in the window, and the index of a fixed cell of the window
for cells outside it.

DERIVED: no numeral. -/
def idx (j : ℕ) (c : Cl) : Fin (Wn.M j) :=
  if h : c ∈ Wn.Λ j then (Wn.Λ j).equivFin ⟨c, h⟩
  else (Wn.Λ j).equivFin ⟨(Wn.ne j).choose, (Wn.ne j).choose_spec⟩

/-- DERIVED: no numeral. -/
theorem cellOf_idx {j : ℕ} {c : Cl} (h : c ∈ Wn.Λ j) : Wn.cellOf j (Wn.idx j c) = c := by
  unfold cellOf idx
  rw [dif_pos h, Equiv.symm_apply_apply]

#print axioms cellOf_idx

/-- **The interval of the window**: the sum of the sup norms of its cell energies.

DERIVED: no numeral. -/
def bnd (e : Cl → C(X, ℝ)) (j : ℕ) : ℝ := ∑ c ∈ Wn.Λ j, ‖e c‖

omit [DecidableEq Cl] in
/-- Every cell energy of the window lies in its interval.

DERIVED: `0` the sign of the norms. -/
theorem abs_le_bnd (e : Cl → C(X, ℝ)) {j : ℕ} {c : Cl} (h : c ∈ Wn.Λ j) (U : X) :
    |e c U| ≤ |Wn.bnd e j| := by
  have h1 : |e c U| ≤ ‖e c‖ := by rw [← Real.norm_eq_abs]; exact (e c).norm_coe_le_norm U
  have h2 : ‖e c‖ ≤ Wn.bnd e j :=
    Finset.single_le_sum (f := fun c => ‖e c‖) (fun c _ => norm_nonneg _) h
  exact h1.trans (h2.trans (le_abs_self _))

#print axioms abs_le_bnd

/-- **The cell energies of the window as a box configuration.**

DERIVED: no numeral. -/
def boxMap (e : Cl → C(X, ℝ)) (j : ℕ) : C(X, Fin (Wn.M j) → Tsp (Wn.bnd e j)) :=
  ⟨fun U m => tspin (Wn.bnd e j) (e (Wn.cellOf j m) U),
    continuous_pi fun m => (continuous_tspin _).comp (e (Wn.cellOf j m)).continuous⟩

/-- **The box law `σ_j`**: the joint law under `ν` of the cell energies of the window `j`
(`Beacon.pushState`).

DERIVED: no numeral. -/
def boxLaw (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (j : ℕ) :
    DLRLimit.State (Fin (Wn.M j) → Tsp (Wn.bnd e j)) :=
  MassGap.Beacon.pushState (Wn.boxMap e j) ν

end Window

namespace Window

variable (Wn : Window Cl)

/-- **A reading of the cells of `A` has the same value under `σ_j` and `ν`** once `A` lies in the
window: the box configuration is the cell configuration on the window, unclamped.

DERIVED: no numeral. -/
theorem boxLaw_read (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (A : Finset Cl)
    (H : C(Cl → ℝ, ℝ)) (hH : ∀ y y' : Cl → ℝ, (∀ c ∈ A, y c = y' c) → H y = H y') {j : ℕ}
    (hA : A ⊆ Wn.Λ j) :
    Wn.boxLaw ν e j (H.comp (pullR (Wn.idx j))) = ν (H.comp (fieldMap e)) := by
  show ν ((H.comp (pullR (Wn.idx j))).comp (Wn.boxMap e j)) = ν (H.comp (fieldMap e))
  congr 1
  ext U
  show H (fun c => clampL (Wn.bnd e j) (e (Wn.cellOf j (Wn.idx j c)) U)) = H (fun c => e c U)
  refine hH _ _ fun c hc => ?_
  show clampL (Wn.bnd e j) (e (Wn.cellOf j (Wn.idx j c)) U) = e c U
  rw [Wn.cellOf_idx (hA hc)]
  exact clampL_of_abs_le (Wn.abs_le_bnd e (hA hc) U)

#print axioms boxLaw_read

/-- **Influence moving one unit of `cd` per step stays within `cd`-distance `n` in `n` steps.** If
`C l k ≠ 0` only for cells at most `1` apart, every site of the `n`-step neighbourhood of the image of
`A' ⊆ Λ_j` has its cell within `n` of a cell of `A'`.

DERIVED: `0` the distance of a cell to itself; `1` the step. -/
theorem reach_cd {j : ℕ} {C : Fin (Wn.M j) → Fin (Wn.M j) → ℝ} {cd : Cl → Cl → ℕ}
    (hcd0 : ∀ c, cd c c = 0) (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c)
    (hz : ∀ l k, C l k ≠ 0 → cd (Wn.cellOf j l) (Wn.cellOf j k) ≤ 1)
    {A' : Finset Cl} (hA' : A' ⊆ Wn.Λ j) :
    ∀ n, ∀ l ∈ reach C (A'.image (Wn.idx j)) n, ∃ c' ∈ A', cd (Wn.cellOf j l) c' ≤ n := by
  intro n
  induction n with
  | zero =>
    intro l hl
    change l ∈ A'.image (Wn.idx j) at hl
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hl
    exact ⟨c', hc', by rw [Wn.cellOf_idx (hA' hc'), hcd0]⟩
  | succ n ih =>
    intro l hl
    simp only [reach, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases hl with h | ⟨k, hk, hCk⟩
    · obtain ⟨c', hc', hd⟩ := ih l h
      exact ⟨c', hc', by omega⟩
    · obtain ⟨c', hc', hd⟩ := ih k hk
      have h1 := hz l k hCk
      have h2 := hcd (Wn.cellOf j l) (Wn.cellOf j k) c'
      exact ⟨c', hc', by omega⟩

#print axioms reach_cd

/-- **The range clause of `W1Law` from the zero pattern**: with influence only between cells at most
one unit of `cd` apart at every `j`, cells of `A` more than `d` from every cell of `A'` lie,
eventually, outside the `d`-step neighbourhood of the image of `A'`.

DERIVED: `1` the step. -/
theorem range_clause {cd : Cl → Cl → ℕ} (hcd0 : ∀ c, cd c c = 0)
    (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c)
    (Cm : (j : ℕ) → Fin (Wn.M j) → Fin (Wn.M j) → ℝ)
    (hz : ∀ j l k, Cm j l k ≠ 0 → cd (Wn.cellOf j l) (Wn.cellOf j k) ≤ 1)
    (A A' : Finset Cl) (d : ℕ) (hsep : ∀ c ∈ A, ∀ c' ∈ A', d < cd c c') :
    ∀ᶠ j in atTop, ∀ c ∈ A, Wn.idx j c ∉ reach (Cm j) (A'.image (Wn.idx j)) d := by
  filter_upwards [(eventually_all_finset A).2 fun c _ => Wn.ev c,
    (eventually_all_finset A').2 fun c _ => Wn.ev c] with j hA hA'
  intro c hc hmem
  obtain ⟨c', hc', hd⟩ := Wn.reach_cd hcd0 hcd (hz j) hA' d _ hmem
  rw [Wn.cellOf_idx (hA c hc)] at hd
  have := hsep c hc c' hc'
  omega

#print axioms range_clause

/-- **The windows from index `j₀` on.**

DERIVED: no numeral. -/
def shift (j0 : ℕ) : Window Cl :=
  ⟨fun j => Wn.Λ (j + j0), fun _ => Wn.ne _, fun c => (tendsto_add_atTop_nat j0).eventually (Wn.ev c)⟩

end Window

end Box

/-! ## 3. The row and the reduction -/

section Row

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **The conditional W1 row at window `j`.** The box law `σ_j` of the window's cell energies has
conditional kernels with a W1 row (`W1Kernel`): `σ_j` is invariant under them (it disintegrates
along them, so they are its own conditional laws), every row sum `Σ_k C l k` is at most `α`, and the
law of cell `l` reads no cell more than one unit of `cd` away (`C l k = 0` there).

DERIVED: `1` the range. -/
def RowAt (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (Wn : Window Cl) (α : ℝ)
    (cd : Cl → Cl → ℕ) (j : ℕ) : Prop :=
  ∃ K : CdfKernel (Wn.bnd e j) (Fin (Wn.M j)),
    Invariant K.toW1.spec (Wn.boxLaw ν e j) ∧ (∀ l, ∑ k, K.C l k ≤ α) ∧
    ∀ l k, K.C l k ≠ 0 → cd (Wn.cellOf j l) (Wn.cellOf j k) ≤ 1

/-- **The conditional W1 row of the cell field**: `RowAt` eventually in the window.

DERIVED: no numeral. -/
def CondW1Row (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (Wn : Window Cl) (α : ℝ)
    (cd : Cl → Cl → ℕ) : Prop :=
  ∀ᶠ j in atTop, RowAt ν e Wn α cd j

/-- **The W1 law from the row at every window**: `σ_j` the box laws, `S_j` the kernels'
specifications, `ι_j` the window indices; the limit clause holds exactly once the cells lie in the
window (`boxLaw_read`) and the range clause follows from the zero pattern (`range_clause`).

DERIVED: no numeral. -/
theorem w1Law_of_rows {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {Wn : Window Cl} {α : ℝ}
    {cd : Cl → Cl → ℕ} (hcd0 : ∀ c, cd c c = 0) (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c)
    (h : ∀ j, RowAt ν e Wn α cd j) : W1Law ν e α cd := by
  choose K hinv hrow hz using h
  refine ⟨atTop, Wn.M, Wn.idx, Wn.bnd e, fun j => (K j).toW1.spec, Wn.boxLaw ν e,
    fun j => (K j).C, inferInstance, fun j => (K j).toW1.w1Infl, fun j => (K j).C0, hrow, hinv,
    fun A A' d hsep => Wn.range_clause hcd0 hcd (fun j => (K j).C) hz A A' d hsep, ?_⟩
  intro A H hH
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset A).2 fun c _ => Wn.ev c] with j hj
  exact (Wn.boxLaw_read ν e A H hH hj).symm

#print axioms w1Law_of_rows

/-- **The W1 law of the cell field from its conditional W1 row**: `CondW1Row ν e Λ α cd` gives
`W1Law ν e α cd` (`w1Law_of_rows` on the windows from the index where the row starts).

DERIVED: no numeral. -/
theorem w1Law_of_condW1Row {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {Wn : Window Cl} {α : ℝ}
    {cd : Cl → Cl → ℕ} (hcd0 : ∀ c, cd c c = 0) (hcd : ∀ a b c, cd a c ≤ cd a b + cd b c)
    (h : CondW1Row ν e Wn α cd) : W1Law ν e α cd := by
  obtain ⟨j0, hj0⟩ := eventually_atTop.1 h
  exact w1Law_of_rows (Wn := Wn.shift j0) hcd0 hcd fun j => hj0 (j + j0) (Nat.le_add_left _ _)

#print axioms w1Law_of_condW1Row

end Row

/-! ## 4. The chain to M on the observer's cell grid -/

section Chain

/-- **The cubic windows of the cell grid**: every base index and the sites with coordinates in
`[-j, j]`.

DERIVED: `0` the base index and site of the first cell. -/
def cellWin (nb : ℕ) (hnb : 0 < nb) : Window (Cell nb) where
  Λ j := Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(j : ℤ)) j)
  ne j := ⟨(⟨0, hnb⟩, 0), by simp⟩
  ev c := by
    refine eventually_atTop.2 ⟨∑ i, (c.2 i).natAbs, fun j hj => ?_⟩
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_Icc]
    intro i
    have h1 : (c.2 i).natAbs ≤ ∑ i, (c.2 i).natAbs :=
      Finset.single_le_sum (f := fun i => (c.2 i).natAbs) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : |c.2 i| ≤ (j : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1.trans hj
    exact abs_le.1 h2

/-- DERIVED: `0` the distance of a cell to itself. -/
theorem cellDist_self (τ : Fin 4) {nb : ℕ} (c : Cell nb) : cellDist τ c c = 0 := by
  simp [cellDist]

#print axioms cellDist_self

/-- The time separation of cells obeys the triangle inequality.

DERIVED: no numeral. -/
theorem cellDist_le (τ : Fin 4) {nb : ℕ} (a b c : Cell nb) :
    cellDist τ a c ≤ cellDist τ a b + cellDist τ b c := by
  unfold cellDist
  have e : a.2 τ - c.2 τ = (a.2 τ - b.2 τ) + (b.2 τ - c.2 τ) := by ring
  rw [e]
  exact Int.natAbs_add_le _ _

#print axioms cellDist_le

/-- **M from E and the conditional W1 row of the cell field at class `0.95`.** For the single-cell
readings of a base family in `D` with a reflection map on `I`, windows `Λ` of the cell grid: E on
`D`, `CondW1Row` of class `95/100` in the time separation of the step-`k` cell energies eventually
in `k`, and the leakage inputs on `coarseSpan (cellSet …)` at `η = 0.093`, `ρr² ≤ 13/20`, give
`FlowClusterAbs` (`w1Law_of_condW1Row`, `cellViewW1_of_law`, `energy_M_of_cellViewW1_95` at
`lv = 1`).

DERIVED: `95/100` the class; `93/1000` the measured leakage; `13/20` as in `eta_demand_W1_95`; `1`
the level; `2` the rank; `1/6` the dominance bound; `0` the sign of `k` and `L`. -/
theorem energy_M_of_condW1Row {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
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
    (Wn : Window (Cell nb))
    (hrow : ∀ᶠ k in atTop, CondW1Row (stateK two_ne k)
      (cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k) Wn (95 / 100) (cellDist τ))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0)
      (coarseSpan (cellSet base m0 τ r I)) k ρr (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellViewW1_95 hc0 hc n R D hD s hs hpos hsub hcube hB τ hphys m0
    (cellSet base m0 τ r I) (emptyMargin_mem_cellSet base m0 τ r I) one_pos base hbase
    (cellViewW1_of_law _ base m0 τ r I ρ hρ
      (hrow.mono fun _ h => w1Law_of_condW1Row (cellDist_self τ) (cellDist_le τ) h))
    hk hρr hL hLw

#print axioms energy_M_of_condW1Row

end Chain

end MassGap.ObserverEnergyCellCond
