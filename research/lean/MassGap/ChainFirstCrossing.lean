import Mathlib
import MassGap.ChainCoarseSeed

/-!
# MassGap.ChainFirstCrossing — the defect comparison on the anti-diagonal of the first crossing

`ChainCoarseSeed` reduces the seed to a comparison between the Wilson torus and the coarse tori of the
flat Migdal–Kadanoff chain `W ↦ N[(W⁴)^{*4}]`. This module fixes the plaquette convention of that comparison
and restricts it to the steps the seed reads.

## The convention

The tree's torus has a plaquette for every ordered pair of directions, the diagonal included
(`TorusDoubling.TPlaq`). `thol_swap`: the swapped pair carries the inverse holonomy; `thol_diag`: a diagonal
pair carries `1`. So for a density with `φ(g⁻¹) = φ(g)` the action is a constant plus twice the sum over
unordered pairs (`fAct_uniformField_pairs`): each plaquette of the torus is counted twice.

The chain's `W_k` is a weight per plaquette: `convT` is the `SU(2)` class convolution, and the power `4` and
the fourfold convolution are those of one Migdal–Kadanoff step on a lattice with one weight per plaquette.
The field that puts `W` on each plaquette of the tree's torus is therefore `halfField W τ = −½ log W(τ ·)`
(`fAct_halfField_suTau`), and the Wilson torus at the tree's coupling `β` is the chain started at `2β`
(`defectW_eq_halfZero`). With the field `−log W` (`ChainCoarseSeed.chainField`) the torus carries `W²` per
plaquette, the step `W ↦ (W⁴)^{*4}` is not the decimation of that lattice, and the 2D step is not an identity.

## The comparison the seed reads

* `HalfStep C i j`: the defect of the side-`2^{j+1}` torus with weight `W_i` is at most that of the side-`2ʲ`
  torus with weight `W_{i+1}`, both with one weight per plaquette.
* `CrossingComparison C k`: `HalfStep C i (k − i)` for every `i < k`, the anti-diagonal that carries the
  Wilson torus at side `2^{k+1}` to the coarse torus at side `2` with weight `W_k`
  (`defectW_le_of_crossing`).
* `FirstCrossingComparison C`: `CrossingComparison C k` at the first `k` whose coarse defect
  (`coarseDefect C k`, side `2`, weight `W_k`) is at most `1/1000`.

`half_coarse_defect_le` bounds the coarse defect by `2ᵈ d² nᵈ π²/(8c)`. `firstCrossing_of_halfOneStep`:
the comparison for every `i, j` implies the first-crossing comparison. `coarseDefect_zero`: at `k = 0` the coarse defect is the Wilson
defect at side `2`, so a first crossing at `0` is the seed at side `2` itself.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ChainFirstCrossing

open MeasureTheory Set Real Filter MassGap.TorusDoubling MassGap.HolderBondMoving
  MassGap.CompactGauge MassGap.ConvolutionTransfer MassGap.ChainCoarseSeed

/-! ## 1. Each plaquette of the tree's torus is counted twice -/

section Convention

variable {G : Type} [Group G] {d n : ℕ}

/-- **The swapped pair carries the inverse holonomy.** -/
theorem thol_swap (i j : Fin d) (x : TSite d n) (U : TLink d n → G) :
    thol ((j, i), x) U = (thol ((i, j), x) U)⁻¹ := by
  simp only [thol]
  group

/-- **A diagonal pair carries `1`.** -/
theorem thol_diag (i : Fin d) (x : TSite d n) (U : TLink d n → G) : thol ((i, i), x) U = 1 := by
  simp only [thol]
  group

/-- A symmetric function on ordered pairs: the diagonal plus twice the pairs `i < j`. DERIVED: `2` the two
orders of an unordered pair. -/
theorem sum_pairs_of_symm (f : Fin d × Fin d → ℝ) (hf : ∀ i j, f (j, i) = f (i, j)) :
    ∑ p : Fin d × Fin d, f p
      = ∑ i, f (i, i) + 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), f p := by
  have h3 : ∀ p : Fin d × Fin d, f p = (if p.1 < p.2 then f p else 0)
      + (if p.2 < p.1 then f p else 0) + (if p.1 = p.2 then f p else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  rw [Finset.sum_congr rfl (fun p _ => h3 p), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hswap : ∑ p : Fin d × Fin d, (if p.2 < p.1 then f p else 0)
      = ∑ p : Fin d × Fin d, (if p.1 < p.2 then f p else 0) := by
    rw [← Equiv.sum_comp (Equiv.prodComm (Fin d) (Fin d))]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨i, j⟩ := p
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hf i j]
  have hdiag : ∑ p : Fin d × Fin d, (if p.1 = p.2 then f p else 0) = ∑ i, f (i, i) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq Finset.univ i (fun j => f (i, j))]
    simp
  rw [hswap, hdiag, Finset.sum_filter]
  ring

/-- **The action of an inverse-symmetric density counts each plaquette twice.** For `φ(g⁻¹) = φ(g)`,
`fAct (uniformField φ) U = d nᵈ φ(1) + 2 Σₓ Σ_{i<j} φ(hol)`. DERIVED: `d nᵈ` the diagonal pairs; `2` the
two orders of a plaquette. -/
theorem fAct_uniformField_pairs {φ : G → ℝ} (hφ : ∀ g, φ g⁻¹ = φ g) (U : TLink d n → G) :
    fAct (uniformField (d := d) (n := n) φ) U
      = (d * n ^ d : ℕ) * φ 1 + 2 * ∑ x : TSite d n,
          ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2), φ (thol (p, x) U) := by
  unfold fAct uniformField
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hx : ∀ x : TSite d n, ∑ p : Fin d × Fin d, φ (thol (p, x) U)
      = d * φ 1 + 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
          φ (thol (p, x) U) := by
    intro x
    rw [sum_pairs_of_symm (fun p => φ (thol (p, x) U)) (fun i j => by
      show φ (thol ((j, i), x) U) = φ (thol ((i, j), x) U)
      rw [thol_swap i j x U, hφ])]
    simp only [thol_diag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ]
  simp only [TSite, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum]
  ring

end Convention

/-! ## 2. The half field -/

section Half

variable {G : Type} [Group G] [MeasurableSpace G] {d n : ℕ}

/-- **The half field** `g ↦ −½ log W(τ g)`: on the tree's torus it puts the weight `W` on each plaquette
(`fAct_halfField_suTau`). DERIVED: `½` because the tree counts each plaquette twice. -/
noncomputable def halfField (W : ℝ → ℝ) (τ : G → ℝ) (g : G) : ℝ := chainField W τ g / 2

/-- `½ Re tr` is inverse invariant. -/
theorem suTau_inv (g : SUN.SU 2) : suTau g⁻¹ = suTau g := by
  unfold suTau
  rw [MassGap.RectWilson.wilsonDensity_inv]

/-- **The half field carries `W` on each plaquette.** On the tree's `SU(2)` torus,
`fAct (uniformField (halfField W suTau)) U = 4 n⁴ · halfField W suTau 1 + Σₓ Σ_{i<j} −log W(½ Re tr hol)`, so
`e^{−fAct}` is a constant times `∏_{plaquettes} W(½ Re tr hol)`. -/
theorem fAct_halfField_suTau (W : ℝ → ℝ) (U : TLink 4 n → SUN.SU 2) :
    fAct (uniformField (d := 4) (n := n) (halfField W suTau)) U
      = (4 * n ^ 4 : ℕ) * halfField W suTau 1 + ∑ x : TSite 4 n,
          ∑ p ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2),
            chainField W suTau (thol (p, x) U) := by
  rw [fAct_uniformField_pairs (fun g => by simp only [halfField, chainField, suTau_inv]) U,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold halfField
  ring

variable {W W' : ℝ → ℝ} {c : ℝ} {τ : G → ℝ}

omit [Group G] [MeasurableSpace G] in
theorem halfField_ge (hW : FlatAdmissible W W' c) (hc : 0 < c) (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1)
    (g : G) : -Real.log (W 1) / 2 ≤ halfField W τ g := by
  unfold halfField
  linarith [chainField_ge hW hc hτ g]

omit [Group G] [MeasurableSpace G] in
/-- The half field oscillates by at most `π²/8c`. DERIVED: half of `π²/4c`;
`8 = 2 · 4`, the half of the `4` in `chainField_le`. -/
theorem halfField_le (hW : FlatAdmissible W W' c) (hc : 0 < c) (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1)
    (g : G) : halfField W τ g ≤ -Real.log (W 1) / 2 + π ^ 2 / (8 * c) := by
  unfold halfField
  have h := chainField_le hW hc hτ g
  have e : π ^ 2 / (8 * c) = π ^ 2 / (4 * c) / 2 := by
    field_simp
    ring
  rw [e]
  linarith

omit [Group G] in
theorem measurable_halfField (hW : FlatAdmissible W W' c) (hτm : Measurable τ) :
    Measurable (halfField W τ) :=
  (measurable_chainField hW hτm).div_const 2

variable [MeasurableMul₂ G] [MeasurableInv G]

/-- **The coarse defect of an admissible weight, one weight per plaquette.** On the side-`n` torus in
dimension `d`, `|fieldDefect| ≤ 2ᵈ d² nᵈ π²/(8c)`. -/
theorem half_coarse_defect_le (μ : Measure G) [IsProbabilityMeasure μ]
    (hW : FlatAdmissible W W' c) (hc : 0 < c) (hτm : Measurable τ)
    (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    |fieldDefect d (halfField W τ) n μ| ≤ 2 ^ d * (d * d * n ^ d : ℕ) * (π ^ 2 / (8 * c)) := by
  have h := abs_fieldDefect_le (d := d) μ (measurable_halfField hW hτm) (halfField_ge hW hc hτ)
    (halfField_le hW hc hτ) n
  have e : -Real.log (W 1) / 2 + π ^ 2 / (8 * c) - -Real.log (W 1) / 2 = π ^ 2 / (8 * c) := by ring
  rwa [e] at h

end Half

/-! ## 3. The comparison on the anti-diagonal -/

section Wilson

/-- **The Wilson defect is the half-field defect of the chain started at twice the coupling**, at every
side: `−½ log e^{2β τ} = β wilsonDensity − β`, and a constant shift does not move the defect. -/
theorem defectW_eq_halfZero {β : ℝ} (C : WilsonChain (2 * β)) (n : ℕ) :
    ZoomSelfScale.defectW 2 β n
      = fieldDefect 4 (halfField (C.W 0) suTau) n (probHaar (SUN.SU 2)) := by
  have hfield : halfField (C.W 0) suTau = fun g => β * WilsonAction.wilsonDensity g + (-β) := by
    funext g
    simp only [halfField, chainField, C.hW0, Real.log_exp, suTau]
    ring
  rw [hfield, fieldDefect_add_const (d := 4) (φ := fun g => β * WilsonAction.wilsonDensity g)
    (probHaar (SUN.SU 2)) (measurable_const.mul WilsonAction.measurable_wilsonDensity)
    (fun g => (abs_le.mp (abs_beta_wilsonDensity_le β g)).1)
    (fun g => (abs_le.mp (abs_beta_wilsonDensity_le β g)).2) (-β) n,
    ← defectWG_four_eq, defectWG_eq_fieldDefect]

/-- The coarse defect at step `k`: the side-`2` torus with weight `W_k` on each plaquette. -/
noncomputable def coarseDefect {β : ℝ} (C : WilsonChain β) (k : ℕ) : ℝ :=
  fieldDefect 4 (halfField (C.W k) suTau) 2 (probHaar (SUN.SU 2))

/-- **At `k = 0` the coarse defect is the Wilson defect at side `2`.** -/
theorem coarseDefect_zero {β : ℝ} (C : WilsonChain (2 * β)) :
    coarseDefect C 0 = ZoomSelfScale.defectW 2 β 2 :=
  (defectW_eq_halfZero C 2).symm

/-- **One step, one weight per plaquette**: the side-`2^{j+1}` torus with weight `W_i` has defect at most
that of the side-`2ʲ` torus with weight `W_{i+1}`. -/
def HalfStep {β : ℝ} (C : WilsonChain β) (i j : ℕ) : Prop :=
  fieldDefect 4 (halfField (C.W i) suTau) (2 ^ (j + 1)) (probHaar (SUN.SU 2))
    ≤ fieldDefect 4 (halfField (C.W (i + 1)) suTau) (2 ^ j) (probHaar (SUN.SU 2))

/-- The step comparison at every `i` and `j`. -/
def HalfOneStep {β : ℝ} (C : WilsonChain β) : Prop := ∀ i j : ℕ, HalfStep C i j

/-- **The anti-diagonal ending at `k`**: `HalfStep C i (k − i)` for every `i < k`, the steps from the
Wilson torus at side `2^{k+1}` to the coarse torus at side `2` with weight `W_k`. -/
def CrossingComparison {β : ℝ} (C : WilsonChain β) (k : ℕ) : Prop :=
  ∀ i < k, HalfStep C i (k - i)

/-- **The comparison at the first crossing**: at the first `k` with coarse defect at most `1/1000`, the
anti-diagonal ending at `k` holds. DERIVED: `1/1000` the doubling-defect seed. -/
def FirstCrossingComparison {β : ℝ} (C : WilsonChain β) : Prop :=
  ∀ k : ℕ, coarseDefect C k ≤ 1 / 1000 → (∀ i < k, 1 / 1000 < coarseDefect C i) →
    CrossingComparison C k

/-- **The anti-diagonal telescopes**: it carries the side-`2^{k+1}` defect with weight `W_0` to the
coarse defect at `k`. -/
theorem defect_le_of_crossing {β : ℝ} (C : WilsonChain β) {k : ℕ} (h : CrossingComparison C k) :
    fieldDefect 4 (halfField (C.W 0) suTau) (2 ^ (k + 1)) (probHaar (SUN.SU 2))
      ≤ coarseDefect C k := by
  have key : ∀ i, i ≤ k → fieldDefect 4 (halfField (C.W 0) suTau) (2 ^ (k + 1))
      (probHaar (SUN.SU 2))
      ≤ fieldDefect 4 (halfField (C.W i) suTau) (2 ^ (k + 1 - i)) (probHaar (SUN.SU 2)) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      refine (ih (by omega)).trans ?_
      have e1 : k + 1 - i = (k - i) + 1 := by omega
      have e2 : k + 1 - (i + 1) = k - i := by omega
      rw [e1, e2]
      exact h i (by omega)
  have := key k le_rfl
  rwa [show k + 1 - k = 1 by omega, pow_one] at this

/-- **The Wilson defect at side `2^{k+1}` is at most the coarse defect at `k`**, on the anti-diagonal. -/
theorem defectW_le_of_crossing {β : ℝ} (C : WilsonChain (2 * β)) {k : ℕ}
    (h : CrossingComparison C k) : ZoomSelfScale.defectW 2 β (2 ^ (k + 1)) ≤ coarseDefect C k := by
  rw [defectW_eq_halfZero C]
  exact defect_le_of_crossing C h

/-- The comparison at every step gives it at the first crossing. -/
theorem firstCrossing_of_halfOneStep {β : ℝ} {C : WilsonChain β} (h : HalfOneStep C) :
    FirstCrossingComparison C :=
  fun k _ _ i _ => h i (k - i)

end Wilson

end MassGap.ChainFirstCrossing

#print axioms MassGap.ChainFirstCrossing.thol_swap
#print axioms MassGap.ChainFirstCrossing.sum_pairs_of_symm
#print axioms MassGap.ChainFirstCrossing.fAct_uniformField_pairs
#print axioms MassGap.ChainFirstCrossing.fAct_halfField_suTau
#print axioms MassGap.ChainFirstCrossing.half_coarse_defect_le
#print axioms MassGap.ChainFirstCrossing.defectW_eq_halfZero
#print axioms MassGap.ChainFirstCrossing.coarseDefect_zero
#print axioms MassGap.ChainFirstCrossing.defect_le_of_crossing
#print axioms MassGap.ChainFirstCrossing.defectW_le_of_crossing
#print axioms MassGap.ChainFirstCrossing.firstCrossing_of_halfOneStep
