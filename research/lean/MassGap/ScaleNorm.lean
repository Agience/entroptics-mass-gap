import Mathlib
import MassGap.FloorFold

/-!
# MassGap.ScaleNorm — the smeared field's two-cell-volume factor `a⁸`, computed from the smearing

`FloorFold.PhysBand` takes a scale `s_k` as data, read as the composites' normalisation `a_k⁸`. This module
computes the smeared field's two-cell-volume factor `a⁸`, the value `FloorFold` reads as `s_k` for the
composites, from the definition of the smeared field, and shows that `PhysBand` needs no scale as data.
Declarations are in the namespace `MassGap.ScaleNorm`.

## 1. The covariance of a state is bilinear (proved)

`stateCov ν u v = ν(uv) − ν(u)ν(v)` is linear in each slot over finite sums (`stateCov_sum_left`,
`stateCov_sum_right`).

## 2. The exact normalisation of a smeared two-point read (proved)

`smear a F f = Σ_x a⁴ f(a x) τ_x F` (`ContinuumField.smear`). For linear maps `L₁`, `L₂` on observables
(a reflection, a translation by the physical gap, the identity) and every state `ν`:

`read_eq_scale`: `Cov_ν(L₁ smear(a,F,f), L₂ smear(a,F,g)) = a⁸ · bracket`, with
`bracket = Σ_{x,y} f(a x) g(a y) Cov_ν(L₁ τ_x F, L₂ τ_y F)`, the sums over the boxes that carry the supports.

The factor is exactly `a⁸ = a⁴ · a⁴`, one cell volume per smeared field. `reflRead_eq_scale` is the case the
composites read: `θ = ireflObs τ 0` on the left, the translation by the lattice vector `v` (the physical
separation `a v`) on the right, so `bracket = Σ_{x,y} f(a x) g(a y) Cov_ν(θ τ_x F, τ_{y+v} F)`.
`physBounds_iff` turns the two bounds of a band at `s = a⁸` into bounds on the bracket: `c a⁸ ≤ read ↔ c ≤ bracket`,
`read ≤ C a⁸ ↔ bracket ≤ C`.

## 3. `PhysBand` needs no scale (proved)

`physBand_iff_ratio`: a positive scale `s` with `PhysBand N βs s m₁ m₂ c C w` exists if and only if, eventually,
the gaps are `w 2^k` apart, the far read is positive and `c · gE(m₁) ≤ C · gE(m₂)`. The scale is supplied by a
lemma, `physScale` (`s_k = gE(m₂ k)/c` where that is positive). `slope_of_ratio` is `FloorFold.slope_of_physBand`
with the scale removed: only the ratio `C/c` of the two reads enters the slope.

## What does not follow, plainly

* `PhysBand` reads `gE` (`BandClose.gE`), the centred tensor read; it is not a smeared read. The `a⁸` of
  `read_eq_scale` is the two cell volumes of the smearing; it says nothing about the size of `gE`. On `gE`
  the scale cancels identically (`physBand_iff_ratio`), so no value of `s` is load-bearing there, and the
  statement "a read at fixed physical gap has size `a_k⁸`" is not a statement about `gE` that anything uses.
* On a smeared read, `s = a⁸` is exact, so the band is the pair of bounds `c ≤ bracket ≤ C` uniformly in `k`.
  Neither is proved here. The bracket has `(2⌈R/a⌉+1)⁸` terms; `norm_smear_le` bounds the read by a constant,
  hence the bracket by a constant times `a⁻⁸` only. A uniform ceiling needs the lattice covariance at
  separation of order `1/a` to be of order `a⁸` (the dimension of the composite), and a uniform floor needs it
  bounded below by the same order; that is the open content, unchanged.

DERIVED (module-wide): `4` the spacetime dimension, the cell-volume exponent; `8 = 4 + 4` the two cell volumes of a
pair; `0` the reflection plane and the signs; `1` the fallback scale where the far read is not positive.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ScaleNorm

open Filter
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField
open MassGap.DLRLimit (State)
open MassGap.FocusZoom (stateCov)
open MassGap.BandClose (gE)

/-! ## 1. Bilinearity of the covariance -/

section Bilinear

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A state carries a finite sum to the sum of its values. DERIVED: `0` the empty sum. -/
theorem state_sum (ν : State X) {ι : Type*} (s : Finset ι) (h : ι → C(X, ℝ)) :
    ν (∑ i ∈ s, h i) = ∑ i ∈ s, ν (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := ν.map_smul 0 0
    simp only [zero_smul, zero_mul] at h0
    simpa using h0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ν.map_add, ih]

/-- The covariance is symmetric. DERIVED: no numeral. -/
theorem stateCov_comm (ν : State X) (u v : C(X, ℝ)) : stateCov ν u v = stateCov ν v u := by
  unfold stateCov
  rw [mul_comm u v, mul_comm (ν u)]

/-- **The covariance is linear in the left slot over finite sums.** DERIVED: no numeral. -/
theorem stateCov_sum_left (ν : State X) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → C(X, ℝ))
    (v : C(X, ℝ)) :
    stateCov ν (∑ i ∈ s, c i • u i) v = ∑ i ∈ s, c i * stateCov ν (u i) v := by
  unfold stateCov
  rw [Finset.sum_mul, state_sum, state_sum]
  simp only [smul_mul_assoc, ν.map_smul]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **The covariance is linear in the right slot over finite sums.** DERIVED: no numeral. -/
theorem stateCov_sum_right (ν : State X) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → C(X, ℝ))
    (v : C(X, ℝ)) :
    stateCov ν v (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * stateCov ν v (u i) := by
  rw [stateCov_comm, stateCov_sum_left]
  exact Finset.sum_congr rfl fun i _ => by rw [stateCov_comm]

end Bilinear

/-! ## 2. The normalisation of a smeared read -/

section Smeared

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- The support radius of a test function, read from its own witness. DERIVED: no numeral. -/
def rad (f : TestFn) : ℝ := f.2.choose

/-- The test bound at the support radius. DERIVED: no numeral. -/
theorem isTest_rad (f : TestFn) : ∃ M : ℝ, IsTest f.1 (rad f) M := f.2.choose_spec

/-- **The bracket**: the lattice covariance of the translates, weighted by `f ⊗ g` at the scaled sites, summed over
the boxes that carry the supports. DERIVED: no numeral. -/
def bracket (ν : State (IConf G)) (L₁ L₂ : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ)) (a : ℝ)
    (F : C(IConf G, ℝ)) (f g : TestFn) : ℝ :=
  ∑ x ∈ box ⌈rad f / a⌉₊, ∑ y ∈ box ⌈rad g / a⌉₊,
    f.1 (site a x) * g.1 (site a y) * stateCov ν (L₁ (transObs x F)) (L₂ (transObs y F))

/-- **The smeared two-point read is `a⁸` times the bracket.** One cell volume `a⁴` per smeared field. DERIVED:
`0` the sign of `a`; `4` the cell-volume exponent; `8 = 4 + 4`. -/
theorem read_eq_scale (ν : State (IConf G)) (L₁ L₂ : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ)) {a : ℝ}
    (ha : 0 < a) (F : C(IConf G, ℝ)) (f g : TestFn) :
    stateCov ν (L₁ (smear a F f)) (L₂ (smear a F g)) = a ^ 8 * bracket ν L₁ L₂ a F f g := by
  obtain ⟨Mf, hf⟩ := isTest_rad f
  obtain ⟨Mg, hg⟩ := isTest_rad g
  rw [smear_eq_sum ha F f hf (Finset.Subset.refl _), smear_eq_sum ha F g hg (Finset.Subset.refl _),
    map_sum, map_sum]
  simp only [map_smul]
  rw [stateCov_sum_left]
  unfold bracket
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [stateCov_sum_right, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => by ring

/-- **The reflected read at a physical separation**: `θ` on the left, the translation by the lattice vector `v` on
the right. The bracket reads `Cov(θ τ_x F, τ_{y+v} F)`. DERIVED: `0` the plane; `8` the two cell volumes. -/
theorem reflRead_eq_scale (ν : State (IConf G)) (τ : Fin 4) (v : ISite) {a : ℝ} (ha : 0 < a)
    (F : C(IConf G, ℝ)) (f g : TestFn) :
    stateCov ν (LatticeReflection.ireflObs τ 0 (smear a F f)) (transObs v (smear a F g))
      = a ^ 8 * ∑ x ∈ box ⌈rad f / a⌉₊, ∑ y ∈ box ⌈rad g / a⌉₊,
          f.1 (site a x) * g.1 (site a y) *
            stateCov ν (LatticeReflection.ireflObs τ 0 (transObs x F)) (transObs (y + v) F) := by
  rw [read_eq_scale ν _ _ ha]
  unfold bracket
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [transObs_transObs, add_comm v y]

/-- **The two bounds of a band at `s = a⁸` are bounds on the bracket.** DERIVED: `0` the sign of `a`; `8` the two
cell volumes. -/
theorem physBounds_iff (ν : State (IConf G)) (L₁ L₂ : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ)) {a : ℝ}
    (ha : 0 < a) (F : C(IConf G, ℝ)) (f g : TestFn) (c C : ℝ) :
    (c * a ^ 8 ≤ stateCov ν (L₁ (smear a F f)) (L₂ (smear a F g)) ↔ c ≤ bracket ν L₁ L₂ a F f g) ∧
    (stateCov ν (L₁ (smear a F f)) (L₂ (smear a F g)) ≤ C * a ^ 8 ↔ bracket ν L₁ L₂ a F f g ≤ C) := by
  have h8 : 0 < a ^ 8 := pow_pos ha 8
  rw [read_eq_scale ν L₁ L₂ ha]
  constructor
  · rw [mul_comm c, mul_le_mul_iff_right₀ h8]
  · rw [mul_comm C, mul_le_mul_iff_right₀ h8]

end Smeared

/-! ## 3. `PhysBand` without a scale -/

section Band

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The scale supplied by the far read**: `gE(m₂ k)/c` where the far read is positive, `1` otherwise. DERIVED:
`0` the sign; `1` the fallback. -/
def physScale (βs : ℕ → ℝ) (m₂ : ℕ → ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  if 0 < gE (N := N) (βs k) (m₂ k) then gE (N := N) (βs k) (m₂ k) / c else 1

/-- The supplied scale is positive. DERIVED: `0` the sign; `1` the fallback. -/
theorem physScale_pos {βs : ℕ → ℝ} {m₂ : ℕ → ℕ} {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 < physScale N βs m₂ c k := by
  unfold physScale
  split_ifs with h
  · exact div_pos h hc
  · exact one_pos

/-- **`PhysBand` is a ratio of two reads**: a positive scale exists iff, eventually, the gaps are `w 2^k` apart,
the far read is positive and `c · gE(m₁) ≤ C · gE(m₂)`. The scale is `physScale`. DERIVED: `0` the signs; `2` the
window base. -/
theorem physBand_iff_ratio {βs : ℕ → ℝ} {m₁ m₂ : ℕ → ℕ} {c C w : ℝ} (hc : 0 < c) :
    (∃ s : ℕ → ℝ, (∀ k, 0 < s k) ∧ FloorFold.PhysBand N βs s m₁ m₂ c C w) ↔
      ∀ᶠ k in atTop, w * 2 ^ k + m₁ k ≤ m₂ k ∧ 0 < gE (N := N) (βs k) (m₂ k) ∧
        c * gE (N := N) (βs k) (m₁ k) ≤ C * gE (N := N) (βs k) (m₂ k) := by
  constructor
  · rintro ⟨s, hs, h⟩
    filter_upwards [h] with k ⟨hgap, hfl, hcl⟩
    refine ⟨hgap, lt_of_lt_of_le (mul_pos hc (hs k)) hfl, ?_⟩
    calc c * gE (N := N) (βs k) (m₁ k) ≤ c * (C * s k) := mul_le_mul_of_nonneg_left hcl hc.le
      _ = C * (c * s k) := by ring
      _ ≤ C * gE (N := N) (βs k) (m₂ k) := by
        rcases le_or_gt 0 C with hC | hC
        · exact mul_le_mul_of_nonneg_left hfl hC
        · -- a negative ceiling: `gE(m₁) ≤ C s < 0`, impossible against `gE ≥ 0`
          exfalso
          have h0 : 0 ≤ gE (N := N) (βs k) (m₁ k) := FloorFold.gP_nonneg (βs k) (FloorFold.connE_mem (βs k)) _
          nlinarith [hs k]
  · intro h
    refine ⟨physScale N βs m₂ c, physScale_pos hc, ?_⟩
    filter_upwards [h] with k ⟨hgap, hpos, hr⟩
    have hsk : physScale N βs m₂ c k = gE (N := N) (βs k) (m₂ k) / c := by
      unfold physScale; rw [if_pos hpos]
    refine ⟨hgap, ?_, ?_⟩
    · rw [hsk, mul_div_cancel₀ _ hc.ne']
    · rw [hsk]
      calc gE (N := N) (βs k) (m₁ k) = c * gE (N := N) (βs k) (m₁ k) / c := by field_simp
        _ ≤ C * gE (N := N) (βs k) (m₂ k) / c := div_le_div_of_nonneg_right hr hc.le
        _ = C * (gE (N := N) (βs k) (m₂ k) / c) := by ring

/-- **The slope from the ratio of two reads**: `FloorFold.slope_of_physBand` with the scale supplied by
`physScale`. DERIVED: `0` the signs; `2` the two steps of one gap and the window base. -/
theorem slope_of_ratio {βs : ℕ → ℝ} {m₁ m₂ : ℕ → ℕ} {c C w U : ℝ} (hc : 0 < c) (hC : 0 < C) (hw : 0 < w)
    (hU0 : 0 ≤ U) (hU : Real.log (C / c) ≤ 2 * w * U)
    (h : ∀ᶠ k in atTop, w * 2 ^ k + m₁ k ≤ m₂ k ∧ 0 < gE (N := N) (βs k) (m₂ k) ∧
        c * gE (N := N) (βs k) (m₁ k) ≤ C * gE (N := N) (βs k) (m₂ k)) :
    FloorFold.SlopeAt N βs U := by
  obtain ⟨s, hs, hb⟩ := (physBand_iff_ratio hc).mpr h
  exact FloorFold.slope_of_physBand hs hc hC hw hU0 hU hb

end Band

end MassGap.ScaleNorm

#print axioms MassGap.ScaleNorm.state_sum
#print axioms MassGap.ScaleNorm.stateCov_comm
#print axioms MassGap.ScaleNorm.stateCov_sum_left
#print axioms MassGap.ScaleNorm.stateCov_sum_right
#print axioms MassGap.ScaleNorm.isTest_rad
#print axioms MassGap.ScaleNorm.read_eq_scale
#print axioms MassGap.ScaleNorm.reflRead_eq_scale
#print axioms MassGap.ScaleNorm.physBounds_iff
#print axioms MassGap.ScaleNorm.physScale_pos
#print axioms MassGap.ScaleNorm.physBand_iff_ratio
#print axioms MassGap.ScaleNorm.slope_of_ratio
