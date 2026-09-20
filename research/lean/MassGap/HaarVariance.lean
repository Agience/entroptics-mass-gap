import Mathlib
import MassGap.WilsonAction

/-!
# MassGap.HaarVariance — `Re tr` has strictly positive variance under pure Haar

A single self-contained constant: on `SU(N)` with `N ≥ 2`, the fundamental-character observable
`U ↦ Re tr U` has strictly positive variance against the normalized Haar measure.

    0 < Var_Haar (fun U => Re tr U)      on SU(N), N ≥ 2

The constant carries **no lattice extent and no coupling**: nothing in the statement or the proof
mentions a lattice, a volume, a boundary condition, a temperature or a `β`. Its only parameter is
the rank `N`, and it is the pure group-theoretic input a Wilson-measure variance bound reduces to.

## The argument

Three facts, and nothing else:

* `Re tr` is CONTINUOUS on `SU(N)` (trace is a finite sum of entries, `Complex.re` is continuous);
* normalized Haar on a compact group is an `IsOpenPosMeasure` (it is a Haar measure, and
  `IsHaarMeasure` carries open-positivity), so a continuous function that is a.e. constant against
  it is constant EVERYWHERE (`Continuous.ae_eq_iff_eq`);
* `Re tr` is NON-CONSTANT, exhibited by two named elements.

If the variance vanished, the centred square `(Re tr U − m)²` — continuous and nonnegative — would
integrate to zero, hence vanish a.e., hence vanish identically, forcing `Re tr ≡ m`. The witnesses
refute that. `PlaqVariance.wilsonCorrConn_self_pos` runs this same shape against the Gibbs measure;
here it is run against bare Haar, with no weight and no geometry, which is what makes the result a
universal constant rather than a property of one lattice.

## The witnesses

`1` has `Re tr = N`. `flipEl`, the diagonal matrix `diag(−1, −1, 1, …, 1)`, has determinant
`(−1)·(−1) = 1` and unit-modulus entries, so it is a genuine element of `SU(N)`, and its real trace
is `N − 4`. `N` and `N − 4` differ, which is the whole of the non-constancy. `N ≥ 2` is exactly what
lets the two `−1`s fit, and it is where the hypothesis is consumed; at `N = 1` the determinant
condition makes the group trivial and the variance is genuinely zero.

The rank is carried as `N = m + 2` inside the construction so that `Fin.prod_univ_succ` twice reaches
the two `−1` slots; `haar_variance_reTr_pos` restates it under `2 ≤ N`.

## The four-link form, and which invariance it uses

A plaquette is the ordered product of four independent link variables. `haar_variance_four_link_pos`
is that statement, and it is REDUCED to the one-element statement rather than assumed: the ordered
product map `(U₁,U₂,U₃,U₄) ↦ U₁U₂U₃U₄` pushes the four-fold product Haar measure forward to Haar
itself (`measurePreserving_prod4`), and variance transfers along any measure-preserving map
(`variance_comp_measurePreserving`).

The invariance consumed is **left-invariance of Haar**, once, in `measurePreserving_mul`: for a
measurable `t`, Fubini for the product measure gives `(μ × μ)(mul⁻¹ t) = ∫⁻ x, μ ((x · ·)⁻¹ t)`, and
left-invariance collapses the integrand to the constant `μ t`, which integrates to `μ t` because `μ`
is a probability measure. Nothing else about Haar is used — not right-invariance, not unimodularity,
not regularity. The reduction therefore holds for any left-invariant probability measure on a
measurable group, and `SU(N)` enters only through the witnesses.

## Constructive or existential

The positivity is NON-CONSTRUCTIVE in the value: the proof produces no lower bound for the variance,
only that it is not zero. That is deliberate and sufficient — the caller needs a strictly positive
number with no lattice extent and no coupling in it, not its size.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python code/lean_build.py build MassGap.HaarVariance`.
-/

namespace MassGap.HaarVariance

open MeasureTheory ProbabilityTheory
open MassGap.SUN MassGap.CompactGauge

/-! ### The observable -/

/-- The fundamental plaquette observable on one group element: `Re tr U`. -/
noncomputable def reTr {N : ℕ} (g : SU N) : ℝ :=
  (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re

/-- `Re tr` is continuous: the trace is a finite sum of matrix entries and `Complex.re` is
continuous. -/
theorem continuous_reTr {N : ℕ} : Continuous (reTr (N := N)) :=
  Complex.continuous_re.comp continuous_subtype_val.matrix_trace

theorem measurable_reTr {N : ℕ} : Measurable (reTr (N := N)) := continuous_reTr.measurable

/-- The identity has `Re tr = N`. -/
theorem reTr_one {N : ℕ} : reTr (1 : SU N) = (N : ℝ) := by
  unfold reTr
  rw [Submonoid.coe_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]

/-! ### The second witness: `diag(−1, −1, 1, …, 1)`

Determinant `(−1)·(−1)·1⋯1 = 1` and unit-modulus entries, so it lies in `SU(m+2)`; its real trace is
`(m + 2) − 4 = m − 2`. -/

/-- The diagonal `(−1, −1, 1, …, 1)` on `Fin (m+2)`.

DERIVED: nothing here is a magnitude, and the count of flipped entries is forced. `i.val < 2` puts
`−1` on TWO entries because the determinant must be `1`: one flip gives `−1` and leaves the special
unitary group, two give `(−1)·(−1) = 1` and stay in it — `flipVec_prod` is that computation. `−1` is
the only unit-modulus real other than `1`, so it is the one entry change that keeps the matrix
unitary (`flipMat_star`, `flipMat_mul_self`) while moving `Re tr`. The `1`s are the remaining
diagonal, i.e. the identity's entries, so the witness differs from `1` in as few places as the group
allows. `Fin (m + 2)` carries the rank as `N = m + 2` for the same reason: `N ≥ 2` is exactly what
lets the two `−1`s fit, it is where `haar_variance_reTr_pos`'s hypothesis is consumed, and at `N = 1`
the determinant condition makes the group trivial and the variance genuinely zero. -/
noncomputable def flipVec (m : ℕ) : Fin (m + 2) → ℂ := fun i => if i.val < 2 then -1 else 1

theorem flipVec_zero (m : ℕ) : flipVec m 0 = -1 := by
  simp only [flipVec, Fin.val_zero]
  norm_num

theorem flipVec_one (m : ℕ) : flipVec m (Fin.succ (0 : Fin (m + 1))) = -1 := by
  simp only [flipVec, Fin.val_succ, Fin.val_zero]
  norm_num

theorem flipVec_succ_succ (m : ℕ) (i : Fin m) :
    flipVec m (Fin.succ (Fin.succ i)) = 1 := by
  have h : ¬ ((Fin.succ (Fin.succ i) : Fin (m + 2)).val < 2) := by
    simp only [Fin.val_succ]; omega
  simp only [flipVec]
  rw [if_neg h]

/-- Two `−1`s multiply to `1`, the rest are `1`: the determinant condition holds. -/
theorem flipVec_prod (m : ℕ) : ∏ i, flipVec m i = 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, flipVec_zero, flipVec_one]
  rw [Finset.prod_congr rfl (fun i _ => flipVec_succ_succ m i)]
  simp

/-- The diagonal matrix itself.

DERIVED: the only numeral is the `2` of `Fin (m + 2)`, which is `flipVec`'s — the rank written as
`N = m + 2` so that `N ≥ 2` is structural and `Fin.prod_univ_succ` twice reaches the two `−1` slots.
It is the minimum rank at which a non-identity diagonal witness exists, not a chosen size, and the
statement `haar_variance_reTr_pos` restates it under the hypothesis `2 ≤ N`. -/
noncomputable def flipMat (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  Matrix.diagonal (flipVec m)

theorem flipMat_star (m : ℕ) : star (flipMat m) = flipMat m := by
  rw [flipMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply, flipVec]
  split <;> simp

theorem flipMat_mul_self (m : ℕ) : flipMat m * flipMat m = 1 := by
  rw [flipMat, Matrix.diagonal_mul_diagonal]
  have h : (fun i => flipVec m i * flipVec m i) = (1 : Fin (m + 2) → ℂ) := by
    funext i
    simp only [flipVec, Pi.one_apply]
    split <;> norm_num
  rw [h]
  simp

theorem flipMat_mem (m : ℕ) :
    flipMat m ∈ Matrix.specialUnitaryGroup (Fin (m + 2)) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [flipMat_star]; exact flipMat_mul_self m
  · rw [flipMat, Matrix.det_diagonal, flipVec_prod]

/-- `diag(−1, −1, 1, …, 1)` as an element of `SU(m+2)`.

DERIVED: both numerals are `flipVec`'s, carried up unchanged — the `2` of `Fin (m + 2)` is the rank
written so that `N ≥ 2` is structural, and the `±1` entries in the prose are the diagonal described
there, where the pair of `−1`s is forced by the determinant condition. Membership is not asserted: it
is `flipMat_mem`. The witness is used only through `reTr_flipEl_ne_reTr_one`, which needs the two
traces to DIFFER and nothing about their size, so no value enters the result. -/
noncomputable def flipEl (m : ℕ) : SU (m + 2) := ⟨flipMat m, flipMat_mem m⟩

/-- The second witness's real trace: `(−1) + (−1) + m = m − 2`, i.e. `N − 4`. -/
theorem reTr_flipEl (m : ℕ) : reTr (flipEl m) = (m : ℝ) - 2 := by
  have hrest : (∑ i : Fin m, (flipVec m (Fin.succ (Fin.succ i))).re) = (m : ℝ) := by
    simp [flipVec_succ_succ]
  show (Matrix.trace (flipMat m)).re = (m : ℝ) - 2
  rw [flipMat, Matrix.trace_diagonal, Complex.re_sum, Fin.sum_univ_succ, Fin.sum_univ_succ,
    flipVec_zero, flipVec_one, hrest]
  simp only [Complex.neg_re, Complex.one_re]
  ring

/-- **Non-constancy, exhibited.** `Re tr` takes two different values on `SU(m+2)`: `m + 2` at the
identity and `m − 2` at `flipEl`. -/
theorem reTr_flipEl_ne_reTr_one (m : ℕ) : reTr (flipEl m) ≠ reTr (1 : SU (m + 2)) := by
  rw [reTr_flipEl, reTr_one]
  push_cast
  intro h
  linarith

/-! ### Positive variance from continuity, open-positivity and two values -/

/-- **A continuous function with two different values has strictly positive variance against any
open-positive probability measure on a compact space.**

If the variance were zero, the continuous nonnegative centred square would integrate to zero, hence
vanish almost everywhere, hence — by `Continuous.ae_eq_iff_eq` against an `IsOpenPosMeasure` —
vanish at EVERY point, making the function constant. Two named values refute that. -/
theorem variance_pos_of_two_values {G : Type*} [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [CompactSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] {f : G → ℝ} (hf : Continuous f) {a b : G} (hab : f a ≠ f b) :
    0 < variance f μ := by
  classical
  set c : ℝ := ∫ x, f x ∂μ with hc
  have hg : Continuous (fun x => (f x - c) ^ 2) := (hf.sub continuous_const).pow 2
  have hgi : Integrable (fun x => (f x - c) ^ 2) μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : (0 : G → ℝ) ≤ fun x => (f x - c) ^ 2 := fun x => sq_nonneg _
  rw [variance_eq_integral hf.measurable.aemeasurable, ← hc]
  refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => ?_)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hgi).mp h0.symm
  have hzero := (Continuous.ae_eq_iff_eq μ hg continuous_const).mp hae
  have hconst : ∀ x, f x = c := by
    intro x
    have hx : (f x - c) ^ 2 = 0 := congrFun hzero x
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
    linarith
  exact hab ((hconst a).trans (hconst b).symm)

/-- **THE CONSTANT, at `N = m + 2`.** `Re tr` has strictly positive variance under normalized Haar
on `SU(m+2)`. No lattice, no coupling, no weight. -/
theorem haar_variance_reTr_pos' (m : ℕ) :
    0 < variance (reTr (N := m + 2)) (probHaar (SU (m + 2))) :=
  variance_pos_of_two_values _ continuous_reTr (reTr_flipEl_ne_reTr_one m)

/-- **THE CONSTANT.** For every `N ≥ 2`, the plaquette observable `Re tr` has strictly positive
variance under pure Haar on `SU(N)`.

The number depends on nothing but `N`: no lattice extent, no boundary condition, no coupling. It is
existential — the proof exhibits no lower bound, only non-vanishing. -/
theorem haar_variance_reTr_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < variance (reTr (N := N)) (probHaar (SU N)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact haar_variance_reTr_pos' m

/-! ### The four-link reduction

The ordered product of independent Haar elements is Haar. Proved, not assumed; the single input is
LEFT-INVARIANCE of the measure. -/

/-- **Multiplication pushes product Haar to Haar.** For a left-invariant probability measure `μ` on
a measurable group, `(U, V) ↦ U * V` is measure-preserving from `μ × μ` to `μ`.

The proof is Fubini plus left-invariance: `(μ × μ)((·*·)⁻¹ t) = ∫⁻ x, μ ((x * ·)⁻¹ t)`, the
integrand is `μ t` by left-invariance, and `∫⁻ x, μ t ∂μ = μ t` because `μ` is a probability. -/
theorem measurePreserving_mul {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    MeasurePreserving (fun p : G × G => p.1 * p.2) (μ.prod μ) μ := by
  have hmeas : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd
  refine ⟨hmeas, ?_⟩
  ext t ht
  rw [Measure.map_apply hmeas ht, Measure.prod_apply (hmeas ht)]
  have hfib : ∀ x : G,
      μ (Prod.mk x ⁻¹' ((fun p : G × G => p.1 * p.2) ⁻¹' t)) = μ t := by
    intro x
    have hpre : (Prod.mk x ⁻¹' ((fun p : G × G => p.1 * p.2) ⁻¹' t))
        = (fun h => x * h) ⁻¹' t := rfl
    rw [hpre, measure_preimage_mul]
  simp only [hfib]
  simp

/-- The ordered product of four group elements. -/
def prod4 {G : Type*} [Mul G] (p : G × G × G × G) : G :=
  p.1 * p.2.1 * p.2.2.1 * p.2.2.2

/-- **The ordered four-fold product pushes the four-fold product Haar to Haar.** Three applications
of `measurePreserving_mul`, so the only invariance consumed is left-invariance. -/
theorem measurePreserving_prod4 {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    MeasurePreserving (prod4 : G × G × G × G → G) (μ.prod (μ.prod (μ.prod μ))) μ := by
  have hmul := measurePreserving_mul μ
  have h1 : MeasurePreserving (Prod.map (id : G → G) (fun q : G × G => q.1 * q.2))
      (μ.prod (μ.prod μ)) (μ.prod μ) := (MeasurePreserving.id μ).prod hmul
  have h2 : MeasurePreserving
      (Prod.map (id : G → G) (Prod.map (id : G → G) (fun q : G × G => q.1 * q.2)))
      (μ.prod (μ.prod (μ.prod μ))) (μ.prod (μ.prod μ)) := (MeasurePreserving.id μ).prod h1
  have hfun : (prod4 : G × G × G × G → G)
      = ((fun q : G × G => q.1 * q.2) ∘ Prod.map (id : G → G) (fun q : G × G => q.1 * q.2))
        ∘ Prod.map (id : G → G) (Prod.map (id : G → G) (fun q : G × G => q.1 * q.2)) := by
    funext p
    show p.1 * p.2.1 * p.2.2.1 * p.2.2.2 = p.1 * (p.2.1 * (p.2.2.1 * p.2.2.2))
    rw [mul_assoc, mul_assoc]
  rw [hfun]
  exact (hmul.comp h1).comp h2

/-- **Variance transfers along a measure-preserving map.** Both the mean and the centred second
moment are integrals, and `integral_map` moves each one across. -/
theorem variance_comp_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {μ : Measure β} {T : α → β} (hT : MeasurePreserving T ν μ)
    {f : β → ℝ} (hf : Measurable f) :
    variance (fun x => f (T x)) ν = variance f μ := by
  have hmap : ∀ g : β → ℝ, Measurable g → ∫ x, g (T x) ∂ν = ∫ y, g y ∂μ := by
    intro g hg
    have h := integral_map (φ := T) (f := g) hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hg.aestronglyMeasurable)
    rw [hT.map_eq] at h
    exact h.symm
  have hfT : Measurable (fun x => f (T x)) := hf.comp hT.measurable
  rw [variance_eq_integral hfT.aemeasurable, variance_eq_integral hf.aemeasurable, hmap f hf]
  exact hmap (fun y => (f y - ∫ z, f z ∂μ) ^ 2) ((hf.sub measurable_const).pow_const 2)

/-- **THE FOUR-LINK FORM.** For four INDEPENDENT Haar-distributed elements of `SU(N)`, `N ≥ 2` — the
product measure on `SU(N)⁴` is exactly the law of four independent Haar variables — the ordered
product's `Re tr` has strictly positive variance, and it is the SAME constant as the one-element
statement, not a new one.

Reduced, not assumed: `measurePreserving_prod4` shows the ordered product of independent Haar
elements is Haar-distributed (left-invariance of Haar, three times), and
`variance_comp_measurePreserving` carries the variance across. Like the one-element form it carries
no lattice extent and no coupling. -/
theorem haar_variance_four_link_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < variance (fun p : SU N × SU N × SU N × SU N => reTr (prod4 p))
      ((probHaar (SU N)).prod
        ((probHaar (SU N)).prod ((probHaar (SU N)).prod (probHaar (SU N))))) := by
  rw [variance_comp_measurePreserving (measurePreserving_prod4 (probHaar (SU N))) measurable_reTr]
  exact haar_variance_reTr_pos hN

/-- The reduction itself, stated on its own: the four-link variance EQUALS the one-element Haar
variance. This is the sentence the caller can quote — the plaquette's Haar variance is the
single-element Haar variance, by left-invariance. -/
theorem four_link_variance_eq {N : ℕ} :
    variance (fun p : SU N × SU N × SU N × SU N => reTr (prod4 p))
        ((probHaar (SU N)).prod
          ((probHaar (SU N)).prod ((probHaar (SU N)).prod (probHaar (SU N)))))
      = variance (reTr (N := N)) (probHaar (SU N)) :=
  variance_comp_measurePreserving (measurePreserving_prod4 (probHaar (SU N))) measurable_reTr

/-! ### Negative control

At `N = 1` the determinant condition pins the single entry to `1`, the group is trivial, `Re tr ≡ 1`
and the variance is exactly zero. So `2 ≤ N` above is load-bearing rather than decoration. -/

theorem reTr_su_one (g : SU 1) : reTr g = 1 := by
  have hdet : (g : Matrix (Fin 1) (Fin 1) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  rw [Matrix.det_fin_one] at hdet
  show (Matrix.trace (g : Matrix (Fin 1) (Fin 1) ℂ)).re = 1
  rw [Matrix.trace_fin_one, hdet, Complex.one_re]

theorem haar_variance_reTr_su_one : variance (reTr (N := 1)) (probHaar (SU 1)) = 0 := by
  have h : (reTr (N := 1)) = fun _ => (1 : ℝ) := funext reTr_su_one
  rw [h, variance_eq_integral (measurable_const.aemeasurable)]
  simp

#print axioms reTr_one
#print axioms reTr_flipEl
#print axioms reTr_flipEl_ne_reTr_one
#print axioms variance_pos_of_two_values
#print axioms haar_variance_reTr_pos'
#print axioms haar_variance_reTr_pos
#print axioms measurePreserving_mul
#print axioms measurePreserving_prod4
#print axioms variance_comp_measurePreserving
#print axioms haar_variance_four_link_pos
#print axioms four_link_variance_eq
#print axioms haar_variance_reTr_su_one

end MassGap.HaarVariance
