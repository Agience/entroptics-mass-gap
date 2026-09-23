import Mathlib
import MassGap.WilsonAction

/-!
# MassGap.HaarVariance — the variance of `Re tr` under normalised Haar on `SU(N)`

`haar_variance_reTr_pos` states that for `2 ≤ N`, the observable `reTr : SU N → ℝ`, `U ↦ Re tr U`,
has strictly positive variance against `probHaar (SU N)`:

    0 < variance reTr (probHaar (SU N))     for 2 ≤ N

Its only parameter is the rank `N`. No lattice, extent, volume, boundary condition or coupling
appears in the statement or in the proof.

## The argument

`variance_pos_of_two_values` is the general step: on a compact space, for a continuous `f` and an
open-positive probability measure, two points where `f` differs give `0 < variance f μ`. If the
variance were zero, the continuous nonnegative centred square would integrate to zero, hence vanish
almost everywhere, hence — by `Continuous.ae_eq_iff_eq` against an `IsOpenPosMeasure` — vanish
everywhere, making `f` constant. `probHaar` on a compact group is open-positive because
`IsHaarMeasure` carries that instance.

The two points are `1`, where `reTr = N`, and `flipEl`, the diagonal `diag(-1, -1, 1, …, 1)`, where
`reTr = N - 4`. `flipVec_prod` computes its determinant as `(-1) * (-1) = 1`, and `flipMat_star`
with `flipMat_mul_self` give unitarity, so `flipMat_mem` places it in `SU(m+2)`. The rank is carried
as `N = m + 2` in the construction so that two applications of `Fin.prod_univ_succ` reach the two
`-1` slots; `haar_variance_reTr_pos` restates the result under `2 ≤ N`.

## The four-link form

`haar_variance_four_link_pos` is the same statement for the ordered product of four independent Haar
elements, and it is reduced to the one-element form rather than assumed: `measurePreserving_prod4`
pushes the four-fold product measure forward to the measure itself, and
`variance_comp_measurePreserving` carries the variance across. `four_link_variance_eq` states the
equality of the two variances on its own.

The only property of the measure used in that reduction is left-invariance, once, in
`measurePreserving_mul`: Fubini gives `(μ × μ)(mul⁻¹ t) = ∫⁻ x, μ ((x * ·)⁻¹ t)`, left-invariance
collapses the integrand to the constant `μ t`, and that integrates to `μ t` because `μ` is a
probability measure. Right-invariance, unimodularity and regularity are not used, so
`measurePreserving_mul` and `measurePreserving_prod4` are stated for any left-invariant probability
measure on a measurable group; `SU(N)` enters only through the witnesses.

## Scope

The positivity is existential in the value: no lower bound for the variance is produced, only
non-vanishing. The hypothesis `2 ≤ N` is load-bearing, and `haar_variance_reTr_su_one` is the
control: at `N = 1` the determinant condition pins the single entry to `1`, so `reTr` is constant
and the variance is exactly `0`.

DERIVED: `2` is the rank offset in `N = m + 2`, the smallest rank at which a non-identity diagonal
witness exists, and the entry count `flipVec` flips; `1` and `-1` are the two diagonal entries, `-1`
being the only unit-modulus real other than `1` and a pair of them being what the determinant
condition allows; `0` is the level positivity is asserted above, and the variance at `N = 1`; `4` is
the trace difference `N - (N - 4)` between the two witnesses.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python code/lean_build.py build MassGap.HaarVariance`.
-/

namespace MassGap.HaarVariance

open MeasureTheory ProbabilityTheory
open MassGap.SUN MassGap.CompactGauge

/-! ### The observable -/

/-- The fundamental-character observable on one group element: the real part of the matrix trace,
`(Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re`. Defined at every rank `N`, including `N = 0` and
`N = 1`.

DERIVED: no numeral appears in the statement. -/
noncomputable def reTr {N : ℕ} (g : SU N) : ℝ :=
  (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re

/-- `Continuous (reTr (N := N))`: the subtype coercion into matrices is continuous, the trace is a
finite sum of entries, and `Complex.re` is continuous.

DERIVED: no numeral appears in the statement. -/
theorem continuous_reTr {N : ℕ} : Continuous (reTr (N := N)) :=
  Complex.continuous_re.comp continuous_subtype_val.matrix_trace

theorem measurable_reTr {N : ℕ} : Measurable (reTr (N := N)) := continuous_reTr.measurable

/-- `reTr (1 : SU N) = (N : ℝ)`: the identity matrix has trace `N`, by `Matrix.trace_one` and
`Fintype.card_fin`.

DERIVED: `1` is the group identity, the first of the two witnesses. -/
theorem reTr_one {N : ℕ} : reTr (1 : SU N) = (N : ℝ) := by
  unfold reTr
  rw [Submonoid.coe_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]

/-! ### The second witness: `diag(-1, -1, 1, …, 1)`

Determinant `(-1) * (-1) * 1 ⋯ 1 = 1` and unit-modulus entries, so it lies in `SU(m+2)`; its real
trace is `(m + 2) - 4 = m - 2`. `flipVec` is the diagonal, `flipMat` the matrix, and `flipEl` the
group element. -/

/-- The diagonal vector `(-1, -1, 1, …, 1)` on `Fin (m + 2)`: `-1` at the two indices with
`i.val < 2`, and `1` elsewhere.

DERIVED: no numeral here is a magnitude, and the count of flipped entries is forced. `i.val < 2`
puts `-1` on two entries because the determinant must be `1`: one flip gives `-1` and leaves the
special unitary group, two give `(-1) * (-1) = 1` and stay in it, which is `flipVec_prod`. `-1` is
the only unit-modulus real other than `1`, so it is the entry change that keeps the matrix unitary
(`flipMat_star`, `flipMat_mul_self`) while moving `reTr`. The `1`s are the identity's remaining
diagonal entries. `Fin (m + 2)` carries the rank as `N = m + 2` so that `N ≥ 2` is structural: that
is what lets the two `-1`s fit, it is where `haar_variance_reTr_pos`'s hypothesis is consumed, and
at `N = 1` the determinant condition makes the group trivial and the variance zero. -/
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

/-- `∏ i, flipVec m i = 1`: two entries of `-1` multiply to `1` and the rest are `1`. Two
applications of `Fin.prod_univ_succ` split off the flipped pair. This is the determinant condition
`flipMat_mem` needs.

DERIVED: `1` is the value the determinant must take in `SU(m+2)`. -/
theorem flipVec_prod (m : ℕ) : ∏ i, flipVec m i = 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, flipVec_zero, flipVec_one]
  rw [Finset.prod_congr rfl (fun i _ => flipVec_succ_succ m i)]
  simp

/-- `Matrix.diagonal (flipVec m)`, the matrix of the second witness on `Fin (m + 2)`. Membership in
the special unitary group is `flipMat_mem`, not part of this definition.

DERIVED: the only numeral is the `2` of `Fin (m + 2)`, carried from `flipVec` — the rank written as
`N = m + 2` so that `N ≥ 2` is structural and `Fin.prod_univ_succ` twice reaches the two `-1` slots.
It is the minimum rank at which a non-identity diagonal witness exists, and
`haar_variance_reTr_pos` restates the result under the hypothesis `2 ≤ N`. -/
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

/-- `flipMat m` bundled with `flipMat_mem m` as an element of `SU (m + 2)`.

The witness is used only through `reTr_flipEl_ne_reTr_one`, which needs the two traces to differ and
nothing about their size, so no value from it enters the variance result.

DERIVED: the `2` of `Fin (m + 2)` is `flipVec`'s, the rank written so that `N ≥ 2` is structural. -/
noncomputable def flipEl (m : ℕ) : SU (m + 2) := ⟨flipMat m, flipMat_mem m⟩

/-- `reTr (flipEl m) = (m : ℝ) - 2`: the trace of the diagonal is `(-1) + (-1) + m`, computed by
`Matrix.trace_diagonal` and two applications of `Fin.sum_univ_succ`. In terms of the rank
`N = m + 2` this is `N - 4`.

DERIVED: `2` is the rank offset in `N = m + 2` and equals the two flipped entries' contribution
`(-1) + (-1)` relative to the identity's `1 + 1`. -/
theorem reTr_flipEl (m : ℕ) : reTr (flipEl m) = (m : ℝ) - 2 := by
  have hrest : (∑ i : Fin m, (flipVec m (Fin.succ (Fin.succ i))).re) = (m : ℝ) := by
    simp [flipVec_succ_succ]
  show (Matrix.trace (flipMat m)).re = (m : ℝ) - 2
  rw [flipMat, Matrix.trace_diagonal, Complex.re_sum, Fin.sum_univ_succ, Fin.sum_univ_succ,
    flipVec_zero, flipVec_one, hrest]
  simp only [Complex.neg_re, Complex.one_re]
  ring

/-- `reTr (flipEl m) ≠ reTr (1 : SU (m + 2))`: the observable takes two different values on
`SU(m+2)`, namely `m - 2` at `flipEl m` and `m + 2` at the identity. It is `reTr_flipEl` and
`reTr_one` followed by `linarith`, and it holds at every `m`, including `m = 0`.

DERIVED: `2` is the rank offset in `N = m + 2`; `1` is the group identity, the first witness. -/
theorem reTr_flipEl_ne_reTr_one (m : ℕ) : reTr (flipEl m) ≠ reTr (1 : SU (m + 2)) := by
  rw [reTr_flipEl, reTr_one]
  push_cast
  intro h
  linarith

/-! ### Positive variance from continuity, open-positivity and two values -/

/-- `0 < variance f μ` for a continuous `f : G → ℝ` on a compact space carrying an open-positive
probability measure `μ`, given two points `a b` with `f a ≠ f b`.

If the variance were zero, the continuous nonnegative centred square `(f x - c)^2` would have
integral zero, hence vanish almost everywhere, hence — by `Continuous.ae_eq_iff_eq` against an
`IsOpenPosMeasure` — vanish at every point, making `f` constant. `hab` refutes that. Compactness is
used to make the centred square integrable, through `HasCompactSupport.of_compactSpace`.

Stated for any topological measurable space with `OpensMeasurableSpace` and `CompactSpace`; no group
structure is required.

DERIVED: `0` is the level the variance is shown to exceed. -/
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

/-- `0 < variance (reTr (N := m + 2)) (probHaar (SU (m + 2)))` at every `m`. It is
`variance_pos_of_two_values` applied to `continuous_reTr` and `reTr_flipEl_ne_reTr_one m`, the
open-positivity and probability instances coming from `probHaar` on a compact group.

DERIVED: `0` is the level the variance is shown to exceed; `2` is the rank offset in `N = m + 2`. -/
theorem haar_variance_reTr_pos' (m : ℕ) :
    0 < variance (reTr (N := m + 2)) (probHaar (SU (m + 2))) :=
  variance_pos_of_two_values _ continuous_reTr (reTr_flipEl_ne_reTr_one m)

/-- `0 < variance (reTr (N := N)) (probHaar (SU N))` for every `N` with `2 ≤ N`. It is
`haar_variance_reTr_pos'` after rewriting `N` as `m + 2`.

No lattice extent, boundary condition or coupling occurs in the statement; the only parameter is
`N`. The conclusion is non-vanishing, not a lower bound: the proof exhibits no numerical value for
the variance. The hypothesis `2 ≤ N` is required, `haar_variance_reTr_su_one` giving variance `0` at
`N = 1`.

DERIVED: `2` is the smallest rank at which the diagonal witness exists, the rank offset in
`N = m + 2`; `0` is the level the variance is shown to exceed. -/
theorem haar_variance_reTr_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < variance (reTr (N := N)) (probHaar (SU N)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact haar_variance_reTr_pos' m

/-! ### The four-link reduction

The ordered product of independent Haar-distributed elements is again Haar-distributed. Proved
rather than assumed, from left-invariance of the measure alone. -/

/-- `MeasurePreserving (fun p : G × G => p.1 * p.2) (μ.prod μ) μ` for a left-invariant probability
measure `μ` on a measurable group with `MeasurableMul₂`.

`Measure.prod_apply` gives `(μ × μ)((· * ·)⁻¹ t) = ∫⁻ x, μ ((x * ·)⁻¹ t)`, `measure_preimage_mul`
collapses the integrand to the constant `μ t` by left-invariance, and that integrates to `μ t`
because `μ` is a probability measure. Right-invariance, unimodularity and regularity are not used.

DERIVED: `1` and `2` are the two product projections `p.1` and `p.2`. -/
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

/-- The ordered product of four group elements, `p.1 * p.2.1 * p.2.2.1 * p.2.2.2`, left-associated.
Defined for any `Mul`.

DERIVED: `1` and `2` are the product projections that select the four components. -/
def prod4 {G : Type*} [Mul G] (p : G × G × G × G) : G :=
  p.1 * p.2.1 * p.2.2.1 * p.2.2.2

/-- `MeasurePreserving prod4 (μ.prod (μ.prod (μ.prod μ))) μ` for a left-invariant probability
measure `μ`. `prod4` is rewritten as a composite of three multiplications through `mul_assoc`, and
each is `measurePreserving_mul`, so the only invariance used is left-invariance.

DERIVED: no numeral appears in the statement. -/
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

/-- `variance (fun x => f (T x)) ν = variance f μ` for a measure-preserving `T : α → β` and
measurable `f : β → ℝ`. Both the mean and the centred second moment are integrals, and `integral_map`
carries each across; the conclusion is an equality of variances, not an inequality.

DERIVED: no numeral appears in the statement. -/
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

/-- `0 < variance (fun p => reTr (prod4 p)) μ⁴` for `2 ≤ N`, where `μ⁴` is the four-fold product of
`probHaar (SU N)` — the law of four independent Haar-distributed links. Rewriting with
`variance_comp_measurePreserving` applied to `measurePreserving_prod4` reduces it to
`haar_variance_reTr_pos`, so the value is the one-element Haar variance rather than a new constant;
`four_link_variance_eq` states that equality on its own.

Like the one-element form, the statement carries no lattice extent and no coupling.

DERIVED: `2` is the lower bound on the rank, inherited from `haar_variance_reTr_pos`; `0` is the
level the variance is shown to exceed. -/
theorem haar_variance_four_link_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < variance (fun p : SU N × SU N × SU N × SU N => reTr (prod4 p))
      ((probHaar (SU N)).prod
        ((probHaar (SU N)).prod ((probHaar (SU N)).prod (probHaar (SU N))))) := by
  rw [variance_comp_measurePreserving (measurePreserving_prod4 (probHaar (SU N))) measurable_reTr]
  exact haar_variance_reTr_pos hN

/-- The reduction as an equality, at every rank including `N ≤ 1`: the variance of
`fun p => reTr (prod4 p)` under the four-fold product of `probHaar (SU N)` equals the variance of
`reTr` under `probHaar (SU N)`. It is `variance_comp_measurePreserving` at
`measurePreserving_prod4`, and it asserts nothing about either value being positive.

DERIVED: no numeral appears in the statement. -/
theorem four_link_variance_eq {N : ℕ} :
    variance (fun p : SU N × SU N × SU N × SU N => reTr (prod4 p))
        ((probHaar (SU N)).prod
          ((probHaar (SU N)).prod ((probHaar (SU N)).prod (probHaar (SU N)))))
      = variance (reTr (N := N)) (probHaar (SU N)) :=
  variance_comp_measurePreserving (measurePreserving_prod4 (probHaar (SU N))) measurable_reTr

/-! ### The rank hypothesis at `N = 1`

At `N = 1` the determinant condition pins the single entry to `1`, so `reTr` is the constant `1`
(`reTr_su_one`) and the variance is exactly `0` (`haar_variance_reTr_su_one`). The hypothesis
`2 ≤ N` in `haar_variance_reTr_pos` is therefore load-bearing: the conclusion is false at `N = 1`.

DERIVED: `1` is the rank at which the group is trivial and the only possible entry; `2` is the
hypothesis those two theorems show cannot be weakened; `0` is the variance at `N = 1`. -/

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
