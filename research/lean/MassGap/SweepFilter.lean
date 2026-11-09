import Mathlib
import MassGap.ChebyshevFilter

noncomputable section

/-!
# MassGap.SweepFilter — covariance decay at the square root of a sweep gap, with the exact vacuum projection

`ChebyshevFilter.chebyshev_cov` filters a generator `H` whose bound `K` on its range must be uniform. For
the heat bath `H = Σ (id − E_l)` that bound grows with the volume. A symmetrised sweep `S = R*R`,
`R = P_q ⋯ P_1` a product of conditional expectations, has `0 ≤ S ≤ 1` and finite depth, so the filter is
put on `S`. This module states and proves the filter for such an `S`, in the unweighted form and with the
exact projection onto the vacuum (no split `f = f₀ + Hy` is needed).

## Setting

`B` symmetric positive semi-definite, `vac` with `⟨vac, vac⟩ = 1`; `S` form-self-adjoint, `S vac = vac`, and
the gap in second-moment form: for `u ⊥ vac`, `⟨Su, Su⟩ ≤ (1 − δ)⟨Su, u⟩`, `0 < δ < 1`. For `S = R*R` this
follows from the first-moment bound `‖R'v‖² ≤ (1 − δ)‖v‖²` of the reversed product `R' = RR*`, at `v = Ru`.

## What it gives

1. `sweep_contract`: `M = (2/(1 − δ)) S − 1` contracts the vacuum complement.
2. `sweep_filter_contract`: `‖aₙ(M) u‖ ≤ ‖u‖` on the vacuum complement (Pell identity).
3. `sweep_cov`: if `⟨Sⁱ f, g⟩ = ⟨f, g⟩` for every `i ≤ d` (the light cones of `f` and `g` under `d` sweeps do
   not meet), then
   `(⟨f, g⟩ − ⟨f, vac⟩⟨vac, g⟩)² ≤ (2/rᵈ)² ‖f − ⟨f, vac⟩vac‖² ‖g‖²`, `r = (1 + √δ)/(1 − √δ)`
   (`ChebyshevFilter.chebR δ 1`, `≥ 1 + 2√δ`).

The light-cone identity is what the classical form of the Gosset–Huang argument uses: `⟨f, E_l h⟩ = ⟨f, h⟩`
whenever `f` does not read `l` (pull-out and the DLR identity), so projections outside the light cones are
removed one at a time.

DERIVED (module-wide): `0`, `1` the signs, the vacuum normalisation and the bounds of `S`; `2` the factor of
`M`, the squares and the endpoint factor.
-/

namespace MassGap.SweepFilter

open Polynomial MassGap.ChebyshevFilter

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} {S : Module.End ℝ E} {vac : E}

/-- The sweep's contraction polynomial `M = (2/(1 − δ)) X − 1`.

DERIVED: `2`, `1`. -/
def Mswp (δ : ℝ) : ℝ[X] := C (2 / (1 - δ)) * X - 1

/-- Polynomials in `S` keep the vacuum complement.

DERIVED: `0` orthogonality. -/
theorem aeval_orth (hsa : ∀ x y, B (S x) y = B x (S y)) (hvac : S vac = vac) (p : ℝ[X]) {u : E}
    (hu : B u vac = 0) : B (aeval S p u) vac = 0 := by
  rw [aeval_selfAdj B S hsa p]
  have : aeval S p vac = p.eval 1 • vac := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
    | monomial n a =>
      rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial, one_pow,
        mul_one]
      congr 1
      induction n with
      | zero => simp
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hvac, ih]
  rw [this, LinearMap.map_smul, hu, smul_zero]

#print axioms aeval_orth

/-- `p(S) vac = p(1) vac`.

DERIVED: `1` the eigenvalue. -/
theorem aeval_vac (hvac : S vac = vac) (p : ℝ[X]) : aeval S p vac = p.eval 1 • vac := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial, one_pow,
      mul_one]
    congr 1
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hvac, ih]

#print axioms aeval_vac

/-- **The sweep contraction**: `‖M u‖² ≤ ‖u‖²` on the vacuum complement.

DERIVED: `2`, `4` from `M = (2/(1−δ))S − 1`. -/
theorem sweep_contract (hsa : ∀ x y, B (S x) y = B x (S y)) {δ : ℝ} (hδ1 : δ < 1)
    (hgap : ∀ u, B u vac = 0 → B (S u) (S u) ≤ (1 - δ) * B (S u) u) {u : E} (hu : B u vac = 0) :
    B (aeval S (Mswp δ) u) (aeval S (Mswp δ) u) ≤ B u u := by
  have hMu : aeval S (Mswp δ) u = (2 / (1 - δ)) • S u - u := by
    simp [Mswp, Module.algebraMap_end_apply]
  rw [hMu]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hsym : B u (S u) = B (S u) u := by rw [← hsa]
  have h := hgap u hu
  have h1δ : 0 < 1 - δ := by linarith
  rw [hsym]
  have key : 2 / (1 - δ) * (2 / (1 - δ) * B (S u) (S u) - B (S u) u)
      - (2 / (1 - δ) * B (S u) u - B u u) - B u u
      = 4 / (1 - δ) ^ 2 * (B (S u) (S u) - (1 - δ) * B (S u) u) := by
    field_simp
    ring
  have hneg : 4 / (1 - δ) ^ 2 * (B (S u) (S u) - (1 - δ) * B (S u) u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

#print axioms sweep_contract

/-- **The filter contracts on the vacuum complement**: `‖aₙ(M) u‖ ≤ ‖u‖`.

DERIVED: `2` the Pell squares. -/
theorem sweep_filter_contract (hsa : ∀ x y, B (S x) y = B x (S y)) (hvac : S vac = vac) {δ : ℝ}
    (hδ1 : δ < 1) (hgap : ∀ u, B u vac = 0 → B (S u) (S u) ≤ (1 - δ) * B (S u) u) (n : ℕ)
    {u : E} (hu : B u vac = 0) :
    B (aeval S ((chebA n).comp (Mswp δ)) u) (aeval S ((chebA n).comp (Mswp δ)) u) ≤ B u u := by
  set Np := (chebA n).comp (Mswp δ)
  set Wp := (chebB n).comp (Mswp δ)
  set Mp := Mswp δ
  have hpell : Np * Np = 1 + Mp * Mp * (Wp * Wp) - Wp * Wp := by
    have h := congrArg (fun p => p.comp Mp) (cheb_pell n)
    simp only [sub_comp, mul_comp, pow_comp, X_comp, one_comp] at h
    linear_combination h
  have hcompa : ∀ (p q : ℝ[X]) (v : E), aeval S p (aeval S q v) = aeval S (p * q) v := by
    intro p q v; rw [map_mul, Module.End.mul_apply]
  set w := aeval S Wp u
  have hw : B w vac = 0 := aeval_orth hsa hvac Wp hu
  have e1 : B (aeval S Np u) (aeval S Np u) = B u (aeval S (Np * Np) u) := aeval_move B S hsa Np Np u u
  have e3 : B (aeval S Mp w) (aeval S Mp w) = B u (aeval S (Mp * Mp * (Wp * Wp)) u) := by
    rw [show w = aeval S Wp u from rfl, hcompa, aeval_move B S hsa,
      show Mp * Wp * (Mp * Wp) = Mp * Mp * (Wp * Wp) by ring]
  have e4 : B w w = B u (aeval S (Wp * Wp) u) := aeval_move B S hsa Wp Wp u u
  have hcon := sweep_contract hsa hδ1 hgap hw
  rw [e1, hpell, map_sub, map_add, map_one, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.map_sub, LinearMap.map_add, ← e3, ← e4]
  linarith

#print axioms sweep_filter_contract

/-- **Covariance decay through the sweep.** See the module docstring, item 3.

DERIVED: `2` the endpoint factor and the squares; `1` the vacuum normalisation and the upper bound of
`S`; `0` the lower end of `i`. -/
theorem sweep_cov (hsymm : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (S x) y = B x (S y)) (hvac : S vac = vac) (hnorm : B vac vac = 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : ∀ u, B u vac = 0 → B (S u) (S u) ≤ (1 - δ) * B (S u) u) (d : ℕ) {f g : E}
    (hloc : ∀ i, i ≤ d → B ((S ^ i) f) g = B f g) :
    (B f g - B f vac * B vac g) ^ 2
      ≤ (2 / chebR δ 1 ^ d) ^ 2 * B (f - B f vac • vac) (f - B f vac • vac) * B g g := by
  set fp := f - B f vac • vac with hfp
  have hfp0 : B fp vac = 0 := by
    rw [hfp, LinearMap.map_sub, LinearMap.map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hnorm, mul_one, sub_self]
  -- the filter polynomial in S
  have h1d : (1 - δ) ≠ 0 := by linarith
  have hα : (1 + δ) / (1 - δ) = 2 / (1 - δ) - 1 := by field_simp; ring
  have hα1 : 1 ≤ (1 + δ) / (1 - δ) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hAge := chebA_eval_ge hα1 d
  obtain ⟨A, hA⟩ : ∃ A, A = (chebA d).eval ((1 + δ) / (1 - δ)) := ⟨_, rfl⟩
  rw [← hA] at hAge
  have hAge' : chebR δ 1 ^ d / 2 ≤ A := hAge
  have hr : 0 < chebR δ 1 := by unfold chebR; positivity
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hAge'
  set P := C (1 / A) * (chebA d).comp (Mswp δ) with hP
  have hP1 : P.eval 1 = 1 := by
    simp only [hP, eval_mul, eval_C, eval_comp, Mswp, eval_sub, eval_X, eval_one, mul_one]
    rw [← hα, ← hA]; field_simp
  -- degree ≤ d
  have hdegM : (Mswp δ).natDegree ≤ 1 := by
    unfold Mswp
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hdegP : P.natDegree ≤ d := (natDegree_C_mul_le _ _).trans
    (natDegree_comp_le.trans (by nlinarith [(natDegree_cheb d).1]))
  -- locality: ⟨P(S) f, g⟩ = P(1) ⟨f, g⟩ = ⟨f, g⟩
  have hPf : B (aeval S P f) g = B f g := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hdegP)]
    simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [hloc i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))])]
    have hs : ∑ i ∈ Finset.range d.succ, P.coeff i = 1 := by
      rw [← hP1, eval_eq_sum_range' (Nat.lt_succ_of_le hdegP)]
      simp
    rw [← Finset.sum_mul, hs, one_mul]
  have hPvac : aeval S P vac = vac := by rw [aeval_vac hvac, hP1, one_smul]
  -- ⟨f, g⟩ − ⟨f, vac⟩⟨vac, g⟩ = ⟨P(S) fp, g⟩
  have hcov : B f g - B f vac * B vac g = B (aeval S P fp) g := by
    rw [hfp, map_sub, map_smul, hPvac, LinearMap.map_sub, LinearMap.map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hPf]
  -- the bound
  have hcs := form_cs B hsymm hpsd (aeval S P fp) g
  have hnorm' : B (aeval S P fp) (aeval S P fp)
      = (1 / A) ^ 2 * B (aeval S ((chebA d).comp (Mswp δ)) fp)
          (aeval S ((chebA d).comp (Mswp δ)) fp) := by
    rw [hP, map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hfc := sweep_filter_contract hsa hvac hδ1 hgap d hfp0
  have hinvA : 1 / A ≤ 2 / chebR δ 1 ^ d := by
    rw [div_le_div_iff₀ hApos (by positivity)]
    linarith [hAge']
  have hinvA0 : 0 ≤ 1 / A := by positivity
  have hsq : (1 / A) ^ 2 ≤ (2 / chebR δ 1 ^ d) ^ 2 := pow_le_pow_left₀ hinvA0 hinvA 2
  have hg0 := hpsd g
  have hf0 := hpsd fp
  rw [hcov]
  calc B (aeval S P fp) g ^ 2 ≤ B (aeval S P fp) (aeval S P fp) * B g g := hcs
    _ = (1 / A) ^ 2 * B (aeval S ((chebA d).comp (Mswp δ)) fp)
          (aeval S ((chebA d).comp (Mswp δ)) fp) * B g g := by rw [hnorm']
    _ ≤ (1 / A) ^ 2 * B fp fp * B g g := by gcongr
    _ ≤ (2 / chebR δ 1 ^ d) ^ 2 * B fp fp * B g g := by gcongr

#print axioms sweep_cov

end MassGap.SweepFilter
