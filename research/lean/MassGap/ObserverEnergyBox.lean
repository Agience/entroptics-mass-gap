import Mathlib
import MassGap.ObserverEnergyMoments

noncomputable section

/-!
# MassGap.ObserverEnergyBox — E for the energy density as the moments of the energy in a cube

`ObserverEnergyMoments` §8 reduces E for the class-scaled observer `energyOn W D` to bounded even
moments of every smeared field of `D`, for every test function. This file removes the test function.

## The canonical factors cancel

At spacing `a` the smeared scaled field is
`smear a (a⁻⁴ (F − s)) g = ∑_x a⁴ g(a x) · a⁻⁴ (F ∘ T_x − s) = ∑_x g(a x) (F ∘ T_x − s)`
(`smear_scaled_apply`): an unweighted lattice sum of the bounded local readings `F ∘ T_x`, about
`(2R/a)⁴` of them. For a field `F ≥ 0` (the plaquette density `1 − ½ Re tr U_p` is one) and `|g| ≤ M`
supported in `[-R, R]⁴`, the sum is dominated by `M` times the **cube energy**
`cubeSum a R F = ∑_{a x ∈ [-R, R]⁴} F ∘ T_x` plus the subtraction's total `M (2R + 3)⁴ |s|/a⁴`
(`abs_smear_scaled_le`). Conversely the cube energy is the smeared field against the indicator of the
cube, which is a test function (`cubeTest`), up to the same subtraction term
(`cubeSum_le_abs_smear`).

## The reduction

`CubeMomentBound hN W O`: for every `R ≥ 0` and `p`, the `2p`-th moment of the observer's cube energy
`cubeSum a_k R (O ∘ V_k)` is bounded eventually in the step. `ScaledSubtractionBound`: `|s_k O| ≤ S a_k⁴`
(true for `s = 0`). For a class `D` of non-negative fields with that subtraction,
`smearedMoments_iff_cubeMoments` proves that the smeared moment input of `ObserverEnergyMoments` §8 holds
exactly when `CubeMomentBound` does on `D`, so the reduction loses nothing.
`observer_energyOn_clay_of_cubeMoments` is the capstone on it.

Sufficient forms: one exponential moment per cube (`CubeExpBound`, `cubeMomentBound_of_exp`, by
`x^n ≤ n! t^{-n} e^{tx}`), the zoom band on the cube moments (`CubeZoomBand`), and the zoom band on one
exponential moment (`CubeExpZoomBand`: one inequality per cube and step).

## The plaquette class

`PlaqClass N`: the plaquette densities and their reflections. It is reflection closed
(`plaqClass_refl`) and non-negative (`plaqClass_nonneg`), so with `s = 0`
`observer_plaq_clay_of_cubeMoments` leaves one input: `CubeMomentBound` for each field of the class.
-/

namespace MassGap.ObserverEnergyBox

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments Filter
open scoped Topology

/-! ## 1. Moments through a state -/

section StateMoments

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **An even power of a sum of two non-negative bounds**: `|u| ≤ X + Y` gives
`u^{2p} ≤ 2^{2p} (X^{2p} + Y^{2p})`. `X + Y ≤ 2 max(X, Y)` and `max^{2p}` is one of the two powers.

DERIVED: `2` is the factor in `X + Y ≤ 2 max(X, Y)` and makes the power even; `0` the signs. -/
theorem pow_le_two_pow_add {u X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : |u| ≤ X + Y) (p : ℕ) :
    u ^ (2 * p) ≤ 2 ^ (2 * p) * (X ^ (2 * p) + Y ^ (2 * p)) := by
  have hq : Even (2 * p) := even_two_mul p
  have hmax : X + Y ≤ 2 * max X Y := by
    have h1 := le_max_left X Y
    have h2 := le_max_right X Y
    linarith
  have hm : max X Y ^ (2 * p) ≤ X ^ (2 * p) + Y ^ (2 * p) := by
    rcases le_total X Y with hxy | hxy
    · rw [max_eq_right hxy]; linarith [pow_nonneg hX (2 * p)]
    · rw [max_eq_left hxy]; linarith [pow_nonneg hY (2 * p)]
  calc u ^ (2 * p) = |u| ^ (2 * p) := (hq.pow_abs u).symm
    _ ≤ (2 * max X Y) ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg u) (h.trans hmax) _
    _ = 2 ^ (2 * p) * max X Y ^ (2 * p) := mul_pow _ _ _
    _ ≤ 2 ^ (2 * p) * (X ^ (2 * p) + Y ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (by norm_num) _)

#print axioms pow_le_two_pow_add

/-- **A pointwise affine domination passes to the even moments**: `|G| ≤ K |B| + c` everywhere, with
`K, c ≥ 0`, gives `ν(G^{2p}) ≤ 2^{2p} (K^{2p} ν(B^{2p}) + c^{2p})` in every state.

DERIVED: `2` is `pow_le_two_pow_add`'s; `1` the unit observable; `0` the signs. -/
theorem state_pow_le_of_abs_le (ν : MassGap.DLRLimit.State X) (G B : C(X, ℝ)) {K c : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c) (h : ∀ U, |G U| ≤ K * |B U| + c) (p : ℕ) :
    ν (G ^ (2 * p)) ≤ 2 ^ (2 * p) * (K ^ (2 * p) * ν (B ^ (2 * p)) + c ^ (2 * p)) := by
  have hq : Even (2 * p) := even_two_mul p
  have hmono : ν (G ^ (2 * p)) ≤ ν ((2 ^ (2 * p) * K ^ (2 * p)) • B ^ (2 * p)
      + (2 ^ (2 * p) * c ^ (2 * p)) • (1 : C(X, ℝ))) := by
    refine ν.mono (fun U => ?_)
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.pow_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    have h1 := pow_le_two_pow_add (mul_nonneg hK (abs_nonneg (B U))) hc (h U) p
    rw [mul_pow, hq.pow_abs] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  rw [ν.map_add, ν.map_smul, ν.map_smul, ν.map_one] at hmono
  calc ν (G ^ (2 * p)) ≤ _ := hmono
    _ = 2 ^ (2 * p) * (K ^ (2 * p) * ν (B ^ (2 * p)) + c ^ (2 * p)) := by ring

#print axioms state_pow_le_of_abs_le

/-- The exponential of an observable, as an observable.

DERIVED: no numeral. -/
def expC (G : C(X, ℝ)) : C(X, ℝ) := (⟨Real.exp, Real.continuous_exp⟩ : C(ℝ, ℝ)).comp G

/-- DERIVED: no numeral. -/
@[simp] theorem expC_apply (G : C(X, ℝ)) (U : X) : expC G U = Real.exp (G U) := rfl

/-- **Every moment of a non-negative observable from one exponential moment**: for `B ≥ 0` and
`t > 0`, `ν(Bⁿ) ≤ n! t⁻ⁿ ν(e^{tB})`, from `xⁿ/n! ≤ eˣ` at `x = tB`.

DERIVED: `0` the signs of `B` and `t`. -/
theorem state_pow_le_exp (ν : MassGap.DLRLimit.State X) (B : C(X, ℝ)) (hB : ∀ U, 0 ≤ B U)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ν (B ^ n) ≤ ((n.factorial : ℝ) / t ^ n) * ν (expC (t • B)) := by
  have htn : 0 < t ^ n := pow_pos ht n
  have hmono : ν (B ^ n) ≤ ν (((n.factorial : ℝ) / t ^ n) • expC (t • B)) := by
    refine ν.mono (fun U => ?_)
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, expC_apply, smul_eq_mul]
    have h1 := Real.pow_div_factorial_le_exp (t * B U) (mul_nonneg ht.le (hB U)) n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hfac, mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ htn]
    calc B U ^ n * t ^ n = t ^ n * B U ^ n := mul_comm _ _
      _ ≤ Real.exp (t * B U) * (n.factorial : ℝ) := h1
      _ = (n.factorial : ℝ) * Real.exp (t * B U) := mul_comm _ _
  rw [ν.map_smul] at hmono
  exact hmono

#print axioms state_pow_le_exp

end StateMoments

/-! ## 2. The cube indicator and the cube energy -/

section Cube

variable {N : ℕ}

open Classical in
/-- **The indicator of the cube `[-R, R]⁴`.**

DERIVED: `4` is the spacetime dimension; `1` and `0` the indicator's values. -/
def cubeInd (R : ℝ) (y : Fin 4 → ℝ) : ℝ := if ∀ i, |y i| ≤ R then 1 else 0

/-- DERIVED: `0` the lower value. -/
theorem cubeInd_nonneg (R : ℝ) (y : Fin 4 → ℝ) : 0 ≤ cubeInd R y := by
  unfold cubeInd; split_ifs <;> norm_num

/-- The cube indicator is a test function: bounded by `1`, supported in `[-R, R]⁴`.

DERIVED: `1` the bound; `0` the sign of `R` and the value off the cube. -/
theorem isTest_cubeInd {R : ℝ} (hR : 0 ≤ R) : IsTest (cubeInd R) R 1 := by
  refine ⟨hR, fun y => ?_, fun y hy i => ?_⟩
  · unfold cubeInd; split_ifs <;> norm_num
  · unfold cubeInd at hy
    split_ifs at hy with h
    · exact h i
    · exact absurd rfl hy

/-- **The cube indicator as a test function.**

DERIVED: `0` the sign of `R`; `1` the bound. -/
def cubeTest (R : ℝ) (hR : 0 ≤ R) : TestFn := ⟨cubeInd R, R, 1, isTest_cubeInd hR⟩

/-- **A test function is dominated by its bound times the cube indicator**: `|f| ≤ M · 1_{[-R,R]⁴}`.

DERIVED: `0` the value off the support; `1` the indicator on the cube. -/
theorem abs_le_mul_cubeInd {f : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (hf : IsTest f R M) (y : Fin 4 → ℝ) :
    |f y| ≤ M * cubeInd R y := by
  unfold cubeInd
  split_ifs with h
  · rw [mul_one]; exact hf.2.1 y
  · have h0 : f y = 0 := by
      by_contra hne
      exact h (hf.2.2 y hne)
    rw [h0, abs_zero, mul_zero]

#print axioms abs_le_mul_cubeInd

/-- **The number of lattice sites in the cube, in physical units**: at `0 < a ≤ 1`,
`∑_{x ∈ box ⌈R/a⌉} 1_{[-R,R]⁴}(a x) ≤ (2R + 3)⁴ / a⁴` (`ContinuumNontrivial.riemann_le` at the
indicator).

DERIVED: `2`, `3`, `4` are `riemann_le`'s; `1` the indicator's bound and the spacing bound; `0` the sign
of `a`. -/
theorem sum_cubeInd_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) ≤ (2 * R + 3) ^ 4 / a ^ 4 := by
  have h := ContinuumNontrivial.riemann_le ha ha1 (isTest_cubeInd hR)
  rw [← Finset.mul_sum, one_mul] at h
  rw [le_div_iff₀ (pow_pos ha 4), mul_comm]
  exact h

#print axioms sum_cubeInd_le

/-- **The cube energy**: `∑_{x ∈ box ⌈R/a⌉} 1_{[-R,R]⁴}(a x) · F ∘ T_x`, the sum of the local reading
`F` over the lattice sites in the physical cube `[-R, R]⁴`, with no cell-volume weight.

DERIVED: `4` is the spacetime dimension. -/
def cubeSum (a R : ℝ) (F : C(Cfg N, ℝ)) : C(Cfg N, ℝ) :=
  ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) • transObs x F

/-- DERIVED: no numeral. -/
theorem cubeSum_apply (a R : ℝ) (F : C(Cfg N, ℝ)) (U : Cfg N) :
    cubeSum a R F U = ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U) := by
  unfold cubeSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
    smul_eq_mul]

/-- The cube energy of a non-negative reading is non-negative.

DERIVED: `0` the sign. -/
theorem cubeSum_nonneg (a R : ℝ) {F : C(Cfg N, ℝ)} (hF : ∀ U, 0 ≤ F U) (U : Cfg N) :
    0 ≤ cubeSum a R F U := by
  rw [cubeSum_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (cubeInd_nonneg _ _) (hF _))

#print axioms cubeSum_nonneg

/-- **The canonical factors cancel in a smeared scaled field**:
`smear a (a⁻⁴ (F − s)) g = ∑_x g(a x) (F ∘ T_x − s)`, the cell volume `a⁴` of the smearing against the
canonical factor `a⁻⁴`.

DERIVED: `4` is the cell-volume exponent and the canonical dimension; `0` the sign of `a`; `1` the unit
observable. -/
theorem smear_scaled_apply {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (s : ℝ) (g : TestFn) {R M : ℝ}
    (hg : IsTest g.1 R M) (U : Cfg N) :
    smear a ((a ^ 4)⁻¹ • (F - s • (1 : C(Cfg N, ℝ)))) g U
      = ∑ x ∈ box ⌈R / a⌉₊, g.1 (site a x) * (F (transConf x U) - s) := by
  rw [smear_eq_sum ha _ g hg (subset_refl _)]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha.ne'
  calc a ^ 4 * g.1 (site a x) * ((a ^ 4)⁻¹ * (F (transConf x U) - s))
      = (a ^ 4 * (a ^ 4)⁻¹) * (g.1 (site a x) * (F (transConf x U) - s)) := by ring
    _ = g.1 (site a x) * (F (transConf x U) - s) := by rw [mul_inv_cancel₀ h4, one_mul]

#print axioms smear_scaled_apply

/-- **The smeared scaled field is dominated by the cube energy**: for `F ≥ 0`, `|g| ≤ M` supported in
`[-R, R]⁴` and `0 < a ≤ 1`,
`|smear a (a⁻⁴ (F − s)) g| ≤ M · cubeSum a R F + M (2R + 3)⁴ |s|/a⁴` pointwise.

DERIVED: `2`, `3`, `4` are `sum_cubeInd_le`'s; `1` the spacing bound and the unit observable; `0` the
signs. -/
theorem abs_smear_scaled_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) (s : ℝ) (g : TestFn) {R M : ℝ} (hg : IsTest g.1 R M) (U : Cfg N) :
    |smear a ((a ^ 4)⁻¹ • (F - s • (1 : C(Cfg N, ℝ)))) g U|
      ≤ M * cubeSum a R F U + M * (2 * R + 3) ^ 4 * (|s| / a ^ 4) := by
  rw [smear_scaled_apply ha F s g hg U, cubeSum_apply]
  have hM := hg.M_nonneg
  have hI := sum_cubeInd_le ha ha1 hg.1
  have hterm : ∀ x ∈ box ⌈R / a⌉₊, |g.1 (site a x) * (F (transConf x U) - s)|
      ≤ M * cubeInd R (site a x) * (F (transConf x U) + |s|) := by
    intro x _
    rw [abs_mul]
    have h1 : |F (transConf x U) - s| ≤ F (transConf x U) + |s| := by
      have := abs_sub (F (transConf x U)) s
      rwa [abs_of_nonneg (hF _)] at this
    exact mul_le_mul (abs_le_mul_cubeInd hg _) h1 (abs_nonneg _)
      (mul_nonneg hM (cubeInd_nonneg _ _))
  have e : ∑ x ∈ box ⌈R / a⌉₊, M * cubeInd R (site a x) * (F (transConf x U) + |s|)
      = M * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)
        + M * |s| * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have h2 : M * |s| * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x)
      ≤ M * |s| * ((2 * R + 3) ^ 4 / a ^ 4) :=
    mul_le_mul_of_nonneg_left hI (mul_nonneg hM (abs_nonneg s))
  calc |∑ x ∈ box ⌈R / a⌉₊, g.1 (site a x) * (F (transConf x U) - s)|
      ≤ ∑ x ∈ box ⌈R / a⌉₊, |g.1 (site a x) * (F (transConf x U) - s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ box ⌈R / a⌉₊, M * cubeInd R (site a x) * (F (transConf x U) + |s|) :=
        Finset.sum_le_sum hterm
    _ = _ := e
    _ ≤ M * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)
        + M * |s| * ((2 * R + 3) ^ 4 / a ^ 4) := by linarith
    _ = _ := by ring

#print axioms abs_smear_scaled_le

/-- **The cube energy is dominated by the smeared field against the cube**: for `F ≥ 0`, `R ≥ 0` and
`0 < a ≤ 1`, `cubeSum a R F ≤ |smear a (a⁻⁴ (F − s)) 1_{[-R,R]⁴}| + (2R + 3)⁴ |s|/a⁴` pointwise.

DERIVED: `2`, `3`, `4` are `sum_cubeInd_le`'s; `1` the spacing bound and the unit observable; `0` the
signs. -/
theorem cubeSum_le_abs_smear {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (F : C(Cfg N, ℝ)) (s : ℝ)
    {R : ℝ} (hR : 0 ≤ R) (U : Cfg N) :
    cubeSum a R F U ≤ |smear a ((a ^ 4)⁻¹ • (F - s • (1 : C(Cfg N, ℝ)))) (cubeTest R hR) U|
      + (2 * R + 3) ^ 4 * (|s| / a ^ 4) := by
  rw [smear_scaled_apply ha F s (cubeTest R hR) (isTest_cubeInd hR) U, cubeSum_apply]
  have hI := sum_cubeInd_le ha ha1 hR
  have hI0 : 0 ≤ ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) :=
    Finset.sum_nonneg (fun x _ => cubeInd_nonneg _ _)
  have e : ∑ x ∈ box ⌈R / a⌉₊, (cubeTest R hR).1 (site a x) * (F (transConf x U) - s)
      = ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)
        - s * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by
      show cubeInd R (site a x) * (F (transConf x U) - s) = _
      ring)
  rw [e]
  have h1 : s * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x)
      ≤ |s| * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) :=
    mul_le_mul_of_nonneg_right (le_abs_self s) hI0
  have h2 : |s| * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) ≤ |s| * ((2 * R + 3) ^ 4 / a ^ 4) :=
    mul_le_mul_of_nonneg_left hI (abs_nonneg s)
  have h3 := le_abs_self (∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)
    - s * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x))
  have e2 : |s| * ((2 * R + 3) ^ 4 / a ^ 4) = (2 * R + 3) ^ 4 * (|s| / a ^ 4) := by ring
  linarith

#print axioms cubeSum_le_abs_smear

end Cube

/-! ## 3. The smeared moments are the cube moments -/

section Reduction

variable {N : ℕ}

/-- **The cube moment bound of a configuration flow at one field**: for every `R ≥ 0` and `p`, the
`2p`-th moment of the cube energy `cubeSum a_k R (O ∘ V_k)` is bounded eventually in the step. The
reading `O ∘ V_k` carries no canonical factor: the sum counts the observer's energy in the physical
cube `[-R, R]⁴` in lattice units.

DERIVED: `0` is the excluded colour count and the lower end of `R`; `2` makes the power even. -/
def CubeMomentBound (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop,
    stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p)) ≤ C

/-- **The subtraction is of the order of the cell volume**: `|s_k O| ≤ S a_k⁴` eventually. `s = 0`
satisfies it.

DERIVED: `4` is the canonical dimension. -/
def ScaledSubtractionBound (N : ℕ) (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ S : ℝ, ∀ᶠ k in atTop, |s k O| ≤ S * dySpacing N k ^ 4

/-- DERIVED: `0` is the excluded colour count. -/
theorem scaledSubtraction_zero (N : ℕ) (O : LField (MassGap.SUN.SU N)) :
    ScaledSubtractionBound N (fun _ _ => 0) O :=
  ⟨0, Filter.Eventually.of_forall (fun k => by simp)⟩

/-- DERIVED: `4` is the canonical dimension; `0` the sign of `a`. -/
theorem div_le_of_scaledSubtraction {a s S : ℝ} (ha : 0 < a) (h : |s| ≤ S * a ^ 4) :
    |s| / a ^ 4 ≤ |S| := by
  rw [div_le_iff₀ (pow_pos ha 4)]
  exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self S) (pow_pos ha 4).le)

/-- **The class-scaled field on its class**: `a_k⁻⁴ (O ∘ V_k − s_k O)`.

DERIVED: `4` is the canonical dimension; `1` the unit observable. -/
theorem energyOn_map_of_mem (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    {s : ℕ → LField (MassGap.SUN.SU N) → ℝ}
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (k : ℕ) :
    ((energyOn W D hD s hs).map k O).1
      = (dySpacing N k ^ 4)⁻¹ • ((W.fieldMap k O).1 - s k O • (1 : C(Cfg N, ℝ))) := by
  show zOn D k O • ((W.fieldMap k O).1 - sOn D s k O • (1 : C(Cfg N, ℝ))) = _
  rw [zOn_of_mem hO, sOn_of_mem hO]
  rfl

/-- **The smeared moments from the cube moments.** For a class `D` of non-negative fields whose
subtraction is of the order of the cell volume, `CubeMomentBound` on `D` gives the smeared moment input
of `ObserverEnergyMoments.smearedMomentBound_energyOn`: for `f` bounded by `M` with support in
`[-R, R]⁴`, `ν_k(S^{2p}) ≤ 2^{2p}(M^{2p} C + (M (2R + 3)⁴ |S'|)^{2p})`, `C` the cube bound and `S'` the
subtraction's.

DERIVED: `0` is the excluded colour count; `1` the spacing bound and the unit observable; `2`, `3`,
`4` are `abs_smear_scaled_le`'s and `state_pow_le_of_abs_le`'s. -/
theorem smearedMoments_of_cubeMoments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound N s O)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O) :
    ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C := by
  intro O hO f p
  obtain ⟨R, M, hf⟩ := f.2
  have hM := hf.M_nonneg
  have h23 : (0 : ℝ) ≤ (2 * R + 3) ^ 4 := (pow_pos (by linarith [hf.1]) 4).le
  obtain ⟨C, hC⟩ := hcube O hO R hf.1 p
  obtain ⟨S, hS⟩ := hsub O hO
  refine ⟨2 ^ (2 * p) * (M ^ (2 * p) * C + (M * (2 * R + 3) ^ 4 * |S|) ^ (2 * p)), ?_⟩
  filter_upwards [hC, hS, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)]
    with k hCk hSk hk1
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [energyOn_map_of_mem W hD hs hO k]
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hsa := div_le_of_scaledSubtraction ha hSk
  have hc0 : 0 ≤ M * (2 * R + 3) ^ 4 * (|s k O| / dySpacing N k ^ 4) :=
    mul_nonneg (mul_nonneg hM h23) (div_nonneg (abs_nonneg _) (pow_pos ha 4).le)
  have h1 := state_pow_le_of_abs_le (stateK hN k)
    (smear (dySpacing N k) ((dySpacing N k ^ 4)⁻¹ • ((W.fieldMap k O).1
      - s k O • (1 : C(Cfg N, ℝ)))) f)
    (cubeSum (dySpacing N k) R (W.fieldMap k O).1) hM hc0
    (fun U => by
      rw [abs_of_nonneg (cubeSum_nonneg _ _ hF U)]
      exact abs_smear_scaled_le ha hk1.le _ hF (s k O) f hf U) p
  refine h1.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hCk (pow_nonneg hM _)) (pow_le_pow_left₀ hc0 ?_ _))
    (pow_nonneg (by norm_num) _))
  exact mul_le_mul_of_nonneg_left hsa (mul_nonneg hM h23)

#print axioms smearedMoments_of_cubeMoments

/-- **The cube moments from the smeared moments**: the converse, at the cube indicator `cubeTest R`.
Together with `smearedMoments_of_cubeMoments` the two inputs are equivalent on such a class.

DERIVED: `0` is the excluded colour count; `1` the spacing bound, the indicator's bound and the unit
observable; `2`, `3`, `4` are `cubeSum_le_abs_smear`'s and `state_pow_le_of_abs_le`'s. -/
theorem cubeMoments_of_smearedMoments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound N s O)
    (h : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C) :
    ∀ O ∈ D, CubeMomentBound hN W O := by
  intro O hO R hR p
  have h23 : (0 : ℝ) ≤ (2 * R + 3) ^ 4 := (pow_pos (by linarith) 4).le
  obtain ⟨C, hC⟩ := h O hO (cubeTest R hR) p
  obtain ⟨S, hS⟩ := hsub O hO
  refine ⟨2 ^ (2 * p) * (1 ^ (2 * p) * C + ((2 * R + 3) ^ 4 * |S|) ^ (2 * p)), ?_⟩
  filter_upwards [hC, hS, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)]
    with k hCk hSk hk1
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [energyOn_map_of_mem W hD hs hO k] at hCk
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hsa := div_le_of_scaledSubtraction ha hSk
  have hc0 : 0 ≤ (2 * R + 3) ^ 4 * (|s k O| / dySpacing N k ^ 4) :=
    mul_nonneg h23 (div_nonneg (abs_nonneg _) (pow_pos ha 4).le)
  have h1 := state_pow_le_of_abs_le (stateK hN k)
    (cubeSum (dySpacing N k) R (W.fieldMap k O).1)
    (smear (dySpacing N k) ((dySpacing N k ^ 4)⁻¹ • ((W.fieldMap k O).1
      - s k O • (1 : C(Cfg N, ℝ)))) (cubeTest R hR)) zero_le_one hc0
    (fun U => by
      rw [abs_of_nonneg (cubeSum_nonneg _ _ hF U), one_mul]
      exact cubeSum_le_abs_smear ha hk1.le _ (s k O) hR U) p
  refine h1.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hCk (pow_nonneg zero_le_one _)) (pow_le_pow_left₀ hc0 ?_ _))
    (pow_nonneg (by norm_num) _))
  exact mul_le_mul_of_nonneg_left hsa h23

#print axioms cubeMoments_of_smearedMoments

/-- **The smeared moment input is the cube moment input.** On a class `D` of non-negative fields with
subtraction of the order of the cell volume, bounded smeared moments of `energyOn W D` for every test
function hold exactly when the observer's cube energy has bounded moments for every cube.

DERIVED: `0` is the excluded colour count; `2` makes the power even. -/
theorem smearedMoments_iff_cubeMoments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound N s O) :
    (∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
      ↔ ∀ O ∈ D, CubeMomentBound hN W O :=
  ⟨cubeMoments_of_smearedMoments hN W D hD s hs hpos hsub,
    smearedMoments_of_cubeMoments hN W D hD s hs hpos hsub⟩

#print axioms smearedMoments_iff_cubeMoments

/-- **E for the class-scaled flow from the cube moments.**

DERIVED: `0` is the excluded colour count. -/
theorem uniformBoundF_energyOn_of_cubeMoments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound N s O)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O) :
    UniformBoundF hN (energyOn W D hD s hs) :=
  uniformBoundF_of_smearedMomentBound hN _ (smearedMomentBound_energyOn hN W D hD s hs
    (smearedMoments_of_cubeMoments hN W D hD s hs hpos hsub hcube))

#print axioms uniformBoundF_energyOn_of_cubeMoments

end Reduction

/-! ## 4. Sufficient forms: one exponential moment, the zoom -/

section Sufficient

variable {N : ℕ}

/-- **One exponential moment per cube**: for every `R ≥ 0` some `t > 0` has `ν_k(e^{t E_k})` bounded
eventually in the step, `E_k = cubeSum a_k R (O ∘ V_k)`.

DERIVED: `0` is the excluded colour count, the lower end of `R` and of `t`. -/
def CubeExpBound (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop,
    stateK hN k (expC (t • cubeSum (dySpacing N k) R (W.fieldMap k O).1)) ≤ C

/-- **The cube moments from one exponential moment**, for a non-negative field:
`ν_k(E_k^{2p}) ≤ (2p)! t^{-2p} C`.

DERIVED: `0` is the excluded colour count and the sign of the field; `2` makes the power even. -/
theorem cubeMomentBound_of_exp (hN : N ≠ 0) (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (hO : ∀ U, 0 ≤ O.1 U) (h : CubeExpBound hN W O) : CubeMomentBound hN W O := by
  intro R hR p
  obtain ⟨t, C, ht, hC⟩ := h R hR
  refine ⟨((2 * p).factorial : ℝ) / t ^ (2 * p) * C, ?_⟩
  filter_upwards [hC] with k hk
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hO (W.V k U)
  exact (state_pow_le_exp (stateK hN k) _ (cubeSum_nonneg _ _ hF) ht (2 * p)).trans
    (mul_le_mul_of_nonneg_left hk (div_nonneg (by positivity) (pow_pos ht _).le))

#print axioms cubeMomentBound_of_exp

/-- **The zoom band of the cube moments**: for every `R ≥ 0` a summable `δ ≥ 0` with
`ν_{k+1}(E_{k+1}^{2p}) ≤ e^{δ_k} ν_k(E_k^{2p})` for every `p` and `k`.

DERIVED: `0` is the excluded colour count, the lower end of `R` and the sign of `δ`; `1` the next step;
`2` makes the power even. -/
def CubeZoomBand (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ δ : ℕ → ℝ, Summable δ ∧ (∀ k, 0 ≤ δ k) ∧ ∀ (p k : ℕ),
    stateK hN (k + 1) (cubeSum (dySpacing N (k + 1)) R (W.fieldMap (k + 1) O).1 ^ (2 * p))
      ≤ Real.exp (δ k) * stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))

/-- **The cube moments from the zoom band** (`ObserverEnergyMoments.le_of_zoomRatio`).

DERIVED: `0` is the excluded colour count; `2` makes the power even. -/
theorem cubeMomentBound_of_zoomBand (hN : N ≠ 0) (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (h : CubeZoomBand hN W O) : CubeMomentBound hN W O := by
  intro R hR p
  obtain ⟨δ, hsum, hδ0, hstep⟩ := h R hR
  exact ⟨_, Filter.Eventually.of_forall (le_of_zoomRatio
    (fun k => stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))) δ
    (fun k => (stateK hN k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _))
    hsum hδ0 (hstep p))⟩

#print axioms cubeMomentBound_of_zoomBand

/-- **The zoom band of one exponential moment**: for every `R ≥ 0` some `t > 0` and a summable `δ ≥ 0`
with `ν_{k+1}(e^{t E_{k+1}}) ≤ e^{δ_k} ν_k(e^{t E_k})` at every step: one inequality per cube and step.

DERIVED: `0` is the excluded colour count, the lower end of `R` and `t` and the sign of `δ`; `1` the next
step. -/
def CubeExpZoomBand (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ t : ℝ, 0 < t ∧ ∃ δ : ℕ → ℝ, Summable δ ∧ (∀ k, 0 ≤ δ k) ∧ ∀ k : ℕ,
    stateK hN (k + 1) (expC (t • cubeSum (dySpacing N (k + 1)) R (W.fieldMap (k + 1) O).1))
      ≤ Real.exp (δ k) * stateK hN k (expC (t • cubeSum (dySpacing N k) R (W.fieldMap k O).1))

/-- **One exponential moment per cube from its zoom band.**

DERIVED: `0` is the excluded colour count. -/
theorem cubeExpBound_of_zoomBand (hN : N ≠ 0) (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (h : CubeExpZoomBand hN W O) : CubeExpBound hN W O := by
  intro R hR
  obtain ⟨t, ht, δ, hsum, hδ0, hstep⟩ := h R hR
  exact ⟨t, _, ht, Filter.Eventually.of_forall (le_of_zoomRatio
    (fun k => stateK hN k (expC (t • cubeSum (dySpacing N k) R (W.fieldMap k O).1))) δ
    (fun k => (stateK hN k).nonneg _ (fun U => by rw [expC_apply]; exact (Real.exp_pos _).le))
    hsum hδ0 hstep)⟩

#print axioms cubeExpBound_of_zoomBand

end Sufficient

/-! ## 5. The plaquette class and the observer -/

section Plaq

variable {N : ℕ}

/-- Reflection is an involution on local fields.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` the reflection constant. -/
theorem refl_refl (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) : (O.refl τ).refl τ = O :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (LatticeReflection.ireflConf τ 0 (LatticeReflection.ireflConf τ 0 U)) = O.1 U
    rw [LatticeReflection.ireflConf_involutive τ 0 U]))

#print axioms refl_refl

/-- Reflection preserves non-negativity.

DERIVED: `0` the sign and the reflection constant. -/
theorem refl_nonneg {O : LField (MassGap.SUN.SU N)} (hO : ∀ U, 0 ≤ O.1 U) (τ : Fin 4) :
    ∀ U, 0 ≤ (O.refl τ).1 U := fun U => by
  show 0 ≤ O.1 (LatticeReflection.ireflConf τ 0 U)
  exact hO _

/-- A field reflected along a list of directions.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def reflList (l : List (Fin 4)) (O : LField (MassGap.SUN.SU N)) : LField (MassGap.SUN.SU N) :=
  l.foldr (fun τ P => P.refl τ) O

/-- **The plaquette class**: the plaquette densities `1 − (1/N) Re tr U_p` and their reflections.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def PlaqClass (N : ℕ) : Set (LField (MassGap.SUN.SU N)) :=
  {O | ∃ (q : MassGap.GibbsSpec.IPlaq) (l : List (Fin 4)), O = reflList l (plaqField q)}

/-- **The plaquette class is reflection closed.**

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem plaqClass_refl (N : ℕ) :
    ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ PlaqClass N ↔ O ∈ PlaqClass N := by
  intro τ O
  constructor
  · rintro ⟨q, l, h⟩
    refine ⟨q, τ :: l, ?_⟩
    calc O = (O.refl τ).refl τ := (refl_refl τ O).symm
      _ = (reflList l (plaqField q)).refl τ := by rw [h]
      _ = reflList (τ :: l) (plaqField q) := rfl
  · rintro ⟨q, l, h⟩
    exact ⟨q, τ :: l, by rw [h]; rfl⟩

#print axioms plaqClass_refl

/-- **The plaquette class is non-negative**: the Wilson density is at least `0`
(`WilsonAction.wilsonDensity_nonneg`) and reflection keeps the sign.

DERIVED: `0` is the excluded colour count and the sign. -/
theorem plaqClass_nonneg (hN : N ≠ 0) : ∀ O ∈ PlaqClass N, ∀ U, 0 ≤ O.1 U := by
  rintro O ⟨q, l, rfl⟩
  induction l with
  | nil =>
    intro U
    show 0 ≤ MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q U)
    exact MassGap.WilsonAction.wilsonDensity_nonneg hN _
  | cons τ l ih => exact refl_nonneg ih τ

#print axioms plaqClass_nonneg

/-- **The class-scaled observer's continuum statement from its cube moments.** For the localised APE
observer scaled by `a⁻⁴` on a reflection-closed class `D` of non-negative fields with subtraction of
the order of the cell volume: bounded moments of the observer's energy in every physical cube, a
physical range bound, absolute clustering at a window `L > 0` and one non-zero connected pairing give,
at every dyadic step, the reconstructed transfer gapped at physical rate `c'/L` on a space with a
non-zero vector orthogonal to the vacuum.

DERIVED: `2` is the rank; `0` the lower end of `L` and `c'`; `1/6` the dominance bound. -/
theorem observer_energyOn_clay_of_cubeMoments {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6)
    (n R : ℕ → ℕ) (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) {L : ℝ}
    (hL : 0 < L) (hcl : FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L)
    (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) D hD s hs
              hpos hsub hcube) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) D hD s hs
              hpos hsub hcube) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  flow_clay_of_abs_cluster two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
    (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) D hD s hs
      hpos hsub hcube) τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) hL hcl hNT

#print axioms observer_energyOn_clay_of_cubeMoments

/-- **The plaquette energy density's continuum statement from its cube moments.** The observer's
energy density on `PlaqClass 2` with no subtraction: the only E input left is `CubeMomentBound` for
each plaquette density and its reflections — bounded moments of the smoothed Wilson action in every
physical cube.

DERIVED: `2` is the rank; `0` the absent subtraction and the lower end of `L` and `c'`; `1/6` the
dominance bound. -/
theorem observer_plaq_clay_of_cubeMoments {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (hcube : ∀ O ∈ PlaqClass 2, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R (PlaqClass 2) (plaqClass_refl 2) (fun _ _ => 0)
      (fun _ _ _ => rfl)).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hcl : FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R (PlaqClass 2) (plaqClass_refl 2)
      (fun _ _ => 0) (fun _ _ _ => rfl)) τ r L)
    (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R (PlaqClass 2) (plaqClass_refl 2)
      (fun _ _ => 0) (fun _ _ _ => rfl)) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R (PlaqClass 2) (plaqClass_refl 2)
              (fun _ _ => 0) (fun _ _ _ => rfl))
            (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) (PlaqClass 2)
              (plaqClass_refl 2) (fun _ _ => 0) (fun _ _ _ => rfl) (plaqClass_nonneg two_ne)
              (fun O _ => scaledSubtraction_zero 2 O) hcube) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R (PlaqClass 2) (plaqClass_refl 2)
              (fun _ _ => 0) (fun _ _ _ => rfl))
            (uniformBoundF_energyOn_of_cubeMoments two_ne (obsConfFlow c hc0 hc n R) (PlaqClass 2)
              (plaqClass_refl 2) (fun _ _ => 0) (fun _ _ _ => rfl) (plaqClass_nonneg two_ne)
              (fun O _ => scaledSubtraction_zero 2 O) hcube) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  observer_energyOn_clay_of_cubeMoments hc0 hc n R (PlaqClass 2) (plaqClass_refl 2) (fun _ _ => 0)
    (fun _ _ _ => rfl) (plaqClass_nonneg two_ne) (fun O _ => scaledSubtraction_zero 2 O) hcube τ
    hphys hL hcl hNT

#print axioms observer_plaq_clay_of_cubeMoments

end Plaq

end MassGap.ObserverEnergyBox
