import Mathlib
import MassGap.ObserverOSGrowth

noncomputable section

/-!
# MassGap.ObserverOSSchwartz — the growth condition of the observer's energy density in a Schwartz seminorm

`ObserverOSGrowth.abs_contSF_energy0_growth` bounds the Schwinger functions of the energy density
`energy0` by the sup norm times the support volume, `‖g‖_∞ (2R + 1)⁴`. Here the bound is moved to the
weighted sup norm

`‖g‖₅ = sup_y (1 + ‖y‖)⁵ |g(y)|`,

`‖y‖` the sup norm of `ℝ⁴`. That is the zeroth-derivative Schwartz seminorm of order five; it does not
see the support. The Schwinger functions are then extended, by truncation, to every function with
`‖g‖₆ < ∞`, Schwartz functions included.

## The test-function class

`ContinuumField.TestFn` is the class `smear` accepts: bounded functions of bounded support, with no
measurability or continuity condition. `smear` is the lattice Riemann sum `∑_x a⁴ g(a x) T_x F`, so
an indicator cut-off of a bounded function is a test function, and no smooth partition of unity is
needed. A Schwartz function is not a `TestFn`; its Schwinger functions are defined here as the limit of
those of its truncations to the cubes `[-R, R]⁴`, `R → ∞` (`schwSF`).

## Dyadic shells

For `(1 + ‖y‖)⁵ |c| ≤ A` pick `j` with `2^j ≤ 1 + ‖y‖ < 2^{j+1}` (`exists_shell`). Then `y` lies in the
cube `[-2^{j+1}, 2^{j+1}]⁴` and `|c| ≤ A 32^{-j}`, so (`abs_le_sum_shell`)

`|c| ≤ ∑_{j ≤ ⌈R⌉} A 32^{-j} 1_{[-2^{j+1}, 2^{j+1}]⁴}(y)`  for `‖y‖ ≤ R`.

Summed against the non-negative field over the lattice (`abs_smear_energy0_le_shells`), the smeared
energy density is dominated by `A ∑_j 32^{-j} E_{2^{j+1}}`, `E_R` the cube energy. Minkowski's
inequality in `L^{2p}` (`ObserverEnergyCoarseN.state_pow_sum_le`) with the weights
`w_j = 32^{-j} (2·2^{j+1} + 1)⁴` and the cube moments `ν(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} c`
(`ObserverOSGrowth.cubeMoments_of_unitExp`) give (`moment_smear_decay_le`)

`ν((smear g)^{2p}) ≤ c (8192 A)^{2p}`,

because `∑_j w_j ≤ 4096 ∑_j 2^{-j} ≤ 8192` (`sum_shellWeight_le`): the volume `16^j` of the shell is
beaten by the decay `32^{-j}`. The exponent five is the least integer above the dimension four.

## The growth condition

`abs_contSF_energy0_decay`: with one exponential moment of the unit-cube energy
(`ObserverOSGrowth.UnitCubeExpBound`), for every `n` and every family of test functions,

`|S_n(g₁, …, gₙ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 ‖gᵢ‖₅`,

uniformly in the supports. `schwartzGrowth_energy0`: `|S_n| ≤ α γⁿ (n!)² ∏ᵢ 8192 ‖gᵢ‖₅` with
`α = 1 + C`, `γ = 8 (1 + t⁻¹)²`.

## The extension

`Decaying`: functions with `‖g‖₆ < ∞`. `trunc g R = 1_{[-R,R]⁴} g` is a test function. The difference
of two truncations, `R ≤ R'`, has `‖·‖₅ ≤ ‖g‖₆ / (1 + R)` (`decayBound_tail`), and the telescoping form
of Hölder's inequality in a state (`abs_state_prod_sub_le`) gives
`|S_n(trunc_{R'} g) − S_n(trunc_R g)| ≤ K / (1 + R)` (`abs_contSF_trunc_sub_le`). The truncated
Schwinger functions are Cauchy in `R`; `schwSF` is their limit (`tendsto_schwSF`). It satisfies the
same growth bound in `‖·‖₅` (`abs_schwSF_le`), it agrees with `contSF` on test functions
(`schwSF_eq_contSF`), and on a Schwartz function `φ` the norm `‖φ‖_K` is at most
`2^K sup_{(k,l) ≤ (K,0)} p_{k,l}(φ)`, Mathlib's Schwartz seminorms (`decayBound_schwartz`,
`abs_schwSF_schwartz_le`).
-/

namespace MassGap.ObserverOSSchwartz

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyBox
  MassGap.ObserverOS MassGap.ObserverOSGrowth Filter
open scoped Topology

/-! ## 1. The weighted sup norm and the dyadic shells -/

section Shells

/-- **The weighted sup bound** `(1 + ‖y‖)^K |g(y)| ≤ A` at every `y`, `‖y‖` the sup norm of `ℝ⁴`: `A`
bounds the zeroth-derivative Schwartz seminorm of order `K`.

DERIVED: `1` makes the weight at least one; `4` in `Fin 4` is the spacetime dimension. -/
def DecayBound (K : ℕ) (g : (Fin 4 → ℝ) → ℝ) (A : ℝ) : Prop :=
  ∀ y, (1 + ‖y‖) ^ K * |g y| ≤ A

/-- DERIVED: `0` the sign and the evaluation point; `1` the weight's unit term. -/
theorem DecayBound.nonneg {K : ℕ} {g : (Fin 4 → ℝ) → ℝ} {A : ℝ} (h : DecayBound K g A) : 0 ≤ A :=
  (mul_nonneg (pow_nonneg (by positivity) _) (abs_nonneg _)).trans (h 0)

#print axioms DecayBound.nonneg

/-- A weighted bound is a sup bound: the weight is at least one.

DERIVED: `1` the weight's lower bound. -/
theorem DecayBound.abs_le {K : ℕ} {g : (Fin 4 → ℝ) → ℝ} {A : ℝ} (h : DecayBound K g A)
    (y : Fin 4 → ℝ) : |g y| ≤ A := by
  have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ K := one_le_pow₀ (by linarith [norm_nonneg y])
  calc |g y| = 1 * |g y| := (one_mul _).symm
    _ ≤ (1 + ‖y‖) ^ K * |g y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ A := h y

#print axioms DecayBound.abs_le

/-- A weighted bound of order `K'` is one of every lower order `K`.

DERIVED: `1` the weight's lower bound. -/
theorem DecayBound.mono {K K' : ℕ} {g : (Fin 4 → ℝ) → ℝ} {A : ℝ} (hK : K ≤ K')
    (h : DecayBound K' g A) : DecayBound K g A := fun y =>
  (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg y]) hK)
    (abs_nonneg _)).trans (h y)

#print axioms DecayBound.mono

/-- **The dyadic shell of a point**: every `x ≥ 1` has `2^j ≤ x < 2^{j+1}` for some `j`.

DERIVED: `2` the dyadic base; `1` the lower end and the step `j + 1`; `0` the first shell. -/
theorem exists_shell {x : ℝ} (hx : 1 ≤ x) : ∃ j : ℕ, (2 : ℝ) ^ j ≤ x ∧ x < 2 ^ (j + 1) := by
  classical
  have hex : ∃ j : ℕ, x < (2 : ℝ) ^ (j + 1) := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, hm.trans (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self m))⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | j
  · simpa using hx
  · have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    push_neg at hmin
    exact hmin

#print axioms exists_shell

/-- **A weighted bound splits over the dyadic cubes**: if `(1 + ‖y‖)⁵ |c| ≤ A` and `‖y‖ ≤ R`, then
`|c| ≤ ∑_{j < ⌈R⌉ + 1} A 32^{-j} 1_{[-2^{j+1}, 2^{j+1}]⁴}(y)`. The shell `j` of `1 + ‖y‖` gives one
term with indicator `1` and `|c| ≤ A / (2^j)⁵`; it has `j < ⌈R⌉ + 1` because `2^j ≤ 1 + R < 2^{⌈R⌉+1}`.

DERIVED: `5` the weight's exponent; `32 = 2⁵` the decay over one dyadic shell; `2`, `1` the shell
`2^j ≤ 1 + ‖y‖ < 2^{j+1}` and the cube side `2^{j+1}`; `0` the sign of the terms. -/
theorem abs_le_sum_shell {y : Fin 4 → ℝ} {c A R : ℝ} (h : (1 + ‖y‖) ^ 5 * |c| ≤ A)
    (hy : ‖y‖ ≤ R) :
    |c| ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) y := by
  have hy0 := norm_nonneg y
  have hA : 0 ≤ A := (mul_nonneg (by positivity) (abs_nonneg c)).trans h
  obtain ⟨j, hj1, hj2⟩ := exists_shell (show (1 : ℝ) ≤ 1 + ‖y‖ by linarith)
  have hjJ : j ∈ Finset.range (⌈R⌉₊ + 1) := by
    rw [Finset.mem_range]
    have h1 : (2 : ℝ) ^ j ≤ 1 + R := hj1.trans (by linarith)
    have h2 : 1 + R ≤ (⌈R⌉₊ : ℝ) + 1 := by linarith [Nat.le_ceil R]
    have h3 : ((⌈R⌉₊ + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (⌈R⌉₊ + 1) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h4 : (2 : ℝ) ^ j < 2 ^ (⌈R⌉₊ + 1) := by push_cast at h3; linarith
    exact (pow_lt_pow_iff_right₀ (by norm_num)).mp h4
  have hind : cubeInd ((2 : ℝ) ^ (j + 1)) y = 1 := by
    unfold cubeInd
    rw [if_pos]
    intro i
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    linarith
  have hterm : |c| ≤ A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) y := by
    rw [hind, mul_one]
    have h32 : ((2 : ℝ) ^ j) ^ 5 = 32 ^ j := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h5 : ((2 : ℝ) ^ j) ^ 5 * |c| ≤ A :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hj1 5) (abs_nonneg c)).trans h
    rw [h32] at h5
    rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), mul_comm]
    exact h5
  exact hterm.trans (Finset.single_le_sum
    (f := fun j => A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) y)
    (fun j _ => mul_nonneg (mul_nonneg hA (by positivity)) (cubeInd_nonneg _ _)) hjJ)

#print axioms abs_le_sum_shell

/-- **The weight of the shell `j`**: its decay `32^{-j}` times the volume factor `(2·2^{j+1} + 1)⁴` of
the cube `[-2^{j+1}, 2^{j+1}]⁴`.

DERIVED: `32 = 2⁵` the decay of order five over a shell; `2`, `1`, `4` the volume factor `(2R + 1)⁴`
of `ObserverOSGrowth.state_cubeSum_pow_le` at `R = 2^{j+1}`. -/
def shellWeight (j : ℕ) : ℝ := (1 / 32) ^ j * (2 * (2 : ℝ) ^ (j + 1) + 1) ^ 4

/-- `w_j ≤ 4096 · 2^{-j}`: `2·2^{j+1} + 1 ≤ 8·2^j`, `8⁴ = 4096` and `16/32 = 1/2`.

DERIVED: `8 = 2³` bounds `2·2^{j+1} + 1` by `2^{j+3}`; `4096 = 8⁴`; `16 = 2⁴` the volume of one
doubling in four dimensions; `1/2 = 16/32`. -/
theorem shellWeight_le (j : ℕ) : shellWeight j ≤ 4096 * (1 / 2) ^ j := by
  have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2 : 2 * (2 : ℝ) ^ (j + 1) + 1 ≤ 8 * 2 ^ j := by rw [pow_succ]; linarith
  have h3 : (2 * (2 : ℝ) ^ (j + 1) + 1) ^ 4 ≤ (8 * 2 ^ j) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h2 4
  have h4 : (8 * (2 : ℝ) ^ j) ^ 4 = 4096 * 16 ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 4, pow_mul]; norm_num
  have h5 : ((1 : ℝ) / 32) ^ j * 16 ^ j = (1 / 2) ^ j := by
    rw [← mul_pow]; norm_num
  unfold shellWeight
  calc ((1 : ℝ) / 32) ^ j * (2 * (2 : ℝ) ^ (j + 1) + 1) ^ 4
      ≤ (1 / 32) ^ j * (4096 * 16 ^ j) := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 4096 * (1 / 2) ^ j := by rw [← h5]; ring

#print axioms shellWeight_le

/-- **The shell weights are summable**: `∑_{j < J} w_j ≤ 8192`, uniformly in `J`.

DERIVED: `8192 = 4096 · 2`, `2` the geometric sum `∑ 2^{-j} ≤ 2`. -/
theorem sum_shellWeight_le (J : ℕ) : ∑ j ∈ Finset.range J, shellWeight j ≤ 8192 := by
  calc ∑ j ∈ Finset.range J, shellWeight j
      ≤ ∑ j ∈ Finset.range J, 4096 * ((1 : ℝ) / 2) ^ j :=
        Finset.sum_le_sum (fun j _ => shellWeight_le j)
    _ = 4096 * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j := by rw [Finset.mul_sum]
    _ ≤ 4096 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le J) (by norm_num)
    _ = 8192 := by norm_num

#print axioms sum_shellWeight_le

/-- DERIVED: `0` the sign. -/
theorem shellWeight_pos (j : ℕ) : 0 < shellWeight j := by
  unfold shellWeight; positivity

#print axioms shellWeight_pos

end Shells

/-! ## 2. The smeared energy density against a decaying test function -/

section Moments

variable {N : ℕ}

/-- **A sum of cube-indicator weights over any set of sites is at most the cube energy**, for `F ≥ 0`:
the sites with indicator one lie in the box `[-⌊R/a⌋, ⌊R/a⌋]⁴`
(`ObserverOSGrowth.mem_box_floor`, `ObserverOSGrowth.boxSum_le_cubeSum`).

DERIVED: `0` the sign of `a`, `R`, `F`; `1` the indicator on the cube. -/
theorem sum_cubeInd_le_cubeSum {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) (s : Finset ISite) (U : Cfg N) :
    ∑ x ∈ s, cubeInd R (site a x) * F (transConf x U) ≤ cubeSum a R F U := by
  classical
  have e : ∑ x ∈ s, cubeInd R (site a x) * F (transConf x U)
      = ∑ x ∈ s.filter (fun x => ∀ i, |site a x i| ≤ R), F (transConf x U) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold cubeInd
    split_ifs <;> simp
  rw [e]
  refine le_trans ?_ (boxSum_le_cubeSum ha hR F hF U)
  rw [boxSum_apply]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hF _)
  exact mem_box_floor ha hR (Finset.mem_filter.mp hx).2

#print axioms sum_cubeInd_le_cubeSum

/-- **The smeared energy density is dominated by the dyadic cube energies**: for `O ∈ D` non-negative
and a test function `g` supported in `[-R, R]⁴` with `‖g‖₅ ≤ A`, at every step,
`|smear a_k (a_k⁻⁴ O ∘ V_k) g| ≤ ∑_{j < ⌈R⌉ + 1} A 32^{-j} cubeSum a_k 2^{j+1} (O ∘ V_k)` pointwise
(`ObserverEnergyBox.smear_scaled_apply` at `s = 0`, `abs_le_sum_shell`, `sum_cubeInd_le_cubeSum`).

DERIVED: `0` is the excluded colour count, the zero subtraction and the vanishing value; `5`, `32`,
`2`, `1` are `abs_le_sum_shell`'s; `4` in `Fin 4` is the spacetime dimension. -/
theorem abs_smear_energy0_le_shells (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (k : ℕ)
    (f : TestFn) {R M A : ℝ} (hRM : IsTest f.1 R M) (hf : DecayBound 5 f.1 A) (U : Cfg N) :
    |smear (dySpacing N k) ((energy0 W D hD).map k O).1 f U|
      ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1),
          A * (1 / 32) ^ j * cubeSum (dySpacing N k) ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1 U := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hA := hf.nonneg
  have hmap : ((energy0 W D hD).map k O).1
      = (dySpacing N k ^ 4)⁻¹ • ((W.fieldMap k O).1 - (0 : ℝ) • (1 : C(Cfg N, ℝ))) := by
    rw [energy0, energyOn_map_of_mem W hD (s0_refl N) hO k]
    rfl
  rw [hmap, smear_scaled_apply ha (W.fieldMap k O).1 0 f hRM U]
  have hterm : ∀ x ∈ box ⌈R / dySpacing N k⌉₊,
      |f.1 (site (dySpacing N k) x) * ((W.fieldMap k O).1 (transConf x U) - 0)|
        ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j
            * (cubeInd ((2 : ℝ) ^ (j + 1)) (site (dySpacing N k) x)
              * (W.fieldMap k O).1 (transConf x U)) := by
    intro x _
    rw [sub_zero, abs_mul, abs_of_nonneg (hF _)]
    have hsh : |f.1 (site (dySpacing N k) x)| ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1),
        A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) (site (dySpacing N k) x) := by
      by_cases h0 : f.1 (site (dySpacing N k) x) = 0
      · rw [h0, abs_zero]
        exact Finset.sum_nonneg
          (fun j _ => mul_nonneg (mul_nonneg hA (by positivity)) (cubeInd_nonneg _ _))
      · refine abs_le_sum_shell (hf _) ?_
        refine (pi_norm_le_iff_of_nonneg hRM.1).mpr (fun i => ?_)
        rw [Real.norm_eq_abs]
        exact hRM.2.2 _ h0 i
    calc |f.1 (site (dySpacing N k) x)| * (W.fieldMap k O).1 (transConf x U)
        ≤ (∑ j ∈ Finset.range (⌈R⌉₊ + 1),
            A * (1 / 32) ^ j * cubeInd ((2 : ℝ) ^ (j + 1)) (site (dySpacing N k) x))
            * (W.fieldMap k O).1 (transConf x U) := mul_le_mul_of_nonneg_right hsh (hF _)
      _ = _ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
  calc |∑ x ∈ box ⌈R / dySpacing N k⌉₊,
          f.1 (site (dySpacing N k) x) * ((W.fieldMap k O).1 (transConf x U) - 0)|
      ≤ ∑ x ∈ box ⌈R / dySpacing N k⌉₊,
          |f.1 (site (dySpacing N k) x) * ((W.fieldMap k O).1 (transConf x U) - 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ box ⌈R / dySpacing N k⌉₊, ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j
            * (cubeInd ((2 : ℝ) ^ (j + 1)) (site (dySpacing N k) x)
              * (W.fieldMap k O).1 (transConf x U)) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (⌈R⌉₊ + 1), A * (1 / 32) ^ j
            * ∑ x ∈ box ⌈R / dySpacing N k⌉₊, cubeInd ((2 : ℝ) ^ (j + 1)) (site (dySpacing N k) x)
              * (W.fieldMap k O).1 (transConf x U) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (sum_cubeInd_le_cubeSum ha (by positivity) _ hF _ U) (mul_nonneg hA (by positivity)))

#print axioms abs_smear_energy0_le_shells

/-- **The moments of the smeared energy density against a decaying test function**: if at step `k`
every cube has `ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} c`, `c ≥ 0`, `p ≥ 1`, then for every test function with
`‖g‖₅ ≤ A`, `ν_k((smear g)^{2p}) ≤ c (8192 A)^{2p}`. Pointwise domination by the dyadic cube energies
(`abs_smear_energy0_le_shells`), Minkowski's inequality in `L^{2p}` with the shell weights
(`ObserverEnergyCoarseN.state_pow_sum_le`) and `∑ w_j ≤ 8192` (`sum_shellWeight_le`). The bound does
not depend on the support of `g`.

DERIVED: `0` is the excluded colour count, the sign of `c` and the excluded moment `p = 0`; `8192` is
`sum_shellWeight_le`'s; `2` makes the power even and with `1`, `4` is the volume factor `(2R + 1)⁴`;
`5`, `32` are `abs_le_sum_shell`'s. -/
theorem moment_smear_decay_le (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (k : ℕ)
    (f : TestFn) {A c : ℝ} (hf : DecayBound 5 f.1 A) (hc0 : 0 ≤ c) (p : ℕ) (hp : p ≠ 0)
    (hc : ∀ R : ℝ, 0 ≤ R → stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))
      ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * c) :
    stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 f ^ (2 * p))
      ≤ c * (8192 * A) ^ (2 * p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hm : 2 * (q + 1) = 2 * q + 2 := by ring
  rw [hm] at hc ⊢
  obtain ⟨R, M, hRM⟩ := f.2
  have hA := hf.nonneg
  have hmono : stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 f ^ (2 * q + 2))
      ≤ stateK hN k ((∑ j ∈ Finset.range (⌈R⌉₊ + 1), (A * (1 / 32) ^ j)
          • cubeSum (dySpacing N k) ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1) ^ (2 * q + 2)) := by
    refine (stateK hN k).mono (fun U => ?_)
    have hb := abs_smear_energy0_le_shells hN W hD hpos hO k f hRM hf U
    have hev : Even (2 * q + 2) := ⟨q + 1, by ring⟩
    simp only [ContinuousMap.pow_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [← hev.pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb _
  have hD' : ∀ j ∈ Finset.range (⌈R⌉₊ + 1),
      stateK hN k (((A * (1 / 32) ^ j) • cubeSum (dySpacing N k) ((2 : ℝ) ^ (j + 1))
        (W.fieldMap k O).1) ^ (2 * q + 2)) ≤ (A ^ (2 * q + 2) * c) * shellWeight j ^ (2 * q + 2) := by
    intro j _
    rw [smul_pow, (stateK hN k).map_smul]
    calc (A * (1 / 32) ^ j) ^ (2 * q + 2) * stateK hN k (cubeSum (dySpacing N k)
          ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1 ^ (2 * q + 2))
        ≤ (A * (1 / 32) ^ j) ^ (2 * q + 2)
            * (((2 * (2 : ℝ) ^ (j + 1) + 1) ^ 4) ^ (2 * q + 2) * c) :=
          mul_le_mul_of_nonneg_left (hc _ (by positivity))
            (pow_nonneg (mul_nonneg hA (by positivity)) _)
      _ = (A ^ (2 * q + 2) * c) * shellWeight j ^ (2 * q + 2) := by
          unfold shellWeight
          rw [mul_pow, mul_pow]
          ring
  have hmink := MassGap.ObserverEnergyCoarseN.state_pow_sum_le (stateK hN k)
    (Finset.range (⌈R⌉₊ + 1))
    (fun j => (A * (1 / 32) ^ j) • cubeSum (dySpacing N k) ((2 : ℝ) ^ (j + 1)) (W.fieldMap k O).1)
    shellWeight (fun j _ => shellWeight_pos j) q hD'
  have hW0 : 0 ≤ ∑ j ∈ Finset.range (⌈R⌉₊ + 1), shellWeight j :=
    Finset.sum_nonneg (fun j _ => (shellWeight_pos j).le)
  calc stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 f ^ (2 * q + 2))
      ≤ _ := hmono
    _ ≤ (A ^ (2 * q + 2) * c) * (∑ j ∈ Finset.range (⌈R⌉₊ + 1), shellWeight j) ^ (2 * q + 2) :=
        hmink
    _ ≤ (A ^ (2 * q + 2) * c) * 8192 ^ (2 * q + 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 (sum_shellWeight_le _) _)
          (mul_nonneg (pow_nonneg hA _) hc0)
    _ = c * (8192 * A) ^ (2 * q + 2) := by rw [mul_pow]; ring

#print axioms moment_smear_decay_le

end Moments

/-! ## 3. The growth condition in the weighted sup norm -/

section Growth

variable {N : ℕ}

/-- **The cube moments at one step, uniform in the cube and the order**: at every eventual step `k`,
`ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} (2p)! t^{-2p} C` for every `R ≥ 0` and `p`; the conclusion of
`ObserverOSGrowth.cubeMoments_of_unitExp`.

DERIVED: `0` the lower end of `R`; `2`, `1`, `4` the volume factor and the even power. -/
def CubeMomentsAt (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) (t C : ℝ) :
    Prop :=
  ∀ᶠ k in atTop, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
    stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))
      ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C)

/-- A bound at every `ε > 0` of a function continuous at `0` holds at `0`.

DERIVED: `0` the limit point. -/
theorem le_of_forall_pos_continuous {x : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ g ε) : x ≤ g 0 :=
  ge_of_tendsto ((hg.tendsto 0).mono_left nhdsWithin_le_nhds : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)))
    (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) (fun ε hε => h ε hε))

#print axioms le_of_forall_pos_continuous

/-- **One step of the weighted growth bound**: under the cube moments at step `k`, a family of `n`
smeared energy densities with `‖gᵢ‖₅ ≤ Aᵢ` has `|latSF| ≤ (1 + n c) ∏ᵢ 8192 (Aᵢ + ε)`,
`c = (2n)! t^{-2n} C`, for every `ε > 0` (`moment_smear_decay_le`, `ObserverOS.abs_state_prod_le`).

DERIVED: `0` is the excluded colour count, the sign of `t`, `C`, `ε`; `8192` is
`sum_shellWeight_le`'s; `1`, `2` are `abs_state_prod_le`'s; `5 = 4 + 1` the weight's exponent, one above the
dimension so the shell decay `32 = 2⁵` beats the shell volume `16 = 2⁴` (`shellWeight_le`). -/
theorem abs_latSF_decay_le (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) {k : ℕ}
    (hk : ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C))
    (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i))
    {ε : ℝ} (hε : 0 < ε) :
    |latSF hN (energy0 W D hD) k (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * (A i + ε) := by
  have hc0 : 0 ≤ ((2 * n).factorial : ℝ) / t ^ (2 * n) * C :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0
  have hb := abs_state_prod_le (stateK hN k)
    (fun i => smear (dySpacing N k) ((energy0 W D hD).map k O).1 (f i))
    (fun i => 8192 * (A i + ε))
    (fun i => mul_pos (by norm_num) (by linarith [(hA i).nonneg]))
    (c := ((2 * n).factorial : ℝ) / t ^ (2 * n) * C)
    (fun i => by
      rw [Fintype.card_fin]
      have hn : n ≠ 0 := by have := i.isLt; omega
      exact (moment_smear_decay_le hN W hD hpos hO k (f i) (hA i) hc0 n hn
        (fun R hR => hk R hR n)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (by norm_num) (hA i).nonneg) (by linarith) _) hc0))
  rw [Fintype.card_fin] at hb
  show |latSk hN k (fun i => (energy0 W D hD).field k ((O, f i) : SField N))| ≤ _
  rw [latSk_eq]
  exact hb

#print axioms abs_latSF_decay_le

/-- **The lattice functions of a decaying family converge along the ultrafilter to `contSF`**.

DERIVED: `1` the choice `ε = 1` in the eventual bound; `5` the weight's exponent, as in
`abs_latSF_decay_le`. -/
theorem tendsto_latSF_decay (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAt hN W O t C)
    (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) :
    Tendsto (fun k => latSF hN (energy0 W D hD) k (fun i => (O, f i))) (ultra : Filter ℕ)
      (𝓝 (contSF hN (energy0 W D hD) (fun i => (O, f i)))) := by
  have hstep : ∀ᶠ k in atTop, |latSF hN (energy0 W D hD) k (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * (A i + 1) :=
    hev.mono (fun k hk => abs_latSF_decay_le hN W hD hpos hO ht hC0 hk n f A hA one_pos)
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hstep
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_latSF_decay

/-- **The weighted growth bound under the cube moments**: `|S_n| ≤ (1 + n c) ∏ᵢ 8192 Aᵢ`.

DERIVED: `0` the sign of `t`, `C`, `Aᵢ` and the limit point; `8192` is `sum_shellWeight_le`'s; `1`,
`2` are `abs_state_prod_le`'s; `5` the weight's exponent, as in `abs_latSF_decay_le`. -/
theorem abs_contSF_decay_le (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAt hN W O t C)
    (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) :
    |contSF hN (energy0 W D hD) (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * A i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hT := tendsto_latSF_decay hN W hD hpos hO ht hC0 hev n f A hA
  have hcont : Continuous (fun ε : ℝ => (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
      * ∏ i, 8192 * (A i + ε)) :=
    continuous_const.mul (continuous_finsetProd _
      (fun i _ => continuous_const.mul (continuous_const.add continuous_id)))
  have h := le_of_forall_pos_continuous hcont (fun ε hε => by
    have hstep : ∀ᶠ k in atTop, |latSF hN (energy0 W D hD) k (fun i => (O, f i))|
        ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * (A i + ε) :=
      hev.mono (fun k hk => abs_latSF_decay_le hN W hD hpos hO ht hC0 hk n f A hA hε)
    exact le_of_tendsto hT.abs (hstep.filter_mono ultra_le))
  simpa only [add_zero] using h

#print axioms abs_contSF_decay_le

/-- **OS0 in the weighted sup norm, from one exponential moment of the unit cube.** For a
non-negative field `O` of `D` with `UnitCubeExpBound`, there are `t > 0`, `C ≥ 0` such that for every
`n` and every family of test functions with `(1 + ‖y‖)⁵ |gᵢ(y)| ≤ Aᵢ`,
`|S_n(g₁, …, gₙ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 Aᵢ`. No support radius enters.

DERIVED: `0` the lower end of `t` and `C`; `5`, `8192` as in `abs_contSF_decay_le`; `2`, `1` the
factorial constant of `cubeMoments_of_unitExp`. -/
theorem abs_contSF_energy0_decay (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ),
      (∀ i, DecayBound 5 (f i).1 (A i)) →
        |contSF hN (energy0 W D hD) (fun i => (O, f i))|
          ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * A i := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExp hN W (hpos O hO) h
  exact ⟨t, C, ht, hC0, fun n f A hA => abs_contSF_decay_le hN W hD hpos hO ht hC0 hev n f A hA⟩

#print axioms abs_contSF_energy0_decay

/-- **The Osterwalder–Schrader growth condition in a Schwartz seminorm.** With `UnitCubeExpBound`,
one `α = 1 + C` and `γ = 8 (1 + t⁻¹)²` give `|S_n(g₁, …, gₙ)| ≤ α γⁿ (n!)² ∏ᵢ 8192 ‖gᵢ‖₅` for every
family of test functions (`abs_contSF_energy0_decay`, `ObserverOSGrowth.growth_const_le`).

DERIVED: `8`, `2`, `1` are `growth_const_le`'s; `5`, `8192` as in `abs_contSF_energy0_decay`; `0` the
sign of `Aᵢ`. -/
theorem schwartzGrowth_energy0 (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ α γ : ℝ, ∀ (n : ℕ) (f : Fin n → TestFn) (A : Fin n → ℝ),
      (∀ i, DecayBound 5 (f i).1 (A i)) →
        |contSF hN (energy0 W D hD) (fun i => (O, f i))|
          ≤ α * γ ^ n * (n.factorial : ℝ) ^ 2 * ∏ i, 8192 * A i := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_contSF_energy0_decay hN W hD hpos hO h
  refine ⟨1 + C, 8 * (1 + t⁻¹) ^ 2, fun n f A hA => ?_⟩
  have hP0 : 0 ≤ ∏ i, 8192 * A i :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hA i).nonneg)
  exact (hb n f A hA).trans (mul_le_mul_of_nonneg_right (growth_const_le ht hC0 n) hP0)

#print axioms schwartzGrowth_energy0

end Growth

/-! ## 4. Hölder's inequality for a difference of products -/

section Telescope

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]

/-- **The difference of two products of `n` observables through a state**: if every `Gᵢ`, `G'ᵢ` has
`2n`-th moment at most `c Lᵢ^{2n}` and every `G'ᵢ − Gᵢ` at most `c Ldᵢ^{2n}`, then
`|ν(∏ G'ᵢ) − ν(∏ Gᵢ)| ≤ (1 + n c) ∑ₐ Ldₐ ∏_{i ≠ a} Lᵢ`. The products are joined through the hybrids
taking the slots of `s` from `G'`; each step is a product with one factor `G'ₐ − Gₐ`
(`ObserverOS.abs_state_prod_le`).

DERIVED: `1`, `2` are `abs_state_prod_le`'s; `0` the sign of `Lᵢ`, `Ldᵢ`. -/
theorem abs_state_prod_sub_le (ν : MassGap.DLRLimit.State Y) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G G' : ι → C(Y, ℝ)) (L Ld : ι → ℝ) (hL : ∀ i, 0 < L i)
    (hLd : ∀ i, 0 < Ld i) {c : ℝ}
    (hG : ∀ i, ν (G i ^ (2 * Fintype.card ι)) ≤ c * L i ^ (2 * Fintype.card ι))
    (hG' : ∀ i, ν (G' i ^ (2 * Fintype.card ι)) ≤ c * L i ^ (2 * Fintype.card ι))
    (hd : ∀ i, ν ((G' i - G i) ^ (2 * Fintype.card ι)) ≤ c * Ld i ^ (2 * Fintype.card ι)) :
    |ν (∏ i, G' i) - ν (∏ i, G i)|
      ≤ (1 + Fintype.card ι * c) * ∑ a, Ld a * ∏ i ∈ Finset.univ \ {a}, L i := by
  let hyb : Finset ι → ι → C(Y, ℝ) := fun s i => if i ∈ s then G' i else G i
  have step : ∀ s : Finset ι, |ν (∏ i, hyb s i) - ν (∏ i, G i)|
      ≤ (1 + Fintype.card ι * c) * ∑ a ∈ s, Ld a * ∏ i ∈ Finset.univ \ {a}, L i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (∏ i, hyb ∅ i) = ∏ i, G i := Finset.prod_congr rfl (fun i _ => by simp [hyb])
      rw [e, sub_self, abs_zero, Finset.sum_empty, mul_zero]
    | insert a s ha ih =>
      have e1 : ∏ i, hyb (insert a s) i = ∏ i, Function.update (hyb s) a (G' a) i := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        by_cases hi : i = a
        · subst hi; simp [hyb]
        · rw [Function.update_of_ne hi]; simp [hyb, hi]
      have e2 : ∏ i, hyb s i = ∏ i, Function.update (hyb s) a (G a) i := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        by_cases hi : i = a
        · subst hi; simp [hyb, ha]
        · rw [Function.update_of_ne hi]
      have e3 : ∏ i, hyb (insert a s) i - ∏ i, hyb s i
          = ∏ i, Function.update (hyb s) a (G' a - G a) i := by
        rw [e1, e2, Finset.prod_update_of_mem (Finset.mem_univ a),
          Finset.prod_update_of_mem (Finset.mem_univ a),
          Finset.prod_update_of_mem (Finset.mem_univ a), sub_mul]
      have hbound := abs_state_prod_le ν (Function.update (hyb s) a (G' a - G a))
        (Function.update L a (Ld a))
        (fun i => by
          by_cases hi : i = a
          · subst hi; rw [Function.update_self]; exact hLd i
          · rw [Function.update_of_ne hi]; exact hL i) (c := c)
        (fun i => by
          by_cases hi : i = a
          · subst hi; rw [Function.update_self, Function.update_self]; exact hd i
          · rw [Function.update_of_ne hi, Function.update_of_ne hi]
            by_cases his : i ∈ s
            · simp only [hyb, if_pos his]; exact hG' i
            · simp only [hyb, if_neg his]; exact hG i)
      rw [Finset.prod_update_of_mem (Finset.mem_univ a) L (Ld a)] at hbound
      rw [Finset.sum_insert ha, mul_add]
      have e4 : ν (∏ i, hyb (insert a s) i) - ν (∏ i, G i)
          = ν (∏ i, Function.update (hyb s) a (G' a - G a) i)
            + (ν (∏ i, hyb s i) - ν (∏ i, G i)) := by
        rw [← e3, ν.map_sub]; ring
      rw [e4]
      exact (abs_add_le _ _).trans (add_le_add hbound ih)
  have e : ∏ i, hyb Finset.univ i = ∏ i, G' i := Finset.prod_congr rfl (fun i _ => by simp [hyb])
  have := step Finset.univ
  rwa [e] at this

#print axioms abs_state_prod_sub_le

end Telescope

/-! ## 5. Truncation and the extension to decaying test functions -/

section Extension

variable {N : ℕ}

/-- **Decaying functions**: functions on `ℝ⁴` with `(1 + ‖y‖)⁶ |g(y)|` bounded. Schwartz functions are
among them (`ofSchwartz`).

DERIVED: `6` is one order above the growth bound's `5`, the order that makes the truncation tails
vanish; `4` in `Fin 4` is the spacetime dimension. -/
def Decaying : Type := {g : (Fin 4 → ℝ) → ℝ // ∃ B : ℝ, DecayBound 6 g B}

/-- DERIVED: `0` the indicator's lower value. -/
theorem abs_cubeInd_mul_le (R : ℝ) (y : Fin 4 → ℝ) (v : ℝ) : |cubeInd R y * v| ≤ |v| := by
  unfold cubeInd; split_ifs <;> simp

#print axioms abs_cubeInd_mul_le

/-- DERIVED: `0` the vanishing value. -/
theorem le_of_cubeInd_mul_ne {R : ℝ} {y : Fin 4 → ℝ} {v : ℝ} (h : cubeInd R y * v ≠ 0)
    (i : Fin 4) : |y i| ≤ R := by
  unfold cubeInd at h
  split_ifs at h with hc
  · exact hc i
  · simp at h

#print axioms le_of_cubeInd_mul_ne

/-- **The truncation of a decaying function to the cube `[-R, R]⁴`**: `1_{[-R,R]⁴} g`, a test function
(bounded by the weighted bound, supported in the cube).

DERIVED: `6` the decay order; `0` the sign of `R`. -/
def trunc (g : Decaying) (R : ℕ) : TestFn :=
  ⟨fun y => cubeInd (R : ℝ) y * g.1 y, by
    obtain ⟨B, hB⟩ := g.2
    exact ⟨R, B, Nat.cast_nonneg R, fun y => (abs_cubeInd_mul_le _ _ _).trans (hB.abs_le y),
      fun y hy i => le_of_cubeInd_mul_ne hy i⟩⟩

/-- A truncation keeps every weighted bound of the function.

DERIVED: `1` the weight's unit term. -/
theorem decayBound_trunc {K : ℕ} {g : Decaying} {A : ℝ} (h : DecayBound K g.1 A) (R : ℕ) :
    DecayBound K (trunc g R).1 A := fun y =>
  (mul_le_mul_of_nonneg_left (abs_cubeInd_mul_le _ _ (g.1 y))
    (pow_nonneg (by linarith [norm_nonneg y]) _)).trans (h y)

#print axioms decayBound_trunc

/-- **The tail between two truncations**: for `R ≤ R'` and `‖g‖₆ ≤ B`, the difference
`trunc_{R'} g − trunc_R g` has `‖·‖₅ ≤ B / (1 + R)`. It vanishes on `[-R, R]⁴`, and off it
`1 + R ≤ 1 + ‖y‖` buys one power of the weight.

DERIVED: `5`, `6` the two orders; `1` the weight's unit term and the coefficient `-1` of the
subtracted truncation; `0` the vanishing value. -/
theorem decayBound_tail {g : Decaying} {B : ℝ} (hB : DecayBound 6 g.1 B) {R R' : ℕ}
    (hRR : R ≤ R') :
    DecayBound 5 (testAdd (trunc g R') (testSmul (-1) (trunc g R))).1 (B / (1 + R)) := by
  intro y
  have hy0 := norm_nonneg y
  have hR0 : (0 : ℝ) < 1 + R := by positivity
  show (1 + ‖y‖) ^ 5 * |cubeInd (R' : ℝ) y * g.1 y + -1 * (cubeInd (R : ℝ) y * g.1 y)|
    ≤ B / (1 + R)
  by_cases hin : ∀ i, |y i| ≤ (R : ℝ)
  · have h1 : cubeInd (R : ℝ) y = 1 := by unfold cubeInd; rw [if_pos hin]
    have h2 : cubeInd (R' : ℝ) y = 1 := by
      unfold cubeInd
      rw [if_pos (fun i => (hin i).trans (by exact_mod_cast hRR))]
    rw [h1, h2, show (1 : ℝ) * g.1 y + -1 * (1 * g.1 y) = 0 by ring, abs_zero, mul_zero]
    exact div_nonneg hB.nonneg hR0.le
  · have h1 : cubeInd (R : ℝ) y = 0 := by unfold cubeInd; rw [if_neg hin]
    rw [h1, zero_mul, mul_zero, add_zero]
    push_neg at hin
    obtain ⟨i, hi⟩ := hin
    have hyi : |y i| ≤ ‖y‖ := by
      have := norm_le_pi_norm y i
      rwa [Real.norm_eq_abs] at this
    have hyR : (R : ℝ) ≤ ‖y‖ := hi.le.trans hyi
    have hp : 0 ≤ (1 + ‖y‖) ^ 5 := by positivity
    rw [le_div_iff₀ hR0]
    calc (1 + ‖y‖) ^ 5 * |cubeInd (R' : ℝ) y * g.1 y| * (1 + R)
        ≤ (1 + ‖y‖) ^ 5 * |g.1 y| * (1 + ‖y‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (abs_cubeInd_mul_le _ _ _) hp) (by linarith)
            hR0.le (mul_nonneg hp (abs_nonneg _))
      _ = (1 + ‖y‖) ^ 6 * |g.1 y| := by ring
      _ ≤ B := hB y

#print axioms decayBound_tail

/-- **Smearing the tail** is the difference of the smeared truncations.

DERIVED: `0` the sign of `a`; `-1` the coefficient of the subtracted test function. -/
theorem smear_tail {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (f g : TestFn) :
    smear a F (testAdd f (testSmul (-1) g)) = smear a F f - smear a F g := by
  rw [smear_testAdd ha, smear_testSmul ha, neg_one_smul, ← sub_eq_add_neg]

#print axioms smear_tail

/-- **Two truncations are close**: under the cube moments, for `R ≤ R'` and `‖gᵢ‖₆ ≤ Bᵢ`,
`|S_n(trunc_{R'} g) − S_n(trunc_R g)| ≤ (1 + n c) ∑ₐ 8192 (Bₐ / (1 + R)) ∏_{i ≠ a} 8192 Bᵢ`. At each
step `abs_state_prod_sub_le` with `Lᵢ = 8192 (Bᵢ + ε)`, `Ldᵢ = 8192 (Bᵢ/(1 + R) + ε)`
(`moment_smear_decay_le`, `decayBound_tail`); the bound passes to the limit and to `ε = 0`.

DERIVED: `0` is the excluded colour count, the sign of `t`, `C`, `ε` and the limit point; `8192`,
`5`, `6` as in `moment_smear_decay_le` and `decayBound_tail`; `1`, `2` are `abs_state_prod_le`'s. -/
theorem abs_contSF_trunc_sub_le (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAt hN W O t C)
    (n : ℕ) (g : Fin n → Decaying) (B : Fin n → ℝ) (hB : ∀ i, DecayBound 6 (g i).1 (B i))
    {R R' : ℕ} (hRR : R ≤ R') :
    |contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R'))
        - contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
        * ∑ a, 8192 * (B a / (1 + R)) * ∏ i ∈ Finset.univ \ {a}, 8192 * B i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  set c : ℝ := ((2 * n).factorial : ℝ) / t ^ (2 * n) * C with hcdef
  have hc0 : 0 ≤ c := mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0
  have hB0 : ∀ i, 0 ≤ B i := fun i => (hB i).nonneg
  have hR0 : (0 : ℝ) < 1 + R := by positivity
  have hB5 : ∀ (S : ℕ) i, DecayBound 5 (trunc (g i) S).1 (B i) :=
    fun S i => decayBound_trunc ((hB i).mono (by norm_num)) S
  have hT' := tendsto_latSF_decay hN W hD hpos hO ht hC0 hev n (fun i => trunc (g i) R') B
    (hB5 R')
  have hT := tendsto_latSF_decay hN W hD hpos hO ht hC0 hev n (fun i => trunc (g i) R) B (hB5 R)
  have hcont : Continuous (fun ε : ℝ => (1 + n * c)
      * ∑ a, 8192 * (B a / (1 + R) + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε)) :=
    continuous_const.mul (continuous_finsetSum _ (fun a _ =>
      (continuous_const.mul (continuous_const.add continuous_id)).mul
        (continuous_finsetProd _
          (fun i _ => continuous_const.mul (continuous_const.add continuous_id)))))
  have h := le_of_forall_pos_continuous hcont (fun ε hε => by
    have hstep : ∀ᶠ k in atTop,
        |latSF hN (energy0 W D hD) k (fun i => (O, trunc (g i) R'))
          - latSF hN (energy0 W D hD) k (fun i => (O, trunc (g i) R))|
        ≤ (1 + n * c)
          * ∑ a, 8192 * (B a / (1 + R) + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε) := by
      filter_upwards [hev] with k hk
      have ha := dySpacing_pos (one_le_of_ne_zero hN) k
      have hmom : ∀ (f : TestFn) (A : ℝ), DecayBound 5 f.1 A → n ≠ 0 →
          stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 f ^ (2 * n))
            ≤ c * (8192 * (A + ε)) ^ (2 * n) := fun f A hA hn =>
        (moment_smear_decay_le hN W hD hpos hO k f hA hc0 n hn (fun S hS => hk S hS n)).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg (by norm_num) hA.nonneg) (by linarith) _) hc0)
      have hb := abs_state_prod_sub_le (stateK hN k)
        (fun i => smear (dySpacing N k) ((energy0 W D hD).map k O).1 (trunc (g i) R))
        (fun i => smear (dySpacing N k) ((energy0 W D hD).map k O).1 (trunc (g i) R'))
        (fun i => 8192 * (B i + ε)) (fun i => 8192 * (B i / (1 + R) + ε))
        (fun i => mul_pos (by norm_num) (by linarith [hB0 i]))
        (fun i => mul_pos (by norm_num) (by linarith [div_nonneg (hB0 i) hR0.le])) (c := c)
        (fun i => by
          rw [Fintype.card_fin]
          exact hmom _ _ (hB5 R i) (by have := i.isLt; omega))
        (fun i => by
          rw [Fintype.card_fin]
          exact hmom _ _ (hB5 R' i) (by have := i.isLt; omega))
        (fun i => by
          rw [Fintype.card_fin]
          show stateK hN k ((smear (dySpacing N k) ((energy0 W D hD).map k O).1 (trunc (g i) R')
              - smear (dySpacing N k) ((energy0 W D hD).map k O).1 (trunc (g i) R)) ^ (2 * n)) ≤ _
          rw [← smear_tail ha]
          exact hmom _ _ (decayBound_tail (hB i) hRR) (by have := i.isLt; omega))
      rw [Fintype.card_fin] at hb
      show |latSk hN k (fun i => (energy0 W D hD).field k ((O, trunc (g i) R') : SField N))
        - latSk hN k (fun i => (energy0 W D hD).field k ((O, trunc (g i) R) : SField N))| ≤ _
      rw [latSk_eq, latSk_eq]
      exact hb
    exact le_of_tendsto (hT'.sub hT).abs (hstep.filter_mono ultra_le))
  simpa only [add_zero] using h

#print axioms abs_contSF_trunc_sub_le

/-- **The Schwinger functions of decaying test functions**: the limit, as `R → ∞`, of the Schwinger
functions of the truncations `trunc_R gᵢ` (`limUnder`; it exists under one exponential moment of the
unit cube, `tendsto_schwSF`).

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def schwSF (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (O : LField (MassGap.SUN.SU N)) {n : ℕ} (g : Fin n → Decaying) : ℝ :=
  limUnder atTop (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R)))

/-- **The truncated Schwinger functions converge**: given `UnitCubeExpBound`, for every family of
decaying functions `S_n(trunc_R g) → schwSF g` as `R → ∞`. They are Cauchy: for `R ≤ R'` they differ
by at most `K / (1 + R)` (`abs_contSF_trunc_sub_le`).

DERIVED: `0` the sign of `ε` and `K`; `1` the shift `1 + R`. -/
theorem tendsto_schwSF (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) {n : ℕ} (g : Fin n → Decaying) :
    Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R))) atTop
      (𝓝 (schwSF hN W D hD O g)) := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExp hN W (hpos O hO) h
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
      * ∑ a, 8192 * B a * ∏ i ∈ Finset.univ \ {a}, 8192 * B i := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0)))
      (Finset.sum_nonneg (fun a _ => mul_nonneg (mul_nonneg (by norm_num) (hB a).nonneg)
        (Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hB i).nonneg))))
  have hdist : ∀ R R' : ℕ, R ≤ R' →
      dist (contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R')))
        (contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R))) ≤ K / (1 + R) := by
    intro R R' hRR
    rw [Real.dist_eq]
    refine (abs_contSF_trunc_sub_le hN W hD hpos hO ht hC0 hev n g B hB hRR).trans
      (le_of_eq ?_)
    rw [hKdef, mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hcs : CauchySeq (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R))) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (K / ε)
    refine ⟨M, fun m hm => (hdist M m hm).trans_lt ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_schwSF

/-- **The growth bound for the extended Schwinger functions**: given `UnitCubeExpBound`, there are
`t > 0`, `C ≥ 0` with `|schwSF g| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 Aᵢ` for every family of decaying
functions with `‖gᵢ‖₅ ≤ Aᵢ`. Each truncation satisfies it (`abs_contSF_decay_le`,
`decayBound_trunc`) and it passes to the limit.

DERIVED: `0` the sign of `t`, `C`; `5`, `8192` as in `abs_contSF_decay_le`; `2`, `1` the factorial
constant. -/
theorem abs_schwSF_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (g : Fin n → Decaying) (A : Fin n → ℝ),
      (∀ i, DecayBound 5 (g i).1 (A i)) →
        |schwSF hN W D hD O g|
          ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * A i := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExp hN W (hpos O hO) h
  refine ⟨t, C, ht, hC0, fun n g A hA => ?_⟩
  exact le_of_tendsto (tendsto_schwSF hN W hD hpos hO h g).abs (Eventually.of_forall
    (fun R => abs_contSF_decay_le hN W hD hpos hO ht hC0 hev n (fun i => trunc (g i) R) A
      (fun i => decayBound_trunc (hA i) R)))

#print axioms abs_schwSF_le

/-- **The extension agrees with `contSF` on test functions**: if each `gᵢ` is (as a function) a test
function `fᵢ`, then `schwSF g = contSF f`. The truncations equal `fᵢ` once `R` exceeds the supports.

DERIVED: `0` the vanishing value; `1` the indicator on the cube. -/
theorem schwSF_eq_contSF (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) {n : ℕ} (g : Fin n → Decaying) (f : Fin n → TestFn)
    (hgf : ∀ i, (g i).1 = (f i).1) :
    schwSF hN W D hD O g = contSF hN (energy0 W D hD) (fun i => (O, f i)) := by
  have hex : ∀ i, ∃ R M : ℝ, IsTest (f i).1 R M := fun i => (f i).2
  choose R0 M hRM using hex
  have hev : ∀ᶠ R : ℕ in atTop, (fun i => (O, trunc (g i) R)) = (fun i => (O, f i)) := by
    filter_upwards [Filter.eventually_ge_atTop ⌈∑ i, R0 i⌉₊] with R hR
    funext i
    refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
    show cubeInd (R : ℝ) y * (g i).1 y = (f i).1 y
    rw [hgf i]
    by_cases h0 : (f i).1 y = 0
    · rw [h0, mul_zero]
    · have hin : ∀ j, |y j| ≤ (R : ℝ) := by
        intro j
        have h1 := (hRM i).2.2 y h0 j
        have h2 : R0 i ≤ ∑ i, R0 i :=
          Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
        have h3 : ∑ i, R0 i ≤ (⌈∑ i, R0 i⌉₊ : ℝ) := Nat.le_ceil _
        have h4 : (⌈∑ i, R0 i⌉₊ : ℝ) ≤ R := by exact_mod_cast hR
        linarith
      have h1 : cubeInd (R : ℝ) y = 1 := by unfold cubeInd; rw [if_pos hin]
      rw [h1, one_mul]
  have hT : Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O, trunc (g i) R))) atTop
      (𝓝 (contSF hN (energy0 W D hD) (fun i => (O, f i)))) :=
    tendsto_const_nhds.congr'
      (hev.mono (fun R hR => congrArg (contSF hN (energy0 W D hD)) hR.symm))
  exact tendsto_nhds_unique (tendsto_schwSF hN W hD hpos hO h g) hT

#print axioms schwSF_eq_contSF

/-- **The weighted norm of a Schwartz function**: `2^K sup_{(k, l) ≤ (K, 0)} p_{k,l}(φ)`, Mathlib's
Schwartz seminorms `p_{k,l}(φ) = sup ‖y‖^k ‖D^l φ(y)‖`.

DERIVED: `2` and `0` are `SchwartzMap.one_add_le_sup_seminorm_apply`'s (`(1 + ‖y‖)^K ≤ 2^K` times the
largest of `1, ‖y‖^K`; derivative order `0`); `4` in `Fin 4` is the spacetime dimension. -/
def schwartzNorm (K : ℕ) (φ : SchwartzMap (Fin 4 → ℝ) ℝ) : ℝ :=
  2 ^ K * (Finset.Iic (K, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ

/-- A Schwartz function has every weighted bound, with constant `schwartzNorm K φ`
(`SchwartzMap.one_add_le_sup_seminorm_apply` at derivative order `0`).

DERIVED: `0` the derivative order. -/
theorem decayBound_schwartz (K : ℕ) (φ : SchwartzMap (Fin 4 → ℝ) ℝ) :
    DecayBound K φ (schwartzNorm K φ) := fun y => by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, 0)) le_rfl le_rfl φ y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

#print axioms decayBound_schwartz

/-- **A Schwartz function as a decaying function.**

DERIVED: `6` the decay order of `Decaying`. -/
def ofSchwartz (φ : SchwartzMap (Fin 4 → ℝ) ℝ) : Decaying :=
  ⟨φ, schwartzNorm 6 φ, decayBound_schwartz 6 φ⟩

/-- **The growth condition on Schwartz test functions.** Given `UnitCubeExpBound`, there are `t > 0`,
`C ≥ 0` such that the Schwinger functions of the energy density, extended to Schwartz functions by
truncation (`schwSF`, convergent by `tendsto_schwSF`), satisfy
`|S_n(φ₁, …, φₙ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 · 32 · sup_{(k,l) ≤ (5,0)} p_{k,l}(φᵢ)`.

DERIVED: `32 = 2⁵` and `5` are `schwartzNorm 5`'s; `8192` as in `abs_schwSF_le`; `0` the sign of `t`,
`C`; `2`, `1` the factorial constant. -/
theorem abs_schwSF_schwartz_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (φ : Fin n → SchwartzMap (Fin 4 → ℝ) ℝ),
      |schwSF hN W D hD O (fun i => ofSchwartz (φ i))|
        ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
          * ∏ i, 8192 * (2 ^ 5 * (Finset.Iic (5, 0)).sup
              (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (φ i)) := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwSF_le hN W hD hpos hO h
  exact ⟨t, C, ht, hC0, fun n φ => hb n _ _ (fun i => decayBound_schwartz 5 (φ i))⟩

#print axioms abs_schwSF_schwartz_le

end Extension

end MassGap.ObserverOSSchwartz
