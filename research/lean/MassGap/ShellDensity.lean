import Mathlib
import MassGap.ShellJoint

/-!
# MassGap.ShellDensity — the zero-momentum sector is a density of the joint measure

`ShellMomentum.clay_zero_momentum_sector` reads the Clay gap under `hσ : σ 0 = rateMeasure (X.time 1)
(P0 T u)`, the rate measure of the exactly translation-invariant component of `u`. `ShellJoint` shows
that `hσ` forces `P0 T u ≠ 0`, which a vector of the vacuum complement of a translation-invariant
continuum theory does not have. The Källén–Lehmann sector at `p = 0` is instead the density at `p = 0`
of the joint (rate, momentum) measure. This module reads the momentum of a character, pushes the joint
measure to rate × momentum, states the corrected identification as a density, and shows the gap
conclusions pass through it. Declarations are in the namespace `MassGap.ShellDensity`.

DERIVED: `Fin 4` is the four-dimensional spacetime index; spatial vectors have three free coordinates.

## 1. The momentum of a character (proved, for vectors with a dyadic Dini bound)

`ej τ j` is the spatial coordinate vector of direction `j` (`0` for `j = τ`), `dy τ j k = 2^{−k} ej τ j`
the dyadic step, `zk J j k χ = χ(U(dy τ j k))` its character value.

* `normSq_char`: `|χ(U x)| = 1` for every character; `char_zsmul`: `χ(U(n x)) = χ(U x)^n`, `n ∈ ℤ`;
  `char_sum`: `χ(U(Σ y)) = Π χ(U y)`; `zk_sq`: `z_k = z_{k+1}²`.
* `integral_normSq`: `∫ |χ(d)|² dμ_u = ‖d u‖²` for every `d` in the joint algebra;
  `measure_re_nonpos_le`: `μ_u {Re χ(U x) ≤ 0} ≤ ‖U x u − u‖²` (Markov).
* `DyadicDini J u`: `Σ_k ‖U(dy τ j k) u − u‖² < ∞` in each direction. `ae_good`: under it, by
  Borel–Cantelli, `μ_u`-almost every `χ` has `Re z_k > 0` for all large `k`. There the principal
  arguments halve (`arg_sq`), `2^k arg z_k` is eventually constant (`pseq_const`), and its limit is the
  momentum `momentum J χ j` (`momentum_eq`): `z_k = e^{i p_j 2^{−k}}` (`zk_eq_exp`), and
  `χ(U(n 2^{−k} e_j)) = e^{i p_j n 2^{−k}}` on every dyadic point past the threshold.
* `ae_char_line`: for every real `t`, `χ(U(t e_j)) = e^{i p_j t}` for `μ_u`-almost every `χ`, from
  `∫ |χ(U(t e_j)) − χ(U(d_k e_j))|² dμ_u = ‖(U(t e_j) − U(d_k e_j)) u‖² → 0` along dyadics `d_k → t`
  (strong continuity of the representation) and Fatou's lemma.
* `ae_char_eq_phase`: for every `x`, `χ(U x) = e^{i p(χ)·x}` almost everywhere;
  `aemeasurable_momentum`; `inner_U_eq_momentum`: `⟪u, U x u⟫ = ∫ e^{i p·x} d(p_* μ_u)`.
  The momentum is read off the signal's own dyadic phases; no frequency is chosen.

Plainly, two things are not proved. (i) The statement is per `x`: for each `x` the identity holds off a
null set that may depend on `x`. That the set of characters with `x ↦ χ(U x)` continuous is itself of
full measure would follow from Bochner's theorem (the push-forward to the Bohr compactification is then the
image of a measure on `ℝ³`); Bochner's theorem is not in Mathlib at this pin, and every integral read
here needs only the per-`x` form. (ii) `DyadicDini` is assumed of `u`. It holds for vectors smooth in
the translations (`‖(U(s e_j) − 1) u‖ ≤ |s| ‖P_j u‖`, so the series is geometric), e.g. for averaged
vectors `∫₀¹ U(t e_j) v dt` and for field vectors smeared with test functions. This is stated, not
formalised here. Extending the momentum
read to every `u` needs either Bochner's theorem or the continuity of `u ↦ μ_u(B)` on Borel sets
together with density of the Dini vectors; neither is built here.

## 2. The joint push-forward and the zero-momentum density (proved)

`nu J u`: the push-forward of `μ_u` restricted to `χ(a) > 0` under `χ ↦ (−log χ(a), p(χ))`.
`nu_fst`: its rate marginal is `rateMeasure a u` (under `DyadicDini`). `nu_Iio_prod`: a rate bottom of
`u` is a bottom of `nu J u` in the rate, for every `u`.

`lam τ`: Lebesgue measure on the spatial momenta (`δ₀` in the time slot); `lam_ball`: the window
`B(0, ε)`, the sup-norm ball (a cube) in `Fin 4 → ℝ`, has volume `(2ε)³` (the time slot contributes the
atom `δ₀`, mass 1). `windowed ν ε`: the rate measure of `ν` restricted to momenta in
`B(0, ε)`. `ZeroDensity τ ν σ₀`: `windowed ν ε / lam(B(0, ε)) → σ₀` converge weakly as `ε → 0⁺`: the
integral of every bounded continuous non-negative `f` against windowed `ν ε / λ(B(0, ε))` tends to its
integral against `σ₀` — the Lebesgue-differentiation form of the density at `p = 0`.

* `zeroDensity_bottom`: a bottom of `ν` in the rate is a bottom of the density.
* `clay_zero_momentum_density`: with Källén–Lehmann data and the corrected identification
  `hσ' : ZeroDensity τ (nu J u) (σ 0)`, for `J` with time step `X.time 1` and `u` in the vacuum
  complement: `σ 0 (−∞, X.gap) = 0`, `X.gap² ≤ M2` (`gap_sq_le_of_sector`), `0 < M2`,
  `X.gap ≤ √M2`, `SpecBottom (σ 0) (√M2)`, and the band excess at every `p²`. Plainly, the two
  conclusions of `ShellGap.clay_zero_momentum` about the vector `u` itself (its decay at rate `√M2`
  and its correlator's read `→ √M2`) do not follow from `hσ'`: the rate measure of `u` collects every
  momentum, so its bottom can lie below the bottom of the `p = 0` density.

`hσ'` is a hypothesis. It is the correct object, and it can hold where `hσ` cannot; it is not
discharged here.

## 3. Load tests (proved)

* `free_density_shell`: the free superposition with a continuous momentum profile `g`, joint measure
  `(√(m² + |p|²), p)_*(g · lam)`, has zero-momentum density `g(0) δ_m`, non-zero when `g(0) ≠ 0`; its
  rate is the shell `√(m² + 0) = m`. The Hilbert-space vector carrying this measure is not built; the
  test is on the measure.
* `vacuum_no_density`: the vacuum (`a v = v`, `U x v = v`, `v ≠ 0`) has `nu = ‖v‖² δ_{(0, 0)}`
  (`nu_vacuum`) and no zero-momentum density with finite mass: the atom over the shrinking window
  diverges. The vacuum complement carries no rate below the gap (`nu_Iio_prod`).
* `planeWave_momentum`: for the plane wave `x ↦ e^{i p·x}` the read momentum is `p` in every spatial
  direction, almost everywhere.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellDensity

open Real Filter Topology MeasureTheory Set WeakDual
open scoped NNReal ENNReal
open MassGap.BandShell (shell SpecBottom)
open MassGap.ShellMeasure (rateMeasure clamp measurable_rate KallenLehmann klWeight measurable_shell
  measurable_klWeight)
open MassGap.ShellGap (gap_rateBottom specBottom_klSector)
open MassGap.ShellJoint (JointData alg UB aB Chars jointMeasure tclamp continuous_tclamp
  rateMeasure_eq_joint ae_eq_of_eigen op_G liftR integral_jointMeasure star_U planeData
  planeWave_dirac)
open MassGap.ShellTranslate (spatial phase mem_spatial spatial_time)
open MassGap.ObserverOSReconstructionS (OSDataS)

noncomputable section

/-! ## 1. The momentum of a character -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {τ : Fin 4} (J : JointData E (spatial τ))

/-- DERIVED: no numeral. -/
theorem UB_add (x y : spatial τ) : UB J (x + y) = UB J x * UB J y := Subtype.ext (J.R.map_add x y)

/-- DERIVED: `1` the unit. -/
theorem UB_zero : UB J 0 = 1 := Subtype.ext J.R.map_zero

/-- DERIVED: no numeral. -/
theorem star_UB (x : spatial τ) : star (UB J x) = UB J (-x) := Subtype.ext (star_U J x)

/-- **A character inverts a translation by the opposite one.** DERIVED: `1` the unit. -/
theorem char_mul_neg (χ : Chars J) (x : spatial τ) : χ (UB J x) * χ (UB J (-x)) = 1 := by
  rw [← map_mul, ← UB_add, add_neg_cancel, UB_zero, map_one]

/-- **A character of a translation has modulus one.** DERIVED: `1` the modulus. -/
theorem normSq_char (χ : Chars J) (x : spatial τ) : Complex.normSq (χ (UB J x)) = 1 := by
  have e : (starRingEnd ℂ) (χ (UB J x)) = χ (UB J (-x)) := by
    rw [← star_UB, map_star]; rfl
  have h : ((Complex.normSq (χ (UB J x)) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, e, mul_comm, char_mul_neg]
  exact_mod_cast h

/-- DERIVED: `1` the modulus; `2` the square. -/
theorem norm_char (χ : Chars J) (x : spatial τ) : ‖χ (UB J x)‖ = 1 := by
  have h := normSq_char J χ x
  rw [Complex.normSq_eq_norm_sq] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- **Integer multiples**: `χ(U(n x)) = χ(U x)^n`. DERIVED: `1` the induction step. -/
theorem char_zsmul (χ : Chars J) (x : spatial τ) (n : ℤ) :
    χ (UB J (n • x)) = χ (UB J x) ^ n := by
  have h0 : χ (UB J x) ≠ 0 := left_ne_zero_of_mul_eq_one (char_mul_neg J χ x)
  have hinv : χ (UB J (-x)) = (χ (UB J x))⁻¹ := eq_inv_of_mul_eq_one_right (char_mul_neg J χ x)
  induction n using Int.induction_on with
  | zero => rw [zero_smul, UB_zero, map_one, zpow_zero]
  | succ n ih => rw [add_smul, one_smul, UB_add, map_mul, ih, zpow_add_one₀ h0]
  | pred n ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg, UB_add, map_mul, ih, zpow_sub_one₀ h0, hinv]

/-- **Sums**: `χ(U(Σ y)) = Π χ(U y)`. DERIVED: `0`, `1` the empty sum and product. -/
theorem char_sum (χ : Chars J) {ι : Type*} (s : Finset ι) (y : ι → spatial τ) :
    χ (UB J (∑ i ∈ s, y i)) = ∏ i ∈ s, χ (UB J (y i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, UB_zero, map_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, UB_add, map_mul, ih]

/-- **The `L²` identity**: `∫ |χ(d)|² dμ_u = ‖d u‖²`. DERIVED: `2` the square. -/
theorem integral_normSq (u : E) (d : alg J) :
    ∫ χ, Complex.normSq (χ d) ∂(jointMeasure J u) = ‖(d : E →L[ℂ] E) u‖ ^ 2 := by
  let f : C(Chars J, ℝ) := ⟨fun χ => Complex.normSq (χ d),
    Complex.continuous_normSq.comp (map_continuous (gelfandStarTransform (alg J) d))⟩
  have hf : liftR J f = gelfandStarTransform (alg J) (star d * d) := ContinuousMap.ext fun χ => by
    show ((Complex.normSq (χ d) : ℝ) : ℂ) = χ (star d * d)
    rw [map_mul, map_star, Complex.normSq_eq_conj_mul_self]; rfl
  have hint := integral_jointMeasure J u f
  rw [hf, op_G] at hint
  show ∫ χ, f χ ∂(jointMeasure J u) = _
  rw [hint]
  show (inner ℂ u ((star (d : E →L[ℂ] E) * (d : E →L[ℂ] E)) u)).re = _
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- **Markov at the left half-plane**: `μ_u {Re χ(U x) ≤ 0} ≤ ‖U x u − u‖²`, since
`|z − 1|² ≥ 1` there. DERIVED: `0` the imaginary axis; `1` the unit; `2` the square. -/
theorem measure_re_nonpos_le (u : E) (x : spatial τ) :
    jointMeasure J u {χ | (χ (UB J x)).re ≤ 0} ≤ ENNReal.ofReal (‖J.R.U x u - u‖ ^ 2) := by
  set d : alg J := UB J x - 1 with hd_def
  have hd : ∀ χ : Chars J, χ d = χ (UB J x) - 1 := fun χ => by rw [hd_def, map_sub, map_one]
  have hdu : (d : E →L[ℂ] E) u = J.R.U x u - u := by
    show (J.R.U x - 1) u = _
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  have hint : Integrable (fun χ : Chars J => Complex.normSq (χ d)) (jointMeasure J u) :=
    (Complex.continuous_normSq.comp (map_continuous (gelfandStarTransform (alg J) d))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun χ : Chars J => Complex.normSq_nonneg (χ d)) hint 1
  rw [one_mul, integral_normSq, hdu] at hM
  calc jointMeasure J u {χ | (χ (UB J x)).re ≤ 0}
      ≤ jointMeasure J u {χ | 1 ≤ Complex.normSq (χ d)} := measure_mono fun χ hχ => by
        simp only [mem_setOf_eq] at hχ ⊢
        rw [hd, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
          Complex.one_im]
        nlinarith [mul_self_nonneg (χ (UB J x)).im]
    _ = ENNReal.ofReal ((jointMeasure J u).real {χ | 1 ≤ Complex.normSq (χ d)}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hM

end Generic

/-- **The spatial coordinate vector** of direction `j` (`0` for the time direction). DERIVED: `0`,
`1` the entries of a coordinate vector. -/
def ej (τ j : Fin 4) : spatial τ :=
  ⟨fun i => if i = τ then 0 else if i = j then 1 else 0, mem_spatial (by simp)⟩

/-- **A spatial vector is the sum of its coordinates.** DERIVED: `0` the time component. -/
theorem sum_ej {τ : Fin 4} (x : spatial τ) : ∑ j, (x : Fin 4 → ℝ) j • ej τ j = x := by
  refine Subtype.ext (funext fun i => ?_)
  rw [Submodule.coe_sum, Finset.sum_apply]
  show ∑ j, (x : Fin 4 → ℝ) j * (if i = τ then (0 : ℝ) else if i = j then 1 else 0) = _
  by_cases hi : i = τ
  · rw [hi, spatial_time x]; simp
  · simp [hi]

/-- **The dyadic step** `2^{−k} e_j`. DERIVED: `1/2` the halving of the dyadic scale. CHOSEN (a
construction, not a parameter of any result): the dyadic base; every integer base `b ≥ 2` serves with
`b`-th roots in `arg_sq`. -/
def dy (τ j : Fin 4) (k : ℕ) : spatial τ := ((1 / 2 : ℝ) ^ k) • ej τ j

/-- DERIVED: `1` the step; `2` the doubling. -/
theorem dy_succ (τ j : Fin 4) (k : ℕ) : dy τ j k = dy τ j (k + 1) + dy τ j (k + 1) := by
  simp only [dy, ← add_smul]
  congr 1
  ring

/-- **Principal arguments halve on the right half-plane**: `Re w > 0` gives
`arg (w²) = 2 arg w`. DERIVED: `0` the half-plane; `2` the square. -/
theorem arg_sq {w : ℂ} (hw : 0 < w.re) : Complex.arg (w ^ 2) = 2 * Complex.arg w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl _ hw
  have ha : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  obtain ⟨h1, h2⟩ := abs_lt.mp ha
  rw [sq, (Complex.arg_mul_eq_add_arg_iff hw0 hw0).mpr ⟨by linarith, by linarith⟩]
  ring

section Generic2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {τ : Fin 4} (J : JointData E (spatial τ))

/-- **The dyadic character values** `z_k = χ(U(2^{−k} e_j))`. DERIVED: no numeral. -/
def zk (j : Fin 4) (k : ℕ) (χ : Chars J) : ℂ := χ (UB J (dy τ j k))

/-- **Each dyadic value is the square of the next.** DERIVED: `1` the step; `2` the square. -/
theorem zk_sq (j : Fin 4) (k : ℕ) (χ : Chars J) : zk J j k χ = zk J j (k + 1) χ ^ 2 := by
  simp only [zk]
  rw [dy_succ τ j k, UB_add, map_mul, sq]

/-- **The dyadic phase read** `2^k arg z_k`. DERIVED: `2` the dyadic base. -/
def pseq (j : Fin 4) (k : ℕ) (χ : Chars J) : ℝ := 2 ^ k * Complex.arg (zk J j k χ)

/-- DERIVED: `0` the half-plane; `1` the step. -/
theorem pseq_succ (j : Fin 4) (k : ℕ) (χ : Chars J) (h : 0 < (zk J j (k + 1) χ).re) :
    pseq J j (k + 1) χ = pseq J j k χ := by
  simp only [pseq]
  rw [zk_sq J j k χ, arg_sq h]
  ring

/-- **The read is constant past a threshold of the right half-plane.** DERIVED: `0` the half-plane;
`1` the step. -/
theorem pseq_const {χ : Chars J} {j : Fin 4} {K : ℕ} (h : ∀ k, K ≤ k → 0 < (zk J j k χ).re) :
    ∀ k, K ≤ k → pseq J j k χ = pseq J j K χ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [pseq_succ J j k χ (h (k + 1) (by omega)), ih]

/-- **The momentum of a character**: the limit of the dyadic phase reads. DERIVED: no numeral. -/
def momentum (χ : Chars J) : Fin 4 → ℝ := fun j => limUnder atTop fun k => pseq J j k χ

/-- DERIVED: `0` the half-plane. -/
theorem momentum_eq {χ : Chars J} {j : Fin 4} {K : ℕ} (h : ∀ k, K ≤ k → 0 < (zk J j k χ).re) :
    momentum J χ j = pseq J j K χ := by
  have ht : Tendsto (fun k => pseq J j k χ) atTop (𝓝 (pseq J j K χ)) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨K, fun k hk => (pseq_const J h k hk).symm⟩)
  exact ht.limUnder_eq

/-- **Past the threshold the dyadic value is the plane-wave phase**: `z_k = e^{i p_j 2^{−k}}`.
DERIVED: `0` the half-plane; `1` the modulus; `1/2` the dyadic scale. -/
theorem zk_eq_exp {χ : Chars J} {j : Fin 4} {K : ℕ} (h : ∀ k, K ≤ k → 0 < (zk J j k χ).re)
    (k : ℕ) (hk : K ≤ k) :
    zk J j k χ = Complex.exp (((momentum J χ j * (1 / 2) ^ k : ℝ) : ℂ) * Complex.I) := by
  have e : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
  have harg : Complex.arg (zk J j k χ) = momentum J χ j * (1 / 2) ^ k := by
    rw [momentum_eq J h, ← pseq_const J h k hk, pseq]
    linear_combination (-(Complex.arg (zk J j k χ))) * e
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (zk J j k χ)]
  rw [harg, show ‖zk J j k χ‖ = 1 from norm_char J χ _, Complex.ofReal_one, one_mul]

/-- **Every dyadic point past the threshold**: `χ(U(n 2^{−k} e_j)) = e^{i p_j n 2^{−k}}`.
DERIVED: `0` the half-plane; `1/2` the dyadic scale. -/
theorem char_line_dyadic {χ : Chars J} {j : Fin 4} {K : ℕ}
    (h : ∀ k, K ≤ k → 0 < (zk J j k χ).re) (k : ℕ) (hk : K ≤ k) (n : ℤ) :
    χ (UB J (((n : ℝ) * (1 / 2) ^ k) • ej τ j))
      = Complex.exp (((momentum J χ j * ((n : ℝ) * (1 / 2) ^ k)) : ℝ) * Complex.I) := by
  have e : ((n : ℝ) * (1 / 2) ^ k) • ej τ j = n • dy τ j k := by
    rw [dy, mul_smul, Int.cast_smul_eq_zsmul]
  rw [e, char_zsmul, show χ (UB J (dy τ j k)) = zk J j k χ from rfl, zk_eq_exp J h k hk,
    ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- **The dyadic Dini bound** of a vector: `Σ_k ‖U(2^{−k} e_j) u − u‖² < ∞` in each direction.
DERIVED: `2` the square. -/
def DyadicDini (u : E) : Prop :=
  ∀ j : Fin 4, Summable fun k : ℕ => ‖J.R.U (dy τ j k) u - u‖ ^ 2

/-- **Borel–Cantelli**: under the Dini bound almost every character is eventually in the right
half-plane at the dyadic steps. DERIVED: `0` the half-plane; `2` the square. -/
theorem ae_good {u : E} (hD : DyadicDini J u) (j : Fin 4) :
    ∀ᵐ χ ∂(jointMeasure J u), ∀ᶠ k in atTop, 0 < (zk J j k χ).re := by
  have hs : (∑' k, jointMeasure J u {χ | (χ (UB J (dy τ j k))).re ≤ 0}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_
      (ENNReal.tsum_le_tsum fun k => measure_re_nonpos_le J u (dy τ j k))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) (hD j)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hs] with χ hχ
  filter_upwards [hχ] with k hk
  simpa [zk, not_le] using hk

/-- **The momentum along a line**: for every real `t`, `χ(U(t e_j)) = e^{i p_j t}` almost
everywhere. Dyadics `d_k → t`, the `L²` identity with strong continuity, and Fatou's lemma.
DERIVED: `0` the half-plane and the vanishing limit; `1` the floor's width; `1/2`, `2` the dyadic
scale. -/
theorem ae_char_line (u : E) (j : Fin 4)
    (hgood : ∀ᵐ χ ∂(jointMeasure J u), ∀ᶠ k in atTop, 0 < (zk J j k χ).re) (t : ℝ) :
    ∀ᵐ χ ∂(jointMeasure J u),
      χ (UB J (t • ej τ j)) = Complex.exp (((momentum J χ j * t : ℝ) : ℂ) * Complex.I) := by
  set μ := jointMeasure J u with hμ
  let d : ℕ → ℝ := fun k => (⌊t * 2 ^ k⌋ : ℝ) * (1 / 2) ^ k
  have hd : Tendsto d atTop (𝓝 t) := by
    have hb : ∀ k : ℕ, |d k - t| ≤ (1 / 2) ^ k := by
      intro k
      have e2 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
      have e : d k - t = ((⌊t * 2 ^ k⌋ : ℝ) - t * 2 ^ k) * (1 / 2) ^ k := by
        simp only [d]; linear_combination t * e2
      rw [e, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k)]
      have h3 := Int.floor_le (t * 2 ^ k)
      have h4 := Int.lt_floor_add_one (t * 2 ^ k)
      have h5 : |(⌊t * 2 ^ k⌋ : ℝ) - t * 2 ^ k| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc _ ≤ 1 * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = _ := one_mul _
    have h0 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun k => norm_nonneg _) (fun k => by rw [Real.norm_eq_abs]; exact hb k) h0)
  let g : ℕ → Chars J → ℝ≥0∞ := fun k χ =>
    ENNReal.ofReal (Complex.normSq (χ (UB J (t • ej τ j)) - χ (UB J (d k • ej τ j))))
  have hgc : ∀ k, Continuous fun χ : Chars J =>
      Complex.normSq (χ (UB J (t • ej τ j)) - χ (UB J (d k • ej τ j))) := fun k =>
    Complex.continuous_normSq.comp
      ((map_continuous (gelfandStarTransform (alg J) (UB J (t • ej τ j)))).sub
        (map_continuous (gelfandStarTransform (alg J) (UB J (d k • ej τ j)))))
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (ENNReal.continuous_ofReal.comp (hgc k)).measurable
  have hgi : ∀ k, ∫⁻ χ, g k χ ∂μ
      = ENNReal.ofReal (‖J.R.U (t • ej τ j) u - J.R.U (d k • ej τ j) u‖ ^ 2) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hgc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall fun χ => Complex.normSq_nonneg _)]
    congr 1
    have h := integral_normSq J u (UB J (t • ej τ j) - UB J (d k • ej τ j))
    simp only [map_sub] at h
    rw [h]
    rfl
  have hU : Tendsto (fun k => J.R.U (d k • ej τ j) u) atTop (𝓝 (J.R.U (t • ej τ j) u)) :=
    (((J.R.cont u).comp (continuous_id.smul continuous_const)).tendsto t).comp hd
  have hlim : Tendsto (fun k => ∫⁻ χ, g k χ ∂μ) atTop (𝓝 0) := by
    simp_rw [hgi]
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hU).pow 2
    rw [zero_pow two_ne_zero] at h1
    have h2 : Tendsto (fun k => ‖J.R.U (t • ej τ j) u - J.R.U (d k • ej τ j) u‖ ^ 2) atTop
        (𝓝 0) := h1.congr fun k => by rw [norm_sub_rev]
    have h3 := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at h3
  have hpt : ∀ᵐ χ ∂μ, Tendsto (fun k => g k χ) atTop (𝓝 (ENNReal.ofReal (Complex.normSq
      (χ (UB J (t • ej τ j)) - Complex.exp (((momentum J χ j * t : ℝ) : ℂ) * Complex.I))))) := by
    filter_upwards [hgood] with χ hχ
    obtain ⟨K, hK⟩ := eventually_atTop.mp hχ
    have hc : Continuous fun z : ℂ =>
        ENNReal.ofReal (Complex.normSq (χ (UB J (t • ej τ j)) - z)) :=
      ENNReal.continuous_ofReal.comp (Complex.continuous_normSq.comp
        (continuous_const.sub continuous_id))
    have hcont : Continuous fun s : ℝ =>
        Complex.exp (((momentum J χ j * s : ℝ) : ℂ) * Complex.I) := by fun_prop
    have hz : Tendsto (fun k => χ (UB J (d k • ej τ j))) atTop
        (𝓝 (Complex.exp (((momentum J χ j * t : ℝ) : ℂ) * Complex.I))) := by
      refine ((hcont.tendsto t).comp hd).congr' (eventually_atTop.mpr ⟨K, fun k hk => ?_⟩)
      exact (char_line_dyadic J hK k hk ⌊t * 2 ^ k⌋).symm
    exact (hc.tendsto _).comp hz
  have hF := lintegral_liminf_le' (μ := μ) (u := atTop) (fun k => (hgm k).aemeasurable)
  rw [hlim.liminf_eq] at hF
  have hG : ∫⁻ χ, liminf (fun k => g k χ) atTop ∂μ = 0 := le_antisymm hF zero_le
  have hGm : Measurable fun χ => liminf (fun k => g k χ) atTop := Measurable.liminf hgm
  have hae := (lintegral_eq_zero_iff hGm).mp hG
  filter_upwards [hae, hpt] with χ h1 h2
  simp only [Pi.zero_apply] at h1
  rw [h2.liminf_eq] at h1
  have h3 : Complex.normSq (χ (UB J (t • ej τ j))
      - Complex.exp (((momentum J χ j * t : ℝ) : ℂ) * Complex.I)) = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp h1) (Complex.normSq_nonneg _)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp h3)

/-- **The momentum identification**: under the Dini bound, for every `x`,
`χ(U x) = e^{i p(χ)·x}` for `μ_u`-almost every `χ`. DERIVED: no numeral. -/
theorem ae_char_eq_phase {u : E} (hD : DyadicDini J u) (x : spatial τ) :
    ∀ᵐ χ ∂(jointMeasure J u),
      χ (UB J x) = Complex.exp ((phase (momentum J χ) x : ℂ) * Complex.I) := by
  have h := ae_all_iff.mpr fun j : Fin 4 =>
    ae_char_line J u j (ae_good J hD j) ((x : Fin 4 → ℝ) j)
  filter_upwards [h] with χ hχ
  conv_lhs => rw [← sum_ej x]
  rw [char_sum, phase, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => hχ j

/-- DERIVED: `2` the dyadic base. -/
theorem measurable_pseq (j : Fin 4) (k : ℕ) : Measurable (pseq J j k) := by
  show Measurable fun χ : Chars J => (2 : ℝ) ^ k * Complex.arg (χ (UB J (dy τ j k)))
  exact (Complex.measurable_arg.comp
    (map_continuous (gelfandStarTransform (alg J) (UB J (dy τ j k)))).measurable).const_mul _

/-- **The momentum is almost everywhere measurable**: an almost-everywhere limit of measurable
reads. DERIVED: no numeral. -/
theorem aemeasurable_momentum {u : E} (hD : DyadicDini J u) :
    AEMeasurable (momentum J) (jointMeasure J u) := by
  refine aemeasurable_pi_lambda _ fun j => aemeasurable_of_tendsto_metrizable_ae'
    (fun k => (measurable_pseq J j k).aemeasurable) ?_
  filter_upwards [ae_good J hD j] with χ hχ
  obtain ⟨K, hK⟩ := eventually_atTop.mp hχ
  rw [momentum_eq J hK]
  exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨K, fun k hk => (pseq_const J hK k hk).symm⟩)

/-- DERIVED: no numeral. -/
theorem continuous_phase_exp (x : spatial τ) :
    Continuous fun p : Fin 4 → ℝ => Complex.exp ((phase p x : ℂ) * Complex.I) := by
  have hφ : Continuous fun p : Fin 4 → ℝ => phase p x :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hφ).mul continuous_const)

/-- **The momentum transform is the characteristic function of the momentum measure**:
`⟪u, U x u⟫ = ∫ e^{i p·x} d(p_* μ_u)`. DERIVED: no numeral. -/
theorem inner_U_eq_momentum {u : E} (hD : DyadicDini J u) (x : spatial τ) :
    inner ℂ u (J.R.U x u) = ∫ p, Complex.exp ((phase p x : ℂ) * Complex.I)
      ∂((jointMeasure J u).map (momentum J)) := by
  rw [integral_map (aemeasurable_momentum J hD) (continuous_phase_exp x).aestronglyMeasurable,
    MassGap.ShellJoint.inner_U_eq_integral]
  exact integral_congr_ae (ae_char_eq_phase J hD x)

/-! ## 2. The joint push-forward -/

/-- **Rate and momentum of a character.** DERIVED: no numeral. -/
def rateMom (χ : Chars J) : ℝ × (Fin 4 → ℝ) := (-Real.log (tclamp J χ).1, momentum J χ)

/-- **The joint (rate, momentum) measure of `u`**: `μ_u` off the kernel `χ(a) = 0`, pushed to
rate × momentum. DERIVED: `0` the excluded kernel point. -/
def nu (u : E) : Measure (ℝ × (Fin 4 → ℝ)) :=
  ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1}).map (rateMom J)

/-- **The rate marginal of `nu` is the rate measure.** DERIVED: no numeral. -/
theorem nu_fst {u : E} (hD : DyadicDini J u) : (nu J u).map Prod.fst = rateMeasure J.a u := by
  have hm : AEMeasurable (rateMom J) ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1}) :=
    (measurable_rate.comp (continuous_tclamp J).measurable).aemeasurable.prodMk
      (aemeasurable_momentum J hD).restrict
  rw [nu, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hm,
    rateMeasure_eq_joint]
  rfl

/-- **A rate bottom of `u` is a rate bottom of `nu`**, for every `u`. DERIVED: no numeral. -/
theorem nu_Iio_prod (u : E) (g : ℝ) (h : rateMeasure J.a u (Iio g) = 0) :
    nu J u (Iio g ×ˢ univ) = 0 := by
  by_cases hm : AEMeasurable (rateMom J) ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1})
  · have hrm : Measurable fun χ : Chars J => -Real.log (tclamp J χ).1 :=
      measurable_rate.comp (continuous_tclamp J).measurable
    rw [nu, Measure.map_apply_of_aemeasurable hm (measurableSet_Iio.prod MeasurableSet.univ)]
    rw [rateMeasure_eq_joint, Measure.map_apply hrm measurableSet_Iio] at h
    convert h using 2
    ext χ
    simp [rateMom]
  · rw [nu, Measure.map_of_not_aemeasurable hm]
    rfl

end Generic2

/-! ### The zero-momentum density -/

/-- **Lebesgue measure on the spatial momenta**, with `δ₀` in the time slot. DERIVED: `0` the time
momentum. -/
def lamF (τ j : Fin 4) : Measure ℝ := if j = τ then Measure.dirac 0 else volume

instance (τ j : Fin 4) : SigmaFinite (lamF τ j) := by
  unfold lamF; split_ifs <;> infer_instance

/-- DERIVED: no numeral. -/
def lam (τ : Fin 4) : Measure (Fin 4 → ℝ) := Measure.pi (lamF τ)

/-- **The momentum window has volume `(2ε)³`.** DERIVED: `2` the two sides of the interval; `3` the
spatial dimension, the four coordinates less the time. -/
theorem lam_ball (τ : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    lam τ (Metric.ball 0 ε) = ENNReal.ofReal (2 * ε) ^ 3 := by
  rw [lam, ball_pi _ hε, Measure.pi_pi]
  have hf : ∀ j, lamF τ j (Metric.ball ((0 : Fin 4 → ℝ) j) ε)
      = if j = τ then 1 else ENNReal.ofReal (2 * ε) := by
    intro j
    unfold lamF
    split_ifs
    · exact Measure.dirac_apply_of_mem (Metric.mem_ball_self hε)
    · exact Real.volume_ball _ _
  simp only [hf]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hc : (Finset.univ.filter fun j : Fin 4 => ¬ j = τ).card = 3 := by
    fin_cases τ <;> decide
  rw [hc]

/-- **The rate measure seen through the momentum window** `B(0, ε)`, the sup-norm ball. DERIVED: `0` the zero
momentum. -/
def windowed (ν : Measure (ℝ × (Fin 4 → ℝ))) (ε : ℝ) : Measure ℝ :=
  (ν.restrict (univ ×ˢ Metric.ball 0 ε)).map Prod.fst

/-- **The zero-momentum density**: the windowed rate measures, divided by the window's volume,
converge weakly as `ε → 0⁺`: the integral of every bounded continuous non-negative `f` against
windowed `ν ε / λ(B(0, ε))` tends to its integral against `σ₀` (Lebesgue differentiation at `p = 0`).
DERIVED: `0` the zero momentum and the shrinking
radius. -/
def ZeroDensity (τ : Fin 4) (ν : Measure (ℝ × (Fin 4 → ℝ))) (σ0 : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ≥0, Continuous f → BddAbove (range f) →
    Tendsto (fun ε => (∫⁻ s, (f s : ℝ≥0∞) ∂(windowed ν ε)) / lam τ (Metric.ball 0 ε))
      (𝓝[>] 0) (𝓝 (∫⁻ s, (f s : ℝ≥0∞) ∂σ0))

/-- DERIVED: no numeral. -/
theorem windowed_Iio {ν : Measure (ℝ × (Fin 4 → ℝ))} {g : ℝ} (h : ν (Iio g ×ˢ univ) = 0)
    (ε : ℝ) : windowed ν ε (Iio g) = 0 := by
  rw [windowed, Measure.map_apply measurable_fst measurableSet_Iio,
    Measure.restrict_apply (measurable_fst measurableSet_Iio)]
  refine measure_mono_null ?_ h
  exact fun q hq => ⟨hq.1, trivial⟩

/-- **A rate bottom passes to the density**: `ν (−∞, g) × ℝ⁴ = 0` gives `σ₀ (−∞, g) = 0`.
DERIVED: `0` the vanishing test integral; `1` the top of the test ramp and the unit fractions. -/
theorem zeroDensity_bottom {τ : Fin 4} {ν : Measure (ℝ × (Fin 4 → ℝ))} {σ0 : Measure ℝ} {g : ℝ}
    (hσ : ZeroDensity τ ν σ0) (h : ν (Iio g ×ˢ univ) = 0) : σ0 (Iio g) = 0 := by
  have key : ∀ g', g' < g → σ0 (Iic g') = 0 := by
    intro g' hg'
    let f : ℝ → ℝ≥0 := fun x => Real.toNNReal (min 1 ((g - x) / (g - g')))
    have hfc : Continuous f := continuous_real_toNNReal.comp
      (continuous_const.min ((continuous_const.sub continuous_id).div_const _))
    have hfb : BddAbove (range f) := bddAbove_def.mpr ⟨1, by
      rintro _ ⟨x, rfl⟩
      exact (Real.toNNReal_le_toNNReal (min_le_left _ _)).trans (by simp)⟩
    have h0 : ∀ ε, ∫⁻ s, (f s : ℝ≥0∞) ∂(windowed ν ε) = 0 := by
      intro ε
      have hae := measure_eq_zero_iff_ae_notMem.mp (windowed_Iio h ε)
      rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
      filter_upwards [hae] with x hx
      have hx' : g ≤ x := not_lt.mp hx
      have hn : (g - x) / (g - g') ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      simp only [f, ENNReal.coe_eq_zero]
      exact Real.toNNReal_eq_zero.mpr ((min_le_right _ _).trans hn)
    have hlim := hσ f hfc hfb
    simp only [h0, ENNReal.zero_div] at hlim
    have hz : ∫⁻ s, (f s : ℝ≥0∞) ∂σ0 = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
    refine nonpos_iff_eq_zero.mp ?_
    calc σ0 (Iic g') = ∫⁻ x, (Iic g').indicator 1 x ∂σ0 :=
          (lintegral_indicator_one measurableSet_Iic).symm
      _ ≤ ∫⁻ x, (f x : ℝ≥0∞) ∂σ0 := lintegral_mono fun x => by
          by_cases hx : x ∈ Iic g'
          · rw [indicator_of_mem hx, Pi.one_apply]
            have h1 : 1 ≤ (g - x) / (g - g') := by
              rw [le_div_iff₀ (by linarith)]; linarith [mem_Iic.mp hx]
            simp only [f, min_eq_left h1, Real.toNNReal_one, ENNReal.coe_one, le_refl]
          · rw [Set.indicator_of_notMem hx]; exact zero_le
      _ = 0 := hz
  have hsub : Iio g ⊆ ⋃ n : ℕ, Iic (g - 1 / (n + 1)) := fun x hx => by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (mem_Iio.mp hx))
    exact mem_iUnion.mpr ⟨n, mem_Iic.mpr (by linarith)⟩
  exact measure_mono_null hsub (measure_iUnion_null fun n => key _ (by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith))

/-- **The Clay gap bounds `ρ`'s bottom through a sector bottom**: `σ 0 (−∞, X.gap) = 0` under
Källén–Lehmann form with `ρ (Iic 0) = 0` gives `X.gap² ≤ M2` (the argument of
`ShellGap.clay_gap_sq_le`, from the sector's bottom). DERIVED: `0` the zero momentum and the support
bound; `2` the square. -/
theorem gap_sq_le_of_sector (X : OSDataS) {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hkl : KallenLehmann σ ρ) (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2)
    (h0 : σ 0 (Iio X.gap) = 0) : X.gap ^ 2 ≤ M2 := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hg := X.gap_pos
  rw [hkl 0 le_rfl, Measure.map_apply (measurable_shell 0) measurableSet_Iio,
    withDensity_apply_eq_zero (measurable_klWeight 0)] at h0
  have hp := hb.2 (X.gap ^ 2 - M2) (sub_pos.mpr hlt)
  rw [add_sub_cancel] at hp
  have hsub : Ico M2 (X.gap ^ 2) ⊆
      ({s | klWeight 0 s ≠ 0} ∩ (fun s => shell s 0) ⁻¹' Iio X.gap) ∪ Iic 0 := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · exact Or.inr hs0
    · have hsh : 0 < shell s 0 := by unfold shell; rw [add_zero]; exact Real.sqrt_pos.mpr hs0
      refine Or.inl (Set.mem_inter ?_ ?_)
      · simp only [mem_setOf_eq, klWeight, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact one_div_pos.mpr (mul_pos two_pos hsh)
      · simp only [mem_preimage, mem_Iio, shell, add_zero]
        rw [Real.sqrt_lt' hg]
        exact hs.2
  have := (measure_mono (μ := ρ) hsub).trans (measure_union_le (μ := ρ) _ _)
  rw [h0, hρ0, add_zero] at this
  exact (lt_of_lt_of_le hp this).false

/-- **The Clay read of the zero-momentum density.** For joint data `J` on the Clay object with time
step `X.time 1`, a vector `u` of the vacuum complement, Källén–Lehmann data with the support clause,
and the corrected identification `hσ'` (`σ 0` is the density at `p = 0` of `nu J u`): the sector
vanishes below the gap, `0 < M2`, `X.gap ≤ √M2`, `σ 0` has bottom `√M2`, and every momentum has band
excess. `hσ'` is undischarged. DERIVED: `0` the zero momentum, the signs and the vanishing pairing;
`1` the unit step; `2` the square. -/
theorem clay_zero_momentum_density {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {σ : ℝ → Measure ℝ}
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hkl : KallenLehmann σ ρ) (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ}
    (hb : SpecBottom ρ M2) (hσ' : ZeroDensity τ (nu J u) (σ 0)) :
    σ 0 (Iio X.gap) = 0 ∧ 0 < M2 ∧ X.gap ≤ Real.sqrt M2 ∧ SpecBottom (σ 0) (Real.sqrt M2)
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 := by
  have hr : rateMeasure J.a u (Iio X.gap) = 0 := by rw [hJ]; exact gap_rateBottom X u hu
  have h0 := zeroDensity_bottom hσ' (nu_Iio_prod J u X.gap hr)
  have hsq := gap_sq_le_of_sector X hkl hρ0 hb h0
  have hg := X.gap_pos
  have hM : 0 < M2 := lt_of_lt_of_le (pow_pos hg 2) hsq
  have hM0 : 0 < M2 + 0 := by rw [add_zero]; exact hM
  have hsh : shell M2 0 = Real.sqrt M2 := by unfold shell; rw [add_zero]
  have hbot := specBottom_klSector hkl hb le_rfl hM0
  rw [hsh] at hbot
  refine ⟨h0, hM, (Real.le_sqrt' hg).mpr hsq, hbot, fun p2 hp => ?_⟩
  exact (MassGap.BandShell.gap_iff_band_excess (MassGap.BandShell.specBottom_dirac M2) hp
    (by linarith) (MassGap.BandShell.shell_rate (MassGap.BandShell.specBottom_dirac M2)
      (by linarith))).mp hM

/-! ## 3. Load tests -/

section Vacuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {τ : Fin 4} (J : JointData E (spatial τ))

/-- **A translation-fixed vector reads momentum `0`.** DERIVED: `0` the momentum; `1` the trivial
value. -/
theorem vacuum_momentum {v : E} (hU : ∀ x, J.R.U x v = v) :
    ∀ᵐ χ ∂(jointMeasure J v), momentum J χ = 0 := by
  have h : ∀ᵐ χ ∂(jointMeasure J v), ∀ j k, zk J j k χ = 1 :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      ae_eq_of_eigen J v (UB J (dy τ j k)) 1 (by rw [one_smul]; exact hU _)
  filter_upwards [h] with χ hχ
  funext j
  have hp : ∀ k, pseq J j k χ = 0 := fun k => by
    simp only [pseq]; rw [hχ j k, Complex.arg_one, mul_zero]
  show limUnder atTop (fun k => pseq J j k χ) = 0
  simp only [hp]
  exact tendsto_const_nhds.limUnder_eq

/-- **The vacuum is the atom at (rate `0`, momentum `0`).** DERIVED: `0` the rate and momentum of
the vacuum; `1` the fixed value. -/
theorem nu_vacuum {v : E} (ha : J.a v = v) (hU : ∀ x, J.R.U x v = v) :
    nu J v = (jointMeasure J v univ) • Measure.dirac ((0 : ℝ), (0 : Fin 4 → ℝ)) := by
  have h1 : ∀ᵐ χ ∂(jointMeasure J v), χ (aB J) = 1 :=
    ae_eq_of_eigen J v (aB J) 1 (by rw [one_smul]; exact ha)
  have ht : ∀ᵐ χ ∂(jointMeasure J v), (tclamp J χ).1 = 1 := by
    filter_upwards [h1] with χ hχ
    show (clamp (χ (aB J)).re).1 = 1
    rw [hχ, Complex.one_re, clamp, projIcc_right]
  have hset : {χ : Chars J | 0 < (tclamp J χ).1} =ᵐ[jointMeasure J v] (univ : Set (Chars J)) := by
    filter_upwards [ht] with χ hχ
    simp only [eq_iff_iff]
    show (0 < (tclamp J χ).1) ↔ True
    rw [hχ]; exact iff_of_true zero_lt_one trivial
  have hfun : rateMom J =ᵐ[jointMeasure J v] fun _ => ((0 : ℝ), (0 : Fin 4 → ℝ)) := by
    filter_upwards [ht, vacuum_momentum J hU] with χ hχ hm
    simp only [rateMom, hχ, hm, Real.log_one, neg_zero]
  rw [nu, Measure.restrict_congr_set hset, Measure.restrict_univ, Measure.map_congr hfun,
    Measure.map_const]

/-- **The vacuum has no zero-momentum density**: its atom over the shrinking window diverges, so no
finite `σ₀` is its density. DERIVED: `0` the vanishing radius and the vacuum's point; `1` the test
function; `2`, `3` as in `lam_ball`. -/
theorem vacuum_no_density {v : E} (hv : v ≠ 0) (ha : J.a v = v) (hU : ∀ x, J.R.U x v = v)
    (σ0 : Measure ℝ) [IsFiniteMeasure σ0] : ¬ ZeroDensity τ (nu J v) σ0 := by
  intro hσ
  have h1 := hσ (fun _ => 1) continuous_const ⟨1, by rintro _ ⟨x, rfl⟩; exact le_rfl⟩
  simp only [ENNReal.coe_one, lintegral_one] at h1
  have hw : ∀ ε, 0 < ε → windowed (nu J v) ε univ = jointMeasure J v univ := by
    intro ε hε
    rw [windowed, Measure.map_apply measurable_fst MeasurableSet.univ,
      Measure.restrict_apply (measurable_fst MeasurableSet.univ), nu_vacuum J ha hU,
      Measure.smul_apply, Measure.dirac_apply_of_mem, smul_eq_mul, mul_one]
    exact ⟨trivial, trivial, Metric.mem_ball_self hε⟩
  have hm : 0 < jointMeasure J v univ := by
    have hpos : 0 < (jointMeasure J v).real univ := by
      rw [MassGap.ShellJoint.jointMeasure_real_univ]; exact pow_pos (norm_pos_iff.mpr hv) 2
    exact (ENNReal.toReal_pos_iff.mp hpos).1
  have hvol : Tendsto (fun ε => lam τ (Metric.ball 0 ε)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 0) := by
      simpa using ((by fun_prop : Continuous fun ε : ℝ => 2 * ε).tendsto 0)
    have h3 := ENNReal.tendsto_ofReal hc
    rw [ENNReal.ofReal_zero] at h3
    have h4 : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * ε) ^ 3) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.pow (n := 3) (h3.mono_left nhdsWithin_le_nhds)
    refine h4.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (lam_ball τ hε).symm
  have hinv : Tendsto (fun ε => jointMeasure J v univ / lam τ (Metric.ball 0 ε)) (𝓝[>] 0)
      (𝓝 ⊤) := by
    have hi : Tendsto (fun ε => (lam τ (Metric.ball 0 ε))⁻¹) (𝓝[>] 0) (𝓝 ⊤) := by
      simpa using ENNReal.tendsto_inv_iff.mpr hvol
    have h5 := ENNReal.Tendsto.const_mul hi (Or.inr (measure_ne_top (jointMeasure J v) univ))
    rw [ENNReal.mul_top hm.ne'] at h5
    simpa [div_eq_mul_inv] using h5
  have hlim : Tendsto (fun ε => jointMeasure J v univ / lam τ (Metric.ball 0 ε)) (𝓝[>] 0)
      (𝓝 (σ0 univ)) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hw ε hε]
  exact absurd (tendsto_nhds_unique hlim hinv) (measure_ne_top σ0 univ)

end Vacuum

/-- **Averages of a function continuous at `0` over the shrinking window converge to its value.**
DERIVED: `0` the window's centre. -/
theorem avg_tendsto (τ : Fin 4) {F : (Fin 4 → ℝ) → ℝ≥0∞} (hF : ContinuousAt F 0) (hF0 : F 0 ≠ ⊤) :
    Tendsto (fun ε => (∫⁻ p in Metric.ball 0 ε, F p ∂lam τ) / lam τ (Metric.ball 0 ε)) (𝓝[>] 0)
      (𝓝 (F 0)) := by
  rw [ENNReal.tendsto_nhds hF0]
  intro η hη
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((ENNReal.tendsto_nhds hF0).mp hF η hη)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hε0 : 0 < ε := hε.1
  have hV0 : lam τ (Metric.ball 0 ε) ≠ 0 := by
    rw [lam_ball τ hε0]; exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hVt : lam τ (Metric.ball 0 ε) ≠ ⊤ := by
    rw [lam_ball τ hε0]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hin : ∀ p ∈ Metric.ball (0 : Fin 4 → ℝ) ε, F p ∈ Icc (F 0 - η) (F 0 + η) := fun p hp =>
    hball p (Metric.ball_subset_ball hε.2.le hp)
  have hae := ae_restrict_of_forall_mem (μ := lam τ) Metric.isOpen_ball.measurableSet hin
  constructor
  · calc F 0 - η = (F 0 - η) * lam τ (Metric.ball 0 ε) / lam τ (Metric.ball 0 ε) :=
          (ENNReal.mul_div_cancel_right hV0 hVt).symm
      _ ≤ _ := by
          refine ENNReal.div_le_div_right ?_ _
          rw [← setLIntegral_const]
          exact lintegral_mono_ae (hae.mono fun p hp => hp.1)
  · calc _ ≤ (F 0 + η) * lam τ (Metric.ball 0 ε) / lam τ (Metric.ball 0 ε) := by
          refine ENNReal.div_le_div_right ?_ _
          rw [← setLIntegral_const]
          exact lintegral_mono_ae (hae.mono fun p hp => hp.2)
      _ = F 0 + η := ENNReal.mul_div_cancel_right hV0 hVt

/-- **The free superposition**: momentum profile `g` against `lam τ`, each momentum on its shell
`√(m² + |p|²)`. DERIVED: `2` the square of the momentum. -/
def freeJoint (τ : Fin 4) (m2 : ℝ) (g : (Fin 4 → ℝ) → ℝ≥0) : Measure (ℝ × (Fin 4 → ℝ)) :=
  ((lam τ).withDensity fun p => (g p : ℝ≥0∞)).map fun p => (shell m2 (∑ j, p j ^ 2), p)

/-- **The free superposition has zero-momentum density `g(0) δ_{shell(m², 0)}`.** DERIVED: `0` the
zero momentum; `2` as in `freeJoint`. -/
theorem free_zeroDensity (τ : Fin 4) (m2 : ℝ) {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) :
    ZeroDensity τ (freeJoint τ m2 g) ((g 0 : ℝ≥0∞) • Measure.dirac (shell m2 0)) := by
  intro f hf _
  have hω : Continuous fun p : Fin 4 → ℝ => shell m2 (∑ j, p j ^ 2) := by
    unfold shell; fun_prop
  have hΦ : Measurable fun p : Fin 4 → ℝ => (shell m2 (∑ j, p j ^ 2), p) :=
    (hω.prodMk continuous_id).measurable
  have hF : Continuous fun p : Fin 4 → ℝ =>
      ((g p * f (shell m2 (∑ j, p j ^ 2)) : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.continuous_coe.comp (hg.mul (hf.comp hω))
  have hfm : Measurable fun s : ℝ => (f s : ℝ≥0∞) := (ENNReal.continuous_coe.comp hf).measurable
  have hfm2 : Measurable fun q : ℝ × (Fin 4 → ℝ) => (f q.1 : ℝ≥0∞) := hfm.comp measurable_fst
  have hfm3 : Measurable fun p : Fin 4 → ℝ => (f (shell m2 (∑ j, p j ^ 2)) : ℝ≥0∞) :=
    hfm.comp hω.measurable
  have hgm : Measurable fun p : Fin 4 → ℝ => (g p : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp hg).measurable
  have hwin : ∀ ε, ∫⁻ s, (f s : ℝ≥0∞) ∂(windowed (freeJoint τ m2 g) ε)
      = ∫⁻ p in Metric.ball 0 ε, ((g p * f (shell m2 (∑ j, p j ^ 2)) : ℝ≥0) : ℝ≥0∞) ∂lam τ := by
    intro ε
    have hS : MeasurableSet ((univ : Set ℝ) ×ˢ Metric.ball (0 : Fin 4 → ℝ) ε) :=
      MeasurableSet.univ.prod Metric.isOpen_ball.measurableSet
    have hpre : (fun p : Fin 4 → ℝ => (shell m2 (∑ j, p j ^ 2), p)) ⁻¹'
        (univ ×ˢ Metric.ball 0 ε) = Metric.ball 0 ε := by
      ext p; simp
    rw [windowed, lintegral_map hfm measurable_fst, freeJoint, Measure.restrict_map hΦ hS,
      lintegral_map hfm2 hΦ, hpre, restrict_withDensity Metric.isOpen_ball.measurableSet]
    exact (lintegral_withDensity_eq_lintegral_mul _ hgm hfm3).trans
      (lintegral_congr fun p => by simp [ENNReal.coe_mul])
  have hR : ∫⁻ s, (f s : ℝ≥0∞) ∂((g 0 : ℝ≥0∞) • Measure.dirac (shell m2 0))
      = ((g 0 * f (shell m2 (∑ j, (0 : Fin 4 → ℝ) j ^ 2)) : ℝ≥0) : ℝ≥0∞) := by
    rw [lintegral_smul_measure, lintegral_dirac]
    simp [ENNReal.coe_mul]
  simp_rw [hwin]
  rw [hR]
  exact avg_tendsto τ hF.continuousAt ENNReal.coe_ne_top

/-- **The free load test**: a superposition of free plane waves of mass `m ≥ 0` with a continuous
momentum profile `g`, `g(0) ≠ 0`, has a non-zero zero-momentum density, `g(0) δ_m`, on the shell
`√(m² + 0) = m`. DERIVED: `0` the zero momentum; `2` the square. CHOSEN (the test's free data):
`m` and `g`, every value. -/
theorem free_density_shell (τ : Fin 4) {m : ℝ} (hm : 0 ≤ m) {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Continuous g) (hg0 : g 0 ≠ 0) :
    ZeroDensity τ (freeJoint τ (m ^ 2) g) ((g 0 : ℝ≥0∞) • Measure.dirac m)
      ∧ (g 0 : ℝ≥0∞) • Measure.dirac m ≠ 0 := by
  have hsh : shell (m ^ 2) 0 = m := by unfold shell; rw [add_zero, Real.sqrt_sq hm]
  have h := free_zeroDensity τ (m ^ 2) hg
  rw [hsh] at h
  refine ⟨h, fun h0 => hg0 ?_⟩
  have := congrArg (fun μ : Measure ℝ => μ univ) h0
  simpa using this

/-- **The read momentum of a plane wave is its momentum** in every spatial direction.
DERIVED: `0` the vanishing scale; `1/2`, `2` the dyadic scale; `π` the branch of the argument. -/
theorem planeWave_momentum (τ : Fin 4) (p : Fin 4 → ℝ) {ω : ℝ} (hω : 0 ≤ ω) :
    ∀ᵐ χ ∂(jointMeasure (planeData τ p hω) 1), ∀ j, j ≠ τ →
      momentum (planeData τ p hω) χ j = p j := by
  have h := ae_all_iff.mpr fun j : Fin 4 => ae_all_iff.mpr fun k : ℕ =>
    (planeWave_dirac τ p hω (dy τ j k)).1
  filter_upwards [h] with χ hχ
  intro j hj
  have hph : ∀ k, phase p (dy τ j k) = p j * (1 / 2) ^ k := by
    intro k
    show ∑ i, p i * (((1 / 2 : ℝ) ^ k • (fun i => if i = τ then (0 : ℝ) else if i = j then 1 else 0))
      i) = _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hi; simp [hi]
    · intro hn; exact absurd (Finset.mem_univ j) hn
  have hsmall : ∀ᶠ k in atTop, |p j * (1 / 2) ^ k| < Real.pi := by
    have h0 : Tendsto (fun k : ℕ => p j * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (p j)
    have h2 := h0.abs
    rw [abs_zero] at h2
    exact h2.eventually (gt_mem_nhds Real.pi_pos)
  have hp : ∀ᶠ k in atTop, pseq (planeData τ p hω) j k χ = p j := by
    filter_upwards [hsmall] with k hk
    obtain ⟨hk1, hk2⟩ := abs_lt.mp hk
    have e : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
    simp only [pseq, zk]
    rw [hχ j k, hph k, Complex.exp_mul_I,
      Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩]
    linear_combination (p j) * e
  exact (tendsto_const_nhds.congr' (hp.mono fun k hk => hk.symm)).limUnder_eq

end

end MassGap.ShellDensity

#print axioms MassGap.ShellDensity.normSq_char
#print axioms MassGap.ShellDensity.char_zsmul
#print axioms MassGap.ShellDensity.char_sum
#print axioms MassGap.ShellDensity.integral_normSq
#print axioms MassGap.ShellDensity.measure_re_nonpos_le
#print axioms MassGap.ShellDensity.sum_ej
#print axioms MassGap.ShellDensity.arg_sq
#print axioms MassGap.ShellDensity.zk_sq
#print axioms MassGap.ShellDensity.pseq_const
#print axioms MassGap.ShellDensity.momentum_eq
#print axioms MassGap.ShellDensity.zk_eq_exp
#print axioms MassGap.ShellDensity.char_line_dyadic
#print axioms MassGap.ShellDensity.ae_good
#print axioms MassGap.ShellDensity.ae_char_line
#print axioms MassGap.ShellDensity.ae_char_eq_phase
#print axioms MassGap.ShellDensity.aemeasurable_momentum
#print axioms MassGap.ShellDensity.inner_U_eq_momentum
#print axioms MassGap.ShellDensity.nu_fst
#print axioms MassGap.ShellDensity.nu_Iio_prod
#print axioms MassGap.ShellDensity.lam_ball
#print axioms MassGap.ShellDensity.zeroDensity_bottom
#print axioms MassGap.ShellDensity.gap_sq_le_of_sector
#print axioms MassGap.ShellDensity.clay_zero_momentum_density
#print axioms MassGap.ShellDensity.vacuum_momentum
#print axioms MassGap.ShellDensity.nu_vacuum
#print axioms MassGap.ShellDensity.vacuum_no_density
#print axioms MassGap.ShellDensity.avg_tendsto
#print axioms MassGap.ShellDensity.free_zeroDensity
#print axioms MassGap.ShellDensity.free_density_shell
#print axioms MassGap.ShellDensity.planeWave_momentum
