import Mathlib

/-!
# MassGap.PurityFreeField — elementary scalar steps of Proposition B.1 of the purity paper

Proposition B.1 (a matched ultraviolet coefficient without an infrared gap) of D. Bhattacharjee,
U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity
Bounds for Yang–Mills Theory at Weak Coupling* (research draft, 15 November 2026,
<https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

The generalized free field has squared-mass density `ρ(s) = c s² / log²(e + s)`,
`c = d∗/(16π²)`; after `u = r√s`, `L = log(1/r)`, (B.1) has integrand
`u⁶ K₁(u) L² / log²(e + u²/r²)` and prefactor `c/(2π²)`.

* `energy_mem`: every point of `0 < s < ε²/4`, `|p| < ε/2` has energy `√(|p|² + s)` in `(0, ε)`.
* `quotient_tendsto_L`, `quotient_tendsto`: at fixed `u > 0`,
  `L² / log²(e + u²/r²) → 1/4` as `r → 0⁺` (`L = log(1/r)`).
* `poly_integral`: `∫₀¹ (1 − z²)² dz = 8/15`; `moment_value`: `6! · 8/15 = 384`.
* `limit_coeff`: `c/(2π²) · 384 · 1/4 = 48c/π²`; `limit_constant`: `= 3d∗/π⁴` for `c = d∗/(16π²)`.

`K₁`, its representation `∫₀^∞ e^{−u√(1+q²)} dq`, `K₁(u) ≤ 1/u`, the Tonelli step
`∫₀^∞ u⁶ K₁ = 6! ∫₀^∞ sech⁶`, `∫₀^∞ sech⁶ = ∫₀¹ (1 − z²)² = 8/15`, `∫₀^∞ u⁶ K₁ = 384` and
the integrability of `u⁶ K₁` on `(0, ∞)` are `PurityBesselK`; integrability of the `C` integrand,
the change of variables (B.1) and the limit `r⁸ log²(1/r) C(r) → 3d∗/π⁴` are `PurityFreeFieldLimit`.

Not formalized here: the Wightman construction, Fock space, locality and positivity of the
generalized free field; temperedness of `ρ`; the identification of the field's separated
Euclidean-time covariance with the `K₁` integral `PurityFreeFieldLimit.C` (taken there as its
definition); uniqueness of the vacuum; the divergence of the raw Euclidean momentum integral.
The positive measure of the low-energy region, `E > 0` almost everywhere and the no-gap
conclusion for the one-particle measure are `PurityFreeFieldSpectrum`.
-/

namespace MassGap.PurityFreeField

open Real Filter Topology intervalIntegral

/-- `0 < s < ε²/4`, `0 ≤ p < ε/2` give `0 < √(p² + s) < ε`. -/
theorem energy_mem {s p ε : ℝ} (hs : 0 < s) (hsε : s < ε ^ 2 / 4) (hp : 0 ≤ p) (hpε : p < ε / 2) :
    0 < sqrt (p ^ 2 + s) ∧ sqrt (p ^ 2 + s) < ε := by
  have hε : 0 < ε := by linarith
  refine ⟨sqrt_pos.2 (by positivity), ?_⟩
  rw [sqrt_lt' hε]
  nlinarith

/-- `log(e + u² e^{2L}) = 2L + log(u² + e^{1−2L})`. -/
theorem log_split (u L : ℝ) (hu : 0 < u) :
    log (exp 1 + u ^ 2 * exp (2 * L)) = 2 * L + log (u ^ 2 + exp (1 - 2 * L)) := by
  have h : exp 1 + u ^ 2 * exp (2 * L) = exp (2 * L) * (u ^ 2 + exp (1 - 2 * L)) := by
    rw [mul_add, ← exp_add]
    ring_nf
  rw [h, log_mul (exp_pos _).ne' (by positivity), log_exp]

/-- At fixed `u > 0`, `L² / log²(e + u² e^{2L}) → 1/4` as `L → ∞`. -/
theorem quotient_tendsto_L {u : ℝ} (hu : 0 < u) :
    Tendsto (fun L : ℝ => L ^ 2 / log (exp 1 + u ^ 2 * exp (2 * L)) ^ 2) atTop (𝓝 (1 / 4)) := by
  set g : ℝ → ℝ := fun L => log (u ^ 2 + exp (1 - 2 * L)) with hgdef
  have h1 : Tendsto (fun L : ℝ => exp (1 - 2 * L)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    have : Tendsto (fun L : ℝ => -(2 * L)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop two_pos)
    simpa [sub_eq_neg_add, add_comm] using this.atBot_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hg : Tendsto g atTop (𝓝 (log (u ^ 2))) := by
    have := (tendsto_const_nhds (x := u ^ 2)).add h1
    rw [add_zero] at this
    exact this.log (by positivity)
  have hq : Tendsto (fun L => (1 / (2 + g L / L)) ^ 2) atTop (𝓝 ((1 / (2 + 0)) ^ 2)) :=
    ((tendsto_const_nhds.div (tendsto_const_nhds.add (hg.div_atTop tendsto_id))
      (by norm_num)).pow 2)
  rw [show ((1 : ℝ) / (2 + 0)) ^ 2 = 1 / 4 by norm_num] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [log_split u L hu, ← div_pow,
    show 2 + g L / L = (2 * L + g L) / L by field_simp, one_div_div]

/-- At fixed `u > 0`, `log²(1/r) / log²(e + u²/r²) → 1/4` as `r → 0⁺`. -/
theorem quotient_tendsto {u : ℝ} (hu : 0 < u) :
    Tendsto (fun r : ℝ => log (1 / r) ^ 2 / log (exp 1 + u ^ 2 / r ^ 2) ^ 2) (𝓝[>] 0)
      (𝓝 (1 / 4)) := by
  have hL : Tendsto (fun r : ℝ => log (1 / r)) (𝓝[>] 0) atTop := by
    refine (tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).congr' (Eventually.of_forall fun r => ?_)
    simp only [Function.comp_apply, one_div]
  refine ((quotient_tendsto_L hu).comp hL).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_apply]
  rw [show exp (2 * log (1 / r)) = 1 / r ^ 2 by
    rw [mul_comm, exp_mul, exp_log (by positivity)]; norm_cast; ring, mul_one_div]

/-- `∫₀¹ (1 − z²)² dz = 8/15`. -/
theorem poly_integral : ∫ z in (0 : ℝ)..1, (1 - z ^ 2) ^ 2 = 8 / 15 := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => z - 2 * z ^ 3 / 3 + z ^ 5 / 5) ((1 - x ^ 2) ^ 2) x := by
    intro x _
    exact (((hasDerivAt_id' x).sub (((hasDerivAt_pow 3 x).const_mul 2).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 5)).congr_deriv (by norm_num; ring)
  rw [integral_eq_sub_of_hasDerivAt hF (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

/-- `6! · 8/15 = 384`. -/
theorem moment_value : (Nat.factorial 6 : ℝ) * (8 / 15) = 384 := by
  norm_num [Nat.factorial]

/-- `c/(2π²) · 384 · 1/4 = 48c/π²`. -/
theorem limit_coeff (c : ℝ) : c / (2 * π ^ 2) * 384 * (1 / 4) = 48 * c / π ^ 2 := by
  have := pi_pos
  field_simp
  ring

/-- `c/(2π²) · 384 · 1/4 = 3d∗/π⁴` for `c = d∗/(16π²)`. -/
theorem limit_constant (d : ℝ) : d / (16 * π ^ 2) / (2 * π ^ 2) * 384 * (1 / 4) = 3 * d / π ^ 4 := by
  have := pi_pos
  field_simp
  ring

end MassGap.PurityFreeField

#print axioms MassGap.PurityFreeField.energy_mem
#print axioms MassGap.PurityFreeField.log_split
#print axioms MassGap.PurityFreeField.quotient_tendsto_L
#print axioms MassGap.PurityFreeField.quotient_tendsto
#print axioms MassGap.PurityFreeField.poly_integral
#print axioms MassGap.PurityFreeField.moment_value
#print axioms MassGap.PurityFreeField.limit_coeff
#print axioms MassGap.PurityFreeField.limit_constant
