import Mathlib

/-!
# The fluctuation-dissipation theorem (finite Gibbs systems)

A susceptibility is the response of a mean to the coupling, and this module proves **from scratch, with
no axiom**, in the finite Gibbs case, that such a response is a covariance, and for the energy itself a
variance, hence nonnegative:

  `χ = -dU/dβ = Var(E) = ⟨E²⟩ - ⟨E⟩² ≥ 0` ,   and generally  `d⟨A⟩/dβ = -Cov(A, E)`.

This is the fluctuation-dissipation archetype: a susceptibility is nonnegative because it is a variance.
The Shannon disorder susceptibility (the Rényi-1 no-bulk-transition response, distinct from the min-entropy
tension whose interior bound A1 consumes via `Complete.d2_le_govern`) is `χ_v = -dH/d\beta` with
`H` the entropy read; its sign is proved deterministically in `Majorization.entropy_antitone` (entropy
falls under concentration). This module is the general covariance identity behind that picture; it takes
no axiom beyond the standard three.
-/

namespace MassGap.Fluctuation

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The finite partition function `Z(β) = ∑ exp(-β Eᵢ)`. -/
noncomputable def Zf (E : ι → ℝ) (β : ℝ) : ℝ := ∑ i, Real.exp (-β * E i)
/-- The Gibbs-weighted energy sum `∑ Eᵢ exp(-β Eᵢ)` (so `⟨E⟩ = N/Z`). -/
noncomputable def Nf (E : ι → ℝ) (β : ℝ) : ℝ := ∑ i, E i * Real.exp (-β * E i)
/-- The Gibbs-weighted squared-energy sum `∑ Eᵢ² exp(-β Eᵢ)` (so `⟨E²⟩ = S2/Z`).

DERIVED: the exponent `2` is the definition of a SECOND moment — the quantity the variance subtracts
the squared mean from. Nothing selects it; it is what `Var = ⟨E²⟩ - ⟨E⟩²` says. -/
noncomputable def S2f (E : ι → ℝ) (β : ℝ) : ℝ := ∑ i, (E i) ^ 2 * Real.exp (-β * E i)
/-- The mean energy `U(β) = ⟨E⟩_β = N/Z`. -/
noncomputable def Uf (E : ι → ℝ) (β : ℝ) : ℝ := Nf E β / Zf E β
/-- The energy variance `Var(β) = ⟨E²⟩ - ⟨E⟩² = S2/Z - U²`.

DERIVED: the exponent `2` is the square of the mean that the definition of a variance subtracts; it
matches `S2f`'s second moment by construction, and no other exponent yields a variance. -/
noncomputable def Varf (E : ι → ℝ) (β : ℝ) : ℝ := S2f E β / Zf E β - (Uf E β) ^ 2

theorem Zf_pos (E : ι → ℝ) (β : ℝ) : 0 < Zf E β :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype ι] [Nonempty ι] in
/-- `exp(-β Eᵢ/2) · exp(-β Eᵢ/2) = exp(-β Eᵢ)`, the half-weight identity. -/
private theorem mul_half_exp (E : ι → ℝ) (β : ℝ) (i : ι) :
    Real.exp (-(β * E i) / 2) * Real.exp (-(β * E i) / 2) = Real.exp (-β * E i) := by
  rw [← Real.exp_add]; congr 1; ring

/-- **The variance is nonnegative** (Cauchy-Schwarz): `⟨E⟩² ≤ ⟨E²⟩`, so `Var = ⟨E²⟩ - ⟨E⟩² ≥ 0`. -/
theorem Varf_nonneg (E : ι → ℝ) (β : ℝ) : 0 ≤ Varf E β := by
  have hZ : 0 < Zf E β := Zf_pos E β
  have hZne : Zf E β ≠ 0 := ne_of_gt hZ
  -- Cauchy-Schwarz with the half-weights exp(-β Eᵢ/2): `N² ≤ S2 · Z`.
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => E i * Real.exp (-(β * E i) / 2)) (fun i => Real.exp (-(β * E i) / 2))
  have hN : (∑ i, E i * Real.exp (-(β * E i) / 2) * Real.exp (-(β * E i) / 2)) = Nf E β := by
    rw [Nf]; exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, mul_half_exp]
  have sq_exp : ∀ i : ι, (Real.exp (-(β * E i) / 2)) ^ 2 = Real.exp (-β * E i) :=
    fun i => (pow_two _).trans (mul_half_exp E β i)
  have hS2 : (∑ i, (E i * Real.exp (-(β * E i) / 2)) ^ 2) = S2f E β := by
    rw [S2f]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, sq_exp i]
  have hZs : (∑ i, (Real.exp (-(β * E i) / 2)) ^ 2) = Zf E β := by
    rw [Zf]; exact Finset.sum_congr rfl fun i _ => sq_exp i
  rw [hN, hS2, hZs] at hcs
  -- `Var = (S2·Z - N²)/Z² ≥ 0`.
  have key : Varf E β = (S2f E β * Zf E β - (Nf E β) ^ 2) / (Zf E β) ^ 2 := by
    rw [Varf, Uf]; field_simp; try ring
  rw [key]
  apply div_nonneg
  · linarith [hcs]
  · positivity

omit [Nonempty ι] in
/-- The partition function's derivative: `Z'(β) = -∑ Eᵢ exp(-β Eᵢ) = -N(β)`. -/
theorem hasDerivAt_Zf (E : ι → ℝ) (β : ℝ) : HasDerivAt (Zf E) (- Nf E β) β := by
  have hZfun : Zf E = ∑ i, (fun b : ℝ => Real.exp (-b * E i)) := by
    funext b; simp only [Zf, Finset.sum_apply]
  have h : HasDerivAt (Zf E) (∑ i, Real.exp (-β * E i) * (-E i)) β := by
    rw [hZfun]; apply HasDerivAt.sum; intro i _
    have hlin : HasDerivAt (fun b : ℝ => -b * E i) (-E i) β := by
      simpa using (hasDerivAt_id β).neg.mul_const (E i)
    simpa using hlin.exp
  have heq : (∑ i, Real.exp (-β * E i) * (-E i)) = - Nf E β := by
    rw [eq_neg_iff_add_eq_zero, Nf, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  rw [heq] at h; exact h

omit [Nonempty ι] in
/-- The energy-sum's derivative: `N'(β) = -∑ Eᵢ² exp(-β Eᵢ) = -S2(β)`. -/
theorem hasDerivAt_Nf (E : ι → ℝ) (β : ℝ) : HasDerivAt (Nf E) (- S2f E β) β := by
  have hNfun : Nf E = ∑ i, (fun b : ℝ => E i * Real.exp (-b * E i)) := by
    funext b; simp only [Nf, Finset.sum_apply]
  have h : HasDerivAt (Nf E) (∑ i, E i * (Real.exp (-β * E i) * (-E i))) β := by
    rw [hNfun]; apply HasDerivAt.sum; intro i _
    have hlin : HasDerivAt (fun b : ℝ => -b * E i) (-E i) β := by
      simpa using (hasDerivAt_id β).neg.mul_const (E i)
    simpa using (hlin.exp).const_mul (E i)
  have heq : (∑ i, E i * (Real.exp (-β * E i) * (-E i))) = - S2f E β := by
    rw [eq_neg_iff_add_eq_zero, S2f, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  rw [heq] at h; exact h

/-- **Fluctuation-dissipation identity.** The mean energy's response to the coupling is minus the
variance: `dU/dβ = -Var(β)`. Hence the susceptibility `χ = -dU/dβ = Var(β)`. Pure quotient rule; no
physics input beyond the finite Gibbs weights. -/
theorem gibbs_susceptibility_eq_variance (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (Uf E) (- Varf E β) β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  have hd := (hasDerivAt_Nf E β).div (hasDerivAt_Zf E β) hZ
  have heq : ((- S2f E β) * Zf E β - Nf E β * (- Nf E β)) / (Zf E β) ^ 2 = - Varf E β := by
    rw [Varf, Uf]; field_simp; try ring
  rw [← heq]; exact hd

/-- **The susceptibility is nonnegative** (fluctuation-dissipation). `-dU/dβ = Var ≥ 0`: the mean energy
is nonincreasing in the coupling, the susceptibility is a variance, hence `≥ 0`. The archetype for a
nonnegative susceptibility; the disorder-susceptibility sign A1 needs is proved deterministically for the
entropy read in `Majorization.entropy_antitone`. -/
theorem gibbs_susceptibility_nonneg (E : ι → ℝ) (β : ℝ) : deriv (Uf E) β ≤ 0 := by
  rw [(gibbs_susceptibility_eq_variance E β).deriv]
  linarith [Varf_nonneg E β]

/-! ## The general fluctuation-dissipation identity (formula ★ of the handoff)

The response of the mean of ANY observable to the coupling is minus its covariance with the energy. The
variance result above is the special case `A = E`. Specializing instead to the entropy read `A = h` gives
exactly `χ_v = -dH/dβ = Cov(h, E)` (PAPER §8.4), the identity that turns the sole open input `χ_v ≥ 0`
into the covariance inequality `Cov(h, E) ≥ 0` (see `_scratch/CHI_V_NONNEGATIVITY_PROBLEM.md`). This
identity is proved here with **no axiom**; only the SIGN of the covariance remains open. -/

omit [Nonempty ι] in
/-- Derivative of a Gibbs-weighted sum: `d/dβ ∑ Aᵢ e^{-βEᵢ} = -∑ Aᵢ Eᵢ e^{-βEᵢ}`. -/
theorem hasDerivAt_weighted (E A : ι → ℝ) (β : ℝ) :
    HasDerivAt (fun b : ℝ => ∑ i, A i * Real.exp (-b * E i))
      (- ∑ i, A i * E i * Real.exp (-β * E i)) β := by
  have hfun : (fun b : ℝ => ∑ i, A i * Real.exp (-b * E i))
      = ∑ i, (fun b : ℝ => A i * Real.exp (-b * E i)) := by
    funext b; simp only [Finset.sum_apply]
  rw [hfun]
  have h : HasDerivAt (∑ i, (fun b : ℝ => A i * Real.exp (-b * E i)))
      (∑ i, A i * (Real.exp (-β * E i) * (-E i))) β := by
    apply HasDerivAt.sum; intro i _
    have hlin : HasDerivAt (fun b : ℝ => -b * E i) (-E i) β := by
      simpa using (hasDerivAt_id β).neg.mul_const (E i)
    simpa using (hlin.exp).const_mul (A i)
  have heq : (∑ i, A i * (Real.exp (-β * E i) * (-E i)))
      = - ∑ i, A i * E i * Real.exp (-β * E i) := by
    rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  rw [heq] at h; exact h

/-- Gibbs mean of an observable `A`: `⟨A⟩_β = (∑ Aᵢ e^{-βEᵢ}) / Z`. -/
noncomputable def meanf (E A : ι → ℝ) (β : ℝ) : ℝ := (∑ i, A i * Real.exp (-β * E i)) / Zf E β

/-- Gibbs covariance of an observable `A` with the energy `E`: `⟨AE⟩ - ⟨A⟩⟨E⟩`. -/
noncomputable def Covf (E A : ι → ℝ) (β : ℝ) : ℝ :=
  (∑ i, A i * E i * Real.exp (-β * E i)) / Zf E β - meanf E A β * meanf E E β

/-- **General fluctuation-dissipation identity.** The response of the mean of any observable `A` to the
coupling is minus its covariance with the energy: `d⟨A⟩/dβ = -Cov(A, E)`. With `A = E` the covariance is
the variance (recovering `gibbs_susceptibility_eq_variance`); with `A = h` the entropy read this is the
identity `χ_v = -dH/dβ = Cov(h, E)` that reframes `χ_v ≥ 0` as `Cov(h, E) ≥ 0`. No axiom. -/
theorem gibbs_mean_deriv_eq_neg_cov (E A : ι → ℝ) (β : ℝ) :
    HasDerivAt (meanf E A) (- Covf E A β) β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  have hd := (hasDerivAt_weighted E A β).div (hasDerivAt_Zf E β) hZ
  have heq : ((- ∑ i, A i * E i * Real.exp (-β * E i)) * Zf E β
      - (∑ i, A i * Real.exp (-β * E i)) * (- Nf E β)) / (Zf E β) ^ 2 = - Covf E A β := by
    simp only [Covf, meanf, Nf]
    generalize (∑ i, A i * E i * Real.exp (-β * E i)) = SAE
    generalize (∑ i, A i * Real.exp (-β * E i)) = SA
    generalize (∑ i, E i * Real.exp (-β * E i)) = SE
    field_simp
    ring
  rw [← heq]; exact hd

/-! ## Cauchy-Schwarz: the derivative bound `Interior.d2_le_of_analytic_grid` asks for

`gibbs_mean_deriv_eq_neg_cov` says the response IS a covariance. What consumes that fact is
`Interior.d2_le_of_analytic_grid`, whose hypothesis

    `hbnd : ∀ x ∈ Set.Icc a b, ‖deriv (d2 N) x‖ ≤ L`

names an `L` and proves nothing about it. This section derives one from the ensemble, in the two
steps the A1-uniform plan §5.1 names and leaves unformalized:

* `|Cov_β(A, E)| ≤ √(Var_β A · Var_β E)` — Cauchy-Schwarz for the Gibbs inner product
  (`abs_Covf_le_sqrt_mul_sqrt`), applied to the half-weights `exp(-βEᵢ/2)`, and
* `Var_β A ≤ (hi - lo)² / 4` — Popoviciu, from the observable's range alone
  (`VarObs_le_sq_range_div_four`).

Together: `‖d⟨A⟩/dβ‖ ≤ ¼ · range(A) · range(E)` at every `β` (`norm_deriv_meanf_le`), a CONSTANT, so
`hbnd`'s shape is met with the constant derived from two ranges rather than assumed
(`norm_deriv_meanf_le_on`), and `differentiableAt_meanf_on` meets the companion `hdiff`.

SCOPE, stated so it is not overread. This is the FINITE-SUM Gibbs family of this module: a `Fintype`
of microstates with weights `exp(-βEᵢ)`. `Interior.d2` is `Complete.d2At`, a read built from the
opaque `wilsonCorrAt`, and the Wilson ensemble's own Gibbs measure is an integral over a compact
group, not a finite sum — so these lemmas supply `hbnd`'s SHAPE and its CONSTANT, not an instance at
`d2At`. What still stands between is recorded at `norm_deriv_meanf_le_on`.
-/

/-- Gibbs variance of an arbitrary observable `A`: `⟨A²⟩_β - ⟨A⟩_β²`. The energy's own `Varf` is the
case `A = E` (`VarObs_self`).

DERIVED: the exponent `2` is the second moment and the square of the mean that define a variance;
the same `2` as `S2f`/`Varf`, and no other exponent yields one. -/
noncomputable def VarObs (E A : ι → ℝ) (β : ℝ) : ℝ :=
  (∑ i, (A i) ^ 2 * Real.exp (-β * E i)) / Zf E β - (meanf E A β) ^ 2

omit [Nonempty ι] in
/-- The mean energy is the Gibbs mean of the energy: `U = ⟨E⟩`. Definitional. -/
theorem Uf_eq_meanf (E : ι → ℝ) (β : ℝ) : Uf E β = meanf E E β := rfl

omit [Nonempty ι] in
/-- The general observable variance at `A = E` is the energy variance. Definitional. -/
theorem VarObs_self (E : ι → ℝ) (β : ℝ) : VarObs E E β = Varf E β := rfl

/-- An unnormalised weighted sum in terms of its mean: `∑ Aᵢ e^{-βEᵢ} = ⟨A⟩_β · Z(β)`. -/
theorem sum_weight_eq_meanf_mul_Zf (E A : ι → ℝ) (β : ℝ) :
    (∑ i, A i * Real.exp (-β * E i)) = meanf E A β * Zf E β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  rw [meanf, div_mul_cancel₀ _ hZ]

/-- **The centring identity.** `∑ (Aᵢ-⟨A⟩)(Bᵢ-⟨B⟩) e^{-βEᵢ} = ∑ AᵢBᵢ e^{-βEᵢ} - ⟨A⟩⟨B⟩·Z`: the
weighted product sum about the means is the raw one minus the product of the means. -/
theorem sum_centred (E A B : ι → ℝ) (β : ℝ) :
    (∑ i, (A i - meanf E A β) * (B i - meanf E B β) * Real.exp (-β * E i))
      = (∑ i, A i * B i * Real.exp (-β * E i)) - meanf E A β * meanf E B β * Zf E β := by
  have hA := sum_weight_eq_meanf_mul_Zf E A β
  have hB := sum_weight_eq_meanf_mul_Zf E B β
  have hZ : (∑ i, Real.exp (-β * E i)) = Zf E β := rfl
  have hexp : ∀ i : ι, (A i - meanf E A β) * (B i - meanf E B β) * Real.exp (-β * E i)
      = A i * B i * Real.exp (-β * E i)
        + (-(meanf E B β)) * (A i * Real.exp (-β * E i))
        + (-(meanf E A β)) * (B i * Real.exp (-β * E i))
        + (meanf E A β * meanf E B β) * Real.exp (-β * E i) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hA, hB, hZ]
  ring

/-- The centred second moment is `Z · Var`: `∑ (Aᵢ-⟨A⟩)² e^{-βEᵢ} = Z(β)·Var_β(A)`. -/
theorem sum_centred_sq (E A : ι → ℝ) (β : ℝ) :
    (∑ i, (A i - meanf E A β) ^ 2 * Real.exp (-β * E i)) = Zf E β * VarObs E A β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  have hsq : (∑ i, (A i - meanf E A β) ^ 2 * Real.exp (-β * E i))
      = ∑ i, (A i - meanf E A β) * (A i - meanf E A β) * Real.exp (-β * E i) :=
    Finset.sum_congr rfl fun i _ => by ring
  have hraw : (∑ i, A i * A i * Real.exp (-β * E i))
      = ∑ i, (A i) ^ 2 * Real.exp (-β * E i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsq, sum_centred E A A β, hraw, VarObs]
  field_simp

/-- The centred cross moment against the energy is `Z · Cov`. -/
theorem sum_centred_cov (E A : ι → ℝ) (β : ℝ) :
    (∑ i, (A i - meanf E A β) * (E i - meanf E E β) * Real.exp (-β * E i))
      = Zf E β * Covf E A β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  rw [sum_centred E A E β, Covf]
  generalize (∑ i, A i * E i * Real.exp (-β * E i)) = S
  field_simp

/-- **Every observable variance is nonnegative** — it is a weighted sum of squares over `Z > 0`. -/
theorem VarObs_nonneg (E A : ι → ℝ) (β : ℝ) : 0 ≤ VarObs E A β := by
  have hZ : 0 < Zf E β := Zf_pos E β
  have hs : 0 ≤ ∑ i, (A i - meanf E A β) ^ 2 * Real.exp (-β * E i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [sum_centred_sq E A β] at hs
  by_contra hneg
  exact absurd hs (not_le.mpr (mul_neg_of_pos_of_neg hZ (not_le.mp hneg)))

/-- **Cauchy-Schwarz for the Gibbs covariance.** `|Cov_β(A, E)| ≤ √(Var_β A) · √(Var_β E)`.

This is the inequality the A1-uniform plan §5.1 names as the route to the interior's Lipschitz
constant and leaves unformalized. The proof is Cauchy-Schwarz on the half-weights `exp(-βEᵢ/2)`: the
centred sums `∑ (Aᵢ-⟨A⟩)(Eᵢ-⟨E⟩)e^{-βEᵢ}`, `∑ (Aᵢ-⟨A⟩)²e^{-βEᵢ}` and `∑ (Eᵢ-⟨E⟩)²e^{-βEᵢ}` are
`Z·Cov`, `Z·Var A` and `Z·Var E`, so the common `Z²` divides out. No axiom, no hypothesis. -/
theorem abs_Covf_le_sqrt_mul_sqrt (E A : ι → ℝ) (β : ℝ) :
    |Covf E A β| ≤ Real.sqrt (VarObs E A β) * Real.sqrt (Varf E β) := by
  have hZ : 0 < Zf E β := Zf_pos E β
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => (A i - meanf E A β) * Real.exp (-(β * E i) / 2))
    (fun i => (E i - meanf E E β) * Real.exp (-(β * E i) / 2))
  have h1 : (∑ i, (A i - meanf E A β) * Real.exp (-(β * E i) / 2)
        * ((E i - meanf E E β) * Real.exp (-(β * E i) / 2)))
      = Zf E β * Covf E A β := by
    rw [← sum_centred_cov E A β]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (A i - meanf E A β) * Real.exp (-(β * E i) / 2)
          * ((E i - meanf E E β) * Real.exp (-(β * E i) / 2))
        = (A i - meanf E A β) * (E i - meanf E E β)
          * (Real.exp (-(β * E i) / 2) * Real.exp (-(β * E i) / 2)) from by ring,
      mul_half_exp]
  have h2 : (∑ i, ((A i - meanf E A β) * Real.exp (-(β * E i) / 2)) ^ 2)
      = Zf E β * VarObs E A β := by
    rw [← sum_centred_sq E A β]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mul_pow, pow_two (Real.exp (-(β * E i) / 2)), mul_half_exp]
  have h3 : (∑ i, ((E i - meanf E E β) * Real.exp (-(β * E i) / 2)) ^ 2)
      = Zf E β * Varf E β := by
    rw [← VarObs_self E β, ← sum_centred_sq E E β]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mul_pow, pow_two (Real.exp (-(β * E i) / 2)), mul_half_exp]
  rw [h1, h2, h3] at hcs
  have hZ2 : (0 : ℝ) < Zf E β ^ 2 := by positivity
  have hh : Zf E β ^ 2 * (Covf E A β) ^ 2 ≤ Zf E β ^ 2 * (VarObs E A β * Varf E β) := by
    have e1 : Zf E β ^ 2 * (Covf E A β) ^ 2 = (Zf E β * Covf E A β) ^ 2 := by ring
    have e2 : Zf E β ^ 2 * (VarObs E A β * Varf E β)
        = (Zf E β * VarObs E A β) * (Zf E β * Varf E β) := by ring
    rw [e1, e2]; exact hcs
  have hkey : (Covf E A β) ^ 2 ≤ VarObs E A β * Varf E β := le_of_mul_le_mul_left hh hZ2
  calc |Covf E A β| = Real.sqrt ((Covf E A β) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (VarObs E A β * Varf E β) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt (VarObs E A β) * Real.sqrt (Varf E β) :=
        Real.sqrt_mul (VarObs_nonneg E A β) _

/-- A Gibbs mean never leaves the observable's range, above. -/
theorem meanf_le (E A : ι → ℝ) (β : ℝ) {hi : ℝ} (h : ∀ i, A i ≤ hi) : meanf E A β ≤ hi := by
  have hZ : 0 < Zf E β := Zf_pos E β
  rw [meanf, div_le_iff₀ hZ]
  calc (∑ i, A i * Real.exp (-β * E i)) ≤ ∑ i, hi * Real.exp (-β * E i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (Real.exp_pos _).le
    _ = hi * Zf E β := by rw [← Finset.mul_sum]; rfl

/-- A Gibbs mean never leaves the observable's range, below. -/
theorem le_meanf (E A : ι → ℝ) (β : ℝ) {lo : ℝ} (h : ∀ i, lo ≤ A i) : lo ≤ meanf E A β := by
  have hZ : 0 < Zf E β := Zf_pos E β
  rw [meanf, le_div_iff₀ hZ]
  calc lo * Zf E β = ∑ i, lo * Real.exp (-β * E i) := by rw [← Finset.mul_sum]; rfl
    _ ≤ ∑ i, A i * Real.exp (-β * E i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (Real.exp_pos _).le

/-- **Popoviciu's inequality for the Gibbs variance.** An observable confined to `[lo, hi]` has
`Var_β(A) ≤ (hi - lo)²/4`, at every `β`. Pointwise `(hi - Aᵢ)(Aᵢ - lo) ≥ 0` gives
`⟨A²⟩ ≤ (hi+lo)⟨A⟩ - hi·lo`, so `Var ≤ (hi - ⟨A⟩)(⟨A⟩ - lo)`, and AM-GM on that product caps it at a
quarter of the squared range. The `4` is the AM-GM constant, not a choice. -/
theorem VarObs_le_sq_range_div_four (E A : ι → ℝ) (β : ℝ) {lo hi : ℝ}
    (hlo : ∀ i, lo ≤ A i) (hhi : ∀ i, A i ≤ hi) :
    VarObs E A β ≤ (hi - lo) ^ 2 / 4 := by
  have hZ : 0 < Zf E β := Zf_pos E β
  have hnum : (∑ i, (A i) ^ 2 * Real.exp (-β * E i))
      ≤ ((hi + lo) * meanf E A β - hi * lo) * Zf E β := by
    have hstep : ∀ i ∈ (Finset.univ : Finset ι),
        (A i) ^ 2 * Real.exp (-β * E i)
          ≤ ((hi + lo) * A i - hi * lo) * Real.exp (-β * E i) := by
      intro i _
      have hp : 0 ≤ (hi - A i) * (A i - lo) :=
        mul_nonneg (by linarith [hhi i]) (by linarith [hlo i])
      exact mul_le_mul_of_nonneg_right (by nlinarith [hp]) (Real.exp_pos _).le
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsplit : (∑ i, ((hi + lo) * A i - hi * lo) * Real.exp (-β * E i))
        = (hi + lo) * (∑ i, A i * Real.exp (-β * E i))
          - (hi * lo) * (∑ i, Real.exp (-β * E i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hzz : (∑ i, Real.exp (-β * E i)) = Zf E β := rfl
    rw [hsplit, sum_weight_eq_meanf_mul_Zf E A β, hzz]
    exact le_of_eq (by ring)
  have hq : (∑ i, (A i) ^ 2 * Real.exp (-β * E i)) / Zf E β
      ≤ (hi + lo) * meanf E A β - hi * lo := by rw [div_le_iff₀ hZ]; exact hnum
  have hstep2 : VarObs E A β ≤ (hi + lo) * meanf E A β - hi * lo - (meanf E A β) ^ 2 := by
    rw [VarObs]; linarith
  nlinarith [hstep2, sq_nonneg (hi + lo - 2 * meanf E A β)]

/-- **A Gibbs mean is differentiable in the coupling, everywhere.** Immediate from
`gibbs_mean_deriv_eq_neg_cov`; this is the shape of `Interior.d2_le_of_analytic_grid`'s `hdiff`. -/
theorem differentiableAt_meanf (E A : ι → ℝ) (β : ℝ) : DifferentiableAt ℝ (meanf E A) β :=
  (gibbs_mean_deriv_eq_neg_cov E A β).differentiableAt

/-- **THE DERIVATIVE BOUND, DERIVED FROM TWO RANGES.** If `A` takes values in `[loA, hiA]` and the
energy in `[loE, hiE]`, then at every coupling

    `‖d⟨A⟩_β/dβ‖ ≤ ¼ · (hiA - loA) · (hiE - loE)` .

Identity (`gibbs_mean_deriv_eq_neg_cov`) + Cauchy-Schwarz (`abs_Covf_le_sqrt_mul_sqrt`) + Popoviciu
(`VarObs_le_sq_range_div_four`), each proved here. Nothing is measured and nothing is assumed: the
constant is a product of the two ranges the caller already knows. -/
theorem norm_deriv_meanf_le (E A : ι → ℝ) {loA hiA loE hiE : ℝ}
    (hAlo : ∀ i, loA ≤ A i) (hAhi : ∀ i, A i ≤ hiA)
    (hElo : ∀ i, loE ≤ E i) (hEhi : ∀ i, E i ≤ hiE) (β : ℝ) :
    ‖deriv (meanf E A) β‖ ≤ (hiA - loA) * (hiE - loE) / 4 := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  have hrA : (0 : ℝ) ≤ hiA - loA := by linarith [hAlo i0, hAhi i0]
  have hrE : (0 : ℝ) ≤ hiE - loE := by linarith [hElo i0, hEhi i0]
  rw [(gibbs_mean_deriv_eq_neg_cov E A β).deriv, Real.norm_eq_abs, abs_neg]
  have hA : VarObs E A β ≤ (hiA - loA) ^ 2 / 4 := VarObs_le_sq_range_div_four E A β hAlo hAhi
  have hE : Varf E β ≤ (hiE - loE) ^ 2 / 4 := by
    rw [← VarObs_self E β]; exact VarObs_le_sq_range_div_four E E β hElo hEhi
  have s1 : Real.sqrt (VarObs E A β) ≤ (hiA - loA) / 2 := by
    rw [show (hiA - loA) / 2 = Real.sqrt (((hiA - loA) / 2) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hA])
  have s2 : Real.sqrt (Varf E β) ≤ (hiE - loE) / 2 := by
    rw [show (hiE - loE) / 2 = Real.sqrt (((hiE - loE) / 2) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hE])
  calc |Covf E A β| ≤ Real.sqrt (VarObs E A β) * Real.sqrt (Varf E β) :=
        abs_Covf_le_sqrt_mul_sqrt E A β
    _ ≤ ((hiA - loA) / 2) * ((hiE - loE) / 2) :=
        mul_le_mul s1 s2 (Real.sqrt_nonneg _) (by linarith)
    _ = (hiA - loA) * (hiE - loE) / 4 := by ring

/-- **`hdiff`, in `Interior`'s shape.** -/
theorem differentiableAt_meanf_on (E A : ι → ℝ) (a b : ℝ) :
    ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (meanf E A) x :=
  fun x _ => differentiableAt_meanf E A x

/-- **`hbnd`, in `Interior`'s shape, with the constant derived.**
`Interior.d2_le_of_analytic_grid` asks for `∀ x ∈ Set.Icc a b, ‖deriv f x‖ ≤ L` and supplies no `L`.
For a Gibbs mean this is that statement with `L = ¼·range(A)·range(E)`, a theorem.

WHAT THIS DOES NOT DO, so the wiring is not overread. `Interior.d2` is `Complete.d2At`, which is not
a Gibbs mean of this module's form: it is `∑_d p_d(β)·circLag(d)²` over the read built from the
opaque `wilsonCorrAt`, whose β-dependence no theorem in the tree relates to a finite Gibbs weight.
The genuine Wilson ensemble's own version of the identity lives in `WilsonAnalytic`
(`expect_hasDerivAt`), over a Haar INTEGRAL rather than a finite sum, so transporting these two
steps there is a restatement in the integral setting, not a corollary of what is proved here.
And the constant it would yield is `¼·range(O)·range(S)` with `range(S) = 2·#Plaq`: Cauchy-Schwarz
sharpens `WilsonAnalytic.cov_bound_extensive`'s `O(V)` to `O(√V)` only if `Var_β S` is bounded by the
susceptibility rather than by Popoviciu, and by Popoviciu alone it is `O(V)` again. So this closes
`hbnd` at FIXED volume with a derived rather than assumed constant; the volume-uniformity that
`Complete.confinement_of_bounded_substrate` needs (one `B` at every aperture) is untouched, and
remains clustering. -/
theorem norm_deriv_meanf_le_on (E A : ι → ℝ) {loA hiA loE hiE : ℝ}
    (hAlo : ∀ i, loA ≤ A i) (hAhi : ∀ i, A i ≤ hiA)
    (hElo : ∀ i, loE ≤ E i) (hEhi : ∀ i, E i ≤ hiE) (a b : ℝ) :
    ∀ x ∈ Set.Icc a b, ‖deriv (meanf E A) x‖ ≤ (hiA - loA) * (hiE - loE) / 4 :=
  fun x _ => norm_deriv_meanf_le E A hAlo hAhi hElo hEhi x

/-- **The Lipschitz statement itself**, in the shape `MassGap.le_of_lipschitz_grid` consumes as
`hlip` — the same shape `Interior.d2_lipschitz_of_deriv_bound` produces from an ASSUMED derivative
bound, here produced from the observable's range instead. Mean value on `norm_deriv_meanf_le_on`. -/
theorem meanf_lipschitz (E A : ι → ℝ) {loA hiA loE hiE : ℝ}
    (hAlo : ∀ i, loA ≤ A i) (hAhi : ∀ i, A i ≤ hiA)
    (hElo : ∀ i, loE ≤ E i) (hEhi : ∀ i, E i ≤ hiE) (a b : ℝ) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |meanf E A x - meanf E A y| ≤ ((hiA - loA) * (hiE - loE) / 4) * |x - y| := by
  intro x hx y hy
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (differentiableAt_meanf_on E A a b)
    (norm_deriv_meanf_le_on E A hAlo hAhi hElo hEhi a b) hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |meanf E A x - meanf E A y| = |meanf E A y - meanf E A x| := abs_sub_comm _ _
    _ ≤ ((hiA - loA) * (hiE - loE) / 4) * |y - x| := h
    _ = ((hiA - loA) * (hiE - loE) / 4) * |x - y| := by rw [abs_sub_comm y x]

#print axioms Varf_nonneg
#print axioms hasDerivAt_Zf
#print axioms gibbs_susceptibility_eq_variance
#print axioms gibbs_susceptibility_nonneg
#print axioms gibbs_mean_deriv_eq_neg_cov
#print axioms abs_Covf_le_sqrt_mul_sqrt
#print axioms VarObs_le_sq_range_div_four
#print axioms norm_deriv_meanf_le
#print axioms norm_deriv_meanf_le_on
#print axioms meanf_lipschitz

end MassGap.Fluctuation
