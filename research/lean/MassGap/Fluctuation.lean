import Mathlib

/-!
# MassGap.Fluctuation — derivatives of finite Gibbs means in the coupling

A finite Gibbs family over a nonempty `Fintype ι`: energies `E : ι → ℝ`, weights `exp (-β * E i)`,
partition function `Zf`, mean `meanf`, variance `VarObs`, covariance with the energy `Covf`.

The identities proved here:

* `gibbs_mean_deriv_eq_neg_cov` — `d⟨A⟩/dβ = -Cov(A, E)`, for any observable `A`, by the quotient
  rule on `hasDerivAt_weighted` and `hasDerivAt_Zf`.
* `gibbs_susceptibility_eq_variance` — the case `A = E`: `dU/dβ = -Var(E)`.
* `Varf_nonneg`, `VarObs_nonneg` — variances are nonnegative, by Cauchy–Schwarz on the half-weights
  and by `sum_centred_sq` respectively; `gibbs_susceptibility_nonneg` is the consequence
  `deriv (Uf E) β ≤ 0`.
* `abs_Covf_le_sqrt_mul_sqrt` — `|Cov(A, E)| ≤ √(Var A) · √(Var E)`, Cauchy–Schwarz on the
  half-weights `exp(-βEᵢ/2)`, using the centring identities `sum_centred`, `sum_centred_sq`,
  `sum_centred_cov`.
* `VarObs_le_sq_range_div_four` — Popoviciu: an observable confined to `[lo, hi]` has variance at
  most `(hi − lo)²/4`.
* `norm_deriv_meanf_le`, `norm_deriv_meanf_le_on`, `meanf_lipschitz` — combining the three,
  `‖d⟨A⟩/dβ‖ ≤ ¼ · range(A) · range(E)` at every `β`, and the mean-value Lipschitz bound that
  follows. `differentiableAt_meanf` and `differentiableAt_meanf_on` are the differentiability.

## Scope

The family is a finite sum over a `Fintype` with weights `exp (-β * E i)`. Nothing here is stated for
a measure-theoretic Gibbs state, and no statement mentions a lattice, a gauge group or a correlation
function; `E` and `A` are arbitrary real functions on `ι` and `β` is an arbitrary real.

Consequently the derivative bound is at fixed `ι`: the constant `¼ · range(A) · range(E)` depends on
the two ranges, and nothing here bounds it uniformly over a family of index types.
-/

namespace MassGap.Fluctuation

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The partition function `Z(β) = ∑ᵢ exp(-β Eᵢ)`, a finite sum over the `Fintype ι`. Strictly
positive by `Zf_pos`, since each summand is.

DERIVED: no numeral. `E` and `β` are the caller's. -/
noncomputable def Zf (E : ι → ℝ) (β : ℝ) : ℝ := ∑ i, Real.exp (-β * E i)
/-- The Gibbs-weighted energy sum `∑ᵢ Eᵢ exp(-β Eᵢ)`, the unnormalised numerator of `Uf`.

DERIVED: no numeral. -/
noncomputable def Nf (E : ι → ℝ) (β : ℝ) : ℝ := ∑ i, E i * Real.exp (-β * E i)
/-- The Gibbs-weighted squared-energy sum `∑ᵢ Eᵢ² exp(-β Eᵢ)`, the unnormalised second moment.

DERIVED: the exponent `2` is the order of the moment — the quantity a variance subtracts the squared
mean from. Nothing selects it; it is what `Var = ⟨E²⟩ − ⟨E⟩²` requires. -/
noncomputable def S2f (E : ι → ℝ) (β : ℝ) : ℝ := ∑ i, (E i) ^ 2 * Real.exp (-β * E i)
/-- The mean energy `U(β) = Nf E β / Zf E β`. Well behaved everywhere, since `Zf` is positive.

DERIVED: no numeral. -/
noncomputable def Uf (E : ι → ℝ) (β : ℝ) : ℝ := Nf E β / Zf E β
/-- The energy variance `S2f/Zf − Uf²`, the second moment minus the squared mean.

DERIVED: the exponent `2` squares the mean that the definition of a variance subtracts; it matches
`S2f`'s moment order by construction, and no other exponent yields a variance. -/
noncomputable def Varf (E : ι → ℝ) (β : ℝ) : ℝ := S2f E β / Zf E β - (Uf E β) ^ 2

/-- `0 < Zf E β`, at every `E` and `β`. Each summand `exp (-β * E i)` is positive and `ι` is
nonempty, so `Finset.sum_pos` applies.

`[Nonempty ι]` is required: an empty index type gives an empty sum, which is `0`.

DERIVED: `0` is the strict lower bound asserted; it is the only numeral. -/
theorem Zf_pos (E : ι → ℝ) (β : ℝ) : 0 < Zf E β :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype ι] [Nonempty ι] in
/-- `exp(-(β Eᵢ)/2) · exp(-(β Eᵢ)/2) = exp(-β Eᵢ)`. `Real.exp_add` and `ring`.

The identity that lets a Gibbs weight be split evenly between the two factors of a Cauchy–Schwarz
pairing; used in `Varf_nonneg` and `abs_Covf_le_sqrt_mul_sqrt`.

DERIVED: `2` halves the exponent, because the weight is split between exactly two factors; it is
Cauchy–Schwarz's pairing of two sequences, not a chosen exponent. -/
private theorem mul_half_exp (E : ι → ℝ) (β : ℝ) (i : ι) :
    Real.exp (-(β * E i) / 2) * Real.exp (-(β * E i) / 2) = Real.exp (-β * E i) := by
  rw [← Real.exp_add]; congr 1; ring

/-- `0 ≤ Varf E β`, at every `E` and `β`. `Finset.sum_mul_sq_le_sq_mul_sq` at the half-weights
`exp(-(β Eᵢ)/2)` gives `Nf² ≤ S2f · Zf`; rewriting `Varf` as `(S2f·Zf − Nf²)/Zf²` makes the
conclusion a quotient of nonnegatives.

DERIVED: `0` is the lower bound asserted; it is the only numeral in the statement. The halving and
the squares belong to the proof's Cauchy–Schwarz step and to `Varf`'s own definition. -/
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
/-- `HasDerivAt (Zf E) (-Nf E β) β`: the partition function's derivative in the coupling is minus the
weighted energy sum. Termwise by `HasDerivAt.sum`, each term the chain rule on `exp` composed with
`b ↦ -b * E i`.

`[Nonempty ι]` is not needed and is omitted; the identity holds for an empty index type too, where
both sides are `0`.

DERIVED: no numeral. -/
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
/-- `HasDerivAt (Nf E) (-S2f E β) β`: differentiating the weighted energy sum brings down a second
factor of the energy. Same termwise argument as `hasDerivAt_Zf`, with the extra constant factor
`E i`.

`[Nonempty ι]` is omitted here as well.

DERIVED: no numeral. -/
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

/-- `HasDerivAt (Uf E) (-Varf E β) β`: the mean energy's derivative in the coupling is minus the
energy variance. The quotient rule on `hasDerivAt_Nf` and `hasDerivAt_Zf`, with `Zf_pos` supplying the
nonvanishing denominator, followed by a `field_simp`/`ring` identification of the result with
`-Varf`.

A derivative at every real `β`, with no restriction on the energies.

DERIVED: no numeral. `E` and `β` are the caller's; the square in `Varf` is that definition's. -/
theorem gibbs_susceptibility_eq_variance (E : ι → ℝ) (β : ℝ) :
    HasDerivAt (Uf E) (- Varf E β) β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  have hd := (hasDerivAt_Nf E β).div (hasDerivAt_Zf E β) hZ
  have heq : ((- S2f E β) * Zf E β - Nf E β * (- Nf E β)) / (Zf E β) ^ 2 = - Varf E β := by
    rw [Varf, Uf]; field_simp; try ring
  rw [← heq]; exact hd

/-- `deriv (Uf E) β ≤ 0`, at every `E` and `β`: the mean energy is nonincreasing in the coupling.
`gibbs_susceptibility_eq_variance` identifies the derivative as `-Varf`, and `Varf_nonneg` gives its
sign.

A pointwise statement about the derivative; monotonicity of `Uf` itself is not stated.

DERIVED: `0` is the upper bound asserted of the derivative; it is the only numeral. -/
theorem gibbs_susceptibility_nonneg (E : ι → ℝ) (β : ℝ) : deriv (Uf E) β ≤ 0 := by
  rw [(gibbs_susceptibility_eq_variance E β).deriv]
  linarith [Varf_nonneg E β]

/-! ## The identity for an arbitrary observable

The derivative of the mean of any observable `A` in the coupling is minus its covariance with the
energy. `gibbs_susceptibility_eq_variance` is the case `A = E`, where the covariance is the variance.
The sign of the covariance is not determined for a general `A`: `VarObs_nonneg` applies only to the
variance, and `Covf` can take either sign. -/

omit [Nonempty ι] in
/-- `HasDerivAt (fun b => ∑ᵢ Aᵢ exp(-b Eᵢ)) (-∑ᵢ Aᵢ Eᵢ exp(-β Eᵢ)) β`: differentiating a
Gibbs-weighted sum brings down a factor of the energy. `hasDerivAt_Nf` with `A` in place of `E` in
the weight position.

DERIVED: no numeral. -/
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

/-- The Gibbs mean `(∑ᵢ Aᵢ exp(-β Eᵢ)) / Zf E β` of an observable `A`. `Uf` is the case `A = E`
(`Uf_eq_meanf`, definitional).

DERIVED: no numeral. -/
noncomputable def meanf (E A : ι → ℝ) (β : ℝ) : ℝ := (∑ i, A i * Real.exp (-β * E i)) / Zf E β

/-- The Gibbs covariance of `A` with the energy: `⟨AE⟩ − ⟨A⟩⟨E⟩`, written with the first term as an
explicit weighted sum over `Zf`.

Not assumed to have any sign. `Varf` is the case `A = E`, and only there is nonnegativity available.

DERIVED: no numeral. -/
noncomputable def Covf (E A : ι → ℝ) (β : ℝ) : ℝ :=
  (∑ i, A i * E i * Real.exp (-β * E i)) / Zf E β - meanf E A β * meanf E E β

/-- `HasDerivAt (meanf E A) (-Covf E A β) β`, for any observable `A`: the derivative of the Gibbs
mean in the coupling is minus its covariance with the energy. The quotient rule on
`hasDerivAt_weighted` and `hasDerivAt_Zf`, with the three sums generalised away before `field_simp`
identifies the result with `-Covf`.

At `A = E` this is `gibbs_susceptibility_eq_variance`. For a general `A` the statement determines the
derivative but not its sign, since `Covf` may be of either sign.

DERIVED: no numeral. `E`, `A` and `β` are the caller's. -/
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

/-! ## A derivative bound from the observables' ranges

Two inequalities turn `gibbs_mean_deriv_eq_neg_cov` into a numeric bound on the derivative:

* `abs_Covf_le_sqrt_mul_sqrt` — `|Cov_β(A, E)| ≤ √(Var_β A) · √(Var_β E)`, Cauchy–Schwarz on the
  half-weights `exp(-βEᵢ/2)`, and
* `VarObs_le_sq_range_div_four` — `Var_β A ≤ (hi − lo)²/4`, Popoviciu, from the observable's range
  alone.

Together they give `‖d⟨A⟩/dβ‖ ≤ ¼ · range(A) · range(E)` at every `β` (`norm_deriv_meanf_le`), a
constant depending only on the two ranges. `norm_deriv_meanf_le_on` and `differentiableAt_meanf_on`
state that bound and the differentiability on an interval, and `meanf_lipschitz` is the mean-value
consequence.

The family is the finite-sum one of this module: a `Fintype` of indices with weights
`exp (-β * E i)`. Nothing here is stated for a Gibbs state given by an integral against a measure,
and no statement relates these means to `wilsonCorrAt` or to any lattice quantity. -/

/-- The Gibbs variance of an arbitrary observable `A`: `⟨A²⟩_β − ⟨A⟩_β²`. The energy's `Varf` is the
case `A = E`, definitionally (`VarObs_self`).

DERIVED: the exponent `2` is the moment order and the square of the mean that together define a
variance — the same `2` as in `S2f` and `Varf`, and no other exponent yields one. -/
noncomputable def VarObs (E A : ι → ℝ) (β : ℝ) : ℝ :=
  (∑ i, (A i) ^ 2 * Real.exp (-β * E i)) / Zf E β - (meanf E A β) ^ 2

omit [Nonempty ι] in
/-- `Uf E β = meanf E E β`, by `rfl`: the mean energy is the Gibbs mean of the energy itself.

DERIVED: no numeral. -/
theorem Uf_eq_meanf (E : ι → ℝ) (β : ℝ) : Uf E β = meanf E E β := rfl

omit [Nonempty ι] in
/-- `VarObs E E β = Varf E β`, by `rfl`: the general observable variance at `A = E` is the energy
variance.

DERIVED: no numeral. -/
theorem VarObs_self (E : ι → ℝ) (β : ℝ) : VarObs E E β = Varf E β := rfl

/-- `∑ᵢ Aᵢ exp(-β Eᵢ) = meanf E A β * Zf E β`: the unnormalised weighted sum recovered from its
mean. `div_mul_cancel₀` against the nonzero `Zf`.

DERIVED: no numeral. -/
theorem sum_weight_eq_meanf_mul_Zf (E A : ι → ℝ) (β : ℝ) :
    (∑ i, A i * Real.exp (-β * E i)) = meanf E A β * Zf E β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  rw [meanf, div_mul_cancel₀ _ hZ]

/-- `∑ᵢ (Aᵢ − ⟨A⟩)(Bᵢ − ⟨B⟩) exp(-β Eᵢ) = ∑ᵢ AᵢBᵢ exp(-β Eᵢ) − ⟨A⟩⟨B⟩ · Zf E β`: expanding the
product about the means leaves the raw weighted sum minus the product of the means times the total
weight. Expand pointwise, split the sum, and apply `sum_weight_eq_meanf_mul_Zf` to each cross term.

Stated for two arbitrary observables `A` and `B`; `sum_centred_sq` and `sum_centred_cov` are the
cases `B = A` and `B = E`.

DERIVED: no numeral. -/
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

/-- `∑ᵢ (Aᵢ − ⟨A⟩)² exp(-β Eᵢ) = Zf E β * VarObs E A β`: the centred second moment is the total
weight times the variance. `sum_centred` at `B = A`, then `field_simp` against the definition of
`VarObs`.

DERIVED: the exponent `2` is the square of the centred observable, matching `VarObs`'s moment
order. -/
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

/-- `∑ᵢ (Aᵢ − ⟨A⟩)(Eᵢ − ⟨E⟩) exp(-β Eᵢ) = Zf E β * Covf E A β`: the centred cross moment against the
energy is the total weight times the covariance. `sum_centred` at `B = E`, then `field_simp`.

DERIVED: no numeral. -/
theorem sum_centred_cov (E A : ι → ℝ) (β : ℝ) :
    (∑ i, (A i - meanf E A β) * (E i - meanf E E β) * Real.exp (-β * E i))
      = Zf E β * Covf E A β := by
  have hZ : Zf E β ≠ 0 := ne_of_gt (Zf_pos E β)
  rw [sum_centred E A E β, Covf]
  generalize (∑ i, A i * E i * Real.exp (-β * E i)) = S
  field_simp

/-- `0 ≤ VarObs E A β`, for every observable `A`. By `sum_centred_sq` the variance times the positive
`Zf` equals a sum of nonnegative terms, so it cannot be negative.

Holds for every `A`; `Covf` has no such property, which is why the Cauchy–Schwarz bound below is
stated on `|Covf|`.

DERIVED: `0` is the lower bound asserted; it is the only numeral. -/
theorem VarObs_nonneg (E A : ι → ℝ) (β : ℝ) : 0 ≤ VarObs E A β := by
  have hZ : 0 < Zf E β := Zf_pos E β
  have hs : 0 ≤ ∑ i, (A i - meanf E A β) ^ 2 * Real.exp (-β * E i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [sum_centred_sq E A β] at hs
  by_contra hneg
  exact absurd hs (not_le.mpr (mul_neg_of_pos_of_neg hZ (not_le.mp hneg)))

/-- `|Covf E A β| ≤ √(VarObs E A β) * √(Varf E β)`, at every `A` and `β`.

Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) applied to the centred observables against the
half-weights `exp(-(β Eᵢ)/2)`. The three resulting sums are `Zf·Covf`, `Zf·VarObs` and `Zf·Varf` by
`sum_centred_cov` and `sum_centred_sq`, so the common factor `Zf²` cancels by
`le_of_mul_le_mul_left`; `Real.sqrt_sq_eq_abs` and `Real.sqrt_mul` finish, the latter needing
`VarObs_nonneg`.

No hypothesis beyond the instances: `A`, `E` and `β` are arbitrary.

DERIVED: no numeral in the statement. The half-weights and the squares belong to the proof's
Cauchy–Schwarz step, and the square roots are taken of `VarObs` and `Varf`, both of which carry
their own definitions' exponents. -/
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

/-- If `A i ≤ hi` at every `i`, then `meanf E A β ≤ hi`. Bound the weighted sum termwise by
`hi * exp(-β Eᵢ)`, whose sum is `hi * Zf`, then divide by the positive `Zf`.

DERIVED: no numeral. `hi` is the caller's bound. -/
theorem meanf_le (E A : ι → ℝ) (β : ℝ) {hi : ℝ} (h : ∀ i, A i ≤ hi) : meanf E A β ≤ hi := by
  have hZ : 0 < Zf E β := Zf_pos E β
  rw [meanf, div_le_iff₀ hZ]
  calc (∑ i, A i * Real.exp (-β * E i)) ≤ ∑ i, hi * Real.exp (-β * E i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (Real.exp_pos _).le
    _ = hi * Zf E β := by rw [← Finset.mul_sum]; rfl

/-- If `lo ≤ A i` at every `i`, then `lo ≤ meanf E A β`. The mirror of `meanf_le`, bounding the
weighted sum below termwise.

DERIVED: no numeral. `lo` is the caller's bound. -/
theorem le_meanf (E A : ι → ℝ) (β : ℝ) {lo : ℝ} (h : ∀ i, lo ≤ A i) : lo ≤ meanf E A β := by
  have hZ : 0 < Zf E β := Zf_pos E β
  rw [meanf, le_div_iff₀ hZ]
  calc lo * Zf E β = ∑ i, lo * Real.exp (-β * E i) := by rw [← Finset.mul_sum]; rfl
    _ ≤ ∑ i, A i * Real.exp (-β * E i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (Real.exp_pos _).le

/-- Popoviciu's inequality: an observable with `lo ≤ A i ≤ hi` at every `i` has
`VarObs E A β ≤ (hi − lo)² / 4`, at every `β`.

Pointwise `(hi − Aᵢ)(Aᵢ − lo) ≥ 0` gives `Aᵢ² ≤ (hi + lo)Aᵢ − hi·lo`; summing against the weights and
dividing by `Zf` gives `⟨A²⟩ ≤ (hi + lo)⟨A⟩ − hi·lo`, so `VarObs ≤ (hi − ⟨A⟩)(⟨A⟩ − lo)`, and
`nlinarith` against `(hi + lo − 2⟨A⟩)² ≥ 0` caps that product.

The bound depends on the range alone, not on `E`, `β` or the distribution of `A` within `[lo, hi]`.

DERIVED: the exponent `2` squares the range. `4` is the arithmetic–geometric-mean constant: the
product `(hi − m)(m − lo)` of two numbers with fixed sum `hi − lo` is largest when they are equal,
at a quarter of the square of that sum. Neither is a choice; `lo` and `hi` are the caller's. -/
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

/-- `DifferentiableAt ℝ (meanf E A) β`, at every `β`. The `differentiableAt` projection of
`gibbs_mean_deriv_eq_neg_cov`.

DERIVED: no numeral. -/
theorem differentiableAt_meanf (E A : ι → ℝ) (β : ℝ) : DifferentiableAt ℝ (meanf E A) β :=
  (gibbs_mean_deriv_eq_neg_cov E A β).differentiableAt

/-- If `A` takes values in `[loA, hiA]` and `E` in `[loE, hiE]`, then at every real `β`

    ‖deriv (meanf E A) β‖ ≤ (hiA − loA) * (hiE − loE) / 4.

Three steps: `gibbs_mean_deriv_eq_neg_cov` identifies the derivative as `-Covf`,
`abs_Covf_le_sqrt_mul_sqrt` bounds its absolute value by a product of square roots, and
`VarObs_le_sq_range_div_four` bounds each variance, so each square root is at most half its range.
`[Nonempty ι]` is used to produce one index at which both ranges are seen to be nonnegative.

The bound is a constant in `β`. It depends on the two ranges only, not on `E`, `A` or `ι` beyond
those.

DERIVED: `4` is the product of the two halves `(hiA − loA)/2` and `(hiE − loE)/2` that the square
roots are bounded by, so it is Popoviciu's constant appearing once for each of the two variances and
not a chosen tolerance. `loA`, `hiA`, `loE`, `hiE` are the caller's. -/
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

/-- `differentiableAt_meanf` restated on a closed interval: `meanf E A` is differentiable at every
`x ∈ Set.Icc a b`. The interval plays no role — differentiability holds at every real — and the
statement exists to match the shape a mean-value argument consumes.

DERIVED: no numeral. `a` and `b` are the caller's endpoints. -/
theorem differentiableAt_meanf_on (E A : ι → ℝ) (a b : ℝ) :
    ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (meanf E A) x :=
  fun x _ => differentiableAt_meanf E A x

/-- `norm_deriv_meanf_le` restated on a closed interval: under the same range hypotheses,
`‖deriv (meanf E A) x‖ ≤ (hiA − loA) * (hiE − loE) / 4` for every `x ∈ Set.Icc a b`. The interval
plays no role, since the bound holds at every real `x`.

Scope: `meanf` is the finite-sum Gibbs mean of this module, over a `Fintype ι` with weights
`exp (-β * E i)`. No statement here relates it to `Complete.d2At`, to `wilsonCorrAt`, or to a Gibbs
state given by an integral against a measure; the Wilson ensemble's own differentiation identity is
`WilsonAnalytic.expect_hasDerivAt`, over a Haar integral rather than a finite sum.

The constant depends on the two ranges at the fixed index type `ι`. Nothing here bounds it uniformly
over a family of index types of growing size.

DERIVED: `4` is `norm_deriv_meanf_le`'s, Popoviciu's constant appearing once for each of the two
variances; the statement adds no numeral of its own. -/
theorem norm_deriv_meanf_le_on (E A : ι → ℝ) {loA hiA loE hiE : ℝ}
    (hAlo : ∀ i, loA ≤ A i) (hAhi : ∀ i, A i ≤ hiA)
    (hElo : ∀ i, loE ≤ E i) (hEhi : ∀ i, E i ≤ hiE) (a b : ℝ) :
    ∀ x ∈ Set.Icc a b, ‖deriv (meanf E A) x‖ ≤ (hiA - loA) * (hiE - loE) / 4 :=
  fun x _ => norm_deriv_meanf_le E A hAlo hAhi hElo hEhi x

/-- Under the same range hypotheses, `meanf E A` is Lipschitz on `Set.Icc a b` with constant
`(hiA − loA) * (hiE − loE) / 4`: for all `x, y` in the interval,
`|meanf E A x − meanf E A y| ≤ L * |x − y|`.

`Convex.norm_image_sub_le_of_norm_deriv_le` on the interval, fed by `differentiableAt_meanf_on` and
`norm_deriv_meanf_le_on`, with `abs_sub_comm` to orient the difference.

DERIVED: `4` is `norm_deriv_meanf_le_on`'s constant, carried unchanged into the Lipschitz constant;
`a`, `b` and the four range endpoints are the caller's. -/
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
