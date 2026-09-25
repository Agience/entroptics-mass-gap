import Mathlib
import MassGap.PeriodicContent
import MassGap.AsymptoticScaling

/-!
# MassGap.ThreePointN — requirement N as a connected three-point function at separated supports

## The statistic

For three observables `A`, `B`, `C` under a state `ν`, with `cen ν f = f − ν(f)·1`:

    cov2 ν A B    = ν (cen A · cen B)                 connected two-point function
    cum3 ν A B C  = ν (cen A · cen B · cen C)         connected three-point function
    sepRatio      = cum3² / |cov2 A B · cov2 B C · cov2 C A|

`sepRatio_affine`: `sepRatio` does not change under `A ↦ a·A + b·1`, `B ↦ a'·B + b'·1`,
`C ↦ a''·C + b''·1` with `a a' a'' ≠ 0`, so it survives a multiplicative field renormalisation and an
additive (identity-mixing) one. With the three supports pairwise disjoint and at fixed physical
separation, no coincident-point product enters any of the four cumulants.

## The free gauge theory's value is zero

In the free (`g = 0`) gauge theory the composite `tr F²` is a quadratic form in a Gaussian field. For
symmetric `Pⱼ` and two-point matrices with `Wⱼᵢ = Wᵢⱼᵀ`, Wick's theorem writes the connected
three-point function of three forms `φᵀPⱼφ` as `8 · trace (P₁ W₁₂ P₂ W₂₃ P₃ W₃₁)`. `freeCum3` is that
expression on matrices; the Gaussian integral is not formed. `trace_three_eq_zero_of_duality` proves
that any `J`, `K` with `K Pⱼ J = −Pⱼ` and `J W K = W` make the trace zero
(`freeCum3_eq_zero_of_duality`), and `freeSepRatio_of_duality` gives `‖freeCum3‖² / ‖c₁₂ c₂₃ c₃₁‖ = 0`
for every `c`. For the free Maxwell field the duality rotation `(E, B) ↦ (B, −E)` preserves the
two-point function and negates the Minkowski density `E² − B²`; in Euclidean signature the same zero is
the case `J = diag(1, −1)`, `K = −J` on the self-dual and anti-self-dual parts, which the
separated-point propagator pairs with each other. Reading the matrix statement as the free field's value
is physics; that link is not constructed here. The two-point trace stays free: `dual_example` satisfies
the duality hypotheses with a zero three-point value and a non-zero two-point trace.

A Gaussian law has every connected function of order three vanish, so `0` is also the value when the
block composites are jointly Gaussian (a generalised free field in `tr F²`). A family with `sepRatio`
bounded below is separated from both. A quadratic composite of a free field without the duality has
`8 · trace (P₁ W₁₂ P₂ W₂₃ P₃ W₃₁)` non-zero in general (`P = W = 1` on two components gives `16`), so the
Wick square of a free massive scalar or vector field also has `sepRatio` bounded below: this statistic
separates `tr F²` from Gaussian laws and from the free massless gauge field, and the free massive fields
are separated by the short-distance behaviour asymptotic freedom prescribes (requirement Y).

## Along a family, and in the limit

`ThreePointSeparated ν A B C`: `sepRatio` is eventually at least one `c > 0`. It is invariant under
renormalising each member (`threePointSeparated_renormalize`), forces the connected three-point
function to be non-zero eventually (`threePointSeparated_cum3_ne_zero`), and passes to limits:
`ratio_le_of_tendsto` carries `c ≤ sepRatio` to the limits of the renormalised cumulants when the
limiting two-point product is non-zero, and `ne_zero_of_le_ratio` makes the limiting three-point
function non-zero.

## The Wilson family, and the one open statement

`tripleObs N ℓ D β j`, `j = 0, 1, 2`: the plaquette-energy composite summed over a block of side
`⌈ℓ / aRun N β⌉` lattice units, at base sites `0`, `⌈D / aRun N β⌉·e₀`, `⌈D / aRun N β⌉·e₁`: three
blocks of physical side `ℓ` whose base sites are `D` apart along `e₀` and along `e₁` (pairwise offsets
`D`, `D`, `√2·D`), at the two-loop spacing `aRun N β`. At `N = 3` this is the `aRun 3` family. Once
`aRun N β ≤ D − ℓ`, which holds at every large `β` (`WeakCouplingWindow.eventually_aRun_le`),
`latUnits_lt` puts the block side strictly below the offset, so the three blocks' plaquettes use
pairwise disjoint link sets; that support statement is not formalised here.

`WilsonThreePointSeparation N hN` is the statement this module does not prove: there are `0 < ℓ < D`
and `c > 0` with `c ≤ sepRatio` of the three blocks under `PeriodicState.periodicState hN β` for every
large `β`. `wilson_threePointSeparated`, `wilson_separated_from_free` and
`wilson_continuum_threePoint` derive from it the family statement, the uniform separation from the
free value, and a non-zero connected three-point function in every limit of the renormalised
cumulants with non-degenerate two-point limits.

## Scope

Nothing in the tree bounds a connected function of order three or more from below at any `β > 0`:
the variance floors are two-point, the strong-coupling cluster bounds are upper bounds, and none of
them reaches `β → ∞`. The identification of the Wick trace with the free field's three-point function,
and of the duality `J`, `K` with the free Maxwell field's, is not constructed here. The duality is
not shown to act on the lattice field at `g = 0`, so the comparator is the continuum free value `0`.
-/

namespace MassGap.ThreePointN

open MeasureTheory Filter Topology

/-! ## 1. Connected functions of a state, and their renormalisation -/

section Cumulants

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The centred observable `f − ν(f)·1`.

DERIVED: `1` is the constant observable the mean multiplies. -/
noncomputable def cen (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) : C(X, ℝ) :=
  f - (ν f) • (1 : C(X, ℝ))

#print axioms cen

/-- The connected two-point function `ν (cen A · cen B)`.

DERIVED: no numeral. -/
noncomputable def cov2 (ν : MassGap.DLRLimit.State X) (A B : C(X, ℝ)) : ℝ :=
  ν (cen ν A * cen ν B)

#print axioms cov2

/-- The connected three-point function `ν (cen A · cen B · cen C)`, the third joint cumulant.

DERIVED: no numeral. -/
noncomputable def cum3 (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) : ℝ :=
  ν (cen ν A * cen ν B * cen ν C)

#print axioms cum3

/-- **The normalised three-point statistic** `cum3² / |cov2 A B · cov2 B C · cov2 C A|`. At a zero
two-point product it is `0`, by `x / 0 = 0`.

DERIVED: `2` makes the numerator scale as the product of the three squared scales, the scaling of the
denominator, so the ratio is scale-free (`sepRatio_affine`). CHOSEN: the square and the absolute
value rather than a signed ratio with a square root: they need no sign condition on the two-point
functions. -/
noncomputable def sepRatio (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) : ℝ :=
  cum3 ν A B C ^ 2 / |cov2 ν A B * cov2 ν B C * cov2 ν C A|

#print axioms sepRatio

/-- DERIVED: `0` is the lower bound; `2` is the square. -/
theorem sepRatio_nonneg (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) :
    0 ≤ sepRatio ν A B C :=
  div_nonneg (sq_nonneg _) (abs_nonneg _)

#print axioms sepRatio_nonneg

/-- **Centring absorbs the shift and keeps the scale.** `cen ν (a • f + b • 1) = a • cen ν f`.

DERIVED: `1` is the constant observable. -/
theorem cen_affine (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (a b : ℝ) :
    cen ν (a • f + b • (1 : C(X, ℝ))) = a • cen ν f := by
  have hmean : ν (a • f + b • (1 : C(X, ℝ))) = a * ν f + b := by
    rw [ν.map_add, ν.map_smul, ν.map_smul, ν.map_one, mul_one]
  unfold cen
  rw [hmean]
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul]
  ring

#print axioms cen_affine

/-- The connected two-point function scales by the product of the two scales.

DERIVED: `1` is the constant observable. -/
theorem cov2_affine (ν : MassGap.DLRLimit.State X) (A B : C(X, ℝ)) (a b a' b' : ℝ) :
    cov2 ν (a • A + b • (1 : C(X, ℝ))) (a' • B + b' • (1 : C(X, ℝ))) = a * a' * cov2 ν A B := by
  unfold cov2
  rw [cen_affine, cen_affine, smul_mul_smul_comm, ν.map_smul]

#print axioms cov2_affine

/-- The connected three-point function scales by the product of the three scales.

DERIVED: `1` is the constant observable. -/
theorem cum3_affine (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) (a b a' b' a'' b'' : ℝ) :
    cum3 ν (a • A + b • (1 : C(X, ℝ))) (a' • B + b' • (1 : C(X, ℝ)))
        (a'' • C + b'' • (1 : C(X, ℝ)))
      = a * a' * a'' * cum3 ν A B C := by
  unfold cum3
  rw [cen_affine, cen_affine, cen_affine, smul_mul_smul_comm, smul_mul_smul_comm, ν.map_smul]

#print axioms cum3_affine

/-- **`sepRatio` is renormalisation-invariant.** For non-zero scales `a`, `a'`, `a''` and any shifts,
the renormalised triple has the same `sepRatio`. Numerator and denominator both carry
`(a a' a'')²`.

DERIVED: `0` is the excluded scale; `1` is the constant observable. -/
theorem sepRatio_affine (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) {a a' a'' : ℝ}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (ha'' : a'' ≠ 0) (b b' b'' : ℝ) :
    sepRatio ν (a • A + b • (1 : C(X, ℝ))) (a' • B + b' • (1 : C(X, ℝ)))
        (a'' • C + b'' • (1 : C(X, ℝ)))
      = sepRatio ν A B C := by
  unfold sepRatio
  rw [cum3_affine, cov2_affine, cov2_affine, cov2_affine]
  have hne : a * a' * a'' ≠ 0 := mul_ne_zero (mul_ne_zero ha ha') ha''
  have hs : 0 < (a * a' * a'') ^ 2 := sq_pos_iff.mpr hne
  rw [show (a * a' * a'' * cum3 ν A B C) ^ 2 = (a * a' * a'') ^ 2 * cum3 ν A B C ^ 2 by ring,
    show a * a' * cov2 ν A B * (a' * a'' * cov2 ν B C) * (a'' * a * cov2 ν C A)
      = (a * a' * a'') ^ 2 * (cov2 ν A B * cov2 ν B C * cov2 ν C A) by ring,
    abs_mul ((a * a' * a'') ^ 2) (cov2 ν A B * cov2 ν B C * cov2 ν C A), abs_of_pos hs]
  exact mul_div_mul_left _ _ hs.ne'

#print axioms sepRatio_affine

/-- **A positive lower bound on `sepRatio` makes the connected three-point function and the
two-point product non-zero.** At `cum3 = 0` or at a zero two-point product the ratio is `0`.

DERIVED: `0` is the strict lower bound on `c`, the excluded values, and the value of the ratio at
them; `2` is the square. -/
theorem cum3_ne_zero_of_le (ν : MassGap.DLRLimit.State X) (A B C : C(X, ℝ)) {c : ℝ}
    (hc : 0 < c) (h : c ≤ sepRatio ν A B C) :
    cum3 ν A B C ≠ 0 ∧ cov2 ν A B * cov2 ν B C * cov2 ν C A ≠ 0 := by
  constructor
  · intro h0
    unfold sepRatio at h
    rw [h0, zero_pow two_ne_zero, zero_div] at h
    linarith
  · intro h0
    unfold sepRatio at h
    rw [h0, abs_zero, div_zero] at h
    linarith

#print axioms cum3_ne_zero_of_le

end Cumulants

/-! ## 2. The free gauge theory's value: the Wick trace under duality -/

section Free

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Wick value of the connected three-point function of three quadratic composites.** For a
Gaussian field `φ`, symmetric `Pⱼ` and `Wⱼᵢ = Wᵢⱼᵀ` (so `W₃₁ = W₁₃ᵀ`), and composites `φᵀPⱼφ`,
Wick's theorem gives the connected three-point function as
`8 · trace (P₁ W₁₂ P₂ W₂₃ P₃ W₃₁)`, `Wᵢⱼ` the field's two-point matrix between the supports of `Pᵢ`
and `Pⱼ`. This is the definition; the Gaussian integral it evaluates is not formed here.

DERIVED: `8 = 2^{3−1}·(3−1)!`, the cumulant coefficient of a quadratic form at order `3`: the number
of ways to close three pairs of field legs into one cycle. -/
noncomputable def freeCum3 (P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ : Matrix n n 𝕜) : 𝕜 :=
  8 * Matrix.trace (P₁ * W₁₂ * P₂ * W₂₃ * P₃ * W₃₁)

#print axioms freeCum3

/-- **Duality forces the three-point trace to zero.** If `K Pⱼ J = −Pⱼ` for the three composites and
`J W K = W` for the three two-point matrices, then `trace (P₁ W₁₂ P₂ W₂₃ P₃ W₃₁) = 0`.

Inserting `J W K` for each `W` and moving the last `K` to the front by cyclicity of the trace writes
the trace as the same expression in `K Pⱼ J = −Pⱼ`; three signs give `t = −t`, so `t = 0` in
characteristic zero. For the free Maxwell field `J` is the duality rotation `(E, B) ↦ (B, −E)`,
`K` its transpose, and `Pⱼ` the Lagrangian density `E² − B²`, which the rotation negates.

DERIVED: `0` is the conclusion; the three signs are the three composites. -/
theorem trace_three_eq_zero_of_duality (J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ : Matrix n n 𝕜)
    (h₁ : K * P₁ * J = -P₁) (h₂ : K * P₂ * J = -P₂) (h₃ : K * P₃ * J = -P₃)
    (w₁₂ : J * W₁₂ * K = W₁₂) (w₂₃ : J * W₂₃ * K = W₂₃) (w₃₁ : J * W₃₁ * K = W₃₁) :
    Matrix.trace (P₁ * W₁₂ * P₂ * W₂₃ * P₃ * W₃₁) = 0 := by
  have key : Matrix.trace (P₁ * W₁₂ * P₂ * W₂₃ * P₃ * W₃₁)
      = Matrix.trace ((K * P₁ * J) * W₁₂ * (K * P₂ * J) * W₂₃ * (K * P₃ * J) * W₃₁) := by
    calc Matrix.trace (P₁ * W₁₂ * P₂ * W₂₃ * P₃ * W₃₁)
        = Matrix.trace (P₁ * (J * W₁₂ * K) * P₂ * (J * W₂₃ * K) * P₃ * (J * W₃₁ * K)) := by
          rw [w₁₂, w₂₃, w₃₁]
      _ = Matrix.trace ((P₁ * J * W₁₂ * K * P₂ * J * W₂₃ * K * P₃ * J * W₃₁) * K) := by
          simp only [Matrix.mul_assoc, mul_assoc]
      _ = Matrix.trace (K * (P₁ * J * W₁₂ * K * P₂ * J * W₂₃ * K * P₃ * J * W₃₁)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((K * P₁ * J) * W₁₂ * (K * P₂ * J) * W₂₃ * (K * P₃ * J) * W₃₁) := by
          simp only [Matrix.mul_assoc, mul_assoc]
  rw [h₁, h₂, h₃] at key
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_mul, mul_neg, neg_neg, Matrix.trace_neg] at key
  exact CharZero.eq_neg_self_iff.mp key

#print axioms trace_three_eq_zero_of_duality

/-- **`freeCum3` is zero under the duality hypotheses.**

DERIVED: `0` is the value; `8` is `freeCum3`'s coefficient, inside the proof. -/
theorem freeCum3_eq_zero_of_duality (J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ : Matrix n n 𝕜)
    (h₁ : K * P₁ * J = -P₁) (h₂ : K * P₂ * J = -P₂) (h₃ : K * P₃ * J = -P₃)
    (w₁₂ : J * W₁₂ * K = W₁₂) (w₂₃ : J * W₂₃ * K = W₂₃) (w₃₁ : J * W₃₁ * K = W₃₁) :
    freeCum3 P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ = 0 := by
  unfold freeCum3
  rw [trace_three_eq_zero_of_duality J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ h₁ h₂ h₃ w₁₂ w₂₃ w₃₁, mul_zero]

#print axioms freeCum3_eq_zero_of_duality

end Free

/-- **The free value of the normalised statistic**, from a complex three-point value `t₃` and three
complex two-point values: `‖t₃‖² / ‖c₁₂ c₂₃ c₃₁‖`. Wightman functions are complex, so the free side
is stated over `ℂ`.

DERIVED: `2` is the square, matching `sepRatio`. -/
noncomputable def freeSepRatio (t₃ c₁₂ c₂₃ c₃₁ : ℂ) : ℝ :=
  ‖t₃‖ ^ 2 / ‖c₁₂ * c₂₃ * c₃₁‖

#print axioms freeSepRatio

/-- **The free value of the statistic is `0`**, for all matrices satisfying the duality hypotheses
and all three two-point values `c₁₂ c₂₃ c₃₁`.

DERIVED: `0` is the value; `2` is the square. -/
theorem freeSepRatio_of_duality {n : Type*} [Fintype n] [DecidableEq n]
    (J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ : Matrix n n ℂ)
    (h₁ : K * P₁ * J = -P₁) (h₂ : K * P₂ * J = -P₂) (h₃ : K * P₃ * J = -P₃)
    (w₁₂ : J * W₁₂ * K = W₁₂) (w₂₃ : J * W₂₃ * K = W₂₃) (w₃₁ : J * W₃₁ * K = W₃₁)
    (c₁₂ c₂₃ c₃₁ : ℂ) :
    freeSepRatio (freeCum3 P₁ P₂ P₃ W₁₂ W₂₃ W₃₁) c₁₂ c₂₃ c₃₁ = 0 := by
  unfold freeSepRatio
  rw [freeCum3_eq_zero_of_duality J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ h₁ h₂ h₃ w₁₂ w₂₃ w₃₁, norm_zero,
    zero_pow two_ne_zero, zero_div]

#print axioms freeSepRatio_of_duality

/-! ### A named case: the duality hypotheses hold, the two-point trace does not vanish -/

/-- The duality rotation `(E, B) ↦ (B, −E)` on one electric and one magnetic component.

DERIVED: the entries `0`, `1`, `−1` are the rotation by a quarter turn; `2` is the number of
components. -/
noncomputable def dualJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The transpose of `dualJ`.

DERIVED: the entries are `dualJ`'s transposed; `2` is the number of components. -/
noncomputable def dualK : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The Lagrangian density `E² − B²` as a quadratic form.

DERIVED: `1` and `−1` are the coefficients of `E²` and `B²`; `0` the absent cross term; `2` the
number of components. -/
noncomputable def dualP : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- **The named case.** `dualK · dualP · dualJ = −dualP`, `dualJ · 1 · dualK = 1` (the identity
two-point matrix is duality-invariant), the free three-point value at three copies of `dualP` with
identity two-point matrices is `0`, and the two-point trace `trace (dualP · 1 · dualP · 1)` is `2`, not
`0`: duality removes the odd connected function and keeps the even one.

DERIVED: `1` is the identity two-point matrix; `0` the three-point value; `2` is `1² + (−1)²`, the
two-point trace, and the number of components. -/
theorem dual_example :
    dualK * dualP * dualJ = -dualP
      ∧ dualJ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * dualK = 1
      ∧ freeCum3 dualP dualP dualP 1 1 1 = 0
      ∧ Matrix.trace (dualP * 1 * dualP * 1) = 2 := by
  have hP : dualK * dualP * dualJ = -dualP := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dualJ, dualK, dualP, Matrix.mul_apply, Fin.sum_univ_two]
  have hW : dualJ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * dualK = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dualJ, dualK, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  refine ⟨hP, hW, freeCum3_eq_zero_of_duality dualJ dualK dualP dualP dualP 1 1 1
    hP hP hP hW hW hW, ?_⟩
  norm_num [dualP, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms dual_example

/-! ## 3. Along a family, and in the limit -/

section Family

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The three-point condition along a family.** Eventually in `i`, `sepRatio` of `A i`, `B i`,
`C i` under `ν i` is at least one `c > 0`. The duality matrix model's ratio is `0`
(`freeSepRatio_of_duality`), the value the free gauge field's composite takes at separated supports, and
a jointly Gaussian triple has `cum3 = 0`; this bounds the family away from both.

DERIVED: `0` is the strict lower bound on `c`. -/
def ThreePointSeparated (ν : ℕ → MassGap.DLRLimit.State X) (A B C : ℕ → C(X, ℝ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, c ≤ sepRatio (ν i) (A i) (B i) (C i)

#print axioms ThreePointSeparated

/-- **`ThreePointSeparated` does not see field renormalisation.** For non-zero `Z i` and any shifts,
the renormalised family satisfies it exactly when the bare one does.

DERIVED: `0` is the excluded scale; `1` is the constant observable. -/
theorem threePointSeparated_renormalize (ν : ℕ → MassGap.DLRLimit.State X)
    (A B C : ℕ → C(X, ℝ)) (Z b b' b'' : ℕ → ℝ) (hZ : ∀ i, Z i ≠ 0) :
    ThreePointSeparated ν (fun i => Z i • A i + b i • (1 : C(X, ℝ)))
        (fun i => Z i • B i + b' i • (1 : C(X, ℝ))) (fun i => Z i • C i + b'' i • (1 : C(X, ℝ)))
      ↔ ThreePointSeparated ν A B C := by
  have hk : ∀ i, sepRatio (ν i) (Z i • A i + b i • (1 : C(X, ℝ)))
      (Z i • B i + b' i • (1 : C(X, ℝ))) (Z i • C i + b'' i • (1 : C(X, ℝ)))
      = sepRatio (ν i) (A i) (B i) (C i) :=
    fun i => sepRatio_affine (ν i) (A i) (B i) (C i) (hZ i) (hZ i) (hZ i) (b i) (b' i) (b'' i)
  unfold ThreePointSeparated
  simp only [hk]

#print axioms threePointSeparated_renormalize

/-- **It separates the family from the free value.** `ThreePointSeparated` holds exactly when
`|sepRatio − 0|` is eventually at least one `c > 0`, `0` being the free and the Gaussian value.

DERIVED: `0` is the free value and the strict lower bound on `c`. -/
theorem threePointSeparated_iff_from_free (ν : ℕ → MassGap.DLRLimit.State X)
    (A B C : ℕ → C(X, ℝ)) :
    ThreePointSeparated ν A B C
      ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, c ≤ |sepRatio (ν i) (A i) (B i) (C i) - 0| := by
  have h : ∀ i, |sepRatio (ν i) (A i) (B i) (C i) - 0| = sepRatio (ν i) (A i) (B i) (C i) :=
    fun i => by rw [sub_zero, abs_of_nonneg (sepRatio_nonneg _ _ _ _)]
  unfold ThreePointSeparated
  simp only [h]

#print axioms threePointSeparated_iff_from_free

/-- **It forces a non-zero connected three-point function.** Eventually `cum3 ≠ 0` and the two-point
product is non-zero; a Gaussian family, and the free massless gauge field's composite at separated
supports, have `cum3 = 0`.

DERIVED: `0` is the excluded value. -/
theorem threePointSeparated_cum3_ne_zero (ν : ℕ → MassGap.DLRLimit.State X)
    (A B C : ℕ → C(X, ℝ)) (h : ThreePointSeparated ν A B C) :
    ∀ᶠ i in atTop, cum3 (ν i) (A i) (B i) (C i) ≠ 0
      ∧ cov2 (ν i) (A i) (B i) * cov2 (ν i) (B i) (C i) * cov2 (ν i) (C i) (A i) ≠ 0 := by
  obtain ⟨c, hc, hev⟩ := h
  filter_upwards [hev] with i hi
  exact cum3_ne_zero_of_le (ν i) (A i) (B i) (C i) hc hi

#print axioms threePointSeparated_cum3_ne_zero

end Family

/-- **The bound passes to limits.** If `k₃ → K₃`, the three two-point sequences converge with a
non-zero limiting product, and `c ≤ k₃² / |k₁₂ k₂₃ k₃₁|` eventually, then
`c ≤ K₃² / |K₁₂ K₂₃ K₃₁|`. The map `(x, y, z, w) ↦ x² / |y z w|` is continuous where `y z w ≠ 0`.

DERIVED: `2` is the square; `0` is the excluded limiting product. -/
theorem ratio_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {k₃ k₁₂ k₂₃ k₃₁ : ι → ℝ}
    {K₃ K₁₂ K₂₃ K₃₁ c : ℝ} (h₃ : Tendsto k₃ l (𝓝 K₃)) (h₁₂ : Tendsto k₁₂ l (𝓝 K₁₂))
    (h₂₃ : Tendsto k₂₃ l (𝓝 K₂₃)) (h₃₁ : Tendsto k₃₁ l (𝓝 K₃₁)) (hK : K₁₂ * K₂₃ * K₃₁ ≠ 0)
    (hev : ∀ᶠ i in l, c ≤ k₃ i ^ 2 / |k₁₂ i * k₂₃ i * k₃₁ i|) :
    c ≤ K₃ ^ 2 / |K₁₂ * K₂₃ * K₃₁| := by
  have ht : Tendsto (fun i => k₃ i ^ 2 / |k₁₂ i * k₂₃ i * k₃₁ i|) l
      (𝓝 (K₃ ^ 2 / |K₁₂ * K₂₃ * K₃₁|)) :=
    (h₃.pow 2).div ((h₁₂.mul h₂₃).mul h₃₁).abs (abs_ne_zero.mpr hK)
  exact ge_of_tendsto ht hev

#print axioms ratio_le_of_tendsto

/-- **A positive lower bound on the limiting ratio makes the limiting three-point value non-zero.**

DERIVED: `0` is the strict lower bound on `c` and the excluded value; `2` is the square. -/
theorem ne_zero_of_le_ratio {K₃ K₁₂ K₂₃ K₃₁ c : ℝ} (hc : 0 < c)
    (h : c ≤ K₃ ^ 2 / |K₁₂ * K₂₃ * K₃₁|) : K₃ ≠ 0 := by
  intro h0
  rw [h0, zero_pow two_ne_zero, zero_div] at h
  linarith

#print axioms ne_zero_of_le_ratio

/-! ## 4. The Wilson family at the periodic state -/

/-- A physical length `x` in lattice units at spacing `a`, rounded up: `⌈x / a⌉₊`.

DERIVED: no numeral. -/
noncomputable def latUnits (x a : ℝ) : ℕ := ⌈x / a⌉₊

#print axioms latUnits

/-- **Rounded-up lattice lengths keep a strict order once the spacing is below the difference.** For
`0 ≤ ℓ`, `0 < a` and `a ≤ D − ℓ`, `latUnits ℓ a < latUnits D a`: `⌈ℓ/a⌉ < ℓ/a + 1 ≤ D/a ≤ ⌈D/a⌉`.

DERIVED: `0` is the sign of `ℓ` and of `a`; `1` is the rounding slack of `⌈·⌉₊`, inside the proof. -/
theorem latUnits_lt {ℓ D a : ℝ} (hℓ : 0 ≤ ℓ) (ha : 0 < a) (had : a ≤ D - ℓ) :
    latUnits ℓ a < latUnits D a := by
  unfold latUnits
  have h1 : (⌈ℓ / a⌉₊ : ℝ) < ℓ / a + 1 := Nat.ceil_lt_add_one (div_nonneg hℓ ha.le)
  have h2 : 1 ≤ (D - ℓ) / a := by
    rw [le_div_iff₀ ha]
    linarith
  have h3 : (D - ℓ) / a = D / a - ℓ / a := sub_div D ℓ a
  have h4 : D / a ≤ (⌈D / a⌉₊ : ℝ) := Nat.le_ceil _
  have h5 : (⌈ℓ / a⌉₊ : ℝ) < (⌈D / a⌉₊ : ℝ) := by linarith
  exact_mod_cast h5

#print axioms latUnits_lt

/-- **The plaquette-energy composite of a block.** The sum of `iplaqObs q` over the plaquettes with
directions `μ < ν` and base site in `x₀ + [0, R)⁴`. Each summand is a class function of a plaquette
holonomy, so the sum is gauge invariant; the membership in `GaugeInvariantAlgebra`'s algebra is not
restated here. At weak coupling `iplaqObs q` is `a⁴g²·tr F²/(2N)` plus operators of higher dimension,
so the block is the lattice form of `tr F²` smeared over the block.

DERIVED: `4` is the spacetime dimension. CHOSEN: directions `μ < ν`, one orientation per plane,
since the density does not see orientation. -/
noncomputable def blockObs (N : ℕ) (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ) :
    C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) :=
  ∑ v : Fin 4 → Fin R, ∑ d ∈ Finset.univ.filter (fun d : Fin 4 × Fin 4 => d.1 < d.2),
    MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (d, fun μ => x₀ μ + ((v μ : ℕ) : ℤ))

#print axioms blockObs

/-- The three base sites: `j = 0` at the origin, `j = 1` at `n·e₀`, `j = 2` at `n·e₁`.

CHOSEN: the two coordinate directions `0` and `1`, which put the three blocks at the corners of a
right isosceles triangle; any three pairwise separated positions serve. DERIVED: `0` is the origin
coordinate; `j = μ + 1` selects
`μ = 0` at `j = 1` and `μ = 1` at `j = 2`, and no `μ` at `j = 0`; `3` is the number of blocks. -/
def tripleBase (n : ℕ) (j : Fin 3) : MassGap.GibbsSpec.ISite :=
  fun μ => if (j : ℕ) = (μ : ℕ) + 1 then (n : ℤ) else 0

#print axioms tripleBase

/-- **The three composites at coupling `β`.** Blocks of side `latUnits ℓ (aRun N β)` at the base sites
`tripleBase (latUnits D (aRun N β)) j`: physical side `ℓ`, physical separation `D`, at the two-loop
`SU(N)` spacing. At `N = 3` the spacing is `aRun 3`.

DERIVED: `3` is the number of blocks. -/
noncomputable def tripleObs (N : ℕ) (ℓ D β : ℝ) (j : Fin 3) :
    C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) :=
  blockObs N (tripleBase (latUnits D (MassGap.AsymptoticScaling.aRun N β)) j)
    (latUnits ℓ (MassGap.AsymptoticScaling.aRun N β))

#print axioms tripleObs

/-- **THE OPEN STATEMENT.** There are a physical block side `ℓ`, a physical separation `D > ℓ` and a
constant `c > 0` such that, for every large `β`, the three block composites under the periodic
infinite-volume Wilson state have `sepRatio` at least `c`.

Every block is gauge invariant (each summand is a class function of a plaquette holonomy). Once
`aRun N β ≤ D − ℓ`, `latUnits_lt` puts the side below the offset, so the link supports are disjoint. The
free value is `0` in the duality matrix model (`freeSepRatio_of_duality`), so this separates a connected
function of order three from its free massless value, in renormalisation-invariant form
(`sepRatio_affine`). It is open at every `β > 0`.

DERIVED: `0` is the lower bound on `ℓ` and `c` and indexes the first block; `1` and `2` index the
second and third. -/
def WilsonThreePointSeparation (N : ℕ) (hN : N ≠ 0) : Prop :=
  ∃ ℓ D c : ℝ, 0 < ℓ ∧ ℓ < D ∧ 0 < c ∧
    ∀ᶠ β in atTop, c ≤ sepRatio (MassGap.PeriodicState.periodicState hN β)
      (tripleObs N ℓ D β 0) (tripleObs N ℓ D β 1) (tripleObs N ℓ D β 2)

#print axioms WilsonThreePointSeparation

variable {N : ℕ}

/-- **Along every coupling sequence to infinity, the Wilson family is `ThreePointSeparated`.** From
`WilsonThreePointSeparation`, with the same `ℓ`, `D`, for every `β i → ∞`.

DERIVED: `0` is the lower bound on `ℓ` and indexes the first block; `1` and `2` index the second and
third block. -/
theorem wilson_threePointSeparated (hN : N ≠ 0) (hsep : WilsonThreePointSeparation N hN) :
    ∃ ℓ D : ℝ, 0 < ℓ ∧ ℓ < D ∧ ∀ β : ℕ → ℝ, Tendsto β atTop atTop →
      ThreePointSeparated (fun i => MassGap.PeriodicState.periodicState hN (β i))
        (fun i => tripleObs N ℓ D (β i) 0) (fun i => tripleObs N ℓ D (β i) 1)
        (fun i => tripleObs N ℓ D (β i) 2) := by
  obtain ⟨ℓ, D, c, hℓ, hD, hc, hev⟩ := hsep
  exact ⟨ℓ, D, hℓ, hD, fun β hβ => ⟨c, hc, hβ.eventually hev⟩⟩

#print axioms wilson_threePointSeparated

/-- **Uniform separation from the free value.** From `WilsonThreePointSeparation`: along every
`β i → ∞`, for any free data satisfying the duality hypotheses and any free two-point values, the
Wilson `sepRatio` eventually differs from the free one by at least `c`.

DERIVED: `0` is the lower bound on `ℓ` and `c` and indexes the first block; `1` and `2` index the
second and third block. -/
theorem wilson_separated_from_free (hN : N ≠ 0) (hsep : WilsonThreePointSeparation N hN) :
    ∃ ℓ D c : ℝ, 0 < ℓ ∧ ℓ < D ∧ 0 < c ∧ ∀ β : ℕ → ℝ, Tendsto β atTop atTop →
      ∀ (n : Type) [Fintype n] [DecidableEq n] (J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ : Matrix n n ℂ),
        K * P₁ * J = -P₁ → K * P₂ * J = -P₂ → K * P₃ * J = -P₃ →
        J * W₁₂ * K = W₁₂ → J * W₂₃ * K = W₂₃ → J * W₃₁ * K = W₃₁ →
        ∀ c₁₂ c₂₃ c₃₁ : ℂ, ∀ᶠ i in atTop,
          c ≤ |sepRatio (MassGap.PeriodicState.periodicState hN (β i))
              (tripleObs N ℓ D (β i) 0) (tripleObs N ℓ D (β i) 1) (tripleObs N ℓ D (β i) 2)
            - freeSepRatio (freeCum3 P₁ P₂ P₃ W₁₂ W₂₃ W₃₁) c₁₂ c₂₃ c₃₁| := by
  obtain ⟨ℓ, D, c, hℓ, hD, hc, hev⟩ := hsep
  refine ⟨ℓ, D, c, hℓ, hD, hc, fun β hβ n _ _ J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ h₁ h₂ h₃ w₁₂ w₂₃ w₃₁
    c₁₂ c₂₃ c₃₁ => ?_⟩
  have hfree := freeSepRatio_of_duality J K P₁ P₂ P₃ W₁₂ W₂₃ W₃₁ h₁ h₂ h₃ w₁₂ w₂₃ w₃₁ c₁₂ c₂₃ c₃₁
  filter_upwards [hβ.eventually hev] with i hi
  rw [hfree, sub_zero, abs_of_nonneg (sepRatio_nonneg _ _ _ _)]
  exact hi

#print axioms wilson_separated_from_free

/-- **The continuum statement.** From `WilsonThreePointSeparation`: along every `β i → ∞`, for every
renormalisation `A ↦ Z i • A + bⱼ i • 1` with `Z i ≠ 0`, if the renormalised connected three-point
function converges to `K₃` and the three renormalised connected two-point functions converge with a
non-zero product, then `c ≤ K₃² / |K₀₁ K₁₂ K₂₀|` and `K₃ ≠ 0`. The limiting connected three-point
function of the composite is non-zero, where the free massless gauge field's is `0`.

DERIVED: `0` is the lower bound on `ℓ` and `c`, the excluded scale, product and value, and indexes
the first block; `1` is the
constant observable and indexes the second block; `2` indexes the third block and is the square. -/
theorem wilson_continuum_threePoint (hN : N ≠ 0) (hsep : WilsonThreePointSeparation N hN) :
    ∃ ℓ D c : ℝ, 0 < ℓ ∧ ℓ < D ∧ 0 < c ∧ ∀ β : ℕ → ℝ, Tendsto β atTop atTop →
      ∀ Z b₀ b₁ b₂ : ℕ → ℝ, (∀ i, Z i ≠ 0) →
      ∀ K₃ K₀₁ K₁₂ K₂₀ : ℝ, K₀₁ * K₁₂ * K₂₀ ≠ 0 →
      Tendsto (fun i => cum3 (MassGap.PeriodicState.periodicState hN (β i))
          (Z i • tripleObs N ℓ D (β i) 0
            + b₀ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          (Z i • tripleObs N ℓ D (β i) 1
            + b₁ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          (Z i • tripleObs N ℓ D (β i) 2
            + b₂ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))) atTop (𝓝 K₃) →
      Tendsto (fun i => cov2 (MassGap.PeriodicState.periodicState hN (β i))
          (Z i • tripleObs N ℓ D (β i) 0
            + b₀ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          (Z i • tripleObs N ℓ D (β i) 1
            + b₁ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))) atTop (𝓝 K₀₁) →
      Tendsto (fun i => cov2 (MassGap.PeriodicState.periodicState hN (β i))
          (Z i • tripleObs N ℓ D (β i) 1
            + b₁ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          (Z i • tripleObs N ℓ D (β i) 2
            + b₂ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))) atTop (𝓝 K₁₂) →
      Tendsto (fun i => cov2 (MassGap.PeriodicState.periodicState hN (β i))
          (Z i • tripleObs N ℓ D (β i) 2
            + b₂ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          (Z i • tripleObs N ℓ D (β i) 0
            + b₀ i • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))) atTop (𝓝 K₂₀) →
      c ≤ K₃ ^ 2 / |K₀₁ * K₁₂ * K₂₀| ∧ K₃ ≠ 0 := by
  obtain ⟨ℓ, D, c, hℓ, hD, hc, hev⟩ := hsep
  refine ⟨ℓ, D, c, hℓ, hD, hc,
    fun β hβ Z b₀ b₁ b₂ hZ K₃ K₀₁ K₁₂ K₂₀ hK h₃ h₀₁ h₁₂ h₂₀ => ?_⟩
  have hle : c ≤ K₃ ^ 2 / |K₀₁ * K₁₂ * K₂₀| := by
    refine ratio_le_of_tendsto h₃ h₀₁ h₁₂ h₂₀ hK ?_
    filter_upwards [hβ.eventually hev] with i hi
    have e := sepRatio_affine (MassGap.PeriodicState.periodicState hN (β i))
      (tripleObs N ℓ D (β i) 0) (tripleObs N ℓ D (β i) 1) (tripleObs N ℓ D (β i) 2)
      (hZ i) (hZ i) (hZ i) (b₀ i) (b₁ i) (b₂ i)
    exact le_of_le_of_eq hi e.symm
  exact ⟨hle, ne_zero_of_le_ratio hc hle⟩

#print axioms wilson_continuum_threePoint

end MassGap.ThreePointN
