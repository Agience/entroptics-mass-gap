import Mathlib
import MassGap.GapToOperator
import MassGap.VolumeRate

/-!
# MassGap.B2Locality — a contraction applied after the transfer step preserves a `GapAt` bound

Three inequalities about composing a bounded operator with `GapToOperator.opT`, plus the
proposition `ConnectedRadiusAtCellCeiling` and one consequence of it.

Contents:
* `aperture_does_not_weaken` — for a `TransferData D`, a rate `r` with `0 ≤ r` and `GapAt D r`, a
  continuous linear `P` with `‖P‖ ≤ 1`, and `x` orthogonal to the vacuum vector `Omega`,
  `‖P (opT D x)‖ ≤ r * ‖x‖`.
* `aperture_does_not_weaken_pow` — the same with `opT D ^ n` in place of `opT D` and `r ^ n` in
  place of `r`. One `P`, applied once after the `n` steps.
* `unapertured_suffices` — the previous statement for an index family `D : ι → TransferData A`,
  applied at a single index `F`.
* `ConnectedRadiusAtCellCeiling D` — the proposition `∀ F, GapAt (D F) ((3 : ℝ) ^ (-(1 : ℝ) / 4))`.
* `forgets_at_the_floor_of_B2` — from that proposition, `‖(opT (D F) ^ n) x‖ ≤ exp (-(κ₀YM * n)) * ‖x‖`
  on the vacuum complement, using `VolumeRate.cell_ceiling_eq_exp_neg_floor` to rewrite the ceiling
  as `exp (-κ₀YM)`.

Scope.
* `ConnectedRadiusAtCellCeiling` is a `def` producing a `Prop`; it is a hypothesis of
  `forgets_at_the_floor_of_B2` and no declaration in this module proves it.
* `P` is an arbitrary continuous linear map with `‖P‖ ≤ 1`, not an orthogonal projection: the
  inequalities use only the norm bound, so nothing here refers to a resolved subspace.
* Each theorem applies `P` once, after the transfer steps. The iterated composition
  `(P ∘ opT) ^ n` does not appear; iterating would need `P (opT x)` orthogonal to `Omega` at each
  stage, which would be a further hypothesis.
* `D : ι → TransferData A` ranges over a single fixed algebra `A`, so the index family in
  `unapertured_suffices` and `forgets_at_the_floor_of_B2` is used only at one index at a time
  (`hg F`, `hB2 F`), and carriers that vary with the geometry — such as
  `OSPositivity.wilsonSlabTransfer`'s — do not fit this signature.
* `GapAt` is a bound on the form of a `TransferData`. The bounds named `hbound` in
  `Certify.gap_uniform_in_volume_of_intensive` and `hint` in
  `CellSpectrum.gap_uniform_of_cell_intensive` are bounds on an abstract sequence `ℕ → ℝ`; no
  declaration relates the two.
* `TransferData`'s self-adjointness and contractivity are structure fields (`T_symm`,
  `T_contract`). `GNSHilbert.PositiveTransfer` is a separate condition, produced only by
  `positiveTransfer_of_T_eq_id` and `positiveTransfer_of_gram`, and is not assumed here.
-/

namespace MassGap.B2Locality

open MassGap.GNSHilbert MassGap.TransferGap MassGap.Transfer MassGap.GapToOperator

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A contraction applied after one transfer step inherits the vacuum-complement bound. For a
`TransferData D`, a rate `r` with `0 ≤ r` and `hg : GapAt D r`, a continuous linear map `P` on
`H D.toReflForm` with `‖P‖ ≤ 1`, and a vector `x` with `inner ℂ (Omega D.toReflForm D.vac) x = 0`,
the conclusion is `‖P (opT D x)‖ ≤ r * ‖x‖`. The proof chains `P.le_opNorm`, the bound `‖P‖ ≤ 1`,
and `GapToOperator.norm_opT_le_of_orth`.

Scope: `P` need only satisfy `‖P‖ ≤ 1`; it is not required to be a projection, and the
orthogonality hypothesis is on `x`, not on `P x`.

DERIVED: `0` is the lower bound on the rate `r`, which
`GapToOperator.norm_opT_le_of_orth` requires, and the value of the inner product expressing
orthogonality to the vacuum; `1` is the bound on `‖P‖`, the contraction constant, and is what makes
the middle step of the calculation an equality after `one_mul`. `r` is `GapAt`'s own rate. -/
theorem aperture_does_not_weaken (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (P : H D.toReflForm →L[ℂ] H D.toReflForm) (hP : ‖P‖ ≤ 1)
    (x : H D.toReflForm) (hx : inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ)) :
    ‖P (opT D x)‖ ≤ r * ‖x‖ := by
  have h1 : ‖P (opT D x)‖ ≤ ‖P‖ * ‖opT D x‖ := P.le_opNorm _
  have h2 : ‖P‖ * ‖opT D x‖ ≤ 1 * ‖opT D x‖ :=
    mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  have h3 : ‖opT D x‖ ≤ r * ‖x‖ := norm_opT_le_of_orth D hr hg x hx
  calc ‖P (opT D x)‖ ≤ ‖P‖ * ‖opT D x‖ := h1
    _ ≤ 1 * ‖opT D x‖ := h2
    _ = ‖opT D x‖ := one_mul _
    _ ≤ r * ‖x‖ := h3

#print axioms aperture_does_not_weaken

/-- The same bound after `n` transfer steps: under the hypotheses of `aperture_does_not_weaken` and
for any `n : ℕ`, `‖P ((opT D ^ n) x)‖ ≤ r ^ n * ‖x‖`. The proof is the same chain with
`GapToOperator.norm_opT_pow_le` in place of `norm_opT_le_of_orth`.

Scope: the statement contains one `P`, applied once after the `n` steps. It is not a bound on
`(P ∘ opT) ^ n`, which would require `P (opT x)` to stay orthogonal to the vacuum at each stage.

DERIVED: `0` is the lower bound on `r` and the value of the vacuum inner product; `1` is the bound
on `‖P‖`. `n` is the caller's step count, appearing as both the operator power and the exponent of
`r`. -/
theorem aperture_does_not_weaken_pow (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (P : H D.toReflForm →L[ℂ] H D.toReflForm) (hP : ‖P‖ ≤ 1) (n : ℕ)
    (x : H D.toReflForm) (hx : inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ)) :
    ‖P ((opT D ^ n) x)‖ ≤ r ^ n * ‖x‖ := by
  have h1 : ‖P ((opT D ^ n) x)‖ ≤ ‖P‖ * ‖(opT D ^ n) x‖ := P.le_opNorm _
  have h2 : ‖P‖ * ‖(opT D ^ n) x‖ ≤ 1 * ‖(opT D ^ n) x‖ :=
    mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  have h3 : ‖(opT D ^ n) x‖ ≤ r ^ n * ‖x‖ := norm_opT_pow_le D hr hg n x hx
  calc ‖P ((opT D ^ n) x)‖ ≤ ‖P‖ * ‖(opT D ^ n) x‖ := h1
    _ ≤ 1 * ‖(opT D ^ n) x‖ := h2
    _ = ‖(opT D ^ n) x‖ := one_mul _
    _ ≤ r ^ n * ‖x‖ := h3

#print axioms aperture_does_not_weaken_pow

/-- The indexed form. For `D : ι → TransferData A`, `0 ≤ r`, `hg : ∀ F, GapAt (D F) r`, an index
`F`, a contraction `P` on `H (D F).toReflForm`, a step count `n` and a vector `x` orthogonal to the
vacuum, `‖P ((opT (D F) ^ n) x)‖ ≤ r ^ n * ‖x‖`. Directly
`aperture_does_not_weaken_pow (D F) hr (hg F) P hP n x hx`.

Scope: `hg` is used only at the single index `F`, so the hypothesis could be weakened to that
index; the family quantifier carries no extra content in this statement. The implication runs one
way — a bound on `P` composed with the iterate is not claimed to give a bound on the iterate.

DERIVED: `0` is the lower bound on `r` and the value of the vacuum inner product; `1` is the bound
on `‖P‖`; `n` is the step count. All are inherited from
`aperture_does_not_weaken_pow`. -/
theorem unapertured_suffices {ι : Type*} (D : ι → TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ F, GapAt (D F) r) (F : ι)
    (P : H (D F).toReflForm →L[ℂ] H (D F).toReflForm) (hP : ‖P‖ ≤ 1) (n : ℕ)
    (x : H (D F).toReflForm)
    (hx : inner ℂ (Omega (D F).toReflForm (D F).vac) x = (0 : ℂ)) :
    ‖P ((opT (D F) ^ n) x)‖ ≤ r ^ n * ‖x‖ :=
  aperture_does_not_weaken_pow (D F) hr (hg F) P hP n x hx

#print axioms unapertured_suffices

/-! ## The uniform ceiling, as a proposition -/

/-- The proposition `∀ F, GapAt (D F) ((3 : ℝ) ^ (-(1 : ℝ) / 4))`: the connected radius of every
member of the family `D : ι → TransferData A` is bounded by the single-cell ceiling, with one rate
shared across all indices. A `def` returning a `Prop`; it asserts nothing on its own and is
consumed as a hypothesis by `forgets_at_the_floor_of_B2`.

By `GNSCompare.gapAt_iff_opT_contracts` it can equivalently be read as
`‖opT (D F)‖ ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)` on each vacuum complement.

Scope: `A` is a single fixed algebra across the family, so carriers varying with the geometry, such
as `OSPositivity.wilsonSlabTransfer`'s `↥(localObs (blkS τ a m) (blkR τ a m))`, do not instantiate
this signature.

DERIVED: the ceiling is `(3 : ℝ) ^ (-(1 : ℝ) / 4)`. The `3` is the base of the entropy floor
`κ₀ = (1 / 4) * log 3`; the `1` and the `4` are that floor's coefficient `1 / 4` carried into the
exponent, negated because the ceiling is `exp (-κ₀)` — the identity
`VolumeRate.cell_ceiling_eq_exp_neg_floor`. No numeral is chosen here. -/
def ConnectedRadiusAtCellCeiling {ι : Type*} (D : ι → TransferData A) : Prop :=
  ∀ F, GapAt (D F) ((3 : ℝ) ^ (-(1 : ℝ) / 4))

#print axioms ConnectedRadiusAtCellCeiling

/-- The ceiling rewritten as an exponential rate. From `hB2 : ConnectedRadiusAtCellCeiling D`, for
every index `F`, every `n : ℕ` and every `x` with `inner ℂ (Omega (D F).toReflForm (D F).vac) x = 0`,

    ‖(opT (D F) ^ n) x‖ ≤ Real.exp (-(MassGap.κ₀YM * n)) * ‖x‖.

The proof applies `GapToOperator.norm_opT_pow_le` at the ceiling, then rewrites
`(3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM)` by `VolumeRate.cell_ceiling_eq_exp_neg_floor` and
pulls the power `n` into the exponent with `Real.exp_nat_mul`.

Scope: a norm bound on the iterate at each fixed `n`, not a limit statement, and stated on the
vacuum complement only. `hB2` is a hypothesis, used at the single index `F`. The correlation form of
the same content is `GapToOperator.clustering_opT_general`, a separate declaration.

DERIVED: the one numeral in the statement is `0`, the value of the inner product expressing
orthogonality to the vacuum. The rate is the named constant `MassGap.κ₀YM`; the `3`, `1` and `4` of
the ceiling occur only in the proof, where the rewrite to `exp (-κ₀YM)` happens. -/
theorem forgets_at_the_floor_of_B2 {ι : Type*} (D : ι → TransferData A)
    (hB2 : ConnectedRadiusAtCellCeiling D) :
    ∀ (F : ι) (n : ℕ) (x : H (D F).toReflForm),
      inner ℂ (Omega (D F).toReflForm (D F).vac) x = (0 : ℂ) →
        ‖(opT (D F) ^ n) x‖ ≤ Real.exp (-(MassGap.κ₀YM * n)) * ‖x‖ := by
  intro F n x hx
  have hpow := MassGap.GapToOperator.norm_opT_pow_le (D F)
    (by positivity) (hB2 F) n x hx
  have hceil : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = Real.exp (-MassGap.κ₀YM) :=
    MassGap.VolumeRate.cell_ceiling_eq_exp_neg_floor
  have hexp : Real.exp (-(MassGap.κ₀YM * n)) = ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ n := by
    rw [hceil, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  exact hpow

#print axioms forgets_at_the_floor_of_B2

end MassGap.B2Locality
