import Mathlib
import MassGap.GapToOperator
import MassGap.VolumeRate

/-!
# MassGap.B2Locality — the aperture comes off the obligation

## What B2 is

The step between "one plaquette is gapped" and "the lattice is gapped at the same rate" has a name.
In operator terms it is

    ∀ F, TransferGap.GapAt (D F) (3 ^ (-(1:ℝ)/4))

— the connected radius at every volume bounded by the SINGLE-CELL ceiling `m_cell = e^{-κ₀}`. It is
`GapToOperator.forgets_at_one_rate`'s `hg` at that radius, and **no declaration in this tree
concludes it.**

**⚠ IT IS NOT THE SAME PROPOSITION AS THE MODE-FAMILY OBLIGATIONS**, though it shares their numeral.
`Certify.gap_uniform_in_volume_of_intensive`'s `hbound` is `∀ F, μ₁ F ≤ r` and
`CellSpectrum.gap_uniform_of_cell_intensive`'s `hint` is `∀ F, mHi F ≤ 3^{-1/4}`, both bounds on an
abstract sequence `ℕ → ℝ`; `GapAt` is a contraction of the FORM on a `TransferData`. They are
analogues, and nothing in the tree relates them. `CellSpectrum` does say of its own input what is
said here: the physical statement is OPEN.

The argument for B2 has three parts, in order: the transfer operator is a positive self-adjoint
contraction; the claim that adding cells cannot raise the top CONNECTED eigenvalue above the local
one, which is the whole content and is nowhere argued; and a read, which keeps only the modes it
resolves and cannot enlarge what it is applied to.

**⛔ AND PART ONE IS NOT SIMPLY "HAD", WHICH IS WORTH SAYING BECAUSE IT READS THAT WAY.**
Self-adjointness and contractivity are `TransferData`'s STRUCTURE FIELDS `T_symm` and `T_contract`,
so they hold by construction rather than as consequences of reflection positivity. POSITIVITY is a
separate and OPEN condition: `GNSHilbert.PositiveTransfer` has exactly two producers,
`positiveTransfer_of_T_eq_id` (which needs `T = id`) and `positiveTransfer_of_gram` (which needs a
linear Gram factorisation of the form), and neither is available for a genuine transfer. As
`GNSHilbert` puts it, positivity is reflection positivity about a HALF-INTEGER time plane — a second
application of the same physics, not a corollary of the first.

## What this module does, and how little

It discharges the THIRD part, which is the easy one: `aperture_does_not_weaken` — any contraction
applied after the transfer step inherits the bound, so a read cannot spoil it. The read is not where
the difficulty is.

**⚠ AND THE TREE DOES NOT MODEL A READ THIS WAY.** No other declaration applies a bounded operator
after a transfer operator; the aperture apparatus elsewhere is a finite MODE SUM (`Aperture`), and
"resolved modes" there is an index count on correlation eigenvalues, not the range of a projection.
So `P` here is connected to nothing else in the tree, and the three-part decomposition this module
discharges a part of lives in this header and in
`_archive/2026-08-25-pre-convention/PATH1-STEPB-STRATEGY.md` — not in the Lean.

Stated for an arbitrary `‖P‖ ≤ 1` rather than an orthogonal projection, because that is all the
inequality uses. The generality costs the interpretation: with no projection there is no resolved
subspace, and the theorem never applies `P` to its input.

## ⛔ What is left, and four routes that are closed

What remains is the MIDDLE part. Four ways to it are obstructed, and the obstructions differ in
strength — which matters, because two of them are theorems and two are not:

* **operator-norm perturbation off the decoupled product** — THEOREM, conditionally.
  `CellCouple.coupling_form_extensive` gives `(s.card) * a ≤ δ` **given one vector that lowers every
  bond's form by at least `a`**, and `form_perturbation_reaches_finitely_many` then bounds the reach.
  Where such a common extremal vector exists the growth is real and not an artifact of the triangle
  inequality; `CellCouple`'s own header characterises when it does.
* **this tree's cluster expansion** — THEOREM. `SpectralBound.expansion_domain_bounded` proves
  `∃ B > 0, ∀ β ≥ B, 1 < coreRate (16*4) β`: the convergence condition is false on a half-line.
* **Doeblin / Dobrushin minorisation** — PARTIAL. `SpectralBound.doeblin_exceeds_lambdaThreshold`
  gives `∃ L₀, ∀ L ≥ L₀, lambdaThreshold < doeblinFloor b L`, a statement in `L`. Its own docstring
  records that **THAT the link count grows with the volume is not proved there**, since `L` enters as
  `Fintype.card` of an arbitrary finite index. The route fails in `L`; the step from `L` to the
  volume is assumed.
* **Knabe / Gosset–Mozgunov local-gap criteria** — BLOCKED BY A TYPE MISMATCH, readable off the
  signature. `LocalGap.knabe_chain_gap` carries `hproj : ∀ b, h b * h b = h b`: every bond term must
  be IDEMPOTENT, a projector. `Transfer.Tq` is a positive self-adjoint CONTRACTION on a GNS quotient
  and is not presented as a sum of projectors anywhere, so the criterion has nothing to consume.
  `LocalGap.laplace_no_uniform_gap` is NOT evidence for this — it is the control for the THRESHOLD
  (its docstring: a chain meeting every structural hypothesis but sitting below the threshold has no
  volume-independent gap), and its control chain is itself frustration-free
  (`LocalGap.laplace_ground_state`). **That Kogut–Susskind is frustrated at finite coupling is stated
  nowhere in this tree as a theorem**, so the frustration reading is a citation to the physics
  literature, not to this development.

What survives is a clustering argument on the vacuum complement that does NOT pass through a
per-bond norm estimate. `CellCouple`'s header reaches the same conclusion from the other side.

**And the decoupled case is proved in the OTHER apparatus** — `CellSpectrum.product_volume_gap`
concludes `∃ κ > 0, ∀ F, Tendsto … (nhds 0)` for an abstract mode family, from the single-cell
ceiling as a HYPOTHESIS. It concludes no `GapAt`, so it is the decoupled case of the mode-magnitude
obligation and not of B2 as stated above. The correction to the product remains the open content
either way.

Nothing here produces a gap.
-/

namespace MassGap.B2Locality

open MassGap.GNSHilbert MassGap.TransferGap MassGap.Transfer MassGap.GapToOperator

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **⭐ A READ CANNOT WEAKEN THE BOUND.** Any contraction applied after the transfer step inherits
the vacuum-complement bound, so the obligation about the modes a read RESOLVES follows from the
obligation about the whole complement.

This is the third of B2's three parts, and discharging it is what takes the aperture out of the open
statement: whatever the read keeps, it is bounded by what the operator does. Stated for an arbitrary
`‖P‖ ≤ 1` because that is all the argument uses.

DERIVED: the `1` is the contraction constant of a read, which is a projection; `r` is `GapAt`'s. -/
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

/-- **ONE READ, AFTER `n` STEPS.** `n` transfer steps followed by a single read are bounded by `rⁿ`.

**⛔ THIS IS NOT A READ AT EVERY STEP.** The statement contains ONE `P`, applied once at the end.
Reading at every step is `(P ∘ opT)^n`, which does not appear here and does not follow: iterating
needs `P (opT x) ⊥ Ω` at each stage, hence `P Ω = Ω` — that the read resolves the vacuum — which is
an extra hypothesis nothing here states.

DERIVED: `n` is the caller's step count; the `1` is the read's contraction constant. -/
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

/-- **⛔ THE REDUCTION, STATED AS THE OBLIGATION IT LEAVES.** If the vacuum-complement bound holds at
every index with one `r`, then so does every read of it. So B2's content is the UNAPERTURED
statement, and an attempt may ignore the read entirely.

The converse is not claimed and is not true in general: a read can hide a mode it does not resolve,
which is why the obligation is stated on the complement and not on the read.

**⚠ The index family is decorative.** `D` is used only as `D F` and `hg` only as `hg F`, so this is
`aperture_does_not_weaken_pow` at one index with a wrapper.

DERIVED: no numeral of its own. -/
theorem unapertured_suffices {ι : Type*} (D : ι → TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ F, GapAt (D F) r) (F : ι)
    (P : H (D F).toReflForm →L[ℂ] H (D F).toReflForm) (hP : ‖P‖ ≤ 1) (n : ℕ)
    (x : H (D F).toReflForm)
    (hx : inner ℂ (Omega (D F).toReflForm (D F).vac) x = (0 : ℂ)) :
    ‖P ((opT (D F) ^ n) x)‖ ≤ r ^ n * ‖x‖ :=
  aperture_does_not_weaken_pow (D F) hr (hg F) P hP n x hx

#print axioms unapertured_suffices

/-! ## ⭐ B2, as a statement -/

/-- **⭐ B2.** The connected radius is bounded by the SINGLE-CELL ceiling `m_cell = 3^{-1/4}`, at
every index at once.

This is the open step, typed. It is `Certify.gap_uniform_in_volume_of_intensive`'s `hbound`,
`CellSpectrum.gap_uniform_of_cell_intensive`'s `hint` and `GapToOperator.forgets_at_one_rate`'s `hg`
at the ceiling, and the archived form `connected_radius_le_cell : ∀ F, m_hi_phys F ≤ m_cell`.
**Nothing in this tree concludes it.**

By `GNSCompare.gapAt_iff_opT_contracts` it may equally be read as `‖opT (D F)‖ ≤ 3^{-1/4}` on each
vacuum complement, which is the form a SPECTRAL argument would deliver — and every certificate that
could discharge it is spectral.

**⛔ AND THE TREE'S WILSON TRANSFER DATA CANNOT BE SUBSTITUTED HERE.** `D : ι → TransferData A`
ranges over one FIXED algebra `A`, while `OSPositivity.wilsonSlabTransfer` has a carrier
`↥(localObs (blkS τ a m) (blkR τ a m))` that varies with the slab geometry. So this types the SHAPE of
B2, not B2 at a genuine volume family — the same limitation `GapToOperator.forgets_at_one_rate`
records about itself. The archived form is `connected_radius_le_cell : ∀ F, m_hi_phys F ≤ m_cell` in
`_archive/2026-08-25-pre-convention/PATH1-STEPB-STRATEGY.md`, which is prose and not Lean.

DERIVED: `3^{-1/4} = e^{-κ₀}` is the single-cell ceiling
(`VolumeRate.cell_ceiling_eq_exp_neg_floor`), from the certified `E₁ - E₀ ≥ κ₀ = ¼ log 3`. Nothing is
chosen here. -/
def ConnectedRadiusAtCellCeiling {ι : Type*} (D : ι → TransferData A) : Prop :=
  ∀ F, GapAt (D F) ((3 : ℝ) ^ (-(1 : ℝ) / 4))

#print axioms ConnectedRadiusAtCellCeiling

/-- **⭐ AND WHAT B2 BUYS: the rate is the entropy floor, exactly.** Under B2 the NORM of an iterate
on the vacuum complement is bounded by `e^{-κ₀ n}‖x‖` — a bound, not a limit — with `κ₀ = ¼ log 3`,
the surface entropy density `VortexCount.kappa0_is_the_surface_entropy_density` computes. The
CORRELATION form is `GapToOperator.clustering_opT_general`, a separate step.

**⚠ The index family is decorative** here too: `hB2` is used only as `hB2 F`.

So the mass gap delivered by B2 IS the entropy floor, on the genuine completed operator, with no
spectrum, no logarithm of an operator and no invertibility anywhere in the route.

**⚠ B2 is a hypothesis here and is supplied nowhere.** This spends it.

DERIVED: `κ₀ = ¼ log 3` is `Complete.κ₀YM`; the ceiling is `e^{-κ₀}`. No numeral is chosen. -/
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
