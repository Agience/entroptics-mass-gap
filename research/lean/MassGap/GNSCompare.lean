import Mathlib
import MassGap.GNSHilbert
import MassGap.GapToOperator
import MassGap.VolumeRate
import MassGap.SecondEigenvalue

/-!
# MassGap.GNSCompare — the two Hilbert spaces built from one `TransferData`, related

## ⛔ The defect this addresses

`Transfer.TransferData` gives rise to TWO Hilbert-space constructions in this tree, and until now
nothing connected them:

* the **real quotient** `Transfer.GNS P = A ⧸ P.nullSpace`, with step map `Tq` and `TqL`, which
  `VolumeRate`, `SecondEigenvalue`, `PeriodicRayleigh` and `HalfLineTransfer` consume;
* the **complex completion** `GNSHilbert.H P = Completion (Pre P)`, with `opT`, which `OpTBridge`
  and `GapToOperator` consume.

Each carried its own copy of the vacuum-complement decay law. **They are not literally the same
statement**: `VolumeRate.norm_Tq_pow_le` ASSUMES the per-step operator bound on its own space and
supplies only the induction, while `GapToOperator.norm_opT_pow_le` assumes `TransferGap.GapAt`, a
statement about the form on `A`, and does the density extension to reach the per-step bound.

That hypothesis was ALREADY dischargeable — `SecondEigenvalue.norm_Tq_le_of_rayleigh` and
`Tq_pow_norm_le_of_rayleigh` supply it from a Rayleigh-quotient premise. What was missing was the
route from `GapAt`, and `tq_contracts_of_gapAt` supplies that; `norm_Tq_pow_le_of_gapAt` then gets
the quotient-side iterate from `GapAt` alone. So the two decay laws are now connected, by a second
route rather than a first.

## What is established

The real observable `x : A` reaches the completion as `↑(Pre.ofPair P x 0)`, the class with `x` in
the real component and `0` in the imaginary one. Along that map:

* `norm_coe_ofPair` — the norm agrees with `‖GNS.mk P x‖`. Both squares are `P.form x x`.
* `inner_coe_ofPair` — the complex pairing of two such classes is the real form, with zero
  imaginary part. So the embedding is isometric AND preserves the inner product, not merely the
  norm.
* `opT_coe_ofPair` — `opT` acts as `D.T` does, so it intertwines with `Tq` through `Transfer.Tq_mk`.
* `coe_ofPair_eq_zero_iff` — the map kills exactly the null space, which is what `GNS`'s quotient
  divides by. So the two constructions agree on the real component **and nothing is lost**.

## ⭐ And the gap crosses in BOTH directions

`gapAt_iff_opT_contracts`: `TransferGap.GapAt D r` holds exactly when `opT D` contracts the vacuum's
complement by `r`. Forward is `GapToOperator.norm_opT_le_of_orth` and needs the density argument;
backward is `gapAt_of_opT_contracts` and is the direction **B2 needs** — `GapAt` is a statement about
the FORM, while every certificate that could discharge it (`CellCover.cell_gap_on_range` and its
relatives) is SPECTRAL. Without the backward direction a spectral bound could not be handed to the
chain at all; with it, B5 may be stated, attacked and discharged on whichever side suits.

## ⚠ What this does NOT do

It does not bundle the map as a `LinearIsometry`, and it does not need to for the transfers above.
**The blocker was never the `ℝ`-module structure on `H P`** — the crossings here use
`Transfer.GNS.exists_mk`, `inner_mk`, `norm_mk_mul_norm_mk` and this module's own three lemmas, and
no restriction of scalars anywhere.

**And `toH` duplicates `GNSHilbert.Omega`'s body character for character** — `toH_vac` is `rfl`,
which is the proof. So a module about removing duplication adds a third name for one map.
`opT_coe_ofPair` generalises `GNSHilbert.opT_Omega` and `norm_coe_ofPair` generalises
`GNSHilbert.norm_Omega`; neither is rederived from the new one.

Nothing here produces a gap, and nothing here consumes one.
-/

namespace MassGap.GNSCompare

open MassGap.GNSHilbert MassGap.Transfer MassGap.TransferGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **THE REAL OBSERVABLE, IN THE COMPLEX COMPLETION.** `x` in the real component, `0` in the
imaginary one.

**This IS `GNSHilbert.Omega`**, whose definition already takes an arbitrary `v : A` and is only
NAMED for the vacuum. Defined through it rather than beside it, so the tree carries one map and not
two; the alias exists because `Omega` reads wrongly when the argument is not the vacuum.

DERIVED: the `0` is the imaginary component of a real observable, and it is `Omega`s. -/
noncomputable def toH (P : ReflForm A) (x : A) : H P := Omega P x

/-- The unfolded form, for rewriting: the class of the pair `(x, 0)`. -/
theorem toH_def (P : ReflForm A) (x : A) :
    toH P x = ((Pre.ofPair P x 0 : Pre P) : H P) := rfl

/-- **THE PAIRING IS THE REAL FORM**, with nothing in the imaginary part: the cross terms both carry
a `0` component.

DERIVED: no numeral of its own. -/
@[simp] theorem inner_coe_ofPair (P : ReflForm A) (x y : A) :
    inner ℂ (toH P x) (toH P y) = ((P.form x y : ℝ) : ℂ) := by
  rw [toH_def, toH_def, inner_coe]
  simp [MassGap.OSPositivity.cform, Transfer.PreForm.form_zero_left,
    Transfer.PreForm.form_zero_right]

/-- **⭐ THE NORM AGREES WITH THE REAL GNS NORM.** Both squares are `P.form x x`, so the embedding is
isometric onto its image.

DERIVED: no numeral of its own. -/
theorem norm_coe_ofPair (P : ReflForm A) (x : A) :
    ‖toH P x‖ = ‖GNS.mk P x‖ := by
  have h1 : ‖toH P x‖ * ‖toH P x‖ = P.form x x := by
    rw [toH_def, UniformSpace.Completion.norm_coe, Pre.norm_mul_norm]
    simp [Transfer.PreForm.form_zero_left]
  have h2 : ‖GNS.mk P x‖ * ‖GNS.mk P x‖ = P.form x x := GNS.norm_mk_mul_norm_mk x
  nlinarith [norm_nonneg (toH P x), norm_nonneg (GNS.mk P x)]

/-- **AND IT KILLS EXACTLY THE NULL SPACE** — the submodule `GNS` quotients by. So passing to the
completion loses no more and no less than passing to the quotient.

DERIVED: the `0`s are the zero vector and the form's value on the null space. -/
theorem coe_ofPair_eq_zero_iff (P : ReflForm A) (x : A) :
    toH P x = 0 ↔ P.form x x = 0 := by
  constructor
  · intro h
    have hn : ‖toH P x‖ = 0 := by rw [h, norm_zero]
    have := norm_coe_ofPair P x
    rw [hn] at this
    have h2 : ‖GNS.mk P x‖ * ‖GNS.mk P x‖ = P.form x x := GNS.norm_mk_mul_norm_mk x
    rw [← this] at h2
    simpa using h2.symm
  · intro h
    have hn : ‖toH P x‖ * ‖toH P x‖ = P.form x x := by
      rw [toH_def, UniformSpace.Completion.norm_coe, Pre.norm_mul_norm]
      simp [Transfer.PreForm.form_zero_left]
    rw [h] at hn
    have : ‖toH P x‖ = 0 := by nlinarith [norm_nonneg (toH P x)]
    exact norm_eq_zero.mp this

/-- **⭐ AND `opT` ACTS AS `D.T` DOES.** With `Transfer.Tq_mk`, this is the intertwining: the two
step maps are the same map read on the two constructions.

DERIVED: the `0` is the imaginary component, preserved because `D.T` is linear. -/
@[simp] theorem opT_coe_ofPair (D : TransferData A) (x : A) :
    opT D (toH D.toReflForm x) = toH D.toReflForm (D.T x) := by
  rw [toH_def, opT_coe, cTL_apply]
  congr 1
  refine Pre.ext ?_ ?_
  · rw [cT_fst]; simp [Pre.ofPair]
  · rw [cT_snd]; simp [Pre.ofPair, map_zero]

/-- The intertwining, with both step maps named. `Tq` moves the class in the quotient, `opT` moves
the class in the completion, and the embedding carries one to the other.

DERIVED: no numeral. -/
theorem intertwines (D : TransferData A) (x : A) :
    opT D (toH D.toReflForm x) = toH D.toReflForm (D.T x) ∧
      D.Tq (GNS.mk D.toReflForm x) = GNS.mk D.toReflForm (D.T x) :=
  ⟨opT_coe_ofPair D x, D.Tq_mk x⟩

/-- The vacuum of the completion is the embedding of the vacuum of `A`. -/
theorem toH_vac (D : TransferData A) :
    toH D.toReflForm D.vac = Omega D.toReflForm D.vac := rfl

/-! ## ⭐ Crossing back: an operator bound supplies `GapAt` -/

/-- The embedded observable's norm squares to the form. Extracted from `norm_coe_ofPair`'s proof so
the crossing below can use it directly.

DERIVED: no numeral of its own. -/
theorem norm_toH_mul_norm_toH (P : ReflForm A) (x : A) :
    ‖toH P x‖ * ‖toH P x‖ = P.form x x := by
  rw [toH_def, UniformSpace.Completion.norm_coe, Pre.norm_mul_norm]
  simp [Transfer.PreForm.form_zero_left]

#print axioms norm_toH_mul_norm_toH

/-- **PAIRING WITH THE VACUUM IS THE FORM AGAINST THE VACUUM.** So the completion's orthogonality
condition and `TransferGap.GapAt`'s are the same condition, written on the two sides.

DERIVED: the `0`s are the two orthogonality conditions, not levels. -/
theorem inner_vac_toH_eq_zero_iff (P : ReflForm A) (v x : A) :
    inner ℂ (Omega P v) (toH P x) = (0 : ℂ) ↔ P.form x v = 0 := by
  have h : inner ℂ (Omega P v) (toH P x) = ((P.form v x : ℝ) : ℂ) := inner_coe_ofPair P v x
  rw [h, P.form_symm v x]
  constructor
  · intro hz; exact_mod_cast hz
  · intro hz; exact_mod_cast congrArg (fun y : ℝ => (y : ℂ)) hz

#print axioms inner_vac_toH_eq_zero_iff

/-- **⭐ AN OPERATOR BOUND ON THE COMPLETION SUPPLIES `GapAt`.** The converse of
`GapToOperator.norm_opT_le_of_orth`, and the direction B2 needs.

`TransferGap.GapAt` is a statement about the FORM on `A`; the certificates that could discharge it
— `CellCover.cell_gap_on_range` and the rest — are SPECTRAL, about eigenvalues of an operator.
Without this direction a spectral bound could not be handed to the chain at all. With it, anyone who
bounds `opT` on the vacuum's complement has produced `GapAt`.

Three steps, each already here: the embedded observable is vacuum-orthogonal exactly when the
observable is (`inner_vac_toH_eq_zero_iff`), `opT` moves it as `D.T` does (`opT_coe_ofPair`), and
its norm squares to the form (`norm_toH_mul_norm_toH`).

DERIVED: the `2` is the form's degree, as in `GapAt`; `r` is the caller's. -/
theorem gapAt_of_opT_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : H D.toReflForm, inner ℂ (Omega D.toReflForm D.vac) y = (0 : ℂ) →
      ‖opT D y‖ ≤ r * ‖y‖) :
    GapAt D r := by
  intro x hx
  have hperp : inner ℂ (Omega D.toReflForm D.vac) (toH D.toReflForm x) = (0 : ℂ) :=
    (inner_vac_toH_eq_zero_iff D.toReflForm D.vac x).2 hx
  have hb := h (toH D.toReflForm x) hperp
  rw [opT_coe_ofPair] at hb
  have hTx : ‖toH D.toReflForm (D.T x)‖ * ‖toH D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := norm_toH_mul_norm_toH D.toReflForm (D.T x)
  have hxx : ‖toH D.toReflForm x‖ * ‖toH D.toReflForm x‖ = D.form x x :=
    norm_toH_mul_norm_toH D.toReflForm x
  have hnn : 0 ≤ ‖toH D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖toH D.toReflForm x‖ := norm_nonneg _
  nlinarith [hb, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms gapAt_of_opT_contracts

/-- **SO THE TWO FORMS OF THE GAP ARE EQUIVALENT.** `GapAt` on the form and the contraction bound on
the completion's vacuum complement say the same thing.

The forward direction is `GapToOperator.norm_opT_le_of_orth`, which needs the density argument; the
backward one is above. B5 may therefore be stated, attacked and discharged on whichever side suits,
and a spectral argument is admissible.

DERIVED: no numeral of its own. -/
theorem gapAt_iff_opT_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) :
    GapAt D r ↔ ∀ y : H D.toReflForm,
      inner ℂ (Omega D.toReflForm D.vac) y = (0 : ℂ) → ‖opT D y‖ ≤ r * ‖y‖ :=
  ⟨fun hg y hy => MassGap.GapToOperator.norm_opT_le_of_orth D hr hg y hy,
   gapAt_of_opT_contracts D hr⟩

#print axioms gapAt_iff_opT_contracts

/-! ## ⭐ The same crossing on the real quotient -/

/-- **⭐ `GapAt` GIVES THE QUOTIENT-SIDE STEP BOUND.** `TransferGap.GapAt` is about the form;
`VolumeRate.norm_Tq_pow_le` ASSUMES a bound on `Tq` and supplies only the induction. Nothing derived
the second's hypothesis from the first, which is why the two decay laws stood as independent
developments. This is the derivation.

Every class is an `mk x` (`Transfer.GNS.exists_mk`), orthogonality to the vacuum class is the form
against the vacuum (`inner_mk`), `Tq` moves the class as `D.T` moves the observable (`Tq_mk`), and
the norm squares to the form (`norm_mk_mul_norm_mk`).

DERIVED: the `2` is the form's degree, as in `GapAt`; `r` is the caller's. -/
theorem tq_contracts_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (y : GNS D.toReflForm) (hy : inner ℝ D.vacGNS y = (0 : ℝ)) :
    ‖D.Tq y‖ ≤ r * ‖y‖ := by
  obtain ⟨x, rfl⟩ := GNS.exists_mk y
  have hform : D.form x D.vac = 0 := by
    have h : D.form D.vac x = 0 := by
      simpa [TransferData.vacGNS] using hy
    rw [D.form_symm]
    exact h
  have hgap := hg x hform
  rw [D.Tq_mk]
  have hTx : ‖GNS.mk D.toReflForm (D.T x)‖ * ‖GNS.mk D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := GNS.norm_mk_mul_norm_mk _
  have hxx : ‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖ = D.form x x :=
    GNS.norm_mk_mul_norm_mk _
  have hnn : 0 ≤ ‖GNS.mk D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖GNS.mk D.toReflForm x‖ := norm_nonneg _
  nlinarith [hgap, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms tq_contracts_of_gapAt

/-- **AND SO THE QUOTIENT-SIDE ITERATE FOLLOWS FROM `GapAt` ALONE.**
`VolumeRate.norm_Tq_pow_le` with its hypothesis discharged — the duplication between the two decay
laws is now a derivation rather than two independent developments.

DERIVED: `n` is the caller's step count; `r` is `GapAt`'s. -/
theorem norm_Tq_pow_le_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (y : GNS D.toReflForm) (hy : inner ℝ D.vacGNS y = (0 : ℝ)) (n : ℕ) :
    ‖(D.Tq ^ n) y‖ ≤ r ^ n * ‖y‖ :=
  MassGap.VolumeRate.norm_Tq_pow_le D hr (tq_contracts_of_gapAt D hr hg) hy n

#print axioms norm_Tq_pow_le_of_gapAt

/-! ## ⭐ And back again: a quotient bound supplies `GapAt` -/

/-- **⭐ A `Tq` BOUND SUPPLIES `GapAt`.** The converse of `tq_contracts_of_gapAt`, and the direction
that lets the Rayleigh machinery reach B5.

Every class is an `mk x`, so a bound on `Tq` over the vacuum complement is a bound on the form at
every observable orthogonal to the vacuum — which is `GapAt`.

DERIVED: the `2` is the form's degree, as in `GapAt`; `r` is the caller's. -/
theorem gapAt_of_tq_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ r * ‖y‖) :
    GapAt D r := by
  intro x hx
  have hvx : D.form D.vac x = 0 := by rw [D.form_symm]; exact hx
  have hy : inner ℝ D.vacGNS (GNS.mk D.toReflForm x) = (0 : ℝ) := by
    simpa [TransferData.vacGNS] using hvx
  have hb := h (GNS.mk D.toReflForm x) hy
  rw [D.Tq_mk] at hb
  have hTx : ‖GNS.mk D.toReflForm (D.T x)‖ * ‖GNS.mk D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := GNS.norm_mk_mul_norm_mk _
  have hxx : ‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖ = D.form x x :=
    GNS.norm_mk_mul_norm_mk _
  have hnn : 0 ≤ ‖GNS.mk D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖GNS.mk D.toReflForm x‖ := norm_nonneg _
  nlinarith [hb, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms gapAt_of_tq_contracts

/-- **AND SO THE QUOTIENT FORM OF THE GAP IS EQUIVALENT TOO.**

DERIVED: no numeral of its own. -/
theorem gapAt_iff_tq_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) :
    GapAt D r ↔ ∀ y : GNS D.toReflForm,
      inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ r * ‖y‖ :=
  ⟨tq_contracts_of_gapAt D hr, gapAt_of_tq_contracts D hr⟩

#print axioms gapAt_iff_tq_contracts

/-- **⭐ A RAYLEIGH BOUND PRODUCES `GapAt`.** `SecondEigenvalue.norm_Tq_le_of_rayleigh` turns a
QUADRATIC FORM estimate on the vacuum complement — `⟪Ty, y⟫ ≤ Λ‖y‖²`, with `⟪Ty, y⟫ ≥ 0` — into a
norm bound on `Tq`; `gapAt_of_tq_contracts` carries that to `GapAt`.

**Why this is the useful direction.** Reflection positivity delivers statements about the FORM
`⟪Ty, y⟫`, not about an operator norm, so a Rayleigh estimate is what an argument from RP can
realistically produce. Before this the Rayleigh machinery had nowhere to go: `GapAt` was stated on
the form over `A` and nothing connected the two. Now a bound on the Rayleigh quotient of `Tq` over
the vacuum complement yields `GapAt`, hence — through `GapToOperator.norm_opT_pow_le` — the decay on
the genuine completed operator, and at `Λ = 3^{-1/4}` that is B2.

**⚠ It produces no bound.** `hpos` and `hray` are hypotheses; nothing here supplies them, and
`SecondEigenvalue`'s own header records that the smallest `Λ` any construction in this tree can
report is `√(ρ(2)/ρ(0))`.

DERIVED: `Λ` is the caller's; the `2` is the square in the Rayleigh quotient. -/
theorem gapAt_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    GapAt D Λ :=
  gapAt_of_tq_contracts D hΛ
    (fun _y hy => MassGap.SecondEigenvalue.norm_Tq_le_of_rayleigh D hΛ hpos hray hy)

#print axioms gapAt_of_rayleigh

/-- **`PositiveTransfer` IS THE POSITIVITY THE RAYLEIGH ROUTE ASKS FOR.** `GNSHilbert.PositiveTransfer`
is `∀ x, 0 ≤ form x (T x)`; on a class `mk x` that is exactly `0 ≤ ⟪Tq y, y⟫`, with no orthogonality
needed.

DERIVED: the `0` is positivity itself. -/
theorem inner_Tq_nonneg_of_positiveTransfer (D : TransferData A)
    (hP : MassGap.GNSHilbert.PositiveTransfer D) (y : GNS D.toReflForm) :
    (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ) := by
  obtain ⟨x, rfl⟩ := GNS.exists_mk y
  rw [D.Tq_mk, GNS.inner_mk, D.form_symm]
  exact hP x

#print axioms inner_Tq_nonneg_of_positiveTransfer

/-- **⭐ THE RAYLEIGH ROUTE, AGAINST THE TREE'S OWN POSITIVITY PREDICATE.** `GapAt` from
`PositiveTransfer` plus ONE quadratic-form bound.

This is the shape an argument from reflection positivity can actually aim at: RP supplies positivity
of the transfer operator (`PositiveTransfer`, which `GNSHilbert` records is NOT a consequence of
`TransferData`'s fields and is discharged in this tree only at the identity), and what remains is a
single Rayleigh estimate `⟪Tq y, y⟫ ≤ Λ‖y‖²` on the vacuum complement. At `Λ = 3^{-1/4}` the
conclusion is B2, and `GapToOperator.norm_opT_pow_le` then gives decay at `κ₀` on the genuine
completed operator.

**⚠ Both inputs are open.** Nothing in this tree supplies `PositiveTransfer` for a non-identity
transfer, and `SecondEigenvalue`'s header records that the smallest `Λ` any construction here can
report is `√(ρ(2)/ρ(0))`.

DERIVED: `Λ` is the caller's; the `2` is the square in the Rayleigh quotient. -/
theorem gapAt_of_positiveTransfer_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    GapAt D Λ :=
  gapAt_of_rayleigh D hΛ (fun y _ => inner_Tq_nonneg_of_positiveTransfer D hP y) hray

#print axioms gapAt_of_positiveTransfer_of_rayleigh

/-! ## Footprints -/

section Audit
#print axioms toH
#print axioms toH_def
#print axioms inner_coe_ofPair
#print axioms norm_coe_ofPair
#print axioms coe_ofPair_eq_zero_iff
#print axioms opT_coe_ofPair
#print axioms intertwines
#print axioms toH_vac
end Audit

end MassGap.GNSCompare
