import Mathlib
import MassGap.GNSHilbert

/-!
# MassGap.GNSCompare — the two Hilbert spaces built from one `TransferData`, related

## ⛔ The defect this addresses

`Transfer.TransferData` gives rise to TWO Hilbert-space constructions in this tree, and until now
nothing connected them:

* the **real quotient** `Transfer.GNS P = A ⧸ P.nullSpace`, with step map `Tq` and `TqL`, which
  `VolumeRate`, `SecondEigenvalue`, `PeriodicRayleigh` and `HalfLineTransfer` consume;
* the **complex completion** `GNSHilbert.H P = Completion (Pre P)`, with `opT`, which `OpTBridge`
  and `GapToOperator` consume.

Each carries its own copy of the vacuum-complement decay law. **They are not literally the same
statement**: `VolumeRate.norm_Tq_pow_le` ASSUMES the per-step operator bound on its own space and
supplies only the induction, while `GapToOperator.norm_opT_pow_le` assumes `TransferGap.GapAt`, a
statement about the form on `A`, and does the density extension to reach the per-step bound.
Deleting one copy therefore needs `GapAt D r` to imply the other's hypothesis as well — short, from
`inner_mk` and `norm_mk_mul_norm_mk`, and unproved.

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

## ⚠ What this does NOT do

It does not bundle the map as a `LinearIsometry`. **The blocker is not the `ℝ`-module structure on
`H P`** — the `H → GNS` direction needs none of that: `Transfer.GNS.exists_mk` makes every class an
`mk x`, `inner_coe_ofPair` with `toH_vac` makes the two orthogonality hypotheses interchangeable,
`norm_coe_ofPair` matches the norms, and what is missing is only the two POWER inductions, since
this module states the step maps at `n = 1` alone.

**And `toH` duplicates `GNSHilbert.Omega`'s body character for character** — `toH_vac` is `rfl`,
which is the proof. So a module about removing duplication adds a third name for one map.
`opT_coe_ofPair` generalises `GNSHilbert.opT_Omega` and `norm_coe_ofPair` generalises
`GNSHilbert.norm_Omega`; neither is rederived from the new one.

Nothing here produces a gap, and nothing here consumes one.
-/

namespace MassGap.GNSCompare

open MassGap.GNSHilbert MassGap.Transfer

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
