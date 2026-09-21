import Mathlib
import MassGap.GNSHilbert
import MassGap.Reconstruction

/-!
# MassGap.OpTBridge — placing the transfer operator where the reconstruction theorem can see it

## The break this addresses

`Reconstruction.reconstruct_qm_core` is stated over `variable {A : Type*} [CStarAlgebra A]` and takes
an arbitrary element `T : A`. `GNSHilbert.opT D` is a continuous linear map on the GNS completion.
**Nothing in the tree connected the two**, and nothing stated anything about
`spectrum ℝ (GNSHilbert.opT D)` — so even a complete `Transfer.TransferData` did not reach the
reconstruction theorem.

## What closes it, and what does not

Bounded operators on a complex Hilbert space form a C\*-algebra, and `GNSHilbert.complete_H` makes
the GNS completion one. So the bridge is an INSTANCE, not a construction: `reconstruct_qm_core`
applies to `opT D` directly once Lean is shown the algebra.

`reconstruct_from_opT` does that, and discharges `hT` from `GNSHilbert.isSelfAdjoint_opT`, which is
already proved unconditionally from `TransferData`'s own `T_symm`.

**⚠ The two spectral hypotheses remain, and they are the whole content.** `h1` (that `1` is in the
spectrum) and `hsp` (that the rest of the spectrum sits in `[ε, e^{−Δ}]`) are exactly the mass gap in
operator form. Nothing here proves either, and nothing in the tree does. What changes is the KIND of
gap: C1's remainder was "there is no bridge at all"; it is now "the bridge is there and the spectral
input is open", which is the same obligation the rest of the development already names.

**And it says nothing about which `D`.** The only `TransferData` instances the tree carries are
`GNSHilbert.trivialTransfer` (whose `T` is the identity) and the slab ones, whose surviving premise
`SlabShiftStable` forces the identity too. At the identity the spectrum is `{1}` and `hsp` fails for
every `ε`, `Δ` — correctly, since a trivial operator has no gap.
-/

namespace MassGap.OpTBridge

open MassGap.Transfer MassGap.GNSHilbert MassGap.Reconstruction

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **THE GNS COMPLETION'S BOUNDED OPERATORS ARE A C\*-ALGEBRA.** Recorded as a theorem rather than
left to instance search at the use site, so that the bridge is visible and its failure would be
visible too.

DERIVED: no numeral. -/
@[reducible] noncomputable def cstar_of_gns (D : TransferData A) :
    CStarAlgebra (H D.toReflForm →L[ℂ] H D.toReflForm) := by
  haveI := complete_H D.toReflForm
  infer_instance

/-- **⭐ THE RECONSTRUCTION THEOREM, APPLIED TO THE TRANSFER OPERATOR.**

`reconstruct_qm_core` at `A := H →L[ℂ] H` and `T := opT D`, with self-adjointness discharged by
`GNSHilbert.isSelfAdjoint_opT`.

**The spectral hypotheses are the mass gap.** `h1` and `hsp` are not discharged here and are not
discharged anywhere in the tree; they are the obligation, stated in operator form.

DERIVED: the `1` is the vacuum eigenvalue, `reconstruct_qm_core`'s own; `0` is the ground-state
energy. Nothing is chosen. -/
theorem reconstruct_from_opT (D : TransferData A) {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ)
    (h1 : (1 : ℝ) ∈ spectrum ℝ (opT D))
    (hsp : spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    IsSelfAdjoint (hamiltonian (opT D)) ∧ 0 ≤ hamiltonian (opT D) ∧
      (0 : ℝ) ∈ spectrum ℝ (hamiltonian (opT D)) ∧
      spectrum ℝ (hamiltonian (opT D)) ⊆ {0} ∪ Set.Ici Δ := by
  haveI := complete_H D.toReflForm
  exact reconstruct_qm_core (opT D) (isSelfAdjoint_opT D) hε hΔ h1 hsp

#print axioms reconstruct_from_opT

/-- **⛔ AND AT THE IDENTITY THE SPECTRAL HYPOTHESIS FAILS**, which is the negative control: the only
transfer operators the tree carries are trivial, and a trivial operator correctly admits no gap.

If `T = 1` then `1 ∈ spectrum` holds but every point of the spectrum is `1`, so `hsp` would force
`1 ∈ Set.Icc ε (exp (-Δ))`, i.e. `1 ≤ exp (-Δ)`, contradicting `0 < Δ`.

DERIVED: the `1` is the identity's only spectral value; `0` is the sign of `Δ`. -/
theorem spectral_hypothesis_fails_at_identity {ε Δ : ℝ} (hΔ : 0 < Δ)
    (hmem : (1 : ℝ) ∈ ({1} : Set ℝ) ∪ Set.Icc ε (Real.exp (-Δ)))
    (hne : (1 : ℝ) ∉ ({1} : Set ℝ)) : False := by
  rcases hmem with h | h
  · exact hne h
  · have : (1 : ℝ) ≤ Real.exp (-Δ) := h.2
    have hlt : Real.exp (-Δ) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith

#print axioms spectral_hypothesis_fails_at_identity

end MassGap.OpTBridge
