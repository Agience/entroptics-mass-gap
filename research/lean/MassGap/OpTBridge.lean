import Mathlib
import MassGap.GNSHilbert
import MassGap.Reconstruction

/-!
# MassGap.OpTBridge — `Reconstruction.reconstruct_qm_core` applied at `GNSHilbert.opT`

`Reconstruction.reconstruct_qm_core` is stated for an arbitrary element `T` of an abstract
`CStarAlgebra A`. `GNSHilbert.opT D` is a continuous linear endomorphism of the GNS completion
`H D.toReflForm`. Bounded operators on a complex Hilbert space form a C\*-algebra, and
`GNSHilbert.complete_H` supplies the completeness instance, so the application needs no construction
— only that Lean sees the algebra structure.

`cstar_of_gns` records that instance. `reconstruct_from_opT` performs the application, discharging
the self-adjointness hypothesis from `GNSHilbert.isSelfAdjoint_opT` (itself derived from
`TransferData`'s `T_symm`) and leaving the two spectral hypotheses — `1 ∈ spectrum ℝ (opT D)` and
`spectrum ℝ (opT D) ⊆ {1} ∪ [ε, e^{-Δ}]` — as premises on the caller.

`spectral_hypothesis_fails_at_identity` is a real-arithmetic incompatibility: for `0 < Δ`, the value
`1` cannot lie in `Set.Icc ε (Real.exp (-Δ))`, since `Real.exp (-Δ) < 1`.

Scope: `D` ranges over `TransferData A` for `A` an `ℝ`-module; nothing here constructs a `D`, proves
a spectral containment, or says which operators `opT D` can be. With `0 < ε`, the hypothesis `hsp`
of `reconstruct_from_opT` keeps `0` out of `spectrum ℝ (opT D)`, so it applies only to invertible
transfer operators.
-/

namespace MassGap.OpTBridge

open MassGap.Transfer MassGap.GNSHilbert MassGap.Reconstruction

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The C\*-algebra structure on the continuous linear endomorphisms of the GNS completion,
`H D.toReflForm →L[ℂ] H D.toReflForm`, for a `TransferData A`. The body introduces
`GNSHilbert.complete_H D.toReflForm` and then defers to instance search, so this is a named handle on
an instance rather than a construction. Marked `@[reducible]`, so it unfolds during elaboration.

DERIVED: no numeral appears in the statement. -/
@[reducible] noncomputable def cstar_of_gns (D : TransferData A) :
    CStarAlgebra (H D.toReflForm →L[ℂ] H D.toReflForm) := by
  haveI := complete_H D.toReflForm
  infer_instance

/-- `Reconstruction.reconstruct_qm_core` instantiated at `A := H D.toReflForm →L[ℂ] H D.toReflForm`
and `T := opT D`. Given `0 < ε`, `0 < Δ`, `(1 : ℝ) ∈ spectrum ℝ (opT D)` and
`spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))`, it concludes that `hamiltonian (opT D)` is
self-adjoint, is `≥ 0`, has `(0 : ℝ)` in its spectrum, and has spectrum inside
`{0} ∪ Set.Ici Δ`.

Self-adjointness of `opT D` is discharged internally from `GNSHilbert.isSelfAdjoint_opT`; `h1` and
`hsp` are premises the caller supplies. Scope: `h1` and `hsp` together with `0 < ε` require
`spectrum ℝ (opT D)` to avoid `0`, so `opT D` must be invertible for the hypotheses to be
satisfiable.

DERIVED: `0` is the positivity threshold of `ε`, the positivity threshold of `Δ`, the lower bound in
`0 ≤ hamiltonian (opT D)`, the spectral point asserted present, and the singleton in the concluded
union; `1` is the spectral value of `opT D` assumed present in `h1` and the singleton in `hsp`. Both
are inherited from `reconstruct_qm_core`; nothing is chosen here. -/
theorem reconstruct_from_opT (D : TransferData A) {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ)
    (h1 : (1 : ℝ) ∈ spectrum ℝ (opT D))
    (hsp : spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    IsSelfAdjoint (hamiltonian (opT D)) ∧ 0 ≤ hamiltonian (opT D) ∧
      (0 : ℝ) ∈ spectrum ℝ (hamiltonian (opT D)) ∧
      spectrum ℝ (hamiltonian (opT D)) ⊆ {0} ∪ Set.Ici Δ := by
  haveI := complete_H D.toReflForm
  exact reconstruct_qm_core (opT D) (isSelfAdjoint_opT D) hε hΔ h1 hsp

#print axioms reconstruct_from_opT

/-- A real-arithmetic incompatibility, stated over reals `ε`, `Δ`: from `0 < Δ`, the membership
`(1 : ℝ) ∈ ({1} : Set ℝ) ∪ Set.Icc ε (Real.exp (-Δ))` and the non-membership
`(1 : ℝ) ∉ ({1} : Set ℝ)`, it derives `False`. The proof splits the union; the singleton branch
contradicts `hne`, and the interval branch gives `1 ≤ Real.exp (-Δ)` against `Real.exp (-Δ) < 1`.

Scope, and it is a strong one: `hne` says `(1 : ℝ) ∉ ({1} : Set ℝ)`, which is false outright, so no
caller can supply it and the theorem cannot be instantiated. The statement mentions no operator, no
spectrum and no `TransferData`; the content that survives is the interval branch, namely that `1` is
not in `Set.Icc ε (Real.exp (-Δ))` when `0 < Δ`.

DERIVED: `0` is the positivity threshold of `Δ`. `1` appears four times — as the element and as the
singleton in `hmem`, and again as the element and as the singleton in `hne`. -/
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
