import Mathlib
import MassGap.ObserverRotation

noncomputable section

/-!
# MassGap.ObserverAxisN — the hypercubic group for a covariant flow

`ofConf_axisCov`, `scaled_axisCov`: the unscaled flow and the energy density (factor `a⁻⁴`, any
relabelling-blind subtraction) of a configuration flow that commutes with the axis permutations are
`Flow.AxisCov`. With `ContinuumFlow.contSF_reflect` this gives the hypercubic group in the limit, as
identities of `limUnder` values with no bound assumed: `signed_of_axisCov` for any covariant flow,
at `HypScalar` fields, and `latSF_signed_of_axisCov` at every lattice step.
-/

namespace MassGap.ObserverAxisN

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumHypercubic MassGap.ContinuumFlow MassGap.BlockLattice
  MassGap.LocalApe MassGap.ObserverFlow MassGap.ObserverRotation

section Step

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

end Step

/-! ## The flow and its energy density -/

section Flow

variable {N : ℕ}

/-- **The unscaled flow of a covariant configuration flow is covariant.**

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem ofConf_axisCov (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U)) :
    Flow.AxisCov (Flow.ofConf W) :=
  ofConfScaled_axisCov W _ _ _ _ hW (fun _ _ _ => rfl) (fun _ _ _ => rfl)

#print axioms ofConf_axisCov

/-- **The energy density of a covariant configuration flow is covariant**: the canonical factor `a⁻⁴`
and any subtraction blind to the relabelling.

DERIVED: `4` in `Fin 4` is the spacetime dimension and the factor's exponent. -/
theorem scaled_axisCov (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hsa : ∀ k e O, s k (lfieldAxis e O) = s k O) :
    Flow.AxisCov (Flow.ofConfScaled W (canonZ N) s (canonZ_refl N) hs) :=
  ofConfScaled_axisCov W _ _ _ _ hW (fun _ _ _ => rfl) hsa

#print axioms scaled_axisCov

/-- **The hypercubic rotations of a covariant flow in the limit.** For a matrix acting on `ℝ⁴` as a
signed permutation and `HypScalar` fields, composing every test function with it leaves the limit
unchanged.

DERIVED: `0` is the excluded colour count; `1` and `-1` the signs; `4` the dimension. -/
theorem signed_of_axisCov (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ)
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
      ∀ y i, A.mulVec y i = sg i * y (σ i))
    {ι : Type} [Fintype ι] (F F' : ι → SField N) (hH : ∀ i, HypScalar (F i).1)
    (hfield : ∀ i, (F' i).1 = (F i).1) (htest : ∀ i y, (F' i).2.1 y = (F i).2.1 (A.mulVec y)) :
    contSF hN Φ F' = contSF hN Φ F := by
  obtain ⟨σ, sg, hsg, hAy⟩ := hA
  refine contSF_signed hN Φ hΦ σ sg hsg F F' hH hfield (fun i y => ?_)
  rw [htest i y]
  exact congrArg (F i).2.1 (funext fun j => hAy y j)

#print axioms signed_of_axisCov

/-- The same at every lattice step.

DERIVED: `0` is the excluded colour count; `1` and `-1` the signs; `4` the dimension. -/
theorem latSF_signed_of_axisCov (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ) (k : ℕ)
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
      ∀ y i, A.mulVec y i = sg i * y (σ i))
    {ι : Type} [Fintype ι] (F F' : ι → SField N) (hH : ∀ i, HypScalar (F i).1)
    (hfield : ∀ i, (F' i).1 = (F i).1) (htest : ∀ i y, (F' i).2.1 y = (F i).2.1 (A.mulVec y)) :
    latSF hN Φ k F' = latSF hN Φ k F := by
  obtain ⟨σ, sg, hsg, hAy⟩ := hA
  refine latSF_signed hN Φ hΦ k σ sg hsg F F' hH hfield (fun i y => ?_)
  rw [htest i y]
  exact congrArg (F i).2.1 (funext fun j => hAy y j)

#print axioms latSF_signed_of_axisCov

end Flow

section Polar


variable {N : ℕ} [NeZero N]

end Polar

end MassGap.ObserverAxisN
