import Mathlib
import MassGap.ContinuumNontrivial

noncomputable section

/-!
# MassGap.ContinuumClay — the continuum gap on a non-trivial reconstructed space

`ContinuumSep.continuum_gap_sep` gives the reconstructed continuum transfer operator a spectral gap of
physical rate at least `c/L` at every dyadic step, and `ContinuumNontrivial.exists_orth_ne_zero_of_af`
gives the same reconstructed space a non-zero vector orthogonal to the vacuum and outside its span.
Both are stated at the connected renormalisation `Renorm.connected hN Z` with its reflection
compatibility `Renorm.connected_reflCompat hN Z τ hZ`, so they compose into one statement on one
Hilbert space: `continuum_gap_nontrivial`. `GappedAt` and `NontrivialVacuum` name the two halves on
any transfer data, and `contD` names the reconstructed transfer data at a dyadic step.

## Scope

The hypotheses are the open inputs of E, M, N and Y at the continuum level:
`ContinuumSep.UniformBoundSep` (E, a uniform bound on separated families at a growing `Z`),
`WeakCouplingWindow.FixedWindowDecay` (M, the uniform physical gap), `ContinuumNontrivial.KernelConvergesSep`
(the renormalised kernel of the field `O` converging to a radial `G` on separated points) and
`ShortDistanceY.AFShortDistance G` (Y). Rotation invariance off the hypercubic group is
`ContinuumHypercubic.RotationOpen`, outside this statement.
-/

namespace MassGap.ContinuumClay

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

section Predicates

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The gap on the reconstructed space at rate `r`.** `0 < r < 1`, `TransferGap.GapAt D r`, the vacuum
complement of the reconstructed Hilbert space contracted by `r`, spectrum in `{1} ∪ [0, r]` and `1` its
greatest element — the conjunction `ContinuumSep.continuum_gap_sep` concludes at each step.

DERIVED: `0` is the lower end of `r` and of the spectral interval and the vanishing vacuum pairing;
`1` is the vacuum eigenvalue and the upper end of `r`. -/
def GappedAt (D : Transfer.TransferData A) (r : ℝ) : Prop :=
  0 < r ∧ r < 1 ∧ TransferGap.GapAt D r
    ∧ (∀ u : GNSHilbert.H D.toReflForm,
        inner ℂ (GNSHilbert.Omega D.toReflForm D.vac) u = (0 : ℂ) →
        ‖GNSHilbert.opT D u‖ ≤ r * ‖u‖)
    ∧ spectrum ℝ (GNSHilbert.opT D) ⊆ {1} ∪ Set.Icc 0 r
    ∧ IsGreatest (spectrum ℝ (GNSHilbert.opT D)) 1

/-- **The reconstructed space is not spanned by the vacuum.** Some non-zero vector is orthogonal to the
vacuum and is no complex multiple of it.

DERIVED: `0` is the vanishing vacuum pairing and the zero vector. -/
def NontrivialVacuum (D : Transfer.TransferData A) : Prop :=
  ∃ u : GNSHilbert.H D.toReflForm,
    inner ℂ (GNSHilbert.Omega D.toReflForm D.vac) u = (0 : ℂ) ∧ u ≠ 0
      ∧ ∀ a : ℂ, u ≠ a • GNSHilbert.Omega D.toReflForm D.vac

end Predicates

variable {N : ℕ}

/-- **The reconstructed continuum transfer data at dyadic step `m`**, at the connected renormalisation
`Renorm.connected hN Z` with its reflection compatibility.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def contD (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) (m : ℕ) :
    Transfer.TransferData (ContinuumSep.AmodSep N τ) :=
  ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB (Renorm.connected_reflCompat hN Z τ hZ) m

/-- **The continuum gap on a non-trivial space.** At `2 ≤ N`, a reflection-invariant field-strength
factor `Z`, the separated uniform bound at `Renorm.connected hN Z`, `FixedWindowDecay` at a window
`L > 0`, and a field `O` whose renormalised kernel converges to a radial `G` of asymptotic-freedom
short-distance form: there is `c > 0` such that at every dyadic step `m` the reconstructed transfer
data `contD` is `GappedAt` the rate `e^{−(c/L)·dySpacing N m}` — a physical gap of at least `c/L` — and
its Hilbert space is `NontrivialVacuum` (`ContinuumSep.continuum_gap_sep`,
`ContinuumNontrivial.exists_orth_ne_zero_of_af`).

DERIVED: `2` is the least rank with a non-zero Haar variance
(`WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay`'s); `0` is the excluded colour count and the
lower end of `L` and `c`; `4` in `Fin 4` is the spacetime dimension. -/
theorem continuum_gap_nontrivial (hN2 : 2 ≤ N) (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      GappedAt (contD hN Z τ hZ hB m) (Real.exp (-(c / L) * dySpacing N m))
        ∧ NontrivialVacuum (contD hN Z τ hZ hB m) := by
  obtain ⟨c, hc, hgap⟩ := ContinuumSep.continuum_gap_sep hN2 hN (Renorm.connected hN Z) hB τ
    (Renorm.connected_reflCompat hN Z τ hZ) hL hW
  exact ⟨c, hc, fun m =>
    ⟨hgap m, ContinuumNontrivial.exists_orth_ne_zero_of_af hN Z τ hZ hB m O G hconv hY⟩⟩

#print axioms continuum_gap_nontrivial

end MassGap.ContinuumClay
