import MassGap.Reconstruction

/-!
# The reconstructed gapped quantum theory, as data

`Reconstruction.reconstruct_qm_core` proves the operator-theoretic output of OS reconstruction — a
self-adjoint Hamiltonian `H = -log T`, `H ≥ 0`, a vacuum at energy `0`, and a positive mass gap (no spectrum
in the open interval `(0, Δ)`). This module packages that output as a `structure` that carries the
Hilbert-space-algebra Hamiltonian together with its vacuum and its gap, so `reconstruct_gapped` returns a
CONSTRUCTED gapped quantum theory (real data), assembled from the CFC core. Foundational axioms only.
-/

namespace MassGap.Reconstruction

/-- **A reconstructed gapped quantum theory** — the operator-theoretic output of OS reconstruction as data:
a self-adjoint Hamiltonian `ham` on a C*-algebra, nonnegative, with the vacuum energy `0` attained and a
positive mass gap `gap` (no spectrum in the open interval `(0, gap)`). -/
structure GappedQuantumTheory (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  /-- The reconstructed Hamiltonian. -/
  ham : A
  /-- The mass gap. -/
  gap : ℝ
  /-- The gap is positive. -/
  gap_pos : 0 < gap
  /-- The Hamiltonian is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint ham
  /-- The Hamiltonian is nonnegative, `H ≥ 0`. -/
  nonneg : 0 ≤ ham
  /-- The vacuum: ground-state energy `0` is attained. -/
  vacuum : (0 : ℝ) ∈ spectrum ℝ ham
  /-- The mass gap: no spectrum in the open interval `(0, gap)`. -/
  spectral_gap : spectrum ℝ ham ⊆ {0} ∪ Set.Ici gap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **OS reconstruction produces a gapped quantum theory.** From a gapped Euclidean-time transfer operator
`T` (self-adjoint, spectrum `{1} ∪ [ε, e^{-Δ}]`, `ε>0`, `Δ>0`, vacuum eigenvalue `1`), the reconstruction
yields a `GappedQuantumTheory` with Hamiltonian `H = -log T` and mass gap `Δ`: a constructed
Hilbert-space-algebra Hamiltonian with a vacuum and a positive gap, foundational axioms only. -/
noncomputable def reconstruct_gapped (T : A) {ε Δ : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (hΔ : 0 < Δ) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    GappedQuantumTheory A :=
  let h := reconstruct_qm_core T hT hε hΔ h1 hsp
  ⟨hamiltonian T, Δ, hΔ, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end MassGap.Reconstruction
