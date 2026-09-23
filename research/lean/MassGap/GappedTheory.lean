import MassGap.Reconstruction

/-!
# The reconstructed gapped quantum theory, as data

`Reconstruction.reconstruct_qm_core` takes a self-adjoint element `T` of a C*-algebra whose real
spectrum sits inside `{1} ∪ [ε, e^{-Δ}]` and returns four facts about `Reconstruction.hamiltonian T`,
the continuous functional calculus of `-log` applied to `T`: it is self-adjoint, it is nonnegative in
the star order, `0` lies in its real spectrum, and its real spectrum is contained in
`{0} ∪ [Δ, ∞)`.

This module bundles those four facts. `GappedQuantumTheory A` is a structure carrying an element of
`A`, a real gap, and the four proofs; `reconstruct_gapped` builds one from the core lemma, taking the
gap to be the `Δ` of the spectral hypothesis.

Everything is stated for an element of a `CStarAlgebra` equipped with a `PartialOrder` and
`StarOrderedRing` structure. No Hilbert space, no GNS representation and no unbounded operator
appears; `ham` is an algebra element and `spectrum ℝ` is the real spectrum of that element.
-/

namespace MassGap.Reconstruction

/-- An element `ham` of a C*-algebra `A` together with a real number `gap`, bundled with four proofs:
`gap` is positive, `ham` is self-adjoint, `ham` is nonnegative in the star order, `0` belongs to the
real spectrum of `ham`, and that spectrum is contained in `{0} ∪ [gap, ∞)`. The last two together say
the spectrum meets `(0, gap)` nowhere while attaining `0`.

The order on `A` is the one supplied by the `PartialOrder`/`StarOrderedRing` instances, so `0 ≤ ham`
is the star order and not an inequality of numbers.

DERIVED: `0` is the only numeral and it appears four times, each time as a location rather than a
magnitude — the sign of `gap`, the lower bound of the star order, the spectral point the vacuum sits
at, and the isolated spectral point below the gap. `gap` is a field of the structure, so it is
quantified by whoever builds the structure and fixed by nothing here. -/
structure GappedQuantumTheory (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  /-- The Hamiltonian, an element of the algebra. -/
  ham : A
  /-- The width of the spectral gap above the vacuum. -/
  gap : ℝ
  /-- `gap` is strictly positive. -/
  gap_pos : 0 < gap
  /-- `ham` is self-adjoint. -/
  selfAdjoint : IsSelfAdjoint ham
  /-- `ham` is nonnegative in the star order of `A`. -/
  nonneg : 0 ≤ ham
  /-- `0` belongs to the real spectrum of `ham`. -/
  vacuum : (0 : ℝ) ∈ spectrum ℝ ham
  /-- The real spectrum of `ham` lies in `{0} ∪ [gap, ∞)`, so it misses `(0, gap)`. -/
  spectral_gap : spectrum ℝ ham ⊆ {0} ∪ Set.Ici gap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Builds a `GappedQuantumTheory A` from a self-adjoint `T : A` whose real spectrum contains `1` and
is contained in `{1} ∪ [ε, e^{-Δ}]`, with `ε` and `Δ` positive. The Hamiltonian field is
`Reconstruction.hamiltonian T` and the gap field is the `Δ` of the hypothesis; the four proof fields
are the four components of `reconstruct_qm_core` applied to the same hypotheses.

The gap delivered is exactly the `Δ` the caller supplies in `hsp`; nothing here improves it or
derives it from `T`. `ε` is used only to bound the spectrum away from `0` and does not appear in the
result.

DERIVED: `0` is the sign of `ε` and of `Δ` in the two positivity hypotheses. `1` is the spectral
point the vacuum of `T` sits at — it appears once as the membership `h1` and once as the isolated
point of the spectral inclusion `hsp` — and is the multiplicative identity of `A` read through
`spectrum ℝ`, not a chosen magnitude. `ε` and `Δ` are implicit arguments, quantified by the caller. -/
noncomputable def reconstruct_gapped (T : A) {ε Δ : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (hΔ : 0 < Δ) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    GappedQuantumTheory A :=
  let h := reconstruct_qm_core T hT hε hΔ h1 hsp
  ⟨hamiltonian T, Δ, hΔ, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end MassGap.Reconstruction
