import Mathlib
import MassGap.Reconstruction

/-!
# MassGap.TransferInvertibility — the spectral hypothesis asks the transfer operator to be INVERTIBLE

## ⛔ What `reconstruct_qm_core` actually requires

`Reconstruction.reconstruct_qm_core` takes

    hε  : 0 < ε
    hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))

and its own first step (`hpos`) reads off that every spectral value is strictly positive. The
consequence nobody wrote down is that this puts `0` OUTSIDE the spectrum, which in a unital algebra
is exactly the statement that **`T` is a unit** — `isUnit_of_spectral_hypothesis` below.

`ClayAssembly` records that `-log T` "needs `0 ∉ spectrum T` rather than injectivity", as a
requirement still to be met. The point of this module is that for the object the Clay problem is
about the requirement is **not merely unmet — it is unmeetable**, and so the shape of what is open
in Chain B is different from what the tree says it is.

## ⛔ Why that is an obstruction and not a to-do

The structure is sharper than "not invertible", and it is standard.

* **`T` is self-adjoint and STRICTLY positive** — M. Lüscher, *Construction of a selfadjoint,
  strictly positive transfer matrix for Euclidean lattice gauge theories*, Comm. Math. Phys. **54**
  (1977) 283. Strict positivity says `0` is not an EIGENVALUE, which is what makes `-log T` a
  well-defined self-adjoint operator at all. Reflection positivity and the positive self-adjoint
  transfer matrix: K. Osterwalder and E. Seiler, Ann. Phys. **110** (1978) 440; the monograph is
  E. Seiler, *Gauge Theories as a Problem of Constructive Quantum Field Theory and Statistical
  Mechanics*, Lect. Notes in Physics **159**, Springer (1982).
* **But `0` is in the SPECTRUM.** On a finite spatial lattice with a CONTINUOUS compact group the
  physical space is the gauge-invariant part of `L²(G^E)`, which is infinite-dimensional, and `T`
  has a smooth kernel on a compact manifold, hence is trace class. Its eigenvalues accumulate at `0`,
  so `0` lies in the spectrum as approximate point spectrum.

So `T` is **injective with dense range and an unbounded inverse** — not boundedly invertible — and
`H = -log T` is unbounded above, as the Kogut–Susskind electric energy `∑ E²` independently forces.
`isUnit_of_spectral_hypothesis` asks for exactly the property `T` lacks.

**⭐ AND THE RIESZ HALF IS NOW PROVED.** § 2 below: `not_isUnit_of_isCompactOperator` — a compact
operator on an infinite-dimensional space is never invertible, since `1 = T ∘ T⁻¹` would be compact.
`spectral_hypothesis_fails_for_compact` composes it with `isUnit_of_spectral_hypothesis`: for such an
operator the spectral hypothesis holds at NO `ε > 0` and no `Δ`. Foundational axioms only.

**⚠ WHAT REMAINS CITED IS THE IDENTIFICATION**, and only that: that the physical transfer operator
IS compact and its slice space infinite-dimensional. That is the Lüscher / Osterwalder–Seiler
description above, and it is formalised nowhere in this tree. The implication it feeds is no longer a
citation; the premise still is.

**⛔ AND THE EXCEPTION IS INSTRUCTIVE.** For a FINITE gauge group on a finite lattice the physical
space is finite-dimensional and `T` IS invertible, so the obstruction comes from the CONTINUITY of
the group, not from the lattice. That is the same place the physics divides: 4-D theories with
finite abelian gauge groups are known not to confine at large coupling (Guth 1980;
Fröhlich–Spencer, Comm. Math. Phys. **83** (1982) 411; Kotecký–Shlosman 1982), so an argument that
is blind to the group would be proving something false there.

## What this does and does not close

It does NOT refute the mass gap, and it does not say `reconstruct_qm_core` is wrong — that theorem
is correct, and `GappedExample` instantiates it. What it says is that the hypothesis is satisfied by
operators with a LARGEST energy `-log ε`, and that reaching the Clay conclusion through it therefore
needs either a different endpoint, stated for an unbounded `H` on a dense domain, or a route that
restricts to a spectral subspace on which `T` is bounded below.

`energies_bounded_of_spectral_hypothesis` is the same fact from the energy side: under the
hypothesis the reconstructed `H` has no spectrum above `-log ε`.
-/

namespace MassGap.TransferInvertibility

open MassGap.Reconstruction

section Abstract

-- The spectral lemmas below need only a ring with an `ℝ`-algebra structure: `spectrum.mem_iff` and
-- `IsUnit.neg` are the whole of what they use. Stating them here rather than at `CStarAlgebra` is
-- what lets them reach `E →L[ℂ] E` in § 2, where the obstruction lives.
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **THE HYPOTHESIS KEEPS `0` OUT OF THE SPECTRUM.** Either a spectral value is `1`, or it is at
least `ε > 0`; neither is `0`.

DERIVED: `0` and `1` are the spectral values the two branches name, not levels chosen here. -/
theorem zero_not_mem_spectrum (T : A) {ε Δ : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    (0 : ℝ) ∉ spectrum ℝ T := by
  intro h0
  rcases hsp h0 with h | h
  · rw [Set.mem_singleton_iff] at h
    exact absurd h (by norm_num)
  · exact absurd h.1 (by linarith)

/-- **⛔ SO THE HYPOTHESIS SAYS THE TRANSFER OPERATOR IS INVERTIBLE.** In a unital algebra
`0 ∈ spectrum 𝕜 a ↔ ¬ IsUnit a`, so keeping `0` out is exactly invertibility.

This is the content of `reconstruct_qm_core`'s `hε`, made explicit. It is a strong hypothesis about
the operator and not a normalisation.

DERIVED: no numeral of its own. -/
theorem isUnit_of_spectral_hypothesis (T : A) {ε Δ : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    IsUnit T := by
  by_contra h
  apply zero_not_mem_spectrum T hε hsp
  rw [spectrum.mem_iff, map_zero, zero_sub]
  intro hu
  exact h (by simpa using hu.neg)

/-- **AND THE RECONSTRUCTED HAMILTONIAN HAS A LARGEST ENERGY.** Every spectral value of `T` is at
least `ε`, so every energy `-log x` is at most `-log ε`.

Stated on the spectrum of `T` rather than through the functional calculus, which is the same fact
one step earlier and needs no spectral-mapping lemma: the energies the hypothesis admits are exactly
`-log` of the admitted spectral values, and those are bounded.

**THE `max` IS NOT SLACK.** `ε` is not required to be below `1`: if `Real.exp (-Δ) < ε` the interval
is EMPTY and the hypothesis reads `spectrum T ⊆ {1}`, where the only energy is `-log 1 = 0` while
`-log ε` is negative. So `-log ε` alone is not an upper bound, and the vacuum is the reason.

DERIVED: `1` is the vacuum's spectral value, whose energy is `-log 1 = 0`; `ε` is the caller's
floor; the `0` in the `max` is that vacuum energy. No magnitude is chosen here. -/
theorem energies_bounded_of_spectral_hypothesis (T : A) {ε Δ : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    ∀ x ∈ spectrum ℝ T, -Real.log x ≤ max 0 (-Real.log ε) := by
  intro x hx
  rcases hsp hx with h | h
  · rw [Set.mem_singleton_iff] at h
    subst h
    simp
  · have hlog : Real.log ε ≤ Real.log x := Real.log_le_log hε h.1
    exact le_max_of_le_right (by linarith)

end Abstract

/-! ## 2. ⭐ The obstruction, proved -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A compact operator precomposed with a bounded one is compact: push the compact set forward
through the preimage of the witnessing neighbourhood.

DERIVED: no numeral. -/
theorem isCompactOperator_comp (T S : E →L[ℂ] E) (hc : IsCompactOperator T) :
    IsCompactOperator (T ∘L S) := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image] at hc ⊢
  obtain ⟨V, hV, hK⟩ := hc
  refine ⟨S ⁻¹' V, ?_, ?_⟩
  · have hS : Filter.Tendsto S (nhds 0) (nhds 0) := by
      simpa using (S.continuous.tendsto 0)
    exact hS hV
  · refine IsCompact.of_isClosed_subset hK isClosed_closure (closure_mono ?_)
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨S w, hw, rfl⟩

#print axioms isCompactOperator_comp

/-- **⭐ A COMPACT OPERATOR ON AN INFINITE-DIMENSIONAL SPACE IS NOT INVERTIBLE.** If `T` had an
inverse then `1 = T ∘ T⁻¹` would be compact, and `FiniteDimensional.of_isCompactOperator_id` — Riesz
— forbids that.

**This is the half of the obstruction that is now a THEOREM** rather than a citation.

DERIVED: the `1` is the identity of the operator algebra. -/
theorem not_isUnit_of_isCompactOperator (T : E →L[ℂ] E) (hc : IsCompactOperator T)
    (hinf : ¬ FiniteDimensional ℂ E) : ¬ IsUnit T := by
  intro hu
  obtain ⟨u, rfl⟩ := hu
  have h1 : IsCompactOperator ((u : E →L[ℂ] E) ∘L (↑u⁻¹ : E →L[ℂ] E)) :=
    isCompactOperator_comp _ _ hc
  have he : (u : E →L[ℂ] E) ∘L (↑u⁻¹ : E →L[ℂ] E) = 1 := by
    rw [← ContinuousLinearMap.mul_def]
    exact u.mul_inv
  rw [he, ContinuousLinearMap.one_def] at h1
  exact hinf (FiniteDimensional.of_isCompactOperator_id h1)

#print axioms not_isUnit_of_isCompactOperator

/-- **⭐⛔ SO THE SPECTRAL HYPOTHESIS IS UNSATISFIABLE FOR A COMPACT OPERATOR IN INFINITE DIMENSIONS.**

`reconstruct_qm_core`'s `hsp` with `0 < ε` forces `IsUnit T` (`isUnit_of_spectral_hypothesis`), and a
compact operator on an infinite-dimensional space is not a unit. **No `ε`, no `Δ`, no operator of that
kind.**

What remains cited is only which OBJECTS satisfy the two premises. The Euclidean transfer operator of
a lattice gauge theory with a continuous compact structure group acts on an infinite-dimensional
slice space through a continuous kernel on a compact manifold, hence is trace class and a fortiori
compact — Lüscher, Osterwalder–Seiler and Seiler, as § 1 records. **That identification is still not
formalised**; the implication it feeds now is.

DERIVED: `0` and `1` are the spectral values the hypothesis names; `ε`, `Δ` are the caller's. -/
theorem spectral_hypothesis_fails_for_compact (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hinf : ¬ FiniteDimensional ℂ E) {ε Δ : ℝ} (hε : 0 < ε) :
    ¬ (spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) := by
  intro hsp
  exact not_isUnit_of_isCompactOperator T hc hinf (isUnit_of_spectral_hypothesis T hε hsp)

#print axioms spectral_hypothesis_fails_for_compact

end Compact

/-! ## Footprints -/

section Audit
#print axioms zero_not_mem_spectrum
#print axioms isUnit_of_spectral_hypothesis
#print axioms energies_bounded_of_spectral_hypothesis
end Audit

end MassGap.TransferInvertibility
