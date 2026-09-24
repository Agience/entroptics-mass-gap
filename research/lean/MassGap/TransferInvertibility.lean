import Mathlib
import MassGap.Reconstruction

/-!
# MassGap.TransferInvertibility — consequences of `reconstruct_qm_core`'s spectral hypothesis

`Reconstruction.reconstruct_qm_core` takes

    hε  : 0 < ε
    hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))

This module derives three consequences of that pair, and one fact about compact operators.

## § 1, in any ring with an `ℝ`-algebra structure

* `zero_not_mem_spectrum` — `hsp` puts every spectral value either at `1` or at or above `ε > 0`, so
  `(0 : ℝ) ∉ spectrum ℝ T`.
* `isUnit_of_spectral_hypothesis` — in a unital ring, `0 ∈ spectrum ℝ a ↔ ¬ IsUnit a`, so the same
  hypotheses give `IsUnit T`. The spectral hypothesis therefore asks `T` to be invertible, which is
  a condition on the operator rather than a normalisation.
* `energies_bounded_of_spectral_hypothesis` — every `x ∈ spectrum ℝ T` satisfies
  `-Real.log x ≤ max 0 (-Real.log ε)`. Stated on the spectrum of `T` rather than through the
  functional calculus, so no spectral-mapping lemma is needed. The `max` with `0` is not slack: `ε`
  is not required to be below `1`, and when `Real.exp (-Δ) < ε` the interval is empty, `hsp` reads
  `spectrum ℝ T ⊆ {1}`, the only energy is `-Real.log 1 = 0`, and `-Real.log ε` is negative.

## § 2, for continuous linear maps `E →L[ℂ] E`

* `isCompactOperator_comp` — `IsCompactOperator T` gives `IsCompactOperator (T ∘L S)` for any
  bounded `S`.
* `not_isUnit_of_isCompactOperator` — a compact operator on a space that is not finite-dimensional
  over `ℂ` is not a unit, since the identity would then be compact and
  `FiniteDimensional.of_isCompactOperator_id` applies.
* `spectral_hypothesis_fails_for_compact` — composing the two: for a compact `T` on an
  infinite-dimensional `E`, `hsp` holds at no `ε > 0` and no `Δ`.

## Scope

Compactness of `T` and infinite-dimensionality of `E` are hypotheses of § 2, not results: no
operator is exhibited satisfying them, and nothing here identifies any particular lattice transfer
operator as compact. The physical description those hypotheses are drawn from is in the literature:
M. Lüscher, *Construction of a selfadjoint, strictly positive transfer matrix for Euclidean lattice
gauge theories*, Comm. Math. Phys. **54** (1977) 283; K. Osterwalder and E. Seiler, Ann. Phys.
**110** (1978) 440; E. Seiler, *Gauge Theories as a Problem of Constructive Quantum Field Theory and
Statistical Mechanics*, Lect. Notes in Physics **159**, Springer (1982). There, on a finite spatial
lattice with a continuous compact structure group, the physical space is the gauge-invariant part of
`L²(G^E)` and is infinite-dimensional, while `T` has a continuous kernel on a compact manifold and
is trace class, so its eigenvalues accumulate at `0`. For a finite gauge group on a finite lattice
the physical space is instead finite-dimensional, and the hypothesis `hinf` of § 2 fails.

`reconstruct_qm_core` itself is unaffected by anything here; `GappedExample` instantiates it.

DERIVED: `0` is the positivity threshold on `ε`, the spectral value the first two theorems exclude,
and the vacuum energy `-Real.log 1` entering the `max`; `1` is the spectral value the hypothesis
admits alongside the interval. `ε` and `Δ` are the caller's.
-/

namespace MassGap.TransferInvertibility

open MassGap.Reconstruction

section Abstract

-- The spectral lemmas below need only a ring with an `ℝ`-algebra structure: `spectrum.mem_iff` and
-- `IsUnit.neg` are the whole of what they use. Stating them at this generality rather than at
-- `CStarAlgebra` is what lets § 2 apply them to `E →L[ℂ] E`.
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- `(0 : ℝ) ∉ spectrum ℝ T` under `0 < ε` and
`hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))`. A spectral value is either `1` or at least
`ε`, and neither branch admits `0`. `Δ` is unconstrained and the upper endpoint is never used.

Stated for any `A` that is a `Ring` with an `Algebra ℝ A` instance.

DERIVED: `1` is the spectral value the singleton branch names and `0` the one excluded, both read
off `hsp`; the `0` in `0 < ε` is the positivity threshold on the interval's lower endpoint. -/
theorem zero_not_mem_spectrum (T : A) {ε Δ : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    (0 : ℝ) ∉ spectrum ℝ T := by
  intro h0
  rcases hsp h0 with h | h
  · rw [Set.mem_singleton_iff] at h
    exact absurd h (by norm_num)
  · exact absurd h.1 (by linarith)

/-- `IsUnit T` under the same two hypotheses. In a unital ring `0 ∈ spectrum 𝕜 a ↔ ¬ IsUnit a`, so
`zero_not_mem_spectrum` gives invertibility; the proof goes by contradiction through
`spectrum.mem_iff` and `IsUnit.neg`.

So `reconstruct_qm_core`'s spectral hypothesis entails that `T` is invertible in `A`, a condition on
the operator rather than a normalisation.

DERIVED: `0` is the positivity threshold on `ε`; `1` is the spectral value `hsp`'s singleton branch
names. Both come from the hypothesis, and the conclusion contains no numeral. -/
theorem isUnit_of_spectral_hypothesis (T : A) {ε Δ : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    IsUnit T := by
  by_contra h
  apply zero_not_mem_spectrum T hε hsp
  rw [spectrum.mem_iff, map_zero, zero_sub]
  intro hu
  exact h (by simpa using hu.neg)

/-- Under the same two hypotheses, `-Real.log x ≤ max 0 (-Real.log ε)` for every
`x ∈ spectrum ℝ T`. The singleton branch gives `-Real.log 1 = 0`; the interval branch gives
`Real.log ε ≤ Real.log x` by `Real.log_le_log`, hence a bound by the second argument of the `max`.

Stated on the spectrum of `T`, not through the functional calculus, so no spectral-mapping lemma is
required. The `max` with `0` is needed rather than decorative: `ε` is not required to be below `1`,
and if `Real.exp (-Δ) < ε` the interval is empty, `hsp` reduces to `spectrum ℝ T ⊆ {1}`, and
`-Real.log ε` is then negative while the admitted energy is `0`.

DERIVED: `1` is the spectral value the singleton branch names, whose energy is `-Real.log 1 = 0`;
that `0` is the first argument of the `max`; the `0` in `0 < ε` is the positivity threshold on the
interval's lower endpoint. -/
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

/-! ### ε restated as a non-membership -/

/-- **A compact set of reals inside `Set.Ici 0` that does not contain `0` has a strictly positive
lower bound.** Compactness makes the infimum attained, so the bound is a MEMBER of the set: there is
no constant to choose here, only a minimum to name.

`Aperture.no_interior_transition` is the same minimiser argument on an interval.

The empty case returns `1` and is not slack — the empty set is bounded below by everything and the
witness still has to be some positive real.

DERIVED: `0` is the excluded point and the lower end of `Set.Ici`; `1` is the empty-case witness,
where every positive real serves. -/
theorem exists_pos_lower_bound_of_compact {S : Set ℝ} (hc : IsCompact S)
    (hpos : S ⊆ Set.Ici 0) (h0 : (0 : ℝ) ∉ S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε ≤ x := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨m, hmS, hmin⟩ := IsCompact.exists_isMinOn hc hne continuousOn_id
    refine ⟨m, ?_, fun x hx => by simpa using isMinOn_iff.mp hmin x hx⟩
    rcases lt_or_eq_of_le (Set.mem_Ici.mp (hpos hmS)) with h | h
    · exact h
    · exact absurd (show (0 : ℝ) ∈ S by rw [h]; exact hmS) h0

#print axioms exists_pos_lower_bound_of_compact

/-- **`reconstruct_qm_core`'s spectral hypothesis, assembled from a band and three facts.**

Everything above reads consequences OUT of `hsp`. This puts one together, from the band the transfer
chain delivers — `GNSCompare.spectrum_opT_subset_of_positiveTransfer_of_rayleigh` gives
`spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (-Λ) Λ` from the Rayleigh ceiling and `PositiveTransfer` — together
with `hpos`, `h0` and compactness.

`Δ` comes out as `-Real.log Λ`, which `Real.exp_log` returns to `Λ` at the upper endpoint and which
`gap_pos_of_lt_one` makes positive exactly when `Λ < 1`. So the gap is the band's own width read
logarithmically; nothing is selected. `Aperture.lean` uses the same `neg_neg`/`Real.exp_log` step.

**THIS IS A RESTATEMENT, NOT PROGRESS ON THE GAP, and the accounting is against it.** In goes one
obligation and out come three.

* `h0` is equivalent to the thing it replaces. `zero_not_mem_spectrum` derives `h0` FROM `hsp`, so
  this closes the cycle rather than opening the door: with the band and `hpos` in hand, `hsp`, `h0`
  and — by `isUnit_of_spectral_hypothesis` and the same `spectrum.mem_iff` rewrite in reverse —
  `IsUnit T` all say the same thing.
* `hpos` is open. No declaration in this tree, for any operator, goes from a nonnegative quadratic
  form to `spectrum ⊆ Set.Ici 0`. `GNSHilbert.re_inner_opT_nonneg` supplies
  `0 ≤ RCLike.re (inner ℂ x (opT D x))` given `PositiveTransfer D`, and its only consumer reports it
  as a property rather than feeding it to a spectral lemma. Every declaration wanting spectral
  positivity takes it as a binder — `RefinementLaw` does so five times.
* `hc` is open. `spectrum.isCompact` and `spectrum.isClosed` occur nowhere in this tree, so
  compactness is a hypothesis here. A caller holding closedness could get it from
  `IsCompact.of_isClosed_subset` against `GNSHilbert.spectrum_opT_subset_unit_interval`.

What it buys is shape: an existential over `ε`, entangled with `Δ`, becomes one non-membership that
can be attacked directly — by a lower bound `c‖x‖ ≤ ‖opT D x‖`, or by invertibility read off the
transfer structure. Either would have to avoid routing back through `hsp`.

**The sharp edge.** If `opT D` is ever shown compact as an operator on an infinite-dimensional
`H D.toReflForm`, `spectral_hypothesis_fails_for_compact` says no `ε` exists, `h0` is false, and this
theorem is vacuous rather than merely unused. Nothing in the tree decides that.

DERIVED: `0` is the excluded spectral point and the lower end of `Set.Ici`; `1` is the spectral value
the singleton branch names, `opT`'s vacuum eigenvalue. `Λ` is the caller's and `ε` is the minimum's;
no numeral is chosen. -/
theorem spectral_hypothesis_of_band (T : A) {Λ : ℝ} (hΛ : 0 < Λ)
    (hband : spectrum ℝ T ⊆ {1} ∪ Set.Icc (-Λ) Λ)
    (hpos : spectrum ℝ T ⊆ Set.Ici 0) (h0 : (0 : ℝ) ∉ spectrum ℝ T)
    (hc : IsCompact (spectrum ℝ T)) :
    ∃ ε : ℝ, 0 < ε ∧
      spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-(-Real.log Λ))) := by
  obtain ⟨ε, hε, hmin⟩ := exists_pos_lower_bound_of_compact hc hpos h0
  refine ⟨ε, hε, ?_⟩
  rw [neg_neg, Real.exp_log hΛ]
  intro x hx
  rcases hband hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hmin x hx, h.2⟩

#print axioms spectral_hypothesis_of_band

/-- The gap the band buys: `0 < -Real.log Λ` exactly when `0 < Λ < 1`, which is
`reconstruct_from_opT`'s `hΔ`.

This is where `Λ < 1` is spent. At `Λ = 1` the gap is `0` and above it the gap is negative — the same
statement as the band saying nothing, since `GNSHilbert.spectrum_opT_subset_unit_interval` already
confines the spectrum to `[-1, 1]` with no hypothesis at all.

DERIVED: `0` is the positivity threshold; `1` is both the vacuum eigenvalue and the contraction
constant, and their coinciding is what makes `Λ < 1` the content rather than a choice. -/
theorem gap_pos_of_lt_one {Λ : ℝ} (hΛ : 0 < Λ) (h1 : Λ < 1) : 0 < -Real.log Λ := by
  simpa using Real.log_neg hΛ h1

#print axioms gap_pos_of_lt_one

end Abstract

/-! ## 2. Compact operators are not units in infinite dimensions -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `IsCompactOperator (T ∘L S)` whenever `IsCompactOperator T`, for continuous linear maps
`T S : E →L[ℂ] E`. Through
`isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image`, the witnessing neighbourhood for
the composite is `S ⁻¹' V`, a neighbourhood of `0` by continuity of `S`, and its image under
`T ∘L S` is contained in the image of `V` under `T`.

No compactness is required of `S`, only boundedness.

DERIVED: no numeral appears in the statement. -/
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

/-- `¬ IsUnit T` for a compact operator `T : E →L[ℂ] E` on a space that is not finite-dimensional
over `ℂ`. If `T` were a unit, `isCompactOperator_comp` would make `T ∘L T⁻¹` compact; that composite
is the identity, and `FiniteDimensional.of_isCompactOperator_id` — Riesz's lemma — would then force
`FiniteDimensional ℂ E`, contradicting `hinf`.

Compactness of `T` and infinite-dimensionality of `E` are both hypotheses; no operator satisfying
them is exhibited here.

DERIVED: no numeral appears in the statement. The `1` of the operator algebra occurs only inside the
proof, as the identity `T ∘L T⁻¹` reduces to. -/
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

/-- For a compact `T : E →L[ℂ] E` on a space that is not finite-dimensional over `ℂ`, and any
`ε > 0` and any `Δ`, `¬ (spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ)))`. The inclusion would give
`IsUnit T` by `isUnit_of_spectral_hypothesis`, which `not_isUnit_of_isCompactOperator` refutes. The
conclusion is universally quantified over `ε` and `Δ`, so no choice of either satisfies `hsp` for
such an operator.

Compactness and infinite-dimensionality are hypotheses supplied by the caller; this module
identifies no operator as compact.

DERIVED: `0` is the positivity threshold on `ε`; `1` is the spectral value the negated inclusion's
singleton branch names. `ε` and `Δ` are the caller's. -/
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
#print axioms exists_pos_lower_bound_of_compact
#print axioms spectral_hypothesis_of_band
#print axioms gap_pos_of_lt_one
end Audit

end MassGap.TransferInvertibility
