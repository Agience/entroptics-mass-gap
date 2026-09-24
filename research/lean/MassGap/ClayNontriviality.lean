import Mathlib
import MassGap.DLRLimit
import MassGap.InfiniteVolume
import MassGap.WilsonDLR

/-!
# MassGap.ClayNontriviality — a non-degenerate DLR limit from the Wilson contact floor

Composes two results of the tree:

* `DLRLimit.exists_infinite_volume_gibbs_state_nondegenerate`, which produces a normalised DLR state
  that is not a point mass, given a family of finite-volume states, the DLR consistency relation,
  and a positive constant bounding the variance of one observable below, uniformly in the volume.
* `InfiniteVolume.exists_uniform_contact_floor`, which supplies such a constant for the Wilson
  contact value: `∃ δ₀ > 0, ∀ N β, 0 ≤ β → exp (-(128 * β)) * δ₀ ≤ wilsonCorrAt N β 0`, with `δ₀`
  bound outside the quantifier over apertures `N`.

`PlaqVariance.corrClay_zero_eq` identifies `wilsonCorrAt N β 0` with the connected correlation of a
plaquette observable with itself, so the floor is a variance floor.

Contents:
* `clay_nontriviality_of_wilson_variance` — the composition, for an abstract kernel `γ`, family `μ`
  and consistency relation `hcons`, with the floor discharged rather than assumed.
* `clay_nontriviality_of_wilson_bridge` — the same, with `γ`, `μ` and `hcons` instantiated at
  `WilsonDLR.specCM`, `WilsonDLR.specState` and `WilsonDLR.hcons_specState`, leaving `hbridge` as the
  only substantive hypothesis.
* `uniform_variance_floor_exists` — the floor restated with its positivity alongside it.
* `floor_is_independent_of_any_family` — a positive lower bound on `wilsonCorrAt N β 0` with no
  family, kernel or consistency relation in the statement.

Scope, stated for both main theorems.
* The conclusion is `¬ IsPointMass ν`: the limit state is not concentrated at a single
  configuration. It is not a statement that the correlations differ from a generalised free field.
* The constant `exp (-(128 * β)) * δ₀` degrades with `β` and is therefore not uniform in the
  coupling; it is uniform in the aperture, because `128` is `16 * dim` at `dim = 4` doubled — the
  plaquette-touch count of `StrongCoupling.touchDeg_bd_le`, which carries no extent.
* `hbridge` compares two different volume indexings: `wilsonCorrAt` is a variance on a finite
  periodic lattice indexed by an aperture, while `specState` is indexed by a `Finset ILink` of `ℤ⁴`
  with a frozen boundary `ω₀`. It is stated as an inequality, so only one direction of the
  comparison is required.
-/

namespace MassGap.ClayNontriviality

open MassGap.DLRLimit

/-- A non-degenerate infinite-volume DLR state, with the variance floor discharged. Takes a compact
topological space `G`, a specification kernel `γ`, a family `μ` of states indexed by `Finset ILink`,
the DLR consistency relation `hcons`, an observable `f₀`, a coupling `β` with `0 ≤ β`, an aperture
assignment `ap : Finset ILink → ℕ`, and `hbridge`, which bounds `wilsonCorrAt (ap Λ) β 0` above by
the variance `μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2` at every `Λ`. Produces
`∃ ν : State (IConf G), IsDLR γ ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν`.

The proof takes `δ₀` from `InfiniteVolume.exists_uniform_contact_floor`, uses
`Real.exp (-(128 * β)) * δ₀` as the floor constant for
`exists_infinite_volume_gibbs_state_nondegenerate`, and chains that floor through `hbridge`. The
floor is therefore not a hypothesis of this theorem.

Scope. `ap` is unconstrained: no relation between `Λ` and `ap Λ` is required, because the floor
holds at every aperture. The conclusion is non-degeneracy in the sense of `¬ IsPointMass`, not a
statement about the form of the correlations. `hbridge` remains a hypothesis and relates two
different volume indexings.

DERIVED: `0` is the lower bound on `β` and the contact lag in `wilsonCorrAt (ap Λ) β 0`; `2` is the
square of the first moment in the variance `μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2`; `1` is the unit
observable and the normalisation `ν 1 = 1`. The `128` of the floor occurs in the proof term only —
it is `exists_uniform_contact_floor`'s own exponent, `16 * dim` at `dim = 4` doubled — and does not
appear in the statement. -/
theorem clay_nontriviality_of_wilson_variance (G : Type) [TopologicalSpace G] [CompactSpace G]
    (γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ))
    (μ : Finset ILink → State (IConf G))
    (hcons : ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ), μ Λ (γ Λ' f) = μ Λ f)
    (f₀ : C(IConf G, ℝ)) (β : ℝ) (hβ : 0 ≤ β) (ap : Finset ILink → ℕ)
    (hbridge : ∀ Λ : Finset ILink,
      MassGap.wilsonCorrAt (ap Λ) β 0 ≤ μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2) :
    ∃ ν : State (IConf G), IsDLR γ ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  refine exists_infinite_volume_gibbs_state_nondegenerate G γ μ hcons f₀
    (Real.exp (-(128 * β)) * δ₀) (mul_pos (Real.exp_pos _) hδ₀) (fun Λ => ?_)
  exact le_trans (hfloor (ap Λ) β hβ) (hbridge Λ)

#print axioms clay_nontriviality_of_wilson_variance

/-- The same conclusion with the kernel, the family and the consistency relation instantiated at the
Wilson objects. For a compact second-countable Borel topological group `G`, a continuous plaquette
density `φ : G → ℝ` with `0 ≤ φ g` and `φ g ≤ 2` at every `g`, a coupling `β` with `0 ≤ β`, a
probability measure `μ` on `G`, a frozen boundary `ω₀`, an observable `f₀` and an aperture
assignment `ap`, together with `hbridge` bounding `wilsonCorrAt (ap Λ) β 0` above by the variance of
`f₀` under `WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ`, the conclusion is a state `ν` that is DLR for
`WilsonDLR.specCM hφc hφ0 hφ2 β μ`, satisfies `ν 1 = 1`, and is not a point mass.

The proof applies `clay_nontriviality_of_wilson_variance` with

* `γ := WilsonDLR.specCM hφc hφ0 hφ2 β μ`,
* the family `WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀`,
* `hcons := WilsonDLR.hcons_specState hφc hφ0 hφ2 β μ ω₀`,

so `hbridge` is the only hypothesis of the composition not instantiated from the tree.

⛔ **`hbridge` HAS NO WITNESS, SO THIS THEOREM IS VACUOUSLY TRUE.**
`VarianceBridge.wilson_bridge_hypothesis_unsatisfiable` refutes it: `hbridge` is quantified over
EVERY finite region, and at the empty one the variance is zero — `variance_at_empty_eq_zero` — while
`PlaqVariance.corrClay_zero_pos` puts the torus contact value strictly above zero at every extent and
every real coupling, with no hypotheses. The inequality reads "a positive number is at most zero", at
every `ap`, `f₀`, `ω₀` and `β`.

Use `VarianceBridge.clay_nontriviality_of_eventual_wilson_bridge` instead. It is this statement with
`hbridge` at `atTop`, which drops the small regions and in particular the empty one; the conclusion
is identical, and `DLRLimit.not_isPointMass_of_uniform_variance` takes an `∀ᶠ` hypothesis anyway, so
the universal form was never spending its extra strength.

That refutes the ROUTE, not non-triviality: the empty region has no observable to be non-trivial
about.

Scope. `hbridge` compares a variance on the finite periodic lattice that `wilsonCorrAt` is defined
on with a variance of `specState`, which is indexed by a `Finset ILink` of `ℤ⁴` at a frozen
boundary — and restricting to `atTop` removes the refutation, not that comparison. The conclusion is
`¬ IsPointMass ν`, not a statement about the correlations' functional form.

DERIVED: `0` is the lower bound on `φ` and on `β`, and the contact lag in `wilsonCorrAt (ap Λ) β 0`;
`2` appears twice, once as the upper bound `φ g ≤ 2` on the plaquette density (matching
`WilsonAction.wilsonDensity_le_two`) and once as the square of the first moment in the variance;
`1` is the unit observable and the normalisation `ν 1 = 1`. Every one is inherited, from the theorem
being instantiated or from `specCM`'s own hypotheses. -/
theorem clay_nontriviality_of_wilson_bridge {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [MeasurableMul₂ G] [MeasurableInv G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (hβ : 0 ≤ β) (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
    (ω₀ : IConf G) (f₀ : C(IConf G, ℝ)) (ap : Finset ILink → ℕ)
    (hbridge : ∀ Λ : Finset ILink,
      MassGap.wilsonCorrAt (ap Λ) β 0 ≤
        MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ (f₀ * f₀)
          - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ f₀) ^ 2) :
    ∃ ν : State (IConf G),
      IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μ) ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν :=
  clay_nontriviality_of_wilson_variance G (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μ)
    (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀)
    (MassGap.WilsonDLR.hcons_specState hφc hφ0 hφ2 β μ ω₀) f₀ β hβ ap hbridge

#print axioms clay_nontriviality_of_wilson_bridge


/-- The contact floor with its positivity attached: there is `δ₀` with `0 < δ₀` such that for every
aperture `N` and every `β` with `0 ≤ β`, the constant `Real.exp (-(128 * β)) * δ₀` is positive and
at most `wilsonCorrAt N β 0`. Unpacks `InfiniteVolume.exists_uniform_contact_floor` and pairs each
 instance with `mul_pos (Real.exp_pos _) hδ₀`.

Scope: `δ₀` is bound outside the quantifier over `N`, so the constant is uniform in the aperture.
It depends on `β` through the exponential factor, so it is not uniform in the coupling. By
`PlaqVariance.corrClay_zero_eq` the quantity bounded below is the connected correlation of a
plaquette observable with itself.

DERIVED: `0` is the strict lower bound on `δ₀` and on the product, the lower bound on `β`, and the
contact lag in `wilsonCorrAt N β 0`; `128` is `exists_uniform_contact_floor`'s own exponent,
`16 * dim` at `dim = 4` doubled, transcribed unchanged. -/
theorem uniform_variance_floor_exists :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      0 < Real.exp (-(128 * β)) * δ₀ ∧
      Real.exp (-(128 * β)) * δ₀ ≤ MassGap.wilsonCorrAt N β 0 := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  exact ⟨δ₀, hδ₀, fun N β hβ => ⟨mul_pos (Real.exp_pos _) hδ₀, hfloor N β hβ⟩⟩

#print axioms uniform_variance_floor_exists

/-- The floor with the witness existentially quantified and no family in sight: for every aperture
`N` and every `β` with `0 ≤ β`, there is `c` with `0 < c` and `c ≤ wilsonCorrAt N β 0`. The witness
is `Real.exp (-(128 * β)) * δ₀` from `InfiniteVolume.exists_uniform_contact_floor`.

Scope: the statement mentions no state family, no kernel and no consistency relation, so it records
what the floor gives on its own. It is a lower bound at a fixed aperture and coupling; unlike
`uniform_variance_floor_exists` the witness `c` is bound inside the quantifiers over `N` and `β`, so
this form carries no uniformity.

DERIVED: the one numeral is `0`, the lower bound on `β`, the strict lower bound on `c`, and the
contact lag in `wilsonCorrAt N β 0`. The `128` of the witness is in the proof term, not the
statement. -/
theorem floor_is_independent_of_any_family (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ c ≤ MassGap.wilsonCorrAt N β 0 := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  exact ⟨Real.exp (-(128 * β)) * δ₀, mul_pos (Real.exp_pos _) hδ₀, hfloor N β hβ⟩

#print axioms floor_is_independent_of_any_family

end MassGap.ClayNontriviality
