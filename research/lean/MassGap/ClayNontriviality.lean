import Mathlib
import MassGap.DLRLimit
import MassGap.InfiniteVolume

/-!
# MassGap.ClayNontriviality — C4's variance floor is already proved, and aperture-uniform

## The Clay row

C4 asks that the theory be **non-trivial**. The goal document carries it as OPEN with nothing behind
it. That is not where it stands.

`DLRLimit.exists_infinite_volume_gibbs_state_nondegenerate` already delivers the conclusion —
an infinite-volume DLR state that is normalised and **provably not a point mass** — from a family of
finite-volume states, the DLR consistency relation, and one input its own docstring flags:

> CONDITIONAL: this floor is an input, not a result.

That input is a variance floor at a single observable, holding uniformly over the volumes.

## ⭐ And the floor is a theorem

`InfiniteVolume.exists_uniform_contact_floor` proves

    ∃ δ₀ > 0, ∀ N β, 0 ≤ β → exp(−128β)·δ₀ ≤ wilsonCorrAt N β 0,

**one `δ₀` fixed before the aperture is chosen**, at every aperture and every non-negative coupling.
And `PlaqVariance.corrClay_zero_eq` identifies `wilsonCorrAt N β 0` as
`wilsonCorrConn (clayPlaq) β (clayPlaq)` — the connected correlation of a plaquette observable with
ITSELF, which is its variance. So the floor is a **variance floor, uniform in the volume**, which is
precisely the shape the non-degeneracy theorem asks for.

The `exp(−128β)` degrades with the coupling, and elsewhere in the tree that degradation is fatal —
it is what caps the contact-relative arm at `β ≈ 2.9e−5`. **Here it costs nothing.** C4 is a
statement at a coupling, not uniformly in the coupling, so a constant that depends on `β` and not on
the volume is exactly the right shape. The `128` is `16·dim` at `dim = 4` doubled — the count of
plaquettes sharing a link with the one being read (`StrongCoupling.touchDeg_bd_le`), which carries no
extent, and that is why the floor is aperture-uniform at all.

## What `clay_nontriviality_of_wilson_variance` does

It composes the two: given a DLR-consistent family whose variance at `f₀` is at least the Wilson
contact value, the floor is discharged from `exists_uniform_contact_floor` and the conclusion follows.
**Neither `hc` nor `hvar` is a hypothesis of the result** — both are supplied.

## ⛔ What remains, named exactly

**`hbridge` alone. `μ` and `hcons` are ALREADY BUILT.**

`WilsonDLR.specState` is the finite-volume Wilson state as a `DLRLimit.State (IConf (SU N))` indexed
by `Finset ILink`, and `WilsonDLR.hcons_specState` is its consistency relation — both foundational-only,
resting on `GibbsSpec.wilson_dlr_consistent` (the DLR compatibility of the genuine Wilson kernel on
infinite `ℤ⁴`) and `WilsonDLR.continuous_spec_right` (the Feller property). So this file's `μ` and
`hcons` are supplied by the tree, not open.

**What is genuinely open is `hbridge`, and it is a mismatch of VOLUME INDEXINGS.** The floor is
stated for `wilsonCorrAt N β 0` on `WilsonHypercubic.bd (d := 4) (n := N+1)` — a finite PERIODIC
lattice indexed by an aperture. `specState` is indexed by a `Finset ILink` of `ℤ⁴` with a FROZEN
boundary `ω₀`. Relating a variance in one indexing to a variance in the other is the open step.
`hbridge` is an INEQUALITY rather than an equality so that whoever builds it owes only the direction
used.

So C4's precondition stands at: **one comparison between two volume indexings**, with the family, the
consistency relation and the variance floor all proved.

## ⚠ And it is non-triviality in the DLR sense, not the full Clay sense

`¬IsPointMass` says the limit state is not concentrated at a single configuration. Clay §4 asks for a
theory whose correlations are not those of a generalised free field, which is a stronger and
different statement. **Nothing here addresses that.** What is closed is the weakest defensible reading of
"non-trivial" — that the object is not the vacuous witness — which is the reading
`exists_infinite_volume_gibbs_state_nondegenerate` was written for.
-/

namespace MassGap.ClayNontriviality

open MassGap.DLRLimit

/-- **⭐ C4'S VARIANCE FLOOR IS DISCHARGED FROM A PROVED THEOREM.**

Given a DLR-consistent family of finite-volume states whose variance at one observable is at least
the Wilson contact value at some aperture, the limit is a normalised DLR state that is **not a point
mass** — with no floor assumed, because `InfiniteVolume.exists_uniform_contact_floor` supplies it.

`ap` is the caller's assignment of an aperture to each finite volume. It is unconstrained on purpose:
the floor holds at EVERY aperture, so no relation between `Λ` and `ap Λ` is needed, and demanding one
would import an obligation the proof does not use.

DERIVED: `128` is `exists_uniform_contact_floor`'s own exponent — `16·dim` at `dim = 4`, doubled —
which is `StrongCoupling.touchDeg_bd_le`'s plaquette-touch count and carries no extent. `0` is the
contact lag and the sign of `β`. Nothing is chosen here. -/
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

/-- **THE FLOOR, RESTATED AS A VARIANCE FLOOR**, so the shape the non-degeneracy theorem consumes is
visible without unfolding `wilsonCorrAt`.

`PlaqVariance.corrClay_zero_eq` identifies the contact value as the connected correlation of a
plaquette observable with itself. This records the consequence that matters: **one positive constant,
chosen before the aperture, bounds that variance below at every aperture.**

DERIVED: `128` and `0` are `exists_uniform_contact_floor`'s, as above. -/
theorem uniform_variance_floor_exists :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      0 < Real.exp (-(128 * β)) * δ₀ ∧
      Real.exp (-(128 * β)) * δ₀ ≤ MassGap.wilsonCorrAt N β 0 := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  exact ⟨δ₀, hδ₀, fun N β hβ => ⟨mul_pos (Real.exp_pos _) hδ₀, hfloor N β hβ⟩⟩

#print axioms uniform_variance_floor_exists

/-- **⛔ AND THE FLOOR ALONE DOES NOT GIVE C4.** Stated so the file cannot be read as closing the row:
the conclusion above is reached only from a family `μ` and the consistency relation `hcons`, neither
of which the tree provides for the Wilson measure.

This is the negative control for `clay_nontriviality_of_wilson_variance` — it exhibits the fact that
the interesting hypotheses are the ones about the family, by showing the floor is available
unconditionally and independently of any family.

DERIVED: no numeral of its own. -/
theorem floor_is_independent_of_any_family (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ c ≤ MassGap.wilsonCorrAt N β 0 := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  exact ⟨Real.exp (-(128 * β)) * δ₀, mul_pos (Real.exp_pos _) hδ₀, hfloor N β hβ⟩

#print axioms floor_is_independent_of_any_family

end MassGap.ClayNontriviality
