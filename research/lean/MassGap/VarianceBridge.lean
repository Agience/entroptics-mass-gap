import Mathlib
import MassGap.ClayNontriviality
import MassGap.ClayAssembly
import MassGap.LagTwoEight
import MassGap.FreeFieldLagTwoSix
import MassGap.SubstrateArms
import MassGap.WilsonOS

/-!
# MassGap.VarianceBridge — the size requirement removed from Part IV's input

`ClayNontriviality.clay_nontriviality_of_wilson_bridge` takes `hbridge`: at every region `Λ`, the
finite-torus contact value is at most the infinite-volume state's variance of an observable `f₀`,

    wilsonCorrAt (ap Λ) β 0  ≤  ν Λ (f₀ * f₀) − (ν Λ f₀)²

**That hypothesis has no witness.** `wilson_bridge_hypothesis_unsatisfiable` refutes it: at `Λ = ∅`
the specification kernel is a point evaluation (`spec_empty`), so the variance is `0`
(`variance_at_empty_eq_zero`) while `PlaqVariance.corrClay_zero_pos` keeps the torus side strictly
positive at every extent and coupling. `clay_nontriviality_of_wilson_bridge` is therefore vacuous, and
it has no caller.

## What this file establishes

**1. Weakening the SIZE requirement does not help.** `hbridge` asks two things at once: that the
variance be positive, and that it be large enough to clear the torus side. The second is free —
a `DLRLimit.State` is homogeneous, so the variance of `c • f` is `c²` times that of `f`
(`variance_smul`), while the torus side is bounded by `4` with no hypothesis at all
(`InfiniteVolume.wilsonCorrAt_abs_le_four`). `bridge_of_uniform_variance_floor` and
`wilson_bridge_of_uniform_variance_floor` carry out that reduction, leaving a floor `δ > 0` holding
UNIFORMLY in the region.

**That form is unsatisfiable too**, by `uniform_variance_floor_unsatisfiable`, and for the same
reason: `∅` is still a region. So section 1 is a dead end, and neither of its two bridges has a
caller anywhere in the tree. The obstruction was never the size requirement.

**2. Weakening the QUANTIFIER does.** `nondegenerate_of_eventual_variance_floor` asks for the floor
only `∀ᶠ Λ in atTop`, which never mentions `∅`, and reaches the same conclusion — the universal form
was a strengthening introduced by `DLRLimit.exists_infinite_volume_gibbs_state_nondegenerate` and
used nowhere. `clay_nontriviality_of_eventual_variance_floor` is Part IV at the Wilson objects.

**3. The four parts, conjoined.** `clay_four_parts` states all of the Clay statement from
`ApertureRoute.ConfinesAtAnAperture` and that eventual floor;
`clay_four_parts_of_lag_two_above_the_cut` does it from the two open inequalities directly.
-/

namespace MassGap.VarianceBridge

open MassGap.DLRLimit

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The variance of a `State` scales quadratically in the observable:
`ν ((c•f)*(c•f)) − (ν (c•f))² = c² · (ν (f*f) − (ν f)²)`.

`State.map_smul'` is homogeneity, and `(c•f)*(c•f) = (c*c)•(f*f)` pointwise.

DERIVED: the exponent `2` is what a variance is — the square of the mean subtracted from the mean of
the square — and `c * c` is that same square written for the pointwise step. No other numeral. -/
theorem variance_smul (ν : State X) (f : C(X, ℝ)) (c : ℝ) :
    ν ((c • f) * (c • f)) - (ν (c • f)) ^ 2
      = c ^ 2 * (ν (f * f) - (ν f) ^ 2) := by
  have hmul : (c • f) * (c • f) = (c * c) • (f * f) := by
    ext x
    simp [mul_comm, mul_assoc]
  rw [hmul, ν.map_smul' (c * c) (f * f), ν.map_smul' c f]
  ring

#print axioms variance_smul

/-- **THE SIZE REQUIREMENT IS FREE.** Given a variance floor `δ > 0` holding at every region, and any
region-indexed quantity `T` bounded above by a constant `M`, there is an observable whose variance
clears `T` everywhere: scale `f` by `√(M/δ)` when `M` is positive, and by anything when it is not.

So a hypothesis of the shape "the torus value is at most the state's variance" splits into a
POSITIVE UNIFORM VARIANCE, which is a statement about the infinite-volume state alone, and a bound on
the torus side, which is already proved.

DERIVED: `0` is the sign of `δ` and of the scale; `2` is the variance's own square, through
`variance_smul`. `M` and `δ` are the caller's, and the scale `√(M/δ)` is read off the requirement
`c²·δ ≥ M` rather than chosen — it is that inequality solved at equality. -/
theorem bridge_of_uniform_variance_floor {ι : Type*} (ν : ι → State X) (f : C(X, ℝ))
    {δ M : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ L, δ ≤ ν L (f * f) - (ν L f) ^ 2)
    (T : ι → ℝ) (hT : ∀ L, T L ≤ M) :
    ∃ g : C(X, ℝ), ∀ L, T L ≤ ν L (g * g) - (ν L g) ^ 2 := by
  classical
  set c : ℝ := Real.sqrt (max M 0 / δ) with hc
  have hMδ : 0 ≤ max M 0 / δ := div_nonneg (le_max_right M 0) (le_of_lt hδ)
  have hcsq : c ^ 2 = max M 0 / δ := Real.sq_sqrt hMδ
  refine ⟨c • f, fun L => ?_⟩
  rw [variance_smul]
  have hvar : δ ≤ ν L (f * f) - (ν L f) ^ 2 := hfloor L
  have hcs : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  have hstep : c ^ 2 * δ ≤ c ^ 2 * (ν L (f * f) - (ν L f) ^ 2) :=
    mul_le_mul_of_nonneg_left hvar hcs
  have hval : c ^ 2 * δ = max M 0 := by
    rw [hcsq]; field_simp
  have hTM : T L ≤ max M 0 := le_trans (hT L) (le_max_left M 0)
  linarith [hstep, hval.symm.le, hval.le]

#print axioms bridge_of_uniform_variance_floor

/-- **Part IV's bridge, with the torus side discharged.** The finite-torus contact value is bounded
by `4` at every aperture and every coupling (`InfiniteVolume.wilsonCorrAt_abs_le_four`, which carries
no hypothesis), so a uniform positive variance floor is enough: some observable's variance clears the
torus contact value at every region.

This is what `ClayNontriviality.clay_nontriviality_of_wilson_bridge`'s `hbridge` asks for, with the
size requirement removed. What remains is a statement about the infinite-volume state alone — that
the variance of SOME observable is bounded below by a positive constant, uniformly in the region.

DERIVED: `4` is `InfiniteVolume.wilsonCorrAt_abs_le_four`'s bound on the connected correlation, its
own and not a scale chosen here; `0` is the sign of `δ` and the contact lag; `2` is the variance's
square. The aperture map `ap`, the coupling `β` and the observable are the caller's. -/
theorem wilson_bridge_of_uniform_variance_floor {ι : Type*} (ν : ι → State X) (f : C(X, ℝ))
    {δ : ℝ} (hδ : 0 < δ)
    (hfloor : ∀ L, δ ≤ ν L (f * f) - (ν L f) ^ 2)
    (ap : ι → ℕ) (β : ℝ) :
    ∃ g : C(X, ℝ), ∀ L, MassGap.wilsonCorrAt (ap L) β 0 ≤ ν L (g * g) - (ν L g) ^ 2 := by
  refine bridge_of_uniform_variance_floor ν f hδ hfloor
    (fun L => MassGap.wilsonCorrAt (ap L) β 0) (M := 4) (fun L => ?_)
  have h := MassGap.InfiniteVolume.wilsonCorrAt_abs_le_four (ap L) β 0
  exact le_trans (le_abs_self _) h

#print axioms wilson_bridge_of_uniform_variance_floor

/-! ## The degenerate region, where the bridge hypothesis is tested -/

section EmptyRegion

open MeasureTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [MeasurableMul₂ G]
  [MeasurableInv G]

omit [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G] in
/-- **The specification kernel at the empty region is a point evaluation.**
`GibbsSpec.spec φ β ∅ μ f ω = f ω`.

`GibbsSpec.splice ∅ u ω = ω` because no link lies inside, so the numerator's integrand is the
constant `f ω` times the weight; pulling the constant out leaves `f ω` times the partition function,
which `GibbsSpec.part_pos` keeps nonzero.

Names are written out rather than opened: `MassGap.GibbsSpec` and `MassGap.DLRLimit` each declare
`ILink` and `IConf`, so opening both makes every use ambiguous. They are the same type — `ISite` is
`Fin 4 → ℤ` in both — and `abbrev` is reducible, so the two names unify wherever either is expected.

DERIVED: `0` is the strict lower bound on the partition function, `GibbsSpec.part_pos`'s, and the
pointwise lower bound on the density; `2` is the density's upper bound. Both are `GibbsSpec`'s own
conditions on `φ`, carried unchanged. -/
theorem spec_empty {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (f : MassGap.GibbsSpec.IConf G → ℝ) (ω : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.spec φ β ∅ μ f ω = f ω := by
  have hsplice : ∀ u : MassGap.GibbsSpec.VConf G (∅ : Finset MassGap.GibbsSpec.ILink), MassGap.GibbsSpec.splice ∅ u ω = ω := by
    intro u
    funext l
    exact MassGap.GibbsSpec.splice_not_mem
      (by simp : l ∉ (∅ : Finset MassGap.GibbsSpec.ILink))
  have hpart : 0 < MassGap.GibbsSpec.part φ β ∅ μ ω := MassGap.GibbsSpec.part_pos hφc.measurable hφ0 hφ2 β ∅ μ ω
  have hnum : MassGap.GibbsSpec.num φ β ∅ μ f ω = f ω * MassGap.GibbsSpec.part φ β ∅ μ ω := by
    unfold MassGap.GibbsSpec.num MassGap.GibbsSpec.part
    have hfun : (fun u : MassGap.GibbsSpec.VConf G (∅ : Finset MassGap.GibbsSpec.ILink) => f (MassGap.GibbsSpec.splice ∅ u ω) * MassGap.GibbsSpec.wt φ β ∅ u ω)
        = fun u : MassGap.GibbsSpec.VConf G (∅ : Finset MassGap.GibbsSpec.ILink) => f ω * MassGap.GibbsSpec.wt φ β ∅ u ω := by
      funext u
      rw [hsplice u]
    rw [hfun, integral_const_mul]
  unfold MassGap.GibbsSpec.spec
  rw [hnum]
  field_simp

#print axioms spec_empty

/-- **The variance at the empty region is zero**, for every observable.

`spec_empty` makes the state a point evaluation there, and a point evaluation's second moment is the
square of its first.

DERIVED: `0` is the variance concluded and the density's lower bound; `2` is the variance's own
square and the density's upper bound. -/
theorem variance_at_empty_eq_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω₀ : MassGap.GibbsSpec.IConf G) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ ∅ (f * f)
      - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ ∅ f) ^ 2 = 0 := by
  have h1 : MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ ∅ f = f ω₀ :=
    spec_empty hφc hφ0 hφ2 β μ (⇑f) ω₀
  have h2 : MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ ∅ (f * f) = f ω₀ * f ω₀ := by
    -- `simpa` rewrote `⇑(f * f)` to `⇑f * ⇑f` and the two sides stopped matching; keep the
    -- coercion as the state applies it and finish with the pointwise product's own `rfl`.
    have h := spec_empty hφc hφ0 hφ2 β μ (⇑(f * f)) ω₀
    have hpt : (f * f) ω₀ = f ω₀ * f ω₀ := rfl
    rw [← hpt]
    exact h
  rw [h1, h2]
  ring

#print axioms variance_at_empty_eq_zero

/-- **`clay_nontriviality_of_wilson_bridge`'s hypothesis cannot be satisfied.**

`hbridge` is quantified over EVERY finite region. At the empty one the variance is zero
(`variance_at_empty_eq_zero`) while the torus contact value is strictly positive at every extent and
every real coupling (`PlaqVariance.corrClay_zero_pos`, which carries no hypotheses). So the
inequality reads "a positive number is at most zero", for every choice of `ap`, `f`, `ω₀` and `β`.

Part IV therefore rests on a hypothesis nothing can discharge, and the theorem taking it is
vacuously true.

This refutes the ROUTE, not non-triviality. The repair is to quantify the bridge over regions large
enough to carry the observable rather than over all of them — the empty region has no observable to
be non-trivial about.

DERIVED: `0` is the contact lag, the variance at the empty region, the density's lower bound, and
the strict lower bound `corrClay_zero_pos` concludes; `2` is the variance's square and the density's
upper bound; `1` is the `N + 1` extent offset `corrClay_zero_pos` is stated at. -/
theorem wilson_bridge_hypothesis_unsatisfiable {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω₀ : MassGap.GibbsSpec.IConf G) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) (ap : Finset MassGap.GibbsSpec.ILink → ℕ) :
    ¬ (∀ Λ : Finset MassGap.GibbsSpec.ILink,
        MassGap.wilsonCorrAt (ap Λ) β 0
          ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ (f * f)
            - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ f) ^ 2) := by
  intro hbridge
  have hzero := variance_at_empty_eq_zero hφc hφ0 hφ2 β μ ω₀ f
  have hpos : 0 < MassGap.wilsonCorrAt (ap ∅) β 0 :=
    MassGap.PlaqVariance.corrClay_zero_pos (ap ∅) β
  have h := hbridge ∅
  rw [hzero] at h
  linarith

#print axioms wilson_bridge_hypothesis_unsatisfiable

/-- **The UNIFORM variance floor is unsatisfiable too** — there is no positive `δ` below the
variance of a fixed observable at every region.

`wilson_bridge_hypothesis_unsatisfiable` refutes the torus-comparison form. This refutes the form
section 1 reduces it to: `bridge_of_uniform_variance_floor` asks for `δ > 0` with
`δ ≤ ν L (f*f) − (ν L f)²` at every `L`, and at `L = ∅` the variance is `0` by
`variance_at_empty_eq_zero`, whatever the observable. So `δ ≤ 0`.

Section 1's reduction is therefore dead at the Wilson instance: removing the SIZE requirement from
`hbridge` leaves a hypothesis that is still empty, because the obstruction was never the size but the
empty region. Neither `bridge_of_uniform_variance_floor` nor
`wilson_bridge_of_uniform_variance_floor` has a caller anywhere in the tree.

What survives is the `Repair` section below, where the floor is asked only EVENTUALLY in the region
and so never mentions `∅`.

DERIVED: `0` is the strict lower bound asserted of `δ`, the value the variance takes at the empty
region, and the lower bound on the density; `2` is the density's upper bound and the square of the
first moment in the variance. -/
theorem uniform_variance_floor_unsatisfiable {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω₀ : MassGap.GibbsSpec.IConf G) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    ¬ (∃ δ : ℝ, 0 < δ ∧ ∀ Λ : Finset MassGap.GibbsSpec.ILink,
        δ ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ (f * f)
          - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ f) ^ 2) := by
  rintro ⟨δ, hδ, hfloor⟩
  have hzero := variance_at_empty_eq_zero hφc hφ0 hφ2 β μ ω₀ f
  have h := hfloor ∅
  rw [hzero] at h
  linarith

#print axioms uniform_variance_floor_unsatisfiable

end EmptyRegion

/-! ## The repair — the floor is only needed eventually -/

section Repair

open Filter

/-- **Non-degeneracy from an EVENTUAL variance floor.**

`DLRLimit.exists_infinite_volume_gibbs_state_nondegenerate` asks for the floor at every region and
reaches its conclusion through `DLRLimit.not_isPointMass_of_uniform_variance`, which takes an
`∀ᶠ` hypothesis — the universal one is wrapped with `Filter.Eventually.of_forall` at that layer and
the extra strength is used nowhere.

`DLRLimit.exists_dlr_state` returns the ultrafilter with `u ≤ atTop`, so an `atTop`-eventual floor
transports to it by `Filter.Eventually.filter_mono`. The conclusion is unchanged; the hypothesis
stops mentioning the small regions, and in particular stops mentioning the empty one, where
`wilson_bridge_hypothesis_unsatisfiable` shows the variance is zero.

DERIVED: `0` is the strict lower bound on `c`; `1` is the unit observable and the normalisation
`ν 1 = 1`; `2` is the square of the first moment in the variance. All are
`exists_infinite_volume_gibbs_state_nondegenerate`'s, carried unchanged. -/
theorem nondegenerate_of_eventual_variance_floor (G : Type) [TopologicalSpace G] [CompactSpace G]
    (γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ))
    (μ : Finset ILink → State (IConf G))
    (hcons : ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ), μ Λ (γ Λ' f) = μ Λ f)
    (f₀ : C(IConf G, ℝ)) (c : ℝ) (hc : 0 < c)
    (hvar : ∀ᶠ Λ : Finset ILink in atTop, c ≤ μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2) :
    ∃ ν : State (IConf G), IsDLR γ ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν := by
  classical
  obtain ⟨u, ν, hle, htend, hdlr⟩ := exists_dlr_state γ μ hcons
  haveI hub : (u : Filter (Finset ILink)).NeBot := u.neBot'
  obtain ⟨hone, hpm⟩ :=
    not_isPointMass_of_uniform_variance htend f₀ c hc (hvar.filter_mono hle)
  exact ⟨ν, hdlr, hone, hpm⟩

#print axioms nondegenerate_of_eventual_variance_floor

/-- **Part IV, repaired.** The Wilson instance of the previous theorem: an eventual variance floor
for `WilsonDLR.specState` gives a state that is DLR for `WilsonDLR.specCM`, normalised, and not a
point mass.

This replaces `ClayNontriviality.clay_nontriviality_of_wilson_bridge`, whose hypothesis
`wilson_bridge_hypothesis_unsatisfiable` refutes: that one asks for the bound at every region, and at
the empty region the kernel is a point evaluation with variance zero while the torus contact value is
strictly positive.

The consistency relation is `WilsonDLR.hcons_specState`, so the floor is the only hypothesis not
instantiated from the tree — and it is now a statement about the infinite-volume family at large
regions alone, with no torus quantity and no size requirement in it.

DERIVED: `0` is the lower bound on the density, on the coupling and on `c`; `2` is the density's
upper bound and the variance's square; `1` is the unit observable and the normalisation. All are
inherited from the theorem composed and from `WilsonDLR.specState`'s own conditions. -/
theorem clay_nontriviality_of_eventual_variance_floor {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [MeasurableMul₂ G] [MeasurableInv G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
    (ω₀ : IConf G) (f₀ : C(IConf G, ℝ)) (c : ℝ) (hc : 0 < c)
    (hvar : ∀ᶠ Λ : Finset ILink in atTop,
      c ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ (f₀ * f₀)
        - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀ Λ f₀) ^ 2) :
    ∃ ν : State (IConf G),
      IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μ) ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν :=
  nondegenerate_of_eventual_variance_floor G
    (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μ)
    (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω₀)
    (MassGap.WilsonDLR.hcons_specState hφc hφ0 hφ2 β μ ω₀) f₀ c hc hvar

#print axioms clay_nontriviality_of_eventual_variance_floor

end Repair

/-! ## The four parts in one statement -/

section FourParts

open Filter

/-- **THE FOUR PARTS, CONJOINED.**

Everything the Clay statement asks for, from two hypotheses and nothing else:

1. **Parts I and II**, as `ApertureRoute.FlagshipAt`: the mode sum tends to zero in the separation,
   the tension stays strictly below the entropy floor at every coupling, the directional read is
   independent of direction, and a subsequence of the Schwinger functions converges to a bounded,
   nonnegative limit invariant under the gauge and plaquette actions.
2. **Part III**, reconstruction: a Wightman theory from Osterwalder–Schrader data whose Schwinger
   form is the `SU(N)` Wilson Gibbs reflected pairing, with test space and state space both
   non-trivial.
3. **Part IV**, non-triviality: an infinite-volume DLR state, normalised, and not a point mass.

`hc` gives 1 and 2; `hvar` gives 3. **Part III follows from neither** —
`WilsonOS.wilson_reconstructed_nontrivial` assumes no hypothesis, and its conjunct appears because the
Clay statement asks for it. It is unconditional in hypotheses, NOT in axioms: it is where the cited
reconstruction axiom `os_reconstruction_wightman` enters, and it is the only place any named axiom
enters this statement. Its lattice is its own, which is why this theorem carries a coupling `β`
for the infinite-volume side and a separate `βsl` for the slab.

**Why `ConfinesAtAnAperture` and not one route's own hypothesis.** Three lag-two obligations reduce
to it, at three extents — `LagTwoBound.confines_of_lag_two_ratio`,
`LagTwoSix.confines_of_lagTwoRatioSix` and `LagTwoEight.confines_of_lagTwoRatioEight` — and
`ApertureRoute.flagship_of_confinement_at_an_aperture` carries it the rest of the way. Taking the
common interface leaves the capstone unchanged whichever of the three is discharged first, so no
choice between them is baked into the assembled claim.

It is also the weakest form available. `ClayAssembly.flagship_of_clayRemaining` reaches the same
place from `ClayRemaining`, but that structure has a second field, `I2_clustering`, which the
flagship route never reads — `lagTwoRatioSix_of_clayRemaining` destructures `I1_lagTwo` alone.
Carrying it would make Parts I and II look as though they need a clustering constant. They do not;
`SubstrateArms` is where that field's consumers are.

`SubstrateArms.clay_assembly_of_spectral_rate` reaches the first two parts from a geometric spectral
rate instead. That is a different and stronger hypothesis standing beside the one the development is
reducing, so it is not what the assembled claim is built on.

**SCOPE — which gauge group this covers.** The Clay statement asks for any compact simple gauge
group. This does not deliver that, and the parts disagree: Part IV is stated at an arbitrary compact
`G`, Part III at `SU(N)` for any `N ≠ 0`, but Parts I and II are `SU(3)` in four dimensions and
nothing else — `WilsonBridge.corrClay` is `corrHyper (d := 4) 3 n 0 1 2`, so the colour rank and the
dimension are written into the definition every lag-two obligation is stated against rather than
supplied by a caller. The narrowest part governs, so **this theorem is an `SU(3)` statement in four
dimensions.** That is the physically intended case, and a limit of generality rather than a defect,
but the conjunction must not be read as more than it is.

DERIVED: every numeral is carried in from the declaration it belongs to, and this statement
introduces none. `0` — the sign condition on `msl` and on `cvar`, and the index of the family member
pinned to the unit. `1` — the family index offset `ksl + 1`, the unit observable, and the
normalisation `ν 1 = 1`. `2` — the reflection geometry `nsl = 2 * msl`, the upper bound on the density
`φ`, and the square of the first moment in the variance. -/
theorem clay_four_parts
    -- Parts I and II: confinement at some aperture, whichever route supplies it
    (hc : MassGap.ApertureRoute.ConfinesAtAnAperture)
    -- Part III: the slab carrying the reflected form, and a family whose first member is the unit
    {dsl nsl Nsl : ℕ} [NeZero nsl] (hNsl : Nsl ≠ 0) (τ : Fin dsl) (a : Fin nsl) (msl : ℕ)
    (hsl : nsl = 2 * msl) (hsl0 : 0 < msl) (βsl : ℝ) (ksl : ℕ)
    (v : Fin (ksl + 1) → ↥(MassGap.WilsonOS.slabMod dsl nsl Nsl τ a msl))
    (hv : v 0 = MassGap.WilsonOS.slabOne dsl nsl Nsl τ a msl)
    -- Part IV: an eventual variance floor for the infinite-volume family
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [MeasurableMul₂ G]
    [MeasurableInv G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μG : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μG]
    (ω₀ : IConf G) (f₀ : C(IConf G, ℝ)) (cvar : ℝ) (hcvar : 0 < cvar)
    (hvar : ∀ᶠ Λ : Finset ILink in atTop,
      cvar ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μG ω₀ Λ (f₀ * f₀)
        - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μG ω₀ Λ f₀) ^ 2) :
    -- 1, 2. the lattice gap and the Schwinger limit
    MassGap.ApertureRoute.FlagshipAt hc
    -- 3. reconstruction from the Wilson Gibbs reflected form
    ∧ (Nontrivial (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv).Test ∧
        Nontrivial (MassGap.WightmanData.os_reconstruction_wightman
          (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv)).Space)
    -- 4. non-triviality of the infinite-volume state
    ∧ (∃ ν : State (IConf G),
        IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μG) ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν) :=
  ⟨MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture hc,
    MassGap.WilsonOS.wilson_reconstructed_nontrivial hNsl τ a msl hsl hsl0 βsl ksl v hv,
    clay_nontriviality_of_eventual_variance_floor hφc hφ0 hφ2 β μG ω₀ f₀ cvar hcvar hvar⟩

#print axioms clay_four_parts

/-- **The capstone at the extent-eight obligation.** `LagTwoRatioEight` is one real constant below
`lagTwoThresholdEight` bounding `ρ(2)` by `K·ρ(0)` at every nonnegative coupling, and
`LagTwoEight.confines_of_lagTwoRatioEight` supplies `hc` from it.

The six- and four-extent obligations instantiate `clay_four_parts` the same way, through
`LagTwoSix.confines_of_lagTwoRatioSix` and `LagTwoBound.confines_of_lag_two_ratio`. This corollary
exists to record that the capstone is reachable from a named lag-two obligation and not only from an
abstract `ConfinesAtAnAperture`.

**The three are not ordered by strength.** `lagTwoThresholdSix_lt_lagTwoThresholdEight` compares two
closed-form reals and nothing else — and `admissible_at_eight_of_admissible_at_six`, which looks like
a transport, is one `lt_trans` on constants mentioning no correlation function. Each threshold bounds
the lag-two ratio of a DIFFERENT function: `wilsonCorrAt 3`, `wilsonCorrAt 5` and `wilsonCorrAt 7` are
`corrClay` at periodic extent four, six and eight, three measures on three lattices with no transport
between them. A larger threshold is a weaker hypothesis only when the bounded object is held fixed,
and it is not. The three routes are independent alternatives; discharging one says nothing about the
others, which is why `clay_four_parts` takes the interface they share rather than any one of them.

DERIVED: this corollary restates the full conclusion, so it carries the same numerals as
`clay_four_parts` and introduces none. `0` — the sign condition on `msl` and on `cvar`, and the index
of the family member pinned to the unit. `1` — the family index offset `ksl + 1`, the unit
observable, and the normalisation `ν 1 = 1`. `2` — the reflection geometry `nsl = 2 * msl`, the upper
bound on the density `φ`, and the square of the first moment in the variance. -/
theorem clay_four_parts_of_lagTwoRatioEight (h8 : MassGap.LagTwoEight.LagTwoRatioEight)
    {dsl nsl Nsl : ℕ} [NeZero nsl] (hNsl : Nsl ≠ 0) (τ : Fin dsl) (a : Fin nsl) (msl : ℕ)
    (hsl : nsl = 2 * msl) (hsl0 : 0 < msl) (βsl : ℝ) (ksl : ℕ)
    (v : Fin (ksl + 1) → ↥(MassGap.WilsonOS.slabMod dsl nsl Nsl τ a msl))
    (hv : v 0 = MassGap.WilsonOS.slabOne dsl nsl Nsl τ a msl)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [MeasurableMul₂ G]
    [MeasurableInv G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μG : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μG]
    (ω₀ : IConf G) (f₀ : C(IConf G, ℝ)) (cvar : ℝ) (hcvar : 0 < cvar)
    (hvar : ∀ᶠ Λ : Finset ILink in atTop,
      cvar ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μG ω₀ Λ (f₀ * f₀)
        - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μG ω₀ Λ f₀) ^ 2) :
    MassGap.ApertureRoute.FlagshipAt
      (MassGap.LagTwoEight.confines_of_lagTwoRatioEight h8)
    ∧ (Nontrivial (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv).Test ∧
        Nontrivial (MassGap.WightmanData.os_reconstruction_wightman
          (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv)).Space)
    ∧ (∃ ν : State (IConf G),
        IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μG) ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν) :=
  clay_four_parts (MassGap.LagTwoEight.confines_of_lagTwoRatioEight h8)
    hNsl τ a msl hsl hsl0 βsl ksl v hv hφc hφ0 hφ2 β μG ω₀ f₀ cvar hcvar hvar

#print axioms clay_four_parts_of_lagTwoRatioEight


/-- **THE WHOLE CLAIM, FROM TWO HYPOTHESES.**

All four parts of the Clay statement from exactly two named hypotheses and Part III's own lattice
data:

* `habove` — the lag-two ratio bound `ρ(2) ≤ K·ρ(0)` on `[strongCutSix hK0, ∞)`, the single named
  cut `LagTwoSix.exists_cut_lag_two_ratio_six` returns. Below that cut the bound is already proved,
  at every `K > 0`. `K` is any real below the closed-form `LagTwoSix.lagTwoThresholdSix`.
* `hvar` — an eventual variance floor for `WilsonDLR.specState`.

Part III assumes no hypothesis and depends on neither. It is unconditional in hypotheses, NOT in
axioms: it is where the cited reconstruction axiom `os_reconstruction_wightman` enters, and it is the
only place any named axiom enters this statement.

This is `clay_four_parts` with `ConfinesAtAnAperture` discharged by
`FreeFieldLagTwoSix.lagTwoRatioSix_of_above_strongCut` through
`LagTwoSix.confines_of_lagTwoRatioSix`. Where `clay_four_parts` is right to take the interface
abstractly — three lag-two routes supply it, at three extents, and they are independent alternatives
— this one records what supplying it actually costs on the route the development is reducing.

**Scope is `clay_four_parts`'s**: Parts I and II are `SU(3)` in four dimensions, because
`WilsonBridge.corrClay` fixes the colour rank and the dimension in its definition. The narrowest part
governs, so this is an `SU(3)` statement.

DERIVED: every numeral is `clay_four_parts`'s or `lagTwoRatioSix_of_above_strongCut`'s, carried
unchanged, and this declaration introduces none. `0` — the sign conditions on `K`, `msl`, `cvar` and
the coupling, the contact lag, and the index of the family member pinned to the unit. `1` — the family
index offset `ksl + 1`, the unit observable, and the normalisation `ν 1 = 1`. `2` — the lag the ratio
is taken at, the reflection geometry `nsl = 2 * msl`, the density's upper bound, and the variance's
square. `5` — the aperture index, `corrClay` at periodic extent six. -/
theorem clay_four_parts_of_lag_two_above_the_cut
    -- Parts I and II: one inequality above the strong cut
    {K : ℝ} (hK0 : 0 < K) (hKlt : K < MassGap.LagTwoSix.lagTwoThresholdSix)
    (habove : ∀ β : ℝ, MassGap.FreeFieldLagTwoSix.strongCutSix hK0 ≤ β →
      MassGap.wilsonCorrAt 5 β 2 ≤ K * MassGap.wilsonCorrAt 5 β 0)
    -- Part III: the slab, unconditional
    {dsl nsl Nsl : ℕ} [NeZero nsl] (hNsl : Nsl ≠ 0) (τ : Fin dsl) (a : Fin nsl) (msl : ℕ)
    (hsl : nsl = 2 * msl) (hsl0 : 0 < msl) (βsl : ℝ) (ksl : ℕ)
    (v : Fin (ksl + 1) → ↥(MassGap.WilsonOS.slabMod dsl nsl Nsl τ a msl))
    (hv : v 0 = MassGap.WilsonOS.slabOne dsl nsl Nsl τ a msl)
    -- Part IV: an eventual variance floor
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [MeasurableMul₂ G]
    [MeasurableInv G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μG : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μG]
    (ω₀ : IConf G) (f₀ : C(IConf G, ℝ)) (cvar : ℝ) (hcvar : 0 < cvar)
    (hvar : ∀ᶠ Λ : Finset ILink in atTop,
      cvar ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μG ω₀ Λ (f₀ * f₀)
        - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μG ω₀ Λ f₀) ^ 2) :
    MassGap.ApertureRoute.FlagshipAt
      (MassGap.LagTwoSix.confines_of_lagTwoRatioSix
        (MassGap.FreeFieldLagTwoSix.lagTwoRatioSix_of_above_strongCut hK0 hKlt habove))
    ∧ (Nontrivial (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv).Test ∧
        Nontrivial (MassGap.WightmanData.os_reconstruction_wightman
          (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv)).Space)
    ∧ (∃ ν : State (IConf G),
        IsDLR (MassGap.WilsonDLR.specCM hφc hφ0 hφ2 β μG) ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν) :=
  clay_four_parts
    (MassGap.LagTwoSix.confines_of_lagTwoRatioSix
      (MassGap.FreeFieldLagTwoSix.lagTwoRatioSix_of_above_strongCut hK0 hKlt habove))
    hNsl τ a msl hsl hsl0 βsl ksl v hv hφc hφ0 hφ2 β μG ω₀ f₀ cvar hcvar hvar

#print axioms clay_four_parts_of_lag_two_above_the_cut

end FourParts

end MassGap.VarianceBridge
