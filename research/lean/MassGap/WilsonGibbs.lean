import Mathlib
import MassGap.GibbsSpec
import MassGap.InfiniteLattice
import MassGap.DLRLimit
import MassGap.WilsonDLR
import MassGap.SUN
import MassGap.WilsonAction

/-!
# MassGap.WilsonGibbs — the DLR equation against BOUNDED MEASURABLE observables

`WilsonDLR.exists_wilson_infinite_volume_gibbs_measure` produces a probability measure `P` on
`IConf (SU N)` satisfying `∫ spec wilsonDensity β Λ probHaar f dP = ∫ f dP` for every finite volume
`Λ` and every CONTINUOUS observable `f`. `GibbsSpec.IsGibbsMeasure` asks for the same equation
against every BOUNDED MEASURABLE observable, so the object produced there was a continuous
restriction of the object `GibbsSpec` defines. This file removes the restriction and lands
`IsGibbsMeasure` itself.

## How the extension is made

NOT by approximating an observable. Continuous functions are dense in `L¹(P)`, but the DLR equation
reads `f` twice — once against `P` and once against the kernel `spec … f ω`, which integrates `f`
against a DIFFERENT measure for each `ω` — and `L¹(P)`-convergence says nothing about the second.
`GibbsSpec.abs_spec_le` bounds the kernel by the SUP norm of the observable, not by its `L¹(P)`
norm, so a dominated limit along an `L¹(P)`-approximating sequence does not close.

What closes is the measure-level statement. The kernel applied to `P`,

    Q(A) = ∫ spec φ β Λ μ 1_A ω dP(ω),

is exhibited here as an honest measure `specMeasure`: the push-forward along the splice
`(ω, u) ↦ splice Λ u ω` of the product measure `P ⊗ vol μ Λ` weighted by the normalised Boltzmann
weight `wt / part`. Fubini on that product — legitimate because the weight is bounded above and
below uniformly in both arguments, `exp_neg_escale_le_part` being the lower bound — gives
`∫ f dQ = ∫ spec φ β Λ μ f dP` for EVERY bounded measurable `f` at once
(`integral_specMeasure`). The continuous DLR equation then says `Q` and `P` integrate every bounded
continuous function alike, and two finite Borel measures that do so on a pseudometrizable space are
equal (`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`). With `Q = P` the bounded
measurable equation is the bounded continuous one read at a different measure.

The pseudometrizability is not an extra hypothesis: `IConf G` is a topological group, hence regular,
and second countable when `G` is, and Urysohn's theorem does the rest
(`hasOuterApproxClosed_IConf`).

## What is proved

* `integral_specMeasure` — `∫ f d(specMeasure φ β Λ μ P) = ∫ spec φ β Λ μ f dP` for every bounded
  measurable `f`. The kernel applied to a measure IS a measure.
* `specMeasure_eq_self` — `specMeasure φ β Λ μ P = P` for a `P` satisfying the continuous DLR
  equation.
* `dlr_bounded_measurable` — the DLR equation at every bounded measurable observable.
* `exists_isGibbsMeasure_of_density` / `existsGibbsMeasure_of_density` — `GibbsSpec.IsGibbsMeasure`
  for a continuous plaquette density with values in `[0,2]`, at every real `β`; the second is
  `GibbsSpec.ExistsGibbsMeasure`, the proposition `GibbsSpec` flags as NOT PROVED THERE. Both also
  ask `G` to be Hausdorff and take the boundary configuration the finite-volume family is anchored
  at as a parameter, on top of the standing context of Part 2: a compact, second-countable, Borel
  topological group with measurable multiplication and inversion. `SU(N)` carries every one.
* `exists_wilson_isGibbsMeasure` — the same at the genuine `WilsonAction.wilsonDensity` on `SU(N)`
  against `CompactGauge.probHaar`, for every `N ≠ 0` and every real `β`. Row A6's object is now the
  one `GibbsSpec.IsGibbsMeasure` defines.
* `gibbsSpec_plaqsIn_eq` — the bridge between `GibbsSpec.plaqsIn` and `InfiniteLattice.plaqsIn`.
  They are extensionally equal and NOT defeq: the first filters `boundaryPlaqs Λ` by a `List.all`
  over `ilinks`, the second filters a site-image candidate set by `linksOf ⊆ Λ`. Both `mem_` lemmas
  say "every link the plaquette reads lies in `Λ`", so `Finset.ext` closes it.

## Duplicated skeletons

`GibbsSpec`, `InfiniteLattice` and `DLRLimit` each declare `ISite`, `ILink`, `IPlaq` and `IConf` in
their own namespace, in every case as the `abbrev`s `Fin 4 → ℤ`, `Fin 4 × ISite`,
`(Fin 4 × Fin 4) × ISite` and `ILink → G`. Being reducible abbreviations with identical bodies they
are interchangeable by `rfl`, which is what lets a statement in one namespace be read against a
measure built in another with no transport.

Below the types, the three bridges are of three different strengths, and the difference matters:

* the boundary WORDS are equal by `rfl` (`ibd_eq`) — same body, same `ishift`;
* the link SETS do not even share a type — `InfiniteLattice.linksOf q` is a `Finset`,
  `GibbsSpec.ilinks q` the `List` it is the `toFinset` of — so `mem_linksOf_iff` relates them by
  `List.mem_toFinset`, NOT by `rfl`;
* the two `plaqsIn` are equal neither by `rfl` nor by a coercion: they filter different candidate
  sets, and `gibbsSpec_plaqsIn_eq` is an extensional `Finset.ext` argument.

## What is NOT proved

Uniqueness of `P`, translation invariance, and non-degeneracy — exactly as in `WilsonDLR`. The
measure inherited here is the same subsequential limit, taken along an ultrafilter refining `atTop`
on finite volumes, and may depend on the frozen boundary configuration.

DERIVED: `4` is the dimension of the Clay problem; `2` is the proved upper bound on the plaquette
density (`WilsonAction.wilsonDensity_le_two`), `0` its proved lower bound
(`wilsonDensity_nonneg`), and `1` is the normalisation of a probability measure and the radius of
the ball of observables `IsGibbsMeasure` is stated on. No constant is chosen here and none is
fitted.

Foundational footprint only (`#print axioms` after every declaration).
Build: `python research/code/lean_build.py build MassGap.WilsonGibbs`.
-/

namespace MassGap.WilsonGibbs

open MeasureTheory
open MassGap.GibbsSpec MassGap.WilsonLattice

/-! ## Part 0 — the bridge between the two plaquette-set definitions

`GibbsSpec` and `InfiniteLattice` each carry a `plaqsIn`. The underlying boundary word is the same
list in both (`ibd_eq`, a `rfl`), so the link sets agree definitionally; the two `plaqsIn` do not,
because they filter different candidate sets. `gibbsSpec_plaqsIn_eq` is the one-line consequence, so
that nothing downstream has to rediscover it. -/

/-- **The two boundary words are the same list.** `GibbsSpec.ibd` and `InfiniteLattice.ibd` have
identical bodies over identical `ishift`s, so this is `rfl` and the two namespaces' plaquette
combinatorics are interchangeable.

DERIVED: no numeral appears in this statement. The word has four letters because a plaquette is a
square and has four edges, which is a count of the loop and not the dimension `4` that `ILink`
carries; neither is written here. -/
theorem ibd_eq (q : IPlaq) : MassGap.GibbsSpec.ibd q = MassGap.InfiniteLattice.ibd q := rfl

#print axioms ibd_eq

/-- **A link is read by a plaquette in one namespace exactly when it is in the other.**
`InfiniteLattice.linksOf` is the `Finset` of `GibbsSpec.ilinks`. -/
theorem mem_linksOf_iff {q : IPlaq} {l : ILink} :
    l ∈ MassGap.InfiniteLattice.linksOf q ↔ l ∈ MassGap.GibbsSpec.ilinks q :=
  List.mem_toFinset

#print axioms mem_linksOf_iff

/-- **The two `plaqsIn` agree.** `GibbsSpec.plaqsIn Λ` filters `boundaryPlaqs Λ` by a `List.all`
over `ilinks`; `InfiniteLattice.plaqsIn Λ` filters a candidate set built from the sites of `Λ` by
`linksOf q ⊆ Λ`. The candidate sets differ, so the two are NOT defeq, but both `mem_` lemmas say
"every link `q` reads lies in `Λ`". -/
theorem gibbsSpec_plaqsIn_eq (Λ : Finset ILink) :
    MassGap.GibbsSpec.plaqsIn Λ = MassGap.InfiniteLattice.plaqsIn Λ := by
  ext q
  rw [MassGap.GibbsSpec.mem_plaqsIn, MassGap.InfiniteLattice.mem_plaqsIn]
  constructor
  · intro h l hl
    exact h l (mem_linksOf_iff.mp hl)
  · intro h l hl
    exact h (mem_linksOf_iff.mpr hl)

#print axioms gibbsSpec_plaqsIn_eq

/-! ## Part 1 — the configuration space is pseudometrizable

This is what makes a finite Borel measure on `IConf G` determined by its integrals against bounded
continuous functions, and it costs no hypothesis that is not already carried: `IConf G` is a product
of topological groups, hence a topological group, hence regular; it is second countable because
`ILink` is countable and `G` is; and Urysohn's metrization theorem turns regular plus second
countable into pseudometrizable. -/

section Space

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **The configuration space is pseudometrizable.** Instance search only: topological group ⇒
regular, countable index and second countable factors ⇒ second countable, Urysohn ⇒ metrizable. -/
theorem pseudoMetrizable_IConf : TopologicalSpace.PseudoMetrizableSpace (IConf G) := inferInstance

#print axioms pseudoMetrizable_IConf

/-- **Indicators of closed sets are approximable from above on the configuration space.** The
hypothesis `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` runs on: a finite Borel
measure on such a space is determined by its integrals against bounded continuous functions.

This and `pseudoMetrizable_IConf` are witnesses, not steps: instance search finds the same two facts
unaided where `specMeasure_eq_self` needs them. They are stated so that a reader can see WHICH
property of the configuration space the measure-uniqueness argument spends, and check it here rather
than inside a failed elaboration. -/
theorem hasOuterApproxClosed_IConf : HasOuterApproxClosed (IConf G) := inferInstance

#print axioms hasOuterApproxClosed_IConf

end Space

/-! ## Part 2 — the working context

The same compact, second-countable, Borel topological group `WilsonDLR` works over; `SU(N)` carries
every instance in the block. -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-! ## Part 3 — the Boltzmann weight is bounded on BOTH sides

`GibbsSpec.wt_le` bounds the weight above. Fubini on `P ⊗ vol μ Λ` needs the NORMALISED weight
`wt / part` bounded above, which needs the partition function bounded BELOW — uniformly in the
boundary condition, since the boundary condition is one of the two integration variables. -/

/-- **The energy scale of a finite volume**: the largest the action of `boundaryPlaqs Λ` can
contribute to the exponent, in absolute value.

DERIVED: `2` is the proved upper bound on the plaquette density (`WilsonAction.wilsonDensity_le_two`
at the Wilson instance, the hypothesis `hφ2` in general), so `card * 2` is
`GibbsSpec.actionOn_le`'s bound on the action of a finite plaquette set, and `|β|` is the coupling
in absolute value. Nothing is chosen: this is the bound `actionOn_le` already proves, given a
name. -/
noncomputable def escale (β : ℝ) (Λ : Finset ILink) : ℝ :=
  |β| * (((boundaryPlaqs Λ).card : ℝ) * 2)

#print axioms escale

/-- **The energy scale is nonnegative.**

DERIVED: `0` is the additive identity, and `2` is the density bound carried by `escale`. -/
theorem escale_nonneg (β : ℝ) (Λ : Finset ILink) : 0 ≤ escale β Λ :=
  mul_nonneg (abs_nonneg β) (mul_nonneg (Nat.cast_nonneg _) (by norm_num))

#print axioms escale_nonneg

/-- **The Boltzmann weight is bounded below**, uniformly in the inside configuration AND the
boundary condition. `GibbsSpec.wt_le` is the matching upper bound.

DERIVED: `0` and `2` are the proved range of the plaquette density — `hφ0` and `hφ2`, discharged at
the Wilson instance by `wilsonDensity_nonneg` and `wilsonDensity_le_two`. The exponent is
`-escale β Λ`, whose numeral is declared at `escale`. -/
theorem exp_neg_escale_le_wt {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) :
    Real.exp (-escale β Λ) ≤ wt φ β Λ u ω := by
  unfold wt escale
  rw [Real.exp_le_exp]
  have h0 : 0 ≤ actionOn φ (boundaryPlaqs Λ) (splice Λ u ω) := actionOn_nonneg hφ0 _ _
  have h1 : actionOn φ (boundaryPlaqs Λ) (splice Λ u ω) ≤ (((boundaryPlaqs Λ).card : ℝ) * 2) :=
    actionOn_le hφ2 _ _
  have h2 : -|β| * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)
      ≤ -β * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω) :=
    mul_le_mul_of_nonneg_right (neg_le_neg (le_abs_self β)) h0
  have h3 : |β| * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)
      ≤ |β| * (((boundaryPlaqs Λ).card : ℝ) * 2) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
  linarith

#print axioms exp_neg_escale_le_wt

/-- **The partition function is bounded below, uniformly in the boundary condition.**
`GibbsSpec.part_pos` gives positivity at each `ω` separately, which is not enough to bound the
normalised weight on the product space; the bound here is one constant for all `ω`.

DERIVED: `0` and `2` are the proved range of the plaquette density, as in `exp_neg_escale_le_wt`. -/
theorem exp_neg_escale_le_part {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω : IConf G) : Real.exp (-escale β Λ) ≤ part φ β Λ μ ω := by
  unfold part
  calc Real.exp (-escale β Λ)
      = ∫ _u : VConf G Λ, Real.exp (-escale β Λ) ∂(vol μ Λ) := by simp
    _ ≤ ∫ u, wt φ β Λ u ω ∂(vol μ Λ) :=
        integral_mono (integrable_const _) (integrable_wt hφ hφ0 hφ2 β Λ μ ω)
          (fun u => exp_neg_escale_le_wt hφ0 hφ2 β Λ u ω)

#print axioms exp_neg_escale_le_part

/-- **The uniform bound on the normalised Boltzmann weight.**

DERIVED: `2` multiplying the energy scale is `exp a / exp (-a) = exp (2a)` — the upper bound on the
weight divided by the lower bound on the partition function, each at the scale `escale β Λ`. It is
arithmetic, not a coupling window; the numeral inside `escale` is declared there. -/
noncomputable def ratioBound (β : ℝ) (Λ : Finset ILink) : ℝ := Real.exp (2 * escale β Λ)

#print axioms ratioBound

/-- **The normalised weight is nonnegative.**

DERIVED: `0` is the additive identity; `2` is the density bound in `hφ2`. -/
theorem wt_div_part_nonneg {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (u : VConf G Λ) (ω : IConf G) : 0 ≤ wt φ β Λ u ω / part φ β Λ μ ω :=
  div_nonneg (wt_pos φ β Λ u ω).le (part_pos hφ hφ0 hφ2 β Λ μ ω).le

#print axioms wt_div_part_nonneg

/-- **The normalised weight is bounded above, uniformly in both arguments.** This is what makes the
integrand of the product integral in Part 4 bounded, hence integrable against the product of two
probability measures.

DERIVED: `0` and `2` are the proved range of the plaquette density. -/
theorem wt_div_part_le {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (u : VConf G Λ) (ω : IConf G) : wt φ β Λ u ω / part φ β Λ μ ω ≤ ratioBound β Λ := by
  have hp : 0 < part φ β Λ μ ω := part_pos hφ hφ0 hφ2 β Λ μ ω
  unfold ratioBound
  rw [div_le_iff₀ hp]
  calc wt φ β Λ u ω ≤ Real.exp (escale β Λ) := wt_le hφ0 hφ2 β Λ u ω
    _ = Real.exp (2 * escale β Λ) * Real.exp (-escale β Λ) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * escale β Λ) * part φ β Λ μ ω :=
        mul_le_mul_of_nonneg_left (exp_neg_escale_le_part hφ hφ0 hφ2 β Λ μ ω) (Real.exp_nonneg _)

#print axioms wt_div_part_le

/-! ## Part 4 — the kernel applied to a measure IS a measure

`spec φ β Λ μ f ω` is an integral against `vol μ Λ` of `f ∘ splice` weighted by `wt / part`. Read on
the product space `IConf G × VConf G Λ`, that is one integral against `P ⊗ vol μ Λ` of the same
integrand, and the push-forward of the weighted product along the splice is a measure whose integral
of ANY bounded measurable `f` is `∫ spec φ β Λ μ f dP`. No approximation of `f` anywhere. -/

/-- **The normalised Boltzmann weight as a density**, `ℝ≥0`-valued so that
`MeasureTheory.integral_withDensity_eq_integral_smul` applies directly.

DERIVED: no numeral appears; the nonnegativity that makes `Real.toNNReal` lossless here is
`wt_div_part_nonneg`. -/
noncomputable def dens (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (z : IConf G × VConf G Λ) : NNReal :=
  Real.toNNReal (wt φ β Λ z.2 z.1 / part φ β Λ μ z.1)

#print axioms dens

/-- **The density is measurable on the product.** `GibbsSpec.measurable_wt_prod` is joint in the two
arguments, which is exactly what the product space needs. -/
theorem measurable_dens {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] : Measurable (dens φ β Λ μ) := by
  unfold dens
  exact ((measurable_wt_prod hφ β Λ).div
    ((measurable_part_right hφ β Λ μ).comp measurable_fst)).real_toNNReal

#print axioms measurable_dens

/-- **The specification kernel applied to a measure.** The push-forward along the splice
`(ω, u) ↦ splice Λ u ω` of `P ⊗ vol μ Λ` weighted by the normalised Boltzmann weight. This is the
measure `∫ spec φ β Λ μ · ω dP(ω)` is the integral against — `integral_specMeasure` — and being a
measure by construction is the whole point: no countable additivity has to be proved for the
kernel. -/
noncomputable def specMeasure (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (P : Measure (IConf G)) : Measure (IConf G) :=
  ((P.prod (vol μ Λ)).withDensity (fun z => (dens φ β Λ μ z : ENNReal))).map
    (fun z => splice Λ z.2 z.1)

#print axioms specMeasure

/-- **The inner integral is the kernel.** Pure algebra: the partition function does not depend on
the inside configuration, so it comes out of the integral, and what is left is `num / part`. No
hypothesis on `φ`, `β` or `μ` is used. -/
theorem integral_wt_div_part (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (f : IConf G → ℝ) (ω : IConf G) :
    (∫ u, f (splice Λ u ω) * (wt φ β Λ u ω / part φ β Λ μ ω) ∂(vol μ Λ))
      = spec φ β Λ μ f ω := by
  have h : (fun u : VConf G Λ => f (splice Λ u ω) * (wt φ β Λ u ω / part φ β Λ μ ω))
      = fun u : VConf G Λ => (f (splice Λ u ω) * wt φ β Λ u ω) * (part φ β Λ μ ω)⁻¹ := by
    funext u
    rw [div_eq_mul_inv, ← mul_assoc]
  rw [h, integral_mul_const, ← div_eq_mul_inv]
  rfl

#print axioms integral_wt_div_part

/-- **THE KERNEL APPLIED TO A MEASURE, TESTED ON A BOUNDED MEASURABLE OBSERVABLE.** For every
bounded measurable `f`,

    ∫ f d(specMeasure φ β Λ μ P) = ∫ spec φ β Λ μ f dP.

Continuity of `f` is not used and no limit is taken: the equation is Fubini on
`P ⊗ vol μ Λ` for an integrand bounded by `C * ratioBound β Λ`, followed by the change of variables
along the splice and the change of measure along the density.

DERIVED: `0` and `2` are the proved range of the plaquette density (`hφ0`, `hφ2`); `1` in the
nonnegativity of `C` is the constant configuration the bound `hC` is evaluated at, chosen only
because SOME configuration is needed to see `0 ≤ C`, and any other gives the same conclusion. -/
theorem integral_specMeasure {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (P : Measure (IConf G)) [IsProbabilityMeasure P]
    {f : IConf G → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ U, |f U| ≤ C) :
    (∫ U, f U ∂(specMeasure φ β Λ μ P)) = ∫ ω, spec φ β Λ μ f ω ∂P := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 1))
  have hT : Measurable (fun z : IConf G × VConf G Λ => splice Λ z.2 z.1) :=
    measurable_splice_prod Λ
  have hFm : Measurable (fun z : IConf G × VConf G Λ =>
      f (splice Λ z.2 z.1) * (wt φ β Λ z.2 z.1 / part φ β Λ μ z.1)) :=
    (hf.comp hT).mul ((measurable_wt_prod hφ β Λ).div
      ((measurable_part_right hφ β Λ μ).comp measurable_fst))
  have hFb : ∀ z : IConf G × VConf G Λ,
      |f (splice Λ z.2 z.1) * (wt φ β Λ z.2 z.1 / part φ β Λ μ z.1)| ≤ C * ratioBound β Λ := by
    intro z
    rw [abs_mul, abs_of_nonneg (wt_div_part_nonneg hφ hφ0 hφ2 β Λ μ z.2 z.1)]
    exact mul_le_mul (hC _) (wt_div_part_le hφ hφ0 hφ2 β Λ μ z.2 z.1)
      (wt_div_part_nonneg hφ hφ0 hφ2 β Λ μ z.2 z.1) hCnn
  have hFint : Integrable (fun z : IConf G × VConf G Λ =>
      f (splice Λ z.2 z.1) * (wt φ β Λ z.2 z.1 / part φ β Λ μ z.1)) (P.prod (vol μ Λ)) :=
    integrable_of_bounded _ hFm hFb
  calc (∫ U, f U ∂(specMeasure φ β Λ μ P))
      = ∫ z, f (splice Λ z.2 z.1)
          ∂((P.prod (vol μ Λ)).withDensity (fun z => (dens φ β Λ μ z : ENNReal))) := by
        unfold specMeasure
        exact integral_map hT.aemeasurable hf.aestronglyMeasurable
    _ = ∫ z, dens φ β Λ μ z • f (splice Λ z.2 z.1) ∂(P.prod (vol μ Λ)) :=
        integral_withDensity_eq_integral_smul (measurable_dens hφ β Λ μ) _
    _ = ∫ z, f (splice Λ z.2 z.1) * (wt φ β Λ z.2 z.1 / part φ β Λ μ z.1)
          ∂(P.prod (vol μ Λ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        have hnn := wt_div_part_nonneg hφ hφ0 hφ2 β Λ μ z.2 z.1
        show dens φ β Λ μ z • f (splice Λ z.2 z.1)
            = f (splice Λ z.2 z.1) * (wt φ β Λ z.2 z.1 / part φ β Λ μ z.1)
        rw [NNReal.smul_def, smul_eq_mul, dens, Real.coe_toNNReal _ hnn]
        ring
    _ = ∫ ω, ∫ u, f (splice Λ u ω) * (wt φ β Λ u ω / part φ β Λ μ ω) ∂(vol μ Λ) ∂P :=
        integral_prod _ hFint
    _ = ∫ ω, spec φ β Λ μ f ω ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun ω => integral_wt_div_part φ β Λ μ f ω))

#print axioms integral_specMeasure

/-- **The kernel applied to a probability measure has total mass one.** The `f = 1` case of
`integral_specMeasure` together with `GibbsSpec.spec_one`.

DERIVED: `1` is the constant observable and the normalisation of a probability measure — the same
`1` on both sides, which is what the statement says. `0` and `2` are the proved range of the
plaquette density. -/
theorem specMeasure_univ_toReal {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (P : Measure (IConf G)) [IsProbabilityMeasure P] :
    ((specMeasure φ β Λ μ P) Set.univ).toReal = 1 := by
  calc ((specMeasure φ β Λ μ P) Set.univ).toReal
      = ∫ _U, (1 : ℝ) ∂(specMeasure φ β Λ μ P) := by
        rw [integral_const, smul_eq_mul, mul_one]
        rfl
    _ = ∫ ω, spec φ β Λ μ (fun _ => (1 : ℝ)) ω ∂P :=
        integral_specMeasure hφ hφ0 hφ2 β Λ μ P measurable_const (C := 1)
          (fun _ => by norm_num)
    _ = ∫ _ω, (1 : ℝ) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun ω => spec_one hφ hφ0 hφ2 β Λ μ ω))
    _ = 1 := by simp

#print axioms specMeasure_univ_toReal

/-- **The kernel applied to a probability measure is a probability measure.**

DERIVED: `1` is the normalisation, `0` and `2` the proved range of the plaquette density. -/
theorem isProbabilityMeasure_specMeasure {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (P : Measure (IConf G)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (specMeasure φ β Λ μ P) := by
  have h1 := specMeasure_univ_toReal hφ hφ0 hφ2 β Λ μ P
  have hne : specMeasure φ β Λ μ P Set.univ ≠ ⊤ := by
    intro htop
    rw [htop] at h1
    simp at h1
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_toReal hne, h1, ENNReal.ofReal_one]

#print axioms isProbabilityMeasure_specMeasure

/-! ## Part 5 — the continuous DLR equation forces the measure equation

Two finite Borel measures on a pseudometrizable space with the same integral against every bounded
continuous function are equal. `specMeasure` and `P` have that, by
`WilsonDLR.exists_infinite_volume_gibbs_measure_of_density`'s conclusion read through
`integral_specMeasure`. -/

/-- **The kernel fixes the measure.** For a `P` satisfying the DLR equation at continuous
observables, `specMeasure φ β Λ μ P = P` at every finite volume — an equality of MEASURES, from
which the bounded measurable equation follows by reading it at one observable.

DERIVED: `0` and `2` are the proved range of the plaquette density (`hφ0`, `hφ2`). -/
theorem specMeasure_eq_self {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (P : Measure (IConf G)) [IsProbabilityMeasure P]
    (hdlr : ∀ (Λ : Finset ILink) (f : C(IConf G, ℝ)),
      (∫ U, spec φ β Λ μ (⇑f) U ∂P) = ∫ U, f U ∂P)
    (Λ : Finset ILink) : specMeasure φ β Λ μ P = P := by
  haveI := isProbabilityMeasure_specMeasure hφc.measurable hφ0 hφ2 β Λ μ P
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (fun g => ?_)
  have hgm : Measurable (⇑g) := g.continuous.measurable
  have hgb : ∀ U, |g U| ≤ ‖g‖ := fun U => by
    simpa [Real.norm_eq_abs] using g.norm_coe_le_norm U
  calc (∫ U, g U ∂(specMeasure φ β Λ μ P))
      = ∫ ω, spec φ β Λ μ (⇑g) ω ∂P :=
        integral_specMeasure hφc.measurable hφ0 hφ2 β Λ μ P hgm hgb
    _ = ∫ U, g U ∂P := hdlr Λ g.toContinuousMap

#print axioms specMeasure_eq_self

/-- **THE DLR EQUATION AT EVERY BOUNDED MEASURABLE OBSERVABLE.** The conclusion
`GibbsSpec.IsGibbsMeasure` asks for, from the conclusion `WilsonDLR` delivers.

DERIVED: `1` is the radius of the ball of observables `IsGibbsMeasure` is stated on — by linearity
of both sides in `f` the statement at any other finite bound `B > 0` is this one applied to `f / B`,
so it is a normalisation and not a restriction. `0` and `2` are the proved range of the plaquette
density. -/
theorem dlr_bounded_measurable {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (P : Measure (IConf G)) [IsProbabilityMeasure P]
    (hdlr : ∀ (Λ : Finset ILink) (f : C(IConf G, ℝ)),
      (∫ U, spec φ β Λ μ (⇑f) U ∂P) = ∫ U, f U ∂P)
    (Λ : Finset ILink) (f : IConf G → ℝ) (hf : Measurable f) (hf1 : ∀ U, |f U| ≤ 1) :
    (∫ U, f U ∂P) = ∫ U, spec φ β Λ μ f U ∂P := by
  have h := integral_specMeasure hφc.measurable hφ0 hφ2 β Λ μ P hf hf1
  rwa [specMeasure_eq_self hφc hφ0 hφ2 β μ P hdlr Λ] at h

#print axioms dlr_bounded_measurable

/-! ## Part 6 — `IsGibbsMeasure`, for a general density and then for Wilson -/

/-- **THE INFINITE-VOLUME GIBBS MEASURE OF A BOUNDED CONTINUOUS PLAQUETTE DENSITY, AS
`GibbsSpec.IsGibbsMeasure`.** The measure is `WilsonDLR`'s; what is new is that it satisfies the DLR
equation against every bounded measurable observable and not only every continuous one, so it is a
Gibbs measure in the sense the specification's own definition names.

DERIVED: `0` and `2` are the proved range of the plaquette density — the hypotheses `hφ0` and
`hφ2`, discharged at the Wilson instance by `wilsonDensity_nonneg` and `wilsonDensity_le_two`. They
are the only numerals in the statement: the boundary configuration the finite-volume family is
anchored at is the PARAMETER `ω₀`, quantified over, so nothing is chosen here. -/
theorem exists_isGibbsMeasure_of_density [T2Space G] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω₀ : IConf G) : ∃ P : Measure (IConf G), IsGibbsMeasure φ β μ P := by
  obtain ⟨P, hP, hdlr⟩ :=
    MassGap.WilsonDLR.exists_infinite_volume_gibbs_measure_of_density hφc hφ0 hφ2 β μ ω₀
  haveI := hP
  exact ⟨P, hP, fun Λ f hf hf1 => dlr_bounded_measurable hφc hφ0 hφ2 β μ P hdlr Λ f hf hf1⟩

#print axioms exists_isGibbsMeasure_of_density

/-- **`GibbsSpec.ExistsGibbsMeasure`, discharged.** `GibbsSpec` declares this proposition and
records it as NOT PROVED THERE; it is the same statement as `exists_isGibbsMeasure_of_density`,
under the name the specification gives it.

DERIVED: `0` and `2` are the proved range of the plaquette density (`hφ0`, `hφ2`), the only
numerals in the statement; the anchoring boundary configuration is the parameter `ω₀`, as at
`exists_isGibbsMeasure_of_density`. -/
theorem existsGibbsMeasure_of_density [T2Space G] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω₀ : IConf G) : ExistsGibbsMeasure φ β μ :=
  exists_isGibbsMeasure_of_density hφc hφ0 hφ2 β μ ω₀

#print axioms existsGibbsMeasure_of_density

section Wilson

open MassGap.CompactGauge MassGap.WilsonAction

/-- **THE WILSON SPECIFICATION HAS A GIBBS MEASURE ON `SU(N)`, IN THE FULL SENSE.** For every
`N ≠ 0` and every real `β` there is a probability measure `P` on the configuration space of the
infinite four-dimensional lattice with

    ∫ f dP = ∫ spec wilsonDensity β Λ probHaar f dP

for every finite volume `Λ` and every BOUNDED MEASURABLE observable `f` — `GibbsSpec.IsGibbsMeasure`
itself, not a continuous restriction of it. The density is the genuine `1 − Re tr U / N`, the
single-link measure is probability Haar, and the conditioning is against a real boundary condition
(`GibbsSpec.boundaryPlaqs`).

Hypotheses, in full: `N ≠ 0` and `β : ℝ` arbitrary. No coupling regime, no volume bound, no
smallness condition.

DERIVED: the `0` in the statement is the rank condition `N ≠ 0` — the density `1 − Re tr U / N`
needs `N` invertible, and `N ≠ 0` is exactly what `wilsonDensity_nonneg` and `wilsonDensity_le_two`
consume to place it in `[0,2]` (the upper bound is not claimed least: at `SU(3)` the true supremum
of `1 − Re tr g / 3` is `3/2`). The `1` is the identity configuration the finite-volume family is
anchored at, a boundary condition rather than a constant of the model — any other configuration
proves the same existence statement. No other numeral appears. -/
theorem exists_wilson_isGibbsMeasure (N : ℕ) (hN : N ≠ 0) (β : ℝ) :
    ∃ P : Measure (IConf (MassGap.SUN.SU N)),
      IsGibbsMeasure (wilsonDensity (N := N)) β (probHaar (MassGap.SUN.SU N)) P :=
  exists_isGibbsMeasure_of_density continuous_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β (probHaar (MassGap.SUN.SU N)) (fun _ => 1)

#print axioms exists_wilson_isGibbsMeasure

/-- **The same, written out.** `IsGibbsMeasure` unfolded, so the DLR equation for bounded measurable
observables can be read off the statement without chasing a definition.

DERIVED: `1` is the radius of the ball of observables the DLR equation is tested on — by linearity
of both sides in `f`, the statement at any other finite bound `B > 0` is this one applied to
`f / B`. The `0` is the rank condition `N ≠ 0`, as at `exists_wilson_isGibbsMeasure`. No other
numeral appears. -/
theorem wilson_dlr_bounded_measurable (N : ℕ) (hN : N ≠ 0) (β : ℝ) :
    ∃ P : Measure (IConf (MassGap.SUN.SU N)), IsProbabilityMeasure P ∧
      ∀ (Λ : Finset ILink) (f : IConf (MassGap.SUN.SU N) → ℝ), Measurable f →
        (∀ U, |f U| ≤ 1) →
        (∫ U, f U ∂P)
          = ∫ U, spec (wilsonDensity (N := N)) β Λ (probHaar (MassGap.SUN.SU N)) f U ∂P :=
  exists_wilson_isGibbsMeasure N hN β

#print axioms wilson_dlr_bounded_measurable

end Wilson

end MassGap.WilsonGibbs
