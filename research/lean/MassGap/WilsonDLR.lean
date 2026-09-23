import Mathlib
import MassGap.GibbsSpec
import MassGap.InfiniteLattice
import MassGap.DLRLimit
import MassGap.SUN
import MassGap.WilsonAction

/-!
# MassGap.WilsonDLR — the Feller property of the Wilson specification, and the limit it unlocks

`GibbsSpec` builds the finite-volume kernel `spec φ β Λ μ f ω` with a boundary condition and proves
it DLR-consistent (`GibbsSpec.dlr_consistent`, instantiated at `WilsonAction.wilsonDensity` on `SU N`
by `GibbsSpec.wilson_dlr_consistent`). `DLRLimit` builds an infinite-volume state and measure from
any specification presented as `γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ)`, whose type demands
that the kernel carry continuous observables to continuous ones. `GibbsSpec` proves measurability in
the boundary condition. This file proves the continuity and applies `DLRLimit`.

## Parts 0–6: continuity, locality, linearity

`bounded_of_continuous` uses compactness of `IConf G`. `continuous_splice_right`,
`continuous_stepListProd`, `continuous_ihol`, `continuous_actionOn` and `continuous_wt_right` are the
continuity mirrors of `GibbsSpec`'s measurability lemmas. `continuous_num_right` and
`continuous_part_right` apply `MeasureTheory.continuous_of_dominated`, the domination being by a
constant because the observable is bounded and the weight is bounded by
`exp (|β| * (#boundaryPlaqs Λ * 2))`; `GibbsSpec.part_pos` keeps the quotient continuous, giving
`continuous_spec_right`.

`bdLinks Λ` is the finite set of links the plaquettes of `boundaryPlaqs Λ` read. `isLocalOn_spec`
shows the kernel of an observable local on `S` is local on `S ∪ bdLinks Λ`, and
`spec_mem_localAlg` packages that with continuity as membership in `InfiniteLattice.localAlg`.
`spec_smul`, `spec_add` and `spec_nonneg` are the three algebraic facts a state needs, and
`dlr_general` is `GibbsSpec.dlr_consistent` with its `|f| ≤ 1` restriction removed by scaling.

## Part 7: what `DLRLimit` consumes

`specCM` is the kernel as a map on continuous observables; `specState` freezes a boundary
configuration `ω₀` and reads it as a `DLRLimit.State`; `hcons_specState` is `dlr_general` in the
index direction `DLRLimit.exists_dlr_state` takes.

## Part 7b: coupling zero

At `β = 0` the Boltzmann weight is `1` (`wt_at_zero`), the partition function is `1`
(`part_at_zero`), and the kernel is the plain product-Haar average (`spec_at_zero`). An observable
local on `S ⊆ Λ` reads the spliced configuration only inside `S`, where the splice takes the
integration variable, so `spec_at_zero_const` makes the kernel constant in the boundary condition.
`dlr_apply_at_zero`, `dlr_eq_of_isDLR_at_zero` and `dlr_unique_at_zero` turn that into uniqueness of
the DLR state, through `DLRLimit.State.eq_of_eqOn_localObs`; `dlr_unique_at_zero_eq` states it as
equality of states and `tendsto_specState_at_zero` feeds it to `DLRLimit.tendsto_of_unique_dlr`, so
the finite-volume states converge along `atTop` rather than along an ultrafilter.
`dlr_mul_at_zero` is factorisation on disjoint local supports, from
`spec_at_zero_mul_of_disjoint`.

`permConf`, `twistConf` and their volume-level companions `volReindex`, `coordTwist`, `volTwist`
carry a link bijection, optionally with a coordinatewise twist, through the splice and the product
measure. `spec_at_zero_permConf` and `spec_at_zero_twistConf` show the kernel commutes with them at
`β = 0`; `permState`, `twistState`, `isDLR_permState_at_zero` and `isDLR_twistState_at_zero` lift
that to states, and uniqueness collapses each onto the original in `dlr_permCM_at_zero` and
`dlr_twistCM_at_zero`.

## Parts 8–9: the measure

`exists_infinite_volume_gibbs_measure_of_density` applies
`DLRLimit.exists_infinite_volume_gibbs_measure` to the genuine kernel, giving a probability measure
`P` on `IConf G` with `∫ spec φ β Λ μ f dP = ∫ f dP` at every finite volume and every continuous
observable. `wilson_continuous_spec_right` and `exists_wilson_infinite_volume_gibbs_measure`
instantiate at `wilsonDensity` on `SU N` against `CompactGauge.probHaar`, at every real `β`, with the
boundary configuration anchored at the identity.

## Scope

* The limit is subsequential except at `β = 0`: `exists_infinite_volume_gibbs_measure_of_density`
  goes through an ultrafilter refining `atTop` on `Finset ILink`, and nothing shows the net itself
  converges or that the result is independent of `ω₀`. `tendsto_specState_at_zero` is the exception,
  and its argument runs through `spec_at_zero_const`, which holds only at zero coupling.
* Uniqueness, translation invariance and non-degeneracy are not proved at general coupling.
  `DLRLimit.not_isPointMass_of_uniform_variance` needs a variance floor uniform in the volume.
  `InfiniteVolume.exists_uniform_contact_floor` supplies one `δ₀ > 0` with
  `exp (-128 * β) * δ₀ ≤ wilsonCorrAt N β 0` at every aperture and every `β ≥ 0`, and
  `PlaqVariance.corrClay_zero_eq` makes that contact value a plaquette variance;
  `ClayNontriviality.clay_nontriviality_of_wilson_variance` composes the two. That floor is stated
  for `wilsonCorrAt N β 0` on a finite periodic lattice indexed by an aperture, while `specState` is
  indexed by a `Finset ILink` of `ℤ⁴` with a frozen boundary; relating a variance in one indexing to
  a variance in the other is not done here.
* The DLR equation delivered here is tested against CONTINUOUS observables, so
  `GibbsSpec.IsGibbsMeasure` — which asks for it against every bounded measurable observable — is not
  claimed. `MassGap.WilsonGibbs.exists_wilson_isGibbsMeasure` carries it there, by exhibiting the
  kernel applied to `P` as a measure and using that two finite Borel measures agreeing on continuous
  observables are equal; an `L¹` approximation would not pass under the kernel, which is bounded in
  the sup norm rather than the `L¹(P)` norm.
* `φ` is a general density with `0 ≤ φ ≤ 2` throughout. `WilsonAction.wilsonDensity_nonneg` and
  `wilsonDensity_le_two` discharge those two at the Wilson instance; the upper bound `2` is proved,
  not attained — at `SU 3` the supremum of `1 - Re tr g / 3` is `3 / 2`.

Build: `python research/code/lean_build.py build MassGap.WilsonDLR`.
-/

namespace MassGap.WilsonDLR

open MeasureTheory
open MassGap.GibbsSpec MassGap.WilsonLattice

/-! ## Part 0 — boundedness on the compact configuration space

`IConf G` is a product of copies of a compact group, hence compact, so every continuous observable
on it is bounded. That is where the domination in Part 4 comes from: the bound is a constant, and a
constant is integrable against the probability measure `vol μ Λ`. -/

section Bounded

variable {G : Type} [TopologicalSpace G] [CompactSpace G]

/-- `∃ C, ∀ U, |F U| ≤ C` for a continuous `F : IConf G → ℝ`. The range is compact, hence bounded
above and below, and `|a| + |b|` at those two bounds serves.
`InfiniteLattice.bounded_of_continuous` is the same statement in its own namespace.

DERIVED: no numeral appears in the statement. -/
theorem bounded_of_continuous {F : IConf G → ℝ} (hF : Continuous F) : ∃ C : ℝ, ∀ U, |F U| ≤ C := by
  obtain ⟨b, hb⟩ := (isCompact_range hF).bddAbove
  obtain ⟨a, ha⟩ := (isCompact_range hF).bddBelow
  refine ⟨|a| + |b|, fun U => ?_⟩
  have h1 : F U ≤ b := hb (Set.mem_range_self U)
  have h2 : a ≤ F U := ha (Set.mem_range_self U)
  have h3 : -|a| ≤ a := neg_abs_le a
  have h4 : b ≤ |b| := le_abs_self b
  have h5 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h6 : (0 : ℝ) ≤ |b| := abs_nonneg b
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms bounded_of_continuous

end Bounded

/-! ## Part 1 — the links a finite volume's plaquettes read

`GibbsSpec.boundaryPlaqs Λ` collects the plaquettes with at least one link in `Λ`, so some of their
links lie outside `Λ` and the kernel reads the boundary condition there. That set of links is
finite, which is what makes the kernel of a local observable local. -/

/-- `(boundaryPlaqs Λ).biUnion (fun q => (ilinks q).toFinset)`: the links read by the plaquettes of
`boundaryPlaqs Λ`, inside and outside `Λ` alike. Finite, being a `biUnion` of finitely many finite
lists.

DERIVED: no numeral appears in the statement. -/
def bdLinks (Λ : Finset ILink) : Finset ILink :=
  (boundaryPlaqs Λ).biUnion (fun q => (ilinks q).toFinset)

#print axioms bdLinks

theorem mem_bdLinks {Λ : Finset ILink} {q : IPlaq} (hq : q ∈ boundaryPlaqs Λ) {l : ILink}
    (hl : l ∈ ilinks q) : l ∈ bdLinks Λ :=
  Finset.mem_biUnion.mpr ⟨q, hq, List.mem_toFinset.mpr hl⟩

#print axioms mem_bdLinks

/-! ## Part 2 — the working context

One instance block for the rest of the file: a compact, second-countable, Borel topological group
with measurable multiplication and inversion. `MassGap.SUN.SU N` carries all of them, and
`GibbsSpec`'s kernel is defined over the measurable ones. -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-! ## Part 3 — continuity of the pieces in the boundary condition

The splice, the holonomy, the action and the Boltzmann weight, each continuous in `ω` with the
inside configuration `u` held fixed. These mirror `GibbsSpec.measurable_splice_right`,
`GibbsSpec.measurable_ihol`, `GibbsSpec.measurable_actionOn` and `GibbsSpec.measurable_wt_left`. -/

/-- `fun ω => splice Λ u ω` is continuous, for a fixed inside configuration `u`. Checked
coordinatewise: at a link of `Λ` the value is the constant `u`, and at a link outside it is
evaluation of `ω`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_splice_right (Λ : Finset ILink) (u : VConf G Λ) :
    Continuous (fun ω : IConf G => splice Λ u ω) := by
  refine continuous_pi (fun l => ?_)
  by_cases h : l ∈ Λ
  · have he : (fun ω : IConf G => splice Λ u ω l) = fun _ => u ⟨l, h⟩ :=
      funext fun _ => splice_mem h
    rw [he]; exact continuous_const
  · have he : (fun ω : IConf G => splice Λ u ω l) = fun ω => ω l :=
      funext fun _ => splice_not_mem h
    rw [he]; exact continuous_apply l

#print axioms continuous_splice_right

/-- `fun U => (w.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod` is continuous, for a
fixed word `w : List (ILink × Bool)`. Induction on the list, with continuity of multiplication,
evaluation and inversion at each step. It mirrors `WilsonLattice.measurable_stepListProd`.

DERIVED: no numeral appears in the statement; `.1` and `.2` are projections and `true`/`false` are
orientation flags. -/
theorem continuous_stepListProd (w : List (ILink × Bool)) :
    Continuous
      (fun U : IConf G => (w.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil]; exact continuous_const
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Continuous.mul ?_ ih
    by_cases ha : a.2 = true
    · have he : (fun U : IConf G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => U a.1 :=
        funext fun U => if_pos ha
      rw [he]; exact continuous_apply a.1
    · have he : (fun U : IConf G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => (U a.1)⁻¹ :=
        funext fun U => if_neg ha
      rw [he]; exact (continuous_apply a.1).inv

#print axioms continuous_stepListProd

/-- `fun U => ihol q U` is continuous, at every plaquette `q`: it unfolds to `wilsonHol` at the
boundary word `ibd q`, which `continuous_stepListProd` handles.

DERIVED: no numeral appears in the statement. -/
theorem continuous_ihol (q : IPlaq) : Continuous (fun U : IConf G => ihol q U) := by
  unfold ihol wilsonHol
  exact continuous_stepListProd (ibd q)

#print axioms continuous_ihol

/-- `fun U => actionOn φ S U` is continuous for a continuous density `φ` and a `Finset IPlaq` `S`:
it is a finite sum of `φ` composed with `continuous_ihol`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_actionOn {φ : G → ℝ} (hφc : Continuous φ) (S : Finset IPlaq) :
    Continuous (fun U : IConf G => actionOn φ S U) := by
  unfold actionOn
  exact continuous_finsetSum S (fun q _ => hφc.comp (continuous_ihol q))

#print axioms continuous_actionOn

/-- `fun ω => wt φ β Λ u ω` is continuous for a continuous density, with the inside configuration
`u` held fixed: `Real.exp` composed with a constant multiple of `continuous_actionOn` composed with
`continuous_splice_right`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_wt_right {φ : G → ℝ} (hφc : Continuous φ) (β : ℝ) (Λ : Finset ILink)
    (u : VConf G Λ) : Continuous (fun ω : IConf G => wt φ β Λ u ω) := by
  unfold wt
  exact Real.continuous_exp.comp
    (continuous_const.mul ((continuous_actionOn hφc (boundaryPlaqs Λ)).comp
      (continuous_splice_right Λ u)))

#print axioms continuous_wt_right

/-! ## Part 4 — continuity of the kernel in the boundary condition

Both the numerator and the partition function are integrals over the finite product `VConf G Λ` of an
integrand continuous in `ω` and bounded by a constant uniformly in `ω`, so
`MeasureTheory.continuous_of_dominated` applies — `IConf G` is a countable product of
second-countable spaces, hence first countable, which is what that lemma requires of the parameter
space. `GibbsSpec.part_pos` keeps the quotient continuous. -/

/-- `fun ω => num φ β Λ μ f ω` is continuous, for a continuous density with `0 ≤ φ ≤ 2`, a
continuous observable `f` bounded by `C`, and a probability measure `μ`.
`MeasureTheory.continuous_of_dominated` applies with the constant dominating function
`C * exp (|β| * (#boundaryPlaqs Λ * 2))`, from `GibbsSpec.wt_le`; measurability comes from
`measurable_splice_left` and `measurable_wt_left`, and continuity of the integrand from
`continuous_splice_right` and `continuous_wt_right`.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound, which is
what `GibbsSpec.wt_le` needs to bound the weight. -/
theorem continuous_num_right {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hfc : Continuous f) {C : ℝ} (hC : ∀ U, |f U| ≤ C) :
    Continuous (fun ω : IConf G => num φ β Λ μ f ω) := by
  have hφm : Measurable φ := hφc.measurable
  have hfm : Measurable f := hfc.measurable
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 1))
  have hms : ∀ ω : IConf G,
      AEStronglyMeasurable (fun u : VConf G Λ => f (splice Λ u ω) * wt φ β Λ u ω) (vol μ Λ) :=
    fun ω => ((hfm.comp (measurable_splice_left Λ ω)).mul
      (measurable_wt_left hφm β Λ ω)).aestronglyMeasurable
  have hbd : ∀ ω : IConf G, ∀ᵐ u ∂(vol μ Λ),
      ‖f (splice Λ u ω) * wt φ β Λ u ω‖
        ≤ C * Real.exp (|β| * (((boundaryPlaqs Λ).card : ℝ) * 2)) := by
    intro ω
    refine Filter.Eventually.of_forall (fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos φ β Λ u ω)]
    exact mul_le_mul (hC _) (wt_le hφ0 hφ2 β Λ u ω) (wt_pos φ β Λ u ω).le hCnn
  have hct : ∀ᵐ u ∂(vol μ Λ),
      Continuous (fun ω : IConf G => f (splice Λ u ω) * wt φ β Λ u ω) :=
    Filter.Eventually.of_forall (fun u =>
      (hfc.comp (continuous_splice_right Λ u)).mul (continuous_wt_right hφc β Λ u))
  exact continuous_of_dominated hms hbd (integrable_const _) hct

#print axioms continuous_num_right

/-- `fun ω => part φ β Λ μ ω` is continuous, for a continuous density with `0 ≤ φ ≤ 2` and a
probability measure `μ`. Same argument as `continuous_num_right` without the observable factor, the
dominating constant being `exp (|β| * (#boundaryPlaqs Λ * 2))`.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound. -/
theorem continuous_part_right {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ] :
    Continuous (fun ω : IConf G => part φ β Λ μ ω) := by
  have hφm : Measurable φ := hφc.measurable
  have hms : ∀ ω : IConf G,
      AEStronglyMeasurable (fun u : VConf G Λ => wt φ β Λ u ω) (vol μ Λ) :=
    fun ω => (measurable_wt_left hφm β Λ ω).aestronglyMeasurable
  have hbd : ∀ ω : IConf G, ∀ᵐ u ∂(vol μ Λ),
      ‖wt φ β Λ u ω‖ ≤ Real.exp (|β| * (((boundaryPlaqs Λ).card : ℝ) * 2)) := by
    intro ω
    refine Filter.Eventually.of_forall (fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (wt_pos φ β Λ u ω)]
    exact wt_le hφ0 hφ2 β Λ u ω
  have hct : ∀ᵐ u ∂(vol μ Λ), Continuous (fun ω : IConf G => wt φ β Λ u ω) :=
    Filter.Eventually.of_forall (fun u => continuous_wt_right hφc β Λ u)
  exact continuous_of_dominated hms hbd (integrable_const _) hct

#print axioms continuous_part_right

/-- `fun ω => spec φ β Λ μ f ω` is continuous, for a continuous density with `0 ≤ φ ≤ 2` and a
continuous observable `f`. The observable is bounded by `bounded_of_continuous`, so
`continuous_num_right` and `continuous_part_right` apply, and `GibbsSpec.part_pos` makes the
denominator nonvanishing.

This is the property `DLRLimit` records in the type of its `γ`;
`GibbsSpec.measurable_spec_right` gives measurability of the same map.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound. -/
theorem continuous_spec_right {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hfc : Continuous f) :
    Continuous (fun ω : IConf G => spec φ β Λ μ f ω) := by
  obtain ⟨C, hC⟩ := bounded_of_continuous hfc
  exact (continuous_num_right hφc hφ0 hφ2 β Λ μ hfc hC).div₀
    (continuous_part_right hφc hφ0 hφ2 β Λ μ)
    (fun ω => (part_pos hφc.measurable hφ0 hφ2 β Λ μ ω).ne')

#print axioms continuous_spec_right

/-! ## Part 5 — the kernel preserves locality

A finite volume's kernel reads its boundary condition through two windows: the observable `f`, and
the plaquettes of `boundaryPlaqs Λ` whose links lie outside `Λ`. Both are finite, so the image of a
local observable is local. -/

/-- If `f` is local on `S`, then `fun ω => spec φ β Λ μ f ω` is local on `S ∪ bdLinks Λ`. Two
boundary conditions agreeing on that union give the same spliced configuration at every link of `S`
and the same energy on `boundaryPlaqs Λ` (by `GibbsSpec.actionOn_congr` and `mem_bdLinks`), so the
numerator and the partition function agree.

DERIVED: no numeral appears in the statement. -/
theorem isLocalOn_spec (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    {S : Finset ILink} {f : IConf G → ℝ} (hf : MassGap.InfiniteLattice.IsLocalOn S f) :
    MassGap.InfiniteLattice.IsLocalOn (S ∪ bdLinks Λ) (fun ω => spec φ β Λ μ f ω) := by
  intro ω ω' h
  have hin : ∀ (u : VConf G Λ) (l : ILink), l ∈ S → splice Λ u ω l = splice Λ u ω' l := by
    intro u l hl
    by_cases hlΛ : l ∈ Λ
    · rw [splice_mem hlΛ, splice_mem hlΛ]
    · rw [splice_not_mem hlΛ, splice_not_mem hlΛ]
      exact h l (Finset.mem_union_left _ hl)
  have hf_eq : ∀ u : VConf G Λ, f (splice Λ u ω) = f (splice Λ u ω') :=
    fun u => hf _ _ (hin u)
  have hwt : ∀ u : VConf G Λ, wt φ β Λ u ω = wt φ β Λ u ω' := by
    intro u
    have hact : actionOn φ (boundaryPlaqs Λ) (splice Λ u ω)
        = actionOn φ (boundaryPlaqs Λ) (splice Λ u ω') := by
      refine actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
      by_cases hlΛ : l ∈ Λ
      · rw [splice_mem hlΛ, splice_mem hlΛ]
      · rw [splice_not_mem hlΛ, splice_not_mem hlΛ]
        exact h l (Finset.mem_union_right _ (mem_bdLinks hq hl))
    unfold wt
    rw [hact]
  have hnum : num φ β Λ μ f ω = num φ β Λ μ f ω' := by
    unfold num
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show f (splice Λ u ω) * wt φ β Λ u ω = f (splice Λ u ω') * wt φ β Λ u ω'
    rw [hf_eq u, hwt u]
  have hpart : part φ β Λ μ ω = part φ β Λ μ ω' := by
    unfold part
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => hwt u))
  show spec φ β Λ μ f ω = spec φ β Λ μ f ω'
  unfold spec
  rw [hnum, hpart]

#print axioms isLocalOn_spec

/-- If `f ∈ InfiniteLattice.localAlg S`, then `fun ω => spec φ β Λ μ f ω` is in
`InfiniteLattice.localAlg (S ∪ bdLinks Λ)`: continuity from `continuous_spec_right` and locality
from `isLocalOn_spec`, which is what membership in `localAlg` is.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound. -/
theorem spec_mem_localAlg {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {S : Finset ILink} {f : IConf G → ℝ} (hf : f ∈ MassGap.InfiniteLattice.localAlg S) :
    (fun ω => spec φ β Λ μ f ω) ∈ MassGap.InfiniteLattice.localAlg (S ∪ bdLinks Λ) :=
  ⟨continuous_spec_right hφc hφ0 hφ2 β Λ μ hf.1, isLocalOn_spec φ β Λ μ hf.2⟩

#print axioms spec_mem_localAlg

/-! ## Part 6 — linearity and positivity of the kernel in the observable

The three algebraic facts a state needs. `spec_smul` is exact homogeneity and needs no integrability;
`spec_add` needs the integrands integrable, which `GibbsSpec.integrable_num` supplies from
boundedness. -/

/-- `spec φ β Λ μ (fun U => c * f U) ω = c * spec φ β Λ μ f ω`, by pulling the constant out of the
numerator's integral. No integrability, boundedness or measurability hypothesis is needed.

DERIVED: no numeral appears in the statement. -/
theorem spec_smul (φ : G → ℝ) (β : ℝ) (Λ : Finset ILink) (μ : Measure G)
    (c : ℝ) (f : IConf G → ℝ) (ω : IConf G) :
    spec φ β Λ μ (fun U => c * f U) ω = c * spec φ β Λ μ f ω := by
  have hnum : num φ β Λ μ (fun U => c * f U) ω = c * num φ β Λ μ f ω := by
    show (∫ u, c * f (splice Λ u ω) * wt φ β Λ u ω ∂(vol μ Λ))
        = c * ∫ u, f (splice Λ u ω) * wt φ β Λ u ω ∂(vol μ Λ)
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))
  unfold spec
  rw [hnum, mul_div_assoc]

#print axioms spec_smul

/-- `spec φ β Λ μ (fun U => f U + g U) ω = spec φ β Λ μ f ω + spec φ β Λ μ g ω` for measurable `f`,
`g` bounded by `Cf` and `Cg`. `MeasureTheory.integral_add` splits the numerator, its two
integrability hypotheses supplied by `GibbsSpec.integrable_num`.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound. The
bounds `Cf` and `Cg` are the caller's. -/
theorem spec_add {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f g : IConf G → ℝ} (hf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hg : Measurable g) {Cg : ℝ} (hCg : ∀ U, |g U| ≤ Cg) (ω : IConf G) :
    spec φ β Λ μ (fun U => f U + g U) ω = spec φ β Λ μ f ω + spec φ β Λ μ g ω := by
  have hnum : num φ β Λ μ (fun U => f U + g U) ω = num φ β Λ μ f ω + num φ β Λ μ g ω := by
    show (∫ u, (f (splice Λ u ω) + g (splice Λ u ω)) * wt φ β Λ u ω ∂(vol μ Λ))
        = (∫ u, f (splice Λ u ω) * wt φ β Λ u ω ∂(vol μ Λ))
          + ∫ u, g (splice Λ u ω) * wt φ β Λ u ω ∂(vol μ Λ)
    rw [← integral_add (integrable_num hφ hφ0 hφ2 β Λ μ hf hCf ω)
      (integrable_num hφ hφ0 hφ2 β Λ μ hg hCg ω)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))
  unfold spec
  rw [hnum, add_div]

#print axioms spec_add

/-- `0 ≤ spec φ β Λ μ f ω` for a pointwise nonnegative `f`: the numerator is an integral of a product
of nonnegatives and the partition function is positive by `GibbsSpec.part_pos`.

DERIVED: `0` occurs four times — the pointwise lower bound on the density, the pointwise lower bound
on `f`, and the lower bound on the kernel's value; the remaining `0` is the lower bound in
`hφ0 : ∀ g, 0 ≤ φ g`. `2` is the density's pointwise upper bound. -/
theorem spec_nonneg {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : ∀ U, 0 ≤ f U) (ω : IConf G) : 0 ≤ spec φ β Λ μ f ω := by
  unfold spec
  refine div_nonneg ?_ (part_pos hφ hφ0 hφ2 β Λ μ ω).le
  unfold num
  exact integral_nonneg (fun u => mul_nonneg (hf _) (wt_pos φ β Λ u ω).le)

#print axioms spec_nonneg

/-- `spec φ β Λ' μ (fun v => spec φ β Λ μ f v) ω = spec φ β Λ' μ f ω` for `Λ ⊆ Λ'` and a measurable
`f` bounded by any `C`. `GibbsSpec.dlr_consistent` is stated for `|f| ≤ 1`; here `f` is scaled by
`(C + 1)⁻¹` to meet that, and `spec_smul` — exact homogeneity in the observable — cancels the scalar
from both sides.

Scope: a bound `hC` is still taken; what is removed is its being fixed at `1`.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound. The
scaling constant `(C + 1)⁻¹` is built in the proof. -/
theorem dlr_general {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ') {f : IConf G → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ U, |f U| ≤ C) (ω : IConf G) :
    spec φ β Λ' μ (fun v => spec φ β Λ μ f v) ω = spec φ β Λ' μ f ω := by
  have hCnn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC (fun _ => 1))
  have hp : (0 : ℝ) < C + 1 := by linarith
  obtain ⟨c, hcpos, hbound⟩ : ∃ c : ℝ, 0 < c ∧ ∀ U, |c * f U| ≤ 1 := by
    refine ⟨(C + 1)⁻¹, inv_pos.mpr hp, fun U => ?_⟩
    rw [abs_mul, abs_of_pos (inv_pos.mpr hp)]
    have h1 : |f U| ≤ C + 1 := le_trans (hC U) (by linarith)
    calc (C + 1)⁻¹ * |f U| ≤ (C + 1)⁻¹ * (C + 1) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hp).le
      _ = 1 := inv_mul_cancel₀ hp.ne'
  have h := dlr_consistent hφ hφ0 hφ2 β μ Λ Λ' hsub (fun U => c * f U) (hf.const_mul c) hbound ω
  have hinner : (fun v => spec φ β Λ μ (fun U => c * f U) v)
      = fun v => c * spec φ β Λ μ f v :=
    funext fun v => spec_smul φ β Λ μ c f v
  rw [hinner, spec_smul, spec_smul] at h
  exact mul_left_cancel₀ hcpos.ne' h

#print axioms dlr_general

/-! ## Part 7 — the specification in the shape `DLRLimit` consumes

`specCM` is the kernel as a map `C(IConf G, ℝ) → C(IConf G, ℝ)`, which `continuous_spec_right` makes
well defined. `specState` freezes one boundary configuration and reads the kernel as a
`DLRLimit.State`. `hcons_specState` is `dlr_general` at that configuration, with the index directions
matched to `DLRLimit.exists_dlr_state`. -/

/-- The kernel as a map `C(IConf G, ℝ) → C(IConf G, ℝ)`: the underlying function is
`fun ω => spec φ β Λ μ f ω` and the continuity field is `continuous_spec_right`. This is the type
`DLRLimit`'s `γ` has.

DERIVED: `0` and `2` are the pointwise lower and upper bounds on the density. At
`wilsonDensity g = 1 - Re tr g / N` on `SU N` the trace ratio has modulus at most one, so the density
lies in `[0, 2]`; `WilsonAction.wilsonDensity_nonneg` and `wilsonDensity_le_two` discharge the two
hypotheses there. They are hypotheses here because the development is stated for a general
density. -/
noncomputable def specCM {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (Λ : Finset ILink) (f : C(IConf G, ℝ)) : C(IConf G, ℝ) :=
  ⟨fun ω => spec φ β Λ μ (⇑f) ω, continuous_spec_right hφc hφ0 hφ2 β Λ μ f.continuous⟩

#print axioms specCM

theorem specCM_apply {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ]
    (Λ : Finset ILink) (f : C(IConf G, ℝ)) (ω : IConf G) :
    specCM hφc hφ0 hφ2 β μ Λ f ω = spec φ β Λ μ (⇑f) ω := rfl

#print axioms specCM_apply

/-! ## Part 7b — coupling zero

At `β = 0` the Boltzmann weight is `Real.exp 0 = 1`, so the partition function is `1` and the kernel
is the plain product-Haar average over the volume. An observable local on `S` reads the spliced
configuration only inside `S`, and for `S ⊆ Λ` the splice takes the integration variable there, never
the boundary condition, so the kernel of a local observable is constant in the boundary. A DLR state
is unmoved by the kernel, so it reads that observable as that one constant, the same number for every
DLR state; `DLRLimit.State.eq_of_eqOn_localObs` then gives equality of states.

The boundary dependence at this coupling is absent rather than small, so no limit, cluster expansion
or Dobrushin condition enters, and the argument does not extend to nonzero coupling.
-/

/-- `wt φ 0 Λ u ω = 1` at every volume, inside configuration and boundary condition: unfolding the
weight leaves `Real.exp (0 * _)`, which `simp` evaluates.

DERIVED: `0` is the coupling at which the statement is read; `1` is the value `Real.exp 0`. -/
theorem wt_at_zero (φ : G → ℝ) (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) :
    wt φ 0 Λ u ω = 1 := by
  unfold wt
  simp

#print axioms wt_at_zero

/-- `part φ 0 Λ μ ω = 1`: the partition function is the integral of `wt_at_zero`'s constant `1`
against `vol μ Λ`, which is a probability measure.

DERIVED: `0` is the coupling; `1` is the value, which is the total mass of a probability measure. -/
theorem part_at_zero (φ : G → ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω : IConf G) : part φ 0 Λ μ ω = 1 := by
  unfold part
  simp [wt_at_zero]

#print axioms part_at_zero

/-- `num φ 0 Λ μ f ω = ∫ u, f (splice Λ u ω) ∂(vol μ Λ)`: at zero coupling the weight is `1` by
`wt_at_zero`, so the numerator is the plain average of the spliced observable.

DERIVED: `0` is the coupling. -/
theorem num_at_zero (φ : G → ℝ) (Λ : Finset ILink) (μ : Measure G) (f : IConf G → ℝ)
    (ω : IConf G) : num φ 0 Λ μ f ω = ∫ u, f (splice Λ u ω) ∂(vol μ Λ) := by
  unfold num
  simp [wt_at_zero]

#print axioms num_at_zero

/-- `spec φ 0 Λ μ f ω = ∫ u, f (splice Λ u ω) ∂(vol μ Λ)`: `num_at_zero` over `part_at_zero`, the
denominator being `1`.

Scope: the right side does not depend on the density `φ` at all, which is what the rest of Part 7b
rests on.

DERIVED: `0` is the coupling. -/
theorem spec_at_zero (φ : G → ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (f : IConf G → ℝ) (ω : IConf G) :
    spec φ 0 Λ μ f ω = ∫ u, f (splice Λ u ω) ∂(vol μ Λ) := by
  unfold spec
  rw [num_at_zero, part_at_zero, div_one]

#print axioms spec_at_zero

/-! ### Relabelling the links

A bijection of the links acts on configurations by precomposition. At zero coupling the kernel
commutes with that action, once the volume is relabelled along with it. This is the measure-theoretic
input of `WilsonTransferReduction.transferData_of_state_facts`'s state facts in the case where no
group inversion enters, which is the case the shift presents. -/

/-- `fun l => U (e l)`: a configuration relabelled along a bijection `e` of the links.
`InfiniteShift.ishiftConf` is this at `e = ishiftLink`.

DERIVED: no numeral appears in the statement. -/
def permConf (e : ILink ≃ ILink) (U : IConf G) : IConf G := fun l => U (e l)

#print axioms permConf

/-- `permConf e` is continuous: coordinatewise it is evaluation at `e l`, so `continuous_pi` and
`continuous_apply` suffice.

DERIVED: no numeral appears in the statement. -/
theorem continuous_permConf (e : ILink ≃ ILink) :
    Continuous (permConf (G := G) e) :=
  continuous_pi (fun l => continuous_apply (e l))

#print axioms continuous_permConf

/-- The equivalence `↑Λ ≃ ↑(Λ.image e)` induced by a link bijection `e`, sending `l` to `e l`. The
inverse sends `m` to `e.symm m`, which lands back in `Λ` because `m` is in the image; injectivity of
`e` is what makes that recovery well defined.

DERIVED: no numeral appears in the statement. -/
def imgEquiv (e : ILink ≃ ILink) (Λ : Finset ILink) : ↑Λ ≃ ↑(Λ.image e) where
  toFun l := ⟨e l.1, Finset.mem_image_of_mem _ l.2⟩
  invFun m := ⟨e.symm m.1, by
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp m.2
    have hsym : e.symm m.1 = a := by rw [← hae, e.symm_apply_apply]
    rw [hsym]; exact ha⟩
  left_inv l := by apply Subtype.ext; simp
  right_inv m := by apply Subtype.ext; simp

#print axioms imgEquiv

/-- `VConf G (Λ.image e) ≃ᵐ VConf G Λ`, as the inverse of `MeasurableEquiv.piCongrLeft` along
`imgEquiv e Λ`. Same construction as `GibbsSpec.toIn`, along `imgEquiv` instead of `subEquivIn`.

DERIVED: no numeral appears in the statement. -/
noncomputable def volReindex (e : ILink ≃ ILink) (Λ : Finset ILink) :
    VConf G (Λ.image e) ≃ᵐ VConf G Λ :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↑(Λ.image ⇑e) => G) (imgEquiv e Λ)).symm

#print axioms volReindex

theorem volReindex_apply (e : ILink ≃ ILink) (Λ : Finset ILink) (w : VConf G (Λ.image e))
    (l : ↑Λ) : volReindex (G := G) e Λ w l = w (imgEquiv e Λ l) := rfl

#print axioms volReindex_apply

/-- `volReindex e Λ` is measure-preserving from `vol μ (Λ.image e)` to `vol μ Λ`. It is
`measurePreserving_piCongrLeft` along `imgEquiv e Λ`, taken backwards by
`MeasurePreserving.symm` — the same move as `GibbsSpec.measurePreserving_toIn`.

DERIVED: no numeral appears in the statement. -/
theorem measurePreserving_volReindex (e : ILink ≃ ILink) (Λ : Finset ILink) (μ : Measure G)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (volReindex (G := G) e Λ) (vol μ (Λ.image e)) (vol μ Λ) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ↑(Λ.image ⇑e) => G) (imgEquiv e Λ))
      (vol μ Λ) (vol μ (Λ.image e)) := by
    simpa [vol] using
      measurePreserving_piCongrLeft (μ := fun _ : ↑(Λ.image ⇑e) => μ) (imgEquiv e Λ)
  exact MeasurePreserving.symm _ h

#print axioms measurePreserving_volReindex

/-- `permConf e (splice (Λ.image e) w U) = splice Λ (volReindex e Λ w) (permConf e U)`. Checked
link by link: inside `Λ` both sides read the integration variable at the relabelled index, and
outside it both read the boundary condition at the relabelled link. Injectivity of `e` is what makes
`l ∉ Λ` give `e l ∉ Λ.image e`.

DERIVED: no numeral appears in the statement. -/
theorem permConf_splice (e : ILink ≃ ILink) (Λ : Finset ILink) (w : VConf G (Λ.image e))
    (U : IConf G) :
    permConf e (splice (Λ.image e) w U) = splice Λ (volReindex e Λ w) (permConf e U) := by
  funext l
  simp only [permConf]
  by_cases hl : l ∈ Λ
  · have hel : e l ∈ Λ.image ⇑e := Finset.mem_image_of_mem _ hl
    rw [splice_mem hel, splice_mem hl]
    rfl
  · have hel : e l ∉ Λ.image ⇑e := by
      intro hc
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hc
      exact hl (by rwa [e.injective hae] at ha)
    rw [splice_not_mem hel, splice_not_mem hl]
    rfl

#print axioms permConf_splice

/-- `spec φ 0 (Λ.image e) μ (fun V => f (permConf e V)) U = spec φ 0 Λ μ f (permConf e U)`:
relabelling the observable and the volume together, and evaluating at the relabelled boundary
condition, gives the same number. `spec_at_zero` turns both sides into integrals,
`permConf_splice` matches the integrands, and `measurePreserving_volReindex` matches the measures.

Scope: `e` is an arbitrary link bijection — nothing here is specific to a shift or a reflection.

DERIVED: `0` occurs twice, as the coupling on each side. -/
theorem spec_at_zero_permConf (φ : G → ℝ) (e : ILink ≃ ILink) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] (f : IConf G → ℝ) (U : IConf G) :
    spec φ 0 (Λ.image e) μ (fun V => f (permConf e V)) U
      = spec φ 0 Λ μ f (permConf e U) := by
  rw [spec_at_zero, spec_at_zero]
  have hmp := measurePreserving_volReindex (G := G) e Λ μ
  calc (∫ w, (fun V => f (permConf e V)) (splice (Λ.image ⇑e) w U) ∂(vol μ (Λ.image ⇑e)))
      = ∫ w, f (splice Λ (volReindex e Λ w) (permConf e U)) ∂(vol μ (Λ.image ⇑e)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        show f (permConf e (splice (Λ.image ⇑e) w U))
          = f (splice Λ (volReindex e Λ w) (permConf e U))
        rw [permConf_splice]
    _ = ∫ v, f (splice Λ v (permConf e U)) ∂(vol μ Λ) :=
        hmp.integral_comp (volReindex e Λ).measurableEmbedding
          (fun v => f (splice Λ v (permConf e U)))

#print axioms spec_at_zero_permConf

section ProbeInv
#check @MeasurableEquiv.piCongrRight
#check @MeasurableEquiv.inv
#check @MeasureTheory.Measure.IsInvInvariant
#check @MeasureTheory.Measure.pi_map_pi
end ProbeInv

/-! ### Relabelling with a coordinatewise twist

`LatticeReflection.ireflConf` is not a pure relabelling: it inverts the group element on `τ`-links.
So the action needed there is a relabelling followed by a map applied coordinate by coordinate. The
measure argument gains one factor: a coordinatewise map preserves a product measure when each
coordinate does. -/

/-- `fun l => σ l (U (e l))`: a configuration relabelled along `e` and then acted on coordinatewise
by the measurable equivalences `σ`. `permConf` is the case where every `σ l` is the identity.

DERIVED: no numeral appears in the statement. -/
def twistConf (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (U : IConf G) : IConf G :=
  fun l => σ l (U (e l))

#print axioms twistConf

/-- `twistConf e σ` is continuous when every `σ l` is: coordinatewise it is `σ l` composed with
evaluation at `e l`.

Scope: `σ l` is a `MeasurableEquiv`, so continuity is a separate hypothesis `hσc`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_twistConf (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G)
    (hσc : ∀ l, Continuous (σ l)) : Continuous (twistConf (G := G) e σ) :=
  continuous_pi (fun l => (hσc l).comp (continuous_apply (e l)))

#print axioms continuous_twistConf

/-- `MeasurableEquiv.piCongrRight (fun l : ↑Λ => σ l.1)`: the coordinatewise part of the twist, as a
measurable equivalence of `VConf G Λ` with itself.

DERIVED: no numeral appears in the statement. -/
def coordTwist (Λ : Finset ILink) (σ : ILink → G ≃ᵐ G) : VConf G Λ ≃ᵐ VConf G Λ :=
  MeasurableEquiv.piCongrRight (fun l : ↑Λ => σ l.1)

#print axioms coordTwist

theorem coordTwist_apply (Λ : Finset ILink) (σ : ILink → G ≃ᵐ G) (v : VConf G Λ) (l : ↑Λ) :
    coordTwist (G := G) Λ σ v l = σ l.1 (v l) := rfl

#print axioms coordTwist_apply

/-- `coordTwist Λ σ` is measure-preserving for `vol μ Λ` when every `σ l` is measure-preserving for
`μ`. It is `Measure.pi_map_pi`, the same move `ActionSplit.twist_measurePreserving` makes for a full
index type; here the index is a volume's links.

DERIVED: no numeral appears in the statement. -/
theorem measurePreserving_coordTwist (Λ : Finset ILink) (σ : ILink → G ≃ᵐ G) (μ : Measure G)
    [IsProbabilityMeasure μ] (hσ : ∀ l, MeasurePreserving (σ l) μ μ) :
    MeasurePreserving (coordTwist (G := G) Λ σ) (vol μ Λ) (vol μ Λ) := by
  refine ⟨(coordTwist Λ σ).measurable, ?_⟩
  have hmap : Measure.map (fun (v : VConf G Λ) (l : ↑Λ) => (σ l.1) (v l))
      (Measure.pi (fun _ : ↑Λ => μ)) = Measure.pi (fun _ : ↑Λ => μ) := by
    rw [Measure.pi_map_pi (fun l : ↑Λ => (hσ l.1).aemeasurable)]
    exact congrArg Measure.pi (funext fun l => (hσ l.1).map_eq)
  show Measure.map (fun (v : VConf G Λ) (l : ↑Λ) => (σ l.1) (v l)) (vol μ Λ) = vol μ Λ
  exact hmap

#print axioms measurePreserving_coordTwist

/-- `(volReindex e Λ).trans (coordTwist Λ σ)`: relabelling a volume configuration and then twisting
it coordinatewise, as a measurable equivalence `VConf G (Λ.image e) ≃ᵐ VConf G Λ`.

DERIVED: no numeral appears in the statement. -/
noncomputable def volTwist (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink) :
    VConf G (Λ.image e) ≃ᵐ VConf G Λ :=
  (volReindex e Λ).trans (coordTwist Λ σ)

#print axioms volTwist

theorem volTwist_apply (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink)
    (w : VConf G (Λ.image e)) (l : ↑Λ) :
    volTwist (G := G) e σ Λ w l = σ l.1 (w (imgEquiv e Λ l)) := rfl

#print axioms volTwist_apply

/-- `volTwist e σ Λ` is measure-preserving from `vol μ (Λ.image e)` to `vol μ Λ`, as the composition
of `measurePreserving_volReindex` with `measurePreserving_coordTwist`.

DERIVED: no numeral appears in the statement. -/
theorem measurePreserving_volTwist (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] (hσ : ∀ l, MeasurePreserving (σ l) μ μ) :
    MeasurePreserving (volTwist (G := G) e σ Λ) (vol μ (Λ.image e)) (vol μ Λ) :=
  (measurePreserving_coordTwist Λ σ μ hσ).comp (measurePreserving_volReindex e Λ μ)

#print axioms measurePreserving_volTwist

/-- `twistConf e σ (splice (Λ.image e) w U) = splice Λ (volTwist e σ Λ w) (twistConf e σ U)`. The
same case split as `permConf_splice`, with `σ l` applied on both sides of it.

DERIVED: no numeral appears in the statement. -/
theorem twistConf_splice (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink)
    (w : VConf G (Λ.image e)) (U : IConf G) :
    twistConf e σ (splice (Λ.image e) w U) = splice Λ (volTwist e σ Λ w) (twistConf e σ U) := by
  funext l
  simp only [twistConf]
  by_cases hl : l ∈ Λ
  · have hel : e l ∈ Λ.image ⇑e := Finset.mem_image_of_mem _ hl
    rw [splice_mem hel, splice_mem hl]
    rfl
  · have hel : e l ∉ Λ.image ⇑e := by
      intro hc
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hc
      exact hl (by rwa [e.injective hae] at ha)
    rw [splice_not_mem hel, splice_not_mem hl]
    rfl

#print axioms twistConf_splice

/-- `spec φ 0 (Λ.image e) μ (fun V => f (twistConf e σ V)) U = spec φ 0 Λ μ f (twistConf e σ U)`,
when every `σ l` preserves `μ`. Same argument as `spec_at_zero_permConf`, with `twistConf_splice`
and `measurePreserving_volTwist` in place of their untwisted counterparts.

DERIVED: `0` occurs twice, as the coupling on each side. -/
theorem spec_at_zero_twistConf (φ : G → ℝ) (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G)
    (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (hσ : ∀ l, MeasurePreserving (σ l) μ μ) (f : IConf G → ℝ) (U : IConf G) :
    spec φ 0 (Λ.image e) μ (fun V => f (twistConf e σ V)) U
      = spec φ 0 Λ μ f (twistConf e σ U) := by
  rw [spec_at_zero, spec_at_zero]
  have hmp := measurePreserving_volTwist (G := G) e σ Λ μ hσ
  calc (∫ w, (fun V => f (twistConf e σ V)) (splice (Λ.image ⇑e) w U) ∂(vol μ (Λ.image ⇑e)))
      = ∫ w, f (splice Λ (volTwist e σ Λ w) (twistConf e σ U)) ∂(vol μ (Λ.image ⇑e)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        show f (twistConf e σ (splice (Λ.image ⇑e) w U))
          = f (splice Λ (volTwist e σ Λ w) (twistConf e σ U))
        rw [twistConf_splice]
    _ = ∫ v, f (splice Λ v (twistConf e σ U)) ∂(vol μ Λ) :=
        hmp.integral_comp (volTwist e σ Λ).measurableEmbedding
          (fun v => f (splice Λ v (twistConf e σ U)))

#print axioms spec_at_zero_twistConf



/-- `DLRLimit.IsLocalOnC S F → InfiniteLattice.IsLocalOn S (⇑F)`, by `rfl`: the two statements are
the same Pi type. Named so the step is not left to definitional unfolding at each use site.

DERIVED: no numeral appears in the statement. -/
theorem isLocalOn_of_isLocalOnC {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : MassGap.DLRLimit.IsLocalOnC S F) : MassGap.InfiniteLattice.IsLocalOn S (⇑F) := hF

#print axioms isLocalOn_of_isLocalOnC

/-- For `S ⊆ Λ` and `f` local on `S`, `spec φ 0 Λ μ f ω = spec φ 0 Λ μ f ω'` at every pair of
boundary conditions. `spec_at_zero` turns both sides into integrals, and at every link of `S` the
splice takes the integration variable, so the integrands coincide.

Scope: `S ⊆ Λ` is what makes the splice ignore the boundary on `f`'s support; without it the kernel
does move with the boundary.

DERIVED: `0` occurs twice, as the coupling on each side. -/
theorem spec_at_zero_const {φ : G → ℝ} {S Λ : Finset ILink} (hSΛ : S ⊆ Λ) (μ : Measure G)
    [IsProbabilityMeasure μ] {f : IConf G → ℝ}
    (hf : MassGap.InfiniteLattice.IsLocalOn S f) (ω ω' : IConf G) :
    spec φ 0 Λ μ f ω = spec φ 0 Λ μ f ω' := by
  rw [spec_at_zero, spec_at_zero]
  have hEq : (fun u : VConf G Λ => f (splice Λ u ω))
      = fun u : VConf G Λ => f (splice Λ u ω') := by
    funext u
    refine hf _ _ (fun l hl => ?_)
    have hlΛ : l ∈ Λ := hSΛ hl
    rw [splice_mem hlΛ, splice_mem hlΛ]
  rw [hEq]

#print axioms spec_at_zero_const

/-- For `S` and `T` disjoint and `H` local on `T`,
`spec φ 0 S μ (fun U => F U * H U) ω = spec φ 0 S μ F ω * H ω`. The kernel at volume `S` splices
only the links of `S`, so `H` reads the same configuration whatever the integration variable does
and leaves the integral by `integral_mul_const`.

DERIVED: `0` occurs twice, as the coupling on each side. -/
theorem spec_at_zero_mul_of_disjoint (φ : G → ℝ) {S T : Finset ILink} (hST : Disjoint S T)
    (μ : Measure G) [IsProbabilityMeasure μ] {H : IConf G → ℝ}
    (hH : MassGap.InfiniteLattice.IsLocalOn T H) (F : IConf G → ℝ) (ω : IConf G) :
    spec φ 0 S μ (fun U => F U * H U) ω = spec φ 0 S μ F ω * H ω := by
  rw [spec_at_zero, spec_at_zero]
  have hsplit : ∀ u : VConf G S, H (splice S u ω) = H ω := by
    intro u
    refine hH _ _ (fun l hl => ?_)
    have hlS : l ∉ S := fun hc => (Finset.disjoint_left.mp hST hc) hl
    exact splice_not_mem hlS
  have hEq : (fun u : VConf G S => (fun U => F U * H U) (splice S u ω))
      = fun u : VConf G S => F (splice S u ω) * H ω := by
    funext u
    show F (splice S u ω) * H (splice S u ω) = F (splice S u ω) * H ω
    rw [hsplit u]
  rw [hEq, integral_mul_const]

#print axioms spec_at_zero_mul_of_disjoint

/-- For a state `ν` satisfying `IsDLR (specCM … 0 μ)` and an `F` local on `S`,
`ν F = spec φ 0 S μ F ω` at EVERY boundary configuration `ω`. Taking the volume to be `S` itself,
`spec_at_zero_const` makes the kernel the constant observable `spec φ 0 S μ F ω • 1`, and the DLR
equation with `State.map_smul` and `State.map_one` reads the value off it.

DERIVED: `0` occurs three times — the pointwise lower bound on the density, the coupling in
`specCM`, and the coupling in `spec`. `2` is the density's pointwise upper bound. -/
theorem dlr_apply_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν : MassGap.DLRLimit.State (IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν)
    {F : C(IConf G, ℝ)} {S : Finset ILink} (hF : MassGap.DLRLimit.IsLocalOnC S F)
    (ω : IConf G) : ν F = spec φ 0 S μ (⇑F) ω := by
  have hconst : specCM hφc hφ0 hφ2 0 μ S F
      = (spec φ 0 S μ (⇑F) ω : ℝ) • (1 : C(IConf G, ℝ)) := by
    ext ω'
    rw [specCM_apply]
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact spec_at_zero_const (Finset.Subset.refl S) μ (isLocalOn_of_isLocalOnC hF) ω' ω
  rw [← hν S F, hconst, ν.map_smul, ν.map_one, mul_one]

#print axioms dlr_apply_at_zero


/-- Two states satisfying `IsDLR (specCM … 0 μ)` agree at every `F` local on some `S`: both equal
`spec φ 0 S μ F ω₀` by `dlr_apply_at_zero`, at a base configuration `ω₀` obtained from
`DLRLimit.State.nonempty`.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in each
of the two `specCM` hypotheses. `2` is the density's pointwise upper bound. -/
theorem dlr_eq_of_isDLR_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν₁ ν₂ : MassGap.DLRLimit.State (IConf G)}
    (h₁ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₁)
    (h₂ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₂)
    (F : C(IConf G, ℝ)) (S : Finset ILink) (hF : MassGap.DLRLimit.IsLocalOnC S F) :
    ν₁ F = ν₂ F := by
  obtain ⟨ω₀⟩ := ν₁.nonempty
  rw [dlr_apply_at_zero hφc hφ0 hφ2 μ h₁ hF ω₀,
    dlr_apply_at_zero hφc hφ0 hφ2 μ h₂ hF ω₀]

#print axioms dlr_eq_of_isDLR_at_zero

/-- For a state satisfying `IsDLR (specCM … 0 μ)` and observables `F`, `H` local on disjoint `S`,
`T`, `ν (F * H) = ν F * ν H`. Applying the kernel at `S`, `spec_at_zero_mul_of_disjoint` takes `H`
out of the integral and `dlr_apply_at_zero` evaluates the rest as `ν F`, leaving `(ν F) • H`; the
DLR equation and `State.map_smul` finish.

For an observable supported on one half of the lattice and its reflection on the other, the two
supports are disjoint, so the pairing is `ν F * ν F` at this coupling.

DERIVED: `0` occurs twice — the pointwise lower bound on the density and the coupling in `specCM`.
`2` is the density's pointwise upper bound. -/
theorem dlr_mul_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν : MassGap.DLRLimit.State (IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν)
    {F H : C(IConf G, ℝ)} {S T : Finset ILink} (hST : Disjoint S T)
    (hF : MassGap.DLRLimit.IsLocalOnC S F) (hH : MassGap.DLRLimit.IsLocalOnC T H) :
    ν (F * H) = ν F * ν H := by
  have hkey : specCM hφc hφ0 hφ2 0 μ S (F * H) = (ν F : ℝ) • H := by
    ext ω
    rw [specCM_apply]
    have hcoe : (⇑(F * H) : IConf G → ℝ) = fun U => F U * H U := by funext U; simp
    rw [hcoe, spec_at_zero_mul_of_disjoint φ hST μ (isLocalOn_of_isLocalOnC hH) (⇑F) ω,
      ← dlr_apply_at_zero hφc hφ0 hφ2 μ hν hF ω]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
  calc ν (F * H) = ν (specCM hφc hφ0 hφ2 0 μ S (F * H)) := (hν S (F * H)).symm
    _ = ν ((ν F : ℝ) • H) := by rw [hkey]
    _ = ν F * ν H := ν.map_smul _ _

#print axioms dlr_mul_at_zero


/-- Two states satisfying `IsDLR (specCM … 0 μ)` agree at every continuous observable, for `G`
compact Hausdorff. `dlr_eq_of_isDLR_at_zero` gives agreement on the local observables and
`DLRLimit.State.eq_of_eqOn_localObs` carries it everywhere.

Scope: coupling zero only — the argument runs through `spec_at_zero_const`, where the kernel of a
local observable is constant in the boundary condition.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in each
of the two `specCM` hypotheses. `2` is the density's pointwise upper bound. -/
theorem dlr_unique_at_zero [T2Space G] {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν₁ ν₂ : MassGap.DLRLimit.State (IConf G)}
    (h₁ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₁)
    (h₂ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₂) :
    ∀ F : C(IConf G, ℝ), ν₁ F = ν₂ F := by
  refine MassGap.DLRLimit.State.eq_of_eqOn_localObs (fun F hF => ?_)
  obtain ⟨S, hS⟩ := MassGap.DLRLimit.mem_localObsAlg.mp hF
  exact dlr_eq_of_isDLR_at_zero hφc hφ0 hφ2 μ h₁ h₂ F S hS

#print axioms dlr_unique_at_zero


/-- The `DLRLimit.State (IConf G)` given by `fun f => spec φ β Λ μ f ω₀`, the kernel at volume `Λ`
evaluated at the frozen boundary configuration `ω₀`. Additivity is `spec_add` with the two bounds
from `bounded_of_continuous`, homogeneity is `spec_smul`, positivity is `spec_nonneg`, and
normalisation is `GibbsSpec.spec_one`.

DERIVED: `0` and `2` are the pointwise lower and upper bounds on the density, as at `specCM`. The
`1` of the `one'` field — `spec φ β Λ μ 1 ω₀ = 1`, proved by `spec_one` — is in the body. -/
noncomputable def specState {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] (ω₀ : IConf G)
    (Λ : Finset ILink) : MassGap.DLRLimit.State (IConf G) where
  toFun f := spec φ β Λ μ (⇑f) ω₀
  map_add' f g := by
    obtain ⟨Cf, hCf⟩ := bounded_of_continuous f.continuous
    obtain ⟨Cg, hCg⟩ := bounded_of_continuous g.continuous
    have hcoe : (⇑(f + g) : IConf G → ℝ) = fun U => f U + g U := by funext U; simp
    show spec φ β Λ μ (⇑(f + g)) ω₀ = spec φ β Λ μ (⇑f) ω₀ + spec φ β Λ μ (⇑g) ω₀
    rw [hcoe]
    exact spec_add hφc.measurable hφ0 hφ2 β Λ μ f.continuous.measurable hCf
      g.continuous.measurable hCg ω₀
  map_smul' c f := by
    have hcoe : (⇑(c • f) : IConf G → ℝ) = fun U => c * f U := by funext U; simp
    show spec φ β Λ μ (⇑(c • f)) ω₀ = c * spec φ β Λ μ (⇑f) ω₀
    rw [hcoe]
    exact spec_smul φ β Λ μ c (⇑f) ω₀
  nonneg' f hf := by
    show 0 ≤ spec φ β Λ μ (⇑f) ω₀
    exact spec_nonneg hφc.measurable hφ0 hφ2 β Λ μ hf ω₀
  one' := by
    have hcoe : (⇑(1 : C(IConf G, ℝ)) : IConf G → ℝ) = fun _ => (1 : ℝ) := by funext U; simp
    show spec φ β Λ μ (⇑(1 : C(IConf G, ℝ))) ω₀ = 1
    rw [hcoe]
    exact spec_one hφc.measurable hφ0 hφ2 β Λ μ ω₀

#print axioms specState

theorem specState_apply {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] (ω₀ : IConf G)
    (Λ : Finset ILink) (f : C(IConf G, ℝ)) :
    specState hφc hφ0 hφ2 β μ ω₀ Λ f = spec φ β Λ μ (⇑f) ω₀ := rfl

#print axioms specState_apply

/-- `specState … Λ (specCM … Λ' f) = specState … Λ f` for `Λ' ≤ Λ` and every continuous `f`: the
consistency hypothesis `DLRLimit.exists_dlr_state` takes, with the outer volume `Λ` and the inner
`Λ'`. It is `dlr_general` at the frozen boundary configuration, the observable's bound coming from
`bounded_of_continuous`.

DERIVED: `0` and `2` are the pointwise lower and upper bounds on the density. -/
theorem hcons_specState {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] (ω₀ : IConf G) :
    ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ),
      specState hφc hφ0 hφ2 β μ ω₀ Λ (specCM hφc hφ0 hφ2 β μ Λ' f)
        = specState hφc hφ0 hφ2 β μ ω₀ Λ f := by
  intro Λ Λ' hle f
  obtain ⟨C, hC⟩ := bounded_of_continuous f.continuous
  show spec φ β Λ μ (fun v => spec φ β Λ' μ (⇑f) v) ω₀ = spec φ β Λ μ (⇑f) ω₀
  exact dlr_general hφc.measurable hφ0 hφ2 β μ hle f.continuous.measurable hC ω₀

#print axioms hcons_specState

/-! ### Convergence along `atTop` at coupling zero

`dlr_unique_at_zero` gives agreement at every observable; `DLRLimit.tendsto_of_unique_dlr` asks for
equality of states, and `DLRLimit.State.eq_of_apply_eq` bridges the two. The finite-volume states
then converge along `atTop` rather than along an ultrafilter. -/

/-- `ν₁ = ν₂` for two states satisfying `IsDLR (specCM … 0 μ)`: `dlr_unique_at_zero` followed by
`DLRLimit.State.eq_of_apply_eq`. This is the form `DLRLimit.tendsto_of_unique_dlr` takes.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in each
of the two `specCM` hypotheses. `2` is the density's pointwise upper bound. -/
theorem dlr_unique_at_zero_eq [T2Space G] {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν₁ ν₂ : MassGap.DLRLimit.State (IConf G)}
    (h₁ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₁)
    (h₂ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₂) : ν₁ = ν₂ :=
  MassGap.DLRLimit.State.eq_of_apply_eq (dlr_unique_at_zero hφc hφ0 hφ2 μ h₁ h₂)

#print axioms dlr_unique_at_zero_eq

/-! ### Invariance of the zero-coupling state under a link bijection

`spec_at_zero_permConf` says the kernel commutes with a relabelling, so the relabelled state solves
the same DLR equation and uniqueness collapses it onto the original. This is the shape
`WilsonTransferReduction.transferData_of_state_facts`'s `hnu` asks for. -/

/-- Precomposition with `permConf e`, as an `ℝ`-linear endomorphism of `C(IConf G, ℝ)`. Additivity
and homogeneity are `rfl`, precomposition being pointwise. `ReflectionShift.ishiftObsL` is this at
the shift.

DERIVED: no numeral appears in the statement. -/
def permCM (e : ILink ≃ ILink) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨permConf e, continuous_permConf e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

#print axioms permCM

@[simp] theorem permCM_apply (e : ILink ≃ ILink) (F : C(IConf G, ℝ)) (U : IConf G) :
    permCM e F U = F (permConf e U) := rfl

#print axioms permCM_apply

/-- The state `fun F => ν (permCM e F)`. Additivity and homogeneity come from `permCM` being linear
and `ν` a state; positivity because precomposition moves no values; normalisation because
`permCM e 1 = 1`.

DERIVED: no numeral appears in the statement. The `1` of the `one'` field is the unit observable,
which precomposition fixes. -/
noncomputable def permState (e : ILink ≃ ILink) (ν : MassGap.DLRLimit.State (IConf G)) :
    MassGap.DLRLimit.State (IConf G) where
  toFun F := ν (permCM e F)
  map_add' f g := by
    show ν (permCM e (f + g)) = ν (permCM e f) + ν (permCM e g)
    rw [map_add]
    exact ν.map_add _ _
  map_smul' c f := by
    show ν (permCM e (c • f)) = c * ν (permCM e f)
    rw [map_smul]
    exact ν.map_smul _ _
  nonneg' f hf := ν.nonneg _ (fun U => hf _)
  one' := by
    show ν (permCM e (1 : C(IConf G, ℝ))) = 1
    have h1 : permCM e (1 : C(IConf G, ℝ)) = 1 := by ext U; rfl
    rw [h1]
    exact ν.map_one

#print axioms permState

/-- `permCM e (specCM … 0 μ Λ f) = specCM … 0 μ (Λ.image e) (permCM e f)`: the bundled form of
`spec_at_zero_permConf`, with the volume relabelled on the right.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in each
of the two `specCM` applications. `2` is the density's pointwise upper bound. -/
theorem specCM_permCM_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ] (e : ILink ≃ ILink)
    (Λ : Finset ILink) (f : C(IConf G, ℝ)) :
    permCM e (specCM hφc hφ0 hφ2 0 μ Λ f)
      = specCM hφc hφ0 hφ2 0 μ (Λ.image e) (permCM e f) := by
  ext U
  show spec φ 0 Λ μ (⇑f) (permConf e U)
    = spec φ 0 (Λ.image ⇑e) μ (⇑(permCM e f)) U
  rw [← spec_at_zero_permConf φ e Λ μ (⇑f) U]
  rfl

#print axioms specCM_permCM_at_zero

/-- `IsDLR (specCM … 0 μ) (permState e ν)` whenever `IsDLR (specCM … 0 μ) ν`. The kernel commutes
with the relabelling by `specCM_permCM_at_zero`, and the relabelled volume `Λ.image e` is absorbed
by the quantifier over volumes in `IsDLR`.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in the
hypothesis's and the conclusion's `specCM`. `2` is the density's pointwise upper bound. -/
theorem isDLR_permState_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ] (e : ILink ≃ ILink)
    {ν : MassGap.DLRLimit.State (IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν) :
    MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) (permState e ν) := by
  intro Λ f
  show ν (permCM e (specCM hφc hφ0 hφ2 0 μ Λ f)) = ν (permCM e f)
  rw [specCM_permCM_at_zero hφc hφ0 hφ2 μ e Λ f]
  exact hν (Λ.image e) (permCM e f)

#print axioms isDLR_permState_at_zero

/-- `ν (permCM e F) = ν F` at every continuous observable, for a state satisfying
`IsDLR (specCM … 0 μ)` and `G` compact Hausdorff. `isDLR_permState_at_zero` makes `permState e ν` a
DLR state and `dlr_unique_at_zero_eq` identifies it with `ν`.

Scope: `e` is an arbitrary link bijection — no geometric property of it is assumed. At zero coupling
the kernel is a product-Haar average, which does not distinguish links.

DERIVED: `0` occurs twice — the pointwise lower bound on the density and the coupling in `specCM`.
`2` is the density's pointwise upper bound. -/
theorem dlr_permCM_at_zero [T2Space G] {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ] (e : ILink ≃ ILink)
    {ν : MassGap.DLRLimit.State (IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν)
    (F : C(IConf G, ℝ)) : ν (permCM e F) = ν F := by
  have heq : permState e ν = ν :=
    dlr_unique_at_zero_eq hφc hφ0 hφ2 μ (isDLR_permState_at_zero hφc hφ0 hφ2 μ e hν) hν
  exact congrArg (fun s : MassGap.DLRLimit.State (IConf G) => s.toFun F) heq

#print axioms dlr_permCM_at_zero

/-! ### The same, with the coordinate twist

The state-level argument is unchanged: the twisted state solves the same DLR equation, so uniqueness
collapses it onto the original. This is the shape a reflection asks for, the twist carrying the group
inversion on the reflected links. -/

/-- Precomposition with `twistConf e σ`, as an `ℝ`-linear endomorphism of `C(IConf G, ℝ)`, given
continuity of each `σ l`. `permCM` is the case where every `σ l` is the identity;
`LatticeReflection.ireflObs` the case where `σ l` is the group inversion on `τ`-links.

DERIVED: no numeral appears in the statement. -/
def twistCM (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (hσc : ∀ l, Continuous (σ l)) :
    C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨twistConf e σ, continuous_twistConf e σ hσc⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

#print axioms twistCM

@[simp] theorem twistCM_apply (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G)
    (hσc : ∀ l, Continuous (σ l)) (F : C(IConf G, ℝ)) (U : IConf G) :
    twistCM e σ hσc F U = F (twistConf e σ U) := rfl

#print axioms twistCM_apply

/-- The state `fun F => ν (twistCM e σ hσc F)`, the twisted counterpart of `permState`. The four
fields are proved the same way, normalisation because `twistCM e σ hσc 1 = 1`.

DERIVED: no numeral appears in the statement. The `1` of the `one'` field is the unit observable,
which precomposition fixes. -/
noncomputable def twistState (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G)
    (hσc : ∀ l, Continuous (σ l)) (ν : MassGap.DLRLimit.State (IConf G)) :
    MassGap.DLRLimit.State (IConf G) where
  toFun F := ν (twistCM e σ hσc F)
  map_add' f g := by
    show ν (twistCM e σ hσc (f + g)) = ν (twistCM e σ hσc f) + ν (twistCM e σ hσc g)
    rw [map_add]
    exact ν.map_add _ _
  map_smul' c f := by
    show ν (twistCM e σ hσc (c • f)) = c * ν (twistCM e σ hσc f)
    rw [map_smul]
    exact ν.map_smul _ _
  nonneg' f hf := ν.nonneg _ (fun U => hf _)
  one' := by
    show ν (twistCM e σ hσc (1 : C(IConf G, ℝ))) = 1
    have h1 : twistCM e σ hσc (1 : C(IConf G, ℝ)) = 1 := by ext U; rfl
    rw [h1]
    exact ν.map_one

#print axioms twistState

/-- `twistCM e σ hσc (specCM … 0 μ Λ f) = specCM … 0 μ (Λ.image e) (twistCM e σ hσc f)`, given that
every `σ l` preserves `μ`: the bundled form of `spec_at_zero_twistConf`.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in each
of the two `specCM` applications. `2` is the density's pointwise upper bound. -/
theorem specCM_twistCM_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ] (e : ILink ≃ ILink)
    (σ : ILink → G ≃ᵐ G) (hσc : ∀ l, Continuous (σ l))
    (hσ : ∀ l, MeasurePreserving (σ l) μ μ) (Λ : Finset ILink) (f : C(IConf G, ℝ)) :
    twistCM e σ hσc (specCM hφc hφ0 hφ2 0 μ Λ f)
      = specCM hφc hφ0 hφ2 0 μ (Λ.image e) (twistCM e σ hσc f) := by
  ext U
  show spec φ 0 Λ μ (⇑f) (twistConf e σ U)
    = spec φ 0 (Λ.image ⇑e) μ (⇑(twistCM e σ hσc f)) U
  rw [← spec_at_zero_twistConf φ e σ Λ μ hσ (⇑f) U]
  rfl

#print axioms specCM_twistCM_at_zero

/-- `IsDLR (specCM … 0 μ) (twistState e σ hσc ν)` whenever `IsDLR (specCM … 0 μ) ν` and every `σ l`
preserves `μ`, by `specCM_twistCM_at_zero` and the quantifier over volumes.

DERIVED: `0` occurs three times — the pointwise lower bound on the density and the coupling in the
hypothesis's and the conclusion's `specCM`. `2` is the density's pointwise upper bound. -/
theorem isDLR_twistState_at_zero {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ] (e : ILink ≃ ILink)
    (σ : ILink → G ≃ᵐ G) (hσc : ∀ l, Continuous (σ l))
    (hσ : ∀ l, MeasurePreserving (σ l) μ μ)
    {ν : MassGap.DLRLimit.State (IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν) :
    MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) (twistState e σ hσc ν) := by
  intro Λ f
  show ν (twistCM e σ hσc (specCM hφc hφ0 hφ2 0 μ Λ f)) = ν (twistCM e σ hσc f)
  rw [specCM_twistCM_at_zero hφc hφ0 hφ2 μ e σ hσc hσ Λ f]
  exact hν (Λ.image e) (twistCM e σ hσc f)

#print axioms isDLR_twistState_at_zero

/-- `ν (twistCM e σ hσc F) = ν F` at every continuous observable, for a state satisfying
`IsDLR (specCM … 0 μ)`, `G` compact Hausdorff, and every `σ l` continuous and measure-preserving for
`μ`. `isDLR_twistState_at_zero` and `dlr_unique_at_zero_eq`, as in `dlr_permCM_at_zero`.

A lattice reflection is a relabelling of the links together with the group inversion on the
reflected ones, and Haar on a compact group preserves inversion, so it is an instance.

DERIVED: `0` occurs twice — the pointwise lower bound on the density and the coupling in `specCM`.
`2` is the density's pointwise upper bound. -/
theorem dlr_twistCM_at_zero [T2Space G] {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ] (e : ILink ≃ ILink)
    (σ : ILink → G ≃ᵐ G) (hσc : ∀ l, Continuous (σ l))
    (hσ : ∀ l, MeasurePreserving (σ l) μ μ)
    {ν : MassGap.DLRLimit.State (IConf G)}
    (hν : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν)
    (F : C(IConf G, ℝ)) : ν (twistCM e σ hσc F) = ν F := by
  have heq : twistState e σ hσc ν = ν :=
    dlr_unique_at_zero_eq hφc hφ0 hφ2 μ
      (isDLR_twistState_at_zero hφc hφ0 hφ2 μ e σ hσc hσ hν) hν
  exact congrArg (fun s : MassGap.DLRLimit.State (IConf G) => s.toFun F) heq

#print axioms dlr_twistCM_at_zero



/-- There is a state `ν` with `IsDLR (specCM … 0 μ) ν` such that
`specState … 0 μ ω₀ Λ f → ν f` along `Filter.atTop` on `Finset ILink`, at every continuous
observable. `DLRLimit.exists_infinite_volume_gibbs_state` produces the DLR state and
`DLRLimit.tendsto_of_unique_dlr` upgrades the ultrafilter limit, its uniqueness hypothesis supplied
by `dlr_unique_at_zero_eq`.

Scope: no subsequence or ultrafilter remains in the conclusion. It is stated at coupling zero only —
the argument runs through `spec_at_zero_const`, where the kernel of a local observable is constant
in the boundary condition.

DERIVED: `0` occurs four times — the pointwise lower bound on the density, and the coupling in
`specCM` and in the two uses of `specState`. `2` is the density's pointwise upper bound. -/
theorem tendsto_specState_at_zero [T2Space G] {φ : G → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω₀ : IConf G) :
    ∃ ν : MassGap.DLRLimit.State (IConf G),
      MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν ∧
      ∀ f : C(IConf G, ℝ),
        Filter.Tendsto (fun Λ : Finset ILink => specState hφc hφ0 hφ2 0 μ ω₀ Λ f)
          Filter.atTop (nhds (ν f)) := by
  obtain ⟨u, ν, hle, htend, hdlr, -, -⟩ :=
    MassGap.DLRLimit.exists_infinite_volume_gibbs_state G
      (specCM hφc hφ0 hφ2 0 μ) (specState hφc hφ0 hφ2 0 μ ω₀)
      (hcons_specState hφc hφ0 hφ2 0 μ ω₀)
  refine ⟨ν, hdlr, ?_⟩
  refine MassGap.DLRLimit.tendsto_of_unique_dlr
    (l := Filter.atTop) (κ := Finset ILink) (γ := specCM hφc hφ0 hφ2 0 μ)
    (specState hφc hφ0 hφ2 0 μ ω₀) ν ?_ ?_
  · intro Λ' f
    filter_upwards [Filter.eventually_ge_atTop Λ'] with Λ hΛ
    exact hcons_specState hφc hφ0 hφ2 0 μ ω₀ Λ Λ' hΛ f
  · intro ν' hν'
    exact dlr_unique_at_zero_eq hφc hφ0 hφ2 μ hν' hdlr

#print axioms tendsto_specState_at_zero


/-! ## Part 8 — the measure, at a general density

`DLRLimit.exists_infinite_volume_gibbs_measure` applied to `specCM` rather than to an abstract `γ`.
The conclusion mentions neither `State` nor `IsDLR`: it is a probability measure on the full
configuration space whose integral is unmoved by every finite volume's kernel, which is the DLR
equation for a measure, tested on continuous observables. -/

/-- For a compact Hausdorff `G`, a continuous density with `0 ≤ φ ≤ 2`, a single-link probability
measure `μ`, any real `β` and any boundary configuration `ω₀`, there is a probability measure `P` on
`IConf G` with `∫ U, spec φ β Λ μ f U ∂P = ∫ U, f U ∂P` at every finite volume `Λ` and every
continuous observable `f`.

`DLRLimit.exists_infinite_volume_gibbs_measure` at `specCM` and `specState`, with consistency from
`hcons_specState`; the DLR equation for the state is then transported through the representation.

Scope: the limit is taken along an ultrafilter refining `atTop` on the finite volumes, so it is
subsequential and `P` may depend on `ω₀`. The equation is tested on continuous observables only.

DERIVED: `0` is the pointwise lower bound on the density; `2` is its pointwise upper bound. -/
theorem exists_infinite_volume_gibbs_measure_of_density [T2Space G] {φ : G → ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G)
    [IsProbabilityMeasure μ] (ω₀ : IConf G) :
    ∃ P : Measure (IConf G), IsProbabilityMeasure P ∧
      ∀ (Λ : Finset ILink) (f : C(IConf G, ℝ)),
        (∫ U, spec φ β Λ μ (⇑f) U ∂P) = ∫ U, f U ∂P := by
  obtain ⟨P, ν, hP, hrep, hdlr⟩ :=
    MassGap.DLRLimit.exists_infinite_volume_gibbs_measure G
      (specCM hφc hφ0 hφ2 β μ) (specState hφc hφ0 hφ2 β μ ω₀)
      (hcons_specState hφc hφ0 hφ2 β μ ω₀)
  refine ⟨P, hP, fun Λ f => ?_⟩
  calc (∫ U, spec φ β Λ μ (⇑f) U ∂P)
      = ∫ U, (specCM hφc hφ0 hφ2 β μ Λ f) U ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall (fun U => rfl))
    _ = ν (specCM hφc hφ0 hφ2 β μ Λ f) := hrep _
    _ = ν f := hdlr Λ f
    _ = ∫ U, f U ∂P := (hrep f).symm

#print axioms exists_infinite_volume_gibbs_measure_of_density

/-! ## Part 9 — the instantiation at the Wilson density

The density is `WilsonAction.wilsonDensity`, that is `1 - Re tr U / N`; the single-link measure is
`CompactGauge.probHaar` on `SU N`; and the plaquette set of a finite volume is
`GibbsSpec.boundaryPlaqs`, so the conditioning reads a boundary condition rather than a free
one. -/

section Wilson

open MassGap.CompactGauge MassGap.WilsonAction

/-- `continuous_spec_right` at `φ := wilsonDensity (N := N)` and `μ := probHaar (SUN.SU N)`, with the
two range hypotheses discharged by `WilsonAction.wilsonDensity_nonneg` and `wilsonDensity_le_two`.

DERIVED: `0` is the value `N` is assumed to differ from, which is what makes the density
`1 - Re tr U / N` defined. -/
theorem wilson_continuous_spec_right (N : ℕ) (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    {f : IConf (MassGap.SUN.SU N) → ℝ} (hfc : Continuous f) :
    Continuous (fun ω : IConf (MassGap.SUN.SU N) =>
      spec (wilsonDensity (N := N)) β Λ (probHaar (MassGap.SUN.SU N)) f ω) :=
  continuous_spec_right continuous_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β Λ (probHaar (MassGap.SUN.SU N)) hfc

#print axioms wilson_continuous_spec_right

/-- For every `N ≠ 0` and every real `β`, there is a probability measure `P` on
`IConf (SUN.SU N) = ILink → SUN.SU N` with

    ∫ U, spec wilsonDensity β Λ probHaar f U ∂P = ∫ U, f U ∂P

at every finite volume `Λ` and every continuous observable `f`. It is
`exists_infinite_volume_gibbs_measure_of_density` at the Wilson density, with the range hypotheses
from `wilsonDensity_nonneg` and `wilsonDensity_le_two` and the boundary configuration anchored at
`fun _ => 1`, the identity configuration.

Scope: the only hypotheses are `N ≠ 0` and `β : ℝ` arbitrary — no coupling regime, volume bound or
smallness condition. As in the general statement, the limit is subsequential and `P` may depend on
the anchor; the equation is tested on continuous observables.

DERIVED: `0` is the value `N` is assumed to differ from, which makes the density `1 - Re tr U / N`
defined and places it in `[0, 2]`. -/
theorem exists_wilson_infinite_volume_gibbs_measure (N : ℕ) (hN : N ≠ 0) (β : ℝ) :
    ∃ P : Measure (IConf (MassGap.SUN.SU N)), IsProbabilityMeasure P ∧
      ∀ (Λ : Finset ILink) (f : C(IConf (MassGap.SUN.SU N), ℝ)),
        (∫ U, spec (wilsonDensity (N := N)) β Λ (probHaar (MassGap.SUN.SU N)) (⇑f) U ∂P)
          = ∫ U, f U ∂P :=
  exists_infinite_volume_gibbs_measure_of_density continuous_wilsonDensity
    (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β (probHaar (MassGap.SUN.SU N))
    (fun _ => 1)

#print axioms exists_wilson_infinite_volume_gibbs_measure

end Wilson

end MassGap.WilsonDLR
