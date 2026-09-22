import Mathlib
import MassGap.GibbsSpec
import MassGap.InfiniteLattice
import MassGap.DLRLimit
import MassGap.SUN
import MassGap.WilsonAction

/-!
# MassGap.WilsonDLR — the infinite-volume Gibbs measure OF THE WILSON SPECIFICATION

`GibbsSpec` builds the finite-volume Wilson kernel `spec φ β Λ μ f ω` with a genuine boundary
condition and proves it DLR-consistent (`GibbsSpec.dlr_consistent`, instantiated at the real
`WilsonAction.wilsonDensity` on `SU(N)` by `GibbsSpec.wilson_dlr_consistent`). `DLRLimit` builds an
infinite-volume state and measure out of ANY specification presented as a family of maps
`γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ)`. The type of `γ` is what the two modules did not
share: it demands that the kernel carry CONTINUOUS observables to CONTINUOUS observables — the Feller
property — and `GibbsSpec` proves measurability in the boundary condition and nothing stronger.

This file proves the Feller property and closes the join.

## What is proved

* `continuous_spec_right` — for a continuous density `φ` with values in `[0,2]`, a fixed finite
  volume `Λ` and a continuous observable `f`, the map `ω ↦ spec φ β Λ μ f ω` is continuous. The
  numerator and the partition function are integrals over the finitely many links of `Λ` of an
  integrand continuous in `ω` and dominated by a constant, so `MeasureTheory.continuous_of_dominated`
  applies to each; `GibbsSpec.part_pos` keeps the quotient continuous. The domination is a constant
  because `IConf G` is compact, so a continuous observable on it is bounded.
* `spec_mem_localAlg` — the kernel preserves locality: if `f` is local on `S` then
  `spec φ β Λ μ f` is local on `S ∪ bdLinks Λ`, where `bdLinks Λ` is the finite set of links read by
  the plaquettes of `boundaryPlaqs Λ`. With continuity this is membership in
  `InfiniteLattice.localAlg`, so `specCM` lands in `C(IConf G, ℝ)` as a local observable and not by
  fiat.
* `specCM` / `specState` — the kernel as a map on continuous observables, and the finite-volume state
  obtained by freezing one boundary configuration `ω₀`. Its four `State` fields come from
  `spec_add`, `spec_smul`, `spec_nonneg` and `GibbsSpec.spec_one`.
* `dlr_general` — `GibbsSpec.dlr_consistent` freed of its `|f| ≤ 1` restriction by the exact
  homogeneity `spec_smul`, which is what an arbitrary `f : C(IConf G, ℝ)` needs.
* `exists_infinite_volume_gibbs_measure_of_density` — a probability measure `P` on `IConf G`
  satisfying the DLR equation `∫ spec φ β Λ μ f dP = ∫ f dP` at EVERY finite volume `Λ` and every
  continuous observable `f`.
* `exists_wilson_infinite_volume_gibbs_measure` — the same at `φ = WilsonAction.wilsonDensity` on
  `SU(N)` against `CompactGauge.probHaar`, at every real `β`. The Clay row A6 object for the Wilson
  theory rather than for an abstract specification.

## What is not proved

Uniqueness, translation invariance, and non-degeneracy. The limit is subsequential: it is taken along
an ultrafilter refining `atTop` on `Finset ILink`, and nothing here shows the net itself converges,
nor that the result is independent of the frozen boundary configuration `ω₀`.
`DLRLimit.not_isPointMass_of_uniform_variance` rules out a point mass only when handed a variance
floor uniform in the volume.

**Such a floor DOES exist**: `InfiniteVolume.exists_uniform_contact_floor` fixes one `δ₀ > 0` BEFORE
the aperture with `exp(−128β)·δ₀ ≤ wilsonCorrAt N β 0` at every aperture and every `β ≥ 0`, and
`PlaqVariance.corrClay_zero_eq` makes that contact value a plaquette VARIANCE.
`ClayNontriviality.clay_nontriviality_of_wilson_variance` composes it with the non-degeneracy
theorem.

**What is genuinely missing is the BRIDGE between the two volume indexings.** The floor is stated for
`wilsonCorrAt N β 0` on `WilsonHypercubic.bd (d := 4) (n := N+1)` — a finite PERIODIC lattice indexed
by an aperture. `specState` is indexed by a `Finset ILink` of `ℤ⁴` with a FROZEN boundary. Relating a
variance in one indexing to a variance in the other is the open step, and it is not a rewriting.

The DLR equation delivered HERE is tested against CONTINUOUS observables, so `IsGibbsMeasure` is not
claimed in this file. `GibbsSpec.IsGibbsMeasure` asks for the equation against every bounded
MEASURABLE observable, and `MassGap.WilsonGibbs` carries it there: not by approximating an
observable — the kernel is bounded by the sup norm, not the `L¹(P)` norm, so an `L¹` approximation
does not pass under it — but by exhibiting the kernel applied to `P` as a measure and using that two
finite Borel measures agreeing on continuous observables are equal.
`MassGap.WilsonGibbs.exists_wilson_isGibbsMeasure` is the result.

DERIVED: `4` is the problem's dimension, `2` the proved upper bound on the Wilson density (`WilsonAction.wilsonDensity_le_two`; nothing shows it attained or least, and at `SU(3)` the true supremum of `1 − Re tr g / 3` is `3/2`), `1` the normalisation of
a probability state. No constant is chosen here and none is fitted.

Build: `python research/code/lean_build.py build MassGap.WilsonDLR`.
-/

namespace MassGap.WilsonDLR

open MeasureTheory
open MassGap.GibbsSpec MassGap.WilsonLattice

/-! ## Part 0 — boundedness on the compact configuration space

`IConf G` is a product of copies of a compact group, so it is compact by Tychonoff and every
continuous observable on it is bounded. This is where the domination in Part 2 comes from: the bound
is a constant, and a constant is integrable against the probability measure `vol μ Λ`. -/

section Bounded

variable {G : Type} [TopologicalSpace G] [CompactSpace G]

/-- **A continuous function on the configuration space is bounded.** Compactness, not a hypothesis;
`InfiniteLattice.bounded_of_continuous` says the same thing in its own namespace. -/
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

`boundaryPlaqs Λ` is the plaquettes with AT LEAST ONE link in `Λ`, so some of their links lie outside
`Λ` and the kernel reads the boundary condition there. That set is finite, which is what makes the
kernel of a local observable local. -/

/-- **The links a finite volume's plaquettes read**, inside and outside `Λ` alike. -/
def bdLinks (Λ : Finset ILink) : Finset ILink :=
  (boundaryPlaqs Λ).biUnion (fun q => (ilinks q).toFinset)

#print axioms bdLinks

theorem mem_bdLinks {Λ : Finset ILink} {q : IPlaq} (hq : q ∈ boundaryPlaqs Λ) {l : ILink}
    (hl : l ∈ ilinks q) : l ∈ bdLinks Λ :=
  Finset.mem_biUnion.mpr ⟨q, hq, List.mem_toFinset.mpr hl⟩

#print axioms mem_bdLinks

/-! ## Part 2 — the working context

One instance block for the whole development: a compact, second-countable, Borel topological group.
`SU(N)` carries every one of these (`MassGap.SUN`), and `GibbsSpec`'s kernel is defined over exactly
the measurable half of them. -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-! ## Part 3 — continuity of the pieces in the boundary condition

The splice, the holonomy, the action and the Boltzmann weight, each continuous in `ω` with the inside
configuration `u` held fixed. These are the continuity mirrors of `GibbsSpec.measurable_splice_right`,
`GibbsSpec.measurable_ihol`, `GibbsSpec.measurable_actionOn` and `GibbsSpec.measurable_wt_left`. -/

/-- **The splice is continuous in the boundary configuration.** Coordinatewise: inside `Λ` it is a
constant, outside it is an evaluation. -/
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

/-- The ordered product of link-dependent step factors is continuous — the continuity mirror of
`WilsonLattice.measurable_stepListProd`, by the same list induction. -/
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

/-- **The plaquette holonomy is continuous** in the configuration. -/
theorem continuous_ihol (q : IPlaq) : Continuous (fun U : IConf G => ihol q U) := by
  unfold ihol wilsonHol
  exact continuous_stepListProd (ibd q)

#print axioms continuous_ihol

/-- **The energy of a finite plaquette set is continuous** when the density is. -/
theorem continuous_actionOn {φ : G → ℝ} (hφc : Continuous φ) (S : Finset IPlaq) :
    Continuous (fun U : IConf G => actionOn φ S U) := by
  unfold actionOn
  exact continuous_finsetSum S (fun q _ => hφc.comp (continuous_ihol q))

#print axioms continuous_actionOn

/-- **The Boltzmann weight is continuous in the boundary condition**, the inside configuration held
fixed. -/
theorem continuous_wt_right {φ : G → ℝ} (hφc : Continuous φ) (β : ℝ) (Λ : Finset ILink)
    (u : VConf G Λ) : Continuous (fun ω : IConf G => wt φ β Λ u ω) := by
  unfold wt
  exact Real.continuous_exp.comp
    (continuous_const.mul ((continuous_actionOn hφc (boundaryPlaqs Λ)).comp
      (continuous_splice_right Λ u)))

#print axioms continuous_wt_right

/-! ## Part 4 — THE FELLER PROPERTY

Both the numerator and the partition function are integrals over the finite product `VConf G Λ` of an
integrand continuous in `ω` and bounded by a constant uniformly in `ω`, so
`MeasureTheory.continuous_of_dominated` applies: `IConf G` is a countable product of second-countable
spaces, hence first countable, which is the hypothesis that lemma places on the parameter space.
`GibbsSpec.part_pos` makes the quotient continuous. -/

/-- **The unnormalised expectation is continuous in the boundary condition.** -/
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

/-- **The partition function is continuous in the boundary condition.** -/
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

/-- **THE FELLER PROPERTY.** The specification kernel of a finite volume carries a continuous
observable to a function of the boundary condition that is again continuous. This is the one
obligation `DLRLimit` records in the type of its `γ` and `GibbsSpec` does not discharge:
`GibbsSpec.measurable_spec_right` gives measurability, and measurability is not enough to evaluate a
weak-* limit of states. -/
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
the plaquettes of `boundaryPlaqs Λ` whose links stick out of `Λ`. Both are finite, so the image of a
local observable is local. -/

/-- **The kernel of a local observable is local.** `InfiniteLattice.IsLocalOn S F` is the statement
that `F` is unchanged by any modification of the configuration off `S`. -/
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

/-- **The kernel maps the local algebra into the local algebra.** Continuity from
`continuous_spec_right`, locality from `isLocalOn_spec`; together they are exactly membership in
`InfiniteLattice.localAlg`, which is what makes `specCM` below a legitimate element of
`C(IConf G, ℝ)` rather than a function declared continuous by fiat. -/
theorem spec_mem_localAlg {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {S : Finset ILink} {f : IConf G → ℝ} (hf : f ∈ MassGap.InfiniteLattice.localAlg S) :
    (fun ω => spec φ β Λ μ f ω) ∈ MassGap.InfiniteLattice.localAlg (S ∪ bdLinks Λ) :=
  ⟨continuous_spec_right hφc hφ0 hφ2 β Λ μ hf.1, isLocalOn_spec φ β Λ μ hf.2⟩

#print axioms spec_mem_localAlg

/-! ## Part 6 — the kernel is linear and positive in the observable

The three algebraic facts a state needs. `spec_smul` is exact homogeneity and needs no integrability
at all; `spec_add` needs the integrands to be integrable, which `GibbsSpec.integrable_num` supplies
from boundedness. -/

/-- **The kernel is homogeneous in the observable.** -/
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

/-- **The kernel is additive in the observable.** -/
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

/-- **The kernel is positive in the observable.** -/
theorem spec_nonneg {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : ∀ U, 0 ≤ f U) (ω : IConf G) : 0 ≤ spec φ β Λ μ f ω := by
  unfold spec
  refine div_nonneg ?_ (part_pos hφ hφ0 hφ2 β Λ μ ω).le
  unfold num
  exact integral_nonneg (fun u => mul_nonneg (hf _) (wt_pos φ β Λ u ω).le)

#print axioms spec_nonneg

/-- **DLR consistency at ANY bound on the observable.** A bound `hC : ∀ U, |f U| ≤ C` is still taken; what is removed is its being fixed at `1`. `GibbsSpec.dlr_consistent` is stated for
`|f| ≤ 1`; an arbitrary continuous observable on a compact space is bounded but not by `1`, so the
restriction is removed by scaling — exact homogeneity of `spec` in the observable lets the scale be
cancelled from both sides. -/
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

/-! ## Part 7 — the specification as `DLRLimit` consumes it

`specCM` is the kernel packaged as a map `C(IConf G, ℝ) → C(IConf G, ℝ)`, which the Feller property
makes well defined. `specState` freezes one boundary configuration and reads the kernel as a state.
`hcons_specState` is `dlr_general` at that configuration, with the index directions matched to
`DLRLimit.exists_dlr_state`. -/

/-- **The specification kernel on continuous observables.** The continuity field is
`continuous_spec_right`; this is the map whose existence was the whole gap between `GibbsSpec` and
`DLRLimit`.

DERIVED: `0` and `2` are the PROVED range of the plaquette density, not a chosen window. For
`wilsonDensity g = 1 − Re tr g / N` on `SU(N)` the trace ratio has modulus at most one, so the
density lies in `[0, 2]` — exactly `WilsonAction.wilsonDensity_nonneg` and
`wilsonDensity_le_two`, which are what discharge these two hypotheses at the Wilson instance. They
are hypotheses on `φ` rather than facts about it only because this development is stated for a
general density. -/
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

/-! ## Part 7b — zero coupling, where obligation II closes end to end

Obligation II is uniqueness of the DLR state. Its general half is `DLRLimit.State.eq_of_eqOn_localObs`:
two states agreeing on the LOCAL observables are equal, with no density and no separation hypothesis
left. Its Wilson half — that the specification PINS a DLR state on those local observables — is open
at general coupling and is proved here at coupling ZERO.

At zero coupling the Boltzmann weight is `Real.exp 0 = 1`, so the partition function is `1` and the
kernel is the plain product-Haar average over the volume. An observable local on `S` reads the
spliced configuration only inside `S`, and inside `S ⊆ Λ` the splice takes the INTEGRATION variable,
never the boundary condition — so the kernel of a local observable is a CONSTANT function of the
boundary. A DLR state is unmoved by the kernel, so it reads that observable as that one constant,
which is the same number for every DLR state. The general half then gives equality outright.

Nothing here is a limit, a cluster expansion or a Dobrushin condition; the boundary dependence is
not small, it is absent. That is exactly why this is the instance where the chain can be seen to
close, and not an approach to the general case.
-/

/-- **AT ZERO COUPLING THE BOLTZMANN WEIGHT IS ONE.**

DERIVED: the `0` is the coupling at which the statement is read, and the `1` is `Real.exp 0`.
Neither is chosen. -/
theorem wt_at_zero (φ : G → ℝ) (Λ : Finset ILink) (u : VConf G Λ) (ω : IConf G) :
    wt φ 0 Λ u ω = 1 := by
  unfold wt
  simp

#print axioms wt_at_zero

/-- **SO THE PARTITION FUNCTION IS ONE**, the product Haar measure being a probability measure.

DERIVED: the `0` is the coupling; the `1` is the total mass of a probability measure. -/
theorem part_at_zero (φ : G → ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω : IConf G) : part φ 0 Λ μ ω = 1 := by
  unfold part
  simp [wt_at_zero]

#print axioms part_at_zero

/-- **AND THE NUMERATOR IS THE PLAIN PRODUCT-HAAR AVERAGE.**

DERIVED: the `0` is the coupling. -/
theorem num_at_zero (φ : G → ℝ) (Λ : Finset ILink) (μ : Measure G) (f : IConf G → ℝ)
    (ω : IConf G) : num φ 0 Λ μ f ω = ∫ u, f (splice Λ u ω) ∂(vol μ Λ) := by
  unfold num
  simp [wt_at_zero]

#print axioms num_at_zero

/-- **THE KERNEL AT ZERO COUPLING IS THE PRODUCT-HAAR AVERAGE**, the normalisation being trivial.

DERIVED: the `0` is the coupling. -/
theorem spec_at_zero (φ : G → ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    (f : IConf G → ℝ) (ω : IConf G) :
    spec φ 0 Λ μ f ω = ∫ u, f (splice Λ u ω) ∂(vol μ Λ) := by
  unfold spec
  rw [num_at_zero, part_at_zero, div_one]

#print axioms spec_at_zero

/-! ### Relabelling the links

A bijection of the links acts on configurations by precomposition. At zero coupling the kernel
COMMUTES with that action, once the volume is relabelled along with everything else. This is the
measure-theoretic core of all three state facts `transferData_of_state_facts` needs, in the case
where no group inversion enters — which is exactly the case the SHIFT presents. -/

/-- **RELABEL A CONFIGURATION** along a bijection of the links. `InfiniteShift.ishiftConf` is this
at `e = ishiftLink`.

DERIVED: no numeral. -/
def permConf (e : ILink ≃ ILink) (U : IConf G) : IConf G := fun l => U (e l)

#print axioms permConf

/-- The relabelling is continuous: it is a reindexing of a product.

DERIVED: no numeral. -/
theorem continuous_permConf (e : ILink ≃ ILink) :
    Continuous (permConf (G := G) e) :=
  continuous_pi (fun l => continuous_apply (e l))

#print axioms continuous_permConf

/-- **THE INDEX EQUIVALENCE A LINK BIJECTION INDUCES** between a volume and its image. Injectivity
is what makes the inverse land back inside `Λ`.

DERIVED: no numeral. -/
def imgEquiv (e : ILink ≃ ILink) (Λ : Finset ILink) : ↑Λ ≃ ↑(Λ.image e) where
  toFun l := ⟨e l.1, Finset.mem_image_of_mem _ l.2⟩
  invFun m := ⟨e.symm m.1, by
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp m.2
    have hsym : e.symm m.1 = a := by rw [← hae, e.symm_apply_apply]
    rw [hsym]; exact ha⟩
  left_inv l := by apply Subtype.ext; simp
  right_inv m := by apply Subtype.ext; simp

#print axioms imgEquiv

/-- Relabelling a volume configuration, as a measurable equivalence. Same construction as
`GibbsSpec.toIn`, along `imgEquiv` instead of `subEquivIn`.

DERIVED: no numeral. -/
noncomputable def volReindex (e : ILink ≃ ILink) (Λ : Finset ILink) :
    VConf G (Λ.image e) ≃ᵐ VConf G Λ :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↑(Λ.image ⇑e) => G) (imgEquiv e Λ)).symm

#print axioms volReindex

theorem volReindex_apply (e : ILink ≃ ILink) (Λ : Finset ILink) (w : VConf G (Λ.image e))
    (l : ↑Λ) : volReindex (G := G) e Λ w l = w (imgEquiv e Λ l) := rfl

#print axioms volReindex_apply

/-- **AND IT PRESERVES THE PRODUCT MEASURE.** `measurePreserving_piCongrLeft` along the index
equivalence, taken backwards — the same move as `GibbsSpec.measurePreserving_toIn`.

DERIVED: no numeral. -/
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

/-- **THE SPLICE COMMUTES WITH THE RELABELLING**, once the volume is relabelled too. Inside the
volume both sides read the integration variable at the same relabelled index; outside it both read
the boundary condition at the relabelled link.

DERIVED: no numeral. -/
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

/-- **⭐ SO AT ZERO COUPLING THE KERNEL COMMUTES WITH A LINK RELABELLING.**

Relabelling the observable and the volume together, and evaluating at the relabelled boundary
condition, gives the same number. Nothing here is special to the shift or the reflection; it is the
relabelling alone.

DERIVED: the `0` is the coupling. -/
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

`ireflConf` is not a pure relabelling: it INVERTS the group element on `τ`-links. So the action that
`hinv` needs is a relabelling followed by a map applied coordinate by coordinate. The measure
argument gains exactly one factor — a coordinatewise map preserves a product measure when each
coordinate does. -/

/-- **RELABEL AND TWIST.** `permConf` is the case where every `σ l` is the identity.

DERIVED: no numeral. -/
def twistConf (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (U : IConf G) : IConf G :=
  fun l => σ l (U (e l))

#print axioms twistConf

/-- The twisted relabelling is continuous when each coordinate map is.

DERIVED: no numeral. -/
theorem continuous_twistConf (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G)
    (hσc : ∀ l, Continuous (σ l)) : Continuous (twistConf (G := G) e σ) :=
  continuous_pi (fun l => (hσc l).comp (continuous_apply (e l)))

#print axioms continuous_twistConf

/-- The coordinatewise part, as a measurable equivalence of volume configurations.

DERIVED: no numeral. -/
def coordTwist (Λ : Finset ILink) (σ : ILink → G ≃ᵐ G) : VConf G Λ ≃ᵐ VConf G Λ :=
  MeasurableEquiv.piCongrRight (fun l : ↑Λ => σ l.1)

#print axioms coordTwist

theorem coordTwist_apply (Λ : Finset ILink) (σ : ILink → G ≃ᵐ G) (v : VConf G Λ) (l : ↑Λ) :
    coordTwist (G := G) Λ σ v l = σ l.1 (v l) := rfl

#print axioms coordTwist_apply

/-- **A COORDINATEWISE MAP PRESERVES THE PRODUCT MEASURE** when each coordinate does. This is
`Measure.pi_map_pi`, the same move `ActionSplit.twist_measurePreserving` makes for a full index
type; here the index type is a volume's links.

DERIVED: no numeral. -/
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

/-- Relabelling a volume configuration AND twisting it, as a measurable equivalence.

DERIVED: no numeral. -/
noncomputable def volTwist (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink) :
    VConf G (Λ.image e) ≃ᵐ VConf G Λ :=
  (volReindex e Λ).trans (coordTwist Λ σ)

#print axioms volTwist

theorem volTwist_apply (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink)
    (w : VConf G (Λ.image e)) (l : ↑Λ) :
    volTwist (G := G) e σ Λ w l = σ l.1 (w (imgEquiv e Λ l)) := rfl

#print axioms volTwist_apply

/-- **AND IT PRESERVES THE PRODUCT MEASURE**, being a relabelling after a coordinatewise twist.

DERIVED: no numeral. -/
theorem measurePreserving_volTwist (e : ILink ≃ ILink) (σ : ILink → G ≃ᵐ G) (Λ : Finset ILink)
    (μ : Measure G) [IsProbabilityMeasure μ] (hσ : ∀ l, MeasurePreserving (σ l) μ μ) :
    MeasurePreserving (volTwist (G := G) e σ Λ) (vol μ (Λ.image e)) (vol μ Λ) :=
  (measurePreserving_coordTwist Λ σ μ hσ).comp (measurePreserving_volReindex e Λ μ)

#print axioms measurePreserving_volTwist

/-- **THE SPLICE COMMUTES WITH THE TWISTED RELABELLING.** Same case split as `permConf_splice`, with
the coordinate map applied on both sides of it.

DERIVED: no numeral. -/
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

/-- **⭐ SO AT ZERO COUPLING THE KERNEL COMMUTES WITH A TWISTED RELABELLING TOO.**

DERIVED: the `0` is the coupling. -/
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



/-- A bundled local observable is local unbundled. The two statements are the same Pi type; this
names the step rather than leaving it to defeq at each use site.

DERIVED: no numeral. -/
theorem isLocalOn_of_isLocalOnC {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : MassGap.DLRLimit.IsLocalOnC S F) : MassGap.InfiniteLattice.IsLocalOn S (⇑F) := hF

#print axioms isLocalOn_of_isLocalOnC

/-- **⭐ AT ZERO COUPLING THE KERNEL OF A LOCAL OBSERVABLE DOES NOT SEE THE BOUNDARY.**

For `S ⊆ Λ` the splice takes the integration variable at every link of `S`, so the integrand does
not move when the boundary condition does. This is the whole of obligation II(a) at this coupling.

DERIVED: the `0` is the coupling. -/
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

/-- **⭐ A DISJOINT LOCAL FACTOR PULLS OUT OF THE KERNEL.**

The kernel at volume `S` splices only the links of `S`. An observable local on a `T` disjoint from
`S` therefore reads the SAME configuration whatever the integration variable does, so it is a
constant of the integration and leaves the integral.

DERIVED: the `0` is the coupling. -/
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

/-- **⭐ THE VALUE OF A DLR STATE AT A LOCAL OBSERVABLE, AT ZERO COUPLING.**

The kernel at the observable's own support is constant in the boundary condition, so the DLR
equation reads the state's value straight off it — at ANY boundary configuration, the answer being
the same for all of them.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`; the `1` is the unit observable. -/
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


/-- **⭐ EVERY DLR STATE AT ZERO COUPLING READS A LOCAL OBSERVABLE AS THE SAME CONSTANT.**

Take the volume to be the observable's own support. The kernel is then constant in the boundary
condition, so it is `c • 1` for a number `c` that does not depend on the state; the DLR equation
turns `ν F` into `ν (c • 1) = c`. The base configuration needed to name `c` comes from
`State.nonempty` — a state cannot exist on an empty space.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range
(`WilsonAction.wilsonDensity_le_two`), as at `specCM`; the `1` is the unit observable. -/
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

/-- **⭐⭐ AT ZERO COUPLING THE STATE FACTORISES ON DISJOINT LOCAL SUPPORTS.**

`ν (F · H) = ν F · ν H` whenever `F` and `H` read disjoint finite sets of links. Apply the kernel at
`F`'s own support: `H` does not read those links, so it leaves the integral
(`spec_at_zero_mul_of_disjoint`), and what remains is `ν F` times `H`
(`dlr_apply_at_zero`). The DLR equation then reads off both factors.

**This is the input reflection positivity needs at this coupling.** For an observable on the
positive half of the lattice, its reflection lives on the negative half; the two supports are
disjoint, so the pairing is `ν F · ν F` and is nonnegative for that reason alone. No cluster
expansion and no Cauchy–Schwarz enter.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`. -/
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


/-- **⭐⭐⭐ THE DLR STATE AT ZERO COUPLING IS UNIQUE — OBLIGATION II, CLOSED AT THIS COUPLING.**

The Wilson half pins every DLR state on the local observables (`dlr_eq_of_isDLR_at_zero`); the
general half carries agreement there to agreement everywhere
(`DLRLimit.State.eq_of_eqOn_localObs`). Nothing is assumed beyond the gauge group being compact
Hausdorff, which `SU N` is.

This is the first instance in which obligation II closes, and it is what shows the II interfaces
compose rather than merely typecheck. It does NOT bear on general coupling: at zero coupling the
boundary dependence is absent, not small.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`. -/
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


/-- **The finite-volume state with the boundary configuration `ω₀` frozen.** Linearity and positivity
are `spec_add`, `spec_smul` and `spec_nonneg`; normalisation is `GibbsSpec.spec_one`.

DERIVED: `0` and `2` are the proved range of the plaquette density, as at `specCM` —
`WilsonAction.wilsonDensity_nonneg` and `wilsonDensity_le_two` for `1 − Re tr g / N`. `1` is the
unit of `C(IConf G, ℝ)`, the constant-one observable, together with the value the state must take on
it: `one'` is `spec φ β Λ μ 1 ω₀ = 1`, which is what makes this a STATE rather than an arbitrary
positive functional, and it is proved by `spec_one`, not imposed. -/
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

/-- **The consistency hypothesis of `DLRLimit.exists_dlr_state`, discharged.** The outer volume is
`Λ`, the inner one `Λ'`, and the equation is `GibbsSpec.dlr_consistent` read at the frozen boundary
configuration with the `|f| ≤ 1` restriction removed by `dlr_general`. -/
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

/-! ### The zero-coupling payoff: `htend`, proved

`dlr_unique_at_zero` gives agreement at every observable; `DLRLimit.tendsto_of_unique_dlr` asks for
equality of STATES. `DLRLimit.State.eq_of_apply_eq` closes that gap, and the finite-volume states
then converge along `atTop` rather than merely along some ultrafilter — which is exactly the
hypothesis `htend` that obligation II exists to supply. -/

/-- **THE DLR STATE AT ZERO COUPLING IS UNIQUE, AS A STATE.**

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`. -/
theorem dlr_unique_at_zero_eq [T2Space G] {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (μ : Measure G) [IsProbabilityMeasure μ]
    {ν₁ ν₂ : MassGap.DLRLimit.State (IConf G)}
    (h₁ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₁)
    (h₂ : MassGap.DLRLimit.IsDLR (specCM hφc hφ0 hφ2 0 μ) ν₂) : ν₁ = ν₂ :=
  MassGap.DLRLimit.State.eq_of_apply_eq (dlr_unique_at_zero hφc hφ0 hφ2 μ h₁ h₂)

#print axioms dlr_unique_at_zero_eq

/-! ### The zero-coupling state is invariant under EVERY link bijection

`spec_at_zero_permConf` says the kernel commutes with a relabelling. So the relabelled state solves
the same DLR equation, and uniqueness collapses it onto the original. This is the tool all three of
`transferData_of_state_facts`'s state facts want; `hnu` is the case it settles outright. -/

/-- **RELABEL AN OBSERVABLE** along a link bijection, as a linear map. `ReflectionShift.ishiftObsL`
is this at the shift.

DERIVED: no numeral. -/
def permCM (e : ILink ≃ ILink) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨permConf e, continuous_permConf e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

#print axioms permCM

@[simp] theorem permCM_apply (e : ILink ≃ ILink) (F : C(IConf G, ℝ)) (U : IConf G) :
    permCM e F U = F (permConf e U) := rfl

#print axioms permCM_apply

/-- **RELABEL A STATE.** Positivity and normalisation survive because the relabelling is
precomposition with a map of the configuration space, so it moves no values.

DERIVED: the `1` is the unit observable, which precomposition fixes. -/
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

/-- **THE KERNEL COMMUTES WITH THE RELABELLING**, bundled. `spec_at_zero_permConf` with the volume
carried along.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`. -/
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

/-- **SO THE RELABELLED STATE IS AGAIN A DLR STATE**, for the same specification and the same
volumes — the volume relabelling is absorbed by the quantifier over volumes.

DERIVED: the `0` is the coupling; the `2` is the plaquette density's proved upper end. -/
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

/-- **⭐⭐ AND UNIQUENESS COLLAPSES IT: THE ZERO-COUPLING STATE IS INVARIANT UNDER EVERY LINK
BIJECTION.**

Nothing is assumed of the bijection — not that it is a shift, not that it preserves any geometry.
The whole content is that at zero coupling the kernel is a product-Haar average, which does not
know one link from another.

DERIVED: the `0` is the coupling; the `2` is the plaquette density's proved upper end. -/
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

`hnu` needed only the relabelling. `hinv` needs the twist as well, and the state-level argument is
unchanged: the twisted state solves the same DLR equation, so uniqueness collapses it. -/

/-- **RELABEL AND TWIST AN OBSERVABLE**, as a linear map. `permCM` is the case where every `σ l` is
the identity; `LatticeReflection.ireflObs` is the case where `σ l` is the group inversion on
`τ`-links.

DERIVED: no numeral. -/
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

/-- **RELABEL AND TWIST A STATE.**

DERIVED: the `1` is the unit observable, which precomposition fixes. -/
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

/-- **THE KERNEL COMMUTES WITH THE TWISTED RELABELLING**, bundled.

DERIVED: the `0` is the coupling; the `2` is the plaquette density's proved upper end. -/
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

/-- **SO THE TWISTED STATE IS AGAIN A DLR STATE.**

DERIVED: the `0` is the coupling; the `2` is the plaquette density's proved upper end. -/
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

/-- **⭐⭐ AND THE ZERO-COUPLING STATE IS INVARIANT UNDER EVERY TWISTED RELABELLING** whose
coordinate maps preserve the single-link measure.

This is what `hinv` consumes: the lattice reflection is a relabelling of the links together with a
group inversion on the `τ`-links, and Haar on a compact group preserves inversion.

DERIVED: the `0` is the coupling; the `2` is the plaquette density's proved upper end. -/
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



/-- **⭐⭐⭐ AT ZERO COUPLING THE FINITE-VOLUME STATES CONVERGE ALONG `atTop` — `htend`, PROVED.**

Existence supplies a DLR state along SOME ultrafilter; uniqueness upgrades that to convergence along
`atTop` itself, for every continuous observable. No subsequence and no choice of ultrafilter remains
in the conclusion.

This is obligation II delivering what it was for. It holds at coupling ZERO only: the argument runs
through `spec_at_zero_const`, where the kernel of a local observable is constant in the boundary
condition, and at general coupling that constancy is false.

DERIVED: the `0` is the coupling; the `2` is the proved upper end of the plaquette density's range,
as at `specCM`. -/
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


/-! ## Part 8 — the infinite-volume Gibbs measure of the specification

`DLRLimit.exists_infinite_volume_gibbs_measure` is now applied to the genuine kernel rather than to
an abstract `γ`. The conclusion is stated without mentioning `State` or `IsDLR`: a probability
measure on the full configuration space whose integral is unmoved by every finite volume's kernel.
That equation, `∫ spec φ β Λ μ f dP = ∫ f dP`, is the DLR equation for a measure, tested on
continuous observables. -/

/-- **THE INFINITE-VOLUME GIBBS MEASURE OF A BOUNDED CONTINUOUS PLAQUETTE DENSITY.** For a compact
gauge group, a continuous plaquette density with values in `[0,2]`, a single-link probability measure
and any real `β`, there is a probability measure on the configuration space of the FULL infinite
four-dimensional lattice satisfying the DLR equation at every finite volume and every continuous
observable.

The boundary configuration `ω₀` is the one the finite-volume family is anchored at; the limit is
taken along an ultrafilter refining `atTop` on the finite volumes, so it is subsequential and the
limiting measure may depend on `ω₀`. -/
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

/-! ## Part 9 — the Wilson theory

The density is `WilsonAction.wilsonDensity`, the genuine `1 − Re tr U / N`; the single-link measure is
`CompactGauge.probHaar` on `SU(N)`; the plaquette set of a finite volume is `GibbsSpec.boundaryPlaqs`,
so the conditioning is a real boundary condition and not a free one. -/

section Wilson

open MassGap.CompactGauge MassGap.WilsonAction

/-- **The Wilson specification has the Feller property on `SU(N)`** — the statement that was the gap,
at the genuine density and the genuine measure. -/
theorem wilson_continuous_spec_right (N : ℕ) (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    {f : IConf (MassGap.SUN.SU N) → ℝ} (hfc : Continuous f) :
    Continuous (fun ω : IConf (MassGap.SUN.SU N) =>
      spec (wilsonDensity (N := N)) β Λ (probHaar (MassGap.SUN.SU N)) f ω) :=
  continuous_spec_right continuous_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β Λ (probHaar (MassGap.SUN.SU N)) hfc

#print axioms wilson_continuous_spec_right

/-- **THE INFINITE-VOLUME GIBBS MEASURE OF THE WILSON SPECIFICATION ON `SU(N)`.**

For every `N ≠ 0` and every real `β` there is a probability measure `P` on the configuration space of
the infinite four-dimensional lattice `IConf (SU N) = ILink → SU N` such that, for every finite
volume `Λ` and every continuous observable `f`,

    ∫ spec wilsonDensity β Λ probHaar f dP = ∫ f dP,

which is the DLR equation for the Wilson specification. The object Clay row A6 asks for, carried by
the Wilson action rather than by an abstract specification.

Hypotheses, in full: `N ≠ 0` (so the density `1 − Re tr U / N` is defined and lies in `[0,2]`) and
`β : ℝ` arbitrary. No coupling regime, no volume bound, no smallness condition. The boundary
configuration the family is anchored at is the identity configuration. -/
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
