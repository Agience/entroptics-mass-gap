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
floor uniform in the volume, and no such floor exists in this tree.

The DLR equation delivered is tested against CONTINUOUS observables. `GibbsSpec.IsGibbsMeasure` asks
for it against every bounded MEASURABLE observable; that strengthening needs a density argument this
file does not carry, so `IsGibbsMeasure` is not claimed.

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

/-- **DLR consistency with no bound on the observable.** `GibbsSpec.dlr_consistent` is stated for
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
