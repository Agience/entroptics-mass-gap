import Mathlib
import MassGap.GibbsSpec
import MassGap.ActionSplit
import MassGap.WilsonDLR
import MassGap.HaarVariance
import MassGap.ReflectionHalfSpace

/-!
# MassGap.SpecVarianceFloor — the Gibbs kernel's variance, bounded below uniformly in the volume

Part IV of `VarianceBridge.clay_four_parts` asks for a `cvar > 0` with
`cvar ≤ specState … Λ (f₀ * f₀) - (specState … Λ f₀)²` for all large `Λ`. The observable, the boundary
condition and the constant are the caller's to choose, so nothing forces a comparison with the
periodic torus — a floor proved directly on `ℤ⁴` discharges Part IV outright.

**The move that makes the bound uniform in the volume.** Take the observable to read a single link
`l₀` and cut the action at `boundaryPlaqs {l₀}`, the plaquettes having `l₀` among their links. That set
does not depend on `Λ` once `l₀ ∈ Λ`, so a bound written in its cardinality carries no region. Every
region-indexed cut — `iplqZero`, `iplqPlus`, `boundaryPlaqs` of a smaller box — leaves a factor whose
plaquette count grows, which is why `BoxNumericFloor`'s floor decays as the box grows.

The remaining factor is then never evaluated: it is common to numerator and denominator and is
discharged by the inequality `part ≤ ∫ rest`, not by an identity. `ContactFloor` does the same on the
torus, and that is what keeps the volume out of the exponent.

`GibbsSpec` and `ActionSplit` do not import one another, so something has to bring them together;
`ReflectionHalfSpace` already uses both, and what is new here is `GibbsSpec.spec` against
`ActionSplit.block_factor` in particular.
-/

namespace MassGap.SpecVarianceFloor

open MeasureTheory
open MassGap.GibbsSpec

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- **The centred square at one link factors against the remaining weight.**

`ActionSplit.block_factor` at the blocks `{l₀}` and its complement: the centred square reads only
`l₀`, and the remainder does not read `l₀` at all (`GibbsSpec.actionOn_sdiff_fillLink`), so the
integral of the product is the product of the integrals. `ActionSplit.integral_eval_cvol` then
evaluates the one-link factor as an integral over the group itself, with no region left in it.

`GibbsSpec.vol` is `ActionSplit.cvol` at `↥Λ`, so both lemmas apply without transport.

DERIVED: `2` is the exponent of the centred square. `c` and `β` are the caller's. -/
theorem integral_centred_mul_rest {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ)
    {Λ : Finset ILink} {l₀ : ILink} (hl₀ : l₀ ∈ Λ) (μ : Measure G) [IsProbabilityMeasure μ]
    {h : G → ℝ} (hh : Measurable h) (c : ℝ) (ω : IConf G) :
    (∫ u, (h (u ⟨l₀, hl₀⟩) - c) ^ 2
        * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω))
        ∂(vol μ Λ))
      = (∫ g, (h g - c) ^ 2 ∂μ)
        * ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
            (splice Λ u ω)) ∂(vol μ Λ) := by
  classical
  set l₀' : ↑Λ := ⟨l₀, hl₀⟩ with hl'
  set S : Finset ↑Λ := {l₀'} with hSdef
  set T : Finset ↑Λ := Sᶜ with hTdef
  set Φ : (↑S → G) → ℝ := fun v => (h (v ⟨l₀', Finset.mem_singleton_self _⟩) - c) ^ 2 with hΦdef
  set Ψ : (↑T → G) → ℝ := fun w =>
    Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
      (splice Λ (fillLink l₀' w) ω)) with hΨdef
  have hΦm : Measurable Φ :=
    ((hh.comp (measurable_pi_apply _)).sub_const c).pow_const 2
  have hΨm : Measurable Ψ :=
    Real.continuous_exp.measurable.comp
      ((((measurable_actionOn hφ _).comp (measurable_splice_left Λ ω)).comp
        (measurable_fillLink l₀')).const_mul (-β))
  have hΦpt : ∀ u : VConf G Λ, Φ (fun i : ↑S => u i.val) = (h (u l₀') - c) ^ 2 :=
    fun _ => rfl
  have hΨpt : ∀ u : VConf G Λ, Ψ (fun i : ↑T => u i.val)
      = Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω)) := by
    intro u
    simp only [hΨdef]
    rw [actionOn_sdiff_fillLink hl₀ φ u ω]
  have hfac := MassGap.ActionSplit.block_factor μ S T disjoint_compl_right Φ Ψ hΦm hΨm
  have hone : (∫ u, Φ (fun i : ↑S => u i.val) ∂(vol μ Λ)) = ∫ g, (h g - c) ^ 2 ∂μ := by
    simp only [hΦpt]
    exact MassGap.ActionSplit.integral_eval_cvol μ l₀' (fun g => (h g - c) ^ 2)
      ((hh.sub_const c).pow_const 2)
  calc (∫ u, (h (u l₀') - c) ^ 2
        * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω))
        ∂(vol μ Λ))
      = ∫ u, Φ (fun i : ↑S => u i.val) * Ψ (fun i : ↑T => u i.val) ∂(vol μ Λ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only [hΦpt u, hΨpt u]
    _ = (∫ u, Φ (fun i : ↑S => u i.val) ∂(vol μ Λ))
          * ∫ u, Ψ (fun i : ↑T => u i.val) ∂(vol μ Λ) := hfac
    _ = (∫ g, (h g - c) ^ 2 ∂μ)
          * ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
              (splice Λ u ω)) ∂(vol μ Λ) := by
        rw [hone]
        refine congrArg _ (integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_)))
        simp only [hΨpt u]

#print axioms integral_centred_mul_rest

/-- The remainder factor is measurable. -/
theorem measurable_rest {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ)
    (Λ : Finset ILink) (l₀ : ILink) (ω : IConf G) :
    Measurable (fun u : VConf G Λ => Real.exp (-β * actionOn φ
      (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω))) :=
  Real.continuous_exp.measurable.comp
    (((measurable_actionOn hφ _).comp (measurable_splice_left Λ ω)).const_mul (-β))

#print axioms measurable_rest

/-- The remainder factor is integrable, bounded by an exponential of its own plaquette count. -/
theorem integrable_rest {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (l₀ : ILink) (μ : Measure G)
    [IsProbabilityMeasure μ] (ω : IConf G) :
    Integrable (fun u : VConf G Λ => Real.exp (-β * actionOn φ
      (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω))) (vol μ Λ) :=
  integrable_of_bounded _ (measurable_rest hφ β Λ l₀ ω)
    (fun u => MassGap.ReflectionHalfSpace.abs_exp_neg_actionOn_le hφ0 hφ2 β _ _)

#print axioms integrable_rest

/-- **The partition function is at most the remainder's integral.**

The factor the split leaves at `l₀` is at most one at nonnegative coupling, so dropping it can only
increase the integral. This is the inequality that lets the remainder cancel: it is never evaluated,
only compared with the denominator it sits above.

DERIVED: `0` is the lower bound on `β` and on the density; `2` is the density's ceiling. -/
theorem part_le_integral_rest {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) {β : ℝ} (hβ : 0 ≤ β)
    {Λ : Finset ILink} {l₀ : ILink} (hl₀ : l₀ ∈ Λ) (μ : Measure G) [IsProbabilityMeasure μ]
    (ω : IConf G) :
    part φ β Λ μ ω
      ≤ ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
          (splice Λ u ω)) ∂(vol μ Λ) := by
  refine integral_mono (integrable_wt hφ hφ0 hφ2 β Λ μ ω)
    (integrable_rest hφ hφ0 hφ2 β Λ l₀ μ ω) (fun u => ?_)
  rw [wt_split_at_link hl₀ φ β u ω]
  have h1 := exp_neg_actionOn_le_one hφ0 hβ (boundaryPlaqs {l₀}) (splice Λ u ω)
  have h2 : (0 : ℝ) < Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
      (splice Λ u ω)) := Real.exp_pos _
  nlinarith

#print axioms part_le_integral_rest

/-- **The numerator, bounded below by a region-free constant times the remainder's integral.**

The factor at `l₀` is at least `exp (-(|β| * card (boundaryPlaqs {l₀}) * 2))`, and
`boundaryPlaqs {l₀}` does not depend on `Λ`, so that constant carries no volume. What is left
factorises by `integral_centred_mul_rest` into the group integral and the remainder's integral.

DERIVED: `0` is the lower bound on the density; `2` is its ceiling and the exponent of the square.
`c` and `Ch` are the caller's. -/
theorem num_centred_ge {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    {Λ : Finset ILink} {l₀ : ILink} (hl₀ : l₀ ∈ Λ) (μ : Measure G) [IsProbabilityMeasure μ]
    {h : G → ℝ} (hh : Measurable h) {Ch : ℝ} (hhb : ∀ g, |h g| ≤ Ch) (c : ℝ) (ω : IConf G) :
    Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
        * ((∫ g, (h g - c) ^ 2 ∂μ)
          * ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
              (splice Λ u ω)) ∂(vol μ Λ))
      ≤ num φ β Λ μ (fun U => (h (U l₀) - c) ^ 2) ω := by
  classical
  have hCh0 : (0 : ℝ) ≤ Ch := le_trans (abs_nonneg _) (hhb 1)
  have hsqb : ∀ g : G, |(h g - c) ^ 2| ≤ (Ch + |c|) ^ 2 := by
    intro g
    have h1 := abs_le.mp (hhb g)
    have h2 := abs_nonneg c
    have h3 := neg_abs_le c
    have h4 := le_abs_self c
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hfm : Measurable (fun U : IConf G => (h (U l₀) - c) ^ 2) :=
    ((hh.comp (measurable_pi_apply l₀)).sub_const c).pow_const 2
  have hfb : ∀ U : IConf G, |(h (U l₀) - c) ^ 2| ≤ (Ch + |c|) ^ 2 := fun U => hsqb _
  have hnum : num φ β Λ μ (fun U => (h (U l₀) - c) ^ 2) ω
      = ∫ u, (h (u ⟨l₀, hl₀⟩) - c) ^ 2
          * (Real.exp (-β * actionOn φ (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω))
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
                (splice Λ u ω))) ∂(vol μ Λ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show (h (splice Λ u ω l₀) - c) ^ 2 * wt φ β Λ u ω = _
    rw [splice_mem hl₀, wt_split_at_link hl₀ φ β u ω]
  have hRHSint : Integrable (fun u : VConf G Λ => (h (u ⟨l₀, hl₀⟩) - c) ^ 2
      * (Real.exp (-β * actionOn φ (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω))
        * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
            (splice Λ u ω)))) (vol μ Λ) := by
    refine (integrable_num hφ hφ0 hφ2 β Λ μ hfm hfb ω).congr
      (Filter.Eventually.of_forall (fun u => ?_))
    show (h (splice Λ u ω l₀) - c) ^ 2 * wt φ β Λ u ω = _
    rw [splice_mem hl₀, wt_split_at_link hl₀ φ β u ω]
  have hLint : Integrable (fun u : VConf G Λ =>
      Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
        * ((h (u ⟨l₀, hl₀⟩) - c) ^ 2
          * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
              (splice Λ u ω)))) (vol μ Λ) := by
    refine Integrable.const_mul ?_ _
    refine integrable_of_bounded _
      ((((hh.comp (measurable_pi_apply (⟨l₀, hl₀⟩ : ↑Λ))).sub_const c).pow_const 2).mul
        (measurable_rest hφ β Λ l₀ ω))
      (C := (Ch + |c|) ^ 2
        * Real.exp (|β| * (((boundaryPlaqs Λ \ boundaryPlaqs {l₀}).card : ℝ) * 2)))
      (fun u => ?_)
    rw [abs_mul]
    exact mul_le_mul (hsqb _)
      (MassGap.ReflectionHalfSpace.abs_exp_neg_actionOn_le hφ0 hφ2 β _ _) (abs_nonneg _)
      (by positivity)
  have hpt : ∀ u : VConf G Λ,
      Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
        * ((h (u ⟨l₀, hl₀⟩) - c) ^ 2
          * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω)))
      ≤ (h (u ⟨l₀, hl₀⟩) - c) ^ 2
          * (Real.exp (-β * actionOn φ (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω))
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
                (splice Λ u ω))) := by
    intro u
    have hTge := MassGap.ReflectionHalfSpace.exp_neg_actionOn_ge hφ0 hφ2 β
      (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω)
    have hR0 : (0 : ℝ) < Real.exp (-β * actionOn φ
      (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω)) := Real.exp_pos _
    have hsq : (0 : ℝ) ≤ (h (u ⟨l₀, hl₀⟩) - c) ^ 2 := sq_nonneg _
    calc Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
          * ((h (u ⟨l₀, hl₀⟩) - c) ^ 2
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω)))
        = ((h (u ⟨l₀, hl₀⟩) - c) ^ 2
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω)))
          * Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2))) := by ring
      _ ≤ ((h (u ⟨l₀, hl₀⟩) - c) ^ 2
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀}) (splice Λ u ω)))
          * Real.exp (-β * actionOn φ (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω)) :=
          mul_le_mul_of_nonneg_left hTge (mul_nonneg hsq hR0.le)
      _ = (h (u ⟨l₀, hl₀⟩) - c) ^ 2
            * (Real.exp (-β * actionOn φ (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω))
              * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
                  (splice Λ u ω))) := by ring
  rw [hnum]
  calc Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
        * ((∫ g, (h g - c) ^ 2 ∂μ)
          * ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
              (splice Λ u ω)) ∂(vol μ Λ))
      = Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
          * ∫ u, (h (u ⟨l₀, hl₀⟩) - c) ^ 2
              * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
                  (splice Λ u ω)) ∂(vol μ Λ) := by
        rw [integral_centred_mul_rest hφ β hl₀ μ hh c ω]
    _ = ∫ u, Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
          * ((h (u ⟨l₀, hl₀⟩) - c) ^ 2
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
                (splice Λ u ω))) ∂(vol μ Λ) := (integral_const_mul _ _).symm
    _ ≤ ∫ u, (h (u ⟨l₀, hl₀⟩) - c) ^ 2
          * (Real.exp (-β * actionOn φ (boundaryPlaqs ({l₀} : Finset ILink)) (splice Λ u ω))
            * Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
                (splice Λ u ω))) ∂(vol μ Λ) := integral_mono hLint hRHSint hpt

#print axioms num_centred_ge

/-- **A variance floor for the Gibbs kernel, uniform in the volume.**

For an observable reading one link `l₀`, the kernel's variance at any region containing `l₀` is at
least `exp (-(|β| * card (boundaryPlaqs {l₀}) * 2))` times the observable's variance under `μ` itself.

⚠ On its own this says nothing when `h` is constant, since both sides are then `0`. The content is
supplied by the caller's choice of `h`; `wilson_eventual_variance_floor` takes the real trace, whose
variance `HaarVariance.haar_variance_reTr_pos` puts strictly above zero at `2 ≤ N`.

**Nothing on the left mentions the region.** `boundaryPlaqs {l₀}` is the set of plaquettes having `l₀`
among their links, and it does not grow with `Λ`. That is the whole content: the same argument cut at
any region-indexed plaquette set gives a bound that decays to zero as the region grows, which is what
`BoxNumericFloor.box_reflection_form_ge_number` does and why that floor cannot be used here.

**How the remainder leaves.** `num_centred_ge` bounds the numerator below by a constant times the
remainder's integral, and `part_le_integral_rest` bounds the denominator above by that same integral.
So it cancels without ever being evaluated — `ContactFloor` makes the same move on the torus. Any
route that computed it would put the region's plaquette count back into the exponent.

`WilsonDLR.spec_variance_centred` supplies the centred form, and
`ActionSplit.variance_le_integral_centred` discards the Gibbs mean, which depends on the coupling, the
region and the boundary condition and is never evaluated either.

DERIVED: `0` is the lower bound on `β` and on the density; `2` is the density's ceiling and the
exponent of each square. `Ch` is the caller's. -/
theorem spec_variance_floor [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [BorelSpace G] [SecondCountableTopology G]
    {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) {β : ℝ} (hβ : 0 ≤ β)
    {Λ : Finset ILink} {l₀ : ILink} (hl₀ : l₀ ∈ Λ) (μ : Measure G) [IsProbabilityMeasure μ]
    {h : G → ℝ} (hh : Measurable h) {Ch : ℝ} (hhb : ∀ g, |h g| ≤ Ch) (ω : IConf G) :
    Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
        * ((∫ g, h g ^ 2 ∂μ) - (∫ g, h g ∂μ) ^ 2)
      ≤ spec φ β Λ μ (fun U => h (U l₀) * h (U l₀)) ω
        - (spec φ β Λ μ (fun U => h (U l₀)) ω) ^ 2 := by
  classical
  have hCh0 : (0 : ℝ) ≤ Ch := le_trans (abs_nonneg _) (hhb 1)
  have hfm : Measurable (fun U : IConf G => h (U l₀)) := hh.comp (measurable_pi_apply l₀)
  have hfb : ∀ U : IConf G, |h (U l₀)| ≤ Ch := fun U => hhb _
  set m : ℝ := spec φ β Λ μ (fun U => h (U l₀)) ω with hm
  set E : ℝ := Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2))) with hE
  set V : ℝ := (∫ g, h g ^ 2 ∂μ) - (∫ g, h g ∂μ) ^ 2 with hV
  set J : ℝ := ∫ u, Real.exp (-β * actionOn φ (boundaryPlaqs Λ \ boundaryPlaqs {l₀})
    (splice Λ u ω)) ∂(vol μ Λ) with hJ
  have hZpos : 0 < part φ β Λ μ ω := part_pos hφ hφ0 hφ2 β Λ μ ω
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hhint : Integrable h μ := integrable_of_bounded _ hh hhb
  have hh2int : Integrable (fun g => h g ^ 2) μ :=
    integrable_of_bounded _ (hh.pow_const 2) (fun g => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (h g)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hhb g) 2)
  have hV0 : (0 : ℝ) ≤ V := MassGap.ActionSplit.variance_nonneg μ h hhint hh2int
  have hcent : V ≤ ∫ g, (h g - m) ^ 2 ∂μ :=
    MassGap.ActionSplit.variance_le_integral_centred μ h hhint hh2int m
  have hZJ : part φ β Λ μ ω ≤ J := part_le_integral_rest hφ hφ0 hφ2 hβ hl₀ μ ω
  have hJ0 : (0 : ℝ) ≤ J := le_trans hZpos.le hZJ
  have hnum := num_centred_ge hφ hφ0 hφ2 β hl₀ μ hh hhb m ω
  have hkey : E * V ≤ spec φ β Λ μ (fun U => (h (U l₀) - m) ^ 2) ω := by
    have hsp : spec φ β Λ μ (fun U => (h (U l₀) - m) ^ 2) ω
        = num φ β Λ μ (fun U => (h (U l₀) - m) ^ 2) ω / part φ β Λ μ ω := rfl
    rw [hsp, le_div_iff₀ hZpos]
    calc E * V * part φ β Λ μ ω
        ≤ E * V * J := mul_le_mul_of_nonneg_left hZJ (mul_nonneg hE0.le hV0)
      _ ≤ E * (∫ g, (h g - m) ^ 2 ∂μ) * J :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcent hE0.le) hJ0
      _ = E * ((∫ g, (h g - m) ^ 2 ∂μ) * J) := by ring
      _ ≤ num φ β Λ μ (fun U => (h (U l₀) - m) ^ 2) ω := hnum
  rw [MassGap.WilsonDLR.spec_variance_centred hφ hφ0 hφ2 β Λ μ hfm hfb ω] at hkey
  exact hkey

#print axioms spec_variance_floor

/-- **Part IV of the Clay statement, discharged.**

`VarianceBridge.clay_four_parts` takes `hvar` — an eventual variance floor for the finite-volume
Wilson states — and leaves the observable, the boundary condition and the constant to the caller.
`spec_variance_floor` supplies exactly that: read one link, and the floor holds at every region
containing it, with a constant that mentions no region. `Filter.eventually_ge_atTop` turns "contains
`l₀`" into "eventually along `atTop`".

**No comparison with the periodic torus appears anywhere in this.**
`VarianceBridge.clay_nontriviality_of_eventual_wilson_bridge` is the route that goes through
`wilsonCorrAt`, and it needs the torus-to-`ℤ⁴` transport; this one does not, because `cvar` is ours to
choose rather than forced to be a torus contact value. The universal form of that bridge is refuted
outright by `VarianceBridge.wilson_bridge_hypothesis_unsatisfiable`.

The only input left is `hpos`, positivity of the observable's variance under `μ` itself — a statement
about the gauge group with no lattice, no coupling and no volume in it.
`HaarVariance.haar_variance_reTr_pos` supplies it at `SU N` for `2 ≤ N`, and
`haar_variance_reTr_su_one` shows it FAILS at rank one, so some rank hypothesis is unavoidable.

DERIVED: `0` is the lower bound on `β` and on the density, and the strict lower bound on the
variance; `2` is the density's ceiling and the exponent of each square. -/
theorem exists_eventual_variance_floor [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [BorelSpace G] [SecondCountableTopology G]
    {φ : G → ℝ} (hφc : Continuous φ) (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (μ : Measure G) [IsProbabilityMeasure μ] (ω : IConf G)
    {h : G → ℝ} (hhc : Continuous h) {Ch : ℝ} (hhb : ∀ g, |h g| ≤ Ch)
    (hpos : 0 < (∫ g, h g ^ 2 ∂μ) - (∫ g, h g ∂μ) ^ 2) (l₀ : ILink) :
    ∃ (f₀ : C(IConf G, ℝ)) (cvar : ℝ), 0 < cvar ∧
      ∀ᶠ Λ : Finset ILink in Filter.atTop,
        cvar ≤ MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω Λ (f₀ * f₀)
          - (MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω Λ f₀) ^ 2 := by
  classical
  refine ⟨⟨fun U => h (U l₀), hhc.comp (continuous_apply l₀)⟩,
    Real.exp (-(|β| * (((boundaryPlaqs ({l₀} : Finset ILink)).card : ℝ) * 2)))
      * ((∫ g, h g ^ 2 ∂μ) - (∫ g, h g ∂μ) ^ 2),
    mul_pos (Real.exp_pos _) hpos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop ({l₀} : Finset ILink)] with Λ hΛ
  have hl₀ : l₀ ∈ Λ := hΛ (Finset.mem_singleton_self l₀)
  have h1 : MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω Λ
        (⟨fun U => h (U l₀), hhc.comp (continuous_apply l₀)⟩
          * ⟨fun U => h (U l₀), hhc.comp (continuous_apply l₀)⟩)
      = spec φ β Λ μ (fun U => h (U l₀) * h (U l₀)) ω := rfl
  have h2 : MassGap.WilsonDLR.specState hφc hφ0 hφ2 β μ ω Λ
        ⟨fun U => h (U l₀), hhc.comp (continuous_apply l₀)⟩
      = spec φ β Λ μ (fun U => h (U l₀)) ω := rfl
  rw [h1, h2]
  exact spec_variance_floor hφc.measurable hφ0 hφ2 hβ hl₀ μ hhc.measurable hhb ω

#print axioms exists_eventual_variance_floor

/-- **Part IV of the Clay statement, at `SU N`.**

`VarianceBridge.clay_four_parts`'s fourth input, produced rather than assumed. The observable is the
real trace at one link, `HaarVariance.haar_variance_reTr_pos` gives its variance under Haar strictly
positive at `2 ≤ N`, and `spec_variance_floor` carries that to every finite region containing the
link with a constant that mentions no region.

**The bridge to `ProbabilityTheory.variance`.** `variance_eq_integral` writes the variance as a
centred second moment and `ActionSplit.integral_centred_eq` expands that into the second-moment form
this module uses; the two differ by nothing.

⚠ `2 ≤ N` is load-bearing and not a convenience:
`HaarVariance.haar_variance_reTr_su_one` computes the variance as exactly `0` at rank one, where the
determinant condition makes the group trivial. No choice of observable repairs that, since every
function on a one-point space is constant.

⚠ And the constant is existential. `haar_variance_reTr_pos` produces no numerical lower bound — it
runs `Continuous.ae_eq_iff_eq` against an open-positive measure — so `cvar` here is positive and
unevaluated. That is all Part IV asks for; nothing downstream reads its value.

DERIVED: `0` is the excluded rank in `hN`, the lower bound on `β` and on the density, and the strict
lower bound on the variance; `2` is the rank bound in `hN2`, the density's ceiling and the exponent
of each square. -/
theorem wilson_eventual_variance_floor {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ω : IConf (MassGap.SUN.SU N)) (l₀ : ILink) :
    ∃ (f₀ : C(IConf (MassGap.SUN.SU N), ℝ)) (cvar : ℝ), 0 < cvar ∧
      ∀ᶠ Λ : Finset ILink in Filter.atTop,
        cvar ≤ MassGap.WilsonDLR.specState
            (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β
            (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) ω Λ (f₀ * f₀)
          - (MassGap.WilsonDLR.specState
            (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β
            (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) ω Λ f₀) ^ 2 := by
  classical
  obtain ⟨Ch, hCh⟩ := MassGap.ActionSplit.exists_bound_of_continuous
    (MassGap.HaarVariance.continuous_reTr (N := N))
  have hm : Measurable (MassGap.HaarVariance.reTr (N := N)) :=
    MassGap.HaarVariance.continuous_reTr.measurable
  have hint : Integrable (MassGap.HaarVariance.reTr (N := N))
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
    integrable_of_bounded _ hm hCh
  have hint2 : Integrable (fun g => MassGap.HaarVariance.reTr (N := N) g ^ 2)
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
    integrable_of_bounded _ (hm.pow_const 2) (fun g => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (MassGap.HaarVariance.reTr g)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hCh g) 2)
  have hbridge : (∫ g, MassGap.HaarVariance.reTr (N := N) g ^ 2
        ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))
      - (∫ g, MassGap.HaarVariance.reTr (N := N) g
        ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ^ 2
      = ProbabilityTheory.variance (MassGap.HaarVariance.reTr (N := N))
        (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) := by
    rw [ProbabilityTheory.variance_eq_integral hm.aemeasurable,
      MassGap.ActionSplit.integral_centred_eq _ _ hint hint2
        (∫ g, MassGap.HaarVariance.reTr (N := N) g
          ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))]
    ring
  exact exists_eventual_variance_floor
    (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) hβ _ ω
    MassGap.HaarVariance.continuous_reTr hCh
    (hbridge ▸ MassGap.HaarVariance.haar_variance_reTr_pos hN2) l₀

#print axioms wilson_eventual_variance_floor

end MassGap.SpecVarianceFloor
