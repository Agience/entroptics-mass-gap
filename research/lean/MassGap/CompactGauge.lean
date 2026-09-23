import MassGap.LatticeGauge

/-!
# MassGap.CompactGauge — the probability Haar measure on a compact group (step A2a)

Fixes a canonical measure on a compact gauge group and derives what lattice-gauge correlations need
from it.

`probHaar G` is `haarMeasure (default : PositiveCompacts G)`; on a compact group the default positive
compact is the whole group, so `haarMeasure_self` makes it a probability measure. Instances record
that it is left-invariant, a Haar measure and regular, all inherited from `haarMeasure`, and that it
is right-invariant — the latter argued from the modular character, since `G` is not assumed abelian.

`confConj G g` is per-link conjugation `U ↦ (l ↦ g * U l * g⁻¹)` of a configuration `ι → G`.
`confConj_measurePreserving` shows it preserves the product measure `Measure.pi (fun _ : ι => probHaar G)`
for `ι` a `Fintype`, and `confConjEquiv` packages it as a `MeasurableEquiv` with inverse conjugation
by `g⁻¹`. `expect_invariant_haar` instantiates `LatticeGauge.Symmetry.expect_invariant` at
`μ := probHaar G`.

Scope: `G` is a group carrying `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`, `Nonempty`,
`MeasurableSpace` and `BorelSpace` instances. Nothing here instantiates those at
`Matrix.specialUnitaryGroup n ℂ`; the results are stated for the abstract `G` only. The index type
`ι` is finite for the measure-preserving results.
-/

namespace MassGap.CompactGauge

open MeasureTheory Measure TopologicalSpace
open MassGap.LatticeGauge

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure of `G` at the default `PositiveCompacts G`. On a compact group that default is
the whole group, so this is the Haar measure normalised to total mass one.

DERIVED: no numeral appears in the statement. -/
noncomputable def probHaar : Measure G := haarMeasure (default : PositiveCompacts G)

/-- `probHaar G` is a probability measure. The proof rewrites the default positive compact to
`Set.univ` via `PositiveCompacts.coe_top` and applies `haarMeasure_self`, which gives the chosen
positive compact measure one.

DERIVED: no numeral appears in the statement; the total mass one is inside `IsProbabilityMeasure`. -/
instance isProbabilityMeasure_probHaar : IsProbabilityMeasure (probHaar G) := by
  refine ⟨?_⟩
  have h : ((default : PositiveCompacts G) : Set G) = Set.univ := PositiveCompacts.coe_top
  rw [probHaar, ← h]
  exact haarMeasure_self

/-- `probHaar G` is left-invariant, inherited from `isMulLeftInvariant_haarMeasure`.

DERIVED: no numeral appears in the statement. -/
instance isMulLeftInvariant_probHaar : IsMulLeftInvariant (probHaar G) :=
  isMulLeftInvariant_haarMeasure _

/-- `probHaar G` is a Haar measure, inherited from `isHaarMeasure_haarMeasure`.

DERIVED: no numeral appears in the statement. -/
instance isHaarMeasure_probHaar : IsHaarMeasure (probHaar G) := isHaarMeasure_haarMeasure _

/-- `probHaar G` is regular, inherited from `regular_haarMeasure`. Inner regularity follows from
`Regular` and is not separately stated.

DERIVED: no numeral appears in the statement. -/
instance regular_probHaar : (probHaar G).Regular := regular_haarMeasure

/-- `probHaar G` is right-invariant: the compact group `G` is unimodular. The proof evaluates
`map_right_mul_eq_modularCharacterFun_smul` on `Set.univ`; both sides then have total mass
`modularCharacterFun g` times one, and since `probHaar G` is a probability measure this forces
`modularCharacterFun g = 1`, so the right translate equals the measure.

Scope: `G` is not assumed commutative, so this goes through the modular character rather than
`IsMulLeftInvariant.isMulRightInvariant`. Compactness is what makes the total mass finite and equal
on both sides.

DERIVED: no numeral appears in the statement. -/
instance isMulRightInvariant_probHaar : IsMulRightInvariant (probHaar G) := by
  refine ⟨fun g => ?_⟩
  have hmap := map_right_mul_eq_modularCharacterFun_smul (probHaar G) g
  have hone : modularCharacterFun g = 1 := by
    have h1 : (Measure.map (· * g) (probHaar G)) Set.univ = (modularCharacterFun g : ENNReal) := by
      rw [hmap, Measure.smul_apply, measure_univ, ENNReal.smul_one]
    rw [Measure.map_apply (continuous_mul_const g).measurable MeasurableSet.univ, Set.preimage_univ,
      measure_univ] at h1
    exact_mod_cast h1.symm
  rw [hmap, hone, one_smul]

/-- Per-link conjugation of a configuration `U : ι → G` by a fixed `g : G`:
`confConj G g U l = g * U l * g⁻¹`. The same `g` is used at every index, so this is a constant
(global) gauge transformation, not a site-dependent one. `ι` is an arbitrary type here.

DERIVED: no numeral appears in the statement. -/
def confConj {ι : Type} (g : G) (U : ι → G) : ι → G := fun l => g * U l * g⁻¹

/-- For a finite index type `ι` and any `g : G`, `confConj G g` is measure-preserving from
`Measure.pi (fun _ : ι => probHaar G)` to itself. Per coordinate the map factors as
`(g * ·) ∘ (· * g⁻¹)`, measure-preserving by left-invariance and by the right-invariance established
above; `Measure.pi_map_pi` lifts this to the product.

Scope: `ι` must be a `Fintype` for the product measure to be handled this way; the transformation is
global (one `g` for all links).

DERIVED: no numeral appears in the statement. -/
theorem confConj_measurePreserving {ι : Type} [Fintype ι] (g : G) :
    MeasurePreserving (confConj G g) (Measure.pi fun _ : ι => probHaar G)
      (Measure.pi fun _ : ι => probHaar G) := by
  have hconj : MeasurePreserving (fun u => g * u * g⁻¹) (probHaar G) (probHaar G) := by
    have h := (measurePreserving_mul_left (probHaar G) g).comp
      (measurePreserving_mul_right (probHaar G) g⁻¹)
    convert h using 1
    funext u; simp [Function.comp, mul_assoc]
  haveI hsf : ∀ _ : ι, SigmaFinite ((probHaar G).map (fun u => g * u * g⁻¹)) :=
    fun _ => by rw [hconj.map_eq]; infer_instance
  refine ⟨measurable_pi_lambda _ (fun l => hconj.measurable.comp (measurable_pi_apply l)), ?_⟩
  rw [show confConj G g = (fun (U : ι → G) (l : ι) => (fun u => g * u * g⁻¹) (U l)) from rfl,
      Measure.pi_map_pi (fun _ => hconj.aemeasurable)]
  simp only [hconj.map_eq]

/-- `confConj G g` packaged as a measurable equivalence `(ι → G) ≃ᵐ (ι → G)`, with inverse
`confConj G g⁻¹`. The two inverse laws are `group`-normalisation of `g⁻¹ * (g * U l * g⁻¹) * g⁻¹⁻¹`
and its mirror; measurability in both directions comes from continuity of conjugation.

DERIVED: no numeral appears in the statement. -/
noncomputable def confConjEquiv {ι : Type} (g : G) : (ι → G) ≃ᵐ (ι → G) where
  toFun := confConj G g
  invFun := confConj G g⁻¹
  left_inv := fun U => by funext l; simp only [confConj]; group
  right_inv := fun U => by funext l; simp only [confConj]; group
  measurable_toFun := by
    have hcont : Continuous (fun u : G => g * u * g⁻¹) :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact measurable_pi_lambda _ (fun l => hcont.measurable.comp (measurable_pi_apply l))
  measurable_invFun := by
    have hcont : Continuous (fun u : G => g⁻¹ * u * g⁻¹⁻¹) :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact measurable_pi_lambda _ (fun l => hcont.measurable.comp (measurable_pi_apply l))

/-- `confConjEquiv G g` is measure-preserving for the product measure, for a finite `ι`. Its
underlying function is definitionally `confConj G g`, so the proof is `confConj_measurePreserving`
directly.

DERIVED: no numeral appears in the statement. -/
theorem confConjEquiv_measurePreserving {ι : Type} [Fintype ι] (g : G) :
    MeasurePreserving (confConjEquiv G g) (Measure.pi fun _ : ι => probHaar G)
      (Measure.pi fun _ : ι => probHaar G) :=
  confConj_measurePreserving G g

/-- `LatticeGauge.Symmetry.expect_invariant` instantiated at `μ := probHaar G`: for a `System G`,
a `Symmetry sys`, an inverse temperature `β` and an observable `O : sys.Config → ℝ`, the expectation
of `O ∘ Symmetry.reindex sym.onLink` equals the expectation of `O`.

The measure is supplied by `probHaar`, so no left-invariant probability measure is assumed at this
call site. Scope: the symmetry is the reindexing carried by `sym.onLink`; `β` is an arbitrary real,
not required positive.

DERIVED: no numeral appears in the statement. -/
theorem expect_invariant_haar {sys : System G} (sym : Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (probHaar G) β (fun U => O (Symmetry.reindex sym.onLink U))
      = sys.expect (probHaar G) β O :=
  Symmetry.expect_invariant sys (probHaar G) sym β O

#print axioms expect_invariant_haar

end MassGap.CompactGauge
