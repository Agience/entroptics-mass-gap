import MassGap.LatticeGauge

/-!
# MassGap.CompactGauge — the canonical probability Haar on a compact gauge group (step A2a)

`LatticeGauge` (step A1) derives the invariance of lattice-gauge correlations for *any* gauge group
carrying a left-invariant probability measure. This file discharges that measure hypothesis: a
compact, Hausdorff (`T2`), Borel topological group carries a **canonical left-invariant probability
measure** — the Haar measure normalized on the whole (compact) group. So the correlation invariance
`Symmetry.expect_invariant` holds with the measure `μ` **derived**, not assumed.

The measure is `probHaar G := haarMeasure ⊤`, normalized to total mass one by `haarMeasure_self`
(the whole compact group has Haar-measure one) and left-invariant by `isMulLeftInvariant_haarMeasure`.

What remains for a fully concrete SU(N) realisation (step A2b) is purely the topological instances on
`Matrix.specialUnitaryGroup n ℂ` — `TopologicalSpace`/`IsTopologicalGroup`/`CompactSpace`/`BorelSpace`
— which Mathlib v4.31 does not yet provide; the measure-theoretic content is complete here.

Foundational footprint only (`#print axioms` at the end). Build: `lake build MassGap.CompactGauge`.
-/

namespace MassGap.CompactGauge

open MeasureTheory Measure TopologicalSpace
open MassGap.LatticeGauge

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]

/-- The canonical probability Haar measure on a compact gauge group: the Haar measure normalized so
that the whole (compact) group has measure one. -/
noncomputable def probHaar : Measure G := haarMeasure (default : PositiveCompacts G)

/-- `probHaar` is a probability measure: the whole compact group carries Haar-measure one
(`haarMeasure_self`, with `default = ⊤` whose carrier is `univ`). -/
instance isProbabilityMeasure_probHaar : IsProbabilityMeasure (probHaar G) := by
  refine ⟨?_⟩
  have h : ((default : PositiveCompacts G) : Set G) = Set.univ := PositiveCompacts.coe_top
  rw [probHaar, ← h]
  exact haarMeasure_self

/-- `probHaar` is left-invariant (inherited from `haarMeasure`). -/
instance isMulLeftInvariant_probHaar : IsMulLeftInvariant (probHaar G) :=
  isMulLeftInvariant_haarMeasure _

/-- `probHaar` is a Haar measure (inherited from `haarMeasure`). -/
instance isHaarMeasure_probHaar : IsHaarMeasure (probHaar G) := isHaarMeasure_haarMeasure _

/-- `probHaar` is regular (inherited from `haarMeasure`), hence inner regular. -/
instance regular_probHaar : (probHaar G).Regular := regular_haarMeasure

/-- **Compact-group unimodularity.** On a COMPACT group the probability Haar measure is also
RIGHT-invariant. The modular character `Δ` satisfies `map (·*g) μ = Δ(g) • μ`; taking total mass, the
left side is a probability (`μ (·*g)⁻¹univ = μ univ = 1`) and the right side has mass `Δ(g)·1`, so
`Δ(g) = 1` and the right-translate equals `μ`. (SU(N) is non-abelian, so this needs the mass argument,
not the commutative `IsMulLeftInvariant.isMulRightInvariant`.) -/
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

/-- Per-link conjugation of a configuration by a fixed group element `g`: `U ↦ (l ↦ g · U l · g⁻¹)` —
a constant (global) gauge transformation. -/
def confConj {ι : Type} (g : G) (U : ι → G) : ι → G := fun l => g * U l * g⁻¹

/-- **A constant gauge transformation preserves the product Haar measure.** Per link the map is
`u ↦ g·u·g⁻¹ = (g·_) ∘ (_·g⁻¹)`, measure-preserving by LEFT- and RIGHT-invariance (the unimodularity
just established); the product measure is preserved coordinatewise. So the lattice-gauge measure is
invariant under a global gauge transformation. -/
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

/-- The constant gauge transformation as a MEASURABLE EQUIVALENCE (inverse: conjugation by `g⁻¹`). -/
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

/-- `confConjEquiv` preserves the product Haar measure (same map as `confConj`). -/
theorem confConjEquiv_measurePreserving {ι : Type} [Fintype ι] (g : G) :
    MeasurePreserving (confConjEquiv G g) (Measure.pi fun _ : ι => probHaar G)
      (Measure.pi fun _ : ι => probHaar G) :=
  confConj_measurePreserving G g

/-- **Correlation invariance over the canonical Haar measure** — the A1 payoff instantiated at
`μ := probHaar G`, with the measure now derived from compactness rather than assumed:
`⟨O ∘ reindex⟩ = ⟨O⟩` for the Gibbs expectation against normalized Haar. This is the derived form of
the Osterwalder–Schrader invariances `os_euc`/`os_perm` on a genuine compact gauge measure. -/
theorem expect_invariant_haar {sys : System G} (sym : Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (probHaar G) β (fun U => O (Symmetry.reindex sym.onLink U))
      = sys.expect (probHaar G) β O :=
  Symmetry.expect_invariant sys (probHaar G) sym β O

#print axioms expect_invariant_haar

end MassGap.CompactGauge
