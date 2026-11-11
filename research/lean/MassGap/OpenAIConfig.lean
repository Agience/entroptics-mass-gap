import Mathlib
import MassGap.OpenAIDictionary

/-!
# MassGap.OpenAIConfig — the OpenAI lattice configuration type and ours

The OpenAI submission `yang-mills-group/OpenAI-YM-20261028` (commit `3456e5e`) is built on Lean 4.32
and cannot be imported here (Lean 4.31). This module restates, exactly, the definitions of its
four-dimensional periodic Wilson lattice — `GaugeGroup` (`PublicTheory.lean:20–33`), `Axis`
(`PublicTheory.lean:51`), `Site`, `Configuration`, `Directions` (`PublicWilson.lean:11–13`), the Borel
structure on the group (`PublicWilson.lean:15–18`), `plaquette` (`PublicWilson.lean:20`),
`wilsonEnergy` (`PublicWilson.lean:25`) and `wilsonLaw` (`PublicWilson.lean:29`) — and proves the
correspondence with the configuration type `Link 4 l → G` of `MassGap.OpenAIDictionary`. The model is
the group's own bridge, `YM/submissions/openai-20261028/checks/LGTWilsonBridge.lean` (`configEquiv`,
`plaquette_eq`, `action_eq`, `law_preserving`).

## The dictionary

* `instGaugeGroupImage`: the image subgroup `g.image ≤ U(n+1)` of their gauge group is a
  `MassGap.GaugeGroup` whose representation is the inclusion, so `dim = n + 1`. `wilsonDensityG_image`:
  our density there is their summand `1 − Re tr u / (n+1)`.
* `siteEquiv`: `Fin l ≃+* ZMod l` coordinatewise (`ZMod.finEquiv`, `l ≥ 1` because `l : ℕ+`);
  `siteEquiv_shift`: our periodic step `shift a x` goes to their `x + Pi.single a 1`.
* `linkEquiv`: our link `(a, x)` is their `(x, a)`; `configEquiv`: the measurable equivalence of
  configuration types it induces, `configEquiv_apply` its value.
* `plaquette_eq`: their `plaquette` at `(x, a, b)` is our holonomy `wilsonHol bd ((a, b), x)`.
* `wilsonEnergy_configEquiv`: their `wilsonEnergy ∘ configEquiv` is `OpenAIDictionary.wilsonEnergy`.
* `measurePreserving_wilsonLaw`, `map_wilsonLaw`: their law at `β` is the pushforward of
  `OpenAIDictionary.wilsonLaw β` under `configEquiv`, for every σ-finite single-link measure, in
  particular their probability Haar measure.
* `expect_eq_integral_openAILaw`: our Gibbs expectation at `β` of `O ∘ configEquiv` is the integral of
  `O` against their law at `2β` on their configuration type (with
  `OpenAIDictionary.expect_eq_integral_wilsonLaw`); `integrable_iff` transports integrability.
* `wilsonDensityG_SU_eq`, `wilsonDensityG_image_eq_SU`: at `SU(N)` in the defining representation our
  density is `1 − Re tr / N`, their normalization with `D = n + 1 = N`.
* `familyGap_on_openAI_laws`: when their image is `SU(n+1)` as a set (`ImageIsSU`), their law at `β` on
  the side `2^k · n` torus is the pushforward of our `SU(n+1)` law at `β/2`, whose transfer operator has
  the gap of `OpenAIDictionary.familyGap_of_seed`.
* `map_imageEquivSU_eq_probHaar`: their single-link measure (`WilsonFamily.haar`, a probability Haar
  measure, `PublicWilson.lean:41–43`) corresponds to our `probHaar (SU(n+1))`, by uniqueness of Haar
  measure; `familyGap_on_openAI_laws'` is the gap statement with that hypothesis discharged.
* `suGauge`: `SU(n+1)` as one of their `GaugeGroup` values, with Lie algebra `𝔰𝔲(n+1)` and their
  `generates` field proved (`generates_su`, through `det exp X = exp tr X` for anti-Hermitian `X`,
  `det_exp_of_skew`); `eq_suGauge`: every value of theirs with that image is `suGauge`, their `su2`
  among them. `familyGap_on_openAI_SU`: the gap statement at `suGauge r` under the seed alone.

## Scope

These are identities on one finite periodic lattice of side `l` at one coupling, and the gap of the
transfer operator on the tori `2^k · n`. Nothing here identifies their limit theory with ours or
discharges the seed hypothesis of `familyGap_of_seed`.
-/

namespace MassGap.OpenAIConfig

open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius Matrix
open MassGap.WilsonLattice

/-! ## 1. Their definitions, restated -/

/-- The fixed faithful unitary representation of their gauge groups, `U(n+1)`. Restated from the
OpenAI submission, `PublicTheory.lean:20` (`UnitaryRepresentation n := Matrix.unitaryGroup
(Fin (n + 1)) ℂ`).

DERIVED: `1` is the shift making the matrix size `n + 1` at least one. -/
abbrev UnitaryRepresentation (n : ℕ) := Matrix.unitaryGroup (Fin (n + 1)) ℂ

/-- Their compact matrix gauge group: a closed subgroup `image` of `U(n+1)` with its one-parameter Lie
algebra. Restated from `PublicTheory.lean:25–33` field for field.

DERIVED: `1` is the shift making the matrix size `n + 1` at least one. -/
structure GaugeGroup where
  n : ℕ
  image : Subgroup (UnitaryRepresentation n)
  imageClosed : IsClosed (image : Set (UnitaryRepresentation n))
  lieAlgebra : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  generates : ∀ X,
    X ∈ lieAlgebra ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Set.range (fun u : image ↦ (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

/-- Their spacetime axes, `Fin 4`. Restated from `PublicTheory.lean:51` (`Axis := Fin 4`).

DERIVED: `4` is the spacetime dimension. -/
abbrev Axis := Fin 4

/-- Their lattice sites of side `l`: `Axis → ZMod l`. Restated from `PublicWilson.lean:11`
(`Site (l : ℕ+) := Axis → ZMod l.val`).

DERIVED: no numeral appears in the statement. -/
abbrev Site (l : ℕ+) := Axis → ZMod l.val

/-- Their configurations: a group element of `g.image` on each pair (site, axis). Restated from
`PublicWilson.lean:12` (`Configuration g l := (Site l × Axis) → g.image`).

DERIVED: no numeral appears in the statement. -/
abbrev Configuration (g : GaugeGroup) (l : ℕ+) := (Site l × Axis) → g.image

/-- Their unordered planes, pairs of axes `p.1 < p.2`. Restated from `PublicWilson.lean:13`
(`Directions := {p : Axis × Axis // p.1 < p.2}`); it is `OpenAIDictionary.Directions 4`.

DERIVED: no numeral appears in the statement. -/
abbrev Directions := {p : Axis × Axis // p.1 < p.2}

namespace GaugeGroup

/-- The Borel σ-algebra on `g.image`. Restated from `PublicWilson.lean:16`.

DERIVED: no numeral appears in the statement. -/
noncomputable instance (g : GaugeGroup) : MeasurableSpace g.image := borel _

/-- `g.image` is a Borel space. Restated from `PublicWilson.lean:17`.

DERIVED: no numeral appears in the statement. -/
instance (g : GaugeGroup) : BorelSpace g.image := ⟨rfl⟩

end GaugeGroup

/-- Their plaquette at site `x` in the plane `(i, j)`:
`U(x, i) · U(x + î, j) · U(x + ĵ, i)⁻¹ · U(x, j)⁻¹`, with `î = Pi.single i 1`. Restated from
`PublicWilson.lean:20–23`.

DERIVED: `1` is the unit step in `ZMod l` along an axis. -/
def plaquette {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (x : Site l)
    (i j : Axis) : g.image :=
  U (x,i) * (U (x + Pi.single i 1,j) *
    ((U (x + Pi.single j 1,i))⁻¹ * (U (x,j))⁻¹))

/-- Their Wilson energy, `∑_{x, i<j} (1 − Re tr U_p / (n+1))`. Restated from `PublicWilson.lean:25–27`.

DERIVED: the leading `1` normalizes the identity holonomy to cost nothing; `1` in `n + 1` is the
matrix-size shift of `UnitaryRepresentation`. -/
noncomputable def wilsonEnergy {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) : ℝ :=
  ∑ p : Site l × Directions,
    (1 - ((plaquette U p.1 p.2.val.1 p.2.val.2).val.val.trace).re / ((g.n+1 : ℕ) : ℝ))

/-- Their Wilson law at coupling `β` with single-link measure `haar`: the product measure with
density `exp(−β E) / ∫ exp(−β E)`. Restated from `PublicWilson.lean:29–33`.

DERIVED: no numeral appears in the statement. -/
noncomputable def wilsonLaw (g : GaugeGroup) (l : ℕ+) (β : ℝ) (haar : Measure g.image) :
    Measure (Configuration g l) :=
  let prior : Measure (Configuration g l) := Measure.pi fun _ => haar
  let density := fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)
  prior.withDensity fun U => ENNReal.ofReal (density U / ∫ V, density V ∂prior)

/-- Their law with the two `let`s of `PublicWilson.lean:30–31` inlined.

DERIVED: no numeral appears in the statement. -/
theorem wilsonLaw_eq (g : GaugeGroup) (l : ℕ+) (β : ℝ) (haar : Measure g.image) :
    wilsonLaw g l β haar
      = (Measure.pi fun _ : Site l × Axis => haar).withDensity fun U =>
          ENNReal.ofReal (Real.exp (-β * wilsonEnergy U) /
            ∫ V, Real.exp (-β * wilsonEnergy V) ∂(Measure.pi fun _ : Site l × Axis => haar)) :=
  rfl

/-! ## 2. Their group is one of ours -/

/-- The image subgroup of their gauge group is a `MassGap.GaugeGroup` with the inclusion
`g.image ≤ U(n+1)` as its representation, so `dim = n + 1`. Compact as a closed subgroup of the
compact `U(n+1)` (`GaugeGroup.compactSpace_unitaryGroup`), second countable as a subspace of matrices,
Borel by their instance; the inclusion is continuous and injective. The same construction as
`GaugeInstances.instGaugeGroupUSp`.

DERIVED: `1` is the matrix-size shift of `UnitaryRepresentation`. -/
noncomputable instance instGaugeGroupImage (g : GaugeGroup) : MassGap.GaugeGroup g.image where
  isTopologicalGroup := inferInstance
  compactSpace := isCompact_iff_compactSpace.mp g.imageClosed.isCompact
  borelSpace := inferInstance
  secondCountable := Topology.IsInducing.subtypeVal.secondCountableTopology
  nonempty := ⟨1⟩
  repDim := g.n + 1
  repDim_pos := Nat.succ_pos _
  rep := g.image.subtype
  continuous_rep := continuous_subtype_val.comp continuous_subtype_val
  rep_injective := Subgroup.subtype_injective _

/-- **The trace normalization on their group**: our Wilson density on `g.image` is their summand,
`wilsonDensityG g.image u = 1 − Re tr u / (n+1)`, their `D = n + 1` being our `dim` of the inclusion.

DERIVED: the leading `1` normalizes the identity holonomy; `1` in `n + 1` is the matrix-size shift. -/
theorem wilsonDensityG_image (g : GaugeGroup) (u : g.image) :
    MassGap.GaugeGroup.wilsonDensityG g.image u
      = 1 - (u.val.val.trace).re / ((g.n+1 : ℕ) : ℝ) := by
  show 1 - (1 / ((g.n + 1 : ℕ) : ℝ)) * (Matrix.trace u.val.val).re = _
  ring

/-! ## 3. The index correspondence -/

variable (l : ℕ+)

/-- Our sites of side `l` are theirs: `Fin l ≃+* ZMod l` (`ZMod.finEquiv`, `l ≥ 1` since `l : ℕ+`)
in each coordinate.

DERIVED: `4` is the spacetime dimension. -/
def siteEquiv : WilsonHypercubic.Site 4 l ≃ Site l where
  toFun x i := ZMod.finEquiv l (x i)
  invFun y i := (ZMod.finEquiv l).symm (y i)
  left_inv x := funext fun i => by simp
  right_inv y := funext fun i => by simp

/-- `siteEquiv` in coordinates.

DERIVED: `4` is the spacetime dimension. -/
theorem siteEquiv_apply (x : WilsonHypercubic.Site 4 l) (i : Axis) :
    siteEquiv l x i = ZMod.finEquiv l (x i) := rfl

/-- **The shifts agree**: our periodic step `WilsonHypercubic.shift a x = update x a (x a + 1)` is
their `x + Pi.single a 1`, because `ZMod.finEquiv` is additive and sends `1` to `1`. The model is
`LGTWilsonBridge.lean:39` (`shift_eq`).

DERIVED: `4` is the spacetime dimension; `1` the unit step along an axis. -/
theorem siteEquiv_shift (a : Fin 4) (x : WilsonHypercubic.Site 4 l) :
    siteEquiv l (WilsonHypercubic.shift a x) = siteEquiv l x + Pi.single a 1 := by
  funext j
  by_cases h : j = a
  · subst h
    simp [siteEquiv_apply, WilsonHypercubic.shift, map_add, map_one]
  · simp [siteEquiv_apply, WilsonHypercubic.shift, Function.update_of_ne h, Pi.single_eq_of_ne h]

/-- Our link `(a, x)` (direction, site) is their pair `(x, a)` (site, axis). The model is
`LGTWilsonBridge.lean:12` (`linkEquiv`).

DERIVED: `4` is the spacetime dimension. -/
def linkEquiv : WilsonHypercubic.Link 4 l ≃ Site l × Axis where
  toFun e := (siteEquiv l e.2, e.1)
  invFun e := (e.2, (siteEquiv l).symm e.1)
  left_inv e := by simp
  right_inv e := by simp

/-- **The configuration correspondence**: the measurable equivalence between our configurations
`Link 4 l → H` and their `(Site l × Axis) → H`, induced by `linkEquiv`; at `H = g.image` the target is
`Configuration g l`. A reindexing of the same link variables, with no gauge fixing. The model is
`LGTWilsonBridge.lean:36` (`configEquiv`).

DERIVED: `4` is the spacetime dimension. -/
noncomputable def configEquiv {H : Type*} [MeasurableSpace H] :
    (WilsonHypercubic.Link 4 l → H) ≃ᵐ (Site l × Axis → H) :=
  MeasurableEquiv.piCongrLeft (fun _ => H) (linkEquiv l)

/-- `configEquiv U` at their pair `(siteEquiv x, a)` is `U` at our link `(a, x)`.

DERIVED: `4` is the spacetime dimension. -/
theorem configEquiv_apply {H : Type*} [MeasurableSpace H] (U : WilsonHypercubic.Link 4 l → H)
    (a : Fin 4) (x : WilsonHypercubic.Site 4 l) :
    configEquiv l U (siteEquiv l x, a) = U (a, x) :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => H) (linkEquiv l) U (a, x)

/-! ## 4. Plaquette, energy, law -/

/-- **The plaquette identity**: their plaquette of `configEquiv U` at `(siteEquiv x, a, b)` is our
holonomy of `U` around the ordered plaquette `((a, b), x)`, `wilsonHol bd ((a, b), x) U`. Both words
are `U_a(x) U_b(x+â) U_a(x+b̂)⁻¹ U_b(x)⁻¹`; the shifts agree by `siteEquiv_shift`. The model is
`LGTWilsonBridge.lean:46` (`plaquette_eq`).

DERIVED: `4` is the spacetime dimension. -/
theorem plaquette_eq {g : GaugeGroup} (U : WilsonHypercubic.Link 4 l → g.image) (a b : Fin 4)
    (x : WilsonHypercubic.Site 4 l) :
    plaquette (configEquiv l U) (siteEquiv l x) a b
      = wilsonHol (WilsonHypercubic.bd (d := 4) (n := l)) ((a, b), x) U := by
  unfold plaquette
  rw [← siteEquiv_shift, ← siteEquiv_shift]
  simp only [configEquiv_apply]
  simp [wilsonHol, WilsonHypercubic.bd]

/-- **The energy identity**: their Wilson energy of `configEquiv U` is the energy
`OpenAIDictionary.wilsonEnergy U` of section 1 of that module, at `G = g.image` with the inclusion
representation. The site sum is reindexed by `siteEquiv`, each term is `plaquette_eq`, and the
normalization is `wilsonDensityG_image`.

DERIVED: `4` is the spacetime dimension. -/
theorem wilsonEnergy_configEquiv (g : GaugeGroup) (U : WilsonHypercubic.Link 4 l → g.image) :
    wilsonEnergy (configEquiv l U) = OpenAIDictionary.wilsonEnergy (d := 4) (n := l) U := by
  unfold wilsonEnergy OpenAIDictionary.wilsonEnergy
  symm
  refine Fintype.sum_equiv ((siteEquiv l).prodCongr (Equiv.refl _)) _ _ (fun p => ?_)
  obtain ⟨x, ⟨⟨a, b⟩, hab⟩⟩ := p
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id]
  rw [plaquette_eq, wilsonDensityG_image]

/-- The product measures correspond: `configEquiv` carries `μ^{⊗ links}` on our configurations to
`μ^{⊗ links}` on theirs (`measurePreserving_piCongrLeft`). The model is `LGTWilsonBridge.lean:88`
(`prior_preserving`).

DERIVED: `4` is the spacetime dimension. -/
theorem measurePreserving_pi {H : Type*} [MeasurableSpace H] (μ : Measure H) [SigmaFinite μ] :
    MeasurePreserving (configEquiv l (H := H)) (Measure.pi fun _ : WilsonHypercubic.Link 4 l => μ)
      (Measure.pi fun _ : Site l × Axis => μ) :=
  measurePreserving_piCongrLeft (fun _ => μ) (linkEquiv l)

/-- **The law identity**: `configEquiv` carries `OpenAIDictionary.wilsonLaw β μ` on our
configurations to their `wilsonLaw g l β μ`, for every coupling `β` and every σ-finite single-link
measure `μ` — in particular their probability Haar measure. The product measures correspond by
`measurePreserving_pi`, the energies by `wilsonEnergy_configEquiv`, hence the normalizers by
`MeasurePreserving.integral_comp'` and the densities on every measurable set by
`MeasurePreserving.setLIntegral_comp_preimage_emb`. The model is `LGTWilsonBridge.lean:107`
(`law_preserving`).

DERIVED: `4` is the spacetime dimension. -/
theorem measurePreserving_wilsonLaw (g : GaugeGroup) (β : ℝ) (μ : Measure g.image)
    [SigmaFinite μ] :
    MeasurePreserving (configEquiv l)
      (OpenAIDictionary.wilsonLaw (d := 4) (n := l) β μ) (wilsonLaw g l β μ) := by
  have hpi := measurePreserving_pi l μ
  have hE : ∀ U, wilsonEnergy (configEquiv l U) = OpenAIDictionary.wilsonEnergy (d := 4) (n := l) U :=
    wilsonEnergy_configEquiv l g
  have hZ : ∫ V, Real.exp (-β * wilsonEnergy V) ∂(Measure.pi fun _ : Site l × Axis => μ)
      = ∫ V, Real.exp (-β * OpenAIDictionary.wilsonEnergy (d := 4) (n := l) V)
          ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 l => μ) := by
    have h := hpi.integral_comp' (fun V => Real.exp (-β * wilsonEnergy V))
    simp only [hE] at h
    exact h.symm
  refine ⟨(configEquiv l).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (configEquiv l).measurable hs, OpenAIDictionary.wilsonLaw,
    withDensity_apply _ ((configEquiv l).measurable hs), wilsonLaw_eq, withDensity_apply _ hs]
  have h := hpi.setLIntegral_comp_preimage_emb (configEquiv l).measurableEmbedding
    (fun V => ENNReal.ofReal (Real.exp (-β * wilsonEnergy V) /
      ∫ V, Real.exp (-β * wilsonEnergy V) ∂(Measure.pi fun _ : Site l × Axis => μ))) s
  rw [← h]
  simp only [hE, hZ]

/-- **The pushforward form of the law identity**: their law at `β` is the pushforward of
`OpenAIDictionary.wilsonLaw β μ` under `configEquiv`.

DERIVED: `4` is the spacetime dimension. -/
theorem map_wilsonLaw (g : GaugeGroup) (β : ℝ) (μ : Measure g.image) [SigmaFinite μ] :
    (OpenAIDictionary.wilsonLaw (d := 4) (n := l) β μ).map (configEquiv l) = wilsonLaw g l β μ :=
  (measurePreserving_wilsonLaw l g β μ).map_eq

/-- **Integrability is transported**: `O ∘ configEquiv` is integrable against
`OpenAIDictionary.wilsonLaw β μ` iff `O` is integrable against their law at `β`. The model is
`LGTWilsonBridge.lean:124` (`integrable_iff`).

DERIVED: `4` is the spacetime dimension. -/
theorem integrable_iff (g : GaugeGroup) (β : ℝ) (μ : Measure g.image) [SigmaFinite μ]
    (O : Configuration g l → ℝ) :
    Integrable (fun U => O (configEquiv l U)) (OpenAIDictionary.wilsonLaw (d := 4) (n := l) β μ)
      ↔ Integrable O (wilsonLaw g l β μ) :=
  (measurePreserving_wilsonLaw l g β μ).integrable_comp_emb (configEquiv l).measurableEmbedding

/-- **Our expectations on their law, on their configuration type**: for every real observable `O` on
their configurations, our Gibbs expectation at coupling `β` of `O ∘ configEquiv`, against product
`μ`, is the integral of `O` against their law at `2β`:
`(sysWilsonG g.image 4 l).expect μ β (O ∘ configEquiv) = ∫ O ∂(wilsonLaw g l (2β) μ)`.
This is `OpenAIDictionary.expect_eq_integral_wilsonLaw` composed with `measurePreserving_wilsonLaw`.
At `μ` their probability Haar measure the right side is the law of `PublicWilson.lean:57`
(`finiteMoment`). No integrability of `O` is used.

DERIVED: `4` is the spacetime dimension; `2` is the factor of
`OpenAIDictionary.action_eq_two_mul_wilsonEnergy` (two orientations of one plane). -/
theorem expect_eq_integral_openAILaw (g : GaugeGroup) (β : ℝ) (μ : Measure g.image)
    [SigmaFinite μ] (O : Configuration g l → ℝ) :
    (GaugeWilson.sysWilsonG g.image 4 l).expect μ β (fun U => O (configEquiv l U))
      = ∫ V, O V ∂(wilsonLaw g l (2 * β) μ) := by
  rw [OpenAIDictionary.expect_eq_integral_wilsonLaw]
  exact (measurePreserving_wilsonLaw l g (2 * β) μ).integral_comp' O

/-! ## 5. The trace normalization at `SU(N)` -/

/-- **Their normalization is our density at `SU(N)`**: in the defining representation
(`GaugeInstances.instGaugeGroupSU`, `dim = N`) our density on `SU(n+1)` is
`1 − Re tr h / (n+1)`, their summand with `D = n + 1 = N`.

DERIVED: the leading `1` normalizes the identity holonomy; `1` in `n + 1` is their matrix-size
shift. -/
theorem wilsonDensityG_SU_eq (n : ℕ) (h : MassGap.SUN.SU (n + 1)) :
    MassGap.GaugeGroup.wilsonDensityG (MassGap.SUN.SU (n + 1)) h
      = 1 - (Matrix.trace (h : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re / ((n + 1 : ℕ) : ℝ) := by
  show 1 - (1 / ((n + 1 : ℕ) : ℝ)) * (Matrix.trace (h : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re = _
  ring

/-- **Their group and `SU(N)` carry one density on shared matrices**: if `u ∈ g.image` and
`h ∈ SU(n+1)` are the same matrix, our density of `u` on their group (`instGaugeGroupImage`) equals
our density of `h` on `SU(n+1)` (`instGaugeGroupSU`). So when `g.image` is `SU(n+1)`, the energies of
`wilsonEnergy_configEquiv` are the `SU(N)` Wilson energies of `OpenAIDictionary`.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
theorem wilsonDensityG_image_eq_SU (g : GaugeGroup) (u : g.image) (h : MassGap.SUN.SU (g.n + 1))
    (huh : u.val.val = (h : Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ)) :
    MassGap.GaugeGroup.wilsonDensityG g.image u
      = MassGap.GaugeGroup.wilsonDensityG (MassGap.SUN.SU (g.n + 1)) h := by
  rw [wilsonDensityG_image, wilsonDensityG_SU_eq, huh]


/-! ## 6. Theorem 4.46 on their laws -/

/-- **Gibbs laws are carried by an energy-matching map**: if a measurable equivalence `T` carries the
prior `P` to `Q` and `E_Y ∘ T = E_X`, then `T` carries the normalized law `P` with density
`exp(−β E_X)/∫ exp(−β E_X)` to `Q` with density `exp(−β E_Y)/∫ exp(−β E_Y)`. The normalizers agree by
`MeasurePreserving.integral_comp'`, the densities on every measurable set by
`MeasurePreserving.setLIntegral_comp_preimage_emb`.

DERIVED: no numeral appears in the statement. -/
theorem measurePreserving_gibbs {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (T : X ≃ᵐ Y)
    {P : Measure X} {Q : Measure Y} (hT : MeasurePreserving T P Q) (EX : X → ℝ) (EY : Y → ℝ)
    (hE : ∀ x, EY (T x) = EX x) (β : ℝ) :
    MeasurePreserving T
      (P.withDensity fun x => ENNReal.ofReal (Real.exp (-β * EX x) / ∫ x', Real.exp (-β * EX x') ∂P))
      (Q.withDensity fun y =>
        ENNReal.ofReal (Real.exp (-β * EY y) / ∫ y', Real.exp (-β * EY y') ∂Q)) := by
  have hZ : ∫ y, Real.exp (-β * EY y) ∂Q = ∫ x, Real.exp (-β * EX x) ∂P := by
    have h := hT.integral_comp' (fun y => Real.exp (-β * EY y))
    simp only [hE] at h
    exact h.symm
  refine ⟨T.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply T.measurable hs, withDensity_apply _ (T.measurable hs),
    withDensity_apply _ hs]
  have h := hT.setLIntegral_comp_preimage_emb T.measurableEmbedding
    (fun y => ENNReal.ofReal (Real.exp (-β * EY y) / ∫ y', Real.exp (-β * EY y') ∂Q)) s
  rw [← h]
  simp only [hE, hZ]

/-- A group homomorphism commutes with the hypercubic holonomy:
`wilsonHol bd q (f ∘ U) = f (wilsonHol bd q U)`, the boundary word being a product of link variables
and their inverses.

DERIVED: no numeral appears in the statement. -/
theorem wilsonHol_map {H K : Type} [Group H] [Group K] (f : H →* K) {d n : ℕ} [NeZero n]
    (q : WilsonHypercubic.Plaq d n) (U : WilsonHypercubic.Link d n → H) :
    wilsonHol (WilsonHypercubic.bd (d := d) (n := n)) q (fun i => f (U i))
      = f (wilsonHol (WilsonHypercubic.bd (d := d) (n := n)) q U) := by
  simp [wilsonHol, WilsonHypercubic.bd, map_mul, map_inv]

section SUImage

open RectWilson RectTransfer KernelPower DoublingWilson DoublingRecursion SlabKernelOperator

/-- The hypothesis that the image of their gauge group is `SU(n+1)` as a set of matrices: a unitary
`U` lies in `g.image` iff its determinant is `1`.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
abbrev ImageIsSU (g : GaugeGroup) : Prop :=
  ∀ U : UnitaryRepresentation g.n,
    U ∈ g.image ↔ (U : Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ)
      ∈ Matrix.specialUnitaryGroup (Fin (g.n + 1)) ℂ


/-- When the image of their gauge group is `SU(n+1)` as a set of matrices (`hg`), it is `SU(n+1)` as
a group: the identity on matrices.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
def imageMulEquivSU (g : GaugeGroup) (hg : ImageIsSU g) : g.image ≃* MassGap.SUN.SU (g.n + 1) where
  toFun u := ⟨u.val.val, (hg u.val).1 u.prop⟩
  invFun h := ⟨⟨h.val, (Matrix.mem_specialUnitaryGroup_iff.mp h.2).1⟩,
    (hg ⟨h.val, (Matrix.mem_specialUnitaryGroup_iff.mp h.2).1⟩).2 h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `imageMulEquivSU` as a measurable equivalence: both directions are continuous (subtype maps of
the matrix inclusion), and both sides carry their Borel σ-algebras.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
noncomputable def imageEquivSU (g : GaugeGroup) (hg : ImageIsSU g) : g.image ≃ᵐ MassGap.SUN.SU (g.n + 1) where
  toEquiv := (imageMulEquivSU g hg).toEquiv
  measurable_toFun := by
    have h0 : Continuous fun u : g.image =>
        ((u : UnitaryRepresentation g.n) : Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ) :=
      continuous_subtype_val.comp continuous_subtype_val
    have h : Continuous (imageMulEquivSU g hg) := continuous_induced_rng.2 h0
    exact h.measurable
  measurable_invFun := by
    have h : Continuous (imageMulEquivSU g hg).symm :=
      continuous_induced_rng.2 (continuous_induced_rng.2 continuous_subtype_val)
    exact h.measurable

/-- The map from our `SU(n+1)` configurations on the cubic torus of side `L` to their configurations:
each link variable read in `g.image` (`imageEquivSU`), then reindexed by `configEquiv`.

DERIVED: `4` is the spacetime dimension; `1` in `n + 1` is their matrix-size shift. -/
noncomputable def suToOpenAI (g : GaugeGroup) (hg : ImageIsSU g) (L : ℕ+) :
    (WilsonHypercubic.Link 4 L → MassGap.SUN.SU (g.n + 1)) ≃ᵐ Configuration g L :=
  (MeasurableEquiv.piCongrRight fun _ => (imageEquivSU g hg).symm).trans (configEquiv L)

/-- The energy of section 1 of `OpenAIDictionary` is the same on an `SU(n+1)` configuration and on
the same configuration read in `g.image`: the holonomies correspond by `wilsonHol_map`, the densities
by `wilsonDensityG_image_eq_SU`.

DERIVED: `4` is the spacetime dimension; `1` in `n + 1` is their matrix-size shift. -/
theorem wilsonEnergy_image_SU (g : GaugeGroup) (hg : ImageIsSU g) (L : ℕ+) (U : WilsonHypercubic.Link 4 L → MassGap.SUN.SU (g.n + 1)) :
    OpenAIDictionary.wilsonEnergy (d := 4) (n := L) (fun i => (imageMulEquivSU g hg).symm (U i))
      = OpenAIDictionary.wilsonEnergy (d := 4) (n := L) U := by
  unfold OpenAIDictionary.wilsonEnergy
  refine Finset.sum_congr rfl fun p _ => ?_
  have hm := wilsonHol_map (imageMulEquivSU g hg).symm.toMonoidHom (p.2.1, p.1) U
  simp only [MulEquiv.coe_toMonoidHom] at hm
  rw [hm]
  exact wilsonDensityG_image_eq_SU g _ _ rfl

/-- **Their law is the pushforward of our `SU(n+1)` torus law**: if `μ` on `g.image` corresponds to
`probHaar (SU(n+1))` under `imageEquivSU`, then `suToOpenAI` carries `OpenAIDictionary.wilsonLaw β`
over `probHaar` on the cubic torus of side `L` to their `wilsonLaw g L β μ`.

DERIVED: `4` is the spacetime dimension; `1` in `n + 1` is their matrix-size shift. -/
theorem measurePreserving_suToOpenAI (g : GaugeGroup) (hg : ImageIsSU g) (L : ℕ+) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hμ : μ.map (imageEquivSU g hg) = CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1))) (β : ℝ) :
    MeasurePreserving (suToOpenAI g hg L)
      (OpenAIDictionary.wilsonLaw (d := 4) (n := L) β
        (CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1))))
      (wilsonLaw g L β μ) := by
  have h1 : MeasurePreserving (imageEquivSU g hg).symm
      (CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1))) μ := by
    have h0 := (imageEquivSU g hg).measurable.measurePreserving μ
    rw [hμ] at h0
    exact MeasurePreserving.symm _ h0
  have hT : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ => (imageEquivSU g hg).symm)
      (Measure.pi fun _ : WilsonHypercubic.Link 4 L =>
        CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1)))
      (Measure.pi fun _ : WilsonHypercubic.Link 4 L => μ) :=
    MeasureTheory.measurePreserving_pi _ _ (fun _ => h1)
  have hG := measurePreserving_gibbs _ hT
    (OpenAIDictionary.wilsonEnergy (d := 4) (n := L))
    (OpenAIDictionary.wilsonEnergy (d := 4) (n := L))
    (fun U => wilsonEnergy_image_SU g hg L U) β
  exact (measurePreserving_wilsonLaw L g β μ).comp hG

/-- **Theorem 4.46 on their laws** (`SU(N)` with `N = n + 1`; their coupling `β_OAI`, ours
`β_OAI / 2`).

Let `g` be their gauge group with image `SU(n+1)` as a set of matrices (`hg`), and `μ` a probability
measure on `g.image` corresponding to `probHaar (SU(n+1))` (`hμ`; for their probability Haar measure
this is `map_imageEquivSU_eq_probHaar`, and `familyGap_on_openAI_laws'` drops it). Let `β m p ≥ 0` be couplings in their
normalization and `n m` base sides, and suppose the seed of `DoublingSharp.wilson_gap_sharp` at
`(n m, β m p / 2)`, eventually in `m` and for all `p`, as in `OpenAIDictionary.familyGap_of_seed`.
Then for all large `m`, all `p`, all `k` and every side `L : ℕ+` with `L = 2^k · n m`:

* the rectangular system `sysR (ext (n m) (corner k))`, whose transfer operator is the operator of
  the gap, is `sysWilsonG (SU(n+1)) 4 L` (`OpenAIDictionary.sysR_ext_corner`);
* its Gibbs law at `β m p / 2` against `probHaar` integrates to their law at `β m p`: for every real
  observable `O` on their configurations of side `L`, our expectation of `O ∘ suToOpenAI` is
  `∫ O ∂(wilsonLaw g L (β m p) μ)` (`OpenAIDictionary.expect_eq_integral_wilsonLaw`,
  `measurePreserving_suToOpenAI`);
* that transfer operator has the gap of `familyGap_of_seed`: a unit top eigenvector, with its
  `n m`-th power contracting the orthogonal complement by `1/2` relative to `‖T‖^(n m)`.

So their law at `β m p` on side `2^k · n m` is the torus law whose transfer operator has the gap.

DERIVED: `4` is the spacetime dimension; `16` and `1000` are the seed of `wilson_gap_sharp`
(`DoublingSharp`); `2` is the halving of the coupling (`action_eq_two_mul_wilsonEnergy`), the doubled
side, the `L²` exponent and the contraction `1/2`; `0` the sign of the coupling and the time
direction of the slice; `1` the unit norm, the kernel exponent and their matrix-size shift. -/
theorem familyGap_on_openAI_laws (g : GaugeGroup) (hg : ImageIsSU g) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hμ : μ.map (imageEquivSU g hg) = CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1)))
    (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      16 * Real.log (ZR (fun _ => n m) (g.n + 1) (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) (g.n + 1) (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ p k (L : ℕ+), (L : ℕ) = 2 ^ k * n m →
      sysR (ext (n m) (corner k)) (g.n + 1)
          = GaugeWilson.sysWilsonG (MassGap.SUN.SU (g.n + 1)) 4 L ∧
      (∀ O : Configuration g L → ℝ,
        (GaugeWilson.sysWilsonG (MassGap.SUN.SU (g.n + 1)) 4 L).expect
            (CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1))) (β m p / 2)
            (fun U => O (suToOpenAI g hg L U))
          = ∫ V, O V ∂(wilsonLaw g L (β m p) μ)) ∧
      ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1)), ‖ψ‖ = 1 ∧
        ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))‖ ∧
        kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1)) ψ
          = c • ψ ∧
        ∀ f : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1)), inner ℝ f ψ = 0 →
          ‖((kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))) ^ n m) f‖
            ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
              (continuous_kT (β m p / 2)).measurable zero_le_one
              (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
              (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
              (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))‖ ^ n m * ‖f‖ := by
  filter_upwards [OpenAIDictionary.familyGap_of_seed (Nat.succ_ne_zero g.n) β n hβ hfam]
    with m hgap p k L hL
  refine ⟨?_, fun O => ?_, hgap p k⟩
  · obtain ⟨L, hLpos⟩ := L
    simp only [PNat.mk_coe] at hL
    subst hL
    haveI : NeZero (2 ^ k * n m) := ⟨hLpos.ne'⟩
    exact OpenAIDictionary.sysR_ext_corner (g.n + 1) (n m) k
  · rw [OpenAIDictionary.expect_eq_integral_wilsonLaw, show 2 * (β m p / 2) = β m p by ring]
    exact (measurePreserving_suToOpenAI g hg L μ hμ (β m p)).integral_comp' O

/-! ## 7. Their probability Haar measure is ours -/

/-- **Their Haar measure is our `probHaar`**: when the image of their gauge group is `SU(n+1)`
(`hg`), every left-invariant probability measure `μ` on `g.image` is carried by `imageEquivSU` to
`probHaar (SU(n+1))`. Their single-link measure is such a `μ`: `WilsonFamily.haar` with the fields
`probability : IsProbabilityMeasure haar` and `invariantHaar : haar.IsHaarMeasure`
(`PublicWilson.lean:41–43`), and `IsHaarMeasure` extends `IsMulLeftInvariant`. The pushforward is a
probability measure and left-invariant, because `imageMulEquivSU` is a group isomorphism:
`h · e(u) = e(e⁻¹(h) · u)`; `haarMeasure_unique` at the default positive compact, which is all of
`SU(n+1)`, then fixes it as `probHaar`. The model is `SU2DiskLaw.probHaar_eq_nu`.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
theorem map_imageEquivSU_eq_probHaar (g : GaugeGroup) (hg : ImageIsSU g) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    μ.map (imageEquivSU g hg) = CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1)) := by
  set e := imageEquivSU g hg
  haveI : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  haveI : (μ.map e).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) e.measurable]
    have hc : ((fun x => h * x) ∘ e) = e ∘ fun u => (imageMulEquivSU g hg).symm h * u := by
      funext u
      exact Subtype.ext rfl
    rw [hc, ← Measure.map_map e.measurable (measurable_const_mul _), map_mul_left_eq_self]
  have h := MeasureTheory.Measure.haarMeasure_unique (μ.map e)
    (default : TopologicalSpace.PositiveCompacts (MassGap.SUN.SU (g.n + 1)))
  have hd : ((default : TopologicalSpace.PositiveCompacts (MassGap.SUN.SU (g.n + 1))) :
      Set (MassGap.SUN.SU (g.n + 1))) = Set.univ := TopologicalSpace.PositiveCompacts.coe_top
  rw [hd, measure_univ, one_smul] at h
  exact h

/-- **Theorem 4.46 on their laws, at their Haar measure** (`SU(N)` with `N = n + 1`; their coupling
`β_OAI`, ours `β_OAI / 2`). `familyGap_on_openAI_laws` with its measure hypothesis discharged: `μ` is
any measure with the two fields their `WilsonFamily` carries for `haar`, `IsProbabilityMeasure` and
`IsHaarMeasure` (`PublicWilson.lean:41–43`), and `map_imageEquivSU_eq_probHaar` makes it correspond to
`probHaar (SU(n+1))`. The remaining hypotheses are those of `familyGap_on_openAI_laws`: the image is
`SU(n+1)` as a set (`hg`), the couplings are non-negative, and the seed of
`DoublingSharp.wilson_gap_sharp` holds eventually.

DERIVED: `4` is the spacetime dimension; `16` and `1000` are the seed of `wilson_gap_sharp`
(`DoublingSharp`); `2` is the halving of the coupling (`action_eq_two_mul_wilsonEnergy`), the doubled
side, the `L²` exponent and the contraction `1/2`; `0` the sign of the coupling and the time
direction of the slice; `1` the unit norm, the kernel exponent and their matrix-size shift. -/
theorem familyGap_on_openAI_laws' (g : GaugeGroup) (hg : ImageIsSU g) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      16 * Real.log (ZR (fun _ => n m) (g.n + 1) (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) (g.n + 1) (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ p k (L : ℕ+), (L : ℕ) = 2 ^ k * n m →
      sysR (ext (n m) (corner k)) (g.n + 1)
          = GaugeWilson.sysWilsonG (MassGap.SUN.SU (g.n + 1)) 4 L ∧
      (∀ O : Configuration g L → ℝ,
        (GaugeWilson.sysWilsonG (MassGap.SUN.SU (g.n + 1)) 4 L).expect
            (CompactGauge.probHaar (MassGap.SUN.SU (g.n + 1))) (β m p / 2)
            (fun U => O (suToOpenAI g hg L U))
          = ∫ V, O V ∂(wilsonLaw g L (β m p) μ)) ∧
      ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1)), ‖ψ‖ = 1 ∧
        ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))‖ ∧
        kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1)) ψ
          = c • ψ ∧
        ∀ f : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1)), inner ℝ f ψ = 0 →
          ‖((kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))) ^ n m) f‖
            ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (g.n + 1) (β m p / 2)) 1
              (continuous_kT (β m p / 2)).measurable zero_le_one
              (abs_kT_le (Nat.succ_ne_zero g.n) (div_nonneg (hβ m p) zero_le_two))
              (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))
              (hS 0 (tr (ext (n m) (corner k)) 0) (g.n + 1))‖ ^ n m * ‖f‖ :=
  familyGap_on_openAI_laws g hg μ (map_imageEquivSU_eq_probHaar g hg μ) β n hβ hfam

/-! ## 8. `SU(N)` as one of their gauge groups -/

/-- `SU(n+1)` as a subgroup of their `U(n+1)`: the unitaries of determinant one. The carrier and the
closure proofs are those of their `SUtwo` (`YM/Next/FOUNDATIONS/SU2.lean:36–46`) at every `n`.

DERIVED: `1` is the determinant of the group and the matrix-size shift of `UnitaryRepresentation`. -/
def suImage (n : ℕ) : Subgroup (UnitaryRepresentation n) where
  carrier := {U | (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det = 1}
  one_mem' := Matrix.det_one
  mul_mem' {X Y} hx hy := by
    change (X.val * Y.val).det = 1
    rw [Matrix.det_mul, hx, hy, mul_one]
  inv_mem' {X} hx := by
    change (star X.val).det = 1
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hx, star_one]

/-- `suImage n` is closed in `U(n+1)`: the zero set of `det − 1`, `det` being continuous. Their
`closed_imageGroup` for `SUtwo` (`YM/Next/FOUNDATIONS/SU2.lean:47`).

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
theorem isClosed_suImage (n : ℕ) : IsClosed (suImage n : Set (UnitaryRepresentation n)) :=
  isClosed_eq (Continuous.matrix_det continuous_subtype_val) continuous_const

/-- `𝔰𝔲(n+1)`: the anti-Hermitian traceless complex matrices, a real subspace.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
def suAlgebra (n : ℕ) : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) where
  carrier := {X | Xᴴ = -X ∧ Matrix.trace X = 0}
  add_mem' {X Y} hX hY := ⟨by rw [Matrix.conjTranspose_add, hX.1, hY.1]; abel,
    by rw [Matrix.trace_add, hX.2, hY.2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c X hX := ⟨by rw [Matrix.conjTranspose_smul, hX.1, star_trivial, smul_neg],
    by rw [Matrix.trace_smul, hX.2, smul_zero]⟩

/-- **`det exp X = exp tr X` for anti-Hermitian `X`**, by the spectral theorem for the Hermitian
`−iX`: `X = u · diag(v) · u⁻¹` with `u` unitary, so `det exp X = ∏ exp vₖ = exp ∑ vₖ = exp tr X`. The
model is `ExactIneq.det_exp_eq_one`, the traceless case.

DERIVED: no numeral appears in the statement. -/
theorem det_exp_of_skew {N : ℕ} {X : Matrix (Fin N) (Fin N) ℂ} (hs : Xᴴ = -X) :
    Matrix.det (NormedSpace.exp X) = Complex.exp (Matrix.trace X) := by
  set H : Matrix (Fin N) (Fin N) ℂ := (-Complex.I) • X with hH
  have hHerm : H.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH, Matrix.conjTranspose_smul, hs]
    simp
  have hsp := hHerm.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  set u : Matrix (Fin N) (Fin N) ℂ := (hHerm.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hu
  have hu1 : u * star u = 1 := Unitary.coe_mul_star_self hHerm.eigenvectorUnitary
  have hu2 : star u * u = 1 := Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
  have hinv : u⁻¹ = star u := Matrix.inv_eq_right_inv hu1
  have hunit : IsUnit u := ⟨⟨u, star u, hu1, hu2⟩, rfl⟩
  set v : Fin N → ℂ := fun k => Complex.I * ((hHerm.eigenvalues k : ℝ) : ℂ) with hv
  have hd : Complex.I • Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) = Matrix.diagonal v := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hv]
    · simp [Matrix.diagonal_apply_ne, hab]
  have hX : X = u * Matrix.diagonal v * u⁻¹ := by
    have h1 : X = Complex.I • H := by
      rw [hH, smul_smul]; simp
    rw [h1, hsp, hinv, ← hd]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have htr : ∑ k, v k = Matrix.trace X := by
    have h1 : Matrix.trace (u * Matrix.diagonal v * star u) = ∑ k, v k := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, hu2, one_mul, Matrix.trace_diagonal]
    rw [← h1, ← hinv, ← hX]
  rw [← htr, hX, Matrix.exp_conj _ _ hunit, hinv, Matrix.exp_diagonal, Matrix.det_mul, Matrix.det_mul,
    mul_right_comm, ← Matrix.det_mul, hu1, Matrix.det_one, one_mul, Matrix.det_diagonal]
  simp only [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_sum]

/-- **Their `generates` field at `SU(n+1)`**: `X ∈ 𝔰𝔲(n+1)` iff `exp(tX)` lies in `suImage n` for
every real `t` — the field `generates` of their `GaugeGroup` (`PublicTheory.lean:30–33`) with
`lieAlgebra = suAlgebra n`. Forward: `exp(tX)` is unitary because `(tX)ᴴ = −tX` commutes with `tX`,
and `det exp(tX) = exp(t tr X) = 1` by `det_exp_of_skew`. Backward: `exp(tX) · exp(tX)ᴴ = 1` for all
`t`, so its derivative `X + Xᴴ` at `t = 0` vanishes; then `exp(t tr X) = det exp(tX) = 1` for all
`t`, so its derivative `tr X` at `t = 0` vanishes. Their own `generates_skew`
(`YM/Gauge/Lie.lean:39`) is the model for the first derivative.

DERIVED: `0` is the base point of the derivative and the trace of `𝔰𝔲`; `1` in `n + 1` is their
matrix-size shift. -/
theorem generates_su (n : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    X ∈ suAlgebra n ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈
      Set.range (fun u : suImage n ↦ (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  haveI : CompleteSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := FiniteDimensional.complete ℝ _
  have hskew : ∀ t : ℝ, Xᴴ = -X → (t • X)ᴴ = -(t • X) := fun t hs => by
    rw [Matrix.conjTranspose_smul, hs, star_trivial, smul_neg]
  constructor
  · rintro ⟨hs, ht⟩ t
    have hu : NormedSpace.exp (t • X) ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
        hskew t hs, ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl (t • X))),
        add_neg_cancel, NormedSpace.exp_zero]
    refine ⟨⟨⟨_, hu⟩, ?_⟩, rfl⟩
    show Matrix.det (NormedSpace.exp (t • X)) = 1
    rw [det_exp_of_skew (hskew t hs), Matrix.trace_smul, ht, smul_zero, Complex.exp_zero]
  · intro h
    have hs : Xᴴ = -X := by
      have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
      have hp := (hd.mul hd.star).congr_of_eventuallyEq (f₁ := fun _ : ℝ =>
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) (Filter.Eventually.of_forall fun t => by
          obtain ⟨u, hu⟩ := h t
          show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            = NormedSpace.exp (t • X) * star (NormedSpace.exp (t • X))
          rw [← hu]
          exact (Matrix.mem_unitaryGroup_iff.mp u.1.2).symm)
      have e := hp.unique (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      simp only [zero_smul, NormedSpace.exp_zero, one_mul, star_one, mul_one] at e
      rw [← Matrix.star_eq_conjTranspose]
      exact eq_neg_of_add_eq_zero_right e
    refine ⟨hs, ?_⟩
    have hc : ∀ t : ℝ, NormedSpace.exp (t • Matrix.trace X) = 1 := by
      intro t
      obtain ⟨u, hu⟩ := h t
      have hdet : Matrix.det (NormedSpace.exp (t • X)) = 1 := by
        rw [← hu]
        exact u.2
      rw [det_exp_of_skew (hskew t hs), Matrix.trace_smul, Complex.exp_eq_exp_ℂ] at hdet
      exact hdet
    have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.trace X) 0
    have hfun : (fun u : ℝ => NormedSpace.exp (u • Matrix.trace X)) = fun _ => 1 := funext hc
    rw [hfun] at hd
    have e := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
    simpa using e

/-- **`SU(N)` as their gauge group** (`N = n + 1`): the value of their `GaugeGroup`
(`PublicTheory.lean:25–33`) with image `suImage n`, closed by `isClosed_suImage`, Lie algebra
`𝔰𝔲(n+1)`, and the `generates` field `generates_su`. At `n = 1` its image is their `SUtwo` image
(`YM/Next/FOUNDATIONS/SU2.lean:36–47`), the image of their `su2` (`ConcreteSU2.lean:8–10`), and
`eq_suGauge` identifies the two values.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
def suGauge (n : ℕ) : GaugeGroup :=
  ⟨n, suImage n, isClosed_suImage n, suAlgebra n, generates_su n⟩

/-- The image of `suGauge n` is `SU(n+1)` as a set of matrices, so `familyGap_on_openAI_laws'`
applies to it.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
theorem imageIsSU_suGauge (n : ℕ) : ImageIsSU (suGauge n) := fun U =>
  ⟨fun h => Matrix.mem_specialUnitaryGroup_iff.mpr ⟨U.2, h⟩,
    fun h => (Matrix.mem_specialUnitaryGroup_iff.mp h).2⟩

/-- **A gauge group of theirs is fixed by its image**: every `g : GaugeGroup` whose image is
`suImage g.n` is `suGauge g.n`. Its `generates` field determines `lieAlgebra` from `image`, so the Lie
algebra is `𝔰𝔲(n+1)` by `generates_su`; the remaining fields are proofs. In particular their `su2`
(`ConcreteSU2.lean:8–10`), whose image has the carrier `{U | det U = 1}`, is `suGauge 1`.

DERIVED: no numeral appears in the statement. -/
theorem eq_suGauge (g : GaugeGroup) (h : g.image = suImage g.n) : g = suGauge g.n := by
  obtain ⟨n, image, closed, lie, gen⟩ := g
  change image = suImage n at h
  subst h
  have hl : lie = suAlgebra n := by
    ext X
    rw [gen X, generates_su]
  subst hl
  rfl

/-- **Theorem 4.46 on their laws at `SU(N)`, unconditionally on the group** (`N = r + 1`). At their
gauge group `suGauge r`, against any single-link measure with the fields of their `WilsonFamily.haar`
(`PublicWilson.lean:41–43`), the conclusion of `familyGap_on_openAI_laws'` holds under the seed
hypothesis alone: `imageIsSU_suGauge` supplies the image hypothesis and
`map_imageEquivSU_eq_probHaar` the measure.

DERIVED: `4` is the spacetime dimension; `16` and `1000` are the seed of `wilson_gap_sharp`
(`DoublingSharp`); `2` is the halving of the coupling (`action_eq_two_mul_wilsonEnergy`), the doubled
side, the `L²` exponent and the contraction `1/2`; `0` the sign of the coupling and the time
direction of the slice; `1` the unit norm, the kernel exponent and their matrix-size shift. -/
theorem familyGap_on_openAI_SU (r : ℕ) (μ : Measure (suGauge r).image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      16 * Real.log (ZR (fun _ => n m) (r + 1) (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) (r + 1) (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ p k (L : ℕ+), (L : ℕ) = 2 ^ k * n m →
      sysR (ext (n m) (corner k)) (r + 1)
          = GaugeWilson.sysWilsonG (MassGap.SUN.SU (r + 1)) 4 L ∧
      (∀ O : Configuration (suGauge r) L → ℝ,
        (GaugeWilson.sysWilsonG (MassGap.SUN.SU (r + 1)) 4 L).expect
            (CompactGauge.probHaar (MassGap.SUN.SU (r + 1))) (β m p / 2)
            (fun U => O (suToOpenAI (suGauge r) (imageIsSU_suGauge r) L U))
          = ∫ V, O V ∂(wilsonLaw (suGauge r) L (β m p) μ)) ∧
      ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1)), ‖ψ‖ = 1 ∧
        ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (r + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero r) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))‖ ∧
        kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (r + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero r) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1)) ψ
          = c • ψ ∧
        ∀ f : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1)), inner ℝ f ψ = 0 →
          ‖((kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (r + 1) (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le (Nat.succ_ne_zero r) (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))
            (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))) ^ n m) f‖
            ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) (r + 1) (β m p / 2)) 1
              (continuous_kT (β m p / 2)).measurable zero_le_one
              (abs_kT_le (Nat.succ_ne_zero r) (div_nonneg (hβ m p) zero_le_two))
              (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))
              (hS 0 (tr (ext (n m) (corner k)) 0) (r + 1))‖ ^ n m * ‖f‖ :=
  familyGap_on_openAI_laws' (suGauge r) (imageIsSU_suGauge r) μ β n hβ hfam

end SUImage

end MassGap.OpenAIConfig
