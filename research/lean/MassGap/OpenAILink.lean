import Mathlib
import MassGap.OpenAIConfig
import MassGap.OpenAIBridgeLimits

/-!
# MassGap.OpenAILink — the open link of section 4.8, conditional on named inputs

The OpenAI submission `yang-mills-group/OpenAI-YM-20261028` (commit `3456e5e`, Lean 4.32, not
importable here at Lean 4.31) ties its limit theory to the lattice only through `Properties.wilson`
(`ChallengeSpec.lean:178`): the mixed correlation `correlation none` is the iterated limit, spacing
first at each suitable volume and then volume along their order, of smeared lattice moments
(`Converges`, `PublicWilson.lean:85`). This module restates, exactly and with file and line, the
objects of that statement that the configuration restatement `MassGap.OpenAIConfig` does not
already carry, and proves two conditional steps on them.

## Their definitions, restated (section 1)

`timeAxis`, `Spacetime`, `time` (`PublicTheory.lean:53–57`); `Points`, `WilsonFamily`, `mesh`,
`place`, `finiteMoment`, `separated`, `SeparatedTest`, `suitable`, `smear`, `Converges`
(`PublicWilson.lean:10–90`). Their gauge group, sites, configurations and Wilson law are those of
`MassGap.OpenAIConfig`. Of their `Hierarchy` (`ChallengeSpec.lean:24–48`) the fields read here are
restated as `HierarchyFields`, and of their `Reconstructed` (`ChallengeSpec.lean:117–143`) the six
fields read here as `ReconstructedFields`: every hierarchy of theirs carries these fields with these
types, and the statements below read no other field.

## (i) The conditional transfer (sections 2–6)

`UniformDecayFrom` is the open input (U): for every time floor `δ > 0` and internal separation
`ε > 0` there is a constant `K = K(δ, ε)` (`DecayOn`) such that for every tensor test whose second
factor lies at least `τ ≥ δ` after the first in time (some `T` bounds every time of the first and
`T + τ` is below every time of the second) and keep the points of each factor `ε` apart, the smeared connected
lattice correlation of two groups of insertions is at most `K e^{−μτ} ‖t₁‖₁ ‖t₂‖₁`, eventually along
their volume order and then eventually in the spacing; the rate `μ` does not depend on `δ`, `ε`.
`DecayOn.of_eventually_forall` gives `DecayOn` from the form "eventually in `N`, for all `p`".

* `smeared_connected_le`: `DecayOn` with `Converges` at `n₁`, `n₂` and `n₁ + n₂` gives the same bound
  for the smeared connected `correlation none`, through
  `OpenAIBridgeLimits.norm_le_exp_of_iterated_limits` with their limit order.
* `connected_le_of_decayOn`, `connected_le_of_uniform`: for every `δ, ε > 0` there is `K` such that at
  every separated configuration whose two groups keep their points `ε` apart and whose second group
  lies at least `τ ≥ δ` after the first in time, the pointwise connected `correlation none` is at most `K e^{−μτ}`. Normalized product bumps
  (`bumpTest`) shrink onto the configuration; `smooth` (continuity on `separated`) carries the
  smeared values to the point values (`tendsto_integral_bump`), and `integral_prod_coord` (the volume of
  `Points n` is the product volume, through the linear isometries `pointsOneIso` and `splitIso`)
  normalizes them.

## (ii) The conditional identification (section 7)

`component_eq_mixture_of_uniform`: (U) for every pair of token groups (`UniformDecayAll`), with
component clustering (`ComponentClustering`), a conjugation of observables (`Conjugation`), a bound on
the component products (`ComponentBound`) and time-translation invariance of the mixed correlation
(`MixedTimeInvariance`), gives `correlation (some ξ) = correlation none` at every separated
configuration of at least one point, for every phase `ξ`. The mixed theory clusters by (i);
`OpenAIBridgeLimits.component_eq_mixture_of_clusters` with their `mixture`, `characterContinuity`,
`normalized` and `fullSupport` identifies the components; `represents` supplies the tokens.

## Why (U) carries floors (section 8)

`unfloored_contradicts_shortDistance`: the unfloored form (`UniformDecayUnfloored`, one constant for
every time gap, including `0`, and every test) bounds the connected two-point function at arbitrarily
close points (`connected_le_of_decayOn` at `timePair r`, gap `r`). With the identification of the
selected component with `correlation none` on `timePair r` (what (ii) delivers), this contradicts
their `TraceTest.shortDistance` (`r⁸ log²(1/r) · traceTwo r → 3 dim g / π⁴ ≠ 0`), restated as a
hypothesis. The floors `δ`, `ε` remove the contradiction: `K(δ, ε)` may grow as `δ → 0`.

## Scope

Five inputs stay open, each a named hypothesis: (U); component clustering; the conjugation; the
component bound; time-translation invariance of `correlation none`. Their public statement provides
none of them. Nothing here proves (U) for their family, ties `correlation (some selected)` to their
Wightman theory, or constructs a Hamiltonian.
-/

namespace MassGap.OpenAILink

open MeasureTheory Filter Topology Set
open scoped ContDiff ComplexConjugate
open MassGap.OpenAIConfig

/-! ## 1. Their definitions, restated -/

/-- Their time axis, the last of the four. Restated from the OpenAI submission,
`PublicTheory.lean:53` (`timeAxis : Axis := Fin.last 3`).

DERIVED: `3` is the last index of `Fin 4`; time is the final coordinate. -/
abbrev timeAxis : Axis := Fin.last 3

/-- Their Euclidean spacetime. Restated from `PublicTheory.lean:54`
(`Spacetime := EuclideanSpace ℝ Axis`).

DERIVED: no numeral appears in the statement. -/
abbrev Spacetime := EuclideanSpace ℝ Axis

/-- The time coordinate of a point. Restated from `PublicTheory.lean:57` (`time x := x timeAxis`).

DERIVED: no numeral appears in the statement. -/
def time (x : Spacetime) : ℝ := x timeAxis

/-- Ordered configurations of `n` points. Restated from `PublicWilson.lean:10`
(`Points n := PiLp 2 (fun _ : Fin n => Spacetime)`).

DERIVED: `2` is the `L²` exponent. -/
abbrev Points (n : ℕ) := PiLp 2 (fun _ : Fin n => Spacetime)

/-- Their Wilson family: periods and spacing denominators, strictly increasing, couplings `beta N p`,
a probability Haar measure on the group, a token type and lattice insertions. Restated from
`PublicWilson.lean:35–46` field for field; `GaugeGroup`, `Site` and `Configuration` are those of
`MassGap.OpenAIConfig`.

DERIVED: no numeral appears in the statement. -/
structure WilsonFamily (g : OpenAIConfig.GaugeGroup) where
  period : ℕ → ℕ+
  denominator : ℕ → ℕ+
  periodStrict : StrictMono fun p => (period p).val
  denominatorStrict : StrictMono fun N => (denominator N).val
  beta : ℕ → ℕ → ℝ
  haar : Measure g.image
  probability : IsProbabilityMeasure haar
  invariantHaar : haar.IsHaarMeasure
  Token : Type
  insertion (N p : ℕ) : Token → Site (period p * denominator N) →
    Configuration g (period p * denominator N) → ℂ

namespace WilsonFamily

variable {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g)

/-- The lattice spacing `1 / denominator N`. Restated from `PublicWilson.lean:50`.

DERIVED: no numeral appears in the statement. -/
noncomputable def mesh (N : ℕ) := ((C.denominator N).val : ℝ)⁻¹

/-- The physical position of a lattice site, coordinates in `(−l/2, l/2]` scaled by the spacing.
Restated from `PublicWilson.lean:51–52`.

DERIVED: `2` is the `L²` exponent. -/
noncomputable def place (N p : ℕ) (y : Site (C.period p * C.denominator N)) : Spacetime :=
  WithLp.toLp 2 fun i => C.mesh N * (ZMod.valMinAbs (y i) : ℝ)

/-- The finite-volume lattice moment of `n` insertions against their Wilson law. Restated from
`PublicWilson.lean:54–57`.

DERIVED: no numeral appears in the statement. -/
noncomputable def finiteMoment (N p : ℕ) {n : ℕ} (labels : Fin n → C.Token)
    (x : Fin n → Site (C.period p * C.denominator N)) : ℂ :=
  ∫ U, ∏ i, C.insertion N p (labels i) (x i) U
    ∂wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar

/-- The open set of configurations of pairwise distinct points. Restated from
`PublicWilson.lean:59–71`, proof included.

DERIVED: no numeral appears in the statement. -/
def separated (n : ℕ) : TopologicalSpace.Opens (Points n) :=
  ⟨{x | Function.Injective x.ofLp}, by
    classical
    have eqSet : {x : Points n | Function.Injective x.ofLp} =
        ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), {x : Points n | x i ≠ x j} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      exact ⟨fun h i j hij => fun he => hij (h he), fun h i j he => by_contra fun hij => h i j hij he⟩
    rw [eqSet]
    apply isOpen_iInter_of_finite; intro i
    apply isOpen_iInter_of_finite; intro j
    apply isOpen_iInter_of_finite; intro _
    exact isOpen_ne_fun (PiLp.continuous_apply _ _ i) (PiLp.continuous_apply _ _ j)⟩

/-- Smooth compactly supported tests on separated configurations. Restated from
`PublicWilson.lean:73`.

DERIVED: no numeral appears in the statement. -/
abbrev SeparatedTest (n : ℕ) := _root_.TestFunction (separated n) ℂ ⊤

/-- A test is suitable at volume `p` when its support lies in the open box of side `period p`.
Restated from `PublicWilson.lean:75–77`.

DERIVED: `2` halves the period. -/
def suitable (p : ℕ) {n : ℕ} (t : SeparatedTest n) : Prop :=
  tsupport t ⊆ {x : Points n | ∀ i a, -((C.period p).val / (2:ℝ)) < x i a ∧
    x i a < (C.period p).val / (2:ℝ)}

/-- The smeared lattice moment: the Riemann sum `mesh^{4n} Σ_x t(place x) · finiteMoment x`.
Restated from `PublicWilson.lean:79–81`.

DERIVED: `4` is the spacetime dimension; `2` the `L²` exponent. -/
noncomputable def smear (N p : ℕ) {n : ℕ} (v : Fin n → C.Token) (t : SeparatedTest n) : ℂ :=
  (C.mesh N : ℂ) ^ (4*n) * ∑ x : Fin n → Site (C.period p * C.denominator N),
    t (WithLp.toLp 2 fun i => C.place N p (x i)) * C.finiteMoment N p v x

/-- Their convergence: for every test, suitable eventually along the volume order, the full mesh
limit `row p` at each suitable volume, then the limit of `row` along the volume order is the smeared
limit correlation. Restated from `PublicWilson.lean:83–90`.

DERIVED: no numeral appears in the statement. -/
def Converges (volumeOrder : ℕ → ℕ)
    (unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : Prop :=
  ∀ n (v : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (volumeOrder k) t) ∧ ∃ row : ℕ → ℂ,
    (∀ p, C.suitable p t → Tendsto (fun N => C.smear N p v t) atTop (𝓝 (row p))) ∧
    Tendsto (fun k => row (volumeOrder k)) atTop (𝓝 (∫ x, t x * unselected v x))

end WilsonFamily

/-- The fields of their `Hierarchy` (`ChallengeSpec.lean:24–48`) that the statements here read,
restated with their names and types: `Field` and its three instances (`ChallengeSpec.lean:28–31`),
`project` (`:33`), `Character` and its four instances (`:34–38`), `phaseMeasure` (`:39`) and
`correlation` (`:41`). Every `Hierarchy C` of theirs carries these fields; the Wightman theory, the
continuation, the OPE data and `centeredTrace` are not read.

DERIVED: no numeral appears in the statement. -/
structure HierarchyFields {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) where
  Field : ℕ → Type
  [fieldAdd (d : ℕ) : NormedAddCommGroup (Field d)]
  [fieldSpace (d : ℕ) : NormedSpace ℂ (Field d)]
  [fieldFinite (d : ℕ) : FiniteDimensional ℂ (Field d)]
  project : C.Token → (Σ d, Field d)
  Character : Type
  [characterMetric : MetricSpace Character]
  [characterSets : MeasurableSpace Character]
  [characterBorel : BorelSpace Character]
  [characterCompact : CompactSpace Character]
  phaseMeasure : Measure Character
  correlation {n : ℕ} : Option Character → (Fin n → Σ d, Field d) → Points n → ℂ

attribute [instance] HierarchyFields.fieldAdd HierarchyFields.fieldSpace HierarchyFields.fieldFinite
  HierarchyFields.characterMetric HierarchyFields.characterSets HierarchyFields.characterBorel
  HierarchyFields.characterCompact

/-- Their tags, a field of some dimension. Restated from `ChallengeSpec.lean:55`
(`Tag := Σ d, T.Field d`).

DERIVED: no numeral appears in the statement. -/
abbrev HierarchyFields.Tag {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C) :=
  Σ d, T.Field d

/-- The fields of their `Reconstructed` (`ChallengeSpec.lean:117–143`) that the statements here
read, restated with their names and types: `represents` (`:123`), `normalized` (`:124`),
`fullSupport` (`:125`), `smooth` (`:129–130`), `characterContinuity` (`:131–132`) and `mixture`
(`:133–134`). Every proof of their `Reconstructed` carries these fields.

DERIVED: no numeral appears in the statement. -/
structure ReconstructedFields {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C) :
    Prop where
  represents : Function.Surjective T.project
  normalized : IsProbabilityMeasure T.phaseMeasure
  fullSupport : T.phaseMeasure.IsOpenPosMeasure
  smooth (s : Option T.Character) {n : ℕ} (a : Fin n → T.Tag) :
    ContDiffOn ℝ ∞ (T.correlation s a) (WilsonFamily.separated n)
  characterContinuity {n : ℕ} (a : Fin n → T.Tag) (x : Points n)
      (h : x ∈ WilsonFamily.separated n) : Continuous (fun i => T.correlation (some i) a x)
  mixture {n : ℕ} (a : Fin n → T.Tag) (x : Points n) (h : x ∈ WilsonFamily.separated n) :
    (∫ i, T.correlation (some i) a x ∂T.phaseMeasure) = T.correlation none a x

/-! ## 2. Splitting and joining configurations -/

/-- The first `n₁` points of a configuration of `n₁ + n₂`.

DERIVED: `2` is the `L²` exponent. -/
def leftPts {n₁ n₂ : ℕ} (y : Points (n₁ + n₂)) : Points n₁ :=
  WithLp.toLp 2 fun i => y (Fin.castAdd n₂ i)

/-- The last `n₂` points of a configuration of `n₁ + n₂`.

DERIVED: `2` is the `L²` exponent. -/
def rightPts {n₁ n₂ : ℕ} (y : Points (n₁ + n₂)) : Points n₂ :=
  WithLp.toLp 2 fun j => y (Fin.natAdd n₁ j)

/-- The configuration of `n₁ + n₂` points listing `y` and then `z`.

DERIVED: `2` is the `L²` exponent. -/
def appendPts {n₁ n₂ : ℕ} (y : Points n₁) (z : Points n₂) : Points (n₁ + n₂) :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp y) (WithLp.ofLp z))

/-- `appendPts y z` at a first-block index is `y` there.

DERIVED: no numeral appears in the statement. -/
@[simp] theorem appendPts_castAdd {n₁ n₂ : ℕ} (y : Points n₁) (z : Points n₂) (i : Fin n₁) :
    appendPts y z (Fin.castAdd n₂ i) = y i := by
  simp [appendPts]

/-- `appendPts y z` at a second-block index is `z` there.

DERIVED: no numeral appears in the statement. -/
@[simp] theorem appendPts_natAdd {n₁ n₂ : ℕ} (y : Points n₁) (z : Points n₂) (j : Fin n₂) :
    appendPts y z (Fin.natAdd n₁ j) = z j := by
  simp [appendPts]

/-- The first block of `appendPts y z` is `y`.

DERIVED: no numeral appears in the statement. -/
@[simp] theorem leftPts_appendPts {n₁ n₂ : ℕ} (y : Points n₁) (z : Points n₂) :
    leftPts (appendPts y z) = y :=
  PiLp.ext fun i => by simp [leftPts]

/-- The second block of `appendPts y z` is `z`.

DERIVED: no numeral appears in the statement. -/
@[simp] theorem rightPts_appendPts {n₁ n₂ : ℕ} (y : Points n₁) (z : Points n₂) :
    rightPts (appendPts y z) = z :=
  PiLp.ext fun j => by simp [rightPts]

/-- The first block of a separated configuration is separated.

DERIVED: no numeral appears in the statement. -/
theorem leftPts_mem_separated {n₁ n₂ : ℕ} {x : Points (n₁ + n₂)}
    (hx : x ∈ WilsonFamily.separated (n₁ + n₂)) : leftPts x ∈ WilsonFamily.separated n₁ := by
  show Function.Injective (WithLp.ofLp (leftPts x))
  intro i j h
  exact Fin.castAdd_injective _ _ (hx h)

/-- The second block of a separated configuration is separated.

DERIVED: no numeral appears in the statement. -/
theorem rightPts_mem_separated {n₁ n₂ : ℕ} {x : Points (n₁ + n₂)}
    (hx : x ∈ WilsonFamily.separated (n₁ + n₂)) : rightPts x ∈ WilsonFamily.separated n₂ := by
  show Function.Injective (WithLp.ofLp (rightPts x))
  intro i j h
  exact Fin.natAdd_injective _ _ (hx h)

/-- Composition distributes over `Fin.append`.

DERIVED: no numeral appears in the statement. -/
theorem comp_finAppend {α β : Type*} {m k : ℕ} (f : α → β) (u : Fin m → α) (v : Fin k → α) :
    f ∘ Fin.append u v = Fin.append (f ∘ u) (f ∘ v) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [Fin.append_left]
  | right j => simp [Fin.append_right]

/-- The time difference of two points is at most their distance.

DERIVED: no numeral appears in the statement. -/
theorem abs_time_sub_le (u v : Spacetime) : |time u - time v| ≤ dist u v := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (u - v) timeAxis
  rw [Real.norm_eq_abs] at h
  exact h

/-! ## 3. The volume of `Points n` is the product volume -/

/-- `y ↦ y 0` as a linear isometry `Points 1 ≃ Spacetime`.

DERIVED: `1` is the number of points; `0` its only index; `2` the `L²` exponent. -/
noncomputable def pointsOneIso : Points 1 ≃ₗᵢ[ℝ] Spacetime :=
  LinearEquiv.isometryOfInner
    { toFun := fun y => y 0
      invFun := fun z => WithLp.toLp 2 fun _ => z
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun y => PiLp.ext fun i => by fin_cases i; rfl
      right_inv := fun _ => rfl }
    (fun y z => by
      show inner ℝ (y 0) (z 0) = inner ℝ y z
      rw [PiLp.inner_apply y z, Fin.sum_univ_one])

/-- Splitting `n₁ + n₂` points into two blocks, `y ↦ (leftPts y, rightPts y)`, as a linear isometry
onto the `L²` product.

DERIVED: `2` is the `L²` exponent. -/
noncomputable def splitIso (n₁ n₂ : ℕ) :
    Points (n₁ + n₂) ≃ₗᵢ[ℝ] WithLp 2 (Points n₁ × Points n₂) :=
  LinearEquiv.isometryOfInner
    { toFun := fun y => WithLp.toLp 2 (leftPts y, rightPts y)
      invFun := fun w => appendPts (WithLp.ofLp w).1 (WithLp.ofLp w).2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun y => PiLp.ext fun i => by
        induction i using Fin.addCases with
        | left i => simp [leftPts]
        | right j => simp [rightPts]
      right_inv := fun w => by
        obtain ⟨⟨a, b⟩⟩ := w
        simp }
    (fun y z => by
      show inner ℝ (WithLp.toLp 2 (leftPts y, rightPts y)) (WithLp.toLp 2 (leftPts z, rightPts z))
        = inner ℝ y z
      rw [WithLp.prod_inner_apply, PiLp.inner_apply y z, Fin.sum_univ_add]
      rfl)

/-- Integrating a function of the single point of `Points 1` is integrating it over spacetime.

DERIVED: `1` is the number of points; `0` its only index. -/
theorem integral_pointsOne (f : Spacetime → ℝ) : ∫ y : Points 1, f (y 0) = ∫ z, f z :=
  pointsOneIso.measurePreserving.integral_comp pointsOneIso.toHomeomorph.measurableEmbedding f

/-- **Fubini on configurations**: the integral over `Points (n₁ + n₂)` of `f (first block) ·
g (second block)` is the product of the integrals. `splitIso` preserves volume
(`LinearIsometryEquiv.measurePreserving`), the `L²` product carries the product volume
(`WithLp.volume_preserving_symm_measurableEquiv_toLp_prod`), and `integral_prod_mul` finishes.

DERIVED: no numeral appears in the statement. -/
theorem integral_split_mul {n₁ n₂ : ℕ} (f : Points n₁ → ℝ) (g : Points n₂ → ℝ) :
    ∫ y : Points (n₁ + n₂), f (leftPts y) * g (rightPts y) = (∫ y, f y) * ∫ y, g y := by
  have h1 := (splitIso n₁ n₂).measurePreserving.integral_comp
    (splitIso n₁ n₂).toHomeomorph.measurableEmbedding
    (fun w : WithLp 2 (Points n₁ × Points n₂) => f (WithLp.ofLp w).1 * g (WithLp.ofLp w).2)
  have h2 := (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod (Points n₁)
    (Points n₂)).integral_comp' (fun q : Points n₁ × Points n₂ => f q.1 * g q.2)
  have h3 : ∫ q : Points n₁ × Points n₂, f q.1 * g q.2 = (∫ y, f y) * ∫ y, g y :=
    integral_prod_mul f g
  exact h1.trans (h2.trans h3)

/-- **The product integral on `m + 1` points**: `∫ ∏ᵢ φᵢ(yᵢ) dy = ∏ᵢ ∫ φᵢ`. By induction, splitting
off the last point with `integral_split_mul` and reading it with `integral_pointsOne`.

DERIVED: `1` is the step of the induction and the one-point block. -/
theorem integral_prod_coord (m : ℕ) :
    ∀ φ : Fin (m + 1) → Spacetime → ℝ, ∫ y : Points (m + 1), ∏ i, φ i (y i) = ∏ i, ∫ z, φ i z := by
  induction m with
  | zero =>
    intro φ
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    exact integral_pointsOne (φ 0)
  | succ m ih =>
    intro φ
    have hl : Fin.natAdd (m + 1) (0 : Fin 1) = Fin.last (m + 1) := Fin.ext (by simp)
    have hsplit : ∀ y : Points (m + 1 + 1), ∏ i, φ i (y i)
        = (∏ i : Fin (m + 1), φ (Fin.castSucc i) (leftPts y i))
          * φ (Fin.last (m + 1)) (rightPts y 0) := by
      intro y
      rw [Fin.prod_univ_castSucc]
      show _ = (∏ i : Fin (m + 1), φ (Fin.castSucc i) (y (Fin.castAdd 1 i)))
          * φ (Fin.last (m + 1)) (y (Fin.natAdd (m + 1) 0))
      rw [hl]
      rfl
    calc ∫ y : Points (m + 1 + 1), ∏ i, φ i (y i)
        = ∫ y : Points (m + 1 + 1), (∏ i : Fin (m + 1), φ (Fin.castSucc i) (leftPts y i))
            * φ (Fin.last (m + 1)) (rightPts y 0) :=
          integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = (∫ u : Points (m + 1), ∏ i : Fin (m + 1), φ (Fin.castSucc i) (u i))
            * ∫ v : Points 1, φ (Fin.last (m + 1)) (v 0) :=
          integral_split_mul (fun u : Points (m + 1) => ∏ i : Fin (m + 1), φ (Fin.castSucc i) (u i))
            (fun v : Points 1 => φ (Fin.last (m + 1)) (v 0))
      _ = (∏ i : Fin (m + 1), ∫ z, φ (Fin.castSucc i) z) * ∫ z, φ (Fin.last (m + 1)) z := by
          rw [ih (fun i => φ (Fin.castSucc i)), integral_pointsOne (φ (Fin.last (m + 1)))]
      _ = ∏ i, ∫ z, φ i z := (Fin.prod_univ_castSucc (fun i => ∫ z, φ i z)).symm

/-! ## 4. Product bumps -/

/-- The smooth bump at `c` equal to one on the ball of radius `r/2`, supported in the ball of
radius `r`.

DERIVED: `2` halves the radius. -/
noncomputable def bumpAt (c : Spacetime) (r : ℝ) (hr : 0 < r) : ContDiffBump c :=
  ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

/-- The product of normalized bumps of radius `r` at the points of `c`: `∏ᵢ φ_{cᵢ}(yᵢ)`, each
factor of integral one.

DERIVED: no numeral appears in the statement. -/
noncomputable def bumpFun {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r) (y : Points n) : ℝ :=
  ∏ i, (bumpAt (c i) r hr).normed volume (y i)

/-- The configurations within `r` of `c` in every point.

DERIVED: no numeral appears in the statement. -/
def coordBox {n : ℕ} (c : Points n) (r : ℝ) : Set (Points n) := {y | ∀ i, dist (y i) (c i) ≤ r}

/-- `coordBox c r` is compact: the image of a product of closed balls.

DERIVED: `2` is the `L²` exponent. -/
theorem isCompact_coordBox {n : ℕ} (c : Points n) (r : ℝ) : IsCompact (coordBox c r) := by
  have h : coordBox c r = WithLp.toLp 2 '' Set.univ.pi fun i => Metric.closedBall (c i) r := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, fun i _ => hy i, by simp⟩
    · rintro ⟨w, hw, rfl⟩ i
      exact hw i (Set.mem_univ i)
  rw [h]
  exact (isCompact_univ_pi fun i => isCompact_closedBall (c i) r).image (PiLp.continuous_toLp 2 _)

/-- The product bump is nonnegative.

DERIVED: `0` is the lower bound. -/
theorem bumpFun_nonneg {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r) (y : Points n) :
    0 ≤ bumpFun c r hr y :=
  Finset.prod_nonneg fun i _ => (bumpAt (c i) r hr).nonneg_normed (y i)

/-- Where the product bump is not zero, every point is within `r` of its centre.

DERIVED: `0` is the vanishing value. -/
theorem dist_lt_of_bumpFun_ne_zero {n : ℕ} {c : Points n} {r : ℝ} {hr : 0 < r} {y : Points n}
    (h : bumpFun c r hr y ≠ 0) (i : Fin n) : dist (y i) (c i) < r := by
  have hi : (bumpAt (c i) r hr).normed volume (y i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
  have hs : y i ∈ Function.support ((bumpAt (c i) r hr).normed volume) := hi
  rw [(bumpAt (c i) r hr).support_normed_eq] at hs
  exact hs

/-- The product bump vanishes off `coordBox c r`.

DERIVED: `0` is the vanishing value. -/
theorem bumpFun_eq_zero_of_not_mem {n : ℕ} {c : Points n} {r : ℝ} {hr : 0 < r} {y : Points n}
    (hy : y ∉ coordBox c r) : bumpFun c r hr y = 0 := by
  by_contra h
  exact hy fun i => (dist_lt_of_bumpFun_ne_zero h i).le

/-- The product bump is smooth.

DERIVED: no numeral appears in the statement. -/
theorem contDiff_bumpFun {n : ℕ} {k : ℕ∞} (c : Points n) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ k (bumpFun c r hr) := by
  unfold bumpFun
  exact contDiff_prod fun i _ =>
    (bumpAt (c i) r hr).contDiff_normed.comp (contDiff_piLp_apply (p := 2))

/-- The product bump is continuous.

DERIVED: no numeral appears in the statement. -/
theorem continuous_bumpFun {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r) :
    Continuous (bumpFun c r hr) :=
  (contDiff_bumpFun (k := ⊤) c r hr).continuous

/-- The product bump has compact support.

DERIVED: no numeral appears in the statement. -/
theorem hasCompactSupport_bumpFun {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (bumpFun c r hr) :=
  HasCompactSupport.intro (isCompact_coordBox c r) fun _ hy => bumpFun_eq_zero_of_not_mem hy

/-- The support closure of the product bump lies in `coordBox c r`.

DERIVED: no numeral appears in the statement. -/
theorem tsupport_bumpFun_subset {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r) :
    tsupport (bumpFun c r hr) ⊆ coordBox c r :=
  closure_minimal (fun _ hy i => (dist_lt_of_bumpFun_ne_zero hy i).le)
    (isCompact_coordBox c r).isClosed

/-- The product bump is integrable.

DERIVED: no numeral appears in the statement. -/
theorem integrable_bumpFun {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r) :
    Integrable (bumpFun c r hr) :=
  (continuous_bumpFun c r hr).integrable_of_hasCompactSupport (hasCompactSupport_bumpFun c r hr)

/-- The product bump on at least one point has integral one (`integral_prod_coord`, each factor
normalized).

DERIVED: `0` and `1`: at least one point, and the unit integral. -/
theorem integral_bumpFun {n : ℕ} (hn : 0 < n) (c : Points n) (r : ℝ) (hr : 0 < r) :
    ∫ y, bumpFun c r hr y = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold bumpFun
  rw [integral_prod_coord m (fun i => (bumpAt (c i) r hr).normed volume)]
  exact Finset.prod_eq_one fun i _ => (bumpAt (c i) r hr).integral_normed

/-- The product bump as one of their separated tests, when `coordBox c r` lies in `separated n`.

DERIVED: no numeral appears in the statement. -/
noncomputable def bumpTest {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r)
    (hs : coordBox c r ⊆ WilsonFamily.separated n) : WilsonFamily.SeparatedTest n :=
  ⟨fun y => (bumpFun c r hr y : ℂ),
    Complex.ofRealCLM.contDiff.comp (contDiff_bumpFun c r hr),
    HasCompactSupport.intro (isCompact_coordBox c r) fun _ hy => by
      simp only [bumpFun_eq_zero_of_not_mem hy, Complex.ofReal_zero],
    (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero (bumpFun c r hr)).trans
      ((tsupport_bumpFun_subset c r hr).trans hs)⟩

/-- `bumpTest` is the product bump, read in `ℂ`.

DERIVED: no numeral appears in the statement. -/
theorem bumpTest_apply {n : ℕ} (c : Points n) (r : ℝ) (hr : 0 < r)
    (hs : coordBox c r ⊆ WilsonFamily.separated n) (y : Points n) :
    bumpTest c r hr hs y = (bumpFun c r hr y : ℂ) := rfl

/-- The `L¹` norm of `bumpTest` on at least one point is one.

DERIVED: `0` and `1`: at least one point, and the unit norm. -/
theorem integral_norm_bumpTest {n : ℕ} (hn : 0 < n) (c : Points n) (r : ℝ) (hr : 0 < r)
    (hs : coordBox c r ⊆ WilsonFamily.separated n) : ∫ y, ‖bumpTest c r hr hs y‖ = 1 := by
  have h : ∀ y, ‖bumpTest c r hr hs y‖ = bumpFun c r hr y := fun y =>
    Complex.norm_of_nonneg (bumpFun_nonneg c r hr y)
  exact (integral_congr_ae (Filter.Eventually.of_forall h)).trans (integral_bumpFun hn c r hr)

/-- The product bump times a function continuous on `separated n` is integrable, when the box lies
in `separated n`.

DERIVED: no numeral appears in the statement. -/
theorem integrable_bump_mul {n : ℕ} {c : Points n} {r : ℝ} {hr : 0 < r}
    (hs : coordBox c r ⊆ WilsonFamily.separated n) {f : Points n → ℂ}
    (hf : ContinuousOn f (WilsonFamily.separated n)) :
    Integrable (fun y => (bumpFun c r hr y : ℂ) * f y) := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := coordBox c r) ?_ ?_
  · exact ContinuousOn.integrableOn_compact (isCompact_coordBox c r)
      ((Complex.continuous_ofReal.comp (continuous_bumpFun c r hr)).continuousOn.mul (hf.mono hs))
  · intro y hy
    simp only [bumpFun_eq_zero_of_not_mem hy, Complex.ofReal_zero, zero_mul]

/-- A neighbourhood of a configuration contains every configuration close to it point by point.

DERIVED: `0` is the lower bound of the radius; `2` the `L²` exponent. -/
theorem exists_coord_nhds {n : ℕ} {x : Points n} {s : Set (Points n)} (hs : s ∈ 𝓝 x) :
    ∃ ε > 0, ∀ y : Points n, (∀ i, dist (y i) (x i) < ε) → y ∈ s := by
  have h1 : (WithLp.toLp 2 : (Fin n → Spacetime) → Points n) ⁻¹' s ∈ 𝓝 (WithLp.ofLp x) := by
    apply (PiLp.continuous_toLp 2 _).continuousAt.preimage_mem_nhds
    rwa [WithLp.toLp_ofLp]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h1
  refine ⟨ε, hε, fun y hy => ?_⟩
  have hy' : WithLp.ofLp y ∈ Metric.ball (WithLp.ofLp x) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    exact hy
  have h2 := hball hy'
  simpa using h2

/-- **Approximate identities**: normalized nonnegative weights whose supports shrink onto `x₀` carry
`∫ t_k f` to `f x₀` at a point of continuity.

DERIVED: `2` halves the tolerance; `0` and `1` are the weight sign and the unit integral. -/
theorem tendsto_integral_bump {E : Type*} [MeasurableSpace E] [TopologicalSpace E] {μ : Measure E}
    {f : E → ℂ} {x₀ : E} (hf : ContinuousAt f x₀) (t : ℕ → E → ℝ) (ht0 : ∀ k y, 0 ≤ t k y)
    (htI : ∀ k, Integrable (t k) μ) (ht1 : ∀ k, ∫ y, t k y ∂μ = 1)
    (hsupp : ∀ s ∈ 𝓝 x₀, ∀ᶠ k in atTop, ∀ y, t k y ≠ 0 → y ∈ s)
    (hI : ∀ k, Integrable (fun y => (t k y : ℂ) * f y) μ) :
    Tendsto (fun k => ∫ y, (t k y : ℂ) * f y ∂μ) atTop (𝓝 (f x₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hs : f ⁻¹' Metric.ball (f x₀) (ε / 2) ∈ 𝓝 x₀ :=
    hf.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hsupp _ hs] with k hk
  have htC : Integrable (fun y => (t k y : ℂ)) μ := (htI k).ofReal
  have hsplit : (∫ y, (t k y : ℂ) * f y ∂μ) - f x₀ = ∫ y, (t k y : ℂ) * (f y - f x₀) ∂μ := by
    have h1 : ∫ y, (t k y : ℂ) * f x₀ ∂μ = f x₀ := by
      rw [integral_mul_const, integral_complex_ofReal, ht1, Complex.ofReal_one, one_mul]
    simp_rw [mul_sub]
    rw [integral_sub (hI k) (htC.mul_const _), h1]
  rw [dist_eq_norm, hsplit]
  have hle : ‖∫ y, (t k y : ℂ) * (f y - f x₀) ∂μ‖ ≤ ∫ y, t k y * (ε / 2) ∂μ := by
    refine norm_integral_le_of_norm_le ((htI k).mul_const _) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_of_nonneg (ht0 k y)]
    by_cases hy : t k y = 0
    · simp [hy]
    · have h := hk y hy
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_left h.le (ht0 k y)
  rw [integral_mul_const, ht1, one_mul] at hle
  linarith

/-- Product bumps of radii `r k → 0` at a separated configuration `c` carry `∫ bump · f` to `f c`,
for `f` continuous on `separated n`.

DERIVED: `0` is the limit of the radii and the lower bounds. -/
theorem tendsto_bump_integral {n : ℕ} (hn : 0 < n) {c : Points n}
    (hc : c ∈ WilsonFamily.separated n) {f : Points n → ℂ}
    (hf : ContinuousOn f (WilsonFamily.separated n)) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hbox : ∀ k, coordBox c (r k) ⊆ WilsonFamily.separated n) :
    Tendsto (fun k => ∫ y, (bumpFun c (r k) (hr k) y : ℂ) * f y) atTop (𝓝 (f c)) :=
  tendsto_integral_bump (hf.continuousAt ((WilsonFamily.separated n).isOpen.mem_nhds hc))
    (fun k => bumpFun c (r k) (hr k)) (fun k y => bumpFun_nonneg c (r k) (hr k) y)
    (fun k => integrable_bumpFun c (r k) (hr k)) (fun k => integral_bumpFun hn c (r k) (hr k))
    (fun s hs => by
      obtain ⟨ε, hε, h⟩ := exists_coord_nhds hs
      filter_upwards [hr0.eventually (gt_mem_nhds hε)] with k hk y hy
      exact h y fun i => (dist_lt_of_bumpFun_ne_zero hy i).trans hk)
    (fun k => integrable_bump_mul (hbox k) hf)

/-- The product bump at a configuration of `n₁ + n₂` points is the product of the bumps at its two
blocks.

DERIVED: no numeral appears in the statement. -/
theorem bumpFun_split {n₁ n₂ : ℕ} (c : Points (n₁ + n₂)) (r : ℝ) (hr : 0 < r)
    (y : Points (n₁ + n₂)) :
    bumpFun c r hr y = bumpFun (leftPts c) r hr (leftPts y) * bumpFun (rightPts c) r hr (rightPts y) := by
  unfold bumpFun
  rw [Fin.prod_univ_add]
  rfl

/-! ## 5. (U) and the smeared transfer -/

/-- The points of a configuration are pairwise at least `ε` apart.

DERIVED: no numeral appears in the statement. -/
def PtsSep {n : ℕ} (ε : ℝ) (y : Points n) : Prop :=
  ∀ i i' : Fin n, i ≠ i' → ε ≤ dist (y i) (y i')

/-- Every configuration in the support of a test has its points pairwise at least `ε` apart.

DERIVED: no numeral appears in the statement. -/
def GroupSep {n : ℕ} (ε : ℝ) (t : WilsonFamily.SeparatedTest n) : Prop :=
  ∀ y ∈ tsupport t, PtsSep ε y

/-- Every separated configuration has its points pairwise at least some `ε > 0` apart.

DERIVED: `0` is the lower bound of the separation. -/
theorem exists_ptsSep {n : ℕ} {x : Points n} (hx : x ∈ WilsonFamily.separated n) :
    ∃ ε : ℝ, 0 < ε ∧ PtsSep ε x := by
  classical
  let d : Fin n × Fin n → ℝ := fun q => dist (x q.1) (x q.2)
  let S : Finset (Fin n × Fin n) := Finset.univ.filter (fun q => q.1 ≠ q.2)
  by_cases hS : S.Nonempty
  · obtain ⟨q₀, hq₀, hmin⟩ := S.exists_min_image d hS
    refine ⟨d q₀, dist_pos.2 fun h => (Finset.mem_filter.1 hq₀).2 (hx h), fun i i' hii => ?_⟩
    exact hmin (i, i') (Finset.mem_filter.2 ⟨Finset.mem_univ _, hii⟩)
  · refine ⟨1, one_pos, fun i i' hii => ?_⟩
    exact absurd ⟨(i, i'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hii⟩⟩ hS

/-- A smaller separation is implied by a larger one.

DERIVED: no numeral appears in the statement. -/
theorem PtsSep.mono {n : ℕ} {ε ε' : ℝ} {y : Points n} (h : PtsSep ε y) (hε : ε' ≤ ε) :
    PtsSep ε' y :=
  fun i i' hii => hε.trans (h i i' hii)

/-- The smeared clustering bound with a fixed constant `K` and rate `μ`, on the tensor tests
`t = t₁ ⊗ t₂` whose second factor lies at least `τ ≥ δ` after the first in time (some `T` bounds
every time of `t₁` and `T + τ` is below every time of `t₂`) and keep the points of each factor at
least `ε` apart: eventually along their volume order and then in the spacing, the smeared lattice
connected correlation is at most `K e^{−μτ} ‖t₁‖₁ ‖t₂‖₁`.

DERIVED: no numeral appears in the statement. -/
def DecayOn {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) (order : ℕ → ℕ) {n₁ n₂ : ℕ}
    (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (K μ δ ε : ℝ) : Prop :=
  ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
    (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
    (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧ ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
    ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
      ‖C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂‖ ≤
        K * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) * Real.exp (-μ * τ)

/-- `DecayOn` from its form "eventually in `N`, for all `p` and all admissible tensor tests".

DERIVED: no numeral appears in the statement. -/
theorem DecayOn.of_eventually_forall {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    {order : ℕ → ℕ} {n₁ n₂ : ℕ} {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {K μ δ ε : ℝ}
    (h : ∀ᶠ N in atTop, ∀ p (t : WilsonFamily.SeparatedTest (n₁ + n₂))
      (t₁ : WilsonFamily.SeparatedTest n₁) (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ),
      δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
      (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
      (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧ ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
      ‖C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂‖ ≤
        K * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) * Real.exp (-μ * τ)) :
    DecayOn C order w₁ w₂ K μ δ ε :=
  fun t t₁ t₂ τ hτ hs₁ hs₂ ht hg =>
    Filter.Eventually.of_forall fun p => h.mono fun _ hN => hN p t t₁ t₂ τ hτ hs₁ hs₂ ht hg

/-- **Open input (U), floored uniform smeared clustering on the lattice.** For token groups `w₁`,
`w₂` and a rate `μ`: for every time floor `δ > 0` and every internal separation `ε > 0` there is a
constant `K = K(δ, ε)` with `DecayOn C order w₁ w₂ K μ δ ε`, i.e. every tensor test whose second
factor lies at least `τ ≥ δ` after the first in time and keep the points of each factor `ε` apart has smeared lattice connected
correlation at most `K e^{−μτ} ‖t₁‖₁ ‖t₂‖₁`, eventually along their volume order and then in the
spacing. The rate does not depend on `δ` or `ε`.

The floors are necessary. Without them (`UniformDecayUnfloored`), the constant would bound the
connected correlation at arbitrarily close points, which no insertion of positive dimension
allows: `unfloored_contradicts_shortDistance`. Their public statement does not provide (U):
`WilsonRegularity` bounds no insertion uniformly in the spacing, and their insertions are
renormalized.

DERIVED: `0` is the lower bound of the floors. -/
def UniformDecayFrom {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) (order : ℕ → ℕ) {n₁ n₂ : ℕ}
    (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (μ : ℝ) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K : ℝ, DecayOn C order w₁ w₂ K μ δ ε

/-- The unfloored form: one constant `K` for every tensor test whose second factor lies at least `τ`
after the first in time,
for every real `τ`, with no internal separation. It is refuted for every insertion with a singular
short-distance two-point function (`unfloored_contradicts_shortDistance`); it is kept only as the
hypothesis of that refutation.

DERIVED: no numeral appears in the statement. -/
def UniformDecayUnfloored {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) (order : ℕ → ℕ)
    {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (K μ : ℝ) : Prop :=
  ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ),
    (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
    (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧ ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
    ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
      ‖C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂‖ ≤
        K * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) * Real.exp (-μ * τ)

/-- The unfloored form gives `DecayOn` at every floor with the same constant.

DERIVED: no numeral appears in the statement. -/
theorem UniformDecayUnfloored.decayOn {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    {order : ℕ → ℕ} {n₁ n₂ : ℕ} {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {K μ : ℝ}
    (h : UniformDecayUnfloored C order w₁ w₂ K μ) (δ ε : ℝ) : DecayOn C order w₁ w₂ K μ δ ε :=
  fun t t₁ t₂ τ _ _ _ ht hg => h t t₁ t₂ τ ht hg

/-- **The smeared transfer.** Under `DecayOn` at a floor `δ`, `ε` and their convergence
`Properties.wilson` (`ChallengeSpec.lean:178`, `Converges` at `n₁`, `n₂` and `n₁ + n₂`), the smeared
connected mixed correlation of a tensor test whose second factor lies at least `τ ≥ δ` after the first
in time and keep their
points `ε` apart obeys the bound of `DecayOn`. The three
rows converge in the spacing at every volume where all three tests are suitable, then along the
volume order; `OpenAIBridgeLimits.norm_le_exp_of_iterated_limits` with `l₁ = atTop` (spacing) and
`l₂ = map order atTop` (volume) carries the bound through both limits.

DERIVED: no numeral appears in the statement. -/
theorem smeared_connected_le {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C)
    {order : ℕ → ℕ} (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    {n₁ n₂ : ℕ} {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {K μ δ ε : ℝ}
    (hU : DecayOn C order w₁ w₂ K μ δ ε) (t : WilsonFamily.SeparatedTest (n₁ + n₂))
    (t₁ : WilsonFamily.SeparatedTest n₁) (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ)
    (hτ : δ ≤ τ) (hg₁ : GroupSep ε t₁) (hg₂ : GroupSep ε t₂)
    (htens : ∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y))
    (hgap : ∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
      ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) :
    ‖(∫ y, t y * T.correlation none (T.project ∘ Fin.append w₁ w₂) y)
        - (∫ y, t₁ y * T.correlation none (T.project ∘ w₁) y)
          * ∫ y, t₂ y * T.correlation none (T.project ∘ w₂) y‖
      ≤ K * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) * Real.exp (-μ * τ) := by
  classical
  obtain ⟨hs, row, hrow, hlim⟩ := hW (n₁ + n₂) (Fin.append w₁ w₂) t
  obtain ⟨hs₁, row₁, hrow₁, hlim₁⟩ := hW n₁ w₁ t₁
  obtain ⟨hs₂, row₂, hrow₂, hlim₂⟩ := hW n₂ w₂ t₂
  let P : ℕ → Prop := fun p => C.suitable p t ∧ C.suitable p t₁ ∧ C.suitable p t₂
  let c : ℕ → ℕ → ℝ → ℂ := fun N p _ => if P p then
    C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂ else 0
  let L : ℕ → ℝ → ℂ := fun p _ => if P p then row p - row₁ p * row₂ p else 0
  refine OpenAIBridgeLimits.norm_le_exp_of_iterated_limits (l₁ := fun _ : ℕ => (atTop : Filter ℕ))
    (l₂ := Filter.map order atTop) (c := c) (L := L) (T := {τ})
    (Llim := fun _ => (∫ y, t y * T.correlation none (T.project ∘ Fin.append w₁ w₂) y)
        - (∫ y, t₁ y * T.correlation none (T.project ∘ w₁) y)
          * ∫ y, t₂ y * T.correlation none (T.project ∘ w₂) y)
    (C := K * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖)) (μ := μ) ?_ ?_ ?_ τ (Set.mem_singleton τ)
  · intro τ' _ p
    by_cases hp : P p
    · simp only [c, L, if_pos hp]
      exact (hrow p hp.1).sub ((hrow₁ p hp.2.1).mul (hrow₂ p hp.2.2))
    · simp only [c, L, if_neg hp]
      exact tendsto_const_nhds
  · intro τ' _
    rw [tendsto_map'_iff]
    refine Tendsto.congr' ?_ (hlim.sub (hlim₁.mul hlim₂))
    filter_upwards [hs, hs₁, hs₂] with k h h₁ h₂
    have hP : P (order k) := ⟨h, h₁, h₂⟩
    simp only [Function.comp_apply, L, if_pos hP]
  · intro τ' hτ'
    rw [Set.mem_singleton_iff.mp hτ']
    have hev : ∀ᶠ p in Filter.map order atTop, P p :=
      Filter.eventually_map.2 ((hs.and (hs₁.and hs₂)).mono fun _ h => h)
    filter_upwards [hU t t₁ t₂ τ hτ hg₁ hg₂ htens hgap, hev] with p hp hP
    filter_upwards [hp] with N hN
    simp only [c, if_pos hP]
    exact hN

/-! ## 6. The pointwise transfer -/

/-- **The pointwise transfer at a fixed constant.** Under `DecayOn C order w₁ w₂ K μ (δ/2) (ε/2)` for
token groups of at least one token each, their convergence `Properties.wilson` and their smoothness
`smooth` at `none`: at every separated configuration `x` of `n₁ + n₂` points whose blocks keep their
points `ε` apart and whose second block lies at least `τ ≥ δ` after the first in time,
`‖S(x) − S(leftPts x) · S(rightPts x)‖ ≤ K e^{−μτ}`.

Normalized product bumps of radius `r_k → 0`, `r_k ≤ δ/4` and `r_k ≤ ε/4`, at `x` and at its two
blocks form tensor tests in `separated` whose factors are `τ − 2 r_k ≥ δ/2` apart, keep their points
`ε − 2 r_k ≥ ε/2` apart and have `L¹` norm one (`integral_bumpFun`). `smeared_connected_le` bounds
their smeared connected correlation by `K e^{−μ(τ − 2 r_k)}`; continuity on `separated` (`smooth`)
carries the three smeared values to the point values (`tendsto_bump_integral`), and the bound passes
to the limit.

DERIVED: `0` is the lower bound of the block sizes and of the floors; `2` halves the floors. -/
theorem connected_le_of_decayOn {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C)
    (hR : ReconstructedFields T) {order : ℕ → ℕ}
    (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token}
    {K μ δ ε : ℝ} (hδ : 0 < δ) (hεpos : 0 < ε) (hU : DecayOn C order w₁ w₂ K μ (δ / 2) (ε / 2))
    (x : Points (n₁ + n₂)) (hx : x ∈ WilsonFamily.separated (n₁ + n₂))
    (hsep₁ : PtsSep ε (leftPts x)) (hsep₂ : PtsSep ε (rightPts x)) (τ : ℝ) (hδτ : δ ≤ τ)
    (hτ : ∃ T : ℝ, (∀ i, time (x (Fin.castAdd n₂ i)) ≤ T) ∧
      ∀ j, T + τ ≤ time (x (Fin.natAdd n₁ j))) :
    ‖T.correlation none (T.project ∘ Fin.append w₁ w₂) x
        - T.correlation none (T.project ∘ w₁) (leftPts x)
          * T.correlation none (T.project ∘ w₂) (rightPts x)‖
      ≤ K * Real.exp (-μ * τ) := by
  have hx₁ := leftPts_mem_separated hx
  have hx₂ := rightPts_mem_separated hx
  obtain ⟨ε₀, hε₀, h₀⟩ := exists_coord_nhds ((WilsonFamily.separated (n₁ + n₂)).isOpen.mem_nhds hx)
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_coord_nhds ((WilsonFamily.separated n₁).isOpen.mem_nhds hx₁)
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_coord_nhds ((WilsonFamily.separated n₂).isOpen.mem_nhds hx₂)
  set ε' := min (min ε₀ (min ε₁ ε₂)) (min (δ / 4) (ε / 4))
  have hε' : 0 < ε' := lt_min (lt_min hε₀ (lt_min hε₁ hε₂)) (lt_min (by linarith) (by linarith))
  have hεa : ε' ≤ min ε₀ (min ε₁ ε₂) := min_le_left _ _
  have hεδ : ε' ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεε : ε' ≤ ε / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let r : ℕ → ℝ := fun k => ε' / ((k + 2 : ℕ) : ℝ)
  have hr : ∀ k, 0 < r k := fun k => div_pos hε' (by positivity)
  have hrε : ∀ k, r k < ε' := fun k => div_lt_self hε' (by norm_cast; omega)
  have hr0 : Tendsto r atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat ε')
  have hb0 : ∀ k, coordBox x (r k) ⊆ WilsonFamily.separated (n₁ + n₂) := fun k y hy =>
    h₀ y fun i => (hy i).trans_lt (((hrε k).trans_le hεa).trans_le (min_le_left _ _))
  have hb1 : ∀ k, coordBox (leftPts x) (r k) ⊆ WilsonFamily.separated n₁ := fun k y hy =>
    h₁ y fun i => (hy i).trans_lt (((hrε k).trans_le hεa).trans_le
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hb2 : ∀ k, coordBox (rightPts x) (r k) ⊆ WilsonFamily.separated n₂ := fun k y hy =>
    h₂ y fun i => (hy i).trans_lt (((hrε k).trans_le hεa).trans_le
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hc0 := (hR.smooth none (T.project ∘ Fin.append w₁ w₂)).continuousOn
  have hc1 := (hR.smooth none (T.project ∘ w₁)).continuousOn
  have hc2 := (hR.smooth none (T.project ∘ w₂)).continuousOn
  have hS := tendsto_bump_integral (by omega) hx hc0 hr hr0 hb0
  have hS₁ := tendsto_bump_integral hn₁ hx₁ hc1 hr hr0 hb1
  have hS₂ := tendsto_bump_integral hn₂ hx₂ hc2 hr hr0 hb2
  have hsepBox : ∀ {m : ℕ} (c : Points m), PtsSep ε c → ∀ k, ∀ y ∈ coordBox c (r k),
      PtsSep (ε / 2) y := by
    intro m c hc k y hy i i' hii
    have h4 := dist_triangle4 (c i) (y i) (y i') (c i')
    have e1 : dist (c i) (y i) ≤ r k := by rw [dist_comm]; exact hy i
    have e2 : dist (y i') (c i') ≤ r k := hy i'
    have e3 := hc i i' hii
    have e4 : r k ≤ ε / 4 := ((hrε k).le).trans hεε
    linarith
  have hbound : ∀ k,
      ‖(∫ y, (bumpFun x (r k) (hr k) y : ℂ) * T.correlation none (T.project ∘ Fin.append w₁ w₂) y)
        - (∫ y, (bumpFun (leftPts x) (r k) (hr k) y : ℂ) * T.correlation none (T.project ∘ w₁) y)
          * ∫ y, (bumpFun (rightPts x) (r k) (hr k) y : ℂ) * T.correlation none (T.project ∘ w₂) y‖
        ≤ K * Real.exp (-μ * (τ - 2 * r k)) := by
    intro k
    have htens : ∀ y, bumpTest x (r k) (hr k) (hb0 k) y
        = bumpTest (leftPts x) (r k) (hr k) (hb1 k) (leftPts y)
          * bumpTest (rightPts x) (r k) (hr k) (hb2 k) (rightPts y) := fun y => by
      rw [bumpTest_apply, bumpTest_apply, bumpTest_apply, bumpFun_split, Complex.ofReal_mul]
    have hsupp1 : ∀ y ∈ tsupport (bumpTest (leftPts x) (r k) (hr k) (hb1 k)),
        y ∈ coordBox (leftPts x) (r k) := fun y hy =>
      ((tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
        (bumpFun (leftPts x) (r k) (hr k))).trans (tsupport_bumpFun_subset _ _ _)) hy
    have hsupp2 : ∀ z ∈ tsupport (bumpTest (rightPts x) (r k) (hr k) (hb2 k)),
        z ∈ coordBox (rightPts x) (r k) := fun z hz =>
      ((tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
        (bumpFun (rightPts x) (r k) (hr k))).trans (tsupport_bumpFun_subset _ _ _)) hz
    have hgap : ∃ T' : ℝ,
        (∀ y ∈ tsupport (bumpTest (leftPts x) (r k) (hr k) (hb1 k)), ∀ i, time (y i) ≤ T') ∧
        ∀ z ∈ tsupport (bumpTest (rightPts x) (r k) (hr k) (hb2 k)), ∀ j,
          T' + (τ - 2 * r k) ≤ time (z j) := by
      obtain ⟨T₀, hT₁, hT₂⟩ := hτ
      refine ⟨T₀ + r k, fun y hy i => ?_, fun z hz j => ?_⟩
      · have e2 : |time (y i) - time (x (Fin.castAdd n₂ i))| ≤ r k :=
          (abs_time_sub_le _ _).trans (hsupp1 y hy i)
        have := hT₁ i
        linarith [(abs_le.mp e2).2]
      · have e1 : |time (z j) - time (x (Fin.natAdd n₁ j))| ≤ r k :=
          (abs_time_sub_le _ _).trans (hsupp2 z hz j)
        have := hT₂ j
        linarith [(abs_le.mp e1).1]
    have hτk : δ / 2 ≤ τ - 2 * r k := by
      have := ((hrε k).le).trans hεδ
      linarith
    have h := smeared_connected_le T hW hU _ _ _ (τ - 2 * r k) hτk
      (fun y hy => hsepBox _ hsep₁ k y (hsupp1 y hy))
      (fun z hz => hsepBox _ hsep₂ k z (hsupp2 z hz)) htens hgap
    rw [integral_norm_bumpTest hn₁, integral_norm_bumpTest hn₂, mul_one, mul_one] at h
    exact h
  have hL := (hS.sub (hS₁.mul hS₂)).norm
  have hRt : Tendsto (fun k => K * Real.exp (-μ * (τ - 2 * r k))) atTop
      (𝓝 (K * Real.exp (-μ * τ))) := by
    have h1 : Tendsto (fun k => τ - 2 * r k) atTop (𝓝 (τ - 2 * 0)) :=
      tendsto_const_nhds.sub (hr0.const_mul 2)
    rw [mul_zero, sub_zero] at h1
    exact ((Real.continuous_exp.tendsto _).comp (h1.const_mul (-μ))).const_mul K
  exact le_of_tendsto_of_tendsto' hL hRt hbound

/-- **(i) The conditional transfer.** Under the floored (U) (`UniformDecayFrom`) for token groups
`w₁`, `w₂` of at least one token each, their convergence `Properties.wilson` and their smoothness
`smooth` at `none`: for every floor `δ > 0` and internal separation `ε > 0` there is a constant `K`
such that at every separated configuration `x` of `n₁ + n₂` points whose blocks keep their points
`ε` apart and whose second block lies at least `τ ≥ δ` after the first in time,
`‖S(x) − S(leftPts x) · S(rightPts x)‖ ≤ K e^{−μτ}`.
`K` is the constant of (U) at `δ/2`, `ε/2` (`connected_le_of_decayOn`).

DERIVED: `0` is the lower bound of the block sizes and of the floors; `2` halves the floors. -/
theorem connected_le_of_uniform {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C)
    (hR : ReconstructedFields T) {order : ℕ → ℕ}
    (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token}
    {μ : ℝ} (hU : UniformDecayFrom C order w₁ w₂ μ) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ x : Points (n₁ + n₂), x ∈ WilsonFamily.separated (n₁ + n₂) →
      PtsSep ε (leftPts x) → PtsSep ε (rightPts x) → ∀ τ : ℝ, δ ≤ τ →
      (∃ T : ℝ, (∀ i, time (x (Fin.castAdd n₂ i)) ≤ T) ∧ ∀ j, T + τ ≤ time (x (Fin.natAdd n₁ j))) →
      ‖T.correlation none (T.project ∘ Fin.append w₁ w₂) x
          - T.correlation none (T.project ∘ w₁) (leftPts x)
            * T.correlation none (T.project ∘ w₂) (rightPts x)‖
        ≤ K * Real.exp (-μ * τ) := by
  obtain ⟨K, hK⟩ := hU (δ / 2) (ε / 2) (by linarith) (by linarith)
  exact ⟨K, fun x hx h₁ h₂ τ hδτ hτ =>
    connected_le_of_decayOn T hR hW hn₁ hn₂ hδ hε hK x hx h₁ h₂ τ hδτ hτ⟩

/-! ## 7. The conditional identification -/

/-- The point `y` moved by `t` along the time axis.

DERIVED: `2` is the `L²` exponent. -/
noncomputable def timeShift (t : ℝ) (y : Spacetime) : Spacetime :=
  WithLp.toLp 2 fun a => y a + (Pi.single timeAxis t : Axis → ℝ) a

/-- `timeShift t` adds `t` to the time.

DERIVED: no numeral appears in the statement. -/
@[simp] theorem time_timeShift (t : ℝ) (y : Spacetime) : time (timeShift t y) = time y + t := by
  simp [time, timeShift]

/-- `timeShift t` is injective.

DERIVED: no numeral appears in the statement. -/
theorem timeShift_injective (t : ℝ) : Function.Injective (timeShift t) := fun u v h =>
  PiLp.ext fun a => by
    have h' := congrArg (fun w : Spacetime => w a) h
    simpa [timeShift] using h'

/-- Every point of a configuration moved by `t` along the time axis.

DERIVED: `2` is the `L²` exponent. -/
noncomputable def shiftPts {n : ℕ} (t : ℝ) (y : Points n) : Points n :=
  WithLp.toLp 2 fun i => timeShift t (y i)

/-- `shiftPts t y` at `i` is `timeShift t (y i)`.

DERIVED: no numeral appears in the statement. -/
@[simp] theorem shiftPts_apply {n : ℕ} (t : ℝ) (y : Points n) (i : Fin n) :
    shiftPts t y i = timeShift t (y i) := rfl

/-- An observable of their hierarchy: at least one tag, at a separated configuration.

DERIVED: `0` is the lower bound of the number of points. -/
structure Observable {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C) where
  n : ℕ
  pos : 0 < n
  tags : Fin n → T.Tag
  pts : Points n
  sep : pts ∈ WilsonFamily.separated n

/-- **Open input (U) for every pair of token groups**: each pair of groups of at least one token has
a rate `μ > 0` for which the floored (U) holds (`UniformDecayFrom`: a constant for every floor `δ > 0`
and internal separation `ε > 0`).

DERIVED: `0` is the lower bound of the group sizes and of the rate. -/
def UniformDecayAll {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) (order : ℕ → ℕ) : Prop :=
  ∀ {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token), 0 < n₁ → 0 < n₂ →
    ∃ μ : ℝ, 0 < μ ∧ UniformDecayFrom C order w₁ w₂ μ

/-- **Open input, component clustering**: in every component `ξ`, the correlation of `a` together
with `b` moved by `t` along the time axis tends to the product of the component values of `a` and `b`
as `t → ∞`. This is `hcomp` of `OpenAIBridgeLimits.component_eq_mixture_of_clusters`; it carries the
time-translation invariance of the components. Nothing public ties `correlation (some ξ)` to the
lattice.

DERIVED: no numeral appears in the statement. -/
def ComponentClustering {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C) : Prop :=
  ∀ (a b : Observable T) (ξ : T.Character),
    Tendsto (fun t => T.correlation (some ξ) (Fin.append a.tags b.tags)
        (appendPts a.pts (shiftPts t b.pts))) atTop
      (𝓝 (T.correlation (some ξ) a.tags a.pts * T.correlation (some ξ) b.tags b.pts))

/-- **Open input, a conjugation of observables**: `cj a` has, in every component, the complex
conjugate value of `a`. This is `hstar` of `OpenAIBridgeLimits.component_eq_mixture_of_clusters`;
their `adjointLabel` acts on Wightman labels of the selected component only.

DERIVED: no numeral appears in the statement. -/
def Conjugation {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C)
    (cj : Observable T → Observable T) : Prop :=
  ∀ (a : Observable T) (ξ : T.Character),
    T.correlation (some ξ) (cj a).tags (cj a).pts = conj (T.correlation (some ξ) a.tags a.pts)

/-- **Open input, a bound on the component products**: for each pair of observables, the component
values of `a` with `b` moved by `t` are bounded uniformly in the phase, for all large `t`. This is
`hbd` of `OpenAIBridgeLimits.component_eq_mixture_of_clusters`; `characterContinuity` bounds them at
each fixed `t` only.

DERIVED: no numeral appears in the statement. -/
def ComponentBound {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C) : Prop :=
  ∀ a b : Observable T, ∃ M : ℝ, ∀ᶠ t in atTop, ∀ ξ : T.Character,
    ‖T.correlation (some ξ) (Fin.append a.tags b.tags) (appendPts a.pts (shiftPts t b.pts))‖ ≤ M

/-- **Open input, time-translation invariance of the mixed correlation**: moving every point of an
observable by `t` along the time axis does not change `correlation none`. Nothing public states it.

DERIVED: no numeral appears in the statement. -/
def MixedTimeInvariance {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C) : Prop :=
  ∀ (a : Observable T) (t : ℝ), T.correlation none a.tags (shiftPts t a.pts)
    = T.correlation none a.tags a.pts

/-- `a` with `b` moved by `t` along the time axis is separated for all large `t`.

DERIVED: no numeral appears in the statement. -/
theorem eventually_pair_separated {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} {T : HierarchyFields C}
    (a b : Observable T) :
    ∀ᶠ t in atTop, appendPts a.pts (shiftPts t b.pts) ∈ WilsonFamily.separated (a.n + b.n) := by
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    eventually_gt_atTop (time (a.pts i) - time (b.pts j))] with t ht
  show Function.Injective (WithLp.ofLp (appendPts a.pts (shiftPts t b.pts)))
  intro u v huv
  induction u using Fin.addCases with
  | left i =>
    induction v using Fin.addCases with
    | left i' =>
      simp only [appendPts, WithLp.ofLp_toLp, Fin.append_left] at huv
      exact congrArg _ (a.sep huv)
    | right j' =>
      simp only [appendPts, shiftPts, WithLp.ofLp_toLp, Fin.append_left, Fin.append_right] at huv
      have h := congrArg time huv
      rw [time_timeShift] at h
      have := ht i j'
      exfalso
      linarith
  | right j =>
    induction v using Fin.addCases with
    | left i' =>
      simp only [appendPts, shiftPts, WithLp.ofLp_toLp, Fin.append_left, Fin.append_right] at huv
      have h := congrArg time huv
      rw [time_timeShift] at h
      have := ht i' j
      exfalso
      linarith
    | right j' =>
      simp only [appendPts, shiftPts, WithLp.ofLp_toLp, Fin.append_right] at huv
      exact congrArg _ (b.sep (timeShift_injective t huv))

/-- Moving two points by the same time does not change their distance.

DERIVED: no numeral appears in the statement. -/
theorem dist_timeShift (t : ℝ) (u v : Spacetime) : dist (timeShift t u) (timeShift t v) = dist u v := by
  simp [EuclideanSpace.dist_eq, timeShift]

/-- Moving a configuration along the time axis keeps its internal separation.

DERIVED: no numeral appears in the statement. -/
theorem PtsSep.shiftPts {n : ℕ} {ε : ℝ} {y : Points n} (h : PtsSep ε y) (t : ℝ) :
    PtsSep ε (shiftPts t y) := fun i i' hii => by
  rw [shiftPts_apply, shiftPts_apply, dist_timeShift]
  exact h i i' hii

/-- **The mixed theory clusters.** Under the floored (U) for the token groups of `a` and `b`,
`Properties.wilson`, `smooth`, `represents` and time-translation invariance of `correlation none`,
there is a constant `K` such that, for every `M` bounding the time differences of `a` and `b`, the
connected mixed correlation of `a` with `b` moved by `t` is at most `K e^{−μ(t − M)}` for all large
`t`. `represents` gives tokens for the tags; `exists_ptsSep` gives the internal separations of `a` and
`b` (kept by the time shift, `PtsSep.shiftPts`); `connected_le_of_uniform` at the floor `1` bounds the
connected part once `t − M ≥ 1`.

DERIVED: `1` is the time floor. -/
theorem mixed_clusters {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g} (T : HierarchyFields C)
    (hR : ReconstructedFields T) {order : ℕ → ℕ}
    (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    (htrans : MixedTimeInvariance T) (a b : Observable T) {μ : ℝ}
    (hU : UniformDecayFrom C order
        (fun i => Function.surjInv hR.represents (a.tags i))
        (fun j => Function.surjInv hR.represents (b.tags j)) μ) :
    ∃ K : ℝ, ∀ M : ℝ, (∀ i j, |time (b.pts j) - time (a.pts i)| ≤ M) →
      ∀ᶠ t in atTop,
      ‖T.correlation none (Fin.append a.tags b.tags) (appendPts a.pts (shiftPts t b.pts))
          - T.correlation none a.tags a.pts * T.correlation none b.tags b.pts‖
        ≤ K * Real.exp (-μ * (t - M)) := by
  obtain ⟨εa, hεa, hsa⟩ := exists_ptsSep a.sep
  obtain ⟨εb, hεb, hsb⟩ := exists_ptsSep b.sep
  obtain ⟨K, hK⟩ := connected_le_of_uniform T hR hW a.pos b.pos hU 1 (min εa εb) one_pos
    (lt_min hεa hεb)
  refine ⟨K, fun M hM => ?_⟩
  filter_upwards [eventually_pair_separated a b, eventually_ge_atTop (M + 1)] with t ht htM
  set w₁ : Fin a.n → C.Token := fun i => Function.surjInv hR.represents (a.tags i)
  set w₂ : Fin b.n → C.Token := fun j => Function.surjInv hR.represents (b.tags j)
  have hp₁ : T.project ∘ w₁ = a.tags := funext fun i => Function.surjInv_eq hR.represents (a.tags i)
  have hp₂ : T.project ∘ w₂ = b.tags := funext fun j => Function.surjInv_eq hR.represents (b.tags j)
  have h₁ : PtsSep (min εa εb) (leftPts (appendPts a.pts (shiftPts t b.pts))) := by
    rw [leftPts_appendPts]
    exact hsa.mono (min_le_left _ _)
  have h₂ : PtsSep (min εa εb) (rightPts (appendPts a.pts (shiftPts t b.pts))) := by
    rw [rightPts_appendPts]
    exact (hsb.mono (min_le_right _ _)).shiftPts t
  haveI : Nonempty (Fin a.n) := ⟨⟨0, a.pos⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i : Fin a.n => time (a.pts i))
  have hb := hK (appendPts a.pts (shiftPts t b.pts)) ht h₁ h₂ (t - M) (by linarith)
    ⟨time (a.pts i₀), fun i => by rw [appendPts_castAdd]; exact hi₀ i, fun j => by
      rw [appendPts_natAdd, shiftPts_apply, time_timeShift]
      have h1 := hM i₀ j
      have h2 := neg_abs_le (time (b.pts j) - time (a.pts i₀))
      linarith⟩
  rw [comp_finAppend, hp₁, hp₂, leftPts_appendPts, rightPts_appendPts, htrans b t] at hb
  exact hb

/-- **(ii) The conditional identification.** Under their `Properties.wilson` and the fields of
`Reconstructed` restated in `ReconstructedFields`, and the five open inputs — (U) for every pair of
token groups (`UniformDecayAll`), component clustering (`ComponentClustering`), a conjugation of
observables (`Conjugation`), a bound on the component products (`ComponentBound`) and
time-translation invariance of `correlation none` (`MixedTimeInvariance`) — every component equals
the mixture: `correlation (some ξ) a x = correlation none a x` at every separated configuration `x`
of at least one point, for every phase `ξ`.

The mixed theory clusters (`mixed_clusters`, from (i)), and
`OpenAIBridgeLimits.component_eq_mixture_of_clusters` with their `characterContinuity`, `mixture`,
`normalized` and `fullSupport` concludes; off the eventually separated range the product values are
read as zero, which no limit sees.

DERIVED: `0` is the lower bound of the number of points. -/
theorem component_eq_mixture_of_uniform {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    (T : HierarchyFields C) (hR : ReconstructedFields T) {order : ℕ → ℕ}
    (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    (hU : UniformDecayAll C order) (hcomp : ComponentClustering T)
    (cj : Observable T → Observable T) (hstar : Conjugation T cj) (hbd : ComponentBound T)
    (htrans : MixedTimeInvariance T) :
    ∀ (ξ : T.Character) {n : ℕ} (a : Fin n → T.Tag) (x : Points n), 0 < n →
      x ∈ WilsonFamily.separated n → T.correlation (some ξ) a x = T.correlation none a x := by
  classical
  haveI := hR.normalized
  haveI := hR.fullSupport
  let F : Observable T → Observable T → ℝ → T.Character → ℂ := fun a b t ξ =>
    if appendPts a.pts (shiftPts t b.pts) ∈ WilsonFamily.separated (a.n + b.n) then
      T.correlation (some ξ) (Fin.append a.tags b.tags) (appendPts a.pts (shiftPts t b.pts))
    else 0
  let Fmix : Observable T → Observable T → ℝ → ℂ := fun a b t =>
    if appendPts a.pts (shiftPts t b.pts) ∈ WilsonFamily.separated (a.n + b.n) then
      T.correlation none (Fin.append a.tags b.tags) (appendPts a.pts (shiftPts t b.pts))
    else 0
  have hmeas : ∀ a b, ∀ᶠ t in (atTop : Filter ℝ), AEStronglyMeasurable (F a b t) T.phaseMeasure :=
    fun a b => Filter.Eventually.of_forall fun t => by
      by_cases h : appendPts a.pts (shiftPts t b.pts) ∈ WilsonFamily.separated (a.n + b.n)
      · simp only [F, if_pos h]
        exact (hR.characterContinuity _ _ h).aestronglyMeasurable
      · simp only [F, if_neg h]
        exact aestronglyMeasurable_const
  have hbd' : ∀ a b, ∀ᶠ t in (atTop : Filter ℝ), ∀ ξ, ‖F a b t ξ‖ ≤ (hbd a b).choose :=
    fun a b => by
      filter_upwards [(hbd a b).choose_spec, eventually_pair_separated a b] with t h hs ξ
      simp only [F, if_pos hs]
      exact h ξ
  have hcomp' : ∀ a b ξ, Tendsto (fun t => F a b t ξ) atTop
      (𝓝 (T.correlation (some ξ) a.tags a.pts * T.correlation (some ξ) b.tags b.pts)) :=
    fun a b ξ => (hcomp a b ξ).congr' (by
      filter_upwards [eventually_pair_separated a b] with t hs
      simp only [F, if_pos hs])
  have hFmix : ∀ a b t, ∫ ξ, F a b t ξ ∂T.phaseMeasure = Fmix a b t := fun a b t => by
    by_cases h : appendPts a.pts (shiftPts t b.pts) ∈ WilsonFamily.separated (a.n + b.n)
    · simp only [F, Fmix, if_pos h]
      exact hR.mixture _ _ h
    · simp only [F, Fmix, if_neg h, integral_zero]
  have hclust : ∀ a b, Tendsto (Fmix a b) atTop
      (𝓝 (T.correlation none a.tags a.pts * T.correlation none b.tags b.pts)) := by
    intro a b
    obtain ⟨μ, hμ, hUab⟩ := hU (fun i => Function.surjInv hR.represents (a.tags i))
      (fun j => Function.surjInv hR.represents (b.tags j)) a.pos b.pos
    obtain ⟨K, hK⟩ := mixed_clusters T hR hW htrans a b hUab
    obtain ⟨M, hM⟩ := (Set.finite_range fun q : Fin a.n × Fin b.n =>
      |time (b.pts q.2) - time (a.pts q.1)|).bddAbove
    have hM' : ∀ i j, |time (b.pts j) - time (a.pts i)| ≤ M := fun i j => hM ⟨(i, j), rfl⟩
    have h0 : Tendsto (fun t : ℝ => t - M) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-M) tendsto_id).congr fun t => (sub_eq_add_neg t M).symm
    have h1 : Tendsto (fun t : ℝ => -μ * (t - M)) atTop atBot := by
      have h2 := tendsto_neg_atTop_atBot.comp (h0.const_mul_atTop hμ)
      refine h2.congr fun t => ?_
      simp only [Function.comp_apply, neg_mul]
    have hdecay : Tendsto (fun t : ℝ => K * Real.exp (-μ * (t - M))) atTop (𝓝 0) := by
      have h3 := (Real.tendsto_exp_atBot.comp h1).const_mul K
      rw [mul_zero] at h3
      exact h3
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hdecay
    filter_upwards [hK M hM', eventually_pair_separated a b]
      with t h hs
    simp only [Fmix, if_pos hs]
    exact h
  have key := OpenAIBridgeLimits.component_eq_mixture_of_clusters (ν := T.phaseMeasure)
    (l := (atTop : Filter ℝ)) (fun s (a : Observable T) => T.correlation s a.tags a.pts) cj
    (fun a => hR.characterContinuity a.tags a.pts a.sep) (fun a => hR.mixture a.tags a.pts a.sep)
    hstar F Fmix (fun a b => (hbd a b).choose) (fun a b => hmeas a b) hbd' hcomp' hFmix hclust
  intro ξ n a x hn hx
  exact key ⟨n, hn, a, x, hx⟩ ξ


/-! ## 8. Why (U) carries floors -/

/-- Two points on the time axis at `−r/2` and `r/2`. Restated from the OpenAI submission,
`ChallengeSpec.lean:145–147` (`timePair`).

DERIVED: `2` halves the separation and is the `L²` exponent; `3` the spatial axes; `0` the spatial
coordinates; `1` the size of each block of `Fin.append`. -/
noncomputable def timePair (r : ℝ) : Points 2 :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 (Fin.snoc (fun _ : Fin 3 => (0:ℝ))
    (Fin.append (fun _ : Fin 1 => -(r/2)) (fun _ : Fin 1 => r/2) i))

/-- The time of the points of `timePair r`.

DERIVED: `2` halves the separation; `1` the size of each block of `Fin.append`. -/
theorem time_timePair (r : ℝ) (i : Fin 2) :
    time (timePair r i) = Fin.append (fun _ : Fin 1 => -(r/2)) (fun _ : Fin 1 => r/2) i := by
  rfl

/-- `timePair r` is separated for `r ≠ 0`.

DERIVED: `0` is the excluded separation; `2` the number of points. -/
theorem timePair_mem {r : ℝ} (hr : r ≠ 0) : timePair r ∈ WilsonFamily.separated 2 := by
  intro i j h
  have ht := congrArg time (show timePair r i = timePair r j from h)
  rw [time_timePair, time_timePair] at ht
  fin_cases i <;> fin_cases j
  · rfl
  · change -(r/2) = r/2 at ht
    exact absurd (by linarith : r = 0) hr
  · change r/2 = -(r/2) at ht
    exact absurd (by linarith : r = 0) hr
  · rfl

/-- Every configuration of one point is separated.

DERIVED: `1` is the number of points. -/
theorem mem_separated_one (y : Points 1) : y ∈ WilsonFamily.separated 1 :=
  fun i j _ => Subsingleton.elim i j

/-- `r ↦ leftPts (timePair r)` and `r ↦ rightPts (timePair r)` are continuous.

DERIVED: `1` is the size of each block. -/
theorem continuous_blocks_timePair :
    Continuous (fun r : ℝ => leftPts (n₁ := 1) (n₂ := 1) (timePair r)) ∧
      Continuous (fun r : ℝ => rightPts (n₁ := 1) (n₂ := 1) (timePair r)) := by
  have hc : ∀ i : Fin 2, Continuous (fun r : ℝ => timePair r i) := by
    intro i
    fin_cases i <;>
    · refine (PiLp.continuous_toLp _ _).comp (continuous_pi fun a => ?_)
      fin_cases a
      · show Continuous fun _ : ℝ => (0:ℝ)
        exact continuous_const
      · show Continuous fun _ : ℝ => (0:ℝ)
        exact continuous_const
      · show Continuous fun _ : ℝ => (0:ℝ)
        exact continuous_const
      · first
        | (show Continuous fun r : ℝ => -(r/2); fun_prop)
        | (show Continuous fun r : ℝ => r/2; fun_prop)
  constructor
  · exact (PiLp.continuous_toLp _ _).comp (continuous_pi fun i => hc _)
  · exact (PiLp.continuous_toLp _ _).comp (continuous_pi fun i => hc _)

/-- `r⁸ log²(1/r) → 0` as `r → 0⁺`.

DERIVED: `8` and `2` are the exponents of their `shortDistance`; `4` is half of `8`; `0` the limit
point. -/
theorem tendsto_shortDistance_weight :
    Tendsto (fun r : ℝ => r ^ 8 * (Real.log r⁻¹) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 4) (by norm_num)).pow 2
  rw [zero_pow two_ne_zero] at h
  refine h.congr fun r => ?_
  have h4 : r ^ (4:ℝ) = r ^ (4:ℕ) := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [h4, Real.log_inv]
  ring

/-- **The unfloored (U) is refuted by their short-distance law.** Let `v` be a token and `sel` a
component, and suppose:
* the unfloored (U) for `v` against itself (`UniformDecayUnfloored`, one constant `K` for every
  time gap and every test);
* the identification of the component `sel` with `correlation none` on `timePair r`, `r > 0` (what
  `component_eq_mixture_of_uniform` delivers at `sel`);
* the short-distance law of their `TraceTest.shortDistance` (`ChallengeSpec.lean:173`), restated
  for `v`: `r⁸ log²(1/r) · S_sel(v, v)(timePair r) → A` as `r → 0⁺`, with `A ≠ 0` (their
  `A = 3 dim g / π⁴ > 0` by `amplitudePositive`, for `v` a token of `centeredTrace`).

Then `False`. The unfloored (U) gives `DecayOn` at every floor with the same `K`
(`UniformDecayUnfloored.decayOn`); `connected_le_of_decayOn` at `timePair r` (blocks of one point,
time gap `r`) bounds the connected two-point function by `K e^{−μr}` for every `r > 0`. The one-point
functions are continuous (`smooth`, every configuration of one point is separated), hence bounded near
`r = 0`. So `S_sel(timePair r)` is bounded near `0⁺`, and `r⁸ log²(1/r) · S_sel → 0 ≠ A`.

DERIVED: `8` and `2` are the exponents of their `shortDistance`; `0` the limit point and the excluded
value of `A`; `1` the size of each block and the radius of the neighbourhood; `2` the number of
points and the halved floors. -/
theorem unfloored_contradicts_shortDistance {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    (T : HierarchyFields C) (hR : ReconstructedFields T) {order : ℕ → ℕ}
    (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    (v : C.Token) (sel : T.Character) {K μ : ℝ} {A : ℂ}
    (hU : UniformDecayUnfloored C order (fun _ : Fin 1 => v) (fun _ : Fin 1 => v) K μ)
    (hid : ∀ r : ℝ, 0 < r → T.correlation (some sel) (fun _ : Fin 2 => T.project v) (timePair r)
      = T.correlation none (fun _ : Fin 2 => T.project v) (timePair r))
    (hshort : Tendsto (fun r : ℝ => (r ^ 8 * (Real.log r⁻¹) ^ 2) •
      T.correlation (some sel) (fun _ : Fin 2 => T.project v) (timePair r)) (𝓝[>] 0) (𝓝 A))
    (hA : A ≠ 0) : False := by
  set f₁ : ℝ → ℂ := fun r => T.correlation none (T.project ∘ fun _ : Fin 1 => v)
    (leftPts (n₁ := 1) (n₂ := 1) (timePair r))
  set f₂ : ℝ → ℂ := fun r => T.correlation none (T.project ∘ fun _ : Fin 1 => v)
    (rightPts (n₁ := 1) (n₂ := 1) (timePair r))
  have hone : ContinuousOn (T.correlation none (T.project ∘ fun _ : Fin 1 => v))
      (WilsonFamily.separated 1) := (hR.smooth none _).continuousOn
  have hca : ∀ y : Points 1,
      ContinuousAt (T.correlation none (T.project ∘ fun _ : Fin 1 => v)) y := fun y =>
    hone.continuousAt ((WilsonFamily.separated 1).isOpen.mem_nhds (mem_separated_one y))
  have hf₁ : ContinuousAt f₁ 0 :=
    (hca _).comp continuous_blocks_timePair.1.continuousAt
  have hf₂ : ContinuousAt f₂ 0 :=
    (hca _).comp continuous_blocks_timePair.2.continuousAt
  have hb₁ : ∀ᶠ r in 𝓝 (0:ℝ), ‖f₁ r‖ < ‖f₁ 0‖ + 1 :=
    hf₁.norm.eventually (gt_mem_nhds (by linarith))
  have hb₂ : ∀ᶠ r in 𝓝 (0:ℝ), ‖f₂ r‖ < ‖f₂ 0‖ + 1 :=
    hf₂.norm.eventually (gt_mem_nhds (by linarith))
  have hcomp : T.project ∘ Fin.append (fun _ : Fin 1 => v) (fun _ : Fin 1 => v)
      = fun _ : Fin 2 => T.project v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · show T.project (Fin.append (fun _ : Fin 1 => v) (fun _ : Fin 1 => v) (Fin.castAdd 1 j)) = _
      rw [Fin.append_left]
    · show T.project (Fin.append (fun _ : Fin 1 => v) (fun _ : Fin 1 => v) (Fin.natAdd 1 j)) = _
      rw [Fin.append_right]
  have hconn : ∀ r : ℝ, 0 < r →
      ‖T.correlation none (fun _ : Fin 2 => T.project v) (timePair r) - f₁ r * f₂ r‖
        ≤ K * Real.exp (-μ * r) := by
    intro r hr
    have h := connected_le_of_decayOn T hR hW (n₁ := 1) (n₂ := 1) one_pos one_pos hr one_pos
      (hU.decayOn (r / 2) (1 / 2)) (timePair r) (timePair_mem hr.ne')
      (fun i i' hii => absurd (Subsingleton.elim i i') hii)
      (fun i i' hii => absurd (Subsingleton.elim i i') hii) r le_rfl
      ⟨-(r / 2), fun i => le_of_eq (by rw [time_timePair, Fin.append_left]),
        fun j => by rw [time_timePair, Fin.append_right]; linarith⟩
    rw [hcomp] at h
    exact h
  set B : ℝ := |K| * Real.exp |μ| + (‖f₁ 0‖ + 1) * (‖f₂ 0‖ + 1)
  have hbd : ∀ᶠ r in 𝓝[>] (0:ℝ),
      ‖T.correlation (some sel) (fun _ : Fin 2 => T.project v) (timePair r)‖ ≤ B := by
    have h1 : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, h1, nhdsWithin_le_nhds hb₁, nhdsWithin_le_nhds hb₂]
      with r hr hr1 h₁ h₂
    have hr0 : 0 < r := hr
    rw [hid r hr0]
    have hc := hconn r hr0
    have hexp : Real.exp (-μ * r) ≤ Real.exp |μ| := by
      apply Real.exp_le_exp.2
      have h3 : -μ * r ≤ |μ| * r := mul_le_mul_of_nonneg_right (neg_le_abs μ) hr0.le
      have h4 : |μ| * r ≤ |μ| := mul_le_of_le_one_right (abs_nonneg μ) hr1.le
      linarith
    have hK : K * Real.exp (-μ * r) ≤ |K| * Real.exp |μ| :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left hexp (abs_nonneg K))
    have hprod : ‖f₁ r * f₂ r‖ ≤ (‖f₁ 0‖ + 1) * (‖f₂ 0‖ + 1) := by
      rw [norm_mul]
      exact mul_le_mul h₁.le h₂.le (norm_nonneg _) (by positivity)
    calc ‖T.correlation none (fun _ : Fin 2 => T.project v) (timePair r)‖
        = ‖(T.correlation none (fun _ : Fin 2 => T.project v) (timePair r) - f₁ r * f₂ r)
            + f₁ r * f₂ r‖ := by rw [sub_add_cancel]
      _ ≤ ‖T.correlation none (fun _ : Fin 2 => T.project v) (timePair r) - f₁ r * f₂ r‖
            + ‖f₁ r * f₂ r‖ := norm_add_le _ _
      _ ≤ B := add_le_add (hc.trans hK) hprod
  have hw := tendsto_shortDistance_weight
  have h0 : Tendsto (fun r : ℝ => (r ^ 8 * (Real.log r⁻¹) ^ 2) •
      T.correlation (some sel) (fun _ : Fin 2 => T.project v) (timePair r)) (𝓝[>] 0) (𝓝 0) := by
    have hw' : Tendsto (fun r : ℝ => r ^ 8 * (Real.log r⁻¹) ^ 2 * B) (𝓝[>] 0) (𝓝 0) := by
      simpa using hw.mul_const B
    refine squeeze_zero_norm' ?_ hw'
    filter_upwards [hbd] with r hr
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  exact hA (tendsto_nhds_unique hshort h0)

end MassGap.OpenAILink

#print axioms MassGap.OpenAILink.appendPts_castAdd
#print axioms MassGap.OpenAILink.appendPts_natAdd
#print axioms MassGap.OpenAILink.leftPts_appendPts
#print axioms MassGap.OpenAILink.rightPts_appendPts
#print axioms MassGap.OpenAILink.leftPts_mem_separated
#print axioms MassGap.OpenAILink.rightPts_mem_separated
#print axioms MassGap.OpenAILink.comp_finAppend
#print axioms MassGap.OpenAILink.abs_time_sub_le
#print axioms MassGap.OpenAILink.integral_pointsOne
#print axioms MassGap.OpenAILink.integral_split_mul
#print axioms MassGap.OpenAILink.integral_prod_coord
#print axioms MassGap.OpenAILink.isCompact_coordBox
#print axioms MassGap.OpenAILink.bumpFun_nonneg
#print axioms MassGap.OpenAILink.dist_lt_of_bumpFun_ne_zero
#print axioms MassGap.OpenAILink.bumpFun_eq_zero_of_not_mem
#print axioms MassGap.OpenAILink.contDiff_bumpFun
#print axioms MassGap.OpenAILink.continuous_bumpFun
#print axioms MassGap.OpenAILink.hasCompactSupport_bumpFun
#print axioms MassGap.OpenAILink.tsupport_bumpFun_subset
#print axioms MassGap.OpenAILink.integrable_bumpFun
#print axioms MassGap.OpenAILink.integral_bumpFun
#print axioms MassGap.OpenAILink.bumpTest_apply
#print axioms MassGap.OpenAILink.integral_norm_bumpTest
#print axioms MassGap.OpenAILink.integrable_bump_mul
#print axioms MassGap.OpenAILink.exists_coord_nhds
#print axioms MassGap.OpenAILink.tendsto_integral_bump
#print axioms MassGap.OpenAILink.tendsto_bump_integral
#print axioms MassGap.OpenAILink.bumpFun_split
#print axioms MassGap.OpenAILink.exists_ptsSep
#print axioms MassGap.OpenAILink.PtsSep.mono
#print axioms MassGap.OpenAILink.DecayOn.of_eventually_forall
#print axioms MassGap.OpenAILink.UniformDecayUnfloored.decayOn
#print axioms MassGap.OpenAILink.smeared_connected_le
#print axioms MassGap.OpenAILink.connected_le_of_decayOn
#print axioms MassGap.OpenAILink.connected_le_of_uniform
#print axioms MassGap.OpenAILink.time_timeShift
#print axioms MassGap.OpenAILink.timeShift_injective
#print axioms MassGap.OpenAILink.shiftPts_apply
#print axioms MassGap.OpenAILink.eventually_pair_separated
#print axioms MassGap.OpenAILink.dist_timeShift
#print axioms MassGap.OpenAILink.PtsSep.shiftPts
#print axioms MassGap.OpenAILink.mixed_clusters
#print axioms MassGap.OpenAILink.component_eq_mixture_of_uniform
#print axioms MassGap.OpenAILink.time_timePair
#print axioms MassGap.OpenAILink.timePair_mem
#print axioms MassGap.OpenAILink.mem_separated_one
#print axioms MassGap.OpenAILink.continuous_blocks_timePair
#print axioms MassGap.OpenAILink.tendsto_shortDistance_weight
#print axioms MassGap.OpenAILink.unfloored_contradicts_shortDistance
