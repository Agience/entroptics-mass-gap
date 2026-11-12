import Mathlib
import MassGap.OpenAILink
import MassGap.OpenAIBridgeGap

/-!
# MassGap.OpenAISemigroup — the Euclidean semigroup of their Wightman theory, and its gap

The OpenAI submission `yang-mills-group/OpenAI-YM-20261028` (commit `3456e5e`, Lean 4.32, not
importable here at Lean 4.31) states its Wightman theory through public fields
(`PublicTheory.lean:255–321`): a Hilbert space, fields on a dense domain with a cyclic unit vacuum,
a unitary translation group, and a projection-valued energy–momentum measure `E` tied to the
translations by the spectral representation and supported in the closed forward cone. Its
`Reconstructed` names no Euclidean time semigroup. This module builds one from those fields alone and
connects it to `OpenAIBridgeGap`.

## Their definitions, restated (section 1)

`SpaceAxis`, `Space`, `spatial`, `forwardCone`, `TestFunction` (`PublicTheory.lean:52–70`);
`FieldSystem` and `FieldSystem.vector` (`:105–118`); `TranslationAction` (`:169–177`);
`EnergyMomentumMeasure` (`:180–200`). Of `PoincareAction` (`:219–246`) the three fields read here
are restated as `PoincareFields`, of `WightmanTheory` (`:255–262`) the four fields and the compatibility
read here as `WightmanFields`, and of W0, W1 and W2 (`:270–307`) the seven axioms read here as
`AxiomFields`. `Spacetime` and `time` are those of `OpenAILink`.

## The functional calculus of `E` (sections 2–5)

Mathlib has no integral against a projection-valued measure; it is built here for bounded measurable
real functions `h` with `|h| ≤ 1` (`UnitBounded`). For a vector `u` let `ν u = E.diagonal u`, a finite
measure with `ν u (A) = ⟪u, E A u⟫`.

* `simpleOp`: for a simple function `s`, `Σ_c c E(s⁻¹{c})`; `inner_simpleOp_self` gives
  `⟪u, simpleOp s u⟫ = ∫ s dν u`.
* `form h u v`: the polarization of `u ↦ ∫ h dν u`. Along the simple approximants `approx` of `h`,
  `⟪u, simpleOp (approx n) v⟫ → form h u v` by dominated convergence (`tendsto_form_approx`), so
  `form h` is sesquilinear as a pointwise limit of sesquilinear forms, and `|form h u v| ≤ 2 ‖u‖ ‖v‖`.
* `op h`: the operator of `form h` (`InnerProductSpace.continuousLinearMapOfBilin`), with
  `⟪u, op h v⟫ = form h u v` and `⟪u, op h u⟫ = ∫ h dν u`; self-adjoint (`op_sa`).
* `op_proj`: `op h ∘ E B = op (1_B h)`, from `E B (op h) E B = op (1_B h)` (the diagonal of `E B u`
  is `ν u` restricted to `B`, `diagonal_proj`) and `E B + E Bᶜ = 1`.
* `op_mul`: `op f ∘ op g = op (f g)`. For simple `g` it is `op_proj` summed (`op_simpleOp`); in
  general `op g` is the weak limit of `op (approx n)` and `op (f · approx n)` converges weakly to
  `op (f g)`.
* `norm_op_apply_sq`: `‖op h u‖² = ∫ h² dν u`, so `‖op h‖ ≤ 1`.

## The semigroup (section 6)

`euclid t = op (p ↦ e^{−t⁺ p₀⁺})` with `p₀ = time p` and `x⁺ = max x 0`; on the support of `E`, the
forward cone, `p₀⁺ = p₀`, and for `t ≥ 0` this is `∫ e^{−t p₀} dE`. `euclid_zero` (`S 0 = 1`),
`euclid_add` (`S (s + t) = S s S t`, `s, t ≥ 0`), `euclid_sa`, `norm_euclid_le` (`‖S t‖ ≤ 1`).
With the vacuum: the spectral representation and translation invariance give
`ν Ω = δ₀` (`diagonal_eq_dirac`, `Measure.ext_of_charFun`), hence `op_fix`: `S t Ω = Ω`.

## The gap (section 7)

`diagonal_lt_null`: a vector with `‖S t u‖ ≤ e^{−m t} ‖u‖` at every `t ≥ 0` has `ν u {p₀ < m} = 0`.
On `{p₀ ≤ c}` with `0 ≤ c < m`, `e^{−2tc} ν u {p₀ ≤ c} ≤ ‖S t u‖² ≤ e^{−2mt} ‖u‖²` for every `t`; below
`p₀ = 0` the forward cone carries no weight (`positiveEnergy`). Hence `proj_gap`: decay on the vacuum
complement gives `E{0 < p₀ < m} = 0` on the whole space, and `proj_low`: for `m > 0`,
`E{p₀ < m} u = ⟪Ω, u⟫ Ω`, the spectrum of `H` on the vacuum complement in `[m, ∞)`.

`proj_zeroEnergy`, with `uniqueVacuum` and no further input: `E{p₀ ≤ 0} u = ⟪Ω, u⟫ Ω`. A vector in
that spectral subspace has its measure at `p = 0` (the cone meets `{p₀ ≤ 0}` only there), so the
spectral representation makes it translation invariant, and `uniqueVacuum` puts it on the vacuum line:
the zero-energy subspace of their theory is the vacuum line.

## Their theory (section 8)

On `WightmanFields` with `AxiomFields`: `euclid_zero`, `euclid_add`, `euclid_sa`, `euclid_vacuum`,
`norm_euclid_le` are the hypotheses of `OpenAIBridgeGap.gap_of_cluster_time` other than clustering,
and `dense_span_fieldVectors` (W1: the field vectors span the dense domain) is its density hypothesis.
`EuclideanClustering` is the remaining one, named: the connected readings `⟪v, S t w⟫ − ⟪v, Ω⟫⟪Ω, w⟫`
of their field vectors decay as `C e^{−m t}`. Given it, `gap_of_clustering`,
`spectralGap_of_clustering` (`E{0 < p₀ < m} = 0`), `lowEnergy_of_clustering`, and the generator
statements `hamiltonian_gap_of_clustering`, `hamiltonian_ker_of_clustering`.

## Scope

Built from public fields: the semigroup, its properties, the vacuum invariance, the passage from decay
to the spectral gap, and the zero-energy subspace. Not public, and open here as `EuclideanClustering`:
that the readings `⟪v, S t w⟫` of their field vectors are the Euclidean values of
`correlation (some selected)` (the Osterwalder–Schrader link, their internal reconstruction) and
that those decay. This module does not attempt it.
-/

namespace MassGap.OpenAISemigroup

open MeasureTheory Filter Topology Set
open scoped Function
open MassGap.OpenAILink (Spacetime time timeAxis abs_time_sub_le)

/-! ## 1. Their definitions, restated -/

/-- Their spatial axes. Restated from `PublicTheory.lean:52` (`SpaceAxis := Fin 3`).

DERIVED: `3` is the number of spatial axes of `Fin 4`. -/
abbrev SpaceAxis := Fin 3

/-- Their space. Restated from `PublicTheory.lean:55` (`Space := EuclideanSpace ℝ SpaceAxis`).

DERIVED: no numeral appears in the statement. -/
abbrev Space := EuclideanSpace ℝ SpaceAxis

/-- The spatial part of a point. Restated from `PublicTheory.lean:59–60`
(`spatial x := WithLp.toLp 2 fun i ↦ x i.castSucc`).

DERIVED: `2` is the `L²` exponent. -/
noncomputable def spatial (x : Spacetime) : Space :=
  WithLp.toLp 2 fun i ↦ x i.castSucc

/-- The closed forward light cone, time last. Restated from `PublicTheory.lean:64`
(`forwardCone := {x | ‖spatial x‖ ≤ time x}`).

DERIVED: no numeral appears in the statement. -/
def forwardCone : Set Spacetime := {x | ‖spatial x‖ ≤ time x}

/-- Their test functions. Restated from `PublicTheory.lean:70`
(`TestFunction := SchwartzMap Spacetime ℂ`).

DERIVED: no numeral appears in the statement. -/
abbrev TestFunction := SchwartzMap Spacetime ℂ

/-- Operator-valued tempered fields on one common domain. Restated from `PublicTheory.lean:105–109`;
their `HilbertSpace` and `FieldLabels` (`:79`, `:96`) are the type classes on `H` and `L`.

DERIVED: no numeral appears in the statement. -/
structure FieldSystem (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Type) [AddCommGroup L] [Module ℂ L] where
  domain : Submodule ℂ H
  vacuum : domain
  field : L →ₗ[ℂ] TestFunction →ₗ[ℂ] (domain →ₗ[ℂ] domain)

/-- The vector of a word of smeared fields applied to the vacuum. Restated from
`PublicTheory.lean:115–118`.

DERIVED: no numeral appears in the statement. -/
noncomputable def FieldSystem.vector {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {L : Type} [AddCommGroup L] [Module ℂ L] (F : FieldSystem H L) :
    List (L × TestFunction) → F.domain
  | [] => F.vacuum
  | letter :: word => F.field letter.1 letter.2 (F.vector word)

/-- A strongly continuous unitary representation of translations. Restated from
`PublicTheory.lean:169–177`.

DERIVED: `0` is the origin. -/
structure TranslationAction (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  operator : Spacetime → H →L[ℂ] H
  identity : operator 0 = ContinuousLinearMap.id ℂ _
  add (x y : Spacetime) : (operator x).comp (operator y) = operator (x + y)
  unitary (x : Spacetime) (state : H) : ‖operator x state‖ = ‖state‖
  stronglyContinuous (state : H) : Continuous fun x ↦ operator x state

/-- A projection-valued joint energy–momentum measure. Restated from `PublicTheory.lean:180–200`.

DERIVED: `0` is the zero operator. -/
structure EnergyMomentumMeasure (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  projection : Set Spacetime → H →L[ℂ] H
  empty : projection ∅ = 0
  univ : projection Set.univ = ContinuousLinearMap.id ℂ _
  intersection {left right : Set Spacetime} :
    MeasurableSet left → MeasurableSet right →
      (projection left).comp (projection right) = projection (left ∩ right)
  selfAdjoint {region : Set Spacetime} :
    MeasurableSet region → (projection region).adjoint = projection region
  countablyAdditive (regions : ℕ → Set Spacetime)
      (measurable : ∀ i, MeasurableSet (regions i))
      (disjoint : Pairwise (Disjoint on regions)) (state : H) :
    HasSum (fun i ↦ projection (regions i) state) (projection (⋃ i, regions i) state)
  diagonal : H → Measure Spacetime
  finite (state : H) : IsFiniteMeasure (diagonal state)
  diagonalIdentity {region : Set Spacetime} (measurable : MeasurableSet region) (state : H) :
    ↑((diagonal state).real region) = inner ℂ state (projection region state)

attribute [instance] EnergyMomentumMeasure.finite

/-- The fields of their `PoincareAction` (`PublicTheory.lean:219–246`) read here: `Symmetry`
(`:220`), `onStates` (`:224`) and `pureTranslation` (`:227`).

DERIVED: no numeral appears in the statement. -/
structure PoincareFields (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  Symmetry : Type
  onStates : Symmetry → H →L[ℂ] H
  pureTranslation : Spacetime → Symmetry

/-- The fields of their `WightmanTheory` (`PublicTheory.lean:255–262`) read here: `fields`,
`translations`, `energyMomentum`, `poincare` (its fields `PoincareFields`) and
`translationCompatibility`. `adjointLabel` is not read.

DERIVED: no numeral appears in the statement. -/
structure WightmanFields (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Type) [AddCommGroup L] [Module ℂ L] where
  fields : FieldSystem H L
  translations : TranslationAction H
  energyMomentum : EnergyMomentumMeasure H
  poincare : PoincareFields H
  translationCompatibility (x : Spacetime) :
    poincare.onStates (poincare.pureTranslation x) = translations.operator x

/-- The axioms of their `WightmanTheory.Axioms` read here, with their names: from W0
(`PublicTheory.lean:270–278`) `spectralRepresentation`, `positiveEnergy`, `uniqueVacuum`; from W1's
`DomainAxioms` (`:127–131`) `normalizedVacuum`, `denseDomain`, `cyclicVacuum`; from W2 (`:297–299`)
`vacuumInvariant`. Every proof of their `Axioms` carries these.

DERIVED: `1` is the unit norm of the vacuum; `0` the zero operator. -/
structure AxiomFields {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {L : Type} [AddCommGroup L] [Module ℂ L] (T : WightmanFields H L) : Prop where
  spectralRepresentation : ∀ state : H, ∀ momentum : Spacetime,
    charFun (T.energyMomentum.diagonal state) momentum =
      inner ℂ state (T.translations.operator momentum state)
  positiveEnergy : T.energyMomentum.projection forwardConeᶜ = 0
  uniqueVacuum (state : H) :
    (∀ x, T.translations.operator x state = state) →
      ∃ scalar : ℂ, scalar • T.fields.vacuum.1 = state
  normalizedVacuum : ‖T.fields.vacuum.1‖ = 1
  denseDomain : Dense (T.fields.domain : Set H)
  cyclicVacuum : T.fields.domain =
    Submodule.span ℂ (Set.range fun word ↦ (T.fields.vector word).1)
  vacuumInvariant (g : T.poincare.Symmetry) :
    T.poincare.onStates g T.fields.vacuum.1 = T.fields.vacuum.1

/-! ## 2. Geometry of the cone, and bounded weights -/

/-- The time coordinate is continuous (it is `1`-Lipschitz, `OpenAILink.abs_time_sub_le`).

DERIVED: `1` is the Lipschitz constant, in the proof only. -/
theorem continuous_time : Continuous time :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun u v => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul]; exact abs_time_sub_le u v).continuous

/-- The spatial part is continuous.

DERIVED: no numeral appears in the statement. -/
theorem continuous_spatial : Continuous spatial := by
  unfold spatial; fun_prop

/-- The forward cone is measurable (it is closed).

DERIVED: no numeral appears in the statement. -/
theorem measurableSet_forwardCone : MeasurableSet forwardCone :=
  measurableSet_le (continuous_norm.comp continuous_spatial).measurable continuous_time.measurable

/-- The origin has time `0`.

DERIVED: `0` is the origin and its time. -/
theorem time_zero : time 0 = 0 := by
  simp [OpenAILink.time]

/-- A point with zero spatial part and zero time is the origin.

DERIVED: `0` is the origin, the zero spatial vector and the zero time. -/
theorem eq_zero_of_spatial_time {p : Spacetime} (hs : spatial p = 0) (ht : time p = 0) : p = 0 := by
  refine PiLp.ext fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    show p timeAxis = (0 : Spacetime) timeAxis
    rw [show p timeAxis = 0 from ht]
    simp
  | cast j =>
    have h := congrArg (fun v : Space => v j) hs
    simpa [spatial] using h

/-- A point of the forward cone at time `≤ 0` is the origin: `‖spatial p‖ ≤ time p ≤ 0`.

DERIVED: `0` is the time bound and the origin. -/
theorem eq_zero_of_mem_cone {p : Spacetime} (hc : p ∈ forwardCone) (ht : time p ≤ 0) : p = 0 := by
  have hs : ‖spatial p‖ ≤ time p := hc
  have hs0 : ‖spatial p‖ = 0 := le_antisymm (hs.trans ht) (norm_nonneg _)
  exact eq_zero_of_spatial_time (norm_eq_zero.mp hs0) (le_antisymm ht ((norm_nonneg _).trans hs))

/-- Points of the forward cone have nonnegative time.

DERIVED: `0` is the time bound. -/
theorem time_nonneg_of_mem_cone {p : Spacetime} (hc : p ∈ forwardCone) : 0 ≤ time p :=
  (norm_nonneg _).trans hc

/-- A weight for the functional calculus: measurable, with `|h| ≤ 1`.

DERIVED: `1` is the bound. -/
structure UnitBounded (h : Spacetime → ℝ) : Prop where
  measurable : Measurable h
  abs_le : ∀ p, |h p| ≤ 1

/-- A weight is integrable against a finite measure.

DERIVED: `1` is the dominating constant, in the proof only. -/
theorem UnitBounded.integrable {h : Spacetime → ℝ} (hh : UnitBounded h) (μ : Measure Spacetime)
    [IsFiniteMeasure μ] : Integrable h μ :=
  (integrable_const (1 : ℝ)).mono' hh.measurable.aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hh.abs_le p)

/-- The product of weights is a weight.

DERIVED: `1` is the bound. -/
theorem UnitBounded.mul {f g : Spacetime → ℝ} (hf : UnitBounded f) (hg : UnitBounded g) :
    UnitBounded (fun p => f p * g p) :=
  ⟨hf.measurable.mul hg.measurable, fun p => by
    rw [abs_mul]; exact mul_le_one₀ (hf.abs_le p) (abs_nonneg _) (hg.abs_le p)⟩

/-- The restriction of a weight to a measurable set is a weight.

DERIVED: `0` is the value off the set; `1` the bound. -/
theorem UnitBounded.indicator {f : Spacetime → ℝ} (hf : UnitBounded f) {B : Set Spacetime}
    (hB : MeasurableSet B) : UnitBounded (B.indicator f) :=
  ⟨hf.measurable.indicator hB, fun p => by
    by_cases hp : p ∈ B
    · rw [Set.indicator_of_mem hp]; exact hf.abs_le p
    · rw [Set.indicator_of_notMem hp, abs_zero]; exact zero_le_one⟩

/-- The simple approximants of a weight, with values in `[−1, 1]`.

DERIVED: `1` is the bound; `0` the base value of the approximation. -/
noncomputable def approx {g : Spacetime → ℝ} (hg : UnitBounded g) (n : ℕ) : SimpleFunc Spacetime ℝ :=
  SimpleFunc.approxOn g hg.measurable (Icc (-1) 1) 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) n

/-- The approximants are bounded by `1`.

DERIVED: `1` is the bound. -/
theorem approx_abs_le {g : Spacetime → ℝ} (hg : UnitBounded g) (n : ℕ) (p : Spacetime) :
    |approx hg n p| ≤ 1 := by
  unfold approx
  exact abs_le.mpr (Set.mem_Icc.mp (SimpleFunc.approxOn_mem _ _ _ _))

/-- The approximants converge pointwise.

DERIVED: no numeral appears in the statement. -/
theorem tendsto_approx {g : Spacetime → ℝ} (hg : UnitBounded g) (p : Spacetime) :
    Tendsto (fun n => approx hg n p) atTop (𝓝 (g p)) := by
  unfold approx
  exact SimpleFunc.tendsto_approxOn _ _ (subset_closure (Set.mem_Icc.mpr (abs_le.mp (hg.abs_le p))))

/-! ## 3. Operators determined by their quadratic forms -/

section Ops

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Two operators with the same diagonal readings `⟪u, A u⟫` are equal (complex scalars).

DERIVED: no numeral appears in the statement. -/
theorem op_ext {A B : H →L[ℂ] H} (h : ∀ u, inner ℂ u (A u) = inner ℂ u (B u)) : A = B := by
  apply ContinuousLinearMap.coe_injective
  refine (ext_inner_map _ _).mp fun x => ?_
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, h x, inner_conj_symm]

/-- An operator with real diagonal readings is self-adjoint.

DERIVED: no numeral appears in the statement. -/
theorem isSelfAdjoint_of_inner_real {A : H →L[ℂ] H} (h : ∀ u, ∃ r : ℝ, inner ℂ u (A u) = r) :
    IsSelfAdjoint A := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  obtain ⟨r, hr⟩ := h v
  have hv : inner ℂ (A v) v = (r : ℂ) := by rw [← inner_conj_symm, hr, Complex.conj_ofReal]
  simp only [ContinuousLinearMap.coe_coe]
  rw [hv, Complex.conj_ofReal]

omit [CompleteSpace H] in
/-- `⟪x, x⟫ = ‖x‖²` as a complex number with zero imaginary part.

DERIVED: `2` is the square. -/
theorem inner_self_real (x : H) : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  · rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) x

omit [CompleteSpace H] in
/-- Two vectors with `‖x‖ = ‖y‖` and `re ⟪x, y⟫ = ‖y‖²` are equal: `‖x − y‖² = 0`.

DERIVED: `2` is the square. -/
theorem eq_of_norm_sq_re_inner {x y : H} (h1 : ‖x‖ ^ 2 = ‖y‖ ^ 2)
    (h2 : RCLike.re (inner ℂ x y) = ‖y‖ ^ 2) : x = y := by
  have h : ‖x - y‖ ^ 2 = 0 := by rw [norm_sub_sq (𝕜 := ℂ), h1, h2]; ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h))

end Ops

/-! ## 4. The spectral measure -/

namespace EnergyMomentumMeasure

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : EnergyMomentumMeasure H)

/-- The projections are symmetric: `⟪E A x, y⟫ = ⟪x, E A y⟫`.

DERIVED: no numeral appears in the statement. -/
theorem inner_proj_left {A : Set Spacetime} (hA : MeasurableSet A) (x y : H) :
    inner ℂ (E.projection A x) y = inner ℂ x (E.projection A y) := by
  have h := ContinuousLinearMap.adjoint_inner_left (E.projection A) y x
  rw [E.selfAdjoint hA] at h
  exact h

/-- `E A (E B x) = E (A ∩ B) x`.

DERIVED: no numeral appears in the statement. -/
theorem proj_inter_apply {A B : Set Spacetime} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (x : H) : E.projection A (E.projection B x) = E.projection (A ∩ B) x := by
  rw [← E.intersection hA hB, ContinuousLinearMap.comp_apply]

/-- The projections are idempotent.

DERIVED: no numeral appears in the statement. -/
theorem proj_idem {A : Set Spacetime} (hA : MeasurableSet A) (x : H) :
    E.projection A (E.projection A x) = E.projection A x := by
  rw [E.proj_inter_apply hA hA, Set.inter_self]

/-- `⟪u, E A u⟫ = ν u (A)`.

DERIVED: no numeral appears in the statement. -/
theorem inner_proj_self {A : Set Spacetime} (hA : MeasurableSet A) (u : H) :
    inner ℂ u (E.projection A u) = (((E.diagonal u).real A : ℝ) : ℂ) :=
  (E.diagonalIdentity hA u).symm

/-- `‖E A u‖² = ν u (A)`.

DERIVED: `2` is the square. -/
theorem norm_proj_sq {A : Set Spacetime} (hA : MeasurableSet A) (u : H) :
    ‖E.projection A u‖ ^ 2 = (E.diagonal u).real A := by
  have h : inner ℂ (E.projection A u) (E.projection A u) = (((E.diagonal u).real A : ℝ) : ℂ) := by
    rw [E.inner_proj_left hA, E.proj_idem hA, E.inner_proj_self hA]
  rw [inner_self_real] at h
  exact Complex.ofReal_injective h

/-- The total mass of `ν u` is `‖u‖²`.

DERIVED: `2` is the square. -/
theorem real_univ (u : H) : (E.diagonal u).real Set.univ = ‖u‖ ^ 2 := by
  have h := E.diagonalIdentity MeasurableSet.univ u
  rw [E.univ, ContinuousLinearMap.id_apply, inner_self_real] at h
  exact Complex.ofReal_injective h

/-- Finite measures with the same real values on measurable sets are equal.

DERIVED: no numeral appears in the statement. -/
theorem measure_eq_of_real {μ ν : Measure Spacetime} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ A, MeasurableSet A → μ.real A = ν.real A) : μ = ν :=
  Measure.ext fun A hA => by rw [← ofReal_measureReal, h A hA, ofReal_measureReal]

/-- The diagonal measure of `E B u` is `ν u` restricted to `B`.

DERIVED: no numeral appears in the statement. -/
theorem diagonal_proj {B : Set Spacetime} (hB : MeasurableSet B) (u : H) :
    E.diagonal (E.projection B u) = (E.diagonal u).restrict B := by
  refine measure_eq_of_real fun A hA => ?_
  have hset : B ∩ (A ∩ B) = A ∩ B := by
    ext p; simp only [Set.mem_inter_iff]; tauto
  have h1 := E.diagonalIdentity hA (E.projection B u)
  rw [E.proj_inter_apply hA hB, E.inner_proj_left hB, E.proj_inter_apply hB (hA.inter hB), hset,
    ← E.diagonalIdentity (hA.inter hB)] at h1
  rw [measureReal_restrict_apply hA]
  exact_mod_cast h1

/-- A set whose projection vanishes carries no weight of any `ν u`.

DERIVED: `0` is the zero operator and the zero mass. -/
theorem diagonal_eq_zero_of_proj {A : Set Spacetime} (hA : MeasurableSet A)
    (hP : E.projection A = 0) (u : H) : E.diagonal u A = 0 := by
  have h := E.norm_proj_sq hA u
  rw [hP, _root_.zero_apply, norm_zero] at h
  exact (measureReal_eq_zero_iff).mp (by rw [← h]; norm_num)

/-! ## 5. The functional calculus -/

/-- The diagonal reading `∫ h dν u` of a weight.

DERIVED: no numeral appears in the definition. -/
noncomputable def quad (h : Spacetime → ℝ) (u : H) : ℂ := ((∫ p, h p ∂E.diagonal u : ℝ) : ℂ)

/-- The polarization of `quad h`: for an operator with diagonal readings `quad h` it is `⟪u, A v⟫`.

DERIVED: `4` is the polarization denominator. -/
noncomputable def form (h : Spacetime → ℝ) (u v : H) : ℂ :=
  (E.quad h (u + v) - E.quad h (u - v) - Complex.I * E.quad h (u + Complex.I • v) +
    Complex.I * E.quad h (u - Complex.I • v)) / 4

/-- The operator `Σ_c c E(s⁻¹{c})` of a simple function.

DERIVED: no numeral appears in the definition. -/
noncomputable def simpleOp (s : SimpleFunc Spacetime ℝ) : H →L[ℂ] H :=
  ∑ c ∈ s.range, (c : ℂ) • E.projection (s ⁻¹' {c})

/-- `simpleOp s x = Σ_c c E(s⁻¹{c}) x`.

DERIVED: no numeral appears in the statement. -/
theorem simpleOp_apply (s : SimpleFunc Spacetime ℝ) (x : H) :
    E.simpleOp s x = ∑ c ∈ s.range, (c : ℂ) • E.projection (s ⁻¹' {c}) x := by
  simp only [simpleOp, _root_.sum_apply, _root_.smul_apply]

/-- `⟪u, simpleOp s u⟫ = ∫ s dν u`.

DERIVED: no numeral appears in the statement. -/
theorem inner_simpleOp_self (s : SimpleFunc Spacetime ℝ) (u : H) :
    inner ℂ u (E.simpleOp s u) = E.quad s u := by
  rw [E.simpleOp_apply, inner_sum, quad,
    SimpleFunc.integral_eq_sum s (SimpleFunc.integrable_of_isFiniteMeasure s), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [inner_smul_right, E.inner_proj_self (s.measurableSet_preimage _), smul_eq_mul]
  push_cast
  ring

/-- The operator of a simple function is self-adjoint.

DERIVED: no numeral appears in the statement. -/
theorem simpleOp_sa (s : SimpleFunc Spacetime ℝ) : IsSelfAdjoint (E.simpleOp s) :=
  isSelfAdjoint_of_inner_real fun u => ⟨∫ p, s p ∂E.diagonal u, E.inner_simpleOp_self s u⟩

/-- `⟪u, simpleOp s v⟫ = form s u v`, the complex polarization identity.

DERIVED: no numeral appears in the statement. -/
theorem inner_simpleOp (s : SimpleFunc Spacetime ℝ) (u v : H) :
    inner ℂ u (E.simpleOp s v) = E.form s u v := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (E.simpleOp_sa s)
  have hq : ∀ z, inner ℂ (E.simpleOp s z) z = E.quad s z := fun z => by
    have := hs z z
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, E.inner_simpleOp_self]
  have hp := inner_map_polarization' (E.simpleOp s : H →ₗ[ℂ] H) u v
  simp only [ContinuousLinearMap.coe_coe] at hp
  have huv := hs u v
  simp only [ContinuousLinearMap.coe_coe] at huv
  rw [← huv, hp, hq, hq, hq, hq]
  rfl

/-- Dominated convergence for the diagonal readings: weights `hs n → h` pointwise with `|hs n| ≤ 1`
have `quad (hs n) u → quad h u`.

DERIVED: `1` is the bound. -/
theorem tendsto_quad {hs : ℕ → Spacetime → ℝ} {h : Spacetime → ℝ} (hm : ∀ n, Measurable (hs n))
    (hb : ∀ n p, |hs n p| ≤ 1) (hl : ∀ p, Tendsto (fun n => hs n p) atTop (𝓝 (h p))) (u : H) :
    Tendsto (fun n => E.quad (hs n) u) atTop (𝓝 (E.quad h u)) := by
  have hi := tendsto_integral_of_dominated_convergence (μ := E.diagonal u) (fun _ => (1 : ℝ))
    (fun n => (hm n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb n p)
    (Eventually.of_forall hl)
  exact (Complex.continuous_ofReal.tendsto _).comp hi

/-- Dominated convergence for the polarized readings.

DERIVED: `1` is the bound. -/
theorem tendsto_form {hs : ℕ → Spacetime → ℝ} {h : Spacetime → ℝ} (hm : ∀ n, Measurable (hs n))
    (hb : ∀ n p, |hs n p| ≤ 1) (hl : ∀ p, Tendsto (fun n => hs n p) atTop (𝓝 (h p))) (u v : H) :
    Tendsto (fun n => E.form (hs n) u v) atTop (𝓝 (E.form h u v)) := by
  have q := fun z => E.tendsto_quad hm hb hl z
  exact ((((q (u + v)).sub (q (u - v))).sub ((q (u + Complex.I • v)).const_mul Complex.I)).add
    ((q (u - Complex.I • v)).const_mul Complex.I)).div_const 4

/-- The polarized readings of the simple approximants converge to those of the weight.

DERIVED: no numeral appears in the statement. -/
theorem tendsto_form_approx {h : Spacetime → ℝ} (hh : UnitBounded h) (u v : H) :
    Tendsto (fun n => E.form (approx hh n) u v) atTop (𝓝 (E.form h u v)) :=
  E.tendsto_form (hs := fun n => ⇑(approx hh n)) (fun _ => SimpleFunc.measurable _)
    (approx_abs_le hh) (tendsto_approx hh) u v

/-- `form h` is additive in its second slot (a pointwise limit of `⟪u, simpleOp s ·⟫`).

DERIVED: no numeral appears in the statement. -/
theorem form_add_right {h : Spacetime → ℝ} (hh : UnitBounded h) (u v w : H) :
    E.form h u (v + w) = E.form h u v + E.form h u w := by
  refine tendsto_nhds_unique (E.tendsto_form_approx hh u (v + w)) ?_
  have : ∀ n, E.form (approx hh n) u (v + w) =
      E.form (approx hh n) u v + E.form (approx hh n) u w := fun n => by
    rw [← E.inner_simpleOp, ← E.inner_simpleOp, ← E.inner_simpleOp, map_add, inner_add_right]
  simp only [this]
  exact (E.tendsto_form_approx hh u v).add (E.tendsto_form_approx hh u w)

/-- `form h` is linear in its second slot.

DERIVED: no numeral appears in the statement. -/
theorem form_smul_right {h : Spacetime → ℝ} (hh : UnitBounded h) (c : ℂ) (u v : H) :
    E.form h u (c • v) = c * E.form h u v := by
  refine tendsto_nhds_unique (E.tendsto_form_approx hh u (c • v)) ?_
  have : ∀ n, E.form (approx hh n) u (c • v) = c * E.form (approx hh n) u v := fun n => by
    rw [← E.inner_simpleOp, ← E.inner_simpleOp, map_smul, inner_smul_right]
  simp only [this]
  exact (E.tendsto_form_approx hh u v).const_mul c

/-- `form h` is additive in its first slot.

DERIVED: no numeral appears in the statement. -/
theorem form_add_left {h : Spacetime → ℝ} (hh : UnitBounded h) (u u' v : H) :
    E.form h (u + u') v = E.form h u v + E.form h u' v := by
  refine tendsto_nhds_unique (E.tendsto_form_approx hh (u + u') v) ?_
  have : ∀ n, E.form (approx hh n) (u + u') v =
      E.form (approx hh n) u v + E.form (approx hh n) u' v := fun n => by
    rw [← E.inner_simpleOp, ← E.inner_simpleOp, ← E.inner_simpleOp, inner_add_left]
  simp only [this]
  exact (E.tendsto_form_approx hh u v).add (E.tendsto_form_approx hh u' v)

/-- `form h` is conjugate-linear in its first slot.

DERIVED: no numeral appears in the statement. -/
theorem form_smul_left {h : Spacetime → ℝ} (hh : UnitBounded h) (c : ℂ) (u v : H) :
    E.form h (c • u) v = (starRingEnd ℂ) c * E.form h u v := by
  refine tendsto_nhds_unique (E.tendsto_form_approx hh (c • u) v) ?_
  have : ∀ n, E.form (approx hh n) (c • u) v = (starRingEnd ℂ) c * E.form (approx hh n) u v :=
    fun n => by rw [← E.inner_simpleOp, ← E.inner_simpleOp, inner_smul_left]
  simp only [this]
  exact (E.tendsto_form_approx hh u v).const_mul _

/-- On the diagonal, `form h u u = quad h u`.

DERIVED: no numeral appears in the statement. -/
theorem form_self {h : Spacetime → ℝ} (hh : UnitBounded h) (u : H) : E.form h u u = E.quad h u := by
  refine tendsto_nhds_unique (E.tendsto_form_approx hh u u) ?_
  have : ∀ n, E.form (approx hh n) u u = E.quad (approx hh n) u := fun n => by
    rw [← E.inner_simpleOp, E.inner_simpleOp_self]
  simp only [this]
  exact E.tendsto_quad (hs := fun n => ⇑(approx hh n)) (fun n => SimpleFunc.measurable _)
    (approx_abs_le hh) (tendsto_approx hh) u

/-- `form h` vanishes at the zero vector in the first slot.

DERIVED: `0` is the zero vector and the zero reading. -/
theorem form_zero_left {h : Spacetime → ℝ} (hh : UnitBounded h) (v : H) : E.form h 0 v = 0 := by
  have := E.form_smul_left hh 0 0 v
  rwa [zero_smul, map_zero, zero_mul] at this

/-- `form h` vanishes at the zero vector in the second slot.

DERIVED: `0` is the zero vector and the zero reading. -/
theorem form_zero_right {h : Spacetime → ℝ} (hh : UnitBounded h) (u : H) : E.form h u 0 = 0 := by
  have := E.form_smul_right hh 0 u 0
  rwa [zero_smul, zero_mul] at this

/-- `|quad h u| ≤ ‖u‖²`.

DERIVED: `2` is the square. -/
theorem norm_quad_le {h : Spacetime → ℝ} (hh : UnitBounded h) (u : H) : ‖E.quad h u‖ ≤ ‖u‖ ^ 2 := by
  rw [quad, Complex.norm_real, ← E.real_univ u]
  have := norm_integral_le_of_norm_le_const (μ := E.diagonal u) (f := h) (C := 1)
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hh.abs_le p)
  simpa using this

/-- `|form h u v| ≤ ‖u‖² + ‖v‖²`, by the parallelogram law.

DERIVED: `2` is the square; `4` the polarization denominator, in the proof only. -/
theorem norm_form_le_sq {h : Spacetime → ℝ} (hh : UnitBounded h) (u v : H) :
    ‖E.form h u v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have h1 := E.norm_quad_le hh (u + v)
  have h2 := E.norm_quad_le hh (u - v)
  have h3 := E.norm_quad_le hh (u + Complex.I • v)
  have h4 := E.norm_quad_le hh (u - Complex.I • v)
  have p1 := parallelogram_law_with_norm (𝕜 := ℂ) u v
  have p2 := parallelogram_law_with_norm (𝕜 := ℂ) u (Complex.I • v)
  rw [norm_smul, Complex.norm_I, one_mul] at p2
  have key : ∀ a b c d : ℂ,
      ‖a - b - Complex.I * c + Complex.I * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have e1 := norm_add_le (a - b - Complex.I * c) (Complex.I * d)
    have e2 := norm_sub_le (a - b) (Complex.I * c)
    have e3 := norm_sub_le a b
    rw [norm_mul, Complex.norm_I, one_mul] at e1 e2
    linarith
  have k := key (E.quad h (u + v)) (E.quad h (u - v)) (E.quad h (u + Complex.I • v))
    (E.quad h (u - Complex.I • v))
  have h4n : ‖(4 : ℂ)‖ = 4 := by simp
  rw [form, norm_div, h4n, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- `|form h u v| ≤ 2 ‖u‖ ‖v‖`: `norm_form_le_sq` at `(a u, a⁻¹ v)` with `a² = ‖v‖ / ‖u‖`.

DERIVED: `2` is the bound (the sum `‖u‖‖v‖ + ‖u‖‖v‖` of the balanced squares). -/
theorem norm_form_le {h : Spacetime → ℝ} (hh : UnitBounded h) (u v : H) :
    ‖E.form h u v‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [E.form_zero_left hh]; simp
  rcases eq_or_ne v 0 with rfl | hv
  · rw [E.form_zero_right hh]; simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set a : ℝ := Real.sqrt (‖v‖ / ‖u‖) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (div_pos hv' hu')
  have ha2 : a ^ 2 = ‖v‖ / ‖u‖ := Real.sq_sqrt (div_pos hv' hu').le
  have hu0 : ‖u‖ ≠ 0 := hu'.ne'
  have hv0 : ‖v‖ ≠ 0 := hv'.ne'
  have hscale : E.form h u v = E.form h ((a : ℂ) • u) (((a⁻¹ : ℝ) : ℂ) • v) := by
    rw [E.form_smul_left hh, E.form_smul_right hh, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ ha0.ne', Complex.ofReal_one, one_mul]
  rw [hscale]
  refine (E.norm_form_le_sq hh _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ha0, abs_of_pos (inv_pos.mpr ha0), mul_pow, mul_pow, inv_pow, ha2]
  field_simp
  ring

/-- The bounded sesquilinear form of a weight.

DERIVED: `2` is the bound of `norm_form_le`. -/
noncomputable def formCLM {h : Spacetime → ℝ} (hh : UnitBounded h) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (E.form h) (E.form_add_left hh)
      (fun c u v => by rw [E.form_smul_left hh, smul_eq_mul])
      (E.form_add_right hh)
      (fun c u v => by rw [E.form_smul_right hh, smul_eq_mul, RingHom.id_apply]))
    2 (fun u v => E.norm_form_le hh u v)

/-- The operator `∫ h dE` of a weight: the operator of `formCLM` (Riesz).

DERIVED: no numeral appears in the definition. -/
noncomputable def op {h : Spacetime → ℝ} (hh : UnitBounded h) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (E.formCLM hh))

/-- `⟪u, op h v⟫ = form h u v`.

DERIVED: no numeral appears in the statement. -/
theorem inner_op {h : Spacetime → ℝ} (hh : UnitBounded h) (u v : H) :
    inner ℂ u (E.op hh v) = E.form h u v := by
  rw [op, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- `⟪u, op h u⟫ = ∫ h dν u`.

DERIVED: no numeral appears in the statement. -/
theorem inner_op_self {h : Spacetime → ℝ} (hh : UnitBounded h) (u : H) :
    inner ℂ u (E.op hh u) = E.quad h u := by
  rw [E.inner_op, E.form_self hh]

/-- `op h` is self-adjoint.

DERIVED: no numeral appears in the statement. -/
theorem op_sa {h : Spacetime → ℝ} (hh : UnitBounded h) : IsSelfAdjoint (E.op hh) :=
  isSelfAdjoint_of_inner_real fun u => ⟨∫ p, h p ∂E.diagonal u, E.inner_op_self hh u⟩

/-- `⟪op h x, y⟫ = ⟪x, op h y⟫`.

DERIVED: no numeral appears in the statement. -/
theorem op_symm {h : Spacetime → ℝ} (hh : UnitBounded h) (x y : H) :
    inner ℂ (E.op hh x) y = inner ℂ x (E.op hh y) := by
  have := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (E.op_sa hh) x y
  simpa only [ContinuousLinearMap.coe_coe] using this

/-- An operator with diagonal readings `∫ h dν u` is `op h`.

DERIVED: no numeral appears in the statement. -/
theorem op_eq_of_quad {h : Spacetime → ℝ} (hh : UnitBounded h) (A : H →L[ℂ] H)
    (hA : ∀ u, inner ℂ u (A u) = E.quad h u) : A = E.op hh :=
  op_ext fun u => by rw [hA, E.inner_op_self]

/-- `op` depends only on the weight.

DERIVED: no numeral appears in the statement. -/
theorem op_congr {h h' : Spacetime → ℝ} (hh : UnitBounded h) (hh' : UnitBounded h') (heq : h = h') :
    E.op hh = E.op hh' := by
  subst heq; rfl

/-- `E B (op h) E B = op (1_B h)`: the diagonal measure of `E B u` is `ν u` restricted to `B`.

DERIVED: no numeral appears in the statement. -/
theorem proj_op_proj {h : Spacetime → ℝ} (hh : UnitBounded h) {B : Set Spacetime}
    (hB : MeasurableSet B) (x : H) :
    E.projection B (E.op hh (E.projection B x)) = E.op (hh.indicator hB) x := by
  have key : (E.projection B).comp ((E.op hh).comp (E.projection B)) = E.op (hh.indicator hB) := by
    refine E.op_eq_of_quad _ _ fun u => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← E.inner_proj_left hB,
      E.inner_op_self, quad, quad, E.diagonal_proj hB, integral_indicator hB]
  exact congrArg (fun T : H →L[ℂ] H => T x) key

/-- `op h = op (1_B h) + op (1_{Bᶜ} h)`.

DERIVED: no numeral appears in the statement. -/
theorem op_split {h : Spacetime → ℝ} (hh : UnitBounded h) {B : Set Spacetime}
    (hB : MeasurableSet B) : E.op hh = E.op (hh.indicator hB) + E.op (hh.indicator hB.compl) := by
  symm
  refine E.op_eq_of_quad _ _ fun u => ?_
  rw [_root_.add_apply, inner_add_right, E.inner_op_self, E.inner_op_self, quad, quad, quad,
    ← Complex.ofReal_add,
    ← integral_add ((hh.indicator hB).integrable _) ((hh.indicator hB.compl).integrable _)]
  simp only [Set.indicator_self_add_compl_apply]

/-- **`op h ∘ E B = op (1_B h)`**: the projections commute with `op h`.

DERIVED: `0` is the zero vector, in the proof only. -/
theorem op_proj {h : Spacetime → ℝ} (hh : UnitBounded h) {B : Set Spacetime}
    (hB : MeasurableSet B) (x : H) : E.op hh (E.projection B x) = E.op (hh.indicator hB) x := by
  have h1 : E.op (hh.indicator hB) (E.projection B x) = E.op (hh.indicator hB) x := by
    rw [← E.proj_op_proj hh hB, E.proj_idem hB, E.proj_op_proj hh hB]
  have h2 : E.op (hh.indicator hB.compl) (E.projection B x) = 0 := by
    rw [← E.proj_op_proj hh hB.compl, E.proj_inter_apply hB.compl hB, Set.compl_inter_self,
      E.empty, _root_.zero_apply, map_zero, map_zero]
  rw [E.op_split hh hB, _root_.add_apply, h1, h2, add_zero]

/-- `op h ∘ simpleOp s = op (h s)` for a simple `s` with `|s| ≤ 1`: `op_proj` summed over the values
of `s`.

DERIVED: `1` is the bound. -/
theorem op_simpleOp {h : Spacetime → ℝ} (hh : UnitBounded h) (s : SimpleFunc Spacetime ℝ)
    (hs : ∀ p, |s p| ≤ 1) (x : H) :
    E.op hh (E.simpleOp s x) = E.op (hh.mul ⟨s.measurable, hs⟩) x := by
  have hpt : (fun p => h p * s p) = fun p => ∑ c ∈ s.range, c * (s ⁻¹' {c}).indicator h p := by
    funext p
    rw [Finset.sum_eq_single (s p)]
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr (Set.mem_singleton _)), mul_comm]
    · intro c _ hc
      rw [Set.indicator_of_notMem (show p ∉ s ⁻¹' {c} from fun hp =>
        hc (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hp)).symm), mul_zero]
    · intro hn
      exact absurd (s.mem_range_self p) hn
  have key : (E.op hh).comp (E.simpleOp s) = E.op (hh.mul ⟨s.measurable, hs⟩) := by
    refine E.op_eq_of_quad _ _ fun u => ?_
    rw [ContinuousLinearMap.comp_apply, E.simpleOp_apply, map_sum, inner_sum]
    have hterm : ∀ c ∈ s.range, inner ℂ u (E.op hh ((c : ℂ) • E.projection (s ⁻¹' {c}) u)) =
        (c : ℂ) * E.quad ((s ⁻¹' {c}).indicator h) u := by
      intro c _
      rw [map_smul, inner_smul_right, E.op_proj hh (s.measurableSet_preimage _), E.inner_op_self]
    rw [Finset.sum_congr rfl hterm,
      show E.quad (fun p => h p * s p) u =
        E.quad (fun p => ∑ c ∈ s.range, c * (s ⁻¹' {c}).indicator h p) u by rw [hpt]]
    simp only [quad]
    rw [integral_finsetSum _ (fun c _ =>
        ((hh.indicator (s.measurableSet_preimage {c})).integrable _).const_mul c),
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_const_mul, Complex.ofReal_mul]
  exact congrArg (fun T : H →L[ℂ] H => T x) key

/-- **`op f ∘ op g = op (f g)`.** `op g` is the weak limit of `simpleOp (approx g n)`, and
`op f ∘ simpleOp (approx g n) = op (f · approx g n)` (`op_simpleOp`) converges weakly to
`op (f g)` by dominated convergence.

DERIVED: no numeral appears in the statement. -/
theorem op_mul {f g : Spacetime → ℝ} (hf : UnitBounded f) (hg : UnitBounded g) (v : H) :
    E.op hf (E.op hg v) = E.op (hf.mul hg) v := by
  refine ext_inner_left ℂ fun u => ?_
  rw [← E.op_symm hf u (E.op hg v), E.inner_op hg (E.op hf u) v, E.inner_op (hf.mul hg) u v]
  refine tendsto_nhds_unique (E.tendsto_form_approx hg (E.op hf u) v) ?_
  have heq : ∀ n, E.form (approx hg n) (E.op hf u) v =
      E.form (fun p => f p * approx hg n p) u v := by
    intro n
    rw [← E.inner_simpleOp, E.op_symm hf u, E.op_simpleOp hf _ (approx_abs_le hg n), E.inner_op]
  simp only [heq]
  exact E.tendsto_form (hs := fun n p => f p * approx hg n p)
    (fun n => (hf.mul ⟨SimpleFunc.measurable _, approx_abs_le hg n⟩).measurable)
    (fun n => (hf.mul ⟨SimpleFunc.measurable _, approx_abs_le hg n⟩).abs_le)
    (fun p => tendsto_const_nhds.mul (tendsto_approx hg p)) u v

/-- `‖op h u‖² = ∫ h² dν u`.

DERIVED: `2` is the square. -/
theorem norm_op_apply_sq {h : Spacetime → ℝ} (hh : UnitBounded h) (u : H) :
    ((‖E.op hh u‖ ^ 2 : ℝ) : ℂ) = E.quad (fun p => h p * h p) u := by
  rw [← inner_self_real, E.op_symm, E.op_mul hh hh,
    E.inner_op_self]

/-- `‖op h u‖ ≤ ‖u‖`.

DERIVED: `2` is the square, in the proof only. -/
theorem norm_op_apply_le {h : Spacetime → ℝ} (hh : UnitBounded h) (u : H) :
    ‖E.op hh u‖ ≤ ‖u‖ := by
  have h1 := congrArg norm (E.norm_op_apply_sq hh u)
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h1
  have h2 := E.norm_quad_le (hh.mul hh) u
  rw [← h1] at h2
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h2

/-- If the vacuum's spectral measure is the point mass at `0`, the diagonal reading at the vacuum is
the value at `0`.

DERIVED: `0` is the origin. -/
theorem quad_of_dirac {Ω : H} (hδ : E.diagonal Ω = Measure.dirac 0) (h : Spacetime → ℝ) :
    E.quad h Ω = (h 0 : ℂ) := by
  rw [quad, hδ, integral_dirac]

/-- **The vacuum's spectral measure is the point mass at `0`**: a unit vector fixed by every
translation has characteristic function `⟪Ω, U x Ω⟫ = 1`, that of `δ₀` (`Measure.ext_of_charFun`).

DERIVED: `0` is the origin; `1` the unit norm. -/
theorem diagonal_eq_dirac {U : Spacetime → H →L[ℂ] H} {Ω : H} (hn : ‖Ω‖ = 1)
    (hΩ : ∀ x, U x Ω = Ω) (hrep : ∀ x, charFun (E.diagonal Ω) x = inner ℂ Ω (U x Ω)) :
    E.diagonal Ω = Measure.dirac 0 := by
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [hrep x, hΩ x, inner_self_real, hn, charFun_dirac]
  simp

/-- A weight with value `1` at the origin fixes the vacuum: `op h Ω = Ω` when `ν Ω = δ₀`.

DERIVED: `0` is the origin; `1` the weight there and the unit norm. -/
theorem op_fix {Ω : H} (hδ : E.diagonal Ω = Measure.dirac 0) (hn : ‖Ω‖ = 1) {h : Spacetime → ℝ}
    (hh : UnitBounded h) (h0 : h 0 = 1) : E.op hh Ω = Ω := by
  refine eq_of_norm_sq_re_inner ?_ ?_
  · have h1 := E.norm_op_apply_sq hh Ω
    simp only [E.quad_of_dirac hδ, h0, mul_one, Complex.ofReal_one] at h1
    rw [hn, one_pow]
    exact_mod_cast h1
  · rw [E.op_symm, E.inner_op_self, E.quad_of_dirac hδ, h0, hn]
    simp

/-- A measurable set containing the origin has `E A Ω = Ω` when `ν Ω = δ₀`.

DERIVED: `0` is the origin; `1` the unit norm. -/
theorem proj_vacuum_of_mem {Ω : H} (hδ : E.diagonal Ω = Measure.dirac 0) (hn : ‖Ω‖ = 1)
    {A : Set Spacetime} (hA : MeasurableSet A) (h0 : (0 : Spacetime) ∈ A) :
    E.projection A Ω = Ω := by
  have hr : (E.diagonal Ω).real A = 1 := by
    rw [hδ, measureReal_def, Measure.dirac_apply' _ hA, Set.indicator_of_mem h0]; simp
  refine eq_of_norm_sq_re_inner ?_ ?_
  · rw [E.norm_proj_sq hA, hr, hn, one_pow]
  · rw [E.inner_proj_left hA, E.inner_proj_self hA, hr, hn]; simp

/-- A measurable set missing the origin has `E A Ω = 0` when `ν Ω = δ₀`.

DERIVED: `0` is the origin and the zero vector. -/
theorem proj_vacuum_of_not_mem {Ω : H} (hδ : E.diagonal Ω = Measure.dirac 0)
    {A : Set Spacetime} (hA : MeasurableSet A) (h0 : (0 : Spacetime) ∉ A) :
    E.projection A Ω = 0 := by
  have hr : (E.diagonal Ω).real A = 0 := by
    rw [hδ, measureReal_def, Measure.dirac_apply' _ hA, Set.indicator_of_notMem h0]; simp
  have h := E.norm_proj_sq hA Ω
  rw [hr] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)

/-! ## 6. The Euclidean semigroup -/

/-- The weight `e^{−t⁺ p₀⁺}` of the semigroup, `p₀ = time p`, `x⁺ = max x 0`. On the forward cone and
at `t ≥ 0` it is `e^{−t p₀}`.

DERIVED: `0` is the floor of the positive parts. -/
noncomputable def euclidWeight (t : ℝ) (p : Spacetime) : ℝ :=
  Real.exp (-(max t 0 * max (time p) 0))

/-- The semigroup weight is a weight: `0 < e^{−t⁺ p₀⁺} ≤ 1`.

DERIVED: `0` is the floor of the positive parts; `1` the bound. -/
theorem unitBounded_euclidWeight (t : ℝ) : UnitBounded (euclidWeight t) where
  measurable := by
    have ht : Measurable time := continuous_time.measurable
    unfold euclidWeight
    fun_prop
  abs_le p := by
    unfold euclidWeight
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

/-- The weight at time `0` is `1`.

DERIVED: `0` is the time origin; `1` the weight. -/
theorem euclidWeight_zero : euclidWeight 0 = fun _ => 1 := by
  funext p; simp [euclidWeight]

/-- The weights multiply: `e^{−s p₀⁺} e^{−t p₀⁺} = e^{−(s+t) p₀⁺}` at `s, t ≥ 0`.

DERIVED: `0` is the time origin. -/
theorem euclidWeight_mul {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (p : Spacetime) :
    euclidWeight s p * euclidWeight t p = euclidWeight (s + t) p := by
  simp only [euclidWeight, max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht)]
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The Euclidean semigroup `S t = ∫ e^{−t p₀} dE`** of the energy–momentum measure.

DERIVED: no numeral appears in the definition. -/
noncomputable def euclid (t : ℝ) : H →L[ℂ] H := E.op (unitBounded_euclidWeight t)

/-- `S 0 = 1`.

DERIVED: `0` is the time origin; `1` the identity. -/
theorem euclid_zero : E.euclid 0 = 1 := by
  refine (E.op_eq_of_quad _ 1 fun u => ?_).symm
  have h1 : ∫ p, euclidWeight 0 p ∂E.diagonal u = ‖u‖ ^ 2 := by
    simp only [euclidWeight_zero, integral_const, smul_eq_mul, mul_one, E.real_univ]
  rw [one_apply_eq_self, quad, h1, inner_self_real]

/-- `S (s + t) = S s S t` for `s, t ≥ 0`.

DERIVED: `0` is the time origin. -/
theorem euclid_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    E.euclid (s + t) = E.euclid s * E.euclid t := by
  have hfun : (fun p => euclidWeight s p * euclidWeight t p) = euclidWeight (s + t) :=
    funext fun p => euclidWeight_mul hs ht p
  ext v
  simp only [euclid, mul_apply_eq_comp]
  rw [E.op_mul, E.op_congr _ (unitBounded_euclidWeight (s + t)) hfun]

/-- `S t` is self-adjoint.

DERIVED: no numeral appears in the statement. -/
theorem euclid_sa (t : ℝ) : IsSelfAdjoint (E.euclid t) := E.op_sa _

/-- `‖S t‖ ≤ 1`.

DERIVED: `1` is the bound. -/
theorem norm_euclid_le (t : ℝ) : ‖E.euclid t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]; exact E.norm_op_apply_le _ u

/-- `S t Ω = Ω` when `ν Ω = δ₀`.

DERIVED: `0` is the origin; `1` the unit norm. -/
theorem euclid_fix {Ω : H} (hδ : E.diagonal Ω = Measure.dirac 0) (hn : ‖Ω‖ = 1) (t : ℝ) :
    E.euclid t Ω = Ω :=
  E.op_fix hδ hn _ (by simp [euclidWeight, time_zero])

/-! ## 7. From decay to the spectral gap -/

/-- `‖S t u‖² = ∫ e^{−2 t⁺ p₀⁺} dν u`.

DERIVED: `2` is the square. -/
theorem norm_euclid_sq (t : ℝ) (u : H) :
    ‖E.euclid t u‖ ^ 2 = ∫ p, euclidWeight t p * euclidWeight t p ∂E.diagonal u := by
  have := E.norm_op_apply_sq (unitBounded_euclidWeight t) u
  rw [quad] at this
  exact_mod_cast this

/-- **Decay empties the low-energy shells.** A vector with `‖S t u‖ ≤ e^{−m t} ‖u‖` at every `t ≥ 0`
puts no weight on `{p₀ ≤ c}` for any `c < m`. For `c < 0` the shell lies outside the forward cone
(`positiveEnergy`); for `0 ≤ c`, `e^{−2tc} ν u {p₀ ≤ c} ≤ ‖S t u‖² ≤ e^{−2mt} ‖u‖²` for every `t`.

DERIVED: `0` is the time origin, the sign split of `c` and the zero mass; `2` the square, in the
proof only. -/
theorem diagonal_le_null (hpos : E.projection forwardConeᶜ = 0) {u : H} {m c : ℝ} (hcm : c < m)
    (hdec : ∀ t : ℝ, 0 ≤ t → ‖E.euclid t u‖ ≤ Real.exp (-(m * t)) * ‖u‖) :
    E.diagonal u {p | time p ≤ c} = 0 := by
  rcases lt_or_ge c 0 with hc | hc
  · refine measure_mono_null ?_ (E.diagonal_eq_zero_of_proj measurableSet_forwardCone.compl hpos u)
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp only [Set.mem_compl_iff]
    intro hcone
    linarith [time_nonneg_of_mem_cone hcone]
  · have hB : MeasurableSet {p : Spacetime | time p ≤ c} :=
      measurableSet_le continuous_time.measurable measurable_const
    have hbound : ∀ t : ℝ, 0 ≤ t →
        (E.diagonal u).real {p | time p ≤ c} ≤ Real.exp (-(2 * (m - c) * t)) * ‖u‖ ^ 2 := by
      intro t ht
      have hind : ∫ p, {p : Spacetime | time p ≤ c}.indicator (fun _ => Real.exp (-(2 * t * c))) p
          ∂E.diagonal u = (E.diagonal u).real {p | time p ≤ c} * Real.exp (-(2 * t * c)) := by
        rw [integral_indicator_const _ hB, smul_eq_mul]
      have hlow : (E.diagonal u).real {p | time p ≤ c} * Real.exp (-(2 * t * c)) ≤
          ‖E.euclid t u‖ ^ 2 := by
        rw [E.norm_euclid_sq, ← hind]
        refine integral_mono ((integrable_const _).indicator hB)
          (((unitBounded_euclidWeight t).mul (unitBounded_euclidWeight t)).integrable _) fun p => ?_
        by_cases hp : p ∈ {p : Spacetime | time p ≤ c}
        · rw [Set.indicator_of_mem hp]
          simp only [euclidWeight, max_eq_left ht]
          rw [← Real.exp_add, Real.exp_le_exp]
          have hp' : time p ≤ c := hp
          have h1 : max (time p) 0 ≤ c := max_le hp' hc
          have h2 := mul_le_mul_of_nonneg_left h1 ht
          linarith
        · rw [Set.indicator_of_notMem hp]
          exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      have hup : ‖E.euclid t u‖ ^ 2 ≤ Real.exp (-(2 * m * t)) * ‖u‖ ^ 2 := by
        calc ‖E.euclid t u‖ ^ 2 ≤ (Real.exp (-(m * t)) * ‖u‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hdec t ht) 2
          _ = Real.exp (-(2 * m * t)) * ‖u‖ ^ 2 := by
              rw [mul_pow, ← Real.exp_nat_mul]
              congr 2
              push_cast
              ring
      calc (E.diagonal u).real {p | time p ≤ c}
          = Real.exp (2 * t * c) *
              ((E.diagonal u).real {p | time p ≤ c} * Real.exp (-(2 * t * c))) := by
            rw [mul_comm ((E.diagonal u).real _), ← mul_assoc, ← Real.exp_add, add_neg_cancel,
              Real.exp_zero, one_mul]
        _ ≤ Real.exp (2 * t * c) * (Real.exp (-(2 * m * t)) * ‖u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hlow.trans hup) (Real.exp_pos _).le
        _ = Real.exp (-(2 * (m - c) * t)) * ‖u‖ ^ 2 := by
            rw [← mul_assoc, ← Real.exp_add]
            congr 2
            ring
    have hlim : Tendsto (fun n : ℕ => Real.exp (-(2 * (m - c) * n)) * ‖u‖ ^ 2) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : (0 : ℝ) < 2 * (m - c)))).mul_const
        (‖u‖ ^ 2)
      rw [zero_mul] at h
      exact h
    have hreal : (E.diagonal u).real {p | time p ≤ c} = 0 :=
      le_antisymm (ge_of_tendsto' hlim fun n => hbound n n.cast_nonneg) measureReal_nonneg
    exact (measureReal_eq_zero_iff).mp hreal

/-- A vector decaying at rate `m` under `S` puts no weight on `{p₀ < m}`.

DERIVED: `0` is the time origin and the zero mass; `1` the unit of the shells `m − 1/(n+1)`, in the
proof only. -/
theorem diagonal_lt_null (hpos : E.projection forwardConeᶜ = 0) {u : H} {m : ℝ}
    (hdec : ∀ t : ℝ, 0 ≤ t → ‖E.euclid t u‖ ≤ Real.exp (-(m * t)) * ‖u‖) :
    E.diagonal u {p | time p < m} = 0 := by
  have hsub : {p : Spacetime | time p < m} ⊆ ⋃ n : ℕ, {p | time p ≤ m - 1 / ((n : ℝ) + 1)} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hp)
    exact Set.mem_iUnion.mpr ⟨n, show time p ≤ m - 1 / ((n : ℝ) + 1) by linarith⟩
  refine measure_mono_null hsub (measure_iUnion_null_iff.mpr fun n => E.diagonal_le_null hpos ?_ hdec)
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- A vector decaying at rate `m` under `S` has `E{p₀ < m} u = 0`.

DERIVED: `0` is the time origin and the zero vector. -/
theorem proj_lt_eq_zero (hpos : E.projection forwardConeᶜ = 0) {u : H} {m : ℝ}
    (hdec : ∀ t : ℝ, 0 ≤ t → ‖E.euclid t u‖ ≤ Real.exp (-(m * t)) * ‖u‖) :
    E.projection {p | time p < m} u = 0 := by
  have hA : MeasurableSet {p : Spacetime | time p < m} :=
    measurableSet_lt continuous_time.measurable measurable_const
  have h := E.norm_proj_sq hA u
  rw [(measureReal_eq_zero_iff).mpr (E.diagonal_lt_null hpos hdec)] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)

omit [CompleteSpace H] in
/-- The vacuum-complement part `u − ⟪Ω, u⟫ Ω` is orthogonal to a unit `Ω`.

DERIVED: `0` is the vanishing pairing; `1` the unit norm. -/
theorem inner_compl_eq_zero {Ω : H} (hn : ‖Ω‖ = 1) (u : H) :
    inner ℂ Ω (u - inner ℂ Ω u • Ω) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_real, hn]
  simp

/-- **The spectral gap from decay on the vacuum complement**: if `‖S t u‖ ≤ e^{−m t} ‖u‖` for every
`t ≥ 0` and `u ⊥ Ω`, then `E{0 < p₀ < m} = 0`.

DERIVED: `0` is the time origin, the vanishing pairing, the origin and the zero operator; `1` the
unit norm. -/
theorem proj_gap (hpos : E.projection forwardConeᶜ = 0) {Ω : H}
    (hδ : E.diagonal Ω = Measure.dirac 0) (hn : ‖Ω‖ = 1) {m : ℝ}
    (hdec : ∀ u : H, inner ℂ Ω u = 0 → ∀ t : ℝ, 0 ≤ t →
      ‖E.euclid t u‖ ≤ Real.exp (-(m * t)) * ‖u‖) :
    E.projection {p | 0 < time p ∧ time p < m} = 0 := by
  have hA : MeasurableSet {p : Spacetime | 0 < time p ∧ time p < m} :=
    (measurableSet_lt measurable_const continuous_time.measurable).inter
      (measurableSet_lt continuous_time.measurable measurable_const)
  have hL : MeasurableSet {p : Spacetime | time p < m} :=
    measurableSet_lt continuous_time.measurable measurable_const
  have hsub : {p : Spacetime | 0 < time p ∧ time p < m} ∩ {p | time p < m} =
      {p | 0 < time p ∧ time p < m} := Set.inter_eq_left.mpr fun p hp => hp.2
  ext u
  obtain ⟨u', hu'⟩ : ∃ u', u' = u - inner ℂ Ω u • Ω := ⟨_, rfl⟩
  have hu'0 : inner ℂ Ω u' = 0 := by rw [hu']; exact inner_compl_eq_zero hn u
  have h1 : E.projection {p | 0 < time p ∧ time p < m} u' = 0 := by
    have := E.proj_inter_apply hA hL u'
    rw [hsub, E.proj_lt_eq_zero hpos (hdec u' hu'0), map_zero] at this
    exact this.symm
  have h2 : E.projection {p | 0 < time p ∧ time p < m} Ω = 0 :=
    E.proj_vacuum_of_not_mem hδ hA (by simp [time_zero])
  have hdecomp : u = u' + inner ℂ Ω u • Ω := by rw [hu', sub_add_cancel]
  rw [_root_.zero_apply, hdecomp, map_add, map_smul, h1, h2, smul_zero, add_zero]

/-- **Below the gap only the vacuum**: under the decay of `proj_gap` with `m > 0`,
`E{p₀ < m} u = ⟪Ω, u⟫ Ω`; the spectrum of `H` on the vacuum complement lies in `[m, ∞)`.

DERIVED: `0` is the time origin, the vanishing pairing, the origin and the sign of `m`; `1` the
unit norm. -/
theorem proj_low (hpos : E.projection forwardConeᶜ = 0) {Ω : H}
    (hδ : E.diagonal Ω = Measure.dirac 0) (hn : ‖Ω‖ = 1) {m : ℝ} (hm : 0 < m)
    (hdec : ∀ u : H, inner ℂ Ω u = 0 → ∀ t : ℝ, 0 ≤ t →
      ‖E.euclid t u‖ ≤ Real.exp (-(m * t)) * ‖u‖) (u : H) :
    E.projection {p | time p < m} u = inner ℂ Ω u • Ω := by
  have hL : MeasurableSet {p : Spacetime | time p < m} :=
    measurableSet_lt continuous_time.measurable measurable_const
  obtain ⟨u', hu'⟩ : ∃ u', u' = u - inner ℂ Ω u • Ω := ⟨_, rfl⟩
  have hu'0 : inner ℂ Ω u' = 0 := by rw [hu']; exact inner_compl_eq_zero hn u
  have hdecomp : u = u' + inner ℂ Ω u • Ω := by rw [hu', sub_add_cancel]
  have hΩ : E.projection {p | time p < m} Ω = Ω :=
    E.proj_vacuum_of_mem hδ hn hL (by simp [time_zero, hm])
  conv_lhs => rw [hdecomp]
  rw [map_add, map_smul, E.proj_lt_eq_zero hpos (hdec u' hu'0), hΩ, zero_add]

/-- **The zero-energy subspace is the vacuum line**: with a unitary translation group `U` tied to
`E` by the spectral representation, a unit vacuum fixed by `U`, and the uniqueness of the invariant
vacuum, `E{p₀ ≤ 0} u = ⟪Ω, u⟫ Ω`. The measure of `w = E{p₀ ≤ 0} u` sits at `p = 0` (the cone meets
`{p₀ ≤ 0}` only there), so `⟪w, U x w⟫ = ‖w‖²` and `U x w = w`.

DERIVED: `0` is the time bound, the origin and the zero operator; `1` the unit norm; `2` the
square. -/
theorem proj_zeroEnergy {U : Spacetime → H →L[ℂ] H} (hU : ∀ x v, ‖U x v‖ = ‖v‖)
    (hrep : ∀ v x, charFun (E.diagonal v) x = inner ℂ v (U x v))
    (hpos : E.projection forwardConeᶜ = 0) {Ω : H} (hn : ‖Ω‖ = 1) (hΩ : ∀ x, U x Ω = Ω)
    (huniq : ∀ v, (∀ x, U x v = v) → ∃ c : ℂ, c • Ω = v) (u : H) :
    E.projection {p | time p ≤ 0} u = inner ℂ Ω u • Ω := by
  have hZ : MeasurableSet {p : Spacetime | time p ≤ 0} :=
    measurableSet_le continuous_time.measurable measurable_const
  have hδ := E.diagonal_eq_dirac hn hΩ (hrep Ω)
  obtain ⟨w, hw⟩ : ∃ w, w = E.projection {p | time p ≤ 0} u := ⟨_, rfl⟩
  have hnull : E.diagonal w {(0 : Spacetime)}ᶜ = 0 := by
    rw [hw, E.diagonal_proj hZ, Measure.restrict_apply (measurableSet_singleton _).compl]
    refine measure_mono_null ?_ (E.diagonal_eq_zero_of_proj measurableSet_forwardCone.compl hpos u)
    intro p hp
    obtain ⟨hp0, hpZ⟩ := hp
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hp0
    simp only [Set.mem_setOf_eq] at hpZ
    simp only [Set.mem_compl_iff]
    intro hcone
    exact hp0 (eq_zero_of_mem_cone hcone hpZ)
  have hreal : (E.diagonal w).real {(0 : Spacetime)} = ‖w‖ ^ 2 := by
    have := measureReal_add_measureReal_compl (μ := E.diagonal w)
      (measurableSet_singleton (0 : Spacetime))
    rw [(measureReal_eq_zero_iff).mpr hnull, add_zero, E.real_univ] at this
    exact this
  have hae : ∀ᵐ p ∂E.diagonal w, p ∈ ({0} : Set Spacetime) := by
    rw [ae_iff]; exact hnull
  have hres : (E.diagonal w).restrict {0} = E.diagonal w := Measure.restrict_eq_self_of_ae_mem hae
  have hinner : ∀ x, inner ℂ w (U x w) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [← hrep w x, charFun_apply, ← hres, integral_singleton, hreal]
    simp
  have hfix : ∀ x, U x w = w := by
    intro x
    refine eq_of_norm_sq_re_inner (by rw [hU]) ?_
    rw [← inner_conj_symm, hinner x, Complex.conj_ofReal]
    exact Complex.ofReal_re _
  obtain ⟨c, hc⟩ := huniq w hfix
  have hPΩ : E.projection {p | time p ≤ 0} Ω = Ω :=
    E.proj_vacuum_of_mem hδ hn hZ (by simp [time_zero])
  have hcoef : c = inner ℂ Ω u := by
    have h1 : inner ℂ Ω w = inner ℂ Ω u := by rw [hw, ← E.inner_proj_left hZ, hPΩ]
    rw [← hc, inner_smul_right, inner_self_real, hn] at h1
    simpa using h1
  rw [← hw, ← hc, hcoef]

end EnergyMomentumMeasure

/-! ## 8. Their theory -/

namespace WightmanFields

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {L : Type} [AddCommGroup L] [Module ℂ L] (T : WightmanFields H L)

/-- **The Euclidean semigroup `S t = e^{−t H}` of their theory**, `∫ e^{−t p₀} dE` over their
energy–momentum measure (`PublicTheory.lean:259`).

DERIVED: no numeral appears in the definition. -/
noncomputable def euclid (t : ℝ) : H →L[ℂ] H := T.energyMomentum.euclid t

/-- Their field vectors: the vectors of all words of smeared fields on the vacuum
(`PublicTheory.lean:115–118`, `:130–131`).

DERIVED: no numeral appears in the definition. -/
def fieldVectors : Set H := Set.range fun word => (T.fields.vector word).1

/-- `S 0 = 1`.

DERIVED: `0` is the time origin; `1` the identity. -/
theorem euclid_zero : T.euclid 0 = 1 := T.energyMomentum.euclid_zero

/-- `S (s + t) = S s S t` for `s, t ≥ 0`.

DERIVED: `0` is the time origin. -/
theorem euclid_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.euclid (s + t) = T.euclid s * T.euclid t :=
  T.energyMomentum.euclid_add hs ht

/-- `S t` is self-adjoint.

DERIVED: `0` is the time origin. -/
theorem euclid_sa (t : ℝ) (_ : 0 ≤ t) : IsSelfAdjoint (T.euclid t) :=
  T.energyMomentum.euclid_sa t

/-- `‖S t‖ ≤ 1`.

DERIVED: `1` is the bound. -/
theorem norm_euclid_le (t : ℝ) : ‖T.euclid t‖ ≤ 1 := T.energyMomentum.norm_euclid_le t

variable {T}

/-- Their vacuum is fixed by every translation: W2's `vacuumInvariant` at the pure translation,
through `translationCompatibility`.

DERIVED: no numeral appears in the statement. -/
theorem translation_vacuum (hA : AxiomFields T) (x : Spacetime) :
    T.translations.operator x T.fields.vacuum.1 = T.fields.vacuum.1 := by
  rw [← T.translationCompatibility x]; exact hA.vacuumInvariant _

/-- The spectral measure of their vacuum is the point mass at `0`.

DERIVED: `0` is the origin. -/
theorem diagonal_vacuum (hA : AxiomFields T) :
    T.energyMomentum.diagonal T.fields.vacuum.1 = Measure.dirac 0 :=
  T.energyMomentum.diagonal_eq_dirac hA.normalizedVacuum (translation_vacuum hA)
    (hA.spectralRepresentation _)

/-- `S t Ω = Ω`.

DERIVED: `0` is the time origin. -/
theorem euclid_vacuum (hA : AxiomFields T) (t : ℝ) (_ : 0 ≤ t) :
    T.euclid t T.fields.vacuum.1 = T.fields.vacuum.1 :=
  T.energyMomentum.euclid_fix (diagonal_vacuum hA) hA.normalizedVacuum t

/-- The field vectors span a dense subspace (W1: their span is the dense domain).

DERIVED: no numeral appears in the statement. -/
theorem dense_span_fieldVectors (hA : AxiomFields T) :
    Dense (Submodule.span ℂ T.fieldVectors : Set H) := by
  have h := hA.denseDomain
  rw [hA.cyclicVacuum] at h
  exact h

/-- **The named open input**: exponential clustering at rate `m` of the connected Euclidean readings
`⟪v, S t w⟫ − ⟪v, Ω⟫ ⟪Ω, w⟫` of their field vectors. Not public: it is what the identification of
these readings with the Euclidean values of `correlation (some selected)` (the Osterwalder–Schrader
link of their reconstruction) and the decay of those values would give.

DERIVED: `0` is the time origin. -/
def EuclideanClustering (T : WightmanFields H L) (m : ℝ) : Prop :=
  ∀ v ∈ T.fieldVectors, ∀ w ∈ T.fieldVectors, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    ‖inner ℂ v (T.euclid t w) - inner ℂ v T.fields.vacuum.1 * inner ℂ T.fields.vacuum.1 w‖ ≤
      C * Real.exp (-(m * t))

/-- **Clustering gives decay on the vacuum complement**: `OpenAIBridgeGap.gap_of_cluster_time` with
every hypothesis but clustering discharged from their public fields.

DERIVED: `0` is the time origin and the vanishing pairing. -/
theorem gap_of_clustering (hA : AxiomFields T) {m : ℝ} (hcl : T.EuclideanClustering m)
    {t : ℝ} (ht : 0 ≤ t) (u : H) (hu : inner ℂ T.fields.vacuum.1 u = 0) :
    ‖T.euclid t u‖ ≤ Real.exp (-(m * t)) * ‖u‖ :=
  OpenAIBridgeGap.gap_of_cluster_time (S := T.euclid) T.euclid_zero T.euclid_add T.euclid_sa
    hA.normalizedVacuum (euclid_vacuum hA) (dense_span_fieldVectors hA) hcl ht u hu

/-- **The spectral gap of their theory, stated publicly**: under clustering at rate `m`,
`E{0 < p₀ < m} = 0`.

DERIVED: `0` is the energy floor and the zero operator. -/
theorem spectralGap_of_clustering (hA : AxiomFields T) {m : ℝ} (hcl : T.EuclideanClustering m) :
    T.energyMomentum.projection {p | 0 < time p ∧ time p < m} = 0 :=
  T.energyMomentum.proj_gap hA.positiveEnergy (diagonal_vacuum hA) hA.normalizedVacuum
    fun u hu _ ht => gap_of_clustering hA hcl ht u hu

/-- Under clustering at rate `m > 0`, `E{p₀ < m} u = ⟪Ω, u⟫ Ω`: below `m` only the vacuum.

DERIVED: `0` is the sign of `m`. -/
theorem lowEnergy_of_clustering (hA : AxiomFields T) {m : ℝ} (hm : 0 < m)
    (hcl : T.EuclideanClustering m) (u : H) :
    T.energyMomentum.projection {p | time p < m} u =
      inner ℂ T.fields.vacuum.1 u • T.fields.vacuum.1 :=
  T.energyMomentum.proj_low hA.positiveEnergy (diagonal_vacuum hA) hA.normalizedVacuum hm
    (fun u hu _ ht => gap_of_clustering hA hcl ht u hu) u

/-- **The zero-energy subspace of their theory is the vacuum line**, unconditionally:
`E{p₀ ≤ 0} u = ⟪Ω, u⟫ Ω`, from the spectral representation, positive energy, unitarity of the
translations and `uniqueVacuum`.

DERIVED: `0` is the energy bound. -/
theorem zeroEnergy (hA : AxiomFields T) (u : H) :
    T.energyMomentum.projection {p | time p ≤ 0} u =
      inner ℂ T.fields.vacuum.1 u • T.fields.vacuum.1 :=
  T.energyMomentum.proj_zeroEnergy T.translations.unitary hA.spectralRepresentation
    hA.positiveEnergy hA.normalizedVacuum (translation_vacuum hA) hA.uniqueVacuum u

/-- Under clustering at rate `m ≥ 0`, the generator `H` of `S`
(`ClassHamiltonian.generator`) has `m ‖u‖² ≤ re ⟪u, H u⟫` on the vacuum complement of its domain
(`OpenAIBridgeGap.hamiltonian_gap_of_cluster`).

DERIVED: `0` is the sign of `m` and the vanishing pairing; `2` the square. -/
theorem hamiltonian_gap_of_clustering (hA : AxiomFields T) {m : ℝ} (hm : 0 ≤ m)
    (hcl : T.EuclideanClustering m) (u : (ClassHamiltonian.generator T.euclid).domain)
    (hu : inner ℂ T.fields.vacuum.1 (u : H) = 0) :
    m * ‖(u : H)‖ ^ 2 ≤ (inner ℂ (u : H) (ClassHamiltonian.generator T.euclid u)).re :=
  OpenAIBridgeGap.hamiltonian_gap_of_cluster (S := T.euclid) T.euclid_zero T.euclid_add T.euclid_sa
    hA.normalizedVacuum (euclid_vacuum hA) (dense_span_fieldVectors hA) hm hcl u hu

/-- Under clustering at rate `m > 0`, the kernel of the generator `H` of `S` is the vacuum line
(`OpenAIBridgeGap.hamiltonian_ker_of_cluster`).

DERIVED: `0` is the sign of `m` and the zero vector. -/
theorem hamiltonian_ker_of_clustering (hA : AxiomFields T) {m : ℝ} (hm : 0 < m)
    (hcl : T.EuclideanClustering m) (u : (ClassHamiltonian.generator T.euclid).domain)
    (hHu : ClassHamiltonian.generator T.euclid u = 0) :
    ∃ c : ℂ, (u : H) = c • T.fields.vacuum.1 :=
  OpenAIBridgeGap.hamiltonian_ker_of_cluster (S := T.euclid) T.euclid_zero T.euclid_add
    T.euclid_sa hA.normalizedVacuum (euclid_vacuum hA) (dense_span_fieldVectors hA) hm hcl u hHu

end WightmanFields

end MassGap.OpenAISemigroup

#print axioms MassGap.OpenAISemigroup.continuous_time
#print axioms MassGap.OpenAISemigroup.continuous_spatial
#print axioms MassGap.OpenAISemigroup.measurableSet_forwardCone
#print axioms MassGap.OpenAISemigroup.time_zero
#print axioms MassGap.OpenAISemigroup.eq_zero_of_spatial_time
#print axioms MassGap.OpenAISemigroup.eq_zero_of_mem_cone
#print axioms MassGap.OpenAISemigroup.time_nonneg_of_mem_cone
#print axioms MassGap.OpenAISemigroup.UnitBounded.integrable
#print axioms MassGap.OpenAISemigroup.UnitBounded.mul
#print axioms MassGap.OpenAISemigroup.UnitBounded.indicator
#print axioms MassGap.OpenAISemigroup.approx_abs_le
#print axioms MassGap.OpenAISemigroup.tendsto_approx
#print axioms MassGap.OpenAISemigroup.op_ext
#print axioms MassGap.OpenAISemigroup.isSelfAdjoint_of_inner_real
#print axioms MassGap.OpenAISemigroup.inner_self_real
#print axioms MassGap.OpenAISemigroup.eq_of_norm_sq_re_inner
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_proj_left
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_inter_apply
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_idem
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_proj_self
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_proj_sq
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.real_univ
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.measure_eq_of_real
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.diagonal_proj
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.diagonal_eq_zero_of_proj
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.simpleOp_apply
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_simpleOp_self
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.simpleOp_sa
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_simpleOp
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.tendsto_quad
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.tendsto_form
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.tendsto_form_approx
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_add_right
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_smul_right
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_add_left
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_smul_left
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_self
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_zero_left
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.form_zero_right
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_quad_le
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_form_le_sq
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_form_le
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_op
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_op_self
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_sa
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_symm
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_eq_of_quad
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_congr
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_op_proj
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_split
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_proj
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_simpleOp
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_mul
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_op_apply_sq
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_op_apply_le
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.quad_of_dirac
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.diagonal_eq_dirac
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.op_fix
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_vacuum_of_mem
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_vacuum_of_not_mem
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.unitBounded_euclidWeight
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.euclidWeight_zero
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.euclidWeight_mul
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.euclid_zero
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.euclid_add
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.euclid_sa
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_euclid_le
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.euclid_fix
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.norm_euclid_sq
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.diagonal_le_null
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.diagonal_lt_null
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_lt_eq_zero
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.inner_compl_eq_zero
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_gap
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_low
#print axioms MassGap.OpenAISemigroup.EnergyMomentumMeasure.proj_zeroEnergy
#print axioms MassGap.OpenAISemigroup.WightmanFields.euclid_zero
#print axioms MassGap.OpenAISemigroup.WightmanFields.euclid_add
#print axioms MassGap.OpenAISemigroup.WightmanFields.euclid_sa
#print axioms MassGap.OpenAISemigroup.WightmanFields.norm_euclid_le
#print axioms MassGap.OpenAISemigroup.WightmanFields.translation_vacuum
#print axioms MassGap.OpenAISemigroup.WightmanFields.diagonal_vacuum
#print axioms MassGap.OpenAISemigroup.WightmanFields.euclid_vacuum
#print axioms MassGap.OpenAISemigroup.WightmanFields.dense_span_fieldVectors
#print axioms MassGap.OpenAISemigroup.WightmanFields.gap_of_clustering
#print axioms MassGap.OpenAISemigroup.WightmanFields.spectralGap_of_clustering
#print axioms MassGap.OpenAISemigroup.WightmanFields.lowEnergy_of_clustering
#print axioms MassGap.OpenAISemigroup.WightmanFields.zeroEnergy
#print axioms MassGap.OpenAISemigroup.WightmanFields.hamiltonian_gap_of_clustering
#print axioms MassGap.OpenAISemigroup.WightmanFields.hamiltonian_ker_of_clustering
