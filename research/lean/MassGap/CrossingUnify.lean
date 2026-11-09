import Mathlib
import MassGap.MomentCompare

/-!
# MassGap.CrossingUnify — the coarse scale of (1b) placed at the first crossing

`MomentCompare.clay_canonical_unitOsc_fac` reads `hpos` (1b) through `CoarseUnitOsc ρs cP cL` at a coarse family
`ρs` that it leaves free, and the block condition `√(1 − e^{−2 m cL}) (1 + e^{m cL}) ≤ π₁`. `ScreenBridge` feeds
the `hW` side (the sector seed) from `CrossingUnitOsc cP`, the per-unit oscillation of the exact effective density
`effIter` at the first crossing. This module puts the coarse family of (1b) at the first crossing itself, so both
items read one Prop on one density.

## What is proved

* **One Prop at the crossing** (`CrossingSmall`, `crossingUnitOsc_of_crossingSmall`, `unitOsc_mono`).
  `CrossingSmall δ`: eventually in `β`, at the first crossing of the chain from `2β`, the side-`4` exact effective
  density of `W₀` has `UnitOsc` with both constants `δ` (per background plaquette and per link). It gives
  `CrossingUnitOsc δ`, the `hW`-side input, with `cL := δ`.
* **The crossing density as a family** (`crossIdx`, `crossDens`, `crossDens_banded`). `crossIdx β` is the
  first `k` with coarse defect at most `1/1000`. `crossDens β` is the `crossIdx β`-step exact effective
  density; it is banded.
* **The coarse family of (1b) at the crossing** (`crossTower`). `crossTower hN k` is
  `crossDens (dyBeta k)`: the crossing density of the chain from `2 · dyBeta k`, the pinned coupling of step `k`.
* **The block condition from crossing smallness** (`blockFactor_le_sqrt`, `blockFactor_le`,
  `blockFactor_le_of_crossing`). For `0 ≤ x ≤ 1`: `√(1 − e^{−2x}) (1 + e^x) ≤ √(32 x)` (`fac_factor_le` and
  `e^x ≤ 3`). So `m ≤ m₀`, `m₀ δ ≤ 1` and `32 m₀ δ ≤ π₁²` give the block condition at `m δ`. PROVED: the block
  condition holds at a block count bounded by `m₀` once `δ` is small against `π₁² / m₀`.
* **The factorisation and one-point clauses at the crossing** (`FacPixelAt`, `FacOnePointAt`,
  `effScreenFacPixel_of_crossing`, `effScreenFacOnePoint_of_crossing`). `FacPixelAt … ρs m₀` is the factorisation
  `EffScreenFac` at the torus-centred composite through at most `m₀` blocks, with no scalar clause; with
  `CrossingSmall` it gives `EffScreenFacPixel … π₁ … δ`. `FacOnePointAt … ρs m₀ R` is the factorisation at the two
  single-site fields through at most `m₀` blocks and the ratio clause
  `|w₀| √V₀ · |w₁| √V₁ ≤ R √refMomentS` (torus variances); with `32 m₀ δ R ≤ π₂` it gives `EffScreenFacOnePoint`.
  The block factors `Δᵢ` are chosen as the factor times `√Vᵢ` and both factors are at most `√(32 m₀ δ)`.
* **One threshold** (`crossing_threshold`). For `m₀`, `π₁, π₂ > 0` and `R`, some `δ₀ > 0` makes every `δ ∈ [0, δ₀]`
  satisfy all four scalar conditions: `m₀ δ ≤ 1`, `32 m₀ δ ≤ π₁²`, `32 m₀ δ R ≤ π₂`, `9 · 1024 δ ≤ 1/80000`.

## What is not proved

* `cL ≤ f(cP)` for the effective density: NO. `UnitOsc` does not bound the link constant by the plaquette
  constant in general (a background-independent density has `cP = 0` and any `cL`). For the fine Wilson density the
  link change at `l` is a background change on the plaquettes through `l`: each term reads `ζ_p U_p`, and
  `ζ'_p := ζ_p U'_p U_p⁻¹` gives `ζ'_p U_p = ζ_p U'_p`, so `cL ≤ 6 cP` there (argued). That covariance does not pass
  through `effStep`: the fine backgrounds it changes depend on the integrated variables and are not the pull-back
  of one coarse background (argued). So `CrossingSmall` asks for both constants; it is one Prop on one density at
  one scale, not a consequence of `CrossingUnitOsc`.
* `CrossingSmall δ` itself, for some `δ` below `δ₀`. It is the statement that the exact effective density at the
  first crossing is close to flat in every unit; the a priori flow (`unitOsc_effIter`) carries `cL` unchanged from
  the fine torus and multiplies `cP` by `16` per step, so neither is small from the flow alone.
* The factorisation `FacPixelAt` / `FacOnePointAt` (clause 1 of `RelativeScreen`, unchanged): a refinement screen
  of the SU(N) box whose output at the squared deviations is a reading under the SU(2) crossing density. Placing the
  coarse scale at the crossing does not make it easier in Lean terms: `crossTower` fixes `ρs`, and the clause is the
  same `EffScreenFac` (argued: the fine-face obstruction of `ScreenBridge` is about the screen, not the density).
* The one-point ratio `R` uniform in `k`. `|wᵢ|` is of order the physical cube volume and `Vᵢ` is a single-site
  variance of order one, while `√refMomentS` is a smeared-field scale that shrinks as `k` grows, so the ratio grows
  with `k` and a fixed `δ` does not close the one-point clause (argued). The like-against-like form reads the
  one-point difference at the smeared field, `wᵢ (stateK − stateTD)(Oᵢ) = (stateK − stateTD)(smear Oᵢ)`, which
  needs the translation invariance of the torus state `stateTD` (not in the tree).
* `hW` from `CrossingSmall`: NO. `CrossingSmall` gives `CrossingUnitOsc` and with `SectorRest` the sector seed;
  `WDelta2` needs the `RunSeed` physical-size clause, which the crossing does not supply.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.CrossingUnify

open MeasureTheory Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing
  MassGap.ElectricStepChain MassGap.MovedTorusDecimation MassGap.ElectricExactProof
  MassGap.GapSideVortexAntiDiagonal MassGap.WilsonChainExists
  MassGap.GapSideExactDecimation MassGap.CoarseBoundary MassGap.EffectiveDensityBound
  MassGap.ScreenBridge MassGap.MomentCompare
open MassGap.TwistedTraceBound (negOne coe_negOne)

/-! ## 1. One Prop at the crossing -/

section Crossing

/-- **`UnitOsc` is monotone in its constants.** -/
theorem unitOsc_mono {n : ℕ} {ρ : DensE n} {cP cL cP' cL' : ℝ} (h : UnitOsc ρ cP cL)
    (hP : cP ≤ cP') (hL : cL ≤ cL') : UnitOsc ρ cP' cL' := by
  intro b x x' hx
  refine (h b x x' hx).trans ?_
  cases b with
  | inl q => exact hP
  | inr l => exact hL

/-- **Crossing smallness**: eventually in `β`, at the first crossing `k` of the chain from `2β`, the side-`4`
exact effective density of `W₀` has per-unit oscillation at most `δ` at every background plaquette and at every
link.

DERIVED: Inherited: `1/1000` the doubling-defect seed of `ChainFirstCrossing.FirstCrossingComparison`. -/
def CrossingSmall (δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    UnitOsc (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))) δ δ

/-- **Crossing smallness gives the `hW`-side input** with link constant `δ`. -/
theorem crossingUnitOsc_of_crossingSmall {δ : ℝ} (h : CrossingSmall δ) : CrossingUnitOsc δ :=
  h.mono fun _ hβ k hk hmin => ⟨δ, hβ k hk hmin⟩

/-- The first crossing index of the chain from `2β`: the least `k` with coarse defect at most `1/1000`.

DERIVED: Inherited: `1/1000` the doubling-defect seed of `ChainFirstCrossing.FirstCrossingComparison`. -/
def crossIdx (β : ℝ) : ℕ := sInf {k | coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000}

/-- The exact effective density of `W₀` at the first crossing of the chain from `2β`, on the side-`4` torus. -/
def crossDens (β : ℝ) : DensE 4 :=
  effIter (crossIdx β) 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))

theorem crossDens_banded (β : ℝ) : Banded (crossDens β) :=
  effIter_banded _ 4 _ (fineDens_banded (continuous_halfField (wilsonChainOf (2 * β)) 0))

/-- **The coarse family of (1b) at the crossing**: at step `k`, the crossing density of the chain from
`2 · dyBeta k`. -/
def crossTower {N : ℕ} (hN : N ≠ 0) (k : ℕ) : DensE 4 :=
  crossDens (MassGap.ContinuumSchwinger.dyBeta (MassGap.ContinuumSchwinger.one_le_of_ne_zero hN) k)

end Crossing

/-! ## 2. The block condition from crossing smallness -/

section Block

/-- **The block factor below `√(32 x)`** for `0 ≤ x ≤ 1`. -/
theorem blockFactor_le_sqrt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (1 - Real.exp (-(2 * x))) * (1 + Real.exp x) ≤ Real.sqrt (32 * x) := by
  have e1 : Real.exp x ≤ 3 :=
    (Real.exp_le_exp.mpr hx1).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hs : Real.sqrt (2 * x) * 4 = Real.sqrt (32 * x) := by
    rw [show (32 : ℝ) * x = 2 * x * 4 ^ 2 by ring, Real.sqrt_mul (by linarith) (4 ^ 2),
      Real.sqrt_sq (by norm_num)]
  calc Real.sqrt (1 - Real.exp (-(2 * x))) * (1 + Real.exp x)
      ≤ Real.sqrt (2 * x) * (1 + Real.exp x) := fac_factor_le x
    _ ≤ Real.sqrt (2 * x) * 4 := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ = Real.sqrt (32 * x) := hs

/-- **The block condition from smallness**: `0 ≤ x ≤ 1` and `32 x ≤ π²` give
`√(1 − e^{−2x}) (1 + e^x) ≤ π`. -/
theorem blockFactor_le {x π : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hπ : 0 ≤ π) (h : 32 * x ≤ π ^ 2) :
    Real.sqrt (1 - Real.exp (-(2 * x))) * (1 + Real.exp x) ≤ π :=
  (blockFactor_le_sqrt hx0 hx1).trans ((Real.sqrt_le_sqrt h).trans (Real.sqrt_sq hπ).le)

/-- **The block condition at a bounded block count**: `m ≤ m₀`, `m₀ δ ≤ 1` and `32 m₀ δ ≤ π²`. -/
theorem blockFactor_le_of_crossing {m m₀ : ℕ} {δ π : ℝ} (hm : m ≤ m₀) (hδ : 0 ≤ δ)
    (h1 : (m₀ : ℝ) * δ ≤ 1) (hπ : 0 ≤ π) (h : 32 * ((m₀ : ℝ) * δ) ≤ π ^ 2) :
    Real.sqrt (1 - Real.exp (-(2 * (m * δ)))) * (1 + Real.exp (m * δ)) ≤ π := by
  have hmm : (m : ℝ) * δ ≤ m₀ * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hδ
  exact blockFactor_le (by positivity) (hmm.trans h1) hπ (by linarith)

/-- **The one-point product from the block factors**: both factors at most `√K` and the ratio clause
`u₀ v₀ · u₁ v₁ ≤ R M` with `K R ≤ π` give `u₀ (A v₀) · u₁ (B v₁) ≤ π M`. -/
theorem prod_le_of_factors {A B K u₀ u₁ v₀ v₁ R M π : ℝ} (hB0 : 0 ≤ B)
    (hA : A ≤ Real.sqrt K) (hB : B ≤ Real.sqrt K) (hK : 0 ≤ K) (hu₀ : 0 ≤ u₀) (hu₁ : 0 ≤ u₁)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hR : u₀ * v₀ * (u₁ * v₁) ≤ R * M) (hM : 0 ≤ M) (h : K * R ≤ π) :
    u₀ * (A * v₀) * (u₁ * (B * v₁)) ≤ π * M := by
  have hAB : A * B ≤ K :=
    calc A * B ≤ Real.sqrt K * Real.sqrt K := mul_le_mul hA hB hB0 (Real.sqrt_nonneg _)
      _ = K := Real.mul_self_sqrt hK
  have hX : 0 ≤ u₀ * v₀ * (u₁ * v₁) := by positivity
  calc u₀ * (A * v₀) * (u₁ * (B * v₁)) = (A * B) * (u₀ * v₀ * (u₁ * v₁)) := by ring
    _ ≤ K * (u₀ * v₀ * (u₁ * v₁)) := mul_le_mul_of_nonneg_right hAB hX
    _ ≤ K * (R * M) := mul_le_mul_of_nonneg_left hR hK
    _ = (K * R) * M := by ring
    _ ≤ π * M := mul_le_mul_of_nonneg_right h hM

/-- **One threshold for every scalar condition**: for `m₀`, `π₁, π₂ > 0` and `R`, some `δ₀ > 0` makes every
`δ ∈ [0, δ₀]` satisfy `m₀ δ ≤ 1`, `32 m₀ δ ≤ π₁²`, `32 m₀ δ R ≤ π₂` and `9 · 1024 δ ≤ 1/80000`. -/
theorem crossing_threshold (m₀ : ℕ) {π₁ π₂ : ℝ} (hπ₁ : 0 < π₁) (hπ₂ : 0 < π₂) (R : ℝ) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
      (m₀ : ℝ) * δ ≤ 1 ∧ 32 * ((m₀ : ℝ) * δ) ≤ π₁ ^ 2 ∧ 32 * ((m₀ : ℝ) * δ) * R ≤ π₂
      ∧ 9 * (1024 * δ) ≤ 1 / 80000 := by
  have hD : (0 : ℝ) < (m₀ : ℝ) + 1 := by positivity
  have hR1 : (0 : ℝ) < |R| + 1 := by positivity
  refine ⟨min (min (1 / ((m₀ : ℝ) + 1)) (π₁ ^ 2 / (32 * ((m₀ : ℝ) + 1))))
    (min (π₂ / (32 * ((m₀ : ℝ) + 1) * (|R| + 1))) (1 / (9 * 1024 * 80000))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)),
    fun δ hδ hle => ?_⟩
  have h1 : δ ≤ 1 / ((m₀ : ℝ) + 1) := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : δ ≤ π₁ ^ 2 / (32 * ((m₀ : ℝ) + 1)) :=
    hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : δ ≤ π₂ / (32 * ((m₀ : ℝ) + 1) * (|R| + 1)) :=
    hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : δ ≤ 1 / (9 * 1024 * 80000) := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have e1 : δ * ((m₀ : ℝ) + 1) ≤ 1 := (le_div_iff₀ hD).mp h1
  have e2 : δ * (32 * ((m₀ : ℝ) + 1)) ≤ π₁ ^ 2 := (le_div_iff₀ (by positivity)).mp h2
  have e3 : δ * (32 * ((m₀ : ℝ) + 1) * (|R| + 1)) ≤ π₂ := (le_div_iff₀ (by positivity)).mp h3
  have hmD : (m₀ : ℝ) * δ ≤ ((m₀ : ℝ) + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
  have hP : 0 ≤ 32 * ((m₀ : ℝ) * δ) := by positivity
  refine ⟨by linarith, by linarith, ?_, by linarith⟩
  calc 32 * ((m₀ : ℝ) * δ) * R ≤ 32 * ((m₀ : ℝ) * δ) * (|R| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [le_abs_self R]) hP
    _ ≤ 32 * (((m₀ : ℝ) + 1) * δ) * (|R| + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hR1.le
    _ = δ * (32 * ((m₀ : ℝ) + 1) * (|R| + 1)) := by ring
    _ ≤ π₂ := e3

end Block

/-! ## 3. The factorisation and one-point clauses at the crossing -/

section Pixel

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing MassGap.TypicalBoundary

variable {N : ℕ}

/-- **The factorisation at the torus-centred composite through at most `m₀` blocks**, eventually in `k`; no
scalar clause. -/
def FacPixelAt (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (m₀ : ℕ) : Prop :=
  ∀ᶠ k in atTop, ∃ m : ℕ, m ≤ m₀ ∧ EffScreenFac hN (2 * (2 ^ (c + k) - 1) + 1)
    (dyBeta (one_le_of_ne_zero hN) k) (refObs (RelativeDecay.stateTD hN c k) O t ℓ k) (ρs k) m

/-- **The factorisations at the two single-site fields through at most `m₀` blocks, and the ratio clause**
`|w₀| √V₀ · |w₁| √V₁ ≤ R √refMomentS` at torus variances about some centres `s₀`, `s₁`. -/
def FacOnePointAt (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (m₀ : ℕ) (R : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ (s₀ s₁ : ℝ) (a b : ℕ), a ≤ m₀ ∧ b ≤ m₀
    ∧ EffScreenFac hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) (O.refl 0).1
      (ρs k) a
    ∧ EffScreenFac hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) O.1 (ρs k) b
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)|
        * Real.sqrt (RelativeDecay.stateTD hN c k (sqDev (O.refl 0).1 s₀))
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)|
          * Real.sqrt (RelativeDecay.stateTD hN c k (sqDev O.1 s₁)))
      ≤ R * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The pixel clause from the factorisation and crossing smallness.** -/
theorem effScreenFacPixel_of_crossing {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π : ℝ} {n : ℕ} {ρs : ℕ → DensE n} {m₀ : ℕ} {δ : ℝ} (hS : FacPixelAt hN c O t ℓ ρs m₀)
    (hδ : 0 ≤ δ) (h1 : (m₀ : ℝ) * δ ≤ 1) (hπ : 0 ≤ π) (h : 32 * ((m₀ : ℝ) * δ) ≤ π ^ 2) :
    EffScreenFacPixel hN c O t ℓ π ρs δ := by
  filter_upwards [hS] with k hk
  obtain ⟨m, hm, hF⟩ := hk
  exact ⟨m, hF, blockFactor_le_of_crossing hm hδ h1 hπ h⟩

/-- **The one-point clause from the factorisations, the ratio clause and crossing smallness.** -/
theorem effScreenFacOnePoint_of_crossing {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π : ℝ} {n : ℕ} {ρs : ℕ → DensE n} {m₀ : ℕ} {R δ : ℝ}
    (hS : FacOnePointAt hN c O t ℓ ρs m₀ R) (hδ : 0 ≤ δ) (h1 : (m₀ : ℝ) * δ ≤ 1)
    (h : 32 * ((m₀ : ℝ) * δ) * R ≤ π) : EffScreenFacOnePoint hN c O t ℓ π ρs δ := by
  filter_upwards [hS] with k hk
  obtain ⟨s₀, s₁, a, b, ha, hb, hF₀, hF₁, hR⟩ := hk
  have fa : (a : ℝ) * δ ≤ m₀ * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast ha) hδ
  have fb : (b : ℝ) * δ ≤ m₀ * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hδ
  have hA : Real.sqrt (1 - Real.exp (-(2 * (a * δ)))) * (1 + Real.exp (a * δ))
      ≤ Real.sqrt (32 * ((m₀ : ℝ) * δ)) :=
    (blockFactor_le_sqrt (by positivity) (fa.trans h1)).trans (Real.sqrt_le_sqrt (by linarith))
  have hB : Real.sqrt (1 - Real.exp (-(2 * (b * δ)))) * (1 + Real.exp (b * δ))
      ≤ Real.sqrt (32 * ((m₀ : ℝ) * δ)) :=
    (blockFactor_le_sqrt (by positivity) (fb.trans h1)).trans (Real.sqrt_le_sqrt (by linarith))
  refine ⟨_, _, s₀, s₁, a, b, hF₀, hF₁, le_rfl, le_rfl, ?_⟩
  exact prod_le_of_factors (by positivity) hA hB (by positivity) (abs_nonneg _)
    (abs_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hR (Real.sqrt_nonneg _) h

end Pixel

/-! ## 4. The pinned path from one crossing Prop -/

section Pinned

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing

variable {N : ℕ}

end Pinned

end MassGap.CrossingUnify

end

#print axioms MassGap.CrossingUnify.unitOsc_mono
#print axioms MassGap.CrossingUnify.crossingUnitOsc_of_crossingSmall
#print axioms MassGap.CrossingUnify.crossDens_banded
#print axioms MassGap.CrossingUnify.blockFactor_le_sqrt
#print axioms MassGap.CrossingUnify.blockFactor_le
#print axioms MassGap.CrossingUnify.blockFactor_le_of_crossing
#print axioms MassGap.CrossingUnify.prod_le_of_factors
#print axioms MassGap.CrossingUnify.crossing_threshold
#print axioms MassGap.CrossingUnify.effScreenFacPixel_of_crossing
#print axioms MassGap.CrossingUnify.effScreenFacOnePoint_of_crossing
