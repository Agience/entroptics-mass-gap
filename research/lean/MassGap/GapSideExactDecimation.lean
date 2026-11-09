import Mathlib
import MassGap.GapSideSheetPolymerWrap

/-!
# MassGap.GapSideExactDecimation — the exact decimation carries the sheet: the vortex free energy is the effective one, with no remainder

`GapSideVortexAntiDiagonal` decimates after Migdal–Kadanoff bond moving, which truncates the effective action to
one plaquette weight; the step remainder `Σ (holderExcessTw − holderExcess)` is the price of that truncation.
This module decimates without bond moving. The fine links off the coarse skeleton are integrated out exactly,
so `Z` and `Z^tw` are kept exactly, and the vortex free energy of the fine torus equals that of the effective
density on the coarse torus. All content moves into the effective density at the crossing scale.

## The objects

* `effDens μr glue E ρ`: for a measure-preserving `glue : Ωc × Ωr → Ωf` and a background map `E : Bc → Bf`,
  the effective density `ζ, V ↦ ∫ ρ(E ζ, glue(V, R)) dμr(R)`.
* `glueStep n`: the full parametrisation of the fine links of the side-`2n` 4-torus by the coarse links `V`, the
  second fine link `u₂` of each coarse line, the four interior links of each block and the remaining fine
  links (`MovedTorusDecimation.asm`); the first line link is `u₁ = V u₂⁻¹`, so the coarse link is the product
  `u₁ u₂` of the two fine links on its line. No link is dropped and no plaquette is moved.
* `pullTw`: the pullback of a coarse plaquette background along the cellular map `x ↦ ⌊x/2⌋`: the coarse value
  sits on the fine plaquette `(i, j)` at `x` iff `x_i` and `x_j` are odd.
* `fineDens Φ ζ U = exp(−Σ_q Φ(ζ_q hol_q U))`: the fine density of the class field `Φ` at the background `ζ`, on
  every fine plaquette.
* `effIter k n ρ`: `k` exact steps, from side `sideOf k n = 2^k n` to side `n`. `ZE`, `FE`: the partition
  function and the vortex free energy `−log(Z(ζ)/Z(1))` of a density family.

## What is proved

* **Generic exact step** (`integral_glue`, `Z_effDens`, `integrable_effDens`, `freeE_effDens`): for any
  measure-preserving `glue` from a product measure, `∫ ρ_eff(ζ) = ∫ ρ(E ζ)` and the free energies agree.
  `effDens_covariant`: if a fine move `φf` carries the background `E ζ'` to `E ζ` and acts through `glue` as a
  coarse move `φc` times a measure-preserving map of the integrated variables, then
  `ρ_eff(ζ', V) = ρ_eff(ζ, φc V)`.
* **The gauge instance.** `measurePreserving_glueStep`. `pullTw_sheetAt`: the pullback of the sheet at
  coarse position `(u, v)` is the fine sheet at `(2u + 1, 2v + 1)`; `pullIter_sheetAt`: after `k` steps it is
  the sheet at `(2^k (u+1) − 1, 2^k (v+1) − 1)`. `effIter_spec`: `Z_{fine}(pullIter ζ) = Z_{eff}(ζ)`, at every
  background, for every density family integrable at every background.
* **The twist passes to the coarse level** (`Z_twist_passes`): `Z^tw` of the fine torus of side `2^k n` with
  the 't Hooft sheet equals the `k`-step effective partition function with the coarse sheet as its background.
  The fine sheet is moved to the pulled-back position by a centre relabelling
  (`GapSideSheetPolymerWrap.sheet_mul_thol_eq`, `GapSideSheetPolymer.integral_twist_coboundary`; `−1` is
  central). **`vortex_exact`**: `FE_fine(2^k n) = FE_eff(n)`, no remainder.
  **`vortexF_crossing_exact`**: `vortexF C i P (2^{k+2}) = FE(effIter k 4 (fineDens h_i), sheet_P)`.
* **The end condition** (`abs_FE_le_polymer`): for an effective density of the form
  `exp(−Σ_q φ(ζ_q hol_q V) + Σ_X R_X(ζ, V))`, with `ζ = 1` off a plaquette set `T`, `R_X(ζ) = R_X(1)` when the
  support of `X` misses `T`, `|φ(ζ_q g) − φ(g)| ≤ δ` on `T` and `|R_X(ζ) − R_X(1)| ≤ D_X`,
  `|FE| ≤ |T| δ + Σ_{q ∈ T} Σ_{X ∋ q} D_X`: only the twist-odd part of the polymers that touch the sheet counts.
  `FE_const`: the unit control (constant weight, no polymers) gives `FE = 0` from the same bound.
* **The new input and the feed.** `ExactEffectiveSmall ε` (below). `vortexF_le_of_exactEffectiveSmall`:
  it gives `F(W₀, 2^{k+2}) ≤ ε` at the first crossing; `sectorSeed_of_exactEffectiveSmall`: with `9ε ≤ 1/80000` and `SectorRest` it gives
  `FirstCrossingSectorSeed`, with no `VortexChainEnd` input.

## The new open input

`ExactEffectiveSmall ε`: eventually in `β`, at the first crossing `k`, for every sheet plane `P`, the `k`-step
exact effective density of the Wilson torus of side `2^{k+2}` at weight `W₀` of the chain from `2β`, on the
side-`4` torus, has the polymer form above (polymers indexed by their plaquette supports, each `R_X` depending
on the background only on `X`), with effective plaquette odd oscillation `δ` and per-plaquette odd polymer sum
`η` on the sheet, and `32(δ + η) ≤ ε`.

Relation to the old input (proved): `ExactEffectiveSmall ε → F(W₀, 2^{k+2}) ≤ ε → VortexStepNet ε`. Relation
(argued, not formalised): on the side-`4` torus every plaquette set is a polymer, and the one-polymer
representation (`X = univ`, `R = log ρ_k + Σ φ`, `φ = 0`) is always available, so the Prop holds whenever
`sup_V |log ρ_k(sheet, V) − log ρ_k(1, V)| ≤ ε/32`; conversely every admissible representation bounds that sup
by `32(δ + η) ≤ ε`. The Prop is the pointwise ratio bound up to the factor `32`, a statement about one density
at one scale, and the locality clause is degenerate at side `4`. `F` is minus the log of the untwisted average
of the same ratio, so the Prop is strictly stronger than `F(W₀, 2^{k+2}) ≤ ε`. It is a STRENGTHENING, not a
reduction: the bare bound `F(W₀, 2^{k+2}) ≤ ε` at the first crossing already feeds
`fluxShareN_zero_le_of_vortex`, and `ExactEffectiveSmall` is a pointwise form of it. The local content would be
a representation of the effective action at scale `k` with volume-uniform polymer bounds (Bałaban type) whose
restriction is the side-`4` density; this module does not supply it.

Comparison with Bałaban's bounds (argued; cited from the literature, not in this tree), which band
each block-spin density between
`χ_k exp[−A/g_k² − E₋|T|]` and `exp(E₊|T|)` at small running coupling. That is the small-field, weak-coupling
regime; `ExactEffectiveSmall` asks for the small-activity (strong-coupling) regime of the same exact effective
density at the scale where Migdal–Kadanoff crosses. No published result gives the crossover from one to the
other; that crossover is the content.

## Controls

* Unit (proved, `FE_const`): a constant weight with no polymers has `FE = 0`.
* `U(1)` (argued): the exact steps and `effDens_covariant` hold for any compact group; only the sheet class
  uses `SU(2)`. For `U(1)` the effective action stays Coulomb at every scale (the effective coupling does not
  grow), so the twist-odd part of the effective action stays of order the effective `β`, which does not shrink, and the pointwise
  ratio bound fails: the analogue of `ExactEffectiveSmall` fails at the clause `32(δ + η) ≤ ε` in every
  representation, consistent with the positive twisted action of a commutative group. If the `U(1)` chain has no first crossing the hypothesis is empty,
  the Prop holds vacuously and the control shows nothing.

## Not reached

The bound `F(W, 4) ≤ 4 d⁴` for a crossed class weight, for an effective
density with polymers: its proof runs through the class-weight transfer of a product of plaquette weights,
which a polymer factor breaks. The covariance of the gauge instance (`pullTw` is a chain map, and the centre
field `pullTw χ` acts through `glueStep` as `χ` on `V` and a Haar-preserving map on the rest) is (argued) the
hypothesis of `effDens_covariant`; it is not used by any theorem here, since the sheet class is moved on the
finest torus only.

DERIVED (module-wide): `2` the block factor; `2u + 1` the odd fine coordinate of the coarse cell `u` under
`x ↦ ⌊x/2⌋`; `2^k (u+1) − 1` its `k`-fold iterate; `4` the crossing side and `2^{k+2} = 2^k · 4`;
`32 = 2 · 4²` the sheet count at side `4` (`GapSideSheetPolymer.card_sheetSet_le`); `9` and `1/80000` from
`GapSideVortexAntiDiagonal.fluxShareN_zero_le_of_vortex` and `FirstCrossingSectorSeed`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.GapSideExactDecimation

open MeasureTheory Set Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing
  MassGap.ElectricStepChain MassGap.MovedTorusDecimation MassGap.ElectricExactProof
  MassGap.GapSideVortexAntiDiagonal MassGap.WilsonChainExists
open MassGap.TwistedTraceBound (negOne coe_negOne)

/-! ## 1. The generic exact step -/

section Abstract

variable {Ωf Ωc Ωr Bf Bc : Type*} [MeasurableSpace Ωf] [MeasurableSpace Ωc] [MeasurableSpace Ωr]

/-- **The effective density** of `ρ` under `glue`, at the coarse background `ζ`:
`ρ_eff(ζ, V) = ∫ ρ(E ζ, glue(V, R)) dμr(R)`. -/
def effDens (μr : Measure Ωr) (glue : Ωc × Ωr → Ωf) (E : Bc → Bf) (ρ : Bf → Ωf → ℝ) :
    Bc → Ωc → ℝ :=
  fun ζ V => ∫ R, ρ (E ζ) (glue (V, R)) ∂μr

/-- The vortex free energy `−log(Z(tw)/Z(one))` of a density family. -/
def freeE {Ω B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ρ : B → Ω → ℝ) (tw one : B) : ℝ :=
  -Real.log ((∫ U, ρ tw U ∂μ) / ∫ U, ρ one U ∂μ)

variable {μf : Measure Ωf} {μc : Measure Ωc} {μr : Measure Ωr} [SFinite μc] [SFinite μr]
  {glue : Ωc × Ωr → Ωf}

/-- **Integrating the rest, then the coarse variables**, is integrating the fine variables. -/
theorem integral_glue (hg : MeasurePreserving glue (μc.prod μr) μf) {f : Ωf → ℝ}
    (hf : Integrable f μf) :
    ∫ V, ∫ R, f (glue (V, R)) ∂μr ∂μc = ∫ U, f U ∂μf := by
  have h1 : Integrable (f ∘ glue) (μc.prod μr) := hg.integrable_comp_of_integrable hf
  have h2 : ∫ z, f (glue z) ∂(μc.prod μr) = ∫ U, f U ∂μf := by
    have hm : AEStronglyMeasurable f (Measure.map glue (μc.prod μr)) := by
      rw [hg.map_eq]; exact hf.aestronglyMeasurable
    rw [← integral_map hg.measurable.aemeasurable hm, hg.map_eq]
  rw [← h2]
  exact (integral_prod (f ∘ glue) h1).symm

/-- **The exact step keeps `Z`**: `∫ ρ_eff(ζ) dμc = ∫ ρ(E ζ) dμf`. -/
theorem Z_effDens (hg : MeasurePreserving glue (μc.prod μr) μf) (ρ : Bf → Ωf → ℝ) (E : Bc → Bf)
    (ζ : Bc) (hρ : Integrable (ρ (E ζ)) μf) :
    ∫ V, effDens μr glue E ρ ζ V ∂μc = ∫ U, ρ (E ζ) U ∂μf :=
  integral_glue hg hρ

/-- The effective density is integrable. -/
theorem integrable_effDens (hg : MeasurePreserving glue (μc.prod μr) μf) (ρ : Bf → Ωf → ℝ)
    (E : Bc → Bf) (ζ : Bc) (hρ : Integrable (ρ (E ζ)) μf) :
    Integrable (effDens μr glue E ρ ζ) μc :=
  (hg.integrable_comp_of_integrable hρ).integral_prod_left

/-- **The exact step keeps the vortex free energy.** -/
theorem freeE_effDens (hg : MeasurePreserving glue (μc.prod μr) μf) (ρ : Bf → Ωf → ℝ) (E : Bc → Bf)
    (tw one : Bc) (htw : Integrable (ρ (E tw)) μf) (hone : Integrable (ρ (E one)) μf) :
    freeE μc (effDens μr glue E ρ) tw one = freeE μf ρ (E tw) (E one) := by
  unfold freeE
  rw [← integral_glue hg htw, ← integral_glue hg hone]
  rfl

/-- **Covariance passes to the coarse level.** If the fine move `φf` carries the background `E ζ'` to `E ζ`
and acts through `glue` as the coarse move `φc` times a measure-preserving map of the integrated variables,
then `ρ_eff(ζ', V) = ρ_eff(ζ, φc V)`. -/
theorem effDens_covariant (E : Bc → Bf) (ρ : Bf → Ωf → ℝ) {ζ ζ' : Bc} {φc : Ωc → Ωc}
    {φf : Ωf → Ωf} (m : Ωc → Ωr ≃ᵐ Ωr) (hm : ∀ V, MeasurePreserving (m V) μr μr)
    (hρ : ∀ U, ρ (E ζ') U = ρ (E ζ) (φf U))
    (hint : ∀ V R, φf (glue (V, R)) = glue (φc V, m V R)) (V : Ωc) :
    effDens μr glue E ρ ζ' V = effDens μr glue E ρ ζ (φc V) := by
  unfold effDens
  calc ∫ R, ρ (E ζ') (glue (V, R)) ∂μr = ∫ R, ρ (E ζ) (glue (φc V, m V R)) ∂μr :=
        integral_congr_ae (Eventually.of_forall fun R =>
          (hρ (glue (V, R))).trans (congrArg (ρ (E ζ)) (hint V R)))
    _ = ∫ R, ρ (E ζ) (glue (φc V, R)) ∂μr :=
        (hm V).integral_comp' (fun R => ρ (E ζ) (glue (φc V, R)))

end Abstract

/-! ## 2. The gauge instance: the side-`2n` 4-torus onto the side-`n` torus, no bond moving -/

section Gauge

/-- Product Haar measure on the links of the side-`N` 4-torus. -/
abbrev piL (N : ℕ) : Measure (TLink 4 N → SU 2) := Measure.pi fun _ : TLink 4 N => probHaar (SU 2)

/-- The block-interior part of `MovedTorusDecimation.cfgMeasure`. -/
abbrev blkM (n : ℕ) : Measure (TSite 4 n × Plane → (SU 2 × SU 2) × (SU 2 × SU 2)) :=
  Measure.pi fun _ : TSite 4 n × Plane =>
    ((probHaar (SU 2)).prod (probHaar (SU 2))).prod ((probHaar (SU 2)).prod (probHaar (SU 2)))

/-- The remaining-links part of `MovedTorusDecimation.cfgMeasure`. -/
abbrev freeM (n : ℕ) : Measure (Free n → SU 2) := Measure.pi fun _ : Free n => probHaar (SU 2)

/-- **The integrated-out fine variables**: the second fine link of each coarse line, the four interior links
of each block, and the remaining fine links. -/
abbrev RestV (n : ℕ) : Type :=
  (TLink 4 n → SU 2) × ((TSite 4 n × Plane → (SU 2 × SU 2) × (SU 2 × SU 2)) × (Free n → SU 2))

/-- Product Haar measure on the integrated-out fine variables. -/
abbrev restM (n : ℕ) : Measure (RestV n) := (piL n).prod ((blkM n).prod (freeM n))

/-- **The fine configuration from the coarse links and the rest**: the line of the coarse link `l` carries
`(V_l u₂_l⁻¹, u₂_l)`, so `V_l = u₁ u₂` is the product of the two fine links on the line. -/
def glueStep (n : ℕ) (z : (TLink 4 n → SU 2) × RestV n) : TLink 4 (2 * n) → SU 2 :=
  asm (((MeasurableEquiv.arrowProdEquivProdArrow (SU 2) (SU 2) (TLink 4 n)).symm
    (z.1 / z.2.1, z.2.1), z.2.2.1), z.2.2.2)

/-- **The parametrisation is measure-preserving**: product Haar measure on the coarse links and the rest is
product Haar measure on all fine links. -/
theorem measurePreserving_glueStep (n : ℕ) :
    MeasurePreserving (glueStep n) ((piL n).prod (restM n)) (piL (2 * n)) := by
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (piL n) (piL n) ((blkM n).prod (freeM n)))
  have hb := (measurePreserving_div_prod (piL n) (piL n)).prod
    (MeasurePreserving.id ((blkM n).prod (freeM n)))
  have hc := (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow (SU 2) (SU 2) (TLink 4 n))
    (measurePreserving_arrowProdEquivProdArrow (SU 2) (SU 2) (TLink 4 n)
      (fun _ => probHaar (SU 2)) (fun _ => probHaar (SU 2)))).prod
    (MeasurePreserving.id ((blkM n).prod (freeM n)))
  have hd := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc
      (Measure.pi fun _ : TLink 4 n => (probHaar (SU 2)).prod (probHaar (SU 2))) (blkM n) (freeM n))
  have he := measurePreserving_asm (n := n) (G := SU 2)
  exact he.comp (hd.comp (hc.comp (hb.comp ha)))

/-- The coarse site of a fine site under `x ↦ ⌊x/2⌋`. -/
def halfSite {n : ℕ} (x : TSite 4 (2 * n)) : TSite 4 n :=
  fun k => ⟨(x k).val / 2, by have := (x k).isLt; omega⟩

/-- **The pullback of a coarse plaquette background** along `x ↦ ⌊x/2⌋`: the coarse value sits on the fine
plaquette `(i, j)` at `x` iff `x_i` and `x_j` are odd; elsewhere `1`. -/
def pullTw {n : ℕ} (ζ : TPlaq 4 n → SU 2) (q : TPlaq 4 (2 * n)) : SU 2 :=
  if (q.2 q.1.1).val % 2 = 1 ∧ (q.2 q.1.2).val % 2 = 1 then ζ (q.1, halfSite q.2) else 1

theorem pullTw_one {n : ℕ} : pullTw (n := n) (fun _ => (1 : SU 2)) = fun _ => 1 := by
  funext q
  unfold pullTw
  split_ifs <;> rfl

/-- **The pulled-back sheet**: the coarse sheet at position `(u, v)` pulls back to the fine sheet at
`(2u + 1, 2v + 1)`. -/
theorem pullTw_sheetAt {n : ℕ} (a b : Fin 4) (u v : ℕ) :
    pullTw (n := n) (GapSideSheetPolymerWrap.sheetAt a b u v)
      = GapSideSheetPolymerWrap.sheetAt a b (2 * u + 1) (2 * v + 1) := by
  funext q
  obtain ⟨⟨i, j⟩, x⟩ := q
  unfold pullTw GapSideSheetPolymerWrap.sheetAt
  by_cases ho : (i, j) = (a, b) ∨ (i, j) = (b, a)
  · have hij : ((x i).val % 2 = 1 ∧ (x j).val % 2 = 1) ↔ ((x a).val % 2 = 1 ∧ (x b).val % 2 = 1) := by
      rcases ho with h | h <;> obtain ⟨h1, h2⟩ := Prod.mk.inj h <;> (rw [h1, h2]; try tauto)
    have hiff : ((x i).val % 2 = 1 ∧ (x j).val % 2 = 1) ∧ ((x a).val / 2 = u ∧ (x b).val / 2 = v)
        ↔ ((x a).val = 2 * u + 1 ∧ (x b).val = 2 * v + 1) := by
      rw [hij]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    simp only [ho, true_and, halfSite]
    rw [← ite_and]
    exact if_congr hiff rfl rfl
  · simp only [ho, false_and, ite_self, ↓reduceIte]

/-- The side after `k` steps from side `n`: `sideOf k n = 2^k n` (`sideOf_eq`). -/
def sideOf : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => sideOf k (2 * n)

theorem sideOf_eq (k n : ℕ) : sideOf k n = 2 ^ k * n := by
  induction k generalizing n with
  | zero => simp [sideOf]
  | succ k ih =>
    show sideOf k (2 * n) = 2 ^ (k + 1) * n
    rw [ih]
    ring

/-- A density family on the side-`N` torus, indexed by the plaquette background. -/
abbrev DensE (N : ℕ) : Type := (TPlaq 4 N → SU 2) → (TLink 4 N → SU 2) → ℝ

/-- **One exact step**: the effective density on the side-`n` torus of a family on the side-`2n` torus. -/
def effStep (n : ℕ) (ρ : DensE (2 * n)) : DensE n :=
  effDens (restM n) (glueStep n) pullTw ρ

/-- **`k` exact steps**, from side `sideOf k n` to side `n`. -/
def effIter : (k n : ℕ) → DensE (sideOf k n) → DensE n
  | 0, _, ρ => ρ
  | k + 1, n, ρ => effStep n (effIter k (2 * n) ρ)

/-- The `k`-fold pullback of a background, from side `n` to side `sideOf k n`. -/
def pullIter : (k n : ℕ) → (TPlaq 4 n → SU 2) → (TPlaq 4 (sideOf k n) → SU 2)
  | 0, _, ζ => ζ
  | k + 1, n, ζ => pullIter k (2 * n) (pullTw ζ)

theorem pullIter_one : ∀ k n : ℕ, pullIter k n (fun _ => (1 : SU 2)) = fun _ => 1
  | 0, _ => rfl
  | k + 1, n => by
    show pullIter k (2 * n) (pullTw fun _ => 1) = _
    rw [pullTw_one]
    exact pullIter_one k (2 * n)

/-- **The `k`-fold pullback of a positioned sheet.** -/
theorem pullIter_sheetAt : ∀ (k n : ℕ) (a b : Fin 4) (u v : ℕ),
    pullIter k n (GapSideSheetPolymerWrap.sheetAt a b u v)
      = GapSideSheetPolymerWrap.sheetAt a b (2 ^ k * (u + 1) - 1) (2 ^ k * (v + 1) - 1)
  | 0, n, a, b, u, v => by
    simp [pullIter]
    rfl
  | k + 1, n, a, b, u, v => by
    show pullIter k (2 * n) (pullTw (GapSideSheetPolymerWrap.sheetAt a b u v)) = _
    rw [pullTw_sheetAt, pullIter_sheetAt k (2 * n)]
    have e1 : 2 ^ k * (2 * u + 1 + 1) = 2 ^ (k + 1) * (u + 1) := by ring
    have e2 : 2 ^ k * (2 * v + 1 + 1) = 2 ^ (k + 1) * (v + 1) := by ring
    rw [e1, e2]
    rfl

/-- The partition function of a density family at the background `ζ`. -/
def ZE {N : ℕ} (ρ : DensE N) (ζ : TPlaq 4 N → SU 2) : ℝ := ∫ U, ρ ζ U ∂(piL N)

/-- The vortex free energy of a density family: `−log(Z(ζ)/Z(1))`. -/
def FE {N : ℕ} (ρ : DensE N) (ζ : TPlaq 4 N → SU 2) : ℝ := -Real.log (ZE ρ ζ / ZE ρ (fun _ => 1))

/-- **`k` exact steps keep `Z` at every background**, and every effective density is integrable. -/
theorem effIter_spec : ∀ (k n : ℕ) (ρ : DensE (sideOf k n)),
    (∀ ζ, Integrable (ρ ζ) (piL (sideOf k n))) →
    ∀ ζ, Integrable (effIter k n ρ ζ) (piL n) ∧ ZE (effIter k n ρ) ζ = ZE ρ (pullIter k n ζ)
  | 0, _, _, hρ, ζ => ⟨hρ ζ, rfl⟩
  | k + 1, n, ρ, hρ, ζ => by
    have ih := effIter_spec k (2 * n) ρ hρ (pullTw ζ)
    refine ⟨?_, ?_⟩
    · exact integrable_effDens (measurePreserving_glueStep n) (effIter k (2 * n) ρ) pullTw ζ ih.1
    · exact (Z_effDens (measurePreserving_glueStep n) (effIter k (2 * n) ρ) pullTw ζ ih.1).trans ih.2

/-- **The fine density of a class field `Φ`** at the background `ζ`, on every fine plaquette. -/
def fineDens {N : ℕ} (Φ : SU 2 → ℝ) : DensE N :=
  fun ζ U => Real.exp (-fAct (fun q g => Φ (ζ q * g)) U)

theorem continuous_fineDens {N : ℕ} {Φ : SU 2 → ℝ} (hΦ : Continuous Φ) (ζ : TPlaq 4 N → SU 2) :
    Continuous (fineDens (N := N) Φ ζ) :=
  Real.continuous_exp.comp (GapSideCrossover.continuous_fAct_of
    (fun _ => hΦ.comp (continuous_const.mul continuous_id))).neg

theorem integrable_fineDens {N : ℕ} {Φ : SU 2 → ℝ} (hΦ : Continuous Φ) (ζ : TPlaq 4 N → SU 2) :
    Integrable (fineDens (N := N) Φ ζ) (piL N) :=
  MovedTorusDecimation.integrable_of_continuous (continuous_fineDens hΦ ζ)

/-- **The sheet class on the fine torus**: the sheet at `(0, 0)` and the sheet at any `(s, t)` give the same
`Z` (a centre relabelling). -/
theorem ZE_sheet_eq_sheetAt {N : ℕ} {a b : Fin 4} (hab : a ≠ b) (Φ : SU 2 → ℝ) (s t : Fin N) :
    ZE (N := N) (fineDens Φ) (GapSideTwistFlat.sheet a b negOne)
      = ZE (N := N) (fineDens Φ) (GapSideSheetPolymerWrap.sheetAt a b s.val t.val) := by
  obtain ⟨χ, hχ, hq⟩ := GapSideSheetPolymerWrap.sheet_mul_thol_eq hab s t
  have h := GapSideSheetPolymer.integral_twist_coboundary (d := 4) (n := N)
    (fun h => Real.exp (-∑ q, Φ (h q))) (GapSideTwistFlat.sheet a b negOne) χ hχ
  simp only [hq] at h
  exact h

/-- **The twist passes to the coarse level.** The fine torus of side `sideOf k n` with the 't Hooft sheet has
the `Z` of the `k`-step effective density with the coarse sheet as its background. -/
theorem Z_twist_passes (Φ : SU 2 → ℝ) (hΦ : Continuous Φ) (k n : ℕ) (hn : 0 < n) {a b : Fin 4}
    (hab : a ≠ b) :
    ZE (N := sideOf k n) (fineDens Φ) (GapSideTwistFlat.sheet a b negOne)
      = ZE (effIter k n (fineDens Φ)) (GapSideTwistFlat.sheet a b negOne) := by
  have hlt : 2 ^ k - 1 < sideOf k n := by
    rw [sideOf_eq]
    exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) one_pos) (Nat.le_mul_of_pos_right _ hn)
  have hi := effIter_spec k n (fineDens Φ) (fun ζ => integrable_fineDens hΦ ζ)
    (GapSideTwistFlat.sheet a b negOne)
  have e1 : pullIter k n (GapSideTwistFlat.sheet a b negOne)
      = GapSideSheetPolymerWrap.sheetAt a b (2 ^ k - 1) (2 ^ k - 1) := by
    rw [GapSideSheetPolymerWrap.sheet_eq_sheetAt, pullIter_sheetAt]
    simp
  rw [hi.2, e1]
  exact ZE_sheet_eq_sheetAt hab Φ ⟨2 ^ k - 1, hlt⟩ ⟨2 ^ k - 1, hlt⟩

/-- **The exact anti-diagonal**: the vortex free energy of the fine torus of side `2^k n` is the vortex free
energy of the `k`-step effective density on the side-`n` torus. No remainder. -/
theorem vortex_exact (Φ : SU 2 → ℝ) (hΦ : Continuous Φ) (k n : ℕ) (hn : 0 < n) {a b : Fin 4}
    (hab : a ≠ b) :
    FE (fineDens Φ) (GapSideTwistFlat.sheet a b negOne : TPlaq 4 (sideOf k n) → SU 2)
      = FE (effIter k n (fineDens Φ)) (GapSideTwistFlat.sheet a b negOne) := by
  have h1 := (effIter_spec k n (fineDens Φ) (fun ζ => integrable_fineDens hΦ ζ) (fun _ => 1)).2
  rw [pullIter_one] at h1
  unfold FE
  rw [Z_twist_passes Φ hΦ k n hn hab, ← h1]

/-- The twisted field of weight `1` is the background-shifted field. -/
theorem twistField_one_eq {N : ℕ} (h : SU 2 → ℝ) (ζ : TPlaq 4 N → SU 2) :
    twistField 1 h ζ = fun q g => h (ζ q * g) := by
  funext q g
  simp only [twistField, one_mul]

/-- **The chain's vortex free energy is `FE` of the fine density.** -/
theorem vortexF_eq_FE {β : ℝ} (C : WilsonChain β) (i : ℕ) (P : Plane) (N : ℕ) :
    vortexF C i P N = FE (fineDens (N := N) (halfField (C.W i) suTau))
      (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) := by
  have e1 : Ztw C i P N = ZE (fineDens (N := N) (halfField (C.W i) suTau))
      (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) := by
    unfold Ztw
    rw [twistField_one_eq]
    rfl
  have e2 : Zh C i N = ZE (fineDens (N := N) (halfField (C.W i) suTau)) (fun _ => 1) := by
    have e : uniformField (d := 4) (n := N) (halfField (C.W i) suTau)
        = fun q g => halfField (C.W i) suTau ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g) := by
      funext q g
      simp only [uniformField, one_mul]
    show ZF (probHaar (SU 2)) (uniformField (d := 4) (n := N) (halfField (C.W i) suTau)) = _
    rw [e]
    rfl
  unfold vortexF FE
  rw [e1, e2]

/-- **The Wilson vortex free energy at the first-crossing side is the effective one on the side-`4` torus.** -/
theorem vortexF_crossing_exact {β : ℝ} (C : WilsonChain β) (i : ℕ) (P : Plane) (k : ℕ) :
    vortexF C i P (2 ^ (k + 2)) = FE (effIter k 4 (fineDens (halfField (C.W i) suTau)))
      (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) := by
  have hs : sideOf k 4 = 2 ^ (k + 2) := by rw [sideOf_eq]; ring
  rw [← hs, vortexF_eq_FE]
  exact vortex_exact _ (continuous_halfField C i) k 4 (by norm_num) (ne_of_lt P.2)

end Gauge

/-! ## 3. The end condition: only the twist-odd part of polymers that touch the sheet counts -/

section End

/-- A positive integrand on a probability space has a positive integral. -/
theorem integral_exp_neg_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Ω → ℝ} (hi : Integrable (fun U => Real.exp (-A U)) μ) : 0 < ∫ U, Real.exp (-A U) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun U => (Real.exp_pos _).le) hi]
  rw [show Function.support (fun U => Real.exp (-A U)) = univ from
    Set.eq_univ_of_forall fun U => (Real.exp_pos _).ne', measure_univ]
  exact one_pos

/-- **Two actions within `c` pointwise give log partition functions within `c`.** -/
theorem abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A B : Ω → ℝ) {c : ℝ} (hpt : ∀ U, |A U - B U| ≤ c)
    (hiA : Integrable (fun U => Real.exp (-A U)) μ) (hiB : Integrable (fun U => Real.exp (-B U)) μ) :
    |Real.log (∫ U, Real.exp (-A U) ∂μ) - Real.log (∫ U, Real.exp (-B U) ∂μ)| ≤ c := by
  have hA := integral_exp_neg_pos hiA
  have hB := integral_exp_neg_pos hiB
  have h1 : ∫ U, Real.exp (-A U) ∂μ ≤ Real.exp c * ∫ U, Real.exp (-B U) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hiA (hiB.const_mul _) fun U => ?_
    show Real.exp (-A U) ≤ Real.exp c * Real.exp (-B U)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hpt U)).1])
  have h2 : ∫ U, Real.exp (-B U) ∂μ ≤ Real.exp c * ∫ U, Real.exp (-A U) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hiB (hiA.const_mul _) fun U => ?_
    show Real.exp (-B U) ≤ Real.exp c * Real.exp (-A U)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hpt U)).2])
  have l1 := Real.log_le_log hA h1
  rw [Real.log_mul (Real.exp_pos c).ne' hB.ne', Real.log_exp] at l1
  have l2 := Real.log_le_log hB h2
  rw [Real.log_mul (Real.exp_pos c).ne' hA.ne', Real.log_exp] at l2
  rw [abs_le]
  constructor <;> linarith

variable {N : ℕ}

/-- **The polymer action**: `Σ_q φ(ζ_q hol_q V) − Σ_i R_i(ζ, V)`. -/
def actP {ι : Type} [Fintype ι] (φ : SU 2 → ℝ) (R : ι → (TPlaq 4 N → SU 2) → (TLink 4 N → SU 2) → ℝ)
    (ζ : TPlaq 4 N → SU 2) (V : TLink 4 N → SU 2) : ℝ :=
  fAct (fun q g => φ (ζ q * g)) V - ∑ i, R i ζ V

/-- **The end bound for a polymer density.** For a density `exp(−actP φ R ζ')` at `ζ' = ζ` and `ζ' = 1`, with
`ζ = 1` off `T`, `R_i(ζ) = R_i(1)` whenever the support `S_i` misses `T`, `|φ(ζ_q g) − φ(g)| ≤ δ` on `T` and
`|R_i(ζ) − R_i(1)| ≤ D_i`: `|FE| ≤ |T| δ + Σ_{q ∈ T} Σ_{i : q ∈ S_i} D_i`. -/
theorem abs_FE_le_polymer (ρ : DensE N) (ζ : TPlaq 4 N → SU 2) (T : Finset (TPlaq 4 N))
    (hT : ∀ q ∉ T, ζ q = 1) {ι : Type} [Fintype ι] (φ : SU 2 → ℝ) (S : ι → Finset (TPlaq 4 N))
    (R : ι → (TPlaq 4 N → SU 2) → (TLink 4 N → SU 2) → ℝ)
    (hform : ∀ ζ' : TPlaq 4 N → SU 2, (ζ' = ζ ∨ ζ' = fun _ => 1) → ∀ V,
      ρ ζ' V = Real.exp (-actP φ R ζ' V))
    (hloc : ∀ i, (∀ q ∈ T, q ∉ S i) → ∀ V, R i ζ V = R i (fun _ => 1) V)
    {δ : ℝ} (hδ : ∀ q ∈ T, ∀ g, |φ (ζ q * g) - φ g| ≤ δ)
    (D : ι → ℝ) (hD0 : ∀ i, 0 ≤ D i) (hD : ∀ i V, |R i ζ V - R i (fun _ => 1) V| ≤ D i)
    (hi : ∀ ζ' : TPlaq 4 N → SU 2, (ζ' = ζ ∨ ζ' = fun _ => 1) → Integrable (ρ ζ') (piL N)) :
    |FE ρ ζ| ≤ T.card * δ + ∑ q ∈ T, ∑ i, (if q ∈ S i then D i else 0) := by
  have hZ : ∀ ζ' : TPlaq 4 N → SU 2, (ζ' = ζ ∨ ζ' = fun _ => 1) →
      ZE ρ ζ' = ∫ V, Real.exp (-actP φ R ζ' V) ∂(piL N) := fun ζ' hζ' =>
    integral_congr_ae (Eventually.of_forall fun V => hform ζ' hζ' V)
  have hiA : ∀ ζ' : TPlaq 4 N → SU 2, (ζ' = ζ ∨ ζ' = fun _ => 1) →
      Integrable (fun V => Real.exp (-actP φ R ζ' V)) (piL N) := fun ζ' hζ' =>
    (hi ζ' hζ').congr (Eventually.of_forall fun V => hform ζ' hζ' V)
  have hnn : ∀ i q, 0 ≤ (if q ∈ S i then D i else 0) := fun i q => by
    split_ifs
    exacts [hD0 i, le_rfl]
  have hR1 : ∀ i V, |R i ζ V - R i (fun _ => 1) V| ≤ ∑ q ∈ T, (if q ∈ S i then D i else 0) := by
    intro i V
    by_cases hm : ∃ q ∈ T, q ∈ S i
    · obtain ⟨q0, hq0, hqS⟩ := hm
      calc |R i ζ V - R i (fun _ => 1) V| ≤ D i := hD i V
        _ = (if q0 ∈ S i then D i else 0) := (if_pos hqS).symm
        _ ≤ ∑ q ∈ T, (if q ∈ S i then D i else 0) :=
          Finset.single_le_sum (f := fun q => if q ∈ S i then D i else 0) (fun q _ => hnn i q) hq0
    · push Not at hm
      rw [hloc i hm V, sub_self, abs_zero]
      exact Finset.sum_nonneg fun q _ => hnn i q
  have hact : ∀ V, |fAct (fun q g => φ (ζ q * g)) V
      - fAct (fun q g => φ ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g)) V| ≤ T.card * δ := by
    intro V
    refine GapSideSheetPolymer.fAct_sub_abs_le
      (fun q g => φ ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g)) (fun q g => φ (ζ q * g)) T ?_ ?_ V
    · intro q hq
      funext g
      simp only [hT q hq]
    · intro q hq g
      simp only [one_mul]
      exact hδ q hq g
  have hpt : ∀ V, |actP φ R ζ V - actP φ R (fun _ => 1) V|
      ≤ T.card * δ + ∑ q ∈ T, ∑ i, (if q ∈ S i then D i else 0) := by
    intro V
    have h2 : |∑ i, R i ζ V - ∑ i, R i (fun _ => 1) V|
        ≤ ∑ q ∈ T, ∑ i, (if q ∈ S i then D i else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hR1 i V).trans ?_
      exact (Finset.sum_comm).le
    have e : actP φ R ζ V - actP φ R (fun _ => 1) V
        = (fAct (fun q g => φ (ζ q * g)) V
            - fAct (fun q g => φ ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g)) V)
          - (∑ i, R i ζ V - ∑ i, R i (fun _ => 1) V) := by
      unfold actP
      ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (hact V) h2)
  unfold FE
  rw [hZ ζ (Or.inl rfl), hZ (fun _ => 1) (Or.inr rfl),
    Real.log_div (integral_exp_neg_pos (hiA ζ (Or.inl rfl))).ne'
      (integral_exp_neg_pos (hiA _ (Or.inr rfl))).ne', abs_neg]
  exact abs_log_integral_exp_sub_le (piL N) (actP φ R ζ) (actP φ R (fun _ => 1)) hpt
    (hiA ζ (Or.inl rfl)) (hiA _ (Or.inr rfl))

/-- **Unit control**: a constant weight with no polymers has `FE = 0` at every background, from the same
bound. -/
theorem FE_const (c : ℝ) (ζ : TPlaq 4 N → SU 2) : FE (fineDens (N := N) (fun _ => c)) ζ = 0 := by
  have h := abs_FE_le_polymer (fineDens (N := N) (fun _ => c)) ζ Finset.univ
    (fun q hq => absurd (Finset.mem_univ q) hq) (ι := Empty) (fun _ => c) (fun i => i.elim)
    (fun i => i.elim)
    (fun ζ' _ V => by simp [fineDens, actP])
    (fun i => i.elim) (δ := 0) (fun q _ g => by simp) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun ζ' _ => integrable_fineDens continuous_const ζ')
  simp only [mul_zero, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, add_zero] at h
  exact abs_nonpos_iff.mp h

/-- The sheet is `1` off `sheetSet`. -/
theorem sheet_off (a b : Fin 4) (q : TPlaq 4 N) (hq : q ∉ GapSideSheetPolymer.sheetSet a b) :
    GapSideTwistFlat.sheet a b negOne q = 1 := by
  simp only [GapSideSheetPolymer.sheetSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  unfold GapSideTwistFlat.sheet
  rw [if_neg hq]

/-- The sheet is `−1` on `sheetSet`. -/
theorem sheet_on (a b : Fin 4) (q : TPlaq 4 N) (hq : q ∈ GapSideSheetPolymer.sheetSet a b) :
    GapSideTwistFlat.sheet a b negOne q = negOne := by
  simp only [GapSideSheetPolymer.sheetSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  unfold GapSideTwistFlat.sheet
  rw [if_pos hq]

end End

/-! ## 4. The new input: the exact effective density at the crossing is small -/

section Net

/-- **The polymer form** of a density family at the background `ζ` and at `1`, with polymers indexed by their
plaquette supports. -/
def EffForm {N : ℕ} (ρ : DensE N) (φ : SU 2 → ℝ)
    (R : Finset (TPlaq 4 N) → (TPlaq 4 N → SU 2) → (TLink 4 N → SU 2) → ℝ) (ζ : TPlaq 4 N → SU 2) : Prop :=
  ∀ ζ' : TPlaq 4 N → SU 2, (ζ' = ζ ∨ ζ' = fun _ => 1) → ∀ V, ρ ζ' V = Real.exp (-actP φ R ζ' V)

/-- **The exact effective density at the crossing is small.** Eventually in `β`, at the first crossing `k` of
the chain from `2β`, for every sheet plane `P`, the `k`-step exact effective density of the Wilson torus of side
`2^{k+2}` at weight `W₀`, on the side-`4` torus, has the polymer form, each polymer `R_X` depending on the
background only on its support `X`, with effective plaquette odd oscillation `δ`, polymer odd parts `D_X`,
per-plaquette sum `Σ_{X ∋ q} D_X ≤ η` on the sheet, and `32(δ + η) ≤ ε`. At side `4` the single polymer
`X = univ` is admissible, so (argued) this is the pointwise bound on `|log ρ_k(sheet, V) − log ρ_k(1, V)|` up
to the factor `32`: a strengthening of `F(W₀, 2^{k+2}) ≤ ε`, not a reduction of it.

DERIVED: `32 = 2 · 4²` the sheet count at side `4` (`GapSideSheetPolymer.card_sheetSet_le`); `4` the
crossing side; `2` the doubled coupling; `0` the finest weight. Inherited: `1/1000` the doubling-defect seed
of `ChainFirstCrossing.FirstCrossingComparison`. -/
def ExactEffectiveSmall (ε : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ P : Plane, ∃ (φ : SU 2 → ℝ) (R : Finset (TPlaq 4 4) → (TPlaq 4 4 → SU 2) → (TLink 4 4 → SU 2) → ℝ)
      (D : Finset (TPlaq 4 4) → ℝ) (δ η : ℝ),
      EffForm (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))) φ R
        (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) ∧
      (∀ X ζ1 ζ2, (∀ q ∈ X, ζ1 q = ζ2 q) → R X ζ1 = R X ζ2) ∧
      (∀ g, |φ (negOne * g) - φ g| ≤ δ) ∧
      (∀ X, 0 ≤ D X) ∧
      (∀ X V, |R X (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) V - R X (fun _ => 1) V| ≤ D X) ∧
      (∀ q ∈ GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2,
        ∑ X, (if q ∈ X then D X else 0) ≤ η) ∧
      0 ≤ η ∧ 32 * (δ + η) ≤ ε

/-- **The new input bounds the Wilson vortex free energy at the first-crossing side.** -/
theorem vortexF_le_of_exactEffectiveSmall {ε : ℝ} (h : ExactEffectiveSmall ε) :
    ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
      (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
      ∀ P : Plane, vortexF (wilsonChainOf (2 * β)) 0 P (2 ^ (k + 2)) ≤ ε := by
  filter_upwards [h] with β hβ
  intro k hk hmin P
  obtain ⟨φ, R, D, δ, η, hform, hloc, hδ, hD0, hD, hη, hη0, hε⟩ := hβ k hk hmin P
  rw [vortexF_crossing_exact]
  have hspec := effIter_spec k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))
    (fun ζ => integrable_fineDens (continuous_halfField (wilsonChainOf (2 * β)) 0) ζ)
  have hb := abs_FE_le_polymer (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau)))
    (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) (GapSideSheetPolymer.sheetSet P.1.1 P.1.2)
    (fun q hq => sheet_off _ _ q hq) φ (fun X => X) R hform
    (fun X hX V => congrFun (hloc X _ _ (fun q hqX => sheet_off _ _ q (fun hqT => hX q hqT hqX))) V)
    (δ := δ) (fun q hq g => by rw [sheet_on _ _ q hq]; exact hδ g) D hD0 hD
    (fun ζ' _ => (hspec ζ').1)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 1)
  have hc : ((GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card : ℝ) ≤ 32 := by
    have h1 : (GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card ≤ 32 :=
      (GapSideSheetPolymer.card_sheetSet_le (N := 4) (ne_of_lt P.2)).trans (by norm_num)
    exact_mod_cast h1
  have hs : ∑ q ∈ GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2,
      ∑ X, (if q ∈ X then D X else 0)
      ≤ (GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card * η := by
    calc _ ≤ ∑ _q ∈ GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2, η := Finset.sum_le_sum hη
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have m1 := mul_le_mul_of_nonneg_right hc hδ0
  have m2 := mul_le_mul_of_nonneg_right hc hη0
  have := le_abs_self (FE (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau)))
    (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne))
  linarith

/-- **The sector seed from the new input**, with the rest of the sectors; no chain-end input is used. -/
theorem sectorSeed_of_exactEffectiveSmall {ε : ℝ} (h : ExactEffectiveSmall ε) (hb : 9 * ε ≤ 1 / 80000)
    (hR : SectorRest) : GapSideTwistFlat.FirstCrossingSectorSeed := by
  unfold GapSideTwistFlat.FirstCrossingSectorSeed
  filter_upwards [vortexF_le_of_exactEffectiveSmall h, hR, eventually_ge_atTop (0 : ℝ)] with β hV hR hβ
  intro k hk hmin i
  obtain ⟨hR1, hR2⟩ := hR k hk hmin
  refine ⟨?_, hR2 i⟩
  by_cases hi : i = 0
  · subst hi
    have hF : ∀ ν : {j : Fin 4 // j ≠ 0},
        vortexF (wilsonChainOf (2 * β)) 0 (plane0 ν) (2 ^ (k + 2)) ≤ max 0 ε :=
      fun ν => le_max_of_le_right (hV k hk hmin (plane0 ν))
    have hfl := fluxShareN_zero_le_of_vortex hβ k (le_max_left 0 ε) hF
    have hm : 9 * max 0 ε ≤ 1 / 80000 := by
      rcases le_total 0 ε with h0 | h0
      · rw [max_eq_right h0]; exact hb
      · rw [max_eq_left h0]; norm_num
    linarith
  · exact hR1 i hi

end Net

end MassGap.GapSideExactDecimation

end

#print axioms MassGap.GapSideExactDecimation.integral_glue
#print axioms MassGap.GapSideExactDecimation.Z_effDens
#print axioms MassGap.GapSideExactDecimation.freeE_effDens
#print axioms MassGap.GapSideExactDecimation.effDens_covariant
#print axioms MassGap.GapSideExactDecimation.measurePreserving_glueStep
#print axioms MassGap.GapSideExactDecimation.pullTw_sheetAt
#print axioms MassGap.GapSideExactDecimation.pullIter_sheetAt
#print axioms MassGap.GapSideExactDecimation.effIter_spec
#print axioms MassGap.GapSideExactDecimation.ZE_sheet_eq_sheetAt
#print axioms MassGap.GapSideExactDecimation.Z_twist_passes
#print axioms MassGap.GapSideExactDecimation.vortex_exact
#print axioms MassGap.GapSideExactDecimation.vortexF_eq_FE
#print axioms MassGap.GapSideExactDecimation.vortexF_crossing_exact
#print axioms MassGap.GapSideExactDecimation.abs_log_integral_exp_sub_le
#print axioms MassGap.GapSideExactDecimation.abs_FE_le_polymer
#print axioms MassGap.GapSideExactDecimation.FE_const
#print axioms MassGap.GapSideExactDecimation.vortexF_le_of_exactEffectiveSmall
#print axioms MassGap.GapSideExactDecimation.sectorSeed_of_exactEffectiveSmall
