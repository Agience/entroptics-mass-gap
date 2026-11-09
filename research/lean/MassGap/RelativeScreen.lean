import Mathlib
import MassGap.ScreenBridge

/-!
# MassGap.RelativeScreen — the screen read relative to the second moment

`ScreenBridge` leaves (1b) at `EffScreenPixel ∧ EffScreenOnePoint`, whose smallness clause compares the
oscillation `δ` of the read observable, an absolute quantity, with `√refMomentS`, which shrinks with the cell
volume. This module replaces the oscillation contraction of a Doeblin minorisation by its variance contraction,
measured under the states, iterates it over layers, and puts it on the pinned path.

## What is proved

* **The variance contraction of a minorised Markov map** (`sq_le_of_quad`, `quad_of_linear`, `minor_sq_le`).
  `L` Markov, `x₀` a reference point, `0 ≤ ε ≤ 1`, and the minorisation at the second moments of one observable
  only: `ε · L((f − t)²)(x₀) ≤ L((f − t)²)(x)` for every centre `t` and every `x`. Then at every `s` and `x`,
  `(L f x − u)² ≤ (1 − ε) · L((f − s)²)(x)`, `u = (1 − ε) s + ε · L f x₀`. No range of `f` enters: the
  minorisation is used only on the three functions `1, f, f²` (discriminant of `t ↦ M((f − s − t)²)`,
  `M = L(·)(x) − ε L(·)(x₀)`).
* **The state form** (`state_le_mul`, `state_sq_le`, `minor_abs_le`, `minor_closing`). For two states invariant
  under `L` at `f` and at `(f − s)²`:
  `|ν₁ f − ν₂ f| ≤ √(1 − ε) · (√ν₁((f − s)²) + √ν₂((f − s)²))`. The error is relative to the observable's own
  second moment in each state.
* **Layers** (`ctr`, `layers_sq_le`, `layers_mean`, `layers_abs_le`, `layers_closing`, `layer_factor_small`).
  A chain `g (i+1) = L i (g i)`, `g 0 = f`, each `L i` Markov, minorised with the same `ε` at the second moments
  of `g i` and invariant for the state at `g i` and every `(g i − t)²`: the second moment of `g j` about the
  centre `ctr j` is at most `(1 − ε)^j` times that of `f` about `s`, and
  `|ν₁ f − ν₂ f| ≤ √((1 − ε)^j) · (√V₁ + √V₂)`. For `ε > 0` the factor tends to `0` in `j`; for every `C` and
  `π > 0` some `j` gives `√((1 − ε)^j) · C ≤ π`.
* **The variance version of `wRead_osc` / `coarseGibbs_osc`** (`wRead_nonneg`, `integrable_sq_mul`, `wRead_quad`,
  `wRead_minor`, `wRead_var`, `coarseGibbs_var`). Two weights with `e^{−c} w ≤ w' ≤ e^c w`:
  `(wRead h w' − u)² ≤ (1 − e^{−2c}) · wRead((h − s)²) w'`, `u = (1 − e^{−2c}) s + e^{−2c} wRead h w`; for a coarse
  Gibbs weight with per-block log-oscillation `c_b`, the same with `c = Σ_b c_b`. The bound reads `h` only through
  its second moment about `s` under the reading; the range `δ` of `h` is absent.
* **The Wilson box** (`LayerBound`, `LayerBound.closing`, `RelScreen`, `layerBound_of_relScreen`).
  `LayerBound hN M β F Δ`: layers of Markov maps invariant for the torus and the infinite-volume state at the
  iterates and their squared deviations, minorised at the second moments of the iterates, with
  `√((1 − ε)^j) (√V_T + √V_∞) ≤ Δ`; it closes the torus against the infinite volume at `Δ`. `RelScreen`: one
  refinement screen `Q` of a box `Λ'` (`ScreenBridge.Refines`), Markov, minorised at `Q ∘ wspec Λ` on the second
  moments of `F`; it gives `LayerBound` with `j = 1` (both state clauses from `Refines`).
* **The factored screen in relative form** (`EffScreenRel`, `relScreen_of_effScreenRel`). The screen of
  `ScreenBridge.EffScreen` with the factorisation asked only at the squared deviations `(F − t)²`, through
  nonnegative bounded interior functions `H t`; no factorisation at `F`, no range `δ`. With `UnitOsc ρ cP cL` and
  `Banded ρ` it gives `RelScreen` with `ε = e^{−2 m cL}`: the minorisation constant contains `m` and `cL` only.
* **The pinned path** (`clay_canonical_layer`, `EffScreenRelPixel`, `EffScreenRelOnePoint`,
  `boundPixel_of_effScreenRel`, `boundOnePoint_of_effScreenRel`, `clay_canonical_unitOsc_rel`).
  `clay_canonical_unitOsc_rel` is `ExistenceReduce.clay_canonical` with `hpos` replaced by `CoarseUnitOsc`,
  `ReadingFloor` and the relative factored screens; `hD`, `hW` unchanged.

## What is not proved

* `hpos ⇐ CoarseUnitOsc + ReadingFloor`: NO. The remainder on this route is
  `EffScreenRelPixel ∧ EffScreenRelOnePoint` minus what `Refines` and `UnitOsc` discharge, i.e. per observable:
  1. the factorisation of a refinement screen through coarse blocks at the squared deviations
     `Q (wspec Λ (F − t)²) ω = wRead μ (H t) (ρ ζ ∘ join (c ω))` (clause 1, weakened: the second moments only);
  2. the moment clause `√(1 − e^{−2 m cL}) (√V_T + √V_∞) ≤ π √refMomentS`, `V = state((F − s)²)`.
* Clause 1 is not removed by the variance form (argued). The variance contraction needs only a minorisation of
  the screen at the observable's second moments (`RelScreen`), not an exact factorisation; but the only source of
  a minorisation constant that does not contain the fine-face count is the coarse reading of `UnitOsc`, and that
  needs the screen's output to be a reweighting by the effective density, which is the factorisation. The
  torus screen `ScreenBridge.coarseQ` reads `f (glueStep (V, R))`, so the integrand itself depends on the coarse
  links `V` and `coarseQ` is not a fixed-integrand reweighting: `wRead_minor` does not apply to it, and a
  minorisation in `V` fails for observables that read `V` (argued). The infinite-volume state is not a reading of
  `coarseQ` either, and `coarseQ` lives on the `SU 2` torus of side `2n`, not on `IConf (SU N)`. The DLR limit
  gives invariance of a refinement screen (`Refines.periodic`), not a minorisation. So the weaker screen
  hypothesis is `RelScreen`, and it is not proved from `coarseQ` plus the DLR limit.
* Clause 2 is now like against like (argued). `V_T`, `V_∞` are second moments of the composite `refObs`, centred
  at one common `s`; `refMomentS` is the second moment of the torus-centred composite `refObs (stateTD)` in the torus (`MomentCompare.refMomentS_eq`). The clause
  holds once `√V_T + √V_∞ ≤ C √refMomentS` with `C` fixed and the contraction factor at most `π / C`; with `j`
  layers at a `k`-uniform `ε` the factor is `(1 − ε)^{j/2}` (`layers_closing`), and `layer_factor_small` gives the
  `j`. Neither the moment comparison (a ratio of the infinite-volume and the torus second moments) nor `j`
  factored layers inside the box are proved; the pinned form uses one layer.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.RelativeScreen

open MeasureTheory Filter MassGap.TypicalBoundary MassGap.CoarseBoundary
open MassGap.DLRLimit (State)

/-! ## 1. The variance contraction of a minorised Markov map -/

section Quad

/-- **A nonnegative quadratic has a nonpositive discriminant**: `A − 2 t a + t² b ≥ 0` for every `t` and
`b ≥ 0` give `a² ≤ b A`. -/
theorem sq_le_of_quad {A a b : ℝ} (hb : 0 ≤ b) (h : ∀ t : ℝ, 0 ≤ A - 2 * t * a + t * t * b) :
    a * a ≤ b * A := by
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · rw [← hb0, zero_mul]
    by_contra hne
    have ha : a ≠ 0 := by
      intro h0
      apply hne
      rw [h0, mul_zero]
    obtain ⟨t, ht⟩ : ∃ t, t = (A + 1) / (2 * a) := ⟨_, rfl⟩
    have hta : t * (2 * a) = A + 1 := by
      rw [ht]
      exact div_mul_cancel₀ _ (mul_ne_zero two_ne_zero ha)
    have e : 2 * t * a = A + 1 := by linear_combination hta
    have h1 := h t
    rw [← hb0, mul_zero, add_zero, e] at h1
    linarith
  · obtain ⟨t, ht⟩ : ∃ t, t = a / b := ⟨_, rfl⟩
    have htb : t * b = a := by
      rw [ht]
      exact div_mul_cancel₀ a hb0.ne'
    have h1 := h t
    have e : t * t * b = t * a := by rw [mul_assoc, htb]
    rw [e] at h1
    have h2 : 0 ≤ b * (A - t * a) := mul_nonneg hb (by linarith)
    have e2 : b * (t * a) = a * a := by
      rw [← htb]
      ring
    have h3 : b * (A - t * a) = b * A - a * a := by rw [mul_sub, e2]
    linarith

end Quad

section Generic

variable {X : Type*} [TopologicalSpace X]

/-- Moving the centre of a squared deviation. -/
theorem sqDev_shift (g : C(X, ℝ)) (r t : ℝ) :
    sqDev g (r + t) = sqDev g r + (-(2 * t)) • g + (2 * t * r + t * t) • (1 : C(X, ℝ)) := by
  ext x
  simp only [sqDev_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul]
  ring

/-- **A linear functional on a squared deviation is quadratic in the centre.** -/
theorem quad_of_linear (φ : C(X, ℝ) → ℝ) (hadd : ∀ f g, φ (f + g) = φ f + φ g)
    (hsmul : ∀ (c : ℝ) f, φ (c • f) = c * φ f) (g : C(X, ℝ)) (r t : ℝ) :
    φ (sqDev g (r + t)) = φ (sqDev g r) - 2 * t * (φ g - r * φ 1) + t * t * φ 1 := by
  rw [sqDev_shift, hadd, hadd, hsmul, hsmul]
  ring

/-- **The variance contraction of a minorised Markov map, pointwise.** A Markov `L` minorised at a reference
point `x₀` on the second moments of `f`, `ε L((f − t)²)(x₀) ≤ L((f − t)²)(x)`, contracts the squared deviation:
`(L f x − u)² ≤ (1 − ε) L((f − s)²)(x)`, `u = (1 − ε) s + ε L f x₀`. -/
theorem minor_sq_le {L : C(X, ℝ) → C(X, ℝ)} (hL : Markov L) (f : C(X, ℝ)) (x₀ : X) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hmin : ∀ t x, ε * L (sqDev f t) x₀ ≤ L (sqDev f t) x)
    (s : ℝ) (x : X) :
    sqDev (L f) ((1 - ε) * s + ε * L f x₀) x ≤ (1 - ε) * L (sqDev f s) x := by
  obtain ⟨φ, hφ⟩ : ∃ φ : C(X, ℝ) → ℝ, φ = fun G => L G x - ε * L G x₀ := ⟨_, rfl⟩
  have hadd : ∀ f g, φ (f + g) = φ f + φ g := fun f g => by
    simp only [hφ, hL.add, ContinuousMap.add_apply]
    ring
  have hsmul : ∀ (c : ℝ) f, φ (c • f) = c * φ f := fun c f => by
    simp only [hφ, hL.smul, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  have h1 : φ 1 = 1 - ε := by
    simp only [hφ, hL.one, ContinuousMap.one_apply]
    ring
  have hq : ∀ t, 0 ≤ φ (sqDev f s) - 2 * t * (φ f - s * (1 - ε)) + t * t * (1 - ε) := fun t => by
    have e := quad_of_linear φ hadd hsmul f s t
    rw [h1] at e
    rw [← e, hφ]
    have := hmin (s + t) x
    linarith
  have key := sq_le_of_quad (by linarith : (0 : ℝ) ≤ 1 - ε) hq
  have hp0 : 0 ≤ L (sqDev f s) x₀ :=
    hL.pos _ (fun y => by rw [sqDev_apply]; exact mul_self_nonneg _) x₀
  have hA : φ (sqDev f s) ≤ L (sqDev f s) x := by
    rw [hφ]
    nlinarith [mul_nonneg hε0 hp0]
  have e : φ f - s * (1 - ε) = L f x - ((1 - ε) * s + ε * L f x₀) := by
    rw [hφ]
    ring
  rw [e] at key
  rw [sqDev_apply]
  have := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 1 - ε)
  linarith

/-- The centres of a chain of minorised layers: `ctr 0 = s`, `ctr (i+1) = (1 − ε) ctr i + ε L i (g i) x₀`. -/
def ctr (L : ℕ → C(X, ℝ) → C(X, ℝ)) (g : ℕ → C(X, ℝ)) (x₀ : X) (ε s : ℝ) : ℕ → ℝ
  | 0 => s
  | i + 1 => (1 - ε) * ctr L g x₀ ε s i + ε * L i (g i) x₀

variable [CompactSpace X]

/-- A pointwise bound by a multiple passes to the state. -/
theorem state_le_mul {ν : State X} {G H : C(X, ℝ)} {c : ℝ} (h : ∀ x, G x ≤ c * H x) :
    ν G ≤ c * ν H := by
  have := ν.mono (f := G) (g := c • H) (fun x => by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    exact h x)
  rwa [ν.map_smul] at this

/-- **Cauchy–Schwarz for a state**: `(ν g − r)² ≤ ν((g − r)²)`. -/
theorem state_sq_le (ν : State X) (g : C(X, ℝ)) (r : ℝ) :
    (ν g - r) * (ν g - r) ≤ ν (sqDev g r) := by
  have hq : ∀ t, 0 ≤ ν (sqDev g r) - 2 * t * (ν g - r) + t * t * 1 := fun t => by
    have e := quad_of_linear ν.toFun ν.map_add ν.map_smul g r t
    have h1 : ν.toFun 1 = 1 := ν.map_one
    rw [h1, mul_one, mul_one] at e
    have h0 := sqDev_nonneg ν g (r + t)
    have e' : ν (sqDev g (r + t)) = ν (sqDev g r) - 2 * t * (ν g - r) + t * t := e
    rw [mul_one]
    linarith
  have := sq_le_of_quad zero_le_one hq
  linarith

/-- **One state, one minorised layer**: `|ν f − u| ≤ √(1 − ε) √ν((f − s)²)`. -/
theorem minor_abs_le {L : C(X, ℝ) → C(X, ℝ)} (hL : Markov L) (ν : State X) (f : C(X, ℝ)) (x₀ : X)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hmin : ∀ t x, ε * L (sqDev f t) x₀ ≤ L (sqDev f t) x)
    (s : ℝ) (hK : ν (L f) = ν f) (hK2 : ν (L (sqDev f s)) = ν (sqDev f s)) :
    |ν f - ((1 - ε) * s + ε * L f x₀)| ≤ Real.sqrt (1 - ε) * Real.sqrt (ν (sqDev f s)) := by
  have h1 := state_sq_le ν (L f) ((1 - ε) * s + ε * L f x₀)
  have h2 : ν (sqDev (L f) ((1 - ε) * s + ε * L f x₀)) ≤ (1 - ε) * ν (L (sqDev f s)) :=
    state_le_mul (minor_sq_le hL f x₀ hε0 hε1 hmin s)
  rw [hK] at h1
  rw [hK2] at h2
  rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 - ε)]
  exact Real.abs_le_sqrt (by rw [sq]; linarith)

/-- **The minorised closing, relative form**: two states invariant under `L` at `f` and at `(f − s)²` differ
on `f` by at most `√(1 − ε) (√ν₁((f − s)²) + √ν₂((f − s)²))`. -/
theorem minor_closing {L : C(X, ℝ) → C(X, ℝ)} (hL : Markov L) (ν₁ ν₂ : State X) (f : C(X, ℝ))
    (x₀ : X) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmin : ∀ t x, ε * L (sqDev f t) x₀ ≤ L (sqDev f t) x) (s : ℝ)
    (h₁ : ν₁ (L f) = ν₁ f) (h₂ : ν₂ (L f) = ν₂ f)
    (h₁' : ν₁ (L (sqDev f s)) = ν₁ (sqDev f s)) (h₂' : ν₂ (L (sqDev f s)) = ν₂ (sqDev f s)) :
    |ν₁ f - ν₂ f|
      ≤ Real.sqrt (1 - ε) * (Real.sqrt (ν₁ (sqDev f s)) + Real.sqrt (ν₂ (sqDev f s))) := by
  have a₁ := minor_abs_le hL ν₁ f x₀ hε0 hε1 hmin s h₁ h₁'
  have a₂ := minor_abs_le hL ν₂ f x₀ hε0 hε1 hmin s h₂ h₂'
  have ht := abs_sub_le (ν₁ f) ((1 - ε) * s + ε * L f x₀) (ν₂ f)
  rw [abs_sub_comm ((1 - ε) * s + ε * L f x₀)] at ht
  linarith

/-- **Layers contract the second moment geometrically**: after `j` minorised layers the second moment of
`g j` about `ctr j` is at most `(1 − ε)^j` times that of `g 0` about `s`. -/
theorem layers_sq_le (L : ℕ → C(X, ℝ) → C(X, ℝ)) (hL : ∀ i, Markov (L i)) (g : ℕ → C(X, ℝ))
    (hg : ∀ i, g (i + 1) = L i (g i)) (x₀ : X) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ν : State X) (s : ℝ) : ∀ j : ℕ,
    (∀ i < j, ∀ t x, ε * L i (sqDev (g i) t) x₀ ≤ L i (sqDev (g i) t) x) →
    (∀ i < j, ∀ t, ν (L i (sqDev (g i) t)) = ν (sqDev (g i) t)) →
    ν (sqDev (g j) (ctr L g x₀ ε s j)) ≤ (1 - ε) ^ j * ν (sqDev (g 0) s)
  | 0, _, _ => by simp [ctr]
  | j + 1, hmin, hinv => by
    have ih := layers_sq_le L hL g hg x₀ hε0 hε1 ν s j (fun i hi => hmin i (by omega))
      (fun i hi => hinv i (by omega))
    have hstep : ν (sqDev (g (j + 1)) (ctr L g x₀ ε s (j + 1)))
        ≤ (1 - ε) * ν (L j (sqDev (g j) (ctr L g x₀ ε s j))) := by
      rw [hg j]
      exact state_le_mul (minor_sq_le (hL j) (g j) x₀ hε0 hε1 (hmin j (by omega)) _)
    rw [hinv j (by omega)] at hstep
    have h1e : 0 ≤ 1 - ε := by linarith
    calc _ ≤ (1 - ε) * ν (sqDev (g j) (ctr L g x₀ ε s j)) := hstep
      _ ≤ (1 - ε) * ((1 - ε) ^ j * ν (sqDev (g 0) s)) := mul_le_mul_of_nonneg_left ih h1e
      _ = (1 - ε) ^ (j + 1) * ν (sqDev (g 0) s) := by ring

/-- Invariant layers keep the state's value. -/
theorem layers_mean (L : ℕ → C(X, ℝ) → C(X, ℝ)) (g : ℕ → C(X, ℝ))
    (hg : ∀ i, g (i + 1) = L i (g i)) (ν : State X) : ∀ j : ℕ,
    (∀ i < j, ν (L i (g i)) = ν (g i)) → ν (g j) = ν (g 0)
  | 0, _ => rfl
  | j + 1, h => by
    rw [hg j, h j (by omega)]
    exact layers_mean L g hg ν j (fun i hi => h i (by omega))

/-- **One state, `j` layers**: `|ν (g 0) − ctr j| ≤ √((1 − ε)^j) √ν((g 0 − s)²)`. -/
theorem layers_abs_le (L : ℕ → C(X, ℝ) → C(X, ℝ)) (hL : ∀ i, Markov (L i)) (g : ℕ → C(X, ℝ))
    (hg : ∀ i, g (i + 1) = L i (g i)) (x₀ : X) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ν : State X) (s : ℝ) (j : ℕ)
    (hmin : ∀ i < j, ∀ t x, ε * L i (sqDev (g i) t) x₀ ≤ L i (sqDev (g i) t) x)
    (hinv : ∀ i < j, ∀ t, ν (L i (sqDev (g i) t)) = ν (sqDev (g i) t))
    (hm : ∀ i < j, ν (L i (g i)) = ν (g i)) :
    |ν (g 0) - ctr L g x₀ ε s j|
      ≤ Real.sqrt ((1 - ε) ^ j) * Real.sqrt (ν (sqDev (g 0) s)) := by
  have h1 := state_sq_le ν (g j) (ctr L g x₀ ε s j)
  have h2 := layers_sq_le L hL g hg x₀ hε0 hε1 ν s j hmin hinv
  rw [layers_mean L g hg ν j hm] at h1
  rw [← Real.sqrt_mul (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) j)]
  exact Real.abs_le_sqrt (by rw [sq]; linarith)

/-- **The layered closing, relative form**:
`|ν₁ f − ν₂ f| ≤ √((1 − ε)^j) (√ν₁((f − s)²) + √ν₂((f − s)²))`, `f = g 0`. -/
theorem layers_closing (L : ℕ → C(X, ℝ) → C(X, ℝ)) (hL : ∀ i, Markov (L i)) (g : ℕ → C(X, ℝ))
    (hg : ∀ i, g (i + 1) = L i (g i)) (x₀ : X) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ν₁ ν₂ : State X) (s : ℝ) (j : ℕ)
    (hmin : ∀ i < j, ∀ t x, ε * L i (sqDev (g i) t) x₀ ≤ L i (sqDev (g i) t) x)
    (hinv₁ : ∀ i < j, ∀ t, ν₁ (L i (sqDev (g i) t)) = ν₁ (sqDev (g i) t))
    (hinv₂ : ∀ i < j, ∀ t, ν₂ (L i (sqDev (g i) t)) = ν₂ (sqDev (g i) t))
    (hm₁ : ∀ i < j, ν₁ (L i (g i)) = ν₁ (g i)) (hm₂ : ∀ i < j, ν₂ (L i (g i)) = ν₂ (g i)) :
    |ν₁ (g 0) - ν₂ (g 0)|
      ≤ Real.sqrt ((1 - ε) ^ j)
        * (Real.sqrt (ν₁ (sqDev (g 0) s)) + Real.sqrt (ν₂ (sqDev (g 0) s))) := by
  have a₁ := layers_abs_le L hL g hg x₀ hε0 hε1 ν₁ s j hmin hinv₁ hm₁
  have a₂ := layers_abs_le L hL g hg x₀ hε0 hε1 ν₂ s j hmin hinv₂ hm₂
  have ht := abs_sub_le (ν₁ (g 0)) (ctr L g x₀ ε s j) (ν₂ (g 0))
  rw [abs_sub_comm (ctr L g x₀ ε s j)] at ht
  linarith

end Generic

/-- **Enough layers make the factor small**: for `0 < ε ≤ 1`, every `C` and `π > 0`, some `j` gives
`√((1 − ε)^j) · C ≤ π`. -/
theorem layer_factor_small {ε C π : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hπ : 0 < π) :
    ∃ j : ℕ, Real.sqrt ((1 - ε) ^ j) * C ≤ π := by
  have h1 : Tendsto (fun j : ℕ => (1 - ε) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h2 : Tendsto (fun j : ℕ => Real.sqrt ((1 - ε) ^ j) * C) atTop (nhds (Real.sqrt 0 * C)) :=
    ((Real.continuous_sqrt.tendsto 0).comp h1).mul_const C
  rw [Real.sqrt_zero, zero_mul] at h2
  obtain ⟨j, hj⟩ := (h2.eventually (gt_mem_nhds hπ)).exists
  exact ⟨j, hj.le⟩

/-! ## 2. The variance version of the coarse reading bound -/

section Reweight

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

theorem wRead_nonneg {h w : Z → ℝ} (hw : ∀ z, 0 < w z) (hZ : 0 < ∫ z, w z ∂μ)
    (hh : ∀ z, 0 ≤ h z) : 0 ≤ wRead μ h w :=
  div_nonneg (integral_nonneg fun z => mul_nonneg (hh z) (hw z).le) hZ.le

theorem integrable_sq_mul {h w : Z → ℝ} (s : ℝ) (iw : Integrable w μ)
    (ihw : Integrable (fun z => h z * w z) μ) (ihw2 : Integrable (fun z => h z * h z * w z) μ) :
    Integrable (fun z => (h z - s) * (h z - s) * w z) μ := by
  have e : (fun z => (h z - s) * (h z - s) * w z)
      = fun z => h z * h z * w z - (2 * s) * (h z * w z) + (s * s) * w z := by
    funext z
    ring
  rw [e]
  exact (ihw2.sub (ihw.const_mul _)).add (iw.const_mul _)

/-- **The reading of a squared deviation is quadratic in the centre.** -/
theorem wRead_quad {h w : Z → ℝ} (s t : ℝ) (iw : Integrable w μ)
    (ihw : Integrable (fun z => h z * w z) μ) (ihw2 : Integrable (fun z => h z * h z * w z) μ)
    (hZ : 0 < ∫ z, w z ∂μ) :
    wRead μ (fun z => (h z - (s + t)) * (h z - (s + t))) w
      = wRead μ (fun z => (h z - s) * (h z - s)) w - 2 * t * (wRead μ h w - s) + t * t := by
  have iq := integrable_sq_mul s iw ihw ihw2
  have id := integrable_sub_mul s iw ihw
  have e : (fun z => (h z - (s + t)) * (h z - (s + t)) * w z)
      = fun z => (h z - s) * (h z - s) * w z - (2 * t) * ((h z - s) * w z) + (t * t) * w z := by
    funext z
    ring
  rw [wRead_sub h w s iw ihw hZ]
  show (∫ z, (h z - (s + t)) * (h z - (s + t)) * w z ∂μ) / (∫ z, w z ∂μ)
      = (∫ z, (h z - s) * (h z - s) * w z ∂μ) / (∫ z, w z ∂μ)
        - 2 * t * ((∫ z, (h z - s) * w z ∂μ) / ∫ z, w z ∂μ) + t * t
  have i1 : Integrable (fun z => (h z - s) * (h z - s) * w z - 2 * t * ((h z - s) * w z)) μ :=
    iq.sub (id.const_mul _)
  have i2 : Integrable (fun z => t * t * w z) μ := iw.const_mul _
  have i3 : Integrable (fun z => 2 * t * ((h z - s) * w z)) μ := id.const_mul _
  rw [e, integral_add i1 i2, integral_sub iq i3, integral_const_mul, integral_const_mul, add_div,
    sub_div, mul_div_assoc (2 * t), mul_div_assoc (t * t), div_self hZ.ne', mul_one]

/-- **The coarse reading is minorised**: a weight ratio `e^{±c}` and `h ≥ 0` give
`e^{−2c} wRead h w ≤ wRead h w'`. -/
theorem wRead_minor {h w w' : Z → ℝ} {c : ℝ} (hw : ∀ z, 0 < w z)
    (hlo : ∀ z, Real.exp (-c) * w z ≤ w' z) (hhi : ∀ z, w' z ≤ Real.exp c * w z)
    (iw : Integrable w μ) (iw' : Integrable w' μ) (ihw : Integrable (fun z => h z * w z) μ)
    (ihw' : Integrable (fun z => h z * w' z) μ) (hZ : 0 < ∫ z, w z ∂μ) (hh : ∀ z, 0 ≤ h z) :
    Real.exp (-(2 * c)) * wRead μ h w ≤ wRead μ h w' := by
  have := wRead_lower (m := 0) hw hlo hhi iw iw' ihw ihw' hZ hh
  simpa using this

/-- **The variance version of `wRead_osc`**: a weight ratio `e^{±c}` gives
`(wRead h w' − u)² ≤ (1 − e^{−2c}) wRead((h − s)²) w'`, `u = (1 − e^{−2c}) s + e^{−2c} wRead h w`. No range of
`h` enters. -/
theorem wRead_var {h w w' : Z → ℝ} {c : ℝ} (hc : 0 ≤ c) (hw : ∀ z, 0 < w z)
    (hlo : ∀ z, Real.exp (-c) * w z ≤ w' z) (hhi : ∀ z, w' z ≤ Real.exp c * w z)
    (iw : Integrable w μ) (iw' : Integrable w' μ) (ihw : Integrable (fun z => h z * w z) μ)
    (ihw' : Integrable (fun z => h z * w' z) μ) (ihw2 : Integrable (fun z => h z * h z * w z) μ)
    (ihw2' : Integrable (fun z => h z * h z * w' z) μ) (hZ : 0 < ∫ z, w z ∂μ)
    (hZ' : 0 < ∫ z, w' z ∂μ) (s : ℝ) :
    (wRead μ h w' - ((1 - Real.exp (-(2 * c))) * s + Real.exp (-(2 * c)) * wRead μ h w))
      * (wRead μ h w' - ((1 - Real.exp (-(2 * c))) * s + Real.exp (-(2 * c)) * wRead μ h w))
      ≤ (1 - Real.exp (-(2 * c))) * wRead μ (fun z => (h z - s) * (h z - s)) w' := by
  set ε := Real.exp (-(2 * c)) with hε
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hq : ∀ t, 0 ≤ (wRead μ (fun z => (h z - s) * (h z - s)) w'
      - ε * wRead μ (fun z => (h z - s) * (h z - s)) w)
      - 2 * t * ((wRead μ h w' - s) - ε * (wRead μ h w - s)) + t * t * (1 - ε) := fun t => by
    have m := wRead_minor (h := fun z => (h z - (s + t)) * (h z - (s + t))) hw hlo hhi iw iw'
      (integrable_sq_mul (s + t) iw ihw ihw2) (integrable_sq_mul (s + t) iw' ihw' ihw2') hZ
      (fun z => mul_self_nonneg _)
    rw [← hε, wRead_quad s t iw ihw ihw2 hZ, wRead_quad s t iw' ihw' ihw2' hZ'] at m
    nlinarith [m]
  have key := sq_le_of_quad (by linarith : (0 : ℝ) ≤ 1 - ε) hq
  have e : (wRead μ h w' - s) - ε * (wRead μ h w - s)
      = wRead μ h w' - ((1 - ε) * s + ε * wRead μ h w) := by ring
  rw [e] at key
  have hQ := wRead_nonneg (μ := μ) (h := fun z => (h z - s) * (h z - s)) hw hZ
    (fun z => mul_self_nonneg _)
  nlinarith [key, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) (mul_nonneg hε0 hQ)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}

/-- **The variance version of `coarseGibbs_osc`**: a coarse weight with per-block log-oscillation `c_b`
contracts the squared deviation of the reading by `1 − e^{−2 Σ_b c_b}` between any two coarse configurations. -/
theorem coarseGibbs_var (h : Z → ℝ) (w : (∀ b, Y b) → Z → ℝ) {cb : ι → ℝ}
    (hw : ∀ y z, 0 < w y z) (iw : ∀ y, Integrable (w y) μ)
    (ihw : ∀ y, Integrable (fun z => h z * w y z) μ)
    (ihw2 : ∀ y, Integrable (fun z => h z * h z * w y z) μ) (hZ : ∀ y, 0 < ∫ z, w y z ∂μ)
    (hosc : ∀ z, BlockOsc (fun y => Real.log (w y z)) cb) (hcb : ∀ b, 0 ≤ cb b)
    (y y' : ∀ b, Y b) (s : ℝ) :
    (wRead μ h (w y') - ((1 - Real.exp (-(2 * ∑ b, cb b))) * s
        + Real.exp (-(2 * ∑ b, cb b)) * wRead μ h (w y)))
      * (wRead μ h (w y') - ((1 - Real.exp (-(2 * ∑ b, cb b))) * s
        + Real.exp (-(2 * ∑ b, cb b)) * wRead μ h (w y)))
      ≤ (1 - Real.exp (-(2 * ∑ b, cb b))) * wRead μ (fun z => (h z - s) * (h z - s)) (w y') := by
  have r : ∀ z, Real.exp (-(∑ b, cb b)) * w y z ≤ w y' z ∧ w y' z ≤ Real.exp (∑ b, cb b) * w y z :=
    fun z => ratio_of_log (hw y z) (hw y' z) (abs_sub_le_sum (hosc z) y y')
  exact wRead_var (Finset.sum_nonneg fun b _ => hcb b) (hw y) (fun z => (r z).1) (fun z => (r z).2)
    (iw y) (iw y') (ihw y) (ihw y') (ihw2 y) (ihw2 y') (hZ y) (hZ y') s

end Reweight

/-! ## 3. The Wilson box -/

section Wilson

open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.PeriodicState MassGap.LocalClosing
  MassGap.ScreenBridge
open MassGap.DLRLimit (IsLocalOnC)

variable {N : ℕ}

/-- **A layered relative bound**: `j` Markov layers `L i`, invariant for the torus and the infinite-volume
state at the iterates `g i` and at every squared deviation of them, minorised with one `ε` at a reference
configuration on the second moments of the iterates, and `√((1 − ε)^j) (√V_T + √V_∞) ≤ Δ`, `V = state((F − s)²)`. -/
def LayerBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) : Prop :=
  ∃ (j : ℕ) (L : ℕ → C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ))
    (g : ℕ → C(IConf (MassGap.SUN.SU N), ℝ)) (x₀ : IConf (MassGap.SUN.SU N)) (ε s : ℝ),
    g 0 = F ∧ (∀ i, Markov (L i)) ∧ (∀ i, g (i + 1) = L i (g i)) ∧ 0 ≤ ε ∧ ε ≤ 1
    ∧ (∀ i < j, ∀ t ω, ε * L i (sqDev (g i) t) x₀ ≤ L i (sqDev (g i) t) ω)
    ∧ (∀ i < j, torusState hN M β (L i (g i)) = torusState hN M β (g i))
    ∧ (∀ i < j, periodicState hN β (L i (g i)) = periodicState hN β (g i))
    ∧ (∀ i < j, ∀ t, torusState hN M β (L i (sqDev (g i) t)) = torusState hN M β (sqDev (g i) t))
    ∧ (∀ i < j, ∀ t, periodicState hN β (L i (sqDev (g i) t)) = periodicState hN β (sqDev (g i) t))
    ∧ Real.sqrt ((1 - ε) ^ j) * (Real.sqrt (torusState hN M β (sqDev F s))
        + Real.sqrt (periodicState hN β (sqDev F s))) ≤ Δ

/-- **The torus against the infinite volume, layered relative form.** -/
theorem LayerBound.closing {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {Δ : ℝ} (h : LayerBound hN M β F Δ) :
    |torusState hN M β F - periodicState hN β F| ≤ Δ := by
  obtain ⟨j, L, g, x₀, ε, s, hg0, hL, hg, hε0, hε1, hmin, hT, hP, hT2, hP2, hle⟩ := h
  subst hg0
  have := layers_closing L hL g hg x₀ hε0 hε1 (torusState hN M β) (periodicState hN β) s j hmin
    hT2 hP2 hT hP
  linarith

/-- **A relative screen**: a refinement screen `Q` of a box `Λ'`, Markov, with `Q ∘ wspec Λ` minorised at a
reference configuration on the second moments `(F − t)²`, the locality that puts both states' invariance on
`Refines`, and `√(1 − ε) (√V_T + √V_∞) ≤ Δ`. No factorisation and no range of `F`. -/
def RelScreen (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (ε Δ : ℝ) : Prop :=
  ∃ (Λ S Λ' S' : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ))
    (x₀ : IConf (MassGap.SUN.SU N)) (s : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ Refines hN β Λ' Q ∧ Markov Q ∧ BoxFits M Λ' S'
    ∧ IsLocalOnC S' (Q (wspec hN β Λ F)) ∧ IsLocalOnC S' (wspec hN β Λ F)
    ∧ (∀ t, IsLocalOnC S' (Q (wspec hN β Λ (sqDev F t))))
    ∧ (∀ t, IsLocalOnC S' (wspec hN β Λ (sqDev F t)))
    ∧ 0 ≤ ε ∧ ε ≤ 1
    ∧ (∀ t ω, ε * Q (wspec hN β Λ (sqDev F t)) x₀ ≤ Q (wspec hN β Λ (sqDev F t)) ω)
    ∧ Real.sqrt (1 - ε) * (Real.sqrt (torusState hN M β (sqDev F s))
        + Real.sqrt (periodicState hN β (sqDev F s))) ≤ Δ

/-- **A relative screen is one layer.** -/
theorem layerBound_of_relScreen {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {ε Δ : ℝ} (h : RelScreen hN M β F ε Δ) : LayerBound hN M β F Δ := by
  obtain ⟨Λ, S, Λ', S', Q, x₀, s, hloc, hfit, hR, hQ, hfit', hQl, hGl, hQl2, hGl2, hε0, hε1, hmin,
    hle⟩ := h
  refine ⟨1, fun _ G => Q (wspec hN β Λ G), fun i => (fun G => Q (wspec hN β Λ G))^[i] F, x₀, ε, s,
    rfl, fun _ => markov_comp hQ (markov_wspec hN β Λ),
    fun i => Function.iterate_succ_apply' _ i F, hε0, hε1, ?_, ?_, ?_, ?_, ?_, by rwa [pow_one]⟩
  · intro i hi t ω
    obtain rfl : i = 0 := by omega
    exact hmin t ω
  · intro i hi
    obtain rfl : i = 0 := by omega
    exact (hR.torus hQl hGl hfit').trans (torusState_dlr hN M β Λ S F hloc hfit.1 hfit.2)
  · intro i hi
    obtain rfl : i = 0 := by omega
    exact (hR.periodic _).trans (periodicState_dlr hN β Λ F)
  · intro i hi t
    obtain rfl : i = 0 := by omega
    exact (hR.torus (hQl2 t) (hGl2 t) hfit').trans
      (torusState_dlr hN M β Λ S _ (isLocalOnC_sqDev hloc t) hfit.1 hfit.2)
  · intro i hi t
    obtain rfl : i = 0 := by omega
    exact (hR.periodic _).trans (periodicState_dlr hN β Λ _)

end Wilson

/-! ## 4. The factored screen in relative form -/

section Factored

open MassGap.SUN MassGap.TorusDoubling MassGap.GapSideExactDecimation MassGap.EffectiveDensityBound
open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.PeriodicState MassGap.LocalClosing
  MassGap.ScreenBridge
open MassGap.DLRLimit (IsLocalOnC)

variable {N : ℕ}

/-- **The factored screen, relative form**: a refinement screen `Q` of a box `Λ'`, Markov, whose composite
with the box kernel at every squared deviation `(F − t)²` is the reading, over interior variables with law `μ`,
of a nonnegative bounded `H t` under the weight `ρ ζ (join (c ω) z)`, with `join` changing only the coarse link
`e b` when block `b` changes; and `√(1 − e^{−2 m cL}) (√V_T + √V_∞) ≤ Δ`. -/
def EffScreenRel (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) {n : ℕ}
    (ρ : DensE n) (m : ℕ) (cL Δ : ℝ) : Prop :=
  ∃ (Λ S Λ' S' : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ))
    (e : Fin m → TLink 4 n) (c : IConf (MassGap.SUN.SU N) → Fin m → SU 2)
    (μ : Measure (IConf (MassGap.SUN.SU N))) (ζ : TPlaq 4 n → SU 2)
    (join : (Fin m → SU 2) → IConf (MassGap.SUN.SU N) → TLink 4 n → SU 2)
    (H : ℝ → IConf (MassGap.SUN.SU N) → ℝ) (C : ℝ → ℝ) (s : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ Refines hN β Λ' Q ∧ Markov Q ∧ BoxFits M Λ' S'
    ∧ IsLocalOnC S' (Q (wspec hN β Λ F)) ∧ IsLocalOnC S' (wspec hN β Λ F)
    ∧ (∀ t, IsLocalOnC S' (Q (wspec hN β Λ (sqDev F t))))
    ∧ (∀ t, IsLocalOnC S' (wspec hN β Λ (sqDev F t)))
    ∧ (∀ t ω, Q (wspec hN β Λ (sqDev F t)) ω = wRead μ (H t) (fun z => ρ ζ (join (c ω) z)))
    ∧ (∀ z b (y y' : Fin m → SU 2), (∀ b', b' ≠ b → y b' = y' b') →
        ∀ l, l ≠ e b → join y z l = join y' z l)
    ∧ IsProbabilityMeasure μ ∧ (∀ y, Measurable (join y)) ∧ (∀ t, Measurable (H t))
    ∧ (∀ t z, 0 ≤ H t z ∧ H t z ≤ C t)
    ∧ Real.sqrt (1 - Real.exp (-(2 * (m * cL)))) * (Real.sqrt (torusState hN M β (sqDev F s))
        + Real.sqrt (periodicState hN β (sqDev F s))) ≤ Δ

/-- **The shared Prop and a relative factored screen give a relative screen** with `ε = e^{−2 m cL}`. -/
theorem relScreen_of_effScreenRel {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {n : ℕ} {ρ : DensE n} {m : ℕ} {cP cL Δ : ℝ} (hU : UnitOsc ρ cP cL) (hb : Banded ρ)
    (hS : EffScreenRel hN M β F ρ m cL Δ) :
    RelScreen hN M β F (Real.exp (-(2 * (m * cL)))) Δ := by
  obtain ⟨Λ, S, Λ', S', Q, e, c, μ, ζ, join, H, C, s, hloc, hfit, hR, hQ, hfit', hQl, hGl, hQl2,
    hGl2, hfac, hjoin, hμ, hjm, hHm, hH, hle⟩ := hS
  haveI := hμ
  obtain ⟨hρm, a, b, ha, hab⟩ := hb ζ
  have hw : ∀ (y : Fin m → SU 2) z, 0 < ρ ζ (join y z) := fun y z => lt_of_lt_of_le ha (hab _).1
  have hmeas : ∀ y : Fin m → SU 2, Measurable (fun z => ρ ζ (join y z)) := fun y =>
    hρm.comp (hjm y)
  have iw : ∀ y : Fin m → SU 2, Integrable (fun z => ρ ζ (join y z)) μ := fun y =>
    Integrable.mono' (integrable_const b) (hmeas y).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (hw y z)]
        exact (hab _).2)
  have ihw : ∀ t (y : Fin m → SU 2), Integrable (fun z => H t z * ρ ζ (join y z)) μ := fun t y =>
    Integrable.mono' (integrable_const (C t * b)) ((hHm t).mul (hmeas y)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hw y z), abs_of_nonneg (hH t z).1]
        exact mul_le_mul (hH t z).2 (hab _).2 (hw y z).le ((hH t z).1.trans (hH t z).2))
  have hZ : ∀ y : Fin m → SU 2, 0 < ∫ z, ρ ζ (join y z) ∂μ := fun y => by
    have h1 := integral_mono (integrable_const a) (iw y) (fun z => (hab (join y z)).1)
    rw [integral_const, probReal_univ, one_smul] at h1
    exact lt_of_lt_of_le ha h1
  have hmc : 0 ≤ (m : ℝ) * cL := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0, Nat.cast_zero, zero_mul]
    · exact mul_nonneg (Nat.cast_nonneg _) (cL_nonneg_of_unitOsc hU (e ⟨0, hm0⟩))
  have hratio : ∀ (y y' : Fin m → SU 2) z,
      |Real.log (ρ ζ (join y z)) - Real.log (ρ ζ (join y' z))| ≤ m * cL := by
    intro y y' z
    have hosc : BlockOsc (Y := fun _ : Fin m => SU 2) (fun y => Real.log (ρ ζ (join y z)))
        (fun _ => cL) :=
      fun b' y y' hy => hU.link ζ (e b') (join y z) (join y' z) (hjoin z b' y y' hy)
    have h1 := abs_sub_le_sum hosc y y'
    have hs : ∑ _b : Fin m, cL = m * cL := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rwa [hs] at h1
  refine ⟨Λ, S, Λ', S', Q, fun _ => 1, s, hloc, hfit, hR, hQ, hfit', hQl, hGl, hQl2, hGl2,
    (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith), ?_, hle⟩
  intro t ω
  rw [hfac, hfac]
  have r := fun z => ratio_of_log (hw (c (fun _ => 1)) z) (hw (c ω) z) (hratio _ _ z)
  exact wRead_minor (hw _) (fun z => (r z).1) (fun z => (r z).2) (iw _) (iw _) (ihw t _)
    (ihw t _) (hZ _) (fun z => (hH t z).1)

end Factored

/-! ## 5. The pinned path -/

section Pixel

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing
open MassGap.SUN MassGap.GapSideExactDecimation MassGap.EffectiveDensityBound MassGap.ScreenBridge

variable {N : ℕ}

/-- **The pinned path with `hpos` read through layered relative bounds and the floor.** -/
theorem clay_canonical_layer (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoundPixel hN c O t ℓ π₁ (LayerBound hN))
    (h1 : BoundOnePoint hN c O t ℓ π₂ (LayerBound hN))
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_bound hN2 hN O (fun _ _ _ _ h => h.closing) ht c hκ hπ₁ hπ₂ hπκ hB h1 hF hD hℓ hW

/-- **The relative factored screen at the pixel observable**, eventually in `k`, at `π · √(refMomentS)`,
with some block count `m` at each `k`. -/
def EffScreenRelPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ m : ℕ, EffScreenRel hN (2 * (2 ^ (c + k) - 1) + 1)
    (dyBeta (one_le_of_ne_zero hN) k) (refObs (stateK hN k) O t ℓ k) (ρs k) m cL
    (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k))

/-- **The relative factored screen at the two one-point observables**, with bounds whose product with the
cube weights is at most `π · √(refMomentS)`. -/
def EffScreenRelOnePoint (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ (Δ₀ Δ₁ : ℝ) (m₀ m₁ : ℕ),
    EffScreenRel hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) (O.refl 0).1
      (ρs k) m₀ cL Δ₀
    ∧ EffScreenRel hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) O.1 (ρs k) m₁
      cL Δ₁
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)| * Δ₀
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)| * Δ₁)
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

theorem boundPixel_of_effScreenRel {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π : ℝ} {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hS : EffScreenRelPixel hN c O t ℓ π ρs cL) : BoundPixel hN c O t ℓ π (LayerBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨m, hm⟩ := hs
  exact layerBound_of_relScreen (relScreen_of_effScreenRel hk.1 hk.2 hm)

theorem boundOnePoint_of_effScreenRel {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π : ℝ} {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hS : EffScreenRelOnePoint hN c O t ℓ π ρs cL) :
    BoundOnePoint hN c O t ℓ π (LayerBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨Δ₀, Δ₁, m₀, m₁, h₀, h₁, hle⟩ := hs
  exact ⟨Δ₀, Δ₁, layerBound_of_relScreen (relScreen_of_effScreenRel hk.1 hk.2 h₀),
    layerBound_of_relScreen (relScreen_of_effScreenRel hk.1 hk.2 h₁), hle⟩

/-- **The pinned path with `hpos` replaced by the shared Prop at the coarse scale, the relative factored
screens and the floor**; `hD` and `hW` unchanged. -/
theorem clay_canonical_unitOsc_rel (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hSP : EffScreenRelPixel hN c O t ℓ π₁ ρs cL) (hS1 : EffScreenRelOnePoint hN c O t ℓ π₂ ρs cL)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_layer hN2 hN O ht c hκ hπ₁ hπ₂ hπκ (boundPixel_of_effScreenRel hU hSP)
    (boundOnePoint_of_effScreenRel hU hS1) hF hD hℓ hW

end Pixel

end MassGap.RelativeScreen

end

#print axioms MassGap.RelativeScreen.sq_le_of_quad
#print axioms MassGap.RelativeScreen.sqDev_shift
#print axioms MassGap.RelativeScreen.quad_of_linear
#print axioms MassGap.RelativeScreen.minor_sq_le
#print axioms MassGap.RelativeScreen.state_le_mul
#print axioms MassGap.RelativeScreen.state_sq_le
#print axioms MassGap.RelativeScreen.minor_abs_le
#print axioms MassGap.RelativeScreen.minor_closing
#print axioms MassGap.RelativeScreen.layers_sq_le
#print axioms MassGap.RelativeScreen.layers_mean
#print axioms MassGap.RelativeScreen.layers_abs_le
#print axioms MassGap.RelativeScreen.layers_closing
#print axioms MassGap.RelativeScreen.layer_factor_small
#print axioms MassGap.RelativeScreen.wRead_nonneg
#print axioms MassGap.RelativeScreen.integrable_sq_mul
#print axioms MassGap.RelativeScreen.wRead_quad
#print axioms MassGap.RelativeScreen.wRead_minor
#print axioms MassGap.RelativeScreen.wRead_var
#print axioms MassGap.RelativeScreen.coarseGibbs_var
#print axioms MassGap.RelativeScreen.LayerBound.closing
#print axioms MassGap.RelativeScreen.layerBound_of_relScreen
#print axioms MassGap.RelativeScreen.relScreen_of_effScreenRel
#print axioms MassGap.RelativeScreen.clay_canonical_layer
#print axioms MassGap.RelativeScreen.boundPixel_of_effScreenRel
#print axioms MassGap.RelativeScreen.boundOnePoint_of_effScreenRel
#print axioms MassGap.RelativeScreen.clay_canonical_unitOsc_rel
