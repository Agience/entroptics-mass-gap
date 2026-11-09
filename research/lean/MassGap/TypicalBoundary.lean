import Mathlib
import MassGap.ClayRoutes
import MassGap.DoublingClay2
import MassGap.ExistenceReduce
import MassGap.LightConePassage
import MassGap.LocalClosing

noncomputable section

/-!
# MassGap.TypicalBoundary — the local closing read only on typical boundary conditions

`LocalClosing.local_closing` bounds `|ν₁ f − ν₂ f|` by the spread of the box kernel `K f` over every
pair of boundary conditions. The two states read `K f` only through their own measures
(`DLRLimit.gibbsMeasure`, Riesz–Markov), so it is enough that `K f` is nearly constant on a set `G` of
boundary conditions, and that the part of `K f` off `G` has small weight under each state. This
module proves that form, puts it on the Wilson torus against the infinite volume, carries it to the
pinned path, and measures what the good set costs along the family.

## 1. The typical local closing (proved, any compact `X`)

For a `DLRLimit.State ν` with measure `μ = gibbsMeasure ν`, a kernel `K` with `ν (K f) = ν f`, a
measurable `G` and `|K f x − r| ≤ δ` on `G`:

* `abs_sub_le_integral`: `|ν g − r| ≤ ∫ |g − r| dμ`.
* `typical_abs_le`: `|ν f − r| ≤ δ + ∫_{Gᶜ} |K f − r| dμ`.
* `typical_local_closing`: two such states with `∫_{Gᶜ} |K f − r| dμᵢ ≤ ε` give
  `|ν₁ f − ν₂ f| ≤ 2 (δ + ε)`.
* `setIntegral_compl_le_mass`, `typical_closing_mass`: if `|K f − r| ≤ C` everywhere, the off-`G` term
  is at most `C · μ(Gᶜ)`.

## 2. The relative form (proved)

* `Markov K`: `K` additive, homogeneous, unital and positive. `Markov.sq_le` (Kadison–Schwarz):
  `(K h x)² ≤ K (h²) x`.
* `sqDev f r = (f − r)²`. `setIntegral_compl_amgm`: `2t ∫_{Gᶜ} |g − r| ≤ t² μ(Gᶜ) + ν (sqDev g r)` at every
  `t`; `le_sqrt_of_amgm` takes the infimum over `t > 0`.
* `typical_abs_le_rel`: for `K` Markov, DLR at `f` and at `sqDev f r`,
  `|ν f − r| ≤ δ + √(μ(Gᶜ) · ν (sqDev f r))`.
* `typical_closing_rel`: `|ν₁ f − ν₂ f| ≤ 2δ + √(μ₁(Gᶜ) V₁) + √(μ₂(Gᶜ) V₂)`, `Vᵢ = νᵢ (sqDev f r)`.
  The off-`G` part is relative to the second moment of `f` about `r`: the mass of `Gᶜ` has to be
  small against a fixed number, not against a scale that shrinks with `k`.

## 3. The Wilson torus against the infinite volume (proved)

* `markov_wspec`: the box kernel `wspec hN β Λ` is Markov.
* `TypicalBound hN M β F Δ`: a box and support that fit in the torus of extent `M + 1`, a measurable
  `G`, a centre `r` and `δ ≥ 0` with `|wspec F ω − r| ≤ δ` on `G`, and
  `2δ + √(μ_T(Gᶜ) V_T) + √(μ_∞(Gᶜ) V_∞) ≤ Δ`. `TypicalBound.closing`:
  `|torusState hN M β F − periodicState hN β F| ≤ Δ`.
* `typicalBound_of_spread`: a spread `≤ d` over every pair gives `TypicalBound` at `Δ = 2d` with `G`
  everything. The typical form is never stronger than `BoxPixel` beyond the factor `2`.

## 4. The pinned path (proved reductions)

* `TypicalBoxPixel`, `TypicalOnePoint`: `LocalClosing.BoxPixel` and `LocalClosing.OnePointPixel` with
  each spread over every pair replaced by `TypicalBound`. `boxPixel_typical`,
  `pixelPassage_of_typical`, `centringPixel_of_typical`, `clay_canonical_typical` (the pinned path
  with `hpos` read through the two and `ReadingFloor`).

## 5. The smooth good set and its mass (proved)

* `smoothSet P θ`: every plaquette of `P` has Wilson density `1 − Re tr U_p / N` at most `θ`.
  `isClosed_smoothSet`, `measurableSet_smoothSet`; `smoothSet_compl`: its complement is the union of the
  single-plaquette tail events; `mass_smooth_compl_le`: the union bound, and with a per-plaquette tail
  `τ`, `μ(Gᶜ) ≤ #P · τ`.
* `SmoothBound`, `typicalBound_of_smooth`, `SmoothBoxPixel`, `typicalBoxPixel_of_smooth`: `TypicalBound`
  from a spread bound on `smoothSet P θ` and per-plaquette tails under both states.

## 6. The scaling of the union bound (proved, parametric)

The count `n_k` of plaquettes on a box of fixed physical size grows like `8^k`
(`dySpacing N k = aRun N 1 / 2^{k+1}`). With a tail `A e^{−β θ}` and couplings along the family:

* `union_tail_tendsto_zero`: `n_k ≤ C 8^k`, `β_k ≥ b k − B`, `log 8 < b θ` give `n_k A e^{−β_k θ} → 0`.
* `union_tail_tendsto_top`: `n_k ≥ c 8^k`, `β_k ≤ b k + B`, `b θ < log 8` give `n_k A e^{−β_k θ} → ∞`.
* `vacuum_width_tendsto_top`: at `β_k θ_k ≤ κ` (smoothness on the scale of the vacuum's own
  fluctuations) and `n_k → ∞`, `n_k A e^{−β_k θ_k} → ∞` for every per-plaquette lower tail.

## What stays open

`BoxPixel` and `OnePointPixel` are not proved, and neither are `TypicalBoxPixel` and
`TypicalOnePoint`. The remainder of (1b) on this route is `TypicalBoxPixel ∧ TypicalOnePoint`
(`clay_canonical_typical`), and through the smooth set, `SmoothBoxPixel` (`typicalBoxPixel_of_smooth`).
It has two parts, and they pull `θ` in opposite directions (argued):

1. The mass of `Gᶜ`. From `aRun N β = aRunStd N (2β)` the family's coupling runs as
   `β_k ≈ b k` with `b = 11 N² log 2 / (24 π²)` (Lean `β`; `b ≈ 0.129` at `N = 2`, `0.290` at `N = 3`)
   (argued). A per-plaquette tail `e^{−c β θ}` up to factors polynomial in `β` (the plaquette's own
   weight gives `c ≥ 1`; `c ≈ 2` in four dimensions from the plaquette's share of the link
   fluctuations) (argued) closes the union bound exactly when `c b θ > log 8`
   (`union_tail_tendsto_zero`, `union_tail_tendsto_top`). At `c = 1` that is `θ > 72 π² / (11 N²)`,
   above the largest value `2` of the density for `N ≤ 5`; at `c = 2` it is `θ > 36 π² / (11 N²)`, above
   `2` for `N ≤ 4`. So at a fixed `θ` in lattice units the mass is small only for large `N`, and only at
   `θ` of order one, which is no smoothness on the scale of the vacuum. A `θ` fixed in physical units
   (`θ_k ≈ a_k⁴ Θ²`, field strength at most `Θ`) is worse: the vacuum fluctuation of a plaquette is
   `≈ 1/β_k ≫ a_k⁴ Θ²`, so each plaquette leaves `G` with probability tending to `1` (argued).
2. The spread on `G`. Smoothness of `ω` does not constrain the inside of the box, so the Doeblin
   constant restricted to `G` is still `e^{−2β · #boundaryPlaqs}`. In the transfer reading the
   per-link excess of a smooth boundary condition against the vacuum is the overlap of a conditional
   law with its marginal at the vacuum's own width `1/√β`; it is of order one and does not depend on
   `β` (argued). Typicality removes the factor `β` per boundary link and keeps the count: `n_k η` with
   `η` of order one and `n_k ≈ (dist / a_k)³`, so the volume obstruction still applies to the cone.
   A spread bound on `G` that a smoothness condition could buy needs smoothness on the vacuum width,
   `θ_k ≲ 1/β_k` (argued), and there `vacuum_width_tendsto_top` makes the union bound diverge at
   every `N`.

Exact remainder (typed): `TypicalBoxPixel hN c O t ℓ π₁ ∧ TypicalOnePoint hN c O t ℓ π₂`. Through the
smooth set the failing step is `SmoothBound` along `k`: a spread at most `δ` on `smoothSet P θ_k`
together with per-plaquette tails `τ_k` and `#P_k · τ_k` bounded by a fixed small number. The mass
clause asks `θ_k` bounded below by `log 8 / (c b)`, the spread clause asks `θ_k ≲ 1/β_k → 0`, so
the two clauses do not hold together along `k` (argued).
-/

namespace MassGap.TypicalBoundary

open MeasureTheory Filter
open MassGap.DLRLimit (State gibbsMeasure integral_gibbsMeasure IsLocalOnC)

/-! ## 1. The typical local closing -/

section Generic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem integrable_cm (ν : State X) (g : C(X, ℝ)) :
    Integrable (fun x => g x) (gibbsMeasure ν) :=
  (BoundedContinuousFunction.mkOfCompact g).integrable _

/-- A state against a constant, through its measure. -/
theorem abs_sub_le_integral (ν : State X) (g : C(X, ℝ)) (r : ℝ) :
    |ν g - r| ≤ ∫ x, |g x - r| ∂(gibbsMeasure ν) := by
  have e : ν g - r = ∫ x, (g x - r) ∂(gibbsMeasure ν) := by
    rw [integral_sub (integrable_cm ν g) (integrable_const r), integral_const, probReal_univ,
      one_smul, integral_gibbsMeasure]
  rw [e]
  exact abs_integral_le_integral_abs

theorem integrable_abs_sub (ν : State X) (g : C(X, ℝ)) (r : ℝ) :
    Integrable (fun x => |g x - r|) (gibbsMeasure ν) :=
  ((integrable_cm ν g).sub (integrable_const r)).abs

/-- **A DLR state against a value, off a bad set**: `|K f − r| ≤ δ` on `G` gives
`|ν f − r| ≤ δ + ∫_{Gᶜ} |K f − r|`. -/
theorem typical_abs_le (K : C(X, ℝ) → C(X, ℝ)) (ν : State X) (f : C(X, ℝ))
    (hK : ν (K f) = ν f) {G : Set X} (hG : MeasurableSet G) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hgood : ∀ x ∈ G, |K f x - r| ≤ δ) :
    |ν f - r| ≤ δ + ∫ x in Gᶜ, |K f x - r| ∂(gibbsMeasure ν) := by
  rw [← hK]
  have hint := integrable_abs_sub ν (K f) r
  have hpt : ∀ x, |K f x - r| ≤ δ + Gᶜ.indicator (fun x => |K f x - r|) x := by
    intro x
    by_cases hx : x ∈ G
    · have hx' : x ∉ Gᶜ := fun h => h hx
      rw [Set.indicator_of_notMem hx']
      linarith [hgood x hx]
    · rw [Set.indicator_of_mem (Set.mem_compl hx)]
      linarith
  calc |ν (K f) - r| ≤ ∫ x, |K f x - r| ∂(gibbsMeasure ν) := abs_sub_le_integral ν (K f) r
    _ ≤ ∫ x, (δ + Gᶜ.indicator (fun x => |K f x - r|) x) ∂(gibbsMeasure ν) :=
        integral_mono hint ((integrable_const δ).add (hint.indicator hG.compl)) hpt
    _ = δ + ∫ x in Gᶜ, |K f x - r| ∂(gibbsMeasure ν) := by
        rw [integral_add (integrable_const δ) (hint.indicator hG.compl), integral_const,
          probReal_univ, one_smul, integral_indicator hG.compl]

/-- **The typical local closing**: two states, both DLR for `K` at `f`, with `|K f − r| ≤ δ` on `G`
and the part of `|K f − r|` off `G` at most `ε` under each, differ on `f` by at most `2(δ + ε)`. -/
theorem typical_local_closing (K : C(X, ℝ) → C(X, ℝ)) (ν₁ ν₂ : State X) (f : C(X, ℝ))
    (h₁ : ν₁ (K f) = ν₁ f) (h₂ : ν₂ (K f) = ν₂ f) {G : Set X} (hG : MeasurableSet G)
    {r δ ε : ℝ} (hδ : 0 ≤ δ) (hgood : ∀ x ∈ G, |K f x - r| ≤ δ)
    (hε₁ : ∫ x in Gᶜ, |K f x - r| ∂(gibbsMeasure ν₁) ≤ ε)
    (hε₂ : ∫ x in Gᶜ, |K f x - r| ∂(gibbsMeasure ν₂) ≤ ε) :
    |ν₁ f - ν₂ f| ≤ 2 * (δ + ε) := by
  have a₁ := typical_abs_le K ν₁ f h₁ hG hδ hgood
  have a₂ := typical_abs_le K ν₂ f h₂ hG hδ hgood
  have ht := abs_sub_le (ν₁ f) r (ν₂ f)
  rw [abs_sub_comm r] at ht
  linarith

/-- The part off `G` is at most the bound on `|K f − r|` times the mass of `Gᶜ`. -/
theorem setIntegral_compl_le_mass (ν : State X) (g : C(X, ℝ)) {G : Set X} (hG : MeasurableSet G)
    {r C : ℝ} (hC : ∀ x, |g x - r| ≤ C) :
    ∫ x in Gᶜ, |g x - r| ∂(gibbsMeasure ν) ≤ C * (gibbsMeasure ν).real Gᶜ := by
  rw [← integral_indicator hG.compl]
  have hint := integrable_abs_sub ν g r
  have hpt : ∀ x, Gᶜ.indicator (fun x => |g x - r|) x ≤ Gᶜ.indicator (fun _ => C) x := by
    intro x
    by_cases hx : x ∈ Gᶜ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact hC x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  calc ∫ x, Gᶜ.indicator (fun x => |g x - r|) x ∂(gibbsMeasure ν)
      ≤ ∫ x, Gᶜ.indicator (fun _ => C) x ∂(gibbsMeasure ν) :=
        integral_mono (hint.indicator hG.compl) ((integrable_const C).indicator hG.compl) hpt
    _ = C * (gibbsMeasure ν).real Gᶜ := by
        rw [integral_indicator_const _ hG.compl, smul_eq_mul, mul_comm]

/-- **The typical local closing, mass form**: `|K f − r| ≤ C` everywhere and `≤ δ` on `G`. -/
theorem typical_closing_mass (K : C(X, ℝ) → C(X, ℝ)) (ν₁ ν₂ : State X) (f : C(X, ℝ))
    (h₁ : ν₁ (K f) = ν₁ f) (h₂ : ν₂ (K f) = ν₂ f) {G : Set X} (hG : MeasurableSet G)
    {r δ C : ℝ} (hδ : 0 ≤ δ) (hgood : ∀ x ∈ G, |K f x - r| ≤ δ) (hC : ∀ x, |K f x - r| ≤ C) :
    |ν₁ f - ν₂ f|
      ≤ 2 * δ + C * ((gibbsMeasure ν₁).real Gᶜ + (gibbsMeasure ν₂).real Gᶜ) := by
  have a₁ := typical_abs_le K ν₁ f h₁ hG hδ hgood
  have a₂ := typical_abs_le K ν₂ f h₂ hG hδ hgood
  have m₁ := setIntegral_compl_le_mass ν₁ (K f) hG hC
  have m₂ := setIntegral_compl_le_mass ν₂ (K f) hG hC
  have ht := abs_sub_le (ν₁ f) r (ν₂ f)
  rw [abs_sub_comm r] at ht
  nlinarith

end Generic

/-! ## 2. The relative form -/

section Relative

variable {X : Type*} [TopologicalSpace X]

/-- `K` is additive, homogeneous, unital and positive: a Markov map on observables. -/
structure Markov (K : C(X, ℝ) → C(X, ℝ)) : Prop where
  add : ∀ f g : C(X, ℝ), K (f + g) = K f + K g
  smul : ∀ (c : ℝ) (f : C(X, ℝ)), K (c • f) = c • K f
  one : K 1 = 1
  pos : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ K f x

theorem Markov.sub {K : C(X, ℝ) → C(X, ℝ)} (hK : Markov K) (f g : C(X, ℝ)) :
    K (f - g) = K f - K g := by
  have h := hK.add (f - g) g
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem Markov.sub_const {K : C(X, ℝ) → C(X, ℝ)} (hK : Markov K) (f : C(X, ℝ)) (r : ℝ) :
    K (f - r • 1) = K f - r • 1 := by
  rw [hK.sub, hK.smul, hK.one]

/-- **Kadison–Schwarz for a Markov map**: `(K h x)² ≤ K (h²) x`. -/
theorem Markov.sq_le {K : C(X, ℝ) → C(X, ℝ)} (hK : Markov K) (h : C(X, ℝ)) (x : X) :
    K h x * K h x ≤ K (h * h) x := by
  obtain ⟨c, hc⟩ : ∃ c, c = K h x := ⟨_, rfl⟩
  have hp := hK.pos ((h - c • 1) * (h - c • 1)) (fun y => by
    simp only [ContinuousMap.mul_apply]
    exact mul_self_nonneg _) x
  have e : (h - c • (1 : C(X, ℝ))) * (h - c • 1) = h * h - (2 * c) • h + (c * c) • 1 := by
    ext y
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [e, hK.add, hK.sub, hK.smul, hK.smul, hK.one] at hp
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one] at hp
  rw [← hc] at hp ⊢
  linarith

/-- The squared deviation of `f` from `r`. -/
def sqDev (f : C(X, ℝ)) (r : ℝ) : C(X, ℝ) := (f - r • 1) * (f - r • 1)

theorem sqDev_apply (f : C(X, ℝ)) (r : ℝ) (x : X) : sqDev f r x = (f x - r) * (f x - r) := by
  simp [sqDev]

/-- The box reading's squared deviation is below the kernel of the squared deviation. -/
theorem Markov.sqDev_le {K : C(X, ℝ) → C(X, ℝ)} (hK : Markov K) (f : C(X, ℝ)) (r : ℝ) (x : X) :
    sqDev (K f) r x ≤ K (sqDev f r) x := by
  have h := hK.sq_le (f - r • 1) x
  rw [hK.sub_const] at h
  have e : sqDev (K f) r x = (K f - r • 1) x * (K f - r • 1) x := by
    simp [sqDev]
  rw [e]
  exact h

/-- The infimum of `t² m + V` over `2t`, `t > 0`, is at most `√(m V)`. -/
theorem le_sqrt_of_amgm {S m V : ℝ} (hm : 0 ≤ m)
    (h : ∀ t : ℝ, 0 < t → 2 * t * S ≤ t * t * m + V) : S ≤ Real.sqrt (m * V) := by
  by_contra hlt
  rw [not_le] at hlt
  have hS : 0 < S := lt_of_le_of_lt (Real.sqrt_nonneg _) hlt
  rcases eq_or_lt_of_le hm with hm0 | hm0
  · have hV : 0 ≤ V := by
      have := h 1 one_pos
      rw [← hm0] at this
      linarith
    have h1 := h ((V + 1) / S) (by positivity)
    have e : (V + 1) / S * S = V + 1 := div_mul_cancel₀ _ hS.ne'
    rw [← hm0, mul_zero, zero_add] at h1
    nlinarith
  · obtain ⟨t, ht⟩ : ∃ t, t = S / m := ⟨_, rfl⟩
    have htm : t * m = S := by rw [ht]; exact div_mul_cancel₀ _ hm0.ne'
    have htp : 0 < t := by rw [ht]; exact div_pos hS hm0
    have h1 := h t htp
    have e : t * t * m = t * S := by rw [mul_assoc, htm]
    rw [e] at h1
    have h2 : t * S ≤ V := by linarith
    have h3 : S * S ≤ m * V := by
      have := mul_le_mul_of_nonneg_left h2 hm
      calc S * S = (t * m) * S := by rw [htm]
        _ = m * (t * S) := by ring
        _ ≤ m * V := this
    have h4 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_mul_self hS.le] at h4
    linarith

variable [CompactSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The part off `G`, by the arithmetic–geometric mean**: at every `t`,
`2t ∫_{Gᶜ} |g − r| ≤ t² μ(Gᶜ) + ν (sqDev g r)`. -/
theorem setIntegral_compl_amgm (ν : State X) (g : C(X, ℝ)) {G : Set X} (hG : MeasurableSet G)
    (r t : ℝ) :
    2 * t * ∫ x in Gᶜ, |g x - r| ∂(gibbsMeasure ν)
      ≤ t * t * (gibbsMeasure ν).real Gᶜ + ν (sqDev g r) := by
  have hq : Integrable (fun x => sqDev g r x) (gibbsMeasure ν) := integrable_cm ν _
  have hab := integrable_abs_sub ν g r
  rw [← integral_indicator hG.compl, ← integral_const_mul]
  have hpt : ∀ x, 2 * t * Gᶜ.indicator (fun x => |g x - r|) x
      ≤ Gᶜ.indicator (fun _ => t * t) x + sqDev g r x := by
    intro x
    rw [sqDev_apply]
    by_cases hx : x ∈ Gᶜ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      nlinarith [sq_nonneg (|g x - r| - t), abs_mul_abs_self (g x - r)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      nlinarith [mul_self_nonneg (g x - r)]
  calc ∫ x, 2 * t * Gᶜ.indicator (fun x => |g x - r|) x ∂(gibbsMeasure ν)
      ≤ ∫ x, (Gᶜ.indicator (fun _ => t * t) x + sqDev g r x) ∂(gibbsMeasure ν) :=
        integral_mono ((hab.indicator hG.compl).const_mul _)
          (((integrable_const (t * t)).indicator hG.compl).add hq) hpt
    _ = t * t * (gibbsMeasure ν).real Gᶜ + ν (sqDev g r) := by
        rw [integral_add ((integrable_const (t * t)).indicator hG.compl) hq,
          integral_indicator_const _ hG.compl, smul_eq_mul, mul_comm ((gibbsMeasure ν).real Gᶜ),
          integral_gibbsMeasure]

/-- **The typical bound, relative to the second moment**: for `K` Markov, DLR at `f` and at
`sqDev f r`, `|ν f − r| ≤ δ + √(μ(Gᶜ) · ν (sqDev f r))`. -/
theorem typical_abs_le_rel {K : C(X, ℝ) → C(X, ℝ)} (hK : Markov K) (ν : State X) (f : C(X, ℝ))
    {r : ℝ} (hdlr : ν (K f) = ν f) (hdlr2 : ν (K (sqDev f r)) = ν (sqDev f r))
    {G : Set X} (hG : MeasurableSet G) {δ : ℝ} (hδ : 0 ≤ δ) (hgood : ∀ x ∈ G, |K f x - r| ≤ δ) :
    |ν f - r| ≤ δ + Real.sqrt ((gibbsMeasure ν).real Gᶜ * ν (sqDev f r)) := by
  have h1 := typical_abs_le K ν f hdlr hG hδ hgood
  have hV : ν (sqDev (K f) r) ≤ ν (sqDev f r) := by
    rw [← hdlr2]
    exact ν.mono (fun x => hK.sqDev_le f r x)
  have h2 : ∫ x in Gᶜ, |K f x - r| ∂(gibbsMeasure ν)
      ≤ Real.sqrt ((gibbsMeasure ν).real Gᶜ * ν (sqDev f r)) :=
    le_sqrt_of_amgm measureReal_nonneg (fun t _ => by
      have := setIntegral_compl_amgm ν (K f) hG r t
      linarith)
  linarith

/-- **The typical local closing, relative form**:
`|ν₁ f − ν₂ f| ≤ 2δ + √(μ₁(Gᶜ) V₁) + √(μ₂(Gᶜ) V₂)`, `Vᵢ = νᵢ (sqDev f r)`. -/
theorem typical_closing_rel {K : C(X, ℝ) → C(X, ℝ)} (hK : Markov K) (ν₁ ν₂ : State X)
    (f : C(X, ℝ)) {r : ℝ} (h₁ : ν₁ (K f) = ν₁ f) (h₂ : ν₂ (K f) = ν₂ f)
    (h₁' : ν₁ (K (sqDev f r)) = ν₁ (sqDev f r)) (h₂' : ν₂ (K (sqDev f r)) = ν₂ (sqDev f r))
    {G : Set X} (hG : MeasurableSet G) {δ : ℝ} (hδ : 0 ≤ δ) (hgood : ∀ x ∈ G, |K f x - r| ≤ δ) :
    |ν₁ f - ν₂ f|
      ≤ 2 * δ + (Real.sqrt ((gibbsMeasure ν₁).real Gᶜ * ν₁ (sqDev f r))
        + Real.sqrt ((gibbsMeasure ν₂).real Gᶜ * ν₂ (sqDev f r))) := by
  have a₁ := typical_abs_le_rel hK ν₁ f h₁ h₁' hG hδ hgood
  have a₂ := typical_abs_le_rel hK ν₂ f h₂ h₂' hG hδ hgood
  have ht := abs_sub_le (ν₁ f) r (ν₂ f)
  rw [abs_sub_comm r] at ht
  linarith

end Relative

/-! ## 3. The Wilson torus against the infinite volume -/

section Wilson

open MassGap.GibbsSpec MassGap.WilsonAction MassGap.CompactGauge MassGap.PeriodicStateDLR
  MassGap.PeriodicState MassGap.LocalClosing

variable {N : ℕ}

/-- **The box kernel is a Markov map.** -/
theorem markov_wspec (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) : Markov (wspec hN β Λ) where
  add := wspec_add hN β Λ
  smul := wspec_smul hN β Λ
  one := wspec_one hN β Λ
  pos _ hf ω := MassGap.WilsonDLR.spec_nonneg measurable_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β Λ (probHaar (MassGap.SUN.SU N)) hf ω

theorem isLocalOnC_sqDev {S : Finset ILink} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    (hF : IsLocalOnC S F) (r : ℝ) : IsLocalOnC S (sqDev F r) := by
  intro U V h
  rw [sqDev_apply, sqDev_apply, hF U V h]

/-- **The typical bound on the torus against the infinite volume**: a box and support that fit in
the torus of extent `M + 1`, a measurable good set `G`, a centre `r` and `δ ≥ 0` with
`|wspec F ω − r| ≤ δ` on `G`, and `2δ` plus the two off-`G` terms at most `Δ`. -/
def TypicalBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) :
    Prop :=
  ∃ (Λ S : Finset ILink) (G : Set (IConf (MassGap.SUN.SU N))) (r δ : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ MeasurableSet G ∧ 0 ≤ δ
    ∧ (∀ ω ∈ G, |wspec hN β Λ F ω - r| ≤ δ)
    ∧ 2 * δ + (Real.sqrt ((gibbsMeasure (torusState hN M β)).real Gᶜ
          * torusState hN M β (sqDev F r))
        + Real.sqrt ((gibbsMeasure (periodicState hN β)).real Gᶜ
          * periodicState hN β (sqDev F r))) ≤ Δ

/-- **The torus against the infinite volume, typical form.** -/
theorem TypicalBound.closing {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {Δ : ℝ} (h : TypicalBound hN M β F Δ) :
    |torusState hN M β F - periodicState hN β F| ≤ Δ := by
  obtain ⟨Λ, S, G, r, δ, hloc, hfit, hG, hδ, hgood, hle⟩ := h
  have hT := typical_closing_rel (markov_wspec hN β Λ) (torusState hN M β) (periodicState hN β) F
    (torusState_dlr hN M β Λ S F hloc hfit.1 hfit.2) (periodicState_dlr hN β Λ F)
    (torusState_dlr hN M β Λ S _ (isLocalOnC_sqDev hloc r) hfit.1 hfit.2)
    (periodicState_dlr hN β Λ _) hG hδ hgood
  linarith

/-- **A spread over every pair is a typical bound with `G` everything**, at twice the spread. -/
theorem typicalBound_of_spread (hN : N ≠ 0) {M : ℕ} {β : ℝ} {Λ S : Finset ILink}
    {F : C(IConf (MassGap.SUN.SU N), ℝ)} (hloc : IsLocalOnC S F) (hfit : BoxFits M Λ S) {d : ℝ}
    (hosc : ∀ ω ω', |wspec hN β Λ F ω - wspec hN β Λ F ω'| ≤ d) :
    TypicalBound hN M β F (2 * d) := by
  have hd : 0 ≤ d := le_trans (abs_nonneg _) (hosc (fun _ => 1) (fun _ => 1))
  refine ⟨Λ, S, Set.univ, wspec hN β Λ F (fun _ => 1), d, hloc, hfit, MeasurableSet.univ, hd,
    fun ω _ => hosc ω (fun _ => 1), ?_⟩
  simp only [Set.compl_univ, measureReal_empty, zero_mul, Real.sqrt_zero, add_zero, le_refl]

end Wilson

/-! ## 4. The pinned path -/

section Pixel

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing

variable {N : ℕ}

/-- **`BoxPixel` in typical form**: eventually in `k`, a typical bound for the infinite-volume
composite in the torus of `stateTD hN c k`, at `π · √(refMomentS)`. -/
def TypicalBoxPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop, TypicalBound hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k)
    (refObs (stateK hN k) O t ℓ k)
    (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k))

/-- `BoxPixel` gives `TypicalBoxPixel` at twice the constant. -/
theorem boxPixel_typical (hN : N ≠ 0) {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    (h : BoxPixel hN c O t ℓ π) : TypicalBoxPixel hN c O t ℓ (2 * π) := by
  filter_upwards [h] with k hk
  obtain ⟨Λ, S, hloc, hfit, hosc⟩ := hk
  have e : 2 * π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)
      = 2 * (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)) := by
    ring
  rw [e]
  exact typicalBound_of_spread hN hloc hfit hosc

/-- **The pixel from typical boundary influence and centring.** -/
theorem pixelPassage_of_typical (hN : N ≠ 0) {c : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ π₁ π₂ : ℝ} (hB : TypicalBoxPixel hN c O t ℓ π₁) (hC : CentringPixel hN c O t ℓ π₂) :
    LightConePassage.PixelPassage hN (RelativeDecay.stateTD hN c) O t ℓ (π₁ + π₂) := by
  filter_upwards [hB, hC] with k hk hc
  have h1 := hk.closing
  have h1' : |stateK hN k (refObs (stateK hN k) O t ℓ k)
      - RelativeDecay.stateTD hN c k (refObs (stateK hN k) O t ℓ k)|
      ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by
    rw [abs_sub_comm]
    exact h1
  calc |ExistenceReduce.refReading hN O t ℓ k - refReadingS (RelativeDecay.stateTD hN c) O t ℓ k|
      ≤ _ := pixel_split hN (RelativeDecay.stateTD hN c) O t ℓ k
    _ ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)
        + π₂ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) :=
        add_le_add h1' hc
    _ = (π₁ + π₂)
        * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by ring

/-- **`OnePointPixel` in typical form**: typical bounds `Δ₀`, `Δ₁` for the reflected and the plain
single-site field whose product with the cube weights is at most `π · √(refMomentS)`. -/
def TypicalOnePoint (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ Δ₀ Δ₁ : ℝ,
    TypicalBound hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) (O.refl 0).1 Δ₀
    ∧ TypicalBound hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) O.1 Δ₁
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)| * Δ₀
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)| * Δ₁)
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The centring from typical one-point bounds.** -/
theorem centringPixel_of_typical (hN : N ≠ 0) {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    (h : TypicalOnePoint hN c O t ℓ π) : CentringPixel hN c O t ℓ π := by
  filter_upwards [h] with k hk
  obtain ⟨Δ₀, Δ₁, h₀, h₁, hle⟩ := hk
  have d₀ : |stateK hN k (O.refl 0).1 - RelativeDecay.stateTD hN c k (O.refl 0).1| ≤ Δ₀ := by
    rw [abs_sub_comm]
    exact h₀.closing
  have d₁ : |stateK hN k O.1 - RelativeDecay.stateTD hN c k O.1| ≤ Δ₁ := by
    rw [abs_sub_comm]
    exact h₁.closing
  rw [centring_eq, abs_mul, abs_mul, abs_mul]
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left d₀ (abs_nonneg _))
    (mul_le_mul_of_nonneg_left d₁ (abs_nonneg _)) (by positivity)
    (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans d₀))) hle

/-- **The pinned path with `hpos` read through typical boundary influence and the floor.** -/
theorem clay_canonical_typical (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : TypicalBoxPixel hN c O t ℓ π₁) (h1 : TypicalOnePoint hN c O t ℓ π₂)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  LightConePassage.clay_canonical_lightCone hN2 hN O ht c hκ (add_nonneg hπ₁ hπ₂) hπκ
    (pixelPassage_of_typical hN hB (centringPixel_of_typical hN h1)) hF hD hℓ hW

end Pixel

/-! ## 5. The smooth good set and its mass -/

section Smooth

open MassGap.GibbsSpec MassGap.WilsonAction MassGap.PeriodicStateDLR MassGap.PeriodicState
  MassGap.LocalClosing

variable {N : ℕ}

/-- The boundary conditions whose plaquettes in `P` all have Wilson density at most `θ`. -/
def smoothSet (P : Finset IPlaq) (θ : ℝ) : Set (IConf (MassGap.SUN.SU N)) :=
  {U | ∀ q ∈ P, wilsonDensity (ihol q U) ≤ θ}

theorem isClosed_smoothSet (P : Finset IPlaq) (θ : ℝ) :
    IsClosed (smoothSet (N := N) P θ) := by
  have e : smoothSet (N := N) P θ = ⋂ q ∈ P, {U | wilsonDensity (ihol q U) ≤ θ} := by
    ext U
    simp [smoothSet]
  rw [e]
  exact isClosed_biInter (fun q _ =>
    isClosed_le (continuous_wilsonDensity.comp (MassGap.WilsonDLR.continuous_ihol q))
      continuous_const)

theorem measurableSet_smoothSet (P : Finset IPlaq) (θ : ℝ) :
    MeasurableSet (smoothSet (N := N) P θ) :=
  (isClosed_smoothSet P θ).measurableSet

/-- The complement of the smooth set is the union of the single-plaquette tail events. -/
theorem smoothSet_compl (P : Finset IPlaq) (θ : ℝ) :
    (smoothSet (N := N) P θ)ᶜ = ⋃ q ∈ P, {U | θ < wilsonDensity (ihol q U)} := by
  ext U
  simp [smoothSet]

/-- **The union bound**: the mass off the smooth set is at most the sum of the single-plaquette
tails, and at most `#P · τ` with a per-plaquette tail `τ`. -/
theorem mass_smooth_compl_le (μ : MeasureTheory.Measure (IConf (MassGap.SUN.SU N)))
    [IsFiniteMeasure μ] (P : Finset IPlaq) (θ τ : ℝ)
    (hτ : ∀ q ∈ P, μ.real {U | θ < wilsonDensity (ihol q U)} ≤ τ) :
    μ.real (smoothSet P θ)ᶜ ≤ P.card * τ := by
  rw [smoothSet_compl]
  calc μ.real (⋃ q ∈ P, {U | θ < wilsonDensity (ihol q U)})
      ≤ ∑ q ∈ P, μ.real {U | θ < wilsonDensity (ihol q U)} := measureReal_biUnion_finset_le _ _
    _ ≤ P.card • τ := Finset.sum_le_card_nsmul _ _ _ hτ
    _ = P.card * τ := nsmul_eq_mul _ _

/-- **The typical bound through the smooth set**: a spread at most `δ` about `r` on `smoothSet P θ`,
per-plaquette tails at most `τ` under the torus and the infinite-volume state, and
`2δ + √(#P τ V_T) + √(#P τ V_∞) ≤ Δ`. -/
def SmoothBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) :
    Prop :=
  ∃ (Λ S : Finset ILink) (P : Finset IPlaq) (θ r δ τ : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ 0 ≤ δ
    ∧ (∀ ω ∈ smoothSet P θ, |wspec hN β Λ F ω - r| ≤ δ)
    ∧ (∀ q ∈ P, (gibbsMeasure (torusState hN M β)).real
        {U | θ < wilsonDensity (ihol q U)} ≤ τ)
    ∧ (∀ q ∈ P, (gibbsMeasure (periodicState hN β)).real
        {U | θ < wilsonDensity (ihol q U)} ≤ τ)
    ∧ 2 * δ + (Real.sqrt (P.card * τ * torusState hN M β (sqDev F r))
        + Real.sqrt (P.card * τ * periodicState hN β (sqDev F r))) ≤ Δ

theorem sqDev_nonneg {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : State X)
    (f : C(X, ℝ)) (r : ℝ) : 0 ≤ ν (sqDev f r) :=
  ν.nonneg _ (fun x => by rw [sqDev_apply]; exact mul_self_nonneg _)

theorem typicalBound_of_smooth {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {Δ : ℝ} (h : SmoothBound hN M β F Δ) : TypicalBound hN M β F Δ := by
  obtain ⟨Λ, S, P, θ, r, δ, τ, hloc, hfit, hδ, hgood, hT, hP, hle⟩ := h
  refine ⟨Λ, S, smoothSet P θ, r, δ, hloc, hfit, measurableSet_smoothSet P θ, hδ, hgood, ?_⟩
  have mT := mass_smooth_compl_le _ P θ τ hT
  have mP := mass_smooth_compl_le _ P θ τ hP
  have sT := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right mT (sqDev_nonneg (torusState hN M β) F r))
  have sP := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right mP (sqDev_nonneg (periodicState hN β) F r))
  linarith

/-- **`TypicalBoxPixel` through the smooth set.** -/
def SmoothBoxPixel (hN : N ≠ 0) (c : ℕ) (O : MassGap.ContinuumField.LField (MassGap.SUN.SU N))
    (t ℓ π : ℝ) : Prop :=
  ∀ᶠ k in atTop, SmoothBound hN (2 * (2 ^ (c + k) - 1) + 1)
    (MassGap.ContinuumSchwinger.dyBeta (MassGap.ContinuumSchwinger.one_le_of_ne_zero hN) k)
    (refObs (MassGap.ContinuumSchwinger.stateK hN k) O t ℓ k)
    (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k))

theorem typicalBoxPixel_of_smooth (hN : N ≠ 0) {c : ℕ}
    {O : MassGap.ContinuumField.LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    (h : SmoothBoxPixel hN c O t ℓ π) : TypicalBoxPixel hN c O t ℓ π := by
  filter_upwards [h] with k hk
  exact typicalBound_of_smooth hk

end Smooth

/-! ## 6. The scaling of the union bound -/

section Scaling

theorem pow_eight_eq (k : ℕ) : (8 : ℝ) ^ k = Real.exp (k * Real.log 8) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- **The union bound closes** when the tail rate beats the count: `n_k ≤ C 8^k`,
`β_k ≥ b k − B`, `log 8 < b θ` give `n_k A e^{−β_k θ} → 0`. -/
theorem union_tail_tendsto_zero {C A θ b B : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (hrate : Real.log 8 < b * θ) {n β : ℕ → ℝ} (hn0 : ∀ k, 0 ≤ n k) (hn : ∀ k, n k ≤ C * 8 ^ k)
    (hβ : ∀ k, b * k - B ≤ β k) :
    Tendsto (fun k => n k * (A * Real.exp (-(β k * θ)))) atTop (nhds 0) := by
  set d := b * θ - Real.log 8 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hg : Tendsto (fun k : ℕ => C * A * Real.exp (B * θ) * Real.exp (-(d * k))) atTop
      (nhds (C * A * Real.exp (B * θ) * 0)) := by
    refine Tendsto.const_mul _ ?_
    refine Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_
    exact Tendsto.const_mul_atTop hd0 tendsto_natCast_atTop_atTop
  rw [mul_zero] at hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (hn0 k) (mul_nonneg hA (Real.exp_pos _).le)
  · have he : Real.exp (-(β k * θ)) ≤ Real.exp (-((b * k - B) * θ)) := by
      rw [Real.exp_le_exp]
      nlinarith [hβ k]
    calc n k * (A * Real.exp (-(β k * θ)))
        ≤ C * 8 ^ k * (A * Real.exp (-((b * k - B) * θ))) :=
          mul_le_mul (hn k) (mul_le_mul_of_nonneg_left he hA)
            (mul_nonneg hA (Real.exp_pos _).le) (by positivity)
      _ = C * A * (Real.exp (k * Real.log 8) * Real.exp (-((b * k - B) * θ))) := by
          rw [pow_eight_eq]; ring
      _ = C * A * Real.exp (k * Real.log 8 + -((b * k - B) * θ)) := by rw [Real.exp_add]
      _ = C * A * Real.exp (B * θ + -(d * k)) := by
          congr 2
          rw [hd]
          ring
      _ = C * A * Real.exp (B * θ) * Real.exp (-(d * k)) := by rw [Real.exp_add]; ring

/-- **The union bound diverges** when the count beats the tail rate: `n_k ≥ c 8^k`,
`β_k ≤ b k + B`, `b θ < log 8` give `n_k A e^{−β_k θ} → ∞`. -/
theorem union_tail_tendsto_top {c A θ b B : ℝ} (hc : 0 < c) (hA : 0 < A) (hθ : 0 ≤ θ)
    (hrate : b * θ < Real.log 8) {n β : ℕ → ℝ} (hn : ∀ k, c * 8 ^ k ≤ n k)
    (hβ : ∀ k, β k ≤ b * k + B) :
    Tendsto (fun k => n k * (A * Real.exp (-(β k * θ)))) atTop atTop := by
  set d := Real.log 8 - b * θ with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hg : Tendsto (fun k : ℕ => c * A * Real.exp (-(B * θ)) * Real.exp (d * k)) atTop atTop := by
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hd0 tendsto_natCast_atTop_atTop)
  refine tendsto_atTop_mono (fun k => ?_) hg
  have he : Real.exp (-((b * k + B) * θ)) ≤ Real.exp (-(β k * θ)) := by
    rw [Real.exp_le_exp]
    nlinarith [hβ k]
  calc c * A * Real.exp (-(B * θ)) * Real.exp (d * k)
      = c * A * (Real.exp (k * Real.log 8) * Real.exp (-((b * k + B) * θ))) := by
        rw [← Real.exp_add, mul_assoc (c * A), ← Real.exp_add]
        congr 2
        rw [hd]
        ring
    _ = c * 8 ^ k * (A * Real.exp (-((b * k + B) * θ))) := by rw [pow_eight_eq]; ring
    _ ≤ n k * (A * Real.exp (-(β k * θ))) :=
        mul_le_mul (hn k) (mul_le_mul_of_nonneg_left he hA.le)
          (mul_nonneg hA.le (Real.exp_pos _).le) (le_trans (by positivity) (hn k))

/-- **Smoothness on the vacuum width does not survive the union bound**: at `β_k θ_k ≤ κ`, a lower
tail `A e^{−β_k θ_k}` per plaquette and a count `n_k → ∞`, the union bound diverges. -/
theorem vacuum_width_tendsto_top {A κ : ℝ} (hA : 0 < A) {n β θ : ℕ → ℝ}
    (hn : Tendsto n atTop atTop) (hκ : ∀ k, β k * θ k ≤ κ) :
    Tendsto (fun k => n k * (A * Real.exp (-(β k * θ k)))) atTop atTop := by
  have hg : Tendsto (fun k => n k * (A * Real.exp (-κ))) atTop atTop :=
    hn.atTop_mul_const (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [hn.eventually_ge_atTop 0] with k hk
  have he : Real.exp (-κ) ≤ Real.exp (-(β k * θ k)) := by
    rw [Real.exp_le_exp]
    linarith [hκ k]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hA.le) hk

end Scaling

end MassGap.TypicalBoundary

#print axioms MassGap.TypicalBoundary.abs_sub_le_integral
#print axioms MassGap.TypicalBoundary.typical_abs_le
#print axioms MassGap.TypicalBoundary.typical_local_closing
#print axioms MassGap.TypicalBoundary.setIntegral_compl_le_mass
#print axioms MassGap.TypicalBoundary.typical_closing_mass
#print axioms MassGap.TypicalBoundary.Markov.sq_le
#print axioms MassGap.TypicalBoundary.Markov.sqDev_le
#print axioms MassGap.TypicalBoundary.le_sqrt_of_amgm
#print axioms MassGap.TypicalBoundary.setIntegral_compl_amgm
#print axioms MassGap.TypicalBoundary.typical_abs_le_rel
#print axioms MassGap.TypicalBoundary.typical_closing_rel
#print axioms MassGap.TypicalBoundary.markov_wspec
#print axioms MassGap.TypicalBoundary.TypicalBound.closing
#print axioms MassGap.TypicalBoundary.typicalBound_of_spread
#print axioms MassGap.TypicalBoundary.boxPixel_typical
#print axioms MassGap.TypicalBoundary.pixelPassage_of_typical
#print axioms MassGap.TypicalBoundary.centringPixel_of_typical
#print axioms MassGap.TypicalBoundary.clay_canonical_typical
#print axioms MassGap.TypicalBoundary.isClosed_smoothSet
#print axioms MassGap.TypicalBoundary.smoothSet_compl
#print axioms MassGap.TypicalBoundary.mass_smooth_compl_le
#print axioms MassGap.TypicalBoundary.typicalBound_of_smooth
#print axioms MassGap.TypicalBoundary.typicalBoxPixel_of_smooth
#print axioms MassGap.TypicalBoundary.union_tail_tendsto_zero
#print axioms MassGap.TypicalBoundary.union_tail_tendsto_top
#print axioms MassGap.TypicalBoundary.vacuum_width_tendsto_top
