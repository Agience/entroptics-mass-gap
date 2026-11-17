import Mathlib
import MassGap.OpenAIBridgeThermal

/-!
# MassGap.OpenAIBridgeNearCubic — the thermal remainder at a growing shortening

`OpenAIBridgeThermal.thermRem_shorten_moment` bounds the thermal remainder by the gap contraction
over `q' + 1` of its steps times the reflected moment on the torus shortened in time by
`2(q + 1) + 2(q' + 1)` steps.
Here the shortening is chosen from the seed side `n` and the half-side `m` of the cubic torus:

    q' + 1 = n · K,   K = ⌊√⌊m/n⌋⌋   (`shortSteps`).

Then `⌊(q'+1)/n⌋ = K`, so the contraction is `(1/2)^{2K}`, and `(q'+1) · K ≤ m`, so the shortening
`q' + 1` is at most the fraction `1/K` of `m` (`shortSteps_div`, `shortSteps_mul_le`). On their
family, `n · mesh ≤ ℓ` and `period ≤ 2 m · mesh` give `2ℓ K₀² ≤ period ⇒ K₀ ≤ K`
(`le_sqrt_of_period`); as the period tends to infinity along the order, `K` tends to infinity
eventually along the order and then in the spacing, with a threshold in the order independent of
the spacing (`eventually_le_sqrt`). The contraction then
tends to zero while `q' + 1` is at most the fraction `1/K` of `m`.

* `shortSteps`, `shortSteps_div`, `shortSteps_mul_le` — the choice of shortening.
* `le_sqrt_of_period`, `eventually_le_sqrt` — `K` grows with the period.
* `thermRem_nearCubic_moment` — the thermal remainder below `(1/2)^{2K}` times the reflected moment
  on the near-cubic torus.
* `thermRem_nearCubic_slab` — with the window data of the seed and `8(q' + n + 2) ≤ 2m`, the
  excited weight there is at most `1`: the remainder is below `(1/2)^{2K}` times twice the moment.
* `thermalRemainderVanishes_nearCubic` — a remainder below `(1/2)^{2K}` times an eventually bounded
  moment, on their family's bounds, satisfies `OpenAIBridgeCubic.ThermalRemainderVanishes`.

The bound on the reflected moments on the near-cubic tori is an input.
-/

namespace MassGap.OpenAIBridgeNearCubic

open MeasureTheory Real Filter
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCubic
  MassGap.OpenAIBridgeThermal

/-! ## The choice of shortening -/

/-- **The shortening steps** `n · ⌊√⌊m/n⌋⌋` for seed side `n` and half-side `m`. -/
def shortSteps (n m : ℕ) : ℕ := n * Nat.sqrt (m / n)

/-- **The contraction count of the shortening**: `⌊shortSteps n m / n⌋ = ⌊√⌊m/n⌋⌋`.

DERIVED: `0` is the sign of `n`. -/
theorem shortSteps_div {n : ℕ} (hn : 0 < n) (m : ℕ) : shortSteps n m / n = Nat.sqrt (m / n) := by
  unfold shortSteps
  exact Nat.mul_div_cancel_left _ hn

/-- **The shortening is at most the fraction `1/K` of `m`**: `shortSteps n m · ⌊√⌊m/n⌋⌋ ≤ m`. -/
theorem shortSteps_mul_le (n m : ℕ) : shortSteps n m * Nat.sqrt (m / n) ≤ m := by
  unfold shortSteps
  calc n * Nat.sqrt (m / n) * Nat.sqrt (m / n) = n * (Nat.sqrt (m / n) * Nat.sqrt (m / n)) := by
        ring
    _ ≤ n * (m / n) := Nat.mul_le_mul_left _ (Nat.sqrt_le _)
    _ ≤ m := Nat.mul_div_le m n

/-- **The contraction count grows with the period**: if `n · a ≤ ℓ`, `P ≤ 2 m a` and
`2 ℓ K₀² ≤ P` with `a > 0`, then `K₀ ≤ ⌊√⌊m/n⌋⌋`.

DERIVED: `2` is the doubled half-side and the square; `0` the signs of `n` and `a`. -/
theorem le_sqrt_of_period {n m K₀ : ℕ} {a ℓ P : ℝ} (hn : 0 < n) (ha : 0 < a)
    (hna : (n : ℝ) * a ≤ ℓ) (hP : P ≤ 2 * ((m : ℝ) * a)) (hK : 2 * ℓ * (K₀ : ℝ) ^ 2 ≤ P) :
    K₀ ≤ Nat.sqrt (m / n) := by
  rw [Nat.le_sqrt, Nat.le_div_iff_mul_le hn]
  have h1 : (n : ℝ) * a * (K₀ : ℝ) ^ 2 ≤ ℓ * (K₀ : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hna (sq_nonneg _)
  have h : ((K₀ * K₀ * n : ℕ) : ℝ) * a ≤ (m : ℝ) * a := by
    push_cast
    nlinarith
  exact_mod_cast le_of_mul_le_mul_right h ha

/-- **The contraction count tends to infinity along the order**: if their period `P` tends to
infinity and, eventually along the order and then in the spacing, `n > 0`, `n · a ≤ ℓ` and
`P ≤ 2 m a` with `a > 0`, then for every `K₀`, eventually along the order and then in the spacing,
`K₀ ≤ ⌊√⌊m/n⌋⌋`.

DERIVED: `2` is the doubled half-side and the square; `0` the signs of `n` and `a`. -/
theorem eventually_le_sqrt {P : ℕ → ℝ} (hP : Tendsto P atTop atTop) {ℓ : ℝ} {a : ℕ → ℝ}
    (ha : ∀ N, 0 < a N) {n m : ℕ → ℕ → ℕ}
    (hev : ∀ᶠ p in atTop, ∀ᶠ N in atTop,
      0 < n p N ∧ (n p N : ℝ) * a N ≤ ℓ ∧ P p ≤ 2 * ((m p N : ℝ) * a N)) (K₀ : ℕ) :
    ∀ᶠ p in atTop, ∀ᶠ N in atTop, K₀ ≤ Nat.sqrt (m p N / n p N) := by
  filter_upwards [hev, hP.eventually_ge_atTop (2 * ℓ * (K₀ : ℝ) ^ 2)] with p h1 h2
  filter_upwards [h1] with N hN
  exact le_sqrt_of_period hN.1 (ha N) hN.2.1 hN.2.2 h2

/-! ## The thermal remainder on the near-cubic torus -/

section Shorten

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

variable (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) {n : ℕ}
  (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖
      ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖)

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The thermal remainder below the reflected moment on the near-cubic torus**: for
`q' + 1 = shortSteps n m`,

    D_L(f; p + 1, p' + q' + 1) ≤ (1/2)^{2⌊√⌊m/n⌋⌋} (1 + σ₀') E_{L'}[f · θf],

`σ₀' = excited (w + p + p' + 2)` and `E_{L'}` the reflected moment at separations `2p + 2`, `2p' + 2`
on the torus of `L' = 2(w + p + p' + 2)` steps (`OpenAIBridgeThermal.thermRem_shorten_moment` with
`q = 0`, whose contraction factor is at most `1`, and `shortSteps_div`).

DERIVED: `1/2` is the contraction; `1` the vacuum's own weight and the offsets; `2` the squares and
the offset of the excited weight; `0` the unshortened left side and the signs. -/
theorem thermRem_nearCubic_moment (hc0 : c ≠ 0) (hn : 0 < n) {F : X → X → ℝ} (hF : Bdd F)
    (w p p' q' m : ℕ) (hq : q' + 1 = shortSteps n m) :
    thermRem μ k c φ F w (p + 1) (p' + q' + 1)
      ≤ ((1 / 2) ^ Nat.sqrt (m / n)) ^ 2
        * ((1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1)) := by
  have h := thermRem_shorten_moment hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF w p 0 p' q'
  rw [Nat.add_zero, hq, shortSteps_div hn] at h
  have hX : 0 ≤ (1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1) :=
    (thermRem_nonneg (μ := μ) k c φ F w p p').trans
      (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w p p').1
  have h1 : ((1 / 2 : ℝ) ^ ((0 + 1) / n)) ^ 2 ≤ 1 :=
    pow_le_one₀ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  refine h.trans ?_
  calc ((1 / 2 : ℝ) ^ ((0 + 1) / n)) ^ 2 * ((1 / 2) ^ Nat.sqrt (m / n)) ^ 2
        * ((1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1))
      ≤ 1 * ((1 / 2) ^ Nat.sqrt (m / n)) ^ 2
        * ((1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hX
    _ = ((1 / 2) ^ Nat.sqrt (m / n)) ^ 2
        * ((1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1)) := by
        ring

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The thermal remainder below the reflected moment alone**: with the window data of the seed
on the torus of `2m` steps (`σ_{j0} ≤ (1/2)^{2^a}`, `4 j0 ≤ 2m ≤ 2^(a+3) n`, the output of
`OpenAIBridgeGroups.gap_side_excitedG`), `m = w + p + p' + q' + 4` and
`4(2q' + 4) + 8n ≤ 2m`, for `q' + 1 = shortSteps n m`,

    D_L(f; p + 1, p' + q' + 1) ≤ (1/2)^{2⌊√⌊m/n⌋⌋} · 2 E_{L'}[f · θf].

The shortened torus of `L' = 2(w + p + p' + 2)` steps leaves the slab of `2q' + 4` steps, and
`OpenAIBridgeSlab.excited_le_slab` gives `σ₀' ≤ (1/2)^⌊(w + p + p' + 2)/n⌋ ≤ 1`, and
`thermRem_nearCubic_moment` concludes.

DERIVED: `4` and `8` are the slab condition of `excited_le_slab`, `4` also the offsets
`2 + 2` of the two separations; `3` the window exponent; `1/2` the contraction; `2` the doubled
half-side, the squares and the bound `1 + σ₀' ≤ 2`; `1` the least `j0`, the offsets `q' + 1` and
`w + p + p' + 1`, and the vacuum's weight in `1 + σ₀' ≤ 2`; `0` the signs. -/
theorem thermRem_nearCubic_slab (hc0 : c ≠ 0) (hn : 0 < n) {F : X → X → ℝ} (hF : Bdd F)
    {a j0 : ℕ} (hj0 : 1 ≤ j0) (w p p' q' m : ℕ) (hL4 : 2 * (2 * j0) ≤ 2 * m)
    (hhi : 2 * m ≤ 2 ^ (a + 3) * n) (hexc : excited μ k c φ j0 ≤ (1 / 2) ^ (2 ^ a))
    (hm : w + p + p' + q' + 4 = m) (hW : 4 * (2 * q' + 4) + 8 * n ≤ 2 * m)
    (hq : q' + 1 = shortSteps n m) :
    thermRem μ k c φ F w (p + 1) (p' + q' + 1)
      ≤ ((1 / 2) ^ Nat.sqrt (m / n)) ^ 2 * (2 * torusMom μ k F p p' (w + p + p' + 1)) := by
  have h := thermRem_nearCubic_moment hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hn hF
    w p p' q' m hq
  have hσ := excited_le_slab hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hn hj0 hL4 hhi hexc
    (ℓ := w + p + p' + 2) (W := 2 * q' + 4) (by omega) hW
  have hσ1 : excited μ k c φ (w + p + p' + 2) ≤ 1 :=
    hσ.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hσ0 : 0 ≤ excited μ k c φ (w + p + p' + 2) := by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have hX : 0 ≤ (1 + excited μ k c φ (w + p + p' + 2)) * torusMom μ k F p p' (w + p + p' + 1) :=
    (thermRem_nonneg (μ := μ) k c φ F w p p').trans
      (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w p p').1
  have hT : 0 ≤ torusMom μ k F p p' (w + p + p' + 1) :=
    nonneg_of_mul_nonneg_right (by rwa [mul_comm] at hX) (by linarith)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact mul_le_mul_of_nonneg_right (by linarith) hT

end Shorten

/-! ## Vanishing on near-cubic tori -/

/-- **The thermal remainders vanish from bounded moments on near-cubic tori**: if their period `P`
tends to infinity and, eventually along the order and then in the spacing, `n > 0`, `n · a ≤ ℓ`,
`P ≤ 2 m a` and `D p N ≤ (1/2)^{2⌊√⌊m/n⌋⌋} M p N`, with `a > 0` and `M` eventually at most `M₀`,
then `ThermalRemainderVanishes D`. With `thermRem_nearCubic_moment`, `M` is `1 + σ₀'` times the
reflected moment on the torus shortened by `2(1 + shortSteps n m)` steps, with
`shortSteps n m · ⌊√⌊m/n⌋⌋ ≤ m` (`shortSteps_mul_le`).

DERIVED: `1/2` is the contraction; `2` the square and the doubled half-side; `0` the signs. -/
theorem thermalRemainderVanishes_nearCubic {P : ℕ → ℝ} (hP : Tendsto P atTop atTop) {ℓ M₀ : ℝ}
    {a : ℕ → ℝ} (ha : ∀ N, 0 < a N) {n m : ℕ → ℕ → ℕ} {D M : ℕ → ℕ → ℝ}
    (hev : ∀ᶠ p in atTop, ∀ᶠ N in atTop,
      0 < n p N ∧ (n p N : ℝ) * a N ≤ ℓ ∧ P p ≤ 2 * ((m p N : ℝ) * a N) ∧
        D p N ≤ ((1 / 2 : ℝ) ^ Nat.sqrt (m p N / n p N)) ^ 2 * M p N)
    (hM : ∀ᶠ p in atTop, ∀ᶠ N in atTop, M p N ≤ M₀) :
    ThermalRemainderVanishes D := by
  have hgeom : ∀ᶠ p in atTop, ∀ᶠ N in atTop,
      0 < n p N ∧ (n p N : ℝ) * a N ≤ ℓ ∧ P p ≤ 2 * ((m p N : ℝ) * a N) := by
    filter_upwards [hev] with p hp
    filter_upwards [hp] with N hN
    exact ⟨hN.1, hN.2.1, hN.2.2.1⟩
  refine thermalRemainderVanishes_of_bound (s := fun p N => ((1 / 2 : ℝ) ^ Nat.sqrt (m p N / n p N)) ^ 2)
    ?_ ?_ hM
  · filter_upwards [hev] with p hp
    filter_upwards [hp] with N hN
    exact hN.2.2.2
  · intro ε hε
    obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [eventually_le_sqrt hP ha hgeom K₀] with p hp
    filter_upwards [hp] with N hN
    refine ⟨by positivity, ?_⟩
    have e1 : ((1 / 2 : ℝ) ^ Nat.sqrt (m p N / n p N)) ^ 2 ≤ (1 / 2 : ℝ) ^ Nat.sqrt (m p N / n p N) :=
      pow_le_of_le_one (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)) two_ne_zero
    have e2 : (1 / 2 : ℝ) ^ Nat.sqrt (m p N / n p N) ≤ (1 / 2 : ℝ) ^ K₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
    exact e1.trans (e2.trans hK₀.le)

end MassGap.OpenAIBridgeNearCubic

#print axioms MassGap.OpenAIBridgeNearCubic.shortSteps_div
#print axioms MassGap.OpenAIBridgeNearCubic.shortSteps_mul_le
#print axioms MassGap.OpenAIBridgeNearCubic.le_sqrt_of_period
#print axioms MassGap.OpenAIBridgeNearCubic.eventually_le_sqrt
#print axioms MassGap.OpenAIBridgeNearCubic.thermRem_nearCubic_moment
#print axioms MassGap.OpenAIBridgeNearCubic.thermRem_nearCubic_slab
#print axioms MassGap.OpenAIBridgeNearCubic.thermalRemainderVanishes_nearCubic
