import Mathlib
import MassGap.ExistencePosNonnull
import MassGap.NonTrivialCanonical

noncomputable section

/-!
# MassGap.DiagBoundProof — `hD` of the pinned path as a unit-strength ratio

`ExistenceReduce.clay_canonical` carries `hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0`:
every separated positive-time monomial `P` has its reflected second moment at the canonical factor bounded,
eventually in the step. `zCan` is one number for every field, `1/√(refReading_k)`, so the canonical reading of
`θP ∪ P` is `refReading_k^{−|P|}` times its unit-strength reading (`latSkR_zCan_pair`).

* `MonoRatio hN O t ℓ`: for every `P : SepMono N 0` one `C` with, eventually in the step,
  `latSkR (rho1) (θP ∪ P) ≤ C · refReading_k^{|P|}`. It is a statement per monomial and eventually in the step
  (uniform in `k` past a threshold that depends on `P`); the state is the infinite-volume periodic state of
  each step, so no volume enters.
* `diagBoundSep_zCan_of_monoRatio`: `MonoRatio` gives `hD`, with no positivity hypothesis.
* `monoRatio_of_diagBoundSep_zCan`: the converse at an eventually positive reference reading;
  `diagBoundSep_zCan_iff_monoRatio` the equivalence.
* `unitRatio_refSpan`: the part of `MonoRatio` that reflection positivity gives. One-field monomials of the
  reference field whose test function lies in the span of forward-time, spatially shifted dyadic translates of the
  reference cube satisfy the ratio bound with `C = n ∑ cᵢ²` (`ExistencePos.diag_refSpan_le`).
* `lagFacts_bound_nothing_upward`: the facts reflection positivity gives a lag profile — non-negative,
  non-increasing, log-convex — bound no reading at a shorter lag by a multiple of a reading at a longer lag:
  `b_n = εⁿ` has all three and `b₀/b₁ = 1/ε`. Shrinking the separation of a monomial below the reference's
  therefore needs an input beyond reflection positivity; in the tree that input is the running bound
  `ShortDistanceRunning.RunningBelow` with `PointCubeLocal`, which give `hD` through `PointReadingRatio`.
* `clay_canonical_monoRatio`: the pinned path with `hD` replaced by `MonoRatio`.
-/

namespace MassGap.DiagBoundProof

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ExistenceReduce Filter

variable {N : ℕ}

/-! ## 1. The canonical reading of a reflected pair -/

/-- **The canonical reading of `θP ∪ P` is `((1/√r)²)^{|P|}` times its unit-strength reading.** -/
theorem latSkR_zCan_pair (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ)
    (P : Mono N) :
    latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k (pairFam 0 P P)
      = ((1 / Real.sqrt (refReading hN O t ℓ k)) ^ 2) ^ P.1
          * latSkR hN (NonTrivialCanonical.rho1 hN) k (pairFam 0 P P) := by
  rw [NonTrivialCanonical.latSkR_zCan_eq, Fintype.card_sum, Fintype.card_fin, ← pow_mul, two_mul]

/-- A unit-strength bound `u ≤ C rⁿ` bounds the normalised value `((1/√r)²)ⁿ u` by `max C 0`, at every `r`. -/
theorem ratio_le {r u C : ℝ} (n : ℕ) (h : u ≤ C * r ^ n) :
    ((1 / Real.sqrt r) ^ 2) ^ n * u ≤ max C 0 := by
  by_cases hr : 0 < r
  · have hs : (1 / Real.sqrt r) ^ 2 = r⁻¹ := by
      rw [div_pow, one_pow, Real.sq_sqrt hr.le, one_div]
    have hrn : 0 < r ^ n := pow_pos hr n
    rw [hs, inv_pow]
    calc (r ^ n)⁻¹ * u ≤ (r ^ n)⁻¹ * (C * r ^ n) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hrn.le)
      _ = C := by rw [mul_comm C, ← mul_assoc, inv_mul_cancel₀ hrn.ne', one_mul]
      _ ≤ max C 0 := le_max_left _ _
  · have hs : Real.sqrt r = 0 := Real.sqrt_eq_zero'.mpr (le_of_not_gt hr)
    rw [hs, div_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [pow_zero, one_mul]
      rw [pow_zero, mul_one] at h
      exact h.trans (le_max_left _ _)
    · rw [zero_pow two_ne_zero, zero_pow hn.ne', zero_mul]
      exact le_max_right _ _

/-- At `r > 0` a normalised bound `((1/√r)²)ⁿ u ≤ C` is the unit-strength bound `u ≤ C rⁿ`. -/
theorem le_of_ratio {r u C : ℝ} (n : ℕ) (hr : 0 < r) (h : ((1 / Real.sqrt r) ^ 2) ^ n * u ≤ C) :
    u ≤ C * r ^ n := by
  have hs : (1 / Real.sqrt r) ^ 2 = r⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt hr.le, one_div]
  rw [hs, inv_pow] at h
  have hrn : 0 < r ^ n := pow_pos hr n
  calc u = r ^ n * ((r ^ n)⁻¹ * u) := by rw [← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul]
    _ ≤ r ^ n * C := mul_le_mul_of_nonneg_left h hrn.le
    _ = C * r ^ n := mul_comm _ _

/-! ## 2. `hD` is the unit-strength ratio -/

/-- **The unit-strength ratio bound on separated monomials.** For every separated positive-time monomial `P`
there is one `C` with `latSkR (rho1) (θP ∪ P) ≤ C · refReading_k^{|P|}` eventually in the step. -/
def MonoRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∀ P : ContinuumSep.SepMono N 0, ∃ C : ℝ, ∀ᶠ k in atTop,
    latSkR hN (NonTrivialCanonical.rho1 hN) k (pairFam 0 P.1 P.1)
      ≤ C * refReading hN O t ℓ k ^ P.1.1

/-- **`MonoRatio` gives `hD`**, with no positivity hypothesis. -/
theorem diagBoundSep_zCan_of_monoRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h : MonoRatio hN O t ℓ) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0 := by
  intro P
  obtain ⟨C, hC⟩ := h P
  refine ⟨max C 0, ?_⟩
  filter_upwards [hC] with k hk
  show latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k (pairFam 0 P.1 P.1) ≤ max C 0
  rw [latSkR_zCan_pair]
  exact ratio_le _ hk

/-- **`hD` gives `MonoRatio`** at an eventually positive reference reading. -/
theorem monoRatio_of_diagBoundSep_zCan (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k)
    (h : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0) :
    MonoRatio hN O t ℓ := by
  intro P
  obtain ⟨C, hC⟩ := h P
  refine ⟨C, ?_⟩
  filter_upwards [hC, hpos] with k hk hr
  have hk' : latSkR hN (Renorm.connected hN (zCan hN O t ℓ)) k (pairFam 0 P.1 P.1) ≤ C := hk
  rw [latSkR_zCan_pair] at hk'
  exact le_of_ratio _ hr hk'

/-- **`hD` is `MonoRatio`** at an eventually positive reference reading. -/
theorem diagBoundSep_zCan_iff_monoRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0 ↔ MonoRatio hN O t ℓ :=
  ⟨monoRatio_of_diagBoundSep_zCan hN O t ℓ hpos, diagBoundSep_zCan_of_monoRatio hN O t ℓ⟩

/-! ## 3. What reflection positivity gives, and what it does not -/

/-- **The ratio bound on the dyadic span of the reference cube.** For a one-field monomial of the reference
field whose test function is `∑ᵢ cᵢ · (reference cube translated by dySpacing N m · (jᵢ e₀ + xsᵢ))`, `jᵢ ≥ 0`,
`xsᵢ` spatial, the unit-strength reflected diagonal is eventually at most `n ∑ cᵢ² · refReading_k`. -/
theorem unitRatio_refSpan (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t)
    (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k) (f : TestFn) {n m : ℕ}
    (c : Fin n → ℝ) (j : Fin n → ℕ) (xs : Fin n → MassGap.InfiniteLattice.ISite)
    (hxs : ∀ i, xs i 0 = 0)
    (hf : ∀ y, f.1 y = ∑ i, c i * ((ContinuumNontrivial.cubeTest t ℓ).translate
      (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))).1 y) :
    ∀ᶠ k in atTop,
      latSkR hN (NonTrivialCanonical.rho1 hN) k
          (pairFam 0 (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f)))
        ≤ (n * ∑ i, c i ^ 2) * refReading hN O t ℓ k ^ 1 := by
  filter_upwards [ExistencePos.diag_refSpan_le hN O ht hpos f c j xs hxs hf, hpos] with k hk hr
  rw [latSkR_zCan_pair] at hk
  exact le_of_ratio 1 hr hk

/-- **The lag-profile facts bound nothing upward.** For every `C` there is a sequence that is non-negative,
non-increasing and log-convex — the properties reflection positivity gives the lag profile of a positive
transfer (`ChessboardRead.lagProfile_nonneg`, `ChessboardRead.lagProfile_log_convex`, `T_contract`) — with
`b₀ > C · b₁`. -/
theorem lagFacts_bound_nothing_upward (C : ℝ) :
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (∀ n, b (n + 1) ≤ b n) ∧
      (∀ n, b (n + 1) ^ 2 ≤ b n * b (n + 2)) ∧ C * b 1 < b 0 := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (|C| + 1) := ⟨_, rfl⟩
  have hA : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hA]
    linarith [abs_nonneg C]
  refine ⟨fun n => ε ^ n, fun n => (pow_pos hε n).le, fun n => ?_, fun n => le_of_eq (by ring), ?_⟩
  · show ε ^ (n + 1) ≤ ε ^ n
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hε.le n) hε1
  · show C * ε ^ 1 < ε ^ 0
    rw [pow_one, pow_zero]
    have h1 : C * ε ≤ |C| * ε := mul_le_mul_of_nonneg_right (le_abs_self C) hε.le
    have h2 : |C| * ε = |C| / (|C| + 1) := by rw [hεdef]; ring
    have h3 : |C| / (|C| + 1) < 1 := (div_lt_one hA).mpr (by linarith)
    linarith

/-! ## 4. The pinned path with `hD` replaced by `MonoRatio` -/

/-- **The pinned path at the canonical normalisation, with `hD` as the unit-strength ratio.** -/
theorem clay_canonical_monoRatio (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (hpos : ∀ᶠ k in atTop, 0 < refReading hN O t ℓ k) (hM : MonoRatio hN O t ℓ)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ))
        (diagBoundSep_zCan_of_monoRatio hN O t ℓ hM)) (5 * ℓ₀) :=
  clay_canonical hN2 hN O ht hpos (diagBoundSep_zCan_of_monoRatio hN O t ℓ hM) hℓ hW

end MassGap.DiagBoundProof

#print axioms MassGap.DiagBoundProof.latSkR_zCan_pair
#print axioms MassGap.DiagBoundProof.ratio_le
#print axioms MassGap.DiagBoundProof.le_of_ratio
#print axioms MassGap.DiagBoundProof.diagBoundSep_zCan_of_monoRatio
#print axioms MassGap.DiagBoundProof.monoRatio_of_diagBoundSep_zCan
#print axioms MassGap.DiagBoundProof.diagBoundSep_zCan_iff_monoRatio
#print axioms MassGap.DiagBoundProof.unitRatio_refSpan
#print axioms MassGap.DiagBoundProof.lagFacts_bound_nothing_upward
#print axioms MassGap.DiagBoundProof.clay_canonical_monoRatio
