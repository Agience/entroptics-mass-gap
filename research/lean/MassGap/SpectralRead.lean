import Mathlib
import MassGap.SpectralRep
import MassGap.ZeroMode

/-!
# The read of a spectral measure

A correlation profile that is a weighted moment sequence of a measure `w` on `[0, 1]`,
`ρ(d) = ∫ g(λ) λ^{circLag d} dw(λ)` with a continuous weight `g ≥ 0` that vanishes below `λ₀`, is read
through a screen of `n = 2(k + 1)` lags. Every point of the weight's support spreads the profile around
the circle at least as far as `λ₀` does (`ZeroMode.twelve_weighted_moment_ge`), so the read's
substrate is at least `λ₀^{k+1}/12` (`substrate_ge_of_weight`). A tension below the floor `¼·log 3`
caps the substrate (`Moment.Read.substrate_lt_of_tension_lt_floor`), so

    0 < ⟨cos⟩  and  μ < κ₀   ⟹   λ₀^{k+1} < 12 · (1 − 3^{−1/4}) / 8

(`lam0_pow_lt_of_tension`). This is the weighted-measure analogue of `ZeroMode.lam_pow_lt_of_tension`;
a point mass at `λ` is covered for every `λ₀ < λ`. `SpectralRep.exists_spectral_measure` supplies the measure of a vector; the weight
is `φ²` for a ramp `φ`, which is how `SpectralGap` isolates spectral weight near `1` into a vector.
-/

namespace MassGap.SpectralRead

open MeasureTheory MassGap.ZeroMode

/-- The `c`-th moment of a measure on `[0, 1]` against the weight `g`.

DERIVED: `0` and `1` are the interval's ends. -/
noncomputable def momW (w : Measure (Set.Icc (0 : ℝ) 1)) (g : Set.Icc (0 : ℝ) 1 → ℝ) (c : ℕ) : ℝ :=
  ∫ t, g t * (t : ℝ) ^ c ∂w

/-- `ZeroMode.twelve_weighted_moment_ge` at a point `λ` above `λ₀`: `λ₀^{k+1} n³` is at most `12`
times the weighted second moment of `λ`'s circle profile, `n = 2(k + 1)`.

DERIVED: `2`, `12` and the exponents `2` and `3` are `twelve_weighted_moment_ge`'s; `0` and `1`
bracket `λ₀ ≤ λ`, and `1` is also the `+ 1` of the extent. -/
theorem twelve_weighted_moment_ge_of_le (k : ℕ) {lam0 lam : ℝ} (h0 : 0 ≤ lam0)
    (hle : lam0 ≤ lam) (h1 : lam ≤ 1) :
    lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3
      ≤ 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 :=
  (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hle _) (by positivity)).trans
    (twelve_weighted_moment_ge k lam (h0.trans hle) h1)

#print axioms twelve_weighted_moment_ge_of_le

/-- **A weighted spectral measure above `λ₀` has a large substrate.** For a finite measure `w` on
`[0, 1]` and a continuous weight `g ≥ 0` vanishing below `λ₀`, with `n = 2(k + 1)`:

    λ₀^{k+1} · n² · ∑_{d<n} momW(clag d)  ≤  12 · ∑_{d<n} momW(clag d) · (clag d)²

The zeroth sum is at most `(∫ g) · n`, every power being at most `1`; the second dominates
`(∫ g) · λ₀^{k+1} n³ / 12` by integrating `twelve_weighted_moment_ge_of_le` against `g dw`.

DERIVED: `2`, `12` and the exponents are `twelve_weighted_moment_ge`'s; `0` and `1` are the
interval's ends and the lower end of `λ₀` and of `g`; `1` is also the `+ 1` of the extent. -/
theorem substrate_ge_of_weight (k : ℕ) (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (g : Set.Icc (0 : ℝ) 1 → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (lam0 : ℝ) (h0 : 0 ≤ lam0) (hgs : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) < lam0 → g t = 0) :
    lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
        * ∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d)
      ≤ 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          momW w g (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
  have hint : ∀ c : ℕ, Integrable (fun t : Set.Icc (0 : ℝ) 1 => g t * (t : ℝ) ^ c) w :=
    fun c => SpectralRep.integrable_of_continuous w (hg.mul (continuous_subtype_val.pow c))
  have hG : Integrable g w := SpectralRep.integrable_of_continuous w hg
  have hS0le : ∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d)
      ≤ (∫ t, g t ∂w) * ((2 * (k + 1) : ℕ) : ℝ) := by
    calc ∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d)
        ≤ ∑ _d ∈ Finset.range (2 * (k + 1)), ∫ t, g t ∂w := by
          refine Finset.sum_le_sum (fun d _ => ?_)
          exact integral_mono (hint _) hG
            (fun t => mul_le_of_le_one_right (hg0 t) (pow_le_one₀ t.2.1 t.2.2))
      _ = (∫ t, g t ∂w) * ((2 * (k + 1) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hS2ge : (∫ t, g t ∂w) * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3)
      ≤ 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          momW w g (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    have hL : (∫ t, g t ∂w) * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3)
        = ∫ t, g t * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3) ∂w :=
      (integral_mul_const _ _).symm
    have hR : 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          momW w g (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2
        = ∫ t, 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          g t * (t : ℝ) ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 ∂w := by
      rw [integral_const_mul, integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [integral_mul_const]
        rfl
      · intro d _
        exact (hint _).mul_const _
    rw [hL, hR]
    refine integral_mono (hG.mul_const _) ?_ (fun t => ?_)
    · exact (integrable_finsetSum _ (fun d _ => (hint _).mul_const _)).const_mul _
    · by_cases ht : (t : ℝ) < lam0
      · simp [hgs t ht]
      · push_neg at ht
        have hm := twelve_weighted_moment_ge_of_le k h0 ht t.2.2
        calc g t * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3)
            ≤ g t * (12 * ∑ d ∈ Finset.range (2 * (k + 1)),
                (t : ℝ) ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_left hm (hg0 t)
          _ = 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
                g t * (t : ℝ) ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
              rw [mul_left_comm, Finset.mul_sum]
              congr 1
              exact Finset.sum_congr rfl (fun d _ => by ring)
  have hc : 0 ≤ lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2 :=
    mul_nonneg (pow_nonneg h0 _) (by positivity)
  calc lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
        * ∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d)
      ≤ lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * ((∫ t, g t ∂w) * ((2 * (k + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hS0le hc
    _ = (∫ t, g t ∂w) * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3) := by ring
    _ ≤ _ := hS2ge

#print axioms substrate_ge_of_weight

/-- **The read of a weighted spectral measure bounds where it can sit.** A read at aperture `2k + 1`
whose correlation is `ρ(d) = momW w g (circLag d)`, with a continuous weight `g ≥ 0` vanishing below
`λ₀`, a positive cosine average and a tension below the floor, gives

    λ₀^{k+1}  <  12 · (1 − 3^{−1/4}) / 8.

The positive cosine average is needed: `Real.log 0 = 0`, so the flat profile of a point mass at `1`
has tension `0`. `Moment.Read.substrate_lt_of_tension_lt_floor` caps the substrate and
`substrate_ge_of_weight` bounds it below; this is the weighted-measure analogue of
`ZeroMode.lam_pow_lt_of_tension`, a point mass at `λ` being covered for every `λ₀ < λ`.

DERIVED: `12` is the sum-of-squares denominator, `8` the constant of `cos_avg_le_circ`, and
`3^{−1/4}` is `e^{−κ₀}` with the floor `κ₀ = ¼·log 3`; `0` is the lower end of `λ₀`, of `g` and of the
cosine average; `1` is the `+ 1` of the aperture and `2` the doubling in `2k + 1`. -/
theorem lam0_pow_lt_of_tension (k : ℕ) (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (g : Set.Icc (0 : ℝ) 1 → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (lam0 : ℝ) (h0 : 0 ≤ lam0) (hgs : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) < lam0 → g t = 0)
    (R : Moment.Read (2 * k + 1))
    (hρ : ∀ d, R.ρ d = momW w g (Moment.circLag d))
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    lam0 ^ (k + 1) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) := by
  have hcap := R.substrate_lt_of_tension_lt_floor hpos htens
  have hlb := substrate_ge_of_weight k w g hg hg0 lam0 h0 hgs
  have hden : ∑ d, R.ρ d
      = ∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d) := by
    rw [Finset.sum_congr rfl (fun d _ => hρ d)]
    exact sum_circLag_eq_range (N := 2 * k + 1) (fun c => momW w g c)
  have hnum : ∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2
      = ∑ d ∈ Finset.range (2 * (k + 1)),
          momW w g (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    rw [Finset.sum_congr rfl (fun d _ => by rw [hρ d])]
    exact sum_circLag_eq_range (N := 2 * k + 1) (fun c => momW w g c * ((c : ℝ)) ^ 2)
  have hsub_eq : (∑ d, R.p d * ((Moment.circLag d : ℝ)) ^ 2)
      = (∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  have hNcast : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring
  have hdenpos : (0 : ℝ) < ∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d) := by
    rw [← hden]; exact R.hpos
  have hkey : lam0 ^ (k + 1)
      ≤ 12 * ((∑ d, R.p d * ((Moment.circLag d : ℝ)) ^ 2) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) := by
    rw [hsub_eq, hden, hnum, hNcast, div_div, ← mul_div_assoc,
      le_div_iff₀ (by positivity)]
    have hassoc : lam0 ^ (k + 1)
        * ((∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d))
            * ((2 * (k + 1) : ℕ) : ℝ) ^ 2)
      = lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), momW w g (clag (2 * (k + 1)) d)) := by ring
    linarith [hlb, hassoc.le, hassoc.ge]
  linarith [hcap, hkey]

#print axioms lam0_pow_lt_of_tension

end MassGap.SpectralRead
