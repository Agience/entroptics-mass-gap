import Mathlib
import MassGap.SpectralGap
import MassGap.ReadConverse
import MassGap.ReadReduce
import MassGap.PeriodicReduce
import MassGap.PeriodicContent
import MassGap.ZeroMode

/-!
# MassGap.FloorRead — the margin inequality is a spectral bound, and the floor sets only where

`ReadReduce.ReadsClearWith a Ω k γ` — every vector `v ⊥ Ω` has
`0 ≤ ∑_d (cos θ_d − γ)·re ⟪v, a^{circLag d} v⟫` — is the form the Clay chain consumes, through
`PeriodicReduce.TorusReadsClearWith` (`periodic_localReads_of_torusReads`,
`ReadReduce.readsClearWith_of_local`). This module brackets it by two contractions of the vacuum
complement that meet at the root of `modeCosAvg k r = γ`:

* `readsClearWith_of_contraction`: `‖a u‖ ≤ r ‖u‖` on `Ω⊥` and `γ ≤ modeCosAvg k r` give
  `ReadsClearWith a Ω k γ`;
* `contraction_of_readsClearWith`: `ReadsClearWith a Ω k γ` gives `‖aᵐ u‖ ≤ sᵐ ‖u‖` on `Ω⊥` at every
  `s ≥ 0` with `modeCosAvg k s < γ`.

`modeCosAvg k` is continuous and antitone on `[0, ∞)` (`ReadConverse.modeCosAvg_antitone`), `1` at
`0` and `0` at `1` (`modeCosAvg_one`), so for `0 < γ ≤ 1` the set `{r ≥ 0 | γ ≤ modeCosAvg k r}` is
a closed interval `[0, r_γ(k)]` with `r_γ(k) < 1`, and `{s ≥ 0 | modeCosAvg k s < γ}` is
`(r_γ(k), ∞)`. A contraction at every `s > r_γ(k)` is one at `r_γ(k)`, so for `0 < γ ≤ 1` the
margin inequality at `(k, γ)` holds exactly when `‖a u‖ ≤ r_γ(k)·‖u‖` on `Ω⊥`, endpoint included.
This is argued from the two theorems; `r_γ(k)` is not defined and the equivalence is not stated
here.

`contraction_of_readsClear` is the converse of `ReadConverse.readsClear_of_contraction` and sharpens
`SpectralGap.gap_of_reads`: it contracts at every `s ≥ 0` with `modeCosAvg k s ≤ 3^{−1/4}`, at or
above the root (`0.1365` against `0.6002` at `k = 1`; computed, not proved here).

The core is `cosAvg_le_of_support`: a read whose correlation is `∫ G t^c dw` with `G ≥ 0` vanishing
below `s` has cosine average at most `modeCosAvg k s` — `ReadConverse.modeCos_mul_modeMass_le`
integrated over `[s, 1]`, the mirror of the step `ReadConverse.readsClear_of_contraction` takes over
`[0, r]`. `measure_gt_eq_zero_of_reads_gt` feeds it the ramp vector of
`SpectralGap.measure_gt_eq_zero`.

What the floor contributes. `exists_contraction_lt_one_of_readsClearWith`: at ANY `γ > 0` the
margin inequality already gives a contraction below `1`, because the massless single mode reads a
cosine average of exactly `0` (`modeCosAvg_one`). The value `γ = 3^{−1/4} = e^{−κ₀}` fixes which
root, not whether there is one.

At the periodic state (`periodic_contraction_of_torusReads`, `periodic_torusReads_of_contraction`)
the bracket reads: `TorusReadsClearWith τ p hN β k γ` gives the contraction at every `s` above the
root, and a contraction at a rate `r` with `γ ≤ modeCosAvg k r` gives `TorusReadsClearWith`.
`local_of_readsClearWith` is the step from the GNS space back to the local observables that the
second direction needs.

`periodic_clayGapAt_of_torusReads_any_margin` and
`wilson_gaugeInv_mass_gap_every_coupling_any_margin` take the Clay chain's one input,
`PeriodicReduce.TorusReadsClearWith τ p hN β k γ`, at any `γ > 0` instead of `γ > 3^{−1/4}`, and
conclude `PeriodicContent.PeriodicClayGapAt`. At `γ > 0` that input is the gap itself:
`periodic_torusReads_of_clayGapAt` gives it back, at `k = 0` and `γ = (1 − ρ)/(1 + ρ)`, from the
contraction below `1` that `PeriodicContent.PeriodicClayGapAt τ p hN β ρ` carries, and at `γ = 0` it
holds at every `β ≥ 0` (`periodic_torusReads_zero_margin`).
-/

namespace MassGap.FloorRead

open MeasureTheory MassGap.SpectralRep MassGap.SpectralRead MassGap.SpectralGap
  MassGap.ReadConverse

/-! ## 1. The single mode at the two ends -/

section Mode

/-- **The massless single mode has zero cosine sum.** `modeCos k 1 = ∑_d cos(2π·circLag d/n) = 0`,
`n = (2k + 1) + 1`: the cosines of the lag angles of any read at aperture `2k + 1`
(`Moment.Read.cos_theta_circ`) sum to zero over the full circle (`ZeroMode.sum_cos_theta_eq_zero`).

DERIVED: `1` is the mode `t = 1` (no decay); `0` is the concluded sum; `2` and the first `1` of
`2 * k + 1` spell the aperture. -/
theorem modeCos_one (k : ℕ) : modeCos k 1 = 0 := by
  have R : Moment.Read (2 * k + 1) := default
  have h : ∀ d : Fin (2 * k + 1 + 1), (1 : ℝ) ^ Moment.circLag d
      * Real.cos (2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1))
      = Real.cos (R.θ d) := by
    intro d
    rw [one_pow, one_mul]
    exact (R.cos_theta_circ d).symm
  unfold modeCos
  rw [Finset.sum_congr rfl (fun d _ => h d)]
  exact MassGap.ZeroMode.sum_cos_theta_eq_zero R (by omega)

#print axioms modeCos_one

/-- **The massless single mode reads a cosine average of zero**: `modeCosAvg k 1 = 0`.

DERIVED: `1` is the mode `t = 1`; `0` is the concluded average. -/
theorem modeCosAvg_one (k : ℕ) : modeCosAvg k 1 = 0 := by
  unfold modeCosAvg
  rw [modeCos_one, zero_div]

#print axioms modeCosAvg_one

/-- **Below any positive threshold, strictly before the massless mode.** For `0 < γ` there is
`s ∈ [0, 1)` with `modeCosAvg k s < γ`: `modeCosAvg k` is continuous at `1` (`modeMass k 1 > 0`)
with value `0` there (`modeCosAvg_one`).

DERIVED: `0` is the sign of `γ` and the lower end of `s`; `1` is the massless mode; `2` in
`1 − ε/2` halves the radius of the neighbourhood so the point lies inside it. -/
theorem exists_lt_one_modeCosAvg_lt (k : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ modeCosAvg k s < γ := by
  have hc : ContinuousAt (modeCos k / modeMass k) 1 :=
    (continuous_modeCos k).continuousAt.div (continuous_modeMass k).continuousAt
      (ne_of_gt (modeMass_pos k zero_le_one))
  have h1 : (modeCos k / modeMass k) 1 < γ := by
    show modeCos k 1 / modeMass k 1 < γ
    rw [modeCos_one, zero_div]
    exact hγ
  have hev : ∀ᶠ t in nhds (1 : ℝ), (modeCos k / modeMass k) t < γ :=
    hc.eventually_lt continuousAt_const h1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hle1 : max 0 (1 - ε / 2) ≤ 1 := max_le (by norm_num) (by linarith)
  have hge : 1 - ε / 2 ≤ max 0 (1 - ε / 2) := le_max_right _ _
  have hneg : max 0 (1 - ε / 2) - 1 ≤ 0 := by linarith
  have hd : dist (max 0 (1 - ε / 2)) 1 < ε := by
    rw [Real.dist_eq, abs_of_nonpos hneg]
    linarith
  refine ⟨max 0 (1 - ε / 2), le_max_left _ _, max_lt (by norm_num) (by linarith), ?_⟩
  exact hball hd

#print axioms exists_lt_one_modeCosAvg_lt

end Mode

/-! ## 2. A read supported above `s` has cosine average at most `modeCosAvg k s` -/

section Support

/-- **Chebyshev over `[s, 1]`.** For a finite measure `w` on `[0, 1]`, a continuous weight `G ≥ 0`
vanishing below `s ≥ 0`, and a read `R` at aperture `2k + 1` whose correlation at lag `d` is
`momW w G (circLag d) = ∫ G t^{circLag d} dw`: the read's cosine average is at most
`modeCosAvg k s`. Pointwise, for `t ≥ s`,
`modeCos k t · modeMass k s ≤ modeCos k s · modeMass k t` (`ReadConverse.modeCos_mul_modeMass_le`);
below `s` the weight is zero; integrating against `G dw` and dividing by the two positive masses
gives the bound.

DERIVED: `0` is the sign of `G`, of `s` and the lower end of the interval; `1` its upper end; `2`
and `1` spell the aperture `2k + 1`. -/
theorem cosAvg_le_of_support (k : ℕ) (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (G : Set.Icc (0 : ℝ) 1 → ℝ) (hGc : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (s : ℝ) (hs0 : 0 ≤ s) (hGs : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) < s → G t = 0)
    (R : Moment.Read (2 * k + 1)) (hρ : ∀ d, R.ρ d = momW w G (Moment.circLag d)) :
    ∑ d, R.p d * Real.cos (R.θ d) ≤ modeCosAvg k s := by
  have hD : ∑ d, R.ρ d = ∫ t, G t * modeMass k (t : ℝ) ∂w := by
    unfold modeMass
    simp only [Finset.mul_sum]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun d _ => hρ d)
    · intro d _
      exact integrable_of_continuous w (hGc.mul (continuous_subtype_val.pow _))
  have hN : ∑ d, R.ρ d * Real.cos (R.θ d) = ∫ t, G t * modeCos k (t : ℝ) ∂w := by
    unfold modeCos
    simp only [Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [hρ d, R.cos_theta_circ d]
      show (∫ t, G t * (t : ℝ) ^ Moment.circLag d ∂w) * _ = _
      rw [← integral_mul_const]
      congr 1
      funext t
      simp only [mul_assoc]
    · intro d _
      exact integrable_of_continuous w
        (hGc.mul ((continuous_subtype_val.pow _).mul continuous_const))
  have hS : 0 < ∑ d, R.ρ d := R.hpos
  have hMs : 0 < modeMass k s := modeMass_pos k hs0
  have hcmp : (∫ t, G t * modeCos k (t : ℝ) ∂w) * modeMass k s
      ≤ modeCos k s * ∫ t, G t * modeMass k (t : ℝ) ∂w := by
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_mono ?_ ?_ (fun t => ?_)
    · exact integrable_of_continuous w
        ((hGc.mul ((continuous_modeCos k).comp continuous_subtype_val)).mul continuous_const)
    · exact integrable_of_continuous w
        (continuous_const.mul (hGc.mul ((continuous_modeMass k).comp continuous_subtype_val)))
    · show G t * modeCos k (t : ℝ) * modeMass k s ≤ modeCos k s * (G t * modeMass k (t : ℝ))
      by_cases hts : s ≤ (t : ℝ)
      · have h := modeCos_mul_modeMass_le k hs0 hts
        calc G t * modeCos k (t : ℝ) * modeMass k s
            = G t * (modeCos k (t : ℝ) * modeMass k s) := by ring
          _ ≤ G t * (modeCos k s * modeMass k (t : ℝ)) := mul_le_mul_of_nonneg_left h (hG0 t)
          _ = modeCos k s * (G t * modeMass k (t : ℝ)) := by ring
      · have hz : G t = 0 := hGs t (not_le.mp hts)
        rw [hz]
        simp
  rw [← hD, ← hN] at hcmp
  have havg : ∑ d, R.p d * Real.cos (R.θ d)
      = (∑ d, R.ρ d * Real.cos (R.θ d)) / ∑ d, R.ρ d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold Moment.Read.p
    ring
  rw [havg, modeCosAvg, div_le_div_iff₀ hS hMs]
  exact hcmp

#print axioms cosAvg_le_of_support

end Support

/-! ## 3. Reads above `modeCosAvg k s` put no spectral weight above `s` -/

section Sharp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **No spectral weight above `s`.** Let `a` be self-adjoint with spectrum in `[0, 1]`, `a Ω = Ω`,
`s ≥ 0`, and suppose every read at aperture `2k + 1` of every vector orthogonal to `Ω` has cosine
average strictly above `modeCosAvg k s`. Then for `u ⊥ Ω` with spectral measure `w`,
`w {t | s < t} = 0`.

Were the mass above `s` positive, a slice `[s + 2δ, 1]` would carry some; the ramp `φ` rising from
`0` at `s + δ` to `1` at `s + 2δ` makes `v = φ(a) u` a vector orthogonal to `Ω`
(`SpectralRep.cfc_apply_of_fixed`) whose correlation is `∫ φ² t^c dw` (`SpectralRep.inner_cfc_cfc`)
with `φ²` vanishing below `s`; `cosAvg_le_of_support` puts its cosine average at or below
`modeCosAvg k s`, against the hypothesis.

DERIVED: `0` and `1` are the interval's ends; `0` is the orthogonality, the sign of `s` and the
concluded null mass; `1 / (n + 1)` and its half `δ` are the slice widths of the countable union, the
`2` halving; `2` and `1` spell the aperture `2k + 1`. -/
theorem measure_gt_eq_zero_of_reads_gt (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s)
    (hread : ∀ v : E, inner ℂ Ω v = 0 → ∀ R : Moment.Read (2 * k + 1),
      (∀ d, R.ρ d = RCLike.re (inner ℂ v ((a ^ Moment.circLag d) v))) →
        modeCosAvg k s < ∑ d, R.p d * Real.cos (R.θ d))
    (u : E) (hu : inner ℂ Ω u = 0)
    (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (hw : ∀ h : ℝ → ℝ, Continuous h → RCLike.re (inner ℂ u (cfc h a u)) = ∫ t, h (t : ℝ) ∂w) :
    w {t | s < (t : ℝ)} = 0 := by
  by_contra hne
  have hU : {t : Set.Icc (0 : ℝ) 1 | s < (t : ℝ)}
      = ⋃ n : ℕ, {t : Set.Icc (0 : ℝ) 1 | s + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [hU, measure_iUnion_null_iff] at hne
  push_neg at hne
  obtain ⟨n, hn⟩ := hne
  set δ : ℝ := 1 / ((n : ℝ) + 1) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hslice : s + 1 / ((n : ℝ) + 1) = (s + δ) + δ := by rw [hδ_def]; ring
  set G : Set.Icc (0 : ℝ) 1 → ℝ := fun t => ramp (s + δ) δ t * ramp (s + δ) δ t with hG_def
  have hGc : Continuous G :=
    ((continuous_ramp _ _).comp continuous_subtype_val).mul
      ((continuous_ramp _ _).comp continuous_subtype_val)
  have hG0 : ∀ t, 0 ≤ G t := fun t => mul_self_nonneg _
  have hGs : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) < s → G t = 0 := by
    intro t ht
    have ht' : (t : ℝ) < s + δ := by linarith
    simp only [hG_def, ramp_eq_zero hδ ht', mul_zero]
  -- the vector `v = φ(a) u`: its correlation is the weighted moment sequence
  have hmom : ∀ c : ℕ, RCLike.re (inner ℂ (cfc (ramp (s + δ) δ) a u)
      ((a ^ c) (cfc (ramp (s + δ) δ) a u))) = momW w G c := by
    intro c
    have h1' := inner_cfc_cfc a (ramp (s + δ) δ) (fun x : ℝ => x ^ c)
      (continuous_ramp _ _) (continuous_pow c) u
    have h2' := hw (fun t => ramp (s + δ) δ t * t ^ c * ramp (s + δ) δ t)
      (((continuous_ramp _ _).mul (continuous_pow c)).mul (continuous_ramp _ _))
    beta_reduce at h1' h2'
    rw [cfc_pow_id (R := ℝ) a c ha] at h1'
    rw [h1', h2']
    show ∫ t, ramp (s + δ) δ (t : ℝ) * (t : ℝ) ^ c * ramp (s + δ) δ (t : ℝ) ∂w
      = ∫ t, G t * (t : ℝ) ^ c ∂w
    congr 1
    funext t
    simp only [hG_def]
    ring
  have hnn : ∀ c : ℕ, 0 ≤ momW w G c :=
    fun c => integral_nonneg (fun t => mul_nonneg (hG0 t) (pow_nonneg t.2.1 _))
  have hS : MeasurableSet {t : Set.Icc (0 : ℝ) 1 | s + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)} :=
    measurableSet_le measurable_const measurable_subtype_coe
  have hmass : 0 < momW w G 0 := by
    have hpos : 0 < w.real {t : Set.Icc (0 : ℝ) 1 | s + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)} :=
      ENNReal.toReal_pos hn (measure_ne_top w _)
    refine lt_of_lt_of_le hpos ?_
    rw [← integral_indicator_one hS]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS)
      (integrable_of_continuous w (hGc.mul (continuous_subtype_val.pow 0))) (fun t => ?_)
    by_cases ht : t ∈ {t : Set.Icc (0 : ℝ) 1 | s + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)}
    · rw [Set.indicator_of_mem ht]
      have ht' : s + δ + δ ≤ (t : ℝ) := by rw [← hslice]; exact ht
      simp only [hG_def, ramp_eq_one hδ ht', pow_zero, mul_one, Pi.one_apply, le_refl]
    · rw [Set.indicator_of_notMem ht]
      exact mul_nonneg (hG0 t) (pow_nonneg t.2.1 _)
  have hlag0 : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by simp [Moment.circLag]
  let R : Moment.Read (2 * k + 1) :=
    { ρ := fun d => momW w G (Moment.circLag d)
      hρ := fun d => hnn _
      hpos := by
        refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun d _ => hnn (Moment.circLag d))
          (Finset.mem_univ (0 : Fin (2 * k + 1 + 1))))
        rw [hlag0]
        exact hmass }
  -- `v` is orthogonal to `Ω`
  have hv : inner ℂ Ω (cfc (ramp (s + δ) δ) a u) = 0 := by
    have hsa : IsSelfAdjoint (cfc (ramp (s + δ) δ) a) := cfc_predicate _ a
    have hsym : inner ℂ (cfc (ramp (s + δ) δ) a Ω) u
        = inner ℂ Ω (cfc (ramp (s + δ) δ) a u) := hsa.isSymmetric Ω u
    rw [← hsym, cfc_apply_of_fixed a ha hspec Ω hΩ _ (continuous_ramp _ _),
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hu, mul_zero]
  have hgt := hread _ hv R (fun d => (hmom _).symm)
  have hle := cosAvg_le_of_support k w G hGc hG0 s hs0 hGs R (fun d => rfl)
  linarith

#print axioms measure_gt_eq_zero_of_reads_gt

/-- **The contraction at `s`.** Under the hypothesis of `measure_gt_eq_zero_of_reads_gt`: every
`u ⊥ Ω` has `‖aᵐ u‖ ≤ sᵐ ‖u‖`. With no spectral weight above `s`,
`‖aᵐ u‖² = ∫ t^{2m} dw ≤ s^{2m} ‖u‖²`.

DERIVED: `0` and `1` are the interval's ends; `0` is the orthogonality and the sign of `s`; `2` is
the square in the norm; `2` and `1` spell the aperture `2k + 1`. -/
theorem norm_pow_le_of_reads_gt (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s)
    (hread : ∀ v : E, inner ℂ Ω v = 0 → ∀ R : Moment.Read (2 * k + 1),
      (∀ d, R.ρ d = RCLike.re (inner ℂ v ((a ^ Moment.circLag d) v))) →
        modeCosAvg k s < ∑ d, R.p d * Real.cos (R.θ d))
    (u : E) (hu : inner ℂ Ω u = 0) (m : ℕ) :
    ‖(a ^ m) u‖ ≤ s ^ m * ‖u‖ := by
  obtain ⟨w, hw, hint⟩ := exists_spectral_measure a ha hspec u
  have hnull := measure_gt_eq_zero_of_reads_gt a ha hspec Ω hΩ k s hs0 hread u hu w hint
  have hae : ∀ᵐ t : Set.Icc (0 : ℝ) 1 ∂w, (t : ℝ) ≤ s := by
    rw [ae_iff]
    simpa only [not_le] using hnull
  have hA : ‖(a ^ m) u‖ ^ 2 = ∫ t, (t : ℝ) ^ m * (t : ℝ) ^ m ∂w := by
    have h1' := norm_sq_cfc a ha (fun x : ℝ => x ^ m) (continuous_pow m) u
    have h2' := hint (fun x : ℝ => x ^ m * x ^ m) ((continuous_pow m).mul (continuous_pow m))
    beta_reduce at h1' h2'
    rw [cfc_pow_id (R := ℝ) a m ha] at h1'
    rw [h1', h2']
  have hu2 : ‖u‖ ^ 2 = ∫ _t, (1 : ℝ) ∂w := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
    have h := hint (fun _ => 1) continuous_const
    rw [cfc_const_one ℝ a ha, ContinuousLinearMap.one_apply] at h
    exact h
  have hsq : ‖(a ^ m) u‖ ^ 2 ≤ (s ^ m * ‖u‖) ^ 2 := by
    rw [hA, mul_pow, hu2, ← integral_const_mul]
    refine integral_mono_ae
      (integrable_of_continuous w
        ((continuous_subtype_val.pow m).mul (continuous_subtype_val.pow m)))
      (integrable_const _) ?_
    filter_upwards [hae] with t ht
    have hp := pow_le_pow_left₀ t.2.1 ht m
    have hp0 := pow_nonneg t.2.1 m
    show (t : ℝ) ^ m * (t : ℝ) ^ m ≤ (s ^ m) ^ 2 * 1
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

#print axioms norm_pow_le_of_reads_gt

/-- **`SpectralGap.ReadsClear` contracts the vacuum complement at every rate at or above the
root.** Under `ReadsClear a Ω k`, every `s ≥ 0` with `modeCosAvg k s ≤ 3^{−1/4}` contracts the
vacuum complement: `‖aᵐ u‖ ≤ sᵐ ‖u‖`. A read clearing the floor has cosine average above
`3^{−1/4}` (`Moment.Read.cosAvg_gt_of_tension_lt_floor`), hence above `modeCosAvg k s`. The converse
of `ReadConverse.readsClear_of_contraction`; it sharpens `SpectralGap.gap_of_reads`, replacing
`cap^{1/(k+1)}` by the root (`0.1365` against `0.6002` at `k = 1`; computed, not proved here).

DERIVED: `3`, `1` and `4` spell the floor's `3^{−1/4} = e^{−κ₀}`; `0` is the sign of `s` and the
orthogonality; `0` and `1` are the interval's ends. -/
theorem contraction_of_readsClear (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ)
    (hread : ReadsClear a Ω k) (s : ℝ) (hs0 : 0 ≤ s)
    (hsγ : modeCosAvg k s ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (u : E) (hu : inner ℂ Ω u = 0) (m : ℕ) :
    ‖(a ^ m) u‖ ≤ s ^ m * ‖u‖ :=
  norm_pow_le_of_reads_gt a ha hspec Ω hΩ k s hs0
    (fun v hv R hR => by
      obtain ⟨hpos, htens⟩ := hread v hv R hR
      exact lt_of_le_of_lt hsγ (R.cosAvg_gt_of_tension_lt_floor hpos htens)) u hu m

#print axioms contraction_of_readsClear

/-- **The margin inequality contracts the vacuum complement at every rate reading below `γ`.**
Under `ReadReduce.ReadsClearWith a Ω k γ`, every `s ≥ 0` with `modeCosAvg k s < γ` contracts the
vacuum complement: `‖aᵐ u‖ ≤ sᵐ ‖u‖`. A read of `v ⊥ Ω` has `0 ≤ ∑ (cos θ_d − γ) ρ_d`
(`ReadReduce.marginSum_eq_read`), i.e. cosine average at least `γ` (`ReadReduce.margin_nonneg_iff`),
hence strictly above `modeCosAvg k s`. The converse of `readsClearWith_of_contraction`.

DERIVED: `0` is the sign of `s` and the orthogonality; `0` and `1` are the interval's ends. -/
theorem contraction_of_readsClearWith (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (γ : ℝ)
    (h : ReadReduce.ReadsClearWith a Ω k γ) (s : ℝ) (hs0 : 0 ≤ s)
    (hsγ : modeCosAvg k s < γ) (u : E) (hu : inner ℂ Ω u = 0) (m : ℕ) :
    ‖(a ^ m) u‖ ≤ s ^ m * ‖u‖ :=
  norm_pow_le_of_reads_gt a ha hspec Ω hΩ k s hs0
    (fun v hv R hR => by
      have hlin : 0 ≤ ∑ d, (Real.cos (R.θ d) - γ) * R.ρ d :=
        le_of_le_of_eq (h v hv)
          (ReadReduce.marginSum_eq_read γ R (fun c => RCLike.re (inner ℂ v ((a ^ c) v))) hR)
      exact lt_of_lt_of_le hsγ ((ReadReduce.margin_nonneg_iff R γ).mp hlin)) u hu m

#print axioms contraction_of_readsClearWith

/-- **The margin inequality from a contraction.** For `a` self-adjoint with spectrum in `[0, 1]`,
`a Ω = Ω`, `0 ≤ r`, `‖a u‖ ≤ r ‖u‖` on `Ω⊥`, and `γ ≤ modeCosAvg k r`:
`ReadReduce.ReadsClearWith a Ω k γ`. For `v ⊥ Ω` the margin sum is
`∫ (modeCos k t − γ·modeMass k t) dw_v`; `ReadConverse.ae_le_of_contraction` puts `w_v` on `[0, r]`,
where `modeCosAvg k t ≥ modeCosAvg k r ≥ γ` (`ReadConverse.modeCosAvg_antitone`), so the integrand
is nonnegative.

DERIVED: `0` and `1` are the interval's ends; `0` is the sign of `r`, the orthogonality and the sign
of the margin sum; `2` and `1` spell the aperture `2k + 1`. -/
theorem readsClearWith_of_contraction (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (γ : ℝ) (r : ℝ)
    (hr0 : 0 ≤ r) (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖)
    (hmode : γ ≤ modeCosAvg k r) :
    ReadReduce.ReadsClearWith a Ω k γ := by
  intro v hv
  obtain ⟨w, hwfin, hw⟩ := exists_spectral_measure a ha hspec v
  have hsupp := ae_le_of_contraction a ha hspec Ω hΩ r hr0 hcon v hv w hw
  have hmom : ∀ c : ℕ, RCLike.re (inner ℂ v ((a ^ c) v)) = ∫ t, (t : ℝ) ^ c ∂w := by
    intro c
    have h : RCLike.re (inner ℂ v (cfc (fun x : ℝ => x ^ c) a v)) = ∫ t, (t : ℝ) ^ c ∂w :=
      hw (fun x : ℝ => x ^ c) (continuous_pow c)
    rw [cfc_pow_id (R := ℝ) a c ha] at h
    exact h
  have hpt : ∀ t : ℝ, 0 ≤ t → t ≤ r →
      0 ≤ ∑ d : Fin (2 * k + 1 + 1),
        (Real.cos (ReadReduce.readAngle k d) - γ) * t ^ Moment.circLag d := by
    intro t ht0 htr
    have hid : ∑ d : Fin (2 * k + 1 + 1),
        (Real.cos (ReadReduce.readAngle k d) - γ) * t ^ Moment.circLag d
        = modeCos k t - γ * modeMass k t := by
      unfold modeCos modeMass
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      have hc : Real.cos (ReadReduce.readAngle k d)
          = Real.cos (2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1)) :=
        (default : Moment.Read (2 * k + 1)).cos_theta_circ d
      rw [hc]
      ring
    rw [hid]
    have hMt : 0 < modeMass k t := modeMass_pos k ht0
    have hav : modeCosAvg k r ≤ modeCosAvg k t :=
      modeCosAvg_antitone k (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr hr0) htr
    have hγt : γ ≤ modeCosAvg k t := le_trans hmode hav
    have hγM : γ * modeMass k t ≤ modeCos k t := by
      unfold modeCosAvg at hγt
      rwa [le_div_iff₀ hMt] at hγt
    linarith
  have hsum : ReadReduce.marginSum k γ (fun c => RCLike.re (inner ℂ v ((a ^ c) v)))
      = ∫ t, ∑ d : Fin (2 * k + 1 + 1),
          (Real.cos (ReadReduce.readAngle k d) - γ) * (t : ℝ) ^ Moment.circLag d ∂w := by
    rw [integral_finsetSum]
    · show ∑ d : Fin (2 * k + 1 + 1), (Real.cos (ReadReduce.readAngle k d) - γ)
          * RCLike.re (inner ℂ v ((a ^ Moment.circLag d) v)) = _
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [hmom, integral_const_mul]
    · intro d _
      exact integrable_of_continuous w (continuous_const.mul (continuous_subtype_val.pow _))
  rw [hsum]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hsupp] with t ht
  exact hpt t t.2.1 ht

#print axioms readsClearWith_of_contraction

/-- **Any positive threshold already forces a contraction below one.** Under
`ReadReduce.ReadsClearWith a Ω k γ` with `0 < γ` — at any positive margin, not only at
`γ > 3^{−1/4}` — there is `s ∈ [0, 1)` with `‖aᵐ u‖ ≤ sᵐ ‖u‖` on the vacuum complement
(`exists_lt_one_modeCosAvg_lt`, `contraction_of_readsClearWith`). The massless mode reads `0`
(`modeCosAvg_one`); the value of `γ` sets how far below `1` the contraction sits, not whether it
exists, and the floor `3^{−1/4}` is one such value.

DERIVED: `0` is the sign of `γ`, the lower end of `s` and the orthogonality; `1` is the massless
mode; `0` and `1` are the interval's ends. -/
theorem exists_contraction_lt_one_of_readsClearWith (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (h : ReadReduce.ReadsClearWith a Ω k γ) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧
      ∀ u : E, inner ℂ Ω u = 0 → ∀ m : ℕ, ‖(a ^ m) u‖ ≤ s ^ m * ‖u‖ := by
  obtain ⟨s, hs0, hs1, hsγ⟩ := exists_lt_one_modeCosAvg_lt k hγ
  exact ⟨s, hs0, hs1, fun u hu m =>
    contraction_of_readsClearWith a ha hspec Ω hΩ k γ h s hs0 hsγ u hu m⟩

#print axioms exists_contraction_lt_one_of_readsClearWith

end Sharp

/-! ## 4. At the periodic state: the torus input is the spectral bound -/

section Periodic

open MassGap.Transfer MassGap.GNSHilbert MassGap.PeriodicState

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The class of the pair `(x, 0)` is orthogonal to the vacuum whenever `D.form x D.vac = 0`: the
real part of `cform (vac, 0) (x, 0)` is `D.form vac x + D.form 0 0`, the imaginary part
`D.form vac 0 − D.form 0 x`.

DERIVED: `0` is the imaginary component of both pairs and the orthogonality. -/
theorem inner_Omega_ofPair (D : TransferData A) (x : A) (hx : D.form x D.vac = 0) :
    inner ℂ (Omega D.toReflForm D.vac)
      ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm) = 0 := by
  show inner ℂ ((Pre.ofPair D.toReflForm D.vac (0 : A) : Pre D.toReflForm) : H D.toReflForm)
      ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm) = 0
  rw [MassGap.GNSHilbert.inner_coe]
  apply Complex.ext
  · simp only [OSPositivity.cform_re, Pre.ofPair_fst, Pre.ofPair_snd,
      Transfer.PreForm.form_zero_left, add_zero, Complex.zero_re]
    exact (D.form_symm D.vac x).trans hx
  · simp only [OSPositivity.cform_im, Pre.ofPair_fst, Pre.ofPair_snd,
      Transfer.PreForm.form_zero_left, Transfer.PreForm.form_zero_right, sub_zero,
      Complex.zero_im]

#print axioms inner_Omega_ofPair

/-- The profile of the class of `(x, 0)` is the real profile of `x`:
`re ⟪(x,0), opTᶜ (x,0)⟫ = D.form x (Tᶜ x)` (`ReadReduce.re_inner_opT_pow_coe`, the second component
contributing `D.form 0 (Tᶜ 0) = 0`).

DERIVED: `0` is the imaginary component of the pair. -/
theorem re_inner_opT_pow_ofPair (D : TransferData A) (x : A) (c : ℕ) :
    RCLike.re (inner ℂ ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm)
      (((opT D) ^ c) ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm)))
      = D.form x ((D.T ^ c) x) := by
  rw [ReadReduce.re_inner_opT_pow_coe D (Pre.ofPair D.toReflForm x (0 : A)) c]
  simp only [Pre.ofPair_fst, Pre.ofPair_snd, map_zero, Transfer.PreForm.form_zero_left, add_zero]

#print axioms re_inner_opT_pow_ofPair

/-- **The local margin inequality from the GNS one.** `ReadReduce.ReadsClearWith (opT D) Ω k γ`
gives, at every `x : A` with `D.form x D.vac = 0`,
`0 ≤ marginSum k γ (c ↦ D.form x (Tᶜ x))`: apply it at the class of `(x, 0)`
(`inner_Omega_ofPair`, `re_inner_opT_pow_ofPair`). The converse of
`ReadReduce.readsClearWith_of_local`.

DERIVED: `0` is the orthogonality and the sign of the sum. -/
theorem local_of_readsClearWith (D : TransferData A) (k : ℕ) (γ : ℝ)
    (h : ReadReduce.ReadsClearWith (opT D) (Omega D.toReflForm D.vac) k γ)
    (x : A) (hx : D.form x D.vac = 0) :
    0 ≤ ReadReduce.marginSum k γ (fun c => D.form x ((D.T ^ c) x)) :=
  le_of_le_of_eq (h _ (inner_Omega_ofPair D x hx))
    (ReadReduce.marginSum_congr k γ (fun c => re_inner_opT_pow_ofPair D x c))

#print axioms local_of_readsClearWith

variable {N : ℕ}

/-- **The torus input gives the contraction at every rate above the root.** At `0 ≤ β`, under
`PeriodicReduce.TorusReadsClearWith τ p hN β k γ`, every `s ≥ 0` with `modeCosAvg k s < γ`
contracts the vacuum complement of the gauge-invariant GNS space at the periodic state:
`‖opTᵐ u‖ ≤ sᵐ ‖u‖`. `PeriodicReduce.periodic_localReads_of_torusReads`, then
`ReadReduce.readsClearWith_of_local`, then `contraction_of_readsClearWith`.

At `γ > 3^{−1/4}` the edge `r_γ(k)` (the largest `r ≥ 0` with `γ ≤ modeCosAvg k r`) lies at or
below the root `r*(k)` of `modeCosAvg k r = 3^{−1/4}`: `0.1365, 0.2888, 0.9788` at `k = 1, 3, 255`
(computed, not proved here; at `k = 1`, `modeCosAvg 1 r = (1 − r)/(1 + r)`, so
`r*(1) = (1 − 3^{−1/4})/(1 + 3^{−1/4})`). Every `s > r_γ(k)` has `modeCosAvg k s < γ`, so this
contracts at every rate above `r_γ(k)`, where `PeriodicReduce.periodic_gap_of_torusReads` gives
`cap^{1/(k+1)}` (`0.6002, 0.7747, 0.9960`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β` and of `s`,
and the orthogonality; `0` and `1` bound the spectrum. -/
theorem periodic_contraction_of_torusReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) (k : ℕ) (γ : ℝ)
    (htorus : MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ)
    (s : ℝ) (hs0 : 0 ≤ s) (hsγ : modeCosAvg k s < γ) :
    ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
      inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
        (periodicGaugeInvData τ p hN β).vac) u = 0 →
      ∀ m : ℕ, ‖((opT (periodicGaugeInvData τ p hN β)) ^ m) u‖ ≤ s ^ m * ‖u‖ :=
  fun u hu m =>
    contraction_of_readsClearWith (opT (periodicGaugeInvData τ p hN β))
      (isSelfAdjoint_opT (periodicGaugeInvData τ p hN β))
      (fun x hx => ⟨spectrum_opT_nonneg (periodicGaugeInvData τ p hN β)
          (periodic_positiveTransfer τ p hN hβ) hx,
        (spectrum_opT_subset_unit_interval (periodicGaugeInvData τ p hN β) hx).2⟩)
      _ (opT_Omega (periodicGaugeInvData τ p hN β)) k γ
      (ReadReduce.readsClearWith_of_local (periodicGaugeInvData τ p hN β) k γ
        (MassGap.PeriodicReduce.periodic_localReads_of_torusReads τ p hN β k γ htorus))
      s hs0 hsγ u hu m

#print axioms periodic_contraction_of_torusReads

/-- **A contraction at a rate reading at least `γ` gives the torus input.** At `0 ≤ β`: if the
vacuum complement at the periodic state is contracted, `‖opT u‖ ≤ r ‖u‖`, at a rate with
`γ ≤ modeCosAvg k r`, then `PeriodicReduce.TorusReadsClearWith τ p hN β k γ`.
`readsClearWith_of_contraction`, `local_of_readsClearWith`, then
`PeriodicReduce.periodic_torusReads_of_localReads`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β` and of `r`,
and the orthogonality. -/
theorem periodic_torusReads_of_contraction (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) (k : ℕ) (γ : ℝ) (r : ℝ) (hr0 : 0 ≤ r)
    (hcon : ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
      inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
        (periodicGaugeInvData τ p hN β).vac) u = 0 →
      ‖(opT (periodicGaugeInvData τ p hN β)) u‖ ≤ r * ‖u‖)
    (hmode : γ ≤ modeCosAvg k r) :
    MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ :=
  MassGap.PeriodicReduce.periodic_torusReads_of_localReads τ p hN β k γ
    (fun x hx => local_of_readsClearWith (periodicGaugeInvData τ p hN β) k γ
      (readsClearWith_of_contraction (opT (periodicGaugeInvData τ p hN β))
        (isSelfAdjoint_opT (periodicGaugeInvData τ p hN β))
        (fun y hy => ⟨spectrum_opT_nonneg (periodicGaugeInvData τ p hN β)
            (periodic_positiveTransfer τ p hN hβ) hy,
          (spectrum_opT_subset_unit_interval (periodicGaugeInvData τ p hN β) hy).2⟩)
        _ (opT_Omega (periodicGaugeInvData τ p hN β)) k γ r hr0 hcon hmode)
      x hx)

#print axioms periodic_torusReads_of_contraction

/-- **The torus input, bracketed.** At `0 ≤ β`, aperture `2k + 1` and margin `γ`:

* a contraction of the periodic vacuum complement at a rate `r ≥ 0` with `γ ≤ modeCosAvg k r` gives
  `TorusReadsClearWith τ p hN β k γ`;
* `TorusReadsClearWith τ p hN β k γ` gives the contraction at every `s ≥ 0` with
  `modeCosAvg k s < γ`.

For `0 < γ ≤ 1` the two parameter sets are `[0, r_γ(k)]` and `(r_γ(k), ∞)`, and a contraction at
every `s > r_γ(k)` is one at `r_γ(k)`: the torus input is the statement that `opT` contracts the
vacuum complement at `r_γ(k)`, endpoint included (argued; not stated as a biconditional).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β`, `r`, `s`,
and the orthogonality. -/
theorem torusReads_bracket (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (k : ℕ)
    (γ : ℝ) :
    ((∃ r : ℝ, 0 ≤ r ∧ γ ≤ modeCosAvg k r ∧
        ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
          inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
            (periodicGaugeInvData τ p hN β).vac) u = 0 →
          ‖(opT (periodicGaugeInvData τ p hN β)) u‖ ≤ r * ‖u‖) →
      MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ) ∧
    (MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ →
      ∀ s : ℝ, 0 ≤ s → modeCosAvg k s < γ →
        ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
          inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
            (periodicGaugeInvData τ p hN β).vac) u = 0 →
          ∀ m : ℕ, ‖((opT (periodicGaugeInvData τ p hN β)) ^ m) u‖ ≤ s ^ m * ‖u‖) :=
  ⟨fun ⟨r, hr0, hmode, hcon⟩ =>
      periodic_torusReads_of_contraction τ p hN hβ k γ r hr0 hcon hmode,
    fun htorus s hs0 hsγ => periodic_contraction_of_torusReads τ p hN hβ k γ htorus s hs0 hsγ⟩

#print axioms torusReads_bracket

/-- **The torus input at margin `0` holds at every `β ≥ 0`.** At every aperture `2k + 1`,
`PeriodicReduce.TorusReadsClearWith τ p hN β k 0`: `opT` contracts the vacuum complement at rate `1`
(`GNSHilbert.norm_opT_le_one`), and `0 ≤ modeCosAvg k 1 = 0` (`modeCosAvg_one`), so
`periodic_torusReads_of_contraction` applies at `r = 1`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β` and the
margin; the `1` in the proof is `norm_opT_le_one`'s contraction constant, the massless mode at which
`modeCosAvg k` reads `0`. -/
theorem periodic_torusReads_zero_margin (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (k : ℕ) : MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k 0 :=
  periodic_torusReads_of_contraction τ p hN hβ k 0 1 zero_le_one
    (fun u _ => le_trans ((opT (periodicGaugeInvData τ p hN β)).le_opNorm u)
      (mul_le_mul_of_nonneg_right
        (MassGap.GNSHilbert.norm_opT_le_one (periodicGaugeInvData τ p hN β)) (norm_nonneg u)))
    (le_of_eq (modeCosAvg_one k).symm)

#print axioms periodic_torusReads_zero_margin

/-- **`PeriodicClayGapAt` gives the torus input back.** At `0 ≤ β`,
`PeriodicContent.PeriodicClayGapAt τ p hN β ρ` gives
`PeriodicReduce.TorusReadsClearWith τ p hN β 0 ((1 − ρ)/(1 + ρ))`. Its contraction conjunct,
`‖opT u‖ ≤ ρ ‖u‖` on the vacuum complement with `0 < ρ`, feeds `periodic_torusReads_of_contraction`
at `k = 0`, where `modeCosAvg 0 ρ = (1 − ρ)/(1 + ρ)`: the two lags have `circLag = 0, 1` and
cosines `cos 0 = 1`, `cos π = −1`, so `modeCos 0 ρ = 1 − ρ` and `modeMass 0 ρ = 1 + ρ`. With
`periodic_clayGapAt_of_torusReads_any_margin` at `2 ≤ N`, the torus input at some aperture and some
positive margin holds exactly when `PeriodicClayGapAt` holds at some `ρ` (argued; not stated as a
biconditional).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β` and the
aperture index `k = 0` (aperture `1`, lags `0` and `1`); in `(1 − ρ)/(1 + ρ)` each `1` is the
lag-`0` term `ρ⁰` (cosine `1`) and `ρ` the lag-`1` term (cosine `−1`). -/
theorem periodic_torusReads_of_clayGapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : ℝ} (h : MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β ρ) :
    MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β 0 ((1 - ρ) / (1 + ρ)) := by
  obtain ⟨hρ0, -, -, -, -, hcon, -⟩ := h
  have h0 : Moment.circLag (0 : Fin 2) = 0 := by decide
  have h1 : Moment.circLag (1 : Fin 2) = 1 := by decide
  have hd : ((2 * 0 + 1 : ℕ) : ℝ) + 1 = 2 := by norm_num
  have hM : modeMass 0 ρ = 1 + ρ := by
    show ∑ d : Fin 2, ρ ^ Moment.circLag d = 1 + ρ
    rw [Fin.sum_univ_two, h0, h1, pow_zero, pow_one]
  have ha : 2 * Real.pi * ((0 : ℕ) : ℝ) / (((2 * 0 + 1 : ℕ) : ℝ) + 1) = 0 := by
    rw [Nat.cast_zero]
    ring
  have hb : 2 * Real.pi * ((1 : ℕ) : ℝ) / (((2 * 0 + 1 : ℕ) : ℝ) + 1) = Real.pi := by
    rw [hd, Nat.cast_one]
    ring
  have hC : modeCos 0 ρ = 1 - ρ := by
    show ∑ d : Fin 2, ρ ^ Moment.circLag d
        * Real.cos (2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * 0 + 1 : ℕ) : ℝ) + 1)) = 1 - ρ
    rw [Fin.sum_univ_two, h0, h1, ha, hb, Real.cos_zero, Real.cos_pi, pow_zero, pow_one]
    ring
  have hmode : (1 - ρ) / (1 + ρ) ≤ modeCosAvg 0 ρ := by
    have e : modeCosAvg 0 ρ = (1 - ρ) / (1 + ρ) := by
      unfold modeCosAvg
      rw [hC, hM]
    exact le_of_eq e.symm
  exact periodic_torusReads_of_contraction τ p hN hβ 0 ((1 - ρ) / (1 + ρ)) ρ hρ0.le hcon hmode

#print axioms periodic_torusReads_of_clayGapAt

/-- **`PeriodicClayGapAt` from the torus input at any positive margin.** At `2 ≤ N`, `0 ≤ β` and
`0 < γ`, `PeriodicReduce.TorusReadsClearWith τ p hN β k γ` gives `ρ` with
`PeriodicContent.PeriodicClayGapAt τ p hN β ρ`. `exists_lt_one_modeCosAvg_lt` gives `s < 1` with
`modeCosAvg k s < γ`; `periodic_contraction_of_torusReads` contracts the vacuum complement at `s`,
hence at `ρ = (s + 1)/2 ∈ (0, 1)`; `GNSCompare.gapAt_iff_opT_contracts`,
`ClayCapstone.clay_gap_of_gapAt` and `PeriodicContent.periodic_exists_ne_zero_orth_vacuum` finish
as in `PeriodicContent.periodic_clayGapAt_of_reads`.

`0` is the threshold: at `γ = 0` the torus input holds at every `β ≥ 0`
(`periodic_torusReads_zero_margin`). At `γ > 0` the input is the gap itself: the contraction
conjunct of `PeriodicClayGapAt τ p hN β ρ`, at a rate `ρ ∈ (0, 1)`, gives it back at `k = 0`,
`γ = modeCosAvg 0 ρ = (1 − ρ)/(1 + ρ)` (`periodic_torusReads_of_clayGapAt`). The theorem adds the
spectral assembly and the non-zero complement to a contraction below `1`; it does not reduce the gap
to a weaker condition.

DERIVED: `2` is the least rank with a non-zero Haar variance of the real trace; `4` the spacetime
dimension; `0` the excluded rank, the lower end of `β`, the sign of `γ`. CHOSEN: `(s + 1)/2` inside
the proof, a point of `(s, 1)` that stays positive at `s = 0`; any such point serves. -/
theorem periodic_clayGapAt_of_torusReads_any_margin (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N)
    (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (htorus : MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ) :
    ∃ ρ : ℝ, MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β ρ := by
  obtain ⟨s, hs0, hs1, hsγ⟩ := exists_lt_one_modeCosAvg_lt k hγ
  have hcon := periodic_contraction_of_torusReads τ p hN hβ k γ htorus s hs0 hsγ
  have hρ0 : (0 : ℝ) < (s + 1) / 2 := by linarith
  have hρ1 : (s + 1) / 2 < 1 := by linarith
  have hcon' : ∀ y : H (periodicGaugeInvData τ p hN β).toReflForm,
      inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
        (periodicGaugeInvData τ p hN β).vac) y = (0 : ℂ) →
      ‖opT (periodicGaugeInvData τ p hN β) y‖ ≤ (s + 1) / 2 * ‖y‖ := by
    intro y hy
    have h1 := hcon y hy 1
    rw [pow_one, pow_one] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg y))
  have hg := (MassGap.GNSCompare.gapAt_iff_opT_contracts (periodicGaugeInvData τ p hN β)
    hρ0.le).mpr hcon'
  obtain ⟨hsa, _, hspec, hgreat⟩ := MassGap.ClayCapstone.clay_gap_of_gapAt
    (periodicGaugeInvData τ p hN β) hρ0 hρ1 (periodic_positiveTransfer τ p hN hβ) hg
  exact ⟨(s + 1) / 2, hρ0, hρ1, hsa, hspec, hgreat, hcon',
    MassGap.PeriodicContent.periodic_exists_ne_zero_orth_vacuum τ p hN2 hN hβ⟩

#print axioms periodic_clayGapAt_of_torusReads_any_margin

/-- **The gap at every positive coupling from the torus input at some positive margin.** At
`2 ≤ N`: if at every `β > 0` some aperture `2k + 1` and some margin `γ > 0` have
`TorusReadsClearWith τ p hN β k γ`, then at every `β > 0` there is `ρ` with
`PeriodicClayGapAt τ p hN β ρ` (`periodic_clayGapAt_of_torusReads_any_margin`). The hypothesis
holds at each `β > 0` exactly when the vacuum complement is contracted at some rate below `1`
(`periodic_torusReads_of_clayGapAt`; argued, not stated as a biconditional), which is the
conclusion's contraction conjunct.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` the excluded rank, the lower end
of `β` and the sign of `γ`; `4` the spacetime dimension. -/
theorem wilson_gaugeInv_mass_gap_every_coupling_any_margin (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N)
    (hN : N ≠ 0)
    (htorus : ∀ β : ℝ, 0 < β → ∃ k : ℕ, ∃ γ : ℝ, 0 < γ ∧
      MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ) :
    ∀ β : ℝ, 0 < β → ∃ ρ : ℝ, MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β ρ := by
  intro β hβ
  obtain ⟨k, γ, hγ, h⟩ := htorus β hβ
  exact periodic_clayGapAt_of_torusReads_any_margin τ p hN2 hN hβ.le k hγ h

#print axioms wilson_gaugeInv_mass_gap_every_coupling_any_margin

end Periodic

end MassGap.FloorRead
