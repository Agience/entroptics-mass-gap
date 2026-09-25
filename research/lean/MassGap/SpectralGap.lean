import Mathlib
import MassGap.SpectralRead
import MassGap.GNSHilbert

/-!
# The transfer gap from the reads

Let `a` be a self-adjoint operator with spectrum in `[0, 1]` fixing a vector `Ω`. Suppose every vector
orthogonal to `Ω` reads below the floor at aperture `2k + 1` (`ReadsClear`): the read whose correlation
is `d ↦ re ⟪v, a^{circLag d} v⟫` has a positive cosine average and tension below `¼·log 3`. Then
every vector orthogonal to `Ω` is contracted:

    ‖aᵐ u‖ ≤ ρᵐ ‖u‖,   ρ^{k+1} = 12 · (1 − 3^{−1/4}) / 8,   ρ < 1

(`gap_of_reads`), a gap of at least `−log ρ = −log(12(1 − 3^{−1/4})/8)/(k + 1)`, a bound set by the
aperture alone.

How. The spectral measure `w_u` of `u` (`SpectralRep.exists_spectral_measure`) gives no mass above
`λ₁` whenever `λ₁^{k+1}` reaches the cap (`measure_gt_eq_zero`): mass above `λ₁` has a slice
`[λ₁ + 2s, 1]` of positive measure, and the ramp `φ` rising from `0` at `λ₁ + s` to `1` at `λ₁ + 2s`
makes `v = φ(a) u` a vector orthogonal to `Ω` (`SpectralRep.cfc_apply_of_fixed`) whose correlation is
`∫ φ² λ^c dw_u` (`SpectralRep.inner_cfc_cfc`). Its read clears the floor, so
`SpectralRead.lam0_pow_lt_of_tension` puts `(λ₁ + s)^{k+1}` below the cap, which `λ₁^{k+1}` already
reaches. With no mass above `λ₁`, `‖aᵐ u‖² = ∫ λ^{2m} dw_u ≤ λ₁^{2m} ‖u‖²` (`norm_pow_le_of_reads`).

Why every vector. One profile clearing the floor is not a gap criterion — a profile decaying as a
power clears it. Reading every vector orthogonal to the vacuum is: a massless theory has vectors
whose spectral weight sits within any distance of `1`, and at a fixed aperture their reads fail.

What `ReadsClear` is. At a fixed aperture it is a condition on where the spectrum of `a` on the
complement of `Ω` sits. The cosine average of `v` is the `w_v`-weighted average of the single-mode
average, which vanishes at `1` (`ZeroMode.sum_cos_theta_eq_zero`), so the condition keeps that
spectrum out of a neighbourhood of `1`: it is the gap stated as a read. `gap_of_reads` turns it into a
norm bound, at a rate about `5.4` times below the single-mode threshold as `k` grows.
-/

namespace MassGap.SpectralGap

open MeasureTheory MassGap.SpectralRep MassGap.SpectralRead

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Every vector orthogonal to `Ω` reads below the floor at aperture `2k + 1`**: any read whose
correlation is `d ↦ re ⟪v, a^{circLag d} v⟫` has a positive cosine average and tension below
`¼·log 3`. The zero vector has no such read, its correlation summing to zero. For `a` self-adjoint with
spectrum in `[0, 1]` every nonzero `v` has exactly one such read, its correlation being the moments
of a positive measure with `ρ(0) = ‖v‖²`; the theorems below take that spectral condition.

DERIVED: `2` and `1` spell the aperture `2k + 1`; `0` is the orthogonality and the lower end of the
cosine average; `(1 / 4) * log 3` is the floor `κ₀YM`. -/
def ReadsClear (a : E →L[ℂ] E) (Ω : E) (k : ℕ) : Prop :=
  ∀ v : E, inner ℂ Ω v = 0 → ∀ R : Moment.Read (2 * k + 1),
    (∀ d, R.ρ d = RCLike.re (inner ℂ v ((a ^ Moment.circLag d) v))) →
      0 < ∑ d, R.p d * Real.cos (R.θ d) ∧ R.tension < (1 / 4) * Real.log 3

/-- The ramp rising from `0` at `m` to `1` at `m + s`, for `0 < s`.

DERIVED: `0` and `1` are the ramp's floor and ceiling. -/
noncomputable def ramp (m s : ℝ) (t : ℝ) : ℝ := min 1 (max 0 ((t - m) / s))

/-- `ramp m s` is continuous for every `m` and `s`.

DERIVED: no numeral occurs in the statement. -/
theorem continuous_ramp (m s : ℝ) : Continuous (ramp m s) :=
  continuous_const.min (continuous_const.max ((continuous_id.sub continuous_const).div_const s))

/-- DERIVED: `0` is the ramp's floor. -/
theorem ramp_nonneg (m s t : ℝ) : 0 ≤ ramp m s t := le_min zero_le_one (le_max_left _ _)

/-- DERIVED: `0` is the ramp's floor and the sign of `s`. -/
theorem ramp_eq_zero {m s t : ℝ} (hs : 0 < s) (ht : t < m) : ramp m s t = 0 := by
  have h : (t - m) / s < 0 := div_neg_of_neg_of_pos (by linarith) hs
  unfold ramp
  rw [max_eq_left h.le, min_eq_right zero_le_one]

/-- DERIVED: `1` is the ramp's ceiling; `0` the sign of `s`. -/
theorem ramp_eq_one {m s t : ℝ} (hs : 0 < s) (ht : m + s ≤ t) : ramp m s t = 1 := by
  have h : 1 ≤ (t - m) / s := by rw [le_div_iff₀ hs]; linarith
  unfold ramp
  rw [max_eq_right (by linarith), min_eq_left h]

/-- **No spectral weight above the cap.** Under `ReadsClear a Ω k`, for `u` orthogonal to `Ω` with
spectral measure `w`, and `λ₁ ≥ 0` with `λ₁^{k+1}` at least the cap `12(1 − 3^{−1/4})/8`,
`w` gives no mass to `{λ > λ₁}`.

DERIVED: `12`, `8`, `3`, `1` and `4` spell the cap of `SpectralRead.lam0_pow_lt_of_tension`; `0` and
`1` are the interval's ends; `0` is the orthogonality, the lower end of `λ₁` and the concluded null
mass; `1` is also the `+ 1` of `k + 1`, the aperture's; `2` and `1` spell the aperture `2k + 1`. -/
theorem measure_gt_eq_zero (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ)
    (hread : ReadsClear a Ω k) (u : E) (hu : inner ℂ Ω u = 0)
    (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (hw : ∀ h : ℝ → ℝ, Continuous h → RCLike.re (inner ℂ u (cfc h a u)) = ∫ t, h (t : ℝ) ∂w)
    (lam1 : ℝ) (h1 : 0 ≤ lam1)
    (hcap : 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ≤ lam1 ^ (k + 1)) :
    w {t | lam1 < (t : ℝ)} = 0 := by
  by_contra hne
  have hU : {t : Set.Icc (0 : ℝ) 1 | lam1 < (t : ℝ)}
      = ⋃ n : ℕ, {t : Set.Icc (0 : ℝ) 1 | lam1 + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)} := by
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
  -- the slice `[λ₁ + 2s, 1]` has positive mass; the ramp rises on `[λ₁ + s, λ₁ + 2s]`
  set s : ℝ := 1 / ((n : ℝ) + 1) / 2 with hs_def
  have hs : 0 < s := by positivity
  have hslice : lam1 + 1 / ((n : ℝ) + 1) = (lam1 + s) + s := by rw [hs_def]; ring
  have hm0 : 0 ≤ lam1 + s := by linarith
  set G : Set.Icc (0 : ℝ) 1 → ℝ := fun t => ramp (lam1 + s) s t * ramp (lam1 + s) s t with hG_def
  have hGc : Continuous G :=
    ((continuous_ramp _ _).comp continuous_subtype_val).mul
      ((continuous_ramp _ _).comp continuous_subtype_val)
  have hG0 : ∀ t, 0 ≤ G t := fun t => mul_self_nonneg _
  have hGs : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) < lam1 + s → G t = 0 := by
    intro t ht
    simp only [hG_def, ramp_eq_zero hs ht, mul_zero]
  -- the vector `v = φ(a) u`: its correlation is the weighted moment sequence
  have hmom : ∀ c : ℕ, RCLike.re (inner ℂ (cfc (ramp (lam1 + s) s) a u)
      ((a ^ c) (cfc (ramp (lam1 + s) s) a u))) = momW w G c := by
    intro c
    have h1' := inner_cfc_cfc a (ramp (lam1 + s) s) (fun x : ℝ => x ^ c)
      (continuous_ramp _ _) (continuous_pow c) u
    have h2' := hw (fun t => ramp (lam1 + s) s t * t ^ c * ramp (lam1 + s) s t)
      (((continuous_ramp _ _).mul (continuous_pow c)).mul (continuous_ramp _ _))
    beta_reduce at h1' h2'
    rw [cfc_pow_id (R := ℝ) a c ha] at h1'
    rw [h1', h2']
    show ∫ t, ramp (lam1 + s) s (t : ℝ) * (t : ℝ) ^ c * ramp (lam1 + s) s (t : ℝ) ∂w
      = ∫ t, G t * (t : ℝ) ^ c ∂w
    congr 1
    funext t
    simp only [hG_def]
    ring
  -- its correlation is nonnegative and has positive mass at lag zero
  have hnn : ∀ c : ℕ, 0 ≤ momW w G c :=
    fun c => integral_nonneg (fun t => mul_nonneg (hG0 t) (pow_nonneg t.2.1 _))
  have hS : MeasurableSet {t : Set.Icc (0 : ℝ) 1 | lam1 + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)} :=
    measurableSet_le measurable_const measurable_subtype_coe
  have hmass : 0 < momW w G 0 := by
    have hpos : 0 < w.real {t : Set.Icc (0 : ℝ) 1 | lam1 + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)} :=
      ENNReal.toReal_pos hn (measure_ne_top w _)
    refine lt_of_lt_of_le hpos ?_
    rw [← integral_indicator_one hS]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS)
      (integrable_of_continuous w (hGc.mul (continuous_subtype_val.pow 0))) (fun t => ?_)
    by_cases ht : t ∈ {t : Set.Icc (0 : ℝ) 1 | lam1 + 1 / ((n : ℝ) + 1) ≤ (t : ℝ)}
    · rw [Set.indicator_of_mem ht]
      have ht' : lam1 + s + s ≤ (t : ℝ) := by rw [← hslice]; exact ht
      simp only [hG_def, ramp_eq_one hs ht', pow_zero, mul_one, Pi.one_apply, le_refl]
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
  have hv : inner ℂ Ω (cfc (ramp (lam1 + s) s) a u) = 0 := by
    have hsa : IsSelfAdjoint (cfc (ramp (lam1 + s) s) a) := cfc_predicate _ a
    have hsym : inner ℂ (cfc (ramp (lam1 + s) s) a Ω) u
        = inner ℂ Ω (cfc (ramp (lam1 + s) s) a u) := hsa.isSymmetric Ω u
    rw [← hsym, cfc_apply_of_fixed a ha hspec Ω hΩ _ (continuous_ramp _ _),
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hu, mul_zero]
  obtain ⟨hcos, htens⟩ := hread _ hv R (fun d => (hmom _).symm)
  have hlt := lam0_pow_lt_of_tension k w G hGc hG0 (lam1 + s) hm0 hGs R (fun d => rfl) hcos htens
  have hmono : lam1 ^ (k + 1) < (lam1 + s) ^ (k + 1) :=
    pow_lt_pow_left₀ (by linarith) h1 (Nat.succ_ne_zero k)
  linarith

#print axioms measure_gt_eq_zero

/-- **Every vector orthogonal to `Ω` is contracted at the cap's rate.** Under `ReadsClear a Ω k`, for
`u` orthogonal to `Ω` and `λ₁ ≥ 0` with `λ₁^{k+1}` at least the cap: `‖aᵐ u‖ ≤ λ₁ᵐ ‖u‖`.

DERIVED: `12`, `8`, `3`, `1` and `4` spell the cap; `0` and `1` are the interval's ends; `0` is the
orthogonality and the lower end of `λ₁`; `1` is also the `+ 1` of `k + 1`, the aperture's. -/
theorem norm_pow_le_of_reads (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ)
    (hread : ReadsClear a Ω k) (u : E) (hu : inner ℂ Ω u = 0) (lam1 : ℝ) (h1 : 0 ≤ lam1)
    (hcap : 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ≤ lam1 ^ (k + 1)) (m : ℕ) :
    ‖(a ^ m) u‖ ≤ lam1 ^ m * ‖u‖ := by
  obtain ⟨w, hw, hint⟩ := exists_spectral_measure a ha hspec u
  have hnull := measure_gt_eq_zero a ha hspec Ω hΩ k hread u hu w hint lam1 h1 hcap
  have hae : ∀ᵐ t : Set.Icc (0 : ℝ) 1 ∂w, (t : ℝ) ≤ lam1 := by
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
  have hsq : ‖(a ^ m) u‖ ^ 2 ≤ (lam1 ^ m * ‖u‖) ^ 2 := by
    rw [hA, mul_pow, hu2, ← integral_const_mul]
    refine integral_mono_ae
      (integrable_of_continuous w
        ((continuous_subtype_val.pow m).mul (continuous_subtype_val.pow m)))
      (integrable_const _) ?_
    filter_upwards [hae] with t ht
    have hp := pow_le_pow_left₀ t.2.1 ht m
    have hp0 := pow_nonneg t.2.1 m
    show (t : ℝ) ^ m * (t : ℝ) ^ m ≤ (lam1 ^ m) ^ 2 * 1
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

#print axioms norm_pow_le_of_reads

/-- The cap `12(1 − 3^{−1/4})/8 = 0.3602…` lies in `(0, 1)`: `3^{−1/4}` lies strictly between `1/3`
and `1`. The bracket of `ZeroMode.exists_uniform_rate_of_mode_invariant`.

DERIVED: `12`, `8`, `3`, `1` and `4` spell the cap; `0` and `1` are the ends of the unit interval;
`1/3 = 3^{−1}` is the lower bracket. -/
theorem cap_pos_lt_one :
    0 < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)
      ∧ 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) < 1 := by
  have hlt1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgt : (3 : ℝ) ^ (-(1 : ℝ) / 4) > 1 / 3 := by
    have hstep : (3 : ℝ) ^ (-(1 : ℝ)) < (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    rw [Real.rpow_neg_one] at hstep
    norm_num at hstep ⊢
    linarith
  constructor <;> nlinarith

#print axioms cap_pos_lt_one

/-- **The transfer gap from the reads.** Under `ReadsClear a Ω k`, with `ρ = cap^{1/(k+1)}`:
`0 ≤ ρ < 1`, `ρ^{k+1} = 12(1 − 3^{−1/4})/8`, and every vector orthogonal to `Ω` has
`‖aᵐ u‖ ≤ ρᵐ ‖u‖`: a gap of at least `−log ρ = −log(12(1 − 3^{−1/4})/8)/(k + 1)`, a bound set by the
aperture alone.

DERIVED: `12`, `8`, `3`, `1` and `4` spell the cap; `1` in `k + 1` is the aperture's `+ 1`; `0` and `1`
bracket `ρ` and are the interval's ends; `0` is the orthogonality. -/
theorem gap_of_reads (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ)
    (hread : ReadsClear a Ω k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : E, inner ℂ Ω u = 0 → ∀ m : ℕ, ‖(a ^ m) u‖ ≤ ρ ^ m * ‖u‖ := by
  obtain ⟨hc0, hc1⟩ := cap_pos_lt_one
  set c : ℝ := 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) with hc_def
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpow : (c ^ ((1 : ℝ) / ((k : ℝ) + 1))) ^ (k + 1) = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    have : (1 : ℝ) / ((k : ℝ) + 1) * ((k + 1 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  refine ⟨c ^ ((1 : ℝ) / ((k : ℝ) + 1)), Real.rpow_nonneg hc0.le _,
    Real.rpow_lt_one hc0.le hc1 (by positivity), hpow, fun u hu m => ?_⟩
  exact norm_pow_le_of_reads a ha hspec Ω hΩ k hread u hu _ (Real.rpow_nonneg hc0.le _)
    hpow.ge m

#print axioms gap_of_reads

/-- **The transfer gap on the GNS Hilbert space, from the reads.** For transfer data `D` with
`PositiveTransfer D`, the operator `opT D` is self-adjoint (`GNSHilbert.isSelfAdjoint_opT`) with
spectrum in `[0, 1]` (`GNSHilbert.spectrum_opT_subset_unit_interval`,
`GNSHilbert.spectrum_opT_nonneg`) and fixes the vacuum (`GNSHilbert.opT_Omega`); so `ReadsClear` at
aperture `2k + 1` gives `gap_of_reads`.

DERIVED: `12`, `8`, `3`, `1` and `4` spell the cap `12(1 − 3^{−1/4})/8`; `1` is also the `+ 1` of
`k + 1`, the aperture's; `0` and `1` bracket `ρ`; `0` is the orthogonality. -/
theorem opT_gap_of_reads {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : MassGap.Transfer.TransferData A) (hP : MassGap.GNSHilbert.PositiveTransfer D) (k : ℕ)
    (hread : ReadsClear (MassGap.GNSHilbert.opT D)
      (MassGap.GNSHilbert.Omega D.toReflForm D.vac) k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : MassGap.GNSHilbert.H D.toReflForm,
        inner ℂ (MassGap.GNSHilbert.Omega D.toReflForm D.vac) u = 0 →
        ∀ m : ℕ, ‖((MassGap.GNSHilbert.opT D) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  gap_of_reads (MassGap.GNSHilbert.opT D) (MassGap.GNSHilbert.isSelfAdjoint_opT D)
    (fun x hx => ⟨MassGap.GNSHilbert.spectrum_opT_nonneg D hP hx,
      (MassGap.GNSHilbert.spectrum_opT_subset_unit_interval D hx).2⟩)
    _ (MassGap.GNSHilbert.opT_Omega D) k hread

#print axioms opT_gap_of_reads

/-- **The physical rate at a fixed window.** Under `ReadsClear a Ω k`, with `sp` the spacing and the
aperture `2k + 1` spanning the physical extent `L = 2(k + 1)·sp`: the vacuum complement is contracted
at a rate `ρ` with `−log ρ / sp = −2·log(12(1 − 3^{−1/4})/8) / L = κ*/L`, `κ* ≈ 2.04`, so the
physical gap is at least `κ*/L`, a bound that reads no spacing.

DERIVED: `2(k + 1)` is the number of sites of the aperture `2k + 1`; `2` in `κ* = −2·log cap` is that
doubling; `12`, `8`, `3`, `1` and `4` spell the cap; `0` and `1` bracket `ρ` and are the interval's
ends; `0` is the sign of `sp`, of the physical rate, and the orthogonality. -/
theorem physical_gap_of_reads (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ)
    (hread : ReadsClear a Ω k) (sp L : ℝ) (hsp : 0 < sp)
    (hL : (2 * ((k : ℝ) + 1)) * sp = L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      -Real.log ρ / sp = -2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) / L ∧
      0 < -Real.log ρ / sp ∧
      ∀ u : E, inner ℂ Ω u = 0 → ∀ m : ℕ, ‖(a ^ m) u‖ ≤ ρ ^ m * ‖u‖ := by
  obtain ⟨ρ, hρ0, hρ1, hρk, hdec⟩ := gap_of_reads a ha hspec Ω hΩ k hread
  obtain ⟨hc0, _⟩ := cap_pos_lt_one
  have hρpos : 0 < ρ := by
    rcases hρ0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow (Nat.succ_ne_zero k)] at hρk
      linarith
  have hlog : ((k : ℝ) + 1) * Real.log ρ
      = Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) := by
    rw [← hρk, Real.log_pow]
    push_cast
    ring
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hneg : Real.log ρ < 0 := Real.log_neg hρpos hρ1
  refine ⟨ρ, hρpos, hρ1, ?_, div_pos (by linarith) hsp, hdec⟩
  rw [← hL, ← hlog, div_eq_div_iff (ne_of_gt hsp) (by positivity)]
  ring

#print axioms physical_gap_of_reads

/-- **One physical rate across spacings.** A family of self-adjoint operators `a j` with spectrum in
`[0, 1]` fixing `Ω j` (in use, lattice transfer operators at spacing `sp j`), each satisfying
`ReadsClear` at aperture `2k_j + 1`, with `2(k_j + 1)·sp j = L`: every member contracts its vacuum
complement at a rate whose physical value is `κ*/L = −2·log(12(1 − 3^{−1/4})/8)/L`, so every member's
physical gap is at least `κ*/L`. `physical_gap_of_reads` at each `j`; the members are not related to
one another and no limit is taken.

DERIVED: `2(k_j + 1)` is the number of sites of the aperture `2k_j + 1`, and `2` in
`κ* = −2·log cap` is that doubling; `12`, `8`, `3`, `1` and `4` spell the cap; `0` and `1` bracket `ρ`,
`0` is the sign of each spacing and the orthogonality. -/
theorem uniform_physical_gap_of_reads {ι : Type*} (E' : ι → Type*)
    [∀ j, NormedAddCommGroup (E' j)] [∀ j, InnerProductSpace ℂ (E' j)] [∀ j, CompleteSpace (E' j)]
    (a : ∀ j, E' j →L[ℂ] E' j) (ha : ∀ j, IsSelfAdjoint (a j))
    (hspec : ∀ j, spectrum ℝ (a j) ⊆ Set.Icc 0 1) (Ω : ∀ j, E' j) (hΩ : ∀ j, a j (Ω j) = Ω j)
    (k : ι → ℕ) (hread : ∀ j, ReadsClear (a j) (Ω j) (k j))
    (sp : ι → ℝ) (L : ℝ) (hsp : ∀ j, 0 < sp j) (hL : ∀ j, (2 * ((k j : ℝ) + 1)) * sp j = L) :
    ∀ j, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      -Real.log ρ / sp j = -2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) / L ∧
      0 < -Real.log ρ / sp j ∧
      ∀ u : E' j, inner ℂ (Ω j) u = 0 → ∀ m : ℕ, ‖((a j) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  fun j => physical_gap_of_reads (a j) (ha j) (hspec j) (Ω j) (hΩ j) (k j) (hread j) (sp j) L
    (hsp j) (hL j)

#print axioms uniform_physical_gap_of_reads

end MassGap.SpectralGap
