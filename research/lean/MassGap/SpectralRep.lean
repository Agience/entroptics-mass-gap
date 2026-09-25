import Mathlib
import MassGap.GNSHilbert

/-!
# The spectral representation of a positive contraction

For a self-adjoint operator `a` on a complex Hilbert space with spectrum in `[0, 1]` and a vector `v`,
the correlation sequence `d ↦ re ⟪v, aᵈ v⟫` is the moment sequence of a measure on `[0, 1]`
(`exists_moment_measure`). The functional `f ↦ re ⟪v, f(a) v⟫` of the continuous functional calculus
is positive and linear on `C([0, 1])` (`momentFunctional`), so it has a Riesz–Markov measure; the
function `t ↦ tᵈ` evaluates to `aᵈ` (`cfc_pow_id`).

This is how an entroptic read is carried to the transfer operator: a read is made of a correlation
profile, and the profile is `∫ λᵈ dw(λ)` with `w ≥ 0` — the form
`ZeroMode.correlation_gap_of_tension` takes for finitely many modes.
-/

namespace MassGap.SpectralRep

open MeasureTheory CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A function on `[0, 1]` extended to `ℝ` by clamping.

DERIVED: `0` and `1` are the interval's ends. -/
noncomputable def ext01 (f : C_c(Set.Icc (0 : ℝ) 1, ℝ)) : ℝ → ℝ :=
  fun t => f (Set.projIcc 0 1 zero_le_one t)

/-- The clamped extension is continuous.

DERIVED: `0` and `1` are the interval's ends. -/
theorem continuous_ext01 (f : C_c(Set.Icc (0 : ℝ) 1, ℝ)) : Continuous (ext01 f) :=
  f.continuous.comp continuous_projIcc

#print axioms continuous_ext01

/-- The moment functional `f ↦ re ⟪v, f(a) v⟫` on continuous functions on `[0, 1]`, linear through
the continuous functional calculus.

DERIVED: `0` and `1` are the interval's ends. -/
noncomputable def momentLinear (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (v : E) :
    C_c(Set.Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ where
  toFun f := RCLike.re (inner ℂ v (cfc (ext01 f) a v))
  map_add' f g := by
    have he : ext01 (f + g) = fun t => ext01 f t + ext01 g t := rfl
    rw [he, cfc_add (a := a) (f := ext01 f) (g := ext01 g) (continuous_ext01 f).continuousOn
      (continuous_ext01 g).continuousOn, ContinuousLinearMap.add_apply, inner_add_right, map_add]
  map_smul' r f := by
    have he : ext01 (r • f) = fun t => r * ext01 f t := rfl
    rw [he, cfc_const_mul r (ext01 f) a (continuous_ext01 f).continuousOn]
    simp

/-- **The moment functional is positive**: a nonnegative `f` gives a positive operator `f(a)`
(`cfc_nonneg`, `ContinuousLinearMap.nonneg_iff_isPositive`), whose diagonal is nonnegative.

DERIVED: `0` and `1` are the interval's ends and the order's zero. -/
theorem momentLinear_nonneg (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (v : E)
    (f : C_c(Set.Icc (0 : ℝ) 1, ℝ)) (hf : 0 ≤ f) : 0 ≤ momentLinear a ha v f := by
  have hpos : 0 ≤ cfc (ext01 f) a := cfc_nonneg (fun x _ => hf _)
  exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos).re_inner_nonneg_right v

#print axioms momentLinear_nonneg

/-- The moment functional as a positive linear map.

DERIVED: `0` and `1` are the interval's ends. -/
noncomputable def momentFunctional (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (v : E) :
    C_c(Set.Icc (0 : ℝ) 1, ℝ) →ₚ[ℝ] ℝ :=
  { momentLinear a ha v with
    monotone' := fun f g hfg => by
      have h := momentLinear_nonneg a ha v (g - f) (sub_nonneg.mpr hfg)
      rw [map_sub] at h
      exact sub_nonneg.mp h }

/-- The monomial `t ↦ tᵈ` on `[0, 1]`, with its compact support.

DERIVED: `0` and `1` are the interval's ends. -/
noncomputable def monomial (d : ℕ) : C_c(Set.Icc (0 : ℝ) 1, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun t => (t : ℝ) ^ d, (continuous_subtype_val.pow d)⟩

/-- **The correlation sequence of a positive contraction is a moment sequence.** For `a` self-adjoint
with spectrum in `[0, 1]` and any `v`, there is a finite measure `w` on `[0, 1]` with
`re ⟪v, aᵈ v⟫ = ∫ tᵈ dw` for every `d`: the Riesz–Markov measure of `momentFunctional`
(`RealRMK.integral_rieszMeasure`), since `t ↦ tᵈ` on the spectrum evaluates to `aᵈ` (`cfc_pow_id`).

DERIVED: `0` and `1` are the interval's ends. -/
theorem exists_moment_measure (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (v : E) :
    ∃ w : Measure (Set.Icc (0 : ℝ) 1), IsFiniteMeasure w ∧
      ∀ d : ℕ, RCLike.re (inner ℂ v ((a ^ d) v)) = ∫ t, (t : ℝ) ^ d ∂w := by
  refine ⟨RealRMK.rieszMeasure (momentFunctional a ha v), inferInstance, fun d => ?_⟩
  have h := RealRMK.integral_rieszMeasure (momentFunctional a ha v) (monomial d)
  have hcfc : cfc (ext01 (monomial d)) a = a ^ d := by
    rw [← cfc_pow_id (R := ℝ) a d ha]
    refine cfc_congr (fun x hx => ?_)
    have hx01 := hspec hx
    show ((Set.projIcc 0 1 zero_le_one x : Set.Icc (0 : ℝ) 1) : ℝ) ^ d = x ^ d
    rw [Set.projIcc_of_mem zero_le_one hx01]
  have hval : momentFunctional a ha v (monomial d) = RCLike.re (inner ℂ v ((a ^ d) v)) := by
    show RCLike.re (inner ℂ v (cfc (ext01 (monomial d)) a v)) = _
    rw [hcfc]
  rw [← hval, ← h]
  rfl

#print axioms exists_moment_measure

/-- A continuous function on `[0, 1]` is integrable against a finite measure: it is bounded, the
interval being compact.

DERIVED: `0` and `1` are the interval's ends. -/
theorem integrable_of_continuous (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    {f : Set.Icc (0 : ℝ) 1 → ℝ} (hf : Continuous f) : Integrable f w := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => hC _ ⟨t, Set.mem_univ _, rfl⟩)

#print axioms integrable_of_continuous

/-- A continuous function on `ℝ` restricted to `[0, 1]`, with its compact support.

DERIVED: `0` and `1` are the interval's ends. -/
noncomputable def restr (h : ℝ → ℝ) (hh : Continuous h) : Set.Icc (0 : ℝ) 1 →C_c ℝ :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun t => h (t : ℝ), hh.comp continuous_subtype_val⟩

/-- On an operator with spectrum in `[0, 1]`, clamping and restricting `h` changes nothing:
`cfc (ext01 (restr h)) a = cfc h a`, the two functions agreeing on the spectrum.

DERIVED: `0` and `1` are the interval's ends. -/
theorem cfc_ext01_restr (a : E →L[ℂ] E) (hspec : spectrum ℝ a ⊆ Set.Icc 0 1)
    (h : ℝ → ℝ) (hh : Continuous h) : cfc (ext01 (restr h hh)) a = cfc h a := by
  refine cfc_congr (fun x hx => ?_)
  have hx01 := hspec hx
  show h ((Set.projIcc 0 1 zero_le_one x : Set.Icc (0 : ℝ) 1) : ℝ) = h x
  rw [Set.projIcc_of_mem zero_le_one hx01]

/-- **The spectral measure of a vector.** For `a` self-adjoint with spectrum in `[0, 1]` and any `v`,
one finite measure `w` on `[0, 1]` represents the whole functional calculus at `v`:
`re ⟪v, h(a) v⟫ = ∫ h dw` for every continuous `h`. The Riesz–Markov measure of `momentFunctional`.

DERIVED: `0` and `1` are the interval's ends. -/
theorem exists_spectral_measure (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (v : E) :
    ∃ w : Measure (Set.Icc (0 : ℝ) 1), IsFiniteMeasure w ∧
      ∀ h : ℝ → ℝ, Continuous h →
        RCLike.re (inner ℂ v (cfc h a v)) = ∫ t, h (t : ℝ) ∂w := by
  refine ⟨RealRMK.rieszMeasure (momentFunctional a ha v), inferInstance, fun h hh => ?_⟩
  have hI := RealRMK.integral_rieszMeasure (momentFunctional a ha v) (restr h hh)
  have hval : momentFunctional a ha v (restr h hh) = RCLike.re (inner ℂ v (cfc h a v)) := by
    show RCLike.re (inner ℂ v (cfc (ext01 (restr h hh)) a v)) = _
    rw [cfc_ext01_restr a hspec h hh]
  rw [← hval, ← hI]
  rfl

#print axioms exists_spectral_measure

/-- `⟪ψ(a) v, χ(a) ψ(a) v⟫ = ⟪v, (ψ χ ψ)(a) v⟫`: `ψ(a)` is self-adjoint (`cfc_predicate`), and the
functional calculus is multiplicative (`cfc_mul`).

DERIVED: no numeral occurs. -/
theorem inner_cfc_cfc (a : E →L[ℂ] E) (ψ χ : ℝ → ℝ) (hψ : Continuous ψ) (hχ : Continuous χ)
    (v : E) :
    inner ℂ (cfc ψ a v) (cfc χ a (cfc ψ a v))
      = inner ℂ v (cfc (fun t => ψ t * χ t * ψ t) a v) := by
  have hsa : IsSelfAdjoint (cfc ψ a) := cfc_predicate ψ a
  have hprod : cfc (fun t => ψ t * χ t * ψ t) a = cfc ψ a * cfc χ a * cfc ψ a := by
    rw [cfc_mul (fun t => ψ t * χ t) ψ a (hψ.mul hχ).continuousOn hψ.continuousOn,
      cfc_mul ψ χ a hψ.continuousOn hχ.continuousOn]
  rw [hprod, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  exact hsa.isSymmetric v _

#print axioms inner_cfc_cfc

/-- `‖ψ(a) v‖² = re ⟪v, ψ²(a) v⟫`: `inner_cfc_cfc` at `χ = 1`.

DERIVED: `2` is the square; `1` is the constant function `χ`. -/
theorem norm_sq_cfc (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (v : E) :
    ‖cfc ψ a v‖ ^ 2 = RCLike.re (inner ℂ v (cfc (fun t => ψ t * ψ t) a v)) := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  have h := inner_cfc_cfc a ψ (fun _ => 1) hψ continuous_const v
  rw [cfc_const_one ℝ a ha, ContinuousLinearMap.one_apply] at h
  rw [h]
  simp only [mul_one]

#print axioms norm_sq_cfc

/-- **A fixed vector is fixed by the whole functional calculus at `φ(1)`**: for `a` self-adjoint with
spectrum in `[0, 1]`, `a Ω = Ω` gives `φ(a) Ω = φ(1) • Ω` for every continuous `φ`. The spectral measure of `Ω` has `∫ (1 − t) dw =
⟪Ω, Ω⟫ − ⟪Ω, a Ω⟫ = 0` with `1 − t ≥ 0`, so it sits at `1`; then `‖(φ − φ(1))(a) Ω‖² =
∫ (φ − φ(1))² dw = 0` (`norm_sq_cfc`).

DERIVED: `1` is the eigenvalue of the fixed vector and the upper end of the interval; `0` its lower
end and the vanishing of the defect; `2` is the square in the norm. -/
theorem cfc_apply_of_fixed (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (φ : ℝ → ℝ)
    (hφ : Continuous φ) : cfc φ a Ω = φ 1 • Ω := by
  obtain ⟨w, hw, hint⟩ := exists_spectral_measure a ha hspec Ω
  have e1 : RCLike.re (inner ℂ Ω Ω) = ∫ _t, (1 : ℝ) ∂w := by
    have h := hint (fun _ => 1) continuous_const
    rw [cfc_const_one ℝ a ha, ContinuousLinearMap.one_apply] at h
    exact h
  have e2 : RCLike.re (inner ℂ Ω Ω) = ∫ t, (t : ℝ) ∂w := by
    have h := hint (fun t => t) continuous_id
    rw [cfc_id' ℝ a ha, hΩ] at h
    exact h
  have hz : ∫ t, (1 - (t : ℝ)) ∂w = 0 := by
    rw [integral_sub (integrable_const _) (integrable_of_continuous w continuous_subtype_val),
      ← e1, ← e2, sub_self]
  have hae : (fun t : Set.Icc (0 : ℝ) 1 => 1 - (t : ℝ)) =ᵐ[w] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun t => by show (0 : ℝ) ≤ 1 - (t : ℝ); exact sub_nonneg.mpr t.2.2)
      (integrable_of_continuous w (continuous_const.sub continuous_subtype_val))).mp hz
  have hψ : Continuous (fun t => φ t - φ 1) := hφ.sub continuous_const
  have hnorm := norm_sq_cfc a ha (fun t => φ t - φ 1) hψ Ω
  have hmeas := hint (fun t => (φ t - φ 1) * (φ t - φ 1)) (hψ.mul hψ)
  have hzero : ∫ t, (φ (t : ℝ) - φ 1) * (φ (t : ℝ) - φ 1) ∂w = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with t ht
    have h1 : (t : ℝ) = 1 := by
      have := ht
      simp only [Pi.zero_apply] at this
      linarith
    simp [h1]
  have hsq : ‖cfc (fun t => φ t - φ 1) a Ω‖ ^ 2 = 0 := by
    rw [hnorm]
    exact hmeas.trans hzero
  have h0 : cfc (fun t => φ t - φ 1) a Ω = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  rw [cfc_sub φ (fun _ => φ 1) a hφ.continuousOn continuousOn_const, cfc_const (φ 1) a ha,
    ContinuousLinearMap.sub_apply, sub_eq_zero, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at h0
  exact h0

#print axioms cfc_apply_of_fixed

end MassGap.SpectralRep
