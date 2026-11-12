import Mathlib
import MassGap.OpenAIBridgeRP

/-!
# MassGap.OpenAIBridgeCubic — the connected slab correlation on the cubic torus alone

`OpenAIBridgeRP.connK_rp_full` bounds the excited–excited trace and the one-point excited traces of
the connected torus correlation by Hilbert–Schmidt readings `hsRead` taken at the sandwich of the
cross terms. Those readings are traces over a short chain and are extensive in the spatial volume.
This module bounds the same traces by Cauchy–Schwarz at full length, so that every factor lives on
the cubic torus of side `L`: the transfer chain of `L` steps of the slice kernel of side `L`.

## The thermal remainder

For a kernel insertion `F` covering `w` steps, with the transfer kernel split at its vacuum,
`K = c φ⊗φ + R`, and a split `L = 2w + (2a+2) + (2b+2)` of the torus,

    Tr(F K^{2a+2} Fᵀ K^{2b+2}) / |c|^L = α_F² + R_F(a) + R_{Fᵀ}(b) + D_L(f)

(`reflMoment_decomp`). The left side is `(1 + σ₀) E_L[f · θf]` with `σ₀` the excited weight of
the torus (`moment_ratio`), the first three terms are the vacuum and reflected readings of
`OpenAIBridgeRP`, and the last,

    D_L(f) = ‖R^{b+1} F R^{a+1}‖²_HS / |c|^L = Tr(F R^{2a+2} Fᵀ R^{2b+2}) / |c|^L ≥ 0,

is the thermal remainder of the reflected moment: the part of `E_L[f · θf]` that the vacuum does
not carry, normalized (`thermRem`, `thermRem_eq_moment`).

## 1. Full-length Cauchy–Schwarz

* `abs_trOne_cubic_rem`, `abs_trOne_cubic` — the one-point excited trace:
  `|Tr(F R^{L−w})| / |c|^L ≤ √D_L(f) √σ₀ ≤ √((1+σ₀) E_L[f · θf]) √σ₀`;
* `abs_trK_sand`, `abs_trK_cubic` — the excited–excited trace, for `p = a_F + b_G + 1`,
  `q = a_G + b_F + 1` and `w + a_F + b_F = w' + a_G + b_G`:
  `|Tr(F R^{p+1} G R^{q+1})| / |c|^L ≤ √(D_L(f) D_L(g))`.

## 2. The connected correlation

* `connK_rp_cubic_rem` — the cross terms of `connK_rp_full`, plus `√(D_L(f) D_L(g))`, plus
  `|α_f||α_g| σ₀ + |α_f| √D_L(g) √σ₀ + |α_g| √D_L(f) √σ₀ + √(D_L(f) D_L(g)) σ₀`;
* `connK_rp_cubic` — the same with every reading bounded by a cubic-torus moment
  `𝓜 = (1+σ₀) E_L[·]` of `F`, `Fᵀ`, `G`, `Gᵀ` (`reflMoment_le_torus_ratio`):
  `|connK| ≤ (1/2)^⌊(j+1)/n⌋ √(𝓜_{f θf} 𝓜_{θg g}) + (1/2)^⌊(j'+1)/n⌋ √(𝓜_{θf f} 𝓜_{g θg})
  + √(D_L(f) D_L(g)) + 2 √(𝓜_{f θf} 𝓜_{g θg}) (σ₀ + √σ₀)`.

## 3. On the Wilson torus of every gauge group

* `measurable_revG`, `abs_revG_le`, `localUpTo_revG` — the reflected slab observable is a bounded
  measurable slab observable of the same width;
* `expect_pair_eqG` — the torus expectation of a product of two slab observables is the trace
  ratio of their slab kernels;
* `wilson_slab_conn_cubicG` — from the seed, on the cubic torus of every side `L = 2l + 2 ≥ 8n`:
  `σ₀ ≤ (1/2)^⌊(l+1)/n⌋`, and the bound of `connK_rp_cubic` with every `E_L` a literal torus
  expectation `⟨f_0 · (θf)_s⟩` of a slab observable times a reflected slab
  (`OpenAIBridgeRP.revG`, `OpenAIBridgeRP.slabKer_rev_wtG`).

## 4. The input that remains

* `ThermalRemainderVanishes` — `D_L(f_t) → 0` along the family order; `sqrt_mul_vanishes` — the
  excited–excited term of `connK_rp_cubic` then vanishes along the same order.

## Scope

No sup bound and no rectangular torus enters any statement. The full-length Cauchy–Schwarz leaves
no decay factor on the excited–excited term: `√(D_L(f) D_L(g))` is small only if the thermal
remainders are, which is the named input `ThermalRemainderVanishes` and is not proved here.
-/

namespace MassGap.OpenAIBridgeCubic

open MeasureTheory Real Filter
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeUniform MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP

/-! ## The thermal remainder and the torus moment -/

section Defs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **The thermal remainder of a reflected moment**: for `F` covering `w` steps and the split
`L = 2w + (2a+2) + (2b+2)`, `thermRem μ k c φ F w a b = ‖R^{b+1} F R^{a+1}‖²_HS / |c|^L`. By
`OpenAIBridgeRP.hs_sand_eq2` the numerator is `Tr(F R^{2a+2} Fᵀ R^{2b+2})`: the part of the torus
moment of `f` with its reflection that no vacuum projection carries (`reflMoment_decomp`).

DERIVED: `2` is the square of the norm and the doubled separations; `1` the offset of `iter`. -/
noncomputable def thermRem (μ : Measure X) (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ)
    (w a b : ℕ) : ℝ :=
  hs μ (conv μ (iter μ (rem k c φ) b) (conv μ F (iter μ (rem k c φ) a)))
    / |c| ^ (w + w + (a + a + 2) + (b + b + 2))

/-- **The reflected torus moment**: `torusMom μ k F a b i = Tr(F K^{2a+2} Fᵀ K^{2b+2}) / Tr K^{2i+2}`,
the torus expectation `E_L[f · θf]` of the insertion with its reflection on the torus of
`L = 2i + 2` steps (when `i = w + a + b + 1`).

DERIVED: `1` and `2` are the offsets of `iter`, so `a + a + 1` is the power `2a + 2`. -/
noncomputable def torusMom (μ : Measure X) (k F : X → X → ℝ) (a b i : ℕ) : ℝ :=
  trK μ k F (tp F) (a + a + 1) (b + b + 1) / trPow μ k (i + i + 1)

/-- The thermal remainder is nonnegative.

DERIVED: `0` is the sign. -/
theorem thermRem_nonneg (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w a b : ℕ) :
    0 ≤ thermRem μ k c φ F w a b :=
  div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg c) _)

/-- The square root of the thermal remainder:
`√(thermRem F w a b) = ‖R^{b+1} F R^{a+1}‖_HS / |c|^{w+a+b+2}`.

DERIVED: `2` is the square and the two offsets of `iter`. -/
theorem sqrt_thermRem (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w a b : ℕ) :
    √(thermRem μ k c φ F w a b)
      = √(hs μ (conv μ (iter μ (rem k c φ) b) (conv μ F (iter μ (rem k c φ) a))))
        / |c| ^ (w + a + b + 2) := by
  unfold thermRem
  rw [show |c| ^ (w + w + (a + a + 2) + (b + b + 2)) = (|c| ^ (w + a + b + 2)) ^ 2 by ring,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (pow_nonneg (abs_nonneg c) _)]

end Defs

/-! ## 1. Full-length Cauchy–Schwarz -/

section Cubic

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

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **The reflected torus moment splits at the vacuum into four nonnegative parts**: for a bounded
kernel insertion `F` covering `w` steps and every `a`, `b`,

    Tr(F K^{2a+2} Fᵀ K^{2b+2}) / |c|^L = α_F² + R_F(a) + R_{Fᵀ}(b) + D_L(f),

`L = 2w + (2a+2) + (2b+2)`: `trK_decomp` with `vac_tp`, two reflected readings (`rpRead_eq`) and
the thermal remainder (`hs_sand_eq2`).

DERIVED: `1` and `2` are the offsets of `iter`, so `a + a + 2` and `b + b + 2` are the separations;
`2` the square of the vacuum reading. -/
theorem reflMoment_decomp (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    trK μ k F (tp F) (a + a + 1) (b + b + 1) / |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      = vacRead μ c φ F w ^ 2 + OpenAIBridgeRP.refl μ k c φ F w a + OpenAIBridgeRP.refl μ k c φ (tp F) w b
        + thermRem μ k c φ F w a b := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hc : 0 < |c| := abs_pos.mpr hc0
  obtain ⟨CF, hCF⟩ := hF.bdd
  have hfm := measurable_kf (μ := μ) hF hφm
  have hfb : ∀ x, |kernelFun F μ φ x| ≤ CF * Bφ := abs_kf_le hCF hφb
  have hum := measurable_kf (μ := μ) (bdd_tp hF) hφm
  have hub : ∀ x, |kernelFun (tp F) μ φ x| ≤ CF * Bφ := abs_kf_le (fun x y => hCF y x) hφb
  have hdec := trK_decomp hφm hφb hφ1 hkm hkb hsym heig hF (bdd_tp hF) (a + a + 1) (b + b + 1)
  have hV : ∫ x, kernelFun (tp F) μ φ x * φ x ∂μ = ∫ x, kernelFun F μ φ x * φ x ∂μ :=
    vac_tp hφm hφb hF
  have hT2 : ∫ x, kernelFun F μ φ x
      * kernelFun (iter μ (rem k c φ) (b + b + 1)) μ (kernelFun (tp (tp F)) μ φ) x ∂μ
      = rpRead μ (rem k c φ) b (kernelFun (tp (tp F)) μ φ) :=
    (rpRead_eq (μ := μ) hr hrs hfm hfb b).symm
  have hT3 : ∫ x, kernelFun (tp F) μ φ x
      * kernelFun (iter μ (rem k c φ) (a + a + 1)) μ (kernelFun (tp F) μ φ) x ∂μ
      = rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ) := (rpRead_eq hr hrs hum hub a).symm
  have hT4 : trK μ (rem k c φ) F (tp F) (a + a + 1) (b + b + 1)
      = hs μ (conv μ (iter μ (rem k c φ) b) (conv μ F (iter μ (rem k c φ) a))) :=
    (hs_sand_eq2 hr hrs hF a b).symm
  rw [hV, hT2, hT3, hT4] at hdec
  have hPa : |c| ^ (a + a + 2) = c ^ (a + a + 1 + 1) := Even.pow_abs ⟨a + 1, by ring⟩ c
  have hPb : |c| ^ (b + b + 2) = c ^ (b + b + 1 + 1) := Even.pow_abs ⟨b + 1, by ring⟩ c
  have hw0 : |c| ^ w ≠ 0 := pow_ne_zero _ hc.ne'
  have ha0 : |c| ^ (a + a + 2) ≠ 0 := pow_ne_zero _ hc.ne'
  have hb0 : |c| ^ (b + b + 2) ≠ 0 := pow_ne_zero _ hc.ne'
  unfold vacRead OpenAIBridgeRP.refl thermRem
  rw [hdec, ← hPa, ← hPb,
    show |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      = |c| ^ w * |c| ^ w * |c| ^ (a + a + 2) * |c| ^ (b + b + 2) by rw [pow_add, pow_add, pow_add],
    show |c| ^ (2 * (w + a + 1)) = |c| ^ w * |c| ^ w * |c| ^ (a + a + 2) by
      rw [show 2 * (w + a + 1) = w + w + (a + a + 2) by ring, pow_add, pow_add],
    show |c| ^ (2 * (w + b + 1)) = |c| ^ w * |c| ^ w * |c| ^ (b + b + 2) by
      rw [show 2 * (w + b + 1) = w + w + (b + b + 2) by ring, pow_add, pow_add]]
  field_simp
  ring

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **The normalized reflected trace is the torus moment times `1 + σ₀`**: with
`L = 2(w + a + b + 2)`, `Tr K^L = |c|^L (1 + σ₀)`, `σ₀ = excited (w + a + b + 2)` (`trPow_even`),
so `Tr(F K^{2a+2} Fᵀ K^{2b+2}) / |c|^L = (1 + σ₀) E_L[f · θf]`.

DERIVED: `1` is the vacuum's own weight in `Tr K^L`; `1` and `2` the offsets of `iter` and of the
excited weight. -/
theorem moment_ratio (hc0 : c ≠ 0) (F : X → X → ℝ) (w a b : ℕ) :
    trK μ k F (tp F) (a + a + 1) (b + b + 1) / |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      = (1 + excited μ k c φ (w + a + b + 2)) * torusMom μ k F a b (w + a + b + 1) := by
  have ht := trPow_even hφm hφb hφ1 hkm hkb hsym heig (w + a + b + 1)
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcL : c ^ (w + a + b + 1 + (w + a + b + 1) + 2)
      = |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := by
    rw [show w + a + b + 1 + (w + a + b + 1) + 2 = w + w + (a + a + 2) + (b + b + 2) by ring]
    exact (Even.pow_abs ⟨w + a + b + 2, by ring⟩ c).symm
  have h2L : |c| ^ (2 * (w + a + b + 2)) = |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := by
    rw [show 2 * (w + a + b + 2) = w + w + (a + a + 2) + (b + b + 2) by ring]
  have hP : 0 < |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := pow_pos hc _
  have hH : 0 ≤ hs μ (iter μ (rem k c φ) (w + a + b + 1)) := hs_nonneg _
  have hPH : |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      + hs μ (iter μ (rem k c φ) (w + a + b + 1)) ≠ 0 := (add_pos_of_pos_of_nonneg hP hH).ne'
  have hP0 : |c| ^ (w + w + (a + a + 2) + (b + b + 2)) ≠ 0 := hP.ne'
  unfold torusMom
  rw [ht, hcL]
  unfold excited
  rw [show w + a + b + 2 - 1 = w + a + b + 1 by omega, h2L]
  field_simp
  try ring

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **The thermal remainder is the reflected moment less its vacuum parts**:
`D_L(f) = (1 + σ₀) E_L[f · θf] − α_F² − R_F(a) − R_{Fᵀ}(b)`, `σ₀ = excited (w + a + b + 2)`
(`reflMoment_decomp`, `moment_ratio`).

DERIVED: `1` is the vacuum's own weight; `2` the square of the vacuum reading and the offset of the
excited weight; `1` the offset of `iter`. -/
theorem thermRem_eq_moment (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    thermRem μ k c φ F w a b
      = (1 + excited μ k c φ (w + a + b + 2)) * torusMom μ k F a b (w + a + b + 1)
        - vacRead μ c φ F w ^ 2 - OpenAIBridgeRP.refl μ k c φ F w a - OpenAIBridgeRP.refl μ k c φ (tp F) w b := by
  have h1 := reflMoment_decomp hφm hφb hφ1 hkm hkb hsym heig hc0 hF w a b
  have h2 := moment_ratio hφm hφb hφ1 hkm hkb hsym heig hc0 F w a b
  linarith

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **Each part of the reflected moment is below it**: the thermal remainder, the squared vacuum
reading and the reflected reading of `F` are each at most `(1 + σ₀) E_L[f · θf]`.

DERIVED: `1` is the vacuum's own weight; `2` the square and the offset of the excited weight; `1`
the offset of `iter`. -/
theorem parts_le_moment (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    thermRem μ k c φ F w a b
        ≤ (1 + excited μ k c φ (w + a + b + 2)) * torusMom μ k F a b (w + a + b + 1)
      ∧ vacRead μ c φ F w ^ 2
        ≤ (1 + excited μ k c φ (w + a + b + 2)) * torusMom μ k F a b (w + a + b + 1)
      ∧ OpenAIBridgeRP.refl μ k c φ F w a
        ≤ (1 + excited μ k c φ (w + a + b + 2)) * torusMom μ k F a b (w + a + b + 1) := by
  have h := thermRem_eq_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w a b
  have e0 := thermRem_nonneg (μ := μ) k c φ F w a b
  have e1 := sq_nonneg (vacRead μ c φ F w)
  have e2 := refl_nonneg (μ := μ) k c φ F w a
  have e3 := refl_nonneg (μ := μ) k c φ (tp F) w b
  refine ⟨by linarith, by linarith, by linarith⟩

include hφm hφb hkm hkb in
/-- **The one-point excited trace at full length, on the cubic torus**: with
`L = 2w + (2a+2) + (2b+2)`,

    |Tr(F R^{L−w})| / |c|^L ≤ √D_L(f) · √σ₀,   σ₀ = excited (L/2).

`R^{L−w} = R^{a+1} R^{L/2} R^{b+1}`, cyclicity puts `R^{b+1} F R^{a+1}` against `R^{L/2}`, and
`OpenAIBridgeRP.abs_trc_le` with `hs(R^{L/2}) = σ₀ |c|^L`. Both factors are on the torus of `L`
steps; no sup bound enters.

DERIVED: `3` is `L − w − 1`, the offset of `iter` included; `1`, `2` the offsets of `iter` and the
squares. -/
theorem abs_trOne_cubic_rem (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    |trc μ (conv μ F (iter μ (rem k c φ) (w + a + a + b + b + 3)))|
        / |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      ≤ √(thermRem μ k c φ F w a b) * √(excited μ k c φ (w + a + b + 2)) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hA : Bdd (iter μ (rem k c φ) a) := hr.iter a
  have hB : Bdd (iter μ (rem k c φ) b) := hr.iter b
  have hE : Bdd (iter μ (rem k c φ) (w + a + b + 1)) := hr.iter (w + a + b + 1)
  have hFA : Bdd (conv μ F (iter μ (rem k c φ) a)) := hF.conv hA
  have hEB : Bdd (conv μ (iter μ (rem k c φ) (w + a + b + 1)) (iter μ (rem k c φ) b)) :=
    hE.conv hB
  have hFAE : Bdd (conv μ (conv μ F (iter μ (rem k c φ) a)) (iter μ (rem k c φ) (w + a + b + 1))) :=
    hFA.conv hE
  have hP : Bdd (conv μ (iter μ (rem k c φ) b) (conv μ F (iter μ (rem k c φ) a))) := hB.conv hFA
  have htr : trc μ (conv μ F (iter μ (rem k c φ) (w + a + a + b + b + 3)))
      = trc μ (conv μ (conv μ (iter μ (rem k c φ) b) (conv μ F (iter μ (rem k c φ) a)))
          (iter μ (rem k c φ) (w + a + b + 1))) := by
    rw [show w + a + a + b + b + 3 = a + (w + a + b + 1 + b + 1) + 1 by omega,
      iter_add hr a (w + a + b + 1 + b + 1), iter_add hr (w + a + b + 1) b,
      conv_assoc hF hA hEB, conv_assoc hFA hE hB, trc_conv_comm hFAE hB, conv_assoc hB hFA hE]
  have h1 := abs_trc_le (μ := μ) hP hE
  have hσ : hs μ (iter μ (rem k c φ) (w + a + b + 1))
      = excited μ k c φ (w + a + b + 2) * (|c| ^ (w + a + b + 2)) ^ 2 := by
    unfold excited
    rw [show w + a + b + 2 - 1 = w + a + b + 1 by omega, ← pow_mul, mul_comm (w + a + b + 2) 2,
      div_mul_cancel₀ _ (pow_ne_zero _ hc.ne')]
  have hσ0 : 0 ≤ excited μ k c φ (w + a + b + 2) := by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  rw [hσ, Real.sqrt_mul hσ0, Real.sqrt_sq (pow_nonneg hc.le _)] at h1
  have hM' : |c| ^ (w + a + b + 2) ≠ 0 := pow_ne_zero _ hc.ne'
  rw [htr, sqrt_thermRem, div_le_iff₀ (pow_pos hc _),
    show |c| ^ (w + w + (a + a + 2) + (b + b + 2)) = |c| ^ (w + a + b + 2) * |c| ^ (w + a + b + 2) by
      rw [← pow_add]; congr 1; omega]
  calc _ ≤ _ := h1
    _ = _ := by field_simp

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **The one-point excited trace below the cubic reflected moment**:

    |Tr(F R^{L−w})| / |c|^L ≤ √((1 + σ₀) E_L[f · θf]) · √σ₀,

with `L = 2w + (2a+2) + (2b+2)` and `σ₀ = excited (L/2)` (`abs_trOne_cubic_rem`,
`parts_le_moment`). Both factors are on the cubic torus of `L` steps.

DERIVED: `3` is `L − w − 1`; `1` the vacuum's own weight and the offset of `iter`; `2` the offsets
of `iter` and of the excited weight. -/
theorem abs_trOne_cubic (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    |trc μ (conv μ F (iter μ (rem k c φ) (w + a + a + b + b + 3)))|
        / |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      ≤ √((1 + excited μ k c φ (w + a + b + 2)) * torusMom μ k F a b (w + a + b + 1))
        * √(excited μ k c φ (w + a + b + 2)) :=
  (abs_trOne_cubic_rem (μ := μ) hφm hφb hkm hkb hc0 hF w a b).trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w a b).1)
      (Real.sqrt_nonneg _))

include hφm hφb hkm hkb in
/-- **The excited–excited trace by Cauchy–Schwarz at full length**: for `p = a_F + b_G + 1`,
`q = a_G + b_F + 1`,

    |Tr(F R^{p+1} G R^{q+1})| / |c|^{(w+a_F+b_F+2) + (w'+a_G+b_G+2)} ≤ √D(f) · √D(g),

`D(f) = thermRem F w a_F b_F`, `D(g) = thermRem G w' a_G b_G`. `R^{p+1} = R^{a_F+1} R^{b_G+1}`,
`R^{q+1} = R^{a_G+1} R^{b_F+1}`, cyclicity gives `Tr((R^{b_F+1} F R^{a_F+1})(R^{b_G+1} G R^{a_G+1}))`,
and `OpenAIBridgeRP.abs_trc_le`.

DERIVED: `1` and `2` are the offsets of `iter`. -/
theorem abs_trK_sand (hc0 : c ≠ 0) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {w w' : ℕ}
    (aF bF aG bG : ℕ) :
    |trK μ (rem k c φ) F G (aF + bG + 1) (aG + bF + 1)|
        / |c| ^ ((w + aF + bF + 2) + (w' + aG + bG + 2))
      ≤ √(thermRem μ k c φ F w aF bF) * √(thermRem μ k c φ G w' aG bG) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hAF : Bdd (iter μ (rem k c φ) aF) := hr.iter aF
  have hBF : Bdd (iter μ (rem k c φ) bF) := hr.iter bF
  have hAG : Bdd (iter μ (rem k c φ) aG) := hr.iter aG
  have hBG : Bdd (iter μ (rem k c φ) bG) := hr.iter bG
  have hU : Bdd (conv μ F (iter μ (rem k c φ) aF)) := hF.conv hAF
  have hV : Bdd (conv μ G (iter μ (rem k c φ) aG)) := hG.conv hAG
  have hUB : Bdd (conv μ (conv μ F (iter μ (rem k c φ) aF)) (iter μ (rem k c φ) bG)) :=
    hU.conv hBG
  have hUBV : Bdd (conv μ (conv μ (conv μ F (iter μ (rem k c φ) aF)) (iter μ (rem k c φ) bG))
      (conv μ G (iter μ (rem k c φ) aG))) := hUB.conv hV
  have hBV : Bdd (conv μ (iter μ (rem k c φ) bG) (conv μ G (iter μ (rem k c φ) aG))) :=
    hBG.conv hV
  have hP : Bdd (conv μ (iter μ (rem k c φ) bF) (conv μ F (iter μ (rem k c φ) aF))) :=
    hBF.conv hU
  have htr : trK μ (rem k c φ) F G (aF + bG + 1) (aG + bF + 1)
      = trc μ (conv μ (conv μ (iter μ (rem k c φ) bF) (conv μ F (iter μ (rem k c φ) aF)))
          (conv μ (iter μ (rem k c φ) bG) (conv μ G (iter μ (rem k c φ) aG)))) := by
    unfold trK
    rw [iter_add hr aF bG, iter_add hr aG bF, conv_assoc hF hAF hBG, conv_assoc hG hAG hBF,
      conv_assoc hUB hV hBF, trc_conv_comm hUBV hBF, ← conv_assoc hU hBG hV,
      conv_assoc hBF hU hBV]
  have h1 := abs_trc_le (μ := μ) hP hBV
  rw [htr, sqrt_thermRem, sqrt_thermRem, div_le_iff₀ (pow_pos hc _),
    pow_add |c| (w + aF + bF + 2) (w' + aG + bG + 2)]
  calc _ ≤ _ := h1
    _ = _ := by
        have h1' : |c| ^ (w + aF + bF + 2) ≠ 0 := pow_ne_zero _ hc.ne'
        have h2' : |c| ^ (w' + aG + bG + 2) ≠ 0 := pow_ne_zero _ hc.ne'
        field_simp

include hφm hφb hkm hkb in
/-- **The excited–excited trace on the cubic torus**: if `w + a_F + b_F + 1 = w' + a_G + b_G + 1 = m`,
so that both reflected moments live on the torus of `L = 2m + 2` steps that carries the
correlation (`p + q + 2 + w + w' = L` for `p = a_F + b_G + 1`, `q = a_G + b_F + 1`),

    |Tr(F R^{p+1} G R^{q+1})| / |c|^L ≤ √(D_L(f) D_L(g))

(`abs_trK_sand`). No decay factor survives: the bound is small only if the thermal remainders are.

DERIVED: `1` and `2` are the offsets of `iter`, so the torus has `2m + 2` steps. -/
theorem abs_trK_cubic (hc0 : c ≠ 0) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {w w' m : ℕ}
    (aF bF aG bG : ℕ) (hmF : w + aF + bF + 1 = m) (hmG : w' + aG + bG + 1 = m) :
    |trK μ (rem k c φ) F G (aF + bG + 1) (aG + bF + 1)| / |c| ^ (m + m + 2)
      ≤ √(thermRem μ k c φ F w aF bF * thermRem μ k c φ G w' aG bG) := by
  have h := abs_trK_sand (μ := μ) hφm hφb hkm hkb hc0 hF hG (w := w) (w' := w') aF bF aG bG
  rw [show (w + aF + bF + 2) + (w' + aG + bG + 2) = m + m + 2 by omega] at h
  rwa [Real.sqrt_mul (thermRem_nonneg _ _ _ _ _ _ _)]

/-! ## 2. The connected correlation on the cubic torus -/

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The connected correlation of two kernel insertions with the trace terms at full length.**
For bounded measurable `F`, `G` covering even `w`, `w'` steps, on the periodic chain of
`L = p + q + 2 + w + w' = 2m + 2` copies of `k` with `p = 2a + j + 2 = a_F + b_G + 1`,
`q = 2a + j' + 2 = a_G + b_F + 1` and `w + a_F + b_F + 1 = w' + a_G + b_G + 1 = m`,

    |connK μ k F G w w' p q|
      ≤ (1/2)^⌊(j+1)/n⌋ √(R_F R_{Gᵀ}) + (1/2)^⌊(j'+1)/n⌋ √(R_{Fᵀ} R_G) + √(D_L(f) D_L(g))
        + |α_F||α_G| σ₀ + |α_F| √D_L(g) √σ₀ + |α_G| √D_L(f) √σ₀ + √(D_L(f) D_L(g)) σ₀,

`σ₀ = excited (m + 1)` the excited weight of the torus. The cross terms are those of
`OpenAIBridgeRP.connK_rp_full` (`abs_cross_rp`); the excited–excited trace is `abs_trK_sand` and
the one-point excited traces are `abs_trOne_cubic_rem`, all on the torus of `L` steps;
`conn_alg4` assembles them. No sup bound and no cap on `σ₀` enters.

DERIVED: `1/2` is the contraction; `1` and `2` the offsets of `iter` and of the excited weight;
`0` the excluded eigenvalue. -/
theorem connK_rp_cubic_rem (hc0 : c ≠ 0) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {w w' : ℕ}
    (hw : Even w) (hw' : Even w') (a j j' : ℕ) {p q : ℕ} (hp : p = a + j + a + 2)
    (hq : q = a + j' + a + 2) {m : ℕ} (aF bF aG bG : ℕ) (hpF : p = aF + bG + 1)
    (hqF : q = aG + bF + 1) (hmF : w + aF + bF + 1 = m) (hmG : w' + aG + bG + 1 = m) :
    |connK μ k F G w w' p q|
      ≤ (1 / 2) ^ ((j + 1) / n) * √(OpenAIBridgeRP.refl μ k c φ F w a * OpenAIBridgeRP.refl μ k c φ (tp G) w' a)
        + (1 / 2) ^ ((j' + 1) / n) * √(OpenAIBridgeRP.refl μ k c φ (tp F) w a * OpenAIBridgeRP.refl μ k c φ G w' a)
        + √(thermRem μ k c φ F w aF bF * thermRem μ k c φ G w' aG bG)
        + (|vacRead μ c φ F w| * |vacRead μ c φ G w'| * excited μ k c φ (m + 1)
          + |vacRead μ c φ F w| * √(thermRem μ k c φ G w' aG bG) * √(excited μ k c φ (m + 1))
          + |vacRead μ c φ G w'| * √(thermRem μ k c φ F w aF bF) * √(excited μ k c φ (m + 1))
          + √(thermRem μ k c φ F w aF bF * thermRem μ k c φ G w' aG bG)
            * excited μ k c φ (m + 1)) := by
  obtain ⟨v, hv⟩ := hw
  obtain ⟨v', hv'⟩ := hw'
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcne : |c| ≠ 0 := hc.ne'
  have hcw : 0 < |c| ^ w := pow_pos hc w
  have hcw' : 0 < |c| ^ w' := pow_pos hc w'
  have hcwne : |c| ^ w ≠ 0 := hcw.ne'
  have hcwne' : |c| ^ w' ≠ 0 := hcw'.ne'
  have hcL : 0 < |c| ^ (p + q + w + w' + 2) := pow_pos hc _
  have hcLne : |c| ^ (p + q + w + w' + 2) ≠ 0 := hcL.ne'
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  have hσdef : ∀ j, hs μ (iter μ (rem k c φ) j)
      = excited μ k c φ (j + 1) * |c| ^ (2 * (j + 1)) := by
    intro j; unfold excited; rw [Nat.add_sub_cancel, div_mul_cancel₀ _ (pow_ne_zero _ hcne)]
  have hexc0 : ∀ j, 0 ≤ excited μ k c φ j := fun j => by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have hss : √(excited μ k c φ (m + 1)) * √(excited μ k c φ (m + 1)) = excited μ k c φ (m + 1) :=
    Real.mul_self_sqrt (hexc0 _)
  -- the partition function
  have hZ : trPow μ k (p + q + w + w' + 1)
      = |c| ^ (p + q + w + w' + 2) * (1 + excited μ k c φ (m + 1)) := by
    have hev : Even (m + m + 2) := ⟨m + 1, by ring⟩
    rw [show p + q + w + w' + 1 = m + m + 1 by omega, trPow_even hφm hφb hφ1 hkm hkb hsym heig m,
      hσdef m, ← hev.pow_abs c, show p + q + w + w' + 2 = m + m + 2 by omega,
      show 2 * (m + 1) = m + m + 2 by ring]
    ring
  -- the one-point traces
  have hOF : trOne μ k F (p + q + w' + 1) = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w
        + trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / |c| ^ (p + q + w + w' + 2)) := by
    have hev : Even (p + q + w' + 1 + 1) := ⟨m + 1 - v, by omega⟩
    have hΛF : |c| ^ (p + q + w + w' + 2) = |c| ^ (p + q + w' + 1 + 1) * |c| ^ w := by
      rw [← pow_add]; congr 1; omega
    rw [trOne_decomp hφm hφb hφ1 hkm hkb hsym heig hF, ← hev.pow_abs c, hΛF]
    field_simp
    try ring
  have hOG : trOne μ k G (p + q + w + 1) = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w'
        + trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / |c| ^ (p + q + w + w' + 2)) := by
    have hev : Even (p + q + w + 1 + 1) := ⟨m + 1 - v', by omega⟩
    have hΛG : |c| ^ (p + q + w + w' + 2) = |c| ^ (p + q + w + 1 + 1) * |c| ^ w' := by
      rw [← pow_add]; congr 1; omega
    rw [trOne_decomp hφm hφb hφ1 hkm hkb hsym heig hG, ← hev.pow_abs c, hΛG]
    field_simp
    try ring
  -- the two-point trace
  have hev2 : Even (p + 1 + (q + 1)) := ⟨m + 1 - v - v', by omega⟩
  have hcc : c ^ (p + 1) * c ^ (q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add, ← pow_add, hev2.pow_abs c]
  have hΛ2 : |c| ^ (p + q + w + w' + 2)
      = |c| ^ (p + 1) * |c| ^ (q + 1) * |c| ^ w * |c| ^ w' := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hT : trK μ k F G p q = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w
          * ((∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w')
        + (c ^ (p + 1) * (∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
            + c ^ (q + 1) * (∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2)) := by
    rw [trK_decomp hφm hφb hφ1 hkm hkb hsym heig hF hG p q, hcc, hΛ2]
    field_simp
    try ring
  -- the separated terms
  have hMp : |c ^ (q + 1) * (∫ x, kernelFun G μ φ x
        * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
        / |c| ^ (p + q + w + w' + 2)|
      ≤ (1 / 2) ^ ((j + 1) / n)
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1))
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1)) := by
    have h : |c ^ (q + 1) * (∫ x, kernelFun G μ φ x
          * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ (kernelFun (tp F) μ φ) x ∂μ)
          / |c| ^ (p + q + w + w' + 2)|
        ≤ (1 / 2) ^ ((j + 1) / n)
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1))
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1)) :=
      abs_cross_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 a j (by omega)
        (measurable_kf (μ := μ) (bdd_tp hF) hφm) (measurable_kf (μ := μ) hG hφm)
        (abs_kf_le (μ := μ) (fun x y => hCF y x) hφb) (abs_kf_le (μ := μ) hCG hφb)
    rw [← hp] at h
    exact h
  have hMq : |c ^ (p + 1) * (∫ x, kernelFun F μ φ x
        * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
        / |c| ^ (p + q + w + w' + 2)|
      ≤ (1 / 2) ^ ((j' + 1) / n)
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1))
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1)) := by
    have h : |c ^ (p + 1) * (∫ x, kernelFun F μ φ x
          * kernelFun (iter μ (rem k c φ) (a + j' + a + 2)) μ (kernelFun (tp G) μ φ) x ∂μ)
          / |c| ^ (p + q + w + w' + 2)|
        ≤ (1 / 2) ^ ((j' + 1) / n)
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1))
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1)) :=
      abs_cross_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 a j' (by omega)
        (measurable_kf (μ := μ) (bdd_tp hG) hφm) (measurable_kf (μ := μ) hF hφm)
        (abs_kf_le (μ := μ) (fun x y => hCG y x) hφb) (abs_kf_le (μ := μ) hCF hφb)
    rw [← hq] at h
    exact h
  -- the excited–excited trace
  have hTb : |trK μ (rem k c φ) F G p q| / |c| ^ (p + q + w + w' + 2)
      ≤ √(thermRem μ k c φ F w aF bF) * √(thermRem μ k c φ G w' aG bG) := by
    have h := abs_trK_sand (μ := μ) hφm hφb hkm hkb hc0 hF hG (w := w) (w' := w') aF bF aG bG
    rw [← hpF, ← hqF, show (w + aF + bF + 2) + (w' + aG + bG + 2) = p + q + w + w' + 2 by omega]
      at h
    exact h
  -- the one-point excited traces
  have hea : |trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / |c| ^ (p + q + w + w' + 2)|
      ≤ √(thermRem μ k c φ F w aF bF) * √(excited μ k c φ (m + 1)) := by
    have h := abs_trOne_cubic_rem (μ := μ) hφm hφb hkm hkb hc0 hF w aF bF
    rw [show w + aF + aF + bF + bF + 3 = p + q + w' + 1 by omega,
      show w + w + (aF + aF + 2) + (bF + bF + 2) = p + q + w + w' + 2 by omega,
      show w + aF + bF + 2 = m + 1 by omega] at h
    rw [abs_div, abs_of_pos hcL]
    exact h
  have heb : |trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / |c| ^ (p + q + w + w' + 2)|
      ≤ √(thermRem μ k c φ G w' aG bG) * √(excited μ k c φ (m + 1)) := by
    have h := abs_trOne_cubic_rem (μ := μ) hφm hφb hkm hkb hc0 hG w' aG bG
    rw [show w' + aG + aG + bG + bG + 3 = p + q + w + 1 by omega,
      show w' + w' + (aG + aG + 2) + (bG + bG + 2) = p + q + w + w' + 2 by omega,
      show w' + aG + bG + 2 = m + 1 by omega] at h
    rw [abs_div, abs_of_pos hcL]
    exact h
  -- assemble
  unfold connK vacRead
  rw [hT, hOF, hOG, hZ, Real.sqrt_mul (refl_nonneg _ _ _ _ _ _),
    Real.sqrt_mul (refl_nonneg _ _ _ _ _ _), Real.sqrt_mul (thermRem_nonneg _ _ _ _ _ _ _),
    sqrt_refl, sqrt_refl, sqrt_refl, sqrt_refl]
  refine (conn_alg4 hcL (hexc0 _)).trans ?_
  set Λ := |c| ^ (p + q + w + w' + 2) with hΛ
  set α := (∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w with hα
  set β := (∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w' with hβ
  set Xq := ∫ x, kernelFun F μ φ x
      * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ with hXq
  set Xp := ∫ x, kernelFun G μ φ x
      * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ with hXp
  set T := trK μ (rem k c φ) F G p q with hTdef
  set ea := trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / Λ with hea'
  set eb := trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / Λ with heb'
  set s := √(excited μ k c φ (m + 1)) with hs'
  set σ0 := excited μ k c φ (m + 1) with hσ0'
  set dF := √(thermRem μ k c φ F w aF bF) with hdF
  set dG := √(thermRem μ k c φ G w' aG bG) with hdG
  set rF := √(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1) with hrF
  set rTG := √(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1)
    with hrTG
  set rTF := √(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1)
    with hrTF
  set rG := √(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1) with hrG
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hF0 : 0 ≤ dF := Real.sqrt_nonneg _
  have hG0 : 0 ≤ dG := Real.sqrt_nonneg _
  have he : |(c ^ (p + 1) * Xq + c ^ (q + 1) * Xp + T) / Λ|
      ≤ |c ^ (p + 1) * Xq / Λ| + |c ^ (q + 1) * Xp / Λ| + |T| / Λ := by
    rw [add_div, add_div]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_div T, abs_of_pos hcL]
  have P2 : |α| * |eb| ≤ |α| * (dG * s) := mul_le_mul_of_nonneg_left heb (abs_nonneg _)
  have P3 : |β| * |ea| ≤ |β| * (dF * s) := mul_le_mul_of_nonneg_left hea (abs_nonneg _)
  have P4 : |ea| * |eb| ≤ dF * dG * σ0 := by
    calc |ea| * |eb| ≤ (dF * s) * (dG * s) :=
          mul_le_mul hea heb (abs_nonneg _) (mul_nonneg hF0 hs0)
      _ = dF * dG * (s * s) := by ring
      _ = dF * dG * σ0 := by rw [hss]
  have key : |(c ^ (p + 1) * Xq + c ^ (q + 1) * Xp + T) / Λ| + |α| * |β| * σ0 + |α| * |eb|
        + |β| * |ea| + |ea| * |eb|
      ≤ (1 / 2) ^ ((j' + 1) / n) * rTF * rG + (1 / 2) ^ ((j + 1) / n) * rTG * rF
        + dF * dG + |α| * |β| * σ0 + |α| * (dG * s) + |β| * (dF * s) + dF * dG * σ0 := by
    linarith
  refine key.trans (le_of_eq ?_)
  ring

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The connected correlation of two kernel insertions bounded by cubic-torus moments.** Under
the hypotheses of `connK_rp_cubic_rem`, and with `c_F`, `c_G` such that `w + a + c_F + 1 = m` and
`w' + a + c_G + 1 = m`, write `𝓜(X; a, b) = (1 + σ₀) E_L[x · θx]` for the reflected moment of an
insertion `X` on the torus of `L = 2m + 2` steps (`torusMom`, `σ₀ = excited (m + 1)`). Then

    |connK μ k F G w w' p q|
      ≤ (1/2)^⌊(j+1)/n⌋ √(𝓜(F; a, c_F) 𝓜(Gᵀ; a, c_G)) + (1/2)^⌊(j'+1)/n⌋ √(𝓜(Fᵀ; a, c_F) 𝓜(G; a, c_G))
        + √(D_L(f) D_L(g)) + 2 √(𝓜(F; a_F, b_F) 𝓜(G; a_G, b_G)) (σ₀ + √σ₀).

Every reading of `connK_rp_cubic_rem` is below its moment (`parts_le_moment`, through
`OpenAIBridgeRP.reflMoment_le_torus_ratio`), so every constant is a moment of `F`, `Fᵀ`, `G`, `Gᵀ`
on the cubic torus, apart from the thermal remainders `D_L`.

DERIVED: `1/2` is the contraction; `2` counts the two cross pairs of the one-point terms; `1` the
vacuum's own weight and the offsets of `iter`; `0` the excluded eigenvalue. -/
theorem connK_rp_cubic (hc0 : c ≠ 0) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {w w' : ℕ}
    (hw : Even w) (hw' : Even w') (a j j' : ℕ) {p q : ℕ} (hp : p = a + j + a + 2)
    (hq : q = a + j' + a + 2) {m : ℕ} (aF bF aG bG cF cG : ℕ) (hpF : p = aF + bG + 1)
    (hqF : q = aG + bF + 1) (hmF : w + aF + bF + 1 = m) (hmG : w' + aG + bG + 1 = m)
    (hcF : w + a + cF + 1 = m) (hcG : w' + a + cG + 1 = m) :
    |connK μ k F G w w' p q|
      ≤ (1 / 2) ^ ((j + 1) / n) * √((1 + excited μ k c φ (m + 1)) * torusMom μ k F a cF m
            * ((1 + excited μ k c φ (m + 1)) * torusMom μ k (tp G) a cG m))
        + (1 / 2) ^ ((j' + 1) / n) * √((1 + excited μ k c φ (m + 1)) * torusMom μ k (tp F) a cF m
            * ((1 + excited μ k c φ (m + 1)) * torusMom μ k G a cG m))
        + √(thermRem μ k c φ F w aF bF * thermRem μ k c φ G w' aG bG)
        + 2 * √((1 + excited μ k c φ (m + 1)) * torusMom μ k F aF bF m
            * ((1 + excited μ k c φ (m + 1)) * torusMom μ k G aG bG m))
          * (excited μ k c φ (m + 1) + √(excited μ k c φ (m + 1))) := by
  have h := connK_rp_cubic_rem hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF hG hw hw'
    a j j' hp hq aF bF aG bG hpF hqF hmF hmG
  have pF := parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w aF bF
  have pG := parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hG w' aG bG
  have r1 := (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hF w a cF).2.2
  have r2 := (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 (bdd_tp hG) w' a cG).2.2
  have r3 := (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 (bdd_tp hF) w a cF).2.2
  have r4 := (parts_le_moment hφm hφb hφ1 hkm hkb hsym heig hc0 hG w' a cG).2.2
  rw [show w + aF + bF + 2 = m + 1 by omega, hmF] at pF
  rw [show w' + aG + bG + 2 = m + 1 by omega, hmG] at pG
  rw [show w + a + cF + 2 = m + 1 by omega, hcF] at r1 r3
  rw [show w' + a + cG + 2 = m + 1 by omega, hcG] at r2 r4
  obtain ⟨dF1, aF1, -⟩ := pF
  obtain ⟨dG1, aG1, -⟩ := pG
  have hexc0 : 0 ≤ excited μ k c φ (m + 1) := by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  set σ := excited μ k c φ (m + 1) with hσ
  set MF := (1 + σ) * torusMom μ k F aF bF m with hMF
  set MG := (1 + σ) * torusMom μ k G aG bG m with hMG
  have hMF0 : 0 ≤ MF := (sq_nonneg _).trans aF1
  have hMG0 : 0 ≤ MG := (sq_nonneg _).trans aG1
  have hX1 : √(OpenAIBridgeRP.refl μ k c φ F w a * OpenAIBridgeRP.refl μ k c φ (tp G) w' a)
      ≤ √((1 + σ) * torusMom μ k F a cF m * ((1 + σ) * torusMom μ k (tp G) a cG m)) :=
    Real.sqrt_le_sqrt (mul_le_mul r1 r2 (refl_nonneg _ _ _ _ _ _)
      ((refl_nonneg _ _ _ _ _ _).trans r1))
  have hX2 : √(OpenAIBridgeRP.refl μ k c φ (tp F) w a * OpenAIBridgeRP.refl μ k c φ G w' a)
      ≤ √((1 + σ) * torusMom μ k (tp F) a cF m * ((1 + σ) * torusMom μ k G a cG m)) :=
    Real.sqrt_le_sqrt (mul_le_mul r3 r4 (refl_nonneg _ _ _ _ _ _)
      ((refl_nonneg _ _ _ _ _ _).trans r3))
  have c1 := mul_le_mul_of_nonneg_left hX1 (by positivity : (0 : ℝ) ≤ (1 / 2) ^ ((j + 1) / n))
  have c2 := mul_le_mul_of_nonneg_left hX2 (by positivity : (0 : ℝ) ≤ (1 / 2) ^ ((j' + 1) / n))
  have hA : |vacRead μ c φ F w| ≤ √MF := Real.abs_le_sqrt aF1
  have hB : |vacRead μ c φ G w'| ≤ √MG := Real.abs_le_sqrt aG1
  have hdF : √(thermRem μ k c φ F w aF bF) ≤ √MF := Real.sqrt_le_sqrt dF1
  have hdG : √(thermRem μ k c φ G w' aG bG) ≤ √MG := Real.sqrt_le_sqrt dG1
  have hm : √(MF * MG) = √MF * √MG := Real.sqrt_mul hMF0 _
  have ht : √(thermRem μ k c φ F w aF bF * thermRem μ k c φ G w' aG bG)
      = √(thermRem μ k c φ F w aF bF) * √(thermRem μ k c φ G w' aG bG) :=
    Real.sqrt_mul (thermRem_nonneg _ _ _ _ _ _ _) _
  have hs0 : 0 ≤ √σ := Real.sqrt_nonneg _
  have b1 : |vacRead μ c φ F w| * |vacRead μ c φ G w'| * σ ≤ √MF * √MG * σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hA hB (abs_nonneg _) (Real.sqrt_nonneg _)) hexc0
  have b2 : |vacRead μ c φ F w| * √(thermRem μ k c φ G w' aG bG) * √σ ≤ √MF * √MG * √σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hA hdG (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hs0
  have b3 : |vacRead μ c φ G w'| * √(thermRem μ k c φ F w aF bF) * √σ ≤ √MG * √MF * √σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hB hdF (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hs0
  have b4 : √(thermRem μ k c φ F w aF bF * thermRem μ k c φ G w' aG bG) * σ
      ≤ √MF * √MG * σ := by
    rw [ht]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hdF hdG (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      hexc0
  refine h.trans ?_
  rw [hm]
  linarith

end Cubic

/-! ## 3. On the Wilson torus of every gauge group -/

section Reflect

open HiddenChain

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Y]

/-- **The reflected slab observable is measurable** when the observable and the map `ι` of the
hidden variables are.

DERIVED: no numeral appears in the statement. -/
theorem measurable_revG {ι : Y → Y} (hι : Measurable ι) (m : ℕ) {f : (ℕ → X) → (ℕ → Y) → ℝ}
    (hfm : Measurable (fun r : (ℕ → X) × (ℕ → Y) => f r.1 r.2)) :
    Measurable (fun r : (ℕ → X) × (ℕ → Y) => revG ι m f r.1 r.2) := by
  have h1 : Measurable (fun r : (ℕ → X) × (ℕ → Y) => fun i => r.1 (m + 1 - i)) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply (m + 1 - i)).comp measurable_fst
  have h2 : Measurable (fun r : (ℕ → X) × (ℕ → Y) =>
      fun i => if i ≤ m then ι (r.2 (m - i)) else Classical.arbitrary Y) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ≤ m
    · simp only [h, ↓reduceIte]; exact hι.comp ((measurable_pi_apply (m - i)).comp measurable_snd)
    · simp only [h, ↓reduceIte]; exact measurable_const
  exact hfm.comp (h1.prodMk h2)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The reflected slab observable has the sup bound of the observable.

DERIVED: no numeral appears in the statement. -/
theorem abs_revG_le (ι : Y → Y) (m : ℕ) {f : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ}
    (hfb : ∀ V A, |f V A| ≤ B) : ∀ V A, |revG ι m f V A| ≤ B :=
  fun _ _ => hfb _ _

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- **The reflected slab observable reads the same slab**: if `f` reads the slices `0, …, m + 1`
and the hidden variables `0, …, m`, so does `revG ι m f`.

DERIVED: `1` is the offset of the number of steps. -/
theorem localUpTo_revG (ι : Y → Y) (m : ℕ) {f : (ℕ → X) → (ℕ → Y) → ℝ}
    (hf : LocalUpTo (m + 1) f) : LocalUpTo (m + 1) (revG ι m f) := by
  intro V V' A A' hV hA
  show f _ _ = f _ _
  apply hf
  · intro i hi
    show V (m + 1 - i) = V' (m + 1 - i)
    exact hV (m + 1 - i) (by omega)
  · intro i hi
    have h1 : i ≤ m := by omega
    show (if i ≤ m then ι (A (m - i)) else Classical.arbitrary Y)
      = (if i ≤ m then ι (A' (m - i)) else Classical.arbitrary Y)
    rw [if_pos h1, if_pos h1, hA (m - i) (by omega)]

end Reflect

section WilsonCubicG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingWilson MassGap.DoublingWilsonG MassGap.GaugeGroup
  MassGap.OpenAIBridgeSides MassGap.OpenAIBridgeGroups

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The torus expectation of two slab observables is the trace ratio of their slab kernels**: on
the cubic torus of `G` of side `M + 1 = (m + 1) + (p + 1) + (m' + 1) + (q + 1)`,
`⟨f_0 g_{m+1+(p+1)}⟩ = Tr(F̂ K^{p+1} Ĝ K^{q+1}) / Tr K^{M+1}`
(`OpenAIBridgeSlab.corrNum_slabKG`, `OpenAIBridgeGroups.ZRG_eq_trPowG`).

DERIVED: `0` is the time direction and the first slice; `1` the offsets of the widths and of
`iter`. -/
theorem expect_pair_eqG {β : ℝ} (hβ : 0 ≤ β) {M m m' p q : ℕ}
    (hM : M = m + 1 + (p + 1) + (m' + 1 + q))
    {f g : (ℕ → TorusChainG.SlG G M) → (ℕ → TorusChainG.AxG G M) → ℝ}
    (hfm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      g r.1 r.2))
    {Bf Bg : ℝ} (hfb : ∀ V A, |f V A| ≤ Bf) (hgb : ∀ V A, |g V A| ≤ Bg)
    (hf : LocalUpTo (m + 1) f) (hg : LocalUpTo (m' + 1) g) :
    (sysRG G (TorusChain.Lc M)).expect (probHaar G) β
        (fun U => f (slabV (TorusChain.Lc M) 0 0 U) (slabA (TorusChain.Lc M) 0 0 U)
          * g (slabV (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U)
            (slabA (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U))
      = trK (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β)
          (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
            (TorusChainG.wtG G M β) m f)
          (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
            (TorusChainG.wtG G M β) m' g) p q
        / trPow (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) M := by
  have h2 := corrNum_slabKG hβ hM hfm hgm hfb hgb hf hg
  have hZ : (sysRG G (TorusChain.Lc M)).partition (probHaar G) β
      = trPow (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) M :=
    ZRG_eq_trPowG G hβ _ _ rfl
  unfold LatticeGauge.System.expect
  rw [h2, hZ]

variable {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
/-- **The connected correlation of two slab observables on the Wilson torus of every gauge group,
bounded by torus moments of the observables and their reflections, from the seed.** If one torus
of even side `n ≥ 2` has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic
torus of `G` of every side `L = 2l + 2 ≥ 8n` there are a normalized eigenfunction `φ` of `kTG` and
its eigenvalue `c ≠ 0` with excited weight `σ₀ = excited (l + 1) ≤ (1/2)^⌊(l+1)/n⌋`, such that for
bounded measurable slab observables `f`, `g` of widths `w = 2v + 2`, `w' = 2v' + 2`, read at times
`0` and `w + p + 1`, `p = 2a + j + 2 = a_F + b_G + 1`, `q = 2a + j' + 2 = a_G + b_F + 1`, with
`w + a_F + b_F + 1 = w' + a_G + b_G + 1 = w + a + c_F + 1 = w' + a + c_G + 1 = l`,

    |⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩|
      ≤ (1/2)^⌊(j+1)/n⌋ √((1+σ₀)⟨f_0 (θf)_{w+2a+2}⟩ · (1+σ₀)⟨(θg)_0 g_{w'+2a+2}⟩)
        + (1/2)^⌊(j'+1)/n⌋ √((1+σ₀)⟨(θf)_0 f_{w+2a+2}⟩ · (1+σ₀)⟨g_0 (θg)_{w'+2a+2}⟩)
        + √(D_L(f) D_L(g))
        + 2 √((1+σ₀)⟨f_0 (θf)_{w+2a_F+2}⟩ · (1+σ₀)⟨g_0 (θg)_{w'+2a_G+2}⟩) (σ₀ + √σ₀).

`θf = revG (·)⁻¹ f` is the observable of the reflected slab, every `⟨·⟩` is the Wilson
expectation on the same cubic torus, and `D_L = thermRem` of the slab kernels. The sup bounds of
`f`, `g` do not enter. `gap_side_excitedG`, `excited_le_slab`, `connK_rp_cubic`,
`OpenAIBridgeRP.slabKer_rev_wtG`, `expect_pair_eqG`, `OpenAIBridgeSlab.connK_eq_expect_slabG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `8` the slab condition of
`excited_le_slab` with no slab, and `4` the spacetime dimension; `1/2` the contraction; `2` the
doubled side, the doubled widths and separations, the offsets of `iter` and the two cross pairs of
the one-point terms; `0` the time direction, the first slice and the sign of the coupling; `1` the
offsets of `iter`, the separation, the unit norm and the vacuum's own weight. -/
theorem wilson_slab_conn_cubicG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (l : ℕ) (hL : 8 * n ≤ l + l + 2) :
    ∃ φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → G) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG G 0 (TorusChain.Tc (l + l + 1))) = 1 ∧
      (∀ z, ∫ y, (kTG G 0 (TorusChain.Tc (l + l + 1)) β) z y * φ y
        ∂(hSG G 0 (TorusChain.Tc (l + l + 1))) = c * φ z) ∧
      excited (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ
        (l + 1) ≤ (1 / 2) ^ ((l + 1) / n) ∧
      ∀ (f g : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → G)
          → (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → G) → ℝ),
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → G)
        × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → G) => f r.1 r.2) →
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → G)
        × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → G) => g r.1 r.2) →
      ∀ A B : ℝ, (∀ V A', |f V A'| ≤ A) → (∀ V A', |g V A'| ≤ B) → ∀ v v' : ℕ,
      LocalUpTo (v + v + 2) f → LocalUpTo (v' + v' + 2) g →
      ∀ a j j' aF bF aG bG cF cG : ℕ,
      a + j + a + 2 = aF + bG + 1 → a + j' + a + 2 = aG + bF + 1 →
      v + v + 2 + aF + bF + 1 = l → v' + v' + 2 + aG + bG + 1 = l →
      v + v + 2 + a + cF + 1 = l → v' + v' + 2 + a + cG + 1 = l →
      |(sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
          (fun U => f (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
              (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
            * g (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))
        - (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
            (fun U => f (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
              (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U))
          * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
            (fun U => g (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))|
        ≤ (1 / 2) ^ ((j + 1) / n)
            * √((1 + excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))
                  * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
                    (fun U => f (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                      * revG (MeasurableEquiv.piCongrRight
                          (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G))
                          (v + v + 1) f
                        (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + a + 2)) U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + a + 2)) U))
                * ((1 + excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))
                  * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
                    (fun U => revG (MeasurableEquiv.piCongrRight
                          (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G))
                          (v' + v' + 1) g
                        (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                      * g (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v' + v' + 2 + (a + a + 2)) U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v' + v' + 2 + (a + a + 2)) U))))
          + (1 / 2) ^ ((j' + 1) / n)
            * √((1 + excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))
                  * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
                    (fun U => revG (MeasurableEquiv.piCongrRight
                          (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G))
                          (v + v + 1) f
                        (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                      * f (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + a + 2)) U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (a + a + 2)) U))
                * ((1 + excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))
                  * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
                    (fun U => g (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                      * revG (MeasurableEquiv.piCongrRight
                          (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G))
                          (v' + v' + 1) g
                        (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v' + v' + 2 + (a + a + 2)) U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v' + v' + 2 + (a + a + 2)) U))))
          + √(thermRem (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
                c φ (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
                  (TorusChainG.wtG G (l + l + 1) β) (v + v + 1) f) (v + v + 2) aF bF
              * thermRem (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
                c φ (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
                  (TorusChainG.wtG G (l + l + 1) β) (v' + v' + 1) g) (v' + v' + 2) aG bG)
          + 2 * √((1 + excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))
                  * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
                    (fun U => f (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                      * revG (MeasurableEquiv.piCongrRight
                          (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G))
                          (v + v + 1) f
                        (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (aF + aF + 2)) U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v + v + 2 + (aF + aF + 2)) U))
                * ((1 + excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))
                  * (sysRG G (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar G) β
                    (fun U => g (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 0 U)
                      * revG (MeasurableEquiv.piCongrRight
                          (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G))
                          (v' + v' + 1) g
                        (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 (v' + v' + 2 + (aG + aG + 2)) U)
                        (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 (v' + v' + 2 + (aG + aG + 2)) U))))
              * (excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1)
                + √(excited (hSG G 0 (TorusChain.Tc (l + l + 1)))
                    (kTG G 0 (TorusChain.Tc (l + l + 1)) β) c φ (l + 1))) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) (by omega : 2 * n ≤ l + l + 1 + 1)
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    gap_side_excitedG hβ hn he h0 a' (l + l + 1 + 1) ⟨l + 1, by ring⟩ hlo hhi
  have hσ := excited_le_slab hφm hφb hφ1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (kTG_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc
    (ℓ := l + 1) (W := 0) (by omega) (by omega)
  refine ⟨φ, c, hc0, hφ1, heig, hσ,
    fun f g hfm hgm A B hfb hgb v v' hf hg a j j' aF bF aG bG cF cG hpF hqF hmF hmG hcF hcG => ?_⟩
  have hw := TorusChainG.wmeas_wtG (G := G) (M := l + l + 1) β
  have hwb := TorusChainG.abs_wtG_le (G := G) (M := l + l + 1) hβ
  have hι : Measurable (MeasurableEquiv.piCongrRight
      (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv G)) :=
    (MeasurableEquiv.piCongrRight _).measurable
  have hf1 : LocalUpTo (v + v + 1 + 1) f := hf.mono (by omega)
  have hg1 : LocalUpTo (v' + v' + 1 + 1) g := hg.mono (by omega)
  have h := connK_rp_cubic hφm hφb hφ1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (kTG_symm β) heig hc hgap hc0
    (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc (l + l + 1)))
      (ν := hAG G 0 (TorusChain.Tc (l + l + 1))) hw hwb (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc (l + l + 1)))
      (ν := hAG G 0 (TorusChain.Tc (l + l + 1))) hw hwb (v' + v' + 1) hgm hgb)
    (w := v + v + 2) (w' := v' + v' + 2) ⟨v + 1, by ring⟩ ⟨v' + 1, by ring⟩ a j j'
    (p := a + j + a + 2) (q := a + j' + a + 2) rfl rfl aF bF aG bG cF cG hpF hqF hmF hmG hcF hcG
  -- the moments are torus expectations
  have E1 := expect_pair_eqG hβ (M := l + l + 1) (m := v + v + 1) (m' := v + v + 1)
    (p := a + a + 1) (q := cF + cF + 1) (by omega) hfm (measurable_revG hι (v + v + 1) hfm)
    hfb (abs_revG_le _ (v + v + 1) hfb) hf1 (localUpTo_revG _ (v + v + 1) hf1)
  have E2 := expect_pair_eqG hβ (M := l + l + 1) (m := v' + v' + 1) (m' := v' + v' + 1)
    (p := a + a + 1) (q := cG + cG + 1) (by omega) (measurable_revG hι (v' + v' + 1) hgm) hgm
    (abs_revG_le _ (v' + v' + 1) hgb) hgb (localUpTo_revG _ (v' + v' + 1) hg1) hg1
  have E3 := expect_pair_eqG hβ (M := l + l + 1) (m := v + v + 1) (m' := v + v + 1)
    (p := a + a + 1) (q := cF + cF + 1) (by omega) (measurable_revG hι (v + v + 1) hfm) hfm
    (abs_revG_le _ (v + v + 1) hfb) hfb (localUpTo_revG _ (v + v + 1) hf1) hf1
  have E4 := expect_pair_eqG hβ (M := l + l + 1) (m := v' + v' + 1) (m' := v' + v' + 1)
    (p := a + a + 1) (q := cG + cG + 1) (by omega) hgm (measurable_revG hι (v' + v' + 1) hgm)
    hgb (abs_revG_le _ (v' + v' + 1) hgb) hg1 (localUpTo_revG _ (v' + v' + 1) hg1)
  have E5 := expect_pair_eqG hβ (M := l + l + 1) (m := v + v + 1) (m' := v + v + 1)
    (p := aF + aF + 1) (q := bF + bF + 1) (by omega) hfm (measurable_revG hι (v + v + 1) hfm)
    hfb (abs_revG_le _ (v + v + 1) hfb) hf1 (localUpTo_revG _ (v + v + 1) hf1)
  have E6 := expect_pair_eqG hβ (M := l + l + 1) (m := v' + v' + 1) (m' := v' + v' + 1)
    (p := aG + aG + 1) (q := bG + bG + 1) (by omega) hgm (measurable_revG hι (v' + v' + 1) hgm)
    hgb (abs_revG_le _ (v' + v' + 1) hgb) hg1 (localUpTo_revG _ (v' + v' + 1) hg1)
  rw [slabKer_rev_wtG hβ (v + v + 1) hfm hfb] at E1 E3 E5
  rw [slabKer_rev_wtG hβ (v' + v' + 1) hgm hgb] at E2 E4 E6
  rw [show v + v + 1 + 1 + (a + a + 1 + 1) = v + v + 2 + (a + a + 2) by omega] at E1 E3
  rw [show v' + v' + 1 + 1 + (a + a + 1 + 1) = v' + v' + 2 + (a + a + 2) by omega] at E2 E4
  rw [show v + v + 1 + 1 + (aF + aF + 1 + 1) = v + v + 2 + (aF + aF + 2) by omega] at E5
  rw [show v' + v' + 1 + 1 + (aG + aG + 1 + 1) = v' + v' + 2 + (aG + aG + 2) by omega] at E6
  have e1 : torusMom (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
      (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
        (TorusChainG.wtG G (l + l + 1) β) (v + v + 1) f) a cF l = _ := E1.symm
  have e2 : torusMom (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
      (tp (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
        (TorusChainG.wtG G (l + l + 1) β) (v' + v' + 1) g)) a cG l = _ := E2.symm
  have e3 : torusMom (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
      (tp (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
        (TorusChainG.wtG G (l + l + 1) β) (v + v + 1) f)) a cF l = _ := E3.symm
  have e4 : torusMom (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
      (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
        (TorusChainG.wtG G (l + l + 1) β) (v' + v' + 1) g) a cG l = _ := E4.symm
  have e5 : torusMom (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
      (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
        (TorusChainG.wtG G (l + l + 1) β) (v + v + 1) f) aF bF l = _ := E5.symm
  have e6 : torusMom (hSG G 0 (TorusChain.Tc (l + l + 1))) (kTG G 0 (TorusChain.Tc (l + l + 1)) β)
      (slabKer (hSG G 0 (TorusChain.Tc (l + l + 1))) (hAG G 0 (TorusChain.Tc (l + l + 1)))
        (TorusChainG.wtG G (l + l + 1) β) (v' + v' + 1) g) aG bG l = _ := E6.symm
  rw [e1, e2, e3, e4, e5, e6] at h
  have heq := connK_eq_expect_slabG hβ (M := l + l + 1) (m := v + v + 1) (m' := v' + v' + 1)
    (p := a + j + a + 2) (q := a + j' + a + 2) (by omega) hfm hgm hfb hgb hf1 hg1
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end WilsonCubicG

/-! ## 4. The input that remains -/

section Remaining

/-- **The thermal remainders vanish along the family order** — the input that the cubic bound
leaves. For a token group and a test, `D p N` is the thermal remainder `thermRem` of the slab
kernel of the smeared insertion at volume index `p` and spacing index `N`, read on the cubic torus
of that volume (`connK_rp_cubic`); the order is the order of the uniform-decay target: first the
spacing (`∀ᶠ N`), then the volume (`∀ᶠ p`). The predicate says `D` is eventually below every
`ε > 0` in that order.

It is not provided here. It is an infinite-volume statement without a rate: the finite-volume
transfer gap gives no bound on `D` that is uniform in the volume without the sup bound of the
insertion, which diverges in the spacing limit. And `D` is a transfer object (`D_L(f) = (1+σ₀)
E_L[f · θf] − α_F² − R_F − R_{Fᵀ}`, `thermRem_eq_moment`) whose reflected readings are infinite-time
limits at a fixed spatial side, so it is not a quantity of the published family.

DERIVED: `0` is the limit the remainders tend to. -/
def ThermalRemainderVanishes (D : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, ∀ᶠ N in atTop, D p N ≤ ε

/-- **The excited–excited term of the cubic bound vanishes with the thermal remainders**: if
`D_f` and `D_g ≥ 0` satisfy `ThermalRemainderVanishes`, so does `√(D_f D_g)`, the term that
`abs_trK_cubic` leaves in `connK_rp_cubic`.

DERIVED: `0` is the sign of `D_g` and the limit. -/
theorem sqrt_mul_vanishes {Df Dg : ℕ → ℕ → ℝ} (hg0 : ∀ p N, 0 ≤ Dg p N)
    (hf : ThermalRemainderVanishes Df) (hg : ThermalRemainderVanishes Dg) :
    ThermalRemainderVanishes (fun p N => √(Df p N * Dg p N)) := by
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with p hp hq
  filter_upwards [hp, hq] with N h1 h2
  calc √(Df p N * Dg p N) ≤ √(ε * ε) :=
        Real.sqrt_le_sqrt (mul_le_mul h1 h2 (hg0 p N) hε.le)
    _ = ε := Real.sqrt_mul_self hε.le

end Remaining

end MassGap.OpenAIBridgeCubic

#print axioms MassGap.OpenAIBridgeCubic.thermRem_nonneg
#print axioms MassGap.OpenAIBridgeCubic.sqrt_thermRem
#print axioms MassGap.OpenAIBridgeCubic.reflMoment_decomp
#print axioms MassGap.OpenAIBridgeCubic.moment_ratio
#print axioms MassGap.OpenAIBridgeCubic.thermRem_eq_moment
#print axioms MassGap.OpenAIBridgeCubic.parts_le_moment
#print axioms MassGap.OpenAIBridgeCubic.abs_trOne_cubic_rem
#print axioms MassGap.OpenAIBridgeCubic.abs_trOne_cubic
#print axioms MassGap.OpenAIBridgeCubic.abs_trK_sand
#print axioms MassGap.OpenAIBridgeCubic.abs_trK_cubic
#print axioms MassGap.OpenAIBridgeCubic.connK_rp_cubic_rem
#print axioms MassGap.OpenAIBridgeCubic.connK_rp_cubic
#print axioms MassGap.OpenAIBridgeCubic.measurable_revG
#print axioms MassGap.OpenAIBridgeCubic.abs_revG_le
#print axioms MassGap.OpenAIBridgeCubic.localUpTo_revG
#print axioms MassGap.OpenAIBridgeCubic.expect_pair_eqG
#print axioms MassGap.OpenAIBridgeCubic.wilson_slab_conn_cubicG
#print axioms MassGap.OpenAIBridgeCubic.sqrt_mul_vanishes
