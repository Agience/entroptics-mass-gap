import Mathlib

/-!
# MassGap.OpenAIBridgeLimits — two abstract steps from Theorem 4.46 to the OpenAI continuum theory

Theorem 4.46 (`OpenAIDictionary.familyGap_of_seed`) gives a transfer gap on every torus of the
OpenAI Yang–Mills lattice family, uniform in the spacing and the volume. Section 4.8 of the paper
names two steps that carry it to their continuum theory; this module states and proves both in the
abstract form in which the OpenAI submission `yang-mills-group/OpenAI-YM-20261028` (Lean 4.32, not
importable here at Lean 4.31) states the objects they act on. Each hypothesis is shaped like the
field of their structure `Reconstructed` (`ChallengeSpec.lean:117`) that supplies it.

## 1. The identification of the components (the group's §6.2)

Their phase space is a compact metric space with its Borel structure (`ChallengeSpec.lean:34–38`)
carrying a measure `phaseMeasure` (`ChallengeSpec.lean:39`) that is a probability measure
(`normalized`, `ChallengeSpec.lean:124`) of full support (`fullSupport`, `ChallengeSpec.lean:125`).
The correlation `correlation : Option Character → … → ℂ` (`ChallengeSpec.lean:41`) reads a component
theory at `some ξ` and the mixed theory at `none`; each component value is continuous in the phase
(`characterContinuity`, `ChallengeSpec.lean:131`) and the mixed value is their average (`mixture`,
`ChallengeSpec.lean:133`). Here an observable — their label tuple together with its separated
insertion points — is an element of an abstract label type `ι`.

The group's assessment (`YM` at `55ba9fc`, release companion §6.2) argues: if the mixed theory
clusters, a short calculation gives `∫ |S_ξ(A) − S_mix(A)|² dν = 0`, and continuity and full support
identify every component. The steps proved here:

* `eq_of_integral_norm_sub_sq_eq_zero`: a continuous function on a compact space whose mean-square
  distance from `m` vanishes, against a finite measure of full support, equals `m` everywhere.
* `eq_of_integral_mul_conj` (complex, their value type) and `eq_of_integral_sq` (real): the second
  moment equal to the square of the mean, with the mean equal to `m`, gives the variance zero, so
  the function is constant.
* `integral_mul_eq_of_clusters`: the short calculation. Each component clusters on the translated
  product `A · τ_t B`, the mixed value of that product is the average of the component values, the
  component values are bounded uniformly, and the mixed theory clusters; dominated convergence then
  gives `∫ S_ξ(A) S_ξ(B) dν = S_mix(A) S_mix(B)`.
* `component_eq_mixture` (from the product moment, with a field conjugation on the labels) and
  `component_eq_mixture_of_clusters` (from clustering itself): every component equals the mixture on
  every observable.

## 2. A uniform bound through iterated limits

Their limit is taken first in the spacing at fixed physical volume, then in the volume along a
subsequence. `norm_le_of_iterated_limits` lets the first limit run along a filter `l₁ p` that may
depend on the volume index `p` (a subsequence chosen per volume), the second along any filter `l₂`,
and asks the bound only eventually in both. `norm_le_of_iterated_subsequences` is the sequence form
with subsequences `φ p` in the spacing and `ψ` in the volume, and a bound for all large spacing
indices and all volumes, the form in which Theorem 4.46 delivers it.
`norm_le_exp_of_iterated_limits` and `norm_le_exp_of_iterated_subsequences` are the exponential forms
`‖c m p τ‖ ≤ C e^{−μτ}`, which pass to `‖L τ‖ ≤ C e^{−μτ}` at every separation `τ` in a set `T`.

## Scope

Nothing here proves that their connected correlations obey a bound of this shape, that their limits
exist along the stated filters, or that clustering of the mixed theory follows from the bound: those
are the open link of section 4.8 (section 1.5, item 7), not formalized. The statements are about functions on a compact space and families of numbers.
-/

namespace MassGap.OpenAIBridgeLimits

open MeasureTheory Filter Topology
open scoped ComplexConjugate

/-! ## 1. The identification of the components -/

section Identification

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X}

/-- A continuous function on a compact space is integrable against a finite measure. Their phase
space is compact (`characterCompact`, `ChallengeSpec.lean:38`) and their phase measure is a
probability measure (`normalized`, `ChallengeSpec.lean:124`), so every component value continuous in
the phase (`characterContinuity`, `ChallengeSpec.lean:131`) is integrable.

DERIVED: no numeral appears in the statement. -/
theorem integrable_of_continuous [IsFiniteMeasure ν] {E : Type*} [NormedAddCommGroup E]
    {f : X → E} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Variance zero, continuity and full support give a constant. If `S` is continuous on a compact
space, `ν` is a finite measure of full support (`fullSupport`, `ChallengeSpec.lean:125`) and
`∫ ‖S ξ − m‖² dν = 0`, then `S ξ = m` at every `ξ`. The integrand is continuous and nonnegative, so a
zero integral makes it zero almost everywhere, and a continuous function zero almost everywhere for a
measure of full support is zero everywhere.

DERIVED: `2` is the square of the mean-square distance; `0` is the value of the variance. -/
theorem eq_of_integral_norm_sub_sq_eq_zero [IsFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {E : Type*} [NormedAddCommGroup E] {S : X → E} {m : E} (hS : Continuous S)
    (h0 : ∫ ξ, ‖S ξ - m‖ ^ 2 ∂ν = 0) : ∀ ξ, S ξ = m := by
  have hg : Continuous fun ξ => ‖S ξ - m‖ ^ 2 := ((hS.sub continuous_const).norm).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (by intro ξ; simp only [Pi.zero_apply]; positivity)
    (integrable_of_continuous (ν := ν) hg)).mp h0
  have heq := (hg.ae_eq_iff_eq ν continuous_zero).mp hae
  intro ξ
  have hξ : ‖S ξ - m‖ ^ 2 = 0 := congrFun heq ξ
  exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hξ))

/-- The complex identification, in their value type (`correlation … → ℂ`, `ChallengeSpec.lean:41`).
If `S` is continuous (`characterContinuity`, `ChallengeSpec.lean:131`), its mean against a
probability measure (`normalized`, `ChallengeSpec.lean:124`) of full support (`fullSupport`,
`ChallengeSpec.lean:125`) is `m` (`mixture`, `ChallengeSpec.lean:133`), and its second moment is the
square of the mean, `∫ S ξ · conj (S ξ) dν = m · conj m`, then `S ξ = m` at every `ξ`. The variance
`∫ |S − m|² dν` expands to `∫ S conj S − conj m ∫ S − m conj (∫ S) + m conj m = 0`.

DERIVED: no numeral appears in the statement. -/
theorem eq_of_integral_mul_conj [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] {S : X → ℂ} {m : ℂ}
    (hS : Continuous S) (hmix : ∫ ξ, S ξ ∂ν = m)
    (hmom : ∫ ξ, S ξ * conj (S ξ) ∂ν = m * conj m) : ∀ ξ, S ξ = m := by
  have hSc : Continuous fun ξ => conj (S ξ) := Complex.continuous_conj.comp hS
  have h1 : Integrable (fun ξ => S ξ * conj (S ξ)) ν := integrable_of_continuous (hS.mul hSc)
  have h2 : Integrable (fun ξ => conj m * S ξ) ν :=
    integrable_of_continuous (continuous_const.mul hS)
  have h3 : Integrable (fun ξ => m * conj (S ξ)) ν :=
    integrable_of_continuous (continuous_const.mul hSc)
  have expand : (fun ξ => ((‖S ξ - m‖ ^ 2 : ℝ) : ℂ))
      = fun ξ => (S ξ * conj (S ξ) - conj m * S ξ - m * conj (S ξ)) + m * conj m := by
    funext ξ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sub]
    ring
  have hc : ∫ ξ, ((‖S ξ - m‖ ^ 2 : ℝ) : ℂ) ∂ν = 0 := by
    have h12 : Integrable (fun ξ => S ξ * conj (S ξ) - conj m * S ξ) ν := h1.sub h2
    have h123 : Integrable (fun ξ => S ξ * conj (S ξ) - conj m * S ξ - m * conj (S ξ)) ν :=
      h12.sub h3
    rw [expand, integral_add h123 (integrable_const _), integral_sub h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
      integral_conj, hmix, hmom, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have hr : ∫ ξ, ((‖S ξ - m‖ ^ 2 : ℝ) : ℂ) ∂ν = ((∫ ξ, ‖S ξ - m‖ ^ 2 ∂ν : ℝ) : ℂ) :=
    integral_ofReal
  rw [hc] at hr
  exact eq_of_integral_norm_sub_sq_eq_zero hS (by exact_mod_cast hr.symm)

/-- The real identification. If `S` is real and continuous, its mean against a probability measure
of full support is `m`, and `∫ (S ξ)² dν = m²`, then `S ξ = m` at every `ξ`: the variance
`∫ (S − m)² dν = ∫ S² − 2 m ∫ S + m²` is zero.

DERIVED: `2` is the square of the second moment. -/
theorem eq_of_integral_sq [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] {S : X → ℝ} {m : ℝ}
    (hS : Continuous S) (hmix : ∫ ξ, S ξ ∂ν = m) (hmom : ∫ ξ, S ξ ^ 2 ∂ν = m ^ 2) :
    ∀ ξ, S ξ = m := by
  have h1 : Integrable (fun ξ => S ξ ^ 2) ν := integrable_of_continuous (hS.pow 2)
  have h2 : Integrable (fun ξ => (2 * m) * S ξ) ν :=
    integrable_of_continuous (continuous_const.mul hS)
  have expand : (fun ξ => ‖S ξ - m‖ ^ 2) = fun ξ => (S ξ ^ 2 - (2 * m) * S ξ) + m ^ 2 := by
    funext ξ
    rw [Real.norm_eq_abs, sq_abs]
    ring
  refine eq_of_integral_norm_sub_sq_eq_zero (ν := ν) hS ?_
  have h12 : Integrable (fun ξ => S ξ ^ 2 - (2 * m) * S ξ) ν := h1.sub h2
  rw [expand, integral_add h12 (integrable_const _), integral_sub h1 h2,
    integral_const_mul, hmix, hmom, integral_const]
  simp only [probReal_univ, one_smul]
  ring

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
/-- The short calculation of the group's §6.2. Let `F t ξ` be the component value at phase `ξ` of
the product `A · τ_t B` of two observables at separation `t`, with `Fmix t` its mixed value. If each
`F t` is measurable and bounded by `K` for all large `t`, each component clusters
(`F t ξ → SA ξ · SB ξ` along `l`), the mixed value is the average of the components
(`mixture`, `ChallengeSpec.lean:133`) and the mixed theory clusters (`Fmix t → mA · mB`), then
`∫ SA ξ · SB ξ dν = mA · mB`. Dominated convergence against the constant `K`, integrable for the
finite measure, carries the component limits through the average; the two limits of `Fmix` agree.

DERIVED: no numeral appears in the statement. -/
theorem integral_mul_eq_of_clusters [IsFiniteMeasure ν] {T : Type*} {l : Filter T} [l.NeBot]
    [l.IsCountablyGenerated] {F : T → X → ℂ} {Fmix : T → ℂ} {SA SB : X → ℂ} {mA mB : ℂ} {K : ℝ}
    (hmeas : ∀ᶠ t in l, AEStronglyMeasurable (F t) ν) (hbd : ∀ᶠ t in l, ∀ ξ, ‖F t ξ‖ ≤ K)
    (hcomp : ∀ ξ, Tendsto (fun t => F t ξ) l (𝓝 (SA ξ * SB ξ)))
    (hmix : ∀ t, ∫ ξ, F t ξ ∂ν = Fmix t) (hclust : Tendsto Fmix l (𝓝 (mA * mB))) :
    ∫ ξ, SA ξ * SB ξ ∂ν = mA * mB := by
  have hdom := tendsto_integral_filter_of_dominated_convergence (fun _ => K) hmeas
    (hbd.mono fun t h => ae_of_all _ h) (integrable_const K) (ae_of_all _ hcomp)
  simp only [hmix] at hdom
  exact tendsto_nhds_unique hdom hclust

/-- Every component equals the mixture, from the product moment. Their correlation
`corr : Option X → ι → ℂ` reads the component at phase `ξ` as `corr (some ξ)` and the mixed theory
as `corr none` (`ChallengeSpec.lean:41`), on an observable `a : ι`. Suppose each component value is
continuous in the phase (`characterContinuity`, `ChallengeSpec.lean:131`), the mixed value is the
average (`mixture`, `ChallengeSpec.lean:133`) against a probability measure (`normalized`,
`ChallengeSpec.lean:124`) of full support (`fullSupport`, `ChallengeSpec.lean:125`), a conjugation
`cj` on observables conjugates every component value (field conjugation; for real observables
`cj` is the identity), and the product moments factor as the mixed values,
`∫ corr (some ξ) a · corr (some ξ) b dν = corr none a · corr none b`. Then
`corr (some ξ) a = corr none a` for every phase `ξ` and every observable `a`. The conjugate mixed
value is `conj (corr none a)` because the integral commutes with conjugation.

DERIVED: no numeral appears in the statement. -/
theorem component_eq_mixture [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure] {ι : Type*}
    (corr : Option X → ι → ℂ) (cj : ι → ι)
    (hcont : ∀ a, Continuous fun ξ => corr (some ξ) a)
    (hmix : ∀ a, ∫ ξ, corr (some ξ) a ∂ν = corr none a)
    (hstar : ∀ a ξ, corr (some ξ) (cj a) = conj (corr (some ξ) a))
    (hmom : ∀ a b, ∫ ξ, corr (some ξ) a * corr (some ξ) b ∂ν = corr none a * corr none b) :
    ∀ a ξ, corr (some ξ) a = corr none a := by
  intro a
  have hstarmix : corr none (cj a) = conj (corr none a) := by
    rw [← hmix (cj a), ← hmix a, ← integral_conj]
    simp only [hstar]
  refine eq_of_integral_mul_conj (hcont a) (hmix a) ?_
  have h := hmom a (cj a)
  simp only [hstar, hstarmix] at h
  exact h

/-- Every component equals the mixture, from clustering of the mixed theory. On top of the
hypotheses of `component_eq_mixture` except the product moment, let `F a b t ξ` be the component
value of the product of `a` with `b` translated by `t`, `Fmix a b t` its mixed value, measurable and
bounded by `K a b` for all large `t`. If each component clusters (`F a b t ξ → corr (some ξ) a ·
corr (some ξ) b`), the mixed product value is the average and the mixed theory clusters
(`Fmix a b t → corr none a · corr none b`), then every component equals the mixture on every
observable. This is the conclusion the group's §6.2 states: clustering of the mixed theory, with
continuity and full support, identifies every component.

DERIVED: no numeral appears in the statement. -/
theorem component_eq_mixture_of_clusters [IsProbabilityMeasure ν] [ν.IsOpenPosMeasure]
    {ι T : Type*} {l : Filter T} [l.NeBot] [l.IsCountablyGenerated]
    (corr : Option X → ι → ℂ) (cj : ι → ι)
    (hcont : ∀ a, Continuous fun ξ => corr (some ξ) a)
    (hmix : ∀ a, ∫ ξ, corr (some ξ) a ∂ν = corr none a)
    (hstar : ∀ a ξ, corr (some ξ) (cj a) = conj (corr (some ξ) a))
    (F : ι → ι → T → X → ℂ) (Fmix : ι → ι → T → ℂ) (K : ι → ι → ℝ)
    (hmeas : ∀ a b, ∀ᶠ t in l, AEStronglyMeasurable (F a b t) ν)
    (hbd : ∀ a b, ∀ᶠ t in l, ∀ ξ, ‖F a b t ξ‖ ≤ K a b)
    (hcomp : ∀ a b ξ, Tendsto (fun t => F a b t ξ) l (𝓝 (corr (some ξ) a * corr (some ξ) b)))
    (hFmix : ∀ a b t, ∫ ξ, F a b t ξ ∂ν = Fmix a b t)
    (hclust : ∀ a b, Tendsto (Fmix a b) l (𝓝 (corr none a * corr none b))) :
    ∀ a ξ, corr (some ξ) a = corr none a :=
  component_eq_mixture corr cj hcont hmix hstar fun a b =>
    integral_mul_eq_of_clusters (hmeas a b) (hbd a b) (hcomp a b) (hFmix a b) (hclust a b)

end Identification

/-! ## 2. A uniform bound through iterated limits -/

section Limits

variable {α β E : Type*} [SeminormedAddCommGroup E]

/-- A bound passes through two iterated limits. Let `c m p` converge to `L p` along a filter `l₁ p`
in the first index (the spacing, along a subsequence that may depend on the volume index `p`), and
`L p` converge to `Llim` along a filter `l₂` in the second (the volume, along a subsequence). If
`‖c m p‖ ≤ B` eventually in `m` along `l₁ p`, for all `p` eventually along `l₂`, then `‖Llim‖ ≤ B`.
The norm is continuous and a closed bound survives each limit.

DERIVED: no numeral appears in the statement. -/
theorem norm_le_of_iterated_limits {l₁ : β → Filter α} [∀ p, (l₁ p).NeBot] {l₂ : Filter β}
    [l₂.NeBot] {c : α → β → E} {L : β → E} {Llim : E} {B : ℝ}
    (h₁ : ∀ p, Tendsto (fun m => c m p) (l₁ p) (𝓝 (L p))) (h₂ : Tendsto L l₂ (𝓝 Llim))
    (hB : ∀ᶠ p in l₂, ∀ᶠ m in l₁ p, ‖c m p‖ ≤ B) : ‖Llim‖ ≤ B := by
  refine le_of_tendsto h₂.norm ?_
  filter_upwards [hB] with p hp
  exact le_of_tendsto (h₁ p).norm hp

/-- The sequence form, in the order of their construction: spacing first along a subsequence `φ p`
chosen at each volume index `p`, then volume along a subsequence `ψ`. If `c (φ p k) p → L p` as
`k → ∞` with `φ p k → ∞`, `L (ψ j) → Llim` as `j → ∞`, and `‖c m p‖ ≤ B` for all large `m` and all
`p` (the uniformity Theorem 4.46 delivers), then `‖Llim‖ ≤ B`.

DERIVED: no numeral appears in the statement. -/
theorem norm_le_of_iterated_subsequences {c : ℕ → ℕ → E} {L : ℕ → E} {Llim : E} {B : ℝ}
    (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ) (hφ : ∀ p, Tendsto (φ p) atTop atTop)
    (h₁ : ∀ p, Tendsto (fun k => c (φ p k) p) atTop (𝓝 (L p)))
    (h₂ : Tendsto (fun j => L (ψ j)) atTop (𝓝 Llim))
    (hB : ∀ᶠ m in atTop, ∀ p, ‖c m p‖ ≤ B) : ‖Llim‖ ≤ B :=
  norm_le_of_iterated_limits (l₁ := fun _ => atTop) (l₂ := atTop)
    (c := fun k j => c (φ (ψ j) k) (ψ j)) (L := fun j => L (ψ j))
    (fun j => h₁ (ψ j)) h₂
    (Eventually.of_forall fun j => ((hφ (ψ j)).eventually hB).mono fun _ h => h (ψ j))

/-- The exponential form. If at every separation `τ ∈ T` the iterated limits hold and
`‖c m p τ‖ ≤ C e^{−μτ}` eventually in both indices, then `‖Llim τ‖ ≤ C e^{−μτ}` at every `τ ∈ T`:
a uniform exponential decay of the finite-volume connected correlations is a decay of the limit
at the same rate `μ` and constant `C`.

DERIVED: no numeral appears in the statement. -/
theorem norm_le_exp_of_iterated_limits {l₁ : β → Filter α} [∀ p, (l₁ p).NeBot] {l₂ : Filter β}
    [l₂.NeBot] {c : α → β → ℝ → E} {L : β → ℝ → E} {Llim : ℝ → E} {C μ : ℝ} {T : Set ℝ}
    (h₁ : ∀ τ ∈ T, ∀ p, Tendsto (fun m => c m p τ) (l₁ p) (𝓝 (L p τ)))
    (h₂ : ∀ τ ∈ T, Tendsto (fun p => L p τ) l₂ (𝓝 (Llim τ)))
    (hB : ∀ τ ∈ T, ∀ᶠ p in l₂, ∀ᶠ m in l₁ p, ‖c m p τ‖ ≤ C * Real.exp (-μ * τ)) :
    ∀ τ ∈ T, ‖Llim τ‖ ≤ C * Real.exp (-μ * τ) := fun τ hτ =>
  norm_le_of_iterated_limits (c := fun m p => c m p τ) (L := fun p => L p τ) (h₁ τ hτ) (h₂ τ hτ) (hB τ hτ)

/-- The exponential form along subsequences, with the bound uniform in the spacing and the volume:
`‖c m p τ‖ ≤ C e^{−μτ}` for all large `m`, all `p` and all `τ ∈ T` gives `‖Llim τ‖ ≤ C e^{−μτ}` at
every `τ ∈ T`, for limits taken in the spacing along `φ p`, then in the volume along `ψ`.

DERIVED: no numeral appears in the statement. -/
theorem norm_le_exp_of_iterated_subsequences {c : ℕ → ℕ → ℝ → E} {L : ℕ → ℝ → E} {Llim : ℝ → E}
    {C μ : ℝ} {T : Set ℝ} (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ) (hφ : ∀ p, Tendsto (φ p) atTop atTop)
    (h₁ : ∀ τ ∈ T, ∀ p, Tendsto (fun k => c (φ p k) p τ) atTop (𝓝 (L p τ)))
    (h₂ : ∀ τ ∈ T, Tendsto (fun j => L (ψ j) τ) atTop (𝓝 (Llim τ)))
    (hB : ∀ᶠ m in atTop, ∀ p, ∀ τ ∈ T, ‖c m p τ‖ ≤ C * Real.exp (-μ * τ)) :
    ∀ τ ∈ T, ‖Llim τ‖ ≤ C * Real.exp (-μ * τ) := fun τ hτ =>
  norm_le_of_iterated_subsequences (c := fun m p => c m p τ) (L := fun p => L p τ) φ ψ hφ
    (h₁ τ hτ) (h₂ τ hτ) (hB.mono fun _ h p => h p τ hτ)

end Limits

end MassGap.OpenAIBridgeLimits

#print axioms MassGap.OpenAIBridgeLimits.integrable_of_continuous
#print axioms MassGap.OpenAIBridgeLimits.eq_of_integral_norm_sub_sq_eq_zero
#print axioms MassGap.OpenAIBridgeLimits.eq_of_integral_mul_conj
#print axioms MassGap.OpenAIBridgeLimits.eq_of_integral_sq
#print axioms MassGap.OpenAIBridgeLimits.integral_mul_eq_of_clusters
#print axioms MassGap.OpenAIBridgeLimits.component_eq_mixture
#print axioms MassGap.OpenAIBridgeLimits.component_eq_mixture_of_clusters
#print axioms MassGap.OpenAIBridgeLimits.norm_le_of_iterated_limits
#print axioms MassGap.OpenAIBridgeLimits.norm_le_of_iterated_subsequences
#print axioms MassGap.OpenAIBridgeLimits.norm_le_exp_of_iterated_limits
#print axioms MassGap.OpenAIBridgeLimits.norm_le_exp_of_iterated_subsequences
