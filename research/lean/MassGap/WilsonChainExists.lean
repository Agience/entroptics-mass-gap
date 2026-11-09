import Mathlib
import MassGap.ChainFirstCrossing

/-!
# MassGap.WilsonChainExists — the flat Migdal–Kadanoff chain from the Wilson weight exists, for every `β`

`ChainCoarseSeed.WilsonChain β` bundles the sequences `W_k`, `P_k` with `W_0 = e^{βt}`, `P_k = μ_k convT(W_k⁴)` and `W_{k+1} = ν_k convT(P_k)` on
`(−1, 1)`, each `P_k`, `W_{k+1}` continuous on `ℝ` and `C¹` on `[−1, 1]` in `t = cos ψ`, the derivative
continuous there, the endpoints `±1` included. This module constructs one, `wilsonChainOf β`, with
`μ = ν = 1`, for every real `β`.

## The regularity class

A weight `V` is in `SmoothClass` when it is continuous on `ℝ` and its class function `ψ ↦ V(cos ψ)` is
`C^∞` on `ℝ`. The construction never asks for regularity in `t`: the class is closed under the fourth
power (`smoothClass_pow_four`) and under the extended convolution (`smoothClass_convExt`), and a weight in
the class is `C¹` in `t` on `[−1, 1]` up to the endpoints (`hasDerivWithinAt_tDeriv`).

## The convolution in the angle

* `ellConv_angle`: `ellConv V ψ = ∫₀^π V(cos a) sin a (Φ(cos(a − ψ)) − Φ(cos(a + ψ))) da`, `Φ` the
  primitive of `V` (`primV`). The substitution `t = cos a` turns the ellipse slice at `t` into the arc
  `[a − ψ, a + ψ]`.
* `contDiff_ellConv`: for `V` in the class, `ψ ↦ ellConv V ψ` is `C^∞`. `Φ ∘ cos` is `C^∞` because its
  derivative is `−V(cos x) sin x` (`contDiff_primV_cos`); a parametric integral of a jointly `C^∞`
  integrand is `C^∞` (`contDiff_intervalIntegral`, by induction on the order, differentiating under the
  integral with a bound from compactness).
* `ellConv` vanishes where `sin ψ = 0` (the slices degenerate), is odd and `2π`-periodic.

## Division by `sin`

`divSin N = N / sin`, with the value `N′/cos` where `sin` vanishes. If `N` is `C^∞` and vanishes where
`sin` does, `divSin N` is `C^∞` (`contDiff_divSin`): at a zero `x₀` of `sin`, `N(x) = (x − x₀) M(x)` and
`sin x = (x − x₀) S(x)` with `M, S` the slope integrals `∫₀¹ N′(x₀ + τ(x − x₀)) dτ` (`slopeInt`),
`S(x₀) = cos x₀ ≠ 0`, so `divSin N = M/S` near `x₀`. For odd, `2π`-periodic `N`, `divSin N` is even and
`2π`-periodic, so it is a function of `cos ψ` (`eq_comp_arccos_cos`).

`convExt V t = divSin (ellConv V) (arccos t)` agrees with `convT V` on `(−1, 1)` (`convExt_eq`), is
continuous on `ℝ`, and its class function is `divSin (ellConv V)` (`convExt_cos`).

## `C¹` in `t` up to `±1`

For `h` in the class, `f = h ∘ cos` is `C^∞` and `f′` vanishes where `sin` does (`f` is even about each
zero of `sin`), so `D = divSin f′` is `C^∞` and `f′ = D sin`. Then on `[−1, 1]`
`h(t) = f(0) − ∫₁ᵗ D(arccos u) du` (the substitution `u = cos s`), and the right side is `C¹` on `ℝ`
with derivative `−D(arccos t)` (`tDeriv`). No limit at the endpoints is taken.

## The chain

`chainW β`, `chainP β`, `chainW' β`, `wilsonChainOf β : WilsonChain β`; `wilsonChain_exists`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.WilsonChainExists

open Real Set MeasureTheory Filter
open scoped ContDiff
open MassGap.ConvolutionTransfer MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing

/-! ## 1. Parametric integrals of smooth integrands -/

section Param

/-- **A parametric interval integral of a jointly `C^∞` integrand is `C^∞`.** -/
theorem contDiff_intervalIntegral {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (a b : ℝ) : ContDiff ℝ ∞ (fun x => ∫ τ in a..b, F x τ) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      hF.continuous a b
  | succ n ih =>
    set F' : ℝ → ℝ → ℝ := fun x τ => fderiv ℝ (Function.uncurry F) (x, τ) (1, 0) with hF'def
    have hF' : ContDiff ℝ ∞ (Function.uncurry F') := by
      have h1 : ContDiff ℝ ∞ (fderiv ℝ (Function.uncurry F)) := hF.fderiv_right (m := ∞) le_rfl
      exact h1.clm_apply contDiff_const
    have hd : ∀ x τ, HasDerivAt (fun x => F x τ) (F' x τ) x := by
      intro x τ
      have hfd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (x, τ)) (x, τ) :=
        ((hF.differentiable (by simp)) (x, τ)).hasFDerivAt
      have hp : HasDerivAt (fun x : ℝ => (x, τ)) ((1 : ℝ), (0 : ℝ)) x :=
        (hasDerivAt_id' x).prodMk (hasDerivAt_const x τ)
      exact hfd.comp_hasDerivAt x hp
    have hcF : ∀ x, Continuous (fun τ => F x τ) := fun x =>
      hF.continuous.comp (continuous_const.prodMk continuous_id)
    have hcF' : ∀ x, Continuous (fun τ => F' x τ) := fun x =>
      hF'.continuous.comp (continuous_const.prodMk continuous_id)
    have hint : ∀ x₀, HasDerivAt (fun x => ∫ τ in a..b, F x τ) (∫ τ in a..b, F' x₀ τ) x₀ := by
      intro x₀
      obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
        (hF'.continuous.continuousOn (s := Icc (x₀ - 1) (x₀ + 1) ×ˢ uIcc a b))
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume) (a := a) (b := b) (x₀ := x₀) (s := Ioo (x₀ - 1) (x₀ + 1))
        (bound := fun _ => C) (Ioo_mem_nhds (by linarith) (by linarith))
        (Eventually.of_forall fun x => (hcF x).aestronglyMeasurable)
        ((hcF x₀).intervalIntegrable _ _) (hcF' x₀).aestronglyMeasurable
        (Eventually.of_forall fun τ hτ x hx => ?_) intervalIntegrable_const
        (Eventually.of_forall fun τ _ x _ => hd x τ)).2
      exact hC (x, τ) ⟨Ioo_subset_Icc_self hx, uIoc_subset_uIcc hτ⟩
    have hderiv : deriv (fun x => ∫ τ in a..b, F x τ) = fun x => ∫ τ in a..b, F' x τ :=
      funext fun x => (hint x).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hint x).differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [hderiv]
    exact ih hF'

/-- The slope integral `∫₀¹ N′(τ x + (1 − τ) x₀) dτ`. -/
def slopeInt (N : ℝ → ℝ) (x₀ x : ℝ) : ℝ := ∫ τ in (0 : ℝ)..1, deriv N (τ * x + (1 - τ) * x₀)

theorem contDiff_slopeInt {N : ℝ → ℝ} (hN : ContDiff ℝ ∞ N) (x₀ : ℝ) :
    ContDiff ℝ ∞ (slopeInt N x₀) := by
  have hN' : ContDiff ℝ ∞ (deriv N) := (contDiff_infty_iff_deriv.1 hN).2
  have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 * p.1 + (1 - p.2) * x₀) := by fun_prop
  exact contDiff_intervalIntegral (F := fun x τ => deriv N (τ * x + (1 - τ) * x₀)) (hN'.comp hg) 0 1

theorem slopeInt_self (N : ℝ → ℝ) (x₀ : ℝ) : slopeInt N x₀ x₀ = deriv N x₀ := by
  unfold slopeInt
  have h : ∀ τ : ℝ, τ * x₀ + (1 - τ) * x₀ = x₀ := fun τ => by ring
  simp only [h, intervalIntegral.integral_const, sub_zero, one_smul]

/-- **The slope form**: `N x − N x₀ = (x − x₀) · slopeInt N x₀ x`. -/
theorem sub_eq_mul_slopeInt {N : ℝ → ℝ} (hN : ContDiff ℝ ∞ N) (x₀ x : ℝ) :
    N x - N x₀ = (x - x₀) * slopeInt N x₀ x := by
  have hd : ∀ τ, HasDerivAt (fun τ => N (τ * x + (1 - τ) * x₀))
      (deriv N (τ * x + (1 - τ) * x₀) * (x - x₀)) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => τ * x + (1 - τ) * x₀) (x - x₀) τ := by
      have e : (fun τ : ℝ => τ * x + (1 - τ) * x₀) = fun τ => τ * (x - x₀) + x₀ := by
        funext y; ring
      rw [e]
      simpa using ((hasDerivAt_id' τ).mul_const (x - x₀)).add_const x₀
    exact ((hN.differentiable (by simp)) _).hasDerivAt.comp τ h1
  have hc : Continuous (fun τ => deriv N (τ * x + (1 - τ) * x₀) * (x - x₀)) :=
    ((hN.continuous_deriv (by simp)).comp (by fun_prop)).mul continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)
    (hc.intervalIntegrable 0 1)
  simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero, zero_add] at h
  rw [intervalIntegral.integral_mul_const] at h
  unfold slopeInt
  rw [← h]
  ring

end Param

/-! ## 2. Division by `sin` -/

section DivSin

/-- `N / sin`, with the value `N′/cos` where `sin` vanishes. -/
def divSin (N : ℝ → ℝ) (x : ℝ) : ℝ := if sin x = 0 then deriv N x / cos x else N x / sin x

theorem divSin_mul_sin {N : ℝ → ℝ} (hz : ∀ x, sin x = 0 → N x = 0) (x : ℝ) :
    divSin N x * sin x = N x := by
  unfold divSin
  split_ifs with h
  · rw [h, mul_zero, hz x h]
  · field_simp

theorem cos_ne_zero_of_sin_eq_zero {x : ℝ} (h : sin x = 0) : cos x ≠ 0 := by
  intro hc
  have := sin_sq_add_cos_sq x
  rw [h, hc] at this
  norm_num at this

/-- **`N / sin` is `C^∞`** when `N` is `C^∞` and vanishes where `sin` does. -/
theorem contDiff_divSin {N : ℝ → ℝ} (hN : ContDiff ℝ ∞ N) (hz : ∀ x, sin x = 0 → N x = 0) :
    ContDiff ℝ ∞ (divSin N) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases h0 : sin x₀ = 0
  · have hc0 := cos_ne_zero_of_sin_eq_zero h0
    have hM := contDiff_slopeInt hN x₀
    have hS := contDiff_slopeInt contDiff_sin x₀
    have hS0 : slopeInt sin x₀ x₀ = cos x₀ := by rw [slopeInt_self, Real.deriv_sin]
    have hSne : ∀ᶠ x in nhds x₀, slopeInt sin x₀ x ≠ 0 :=
      hS.continuous.continuousAt.eventually_ne (by rw [hS0]; exact hc0)
    have heq : divSin N =ᶠ[nhds x₀] fun x => slopeInt N x₀ x / slopeInt sin x₀ x := by
      filter_upwards [hSne] with x hx
      by_cases hxx : x = x₀
      · subst hxx
        rw [slopeInt_self, hS0]
        simp [divSin, h0]
      · have hsx : sin x = (x - x₀) * slopeInt sin x₀ x := by
          have := sub_eq_mul_slopeInt contDiff_sin x₀ x
          rwa [h0, sub_zero] at this
        have hNx : N x = (x - x₀) * slopeInt N x₀ x := by
          have := sub_eq_mul_slopeInt hN x₀ x
          rwa [hz x₀ h0, sub_zero] at this
        have hne : x - x₀ ≠ 0 := sub_ne_zero.2 hxx
        have hsx0 : sin x ≠ 0 := by rw [hsx]; exact mul_ne_zero hne hx
        simp only [divSin, if_neg hsx0]
        rw [hNx, hsx, mul_div_mul_left _ _ hne]
    exact (hM.contDiffAt.div hS.contDiffAt (by rw [hS0]; exact hc0)).congr_of_eventuallyEq heq
  · have heq : divSin N =ᶠ[nhds x₀] fun x => N x / sin x := by
      filter_upwards [continuous_sin.continuousAt.eventually_ne h0] with x hx
      simp [divSin, hx]
    exact (hN.contDiffAt.div contDiff_sin.contDiffAt h0).congr_of_eventuallyEq heq

theorem divSin_neg {N : ℝ → ℝ} (hodd : ∀ x, N (-x) = -N x) (x : ℝ) :
    divSin N (-x) = divSin N x := by
  have hd : deriv N (-x) = deriv N x := by
    have h1 : (fun x => N (-x)) = -N := by funext y; rw [hodd]; rfl
    have h2 := deriv_comp_neg N x
    rw [h1, deriv.neg] at h2
    linarith
  unfold divSin
  simp only [sin_neg, cos_neg, neg_eq_zero, hodd, hd]
  split_ifs with h
  · rfl
  · rw [neg_div_neg_eq]

theorem divSin_add_two_pi {N : ℝ → ℝ} (hper : ∀ x, N (x + 2 * π) = N x) (x : ℝ) :
    divSin N (x + 2 * π) = divSin N x := by
  have hd : deriv N (x + 2 * π) = deriv N x := by
    have h1 : (fun x => N (x + 2 * π)) = N := funext hper
    have h2 := deriv_comp_add_const N (2 * π) x
    rw [h1] at h2
    exact h2.symm
  unfold divSin
  rw [sin_add_two_pi, cos_add_two_pi, hper, hd]

/-- **An even, `2π`-periodic function is a function of `cos`.** -/
theorem eq_comp_arccos_cos {G : ℝ → ℝ} (hev : ∀ x, G (-x) = G x)
    (hper : ∀ x, G (x + 2 * π) = G x) (ψ : ℝ) : G (arccos (cos ψ)) = G ψ := by
  have hc : cos (arccos (cos ψ)) = cos ψ := cos_arccos (neg_one_le_cos ψ) (cos_le_one ψ)
  obtain ⟨k, hk⟩ := Real.cos_eq_cos_iff.1 hc
  have hP : Function.Periodic G (2 * π) := hper
  have hPk := hP.int_mul k
  rcases hk with h | h
  · conv_rhs => rw [h, show 2 * (k : ℝ) * π + arccos (cos ψ) = arccos (cos ψ) + k * (2 * π) by ring]
    rw [hPk]
  · conv_rhs => rw [h, show 2 * (k : ℝ) * π - arccos (cos ψ) = -arccos (cos ψ) + k * (2 * π) by ring]
    rw [hPk, hev]

end DivSin

/-! ## 3. The convolution in the angle -/

section Angle

/-- The primitive `Φ(x) = ∫₀ˣ V`. -/
def primV (V : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, V y

theorem hasDerivAt_primV {V : ℝ → ℝ} (hV : Continuous V) (x : ℝ) :
    HasDerivAt (primV V) (V x) x :=
  (hV.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem continuous_primV {V : ℝ → ℝ} (hV : Continuous V) : Continuous (primV V) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_primV hV x).continuousAt

/-- **The ellipse convolution in the angle**: the substitution `t = cos a` turns the slice of `E_ψ` at
`t` into the arc `[a − ψ, a + ψ]`. -/
theorem ellConv_angle {V : ℝ → ℝ} (hV : Continuous V) (ψ : ℝ) :
    ellConv V ψ = ∫ a in (0 : ℝ)..π,
      V (cos a) * sin a * (primV V (cos (a - ψ)) - primV V (cos (a + ψ))) := by
  rw [ellConv_eq hV ψ]
  have hΦc := continuous_primV hV
  set g : ℝ → ℝ := fun t => V t * (primV V (ellHi ψ t) - primV V (ellLo ψ t)) with hg
  have hcHi : Continuous (fun t => ellHi ψ t) := by unfold ellHi; fun_prop
  have hcLo : Continuous (fun t => ellLo ψ t) := by unfold ellLo; fun_prop
  have hgc : Continuous g := hV.mul ((hΦc.comp hcHi).sub (hΦc.comp hcLo))
  have hL : (∫ t in (-1 : ℝ)..1,
      V t * ((∫ y in (0 : ℝ)..ellHi ψ t, V y) - ∫ y in (0 : ℝ)..ellLo ψ t, V y))
      = ∫ t in (-1 : ℝ)..1, g t := rfl
  rw [hL]
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π) (f := cos)
    (f' := fun x => -sin x) (g := g) (fun x _ => hasDerivAt_cos x)
    ((continuous_sin.neg).continuousOn) hgc
  have e1 : ∫ x in (0 : ℝ)..π, (g ∘ cos) x * sin x = -∫ x in (0 : ℝ)..π, (g ∘ cos) x * -sin x := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x in (0 : ℝ)..π, (g ∘ cos) x * sin x = ∫ t in (-1 : ℝ)..1, g t := by
    rw [e1, hsub, cos_zero, cos_pi, intervalIntegral.integral_symm, neg_neg]
  rw [← e2]
  refine intervalIntegral.integral_congr fun a ha => ?_
  rw [uIcc_of_le pi_pos.le] at ha
  simp only [Function.comp, hg]
  have hHi : ellHi ψ (cos a) = cos (a - ψ) := by
    rw [ellHi, sqrt_one_sub_cos_sq ha, cos_sub]
  have hLo : ellLo ψ (cos a) = cos (a + ψ) := by
    rw [ellLo, sqrt_one_sub_cos_sq ha, cos_add]
  rw [hHi, hLo]
  ring

/-- Weights whose class function `ψ ↦ V(cos ψ)` is `C^∞`, continuous on `ℝ`. -/
def SmoothClass (V : ℝ → ℝ) : Prop := Continuous V ∧ ContDiff ℝ ∞ (fun ψ => V (cos ψ))

theorem contDiff_primV_cos {V : ℝ → ℝ} (hV : SmoothClass V) :
    ContDiff ℝ ∞ (fun x => primV V (cos x)) := by
  have hd : ∀ x, HasDerivAt (fun x => primV V (cos x)) (V (cos x) * -sin x) x := fun x =>
    (hasDerivAt_primV hV.1 (cos x)).comp x (hasDerivAt_cos x)
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have h : deriv (fun x => primV V (cos x)) = fun x => V (cos x) * -sin x :=
    funext fun x => (hd x).deriv
  rw [h]
  exact hV.2.mul contDiff_sin.neg

/-- **The ellipse convolution is `C^∞` in the angle** for a weight in the class. -/
theorem contDiff_ellConv {V : ℝ → ℝ} (hV : SmoothClass V) : ContDiff ℝ ∞ (ellConv V) := by
  have hP := contDiff_primV_cos hV
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => V (cos p.2)) := hV.2.comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => primV V (cos (p.2 - p.1))) :=
    hP.comp (contDiff_snd.sub contDiff_fst)
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => primV V (cos (p.2 + p.1))) :=
    hP.comp (contDiff_snd.add contDiff_fst)
  have h4 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => sin p.2) := contDiff_sin.comp contDiff_snd
  have hF := contDiff_intervalIntegral
    (F := fun ψ a => V (cos a) * sin a * (primV V (cos (a - ψ)) - primV V (cos (a + ψ))))
    ((h1.mul h4).mul (h2.sub h3)) 0 π
  convert hF using 1
  funext ψ
  exact ellConv_angle hV.1 ψ

theorem ellConv_of_sin_eq_zero (V : ℝ → ℝ) {ψ : ℝ} (h : sin ψ = 0) : ellConv V ψ = 0 := by
  unfold ellConv ellInt ellLo ellHi
  simp [h]

theorem ellConv_neg (V : ℝ → ℝ) (ψ : ℝ) : ellConv V (-ψ) = -ellConv V ψ := by
  unfold ellConv ellInt
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have h1 : ellLo (-ψ) t = ellHi ψ t := by unfold ellLo ellHi; rw [cos_neg, sin_neg]; ring
  have h2 : ellHi (-ψ) t = ellLo ψ t := by unfold ellLo ellHi; rw [cos_neg, sin_neg]; ring
  simp only
  rw [h1, h2]
  exact intervalIntegral.integral_symm _ _

theorem ellConv_add_two_pi (V : ℝ → ℝ) (ψ : ℝ) : ellConv V (ψ + 2 * π) = ellConv V ψ := by
  simp only [ellConv, ellInt, ellLo, ellHi, cos_add_two_pi, sin_add_two_pi]

end Angle

/-! ## 4. The extended convolution -/

section Ext

/-- **The class convolution, extended to `ℝ`**: `divSin (ellConv V)` read at `arccos t`. On `(−1, 1)` it is
`convT V` (`convExt_eq`); outside `[−1, 1]` it is constant. -/
def convExt (V : ℝ → ℝ) (t : ℝ) : ℝ := divSin (ellConv V) (arccos t)

theorem convExt_eq (V : ℝ → ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : convExt V t = convT V t := by
  have hψ := arccos_mem_Ioo ht
  have hs : sin (arccos t) ≠ 0 := (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).ne'
  unfold convExt convT divSin
  rw [if_neg hs]

/-- The class function of `convExt V` is `divSin (ellConv V)`. -/
theorem convExt_cos (V : ℝ → ℝ) (ψ : ℝ) : convExt V (cos ψ) = divSin (ellConv V) ψ :=
  eq_comp_arccos_cos (divSin_neg (ellConv_neg V)) (divSin_add_two_pi (ellConv_add_two_pi V)) ψ

/-- **The class is closed under the extended convolution.** -/
theorem smoothClass_convExt {V : ℝ → ℝ} (hV : SmoothClass V) : SmoothClass (convExt V) := by
  have hG := contDiff_divSin (contDiff_ellConv hV) (fun x h => ellConv_of_sin_eq_zero V h)
  refine ⟨hG.continuous.comp continuous_arccos, ?_⟩
  have h : (fun ψ => convExt V (cos ψ)) = divSin (ellConv V) := funext (convExt_cos V)
  rw [h]
  exact hG

/-- **The class is closed under the fourth power.** -/
theorem smoothClass_pow_four {V : ℝ → ℝ} (hV : SmoothClass V) :
    SmoothClass (fun t => V t ^ 4) :=
  ⟨hV.1.pow 4, hV.2.pow 4⟩

theorem smoothClass_exp (β : ℝ) : SmoothClass (fun t => Real.exp (β * t)) :=
  ⟨by fun_prop, (contDiff_const.mul contDiff_cos).exp⟩

end Ext

/-! ## 5. `C¹` in `t` up to the endpoints -/

section TDeriv

/-- The derivative in `t` of a weight in the class: `−divSin (f′) (arccos t)`, `f = h ∘ cos`. -/
def tDeriv (h : ℝ → ℝ) (t : ℝ) : ℝ := -divSin (deriv (fun ψ => h (cos ψ))) (arccos t)

/-- `h ∘ cos` is even about every zero of `sin`, so its derivative vanishes there. -/
theorem deriv_cosComp_eq_zero {h : ℝ → ℝ} (hd : Differentiable ℝ (fun ψ => h (cos ψ)))
    {x₀ : ℝ} (h0 : sin x₀ = 0) : deriv (fun ψ => h (cos ψ)) x₀ = 0 := by
  set f : ℝ → ℝ := fun ψ => h (cos ψ) with hf
  have hD : HasDerivAt f (deriv f x₀) x₀ := (hd x₀).hasDerivAt
  have h1 := HasDerivAt.comp_const_add x₀ 0 (by rw [add_zero]; exact hD)
  have h2 := HasDerivAt.comp_const_sub x₀ 0 (by rw [sub_zero]; exact hD)
  have heq : (fun x => f (x₀ + x)) = fun x => f (x₀ - x) := by
    funext s
    simp only [hf]
    rw [cos_add, cos_sub, h0]
    simp
  rw [heq] at h1
  have := h1.unique h2
  linarith

theorem continuous_tDeriv {h : ℝ → ℝ} (hf : ContDiff ℝ ∞ (fun ψ => h (cos ψ))) :
    Continuous (tDeriv h) := by
  have hdiff : Differentiable ℝ (fun ψ => h (cos ψ)) := hf.differentiable (by simp)
  have hD := contDiff_divSin (contDiff_infty_iff_deriv.1 hf).2
    (fun x hx => deriv_cosComp_eq_zero hdiff hx)
  exact (hD.continuous.comp continuous_arccos).neg

/-- **A weight in the class is `C¹` in `t` on `[−1, 1]`, endpoints included**, with derivative
`tDeriv h`. On `[−1, 1]`, `h(t) = f(0) − ∫₁ᵗ D(arccos u) du` with `D = divSin f′`, `f = h ∘ cos`. -/
theorem hasDerivWithinAt_tDeriv {h : ℝ → ℝ} (hf : ContDiff ℝ ∞ (fun ψ => h (cos ψ))) {y : ℝ}
    (hy : y ∈ Icc (-1 : ℝ) 1) : HasDerivWithinAt h (tDeriv h y) (Icc (-1) 1) y := by
  set f : ℝ → ℝ := fun ψ => h (cos ψ) with hfdef
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hz : ∀ x, sin x = 0 → deriv f x = 0 := fun x hx => deriv_cosComp_eq_zero hdiff hx
  set D : ℝ → ℝ := divSin (deriv f) with hDdef
  have hD : ContDiff ℝ ∞ D := contDiff_divSin (contDiff_infty_iff_deriv.1 hf).2 hz
  have hDs : ∀ x, D x * sin x = deriv f x := divSin_mul_sin hz
  have hDa : Continuous (fun u => D (arccos u)) := hD.continuous.comp continuous_arccos
  set H : ℝ → ℝ := fun t => f 0 - ∫ u in (1 : ℝ)..t, D (arccos u) with hH
  have hHd : ∀ t, HasDerivAt H (-D (arccos t)) t := fun t =>
    ((hDa.integral_hasStrictDerivAt 1 t).hasDerivAt).const_sub (f 0)
  have hEq : EqOn h H (Icc (-1) 1) := by
    intro t ht
    have h1 : h t = f (arccos t) := by simp only [hfdef, cos_arccos ht.1 ht.2]
    have hψ0 : 0 ≤ arccos t := arccos_nonneg t
    have hψπ : arccos t ≤ π := arccos_le_pi t
    have hftc : ∫ s in (0 : ℝ)..arccos t, deriv f s = f (arccos t) - f 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => (hdiff s).hasDerivAt)
        ((hf.continuous_deriv (by simp)).intervalIntegrable _ _)
    have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := arccos t) (f := cos)
      (f' := fun x => -sin x) (g := fun u => D (arccos u)) (fun x _ => hasDerivAt_cos x)
      ((continuous_sin.neg).continuousOn) hDa
    simp only [Function.comp_apply] at hsub
    have hcongr : ∫ s in (0 : ℝ)..arccos t, D (arccos (cos s)) * -sin s
        = -∫ s in (0 : ℝ)..arccos t, deriv f s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hψ0] at hs
      rw [arccos_cos hs.1 (hs.2.trans hψπ), ← hDs s]
      ring
    rw [hcongr, hftc, cos_zero, cos_arccos ht.1 ht.2] at hsub
    rw [h1]
    show f (arccos t) = f 0 - ∫ u in (1 : ℝ)..t, D (arccos u)
    linarith
  exact (hHd y).hasDerivWithinAt.congr hEq (hEq hy)

end TDeriv

/-! ## 6. The chain -/

section Chain

/-- The chain weights: `W_0 = e^{βt}`, `W_{k+1} = convExt (convExt (W_k⁴))`. -/
def chainW (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => Real.exp (β * t)
  | k + 1 => convExt (convExt (fun t => chainW β k t ^ 4))

/-- The intermediate weights `P_k = convExt (W_k⁴)`. -/
def chainP (β : ℝ) (k : ℕ) : ℝ → ℝ := convExt (fun t => chainW β k t ^ 4)

/-- The derivatives in `t`: `β e^{βt}` at `k = 0`, `tDeriv` after. -/
def chainW' (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => β * Real.exp (β * t)
  | k + 1 => tDeriv (chainW β (k + 1))

theorem chainW_succ (β : ℝ) (k : ℕ) : chainW β (k + 1) = convExt (chainP β k) := rfl

theorem smoothClass_chainW (β : ℝ) : ∀ k, SmoothClass (chainW β k)
  | 0 => smoothClass_exp β
  | k + 1 => smoothClass_convExt (smoothClass_convExt (smoothClass_pow_four (smoothClass_chainW β k)))

theorem smoothClass_chainP (β : ℝ) (k : ℕ) : SmoothClass (chainP β k) :=
  smoothClass_convExt (smoothClass_pow_four (smoothClass_chainW β k))

/-- **The flat Migdal–Kadanoff chain from the Wilson weight**, constructed for every `β`, with
`μ = ν = 1`. -/
def wilsonChainOf (β : ℝ) : WilsonChain β where
  W := chainW β
  W' := chainW' β
  P := chainP β
  P' := fun k => tDeriv (chainP β k)
  μ := fun _ => 1
  ν := fun _ => 1
  hμ := fun _ => one_pos
  hν := fun _ => one_pos
  hW0 := rfl
  hW0' := rfl
  hWc := fun k => (smoothClass_chainW β (k + 1)).1
  hWd := fun k _ hy => hasDerivWithinAt_tDeriv (smoothClass_chainW β (k + 1)).2 hy
  hW'c := fun k => (continuous_tDeriv (smoothClass_chainW β (k + 1)).2).continuousOn
  hPc := fun k => (smoothClass_chainP β k).1
  hPd := fun k _ hy => hasDerivWithinAt_tDeriv (smoothClass_chainP β k).2 hy
  hP'c := fun k => (continuous_tDeriv (smoothClass_chainP β k).2).continuousOn
  hPeq := fun k y hy => by rw [one_mul]; exact convExt_eq _ hy
  hWeq := fun k y hy => by rw [one_mul, chainW_succ]; exact convExt_eq _ hy

/-- **A Wilson chain exists for every `β`.** -/
theorem wilsonChain_exists (β : ℝ) : Nonempty (WilsonChain β) := ⟨wilsonChainOf β⟩

end Chain

end MassGap.WilsonChainExists

#print axioms MassGap.WilsonChainExists.contDiff_intervalIntegral
#print axioms MassGap.WilsonChainExists.contDiff_divSin
#print axioms MassGap.WilsonChainExists.ellConv_angle
#print axioms MassGap.WilsonChainExists.contDiff_ellConv
#print axioms MassGap.WilsonChainExists.smoothClass_convExt
#print axioms MassGap.WilsonChainExists.hasDerivWithinAt_tDeriv
#print axioms MassGap.WilsonChainExists.wilsonChainOf
#print axioms MassGap.WilsonChainExists.wilsonChain_exists
