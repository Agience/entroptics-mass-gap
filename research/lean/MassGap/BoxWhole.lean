import Mathlib
import MassGap.BoxFocusTest

/-!
# MassGap.BoxWhole — the box twist ratio at every boundary condition, and what it gives the box kernel

`BoxFocusTest` reduces the gap to `KernelNear` at one box (the box kernel `γ_Λ X(ω)` within `δ` of a
constant at every boundary condition `ω`). This module states the 't Hooft vortex cost for the box law
itself, uniformly in `ω` (`BoundaryVAt`, `BoundaryV`), and tests it against `KernelNear` and against the
whole-system statement (V).

## Objects

* `twistBd τ ω`: the boundary condition `ω` acted on linkwise by `τ` (`WilsonDLR.twistConf` along the
  identity relabelling). The intended instance is left multiplication by a centre element on a set of links
  outside the box (an open Dirac sheet crossing the box surface); the theorems use only that `τ` is the
  identity on the box links and, in section 3, continuous.
* `boxRatio β Λ τ ω = Z_Λ(τ ω) / Z_Λ(ω)`: twisted over untwisted box partition function at boundary `ω`.
* `BoundaryVAt β Λ τ ε`: `|boxRatio − 1| ≤ ε` at every `ω`. `BoundaryV σ A b Λ τ`: for all large `β`,
  `BoundaryVAt β (Λ β) (τ β) (A e^{−σ b})` (the family `Λ β` is the box of physical size `b` at spacing
  `a(β)`; the module does not construct it).
* `LoopTwistAt β Λ τ X ε'`: the same comparison with the observable inserted,
  `|N_Λ(X | τ ω) − N_Λ(X | ω)| ≤ ε' Z_Λ(ω)` at every `ω` (`N = num`, the unnormalised box expectation).
  `BoundaryVAt` is its `X = 1` case.
* `reweight β Λ τ`: `R(U) = exp(−β (S_∂Λ(τ U) − S_∂Λ(U)))`, the box-boundary action change of the twist, a
  continuous observable of the whole configuration.

## Evaluation

1. **BoundaryV ⇒ KernelNear: not by itself** (proved reduction, argued gap).
   `spec_twist_shift_le`: `BoundaryVAt ε` together with `LoopTwistAt ε'` gives
   `|γ_Λ X(τ ω) − γ_Λ X(ω)| ≤ (ε' + M ε)/(1 − ε)` at every `ω`. `loopTwist_of_kernelNear`: conversely
   `KernelNear δ` and `BoundaryVAt ε` give `LoopTwistAt (2δ(1+ε) + Mε)`. So on the pairs `(ω, τ ω)`,
   kernel closeness is exactly `BoundaryV` plus the loop-inserted ratio `LoopTwist`
   (`shift_eq`: `n'/p' − n/p = ((n' − n) − (n/p)(p' − p))/p'`): `BoundaryV` controls the second term only.
   Two inputs are missing, and both are named:
   * `LoopTwistAt` — the twisted-vs-untwisted box expectation of the loop itself (the electric-flux reading
     with a loop inserted). It is implied by the target (`loopTwist_of_kernelNear`), so assuming it is not
     circular in form but is a piece of `KernelNear`'s own content.
   * Pairs off the twist orbit. `kernelNear_of_pairs`/`pairs_of_kernelNear`: `KernelNear` is equivalent to
     closeness at all pairs `(ω, ω')`. A centre twist reaches only `ω' = τ ω`; a generic `ω'` differs from
     `ω` by a non-central field on the surface links, which no twist ratio reads (argued: the twist changes
     each crossing plaquette holonomy by a centre element, so `|tr|` of every crossing plaquette at the
     surface is invariant along the orbit).
   No step here uses `KernelNear`, so the reduction is not circular; it does not close.
2. **(A) "Cost pushes it out" is BoundaryV** (proved for the two-sector `SU(2)` algebra).
   With `Z_e = (Z − Z_tw)/2`, `Z_0 = (Z + Z_tw)/2` (the 't Hooft electric/untwisted split for centre `ℤ₂`),
   `elec = Z_e/Z_0 = (1 − r)/(1 + r)`, `r = boxRatio`. `elec_le_of_ratio`: `|r − 1| ≤ ε ⇒ |elec| ≤ ε/(2 − ε)`;
   `ratio_le_of_elec`: `|elec| ≤ η < 1 ⇒ |r − 1| ≤ 2η/(1 − η)`. "Boundary-imposed electric flux through the
   box costs `σ b` at every `ω`" is therefore `BoundaryV` with a changed constant: same strength, and the same
   two inputs are missing for `KernelNear`. Exponential suppression of the flux sector is a statement about
   partition functions (the `X = 1` reading); suppression of the boundary's effect on a loop at the centre
   is `LoopTwist`, and on non-central boundary data it is not a flux statement at all.
3. **(B) "The observer averages"** (proved identities and one bound; argued gap).
   * `wspec_reweight`, `mean_boxRatio`: `γ_Λ R (ω) = boxRatio(ω)` exactly, so the `ν`-mean of the box twist
     ratio is the whole-system expectation `ν(R)` (DLR). `mean_loopTwist`: for `X` reading only the box,
     the `ν`-mean of `N_Λ(X|τω)/Z_Λ(ω)` is `ν(X R)`. These averaged forms are linear in `ν` and are not
     covariances of `ν` (contrast `BoxFocusTest.meanFocus_eq`, `kernel_var_eq_cov`): averaging the twist
     ratios is non-circular.
   * `mean_sq_boxRatio_le`: `ν((boxRatio − 1)²) ≤ ν((R − 1)²)` (Jensen in the box, then DLR): a typical-set
     form of `BoundaryV` (Chebyshev: the `ν`-weight of boundaries with `|boxRatio − 1| > t` is at most
     `ν((R − 1)²)/t²`) controlled by a whole-system second moment. Not a covariance, so not circular.
   * What is missing (argued): `R` is pointwise a product of `e^{±2β·}` factors over the crossing
     plaquettes, so `ν((R − 1)²)` is not small; the smallness of the box ratio lives in the cancellation
     inside `γ_Λ`, which Jensen discards. And a typical-set `BoundaryV` still feeds only the `X = 1` term:
     the kernel needs `LoopTwist` on the same typical set, and the closing then runs through
     `TypicalBoundary.typical_closing_rel`, whose union bound on the bad-set mass `μ(Gᶜ)` over the
     fine-boundary plaquettes diverges (`TypicalBoundary.vacuum_width_tendsto_top`).
4. **(C) "Fractal: box = whole"** (proved in mean; argued failure for the sup).
   In mean it holds exactly: `mean_boxRatio` is the identity "box law averaged over its boundary = whole
   law" for the twist observable. Note the whole-system object is `ν(R)` for the open-sheet box twist,
   an 't Hooft-loop-type insertion on the periodic system, not the twisted-torus ratio `zR` of
   `FluxCost.VortexCostAt` (argued: a closed twist sheet around a contractible box is a gauge transformation
   and has ratio `1`; a twist with flux through the box has an open sheet whose edge is a vortex line).
   For the sup over `ω`: a boundary condition is a point configuration, not an integrated one, so the box
   law at `ω` is not the periodic law at a coarser scale (`CoarseBoundary`, item 1: no identity
   `wspec F = g ∘ c` through coarse blocks; the exact decimation keeps integrated quantities only). The
   comparison that would move a bound from typical to all `ω` is `FocusZoom.spec_le_of_boundary`, with
   constant `e^{4|β| c_Λ}`, unbounded as `β → ∞` at fixed physical size. So self-similarity gives
   `BoundaryV` in mean (as `ν(R)`, a whole-system 't Hooft-loop quantity, itself not proved), not uniformly in `ω`.

## What is proved

`shift_eq`, `shift_le`, `loopTwist_bound_of_shift`, `elec_le_of_ratio`, `ratio_le_of_elec`,
`spec_twist_shift_le`, `pairs_of_kernelNear`, `kernelNear_of_pairs`, `loopTwist_of_kernelNear`,
`twistConf_splice_refl`, `reweight_mul_wt`, `num_reweight`, `wspec_reweight`, `mean_boxRatio`,
`num_mul_reweight`, `mean_loopTwist`, `sq_state_le`, `mean_sq_boxRatio_le`. No sorry, no axioms beyond
Lean's standard three.

DERIVED (module-wide): `2` in `Z_e`, `Z_0` (hence in `ε/(2 − ε)`, `2η/(1 − η)`) is the order of the centre
`ℤ₂` (sector projector `(1 ± twist)/2`); the `2δ` of `pairs_of_kernelNear` is the two-sided spread of two
points about one constant; `1` is the untwisted ratio.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.BoxWhole

open MeasureTheory Filter
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.PeriodicStateDLR (wspec wspec_apply periodicState_dlr)
open MassGap.PeriodicState (periodicState)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity measurable_wilsonDensity continuous_wilsonDensity
  wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.CompactGauge (probHaar)
open MassGap.WilsonDLR (twistConf continuous_twistConf continuous_actionOn)
open MassGap.BoxFocusTest (KernelNear boxState boxState_apply)

/-! ## 1. Algebra of a ratio of ratios -/

/-- `n'/p' − n/p = ((n' − n) − (n/p)(p' − p)) / p'`. -/
theorem shift_eq {n n' p p' : ℝ} (hp : p ≠ 0) (hp' : p' ≠ 0) :
    n' / p' - n / p = ((n' - n) - (n / p) * (p' - p)) / p' := by
  field_simp
  ring

/-- **Partition ratio plus loop-inserted ratio bound the normalised shift.** -/
theorem shift_le {n n' p p' ε ε' : ℝ} (hp : 0 < p) (hp' : 0 < p') (hε1 : ε < 1)
    (hV : |p' / p - 1| ≤ ε) (hL : |(n' - n) / p| ≤ ε') :
    |n' / p' - n / p| ≤ (ε' + |n / p| * ε) / (1 - ε) := by
  have e : n' / p' - n / p = ((n' - n) / p - (n / p) * (p' / p - 1)) / (p' / p) := by
    field_simp
    ring
  have hr : 1 - ε ≤ p' / p := by have := (abs_le.mp hV).1; linarith
  have hr0 : 0 < 1 - ε := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hV
  have hε'0 : 0 ≤ ε' := (abs_nonneg _).trans hL
  have hq : 0 < p' / p := div_pos hp' hp
  rw [e, abs_div, abs_of_pos hq, div_le_div_iff₀ hq hr0]
  have hnum : |(n' - n) / p - (n / p) * (p' / p - 1)| ≤ ε' + |n / p| * ε := by
    calc _ ≤ |(n' - n) / p| + |(n / p) * (p' / p - 1)| := abs_sub _ _
      _ ≤ ε' + |n / p| * ε := by
        rw [abs_mul]; exact add_le_add hL (mul_le_mul_of_nonneg_left hV (abs_nonneg _))
  have hpos : 0 ≤ ε' + |n / p| * ε := add_nonneg hε'0 (mul_nonneg (abs_nonneg _) hε0)
  calc _ ≤ (ε' + |n / p| * ε) * (1 - ε) := mul_le_mul_of_nonneg_right hnum hr0.le
    _ ≤ (ε' + |n / p| * ε) * (p' / p) := mul_le_mul_of_nonneg_left hr hpos

/-- **Converse**: a normalised shift and a partition ratio bound the loop-inserted ratio. -/
theorem loopTwist_bound_of_shift {n n' p p' ε δ : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hV : |p' / p - 1| ≤ ε) (hS : |n' / p' - n / p| ≤ δ) :
    |(n' - n) / p| ≤ δ * (1 + ε) + |n / p| * ε := by
  have e : (n' - n) / p = (n' / p' - n / p) * (p' / p) + (n / p) * (p' / p - 1) := by
    field_simp
    ring
  have hq : 0 < p' / p := div_pos hp' hp
  have hr : p' / p ≤ 1 + ε := by have := (abs_le.mp hV).2; linarith
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hS
  rw [e]
  calc _ ≤ |(n' / p' - n / p) * (p' / p)| + |(n / p) * (p' / p - 1)| := abs_add_le _ _
    _ ≤ δ * (1 + ε) + |n / p| * ε := by
      rw [abs_mul, abs_mul, abs_of_pos hq]
      exact add_le_add (mul_le_mul hS hr hq.le hδ0) (mul_le_mul_of_nonneg_left hV (abs_nonneg _))

/-- **(A) at `ℤ₂`: the electric ratio from the twist ratio.** `elec = (1 − r)/(1 + r)`. -/
theorem elec_le_of_ratio {r ε : ℝ} (hr : 0 < r) (hε : ε < 2) (h : |r - 1| ≤ ε) :
    |(1 - r) / (1 + r)| ≤ ε / (2 - ε) := by
  have h1 : 2 - ε ≤ 1 + r := by have := (abs_le.mp h).1; linarith
  have h0 : 0 < 2 - ε := by linarith
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans h
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + r), div_le_div_iff₀ (by linarith) h0,
    abs_sub_comm]
  calc |r - 1| * (2 - ε) ≤ ε * (2 - ε) := mul_le_mul_of_nonneg_right h h0.le
    _ ≤ ε * (1 + r) := mul_le_mul_of_nonneg_left h1 hε0

/-- **(A) at `ℤ₂`: the twist ratio from the electric ratio.** -/
theorem ratio_le_of_elec {r η : ℝ} (hr : 0 < r) (hη : η < 1) (h : |(1 - r) / (1 + r)| ≤ η) :
    |r - 1| ≤ 2 * η / (1 - η) := by
  have h1r : 0 < 1 + r := by linarith
  set E := (1 - r) / (1 + r) with hEdef
  have key : (r - 1) * (1 + E) = -2 * E := by
    rw [hEdef]
    field_simp
    ring
  have hE := abs_le.mp h
  have h0 : 0 < 1 - η := by linarith
  have hd : 1 - η ≤ 1 + E := by linarith
  have habs : |r - 1| * (1 + E) = 2 * |E| := by
    rw [← abs_of_pos (by linarith : (0 : ℝ) < 1 + E), ← abs_mul, key, abs_mul]
    norm_num
  rw [le_div_iff₀ h0]
  calc |r - 1| * (1 - η) ≤ |r - 1| * (1 + E) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = 2 * |E| := habs
    _ ≤ 2 * η := by linarith

/-! ## 2. The box twist ratio and the box kernel -/

variable {N : ℕ}

/-- The boundary condition `ω` acted on linkwise by `τ`. -/
def twistBd (τ : ILink → SU N ≃ᵐ SU N) (ω : IConf (SU N)) : IConf (SU N) :=
  twistConf (Equiv.refl ILink) τ ω

/-- `Z_Λ(ω)`, the Wilson box partition function at boundary `ω`. -/
def boxPart (β : ℝ) (Λ : Finset ILink) (ω : IConf (SU N)) : ℝ :=
  part (wilsonDensity (N := N)) β Λ (probHaar (SU N)) ω

/-- `N_Λ(f | ω)`, the unnormalised box expectation. -/
def boxNum (β : ℝ) (Λ : Finset ILink) (f : C(IConf (SU N), ℝ)) (ω : IConf (SU N)) : ℝ :=
  num (wilsonDensity (N := N)) β Λ (probHaar (SU N)) (⇑f) ω

/-- **The box twist ratio** `Z_Λ(τ ω)/Z_Λ(ω)`. -/
def boxRatio (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N) (ω : IConf (SU N)) : ℝ :=
  boxPart β Λ (twistBd τ ω) / boxPart β Λ ω

/-- **BoundaryV at one coupling** (named input, not proved): the box twist ratio within `ε` of `1` at every
boundary condition. -/
def BoundaryVAt (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N) (ε : ℝ) : Prop :=
  ∀ ω, |boxRatio β Λ τ ω - 1| ≤ ε

/-- **BoundaryV** (named input, not proved): for all large `β`, the box `Λ β` (intended: physical size `b`)
has twist ratio within `A e^{−σ b}` of `1` at every boundary condition. -/
def BoundaryV (σ A b : ℝ) (Λ : ℝ → Finset ILink) (τ : ℝ → ILink → SU N ≃ᵐ SU N) : Prop :=
  ∀ᶠ β in atTop, BoundaryVAt β (Λ β) (τ β) (A * Real.exp (-(σ * b)))

/-- **The loop-inserted twist comparison** (named input, not proved). `BoundaryVAt` is its `X = 1` case. -/
def LoopTwistAt (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N) (X : C(IConf (SU N), ℝ))
    (ε' : ℝ) : Prop :=
  ∀ ω, |(boxNum β Λ X (twistBd τ ω) - boxNum β Λ X ω) / boxPart β Λ ω| ≤ ε'

theorem boxPart_pos (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (ω : IConf (SU N)) :
    0 < boxPart β Λ ω :=
  part_pos measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β Λ _ ω

theorem wspec_eq_div (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (f : C(IConf (SU N), ℝ))
    (ω : IConf (SU N)) : wspec hN β Λ f ω = boxNum β Λ f ω / boxPart β Λ ω := rfl

/-- **BoundaryV with LoopTwist moves the kernel little along the twist.** -/
theorem spec_twist_shift_le (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N)
    (X : C(IConf (SU N), ℝ)) {ε ε' M : ℝ} (hε1 : ε < 1) (hV : BoundaryVAt β Λ τ ε)
    (hL : LoopTwistAt β Λ τ X ε') (hM : ∀ ω, |wspec hN β Λ X ω| ≤ M) (ω : IConf (SU N)) :
    |wspec hN β Λ X (twistBd τ ω) - wspec hN β Λ X ω| ≤ (ε' + M * ε) / (1 - ε) := by
  rw [wspec_eq_div, wspec_eq_div]
  have h := shift_le (boxPart_pos hN β Λ ω) (boxPart_pos hN β Λ (twistBd τ ω)) hε1 (hV ω) (hL ω)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hV ω)
  have hc : |boxNum β Λ X ω / boxPart β Λ ω| ≤ M := hM ω
  refine h.trans (div_le_div_of_nonneg_right ?_ (by linarith))
  linarith [mul_le_mul_of_nonneg_right hc hε0]

/-- `KernelNear δ` puts every two boundary conditions within `2δ`. -/
theorem pairs_of_kernelNear (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X : C(IConf (SU N), ℝ))
    {δ : ℝ} (hK : KernelNear hN β Λ X δ) (ω ω' : IConf (SU N)) :
    |wspec hN β Λ X ω' - wspec hN β Λ X ω| ≤ 2 * δ := by
  obtain ⟨c, hc⟩ := hK
  calc _ = |(wspec hN β Λ X ω' - c) - (wspec hN β Λ X ω - c)| := by ring_nf
    _ ≤ |wspec hN β Λ X ω' - c| + |wspec hN β Λ X ω - c| := abs_sub _ _
    _ ≤ 2 * δ := by linarith [hc ω, hc ω']

/-- Closeness at every pair is `KernelNear`. -/
theorem kernelNear_of_pairs (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X : C(IConf (SU N), ℝ))
    {δ : ℝ} (h : ∀ ω ω', |wspec hN β Λ X ω' - wspec hN β Λ X ω| ≤ δ) :
    KernelNear hN β Λ X δ :=
  ⟨wspec hN β Λ X (fun _ => 1), fun ω => h _ ω⟩

/-- **The target implies LoopTwist** (given BoundaryV): `LoopTwist` is part of `KernelNear`'s content. -/
theorem loopTwist_of_kernelNear (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N)
    (X : C(IConf (SU N), ℝ)) {δ ε M : ℝ} (hK : KernelNear hN β Λ X δ) (hV : BoundaryVAt β Λ τ ε)
    (hM : ∀ ω, |wspec hN β Λ X ω| ≤ M) :
    LoopTwistAt β Λ τ X (2 * δ * (1 + ε) + M * ε) := by
  intro ω
  have hS := pairs_of_kernelNear hN β Λ X hK ω (twistBd τ ω)
  rw [wspec_eq_div, wspec_eq_div] at hS
  have h := loopTwist_bound_of_shift (boxPart_pos hN β Λ ω) (boxPart_pos hN β Λ (twistBd τ ω))
    (hV ω) hS
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hV ω)
  have hc : |boxNum β Λ X ω / boxPart β Λ ω| ≤ M := hM ω
  linarith [mul_le_mul_of_nonneg_right hc hε0]

/-! ## 3. The box twist ratio as a box expectation; its ν-mean -/

/-- `R(U) = exp(−β (S_∂Λ(τ U) − S_∂Λ(U)))`, as a function. -/
def reweightFun (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N) (U : IConf (SU N)) : ℝ :=
  Real.exp (-β * (actionOn wilsonDensity (boundaryPlaqs Λ) (twistConf (Equiv.refl ILink) τ U)
    - actionOn wilsonDensity (boundaryPlaqs Λ) U))

/-- `R` as a continuous observable. -/
def reweight (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N) (hτc : ∀ l, Continuous (τ l)) :
    C(IConf (SU N), ℝ) where
  toFun := reweightFun β Λ τ
  continuous_toFun := Real.continuous_exp.comp (continuous_const.mul
    (((continuous_actionOn continuous_wilsonDensity (boundaryPlaqs Λ)).comp
      (continuous_twistConf (Equiv.refl ILink) τ hτc)).sub
      (continuous_actionOn continuous_wilsonDensity (boundaryPlaqs Λ))))

/-- A twist that is the identity on the box commutes with splicing into the box. -/
theorem twistConf_splice_refl {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (u : VConf (SU N) Λ) (ω : IConf (SU N)) :
    twistConf (Equiv.refl ILink) τ (splice Λ u ω) = splice Λ u (twistBd τ ω) := by
  unfold twistBd
  funext l
  by_cases hl : l ∈ Λ
  · simp only [twistConf, Equiv.refl_apply, splice_mem hl, hτΛ l hl]
  · simp only [twistConf, Equiv.refl_apply, splice_not_mem hl]

theorem reweight_mul_wt (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (u : VConf (SU N) Λ) (ω : IConf (SU N)) :
    reweightFun β Λ τ (splice Λ u ω) * wt wilsonDensity β Λ u ω
      = wt wilsonDensity β Λ u (twistBd τ ω) := by
  unfold reweightFun wt
  rw [twistConf_splice_refl hτΛ, ← Real.exp_add]
  congr 1
  ring

theorem num_reweight (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (ω : IConf (SU N)) :
    boxNum β Λ (reweight β Λ τ hτc) ω = boxPart β Λ (twistBd τ ω) := by
  unfold boxNum boxPart num part
  congr 1
  funext u
  exact reweight_mul_wt β hτΛ u ω

/-- **The box twist ratio is the box expectation of `R`**: `γ_Λ R (ω) = Z_Λ(τω)/Z_Λ(ω)`. -/
theorem wspec_reweight (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (ω : IConf (SU N)) :
    wspec hN β Λ (reweight β Λ τ hτc) ω = boxRatio β Λ τ ω := by
  rw [wspec_eq_div, num_reweight β hτc hτΛ]
  rfl

/-- **Box = whole, in mean**: the periodic-state mean of the box twist ratio (as `γ_Λ R`) is `ν(R)`. -/
theorem mean_boxRatio (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) :
    periodicState hN β (wspec hN β Λ (reweight β Λ τ hτc))
      = periodicState hN β (reweight β Λ τ hτc) :=
  periodicState_dlr hN β Λ _

/-- With `X` blind to the twist off the box: `N_Λ(X R | ω) = N_Λ(X | τ ω)`. -/
theorem num_mul_reweight (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (X : C(IConf (SU N), ℝ))
    (hX : ∀ (u : VConf (SU N) Λ) ω, X (splice Λ u (twistBd τ ω)) = X (splice Λ u ω))
    (ω : IConf (SU N)) :
    boxNum β Λ (X * reweight β Λ τ hτc) ω = boxNum β Λ X (twistBd τ ω) := by
  unfold boxNum num
  congr 1
  funext u
  show X (splice Λ u ω) * reweightFun β Λ τ (splice Λ u ω) * wt wilsonDensity β Λ u ω
    = X (splice Λ u (twistBd τ ω)) * wt wilsonDensity β Λ u (twistBd τ ω)
  rw [mul_assoc, reweight_mul_wt β hτΛ u ω, hX]

/-- **The loop-inserted twist ratio in mean**: `ν(N_Λ(X|τ·)/Z_Λ(·)) = ν(X R)`. -/
theorem mean_loopTwist (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (X : C(IConf (SU N), ℝ))
    (hX : ∀ (u : VConf (SU N) Λ) ω, X (splice Λ u (twistBd τ ω)) = X (splice Λ u ω)) :
    (∀ ω, wspec hN β Λ (X * reweight β Λ τ hτc) ω = boxNum β Λ X (twistBd τ ω) / boxPart β Λ ω) ∧
      periodicState hN β (wspec hN β Λ (X * reweight β Λ τ hτc))
        = periodicState hN β (X * reweight β Λ τ hτc) :=
  ⟨fun ω => by rw [wspec_eq_div, num_mul_reweight β hτc hτΛ X hX], periodicState_dlr hN β Λ _⟩

/-- Jensen for a state: `(ν g)² ≤ ν(g g)`. -/
theorem sq_state_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : State X) (g : C(X, ℝ)) :
    (ν g) ^ 2 ≤ ν (g * g) := by
  set c := ν g with hc
  have e : (g - c • (1 : C(X, ℝ))) * (g - c • (1 : C(X, ℝ)))
      = g * g - (2 * c) • g + (c * c) • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  have h0 : 0 ≤ ν ((g - c • (1 : C(X, ℝ))) * (g - c • (1 : C(X, ℝ)))) :=
    ν.nonneg _ (fun x => mul_self_nonneg _)
  rw [e, ν.map_add, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_one, ← hc] at h0
  nlinarith

/-- **(B) a typical-set BoundaryV from a whole-system second moment**:
`ν((γ_Λ R − 1)²) ≤ ν((R − 1)²)`. -/
theorem mean_sq_boxRatio_le (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) :
    periodicState hN β ((wspec hN β Λ (reweight β Λ τ hτc) - 1) *
        (wspec hN β Λ (reweight β Λ τ hτc) - 1))
      ≤ periodicState hN β ((reweight β Λ τ hτc - 1) * (reweight β Λ τ hτc - 1)) := by
  set R := reweight β Λ τ hτc
  rw [← periodicState_dlr hN β Λ ((R - 1) * (R - 1))]
  refine (periodicState hN β).mono fun ω => ?_
  have h1 : wspec hN β Λ R ω - 1 = boxState hN β Λ ω (R - 1) := by
    rw [(boxState hN β Λ ω).map_sub, (boxState hN β Λ ω).map_one, boxState_apply]
  have h2 := sq_state_le (boxState hN β Λ ω) (R - 1)
  rw [boxState_apply] at h2
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
  rw [h1, ← sq]
  exact h2

end MassGap.BoxWhole

#print axioms MassGap.BoxWhole.spec_twist_shift_le
#print axioms MassGap.BoxWhole.loopTwist_of_kernelNear
#print axioms MassGap.BoxWhole.ratio_le_of_elec
#print axioms MassGap.BoxWhole.mean_loopTwist
#print axioms MassGap.BoxWhole.mean_sq_boxRatio_le
