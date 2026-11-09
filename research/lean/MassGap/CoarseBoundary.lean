import Mathlib
import MassGap.TypicalBoundary
import MassGap.GapSideExactDecimation

noncomputable section

/-!
# MassGap.CoarseBoundary — the box boundary read through coarse blocks

A bound on the spread of the box kernel `wspec β Λ F` over boundary conditions that reads every boundary
plaquette pays the number `n_k ≈ (dist / a_k)³` of boundary plaquettes of a box of fixed physical size,
either through `β_k` per plaquette or through the union bound against the vacuum width
(`TypicalBoundary.vacuum_width_tendsto_top`). This module reads the boundary through a fixed number `m` of
coarse blocks. It proves the closings that a coarse reading gives, the per-block constant of a coarse Gibbs
density, the fixed-count union bound, and what the exact decimation step does to a per-block constant.

## 1. Blocks (proved, generic)

* `BlockOsc g ε`: changing the coarse configuration in block `b` alone moves `g` by at most `ε b`.
* `abs_sub_le_sum`: `|g y − g y'| ≤ Σ_b ε b`, by switching one block at a time (`mix`, `abs_sub_mix_le`).
  `abs_sub_le_card_mul`: with `ε b ≤ e`, at most `m · e`: a fixed count times a per-block constant.

## 2. A screen (proved, generic)

A screen is a kernel `Q` for which both states read the box kernel unchanged, `νᵢ (Q (K f)) = νᵢ (K f)`.
* `coarse_closing`: if `Q (K f)` factors as `g ∘ c` through coarse variables `c x : ∀ b, Y b` and
  `BlockOsc g ε`, then `|ν₁ f − ν₂ f| ≤ Σ_b ε b`. `LocalClosing.local_closing` applied to `Q ∘ K`.
* `markov_comp`: a Markov screen after a Markov kernel is Markov, so `TypicalBoundary.typical_closing_rel`
  applies to `Q ∘ K` as well.

## 3. The per-block constant of a coarse Gibbs density (proved, generic)

`wRead μ h w = ∫ h w dμ / ∫ w dμ`, the reading of `h` under the weight `w`.
* `wRead_lower`, `wRead_le`, `wRead_osc`: two positive weights with `e^{−c} w ≤ w' ≤ e^c w` and
  `m ≤ h ≤ m + δ` give `|wRead h w − wRead h w'| ≤ (1 − e^{−2c}) δ` (a Doeblin bound, for a general
  reweighting).
* `ratio_of_log`, `abs_log_le_of_ratio`: a log-ratio bound and a two-sided ratio bound are the same.
* `coarseGibbs_osc`: for a coarse weight `w y z > 0` whose log has per-block oscillation `c_b` at every `z`,
  `|wRead h (w y) − wRead h (w y')| ≤ (1 − e^{−2 Σ_b c_b}) δ` at every pair `y, y'`.
  `blockOsc_coarseGibbs`: the per-block form, `ε_b = (1 − e^{−2 c_b}) δ`.
  With `m` blocks and `c_b ≤ c`, the constant `1 − e^{−2 m c}` does not contain `k`.

## 4. The fixed-count union bound (proved)

* `coarse_mass_le`: `μ((⋂_{b ∈ s} A_b)ᶜ) ≤ #s · τ` when every `μ(A_bᶜ) ≤ τ`. On a coarse good set the count
  is the number of coarse blocks.

## 5. The exact decimation step and a per-block constant (proved)

* `integral_blockOsc_log`: for a probability measure and a positive integrable family `f V R`, if
  `V ↦ log f V R` has per-block oscillation `c` at every `R`, then so does `V ↦ log ∫ f V R dR`.
* `effStep_blockOsc`: on the gauge instance (`GapSideExactDecimation.effStep`, `glueStep`), the effective
  density's per-block log-oscillation in the coarse links is at most the sup over the integrated fine
  variables of the fine density's.
* `glueStep_eq_off`: two coarse configurations that agree off the coarse link `l₀` give, at the same
  integrated variables, fine configurations that agree off the single fine link `eZ (inl (l₀, 0))`
  (`u₁ = V u₂⁻¹`). `effStep_blockOsc_of_fine`: the effective density's per-link log-oscillation at `l` is
  at most the fine density's at that one fine link.
  The a priori per-link bound passes through the exact step unchanged: the count does not enter it, and
  the bound does not shrink. Any decrease of the effective constant has to come from cancellation in the
  integral over the fine variables, which these bounds do not see.

## 6. The Wilson box (proved reductions)

* `ScreenBound hN M β F Δ`: a box, a support, a screen `Q` invariant for the torus and the infinite-volume
  state at `wspec F`, and the spread of `Q (wspec F)` at most `Δ`. `ScreenBound.closing`.
* `CoarseBound`: `ScreenBound` with `Q (wspec F)` factored through `m` coarse blocks and per-block
  oscillations summing to at most `Δ`; `screenBound_of_coarse`. `coarseBound_of_spread`: one block holding
  the whole boundary reproduces the spread, so the form carries content only when the blocks are coarse.
* `CoarseGibbsBound`: `Q (wspec F)` is the reading of a coarse Gibbs weight with per-block log-oscillations
  `c_b` and `(1 − e^{−2 Σ c_b}) δ ≤ Δ`; `screenBound_of_coarseGibbs`.
* `ScreenTypicalBound`: a Markov screen and a good set, read relative to the second moment
  (`TypicalBoundary.typical_closing_rel` on `Q ∘ wspec`); `ScreenTypicalBound.closing`.
  `CoarseTypicalBound`: the good set is cut out by `m` coarse blocks with per-block tails `τ`;
  `screenTypical_of_coarseTypical`, with the union bound `m τ` (section 4).
* `BoundPixel`, `BoundOnePoint`, `pixelPassage_of_bound`, `centringPixel_of_bound`, `clay_canonical_bound`:
  the pinned path with `hpos` read through any bound that closes the torus against the infinite volume.
  `clay_canonical_coarseGibbs`, `clay_canonical_coarseTypical`: the two instances.

## What stays open

`BoxPixel`, `OnePointPixel` and their typical forms are not proved, and neither are the coarse forms.
Remainder of (1b) on this route (typed): `BoundPixel hN c O t ℓ π₁ (CoarseTypicalBound hN) ∧
BoundOnePoint hN c O t ℓ π₂ (CoarseTypicalBound hN)` (`clay_canonical_coarseTypical`), or the same with
`CoarseGibbsBound` (`clay_canonical_coarseGibbs`).

1. The coarse factorisation is not an identity of the box kernel (argued). `wspec β Λ F ω` reads `ω` on
   `bdLinks Λ` through the holonomies of the boundary plaquettes (`WilsonDLR.isLocalOn_spec`), one gauge-
   invariant variable per boundary plaquette, `≈ n_k` of them. The exact decimation keeps integrated
   quantities (`Z_effDens`, `effIter_spec`, `vortex_exact`); a boundary condition is a point configuration
   and is not integrated, so there is no identity `wspec F = g ∘ c` with `c` a coarse block map.
   The coarse map enters only through a screen `Q` that both states leave invariant. A screen built from
   the specification is a larger box kernel (`spec_screen_eq`: `wspec Λ' (wspec Λ F) = wspec Λ' F`), which
   reads the fine face `bdLinks Λ'`: the count comes back at the outer face. A screen that reads only
   coarse variables is the conditional expectation onto them under a law of the fine variables given the
   coarse ones, and that law is common to the two states only through the effective density of the exact
   decimation (argued). What the coarse blocks do not capture is that conditional law: the effective
   density of the fine boundary variables given the coarse ones.
2. The per-block constant. Given a coarse Gibbs form, the constant is `1 − e^{−2 Σ c_b}` with `c_b` the
   per-block log-oscillation of the coarse weight, and it does not contain `k` when `m` and the `c_b` do not
   (`coarseGibbs_osc`). The a priori `c_b` comes from the fine density through the exact step unchanged
   (`effStep_blockOsc`), and a coarse link enters one fine link (`glueStep_eq_off`,
   `effStep_blockOsc_of_fine`). After `j` steps it enters one finest link and that link's
   `2(d − 1) = 6` plaquettes, so the a priori constant is `c_b = 2 β_k · 6 = 12 β_k` (Lean `β`, density
   in `[0, 2]`) (argued: the `j`-fold iteration and the plaquette count are not formalised here). The count is gone from it; `β_k` is
   not. A per-block constant fixed in physical units needs the integral over the fine variables to cancel
   the `β_k` (the effective coupling at the coarse scale is fixed only after integration), which is control
   of the effective density of the exact decimation at scale `a_{k₀}`, uniform in `k` (argued).
3. Smallness. With `m` and `Σ c_b` fixed, one coarse layer contracts by the fixed factor
   `1 − e^{−2 Σ c_b} < 1`; the sup-norm form (`CoarseGibbsBound`) still compares an oscillation `δ` of order
   `‖f‖₁ · osc O` with `√refMomentS`, which shrinks with the cell volume (the Doeblin-route mismatch)
   (argued). The relative form (`CoarseTypicalBound`) removes that comparison: the off-`G`
   part is relative to the second moment, and the mass of `Gᶜ` is `m τ` with `m` fixed (section 4), so the
   two clauses that conflicted on the fine set (`TypicalBoundary`, mass needs `θ` of order one, spread needs
   `θ ≲ 1/β_k`) both live at the coarse scale, where the coupling is fixed (argued). Both clauses then ask
   for the coarse effective density: its per-block tails `τ` and the spread of `Q (wspec F)` on the coarse
   good set.

The failing step is the same object in every clause: a bound on the exact effective density at a fixed
coarse scale, per block, uniform in `k`. That is the multi-scale effective-action control that
`GapSideExactDecimation.ExactEffectiveSmall` asks of the same `effIter` density for `hW` (argued: there
a pointwise twist-odd ratio bound at the crossing scale, here a per-block ratio bound and per-block tails
at the scale `a_{k₀}`; the Props differ, the object and the uniformity are the same).
-/

namespace MassGap.CoarseBoundary

open MeasureTheory Filter

/-! ## 1. Blocks -/

section Blocks

variable {ι : Type*} {Y : ι → Type*}

/-- **Per-block oscillation**: changing the configuration in block `b` alone moves `g` by at most `ε b`. -/
def BlockOsc (g : (∀ b, Y b) → ℝ) (ε : ι → ℝ) : Prop :=
  ∀ b (y y' : ∀ b, Y b), (∀ b', b' ≠ b → y b' = y' b') → |g y - g y'| ≤ ε b

variable [DecidableEq ι]

/-- The configuration equal to `y'` on the blocks in `s` and to `y` elsewhere. -/
def mix (s : Finset ι) (y y' : ∀ b, Y b) : ∀ b, Y b := fun b => if b ∈ s then y' b else y b

theorem abs_sub_mix_le {g : (∀ b, Y b) → ℝ} {ε : ι → ℝ} (h : BlockOsc g ε) (y y' : ∀ b, Y b)
    (s : Finset ι) : |g y - g (mix s y y')| ≤ ∑ b ∈ s, ε b := by
  induction s using Finset.induction_on with
  | empty =>
    have e : mix ∅ y y' = y := by
      funext b
      simp [mix]
    rw [e, sub_self, abs_zero, Finset.sum_empty]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hstep : |g (mix s y y') - g (mix (insert a s) y y')| ≤ ε a :=
      h a _ _ (fun b' hb' => by simp [mix, Finset.mem_insert, hb'])
    calc |g y - g (mix (insert a s) y y')|
        ≤ |g y - g (mix s y y')| + |g (mix s y y') - g (mix (insert a s) y y')| :=
          abs_sub_le _ _ _
      _ ≤ ∑ b ∈ s, ε b + ε a := add_le_add ih hstep
      _ = ε a + ∑ b ∈ s, ε b := add_comm _ _

variable [Fintype ι]

theorem mix_univ (y y' : ∀ b, Y b) : mix Finset.univ y y' = y' := by
  funext b
  simp [mix]

/-- **Block by block**: the per-block oscillations add up. -/
theorem abs_sub_le_sum {g : (∀ b, Y b) → ℝ} {ε : ι → ℝ} (h : BlockOsc g ε) (y y' : ∀ b, Y b) :
    |g y - g y'| ≤ ∑ b, ε b := by
  have := abs_sub_mix_le h y y' Finset.univ
  rwa [mix_univ] at this

/-- **A fixed count times a per-block constant.** -/
theorem abs_sub_le_card_mul {g : (∀ b, Y b) → ℝ} {ε : ι → ℝ} (h : BlockOsc g ε) {e : ℝ}
    (he : ∀ b, ε b ≤ e) (y y' : ∀ b, Y b) : |g y - g y'| ≤ Fintype.card ι * e := by
  refine (abs_sub_le_sum h y y').trans ?_
  calc ∑ b, ε b ≤ ∑ _b : ι, e := Finset.sum_le_sum fun b _ => he b
    _ = Fintype.card ι * e := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Blocks

/-! ## 2. A screen -/

section Screen

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}

/-- **The coarse closing**: a screen `Q` that both states leave invariant at `K f`, through which `Q (K f)`
factors over coarse blocks with per-block oscillation `ε`, bounds the difference of the two states on `f`
by `Σ_b ε b`. -/
theorem coarse_closing (K Q : C(X, ℝ) → C(X, ℝ)) (ν₁ ν₂ : MassGap.DLRLimit.State X) (f : C(X, ℝ))
    (h₁ : ν₁ (K f) = ν₁ f) (h₂ : ν₂ (K f) = ν₂ f)
    (q₁ : ν₁ (Q (K f)) = ν₁ (K f)) (q₂ : ν₂ (Q (K f)) = ν₂ (K f))
    (c : X → ∀ b, Y b) (g : (∀ b, Y b) → ℝ) (hfac : ∀ x, Q (K f) x = g (c x))
    {ε : ι → ℝ} (hosc : BlockOsc g ε) :
    |ν₁ f - ν₂ f| ≤ ∑ b, ε b :=
  MassGap.LocalClosing.local_closing (fun h => Q (K h)) ν₁ ν₂ f (q₁.trans h₁) (q₂.trans h₂)
    (fun x y => by
      show |Q (K f) x - Q (K f) y| ≤ _
      rw [hfac, hfac]
      exact abs_sub_le_sum hosc _ _)

end Screen

section MarkovComp

variable {X : Type*} [TopologicalSpace X]

open MassGap.TypicalBoundary in
/-- A Markov screen after a Markov kernel is Markov. -/
theorem markov_comp {Q K : C(X, ℝ) → C(X, ℝ)} (hQ : Markov Q) (hK : Markov K) :
    Markov (fun f => Q (K f)) where
  add f g := by simp only [hK.add, hQ.add]
  smul c f := by simp only [hK.smul, hQ.smul]
  one := by simp only [hK.one, hQ.one]
  pos f hf x := hQ.pos _ (hK.pos f hf) x

end MarkovComp

/-! ## 3. The per-block constant of a coarse Gibbs density -/

section Reweight

variable {Z : Type*} [MeasurableSpace Z]

/-- The reading of `h` under the positive weight `w`: `∫ h w dμ / ∫ w dμ`. -/
def wRead (μ : Measure Z) (h w : Z → ℝ) : ℝ := (∫ z, h z * w z ∂μ) / ∫ z, w z ∂μ

variable {μ : Measure Z}

theorem integrable_sub_mul {h w : Z → ℝ} (m : ℝ) (iw : Integrable w μ)
    (ihw : Integrable (fun z => h z * w z) μ) : Integrable (fun z => (h z - m) * w z) μ := by
  have e : (fun z => (h z - m) * w z) = fun z => h z * w z - m * w z := by
    funext z
    ring
  rw [e]
  exact ihw.sub (iw.const_mul m)

theorem wRead_sub (h w : Z → ℝ) (m : ℝ) (iw : Integrable w μ)
    (ihw : Integrable (fun z => h z * w z) μ) (hZ : 0 < ∫ z, w z ∂μ) :
    wRead μ h w - m = (∫ z, (h z - m) * w z ∂μ) / ∫ z, w z ∂μ := by
  have e : (fun z => (h z - m) * w z) = fun z => h z * w z - m * w z := by
    funext z
    ring
  unfold wRead
  rw [e, integral_sub ihw (iw.const_mul m), integral_const_mul, sub_div,
    mul_div_cancel_right₀ _ hZ.ne']

/-- The reading is below an upper bound of `h`. -/
theorem wRead_le {h w : Z → ℝ} {M : ℝ} (hw : ∀ z, 0 < w z) (iw : Integrable w μ)
    (ihw : Integrable (fun z => h z * w z) μ) (hZ : 0 < ∫ z, w z ∂μ) (hM : ∀ z, h z ≤ M) :
    wRead μ h w ≤ M := by
  unfold wRead
  rw [div_le_iff₀ hZ, ← integral_const_mul]
  exact integral_mono ihw (iw.const_mul M) fun z => mul_le_mul_of_nonneg_right (hM z) (hw z).le

/-- **The lower reweighting bound**: `e^{−c} w ≤ w' ≤ e^c w` and `m ≤ h` give
`e^{−2c} (wRead h w − m) ≤ wRead h w' − m`. -/
theorem wRead_lower {h w w' : Z → ℝ} {c m : ℝ} (hw : ∀ z, 0 < w z)
    (hlo : ∀ z, Real.exp (-c) * w z ≤ w' z) (hhi : ∀ z, w' z ≤ Real.exp c * w z)
    (iw : Integrable w μ) (iw' : Integrable w' μ) (ihw : Integrable (fun z => h z * w z) μ)
    (ihw' : Integrable (fun z => h z * w' z) μ) (hZ : 0 < ∫ z, w z ∂μ) (hm : ∀ z, m ≤ h z) :
    Real.exp (-(2 * c)) * (wRead μ h w - m) ≤ wRead μ h w' - m := by
  have hZ'lo : Real.exp (-c) * ∫ z, w z ∂μ ≤ ∫ z, w' z ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (iw.const_mul _) iw' hlo
  have hZ' : 0 < ∫ z, w' z ∂μ := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hZ) hZ'lo
  have hZ'hi : ∫ z, w' z ∂μ ≤ Real.exp c * ∫ z, w z ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono iw' (iw.const_mul _) hhi
  have iA := integrable_sub_mul m iw ihw
  have iA' := integrable_sub_mul m iw' ihw'
  have hA0 : 0 ≤ ∫ z, (h z - m) * w z ∂μ :=
    integral_nonneg fun z => mul_nonneg (sub_nonneg.mpr (hm z)) (hw z).le
  have key : Real.exp (-c) * ∫ z, (h z - m) * w z ∂μ ≤ ∫ z, (h z - m) * w' z ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (iA.const_mul _) iA' fun z => ?_
    have := mul_le_mul_of_nonneg_left (hlo z) (sub_nonneg.mpr (hm z))
    show Real.exp (-c) * ((h z - m) * w z) ≤ (h z - m) * w' z
    nlinarith
  rw [wRead_sub h w m iw ihw hZ, wRead_sub h w' m iw' ihw' hZ', le_div_iff₀ hZ']
  set A := ∫ z, (h z - m) * w z ∂μ
  set A' := ∫ z, (h z - m) * w' z ∂μ
  set Zw := ∫ z, w z ∂μ
  set Zw' := ∫ z, w' z ∂μ
  have he : Real.exp (-(2 * c)) * Real.exp c = Real.exp (-c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hq : 0 ≤ A / Zw := div_nonneg hA0 hZ.le
  have h1 : Real.exp (-(2 * c)) * (A / Zw) * Zw' ≤ Real.exp (-(2 * c)) * (A / Zw) * (Real.exp c * Zw) :=
    mul_le_mul_of_nonneg_left hZ'hi (mul_nonneg (Real.exp_pos _).le hq)
  have h2 : Real.exp (-(2 * c)) * (A / Zw) * (Real.exp c * Zw) = Real.exp (-c) * A := by
    calc Real.exp (-(2 * c)) * (A / Zw) * (Real.exp c * Zw)
        = (Real.exp (-(2 * c)) * Real.exp c) * (A / Zw * Zw) := by ring
      _ = Real.exp (-c) * A := by rw [he, div_mul_cancel₀ _ hZ.ne']
  linarith

/-- **Reweighting by a bounded ratio moves the reading by at most `(1 − e^{−2c}) δ`.** -/
theorem wRead_osc {h w w' : Z → ℝ} {c m δ : ℝ} (hc : 0 ≤ c) (hw : ∀ z, 0 < w z)
    (hw' : ∀ z, 0 < w' z) (hlo : ∀ z, Real.exp (-c) * w z ≤ w' z)
    (hhi : ∀ z, w' z ≤ Real.exp c * w z) (iw : Integrable w μ) (iw' : Integrable w' μ)
    (ihw : Integrable (fun z => h z * w z) μ) (ihw' : Integrable (fun z => h z * w' z) μ)
    (hZ : 0 < ∫ z, w z ∂μ) (hZ' : 0 < ∫ z, w' z ∂μ) (hh : ∀ z, m ≤ h z ∧ h z ≤ m + δ) :
    |wRead μ h w - wRead μ h w'| ≤ (1 - Real.exp (-(2 * c))) * δ := by
  have hlo' : ∀ z, Real.exp (-c) * w' z ≤ w z := fun z => by
    have := mul_le_mul_of_nonneg_left (hhi z) (Real.exp_pos (-c)).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at this
    exact this
  have hhi' : ∀ z, w z ≤ Real.exp c * w' z := fun z => by
    have := mul_le_mul_of_nonneg_left (hlo z) (Real.exp_pos c).le
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
    exact this
  have l1 := wRead_lower hw hlo hhi iw iw' ihw ihw' hZ (fun z => (hh z).1)
  have l2 := wRead_lower hw' hlo' hhi' iw' iw ihw' ihw hZ' (fun z => (hh z).1)
  have u1 := wRead_le hw iw ihw hZ (fun z => (hh z).2)
  have u2 := wRead_le hw' iw' ihw' hZ' (fun z => (hh z).2)
  have he1 : 0 ≤ 1 - Real.exp (-(2 * c)) := by
    have : Real.exp (-(2 * c)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have p1 := mul_le_mul_of_nonneg_left (show wRead μ h w - m ≤ δ by linarith) he1
  have p2 := mul_le_mul_of_nonneg_left (show wRead μ h w' - m ≤ δ by linarith) he1
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- A log-ratio bound is a two-sided ratio bound. -/
theorem ratio_of_log {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : |Real.log a - Real.log b| ≤ c) :
    Real.exp (-c) * a ≤ b ∧ b ≤ Real.exp c * a := by
  have h' := abs_le.mp h
  constructor
  · calc Real.exp (-c) * a = Real.exp (-c + Real.log a) := by rw [Real.exp_add, Real.exp_log ha]
      _ ≤ Real.exp (Real.log b) := Real.exp_le_exp.mpr (by linarith [h'.2])
      _ = b := Real.exp_log hb
  · calc b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ ≤ Real.exp (c + Real.log a) := Real.exp_le_exp.mpr (by linarith [h'.1])
      _ = Real.exp c * a := by rw [Real.exp_add, Real.exp_log ha]

/-- A two-sided ratio bound is a log-ratio bound. -/
theorem abs_log_le_of_ratio {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (h1 : Real.exp (-c) * A ≤ B)
    (h2 : B ≤ Real.exp c * A) : |Real.log A - Real.log B| ≤ c := by
  have l1 := Real.log_le_log (mul_pos (Real.exp_pos _) hA) h1
  rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp] at l1
  have l2 := Real.log_le_log hB h2
  rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp] at l2
  rw [abs_le]
  constructor <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}

/-- **The coarse Doeblin bound**: a coarse weight whose log has per-block oscillation `c_b` at every `z`
moves the reading by at most `(1 − e^{−2 Σ_b c_b}) δ` between any two coarse configurations. -/
theorem coarseGibbs_osc (h : Z → ℝ) (w : (∀ b, Y b) → Z → ℝ) {cb : ι → ℝ} {m δ : ℝ}
    (hw : ∀ y z, 0 < w y z) (iw : ∀ y, Integrable (w y) μ)
    (ihw : ∀ y, Integrable (fun z => h z * w y z) μ) (hZ : ∀ y, 0 < ∫ z, w y z ∂μ)
    (hh : ∀ z, m ≤ h z ∧ h z ≤ m + δ) (hosc : ∀ z, BlockOsc (fun y => Real.log (w y z)) cb)
    (hcb : ∀ b, 0 ≤ cb b) (y y' : ∀ b, Y b) :
    |wRead μ h (w y) - wRead μ h (w y')| ≤ (1 - Real.exp (-(2 * ∑ b, cb b))) * δ := by
  have r : ∀ z, Real.exp (-(∑ b, cb b)) * w y z ≤ w y' z ∧ w y' z ≤ Real.exp (∑ b, cb b) * w y z :=
    fun z => ratio_of_log (hw y z) (hw y' z) (abs_sub_le_sum (hosc z) y y')
  exact wRead_osc (Finset.sum_nonneg fun b _ => hcb b) (hw y) (hw y') (fun z => (r z).1)
    (fun z => (r z).2) (iw y) (iw y') (ihw y) (ihw y') (hZ y) (hZ y') hh

omit [Fintype ι] [DecidableEq ι] in
/-- **The per-block form**: the reading has per-block oscillation `(1 − e^{−2 c_b}) δ`. -/
theorem blockOsc_coarseGibbs (h : Z → ℝ) (w : (∀ b, Y b) → Z → ℝ) {cb : ι → ℝ} {m δ : ℝ}
    (hw : ∀ y z, 0 < w y z) (iw : ∀ y, Integrable (w y) μ)
    (ihw : ∀ y, Integrable (fun z => h z * w y z) μ) (hZ : ∀ y, 0 < ∫ z, w y z ∂μ)
    (hh : ∀ z, m ≤ h z ∧ h z ≤ m + δ) (hosc : ∀ z, BlockOsc (fun y => Real.log (w y z)) cb)
    (hcb : ∀ b, 0 ≤ cb b) :
    BlockOsc (fun y => wRead μ h (w y)) (fun b => (1 - Real.exp (-(2 * cb b))) * δ) := by
  intro b y y' hy
  have r : ∀ z, Real.exp (-(cb b)) * w y z ≤ w y' z ∧ w y' z ≤ Real.exp (cb b) * w y z :=
    fun z => ratio_of_log (hw y z) (hw y' z) (hosc z b y y' hy)
  exact wRead_osc (hcb b) (hw y) (hw y') (fun z => (r z).1) (fun z => (r z).2) (iw y) (iw y')
    (ihw y) (ihw y') (hZ y) (hZ y') hh

end Reweight

/-! ## 4. The fixed-count union bound -/

section Mass

/-- **The union bound over coarse blocks**: the mass off `⋂_{b ∈ s} A_b` is at most `#s · τ`. -/
theorem coarse_mass_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {ι : Type*} (s : Finset ι) (A : ι → Set X) (τ : ℝ) (hτ : ∀ b ∈ s, μ.real (A b)ᶜ ≤ τ) :
    μ.real (⋂ b ∈ s, A b)ᶜ ≤ s.card * τ := by
  rw [Set.compl_iInter₂]
  calc μ.real (⋃ b ∈ s, (A b)ᶜ) ≤ ∑ b ∈ s, μ.real (A b)ᶜ := measureReal_biUnion_finset_le _ _
    _ ≤ s.card • τ := Finset.sum_le_card_nsmul _ _ _ hτ
    _ = s.card * τ := nsmul_eq_mul _ _

end Mass

/-! ## 5. The exact decimation step and a per-block constant -/

section Exact

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}

omit [Fintype ι] [DecidableEq ι] in
/-- **Integrating out passes a per-block log-oscillation down unchanged.** -/
theorem integral_blockOsc_log {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : (∀ b, Y b) → Ω → ℝ) (hpos : ∀ V R, 0 < f V R) (hint : ∀ V, Integrable (f V) μ)
    {c : ι → ℝ} (hosc : ∀ R, BlockOsc (fun V => Real.log (f V R)) c) :
    BlockOsc (fun V => Real.log (∫ R, f V R ∂μ)) c := by
  intro b V V' hV
  have hI : ∀ V, 0 < ∫ R, f V R ∂μ := fun V => by
    rw [integral_pos_iff_support_of_nonneg (fun R => (hpos V R).le) (hint V)]
    rw [show Function.support (f V) = Set.univ from
      Set.eq_univ_of_forall fun R => (hpos V R).ne', measure_univ]
    exact one_pos
  have r : ∀ R, Real.exp (-c b) * f V R ≤ f V' R ∧ f V' R ≤ Real.exp (c b) * f V R :=
    fun R => ratio_of_log (hpos V R) (hpos V' R) (hosc R b V V' hV)
  have h1 : ∫ R, f V' R ∂μ ≤ Real.exp (c b) * ∫ R, f V R ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (hint V') ((hint V).const_mul _) fun R => (r R).2
  have h2 : Real.exp (-c b) * ∫ R, f V R ∂μ ≤ ∫ R, f V' R ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono ((hint V).const_mul _) (hint V') fun R => (r R).1
  exact abs_log_le_of_ratio (hI V) (hI V') h2 h1

open MassGap.GapSideExactDecimation MassGap.TorusDoubling MassGap.SUN in
/-- **One exact step on the gauge instance**: the effective density's per-block log-oscillation in the
coarse links is at most the fine density's, at every value of the integrated fine variables. -/
theorem effStep_blockOsc (n : ℕ) (ρ : DensE (2 * n)) (ζ : TPlaq 4 n → SU 2)
    (hpos : ∀ V R, 0 < ρ (pullTw ζ) (glueStep n (V, R)))
    (hint : ∀ V, Integrable (fun R => ρ (pullTw ζ) (glueStep n (V, R))) (restM n))
    {c : TLink 4 n → ℝ}
    (hosc : ∀ R, BlockOsc (Y := fun _ : TLink 4 n => SU 2)
      (fun V => Real.log (ρ (pullTw ζ) (glueStep n (V, R)))) c) :
    BlockOsc (Y := fun _ : TLink 4 n => SU 2) (fun V => Real.log (effStep n ρ ζ V)) c :=
  integral_blockOsc_log (Y := fun _ : TLink 4 n => SU 2) (restM n)
    (fun V R => ρ (pullTw ζ) (glueStep n (V, R))) hpos hint hosc

open MassGap.GapSideExactDecimation MassGap.TorusDoubling MassGap.SUN in
/-- **A coarse link enters one fine link.** Two coarse configurations that agree off the coarse link
`l₀` give fine configurations, at the same integrated variables, that agree off the first fine link
`eZ (inl (l₀, 0))` of its line: `u₁ = V u₂⁻¹` carries `V`, `u₂` and every other fine link do not. -/
theorem glueStep_eq_off (n : ℕ) (V V' : TLink 4 n → SU 2) (R : RestV n) (l₀ : TLink 4 n)
    (hV : ∀ l, l ≠ l₀ → V l = V' l) (ℓ : TLink 4 (2 * n))
    (hℓ : ℓ ≠ MassGap.MovedTorusDecimation.eZ (Sum.inl (l₀, 0))) :
    glueStep n (V, R) ℓ = glueStep n (V', R) ℓ := by
  unfold glueStep MassGap.MovedTorusDecimation.asm
  cases h : MassGap.MovedTorusDecimation.enc.symm ℓ with
  | inr c => rfl
  | inl z =>
    cases z with
    | inr xm => rfl
    | inl ls =>
      obtain ⟨l, s⟩ := ls
      show MassGap.MovedTorusDecimation.sel2 (V l / R.1 l, R.1 l) s
        = MassGap.MovedTorusDecimation.sel2 (V' l / R.1 l, R.1 l) s
      by_cases hl : l = l₀
      · subst hl
        match s, h with
        | 0, h =>
          exact absurd ((MassGap.MovedTorusDecimation.enc.symm_apply_eq.mp h).trans
            (MassGap.MovedTorusDecimation.enc_inl _)) hℓ
        | 1, _ => rfl
      · rw [hV l hl]

open MassGap.GapSideExactDecimation MassGap.TorusDoubling MassGap.SUN in
/-- **One exact step passes the per-link constant of the fine density to the coarse links.** If the
log of the fine density has per-link oscillation `c'`, the log of the effective density has, at the
coarse link `l`, per-link oscillation `c' (eZ (inl (l, 0)))`: one fine link's constant. -/
theorem effStep_blockOsc_of_fine (n : ℕ) (ρ : DensE (2 * n)) (ζ : TPlaq 4 n → SU 2)
    (hpos : ∀ V R, 0 < ρ (pullTw ζ) (glueStep n (V, R)))
    (hint : ∀ V, Integrable (fun R => ρ (pullTw ζ) (glueStep n (V, R))) (restM n))
    {c' : TLink 4 (2 * n) → ℝ}
    (hfine : BlockOsc (Y := fun _ : TLink 4 (2 * n) => SU 2)
      (fun U => Real.log (ρ (pullTw ζ) U)) c') :
    BlockOsc (Y := fun _ : TLink 4 n => SU 2) (fun V => Real.log (effStep n ρ ζ V))
      (fun l => c' (MassGap.MovedTorusDecimation.eZ (Sum.inl (l, 0)))) :=
  effStep_blockOsc n ρ ζ hpos hint (fun R l V V' hV =>
    hfine (MassGap.MovedTorusDecimation.eZ (Sum.inl (l, 0))) _ _
      (fun ℓ hℓ => glueStep_eq_off n V V' R l hV ℓ hℓ))

end Exact

/-! ## 6. The Wilson box -/

section Wilson

open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.PeriodicState MassGap.LocalClosing
  MassGap.TypicalBoundary
open MassGap.DLRLimit (gibbsMeasure IsLocalOnC)

variable {N : ℕ}

/-- A screen built from the specification is the larger box kernel. -/
theorem spec_screen_eq (hN : N ≠ 0) (β : ℝ) {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) : wspec hN β Λ' (wspec hN β Λ F) = wspec hN β Λ' F :=
  (periodicState_dlr_nested hN β hsub F).1

/-- **A screen bound**: a box and support that fit in the torus of extent `M + 1`, a screen `Q` that the
torus and the infinite-volume state leave invariant at `wspec F`, and the spread of `Q (wspec F)` at most
`Δ`. -/
def ScreenBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) : Prop :=
  ∃ (Λ S : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)),
    IsLocalOnC S F ∧ BoxFits M Λ S
    ∧ torusState hN M β (Q (wspec hN β Λ F)) = torusState hN M β (wspec hN β Λ F)
    ∧ periodicState hN β (Q (wspec hN β Λ F)) = periodicState hN β (wspec hN β Λ F)
    ∧ ∀ ω ω', |Q (wspec hN β Λ F) ω - Q (wspec hN β Λ F) ω'| ≤ Δ

theorem ScreenBound.closing {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {Δ : ℝ} (h : ScreenBound hN M β F Δ) :
    |torusState hN M β F - periodicState hN β F| ≤ Δ := by
  obtain ⟨Λ, S, Q, hloc, hfit, hT, hP, hosc⟩ := h
  exact local_closing (fun g => Q (wspec hN β Λ g)) _ _ F
    (hT.trans (torusState_dlr hN M β Λ S F hloc hfit.1 hfit.2))
    (hP.trans (periodicState_dlr hN β Λ F)) hosc

/-- **A coarse bound**: a screen bound whose `Q (wspec F)` factors through `m` coarse blocks with
per-block oscillations summing to at most `Δ`. -/
def CoarseBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) : Prop :=
  ∃ (Λ S : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ)
    (Y : Fin m → Type) (c : IConf (MassGap.SUN.SU N) → ∀ b, Y b) (g : (∀ b, Y b) → ℝ)
    (ε : Fin m → ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S
    ∧ torusState hN M β (Q (wspec hN β Λ F)) = torusState hN M β (wspec hN β Λ F)
    ∧ periodicState hN β (Q (wspec hN β Λ F)) = periodicState hN β (wspec hN β Λ F)
    ∧ (∀ ω, Q (wspec hN β Λ F) ω = g (c ω)) ∧ BlockOsc g ε ∧ ∑ b, ε b ≤ Δ

theorem screenBound_of_coarse {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {Δ : ℝ} (h : CoarseBound hN M β F Δ) : ScreenBound hN M β F Δ := by
  obtain ⟨Λ, S, Q, m, Y, c, g, ε, hloc, hfit, hT, hP, hfac, hosc, hle⟩ := h
  exact ⟨Λ, S, Q, hloc, hfit, hT, hP, fun ω ω' => by
    rw [hfac, hfac]
    exact (abs_sub_le_sum hosc _ _).trans hle⟩

/-- **One block holding the whole boundary is the spread**: a coarse bound carries content only when
its blocks are coarse. -/
theorem coarseBound_of_spread (hN : N ≠ 0) {M : ℕ} {β : ℝ} {Λ S : Finset ILink}
    {F : C(IConf (MassGap.SUN.SU N), ℝ)} (hloc : IsLocalOnC S F) (hfit : BoxFits M Λ S) {d : ℝ}
    (hosc : ∀ ω ω', |wspec hN β Λ F ω - wspec hN β Λ F ω'| ≤ d) : CoarseBound hN M β F d :=
  ⟨Λ, S, fun g => g, 1, fun _ => IConf (MassGap.SUN.SU N), fun ω _ => ω,
    fun y => wspec hN β Λ F (y 0), fun _ => d, hloc, hfit, rfl, rfl, fun _ => rfl,
    fun _ _ _ _ => hosc _ _, by simp⟩

/-- **A coarse Gibbs bound**: a screen bound whose `Q (wspec F)` is the reading of a coarse Gibbs weight
over `m` blocks with per-block log-oscillations `c_b`, and `(1 − e^{−2 Σ c_b}) δ ≤ Δ`. -/
def CoarseGibbsBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) :
    Prop :=
  ∃ (Λ S : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ)
    (Y : Fin m → Type) (c : IConf (MassGap.SUN.SU N) → ∀ b, Y b)
    (μ : Measure (IConf (MassGap.SUN.SU N))) (h : IConf (MassGap.SUN.SU N) → ℝ)
    (w : (∀ b, Y b) → IConf (MassGap.SUN.SU N) → ℝ) (cb : Fin m → ℝ) (lo δ : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S
    ∧ torusState hN M β (Q (wspec hN β Λ F)) = torusState hN M β (wspec hN β Λ F)
    ∧ periodicState hN β (Q (wspec hN β Λ F)) = periodicState hN β (wspec hN β Λ F)
    ∧ (∀ ω, Q (wspec hN β Λ F) ω = wRead μ h (w (c ω)))
    ∧ (∀ y z, 0 < w y z) ∧ (∀ y, Integrable (w y) μ)
    ∧ (∀ y, Integrable (fun z => h z * w y z) μ) ∧ (∀ y, 0 < ∫ z, w y z ∂μ)
    ∧ (∀ z, lo ≤ h z ∧ h z ≤ lo + δ) ∧ (∀ z, BlockOsc (fun y => Real.log (w y z)) cb)
    ∧ (∀ b, 0 ≤ cb b) ∧ (1 - Real.exp (-(2 * ∑ b, cb b))) * δ ≤ Δ

theorem screenBound_of_coarseGibbs {hN : N ≠ 0} {M : ℕ} {β : ℝ}
    {F : C(IConf (MassGap.SUN.SU N), ℝ)} {Δ : ℝ} (h : CoarseGibbsBound hN M β F Δ) :
    ScreenBound hN M β F Δ := by
  obtain ⟨Λ, S, Q, m, Y, c, μ, hf, w, cb, lo, δ, hloc, hfit, hT, hP, hfac, hw, iw, ihw, hZ, hh,
    hosc, hcb, hle⟩ := h
  exact ⟨Λ, S, Q, hloc, hfit, hT, hP, fun ω ω' => by
    rw [hfac, hfac]
    exact (coarseGibbs_osc hf w hw iw ihw hZ hh hosc hcb _ _).trans hle⟩

/-- **A screen bound in typical, relative form**: a Markov screen `Q`, invariant for both states at
`wspec F` and at `wspec (sqDev F r)`, a measurable good set `G` on which `|Q (wspec F) − r| ≤ δ`, and
`2δ + √(μ_T(Gᶜ) V_T) + √(μ_∞(Gᶜ) V_∞) ≤ Δ`. -/
def ScreenTypicalBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) :
    Prop :=
  ∃ (Λ S : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ))
    (G : Set (IConf (MassGap.SUN.SU N))) (r δ : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ Markov Q
    ∧ torusState hN M β (Q (wspec hN β Λ F)) = torusState hN M β (wspec hN β Λ F)
    ∧ periodicState hN β (Q (wspec hN β Λ F)) = periodicState hN β (wspec hN β Λ F)
    ∧ torusState hN M β (Q (wspec hN β Λ (sqDev F r)))
        = torusState hN M β (wspec hN β Λ (sqDev F r))
    ∧ periodicState hN β (Q (wspec hN β Λ (sqDev F r)))
        = periodicState hN β (wspec hN β Λ (sqDev F r))
    ∧ MeasurableSet G ∧ 0 ≤ δ ∧ (∀ ω ∈ G, |Q (wspec hN β Λ F) ω - r| ≤ δ)
    ∧ 2 * δ + (Real.sqrt ((gibbsMeasure (torusState hN M β)).real Gᶜ
          * torusState hN M β (sqDev F r))
        + Real.sqrt ((gibbsMeasure (periodicState hN β)).real Gᶜ
          * periodicState hN β (sqDev F r))) ≤ Δ

theorem ScreenTypicalBound.closing {hN : N ≠ 0} {M : ℕ} {β : ℝ}
    {F : C(IConf (MassGap.SUN.SU N), ℝ)} {Δ : ℝ} (h : ScreenTypicalBound hN M β F Δ) :
    |torusState hN M β F - periodicState hN β F| ≤ Δ := by
  obtain ⟨Λ, S, Q, G, r, δ, hloc, hfit, hQ, hT, hP, hT2, hP2, hG, hδ, hgood, hle⟩ := h
  have hc := typical_closing_rel (markov_comp hQ (markov_wspec hN β Λ)) (torusState hN M β)
    (periodicState hN β) F (hT.trans (torusState_dlr hN M β Λ S F hloc hfit.1 hfit.2))
    (hP.trans (periodicState_dlr hN β Λ F))
    (hT2.trans (torusState_dlr hN M β Λ S _ (isLocalOnC_sqDev hloc r) hfit.1 hfit.2))
    (hP2.trans (periodicState_dlr hN β Λ _)) hG hδ hgood
  linarith

/-- **A coarse typical bound**: the good set of `ScreenTypicalBound` cut out by `m` coarse blocks, each
block's event `c ω b ∈ A b` measurable with complement of mass at most `τ` under both states, and
`2δ + √(m τ V_T) + √(m τ V_∞) ≤ Δ`. -/
def CoarseTypicalBound (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) (Δ : ℝ) :
    Prop :=
  ∃ (Λ S : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ)
    (Y : Fin m → Type) (c : IConf (MassGap.SUN.SU N) → ∀ b, Y b) (A : ∀ b, Set (Y b)) (r δ τ : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ Markov Q
    ∧ torusState hN M β (Q (wspec hN β Λ F)) = torusState hN M β (wspec hN β Λ F)
    ∧ periodicState hN β (Q (wspec hN β Λ F)) = periodicState hN β (wspec hN β Λ F)
    ∧ torusState hN M β (Q (wspec hN β Λ (sqDev F r)))
        = torusState hN M β (wspec hN β Λ (sqDev F r))
    ∧ periodicState hN β (Q (wspec hN β Λ (sqDev F r)))
        = periodicState hN β (wspec hN β Λ (sqDev F r))
    ∧ (∀ b, MeasurableSet {ω | c ω b ∈ A b}) ∧ 0 ≤ δ
    ∧ (∀ ω, (∀ b, c ω b ∈ A b) → |Q (wspec hN β Λ F) ω - r| ≤ δ)
    ∧ (∀ b, (gibbsMeasure (torusState hN M β)).real {ω | c ω b ∈ A b}ᶜ ≤ τ)
    ∧ (∀ b, (gibbsMeasure (periodicState hN β)).real {ω | c ω b ∈ A b}ᶜ ≤ τ)
    ∧ 2 * δ + (Real.sqrt (m * τ * torusState hN M β (sqDev F r))
        + Real.sqrt (m * τ * periodicState hN β (sqDev F r))) ≤ Δ

theorem screenTypical_of_coarseTypical {hN : N ≠ 0} {M : ℕ} {β : ℝ}
    {F : C(IConf (MassGap.SUN.SU N), ℝ)} {Δ : ℝ} (h : CoarseTypicalBound hN M β F Δ) :
    ScreenTypicalBound hN M β F Δ := by
  obtain ⟨Λ, S, Q, m, Y, c, A, r, δ, τ, hloc, hfit, hQ, hT, hP, hT2, hP2, hmeas, hδ, hgood, hτT,
    hτP, hle⟩ := h
  have hmT := coarse_mass_le (gibbsMeasure (torusState hN M β)) (Finset.univ : Finset (Fin m))
    (fun b => {ω | c ω b ∈ A b}) τ (fun b _ => hτT b)
  have hmP := coarse_mass_le (gibbsMeasure (periodicState hN β)) (Finset.univ : Finset (Fin m))
    (fun b => {ω | c ω b ∈ A b}) τ (fun b _ => hτP b)
  rw [Finset.card_univ, Fintype.card_fin] at hmT hmP
  refine ⟨Λ, S, Q, ⋂ b ∈ (Finset.univ : Finset (Fin m)), {ω | c ω b ∈ A b}, r, δ, hloc, hfit, hQ,
    hT, hP, hT2, hP2, Finset.measurableSet_biInter _ fun b _ => hmeas b, hδ,
    fun ω hω => hgood ω fun b => Set.mem_iInter₂.mp hω b (Finset.mem_univ b), ?_⟩
  have sT := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right hmT (sqDev_nonneg (torusState hN M β) F r))
  have sP := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right hmP (sqDev_nonneg (periodicState hN β) F r))
  linarith

end Wilson

/-! ## 7. The pinned path -/

section Pixel

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing

variable {N : ℕ}

/-- **`BoxPixel` through a bound `B`**: eventually in `k`, `B` holds for the infinite-volume composite in
the torus of `stateTD hN c k`, at `π · √(refMomentS)`. -/
def BoundPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ)
    (B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop) : Prop :=
  ∀ᶠ k in atTop, B (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k)
    (refObs (stateK hN k) O t ℓ k)
    (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k))

/-- **`OnePointPixel` through a bound `B`**: bounds `Δ₀`, `Δ₁` for the reflected and the plain
single-site field whose product with the cube weights is at most `π · √(refMomentS)`. -/
def BoundOnePoint (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ)
    (B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop) : Prop :=
  ∀ᶠ k in atTop, ∃ Δ₀ Δ₁ : ℝ,
    B (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) (O.refl 0).1 Δ₀
    ∧ B (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) O.1 Δ₁
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)| * Δ₀
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)| * Δ₁)
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The pixel from any closing bound and centring.** -/
theorem pixelPassage_of_bound (hN : N ≠ 0)
    {B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop}
    (hcl : ∀ M β F Δ, B M β F Δ →
      |MassGap.PeriodicState.torusState hN M β F - MassGap.PeriodicState.periodicState hN β F| ≤ Δ)
    {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π₁ π₂ : ℝ} (hB : BoundPixel hN c O t ℓ π₁ B)
    (hC : CentringPixel hN c O t ℓ π₂) :
    LightConePassage.PixelPassage hN (RelativeDecay.stateTD hN c) O t ℓ (π₁ + π₂) := by
  filter_upwards [hB, hC] with k hk hc
  have h1 := hcl _ _ _ _ hk
  have h1' : |stateK hN k (refObs (stateK hN k) O t ℓ k)
      - RelativeDecay.stateTD hN c k (refObs (stateK hN k) O t ℓ k)|
      ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by
    rw [abs_sub_comm]
    exact h1
  calc |ExistenceReduce.refReading hN O t ℓ k - refReadingS (RelativeDecay.stateTD hN c) O t ℓ k|
      ≤ _ := pixel_split hN (RelativeDecay.stateTD hN c) O t ℓ k
    _ ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)
        + π₂ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) :=
        add_le_add h1' hc
    _ = (π₁ + π₂)
        * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by ring

/-- **The centring from one-point bounds.** -/
theorem centringPixel_of_bound (hN : N ≠ 0)
    {B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop}
    (hcl : ∀ M β F Δ, B M β F Δ →
      |MassGap.PeriodicState.torusState hN M β F - MassGap.PeriodicState.periodicState hN β F| ≤ Δ)
    {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ} (h : BoundOnePoint hN c O t ℓ π B) :
    CentringPixel hN c O t ℓ π := by
  filter_upwards [h] with k hk
  obtain ⟨Δ₀, Δ₁, h₀, h₁, hle⟩ := hk
  have d₀ : |stateK hN k (O.refl 0).1 - RelativeDecay.stateTD hN c k (O.refl 0).1| ≤ Δ₀ := by
    rw [abs_sub_comm]
    exact hcl _ _ _ _ h₀
  have d₁ : |stateK hN k O.1 - RelativeDecay.stateTD hN c k O.1| ≤ Δ₁ := by
    rw [abs_sub_comm]
    exact hcl _ _ _ _ h₁
  rw [centring_eq, abs_mul, abs_mul, abs_mul]
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left d₀ (abs_nonneg _))
    (mul_le_mul_of_nonneg_left d₁ (abs_nonneg _)) (by positivity)
    (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans d₀))) hle

/-- **The pinned path with `hpos` read through any closing bound and the floor.** -/
theorem clay_canonical_bound (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop}
    (hcl : ∀ M β F Δ, B M β F Δ →
      |MassGap.PeriodicState.torusState hN M β F - MassGap.PeriodicState.periodicState hN β F| ≤ Δ)
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoundPixel hN c O t ℓ π₁ B) (h1 : BoundOnePoint hN c O t ℓ π₂ B)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  LightConePassage.clay_canonical_lightCone hN2 hN O ht c hκ (add_nonneg hπ₁ hπ₂) hπκ
    (pixelPassage_of_bound hN hcl hB (centringPixel_of_bound hN hcl h1)) hF hD hℓ hW

/-- **The pinned path with `hpos` read through coarse Gibbs bounds and the floor.** -/
theorem clay_canonical_coarseGibbs (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoundPixel hN c O t ℓ π₁ (CoarseGibbsBound hN))
    (h1 : BoundOnePoint hN c O t ℓ π₂ (CoarseGibbsBound hN))
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_bound hN2 hN O (fun _ _ _ _ h => (screenBound_of_coarseGibbs h).closing) ht c hκ
    hπ₁ hπ₂ hπκ hB h1 hF hD hℓ hW

/-- **The pinned path with `hpos` read through coarse typical bounds and the floor.** -/
theorem clay_canonical_coarseTypical (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoundPixel hN c O t ℓ π₁ (CoarseTypicalBound hN))
    (h1 : BoundOnePoint hN c O t ℓ π₂ (CoarseTypicalBound hN))
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_bound hN2 hN O (fun _ _ _ _ h => (screenTypical_of_coarseTypical h).closing) ht c
    hκ hπ₁ hπ₂ hπκ hB h1 hF hD hℓ hW

end Pixel

end MassGap.CoarseBoundary

#print axioms MassGap.CoarseBoundary.abs_sub_mix_le
#print axioms MassGap.CoarseBoundary.abs_sub_le_sum
#print axioms MassGap.CoarseBoundary.abs_sub_le_card_mul
#print axioms MassGap.CoarseBoundary.coarse_closing
#print axioms MassGap.CoarseBoundary.markov_comp
#print axioms MassGap.CoarseBoundary.wRead_sub
#print axioms MassGap.CoarseBoundary.wRead_le
#print axioms MassGap.CoarseBoundary.wRead_lower
#print axioms MassGap.CoarseBoundary.wRead_osc
#print axioms MassGap.CoarseBoundary.ratio_of_log
#print axioms MassGap.CoarseBoundary.abs_log_le_of_ratio
#print axioms MassGap.CoarseBoundary.coarseGibbs_osc
#print axioms MassGap.CoarseBoundary.blockOsc_coarseGibbs
#print axioms MassGap.CoarseBoundary.coarse_mass_le
#print axioms MassGap.CoarseBoundary.integral_blockOsc_log
#print axioms MassGap.CoarseBoundary.effStep_blockOsc
#print axioms MassGap.CoarseBoundary.glueStep_eq_off
#print axioms MassGap.CoarseBoundary.effStep_blockOsc_of_fine
#print axioms MassGap.CoarseBoundary.spec_screen_eq
#print axioms MassGap.CoarseBoundary.ScreenBound.closing
#print axioms MassGap.CoarseBoundary.screenBound_of_coarse
#print axioms MassGap.CoarseBoundary.coarseBound_of_spread
#print axioms MassGap.CoarseBoundary.screenBound_of_coarseGibbs
#print axioms MassGap.CoarseBoundary.ScreenTypicalBound.closing
#print axioms MassGap.CoarseBoundary.screenTypical_of_coarseTypical
#print axioms MassGap.CoarseBoundary.pixelPassage_of_bound
#print axioms MassGap.CoarseBoundary.centringPixel_of_bound
#print axioms MassGap.CoarseBoundary.clay_canonical_bound
#print axioms MassGap.CoarseBoundary.clay_canonical_coarseGibbs
#print axioms MassGap.CoarseBoundary.clay_canonical_coarseTypical
