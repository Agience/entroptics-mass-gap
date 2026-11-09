import Mathlib
import MassGap.BoxGapBE

noncomputable section

/-!
# MassGap.BoxGapHS — Holley–Stroock, the per-link oscillation, and the box gap past the pair reach

## What it gives

1. `holleyStroock`, `holleyStroock_exp`: a Poincaré inequality of a probability measure `ν` passes to
   `e^{−V} ν / Z` with its constant multiplied by `e^{osc V}`, for any form `∫ Γ` with `Γ ≥ 0`.
2. `link_action_osc`: the action of one link oscillates by at most `24 β` (`12` ordered non-diagonal
   plaquettes, `φ ∈ [0, 2]`).
3. `tiltBounds_sharp`: `PairInterface.TiltBounds` with the tilted partition function kept in the
   denominator, `Z_θ ≥ 1 + t²/(2D) − t3 t³/6`, in place of `Z_θ ≥ 1`. `IsoAt` is the isotropy it reads,
   discharged by `isoAt_su2`, `isoAt_su3`; `SU(2)` also uses parity (`hE2_su2`, `hE1_su2`).
4. `n2_ne_four`: on a torus of extent at least `3` no two links share two plaquettes, so the row sum of
   the pair defect is `18 δ₁`; the term `12 δ₁ + 3 δ₂` belongs to extent `2` alone.
5. `boxLocalGap_of_singleFibre`: `BoxLocalGap hN β n (1 − 18 δ)` at `2 ≤ n` from the single-pair fibre
   bound.
6. `boxLocalGap15_su2_hs`: `BoxLocalGap β 15 (953/12500)` for `SU(2)` at every `β ∈ [0, 83/1000]`.
   `boxLocalGap15_su3_hs`: `BoxLocalGap β 15 (41/500)` for `SU(3)` at every `β ∈ [0, 19/100]`.
7. `clay_of_uvStep_su2_hs`, `clay_of_uvStep_su3_hs`: `BoxGapBE.clay15_of_localGap` at these end couplings.

## The convention

`β` is the Lean coupling. The action sums `1 − Re tr U_p / N` over ordered plaquettes, each plane twice,
so the weight is `exp((2β/N) Σ Re tr U_p)` over planes and the standard Wilson coupling is
`β_W = 2N/g² = 2β`. Bhattacharjee et al. (zenodo 24055064, release v4.42.0, Table `tab:ranges`; unrefereed) use the weight
`exp(N β' Σ Re Tr Q_p)` with `β_W = N² β'`. These ranges are quoted from the unrefereed preprint and the conversion is unchecked here. Their ranges are `SU(2)`: `β_W < 2/9`
ungauged, `β_W < 1/3` in the forest gauge; `SU(3)`: `β_W ≤ 0.52` in the forest gauge; in Lean couplings `β < 1/9`,
`β < 1/6` and `β ≤ 0.26`.

## Where the reach comes from

Items 3 and 4 extend the box, inside the pair route; item 1 does not. On the whole box Holley–Stroock
loses `e^{−ω}` with `ω` extensive: at least `607500` ordered plaquettes meet the `202500` links of a
side-15 box (each link lies in `12`, each plaquette holds at most `4`), so the available bound on `ω` is
of order `10⁶ β` and the constant passes `0.0759` only near `β ≈ 2·10⁻⁶`, inside the strong-coupling base
`2.94·10⁻⁵` (computed, not in Lean). On one link it compares two single-site variances and gives nothing
on the box.

## The reach (computed with Python; the end couplings are checked by `norm_num` below)

The threshold `759/10000` is crossed at `β ≈ 0.08307` (`SU(2)`) and `≈ 0.1906` (`SU(3)`), against
`0.07594`, `0.1821` of `BoxGapBE`. `SU(2)` needs parity: without it the crossing is `0.0807`, short of
`0.0817`, the coupling that mirrors `3/40` across the peak of `aRun`.

## What does not follow

* The first octave is not covered. It asks `[0.0817, 0.3165]` (`SU(2)`) and `[0.1762, 0.7119]` (`SU(3)`)
  in Lean couplings, that is `β_W` up to `0.633` and `1.424`; the box gap stops at `0.083`, `0.19`.
  Zero octaves are covered, so `UVStepMap.uvBelowIR_of_split` has no finite part at `K = 1`.
* The octave lies past every single-link and plaquette-block range in the literature, including the unrefereed preprint: `0.633 > 1/3` and
  `1.424 > 0.52` in `β_W`.
* The sharp quarter of Bhattacharjee et al., `W₁(ν_b, ν_b') ≤ |b − b'|/4` on `S³`, is not formalised here.
  Its proof uses Green's formula in the ball and Bessel series. Through the Lipschitz contraction of the
  two-link Gibbs sampler it would give `FibreBound (τ/4) τ κ` at `SU(2)`, so `δ = β/2`, `Δ = 9β` and a
  reach of `0.1026`. That transfer is an unproved plan.
* The forest gauge is not used. `A = Σ_box (1 − E_l)` dominates the sum over the links off the forest,
  whose pair defect has `12` partners per row, but the two have the same kernel on gauge-invariant
  functions only where every link at the tail site lies in the box. Forest links on the box boundary are
  the obstruction: dropping them restores rows of `18` in the boundary layer.
* The UV step, E, N and Y stay hypotheses in item 7.

DERIVED (module-wide): `4` the spacetime dimension; `15` the box side of `WeightedProfile15`; `0` the
reflection plane, the excluded rank and the lower ends; `2`, `3` the ranks; `2 * j + 1` the index of the
even-extent family and `+ 1` its successor writing the extent.
-/

namespace MassGap.BoxGapHS

open MeasureTheory
open MassGap MassGap.BoxGap MassGap.BoxPatch MassGap.HeatBath MassGap.KnabeCriterion
open MassGap.PairCorrSharp MassGap.PairInterface MassGap.PairFibreAbstract MassGap.TiltedHaar
open MassGap.PairCount MassGap.WeightedProfile15 MassGap.HaarMomentsSU2
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.PeriodicState (torusObs)
open MassGap.PairCorr (twoCondExp)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.WilsonLattice (wilsonHol)
open MassGap.SimpleGroup (negOne2)

open private ev ev_self ev_ne ev_add_ne_zero tp n2_eq_card card_T_eq mem_plq_true nb card_tp_le_one
  tp_fst_inj from MassGap.PairCount
open private int_left from MassGap.HaarMomentsSU2
open private feat_eq s3_sq trc intC intR tr2_zero normSq_int from MassGap.HaarMomentsSU3

/-- The difference of two integrable functions, stated pointwise.

DERIVED: no numeral. -/
private theorem isub {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {f g : Y → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (fun x => f x - g x) μ :=
  hf.sub hg

/-! ## 1. Holley–Stroock -/

section HolleyStroock

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- An integrable function times a bounded measurable weight is integrable.

DERIVED: `0` is the sign of the weight. -/
private theorem integrable_mul_weight {g w : Ω → ℝ} {b : ℝ} (hg : Integrable g ν)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ x, w x ≤ b) (hwm : Measurable w) :
    Integrable (fun x => g x * w x) ν := by
  refine (hg.norm.const_mul b).mono' (hg.aestronglyMeasurable.mul hwm.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hw0 x), mul_comm]
  exact mul_le_mul_of_nonneg_right (hwb x) (norm_nonneg _)

/-- **Holley–Stroock.** Let `a ≤ w ≤ b` with `a > 0`, and `Var_ν f ≤ C ∫ Γ dν` with `Γ ≥ 0`. Then the
variance of `f` in the law `w ν / ∫ w` satisfies the inequality with constant `(b/a) C`. The
normalization `∫ w` appears on both sides, so both are stated unnormalized.

DERIVED: `0` the sign of `a`, `Γ`, `C`; `2` the square. -/
theorem holleyStroock {w f Γ : Ω → ℝ} {a b C : ℝ} (ha : 0 < a) (hwa : ∀ x, a ≤ w x)
    (hwb : ∀ x, w x ≤ b) (hwm : Measurable w) (hf : Integrable f ν)
    (hf2 : Integrable (fun x => f x ^ 2) ν) (hΓ : Integrable Γ ν) (hΓ0 : ∀ x, 0 ≤ Γ x)
    (hC : 0 ≤ C) (hP : ∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν ≤ C * ∫ x, Γ x ∂ν) :
    ∫ x, (f x - (∫ y, f y * w y ∂ν) / ∫ y, w y ∂ν) ^ 2 * w x ∂ν
      ≤ b / a * C * ∫ x, Γ x * w x ∂ν := by
  have hw0 : ∀ x, 0 ≤ w x := fun x => ha.le.trans (hwa x)
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hb : 0 ≤ b := (hw0 x₀).trans (hwb x₀)
  obtain ⟨c, hc⟩ : ∃ c, c = ∫ y, f y ∂ν := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ y, w y ∂ν := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = ∫ y, f y * w y ∂ν := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∫ y, f y ^ 2 * w y ∂ν := ⟨_, rfl⟩
  rw [← hc] at hP
  rw [← hZ, ← hS]
  have iw : Integrable w ν := by
    have h : Integrable (fun x => (fun _ : Ω => (1 : ℝ)) x * w x) ν :=
      integrable_mul_weight (integrable_const (1 : ℝ)) hw0 hwb hwm
    simpa using h
  have i1 := integrable_mul_weight hf hw0 hwb hwm
  have i2 := integrable_mul_weight hf2 hw0 hwb hwm
  have hexp : ∀ x, ∫ y, (f y - x) ^ 2 * w y ∂ν = Q - 2 * x * S + x ^ 2 * Z := by
    intro x
    have e : (fun y => (f y - x) ^ 2 * w y)
        = fun y => (f y ^ 2 * w y - (2 * x) * (f y * w y)) + x ^ 2 * w y := by
      funext y
      ring
    rw [e, integral_add (isub i2 (i1.const_mul (2 * x))) (iw.const_mul (x ^ 2)),
      integral_sub i2 (i1.const_mul (2 * x)), integral_const_mul, integral_const_mul, ← hQ, ← hS,
      ← hZ]
  have hZa : a ≤ Z := by
    have h := integral_mono (integrable_const a) iw hwa
    rw [integral_const, probReal_univ, one_smul] at h
    rw [hZ]
    exact h
  have hZ0 : 0 < Z := lt_of_lt_of_le ha hZa
  obtain ⟨m, hm⟩ : ∃ m, m = S / Z := ⟨_, rfl⟩
  have hSm : S = m * Z := by rw [hm, div_mul_cancel₀ _ hZ0.ne']
  rw [← hm]
  have hmin : ∫ y, (f y - m) ^ 2 * w y ∂ν ≤ ∫ y, (f y - c) ^ 2 * w y ∂ν := by
    rw [hexp m, hexp c, hSm]
    nlinarith [mul_nonneg (sq_nonneg (m - c)) hZ0.le]
  have isq : Integrable (fun y => (f y - c) ^ 2) ν := by
    have e : (fun y => (f y - c) ^ 2) = fun y => f y ^ 2 - (2 * c) * f y + c ^ 2 := by
      funext y
      ring
    rw [e]
    exact (hf2.sub (hf.const_mul _)).add (integrable_const _)
  have ib : ∫ y, (f y - c) ^ 2 * w y ∂ν ≤ b * ∫ y, (f y - c) ^ 2 ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_mul_weight isq hw0 hwb hwm) (isq.const_mul b) (fun y => ?_)
    show (f y - c) ^ 2 * w y ≤ b * (f y - c) ^ 2
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hwb y) (sq_nonneg _)
  have iΓ := integrable_mul_weight hΓ hw0 hwb hwm
  have hΓa : a * ∫ y, Γ y ∂ν ≤ ∫ y, Γ y * w y ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono (hΓ.const_mul a) iΓ (fun y => ?_)
    show a * Γ y ≤ Γ y * w y
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hwa y) (hΓ0 y)
  have hG : ∫ y, Γ y ∂ν ≤ (∫ y, Γ y * w y ∂ν) / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hΓa
  calc ∫ y, (f y - m) ^ 2 * w y ∂ν ≤ b * ∫ y, (f y - c) ^ 2 ∂ν := hmin.trans ib
    _ ≤ b * (C * ∫ y, Γ y ∂ν) := mul_le_mul_of_nonneg_left hP hb
    _ ≤ b * (C * ((∫ y, Γ y * w y ∂ν) / a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hC) hb
    _ = b / a * C * ∫ y, Γ y * w y ∂ν := by ring

#print axioms holleyStroock

/-- **Holley–Stroock in oscillation form**: `w = e^{−V}` with `lo ≤ V ≤ lo + Δ` multiplies the constant
by `e^Δ`.

DERIVED: `0` the sign of `Γ`, `C`; `2` the square. -/
theorem holleyStroock_exp {V f Γ : Ω → ℝ} {lo Δ C : ℝ} (hlo : ∀ x, lo ≤ V x)
    (hhi : ∀ x, V x ≤ lo + Δ) (hVm : Measurable V) (hf : Integrable f ν)
    (hf2 : Integrable (fun x => f x ^ 2) ν) (hΓ : Integrable Γ ν) (hΓ0 : ∀ x, 0 ≤ Γ x)
    (hC : 0 ≤ C) (hP : ∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν ≤ C * ∫ x, Γ x ∂ν) :
    ∫ x, (f x - (∫ y, f y * Real.exp (-V y) ∂ν) / ∫ y, Real.exp (-V y) ∂ν) ^ 2 * Real.exp (-V x) ∂ν
      ≤ Real.exp Δ * C * ∫ x, Γ x * Real.exp (-V x) ∂ν := by
  have h := holleyStroock (w := fun x => Real.exp (-V x)) (a := Real.exp (-(lo + Δ)))
    (b := Real.exp (-lo)) (Real.exp_pos _) (fun x => Real.exp_le_exp.mpr (by linarith [hhi x]))
    (fun x => Real.exp_le_exp.mpr (by linarith [hlo x])) (Real.measurable_exp.comp hVm.neg)
    hf hf2 hΓ hΓ0 hC hP
  have e : Real.exp (-lo) / Real.exp (-(lo + Δ)) = Real.exp Δ := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [e] at h
  exact h

#print axioms holleyStroock_exp

end HolleyStroock

/-! ## 2. The oscillation of one link's action -/

section Link

variable {N : ℕ}

/-- **The per-link oscillation.** The sum of `φ = 1 − Re tr/N` over the non-diagonal plaquettes through
`l` lies in `[0, 24]` at every configuration, so `β` times it oscillates by at most `24 β`, uniformly in
the boundary.

DERIVED: `24 = 2 · 12`; `12 = 2 · 2(d − 1)` at `d = 4`, ordered plaquettes through a link
(`PairCount.card_visit_nondiag_le`); `2` the range of `φ` (`WilsonAction.wilsonDensity_le_two`). -/
theorem link_action_osc (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (M : ℕ)
    (l : WilsonHypercubic.Link 4 (M + 1)) (W W' : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    β * ∑ p ∈ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst), wilsonDensity (wilsonHol (bdT M) p W)
      - β * ∑ p ∈ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst), wilsonDensity (wilsonHol (bdT M) p W')
      ≤ 24 * β := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst), wilsonDensity (wilsonHol (bdT M) p W) ≤ 24 := by
    have hc : ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).card : ℝ) ≤ 12 := by
      exact_mod_cast card_visit_nondiag_le M l
    have h := Finset.sum_le_card_nsmul (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst))
      (fun p => wilsonDensity (wilsonHol (bdT M) p W)) 2 (fun p _ => wilsonDensity_le_two hN _)
    rw [nsmul_eq_mul] at h
    linarith
  have h0 : 0 ≤ ∑ p ∈ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst), wilsonDensity (wilsonHol (bdT M) p W') :=
    Finset.sum_nonneg (fun p _ => wilsonDensity_nonneg hN _)
  nlinarith [mul_le_mul_of_nonneg_left h1 hβ, mul_nonneg hβ h0]

#print axioms link_action_osc

end Link

/-! ## 3. Polynomial bounds -/

section Poly

/-- `|y|⁶ = y⁶`.

DERIVED: `2`, `3`, `6` the exponents. -/
private theorem abs_pow_six (y : ℝ) : |y| ^ 6 = y ^ 6 := by
  have h : |y| ^ 6 = (|y| ^ 2) ^ 3 := by ring
  rw [h, sq_abs]
  ring

/-- **The third-order lower bound** on `|y| ≤ 2` (`TiltedHaar.exp_taylor6`).

DERIVED: `2` keeps `15 + 3y − y² ≥ 0`, the factor of `y⁴(15 + 3y − y²)/360`, the terms past the cubic;
`3` the range of `exp_taylor6`; `6`, `24`, `120`, `360` its denominators. -/
theorem exp_lower {y : ℝ} (hy : |y| ≤ 2) : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 ≤ Real.exp y := by
  have h := (abs_le.mp (exp_taylor6 (y := y) (by linarith))).1
  rw [abs_pow_six] at h
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  have hf : 0 ≤ 15 + 3 * y - y ^ 2 := by nlinarith
  have hp : 0 ≤ y ^ 4 * (15 + 3 * y - y ^ 2) := mul_nonneg (by positivity) hf
  have e : y ^ 4 * (15 + 3 * y - y ^ 2) = 15 * y ^ 4 + 3 * y ^ 5 - y ^ 6 := by ring
  linarith

/-- The coefficient of `|y|³` in `e^y − 1 − y − y²/2` on `|y| ≤ r`.

DERIVED: `6`, `24`, `120` factorials; `360 = 6!/2` the remainder of `exp_taylor6`; the powers of `r` are
the exponents past `3`. -/
def c3 (r : ℝ) : ℝ := 1 / 6 + r / 24 + r ^ 2 / 120 + r ^ 3 / 360

/-- The coefficient of `y²` in `cosh y − 1` on `|y| ≤ r`.

DERIVED: `2`, `24` factorials; `360` the remainder of `exp_taylor6`, both signs together. -/
def cE (r : ℝ) : ℝ := 1 / 2 + r ^ 2 / 24 + r ^ 4 / 360

/-- The coefficient of `|y|³` in `sinh y − y` on `|y| ≤ r`.

DERIVED: `6`, `120` factorials; `360` the remainder of `exp_taylor6`, both signs together. -/
def cO (r : ℝ) : ℝ := 1 / 6 + r ^ 2 / 120 + r ^ 3 / 360

/-- The powers of `a ∈ [0, r]` above `a³`.

DERIVED: `3`, `4`, `5`, `6` the exponents. -/
private theorem pow_steps {a r : ℝ} (h0 : 0 ≤ a) (h : a ≤ r) :
    a ^ 4 ≤ a ^ 3 * r ∧ a ^ 5 ≤ a ^ 3 * r ^ 2 ∧ a ^ 6 ≤ a ^ 3 * r ^ 3 := by
  have h3 : 0 ≤ a ^ 3 := pow_nonneg h0 3
  refine ⟨?_, ?_, ?_⟩
  · calc a ^ 4 = a ^ 3 * a := by ring
      _ ≤ a ^ 3 * r := mul_le_mul_of_nonneg_left h h3
  · calc a ^ 5 = a ^ 3 * a ^ 2 := by ring
      _ ≤ a ^ 3 * r ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 2) h3
  · calc a ^ 6 = a ^ 3 * a ^ 3 := by ring
      _ ≤ a ^ 3 * r ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 3) h3

/-- `−|y|ᵏ ≤ yᵏ ≤ |y|ᵏ`.

DERIVED: `0` the sign of the absolute value. -/
private theorem pow_abs_bounds (y : ℝ) (k : ℕ) : -|y| ^ k ≤ y ^ k ∧ y ^ k ≤ |y| ^ k := by
  have h : |y ^ k| ≤ |y| ^ k := le_of_eq (abs_pow y k)
  exact abs_le.mp h

/-- **The cubic remainder**: `|e^y − 1 − y − y²/2| ≤ c3 r |y|³` on `|y| ≤ r ≤ 3`.

DERIVED: `3` the range of `exp_taylor6`; `2` the Taylor order kept. -/
theorem exp_cubic {y r : ℝ} (hy : |y| ≤ r) (hr : r ≤ 3) :
    |Real.exp y - 1 - y - y ^ 2 / 2| ≤ c3 r * |y| ^ 3 := by
  obtain ⟨h1, h2⟩ := abs_le.mp (exp_taylor6 (y := y) (hy.trans hr))
  obtain ⟨s4, s5, s6⟩ := pow_steps (abs_nonneg y) hy
  obtain ⟨t3l, t3u⟩ := pow_abs_bounds y 3
  obtain ⟨t4l, t4u⟩ := pow_abs_bounds y 4
  obtain ⟨t5l, t5u⟩ := pow_abs_bounds y 5
  have e : c3 r * |y| ^ 3 = |y| ^ 3 / 6 + |y| ^ 3 * r / 24 + |y| ^ 3 * r ^ 2 / 120
      + |y| ^ 3 * r ^ 3 / 360 := by
    unfold c3
    ring
  rw [e, abs_le]
  constructor <;> linarith

/-- **The even part**: `(e^y + e^{−y})/2 ≤ 1 + cE r · y²` on `|y| ≤ r ≤ 3`.

DERIVED: `3` the range of `exp_taylor6`; `2` the two signs and the square. -/
theorem cosh_upper {y r : ℝ} (hy : |y| ≤ r) (hr : r ≤ 3) :
    (Real.exp y + Real.exp (-y)) / 2 ≤ 1 + cE r * y ^ 2 := by
  have hyn : |(-y)| ≤ r := by rwa [abs_neg]
  have h1 := (abs_le.mp (exp_taylor6 (y := y) (hy.trans hr))).2
  have h2 := (abs_le.mp (exp_taylor6 (y := -y) (hyn.trans hr))).2
  rw [abs_neg] at h2
  rw [abs_pow_six] at h1 h2
  have hs : y ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have s4 : y ^ 4 ≤ y ^ 2 * r ^ 2 := by
    calc y ^ 4 = y ^ 2 * y ^ 2 := by ring
      _ ≤ y ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hs hy2
  have s6 : y ^ 6 ≤ y ^ 2 * r ^ 4 := by
    calc y ^ 6 = y ^ 2 * (y ^ 2 * y ^ 2) := by ring
      _ ≤ y ^ 2 * (r ^ 2 * r ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hs hs hy2 hr2) hy2
      _ = y ^ 2 * r ^ 4 := by ring
  have e : cE r * y ^ 2 = y ^ 2 / 2 + y ^ 2 * r ^ 2 / 24 + y ^ 2 * r ^ 4 / 360 := by
    unfold cE
    ring
  have n3 : (-y) ^ 3 = -y ^ 3 := by ring
  have n5 : (-y) ^ 5 = -y ^ 5 := by ring
  have n2 : (-y) ^ 2 = y ^ 2 := by ring
  have n4 : (-y) ^ 4 = y ^ 4 := by ring
  rw [n2, n3, n4, n5] at h2
  rw [e]
  linarith

/-- **The odd part**: `|(e^y − e^{−y})/2 − y| ≤ cO r |y|³` on `|y| ≤ r ≤ 3`.

DERIVED: `3` the range of `exp_taylor6`; `2` the two signs. -/
theorem sinh_cubic {y r : ℝ} (hy : |y| ≤ r) (hr : r ≤ 3) :
    |(Real.exp y - Real.exp (-y)) / 2 - y| ≤ cO r * |y| ^ 3 := by
  have hyn : |(-y)| ≤ r := by rwa [abs_neg]
  obtain ⟨a1, a2⟩ := abs_le.mp (exp_taylor6 (y := y) (hy.trans hr))
  obtain ⟨b1, b2⟩ := abs_le.mp (exp_taylor6 (y := -y) (hyn.trans hr))
  rw [abs_neg] at b1 b2
  obtain ⟨_, s5, s6⟩ := pow_steps (abs_nonneg y) hy
  obtain ⟨t3l, t3u⟩ := pow_abs_bounds y 3
  obtain ⟨t5l, t5u⟩ := pow_abs_bounds y 5
  have n3 : (-y) ^ 3 = -y ^ 3 := by ring
  have n5 : (-y) ^ 5 = -y ^ 5 := by ring
  have n2 : (-y) ^ 2 = y ^ 2 := by ring
  have n4 : (-y) ^ 4 = y ^ 4 := by ring
  rw [n2, n3, n4, n5] at b1 b2
  have e : cO r * |y| ^ 3 = |y| ^ 3 / 6 + |y| ^ 3 * r ^ 2 / 120 + |y| ^ 3 * r ^ 3 / 360 := by
    unfold cO
    ring
  rw [e, abs_le]
  constructor <;> linarith

#print axioms exp_lower
#print axioms exp_cubic
#print axioms cosh_upper
#print axioms sinh_cubic

end Poly

/-! ## 4. The tilted constants with the partition function kept -/

section Sharp

variable {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Ω → E}

/-- **The isotropy read at one tilt.** `t` is the effective norm of `θ`: `E⟪θ, X⟫² = t²/D`. It is at
most `‖θ‖`, and strictly less at `SU(2)` when `θ` leaves the real span of the feature.

DERIVED: `2`, `3`, `4` the moment orders. -/
structure IsoAt (P : Measure Ω) (X : Ω → E) (D q4 t3 : ℝ) (θ : E) (t : ℝ) : Prop where
  t0 : 0 ≤ t
  tle : t ≤ ‖θ‖
  sec : ∫ g, inner ℝ θ (X g) ^ 2 ∂P = t ^ 2 / D
  four : ∫ g, inner ℝ θ (X g) ^ 4 ∂P ≤ q4 * t ^ 4
  th1 : ∀ u : E, |∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ∂P| ≤ t3 * ‖u‖ ^ 2 * t
  th2 : ∀ w : E, |∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P| ≤ t3 * t ^ 2 * ‖w‖
  th3 : |∫ g, inner ℝ θ (X g) ^ 3 ∂P| ≤ t3 * t ^ 3

/-- `‖θ‖ ≤ κ` bounds the linear functional.

DERIVED: `1` the norm bound of the feature. -/
private theorem abs_ip_le (hX1 : ∀ g, ‖X g‖ ≤ 1) {κ : ℝ} {θ : E} (hθ : ‖θ‖ ≤ κ) (g : Ω) :
    |inner ℝ θ (X g)| ≤ κ :=
  le_trans (abs_real_inner_le_norm θ (X g))
    (le_trans (mul_le_of_le_one_right (norm_nonneg θ) (hX1 g)) hθ)

/-- A pointwise absolute bound integrates.

DERIVED: no numeral. -/
private theorem abs_int_le {F G : Ω → ℝ} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ g, |F g| ≤ G g) : |∫ g, F g ∂P| ≤ ∫ g, G g ∂P := by
  have iF := integrable_of_continuous P hF
  have iG := integrable_of_continuous P hG
  rw [abs_le]
  constructor
  · rw [← integral_neg]
    exact integral_mono iG.neg iF (fun g => by
      show -G g ≤ F g
      exact (abs_le.mp (h g)).1)
  · exact integral_mono iF iG (fun g => (abs_le.mp (h g)).2)

/-- `∫ (a + b + r c + s d)`.

DERIVED: no numeral. -/
private theorem int_add4 {a b c d : Ω → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) (r s : ℝ) :
    ∫ g, (a g + b g + r * c g + s * d g) ∂P
      = ∫ g, a g ∂P + ∫ g, b g ∂P + r * ∫ g, c g ∂P + s * ∫ g, d g ∂P := by
  have ia := integrable_of_continuous P ha
  have ib := integrable_of_continuous P hb
  have ic := (integrable_of_continuous P hc).const_mul r
  have id := (integrable_of_continuous P hd).const_mul s
  rw [integral_add ((ia.fun_add ib).fun_add ic) id, integral_add (ia.fun_add ib) ic,
    integral_add ia ib,
    integral_const_mul, integral_const_mul]

/-- **The mixed fourth moment at the effective norm**: `E⟪u,X⟫²⟪θ,X⟫² ≤ q4 ‖u‖² t²`.

DERIVED: `2`, `4` the moment orders. -/
theorem mixed_le (H : HaarConsts P X) (hX : Continuous X) {θ : E} {t : ℝ}
    (I : IsoAt P X H.D H.q4 H.t3 θ t) (u : E) :
    ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P ≤ H.q4 * ‖u‖ ^ 2 * t ^ 2 := by
  have hcu := (continuous_const.inner hX : Continuous fun g => inner ℝ u (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hq : ∀ s : ℝ, 2 * s * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P
      ≤ s ^ 2 * (H.q4 * ‖u‖ ^ 4) + H.q4 * t ^ 4 := by
    intro s
    have iF : Integrable (fun g => inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2) P :=
      integrable_of_continuous P ((hcu.pow 2).mul (hcθ.pow 2))
    have iG : Integrable (fun g => inner ℝ u (X g) ^ 4) P :=
      integrable_of_continuous P (hcu.pow 4)
    have iK : Integrable (fun g => inner ℝ θ (X g) ^ 4) P :=
      integrable_of_continuous P (hcθ.pow 4)
    have hbase := quad_integral iF iG iK
      (fun (s : ℝ) g => by
        nlinarith [sq_nonneg (s * inner ℝ u (X g) ^ 2 - inner ℝ θ (X g) ^ 2)]) s
    have h4 := mul_le_mul_of_nonneg_left (H.fourth u) (sq_nonneg s)
    linarith [I.four]
  have hC : 0 ≤ H.q4 * ‖u‖ ^ 2 * t ^ 2 :=
    mul_nonneg (mul_nonneg H.q4_nonneg (sq_nonneg _)) (sq_nonneg _)
  exact le_trans (le_abs_self _)
    (abs_le_of_quad (mul_nonneg H.q4_nonneg (pow_nonneg (norm_nonneg u) 4)) hC
      (le_of_eq (by ring)) hq)

#print axioms mixed_le

/-- **The first moment against the tilt**: `|E⟪w,X⟫⟪θ,X⟫| ≤ ‖w‖ t / D`.

DERIVED: `2` the square. -/
theorem linear_le (H : HaarConsts P X) (hX : Continuous X) {θ : E} {t : ℝ}
    (I : IsoAt P X H.D H.q4 H.t3 θ t) (w : E) :
    |∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P| ≤ ‖w‖ * t / H.D := by
  have hcw := (continuous_const.inner hX : Continuous fun g => inner ℝ w (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hq : ∀ s : ℝ, 2 * s * ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
      ≤ s ^ 2 * (‖w‖ ^ 2 / H.D) + t ^ 2 / H.D := by
    intro s
    have iF : Integrable (fun g => inner ℝ w (X g) * inner ℝ θ (X g)) P :=
      integrable_of_continuous P (hcw.mul hcθ)
    have iG : Integrable (fun g => inner ℝ w (X g) ^ 2) P :=
      integrable_of_continuous P (hcw.pow 2)
    have iK : Integrable (fun g => inner ℝ θ (X g) ^ 2) P :=
      integrable_of_continuous P (hcθ.pow 2)
    have hbase := quad_integral iF iG iK
      (fun (s : ℝ) g => by
        nlinarith [sq_nonneg (s * inner ℝ w (X g) - inner ℝ θ (X g))]) s
    have h2 := mul_le_mul_of_nonneg_left (H.second w) (sq_nonneg s)
    rw [I.sec] at hbase
    linarith
  have hD := H.D_pos
  have hA : 0 ≤ ‖w‖ ^ 2 / H.D := by positivity
  have hC : 0 ≤ ‖w‖ * t / H.D := div_nonneg (mul_nonneg (norm_nonneg w) I.t0) hD.le
  exact abs_le_of_quad hA hC (le_of_eq (by field_simp)) hq

#print axioms linear_le

/-- **The cubic moment**: `E|⟪w,X⟫||⟪θ,X⟫|³ ≤ q4 ‖w‖ t³` (`mixed_le`, `IsoAt.four`).

DERIVED: `2`, `3`, `4` the moment orders. -/
theorem cubic_le (H : HaarConsts P X) (hX : Continuous X) {θ : E} {t : ℝ}
    (I : IsoAt P X H.D H.q4 H.t3 θ t) (w : E) :
    ∫ g, |inner ℝ w (X g)| * |inner ℝ θ (X g)| ^ 3 ∂P ≤ H.q4 * ‖w‖ * t ^ 3 := by
  have hcw := (continuous_const.inner hX : Continuous fun g => inner ℝ w (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hq : ∀ s : ℝ, 2 * s * ∫ g, |inner ℝ w (X g)| * |inner ℝ θ (X g)| ^ 3 ∂P
      ≤ s ^ 2 * (H.q4 * ‖w‖ ^ 2 * t ^ 2) + H.q4 * t ^ 4 := by
    intro s
    have iF : Integrable (fun g => |inner ℝ w (X g)| * |inner ℝ θ (X g)| ^ 3) P :=
      integrable_of_continuous P ((hcw.abs).mul (hcθ.abs.pow 3))
    have iG : Integrable (fun g => inner ℝ w (X g) ^ 2 * inner ℝ θ (X g) ^ 2) P :=
      integrable_of_continuous P ((hcw.pow 2).mul (hcθ.pow 2))
    have iK : Integrable (fun g => inner ℝ θ (X g) ^ 4) P :=
      integrable_of_continuous P (hcθ.pow 4)
    have hbase := quad_integral iF iG iK
      (fun (s : ℝ) g => by
        have e1 : inner ℝ w (X g) ^ 2 = |inner ℝ w (X g)| ^ 2 := (sq_abs _).symm
        have e2 : inner ℝ θ (X g) ^ 2 = |inner ℝ θ (X g)| ^ 2 := (sq_abs _).symm
        have e3 : inner ℝ θ (X g) ^ 4 = |inner ℝ θ (X g)| ^ 4 := by
          have : inner ℝ θ (X g) ^ 4 = (inner ℝ θ (X g) ^ 2) ^ 2 := by ring
          rw [this, e2]
          ring
        rw [e1, e2, e3]
        nlinarith [sq_nonneg (s * |inner ℝ w (X g)| * |inner ℝ θ (X g)|
          - |inner ℝ θ (X g)| ^ 2)]) s
    have h2 := mul_le_mul_of_nonneg_left (mixed_le H hX I w) (sq_nonneg s)
    linarith [I.four]
  have hC : 0 ≤ H.q4 * ‖w‖ * t ^ 3 :=
    mul_nonneg (mul_nonneg H.q4_nonneg (norm_nonneg w)) (pow_nonneg I.t0 3)
  have hA : 0 ≤ H.q4 * ‖w‖ ^ 2 * t ^ 2 :=
    mul_nonneg (mul_nonneg H.q4_nonneg (sq_nonneg _)) (sq_nonneg _)
  exact le_trans (le_abs_self _) (abs_le_of_quad hA hC (le_of_eq (by ring)) hq)

#print axioms cubic_le

/-- **The tilted partition function**: `Z_θ ≥ 1 + t²/(2D) − t3 t³/6` at `‖θ‖ ≤ 2` (`exp_lower`).

DERIVED: `2` the range of `exp_lower` and the Taylor denominator; `3` the moment order; `6 = 3!`. -/
theorem Z_ge (H : HaarConsts P X) (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {θ : E} {t : ℝ}
    (hθ : ‖θ‖ ≤ 2) (I : IsoAt P X H.D H.q4 H.t3 θ t) :
    1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6 ≤ ∫ g, Real.exp (inner ℝ θ (X g)) ∂P := by
  have hc := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hint := int_add4 (P := P) (continuous_const (y := (1 : ℝ))) hc (hc.pow 2) (hc.pow 3)
    (1 / 2) (1 / 6)
  have hmono : ∫ g, ((1 : ℝ) + inner ℝ θ (X g) + 1 / 2 * inner ℝ θ (X g) ^ 2
        + 1 / 6 * inner ℝ θ (X g) ^ 3) ∂P ≤ ∫ g, Real.exp (inner ℝ θ (X g)) ∂P := by
    refine integral_mono (integrable_of_continuous P
      (((continuous_const.add hc).add (continuous_const.mul (hc.pow 2))).add
        (continuous_const.mul (hc.pow 3))))
      (integrable_of_continuous P (Real.continuous_exp.comp hc)) (fun g => ?_)
    have h := exp_lower (abs_ip_le hX1 hθ g)
    show (1 : ℝ) + inner ℝ θ (X g) + 1 / 2 * inner ℝ θ (X g) ^ 2 + 1 / 6 * inner ℝ θ (X g) ^ 3 ≤ _
    linarith
  rw [hint, integral_const, probReal_univ, one_smul, H.mean θ, I.sec] at hmono
  have h3 := (abs_le.mp I.th3).1
  have hD := H.D_pos
  have e : t ^ 2 / (2 * H.D) = 1 / 2 * (t ^ 2 / H.D) := by
    field_simp
  rw [e]
  linarith

#print axioms Z_ge

/-- **`TiltBounds` with the partition function kept.** The numerators are bounded through `hE2`, `hE1`,
whose constants `cA`, `cB` are the caller's; `hM`, `hm` compare them with `Z_ge`'s lower bound at every
effective norm `t ≤ κ`.

DERIVED: `2` the range of `Z_ge`, the square and the Taylor denominator; `3` the cube; `6 = 3!`; `0` the
lower ends. -/
theorem tiltBounds_sharp (H : HaarConsts P X) (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1)
    {κ M mb cA cB : ℝ} (hκ2 : κ ≤ 2) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hM0 : 0 ≤ M) (hmb0 : 0 ≤ mb)
    (hiso : ∀ θ : E, ‖θ‖ ≤ κ → ∃ t, IsoAt P X H.D H.q4 H.t3 θ t)
    (hE2 : ∀ θ u : E, ‖θ‖ ≤ κ →
      ∫ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
        ≤ ∫ g, inner ℝ u (X g) ^ 2 ∂P + ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ∂P
          + cA * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P)
    (hE1 : ∀ θ w : E, ‖θ‖ ≤ κ →
      |∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P
          - ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
          - (∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P) / 2|
        ≤ cB * ∫ g, |inner ℝ w (X g)| * |inner ℝ θ (X g)| ^ 3 ∂P)
    (hM : ∀ t : ℝ, 0 ≤ t → t ≤ κ → 1 / H.D + H.t3 * t + cA * H.q4 * t ^ 2
      ≤ M * (1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6))
    (hm : ∀ t : ℝ, 0 ≤ t → t ≤ κ → t / H.D + H.t3 * t ^ 2 / 2 + cB * H.q4 * t ^ 3
      ≤ mb * (1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6)) :
    TiltBounds P X κ M mb := by
  intro θ hθ
  obtain ⟨t, I⟩ := hiso θ hθ
  have htκ := I.tle.trans hθ
  have hZ := Z_ge H hX hX1 (hθ.trans hκ2) I
  refine ⟨fun u => ?_, fun w => ?_⟩
  · have h1 := hE2 θ u hθ
    have hsec := H.second u
    have hth := le_trans (le_abs_self _) (I.th1 u)
    have hmix := mul_le_mul_of_nonneg_left (mixed_le H hX I u) hcA
    have hu : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have k1 := mul_le_mul_of_nonneg_right (hM t I.t0 htκ) hu
    have k2 := mul_le_mul_of_nonneg_left hZ (mul_nonneg hM0 hu)
    have e : (1 / H.D + H.t3 * t + cA * H.q4 * t ^ 2) * ‖u‖ ^ 2
        = ‖u‖ ^ 2 / H.D + H.t3 * ‖u‖ ^ 2 * t + cA * (H.q4 * ‖u‖ ^ 2 * t ^ 2) := by ring
    have e2 : M * (1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6) * ‖u‖ ^ 2
        = M * ‖u‖ ^ 2 * (1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6) := by ring
    rw [e, e2] at k1
    linarith
  · have h1 := abs_le.mp (hE1 θ w hθ)
    have hl := abs_le.mp (linear_le H hX I w)
    have ht := abs_le.mp (I.th2 w)
    have hc := mul_le_mul_of_nonneg_left (cubic_le H hX I w) hcB
    have hw : 0 ≤ ‖w‖ := norm_nonneg _
    have k1 := mul_le_mul_of_nonneg_right (hm t I.t0 htκ) hw
    have k2 := mul_le_mul_of_nonneg_left hZ (mul_nonneg hmb0 hw)
    have e : (t / H.D + H.t3 * t ^ 2 / 2 + cB * H.q4 * t ^ 3) * ‖w‖
        = ‖w‖ * t / H.D + H.t3 * t ^ 2 * ‖w‖ / 2 + cB * (H.q4 * ‖w‖ * t ^ 3) := by ring
    have e2 : mb * (1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6) * ‖w‖
        = mb * ‖w‖ * (1 + t ^ 2 / (2 * H.D) - H.t3 * t ^ 3 / 6) := by ring
    rw [e, e2] at k1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, hl.1, hl.2, ht.1, ht.2]

#print axioms tiltBounds_sharp

/-- **The generic second-moment numerator** (`TiltedHaar.exp_sub_one_sub_le`).

DERIVED: `3` the range of `exp_sub_one_sub_le`; `1` the norm bound of the feature; `2` the square. -/
theorem hE2_gen (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {κ : ℝ} (hκ3 : κ ≤ 3) (θ u : E)
    (hθ : ‖θ‖ ≤ κ) :
    ∫ g, inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g)) ∂P
      ≤ ∫ g, inner ℝ u (X g) ^ 2 ∂P + ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ∂P
        + cR κ * ∫ g, inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2 ∂P := by
  have hcu := (continuous_const.inner hX : Continuous fun g => inner ℝ u (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have hi0 : Integrable (fun g => inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g))) P :=
    integrable_of_continuous P ((hcu.pow 2).mul (Real.continuous_exp.comp hcθ))
  have hi1 : Integrable (fun g => inner ℝ u (X g) ^ 2) P := integrable_of_continuous P (hcu.pow 2)
  have hi2 : Integrable (fun g => inner ℝ u (X g) ^ 2 * inner ℝ θ (X g)) P :=
    integrable_of_continuous P ((hcu.pow 2).mul hcθ)
  have hi3 : Integrable (fun g => inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2) P :=
    integrable_of_continuous P ((hcu.pow 2).mul (hcθ.pow 2))
  have hm := integral_mono hi0 ((hi1.fun_add hi2).fun_add (hi3.const_mul (cR κ)))
    (fun g => by
      have h1 := exp_sub_one_sub_le (abs_ip_le hX1 hθ g) hκ3
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (inner ℝ u (X g)))
      show inner ℝ u (X g) ^ 2 * Real.exp (inner ℝ θ (X g))
        ≤ inner ℝ u (X g) ^ 2 + inner ℝ u (X g) ^ 2 * inner ℝ θ (X g)
          + cR κ * (inner ℝ u (X g) ^ 2 * inner ℝ θ (X g) ^ 2)
      nlinarith [h2])
  rw [integral_add (hi1.fun_add hi2) (hi3.const_mul (cR κ)), integral_add hi1 hi2,
    integral_const_mul] at hm
  exact hm

#print axioms hE2_gen

/-- **The generic mean numerator** (`exp_cubic`, `HaarConsts.mean`).

DERIVED: `3` the range of `exp_cubic`; `1` the norm bound of the feature; `2` the Taylor denominator. -/
theorem hE1_gen (H : HaarConsts P X) (hX : Continuous X) (hX1 : ∀ g, ‖X g‖ ≤ 1) {κ : ℝ}
    (hκ3 : κ ≤ 3) (θ w : E) (hθ : ‖θ‖ ≤ κ) :
    |∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P
        - ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
        - (∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P) / 2|
      ≤ c3 κ * ∫ g, |inner ℝ w (X g)| * |inner ℝ θ (X g)| ^ 3 ∂P := by
  have hcw := (continuous_const.inner hX : Continuous fun g => inner ℝ w (X g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (X g))
  have iA : Integrable (fun g => inner ℝ w (X g) * Real.exp (inner ℝ θ (X g))) P :=
    integrable_of_continuous P (hcw.mul (Real.continuous_exp.comp hcθ))
  have iB : Integrable (fun g => inner ℝ w (X g) * inner ℝ θ (X g)) P :=
    integrable_of_continuous P (hcw.mul hcθ)
  have iC0 : Integrable (fun g => inner ℝ θ (X g) ^ 2 * inner ℝ w (X g)) P :=
    integrable_of_continuous P ((hcθ.pow 2).mul hcw)
  have iC := iC0.const_mul (1 / 2 : ℝ)
  have iW : Integrable (fun g => inner ℝ w (X g)) P := integrable_of_continuous P hcw
  have e : ∫ g, inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) ∂P
        - ∫ g, inner ℝ w (X g) * inner ℝ θ (X g) ∂P
        - (∫ g, inner ℝ θ (X g) ^ 2 * inner ℝ w (X g) ∂P) / 2
      = ∫ g, inner ℝ w (X g) * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g)
          - inner ℝ θ (X g) ^ 2 / 2) ∂P := by
    have e1 : (fun g => inner ℝ w (X g) * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g)
          - inner ℝ θ (X g) ^ 2 / 2))
        = fun g => inner ℝ w (X g) * Real.exp (inner ℝ θ (X g)) - inner ℝ w (X g)
          - inner ℝ w (X g) * inner ℝ θ (X g)
          - (1 / 2 : ℝ) * (inner ℝ θ (X g) ^ 2 * inner ℝ w (X g)) := by
      funext g
      ring
    rw [e1, integral_sub (isub (isub iA iW) iB) iC, integral_sub (isub iA iW) iB,
      integral_sub iA iW,
      integral_const_mul, H.mean w]
    ring
  rw [e]
  have hb := abs_int_le (P := P)
    (F := fun g => inner ℝ w (X g) * (Real.exp (inner ℝ θ (X g)) - 1 - inner ℝ θ (X g)
      - inner ℝ θ (X g) ^ 2 / 2))
    (G := fun g => c3 κ * (|inner ℝ w (X g)| * |inner ℝ θ (X g)| ^ 3))
    (hcw.mul (((((Real.continuous_exp.comp hcθ).sub continuous_const).sub hcθ).sub
      ((hcθ.pow 2).div_const 2))))
    (continuous_const.mul (hcw.abs.mul (hcθ.abs.pow 3)))
    (fun g => by
      have h := exp_cubic (abs_ip_le hX1 hθ g) hκ3
      rw [abs_mul]
      calc |inner ℝ w (X g)| * _ ≤ |inner ℝ w (X g)| * (c3 κ * |inner ℝ θ (X g)| ^ 3) :=
            mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = _ := by ring)
  rw [integral_const_mul] at hb
  exact hb

#print axioms hE1_gen

end Sharp

/-! ## 5. Parity and isotropy at `SU(2)`, isotropy at `SU(3)` -/

section Groups

/-- **The `SU(2)` second-moment numerator by parity**: the order-one Taylor term and the odd part of
`cR` drop, `U ↦ −U` replacing `e^y` by `cosh y` (`HaarMomentsSU2.realFeature_negOne`, `cosh_upper`).

DERIVED: `2` the rank, the square and the two signs; `3` the range of `cosh_upper`; `1` the norm of the
feature; `0` the excluded rank. -/
theorem hE2_su2 {κ : ℝ} (hκ3 : κ ≤ 3) (θ u : FE 2) (hθ : ‖θ‖ ≤ κ) :
    ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * Real.exp (inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2))
      ≤ ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 ∂(probHaar (SU 2))
        + ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ θ (realFeature 2 U)
            ∂(probHaar (SU 2))
        + cE κ * ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ θ (realFeature 2 U) ^ 2
            ∂(probHaar (SU 2)) := by
  have hX := continuous_realFeature 2
  have hX1 : ∀ g : SU 2, ‖realFeature 2 g‖ ≤ 1 := fun g => (norm_realFeature (by norm_num) g).le
  have hcu := (continuous_const.inner hX : Continuous fun g => inner ℝ u (realFeature 2 g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (realFeature 2 g))
  have iP : Integrable (fun U : SU 2 => inner ℝ u (realFeature 2 U) ^ 2
      * Real.exp (inner ℝ θ (realFeature 2 U))) (probHaar (SU 2)) :=
    integrable_of_continuous _ ((hcu.pow 2).mul (Real.continuous_exp.comp hcθ))
  have iN : Integrable (fun U : SU 2 => inner ℝ u (realFeature 2 U) ^ 2
      * Real.exp (-inner ℝ θ (realFeature 2 U))) (probHaar (SU 2)) :=
    integrable_of_continuous _ ((hcu.pow 2).mul (Real.continuous_exp.comp hcθ.neg))
  have e1 : ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * Real.exp (-inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2))
      = ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * Real.exp (inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2)) := by
    have h := int_left (fun U : SU 2 => inner ℝ u (realFeature 2 U) ^ 2
      * Real.exp (inner ℝ θ (realFeature 2 U))) negOne2
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    show _ = inner ℝ u (realFeature 2 (negOne2 * U)) ^ 2
      * Real.exp (inner ℝ θ (realFeature 2 (negOne2 * U)))
    rw [realFeature_negOne, inner_neg_right, inner_neg_right, neg_sq]
  have hi1 : Integrable (fun U : SU 2 => inner ℝ u (realFeature 2 U) ^ 2) (probHaar (SU 2)) :=
    integrable_of_continuous _ (hcu.pow 2)
  have hi3 : Integrable (fun U : SU 2 => inner ℝ u (realFeature 2 U) ^ 2
      * inner ℝ θ (realFeature 2 U) ^ 2) (probHaar (SU 2)) :=
    integrable_of_continuous _ ((hcu.pow 2).mul (hcθ.pow 2))
  have hm := integral_mono (iP.fun_add iN) ((hi1.const_mul 2).fun_add (hi3.const_mul (2 * cE κ)))
    (fun g => by
      have h1 := cosh_upper (abs_ip_le hX1 hθ g) hκ3
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (inner ℝ u (realFeature 2 g)))
      show inner ℝ u (realFeature 2 g) ^ 2 * Real.exp (inner ℝ θ (realFeature 2 g))
          + inner ℝ u (realFeature 2 g) ^ 2 * Real.exp (-inner ℝ θ (realFeature 2 g))
        ≤ 2 * inner ℝ u (realFeature 2 g) ^ 2
          + 2 * cE κ * (inner ℝ u (realFeature 2 g) ^ 2 * inner ℝ θ (realFeature 2 g) ^ 2)
      nlinarith [h2])
  rw [integral_add iP iN, integral_add (hi1.const_mul 2) (hi3.const_mul (2 * cE κ)),
    integral_const_mul, integral_const_mul, e1] at hm
  have h0 : ∫ U : SU 2, inner ℝ u (realFeature 2 U) ^ 2 * inner ℝ θ (realFeature 2 U)
      ∂(probHaar (SU 2)) = 0 := by
    have h := feature_third_su2 u θ
    rw [zero_mul, zero_mul] at h
    exact abs_nonpos_iff.mp h
  rw [h0]
  linarith

#print axioms hE2_su2

/-- **The `SU(2)` mean numerator by parity** (`sinh_cubic`).

DERIVED: `2` the rank, the Taylor denominator and the two signs; `3` the range of `sinh_cubic`; `1` the
norm of the feature; `0` the excluded rank. -/
theorem hE1_su2 {κ : ℝ} (hκ3 : κ ≤ 3) (θ w : FE 2) (hθ : ‖θ‖ ≤ κ) :
    |∫ U : SU 2, inner ℝ w (realFeature 2 U) * Real.exp (inner ℝ θ (realFeature 2 U))
          ∂(probHaar (SU 2))
        - ∫ U : SU 2, inner ℝ w (realFeature 2 U) * inner ℝ θ (realFeature 2 U) ∂(probHaar (SU 2))
        - (∫ U : SU 2, inner ℝ θ (realFeature 2 U) ^ 2 * inner ℝ w (realFeature 2 U)
            ∂(probHaar (SU 2))) / 2|
      ≤ cO κ * ∫ U : SU 2, |inner ℝ w (realFeature 2 U)| * |inner ℝ θ (realFeature 2 U)| ^ 3
          ∂(probHaar (SU 2)) := by
  have hX := continuous_realFeature 2
  have hX1 : ∀ g : SU 2, ‖realFeature 2 g‖ ≤ 1 := fun g => (norm_realFeature (by norm_num) g).le
  have hcw := (continuous_const.inner hX : Continuous fun g => inner ℝ w (realFeature 2 g))
  have hcθ := (continuous_const.inner hX : Continuous fun g => inner ℝ θ (realFeature 2 g))
  have cP : Continuous (fun U : SU 2 => inner ℝ w (realFeature 2 U)
      * Real.exp (inner ℝ θ (realFeature 2 U))) := hcw.mul (Real.continuous_exp.comp hcθ)
  have cN : Continuous (fun U : SU 2 => inner ℝ w (realFeature 2 U)
      * Real.exp (-inner ℝ θ (realFeature 2 U))) := hcw.mul (Real.continuous_exp.comp hcθ.neg)
  have cB : Continuous (fun U : SU 2 => inner ℝ w (realFeature 2 U)
      * inner ℝ θ (realFeature 2 U)) := hcw.mul hcθ
  have e1 : ∫ U : SU 2, inner ℝ w (realFeature 2 U) * Real.exp (-inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2))
      = -∫ U : SU 2, inner ℝ w (realFeature 2 U) * Real.exp (inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2)) := by
    have h := int_left (fun U : SU 2 => inner ℝ w (realFeature 2 U)
      * Real.exp (inner ℝ θ (realFeature 2 U))) negOne2
    rw [← h, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    show _ = -(inner ℝ w (realFeature 2 (negOne2 * U))
      * Real.exp (inner ℝ θ (realFeature 2 (negOne2 * U))))
    rw [realFeature_negOne, inner_neg_right, inner_neg_right]
    ring
  have h0 : ∫ U : SU 2, inner ℝ θ (realFeature 2 U) ^ 2 * inner ℝ w (realFeature 2 U)
      ∂(probHaar (SU 2)) = 0 := by
    have h := feature_third_su2 θ w
    rw [zero_mul, zero_mul] at h
    exact abs_nonpos_iff.mp h
  have hb := abs_int_le (P := probHaar (SU 2))
    (F := fun g => inner ℝ w (realFeature 2 g) * Real.exp (inner ℝ θ (realFeature 2 g))
      - inner ℝ w (realFeature 2 g) * Real.exp (-inner ℝ θ (realFeature 2 g))
      - 2 * (inner ℝ w (realFeature 2 g) * inner ℝ θ (realFeature 2 g)))
    (G := fun g => 2 * cO κ * (|inner ℝ w (realFeature 2 g)| * |inner ℝ θ (realFeature 2 g)| ^ 3))
    ((cP.sub cN).sub (continuous_const.mul cB))
    (continuous_const.mul (hcw.abs.mul (hcθ.abs.pow 3)))
    (fun g => by
      have h := sinh_cubic (abs_ip_le hX1 hθ g) hκ3
      have e : inner ℝ w (realFeature 2 g) * Real.exp (inner ℝ θ (realFeature 2 g))
          - inner ℝ w (realFeature 2 g) * Real.exp (-inner ℝ θ (realFeature 2 g))
          - 2 * (inner ℝ w (realFeature 2 g) * inner ℝ θ (realFeature 2 g))
          = 2 * inner ℝ w (realFeature 2 g)
            * ((Real.exp (inner ℝ θ (realFeature 2 g))
              - Real.exp (-inner ℝ θ (realFeature 2 g))) / 2 - inner ℝ θ (realFeature 2 g)) := by
        ring
      rw [e, abs_mul, abs_mul, abs_two]
      calc 2 * |inner ℝ w (realFeature 2 g)| * _
          ≤ 2 * |inner ℝ w (realFeature 2 g)| * (cO κ * |inner ℝ θ (realFeature 2 g)| ^ 3) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by ring)
  have iP := integrable_of_continuous (probHaar (SU 2)) cP
  have iN := integrable_of_continuous (probHaar (SU 2)) cN
  have iB := (integrable_of_continuous (probHaar (SU 2)) cB).const_mul (2 : ℝ)
  rw [integral_sub (isub iP iN) iB, integral_sub iP iN, integral_const_mul, integral_const_mul,
    e1] at hb
  rw [h0]
  have e2 : ∫ U : SU 2, inner ℝ w (realFeature 2 U) * Real.exp (inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2))
      - -∫ U : SU 2, inner ℝ w (realFeature 2 U) * Real.exp (inner ℝ θ (realFeature 2 U))
        ∂(probHaar (SU 2))
      - 2 * ∫ U : SU 2, inner ℝ w (realFeature 2 U) * inner ℝ θ (realFeature 2 U)
        ∂(probHaar (SU 2))
      = 2 * (∫ U : SU 2, inner ℝ w (realFeature 2 U) * Real.exp (inner ℝ θ (realFeature 2 U))
          ∂(probHaar (SU 2))
        - ∫ U : SU 2, inner ℝ w (realFeature 2 U) * inner ℝ θ (realFeature 2 U)
          ∂(probHaar (SU 2))) := by ring
  rw [e2, abs_mul, abs_two] at hb
  have e3 : (0 : ℝ) / 2 = 0 := by norm_num
  rw [e3, sub_zero]
  linarith

#print axioms hE1_su2

/-- **Isotropy at `SU(2)`**: `⟪θ, X U⟫ = t Re (A U)₀₀` (`HaarMomentsSU2.exists_rot_su2`) gives the
effective norm `t = ρ/√2` and the moments `t²/4`, `t⁴/8` (`haar_su2_re_sq`, `haar_su2_re_four`); the odd
moments vanish (`feature_third_su2`).

DERIVED: `2` the rank and the square; `4`, `1/8` the constants of `haarConsts_su2`; `0` its `t3`. -/
theorem isoAt_su2 (θ : FE 2) :
    ∃ t, IsoAt (probHaar (SU 2)) (realFeature 2) 4 (1 / 8) 0 θ t := by
  obtain ⟨ρ, A, hρ0, hρ2, hrep⟩ := exists_rot_su2 θ
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t, t = ρ / Real.sqrt 2 := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht2 : t ^ 2 = ρ ^ 2 / 2 := by rw [ht, div_pow, hs]
  have hmom : ∀ k : ℕ, ∫ U : SU 2, inner ℝ θ (realFeature 2 U) ^ k ∂(probHaar (SU 2))
      = t ^ k * ∫ U : SU 2, ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ k ∂(probHaar (SU 2)) := by
    intro k
    rw [← int_left (fun U : SU 2 => ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ k) A,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    show inner ℝ θ (realFeature 2 U) ^ k
      = t ^ k * (((A * U : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ k
    rw [hrep U, mul_pow, ht]
  refine ⟨t, ht0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (sq_le_sq₀ ht0 (norm_nonneg θ)).mp ?_
    rw [ht2]
    linarith
  · rw [hmom 2, haar_su2_re_sq]
    ring
  · rw [hmom 4, haar_su2_re_four]
    exact le_of_eq (by ring)
  · intro u
    have h := feature_third_su2 u θ
    rw [zero_mul, zero_mul] at h ⊢
    exact h
  · intro w
    have h := feature_third_su2 θ w
    rw [zero_mul, zero_mul] at h ⊢
    exact h
  · have h := feature_third_su2 θ θ
    rw [zero_mul, zero_mul] at h
    have e : ∀ U : SU 2, inner ℝ θ (realFeature 2 U) ^ 3
        = inner ℝ θ (realFeature 2 U) ^ 2 * inner ℝ θ (realFeature 2 U) := fun U => by ring
    rw [zero_mul, integral_congr_ae (Filter.Eventually.of_forall e)]
    exact h

#print axioms isoAt_su2

/-- **The second moment at `SU(3)` is exact**: `E⟪w, X⟫² = ‖w‖²/18`.

DERIVED: `3` the rank; `18 = 2 · 3²`, the real dimension of the matrices; `2` the moment order. -/
theorem feature_second_eq_su3 (w : FE 3) :
    ∫ U : SU 3, inner ℝ w (realFeature 3 U) ^ 2 ∂(probHaar (SU 3)) = ‖w‖ ^ 2 / 18 := by
  have hpt : ∀ U : SU 3, inner ℝ w (realFeature 3 U) ^ 2
      = 1 / 6 * (Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))
        + (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 2).re) := by
    intro U
    rw [feat_eq, div_pow, s3_sq]
    simp only [sq, Complex.mul_re, Complex.normSq_apply]
    ring
  have c1 : Continuous (fun U : SU 3 =>
      Complex.normSq (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w))) :=
    Complex.continuous_normSq.comp (trc _)
  have c2 : Continuous (fun U : SU 3 =>
      (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 2).re) :=
    Complex.continuous_re.comp ((trc _).pow 2)
  have h2 : ∫ U : SU 3, (Matrix.trace ((U : Matrix (Fin 3) (Fin 3) ℂ) * featDual 3 w) ^ 2).re
      ∂(probHaar (SU 3)) = 0 := by
    have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM
      (intC ((trc (featDual 3 w)).pow 2))
    simp only [Complex.reCLM_apply] at hre
    rw [hre, tr2_zero, Complex.zero_re]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add (intR c1) (intR c2), h2, normSq_int, frob_featDual]
  ring

#print axioms feature_second_eq_su3

/-- **Isotropy at `SU(3)`**: the effective norm is `‖θ‖` (`feature_second_eq_su3`).

DERIVED: `3` the rank; `18`, `1/96`, `1/108` the constants of `haarConsts_su3`. -/
theorem isoAt_su3 (θ : FE 3) :
    ∃ t, IsoAt (probHaar (SU 3)) (realFeature 3) 18 (1 / 96) (1 / 108) θ t := by
  refine ⟨‖θ‖, norm_nonneg θ, le_rfl, feature_second_eq_su3 θ, HaarMomentsSU3.feature_fourth_su3 θ,
    fun u => HaarMomentsSU3.feature_third_su3 u θ, fun w => HaarMomentsSU3.feature_third_su3 θ w, ?_⟩
  have h := HaarMomentsSU3.feature_third_su3 θ θ
  have e : ∀ U : SU 3, inner ℝ θ (realFeature 3 U) ^ 3
      = inner ℝ θ (realFeature 3 U) ^ 2 * inner ℝ θ (realFeature 3 U) := fun U => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e)]
  calc _ ≤ 1 / 108 * ‖θ‖ ^ 2 * ‖θ‖ := h
    _ = 1 / 108 * ‖θ‖ ^ 3 := by ring

#print axioms isoAt_su3

/-- The `SU(2)` second-moment comparison at `κ = 83/100`.

DERIVED: `1/4`, `0`, `1/8`, `2 * 4` from `haarConsts_su2`. CHOSEN: `83/100 = 10 · 83/1000`, the largest
three-digit coupling below the crossing `0.08307`; `5301/10000` rounds `cE (83/100) = 0.530022…` up;
`2723/10000` rounds the ratio `0.272201…` at `κ` up. DERIVED: `3` the cubic Taylor term; `6 = 3!`. -/
theorem su2_hM (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 83 / 100) :
    1 / (4 : ℝ) + 0 * t + cE (83 / 100) * (1 / 8) * t ^ 2
      ≤ 2723 / 10000 * (1 + t ^ 2 / (2 * 4) - 0 * t ^ 3 / 6) := by
  have hs : t ^ 2 ≤ (83 / 100) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hc : cE (83 / 100) ≤ 5301 / 10000 := by norm_num [cE]
  have ht := mul_le_mul_of_nonneg_right hc (sq_nonneg t)
  nlinarith [sq_nonneg t]

/-- The `SU(2)` mean comparison at `κ = 83/100`.

DERIVED: as `su2_hM`. CHOSEN: `174/1000` rounds `cO (83/100) = 0.173995…` up; `2026/10000` rounds the
ratio `0.202498…` at `κ` up. DERIVED: `1/8`, `2 * 4` from `haarConsts_su2`; `3` the cubic Taylor term;
`6 = 3!`. -/
theorem su2_hm (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 83 / 100) :
    t / (4 : ℝ) + 0 * t ^ 2 / 2 + cO (83 / 100) * (1 / 8) * t ^ 3
      ≤ 2026 / 10000 * (1 + t ^ 2 / (2 * 4) - 0 * t ^ 3 / 6) := by
  have hc : cO (83 / 100) ≤ 174 / 1000 := by norm_num [cO]
  have ht := mul_le_mul_of_nonneg_right hc (pow_nonneg h0 3)
  have hB : 0 ≤ 1 / 4 + 174 / 1000 * (t ^ 2 + t * (83 / 100) + (83 / 100) ^ 2) / 8
      - 2026 / 10000 * (t + 83 / 100) / 8 := by nlinarith [sq_nonneg t]
  have hk := mul_nonneg (sub_nonneg.mpr h1) hB
  nlinarith [hk]

/-- The `SU(3)` second-moment comparison at `κ = 19/10`.

DERIVED: `1/18`, `1/108`, `1/96`, `2 * 18` from `haarConsts_su3`; `6 = 3!`. CHOSEN: `19/10 = 10 · 19/100`,
the two-digit coupling below the crossing `0.1906`; `10605/10000` rounds `cR (19/10) = 1.060441…` up;
`1038/10000` rounds the ratio `0.103722…` at `κ` up. -/
theorem su3_hM (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 19 / 10) :
    1 / (18 : ℝ) + 1 / 108 * t + cR (19 / 10) * (1 / 96) * t ^ 2
      ≤ 1038 / 10000 * (1 + t ^ 2 / (2 * 18) - 1 / 108 * t ^ 3 / 6) := by
  have hc : cR (19 / 10) ≤ 10605 / 10000 := by norm_num [cR]
  have ht := mul_le_mul_of_nonneg_right hc (sq_nonneg t)
  have hB : 0 ≤ 1 / 108 + 10605 / 10000 / 96 * (t + 19 / 10)
      - 1038 / 10000 * (t + 19 / 10) / 36
      + 1038 / 10000 * (t ^ 2 + t * (19 / 10) + (19 / 10) ^ 2) / 648 := by
    nlinarith [sq_nonneg t]
  have hk := mul_nonneg (sub_nonneg.mpr h1) hB
  nlinarith [hk]

/-- The `SU(3)` mean comparison at `κ = 19/10`.

DERIVED: as `su3_hM`. CHOSEN: `295/1000` rounds `c3 (19/10) = 0.294969…` up; `1316/10000` rounds the
ratio `0.131545…` at `κ` up. DERIVED: `1/18`, `1/108`, `1/96`, `2 * 18` from `haarConsts_su3`; `3` the
cubic Taylor term; `6 = 3!`. -/
theorem su3_hm (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 19 / 10) :
    t / (18 : ℝ) + 1 / 108 * t ^ 2 / 2 + c3 (19 / 10) * (1 / 96) * t ^ 3
      ≤ 1316 / 10000 * (1 + t ^ 2 / (2 * 18) - 1 / 108 * t ^ 3 / 6) := by
  have hc : c3 (19 / 10) ≤ 295 / 1000 := by norm_num [c3]
  have ht := mul_le_mul_of_nonneg_right hc (pow_nonneg h0 3)
  have hB : 0 ≤ 1 / 18 + (t + 19 / 10) / 216
      + 295 / 1000 / 96 * (t ^ 2 + t * (19 / 10) + (19 / 10) ^ 2)
      - 1316 / 10000 * (t + 19 / 10) / 36
      + 1316 / 10000 * (t ^ 2 + t * (19 / 10) + (19 / 10) ^ 2) / 648 := by
    nlinarith [sq_nonneg t]
  have hk := mul_nonneg (sub_nonneg.mpr h1) hB
  nlinarith [hk]

/-- **`SU(2)`: the tilted constants at `κ = 83/100`.**

DERIVED: `2` the rank and the range of `Z_ge`; `3` the range of the `exp` bounds; `1` the norm of the
feature. CHOSEN: the rationals of `su2_hM`, `su2_hm`. Inherited: `83/100`, `2723/10000`, `2026/10000` from
`su2_hM`, `su2_hm`. -/
theorem tiltBounds_su2 :
    TiltBounds (probHaar (SU 2)) (realFeature 2) (83 / 100) (2723 / 10000) (2026 / 10000) :=
  tiltBounds_sharp HaarMomentsSU2.haarConsts_su2 (continuous_realFeature 2)
    (fun g => (norm_realFeature (by norm_num) g).le) (cA := cE (83 / 100)) (cB := cO (83 / 100))
    (by norm_num) (by norm_num [cE]) (by norm_num [cO]) (by norm_num) (by norm_num)
    (fun θ _ => isoAt_su2 θ)
    (fun θ u hθ => hE2_su2 (by norm_num) θ u hθ)
    (fun θ w hθ => hE1_su2 (by norm_num) θ w hθ) su2_hM su2_hm

#print axioms tiltBounds_su2

/-- **`SU(3)`: the tilted constants at `κ = 19/10`.**

DERIVED: `3` the rank and the range of the `exp` bounds; `2` the range of `Z_ge`; `1` the norm of the
feature. CHOSEN: the rationals of `su3_hM`, `su3_hm`. Inherited: `19/10`, `1038/10000`, `1316/10000` from
`su3_hM`, `su3_hm`. -/
theorem tiltBounds_su3 :
    TiltBounds (probHaar (SU 3)) (realFeature 3) (19 / 10) (1038 / 10000) (1316 / 10000) :=
  tiltBounds_sharp HaarMomentsSU3.haarConsts_su3 (continuous_realFeature 3)
    (fun g => (norm_realFeature (by norm_num) g).le) (cA := cR (19 / 10)) (cB := c3 (19 / 10))
    (by norm_num) (by norm_num [cR]) (by norm_num [c3]) (by norm_num) (by norm_num)
    (fun θ _ => isoAt_su3 θ)
    (fun θ u hθ => hE2_gen (continuous_realFeature 3)
      (fun g => (norm_realFeature (by norm_num) g).le) (by norm_num) θ u hθ)
    (fun θ w hθ => hE1_gen HaarMomentsSU3.haarConsts_su3 (continuous_realFeature 3)
      (fun g => (norm_realFeature (by norm_num) g).le) (by norm_num) θ w hθ) su3_hM su3_hm

#print axioms tiltBounds_su3

/-- **`SU(2)`, the single pair at `β = 83/1000`.**

DERIVED: `83/500 = 2 · 83/1000`, `83/100 = 10 · 83/1000` the single pair's counts; `3` the range of
`exp_sub_one_sub_le`; `0`, `1` the sign and the norm of the feature. CHOSEN: `5219/10000 ≥ √(2723/10000)`;
`5132/100000` rounds the computed `0.0512993…` up. -/
theorem fibre_su2 :
    FibreBound (probHaar (SU 2)) (realFeature 2) (5132 / 100000) (83 / 500) (83 / 100) := by
  have hF := fibreBound_of_tiltBounds (P := probHaar (SU 2)) (continuous_realFeature 2)
    (fun g => (norm_realFeature (by norm_num) g).le) (τ := 83 / 500) (σ := 5219 / 10000)
    (c₂ := cR (83 / 500)) (by norm_num) (by norm_num) (by norm_num)
    (cR_nonneg (by norm_num)) tiltBounds_su2
    (fun u hu => exp_sub_one_sub_le hu (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num [dstarZ]) (by norm_num [dstarDen, dstarE, dstarZ, cR])
  refine hF.mono ?_ le_rfl le_rfl
  norm_num [dstar, dstarNum, dstarDen, dstarE, dstarZ, cR]

#print axioms fibre_su2

/-- **`SU(3)`, the single pair at `β = 19/100`.**

DERIVED: `19/50 = 2 · 19/100`, `19/10 = 10 · 19/100` the single pair's counts; `3` the rank and the range
of `exp_sub_one_sub_le`; `0`, `1` the sign and the norm of the feature. CHOSEN:
`3222/10000 ≥ √(1038/10000)`; `51/1000` rounds the computed `0.0509743…` up. -/
theorem fibre_su3 :
    FibreBound (probHaar (SU 3)) (realFeature 3) (51 / 1000) (19 / 50) (19 / 10) := by
  have hF := fibreBound_of_tiltBounds (P := probHaar (SU 3)) (continuous_realFeature 3)
    (fun g => (norm_realFeature (by norm_num) g).le) (τ := 19 / 50) (σ := 3222 / 10000)
    (c₂ := cR (19 / 50)) (by norm_num) (by norm_num) (by norm_num)
    (cR_nonneg (by norm_num)) tiltBounds_su3
    (fun u hu => exp_sub_one_sub_le hu (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num [dstarZ]) (by norm_num [dstarDen, dstarE, dstarZ, cR])
  refine hF.mono ?_ le_rfl le_rfl
  norm_num [dstar, dstarNum, dstarDen, dstarE, dstarZ, cR]

#print axioms fibre_su3

end Groups

/-! ## 6. No double partner past extent `2` -/

section Count

/-- **Past extent `2` no pair has count `4`.** A count of `4` needs the two bases `y`, `y − ev σ` on the
same partner `(a, y + ev ρ) = (a, y − ev σ)`, so `ev ρ + ev σ = 0`: impossible at `ρ ≠ σ`
(`PairCount.ev_add_ne_zero`), and at `ρ = σ` it reads `1 + 1 = 0` in `Fin (M + 1)`.

DERIVED: `2` the least `M` with `1 + 1 ≠ 0` (extent `3`); `4` the count and the spacetime dimension; `1`
the successor writing the extent. -/
theorem n2_ne_four {M : ℕ} (hM : 2 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) :
    n2 M l m ≠ 4 := by
  obtain ⟨a, y⟩ := l
  have hk : m ≠ (a, y) := Ne.symm hlm
  have hM1 : 1 ≤ M := by omega
  intro h4
  rw [n2_eq_card hM1 a y m, card_T_eq a y m] at h4
  have hc2 : (tp a y m).card = 2 := by omega
  have hma : m.1 = a := by
    by_contra hne
    have := card_tp_le_one hM1 hk hne
    omega
  have hex : ∀ b : Bool, ∃ ρ, (b, ρ) ∈ tp a y m := by
    intro b
    by_contra hno
    push_neg at hno
    have hle : (tp a y m).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro r hr r' hr'
      apply tp_fst_inj hM1 hk hr hr'
      obtain ⟨t, ρ⟩ := r
      obtain ⟨t', σ⟩ := r'
      have ht : t ≠ b := fun e => hno ρ (e ▸ hr)
      have ht' : t' ≠ b := fun e => hno σ (e ▸ hr')
      show t = t'
      cases t <;> cases t' <;> cases b <;> simp_all
    omega
  obtain ⟨ρ, hρ⟩ := hex true
  obtain ⟨σ, hσ⟩ := hex false
  have hρ' := Finset.mem_filter.mp hρ
  have hσ' := Finset.mem_filter.mp hσ
  have hρa : ρ ≠ a := (Finset.mem_erase.mp (Finset.mem_product.mp hρ'.1).2).1
  have hσa : σ ≠ a := (Finset.mem_erase.mp (Finset.mem_product.mp hσ'.1).2).1
  have e1 : m = (a, y + ev M ρ) := by
    rcases mem_plq_true hk hρ'.2 with h1 | h1
    · exact absurd (hma.symm.trans h1) (Ne.symm hρa)
    · exact h1
  have e2 : m = (a, y - ev M σ) := by
    rcases mem_plq_true hk hσ'.2 with h1 | h1
    · exact absurd (hma.symm.trans h1) (Ne.symm hσa)
    · exact h1
  have e3 : y + ev M ρ = y - ev M σ := congrArg Prod.snd (e1.symm.trans e2)
  have e4 : ev M ρ + ev M σ = 0 := by
    have h5 : y + (ev M ρ + ev M σ) = y + 0 := by
      calc y + (ev M ρ + ev M σ) = (y + ev M ρ) + ev M σ := by abel
        _ = (y - ev M σ) + ev M σ := by rw [e3]
        _ = y + 0 := by abel
    exact add_left_cancel h5
  by_cases hrs : ρ = σ
  · subst hrs
    have h6 := congrFun e4 ρ
    rw [Pi.add_apply, ev_self, Pi.zero_apply] at h6
    have h7 : (((1 : Fin (M + 1)) + 1 : Fin (M + 1)) : ℕ) = 2 := by
      have hv : ((1 : Fin (M + 1)) : ℕ) = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [Fin.val_add, hv, Nat.mod_eq_of_lt (by omega)]
    rw [h6] at h7
    simp at h7
  · exact ev_add_ne_zero hM1 hrs e4

#print axioms n2_ne_four

end Count

/-! ## 7. The box gap from the single pair -/

section Box

variable {N : ℕ}

/-- **The two-link correlation past extent `2` from the single-pair fibre bound** (`n2_ne_four`,
`PairCount.n2_cases`, `PairCorrSharp.pairCorr_twoCond_sharp`).

DERIVED: `1` the least `j` with extent `4`; `2`, `10 = 12 − 2` the coupling and tilt counts of a single
pair; `0` the defect of a product law and the lower ends. -/
theorem pairCorrAt_single (hN : N ≠ 0) {β δ : ℝ} (hβ0 : 0 ≤ β) {j : ℕ} (hj : 1 ≤ j)
    (h1 : FibreBound (probHaar (SU N)) (realFeature N) δ (2 * β) (10 * β)) (hδ : 0 ≤ δ) :
    PairCorrAt hN β j (pairDeltaSharp δ 0 j) := by
  intro l m hlm x
  refine ⟨twoCondExp β (2 * j + 1) l m x, PairCorr.torusCondExp_twoCondExp_l β (2 * j + 1) hlm x,
    PairCorr.torusCondExp_twoCondExp_m β (2 * j + 1) l m x, ?_⟩
  have hM : 1 ≤ 2 * j + 1 := by omega
  have hne := n2_ne_four (M := 2 * j + 1) (by omega) hlm
  rcases n2_cases hM hlm with h0 | h2' | h4
  · have hd : pairDeltaSharp δ 0 j l m = 0 := by
      unfold pairDeltaSharp
      rw [if_neg hlm, h0, if_neg (show ¬ (0 : ℕ) = 2 by norm_num),
        if_neg (show ¬ (0 : ℕ) = 4 by norm_num)]
    have hB : FibreBound (probHaar (SU N)) (realFeature N) 0 (β * (n2 (2 * j + 1) l m : ℝ))
        (β * (12 - (n2 (2 * j + 1) l m : ℝ))) := by
      rw [h0, Nat.cast_zero, mul_zero]
      exact fibreBound_zero (continuous_realFeature N) _
    rw [hd]
    exact pairCorr_twoCond_sharp hN hβ0 j hlm le_rfl hB x
  · have hd : pairDeltaSharp δ 0 j l m = δ := by
      unfold pairDeltaSharp
      rw [if_neg hlm, if_pos h2']
    have hB : FibreBound (probHaar (SU N)) (realFeature N) δ (β * (n2 (2 * j + 1) l m : ℝ))
        (β * (12 - (n2 (2 * j + 1) l m : ℝ))) := by
      have e1 : β * (n2 (2 * j + 1) l m : ℝ) = 2 * β := by
        rw [h2']
        push_cast
        ring
      have e2 : β * (12 - (n2 (2 * j + 1) l m : ℝ)) = 10 * β := by
        rw [h2']
        push_cast
        ring
      rw [e1, e2]
      exact h1
    rw [hd]
    exact pairCorr_twoCond_sharp hN hβ0 j hlm hδ hB x
  · exact absurd h4 hne

#print axioms pairCorrAt_single

/-- **The local gap from the single-pair fibre bound at every side `n ≥ 2`.** `BoxLocalGap` reads only
`n ≤ j + 1`, so extent `2` never enters and the row sum is `18 δ`.

DERIVED: `18 = 36/2` the partners of a link (`PairCorrSharp.pairDeltaSharp_row` at `δ₂ = 0`); `1` the gap
at zero defect; `2` the least side with `j ≥ 1`; `2`, `10` as in `pairCorrAt_single`. -/
theorem boxLocalGap_of_singleFibre (hN : N ≠ 0) {β δ : ℝ} (hβ0 : 0 ≤ β) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h1 : FibreBound (probHaar (SU N)) (realFeature N) δ (2 * β) (10 * β)) {n : ℕ} (hn : 2 ≤ n) :
    BoxLocalGap hN β n (1 - 18 * δ) := by
  intro j hj k x
  have hj1 : 1 ≤ j := by omega
  have hD := pairDeltaSharp_defect hδ le_rfl j
  have hmax : max (18 * δ) (12 * δ + 3 * 0) = 18 * δ :=
    max_eq_left (by nlinarith)
  rw [hmax] at hD
  have hle : ∀ l m, pairDeltaSharp δ 0 j l m ≤ 1 := by
    intro l m
    unfold pairDeltaSharp
    split_ifs
    · exact zero_le_one
    · exact hδ1
    · exact zero_le_one
    · exact zero_le_one
  have hpd := pairDefectAt_of_pairCorrAt hN β j (pairDeltaSharp δ 0 j) hD.1 hle
    (pairCorrAt_single hN hβ0 hj1 h1 hδ)
  exact patch_gap_of_defect (torusForm hN β j) (torusForm_nonneg hN β j)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp β (2 * j + 1) l)
    (fun l => selfAdj_id_sub (torusForm hN β j) (torusCondExp β (2 * j + 1) l)
      (torusCondExp_selfAdj hN β j l))
    (fun l => idem_id_sub (torusCondExp β (2 * j + 1) l) (torusCondExp_idem β (2 * j + 1) l))
    (boxWeight n) k (fun l => boxWeight_cases n k l) (pairDeltaSharp δ 0 j) hD x
    (fun l m hlm _ _ => hpd l m hlm x)

#print axioms boxLocalGap_of_singleFibre

/-- **`SU(2)`: the box gap on `[0, 83/1000]`.** The range contains `0.0817`, the coupling that mirrors
`3/40` across the peak of `aRun`, which `BoxGapBE` does not reach.

DERIVED: `2` the rank; `15` the box side; `953/12500 = 1 − 18 · 5132/100000`; `83/500`, `83/100` the
counts `2`, `10` at the end coupling. Inherited: `83/1000` the end coupling chosen in `su2_hM`, the largest
three-digit coupling below the crossing `0.08307`. -/
theorem boxLocalGap15_su2_hs (h2 : (2 : ℕ) ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 83 / 1000) :
    BoxPatch.BoxLocalGap h2 β 15 (953 / 12500) := by
  have hF : FibreBound (probHaar (SU 2)) (realFeature 2) (5132 / 100000) (2 * β) (10 * β) :=
    fibre_su2.mono le_rfl (by linarith) (by linarith)
  have h := boxLocalGap_of_singleFibre h2 hβ0 (by norm_num) (by norm_num) hF (n := 15) (by norm_num)
  have e : (1 : ℝ) - 18 * (5132 / 100000) = 953 / 12500 := by norm_num
  rw [e] at h
  exact h

#print axioms boxLocalGap15_su2_hs

/-- **`SU(3)`: the box gap on `[0, 19/100]`.**

DERIVED: `3` the rank; `15` the box side; `41/500 = 1 − 18 · 51/1000`; `19/50`, `19/10` the counts `2`,
`10` at the end coupling. Inherited: `19/100` the end coupling chosen in `su3_hM`, the two-digit coupling
below the crossing `0.1906`. -/
theorem boxLocalGap15_su3_hs (h3 : (3 : ℕ) ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 19 / 100) :
    BoxPatch.BoxLocalGap h3 β 15 (41 / 500) := by
  have hF : FibreBound (probHaar (SU 3)) (realFeature 3) (51 / 1000) (2 * β) (10 * β) :=
    fibre_su3.mono le_rfl (by linarith) (by linarith)
  have h := boxLocalGap_of_singleFibre h3 hβ0 (by norm_num) (by norm_num) hF (n := 15) (by norm_num)
  have e : (1 : ℝ) - 18 * (51 / 1000) = 41 / 500 := by norm_num
  rw [e] at h
  exact h

#print axioms boxLocalGap15_su3_hs

end Box

/-! ## 8. The continuum statement at the new end couplings -/

section Clay

open MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **`SU(2)`: the continuum Clay statement from the UV step at `β₀ = 83/1000`.**

DERIVED: `2` the rank; `83/1000`, `15`, `953/12500` the coupling, side and gap of `boxLocalGap15_su2_hs`;
`0` the reflection plane; `4` the spacetime dimension. -/
theorem clay_of_uvStep_su2_hs (h2 : (2 : ℕ) ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU 2) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep h2 (Renorm.connected h2 Z)) {L : ℝ} (hL : 0 < L)
    {βUV : ℝ} (hUV : βUV ≤ 83 / 1000)
    (huv : ClayRoutes.UVBelowIR τ 0 h2 (83 / 1000) βUV
      (MassGap.WeightedBox.weightedRate 2 (83 / 1000)
        (MassGap.WeightedBox.weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e (953 / 12500))))
    (O : LField (MassGap.SUN.SU 2)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep h2 (Renorm.connected h2 Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum h2 Z τ hZ hB L :=
  BoxGapBE.clay15_of_localGap (by norm_num) h2 Z τ hZ hB hL (by norm_num) hUV (by norm_num)
    (boxLocalGap15_su2_hs h2 (by norm_num) le_rfl) huv O G hconv hY

#print axioms clay_of_uvStep_su2_hs

/-- **`SU(3)`: the continuum Clay statement from the UV step at `β₀ = 19/100`.**

DERIVED: `3` the rank; `19/100`, `15`, `41/500` the coupling, side and gap of `boxLocalGap15_su3_hs`; `0`
the reflection plane; `4` the spacetime dimension. -/
theorem clay_of_uvStep_su3_hs (h3 : (3 : ℕ) ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU 3) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep h3 (Renorm.connected h3 Z)) {L : ℝ} (hL : 0 < L)
    {βUV : ℝ} (hUV : βUV ≤ 19 / 100)
    (huv : ClayRoutes.UVBelowIR τ 0 h3 (19 / 100) βUV
      (MassGap.WeightedBox.weightedRate 3 (19 / 100)
        (MassGap.WeightedBox.weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e (41 / 500))))
    (O : LField (MassGap.SUN.SU 3)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep h3 (Renorm.connected h3 Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum h3 Z τ hZ hB L :=
  BoxGapBE.clay15_of_localGap (by norm_num) h3 Z τ hZ hB hL (by norm_num) hUV (by norm_num)
    (boxLocalGap15_su3_hs h3 (by norm_num) le_rfl) huv O G hconv hY

#print axioms clay_of_uvStep_su3_hs

end Clay

end MassGap.BoxGapHS
