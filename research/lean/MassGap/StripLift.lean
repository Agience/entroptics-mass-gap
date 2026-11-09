import Mathlib
import MassGap.StripGapThm
import MassGap.MixPlane

/-!
# MassGap.StripLift — the anisotropic transfer gap lifted above the glued strip

`StripGapThm.strip_gap` gives a transfer gap on the anisotropic torus for `0 ≤ t ≤ t_glue(N, β)`. Its only input
is one finite-window seed `DA(β, t, w₀) ≤ 1/1000`. This module reads that dependence in full: the gap holds at
every coupling pair that has a seed at some window, with rate `log 2 / 2^w` set by the window, uniformly in the
torus size. It then places that set above the strip. Declarations are in `MassGap.StripLift`.

## The result

* `TransferGapAt hN hβ ht m w`: in every direction `μ` and at every window `v ≥ w`, the transverse transfer
  operator `K = StripGapThm.KA` of the cubic torus of side `2^v` has a unit eigenvector `ψ` at `|e| = ‖K‖` and
  `‖K^r f‖ ≤ 2 e^{−m r} ‖K‖^r ‖f‖` for every lag `r` and `f ⊥ ψ`.
* `gap_of_seed`: `DA(β, t, w) ≤ 1/1000` at one window `w ≥ 1` gives `TransferGapAt` at rate
  `seedMass w = log 2 / 2^w`.
* `tLift N β = 1/(4048 · 4^{w₀})`, `tGlue_le_tLift`, `tLift_le`: `t_glue ≤ t_lift ≤ 4 t_glue`.
* `seed_lift_lt`, `lift_gap`: the seed holds strictly, and the gap at the strip rate `m = stripMass N β` holds,
  for `0 ≤ t ≤ t_lift`.
* `exists_beyond`, `beyond_gap`: some `ε > 0` (existential) keeps the strict seed at the same window `w₀`, and so
  the gap at the same rate `m`, for `0 ≤ t ≤ t_lift + ε`.
* `gap_on_vanishSet`: every point of `MixPlane.VanishSet N` carries a transfer gap. The gap region of the seed
  route is the whole vanishing set.
* `seed_mono_lt`, `segment_seed`, `segment_gap`: if the segment `{β} × [0, t']` lies in the vanishing set, one
  window `w` serves the whole segment, so the gap holds on it at the single rate `log 2 / 2^w`.
* `diag_gap`: on the isotropic diagonal `t = β`, for `0 ≤ β < b` with `b > 0` existential, the transfer gap holds.

## The region in `(β, t)`

Proved in closed form: `0 ≤ t ≤ t_lift(N, β) = 1/(4048 · 4^{w₀(β)})`, with `t_glue ≤ t_lift ≤ 4 t_glue`, so
`t_lift ≍ c_N⁻¹ (β log β)⁻¹` (read off, not a Lean statement). Proved with an existential margin: `t ≤ t_lift + ε(β)`.
Proved structurally: every segment `{β} × [0, t']` in `VanishSet N`, at a rate uniform on the segment. The
continuation in `t` runs exactly until the first stall `MixPlane.segment_first_stall`; the form without
`TwoDCharacter`, with one rate on each closed `[0, t']` below it, is `StripClose.gap_below_first_stall`.

DERIVED (module-wide): `2` the doubling, the excited ratio and the prefactor; `4 = 2²` the area of the doubling;
`1` the least window and the unit vector; `0` the vacuum and the decoupled end. Inherited: `1/1000` the seed of
`DoublingSharp`; `1/2000` of `StripWiden.seed_glue`; `8192` of `StripWidth.DA_le`; `4048`, `16192` of
`StripWidth.strip_of_seed` and `StripWiden.tGlue`. COMPUTED: `8192 · 2000 = 16384000 < 16386304 = 4048²`, so the
mixed term at `t_lift` is strictly below `1/2000`; `4 · 4048 = 16192`.

## What does not follow

* No closed form for `ε(β)` or for the first stall. `t_lift` is the end of the Hoeffding bound
  `DA(β, t, w) ≤ DA(β, 0, w) + 8192 · 16^w t²` at the seed window: the bound pays `16^w t²` while the decoupled
  seed `DA(β, 0, w) ≤ 1/2000` needs `4^w ≳ A_glue ≍ β log β`. Every window gives `t ≲ 4^{−w}`, so this bound
  caps at `t ≍ (β log β)⁻¹` at every window.
* No volume-independent perturbation of the gap in `t`. The kernel of `KA` carries the mixed action of a whole
  slab; `δt` moves it by up to `δt · MixAnchor.tpCMax`, a sum over the transverse slice, so a Kato/Weyl step from
  the strip gap shrinks with the torus side. The transfer operator is not a sum of local terms, so no Knabe patch
  bound applies to it.
* No gap is shown at `t = β` for large `β`: `(β, β) ∈ VanishSet N ↔ StrongAnchor.Vanishes N β`
  (`MixPlane.diag_mem_iff`), so reaching the diagonal by this route is the isotropic seed itself.
* The rate shrinks with `β`: it is `log 2 / 2^w` in lattice units with `4^w ≳ A_glue(N, β)`, and `A_glue` grows with
  `β`. Nothing bounds it below uniformly in `β`, and no continuum statement follows. No infinite-volume operator or state is built. The transfer form is
  not shown equal to a correlation of gauge-invariant lattice observables.
-/

namespace MassGap.StripLift

open MeasureTheory Filter Topology Set MassGap MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SlabKernelOperator MassGap.DoublingRecursion MassGap.MixAnchor

variable {N : ℕ}

/-! ## 1. The gap from any seed window -/

/-- **The window rate** `log 2 / 2^w`, in lattice units. DERIVED: `2` the excited ratio and the doubling. -/
noncomputable def seedMass (w : ℕ) : ℝ := Real.log 2 / 2 ^ w

theorem seedMass_pos (w : ℕ) : 0 < seedMass w := by
  unfold seedMass
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

/-- The strip rate is the window rate at `w₀`. No numeral. -/
theorem stripMass_eq (β : ℝ) : StripGapThm.stripMass N β = seedMass (StripGapThm.seedWindow N β) := rfl

/-- **The transfer gap at rate `m` from window `w` on**: in every direction `μ` and at every window `v ≥ w`, the
transverse transfer operator `K` of the anisotropic cubic torus of side `2^v` has a unit eigenvector `ψ` at
`|e| = ‖K‖`, and `‖K^r f‖ ≤ 2 e^{−m r} ‖K‖^r ‖f‖` for every lag `r` and `f ⊥ ψ`. DERIVED: `2` the prefactor;
`1` the unit vector; `0` the vacuum. -/
def TransferGapAt (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (m : ℝ) (w : ℕ) : Prop :=
  ∀ (μ : Fin 4) (v : ℕ), w ≤ v →
    ∃ ψ : Lp ℝ 2 (hS μ (tr (fun _ => 2 ^ v) μ) N), ‖ψ‖ = 1 ∧
      ∃ e : ℝ, |e| = ‖StripGapThm.KA hN hβ ht μ (tr (fun _ => 2 ^ v) μ)‖ ∧
        StripGapThm.KA hN hβ ht μ (tr (fun _ => 2 ^ v) μ) ψ = e • ψ ∧
        ∀ f : Lp ℝ 2 (hS μ (tr (fun _ => 2 ^ v) μ) N), inner ℝ f ψ = 0 →
          ∀ r : ℕ, ‖((StripGapThm.KA hN hβ ht μ (tr (fun _ => 2 ^ v) μ)) ^ r) f‖
              ≤ 2 * Real.exp (-(m * r)) * ‖StripGapThm.KA hN hβ ht μ (tr (fun _ => 2 ^ v) μ)‖ ^ r * ‖f‖

/-- **`gap_of_seed`: one seed window gives the gap.** If `DA(β, t, w) ≤ 1/1000` at a window `w ≥ 1`, then
`TransferGapAt` holds at rate `log 2 / 2^w` from window `w` on, uniformly in the torus side. Inherited: `1/1000`
the seed of `DoublingSharp`. DERIVED: `2` the doubling; `1` the least window; `1/1000` the sharp seed
threshold of `DoublingSharp.rec_sharp`. -/
theorem gap_of_seed (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {w : ℕ} (hw1 : 1 ≤ w)
    (h0 : AnisoTorus.DA N β t w ≤ 1 / 1000) : TransferGapAt hN hβ ht (seedMass w) w := by
  intro μ v hv
  obtain ⟨k, rfl⟩ : ∃ k, v = w + k := ⟨v - w, by omega⟩
  have hT : tr (DoublingWilson.ext (2 ^ w) (corner k)) μ = tr (fun _ => 2 ^ (w + k)) μ := by
    congr 1; funext i; simp only [DoublingWilson.ext, corner]; rw [← pow_add, add_comm]
  obtain ⟨ψ, hψ1, e, he, hKψ, hg, -⟩ := StripGapThm.gap_core hN hβ ht hw1 h0 μ k _ hT
  refine ⟨ψ, hψ1, e, he, hKψ, fun f hf r => ?_⟩
  have hK : ∀ u₁ u₂, inner ℝ (StripGapThm.KA hN hβ ht μ (tr (fun _ => 2 ^ (w + k)) μ) u₁) u₂
      = inner ℝ u₁ (StripGapThm.KA hN hβ ht μ (tr (fun _ => 2 ^ (w + k)) μ) u₂) := by
    intro u₁ u₂
    unfold StripGapThm.KA
    exact (SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm _ 1 _ zero_le_one _ _
      (kC_symm (cA β t))).isSymmetric u₁ u₂
  have h := StripGapThm.pow_gap_all hK hKψ (by positivity) hg f hf r
  have em : Real.log 2 / ((2 ^ w : ℕ) : ℝ) = seedMass w := by
    unfold seedMass; push_cast; rfl
  rwa [em] at h

/-! ## 2. The closed-form lift `t_lift` -/

/-- **The lifted width** `t_lift(N, β) = 1/(4048 · 4^{w₀})`, the end of `StripWidth.strip_of_seed` at the seed
window `w₀ = seedWindow N β`. Inherited: `4048` of `StripWidth.strip_of_seed`. DERIVED: `4 = 2²`. -/
noncomputable def tLift (N : ℕ) (β : ℝ) : ℝ := 1 / (4048 * (4 : ℝ) ^ StripGapThm.seedWindow N β)

theorem tLift_pos (β : ℝ) : 0 < tLift N β := by unfold tLift; positivity

/-- **The lift contains the glued strip**: `t_glue ≤ t_lift`, from `4^{w₀} ≤ 4 A_glue`. COMPUTED:
`4 · 4048 = 16192`. -/
theorem tGlue_le_tLift {β : ℝ} (hβ : 0 ≤ β) : StripWiden.tGlue N β ≤ tLift N β := by
  obtain ⟨-, -, h2⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  have hA := StripGapThm.one_lt_areaG (N := N) hβ
  have e : StripWiden.tGlue N β = 1 / (16192 * StripGapThm.areaG N β) := rfl
  rw [e]
  unfold tLift
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **The lift is at most four strips**: `t_lift ≤ 4 t_glue`, from `A_glue ≤ 4^{w₀}`. COMPUTED:
`4 · 4048 = 16192`. -/
theorem tLift_le {β : ℝ} (hβ : 0 ≤ β) : tLift N β ≤ 4 * StripWiden.tGlue N β := by
  obtain ⟨-, h1, -⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  have hA := StripGapThm.one_lt_areaG (N := N) hβ
  have e : 4 * StripWiden.tGlue N β = 1 / (4048 * StripGapThm.areaG N β) := by
    show 4 * (1 / (16192 * StripGapThm.areaG N β)) = _
    have hApos : 0 < StripGapThm.areaG N β := by linarith
    field_simp; ring
  rw [e]
  unfold tLift
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- **The strict seed up to `t_lift`**: `DA(β, t, w₀) < 1/1000` for `0 ≤ t ≤ t_lift`. Inherited: `1/2000` of
`StripWiden.seed_glue`, `8192` of `StripWidth.DA_le`. COMPUTED: `8192 · 2000 < 4048²`. -/
theorem seed_lift_lt (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (htl : t ≤ tLift N β) :
    AnisoTorus.DA N β t (StripGapThm.seedWindow N β) < 1 / 1000 := by
  obtain ⟨hw, h1, -⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  have h0 : AnisoTorus.DA N β 0 (StripGapThm.seedWindow N β) ≤ 1 / 2000 :=
    StripWiden.seed_glue hN hβ (StripWidth.bulkExp_nonneg β) (StripWidth.one_div_bk_le hN hβ) hw h1
  have hpos : (0 : ℝ) < (4 : ℝ) ^ StripGapThm.seedWindow N β := by positivity
  have htw : (4 : ℝ) ^ StripGapThm.seedWindow N β * t ≤ 1 / 4048 := by
    unfold tLift at htl
    rw [le_div_iff₀ (by positivity)] at htl
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hsq : ((4 : ℝ) ^ StripGapThm.seedWindow N β * t) ^ 2 ≤ (1 / 4048) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hpos.le ht) htw 2
  have hD := StripWidth.DA_le hN β t hw
  have e : ((4 : ℝ) ^ StripGapThm.seedWindow N β) ^ 2 * t ^ 2
      = ((4 : ℝ) ^ StripGapThm.seedWindow N β * t) ^ 2 := by ring
  nlinarith

/-- **`lift_gap`: the strip gap up to `t_lift`**, at the strip rate `m = stripMass N β` from window `w₀` on.
No numeral beyond those of `seed_lift_lt`. -/
theorem lift_gap (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (htl : t ≤ tLift N β) :
    TransferGapAt hN hβ ht (StripGapThm.stripMass N β) (StripGapThm.seedWindow N β) := by
  obtain ⟨hw, -, -⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  exact gap_of_seed hN hβ ht hw (seed_lift_lt hN hβ ht htl).le

/-! ## 3. Past `t_lift` at the same window -/

/-- **An open margin past `t_lift`**: some `ε > 0` keeps `DA(β, t, w₀) < 1/1000` for `0 ≤ t ≤ t_lift + ε`, by the
continuity `MixAnchor.continuous_DA` at the strict seed. `ε` is existential. DERIVED: `2` the half margin; `1/1000` the sharp seed threshold of
`DoublingSharp.rec_sharp`. -/
theorem exists_beyond (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t ≤ tLift N β + ε →
      AnisoTorus.DA N β t (StripGapThm.seedWindow N β) < 1 / 1000 := by
  have h0 := seed_lift_lt hN hβ (tLift_pos (N := N) β).le le_rfl
  have hev : ∀ᶠ s in 𝓝 (tLift N β), AnisoTorus.DA N β s (StripGapThm.seedWindow N β) < 1 / 1000 :=
    ((MixAnchor.continuous_DA (N := N) β _).tendsto (tLift N β)).eventually (eventually_lt_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ / 2, by positivity, fun t ht htl => ?_⟩
  by_cases hle : t ≤ tLift N β
  · exact seed_lift_lt hN hβ ht hle
  · rw [not_le] at hle
    refine hball ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-- **`beyond_gap`: the gap at the strip rate past `t_lift`.** Some `ε > 0` (existential) gives `TransferGapAt` at
rate `m = stripMass N β` from window `w₀` on, for every `0 ≤ t ≤ t_lift + ε`. No numeral. -/
theorem beyond_gap (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ ε > 0, ∀ (t : ℝ) (ht : 0 ≤ t), t ≤ tLift N β + ε →
      TransferGapAt hN hβ ht (StripGapThm.stripMass N β) (StripGapThm.seedWindow N β) := by
  obtain ⟨hw, -, -⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  obtain ⟨ε, hε, h⟩ := exists_beyond hN hβ
  exact ⟨ε, hε, fun t ht htl => gap_of_seed hN hβ ht hw (h t ht htl).le⟩

/-! ## 4. The whole vanishing set -/

/-- **`gap_on_vanishSet`: vanishing gives the gap.** At every `(β, t) ∈ MixPlane.VanishSet N` some window
`w ≥ 1` gives `TransferGapAt` at rate `log 2 / 2^w`. DERIVED: `1` the least window. -/
theorem gap_on_vanishSet (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (hp : (β, t) ∈ MixPlane.VanishSet N) : ∃ w : ℕ, 1 ≤ w ∧ TransferGapAt hN hβ ht (seedMass w) w := by
  obtain ⟨-, -, w, hw, h⟩ := (MixPlane.mem_vanishSet_iff_seed hN).mp hp
  exact ⟨w, hw, gap_of_seed hN hβ ht hw h⟩

/-- **The strict seed passes up the windows**: `DA(β, t, w) < 1/1000` gives `DA(β, t, w + 1) < 1/1000`, by
`MixAnchor.DA_contracts`. Inherited: `1/1000`, `1/4`. DERIVED: `1` the step; `1/1000` the sharp seed
threshold of `DoublingSharp.rec_sharp`. -/
theorem seed_mono_lt (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {w : ℕ} (hw : 1 ≤ w)
    (h : AnisoTorus.DA N β t w < 1 / 1000) : AnisoTorus.DA N β t (w + 1) < 1 / 1000 := by
  have hc := MixAnchor.DA_contracts hN hβ ht hw h.le
  have hn := MixAnchor.DA_nonneg hN hβ ht hw
  linarith

/-- **One window for a segment**: if `{β} × [0, t']` lies in `VanishSet N`, one window `w ≥ 1` has
`DA(β, s, w) < 1/1000` for every `0 ≤ s ≤ t'`. Compactness of `[0, t']` against the open seed sets, nested in the
window by `seed_mono_lt`. DERIVED: `1` the least window; `0` the lower end; `1/1000` the sharp seed
threshold of `DoublingSharp.rec_sharp`. -/
theorem segment_seed (hN : N ≠ 0) {β t' : ℝ} (hβ : 0 ≤ β)
    (h : ∀ s : ℝ, 0 ≤ s → s ≤ t' → (β, s) ∈ MixPlane.VanishSet N) :
    ∃ w : ℕ, 1 ≤ w ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t' → AnisoTorus.DA N β s w < 1 / 1000 := by
  let U : ℕ → Set ℝ := fun k => {s | AnisoTorus.DA N β s (k + 1) < 1 / 1000} ∪ Iio 0
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (isOpen_lt (MixAnchor.continuous_DA (N := N) β (k + 1)) continuous_const).union isOpen_Iio
  have hmono : Monotone U := by
    refine monotone_nat_of_le_succ fun k s hs => ?_
    rcases hs with hs | hs
    · by_cases h0 : 0 ≤ s
      · exact Or.inl (seed_mono_lt hN hβ h0 (by omega) hs)
      · exact Or.inr (show s < 0 from lt_of_not_ge h0)
    · exact Or.inr hs
  have hcov : Icc 0 t' ⊆ ⋃ k, U k := by
    rintro s ⟨h0, h1⟩
    obtain ⟨-, w, hw, hlt⟩ := (MixPlane.mem_vanishSet_iff_seed_lt hN).mp (h s h0 h1)
    refine mem_iUnion.mpr ⟨w - 1, Or.inl ?_⟩
    show AnisoTorus.DA N β s (w - 1 + 1) < 1 / 1000
    rw [Nat.sub_add_cancel hw]
    exact hlt
  obtain ⟨k, hk⟩ := isCompact_Icc.elim_directed_cover U hUo hcov hmono.directed_le
  refine ⟨k + 1, by omega, fun s h0 h1 => ?_⟩
  rcases hk ⟨h0, h1⟩ with h' | h'
  · exact h'
  · exact absurd (show s < 0 from h') (not_lt.mpr h0)

/-- **`segment_gap`: the gap along a vanishing segment at one rate.** If `{β} × [0, t']` lies in `VanishSet N`,
one window `w ≥ 1` gives `TransferGapAt` at rate `log 2 / 2^w` at every `0 ≤ s ≤ t'`. DERIVED: `1` the least
window. -/
theorem segment_gap (hN : N ≠ 0) {β t' : ℝ} (hβ : 0 ≤ β)
    (h : ∀ s : ℝ, 0 ≤ s → s ≤ t' → (β, s) ∈ MixPlane.VanishSet N) :
    ∃ w : ℕ, 1 ≤ w ∧ ∀ (s : ℝ) (hs : 0 ≤ s), s ≤ t' → TransferGapAt hN hβ hs (seedMass w) w := by
  obtain ⟨w, hw, hseed⟩ := segment_seed hN hβ h
  exact ⟨w, hw, fun s hs hst => gap_of_seed hN hβ hs hw (hseed s hs hst).le⟩

/-- **`diag_gap`: the isotropic gap near the origin.** Some `b > 0` (existential, from
`MixPlane.diag_anchor`) gives, at every `0 ≤ β < b` on the diagonal `t = β`, a window `w ≥ 1` with
`TransferGapAt` at rate `log 2 / 2^w`. DERIVED: `0` the lower end; `1` the least window. -/
theorem diag_gap (hN : N ≠ 0) :
    ∃ b > 0, ∀ (β : ℝ) (hβ : 0 ≤ β), β < b →
      ∃ w : ℕ, 1 ≤ w ∧ TransferGapAt hN hβ hβ (seedMass w) w := by
  obtain ⟨b, hb, h⟩ := MixPlane.diag_anchor hN
  exact ⟨b, hb, fun β hβ hlt => gap_on_vanishSet hN hβ hβ (h β hβ hlt)⟩

end MassGap.StripLift

#print axioms MassGap.StripLift.seedMass_pos
#print axioms MassGap.StripLift.stripMass_eq
#print axioms MassGap.StripLift.gap_of_seed
#print axioms MassGap.StripLift.tLift_pos
#print axioms MassGap.StripLift.tGlue_le_tLift
#print axioms MassGap.StripLift.tLift_le
#print axioms MassGap.StripLift.seed_lift_lt
#print axioms MassGap.StripLift.lift_gap
#print axioms MassGap.StripLift.exists_beyond
#print axioms MassGap.StripLift.beyond_gap
#print axioms MassGap.StripLift.gap_on_vanishSet
#print axioms MassGap.StripLift.seed_mono_lt
#print axioms MassGap.StripLift.segment_seed
#print axioms MassGap.StripLift.segment_gap
#print axioms MassGap.StripLift.diag_gap
