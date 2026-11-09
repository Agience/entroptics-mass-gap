import Mathlib
import MassGap.ZoomContract

/-!
# MassGap.GapPersist — convexity in the coupling: the countable kinks of the limiting free energy, and what they see of case (T)

`StallRigid.stall_dichotomy` leaves case (T) for a bounded stall: the window read `Y(w) = (λ₁/λ₀)^{2^w}` comes
frequently within every `δ` of `1`. `StallRigid.biased_stall` shows that Perron–Frobenius does not exclude it, and
`StallRigid.isolated_topological` that it can sit at one coupling alone. This module asks what convexity in `β`
excludes. Declarations are in the namespace `MassGap.GapPersist`.

## 1. Countable kinks of a convex function (proved, generic)

`leftD f x`, `rightD f x` are the one-sided derivatives (`derivWithin` on `Iio x`, `Ioi x`), and `kinks S f` the
points of `interior S` where `leftD < rightD`. For `f` convex on `S`:

* `kinks_countable`: the kink set is countable (a rational in each gap `(leftD x, rightD x)`; the gaps are disjoint
  because `rightD x ≤ slope f x y ≤ leftD y` for `x < y`).
* `hasDerivAt_of_not_kink`: off the kink set, in the interior, `f` has a derivative.
* `kinks_null`: the kink set has Lebesgue measure zero.
* `rightD_tendsto` (Griffiths' lemma): convex `f_n → f` pointwise on `S`, `f` differentiable at an interior `x`, then
  `rightD f_n x → f'(x)`.

## 2. The Wilson free energy is convex in `β` (proved, `SU(N)`, every torus)

* `logIntegralExp_convex`: `β ↦ log ∫ e^{−β S} dμ` is convex on `ℝ` for every finite measure with the integrals
  positive and finite. The proof is pointwise convexity of `exp` after normalizing by `Z(β₁)`, `Z(β₂)`: no Hölder.
* `logZ_wilson_convex`, `logZR_convex`: every `SU(N)` Wilson system, every rectangular torus.
* `freeSite_convex`: the window free energy `f_w(β) = log ZR(2^w)/16^w` is convex on `ℝ`.
* `zoomLimit_convex`: the limit `f_∞ = zoomLimit N` is convex on `[0, ∞)`.
* `zoomLimit_kinks_countable`, `zoomLimit_hasDerivAt`: `f_∞` is differentiable at every `β > 0` outside a countable set.
* `window_slope_tendsto`: at those `β`, the right `β`-derivative of `f_w` converges along the windows to `f_∞'(β)`.

## 3. What a kink sees (proved)

* `not_differentiableAt_of_crossing`: two functions differentiable at `x`, both at most `F` near `x` and equal to it
  at `x`, with different derivatives, make `x` a point where `F` is not differentiable.
* `crossing_mem_kinks`, `zoomLimit_crossings_countable`: the couplings `β > 0` at which two differentiable minorants
  of `f_∞` touch it with different slopes form a countable set. This is the first-order shape: two sector free
  energies crossing, the mean action jumping.

## 4. What a kink does not see (proved models)

* `tangency_flat`: `Z_n = 1 + e^{−n|β−1|}`, the partition function of `StallRigid.isolated_topological`
  (`EffectiveCoupling.twoLevel`), has per-volume limit `0` at every `β`. Its (T) point `β = 1` is a tangency, not a
  crossing: `f_∞ ≡ 0` has no kink (`kinks_const`).
* `degenerate_flat`: `Z_n = M e^{n g}` has limit `g` at every `β`: `M` exact vacua at every coupling, the `A₅`
  shape, with no trace in `f_∞`.
* `limit_blind`: the families `1`, `2` and `1 + e^{−n|β−1|}` have the same limit `0`; the first has no (T) point,
  the second has (T) at every `β`, the third at `β = 1` alone.

So convexity excludes (T) of the crossing kind at all but countably many `β`, and excludes nothing of the tangency or
coincident kinds: a degeneracy that contributes `O(1)` to `log Z` (bounded `D`, `DefectBound.bounded_iff_freeEnergy`)
never reaches `f_∞`, and a kink appears only when the near-degenerate sectors carry different action densities.

## The kinds of (T), and the groups (argued and cited)

Case (T) with `D` bounded is a bounded number of near-degenerate top levels on the step slices. Two kinds:

* (T-cross) The near-degenerate sectors have different action densities on one side of `β`. Then their free
  energies cross at `β` and `β` is a kink of `f_∞` (§3): countably many `β` at most. Example: a first-order bulk
  transition of `U(1)` or `A₅` (argued): one kink each.
* (T-local) The sectors are locally indistinguishable: equal action density on a neighbourhood of `β` (or touching
  from below, §4). No kink. Example: `A₅` at large `β`, where the flat `A₅` connections on the slice `T³` (commuting
  triples up to conjugation, more than one class) are separated by tunnelling of order `e^{−σ L²}`, so
  `(λ₁/λ₀)^L → 1` on a whole interval of `β` with `f_∞` analytic there: phase-wide (T), and `A₅` has trivial centre,
  so it lies in the zero-flux sector. Convexity is silent on it.

`SU(N)` has to exclude (T-local) in the zero-flux sector. The classical vacua of the slice are the flat connections
on `T³`; for `SU(N)` every commuting triple lies in a maximal torus and the moduli space is connected (cited, Borel–
Friedman–Morgan 2002), so no discrete family of classical vacua exists to carry an `A₅`-type degeneracy. `G₂` has
commuting triples outside every maximal torus (cited, Witten 1998, Borel–Friedman–Morgan 2002): its moduli space of
flat connections on `T³` is disconnected, yet `G₂` is expected gapped, so connectedness of the flat moduli is not the
input that excludes (T-local) either; the exclusion has to come from the dynamics at the scale of the windows.
`U(1)`: the Coulomb phase is (M) (`StallRigid.rotor_read`, gap `· L` of order one), not (T), and `f_∞` is smooth there
(argued): consistent with §1–§3.

DERIVED (module-wide): `16 = 2⁴` the copies, `2` the doubling and `ε/2` halves of a tolerance; `0`, `1` the limits,
signs, and `a + b = 1` of convexity. CHOSEN: `β = 1` in `tangency_flat` and `limit_blind` (any coupling, inherited
from `StallRigid.isolated_topological`); `M` free in `degenerate_flat`; `2` in `limit_blind` (any `M ≥ 2`).

## What does not follow

(T) is not excluded at any `β` for `SU(N)`. The link from (T) along the windows at `β` to two sector free energies
minorizing `f_∞` is not proved: the transfer spectrum gives no `β`-differentiable sector partition functions, and a
(T) point with equal action densities (T-local) is not a kink at all (§4). So §3 excludes only (T-cross), and only
after that link. The identification of `rightD f_w` with minus the mean plaquette action per site is not stated here.
Convexity alone allows tangency points of a smooth `f_∞` to fill a Cantor set (argued, a difference of convex
functions with any closed zero set): no countability of (T-local) follows from convexity. The group statements in
the section above are cited or argued, not proved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.GapPersist

open Set Filter Topology MeasureTheory
open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.WilsonReal
  MassGap.RectWilson MassGap.CompactGauge MassGap.ZoomContract

/-! ## 1. Countable kinks of a convex function -/

/-- The left derivative. -/
def leftD (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Iio x) x

/-- The right derivative. -/
def rightD (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Ioi x) x

/-- The kinks of `f` in the interior of `S`: the left derivative strictly below the right one. -/
def kinks (S : Set ℝ) (f : ℝ → ℝ) : Set ℝ := {x | x ∈ interior S ∧ leftD f x < rightD f x}

section Kinks

variable {S : Set ℝ} {f : ℝ → ℝ}

/-- **The kinks of a convex function are countable.** A rational in each gap `(leftD x, rightD x)`; the gaps of
`x < y` are disjoint since `rightD x ≤ slope f x y ≤ leftD y`. -/
theorem kinks_countable (hf : ConvexOn ℝ S f) : (kinks S f).Countable := by
  have hq : ∀ x ∈ kinks S f, ∃ q : ℚ, leftD f x < q ∧ (q : ℝ) < rightD f x :=
    fun x hx => exists_rat_btwn hx.2
  choose! q hq using hq
  refine MapsTo.countable_of_injOn (mapsTo_univ q _) ?_ (Set.countable_univ)
  intro x hx y hy hxy
  have key : ∀ {a b : ℝ}, a ∈ kinks S f → b ∈ kinks S f → a < b → (q a : ℝ) < q b := by
    intro a b ha hb hab
    have h1 : rightD f a ≤ slope f a b :=
      hf.rightDeriv_le_slope_of_mem_interior ha.1 (interior_subset hb.1) hab
    have h2 : slope f a b ≤ leftD f b :=
      hf.slope_le_leftDeriv_of_mem_interior (interior_subset ha.1) hb.1 hab
    linarith [(hq a ha).2, (hq b hb).1]
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (congrArg (fun r : ℚ => (r : ℝ)) hxy) (key hx hy h).ne
  · exact h
  · exact absurd (congrArg (fun r : ℚ => (r : ℝ)) hxy) (key hy hx h).ne'

/-- **Off the kinks a convex function is differentiable**, with derivative its right derivative. -/
theorem hasDerivAt_of_not_kink (hf : ConvexOn ℝ S f) {x : ℝ} (hx : x ∈ interior S)
    (hk : x ∉ kinks S f) : HasDerivAt f (rightD f x) x := by
  have hle : leftD f x ≤ rightD f x := hf.leftDeriv_le_rightDeriv_of_mem_interior hx
  have heq : leftD f x = rightD f x := le_antisymm hle (not_lt.1 fun h => hk ⟨hx, h⟩)
  have hr := hf.hasDerivWithinAt_rightDeriv_of_mem_interior hx
  have hl := hf.hasDerivWithinAt_leftDeriv_of_mem_interior hx
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Iio x)).1 hl
    have e : derivWithin f (Iio x) x = rightD f x := heq
    rwa [e] at h
  · exact (hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Ioi x)).1 hr

/-- **The kinks are Lebesgue-null.** -/
theorem kinks_null (hf : ConvexOn ℝ S f) : volume (kinks S f) = 0 :=
  (kinks_countable hf).measure_zero volume

/-- **Griffiths' lemma.** Convex `f_n → f` pointwise on `S` and `f` differentiable at an interior point `x`: the right
derivatives of `f_n` at `x` converge to `f'(x)`. DERIVED: `2` halves of the tolerance. -/
theorem rightD_tendsto {fn : ℕ → ℝ → ℝ} {x d : ℝ} (hconv : ∀ n, ConvexOn ℝ S (fn n))
    (hlim : ∀ y ∈ S, Tendsto (fun n => fn n y) atTop (𝓝 (f y))) (hx : x ∈ interior S)
    (hd : HasDerivAt f d x) : Tendsto (fun n => rightD (fn n) x) atTop (𝓝 d) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hev : slope f x ⁻¹' Metric.ball d (ε / 2) ∈ 𝓝[≠] x :=
    hd.tendsto_slope (Metric.ball_mem_nhds d (half_pos hε))
  rw [Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨η, hη, hsub⟩ := hev
  set h := min δ η / 2 with hhdef
  have hh : 0 < h := by positivity
  have hhδ : h < δ := by have := min_le_left δ η; linarith
  have hhη : h < η := by have := min_le_right δ η; linarith
  have hSp : x + h ∈ S := interior_subset (hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith))
  have hSm : x - h ∈ S := interior_subset (hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith))
  have hSx : x ∈ S := interior_subset hx
  have up : dist (slope f x (x + h)) d < ε / 2 := by
    have : x + h ∈ Metric.ball x η ∩ {x}ᶜ := ⟨by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith⟩
    exact hsub this
  have lo : dist (slope f x (x - h)) d < ε / 2 := by
    have : x - h ∈ Metric.ball x η ∩ {x}ᶜ := ⟨by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith⟩
    exact hsub this
  have T1 : Tendsto (fun n => slope (fn n) x (x + h)) atTop (𝓝 (slope f x (x + h))) := by
    simp only [slope_def_field]
    exact ((hlim _ hSp).sub (hlim _ hSx)).div_const _
  have T2 : Tendsto (fun n => slope (fn n) (x - h) x) atTop (𝓝 (slope f (x - h) x)) := by
    simp only [slope_def_field]
    exact ((hlim _ hSx).sub (hlim _ hSm)).div_const _
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 T1 (ε / 2) (half_pos hε)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 T2 (ε / 2) (half_pos hε)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have a1 := hN1 n (le_of_max_le_left hn)
  have a2 := hN2 n (le_of_max_le_right hn)
  have r1 : rightD (fn n) x ≤ slope (fn n) x (x + h) :=
    (hconv n).rightDeriv_le_slope_of_mem_interior hx hSp (by linarith)
  have r2 : leftD (fn n) x ≤ rightD (fn n) x := (hconv n).leftDeriv_le_rightDeriv_of_mem_interior hx
  have r3 : slope (fn n) (x - h) x ≤ leftD (fn n) x :=
    (hconv n).slope_le_leftDeriv_of_mem_interior hSm hx (by linarith)
  have ec : slope f (x - h) x = slope f x (x - h) := slope_comm f (x - h) x
  rw [ec] at a2
  rw [Real.dist_eq, abs_lt] at a1 a2 up lo ⊢
  constructor
  · linarith [a2.1, lo.1]
  · linarith [a1.2, up.2]

end Kinks

/-! ## 2. The Wilson free energy is convex in `β` -/

/-- **`log Z` is convex in the coupling.** For a finite measure with `e^{−β S}` integrable and `Z(β) > 0` at every
`β`: normalize by `Z(β₁)`, `Z(β₂)`, use convexity of `exp` pointwise, and integrate: `Z(aβ₁ + bβ₂) ≤ Z(β₁)^a Z(β₂)^b`.
DERIVED: `1 = a + b`. -/
theorem logIntegralExp_convex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Ω → ℝ)
    (hint : ∀ β : ℝ, Integrable (fun ω => Real.exp (-β * S ω)) μ)
    (hpos : ∀ β : ℝ, 0 < ∫ ω, Real.exp (-β * S ω) ∂μ) :
    ConvexOn ℝ univ (fun β => Real.log (∫ ω, Real.exp (-β * S ω) ∂μ)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hZx := hpos x
  have hZy := hpos y
  have hZ := hpos (a * x + b * y)
  set Zx := ∫ ω, Real.exp (-x * S ω) ∂μ with hZxd
  set Zy := ∫ ω, Real.exp (-y * S ω) ∂μ with hZyd
  set c := a * Real.log Zx + b * Real.log Zy with hc
  have hpt : ∀ ω, Real.exp (-(a * x + b * y) * S ω) * Real.exp (-c)
      ≤ a * (Real.exp (-x * S ω) / Zx) + b * (Real.exp (-y * S ω) / Zy) := by
    intro ω
    have h1 : Real.exp (-(a * x + b * y) * S ω) * Real.exp (-c)
        = Real.exp (a * (-x * S ω - Real.log Zx) + b * (-y * S ω - Real.log Zy)) := by
      rw [← Real.exp_add, hc]; congr 1; ring
    have h2 : Real.exp (-x * S ω) / Zx = Real.exp (-x * S ω - Real.log Zx) := by
      rw [Real.exp_sub, Real.exp_log hZx]
    have h3 : Real.exp (-y * S ω) / Zy = Real.exp (-y * S ω - Real.log Zy) := by
      rw [Real.exp_sub, Real.exp_log hZy]
    rw [h1, h2, h3]
    have := convexOn_exp.2 (mem_univ (-x * S ω - Real.log Zx)) (mem_univ (-y * S ω - Real.log Zy))
      ha hb hab
    simp only [smul_eq_mul] at this
    exact this
  have hle : (∫ ω, Real.exp (-(a * x + b * y) * S ω) * Real.exp (-c) ∂μ)
      ≤ ∫ ω, (a * (Real.exp (-x * S ω) / Zx) + b * (Real.exp (-y * S ω) / Zy)) ∂μ :=
    integral_mono ((hint _).mul_const _)
    ((((hint x).div_const Zx).const_mul a).add (((hint y).div_const Zy).const_mul b)) hpt
  rw [integral_mul_const, integral_add (((hint x).div_const Zx).const_mul a)
    (((hint y).div_const Zy).const_mul b), integral_const_mul, integral_const_mul, integral_div,
    integral_div, ← hZxd, ← hZyd, div_self hZx.ne', div_self hZy.ne', mul_one, mul_one, hab] at hle
  have hle' : (∫ ω, Real.exp (-(a * x + b * y) * S ω) ∂μ) ≤ Real.exp c := by
    have e : (∫ ω, Real.exp (-(a * x + b * y) * S ω) ∂μ)
        = (∫ ω, Real.exp (-(a * x + b * y) * S ω) ∂μ) * Real.exp (-c) * Real.exp c := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [e]
    calc (∫ ω, Real.exp (-(a * x + b * y) * S ω) ∂μ) * Real.exp (-c) * Real.exp c
        ≤ 1 * Real.exp c := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = Real.exp c := one_mul _
  exact (Real.log_le_iff_le_exp hZ).2 hle'

variable {N : ℕ}

/-- **Every `SU(N)` Wilson system has `log Z` convex in `β`.** -/
theorem logZ_wilson_convex (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) :
    ConvexOn ℝ univ (fun β => Real.log ((wilsonSystem bd (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) β)) := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  show ConvexOn ℝ univ (fun β => Real.log (∫ U, Real.exp (-β *
    (wilsonSystem bd (wilsonDensity (N := N))).action U)
      ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))))
  refine logIntegralExp_convex _ _ (fun β => ?_) (fun β => wilsonSystem_partition_pos hN bd β)
  refine (integrable_const (Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))))).mono'
    (measurable_wilsonSystem_boltz bd β).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  have h0 := wilsonSystem_action_nonneg hN bd U
  have h2 := wilsonSystem_action_le hN bd U
  have h3 := mul_le_mul_of_nonneg_right (neg_le_abs β) h0
  have h4 := mul_le_mul_of_nonneg_left h2 (abs_nonneg β)
  linarith

/-- **The rectangular torus.** -/
theorem logZR_convex (hN : N ≠ 0) (L : Fin 4 → ℕ) :
    ConvexOn ℝ univ (fun β => Real.log (ZR L N β)) :=
  logZ_wilson_convex hN (rbd L)

/-- **The window free energy is convex in `β`.** DERIVED: `16 = 2⁴`. -/
theorem freeSite_convex (hN : N ≠ 0) (w : ℕ) : ConvexOn ℝ univ (fun β => freeSite N β w) := by
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab => ?_⟩
  have h := (logZR_convex hN (fun _ => 2 ^ w)).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  simp only [freeSite]
  have h16 : (0 : ℝ) < 16 ^ w := by positivity
  have e : ∀ p q : ℝ, a * (p / 16 ^ w) + b * (q / 16 ^ w) = (a * p + b * q) / 16 ^ w := by
    intro p q; ring
  rw [e]
  exact div_le_div_of_nonneg_right h h16.le

/-- **The limiting free energy is convex on `[0, ∞)`**: a pointwise limit of convex functions. -/
theorem zoomLimit_convex (hN : N ≠ 0) : ConvexOn ℝ (Ici 0) (zoomLimit N) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : (0 : ℝ) ≤ x := hx
  have hy' : (0 : ℝ) ≤ y := hy
  have hz : (0 : ℝ) ≤ a • x + b • y := by
    simp only [smul_eq_mul]; exact add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy')
  have t1 := tendsto_freeSite hN hz
  have t2 := ((tendsto_freeSite hN hx').const_smul a).add ((tendsto_freeSite hN hy').const_smul b)
  exact le_of_tendsto_of_tendsto' t1 t2
    (fun w => (freeSite_convex hN w).2 (mem_univ x) (mem_univ y) ha hb hab)

/-- **The limiting free energy has countably many kinks in `β > 0`.** -/
theorem zoomLimit_kinks_countable (hN : N ≠ 0) : (kinks (Ici 0) (zoomLimit N)).Countable :=
  kinks_countable (zoomLimit_convex hN)

/-- **Off the kinks the limiting free energy is differentiable at every `β > 0`.** -/
theorem zoomLimit_hasDerivAt (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (hk : β ∉ kinks (Ici 0) (zoomLimit N)) :
    HasDerivAt (zoomLimit N) (rightD (zoomLimit N) β) β := by
  have hint : β ∈ interior (Ici (0 : ℝ)) := by rw [interior_Ici]; exact hβ
  exact hasDerivAt_of_not_kink (zoomLimit_convex hN) hint hk

/-- **Off the kinks the window slopes converge.** At every `β > 0` outside the countable kink set, the right
`β`-derivative of the window free energy `f_w` converges along the windows to `f_∞'(β)`. -/
theorem window_slope_tendsto (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hk : β ∉ kinks (Ici 0) (zoomLimit N)) :
    Tendsto (fun w => rightD (fun b => freeSite N b w) β) atTop (𝓝 (rightD (zoomLimit N) β)) := by
  have hint : β ∈ interior (Ici (0 : ℝ)) := by rw [interior_Ici]; exact hβ
  exact rightD_tendsto (fn := fun w b => freeSite N b w)
    (fun w => (freeSite_convex hN w).subset (subset_univ _) (convex_Ici 0))
    (fun y hy => tendsto_freeSite hN hy) hint (zoomLimit_hasDerivAt hN hβ hk)

/-! ## 3. What a kink sees: crossing sectors -/

/-- **A transverse crossing is a kink.** `g`, `h` differentiable at `x`, both at most `F` near `x` and equal to `F`
at `x`, with different derivatives: `F` is not differentiable at `x`. -/
theorem not_differentiableAt_of_crossing {F g h : ℝ → ℝ} {x g' h' : ℝ}
    (hg : ∀ᶠ y in 𝓝 x, g y ≤ F y) (hh : ∀ᶠ y in 𝓝 x, h y ≤ F y) (hgx : g x = F x) (hhx : h x = F x)
    (hg' : HasDerivAt g g' x) (hh' : HasDerivAt h h' x) (hne : g' ≠ h') :
    ¬ DifferentiableAt ℝ F x := by
  intro hF
  have e1 : deriv F x = g' := by
    have hmin : IsLocalMin (fun y => F y - g y) x := hg.mono fun y hy => by
      show F x - g x ≤ F y - g y
      linarith
    have := hmin.hasDerivAt_eq_zero (hF.hasDerivAt.sub hg')
    linarith
  have e2 : deriv F x = h' := by
    have hmin : IsLocalMin (fun y => F y - h y) x := hh.mono fun y hy => by
      show F x - h x ≤ F y - h y
      linarith
    have := hmin.hasDerivAt_eq_zero (hF.hasDerivAt.sub hh')
    linarith
  exact hne (e1.symm.trans e2)

/-- **A crossing of a convex function lies in its kink set.** -/
theorem crossing_mem_kinks {S : Set ℝ} {F g h : ℝ → ℝ} {x g' h' : ℝ} (hF : ConvexOn ℝ S F)
    (hx : x ∈ interior S) (hg : ∀ᶠ y in 𝓝 x, g y ≤ F y) (hh : ∀ᶠ y in 𝓝 x, h y ≤ F y)
    (hgx : g x = F x) (hhx : h x = F x) (hg' : HasDerivAt g g' x) (hh' : HasDerivAt h h' x)
    (hne : g' ≠ h') : x ∈ kinks S F := by
  by_contra hk
  exact not_differentiableAt_of_crossing hg hh hgx hhx hg' hh' hne
    (hasDerivAt_of_not_kink hF hx hk).differentiableAt

/-- The couplings `β > 0` at which two differentiable minorants of `f_∞` touch it with different slopes. -/
def Crossings (N : ℕ) : Set ℝ :=
  {β | 0 < β ∧ ∃ g h : ℝ → ℝ, ∃ g' h' : ℝ, (∀ᶠ y in 𝓝 β, g y ≤ zoomLimit N y) ∧
    (∀ᶠ y in 𝓝 β, h y ≤ zoomLimit N y) ∧ g β = zoomLimit N β ∧ h β = zoomLimit N β ∧
    HasDerivAt g g' β ∧ HasDerivAt h h' β ∧ g' ≠ h'}

/-- **Crossing sectors occur at countably many couplings.** -/
theorem zoomLimit_crossings_countable (hN : N ≠ 0) : (Crossings N).Countable := by
  refine (zoomLimit_kinks_countable hN).mono ?_
  rintro β ⟨hβ, g, h, g', h', hg, hh, hgx, hhx, hg', hh', hne⟩
  have hint : β ∈ interior (Ici (0 : ℝ)) := by rw [interior_Ici]; exact hβ
  exact crossing_mem_kinks (zoomLimit_convex hN) hint hg hh hgx hhx hg' hh' hne

/-! ## 4. What a kink does not see -/

/-- **A constant has no kinks.** -/
theorem kinks_const (S : Set ℝ) (c : ℝ) : kinks S (fun _ => c) = ∅ := by
  ext x
  simp [kinks, leftD, rightD]

/-- **The tangency of `isolated_topological` is flat.** `log(1 + e^{−n|β−1|})/n → 0` at every `β`, `β = 1`
included. CHOSEN: `β = 1` the coupling of the tangency. -/
theorem tangency_flat (β : ℝ) :
    Tendsto (fun n : ℕ => Real.log (1 + Real.exp (-|β - 1|) ^ n) / n) atTop (𝓝 0) := by
  have hr0 : 0 ≤ Real.exp (-|β - 1|) := (Real.exp_pos _).le
  have hr1 : Real.exp (-|β - 1|) ≤ 1 := Real.exp_le_one_iff.mpr (by simp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)) (fun n => ?_) (fun n => ?_)
  · have hp : 0 ≤ Real.exp (-|β - 1|) ^ n := pow_nonneg hr0 n
    exact div_nonneg (Real.log_nonneg (by linarith)) (Nat.cast_nonneg n)
  · have hp : 0 ≤ Real.exp (-|β - 1|) ^ n := pow_nonneg hr0 n
    have hp1 : Real.exp (-|β - 1|) ^ n ≤ 1 := pow_le_one₀ hr0 hr1
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith) (by linarith)) (Nat.cast_nonneg n)

/-- **The tangency has `(λ₁/λ₀)^n = 1` at `β = 1` at every volume.** -/
theorem tangency_degenerate (n : ℕ) : Real.exp (-|(1 : ℝ) - 1|) ^ n = 1 := by simp

/-- **Exact degeneracy at every coupling is flat.** `log(M e^{n g(β)})/n → g(β)`: `M` vacua leave no trace in `f_∞`. -/
theorem degenerate_flat {M : ℝ} (hM : 0 < M) (g : ℝ → ℝ) (β : ℝ) :
    Tendsto (fun n : ℕ => Real.log (M * Real.exp (n * g β)) / n) atTop (𝓝 (g β)) := by
  have e : ∀ n : ℕ, 0 < n →
      Real.log (M * Real.exp (n * g β)) / n = Real.log M / n + g β := by
    intro n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
  have t : Tendsto (fun n : ℕ => Real.log M / n + g β) atTop (𝓝 (0 + g β)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log M)).add tendsto_const_nhds
  rw [zero_add] at t
  refine t.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (e n hn).symm

/-- **The limit free energy is blind to (T).** `Z_n = 1` (no degeneracy), `Z_n = 2` (exact degeneracy at every `β`)
and `Z_n = 1 + e^{−n|β−1|}` (degeneracy at `β = 1` alone) have the same per-volume limit `0` at every `β`, and the
limit has no kinks. CHOSEN: `2` any `M ≥ 2`; `β = 1` the tangency. -/
theorem limit_blind (β : ℝ) :
    Tendsto (fun n : ℕ => Real.log 1 / n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => Real.log 2 / n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => Real.log (1 + Real.exp (-|β - 1|) ^ n) / n) atTop (𝓝 0) ∧
    kinks univ (fun _ => (0 : ℝ)) = ∅ :=
  ⟨tendsto_const_div_atTop_nhds_zero_nat _, tendsto_const_div_atTop_nhds_zero_nat _, tangency_flat β,
    kinks_const _ _⟩

end MassGap.GapPersist

#print axioms MassGap.GapPersist.kinks_countable
#print axioms MassGap.GapPersist.hasDerivAt_of_not_kink
#print axioms MassGap.GapPersist.kinks_null
#print axioms MassGap.GapPersist.rightD_tendsto
#print axioms MassGap.GapPersist.logIntegralExp_convex
#print axioms MassGap.GapPersist.logZ_wilson_convex
#print axioms MassGap.GapPersist.logZR_convex
#print axioms MassGap.GapPersist.freeSite_convex
#print axioms MassGap.GapPersist.zoomLimit_convex
#print axioms MassGap.GapPersist.zoomLimit_kinks_countable
#print axioms MassGap.GapPersist.zoomLimit_hasDerivAt
#print axioms MassGap.GapPersist.window_slope_tendsto
#print axioms MassGap.GapPersist.not_differentiableAt_of_crossing
#print axioms MassGap.GapPersist.crossing_mem_kinks
#print axioms MassGap.GapPersist.zoomLimit_crossings_countable
#print axioms MassGap.GapPersist.kinks_const
#print axioms MassGap.GapPersist.tangency_flat
#print axioms MassGap.GapPersist.tangency_degenerate
#print axioms MassGap.GapPersist.degenerate_flat
#print axioms MassGap.GapPersist.limit_blind
