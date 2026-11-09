import Mathlib
import MassGap.MixPlane
import MassGap.WindowRead

/-!
# MassGap.MixCut — the mixed cut energy and the first stall on the segment

The bridge is `CouplingTower.StrongEnd N`, placed in the coupling quadrant `(β, β_⊥)` by `MixPlane`. On the
vertical segment above `β`, write `D(t, w) = AnisoTorus.DA N β t w` and `n = 2^w`. This module computes the
`β_⊥`-derivative of `D`, evaluates it at the decoupled end, and reduces `MixPlane.NoStallOnSegment N β` to one
one-sided, window-uniform bound on that derivative. Declarations are in `MassGap.MixCut`.

## 1. The mixed cut energy (proved)

* `sinR`, `smixR`: the in-plane and mixed actions on the rectangular configuration space of side `n`
  (`sin_eq`, `smix_eq`: they are `AnisoTorus.Sin`, `AnisoTorus.Smix`); `ZA_eq_int`: `ZA` as an integral of them.
* `meanMix N β β_⊥ n = ⟨S_mix⟩_n`, the Gibbs mean of the mixed action at side `n`, and the mixed cut energy
  `mixCut N β β_⊥ w = ⟨S_mix⟩_{2n} − 16 ⟨S_mix⟩_n`.
* `hasDerivAt_ZA`, `hasDerivAt_logZA`: `∂_{β_⊥} log ZA(n) = −⟨S_mix⟩_n`, by differentiation under the integral of a
  continuous integrand on a compact configuration space (`hasDerivAt_integral_exp_lin`).
* `hasDerivAt_DA_mix`: `∂_{β_⊥} D(β_⊥, w) = mixCut N β β_⊥ w`, at every `β`, `β_⊥`, `w`, with no hypothesis on `N`.

## 2. The decoupled end (proved)

`mixCut_zero`: `mixCut N β 0 w = 0` for every `β` and every window `w ≥ 1`. At `β_⊥ = 0` the weight reads only
`S_in`. A gauge rotation by `a` at one site `x`, applied to the links of directions `0` and `1` only (`gT`,
`siteG`), conjugates every in-plane holonomy and leaves every `(2,3)` holonomy alone, so `S_in` is invariant
(`sinR_gT`). It translates the holonomy of a mixed plaquette based at `x`: `a · hol` when the first direction is in
`{0, 1}` (`hol_gT_mixA`), `hol · a⁻¹` otherwise (`hol_gT_mixB`). It preserves product Haar (`gT_measurePreserving`).
Averaging over `a` (`integral_haar_avg`) gives `∫ φ(hol_q) e^{−β S_in} = ⟨φ⟩_Haar ∫ e^{−β S_in}` for every mixed
plaquette (`integral_plaq_mul_exp`), so `⟨S_mix⟩_n(β, 0) = 8 n⁴ ⟨φ⟩_Haar` (`meanMix_zero`), extensive, and the
cut energy cancels as the volume count does: `8 (2n)⁴ − 16 · 8 n⁴ = 0`. Extent `≥ 2` is what makes the shifted
sites distinct; it is `2^w ≥ 2` at `w ≥ 1`.

## 3. The bound and the stall (proved reduction, named input)

`MixCutBound N β`: some `M` with `mixCut N β t w ≤ M` at every window `w ≥ 1` and every `t ∈ [0, β]`. One-sided,
`M` existential and `β`-dependent.

* `vanish_of_cut_le`: if the segment vanishes on `[s, t*)` and the cut energy is at most `M` on `(s, t*)` at every
  window, then `(β, t*)` vanishes. Pick `s' ∈ [s, t*)` with `M (t* − s') < 1/2000`, a window `w` with
  `D(s', w) < 1/2000` (vanishing at `s'`), and the mean value theorem: `D(t*, w) ≤ D(s', w) + M (t* − s') <
  1/1000`, a seed (`MixPlane.mem_vanishSet_iff_seed_lt`).
* `noStallOnSegment_of_mixCutBound`: `TwoDCharacter N β ∧ MixCutBound N β ⇒ NoStallOnSegment N β`, through
  `MixPlane.segment_first_stall`. `strongEnd_of_mixCutBound`: frequently in `β`, the pair gives `StrongEnd N`.
* `first_stall_mixCut_unbounded`: at a first stall `t*` (stalled at `t*`, vanishing on `[0, t*)`), for every
  `s ∈ [0, t*)` and every `M` some window `w ≥ 1` and some `τ ∈ (s, t*)` have `M < mixCut N β τ w`.
  `segment_stall_mixCut_unbounded`: the same from `¬ NoStallOnSegment N β` and the cited `TwoDCharacter N β`.

## What `MixCutBound` is (argued, not proved)

`MixCutBound N β` is a window-uniform finite-size energy estimate. `mixCut = 8 (2n)⁴ e(2n) − 16 · 8 n⁴ e(n) =
8 (2n)⁴ (e(2n) − e(n))`, with `e(L)` the mean mixed plaquette action at side `L`: the volume times the difference of
mixed energy densities at sides `2n` and `n`. It is bounded when the finite-size corrections to the mixed energy
density fall at least like the inverse volume, as in a massive phase where they are exponentially small in `n`.
Any first stall violates it (`first_stall_mixCut_unbounded`); so for `U(1)`, where the segment is argued to stall
(Coulomb phase at large `β`; Guth 1980, Fröhlich–Spencer 1982), it fails. It is not proved for `SU(N)` at any `β`
beyond the anchors' neighbourhoods, and it carries the non-abelian content.

DERIVED (module-wide): `16 = 2⁴` the copies; `2` the doubling and the least extent with two sites; `8` the mixed
ordered orientations (`4 · 4 − 8` in-plane ones, of which `4` diagonal); `4` the dimension; `0` the decoupled end,
the lower ends and the signs; `1` the least window and the unit ball of the differentiation; `1/2000 = (1/1000)/2`
the half seed split between the window read and the mean-value increment. Inherited: `1/1000` the seed of
`DoublingSharp` (through `MixPlane`). Cited: `LayerSplit.TwoDCharacter N β`.

## What does not follow

`MixCutBound N β` is not proved at any `β > 0`; nothing here bounds `mixCut` away from `β_⊥ = 0`. The reduction
`noStallOnSegment_of_mixCutBound` replaces `NoStallOnSegment N β` by a stronger-looking but real-variable input; it
does not discharge it, and `strongEnd_of_mixCutBound` discharges no hypothesis of the bridge. `mixCut_zero` holds
at one point of the segment and gives no bound at any `t > 0`. No statement here reads the non-abelian structure of
`SU(N)`: every proof is argued to go through verbatim for any compact gauge group with the tree's density (not checked), which is why the
open content sits in `MixCutBound`. `LayerSplit.TwoDCharacter N β` stays a cited input.
-/

namespace MassGap.MixCut

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.RectWilson
open MassGap.CouplingTower (StrongEnd)

variable {N : ℕ}

/-! ## 1. Differentiation under the integral -/

/-- **`x ↦ ∫ e^{−(A + x B)}` is differentiable** with derivative `−∫ B e^{−(A + t B)}`, for continuous `A`, `B` on
a compact space and a finite measure. DERIVED: `1` the radius of the dominating ball. -/
theorem hasDerivAt_integral_exp_lin {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {A B : X → ℝ} (hA : Continuous A)
    (hB : Continuous B) (t : ℝ) :
    HasDerivAt (fun x => ∫ U, Real.exp (-(A U + x * B U)) ∂μ)
      (-∫ U, B U * Real.exp (-(A U + t * B U)) ∂μ) t := by
  obtain ⟨CA, hCA⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨CB, hCB⟩ := isCompact_univ.exists_bound_of_continuousOn hB.continuousOn
  have hA' : ∀ U, |A U| ≤ CA := fun U => by simpa [Real.norm_eq_abs] using hCA U (mem_univ U)
  have hB' : ∀ U, |B U| ≤ max CB 0 := fun U =>
    (by simpa [Real.norm_eq_abs] using hCB U (mem_univ U) : |B U| ≤ CB).trans (le_max_left _ _)
  have hC0 : 0 ≤ max CB 0 := le_max_right _ _
  have hF : ∀ x : ℝ, Continuous fun U => Real.exp (-(A U + x * B U)) := fun x =>
    Real.continuous_exp.comp (hA.add (continuous_const.mul hB)).neg
  have hexp : ∀ (x : ℝ) (U : X), Real.exp (-(A U + x * B U)) ≤ Real.exp (CA + |x| * max CB 0) := by
    intro x U
    refine Real.exp_le_exp.mpr ?_
    have h1 : |x * B U| ≤ |x| * max CB 0 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB' U) (abs_nonneg x)
    linarith [neg_abs_le (A U), neg_abs_le (x * B U), hA' U]
  have hint : Integrable (fun U => Real.exp (-(A U + t * B U))) μ :=
    (integrable_const (Real.exp (CA + |t| * max CB 0))).mono' (hF t).aestronglyMeasurable
      (Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp t U)
  have hbd : ∀ᵐ U ∂μ, ∀ x ∈ Metric.ball t 1,
      ‖-B U * Real.exp (-(A U + x * B U))‖ ≤ max CB 0 * Real.exp (CA + (|t| + 1) * max CB 0) := by
    refine Eventually.of_forall fun U x hx => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hx' : |x| ≤ |t| + 1 := by linarith [abs_sub_abs_le_abs_sub x t]
    have he : Real.exp (-(A U + x * B U)) ≤ Real.exp (CA + (|t| + 1) * max CB 0) :=
      (hexp x U).trans (Real.exp_le_exp.mpr (by nlinarith))
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hB' U) he (Real.exp_pos _).le hC0
  have hdiff : ∀ᵐ U ∂μ, ∀ x ∈ Metric.ball t 1,
      HasDerivAt (fun y => Real.exp (-(A U + y * B U))) (-B U * Real.exp (-(A U + x * B U))) x := by
    refine Eventually.of_forall fun U x _ => ?_
    have h := (((hasDerivAt_id' x).mul_const (B U)).const_add (A U)).neg.exp
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (x : ℝ) U => Real.exp (-(A U + x * B U)))
    (F' := fun (x : ℝ) U => -B U * Real.exp (-(A U + x * B U)))
    (x₀ := t) (bound := fun _ => max CB 0 * Real.exp (CA + (|t| + 1) * max CB 0))
    (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun x => (hF x).aestronglyMeasurable) hint
    ((hB.neg.mul (hF t)).aestronglyMeasurable) hbd (integrable_const _) hdiff
  refine key.2.congr_deriv ?_
  simp only [neg_mul, integral_neg]

/-! ## 2. The in-plane and mixed actions on the rectangular configuration space -/

/-- Links of the side-`n` torus. No numeral. -/
abbrev Lk (n : ℕ) : Type := RLink (fun _ : Fin 4 => n)

/-- Plaquettes of the side-`n` torus. No numeral. -/
abbrev Pq (n : ℕ) : Type := RPlaq (fun _ : Fin 4 => n)

/-- Product Haar on the side-`n` configuration space. No numeral. -/
noncomputable abbrev piH (N n : ℕ) : Measure (Lk n → SUN.SU N) :=
  Measure.pi fun _ : Lk n => probHaar (SUN.SU N)

/-- The density of one plaquette. No numeral. -/
noncomputable def plaq (N n : ℕ) (q : Pq n) (U : Lk n → SUN.SU N) : ℝ :=
  WilsonAction.wilsonDensity ((sysR (fun _ => n) N).hol q U)

/-- The in-plane action. DERIVED: `0` the excluded terms. -/
noncomputable def sinR (N n : ℕ) (U : Lk n → SUN.SU N) : ℝ :=
  ∑ q : Pq n, if AnisoTorus.inPlane q.1 then plaq N n q U else 0

/-- The mixed action. DERIVED: `0` the excluded terms. -/
noncomputable def smixR (N n : ℕ) (U : Lk n → SUN.SU N) : ℝ :=
  ∑ q : Pq n, if AnisoTorus.inPlane q.1 then 0 else plaq N n q U

theorem sin_eq (n : ℕ) (U : Lk n → SUN.SU N) : AnisoTorus.Sin N n U = sinR N n U := by
  unfold AnisoTorus.Sin sinR
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, j⟩, x⟩ := q
  rfl

theorem smix_eq (n : ℕ) (U : Lk n → SUN.SU N) : AnisoTorus.Smix N n U = smixR N n U := by
  unfold AnisoTorus.Smix smixR
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, j⟩, x⟩ := q
  rfl

/-- **`ZA` as an integral of the two actions.** No numeral. -/
theorem ZA_eq_int (β βp : ℝ) (n : ℕ) :
    AnisoTorus.ZA N β βp n = ∫ U, Real.exp (-(β * sinR N n U + βp * smixR N n U)) ∂piH N n := by
  unfold AnisoTorus.ZA
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show Real.exp (-(β * AnisoTorus.Sin N n U + βp * AnisoTorus.Smix N n U)) = _
  rw [sin_eq, smix_eq]

theorem ZA_pos (β βp : ℝ) (n : ℕ) : 0 < AnisoTorus.ZA N β βp n := by
  rw [MixAnchor.ZA_eq]; exact MixAnchor.ZC_pos N _ _

theorem continuous_plaq (n : ℕ) (q : Pq n) : Continuous (plaq N n q) :=
  WilsonAction.continuous_wilsonDensity.comp (MixAnchor.continuous_hol q)

theorem continuous_sinR (n : ℕ) : Continuous (sinR N n) := by
  unfold sinR
  exact continuous_finsetSum _ fun q _ =>
    continuous_if_const _ (fun _ => continuous_plaq n q) (fun _ => continuous_const)

theorem continuous_smixR (n : ℕ) : Continuous (smixR N n) := by
  unfold smixR
  exact continuous_finsetSum _ fun q _ =>
    continuous_if_const _ (fun _ => continuous_const) (fun _ => continuous_plaq n q)

/-! ## 3. The mixed mean and the mixed cut energy -/

/-- The unnormalized mixed mean `∫ S_mix e^{−(β S_in + β_⊥ S_mix)}`. No numeral. -/
noncomputable def mixNum (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ :=
  ∫ U, smixR N n U * Real.exp (-(β * sinR N n U + βp * smixR N n U)) ∂piH N n

/-- **The mixed mean** `⟨S_mix⟩_n` at `(β, β_⊥)`. No numeral. -/
noncomputable def meanMix (N : ℕ) (β βp : ℝ) (n : ℕ) : ℝ := mixNum N β βp n / AnisoTorus.ZA N β βp n

/-- **The mixed cut energy** `C(β, β_⊥, w) = ⟨S_mix⟩_{2n} − 16 ⟨S_mix⟩_n`, `n = 2^w`. DERIVED: `16 = 2⁴` the
copies; `2` the doubling; `1` the next window. -/
noncomputable def mixCut (N : ℕ) (β βp : ℝ) (w : ℕ) : ℝ :=
  meanMix N β βp (2 ^ (w + 1)) - 16 * meanMix N β βp (2 ^ w)

/-- `∂_{β_⊥} ZA = −∫ S_mix e^{−(β S_in + β_⊥ S_mix)}`. No numeral. -/
theorem hasDerivAt_ZA (β t : ℝ) (n : ℕ) :
    HasDerivAt (fun x => AnisoTorus.ZA N β x n) (-mixNum N β t n) t := by
  have e : (fun x => AnisoTorus.ZA N β x n)
      = fun x => ∫ U, Real.exp (-(β * sinR N n U + x * smixR N n U)) ∂piH N n :=
    funext fun x => ZA_eq_int β x n
  rw [e]
  exact hasDerivAt_integral_exp_lin (piH N n) (A := fun U => β * sinR N n U)
    (continuous_const.mul (continuous_sinR n)) (continuous_smixR n) t

/-- **`∂_{β_⊥} log ZA(n) = −⟨S_mix⟩_n`.** No numeral. -/
theorem hasDerivAt_logZA (β t : ℝ) (n : ℕ) :
    HasDerivAt (fun x => AnisoTorus.logZA N β x n) (-meanMix N β t n) t := by
  have h := (hasDerivAt_ZA (N := N) β t n).log (ZA_pos β t n).ne'
  refine h.congr_deriv ?_
  unfold meanMix
  rw [neg_div]

/-- **The `β_⊥`-derivative of the anisotropic window defect is the mixed cut energy**:
`∂_{β_⊥} DA N β β_⊥ w = ⟨S_mix⟩_{2n} − 16 ⟨S_mix⟩_n`, at every `β`, `β_⊥`, `w`. DERIVED: `16 = 2⁴` the copies;
`2` the doubling; `1` the next window. -/
theorem hasDerivAt_DA_mix (β t : ℝ) (w : ℕ) :
    HasDerivAt (fun x => AnisoTorus.DA N β x w) (mixCut N β t w) t := by
  have h1 := hasDerivAt_logZA (N := N) β t (2 ^ w)
  have h2 := hasDerivAt_logZA (N := N) β t (2 ^ (w + 1))
  have e : (fun x => AnisoTorus.DA N β x w)
      = fun x => 16 * AnisoTorus.logZA N β x (2 ^ w) - AnisoTorus.logZA N β x (2 ^ (w + 1)) :=
    funext fun x => rfl
  rw [e]
  exact ((h1.const_mul 16).sub h2).congr_deriv (by unfold mixCut; ring)

/-! ## 4. The layer gauge rotation -/

section Gauge

variable (L : Fin 4 → ℕ)

/-- Two steps in different orders reach the same site. No numeral. -/
theorem rshift_comm (i j : Fin 4) (x : RSite L) :
    rshift L i (rshift L j x) = rshift L j (rshift L i x) := by
  by_cases hij : i = j
  · subst hij; rfl
  · funext k
    by_cases hki : k = i
    · subst hki
      simp only [rshift, Function.update_self, Function.update_of_ne hij]
    · by_cases hkj : k = j
      · subst hkj
        simp only [rshift, Function.update_self, Function.update_of_ne (Ne.symm hij)]
      · simp only [rshift, Function.update_of_ne hki, Function.update_of_ne hkj]

/-- Two steps in different directions move every site, along an extent `≥ 2`. DERIVED: `2` the least extent with
two sites. -/
theorem rshift2_ne {i j : Fin 4} (hij : i ≠ j) (hL : 2 ≤ L i) (x : RSite L) :
    rshift L i (rshift L j x) ≠ x := by
  intro h
  have h1 := congrFun h i
  simp only [rshift, Function.update_self, Function.update_of_ne hij] at h1
  exact WindowRead.finRotate_ne hL (x i) h1

/-- **The gauge rotation of the links of directions `0` and `1`** by a site function `h`:
`U(l) ↦ h(x) U(l) h(x + l)⁻¹` on those links, the identity on the links of directions `2` and `3`.
DERIVED: `2` the size of each plane's direction block; `0` the first block. -/
noncomputable def gT (h : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) : RLink L → SUN.SU N :=
  fun l => if l.1.val / 2 = 0 then h l.2 * U l * (h (rshift L l.1 l.2))⁻¹ else U l

/-- The site function equal to `a` at `x` and to `1` elsewhere. DERIVED: `1` the identity. -/
noncomputable def siteG (x : RSite L) (a : SUN.SU N) (y : RSite L) : SUN.SU N := if y = x then a else 1

/-- **A `(0,1)` holonomy is conjugated.** DERIVED: `2`, `0` as in `gT`. -/
theorem hol_gT_low (h : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) {i j : Fin 4} (hi : i.val / 2 = 0)
    (hj : j.val / 2 = 0) (x : RSite L) :
    (sysR L N).hol ((i, j), x) (gT L h U) = h x * (sysR L N).hol ((i, j), x) U * (h x)⁻¹ := by
  rw [hol_eq, hol_eq]
  simp only [gT, if_pos hi, if_pos hj]
  rw [rshift_comm L j i x]
  group

/-- **A `(2,3)` holonomy is unchanged.** DERIVED: `2`, `0` as in `gT`. -/
theorem hol_gT_high (h : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) {i j : Fin 4} (hi : ¬ i.val / 2 = 0)
    (hj : ¬ j.val / 2 = 0) (x : RSite L) :
    (sysR L N).hol ((i, j), x) (gT L h U) = (sysR L N).hol ((i, j), x) U := by
  rw [hol_eq, hol_eq]
  simp only [gT, if_neg hi, if_neg hj]

/-- **A mixed holonomy with first direction in `{0, 1}` is left-translated** by the site rotation at its base.
DERIVED: `2` the least extent; `2`, `0` as in `gT`. -/
theorem hol_gT_mixA (hL : ∀ k, 2 ≤ L k) (a : SUN.SU N) (U : RLink L → SUN.SU N) {i j : Fin 4}
    (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (x : RSite L) :
    (sysR L N).hol ((i, j), x) (gT L (siteG L x a) U) = a * (sysR L N).hol ((i, j), x) U := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have h1 : rshift L i x ≠ x := WindowRead.rshift_ne L (hL i) x
  have h3 : rshift L i (rshift L j x) ≠ x := rshift2_ne L hij (hL i) x
  have h2 : rshift L j x ≠ x := WindowRead.rshift_ne L (hL j) x
  rw [hol_eq, hol_eq]
  simp only [gT, siteG, if_pos hi, if_neg hj, if_neg h1, if_neg h2, if_neg h3, ↓reduceIte, inv_one,
    mul_one, one_mul]
  group

/-- **A mixed holonomy with first direction in `{2, 3}` is right-translated** by the inverse site rotation.
DERIVED: `2` the least extent; `2`, `0` as in `gT`. -/
theorem hol_gT_mixB (hL : ∀ k, 2 ≤ L k) (a : SUN.SU N) (U : RLink L → SUN.SU N) {i j : Fin 4}
    (hi : ¬ i.val / 2 = 0) (hj : j.val / 2 = 0) (x : RSite L) :
    (sysR L N).hol ((i, j), x) (gT L (siteG L x a) U) = (sysR L N).hol ((i, j), x) U * a⁻¹ := by
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  have h1 : rshift L i x ≠ x := WindowRead.rshift_ne L (hL i) x
  have h2 : rshift L j x ≠ x := WindowRead.rshift_ne L (hL j) x
  have h3 : rshift L j (rshift L i x) ≠ x := rshift2_ne L hji (hL j) x
  rw [hol_eq, hol_eq]
  simp only [gT, siteG, if_neg hi, if_pos hj, if_neg h1, if_neg h2, if_neg h3, ↓reduceIte, inv_one,
    mul_one, one_mul]
  group

/-- **The gauge rotation preserves product Haar**: left and right invariance of `probHaar` per link, assembled
by `Measure.pi_map_pi`. DERIVED: `2`, `0` as in `gT`. -/
theorem gT_measurePreserving (h : RSite L → SUN.SU N) :
    MeasurePreserving (gT L h) (Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  have hc : ∀ l : RLink L, MeasurePreserving
      (fun u : SUN.SU N => if l.1.val / 2 = 0 then h l.2 * u * (h (rshift L l.1 l.2))⁻¹ else u)
      (probHaar (SUN.SU N)) (probHaar (SUN.SU N)) := by
    intro l
    by_cases hl : l.1.val / 2 = 0
    · simp only [if_pos hl]
      exact (measurePreserving_mul_right (probHaar (SUN.SU N)) _).comp
        (measurePreserving_mul_left (probHaar (SUN.SU N)) _)
    · simp only [if_neg hl]
      exact MeasurePreserving.id _
  have hmeas : Measurable (gT L h) := by
    refine measurable_pi_lambda _ fun l => ?_
    by_cases hl : l.1.val / 2 = 0
    · simp only [gT, if_pos hl]
      exact (measurable_const.mul (measurable_pi_apply l)).mul measurable_const
    · simp only [gT, if_neg hl]
      exact measurable_pi_apply l
  refine ⟨hmeas, ?_⟩
  have hform : gT L h = fun (U : RLink L → SUN.SU N) (l : RLink L) =>
      (fun u : SUN.SU N => if l.1.val / 2 = 0 then h l.2 * u * (h (rshift L l.1 l.2))⁻¹ else u) (U l) := by
    funext U l; rfl
  rw [hform, Measure.pi_map_pi (fun l => (hc l).aemeasurable)]
  simp only [(hc _).map_eq]

/-- Product-Haar integrals of continuous functions are invariant under the gauge rotation. No numeral. -/
theorem integral_gT (h : RSite L → SUN.SU N) (F : (RLink L → SUN.SU N) → ℝ) (hF : Continuous F) :
    ∫ U, F (gT L h U) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
      = ∫ U, F U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  have hmp := gT_measurePreserving (N := N) L h
  rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable),
    hmp.map_eq]

/-- **Averaging over a translating family**: if measure-preserving maps `T g` leave `E` invariant and move the
holonomy `Φ` by `m g`, and `∫ φ(m g k) dg = ⟨φ⟩_Haar` for every `k`, then `∫ φ(Φ) E = ⟨φ⟩_Haar ∫ E`.
No numeral. -/
theorem integral_haar_avg (T : SUN.SU N → (RLink L → SUN.SU N) → (RLink L → SUN.SU N))
    (hT : ∀ (g : SUN.SU N) (F : (RLink L → SUN.SU N) → ℝ), Continuous F →
      ∫ U, F (T g U) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
        = ∫ U, F U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)))
    (Φ : (RLink L → SUN.SU N) → SUN.SU N) (hΦ : Continuous Φ) (E : (RLink L → SUN.SU N) → ℝ)
    (hE : Continuous E) (m : SUN.SU N → SUN.SU N → SUN.SU N)
    (hm : Continuous fun p : SUN.SU N × SUN.SU N => m p.1 p.2)
    (hmΦ : ∀ g U, Φ (T g U) = m g (Φ U)) (hET : ∀ g U, E (T g U) = E U)
    (hmH : ∀ k, ∫ g, WilsonAction.wilsonDensity (m g k) ∂(probHaar (SUN.SU N)) = WindowRead.haarMeanN N) :
    ∫ U, WilsonAction.wilsonDensity (Φ U) * E U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
      = WindowRead.haarMeanN N * ∫ U, E U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  set π : Measure (RLink L → SUN.SU N) := Measure.pi fun _ : RLink L => probHaar (SUN.SU N) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  have hshift : ∀ g : SUN.SU N, ∫ U, WilsonAction.wilsonDensity (m g (Φ U)) * E U ∂π
      = ∫ U, WilsonAction.wilsonDensity (Φ U) * E U ∂π := by
    intro g
    rw [← hT g (fun U => WilsonAction.wilsonDensity (Φ U) * E U)
      ((WilsonAction.continuous_wilsonDensity.comp hΦ).mul hE)]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp only [hmΦ, hET]
  have hjc : Continuous fun z : SUN.SU N × (RLink L → SUN.SU N) =>
      WilsonAction.wilsonDensity (m z.1 (Φ z.2)) * E z.2 :=
    (WilsonAction.continuous_wilsonDensity.comp
      (hm.comp (continuous_fst.prodMk (hΦ.comp continuous_snd)))).mul (hE.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (g : SUN.SU N) (U : RLink L → SUN.SU N) =>
      WilsonAction.wilsonDensity (m g (Φ U)) * E U) ((probHaar (SUN.SU N)).prod π) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hjc.continuousOn
    exact ContactFloor.integrable_of_bounded hjc.measurable M
      (fun z => by have hz := hM z (mem_univ z); rw [Real.norm_eq_abs] at hz; exact hz)
  have hswap := integral_integral_swap hint
  calc ∫ U, WilsonAction.wilsonDensity (Φ U) * E U ∂π
      = ∫ _g : SUN.SU N, (∫ U, WilsonAction.wilsonDensity (Φ U) * E U ∂π) ∂(probHaar (SUN.SU N)) :=
        (ContactFloor.integral_const_prob _ _).symm
    _ = ∫ g, (∫ U, WilsonAction.wilsonDensity (m g (Φ U)) * E U ∂π) ∂(probHaar (SUN.SU N)) := by
        simp only [hshift]
    _ = ∫ U, (∫ g, WilsonAction.wilsonDensity (m g (Φ U)) * E U ∂(probHaar (SUN.SU N))) ∂π := hswap
    _ = ∫ U, WindowRead.haarMeanN N * E U ∂π := by
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        simp only [integral_mul_const, hmH]
    _ = WindowRead.haarMeanN N * ∫ U, E U ∂π := integral_const_mul _ _

end Gauge

/-! ## 5. The decoupled end -/

/-- **The in-plane action is gauge invariant under `gT`.** DERIVED: `2`, `0` as in `gT`. -/
theorem sinR_gT (n : ℕ) (h : RSite (fun _ : Fin 4 => n) → SUN.SU N) (U : Lk n → SUN.SU N) :
    sinR N n (gT (fun _ => n) h U) = sinR N n U := by
  unfold sinR
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, j⟩, x⟩ := q
  dsimp only
  by_cases hq : AnisoTorus.inPlane (i, j) = true
  · rw [if_pos hq, if_pos hq]
    unfold plaq
    have key : ∀ i j : Fin 4, AnisoTorus.inPlane (i, j) = true →
        (i.val / 2 = 0 ∧ j.val / 2 = 0) ∨ (¬ i.val / 2 = 0 ∧ ¬ j.val / 2 = 0) := by decide
    rcases key i j hq with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [hol_gT_low _ h U hi hj x]
      exact WilsonAction.wilsonDensity_conj _ _
    · rw [hol_gT_high _ h U hi hj x]
  · rw [if_neg hq, if_neg hq]

/-- **A mixed plaquette is Haar-distributed under the decoupled weight**:
`∫ φ(hol_q) e^{−β S_in} = ⟨φ⟩_Haar ∫ e^{−β S_in}`, on a torus of side `n ≥ 2`. DERIVED: `2` the least extent;
`0` the decoupled end. -/
theorem integral_plaq_mul_exp {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (q : Pq n)
    (hq : ¬ AnisoTorus.inPlane q.1 = true) :
    ∫ U, plaq N n q U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = WindowRead.haarMeanN N * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  have hq' : ¬ AnisoTorus.inPlane (i, j) = true := hq
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
  have key : ∀ i j : Fin 4, ¬ AnisoTorus.inPlane (i, j) = true →
      (i.val / 2 = 0 ∧ ¬ j.val / 2 = 0) ∨ (¬ i.val / 2 = 0 ∧ j.val / 2 = 0) := by decide
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hET : ∀ (h : RSite (fun _ : Fin 4 => n) → SUN.SU N) (U : Lk n → SUN.SU N),
      Real.exp (-(β * sinR N n (gT (fun _ => n) h U))) = Real.exp (-(β * sinR N n U)) :=
    fun h U => by rw [sinR_gT]
  unfold plaq
  rcases key i j hq' with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact integral_haar_avg (fun _ => n) (fun g U => gT (fun _ => n) (siteG (fun _ => n) x g) U)
      (fun g F hF => integral_gT (fun _ => n) _ F hF)
      (fun U => (sysR (fun _ => n) N).hol ((i, j), x) U) (MixAnchor.continuous_hol _)
      (fun U => Real.exp (-(β * sinR N n U))) hE (fun g k => g * k) continuous_mul
      (fun g U => hol_gT_mixA (fun _ => n) hL g U hi hj x) (fun g U => hET _ U)
      (fun k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) WilsonAction.wilsonDensity k)
  · exact integral_haar_avg (fun _ => n) (fun g U => gT (fun _ => n) (siteG (fun _ => n) x g⁻¹) U)
      (fun g F hF => integral_gT (fun _ => n) _ F hF)
      (fun U => (sysR (fun _ => n) N).hol ((i, j), x) U) (MixAnchor.continuous_hol _)
      (fun U => Real.exp (-(β * sinR N n U))) hE (fun g k => k * g) (continuous_snd.mul continuous_fst)
      (fun g U => by rw [hol_gT_mixB (fun _ => n) hL g⁻¹ U hi hj x, inv_inv]) (fun g U => hET _ U)
      (fun k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) WilsonAction.wilsonDensity k)

/-- The mixed orientations count `8` per site. DERIVED: `8` the mixed ordered orientations; `4` the
dimension; `0` the excluded terms. -/
theorem sum_mixed (n : ℕ) (H : ℝ) :
    (∑ q : Pq n, if AnisoTorus.inPlane q.1 then (0 : ℝ) else H) = 8 * (n : ℝ) ^ 4 * H := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, AnisoTorus.inPlane, Fintype.card_pi]
  ring

/-- **The unnormalized mixed mean at the decoupled end.** DERIVED: `2` the least extent; `0` the decoupled end
and the excluded terms. -/
theorem mixNum_zero {n : ℕ} (hn : 2 ≤ n) (β : ℝ) :
    mixNum N β 0 n
      = (∑ q : Pq n, if AnisoTorus.inPlane q.1 then (0 : ℝ) else WindowRead.haarMeanN N)
        * AnisoTorus.ZA N β 0 n := by
  have hZ : AnisoTorus.ZA N β 0 n = ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    rw [ZA_eq_int]; simp only [zero_mul, add_zero]
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  rw [hZ, Finset.sum_mul]
  unfold mixNum
  simp only [zero_mul, add_zero]
  unfold smixR
  simp only [Finset.sum_mul]
  have hint : ∀ q : Pq n, Integrable (fun U : Lk n → SUN.SU N =>
      (if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U) * Real.exp (-(β * sinR N n U))) (piH N n) :=
    fun q => ((continuous_if_const _ (fun _ => continuous_const) (fun _ => continuous_plaq n q)).mul
      hE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun q _ => hint q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : AnisoTorus.inPlane q.1 = true
  · simp only [if_pos hq, zero_mul, integral_zero]
  · simp only [if_neg hq]
    exact integral_plaq_mul_exp hn β q hq

/-- **The mixed mean at the decoupled end is extensive**: `⟨S_mix⟩_n(β, 0) = 8 n⁴ ⟨φ⟩_Haar`, side `n ≥ 2`.
DERIVED: `8` the mixed ordered orientations; `4` the dimension; `2` the least extent; `0` the decoupled end. -/
theorem meanMix_zero {n : ℕ} (hn : 2 ≤ n) (β : ℝ) :
    meanMix N β 0 n = 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N := by
  unfold meanMix
  rw [mixNum_zero hn, mul_div_assoc, div_self (ZA_pos β 0 n).ne', mul_one, sum_mixed]

/-- **The mixed cut energy vanishes at the decoupled end**, at every `β` and every window `w ≥ 1`.
DERIVED: `16 = 2⁴`, `2` the doubling; `8`, `4` as in `meanMix_zero`; `1` the least window; `0` the decoupled
end. -/
theorem mixCut_zero (β : ℝ) {w : ℕ} (hw : 1 ≤ w) : mixCut N β 0 w = 0 := by
  have h1 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have h2 : 2 ≤ 2 ^ (w + 1) := DeltaLengthTower.two_le_two_pow (by omega)
  unfold mixCut
  rw [meanMix_zero h2, meanMix_zero h1]
  push_cast
  ring

/-! ## 6. The bound and the stall -/

/-- **`MixCutBound N β`, a named input (not proved)**: the mixed cut energy is bounded above, uniformly over the
windows `w ≥ 1` and the segment `t ∈ [0, β]`. A window-uniform finite-size energy estimate (module docstring);
it fails wherever the segment has a first stall (`first_stall_mixCut_unbounded`). DERIVED: `1` the least window;
`0` the axis. -/
def MixCutBound (N : ℕ) (β : ℝ) : Prop :=
  ∃ M : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ t : ℝ, 0 ≤ t → t ≤ β → mixCut N β t w ≤ M

/-- **A bounded cut energy carries vanishing across the end of an interval**: if `(β, t)` vanishes for
`t ∈ [s, t*)` and `mixCut N β τ w ≤ M` for `τ ∈ (s, t*)` and every window `w ≥ 1`, then `(β, t*)` vanishes.
Inherited: `1/1000` the seed. DERIVED: `1/2000` half the seed; `1` the least window. -/
theorem vanish_of_cut_le (hN : N ≠ 0) {β s ts M : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (hst : s < ts)
    (hvan : ∀ t : ℝ, s ≤ t → t < ts → (β, t) ∈ MixPlane.VanishSet N)
    (hC : ∀ w : ℕ, 1 ≤ w → ∀ τ : ℝ, s < τ → τ < ts → mixCut N β τ w ≤ M) :
    (β, ts) ∈ MixPlane.VanishSet N := by
  set δ : ℝ := 1 / (2000 * (|M| + 1)) with hδdef
  have hM1 : (0 : ℝ) < |M| + 1 := by positivity
  have hδ : 0 < δ := by positivity
  set s' : ℝ := max s (ts - δ) with hs'def
  have hs's : s ≤ s' := le_max_left _ _
  have hs't : s' < ts := max_lt hst (by linarith)
  have hgap : ts - s' ≤ δ := by linarith [le_max_right s (ts - δ)]
  have hpos : 0 < ts - s' := by linarith
  have hMgap : M * (ts - s') < 1 / 2000 := by
    calc M * (ts - s') ≤ |M| * (ts - s') := mul_le_mul_of_nonneg_right (le_abs_self M) hpos.le
      _ ≤ |M| * δ := mul_le_mul_of_nonneg_left hgap (abs_nonneg M)
      _ < (|M| + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
      _ = 1 / 2000 := by rw [hδdef]; field_simp
  have hv := hvan s' hs's hs't
  obtain ⟨w, hlt, hw⟩ := ((hv.2.2.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2000 by norm_num))).and
    (eventually_ge_atTop 1)).exists
  obtain ⟨τ, hτ, hτeq⟩ := exists_hasDerivAt_eq_slope (fun x => AnisoTorus.DA N β x w)
    (fun x => mixCut N β x w) hs't (MixAnchor.continuous_DA β w).continuousOn
    (fun x _ => hasDerivAt_DA_mix β x w)
  have hCτ := hC w hw τ (lt_of_le_of_lt hs's hτ.1) hτ.2
  rw [hτeq, div_le_iff₀ hpos] at hCτ
  have hseed : AnisoTorus.DA N β ts w < 1 / 1000 := by
    have : AnisoTorus.DA N β s' w < 1 / 2000 := hlt
    linarith
  exact (MixPlane.mem_vanishSet_iff_seed_lt hN).mpr ⟨⟨hβ, by linarith⟩, w, hw, hseed⟩

/-- **A bounded mixed cut energy excludes a stall on the segment**: under the cited `TwoDCharacter N β`,
`MixCutBound N β` gives `NoStallOnSegment N β`. At a first stall `t*` (`MixPlane.segment_first_stall`),
`vanish_of_cut_le` from `s = 0` makes `(β, t*)` vanish. DERIVED: `0` the axis. -/
theorem noStallOnSegment_of_mixCutBound (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hC : LayerSplit.TwoDCharacter N β) (hM : MixCutBound N β) : MixPlane.NoStallOnSegment N β := by
  by_contra h
  obtain ⟨ts, hts0, htsβ, hstall, hvan⟩ := MixPlane.segment_first_stall hN hβ hC h
  obtain ⟨M, hMb⟩ := hM
  exact hstall.2 (vanish_of_cut_le hN hβ le_rfl hts0 (fun t ht htt => hvan t ht htt)
    (fun w hw τ hτ hτt => hMb w hw τ hτ.le (hτt.le.trans htsβ)))

/-- **Frequently `TwoDCharacter ∧ MixCutBound` gives the strong end.** DERIVED: `0` the lower end. -/
theorem strongEnd_of_mixCutBound (hN : N ≠ 0)
    (h : ∃ᶠ β in atTop, LayerSplit.TwoDCharacter N β ∧ MixCutBound N β) : StrongEnd N :=
  MixPlane.strongEnd_of_noStallOnSegment ((h.and_eventually (eventually_ge_atTop (0 : ℝ))).mono
    fun _ hβ => noStallOnSegment_of_mixCutBound hN hβ.2 hβ.1.1 hβ.1.2)

/-- **At a first stall the mixed cut energy is unbounded above** on `(s, t*)` × windows, for every
`s ∈ [0, t*)`: the contrapositive of `vanish_of_cut_le`. DERIVED: `1` the least window; `0` the axis. -/
theorem first_stall_mixCut_unbounded (hN : N ≠ 0) {β ts : ℝ} (hβ : 0 ≤ β)
    (hstall : (β, ts) ∈ MixPlane.StallSet N)
    (hvan : ∀ t : ℝ, 0 ≤ t → t < ts → (β, t) ∈ MixPlane.VanishSet N) {s : ℝ} (hs : 0 ≤ s) (hst : s < ts)
    (M : ℝ) : ∃ w : ℕ, 1 ≤ w ∧ ∃ τ : ℝ, s < τ ∧ τ < ts ∧ M < mixCut N β τ w := by
  by_contra hcon
  push Not at hcon
  exact hstall.2 (vanish_of_cut_le hN hβ hs hst (fun t ht htt => hvan t (hs.trans ht) htt) hcon)

/-- **A stall on the segment forces an unbounded mixed cut energy below its first point**: under the cited
`TwoDCharacter N β`, `¬ NoStallOnSegment N β` gives `t* ∈ (0, β]` with `(β, t*)` stalled and, for every
`s ∈ [0, t*)` and every `M`, a window `w ≥ 1` and `τ ∈ (s, t*)` with `M < mixCut N β τ w`. DERIVED: `0` the axis;
`1` the least window. -/
theorem segment_stall_mixCut_unbounded (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hC : LayerSplit.TwoDCharacter N β) (h : ¬ MixPlane.NoStallOnSegment N β) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ β ∧ (β, ts) ∈ MixPlane.StallSet N ∧
      ∀ s : ℝ, 0 ≤ s → s < ts → ∀ M : ℝ, ∃ w : ℕ, 1 ≤ w ∧ ∃ τ : ℝ, s < τ ∧ τ < ts ∧ M < mixCut N β τ w := by
  obtain ⟨ts, hts0, htsβ, hstall, hvan⟩ := MixPlane.segment_first_stall hN hβ hC h
  exact ⟨ts, hts0, htsβ, hstall, fun s hs hst M =>
    first_stall_mixCut_unbounded hN hβ hstall hvan hs hst M⟩

end MassGap.MixCut

#print axioms MassGap.MixCut.hasDerivAt_integral_exp_lin
#print axioms MassGap.MixCut.sin_eq
#print axioms MassGap.MixCut.smix_eq
#print axioms MassGap.MixCut.ZA_eq_int
#print axioms MassGap.MixCut.ZA_pos
#print axioms MassGap.MixCut.continuous_plaq
#print axioms MassGap.MixCut.continuous_sinR
#print axioms MassGap.MixCut.continuous_smixR
#print axioms MassGap.MixCut.hasDerivAt_ZA
#print axioms MassGap.MixCut.hasDerivAt_logZA
#print axioms MassGap.MixCut.hasDerivAt_DA_mix
#print axioms MassGap.MixCut.rshift_comm
#print axioms MassGap.MixCut.rshift2_ne
#print axioms MassGap.MixCut.hol_gT_low
#print axioms MassGap.MixCut.hol_gT_high
#print axioms MassGap.MixCut.hol_gT_mixA
#print axioms MassGap.MixCut.hol_gT_mixB
#print axioms MassGap.MixCut.gT_measurePreserving
#print axioms MassGap.MixCut.integral_gT
#print axioms MassGap.MixCut.integral_haar_avg
#print axioms MassGap.MixCut.sinR_gT
#print axioms MassGap.MixCut.integral_plaq_mul_exp
#print axioms MassGap.MixCut.sum_mixed
#print axioms MassGap.MixCut.mixNum_zero
#print axioms MassGap.MixCut.meanMix_zero
#print axioms MassGap.MixCut.mixCut_zero
#print axioms MassGap.MixCut.vanish_of_cut_le
#print axioms MassGap.MixCut.noStallOnSegment_of_mixCutBound
#print axioms MassGap.MixCut.strongEnd_of_mixCutBound
#print axioms MassGap.MixCut.first_stall_mixCut_unbounded
#print axioms MassGap.MixCut.segment_stall_mixCut_unbounded
