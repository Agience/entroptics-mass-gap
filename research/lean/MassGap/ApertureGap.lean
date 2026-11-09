import Mathlib
import MassGap.GapAttack

/-!
# MassGap.ApertureGap — the gap at every finite aperture, the fixed-diffraction bridge, and its unit tests

The aperture is a box of fixed physical size `L`. Its slice transfer kernel `kT` carries the view: the half-waves
that fit are measurable (a discrete top of the spectrum, so a gap at every finite aperture), and what is too far
away drops off (clustering). This module proves the first half eigen-free at every finite cross-section, states
the second half as one statement on the slice kernels, and tests that statement on three models.

## 1. The finite-aperture gap (proved, eigen-free)

`CrossRatio K t`: `|K(x,y)K(x',y') − K(x,y')K(x',y)| ≤ t (K(x,y)K(x',y') + K(x,y')K(x',y))` for all four points.
At `t < 1` every two rows of `K` are proportional within the factor `(1+t)/(1−t)`: `K` is rank one up to `t`.

* `crossRatio_of_bounds`: `c ≤ a ≤ M`, `c > 0` give `CrossRatio a θ`, `θ = (M² − c²)/(M² + c²) < 1`.
* `crossRatio_conv`: `CrossRatio B θ`, `CrossRatio K t` give `CrossRatio (B ∗ K) (θ t)`. The difference of the
  two cross products of `B ∗ K` is half the integral of the product of the differences for `B` and for `K`,
  and their sum is half the integral of the product of the sums (Fubini, `integral_prod_mul`). This is the
  Birkhoff contraction of the positive cone, in the form the cyclic integrals read.
* `crossRatio_iter`: `CrossRatio a θ ⇒ CrossRatio a^{∗(i+1)} θ^{i+1}`.
* `cyc_double_ge`: `(1 − θⁿ) cyc(a, n)² ≤ (1 + θⁿ) cyc(a, 2n)` for `n ≥ 1`. The cycle `cyc(2n)` is
  `∫∫ a^{∗n}(x,y) a^{∗n}(y,x)` and `cyc(n)²` is `∫∫ a^{∗n}(x,x) a^{∗n}(y,y)`; the cross ratio at `(x,y,x,y)`
  compares them pointwise.
* `aperture_gap`: for the slice kernel of every cross-section `T`, direction `s` and `β ≥ 0`, with
  `θ = (1 − kTmin²)/(1 + kTmin²) ∈ [0, 1)` (`apTheta_nonneg`, `apTheta_lt_one`):
  `(1 − θⁿ) cyc(kT, n)² ≤ (1 + θⁿ) cyc(kT, 2n)` at every `n ≥ 1`.
* `aperture_gap_tendsto`: at fixed cross-section, `cyc(kT, 4j)/cyc(kT, 2j)² → 1`: the cycle-direction doubling
  defect tends to `0`. The top of the spectrum is simple and isolated, with excited weight at most `θⁿ` per
  length `n`. The lower side uses only `kTmin ≤ kT ≤ 1`; the upper side `cyc(4j) ≤ cyc(2j)²` is
  `ApertureWindow.cycT_pos_le` (symmetry of `kT`). No eigenbasis, compactness or definiteness is used.

`θ` is a property of one cross-section at one coupling. `kTmin = exp(−β(spMax + 2 tpMax))` and both maxima grow
with the number of cross-section sites, so at the physical side `θ` tends to `1` faster than `θⁿ` decays:
`aperture_gap` is the gap at a finite aperture in lattice units, not uniformly in the zoom.

## 2. The fixed-diffraction statement (defined) and its consequence (proved)

`FixedDiffraction m C d`: `m > 0`, and for every physical size `L ≥ 1`, eventually in `β`, at the physical side
`n = 2^{kPhys L β + 2}` (lattice side `n`, physical side in `(L/2, L]`) and in every direction `s`,

  `cyc(kT_s, 2n) ≥ exp(−C L^d e^{−mL}) · cyc(kT_s, n)²`.

One statement. Read in the eigenvalue model (`ApertureTwo.tau`, `r_i = e^{−E_i a}` with `E_i` the excited
energies in physical units and `ℓ = n a` the physical length of the cycle), the defect is at most
`2 log(1 + τ)` with `τ = Σ_{i ≥ 1} e^{−E_i ℓ} = e^{−mℓ} Σ_{i ≥ 1} e^{−(E_i − m)ℓ}`. The multiplicity is part of
the statement, as its prefactor: `C L^d` bounds the weighted density of states `Σ_{i ≥ 1} e^{−(E_i − m)ℓ}` of a
box of physical size `L`, uniformly in the lattice spacing. `model_defect_le` proves that reading: a gap clause
(`E_i ≥ m`, implicit in the weighted count being finite at the rate `m`) and the weighted count `≤ P` give a
defect at most `2 P e^{−mℓ}`. A gap uniform in the zoom without the prefactor is not enough
(`GapAttack` section 2): the number of excited levels grows with the cross-section.

* `kernFar_of_fixedDiffraction`: at `L ≥ 1` with `C L^d e^{−mL} ≤ ε`, `FixedDiffraction m C d ⇒ KernFar L ε`.
* `eventually_poly_exp_le`: `C L^d e^{−mL} ≤ ε` eventually in `L`, for `m, ε > 0`.
* `physDefect_of_fixedDiffraction`: eventually in `L`, `PhysDefect L (1/1000)` (at `ε = 1/15000`, the factor
  `15` of `GapAttack.physDefect_of_kernFar`).
* `runSeed_of_fixedDiffraction`: `FixedDiffraction m C d ⇒ WDeltaRun.RunSeed 2`, the `hW` input.

## 3. Unit tests (proved)

`ModelFD D m C d`: `D L K ≤ C L^d e^{−mL}` for every `L ≥ 1` and every zoom `K` (the number of lattice modes per
direction of the box), with `D L K` the one-direction doubling defect `2 log Z(L) − log Z(2L)` of the box of
physical side `L` on a cycle of physical length `L`. It is stronger than `FixedDiffraction`'s defect form (it
asks every zoom `K`, where `FixedDiffraction` asks eventually in `β`).

* 2D `SU(2)` by characters. On the torus of sides `L` and `ℓ`, the heat-kernel character
  expansion gives `Z = Σ_{n ≥ 1} exp(−κ L ℓ (n² − 1))` (`n = 2j + 1`, `κ = g²/8`, the Casimir `(n² − 1)/4`).
  `ym_modelFD`: `ModelFD` holds for every `m > 0` (`d = 0`). The first excited level `3κL` grows with `L`
  (the flux energy of the string), so the excited weight `e^{−3κL²}` decays faster than any `e^{−mL}`.
* 4D massless Gaussian. Dirichlet modes of the lattice box (`k_i ∈ {1, …, K}`, lattice dispersion
  `p̂ = (2(K+1)/L) sin(π k/(2(K+1)))`), one oscillator per mode with defect `log((1+q)/(1−q))`, `q = e^{−ωL}`.
  `massless_not_modelFD`: no `m > 0`, `C`, `d` satisfy `ModelFD` (the counterexample is exhibited at zoom
  `K = 1`; `freq_low_le` holds at every `K ≥ 1`, and `ObserverTheory.gaussD_lower_zoom` gives the lower bound at
  every zoom `K ≥ 1`). The lowest half-wave has `ωL ≤ 2π` at every
  `L` (`E₁ L` constant), so the defect stays above `e^{−2π}`.
* 4D massive Gaussian of mass `M > 0`, same modes. `massive_modelFD`: `ModelFD` holds at every `m < M`
  (`d = 0`); `massive_not_modelFD`: it fails at every `m > M` (exhibited at `K = 1`). The diffraction length is `1/M`.
`FixedDiffraction` is strictly stronger than the far input it feeds (it gives `PhysDefect` at every large `L`
with a rate; `RunSeed 2` needs one `L`).

DERIVED (module-wide): `1/1000` the `PhysDefect` threshold of `ApertureBridge.runSeed_of_physDefect`; `15` from
`GapAttack.physDefect_of_kernFar`; `1/15000 = (1/1000)/15`; `2` in `kPhys + 2` from `GapAttack.KernFar`; `1` the
bound `kT ≤ 1` (`RectTransfer.kT_le_one`); `2π` the bound `π√3 ≤ 2π` on the lowest Dirichlet half-wave; `3` the
dimension of the box; `(1 − λ)/2` the transverse weight of the Cauchy–Schwarz split `λ² + 3((1 − λ)/2)² ≤ 1`.
-/

noncomputable section

namespace MassGap.ApertureGap

open MeasureTheory Real Filter Topology Set MassGap MassGap.KernelPower MassGap.CyclicKernel
  MassGap.PhysicalScaleSmall MassGap.ApertureNearAll MassGap.RectWilson

/-! ## 1. The finite-aperture gap -/

section CrossRatio

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The cross ratio of a kernel is within `t`**: every two rows are proportional within `(1+t)/(1−t)`. -/
def CrossRatio (K : X → X → ℝ) (t : ℝ) : Prop :=
  ∀ x x' y y', |K x y * K x' y' - K x y' * K x' y| ≤ t * (K x y * K x' y' + K x y' * K x' y)

omit [MeasurableSpace X] in
/-- A kernel with `c ≤ a ≤ M`, `c > 0`, has cross ratio within `(M² − c²)/(M² + c²)`. -/
theorem crossRatio_of_bounds {a : X → X → ℝ} {c M : ℝ} (hc : 0 < c) (hlo : ∀ x y, c ≤ a x y)
    (hhi : ∀ x y, a x y ≤ M) : CrossRatio a ((M ^ 2 - c ^ 2) / (M ^ 2 + c ^ 2)) := by
  intro x x' y y'
  have hD : 0 < M ^ 2 + c ^ 2 := by positivity
  have hp1 : c ^ 2 ≤ a x y * a x' y' := by
    rw [sq]; exact mul_le_mul (hlo x y) (hlo x' y') hc.le (hc.le.trans (hlo x y))
  have hp2 : a x y * a x' y' ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul (hhi x y) (hhi x' y') (hc.le.trans (hlo x' y'))
      (hc.le.trans ((hlo x y).trans (hhi x y)))
  have hq1 : c ^ 2 ≤ a x y' * a x' y := by
    rw [sq]; exact mul_le_mul (hlo x y') (hlo x' y) hc.le (hc.le.trans (hlo x y'))
  have hq2 : a x y' * a x' y ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul (hhi x y') (hhi x' y) (hc.le.trans (hlo x' y))
      (hc.le.trans ((hlo x y).trans (hhi x y)))
  have e1 := mul_le_mul_of_nonneg_left hp2 (sq_nonneg c)
  have e2 := mul_le_mul_of_nonneg_left hq1 (sq_nonneg M)
  have e3 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg c)
  have e4 := mul_le_mul_of_nonneg_left hp1 (sq_nonneg M)
  rw [div_mul_eq_mul_div, abs_sub_le_iff, le_div_iff₀ hD, le_div_iff₀ hD]
  constructor <;> nlinarith

theorem integrable_row_col {B K : X → X → ℝ} (hB : Bdd B) (hK : Bdd K) (x y : X) :
    Integrable (fun z => B x z * K z y) μ := by
  obtain ⟨CB, hCB⟩ := hB.bdd
  obtain ⟨CK, hCK⟩ := hK.bdd
  refine integrable_of_bdd ((hB.row x).mul (hK.col y)) (C := CB * CK) fun z => ?_
  rw [abs_mul]
  exact mul_le_mul (hCB x z) (hCK z y) (abs_nonneg _) ((abs_nonneg _).trans (hCB x z))

/-- One side of the composition step. -/
theorem crossRatio_conv_le {B K : X → X → ℝ} (hB : Bdd B) (hK : Bdd K) {θ t : ℝ}
    (hBc : CrossRatio B θ) (hKc : CrossRatio K t) (x x' y y' : X) :
    conv μ B K x y * conv μ B K x' y' - conv μ B K x y' * conv μ B K x' y
      ≤ θ * t * (conv μ B K x y * conv μ B K x' y' + conv μ B K x y' * conv μ B K x' y) := by
  have i1 : Integrable (fun p : X × X => (B x p.1 * K p.1 y) * (B x' p.2 * K p.2 y')) (μ.prod μ) :=
    (integrable_row_col (μ := μ) hB hK x y).mul_prod (integrable_row_col (μ := μ) hB hK x' y')
  have i2 : Integrable (fun p : X × X => (B x p.1 * K p.1 y') * (B x' p.2 * K p.2 y)) (μ.prod μ) :=
    (integrable_row_col (μ := μ) hB hK x y').mul_prod (integrable_row_col (μ := μ) hB hK x' y)
  have i3 : Integrable (fun p : X × X => (B x' p.1 * K p.1 y) * (B x p.2 * K p.2 y')) (μ.prod μ) :=
    (integrable_row_col (μ := μ) hB hK x' y).mul_prod (integrable_row_col (μ := μ) hB hK x y')
  have i4 : Integrable (fun p : X × X => (B x' p.1 * K p.1 y') * (B x p.2 * K p.2 y)) (μ.prod μ) :=
    (integrable_row_col (μ := μ) hB hK x' y').mul_prod (integrable_row_col (μ := μ) hB hK x y)
  have I1 : ∫ p : X × X, (B x p.1 * K p.1 y) * (B x' p.2 * K p.2 y') ∂(μ.prod μ)
      = conv μ B K x y * conv μ B K x' y' :=
    integral_prod_mul (fun z => B x z * K z y) (fun z => B x' z * K z y')
  have I2 : ∫ p : X × X, (B x p.1 * K p.1 y') * (B x' p.2 * K p.2 y) ∂(μ.prod μ)
      = conv μ B K x y' * conv μ B K x' y :=
    integral_prod_mul (fun z => B x z * K z y') (fun z => B x' z * K z y)
  have I3 : ∫ p : X × X, (B x' p.1 * K p.1 y) * (B x p.2 * K p.2 y') ∂(μ.prod μ)
      = conv μ B K x' y * conv μ B K x y' :=
    integral_prod_mul (fun z => B x' z * K z y) (fun z => B x z * K z y')
  have I4 : ∫ p : X × X, (B x' p.1 * K p.1 y') * (B x p.2 * K p.2 y) ∂(μ.prod μ)
      = conv μ B K x' y' * conv μ B K x y :=
    integral_prod_mul (fun z => B x' z * K z y') (fun z => B x z * K z y)
  have hpt : ∀ p : X × X,
      (1 - θ * t) * ((B x p.1 * K p.1 y) * (B x' p.2 * K p.2 y') + (B x' p.1 * K p.1 y') * (B x p.2 * K p.2 y))
        ≤ (1 + θ * t) * ((B x p.1 * K p.1 y') * (B x' p.2 * K p.2 y)
          + (B x' p.1 * K p.1 y) * (B x p.2 * K p.2 y')) := by
    intro p
    have hA := hBc x x' p.1 p.2
    have hK' := hKc p.1 p.2 y y'
    have hprod : (B x p.1 * B x' p.2 - B x p.2 * B x' p.1) * (K p.1 y * K p.2 y' - K p.1 y' * K p.2 y)
        ≤ θ * (B x p.1 * B x' p.2 + B x p.2 * B x' p.1) * (t * (K p.1 y * K p.2 y' + K p.1 y' * K p.2 y)) :=
      calc _ ≤ |(B x p.1 * B x' p.2 - B x p.2 * B x' p.1) * (K p.1 y * K p.2 y' - K p.1 y' * K p.2 y)| :=
            le_abs_self _
        _ = |B x p.1 * B x' p.2 - B x p.2 * B x' p.1| * |K p.1 y * K p.2 y' - K p.1 y' * K p.2 y| :=
            abs_mul _ _
        _ ≤ _ := mul_le_mul hA hK' (abs_nonneg _) ((abs_nonneg _).trans hA)
    linarith [hprod]
  have i14 : Integrable (fun p : X × X => (1 - θ * t) *
      ((B x p.1 * K p.1 y) * (B x' p.2 * K p.2 y') + (B x' p.1 * K p.1 y') * (B x p.2 * K p.2 y))) (μ.prod μ) :=
    (i1.add i4).const_mul _
  have i23 : Integrable (fun p : X × X => (1 + θ * t) *
      ((B x p.1 * K p.1 y') * (B x' p.2 * K p.2 y) + (B x' p.1 * K p.1 y) * (B x p.2 * K p.2 y'))) (μ.prod μ) :=
    (i2.add i3).const_mul _
  have hmono := integral_mono i14 i23 hpt
  rw [integral_const_mul, integral_const_mul, integral_add i1 i4, integral_add i2 i3, I1, I2, I3, I4]
    at hmono
  linarith [hmono]

/-- **The composition step**: `CrossRatio B θ`, `CrossRatio K t ⇒ CrossRatio (B ∗ K) (θ t)`. -/
theorem crossRatio_conv {B K : X → X → ℝ} (hB : Bdd B) (hK : Bdd K) {θ t : ℝ}
    (hBc : CrossRatio B θ) (hKc : CrossRatio K t) : CrossRatio (conv μ B K) (θ * t) := by
  intro x x' y y'
  rw [abs_sub_le_iff]
  refine ⟨crossRatio_conv_le hB hK hBc hKc x x' y y', ?_⟩
  have h := crossRatio_conv_le (μ := μ) hB hK hBc hKc x x' y' y
  linarith

/-- **Iterates contract**: `CrossRatio a θ ⇒ CrossRatio a^{∗(i+1)} θ^{i+1}`. -/
theorem crossRatio_iter {a : X → X → ℝ} (ha : Bdd a) {θ : ℝ} (hc : CrossRatio a θ) :
    ∀ i, CrossRatio (iter μ a i) (θ ^ (i + 1))
  | 0 => by simpa [iter] using hc
  | i + 1 => by
    have h := crossRatio_conv (μ := μ) ha (ha.iter i) hc (crossRatio_iter ha hc i)
    rw [show θ ^ (i + 1 + 1) = θ * θ ^ (i + 1) by ring]
    exact h

/-- **The doubling of a contracting kernel**: `(1 − t) cyc(a, m+1)² ≤ (1 + t) cyc(a, 2(m+1))` when the
`(m+1)`-fold iterate has cross ratio within `t`. -/
theorem cyc_double_ge_of {a : X → X → ℝ} (ha : Bdd a) {t : ℝ} (m : ℕ) (hc : CrossRatio (iter μ a m) t) :
    (1 - t) * cyc μ a (m + 1) ^ 2 ≤ (1 + t) * cyc μ a (2 * (m + 1)) := by
  set K := iter μ a m with hKdef
  have hK : Bdd K := ha.iter m
  obtain ⟨CK, hCK⟩ := hK.bdd
  have hdiag : Measurable fun x => K x x := hK.meas.comp (measurable_id.prodMk measurable_id)
  have idiag : Integrable (fun x => K x x) μ := integrable_of_bdd hdiag (fun x => hCK x x)
  have i1 : Integrable (fun p : X × X => K p.1 p.1 * K p.2 p.2) (μ.prod μ) := idiag.mul_prod idiag
  have hm2 : Measurable fun p : X × X => K p.1 p.2 * K p.2 p.1 :=
    hK.meas.mul (hK.meas.comp measurable_swap)
  have i2 : Integrable (fun p : X × X => K p.1 p.2 * K p.2 p.1) (μ.prod μ) := by
    refine integrable_of_bdd hm2 (C := CK * CK) fun p => ?_
    rw [abs_mul]
    exact mul_le_mul (hCK p.1 p.2) (hCK p.2 p.1) (abs_nonneg _) ((abs_nonneg _).trans (hCK p.1 p.2))
  have hc1 : cyc μ a (m + 1) = ∫ x, K x x ∂μ := cyc_succ ha m
  have hc2 : cyc μ a (2 * (m + 1)) = ∫ x, ∫ y, K x y * K y x ∂μ ∂μ := by
    rw [show 2 * (m + 1) = (m + m + 1) + 1 by ring, cyc_succ ha, iter_add ha m m]
    rfl
  have J1 : ∫ p : X × X, K p.1 p.1 * K p.2 p.2 ∂(μ.prod μ) = cyc μ a (m + 1) ^ 2 := by
    rw [integral_prod_mul (fun x => K x x) (fun x => K x x), hc1, sq]
  have J2 : ∫ p : X × X, K p.1 p.2 * K p.2 p.1 ∂(μ.prod μ) = cyc μ a (2 * (m + 1)) := by
    rw [integral_prod _ i2, hc2]
  have hpt : ∀ p : X × X, (1 - t) * (K p.1 p.1 * K p.2 p.2) ≤ (1 + t) * (K p.1 p.2 * K p.2 p.1) := by
    intro p
    have h := hc p.1 p.2 p.1 p.2
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  have hmono := integral_mono (i1.const_mul (1 - t)) (i2.const_mul (1 + t)) hpt
  rw [integral_const_mul, integral_const_mul, J1, J2] at hmono
  exact hmono

/-- **The finite-aperture gap for a kernel with a positive floor**, eigen-free: with
`θ = (M² − c²)/(M² + c²)`, `(1 − θⁿ) cyc(a, n)² ≤ (1 + θⁿ) cyc(a, 2n)` at every `n ≥ 1`. -/
theorem cyc_double_ge {a : X → X → ℝ} (ha : Bdd a) {c M : ℝ} (hc : 0 < c) (hlo : ∀ x y, c ≤ a x y)
    (hhi : ∀ x y, a x y ≤ M) (n : ℕ) (hn : 1 ≤ n) :
    (1 - ((M ^ 2 - c ^ 2) / (M ^ 2 + c ^ 2)) ^ n) * cyc μ a n ^ 2
      ≤ (1 + ((M ^ 2 - c ^ 2) / (M ^ 2 + c ^ 2)) ^ n) * cyc μ a (2 * n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact cyc_double_ge_of ha m (crossRatio_iter ha (crossRatio_of_bounds hc hlo hhi) m)

end CrossRatio

section Slice

/-- The contraction coefficient of the slice kernel of cross-section `T` at coupling `β`. -/
def apTheta (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) (β : ℝ) : ℝ :=
  (1 - RectTransfer.kTmin s T β ^ 2) / (1 + RectTransfer.kTmin s T β ^ 2)

theorem kTmin_le_one (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    RectTransfer.kTmin s T β ≤ 1 :=
  (RectTransfer.kT_lower (N := 2) (by norm_num) hβ 1 1).trans (RectTransfer.kT_le_one (by norm_num) hβ 1 1)

theorem apTheta_nonneg (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ apTheta s T β := by
  have h0 := (RectTransfer.kTmin_pos (μ := s) (T := T) β).le
  have h1 := kTmin_le_one s T hβ
  unfold apTheta
  refine div_nonneg ?_ (by positivity)
  nlinarith

theorem apTheta_lt_one (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) (β : ℝ) : apTheta s T β < 1 := by
  have h0 := RectTransfer.kTmin_pos (μ := s) (T := T) β
  unfold apTheta
  rw [div_lt_one (by positivity)]
  nlinarith [pow_pos h0 2]

/-- **The finite-aperture gap** (`aperture_gap`): for every cross-section `T`, direction `s`, `β ≥ 0` and
`n ≥ 1`, `(1 − θⁿ) cyc(kT, n)² ≤ (1 + θⁿ) cyc(kT, 2n)` with `θ = apTheta s T β ∈ [0, 1)`. -/
theorem aperture_gap (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (hn : 1 ≤ n) :
    (1 - apTheta s T β ^ n) * cycT s T β n ^ 2 ≤ (1 + apTheta s T β ^ n) * cycT s T β (2 * n) := by
  have hN : (2 : ℕ) ≠ 0 := by norm_num
  have h := cyc_double_ge (μ := RectTransfer.hS s T 2) (RectTransfer.bdd_kT (μ := s) (T := T) hN hβ)
    (RectTransfer.kTmin_pos β) (RectTransfer.kT_lower hN hβ) (RectTransfer.kT_le_one hN hβ) n hn
  simp only [one_pow] at h
  unfold apTheta
  exact h

/-- **The cycle-direction doubling defect tends to `0` at fixed cross-section**:
`cyc(kT, 4j)/cyc(kT, 2j)² → 1`. -/
theorem aperture_gap_tendsto (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun j : ℕ => cycT s T β (2 * (2 * (j + 1))) / cycT s T β (2 * (j + 1)) ^ 2) atTop (𝓝 1) := by
  have h0 := apTheta_nonneg s T hβ
  have h1 := apTheta_lt_one s T β
  have hpow : Tendsto (fun j : ℕ => apTheta s T β ^ (2 * (j + 1))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
      (tendsto_atTop_mono (fun j => show j ≤ 2 * (j + 1) by omega) tendsto_id)
  have hlow : Tendsto (fun j : ℕ => (1 - apTheta s T β ^ (2 * (j + 1))) / (1 + apTheta s T β ^ (2 * (j + 1))))
      atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h2 : Tendsto (fun j : ℕ => (1 - apTheta s T β ^ (2 * (j + 1))) / (1 + apTheta s T β ^ (2 * (j + 1))))
        atTop (𝓝 ((1 - 0) / (1 + 0))) := (hc.sub hpow).div (hc.add hpow) (by norm_num)
    rw [sub_zero, add_zero, div_one] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun j => ?_) (fun j => ?_)
  · obtain ⟨hpos, hle⟩ := ApertureWindow.cycT_pos_le s T hβ (j := j + 1) (by omega)
    have hsq : 0 < cycT s T β (2 * (j + 1)) ^ 2 := lt_of_lt_of_le hpos hle
    have hg := aperture_gap s T hβ (2 * (j + 1)) (by omega)
    have hd : 0 < 1 + apTheta s T β ^ (2 * (j + 1)) := by
      have := pow_nonneg h0 (2 * (j + 1)); linarith
    rw [div_le_div_iff₀ hd hsq]
    linarith
  · obtain ⟨hpos, hle⟩ := ApertureWindow.cycT_pos_le s T hβ (j := j + 1) (by omega)
    have hsq : 0 < cycT s T β (2 * (j + 1)) ^ 2 := lt_of_lt_of_le hpos hle
    exact (div_le_one hsq).2 hle

end Slice

/-! ## 2. The fixed-diffraction statement -/

section Bridge

/-- **Fixed diffraction**: the aperture gap tends to a fixed physical mass `m > 0` uniformly in the zoom, with
the excited levels of a box of physical size `L` counted by `C L^d`. One statement: eventually in `β`, at the
physical side `n = 2^{kPhys L β + 2}` and in every direction, `cyc(kT_s, 2n) ≥ exp(−C L^d e^{−mL}) cyc(kT_s, n)²`,
for every `L ≥ 1`. -/
def FixedDiffraction (m C : ℝ) (d : ℕ) : Prop :=
  0 < m ∧ ∀ L : ℝ, 1 ≤ L → ∀ᶠ β in atTop, ∀ s : Fin 4,
    Real.exp (-(C * L ^ d * Real.exp (-(m * L)))) *
        cycT s (tr (Ls (2 ^ (kPhys L β + 2)) s) s) β (2 ^ (kPhys L β + 2)) ^ 2
      ≤ cycT s (tr (Ls (2 ^ (kPhys L β + 2)) s) s) β (2 * 2 ^ (kPhys L β + 2))

/-- **Fixed diffraction gives the kernel form of the far input** at every `L ≥ 1` with `C L^d e^{−mL} ≤ ε`. -/
theorem kernFar_of_fixedDiffraction {m C : ℝ} {d : ℕ} (h : FixedDiffraction m C d) {L ε : ℝ} (hL : 1 ≤ L)
    (hε : C * L ^ d * Real.exp (-(m * L)) ≤ ε) : GapAttack.KernFar L ε := by
  unfold GapAttack.KernFar
  filter_upwards [h.2 L hL] with β hβ s
  refine le_trans ?_ (hβ s)
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (sq_nonneg _)

/-- `C L^d e^{−mL} ≤ ε` eventually in `L`. -/
theorem eventually_poly_exp_le {m : ℝ} (hm : 0 < m) (C : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L in atTop, C * L ^ d * Real.exp (-(m * L)) ≤ ε := by
  have h1 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp (tendsto_id.const_mul_atTop hm)
  have h2 := h1.const_mul (C / m ^ d)
  rw [mul_zero] at h2
  have hmd : m ^ d ≠ 0 := pow_ne_zero _ hm.ne'
  have h3 : Tendsto (fun L : ℝ => C * L ^ d * Real.exp (-(m * L))) atTop (𝓝 0) := by
    refine h2.congr fun L => ?_
    simp only [Function.comp_apply, id_eq]
    rw [mul_pow, div_mul_eq_mul_div, div_eq_iff hmd]
    ring
  exact h3.eventually (Iic_mem_nhds hε)

/-- **Fixed diffraction gives the physical-side defect** at every large enough aperture. -/
theorem physDefect_of_fixedDiffraction {m C : ℝ} {d : ℕ} (h : FixedDiffraction m C d) :
    ∀ᶠ L in atTop, ApertureBridge.PhysDefect L (1 / 1000) := by
  filter_upwards [eventually_poly_exp_le h.1 C d (ε := 1 / 15000) (by norm_num), eventually_ge_atTop 1]
    with L hs hL
  have := GapAttack.physDefect_of_kernFar (kernFar_of_fixedDiffraction h hL hs)
  rwa [show (15 : ℝ) * (1 / 15000) = 1 / 1000 by norm_num] at this

/-- **Fixed diffraction gives the run seed**, the `hW` input. -/
theorem runSeed_of_fixedDiffraction {m C : ℝ} {d : ℕ} (h : FixedDiffraction m C d) : WDeltaRun.RunSeed 2 := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (physDefect_of_fixedDiffraction h)
  exact ApertureBridge.runSeed_of_physDefect (lt_of_lt_of_le one_pos (le_max_right L₀ 1))
    (hL₀ _ (le_max_left _ _))

/-- **The multiplicity reading in the eigenvalue model**: excited energies `E_i` in physical units on a cycle
of physical length `ℓ` (`r_{i+1} = e^{−E_i ℓ}` at length `1`), with weighted density of states
`Σ_i e^{−(E_i − m)ℓ} ≤ P`, give the defect at most `2 P e^{−mℓ}`. -/
theorem model_defect_le {k : ℕ} (E : Fin k → ℝ) {m ℓ P : ℝ}
    (hP : ∑ i, Real.exp (-((E i - m) * ℓ)) ≤ P) :
    2 * Real.log (ApertureTwo.trZ (Fin.cons 1 fun i => Real.exp (-(E i * ℓ))) 1)
        - Real.log (ApertureTwo.trZ (Fin.cons 1 fun i => Real.exp (-(E i * ℓ))) (2 * 1))
      ≤ 2 * (P * Real.exp (-(m * ℓ))) := by
  set r : Fin (k + 1) → ℝ := Fin.cons 1 fun i => Real.exp (-(E i * ℓ)) with hr
  have hr0 : r 0 = 1 := by simp [hr]
  have hrn : ∀ i, 0 ≤ r i := by
    intro i
    induction i using Fin.cases with
    | zero => simp [hr]
    | succ j => simp only [hr, Fin.cons_succ]; positivity
  have h := ApertureTwo.stepDefect_le r hr0 hrn 1
  have ht : ApertureTwo.tau r 1 ≤ P * Real.exp (-(m * ℓ)) := by
    unfold ApertureTwo.tau
    have e : ∀ i : Fin k, r i.succ ^ 1 = Real.exp (-((E i - m) * ℓ)) * Real.exp (-(m * ℓ)) := by
      intro i
      simp only [hr, Fin.cons_succ, pow_one, ← Real.exp_add]
      congr 1; ring
    simp only [e, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
  have hl : Real.log (1 + ApertureTwo.tau r 1) ≤ ApertureTwo.tau r 1 := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ApertureTwo.tau r 1)
      (by linarith [ApertureTwo.tau_nonneg r hrn 1])
    linarith
  linarith

end Bridge

/-! ## 3. Unit tests -/

section Tests

/-- **The model form of fixed diffraction**: the doubling defect `D L K` of the box of physical side `L` at
zoom `K` is at most `C L^d e^{−mL}` for every `L ≥ 1` and every `K`. -/
def ModelFD (D : ℝ → ℕ → ℝ) (m C : ℝ) (d : ℕ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ K : ℕ, D L K ≤ C * L ^ d * Real.exp (-(m * L))

/-- A defect bounded below by `δ e^{−M L}` along every `L ≥ 1` admits no `ModelFD` at any rate `m > M`. -/
theorem not_modelFD_of_lower {D : ℝ → ℕ → ℝ} {M m δ : ℝ} (hδ : 0 < δ) (hmM : M < m)
    (hlow : ∀ L : ℝ, 1 ≤ L → δ * Real.exp (-(M * L)) ≤ D L 1) (C : ℝ) (d : ℕ) : ¬ ModelFD D m C d := by
  intro h
  obtain ⟨L, hs, hL⟩ := ((eventually_poly_exp_le (sub_pos.2 hmM) C d (half_pos hδ)).and
    (eventually_ge_atTop (1 : ℝ))).exists
  have h1 := (hlow L hL).trans (h L hL 1)
  have e : C * L ^ d * Real.exp (-(m * L)) = C * L ^ d * Real.exp (-((m - M) * L)) * Real.exp (-(M * L)) := by
    have : Real.exp (-(m * L)) = Real.exp (-((m - M) * L)) * Real.exp (-(M * L)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [e] at h1
  have h2 := le_of_mul_le_mul_right h1 (Real.exp_pos _)
  linarith

/-! ### 2D `SU(2)` by characters -/

/-- The character sum of 2D `SU(2)` on the cylinder of area `A`, `c = κ A`: `Σ_{n ≥ 0} exp(−c((n+1)² − 1))`. -/
def ymZ (c : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-(c * (((n : ℝ) + 1) ^ 2 - 1)))

/-- The doubling defect of the box of side `L` (cycle of length `L`, area `L²`). -/
def ymD (κ : ℝ) (L : ℝ) (_K : ℕ) : ℝ := 2 * Real.log (ymZ (κ * L ^ 2)) - Real.log (ymZ (2 * (κ * L ^ 2)))

theorem ym_term_le {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Real.exp (-(c * (((n : ℝ) + 1 + 1) ^ 2 - 1))) ≤ Real.exp (-(3 * c)) * Real.exp (-c) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hc (mul_nonneg hn hn), mul_nonneg hc hn]

theorem ym_summable {c : ℝ} (hc : 0 < c) : Summable fun n : ℕ => Real.exp (-(c * (((n : ℝ) + 1) ^ 2 - 1))) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_)
    (summable_geometric_of_lt_one (Real.exp_pos (-c)).le (Real.exp_lt_one_iff.2 (by linarith)))
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hc.le (mul_nonneg hn hn)]

theorem ymZ_eq {c : ℝ} (hc : 0 < c) :
    ymZ c = 1 + ∑' n : ℕ, Real.exp (-(c * (((n : ℝ) + 1 + 1) ^ 2 - 1))) := by
  unfold ymZ
  rw [(ym_summable hc).tsum_eq_zero_add]
  congr 1
  · simp
  · congr 1; funext n; rw [Nat.cast_succ]

theorem ym_tail_le {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, Real.exp (-(c * (((n : ℝ) + 1 + 1) ^ 2 - 1))) ≤ Real.exp (-(3 * c)) * (1 - Real.exp (-c))⁻¹ := by
  have hq0 := (Real.exp_pos (-c)).le
  have hq1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-(3 * c)))
  rw [← tsum_geometric_of_lt_one hq0 hq1, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => ym_term_le hc.le n)
    (Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ym_term_le hc.le n) hs) hs

theorem ym_tail_nonneg (c : ℝ) : 0 ≤ ∑' n : ℕ, Real.exp (-(c * (((n : ℝ) + 1 + 1) ^ 2 - 1))) :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- **2D `SU(2)`: fixed diffraction holds at every rate `m`** (`d = 0`). -/
theorem ym_modelFD {κ : ℝ} (hκ : 0 < κ) (m : ℝ) :
    ModelFD (ymD κ) m (2 * Real.exp (m ^ 2 / (12 * κ)) * (1 - Real.exp (-κ))⁻¹) 0 := by
  intro L hL _
  have hL0 : 0 < L := by linarith
  have hc : 0 < κ * L ^ 2 := by positivity
  have hc2 : 0 < 2 * (κ * L ^ 2) := by positivity
  have hZ1 := ymZ_eq hc
  have hZ2 := ymZ_eq hc2
  have ht1 := ym_tail_le hc
  have ht0 := ym_tail_nonneg (κ * L ^ 2)
  have ht02 := ym_tail_nonneg (2 * (κ * L ^ 2))
  have hlog2 : 0 ≤ Real.log (ymZ (2 * (κ * L ^ 2))) := Real.log_nonneg (by rw [hZ2]; linarith)
  have hlog1 : Real.log (ymZ (κ * L ^ 2)) ≤ ymZ (κ * L ^ 2) - 1 :=
    Real.log_le_sub_one_of_pos (by rw [hZ1]; linarith)
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hq : Real.exp (-(κ * L ^ 2)) ≤ Real.exp (-κ) := Real.exp_le_exp.2 (by nlinarith)
  have hqk : Real.exp (-κ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hinv : (1 - Real.exp (-(κ * L ^ 2)))⁻¹ ≤ (1 - Real.exp (-κ))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have hexp : Real.exp (-(3 * (κ * L ^ 2))) ≤ Real.exp (m ^ 2 / (12 * κ)) * Real.exp (-(m * L)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h12 : 0 < 12 * κ := by positivity
    have hsq : 0 ≤ (6 * κ * L - m) ^ 2 := sq_nonneg _
    have hdiv : m ^ 2 / (12 * κ) * (12 * κ) = m ^ 2 := div_mul_cancel₀ _ h12.ne'
    have key : 0 ≤ 12 * κ * (3 * (κ * L ^ 2) + m ^ 2 / (12 * κ) - m * L) := by nlinarith [hsq, hdiv]
    have key' : 0 ≤ 3 * (κ * L ^ 2) + m ^ 2 / (12 * κ) - m * L := (mul_nonneg_iff_of_pos_left h12).1 key
    linarith
  unfold ymD
  have hpos : 0 ≤ (1 - Real.exp (-(κ * L ^ 2)))⁻¹ := inv_nonneg.2 (by linarith)
  calc 2 * Real.log (ymZ (κ * L ^ 2)) - Real.log (ymZ (2 * (κ * L ^ 2)))
      ≤ 2 * (Real.exp (-(3 * (κ * L ^ 2))) * (1 - Real.exp (-(κ * L ^ 2)))⁻¹) := by
        have := mul_le_mul_of_nonneg_left ht1 (show (0 : ℝ) ≤ 2 by norm_num)
        linarith
    _ ≤ 2 * ((Real.exp (m ^ 2 / (12 * κ)) * Real.exp (-(m * L))) * (1 - Real.exp (-κ))⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hexp hinv hpos (by positivity)) (by norm_num)
    _ = 2 * Real.exp (m ^ 2 / (12 * κ)) * (1 - Real.exp (-κ))⁻¹ * L ^ 0 * Real.exp (-(m * L)) := by ring

/-! ### 4D Gaussian fields in a lattice box -/

/-- The doubling defect of one oscillator, `q = e^{−ωℓ}`: `2 log Z(ℓ) − log Z(2ℓ)` with `Z(ℓ) = (1 − q)⁻¹`, the
trace `Σ_k q^k` of its transfer on the cycle of length `ℓ` (`oscZ_eq_tsum`). -/
def oscD (q : ℝ) : ℝ := 2 * Real.log ((1 - q)⁻¹) - Real.log ((1 - q ^ 2)⁻¹)

theorem oscZ_eq_tsum {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) : (1 - q)⁻¹ = ∑' k : ℕ, q ^ k :=
  (tsum_geometric_of_lt_one h0 h1).symm

theorem oscD_eq {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) : oscD q = Real.log ((1 + q) / (1 - q)) := by
  unfold oscD
  have ha : (1 - q) ≠ 0 := by linarith
  have hb : (1 + q) ≠ 0 := by linarith
  rw [Real.log_inv, Real.log_inv, show 1 - q ^ 2 = (1 - q) * (1 + q) by ring, Real.log_mul ha hb,
    Real.log_div hb ha]
  ring

theorem oscD_le {q q₀ : ℝ} (h0 : 0 ≤ q) (hq : q ≤ q₀) (h1 : q₀ < 1) : oscD q ≤ 2 * (1 - q₀)⁻¹ * q := by
  rw [oscD_eq h0 (hq.trans_lt h1)]
  have hp : 0 < 1 - q := by linarith
  have hlog := Real.log_le_sub_one_of_pos (x := (1 + q) / (1 - q)) (div_pos (by linarith) hp)
  have e : (1 + q) / (1 - q) - 1 = 2 * q / (1 - q) := by
    rw [div_sub_one hp.ne']; congr 1; ring
  have h2 : 2 * q / (1 - q) ≤ 2 * (1 - q₀)⁻¹ * q := by
    rw [div_le_iff₀ hp]
    have : (1 - q₀)⁻¹ * (1 - q) ≥ 1 := by
      rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]; linarith
    nlinarith
  linarith

theorem oscD_ge {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) : q ≤ oscD q := by
  rw [oscD_eq h0 h1]
  have hp : 0 < (1 + q) / (1 - q) := by apply div_pos <;> linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have e : 1 - ((1 + q) / (1 - q))⁻¹ = 2 * q / (1 + q) := by
    have hb : (1 + q) ≠ 0 := by linarith
    rw [inv_div, one_sub_div hb]; congr 1; ring
  have h2 : q ≤ 2 * q / (1 + q) := by rw [le_div_iff₀ (by linarith)]; nlinarith
  linarith

theorem oscD_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) : 0 ≤ oscD q := h0.trans (oscD_ge h0 h1)

/-- The lattice momentum of the Dirichlet mode `j ∈ {1, …, K}` in the box of side `L` with `K + 1` cells per
direction: `(2(K+1)/L) sin(π j/(2(K+1)))`. -/
def phat (L : ℝ) (K j : ℕ) : ℝ := 2 * ((K : ℝ) + 1) / L * Real.sin (π * j / (2 * ((K : ℝ) + 1)))

theorem phat_arg {K j : ℕ} (hj : j ≤ K) :
    0 ≤ π * j / (2 * ((K : ℝ) + 1)) ∧ π * j / (2 * ((K : ℝ) + 1)) ≤ π / 2 := by
  have hK : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by positivity
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hK]
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hjK Real.pi_pos.le]

theorem phat_ge {L : ℝ} (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) : 2 * (j : ℝ) / L ≤ phat L K j := by
  obtain ⟨h0, h1⟩ := phat_arg hj
  have hs := Real.mul_le_sin h0 h1
  have hc : 0 ≤ 2 * ((K : ℝ) + 1) / L := by positivity
  have hπ : π ≠ 0 := Real.pi_pos.ne'
  have hL' : L ≠ 0 := hL.ne'
  have hK' : (K : ℝ) + 1 ≠ 0 := by positivity
  have e : 2 * (j : ℝ) / L = 2 * ((K : ℝ) + 1) / L * (2 / π * (π * j / (2 * ((K : ℝ) + 1)))) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hs hc

theorem phat_le {L : ℝ} (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) : phat L K j ≤ π * j / L := by
  obtain ⟨h0, _⟩ := phat_arg hj
  have hs := Real.sin_le h0
  have hc : 0 ≤ 2 * ((K : ℝ) + 1) / L := by positivity
  have hL' : L ≠ 0 := hL.ne'
  have hK' : (K : ℝ) + 1 ≠ 0 := by positivity
  have e : π * (j : ℝ) / L = 2 * ((K : ℝ) + 1) / L * (π * j / (2 * ((K : ℝ) + 1))) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hs hc

theorem phat_nonneg {L : ℝ} (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) : 0 ≤ phat L K j :=
  le_trans (by positivity) (phat_ge hL hj)

/-- The Dirichlet modes of the box: `k ∈ {1, …, K}³`. DERIVED: `3` the spatial directions of a time
slice; `1` the lowest Dirichlet mode. -/
def box (K : ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset fun _ => Finset.Icc 1 K

/-- The frequency of the mode `k` of a field of mass `M` in the box of side `L` at zoom `K`.
DERIVED: `3` the spatial directions of a time slice, read at `0, 1, 2`; `2` the square. -/
def freq (M L : ℝ) (K : ℕ) (k : Fin 3 → ℕ) : ℝ :=
  Real.sqrt (M ^ 2 + (phat L K (k 0) ^ 2 + phat L K (k 1) ^ 2 + phat L K (k 2) ^ 2))

/-- **The Gaussian doubling defect**: one oscillator per mode, cycle of length `L`. -/
def gaussD (M L : ℝ) (K : ℕ) : ℝ := ∑ k ∈ box K, oscD (Real.exp (-(freq M L K k * L)))

theorem freq_nonneg (M L : ℝ) (K : ℕ) (k : Fin 3 → ℕ) : 0 ≤ freq M L K k := Real.sqrt_nonneg _

theorem gauss_q {M L : ℝ} (hL : 0 < L) {K : ℕ} (k : Fin 3 → ℕ) :
    0 ≤ Real.exp (-(freq M L K k * L)) ∧ Real.exp (-(freq M L K k * L)) ≤ 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by nlinarith [freq_nonneg M L K k])⟩

/-- The lowest half-wave `(1,1,1)` has `ω L ≤ M L + 2π`. -/
theorem freq_low_le {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L) {K : ℕ} (hK : 1 ≤ K) :
    freq M L K (fun _ => 1) * L ≤ M * L + 2 * π := by
  have hp := phat_le hL (K := K) (j := 1) hK
  have hp0 := phat_nonneg hL (K := K) (j := 1) hK
  simp only [Nat.cast_one, mul_one] at hp
  have hpL : 0 ≤ π / L := div_nonneg Real.pi_pos.le hL.le
  have hsq : phat L K 1 ^ 2 ≤ (π / L) ^ 2 := pow_le_pow_left₀ hp0 hp 2
  have hfr : freq M L K (fun _ => 1) ≤ M + 2 * π / L := by
    show Real.sqrt (M ^ 2 + (phat L K 1 ^ 2 + phat L K 1 ^ 2 + phat L K 1 ^ 2)) ≤ _
    have hy : 0 ≤ M + 2 * π / L := add_nonneg hM (div_nonneg (by linarith [Real.pi_pos]) hL.le)
    calc Real.sqrt (M ^ 2 + (phat L K 1 ^ 2 + phat L K 1 ^ 2 + phat L K 1 ^ 2))
        ≤ Real.sqrt ((M + 2 * π / L) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have e : (M + 2 * π / L) ^ 2 = M ^ 2 + 4 * M * (π / L) + 4 * (π / L) ^ 2 := by ring
          rw [e]
          nlinarith [mul_nonneg hM hpL]
      _ = M + 2 * π / L := Real.sqrt_sq hy
  calc freq M L K (fun _ => 1) * L ≤ (M + 2 * π / L) * L := mul_le_mul_of_nonneg_right hfr hL.le
    _ = M * L + 2 * π := by rw [add_mul, div_mul_cancel₀ _ hL.ne']

/-- The Gaussian defect is at least `e^{−2π} e^{−ML}` at every `L ≥ 1`, zoom `K = 1`. -/
theorem gaussD_lower {M L : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L) :
    Real.exp (-(2 * π)) * Real.exp (-(M * L)) ≤ gaussD M L 1 := by
  have hL0 : 0 < L := by linarith
  have hmem : (fun _ => 1 : Fin 3 → ℕ) ∈ box 1 := by
    simp [box]
  have hq : ∀ k, 0 ≤ oscD (Real.exp (-(freq M L 1 k * L))) := by
    intro k
    obtain ⟨h0, h1⟩ := gauss_q (M := M) hL0 (K := 1) k
    rcases h1.lt_or_eq with h1 | h1
    · exact oscD_nonneg h0 h1
    · rw [h1]; simp [oscD]
  have hone := Finset.single_le_sum (fun k _ => hq k) hmem
  have hfl := freq_low_le hM hL0 (K := 1) le_rfl
  have hqlow : Real.exp (-(2 * π)) * Real.exp (-(M * L)) ≤ Real.exp (-(freq M L 1 (fun _ => 1) * L)) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have hlt : Real.exp (-(freq M L 1 (fun _ => 1) * L)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hf : 0 < freq M L 1 (fun _ => 1) := by
      show 0 < Real.sqrt (M ^ 2 + (phat L 1 1 ^ 2 + phat L 1 1 ^ 2 + phat L 1 1 ^ 2))
      apply Real.sqrt_pos.2
      have h1 := phat_ge hL0 (K := 1) (j := 1) le_rfl
      have h2 : 0 < 2 * ((1 : ℕ) : ℝ) / L := div_pos (by norm_num) hL0
      nlinarith [sq_nonneg M, pow_pos (h2.trans_le h1) 2]
    have := mul_pos hf hL0
    linarith
  exact hqlow.trans ((oscD_ge (Real.exp_pos _).le hlt).trans hone)

/-- **4D massless Gaussian: fixed diffraction fails at every rate.** -/
theorem massless_not_modelFD {m : ℝ} (hm : 0 < m) (C : ℝ) (d : ℕ) : ¬ ModelFD (gaussD 0) m C d :=
  not_modelFD_of_lower (Real.exp_pos _) hm (fun _ hL => gaussD_lower le_rfl hL) C d

/-- **4D massive Gaussian: fixed diffraction fails at every rate above the mass.** -/
theorem massive_not_modelFD {M m : ℝ} (hM : 0 ≤ M) (hmM : M < m) (C : ℝ) (d : ℕ) :
    ¬ ModelFD (gaussD M) m C d :=
  not_modelFD_of_lower (Real.exp_pos _) hmM (fun _ hL => gaussD_lower hM hL) C d

/-- `λ M + ν(a + b + c) ≤ √(M² + a² + b² + c²)` for `ν = (1 − λ)/2`, since `λ² + 3ν² ≤ 1`. -/
theorem cs_split {M a b c lam : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) :
    lam * M + (1 - lam) / 2 * (a + b + c) ≤ Real.sqrt (M ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2)) := by
  have hν0 : 0 ≤ (1 - lam) / 2 := by linarith
  have hy : 0 ≤ lam * M + (1 - lam) / 2 * (a + b + c) :=
    add_nonneg (mul_nonneg hl0 hM) (mul_nonneg hν0 (by linarith))
  have hw : lam ^ 2 + 3 * ((1 - lam) / 2) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hl0 (sub_nonneg.2 hl1)]
  have hS : 0 ≤ M ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2) := by positivity
  have hcs : (lam * M + (1 - lam) / 2 * (a + b + c)) ^ 2
      ≤ (lam ^ 2 + 3 * ((1 - lam) / 2) ^ 2) * (M ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2)) := by
    nlinarith [sq_nonneg (lam * a - (1 - lam) / 2 * M), sq_nonneg (lam * b - (1 - lam) / 2 * M),
      sq_nonneg (lam * c - (1 - lam) / 2 * M), sq_nonneg ((1 - lam) / 2 * a - (1 - lam) / 2 * b),
      sq_nonneg ((1 - lam) / 2 * a - (1 - lam) / 2 * c), sq_nonneg ((1 - lam) / 2 * b - (1 - lam) / 2 * c)]
  have h2 : (lam * M + (1 - lam) / 2 * (a + b + c)) ^ 2 ≤ M ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2) :=
    hcs.trans (by simpa using mul_le_mul_of_nonneg_right hw hS)
  calc lam * M + (1 - lam) / 2 * (a + b + c)
      = Real.sqrt ((lam * M + (1 - lam) / 2 * (a + b + c)) ^ 2) := (Real.sqrt_sq hy).symm
    _ ≤ _ := Real.sqrt_le_sqrt h2

/-- Cauchy–Schwarz split of the frequency: `ω ≥ λ M + ν (p̂₀ + p̂₁ + p̂₂)` with `ν = (1 − λ)/2`. -/
theorem freq_ge {M L : ℝ} (hM : 0 ≤ M) {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {K : ℕ} (k : Fin 3 → ℕ)
    (ha : ∀ i, 0 ≤ phat L K (k i)) :
    lam * M + (1 - lam) / 2 * (phat L K (k 0) + phat L K (k 1) + phat L K (k 2)) ≤ freq M L K k :=
  cs_split hM (ha 0) (ha 1) (ha 2) hl0 hl1

theorem geom_finset_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (s : Finset ℕ) : ∑ j ∈ s, r ^ j ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum s (fun j _ => pow_nonneg h0 j)

/-- **4D massive Gaussian of mass `M > 0`: fixed diffraction holds at every rate `λ M`, `0 < λ < 1`**
(`d = 0`), uniformly in the zoom `K`. -/
theorem massive_modelFD {M : ℝ} (hM : 0 < M) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ModelFD (gaussD M) (lam * M)
      (2 * (1 - Real.exp (-(lam * M)))⁻¹ * ((1 - Real.exp (-(1 - lam))) ^ 3)⁻¹) 0 := by
  intro L hL K
  have hL0 : 0 < L := by linarith
  set q₀ := Real.exp (-(lam * M)) with hq₀
  have hq₀1 : q₀ < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  set r := Real.exp (-(1 - lam)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hmode : ∀ k ∈ box K, Real.exp (-(freq M L K k * L))
      ≤ Real.exp (-(lam * M * L)) * ∏ i, r ^ (k i) := by
    intro k hk
    have hki : ∀ i, k i ≤ K := fun i => (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)).2
    have ha : ∀ i, 0 ≤ phat L K (k i) := fun i => phat_nonneg hL0 (hki i)
    have hf := freq_ge hM.le hl0.le hl1.le k ha
    have hg0 := phat_ge hL0 (hki 0)
    have hg1 := phat_ge hL0 (hki 1)
    have hg2 := phat_ge hL0 (hki 2)
    have hprod : ∏ i, r ^ (k i) = Real.exp (-((1 - lam) * ((k 0 : ℝ) + k 1 + k 2))) := by
      rw [Fin.prod_univ_three, hr, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
        ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    rw [hprod, ← Real.exp_add, Real.exp_le_exp]
    have hν : 0 ≤ (1 - lam) / 2 := by linarith
    have hLne : L ≠ 0 := hL0.ne'
    have hsum : (1 - lam) / 2 * (2 * (k 0 : ℝ) / L + 2 * (k 1 : ℝ) / L + 2 * (k 2 : ℝ) / L) * L
        = (1 - lam) * ((k 0 : ℝ) + k 1 + k 2) := by field_simp
    have hmono : (1 - lam) / 2 * (2 * (k 0 : ℝ) / L + 2 * (k 1 : ℝ) / L + 2 * (k 2 : ℝ) / L)
        ≤ (1 - lam) / 2 * (phat L K (k 0) + phat L K (k 1) + phat L K (k 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hν
    have hfL : (lam * M + (1 - lam) / 2 * (2 * (k 0 : ℝ) / L + 2 * (k 1 : ℝ) / L + 2 * (k 2 : ℝ) / L)) * L
        ≤ freq M L K k * L := mul_le_mul_of_nonneg_right (by linarith) hL0.le
    have e2 : (lam * M + (1 - lam) / 2 * (2 * (k 0 : ℝ) / L + 2 * (k 1 : ℝ) / L + 2 * (k 2 : ℝ) / L)) * L
        = lam * M * L + (1 - lam) * ((k 0 : ℝ) + k 1 + k 2) := by rw [add_mul, hsum]
    linarith
  have hqle : ∀ k ∈ box K, Real.exp (-(freq M L K k * L)) ≤ q₀ := by
    intro k hk
    have hki : ∀ i, k i ≤ K := fun i => (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)).2
    have ha : ∀ i, 0 ≤ phat L K (k i) := fun i => phat_nonneg hL0 (hki i)
    rw [hq₀, Real.exp_le_exp]
    have hf := freq_ge hM.le hl0.le hl1.le k ha
    have hν : 0 ≤ (1 - lam) / 2 * (phat L K (k 0) + phat L K (k 1) + phat L K (k 2)) := by
      have := ha 0; have := ha 1; have := ha 2
      apply mul_nonneg (by linarith); linarith
    have hlm : lam * M ≤ freq M L K k := by linarith
    nlinarith [mul_nonneg hl0.le hM.le, freq_nonneg M L K k]
  have hsum : ∑ k ∈ box K, ∏ i, r ^ (k i) = (∑ j ∈ Finset.Icc 1 K, r ^ j) ^ 3 := by
    have h : ∏ _i : Fin 3, ∑ j ∈ Finset.Icc 1 K, r ^ j
        = ∑ x ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 K), ∏ i, r ^ (x i) :=
      Finset.prod_univ_sum (fun _ : Fin 3 => Finset.Icc 1 K) (fun _ j => r ^ j)
    unfold box
    rw [← h, Fin.prod_const]
  have hgeo := geom_finset_le hr0 hr1 (Finset.Icc 1 K)
  have hS0 : 0 ≤ ∑ j ∈ Finset.Icc 1 K, r ^ j := Finset.sum_nonneg fun j _ => pow_nonneg hr0 j
  have hcube : (∑ j ∈ Finset.Icc 1 K, r ^ j) ^ 3 ≤ ((1 - r) ^ 3)⁻¹ := by
    rw [← inv_pow]; exact pow_le_pow_left₀ hS0 hgeo 3
  have hq0pos : 0 < 1 - q₀ := by linarith
  have hc0 : 0 ≤ 2 * (1 - q₀)⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.2 hq0pos.le)
  unfold gaussD
  calc ∑ k ∈ box K, oscD (Real.exp (-(freq M L K k * L)))
      ≤ ∑ k ∈ box K, 2 * (1 - q₀)⁻¹ * (Real.exp (-(lam * M * L)) * ∏ i, r ^ (k i)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine (oscD_le (Real.exp_pos _).le (hqle k hk) hq₀1).trans ?_
        exact mul_le_mul_of_nonneg_left (hmode k hk) hc0
    _ = 2 * (1 - q₀)⁻¹ * Real.exp (-(lam * M * L)) * (∑ j ∈ Finset.Icc 1 K, r ^ j) ^ 3 := by
        rw [← hsum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 2 * (1 - q₀)⁻¹ * Real.exp (-(lam * M * L)) * ((1 - r) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hcube (mul_nonneg hc0 (Real.exp_pos _).le)
    _ = 2 * (1 - q₀)⁻¹ * ((1 - r) ^ 3)⁻¹ * L ^ 0 * Real.exp (-(lam * M * L)) := by ring

end Tests

end MassGap.ApertureGap

#print axioms MassGap.ApertureGap.crossRatio_of_bounds
#print axioms MassGap.ApertureGap.crossRatio_conv
#print axioms MassGap.ApertureGap.crossRatio_iter
#print axioms MassGap.ApertureGap.cyc_double_ge
#print axioms MassGap.ApertureGap.aperture_gap
#print axioms MassGap.ApertureGap.aperture_gap_tendsto
#print axioms MassGap.ApertureGap.kernFar_of_fixedDiffraction
#print axioms MassGap.ApertureGap.physDefect_of_fixedDiffraction
#print axioms MassGap.ApertureGap.runSeed_of_fixedDiffraction
#print axioms MassGap.ApertureGap.model_defect_le
#print axioms MassGap.ApertureGap.ym_modelFD
#print axioms MassGap.ApertureGap.massless_not_modelFD
#print axioms MassGap.ApertureGap.massive_not_modelFD
#print axioms MassGap.ApertureGap.massive_modelFD
