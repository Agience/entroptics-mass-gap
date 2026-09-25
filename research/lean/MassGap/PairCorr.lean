import Mathlib
import MassGap.BoxGap
import MassGap.HeatBathLocal

noncomputable section

/-!
# MassGap.PairCorr — the two-link correlation is linear in the coupling

## What it gives

1. **Haar integrals on `SU(N)`.** `integrable_su`, `integral_le_const`, `const_le_integral`,
   `integral_pos_of_pos`, `continuous_param` (a Haar integral of a jointly continuous function is
   continuous in the parameter) and `integral_three` (linearity on three continuous terms).
2. **The fibre correlation bound.** `corr_pt` and `fibre_corr_le`: on `SU(N) × SU(N)` with the
   product Haar measure, a weight `w(h, g)` and two functions `p(g)`, `q(h)`, all between `m₀` and
   `κ m₀`, and `a` of zero `q`-mean, have `∫∫ a(h) b(g) w ≤ ((κ² − 1)κ/2)(∫ a² q + ∫ b² p)`. The
   product weight `p(g)q(h)/Z` carries no correlation, and `|wZ − pq| ≤ (κ² − 1) pq` pointwise.
   `fibre_corr_config` applies it with `p`, `q` the two marginals of `w`.
3. **The two-link heat bath.** `heatAvg2 bd β l m f W`: the average of `f` over the variables at
   `l` and `m` with the Wilson weight, the other links held at `W`. It reads neither `l` nor `m`
   (`heatAvg2_update_l`, `heatAvg2_update_m`), fixes every function reading neither
   (`heatAvg2_of_readsNot`), and `f − heatAvg2 f` has vanishing two-link numerator
   (`heatNum2_sub_self`). `heatLift2` and `twoCondExp` carry it to the periodic gauge-invariant
   observables (`heatLift2_mem`, through `heatAvg2_gauge`); the result is fixed by the one-link
   conditional expectations at `l` and at `m` (`torusCondExp_twoCondExp_l`,
   `torusCondExp_twoCondExp_m`).
4. **The two-link weight.** `pairLocSum`, `pairRestSum`: the action of the plaquettes visiting
   `l` or `m`, and of the rest. On the periodic lattice at most `256` plaquettes visit a link
   (`card_visit_le`) at every extent, so `0 ≤ pairLocSum` (`pairLocSum_nonneg`) and
   `pairLocSum ≤ 1024` (`pairLocSum_le_torus`), and on
   the fibre of `(l, m)` the weight lies in `[e^{−1024β} E, E]` for `β ≥ 0`, `E` a constant of the
   frozen links (`wt_pair_bounds`).
5. **The Gibbs correlation bound.** `fibre_corr_config` is `fibre_corr_le` on the fibre of `(l, m)`
   over a frozen `W`; `gibbs_corr_le` integrates it over `W` (`HeatBathErgodic.integral_havg`).
   `exp_cube_sub_le`: `(e^{2t} − 1)e^t ≤ (45/8) t` for `0 ≤ 3t ≤ 1`. `pairCorr_twoCond`: for
   `0 ≤ β`, `3072 β ≤ 1` and any two distinct links, with `y = twoCondExp x`,
   `⟨E_l(x − y), E_m(x − y)⟩ ≤ 5760 β (‖E_l(x − y)‖² + ‖E_m(x − y)‖²)/2` in `torusForm`, at every
   extent.
6. **The result.** `pairDelta β j l m = 5760 β` on the neighbours `HeatBathLocal.nbT j l` (at most
   `21`), `0` off them; it is a defect matrix of row and column sums at most `120960 β`
   (`pairDelta_defect`). Pairs sharing no plaquette take `y = E_l E_m x` and have correlation `0`
   (`BoxGap.corr_zero_of_comm`, `HeatBath.torusCondExp_comm`). `pairCorrLinear_holds`:
   `BoxGap.PairCorrLinear hN 120960 (1/5760)` for every `N ≠ 0`. `boxPatchGap_small`:
   `BoxPatch.BoxPatchGap hN β 80 (1 − 120960 β)` for `0 ≤ β ≤ 1/241920`, and `boxPatchGap_at`:
   `BoxPatch.BoxPatchGap hN (1/241920) 80 (1/2)`.

## Scope

Every constant is uniform in the extent index `j` and in `N`: the only volume-dependent quantities,
the weight of the plaquettes not visiting `l` or `m`, cancel between the fibre weight and its
marginals. The constants are explicit and not optimised; the coupling range `β ≤ 1/241920` is a
small-coupling range only.
-/

namespace MassGap.PairCorr

open MeasureTheory
open MassGap.HeatBath MassGap.HeatBathErgodic MassGap.KnabeCriterion MassGap.BoxGap
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.PeriodicState (torusObs)
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity)

/-! ## 1. Haar integrals on `SU(N)` -/

section Haar

variable {N : ℕ}

/-- A continuous function on `SU(N)` is Haar integrable (`HeatBath.exists_abs_le`,
`HeatBath.integrable_of_abs_le`).

DERIVED: no numeral. -/
theorem integrable_su {φ : SU N → ℝ} (hφ : Continuous φ) : Integrable φ (probHaar (SU N)) := by
  obtain ⟨C, hC⟩ := exists_abs_le hφ
  exact integrable_of_abs_le _ hφ.measurable hC

#print axioms integrable_su

/-- A continuous function below a constant has Haar integral below it.

DERIVED: no numeral. -/
theorem integral_le_const {φ : SU N → ℝ} (hφ : Continuous φ) {c : ℝ} (h : ∀ x, φ x ≤ c) :
    ∫ x, φ x ∂(probHaar (SU N)) ≤ c := by
  have h1 := integral_mono (integrable_su hφ) (integrable_const c) h
  rwa [integral_const, probReal_univ, one_smul] at h1

#print axioms integral_le_const

/-- A continuous function above a constant has Haar integral above it.

DERIVED: no numeral. -/
theorem const_le_integral {φ : SU N → ℝ} (hφ : Continuous φ) {c : ℝ} (h : ∀ x, c ≤ φ x) :
    c ≤ ∫ x, φ x ∂(probHaar (SU N)) := by
  have h1 := integral_mono (integrable_const c) (integrable_su hφ) h
  rwa [integral_const, probReal_univ, one_smul] at h1

#print axioms const_le_integral

/-- A positive continuous function has positive Haar integral.

DERIVED: `0` is the sign asserted. -/
theorem integral_pos_of_pos {φ : SU N → ℝ} (hφ : Continuous φ) (hpos : ∀ x, 0 < φ x) :
    0 < ∫ x, φ x ∂(probHaar (SU N)) := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) (integrable_su hφ)]
  have hsupp : Function.support φ = Set.univ :=
    Set.eq_univ_of_forall (fun x => Function.mem_support.mpr (hpos x).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms integral_pos_of_pos

/-- **A Haar integral in one variable of a jointly continuous function is continuous in the other**
(`continuous_of_dominated`, the bound a constant by compactness).

DERIVED: `1` and `2` in `z.1`, `z.2` are the projections of the pair, not numbers. -/
theorem continuous_param {F : SU N → SU N → ℝ}
    (hF : Continuous (fun z : SU N × SU N => F z.1 z.2)) :
    Continuous (fun h => ∫ g, F h g ∂(probHaar (SU N))) := by
  obtain ⟨C, hC⟩ := exists_abs_le hF
  refine continuous_of_dominated (bound := fun _ => C) (fun h => ?_) (fun h => ?_)
    (integrable_const C) ?_
  · exact (hF.comp (continuous_const.prodMk continuous_id :
      Continuous fun g : SU N => (h, g))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun g => by rw [Real.norm_eq_abs]; exact hC (h, g))
  · exact Filter.Eventually.of_forall (fun g => hF.comp (continuous_id.prodMk continuous_const :
      Continuous fun h : SU N => (h, g)))

#print axioms continuous_param

/-- **Linearity on three continuous terms**:
`∫ (c₁ f₁ + c₂ f₂ + c₃ f₃) = c₁ ∫ f₁ + c₂ ∫ f₂ + c₃ ∫ f₃` (`integral_add`, `integral_const_mul`).

DERIVED: no numeral; the subscripts `₁`, `₂`, `₃` are names. -/
theorem integral_three {f₁ f₂ f₃ : SU N → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous f₃) (c₁ c₂ c₃ : ℝ) :
    ∫ x, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) ∂(probHaar (SU N))
      = c₁ * ∫ x, f₁ x ∂(probHaar (SU N)) + c₂ * ∫ x, f₂ x ∂(probHaar (SU N))
        + c₃ * ∫ x, f₃ x ∂(probHaar (SU N)) := by
  have i₁ : Integrable (fun x => c₁ * f₁ x) (probHaar (SU N)) :=
    integrable_su (continuous_const.mul h₁)
  have i₂ : Integrable (fun x => c₂ * f₂ x) (probHaar (SU N)) :=
    integrable_su (continuous_const.mul h₂)
  have i₃ : Integrable (fun x => c₃ * f₃ x) (probHaar (SU N)) :=
    integrable_su (continuous_const.mul h₃)
  have i₁₂ : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x) (probHaar (SU N)) :=
    integrable_su ((continuous_const.mul h₁).add (continuous_const.mul h₂))
  rw [integral_add i₁₂ i₃, integral_add i₁ i₂, integral_const_mul, integral_const_mul,
    integral_const_mul]

#print axioms integral_three

end Haar

/-! ## 2. The fibre correlation bound -/

section Fibre

variable {N : ℕ}

/-- **The pointwise comparison with the product weight.** For `0 < m₀`, `1 ≤ κ` and `w`, `p`, `q`,
`Z` in `[m₀, κ m₀]`:
`a b w ≤ (a q/Z)(b p) + ((κ² − 1)/(2Z))(a² q) p + ((κ² − 1)/(2Z)) q (b² p)`. From
`|wZ − pq| ≤ κ²m₀² − m₀² ≤ (κ² − 1) pq` and `|ab| ≤ (a² + b²)/2`, then division by `Z`.

DERIVED: `0` is the sign of `m₀`; `1` is the least `κ` and the `1` of `κ² − 1`; `2` is the square
and the halving of `|ab| ≤ (a² + b²)/2`. -/
theorem corr_pt (a b : ℝ) {w p q Z m₀ κ : ℝ} (hm₀ : 0 < m₀) (hκ : 1 ≤ κ)
    (hw0 : m₀ ≤ w) (hw1 : w ≤ κ * m₀) (hp0 : m₀ ≤ p) (hp1 : p ≤ κ * m₀)
    (hq0 : m₀ ≤ q) (hq1 : q ≤ κ * m₀) (hZ0 : m₀ ≤ Z) (hZ1 : Z ≤ κ * m₀) :
    a * b * w ≤ a * q / Z * (b * p) + (κ ^ 2 - 1) / (2 * Z) * (a ^ 2 * q) * p
      + (κ ^ 2 - 1) / (2 * Z) * q * (b ^ 2 * p) := by
  have hZpos : 0 < Z := lt_of_lt_of_le hm₀ hZ0
  have hp0' : 0 ≤ p := le_trans hm₀.le hp0
  have hq0' : 0 ≤ q := le_trans hm₀.le hq0
  have hw0' : 0 ≤ w := le_trans hm₀.le hw0
  have hkm : 0 ≤ κ * m₀ := mul_nonneg (by linarith) hm₀.le
  have hε : 0 ≤ κ ^ 2 - 1 := by nlinarith
  have hpq0 : m₀ * m₀ ≤ p * q := mul_le_mul hp0 hq0 hm₀.le hp0'
  have hpq1 : p * q ≤ (κ * m₀) * (κ * m₀) := mul_le_mul hp1 hq1 hq0' hkm
  have hwZ0 : m₀ * m₀ ≤ w * Z := mul_le_mul hw0 hZ0 hm₀.le hw0'
  have hwZ1 : w * Z ≤ (κ * m₀) * (κ * m₀) := mul_le_mul hw1 hZ1 hZpos.le hkm
  have hεpq : (κ ^ 2 - 1) * (m₀ * m₀) ≤ (κ ^ 2 - 1) * (p * q) :=
    mul_le_mul_of_nonneg_left hpq0 hε
  have hs1 : w * Z - p * q ≤ (κ ^ 2 - 1) * (p * q) := by linarith
  have hs2 : -((κ ^ 2 - 1) * (p * q)) ≤ w * Z - p * q := by linarith
  have hab1 : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have hab2 : -(a * b) ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a + b)]
  have hX : 0 ≤ (κ ^ 2 - 1) * (p * q) := mul_nonneg hε (mul_nonneg hp0' hq0')
  have hcross : a * b * (w * Z - p * q) ≤ (a ^ 2 + b ^ 2) / 2 * ((κ ^ 2 - 1) * (p * q)) := by
    rcases le_total 0 (a * b) with hab | hab
    · calc a * b * (w * Z - p * q) ≤ a * b * ((κ ^ 2 - 1) * (p * q)) :=
            mul_le_mul_of_nonneg_left hs1 hab
        _ ≤ (a ^ 2 + b ^ 2) / 2 * ((κ ^ 2 - 1) * (p * q)) :=
            mul_le_mul_of_nonneg_right hab1 hX
    · calc a * b * (w * Z - p * q) ≤ a * b * (-((κ ^ 2 - 1) * (p * q))) :=
            mul_le_mul_of_nonpos_left hs2 hab
        _ = -(a * b) * ((κ ^ 2 - 1) * (p * q)) := by ring
        _ ≤ (a ^ 2 + b ^ 2) / 2 * ((κ ^ 2 - 1) * (p * q)) :=
            mul_le_mul_of_nonneg_right hab2 hX
  have hkey : a * b * w * Z
      ≤ a * b * (p * q) + (a ^ 2 + b ^ 2) / 2 * ((κ ^ 2 - 1) * (p * q)) := by
    linarith
  have hR : a * q / Z * (b * p) + (κ ^ 2 - 1) / (2 * Z) * (a ^ 2 * q) * p
      + (κ ^ 2 - 1) / (2 * Z) * q * (b ^ 2 * p)
      = (a * b * (p * q) + (a ^ 2 + b ^ 2) / 2 * ((κ ^ 2 - 1) * (p * q))) / Z := by
    ring
  rw [hR, le_div_iff₀ hZpos]
  exact hkey

#print axioms corr_pt

/-- **THE FIBRE CORRELATION BOUND.** On `SU(N) × SU(N)` with the product Haar measure, let `w` be
jointly continuous with `m₀ ≤ w ≤ κ m₀` (`0 < m₀`, `1 ≤ κ`), and `p`, `q` continuous in the same
range (the marginals of `w` in the application), `a`, `b` continuous with `∫ a q = 0`. Then

    ∫∫ a(h) b(g) w(h, g) ≤ ((κ² − 1) κ / 2) (∫ a² q + ∫ b² p).

`corr_pt` pointwise with `Z = ∫ q`; the product term integrates to `(∫ a q)(∫ b p)/Z = 0`, the two
remaining terms to `((κ² − 1)/2)((∫ p / Z) ∫ a² q + ∫ b² p)`, and `∫ p / Z ≤ κ`.

DERIVED: `0` is the sign of `m₀` and the vanishing mean; `1` is the least `κ` and the `1` of
`κ² − 1`; `2` is the square and the halving; `1`, `2` in `z.1`, `z.2` are projections. -/
theorem fibre_corr_le {a b p q : SU N → ℝ} {w : SU N → SU N → ℝ} {m₀ κ : ℝ}
    (ha : Continuous a) (hb : Continuous b) (hp : Continuous p) (hq : Continuous q)
    (hw : Continuous (fun z : SU N × SU N => w z.1 z.2)) (hm₀ : 0 < m₀) (hκ : 1 ≤ κ)
    (hw0 : ∀ h g, m₀ ≤ w h g) (hw1 : ∀ h g, w h g ≤ κ * m₀)
    (hp0 : ∀ g, m₀ ≤ p g) (hp1 : ∀ g, p g ≤ κ * m₀)
    (hq0 : ∀ h, m₀ ≤ q h) (hq1 : ∀ h, q h ≤ κ * m₀)
    (hzero : ∫ h, a h * q h ∂(probHaar (SU N)) = 0) :
    ∫ h, ∫ g, a h * b g * w h g ∂(probHaar (SU N)) ∂(probHaar (SU N))
      ≤ (κ ^ 2 - 1) * κ / 2
        * (∫ h, a h ^ 2 * q h ∂(probHaar (SU N)) + ∫ g, b g ^ 2 * p g ∂(probHaar (SU N))) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∫ h, q h ∂(probHaar (SU N)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∫ g, p g ∂(probHaar (SU N)) := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ B : ℝ, B = ∫ g, b g * p g ∂(probHaar (SU N)) := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B : ℝ, B = ∫ g, b g ^ 2 * p g ∂(probHaar (SU N)) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : ℝ, A = ∫ h, a h ^ 2 * q h ∂(probHaar (SU N)) := ⟨_, rfl⟩
  have hZ0 : m₀ ≤ Z := by rw [hZ]; exact const_le_integral hq hq0
  have hZ1 : Z ≤ κ * m₀ := by rw [hZ]; exact integral_le_const hq hq1
  have hP1 : P ≤ κ * m₀ := by rw [hP]; exact integral_le_const hp hp1
  have hZpos : 0 < Z := lt_of_lt_of_le hm₀ hZ0
  have hε : 0 ≤ κ ^ 2 - 1 := by nlinarith
  have hA2n : 0 ≤ A2 := by
    rw [hA2]
    exact integral_nonneg (fun h => mul_nonneg (sq_nonneg _) (le_trans hm₀.le (hq0 h)))
  have hB2n : 0 ≤ B2 := by
    rw [hB2]
    exact integral_nonneg (fun g => mul_nonneg (sq_nonneg _) (le_trans hm₀.le (hp0 g)))
  -- the pointwise bound
  have key : ∀ h g, a h * b g * w h g ≤ a h * q h / Z * (b g * p g)
      + (κ ^ 2 - 1) / (2 * Z) * (a h ^ 2 * q h) * p g
      + (κ ^ 2 - 1) / (2 * Z) * q h * (b g ^ 2 * p g) :=
    fun h g => corr_pt (a h) (b g) hm₀ hκ (hw0 h g) (hw1 h g) (hp0 g) (hp1 g) (hq0 h) (hq1 h)
      hZ0 hZ1
  have hwc : ∀ h, Continuous (w h) := fun h =>
    hw.comp (continuous_const.prodMk continuous_id : Continuous fun g : SU N => (h, g))
  -- the inner integrals
  have hin : ∀ h, ∫ g, a h * b g * w h g ∂(probHaar (SU N))
      ≤ B1 / Z * (a h * q h) + (κ ^ 2 - 1) * P / (2 * Z) * (a h ^ 2 * q h)
        + (κ ^ 2 - 1) * B2 / (2 * Z) * q h := by
    intro h
    have hl : Continuous (fun g => a h * b g * w h g) := (continuous_const.mul hb).mul (hwc h)
    have hr : Continuous (fun g => a h * q h / Z * (b g * p g)
        + (κ ^ 2 - 1) / (2 * Z) * (a h ^ 2 * q h) * p g
        + (κ ^ 2 - 1) / (2 * Z) * q h * (b g ^ 2 * p g)) :=
      ((continuous_const.mul (hb.mul hp)).add (continuous_const.mul hp)).add
        (continuous_const.mul ((hb.pow 2).mul hp))
    calc ∫ g, a h * b g * w h g ∂(probHaar (SU N))
        ≤ ∫ g, (a h * q h / Z * (b g * p g) + (κ ^ 2 - 1) / (2 * Z) * (a h ^ 2 * q h) * p g
            + (κ ^ 2 - 1) / (2 * Z) * q h * (b g ^ 2 * p g)) ∂(probHaar (SU N)) :=
          integral_mono (integrable_su hl) (integrable_su hr) (fun g => key h g)
      _ = a h * q h / Z * B1 + (κ ^ 2 - 1) / (2 * Z) * (a h ^ 2 * q h) * P
            + (κ ^ 2 - 1) / (2 * Z) * q h * B2 := by
          rw [hB1, hP, hB2]
          exact integral_three (hb.mul hp) hp ((hb.pow 2).mul hp) _ _ _
      _ = B1 / Z * (a h * q h) + (κ ^ 2 - 1) * P / (2 * Z) * (a h ^ 2 * q h)
            + (κ ^ 2 - 1) * B2 / (2 * Z) * q h := by ring
  -- the outer integral
  have hlo : Continuous (fun h => ∫ g, a h * b g * w h g ∂(probHaar (SU N))) :=
    continuous_param (F := fun h g => a h * b g * w h g)
      (((ha.comp continuous_fst).mul (hb.comp continuous_snd)).mul hw)
  have hro : Continuous (fun h => B1 / Z * (a h * q h) + (κ ^ 2 - 1) * P / (2 * Z) * (a h ^ 2 * q h)
      + (κ ^ 2 - 1) * B2 / (2 * Z) * q h) :=
    ((continuous_const.mul (ha.mul hq)).add (continuous_const.mul ((ha.pow 2).mul hq))).add
      (continuous_const.mul hq)
  have hout := integral_mono (integrable_su hlo) (integrable_su hro) hin
  have e3 : (∫ h, (B1 / Z * (a h * q h) + (κ ^ 2 - 1) * P / (2 * Z) * (a h ^ 2 * q h)
      + (κ ^ 2 - 1) * B2 / (2 * Z) * q h) ∂(probHaar (SU N)))
      = B1 / Z * ∫ h, a h * q h ∂(probHaar (SU N))
        + (κ ^ 2 - 1) * P / (2 * Z) * ∫ h, a h ^ 2 * q h ∂(probHaar (SU N))
        + (κ ^ 2 - 1) * B2 / (2 * Z) * ∫ h, q h ∂(probHaar (SU N)) :=
    integral_three (ha.mul hq) ((ha.pow 2).mul hq) hq _ _ _
  rw [e3, hzero, ← hA2, ← hZ, mul_zero, zero_add] at hout
  rw [← hA2, ← hB2]
  refine le_trans hout ?_
  have hPZ : P / Z ≤ κ := by
    rw [div_le_iff₀ hZpos]
    linarith [mul_le_mul_of_nonneg_left hZ0 (by linarith : (0 : ℝ) ≤ κ)]
  have t1 : (κ ^ 2 - 1) * P / (2 * Z) * A2 = (κ ^ 2 - 1) * A2 / 2 * (P / Z) := by ring
  have t2 : (κ ^ 2 - 1) * B2 / (2 * Z) * Z = (κ ^ 2 - 1) * B2 / 2 := by
    rw [show (κ ^ 2 - 1) * B2 / (2 * Z) * Z = (κ ^ 2 - 1) * B2 / 2 * (Z / Z) by ring,
      div_self hZpos.ne', mul_one]
  have t3 : (κ ^ 2 - 1) * A2 / 2 * (P / Z) ≤ (κ ^ 2 - 1) * A2 / 2 * κ :=
    mul_le_mul_of_nonneg_left hPZ (div_nonneg (mul_nonneg hε hA2n) (by norm_num))
  have t4 : (κ ^ 2 - 1) * B2 / 2 ≤ (κ ^ 2 - 1) * B2 / 2 * κ :=
    le_mul_of_one_le_right (div_nonneg (mul_nonneg hε hB2n) (by norm_num)) hκ
  rw [t1, t2]
  calc (κ ^ 2 - 1) * A2 / 2 * (P / Z) + (κ ^ 2 - 1) * B2 / 2
      ≤ (κ ^ 2 - 1) * A2 / 2 * κ + (κ ^ 2 - 1) * B2 / 2 * κ := add_le_add t3 t4
    _ = (κ ^ 2 - 1) * κ / 2 * (A2 + B2) := by ring

#print axioms fibre_corr_le

end Fibre

/-! ## 3. The two-link heat bath -/

section TwoLink

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- **The two-link numerator**: `∫ h, ∫ g, f(W[m ↦ h][l ↦ g]) wt(W[m ↦ h][l ↦ g])`, the Haar
average at `m` of the Haar average at `l` (`HeatBathErgodic.havg`).

DERIVED: no numeral. -/
def heatNum2 (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : ℝ :=
  havg m (havg l (fun V => f V * wt bd β V)) W

/-- **The two-link normalisation**: `∫ h, ∫ g, wt(W[m ↦ h][l ↦ g])`.

DERIVED: no numeral. -/
def heatPart2 (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk) (W : Lk → SU N) : ℝ :=
  havg m (havg l (wt (N := N) bd β)) W

/-- **The two-link heat bath**: the average of `f` over the variables at `l` and `m` with the
Wilson weight, the other links held at `W`: `heatNum2 / heatPart2`.

DERIVED: no numeral. -/
def heatAvg2 (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : ℝ :=
  heatNum2 bd β l m f W / heatPart2 bd β l m W

/-- The Haar average of a non-negative function is non-negative.

DERIVED: `0` is the sign. -/
theorem havg_nonneg (l : Lk) {φ : (Lk → SU N) → ℝ} (hφ : ∀ V, 0 ≤ φ V) (W : Lk → SU N) :
    0 ≤ havg l φ W :=
  integral_nonneg (fun g => hφ _)

#print axioms havg_nonneg

/-- The two-link normalisation is positive (`HeatBath.heatPart_pos`, `integral_pos_of_pos`).

DERIVED: `0` is the sign asserted. -/
theorem heatPart2_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk) (W : Lk → SU N) :
    0 < heatPart2 bd β l m W := by
  show 0 < ∫ h, havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N))
  exact integral_pos_of_pos
    ((continuous_havg l (continuous_wt bd β)).comp (continuous_const.update m continuous_id))
    (fun h => heatPart_pos bd β l (Function.update W m h))

#print axioms heatPart2_pos

/-- The two-link heat bath of a continuous function is continuous.

DERIVED: no numeral. -/
theorem continuous_heatAvg2 (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : Continuous (heatAvg2 bd β l m f) :=
  (continuous_havg m (continuous_havg l (hf.mul (continuous_wt bd β)))).div
    (continuous_havg m (continuous_havg l (continuous_wt bd β)))
    (fun W => (heatPart2_pos bd β l m W).ne')

#print axioms continuous_heatAvg2

/-- The two-link heat bath does not read `m` (`HeatBathErgodic.havg_update`).

DERIVED: no numeral. -/
theorem heatAvg2_update_m (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk)
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) (h : SU N) :
    heatAvg2 bd β l m f (Function.update W m h) = heatAvg2 bd β l m f W := by
  simp only [heatAvg2, heatNum2, heatPart2, havg_update]

#print axioms heatAvg2_update_m

/-- The two-link heat bath does not read `l`, for `l ≠ m` (`HeatBathErgodic.havg_update_other`).

DERIVED: no numeral. -/
theorem heatAvg2_update_l (bd : Pq → List (Lk × Bool)) (β : ℝ) {l m : Lk} (hlm : l ≠ m)
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) (g : SU N) :
    heatAvg2 bd β l m f (Function.update W l g) = heatAvg2 bd β l m f W := by
  unfold heatAvg2 heatNum2 heatPart2
  rw [havg_update_other (φ := havg l (fun V => f V * wt bd β V)) (Ne.symm hlm)
      (fun V g' => havg_update l _ V g') W g,
    havg_update_other (φ := havg l (wt (N := N) bd β)) (Ne.symm hlm)
      (fun V g' => havg_update l _ V g') W g]

#print axioms heatAvg2_update_l

/-- **The two-link heat bath fixes every function reading neither `l` nor `m`.**

DERIVED: no numeral. -/
theorem heatAvg2_of_readsNot (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk)
    {f : (Lk → SU N) → ℝ} (hl : ∀ W g, f (Function.update W l g) = f W)
    (hm : ∀ W h, f (Function.update W m h) = f W) (W : Lk → SU N) :
    heatAvg2 bd β l m f W = f W := by
  have hnum : heatNum2 bd β l m f W = f W * heatPart2 bd β l m W := by
    unfold heatNum2 heatPart2 havg
    simp only [hl, hm, integral_const_mul]
  unfold heatAvg2
  rw [hnum]
  exact mul_div_cancel_right₀ _ (heatPart2_pos bd β l m W).ne'

#print axioms heatAvg2_of_readsNot

/-- **The two-link numerator of `φ − heatAvg2 φ` vanishes**, for continuous `φ` and `l ≠ m`
(`HeatBathErgodic.havg_sub`, `heatAvg2_update_l`, `heatAvg2_update_m`).

DERIVED: `0` is the value asserted. -/
theorem heatNum2_sub_self (bd : Pq → List (Lk × Bool)) (β : ℝ) {l m : Lk} (hlm : l ≠ m)
    {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) (W : Lk → SU N) :
    heatNum2 bd β l m (fun V => φ V - heatAvg2 bd β l m φ V) W = 0 := by
  have hc : Continuous (heatAvg2 bd β l m φ) := continuous_heatAvg2 bd β l m hφ
  have hφw : Continuous (fun V => φ V * wt bd β V) := hφ.mul (continuous_wt bd β)
  have hcw : Continuous (fun V => heatAvg2 bd β l m φ V * wt bd β V) :=
    hc.mul (continuous_wt bd β)
  have e1 : (fun V => (φ V - heatAvg2 bd β l m φ V) * wt bd β V)
      = fun V => φ V * wt bd β V - heatAvg2 bd β l m φ V * wt bd β V :=
    funext fun V => sub_mul _ _ _
  have e2a : ∀ V, havg l (fun V => heatAvg2 bd β l m φ V * wt bd β V) V
      = heatAvg2 bd β l m φ V * havg l (wt (N := N) bd β) V := by
    intro V
    unfold havg
    simp only [heatAvg2_update_l bd β hlm, integral_const_mul]
  have e2 : havg l (fun V => φ V * wt bd β V - heatAvg2 bd β l m φ V * wt bd β V)
      = fun V => havg l (fun V => φ V * wt bd β V) V
        - heatAvg2 bd β l m φ V * havg l (wt (N := N) bd β) V := by
    funext V
    rw [havg_sub l hφw hcw V, e2a V]
  have e3a : havg m (fun V => heatAvg2 bd β l m φ V * havg l (wt (N := N) bd β) V) W
      = heatAvg2 bd β l m φ W * heatPart2 bd β l m W := by
    unfold heatPart2 havg
    simp only [heatAvg2_update_m, integral_const_mul]
  have e4 : heatAvg2 bd β l m φ W * heatPart2 bd β l m W
      = havg m (havg l (fun V => φ V * wt bd β V)) W := by
    unfold heatAvg2
    exact div_mul_cancel₀ _ (heatPart2_pos bd β l m W).ne'
  show havg m (havg l (fun V => (φ V - heatAvg2 bd β l m φ V) * wt bd β V)) W = 0
  have e5 : havg m (fun V => havg l (fun V => φ V * wt bd β V) V
        - heatAvg2 bd β l m φ V * havg l (wt (N := N) bd β) V) W
      = havg m (fun V => havg l (fun V => φ V * wt bd β V) V) W
        - havg m (fun V => heatAvg2 bd β l m φ V * havg l (wt (N := N) bd β) V) W :=
    havg_sub m (continuous_havg l hφw) (hc.mul (continuous_havg l (continuous_wt bd β))) W
  rw [e1, e2, e5, e3a, ← e4, sub_self]

#print axioms heatNum2_sub_self

end TwoLink

/-! ## 4. The two-link weight -/

section PairWeight

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- The action of the plaquettes whose boundary word visits `l` or `m`.

DERIVED: no numeral. -/
def pairLocSum (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => l ∈ (bd p).map Prod.fst ∨ m ∈ (bd p).map Prod.fst),
    wilsonDensity (wilsonHol bd p W)

/-- The action of the plaquettes whose boundary word visits neither `l` nor `m`.

DERIVED: no numeral. -/
def pairRestSum (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => ¬ (l ∈ (bd p).map Prod.fst ∨ m ∈ (bd p).map Prod.fst)),
    wilsonDensity (wilsonHol bd p W)

/-- The action splits at the pair (`Finset.sum_filter_add_sum_filter_not`).

DERIVED: no numeral. -/
theorem action_split_pair (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N) :
    (wilsonSystem bd (wilsonDensity (N := N))).action W
      = pairLocSum bd l m W + pairRestSum bd l m W := by
  show ∑ p, wilsonDensity (wilsonHol bd p W) = _
  unfold pairLocSum pairRestSum
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm

#print axioms action_split_pair

/-- The rest of the action does not read `l` (`HeatBath.wilsonHol_update_of_not_mem`).

DERIVED: no numeral. -/
theorem pairRestSum_update_l (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N)
    (g : SU N) : pairRestSum bd l m (Function.update W l g) = pairRestSum bd l m W := by
  unfold pairRestSum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hl : l ∉ (bd p).map Prod.fst := fun h => (Finset.mem_filter.mp hp).2 (Or.inl h)
  rw [wilsonHol_update_of_not_mem bd p hl]

#print axioms pairRestSum_update_l

/-- The rest of the action does not read `m`.

DERIVED: no numeral. -/
theorem pairRestSum_update_m (bd : Pq → List (Lk × Bool)) (l m : Lk) (W : Lk → SU N)
    (h : SU N) : pairRestSum bd l m (Function.update W m h) = pairRestSum bd l m W := by
  unfold pairRestSum
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hm : m ∉ (bd p).map Prod.fst := fun h' => (Finset.mem_filter.mp hp).2 (Or.inr h')
  rw [wilsonHol_update_of_not_mem bd p hm]

#print axioms pairRestSum_update_m

/-- The weight factors at the pair: `wt = e^{−β pairLocSum} · e^{−β pairRestSum}`.

DERIVED: no numeral. -/
theorem wt_split_pair (bd : Pq → List (Lk × Bool)) (β : ℝ) (l m : Lk) (V : Lk → SU N) :
    wt bd β V = Real.exp (-β * pairLocSum bd l m V) * Real.exp (-β * pairRestSum bd l m V) := by
  unfold wt
  show Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action V) = _
  rw [action_split_pair bd l m V, mul_add, Real.exp_add]

#print axioms wt_split_pair

/-- The pair action is non-negative (`WilsonAction.wilsonDensity_nonneg`).

DERIVED: `0` is the sign and the excluded rank in `hN`. -/
theorem pairLocSum_nonneg (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (l m : Lk)
    (V : Lk → SU N) : 0 ≤ pairLocSum bd l m V := by
  unfold pairLocSum
  exact Finset.sum_nonneg (fun p _ => WilsonAction.wilsonDensity_nonneg hN _)

#print axioms pairLocSum_nonneg

end PairWeight

section TorusWeight

variable {N : ℕ}

/-- **At most `256` plaquettes visit a torus link, at every extent**: a plaquette `((μ, ν), x)`
visiting `l` has `l.2 ∈ {x, x + e_μ, x + e_ν}` (`BoxPatch.bd_site`), so every coordinate of
`x − l.2` is `0` or `−1` (`BoxPatch.site_cases`), and there are `4 · 4 · 2⁴` such plaquettes.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent;
`256 = 4 · 4 · 2⁴`: `4 · 4` ordered direction pairs, `2` values `0`, `−1` per coordinate, `4`
coordinates. -/
theorem card_visit_le (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      l ∈ (bdT M p).map Prod.fst)).card ≤ 256 := by
  have hsub : Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        l ∈ (bdT M p).map Prod.fst)
      ⊆ ((Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ
          Fintype.piFinset (fun _ : Fin 4 => ({0, -1} : Finset (Fin (M + 1))))).image
        (fun q => ((q.1, l.2 + q.2) : WilsonHypercubic.Plaq 4 (M + 1))) := by
    intro p hp
    have hpl : l ∈ (bdT M p).map Prod.fst := (Finset.mem_filter.mp hp).2
    rw [Finset.mem_image]
    refine ⟨(p.1, p.2 - l.2), ?_, ?_⟩
    · rw [Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨Finset.mem_univ _, fun k => ?_⟩
      show (p.2 - l.2) k ∈ ({0, -1} : Finset (Fin (M + 1)))
      rw [Pi.sub_apply]
      rcases (BoxPatch.site_cases (BoxPatch.bd_site p hpl) k).1 with h | h
      · rw [h, sub_self]
        simp
      · rw [h, sub_add_cancel_left]
        simp
    · exact Prod.ext rfl (by show l.2 + (p.2 - l.2) = p.2; abel)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = 4 * 4 * (Fintype.piFinset
          (fun _ : Fin 4 => ({0, -1} : Finset (Fin (M + 1))))).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    _ ≤ 4 * 4 * 16 := by
        refine Nat.mul_le_mul_left _ ?_
        rw [Fintype.card_piFinset_const]
        calc ({0, -1} : Finset (Fin (M + 1))).card ^ 4 ≤ 2 ^ 4 :=
              Nat.pow_le_pow_left Finset.card_le_two 4
          _ = 16 := by norm_num
    _ = 256 := by norm_num

#print axioms card_visit_le

/-- **At most `512` plaquettes visit `l` or `m`** (`card_visit_le` twice).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `512 = 2 · 256`. -/
theorem card_pairVisit_le (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      l ∈ (bdT M p).map Prod.fst ∨ m ∈ (bdT M p).map Prod.fst)).card ≤ 512 := by
  have hsub : Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        l ∈ (bdT M p).map Prod.fst ∨ m ∈ (bdT M p).map Prod.fst)
      ⊆ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          l ∈ (bdT M p).map Prod.fst)
        ∪ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          m ∈ (bdT M p).map Prod.fst) := by
    intro p hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases (Finset.mem_filter.mp hp).2 with h | h
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 256 + 256 := Nat.add_le_add (card_visit_le M l) (card_visit_le M m)
    _ = 512 := by norm_num

#print axioms card_pairVisit_le

/-- **The pair action is at most `1024` at every extent**: at most `512` plaquettes, each of action
at most `2` (`WilsonAction.wilsonDensity_le_two`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent;
`1024 = 2 · 512`; `2` is the largest plaquette action; `512` is `card_pairVisit_le`'s bound; `0`
is the excluded rank in `hN`. -/
theorem pairLocSum_le_torus (hN : N ≠ 0) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (V : WilsonHypercubic.Link 4 (M + 1) → SU N) : pairLocSum (bdT M) l m V ≤ 1024 := by
  unfold pairLocSum
  calc _ ≤ ∑ _p ∈ _, (2 : ℝ) :=
        Finset.sum_le_sum (fun p _ => WilsonAction.wilsonDensity_le_two hN _)
    _ = _ • (2 : ℝ) := Finset.sum_const _
    _ ≤ (512 : ℕ) • (2 : ℝ) := by
        apply nsmul_le_nsmul_left (by norm_num)
        convert card_pairVisit_le M l m
    _ = 1024 := by norm_num

#print axioms pairLocSum_le_torus

/-- **Two exponentials between two constants**: for `0 ≤ β` and `0 ≤ L ≤ 1024`,
`e^{−1024β} e^{−βR} ≤ e^{−βL} e^{−βR} ≤ e^{−βR}`.

DERIVED: `0` is the lower end of `β` and `L`; `1024` is `pairLocSum_le_torus`'s bound. -/
theorem exp_pair_bounds {β L R : ℝ} (hβ : 0 ≤ β) (h0 : 0 ≤ L) (h1 : L ≤ 1024) :
    Real.exp (-(β * 1024)) * Real.exp (-β * R) ≤ Real.exp (-β * L) * Real.exp (-β * R)
      ∧ Real.exp (-β * L) * Real.exp (-β * R) ≤ Real.exp (-β * R) := by
  have hE := Real.exp_pos (-β * R)
  constructor
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hE.le
    linarith [mul_le_mul_of_nonneg_left h1 hβ]
  · have h3 : Real.exp (-β * L) ≤ 1 :=
      calc Real.exp (-β * L) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by linarith [mul_nonneg hβ h0])
        _ = 1 := Real.exp_zero
    calc Real.exp (-β * L) * Real.exp (-β * R) ≤ 1 * Real.exp (-β * R) :=
          mul_le_mul_of_nonneg_right h3 hE.le
      _ = Real.exp (-β * R) := one_mul _

#print axioms exp_pair_bounds

/-- **The weight on the fibre of `(l, m)`**: for `0 ≤ β`, every configuration agreeing with `W` off
`l` and `m` has weight in `[e^{−1024β} E, E]`, `E = e^{−β pairRestSum W}` (`wt_split_pair`,
`pairRestSum_update_l`, `pairRestSum_update_m`, `pairLocSum_le_torus`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` is the lower
end of `β` and the excluded rank in `hN`; `1024` is `pairLocSum_le_torus`'s bound. -/
theorem wt_pair_bounds (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (M : ℕ)
    (l m : WilsonHypercubic.Link 4 (M + 1)) (W : WilsonHypercubic.Link 4 (M + 1) → SU N)
    (h g : SU N) :
    Real.exp (-(β * 1024)) * Real.exp (-β * pairRestSum (bdT M) l m W)
        ≤ wt (bdT M) β (Function.update (Function.update W m h) l g)
      ∧ wt (bdT M) β (Function.update (Function.update W m h) l g)
        ≤ Real.exp (-β * pairRestSum (bdT M) l m W) := by
  have hrest : pairRestSum (bdT M) l m (Function.update (Function.update W m h) l g)
      = pairRestSum (bdT M) l m W := by
    rw [pairRestSum_update_l, pairRestSum_update_m]
  have h0 := pairLocSum_nonneg hN (bdT M) l m (Function.update (Function.update W m h) l g)
  have h2 := pairLocSum_le_torus hN M l m (Function.update (Function.update W m h) l g)
  rw [wt_split_pair (bdT M) β l m, hrest]
  exact exp_pair_bounds hβ h0 h2

#print axioms wt_pair_bounds

/-- `e^t (e^{−t} E) = E`.

DERIVED: no numeral. -/
theorem exp_mul_exp_neg (t E : ℝ) : Real.exp t * (Real.exp (-t) * E) = E := by
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

#print axioms exp_mul_exp_neg

/-- **The cubic bound**: for `0 ≤ t` and `3t ≤ 1`, `(e^{2t} − 1) e^t ≤ (45/8) t`. From
`e^t (1 − t) ≤ 1` (`Real.add_one_le_exp` at `−t`): `e^t ≤ 3/2`, `e^t − 1 ≤ (3/2) t`, and
`(e^t + 1) e^t ≤ 15/4`.

DERIVED: `2` is the square; `1` in `e^{2t} − 1` is `e^0`; `0` is the lower end of `t`.
CHOSEN: `3t ≤ 1` (the `3` and the `1`) keeps `e^t ≤ 3/2`. DERIVED from it: `45/8 = (3/2)(15/4)`, the
product of the bounds on `e^t − 1` and on `(e^t + 1) e^t`. -/
theorem exp_cube_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : 3 * t ≤ 1) :
    (Real.exp t ^ 2 - 1) * Real.exp t ≤ 45 / 8 * t := by
  have he1 : 1 ≤ Real.exp t := Real.one_le_exp ht0
  have hepos := Real.exp_pos t
  have hinv : Real.exp t * (1 - t) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-t)
    have h2 : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_left h1 hepos.le
    linarith
  have he2 : Real.exp t ≤ 3 / 2 := by
    nlinarith [mul_nonneg hepos.le (by linarith : (0 : ℝ) ≤ 1 / 3 - t)]
  have he3 : Real.exp t - 1 ≤ 3 / 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_right he2 ht0]
  have hB : (Real.exp t + 1) * Real.exp t ≤ 15 / 4 := by
    nlinarith [mul_le_mul he2 he2 hepos.le (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  calc (Real.exp t ^ 2 - 1) * Real.exp t
      = (Real.exp t - 1) * ((Real.exp t + 1) * Real.exp t) := by ring
    _ ≤ (3 / 2 * t) * (15 / 4) :=
        mul_le_mul he3 hB (by positivity) (mul_nonneg (by norm_num) ht0)
    _ = 45 / 8 * t := by ring

#print axioms exp_cube_sub_le

end TorusWeight

/-! ## 5. The Gibbs correlation bound -/

section Gibbs

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- **The fibre bound on the configurations.** For `l ≠ m`, continuous `f` with vanishing two-link
numerator at `W`, and the weight on the fibre of `(l, m)` over `W` in `[m₀, κ m₀]`:

    havg_m havg_l (E_l f · E_m f · wt) (W)
      ≤ ((κ² − 1) κ / 2) (havg_m havg_l ((E_l f)² wt) (W) + havg_l havg_m ((E_m f)² wt) (W)),

`E = heatAvg`. `fibre_corr_le` at `a(h) = E_l f(W[m ↦ h])`, `b(g) = E_m f(W[l ↦ g])`,
`q(h) = heatPart_l(W[m ↦ h])`, `p(g) = heatPart_m(W[l ↦ g])` (`HeatBath.heatAvg_update`,
`Function.update_comm`).

DERIVED: `1` is the least `κ` and the `1` of `κ² − 1`; `2` is the square and the halving; `0` is
the sign of `m₀` and the vanishing numerator. -/
theorem fibre_corr_config (bd : Pq → List (Lk × Bool)) (β : ℝ) {l m : Lk} (hlm : l ≠ m)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (W : Lk → SU N) {m₀ κ : ℝ} (hm₀ : 0 < m₀)
    (hκ : 1 ≤ κ)
    (hw0 : ∀ h g, m₀ ≤ wt bd β (Function.update (Function.update W m h) l g))
    (hw1 : ∀ h g, wt bd β (Function.update (Function.update W m h) l g) ≤ κ * m₀)
    (hzero : heatNum2 bd β l m f W = 0) :
    havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
      ≤ (κ ^ 2 - 1) * κ / 2
        * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
          + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W) := by
  have hml : m ≠ l := Ne.symm hlm
  have ha : Continuous (fun h => heatAvg bd β l f (Function.update W m h)) :=
    (continuous_heatAvg bd β l hf).comp (continuous_const.update m continuous_id)
  have hb : Continuous (fun g => heatAvg bd β m f (Function.update W l g)) :=
    (continuous_heatAvg bd β m hf).comp (continuous_const.update l continuous_id)
  have hp : Continuous (fun g => havg m (wt (N := N) bd β) (Function.update W l g)) :=
    (continuous_havg m (continuous_wt bd β)).comp (continuous_const.update l continuous_id)
  have hq : Continuous (fun h => havg l (wt (N := N) bd β) (Function.update W m h)) :=
    (continuous_havg l (continuous_wt bd β)).comp (continuous_const.update m continuous_id)
  have hw : Continuous (fun z : SU N × SU N =>
      wt bd β (Function.update (Function.update W m z.1) l z.2)) :=
    (continuous_wt bd β).comp
      (((continuous_const : Continuous fun _ : SU N × SU N => W).update m
        continuous_fst).update l continuous_snd)
  -- the marginals lie in the same range
  have hq0 : ∀ h, m₀ ≤ havg l (wt (N := N) bd β) (Function.update W m h) := fun h =>
    const_le_integral (φ := fun g => wt bd β (Function.update (Function.update W m h) l g))
      ((continuous_wt bd β).comp (continuous_const.update l continuous_id)) (fun g => hw0 h g)
  have hq1 : ∀ h, havg l (wt (N := N) bd β) (Function.update W m h) ≤ κ * m₀ := fun h =>
    integral_le_const (φ := fun g => wt bd β (Function.update (Function.update W m h) l g))
      ((continuous_wt bd β).comp (continuous_const.update l continuous_id)) (fun g => hw1 h g)
  have hswap : ∀ g h, wt bd β (Function.update (Function.update W l g) m h)
      = wt bd β (Function.update (Function.update W m h) l g) := fun g h => by
    rw [Function.update_comm hlm g h W]
  have hp0 : ∀ g, m₀ ≤ havg m (wt (N := N) bd β) (Function.update W l g) := fun g =>
    const_le_integral (φ := fun h => wt bd β (Function.update (Function.update W l g) m h))
      ((continuous_wt bd β).comp (continuous_const.update m continuous_id))
      (fun h => by
        show m₀ ≤ wt bd β (Function.update (Function.update W l g) m h)
        rw [hswap g h]
        exact hw0 h g)
  have hp1 : ∀ g, havg m (wt (N := N) bd β) (Function.update W l g) ≤ κ * m₀ := fun g =>
    integral_le_const (φ := fun h => wt bd β (Function.update (Function.update W l g) m h))
      ((continuous_wt bd β).comp (continuous_const.update m continuous_id))
      (fun h => by
        show wt bd β (Function.update (Function.update W l g) m h) ≤ κ * m₀
        rw [hswap g h]
        exact hw1 h g)
  -- the vanishing mean
  have hz : ∫ h, heatAvg bd β l f (Function.update W m h)
      * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N)) = 0 := by
    have e : ∀ h, heatAvg bd β l f (Function.update W m h)
        * havg l (wt (N := N) bd β) (Function.update W m h)
        = heatNum bd β l f (Function.update W m h) := fun h =>
      div_mul_cancel₀ _ (heatPart_pos bd β l _).ne'
    calc ∫ h, heatAvg bd β l f (Function.update W m h)
          * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N))
        = ∫ h, heatNum bd β l f (Function.update W m h) ∂(probHaar (SU N)) :=
          integral_congr_ae (Filter.Eventually.of_forall e)
      _ = 0 := hzero
  have key := fibre_corr_le
    (a := fun h => heatAvg bd β l f (Function.update W m h))
    (b := fun g => heatAvg bd β m f (Function.update W l g))
    (p := fun g => havg m (wt (N := N) bd β) (Function.update W l g))
    (q := fun h => havg l (wt (N := N) bd β) (Function.update W m h))
    (w := fun h g => wt bd β (Function.update (Function.update W m h) l g))
    ha hb hp hq hw hm₀ hκ hw0 hw1 hp0 hp1 hq0 hq1 hz
  -- the three fibre integrals
  have E1 : havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
      = ∫ h, ∫ g, heatAvg bd β l f (Function.update W m h)
          * heatAvg bd β m f (Function.update W l g)
          * wt bd β (Function.update (Function.update W m h) l g)
          ∂(probHaar (SU N)) ∂(probHaar (SU N)) := by
    unfold havg
    refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
    show heatAvg bd β l f (Function.update (Function.update W m h) l g)
        * heatAvg bd β m f (Function.update (Function.update W m h) l g)
        * wt bd β (Function.update (Function.update W m h) l g)
      = heatAvg bd β l f (Function.update W m h) * heatAvg bd β m f (Function.update W l g)
        * wt bd β (Function.update (Function.update W m h) l g)
    rw [heatAvg_update bd β l f (Function.update W m h) g, Function.update_comm hml h g W,
      heatAvg_update bd β m f (Function.update W l g) h]
  have E2 : havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
      = ∫ h, heatAvg bd β l f (Function.update W m h) ^ 2
          * havg l (wt (N := N) bd β) (Function.update W m h) ∂(probHaar (SU N)) := by
    unfold havg
    refine integral_congr_ae (Filter.Eventually.of_forall (fun h => ?_))
    show ∫ g, heatAvg bd β l f (Function.update (Function.update W m h) l g)
          * heatAvg bd β l f (Function.update (Function.update W m h) l g)
          * wt bd β (Function.update (Function.update W m h) l g) ∂(probHaar (SU N))
      = heatAvg bd β l f (Function.update W m h) ^ 2
        * ∫ g, wt bd β (Function.update (Function.update W m h) l g) ∂(probHaar (SU N))
    simp only [heatAvg_update, integral_const_mul, sq]
  have E3 : havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W
      = ∫ g, heatAvg bd β m f (Function.update W l g) ^ 2
          * havg m (wt (N := N) bd β) (Function.update W l g) ∂(probHaar (SU N)) := by
    unfold havg
    refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
    show ∫ h, heatAvg bd β m f (Function.update (Function.update W l g) m h)
          * heatAvg bd β m f (Function.update (Function.update W l g) m h)
          * wt bd β (Function.update (Function.update W l g) m h) ∂(probHaar (SU N))
      = heatAvg bd β m f (Function.update W l g) ^ 2
        * ∫ h, wt bd β (Function.update (Function.update W l g) m h) ∂(probHaar (SU N))
    simp only [heatAvg_update, integral_const_mul, sq]
  rw [E1, E2, E3]
  exact key

#print axioms fibre_corr_config

/-- **THE GIBBS CORRELATION BOUND.** For `l ≠ m`, continuous `f` with vanishing two-link numerator
everywhere, `1 ≤ κ`, `(κ² − 1) κ ≤ c`, and at every `W` a positive `m₀` with the weight on the fibre
of `(l, m)` over `W` in `[m₀, κ m₀]`:

    ∫ E_l f · E_m f · wt ≤ (c/2) (∫ (E_l f)² wt + ∫ (E_m f)² wt)

against the product Haar measure (`HeatBathErgodic.integral_havg` twice on each side,
`fibre_corr_config` at every `W`, `integral_mono`).

DERIVED: `1` is the least `κ` and the `1` of `κ² − 1`; `2` is the square and the halving; `0` is
the sign of `m₀` and the vanishing numerator. -/
theorem gibbs_corr_le (bd : Pq → List (Lk × Bool)) (β : ℝ) {l m : Lk} (hlm : l ≠ m)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) (hzero : ∀ W, heatNum2 bd β l m f W = 0)
    {κ c : ℝ} (hκ : 1 ≤ κ) (hc : (κ ^ 2 - 1) * κ ≤ c)
    (hwt : ∀ W : Lk → SU N, ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ h g,
      m₀ ≤ wt bd β (Function.update (Function.update W m h) l g)
        ∧ wt bd β (Function.update (Function.update W m h) l g) ≤ κ * m₀) :
    ∫ W, heatAvg bd β l f W * heatAvg bd β m f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      ≤ c / 2 * (∫ W, heatAvg bd β l f W * heatAvg bd β l f W * wt bd β W
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))
          + ∫ W, heatAvg bd β m f W * heatAvg bd β m f W * wt bd β W
            ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
  have cA := continuous_heatAvg bd β l hf
  have cB := continuous_heatAvg bd β m hf
  have cw := continuous_wt (N := N) bd β
  have cAB : Continuous (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V) :=
    (cA.mul cB).mul cw
  have cAA : Continuous (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V) :=
    (cA.mul cA).mul cw
  have cBB : Continuous (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V) :=
    (cB.mul cB).mul cw
  have e1 : ∫ W, heatAvg bd β l f W * heatAvg bd β m f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg m (continuous_havg l cAB)).trans (integral_havg l cAB)).symm
  have e2 : ∫ W, heatAvg bd β l f W * heatAvg bd β l f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg m (continuous_havg l cAA)).trans (integral_havg l cAA)).symm
  have e3 : ∫ W, heatAvg bd β m f W * heatAvg bd β m f W * wt bd β W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
    ((integral_havg l (continuous_havg m cBB)).trans (integral_havg m cBB)).symm
  have hnnA : ∀ V, 0 ≤ heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V :=
    fun V => mul_nonneg (mul_self_nonneg _) (wt_pos bd β V).le
  have hnnB : ∀ V, 0 ≤ heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V :=
    fun V => mul_nonneg (mul_self_nonneg _) (wt_pos bd β V).le
  have hpt : ∀ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
      ≤ c / 2 * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
        + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W) := by
    intro W
    obtain ⟨m₀, hm₀, hb⟩ := hwt W
    have hfib := fibre_corr_config bd β hlm hf W hm₀ hκ (fun h g => (hb h g).1)
      (fun h g => (hb h g).2) (hzero W)
    have hnn : 0 ≤ havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
        + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W :=
      add_nonneg (havg_nonneg m (fun V => havg_nonneg l hnnA V) W)
        (havg_nonneg l (fun V => havg_nonneg m hnnB V) W)
    exact le_trans hfib (mul_le_mul_of_nonneg_right (by linarith) hnn)
  have i1 : Integrable
      (fun W => havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg m (continuous_havg l cAB))
  have i2 : Integrable
      (fun W => havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg m (continuous_havg l cAA))
  have i3 : Integrable
      (fun W => havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W)
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_havg l (continuous_havg m cBB))
  have i23 : Integrable
      (fun W => c / 2
        * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
          + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W))
      (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    haar_integrable (continuous_const.mul ((continuous_havg m (continuous_havg l cAA)).add
      (continuous_havg l (continuous_havg m cBB))))
  rw [e1, e2, e3]
  calc ∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β m f V * wt bd β V)) W
        ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      ≤ ∫ W, c / 2
          * (havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
            + havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W)
          ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
        integral_mono i1 i23 hpt
    _ = c / 2
          * (∫ W, havg m (havg l (fun V => heatAvg bd β l f V * heatAvg bd β l f V * wt bd β V)) W
              ∂(Measure.pi fun _ : Lk => probHaar (SU N))
            + ∫ W, havg l (havg m (fun V => heatAvg bd β m f V * heatAvg bd β m f V * wt bd β V)) W
              ∂(Measure.pi fun _ : Lk => probHaar (SU N))) := by
        rw [integral_const_mul, integral_add i2 i3]

#print axioms gibbs_corr_le

end Gibbs

/-! ## 6. The two-link conditional expectation on the periodic observables -/

section TorusTwo

variable {N : ℕ}

/-- **A gauge transformation commutes with updating a link**, the new value conjugated by the gauge
function at the link's ends.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` in
`l.1`, `l.2` are projections. -/
theorem update_gaugeTransform {M : ℕ} (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (l : WilsonHypercubic.Link 4 (M + 1))
    (h : SU N) :
    Function.update (LocalGauge.gaugeTransform g W) l h
      = LocalGauge.gaugeTransform g
          (Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2))) := by
  funext l'
  by_cases hl : l' = l
  · rw [hl, Function.update_self]
    show h = g l.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l
      * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
    rw [Function.update_self]
    group
  · rw [Function.update_of_ne hl]
    show g l'.2 * W l' * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
      = g l'.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l'
        * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
    rw [Function.update_of_ne hl]

#print axioms update_gaugeTransform

/-- **The Haar average at a link keeps gauge invariance** (`update_gaugeTransform`,
`HeatBath.integral_twoSided`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem havg_gauge {M : ℕ} (l : WilsonHypercubic.Link 4 (M + 1))
    {Ψ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hΨ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), Ψ (LocalGauge.gaugeTransform g W) = Ψ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    havg l Ψ (LocalGauge.gaugeTransform g W) = havg l Ψ W := by
  unfold havg
  simp only [update_gaugeTransform, hΨ]
  exact integral_twoSided (fun y => Ψ (Function.update W l y)) _ _

#print axioms havg_gauge

/-- Two Haar averages keep gauge invariance (`havg_gauge` twice).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem havg2_gauge {M : ℕ} (l m : WilsonHypercubic.Link 4 (M + 1))
    {Ψ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hΨ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), Ψ (LocalGauge.gaugeTransform g W) = Ψ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    havg m (havg l Ψ) (LocalGauge.gaugeTransform g W) = havg m (havg l Ψ) W :=
  havg_gauge m (fun g' W' => havg_gauge l hΨ g' W') g W

#print axioms havg2_gauge

/-- **The two-link heat bath keeps torus gauge invariance** (`havg2_gauge`,
`LocalGauge.boltz_gauge_invariant_local`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem heatAvg2_gauge (β : ℝ) {M : ℕ} (l m : WilsonHypercubic.Link 4 (M + 1))
    {φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hφ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), φ (LocalGauge.gaugeTransform g W) = φ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    heatAvg2 (bdT M) β l m φ (LocalGauge.gaugeTransform g W) = heatAvg2 (bdT M) β l m φ W := by
  have hwt : ∀ (g' : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (V : WilsonHypercubic.Link 4 (M + 1) → SU N),
      wt (bdT M) β (LocalGauge.gaugeTransform g' V) = wt (bdT M) β V :=
    fun g' V => LocalGauge.boltz_gauge_invariant_local g' β V
  have hφw : ∀ (g' : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (V : WilsonHypercubic.Link 4 (M + 1) → SU N),
      φ (LocalGauge.gaugeTransform g' V) * wt (bdT M) β (LocalGauge.gaugeTransform g' V)
        = φ V * wt (bdT M) β V :=
    fun g' V => by rw [hφ, hwt]
  unfold heatAvg2 heatNum2 heatPart2
  rw [havg2_gauge l m (Ψ := fun V => φ V * wt (bdT M) β V) hφw g W,
    havg2_gauge l m (Ψ := wt (bdT M) β) hwt g W]

#print axioms heatAvg2_gauge

/-- **The two-link heat bath lifted to `ℤ⁴` observables**: the two-link heat bath at the torus links
`l`, `m` of the torus reading of `F`, composed with the restriction to one period.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def heatLift2 (β : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) : C(GibbsSpec.IConf (SU N), ℝ) :=
  ⟨fun U => heatAvg2 (bdT M) β l m (torusObs M F) (restrictConf M U),
    (continuous_heatAvg2 (bdT M) β l m (continuous_torusObs M F)).comp
      (continuous_restrictConf M)⟩

/-- The torus reading of the lifted two-link heat bath is the two-link heat bath of the torus
reading (`HeatBath.restrictConf_pullback`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_heatLift2 (β : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) :
    torusObs M (heatLift2 β M l m F) = heatAvg2 (bdT M) β l m (torusObs M F) := by
  funext W
  show heatAvg2 (bdT M) β l m (torusObs M F) (restrictConf M (InfiniteLattice.pullback M W))
    = heatAvg2 (bdT M) β l m (torusObs M F) W
  rw [restrictConf_pullback]

#print axioms torusObs_heatLift2

/-- **The lifted two-link heat bath keeps periodic gauge invariance** (`restrictConf_igauge`,
`heatAvg2_gauge`, `torusObs_gauge`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem heatLift2_mem (β : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) :
    heatLift2 β M l m F ∈ periodicGaugeInvSubmodule (N := N) M := by
  show ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : GibbsSpec.IConf (SU N)),
    heatLift2 β M l m F
        (GaugeInvariantAlgebra.igaugeTransform (fun x => g (InfiniteLattice.siteMod M x)) U)
      = heatLift2 β M l m F U
  intro g U
  show heatAvg2 (bdT M) β l m (torusObs M F)
      (restrictConf M
        (GaugeInvariantAlgebra.igaugeTransform (fun x => g (InfiniteLattice.siteMod M x)) U))
    = heatAvg2 (bdT M) β l m (torusObs M F) (restrictConf M U)
  rw [restrictConf_igauge]
  exact heatAvg2_gauge β l m (fun g' W => torusObs_gauge hF g' W) g (restrictConf M U)

#print axioms heatLift2_mem

/-- **The two-link conditional expectation of a periodic gauge-invariant observable**: its
conditional expectation given every link but `l` and `m`, as an element of
`periodicGaugeInvSubmodule M`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `2` in `x.2` is
the membership proof, not a number. -/
def twoCondExp (β : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) : ↥(periodicGaugeInvSubmodule (N := N) M) :=
  ⟨heatLift2 β M l m (x : C(GibbsSpec.IConf (SU N), ℝ)), heatLift2_mem β M l m x.2⟩

/-- **The one-link conditional expectation at `l` fixes the two-link one**, for `l ≠ m`
(`HeatBath.heatAvg_of_readsNot`, `heatAvg2_update_l`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_twoCondExp_l (β : ℝ) (M : ℕ) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp β M l (twoCondExp β M l m x) = twoCondExp β M l m x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) β l (torusObs M (heatLift2 β M l m (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg2 (bdT M) β l m (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_heatLift2]
  exact heatAvg_of_readsNot (bdT M) β l (fun W g => heatAvg2_update_l (bdT M) β hlm _ W g) _

#print axioms torusCondExp_twoCondExp_l

/-- **The one-link conditional expectation at `m` fixes the two-link one**
(`HeatBath.heatAvg_of_readsNot`, `heatAvg2_update_m`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusCondExp_twoCondExp_m (β : ℝ) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusCondExp β M m (twoCondExp β M l m x) = twoCondExp β M l m x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show heatAvg (bdT M) β m (torusObs M (heatLift2 β M l m (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = heatAvg2 (bdT M) β l m (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_heatLift2]
  exact heatAvg_of_readsNot (bdT M) β m (fun W h => heatAvg2_update_m (bdT M) β l m _ W h) _

#print axioms torusCondExp_twoCondExp_m

/-- The torus reading of a one-link conditional expectation is the heat bath of the torus reading
(`HeatBath.torusObs_heatLift`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_condExp (β : ℝ) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    torusObs M ((torusCondExp β M l x : ↥(periodicGaugeInvSubmodule (N := N) M))
        : C(GibbsSpec.IConf (SU N), ℝ))
      = heatAvg (bdT M) β l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) :=
  torusObs_heatLift β M l (x : C(GibbsSpec.IConf (SU N), ℝ))

#print axioms torusObs_condExp

/-- **THE TWO-LINK CORRELATION AT SMALL COUPLING.** For `N ≠ 0`, `0 ≤ β`, `3072 β ≤ 1`, every
extent index `j`, every two distinct links `l`, `m` and every periodic gauge-invariant `x`, with
`y = twoCondExp x` (the conditional expectation given every link but `l` and `m`):

    ⟨E_l(x − y), E_m(x − y)⟩ ≤ 5760 β (‖E_l(x − y)‖² + ‖E_m(x − y)‖²)/2

in `torusForm`. `gibbs_corr_le` with `κ = e^{1024β}`, `m₀ = e^{−1024β} e^{−β pairRestSum W}`
(`wt_pair_bounds`, `exp_mul_exp_neg`), `(κ² − 1)κ ≤ (45/8)(1024β) = 5760β` (`exp_cube_sub_le`), and
the vanishing two-link numerator of `x − y` (`heatNum2_sub_self`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the lower end of `β` and the excluded rank in `hN`;
`3072 = 3 · 1024` is `exp_cube_sub_le`'s `3t ≤ 1` at `t = 1024β`; `5760 = (45/8) · 1024`; `2` is
the halving of the pair bound. -/
theorem pairCorr_twoCond (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : 3072 * β ≤ 1) (j : ℕ)
    {l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)} (hlm : l ≠ m)
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (torusCondExp β (2 * j + 1) l (x - twoCondExp β (2 * j + 1) l m x))
        (torusCondExp β (2 * j + 1) m (x - twoCondExp β (2 * j + 1) l m x))
      ≤ 5760 * β
        * (torusForm hN β j (torusCondExp β (2 * j + 1) l (x - twoCondExp β (2 * j + 1) l m x))
            (torusCondExp β (2 * j + 1) l (x - twoCondExp β (2 * j + 1) l m x))
          + torusForm hN β j (torusCondExp β (2 * j + 1) m (x - twoCondExp β (2 * j + 1) l m x))
            (torusCondExp β (2 * j + 1) m (x - twoCondExp β (2 * j + 1) l m x))) / 2 := by
  obtain ⟨F, hFdef⟩ : ∃ F : (WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N) → ℝ,
      F = fun V => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - heatAvg2 (bdT (2 * j + 1)) β l m
            (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V := ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hFdef]
    exact (continuous_torusObs _ _).sub
      (continuous_heatAvg2 (bdT (2 * j + 1)) β l m (continuous_torusObs _ _))
  have hzero : ∀ W, heatNum2 (bdT (2 * j + 1)) β l m F W = 0 := fun W => by
    rw [hFdef]
    exact heatNum2_sub_self (bdT (2 * j + 1)) β hlm (continuous_torusObs _ _) W
  have hF : torusObs (2 * j + 1) ((x - twoCondExp β (2 * j + 1) l m x
      : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ))
      = F := by
    rw [hFdef]
    funext V
    show torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - torusObs (2 * j + 1) (heatLift2 β (2 * j + 1) l m (x : C(GibbsSpec.IConf (SU N), ℝ))) V
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - heatAvg2 (bdT (2 * j + 1)) β l m
            (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V
    rw [torusObs_heatLift2]
  -- the weight hypotheses of `gibbs_corr_le`
  have hκ : 1 ≤ Real.exp (β * 1024) := Real.one_le_exp (mul_nonneg hβ0 (by norm_num))
  have hconst : (Real.exp (β * 1024) ^ 2 - 1) * Real.exp (β * 1024) ≤ 5760 * β := by
    have h := exp_cube_sub_le (t := β * 1024) (mul_nonneg hβ0 (by norm_num)) (by linarith)
    linarith
  have hwt : ∀ W : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N, ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ h g,
      m₀ ≤ wt (bdT (2 * j + 1)) β (Function.update (Function.update W m h) l g)
        ∧ wt (bdT (2 * j + 1)) β (Function.update (Function.update W m h) l g)
          ≤ Real.exp (β * 1024) * m₀ := fun W =>
    ⟨Real.exp (-(β * 1024)) * Real.exp (-β * pairRestSum (bdT (2 * j + 1)) l m W),
      mul_pos (Real.exp_pos _) (Real.exp_pos _), fun h g =>
        ⟨(wt_pair_bounds hN hβ0 (2 * j + 1) l m W h g).1, by
          rw [exp_mul_exp_neg]
          exact (wt_pair_bounds hN hβ0 (2 * j + 1) l m W h g).2⟩⟩
  have hg := gibbs_corr_le (bdT (2 * j + 1)) β hlm hFc hzero hκ hconst hwt
  have hZ := MassGap.WilsonReal.wilsonSystem_partition_pos hN (bdT (2 * j + 1)) β
  -- the forms as Gibbs integrals
  rw [torusForm_eq_integral, torusForm_eq_integral, torusForm_eq_integral,
    torusObs_condExp β (2 * j + 1) l, torusObs_condExp β (2 * j + 1) m, hF]
  refine le_trans (div_le_div_of_nonneg_right hg hZ.le) (le_of_eq ?_)
  ring

#print axioms pairCorr_twoCond

end TorusTwo

/-! ## 7. The defect matrix and the result -/

section Result

variable {N : ℕ}

/-- **The pair defect**: `5760 β` on the neighbours `HeatBathLocal.nbT j l` of `l` (the link itself
and the links sharing a plaquette with it), `0` elsewhere.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `5760 = (45/8) · 1024` is `pairCorr_twoCond`'s constant;
`0` is the defect of commuting pairs. -/
def pairDelta (β : ℝ) (j : ℕ) (l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℝ :=
  if m ∈ HeatBathLocal.nbT j l then 5760 * β else 0

/-- Being a neighbour is symmetric (`HeatBathLocal.mem_nbT`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem mem_nbT_symm {j : ℕ} {l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)}
    (h : m ∈ HeatBathLocal.nbT j l) : l ∈ HeatBathLocal.nbT j m := by
  rcases (HeatBathLocal.mem_nbT j l m).mp h with h1 | h1
  · exact (HeatBathLocal.mem_nbT j m l).mpr (Or.inl h1.symm)
  · obtain ⟨p, hp1, hp2⟩ := h1
    exact (HeatBathLocal.mem_nbT j m l).mpr (Or.inr ⟨p, hp2, hp1⟩)

#print axioms mem_nbT_symm

/-- The pair defect is non-negative.

DERIVED: `0` is the sign and the lower end of `β`; `4` is the spacetime dimension; `2 * j + 1` is
the index of the even-extent family and the `+ 1` its successor writing the extent. -/
theorem pairDelta_nonneg {β : ℝ} (hβ : 0 ≤ β) (j : ℕ)
    (l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : 0 ≤ pairDelta β j l m := by
  unfold pairDelta
  split_ifs
  · exact mul_nonneg (by norm_num) hβ
  · exact le_refl 0

#print axioms pairDelta_nonneg

/-- The pair defect is at most `5760 β`.

DERIVED: `5760` is `pairDelta`'s constant; `0` is the lower end of `β`; `4` is the spacetime
dimension; `2 * j + 1` is the index of the even-extent family and the `+ 1` its successor writing
the extent. -/
theorem pairDelta_le {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    pairDelta β j l m ≤ 5760 * β := by
  unfold pairDelta
  split_ifs
  · exact le_refl _
  · exact mul_nonneg (by norm_num) hβ

#print axioms pairDelta_le

/-- The pair defect is at most `1` for `5760 β ≤ 1`.

DERIVED: `1` is `BoxGap.BoxPairCorr`'s entry bound; `5760` is `pairDelta`'s constant; `0` is the
lower end of `β`; `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent
family and the `+ 1` its successor writing the extent. -/
theorem pairDelta_le_one {β : ℝ} (hβ : 0 ≤ β) (hβ1 : 5760 * β ≤ 1) (j : ℕ)
    (l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : pairDelta β j l m ≤ 1 :=
  le_trans (pairDelta_le hβ j l m) hβ1

#print axioms pairDelta_le_one

/-- **Row sums**: `Σ_m pairDelta β j l m ≤ 120960 β`, at most `21` neighbours
(`HeatBathLocal.card_nbT_le`) of defect `5760 β`.

DERIVED: `120960 = 21 · 5760`; `21` is `HeatBathLocal.card_nbT_le`'s bound; `5760` is
`pairDelta`'s constant; `0` is the lower end of `β`; `4` is the spacetime dimension; `2 * j + 1` is
the index of the even-extent family and the `+ 1` its successor writing the extent. -/
theorem pairDelta_row {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ∑ m, pairDelta β j l m ≤ 120960 * β := by
  have hsub : ∑ m ∈ HeatBathLocal.nbT j l, pairDelta β j l m = ∑ m, pairDelta β j l m :=
    Finset.sum_subset (Finset.subset_univ _) (fun m _ hm => by
      unfold pairDelta
      exact if_neg hm)
  have h1 := Finset.sum_le_card_nsmul (HeatBathLocal.nbT j l) (fun m => pairDelta β j l m)
    (5760 * β) (fun m _ => pairDelta_le hβ j l m)
  rw [nsmul_eq_mul] at h1
  have hc : ((HeatBathLocal.nbT j l).card : ℝ) ≤ 21 := by
    exact_mod_cast HeatBathLocal.card_nbT_le j l
  have h2 : ((HeatBathLocal.nbT j l).card : ℝ) * (5760 * β) ≤ 21 * (5760 * β) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num) hβ)
  rw [← hsub]
  linarith

#print axioms pairDelta_row

/-- **Column sums**: `Σ_l pairDelta β j l m ≤ 120960 β` (`mem_nbT_symm`, `card_nbT_le`).

DERIVED: `120960 = 21 · 5760`; `21` is `HeatBathLocal.card_nbT_le`'s bound; `5760` is
`pairDelta`'s constant; `0` is the lower end of `β`; `4` is the spacetime dimension; `2 * j + 1` is
the index of the even-extent family and the `+ 1` its successor writing the extent. -/
theorem pairDelta_col {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ∑ l, pairDelta β j l m ≤ 120960 * β := by
  have hsub : ∑ l ∈ HeatBathLocal.nbT j m, pairDelta β j l m = ∑ l, pairDelta β j l m :=
    Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => by
      unfold pairDelta
      exact if_neg (fun hm => hl (mem_nbT_symm hm)))
  have h1 := Finset.sum_le_card_nsmul (HeatBathLocal.nbT j m) (fun l => pairDelta β j l m)
    (5760 * β) (fun l _ => pairDelta_le hβ j l m)
  rw [nsmul_eq_mul] at h1
  have hc : ((HeatBathLocal.nbT j m).card : ℝ) ≤ 21 := by
    exact_mod_cast HeatBathLocal.card_nbT_le j m
  have h2 : ((HeatBathLocal.nbT j m).card : ℝ) * (5760 * β) ≤ 21 * (5760 * β) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num) hβ)
  rw [← hsub]
  linarith

#print axioms pairDelta_col

/-- The pair defect is a defect matrix with sums at most `120960 β`.

DERIVED: `120960` is `pairDelta_row`'s and `pairDelta_col`'s bound; `0` is the lower end of `β`;
`4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the `+ 1`
its successor writing the extent. -/
theorem pairDelta_defect {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) :
    DefectMatrix (pairDelta β j) (120960 * β) :=
  ⟨fun l m => pairDelta_nonneg hβ j l m, fun l => pairDelta_row hβ j l,
    fun m => pairDelta_col hβ j m⟩

#print axioms pairDelta_defect

/-- **The two-link correlation bound at every extent** for `0 ≤ β` and `5760 β ≤ 1`:
`BoxGap.PairCorrAt hN β j (pairDelta β j)`. A pair sharing a plaquette takes `y = twoCondExp x`
(`pairCorr_twoCond`; `3072 β ≤ 5760 β ≤ 1`); a pair sharing none takes `y = E_l E_m x`, where the
correlation is `0` (`BoxGap.corr_zero_of_comm`, `HeatBath.torusCondExp_comm`).

DERIVED: `5760` is `pairDelta`'s constant; `1` is the entry bound; `0` is the lower end of `β` and
the excluded rank in `hN`. -/
theorem pairCorrAt_small (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : 5760 * β ≤ 1) (j : ℕ) :
    PairCorrAt hN β j (pairDelta β j) := by
  intro l m hlm x
  by_cases hs : SharePlaq (bdT (2 * j + 1)) l m
  · refine ⟨twoCondExp β (2 * j + 1) l m x, torusCondExp_twoCondExp_l β (2 * j + 1) hlm x,
      torusCondExp_twoCondExp_m β (2 * j + 1) l m x, ?_⟩
    have hδ : pairDelta β j l m = 5760 * β := by
      unfold pairDelta
      exact if_pos ((HeatBathLocal.mem_nbT j l m).mpr (Or.inr hs))
    rw [hδ]
    exact pairCorr_twoCond hN hβ0 (by linarith) j hlm x
  · refine ⟨torusCondExp β (2 * j + 1) l (torusCondExp β (2 * j + 1) m x),
      torusCondExp_idem β (2 * j + 1) l _, ?_, ?_⟩
    · rw [← torusCondExp_comm β (2 * j + 1) hlm hs (torusCondExp β (2 * j + 1) m x),
        torusCondExp_idem β (2 * j + 1) m x]
    · have h0 := corr_zero_of_comm (torusForm hN β j) (torusCondExp β (2 * j + 1) l)
        (torusCondExp β (2 * j + 1) m) (torusCondExp_selfAdj hN β j l)
        (torusCondExp_selfAdj hN β j m) (torusCondExp_idem β (2 * j + 1) l)
        (torusCondExp_idem β (2 * j + 1) m) (fun z => torusCondExp_comm β (2 * j + 1) hlm hs z) x
      rw [h0]
      exact div_nonneg (mul_nonneg (pairDelta_nonneg hβ0 j l m)
        (add_nonneg (torusForm_nonneg hN β j _) (torusForm_nonneg hN β j _))) zero_le_two

#print axioms pairCorrAt_small

/-- **`BoxPairCorr` at small coupling**: `BoxGap.BoxPairCorr hN β (120960 β)` for `0 ≤ β` and
`5760 β ≤ 1`, uniformly in the extent.

DERIVED: `120960` is `pairDelta_defect`'s bound; `5760` is `pairDelta`'s constant; `1` is the
entry bound; `0` is the lower end of `β` and the excluded rank in `hN`. -/
theorem boxPairCorr_small (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : 5760 * β ≤ 1) :
    BoxPairCorr hN β (120960 * β) := fun j =>
  ⟨pairDelta β j, pairDelta_defect hβ0 j, fun l m => pairDelta_le_one hβ0 hβ1 j l m,
    pairCorrAt_small hN hβ0 hβ1 j⟩

#print axioms boxPairCorr_small

/-- **THE TWO-LINK CORRELATION IS LINEAR IN THE COUPLING.** `BoxGap.PairCorrLinear hN 120960
(1/5760)` for every `N ≠ 0`: `BoxPairCorr hN β (120960 β)` for every `0 ≤ β ≤ 1/5760`, at every
extent index.

DERIVED: `120960 = 21 · 5760` is `pairDelta_defect`'s constant; `1/5760` puts `5760 β ≤ 1`, the
entry bound of `BoxPairCorr`; `0` is the excluded rank in `hN`. -/
theorem pairCorrLinear_holds (hN : N ≠ 0) : PairCorrLinear hN 120960 (1 / 5760) := by
  intro β hβ0 hβ1
  have h : β * 5760 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 5760)).mp hβ1
  exact boxPairCorr_small hN hβ0 (by linarith)

#print axioms pairCorrLinear_holds

/-- **THE BOX CHECK AT SMALL COUPLING.** `BoxPatch.BoxPatchGap hN β 80 (1 − 120960 β)` for
`0 ≤ β ≤ 1/241920` (`BoxGap.boxPatchGap_of_pairCorrLinear`, `pairCorrLinear_holds`).

DERIVED: `80` is the side at defect at most `1/2` (`BoxGap.boxPatchGap_of_pairDefect_half`);
`120960` is `pairCorrLinear_holds`'s constant; `241920 = 2 · 120960` puts `120960 β ≤ 1/2`;
`1` is the gap at zero defect; `0` is the lower end of `β` and the excluded rank in `hN`. -/
theorem boxPatchGap_small (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 241920) :
    BoxPatch.BoxPatchGap hN β 80 (1 - 120960 * β) :=
  boxPatchGap_of_pairCorrLinear hN (pairCorrLinear_holds hN) (by norm_num) hβ0
    (le_trans hβ (by norm_num)) (le_trans hβ (by norm_num))

#print axioms boxPatchGap_small

/-- **The box check at one explicit coupling**: `BoxPatch.BoxPatchGap hN (1/241920) 80 (1/2)`,
above the threshold `(40 · 80 − 36)/80² = 791/1600`.

DERIVED: `1/241920` is `boxPatchGap_small`'s largest coupling; `80` is its side; `1/2` is
`1 − 120960/241920`; `0` is the excluded rank in `hN`. -/
theorem boxPatchGap_at (hN : N ≠ 0) : BoxPatch.BoxPatchGap hN (1 / 241920) 80 (1 / 2) := by
  have h := boxPatchGap_small hN (β := 1 / 241920) (by norm_num) le_rfl
  rwa [show (1 : ℝ) - 120960 * (1 / 241920) = 1 / 2 by norm_num] at h

#print axioms boxPatchGap_at

/-- **The finite-size route gives an IR gap at a positive coupling.** At `1 ≤ N`, the box check of
`boxPatchGap_at` gives `0 < boxRate N (1/241920) 80 (1/2)` and the IR gap
`UVIRSplit.IRGapAt τ p hN (1/241920) (boxRate N (1/241920) 80 (1/2))` (`HeatBathLocal.irGapAt_boxRate`).

DERIVED: `1/241920`, `80` and `1/2` are `boxPatchGap_at`'s coupling, side and gap; `1` is the least
colour count; `0` is the excluded rank and the sign of the rate; `4` is the spacetime dimension. -/
theorem irGapAt_small (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) :
    0 < HeatBathLocal.boxRate N (1 / 241920) 80 (1 / 2) ∧
      UVIRSplit.IRGapAt τ p hN (1 / 241920) (HeatBathLocal.boxRate N (1 / 241920) 80 (1 / 2)) :=
  HeatBathLocal.irGapAt_boxRate τ p hN1 hN (by norm_num) (boxPatchGap_at hN)

#print axioms irGapAt_small

end Result

end MassGap.PairCorr
