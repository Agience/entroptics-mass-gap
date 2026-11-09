import Mathlib
import MassGap.TransverseTunnel
import MassGap.ZeroFluxSector

/-!
# MassGap.CentreOdds — inequality (T) split over the centre sectors: the zero-flux corner function and the flux odds

`AxisSplit.TransverseDouble x` is inequality (T), `0 ≤ mixed x μ ν v` for `μ ≠ ν`
(`AxisSplit.transverseDouble_iff`). This module splits it over the electric-flux sectors of the centre. Declarations
are in the namespace `MassGap.CentreOdds`.

## The split

Fix a transfer direction `i`. The centre `G` (for `SU(N)`, `Z_N³` on the three transverse directions,
`SliceCentreAction`) acts on the `i`-slices, and the trace of the transfer splits into the zero-flux trace `Z₁` and the
rest (`ZeroFluxSector`). Write the flux odds `R = (Z − Z₁)/Z₁ = Σ_{ψ ≠ 1} Z_ψ/Z₁ ≥ 0`. Then `log Z = log Z₁ + log(1 + R)`
(`log_hs_split`), and the mixed second difference is additive:

    mixed x μ ν v = mixed (log Z₁) μ ν v + oddsMixed R₀₀ R₁₀ R₀₁ R₁₁,

with `R₀₀ = R(v)`, `R₁₀ = R(v + e_μ)`, `R₀₁ = R(v + e_ν)`, `R₁₁ = R(v + e_μ + e_ν)` and
`oddsMixed = log(1 + R₁₁) − 2 log(1 + R₁₀) − 2 log(1 + R₀₁) + 4 log(1 + R₀₀)` (`mixed_of_split`). The corner function is
the same for every transfer direction, so each pair `(μ, ν)` may be read with `i = μ`.

## What is proved

* `mixed_of_split`, `transverseDouble_of_split`: if for each `μ` the corner function is `y_μ + log(1 + R_μ)`, then (T)
  holds once `y_μ` satisfies (T) at every pair `(μ, ν)` and `oddsMixed ≥ 0` for `R_μ` at every pair.
* `oddsMixed_nonneg_iff`, `oddsMixed_neg_iff`: for nonnegative odds, `oddsMixed ≥ 0` is the product inequality
  `(1 + R₁₀)²(1 + R₀₁)² ≤ (1 + R₁₁)(1 + R₀₀)⁴`.
* `oddsMixed_nonneg_of_anti`: odds that do not increase under either doubling give `oddsMixed ≥ 0`.
* `oddsMixed_nonneg_of_tube` (the flux-tube law): with `r = R₀₀ ≥ 0`, the four conditions
  - transfer doubling squares the odds up to a tolerance, `R₁₀ (1 + 2r)² ≤ r² (2 + 4r + r²)`;
  - transverse doubling at most doubles them, `R₀₁ ≤ 2r`;
  - transverse doubling does not lower them at the doubled corner, `R₁₀ ≤ R₁₁`;
  - nonnegativity,
  give `oddsMixed ≥ 0`. `oddsMixed_nonneg_of_tube_sq`: the first holds when `R₁₀ ≤ r²` and `3r² ≤ 1`.
* `odds_conv_le_ratio`: on a centre-invariant kernel the transfer doubling gives `R[a ∗ a] ≤ k/(1 − k)`,
  `k = R[a]² · exp(dd(zk a)) < 1`, from `ZeroFluxSector.odds_conv_le_zk`. The squaring is in the tree; its cost is the
  zero-flux sector's own doubling defect.
* `floor_needed`: the floor `R₁₀ ≤ R₁₁` cannot be dropped. At `r = 1/2`, `R₁₀ = r²`, `R₀₁ = 2r`, `R₁₁ = 0`,
  `oddsMixed < 0`.
* `coulomb_odds_neg`, `confined_odds_nonneg`: at `r = 1/16`, the Coulomb law `R₁₀ = r²`, `R₀₁ = √r`, `R₁₁ = r`
  gives `oddsMixed < 0`; the tube law `R₁₀ = r²`, `R₀₁ = 2r`, `R₁₁ = 2r²` gives `oddsMixed ≥ 0`.
* `tunX_split`, `tunBulk_mixed`, `tunX_mixed_eq_odds`, `tunOdds_rise`: the corner function of `TransverseTunnel` is
  `tunBulk + log(1 + tunOdds)` with `tunOdds = tanh(κ)^N` the odd-sector odds of the Ising ring. The bulk part has
  `mixed = 0` at every corner of the pair `(0, 1)`, so the failure `TransverseTunnel.mixed_tunX_neg` is entirely
  `oddsMixed`. At the failing corner the transverse doubling multiplies the odds from `(3/5)⁴` to `(15/17)⁴`, more than
  twice: the multiplicity bound of the tube law fails there.

## Where the centre enters

The sector split itself holds for any finite abelian group acting on the slices: `Z_N ⊂ U(1)` acts on `U(1)` links the
same way, and every theorem above is group-blind. The `SU(N)`-specific content can only sit in the hypotheses of the
tube law, and the step where it sits is the transverse multiplicity bound `R₀₁ ≤ 2 R₀₀`.

Argued, not proved: in a confining phase the electric flux `ψ` along `ρ` costs `σ L_i L_ρ`, independent of the
cross-section, and the trace counts the tube's transverse positions, so a transverse doubling multiplies the odds by
about `2`. In the `U(1)` Coulomb phase the same flux costs `g²|e|² L_i L_ρ/(2 A)` with `A` the cross-section, so a
transverse doubling of `A` takes `R` to about `√R`, far above `2R` at small `R`. `coulomb_odds_neg` shows that this
spreading breaks the odds part of (T); `confined_odds_nonneg` shows that the tube law at the same `r` does not. For
`SU(N)` the flux is a `Z_N` label that gluons cannot screen, and confinement is the statement that it does not spread.
Nothing in the centre structure proves that it does not spread: `R₀₁ ≤ 2R₀₀` is a dynamical input.

## The remaining inequalities

For each pair `(μ, ν)`, read along `i = μ`:

* (T₁) the zero-flux corner function `log Z₁^{(μ)}` satisfies (T) at `(μ, ν)`;
* (O) the tube law for `R^{(μ)}`: `R₀₁ ≤ 2R₀₀` (no spreading), `R₁₀ ≤ R₁₁` (floor), and the transfer squaring within
  the tolerance. `odds_conv_le_ratio` gives the last up to the factor `exp(dd(zk))` and the `1/(1 − k)` correction.
  Without that correction, `R₁₀ ≤ r² exp(dd zk)` implies the tolerance whenever
  `exp(dd zk) ≤ (2 + 4r + r²)/(1 + 2r)²`, and that is the exact condition at its worst case `R₁₀ = r² exp(dd zk)`. The ratio decreases in `r`, so it is `≥ 17/16` for `r ≤ 1/2` and the
  condition holds there whenever `dd(zk) ≤ log(17/16)`.

(T₁) is (T) for the trivial-flux corner function, an inequality of the same shape as (T). It is not (S), (M), `RelLip`,
(L) or the next-window floor. (O) has three parts: the squaring is the zero-flux defect (`dd(zk)`), which
`ZeroFluxSector.dd_le_zk` already shows controls `dd` modulo the odds, so it is circular with the defect; the multiplicity
bound is an upper bound on a sector trace of the transversely doubled torus, and the floor a lower bound on one. Neither
is given by reflection positivity in the transfer direction.

## What does not follow

* (T) is not proved: the module trades it for (T₁) and (O).
* The gap: the odds bound `dd(a)` only with the zero-flux defect added (`ZeroFluxSector.dd_le_zk`). The zero-flux
  sector is centre-neutral, and the `U(1)` photon lives in it, so no bound on the flux sectors reaches the zero-flux
  rate.
* The count (Cnt) of `LevelRate` is not read here.
* The physical laws quoted above (tube, Coulomb) are argued; the Lean statements are the four-value inequalities.

DERIVED (module-wide): `2`, `4` the coefficients of the mixed second difference; `2` in `2r` the doubled count of
transverse tube positions; `2 + 4r + r²` and `(1 + 2r)²` from `(1 + r)⁴ = (1 + 2r)² + r²(2 + 4r + r²)`; `3` in `3r² ≤ 1`
from `(1 + 2r)² ≤ 2 + 4r + r² ⇔ 3r² ≤ 1`; `17/16 = (2 + 2 + 1/4)/(1 + 1)²` the tolerance ratio at `r = 1/2`;
`3` in `Z_N³` the transverse directions and `4` in `Fin 4` the dimension, structural counts.
CHOSEN: `1/2` the test odds of `floor_needed`, and the range endpoint `r ≤ 1/2` at which `17/16` is evaluated; `1/16` the test odds of `coulomb_odds_neg` and `confined_odds_nonneg`.
COMPUTED: `1/256 = (1/16)²`, `1/4 = √(1/16)`, `1/8 = 2 · 1/16`, `1/128 = 2 · 1/256`; `3/5`, `15/17` the ratios
`tanh(log 2)`, `tanh(2 log 2)` of `TransverseTunnel` at `K = log 2`, from `e^{log 2} = 2`, `e^{2 log 2} = 4`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CentreOdds

open MassGap.DoublingRecursion MassGap.CasimirStep MassGap.AxisSplit MassGap.TransverseTunnel

/-! ## 1. The odds part of the mixed second difference -/

/-- **The odds part of `mixed`.** DERIVED: `2`, `4` the coefficients of the mixed second difference. -/
def oddsMixed (r r10 r01 r11 : ℝ) : ℝ :=
  Real.log (1 + r11) - 2 * Real.log (1 + r10) - 2 * Real.log (1 + r01) + 4 * Real.log (1 + r)

/-- **`mixed` is additive over the split `x = y + log(1 + R)`.** DERIVED: `1` the trivial sector. -/
theorem mixed_of_split {x y R : Pt → ℝ} (h : ∀ u, x u = y u + Real.log (1 + R u)) (μ ν : Fin 4) (v : Pt) :
    mixed x μ ν v = mixed y μ ν v + oddsMixed (R v) (R (v + E μ)) (R (v + E ν)) (R (v + E μ + E ν)) := by
  simp only [mixed, oddsMixed, h]
  ring

/-- **(T) from the split.** If for every transfer direction `μ` the corner function is `y μ + log(1 + R μ)`, (T) for
`y μ` at the pairs `(μ, ν)` and `oddsMixed ≥ 0` for `R μ` at the same pairs give (T). DERIVED: `0` the sign. -/
theorem transverseDouble_of_split {x : Pt → ℝ} (y R : Fin 4 → Pt → ℝ)
    (h : ∀ μ u, x u = y μ u + Real.log (1 + R μ u))
    (hy : ∀ μ ν v, μ ≠ ν → 0 ≤ mixed (y μ) μ ν v)
    (hR : ∀ μ ν v, μ ≠ ν →
      0 ≤ oddsMixed (R μ v) (R μ (v + E μ)) (R μ (v + E ν)) (R μ (v + E μ + E ν))) :
    TransverseDouble x := by
  rw [transverseDouble_iff]
  intro μ ν v hμν
  rw [mixed_of_split (h μ) μ ν v]
  linarith [hy μ ν v hμν, hR μ ν v hμν]

/-- `oddsMixed` as the log of a ratio, for nonnegative odds. DERIVED: `2`, `4` the powers. -/
theorem oddsMixed_eq_log {r r10 r01 r11 : ℝ} (h : 0 ≤ r) (h10 : 0 ≤ r10) (h01 : 0 ≤ r01) (h11 : 0 ≤ r11) :
    oddsMixed r r10 r01 r11
      = Real.log ((1 + r11) * (1 + r) ^ 4) - Real.log ((1 + r10) ^ 2 * (1 + r01) ^ 2) := by
  have a : (0 : ℝ) < 1 + r := by linarith
  have a10 : (0 : ℝ) < 1 + r10 := by linarith
  have a01 : (0 : ℝ) < 1 + r01 := by linarith
  have a11 : (0 : ℝ) < 1 + r11 := by linarith
  unfold oddsMixed
  rw [Real.log_mul a11.ne' (pow_ne_zero _ a.ne'), Real.log_mul (pow_ne_zero _ a10.ne') (pow_ne_zero _ a01.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **`oddsMixed ≥ 0` is a product inequality.** DERIVED: `2`, `4` the powers. -/
theorem oddsMixed_nonneg_iff {r r10 r01 r11 : ℝ} (h : 0 ≤ r) (h10 : 0 ≤ r10) (h01 : 0 ≤ r01) (h11 : 0 ≤ r11) :
    0 ≤ oddsMixed r r10 r01 r11 ↔ (1 + r10) ^ 2 * (1 + r01) ^ 2 ≤ (1 + r11) * (1 + r) ^ 4 := by
  have a : (0 : ℝ) < 1 + r := by linarith
  have a10 : (0 : ℝ) < 1 + r10 := by linarith
  have a01 : (0 : ℝ) < 1 + r01 := by linarith
  have a11 : (0 : ℝ) < 1 + r11 := by linarith
  rw [oddsMixed_eq_log h h10 h01 h11, sub_nonneg]
  exact Real.log_le_log_iff (mul_pos (pow_pos a10 2) (pow_pos a01 2)) (mul_pos a11 (pow_pos a 4))

/-- **`oddsMixed < 0` is the reverse product inequality.** DERIVED: `2`, `4` the powers. -/
theorem oddsMixed_neg_iff {r r10 r01 r11 : ℝ} (h : 0 ≤ r) (h10 : 0 ≤ r10) (h01 : 0 ≤ r01) (h11 : 0 ≤ r11) :
    oddsMixed r r10 r01 r11 < 0 ↔ (1 + r11) * (1 + r) ^ 4 < (1 + r10) ^ 2 * (1 + r01) ^ 2 := by
  have a : (0 : ℝ) < 1 + r := by linarith
  have a10 : (0 : ℝ) < 1 + r10 := by linarith
  have a01 : (0 : ℝ) < 1 + r01 := by linarith
  have a11 : (0 : ℝ) < 1 + r11 := by linarith
  rw [oddsMixed_eq_log h h10 h01 h11, sub_neg]
  exact Real.log_lt_log_iff (mul_pos a11 (pow_pos a 4)) (mul_pos (pow_pos a10 2) (pow_pos a01 2))

/-! ## 2. Laws for the odds -/

/-- **Odds that do not increase under either doubling satisfy the odds part of (T).** DERIVED: `2`, `4` the
powers. -/
theorem oddsMixed_nonneg_of_anti {r r10 r01 r11 : ℝ} (h10 : 0 ≤ r10) (h01 : 0 ≤ r01) (h11 : 0 ≤ r11)
    (hμ : r10 ≤ r) (hν : r01 ≤ r) : 0 ≤ oddsMixed r r10 r01 r11 := by
  have h : 0 ≤ r := le_trans h10 hμ
  rw [oddsMixed_nonneg_iff h h10 h01 h11]
  have a10 : (0 : ℝ) ≤ 1 + r10 := by linarith
  have a01 : (0 : ℝ) ≤ 1 + r01 := by linarith
  calc (1 + r10) ^ 2 * (1 + r01) ^ 2 ≤ (1 + r) ^ 2 * (1 + r) ^ 2 := by gcongr
    _ = 1 * (1 + r) ^ 4 := by ring
    _ ≤ (1 + r11) * (1 + r) ^ 4 := by gcongr; linarith

/-- **The flux-tube law.** Transfer doubling squares the odds within the tolerance
`R₁₀ (1 + 2r)² ≤ r² (2 + 4r + r²)`, transverse doubling at most doubles them (`R₀₁ ≤ 2r`), and does not lower them at
the doubled corner (`R₁₀ ≤ R₁₁`): then `oddsMixed ≥ 0`. DERIVED: `2` the doubled count of transverse positions;
`2 + 4r + r²` from `(1 + r)⁴ = (1 + 2r)² + r²(2 + 4r + r²)`. -/
theorem oddsMixed_nonneg_of_tube {r r10 r01 r11 : ℝ} (h : 0 ≤ r) (h10 : 0 ≤ r10) (h01 : 0 ≤ r01)
    (hmult : r01 ≤ 2 * r) (hfloor : r10 ≤ r11)
    (hsq : r10 * (1 + 2 * r) ^ 2 ≤ r ^ 2 * (2 + 4 * r + r ^ 2)) :
    0 ≤ oddsMixed r r10 r01 r11 := by
  have h11 : 0 ≤ r11 := le_trans h10 hfloor
  rw [oddsMixed_nonneg_iff h h10 h01 h11]
  have a10 : (0 : ℝ) ≤ 1 + r10 := by linarith
  have a01 : (0 : ℝ) ≤ 1 + r01 := by linarith
  have e2 : (1 + r10) * (1 + 2 * r) ^ 2 ≤ (1 + r) ^ 4 := by nlinarith [hsq]
  calc (1 + r10) ^ 2 * (1 + r01) ^ 2 ≤ (1 + r10) ^ 2 * (1 + 2 * r) ^ 2 := by gcongr
    _ = (1 + r10) * ((1 + r10) * (1 + 2 * r) ^ 2) := by ring
    _ ≤ (1 + r11) * (1 + r) ^ 4 :=
        mul_le_mul (by linarith) e2 (mul_nonneg a10 (sq_nonneg _)) (by linarith)

/-- **The tube law with exact squaring.** `R₁₀ ≤ r²` and `3r² ≤ 1` give the tolerance of `oddsMixed_nonneg_of_tube`.
DERIVED: `3` from `(1 + 2r)² ≤ 2 + 4r + r² ⇔ 3r² ≤ 1`. -/
theorem oddsMixed_nonneg_of_tube_sq {r r10 r01 r11 : ℝ} (h : 0 ≤ r) (h10 : 0 ≤ r10) (h01 : 0 ≤ r01)
    (hmult : r01 ≤ 2 * r) (hfloor : r10 ≤ r11) (hsq : r10 ≤ r ^ 2) (hr : 3 * r ^ 2 ≤ 1) :
    0 ≤ oddsMixed r r10 r01 r11 := by
  refine oddsMixed_nonneg_of_tube h h10 h01 hmult hfloor ?_
  calc r10 * (1 + 2 * r) ^ 2 ≤ r ^ 2 * (1 + 2 * r) ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ ≤ r ^ 2 * (2 + 4 * r + r ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg r)

/-- **The floor cannot be dropped.** At `r = 1/2` with `R₁₀ = r²`, `R₀₁ = 2r` and `R₁₁ = 0` every other hypothesis of
`oddsMixed_nonneg_of_tube_sq` holds, the odds are nonnegative, and `oddsMixed < 0`. CHOSEN: `1/2` the test odds. COMPUTED: `1/4 = (1/2)²`,
`1 = 2 · 1/2`; `3` as in `oddsMixed_nonneg_of_tube_sq`. -/
theorem floor_needed :
    (0 : ℝ) ≤ 1 / 2 ∧ (0 : ℝ) ≤ 1 / 4 ∧ (0 : ℝ) ≤ 1 ∧
      (1 / 4 : ℝ) ≤ (1 / 2) ^ 2 ∧ (1 : ℝ) ≤ 2 * (1 / 2) ∧ 3 * (1 / 2 : ℝ) ^ 2 ≤ 1 ∧
      oddsMixed (1 / 2) (1 / 4) 1 0 < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [oddsMixed_neg_iff (by norm_num) (by norm_num) (by norm_num) le_rfl]
  norm_num

/-- **Coulomb odds break the odds part of (T).** At `r = 1/16`: `R₁₀ = r²` (the flux doubles in length), `R₀₁ = √r`
(the flux spreads over a doubled cross-section), `R₁₁ = r`. The multiplicity bound fails (`2r < R₀₁`) and
`oddsMixed < 0`. CHOSEN: `1/16` the test odds. COMPUTED: `1/256 = (1/16)²`, `1/4 = √(1/16)`, `1/8 = 2 · 1/16`. -/
theorem coulomb_odds_neg :
    (1 / 256 : ℝ) = (1 / 16) ^ 2 ∧ (1 / 4 : ℝ) ^ 2 = 1 / 16 ∧ 2 * (1 / 16 : ℝ) < 1 / 4 ∧
      oddsMixed (1 / 16) (1 / 256) (1 / 4) (1 / 16) < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [oddsMixed_neg_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Tube odds at the same scale satisfy it.** At `r = 1/16`: `R₁₀ = r²`, `R₀₁ = 2r`, `R₁₁ = 2r²`. CHOSEN: `1/16`
the test odds. COMPUTED: `1/256 = (1/16)²`, `1/8 = 2 · 1/16`, `1/128 = 2 · 1/256`; `3` as in
`oddsMixed_nonneg_of_tube_sq`. -/
theorem confined_odds_nonneg : 0 ≤ oddsMixed (1 / 16) (1 / 256) (1 / 8) (1 / 128) :=
  oddsMixed_nonneg_of_tube_sq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ## 3. The centre split of a kernel -/

section Kernel

open MeasureTheory MassGap.KernelPower MassGap.FluxSectorFourier MassGap.ZeroFluxSector MassGap.SectorDefect

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {act : G → X → X} {a : X → X → ℝ}

variable (μ) in
/-- **The flux odds** `R = (Z − Z₁)/Z₁` of a kernel under a centre action. DERIVED: `1` the trivial character. -/
def odds (a : X → X → ℝ) (act : G → X → X) : ℝ := (hs μ a - hs μ (zk a act)) / hs μ (zk a act)

/-- The flux odds are nonnegative. DERIVED: `0` the sign. -/
theorem odds_nonneg (ha : Bdd a) (hA : CentreAction μ act) (hpos : 0 < hs μ (zk a act)) :
    0 ≤ odds μ a act :=
  div_nonneg (by linarith [hs_zk_le ha hA]) hpos.le

/-- **The centre split of the trace**: `log Z = log Z₁ + log(1 + R)`. DERIVED: `1` the trivial sector. -/
theorem log_hs_split (ha : Bdd a) (hA : CentreAction μ act) (hpos : 0 < hs μ (zk a act)) :
    Real.log (hs μ a) = Real.log (hs μ (zk a act)) + Real.log (1 + odds μ a act) := by
  have hZ : 0 < hs μ a := lt_of_lt_of_le hpos (hs_zk_le ha hA)
  have e : 1 + odds μ a act = hs μ a / hs μ (zk a act) := by
    unfold odds
    field_simp
    ring
  rw [e, Real.log_div hZ.ne' hpos.ne']
  ring

/-- **Doubling the transfer squares the odds, at the cost of the zero-flux defect**. It is the odds form
`R′ = s/(1 − s)` of the share bound `ZeroFluxSector.odds_conv_le_zk`:
`R[a ∗ a] ≤ k/(1 − k)` with `k = R[a]² · exp(dd(zk a)) < 1`; `c > 0` is the lower bound of the kernel. DERIVED: `2`
the square; `1` the trivial sector. -/
theorem odds_conv_le_ratio {c : ℝ} (hc : 0 < c) (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) (hinv : ∀ g x y, a (act g x) (act g y) = a x y)
    (hlow : ∀ x y, c ≤ a x y)
    (h1 : odds μ a act ^ 2 * Real.exp (dd μ (zk a act)) < 1) :
    odds μ (conv μ a a) act
      ≤ odds μ a act ^ 2 * Real.exp (dd μ (zk a act)) / (1 - odds μ a act ^ 2 * Real.exp (dd μ (zk a act))) := by
  have hshare := odds_conv_le_zk hc ha hsym hA hinv hlow
  set k := odds μ a act ^ 2 * Real.exp (dd μ (zk a act)) with hk
  have hk' : ((hs μ a - hs μ (zk a act)) / hs μ (zk a act)) ^ 2 * Real.exp (dd μ (zk a act)) = k := rfl
  rw [hk'] at hshare
  have hz : 0 < hs μ (zk (conv μ a a) act) := by
    rw [zk_conv ha hA hinv]; exact hs_conv_zk_pos hc ha hA hlow
  have hle : hs μ (zk (conv μ a a) act) ≤ hs μ (conv μ a a) := by
    rw [zk_conv ha hA hinv]; exact hs_conv_zk_le ha hsym hA hinv
  have hZ : 0 < hs μ (conv μ a a) := lt_of_lt_of_le hz hle
  rw [div_le_iff₀ hZ] at hshare
  unfold odds
  rw [div_le_div_iff₀ hz (by linarith)]
  nlinarith

end Kernel

/-! ## 4. The tunnelling corner function is a bulk part plus odds -/

/-- The bulk part of `tunX`: `N log(2 cosh κ)`. DERIVED: `2^{u_1}` the ring length `N`; `2` in `2 cosh κ` from
`tunCp κ = e^κ + e^{−κ}`. -/
def tunBulk (K : ℝ) (u : Pt) : ℝ := ((2 ^ u 1 : ℕ) : ℝ) * Real.log (tunCp (K * 2 ^ tunSlab u))

/-- The odd-sector odds of `tunX`: `tanh(κ)^N`. DERIVED: `2^{u_1}` the ring length `N`. -/
def tunOdds (K : ℝ) (u : Pt) : ℝ := (tunCm (K * 2 ^ tunSlab u) / tunCp (K * 2 ^ tunSlab u)) ^ (2 ^ u 1)

/-- **`tunX = tunBulk + log(1 + tunOdds)`.** DERIVED: `1` the even sector. -/
theorem tunX_split {K : ℝ} (hK : 0 ≤ K) (u : Pt) : tunX K u = tunBulk K u + Real.log (1 + tunOdds K u) := by
  unfold tunX tunZ tunBulk tunOdds
  have hκ : 0 ≤ K * 2 ^ tunSlab u := mul_nonneg hK (by positivity)
  have hp := tunCp_pos (K * 2 ^ tunSlab u)
  have hm := tunCm_nonneg hκ
  have hq : 0 < 1 + (tunCm (K * 2 ^ tunSlab u) / tunCp (K * 2 ^ tunSlab u)) ^ 2 ^ u 1 := by
    have : 0 ≤ (tunCm (K * 2 ^ tunSlab u) / tunCp (K * 2 ^ tunSlab u)) ^ 2 ^ u 1 :=
      pow_nonneg (div_nonneg hm hp.le) _
    linarith
  have e : tunCp (K * 2 ^ tunSlab u) ^ 2 ^ u 1 + tunCm (K * 2 ^ tunSlab u) ^ 2 ^ u 1
      = tunCp (K * 2 ^ tunSlab u) ^ 2 ^ u 1
        * (1 + (tunCm (K * 2 ^ tunSlab u) / tunCp (K * 2 ^ tunSlab u)) ^ 2 ^ u 1) := by
    rw [div_pow]
    field_simp
  rw [e, Real.log_mul (pow_ne_zero _ hp.ne') hq.ne', Real.log_pow]

/-- **The bulk part does not see the pair `(0, 1)`**: `mixed tunBulk 0 1 v = 0` at every corner. DERIVED: `0`, `1` the
two directions; `2` the doubling. -/
theorem tunBulk_mixed (K : ℝ) (v : Pt) : mixed (tunBulk K) 0 1 v = 0 := by
  have a1 : (v + E 0 + E 1) 1 = v 1 + 1 := by simp [E_apply]
  have a2 : tunSlab (v + E 0 + E 1) = tunSlab v + 1 := by simp [tunSlab, E_apply]; ring
  have a3 : (v + E 0) 1 = v 1 := by simp [E_apply]
  have a4 : tunSlab (v + E 0) = tunSlab v + 1 := by simp [tunSlab, E_apply]; ring
  have a5 : (v + E 1) 1 = v 1 + 1 := by simp [E_apply]
  have a6 : tunSlab (v + E 1) = tunSlab v := by simp [tunSlab, E_apply]
  unfold mixed tunBulk
  rw [a1, a2, a3, a4, a5, a6]
  push_cast
  ring

/-- **The tunnelling failure is all odds**: `mixed tunX 0 1 v = oddsMixed` of `tunOdds`. DERIVED: `0`, `1` the two
directions. -/
theorem tunX_mixed_eq_odds {K : ℝ} (hK : 0 ≤ K) (v : Pt) :
    mixed (tunX K) 0 1 v = oddsMixed (tunOdds K v) (tunOdds K (v + E 0)) (tunOdds K (v + E 1))
      (tunOdds K (v + E 0 + E 1)) := by
  rw [mixed_of_split (fun u => tunX_split hK u) 0 1 v, tunBulk_mixed]
  ring

/-- **At the failing corner the transverse doubling more than doubles the odds**: at `K = log 2`, `v = (0, 2, 0, 0)`,
`tunOdds v = (3/5)⁴` and `tunOdds (v + e_0) = (15/17)⁴ > 2 (3/5)⁴`, and `oddsMixed < 0`. DERIVED: `2` in `(0, 2, 0, 0)`
the coordinate `u_1` of the corner (`N = 2² = 4`); `2` in `2 · tunOdds` the multiplicity bound `R₀₁ ≤ 2R₀₀`; `4` the
ring length. COMPUTED: `3`, `5` in
`3/5 = tanh(log 2)` and `15`, `17` in `15/17 = tanh(2 log 2)`, from `e^{log 2} = 2`, `e^{2 log 2} = 4`. -/
theorem tunOdds_rise :
    tunOdds (Real.log 2) ![0, 2, 0, 0] = (3 / 5) ^ 4 ∧
      tunOdds (Real.log 2) (![0, 2, 0, 0] + E 0) = (15 / 17) ^ 4 ∧
      2 * tunOdds (Real.log 2) ![0, 2, 0, 0] < tunOdds (Real.log 2) (![0, 2, 0, 0] + E 0) ∧
      oddsMixed (tunOdds (Real.log 2) ![0, 2, 0, 0]) (tunOdds (Real.log 2) (![0, 2, 0, 0] + E 0))
        (tunOdds (Real.log 2) (![0, 2, 0, 0] + E 1)) (tunOdds (Real.log 2) (![0, 2, 0, 0] + E 0 + E 1)) < 0 := by
  have hs0 : tunSlab (![0, 2, 0, 0] : Pt) = 0 := by decide
  have hs1 : tunSlab ((![0, 2, 0, 0] : Pt) + E 0) = 1 := by decide
  have hn0 : (![0, 2, 0, 0] : Pt) 1 = 2 := by decide
  have hn1 : ((![0, 2, 0, 0] : Pt) + E 0) 1 = 2 := by decide
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have h4 : Real.exp (Real.log 2 * 2) = 4 := by
    rw [show Real.log 2 * 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by norm_num)
  have o0 : tunOdds (Real.log 2) ![0, 2, 0, 0] = (3 / 5) ^ 4 := by
    unfold tunOdds tunCm tunCp
    rw [hs0, hn0, pow_zero, mul_one, Real.exp_neg, h2]
    norm_num
  have o1 : tunOdds (Real.log 2) (![0, 2, 0, 0] + E 0) = (15 / 17) ^ 4 := by
    unfold tunOdds tunCm tunCp
    rw [hs1, hn1, pow_one, Real.exp_neg, h4]
    norm_num
  refine ⟨o0, o1, ?_, ?_⟩
  · rw [o0, o1]; norm_num
  · rw [← tunX_mixed_eq_odds (Real.log_nonneg (by norm_num))]
    exact mixed_tunX_neg

end MassGap.CentreOdds

end

#print axioms MassGap.CentreOdds.mixed_of_split
#print axioms MassGap.CentreOdds.transverseDouble_of_split
#print axioms MassGap.CentreOdds.oddsMixed_nonneg_iff
#print axioms MassGap.CentreOdds.oddsMixed_neg_iff
#print axioms MassGap.CentreOdds.oddsMixed_nonneg_of_anti
#print axioms MassGap.CentreOdds.oddsMixed_nonneg_of_tube
#print axioms MassGap.CentreOdds.oddsMixed_nonneg_of_tube_sq
#print axioms MassGap.CentreOdds.floor_needed
#print axioms MassGap.CentreOdds.coulomb_odds_neg
#print axioms MassGap.CentreOdds.confined_odds_nonneg
#print axioms MassGap.CentreOdds.log_hs_split
#print axioms MassGap.CentreOdds.odds_conv_le_ratio
#print axioms MassGap.CentreOdds.tunX_split
#print axioms MassGap.CentreOdds.tunBulk_mixed
#print axioms MassGap.CentreOdds.tunX_mixed_eq_odds
#print axioms MassGap.CentreOdds.tunOdds_rise
