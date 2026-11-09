import Mathlib
import MassGap.FluxCost
import MassGap.GlueballArea

/-!
# MassGap.AttractCost — the zero-flux gap from tension plus localisation, and what it still needs

At `SU(2)` the run seed is `FluxCost.runSeed_two_iff_vortex`: `RunSeed 2 ↔ ∃ σ A, 0 < σ ∧ ∃ᶠ ℓ,
VortexCostAt σ A ℓ ∧ HiddenCostAt 2 σ A ℓ`. `GlueballArea.hiddenCostAt_of_uniformGlueball` derives the
hidden half (T) from a zero-flux gap clause and a zero-flux count clause. This module asks whether (T) follows
from the vortex half (V) through the attraction picture: a zero-flux excitation is a closed flux configuration
of physical size `R`; flux costs `σ` per length, so the loop costs at least `c σ R`; localising it at `R` costs
at least `c'/R`; so it costs at least `min_R (c σ R + c'/R) = 2 √(c c' σ) > 0`. With no tension (`σ = 0`, the
abelian case) the minimum is `0`.

## 1. Tension plus localisation (real arithmetic, proved)

* `two_sqrt_le_cost`: `c, c', σ ≥ 0`, `R > 0` give `2 √(c c' σ) ≤ c σ R + c'/R`.
* `cost_at_optimum`: for `c, c', σ > 0` the size `R* = √c'/√(cσ)` attains it: `c σ R* + c'/R* = 2 √(c c' σ)`.
* `no_floor_without_tension`: at `σ = 0`, for every `c'≥ 0` and `m > 0` some `R > 0` has `c'/R < m`
  (the localisation cost alone gives no gap).

## 2. On a family of levels (proved)

`LevelsCost g₀ E c c' σ`: every excited level `j ≠ g₀` has some size `R > 0` with
`c σ R + c'/R ≤ E_j − E_{g₀}`.

* `gap_of_levelsCost`: `LevelsCost g₀ E c c' σ ⇒ GlueballArea.ZeroFluxGap g₀ E (2 √(c c' σ))`.
* **`levelsCost_iff_gap`**: for `c, c', σ > 0`, `LevelsCost g₀ E c c' σ ↔ ZeroFluxGap g₀ E (2 √(c c' σ))`.
  With the size chosen per level (existentially), the tension-plus-localisation clause is the gap clause at
  `m = 2 √(c c' σ)`, no more and no less.
* `not_count_of_gap`: on `ι = ℕ` the levels `E₀ = 0`, `E_j = m` (`j ≥ 1`) have `ZeroFluxGap 0 E m` and fail
  `ZeroFluxCount 0 E t₀ C` for every `t₀`, `C`. A gap does not give the count.

## 3. On the lattice (proved, conditional on `AttractAt`)

* `AttractAt σ A c c' t₀ C ℓ`: on the window of `VortexCostAt` (eventually in `β`, powers of two `n ≥ 2`,
  `n a ∈ [2ℓ, 5ℓ]`, `a = aRun 2 β`, every corner step `i`): **if** the vortex deficits of the box certify the
  rate `σ` (`1 − zR (Lc n i) i ν β ≤ A e^{−σ n a}` for every `ν ≠ i`), **then** the real zero-flux kernel
  `trivKN 2 β n i` has spectral levels (`GlueballArea.ZeroFluxLevels`) with `LevelsCost g₀ E c c' σ` and the
  count clause `ZeroFluxCount g₀ E t₀ C`. `c`, `c'`, `t₀`, `C` are fixed before `β`.
* `uniformGlueball_of_attract`: `VortexCostAt σ A ℓ ∧ AttractAt σ A c c' t₀ C ℓ` (`c, c', σ ≥ 0`) give
  `GlueballArea.UniformGlueball 2 (2 √(c c' σ)) t₀ C ℓ`.
* **`hiddenCostAt_of_attract`**: the same with `0 ≤ t₀ ≤ 2ℓ` give
  `HiddenCostAt 2 m (2 C e^{m t₀}) ℓ`, `m = 2 √(c c' σ)`.
* `vortexCostAt_mono`, `hiddenCostAt_two_mono`: both halves weaken under a smaller rate and a larger
  non-negative constant.
* No run-seed capstone is stated from (V) and attraction asked frequently in `ℓ` with one `t₀` and one `C`:
  that hypothesis is refuted by `InputAudit.not_attractRun` under the argued growth of the zero-flux level
  count.
* `attract_of_uniform`: for `c, c', σ > 0`, `UniformGlueball 2 (2 √(c c' σ)) t₀ C ℓ` gives
  `AttractAt σ A c c' t₀ C ℓ` (the antecedent is not used; `levelsCost_iff_gap`).
* **`attract_iff_uniform_of_vortex`**: for `c, c', σ > 0`, under `VortexCostAt σ A ℓ`,
  `AttractAt σ A c c' t₀ C ℓ ↔ UniformGlueball 2 (2 √(c c' σ)) t₀ C ℓ`. So the attraction route is the
  `UniformGlueball` route repackaged: under (V), `AttractAt` is equivalent to `UniformGlueball`.

In `AttractAt` the rate `σ` enters only through the antecedent, the box's own vortex deficits: without (V) at
the box the clause asserts nothing. The size of the gap is not fixed by `σ`: for every `m > 0` and `σ > 0`,
`c = 1/σ`, `c' = (m/2)²` give `2 √(c c' σ) = m`, so `c`, `c'` carry the gap and `σ` only selects the boxes at
which the clause applies.

## Evaluation

* (V) alone does not give (T) uniformly on the class of kernels the sector machinery uses.
  `FiniteReadingFlux.wilson_neutral` (proved) is the obstruction on that class: the Wilson slice tensored with
  a neutral two-state factor `kB ½` has every twisted ratio (half and doubled extent), hence every vortex
  deficit and the flux share, equal to the Wilson slice's, and zero-flux defect
  `trivialDefectN + log(25/17)`; iterating (`twistRatio_tensor`, `zeroDefect_tensor` applied `k` times; not a
  separate declaration) adds `k log(25/17)` with the twist data unchanged. A neutral mode that the centre twists cannot see is the formal form of "photons do not attract":
  it carries no flux, so no tension bound reaches it. This is a statement about the class at fixed `(β, n)`,
  not a refutation of an inequality special to the Wilson `halfKN` (see that module).
* So the extra input must couple the neutral sector to the flux dynamics. `AttractAt` is that coupling in the
  attraction form, and with it (V) gives (T) (`hiddenCostAt_of_attract`, at one window).
* What `AttractAt` contains, measured: by `levelsCost_iff_gap` its cost clause is the gap clause at
  `m = 2 √(c c' σ)`, the size `R` being chosen per level; and by `not_count_of_gap` (on level families in
  general, not on `trivKN`) the count clause does not follow from the gap clause; on the real levels it is an
  independent second input, carried unchanged from `GlueballArea.UniformGlueball` (argued: `hs_eq` gives
  summability only at `t = n a`, not at a fixed `t₀` with `C` uniform in `β`). The attraction argument
  therefore relocates the gap, it does not discharge it: the minimisation over `R` is exact
  (`cost_at_optimum`), so any formulation with a free size is a gap statement. Argued, not a declaration: the
  argument becomes a derivation only when `R_j` is a property read off the real level (for instance the
  physical extent of the eigenfunction `φ_j` of `trivKN`) and the two costs are proved separately on the
  Wilson measure: the tension cost `E_j − E_{g₀} ≥ c σ R_j` (a closed configuration of extent `R_j` costs at
  least `c` times the flux rate that (V) certifies per length; a non-abelian, Yang–Mills-specific statement,
  the converse direction of Tomboulis–Yaffe that `FluxCost` records as absent from the tree), and the
  localisation floor `E_j − E_{g₀} ≥ c'/R_j` at a fixed physical length (where the running coupling enters:
  a level varying on the physical scale `R_j` pays its kinetic cost at `β → ∞` only if the zoom keeps the
  continuum normalisation, the asymptotic-freedom input). Neither is in the tree or in the archive; the nearest, the
  archived `ZeroMode.gap_phys_of_fixed_screen`, converts units of an assumed floor.

DERIVED (module-wide): `2` in `2 √(c c' σ)` is the AM–GM factor (`(√(cσ) R − √c')² ≥ 0`); `[2ℓ, 5ℓ]`, powers
of two and `n ≥ 2` are the window of `FluxCost.VortexCostAt` and `ObserverTheory.HiddenCostAt`; `2 C e^{m t₀}`
is `GlueballArea.hiddenCostAt_of_uniformGlueball`'s constant.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.AttractCost

open Filter MassGap
open MassGap.GapSideVortexRect (zR Lc)
open MassGap.GlueballArea (ZeroFluxLevels ZeroFluxGap ZeroFluxCount UniformGlueball heatW)
open MassGap.FluxCost (VortexCostAt)
open MassGap.ObserverTheory (HiddenCostAt)

/-! ## 1. Tension plus localisation -/

theorem sqrt_split {c c' σ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ) :
    Real.sqrt (c * c' * σ) = Real.sqrt (c * σ) * Real.sqrt c' := by
  rw [← Real.sqrt_mul (mul_nonneg hc hσ)]; congr 1; ring

/-- **Tension plus localisation is at least `2 √(c c' σ)`** at every size `R > 0`. -/
theorem two_sqrt_le_cost {c c' σ R : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hR : 0 < R) :
    2 * Real.sqrt (c * c' * σ) ≤ c * σ * R + c' / R := by
  rw [sqrt_split hc hσ]
  set a := Real.sqrt (c * σ) with ha
  set b := Real.sqrt c' with hb
  have ha2 : a ^ 2 = c * σ := Real.sq_sqrt (mul_nonneg hc hσ)
  have hb2 : b ^ 2 = c' := Real.sq_sqrt hc'
  have e : (a * R - b) ^ 2 = c * σ * R * R - 2 * (a * b) * R + c' := by
    rw [sub_sq, mul_pow, ha2, hb2]; ring
  have key : 2 * (a * b) * R ≤ c * σ * R * R + c' := by
    linarith [sq_nonneg (a * R - b), e]
  calc 2 * (a * b) = 2 * (a * b) * R / R := by rw [eq_div_iff hR.ne']
    _ ≤ (c * σ * R * R + c') / R := div_le_div_of_nonneg_right key hR.le
    _ = c * σ * R + c' / R := by
        rw [div_eq_iff hR.ne', add_mul, div_mul_cancel₀ _ hR.ne']

/-- **The minimum is attained** at `R* = √c'/√(cσ)`. An alias of `FocusZoom.focus_attains`. -/
alias cost_at_optimum := MassGap.FocusZoom.focus_attains

/-- **No tension, no floor**: at `σ = 0` the localisation cost alone falls below every `m > 0`. -/
theorem no_floor_without_tension {c c' m : ℝ} (hc' : 0 ≤ c') (hm : 0 < m) :
    ∃ R : ℝ, 0 < R ∧ c * 0 * R + c' / R < m := by
  have hR : 0 < 2 * (c' + 1) / m := by positivity
  refine ⟨2 * (c' + 1) / m, hR, ?_⟩
  rw [mul_zero, zero_mul, zero_add, div_lt_iff₀ hR]
  have e : m * (2 * (c' + 1) / m) = 2 * (c' + 1) := by field_simp
  rw [e]; linarith

/-! ## 2. On a family of levels -/

section Levels

variable {ι : Type*}

/-- **Tension plus localisation on a family of levels**: every excited level has a size `R > 0` with
`c σ R + c'/R ≤ E_j − E_{g₀}`. -/
def LevelsCost (g₀ : ι) (E : ι → ℝ) (c c' σ : ℝ) : Prop :=
  ∀ j, j ≠ g₀ → ∃ R : ℝ, 0 < R ∧ c * σ * R + c' / R ≤ E j - E g₀

/-- **The gap from tension plus localisation**: `m = 2 √(c c' σ)`. -/
theorem gap_of_levelsCost {g₀ : ι} {E : ι → ℝ} {c c' σ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ)
    (h : LevelsCost g₀ E c c' σ) : ZeroFluxGap g₀ E (2 * Real.sqrt (c * c' * σ)) := by
  intro j hj
  obtain ⟨R, hR, hE⟩ := h j hj
  have := two_sqrt_le_cost hc hc' hσ hR
  linarith

/-- **With a free size, tension plus localisation is the gap clause**: for `c, c', σ > 0`,
`LevelsCost g₀ E c c' σ ↔ ZeroFluxGap g₀ E (2 √(c c' σ))`. -/
theorem levelsCost_iff_gap {g₀ : ι} {E : ι → ℝ} {c c' σ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ) :
    LevelsCost g₀ E c c' σ ↔ ZeroFluxGap g₀ E (2 * Real.sqrt (c * c' * σ)) := by
  refine ⟨gap_of_levelsCost hc.le hc'.le hσ.le, fun h j hj => ?_⟩
  obtain ⟨hR, he⟩ := cost_at_optimum hc hc' hσ
  refine ⟨_, hR, ?_⟩
  rw [he]
  have := h j hj
  linarith

end Levels

/-- **A gap does not give the count**: on `ℕ`, the levels `E₀ = 0`, `E_j = m` (`j ≥ 1`) have gap `m` and fail
the count clause at every `t₀`, `C`. -/
theorem not_count_of_gap (m t₀ C : ℝ) :
    ZeroFluxGap (0 : ℕ) (fun j : ℕ => if j = 0 then 0 else m) m ∧
      ¬ ZeroFluxCount (0 : ℕ) (fun j : ℕ => if j = 0 then 0 else m) t₀ C := by
  refine ⟨fun j hj => by simp [hj], ?_⟩
  rintro ⟨hs, -⟩
  have ht := hs.tendsto_atTop_zero
  have hev : heatW (0 : ℕ) (fun j : ℕ => if j = 0 then 0 else m) t₀
      =ᶠ[atTop] fun _ => Real.exp (-(m * t₀)) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj0 : j ≠ 0 := by omega
    simp [heatW, hj0]
  have h0 := tendsto_nhds_unique (ht.congr' hev) tendsto_const_nhds
  exact (Real.exp_pos _).ne' h0.symm

/-! ## 3. On the lattice -/

/-- **Attraction at the window**: if the box's vortex deficits certify the rate `σ`, the real zero-flux
kernel has spectral levels paying tension plus localisation, with the count clause at `(t₀, C)`.

DERIVED: `2` and `5` the window `[2ℓ, 5ℓ]` of `FluxCost.VortexCostAt` (`5` leaves room for the power of two at
or above `⌈2ℓ/a⌉`, which is below `4ℓ + 2a`); `2` also the rank and the least side; `4` the dimension; `1` the
unit ratio. -/
def AttractAt (σ A c c' t₀ C ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun 2 β → (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ 5 * ℓ →
    ∀ i : Fin 4,
      (∀ ν : {j : Fin 4 // j ≠ i},
        1 - zR (Lc n i) i ν.1 β ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun 2 β)))) →
      ∃ (ι : Type) (g₀ : ι) (E : ι → ℝ),
        ZeroFluxLevels 2 β n i g₀ E ∧ LevelsCost g₀ E c c' σ ∧ ZeroFluxCount g₀ E t₀ C

/-- **(V) and attraction give the uniform glueball statement** at `m = 2 √(c c' σ)`. -/
theorem uniformGlueball_of_attract {σ A c c' t₀ C ℓ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ)
    (hV : VortexCostAt σ A ℓ) (hA : AttractAt σ A c c' t₀ C ℓ) :
    UniformGlueball 2 (2 * Real.sqrt (c * c' * σ)) t₀ C ℓ := by
  filter_upwards [hV, hA] with β hVβ hAβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, hL, hcost, hC⟩ := hAβ n hn h2 hlo hhi i (fun ν => hVβ n hn h2 hlo hhi i ν)
  exact ⟨ι, g₀, E, hL, gap_of_levelsCost hc hc' hσ hcost, hC⟩

/-- **The uniform glueball statement gives attraction** at `m = 2 √(c c' σ)`, for `c, c', σ > 0`: the
antecedent (the box's vortex deficits) is not used, and the cost clause is `levelsCost_iff_gap`. -/
theorem attract_of_uniform {σ A c c' t₀ C ℓ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ)
    (h : UniformGlueball 2 (2 * Real.sqrt (c * c' * σ)) t₀ C ℓ) : AttractAt σ A c c' t₀ C ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hhi i _
  obtain ⟨ι, g₀, E, hL, hg, hC⟩ := hβ n hn h2 hlo hhi i
  exact ⟨ι, g₀, E, hL, (levelsCost_iff_gap hc hc' hσ).mpr hg, hC⟩

/-- **Under (V), attraction is the uniform glueball statement** at `m = 2 √(c c' σ)`, for `c, c', σ > 0`. -/
theorem attract_iff_uniform_of_vortex {σ A c c' t₀ C ℓ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ)
    (hV : VortexCostAt σ A ℓ) :
    AttractAt σ A c c' t₀ C ℓ ↔ UniformGlueball 2 (2 * Real.sqrt (c * c' * σ)) t₀ C ℓ :=
  ⟨uniformGlueball_of_attract hc.le hc'.le hσ.le hV, attract_of_uniform hc hc' hσ⟩

/-- **(V) and attraction give the hidden half** at rate `m = 2 √(c c' σ)`, constant `2 C e^{m t₀}`. -/
theorem hiddenCostAt_of_attract {σ A c c' t₀ C ℓ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ)
    (ht₀ : 0 ≤ t₀) (hℓ : t₀ ≤ 2 * ℓ) (hV : VortexCostAt σ A ℓ) (hA : AttractAt σ A c c' t₀ C ℓ) :
    HiddenCostAt 2 (2 * Real.sqrt (c * c' * σ))
      (2 * C * Real.exp (2 * Real.sqrt (c * c' * σ) * t₀)) ℓ :=
  GlueballArea.hiddenCostAt_of_uniformGlueball ht₀ hℓ (uniformGlueball_of_attract hc hc' hσ hV hA)

/-- A smaller rate and a larger non-negative constant weaken `A e^{−σ x}` at `x ≥ 0`. -/
theorem bound_mono {A A' σ σ' x : ℝ} (hA : A ≤ A') (hA' : 0 ≤ A') (hσ : σ' ≤ σ) (hx : 0 ≤ x) :
    A * Real.exp (-(σ * x)) ≤ A' * Real.exp (-(σ' * x)) := by
  have h1 : σ' * x ≤ σ * x := mul_le_mul_of_nonneg_right hσ hx
  calc A * Real.exp (-(σ * x)) ≤ A' * Real.exp (-(σ * x)) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ ≤ A' * Real.exp (-(σ' * x)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA'

theorem vortexCostAt_mono {σ σ' A A' ℓ : ℝ} (hσ : σ' ≤ σ) (hA : A ≤ A') (hA' : 0 ≤ A')
    (h : VortexCostAt σ A ℓ) : VortexCostAt σ' A' ℓ := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
  have ha := AsymptoticScaling.aRun_pos (N := 2) (by norm_num) hβ0
  exact (hβ n hn h2 hlo hup i ν).trans (bound_mono hA hA' hσ (by positivity))

theorem hiddenCostAt_two_mono {σ σ' A A' ℓ : ℝ} (hσ : σ' ≤ σ) (hA : A ≤ A') (hA' : 0 ≤ A')
    (h : HiddenCostAt 2 σ A ℓ) : HiddenCostAt 2 σ' A' ℓ := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i
  have ha := AsymptoticScaling.aRun_pos (N := 2) (by norm_num) hβ0
  exact (hβ n hn h2 hlo hup i).trans (bound_mono hA hA' hσ (by positivity))

end MassGap.AttractCost

end

#print axioms MassGap.AttractCost.two_sqrt_le_cost
#print axioms MassGap.AttractCost.cost_at_optimum
#print axioms MassGap.AttractCost.no_floor_without_tension
#print axioms MassGap.AttractCost.gap_of_levelsCost
#print axioms MassGap.AttractCost.levelsCost_iff_gap
#print axioms MassGap.AttractCost.not_count_of_gap
#print axioms MassGap.AttractCost.uniformGlueball_of_attract
#print axioms MassGap.AttractCost.attract_of_uniform
#print axioms MassGap.AttractCost.attract_iff_uniform_of_vortex
#print axioms MassGap.AttractCost.hiddenCostAt_of_attract
#print axioms MassGap.AttractCost.vortexCostAt_mono
#print axioms MassGap.AttractCost.hiddenCostAt_two_mono
