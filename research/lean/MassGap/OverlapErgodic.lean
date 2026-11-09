import Mathlib
import MassGap.OverlapFloor

noncomputable section

/-!
# From a gap on the range of the block generator to the floor

A finite-size criterion of Knabe type concludes a gap of the generator on its own range,
`c · B(Hx, x) ≤ B(Hx, Hx)`; the floor (`OverlapSweep.OverlapPoincare`) is a Poincaré inequality on the vacuum
complement. This module converts the first into the second, so that any such criterion feeds
`OverlapFloor.clay_continuum_of_overlapFloorRun`.

## The generic conversion (`poincare_of_rangeGap`)

On a module with a symmetric positive semi-definite form `B`, a form-self-adjoint `H` with `0 ≤ B(Hx, x)`,
`B(Hy, y) ≤ K B(y, y)` (`1 ≤ K`), a unit vector `vac` with `H vac = 0`, and a Poincaré inequality with ANY
constant `C` (`B(v, v) − B(v, vac)² ≤ C B(Hv, v)`): the gap `c` on the range gives
`(c/2) B(u, u) ≤ B(Hu, u)` for every `u ⊥ vac`. With the lazy step `T = id − H/K`:
`B(v, v) − B(Tv, Tv) ≤ (2/K) B(Hv, v)` (`drop_le`), `B(H Tv, Tv) ≤ (1 − c/K) B(Hv, v)` (`gen_contract`), so
`B(u, u) ≤ B(Tᵐu, Tᵐu) + (2/c) B(Hu, u)` at every `m` (`tele_le`); the finite-`C` Poincaré gives
`B(Tᵐu, Tᵐu) ≤ qᵐ B(u, u)`, `q = 1 − 1/(K(C + 1)) < 1` (`var_contract`), and `m → ∞` closes it. The constant `C`
does not enter the result: it only rules out a slow part on which the range gap says nothing.

## The overlapping block dynamics

`ovH = Σ_K (id − E_K)`. `ovH_form`: `B(ovH u, u) = Σ_K ‖u − E_K u‖²`. The finite-extent Poincaré
(`ov_poincare_finite`) comes from the single-link one (`HeatBathLocal.torus_poincare`) through nested projections:
for a link `l` of box `K`, `E_l (E_K v)` and `E_K v` have the same torus reading, so
`‖v − E_l v‖² ≤ ‖v − E_K v‖²` (`nested_le`), and every link lies in a box (`exists_ovBox_mem`).
`overlapPoincare_of_rangeGap`: the range gap `c` of `ovH` at one extent gives `OverlapPoincare` at `c/2` there.
`clay_continuum_of_overlapRangeGapRun`: a range gap `c > 0` of `ovH`, at every large coupling and every large
extent, at cell side `⌈1/(κ aRun β)⌉₊`, with E, N, Y, gives `ClayContinuum`.
-/

namespace MassGap.OverlapErgodic

open MassGap MassGap.KnabeCriterion MassGap.HeatBath MassGap.HeatBathLocal MassGap.BlockHeatBath
open MassGap.OverlapGeometry MassGap.OverlapSweep MassGap.TileSweep MassGap.PeriodicState
open MassGap.SUN (SU)
open Filter

/-! ## 1. The generic conversion -/

section Generic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (H : E →ₗ[ℝ] E)

/-- The lazy step `T v = v − K⁻¹ H v`. DERIVED: no numeral. -/
def lazy (K : ℝ) (v : E) : E := v - K⁻¹ • H v

/-- Expansion of `B(a − t b, a − t b)`. DERIVED: `2` the cross term. -/
theorem form_sub_smul (hsymm : ∀ x y, B x y = B y x) (a b : E) (t : ℝ) :
    B (a - t • b) (a - t • b) = B a a - 2 * t * B b a + t ^ 2 * B b b := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm a b]
  ring

/-- `B(Hx, Hx) ≤ K B(Hx, x)` from `B(Hy, y) ≤ K B(y, y)`, by Cauchy–Schwarz for `(a, b) ↦ B(Ha, b)`.

DERIVED: `0` the signs; `2` the square. -/
theorem range_le (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (hsa : ∀ x y, B (H x) y = B x (H y))
    (hpos : ∀ x, 0 ≤ B (H x) x) {K : ℝ} (hK0 : 0 < K) (hK : ∀ y, B (H y) y ≤ K * B y y) (x : E) :
    B (H x) (H x) ≤ K * B (H x) x := by
  set Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.comp H with hQ
  have hQa : ∀ a b, Q a b = B (H a) b := fun a b => rfl
  have hQs : ∀ a b, Q a b = Q b a := by
    intro a b; rw [hQa, hQa, hsa, hsymm]
  have hQn : ∀ a, 0 ≤ Q a a := fun a => by rw [hQa]; exact hpos a
  have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul Q hQs hQn x (H x)
  rw [hQa, hQa, hQa] at hcs
  -- hcs : B (H x) (H x) ^ 2 ≤ B (H x) x * B (H (H x)) (H x)
  have h1 := hK (H x)
  have hx := hpos x
  have hHH : 0 ≤ B (H x) (H x) := hnn (H x)
  rcases eq_or_lt_of_le hHH with h0 | hp
  · rw [← h0]; exact mul_nonneg hK0.le hx
  · have h3 : B (H x) (H x) ^ 2 ≤ B (H x) x * (K * B (H x) (H x)) :=
      hcs.trans (mul_le_mul_of_nonneg_left h1 hx)
    nlinarith

/-- **The energy drop of one lazy step.** DERIVED: `2` the cross term. -/
theorem drop_le (hsymm : ∀ x y, B x y = B y x) {K : ℝ} (hnn : ∀ x, 0 ≤ B x x) (v : E) :
    B v v - B (lazy H K v) (lazy H K v) ≤ 2 * K⁻¹ * B (H v) v := by
  unfold lazy
  rw [form_sub_smul B hsymm]
  have := hnn (H v)
  nlinarith [sq_nonneg K⁻¹]

/-- **The generator form contracts under the lazy step**, at the range gap `c`.

DERIVED: `1` the whole form; `2` the cross terms. -/
theorem gen_contract (hsa : ∀ x y, B (H x) y = B x (H y))
    {K c : ℝ} (hK0 : 0 < K) (hK : ∀ y, B (H y) y ≤ K * B y y)
    (hgap : ∀ x, c * B (H x) x ≤ B (H x) (H x)) (v : E) :
    B (H (lazy H K v)) (lazy H K v) ≤ (1 - c / K) * B (H v) v := by
  unfold lazy
  have e1 : B (H (v - K⁻¹ • H v)) (v - K⁻¹ • H v)
      = B (H v) v - 2 * K⁻¹ * B (H v) (H v) + K⁻¹ ^ 2 * B (H (H v)) (H v) := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have : B (H (H v)) v = B (H v) (H v) := by rw [hsa]
    rw [this]
    ring
  rw [e1]
  have h1 := hK (H v)
  have h2 := hgap v
  have hKi : 0 < K⁻¹ := inv_pos.mpr hK0
  have h3 : K⁻¹ ^ 2 * B (H (H v)) (H v) ≤ K⁻¹ * B (H v) (H v) := by
    calc K⁻¹ ^ 2 * B (H (H v)) (H v) ≤ K⁻¹ ^ 2 * (K * B (H v) (H v)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = K⁻¹ * B (H v) (H v) := by field_simp
  have h4 : c / K * B (H v) v ≤ K⁻¹ * B (H v) (H v) := by
    rw [div_eq_mul_inv, mul_comm c, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hKi.le
  nlinarith

/-- **The telescoped bound**: `B(u, u) ≤ B(Tᵐu, Tᵐu) + (2/c) B(Hu, u)` at every `m`.

DERIVED: `2` the energy drop; `0` the signs. -/
theorem tele_le (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (H x) y = B x (H y)) (hpos : ∀ x, 0 ≤ B (H x) x)
    {K c : ℝ} (hK0 : 0 < K) (hc : 0 < c) (hK : ∀ y, B (H y) y ≤ K * B y y)
    (hgap : ∀ x, c * B (H x) x ≤ B (H x) (H x)) :
    ∀ (m : ℕ) (u : E), B u u ≤ B ((lazy H K)^[m] u) ((lazy H K)^[m] u) + 2 / c * B (H u) u := by
  intro m
  induction m with
  | zero =>
    intro u
    simp only [Function.iterate_zero, id]
    have := hpos u
    have : 0 ≤ 2 / c * B (H u) u := mul_nonneg (by positivity) this
    linarith
  | succ m ih =>
    intro u
    rw [Function.iterate_succ_apply]
    have h1 := ih (lazy H K u)
    have h2 := drop_le B H hsymm (K := K) hnn u
    have h3 := gen_contract B H hsa hK0 hK hgap u
    have h4 : 2 / c * B (H (lazy H K u)) (lazy H K u) ≤ 2 / c * ((1 - c / K) * B (H u) u) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 2 / c * ((1 - c / K) * B (H u) u) + 2 * K⁻¹ * B (H u) u = 2 / c * B (H u) u := by
      field_simp
      ring
    linarith

/-- **The variance contracts** under a Poincaré inequality with any constant, on `vac⊥`.

DERIVED: `1` the unit vacuum and the shift `C + 1`; `0` the orthogonality; `2` the cross term. -/
theorem var_contract (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (H x) y = B x (H y)) (hpos : ∀ x, 0 ≤ B (H x) x)
    {K C : ℝ} (hK1 : 1 ≤ K) (hC : 0 ≤ C) (hK : ∀ y, B (H y) y ≤ K * B y y)
    {vac : E} (hHvac : H vac = 0)
    (hP : ∀ v, B v v - B v vac ^ 2 ≤ C * B (H v) v) :
    ∀ (m : ℕ) (u : E), B u vac = 0 →
      B ((lazy H K)^[m] u) ((lazy H K)^[m] u) ≤ (1 - 1 / (K * (C + 1))) ^ m * B u u := by
  have hK0 : 0 < K := by linarith
  have horth : ∀ u, B u vac = 0 → B (lazy H K u) vac = 0 := by
    intro u hu
    unfold lazy
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsa, hHvac, map_zero, hu]
    ring
  have hq0 : 0 ≤ 1 - 1 / (K * (C + 1)) := by
    have : 1 ≤ K * (C + 1) := by nlinarith
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  have hone : ∀ u, B u vac = 0 → B (lazy H K u) (lazy H K u) ≤ (1 - 1 / (K * (C + 1))) * B u u := by
    intro u hu
    have hr := range_le B H hsymm hnn hsa hpos hK0 hK u
    have e : B (lazy H K u) (lazy H K u) = B u u - 2 * K⁻¹ * B (H u) u + K⁻¹ ^ 2 * B (H u) (H u) := by
      unfold lazy; rw [form_sub_smul B hsymm]
    have hKi : 0 < K⁻¹ := inv_pos.mpr hK0
    have h1 : K⁻¹ ^ 2 * B (H u) (H u) ≤ K⁻¹ * B (H u) u := by
      calc K⁻¹ ^ 2 * B (H u) (H u) ≤ K⁻¹ ^ 2 * (K * B (H u) u) :=
            mul_le_mul_of_nonneg_left hr (sq_nonneg _)
        _ = K⁻¹ * B (H u) u := by field_simp
    have hp := hP u
    rw [hu] at hp
    have hpu := hpos u
    have h2 : B u u ≤ (C + 1) * B (H u) u := by nlinarith
    have h3 : 1 / (K * (C + 1)) * B u u ≤ K⁻¹ * B (H u) u := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      calc B u u ≤ (C + 1) * B (H u) u := h2
        _ = K⁻¹ * B (H u) u * (K * (C + 1)) := by field_simp
    nlinarith
  intro m
  induction m with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    rw [Function.iterate_succ_apply, pow_succ]
    have h1 := ih (lazy H K u) (horth u hu)
    have h2 := hone u hu
    calc B ((lazy H K)^[m] (lazy H K u)) ((lazy H K)^[m] (lazy H K u))
        ≤ (1 - 1 / (K * (C + 1))) ^ m * B (lazy H K u) (lazy H K u) := h1
      _ ≤ (1 - 1 / (K * (C + 1))) ^ m * ((1 - 1 / (K * (C + 1))) * B u u) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hq0 m)
      _ = (1 - 1 / (K * (C + 1))) ^ m * (1 - 1 / (K * (C + 1))) * B u u := by ring

/-- **The range gap is a Poincaré inequality on `vac⊥`, at half the constant.** The finite constant `C` does
not enter.

DERIVED: `2` the halving; `1` the unit vacuum; `0` the orthogonality. -/
theorem poincare_of_rangeGap (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x)
    (hsa : ∀ x y, B (H x) y = B x (H y)) (hpos : ∀ x, 0 ≤ B (H x) x)
    {K C c : ℝ} (hK1 : 1 ≤ K) (hC : 0 ≤ C) (hc : 0 < c) (hK : ∀ y, B (H y) y ≤ K * B y y)
    {vac : E} (hHvac : H vac = 0)
    (hP : ∀ v, B v v - B v vac ^ 2 ≤ C * B (H v) v)
    (hgap : ∀ x, c * B (H x) x ≤ B (H x) (H x)) (u : E) (hu : B u vac = 0) :
    c / 2 * B u u ≤ B (H u) u := by
  have hK0 : 0 < K := by linarith
  set q := 1 - 1 / (K * (C + 1)) with hqdef
  have hq0 : 0 ≤ q := by
    have : 1 ≤ K * (C + 1) := by nlinarith
    rw [hqdef, sub_nonneg, div_le_one (by linarith)]
    exact this
  have hq1 : q < 1 := by
    rw [hqdef]
    have : 0 < 1 / (K * (C + 1)) := by positivity
    linarith
  have hb : ∀ m : ℕ, B u u ≤ q ^ m * B u u + 2 / c * B (H u) u := by
    intro m
    have h1 := tele_le B H hsymm hnn hsa hpos hK0 hc hK hgap m u
    have h2 := var_contract B H hsymm hnn hsa hpos hK1 hC hK hHvac hP m u hu
    linarith
  have ht : Tendsto (fun m : ℕ => q ^ m * B u u + 2 / c * B (H u) u) atTop
      (nhds (0 * B u u + 2 / c * B (H u) u)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _).add_const _
  have hle : B u u ≤ 0 * B u u + 2 / c * B (H u) u := ge_of_tendsto' ht hb
  rw [zero_mul, zero_add] at hle
  have := mul_le_mul_of_nonneg_left hle (show 0 ≤ c / 2 by positivity)
  calc c / 2 * B u u ≤ c / 2 * (2 / c * B (H u) u) := this
    _ = B (H u) u := by field_simp

end Generic

#print axioms range_le
#print axioms drop_le
#print axioms gen_contract
#print axioms tele_le
#print axioms var_contract
#print axioms poincare_of_rangeGap

/-! ## 2. The overlapping block dynamics -/

section Wilson

variable {N : ℕ}

/-- **The generator of the overlapping block dynamics**, `Σ_K (id − E_K)`. DERIVED: no numeral. -/
def ovH (β : ℝ) (n j : ℕ) : TE N j →ₗ[ℝ] TE N j :=
  ∑ K, (LinearMap.id - ovP (N := N) β n j K)

theorem ovH_apply (β : ℝ) (n j : ℕ) (u : TE N j) : ovH β n j u = ∑ K, (u - ovP β n j K u) := by
  unfold ovH
  rw [LinearMap.coe_sum, Finset.sum_apply]
  rfl

/-- For a self-adjoint idempotent `P`: `B((1 − P)x, y) = B((1 − P)x, (1 − P)y)`.

DERIVED: `1` the identity. -/
theorem form_compl (hN : N ≠ 0) (β : ℝ) (j : ℕ) (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (x y : TE N j) :
    torusForm hN β j (x - torusBlkCondExp β (2 * j + 1) S x) y
      = torusForm hN β j (x - torusBlkCondExp β (2 * j + 1) S x)
          (y - torusBlkCondExp β (2 * j + 1) S y) := by
  have h : torusForm hN β j (x - torusBlkCondExp β (2 * j + 1) S x) (torusBlkCondExp β (2 * j + 1) S y)
      = 0 := by
    rw [← torusBlkCondExp_selfAdj hN β j S, map_sub, torusBlkCondExp_idem, sub_self, map_zero]
    rfl
  rw [map_sub (torusForm hN β j (x - torusBlkCondExp β (2 * j + 1) S x)), h, sub_zero]

/-- `B(ovH u, u) = Σ_K ‖u − E_K u‖²`. DERIVED: no numeral. -/
theorem ovH_form (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (u : TE N j) :
    torusForm hN β j (ovH β n j u) u
      = ∑ K, torusForm hN β j (u - ovP β n j K u) (u - ovP β n j K u) := by
  rw [ovH_apply, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun K _ => form_compl hN β j _ u u)

/-- `‖x − Px‖² ≤ ‖x‖²`. DERIVED: `0` the sign. -/
theorem compl_le (hN : N ≠ 0) (β : ℝ) (j : ℕ) (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (x : TE N j) :
    torusForm hN β j (x - torusBlkCondExp β (2 * j + 1) S x) (x - torusBlkCondExp β (2 * j + 1) S x)
      ≤ torusForm hN β j x x := by
  set P := torusBlkCondExp (N := N) β (2 * j + 1) S
  have hc : torusForm hN β j (x - P x) (P x) = 0 := by
    rw [← torusBlkCondExp_selfAdj hN β j S, map_sub, torusBlkCondExp_idem, sub_self, map_zero]
    rfl
  have e : torusForm hN β j x x
      = torusForm hN β j (x - P x) (x - P x) + 2 * torusForm hN β j (x - P x) (P x)
        + torusForm hN β j (P x) (P x) := by
    have : x = (x - P x) + P x := by abel
    conv_lhs => rw [this]
    simp only [map_add, LinearMap.add_apply]
    rw [torusForm_symm hN β j (P x) (x - P x)]
    ring
  rw [e, hc]
  have := torusForm_nonneg hN β j (P x)
  linarith

/-- **Nested projections**: for a link `l` of `S`, `‖v − E_l v‖² ≤ ‖v − E_S v‖²`.

DERIVED: `2` the cross term. -/
theorem nested_le (hN : N ≠ 0) (β : ℝ) (j : ℕ) (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    {l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)} (hl : l ∈ S) (v : TE N j) :
    torusForm hN β j (v - torusCondExp β (2 * j + 1) l v) (v - torusCondExp β (2 * j + 1) l v)
      ≤ torusForm hN β j (v - torusBlkCondExp β (2 * j + 1) S v)
          (v - torusBlkCondExp β (2 * j + 1) S v) := by
  set B := torusForm hN β j
  set El := torusCondExp (N := N) β (2 * j + 1) l
  set ES := torusBlkCondExp (N := N) β (2 * j + 1) S
  -- `El (ES v)` and `ES v` differ by a null vector
  have hnull : B (El (ES v) - ES v) (El (ES v) - ES v) = 0 :=
    null_of_torusObs_eq hN β j _ _
      (torusCondExp_keeps β j l (ES v) (torusBlkCondExp_readsNot β j S v l hl))
  have hzero : ∀ w, B w (El (ES v) - ES v) = 0 := by
    intro w
    have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul B (torusForm_symm hN β j)
      (torusForm_nonneg hN β j) w (El (ES v) - ES v)
    rw [hnull, mul_zero] at hcs
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hcs (sq_nonneg _))
  have hperp : ∀ w, B (v - El v) (El w) = 0 := by
    intro w
    rw [← torusCondExp_selfAdj hN β j l, map_sub, torusCondExp_idem, sub_self, map_zero]
    rfl
  set a := v - El v
  set b := El v - ES v
  have hab : B a b = 0 := by
    have : b = El (v - ES v) + (El (ES v) - ES v) := by
      simp only [b, map_sub]; abel
    rw [this, map_add, hperp, hzero, add_zero]
  have hsum : v - ES v = a + b := by simp only [a, b]; abel
  rw [hsum]
  simp only [map_add, LinearMap.add_apply]
  rw [torusForm_symm hN β j b a, hab]
  have := torusForm_nonneg hN β j b
  linarith

/-- **Every link lies in an overlapping box.** DERIVED: Inherited: `3` the least cell count of
`OverlapGeometry.three_le_qO` (`3 n ≤ L` gives at least three cells, `OverlapGeometry.cellO_lt`). -/
theorem exists_ovBox_mem {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ∃ K : Fin 4 → Fin (qO n (2 * j + 1 + 1)), l ∈ ovBox n (2 * j + 1) K := by
  refine ⟨fun μ => ⟨cellO n (2 * j + 1 + 1) (l.2 μ), cellO_lt hn hL _⟩, ?_⟩
  rw [mem_ovBox]
  intro μ
  exact Or.inl rfl

/-- **The finite-extent Poincaré inequality of the overlapping dynamics**, with a constant depending on `j`.

DERIVED: `2` the square; `0` the sign; Inherited: `3` the least cell count of
`OverlapGeometry.three_le_qO`, via `exists_ovBox_mem`. -/
theorem ov_poincare_finite (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : TE N j,
      torusForm hN β j v v - torusForm hN β j v (oneT j) ^ 2
        ≤ C * torusForm hN β j (ovH β n j v) v := by
  obtain ⟨C, hC0, hC⟩ := torus_poincare (N := N) hN β j
  refine ⟨C * Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)), by positivity, fun v => ?_⟩
  have h1 := hC v
  rw [ovH_form]
  set S := ∑ K, torusForm hN β j (v - ovP β n j K v) (v - ovP β n j K v)
  have hS0 : ∀ K, 0 ≤ torusForm hN β j (v - ovP β n j K v) (v - ovP β n j K v) :=
    fun K => torusForm_nonneg hN β j _
  have hl : ∀ l, torusForm hN β j (v - torusCondExp β (2 * j + 1) l v) (v - torusCondExp β (2 * j + 1) l v)
      ≤ S := by
    intro l
    obtain ⟨K, hK⟩ := exists_ovBox_mem hn hL l
    calc _ ≤ torusForm hN β j (v - ovP β n j K v) (v - ovP β n j K v) := nested_le hN β j _ hK v
      _ ≤ S := Finset.single_le_sum (fun K _ => hS0 K) (Finset.mem_univ K)
  have h2 : ∑ l, torusForm hN β j (v - torusCondExp β (2 * j + 1) l v) (v - torusCondExp β (2 * j + 1) l v)
      ≤ Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) * S := by
    calc _ ≤ ∑ _l : WilsonHypercubic.Link 4 (2 * j + 1 + 1), S := Finset.sum_le_sum (fun l _ => hl l)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc _ ≤ C * ∑ l, torusForm hN β j (v - torusCondExp β (2 * j + 1) l v)
            (v - torusCondExp β (2 * j + 1) l v) := h1
    _ ≤ C * (Fintype.card (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) * S) :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = _ := by ring

/-- **The range gap of the overlapping generator at one extent gives the floor's inequality there**, at half
the constant.

DERIVED: `2` the halving; `1` the least cell side; `3` the colour period. -/
theorem overlapPoincare_of_rangeGap (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n)
    (hL : 3 * n ≤ 2 * j + 1 + 1) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ x : TE N j, c * torusForm hN β j (ovH β n j x) x
      ≤ torusForm hN β j (ovH β n j x) (ovH β n j x)) :
    OverlapPoincare hN β n j (c / 2) := by
  set B := torusForm hN β j
  have hsymm := torusForm_symm (N := N) hN β j
  have hnn := torusForm_nonneg (N := N) hN β j
  have hsa : ∀ x y, B (ovH β n j x) y = B x (ovH β n j y) := by
    intro x y
    rw [ovH_apply, ovH_apply, map_sum, LinearMap.coe_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    simp only [map_sub, LinearMap.sub_apply]
    rw [show B (ovP β n j K x) y = B x (ovP β n j K y) from torusBlkCondExp_selfAdj hN β j _ x y]
  have hpos : ∀ x, 0 ≤ B (ovH β n j x) x := by
    intro x
    rw [ovH_form]
    exact Finset.sum_nonneg (fun K _ => hnn _)
  set Kc : ℝ := (Fintype.card (Fin 4 → Fin (qO n (2 * j + 1 + 1))) : ℝ) + 1
  have hK1 : 1 ≤ Kc := by
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin 4 → Fin (qO n (2 * j + 1 + 1))))
    simp only [Kc]; linarith
  have hK : ∀ y, B (ovH β n j y) y ≤ Kc * B y y := by
    intro y
    rw [ovH_form]
    calc _ ≤ ∑ _K : Fin 4 → Fin (qO n (2 * j + 1 + 1)), B y y :=
          Finset.sum_le_sum (fun K _ => compl_le hN β j _ y)
      _ = (Fintype.card (Fin 4 → Fin (qO n (2 * j + 1 + 1))) : ℝ) * B y y := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Kc * B y y := by
          have := hnn y
          simp only [Kc]; nlinarith
  have hHvac : ovH β n j (oneT (N := N) j) = 0 := by
    rw [ovH_apply]
    exact Finset.sum_eq_zero (fun K _ => by rw [ovP_one, sub_self])
  obtain ⟨C, hC0, hP⟩ := ov_poincare_finite hN β hn hL
  intro u hu
  have h := poincare_of_rangeGap B (ovH β n j) hsymm hnn hsa hpos hK1 hC0 hc hK hHvac hP hgap u hu
  rw [ovH_form] at h
  exact h

#print axioms overlapPoincare_of_rangeGap

/-- **The overlapping gap from a range gap at every large extent**, capped at `1`.

DERIVED: `2` the halving; `1` the cap and the least cell side; `3` the colour period. -/
theorem overlapGap_ge_of_rangeGap (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ᶠ j in atTop, ∀ x : TE N j, c * torusForm hN β j (ovH β n j x) x
      ≤ torusForm hN β j (ovH β n j x) (ovH β n j x)) :
    min (c / 2) 1 ≤ overlapGap hN β n := by
  apply le_csSup ⟨1, fun _ h => h.2.1⟩
  refine ⟨le_min (by positivity) zero_le_one, min_le_right _ _, ?_⟩
  filter_upwards [hgap, Filter.eventually_ge_atTop (3 * n)] with j hj hjL
  have hP := overlapPoincare_of_rangeGap hN β hn (by omega) hc hj
  intro u hu
  have h1 := hP u hu
  have h2 : min (c / 2) 1 * torusForm hN β j u u ≤ c / 2 * torusForm hN β j u u :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (torusForm_nonneg hN β j u)
  linarith

#print axioms overlapGap_ge_of_rangeGap

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from a range gap of the overlapping generator at each coupling.** At every
large `β`, at every large extent, `c B(ovH x, x) ≤ B(ovH x, ovH x)` at cell side `⌈1/(κ aRun β)⌉₊`: the output
form of a finite-size criterion of Knabe type. With E, N, Y, `ClayContinuum`.

DERIVED: `2` the least rank and the halving; `0` the signs; `4` the spacetime dimension; `1` the least colour
count, the least cell side and the cap. -/
theorem clay_continuum_of_overlapRangeGapRun (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hgap : ∀ᶠ β in atTop, ∀ᶠ j in atTop, ∀ x : TE N j,
      c * torusForm hN β j
          (ovH β (BlockGapDef.blockSide (fun β => κ * AsymptoticScaling.aRun N β) β) j x) x
        ≤ torusForm hN β j
          (ovH β (BlockGapDef.blockSide (fun β => κ * AsymptoticScaling.aRun N β) β) j x)
          (ovH β (BlockGapDef.blockSide (fun β => κ * AsymptoticScaling.aRun N β) β) j x))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  have hs := OverlapFloor.scaleFunction_const_mul_aRun hN1 hκ one_pos
  refine OverlapFloor.clay_continuum_of_overlapFloorRun hN2 hN Z τ hZ hB hL hκ
    (lt_min (half_pos hc) one_pos) ?_ O G hconvK hY
  filter_upwards [hgap, hs.eventually_small 1 one_pos, hs.eventually_le] with β hβ hs1 hs0
  exact overlapGap_ge_of_rangeGap hN β (blockSide_le hs0.1 hs1).1 hc hβ

#print axioms clay_continuum_of_overlapRangeGapRun

end Wilson

end MassGap.OverlapErgodic
