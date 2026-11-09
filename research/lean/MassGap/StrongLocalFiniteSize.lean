import Mathlib
import MassGap.StrongFiniteSize
import MassGap.WeakCouplingWindow

/-!
# MassGap.StrongLocalFiniteSize — strong-coupling finite-size decay for every bounded observable of finite reach

`StrongFiniteSize` bounds the doubling change of the plaquette energy reading of the torus state at
`|β| ≤ 2^{-16}`. This module states the same bound for any bounded observable of fixed finite reach about the
origin, with the reach entering the constant only through an explicit factor, and applies it to the flowed
plaquette reading of a `ConfFlow`, whose `local_V` field is a reach `W.range k` per output link.

## Reach (proved)

* `HasReach r F`: `F` reads only the links of `StrongFiniteSize.box r`, the links based in `[−r, r]⁴`
  (`StrongKernelNear.IsLocalOn (box r) F`). `hasReach_of_local` turns locality on any finite link set of
  sup-radius `≤ r` into reach `r`; `hasReach_mono` enlarges `r`. `card_box`: `|box r| = 4 (2r + 1)⁴`.
* Non-vacuity: `hasReach_plaqField`, the plaquette density at the origin has reach `1`;
  `hasReach_flowPlaq`, the flowed plaquette density `W.fieldMap k (plaqField (p, 0))` has reach
  `W.range k + 1`, from `ConfFlow.local_V`.

## The bounds (proved)

At every `N ≠ 0`, `|β| ≤ 2^{-16}`, `F` continuous with `|F| ≤ B` and reach `r`, `ν_M = torusState hN M β`:

* `torusState_sub_le_reach`: `|ν_M F − ν_{M'} F| ≤ 16 (2r + 1)⁴ B 2^{−(R + 1 − r)}` at `r ≤ R`,
  `2 (R + 1) < M + 1, M' + 1` (`StrongFiniteSize.torusState_sub_le` applied to `B⁻¹ F` on `box r`).
* **`doubling_sub_le_reach`**: for every side `n` and every `r`,
  `|ν_{2n−1} F − ν_{n−1} F| ≤ 32 (2r + 1)⁴ B 2^r e^{−(log 2/2) n}`;
  **`doubling_sub_le_reach_exp`**: the same as `32 (2r + 1)⁴ B e^{−(log 2/2)(n − 2r)}`.
  The reach costs the factor `(2r + 1)⁴` (the support's link count) and the shift `2r` of the decay.
* `tendsto_doubling_reach`: at fixed `r` the doubling change tends to `0` as `n → ∞`.
* **`doubling_sub_le_tail`**: at `θ ≤ 1` and `2r ≤ θ n`, `|ν_{2n−1} F − ν_{n−1} F| ≤ B · reachTail θ n` with
  `reachTail θ n = 32 (n + 1)⁴ e^{−(log 2/2)(1 − θ) n}`; `tendsto_reachTail`: `→ 0` at `θ < 1`. So the bound
  is uniform over the class of observables of norm `≤ B` and reach `≤ θ n / 2`, a reach growing linearly in
  the side.
* `bareRead_sub_le_reach`: the plaquette reading as the case `r = 1`, `B = 2`:
  `|bareRead (2n) − bareRead n| ≤ 165888 e^{−(log 2/2) n}`. This is `StrongFiniteSize.finiteSize_decay_strong`
  with a larger constant (`1024` there, from the plaquette's four links rather than `|box 1| = 324`).

## The flowed reading (proved)

* `flowRead_sub_le_reach`: `|flowRead (2n) − flowRead n| ≤ 1024 (2ρ + 3)⁴ 2^{ρ+1} e^{−(log 2/2) n}`,
  `ρ = W.range k`, for every `n`; `flowRead_sub_le_tail`: `≤ 32 · reachTail θ n` at `2 (ρ + 1) ≤ θ n`.
* `abs_flowDefect_le_tail`: `|flowDefect hN W k n β| ≤ β · strongReachBound θ n` on `0 ≤ β ≤ 2^{-16}`,
  `strongReachBound θ n = 16 n⁴ · 32 · reachTail θ n`; `tendsto_strongReachBound`: `→ 0` at `θ < 1`.
* `eventually_inWin_ge`: at `C > 0` the window side exceeds any `n₀` eventually in `β`
  (`WeakCouplingWindow.eventually_aRun_le`).
* **`strongPart_of_reach`**: at `x₀ = 2^{-16}`, `C > 0`, `θ < 1`, `η > 0` and any `K`, if eventually in `β` the
  window side `n` has `2 (W.range (κ β) + 1) ≤ θ n`, then eventually in `β`, at the window side,
  `defectW N x₀ n − K · flowDefect hN W (κ β) n x₀ ≤ η`: the hypothesis `hs` of
  `FlowComp.flowEnergyComp_of_split`. `strongPart_of_bounded_range`: the reach hypothesis holds when
  `W.range ∘ κ` is bounded.

## What is not proved here

* The scaling part of `FlowComp.flowEnergyComp_of_split`, `∫_{x₀}^β (bareDelta − K flowDelta) ≤ η₂` on the
  weak-coupling range, and with it `FlowEnergyComp` itself.
* The reach hypothesis of `strongPart_of_reach` for the observer's flow at its step: `2 (W.range (κ β) + 1) ≤ θ n`
  with `θ < 1` at every window side `n`, `C / 2 < n · aRun N β ≤ C`. For a flow of lattice range at most
  `s / aRun N β` at the step (e.g. `ObserverBlock.blFam … m s`, range `≤ s / dySpacing N k` by
  `ObserverMultigrid.spacing_mul_mgRange_le`, at a step with `aRun N β ≤ dySpacing N (κ β)`) it holds eventually
  once `4 s < θ C`, from the window's lower edge `C / 2`; a condition on the flow, the step and the window
  constant, not a consequence of `ConfFlow`. For `blFam` at the step `FlowScalingOnly.obsStep` it is proved in
  `FlowScalingOnly.reach_blFam`.
* Observables of finite reach about a site other than the origin; the readings here are all at the origin.

DERIVED (module-wide): `4` the dimension and the links of a plaquette; `2r + 1` the sites of `[−r, r]`;
`16 = 4 · 4` the kernel factor `4` of `torusState_sub_le` times the four directions of `box r`, and the ordered
planes; `32 = 16 · 2` the two cases of the side bound; `2^r` the shift of the depth by the reach;
`log 2 / 2` the rate `2^{−R}` at `R ≈ n/2`; `65536 = 2^{16}` the strong-coupling threshold; `2` the range of
the plaquette density, the doubling and the two tori; `1` the plaquette's sup-radius and the unit step;
`3`, `5` the least side with `1 ≤ ⌊(n − 3)/2⌋`; `1024 = 16 · 2 · 32`; `165888 = 16 · 32 · 81 · 2 · 2`;
`262144 = 16 · 32 · 32 · 16`; `0` the origin and the lower coupling.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StrongLocalFiniteSize

open Filter Topology
open MassGap.GibbsSpec
open MassGap.StrongKernelNear (IsLocalOn)
open MassGap.PeriodicState (torusState)
open MassGap.ObserverFlowSeed (bareRead flowRead flowDelta InWin)
open MassGap.ObserverEnergyMoments (plaqField)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.StrongFiniteSize (snorm box mem_box snorm_le_iff ilinks_base torusState_sub_le exp_half_le
  strongBound tendsto_strongBound abs_defectW_strong_le)

variable {N : ℕ}

/-! ## 1. Reach -/

/-- **Reach `r`**: `F` reads only the links based in `[−r, r]⁴`. DERIVED: no numeral. -/
def HasReach (r : ℕ) (F : IConf (MassGap.SUN.SU N) → ℝ) : Prop :=
  IsLocalOn (box r) F

/-- Locality on a link set of sup-radius `≤ r` is reach `r`. DERIVED: no numeral. -/
theorem hasReach_of_local {r : ℕ} {A : Finset ILink} {F : IConf (MassGap.SUN.SU N) → ℝ}
    (hA : IsLocalOn A F) (hr : ∀ l ∈ A, snorm l.2 ≤ r) : HasReach r F :=
  fun η η' h => hA η η' fun l hl => h l (mem_box.mpr (hr l hl))

/-- DERIVED: no numeral. -/
theorem hasReach_mono {r r' : ℕ} (h : r ≤ r') {F : IConf (MassGap.SUN.SU N) → ℝ} (hF : HasReach r F) :
    HasReach r' F :=
  hasReach_of_local hF fun _ hl => (mem_box.mp hl).trans h

/-- `|box r| = 4 (2r + 1)⁴`. DERIVED: `4` the directions and the dimension; `2r + 1` the sites of
`[−r, r]`. -/
theorem card_box (r : ℕ) : (box r).card = 4 * (2 * r + 1) ^ 4 := by
  unfold box
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_piFinset,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  have h : (r : ℤ) + 1 - -(r : ℤ) = ((2 * r + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- **Non-vacuity: the plaquette density at the origin has reach `1`.** DERIVED: `1` the plaquette's
sup-radius; `0` the origin. -/
theorem hasReach_plaqField (p : Fin 4 × Fin 4) : HasReach 1 ⇑(plaqField (N := N) (p, 0)).1 := by
  intro η η' h
  show wilsonDensity (ihol (p, 0) η) = wilsonDensity (ihol (p, 0) η')
  rw [ihol_congr (p, 0) η η' fun l hl => h l (mem_box.mpr (snorm_le_iff.mpr fun i => by
    have := ilinks_base hl i
    dsimp only [Pi.zero_apply] at this
    push_cast
    omega))]

/-- **The flowed plaquette density at the origin has reach `W.range k + 1`** (`ConfFlow.local_V`).
DERIVED: `1` the plaquette's sup-radius; `0` the origin. -/
theorem hasReach_flowPlaq (W : ConfFlow N) (k : ℕ) (p : Fin 4 × Fin 4) :
    HasReach (W.range k + 1) ⇑(W.fieldMap k (plaqField (N := N) (p, 0))).1 := by
  intro η η' h
  show wilsonDensity (ihol (p, 0) (W.V k η)) = wilsonDensity (ihol (p, 0) (W.V k η'))
  rw [ihol_congr (p, 0) (W.V k η) (W.V k η') fun l hl => by
    obtain ⟨T, hT, hTl⟩ := W.local_V k l
    exact hTl η η' fun l' hl' => h l' (mem_box.mpr (snorm_le_iff.mpr fun i => by
      have h1 := ilinks_base hl i
      have h2 := abs_le.mp (hT l' hl' i)
      dsimp only [Pi.zero_apply] at h1
      push_cast
      omega))]

/-- The plaquette density and its flowed version lie in `[0, 2]`. DERIVED: `2` the range. -/
theorem abs_flowPlaq_le (hN : N ≠ 0) (W : ConfFlow N) (k : ℕ) (p : Fin 4 × Fin 4)
    (ω : IConf (MassGap.SUN.SU N)) : |(W.fieldMap k (plaqField (N := N) (p, 0))).1 ω| ≤ 2 := by
  show |wilsonDensity (ihol (p, 0) (W.V k ω))| ≤ 2
  exact abs_le.mpr ⟨by linarith [wilsonDensity_nonneg hN (ihol (p, 0) (W.V k ω))],
    wilsonDensity_le_two hN (ihol (p, 0) (W.V k ω))⟩

/-- DERIVED: `2` the range. -/
theorem abs_plaq_le (hN : N ≠ 0) (p : Fin 4 × Fin 4) (ω : IConf (MassGap.SUN.SU N)) :
    |(plaqField (N := N) (p, 0)).1 ω| ≤ 2 := by
  show |wilsonDensity (ihol (p, 0) ω)| ≤ 2
  exact abs_le.mpr ⟨by linarith [wilsonDensity_nonneg hN (ihol (p, 0) ω)],
    wilsonDensity_le_two hN (ihol (p, 0) ω)⟩

/-! ## 2. Two tori read an observable of reach `r` alike -/

/-- `|ν f| ≤ B` for `|f| ≤ B`. DERIVED: no numeral. -/
theorem abs_torusState_le (hN : N ≠ 0) (M : ℕ) (β : ℝ) {B : ℝ} (F : C(IConf (MassGap.SUN.SU N), ℝ))
    (hFB : ∀ ω, |F ω| ≤ B) : |torusState hN M β F| ≤ B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB fun _ => 1)
  exact ((torusState hN M β).abs_le_norm F).trans
    ((ContinuousMap.norm_le _ hB0).mpr fun ω => by rw [Real.norm_eq_abs]; exact hFB ω)

/-- **Two torus states agree on an observable of reach `r` up to `16 (2r+1)⁴ B 2^{−(R+1−r)}`.**
DERIVED: `16 = 4 · 4`, `4` from `torusState_sub_le` and `4` from `card_box`; `65536 = 2^{16}` the
strong-coupling threshold. -/
theorem torusState_sub_le_reach (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {r R M M' : ℕ} {B : ℝ}
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) (hrR : r ≤ R)
    (hM : 2 * (R + 1) < M + 1) (hM' : 2 * (R + 1) < M' + 1) :
    |torusState hN M β F - torusState hN M' β F| ≤ 16 * (2 * r + 1) ^ 4 * B * (1 / 2) ^ (R + 1 - r) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB fun _ => 1)
  rcases hB0.eq_or_lt with hB | hB
  · have h1 := abs_torusState_le hN M β F hFB
    have h2 := abs_torusState_le hN M' β F hFB
    have h3 := abs_sub (torusState hN M β F) (torusState hN M' β F)
    rw [← hB] at h1 h2 ⊢
    rw [mul_zero, zero_mul]
    linarith
  · set G : C(IConf (MassGap.SUN.SU N), ℝ) := B⁻¹ • F with hG
    have hG1 : ∀ ω, |G ω| ≤ 1 := fun ω => by
      rw [hG, ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hB)]
      calc B⁻¹ * |F ω| ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hFB ω) (inv_pos.mpr hB).le
        _ = 1 := inv_mul_cancel₀ hB.ne'
    have hGloc : IsLocalOn (box r) ⇑G := fun η η' h => by
      show B⁻¹ * F η = B⁻¹ * F η'
      rw [hF η η' h]
    have h := torusState_sub_le hN hβ G (box r) hG1 hGloc (fun l hl => mem_box.mp hl) hrR hM hM'
    rw [hG, MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_smul, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hB), card_box] at h
    push_cast at h
    have h' := mul_le_mul_of_nonneg_left h hB.le
    rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul] at h'
    calc _ ≤ B * (4 * (4 * (2 * (r : ℝ) + 1) ^ 4) * (1 / 2) ^ (R + 1 - r)) := h'
      _ = 16 * (2 * r + 1) ^ 4 * B * (1 / 2) ^ (R + 1 - r) := by ring

/-- **The doubling change of an observable of reach `r` at strong coupling, every side.**
`|ν_{2n−1} F − ν_{n−1} F| ≤ 32 (2r+1)⁴ B 2^r e^{−(log 2/2) n}`.
DERIVED: `32 = 16 · 2`; `2^r` the reach's shift of the depth; `3`, `5` the least side with `1 ≤ ⌊(n−3)/2⌋`;
`8 = 2 · 4 ≤ 32` the trivial bound `2B` at small sides; `65536 = 2^{16}` the strong-coupling threshold. -/
theorem doubling_sub_le_reach (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (r n : ℕ) {B : ℝ}
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) :
    |torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F|
      ≤ 32 * (2 * r + 1) ^ 4 * B * 2 ^ r * Real.exp (-(Real.log 2 / 2) * n) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB fun _ => 1)
  have hE : 0 < Real.exp (Real.log 2 / 2 * n) := Real.exp_pos _
  have hP1 : (1 : ℝ) ≤ (2 * r + 1) ^ 4 := one_le_pow₀ (by linarith [(r.cast_nonneg : (0 : ℝ) ≤ r)])
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE]
  by_cases hn : 5 ≤ n ∧ r ≤ (n - 3) / 2
  · set R := (n - 3) / 2 with hR
    have h1 := torusState_sub_le_reach hN hβ (M := 2 * n - 1) (M' := n - 1) F hFB hF hn.2
      (by omega) (by omega)
    have h2 := exp_half_le (n := n) (k := R + 2) (by omega)
    have hsplit : (2 : ℝ) ^ (R + 2) = 2 ^ (R + 1 - r) * 2 ^ r * 2 := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    have hq : (1 / 2 : ℝ) ^ (R + 1 - r) * Real.exp (Real.log 2 / 2 * n) ≤ 2 * 2 ^ r := by
      rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      calc Real.exp (Real.log 2 / 2 * n) ≤ 2 ^ (R + 2) := h2
        _ = 2 * 2 ^ r * 2 ^ (R + 1 - r) := by rw [hsplit]; ring
    have hc : 0 ≤ 16 * (2 * (r : ℝ) + 1) ^ 4 * B := mul_nonneg (by positivity) hB0
    calc _ ≤ 16 * (2 * (r : ℝ) + 1) ^ 4 * B * (1 / 2) ^ (R + 1 - r) * Real.exp (Real.log 2 / 2 * n) :=
          mul_le_mul_of_nonneg_right h1 hE.le
      _ = 16 * (2 * (r : ℝ) + 1) ^ 4 * B * ((1 / 2) ^ (R + 1 - r) * Real.exp (Real.log 2 / 2 * n)) := by
          ring
      _ ≤ 16 * (2 * (r : ℝ) + 1) ^ 4 * B * (2 * 2 ^ r) := mul_le_mul_of_nonneg_left hq hc
      _ = 32 * (2 * r + 1) ^ 4 * B * 2 ^ r := by ring
  · have h2 := exp_half_le (n := n) (k := r + 2) (by omega)
    have ha := abs_torusState_le hN (2 * n - 1) β F hFB
    have hb := abs_torusState_le hN (n - 1) β F hFB
    have hab := abs_sub (torusState hN (2 * n - 1) β F) (torusState hN (n - 1) β F)
    have hd : |torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F| ≤ 2 * B := by linarith
    have hb2 : 0 ≤ B * 2 ^ r := mul_nonneg hB0 h2r.le
    have hPB := mul_le_mul_of_nonneg_left hP1 hb2
    calc _ ≤ 2 * B * 2 ^ (r + 2) := mul_le_mul hd h2 hE.le (by linarith)
      _ = 8 * (B * 2 ^ r * 1) := by ring
      _ ≤ 32 * (B * 2 ^ r * (2 * r + 1) ^ 4) := by nlinarith
      _ = 32 * (2 * r + 1) ^ 4 * B * 2 ^ r := by ring

/-- **The same bound with the reach as a shift of the decay**: `32 (2r+1)⁴ B e^{−(log 2/2)(n − 2r)}`.
DERIVED: `2` the shift per unit of reach (`2^r = e^{(log 2/2) · 2r}`); `65536 = 2^{16}` the strong-coupling
threshold. -/
theorem doubling_sub_le_reach_exp (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (r n : ℕ) {B : ℝ}
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) :
    |torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F|
      ≤ 32 * (2 * r + 1) ^ 4 * B * Real.exp (-(Real.log 2 / 2) * ((n : ℝ) - 2 * r)) := by
  have he : Real.exp (-(Real.log 2 / 2) * ((n : ℝ) - 2 * r))
      = 2 ^ r * Real.exp (-(Real.log 2 / 2) * n) := by
    rw [show -(Real.log 2 / 2) * ((n : ℝ) - 2 * r) = (r : ℝ) * Real.log 2 + -(Real.log 2 / 2) * n by ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [he, ← mul_assoc]
  exact doubling_sub_le_reach hN hβ r n F hFB hF

/-- `n^j e^{−c n} → 0` along the naturals at `c > 0`. DERIVED: no numeral. -/
theorem tendsto_pow_exp (j : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ j * Real.exp (-(c * n))) atTop (𝓝 0) := by
  have hg := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have h := hg.const_mul ((c⁻¹) ^ j)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [← mul_assoc, ← mul_pow, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- `0 < log 2 / 2`. DERIVED: `2` the base and the halving. -/
theorem half_log_two_pos : 0 < Real.log 2 / 2 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- **At fixed reach the doubling change tends to `0`** as the side grows. DERIVED: `0` the power of `n`; `65536 = 2^{16}` the
strong-coupling threshold. -/
theorem tendsto_doubling_reach (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (r : ℕ) {B : ℝ}
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) :
    Tendsto (fun n : ℕ => torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F) atTop (𝓝 0) := by
  have h := (tendsto_pow_exp 0 half_log_two_pos).const_mul (32 * (2 * (r : ℝ) + 1) ^ 4 * B * 2 ^ r)
  rw [mul_zero] at h
  refine squeeze_zero_norm (fun n => ?_) h
  rw [Real.norm_eq_abs, pow_zero, one_mul, ← neg_mul]
  exact doubling_sub_le_reach hN hβ r n F hFB hF

/-! ## 3. A reach growing with the side -/

/-- **The tail at a reach `≤ θ n / 2`**: `32 (n + 1)⁴ e^{−(log 2/2)(1 − θ) n}`. DERIVED: `32` from
`doubling_sub_le_reach`; `4` the dimension; `1` the successor bounding `2r + 1`. -/
def reachTail (θ : ℝ) (n : ℕ) : ℝ :=
  32 * ((n : ℝ) + 1) ^ 4 * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n))

/-- **Uniform over a reach growing linearly in the side**: at `θ ≤ 1` and `2r ≤ θ n`,
`|ν_{2n−1} F − ν_{n−1} F| ≤ B · reachTail θ n`. DERIVED: `2` the shift per unit of reach; `65536 = 2^{16}`
the strong-coupling threshold. -/
theorem doubling_sub_le_tail (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {θ : ℝ} (hθ : θ ≤ 1) (r n : ℕ)
    (hr : 2 * (r : ℝ) ≤ θ * n) {B : ℝ}
    (F : C(IConf (MassGap.SUN.SU N), ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) :
    |torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F| ≤ B * reachTail θ n := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB fun _ => 1)
  have h := doubling_sub_le_reach_exp hN hβ r n F hFB hF
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hθn : θ * n ≤ n := by nlinarith
  have hP : (2 * (r : ℝ) + 1) ^ 4 ≤ ((n : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hc := half_log_two_pos
  have he : Real.exp (-(Real.log 2 / 2) * ((n : ℝ) - 2 * r))
      ≤ Real.exp (-(Real.log 2 / 2 * (1 - θ) * n)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hr hc.le])
  calc _ ≤ 32 * (2 * (r : ℝ) + 1) ^ 4 * B * Real.exp (-(Real.log 2 / 2) * ((n : ℝ) - 2 * r)) := h
    _ ≤ 32 * ((n : ℝ) + 1) ^ 4 * B * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n)) := by
        apply mul_le_mul _ he (Real.exp_pos _).le (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) hB0
    _ = B * reachTail θ n := by unfold reachTail; ring

/-- `(n + 1)⁴ ≤ 16 n⁴` at `n ≥ 1`. DERIVED: `16 = 2⁴`. -/
theorem succ_pow_four_le {n : ℕ} (hn : 1 ≤ n) : ((n : ℝ) + 1) ^ 4 ≤ 16 * (n : ℝ) ^ 4 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc ((n : ℝ) + 1) ^ 4 ≤ (2 * (n : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    _ = 16 * (n : ℝ) ^ 4 := by ring

/-- DERIVED: `512 = 32 · 16`; `1` the least side. -/
theorem tendsto_reachTail {θ : ℝ} (hθ : θ < 1) : Tendsto (reachTail θ) atTop (𝓝 0) := by
  have hc : 0 < Real.log 2 / 2 * (1 - θ) := mul_pos half_log_two_pos (by linarith)
  have h := (tendsto_pow_exp 4 hc).const_mul 512
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold reachTail; positivity) ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold reachTail
  have hs := succ_pow_four_le hn
  have hE := (Real.exp_pos (-(Real.log 2 / 2 * (1 - θ) * n))).le
  calc 32 * ((n : ℝ) + 1) ^ 4 * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n))
      ≤ 32 * (16 * (n : ℝ) ^ 4) * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n)) := by gcongr
    _ = 512 * ((n : ℝ) ^ 4 * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n))) := by ring

/-! ## 4. The plaquette reading as the case `r = 1` -/

/-- **The bare reading from the reach bound**: `|bareRead (2n) − bareRead n| ≤ 165888 e^{−(log 2/2) n}`.
DERIVED: `165888 = 16 · 32 · 3⁴ · 2 · 2`, the ordered planes, `doubling_sub_le_reach` at `r = 1`, `B = 2`;
`65536 = 2^{16}` the strong-coupling threshold. -/
theorem bareRead_sub_le_reach (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (n : ℕ) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 165888 * Real.exp (-(Real.log 2 / 2) * n) := by
  unfold bareRead
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ p : Fin 4 × Fin 4, |torusState hN (2 * n - 1) β (plaqField (N := N) (p, 0)).1
          - torusState hN (n - 1) β (plaqField (N := N) (p, 0)).1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 4 × Fin 4, 32 * (2 * ((1 : ℕ) : ℝ) + 1) ^ 4 * 2 * 2 ^ 1
          * Real.exp (-(Real.log 2 / 2) * n) :=
        Finset.sum_le_sum fun p _ =>
          doubling_sub_le_reach hN hβ 1 n _ (abs_plaq_le hN p) (hasReach_plaqField p)
    _ = 165888 * Real.exp (-(Real.log 2 / 2) * n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring

/-! ## 5. The flowed reading -/

/-- **The flowed reading's doubling change at strong coupling, every side**:
`≤ 1024 (2ρ + 3)⁴ 2^{ρ+1} e^{−(log 2/2) n}` with `ρ = W.range k`. DERIVED: `1024 = 16 · 2 · 32` the
ordered planes, the range `2` and `doubling_sub_le_reach`; `3 = 2 · 1 + 1` from reach `ρ + 1`;
`65536 = 2^{16}` the strong-coupling threshold. -/
theorem flowRead_sub_le_reach (hN : N ≠ 0) (W : ConfFlow N) (k : ℕ) {β : ℝ} (hβ : |β| ≤ 1 / 65536)
    (n : ℕ) :
    |flowRead hN W k (2 * n) β - flowRead hN W k n β|
      ≤ 1024 * (2 * (W.range k : ℝ) + 3) ^ 4 * 2 ^ (W.range k + 1) * Real.exp (-(Real.log 2 / 2) * n) := by
  unfold flowRead
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ p : Fin 4 × Fin 4, |torusState hN (2 * n - 1) β (W.fieldMap k (plaqField (N := N) (p, 0))).1
          - torusState hN (n - 1) β (W.fieldMap k (plaqField (N := N) (p, 0))).1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 4 × Fin 4, 32 * (2 * ((W.range k + 1 : ℕ) : ℝ) + 1) ^ 4 * 2 * 2 ^ (W.range k + 1)
          * Real.exp (-(Real.log 2 / 2) * n) :=
        Finset.sum_le_sum fun p _ =>
          doubling_sub_le_reach hN hβ (W.range k + 1) n _ (abs_flowPlaq_le hN W k p)
            (hasReach_flowPlaq W k p)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **The flowed reading at a reach `≤ θ n / 2`**: `≤ 32 · reachTail θ n` once `2 (W.range k + 1) ≤ θ n`.
DERIVED: `32 = 16 · 2` the ordered planes and the range; `65536 = 2^{16}` the strong-coupling threshold. -/
theorem flowRead_sub_le_tail (hN : N ≠ 0) (W : ConfFlow N) (k : ℕ) {β : ℝ} (hβ : |β| ≤ 1 / 65536)
    {θ : ℝ} (hθ : θ ≤ 1) (n : ℕ) (hr : 2 * ((W.range k : ℝ) + 1) ≤ θ * n) :
    |flowRead hN W k (2 * n) β - flowRead hN W k n β| ≤ 32 * reachTail θ n := by
  unfold flowRead
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ p : Fin 4 × Fin 4, |torusState hN (2 * n - 1) β (W.fieldMap k (plaqField (N := N) (p, 0))).1
          - torusState hN (n - 1) β (W.fieldMap k (plaqField (N := N) (p, 0))).1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 4 × Fin 4, 2 * reachTail θ n :=
        Finset.sum_le_sum fun p _ =>
          doubling_sub_le_tail hN hβ hθ (W.range k + 1) n (by push_cast; linarith) _
            (abs_flowPlaq_le hN W k p) (hasReach_flowPlaq W k p)
    _ = 32 * reachTail θ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        norm_num
        ring

/-- The strong-coupling bound on the flowed doubling rate. DERIVED: `16 = 2⁴` and `4` from `flowDelta`;
`32` from `flowRead_sub_le_tail`. -/
def strongReachBound (θ : ℝ) (n : ℕ) : ℝ := 16 * (n : ℝ) ^ 4 * (32 * reachTail θ n)

/-- DERIVED: `65536 = 2^{16}`. -/
theorem abs_flowDelta_le_tail (hN : N ≠ 0) (W : ConfFlow N) (k : ℕ) {x : ℝ} (hx : |x| ≤ 1 / 65536)
    {θ : ℝ} (hθ : θ ≤ 1) (n : ℕ) (hr : 2 * ((W.range k : ℝ) + 1) ≤ θ * n) :
    |flowDelta hN W k n x| ≤ strongReachBound θ n := by
  unfold flowDelta strongReachBound
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 4)]
  exact mul_le_mul_of_nonneg_left (flowRead_sub_le_tail hN W k hx hθ n hr) (by positivity)

/-- **The flowed defect at strong coupling**: `|flowDefect hN W k n β| ≤ β · strongReachBound θ n` on
`0 ≤ β ≤ 2^{-16}`, at `2 (W.range k + 1) ≤ θ n`. DERIVED: `0` the lower coupling; `65536 = 2^{16}`. -/
theorem abs_flowDefect_le_tail (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) {θ β : ℝ} (hθ : θ ≤ 1)
    (hr : 2 * ((W.range k : ℝ) + 1) ≤ θ * n) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    |MassGap.FlowComp.flowDefect hN W k n β| ≤ β * strongReachBound θ n := by
  unfold MassGap.FlowComp.flowDefect
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := β)
    (f := fun x => flowDelta hN W k n x) (C := strongReachBound θ n) (fun x hx => by
      rw [Set.uIoc_of_le hβ0] at hx
      rw [Real.norm_eq_abs]
      exact abs_flowDelta_le_tail hN W k (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hθ n hr)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hβ0] at h
  linarith

/-- DERIVED: `262144 = 16 · 32 · 32 · 16`; `8 = 4 + 4`; `1` the least side. -/
theorem tendsto_strongReachBound {θ : ℝ} (hθ : θ < 1) : Tendsto (strongReachBound θ) atTop (𝓝 0) := by
  have hc : 0 < Real.log 2 / 2 * (1 - θ) := mul_pos half_log_two_pos (by linarith)
  have h := (tendsto_pow_exp 8 hc).const_mul 262144
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold strongReachBound reachTail; positivity) ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold strongReachBound reachTail
  have hs := succ_pow_four_le hn
  have hE := (Real.exp_pos (-(Real.log 2 / 2 * (1 - θ) * n))).le
  calc 16 * (n : ℝ) ^ 4 * (32 * (32 * ((n : ℝ) + 1) ^ 4 * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n))))
      ≤ 16 * (n : ℝ) ^ 4 * (32 * (32 * (16 * (n : ℝ) ^ 4)
          * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n)))) := by gcongr
    _ = 262144 * ((n : ℝ) ^ 8 * Real.exp (-(Real.log 2 / 2 * (1 - θ) * n))) := by ring

/-! ## 6. The strong part of the coupling split -/

/-- **The window side grows**: at `C > 0`, for every `n₀`, eventually in `β` every side in the window is at
least `n₀`. DERIVED: `2` the window's lower edge `C/2`; `1` the successor keeping the bound positive. -/
theorem eventually_inWin_ge (hN : N ≠ 0) {C : ℝ} (hC : 0 < C) (n₀ : ℕ) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → n₀ ≤ n := by
  have hb : 0 < C / (2 * ((n₀ : ℝ) + 1)) := by positivity
  filter_upwards [MassGap.WeakCouplingWindow.eventually_aRun_le (N := N)
    (Nat.one_le_iff_ne_zero.mpr hN) hb] with β ha n hw
  by_contra hlt
  have hn : (n : ℝ) ≤ n₀ + 1 := by
    have : n ≤ n₀ + 1 := by omega
    exact_mod_cast this
  have h1 := hw.2.2.1
  have h2 : (n : ℝ) * MassGap.AsymptoticScaling.aRun N β ≤ n * (C / (2 * ((n₀ : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left ha n.cast_nonneg
  have h3 : (n : ℝ) * (C / (2 * ((n₀ : ℝ) + 1))) ≤ ((n₀ : ℝ) + 1) * (C / (2 * ((n₀ : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right hn hb.le
  have h4 : ((n₀ : ℝ) + 1) * (C / (2 * ((n₀ : ℝ) + 1))) = C / 2 := by
    field_simp
  linarith

/-- **The strong part of `FlowComp.flowEnergyComp_of_split` from a reach hypothesis on the flow.** At
`x₀ = 2^{-16}`, `C > 0`, `θ < 1`, `η > 0` and any `K`: if eventually in `β` the window side `n` has
`2 (W.range (κ β) + 1) ≤ θ n`, then eventually in `β`, at the window side,
`defectW N x₀ n − K · flowDefect hN W (κ β) n x₀ ≤ η`. DERIVED: `65536 = 2^{16}`; `2` splitting `η`;
`1` keeping `|K| + 1` positive. -/
theorem strongPart_of_reach (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) {C K θ η : ℝ} (hC : 0 < C)
    (hθ : θ < 1) (hη : 0 < η)
    (hr : ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n → 2 * ((W.range (κ β) : ℝ) + 1) ≤ θ * n) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      MassGap.ZoomSelfScale.defectW N (1 / 65536) n
        - K * MassGap.FlowComp.flowDefect hN W (κ β) n (1 / 65536) ≤ η := by
  have hK1 : 0 < |K| + 1 := by positivity
  have ev1 := (tendsto_order.mp tendsto_strongBound).2 (η / 2) (by positivity)
  have ev2 := (tendsto_order.mp (tendsto_strongReachBound hθ)).2 (η / (2 * (|K| + 1))) (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (ev1.and ev2)
  filter_upwards [hr, eventually_inWin_ge hN hC n₀] with β hrβ hwβ n hw
  obtain ⟨hb1, hb2⟩ := hn₀ n (hwβ n hw)
  have hn0 : n ≠ 0 := by have := hw.2.1; omega
  have hD := abs_defectW_strong_le hN hn0 (β := 1 / 65536) (by norm_num) le_rfl
  have hF := abs_flowDefect_le_tail hN W (κ β) n hθ.le (hrβ n hw) (by norm_num) le_rfl
  have hs1 : 0 ≤ strongBound n := by unfold strongBound; positivity
  have hs2 : 0 ≤ strongReachBound θ n := by unfold strongReachBound reachTail; positivity
  have hKF : -(K * MassGap.FlowComp.flowDefect hN W (κ β) n (1 / 65536))
      ≤ |K| * |MassGap.FlowComp.flowDefect hN W (κ β) n (1 / 65536)| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have hKb : |K| * (η / (2 * (|K| + 1))) ≤ η / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg K]
  have hD' := (le_abs_self (MassGap.ZoomSelfScale.defectW N (1 / 65536) n)).trans hD
  have hK0 := abs_nonneg K
  have e1 : (1 / 65536 : ℝ) * strongBound n ≤ η / 2 := by nlinarith
  have e2 : |K| * |MassGap.FlowComp.flowDefect hN W (κ β) n (1 / 65536)| ≤ η / 2 := by
    calc _ ≤ |K| * ((1 / 65536) * strongReachBound θ n) := mul_le_mul_of_nonneg_left hF hK0
      _ ≤ |K| * (η / (2 * (|K| + 1))) := mul_le_mul_of_nonneg_left (by nlinarith) hK0
      _ ≤ η / 2 := hKb
  linarith

/-- **A flow of bounded lattice range at the observer's step meets the reach hypothesis** (at `θ = 1/2`),
so the strong part holds. DERIVED: `2` and `4 = 2 · 2` the reach condition at `θ = 1/2`; `1` the plaquette's
sup-radius; `65536 = 2^{16}` the strong-coupling threshold. -/
theorem strongPart_of_bounded_range (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) {C K η : ℝ} (hC : 0 < C)
    (hη : 0 < η) {ρ : ℕ} (hρ : ∀ β, W.range (κ β) ≤ ρ) :
    ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
      MassGap.ZoomSelfScale.defectW N (1 / 65536) n
        - K * MassGap.FlowComp.flowDefect hN W (κ β) n (1 / 65536) ≤ η := by
  refine strongPart_of_reach hN W κ (θ := 1 / 2) hC (by norm_num) hη ?_
  filter_upwards [eventually_inWin_ge hN hC (4 * (ρ + 1))] with β hw n hn
  have h1 : ((4 * (ρ + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hw n hn
  have h2 : (W.range (κ β) : ℝ) ≤ ρ := by exact_mod_cast hρ β
  push_cast at h1
  linarith

end MassGap.StrongLocalFiniteSize

#print axioms MassGap.StrongLocalFiniteSize.card_box
#print axioms MassGap.StrongLocalFiniteSize.hasReach_plaqField
#print axioms MassGap.StrongLocalFiniteSize.hasReach_flowPlaq
#print axioms MassGap.StrongLocalFiniteSize.torusState_sub_le_reach
#print axioms MassGap.StrongLocalFiniteSize.doubling_sub_le_reach
#print axioms MassGap.StrongLocalFiniteSize.doubling_sub_le_reach_exp
#print axioms MassGap.StrongLocalFiniteSize.tendsto_doubling_reach
#print axioms MassGap.StrongLocalFiniteSize.doubling_sub_le_tail
#print axioms MassGap.StrongLocalFiniteSize.tendsto_reachTail
#print axioms MassGap.StrongLocalFiniteSize.bareRead_sub_le_reach
#print axioms MassGap.StrongLocalFiniteSize.flowRead_sub_le_reach
#print axioms MassGap.StrongLocalFiniteSize.flowRead_sub_le_tail
#print axioms MassGap.StrongLocalFiniteSize.abs_flowDefect_le_tail
#print axioms MassGap.StrongLocalFiniteSize.tendsto_strongReachBound
#print axioms MassGap.StrongLocalFiniteSize.eventually_inWin_ge
#print axioms MassGap.StrongLocalFiniteSize.strongPart_of_reach
#print axioms MassGap.StrongLocalFiniteSize.strongPart_of_bounded_range
