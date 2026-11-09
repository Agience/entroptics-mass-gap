import Mathlib
import MassGap.CasimirStep

/-!
# MassGap.AxisSplit — the window step split axis by axis: what the transverse doubling of a directional count needs

`x : Pt → ℝ` is `log Z` on the torus with sides `2^{v_μ} n_μ` (`DoublingRecursion`), `p x μ v = 2x(v) − x(v+e_μ)` the
one-direction defect, which on a spectral line is `log R₂` of the full transfer spectrum along `μ` at time `2^{v_μ} n_μ`
(`DoublingRecursion.defect`). The window step `Δ x v = 16 x(v) − x(v+𝟙)` is four single-axis doublings. Its split is in
the tree: `DefectBound.path_eq` and `DefectBound.Dw_succ_eq` (`D(w+1) = 8P₀ + 4P₁ + 2P₂ + P₃` for the Wilson torus of
every compact group), with `DefectBound.stepD_eq` reading each `P_i` as the trace defect of the slice transfer
operator. `CasimirStep` holds the one-direction facts: `defect_double_le` (`p` does not increase along its own
direction, at every value), `p_succ_le_of_lineSpectral`, the mixed second difference `mixed` and
`mixed_eq_two_p_sub`, and the no-go `not_vanishing_of_lineSpectral`. This module reads the transverse step against
them. Declarations are in the namespace `MassGap.AxisSplit`.

## 1. The exchange identity (proved)

* `mixed_comm`: `mixed x μ ν v = mixed x ν μ v`.
* `exchange`: `p_μ(v+e_ν) − 2p_μ(v) = p_ν(v+e_μ) − 2p_ν(v)`. The change of the `μ`-count across a `ν`-doubling is the
  change of the `ν`-count across a `μ`-doubling. It is algebra on four corners; no positivity enters.
* `transverse_lower`: with `p ≥ 0`, `2p_μ(v) − 2p_ν(v) ≤ p_μ(v+e_ν)`.
* `exchange_of_swapInv`: if `x` is invariant under the swap of axes `μ`, `ν` and `v` is fixed by it, then
  `p_μ(v+e_ν) = p_ν(v+e_μ)` and `p_μ(v) = p_ν(v)`. At such a corner both sides of `exchange` are the same number: the
  axis-exchange symmetry of the torus maps the identity to itself and adds no inequality.

## 2. One-direction facts and the full symmetry do not compare across a transverse doubling (proved)

`chiX c u = −c · 2^{|u|} · [at least two of the u_μ are ≥ 1]`.

* `chiX_positive`, `chiX_time`, `chiX_perm`: for `c ≥ 0` it satisfies `DoublingRecursion.Positive` (`p ≥ 0` and the
  squaring below `1/4`), `p_μ(v+e_μ) ≤ p_μ(v)` in every direction, and is invariant under every permutation of the
  four axes.
* `chiX_p_zero`, `chiX_p_E1`: `p_0(0) = 0` and `p_0(e_1) = 4c`.
* `no_transverse_bound`: so for every `B` there is such an `x` with `p_0(0) = 0` and `B < p_0(e_1)`, for every real `B`. No bound
  `p_μ(v+e_ν) ≤ φ(p_μ(v))` with `φ(0) = 0` follows from positivity, squaring, time monotonicity and axis symmetry.
* `not_transverseDouble`: in particular `TransverseDouble` (below) does not follow from them.

Scope (argued, not proved here): `chiX` is not line-spectral, since `p_0(e_1) > 0 = p_0(e_1+e_0)` along one line is
excluded by a finite spectrum (rank one at time `2m` forces rank one at time `m`). The test is of the inequalities the
tree states about `x`, not of every spectral line.

## 3. The window step under a transverse bound (proved)

`TransverseDouble x`: `p_μ(v+e_ν) ≤ 2p_μ(v)` for `μ ≠ ν`, i.e. `0 ≤ mixed` (`transverseDouble_iff`): a transverse
doubling at most squares the directional Rényi-2 count. `TimeContract x κ`: `p_μ(v+e_μ) ≤ κ p_μ(v)`.

* `Δ_path`: `Δ x v = 8p_0(v) + 4p_1(v+e_0) + 2p_2(v+e_0+e_1) + p_3(v+e_0+e_1+e_2)` at every corner; it generalizes
  `DefectBound.path_eq`, which is its corner-`1` case.
* `window_le`: `TransverseDouble x` and `TimeContract x κ` (`κ ≥ 0`) give `Δ x (v+𝟙) ≤ 8κ Δ x v`. Each axis
  meets one time doubling (`κ`) and three transverse doublings (`2³ = 8`).
* `window_le_eight`: line-spectral `x` has `κ = 1` (`CasimirStep.p_succ_le_of_lineSpectral`), so
  `Δ x (v+𝟙) ≤ 8 Δ x v`.
* `corner_le`: `Δ x (k𝟙) ≤ (8κ)^k Δ x 0`; `window_le_self`: with `p ≥ 0` and `κ ≥ 0`, `8κ ≤ 1` gives
  `Δ x (v+𝟙) ≤ Δ x v`; `window_le_self_of_lineSpectral`: the same for line-spectral `x`, where `p ≥ 0` is
  `p_nonneg_of_lineSpectral`.
* `degX u = 2^{u_1+u_2+u_3} log 2` (`2^{transverse volume}` exactly degenerate ground levels along axis `0`):
  `degX_lineSpectral`, `degX_transverseDouble`, `degX_window : Δ degX (k𝟙) = 8^k · 8 log 2`. The factor `8` of
  `window_le_eight` is attained, so line spectra with `TransverseDouble` leave the defect growing like `8^w`, the
  surface order of `DefectBound.surface_bound`.

## The remaining inequality

The axis split carries the window step only with two inputs, both open:

* (T) `TransverseDouble`: `x(v+e_μ+e_ν) + 4x(v) ≥ 2x(v+e_μ) + 2x(v+e_ν)` for `μ ≠ ν`. Writing `Z(a,b)` for the
  partition function with sides `a L_μ`, `b L_ν` (the other two sides fixed), the four partition functions of the
  unit square of corners satisfy `Z(2,2) Z(1,1)^4 ≥ Z(2,1)^2 Z(1,2)^2`. It is a two-axis inequality: §2 shows it is not a consequence of the
  one-axis facts and symmetry, and the tree proves it for no Wilson torus.
* (K) a time contraction `8κ ≤ 1` at the window scale: the directional count at time `2m` at most `1/8` of its value
  at `m`. On a line spectrum this is decay of the excited weight at the window time, the gap at that scale; `κ = 1` is
  all the tree proves (`CasimirStep.defect_double_le`), and a line spectrum attains it (`CasimirStep.lineSpectral_const`,
  two exactly degenerate levels, and `degX`), so no one-direction argument gives `κ < 1`.

(T) is not a restatement of the next-window floor, `TransferBand.WindowOverlap` or `BasinGrowth.RelLip`: the floor is a
lower bound on `D(w+1)` (`CountDoubling.floor_of_count` reads it as a count bound in time), `WindowOverlap` compares
covariances, `RelLip` is a `β`-derivative. (T) together with (K) gives the self-similar decrease `D(w+1) ≤ D(w)` of
`CasimirStep.windowCoupling_succ_le_iff` along the diagonal. Argued, not proved here: (K) alone is the gap at the window scale.

## What does not follow

* No bound on `D` along the windows: `window_le_eight` is attained (`degX_window`).
* (T) is not proved at any coupling for any group, and §2 rules out a proof from one-axis positivity and symmetry.
  Whether it holds for every line-spectral `x` is not settled here.
* The module reads abstract corner functions; the Wilson corner function `xWG` enters only through
  `DefectBound.path_eq`, not through a statement here.

DERIVED (module-wide): `8 = 2³` the three transverse doublings an axis meets in one window step and the first
corner-path weight; `16 = 2⁴`; `4`, `2`, `1` the other path weights and the doubling; `3` the last direction label of
`Fin 4`; `2` in `log 2` the degeneracy of one transverse site. Proof-internal: `4c = c · 2^{|e_1| + 1}`; in `window_le`, `64 = 8 · 8`, `32 = 8 · 4`, `16 = 8 · 2`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.AxisSplit

open Finset MassGap.DoublingRecursion MassGap.CasimirStep

/-! ## 0. Corners -/

/-- DERIVED: `0`, `1` the entries of a unit vector. -/
theorem E_apply (μ i : Fin 4) : E μ i = if i = μ then 1 else 0 := by
  fin_cases μ <;> fin_cases i <;> rfl

/-- The diagonal step is the four unit steps. DERIVED: `0`–`3` the four directions. -/
theorem one_eq : one = E 0 + E 1 + E 2 + E 3 := by decide

/-! ## 1. The exchange identity -/

/-- **The mixed second difference is symmetric.** DERIVED: no numeral beyond those of `mixed`. -/
theorem mixed_comm (x : Pt → ℝ) (μ ν : Fin 4) (v : Pt) : mixed x μ ν v = mixed x ν μ v := by
  unfold mixed
  rw [add_right_comm v (E μ) (E ν)]
  ring

/-- **The exchange identity**: `p_μ(v+e_ν) − 2p_μ(v) = p_ν(v+e_μ) − 2p_ν(v)`. DERIVED: `2` the doubling. -/
theorem exchange (x : Pt → ℝ) (μ ν : Fin 4) (v : Pt) :
    p x μ (v + E ν) - 2 * p x μ v = p x ν (v + E μ) - 2 * p x ν v := by
  have h1 := mixed_eq_two_p_sub x μ ν v
  have h2 := mixed_eq_two_p_sub x ν μ v
  rw [mixed_comm] at h1
  linarith

/-- **The transverse lower bound**: `2p_μ(v) − 2p_ν(v) ≤ p_μ(v+e_ν)`. DERIVED: `2` the doubling. -/
theorem transverse_lower {x : Pt → ℝ} (hx : Positive x) (μ ν : Fin 4) (v : Pt) :
    2 * p x μ v - 2 * p x ν v ≤ p x μ (v + E ν) := by
  have := exchange x μ ν v
  have := hx.nonneg ν (v + E μ)
  linarith

/-- The swap of axes `μ`, `ν` on corners. DERIVED: no numeral. -/
def swapPt (μ ν : Fin 4) (v : Pt) : Pt := v ∘ Equiv.swap μ ν

/-- `x` is invariant under the swap of axes `μ`, `ν`. DERIVED: no numeral. -/
def SwapInv (x : Pt → ℝ) (μ ν : Fin 4) : Prop := ∀ v, x (swapPt μ ν v) = x v

/-- DERIVED: no numeral. -/
theorem swapPt_add (μ ν : Fin 4) (v u : Pt) : swapPt μ ν (v + u) = swapPt μ ν v + swapPt μ ν u := rfl

/-- DERIVED: no numeral. -/
theorem swapPt_E_right (μ ν : Fin 4) : swapPt μ ν (E ν) = E μ := by
  funext i
  simp only [swapPt, Function.comp, E_apply]
  rcases eq_or_ne i μ with h | h
  · subst h; simp
  · rcases eq_or_ne i ν with h' | h'
    · subst h'; simp [Equiv.swap_apply_right, Ne.symm h, h]
    · rw [Equiv.swap_apply_of_ne_of_ne h h']; simp [h, h']

/-- DERIVED: no numeral. -/
theorem swapPt_E_left (μ ν : Fin 4) : swapPt μ ν (E μ) = E ν := by
  have : swapPt μ ν = swapPt ν μ := by funext v; simp [swapPt, Equiv.swap_comm]
  rw [this, swapPt_E_right]

/-- **The symmetry maps the exchange identity to itself**: at a corner fixed by the swap of `μ`, `ν`, a swap-invariant
`x` has `p_μ(v+e_ν) = p_ν(v+e_μ)` and `p_μ(v) = p_ν(v)`. DERIVED: `2` the doubling inside `p`. -/
theorem exchange_of_swapInv {x : Pt → ℝ} {μ ν : Fin 4} (hx : SwapInv x μ ν) {v : Pt}
    (hv : swapPt μ ν v = v) :
    p x μ (v + E ν) = p x ν (v + E μ) ∧ p x μ v = p x ν v := by
  have a1 : x (v + E μ) = x (v + E ν) := by
    rw [← hx (v + E μ), swapPt_add, hv, swapPt_E_left]
  have a2 : x (v + E μ + E ν) = x (v + E ν + E μ) := by
    rw [← hx (v + E μ + E ν), swapPt_add, swapPt_add, hv, swapPt_E_left, swapPt_E_right]
  refine ⟨?_, ?_⟩
  · unfold p; rw [a1, a2]
  · unfold p; rw [a1]

/-! ## 2. A positive, time-monotone, symmetric corner function with no transverse comparison -/

/-- The number of axes on which a corner is at least `1`. DERIVED: `1` the first doubling. -/
def cnt (u : Pt) : ℕ := ∑ i, if 1 ≤ u i then 1 else 0

/-- The total doubling count `|u|`. DERIVED: no numeral. -/
def tot (u : Pt) : ℕ := ∑ i, u i

/-- At least two axes doubled. DERIVED: `2` the two axes; `0`, `1` the indicator values. -/
def ind (u : Pt) : ℝ := if 2 ≤ cnt u then 1 else 0

/-- **The test corner function** `−c · 2^{|u|} · ind u`. DERIVED: `2` the volume factor of a doubling. -/
def chiX (c : ℝ) (u : Pt) : ℝ := -(c * 2 ^ tot u * ind u)

/-- DERIVED: `1` the unit step. -/
theorem tot_add_E (u : Pt) (μ : Fin 4) : tot (u + E μ) = tot u + 1 := by
  simp [tot, Finset.sum_add_distrib, E_apply]

/-- DERIVED: `1` the unit step. -/
theorem cnt_mono (u : Pt) (μ : Fin 4) : cnt u ≤ cnt (u + E μ) := by
  unfold cnt
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply]
  split_ifs <;> omega

/-- A second step in the same direction adds no axis. DERIVED: `1` the unit step. -/
theorem cnt_idem (u : Pt) (μ : Fin 4) : cnt (u + E μ + E μ) = cnt (u + E μ) := by
  unfold cnt
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, E_apply]
  split_ifs <;> omega

/-- DERIVED: `0`, `1` the indicator values. -/
theorem ind_mono (u : Pt) (μ : Fin 4) : ind u ≤ ind (u + E μ) := by
  have hm := cnt_mono u μ
  unfold ind
  by_cases h1 : 2 ≤ cnt u
  · have h2 : 2 ≤ cnt (u + E μ) := le_trans h1 hm
    simp [h1, h2]
  · by_cases h2 : 2 ≤ cnt (u + E μ) <;> simp [h1, h2]

/-- **The defect of the test function**: `p_μ(u) = c 2^{|u|+1} (ind(u+e_μ) − ind u)`.
DERIVED: `2` the doubling; `1` the unit step. -/
theorem chiX_p (c : ℝ) (μ : Fin 4) (u : Pt) :
    p (chiX c) μ u = c * 2 ^ (tot u + 1) * (ind (u + E μ) - ind u) := by
  unfold p chiX
  rw [tot_add_E]
  ring

/-- DERIVED: `0` the value. -/
theorem chiX_p_succ (c : ℝ) (μ : Fin 4) (u : Pt) : p (chiX c) μ (u + E μ) = 0 := by
  rw [chiX_p]
  simp [ind, cnt_idem]

/-- DERIVED: `0` the sign. -/
theorem chiX_p_nonneg {c : ℝ} (hc : 0 ≤ c) (μ : Fin 4) (u : Pt) : 0 ≤ p (chiX c) μ u := by
  rw [chiX_p]
  have := ind_mono u μ
  have : (0 : ℝ) ≤ 2 ^ (tot u + 1) := by positivity
  have : 0 ≤ ind (u + E μ) - ind u := by linarith
  positivity

/-- **The test function is positive**: `p ≥ 0`, and the squaring below `1/4` holds since the next defect is `0`.
DERIVED: `4` the squaring constant of `Positive`. -/
theorem chiX_positive {c : ℝ} (hc : 0 ≤ c) : Positive (chiX c) where
  nonneg μ v := chiX_p_nonneg hc μ v
  sq μ v _ := by rw [chiX_p_succ]; positivity

/-- **The test function is time-monotone in every direction.** DERIVED: no numeral. -/
theorem chiX_time {c : ℝ} (hc : 0 ≤ c) (μ : Fin 4) (v : Pt) :
    p (chiX c) μ (v + E μ) ≤ p (chiX c) μ v := by
  rw [chiX_p_succ]; exact chiX_p_nonneg hc μ v

/-- **The test function is invariant under every permutation of the axes.** DERIVED: no numeral. -/
theorem chiX_perm (c : ℝ) (σ : Equiv.Perm (Fin 4)) (v : Pt) : chiX c (v ∘ σ) = chiX c v := by
  have ht : tot (v ∘ σ) = tot v := Equiv.sum_comp σ (fun i => v i)
  have hn : cnt (v ∘ σ) = cnt v := Equiv.sum_comp σ (fun i => if 1 ≤ v i then 1 else 0)
  simp only [chiX, ind, ht, hn]

/-- DERIVED: `0` the value. -/
theorem chiX_p_zero (c : ℝ) : p (chiX c) 0 0 = 0 := by
  rw [chiX_p]
  have h1 : cnt (E 0) = 1 := by decide
  have h0 : cnt (0 : Pt) = 0 := by decide
  simp [ind, h1, h0]

/-- DERIVED: `4 = 2^{|e_1|+1}`, `|e_1| = 1`. -/
theorem chiX_p_E1 (c : ℝ) : p (chiX c) 0 (E 1) = 4 * c := by
  rw [chiX_p]
  have h2 : cnt (E 1 + E 0) = 2 := by decide
  have h1 : cnt (E 1) = 1 := by decide
  have ht : tot (E 1) = 1 := by decide
  simp only [ind, h2, h1, ht]
  norm_num
  ring

/-- **No transverse comparison from the one-direction facts**: for every `B` some corner function that is positive,
time-monotone in every direction and invariant under every permutation of the axes has `p_0(0) = 0` and
`p_0(e_1) > B`. DERIVED: `0`, `1` the corners and directions; `4` from `chiX_p_E1`. -/
theorem no_transverse_bound (B : ℝ) :
    ∃ x : Pt → ℝ, Positive x ∧ (∀ μ v, p x μ (v + E μ) ≤ p x μ v) ∧
      (∀ (σ : Equiv.Perm (Fin 4)) v, x (v ∘ σ) = x v) ∧ p x 0 0 = 0 ∧ B < p x 0 (E 1) := by
  set c := max B 0 + 1
  have hc : 0 ≤ c := by positivity
  refine ⟨chiX c, chiX_positive hc, chiX_time hc, chiX_perm c, chiX_p_zero c, ?_⟩
  rw [chiX_p_E1]
  have : B ≤ max B 0 := le_max_left _ _
  have : 0 ≤ max B 0 := le_max_right _ _
  linarith

/-! ## 3. The window step under a transverse bound -/

/-- **The transverse bound**: a doubling of axis `ν ≠ μ` at most doubles the `μ`-defect (at most squares the
`μ`-count). DERIVED: `2` the doubling. -/
def TransverseDouble (x : Pt → ℝ) : Prop := ∀ μ ν v, μ ≠ ν → p x μ (v + E ν) ≤ 2 * p x μ v

/-- **The time contraction** at rate `κ`. DERIVED: no numeral. -/
def TimeContract (x : Pt → ℝ) (κ : ℝ) : Prop := ∀ μ v, p x μ (v + E μ) ≤ κ * p x μ v

/-- DERIVED: `0` the sign. -/
theorem transverseDouble_iff (x : Pt → ℝ) :
    TransverseDouble x ↔ ∀ μ ν v, μ ≠ ν → 0 ≤ mixed x μ ν v := by
  refine ⟨fun h μ ν v hμν => ?_, fun h μ ν v hμν => ?_⟩
  · rw [mixed_eq_two_p_sub]; linarith [h μ ν v hμν]
  · have := h μ ν v hμν; rw [mixed_eq_two_p_sub] at this; linarith

/-- **`TransverseDouble` does not follow from positivity, time monotonicity and axis symmetry.**
DERIVED: `1` the test scale `c`; `0`, `1` the directions. -/
theorem not_transverseDouble :
    ¬ ∀ x : Pt → ℝ, Positive x → (∀ μ v, p x μ (v + E μ) ≤ p x μ v) →
      (∀ (σ : Equiv.Perm (Fin 4)) v, x (v ∘ σ) = x v) → TransverseDouble x := by
  intro h
  have := h (chiX 1) (chiX_positive zero_le_one) (chiX_time zero_le_one) (chiX_perm 1) 0 1 0 (by decide)
  rw [zero_add, chiX_p_E1, chiX_p_zero] at this
  norm_num at this

/-- **The corner path at every corner.** DERIVED: `8, 4, 2, 1` the path weights; `16 = 2⁴`; `0`–`3` the
directions. -/
theorem Δ_path (x : Pt → ℝ) (v : Pt) :
    Δ x v = 8 * p x 0 v + 4 * p x 1 (v + E 0) + 2 * p x 2 (v + E 0 + E 1)
      + p x 3 (v + E 0 + E 1 + E 2) := by
  have h : v + E 0 + E 1 + E 2 + E 3 = v + one := by rw [one_eq]; abel
  unfold Δ p
  rw [h]
  ring

section Window

variable {x : Pt → ℝ} {κ : ℝ}

/-- One transverse step. DERIVED: `2` the doubling. -/
theorem tstep (hT : TransverseDouble x) (μ ν : Fin 4) (h : μ ≠ ν) (u : Pt) {B : ℝ} (hb : p x μ u ≤ B) :
    p x μ (u + E ν) ≤ 2 * B :=
  (hT μ ν u h).trans (by linarith)

/-- One time step. DERIVED: no numeral. -/
theorem kstep (hK : TimeContract x κ) (hκ : 0 ≤ κ) (μ : Fin 4) (u : Pt) {B : ℝ} (hb : p x μ u ≤ B) :
    p x μ (u + E μ) ≤ κ * B :=
  (hK μ u).trans (mul_le_mul_of_nonneg_left hb hκ)

/-- **The window step under the transverse bound**: `Δ x (v+𝟙) ≤ 8κ Δ x v`. DERIVED: `8 = 2³` the three
transverse doublings each axis meets; `0`–`3` the directions. Proof-internal: `64 = 8 · 8`, `32 = 8 · 4`,
`16 = 8 · 2`, the window factor times the path weights. -/
theorem window_le (hκ : 0 ≤ κ) (hT : TransverseDouble x) (hK : TimeContract x κ) (v : Pt) :
    Δ x (v + one) ≤ 8 * κ * Δ x v := by
  have b0 : p x 0 (v + one) ≤ 2 * (2 * (2 * (κ * p x 0 v))) := by
    have e : v + one = v + E 0 + E 1 + E 2 + E 3 := by rw [one_eq]; abel
    rw [e]
    exact tstep hT 0 3 (by decide) _ (tstep hT 0 2 (by decide) _ (tstep hT 0 1 (by decide) _
      (kstep hK hκ 0 _ le_rfl)))
  have b1 : p x 1 (v + one + E 0) ≤ 2 * (2 * (κ * (2 * p x 1 (v + E 0)))) := by
    have e : v + one + E 0 = v + E 0 + E 0 + E 1 + E 2 + E 3 := by rw [one_eq]; abel
    rw [e]
    exact tstep hT 1 3 (by decide) _ (tstep hT 1 2 (by decide) _ (kstep hK hκ 1 _
      (tstep hT 1 0 (by decide) _ le_rfl)))
  have b2 : p x 2 (v + one + E 0 + E 1) ≤ 2 * (κ * (2 * (2 * p x 2 (v + E 0 + E 1)))) := by
    have e : v + one + E 0 + E 1 = v + E 0 + E 1 + E 0 + E 1 + E 2 + E 3 := by rw [one_eq]; abel
    rw [e]
    exact tstep hT 2 3 (by decide) _ (kstep hK hκ 2 _ (tstep hT 2 1 (by decide) _
      (tstep hT 2 0 (by decide) _ le_rfl)))
  have b3 : p x 3 (v + one + E 0 + E 1 + E 2)
      ≤ κ * (2 * (2 * (2 * p x 3 (v + E 0 + E 1 + E 2)))) := by
    have e : v + one + E 0 + E 1 + E 2 = v + E 0 + E 1 + E 2 + E 0 + E 1 + E 2 + E 3 := by
      rw [one_eq]; abel
    rw [e]
    exact kstep hK hκ 3 _ (tstep hT 3 2 (by decide) _ (tstep hT 3 1 (by decide) _
      (tstep hT 3 0 (by decide) _ le_rfl)))
  rw [Δ_path x (v + one), Δ_path x v]
  have r1 : κ * (2 * p x 1 (v + E 0)) = 2 * (κ * p x 1 (v + E 0)) := by ring
  have r2 : κ * (2 * (2 * p x 2 (v + E 0 + E 1))) = 4 * (κ * p x 2 (v + E 0 + E 1)) := by ring
  have r3 : κ * (2 * (2 * (2 * p x 3 (v + E 0 + E 1 + E 2))))
      = 8 * (κ * p x 3 (v + E 0 + E 1 + E 2)) := by ring
  have goal : 8 * κ * (8 * p x 0 v + 4 * p x 1 (v + E 0) + 2 * p x 2 (v + E 0 + E 1)
      + p x 3 (v + E 0 + E 1 + E 2))
      = 64 * (κ * p x 0 v) + 32 * (κ * p x 1 (v + E 0)) + 16 * (κ * p x 2 (v + E 0 + E 1))
        + 8 * (κ * p x 3 (v + E 0 + E 1 + E 2)) := by ring
  rw [goal]
  linarith

/-- The window step is nonnegative when every directional defect is. DERIVED: `0` the sign. -/
theorem Δ_nonneg_of (hp : ∀ μ v, 0 ≤ p x μ v) (v : Pt) : 0 ≤ Δ x v := by
  rw [Δ_path]
  have := hp 0 v; have := hp 1 (v + E 0); have := hp 2 (v + E 0 + E 1); have := hp 3 (v + E 0 + E 1 + E 2)
  linarith

/-- **Along the diagonal**: `Δ x (k𝟙) ≤ (8κ)^k Δ x 0`. DERIVED: `8` as in `window_le`. -/
theorem corner_le (hκ : 0 ≤ κ) (hT : TransverseDouble x) (hK : TimeContract x κ) :
    ∀ k : ℕ, Δ x (corner k) ≤ (8 * κ) ^ k * Δ x (corner 0) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [corner_succ]
    have h := window_le hκ hT hK (corner k)
    have h8 : 0 ≤ 8 * κ := by positivity
    calc Δ x (corner k + one) ≤ 8 * κ * Δ x (corner k) := h
      _ ≤ 8 * κ * ((8 * κ) ^ k * Δ x (corner 0)) := mul_le_mul_of_nonneg_left ih h8
      _ = (8 * κ) ^ (k + 1) * Δ x (corner 0) := by ring

/-- **A contraction by `1/8` gives the self-similar decrease.** DERIVED: `8` as in `window_le`; `1` the bound. -/
theorem window_le_self (hκ : 0 ≤ κ) (h8 : 8 * κ ≤ 1) (hp : ∀ μ v, 0 ≤ p x μ v) (hT : TransverseDouble x)
    (hK : TimeContract x κ) (v : Pt) : Δ x (v + one) ≤ Δ x v := by
  have h := window_le hκ hT hK v
  have h0 := Δ_nonneg_of hp v
  nlinarith

end Window

/-- A line-spectral defect is nonnegative. DERIVED: `0`, `1` the first two points of the line. -/
theorem p_nonneg_of_lineSpectral {x : Pt → ℝ} (hx : LineSpectral x) (μ : Fin 4) (v : Pt) : 0 ≤ p x μ v := by
  obtain ⟨s, w, i₀, m, hT, hl⟩ := hx μ v
  have h0 := hl 0
  have h1 := hl 1
  simp only [zero_smul, add_zero, pow_zero, one_mul, one_smul, pow_one] at h0 h1
  have := defect_nonneg hT m
  unfold p
  unfold defect at this
  rw [h0, h1]
  linarith

/-- **Line spectra and the transverse bound give at most the factor `8` per window.** DERIVED: `8` as in
`window_le`; `1` the rate `κ` of `CasimirStep.p_succ_le_of_lineSpectral`. -/
theorem window_le_eight {x : Pt → ℝ} (hx : LineSpectral x) (hT : TransverseDouble x) (v : Pt) :
    Δ x (v + one) ≤ 8 * Δ x v := by
  have := window_le zero_le_one hT (fun μ u => by rw [one_mul]; exact p_succ_le_of_lineSpectral hx μ u) v
  linarith

/-- **A contraction by `1/8` gives the self-similar decrease on line spectra.** DERIVED: `8` as in `window_le`;
`1` the bound. -/
theorem window_le_self_of_lineSpectral {x : Pt → ℝ} {κ : ℝ} (hx : LineSpectral x) (hκ : 0 ≤ κ) (h8 : 8 * κ ≤ 1)
    (hT : TransverseDouble x) (hK : TimeContract x κ) (v : Pt) : Δ x (v + one) ≤ Δ x v :=
  window_le_self hκ h8 (p_nonneg_of_lineSpectral hx) hT hK v

/-! ### The factor `8` is attained -/

/-- **The extensively degenerate corner function**: `2^{u_1+u_2+u_3}` exactly degenerate levels along axis `0`.
DERIVED: `2` the degeneracy of one transverse site; `1`, `2`, `3` the transverse directions. -/
def degX (u : Pt) : ℝ := 2 ^ (u 1 + u 2 + u 3) * Real.log 2

/-- DERIVED: `0` the axis of the degeneracy; `2` the doubling. -/
theorem degX_add_E (u : Pt) (μ : Fin 4) : degX (u + E μ) = (if μ = 0 then 1 else 2) * degX u := by
  fin_cases μ <;> simp [degX, E, pow_add, pow_succ] <;> ring

/-- DERIVED: `0`, `1` the axis label and the stated value. -/
theorem degX_line (u : Pt) (μ : Fin 4) (j : ℕ) :
    degX (u + j • E μ) = (if μ = 0 then 1 else 2 ^ j) * degX u := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [succ_nsmul, ← add_assoc, degX_add_E, ih]
    split_ifs <;> ring

/-- **`degX` is line-spectral**: along axis `0` a line of `2^{2^n}` levels of weight `1`; along the other axes one level
of weight `2^{2^n}`, `n = u_1 + u_2 + u_3`. DERIVED: `2` the degeneracy; `0`, `1` the top label and the time. -/
theorem degX_lineSpectral : LineSpectral degX := by
  intro μ v
  set n := v 1 + v 2 + v 3 with hn
  by_cases hμ : μ = 0
  · refine ⟨Finset.range (2 ^ 2 ^ n), fun _ => 1, 0, 1,
      ⟨by simp, one_pos, fun _ _ => zero_le_one, fun _ _ => le_rfl⟩, fun j => ?_⟩
    rw [degX_line, if_pos hμ, one_mul]
    simp only [powSum, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [degX, ← hn]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  · refine ⟨{0}, fun _ => (2 : ℝ) ^ 2 ^ n, 0, 1,
      ⟨by simp, by positivity, fun _ _ => by positivity, fun _ _ => le_rfl⟩, fun j => ?_⟩
    rw [degX_line, if_neg hμ]
    simp only [powSum, Finset.sum_singleton, mul_one]
    rw [← pow_mul, Real.log_pow, degX, ← hn]
    push_cast
    ring

/-- DERIVED: `0` the axis; `2` the doubling. -/
theorem degX_p (μ : Fin 4) (u : Pt) : p degX μ u = (if μ = 0 then 1 else 0) * degX u := by
  unfold p
  rw [degX_add_E]
  split_ifs <;> ring

/-- **`degX` satisfies the transverse bound**, with equality along axis `0`. DERIVED: `2` the doubling. -/
theorem degX_transverseDouble : TransverseDouble degX := by
  intro μ ν u hμν
  rw [degX_p, degX_p, degX_add_E]
  have hl : (0 : ℝ) ≤ degX u := by unfold degX; have := Real.log_pos one_lt_two; positivity
  by_cases hμ : μ = 0
  · have hν : ν ≠ 0 := fun h => hμν (hμ.trans h.symm)
    rw [if_pos hμ, if_neg hν]; linarith
  · rw [if_neg hμ]; simp

/-- DERIVED: `8 = 2³` the three transverse doublings of axis `0`'s degeneracy. -/
theorem degX_one (u : Pt) : degX (u + one) = 8 * degX u := by
  rw [one_eq, ← add_assoc, ← add_assoc, ← add_assoc, degX_add_E, degX_add_E, degX_add_E, degX_add_E]
  simp only [Fin.isValue, if_true, Fin.reduceEq, if_false]
  ring

/-- DERIVED: `8 = 16 − 8` the defect of axis `0`'s weight `8`; `16 = 2⁴`. -/
theorem degX_Δ (u : Pt) : Δ degX u = 8 * degX u := by
  unfold Δ
  rw [degX_one]
  ring

/-- **The factor `8` is attained**: `Δ degX (k𝟙) = 8^k · 8 log 2`. DERIVED: `8` as in `window_le_eight`; `2`
the degeneracy. -/
theorem degX_window (k : ℕ) : Δ degX (corner k) = 8 ^ k * (8 * Real.log 2) := by
  induction k with
  | zero =>
    rw [degX_Δ]
    simp [degX, corner]
  | succ k ih =>
    rw [corner_succ, degX_Δ, degX_one, ← degX_Δ, ih]
    ring

end MassGap.AxisSplit

end

#print axioms MassGap.AxisSplit.mixed_comm
#print axioms MassGap.AxisSplit.exchange
#print axioms MassGap.AxisSplit.transverse_lower
#print axioms MassGap.AxisSplit.exchange_of_swapInv
#print axioms MassGap.AxisSplit.chiX_positive
#print axioms MassGap.AxisSplit.chiX_time
#print axioms MassGap.AxisSplit.chiX_perm
#print axioms MassGap.AxisSplit.no_transverse_bound
#print axioms MassGap.AxisSplit.not_transverseDouble
#print axioms MassGap.AxisSplit.Δ_path
#print axioms MassGap.AxisSplit.window_le
#print axioms MassGap.AxisSplit.corner_le
#print axioms MassGap.AxisSplit.window_le_self
#print axioms MassGap.AxisSplit.window_le_eight
#print axioms MassGap.AxisSplit.window_le_self_of_lineSpectral
#print axioms MassGap.AxisSplit.degX_lineSpectral
#print axioms MassGap.AxisSplit.degX_transverseDouble
#print axioms MassGap.AxisSplit.degX_window
