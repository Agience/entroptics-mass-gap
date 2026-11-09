import Mathlib
import MassGap.ApertureCount
import MassGap.ApertureGap

/-!
# MassGap.FreeLevels — the level decay of the free flowed spectrum, in closed form

`ApertureCount.ApertureCountAt` carries the count hypothesis H3: at every aperture, `apDim ≤ D` and the
occupation of the `i`-th rung of a geometric ladder is at most `c · apDim · (i + 1)^r`. This module proves
H3, and the Rényi-½ bound it feeds, for the spectrum of the free flowed field on the aperture box: the heat
spectrum `λ_k = w_k e^{−2t μ_k}` with `μ_k` the Dirichlet levels of the lattice Laplacian. The constants
are `π`, `e`, the dimension and the local weight ratio `κ` (the weight ratio over the modes within `Y`
e-folds of the top is at most `e^{κY}`); none depends on the zoom `K`. For the massless propagator `κ`
is fixed by the lower bound `τ ≤ 2t/L²` on the flow time relative to the aperture, so the constants are
uniform across apertures exactly while that bound holds; a flow time fixed in lattice units has
`2t/L² → 0`.
Declarations are in the namespace `MassGap.FreeLevels`.

## 1. Reindexing (proved)

`spDim`, `spRenyi` and `levelCount` are invariant under a relabelling of the modes
(`spDim_comp_equiv`, `spRenyi_comp_equiv`, `levelCount_comp_equiv`), so a screen whose Gram spectrum is the
free spectrum up to an equivalence of index sets reads the same counts.

## 2. Two entropy bounds (proved)

* `spDim_ge_of_le` (min-entropy below Shannon): if every weight is at most `M`, then
  `∑ w / M ≤ exp H`.
* `spDim_le_spRenyi` (Shannon below Rényi-½): `exp H ≤ R = (∑ √p)²`. Per mode,
  `−p log p ≤ 2√p/Q − 2p + 2p log Q` with `Q = ∑ √p` (`negMulLog_le_renyi`, from `log x ≤ x − 1`), and the
  sum of the right side is `2 log Q`.

## 3. The heat spectrum (proved)

`heatSpec w u k = w_k e^{−u_k}` with weights in `[w₋, w₊]` and `u` minimal at `k₀`. The heat count
`heatCount u k₀ Y = #{k : u_k − u_{k₀} ≤ Y}` counts the modes within `Y` e-folds of the top.

* `levelCount_heat_le`: the `i`-th rung holds at most `heatCount(log(w₊/w₋) − 2(i + 1) log a)` modes.
* `spDim_heat_ge`: `(w₋/w₊) e^{−Y} heatCount(Y) ≤ exp H` (from `spDim_ge_of_le` at `M = w₊ e^{−u_{k₀}}`).
* `WeylGrowth u k₀ c₀ q m`: `heatCount(Y) ≤ c₀ (1 + qY)^m heatCount(1)` for every `Y ≥ 0` — the heat
  count grows polynomially from its first e-fold.
* `levelCount_heat_weyl` (H3 for the heat spectrum): under `WeylGrowth`,
  `levelCount_i ≤ c₀ e ω (1 + q(log ω − 2 log a))^m · exp H · (i + 1)^m`, `ω = w₊/w₋`, at every ladder
  `a ∈ (0, 1)`.
* `spRenyi_heat_le`, `spRenyi_heat_le_spDim` (the Rényi-½ count): under `WeylGrowth`,
  `R ≤ A² ω e heatCount(1) ≤ A² (ω e)² exp H`, `A = c₀ (1 − 2q log a)^m (1 − a) ∑_i (i + 1)^m a^i`. The
  layer cake runs on `λ_k / (w₊ e^{−u_{k₀}})`, whose rungs are heat counts, and `heatCount(1) ≤ ω e exp H`.
  The factor is linear in the measured count.

## 4. The Dirichlet box (proved)

The box has `K` modes per direction, side `L`, `K + 1` cells; `ApertureGap.phat L K j` is the lattice
momentum of the Dirichlet mode `j ∈ {1, …, K}`.

* `phat_eigen`, `phat_dirichlet`: `sin(θ n)`, `θ = π j/(K + 1)`, is an eigenvector of the one-direction
  lattice Laplacian `(2f(n) − f(n − 1) − f(n + 1))/h²`, `h = L/(K + 1)`, at eigenvalue `phat²`, and vanishes
  at `n = 0` and `n = K + 1`. The box level of `k ∈ {1, …, K}^d` is `μ_k = ∑_μ phat(k_μ)²` (`boxU = 2t μ`).
* `gap1_ge`, `gap1_le`: with `σ = 2t/L²`, one direction's gap `2t(phat(j)² − phat(1)²)` lies between
  `σ(4j² − π²)` and `σ π² j²` (`ApertureGap.phat_ge`, `phat_le`: `2j/L ≤ phat ≤ πj/L`).
* `n1_ratio`: the one-direction count `n₁(Y) = #{j : gap ≤ Y}` has `n₁(Y)² ≤ π²(1 + Y/Z) n₁(Z)²`, uniformly
  in `σ` and `K` (two cases: every mode is inside `Z`, or the count inside `Z` is at least half the radius).
* `heatCount_le_pow`, `heatCount_ge_pow`: the box count lies between `n₁(Y/d)^d` and `n₁(Y)^d`.
* `box_weyl`: in `d = 2m` dimensions the box heat spectrum meets `WeylGrowth` with `c₀ = π^d`, `q = d`.

## 5. H3 for the free spectrum (proved)

* `free_h3` (global weight ratio): a relabelled box heat spectrum with `2t/L² ≥ τ` and weights in
  `[w₋, ω₀ w₋]` has `exp H ≤ A² ω₀ e ((1/τ + π²)/4)^m`, `levelCount_i ≤ π^d e ω₀ (1 + d(log ω₀ − 2 log a))^m ·
  exp H · (i + 1)^m` and `R ≤ A² (ω₀ e)² exp H`. It covers flowed white noise (`ω₀ = 1`).
* `free_h3_local` (local weight ratio): the weight is absorbed into the exponent, `w e^{−u} = e^{−(u − log w)}`
  (`heatSpec_absorb`). If the top weight sits at the lowest mode and
  `log(w(k₀)/w(k)) ≤ κ (u_k − u_{k₀})` — the weight ratio over the modes within `Y` e-folds of the top is at
  most `e^{κY}` — then `u − log w` meets `WeylGrowth` with `c₀ = π^d`, `q = d(1 + κ)` (`box_weyl_local`,
  from `box_weyl_Z` at the reference level `1/(1 + κ)`), and
  `exp H ≤ A_κ² e ((1/τ + π²)/4)^m`, `levelCount_i ≤ π^d e (1 − 2d(1 + κ) log a)^m · exp H · (i + 1)^m`,
  `R ≤ A_κ² e² exp H`. No ratio over all modes enters.
* `propagator_local`: the massless propagator weight `w = 1/μ` has
  `log(μ_k/μ_{k₀}) ≤ μ_k/μ_{k₀} − 1 ≤ (u_k − u_{k₀})/(4dτ)`, because the lowest box level is at least
  `4d/L²` (`boxMu_low`) and `2t/L² ≥ τ`. So `free_h3_propagator`: the flowed massless spectrum
  `e^{−2tμ}/μ` meets H3 with every constant fixed by `τ`, `d` and the ladder, uniformly in the zoom `K`.
* `propagator_global_ratio`, `propagator_global_unbounded`: the ratio of the largest to the smallest
  propagator weight on the box is at least `4K²/π²`, so no fixed global ratio `ω₀` covers it; the hypothesis
  of `free_h3` fails for the massless field, that of `free_h3_local` holds.
* `FreeScreenSpectrum Wf b τ κ`: at every aperture `s ∈ (0, b]`, eventually in the step, for every channel,
  the observer's screen spectrum `apEig` is a relabelled box heat spectrum with `2t/L² ≥ τ` and local weight
  ratio `κ`. `h3_of_freeScreen`: it gives the H3 clause of `ApertureCountAt` exactly, at the witness ladder
  `a = e^{−1/2}` (one e-fold per rung), `r = 2`. The massless free field enters at `κ = 1/(16τ)`.

`FreeScreenSpectrum` is the spectral input. It holds for a Gaussian field whose covariance on the aperture
box is the flowed Dirichlet propagator `e^{−2tμ}/μ`, or the flowed heat kernel. The screens of
`ApertureCount` are read in the lattice gauge state `stateK`, and that their Gram spectra have this form is
not proved; the composite channels are not Gaussian.

## 6. The load-bearing test (proved)

`spRenyi_unbounded_pos` is `ApertureCount.spRenyi_unbounded_at_bounded_spDim` with every weight positive.
`weyl_load_bearing`: for every `c₀, q ≥ 0` and `m` there is a positive spectrum, written as a heat spectrum
(`u = −log p`, unit weights), that fails `WeylGrowth u k₀ c₀ q m` at every top mode `k₀`: otherwise
`spRenyi_heat_le_spDim` would bound its `R` by a fixed multiple of `exp H ≤ e²`, and `R` is unbounded. So
the polynomial growth of the heat count is what carries the bound; every positive spectrum is a heat
spectrum.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the first mode and the empty count; `1` the first e-fold (the
reference level of `heatCount`), the unit weights and the shift of the index; `2` the squares, the factor of
the flow `e^{−2tp²}`, the half-angle and the even dimension `d = 2m`; `4` the square of the lower Jordan
bound `2j/L` and the quarter in `n₁² ≤ (Y/σ + π²)/4`; `π` the upper Jordan bound `phat ≤ πj/L` and the
boundary `sin(πj) = 0`; `e` the first e-fold; `e^{−1/2}` the ladder of one e-fold per rung; `3` the bound
`π > 3`; `exp 2` the Shannon bound of the counterexample; `c₀`, `q`, `m`, `τ`, `κ`, `ω₀`, `w₋`, `w₊` hypotheses; `κ = 1/(4dτ)` of the propagator is derived from
`τ` and the Jordan factor `4`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FreeLevels

open Finset Filter
open scoped Real
open MassGap.ApertureModes MassGap.ApertureCount

/-! ## 1. Reindexing -/

section Reindex

variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- **The measured count does not see the labels**. DERIVED: no numeral. -/
theorem spDim_comp_equiv (e : κ ≃ κ') (w : κ' → ℝ) : spDim (w ∘ e) = spDim w := by
  unfold spDim
  have hS : ∑ i, (w ∘ e) i = ∑ i, w i := Equiv.sum_comp e w
  rw [hS]
  congr 1
  exact Equiv.sum_comp e (fun k => Real.negMulLog (w k / ∑ i', w i'))

/-- **The Rényi-½ count does not see the labels**. DERIVED: no numeral. -/
theorem spRenyi_comp_equiv (e : κ ≃ κ') (w : κ' → ℝ) : spRenyi (w ∘ e) = spRenyi w := by
  unfold spRenyi
  have hS : ∑ i, (w ∘ e) i = ∑ i, w i := Equiv.sum_comp e w
  rw [hS]
  congr 1
  exact Equiv.sum_comp e (fun k => Real.sqrt (w k / ∑ β, w β))

/-- **The level counts do not see the labels**. DERIVED: no numeral. -/
theorem levelCount_comp_equiv (e : κ ≃ κ') (w : κ' → ℝ) (a : ℝ) (i : ℕ) :
    levelCount (w ∘ e) a i = levelCount w a i := by
  unfold levelCount
  have hS : ∑ β, (w ∘ e) β = ∑ β, w β := Equiv.sum_comp e w
  rw [hS]
  refine Finset.card_nbij' e e.symm ?_ ?_ ?_ ?_
  · intro x hx
    simpa [Function.comp_apply] using hx
  · intro y hy
    simpa [Function.comp_apply] using hy
  · intro x _
    simp
  · intro y _
    simp

end Reindex

/-! ## 2. Two entropy bounds -/

section Entropy

variable {κ : Type*} [Fintype κ]

/-- **Min-entropy below Shannon**: weights at most `M` give `∑ w / M ≤ exp H`. DERIVED: `0` the signs. -/
theorem spDim_ge_of_le {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) {M : ℝ} (hM0 : 0 < M) (hM : ∀ k, w k ≤ M)
    (hS : 0 < ∑ k, w k) : (∑ k, w k) / M ≤ spDim w := by
  unfold spDim
  set S := ∑ k, w k with hSdef
  have hq : 0 < S / M := div_pos hS hM0
  rw [← Real.exp_log hq, Real.exp_le_exp]
  have hterm : ∀ k, w k / S * Real.log (S / M) ≤ Real.negMulLog (w k / S) := by
    intro k
    rcases (hw k).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hp : 0 < w k / S := div_pos hpos hS
      rw [Real.negMulLog, neg_mul, ← mul_neg, ← Real.log_inv, inv_div]
      refine mul_le_mul_of_nonneg_left (Real.log_le_log hq ?_) hp.le
      exact div_le_div_of_nonneg_left hS.le hpos (hM k)
  calc Real.log (S / M) = ∑ k, w k / S * Real.log (S / M) := by
        rw [← Finset.sum_mul, ← Finset.sum_div, ← hSdef, div_self hS.ne', one_mul]
    _ ≤ ∑ k, Real.negMulLog (w k / S) := Finset.sum_le_sum fun k _ => hterm k

/-- **One mode of the Shannon–Rényi comparison**: `−x log x ≤ 2√x/Q − 2x + 2x log Q` for `x ≥ 0`, `Q > 0`.
DERIVED: `2` the square root and its square; `1` the tangent `log y ≤ y − 1`. -/
theorem negMulLog_le_renyi {x Q : ℝ} (hx : 0 ≤ x) (hQ : 0 < Q) :
    Real.negMulLog x ≤ 2 / Q * Real.sqrt x - 2 * x + 2 * Real.log Q * x := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · set r := Real.sqrt x with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hxr : x = r ^ 2 := (Real.sq_sqrt hx).symm
    have hrQ : 0 < r * Q := mul_pos hr0 hQ
    have hl := Real.log_le_sub_one_of_pos (inv_pos.2 hrQ)
    rw [Real.log_inv, Real.log_mul hr0.ne' hQ.ne'] at hl
    have key := mul_le_mul_of_nonneg_left hl (sq_nonneg r)
    have e1 : r ^ 2 * (r * Q)⁻¹ = r / Q := by
      rw [sq, mul_inv, div_eq_mul_inv]
      calc r * r * (r⁻¹ * Q⁻¹) = r * (r * r⁻¹) * Q⁻¹ := by ring
        _ = r * Q⁻¹ := by rw [mul_inv_cancel₀ hr0.ne', mul_one]
    rw [mul_sub, e1, mul_one] at key
    rw [hxr, Real.negMulLog, Real.log_pow]
    push_cast
    calc -r ^ 2 * (2 * Real.log r)
        = 2 * (r ^ 2 * -(Real.log r + Real.log Q)) + 2 * Real.log Q * r ^ 2 := by ring
      _ ≤ 2 * (r / Q - r ^ 2) + 2 * Real.log Q * r ^ 2 := by linarith
      _ = 2 / Q * r - 2 * r ^ 2 + 2 * Real.log Q * r ^ 2 := by ring

/-- **Shannon below Rényi-½**: `exp H ≤ (∑ √p)²`. DERIVED: `1` the total probability; `2` the square. -/
theorem spDim_le_spRenyi {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (hS : 0 < ∑ k, w k) :
    spDim w ≤ spRenyi w := by
  set S := ∑ k, w k with hSdef
  have hp0 : ∀ k, 0 ≤ w k / S := fun k => div_nonneg (hw k) hS.le
  have hp1 : ∀ k, w k / S ≤ 1 := fun k =>
    div_le_one_of_le₀ (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ k)) hS.le
  have hsum : ∑ k, w k / S = 1 := by rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  set Q := ∑ k, Real.sqrt (w k / S) with hQdef
  have hQ1 : 1 ≤ Q := by
    rw [hQdef, ← hsum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc w k / S = Real.sqrt (w k / S) * Real.sqrt (w k / S) := (Real.mul_self_sqrt (hp0 k)).symm
      _ ≤ Real.sqrt (w k / S) * 1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 (hp1 k)) (Real.sqrt_nonneg _)
      _ = Real.sqrt (w k / S) := mul_one _
  have hQ : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hH : ∑ k, Real.negMulLog (w k / S) ≤ 2 * Real.log Q := by
    calc ∑ k, Real.negMulLog (w k / S)
        ≤ ∑ k, (2 / Q * Real.sqrt (w k / S) - 2 * (w k / S) + 2 * Real.log Q * (w k / S)) :=
          Finset.sum_le_sum fun k _ => negMulLog_le_renyi (hp0 k) hQ
      _ = 2 / Q * Q - 2 * 1 + 2 * Real.log Q * 1 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum, hsum, ← hQdef]
      _ = 2 * Real.log Q := by rw [div_mul_cancel₀ (2 : ℝ) hQ.ne']; ring
  have hR : spRenyi w = Q ^ 2 := rfl
  have hD : spDim w = Real.exp (∑ k, Real.negMulLog (w k / S)) := rfl
  rw [hR, hD]
  calc Real.exp (∑ k, Real.negMulLog (w k / S)) ≤ Real.exp (2 * Real.log Q) := Real.exp_le_exp.2 hH
    _ = Q ^ 2 := by
        rw [show (2 : ℝ) * Real.log Q = Real.log (Q ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (pow_pos hQ 2)]

end Entropy

/-! ## 3. The heat spectrum -/

section Heat

variable {κ : Type*} [Fintype κ]

/-- **The heat spectrum** `w_k e^{−u_k}`. DERIVED: no numeral. -/
def heatSpec (w u : κ → ℝ) (k : κ) : ℝ := w k * Real.exp (-u k)

/-- **The heat count**: the modes within `Y` e-folds of the mode `k₀`. DERIVED: no numeral. -/
def heatCount (u : κ → ℝ) (k₀ : κ) (Y : ℝ) : ℕ := (univ.filter fun k => u k - u k₀ ≤ Y).card

/-- **Polynomial growth of the heat count from its first e-fold**. DERIVED: `1` the first e-fold and the
unit of `1 + qY`; `0` the sign. -/
def WeylGrowth (u : κ → ℝ) (k₀ : κ) (c₀ q : ℝ) (m : ℕ) : Prop :=
  ∀ Y : ℝ, 0 ≤ Y → (heatCount u k₀ Y : ℝ) ≤ c₀ * (1 + q * Y) ^ m * heatCount u k₀ 1

variable {w u : κ → ℝ} {k₀ : κ} {wlo whi : ℝ}

/-- DERIVED: `0` the sign. -/
theorem heatSpec_nonneg (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi) (k : κ) :
    0 ≤ heatSpec w u k :=
  mul_nonneg (hwlo.le.trans (hw k).1) (Real.exp_pos _).le

/-- DERIVED: no numeral. -/
theorem heatSpec_le (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi) (k : κ) :
    heatSpec w u k ≤ whi * Real.exp (-u k₀) :=
  mul_le_mul (hw k).2 (Real.exp_le_exp.2 (neg_le_neg (hu k))) (Real.exp_pos _).le
    ((hwlo.le.trans (hw k).1).trans (hw k).2)

/-- DERIVED: `0` the sign. -/
theorem heat_sum_pos (k₀ : κ) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi) :
    0 < ∑ k, heatSpec w u k :=
  (mul_pos (hwlo.trans_le (hw k₀).1) (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun k _ => heatSpec_nonneg hwlo hw k) (Finset.mem_univ k₀))

/-- The top mode is counted at every level `Y ≥ 0`. DERIVED: `1` the count; `0` the sign. -/
theorem heatCount_pos {Y : ℝ} (hY : 0 ≤ Y) : 1 ≤ heatCount u k₀ Y :=
  Finset.one_le_card.2 ⟨k₀, by simp [hY]⟩

/-- **The mass within `Y` e-folds**: `w₋ e^{−u_{k₀}} e^{−Y} heatCount(Y) ≤ ∑ λ`. DERIVED: no numeral. -/
theorem heat_sum_ge (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi) (Y : ℝ) :
    wlo * Real.exp (-u k₀) * Real.exp (-Y) * heatCount u k₀ Y ≤ ∑ k, heatSpec w u k := by
  calc wlo * Real.exp (-u k₀) * Real.exp (-Y) * (heatCount u k₀ Y : ℝ)
      = ∑ k ∈ univ.filter (fun k => u k - u k₀ ≤ Y), wlo * Real.exp (-u k₀) * Real.exp (-Y) := by
        rw [Finset.sum_const, nsmul_eq_mul]; unfold heatCount; ring
    _ ≤ ∑ k ∈ univ.filter (fun k => u k - u k₀ ≤ Y), heatSpec w u k := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter] at hk
        rw [mul_assoc, ← Real.exp_add, heatSpec]
        exact mul_le_mul (hw k).1 (Real.exp_le_exp.2 (by linarith [hk.2])) (Real.exp_pos _).le
          (hwlo.le.trans (hw k).1)
    _ ≤ ∑ k, heatSpec w u k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => heatSpec_nonneg hwlo hw k

/-- **The measured count is at least the heat count**: `(w₋/w₊) e^{−Y} heatCount(Y) ≤ exp H`.
DERIVED: no numeral. -/
theorem spDim_heat_ge (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi)
    (Y : ℝ) : wlo / whi * Real.exp (-Y) * heatCount u k₀ Y ≤ spDim (heatSpec w u) := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have hM : 0 < whi * Real.exp (-u k₀) := mul_pos hwhi (Real.exp_pos _)
  have h2 := spDim_ge_of_le (heatSpec_nonneg hwlo hw) hM (heatSpec_le hu hwlo hw)
    (heat_sum_pos (k₀ := k₀) hwlo hw)
  refine le_trans ?_ h2
  rw [le_div_iff₀ hM]
  have e : wlo / whi * Real.exp (-Y) * (heatCount u k₀ Y : ℝ) * (whi * Real.exp (-u k₀))
      = wlo / whi * whi * (Real.exp (-u k₀) * Real.exp (-Y) * heatCount u k₀ Y) := by ring
  rw [e, div_mul_cancel₀ wlo hwhi.ne']
  calc wlo * (Real.exp (-u k₀) * Real.exp (-Y) * (heatCount u k₀ Y : ℝ))
      = wlo * Real.exp (-u k₀) * Real.exp (-Y) * heatCount u k₀ Y := by ring
    _ ≤ _ := heat_sum_ge hwlo hw Y

/-- **The first e-fold against the measured count**: `heatCount(1) ≤ (w₊/w₋) e · exp H`.
DERIVED: `1` the first e-fold. -/
theorem heatCount_one_le (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi) :
    (heatCount u k₀ 1 : ℝ) ≤ whi / wlo * Real.exp 1 * spDim (heatSpec w u) := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have h := spDim_heat_ge hu hwlo hw 1
  have hc : 0 ≤ whi / wlo * Real.exp 1 := mul_nonneg (div_nonneg hwhi.le hwlo.le) (Real.exp_pos 1).le
  have h' := mul_le_mul_of_nonneg_left h hc
  have h1 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have h2 : whi / wlo * (wlo / whi) = 1 := by
    rw [div_mul_div_comm, mul_comm whi wlo, div_self (mul_pos hwlo hwhi).ne']
  have e : whi / wlo * Real.exp 1 * (wlo / whi * Real.exp (-1) * (heatCount u k₀ 1 : ℝ))
      = heatCount u k₀ 1 := by
    calc _ = (whi / wlo * (wlo / whi)) * (Real.exp 1 * Real.exp (-1)) * (heatCount u k₀ 1 : ℝ) := by ring
      _ = heatCount u k₀ 1 := by rw [h1, h2, one_mul, one_mul]
  rw [e] at h'
  exact h'

/-- **A rung holds only modes near the top**: the `i`-th rung is inside
`heatCount(log(w₊/w₋) − 2(i + 1) log a)`. DERIVED: `1`, `2` as in `levelCount`. -/
theorem levelCount_heat_le (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi)
    {a : ℝ} (ha0 : 0 < a) (i : ℕ) :
    levelCount (heatSpec w u) a i ≤ heatCount u k₀ (Real.log (whi / wlo) - 2 * (i + 1) * Real.log a) := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have hS := heat_sum_pos (u := u) (k₀ := k₀) hwlo hw
  unfold levelCount heatCount
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨Finset.mem_univ k, ?_⟩
  have h1 : a ^ (2 * (i + 1)) * ∑ β, heatSpec w u β < heatSpec w u k := by
    have := hk.2
    rwa [lt_div_iff₀ hS] at this
  have hlo : wlo * Real.exp (-u k₀) ≤ ∑ β, heatSpec w u β :=
    (mul_le_mul_of_nonneg_right (hw k₀).1 (Real.exp_pos _).le).trans
      (Finset.single_le_sum (fun k _ => heatSpec_nonneg hwlo hw k) (Finset.mem_univ k₀))
  have hhi : heatSpec w u k ≤ whi * Real.exp (-u k) :=
    mul_le_mul_of_nonneg_right (hw k).2 (Real.exp_pos _).le
  have h2 : a ^ (2 * (i + 1)) * (wlo * Real.exp (-u k₀)) < whi * Real.exp (-u k) :=
    calc a ^ (2 * (i + 1)) * (wlo * Real.exp (-u k₀)) ≤ a ^ (2 * (i + 1)) * ∑ β, heatSpec w u β :=
          mul_le_mul_of_nonneg_left hlo (pow_nonneg ha0.le _)
      _ < heatSpec w u k := h1
      _ ≤ whi * Real.exp (-u k) := hhi
  have h3 := Real.log_lt_log (mul_pos (pow_pos ha0 _) (mul_pos hwlo (Real.exp_pos _))) h2
  rw [Real.log_mul (pow_pos ha0 _).ne' (mul_pos hwlo (Real.exp_pos _)).ne',
    Real.log_mul hwlo.ne' (Real.exp_pos _).ne', Real.log_mul hwhi.ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp, Real.log_exp] at h3
  rw [Real.log_div hwhi.ne' hwlo.ne']
  push_cast at h3
  linarith

/-- **H3 for the heat spectrum**: under `WeylGrowth`,
`levelCount_i ≤ c₀ e ω (1 + q(log ω − 2 log a))^m · exp H · (i + 1)^m`, `ω = w₊/w₋`.
DERIVED: `1` the first e-fold and the shift of the index; `2` as in `levelCount`. -/
theorem levelCount_heat_weyl (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi)
    {c₀ q : ℝ} {m : ℕ} (hc₀ : 0 ≤ c₀) (hq : 0 ≤ q) (hW : WeylGrowth u k₀ c₀ q m)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (i : ℕ) :
    (levelCount (heatSpec w u) a i : ℝ)
      ≤ c₀ * Real.exp 1 * (whi / wlo) * (1 + q * (Real.log (whi / wlo) - 2 * Real.log a)) ^ m
        * spDim (heatSpec w u) * ((i : ℝ) + 1) ^ m := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have hla : Real.log a < 0 := Real.log_neg ha0 ha1
  have hlω : 0 ≤ Real.log (whi / wlo) :=
    Real.log_nonneg ((one_le_div hwlo).2 ((hw k₀).1.trans (hw k₀).2))
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  set Yi := Real.log (whi / wlo) - 2 * ((i : ℝ) + 1) * Real.log a with hYi
  have hY : 0 ≤ Yi := by
    have : 0 ≤ ((i : ℝ) + 1) * -Real.log a := mul_nonneg (by positivity) (by linarith)
    rw [hYi]; linarith
  have h1 : (levelCount (heatSpec w u) a i : ℝ) ≤ heatCount u k₀ Yi :=
    Nat.cast_le.mpr (levelCount_heat_le hu hwlo hw ha0 i)
  have h2 : (heatCount u k₀ Yi : ℝ) ≤ c₀ * (1 + q * Yi) ^ m * heatCount u k₀ 1 := hW Yi hY
  have hB0 : 0 ≤ 1 + q * (Real.log (whi / wlo) - 2 * Real.log a) := by
    have : 0 ≤ q * (Real.log (whi / wlo) - 2 * Real.log a) := mul_nonneg hq (by linarith)
    linarith
  have h3 : 1 + q * Yi ≤ ((i : ℝ) + 1) * (1 + q * (Real.log (whi / wlo) - 2 * Real.log a)) := by
    have : 0 ≤ (i : ℝ) * (q * Real.log (whi / wlo)) := mul_nonneg hi0 (mul_nonneg hq hlω)
    rw [hYi]; nlinarith
  have hY0 : 0 ≤ 1 + q * Yi := by have := mul_nonneg hq hY; linarith
  have h4 := heatCount_one_le hu hwlo hw
  have hN0 : (0 : ℝ) ≤ heatCount u k₀ 1 := Nat.cast_nonneg _
  calc (levelCount (heatSpec w u) a i : ℝ) ≤ heatCount u k₀ Yi := h1
    _ ≤ c₀ * (1 + q * Yi) ^ m * heatCount u k₀ 1 := h2
    _ ≤ c₀ * (((i : ℝ) + 1) * (1 + q * (Real.log (whi / wlo) - 2 * Real.log a))) ^ m
          * heatCount u k₀ 1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 h3 m) hc₀) hN0
    _ ≤ c₀ * (((i : ℝ) + 1) * (1 + q * (Real.log (whi / wlo) - 2 * Real.log a))) ^ m
          * (whi / wlo * Real.exp 1 * spDim (heatSpec w u)) :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hc₀ (pow_nonneg (mul_nonneg (by positivity) hB0) m))
    _ = _ := by rw [mul_pow]; ring

/-- **The rungs of the spectrum relative to its top**: `#{k : a^{2(i+1)} < x_k}`. DERIVED: `1`, `2` as in
`levelCount`. -/
def rungCount (x : κ → ℝ) (a : ℝ) (i : ℕ) : ℕ := (univ.filter fun k => a ^ (2 * (i + 1)) < x k).card

/-- **The layer cake on `[0, 1]`-valued points**. DERIVED: `0`, `1` the interval; `1`, `2` as in
`levelCount`. -/
theorem sum_sqrt_le_rungs {x : κ → ℝ} (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∑ k, Real.sqrt (x k) ≤ ∑' i : ℕ, (rungCount x a i : ℝ) * (a ^ i * (1 - a)) := by
  calc ∑ k, Real.sqrt (x k)
      ≤ ∑ k, ∑' i : ℕ, (if a ^ (2 * (i + 1)) < x k then a ^ i * (1 - a) else 0) :=
        Finset.sum_le_sum fun k _ => sqrt_le_tsum_level (hx0 k) (hx1 k) ha0 ha1
    _ = ∑' i : ℕ, ∑ k, (if a ^ (2 * (i + 1)) < x k then a ^ i * (1 - a) else 0) :=
        (Summable.tsum_finsetSum fun k _ => summable_level _ ha0 ha1).symm
    _ = ∑' i : ℕ, (rungCount x a i : ℝ) * (a ^ i * (1 - a)) := by
        refine tsum_congr fun i => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rfl

/-- **A rung relative to the top is a heat count**. DERIVED: `1`, `2` as in `levelCount`. -/
theorem rungCount_heat_le (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi)
    {a : ℝ} (ha0 : 0 < a) (i : ℕ) :
    rungCount (fun k => heatSpec w u k / (whi * Real.exp (-u k₀))) a i
      ≤ heatCount u k₀ (-(2 * (i + 1) * Real.log a)) := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have hM : 0 < whi * Real.exp (-u k₀) := mul_pos hwhi (Real.exp_pos _)
  unfold rungCount heatCount
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨Finset.mem_univ k, ?_⟩
  have h1 := hk.2
  rw [lt_div_iff₀ hM] at h1
  have h2 : a ^ (2 * (i + 1)) * (whi * Real.exp (-u k₀)) < whi * Real.exp (-u k) :=
    h1.trans_le (mul_le_mul_of_nonneg_right (hw k).2 (Real.exp_pos _).le)
  have h3 := Real.log_lt_log (mul_pos (pow_pos ha0 _) hM) h2
  rw [Real.log_mul (pow_pos ha0 _).ne' hM.ne', Real.log_mul hwhi.ne' (Real.exp_pos _).ne',
    Real.log_mul hwhi.ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp, Real.log_exp] at h3
  push_cast at h3
  linarith

/-- **The Rényi-½ count of the heat spectrum**: under `WeylGrowth`,
`R ≤ A² (w₊/w₋) e · heatCount(1)`, `A = c₀ (1 − 2q log a)^m (1 − a) ∑ (i + 1)^m a^i`.
DERIVED: `1` the first e-fold; `2` the square; `1`, `2` as in `levelCount`. -/
theorem spRenyi_heat_le (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi)
    {c₀ q : ℝ} {m : ℕ} (hc₀ : 0 ≤ c₀) (hq : 0 ≤ q) (hW : WeylGrowth u k₀ c₀ q m)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    spRenyi (heatSpec w u)
      ≤ (c₀ * (1 - 2 * q * Real.log a) ^ m * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i) ^ 2
        * (whi / wlo * Real.exp 1) * heatCount u k₀ 1 := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have hnn : ∀ k, 0 ≤ heatSpec w u k := heatSpec_nonneg hwlo hw
  have hS0 := heat_sum_pos (u := u) (k₀ := k₀) hwlo hw
  have hM0 : 0 < whi * Real.exp (-u k₀) := mul_pos hwhi (Real.exp_pos _)
  have hle := heatSpec_le hu hwlo hw
  have hSlo := heat_sum_ge (u := u) (k₀ := k₀) hwlo hw 1
  have hrung := rungCount_heat_le (u := u) (k₀ := k₀) hwlo hw ha0
  have hla : Real.log a < 0 := Real.log_neg ha0 ha1
  set S := ∑ k, heatSpec w u k with hSdef
  set M := whi * Real.exp (-u k₀) with hMdef
  set N1 : ℝ := (heatCount u k₀ 1 : ℝ) with hN1
  set A := c₀ * (1 - 2 * q * Real.log a) ^ m * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i with hA
  have hx0 : ∀ k, 0 ≤ heatSpec w u k / M := fun k => div_nonneg (hnn k) hM0.le
  have hx1 : ∀ k, heatSpec w u k / M ≤ 1 := fun k => div_le_one_of_le₀ (hle k) hM0.le
  have hsq : ∑ k, Real.sqrt (heatSpec w u k / S)
      = Real.sqrt (M / S) * ∑ k, Real.sqrt (heatSpec w u k / M) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.sqrt_mul (div_nonneg hM0.le hS0.le)]
    congr 1
    rw [div_mul_div_comm, mul_comm M, mul_div_mul_right _ _ hM0.ne']
  have hR : spRenyi (heatSpec w u) = M / S * (∑ k, Real.sqrt (heatSpec w u k / M)) ^ 2 := by
    show (∑ k, Real.sqrt (heatSpec w u k / S)) ^ 2 = _
    rw [hsq, mul_pow, Real.sq_sqrt (div_nonneg hM0.le hS0.le)]
  have hS' := summable_shift_pow_geom m ha0 ha1
  have hga : ∀ i : ℕ, 0 ≤ a ^ i * (1 - a) := fun i => mul_nonneg (pow_nonneg ha0.le i) (by linarith)
  have hqa : 0 ≤ q * -Real.log a := mul_nonneg hq (by linarith)
  have hN0 : 0 ≤ N1 := Nat.cast_nonneg _
  have hbound : ∀ i : ℕ, (rungCount (fun k => heatSpec w u k / M) a i : ℝ) * (a ^ i * (1 - a))
      ≤ c₀ * (1 - 2 * q * Real.log a) ^ m * N1 * (1 - a) * (((i : ℝ) + 1) ^ m * a ^ i) := by
    intro i
    have hY : 0 ≤ -(2 * ((i : ℝ) + 1) * Real.log a) := by
      have : 0 ≤ ((i : ℝ) + 1) * -Real.log a := mul_nonneg (by positivity) (by linarith)
      linarith
    have h1 : (rungCount (fun k => heatSpec w u k / M) a i : ℝ)
        ≤ heatCount u k₀ (-(2 * ((i : ℝ) + 1) * Real.log a)) :=
      Nat.cast_le.mpr (hrung i)
    have h2 : (heatCount u k₀ (-(2 * ((i : ℝ) + 1) * Real.log a)) : ℝ)
        ≤ c₀ * (1 + q * -(2 * ((i : ℝ) + 1) * Real.log a)) ^ m * N1 := hW _ hY
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h3 : 1 + q * -(2 * ((i : ℝ) + 1) * Real.log a)
        ≤ ((i : ℝ) + 1) * (1 - 2 * q * Real.log a) := by nlinarith
    have h0 : 0 ≤ 1 + q * -(2 * ((i : ℝ) + 1) * Real.log a) := by
      have := mul_nonneg hq hY; linarith
    have h4 := pow_le_pow_left₀ h0 h3 m
    calc (rungCount (fun k => heatSpec w u k / M) a i : ℝ) * (a ^ i * (1 - a))
        ≤ (c₀ * (1 + q * -(2 * ((i : ℝ) + 1) * Real.log a)) ^ m * N1) * (a ^ i * (1 - a)) :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (hga i)
      _ ≤ (c₀ * (((i : ℝ) + 1) * (1 - 2 * q * Real.log a)) ^ m * N1) * (a ^ i * (1 - a)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hc₀) hN0) (hga i)
      _ = c₀ * (1 - 2 * q * Real.log a) ^ m * N1 * (1 - a) * (((i : ℝ) + 1) ^ m * a ^ i) := by
          rw [mul_pow]; ring
  have hsum : Summable fun i : ℕ => (rungCount (fun k => heatSpec w u k / M) a i : ℝ) * (a ^ i * (1 - a)) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (Nat.cast_nonneg _) (hga i)) hbound (hS'.mul_left _)
  have hT : ∑ k, Real.sqrt (heatSpec w u k / M) ≤ A * N1 := by
    refine (sum_sqrt_le_rungs hx0 hx1 ha0 ha1).trans ?_
    calc ∑' i : ℕ, (rungCount (fun k => heatSpec w u k / M) a i : ℝ) * (a ^ i * (1 - a))
        ≤ ∑' i : ℕ, c₀ * (1 - 2 * q * Real.log a) ^ m * N1 * (1 - a) * (((i : ℝ) + 1) ^ m * a ^ i) :=
          hsum.tsum_le_tsum hbound (hS'.mul_left _)
      _ = A * N1 := by rw [tsum_mul_left, hA]; ring
  have hSlo' : wlo * Real.exp (-u k₀) * Real.exp (-1) * N1 ≤ S := hSlo
  have key : M * N1 ≤ whi / wlo * Real.exp 1 * S := by
    have hc : 0 ≤ whi / wlo * Real.exp 1 := mul_nonneg (div_nonneg hwhi.le hwlo.le) (Real.exp_pos 1).le
    have h := mul_le_mul_of_nonneg_left hSlo' hc
    have hee : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
    have e : whi / wlo * Real.exp 1 * (wlo * Real.exp (-u k₀) * Real.exp (-1) * N1) = M * N1 := by
      calc _ = (whi / wlo * wlo) * (Real.exp 1 * Real.exp (-1)) * Real.exp (-u k₀) * N1 := by ring
        _ = M * N1 := by rw [div_mul_cancel₀ whi hwlo.ne', hee, mul_one, hMdef]
    linarith
  have hT0 : 0 ≤ ∑ k, Real.sqrt (heatSpec w u k / M) := Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  rw [hR]
  calc M / S * (∑ k, Real.sqrt (heatSpec w u k / M)) ^ 2 ≤ M / S * (A * N1) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hT 2) (div_nonneg hM0.le hS0.le)
    _ ≤ A ^ 2 * (whi / wlo * Real.exp 1) * N1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hS0]
        calc M * (A * N1) ^ 2 = (A ^ 2 * N1) * (M * N1) := by ring
          _ ≤ (A ^ 2 * N1) * (whi / wlo * Real.exp 1 * S) :=
              mul_le_mul_of_nonneg_left key (mul_nonneg (sq_nonneg A) hN0)
          _ = A ^ 2 * (whi / wlo * Real.exp 1) * N1 * S := by ring

/-- **The Rényi-½ count is a structural multiple of the measured count**: under `WeylGrowth`,
`R ≤ A² ((w₊/w₋) e)² exp H`. DERIVED: `1` the first e-fold; `2` the squares. -/
theorem spRenyi_heat_le_spDim (hu : ∀ k, u k₀ ≤ u k) (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ whi)
    {c₀ q : ℝ} {m : ℕ} (hc₀ : 0 ≤ c₀) (hq : 0 ≤ q) (hW : WeylGrowth u k₀ c₀ q m)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    spRenyi (heatSpec w u)
      ≤ (c₀ * (1 - 2 * q * Real.log a) ^ m * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i) ^ 2
        * (whi / wlo * Real.exp 1) ^ 2 * spDim (heatSpec w u) := by
  have hwhi : 0 < whi := hwlo.trans_le ((hw k₀).1.trans (hw k₀).2)
  have h1 := spRenyi_heat_le hu hwlo hw hc₀ hq hW ha0 ha1
  have h2 := heatCount_one_le hu hwlo hw
  have hc : 0 ≤ (c₀ * (1 - 2 * q * Real.log a) ^ m * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i) ^ 2
      * (whi / wlo * Real.exp 1) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (div_nonneg hwhi.le hwlo.le) (Real.exp_pos 1).le)
  calc _ ≤ _ := h1
    _ ≤ (c₀ * (1 - 2 * q * Real.log a) ^ m * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i) ^ 2
          * (whi / wlo * Real.exp 1) * (whi / wlo * Real.exp 1 * spDim (heatSpec w u)) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

end Heat

/-! ## 4. The Dirichlet box -/

section Box

variable (L t : ℝ) (K : ℕ) (hK : 0 < K)

/-- **The one-direction level** of the Dirichlet mode `j + 1`: `phat(j + 1)²`. DERIVED: `1` the shift to
the modes `{1, …, K}`; `2` the square. -/
def lev1 (j : Fin K) : ℝ := ApertureGap.phat L K ((j : ℕ) + 1) ^ 2

/-- **The flowed box level** `2t μ_k`, `μ_k = ∑_μ phat(k_μ + 1)²`. DERIVED: `2` the factor of the flow. -/
def boxU {d : ℕ} (k : Fin d → Fin K) : ℝ := 2 * t * ∑ μ, lev1 L K (k μ)

/-- **One direction's gap above the lowest mode**. DERIVED: `2` the factor of the flow; `0` the lowest
mode. -/
def gap1 (j : Fin K) : ℝ := 2 * t * (lev1 L K j - lev1 L K ⟨0, hK⟩)

/-- **The one-direction count** `n₁(Y) = #{j : gap₁(j) ≤ Y}`. DERIVED: no numeral. -/
def n1 (Y : ℝ) : ℕ := (univ.filter fun j : Fin K => gap1 L t K hK j ≤ Y).card

/-- **The Dirichlet modes are eigenvectors of the lattice Laplacian**: with `h = L/(K + 1)` and
`θ = π j/(K + 1)`, `2 sin(θn) − sin(θ(n − 1)) − sin(θ(n + 1)) = h² phat² sin(θn)`. DERIVED: `2` the second
difference and the half-angle; `1` the neighbours. -/
theorem phat_eigen {L : ℝ} (hL : 0 < L) (K j : ℕ) (n : ℝ) :
    2 * Real.sin (π * j / ((K : ℝ) + 1) * n) - Real.sin (π * j / ((K : ℝ) + 1) * (n - 1))
        - Real.sin (π * j / ((K : ℝ) + 1) * (n + 1))
      = (L / ((K : ℝ) + 1)) ^ 2 * ApertureGap.phat L K j ^ 2 * Real.sin (π * j / ((K : ℝ) + 1) * n) := by
  set x := π * j / (2 * ((K : ℝ) + 1)) with hx
  have hθ : π * j / ((K : ℝ) + 1) = 2 * x := by
    rw [hx, ← mul_div_assoc, mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  set θ := π * j / ((K : ℝ) + 1) with hθdef
  have hc : Real.cos θ = 1 - 2 * Real.sin x ^ 2 := by
    rw [hθ, Real.cos_two_mul]; have := Real.sin_sq_add_cos_sq x; linarith
  rw [show θ * (n - 1) = θ * n - θ by ring, show θ * (n + 1) = θ * n + θ by ring, Real.sin_sub,
    Real.sin_add, hc]
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  have hL0 : L ≠ 0 := hL.ne'
  have hh : L / ((K : ℝ) + 1) * (2 * ((K : ℝ) + 1) / L) = 2 := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  unfold ApertureGap.phat
  rw [← hx]
  calc 2 * Real.sin (θ * n) - (Real.sin (θ * n) * (1 - 2 * Real.sin x ^ 2) - Real.cos (θ * n) * Real.sin θ)
        - (Real.sin (θ * n) * (1 - 2 * Real.sin x ^ 2) + Real.cos (θ * n) * Real.sin θ)
      = 2 ^ 2 * Real.sin x ^ 2 * Real.sin (θ * n) := by ring
    _ = (L / ((K : ℝ) + 1) * (2 * ((K : ℝ) + 1) / L)) ^ 2 * Real.sin x ^ 2 * Real.sin (θ * n) := by
        rw [hh]
    _ = (L / ((K : ℝ) + 1)) ^ 2 * (2 * ((K : ℝ) + 1) / L * Real.sin x) ^ 2 * Real.sin (θ * n) := by ring

/-- **The Dirichlet boundary**: the mode vanishes at the far wall `n = K + 1` (and at `n = 0`).
DERIVED: `1` the wall. -/
theorem phat_dirichlet (K j : ℕ) :
    Real.sin (π * j / ((K : ℝ) + 1) * ((K : ℝ) + 1)) = 0 ∧ Real.sin (π * j / ((K : ℝ) + 1) * 0) = 0 := by
  refine ⟨?_, by simp⟩
  rw [div_mul_cancel₀ _ (by positivity), mul_comm]
  exact Real.sin_nat_mul_pi j

/-- **The lattice momentum increases with the mode**. DERIVED: `0`, `π/2` the arc of `sin`. -/
theorem phat_mono {L : ℝ} (hL : 0 < L) {K i j : ℕ} (hij : i ≤ j) (hj : j ≤ K) :
    ApertureGap.phat L K i ≤ ApertureGap.phat L K j := by
  have hi : i ≤ K := hij.trans hj
  obtain ⟨hi0, _⟩ := ApertureGap.phat_arg hi
  obtain ⟨_, hj1⟩ := ApertureGap.phat_arg hj
  unfold ApertureGap.phat
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by positivity) hL.le)
  refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hj1 ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) Real.pi_pos.le

variable {L t K}

/-- DERIVED: `0` the lowest mode; `1` the shift. -/
theorem lev1_mono (hL : 0 < L) (j : Fin K) : lev1 L K ⟨0, hK⟩ ≤ lev1 L K j := by
  have hj := j.isLt
  unfold lev1
  exact pow_le_pow_left₀ (ApertureGap.phat_nonneg hL (show (0 : ℕ) + 1 ≤ K by omega))
    (phat_mono hL (show (0 : ℕ) + 1 ≤ (j : ℕ) + 1 by omega) (show (j : ℕ) + 1 ≤ K by omega)) 2

/-- DERIVED: `0` the sign. -/
theorem gap1_nonneg (hL : 0 < L) (ht : 0 < t) (j : Fin K) : 0 ≤ gap1 L t K hK j :=
  mul_nonneg (by linarith) (sub_nonneg.2 (lev1_mono hK hL j))

/-- DERIVED: `0` the lowest mode. -/
theorem gap1_zero : gap1 L t K hK ⟨0, hK⟩ = 0 := by simp [gap1]

/-- **The gap from below**: `σ(4(j + 1)² − π²) ≤ gap₁(j)`, `σ = 2t/L²`. DERIVED: `4` the square of `2j/L`;
`π` the upper bound of the lowest mode; `2` the flow. -/
theorem gap1_ge (hL : 0 < L) (ht : 0 < t) (j : Fin K) :
    2 * t / L ^ 2 * (4 * ((j : ℝ) + 1) ^ 2 - π ^ 2) ≤ gap1 L t K hK j := by
  have hj : (j : ℕ) + 1 ≤ K := j.isLt
  have h1 := ApertureGap.phat_ge hL hj
  have h2 := ApertureGap.phat_le hL (show 1 ≤ K by omega)
  rw [Nat.cast_one, mul_one] at h2
  push_cast at h1
  have h1' : (2 * ((j : ℝ) + 1) / L) ^ 2 ≤ lev1 L K j :=
    pow_le_pow_left₀ (div_nonneg (by positivity) hL.le) h1 2
  have h2' : lev1 L K ⟨0, hK⟩ ≤ (π / L) ^ 2 :=
    pow_le_pow_left₀ (ApertureGap.phat_nonneg hL (show 1 ≤ K by omega)) h2 2
  unfold gap1
  calc 2 * t / L ^ 2 * (4 * ((j : ℝ) + 1) ^ 2 - π ^ 2)
      = 2 * t * ((2 * ((j : ℝ) + 1) / L) ^ 2 - (π / L) ^ 2) := by ring
    _ ≤ 2 * t * (lev1 L K j - lev1 L K ⟨0, hK⟩) :=
        mul_le_mul_of_nonneg_left (sub_le_sub h1' h2') (by linarith)

/-- **The gap from above**: `gap₁(j) ≤ σ π² (j + 1)²`. DERIVED: `π` the Jordan bound; `2` the flow. -/
theorem gap1_le (hL : 0 < L) (ht : 0 < t) (j : Fin K) :
    gap1 L t K hK j ≤ 2 * t / L ^ 2 * π ^ 2 * ((j : ℝ) + 1) ^ 2 := by
  have hj : (j : ℕ) + 1 ≤ K := j.isLt
  have h1 := ApertureGap.phat_le hL hj
  push_cast at h1
  have h1' : lev1 L K j ≤ (π * ((j : ℝ) + 1) / L) ^ 2 :=
    pow_le_pow_left₀ (ApertureGap.phat_nonneg hL hj) h1 2
  have h0 : 0 ≤ lev1 L K ⟨0, hK⟩ := sq_nonneg _
  unfold gap1
  calc 2 * t * (lev1 L K j - lev1 L K ⟨0, hK⟩) ≤ 2 * t * (π * ((j : ℝ) + 1) / L) ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = 2 * t / L ^ 2 * π ^ 2 * ((j : ℝ) + 1) ^ 2 := by ring

/-- A filter of `Fin K` whose members satisfy `j + 1 ≤ X` has at most `X` members. DERIVED: `1` the shift;
`0` the sign. -/
theorem card_le_of_succ_le {K : ℕ} (P : Fin K → Prop) [DecidablePred P] {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ j, P j → (j : ℝ) + 1 ≤ X) : ((univ.filter P).card : ℝ) ≤ X := by
  have hc : (univ.filter P).card ≤ (Finset.range ⌊X⌋₊).card := by
    refine Finset.card_le_card_of_injOn (fun j => (j : ℕ)) ?_ ?_
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      rw [Finset.mem_coe, Finset.mem_range]
      have h1 : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ X := by push_cast; exact h j hj.2
      have := Nat.le_floor h1
      show (j : ℕ) < ⌊X⌋₊
      omega
    · intro j _ j' _ hjj
      exact Fin.ext hjj
  rw [Finset.card_range] at hc
  calc ((univ.filter P).card : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hc
    _ ≤ X := Nat.floor_le hX

/-- A filter of `Fin K` holding every `j` with `j + 1 ≤ X` has at least `min K ⌊X⌋` members.
DERIVED: `1` the shift. -/
theorem card_ge_of_succ_le {K : ℕ} (P : Fin K → Prop) [DecidablePred P] {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ j : Fin K, (j : ℝ) + 1 ≤ X → P j) : min K ⌊X⌋₊ ≤ (univ.filter P).card := by
  have hm : min K ⌊X⌋₊ ≤ K := min_le_left _ _
  calc min K ⌊X⌋₊ = (Finset.univ : Finset (Fin (min K ⌊X⌋₊))).card := by simp
    _ ≤ (univ.filter P).card := by
      refine Finset.card_le_card_of_injOn (Fin.castLE hm) ?_ ?_
      · intro i _
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, h _ ?_⟩
        have hi : (i : ℕ) + 1 ≤ ⌊X⌋₊ := by
          have := i.isLt
          have := min_le_right K ⌊X⌋₊
          omega
        have h1 : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hi
        push_cast at h1
        show ((i : ℕ) : ℝ) + 1 ≤ X
        exact h1.trans (Nat.floor_le hX)
      · intro i _ i' _ hii
        exact Fin.castLE_injective hm hii

/-- DERIVED: no numeral. -/
theorem n1_le_K (Y : ℝ) : n1 L t K hK Y ≤ K :=
  (Finset.card_filter_le _ _).trans_eq (by simp)

/-- The lowest mode is counted at every `Y ≥ 0`. DERIVED: `1` the count; `0` the sign. -/
theorem n1_one_le {Y : ℝ} (hY : 0 ≤ Y) : 1 ≤ n1 L t K hK Y :=
  Finset.one_le_card.2 ⟨⟨0, hK⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [gap1_zero]; exact hY⟩⟩

/-- **The one-direction count from above**: `n₁(Y)² ≤ (Y/σ + π²)/4`. DERIVED: `4` the square of `2j/L`;
`π` the lowest mode; `2` the square. -/
theorem n1_sq_le (hL : 0 < L) (ht : 0 < t) {Y : ℝ} (hY : 0 ≤ Y) :
    (n1 L t K hK Y : ℝ) ^ 2 ≤ (Y / (2 * t / L ^ 2) + π ^ 2) / 4 := by
  set σ := 2 * t / L ^ 2 with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (pow_pos hL 2)
  have hB : 0 ≤ (Y / σ + π ^ 2) / 4 :=
    div_nonneg (add_nonneg (div_nonneg hY hσ0.le) (sq_nonneg π)) (by norm_num)
  have hX : (n1 L t K hK Y : ℝ) ≤ Real.sqrt ((Y / σ + π ^ 2) / 4) := by
    refine card_le_of_succ_le (fun j => gap1 L t K hK j ≤ Y) (Real.sqrt_nonneg _) fun j hj => ?_
    have hg : σ * (4 * ((j : ℝ) + 1) ^ 2 - π ^ 2) ≤ gap1 L t K hK j := gap1_ge hK hL ht j
    have h1 : 4 * ((j : ℝ) + 1) ^ 2 - π ^ 2 ≤ Y / σ := by
      rw [le_div_iff₀ hσ0]; linarith
    refine (Real.le_sqrt (by positivity) hB).2 ?_
    linarith
  calc (n1 L t K hK Y : ℝ) ^ 2 ≤ Real.sqrt ((Y / σ + π ^ 2) / 4) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hX 2
    _ = (Y / σ + π ^ 2) / 4 := Real.sq_sqrt hB

/-- **The one-direction count from below**: `min K ⌊√(Z/(σπ²))⌋ ≤ n₁(Z)`. DERIVED: `π` the Jordan bound;
`2` the square. -/
theorem n1_ge (hL : 0 < L) (ht : 0 < t) {Z : ℝ} (hZ : 0 < Z) :
    min K ⌊Real.sqrt (Z / (2 * t / L ^ 2 * π ^ 2))⌋₊ ≤ n1 L t K hK Z := by
  set σ := 2 * t / L ^ 2 with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (pow_pos hL 2)
  have hσπ : 0 < σ * π ^ 2 := mul_pos hσ0 (pow_pos Real.pi_pos 2)
  refine card_ge_of_succ_le (fun j => gap1 L t K hK j ≤ Z) (Real.sqrt_nonneg _) fun j hj => ?_
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ Z / (σ * π ^ 2) := by
    have := pow_le_pow_left₀ (by positivity) hj 2
    rwa [Real.sq_sqrt (div_nonneg hZ.le hσπ.le)] at this
  have hg : gap1 L t K hK j ≤ σ * π ^ 2 * ((j : ℝ) + 1) ^ 2 := gap1_le hK hL ht j
  calc gap1 L t K hK j ≤ σ * π ^ 2 * ((j : ℝ) + 1) ^ 2 := hg
    _ ≤ σ * π ^ 2 * (Z / (σ * π ^ 2)) := mul_le_mul_of_nonneg_left hsq hσπ.le
    _ = Z := mul_div_cancel₀ Z hσπ.ne'

/-- **The one-direction ratio, uniform in the flow time and the zoom**:
`n₁(Y)² ≤ π² (1 + Y/Z) n₁(Z)²`. DERIVED: `π` the Jordan ratio; `1` the first mode; `2` the squares and the
half radius; `3` the bound `π > 3`; `4` as in `n1_sq_le`. -/
theorem n1_ratio (hL : 0 < L) (ht : 0 < t) {Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 < Z) :
    (n1 L t K hK Y : ℝ) ^ 2 ≤ π ^ 2 * (1 + Y / Z) * (n1 L t K hK Z : ℝ) ^ 2 := by
  have hup := n1_sq_le hK hL ht hY
  have hlow := n1_ge hK hL ht hZ
  have hone := n1_one_le (L := L) (t := t) hK hZ.le
  have hYK := n1_le_K (L := L) (t := t) hK Y
  set σ := 2 * t / L ^ 2 with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (pow_pos hL 2)
  have hσπ : 0 < σ * π ^ 2 := mul_pos hσ0 (pow_pos Real.pi_pos 2)
  set X := Real.sqrt (Z / (σ * π ^ 2)) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = Z / (σ * π ^ 2) := Real.sq_sqrt (div_nonneg hZ.le hσπ.le)
  have hA : 0 ≤ Y / Z := div_nonneg hY hZ.le
  have hπ1 : 1 ≤ π ^ 2 * (1 + Y / Z) :=
    one_le_mul_of_one_le_of_one_le (by nlinarith [Real.pi_gt_three]) (by linarith)
  by_cases hc : K ≤ ⌊X⌋₊
  · rw [min_eq_left hc] at hlow
    have h1 : (n1 L t K hK Y : ℝ) ^ 2 ≤ (n1 L t K hK Z : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hYK.trans hlow) 2
    exact h1.trans (le_mul_of_one_le_left (sq_nonneg _) hπ1)
  · rw [min_eq_right (not_le.1 hc).le] at hlow
    have hn1 : (1 : ℝ) ≤ n1 L t K hK Z := by exact_mod_cast hone
    have h2n : X ≤ 2 * (n1 L t K hK Z : ℝ) := by
      have h1 := Nat.lt_floor_add_one X
      have h2 : (⌊X⌋₊ : ℝ) ≤ n1 L t K hK Z := by exact_mod_cast hlow
      linarith
    have hπne : π ≠ 0 := Real.pi_ne_zero
    have hσne : σ ≠ 0 := hσ0.ne'
    have hZne : Z ≠ 0 := hZ.ne'
    have hinv : Y / σ = π ^ 2 * X ^ 2 * (Y / Z) := by
      rw [hX2]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have h4 : X ^ 2 ≤ 4 * (n1 L t K hK Z : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hX0 h2n 2
      nlinarith
    have h5 : Y / Z * X ^ 2 ≤ Y / Z * (4 * (n1 L t K hK Z : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h4 hA
    have h6 : (1 : ℝ) ≤ (n1 L t K hK Z : ℝ) ^ 2 := one_le_pow₀ hn1
    have h7 : (X ^ 2 * (Y / Z) + 1) / 4 ≤ (1 + Y / Z) * (n1 L t K hK Z : ℝ) ^ 2 := by nlinarith
    calc (n1 L t K hK Y : ℝ) ^ 2 ≤ (Y / σ + π ^ 2) / 4 := hup
      _ = π ^ 2 * ((X ^ 2 * (Y / Z) + 1) / 4) := by rw [hinv]; ring
      _ ≤ π ^ 2 * ((1 + Y / Z) * (n1 L t K hK Z : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h7 (sq_nonneg π)
      _ = π ^ 2 * (1 + Y / Z) * (n1 L t K hK Z : ℝ) ^ 2 := by ring

/-- **The box gap is the sum of the direction gaps**. DERIVED: `0` the lowest mode. -/
theorem boxU_sub {d : ℕ} (k : Fin d → Fin K) :
    boxU L t K k - boxU L t K (fun _ : Fin d => (⟨0, hK⟩ : Fin K)) = ∑ μ, gap1 L t K hK (k μ) := by
  simp only [boxU, gap1]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]

/-- **The lowest box mode is the top of the spectrum**. DERIVED: `0` the lowest mode. -/
theorem boxU_min (hL : 0 < L) (ht : 0 < t) {d : ℕ} (k : Fin d → Fin K) :
    boxU L t K (fun _ : Fin d => (⟨0, hK⟩ : Fin K)) ≤ boxU L t K k := by
  have h := boxU_sub (L := L) (t := t) hK k
  have h0 : 0 ≤ ∑ μ, gap1 L t K hK (k μ) := Finset.sum_nonneg fun μ _ => gap1_nonneg hK hL ht (k μ)
  linarith

/-- **The box count from above**: `heatCount(Y) ≤ n₁(Y)^d`. DERIVED: no numeral. -/
theorem heatCount_le_pow (hL : 0 < L) (ht : 0 < t) {d : ℕ} (Y : ℝ) :
    (heatCount (boxU L t K (d := d)) (fun _ => ⟨0, hK⟩) Y : ℝ) ≤ (n1 L t K hK Y : ℝ) ^ d := by
  have hsub : univ.filter (fun k : Fin d → Fin K =>
        boxU L t K k - boxU L t K (fun _ : Fin d => (⟨0, hK⟩ : Fin K)) ≤ Y)
      ⊆ Fintype.piFinset (fun _ : Fin d => univ.filter fun j => gap1 L t K hK j ≤ Y) := by
    intro k hk
    rw [Finset.mem_filter, boxU_sub] at hk
    rw [Fintype.mem_piFinset]
    intro μ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, le_trans ?_ hk.2⟩
    exact Finset.single_le_sum (fun ν _ => gap1_nonneg hK hL ht (k ν)) (Finset.mem_univ μ)
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  unfold heatCount
  exact_mod_cast hc

/-- **The box count from below**: `n₁(Y/d)^d ≤ heatCount(Y)`. DERIVED: no numeral. -/
theorem heatCount_ge_pow {d : ℕ} (hd : 0 < d) (Y : ℝ) :
    (n1 L t K hK (Y / d) : ℝ) ^ d ≤ heatCount (boxU L t K (d := d)) (fun _ => ⟨0, hK⟩) Y := by
  have hd0 : (d : ℝ) ≠ 0 := (Nat.cast_pos.2 hd).ne'
  have hsub : Fintype.piFinset (fun _ : Fin d => univ.filter fun j => gap1 L t K hK j ≤ Y / d)
      ⊆ univ.filter (fun k : Fin d → Fin K =>
        boxU L t K k - boxU L t K (fun _ : Fin d => (⟨0, hK⟩ : Fin K)) ≤ Y) := by
    intro k hk
    rw [Fintype.mem_piFinset] at hk
    rw [Finset.mem_filter, boxU_sub]
    refine ⟨Finset.mem_univ _, ?_⟩
    calc ∑ μ, gap1 L t K hK (k μ) ≤ ∑ _μ : Fin d, Y / d :=
          Finset.sum_le_sum fun μ _ => (Finset.mem_filter.1 (hk μ)).2
      _ = Y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_div_cancel₀ _ hd0]
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  unfold heatCount
  exact_mod_cast hc

/-- **The box heat spectrum grows polynomially** in `d = 2m` dimensions: `WeylGrowth` with `c₀ = π^d` and
`q = d`, uniformly in the flow time, the aperture and the zoom. DERIVED: `2` the even dimension; `π` the
Jordan ratio; `1` the first e-fold. -/
theorem box_weyl (hL : 0 < L) (ht : 0 < t) {m : ℕ} (hm : 0 < m) :
    WeylGrowth (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) ((π ^ 2) ^ m) ((2 * m : ℕ) : ℝ) m := by
  intro Y hY
  have hd : 0 < 2 * m := by omega
  have hdR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := Nat.cast_pos.2 hd
  have hZ : (0 : ℝ) < 1 / ((2 * m : ℕ) : ℝ) := div_pos one_pos hdR
  have hup := heatCount_le_pow hK hL ht (d := 2 * m) Y
  have hlow := heatCount_ge_pow (L := L) (t := t) hK hd 1
  have hr := n1_ratio hK hL ht hY hZ
  have hYZ : Y / (1 / ((2 * m : ℕ) : ℝ)) = ((2 * m : ℕ) : ℝ) * Y := by
    rw [div_div_eq_mul_div, div_one, mul_comm]
  rw [hYZ] at hr
  have hq0 : 0 ≤ 1 + ((2 * m : ℕ) : ℝ) * Y := by have := mul_nonneg hdR.le hY; linarith
  calc (heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) Y : ℝ)
      ≤ (n1 L t K hK Y : ℝ) ^ (2 * m) := hup
    _ = ((n1 L t K hK Y : ℝ) ^ 2) ^ m := pow_mul _ 2 m
    _ ≤ (π ^ 2 * (1 + ((2 * m : ℕ) : ℝ) * Y) * (n1 L t K hK (1 / ((2 * m : ℕ) : ℝ)) : ℝ) ^ 2) ^ m :=
        pow_le_pow_left₀ (sq_nonneg _) hr m
    _ = (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * Y) ^ m
          * (n1 L t K hK (1 / ((2 * m : ℕ) : ℝ)) : ℝ) ^ (2 * m) := by
        rw [mul_pow, mul_pow, ← pow_mul (n1 L t K hK (1 / ((2 * m : ℕ) : ℝ)) : ℝ) 2 m]
    _ ≤ (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * Y) ^ m
          * heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) 1 :=
        mul_le_mul_of_nonneg_left hlow (mul_nonneg (pow_nonneg (sq_nonneg π) m) (pow_nonneg hq0 m))

/-- **The first e-fold of the box from above**: `heatCount(1) ≤ ((1/σ + π²)/4)^m`. DERIVED: `1` the first
e-fold; `2`, `4` as in `n1_sq_le`. -/
theorem heatCount_one_box_le (hL : 0 < L) (ht : 0 < t) {m : ℕ} :
    (heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) 1 : ℝ)
      ≤ ((1 / (2 * t / L ^ 2) + π ^ 2) / 4) ^ m := by
  have hup := heatCount_le_pow hK hL ht (d := 2 * m) 1
  have h1 := n1_sq_le hK hL ht (Y := 1) zero_le_one
  calc (heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) 1 : ℝ)
      ≤ (n1 L t K hK 1 : ℝ) ^ (2 * m) := hup
    _ = ((n1 L t K hK 1 : ℝ) ^ 2) ^ m := pow_mul _ 2 m
    _ ≤ ((1 / (2 * t / L ^ 2) + π ^ 2) / 4) ^ m := pow_le_pow_left₀ (sq_nonneg _) h1 m

end Box

/-! ## 5. H3 for the free spectrum -/

section Free

open scoped Real

/-- **The Rényi-½ factor of the box** in `d = 2m`: `π^d (1 − 2d log a)^m (1 − a) ∑ (i + 1)^m a^i`.
DERIVED: `2` the even dimension and the ladder square; `π` the Jordan ratio; `1` the shift. -/
def renyiFactor (m : ℕ) (a : ℝ) : ℝ :=
  (π ^ 2) ^ m * (1 - 2 * ((2 * m : ℕ) : ℝ) * Real.log a) ^ m * (1 - a)
    * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i

variable {L t : ℝ} {K : ℕ}

/-- **H3 and the Rényi-½ bound for the free spectrum**: a spectrum that is the box heat spectrum up to
relabelling, with `2t/L² ≥ τ` and weights in `[w₋, ω₀ w₋]`, has `exp H ≤ A² ω₀ e ((1/τ + π²)/4)^m`,
`levelCount_i ≤ π^d e ω₀ (1 + d(log ω₀ − 2 log a))^m · exp H · (i + 1)^m` and `R ≤ A² (ω₀ e)² exp H`.
DERIVED: `2` the even dimension and the flow; `1` the first e-fold; `π` the Jordan ratio. -/
theorem free_h3 {κ' : Type*} [Fintype κ'] (hK : 0 < K) (hL : 0 < L) (ht : 0 < t) {m : ℕ} (hm : 0 < m)
    {τ ω₀ : ℝ} (hτ : 0 < τ) (hτσ : τ ≤ 2 * t / L ^ 2)
    {w : (Fin (2 * m) → Fin K) → ℝ} {wlo : ℝ} (hwlo : 0 < wlo) (hw : ∀ k, wlo ≤ w k ∧ w k ≤ ω₀ * wlo)
    {lam : κ' → ℝ} (e : κ' ≃ (Fin (2 * m) → Fin K)) (hlam : lam = heatSpec w (boxU L t K) ∘ e)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    spDim lam ≤ renyiFactor m a ^ 2 * (ω₀ * Real.exp 1) * ((1 / τ + π ^ 2) / 4) ^ m
      ∧ (∀ i : ℕ, (levelCount lam a i : ℝ)
          ≤ (π ^ 2) ^ m * Real.exp 1 * ω₀ * (1 + ((2 * m : ℕ) : ℝ) * (Real.log ω₀ - 2 * Real.log a)) ^ m
            * spDim lam * ((i : ℝ) + 1) ^ m)
      ∧ spRenyi lam ≤ renyiFactor m a ^ 2 * (ω₀ * Real.exp 1) ^ 2 * spDim lam := by
  subst hlam
  rw [spDim_comp_equiv, spRenyi_comp_equiv]
  have hω : ω₀ * wlo / wlo = ω₀ := mul_div_cancel_right₀ ω₀ hwlo.ne'
  have hω0 : 0 ≤ ω₀ := by
    have h := (hwlo.le.trans (hw (fun _ => ⟨0, hK⟩)).1).trans (hw (fun _ => ⟨0, hK⟩)).2
    exact nonneg_of_mul_nonneg_left h hwlo
  have hu := boxU_min (L := L) (t := t) hK hL ht (d := 2 * m)
  have hW := box_weyl (L := L) (t := t) hK hL ht hm
  have hc₀ : (0 : ℝ) ≤ (π ^ 2) ^ m := pow_nonneg (sq_nonneg π) m
  have hq : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, fun i => ?_, ?_⟩
  · have h1 := spDim_le_spRenyi (heatSpec_nonneg (u := boxU L t K) hwlo hw)
      (heat_sum_pos (k₀ := fun _ => ⟨0, hK⟩) hwlo hw)
    have h2 := spRenyi_heat_le hu hwlo hw hc₀ hq hW ha0 ha1
    rw [hω] at h2
    have h3 := heatCount_one_box_le (L := L) (t := t) hK hL ht (m := m)
    have h4 : ((1 / (2 * t / L ^ 2) + π ^ 2) / 4) ^ m ≤ ((1 / τ + π ^ 2) / 4) ^ m := by
      have h5 : 1 / (2 * t / L ^ 2) ≤ 1 / τ := one_div_le_one_div_of_le hτ hτσ
      have h6 : 0 ≤ (1 / (2 * t / L ^ 2) + π ^ 2) / 4 :=
        div_nonneg (add_nonneg (div_nonneg zero_le_one (hτ.le.trans hτσ)) (sq_nonneg π)) (by norm_num)
      exact pow_le_pow_left₀ h6 (by linarith) m
    have hc : 0 ≤ renyiFactor m a ^ 2 * (ω₀ * Real.exp 1) := mul_nonneg (sq_nonneg _)
      (mul_nonneg hω0 (Real.exp_pos 1).le)
    calc spDim (heatSpec w (boxU L t K)) ≤ spRenyi (heatSpec w (boxU L t K)) := h1
      _ ≤ renyiFactor m a ^ 2 * (ω₀ * Real.exp 1)
            * heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) 1 := h2
      _ ≤ renyiFactor m a ^ 2 * (ω₀ * Real.exp 1) * ((1 / τ + π ^ 2) / 4) ^ m :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hc
  · rw [levelCount_comp_equiv]
    have h := levelCount_heat_weyl hu hwlo hw hc₀ hq hW ha0 ha1 i
    rw [hω] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  · have h := spRenyi_heat_le_spDim hu hwlo hw hc₀ hq hW ha0 ha1
    rw [hω] at h
    exact h

end Free

/-! ## 5b. The local weight ratio and the massless propagator -/

section Local

variable {L t : ℝ} {K : ℕ}

/-- **A positive weight is absorbed into the exponent**: `w e^{−u} = e^{−(u − log w)}`. DERIVED: `1` the
unit weight. -/
theorem heatSpec_absorb {κ : Type*} [Fintype κ] {w u : κ → ℝ} (hw : ∀ k, 0 < w k) :
    heatSpec w u = heatSpec (fun _ => (1 : ℝ)) (fun k => u k - Real.log (w k)) := by
  funext k
  simp only [heatSpec, one_mul]
  rw [show -(u k - Real.log (w k)) = Real.log (w k) + -u k by ring, Real.exp_add, Real.exp_log (hw k)]

/-- **The box heat count relative to any reference level `Z`**:
`heatCount(Y) ≤ π^d (1 + d Y/Z)^m heatCount(Z)`, `d = 2m`. DERIVED: `2` the even dimension; `π` the Jordan
ratio. -/
theorem box_weyl_Z (hK : 0 < K) (hL : 0 < L) (ht : 0 < t) {m : ℕ} (hm : 0 < m) {Y Z : ℝ} (hY : 0 ≤ Y)
    (hZ : 0 < Z) :
    (heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) Y : ℝ)
      ≤ (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * (Y / Z)) ^ m
        * heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) Z := by
  have hd : 0 < 2 * m := by omega
  have hdR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := Nat.cast_pos.2 hd
  have hZd : (0 : ℝ) < Z / ((2 * m : ℕ) : ℝ) := div_pos hZ hdR
  have hup := heatCount_le_pow hK hL ht (d := 2 * m) Y
  have hlow := heatCount_ge_pow (L := L) (t := t) hK hd Z
  have hr := n1_ratio hK hL ht hY hZd
  have hYZ : Y / (Z / ((2 * m : ℕ) : ℝ)) = ((2 * m : ℕ) : ℝ) * (Y / Z) := by
    rw [div_div_eq_mul_div]; ring
  rw [hYZ] at hr
  have hq0 : 0 ≤ 1 + ((2 * m : ℕ) : ℝ) * (Y / Z) := by
    have := mul_nonneg hdR.le (div_nonneg hY hZ.le); linarith
  calc (heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) Y : ℝ)
      ≤ (n1 L t K hK Y : ℝ) ^ (2 * m) := hup
    _ = ((n1 L t K hK Y : ℝ) ^ 2) ^ m := pow_mul _ 2 m
    _ ≤ (π ^ 2 * (1 + ((2 * m : ℕ) : ℝ) * (Y / Z))
          * (n1 L t K hK (Z / ((2 * m : ℕ) : ℝ)) : ℝ) ^ 2) ^ m :=
        pow_le_pow_left₀ (sq_nonneg _) hr m
    _ = (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * (Y / Z)) ^ m
          * (n1 L t K hK (Z / ((2 * m : ℕ) : ℝ)) : ℝ) ^ (2 * m) := by
        rw [mul_pow, mul_pow, ← pow_mul (n1 L t K hK (Z / ((2 * m : ℕ) : ℝ)) : ℝ) 2 m]
    _ ≤ (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * (Y / Z)) ^ m
          * heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) Z :=
        mul_le_mul_of_nonneg_left hlow (mul_nonneg (pow_nonneg (sq_nonneg π) m) (pow_nonneg hq0 m))

/-- **A top weight only removes modes from the heat count**: with `w ≤ w(k₀)`, the count of
`v = u − log w` is at most the count of `u`. DERIVED: no numeral. -/
theorem heatCount_absorb_le (hK : 0 < K) {d : ℕ} {w : (Fin d → Fin K) → ℝ} (hw : ∀ k, 0 < w k)
    (htop : ∀ k, w k ≤ w (fun _ => ⟨0, hK⟩)) (Y : ℝ) :
    heatCount (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) Y
      ≤ heatCount (boxU L t K (d := d)) (fun _ => ⟨0, hK⟩) Y := by
  unfold heatCount
  refine Finset.card_le_card fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  have := Real.log_le_log (hw k) (htop k)
  linarith

/-- **The local weight ratio keeps the polynomial growth**: if the weight ratio to the top grows at most
like `e^{κ(u − u₀)}`, `log(w(k₀)/w(k)) ≤ κ (u_k − u_{k₀})`, then `v = u − log w` meets `WeylGrowth` with
`c₀ = π^d` and `q = d(1 + κ)`, uniformly in the zoom. DERIVED: `1` the first e-fold; `2` the even
dimension; `π` the Jordan ratio. -/
theorem box_weyl_local (hK : 0 < K) (hL : 0 < L) (ht : 0 < t) {m : ℕ} (hm : 0 < m)
    {w : (Fin (2 * m) → Fin K) → ℝ} (hw : ∀ k, 0 < w k) (htop : ∀ k, w k ≤ w (fun _ => ⟨0, hK⟩))
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hloc : ∀ k, Real.log (w (fun _ => ⟨0, hK⟩) / w k)
      ≤ κ * (boxU L t K k - boxU L t K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K)))) :
    WeylGrowth (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) ((π ^ 2) ^ m)
      (((2 * m : ℕ) : ℝ) * (1 + κ)) m := by
  intro Y hY
  have hκ1 : 0 < 1 + κ := by linarith
  have hZ : (0 : ℝ) < 1 / (1 + κ) := div_pos one_pos hκ1
  have c1 := heatCount_absorb_le (L := L) (t := t) hK hw htop Y
  have c2 : heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) (1 / (1 + κ))
      ≤ heatCount (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) 1 := by
    unfold heatCount
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    have h := hloc k
    rw [Real.log_div (hw _).ne' (hw k).ne'] at h
    have h2 : (1 + κ) * (boxU L t K k - boxU L t K (fun _ => ⟨0, hK⟩)) ≤ (1 + κ) * (1 / (1 + κ)) :=
      mul_le_mul_of_nonneg_left hk hκ1.le
    rw [mul_one_div_cancel hκ1.ne'] at h2
    nlinarith
  have hw' := box_weyl_Z hK hL ht hm hY hZ
  have hYZ : ((2 * m : ℕ) : ℝ) * (Y / (1 / (1 + κ))) = ((2 * m : ℕ) : ℝ) * (1 + κ) * Y := by
    rw [div_div_eq_mul_div, div_one]; ring
  rw [hYZ] at hw'
  have hq0 : 0 ≤ 1 + ((2 * m : ℕ) : ℝ) * (1 + κ) * Y := by
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (2 * m)) hκ1.le) hY; linarith
  calc (heatCount (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) Y : ℝ)
      ≤ heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) Y := Nat.cast_le.mpr c1
    _ ≤ (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * (1 + κ) * Y) ^ m
          * heatCount (boxU L t K (d := 2 * m)) (fun _ => ⟨0, hK⟩) (1 / (1 + κ)) := hw'
    _ ≤ (π ^ 2) ^ m * (1 + ((2 * m : ℕ) : ℝ) * (1 + κ) * Y) ^ m
          * heatCount (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) 1 :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr c2)
          (mul_nonneg (pow_nonneg (sq_nonneg π) m) (pow_nonneg hq0 m))

/-- **The Rényi-½ factor at local ratio `κ`**: `π^d (1 − 2d(1 + κ) log a)^m (1 − a) ∑ (i + 1)^m a^i`.
DERIVED: `2` the even dimension and the ladder square; `π` the Jordan ratio; `1` the shift. -/
def renyiFactorL (m : ℕ) (κ a : ℝ) : ℝ :=
  (π ^ 2) ^ m * (1 - 2 * (((2 * m : ℕ) : ℝ) * (1 + κ)) * Real.log a) ^ m * (1 - a)
    * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i

/-- **H3 and the Rényi-½ bound at a local weight ratio**: a relabelled box spectrum `w_k e^{−2tμ_k}` with
`2t/L² ≥ τ`, the top weight at the lowest mode and `log(w(k₀)/w(k)) ≤ κ (u_k − u_{k₀})` has
`exp H ≤ A_κ² e ((1/τ + π²)/4)^m`, `levelCount_i ≤ π^d e (1 − 2d(1 + κ) log a)^m · exp H · (i + 1)^m` and
`R ≤ A_κ² e² exp H`. No global weight ratio enters. DERIVED: `1` the unit weights and the first e-fold;
`2` the even dimension; `π` the Jordan ratio. -/
theorem free_h3_local {κ' : Type*} [Fintype κ'] (hK : 0 < K) (hL : 0 < L) (ht : 0 < t) {m : ℕ}
    (hm : 0 < m) {τ κ : ℝ} (hτ : 0 < τ) (hτσ : τ ≤ 2 * t / L ^ 2) (hκ : 0 ≤ κ)
    {w : (Fin (2 * m) → Fin K) → ℝ} (hw : ∀ k, 0 < w k) (htop : ∀ k, w k ≤ w (fun _ => ⟨0, hK⟩))
    (hloc : ∀ k, Real.log (w (fun _ => ⟨0, hK⟩) / w k)
      ≤ κ * (boxU L t K k - boxU L t K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))))
    {lam : κ' → ℝ} (e : κ' ≃ (Fin (2 * m) → Fin K)) (hlam : lam = heatSpec w (boxU L t K) ∘ e)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    spDim lam ≤ renyiFactorL m κ a ^ 2 * Real.exp 1 * ((1 / τ + π ^ 2) / 4) ^ m
      ∧ (∀ i : ℕ, (levelCount lam a i : ℝ)
          ≤ (π ^ 2) ^ m * Real.exp 1 * (1 - 2 * (((2 * m : ℕ) : ℝ) * (1 + κ)) * Real.log a) ^ m
            * spDim lam * ((i : ℝ) + 1) ^ m)
      ∧ spRenyi lam ≤ renyiFactorL m κ a ^ 2 * Real.exp 1 ^ 2 * spDim lam := by
  subst hlam
  rw [spDim_comp_equiv, spRenyi_comp_equiv]
  have hv : ∀ k, (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩)
      ≤ (fun k => boxU L t K k - Real.log (w k)) k := fun k => by
    have h1 := boxU_min (L := L) (t := t) hK hL ht k
    have h2 := Real.log_le_log (hw k) (htop k)
    dsimp only
    linarith
  have hunit : ∀ k : Fin (2 * m) → Fin K, (1 : ℝ) ≤ (fun _ => (1 : ℝ)) k ∧ (fun _ => (1 : ℝ)) k ≤ 1 :=
    fun _ => ⟨le_rfl, le_rfl⟩
  have hW := box_weyl_local hK hL ht hm hw htop hκ hloc
  have hc₀ : (0 : ℝ) ≤ (π ^ 2) ^ m := pow_nonneg (sq_nonneg π) m
  have hq : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) * (1 + κ) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [heatSpec_absorb hw]
    have h1 := spDim_le_spRenyi
      (heatSpec_nonneg (u := fun k => boxU L t K k - Real.log (w k)) one_pos hunit)
      (heat_sum_pos (u := fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) one_pos hunit)
    have h2 := spRenyi_heat_le hv one_pos hunit hc₀ hq hW ha0 ha1
    have h3 : (heatCount (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) 1 : ℝ)
        ≤ ((1 / τ + π ^ 2) / 4) ^ m := by
      have c1 := heatCount_absorb_le (L := L) (t := t) hK hw htop 1
      have h4 := heatCount_one_box_le (L := L) (t := t) hK hL ht (m := m)
      have h5 : 1 / (2 * t / L ^ 2) ≤ 1 / τ := one_div_le_one_div_of_le hτ hτσ
      have h6 : 0 ≤ (1 / (2 * t / L ^ 2) + π ^ 2) / 4 :=
        div_nonneg (add_nonneg (div_nonneg zero_le_one (hτ.le.trans hτσ)) (sq_nonneg π)) (by norm_num)
      exact (Nat.cast_le.mpr c1).trans (h4.trans (pow_le_pow_left₀ h6 (by linarith) m))
    have hc : 0 ≤ renyiFactorL m κ a ^ 2 * (1 / 1 * Real.exp 1) :=
      mul_nonneg (sq_nonneg _) (by rw [div_one, one_mul]; exact (Real.exp_pos 1).le)
    calc spDim (heatSpec (fun _ => (1 : ℝ)) (fun k => boxU L t K k - Real.log (w k)))
        ≤ spRenyi (heatSpec (fun _ => (1 : ℝ)) (fun k => boxU L t K k - Real.log (w k))) := h1
      _ ≤ renyiFactorL m κ a ^ 2 * (1 / 1 * Real.exp 1)
            * heatCount (fun k => boxU L t K k - Real.log (w k)) (fun _ => ⟨0, hK⟩) 1 := h2
      _ ≤ renyiFactorL m κ a ^ 2 * (1 / 1 * Real.exp 1) * ((1 / τ + π ^ 2) / 4) ^ m :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = renyiFactorL m κ a ^ 2 * Real.exp 1 * ((1 / τ + π ^ 2) / 4) ^ m := by
          rw [div_one, one_mul]
  · rw [levelCount_comp_equiv, heatSpec_absorb hw]
    have h := levelCount_heat_weyl hv one_pos hunit hc₀ hq hW ha0 ha1 i
    rw [div_one, Real.log_one,
      show (1 : ℝ) + ((2 * m : ℕ) : ℝ) * (1 + κ) * (0 - 2 * Real.log a)
        = 1 - 2 * (((2 * m : ℕ) : ℝ) * (1 + κ)) * Real.log a by ring] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  · rw [heatSpec_absorb hw]
    have h := spRenyi_heat_le_spDim hv one_pos hunit hc₀ hq hW ha0 ha1
    rw [div_one, one_mul] at h
    exact h

/-- **The box Laplacian level** `μ_k = ∑_μ phat(k_μ + 1)²`. DERIVED: no numeral. -/
def boxMu (L : ℝ) (K : ℕ) {d : ℕ} (k : Fin d → Fin K) : ℝ := ∑ μ, lev1 L K (k μ)

/-- DERIVED: `2` the flow. -/
theorem boxU_eq {d : ℕ} (k : Fin d → Fin K) : boxU L t K k = 2 * t * boxMu L K k := rfl

/-- **The lowest level is at least `d (2/L)²`** (Jordan's lower bound at the lowest mode).
DERIVED: `2` the Jordan factor and the square. -/
theorem boxMu_low (hK : 0 < K) (hL : 0 < L) {d : ℕ} :
    (d : ℝ) * (2 / L) ^ 2 ≤ boxMu L K (fun _ : Fin d => (⟨0, hK⟩ : Fin K)) := by
  have h := ApertureGap.phat_ge hL (show 1 ≤ K by omega)
  rw [Nat.cast_one, mul_one] at h
  have h' : (2 / L) ^ 2 ≤ lev1 L K ⟨0, hK⟩ := pow_le_pow_left₀ (div_nonneg (by norm_num) hL.le) h 2
  unfold boxMu
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg d)

/-- DERIVED: `0` the lowest mode. -/
theorem boxMu_min (hK : 0 < K) (hL : 0 < L) {d : ℕ} (k : Fin d → Fin K) :
    boxMu L K (fun _ : Fin d => (⟨0, hK⟩ : Fin K)) ≤ boxMu L K k :=
  Finset.sum_le_sum fun μ _ => lev1_mono hK hL (k μ)

/-- DERIVED: `0` the sign; `2` as in `boxMu_low`. -/
theorem boxMu_pos (hK : 0 < K) (hL : 0 < L) {m : ℕ} (hm : 0 < m) (k : Fin (2 * m) → Fin K) :
    0 < boxMu L K k := by
  have hdR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  exact (lt_of_lt_of_le (mul_pos hdR (pow_pos (div_pos two_pos hL) 2)) (boxMu_low hK hL)).trans_le
    (boxMu_min hK hL k)

/-- **The massless propagator weight `1/μ` has a local ratio linear in the heat exponent**:
`log(w(k₀)/w(k)) = log(μ_k/μ_{k₀}) ≤ (u_k − u_{k₀})/(4dτ)` whenever `2t/L² ≥ τ`, uniformly in the zoom
(the lowest level is at least `4d/L²`, `boxMu_low`). DERIVED: `4 = 2²` the Jordan factor squared; `1` the
tangent `log x ≤ x − 1`. -/
theorem propagator_local (hK : 0 < K) (hL : 0 < L) (ht : 0 < t) {m : ℕ} (hm : 0 < m) {τ : ℝ}
    (hτ : 0 < τ) (hτσ : τ ≤ 2 * t / L ^ 2) (k : Fin (2 * m) → Fin K) :
    Real.log ((1 / boxMu L K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))) / (1 / boxMu L K k))
      ≤ 1 / (4 * ((2 * m : ℕ) : ℝ) * τ)
        * (boxU L t K k - boxU L t K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))) := by
  have hlow := boxMu_low hK hL (d := 2 * m)
  have hmin := boxMu_min hK hL k
  have hdiff : boxU L t K k - boxU L t K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))
      = 2 * t * (boxMu L K k - boxMu L K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))) := by
    rw [boxU_eq, boxU_eq]; ring
  have hμ0 := boxMu_pos hK hL hm (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))
  have hμk0 := boxMu_pos hK hL hm k
  rw [hdiff]
  set μ0 := boxMu L K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K)) with hμ0def
  set μk := boxMu L K k with hμkdef
  set d : ℝ := ((2 * m : ℕ) : ℝ) with hd
  have hdR : 0 < d := Nat.cast_pos.2 (by omega)
  have hd0 : d ≠ 0 := hdR.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hratio : (1 / μ0) / (1 / μk) = μk / μ0 := by
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_div_eq_mul_div, div_one]; ring)
  rw [hratio]
  have hl := Real.log_le_sub_one_of_pos (div_pos hμk0 hμ0)
  have hsub : μk / μ0 - 1 = (μk - μ0) / μ0 := by rw [sub_div, div_self hμ0.ne']
  have e : 1 / (4 * d * τ) * (2 * t) * (d * (2 / L) ^ 2) = 2 * t / L ^ 2 / τ := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hF1 : 1 ≤ 2 * t / L ^ 2 / τ := (one_le_div hτ).2 hτσ
  have hc0 : 0 ≤ 1 / (4 * d * τ) * (2 * t) :=
    mul_nonneg (div_pos one_pos (mul_pos (mul_pos four_pos hdR) hτ)).le (by linarith)
  have hF : 1 ≤ 1 / (4 * d * τ) * (2 * t) * μ0 :=
    calc 1 ≤ 2 * t / L ^ 2 / τ := hF1
      _ = 1 / (4 * d * τ) * (2 * t) * (d * (2 / L) ^ 2) := e.symm
      _ ≤ 1 / (4 * d * τ) * (2 * t) * μ0 := mul_le_mul_of_nonneg_left hlow hc0
  have hδ : 0 ≤ μk - μ0 := sub_nonneg.2 hmin
  calc Real.log (μk / μ0) ≤ μk / μ0 - 1 := hl
    _ = (μk - μ0) / μ0 := hsub
    _ ≤ 1 / (4 * d * τ) * (2 * t * (μk - μ0)) := by
        rw [div_le_iff₀ hμ0]
        calc μk - μ0 ≤ (μk - μ0) * (1 / (4 * d * τ) * (2 * t) * μ0) := le_mul_of_one_le_right hδ hF
          _ = 1 / (4 * d * τ) * (2 * t * (μk - μ0)) * μ0 := by ring

/-- **H3 for the massless free field, uniformly in the zoom**: the spectrum `e^{−2tμ_k}/μ_k` of the box
(the flowed massless propagator), relabelled, with `2t/L² ≥ τ`, meets `free_h3_local` at
`κ = 1/(4dτ)`. Every constant is fixed by `τ`, `d` and the ladder. DERIVED: `4` as in
`propagator_local`; `1` the propagator's numerator. -/
theorem free_h3_propagator {κ' : Type*} [Fintype κ'] (hK : 0 < K) (hL : 0 < L) (ht : 0 < t) {m : ℕ}
    (hm : 0 < m) {τ : ℝ} (hτ : 0 < τ) (hτσ : τ ≤ 2 * t / L ^ 2)
    {lam : κ' → ℝ} (e : κ' ≃ (Fin (2 * m) → Fin K))
    (hlam : lam = heatSpec (fun x => 1 / boxMu L K x) (boxU L t K) ∘ e) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    spDim lam ≤ renyiFactorL m (1 / (4 * ((2 * m : ℕ) : ℝ) * τ)) a ^ 2 * Real.exp 1
        * ((1 / τ + π ^ 2) / 4) ^ m
      ∧ (∀ i : ℕ, (levelCount lam a i : ℝ)
          ≤ (π ^ 2) ^ m * Real.exp 1
            * (1 - 2 * (((2 * m : ℕ) : ℝ) * (1 + 1 / (4 * ((2 * m : ℕ) : ℝ) * τ))) * Real.log a) ^ m
            * spDim lam * ((i : ℝ) + 1) ^ m)
      ∧ spRenyi lam ≤ renyiFactorL m (1 / (4 * ((2 * m : ℕ) : ℝ) * τ)) a ^ 2 * Real.exp 1 ^ 2
          * spDim lam := by
  have hdR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hκ : (0 : ℝ) ≤ 1 / (4 * ((2 * m : ℕ) : ℝ) * τ) :=
    (div_pos one_pos (mul_pos (mul_pos four_pos hdR) hτ)).le
  have hμ0 := boxMu_pos hK hL hm (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K))
  exact free_h3_local hK hL ht hm hτ hτσ hκ (w := fun x => 1 / boxMu L K x)
    (fun k => one_div_pos.2 (boxMu_pos hK hL hm k))
    (fun k => one_div_le_one_div_of_le hμ0 (boxMu_min hK hL k))
    (fun k => propagator_local hK hL ht hm hτ hτσ k) e hlam ha0 ha1

/-- **The global weight ratio of the propagator grows with the zoom**: on the box, the ratio of the top
weight `1/μ_{k₀}` to the weight at the corner mode `(K, …, K)` is at least `4K²/π²`.
DERIVED: `4 = 2²` the Jordan factor squared; `π` the upper bound of the lowest mode. -/
theorem propagator_global_ratio (hL : 0 < L) {m : ℕ} (hm : 0 < m) (hK : 0 < K) :
    4 * (K : ℝ) ^ 2 / π ^ 2
      ≤ (1 / boxMu L K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K)))
        / (1 / boxMu L K (fun _ : Fin (2 * m) => (⟨K - 1, by omega⟩ : Fin K))) := by
  have hk : K - 1 + 1 = K := by omega
  have hfar0 := ApertureGap.phat_ge hL (show K - 1 + 1 ≤ K by omega)
  rw [hk] at hfar0
  have hfar : (2 * (K : ℝ) / L) ^ 2 ≤ lev1 L K ⟨K - 1, by omega⟩ := by
    unfold lev1
    show (2 * (K : ℝ) / L) ^ 2 ≤ ApertureGap.phat L K (K - 1 + 1) ^ 2
    rw [hk]
    exact pow_le_pow_left₀ (div_nonneg (by positivity) hL.le) hfar0 2
  have h2 := ApertureGap.phat_le hL (show 1 ≤ K by omega)
  rw [Nat.cast_one, mul_one] at h2
  have h0hi : lev1 L K ⟨0, hK⟩ ≤ (π / L) ^ 2 :=
    pow_le_pow_left₀ (ApertureGap.phat_nonneg hL (show 1 ≤ K by omega)) h2 2
  have h1 := ApertureGap.phat_ge hL (show 1 ≤ K by omega)
  rw [Nat.cast_one, mul_one] at h1
  have h0lo : (2 / L) ^ 2 ≤ lev1 L K ⟨0, hK⟩ := pow_le_pow_left₀ (div_nonneg (by norm_num) hL.le) h1 2
  have ha0 : 0 < lev1 L K ⟨0, hK⟩ := lt_of_lt_of_le (pow_pos (div_pos two_pos hL) 2) h0lo
  have hdR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hs : ∀ j : Fin K, boxMu L K (fun _ : Fin (2 * m) => j) = ((2 * m : ℕ) : ℝ) * lev1 L K j := by
    intro j
    unfold boxMu
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs, hs]
  have hL0 : L ≠ 0 := hL.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hd0 : ((2 * m : ℕ) : ℝ) ≠ 0 := hdR.ne'
  have hfar0' : 0 < lev1 L K ⟨K - 1, by omega⟩ := ha0.trans_le ((lev1_mono hK hL ⟨K - 1, by omega⟩))
  have hr : (1 / (((2 * m : ℕ) : ℝ) * lev1 L K ⟨0, hK⟩))
      / (1 / (((2 * m : ℕ) : ℝ) * lev1 L K ⟨K - 1, by omega⟩))
      = lev1 L K ⟨K - 1, by omega⟩ / lev1 L K ⟨0, hK⟩ := by
    have := ha0.ne'
    have := hfar0'.ne'
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [hr]
  have e : 4 * (K : ℝ) ^ 2 / π ^ 2 = (2 * (K : ℝ) / L) ^ 2 / (π / L) ^ 2 := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [e]
  calc (2 * (K : ℝ) / L) ^ 2 / (π / L) ^ 2 ≤ lev1 L K ⟨K - 1, by omega⟩ / (π / L) ^ 2 :=
        div_le_div_of_nonneg_right hfar (sq_nonneg _)
    _ ≤ lev1 L K ⟨K - 1, by omega⟩ / lev1 L K ⟨0, hK⟩ :=
        div_le_div_of_nonneg_left hfar0'.le ha0 h0hi

/-- **No fixed global weight ratio covers the propagator**: for every `ω₀` there is a zoom `K` at which the
ratio of the largest to the smallest propagator weight on the box exceeds `ω₀`. So a hypothesis that bounds
the weight ratio over all modes by one `ω₀` (as `free_h3` does) fails for the massless free field; the
local ratio of `propagator_local` does not. DERIVED: `1` the shift of the ceiling; `4` as in
`propagator_global_ratio`. -/
theorem propagator_global_unbounded (hL : 0 < L) {m : ℕ} (hm : 0 < m) (ω₀ : ℝ) :
    ∃ (K : ℕ) (hK : 0 < K), ω₀
      < (1 / boxMu L K (fun _ : Fin (2 * m) => (⟨0, hK⟩ : Fin K)))
        / (1 / boxMu L K (fun _ : Fin (2 * m) => (⟨K - 1, by omega⟩ : Fin K))) := by
  set K : ℕ := ⌈π ^ 2 * |ω₀|⌉₊ + 1 with hKdef
  have hK : 0 < K := by omega
  refine ⟨K, hK, lt_of_lt_of_le ?_ (propagator_global_ratio hL hm hK)⟩
  have hKr : π ^ 2 * |ω₀| < (K : ℝ) := by
    have := Nat.le_ceil (π ^ 2 * |ω₀|)
    rw [hKdef]; push_cast; linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rw [lt_div_iff₀ (pow_pos Real.pi_pos 2)]
  have h1 : ω₀ * π ^ 2 ≤ |ω₀| * π ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  nlinarith

end Local

/-! ### The H3 clause of `ApertureCountAt` -/

section Clause

open MassGap.ContinuumFlow MassGap.MultiScaleAll

variable {N : ℕ} [NeZero N]

/-- **The spectral input**: at every aperture `s ∈ (0, b]`, eventually in the step, the spectrum of every
channel's screen is a relabelled heat spectrum `w e^{−2tμ}` of the Dirichlet box in `d = 4`, with flow time
relative to the aperture `2t/L² ≥ τ`, positive weights largest at the lowest mode, and a local weight
ratio `log(w(k₀)/w(k)) ≤ κ (u_k − u_{k₀})` (`u = 2tμ`). No ratio over all modes is fixed. DERIVED:
`4 = 2 · 2` the spacetime dimension; `2` the flow; `0` the signs and the lowest mode. -/
def FreeScreenSpectrum (Wf : ℝ → ConfFlow N) (b τ κ : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, ∀ j : MIx, ∃ (K : ℕ) (hK : 0 < K) (L t : ℝ)
    (w : (Fin (2 * 2) → Fin K) → ℝ) (e : (Fin 4 → Fin (apL N k s)) ≃ (Fin (2 * 2) → Fin K)),
    0 < L ∧ 0 < t ∧ τ ≤ 2 * t / L ^ 2 ∧ (∀ x, 0 < w x) ∧ (∀ x, w x ≤ w (fun _ => ⟨0, hK⟩))
      ∧ (∀ x, Real.log (w (fun _ => ⟨0, hK⟩) / w x)
          ≤ κ * (boxU L t K x - boxU L t K (fun _ : Fin (2 * 2) => (⟨0, hK⟩ : Fin K))))
      ∧ apEig Wf k s j = heatSpec w (boxU L t K) ∘ e

/-- **The H3 clause from the spectral input**: `FreeScreenSpectrum Wf b τ κ` gives exactly the count
clause of `ApertureCountAt`, whose ladder is existential; `free_h3_local` holds at every `a ∈ (0, 1)`, and
the witness is `a = e^{−1/2}` (one e-fold per rung), with `r = 2`, `c = π⁴ e (1 + 4(1 + κ))²` and
`D = A_κ² e ((1/τ + π²)/4)²`. The massless free field (`w = 1/μ`) meets the input at `κ = 1/(16τ)`
(`propagator_local`). DERIVED: `2` the exponent `r = d/2`; `1/2` the ladder; `0` the signs. -/
theorem h3_of_freeScreen {Wf : ℝ → ConfFlow N} {b τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 ≤ κ)
    (h : FreeScreenSpectrum Wf b τ κ) :
    ∃ (D c a : ℝ) (r : ℕ), 0 < a ∧ a < 1 ∧ 0 ≤ c ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop,
      ∀ j : MIx, apDim Wf k s j ≤ D
        ∧ ∀ i : ℕ, (levelCount (apEig Wf k s j) a i : ℝ) ≤ c * apDim Wf k s j * ((i : ℝ) + 1) ^ r := by
  set a : ℝ := Real.exp (-(1 / 2)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  set c : ℝ := (π ^ 2) ^ 2 * Real.exp 1
    * (1 - 2 * (((2 * 2 : ℕ) : ℝ) * (1 + κ)) * Real.log a) ^ 2 with hc
  refine ⟨renyiFactorL 2 κ a ^ 2 * Real.exp 1 * ((1 / τ + π ^ 2) / 4) ^ 2, c, a, 2, ha0, ha1, ?_,
    fun s hs hsb => ?_⟩
  · rw [hc]
    exact mul_nonneg (mul_nonneg (pow_nonneg (sq_nonneg π) 2) (Real.exp_pos 1).le) (sq_nonneg _)
  · filter_upwards [h s hs hsb] with k hk j
    obtain ⟨K, hK, L, t, w, e, hL, ht, hτσ, hw, htop, hloc, heq⟩ := hk j
    obtain ⟨hD, hlev, -⟩ :=
      free_h3_local hK hL ht (m := 2) (by norm_num) hτ hτσ hκ hw htop hloc e heq ha0 ha1
    rw [apDim_eq]
    refine ⟨hD, fun i => ?_⟩
    rw [hc]
    calc _ ≤ _ := hlev i
      _ = _ := by ring

end Clause

/-! ## 6. The load-bearing test -/

section Load

/-- **Shannon alone does not control the Rényi-½ count, on positive spectra**: for every `B` a spectrum with
every weight positive, `exp H ≤ e²` and `R ≥ B` (`ApertureCount.spRenyi_unbounded_at_bounded_spDim`, the
same spectrum). DERIVED: `2` the Shannon bound; `0` the signs; `1` the first mode. -/
theorem spRenyi_unbounded_pos (B : ℝ) :
    ∃ (m : ℕ) (w : Fin (m + 1) → ℝ), (∀ i, 0 < w i) ∧ spDim w ≤ Real.exp 2 ∧ B ≤ spRenyi w := by
  obtain ⟨m0, hm0⟩ := exists_nat_gt (4 * B ^ 2)
  set m : ℕ := m0 + 3 with hm
  have hmR : (m : ℝ) = m0 + 3 := by rw [hm]; norm_num
  have hm0' : (0 : ℝ) < m := by rw [hmR]; positivity
  have he : Real.exp 1 < m := by
    have h := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
    rw [hmR]
    norm_num at h
    linarith
  set L := Real.log m with hL
  have hL1 : 1 < L := by rw [hL, Real.lt_log_iff_exp_lt hm0']; exact he
  set ε := 1 / L with hε
  have hε0 : 0 < ε := by rw [hε]; exact div_pos one_pos (by linarith)
  have hε1 : ε < 1 := by rw [hε, div_lt_one (by linarith)]; exact hL1
  set w : Fin (m + 1) → ℝ := fun i => if i = 0 then 1 - ε else ε / m with hw
  have hw0 : ∀ i, 0 < w i := fun i => by
    simp only [hw]
    split_ifs
    · linarith
    · exact div_pos hε0 hm0'
  have hwsucc : ∀ i : Fin m, w i.succ = ε / m := fun i => by simp [hw]
  have hw00 : w 0 = 1 - ε := by simp [hw]
  have hsum : ∑ i, w i = 1 := by
    rw [Fin.sum_univ_succ, hw00]
    simp only [hwsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hm0'.ne']
    ring
  refine ⟨m, w, hw0, ?_, ?_⟩
  · unfold spDim
    rw [hsum, Real.exp_le_exp, Fin.sum_univ_succ]
    simp only [div_one, hw00, hwsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : Real.negMulLog (1 - ε) ≤ ε := by
      have := Real.negMulLog_le_one_sub_self (show 0 ≤ 1 - ε by linarith)
      linarith
    have hmε : (m : ℝ) * (ε / m) = ε := mul_div_cancel₀ _ hm0'.ne'
    have h2 : (m : ℝ) * Real.negMulLog (ε / m) = Real.negMulLog ε + ε * L := by
      simp only [Real.negMulLog]
      rw [Real.log_div hε0.ne' hm0'.ne', ← hL]
      calc (m : ℝ) * (-(ε / m) * (Real.log ε - L)) = -((m : ℝ) * (ε / m)) * (Real.log ε - L) := by ring
        _ = -ε * Real.log ε + ε * L := by rw [hmε]; ring
    have h3 : Real.negMulLog ε ≤ 1 - ε := Real.negMulLog_le_one_sub_self hε0.le
    rw [h2]
    have hεL : ε * L = 1 := by rw [hε]; exact one_div_mul_cancel (ne_of_gt (by linarith))
    linarith
  · unfold spRenyi
    rw [hsum, Fin.sum_univ_succ]
    simp only [div_one, hw00, hwsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hq0 : 0 ≤ (m : ℝ) * Real.sqrt (ε / m) := by positivity
    have hge : (m : ℝ) * Real.sqrt (ε / m) ≤ Real.sqrt (1 - ε) + m * Real.sqrt (ε / m) :=
      le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have hsqr : ((m : ℝ) * Real.sqrt (ε / m)) ^ 2 = m * ε := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hε0.le hm0'.le), sq, mul_assoc, mul_div_cancel₀ _ hm0'.ne']
    have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0'
    have hLle : L ≤ 2 * Real.sqrt m := by
      have hlog := Real.log_le_sub_one_of_pos hsm0
      rw [Real.log_sqrt hm0'.le, ← hL] at hlog
      linarith
    have hmε : (m : ℝ) * ε = m / L := by rw [hε]; ring
    have hhalf : Real.sqrt m / 2 ≤ m * ε := by
      rw [hmε, le_div_iff₀ (by linarith)]
      calc Real.sqrt m / 2 * L ≤ Real.sqrt m / 2 * (2 * Real.sqrt m) :=
            mul_le_mul_of_nonneg_left hLle (by positivity)
        _ = m := by rw [show Real.sqrt m / 2 * (2 * Real.sqrt m) = Real.sqrt m * Real.sqrt m by ring,
            Real.mul_self_sqrt hm0'.le]
    have hB : B ≤ Real.sqrt m / 2 := by
      rcases le_or_gt B 0 with hB0 | hB0
      · linarith
      · have : 2 * B ≤ Real.sqrt m := by
          refine Real.le_sqrt_of_sq_le ?_
          have : (m0 : ℝ) ≤ m := by rw [hmR]; linarith
          nlinarith
        linarith
    calc B ≤ Real.sqrt m / 2 := hB
      _ ≤ m * ε := hhalf
      _ = ((m : ℝ) * Real.sqrt (ε / m)) ^ 2 := hsqr.symm
      _ ≤ (Real.sqrt (1 - ε) + m * Real.sqrt (ε / m)) ^ 2 := pow_le_pow_left₀ hq0 hge 2

/-- **The polynomial growth of the heat count is load-bearing**: for every `c₀, q ≥ 0` and `m` there is a
positive spectrum `p`, written as the heat spectrum `u = −log p` with unit weights, that fails
`WeylGrowth u k₀ c₀ q m` at every top mode `k₀`. Were it to hold, `spRenyi_heat_le_spDim` at the ladder
`e^{−1/2}` would give `R ≤ Φ exp H ≤ Φ e²` with `Φ` fixed by `c₀, q, m`, and `R` is unbounded
(`spRenyi_unbounded_pos`). DERIVED: `1` the unit weights; `1/2` the ladder; `2` the Shannon bound. -/
theorem weyl_load_bearing {c₀ q : ℝ} {m : ℕ} (hc₀ : 0 ≤ c₀) (hq : 0 ≤ q) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ), (∀ i, 0 < p i) ∧
      ∀ k₀, (∀ k, -Real.log (p k₀) ≤ -Real.log (p k)) →
        ¬ WeylGrowth (fun k => -Real.log (p k)) k₀ c₀ q m := by
  set a : ℝ := Real.exp (-(1 / 2)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  set Φ : ℝ := (c₀ * (1 - 2 * q * Real.log a) ^ m * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ m * a ^ i) ^ 2
    * (1 / 1 * Real.exp 1) ^ 2 with hΦ
  have hΦ0 : 0 ≤ Φ := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  obtain ⟨n, p, hp, hD, hR⟩ := spRenyi_unbounded_pos (Φ * Real.exp 2 + 1)
  refine ⟨n, p, hp, fun k₀ hk₀ hW => ?_⟩
  have hspec : heatSpec (fun _ => (1 : ℝ)) (fun k => -Real.log (p k)) = p := by
    funext k
    simp only [heatSpec, neg_neg, one_mul]
    exact Real.exp_log (hp k)
  have hb := spRenyi_heat_le_spDim (w := fun _ => (1 : ℝ)) (wlo := 1) (whi := 1) hk₀ one_pos
    (fun _ => ⟨le_rfl, le_rfl⟩) hc₀ hq hW ha0 ha1
  rw [hspec] at hb
  have hb' : spRenyi p ≤ Φ * spDim p := hb
  have h2 : Φ * spDim p ≤ Φ * Real.exp 2 := mul_le_mul_of_nonneg_left hD hΦ0
  linarith

end Load

end MassGap.FreeLevels

end

#print axioms MassGap.FreeLevels.spDim_comp_equiv
#print axioms MassGap.FreeLevels.spRenyi_comp_equiv
#print axioms MassGap.FreeLevels.levelCount_comp_equiv
#print axioms MassGap.FreeLevels.spDim_ge_of_le
#print axioms MassGap.FreeLevels.negMulLog_le_renyi
#print axioms MassGap.FreeLevels.spDim_le_spRenyi
#print axioms MassGap.FreeLevels.heatSpec_nonneg
#print axioms MassGap.FreeLevels.heatSpec_le
#print axioms MassGap.FreeLevels.heat_sum_pos
#print axioms MassGap.FreeLevels.heatCount_pos
#print axioms MassGap.FreeLevels.heat_sum_ge
#print axioms MassGap.FreeLevels.spDim_heat_ge
#print axioms MassGap.FreeLevels.heatCount_one_le
#print axioms MassGap.FreeLevels.levelCount_heat_le
#print axioms MassGap.FreeLevels.levelCount_heat_weyl
#print axioms MassGap.FreeLevels.sum_sqrt_le_rungs
#print axioms MassGap.FreeLevels.rungCount_heat_le
#print axioms MassGap.FreeLevels.spRenyi_heat_le
#print axioms MassGap.FreeLevels.spRenyi_heat_le_spDim
#print axioms MassGap.FreeLevels.phat_eigen
#print axioms MassGap.FreeLevels.phat_dirichlet
#print axioms MassGap.FreeLevels.phat_mono
#print axioms MassGap.FreeLevels.lev1_mono
#print axioms MassGap.FreeLevels.gap1_nonneg
#print axioms MassGap.FreeLevels.gap1_zero
#print axioms MassGap.FreeLevels.gap1_ge
#print axioms MassGap.FreeLevels.gap1_le
#print axioms MassGap.FreeLevels.card_le_of_succ_le
#print axioms MassGap.FreeLevels.card_ge_of_succ_le
#print axioms MassGap.FreeLevels.n1_le_K
#print axioms MassGap.FreeLevels.n1_one_le
#print axioms MassGap.FreeLevels.n1_sq_le
#print axioms MassGap.FreeLevels.n1_ge
#print axioms MassGap.FreeLevels.n1_ratio
#print axioms MassGap.FreeLevels.boxU_sub
#print axioms MassGap.FreeLevels.boxU_min
#print axioms MassGap.FreeLevels.heatCount_le_pow
#print axioms MassGap.FreeLevels.heatCount_ge_pow
#print axioms MassGap.FreeLevels.box_weyl
#print axioms MassGap.FreeLevels.heatCount_one_box_le
#print axioms MassGap.FreeLevels.free_h3
#print axioms MassGap.FreeLevels.heatSpec_absorb
#print axioms MassGap.FreeLevels.box_weyl_Z
#print axioms MassGap.FreeLevels.heatCount_absorb_le
#print axioms MassGap.FreeLevels.box_weyl_local
#print axioms MassGap.FreeLevels.free_h3_local
#print axioms MassGap.FreeLevels.boxU_eq
#print axioms MassGap.FreeLevels.boxMu_low
#print axioms MassGap.FreeLevels.boxMu_min
#print axioms MassGap.FreeLevels.boxMu_pos
#print axioms MassGap.FreeLevels.propagator_local
#print axioms MassGap.FreeLevels.free_h3_propagator
#print axioms MassGap.FreeLevels.propagator_global_ratio
#print axioms MassGap.FreeLevels.propagator_global_unbounded
#print axioms MassGap.FreeLevels.h3_of_freeScreen
#print axioms MassGap.FreeLevels.spRenyi_unbounded_pos
#print axioms MassGap.FreeLevels.weyl_load_bearing
