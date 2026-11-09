import Mathlib
import MassGap.DLRLimit

noncomputable section

/-!
# MassGap.BoxDobrushin — a Dobrushin influence bound for the single-link kernel

The dynamic route (`PotRateFast.pot_cluster_rate_fast`) clusters the sharp box at `2.6·10⁻⁶` per level,
and `PotRateFast.dyn_route_ceiling` shows that route cannot do better. This module takes the static
route: an influence (Dobrushin) estimate on the single-link conditional law.

1. **Propagation** (`influence_decay`, `influence_eq_zero`). A non-negative discrepancy vector `d`
   on a finite index set with `d ≤ C d` off a boundary set, `C ≥ 0` with row sums `≤ α ≤ 1` and
   range one in a level function `ψ`, satisfies `d l ≤ D α^{ψ l}`. With the recursion everywhere and
   `α < 1`, `d = 0`.
2. **Bridge to the DLR consumer** (`kernel_near_const_of_influence`, `dlr_eq_of_influence`). If the
   kernels' readings of an observable are bounded by `K` times the discrepancies on a support of
   bounded size, and the support sits at unbounded level, the kernels are uniformly near a constant,
   which is the hypothesis of `DLRLimit.dlr_eq_at_of_kernel_near_const`.
3. **The influence of one tilt** (`tilt_core`, `tilt_mean_le`, `qfun_mul_le`, `pair_tv_le`). Tilting a
   probability measure by `w ∈ [A, A s²]` moves the mean of every `0 ≤ φ ≤ 1` by at most
   `(s − 1)/(s + 1)` (that is `tanh(δ/4)` at oscillation `δ = 2 log s`), for any base measure. A tilt
   `exp(h_W + h_V)` with `|h_W| ≤ a`, `|h_V| ≤ b` moves it by at most `q(eᵃ) + q(eᵇ)`.
4. **The numbers** (`wilsonPair_le`, `potPair_le`, `rowSum_wide`, `oscillation_fails_sharp`). At Lean
   `β ≤ 1/40` (`β_std ≤ 1/20`) the Wilson pair term is `≤ 53/1053`; a potential pair term of mixed
   weight `m ≤ 1/16` is `≤ (35/32) m`; eighteen Wilson partners and potential mixes summing to
   `≤ 1/16` give row sum `≤ 39/40`. At `β = 1/20` the oscillation bound alone gives `> 1`.

## Scope

The per-pair inputs to section 4 are the oscillations of the single-link log-weight: a Wilson
plaquette `β Re tr(U S)` with both orientations moves by at most `4β` in absolute value when one link
of its staple changes, and a potential term by at most `2 · mix`. The derivation of those pointwise
bounds from `LocalPotential.wtV` and the identification of the heat-bath conditional law with the
tilted measure of section 3 are not formalised here; nor is the coupling half of Dobrushin's
comparison theorem, the `hread`/`hrec` inputs of section 2 for the Wilson specification.
-/

namespace MassGap.BoxDobrushin

open MeasureTheory Filter Topology

/-! ## 1. Influence propagation -/

section Propagation

variable {ι : Type*} [Fintype ι]

/-- **Influence propagation, truncated at `k` rounds**: `d l ≤ D α^{min k (ψ l)}`.

DERIVED: `0` is the sign of `C`, `d`, `α` and the level at which the recursion is not asked; `1` is
the bound on `α` and the level range of one influence step. -/
theorem influence_decay_min {C : ι → ι → ℝ} {α D : ℝ} (hC0 : ∀ l l', 0 ≤ C l l')
    (hrow : ∀ l, ∑ l', C l l' ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (ψ : ι → ℕ) (hloc : ∀ l l', C l l' ≠ 0 → ψ l ≤ ψ l' + 1)
    {d : ι → ℝ} (hd0 : ∀ l, 0 ≤ d l) (hdD : ∀ l, d l ≤ D)
    (hrec : ∀ l, 0 < ψ l → d l ≤ ∑ l', C l l' * d l') :
    ∀ k : ℕ, ∀ l, d l ≤ D * α ^ min k (ψ l) := by
  intro k
  induction k with
  | zero => intro l; simpa using hdD l
  | succ k ih =>
    intro l
    rcases Nat.eq_zero_or_pos (ψ l) with h0 | hpos
    · simpa [h0] using hdD l
    · obtain ⟨p, hp⟩ : ∃ p, ψ l = p + 1 := ⟨ψ l - 1, by omega⟩
      have hD : 0 ≤ D := (hd0 l).trans (hdD l)
      have hterm : ∀ l', C l l' * d l' ≤ C l l' * (D * α ^ min k p) := by
        intro l'
        by_cases hc : C l l' = 0
        · simp [hc]
        · apply mul_le_mul_of_nonneg_left _ (hC0 l l')
          refine (ih l').trans ?_
          apply mul_le_mul_of_nonneg_left _ hD
          apply pow_le_pow_of_le_one hα0 hα1
          have := hloc l l' hc
          omega
      calc d l ≤ ∑ l', C l l' * d l' := hrec l hpos
        _ ≤ ∑ l', C l l' * (D * α ^ min k p) := Finset.sum_le_sum fun l' _ => hterm l'
        _ = (∑ l', C l l') * (D * α ^ min k p) := by rw [Finset.sum_mul]
        _ ≤ α * (D * α ^ min k p) :=
            mul_le_mul_of_nonneg_right (hrow l) (mul_nonneg hD (pow_nonneg hα0 _))
        _ = D * α ^ min (k + 1) (ψ l) := by
            rw [hp, show min (k + 1) (p + 1) = min k p + 1 by omega, pow_succ]; ring

#print axioms influence_decay_min

/-- **Influence propagation**: `d l ≤ D α^{ψ l}`.

DERIVED: `0` and `1` as in `influence_decay_min`. -/
theorem influence_decay {C : ι → ι → ℝ} {α D : ℝ} (hC0 : ∀ l l', 0 ≤ C l l')
    (hrow : ∀ l, ∑ l', C l l' ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (ψ : ι → ℕ) (hloc : ∀ l l', C l l' ≠ 0 → ψ l ≤ ψ l' + 1)
    {d : ι → ℝ} (hd0 : ∀ l, 0 ≤ d l) (hdD : ∀ l, d l ≤ D)
    (hrec : ∀ l, 0 < ψ l → d l ≤ ∑ l', C l l' * d l') :
    ∀ l, d l ≤ D * α ^ ψ l := fun l => by
  simpa using influence_decay_min hC0 hrow hα0 hα1 ψ hloc hd0 hdD hrec (ψ l) l

#print axioms influence_decay

/-- **Dobrushin uniqueness on a finite index set**: with the recursion at every index and row sums
`≤ α < 1`, a bounded non-negative discrepancy vanishes.

DERIVED: `0` is the sign and the limit of `αⁿ`; `1` is the strict bound on `α`. -/
theorem influence_eq_zero {C : ι → ι → ℝ} {α D : ℝ} (hC0 : ∀ l l', 0 ≤ C l l')
    (hrow : ∀ l, ∑ l', C l l' ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {d : ι → ℝ} (hd0 : ∀ l, 0 ≤ d l) (hdD : ∀ l, d l ≤ D)
    (hrec : ∀ l, d l ≤ ∑ l', C l l' * d l') :
    ∀ l, d l = 0 := by
  intro l
  have hb : ∀ n : ℕ, d l ≤ D * α ^ n := fun n =>
    influence_decay hC0 hrow hα0 hα1.le (fun _ => n) (fun _ _ _ => by omega) hd0 hdD
      (fun l' _ => hrec l') l
  have ht : Tendsto (fun n : ℕ => D * α ^ n) atTop (𝓝 (D * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul D
  have hle : d l ≤ D * 0 := ge_of_tendsto' ht hb
  simp at hle
  exact le_antisymm hle (hd0 l)

#print axioms influence_eq_zero

end Propagation

/-! ## 2. From influence decay to the near-constant kernel, and DLR uniqueness -/

section Bridge

/-- **Decaying influence makes the kernels near-constant.** For each region `k`, a finite index type
`ι k`, an influence matrix `C k` of row sums `≤ α < 1` and range one in the level `ψ k`, and for every
pair of boundary conditions `x, y` a discrepancy vector `d k x y` obeying the recursion at positive
level; if the reading `g k` of an observable differs at `x, y` by at most `K` times the discrepancy
summed over a support `S k` of at most `L` indices, and the support sits at arbitrarily high level,
then for every `ε > 0` some `g k` is within `ε` of a constant.

DERIVED: `0` is the sign of `C`, `d`, `D`, `K`, `α`, `ε` and the excluded level; `1` is the strict
bound on `α`, the level range of one step and the `+ 1` keeping the divisor positive. -/
theorem kernel_near_const_of_influence {X κ : Type*} (ι : κ → Type*) [∀ k, Fintype (ι k)]
    (g : κ → X → ℝ) (C : ∀ k, ι k → ι k → ℝ) (ψ : ∀ k, ι k → ℕ) (d : ∀ k, X → X → ι k → ℝ)
    (S : ∀ k, Finset (ι k)) {K D α : ℝ} {L : ℕ}
    (hC0 : ∀ k l l', 0 ≤ C k l l') (hrow : ∀ k l, ∑ l', C k l l' ≤ α) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hloc : ∀ k l l', C k l l' ≠ 0 → ψ k l ≤ ψ k l' + 1)
    (hd0 : ∀ k x y l, 0 ≤ d k x y l) (hD0 : 0 ≤ D) (hdD : ∀ k x y l, d k x y l ≤ D)
    (hrec : ∀ k x y l, 0 < ψ k l → d k x y l ≤ ∑ l', C k l l' * d k x y l')
    (hK : 0 ≤ K) (hread : ∀ k x y, |g k x - g k y| ≤ K * ∑ l ∈ S k, d k x y l)
    (hcard : ∀ k, (S k).card ≤ L) (hfar : ∀ m : ℕ, ∃ k, ∀ l ∈ S k, m ≤ ψ k l) :
    ∀ ε : ℝ, 0 < ε → ∃ (k : κ) (c : ℝ), ∀ x, |g k x - c| ≤ ε := by
  intro ε hε
  set B : ℝ := K * L * D with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (B + 1) by positivity) hα1
  obtain ⟨k, hk⟩ := hfar m
  have hαm : 0 ≤ α ^ m := pow_nonneg hα0 m
  have hsmall : B * α ^ m ≤ ε := by
    have h1 : (B + 1) * α ^ m < ε := by
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < B + 1)).1 hm
      linarith
    nlinarith
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨k, 0, fun x => (IsEmpty.false x).elim⟩
  · obtain ⟨x0⟩ := hX
    refine ⟨k, g k x0, fun x => ?_⟩
    have hdec : ∀ l ∈ S k, d k x x0 l ≤ D * α ^ m := by
      intro l hl
      refine (influence_decay (hC0 k) (hrow k) hα0 hα1.le (ψ k) (hloc k) (hd0 k x x0)
        (hdD k x x0) (hrec k x x0) l).trans ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα0 hα1.le (hk l hl)) hD0
    have hsum : ∑ l ∈ S k, d k x x0 l ≤ L * (D * α ^ m) := by
      calc ∑ l ∈ S k, d k x x0 l ≤ ∑ _l ∈ S k, D * α ^ m := Finset.sum_le_sum hdec
        _ = (S k).card * (D * α ^ m) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ L * (D * α ^ m) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) (mul_nonneg hD0 hαm)
    calc |g k x - g k x0| ≤ K * ∑ l ∈ S k, d k x x0 l := hread k x x0
      _ ≤ K * (L * (D * α ^ m)) := mul_le_mul_of_nonneg_left hsum hK
      _ = B * α ^ m := by rw [hB]; ring
      _ ≤ ε := hsmall

#print axioms kernel_near_const_of_influence

/-- **DLR uniqueness at an observable from decaying influence**: the hypotheses of
`kernel_near_const_of_influence` with `g k = γ k f` give `ν f = ν' f` for any two DLR states
(`DLRLimit.dlr_eq_at_of_kernel_near_const`).

DERIVED: `0`, `1` as in `kernel_near_const_of_influence`. -/
theorem dlr_eq_of_influence {X : Type*} [TopologicalSpace X] [CompactSpace X] {κ : Type*}
    {γ : κ → C(X, ℝ) → C(X, ℝ)} {f : C(X, ℝ)} (ι : κ → Type*) [∀ k, Fintype (ι k)]
    (C : ∀ k, ι k → ι k → ℝ) (ψ : ∀ k, ι k → ℕ) (d : ∀ k, X → X → ι k → ℝ)
    (S : ∀ k, Finset (ι k)) {K D α : ℝ} {L : ℕ}
    (hC0 : ∀ k l l', 0 ≤ C k l l') (hrow : ∀ k l, ∑ l', C k l l' ≤ α) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hloc : ∀ k l l', C k l l' ≠ 0 → ψ k l ≤ ψ k l' + 1)
    (hd0 : ∀ k x y l, 0 ≤ d k x y l) (hD0 : 0 ≤ D) (hdD : ∀ k x y l, d k x y l ≤ D)
    (hrec : ∀ k x y l, 0 < ψ k l → d k x y l ≤ ∑ l', C k l l' * d k x y l')
    (hK : 0 ≤ K) (hread : ∀ k x y, |γ k f x - γ k f y| ≤ K * ∑ l ∈ S k, d k x y l)
    (hcard : ∀ k, (S k).card ≤ L) (hfar : ∀ m : ℕ, ∃ k, ∀ l ∈ S k, m ≤ ψ k l)
    {ν ν' : DLRLimit.State X} (h : DLRLimit.IsDLR γ ν) (h' : DLRLimit.IsDLR γ ν') :
    ν f = ν' f :=
  DLRLimit.dlr_eq_at_of_kernel_near_const
    (kernel_near_const_of_influence ι (fun k x => γ k f x) C ψ d S hC0 hrow hα0 hα1 hloc hd0 hD0
      hdD hrec hK hread hcard hfar) h h'

#print axioms dlr_eq_of_influence

end Bridge

/-! ## 3. The influence of one tilt -/

section Tilt

/-- **The two-point extremal inequality.** If `0 ≤ a ≤ A s² q` and `b ≥ A (1 − q)` with `q ∈ [0, 1]`,
then `a/(a + b) − q ≤ (s − 1)/(s + 1)`. Equality is at `q = 1/(1 + s)`: the identity
`(q + r)(1 − q) − s² q (1 − q − r) = (s − 1)(s q − 1 + q)²/(s + 1)`, `r = (s − 1)/(s + 1)`.

DERIVED: `0` is the sign; `1` is the total mass and the unit of `s`; `2` is the square of `s`. -/
theorem tilt_core {a b q A s : ℝ} (hA : 0 < A) (hs : 1 ≤ s) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : 0 ≤ a) (hahi : a ≤ A * s ^ 2 * q) (hblo : A * (1 - q) ≤ b) (hab : 0 < a + b) :
    a / (a + b) - q ≤ (s - 1) / (s + 1) := by
  have hs1 : 0 < s + 1 := by linarith
  have hs1' : s + 1 ≠ 0 := hs1.ne'
  have hr0 : 0 ≤ (s - 1) / (s + 1) := div_nonneg (by linarith) hs1.le
  have hid : (q + (s - 1) / (s + 1)) * (1 - q) - s ^ 2 * q * (1 - q - (s - 1) / (s + 1))
      = (s - 1) * (s * q - 1 + q) ^ 2 / (s + 1) := by
    field_simp
    ring
  have hpoly : s ^ 2 * q * (1 - q - (s - 1) / (s + 1)) ≤ (q + (s - 1) / (s + 1)) * (1 - q) := by
    have : 0 ≤ (s - 1) * (s * q - 1 + q) ^ 2 / (s + 1) :=
      div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hs1.le
    linarith
  have hb0 : 0 ≤ b := le_trans (mul_nonneg hA.le (by linarith)) hblo
  rw [sub_le_iff_le_add, div_le_iff₀ hab]
  set r := (s - 1) / (s + 1) with hr
  rcases le_or_gt (1 - q - r) 0 with hneg | hpos
  · nlinarith [mul_nonneg ha0 (show 0 ≤ -(1 - q - r) by linarith), mul_nonneg (by linarith : 0 ≤ q + r) hb0]
  · have h1 : a * (1 - q - r) ≤ A * s ^ 2 * q * (1 - q - r) := mul_le_mul_of_nonneg_right hahi hpos.le
    have h2 : A * (s ^ 2 * q * (1 - q - r)) ≤ A * ((q + r) * (1 - q)) :=
      mul_le_mul_of_nonneg_left hpoly hA.le
    have h3 : (q + r) * (A * (1 - q)) ≤ (q + r) * b := mul_le_mul_of_nonneg_left hblo (by linarith)
    nlinarith

#print axioms tilt_core

/-- **A bounded tilt moves every `[0, 1]`-valued mean by at most `(s − 1)/(s + 1)`**: for a
probability measure `μ`, a weight `A ≤ w ≤ A s²` and `0 ≤ φ ≤ 1`,
`|∫ φ w / ∫ w − ∫ φ| ≤ (s − 1)/(s + 1)`. No property of `μ` beyond total mass one is used, so the
bound holds uniformly over every frozen background.

DERIVED: `0`, `1`, `2` as in `tilt_core`. -/
theorem tilt_mean_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {w φ : Ω → ℝ} {A s : ℝ} (hA : 0 < A) (hs : 1 ≤ s)
    (hw : Integrable w μ) (hφ : Integrable φ μ) (hφw : Integrable (fun x => φ x * w x) μ)
    (hlo : ∀ x, A ≤ w x) (hhi : ∀ x, w x ≤ A * s ^ 2) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    |(∫ x, φ x * w x ∂μ) / (∫ x, w x ∂μ) - ∫ x, φ x ∂μ| ≤ (s - 1) / (s + 1) := by
  set p := ∫ x, φ x ∂μ with hp
  set X := ∫ x, φ x * w x ∂μ with hX
  set Z := ∫ x, w x ∂μ with hZ
  have hcA : ∫ _x, A ∂μ = A := by simp
  have hp0 : 0 ≤ p := integral_nonneg hφ0
  have hp1 : p ≤ 1 := by
    have := integral_mono hφ (integrable_const (1 : ℝ)) hφ1
    simpa using this
  have hX0 : 0 ≤ X := integral_nonneg fun x => mul_nonneg (hφ0 x) (hA.le.trans (hlo x))
  have hXhi : X ≤ A * s ^ 2 * p := by
    have h := integral_mono hφw (hφ.mul_const (A * s ^ 2))
      (fun x => mul_le_mul_of_nonneg_left (hhi x) (hφ0 x))
    rw [integral_mul_const] at h
    calc X ≤ (∫ x, φ x ∂μ) * (A * s ^ 2) := h
      _ = A * s ^ 2 * p := by rw [hp]; ring
  have hXlo : A * p ≤ X := by
    have h := integral_mono (hφ.mul_const A) hφw
      (fun x => mul_le_mul_of_nonneg_left (hlo x) (hφ0 x))
    rw [integral_mul_const] at h
    calc A * p = (∫ x, φ x ∂μ) * A := by rw [hp]; ring
      _ ≤ X := h
  have hY : ∫ x, (w x - φ x * w x) ∂μ = Z - X := integral_sub hw hφw
  have hYlo : A * (1 - p) ≤ Z - X := by
    have h : ∫ x, (A - φ x * A) ∂μ ≤ ∫ x, (w x - φ x * w x) ∂μ :=
      integral_mono ((integrable_const A).sub (hφ.mul_const A)) (hw.sub hφw)
      (fun x => by
        have := mul_le_mul_of_nonneg_left (hlo x) (by linarith [hφ1 x] : 0 ≤ 1 - φ x)
        show A - φ x * A ≤ w x - φ x * w x
        nlinarith)
    rw [integral_sub (integrable_const A) (hφ.mul_const A), integral_mul_const, hcA, hY] at h
    calc A * (1 - p) = A - (∫ x, φ x ∂μ) * A := by rw [hp]; ring
      _ ≤ Z - X := h
  have hYhi : Z - X ≤ A * s ^ 2 * (1 - p) := by
    have hcB : ∫ _x, A * s ^ 2 ∂μ = A * s ^ 2 := by simp
    have h : ∫ x, (w x - φ x * w x) ∂μ ≤ ∫ x, (A * s ^ 2 - φ x * (A * s ^ 2)) ∂μ :=
      integral_mono (hw.sub hφw) ((integrable_const (A * s ^ 2)).sub (hφ.mul_const (A * s ^ 2)))
      (fun x => by
        have := mul_le_mul_of_nonneg_left (hhi x) (by linarith [hφ1 x] : 0 ≤ 1 - φ x)
        show w x - φ x * w x ≤ A * s ^ 2 - φ x * (A * s ^ 2)
        nlinarith)
    rw [integral_sub (integrable_const _) (hφ.mul_const _), hcB, integral_mul_const, hY] at h
    calc Z - X ≤ A * s ^ 2 - (∫ x, φ x ∂μ) * (A * s ^ 2) := h
      _ = A * s ^ 2 * (1 - p) := by rw [hp]; ring
  have hZpos : 0 < Z := by
    have h := integral_mono (integrable_const A) hw hlo
    rw [hcA] at h
    linarith
  have hYge : 0 ≤ Z - X := le_trans (mul_nonneg hA.le (by linarith)) hYlo
  have hup : X / (X + (Z - X)) - p ≤ (s - 1) / (s + 1) :=
    tilt_core hA hs hp0 hp1 hX0 hXhi hYlo (by linarith)
  have hdn : (Z - X) / ((Z - X) + X) - (1 - p) ≤ (s - 1) / (s + 1) :=
    tilt_core hA hs (by linarith) (by linarith) hYge hYhi (by linarith) (by linarith)
  have e1 : X + (Z - X) = Z := by ring
  have e2 : (Z - X) / ((Z - X) + X) = 1 - X / Z := by
    rw [show (Z - X) + X = Z by ring]
    field_simp
  rw [e1] at hup
  rw [e2] at hdn
  rw [abs_le]
  constructor <;> linarith

#print axioms tilt_mean_le

/-- `q s = (s − 1)/(s + 1)`, the influence of a tilt of ratio range `s²` (`tanh` of a quarter of the
oscillation `2 log s`).

DERIVED: `1` is the unit of `s`. -/
def qfun (s : ℝ) : ℝ := (s - 1) / (s + 1)

/-- **`q` is subadditive under products**: `q(s t) ≤ q s + q t` for `s, t ≥ 1`, from
`(st − 1)(s + 1)(t + 1) ≤ 2(st − 1)(st + 1)`, whose gap is `(st − 1)(s − 1)(t − 1) ≥ 0`.

DERIVED: `1` is the unit; `0` the sign. -/
theorem qfun_mul_le {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) : qfun (s * t) ≤ qfun s + qfun t := by
  unfold qfun
  have hst : 1 ≤ s * t := by nlinarith
  rw [div_add_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hst) (sub_nonneg.2 hs)) (sub_nonneg.2 ht)]

#print axioms qfun_mul_le

/-- **The influence of a two-part log-tilt**: for a probability measure `μ`, `|h_W| ≤ a`,
`|h_V| ≤ b` and `0 ≤ φ ≤ 1`, the tilt `exp(h_W + h_V)` moves the mean of `φ` by at most
`q(eᵃ) + q(eᵇ)` (`tilt_mean_le` at `A = e^{−(a+b)}`, `s = e^{a+b}`; `qfun_mul_le`).

DERIVED: `0` is the sign of `a`, `b`; `2` is the square in `A s²`. -/
theorem pair_tv_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {hW hV φ : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haW : ∀ x, |hW x| ≤ a) (hbV : ∀ x, |hV x| ≤ b)
    (hw : Integrable (fun x => Real.exp (hW x + hV x)) μ) (hφ : Integrable φ μ)
    (hφw : Integrable (fun x => φ x * Real.exp (hW x + hV x)) μ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    |(∫ x, φ x * Real.exp (hW x + hV x) ∂μ) / (∫ x, Real.exp (hW x + hV x) ∂μ) - ∫ x, φ x ∂μ|
      ≤ qfun (Real.exp a) + qfun (Real.exp b) := by
  have hs : 1 ≤ Real.exp (a + b) := Real.one_le_exp (by linarith)
  have hlo : ∀ x, Real.exp (-(a + b)) ≤ Real.exp (hW x + hV x) := fun x => by
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (haW x)).1
    have h2 := (abs_le.1 (hbV x)).1
    linarith
  have hhi : ∀ x, Real.exp (hW x + hV x) ≤ Real.exp (-(a + b)) * Real.exp (a + b) ^ 2 := fun x => by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (haW x)).2
    have h2 := (abs_le.1 (hbV x)).2
    linarith
  have h := tilt_mean_le μ (Real.exp_pos _) hs hw hφ hφw hlo hhi hφ0 hφ1
  refine h.trans ?_
  have := qfun_mul_le (Real.one_le_exp ha) (Real.one_le_exp hb)
  rw [← Real.exp_add] at this
  exact this

#print axioms pair_tv_le

end Tilt

/-! ## 4. The row sum at the box -/

section Numbers

/-- `e^{1/10} ≤ 1106/1000` (`Real.exp_bound'` at three terms: `1.105 + 1/4500`).

DERIVED: `1/10 = 4 · (1/40)`, the Wilson half-oscillation at the wide coupling; `1106/1000` is the
three-term bound rounded up; `3` the number of terms. -/
theorem exp_tenth_le : Real.exp (1 / 10) ≤ 1106 / 1000 := by
  have h := Real.exp_bound' (x := 1 / 10) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

#print axioms exp_tenth_le

/-- **The Wilson pair influence at `β ≤ 1/40`**: `q(e^{4β}) ≤ 53/1053`. A change of one staple link
moves `β Re tr(U S)` (both orientations) by at most `4β` in absolute value.

DERIVED: `4 = 2 · 2`, `|Re tr(U Q)| ≤ 2|Q|` with `|Q| ≤ 2`; `1/40` the coupling bound;
`53/1053 = (1106/1000 − 1)/(1106/1000 + 1)`. -/
theorem wilsonPair_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) :
    qfun (Real.exp (4 * β)) ≤ 53 / 1053 := by
  unfold qfun
  have h1 : Real.exp (4 * β) ≤ 1106 / 1000 :=
    (Real.exp_le_exp.2 (by linarith)).trans exp_tenth_le
  have h0 : 0 < Real.exp (4 * β) := Real.exp_pos _
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

#print axioms wilsonPair_le

/-- **A potential pair influence**: `q(e^{2m}) ≤ (35/32) m` for `0 ≤ m ≤ 1/16`, from
`e^x ≤ 1 + x + (3/4)x²` (`Real.exp_bound'` at two terms) and `q t ≤ (t − 1)/2`.

DERIVED: `2` the absolute bound `|ΔV| ≤ 2 mix`; `1/16` the local norm; `35/32 = 1 + (3/2)(1/16)`;
`3/4 = 3/(2 · 2)` the remainder of the two-term bound. -/
theorem potPair_le {m : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ 1 / 16) :
    qfun (Real.exp (2 * m)) ≤ 35 / 32 * m := by
  unfold qfun
  have h := Real.exp_bound' (x := 2 * m) (by linarith) (by linarith) (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h1 : 1 ≤ Real.exp (2 * m) := Real.one_le_exp (by linarith)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

#print axioms potPair_le

/-- **The Dobrushin row sum of the wide box is at most `39/40`**: at Lean `β ≤ 1/40`, eighteen
Wilson partners (`PairCount.sum_n2_le`: `36/2`) at `q(e^{4β})` each, plus potential partners at
`q(e^{2 mix})` each with mixes summing to at most the local norm `1/16`
(`LocalPotential.sum_mix_le`).

DERIVED: `18 = 36/2`; `4`, `2`, `1/40`, `1/16` as in `wilsonPair_le`, `potPair_le`;
`39/40 ≥ 18 · 53/1053 + (35/32)/16 = 0.97434…`. -/
theorem rowSum_wide {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) {ι : Type*} (W T : Finset ι)
    (hW : W.card ≤ 18) (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hm : ∑ i ∈ T, m i ≤ 1 / 16) :
    ∑ _i ∈ W, qfun (Real.exp (4 * β)) + ∑ i ∈ T, qfun (Real.exp (2 * m i)) ≤ 39 / 40 := by
  have hq : 0 ≤ qfun (Real.exp (4 * β)) := by
    unfold qfun
    have := Real.one_le_exp (show 0 ≤ 4 * β by linarith)
    exact div_nonneg (by linarith) (by linarith)
  have hW' : ∑ _i ∈ W, qfun (Real.exp (4 * β)) ≤ 18 * (53 / 1053) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (W.card : ℝ) ≤ 18 := by exact_mod_cast hW
    nlinarith [wilsonPair_le hβ0 hβ]
  have hT : ∑ i ∈ T, qfun (Real.exp (2 * m i)) ≤ 35 / 32 * (1 / 16) := by
    have hle : ∀ i ∈ T, m i ≤ 1 / 16 := fun i hi =>
      le_trans (Finset.single_le_sum (fun j _ => hm0 j) hi) hm
    calc ∑ i ∈ T, qfun (Real.exp (2 * m i)) ≤ ∑ i ∈ T, 35 / 32 * m i :=
          Finset.sum_le_sum fun i hi => potPair_le (hm0 i) (hle i hi)
      _ = 35 / 32 * ∑ i ∈ T, m i := by rw [Finset.mul_sum]
      _ ≤ 35 / 32 * (1 / 16) := by linarith
  linarith

#print axioms rowSum_wide

/-- **The oscillation bound cannot certify the sharp box**: at `β = 1/20`,
`18 · q(e^{4β}) > 1`, since `e^{1/5} ≥ 6/5` gives `q ≥ 1/11`.

DERIVED: `1/5 = 4 · (1/20)`; `6/5 = 1 + 1/5`; `18 = 36/2`; `1/11 = (1/5)/(11/5)`. -/
theorem oscillation_fails_sharp : 1 < 18 * qfun (Real.exp (4 * (1 / 20))) := by
  unfold qfun
  have h : 6 / 5 ≤ Real.exp (4 * (1 / 20)) := by
    have := Real.add_one_le_exp (4 * (1 / 20 : ℝ))
    norm_num at this ⊢
    linarith
  have hpos : 0 < Real.exp (4 * (1 / 20)) + 1 := by positivity
  rw [mul_div_assoc', lt_div_iff₀ hpos]
  linarith

#print axioms oscillation_fails_sharp

end Numbers

end MassGap.BoxDobrushin
