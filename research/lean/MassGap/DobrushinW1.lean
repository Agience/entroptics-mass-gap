import Mathlib
import MassGap.DobrushinUnbounded

noncomputable section

/-!
# MassGap.DobrushinW1 — Dobrushin's theorem in Kantorovich (W1) form for real spins

`DobrushinUnbounded` proves Dobrushin's theorem with a total-variation influence matrix: changing the
spin at `k` moves the conditional mean at `l` of every `[0, 1]`-valued test function by at most
`C l k`. For real spins whose conditional mean responds linearly to a neighbour, that matrix grows with
the spin range. Dobrushin's original condition for unbounded spins is the Kantorovich one: changing
the spin at `k` by `Δ` moves the conditional mean at `l` of every `1`-Lipschitz test function by at
most `C l k · |Δ|`. This module proves the theorem in that form, for spins in a compact interval
`[-|R|, |R|]`. No bound depends on `R` except the vanishing tail of a sweep, so the interval is only
the carrier of a finite box.

1. **Lipschitz vectors and the W1 influence** (`LipLe`, `W1Infl`): `v` bounds the single-site
   Lipschitz constants of `f`; `C` bounds the W1 influence of `k` on `l`.
2. **The contraction** (`lip_stepS`, `lip_sweepS`, `lip_sweep_fullS`, `lip_iterS`): the kernel at `l`
   maps a Lipschitz vector `v` to `oscStep C l v` (`v_k + C l k v_l` off `l`, `0` at `l`), so a full
   sweep contracts `Σ v` by the row-sum bound `α`.
3. **Mixing and uniqueness** (`sweep_mixingW`, `sweep_to_stateW`, `state_unique_lipW`, `lipSub`,
   `state_unique_W1`): the sweep converges to every invariant state at rate `αⁿ`; two invariant states
   agree on every observable (Lipschitz observables form a point-separating subalgebra).
4. **The conditional covariance** (`var_shift`, `var_le`, `condCov_le`): at one site, Lipschitz
   functions of constants `a`, `b` have conditional covariance `≤ a b` times the conditional variance
   of the spin.
5. **Covariance decay** (`cov_stepW`, `cov_runW`, `cov_le_weightedW`, `cov_spatialW`): for an
   invariant state, `|σ(f g) − σ f σ g| ≤ M V_g θ/(θ − α) · Σ_k θ^{ψ k} v_f(k)`, where `M` bounds the
   second moment of the spin at the sites read by `g`.

## Scope

Specifications, invariant states and influence matrices are hypotheses here; nothing derives them
from a lattice measure. The moment enters only as `σ(x_l²) ≤ M` at the sites where `g` moves.
-/

namespace MassGap.DobrushinW1

open MeasureTheory Filter Topology
open MassGap.HeatBath (exists_abs_le)
open MassGap.BoxDobrushinCoupling (oscStep)
open MassGap.BoxDobrushinSpatial (oscCost cost_le reach level level_loc level_of_mem level_far rep
  oscStep_nonneg)
open MassGap.DobrushinGeneral (cmul csmul cadd csub caddc csubc ex ex_mk ex_sub ex_const_mul
  abs_ex_le)
open MassGap.DobrushinUnbounded (Spec Invariant Tsp sweepS continuous_sweepS sweepCS state_iterS
  sweepS_rep continuous_iterS ex_P)

variable {R : ℝ}

/-! ## 1. Lipschitz vectors and the W1 influence -/

section Lip

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **`v` bounds the single-site Lipschitz constants of `f`**: `v ≥ 0`, and changing the spin at `k`
from `W k` to `x` moves `f` by at most `v k · |x − W k|`.

DERIVED: `0` the sign. -/
def LipLe (f : (Lk → Tsp R) → ℝ) (v : Lk → ℝ) : Prop :=
  (∀ k, 0 ≤ v k) ∧ ∀ (W : Lk → Tsp R) (k : Lk) (x : Tsp R),
    |f (Function.update W k x) - f W| ≤ v k * |(x : ℝ) - (W k : ℝ)|

/-- **The Kantorovich (W1) influence matrix of a specification**: changing the spin at `k ≠ l` from
`W k` to `x` moves the `P l`-mean of every continuous `1`-Lipschitz function of the spin at `l` by at
most `C l k · |x − W k|`. By Kantorovich–Rubinstein duality the supremum over these test functions is
the W1 distance of the two single-site conditional laws.

DERIVED: `1` the Lipschitz constant of the test functions. -/
def W1Infl (S : Spec (Tsp R) Lk) (C : Lk → Lk → ℝ) : Prop :=
  ∀ l k, l ≠ k → ∀ (W : Lk → Tsp R) (x : Tsp R) (φ : Tsp R → ℝ), Continuous φ →
    (∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)|) →
    |S.P l (fun V => φ (V l)) (Function.update W k x) - S.P l (fun V => φ (V l)) W|
      ≤ C l k * |(x : ℝ) - (W k : ℝ)|

/-- **Two spins of the interval are at most its diameter apart.**

DERIVED: `2 |R|` the diameter of `[-|R|, |R|]`. -/
theorem abs_sub_le_diam (x y : Tsp R) : |(x : ℝ) - (y : ℝ)| ≤ 2 * |R| := by
  have hx := x.2
  have hy := y.2
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

#print axioms abs_sub_le_diam

/-- **The fibre form of a Lipschitz vector**: on the fibre of `l` at `W`, `f` is `v l`-Lipschitz.

DERIVED: no numeral. -/
theorem LipLe.fibre {f : (Lk → Tsp R) → ℝ} {v : Lk → ℝ} (hv : LipLe f v) (W : Lk → Tsp R)
    (l : Lk) (a b : Tsp R) :
    |f (Function.update W l a) - f (Function.update W l b)| ≤ v l * |(a : ℝ) - (b : ℝ)| := by
  have h := hv.2 (Function.update W l b) l a
  rwa [Function.update_idem, Function.update_self] at h

#print axioms LipLe.fibre

/-- **The kernel step on Lipschitz vectors (Dobrushin's comparison, W1 form).** If `v` is a
Lipschitz vector of a continuous `f` and `C ≥ 0` a W1 influence matrix of `S`, then `oscStep C l v`
is a Lipschitz vector of `P l f`. Changing the spin at `k ≠ l` moves `f` on the fibre by
`≤ v k |Δ|`, and moves the `P l`-mean of the fibre function (a `v l`-Lipschitz function of the spin
at `l`) by `≤ C l k v l |Δ|`.

DERIVED: `0` the oscillation at `l` and the case `v l = 0`. -/
theorem lip_stepS {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {f : (Lk → Tsp R) → ℝ} (hf : Continuous f) {v : Lk → ℝ}
    (hv : LipLe f v) (l : Lk) : LipLe (S.P l f) (oscStep C l v) := by
  refine ⟨oscStep_nonneg hC0 hv.1 l, fun W k x => ?_⟩
  unfold oscStep
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, S.upd, sub_self, abs_zero, zero_mul]
  rw [if_neg hkl]
  have hlk : l ≠ k := Ne.symm hkl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Tsp R → ℝ, ∀ g, ψ g = f (Function.update W l g) := ⟨_, fun _ => rfl⟩
  have hu : Continuous (fun g : Tsp R => Function.update W l g) :=
    continuous_const.update l continuous_id
  have hψc : Continuous ψ := by
    have : ψ = fun g => f (Function.update W l g) := funext hψ
    rw [this]; exact hf.comp hu
  have hF : Continuous (fun V : Lk → Tsp R => ψ (V l)) := hψc.comp (continuous_apply l)
  have hd0 : 0 ≤ |(x : ℝ) - (W k : ℝ)| := abs_nonneg _
  have s1 : |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) (Function.update W k x)|
      ≤ v k * |(x : ℝ) - (W k : ℝ)| := by
    refine S.sub_le l hf hF _ fun g => ?_
    show |f (Function.update (Function.update W k x) l g)
      - ψ (Function.update (Function.update W k x) l g l)| ≤ _
    rw [Function.update_self, hψ, Function.update_comm hkl x g W]
    have h := hv.2 (Function.update W l g) k x
    rwa [Function.update_of_ne hkl] at h
  have s0 : S.P l (fun V => ψ (V l)) W = S.P l f W :=
    S.fibre_eq l hF hf W fun g => by
      show ψ (Function.update W l g l) = f (Function.update W l g)
      rw [Function.update_self, hψ]
  have hψL : ∀ a b, |ψ a - ψ b| ≤ v l * |(a : ℝ) - (b : ℝ)| := fun a b => by
    rw [hψ, hψ]; exact hv.fibre W l a b
  have hvl : 0 ≤ v l := hv.1 l
  have s2 : |S.P l (fun V => ψ (V l)) (Function.update W k x) - S.P l (fun V => ψ (V l)) W|
      ≤ C l k * v l * |(x : ℝ) - (W k : ℝ)| := by
    rcases hvl.eq_or_lt with h0 | hpos
    · have hconst : ∀ g, ψ g = ψ (W l) := fun g => by
        have h := hψL g (W l)
        rw [← h0, zero_mul] at h
        exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
      have e : (fun V : Lk → Tsp R => ψ (V l)) = fun _ => ψ (W l) := funext fun V => hconst _
      rw [e, S.const, S.const, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (hC0 l k) hvl) hd0
    · obtain ⟨φ, hφ⟩ : ∃ φ : Tsp R → ℝ, ∀ g, φ g = ψ g / v l := ⟨_, fun _ => rfl⟩
      have hφc : Continuous φ := by
        have : φ = fun g => ψ g / v l := funext hφ
        rw [this]; exact hψc.div_const _
      have hφL : ∀ a b : Tsp R, |φ a - φ b| ≤ |(a : ℝ) - (b : ℝ)| := fun a b => by
        rw [hφ, hφ, ← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, mul_comm]
        exact hψL a b
      have e : (fun V : Lk → Tsp R => ψ (V l)) = fun V => 0 + v l * φ (V l) := by
        have hne : v l ≠ 0 := hpos.ne'
        funext V; rw [hφ]; field_simp <;> ring
      have hφF : Continuous (fun V : Lk → Tsp R => φ (V l)) := hφc.comp (continuous_apply l)
      rw [e, S.affine l hφF, S.affine l hφF]
      have h := hC l k hlk W x φ hφc hφL
      rw [show 0 + v l * S.P l (fun V => φ (V l)) (Function.update W k x)
          - (0 + v l * S.P l (fun V => φ (V l)) W)
          = v l * (S.P l (fun V => φ (V l)) (Function.update W k x)
            - S.P l (fun V => φ (V l)) W) by ring, abs_mul, abs_of_nonneg hvl]
      calc v l * |S.P l (fun V => φ (V l)) (Function.update W k x) - S.P l (fun V => φ (V l)) W|
          ≤ v l * (C l k * |(x : ℝ) - (W k : ℝ)|) := mul_le_mul_of_nonneg_left h hvl
        _ = C l k * v l * |(x : ℝ) - (W k : ℝ)| := by ring
  rw [← s0]
  calc |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) W|
      ≤ |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) (Function.update W k x)|
        + |S.P l (fun V => ψ (V l)) (Function.update W k x) - S.P l (fun V => ψ (V l)) W| :=
        abs_sub_le _ _ _
    _ ≤ v k * |(x : ℝ) - (W k : ℝ)| + C l k * v l * |(x : ℝ) - (W k : ℝ)| := add_le_add s1 s2
    _ = (v k + C l k * v l) * |(x : ℝ) - (W k : ℝ)| := by ring

#print axioms lip_stepS

/-- **Lipschitz constants add up**: changing the spins of a finite set `s` one at a time moves `F`
by at most `Σ_{k ∈ s} u k |W' k − W k|`.

DERIVED: no numeral. -/
theorem abs_sub_le_lip_finset {F : (Lk → Tsp R) → ℝ} {u : Lk → ℝ} (hu : LipLe F u)
    (W W' : Lk → Tsp R) (s : Finset Lk) :
    |F W - F (fun k => if k ∈ s then W' k else W k)|
      ≤ ∑ k ∈ s, u k * |(W' k : ℝ) - (W k : ℝ)| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have e : (fun k => if k ∈ insert a s then W' k else W k)
        = Function.update (fun k => if k ∈ s then W' k else W k) a (W' a) := by
      funext k
      by_cases hk : k = a
      · subst hk; simp
      · simp [Function.update, hk]
    rw [e, Finset.sum_insert ha]
    have h2 := hu.2 (fun k => if k ∈ s then W' k else W k) a (W' a)
    simp only [if_neg ha] at h2
    calc |F W - F (Function.update (fun k => if k ∈ s then W' k else W k) a (W' a))|
        ≤ |F W - F (fun k => if k ∈ s then W' k else W k)|
          + |F (fun k => if k ∈ s then W' k else W k)
            - F (Function.update (fun k => if k ∈ s then W' k else W k) a (W' a))| :=
          abs_sub_le _ _ _
      _ ≤ ∑ k ∈ s, u k * |(W' k : ℝ) - (W k : ℝ)| + u a * |(W' a : ℝ) - (W a : ℝ)| := by
          rw [abs_sub_comm] at h2; linarith
      _ = u a * |(W' a : ℝ) - (W a : ℝ)| + ∑ k ∈ s, u k * |(W' k : ℝ) - (W k : ℝ)| := by ring

#print axioms abs_sub_le_lip_finset

/-- **The total Lipschitz constant bounds the range**: `|F W − F W'| ≤ Σ u · 2|R|`.

DERIVED: `2 |R|` the diameter of the spin interval. -/
theorem abs_sub_le_sum_lip {F : (Lk → Tsp R) → ℝ} {u : Lk → ℝ} (hu : LipLe F u)
    (W W' : Lk → Tsp R) : |F W - F W'| ≤ (∑ k, u k) * (2 * |R|) := by
  have h := abs_sub_le_lip_finset hu W W' Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  refine h.trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (abs_sub_le_diam _ _) (hu.1 k)

#print axioms abs_sub_le_sum_lip

/-- **The Lipschitz budget along a sweep** (as `DobrushinUnbounded.osc_sweepS`, W1 form).

DERIVED: `0` the sign; `1` the bound on `α`. -/
theorem lip_sweepS {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) (v : Lk → ℝ) :
    ∀ (L : List Lk) (T : Finset Lk) (f : (Lk → Tsp R) → ℝ) (u : Lk → ℝ), Continuous f →
      LipLe f u → (∀ k ∉ T, v k ≤ u k) → ∑ k, u k ≤ α * ∑ k ∈ T, v k + ∑ k ∈ Tᶜ, v k →
      ∃ u' : Lk → ℝ, LipLe (sweepS S L f) u' ∧ (∀ k ∉ T ∪ L.toFinset, v k ≤ u' k) ∧
        ∑ k, u' k ≤ α * ∑ k ∈ T ∪ L.toFinset, v k + ∑ k ∈ (T ∪ L.toFinset)ᶜ, v k
  | [], T, f, u, _, hu, hS, hsum => ⟨u, hu, by simpa using hS, by simpa using hsum⟩
  | l :: L, T, f, u, hf, hu, hS, hsum => by
    have hu0 : ∀ k, 0 ≤ u k := hu.1
    set u1 := oscStep C l u with hu1
    have hosc : LipLe (S.P l f) u1 := lip_stepS hC hC0 hf hu l
    have hS1 : ∀ k ∉ insert l T, v k ≤ u1 k := fun k hk => by
      have hkl : k ≠ l := fun h => hk (h ▸ Finset.mem_insert_self l T)
      have hkS : k ∉ T := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hu1, oscStep, if_neg hkl]
      have := mul_nonneg (hC0 l k) (hu0 l)
      linarith [hS k hkS]
    have htot : ∑ k, u1 k ≤ ∑ k, u k - (1 - α) * u l := by
      have e : ∑ k, u1 k = ∑ k ∈ Finset.univ.erase l, (u k + C l k * u l) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        simp only [hu1, oscStep, ↓reduceIte, zero_add]
        exact Finset.sum_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]
      have e2 : ∑ k ∈ Finset.univ.erase l, (u k + C l k * u l)
          = (∑ k, u k - u l) + (∑ k ∈ Finset.univ.erase l, C l k) * u l := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          ← Finset.add_sum_erase _ u (Finset.mem_univ l)]
        ring
      have hCe : ∑ k ∈ Finset.univ.erase l, C l k ≤ α := by
        refine le_trans ?_ (hrow l)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        linarith [hC0 l l]
      rw [e, e2]
      nlinarith [hu0 l]
    have hsum1 : ∑ k, u1 k ≤ α * ∑ k ∈ insert l T, v k + ∑ k ∈ (insert l T)ᶜ, v k := by
      by_cases hlS : l ∈ T
      · rw [Finset.insert_eq_of_mem hlS]
        nlinarith [hu0 l]
      · rw [Finset.sum_insert hlS, Finset.compl_insert]
        have hc : ∑ k ∈ Tᶜ, v k = v l + ∑ k ∈ Tᶜ.erase l, v k :=
          (Finset.add_sum_erase _ _ (Finset.mem_compl.mpr hlS)).symm
        rw [hc] at hsum
        have := hS l hlS
        nlinarith
    obtain ⟨u', h1, h2, h3⟩ := lip_sweepS hC hC0 hrow hα1 v L (insert l T) (S.P l f) u1
      (S.cont l hf) hosc hS1 hsum1
    have eS : insert l T ∪ L.toFinset = T ∪ (l :: L).toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    rw [eS] at h2 h3
    exact ⟨u', h1, h2, h3⟩

#print axioms lip_sweepS

/-- **A full sweep contracts the total Lipschitz constant by `α`.**

DERIVED: `1` the bound on `α`. -/
theorem lip_sweep_fullS {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) {L : List Lk}
    (hL : ∀ l, l ∈ L) {f : (Lk → Tsp R) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : LipLe f v) :
    ∃ u' : Lk → ℝ, LipLe (sweepS S L f) u' ∧ ∑ k, u' k ≤ α * ∑ k, v k := by
  obtain ⟨u', h1, -, h3⟩ := lip_sweepS hC hC0 hrow hα1 v L ∅ f v hf hv
    (fun _ _ => le_rfl) (by simp)
  have hU : (∅ : Finset Lk) ∪ L.toFinset = Finset.univ := by
    ext l; simp [hL l]
  rw [hU, Finset.compl_univ, Finset.sum_empty, add_zero] at h3
  exact ⟨u', h1, h3⟩

#print axioms lip_sweep_fullS

/-- **`n` full sweeps leave total Lipschitz constant `≤ αⁿ Σ v`.**

DERIVED: `0` the sign of `α`; `1` the bound on `α`. -/
theorem lip_iterS {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {L : List Lk} (hL : ∀ l, l ∈ L) :
    ∀ (n : ℕ) {f : (Lk → Tsp R) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipLe f v →
      ∃ u : Lk → ℝ, LipLe ((sweepS S L)^[n] f) u ∧ ∑ k, u k ≤ α ^ n * ∑ k, v k
  | 0, _, _, v, hv => ⟨v, hv, by simp⟩
  | n + 1, f, hf, v, hv => by
    obtain ⟨u1, h1, h1s⟩ := lip_sweep_fullS hC hC0 hrow hα1 hL hf hv
    obtain ⟨u, hu, hus⟩ := lip_iterS hC hC0 hrow hα0 hα1 hL n (continuous_sweepS S L hf) h1
    refine ⟨u, by rwa [Function.iterate_succ_apply], hus.trans ?_⟩
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left h1s (pow_nonneg hα0 n)
    linarith

#print axioms lip_iterS

/-- **Mixing of the sweep, W1 form**: after `n` full sweeps a continuous `f` with Lipschitz vector
`v` varies by at most `αⁿ Σ v · 2|R|` over all configurations.

DERIVED: `2 |R|` the diameter; `0`, `1` as in `lip_iterS`. -/
theorem sweep_mixingW {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {L : List Lk} (hL : ∀ l, l ∈ L) (n : ℕ) {f : (Lk → Tsp R) → ℝ} (hf : Continuous f)
    {v : Lk → ℝ} (hv : LipLe f v) (W W' : Lk → Tsp R) :
    |(sweepS S L)^[n] f W - (sweepS S L)^[n] f W'| ≤ α ^ n * (∑ k, v k) * (2 * |R|) := by
  obtain ⟨u, hu, hus⟩ := lip_iterS hC hC0 hrow hα0 hα1 hL n hf hv
  refine (abs_sub_le_sum_lip hu W W').trans ?_
  exact mul_le_mul_of_nonneg_right hus (by positivity)

#print axioms sweep_mixingW

/-- **The sweep converges to every invariant state geometrically, W1 form**:
`|Tⁿ f (W) − σ f| ≤ αⁿ Σ v · 2|R|`.

DERIVED: `2 |R|` the diameter; `0`, `1` as in `lip_iterS`. -/
theorem sweep_to_stateW {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)}
    (hσ : Invariant S σ) {C : Lk → Lk → ℝ} (hC : W1Infl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    (n : ℕ) (f : C(Lk → Tsp R, ℝ)) {v : Lk → ℝ} (hv : LipLe f v) (W : Lk → Tsp R) :
    |(sweepS S L)^[n] f W - σ f| ≤ α ^ n * (∑ k, v k) * (2 * |R|) := by
  set B := α ^ n * (∑ k, v k) * (2 * |R|)
  have hinv := state_iterS hσ L n f
  have hmix := fun V => sweep_mixingW hC hC0 hrow hα0 hα1 hL n f.continuous hv V W
  have hlo : ∀ V, (((sweepS S L)^[n] f W - B) • (1 : C(Lk → Tsp R, ℝ))) V
      ≤ sweepCS S L n f V := fun V => by
    have := (abs_le.mp (hmix V)).1
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show _ ≤ (sweepS S L)^[n] f V
    linarith
  have hhi : ∀ V, sweepCS S L n f V
      ≤ (((sweepS S L)^[n] f W + B) • (1 : C(Lk → Tsp R, ℝ))) V := fun V => by
    have := (abs_le.mp (hmix V)).2
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show (sweepS S L)^[n] f V ≤ _
    linarith
  have h1 := σ.mono hlo
  have h2 := σ.mono hhi
  rw [σ.map_smul, σ.map_one, mul_one, hinv] at h1 h2
  rw [abs_le]
  constructor <;> linarith

#print axioms sweep_to_stateW

/-- **Uniqueness on Lipschitz observables**: two states invariant under a specification with W1
influence `C ≥ 0` of row sums `≤ α < 1` agree on every continuous observable with a Lipschitz
vector (`sweep_to_stateW` from one configuration, `αⁿ → 0`).

DERIVED: `0` the sign of `α` and the limit of `αⁿ`; `1` the strict bound on `α`. -/
theorem state_unique_lipW {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ν ν' : DLRLimit.State (Lk → Tsp R)} (hν : Invariant S ν) (hν' : Invariant S ν')
    (f : C(Lk → Tsp R, ℝ)) {v : Lk → ℝ} (hv : LipLe f v) : ν f = ν' f := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  obtain ⟨W0⟩ : Nonempty (Lk → Tsp R) := inferInstance
  have h : ∀ n : ℕ, |ν f - ν' f| ≤ 2 * (α ^ n * (∑ k, v k) * (2 * |R|)) := fun n => by
    have a1 := sweep_to_stateW hν hC hC0 hrow hα0 hα1.le hL n f hv W0
    have a2 := sweep_to_stateW hν' hC hC0 hrow hα0 hα1.le hL n f hv W0
    rw [abs_sub_comm] at a1
    calc |ν f - ν' f| ≤ |ν f - (sweepS S L)^[n] f W0| + |(sweepS S L)^[n] f W0 - ν' f| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  have ht : Tendsto (fun n : ℕ => 2 * (α ^ n * (∑ k, v k) * (2 * |R|))) atTop
      (𝓝 (2 * (0 * (∑ k, v k) * (2 * |R|)))) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const _).mul_const _).const_mul _
  have hle := ge_of_tendsto' ht h
  simp only [zero_mul, mul_zero] at hle
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)

#print axioms state_unique_lipW

/-- **The coordinate observable** `W ↦ W l`.

DERIVED: no numeral. -/
def crd (l : Lk) : C(Lk → Tsp R, ℝ) :=
  ⟨fun W => (W l : ℝ), continuous_subtype_val.comp (continuous_apply l)⟩

/-- **The coordinate has the unit Lipschitz vector at its site.**

DERIVED: `1`, `0` the vector. -/
theorem lipLe_crd (l : Lk) : LipLe (R := R) (crd l) (fun k => if k = l then 1 else 0) := by
  refine ⟨fun k => by dsimp only; split_ifs <;> norm_num, fun W k x => ?_⟩
  show |(Function.update W k x l : ℝ) - (W l : ℝ)|
    ≤ (if k = l then (1 : ℝ) else 0) * |(x : ℝ) - (W k : ℝ)|
  by_cases hk : k = l
  · subst hk
    rw [Function.update_self, if_pos rfl, one_mul]
  · rw [Function.update_of_ne (Ne.symm hk), if_neg hk, sub_self, abs_zero, zero_mul]

#print axioms lipLe_crd

/-- **The observables with a Lipschitz vector form a subalgebra**: constants have the zero vector,
sums add vectors, and a product of `f`, `g` bounded by `B_f`, `B_g` has the vector
`B_f v_g + B_g v_f`.

DERIVED: `0` the vector of a constant; `1` none. -/
def lipSub : Subalgebra ℝ C(Lk → Tsp R, ℝ) where
  carrier := {f | ∃ v, LipLe f v}
  mul_mem' := by
    rintro f g ⟨vf, hvf⟩ ⟨vg, hvg⟩
    obtain ⟨Bf, hBf⟩ := exists_abs_le f.continuous
    obtain ⟨Bg, hBg⟩ := exists_abs_le g.continuous
    show ∃ v, LipLe _ v
    refine ⟨fun k => max Bf 0 * vg k + max Bg 0 * vf k,
      fun k => add_nonneg (mul_nonneg (le_max_right _ _) (hvg.1 k))
        (mul_nonneg (le_max_right _ _) (hvf.1 k)), fun W k x => ?_⟩
    simp only [ContinuousMap.mul_apply]
    have e : f (Function.update W k x) * g (Function.update W k x) - f W * g W
        = f (Function.update W k x) * (g (Function.update W k x) - g W)
          + g W * (f (Function.update W k x) - f W) := by ring
    rw [e]
    have h1 : |f (Function.update W k x)| ≤ max Bf 0 := (hBf _).trans (le_max_left _ _)
    have h2 : |g W| ≤ max Bg 0 := (hBg _).trans (le_max_left _ _)
    calc |f (Function.update W k x) * (g (Function.update W k x) - g W)
          + g W * (f (Function.update W k x) - f W)|
        ≤ |f (Function.update W k x)| * |g (Function.update W k x) - g W|
          + |g W| * |f (Function.update W k x) - f W| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ max Bf 0 * (vg k * |(x : ℝ) - (W k : ℝ)|) + max Bg 0 * (vf k * |(x : ℝ) - (W k : ℝ)|) :=
          add_le_add (mul_le_mul h1 (hvg.2 W k x) (abs_nonneg _) (le_max_right _ _))
            (mul_le_mul h2 (hvf.2 W k x) (abs_nonneg _) (le_max_right _ _))
      _ = (max Bf 0 * vg k + max Bg 0 * vf k) * |(x : ℝ) - (W k : ℝ)| := by ring
  one_mem' := by
    show ∃ v, LipLe _ v
    exact ⟨fun _ => 0, fun _ => le_rfl, fun W k x => by simp⟩
  add_mem' := by
    rintro f g ⟨vf, hvf⟩ ⟨vg, hvg⟩
    show ∃ v, LipLe _ v
    refine ⟨fun k => vf k + vg k, fun k => add_nonneg (hvf.1 k) (hvg.1 k), fun W k x => ?_⟩
    simp only [ContinuousMap.add_apply]
    calc |f (Function.update W k x) + g (Function.update W k x) - (f W + g W)|
        ≤ |f (Function.update W k x) - f W| + |g (Function.update W k x) - g W| := by
          rw [show f (Function.update W k x) + g (Function.update W k x) - (f W + g W)
            = (f (Function.update W k x) - f W) + (g (Function.update W k x) - g W) by ring]
          exact abs_add_le _ _
      _ ≤ vf k * |(x : ℝ) - (W k : ℝ)| + vg k * |(x : ℝ) - (W k : ℝ)| :=
          add_le_add (hvf.2 W k x) (hvg.2 W k x)
      _ = (vf k + vg k) * |(x : ℝ) - (W k : ℝ)| := by ring
  zero_mem' := by
    show ∃ v, LipLe _ v
    exact ⟨fun _ => 0, fun _ => le_rfl, fun W k x => by simp⟩
  algebraMap_mem' c := by
    show ∃ v, LipLe _ v
    exact ⟨fun _ => 0, fun _ => le_rfl, fun W k x => by simp⟩

/-- **The Lipschitz observables separate points**: two configurations that differ at `k` differ in
the coordinate `crd k`.

DERIVED: no numeral. -/
theorem lipSub_separatesPoints : (lipSub (R := R) (Lk := Lk)).SeparatesPoints := by
  intro W W' hne
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  refine ⟨_, ⟨crd k, by show ∃ v, LipLe _ v; exact ⟨_, lipLe_crd k⟩, rfl⟩, ?_⟩
  show (W k : ℝ) ≠ (W' k : ℝ)
  exact fun h => hk (Subtype.ext h)

#print axioms lipSub_separatesPoints

/-- **Uniqueness under Dobrushin's W1 condition**: two states invariant under a specification with
W1 influence `C ≥ 0` of row sums `≤ α < 1` are equal (`state_unique_lipW` on `lipSub`, which
separates points; `DLRLimit.State.eq_of_eqOn_subalgebra`, Stone–Weierstrass).

DERIVED: `0`, `1` as in `state_unique_lipW`. -/
theorem state_unique_W1 {S : Spec (Tsp R) Lk} {C : Lk → Lk → ℝ} (hC : W1Infl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ν ν' : DLRLimit.State (Lk → Tsp R)} (hν : Invariant S ν) (hν' : Invariant S ν')
    (f : C(Lk → Tsp R, ℝ)) : ν f = ν' f :=
  DLRLimit.State.eq_of_eqOn_subalgebra lipSub lipSub_separatesPoints
    (fun g hg => by
      obtain ⟨_, hv⟩ := hg
      exact state_unique_lipW hC hC0 hrow hα0 hα1 hν hν' g hv) f

#print axioms state_unique_W1

end Lip

/-! ## 2. The conditional covariance at one site -/

section CondCov

variable {Lk : Type} [DecidableEq Lk] (S : Spec (Tsp R) Lk)

/-- **Three-term linearity of a kernel** on continuous functions.

DERIVED: `1` the coefficient of the combined pair. -/
theorem P_lin3 (l : Lk) {f g h : (Lk → Tsp R) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (a b c : ℝ) (W : Lk → Tsp R) :
    S.P l (fun V => a * f V + b * g V + c * h V) W
      = a * S.P l f W + b * S.P l g W + c * S.P l h W := by
  have e1 := S.lin l (f := fun V => a * f V + b * g V) (f' := h)
    (cadd (csmul a hf) (csmul b hg)) hh 1 c W
  simp only [one_mul] at e1
  rw [e1, S.lin l hf hg a b W]

#print axioms P_lin3

/-- **The conditional variance in shifted form**: for every constant `c`,
`P(h²) − (P h)² = P((h − c)²) − (P h − c)²`.

DERIVED: `2` the power and the cross term. -/
theorem var_shift (l : Lk) {h : (Lk → Tsp R) → ℝ} (hh : Continuous h) (c : ℝ) (W : Lk → Tsp R) :
    S.P l (fun V => h V ^ 2) W - (S.P l h W) ^ 2
      = S.P l (fun V => (h V - c) ^ 2) W - (S.P l h W - c) ^ 2 := by
  have e : (fun V => (h V - c) ^ 2) = fun V => 1 * h V ^ 2 + (-2 * c) * h V + c ^ 2 := by
    funext V; ring
  have hl := S.lin_const l (f := fun V => h V ^ 2) (f' := h) (hh.pow 2) hh 1 (-2 * c) (c ^ 2) W
  rw [e, hl]
  ring

#print axioms var_shift

/-- **The conditional variance is non-negative.**

DERIVED: `0` the sign; `2` the power. -/
theorem var_nonneg (l : Lk) {h : (Lk → Tsp R) → ℝ} (hh : Continuous h) (W : Lk → Tsp R) :
    0 ≤ S.P l (fun V => h V ^ 2) W - (S.P l h W) ^ 2 := by
  rw [var_shift S l hh (S.P l h W) W, sub_self, zero_pow two_ne_zero, sub_zero]
  have hm := S.mono l (f := fun _ => (0 : ℝ)) (f' := fun V => (h V - S.P l h W) ^ 2)
    continuous_const ((hh.sub continuous_const).pow 2) W fun g => sq_nonneg _
  rwa [S.const] at hm

#print axioms var_nonneg

/-- **The conditional mean of the spin lies in the spin interval.**

DERIVED: `0` the comparison function. -/
theorem abs_P_crd_le (l : Lk) (W : Lk → Tsp R) : |S.P l (fun V => (V l : ℝ)) W| ≤ |R| := by
  have h := S.sub_le l (f := fun V => (V l : ℝ)) (f' := fun _ => (0 : ℝ))
    (continuous_subtype_val.comp (continuous_apply l)) continuous_const W (c := |R|) fun g => by
      show |(Function.update W l g l : ℝ) - 0| ≤ |R|
      rw [sub_zero]
      exact abs_le.mpr ⟨(Function.update W l g l).2.1, (Function.update W l g l).2.2⟩
  rwa [S.const, sub_zero] at h

#print axioms abs_P_crd_le

/-- **The conditional variance of the spin at `l`**: `P(x_l²) − (P x_l)²`.

DERIVED: `2` the power. -/
def cvar (l : Lk) (W : Lk → Tsp R) : ℝ :=
  S.P l (fun V => (V l : ℝ) ^ 2) W - (S.P l (fun V => (V l : ℝ)) W) ^ 2

/-- **A Lipschitz function has conditional variance at most `a²` times that of the spin.** If `h`
is `a`-Lipschitz on the fibre of `l` at `W`, then `P(h²) − (P h)² ≤ a² · cvar l W`: shift by the
value of `h` at the conditional mean `m` of the spin (`var_shift`), and compare `(h − h(m))²` with
`a² (x_l − m)²` on the fibre.

DERIVED: `2` the powers; `0` the sign of `a`. -/
theorem var_le (l : Lk) {h : (Lk → Tsp R) → ℝ} (hh : Continuous h) {a : ℝ} (ha : 0 ≤ a)
    (W : Lk → Tsp R)
    (hl : ∀ g g' : Tsp R, |h (Function.update W l g) - h (Function.update W l g')|
      ≤ a * |(g : ℝ) - (g' : ℝ)|) :
    S.P l (fun V => h V ^ 2) W - (S.P l h W) ^ 2 ≤ a ^ 2 * cvar S l W := by
  set m := S.P l (fun V => (V l : ℝ)) W with hm
  have hmR := abs_le.mp (abs_P_crd_le S l W)
  set mm : Tsp R := ⟨m, hmR.1, hmR.2⟩
  have hcrd : Continuous (fun V : Lk → Tsp R => (V l : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply l)
  rw [var_shift S l hh (h (Function.update W l mm)) W]
  have h1 : S.P l (fun V => (h V - h (Function.update W l mm)) ^ 2) W
      ≤ S.P l (fun V => a ^ 2 * ((V l : ℝ) - m) ^ 2) W := by
    refine S.mono l ((hh.sub continuous_const).pow 2)
      (continuous_const.mul ((hcrd.sub continuous_const).pow 2)) W fun g => ?_
    show (h (Function.update W l g) - h (Function.update W l mm)) ^ 2
      ≤ a ^ 2 * ((Function.update W l g l : ℝ) - m) ^ 2
    rw [Function.update_self]
    have hb := hl g mm
    have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs, mul_pow, sq_abs] at hb2
    exact hb2
  have e : (fun V : Lk → Tsp R => a ^ 2 * ((V l : ℝ) - m) ^ 2)
      = fun V => a ^ 2 * (V l : ℝ) ^ 2 + (-2 * a ^ 2 * m) * (V l : ℝ) + a ^ 2 * m ^ 2 := by
    funext V; ring
  have hl2 := S.lin_const l (f := fun V => (V l : ℝ) ^ 2) (f' := fun V => (V l : ℝ))
    (hcrd.pow 2) hcrd (a ^ 2) (-2 * a ^ 2 * m) (a ^ 2 * m ^ 2) W
  rw [e, hl2, ← hm] at h1
  have hsq := sq_nonneg (S.P l h W - h (Function.update W l mm))
  unfold cvar
  rw [← hm]
  linarith

#print axioms var_le

/-- **The conditional covariance at one site, positive constants**: if `f`, `g` are `a`- and
`b`-Lipschitz on the fibre of `l` at `W` with `a, b > 0`, then
`|P(f g) − P f · P g| ≤ a b · cvar l W` (polarisation: `u± = b f ± a g` are `2ab`-Lipschitz, so
`Var u+ ≤ 4a²b² cvar`, `Var u− ≥ 0`, and `Var u+ − Var u− = 4ab · Cov(f, g)`).

DERIVED: `2`, `4` the polarisation; `0` the signs. -/
theorem condCov_le_pos (l : Lk) {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (W : Lk → Tsp R)
    (hfl : ∀ x y : Tsp R, |f (Function.update W l x) - f (Function.update W l y)|
      ≤ a * |(x : ℝ) - (y : ℝ)|)
    (hgl : ∀ x y : Tsp R, |g (Function.update W l x) - g (Function.update W l y)|
      ≤ b * |(x : ℝ) - (y : ℝ)|) :
    |S.P l (fun V => f V * g V) W - S.P l f W * S.P l g W| ≤ a * b * cvar S l W := by
  have eP : ∀ s t : ℝ, S.P l (fun V => (s * f V + t * g V) ^ 2) W
      = s ^ 2 * S.P l (fun V => f V ^ 2) W + (2 * s * t) * S.P l (fun V => f V * g V) W
        + t ^ 2 * S.P l (fun V => g V ^ 2) W := fun s t => by
    have e : (fun V => (s * f V + t * g V) ^ 2)
        = fun V => s ^ 2 * f V ^ 2 + (2 * s * t) * (f V * g V) + t ^ 2 * g V ^ 2 := by
      funext V; ring
    rw [e]
    exact P_lin3 S l (hf.pow 2) (hf.mul hg) (hg.pow 2) _ _ _ W
  have eL : ∀ s t : ℝ, S.P l (fun V => s * f V + t * g V) W = s * S.P l f W + t * S.P l g W :=
    fun s t => S.lin l hf hg s t W
  have hu : ∀ s t : ℝ, Continuous (fun V => s * f V + t * g V) := fun s t =>
    (continuous_const.mul hf).add (continuous_const.mul hg)
  have hlip : ∀ s t : ℝ, ∀ x y : Tsp R,
      |(s * f (Function.update W l x) + t * g (Function.update W l x))
        - (s * f (Function.update W l y) + t * g (Function.update W l y))|
      ≤ (|s| * a + |t| * b) * |(x : ℝ) - (y : ℝ)| := fun s t x y => by
    rw [show s * f (Function.update W l x) + t * g (Function.update W l x)
        - (s * f (Function.update W l y) + t * g (Function.update W l y))
        = s * (f (Function.update W l x) - f (Function.update W l y))
          + t * (g (Function.update W l x) - g (Function.update W l y)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul_of_nonneg_left (hfl x y) (abs_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left (hgl x y) (abs_nonneg t)
    nlinarith
  have hcon : ∀ s t : ℝ, 0 ≤ |s| * a + |t| * b := fun s t => by positivity
  have vp := var_le S l (hu b a) (hcon b a) W (hlip b a)
  have vm := var_le S l (hu b (-a)) (hcon b (-a)) W (hlip b (-a))
  have np := var_nonneg S l (hu b a) W
  have nm := var_nonneg S l (hu b (-a)) W
  rw [eP, eL] at vp vm np nm
  rw [abs_of_pos ha, abs_of_pos hb] at vp
  rw [abs_neg, abs_of_pos ha, abs_of_pos hb] at vm
  set A := S.P l (fun V => f V ^ 2) W
  set B := S.P l (fun V => f V * g V) W
  set Cg := S.P l (fun V => g V ^ 2) W
  set x := S.P l f W
  set y := S.P l g W
  set Vc := cvar S l W
  have hab : 0 < 4 * a * b := by positivity
  have up : 4 * a * b * (B - x * y) ≤ 4 * a * b * (a * b * Vc) := by nlinarith
  have lo : 4 * a * b * (-(B - x * y)) ≤ 4 * a * b * (a * b * Vc) := by nlinarith
  rw [abs_le]
  constructor
  · have := le_of_mul_le_mul_left lo hab
    linarith
  · exact le_of_mul_le_mul_left up hab

#print axioms condCov_le_pos

/-- **The conditional covariance at one site**: if `f`, `g` are `a`- and `b`-Lipschitz on the
fibre of `l` at `W` (`a, b ≥ 0`), then `|P(f g) − P f · P g| ≤ a b · cvar l W`
(`condCov_le_pos` at `a + 1/(n+1)`, `b + 1/(n+1)`, and the limit).

DERIVED: `1/(n+1)` the vanishing slack; `0` the signs. -/
theorem condCov_le (l : Lk) {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (W : Lk → Tsp R)
    (hfl : ∀ x y : Tsp R, |f (Function.update W l x) - f (Function.update W l y)|
      ≤ a * |(x : ℝ) - (y : ℝ)|)
    (hgl : ∀ x y : Tsp R, |g (Function.update W l x) - g (Function.update W l y)|
      ≤ b * |(x : ℝ) - (y : ℝ)|) :
    |S.P l (fun V => f V * g V) W - S.P l f W * S.P l g W| ≤ a * b * cvar S l W := by
  have hε : ∀ n : ℕ, |S.P l (fun V => f V * g V) W - S.P l f W * S.P l g W|
      ≤ (a + 1 / ((n : ℝ) + 1)) * (b + 1 / ((n : ℝ) + 1)) * cvar S l W := fun n => by
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    refine condCov_le_pos S l hf hg (by linarith) (by linarith) W (fun x y => ?_) (fun x y => ?_)
    · exact (hfl x y).trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
    · exact (hgl x y).trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have ht : Tendsto (fun n : ℕ => (a + 1 / ((n : ℝ) + 1)) * (b + 1 / ((n : ℝ) + 1)) * cvar S l W)
      atTop (𝓝 ((a + 0) * (b + 0) * cvar S l W)) :=
    ((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)).mul_const _
  have h := ge_of_tendsto' ht hε
  simpa using h

#print axioms condCov_le

/-- The conditional variance is continuous in the configuration.

DERIVED: `2` the power. -/
theorem continuous_cvar (l : Lk) : Continuous (cvar S l) := by
  have hcrd : Continuous (fun V : Lk → Tsp R => (V l : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply l)
  exact (S.cont l (hcrd.pow 2)).sub ((S.cont l hcrd).pow 2)

#print axioms continuous_cvar

end CondCov

/-! ## 3. Covariance decay -/

section Cov

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **A pointwise bound by a function bounds the value**: `|F| ≤ G` gives `|σ F| ≤ σ G`.

DERIVED: `-1` the reflected bound. -/
theorem abs_ex_le_ex {X : Type} [TopologicalSpace X] [CompactSpace X] (σ : DLRLimit.State X)
    {F G : X → ℝ} (hF : Continuous F) (hG : Continuous G) (h : ∀ x, |F x| ≤ G x) :
    |ex σ F| ≤ ex σ G := by
  rw [ex_mk σ hF, ex_mk σ hG]
  have h1 := σ.mono (f := ⟨F, hF⟩) (g := ⟨G, hG⟩) fun x => (abs_le.mp (h x)).2
  have h2 := σ.mono (f := (-1 : ℝ) • ⟨G, hG⟩) (g := ⟨F, hF⟩) fun x => by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.coe_mk]
    linarith [(abs_le.mp (h x)).1]
  rw [σ.map_smul] at h2
  rw [abs_le]
  constructor <;> linarith

#print axioms abs_ex_le_ex

/-- **The mean conditional variance is at most the second moment** for an invariant state.

DERIVED: `2` the power; `0` the sign of a square's mean. -/
theorem ex_cvar_le {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)} (hσ : Invariant S σ)
    (l : Lk) : ex σ (cvar S l) ≤ ex σ (fun W => (W l : ℝ) ^ 2) := by
  have hcrd : Continuous (fun V : Lk → Tsp R => (V l : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply l)
  have e := ex_sub σ (S.cont l (hcrd.pow 2)) ((S.cont l hcrd).pow 2)
  have i1 := ex_P hσ l (hcrd.pow 2)
  have hnn : 0 ≤ ex σ (fun W => (S.P l (fun V => (V l : ℝ)) W) ^ 2) := by
    rw [ex_mk σ ((S.cont l hcrd).pow 2)]
    exact σ.nonneg _ fun W => sq_nonneg _
  show ex σ (fun W => S.P l (fun V => (V l : ℝ) ^ 2) W - (S.P l (fun V => (V l : ℝ)) W) ^ 2) ≤ _
  rw [e, i1]
  linarith

#print axioms ex_cvar_le

/-- **One kernel in the covariance, W1 form**: replacing `f` by `P l f` in `σ(f g)` costs at most
`v_f(l) v_g(l) σ(x_l²)` (invariance, pull-out, `condCov_le`, `ex_cvar_le`).

DERIVED: `2` the power. -/
theorem cov_stepW {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)} (hσ : Invariant S σ)
    (l : Lk) {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipLe f vf) (hvg : LipLe g vg) :
    |ex σ (fun W => f W * g W) - ex σ (fun W => S.P l f W * g W)|
      ≤ vf l * vg l * ex σ (fun W => (W l : ℝ) ^ 2) := by
  have hPf := S.cont l hf
  have hPg := S.cont l hg
  have i1 := ex_P hσ l (cmul hf hg)
  have i2 := ex_P hσ l (cmul hPf hg)
  have e2 : S.P l (fun W => S.P l f W * g W) = fun W => S.P l f W * S.P l g W :=
    funext fun W => S.pull l hPf hg (fun V x => S.upd l f V x) W
  rw [e2] at i2
  rw [← i1, ← i2, ← ex_sub σ (S.cont l (cmul hf hg)) (cmul hPf hPg)]
  have hb := abs_ex_le_ex σ (csub (S.cont l (cmul hf hg)) (cmul hPf hPg))
    (csmul (vf l * vg l) (continuous_cvar S l))
    fun W => condCov_le S l hf hg (hvf.1 l) (hvg.1 l) W (hvf.fibre W l) (hvg.fibre W l)
  rw [ex_const_mul σ _ (continuous_cvar S l)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (ex_cvar_le hσ l)
    (mul_nonneg (hvf.1 l) (hvg.1 l)))

#print axioms cov_stepW

/-- **The covariance telescope, W1 form**: if `σ(x_l²) ≤ M` wherever `v_g(l) ≠ 0`, then along any
list `L`, `|σ(f g) − σ((sweep L f) g)| ≤ oscCost C (M v_g) L v_f`.

DERIVED: `0` the cost of the empty run and the vanishing `v_g`. -/
theorem cov_runW {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : W1Infl S C) (hC0 : ∀ l k, 0 ≤ C l k) {g : (Lk → Tsp R) → ℝ}
    (hg : Continuous g) {vg : Lk → ℝ} (hvg : LipLe g vg) {M : ℝ}
    (hM : ∀ l, vg l ≠ 0 → ex σ (fun W => (W l : ℝ) ^ 2) ≤ M) :
    ∀ (L : List Lk) {f : (Lk → Tsp R) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipLe f v →
      |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L f W * g W)|
        ≤ oscCost C (fun l => vg l * M) L v
  | [], f, _, v, _ => by
      show |ex σ (fun W => f W * g W) - ex σ (fun W => f W * g W)| ≤ 0
      simp
  | l :: L, f, hf, v, hv => by
      have h1 := cov_stepW hσ l hf hg hv hvg
      have h1' : v l * vg l * ex σ (fun W => (W l : ℝ) ^ 2) ≤ v l * (vg l * M) := by
        by_cases h0 : vg l = 0
        · rw [h0]; simp
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hM l h0) (hvg.1 l)) (hv.1 l)
      have h2 := cov_runW hσ hC hC0 hg hvg hM L (S.cont l hf) (lip_stepS hC hC0 hf hv l)
      show |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L (S.P l f) W * g W)|
        ≤ v l * (vg l * M) + oscCost C (fun l => vg l * M) L (oscStep C l v)
      calc |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L (S.P l f) W * g W)|
          ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => S.P l f W * g W)|
            + |ex σ (fun W => S.P l f W * g W)
              - ex σ (fun W => sweepS S L (S.P l f) W * g W)| := abs_sub_le _ _ _
        _ ≤ v l * (vg l * M) + oscCost C (fun l => vg l * M) L (oscStep C l v) :=
            add_le_add (h1.trans h1') h2

#print axioms cov_runW

/-- **Dobrushin's covariance bound, W1 form, weighted.** For an invariant state of a specification
with W1 influence `C ≥ 0` of row sums `≤ α`, any `α < θ ≤ 1`, any level `ψ` that one influence step
changes by at most one, continuous `f, g` with Lipschitz vectors `v_f, v_g`, `v_g ≤ V_g θ^ψ`, and
`σ(x_l²) ≤ M` wherever `v_g(l) ≠ 0`:
`|σ(f g) − σ f σ g| ≤ M V_g θ/(θ − α) · Σ_k θ^{ψ k} v_f(k)`.

DERIVED: `0` the sign of `α`, `M` and the limit of `αⁿ`; `1` the bound on `θ`; `2 |R|` the
diameter in the vanishing tail. -/
theorem cov_le_weightedW {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)}
    (hσ : Invariant S σ) {C : Lk → Lk → ℝ} (hC : W1Infl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) (ψ : Lk → ℕ)
    (hloc : ∀ l k, C l k ≠ 0 → ψ l ≤ ψ k + 1) {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f)
    (hg : Continuous g) {vf vg : Lk → ℝ} (hvf : LipLe f vf) (hvg : LipLe g vg) {Vg M : ℝ}
    (hVg : 0 ≤ Vg) (hM0 : 0 ≤ M) (hw : ∀ k, vg k ≤ Vg * θ ^ ψ k)
    (hM : ∀ l, vg l ≠ 0 → ex σ (fun W => (W l : ℝ) ^ 2) ≤ M) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  obtain ⟨B, hB⟩ := exists_abs_le hg
  have hθ0 : 0 ≤ θ := by linarith
  have hα1 : α < 1 := by linarith
  have hθα : 0 < θ - α := by linarith
  have hvf0 : ∀ k, 0 ≤ vf k := hvf.1
  have hS0 : 0 ≤ ∑ k, vf k := Finset.sum_nonneg fun k _ => hvf0 k
  have hw' : ∀ k, vg k * M ≤ M * Vg * θ ^ ψ k := fun k => by
    have := mul_le_mul_of_nonneg_right (hw k) hM0
    linarith
  have hn : ∀ n : ℕ, |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
        + α ^ n * (∑ k, vf k) * (2 * |R|) * B := by
    intro n
    have h1 := cov_runW hσ hC hC0 hg hvg hM (rep L n) hf hvf
    have h2 := cost_le hC0 hrow hαθ.le hθ0 hθ1 ψ hloc (mul_nonneg hM0 hVg) hw' (rep L n) vf hvf0
    have h3 : oscCost C (fun l => vg l * M) (rep L n) vf
        ≤ M * Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k := by
      have e : M * Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
          = M * Vg * (θ * ∑ k, θ ^ ψ k * vf k) / (θ - α) := by ring
      rw [e, le_div_iff₀ hθα]
      linarith
    have hc : Continuous (sweepS S (rep L n) f) := continuous_sweepS S _ hf
    have hT : ∀ W, |(sweepS S (rep L n) f W - ex σ f) * g W|
        ≤ α ^ n * (∑ k, vf k) * (2 * |R|) * B := by
      intro W
      have h := sweep_to_stateW hσ hC hC0 hrow hα0 hα1.le hL n ⟨f, hf⟩ hvf W
      rw [sweepS_rep] at h
      rw [abs_mul, ex_mk σ hf]
      exact mul_le_mul h (hB W) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (pow_nonneg hα0 n) hS0) (by positivity))
    have e : ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g
        = ex σ (fun W => (sweepS S (rep L n) f W - ex σ f) * g W) := by
      have e1 : (fun W => (sweepS S (rep L n) f W - ex σ f) * g W)
          = fun W => sweepS S (rep L n) f W * g W - ex σ f * g W :=
        funext fun W => by ring
      rw [e1, ex_sub σ (F := fun W => sweepS S (rep L n) f W * g W)
        (G := fun W => ex σ f * g W) (cmul hc hg) (csmul _ hg),
        ex_const_mul σ _ hg]
    have h4 : |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g|
        ≤ α ^ n * (∑ k, vf k) * (2 * |R|) * B := by
      rw [e]
      exact abs_ex_le σ (cmul (csubc hc (ex σ f)) hg) hT
    calc |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
        ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S (rep L n) f W * g W)|
          + |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith [h1.trans h3]
  have ht : Tendsto (fun n : ℕ => M * Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
      + α ^ n * (∑ k, vf k) * (2 * |R|) * B)
      atTop (𝓝 (M * Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
        + 0 * (∑ k, vf k) * (2 * |R|) * B)) :=
    ((((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const _).mul_const _).mul_const
      _).const_add _
  have hle := ge_of_tendsto' ht hn
  simpa using hle

#print axioms cov_le_weightedW

/-- **Spatial Dobrushin decay, W1 form.** Under the W1 influence hypotheses with row sums
`≤ α < θ ≤ 1`: if `g` has Lipschitz vector `≤ V_g` on `B` and `0` off it, `σ(x_l²) ≤ M` on `B`, and
`f` has Lipschitz vector `0` on `reach C B d`, then
`|σ(f g) − σ f σ g| ≤ M V_g θ/(θ − α) · θ^{d+1} Σ_k v_f(k)` (`cov_le_weightedW` at
`level C B (d + 1)`).

DERIVED: `0` the sign and the vectors off the supports; `1` the bound on `θ` and the cap beyond
`d`. -/
theorem cov_spatialW {S : Spec (Tsp R) Lk} {σ : DLRLimit.State (Lk → Tsp R)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : W1Infl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    {f g : (Lk → Tsp R) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipLe f vf) (hvg : LipLe g vg) (B : Finset Lk) {Vg M : ℝ} (hVg : 0 ≤ Vg) (hM0 : 0 ≤ M)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg)
    (hM : ∀ l ∈ B, ex σ (fun W => (W l : ℝ) ^ 2) ≤ M) (d : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → k ∉ reach C B d) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg * θ / (θ - α) * (θ ^ (d + 1) * ∑ k, vf k) := by
  have hθ0 : 0 ≤ θ := by linarith
  have hw : ∀ k, vg k ≤ Vg * θ ^ level C B (d + 1) k := by
    intro k
    by_cases hk : k ∈ B
    · rw [level_of_mem C (d + 1) hk, pow_zero, mul_one]
      exact hgV k
    · rw [hgB k hk]
      exact mul_nonneg hVg (pow_nonneg hθ0 _)
  have hM' : ∀ l, vg l ≠ 0 → ex σ (fun W => (W l : ℝ) ^ 2) ≤ M := fun l hl =>
    hM l (by by_contra h; exact hl (hgB l h))
  have h := cov_le_weightedW hσ hC hC0 hrow hα0 hαθ hθ1 (level C B (d + 1))
    (fun l k hlk => level_loc C B (d + 1) hlk) hf hg hvf hvg hVg hM0 hw hM'
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : vf k = 0
    · rw [hk]; simp
    · rw [level_far C B (hfar k hk)]
  · exact div_nonneg (mul_nonneg (mul_nonneg hM0 hVg) hθ0) (by linarith)

#print axioms cov_spatialW

end Cov

end MassGap.DobrushinW1
