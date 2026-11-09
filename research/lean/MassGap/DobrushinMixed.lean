import Mathlib
import MassGap.DobrushinW1
import MassGap.ObserverEnergyCellCondW

noncomputable section

/-!
# MassGap.DobrushinMixed — Dobrushin's theorem with a cost per site

`DobrushinGeneral` and `DobrushinUnbounded` prove Dobrushin's theorem with total-variation influence on a
compact spin space; `DobrushinW1` with Kantorovich (W1) influence on real spins. A carrier whose sites are
of two kinds — group-valued coarse links read in total variation, and real cell energies read in W1 —
needs both at once. Here every site `l` carries its own cost `d l` on one compact spin space `Ω`
(the discrete cost gives total variation, `|x − y|` on a real coordinate gives W1), and the theorem is
proved once for any such family.

1. **Lipschitz vectors and influence per site** (`LipD`, `DInfl`, `LipD.fibre`, `lip_stepD`): `v` bounds
   the change of `f` per unit cost at each site; the kernel at `l` maps `v` to `oscStep C l v`.
2. **Contraction, mixing, convergence** (`abs_sub_le_lipD_finset`, `abs_sub_le_sum_lipD`, `lip_sweepD`,
   `lip_sweep_fullD`, `lip_iterD`, `sweep_mixingD`, `sweep_to_stateD`): with every cost at most `Dm`, the
   sweep converges to every invariant state at rate `αⁿ`, `Dm` entering only the vanishing tail.
3. **Covariance** (`CondCovD`, `condCovD_of_diam`, `cov_stepD`, `cov_runD`, `cov_le_weightedD`,
   `cov_spatialD`): given a conditional covariance bound `|P(fg) − Pf·Pg| ≤ a b V_l` for fibre-Lipschitz
   `f`, `g` (constants `a`, `b` in the cost of `l`), the covariance of `f`, `g` decays as `θ^{d+1}` under the
   weighted row `Σ_k C(l,k)/θ^{D(l,k)} ≤ α < 1`, with constant `M V_g/(1 − α)`, `M` bounding `σ(V_l)` where
   `g` moves. `condCovD_of_diam` discharges the bound with `V = Dm²` for any costs at most `Dm` (the
   total-variation sites).

## Scope

Specifications, invariant states, influence matrices and the conditional covariance bound are hypotheses.
-/

namespace MassGap.DobrushinMixed

open MeasureTheory Filter Topology
open MassGap.HeatBath (exists_abs_le)
open MassGap.BoxDobrushinCoupling (oscStep)
open MassGap.BoxDobrushinSpatial (oscCost rep oscStep_nonneg)
open MassGap.DobrushinGeneral (cmul csmul cadd csub caddc csubc ex ex_mk ex_sub ex_const_mul
  abs_ex_le)
open MassGap.DobrushinUnbounded (Spec Invariant OscLe sweepS continuous_sweepS sweepCS state_iterS
  sweepS_rep ex_P)
open MassGap.DobrushinW1 (abs_ex_le_ex)
open MassGap.ObserverEnergyCellCondW (cost_leU)

variable {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] [Nonempty Ω]

/-! ## 1. Lipschitz vectors and influence per site -/

section Lip

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **`v` bounds the change of `f` per unit cost at each site**: `v ≥ 0`, and changing the spin at `k`
from `W k` to `x` moves `f` by at most `v k · d k x (W k)`.

DERIVED: `0` the sign. -/
def LipD (d : Lk → Ω → Ω → ℝ) (f : (Lk → Ω) → ℝ) (v : Lk → ℝ) : Prop :=
  (∀ k, 0 ≤ v k) ∧ ∀ (W : Lk → Ω) (k : Lk) (x : Ω),
    |f (Function.update W k x) - f W| ≤ v k * d k x (W k)

/-- **The influence matrix in the costs**: changing the spin at `k ≠ l` from `W k` to `x` moves the
`P l`-mean of every continuous function of the spin at `l` that is `1`-Lipschitz in the cost of `l` by at
most `C l k · d k x (W k)`. With the discrete cost this is total variation, with `|x − y|` it is W1.

DERIVED: `1` the Lipschitz constant of the test functions. -/
def DInfl (S : Spec Ω Lk) (d : Lk → Ω → Ω → ℝ) (C : Lk → Lk → ℝ) : Prop :=
  ∀ l k, l ≠ k → ∀ (W : Lk → Ω) (x : Ω) (φ : Ω → ℝ), Continuous φ →
    (∀ a b : Ω, |φ a - φ b| ≤ d l a b) →
    |S.P l (fun V => φ (V l)) (Function.update W k x) - S.P l (fun V => φ (V l)) W|
      ≤ C l k * d k x (W k)

/-- **The fibre form of a Lipschitz vector.**

DERIVED: no numeral. -/
theorem LipD.fibre {d : Lk → Ω → Ω → ℝ} {f : (Lk → Ω) → ℝ} {v : Lk → ℝ} (hv : LipD d f v)
    (W : Lk → Ω) (l : Lk) (a b : Ω) :
    |f (Function.update W l a) - f (Function.update W l b)| ≤ v l * d l a b := by
  have h := hv.2 (Function.update W l b) l a
  rwa [Function.update_idem, Function.update_self] at h

#print axioms LipD.fibre

/-- **The kernel step on Lipschitz vectors.** For a continuous `f` with vector `v` and an influence
matrix `C ≥ 0`, `P l f` has vector `oscStep C l v`.

DERIVED: `0` the entry at `l` and the case `v l = 0`. -/
theorem lip_stepD {S : Spec Ω Lk} {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b)
    {C : Lk → Lk → ℝ} (hC : DInfl S d C) (hC0 : ∀ l k, 0 ≤ C l k) {f : (Lk → Ω) → ℝ}
    (hf : Continuous f) {v : Lk → ℝ} (hv : LipD d f v) (l : Lk) :
    LipD d (S.P l f) (oscStep C l v) := by
  refine ⟨oscStep_nonneg hC0 hv.1 l, fun W k x => ?_⟩
  unfold oscStep
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, S.upd, sub_self, abs_zero, zero_mul]
  rw [if_neg hkl]
  have hlk : l ≠ k := Ne.symm hkl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ω → ℝ, ∀ g, ψ g = f (Function.update W l g) := ⟨_, fun _ => rfl⟩
  have hu : Continuous (fun g : Ω => Function.update W l g) :=
    continuous_const.update l continuous_id
  have hψc : Continuous ψ := by
    have : ψ = fun g => f (Function.update W l g) := funext hψ
    rw [this]; exact hf.comp hu
  have hF : Continuous (fun V : Lk → Ω => ψ (V l)) := hψc.comp (continuous_apply l)
  have hd : 0 ≤ d k x (W k) := hd0 k x (W k)
  have s1 : |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) (Function.update W k x)|
      ≤ v k * d k x (W k) := by
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
  have hψL : ∀ a b, |ψ a - ψ b| ≤ v l * d l a b := fun a b => by
    rw [hψ, hψ]; exact hv.fibre W l a b
  have hvl : 0 ≤ v l := hv.1 l
  have s2 : |S.P l (fun V => ψ (V l)) (Function.update W k x) - S.P l (fun V => ψ (V l)) W|
      ≤ C l k * v l * d k x (W k) := by
    rcases hvl.eq_or_lt with h0 | hpos
    · have hconst : ∀ g, ψ g = ψ (W l) := fun g => by
        have h := hψL g (W l)
        rw [← h0, zero_mul] at h
        exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
      have e : (fun V : Lk → Ω => ψ (V l)) = fun _ => ψ (W l) := funext fun V => hconst _
      rw [e, S.const, S.const, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (hC0 l k) hvl) hd
    · obtain ⟨φ, hφ⟩ : ∃ φ : Ω → ℝ, ∀ g, φ g = ψ g / v l := ⟨_, fun _ => rfl⟩
      have hφc : Continuous φ := by
        have : φ = fun g => ψ g / v l := funext hφ
        rw [this]; exact hψc.div_const _
      have hφL : ∀ a b : Ω, |φ a - φ b| ≤ d l a b := fun a b => by
        rw [hφ, hφ, ← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, mul_comm]
        exact hψL a b
      have e : (fun V : Lk → Ω => ψ (V l)) = fun V => 0 + v l * φ (V l) := by
        have hne : v l ≠ 0 := hpos.ne'
        funext V; rw [hφ]; field_simp <;> ring
      have hφF : Continuous (fun V : Lk → Ω => φ (V l)) := hφc.comp (continuous_apply l)
      rw [e, S.affine l hφF, S.affine l hφF]
      have h := hC l k hlk W x φ hφc hφL
      rw [show 0 + v l * S.P l (fun V => φ (V l)) (Function.update W k x)
          - (0 + v l * S.P l (fun V => φ (V l)) W)
          = v l * (S.P l (fun V => φ (V l)) (Function.update W k x)
            - S.P l (fun V => φ (V l)) W) by ring, abs_mul, abs_of_nonneg hvl]
      calc v l * |S.P l (fun V => φ (V l)) (Function.update W k x) - S.P l (fun V => φ (V l)) W|
          ≤ v l * (C l k * d k x (W k)) := mul_le_mul_of_nonneg_left h hvl
        _ = C l k * v l * d k x (W k) := by ring
  rw [← s0]
  calc |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) W|
      ≤ |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) (Function.update W k x)|
        + |S.P l (fun V => ψ (V l)) (Function.update W k x) - S.P l (fun V => ψ (V l)) W| :=
        abs_sub_le _ _ _
    _ ≤ v k * d k x (W k) + C l k * v l * d k x (W k) := add_le_add s1 s2
    _ = (v k + C l k * v l) * d k x (W k) := by ring

#print axioms lip_stepD

/-- **Lipschitz constants add up over a set of sites.**

DERIVED: no numeral. -/
theorem abs_sub_le_lipD_finset {d : Lk → Ω → Ω → ℝ} {F : (Lk → Ω) → ℝ} {u : Lk → ℝ}
    (hu : LipD d F u) (W W' : Lk → Ω) (s : Finset Lk) :
    |F W - F (fun k => if k ∈ s then W' k else W k)| ≤ ∑ k ∈ s, u k * d k (W' k) (W k) := by
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
      _ ≤ ∑ k ∈ s, u k * d k (W' k) (W k) + u a * d a (W' a) (W a) := by
          rw [abs_sub_comm] at h2; linarith
      _ = u a * d a (W' a) (W a) + ∑ k ∈ s, u k * d k (W' k) (W k) := by ring

#print axioms abs_sub_le_lipD_finset

/-- **The total Lipschitz constant bounds the range**: `|F W − F W'| ≤ Σ u · Dm` when every cost is at
most `Dm`.

DERIVED: no numeral. -/
theorem abs_sub_le_sum_lipD {d : Lk → Ω → Ω → ℝ} {Dm : ℝ} (hD : ∀ l a b, d l a b ≤ Dm)
    {F : (Lk → Ω) → ℝ} {u : Lk → ℝ} (hu : LipD d F u) (W W' : Lk → Ω) :
    |F W - F W'| ≤ (∑ k, u k) * Dm := by
  have h := abs_sub_le_lipD_finset hu W W' Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  refine h.trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hD _ _ _) (hu.1 k)

#print axioms abs_sub_le_sum_lipD

/-- **The Lipschitz budget along a sweep.**

DERIVED: `0` the sign; `1` the bound on `α`. -/
theorem lip_sweepD {S : Spec Ω Lk} {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b)
    {C : Lk → Lk → ℝ} (hC : DInfl S d C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) (v : Lk → ℝ) :
    ∀ (L : List Lk) (T : Finset Lk) (f : (Lk → Ω) → ℝ) (u : Lk → ℝ), Continuous f →
      LipD d f u → (∀ k ∉ T, v k ≤ u k) → ∑ k, u k ≤ α * ∑ k ∈ T, v k + ∑ k ∈ Tᶜ, v k →
      ∃ u' : Lk → ℝ, LipD d (sweepS S L f) u' ∧ (∀ k ∉ T ∪ L.toFinset, v k ≤ u' k) ∧
        ∑ k, u' k ≤ α * ∑ k ∈ T ∪ L.toFinset, v k + ∑ k ∈ (T ∪ L.toFinset)ᶜ, v k
  | [], T, f, u, _, hu, hS, hsum => ⟨u, hu, by simpa using hS, by simpa using hsum⟩
  | l :: L, T, f, u, hf, hu, hS, hsum => by
    have hu0 : ∀ k, 0 ≤ u k := hu.1
    set u1 := oscStep C l u with hu1
    have hosc : LipD d (S.P l f) u1 := lip_stepD hd0 hC hC0 hf hu l
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
    obtain ⟨u', h1, h2, h3⟩ := lip_sweepD hd0 hC hC0 hrow hα1 v L (insert l T) (S.P l f) u1
      (S.cont l hf) hosc hS1 hsum1
    have eS : insert l T ∪ L.toFinset = T ∪ (l :: L).toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    rw [eS] at h2 h3
    exact ⟨u', h1, h2, h3⟩

#print axioms lip_sweepD

/-- **A full sweep contracts the total Lipschitz constant by `α`.**

DERIVED: `1` the bound on `α`. -/
theorem lip_sweep_fullD {S : Spec Ω Lk} {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b)
    {C : Lk → Lk → ℝ} (hC : DInfl S d C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    {f : (Lk → Ω) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : LipD d f v) :
    ∃ u' : Lk → ℝ, LipD d (sweepS S L f) u' ∧ ∑ k, u' k ≤ α * ∑ k, v k := by
  obtain ⟨u', h1, -, h3⟩ := lip_sweepD hd0 hC hC0 hrow hα1 v L ∅ f v hf hv
    (fun _ _ => le_rfl) (by simp)
  have hU : (∅ : Finset Lk) ∪ L.toFinset = Finset.univ := by
    ext l; simp [hL l]
  rw [hU, Finset.compl_univ, Finset.sum_empty, add_zero] at h3
  exact ⟨u', h1, h3⟩

#print axioms lip_sweep_fullD

/-- **`n` full sweeps leave total Lipschitz constant `≤ αⁿ Σ v`.**

DERIVED: `0` the sign of `α`; `1` the bound on `α`. -/
theorem lip_iterD {S : Spec Ω Lk} {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b)
    {C : Lk → Lk → ℝ} (hC : DInfl S d C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipD d f v →
      ∃ u : Lk → ℝ, LipD d ((sweepS S L)^[n] f) u ∧ ∑ k, u k ≤ α ^ n * ∑ k, v k
  | 0, _, _, v, hv => ⟨v, hv, by simp⟩
  | n + 1, f, hf, v, hv => by
    obtain ⟨u1, h1, h1s⟩ := lip_sweep_fullD hd0 hC hC0 hrow hα1 hL hf hv
    obtain ⟨u, hu, hus⟩ := lip_iterD hd0 hC hC0 hrow hα0 hα1 hL n (continuous_sweepS S L hf) h1
    refine ⟨u, by rwa [Function.iterate_succ_apply], hus.trans ?_⟩
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left h1s (pow_nonneg hα0 n)
    linarith

#print axioms lip_iterD

/-- **The sweep converges to every invariant state**: `|Tⁿ f (W) − σ f| ≤ αⁿ Σ v · Dm`.

DERIVED: `0`, `1` as in `lip_iterD`. -/
theorem sweep_to_stateD {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hDm : 0 ≤ Dm)
    (hD : ∀ l a b, d l a b ≤ Dm)
    {C : Lk → Lk → ℝ} (hC : DInfl S d C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    (n : ℕ) (f : C(Lk → Ω, ℝ)) {v : Lk → ℝ} (hv : LipD d f v) (W : Lk → Ω) :
    |(sweepS S L)^[n] f W - σ f| ≤ α ^ n * (∑ k, v k) * Dm := by
  set B := α ^ n * (∑ k, v k) * Dm
  have hinv := state_iterS hσ L n f
  obtain ⟨u, hu, hus⟩ := lip_iterD hd0 hC hC0 hrow hα0 hα1 hL n f.continuous hv
  have hmix : ∀ V, |(sweepS S L)^[n] f V - (sweepS S L)^[n] f W| ≤ B := fun V =>
    (abs_sub_le_sum_lipD hD hu V W).trans (mul_le_mul_of_nonneg_right hus hDm)
  have hlo : ∀ V, (((sweepS S L)^[n] f W - B) • (1 : C(Lk → Ω, ℝ))) V
      ≤ sweepCS S L n f V := fun V => by
    have := (abs_le.mp (hmix V)).1
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show _ ≤ (sweepS S L)^[n] f V
    linarith
  have hhi : ∀ V, sweepCS S L n f V
      ≤ (((sweepS S L)^[n] f W + B) • (1 : C(Lk → Ω, ℝ))) V := fun V => by
    have := (abs_le.mp (hmix V)).2
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show (sweepS S L)^[n] f V ≤ _
    linarith
  have h1 := σ.mono hlo
  have h2 := σ.mono hhi
  rw [σ.map_smul, σ.map_one, mul_one, hinv] at h1 h2
  rw [abs_le]
  constructor <;> linarith

#print axioms sweep_to_stateD

end Lip

/-! ## 2. Covariance -/

section Cov

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **A conditional covariance bound in the costs**: `V l` is continuous and non-negative, and for
continuous `f`, `g` whose fibres at `l` are `a`- and `b`-Lipschitz in the cost of `l`,
`|P(f g) − P f · P g| ≤ a b V l` at that configuration.

DERIVED: `0` the sign. -/
def CondCovD (S : Spec Ω Lk) (d : Lk → Ω → Ω → ℝ) (V : Lk → (Lk → Ω) → ℝ) : Prop :=
  (∀ l, Continuous (V l)) ∧ (∀ l W, 0 ≤ V l W) ∧
  ∀ l {f g : (Lk → Ω) → ℝ}, Continuous f → Continuous g → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
    ∀ W : Lk → Ω, (∀ x y, |f (Function.update W l x) - f (Function.update W l y)| ≤ a * d l x y) →
      (∀ x y, |g (Function.update W l x) - g (Function.update W l y)| ≤ b * d l x y) →
      |S.P l (fun V => f V * g V) W - S.P l f W * S.P l g W| ≤ a * b * V l W

/-- **Costs at most `Dm` give the bound with `V = Dm²`** (`DobrushinUnbounded.Spec.condCov_le` on a
vector that is `a Dm` at `l` and the range of `f` elsewhere). This covers the total-variation sites.

DERIVED: `2` the power. -/
theorem condCovD_of_diam (S : Spec Ω Lk) {d : Lk → Ω → Ω → ℝ} {Dm : ℝ}
    (hd0 : ∀ l a b, 0 ≤ d l a b) (hD : ∀ l a b, d l a b ≤ Dm) :
    CondCovD S d (fun _ _ => Dm ^ 2) := by
  refine ⟨fun _ => continuous_const, fun _ _ => sq_nonneg _, ?_⟩
  intro l f g hf hg a b ha hb W hfL hgL
  obtain ⟨Bf, hBf⟩ := exists_abs_le hf
  obtain ⟨Bg, hBg⟩ := exists_abs_le hg
  -- the kernel at `l` reads `f` only on the fibre at `W`; replace `f`, `g` by fibre-constant-elsewhere copies
  set f' : (Lk → Ω) → ℝ := fun V => f (Function.update W l (V l)) with hf'
  set g' : (Lk → Ω) → ℝ := fun V => g (Function.update W l (V l)) with hg'
  have hu : Continuous (fun V : Lk → Ω => Function.update W l (V l)) :=
    continuous_const.update l (continuous_apply l)
  have hf'c : Continuous f' := hf.comp hu
  have hg'c : Continuous g' := hg.comp hu
  have hosc : ∀ (F : (Lk → Ω) → ℝ) (c : ℝ), 0 ≤ c →
      (∀ x y, |F (Function.update W l x) - F (Function.update W l y)| ≤ c * d l x y) →
      OscLe (fun V => F (Function.update W l (V l))) (fun k => if k = l then c * Dm else 0) := by
    intro F c hc hFL V k x
    by_cases hk : k = l
    · subst hk
      show |F (Function.update W k (Function.update V k x k)) - F (Function.update W k (V k))|
        ≤ if k = k then c * Dm else 0
      rw [if_pos rfl, Function.update_self]
      exact (hFL x (V k)).trans (mul_le_mul_of_nonneg_left (hD _ _ _) hc)
    · show |F (Function.update W l (Function.update V k x l)) - F (Function.update W l (V l))|
        ≤ if k = l then c * Dm else 0
      rw [if_neg hk, Function.update_of_ne (Ne.symm hk), sub_self, abs_zero]
  have hc := S.condCov_le l hf'c hg'c (hosc f a ha hfL) (hosc g b hb hgL) W
  rw [if_pos rfl, if_pos rfl] at hc
  have e1 : S.P l (fun V => f' V * g' V) W = S.P l (fun V => f V * g V) W :=
    S.fibre_eq l (cmul hf'c hg'c) (cmul hf hg) W fun x => by
      show f (Function.update W l (Function.update W l x l))
          * g (Function.update W l (Function.update W l x l))
        = f (Function.update W l x) * g (Function.update W l x)
      rw [Function.update_self]
  have e2 : S.P l f' W = S.P l f W := S.fibre_eq l hf'c hf W fun x => by
    show f (Function.update W l (Function.update W l x l)) = f (Function.update W l x)
    rw [Function.update_self]
  have e3 : S.P l g' W = S.P l g W := S.fibre_eq l hg'c hg W fun x => by
    show g (Function.update W l (Function.update W l x l)) = g (Function.update W l x)
    rw [Function.update_self]
  rw [e1, e2, e3] at hc
  calc _ ≤ a * Dm * (b * Dm) := hc
    _ = a * b * Dm ^ 2 := by ring

#print axioms condCovD_of_diam

/-- **One kernel in the covariance**: replacing `f` by `P l f` in `σ(f g)` costs at most
`v_f(l) v_g(l) σ(V l)`.

DERIVED: no numeral. -/
theorem cov_stepD {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {d : Lk → Ω → Ω → ℝ} {V : Lk → (Lk → Ω) → ℝ} (hV : CondCovD S d V) (l : Lk)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipD d f vf) (hvg : LipD d g vg) :
    |ex σ (fun W => f W * g W) - ex σ (fun W => S.P l f W * g W)| ≤ vf l * vg l * ex σ (V l) := by
  have hPf := S.cont l hf
  have hPg := S.cont l hg
  have i1 := ex_P hσ l (cmul hf hg)
  have i2 := ex_P hσ l (cmul hPf hg)
  have e2 : S.P l (fun W => S.P l f W * g W) = fun W => S.P l f W * S.P l g W :=
    funext fun W => S.pull l hPf hg (fun V x => S.upd l f V x) W
  rw [e2] at i2
  rw [← i1, ← i2, ← ex_sub σ (S.cont l (cmul hf hg)) (cmul hPf hPg)]
  have hb := abs_ex_le_ex σ (csub (S.cont l (cmul hf hg)) (cmul hPf hPg))
    (csmul (vf l * vg l) (hV.1 l))
    fun W => hV.2.2 l hf hg (hvf.1 l) (hvg.1 l) W (hvf.fibre W l) (hvg.fibre W l)
  rw [ex_const_mul σ _ (hV.1 l)] at hb
  exact hb

#print axioms cov_stepD

/-- **The covariance telescope**: if `σ(V l) ≤ M` wherever `v_g(l) ≠ 0`, then along any list `L`,
`|σ(f g) − σ((sweep L f) g)| ≤ oscCost C (M v_g) L v_f`.

DERIVED: `0` the cost of the empty run and the vanishing `v_g`. -/
theorem cov_runD {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {V : Lk → (Lk → Ω) → ℝ}
    (hV : CondCovD S d V) {C : Lk → Lk → ℝ} (hC : DInfl S d C) (hC0 : ∀ l k, 0 ≤ C l k)
    {g : (Lk → Ω) → ℝ} (hg : Continuous g) {vg : Lk → ℝ} (hvg : LipD d g vg) {M : ℝ}
    (hM : ∀ l, vg l ≠ 0 → ex σ (V l) ≤ M) :
    ∀ (L : List Lk) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipD d f v →
      |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L f W * g W)|
        ≤ oscCost C (fun l => vg l * M) L v
  | [], f, _, v, _ => by
      show |ex σ (fun W => f W * g W) - ex σ (fun W => f W * g W)| ≤ 0
      simp
  | l :: L, f, hf, v, hv => by
      have h1 := cov_stepD hσ hV l hf hg hv hvg
      have h1' : v l * vg l * ex σ (V l) ≤ v l * (vg l * M) := by
        by_cases h0 : vg l = 0
        · rw [h0]; simp
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hM l h0) (hvg.1 l)) (hv.1 l)
      have h2 := cov_runD hσ hd0 hV hC hC0 hg hvg hM L (S.cont l hf) (lip_stepD hd0 hC hC0 hf hv l)
      show |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L (S.P l f) W * g W)|
        ≤ v l * (vg l * M) + oscCost C (fun l => vg l * M) L (oscStep C l v)
      calc |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L (S.P l f) W * g W)|
          ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => S.P l f W * g W)|
            + |ex σ (fun W => S.P l f W * g W)
              - ex σ (fun W => sweepS S L (S.P l f) W * g W)| := abs_sub_le _ _ _
        _ ≤ v l * (vg l * M) + oscCost C (fun l => vg l * M) L (oscStep C l v) :=
            add_le_add (h1.trans h1') h2

#print axioms cov_runD

/-- **Dobrushin's covariance bound in the costs, for a weighted row.** For an invariant state, influence
`C ≥ 0` with plain rows `≤ α < 1`, a weight `u ≥ 0` with `Σ_k C(l,k) u_k ≤ α u_l`, `v_g ≤ V_g u`, and
`σ(V l) ≤ M` wherever `v_g(l) ≠ 0`: `|σ(f g) − σ f σ g| ≤ M V_g/(1 − α) · Σ_k u_k v_f(k)`.

DERIVED: `0` the sign of `α`, `M` and the limit of `αⁿ`; `1` the bound on `α`. -/
theorem cov_le_weightedD {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hDm : 0 ≤ Dm)
    (hD : ∀ l a b, d l a b ≤ Dm) {V : Lk → (Lk → Ω) → ℝ} (hV : CondCovD S d V) {C : Lk → Lk → ℝ} (hC : DInfl S d C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {u : Lk → ℝ} (hu : ∀ k, 0 ≤ u k) (hwr : ∀ l, ∑ k, C l k * u k ≤ α * u l)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipD d f vf) (hvg : LipD d g vg) {Vg M : ℝ} (hVg : 0 ≤ Vg) (hM0 : 0 ≤ M)
    (hw : ∀ k, vg k ≤ Vg * u k) (hM : ∀ l, vg l ≠ 0 → ex σ (V l) ≤ M) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g| ≤ M * Vg / (1 - α) * ∑ k, u k * vf k := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  obtain ⟨B, hB⟩ := exists_abs_le hg
  have hα1' : 0 < 1 - α := by linarith
  have hvf0 : ∀ k, 0 ≤ vf k := hvf.1
  have hS0 : 0 ≤ ∑ k, vf k := Finset.sum_nonneg fun k _ => hvf0 k
  have hw' : ∀ k, vg k * M ≤ M * Vg * u k := fun k => by
    have := mul_le_mul_of_nonneg_right (hw k) hM0
    linarith
  have hn : ∀ n : ℕ, |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ M * Vg / (1 - α) * ∑ k, u k * vf k + α ^ n * (∑ k, vf k) * Dm * B := by
    intro n
    have h1 := cov_runD hσ hd0 hV hC hC0 hg hvg hM (rep L n) hf hvf
    have h2 := cost_leU hC0 hα1.le hu hwr (mul_nonneg hM0 hVg) hw' (rep L n) vf hvf0
    have h3 : oscCost C (fun l => vg l * M) (rep L n) vf
        ≤ M * Vg / (1 - α) * ∑ k, u k * vf k := by
      have e : M * Vg / (1 - α) * ∑ k, u k * vf k = M * Vg * (∑ k, u k * vf k) / (1 - α) := by
        ring
      rw [e, le_div_iff₀ hα1']
      linarith
    have hc : Continuous (sweepS S (rep L n) f) := continuous_sweepS S _ hf
    have hT : ∀ W, |(sweepS S (rep L n) f W - ex σ f) * g W| ≤ α ^ n * (∑ k, vf k) * Dm * B := by
      intro W
      have h := sweep_to_stateD hσ hd0 hDm hD hC hC0 hrow hα0 hα1.le hL n ⟨f, hf⟩ hvf W
      rw [sweepS_rep] at h
      rw [abs_mul, ex_mk σ hf]
      exact mul_le_mul h (hB W) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (pow_nonneg hα0 n) hS0) hDm)
    have e : ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g
        = ex σ (fun W => (sweepS S (rep L n) f W - ex σ f) * g W) := by
      have e1 : (fun W => (sweepS S (rep L n) f W - ex σ f) * g W)
          = fun W => sweepS S (rep L n) f W * g W - ex σ f * g W :=
        funext fun W => by ring
      rw [e1, ex_sub σ (F := fun W => sweepS S (rep L n) f W * g W)
        (G := fun W => ex σ f * g W) (cmul hc hg) (csmul _ hg),
        ex_const_mul σ _ hg]
    have h4 : |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g|
        ≤ α ^ n * (∑ k, vf k) * Dm * B := by
      rw [e]
      exact abs_ex_le σ (cmul (csubc hc (ex σ f)) hg) hT
    calc |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
        ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S (rep L n) f W * g W)|
          + |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith [h1.trans h3]
  have ht : Tendsto (fun n : ℕ => M * Vg / (1 - α) * ∑ k, u k * vf k + α ^ n * (∑ k, vf k) * Dm * B)
      atTop (𝓝 (M * Vg / (1 - α) * ∑ k, u k * vf k + 0 * (∑ k, vf k) * Dm * B)) :=
    ((((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const _).mul_const _).mul_const
      _).const_add _
  have hle := ge_of_tendsto' ht hn
  simpa using hle

#print axioms cov_le_weightedD

/-- **Spatial decay in the costs under a weighted row.** For a site distance `D` (zero on the diagonal,
triangle inequality), `0 < θ ≤ 1`, `Σ_k C(l,k)/θ^{D(l,k)} ≤ α < 1`: if `g` has vector `≤ V_g` on `B` and
`0` off it, `σ(V l) ≤ M` on `B`, and `f` reads only sites `D`-farther than `dd` from `B`, then
`|σ(f g) − σ f σ g| ≤ M V_g/(1 − α) · θ^{dd+1} Σ_k v_f(k)` (weight `θ^{dist(·, B)}`, as
`ObserverEnergyCellCondW.cov_spatialWW`).

DERIVED: `0` the sign and the vectors off the supports; `1` the bound on `θ` and the step beyond `dd`. -/
theorem cov_spatialD {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hDm : 0 ≤ Dm)
    (hD : ∀ l a b, d l a b ≤ Dm) {V : Lk → (Lk → Ω) → ℝ} (hV : CondCovD S d V) {C : Lk → Lk → ℝ} (hC : DInfl S d C)
    (hC0 : ∀ l k, 0 ≤ C l k) (Dst : Lk → Lk → ℕ) (hD0 : ∀ l, Dst l l = 0)
    (hDt : ∀ a b c, Dst a c ≤ Dst a b + Dst b c) {α θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hwrow : ∀ l, ∑ k, C l k / θ ^ Dst l k ≤ α)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipD d f vf) (hvg : LipD d g vg) (B : Finset Lk) {Vg M : ℝ} (hVg : 0 ≤ Vg)
    (hM0 : 0 ≤ M) (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg)
    (hM : ∀ l ∈ B, ex σ (V l) ≤ M) (dd : ℕ) (hfar : ∀ k, vf k ≠ 0 → ∀ b ∈ B, dd < Dst k b) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g| ≤ M * Vg / (1 - α) * (θ ^ (dd + 1) * ∑ k, vf k) := by
  obtain ⟨ψ, hψd⟩ : ∃ ψ : Lk → ℕ, ∀ k,
      ψ k = if h : B.Nonempty then B.inf' h (fun b => Dst k b) else dd + 1 := ⟨_, fun _ => rfl⟩
  have hψ : ∀ l k, ψ l ≤ ψ k + Dst l k := by
    intro l k
    rw [hψd l, hψd k]
    by_cases h : B.Nonempty
    · rw [dif_pos h, dif_pos h]
      obtain ⟨b, hb, hbk⟩ := Finset.exists_mem_eq_inf' h (fun b => Dst k b)
      rw [hbk]
      calc B.inf' h (fun b => Dst l b) ≤ Dst l b := Finset.inf'_le _ hb
        _ ≤ Dst l k + Dst k b := hDt l k b
        _ = Dst k b + Dst l k := add_comm _ _
    · rw [dif_neg h, dif_neg h]
      omega
  have hψB : ∀ k ∈ B, ψ k = 0 := by
    intro k hk
    rw [hψd k, dif_pos ⟨k, hk⟩]
    have h := Finset.inf'_le (fun b => Dst k b) hk
    rw [hD0 k] at h
    omega
  have hψfar : ∀ k, vf k ≠ 0 → dd + 1 ≤ ψ k := by
    intro k hk
    rw [hψd k]
    by_cases h : B.Nonempty
    · rw [dif_pos h]
      exact Finset.le_inf' h _ fun b hb => hfar k hk b hb
    · rw [dif_neg h]
  have hθ0' : 0 ≤ θ := hθ0.le
  have hterm : ∀ l k, C l k * θ ^ ψ k ≤ C l k / θ ^ Dst l k * θ ^ ψ l := by
    intro l k
    have hpow : θ ^ ψ k * θ ^ Dst l k ≤ θ ^ ψ l := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hθ0' hθ1 (hψ l k)
    have hp : 0 < θ ^ Dst l k := pow_pos hθ0 _
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]
    calc C l k * θ ^ ψ k * θ ^ Dst l k = C l k * (θ ^ ψ k * θ ^ Dst l k) := by ring
      _ ≤ C l k * θ ^ ψ l := mul_le_mul_of_nonneg_left hpow (hC0 l k)
  have hwr : ∀ l, ∑ k, C l k * θ ^ ψ k ≤ α * θ ^ ψ l := by
    intro l
    calc ∑ k, C l k * θ ^ ψ k ≤ ∑ k, C l k / θ ^ Dst l k * θ ^ ψ l :=
          Finset.sum_le_sum fun k _ => hterm l k
      _ = (∑ k, C l k / θ ^ Dst l k) * θ ^ ψ l := by rw [Finset.sum_mul]
      _ ≤ α * θ ^ ψ l := mul_le_mul_of_nonneg_right (hwrow l) (pow_nonneg hθ0' _)
  have hrow : ∀ l, ∑ k, C l k ≤ α := by
    intro l
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hwrow l)
    have hp : 0 < θ ^ Dst l k := pow_pos hθ0 _
    rw [le_div_iff₀ hp]
    exact mul_le_of_le_one_right (hC0 l k) (pow_le_one₀ hθ0' hθ1)
  have hw : ∀ k, vg k ≤ Vg * θ ^ ψ k := by
    intro k
    by_cases hk : k ∈ B
    · rw [hψB k hk, pow_zero, mul_one]
      exact hgV k
    · rw [hgB k hk]
      exact mul_nonneg hVg (pow_nonneg hθ0' _)
  have hM' : ∀ l, vg l ≠ 0 → ex σ (V l) ≤ M := fun l hl =>
    hM l (by by_contra h; exact hl (hgB l h))
  have h := cov_le_weightedD hσ hd0 hDm hD hV hC hC0 hrow hα0 hα1 (fun k => pow_nonneg hθ0' (ψ k)) hwr
    hf hg hvf hvg hVg hM0 hw hM'
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg (mul_nonneg hM0 hVg) (by linarith)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : vf k = 0
  · rw [hk]; simp
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0' hθ1 (hψfar k hk)) (hvf.1 k)

#print axioms cov_spatialD

end Cov

end MassGap.DobrushinMixed
