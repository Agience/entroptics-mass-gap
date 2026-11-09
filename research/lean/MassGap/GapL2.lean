import Mathlib
import MassGap.ApertureGap

/-!
# MassGap.GapL2 — maximal correlation: tensorisation over cells, stacking along time, and the doubling defect

The far input `ApertureGap.FixedDiffraction` asks for `cyc(2n) ≥ e^{−ε} cyc(n)²` at the physical side, uniformly in
the zoom. The Birkhoff (sup) cross ratio of a slab is additive over independent transverse cells
(`StrongPhys.PhysStrong` is false in 4D for that reason). This module builds the functional that does not grow
with the cross-section: the L²(stationary) contraction on mean-zero functions, the maximal correlation.

Everything is finite-dimensional and eigen-free. A state space is a `Fintype`; a kernel is a real matrix `K`;
`π` is a stationary probability vector.

## 1. Maximal correlation (defined)

* `mean π g = Σ π g`, `nsq π g = Σ π g²`, `ip π f g = Σ π f g`.
* `Markov π K`: `π ≥ 0`, `Σ π = 1`, `K ≥ 0`, rows of `K` sum to `1`, `π K = π`.
* `Contr π K r`: `‖K g‖² ≤ r² ‖g‖²` for every mean-zero `g` (norms in `L²(π)`), `r ≥ 0`.
* `Corr π K r`: `⟨f, K g⟩² ≤ r² ‖f‖² ‖g‖²` for all mean-zero `f, g`: the maximal-correlation bound `ρ ≤ r`.
* `maxCorr π K = sInf {r | Corr π K r}`, the maximal correlation `ρ(K)` itself.
* `corr_iff_contr`: for a Markov pair the two are the same statement (`f = K g` is mean-zero by stationarity).
* `corr_maxCorr`: the infimum is attained, `Corr π K (maxCorr π K)`; `maxCorr_le_one`.

## 2. Tensorisation and stacking (proved)

* `Contr.kron` (Witsenhausen, upper half): for Markov pairs on two independent cells,
  `Contr π₁ K₁ r₁`, `Contr π₂ K₂ r₂ ⇒ Contr (π₁ ⊗ π₂) (K₁ ⊗ K₂) (max r₁ r₂)`. Proof: split `g` into its
  fibre mean `ḡ(x) = E_{π₂} g(x, ·)` and the fibre fluctuation `k = g − ḡ`. Then `‖Kg‖² = ‖K₁ ḡ‖² + V` with
  `V ≤ Σ_{x'} π₁(x') ‖K₂ k(x', ·)‖²` (Jensen in the `K₁` row, then stationarity of `π₁`), so
  `‖Kg‖² ≤ r₁² ‖ḡ‖² + r₂² ‖k‖² ≤ max(r₁, r₂)² ‖g‖²`. The cells combine by `max`, not by a sum.
* `cells`: `N` independent copies of one cell, `Contr π K r ⇒ Contr (π^{⊗N}) (K^{⊗N}) r` for every `N`.
  `maxCorr_cells`: `ρ(K^{⊗N}) ≤ ρ(K)`. **The number of cells does not enter.**
* `Contr.mul` / `maxCorr_mul_le`: `ρ(K₁ K₂) ≤ ρ(K₁) ρ(K₂)` (stacking slabs along the time direction);
  `Contr.pow`: `Contr π (K^n) (rⁿ)`.
* `Contr.perturb`: a kernel within `ε` of a contraction by `r` in the relative norm on mean-zero functions,
  `‖(K − K₀) g‖ ≤ ε ‖g‖`, contracts by `r + ε`. `contr_of_cellInput`: a slab kernel within `ε` of the
  product of `N` cells of maximal correlation `ρ_c` has `Contr … (ρ_c + ε)`, at every `N`.

## 3. The link to the doubling defect (proved)

`trc K = Σ_x K(x, x)`; for the Doob-normalised transfer matrix `trc(Kⁿ) = cyc(n)/λ₀ⁿ = 1 + τ_n`, and the
doubling ratio `cyc(2n)/cyc(n)²` is unchanged by the normalisation.

* `diag_sub_pi`: `Kⁿ(x, x) − π(x) = π(x) ⟨u_x, Kⁿ u_x⟩` with `u_x = δ_x/π(x) − 1` (mean-zero,
  `‖u_x‖² = 1/π(x) − 1`).
* `trace_pow_sub_one_le`: `|trc(Kⁿ) − 1| ≤ (|Ω| − 1) rⁿ`: excited weight at most multiplicity times `ρⁿ`.
* `trace_transport` (reversible `K`): `|trc(K^{2m+q}) − 1| ≤ s (trc(K^{2m}) − 1)` whenever
  `Contr π (K^q) s`. With `q = j p` and `Contr π (K^p) t` (one slab of `p` lattice steps), `s = t^j`:
  `τ_{2m+jp} ≤ t^j τ_{2m}`. The gap clause (`t`, one slab) carries the level count (`τ_{2m}`, one reference
  length) to every longer length.
* `one_le_trace_even`: `trc(K^{2m}) ≥ 1` (reversible).
* `doubling_of_excited`: `|T₁ − 1| ≤ δ`, `T₂ ≥ 1 ⇒ e^{−2δ} T₁² ≤ T₂`, the `FixedDiffraction` form.
* `doubling_global`, `doubling_transport`, `doubling_slab`: the far-input inequality
  `e^{−ε} trc(Kⁿ)² ≤ trc(K^{2n})` with `ε = 2(|Ω| − 1)ρⁿ`, resp. `ε = 2 t^j τ_{2m}` at `n = 2m + jp`.
* `doubling_cells`: for `N` independent copies of a reversible cell with rate `r`,
  `e^{−2N(|Ω_c| − 1)rⁿ} trc(Kⁿ)² ≤ trc(K^{2n})` (`KN_pow`, `trc_KN`: `trc((K^{⊗N})ⁿ) = trc(Kⁿ)^N`). The gap
  enters by `max`, the level count by sum: with `N = (L/ℓ₀)^d` cells this is the `C L^d e^{−m n}` shape of
  `FixedDiffraction`, `d` the number of transverse directions.

## 4. Unit tests (proved)

* `contr_K2_cells`: the two-state cell `K2 a` (stay probability `a`) has `L²` rate `|2a − 1|`, and `N` independent
  copies have the same rate at every `N`.
* `not_crossRatio_K2_cells`: for `1/2 < a < 1` and every `t < 1`, some number of cells violates
  `ApertureGap.CrossRatio … t`: the Birkhoff cross ratio of `N` cells tends to `1`. This is the mechanism that
  makes `StrongPhys.PhysStrong` false, and the `L²` rate does not have it.

The numerical checks (2D Ising strip, `O(2)` clock slabs, 4D lattice Gaussian massive and massless) are
`research/code/gap_l2_checks.py`.

## 5. What remains: the single-cell input

`CellInput π K_c ρ_c ε N K` is the finite form: the slab kernel `K` on `N` cells is Markov for the product
measure and within `ε` (relative operator norm on mean-zero functions) of `K_c^{⊗N}`, with `Contr π K_c ρ_c`.
`contr_of_cellInput` gives `Contr … (ρ_c + ε)` at every `N`. For the Wilson slab of physical thickness `ℓ₀` it
asks: (a) one physical cell of size `ℓ₀` has maximal correlation across the slab at most `ρ_c < 1` uniformly in
`β`; (b) the transverse coupling between cells, measured in the relative `L²` norm on `1⊥`, is at most `ε` with
`ρ_c + ε < 1`, uniformly in `β` and in the number of cells. Neither (a) nor (b) is proved here. Two features of (b)
are structural, not technical: the triangle inequality over the `N` transverse bonds gives `ε` growing with `N`, so
(b) needs a bound in which far-apart bond terms do not add (a Dobrushin-type row-sum condition); and the stationary
measure of the coupled slab is not the product measure, whose density ratio to it grows exponentially in `N`.
-/

namespace GapL2

open Finset Matrix
open scoped Kronecker

section Basic

variable {α : Type*} [Fintype α]

/-- The mean of `g` under `π`. -/
def mean (π g : α → ℝ) : ℝ := ∑ x, π x * g x

/-- The squared `L²(π)` norm. -/
def nsq (π g : α → ℝ) : ℝ := ∑ x, π x * g x ^ 2

/-- The `L²(π)` inner product. -/
def ip (π f g : α → ℝ) : ℝ := ∑ x, π x * f x * g x

/-- Rows sum to one. -/
def Row (K : Matrix α α ℝ) : Prop := ∀ x, ∑ y, K x y = 1

/-- `π` is stationary for `K`. -/
def Stat (π : α → ℝ) (K : Matrix α α ℝ) : Prop := ∀ y, ∑ x, π x * K x y = π y

/-- Detailed balance. -/
def Rev (π : α → ℝ) (K : Matrix α α ℝ) : Prop := ∀ x y, π x * K x y = π y * K y x

/-- A Markov pair: a stochastic kernel with a stationary probability vector. -/
structure Markov (π : α → ℝ) (K : Matrix α α ℝ) : Prop where
  pi_nonneg : ∀ x, 0 ≤ π x
  pi_sum : ∑ x, π x = 1
  nonneg : ∀ x y, 0 ≤ K x y
  row : Row K
  stat : Stat π K

/-- **The `L²(π)` contraction on mean-zero functions**: `‖K g‖ ≤ r ‖g‖` for `E_π g = 0`. -/
def Contr (π : α → ℝ) (K : Matrix α α ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ g : α → ℝ, mean π g = 0 → nsq π (K *ᵥ g) ≤ r ^ 2 * nsq π g

/-- **The maximal-correlation bound** `ρ(K) ≤ r`: `⟨f, K g⟩² ≤ r² ‖f‖² ‖g‖²` for mean-zero `f, g`. -/
def Corr (π : α → ℝ) (K : Matrix α α ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ f g : α → ℝ, mean π f = 0 → mean π g = 0 →
    ip π f (K *ᵥ g) ^ 2 ≤ r ^ 2 * nsq π f * nsq π g

/-- **The maximal correlation** `ρ(K)`. -/
noncomputable def maxCorr (π : α → ℝ) (K : Matrix α α ℝ) : ℝ := sInf {r | Corr π K r}

theorem mulVec_apply' (K : Matrix α α ℝ) (g : α → ℝ) (x : α) :
    (K *ᵥ g) x = ∑ y, K x y * g y := rfl

theorem nsq_eq_ip (π g : α → ℝ) : nsq π g = ip π g g :=
  Finset.sum_congr rfl fun x _ => by ring

theorem nsq_nonneg {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) (g : α → ℝ) : 0 ≤ nsq π g :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hπ x) (sq_nonneg _)

/-- The variance split `E u² = (E u)² + E (u − E u)²` for weights summing to one. -/
theorem var_split {ι : Type*} (s : Finset ι) (w u : ι → ℝ) (hw : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * u i ^ 2 =
      (∑ i ∈ s, w i * u i) ^ 2 + ∑ i ∈ s, w i * (u i - ∑ j ∈ s, w j * u j) ^ 2 := by
  have h : ∀ m : ℝ, ∑ i ∈ s, w i * (u i - m) ^ 2
      = ∑ i ∈ s, w i * u i ^ 2 - 2 * m * ∑ i ∈ s, w i * u i + m ^ 2 * ∑ i ∈ s, w i := by
    intro m
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, hw]; ring

/-- Jensen for the square: `(Σ w u)² ≤ Σ w u²` for a probability vector `w`. -/
theorem sq_avg_le {ι : Type*} (s : Finset ι) (w u : ι → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (hw : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i * u i) ^ 2 ≤ ∑ i ∈ s, w i * u i ^ 2 := by
  rw [var_split s w u hw]
  have := Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw0 i hi) (sq_nonneg (u i - ∑ j ∈ s, w j * u j))
  linarith

theorem nsq_split {π : α → ℝ} (hs : ∑ x, π x = 1) (u : α → ℝ) :
    nsq π u = mean π u ^ 2 + nsq π (fun y => u y - mean π u) :=
  var_split _ π u hs

/-- Weighted Cauchy–Schwarz. -/
theorem ip_sq_le {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) (f g : α → ℝ) :
    ip π f g ^ 2 ≤ nsq π f * nsq π g := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => Real.sqrt (π x) * f x)
    (fun x => Real.sqrt (π x) * g x)
  have e1 : ∀ x, Real.sqrt (π x) * f x * (Real.sqrt (π x) * g x) = π x * f x * g x := fun x => by
    rw [show Real.sqrt (π x) * f x * (Real.sqrt (π x) * g x) = Real.sqrt (π x) ^ 2 * f x * g x by ring,
      Real.sq_sqrt (hπ x)]
  have e2 : ∀ (x) (v : α → ℝ), (Real.sqrt (π x) * v x) ^ 2 = π x * v x ^ 2 := fun x v => by
    rw [mul_pow, Real.sq_sqrt (hπ x)]
  simp only [e1, e2] at h
  exact h

theorem mean_eq_ip (π g : α → ℝ) : mean π g = ip π g (fun _ => 1) :=
  Finset.sum_congr rfl fun x _ => by ring

theorem mean_mulVec {π : α → ℝ} {K : Matrix α α ℝ} (h : Stat π K) (g : α → ℝ) :
    mean π (K *ᵥ g) = mean π g := by
  unfold mean
  simp only [mulVec_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← h y, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem mean_sub_const {π : α → ℝ} (hs : ∑ x, π x = 1) (u : α → ℝ) (c : ℝ) :
    mean π (fun y => u y - c) = mean π u - c := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]

theorem mulVec_sub_const {K : Matrix α α ℝ} (hr : Row K) (u : α → ℝ) (c : ℝ) (y : α) :
    (K *ᵥ fun y' => u y' - c) y = (K *ᵥ u) y - c := by
  simp only [mulVec_apply', mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hr y, one_mul]

/-- A Markov kernel is an `L²(π)` contraction on all functions. -/
theorem nsq_mulVec_le {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (g : α → ℝ) :
    nsq π (K *ᵥ g) ≤ nsq π g := by
  unfold nsq
  calc ∑ x, π x * (K *ᵥ g) x ^ 2 ≤ ∑ x, π x * ∑ y, K x y * g y ^ 2 := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (M.pi_nonneg x)
        rw [mulVec_apply']
        exact sq_avg_le _ _ _ (fun y _ => M.nonneg x y) (M.row x)
    _ = ∑ y, π y * g y ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← M.stat y, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

theorem Contr.of_markov {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : Contr π K 1 :=
  ⟨zero_le_one, fun g _ => by rw [one_pow, one_mul]; exact nsq_mulVec_le M g⟩

theorem Contr.mono {π : α → ℝ} {K : Matrix α α ℝ} {r s : ℝ} (h : Contr π K r) (hrs : r ≤ s)
    (hπ : ∀ x, 0 ≤ π x) : Contr π K s := by
  refine ⟨h.1.trans hrs, fun g hg => (h.2 g hg).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.1 hrs 2) (nsq_nonneg hπ g)

/-! ### Maximal correlation and the contraction are the same statement -/

theorem Corr.of_contr {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (h : Contr π K r) : Corr π K r := by
  refine ⟨h.1, fun f g _ hg => ?_⟩
  calc ip π f (K *ᵥ g) ^ 2 ≤ nsq π f * nsq π (K *ᵥ g) := ip_sq_le hπ _ _
    _ ≤ nsq π f * (r ^ 2 * nsq π g) := mul_le_mul_of_nonneg_left (h.2 g hg) (nsq_nonneg hπ f)
    _ = r ^ 2 * nsq π f * nsq π g := by ring

theorem Contr.of_corr {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hs : Stat π K) (h : Corr π K r) : Contr π K r := by
  refine ⟨h.1, fun g hg => ?_⟩
  have hm : mean π (K *ᵥ g) = 0 := by rw [mean_mulVec hs, hg]
  have h1 := h.2 _ g hm hg
  rw [← nsq_eq_ip π (K *ᵥ g)] at h1
  rcases (nsq_nonneg hπ (K *ᵥ g)).lt_or_eq with hp | hz
  · have h2 : nsq π (K *ᵥ g) * nsq π (K *ᵥ g) ≤ nsq π (K *ᵥ g) * (r ^ 2 * nsq π g) := by
      nlinarith [h1]
    exact le_of_mul_le_mul_left h2 hp
  · rw [← hz]; exact mul_nonneg (sq_nonneg r) (nsq_nonneg hπ g)

/-- **Maximal correlation is the `L²` contraction on `1⊥`.** -/
theorem corr_iff_contr {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (M : Markov π K) :
    Corr π K r ↔ Contr π K r :=
  ⟨Contr.of_corr M.pi_nonneg M.stat, Corr.of_contr M.pi_nonneg⟩

theorem corr_one {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : Corr π K 1 :=
  Corr.of_contr M.pi_nonneg (Contr.of_markov M)

theorem maxCorr_le {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (h : Corr π K r) : maxCorr π K ≤ r :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ h

theorem maxCorr_nonneg {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : 0 ≤ maxCorr π K :=
  le_csInf ⟨1, corr_one M⟩ fun _ hs => hs.1

theorem maxCorr_le_one {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : maxCorr π K ≤ 1 :=
  maxCorr_le (corr_one M)

/-- **The infimum is attained**: `ρ(K)` is itself a maximal-correlation bound. -/
theorem corr_maxCorr {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : Corr π K (maxCorr π K) := by
  refine ⟨maxCorr_nonneg M, fun f g hf hg => ?_⟩
  have hall : ∀ r, Corr π K r → ip π f (K *ᵥ g) ^ 2 ≤ r ^ 2 * (nsq π f * nsq π g) := fun r hr => by
    have := hr.2 f g hf hg; rw [← mul_assoc]; exact this
  rw [mul_assoc]
  have hD : 0 ≤ nsq π f * nsq π g := mul_nonneg (nsq_nonneg M.pi_nonneg f) (nsq_nonneg M.pi_nonneg g)
  by_contra hlt
  rw [not_le] at hlt
  rcases hD.lt_or_eq with hDpos | hD0
  · have hq : maxCorr π K < Real.sqrt (ip π f (K *ᵥ g) ^ 2 / (nsq π f * nsq π g)) := by
      rw [Real.lt_sqrt (maxCorr_nonneg M), lt_div_iff₀ hDpos]; exact hlt
    obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt ⟨1, corr_one M⟩ hq
    have h2 := (Real.lt_sqrt hr.1).1 hrlt
    rw [lt_div_iff₀ hDpos] at h2
    linarith [hall r hr]
  · have h3 := hall 1 (corr_one M)
    rw [← hD0, mul_zero] at h3 hlt
    linarith

theorem contr_maxCorr {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : Contr π K (maxCorr π K) :=
  (corr_iff_contr M).1 (corr_maxCorr M)

theorem maxCorr_le_of_contr {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (M : Markov π K)
    (h : Contr π K r) : maxCorr π K ≤ r :=
  maxCorr_le ((corr_iff_contr M).2 h)

end Basic

/-! ## Stacking along the time direction -/

section Stack

variable {α : Type*} [Fintype α]

theorem Row.mul {K₁ K₂ : Matrix α α ℝ} (h₁ : Row K₁) (h₂ : Row K₂) : Row (K₁ * K₂) := by
  intro x
  have h₂' : ∀ y, ∑ z, K₂ y z = 1 := h₂
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, h₂', mul_one]
  exact h₁ x

theorem Stat.mul {π : α → ℝ} {K₁ K₂ : Matrix α α ℝ} (h₁ : Stat π K₁) (h₂ : Stat π K₂) :
    Stat π (K₁ * K₂) := by
  intro z
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm, ← h₂ z]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← h₁ y, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Markov.mul {π : α → ℝ} {K₁ K₂ : Matrix α α ℝ} (M₁ : Markov π K₁) (M₂ : Markov π K₂) :
    Markov π (K₁ * K₂) where
  pi_nonneg := M₁.pi_nonneg
  pi_sum := M₁.pi_sum
  nonneg x z := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (M₁.nonneg x y) (M₂.nonneg y z)
  row := M₁.row.mul M₂.row
  stat := M₁.stat.mul M₂.stat

theorem Markov.one [DecidableEq α] {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) (hs : ∑ x, π x = 1) :
    Markov π (1 : Matrix α α ℝ) where
  pi_nonneg := hπ
  pi_sum := hs
  nonneg x y := by rw [Matrix.one_apply]; split_ifs <;> norm_num
  row x := by simp [Matrix.one_apply]
  stat y := by simp [Matrix.one_apply]

theorem Markov.pow [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) : ∀ n : ℕ, Markov π (K ^ n)
  | 0 => by rw [pow_zero]; exact Markov.one M.pi_nonneg M.pi_sum
  | n + 1 => by rw [pow_succ]; exact (M.pow n).mul M

/-- **Stacking**: `ρ(K₁ K₂) ≤ ρ(K₁) ρ(K₂)`, contraction form. -/
theorem Contr.mul {π : α → ℝ} {K₁ K₂ : Matrix α α ℝ} {r₁ r₂ : ℝ} (h₂s : Stat π K₂)
    (h₁ : Contr π K₁ r₁) (h₂ : Contr π K₂ r₂) : Contr π (K₁ * K₂) (r₁ * r₂) := by
  refine ⟨mul_nonneg h₁.1 h₂.1, fun g hg => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have hm : mean π (K₂ *ᵥ g) = 0 := by rw [mean_mulVec h₂s, hg]
  calc nsq π (K₁ *ᵥ (K₂ *ᵥ g)) ≤ r₁ ^ 2 * nsq π (K₂ *ᵥ g) := h₁.2 _ hm
    _ ≤ r₁ ^ 2 * (r₂ ^ 2 * nsq π g) := mul_le_mul_of_nonneg_left (h₂.2 g hg) (sq_nonneg _)
    _ = (r₁ * r₂) ^ 2 * nsq π g := by ring

theorem Contr.pow [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (hs : Stat π K) (h : Contr π K r) :
    ∀ n : ℕ, Contr π (K ^ n) (r ^ n)
  | 0 => ⟨by simp, fun g _ => by simp [Matrix.one_mulVec]⟩
  | n + 1 => by rw [pow_succ, pow_succ]; exact (Contr.pow hs h n).mul hs h

/-- **`ρ(K₁ K₂) ≤ ρ(K₁) ρ(K₂)`.** -/
theorem maxCorr_mul_le {π : α → ℝ} {K₁ K₂ : Matrix α α ℝ} (M₁ : Markov π K₁) (M₂ : Markov π K₂) :
    maxCorr π (K₁ * K₂) ≤ maxCorr π K₁ * maxCorr π K₂ :=
  maxCorr_le_of_contr (M₁.mul M₂) ((contr_maxCorr M₁).mul M₂.stat (contr_maxCorr M₂))

theorem maxCorr_pow_le [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (n : ℕ) :
    maxCorr π (K ^ n) ≤ maxCorr π K ^ n :=
  maxCorr_le_of_contr (M.pow n) ((contr_maxCorr M).pow M.stat n)

end Stack

/-! ## Tensorisation over independent cells -/

section Tensor

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The product measure on two cells. -/
def piProd (π₁ : α → ℝ) (π₂ : β → ℝ) : α × β → ℝ := fun p => π₁ p.1 * π₂ p.2

theorem kron_mulVec_apply (K₁ : Matrix α α ℝ) (K₂ : Matrix β β ℝ) (g : α × β → ℝ) (x : α) (y : β) :
    ((K₁ ⊗ₖ K₂) *ᵥ g) (x, y) = ∑ x', K₁ x x' * (K₂ *ᵥ fun y' => g (x', y')) y := by
  simp only [mulVec_apply', Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by ring

theorem nsq_prod (π₁ : α → ℝ) (π₂ : β → ℝ) (F : α × β → ℝ) :
    nsq (piProd π₁ π₂) F = ∑ x, π₁ x * nsq π₂ (fun y => F (x, y)) := by
  simp only [nsq, piProd, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem mean_prod (π₁ : α → ℝ) (π₂ : β → ℝ) (F : α × β → ℝ) :
    mean (piProd π₁ π₂) F = mean π₁ (fun x => mean π₂ (fun y => F (x, y))) := by
  simp only [mean, piProd, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem mean_sum_mul (π : β → ℝ) (c : α → ℝ) (v : α → β → ℝ) :
    mean π (fun y => ∑ x', c x' * v x' y) = ∑ x', c x' * mean π (v x') := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y _ => by ring

theorem Markov.kron {π₁ : α → ℝ} {π₂ : β → ℝ} {K₁ : Matrix α α ℝ} {K₂ : Matrix β β ℝ}
    (M₁ : Markov π₁ K₁) (M₂ : Markov π₂ K₂) : Markov (piProd π₁ π₂) (K₁ ⊗ₖ K₂) where
  pi_nonneg p := mul_nonneg (M₁.pi_nonneg _) (M₂.pi_nonneg _)
  pi_sum := by
    simp only [piProd, Fintype.sum_prod_type, ← Finset.mul_sum, M₂.pi_sum, mul_one, M₁.pi_sum]
  nonneg p q := by
    rw [Matrix.kroneckerMap_apply]; exact mul_nonneg (M₁.nonneg _ _) (M₂.nonneg _ _)
  row p := by
    simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, ← Finset.mul_sum, M₂.row p.2,
      mul_one, M₁.row p.1]
  stat q := by
    simp only [piProd, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
    calc ∑ a, ∑ b, π₁ a * π₂ b * (K₁ a q.1 * K₂ b q.2)
        = ∑ a, π₁ a * K₁ a q.1 * ∑ b, π₂ b * K₂ b q.2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = π₁ q.1 * π₂ q.2 := by rw [M₂.stat, ← Finset.sum_mul, M₁.stat]

/-- **Witsenhausen tensorisation (upper half)**: independent cells combine by `max`. -/
theorem Contr.kron {π₁ : α → ℝ} {π₂ : β → ℝ} {K₁ : Matrix α α ℝ} {K₂ : Matrix β β ℝ} {r₁ r₂ : ℝ}
    (M₁ : Markov π₁ K₁) (M₂ : Markov π₂ K₂) (h₁ : Contr π₁ K₁ r₁) (h₂ : Contr π₂ K₂ r₂) :
    Contr (piProd π₁ π₂) (K₁ ⊗ₖ K₂) (max r₁ r₂) := by
  refine ⟨le_max_of_le_left h₁.1, fun g hg => ?_⟩
  -- the fibre mean `ḡ` and the fibre fluctuation `k x = g(x, ·) − ḡ x`
  obtain ⟨gb, hgb⟩ : ∃ gb : α → ℝ, ∀ x, gb x = mean π₂ (fun y => g (x, y)) := ⟨_, fun _ => rfl⟩
  have hgb0 : mean π₁ gb = 0 := by
    rw [← hg, mean_prod]; exact Finset.sum_congr rfl fun x _ => by rw [hgb x]
  have hk0 : ∀ x, mean π₂ (fun y => g (x, y) - gb x) = 0 := fun x => by
    rw [mean_sub_const M₂.pi_sum, hgb x, sub_self]
  -- the image `G = K g`
  obtain ⟨G, hG⟩ : ∃ G, G = (K₁ ⊗ₖ K₂) *ᵥ g := ⟨_, rfl⟩
  rw [← hG]
  have hGx : ∀ x y, G (x, y) = ∑ x', K₁ x x' * (K₂ *ᵥ fun y' => g (x', y')) y := fun x y => by
    rw [hG, kron_mulVec_apply]
  -- the fibre mean of `G` is `K₁ ḡ`
  have hfm : ∀ x, mean π₂ (fun y => G (x, y)) = (K₁ *ᵥ gb) x := fun x => by
    simp only [hGx]
    rw [mean_sum_mul, mulVec_apply']
    exact Finset.sum_congr rfl fun x' _ => by rw [mean_mulVec M₂.stat, hgb x']
  -- the fibre fluctuation of `G` is `K₁` applied to `K₂ k`
  have hdev : ∀ x y, G (x, y) - (K₁ *ᵥ gb) x
      = ∑ x', K₁ x x' * (K₂ *ᵥ fun y' => g (x', y') - gb x') y := fun x y => by
    rw [hGx, mulVec_apply', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x' _ => by rw [mulVec_sub_const M₂.row, mul_sub]
  -- `F x' = ‖K₂ k(x')‖²`
  obtain ⟨F, hF⟩ : ∃ F : α → ℝ, ∀ x', F x' = nsq π₂ (K₂ *ᵥ fun y' => g (x', y') - gb x') :=
    ⟨_, fun _ => rfl⟩
  have hV : ∀ x, nsq π₂ (fun y => G (x, y) - (K₁ *ᵥ gb) x) ≤ (K₁ *ᵥ F) x := fun x => by
    calc nsq π₂ (fun y => G (x, y) - (K₁ *ᵥ gb) x)
        ≤ mean π₂ (fun y => ∑ x', K₁ x x' * (K₂ *ᵥ fun y' => g (x', y') - gb x') y ^ 2) := by
          unfold nsq mean
          refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (M₂.pi_nonneg y)
          beta_reduce
          rw [hdev]
          exact sq_avg_le _ _ _ (fun x' _ => M₁.nonneg x x') (M₁.row x)
      _ = (K₁ *ᵥ F) x := by
          rw [mean_sum_mul, mulVec_apply']
          exact Finset.sum_congr rfl fun x' _ => by rw [hF x']; rfl
  -- the two pieces
  have hsplitG : nsq (piProd π₁ π₂) G
      = nsq π₁ (K₁ *ᵥ gb) + ∑ x, π₁ x * nsq π₂ (fun y => G (x, y) - (K₁ *ᵥ gb) x) := by
    rw [nsq_prod]
    unfold nsq
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := nsq_split M₂.pi_sum (fun y => G (x, y))
    rw [hfm x] at this
    unfold nsq at this
    rw [this]; ring
  have hsplitg : nsq (piProd π₁ π₂) g
      = nsq π₁ gb + ∑ x, π₁ x * nsq π₂ (fun y => g (x, y) - gb x) := by
    rw [nsq_prod]
    unfold nsq
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := nsq_split M₂.pi_sum (fun y => g (x, y))
    rw [← hgb x] at this
    unfold nsq at this
    rw [this]; ring
  have hA : nsq π₁ (K₁ *ᵥ gb) ≤ r₁ ^ 2 * nsq π₁ gb := h₁.2 gb hgb0
  have hB : ∑ x, π₁ x * nsq π₂ (fun y => G (x, y) - (K₁ *ᵥ gb) x)
      ≤ r₂ ^ 2 * ∑ x, π₁ x * nsq π₂ (fun y => g (x, y) - gb x) := by
    calc ∑ x, π₁ x * nsq π₂ (fun y => G (x, y) - (K₁ *ᵥ gb) x)
        ≤ ∑ x, π₁ x * (K₁ *ᵥ F) x :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hV x) (M₁.pi_nonneg x)
      _ = ∑ x, π₁ x * F x := mean_mulVec M₁.stat F
      _ ≤ ∑ x, π₁ x * (r₂ ^ 2 * nsq π₂ (fun y => g (x, y) - gb x)) := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (M₁.pi_nonneg x)
          rw [hF x]; exact h₂.2 _ (hk0 x)
      _ = r₂ ^ 2 * ∑ x, π₁ x * nsq π₂ (fun y => g (x, y) - gb x) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have hA0 : 0 ≤ nsq π₁ gb := nsq_nonneg M₁.pi_nonneg gb
  have hB0 : 0 ≤ ∑ x, π₁ x * nsq π₂ (fun y => g (x, y) - gb x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (M₁.pi_nonneg x) (nsq_nonneg M₂.pi_nonneg _)
  have hr1 : r₁ ^ 2 ≤ max r₁ r₂ ^ 2 := pow_le_pow_left₀ h₁.1 (le_max_left _ _) 2
  have hr2 : r₂ ^ 2 ≤ max r₁ r₂ ^ 2 := pow_le_pow_left₀ h₂.1 (le_max_right _ _) 2
  rw [hsplitG, hsplitg]
  nlinarith [mul_le_mul_of_nonneg_right hr1 hA0, mul_le_mul_of_nonneg_right hr2 hB0]

/-- **`ρ(K₁ ⊗ K₂) ≤ max(ρ(K₁), ρ(K₂))`.** -/
theorem maxCorr_kron_le {π₁ : α → ℝ} {π₂ : β → ℝ} {K₁ : Matrix α α ℝ} {K₂ : Matrix β β ℝ}
    (M₁ : Markov π₁ K₁) (M₂ : Markov π₂ K₂) :
    maxCorr (piProd π₁ π₂) (K₁ ⊗ₖ K₂) ≤ max (maxCorr π₁ K₁) (maxCorr π₂ K₂) :=
  maxCorr_le_of_contr (M₁.kron M₂) (Contr.kron M₁ M₂ (contr_maxCorr M₁) (contr_maxCorr M₂))

/-! ### Reindexing -/

theorem Markov.reindex {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (e : β ≃ α) :
    Markov (π ∘ e) (K.submatrix e e) where
  pi_nonneg b := M.pi_nonneg (e b)
  pi_sum := (Equiv.sum_comp e π).trans M.pi_sum
  nonneg _ _ := M.nonneg _ _
  row b := (Equiv.sum_comp e (K (e b))).trans (M.row _)
  stat b' := (Equiv.sum_comp e (fun a => π a * K a (e b'))).trans (M.stat _)

theorem Contr.reindex {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (h : Contr π K r) (e : β ≃ α) :
    Contr (π ∘ e) (K.submatrix e e) r := by
  refine ⟨h.1, fun g hg => ?_⟩
  have key : ∀ u : α → ℝ, nsq (π ∘ e) (u ∘ e) = nsq π u := fun u =>
    Equiv.sum_comp e (fun a => π a * u a ^ 2)
  have keym : ∀ u : α → ℝ, mean (π ∘ e) (u ∘ e) = mean π u := fun u =>
    Equiv.sum_comp e (fun a => π a * u a)
  have hgv : g = (g ∘ e.symm) ∘ e := by funext b; simp
  have hK : K.submatrix e e *ᵥ g = (K *ᵥ (g ∘ e.symm)) ∘ e :=
    Matrix.submatrix_mulVec_equiv K g e e
  rw [hK, key]
  rw [hgv, keym] at hg
  calc nsq π (K *ᵥ (g ∘ e.symm)) ≤ r ^ 2 * nsq π (g ∘ e.symm) := h.2 _ hg
    _ = r ^ 2 * nsq (π ∘ e) g := by rw [← key (g ∘ e.symm), ← hgv]

end Tensor

/-! ## `N` independent cells: the cross-section does not enter -/

section Cells

variable {α : Type*} [Fintype α]

/-- The product measure on `N` cells. -/
def piN (π : α → ℝ) (N : ℕ) : (Fin N → α) → ℝ := fun x => ∏ i, π (x i)

/-- The product kernel on `N` cells. -/
def KN (K : Matrix α α ℝ) (N : ℕ) : Matrix (Fin N → α) (Fin N → α) ℝ := fun x x' => ∏ i, K (x i) (x' i)

/-- Split off the first cell. -/
def splitE (α : Type*) (N : ℕ) : (Fin (N + 1) → α) ≃ α × (Fin N → α) where
  toFun x := (x 0, Fin.tail x)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by simp
  right_inv p := by simp

omit [Fintype α] in
theorem piN_succ (π : α → ℝ) (N : ℕ) : piN π (N + 1) = piProd π (piN π N) ∘ splitE α N := by
  funext x
  simp [piN, piProd, splitE, Fin.prod_univ_succ, Fin.tail]

omit [Fintype α] in
theorem KN_succ (K : Matrix α α ℝ) (N : ℕ) :
    KN K (N + 1) = (K ⊗ₖ KN K N).submatrix (splitE α N) (splitE α N) := by
  funext x x'
  simp [KN, splitE, Fin.prod_univ_succ, Fin.tail, Matrix.kroneckerMap_apply]

theorem markov_zero {π : α → ℝ} {K : Matrix α α ℝ} : Markov (piN π 0) (KN K 0) where
  pi_nonneg _ := by simp [piN]
  pi_sum := by simp [piN]
  nonneg _ _ := by simp [KN]
  row _ := by simp [KN]
  stat _ := by simp [piN, KN]

theorem contr_zero {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (hr : 0 ≤ r) :
    Contr (piN π 0) (KN K 0) r := by
  refine ⟨hr, fun g hg => ?_⟩
  have h0 : KN K 0 *ᵥ g = 0 := by
    funext x
    have : (KN K 0 *ᵥ g) x = mean (piN π 0) g := by simp [mulVec_apply', KN, piN, mean]
    rw [this, hg]; rfl
  rw [h0]
  have : nsq (piN π 0) (0 : (Fin 0 → α) → ℝ) = 0 := by simp [nsq]
  rw [this]
  exact mul_nonneg (sq_nonneg r) (nsq_nonneg (fun _ => by simp [piN]) g)

/-- **`N` independent cells contract by the single-cell rate, at every `N`.** -/
theorem cells {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (M : Markov π K) (h : Contr π K r) :
    ∀ N : ℕ, Markov (piN π N) (KN K N) ∧ Contr (piN π N) (KN K N) r
  | 0 => ⟨markov_zero, contr_zero h.1⟩
  | N + 1 => by
    obtain ⟨MN, hN⟩ := cells M h N
    have M2 := (M.kron MN).reindex (splitE α N)
    have h2 := (Contr.kron M MN h hN).reindex (splitE α N)
    rw [max_self] at h2
    rw [piN_succ, KN_succ]
    exact ⟨M2, h2⟩

/-- **`ρ(K^{⊗N}) ≤ ρ(K)` for every number of cells `N`.** -/
theorem maxCorr_cells {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (N : ℕ) :
    maxCorr (piN π N) (KN K N) ≤ maxCorr π K :=
  let h := cells M (contr_maxCorr M) N
  maxCorr_le_of_contr h.1 h.2

end Cells

/-! ## Relative perturbation of a product -/

section Perturb

variable {α : Type*} [Fintype α]

theorem nsq_add (π f g : α → ℝ) : nsq π (f + g) = nsq π f + 2 * ip π f g + nsq π g := by
  simp only [nsq, ip, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **A relative `ε`-perturbation of an `r`-contraction contracts by `r + ε`.** -/
theorem Contr.perturb {π : α → ℝ} {K K₀ : Matrix α α ℝ} {r ε : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (h₀ : Contr π K₀ r) (hε : 0 ≤ ε)
    (hd : ∀ g, mean π g = 0 → nsq π (K *ᵥ g - K₀ *ᵥ g) ≤ ε ^ 2 * nsq π g) : Contr π K (r + ε) := by
  refine ⟨add_nonneg h₀.1 hε, fun g hg => ?_⟩
  have hsplit : K *ᵥ g = K₀ *ᵥ g + (K *ᵥ g - K₀ *ᵥ g) := by abel
  rw [hsplit, nsq_add]
  have hA := h₀.2 g hg
  have hB := hd g hg
  have hN := nsq_nonneg hπ g
  have hcs := ip_sq_le hπ (K₀ *ᵥ g) (K *ᵥ g - K₀ *ᵥ g)
  have hAB : nsq π (K₀ *ᵥ g) * nsq π (K *ᵥ g - K₀ *ᵥ g) ≤ (r * ε * nsq π g) ^ 2 := by
    have h1 := mul_le_mul hA hB (nsq_nonneg hπ _) (mul_nonneg (sq_nonneg r) hN)
    nlinarith [h1]
  have hip : ip π (K₀ *ᵥ g) (K *ᵥ g - K₀ *ᵥ g) ≤ r * ε * nsq π g :=
    (abs_le_of_sq_le_sq' (hcs.trans hAB) (mul_nonneg (mul_nonneg h₀.1 hε) hN)).2
  nlinarith [hip, hA, hB]

/-- **The single-scale input, finite form.** A kernel `K` on `N` cells, Markov for the product measure,
is within `ε` (relative, on mean-zero functions) of the product of `N` copies of one cell kernel `Kc`
whose `L²` contraction rate is `ρc`. -/
def CellInput (π : α → ℝ) (Kc : Matrix α α ℝ) (ρc ε : ℝ) (N : ℕ)
    (K : Matrix (Fin N → α) (Fin N → α) ℝ) : Prop :=
  Markov π Kc ∧ Contr π Kc ρc ∧ 0 ≤ ε ∧
    ∀ g, mean (piN π N) g = 0 →
      nsq (piN π N) (K *ᵥ g - KN Kc N *ᵥ g) ≤ ε ^ 2 * nsq (piN π N) g

/-- **The slab contracts by `ρc + ε` at every number of cells `N`.** -/
theorem contr_of_cellInput {π : α → ℝ} {Kc : Matrix α α ℝ} {ρc ε : ℝ} {N : ℕ}
    {K : Matrix (Fin N → α) (Fin N → α) ℝ} (h : CellInput π Kc ρc ε N K) :
    Contr (piN π N) K (ρc + ε) := by
  obtain ⟨M, hc, hε, hd⟩ := h
  have hN := cells M hc N
  exact Contr.perturb hN.1.pi_nonneg hN.2 hε hd

end Perturb

/-! ## The doubling defect -/

section Defect

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The trace. -/
def trc (K : Matrix α α ℝ) : ℝ := ∑ x, K x x

/-- The centred bump at `x`: `δ_x/π(x) − 1`. -/
noncomputable def bump (π : α → ℝ) (x : α) : α → ℝ := fun z => (if z = x then 1 / π x else 0) - 1

theorem ip_bump {π : α → ℝ} {x : α} (hx : π x ≠ 0) (v : α → ℝ) :
    ip π (bump π x) v = v x - mean π v := by
  have h : ∀ z, π z * bump π x z * v z = (if z = x then v z else 0) - π z * v z := fun z => by
    unfold bump
    split_ifs with hz
    · rw [hz, mul_sub, mul_one_div_cancel hx]; ring
    · ring
  unfold ip mean
  rw [Finset.sum_congr rfl fun z _ => h z, Finset.sum_sub_distrib]
  simp

theorem mean_bump {π : α → ℝ} {x : α} (hx : π x ≠ 0) (hs : ∑ z, π z = 1) : mean π (bump π x) = 0 := by
  rw [mean_eq_ip, ip_bump hx]
  simp [mean, hs]

theorem mulVec_bump {π : α → ℝ} {x : α} (A : Matrix α α ℝ) (hr : Row A) (z : α) :
    (A *ᵥ bump π x) z = A z x / π x - 1 := by
  unfold bump
  rw [mulVec_sub_const hr, mulVec_apply']
  congr 1
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
  simp [div_eq_mul_inv]

/-- **The diagonal of a Markov kernel through one bump**: `A(x,x) − π(x) = π(x) ⟨u_x, A u_x⟩`. -/
theorem diag_sub_pi {π : α → ℝ} {A : Matrix α α ℝ} (M : Markov π A) {x : α} (hx : 0 < π x) :
    A x x - π x = π x * ip π (bump π x) (A *ᵥ bump π x) := by
  rw [ip_bump hx.ne', mean_mulVec M.stat, mean_bump hx.ne' M.pi_sum, mulVec_bump A M.row]
  field_simp
  ring

theorem nsq_bump {π : α → ℝ} {x : α} (hx : 0 < π x) (hs : ∑ z, π z = 1) :
    π x * nsq π (bump π x) = 1 - π x := by
  rw [nsq_eq_ip, ip_bump hx.ne', mean_bump hx.ne' hs]
  simp [bump]
  field_simp

omit [DecidableEq α] in
/-- `|⟨u, A u⟩| ≤ s ‖u‖²` for mean-zero `u` and an `s`-contraction `A`. -/
theorem abs_ip_le {π : α → ℝ} {A : Matrix α α ℝ} {s : ℝ} (hπ : ∀ x, 0 ≤ π x) (h : Contr π A s)
    {u : α → ℝ} (hu : mean π u = 0) : |ip π u (A *ᵥ u)| ≤ s * nsq π u := by
  have hc := (Corr.of_contr hπ h).2 u u hu hu
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg h.1 (nsq_nonneg hπ u))
  calc ip π u (A *ᵥ u) ^ 2 ≤ s ^ 2 * nsq π u * nsq π u := hc
    _ = (s * nsq π u) ^ 2 := by ring

omit [DecidableEq α] in
theorem sum_one_sub_pi {π : α → ℝ} (hs : ∑ x, π x = 1) :
    ∑ x, (1 - π x) = (Fintype.card α : ℝ) - 1 := by
  rw [Finset.sum_sub_distrib, hs]; simp

/-- **Excited weight at most multiplicity times `rⁿ`**: `|trc(A) − 1| ≤ (|Ω| − 1) s` for a Markov
`A` that contracts mean-zero functions by `s`. -/
theorem trace_sub_one_le {π : α → ℝ} {A : Matrix α α ℝ} {s : ℝ} (M : Markov π A)
    (hπ : ∀ x, 0 < π x) (h : Contr π A s) : |trc A - 1| ≤ ((Fintype.card α : ℝ) - 1) * s := by
  have hx : ∀ x, |A x x - π x| ≤ s * (1 - π x) := fun x => by
    rw [diag_sub_pi M (hπ x), abs_mul, abs_of_pos (hπ x), ← nsq_bump (hπ x) M.pi_sum]
    have := abs_ip_le M.pi_nonneg h (mean_bump (hπ x).ne' M.pi_sum)
    nlinarith [hπ x]
  have hsum : trc A - 1 = ∑ x, (A x x - π x) := by
    rw [Finset.sum_sub_distrib, M.pi_sum]; rfl
  rw [hsum]
  calc |∑ x, (A x x - π x)| ≤ ∑ x, |A x x - π x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, s * (1 - π x) := Finset.sum_le_sum fun x _ => hx x
    _ = ((Fintype.card α : ℝ) - 1) * s := by rw [← Finset.mul_sum, sum_one_sub_pi M.pi_sum]; ring

theorem trace_pow_sub_one_le {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (M : Markov π K)
    (hπ : ∀ x, 0 < π x) (h : Contr π K r) (n : ℕ) :
    |trc (K ^ n) - 1| ≤ ((Fintype.card α : ℝ) - 1) * r ^ n :=
  trace_sub_one_le (M.pow n) hπ (h.pow M.stat n)

/-! ### Reversible kernels: the level count is transported by the gap -/

omit [DecidableEq α] in
theorem ip_mulVec_symm {π : α → ℝ} {K : Matrix α α ℝ} (hrev : Rev π K) (f g : α → ℝ) :
    ip π f (K *ᵥ g) = ip π (K *ᵥ f) g := by
  unfold ip
  simp only [mulVec_apply', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  linear_combination (f x * g y) * hrev x y

theorem ip_pow_symm {π : α → ℝ} {K : Matrix α α ℝ} (hrev : Rev π K) (f g : α → ℝ) :
    ∀ n : ℕ, ip π f ((K ^ n) *ᵥ g) = ip π ((K ^ n) *ᵥ f) g
  | 0 => by simp [Matrix.one_mulVec]
  | n + 1 => by
    rw [pow_succ, ← Matrix.mulVec_mulVec, ip_pow_symm hrev f (K *ᵥ g) n, ip_mulVec_symm hrev,
      Matrix.mulVec_mulVec, ← pow_succ', pow_succ]

/-- `A(x,x) − π(x) ≥ 0` and its square form, at an even power. -/
theorem diag_even {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K) {x : α}
    (hx : 0 < π x) (m : ℕ) :
    (K ^ (2 * m)) x x - π x = π x * nsq π ((K ^ m) *ᵥ bump π x) := by
  rw [diag_sub_pi (M.pow (2 * m)) hx, nsq_eq_ip, two_mul, pow_add, ← Matrix.mulVec_mulVec,
    ip_pow_symm hrev]

theorem one_le_trace_even {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    (hπ : ∀ x, 0 < π x) (m : ℕ) : 1 ≤ trc (K ^ (2 * m)) := by
  have h : trc (K ^ (2 * m)) - 1 = ∑ x, ((K ^ (2 * m)) x x - π x) := by
    rw [Finset.sum_sub_distrib, M.pi_sum]; rfl
  have h0 : 0 ≤ ∑ x, ((K ^ (2 * m)) x x - π x) := Finset.sum_nonneg fun x _ => by
    rw [diag_even M hrev (hπ x)]; exact mul_nonneg (hπ x).le (nsq_nonneg M.pi_nonneg _)
  linarith

/-- **Transport of the excited weight**: `|trc(K^{2m+q}) − 1| ≤ s (trc(K^{2m}) − 1)` for a reversible
Markov `K` with `Contr π (K^q) s`. -/
theorem trace_transport {π : α → ℝ} {K : Matrix α α ℝ} {s : ℝ} (M : Markov π K) (hrev : Rev π K)
    (hπ : ∀ x, 0 < π x) (m q : ℕ) (h : Contr π (K ^ q) s) :
    |trc (K ^ (2 * m + q)) - 1| ≤ s * (trc (K ^ (2 * m)) - 1) := by
  have hx : ∀ x, |(K ^ (2 * m + q)) x x - π x| ≤ s * ((K ^ (2 * m)) x x - π x) := fun x => by
    rw [diag_sub_pi (M.pow _) (hπ x), diag_even M hrev (hπ x)]
    have hpow : K ^ (2 * m + q) = K ^ m * (K ^ q * K ^ m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hpow, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ip_pow_symm hrev]
    have hv : mean π ((K ^ m) *ᵥ bump π x) = 0 := by
      rw [mean_mulVec (M.pow m).stat, mean_bump (hπ x).ne' M.pi_sum]
    have := abs_ip_le M.pi_nonneg h hv
    rw [abs_mul, abs_of_pos (hπ x)]
    nlinarith [hπ x]
  have hsum : ∀ n, trc (K ^ n) - 1 = ∑ x, ((K ^ n) x x - π x) := fun n => by
    rw [Finset.sum_sub_distrib, M.pi_sum]; rfl
  rw [hsum, hsum, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => hx x)

/-! ### The far-input form -/

/-- **`|T₁ − 1| ≤ δ` and `T₂ ≥ 1` give `e^{−2δ} T₁² ≤ T₂`.** -/
theorem doubling_of_excited {T₁ T₂ δ : ℝ} (h₁ : |T₁ - 1| ≤ δ) (h₂ : 1 ≤ T₂) :
    Real.exp (-(2 * δ)) * T₁ ^ 2 ≤ T₂ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h₁
  have hT : T₁ ^ 2 ≤ (1 + δ) ^ 2 := by
    have := abs_le.1 h₁
    exact sq_le_sq' (by linarith) (by linarith)
  have he : (1 + δ) ^ 2 ≤ Real.exp (2 * δ) := by
    have h1 : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    calc (1 + δ) ^ 2 ≤ Real.exp δ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      _ = Real.exp (2 * δ) := by rw [← Real.exp_nat_mul]; norm_num
  have hpos := Real.exp_pos (-(2 * δ))
  calc Real.exp (-(2 * δ)) * T₁ ^ 2 ≤ Real.exp (-(2 * δ)) * Real.exp (2 * δ) :=
        mul_le_mul_of_nonneg_left (hT.trans he) hpos.le
    _ = 1 := by rw [← Real.exp_add]; simp
    _ ≤ T₂ := h₂

/-- **The far-input inequality from the gap alone, with the full multiplicity**:
`e^{−2(|Ω|−1)rⁿ} trc(Kⁿ)² ≤ trc(K^{2n})`. -/
theorem doubling_global {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (M : Markov π K) (hrev : Rev π K)
    (hπ : ∀ x, 0 < π x) (h : Contr π K r) (n : ℕ) :
    Real.exp (-(2 * (((Fintype.card α : ℝ) - 1) * r ^ n))) * trc (K ^ n) ^ 2 ≤ trc (K ^ (2 * n)) :=
  doubling_of_excited (trace_pow_sub_one_le M hπ h n) (one_le_trace_even M hrev hπ n)

/-- **The far-input inequality from the gap and one level count**: at `n = 2m + q` with
`Contr π (K^q) s`, `e^{−2 s τ_{2m}} trc(Kⁿ)² ≤ trc(K^{2n})`, `τ_{2m} = trc(K^{2m}) − 1`. -/
theorem doubling_transport {π : α → ℝ} {K : Matrix α α ℝ} {s : ℝ} (M : Markov π K) (hrev : Rev π K)
    (hπ : ∀ x, 0 < π x) (m q : ℕ) (h : Contr π (K ^ q) s) :
    Real.exp (-(2 * (s * (trc (K ^ (2 * m)) - 1)))) * trc (K ^ (2 * m + q)) ^ 2
      ≤ trc (K ^ (2 * (2 * m + q))) :=
  doubling_of_excited (trace_transport M hrev hπ m q h) (one_le_trace_even M hrev hπ _)

/-- **The slab form**: one slab of `p` lattice steps with `ρ ≤ t`, stacked `j` times, carries the level
count `τ_{2m}` to `n = 2m + jp` with the weight `t^j`. -/
theorem doubling_slab {π : α → ℝ} {K : Matrix α α ℝ} {t : ℝ} (M : Markov π K) (hrev : Rev π K)
    (hπ : ∀ x, 0 < π x) (m p j : ℕ) (h : Contr π (K ^ p) t) :
    Real.exp (-(2 * (t ^ j * (trc (K ^ (2 * m)) - 1)))) * trc (K ^ (2 * m + p * j)) ^ 2
      ≤ trc (K ^ (2 * (2 * m + p * j))) := by
  have hj : Contr π (K ^ (p * j)) (t ^ j) := by
    rw [pow_mul]; exact h.pow (M.pow p).stat j
  exact doubling_transport M hrev hπ m (p * j) hj

end Defect

/-! ## The obstacle that killed `PhysStrong`, removed: a two-state cell -/

section TwoState

/-- The symmetric two-state kernel with stay probability `a`. -/
def K2 (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then a else 1 - a

/-- The uniform measure on two states. -/
noncomputable def pi2 : Fin 2 → ℝ := fun _ => 1 / 2

theorem K2_00 (a : ℝ) : K2 a 0 0 = a := by simp [K2]
theorem K2_01 (a : ℝ) : K2 a 0 1 = 1 - a := by simp [K2]
theorem K2_10 (a : ℝ) : K2 a 1 0 = 1 - a := by simp [K2]
theorem K2_11 (a : ℝ) : K2 a 1 1 = a := by simp [K2]

theorem markov_K2 {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : Markov pi2 (K2 a) where
  pi_nonneg _ := by norm_num [pi2]
  pi_sum := by simp only [pi2, Fin.sum_univ_two]; norm_num
  nonneg i j := by unfold K2; split_ifs <;> linarith
  row i := by
    fin_cases i
    · simp only [Fin.sum_univ_two, Fin.zero_eta, K2_00, K2_01]; ring
    · simp only [Fin.sum_univ_two, Fin.mk_one, K2_10, K2_11]; ring
  stat j := by
    fin_cases j
    · simp only [pi2, Fin.sum_univ_two, Fin.zero_eta, K2_00, K2_10]; ring
    · simp only [pi2, Fin.sum_univ_two, Fin.mk_one, K2_01, K2_11]; ring

/-- **One cell**: the maximal correlation of the two-state cell is at most `|2a − 1|`. -/
theorem contr_K2 (a : ℝ) : Contr pi2 (K2 a) |2 * a - 1| := by
  refine ⟨abs_nonneg _, fun g hg => ?_⟩
  have h1 : g 1 = -g 0 := by
    simp only [mean, pi2, Fin.sum_univ_two] at hg; linarith
  have e : nsq pi2 (K2 a *ᵥ g) = (2 * a - 1) ^ 2 * nsq pi2 g := by
    simp only [nsq, pi2, Fin.sum_univ_two, mulVec_apply', K2_00, K2_01, K2_10, K2_11, h1]
    ring
  rw [e, sq_abs]

/-- **`N` independent two-state cells: the `L²` rate is `|2a − 1|` at every `N`.** -/
theorem contr_K2_cells {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (N : ℕ) :
    Contr (piN pi2 N) (KN (K2 a) N) |2 * a - 1| :=
  (cells (markov_K2 h0 h1) (contr_K2 a) N).2

/-- **…while the Birkhoff cross ratio of the `N`-cell kernel tends to `1`**: for every `t < 1` some
number of cells violates `CrossRatio … t`. The sup cross ratio is additive over cells; the `L²` rate is not. -/
theorem not_crossRatio_K2_cells {a t : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) (ht : t < 1) :
    ∃ N : ℕ, ¬ MassGap.ApertureGap.CrossRatio (KN (K2 a) N) t := by
  have ha0 : 0 < a := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ((1 - a) / a) ^ 2 := ⟨_, rfl⟩
  have hq0 : 0 ≤ (1 - a) / a := div_nonneg (by linarith) ha0.le
  have hq1 : (1 - a) / a < 1 := (div_lt_one ha0).2 (by linarith)
  have hu0 : 0 ≤ u := hu ▸ sq_nonneg _
  have hu1 : u < 1 := by
    rw [hu]; nlinarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (1 - t) / 2) hu1
  refine ⟨N, fun h => ?_⟩
  have e1 : KN (K2 a) N (fun _ => 0) (fun _ => 0) = a ^ N := by simp [KN, K2_00]
  have e2 : KN (K2 a) N (fun _ => 1) (fun _ => 1) = a ^ N := by simp [KN, K2_11]
  have e3 : KN (K2 a) N (fun _ => 0) (fun _ => 1) = (1 - a) ^ N := by simp [KN, K2_01]
  have e4 : KN (K2 a) N (fun _ => 1) (fun _ => 0) = (1 - a) ^ N := by simp [KN, K2_10]
  have hc := h (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)
  rw [e1, e2, e3, e4] at hc
  have hA : 0 < a ^ N * a ^ N := mul_pos (pow_pos ha0 N) (pow_pos ha0 N)
  have hB : (1 - a) ^ N * (1 - a) ^ N = u ^ N * (a ^ N * a ^ N) := by
    rw [hu, ← pow_mul, div_pow]
    field_simp
    ring
  have hv0 : 0 ≤ u ^ N := pow_nonneg hu0 N
  have hAB : a ^ N * a ^ N - u ^ N * (a ^ N * a ^ N) ≤ t * (a ^ N * a ^ N + u ^ N * (a ^ N * a ^ N)) := by
    rw [← hB]; exact (le_abs_self _).trans hc
  have key : 1 - t ≤ u ^ N * (1 + t) := by
    by_contra hk
    rw [not_le] at hk
    have := mul_pos hA (sub_pos.2 hk)
    nlinarith
  nlinarith [mul_nonneg hv0 (by linarith : (0 : ℝ) ≤ 1 - t)]

end TwoState

/-! ## `N` independent cells: gap by `max`, level count by sum -/

section CellsDefect

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem KN_mul (A B : Matrix α α ℝ) (N : ℕ) : KN A N * KN B N = KN (A * B) N := by
  funext x z
  simp only [Matrix.mul_apply, KN]
  rw [Fintype.prod_sum (fun i a => A (x i) a * B a (z i))]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm

omit [Fintype α] in
theorem KN_one (N : ℕ) : KN (1 : Matrix α α ℝ) N = 1 := by
  funext x z
  simp only [KN, Matrix.one_apply]
  by_cases h : x = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem KN_pow (K : Matrix α α ℝ) (N : ℕ) : ∀ n : ℕ, KN K N ^ n = KN (K ^ n) N
  | 0 => by rw [pow_zero, pow_zero, KN_one]
  | n + 1 => by rw [pow_succ, KN_pow K N n, KN_mul, ← pow_succ]

omit [DecidableEq α] in
theorem trc_KN (A : Matrix α α ℝ) (N : ℕ) : trc (KN A N) = trc A ^ N := by
  simp only [trc, KN]
  rw [← Fin.prod_const, Fintype.prod_sum (fun _ a => A a a)]

/-- `|T₁| ≤ e^δ` and `T₂ ≥ 1` give `e^{−2δ} T₁² ≤ T₂`. -/
theorem doubling_of_abs_le {T₁ T₂ δ : ℝ} (h₁ : |T₁| ≤ Real.exp δ) (h₂ : 1 ≤ T₂) :
    Real.exp (-(2 * δ)) * T₁ ^ 2 ≤ T₂ := by
  have hT : T₁ ^ 2 ≤ Real.exp (2 * δ) := by
    rw [← sq_abs, show 2 * δ = (2 : ℕ) * δ by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  calc Real.exp (-(2 * δ)) * T₁ ^ 2 ≤ Real.exp (-(2 * δ)) * Real.exp (2 * δ) :=
        mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp
    _ ≤ T₂ := h₂

/-- **The far-input inequality for `N` independent cells**: the gap enters by `max` (one cell's rate `r`),
the level count by sum (the factor `N`): `e^{−2 N (|Ω_c| − 1) rⁿ} trc(Kⁿ)² ≤ trc(K^{2n})` for the `N`-cell
kernel. With `N = (L/ℓ₀)^d` cells this is the `C L^d e^{−m n}` form of `FixedDiffraction`. -/
theorem doubling_cells {π : α → ℝ} {K : Matrix α α ℝ} {r : ℝ} (M : Markov π K) (hrev : Rev π K)
    (hπ : ∀ x, 0 < π x) (h : Contr π K r) (N n : ℕ) :
    Real.exp (-(2 * (N * (((Fintype.card α : ℝ) - 1) * r ^ n)))) * trc (KN K N ^ n) ^ 2
      ≤ trc (KN K N ^ (2 * n)) := by
  rw [KN_pow, KN_pow, trc_KN, trc_KN]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((Fintype.card α : ℝ) - 1) * r ^ n := ⟨_, rfl⟩
  have hc := trace_pow_sub_one_le M hπ h n
  rw [← hδ] at hc ⊢
  have h1 : |trc (K ^ n)| ≤ Real.exp δ := by
    have := abs_le.1 hc
    have he := Real.add_one_le_exp δ
    rw [abs_le]; constructor <;> linarith
  apply doubling_of_abs_le
  · rw [abs_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 N
  · exact one_le_pow₀ (one_le_trace_even M hrev hπ n)

end CellsDefect

#print axioms doubling_cells
#print axioms contr_K2_cells
#print axioms not_crossRatio_K2_cells
#print axioms Contr.kron
#print axioms maxCorr_kron_le
#print axioms maxCorr_cells
#print axioms maxCorr_mul_le
#print axioms corr_maxCorr
#print axioms contr_of_cellInput
#print axioms trace_pow_sub_one_le
#print axioms doubling_global
#print axioms doubling_transport
#print axioms doubling_slab

end GapL2
