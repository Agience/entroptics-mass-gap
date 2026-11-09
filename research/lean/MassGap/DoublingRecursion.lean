import Mathlib

/-!
# MassGap.DoublingRecursion — the four-dimensional box-doubling recursion and its gap consequence

A partition-function test on one 4-torus that bounds the second transfer eigenvalue on every
dyadically larger torus. The two-dimensional version is Proposition `prop:trace-doubling` of
OpenAI, *The canonical massive continuum limit of the two-dimensional O(3) model*, preprint,
October 4 2026, github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/The-canonical-massive-continuum-limit-of-the-two-dimensional-O3-model-October-4-2026
(`build/sections/trace.tex`): "If `Δ_β(n,w) ≤ 2^{-10}`, then, for every `k ≥ 0`,
`Δ_β(2^k n, 2^k w) ≤ 64^{-1} 2^{-2^k}`." Everything below is proved here; nothing is cited as a
hypothesis.

## Part 1: purity squaring for a nonnegative spectrum

`powSum s w m = ∑ wᵢ^m` is `Tr Kᵐ` for a positive operator with eigenvalues `w` (finite family).
`defect s w m = 2 log Tr Kᵐ − log Tr K²ᵐ`. With `i₀` a top eigenvalue (`Top`):

* `excited_le` — the excited weight `∑_{i≠i₀} (wᵢ/w_{i₀})^m ≤ exp(defect) − 1`;
* `defect_nonneg` — `0 ≤ defect`;
* `defect_double_le` — `defect(2m) ≤ 2·excited²`;
* `defect_squaring` — `defect m ≤ 1/4 → defect (2m) ≤ 4·(defect m)²`;
* `ratio_pow_le` — `defect m ≤ 1/4 → (w_j/w_{i₀})^m ≤ 2·defect m` for every other `j`.

## Part 2: the recursion on `{0,1,2}⁴` corners

`x : Pt → ℝ` is `log Z` on the torus with sides `2^{v_μ} n_μ`. `p x μ v = 2x(v) − x(v+e_μ)`,
`Δ x v = 16x(v) − x(v+𝟙)`. `Positive x` holds the two facts Part 1 supplies in each direction:
`p ≥ 0`, and squaring below `1/4`.

* `rec_zero` — `Δ x 0 ≤ 1/108 → Δ x 𝟙 ≤ 3740·(Δ x 0)²`. The constant is
  `4·(8·1 + 4·3² + 2·9² + 27²) = 3740`; the threshold is `27·Δ ≤ 1/4`.
* `rec` — the same at every base corner.
* `iterate` — `3740·Δ(0) ≤ 1/2 → ∀ k, 0 ≤ Δ(k𝟙) ∧ 3740·Δ(k𝟙) ≤ (1/2)^(2^k)`.
* `p_le_Delta` — `8·p x 0 v ≤ Δ x v`.

## Part 3: the gap

`SpectralRep x` says each one-direction doubling of `x` is realised by a finite nonnegative
spectrum. `positive_of_rep` turns it into `Positive x`. `gap` then gives, on the torus of
corner `k`, with `m = 2^k·n` transfer steps in direction 0:
`(w_j/w_{i₀})^n ≤ 1/2` for every non-top eigenvalue, i.e. `λ₂/λ₁ ≤ 2^{-1/n}` at every
circumference `2^k n`, uniformly in `k`, once `Δ ≤ 1/7480` on the first torus.

What the Wilson SU(N) application supplies outside this file: `Z = Tr_{H_inv}(Tᵐ)` with `T` the
Lüscher/Osterwalder–Seiler transfer matrix restricted to gauge-invariant states, positive and
trace class, in each of the four lattice directions. `SpectralRep` here is for finite spectra.
-/

namespace MassGap.DoublingRecursion

open Finset Real

/-! ## Part 1 -/

section Purity

variable {ι : Type} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)

/-- `∑ wᵢ^m`, the trace of `Kᵐ` for a nonnegative spectrum `w`. -/
noncomputable def powSum (m : ℕ) : ℝ := ∑ i ∈ s, w i ^ m

/-- `2 log Tr Kᵐ − log Tr K²ᵐ`. -/
noncomputable def defect (m : ℕ) : ℝ := 2 * log (powSum s w m) - log (powSum s w (2 * m))

/-- The excited trace relative to the top eigenvalue. -/
noncomputable def excited (i₀ : ι) (m : ℕ) : ℝ := (∑ i ∈ s.erase i₀, w i ^ m) / w i₀ ^ m

/-- `i₀` carries the largest eigenvalue, which is positive, and the spectrum is nonnegative. -/
structure Top (i₀ : ι) : Prop where
  mem : i₀ ∈ s
  pos : 0 < w i₀
  nonneg : ∀ i ∈ s, 0 ≤ w i
  le_top : ∀ i ∈ s, w i ≤ w i₀

variable {s w}

theorem powSum_split {i₀ : ι} (h : Top s w i₀) (m : ℕ) :
    powSum s w m = w i₀ ^ m + ∑ i ∈ s.erase i₀, w i ^ m :=
  (Finset.add_sum_erase s (fun i => w i ^ m) h.mem).symm

theorem erase_nonneg {i₀ : ι} (h : Top s w i₀) (m : ℕ) : 0 ≤ ∑ i ∈ s.erase i₀, w i ^ m :=
  Finset.sum_nonneg fun i hi => pow_nonneg (h.nonneg i (Finset.mem_of_mem_erase hi)) m

omit [DecidableEq ι] in
theorem top_pow_pos {i₀ : ι} (h : Top s w i₀) (m : ℕ) : 0 < w i₀ ^ m := pow_pos h.pos m

theorem powSum_pos {i₀ : ι} (h : Top s w i₀) (m : ℕ) : 0 < powSum s w m := by
  rw [powSum_split h]; linarith [top_pow_pos h m, erase_nonneg h m]

omit [DecidableEq ι] in
/-- `Tr K²ᵐ ≤ λ₁ᵐ · Tr Kᵐ`. -/
theorem powSum_double_le {i₀ : ι} (h : Top s w i₀) (m : ℕ) :
    powSum s w (2 * m) ≤ w i₀ ^ m * powSum s w m := by
  unfold powSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [two_mul, pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h.nonneg i hi) (h.le_top i hi) m)
    (pow_nonneg (h.nonneg i hi) m)

/-- The excited part squares: `∑' w^{2m} ≤ (∑' w^m)²`. -/
theorem erase_double_le {i₀ : ι} (h : Top s w i₀) (m : ℕ) :
    ∑ i ∈ s.erase i₀, w i ^ (2 * m) ≤ (∑ i ∈ s.erase i₀, w i ^ m) ^ 2 := by
  rw [sq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hw : 0 ≤ w i := h.nonneg i (Finset.mem_of_mem_erase hi)
  rw [two_mul, pow_add]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun i => w i ^ m)
      (fun j hj => pow_nonneg (h.nonneg j (Finset.mem_of_mem_erase hj)) m) hi)
    (pow_nonneg hw m)

theorem excited_nonneg {i₀ : ι} (h : Top s w i₀) (m : ℕ) : 0 ≤ excited s w i₀ m :=
  div_nonneg (erase_nonneg h m) (top_pow_pos h m).le

theorem one_add_excited {i₀ : ι} (h : Top s w i₀) (m : ℕ) :
    1 + excited s w i₀ m = powSum s w m / w i₀ ^ m := by
  have ha := (top_pow_pos h m).ne'
  rw [powSum_split h, excited]; field_simp

theorem excited_le {i₀ : ι} (h : Top s w i₀) (m : ℕ) :
    excited s w i₀ m ≤ exp (defect s w m) - 1 := by
  have ha := top_pow_pos h m
  have hP := powSum_pos h m
  have hQ := powSum_pos h (2 * m)
  have hlog : log (powSum s w m / w i₀ ^ m) ≤ defect s w m := by
    rw [log_div hP.ne' ha.ne', defect]
    have : log (powSum s w (2 * m)) ≤ log (w i₀ ^ m * powSum s w m) :=
      log_le_log hQ (powSum_double_le h m)
    rw [log_mul ha.ne' hP.ne'] at this
    linarith
  have h1 : powSum s w m / w i₀ ^ m ≤ exp (defect s w m) := by
    calc powSum s w m / w i₀ ^ m = exp (log (powSum s w m / w i₀ ^ m)) :=
          (exp_log (div_pos hP ha)).symm
      _ ≤ exp (defect s w m) := exp_le_exp.mpr hlog
  linarith [one_add_excited h m]

theorem defect_nonneg {i₀ : ι} (h : Top s w i₀) (m : ℕ) : 0 ≤ defect s w m := by
  have h1 := excited_le h m
  have h2 := excited_nonneg h m
  exact one_le_exp_iff.mp (by linarith)

theorem defect_double_le {i₀ : ι} (h : Top s w i₀) (m : ℕ) :
    defect s w (2 * m) ≤ 2 * excited s w i₀ m ^ 2 := by
  set a := w i₀ ^ m with ha_def
  set e := excited s w i₀ m with he_def
  have ha := top_pow_pos h m
  have he0 := excited_nonneg h m
  have hQ := powSum_pos h (2 * m)
  have hR := powSum_pos h (2 * (2 * m))
  -- `Tr K²ᵐ ≤ a²(1 + e²)`
  have hT : ∑ i ∈ s.erase i₀, w i ^ m = e * a := by
    simp only [he_def, ha_def, excited]; field_simp
  have hQle : powSum s w (2 * m) ≤ a ^ 2 * (1 + e ^ 2) := by
    rw [powSum_split h (2 * m)]
    have h2 := erase_double_le h m
    rw [hT] at h2
    have : w i₀ ^ (2 * m) = a ^ 2 := by rw [ha_def, ← pow_mul, mul_comm]
    rw [this]; nlinarith
  -- `Tr K⁴ᵐ ≥ a⁴`
  have hRge : a ^ 4 ≤ powSum s w (2 * (2 * m)) := by
    have : w i₀ ^ (2 * (2 * m)) = a ^ 4 := by
      rw [ha_def, ← pow_mul]; ring_nf
    rw [← this]
    exact Finset.single_le_sum (f := fun i => w i ^ (2 * (2 * m)))
      (fun j hj => pow_nonneg (h.nonneg j hj) _) h.mem
  have h1e : 0 < 1 + e ^ 2 := by positivity
  have hsq : powSum s w (2 * m) ^ 2 ≤ powSum s w (2 * (2 * m)) * (1 + e ^ 2) ^ 2 := by
    calc powSum s w (2 * m) ^ 2 ≤ (a ^ 2 * (1 + e ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hQ.le hQle 2
      _ = a ^ 4 * (1 + e ^ 2) ^ 2 := by ring
      _ ≤ powSum s w (2 * (2 * m)) * (1 + e ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hRge (by positivity)
  have hl := log_le_log (by positivity) hsq
  rw [log_pow, log_mul hR.ne' (by positivity), log_pow] at hl
  have hlog1 : log (1 + e ^ 2) ≤ e ^ 2 := by
    have := log_le_sub_one_of_pos h1e; linarith
  unfold defect
  push_cast at hl
  linarith

theorem excited_le_of_small {i₀ : ι} (h : Top s w i₀) (m : ℕ) (hd : defect s w m ≤ 1 / 4) :
    excited s w i₀ m ≤ 4 / 3 * defect s w m := by
  have hd0 := defect_nonneg h m
  have hexp := exp_bound_div_one_sub_of_interval hd0 (by linarith)
  have hb : 1 / (1 - defect s w m) ≤ 1 + 4 / 3 * defect s w m := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith [excited_le h m]

theorem defect_squaring {i₀ : ι} (h : Top s w i₀) (m : ℕ) (hd : defect s w m ≤ 1 / 4) :
    defect s w (2 * m) ≤ 4 * defect s w m ^ 2 := by
  have h1 := defect_double_le h m
  have h2 := excited_le_of_small h m hd
  have h3 := excited_nonneg h m
  have : excited s w i₀ m ^ 2 ≤ (4 / 3 * defect s w m) ^ 2 := pow_le_pow_left₀ h3 h2 2
  nlinarith

theorem ratio_pow_le {i₀ : ι} (h : Top s w i₀) (m : ℕ) (hd : defect s w m ≤ 1 / 4)
    {j : ι} (hj : j ∈ s) (hji : j ≠ i₀) : (w j / w i₀) ^ m ≤ 2 * defect s w m := by
  have ha := top_pow_pos h m
  have hle : w j ^ m ≤ ∑ i ∈ s.erase i₀, w i ^ m :=
    Finset.single_le_sum (f := fun i => w i ^ m)
      (fun k hk => pow_nonneg (h.nonneg k (Finset.mem_of_mem_erase hk)) m)
      (Finset.mem_erase.mpr ⟨hji, hj⟩)
  have h1 : (w j / w i₀) ^ m ≤ excited s w i₀ m := by
    rw [div_pow, excited]; exact div_le_div_of_nonneg_right hle ha.le
  have h2 := excited_le_of_small h m hd
  have h3 := defect_nonneg h m
  linarith

end Purity

/-! ## Part 2 -/

/-- A corner `v`: the torus with sides `2^{v_μ} n_μ`. -/
abbrev Pt := Fin 4 → ℕ

/-- Unit vectors. -/
def E : Fin 4 → Pt := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- The diagonal step `𝟙`. DERIVED: `𝟙` the unit step `1` in each of the `4` directions. -/
def one : Pt := ![1, 1, 1, 1]

/-- One-direction doubling defect. -/
def p (x : Pt → ℝ) (μ : Fin 4) (v : Pt) : ℝ := 2 * x v - x (v + E μ)

/-- Full doubling defect. DERIVED: `16 = 2⁴`, the one-direction factor `2` of `p` in each of the `4`
directions of the diagonal step `𝟙`. -/
def Δ (x : Pt → ℝ) (v : Pt) : ℝ := 16 * x v - x (v + one)

/-- Positivity of the transfer matrix in every direction, in the two forms the recursion uses. -/
structure Positive (x : Pt → ℝ) : Prop where
  nonneg : ∀ μ v, 0 ≤ p x μ v
  sq : ∀ μ v, p x μ v ≤ 1 / 4 → p x μ (v + E μ) ≤ 4 * p x μ v ^ 2

variable {x : Pt → ℝ}

theorem nn (hx : Positive x) (μ : Fin 4) (v u : Pt) (h : v + E μ = u) :
    0 ≤ 2 * x v - x u := by
  have := hx.nonneg μ v; rw [p, h] at this; exact this

theorem sqr (hx : Positive x) (μ : Fin 4) (v u t : Pt) (h1 : v + E μ = u) (h2 : u + E μ = t)
    (hs : 2 * x v - x u ≤ 1 / 4) : 2 * x u - x t ≤ 4 * (2 * x v - x u) ^ 2 := by
  have := hx.sq μ v
  simp only [p, h1, h2] at this
  exact this hs

/-- The raising step: `p_μ(c+2e_ν) = 2p_μ(c+e_ν) − 2p_ν(c+e_ν) + p_ν(c+e_μ+e_ν)`, and the last
term squares. -/
theorem step (hx : Positive x) (μ ν : Fin 4) (cμ cν cμν cνν cμνν : Pt)
    (h3 : cν + E μ = cμν) (h4 : cμ + E ν = cμν) (h5 : cν + E ν = cνν)
    (h6 : cμν + E ν = cμνν) (h7 : cνν + E μ = cμνν) {B : ℝ} (hB : B ≤ 1 / 4)
    (hA : 2 * x cν - x cμν ≤ B) (hC : 2 * x cμ - x cμν ≤ B) :
    2 * x cνν - x cμνν ≤ 3 * B := by
  have n1 := nn hx ν cν cνν h5
  have n2 := nn hx ν cμ cμν h4
  have s1 := sqr hx ν cμ cμν cμνν h4 h6 (by linarith)
  have : (2 * x cμ - x cμν) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ n2 hC 2
  have _ := h3; have _ := h7
  nlinarith

theorem rec_zero (hx : Positive x) (hD : Δ x ![0, 0, 0, 0] ≤ 1 / 108) :
    Δ x ![1, 1, 1, 1] ≤ 3740 * Δ x ![0, 0, 0, 0] ^ 2 := by
  have e00 : (![0, 0, 0, 0] : Pt) + one = ![1, 1, 1, 1] := by decide
  have e11 : (![1, 1, 1, 1] : Pt) + one = ![2, 2, 2, 2] := by decide
  simp only [Δ, e00, e11] at hD ⊢
  set D := 16 * x ![0, 0, 0, 0] - x ![1, 1, 1, 1] with hDdef
  -- nonnegativity along four telescoping paths
  have a1 := nn hx 1 ![0, 0, 0, 0] ![0, 1, 0, 0] (by decide)
  have a2 := nn hx 2 ![0, 1, 0, 0] ![0, 1, 1, 0] (by decide)
  have a3 := nn hx 3 ![0, 1, 1, 0] ![0, 1, 1, 1] (by decide)
  have a4 := nn hx 0 ![0, 1, 1, 1] ![1, 1, 1, 1] (by decide)
  have b1 := nn hx 0 ![0, 0, 0, 0] ![1, 0, 0, 0] (by decide)
  have b2 := nn hx 2 ![1, 0, 0, 0] ![1, 0, 1, 0] (by decide)
  have b3 := nn hx 3 ![1, 0, 1, 0] ![1, 0, 1, 1] (by decide)
  have b4 := nn hx 1 ![1, 0, 1, 1] ![1, 1, 1, 1] (by decide)
  have c2 := nn hx 1 ![1, 0, 0, 0] ![1, 1, 0, 0] (by decide)
  have c3 := nn hx 3 ![1, 1, 0, 0] ![1, 1, 0, 1] (by decide)
  have c4 := nn hx 2 ![1, 1, 0, 1] ![1, 1, 1, 1] (by decide)
  have d3 := nn hx 2 ![1, 1, 0, 0] ![1, 1, 1, 0] (by decide)
  have d4 := nn hx 3 ![1, 1, 1, 0] ![1, 1, 1, 1] (by decide)
  have hD0 : 0 ≤ D := by linarith
  -- base bounds (`j = 0`)
  have B1 : 2 * x ![0, 1, 1, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B2 : 2 * x ![1, 0, 1, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B3 : 2 * x ![1, 1, 0, 1] - x ![1, 1, 1, 1] ≤ D := by linarith
  have B4 : 2 * x ![1, 1, 1, 0] - x ![1, 1, 1, 1] ≤ D := by linarith
  -- raising steps
  have S1 : 2 * x ![2, 0, 1, 1] - x ![2, 1, 1, 1] ≤ 3 * D :=
    step hx 1 0 ![0, 1, 1, 1] ![1, 0, 1, 1] ![1, 1, 1, 1] ![2, 0, 1, 1] ![2, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) B2 B1
  have S2 : 2 * x ![2, 1, 0, 1] - x ![2, 1, 1, 1] ≤ 3 * D :=
    step hx 2 0 ![0, 1, 1, 1] ![1, 1, 0, 1] ![1, 1, 1, 1] ![2, 1, 0, 1] ![2, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) B3 B1
  have S3 : 2 * x ![2, 2, 0, 1] - x ![2, 2, 1, 1] ≤ 3 * (3 * D) :=
    step hx 2 1 ![2, 0, 1, 1] ![2, 1, 0, 1] ![2, 1, 1, 1] ![2, 2, 0, 1] ![2, 2, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) S2 S1
  have S4 : 2 * x ![2, 1, 1, 0] - x ![2, 1, 1, 1] ≤ 3 * D :=
    step hx 3 0 ![0, 1, 1, 1] ![1, 1, 1, 0] ![1, 1, 1, 1] ![2, 1, 1, 0] ![2, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) B4 B1
  have S6 : 2 * x ![2, 2, 1, 0] - x ![2, 2, 1, 1] ≤ 3 * (3 * D) :=
    step hx 3 1 ![2, 0, 1, 1] ![2, 1, 1, 0] ![2, 1, 1, 1] ![2, 2, 1, 0] ![2, 2, 1, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) S4 S1
  have S7 : 2 * x ![2, 2, 2, 0] - x ![2, 2, 2, 1] ≤ 3 * (3 * (3 * D)) :=
    step hx 3 2 ![2, 2, 0, 1] ![2, 2, 1, 0] ![2, 2, 1, 1] ![2, 2, 2, 0] ![2, 2, 2, 1]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by linarith) S6 S3
  -- nonnegativity of the four squared quantities
  have m1 := nn hx 1 ![2, 0, 1, 1] ![2, 1, 1, 1] (by decide)
  have m2 := nn hx 2 ![2, 2, 0, 1] ![2, 2, 1, 1] (by decide)
  have m3 := nn hx 3 ![2, 2, 2, 0] ![2, 2, 2, 1] (by decide)
  -- final squarings along the path 0,1,2,3 from 𝟙
  have q0 := sqr hx 0 ![0, 1, 1, 1] ![1, 1, 1, 1] ![2, 1, 1, 1] (by decide) (by decide)
    (by linarith)
  have q1 := sqr hx 1 ![2, 0, 1, 1] ![2, 1, 1, 1] ![2, 2, 1, 1] (by decide) (by decide)
    (by linarith)
  have q2 := sqr hx 2 ![2, 2, 0, 1] ![2, 2, 1, 1] ![2, 2, 2, 1] (by decide) (by decide)
    (by linarith)
  have q3 := sqr hx 3 ![2, 2, 2, 0] ![2, 2, 2, 1] ![2, 2, 2, 2] (by decide) (by decide)
    (by linarith)
  have r0 : (2 * x ![0, 1, 1, 1] - x ![1, 1, 1, 1]) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ a4 B1 2
  have r1 : (2 * x ![2, 0, 1, 1] - x ![2, 1, 1, 1]) ^ 2 ≤ (3 * D) ^ 2 :=
    pow_le_pow_left₀ m1 S1 2
  have r2 : (2 * x ![2, 2, 0, 1] - x ![2, 2, 1, 1]) ^ 2 ≤ (3 * (3 * D)) ^ 2 :=
    pow_le_pow_left₀ m2 S3 2
  have r3 : (2 * x ![2, 2, 2, 0] - x ![2, 2, 2, 1]) ^ 2 ≤ (3 * (3 * (3 * D))) ^ 2 :=
    pow_le_pow_left₀ m3 S7 2
  nlinarith

/-- Shift of the base corner. -/
def shift (x : Pt → ℝ) (a : Pt) : Pt → ℝ := fun v => x (a + v)

theorem positive_shift (hx : Positive x) (a : Pt) : Positive (shift x a) where
  nonneg μ v := by
    have := hx.nonneg μ (a + v); simpa [p, shift, add_assoc] using this
  sq μ v h := by
    have := hx.sq μ (a + v) (by simpa [p, shift, add_assoc] using h)
    simpa [p, shift, add_assoc] using this

theorem zero_pt : (![0, 0, 0, 0] : Pt) = 0 := by decide

theorem Δ_shift (a : Pt) : Δ (shift x a) ![0, 0, 0, 0] = Δ x a := by
  simp [Δ, shift, zero_pt]

theorem Δ_shift_one (a : Pt) : Δ (shift x a) ![1, 1, 1, 1] = Δ x (a + one) := by
  simp only [Δ, shift, add_assoc]; rfl

theorem rec (hx : Positive x) (a : Pt) (hD : Δ x a ≤ 1 / 108) :
    Δ x (a + one) ≤ 3740 * Δ x a ^ 2 := by
  have := rec_zero (positive_shift hx a) (by rwa [Δ_shift])
  rwa [Δ_shift_one, Δ_shift] at this

theorem p_le_Δ_zero (hx : Positive x) : 8 * p x 0 ![0, 0, 0, 0] ≤ Δ x ![0, 0, 0, 0] := by
  have e00 : (![0, 0, 0, 0] : Pt) + one = ![1, 1, 1, 1] := by decide
  have b1 := nn hx 0 ![0, 0, 0, 0] ![1, 0, 0, 0] (by decide)
  have c2 := nn hx 1 ![1, 0, 0, 0] ![1, 1, 0, 0] (by decide)
  have d3 := nn hx 2 ![1, 1, 0, 0] ![1, 1, 1, 0] (by decide)
  have d4 := nn hx 3 ![1, 1, 1, 0] ![1, 1, 1, 1] (by decide)
  have e0 : (![0, 0, 0, 0] : Pt) + E 0 = ![1, 0, 0, 0] := by decide
  simp only [Δ, p, e00, e0]
  linarith

theorem p_le_Δ (hx : Positive x) (a : Pt) : 8 * p x 0 a ≤ Δ x a := by
  have := p_le_Δ_zero (positive_shift hx a)
  rw [Δ_shift] at this
  have hp : p (shift x a) 0 ![0, 0, 0, 0] = p x 0 a := by
    simp [p, shift, zero_pt]
  rwa [hp] at this

theorem Δ_nonneg (hx : Positive x) (a : Pt) : 0 ≤ Δ x a := by
  have := p_le_Δ hx a
  have := hx.nonneg 0 a
  linarith

/-- The diagonal corner `k𝟙`. -/
def corner (k : ℕ) : Pt := fun _ => k

theorem corner_succ (k : ℕ) : corner (k + 1) = corner k + one := by
  funext i; fin_cases i <;> rfl

theorem iterate (hx : Positive x) (h0 : 3740 * Δ x (corner 0) ≤ 1 / 2) :
    ∀ k, 3740 * Δ x (corner k) ≤ (1 / 2) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hk0 := Δ_nonneg hx (corner k)
    have hhalf : ((1 : ℝ) / 2) ^ (2 ^ k) ≤ 1 / 2 := by
      have := pow_le_pow_of_le_one (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
        (Nat.one_le_two_pow (n := k))
      simpa using this
    have hsmall : Δ x (corner k) ≤ 1 / 108 := by linarith
    have hr := rec hx (corner k) hsmall
    rw [corner_succ]
    have hsq : (3740 * Δ x (corner k)) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ih 2
    have : ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 = (1 / 2) ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    nlinarith

/-! ## Part 3 -/

/-- Every one-direction doubling of `x` is realised by a finite nonnegative spectrum:
`x v = log Tr Kᵐ`, `x (v+e_μ) = log Tr K²ᵐ`, `x (v+2e_μ) = log Tr K⁴ᵐ`. -/
def SpectralRep (x : Pt → ℝ) : Prop :=
  ∀ μ v, ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → ℝ) (i₀ : ι) (m : ℕ),
    Top s w i₀ ∧ x v = log (powSum s w m) ∧ x (v + E μ) = log (powSum s w (2 * m)) ∧
      x (v + E μ + E μ) = log (powSum s w (2 * (2 * m)))

theorem positive_of_rep (hx : SpectralRep x) : Positive x where
  nonneg μ v := by
    obtain ⟨ι, _, s, w, i₀, m, ht, h1, h2, -⟩ := hx μ v
    have := defect_nonneg ht m
    rw [p, h1, h2]; unfold defect at this; linarith
  sq μ v h := by
    obtain ⟨ι, _, s, w, i₀, m, ht, h1, h2, h3⟩ := hx μ v
    have hp : p x μ v = defect s w m := by rw [p, h1, h2]; rfl
    have hp2 : p x μ (v + E μ) = defect s w (2 * m) := by rw [p, h2, h3]; rfl
    rw [hp] at h ⊢; rw [hp2]
    exact defect_squaring ht m h

/-- The gap. If `Δ ≤ 1/7480` on the first torus, then on the torus of every corner `k`, any
spectrum realising the direction-0 doubling with `m = 2^k·n` steps has `(w_j/w_{i₀})^n ≤ 1/2`
for every non-top eigenvalue: `λ₂/λ₁ ≤ 2^{-1/n}`, uniformly in `k`. -/
theorem gap (hx : Positive x) (h0 : Δ x (corner 0) ≤ 1 / 7480) (k n : ℕ)
    {ι : Type} [DecidableEq ι] {s : Finset ι} {w : ι → ℝ} {i₀ : ι} (ht : Top s w i₀)
    (h1 : x (corner k) = log (powSum s w (2 ^ k * n)))
    (h2 : x (corner k + E 0) = log (powSum s w (2 * (2 ^ k * n))))
    {j : ι} (hj : j ∈ s) (hji : j ≠ i₀) : (w j / w i₀) ^ n ≤ 1 / 2 := by
  have hit := iterate hx (by linarith) k
  have hpd : p x 0 (corner k) = defect s w (2 ^ k * n) := by rw [p, h1, h2]; rfl
  have h8 := p_le_Δ hx (corner k)
  have hhalf : ((1 : ℝ) / 2) ^ (2 ^ k) ≤ 1 / 2 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := k))
    simpa using this
  have hpos : 0 ≤ ((1 : ℝ) / 2) ^ (2 ^ k) := by positivity
  have hd : defect s w (2 ^ k * n) ≤ 1 / 4 := by rw [← hpd]; linarith
  have hr := ratio_pow_le ht (2 ^ k * n) hd hj hji
  have hr0 : 0 ≤ w j / w i₀ := div_nonneg (ht.nonneg j hj) ht.pos.le
  have hbound : ((w j / w i₀) ^ n) ^ (2 ^ k) ≤ ((1 : ℝ) / 2) ^ (2 ^ k) := by
    rw [← pow_mul, Nat.mul_comm n]
    have : 2 * defect s w (2 ^ k * n) ≤ (1 / 2) ^ (2 ^ k) := by rw [← hpd]; linarith
    linarith
  exact (pow_le_pow_iff_left₀ (pow_nonneg hr0 n) (by norm_num) (by positivity)).mp hbound

#print axioms defect_squaring
#print axioms ratio_pow_le
#print axioms rec
#print axioms iterate
#print axioms positive_of_rep
#print axioms gap

end MassGap.DoublingRecursion
