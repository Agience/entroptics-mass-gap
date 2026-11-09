import Mathlib
import MassGap.RelativeGap

/-!
# MassGap.ReadsSlabWilson — the box gap reads the slab, for a finite symmetric positive transfer

`RelativeGap.ReadsSlab gL S τ` asks that every `L²(π)` contraction rate `r > 0` of the slab `S m k` on
mean-zero functions bound the box gap below, `−log r / τ m ≤ gL m k`. This module proves it for the slab
built from a finite transfer matrix by its Perron vector, with `gL` the transfer-matrix gap
`−log(λ₁/λ₀)/a` per unit time. It is an identification at finite volume; it proves no gap.

## 1. Self-adjoint Markov kernels (proved)

For a Markov pair `(π, K)` with detailed balance (`GapL2.Rev`: `K` self-adjoint in `L²(π)`):

* `form_cs`: Cauchy–Schwarz for the form `⟨u, K v⟩` when it is nonnegative on mean-zero functions.
* `rayleigh_of_contr`: `Contr π K r` gives `⟨g, K g⟩ ≤ r ‖g‖²` on mean-zero `g`.
* `contr_of_rayleigh`: if `⟨g, K g⟩ ≥ 0` and `⟨g, K g⟩ ≤ c ‖g‖²` on mean-zero `g`, then `Contr π K c`
  (`‖K g‖² = ⟨g, K (K g)⟩ ≤ ⟨g, K g⟩^{1/2} ⟨K g, K (K g)⟩^{1/2}`).
* `pow_le_of_contr_pow`: for `n ≥ 1`, every rate `s` of `Kⁿ` has `maxCorr π K ^ n ≤ s`. Proof: for
  `r < maxCorr` some mean-zero `g` has `‖K g‖ > r ‖g‖`; `a_j = ‖K^j g‖²` is log-convex
  (`a_{j+1}² ≤ a_j a_{j+2}`, self-adjointness and Cauchy–Schwarz), so `a_n ≥ r^{2n} a_0`.
* `maxCorr_pow_eq`: `maxCorr π (Kⁿ) = (maxCorr π K)ⁿ` for `n ≥ 1`. The norm of a power of a self-adjoint
  operator is the power of its norm; `GapL2.maxCorr_pow_le` is the `≤` half.

## 2. The Perron (Doob) slab of a finite transfer matrix (proved)

`FinTransfer`: a finite nonempty state space `Ω`, a matrix `A` that is symmetric, entrywise `≥ 0`, and
positive semidefinite on `φ⊥` (`h ⬝ᵥ φ = 0 → 0 ≤ h ⬝ᵥ A h`), with a positive vector `φ`, `A φ = λ₀ φ`,
`λ₀ > 0`.

* `piD x = φ(x)² / Σ φ²`, `kD x y = A(x,y) φ(y) / (λ₀ φ(x))`. `markov`: `GapL2.Markov piD kD`; `rev`:
  `GapL2.Rev piD kD`.
* `lam1 = sInf {s ≥ 0 | ∀ h ⊥ φ, h ⬝ᵥ A h ≤ s (h ⬝ᵥ h)}`: the top of the Rayleigh quotient of `A` on
  `φ⊥` (Courant–Fischer for the second eigenvalue). `lam1_spec`: the infimum is a bound;
  `le_lam1_of_eigen`: every eigenvalue of `A` with an eigenvector in `φ⊥` is `≤ lam1`.
* `maxCorr_eq`: `maxCorr piD kD = lam1 / λ₀`. Under `h = φ g`, the mean is `(h ⬝ᵥ φ)/Z`, the norm
  `(h ⬝ᵥ h)/Z`, the form `(h ⬝ᵥ A h)/(Z λ₀)` (`mean_eq`, `nsq_eq`, `ip_eq`); semidefiniteness is what makes
  the contraction rate the top of the spectrum on `φ⊥` and not its largest absolute value.
* `rho_slab`: the slab of `n ≥ 1` steps, `slab n = (piD, kDⁿ)`, has
  `(slab n).rho = (lam1/λ₀)ⁿ`; `contr_slab`: that rate is a contraction rate, and every other is larger.

## 3. `ReadsSlab` (proved)

`boxGap a = −log(lam1/λ₀)/a`, the gap per unit time of one transfer step of length `a`.

* `relGap_slab`: `−log((slab n).rho)/(n a) = boxGap a` when `lam1 > 0`.
* `readsSlab_transfer`: for a family `T m k` of finite transfers, steps `n m k ≥ 1` with
  `n m k · a_k = τ m` (`a_k = FixedAperture.aZ a₀ k`) and `lam1 > 0`,
  `ReadsSlab (fun m k => boxGap (a_k)) (fun m k => slab (n m k)) τ`.
* `readsSlab_box`: the case `τ m = L_m = m a₀`, `n m k = m 2ᵏ` (the slab is the whole periodic side).
* `ratio_pos_of_form_pos`: `lam1 > 0` when some `h ⊥ φ` has `h ⬝ᵥ A h > 0`.

## 4. The Wilson transfer: what matches and what does not

The tree's slice transfer kernel is `RectTransfer.kT μ T N β` on the slice space `SpT μ T → SU N` with
the product Haar measure. Of the fields of `FinTransfer` it has: symmetry (`RectTransfer.kT_symm`),
positivity (`RectTransfer.kT_lower`, `kT ≥ kTmin > 0`), and semidefiniteness on continuous gauge-invariant
functions (`SliceKernelDefinite.sliceKernel_form_nonneg`, at `β ≥ 0`). As an operator on `L²(Haar)`
it is `SlabKernelOperator.kernelCLM (kT …)`, self-adjoint by
`SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm`, and `KernelEigen.exists_eigen` gives a bounded
measurable `φ` with `∫ φ² = 1` and `∫ kT(z, y) φ(y) dy = c φ(z)` at `|c| = ‖K‖`. It does not match in
two places:

* `RelativeGap.Slab.Ω` and every `GapL2` statement require a `Fintype` state space; the Wilson slice
  space is a product of copies of `SU N`, not finite. No `Slab` built from `kT` exists in the tree.
* The Doob normalisation needs `φ > 0` everywhere and `c > 0`; `KernelEigen.exists_eigen` gives
  neither the sign of `φ` nor that of `c` (Jentzsch's theorem for a continuous strictly positive
  kernel on a compact space would give both).

So `ReadsSlab` for the Wilson slab needs either `GapL2.Markov`, `Contr` and `Slab` over a probability
space (`L²(π)` of a measure, `K` a Markov operator) together with a positive top eigenfunction of
`kT`, or a finite approximation of the slice space whose transfer satisfies `FinTransfer`. The proofs
of section 1 use only self-adjointness in `L²(π)`, stationarity and Cauchy–Schwarz.

DERIVED (module-wide): `0` the mean selecting `φ⊥`, the lower end of every rate; `1` the least number
of steps in a slab and the rate of a Markov kernel on all functions; `2` the degree of the norm and of
`φ` in the stationary vector `φ²`.
-/

noncomputable section

namespace MassGap.ReadsSlabWilson

open Matrix GapL2 MassGap.RelativeGap MassGap.FixedAperture

/-! ## 1. Self-adjoint Markov kernels -/

section SelfAdjoint

variable {α : Type*} [Fintype α]

theorem ip_comm (π f g : α → ℝ) : ip π f g = ip π g f :=
  Finset.sum_congr rfl fun x _ => by ring

/-- A real quadratic `a − 2 l b + l² c ≥ 0` at every `l`, with `c ≥ 0`, has `b² ≤ a c`. -/
theorem sq_le_of_quad {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ l : ℝ, 0 ≤ a - 2 * l * b + l ^ 2 * c) :
    b ^ 2 ≤ a * c := by
  rcases hc.lt_or_eq with hc | hc
  · have h1 := h (b / c)
    have e : a - 2 * (b / c) * b + (b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp; ring
    rw [e] at h1
    have h2 : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hc] at h2
    linarith
  · subst hc
    by_cases hb : b = 0
    · subst hb; simp
    · have h1 := h ((a + 1) / (2 * b))
      have e : a - 2 * ((a + 1) / (2 * b)) * b + ((a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
        field_simp; ring
      rw [e] at h1
      linarith

theorem mean_sub_mul {π u v : α → ℝ} (l : ℝ) :
    mean π (fun x => u x - l * v x) = mean π u - l * mean π v := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

theorem mulVec_sub_mul (K : Matrix α α ℝ) (u v : α → ℝ) (l : ℝ) :
    (K *ᵥ fun x => u x - l * v x) = fun x => (K *ᵥ u) x - l * (K *ᵥ v) x := by
  funext x
  simp only [mulVec_apply', mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Cauchy–Schwarz for the transfer form** `⟨u, K v⟩`, symmetric and nonnegative on mean-zero
functions. -/
theorem form_cs {π : α → ℝ} {K : Matrix α α ℝ} (hrev : Rev π K)
    (hpsd : ∀ g, mean π g = 0 → 0 ≤ ip π g (K *ᵥ g)) {u v : α → ℝ} (hu : mean π u = 0)
    (hv : mean π v = 0) : ip π u (K *ᵥ v) ^ 2 ≤ ip π u (K *ᵥ u) * ip π v (K *ᵥ v) := by
  have hsym : ip π v (K *ᵥ u) = ip π u (K *ᵥ v) := by
    rw [ip_mulVec_symm hrev, ip_comm]
  refine sq_le_of_quad (hpsd v hv) fun l => ?_
  have hw := hpsd (fun x => u x - l * v x) (by rw [mean_sub_mul, hu, hv]; ring)
  have e : ip π (fun x => u x - l * v x) (K *ᵥ fun x => u x - l * v x) =
      ip π u (K *ᵥ u) - l * ip π u (K *ᵥ v) - l * ip π v (K *ᵥ u) + l ^ 2 * ip π v (K *ᵥ v) := by
    rw [mulVec_sub_mul]
    simp only [ip, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e, hsym] at hw
  linarith

/-- A contraction rate bounds the Rayleigh quotient: `⟨g, K g⟩ ≤ r ‖g‖²` on mean-zero `g`. -/
theorem rayleigh_of_contr {π : α → ℝ} {K : Matrix α α ℝ} (hπ : ∀ x, 0 ≤ π x) {r : ℝ}
    (h : Contr π K r) (g : α → ℝ) (hg : mean π g = 0) : ip π g (K *ᵥ g) ≤ r * nsq π g := by
  have h1 := ip_sq_le hπ g (K *ᵥ g)
  have h2 := h.2 g hg
  have hG := nsq_nonneg hπ g
  have h3 : ip π g (K *ᵥ g) ^ 2 ≤ (r * nsq π g) ^ 2 := by
    calc ip π g (K *ᵥ g) ^ 2 ≤ nsq π g * nsq π (K *ᵥ g) := h1
      _ ≤ nsq π g * (r ^ 2 * nsq π g) := mul_le_mul_of_nonneg_left h2 hG
      _ = (r * nsq π g) ^ 2 := by ring
  by_contra hlt
  push_neg at hlt
  have h0 : 0 ≤ r * nsq π g := mul_nonneg h.1 hG
  have := mul_self_lt_mul_self h0 hlt
  nlinarith

/-- **A semidefinite self-adjoint kernel contracts at the top of its Rayleigh quotient.** -/
theorem contr_of_rayleigh {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    (hpsd : ∀ g, mean π g = 0 → 0 ≤ ip π g (K *ᵥ g)) {c : ℝ} (hc : 0 ≤ c)
    (hray : ∀ g, mean π g = 0 → ip π g (K *ᵥ g) ≤ c * nsq π g) : Contr π K c := by
  refine ⟨hc, fun g hg => ?_⟩
  have hk : mean π (K *ᵥ g) = 0 := by rw [mean_mulVec M.stat, hg]
  have e1 : nsq π (K *ᵥ g) = ip π g (K *ᵥ (K *ᵥ g)) := by
    rw [nsq_eq_ip]; exact (ip_mulVec_symm hrev g (K *ᵥ g)).symm
  have cs := form_cs hrev hpsd hg hk
  have r1 := hray g hg
  have r2 := hray _ hk
  have p2 := hpsd _ hk
  have hG := nsq_nonneg M.pi_nonneg g
  have h3 : nsq π (K *ᵥ g) ^ 2 ≤ (c * nsq π g) * (c * nsq π (K *ᵥ g)) := by
    calc nsq π (K *ᵥ g) ^ 2 = ip π g (K *ᵥ (K *ᵥ g)) ^ 2 := by rw [e1]
      _ ≤ ip π g (K *ᵥ g) * ip π (K *ᵥ g) (K *ᵥ (K *ᵥ g)) := cs
      _ ≤ (c * nsq π g) * (c * nsq π (K *ᵥ g)) :=
          mul_le_mul r1 r2 p2 (mul_nonneg hc hG)
  rcases (nsq_nonneg M.pi_nonneg (K *ᵥ g)).lt_or_eq with hp | hz
  · nlinarith
  · rw [← hz]; positivity

/-- `r ↦ rⁿ` from below: if `rⁿ ≤ s` for every `r ∈ [0, ρ)`, then `ρⁿ ≤ s` (`n ≥ 1`). -/
theorem pow_le_of_forall_lt {n : ℕ} (hn : n ≠ 0) {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ)
    (h : ∀ r, 0 ≤ r → r < ρ → r ^ n ≤ s) : ρ ^ n ≤ s := by
  by_contra hlt
  push_neg at hlt
  set t := s ^ ((n : ℝ)⁻¹) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hs _
  have htn : t ^ n = s := Real.rpow_inv_natCast_pow hs hn
  have htρ : t < ρ := (pow_lt_pow_iff_left₀ ht0 hρ hn).1 (by rw [htn]; exact hlt)
  have h1 := h ((t + ρ) / 2) (by linarith) (by linarith)
  rw [← htn] at h1
  have h2 := (pow_le_pow_iff_left₀ (by linarith) ht0 hn).1 h1
  linarith

/-- The squared norms `a_j = ‖Kʲ g‖²` of a self-adjoint kernel are log-convex. -/
theorem nsq_pow_logconvex [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hrev : Rev π K) (g : α → ℝ) (j : ℕ) :
    nsq π ((K ^ (j + 1)) *ᵥ g) ^ 2 ≤ nsq π ((K ^ j) *ᵥ g) * nsq π ((K ^ (j + 1 + 1)) *ᵥ g) := by
  have hk1 : (K ^ (j + 1)) *ᵥ g = K *ᵥ ((K ^ j) *ᵥ g) := by rw [pow_succ', ← mulVec_mulVec]
  have hk2 : (K ^ (j + 1 + 1)) *ᵥ g = K *ᵥ (K *ᵥ ((K ^ j) *ᵥ g)) := by
    rw [pow_succ', ← mulVec_mulVec, hk1]
  have e : nsq π ((K ^ (j + 1)) *ᵥ g) = ip π ((K ^ j) *ᵥ g) ((K ^ (j + 1 + 1)) *ᵥ g) := by
    rw [hk1, hk2, nsq_eq_ip]; exact (ip_mulVec_symm hrev _ _).symm
  rw [e]
  exact ip_sq_le hπ _ _

/-- **The power bound for a self-adjoint Markov kernel**: every rate `s` of `Kⁿ`, `n ≥ 1`, has
`(maxCorr π K)ⁿ ≤ s`. -/
theorem pow_le_of_contr_pow [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K)
    (hrev : Rev π K) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (h : Contr π (K ^ n) s) :
    maxCorr π K ^ n ≤ s := by
  refine pow_le_of_forall_lt (by omega) h.1 (maxCorr_nonneg M) fun r hr0 hrρ => ?_
  have hnc : ¬ Contr π K r := fun hc => absurd (maxCorr_le_of_contr M hc) (not_le.2 hrρ)
  obtain ⟨g, hg, hlt⟩ : ∃ g, mean π g = 0 ∧ r ^ 2 * nsq π g < nsq π (K *ᵥ g) := by
    by_contra hne
    push_neg at hne
    exact hnc ⟨hr0, hne⟩
  set a : ℕ → ℝ := fun j => nsq π ((K ^ j) *ᵥ g) with ha
  have ha0 : a 0 = nsq π g := by simp [ha, Matrix.one_mulVec]
  have ha1 : a 1 = nsq π (K *ᵥ g) := by simp [ha]
  have hnn : ∀ j, 0 ≤ a j := fun j => nsq_nonneg M.pi_nonneg _
  have hlc : ∀ j, a (j + 1) ^ 2 ≤ a j * a (j + 1 + 1) := nsq_pow_logconvex M.pi_nonneg hrev g
  have hstep : ∀ j, r ^ 2 * a j ≤ a (j + 1) := by
    intro j
    induction j with
    | zero => rw [ha0, ha1]; exact hlt.le
    | succ j ih =>
      have h1 := hlc j
      rcases (hnn j).lt_or_eq with hp | hz
      · have h2 : r ^ 2 * a j * a (j + 1) ≤ a j * a (j + 1 + 1) :=
          (mul_le_mul_of_nonneg_right ih (hnn (j + 1))).trans (by nlinarith)
        have h3 : a j * (r ^ 2 * a (j + 1)) ≤ a j * a (j + 1 + 1) := by linarith
        exact le_of_mul_le_mul_left h3 hp
      · have : a (j + 1) = 0 := by
          rw [← hz, zero_mul] at h1
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
        rw [this, mul_zero]; exact hnn _
  have hgrow : ∀ j, r ^ (2 * j) * a 0 ≤ a j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc r ^ (2 * (j + 1)) * a 0 = r ^ 2 * (r ^ (2 * j) * a 0) := by ring
        _ ≤ r ^ 2 * a j := mul_le_mul_of_nonneg_left ih (sq_nonneg r)
        _ ≤ a (j + 1) := hstep j
  have hpos : 0 < a 0 := by
    rcases (hnn 0).lt_or_eq with hp | hz
    · exact hp
    · exfalso
      have h1 := nsq_mulVec_le M g
      rw [← ha0, ← hz] at h1 hlt
      linarith
  have hn' : a n ≤ s ^ 2 * a 0 := by rw [ha0]; exact h.2 g hg
  have h4 : (r ^ n) ^ 2 * a 0 ≤ s ^ 2 * a 0 := by
    have := hgrow n
    rw [show r ^ (2 * n) = (r ^ n) ^ 2 by ring] at this
    linarith
  have h5 : (r ^ n) ^ 2 ≤ s ^ 2 := le_of_mul_le_mul_right h4 hpos
  exact (pow_le_pow_iff_left₀ (pow_nonneg hr0 n) h.1 two_ne_zero).1 h5

/-- **The rate of a power of a self-adjoint Markov kernel is the power of its rate**:
`maxCorr π (Kⁿ) = (maxCorr π K)ⁿ` for `n ≥ 1`. -/
theorem maxCorr_pow_eq [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K)
    (hrev : Rev π K) {n : ℕ} (hn : 1 ≤ n) : maxCorr π (K ^ n) = maxCorr π K ^ n :=
  le_antisymm (maxCorr_pow_le M n) (pow_le_of_contr_pow M hrev hn (contr_maxCorr (M.pow n)))

end SelfAdjoint

/-! ## 2. The Perron (Doob) slab of a finite transfer matrix -/

/-- **A finite transfer matrix with its Perron vector**: `A` symmetric, entrywise `≥ 0`, positive
semidefinite on `φ⊥`; `φ > 0` with `A φ = λ₀ φ`, `λ₀ > 0`; the state space finite and nonempty. -/
structure FinTransfer where
  Ω : Type
  [fin : Fintype Ω]
  [dec : DecidableEq Ω]
  [ne : Nonempty Ω]
  A : Matrix Ω Ω ℝ
  symm : ∀ x y, A x y = A y x
  nonneg : ∀ x y, 0 ≤ A x y
  φ : Ω → ℝ
  φ_pos : ∀ x, 0 < φ x
  lam0 : ℝ
  lam0_pos : 0 < lam0
  eig : ∀ x, (A *ᵥ φ) x = lam0 * φ x
  psd : ∀ h : Ω → ℝ, h ⬝ᵥ φ = 0 → 0 ≤ h ⬝ᵥ (A *ᵥ h)

attribute [instance] FinTransfer.fin FinTransfer.dec FinTransfer.ne

namespace FinTransfer

variable (T : FinTransfer)

/-- The normalisation `Z = Σ φ²`. -/
def Z : ℝ := ∑ x, T.φ x ^ 2

theorem Z_pos : 0 < T.Z :=
  Finset.sum_pos (fun x _ => pow_pos (T.φ_pos x) 2) Finset.univ_nonempty

/-- The stationary vector `φ² / Z`. -/
def piD (x : T.Ω) : ℝ := T.φ x ^ 2 / T.Z

/-- The Doob-normalised transfer `A(x,y) φ(y) / (λ₀ φ(x))`. -/
def kD : Matrix T.Ω T.Ω ℝ := fun x y => T.A x y * T.φ y / (T.lam0 * T.φ x)

theorem eig' (x : T.Ω) : ∑ y, T.A x y * T.φ y = T.lam0 * T.φ x := T.eig x

/-- **The Doob slab is a Markov pair.** -/
theorem markov : Markov T.piD T.kD where
  pi_nonneg x := div_nonneg (sq_nonneg _) T.Z_pos.le
  pi_sum := by
    simp only [piD]
    rw [← Finset.sum_div]
    exact div_self T.Z_pos.ne'
  nonneg x y := div_nonneg (mul_nonneg (T.nonneg x y) (T.φ_pos y).le)
    (mul_pos T.lam0_pos (T.φ_pos x)).le
  row x := by
    show ∑ y, T.A x y * T.φ y / (T.lam0 * T.φ x) = 1
    rw [← Finset.sum_div, T.eig' x]
    exact div_self (mul_pos T.lam0_pos (T.φ_pos x)).ne'
  stat y := by
    show ∑ x, T.φ x ^ 2 / T.Z * (T.A x y * T.φ y / (T.lam0 * T.φ x)) = T.φ y ^ 2 / T.Z
    have hZ := T.Z_pos.ne'
    have hl := T.lam0_pos.ne'
    have e : ∀ x, T.φ x ^ 2 / T.Z * (T.A x y * T.φ y / (T.lam0 * T.φ x)) =
        T.φ y / (T.Z * T.lam0) * (T.A y x * T.φ x) := by
      intro x
      have := (T.φ_pos x).ne'
      rw [T.symm x y]
      field_simp
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.mul_sum, T.eig' y]
    field_simp

/-- **Detailed balance**: the Doob slab is self-adjoint in `L²(piD)`. -/
theorem rev : Rev T.piD T.kD := by
  intro x y
  show T.φ x ^ 2 / T.Z * (T.A x y * T.φ y / (T.lam0 * T.φ x)) =
    T.φ y ^ 2 / T.Z * (T.A y x * T.φ x / (T.lam0 * T.φ y))
  have := (T.φ_pos x).ne'
  have := (T.φ_pos y).ne'
  have := T.Z_pos.ne'
  have := T.lam0_pos.ne'
  rw [T.symm y x]
  field_simp

/-- The mean under `piD` in terms of `h = φ g`. -/
theorem mean_eq (g : T.Ω → ℝ) : mean T.piD g = ((fun x => T.φ x * g x) ⬝ᵥ T.φ) / T.Z := by
  simp only [mean, piD, dotProduct, Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The squared norm under `piD` in terms of `h = φ g`. -/
theorem nsq_eq (g : T.Ω → ℝ) :
    nsq T.piD g = ((fun x => T.φ x * g x) ⬝ᵥ (fun x => T.φ x * g x)) / T.Z := by
  simp only [nsq, piD, dotProduct, Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The transfer form under `piD` in terms of `h = φ g`. -/
theorem ip_eq (g : T.Ω → ℝ) :
    ip T.piD g (T.kD *ᵥ g) =
      ((fun x => T.φ x * g x) ⬝ᵥ (T.A *ᵥ fun x => T.φ x * g x)) / (T.Z * T.lam0) := by
  simp only [ip, piD, kD, dotProduct, mulVec_apply', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have := (T.φ_pos x).ne'
  have := T.Z_pos.ne'
  have := T.lam0_pos.ne'
  field_simp

theorem phi_mul_div (h : T.Ω → ℝ) : (fun x => T.φ x * (h x / T.φ x)) = h :=
  funext fun x => mul_div_cancel₀ (h x) (T.φ_pos x).ne'

theorem dot_self_nonneg (h : T.Ω → ℝ) : 0 ≤ h ⬝ᵥ h :=
  Finset.sum_nonneg fun x _ => mul_self_nonneg (h x)

/-- A Rayleigh bound `c` for `kD` is a Rayleigh bound `λ₀ c` for `A` on `φ⊥`. -/
theorem rayA_of_rayK {c : ℝ} (hK : ∀ g, mean T.piD g = 0 → ip T.piD g (T.kD *ᵥ g) ≤ c * nsq T.piD g) :
    ∀ h : T.Ω → ℝ, h ⬝ᵥ T.φ = 0 → h ⬝ᵥ (T.A *ᵥ h) ≤ (T.lam0 * c) * (h ⬝ᵥ h) := by
  intro h hh
  have h1 := hK (fun x => h x / T.φ x) (by rw [mean_eq, phi_mul_div, hh, zero_div])
  rw [ip_eq, nsq_eq, phi_mul_div] at h1
  have hZl : 0 < T.Z * T.lam0 := mul_pos T.Z_pos T.lam0_pos
  rw [div_le_iff₀ hZl] at h1
  have hZ := T.Z_pos.ne'
  calc h ⬝ᵥ (T.A *ᵥ h) ≤ c * ((h ⬝ᵥ h) / T.Z) * (T.Z * T.lam0) := h1
    _ = (T.lam0 * c) * (h ⬝ᵥ h) := by field_simp

/-- A Rayleigh bound `s` for `A` on `φ⊥` is a Rayleigh bound `s/λ₀` for `kD`. -/
theorem rayK_of_rayA {s : ℝ} (hA : ∀ h : T.Ω → ℝ, h ⬝ᵥ T.φ = 0 → h ⬝ᵥ (T.A *ᵥ h) ≤ s * (h ⬝ᵥ h)) :
    ∀ g, mean T.piD g = 0 → ip T.piD g (T.kD *ᵥ g) ≤ (s / T.lam0) * nsq T.piD g := by
  intro g hg
  rw [mean_eq, div_eq_zero_iff] at hg
  have hφ : (fun x => T.φ x * g x) ⬝ᵥ T.φ = 0 := hg.resolve_right T.Z_pos.ne'
  have h1 := hA _ hφ
  rw [ip_eq, nsq_eq]
  have hZl : 0 < T.Z * T.lam0 := mul_pos T.Z_pos T.lam0_pos
  rw [div_le_iff₀ hZl]
  have hZ := T.Z_pos.ne'
  have hl := T.lam0_pos.ne'
  calc _ ≤ s * ((fun x => T.φ x * g x) ⬝ᵥ (fun x => T.φ x * g x)) := h1
    _ = s / T.lam0 * (((fun x => T.φ x * g x) ⬝ᵥ (fun x => T.φ x * g x)) / T.Z) *
        (T.Z * T.lam0) := by field_simp

/-- The transfer form is nonnegative on mean-zero functions of the slab. -/
theorem psdK (g : T.Ω → ℝ) (hg : mean T.piD g = 0) : 0 ≤ ip T.piD g (T.kD *ᵥ g) := by
  rw [mean_eq, div_eq_zero_iff] at hg
  rw [ip_eq]
  exact div_nonneg (T.psd _ (hg.resolve_right T.Z_pos.ne')) (mul_pos T.Z_pos T.lam0_pos).le

/-- The Rayleigh bounds of `A` on `φ⊥`. -/
def raySet : Set ℝ := {s | 0 ≤ s ∧ ∀ h : T.Ω → ℝ, h ⬝ᵥ T.φ = 0 → h ⬝ᵥ (T.A *ᵥ h) ≤ s * (h ⬝ᵥ h)}

/-- **`λ₁`**: the top of the Rayleigh quotient of `A` on `φ⊥` (and `0` if that top is negative). -/
def lam1 : ℝ := sInf T.raySet

theorem lam0_mem : T.lam0 ∈ T.raySet := by
  refine ⟨T.lam0_pos.le, fun h hh => ?_⟩
  have := T.rayA_of_rayK (c := 1)
    (fun g hg => rayleigh_of_contr T.markov.pi_nonneg (Contr.of_markov T.markov) g hg) h hh
  rwa [mul_one] at this

theorem lam1_nonneg : 0 ≤ T.lam1 := le_csInf ⟨_, T.lam0_mem⟩ fun _ hs => hs.1

theorem lam1_le {s : ℝ} (hs : s ∈ T.raySet) : T.lam1 ≤ s := csInf_le ⟨0, fun _ hs => hs.1⟩ hs

/-- **The infimum is a Rayleigh bound**: `h ⬝ᵥ A h ≤ λ₁ (h ⬝ᵥ h)` on `φ⊥`. -/
theorem lam1_spec (h : T.Ω → ℝ) (hh : h ⬝ᵥ T.φ = 0) : h ⬝ᵥ (T.A *ᵥ h) ≤ T.lam1 * (h ⬝ᵥ h) := by
  rcases (T.dot_self_nonneg h).lt_or_eq with hp | hz
  · have : h ⬝ᵥ (T.A *ᵥ h) / (h ⬝ᵥ h) ≤ T.lam1 :=
      le_csInf ⟨_, T.lam0_mem⟩ fun s hs => (div_le_iff₀ hp).2 (hs.2 h hh)
    rwa [div_le_iff₀ hp] at this
  · have := T.lam0_mem.2 h hh
    rw [← hz, mul_zero] at this ⊢
    exact this

theorem lam1_mem : T.lam1 ∈ T.raySet := ⟨T.lam1_nonneg, T.lam1_spec⟩

/-- Every eigenvalue of `A` with an eigenvector in `φ⊥` is at most `λ₁`. -/
theorem le_lam1_of_eigen {ψ : T.Ω → ℝ} {μ : ℝ} (hψ : ψ ⬝ᵥ T.φ = 0) (hne : ψ ≠ 0)
    (hA : T.A *ᵥ ψ = μ • ψ) : μ ≤ T.lam1 := by
  have h1 := T.lam1_spec ψ hψ
  rw [hA, dotProduct_smul, smul_eq_mul] at h1
  have hp : 0 < ψ ⬝ᵥ ψ := by
    rcases (T.dot_self_nonneg ψ).lt_or_eq with hp | hz
    · exact hp
    · exact absurd (dotProduct_self_eq_zero.1 hz.symm) hne
  exact le_of_mul_le_mul_right h1 hp

/-- The second-to-first eigenvalue ratio `λ₁ / λ₀`. -/
def ratio : ℝ := T.lam1 / T.lam0

/-- **The `L²` rate of one step is `λ₁ / λ₀`**: `maxCorr piD kD = λ₁ / λ₀`. -/
theorem maxCorr_eq : maxCorr T.piD T.kD = T.ratio := by
  apply le_antisymm
  · exact maxCorr_le_of_contr T.markov
      (contr_of_rayleigh T.markov T.rev T.psdK (div_nonneg T.lam1_nonneg T.lam0_pos.le)
        (T.rayK_of_rayA T.lam1_spec))
  · have h := T.lam1_le (s := T.lam0 * maxCorr T.piD T.kD)
      ⟨mul_nonneg T.lam0_pos.le (maxCorr_nonneg T.markov),
        T.rayA_of_rayK (rayleigh_of_contr T.markov.pi_nonneg (contr_maxCorr T.markov))⟩
    show T.lam1 / T.lam0 ≤ _
    rw [div_le_iff₀ T.lam0_pos, mul_comm]
    exact h

/-- **The slab of `n` steps**: the Markov pair `(piD, kDⁿ)`. -/
def slab (n : ℕ) : Slab where
  Ω := T.Ω
  π := T.piD
  K := T.kD ^ n
  markov := T.markov.pow n

/-- **The `L²` rate of the slab of `n ≥ 1` steps is `(λ₁/λ₀)ⁿ`.** -/
theorem rho_slab {n : ℕ} (hn : 1 ≤ n) : (T.slab n).rho = T.ratio ^ n := by
  show maxCorr T.piD (T.kD ^ n) = T.ratio ^ n
  rw [maxCorr_pow_eq T.markov T.rev hn, maxCorr_eq]

/-- **`(λ₁/λ₀)ⁿ` is a contraction rate of the slab, and every contraction rate is at least it.** -/
theorem contr_slab {n : ℕ} (hn : 1 ≤ n) :
    Contr (T.slab n).π (T.slab n).K (T.ratio ^ n) ∧
      ∀ r, Contr (T.slab n).π (T.slab n).K r → T.ratio ^ n ≤ r := by
  rw [← T.rho_slab hn]
  exact ⟨contr_maxCorr (T.slab n).markov, fun r hr => maxCorr_le_of_contr (T.slab n).markov hr⟩

/-! ## 3. `ReadsSlab` -/

/-- The transfer gap per unit time of one step of length `a`: `−log(λ₁/λ₀)/a`. -/
def boxGap (a : ℝ) : ℝ := -Real.log T.ratio / a

theorem ratio_nonneg : 0 ≤ T.ratio := div_nonneg T.lam1_nonneg T.lam0_pos.le

/-- **The gap read from the slab is the transfer gap**: `−log ρ_slab / (n a) = −log(λ₁/λ₀)/a`. -/
theorem relGap_slab {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    -Real.log (T.slab n).rho / (n * a) = T.boxGap a := by
  rw [T.rho_slab hn, Real.log_pow, boxGap]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- **One slab reads the transfer gap**: every contraction rate `r` of the slab of `n ≥ 1` steps of length
`a > 0` has `−log r / (n a) ≤ −log(λ₁/λ₀)/a`, when `λ₁ > 0`. -/
theorem le_boxGap_of_contr {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (hpos : 0 < T.ratio)
    {r : ℝ} (hc : Contr (T.slab n).π (T.slab n).K r) :
    -Real.log r / (n * a) ≤ T.boxGap a := by
  have hle := (T.contr_slab hn).2 r hc
  have hlog : Real.log (T.ratio ^ n) ≤ Real.log r := Real.log_le_log (pow_pos hpos n) hle
  rw [← T.relGap_slab hn ha, T.rho_slab hn]
  have hna : 0 < (n : ℝ) * a := mul_pos (by exact_mod_cast (by omega : 0 < n)) ha
  exact div_le_div_of_nonneg_right (by linarith) hna.le

/-- `λ₁ > 0` when the transfer form is positive somewhere on `φ⊥`. -/
theorem ratio_pos_of_form_pos {h : T.Ω → ℝ} (hh : h ⬝ᵥ T.φ = 0) (hp : 0 < h ⬝ᵥ (T.A *ᵥ h)) :
    0 < T.ratio := by
  have h1 := T.lam1_spec h hh
  have h2 := T.dot_self_nonneg h
  have hl : 0 < T.lam1 := by
    rcases T.lam1_nonneg.lt_or_eq with hl | hl
    · exact hl
    · rw [← hl, zero_mul] at h1; linarith
  exact div_pos hl T.lam0_pos

end FinTransfer

/-- **`ReadsSlab` for a family of finite transfers**: at aperture `m` and zoom `k`, the slab of
`n m k ≥ 1` steps of the transfer `T m k`, of physical thickness `τ m = n m k · a_k`
(`a_k = aZ a₀ k`), with `λ₁ > 0`: the box gap `−log(λ₁/λ₀)/a_k` reads the slab. -/
theorem readsSlab_transfer (T : ℕ → ℕ → FinTransfer) {a₀ : ℝ} (ha : 0 < a₀) (n : ℕ → ℕ → ℕ)
    (τ : ℕ → ℝ) (hn : ∀ m k, 0 < m → 1 ≤ n m k)
    (hτ : ∀ m k, 0 < m → (n m k : ℝ) * aZ a₀ k = τ m)
    (hpos : ∀ m k, 0 < m → 0 < (T m k).ratio) :
    ReadsSlab (fun m k => (T m k).boxGap (aZ a₀ k)) (fun m k => (T m k).slab (n m k)) τ := by
  intro m hm
  refine ⟨?_, fun k r _ hc => ?_⟩
  · rw [← hτ m 0 hm]
    exact mul_pos (by exact_mod_cast (by have := hn m 0 hm; omega : 0 < n m 0)) (aZ_pos ha 0)
  · rw [← hτ m k hm]
    exact (T m k).le_boxGap_of_contr (hn m k hm) (aZ_pos ha k) (hpos m k hm) hc

/-- **The gap read from the slab is the box gap**, `relGap = boxGap`, along the family. -/
theorem relGap_transfer (T : ℕ → ℕ → FinTransfer) {a₀ : ℝ} (ha : 0 < a₀) (n : ℕ → ℕ → ℕ)
    (τ : ℕ → ℝ) (hn : ∀ m k, 0 < m → 1 ≤ n m k)
    (hτ : ∀ m k, 0 < m → (n m k : ℝ) * aZ a₀ k = τ m) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    relGap (fun m k => (T m k).slab (n m k)) τ m k = (T m k).boxGap (aZ a₀ k) := by
  show -Real.log ((T m k).slab (n m k)).rho / τ m = _
  rw [← hτ m k hm]
  exact (T m k).relGap_slab (hn m k hm) (aZ_pos ha k)

/-- **The slab across the whole periodic side**: `τ m = L_m = m a₀`, `n m k = m 2ᵏ` steps. -/
theorem readsSlab_box (T : ℕ → ℕ → FinTransfer) {a₀ : ℝ} (ha : 0 < a₀)
    (hpos : ∀ m k, 0 < m → 0 < (T m k).ratio) :
    ReadsSlab (fun m k => (T m k).boxGap (aZ a₀ k)) (fun m k => (T m k).slab (m * 2 ^ k))
      (LA a₀) := by
  refine readsSlab_transfer T ha (fun m k => m * 2 ^ k) (LA a₀) (fun m k hm => ?_)
    (fun m k _ => ?_) hpos
  · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ two_ne_zero))
  · simp only [aZ, LA]
    push_cast
    field_simp

#print axioms form_cs
#print axioms rayleigh_of_contr
#print axioms contr_of_rayleigh
#print axioms pow_le_of_contr_pow
#print axioms maxCorr_pow_eq
#print axioms FinTransfer.markov
#print axioms FinTransfer.rev
#print axioms FinTransfer.lam1_spec
#print axioms FinTransfer.le_lam1_of_eigen
#print axioms FinTransfer.maxCorr_eq
#print axioms FinTransfer.rho_slab
#print axioms FinTransfer.contr_slab
#print axioms FinTransfer.relGap_slab
#print axioms FinTransfer.le_boxGap_of_contr
#print axioms FinTransfer.ratio_pos_of_form_pos
#print axioms readsSlab_transfer
#print axioms relGap_transfer
#print axioms readsSlab_box

end MassGap.ReadsSlabWilson
