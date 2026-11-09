import Mathlib
import MassGap.CouplingTower

/-!
# MassGap.ToronDecrement — the weak-coupling decrement of the SU(2) window coupling

At large `β` the window coupling `g β w = windowCoupling 2 β w = defectW 2 β (2^w)` is argued to have the
Laplace form

  `g β w = F β + 3 c_{2^w} + 16 log(x + B w) − log(x + B (w+1)) + ρ β w`,  `x = (log β)/4`,

with `F` independent of `w`; this form is the content of the open input `ToronLaplace`. The two `w`-dependent
constants are closed forms; what is proved about them is listed below, and the rest is argued.

* `c_L` (`cL`) is the Gaussian part: `c_L = ½(15 log L⁴ − log 16) − (16 ℓ_L − ℓ_{2L})` with
  `ℓ_L = Σ_{p ≠ 0} log Σ_μ 4 sin²(p_μ/2)` over the `L⁴` momenta (`ell`; the zero mode drops out because
  `log 0 = 0`). With `ℓ_L = L⁴ f₀ + 2 log L + C + a/L² + r_L`, the identity `cL_eq` gives
  `c_L = −15 C − (63/4) a/L² − (16 r_L − r_{2L})`: the volume term and the `log L` term cancel exactly in
  `16 ℓ_L − ℓ_{2L}`, so `c_L` converges at rate `L⁻²` once the expansion of `ℓ_L` holds (`EllExpansion`, open).
  The argued closed forms are
  `C = ∫₀^∞ ds/s [1 − e^{−s} − (ϑ(s)⁴ − (4πs)⁻²)]`, `ϑ(s) = Σ_k e^{−4π²k²s}`, and
  `a = −(4/π²) Σ_{m ∈ ℤ⁴∖0} (2 Σ_μ m_μ⁴/|m|¹⁰ − 1/|m|⁶) < 0`.
* `B_L` (`B` at the window index in `ToronLaplace`) is the flat-connection (toron) constant, argued as
  follows. In the adjoint holonomy angle `Θ ∈ [−π, π]⁴` the toron weight is `det(−D_Θ²)^{−2}` with spectrum
  `Σ_μ 4 sin²((2π n_μ + Θ_μ)/(2L))`, and the constant-mode cutoff sits at `|Θ| ∼ β^{−1/4}`, independent of `L`.
  So `B_L = κ + Φ_L`, with `κ` the universal finite part of the twelve-dimensional constant-mode integral and
  `Φ_L` the finite part of the toron integral, which converges to its continuum value at rate `L⁻²`. Proved
  here: the one-dimensional twisted determinant shows the same mechanism exactly (`twisted_det_one_dim`):
  `∏_k 4 sin²((2πk + Θ)/(2L)) = 4 sin²(Θ/2)`, independent of `L`. The untwisted one with the zero mode removed
  is `L²` (`det_prime_one_dim`), which gives the `2 log L` in `ℓ_L`.

The window step `g β (w+1) − g β w` is the sum of the Gaussian decrement `3(c_{2L} − c_L)` (negative,
`≈ (567/16) a/L²`), the toron term `17 log(x+B_{2L}) − log(x+B_{4L}) − 16 log(x+B_L)`, bounded by
`16 (B_{2L} − B_L)/(x + B_L)` (`toron_term_le`), and the remainder step.

* `cL_eq`, `decrement_eq`: exact identities, no hypothesis.
* `decrement_le`, `decrement_neg`: from `EllExpansion` (the `L⁻⁴` remainder of `ℓ_L`) the Gaussian
  decrement is eventually at most `(567/32) a/L² < 0`.
* `ToronLaplace`: the open input, the Laplace asymptotic of `log Z_L` in the form above on windows up to a
  bound `W β → ∞`, with a toron sequence that is positive, nondecreasing, with increments `O(4^{−w})`, and a
  remainder whose window step is at most `ε(β) 4^{−w}`, `ε → 0`.
* `LatticeDecrement`: `3(c_{2^{w+1}} − c_{2^w}) ≤ −α 4^{−w}` for every `w ≥ 1`, a statement about the explicit
  finite sums `ell`.
* `windowCoupling_decreasing`: `ToronLaplace` and `LatticeDecrement` give, eventually in `β`, a strictly
  decreasing window coupling on every window `1 ≤ w`, `w + 1 ≤ W β`.

DERIVED (module-wide): `2` the gauge rank and the doubling; `4` the dimension and `x = (log β)/4` (the
quartic constant-mode scale `β^{−1/4}`); `16 = 2⁴` the copies of the side-`L` torus in the side-`2L` torus;
`17 = 16 + 1` and `15 = 16 − 1` from `16 X_L − X_{2L}` at consecutive windows; `63/4 = 16 − 1/4`,
`567/16 = 3 · (63/4) · (3/4)`, `567/32` half of it; `13107/256 = 3 (16 + 17/16 + 1/256)` the remainder count;
`3` the dimension of `su(2)`; `1/4 = 2⁻²` the `L⁻²` rate per doubling.
-/

noncomputable section

namespace MassGap.ToronDecrement

open Real Filter Topology Finset
open MassGap.CouplingTower (windowCoupling)

/-! ## One-dimensional lattice determinants -/

/-- `|1 − e^{iφ}|² = 2 − 2 cos φ`. DERIVED: `1`, `2` from expanding the square. -/
theorem normSq_one_sub_exp (φ : ℝ) :
    Complex.normSq (1 - Complex.exp (φ * Complex.I)) = 2 - 2 * Real.cos φ := by
  rw [Complex.normSq_apply]
  have hre : (1 - Complex.exp (φ * Complex.I)).re = 1 - Real.cos φ := by
    rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have him : (1 - Complex.exp (φ * Complex.I)).im = -Real.sin φ := by
    rw [Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im]; ring
  rw [hre, him]
  linear_combination Real.sin_sq_add_cos_sq φ

/-- **Twisted one-dimensional determinant.** For a ring of `L ≥ 1` sites with holonomy angle `Θ`,
`∏_{k<L} (2 − 2 cos((2πk + Θ)/L)) = 2 − 2 cos Θ`: the twisted determinant depends on the holonomy only,
not on `L`. DERIVED: `2` from `|1 − e^{iφ}|²`, `2π` the period. -/
theorem twisted_det_one_dim (L : ℕ) (hL : 0 < L) (Θ : ℝ) :
    ∏ k ∈ range L, (2 - 2 * Real.cos ((2 * π * k + Θ) / L)) = 2 - 2 * Real.cos Θ := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hζ := Complex.isPrimitiveRoot_exp L hL.ne'
  have e : Complex.exp (((Θ / L : ℝ) : ℂ) * Complex.I) ^ L = Complex.exp ((Θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    have h : (L : ℂ) * ((Θ : ℂ) / (L : ℂ)) = Θ := mul_div_cancel₀ _ hL0
    push_cast
    linear_combination Complex.I * h
  have hpoly := X_pow_sub_C_eq_prod hζ hL e
  have h1 := congrArg (Polynomial.eval 1) hpoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, one_pow] at h1
  have h2 := congrArg Complex.normSq h1
  rw [map_prod, normSq_one_sub_exp] at h2
  rw [h2]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : Complex.exp (2 * π * Complex.I / L) ^ k * Complex.exp (((Θ / L : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((2 * π * k + Θ) / L : ℝ)) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hk, normSq_one_sub_exp]

/-- **Untwisted one-dimensional determinant without the zero mode.** On a ring of `L + 1` sites,
`∏_{1 ≤ k ≤ L} (2 − 2 cos(2πk/(L+1))) = (L+1)²`; this is the `2 log L` of the lattice determinant.
DERIVED: `2` from `|1 − e^{iφ}|²`, `2π` the period, `1` the removed zero mode. -/
theorem det_prime_one_dim (L : ℕ) :
    ∏ k ∈ range L, (2 - 2 * Real.cos (2 * π * ((k : ℝ) + 1) / ((L : ℝ) + 1))) = ((L : ℝ) + 1) ^ 2 := by
  have hζ := Complex.isPrimitiveRoot_exp (L + 1) (Nat.succ_ne_zero L)
  have h := hζ.prod_one_sub_pow_eq_order
  have h2 := congrArg Complex.normSq h
  rw [map_prod] at h2
  have hR : Complex.normSq ((L : ℂ) + 1) = ((L : ℝ) + 1) ^ 2 := by
    have : ((L : ℂ) + 1) = (((L : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.normSq_ofReal]; ring
  rw [hR] at h2
  rw [← h2]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : Complex.exp (2 * π * Complex.I / ((L + 1 : ℕ) : ℂ)) ^ (k + 1)
      = Complex.exp (((2 * π * ((k : ℝ) + 1) / ((L : ℝ) + 1) : ℝ)) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hk, normSq_one_sub_exp]

/-! ## The four-dimensional Gaussian constant `c_L` -/

/-- `ℓ_L = Σ_{n ∈ (ℤ/L)⁴} log Σ_μ 4 sin²(π n_μ / L)`. The zero mode contributes `log 0 = 0`, so this is the
sum over the nonzero momenta. DERIVED: `4` from `2 − 2 cos p = 4 sin²(p/2)`. -/
def ell (L : ℕ) : ℝ :=
  ∑ n : Fin 4 → Fin L, Real.log (∑ μ, 4 * Real.sin (π * ((n μ : ℕ) : ℝ) / L) ^ 2)

/-- `c_L = ½(15 log L⁴ − log 16) − (16 ℓ_L − ℓ_{2L})`. DERIVED: `16` the copies, `15 = 16 − 1`, `½` the
Gaussian square root. -/
def cL (L : ℕ) : ℝ :=
  (15 * Real.log ((L : ℝ) ^ 4) - Real.log 16) / 2 - (16 * ell L - ell (2 * L))

/-- The remainder of `ℓ_L` after `L⁴ f₀ + 2 log L + C + a/L²`. DERIVED: `2` the `log L` coefficient
(`det_prime_one_dim` in one dimension, zeta value `−1` of the zero mode in four). -/
def rem (f₀ C a : ℝ) (L : ℕ) : ℝ :=
  ell L - ((L : ℝ) ^ 4 * f₀ + 2 * Real.log L + C + a / (L : ℝ) ^ 2)

/-- **The doubling cancellation.** For any `f₀ C a`, `c_L = −15 C − (63/4) a/L² − (16 r_L − r_{2L})`: the
volume term and the `log L` term of `ℓ_L` cancel exactly. -/
theorem cL_eq (f₀ C a : ℝ) {L : ℕ} (hL : 0 < L) :
    cL L = -15 * C - 63 / 4 * a / (L : ℝ) ^ 2 - (16 * rem f₀ C a L - rem f₀ C a (2 * L)) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h2L : Real.log ((2 * L : ℕ) : ℝ) = Real.log 2 + Real.log L := by
    push_cast; exact Real.log_mul two_ne_zero hL'
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  unfold cL rem
  rw [Real.log_pow, h2L, h16]
  push_cast
  ring

/-- **The Gaussian decrement, exactly.**
`3(c_{2L} − c_L) = (567/16) a/L² − 3(17 r_{2L} − r_{4L} − 16 r_L)`. -/
theorem decrement_eq (f₀ C a : ℝ) {L : ℕ} (hL : 0 < L) :
    3 * (cL (2 * L) - cL L) = 567 / 16 * a / (L : ℝ) ^ 2
      - 3 * (17 * rem f₀ C a (2 * L) - rem f₀ C a (2 * (2 * L)) - 16 * rem f₀ C a L) := by
  rw [cL_eq f₀ C a (by omega : 0 < 2 * L), cL_eq f₀ C a hL]
  push_cast
  ring

/-- `ℓ_L = L⁴ f₀ + 2 log L + C + a/L² + O(L⁻⁴)` with `a < 0`: the Euler–Maclaurin (Bessel) expansion of the
explicit finite sum `ell`. The closed forms of `C` and `a` are in the module docstring. -/
def EllExpansion : Prop :=
  ∃ f₀ C a K : ℝ, a < 0 ∧ ∀ L : ℕ, 0 < L → |rem f₀ C a L| ≤ K / (L : ℝ) ^ 4

/-- The decrement with its remainder: `3(c_{2L} − c_L) ≤ (567/16) a/L² + (13107/256) K/L⁴`.
DERIVED: `13107/256 = 3 (16 + 17/16 + 1/256)` the remainder count; `567/16 = 3 · (63/4) · (3/4)` as in
`decrement_eq`; `3` the dimension of `su(2)`. -/
theorem decrement_le {f₀ C a K : ℝ} (hK : ∀ L : ℕ, 0 < L → |rem f₀ C a L| ≤ K / (L : ℝ) ^ 4)
    {L : ℕ} (hL : 0 < L) :
    3 * (cL (2 * L) - cL L) ≤ 567 / 16 * a / (L : ℝ) ^ 2 + 13107 / 256 * (K / (L : ℝ) ^ 4) := by
  rw [decrement_eq f₀ C a hL]
  have h1 := abs_le.mp (hK L hL)
  have h2 := abs_le.mp (hK (2 * L) (by omega))
  have h4 := abs_le.mp (hK (2 * (2 * L)) (by omega))
  have e2 : K / ((2 * L : ℕ) : ℝ) ^ 4 = K / (L : ℝ) ^ 4 / 16 := by push_cast; ring
  have e4 : K / ((2 * (2 * L) : ℕ) : ℝ) ^ 4 = K / (L : ℝ) ^ 4 / 256 := by push_cast; ring
  rw [e2] at h2
  rw [e4] at h4
  have hy : 0 ≤ K / (L : ℝ) ^ 4 := (abs_nonneg _).trans (hK L hL)
  linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2]

/-- **The Gaussian decrement is eventually negative at rate `L⁻²`.** -/
theorem decrement_neg (h : EllExpansion) :
    ∃ α : ℝ, 0 < α ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 0 < L →
      3 * (cL (2 * L) - cL L) ≤ -α / (L : ℝ) ^ 2 := by
  obtain ⟨f₀, C, a, K, ha, hK⟩ := h
  have hA : 0 < -(567 / 32) * a := by linarith
  refine ⟨-(567 / 32) * a, hA, ⌈52 * K / (-(567 / 32) * a)⌉₊ + 1, fun L hL0 hL => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLge : 52 * K / (-(567 / 32) * a) < L := by
    have : (⌈52 * K / (-(567 / 32) * a)⌉₊ : ℝ) + 1 ≤ L := by exact_mod_cast hL0
    linarith [Nat.le_ceil (52 * K / (-(567 / 32) * a))]
  have hKA : 52 * K < -(567 / 32) * a * (L : ℝ) ^ 2 := by
    have h1 : 52 * K < L * (-(567 / 32) * a) := (div_lt_iff₀ hA).mp hLge
    have hLL : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left hLL hA.le
    linarith
  have hb : 3 * (cL (2 * L) - cL L) ≤ 567 / 16 * a / (L : ℝ) ^ 2 + 52 * (K / (L : ℝ) ^ 4) := by
    have hy : 0 ≤ K / (L : ℝ) ^ 4 := (abs_nonneg _).trans (hK L hL)
    linarith [decrement_le hK hL]
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hu : 0 < 1 / (L : ℝ) ^ 2 := by positivity
  have hKu : 52 * K * (1 / (L : ℝ) ^ 2) ≤ -(567 / 32) * a := by
    rw [mul_one_div, div_le_iff₀ hL2]; linarith
  have h3 := mul_le_mul_of_nonneg_right hKu hu.le
  have e1 : 567 / 16 * a / (L : ℝ) ^ 2 = 567 / 16 * a * (1 / (L : ℝ) ^ 2) := by ring
  have e2 : 52 * (K / (L : ℝ) ^ 4) = 52 * K * (1 / (L : ℝ) ^ 2) * (1 / (L : ℝ) ^ 2) := by ring
  have e3 : -(-(567 / 32) * a) / (L : ℝ) ^ 2 = -(-(567 / 32) * a) * (1 / (L : ℝ) ^ 2) := by ring
  rw [e1, e2] at hb
  rw [e3]
  linarith

/-! ## The toron term -/

/-- **The toron term is controlled by the toron increment.** For `0 < x + B₀` and `B₀ ≤ B₁ ≤ B₂`,
`17 log(x+B₁) − log(x+B₂) − 16 log(x+B₀) ≤ 16 (B₁ − B₀)/(x + B₀)`. -/
theorem toron_term_le {x B₀ B₁ B₂ : ℝ} (h0 : 0 < x + B₀) (h01 : B₀ ≤ B₁) (h12 : B₁ ≤ B₂) :
    17 * Real.log (x + B₁) - Real.log (x + B₂) - 16 * Real.log (x + B₀)
      ≤ 16 * (B₁ - B₀) / (x + B₀) := by
  have h1 : 0 < x + B₁ := by linarith
  have hA : Real.log (x + B₁) - Real.log (x + B₀) ≤ (B₁ - B₀) / (x + B₀) := by
    rw [← Real.log_div h1.ne' h0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos h1 h0)
    rw [div_sub_one h0.ne'] at this
    calc _ ≤ (x + B₁ - (x + B₀)) / (x + B₀) := this
      _ = (B₁ - B₀) / (x + B₀) := by ring
  have hB : Real.log (x + B₁) ≤ Real.log (x + B₂) := Real.log_le_log h1 (by linarith)
  have e : 16 * (B₁ - B₀) / (x + B₀) = 16 * ((B₁ - B₀) / (x + B₀)) := by ring
  rw [e]
  linarith

/-! ## The open input and the conclusion -/

/-- **The weak-coupling Laplace asymptotic of the SU(2) window coupling (open input).** There are a
`w`-independent `F`, a toron sequence `B` (positive, nondecreasing, increments at most `θ 4^{−w}`), window
bounds `W β → ∞`, and a remainder `ρ` such that on windows `1 ≤ w ≤ W β`, `β > 1`,
`g β w = F β + 3 c_{2^w} + 16 log(x + B w) − log(x + B (w+1)) + ρ β w` with `x = (log β)/4`, and eventually
in `β` the remainder step `ρ β (w+1) − ρ β w` is at most `ε β · 4^{−w}` with `ε → 0`. `F`, `B` and `ρ` are
otherwise unconstrained, so the content is the step bound: on each window the large-`β` step of `g` is at most
the Gaussian decrement `3(c_{2^{w+1}} − c_{2^w})`. The one-sided bound admits the argued negative
running-coupling term `−(45/2) b log 2/β`.
DERIVED: `16`, `4`, `1/4` as in the module docstring; `1` the least window and `β > 1` where `log β > 0`;
`45/2 = (15/2) · 3` the `log β` coefficient of the defect, `b = 11/(6π²)` the one-loop coefficient of `SU(2)`
(argued, not used in a statement). -/
def ToronLaplace : Prop :=
  ∃ (F : ℝ → ℝ) (B : ℕ → ℝ) (ρ : ℝ → ℕ → ℝ) (ε : ℝ → ℝ) (W : ℝ → ℕ) (θ : ℝ),
    Monotone B ∧ (∀ w, 0 < B w) ∧ (∀ w, B (w + 1) - B w ≤ θ * (1 / 4) ^ w) ∧
    Tendsto ε atTop (𝓝 0) ∧ Tendsto W atTop atTop ∧
    (∀ β : ℝ, 1 < β → ∀ w : ℕ, 1 ≤ w → w ≤ W β →
      windowCoupling 2 β w = F β + 3 * cL (2 ^ w)
        + (16 * Real.log (Real.log β / 4 + B w) - Real.log (Real.log β / 4 + B (w + 1))) + ρ β w) ∧
    (∀ᶠ β in atTop, ∀ w : ℕ, 1 ≤ w → w + 1 ≤ W β → ρ β (w + 1) - ρ β w ≤ ε β * (1 / 4) ^ w)

/-- **The Gaussian decrement on every window**: `3(c_{2^{w+1}} − c_{2^w}) ≤ −α 4^{−w}`, `w ≥ 1`. A statement
about the explicit sums `ell`; `decrement_neg` gives it for `w` past a threshold from `EllExpansion`.
DERIVED: `3` the dimension of `su(2)`; `1/4 = 2⁻²` the `L⁻²` rate per doubling; `1` the least window. -/
def LatticeDecrement : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ w : ℕ, 1 ≤ w → 3 * (cL (2 ^ (w + 1)) - cL (2 ^ w)) ≤ -α * (1 / 4) ^ w

/-- **The window coupling decreases at large `β` on every window up to `W β`.** -/
theorem windowCoupling_decreasing (hT : ToronLaplace) (hc : LatticeDecrement) :
    ∃ W : ℝ → ℕ, Tendsto W atTop atTop ∧ ∀ᶠ β in atTop, ∀ w : ℕ, 1 ≤ w → w + 1 ≤ W β →
      windowCoupling 2 β (w + 1) < windowCoupling 2 β w := by
  obtain ⟨F, B, ρ, ε, W, θ, hmono, hpos, hinc, hε, hW, hdec, hρ⟩ := hT
  obtain ⟨α, hα, hcα⟩ := hc
  refine ⟨W, hW, ?_⟩
  have hθ : 0 ≤ θ := by
    have h := hinc 0
    have h0 := hmono (Nat.le_succ 0)
    simp only [pow_zero, mul_one] at h
    linarith
  have hεe : ∀ᶠ β in atTop, ε β < α / 2 := hε.eventually (gt_mem_nhds (half_pos hα))
  have hxe : ∀ᶠ β in atTop, 4 * (32 * θ / α + 1) < Real.log β :=
    Real.tendsto_log_atTop.eventually_gt_atTop _
  filter_upwards [hεe, hxe, hρ, eventually_gt_atTop (1 : ℝ)] with β hεβ hxβ hρβ hβ1 w hw hwW
  have hg1 := hdec β hβ1 (w + 1) (by omega) hwW
  have hg0 := hdec β hβ1 w hw (by omega)
  have hcw := hcα w hw
  have hρw := hρβ w hw hwW
  have hincw := hinc w
  have e2 : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := pow_succ 2 w
  rw [e2] at hg1 hcw
  have hq : 0 < (1 / 4 : ℝ) ^ w := by positivity
  have hx : 32 * θ / α + 1 < Real.log β / 4 := by linarith
  have hx0 : 0 < Real.log β / 4 := by
    have : 0 ≤ 32 * θ / α := div_nonneg (by linarith) hα.le
    linarith
  have hT := toron_term_le (x := Real.log β / 4) (B₀ := B w) (B₁ := B (w + 1)) (B₂ := B (w + 1 + 1))
    (by linarith [hpos w]) (hmono (Nat.le_succ w)) (hmono (Nat.le_succ (w + 1)))
  have hden : Real.log β / 4 ≤ Real.log β / 4 + B w := by linarith [hpos w]
  have hnum : 0 ≤ 16 * (B (w + 1) - B w) := by linarith [hmono (Nat.le_succ w)]
  have hT1 : 16 * (B (w + 1) - B w) / (Real.log β / 4 + B w) ≤ 16 * (B (w + 1) - B w) / (Real.log β / 4) :=
    div_le_div_of_nonneg_left hnum hx0 hden
  have hT2 : 16 * (B (w + 1) - B w) / (Real.log β / 4) ≤ 16 * (θ * (1 / 4) ^ w) / (Real.log β / 4) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith
  have h32 : 32 * θ < α * (Real.log β / 4) := by
    have h' : 32 * θ / α < Real.log β / 4 := by linarith
    have := (div_lt_iff₀ hα).mp h'
    linarith
  have hT3 : 16 * (θ * (1 / 4) ^ w) / (Real.log β / 4) ≤ α / 2 * (1 / 4) ^ w := by
    rw [div_le_iff₀ hx0]
    have := mul_lt_mul_of_pos_right h32 hq
    linarith
  have hεq : ε β * (1 / 4) ^ w < α / 2 * (1 / 4) ^ w := mul_lt_mul_of_pos_right hεβ hq
  rw [hg1, hg0]
  linarith [hT, hT1, hT2, hT3, hcw, hεq, hρw]

end MassGap.ToronDecrement

#print axioms MassGap.ToronDecrement.normSq_one_sub_exp
#print axioms MassGap.ToronDecrement.twisted_det_one_dim
#print axioms MassGap.ToronDecrement.det_prime_one_dim
#print axioms MassGap.ToronDecrement.cL_eq
#print axioms MassGap.ToronDecrement.decrement_eq
#print axioms MassGap.ToronDecrement.decrement_le
#print axioms MassGap.ToronDecrement.decrement_neg
#print axioms MassGap.ToronDecrement.toron_term_le
#print axioms MassGap.ToronDecrement.windowCoupling_decreasing
