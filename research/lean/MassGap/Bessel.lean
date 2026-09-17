import Mathlib

/-!
# C-2: the leading character ratio `r = I₂/I₁ > 0` from the modified-Bessel series

Mathlib carries no modified Bessel `Iν`, so we give the elementary power series for integer order,

    `I_n(x) = Σ_{k≥0} (x/2)^{2k+n} / (k! (k+n)!)`,

prove it is **summable** (termwise comparison with the exponential series `Σ ((x/2)²)^k/k! = exp((x/2)²)`)
and **strictly positive** for `x > 0` (every term is positive), hence `r = I₂/I₁ > 0` (`ym_ratio_pos`, a
theorem); the only input is that the Bessel argument (a coupling scale) is positive.

**AND BOUNDED ABOVE BY `x/4`** (`ratio_le_quarter`), termwise and with no numeric input, which is what
makes the strong-coupling threshold `β² < ½ log 3` a theorem rather than a certified interval.
-/

namespace MassGap.Bessel

open scoped BigOperators Nat

/-- The `k`-th term of the modified Bessel series `I_n(x)`: `(x/2)^{2k+n} / (k! (k+n)!)`. -/
noncomputable def besselTerm (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (x / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * ((k + n).factorial : ℝ))

/-- The modified Bessel function of the first kind at integer order `n`,
`I_n(x) = Σ_k (x/2)^{2k+n}/(k!(k+n)!)`. -/
noncomputable def besselI (n : ℕ) (x : ℝ) : ℝ := ∑' k, besselTerm n x k

theorem besselTerm_nonneg (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 ≤ x) : 0 ≤ besselTerm n x k := by
  unfold besselTerm
  apply div_nonneg
  · exact pow_nonneg (by linarith) _
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem besselTerm_pos (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 < x) : 0 < besselTerm n x k := by
  unfold besselTerm
  apply div_pos
  · exact pow_pos (by linarith) _
  · exact mul_pos (by exact_mod_cast k.factorial_pos) (by exact_mod_cast (k + n).factorial_pos)

/-- Each term is bounded by the corresponding term of `(x/2)^n · exp((x/2)²)` (drop the `(k+n)!` factor,
which is `≥ 1`). -/
theorem besselTerm_le (n : ℕ) (x : ℝ) (k : ℕ) (hx : 0 ≤ x) :
    besselTerm n x k ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (k.factorial : ℝ) := by
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have hnum : (x / 2) ^ (2 * k + n) = (x / 2) ^ n * ((x / 2) ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  unfold besselTerm
  rw [hnum, ← div_div]
  apply div_le_self
  · exact div_nonneg (mul_nonneg (pow_nonneg hx2 n) (pow_nonneg (sq_nonneg (x / 2)) k))
      (Nat.cast_nonneg _)
  · have h1 : (1 : ℕ) ≤ (k + n).factorial := (k + n).factorial_pos
    exact_mod_cast h1

theorem besselI_summable (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : Summable (besselTerm n x) := by
  have hg : Summable (fun k => (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (k.factorial : ℝ)) := by
    have h := (Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left ((x / 2) ^ n)
    simpa [mul_div_assoc] using h
  exact Summable.of_nonneg_of_le (fun k => besselTerm_nonneg n x k hx)
    (fun k => besselTerm_le n x k hx) hg

/-- **The modified Bessel `I_n` is strictly positive for a positive argument.** Every series term is
positive (`besselTerm_pos`) and the series is summable, so its `tsum` is positive. -/
theorem besselI_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < besselI n x := by
  unfold besselI
  exact (besselI_summable n x hx.le).tsum_pos
    (fun k => besselTerm_nonneg n x k hx.le) 0 (besselTerm_pos n x 0 hx)

/-- **The leading character ratio `I₂/I₁` is positive** for a positive argument — the C-2 content. -/
theorem ratio_pos {x : ℝ} (hx : 0 < x) : 0 < besselI 2 x / besselI 1 x :=
  div_pos (besselI_pos 2 hx) (besselI_pos 1 hx)

/-! ### The leading character ratio is at most `x/4`, and the strong-coupling threshold is exact

`Apriori.apriori_A1_strong` gives `μ β < κ₀` below a threshold `β⋆` defined by `2 β⋆ r(β⋆) = κ₀`, and
until now that threshold's VALUE came from a numeric certificate: `r(β⋆) ∈ [0.182, 0.184]` computed in
Python, with Lean checking only the interval arithmetic around it. The bound below removes the
certificate. It is termwise and elementary, and it makes the threshold an exact inequality between
`β` and `log 3` with no numeral in it at all. -/

/-- **TERMWISE: the `I₂` term is at most `x/4` times the `I₁` term.** The two terms differ by one factor
of `x/2` upstairs and one factor of `k+2` downstairs, and `k + 2 ≥ 2`. That `2` is the ORDER GAP
between `I₂` and `I₁` — the two leading characters the expansion compares — so the `4` below is
`2 · 2`: one from the Bessel argument's own halving, one from the order gap.

DERIVED: `2` is the order gap `2 - 1 + 1` between the two characters, which is what `(k+n)!` advances
by; `4` is that `2` times the `2` of `x/2` in the series' own argument. Neither is chosen. -/
theorem besselTerm_two_le_quarter (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    besselTerm 2 x k ≤ (x / 4) * besselTerm 1 x k := by
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hf1 : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast (k + 1).factorial_pos
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hfac : (((k + 2).factorial : ℕ) : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
    have : (k + 2).factorial = (k + 2) * (k + 1).factorial := Nat.factorial_succ (k + 1)
    rw [this]; push_cast; ring
  have key : besselTerm 2 x k = ((x / 2) / ((k : ℝ) + 2)) * besselTerm 1 x k := by
    unfold besselTerm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ, hfac]
    field_simp
  rw [key]
  refine mul_le_mul_of_nonneg_right ?_ (besselTerm_nonneg 1 x k hx)
  rw [div_le_iff₀ hk2]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- **`I₂(x) ≤ (x/4) · I₁(x)`.** Summed termwise. -/
theorem besselI_two_le_quarter (x : ℝ) (hx : 0 ≤ x) :
    besselI 2 x ≤ (x / 4) * besselI 1 x := by
  unfold besselI
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun k => besselTerm_two_le_quarter x hx k)
    (besselI_summable 2 x hx) ((besselI_summable 1 x hx).mul_left _)

/-- **THE LEADING CHARACTER RATIO IS AT MOST `x/4`**, with no numeric input. It is tight as `x → 0`,
which is the regime the strong-coupling bound is used in. -/
theorem ratio_le_quarter {x : ℝ} (hx : 0 < x) : besselI 2 x / besselI 1 x ≤ x / 4 := by
  rw [div_le_iff₀ (besselI_pos 1 hx)]
  exact besselI_two_le_quarter x hx.le

#print axioms besselTerm_two_le_quarter
#print axioms besselI_two_le_quarter
#print axioms ratio_le_quarter

/-- **THE CHARACTER BOUND IS BELOW THE FLOOR EXACTLY WHEN `β² < ½ log 3`.** Substituting
`r(β) ≤ β/4` into the strong-coupling bound `2 β r(β)` gives `β²/2`, so it sits under
`κ₀ = ¼ log 3` precisely when `β² < ½ log 3`.

**THE THRESHOLD IS NOW A THEOREM AND CARRIES NO NUMERAL.** It is an inequality between the coupling
and the entropy floor's own `log 3` — not a certified interval, not a fitted constant, and nothing to
regenerate. The `½` and `¼` are the `2` and `4` of `ratio_le_quarter` and `κ₀` respectively, both
already derived. -/
theorem two_mul_ratio_lt_kappa0 {β : ℝ} (hβ : 0 < β)
    (hlt : β ^ 2 < (1 / 2) * Real.log 3) :
    2 * β * (besselI 2 β / besselI 1 β) < (1 / 4) * Real.log 3 := by
  have hr := ratio_le_quarter hβ
  have h1 : 2 * β * (besselI 2 β / besselI 1 β) ≤ 2 * β * (β / 4) :=
    mul_le_mul_of_nonneg_left hr (by linarith)
  nlinarith [h1, hlt]

/-- **A1, STRONG-COUPLING SIDE, WITH THE THRESHOLD DERIVED.** Given the character bound
`μ β ≤ 2 β r(β)` — the cited cluster expansion, still the one input here — the tension is below the
counting floor for EVERY coupling with `β² < ½ log 3`. No certificate, no interval, no numeral.

What remains cited on this side is `hbound` alone, and it is the same character expansion the
reflection-positivity axiom needs, so proving it once serves both. -/
theorem strong_coupling_below_threshold {μ : ℝ → ℝ} {β : ℝ}
    (hβ : 0 ≤ β) (hlt : β ^ 2 < (1 / 2) * Real.log 3)
    (hbound : μ β ≤ 2 * β * (besselI 2 β / besselI 1 β)) :
    μ β < (1 / 4) * Real.log 3 := by
  rcases eq_or_lt_of_le hβ with rfl | hpos
  · have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    simp only [mul_zero, zero_mul] at hbound
    linarith
  · exact lt_of_le_of_lt hbound (two_mul_ratio_lt_kappa0 hpos hlt)

#print axioms two_mul_ratio_lt_kappa0
#print axioms strong_coupling_below_threshold

end MassGap.Bessel
