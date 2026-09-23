import Mathlib

/-!
# Sign of the two-term Yang-Mills beta function (PAPER §5, §6, §12)

Six real-arithmetic facts about the two-term Callan-Symanzik beta function
`β(g) = -(b₀ g³) - b₁ g⁵`.

Two of them fix the sign of the pure-`SU(N)` coefficients at `N ≥ 1`: `11N/3 > 0` and `34N²/3 > 0`.
Two are stated for abstract positive `b₀`, `b₁`: at any `g > 0` the two-term expression is strictly
negative, hence nonzero. The remaining two instantiate the abstract pair at the `SU(N)` coefficients.

Scope: these are inequalities over `ℝ`. Nothing here defines a renormalisation-group flow, a
coupling, or a gauge theory; that `11N/3` and `34N²/3` are the beta-function coefficients of pure
`SU(N)` is the cited perturbative computation (Gross-Wilczek, Politzer) and is not formalised. The
two-term polynomial is taken as given, not derived, and no statement quantifies over `g ≤ 0`.
-/

namespace MassGap

/-- For a natural number `N` with `1 ≤ N`, the real `11 * N / 3` is strictly positive. This is the
one-loop coefficient `b₀` of pure `SU(N)` (PAPER §5); the identification is cited, not formalised.

DERIVED: `1` is the lower bound on `N` in the hypothesis; `0` is the comparison point of the
conclusion; `11` and `3` are the one-loop coefficient's numerator and denominator, quoted from the
cited computation. -/
theorem b0_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (11 * (N : ℝ)) / 3 := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

/-- For a natural number `N` with `1 ≤ N`, the real `34 * N ^ 2 / 3` is strictly positive. This is
the two-loop coefficient `b₁` of pure `SU(N)` (PAPER §5); the identification is cited, not
formalised.

DERIVED: `1` is the lower bound on `N` in the hypothesis; `0` is the comparison point of the
conclusion; `34`, the exponent `2` and `3` are the two-loop coefficient's numerator, power of `N`
and denominator, quoted from the cited computation. -/
theorem b1_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (34 * (N : ℝ) ^ 2) / 3 := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
  linarith

/-- For reals `b₀`, `b₁`, `g` all strictly positive, `-(b₀ * g ^ 3) - b₁ * g ^ 5 < 0` (PAPER §5-6).
Both terms are products of positives, so their negated sum is negative. The coefficients are
arbitrary positive reals here; nothing ties them to `SU(N)`.

DERIVED: `0` appears three times as the positivity threshold of `b₀`, `b₁` and `g`, and once as the
comparison point of the conclusion; the exponents `3` and `5` are the two terms' powers of `g`, fixed
by the two-term form of the beta function. -/
theorem beta_neg {b₀ b₁ g : ℝ} (hb0 : 0 < b₀) (hb1 : 0 < b₁) (hg : 0 < g) :
    -(b₀ * g ^ 3) - b₁ * g ^ 5 < 0 := by
  have h3 : 0 < b₀ * g ^ 3 := by positivity
  have h5 : 0 < b₁ * g ^ 5 := by positivity
  linarith

/-- For reals `b₀`, `b₁`, `g` all strictly positive, `-(b₀ * g ^ 3) - b₁ * g ^ 5 ≠ 0` (PAPER §6,
§12). Immediate from `beta_neg`: a strictly negative real is nonzero. Scope: the quantifier is over
`g > 0`, so this says nothing about a zero at `g = 0` or at negative `g`.

DERIVED: `0` appears three times as the positivity threshold of `b₀`, `b₁` and `g`, and once as the
value the expression is asserted to differ from; the exponents `3` and `5` are inherited from
`beta_neg`. -/
theorem no_interior_fixed_point {b₀ b₁ g : ℝ} (hb0 : 0 < b₀) (hb1 : 0 < b₁) (hg : 0 < g) :
    -(b₀ * g ^ 3) - b₁ * g ^ 5 ≠ 0 :=
  ne_of_lt (beta_neg hb0 hb1 hg)

/-- `beta_neg` instantiated at the pure-`SU(N)` coefficients (PAPER §5-6): for `1 ≤ N` and `g > 0`,
`-((11 * N / 3) * g ^ 3) - (34 * N ^ 2 / 3) * g ^ 5 < 0`. The positivity of the two coefficients
comes from `b0_pos` and `b1_pos`.

DERIVED: `1` is the lower bound on `N`; `11`, `3`, `34`, the exponent `2` and the second `3` are the
`SU(N)` coefficients quoted from the cited computation; the exponents `3` and `5` are the two terms'
powers of `g`; `0` is the positivity threshold of `g` and the comparison point of the conclusion. -/
theorem sun_beta_neg {N : ℕ} (hN : 1 ≤ N) {g : ℝ} (hg : 0 < g) :
    -((11 * (N : ℝ) / 3) * g ^ 3) - (34 * (N : ℝ) ^ 2 / 3) * g ^ 5 < 0 :=
  beta_neg (b0_pos hN) (b1_pos hN) hg

/-- `no_interior_fixed_point` instantiated at the pure-`SU(N)` coefficients (PAPER §6, §12): for
`1 ≤ N` and `g > 0`, `-((11 * N / 3) * g ^ 3) - (34 * N ^ 2 / 3) * g ^ 5 ≠ 0`. Scope: the two-term
polynomial has no zero in the open half-line `g > 0`; the endpoint `g = 0` is outside the statement.

DERIVED: `1` is the lower bound on `N`; `11`, `3`, `34`, the exponent `2` and the second `3` are the
`SU(N)` coefficients quoted from the cited computation; the exponents `3` and `5` are the two terms'
powers of `g`; `0` is the positivity threshold of `g` and the value the expression differs from. -/
theorem sun_no_interior_fixed_point {N : ℕ} (hN : 1 ≤ N) {g : ℝ} (hg : 0 < g) :
    -((11 * (N : ℝ) / 3) * g ^ 3) - (34 * (N : ℝ) ^ 2 / 3) * g ^ 5 ≠ 0 :=
  no_interior_fixed_point (b0_pos hN) (b1_pos hN) hg

end MassGap
