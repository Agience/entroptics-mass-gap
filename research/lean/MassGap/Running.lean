import Mathlib

/-!
# Asymptotic freedom forms the aperture (PAPER §5, §6, §12)

The one-loop and two-loop Callan-Symanzik coefficients of pure `SU(N)` Yang-Mills are both positive,
`b₀ = 11N/3 > 0` (Gross-Wilczek, Politzer) and `b₁ = 34N²/3 > 0`, so the two-term beta function
`β(g) = -(b₀ g³) - b₁ g⁵` is strictly negative for every `g > 0`: the coupling runs one way and the
flow has **no interior fixed point** (`β ≠ 0` for every `g > 0`). This is the sign content the
mass-gap argument uses: the running is one-signed, so the aperture forms for `SU(N)` (§5), and
`β ≠ 0` for every coupling is the §12 equivalent form of the gap. It also carries the weak-coupling
end of the confinement inequality `μ < κ₀`: with the running one-signed, `a²μ ~ (aΛ)² → 0` sits far
below the floor.

Only the SIGN is formalized here. That `b₀`, `b₁` are the physical beta-function coefficients is the
cited perturbative computation (Gross-Wilczek, Politzer).
-/

namespace MassGap

/-- **One-loop coefficient is positive** (PAPER §5): `b₀ = 11N/3 > 0` for pure `SU(N)`, `N ≥ 1`. -/
theorem b0_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (11 * (N : ℝ)) / 3 := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

/-- **Two-loop coefficient is positive** (PAPER §5): `b₁ = 34N²/3 > 0` for pure `SU(N)`, `N ≥ 1`. -/
theorem b1_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (34 * (N : ℝ) ^ 2) / 3 := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
  linarith

/-- **The two-term beta function is strictly negative** (PAPER §5-6): with both coefficients positive
and `g > 0`, `β(g) = -(b₀ g³) - b₁ g⁵ < 0`. The running has one sign. -/
theorem beta_neg {b₀ b₁ g : ℝ} (hb0 : 0 < b₀) (hb1 : 0 < b₁) (hg : 0 < g) :
    -(b₀ * g ^ 3) - b₁ * g ^ 5 < 0 := by
  have h3 : 0 < b₀ * g ^ 3 := by positivity
  have h5 : 0 < b₁ * g ^ 5 := by positivity
  linarith

/-- **No interior fixed point** (PAPER §6, §12): with both coefficients positive, the two-term beta
function never vanishes at a finite positive coupling, `β(g) ≠ 0` for every `g > 0`. The flow of pure
`SU(N)` runs one way and has no interior zero. This is the §12 equivalent form of the gap. -/
theorem no_interior_fixed_point {b₀ b₁ g : ℝ} (hb0 : 0 < b₀) (hb1 : 0 < b₁) (hg : 0 < g) :
    -(b₀ * g ^ 3) - b₁ * g ^ 5 ≠ 0 :=
  ne_of_lt (beta_neg hb0 hb1 hg)

/-- **Pure `SU(N)` beta function is strictly negative** (PAPER §5-6): instantiating the positive
coefficients `b₀ = 11N/3`, `b₁ = 34N²/3` gives `β(g) < 0` at every `g > 0`, for every `N ≥ 1`. -/
theorem sun_beta_neg {N : ℕ} (hN : 1 ≤ N) {g : ℝ} (hg : 0 < g) :
    -((11 * (N : ℝ) / 3) * g ^ 3) - (34 * (N : ℝ) ^ 2 / 3) * g ^ 5 < 0 :=
  beta_neg (b0_pos hN) (b1_pos hN) hg

/-- **Pure `SU(N)` has no interior fixed point** (PAPER §6, §12): the beta function is nonzero at
every `g > 0` for every `N ≥ 1`. The flow never stops at an interior coupling: no Coulomb / free
fixed point in the interior, the §12 equivalent form of the gap. -/
theorem sun_no_interior_fixed_point {N : ℕ} (hN : 1 ≤ N) {g : ℝ} (hg : 0 < g) :
    -((11 * (N : ℝ) / 3) * g ^ 3) - (34 * (N : ℝ) ^ 2 / 3) * g ^ 5 ≠ 0 :=
  no_interior_fixed_point (b0_pos hN) (b1_pos hN) hg

end MassGap
