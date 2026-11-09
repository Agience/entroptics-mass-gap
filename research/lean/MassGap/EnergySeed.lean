import Mathlib
import MassGap.EffectiveCoupling

/-!
# MassGap.EnergySeed — the seed as the integral of the finite-size mean action

The 2D O(3) model obtains its doubling bound `0 ≤ 4 log Z(n,w) − log Z(2n,2w) ≤ C(…)e^{−c min(n,w)/X(b)}`
by integrating the coupling from `0` to `b`: the derivative of the doubling difference is the
difference of the normalised bond sums on the two tori, and a mixing estimate that holds uniformly for
every strength in `[0, b]` makes that difference small at every intermediate coupling (OpenAI, *The
canonical massive continuum limit of the two-dimensional O(3) model*, Oct 4 2026, Prop.
"Preliminary mixing and rectangular doubling", last paragraph of its proof). This module carries that
step to the 4D `SU(N)` Wilson defect.

* `finiteSize N n β = ⟨S⟩_{2n} − 16 ⟨S⟩_n`, the finite-size part of the mean Wilson action
  (`EffectiveCoupling.hasDerivAt_defectW`: it is the β-derivative of `defectW N β n`).
* `defectW_le_of_budget` / `le_defectW_of_budget`: a budget `Φ` whose derivative bounds the
  finite-size part from above (below) on `[a, b)`, and which bounds the defect at `a`, bounds it on all
  of `[a, b]`.
* `defectW_le_of_finiteSize`: from zero coupling (`defectW N 0 n = 0`), `finiteSize ≤ ε` on `[0, β)`
  gives `defectW N β n ≤ ε β`.
* `EnergySeedFrequent N`: frequently in `β`, some dyadic side `2ᵇ`, `b ≥ 1`, has finite-size part at
  most `1/(1000 β)` at every coupling in `[0, β)`.
* `defectW_log_growth`: a Coulomb-type finite-size part, `finiteSize ≥ κ/x` on `[a, β)` with `0 < a`,
  forces `defectW N β n ≥ defectW N a n + κ (log β − log a)`. Equipartition of `G`-valued Gaussian
  modes gives `κ = (dim G)·45/2` on boxes far below the correlation length (`3L⁴ − 3` physical modes per
  colour, and `(3·16n⁴ − 3) − 16(3n⁴ − 3) = 45`); that reading is not built.

The exact identity `defectW N β n = ∫₀^β finiteSize` is the seed restated. What the module adds is the
pointwise form: a bound on a local observable's volume dependence at each coupling below `β`, the form
a clustering estimate uniform in the coupling supplies.

DERIVED (module-wide): `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the
doubling; `1/1000` the sharp seed; `0` the coupling at which the defect vanishes; `1` the least dyadic
exponent of `EnergySeedFrequent`.
-/

noncomputable section

namespace MassGap.EnergySeed

open Real Filter Topology Set MassGap MassGap.ZoomSelfScale MassGap.EffectiveCoupling

variable {N : ℕ}

/-- The finite-size part of the mean Wilson action, `⟨S⟩_{2n} − 16 ⟨S⟩_n`.
DERIVED: `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the doubling. -/
def finiteSize (N n : ℕ) (β : ℝ) : ℝ :=
  meanAction N (fun _ => 2 * n) β - 16 * meanAction N (fun _ => n) β

/-- `d/dβ defectW N β n = finiteSize N n β`. -/
theorem hasDerivAt_defectW' (hN : N ≠ 0) (n : ℕ) (β : ℝ) :
    HasDerivAt (fun x => defectW N x n) (finiteSize N n β) β :=
  hasDerivAt_defectW hN n β

/-- The defect vanishes at zero coupling. -/
theorem defectW_zero (N n : ℕ) : defectW N 0 n = 0 :=
  SeedZeroCoupling.defect_at_zero N n

/-- **Upper budget.** If `Φ` bounds the defect at `a` and `Φ' ≥ finiteSize` on `[a, b)`, then `Φ`
bounds the defect on `[a, b]`. -/
theorem defectW_le_of_budget (hN : N ≠ 0) {n : ℕ} {a b : ℝ} {Φ φ : ℝ → ℝ}
    (ha : defectW N a n ≤ Φ a) (hΦ : ∀ x ∈ Icc a b, HasDerivAt Φ (φ x) x)
    (hfs : ∀ x ∈ Ico a b, finiteSize N n x ≤ φ x) :
    ∀ x ∈ Icc a b, defectW N x n ≤ Φ x :=
  image_le_of_deriv_right_le_deriv_boundary (f := fun x => defectW N x n) (f' := finiteSize N n)
    (fun x _ => (hasDerivAt_defectW' hN n x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_defectW' hN n x).hasDerivWithinAt)
    ha (fun x hx => (hΦ x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hΦ x (Ico_subset_Icc_self hx)).hasDerivWithinAt) hfs

/-- **Lower budget.** If `Φ` is below the defect at `a` and `Φ' ≤ finiteSize` on `[a, b)`, then `Φ`
stays below the defect on `[a, b]`. -/
theorem le_defectW_of_budget (hN : N ≠ 0) {n : ℕ} {a b : ℝ} {Φ φ : ℝ → ℝ}
    (ha : Φ a ≤ defectW N a n) (hΦ : ∀ x ∈ Icc a b, HasDerivAt Φ (φ x) x)
    (hfs : ∀ x ∈ Ico a b, φ x ≤ finiteSize N n x) :
    ∀ x ∈ Icc a b, Φ x ≤ defectW N x n :=
  image_le_of_deriv_right_le_deriv_boundary (f := Φ) (f' := φ)
    (fun x hx => (hΦ x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hΦ x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    ha (fun x _ => (hasDerivAt_defectW' hN n x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_defectW' hN n x).hasDerivWithinAt) hfs

/-- **The seed from the finite-size energy.** From zero coupling, a finite-size part at most `ε` at
every coupling in `[0, β)` bounds the defect at `β` by `ε β`. -/
theorem defectW_le_of_finiteSize (hN : N ≠ 0) {n : ℕ} {β ε : ℝ} (hβ : 0 ≤ β)
    (h : ∀ x ∈ Ico 0 β, finiteSize N n x ≤ ε) : defectW N β n ≤ ε * β := by
  have hd : ∀ x ∈ Icc (0 : ℝ) β, HasDerivAt (fun y => ε * y) ε x := fun x _ => by
    simpa using (hasDerivAt_id' x).const_mul ε
  exact defectW_le_of_budget hN (Φ := fun y => ε * y) (φ := fun _ => ε)
    (by rw [defectW_zero]; simp) hd h β ⟨hβ, le_rfl⟩

/-- **The energy form of the frequent seed**: frequently in `β`, some dyadic side `2ᵇ`, `b ≥ 1`, has
finite-size part at most `1/(1000 β)` at every coupling in `[0, β)`.
DERIVED: `1/1000` the sharp seed of `DoublingSharp`, spread over `[0, β)` by `defectW_le_of_finiteSize`;
`1` the least dyadic exponent; `2` the dyadic base. -/
def EnergySeedFrequent (N : ℕ) : Prop :=
  ∃ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ ∀ x ∈ Ico 0 β, finiteSize N (2 ^ b) x ≤ 1 / (1000 * β)

/-- **A Coulomb-type finite-size energy forces logarithmic growth.** If `finiteSize ≥ κ/x` on `[a, β)`
with `0 < a ≤ β`, the defect at `β` exceeds the defect at `a` by at least `κ (log β − log a)`. -/
theorem defectW_log_growth (hN : N ≠ 0) {n : ℕ} {a β κ : ℝ} (ha : 0 < a) (haβ : a ≤ β)
    (h : ∀ x ∈ Ico a β, κ * x⁻¹ ≤ finiteSize N n x) :
    defectW N a n + κ * (Real.log β - Real.log a) ≤ defectW N β n := by
  have hd : ∀ x ∈ Icc a β, HasDerivAt (fun y => defectW N a n + κ * (Real.log y - Real.log a))
      (κ * x⁻¹) x := fun x hx => by
    have hx : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
    exact (((Real.hasDerivAt_log hx).sub_const (Real.log a)).const_mul κ).const_add _
  exact le_defectW_of_budget hN (Φ := fun y => defectW N a n + κ * (Real.log y - Real.log a))
    (φ := fun x => κ * x⁻¹) (by simp) hd h β ⟨haβ, le_rfl⟩

end MassGap.EnergySeed

#print axioms MassGap.EnergySeed.defectW_le_of_budget
#print axioms MassGap.EnergySeed.le_defectW_of_budget
#print axioms MassGap.EnergySeed.defectW_le_of_finiteSize
#print axioms MassGap.EnergySeed.defectW_log_growth
