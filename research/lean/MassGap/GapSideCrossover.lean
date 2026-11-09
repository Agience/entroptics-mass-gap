import Mathlib
import MassGap.CompactGauge
import MassGap.HolderBondMoving
import MassGap.MovedTorusDecimation

/-!
# MassGap.GapSideCrossover — the side arithmetic of the vortex anti-diagonal

Step `i` of the vortex anti-diagonal (`GapSideVortexAntiDiagonal.vortex_antiDiagonal_crossing`) reads the
weight `W_i` on the torus of side `m_i = 2^{k+2−i}`. This module holds the configuration measure of the
side-`m` torus (`muL`), the continuity of the plaquette action on it (`continuous_fAct_of`), and the side
arithmetic of the doubling: for `i < k`, `2^{k+2−i} = 2 · 2^{k+1−i}` (`side_eq`) and `2^{k+1−i}` is even and
at least `2` (`side_even`).

DERIVED (module-wide): `4` the number of moves of one step (the dimension); `2` in `2 * n` the doubling of
one step; `k + 2` the chain-end side `4 = 2²` of `vortex_antiDiagonal_crossing`.
-/

noncomputable section

namespace MassGap.GapSideCrossover

open MeasureTheory Set Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ElectricStep
  MassGap.MovedTorusDecimation

/-! ## 1. The chain fields: the configuration measure and continuity -/

section ChainFields

/-- The configuration measure of the side-`m` torus. -/
abbrev muL (m : ℕ) : Measure (TLink 4 m → SU 2) := Measure.pi fun _ : TLink 4 m => probHaar (SU 2)

theorem continuous_fAct_of {m : ℕ} {Φ : TPlaq 4 m → SU 2 → ℝ} (hΦ : ∀ q, Continuous (Φ q)) :
    Continuous (fAct Φ : (TLink 4 m → SU 2) → ℝ) := by
  unfold fAct
  exact continuous_finsetSum _ fun q _ => (hΦ q).comp (continuous_thol q)

end ChainFields

/-! ## 2. The side arithmetic along the anti-diagonal -/

section Assembly

theorem side_eq (k i : ℕ) (hi : i < k) : 2 ^ (k + 2 - i) = 2 * 2 ^ (k + 1 - i) := by
  rw [show k + 2 - i = (k + 1 - i) + 1 by omega, pow_succ]; ring

theorem side_even (k i : ℕ) (hi : i < k) : Even (2 ^ (k + 1 - i)) ∧ 2 ≤ 2 ^ (k + 1 - i) := by
  refine ⟨(Nat.even_pow' (by omega)).mpr even_two, ?_⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1 - i) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Assembly

end MassGap.GapSideCrossover

end
