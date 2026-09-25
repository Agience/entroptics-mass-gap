import Mathlib
import MassGap.StrongCouplingSharp

/-!
# MassGap.PeriodicStrongCouplingSharp — the periodic corollaries at the recounted rate

`StrongCouplingSharp.periodic_gapAt_strong_coupling'` gives `β₁ > 0` such that at every `0 < β < β₁`
the periodic data has `TransferGap.GapAt` at rate `coreRate' 64 β` with `0 < coreRate' 64 β < 1`;
its witness is `1/1400` (`StrongCouplingSharp.coreRate'_lt_one_of_le`). This file reads it through
the three consumers `PeriodicStrongCoupling` reads `periodic_gapAt_strong_coupling` through:

* `periodic_clayGapAt_strong_coupling'` — `PeriodicContent.PeriodicClayGapAt` at `2 ≤ N`, through
  `GapStep.periodic_clayGapAt_of_gapAt`;
* `periodic_torusLagClear_strong_coupling'` — `ChessboardRead.TorusLagClear` at every lag, through
  `WeakCouplingWindow.torusLagClear_of_gapAt`;
* `periodic_tower_base'` — the base `GapStep.periodic_clay_tower` takes, at every physical rate
  `M ≤ −log (coreRate' 64 β) / aRun N β`, through `GapStep.gapAt_mono`.

Each proof is its `PeriodicStrongCoupling` counterpart's with `periodic_gapAt_strong_coupling'` in
place of `periodic_gapAt_strong_coupling`.
-/

namespace MassGap.PeriodicStrongCouplingSharp

open MassGap

section Headline

variable {N : ℕ}

/-- **`PeriodicClayGapAt` at strong coupling, at the recounted rate.** At `2 ≤ N` there is `β₀ > 0`
such that at every `0 < β < β₀`, `PeriodicContent.PeriodicClayGapAt τ p hN β (coreRate' 64 β)`:
`StrongCouplingSharp.periodic_gapAt_strong_coupling'` and `GapStep.periodic_clayGapAt_of_gapAt`.

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`); the `4` in `Fin 4` is the spacetime dimension; `2` is the least rank with a non-zero Haar
variance of the real trace (`GapStep.periodic_clayGapAt_of_gapAt`'s); `0` is the excluded colour count
in `hN` and the lower end of `β₀` and `β`. -/
theorem periodic_clayGapAt_strong_coupling' (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ →
      PeriodicContent.PeriodicClayGapAt τ p hN β (StrongCouplingSharp.coreRate' (16 * 4) β) := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongCouplingSharp.periodic_gapAt_strong_coupling' (N := N) τ p hN
  exact ⟨β₀, hβ₀, fun β hβ hβb =>
    GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ.le (h β hβ hβb).1 (h β hβ hβb).2.1
      (h β hβ hβb).2.2⟩

#print axioms periodic_clayGapAt_strong_coupling'

/-- **`TorusLagClear` at strong coupling, at every lag, at the recounted rate.** There is `β₀ > 0`
such that at every `0 < β < β₀` and every lag `m`,
`ChessboardRead.TorusLagClear τ p hN β m (coreRate' 64 β)`:
`StrongCouplingSharp.periodic_gapAt_strong_coupling'` and `WeakCouplingWindow.torusLagClear_of_gapAt`.

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`); the `4` in `Fin 4` is the spacetime dimension; `0` is the excluded colour count in `hN` and the
lower end of `β₀` and `β`. -/
theorem periodic_torusLagClear_strong_coupling' (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ → ∀ m : ℕ,
      ChessboardRead.TorusLagClear τ p hN β m (StrongCouplingSharp.coreRate' (16 * 4) β) := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongCouplingSharp.periodic_gapAt_strong_coupling' (N := N) τ p hN
  exact ⟨β₀, hβ₀, fun β hβ hβb m =>
    WeakCouplingWindow.torusLagClear_of_gapAt τ p hN β (h β hβ hβb).1.le (h β hβ hβb).2.2 m⟩

#print axioms periodic_torusLagClear_strong_coupling'

/-- **The base of the coupling tower, at the recounted rate.** At `1 ≤ N` there is `β₀ > 0` such
that at every `0 < β < β₀` and every `M ≤ −log (coreRate' 64 β) / aRun N β`, the periodic data has
`GapAt` at rate `e^{−M·aRun N β}` — the base `GapStep.periodic_clay_tower` takes, at physical rate `M`
(`StrongCouplingSharp.periodic_gapAt_strong_coupling'`, `GapStep.gapAt_mono`:
`coreRate' 64 β ≤ e^{−M·aRun N β}`).

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`); the `4` in `Fin 4` is the spacetime dimension; `1` is the least colour count, for
`AsymptoticScaling.aRun_pos`; `0` is the excluded colour count in `hN` and the lower end of `β₀` and
`β`. -/
theorem periodic_tower_base' (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ → ∀ M : ℝ,
      M ≤ -Real.log (StrongCouplingSharp.coreRate' (16 * 4) β) / AsymptoticScaling.aRun N β →
      TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
        (Real.exp (-(M * AsymptoticScaling.aRun N β))) := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongCouplingSharp.periodic_gapAt_strong_coupling' (N := N) τ p hN
  refine ⟨β₀, hβ₀, fun β hβ hβb M hM => ?_⟩
  obtain ⟨hc0, _, hg⟩ := h β hβ hβb
  have ha : 0 < AsymptoticScaling.aRun N β := AsymptoticScaling.aRun_pos hN1 hβ
  have hMa : M * AsymptoticScaling.aRun N β
      ≤ -Real.log (StrongCouplingSharp.coreRate' (16 * 4) β) :=
    (le_div_iff₀ ha).mp hM
  have hle : StrongCouplingSharp.coreRate' (16 * 4) β
      ≤ Real.exp (-(M * AsymptoticScaling.aRun N β)) := by
    rw [← Real.exp_log hc0]
    exact Real.exp_le_exp.mpr (by linarith)
  exact GapStep.gapAt_mono _ hc0.le hle hg

#print axioms periodic_tower_base'

end Headline

end MassGap.PeriodicStrongCouplingSharp
