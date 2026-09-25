import Mathlib
import MassGap.SpectralGap
import MassGap.ClayCapstone

/-!
# The Wilson transfer gap from the reads, at every coupling

`SpectralGap.opT_gap_of_reads` on the gauge-invariant GNS transfer operator of `SU(N)` Wilson theory on
`ℤ⁴`, `ClayCapstone.wilsonGaugeInvMixCubeData`. `PositiveTransfer` there is
`GaugeInvariantAlgebra.positiveTransfer_gaugeInv` of
`ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit`, which holds at every `β ≥ 0`. So the
gap statement holds at every coupling at which the infinite-volume state exists and the reads of the
vectors orthogonal to the vacuum clear the floor — no strong-coupling condition enters.
-/

namespace MassGap.WilsonReadGap

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.ClayCapstone MassGap.ReflectionHalfSpace

variable {N : ℕ}

/-- **The Wilson transfer gap from the reads, at every `β ≥ 0`.** For `SU(N)` Wilson theory on `ℤ⁴`
at any `β ≥ 0` with infinite-volume state `ν` (the `atTop` limit of the free mixed-cube states), if
every vector of the gauge-invariant GNS space orthogonal to the vacuum reads below the floor at
aperture `2k + 1`, then that complement is contracted at rate `ρ < 1` with
`ρ^{k+1} = 12(1 − 3^{−1/4})/8`. `ReadsClear` is the gap stated as a read (see `SpectralGap`); the
complement is non-zero at `2 ≤ N` (`PlaneVariance.exists_ne_zero_orth_vacuum`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`, the lower end of `β` and of
`ρ`, and the orthogonality; `1` is the all-identity boundary configuration of the free states and the
upper bound on `ρ`; `2` and `1` spell the aperture `2k + 1`; `12`, `8`, `3`, `1` and `4` spell the
cap. -/
theorem wilson_gap_of_reads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ)
    (hread : SpectralGap.ReadsClear (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
        (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : H (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
        inner ℂ (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
          (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) u = 0 →
        ∀ m : ℕ, ‖((opT (wilsonGaugeInvMixCubeData τ p hN β ν htend)) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  SpectralGap.opT_gap_of_reads _
    (MassGap.GaugeInvariantAlgebra.positiveTransfer_gaugeInv τ p ν
      (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
        (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
      (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
        (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
      (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
        (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
        (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))
      (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ ν htend))
    k hread

#print axioms wilson_gap_of_reads

end MassGap.WilsonReadGap
