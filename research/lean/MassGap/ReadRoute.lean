import Mathlib
import MassGap.WilsonReadGap
import MassGap.FreeLimit
import MassGap.PlaneVariance
import MassGap.GNSCompare
import MassGap.StrongCouplingGap
import MassGap.ContinuumE

/-!
# The transfer gap at every coupling: the cluster expansion below the cut, the reads above it

`wilson_gaugeInv_clay_gap_of_reads` turns the reads into the Clay spectral statement on the
gauge-invariant `SU(N)` Wilson transfer operator on `ℤ⁴`: `SpectralGap.opT_gap_of_reads` at one step
is a contraction of the vacuum complement, `GNSCompare.gapAt_iff_opT_contracts` makes it
`TransferGap.GapAt`, and `ClayCapstone.wilson_gaugeInv_clay_gap_of_gapAt` gives the spectrum.

`ClayGapAt` is the gap at one coupling: the spectral statement, `opT` contracting every vector of the
completion orthogonal to the vacuum by `ρ < 1`, and a non-zero vector of the GNS space orthogonal to
the vacuum. The contraction makes `1` a simple eigenvalue; the spectral conjuncts alone hold for the
identity on any space of dimension at least `2`.

`wilson_gaugeInv_mass_gap_every_coupling` covers every `β > 0`: where `coreRate 64 β < 1` the cluster
expansion supplies the state, the spectrum (`FreeLimit.wilson_gaugeInv_mass_gap_lattice`) and the
contraction (`gapAt_of_strong`); elsewhere the single hypothesis `hweak` supplies the infinite-volume
state and an aperture at which every vector orthogonal to the vacuum reads below the floor, and
`gapAt_of_reads` turns the reads into the contraction. At every coupling the vacuum complement is
non-zero (`PlaneVariance.exists_ne_zero_orth_vacuum`, `2 ≤ N`). `hweak` is asked only above the cut;
it is the whole of the weak-coupling input.
-/

namespace MassGap.ReadRoute

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.ClayCapstone MassGap.ReflectionHalfSpace

variable {N : ℕ}

/-- **The reads give `TransferGap.GapAt`, on any transfer data with positive transfer.** If every
vector orthogonal to the vacuum reads below the floor at aperture `2k + 1`, there is `0 < ρ < 1` with
`ρ^{k+1} = 12(1 − 3^{−1/4})/8` and `GapAt D ρ`: `SpectralGap.opT_gap_of_reads` at one step, through
`GNSCompare.gapAt_iff_opT_contracts`.

DERIVED: `0` and `1` bracket `ρ`; `2` and `1` spell the aperture `2k + 1`, and `1` is also the `+ 1`
of `k + 1`; `12`, `8`, `3`, `1` and `4` spell the cap. -/
theorem gapAt_of_reads {A : Type*} [AddCommGroup A] [Module ℝ A] (D : TransferData A)
    (hP : PositiveTransfer D) (k : ℕ)
    (hread : SpectralGap.ReadsClear (opT D) (Omega D.toReflForm D.vac) k) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      MassGap.TransferGap.GapAt D ρ := by
  obtain ⟨ρ, hρ0, hρ1, hρk, hdec⟩ := MassGap.SpectralGap.opT_gap_of_reads D hP k hread
  obtain ⟨hc0, _⟩ := MassGap.SpectralGap.cap_pos_lt_one
  have hρpos : 0 < ρ := by
    rcases hρ0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow (Nat.succ_ne_zero k)] at hρk
      linarith
  refine ⟨ρ, hρpos, hρ1, hρk, (MassGap.GNSCompare.gapAt_iff_opT_contracts D hρ0).mpr ?_⟩
  intro y hy
  have h1 := hdec y hy 1
  rwa [pow_one, pow_one] at h1

#print axioms gapAt_of_reads

/-- **The reads give the Clay spectral statement on the Wilson transfer operator, at any `β ≥ 0`.**
If every vector orthogonal to the vacuum reads below the floor at aperture `2k + 1`, there is
`0 < ρ < 1` with `ρ^{k+1} = 12(1 − 3^{−1/4})/8` such that `opT` is self-adjoint, `−log ρ > 0`, its
spectrum lies in `{1} ∪ [0, ρ]`, and `1` is its largest element.

Scope: these conjuncts do not make `1` a simple eigenvalue; `clayGapAt_of_reads` adds the contraction
of the vacuum complement that does, and a non-zero vector orthogonal to the vacuum.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`, the lower end of `β`, of `ρ`
and of the spectrum, and the sign of the gap; `1` is the all-identity boundary configuration of the
free states, the vacuum eigenvalue and the upper bound on `ρ`; `2` and `1` spell the aperture
`2k + 1`; `12`, `8`, `3`, `1` and `4` spell the cap. -/
theorem wilson_gaugeInv_clay_gap_of_reads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
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
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))) 1 := by
  obtain ⟨ρ, hρpos, hρ1, hρk, hg⟩ := gapAt_of_reads (wilsonGaugeInvMixCubeData τ p hN β ν htend)
    (MassGap.ContinuumE.positiveTransfer_wilsonGaugeInv τ p hN hβ ν htend) k hread
  exact ⟨ρ, hρpos, hρ1, hρk, wilson_gaugeInv_clay_gap_of_gapAt τ p hN hβ ν htend hρpos hρ1 hg⟩

#print axioms wilson_gaugeInv_clay_gap_of_reads

/-- **The Clay gap at one coupling.** For the gauge-invariant transfer data at `β` and state `ν`:
`0 < ρ < 1`, `opT` self-adjoint with spectrum in `{1} ∪ [0, ρ]` and top `1`, `opT` contracting every
vector of the completion orthogonal to the vacuum by `ρ`, and a non-zero vector of the GNS space
orthogonal to the vacuum. The contraction makes `1` a simple eigenvalue; the spectral conjuncts alone
hold for the identity on any space of dimension at least `2`. The non-zero vector makes the
contraction act on a non-zero space.

DERIVED: `4` is the dimension; `0` is the excluded rank, the lower end of `ρ` and of the spectrum,
and the vacuum pairing, both in the contraction's orthogonality and in the non-zero vector's; `1` is
the vacuum eigenvalue, the upper bound on `ρ` and the all-identity boundary configuration. -/
def ClayGapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1
    ∧ IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
    ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
    ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))) 1
    ∧ (∀ u : MassGap.GNSHilbert.H (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
        inner ℂ (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
          (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) u = (0 : ℂ) →
        ‖opT (wilsonGaugeInvMixCubeData τ p hN β ν htend) u‖ ≤ ρ * ‖u‖)
    ∧ ∃ y : MassGap.Transfer.GNS (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
        y ≠ 0 ∧ (inner ℝ (wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0

/-- **Below the cut, `GapAt` at `ρ = coreRate 64 β`.** At `0 < β` with `coreRate 64 β < 1`, for a
state `ν` that is the `atTop` limit of the free mixed-cube states, `TransferGap.GapAt` holds at the
gauge-invariant transfer data at rate `coreRate 64 β`. `StrongCouplingGap.norm_Tq_le_of_orth`
contracts every class of the GNS space orthogonal to the vacuum by that rate, and
`GNSCompare.gapAt_of_tq_contracts` reads the contraction as `GapAt`.

DERIVED: `4` is the spacetime dimension; `16 * 4` is the box touch-degree bound; `0` is the excluded
rank in `hN` and the lower end of `β`; `1` is the geometric threshold of `coreRate` and the
all-identity boundary configuration. -/
theorem gapAt_of_strong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.TransferGap.GapAt (wilsonGaugeInvMixCubeData τ p hN β ν htend)
      (MassGap.StrongCoupling.coreRate (16 * 4) β) :=
  MassGap.GNSCompare.gapAt_of_tq_contracts (wilsonGaugeInvMixCubeData τ p hN β ν htend)
    (MassGap.StrongCouplingGap.coreRate_pos (16 * 4) hβ).le
    (fun y hy => MassGap.StrongCouplingGap.norm_Tq_le_of_orth τ p hN hβ hr ν htend y hy)

#print axioms gapAt_of_strong

/-- **Below the cut: the cluster expansion.** At `0 < β` with `coreRate 64 β < 1` and `2 ≤ N`, there
are a state `ν` and `ρ = coreRate 64 β` with `ClayGapAt`. `FreeLimit.wilson_gaugeInv_mass_gap_lattice`
gives the state and the spectrum, `gapAt_of_strong` through `GNSCompare.gapAt_iff_opT_contracts` the
contraction, and `PlaneVariance.exists_ne_zero_orth_vacuum` the non-zero vector.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero plaquette variance;
`0` the excluded rank and the lower
end of `β`; `16 * 4` is the box touch-degree bound; `1` is the geometric threshold of `coreRate`. -/
theorem clayGapAt_of_strong (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) :
    ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))) (htend : (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))))
      (ρ : ℝ), ClayGapAt τ p hN β ν htend ρ := by
  obtain ⟨ν, htend, hsa, _, hspec, hgreat⟩ :=
    MassGap.FreeLimit.wilson_gaugeInv_mass_gap_lattice τ p hN hβ hr
  exact ⟨ν, htend, MassGap.StrongCoupling.coreRate (16 * 4) β,
    MassGap.StrongCouplingGap.coreRate_pos _ hβ, hr, hsa, hspec, hgreat,
    (MassGap.GNSCompare.gapAt_iff_opT_contracts (wilsonGaugeInvMixCubeData τ p hN β ν htend)
      (MassGap.StrongCouplingGap.coreRate_pos (16 * 4) hβ).le).mp
      (gapAt_of_strong τ p hN hβ hr ν htend),
    MassGap.PlaneVariance.exists_ne_zero_orth_vacuum τ p hN2 hN hβ.le ν htend⟩

#print axioms clayGapAt_of_strong

/-- **Anywhere: the reads.** At `0 ≤ β` with a state `ν`, `2 ≤ N`, and `ReadsClear` at aperture
`2k + 1`, there is `ρ` with `ClayGapAt`. `gapAt_of_reads` gives `GapAt`;
`ClayCapstone.wilson_gaugeInv_clay_gap_of_gapAt` takes it to the spectrum,
`GNSCompare.gapAt_iff_opT_contracts` to the contraction, and
`PlaneVariance.exists_ne_zero_orth_vacuum` gives the non-zero vector.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero plaquette variance;
`0` the excluded rank and the lower
end of `β`; `2` and `1` also spell the aperture `2k + 1`. -/
theorem clayGapAt_of_reads (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))) (htend : (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))))
    (k : ℕ)
    (hread : SpectralGap.ReadsClear (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
        (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) k) :
    ∃ ρ : ℝ, ClayGapAt τ p hN β ν htend ρ := by
  obtain ⟨ρ, hρ0, hρ1, _, hg⟩ := gapAt_of_reads (wilsonGaugeInvMixCubeData τ p hN β ν htend)
    (MassGap.ContinuumE.positiveTransfer_wilsonGaugeInv τ p hN hβ ν htend) k hread
  obtain ⟨hsa, _, hspec, hgreat⟩ :=
    wilson_gaugeInv_clay_gap_of_gapAt τ p hN hβ ν htend hρ0 hρ1 hg
  exact ⟨ρ, hρ0, hρ1, hsa, hspec, hgreat,
    (MassGap.GNSCompare.gapAt_iff_opT_contracts (wilsonGaugeInvMixCubeData τ p hN β ν htend)
      hρ0.le).mp hg,
    MassGap.PlaneVariance.exists_ne_zero_orth_vacuum τ p hN2 hN hβ ν htend⟩

#print axioms clayGapAt_of_reads

/-- **The transfer gap at every `β > 0`, with the weak-coupling input isolated.** For `SU(N)`,
`2 ≤ N`: at every `β > 0` there are an infinite-volume state `ν` (the `atTop` limit of the free
mixed-cube states) and `ρ` with `ClayGapAt` — `0 < ρ < 1`, the gauge-invariant transfer operator
self-adjoint with spectrum in `{1} ∪ [0, ρ]` and top `1`, the vacuum complement of the completion
contracted by `ρ`, which makes `1` a simple eigenvalue, and that complement non-zero. Where
`coreRate 64 β < 1` this is the cluster expansion (`clayGapAt_of_strong`); elsewhere it is
`clayGapAt_of_reads` fed by `hweak`, which asks — only at couplings the cluster expansion does not
reach — for the state and an aperture at which every vector orthogonal to the vacuum reads below the
floor. That read condition is the gap stated as a read (`SpectralGap`).

DERIVED: `2` is the least rank with a non-zero plaquette variance, and `0` the excluded rank in `hN`;
`16 * 4` is the box touch-degree bound `coreRate` is taken at; `4` is the dimension; `0` is the lower
end of `β`; `1` is the geometric threshold of `coreRate` and the all-identity boundary configuration. -/
theorem wilson_gaugeInv_mass_gap_every_coupling (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (hweak : ∀ β : ℝ, 0 < β → ¬ MassGap.StrongCoupling.coreRate (16 * 4) β < 1 →
      ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))) (htend : (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))))
        (k : ℕ),
        SpectralGap.ReadsClear
          (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
          (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
            (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) k) :
    ∀ β : ℝ, 0 < β →
      ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))) (htend : (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))))
        (ρ : ℝ), ClayGapAt τ p hN β ν htend ρ := by
  intro β hβ
  by_cases hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1
  · exact clayGapAt_of_strong τ p hN2 hN hβ hr
  · obtain ⟨ν, htend, k, hread⟩ := hweak β hβ hr
    obtain ⟨ρ, hρ⟩ := clayGapAt_of_reads τ p hN2 hN hβ.le ν htend k hread
    exact ⟨ν, htend, ρ, hρ⟩

#print axioms wilson_gaugeInv_mass_gap_every_coupling

end MassGap.ReadRoute
