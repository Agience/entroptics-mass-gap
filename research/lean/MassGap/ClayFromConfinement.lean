import Mathlib
import MassGap.VarianceBridge
import MassGap.SpecVarianceFloor
import MassGap.ApertureFamily

/-!
# MassGap.ClayFromConfinement — the four parts, with Part IV supplied rather than assumed

`VarianceBridge.clay_four_parts` takes four inputs. Part III is slab data and carries no hypothesis.
Part IV is `hvar`, an eventual variance floor for the finite-volume Wilson states, and
`SpecVarianceFloor.wilson_eventual_variance_floor` now produces it. What is left is Parts I and II:
`ApertureRoute.ConfinesAtAnAperture`.

**Part IV needs no transport.** `clay_four_parts` leaves the observable, the boundary condition and
the constant to the caller, so the floor can be proved directly on `ℤ⁴`.
`VarianceBridge.clay_nontriviality_of_eventual_wilson_bridge` is the other route and does need the
finite-torus comparison; the universal form of that comparison is refuted outright by
`VarianceBridge.wilson_bridge_hypothesis_unsatisfiable`, at the empty region.
-/

namespace MassGap.ClayFromConfinement

open MeasureTheory
open MassGap.GibbsSpec

/-- **The Clay statement's four parts, from confinement at an aperture.**

Parts III and IV are discharged here; Parts I and II are `hc`. Part III's data — the slab and the
family whose first member is the unit — is data, not a hypothesis: any choice serves.

⚠ **This is not a proof of the Clay statement.** `ApertureRoute.ConfinesAtAnAperture` is unproved, and
every producer of it in the tree takes a hypothesis about the finite-torus read or `wilsonCorrAt`.
What this records is that the other three parts no longer stand between confinement and the
conjunction.

⚠ **It carries the named axiom** `WightmanData.os_reconstruction_wightman`, through Part III. Part IV
carries none.

⚠ `2 ≤ N` is load-bearing, with a counterexample behind it:
`HaarVariance.haar_variance_reTr_su_one` computes the variance as exactly `0` at rank one, and no
choice of observable repairs a one-point group — where `¬ IsPointMass ν` is itself false.

`β ≥ 0` is a different kind of restriction and should not be read the same way. THIS proof needs it,
at `SpecVarianceFloor.part_le_integral_rest`, where the weight factor at the chosen link is bounded
above by one only at nonnegative coupling. Nothing here shows the floor fails below zero, and
`ReflectionHalfSpace.exp_neg_actionOn_ge` already holds at every real `β` with `|β|`, so the constant's
own form tolerates it.

`hN : N ≠ 0` is implied by `hN2` and is bound separately only because
`WilsonAction.wilsonDensity_nonneg` takes it, and it appears in the statement's type.

Part IV's `G` is bound separately from Parts I and II, which are `SU(3)` on the periodic torus; taking
`N = 3` here makes the two halves speak about the same gauge group, and nothing in the statement
forces it.

DERIVED: `0` is the excluded rank in `hN`, the lower ends of `hsl0` and `hβ`, and the index of the
family member pinned to the unit; `1` is the family index offset, the unit observable and the
normalisation `ν 1 = 1`; `2` is the rank bound, the reflection geometry `nsl = 2 * msl`, the density's
ceiling and the square in the variance. All are inherited. -/
theorem clay_four_parts_of_confinement
    (hc : MassGap.ApertureRoute.ConfinesAtAnAperture)
    {dsl nsl Nsl : ℕ} [NeZero nsl] (hNsl : Nsl ≠ 0) (τ : Fin dsl) (a : Fin nsl) (msl : ℕ)
    (hsl : nsl = 2 * msl) (hsl0 : 0 < msl) (βsl : ℝ) (ksl : ℕ)
    (v : Fin (ksl + 1) → ↑(MassGap.WilsonOS.slabMod dsl nsl Nsl τ a msl))
    (hv : v 0 = MassGap.WilsonOS.slabOne dsl nsl Nsl τ a msl)
    {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ω : IConf (MassGap.SUN.SU N)) (l₀ : ILink) :
    MassGap.ApertureRoute.FlagshipAt hc
    ∧ (Nontrivial (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv).Test ∧
        Nontrivial (MassGap.WightmanData.os_reconstruction_wightman
          (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv)).Space)
    ∧ (∃ ν : MassGap.DLRLimit.State (IConf (MassGap.SUN.SU N)),
        MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
          (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν
        ∧ ν 1 = 1 ∧ ¬ MassGap.DLRLimit.IsPointMass ν) := by
  obtain ⟨f₀, cvar, hcvar, hvar⟩ :=
    MassGap.SpecVarianceFloor.wilson_eventual_variance_floor hN2 hN hβ ω l₀
  exact MassGap.VarianceBridge.clay_four_parts hc hNsl τ a msl hsl hsl0 βsl ksl v hv
    (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β
    (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) ω f₀ cvar hcvar hvar

#print axioms clay_four_parts_of_confinement

/-- **The four parts from the PER-COUPLING read** — the aperture chosen for the question.

`ConfinesAtAnAperture` is `∃ a, ∀ β`: ONE extent made to serve every coupling.
`ApertureFamily.ConfinesAtEachCoupling` is `∀ β, ∃ a` — the read taken at the coupling asked about.
`ApertureFamily.forall_exists_aperture_does_not_give_exists_forall` shows the swap fails as a
quantifier shape, so this hypothesis is **strictly weaker** and the obligation is strictly smaller.

Parts I and II lose nothing by it. `ApertureFamily.mass_gap_rate_and_continuum_at_each_coupling`
already delivers the whole of what `FlagshipAt` delivers — the surplus `0 < κ₀ - μ β`, the geometric
bound at every `τ`, and the continuum conjunct — at the coupling given. What is given up is a rate
uniform IN THE COUPLING, which `ApertureFamily`'s scope note already records that neither hypothesis
supplies.

Parts III and IV are unchanged: Part III carries no hypothesis, and Part IV is
`SpecVarianceFloor.wilson_eventual_variance_floor`, which never mentions an aperture.

DERIVED: `0` is the excluded rank in `hN`, the lower ends of `hsl0` and `hβ`, the strict lower bound
on the surplus, and the index of the family member pinned to the unit; `1` is the family index
offset, the unit observable and the normalisation `ν 1 = 1`; `2` is the rank bound, the reflection
geometry `nsl = 2 * msl`, the density's ceiling and the square in the variance. All are inherited. -/
theorem clay_four_parts_at_each_coupling
    (hc : MassGap.ApertureFamily.ConfinesAtEachCoupling) (βlat : ℝ)
    {dsl nsl Nsl : ℕ} [NeZero nsl] (hNsl : Nsl ≠ 0) (τ : Fin dsl) (a : Fin nsl) (msl : ℕ)
    (hsl : nsl = 2 * msl) (hsl0 : 0 < msl) (βsl : ℝ) (ksl : ℕ)
    (v : Fin (ksl + 1) → ↑(MassGap.WilsonOS.slabMod dsl nsl Nsl τ a msl))
    (hv : v 0 = MassGap.WilsonOS.slabOne dsl nsl Nsl τ a msl)
    {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ω : IConf (MassGap.SUN.SU N)) (l₀ : ILink) :
    ((0 < (MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.κ₀ - (MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.μ βlat ∧
        ∀ τ' : ℕ, ‖∑ k ∈ (MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.s βlat,
            (MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.P βlat k * ((MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.m βlat k) ^ τ'‖
          ≤ (∑ k ∈ (MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.s βlat, ‖(MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.P βlat k‖)
              * Real.exp (-((MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.κ₀ - (MassGap.ApertureFamily.fullModelOfEachCoupling hc).gap.μ βlat)) ^ τ') ∧
      (∃ (q : (MassGap.ApertureFamily.fullModelOfEachCoupling hc).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Filter.Tendsto (fun k => (MassGap.ApertureFamily.fullModelOfEachCoupling hc).measure.Q j (φ k)) Filter.atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(MassGap.ApertureFamily.fullModelOfEachCoupling hc).measure.c⌉₊ : ℝ) * (MassGap.ApertureFamily.fullModelOfEachCoupling hc).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((MassGap.ApertureFamily.fullModelOfEachCoupling hc).measure.actE g j) = q j) ∧
        (∀ σ j, q ((MassGap.ApertureFamily.fullModelOfEachCoupling hc).measure.actP σ j) = q j)))
    ∧ (Nontrivial (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv).Test ∧
        Nontrivial (MassGap.WightmanData.os_reconstruction_wightman
          (MassGap.WilsonOS.wilsonOSData hNsl τ a msl hsl hsl0 βsl ksl v hv)).Space)
    ∧ (∃ ν : MassGap.DLRLimit.State (IConf (MassGap.SUN.SU N)),
        MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
          (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν
        ∧ ν 1 = 1 ∧ ¬ MassGap.DLRLimit.IsPointMass ν) := by
  obtain ⟨f₀, cvar, hcvar, hvar⟩ :=
    MassGap.SpecVarianceFloor.wilson_eventual_variance_floor hN2 hN hβ ω l₀
  refine ⟨MassGap.ApertureFamily.mass_gap_rate_and_continuum_at_each_coupling hc βlat,
    MassGap.WilsonOS.wilson_reconstructed_nontrivial hNsl τ a msl hsl hsl0 βsl ksl v hv,
    MassGap.VarianceBridge.clay_nontriviality_of_eventual_variance_floor
      (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) ω f₀ cvar hcvar hvar⟩

#print axioms clay_four_parts_at_each_coupling

end MassGap.ClayFromConfinement
