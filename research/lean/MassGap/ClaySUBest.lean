import Mathlib
import MassGap.CompositeLink
import MassGap.ZCanon

/-!
# MassGap.ClaySUBest — the best `SU(N)` capstone, and its inputs in one place

`clayStatementAt_SU_best` is `CompositeLink.clayStatementAt_SU_link`: the observer route at the
symmetrised plaquette class, the composites built from the channel-diagonal mixing of the data and the
bare tensor fields (`ObsLead.fT`, `ObsLead.bT`), the three-point input read on the observer's field
(`NonGaussLink.ObsThreePoint`) and the composites' link replaced by kernel statements
(`CompositeLink.JointRPK`, `ApproxK`, `MixConv`). What is listed below is what it still
takes, with the reductions the tree proves for each.

## The ledger of `clayStatementAt_SU_best`

One line per input: its status, and the declaration and module that reduce it. "open" means no
declaration of the tree constructs it.

* `hN2 : 2 ≤ N`, `W : ConfFlow N` — the range of the statement and the choice of flow; not inputs to
  discharge.
* `hU : ClassMoments … t C` (any `t > 0`, `ht`) — open; reduced to a small-field/large-field split
  (`ExistenceFlow.classMoments_of_split`), to a summable zoom stability
  (`ExistenceFlow.classMoments_of_zoomStable`), or to one exponential moment at one site
  (`ClaySUFinal.classMoments_of_siteExp`, `FlowUV.SiteExp`); met by the flat flow (`ExistenceFlow.flat_hU_hphys_hreach`), at which the target
  fails (`ObserverCarries.not_clayStatementAt_flatFlow_symPlaq`), and failed by the identity flow
  (`PlaquetteFloor.not_classMoments_identity`).
* `hphys : PhysRange r` — open, a choice of flow; reduced to a vanishing reach `a_k · range_k → 0`
  (`ClayData.physD`).
* `hfar : RunSeed N` — open, the mass gap; equivalent to the edge cost per unit physical length above
  a cutoff (`ObserverTheory.runSeedG_iff_edgeCost` with `WindowG.runSeedG_SU`); at `N = 2` equivalent
  to the vortex and zero-flux decays (`FluxCost.runSeed_two_iff_vortex`); implied at `N = 2` by a
  fixed diffraction length (`ApertureGap.runSeed_of_fixedDiffraction`).
* `z`, `hz`, `hzS`, `hzP` — conditions on the chosen channel factors alone; met by `ZCanon.zFix`
  (`ZCanon.zFix_ne`, `tendsto_zFix_sc`, `tendsto_zFix_ps`), which `clayStatementAt_SU_best_zcan`
  uses.
* `G`, `hK : TwoPointKernel` — open; equivalent to a kernel of the connected two-point function of the
  observer's field at the normalisation `((N/16) z_sc k)²` (`WardKernel.twoPointKernel_rhoD_iff`); unchanged by fixing `z_sc`
  (`ZCanon.twoPointKernel_zFix`).
* `hAF : AFCoefficient N G` — open; reads only `G`.
* `hObs : ObsThreePoint` — open; reduced to the canonical three-point statement on three insertions of
  the observer's field (continuous, separated test functions), with an eventual bound on that reading
  (`hB`) and a normalisation match (`hR`) (`NonGaussLink.obsThreePoint_of_canonical`,
  `NonTrivialCanonical.ThreePointCanonical`); carried to `zFix` (`ZCanon.obsThreePoint_zFix`).
* `hWard : WardT` — open; its stress insertion splits into the traceless-Ricci channel and the trace
  (`WardKernel.latT_stress_split`), which is a rewriting, not a reduction.
* `hCO : CompOS` of the built composites — open; no reduction in the tree.
* `hJ : JointRPK` — open; reduced to the continuum reflection covariance of the composites in the
  mixed readings (`JointRP.jointRPK_of_reflLim`, `JointRP.ReflLim`), whose lattice form fails for
  these composites (`JointRP.not_reflCovLat`); removed at the reflection-averaged composites
  (`ReflAvg.clayStatementAt_SU_reflAvg`), at the price of `hWard`, `hCO`, `hA`, `hMC` read there;
  necessary for any vectors of the composites in the pre-observer's space
  (`CompositeLink.jointRPK_of_vectors`).
* `hA : ApproxK` — open; for vectors with the cross pairings and the Gram matrix, equivalent to their
  membership in the closure of the real span of the observer's vectors (`CompositeLink.approx_iff`,
  `CompositeLink.approx_iff_K`).
* `hMC : MixConv` — open; reduced to an eventual bound on each composite mixed reading
  (`CompositeLink.mixConv_of_bounded`).

Proved on the way, so not inputs: everything `ObsLead.clayStatementAt_SU_obs`,
`NonGaussLink.clayStatementAt_SU_ng` and `CompositeLink.linkCPre_of_kernels` discharge (the index map,
the rotation representation, coverage, the rotation tie, the mixing's ties and renormalisation, the
classical tie, `NonGaussianT` from `hObs`, the composites' vectors `wC` with the shift and vacuum
clauses of their link and the cross reading `hX`, and the observer carrying the Hilbert space).

## The alternative at fixed scalar and pseudoscalar factors

`clayStatementAt_SU_best_zcan` is `clayStatementAt_SU_best` at `z = ZCanon.zFix N zri zwe`: `hz`
reduces to `hri`, `hwe`, and `hzS`, `hzP` hold exactly. `hK` and `hObs` are stated at `zFix`; at any
`z` with `z_sc k · a_k⁴ → 2` they carry over (`clayStatementAt_SU_best_zcan_of`), and so does
`NonGaussianT` (`ZCanon.contTr_zFix`). `hWard`, `hCO`, `hJ`, `hA` and `hMC` read channel-mixing
families whose terms rescale by different factors as `z` changes; no declaration carries them to
`zFix`, and fixing `z` can make them harder to meet. So the `zcan` forms are alternatives to
`clayStatementAt_SU_best`, not replacements.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count and the limits of the scalar and pseudoscalar
factors; `0` the reflection plane; `4` the dimension; `1` the colour bound `1 ≤ N` that makes the spacings positive.
-/

noncomputable section

namespace MassGap.ClaySUBest

open Filter
open scoped Topology

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.ClayWiring MassGap.ExistenceReduce MassGap.NonTrivialCanonical
open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData
  MassGap.CompositeLink

variable {N : ℕ}

/-- **The best `SU(N)` capstone**: `CompositeLink.clayStatementAt_SU_link`. Its inputs and their
status are the ledger of the module header. An alias: the statement and proof are those of
`CompositeLink.clayStatementAt_SU_link`. -/
alias clayStatementAt_SU_best := MassGap.CompositeLink.clayStatementAt_SU_link

/-- **The best capstone at `z = ZCanon.zFix N zri zwe`**: the scalar and pseudoscalar factors are
`2/a_k⁴`, so `hz` reduces to `hri`, `hwe` (`ZCanon.zFix_ne`) and `hzS`, `hzP` hold exactly
(`ZCanon.tendsto_zFix_sc`, `ZCanon.tendsto_zFix_ps`). Every other input is that of
`clayStatementAt_SU_best` at `zFix`.

An alternative to `clayStatementAt_SU_best`, not a replacement: `hK` and `hObs` carry over from any
admissible `z` (`clayStatementAt_SU_best_zcan_of`), but `hWard`, `hCO`, `hJ`, `hA` and `hMC` read
channel-mixing families, no declaration carries them to `zFix`, and at `zFix` they can be harder to
meet.

DERIVED: `2` the least colour count; `1` the colour bound `1 ≤ N` that makes the spacings positive; `0` the
plane. -/
theorem clayStatementAt_SU_best_zcan (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (zri zwe : ℕ → ℝ) (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0)
    (G : ℝ → ℝ)
    (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) (ZCanon.zFix N zri zwe)) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) (ZCanon.zFix N zri zwe))
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) (ZCanon.zFix N zri zwe)))
    (hCO : CompOS (ne_zero_of_two_le hN2)
      (build (rhoD (fT N) (ZCanon.zFix N zri zwe)) (bareD (fT N) (bT N))))
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N (ZCanon.zFix N zri zwe)) 0)
      (mixK hN2 W (ZCanon.zFix N zri zwe) r) (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N (ZCanon.zFix N zri zwe)) 0)
      (mixK hN2 W (ZCanon.zFix N zri zwe) r) (gramF hN2 W r))
    (hMC : MixConv hN2 W (ZCanon.zFix N zri zwe) r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  have hN1 : 1 ≤ N := one_le_two.trans hN2
  clayStatementAt_SU_best hN2 W ht hU hphys hfar (ZCanon.zFix N zri zwe)
    (ZCanon.zFix_ne hN1 hri hwe) (ZCanon.tendsto_zFix_sc hN1 zri zwe)
    (ZCanon.tendsto_zFix_ps hN1 zri zwe) G hK hAF hObs hWard hCO hJ hA hMC

/-- **The `zFix` form with `hK` and `hObs` read at any admissible `z`**: `hK` and `hObs` at a `z`
with `z_sc k · a_k⁴ → 2` give them at `zFix` (`ZCanon.twoPointKernel_zFix`,
`ZCanon.obsThreePoint_zFix`), so these two inputs are not made harder by fixing the factors. The
channel-mixing inputs `hWard`, `hCO`, `hJ`, `hA`, `hMC` are still stated at `zFix`.

DERIVED: `2` the limit of the scalar factor and the least colour count; `4` the dimension; `0` the
plane. -/
theorem clayStatementAt_SU_best_zcan_of (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (zri zwe : ℕ → ℝ) (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0)
    (z : Chan → ℕ → ℝ) (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) (ZCanon.zFix N zri zwe)))
    (hCO : CompOS (ne_zero_of_two_le hN2)
      (build (rhoD (fT N) (ZCanon.zFix N zri zwe)) (bareD (fT N) (bT N))))
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N (ZCanon.zFix N zri zwe)) 0)
      (mixK hN2 W (ZCanon.zFix N zri zwe) r) (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N (ZCanon.zFix N zri zwe)) 0)
      (mixK hN2 W (ZCanon.zFix N zri zwe) r) (gramF hN2 W r))
    (hMC : MixConv hN2 W (ZCanon.zFix N zri zwe) r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_best_zcan hN2 W ht hU hphys hfar zri zwe hri hwe G
    ((ZCanon.twoPointKernel_zFix (ne_zero_of_two_le hN2) (fT N) z hzS zri zwe G).mp hK) hAF
    (ZCanon.obsThreePoint_zFix (ne_zero_of_two_le hN2) z hzS zri zwe hObs) hWard hCO hJ hA hMC

end MassGap.ClaySUBest

end

#print axioms MassGap.ClaySUBest.clayStatementAt_SU_best
#print axioms MassGap.ClaySUBest.clayStatementAt_SU_best_zcan
#print axioms MassGap.ClaySUBest.clayStatementAt_SU_best_zcan_of
