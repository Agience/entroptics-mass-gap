# Section 2: theorem-to-Lean map

Declarations in the Lean library, prefix `MassGap.` omitted. Hypotheses transcribed from the Lean signatures. Rows 2.5 to 2.13 are stated at the two-loop couplings (`ContinuumSchwinger.stateK`, `dyBeta`); row 2.14 at `MeasuredTower.schedAlongG` for every coupling sequence. Theorem 2.3 (ii) is `locApe_local` on the base-site box; the observer's midpoint box is `ObserverFlow.mbox`.

| Theorem | Lean declaration | Open hypotheses |
|---|---|---|
| 2.1 | `SU2Quat.det_ne_zero_of_dominant`, `SU2Quat.IsQuat.normalise_mem`; `BlockSU2.blockMat_det_ne_zero`, `BlockSU2.blockLink`, `BlockSU2.continuous_blockLink`, `BlockSU2.blockLink_gauge`, `BlockSU2.blockLink_inv`, `BlockSU2.blockLink_perm` | none |
| 2.2 | `ApeLattice.apeConf`, `ReflApe.apeConf_refl` | none |
| 2.3 | `LocalApe.apeOnIter_agree`, `LocalApe.locApe_local` | none |
| 2.4 | `ObserverFlow.obsConfFlow`, `ObserverFlow.continuous_obsFlow`, `ObserverFlow.obsFlow_gauge`, `ObserverFlow.obsFlow_refl`, `ObserverFlow.obsFlow_local`; `ObserverClay.physRange_of`, `ContinuumFlow.Flow.PhysRange` | none |
| 2.5 | `ObserverEnergyBox.smearedMoments_iff_cubeMoments`; `ObserverEnergyMoments.uniformBoundF_of_smearedMomentBound` | none (an equivalence) |
| 2.6 | `ObserverOSGrowth.state_cubeSum_pow_le`, `cubeMomentBound_of_unit`, `unitCubeMomentBound_of_cube`, `cubeMoments_of_unitExp` | none |
| 2.7 | `ContinuumFlow.contSF_comp_equiv`, `contSF_translate`, `contSF_reflect`, `contSF_gram_nonneg`, `flowTransfer`, `gT_half`, `flowTransfer_positive`; `ContinuumHypercubic.stateK_axis`; `PeriodicState.periodicState_reflInvariant` | none |
| 2.8 | `ContinuumTimeGroup.stepT_sq`, `stepT_eq_powT`, `eq_powT_of_sq`, `stepT_zero_injective`, `exists_shift_preimage`, `timeT_zero`, `timeT_add`, `timeT_dyadic`, `timeT_nonneg_norm`, `norm_powT_sub_le`, `continuousOn_timeT`, `timeT_vacT`; the generator: `ClayFull.observer_generator_isSelfAdjoint`, `ClassHamiltonian.re_inner_generator_nonneg` | none |
| 2.9 | `ObserverRotation.latSF_axis`, `latSF_hyp`, `latSF_signed`, `contSF_axis`, `contSF_signed`; `ObserverAxisN.ofConf_axisCov`, `signed_of_axisCov`, `latSF_signed_of_axisCov`; the symmetrized class: `ObserverSymField.symPlaq_cube` | none |
| 2.10 | `ObserverOS.observer_os`, `exists_os0_const`, `os0_factorial`, `contSF_update_add`, `contSF_update_smul`, `abs_contSF_energy0_sub_le`, `contSF_energy0_translate_real`, `uniformBoundF_energy0` | (C) |
| 2.11 | `ObserverOSGrowth.abs_contSF_energy0_growth`, `growth_const_le`, `temperedGrowth_energy0`, `temperedGrowth_energy0_of_cubeExp` | the unit-cube exponential moment |
| 2.12 (i)–(iv) | `ObserverOSSchwartz.schwartzGrowth_energy0`, `abs_contSF_energy0_decay`, `tendsto_schwSF`, `abs_schwSF_le`, `schwSF_eq_contSF`, `abs_schwSF_schwartz_le`; `ObserverOSTempered.schwSF_update_add`, `schwSF_update_smul`, `schwCML`, `abs_schwCML_le` | as 2.11 |
| 2.12 (v) | `ObserverOSEuclidS.ClassMoments`, `schwSFM`, `tendsto_contSF_approx`, `schwSFM_translate`, `schwSFM_gram_nonneg`, `schwSFM_rotate`; `ObserverOSLinked.observerOSDataSLinked` | class moments, the gap, the non-zero pairing (removed in Theorem 4.15) |
| 2.13 | `ObserverRotationDense.observerSO4_of_pyth`, `orbitContinuous_energy0`, `observerSO4_energy0`; `ObserverSymField.observerSO4_symPlaq`; `ObserverRotation.pyth_pow_ne_one`, `pyth_not_signed`, `pyth_not_lattice`; `SO4Planes.pythAngle_irrational`, `so4_le_of_planes` | invariance under the rotation `pyth` |
| 2.14 | `MeasuredSpacing.schedOS_alongG`, `schedTransInv_alongG`, `schedShiftInv_alongG`, `schedAxisInv_alongG` (module `SchedAlong`); `TimeGroupG.stepTG_sq`, `stepTG_nonneg`, `spectrum_stepTG`, `stepTG_vacTG`, `timeTG_add`, `timeTG_nonneg_norm`, `timeTG_vacTG`; `ObserverOSG.cubeMoments_of_unitExpG`, `tendsto_schwSFG`, `observer_generator_isSelfAdjointG` | the uniform bound and the range where used |
| 2.15 | `ObserverEnergyMoments.obsFlow_central` | none |

Not formalized: the $SU(N)$ step at $N\ge3$; the abelian mode multiplier and the local action bound of the step; the observer's own scale; the plaquette reading $2$ on a centre configuration (arithmetic).
