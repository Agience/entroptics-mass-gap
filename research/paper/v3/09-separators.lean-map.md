# Section 9: theorem-to-Lean map

Declarations in the Lean library, namespace `MassGap.<Module>`. Some rows were read against the Lean signatures, the others from module docstrings with the declaration confirmed to exist by name. "Model" means the statement is about a defined model, not the Wilson measure. The text's stall shape (Σ) is named (M) in the Lean docstrings.

| Theorem | Lean declaration | Open or chosen inputs |
|---|---|---|
| frame | the fork and Perron–Frobenius are Theorems 5.12 and 5.11 (`StallRigid.fork_quant`, `vanishes_iff_read`, `stall_dichotomy`, `massive_stall_grows`; `schur_gap`, `exists_topG`, `Yw_lt_one`); `StallRigid.level_count` | none; (H), (Q), (Σ) open at `SU(N)` |
| 9.1 | `StallRigid.top_centre_neutral` | none |
| 9.2 | `StallRigid.biased_stall` | model |
| 9.3 | `DefectBound.bounded_iff_count`, `DefectBound.bounded_iff_freeEnergy`, `DefectBound.surface_bound` | (H) not proved at any `β > 0` |
| 9.4 | `PhotonStall.dbl_affine`, `defectDβ_massive`, `defectDβ_massless`, `defectPh_split`, `phCoeff`, `photon4`, `vanishes_at_most_one`, `photon_not_strongEnd`, `massless_vanishes_unique`, `chain_negative`, `photon4_stall_of` | model; zero-mode volumes chosen; the `det′` lower bound for the last |
| 9.5 | `ToronSector.su2_toron_not_constant`, `chargedDet_centre`, `su2_ring_weyl`, `toron_vanishes_unique`, `toron_not_strongEnd`, `su2Defect_eq`, `su2_not_strongEnd` | model; weight, cutoff and the limit `B_w → b > 0` chosen |
| 9.6 | `BondMove.defect_le_of_sandwich`, `defect_le_of_matched`, `upperToy_not_step`, `lowerToy_not_step`, `MatchedBlocking`, `zoomStepMap_of_matchedBlocking`, `strongEnd_of_matchedBlocking`, `decim_lt`, `decim_tendsto` | `MatchedBlocking`, `NoFixedAbove φ`; toy counterexamples chosen |
| 9.7 | `PlaneFlow.blockExp`, `sum_card_inter`, `sum_blockExp`, `sum_blockExp_four`, `window_step_id`, `iterate_window_step`, `orbit_mem_iff`, `diag_not_strip`, `const_zoomStepMap_id`, `const_not_tendsto`, `id_not_noFixedAbove` | model |
| 9.8 | `OneStepZoom.hk_step_eq`, `quarter_noFixedAbove`, `hk_zoomStepMap`, `hk_zoomReach`, `phi_groupBlind`, `stack_step`, `stack_exact_fails`, `stack_not_zoomStepMap`, `stack_zoomStepMap_iff` | heat-kernel model |
| 9.9 | `CurveFloor.ricSU_eq`, `ricU1_eq`, `su_floor`, `u1_no_floor`, `heatConst_bounds`, `heatConst_tendsto`, `circle_mode_decay`, `su2_mode_decay`, `circle_gap_every_zoom`, `BlockBE`, `blockBE_iff`, `not_blockBE_of_tendsto`, `not_blockBE_U1`, `closedForms_ne_top`, `sig_triple`, `circle_no_triple` | chain-picture model; `heatConst` as the cited log-Sobolev constant |
| 9.10 | `MasslessExclude.su2_class_curve`, `su2_class_hess`, `cd_fails` | the general compact connected case is argued |
| 9.11 | `CoverCompact.exists_split`, `conserved_iff_affine`, `hom_eq_one_of_perfect`, `conserved_const_of_perfect`, `su_everyCommutator`, `isPerfect_SU`, `so3_everyCommutator`, `isPerfect_SO3`, `isPerfect_A5`, `conserved_const_G2` | perfectness of `G₂` a hypothesis |
| 9.12 | `CubeFlux.bianchi_transported`, `CubeFlux.bianchi_comm` | none |
| 9.13 | `CoverCompact.twistedAction_flat_SU`, `GapSideTwistFlat.not_flat_of_comm`; `FlatCap.windowCoupling_split`, `FlatCap.flat_cap`, `FlatCap.fifteen_constant`, `StallRigid.large_stall_zero_flux`, `FluxFold.z2_deconfined` | (W0) open |
| 9.14 | `VortexEntropy.closed_surfaces_through_plaquette`, `VortexEntropy.floorTerm_summable_iff` | none |
| 9.15 | `ThickSheetCost.cellCost_uniform_tendsto`, `cellCost_uniform_le`, `uniform_trial_not_summable`, `su2_section`, `u1_section` | none |
| 9.16 | `NonCartanTwist.su2_profile_dominated`, `su2_transported_dominated`, `su2_u1_same_floor`, `su2_section_ge`, `su2_trial_summable` | no link field realizing a section is built |
| 9.17 | `FluctSheet.u1_freeEnergy`, `FluctSheet.su2_centre_entropicShift`, `FluctSheet.occ_centre`, `FluctSheet.su2_ring_profile_free` | Gaussian model |
| 9.18 | `VortexSheetFlux.fluxConfinedAt_two_iff_vortexR`, `VortexSheetFlux.vortexR_tendsto_of_tension` | a positive tension; `FluxConfinedAt` |
| 9.19 | `ExactIneq.sd_link`, `sd_page`, `energy_current`, `mixCut_eq_current`, `cross_zero`, `meanMix_le` | "no route passes" is argued |
| 9.20 | `HarmonicVertex.cubic_eq_commutator`, `cubic_comm`, `cubic_su2_ne`, `momentum_selection`, `formFactor_witness`, `gaussian_additive` | the sign of the doubling combination is not computed |
| 9.21 | `GaugeStiffness.dHol_split`, `ward_profile`, `ward_mean`, `resid_comm`, `resid_su2`, `resid_su2_ne`, `freeEnergy_le`, `twistRatio_ge` | stiffness bound; the continuous Cartan twist |
| 9.22 | `MasslessExclude.hasDerivAt_mTerm`, `abs_deriv_mTerm_le`, `fixed_levels_flat`, `split_defect`, `perSite_tendsto`, `hasDerivAt_cutE`, `line_strictMono`, `point_blind`, `not_antitone_SU` | no route excludes (Σ) |
| 9.23 | `GapPersist.logZ_wilson_convex`, `zoomLimit_kinks_countable`, `zoomLimit_crossings_countable`, `limit_blind`, `tangency_flat`, `degenerate_flat` | the link from a stall to two sector free energies is not proved |
| 9.24 | `AxisSplit.exchange`, `Δ_path`, `window_le`, `corner_le`, `not_transverseDouble`, `degX_window`; `TransverseTunnel.tunX_lineSpectral`, `tunX_positive`, `mixed_tunX_neg`, `not_transverseDouble_of_lineSpectral` | `AxisSplit.TransverseDouble`, `TimeContract` for `window_le` |
| two-phase filter | `StallRigid.isolated_topological` | model |

`MasslessExclude.cd_fails` is arithmetic; its content is the pairing with `su2_class_hess`, at `SU(2)` only. `CurveFloor` statements concern the chain picture, not the Wilson block law. `PlaneFlow`, `PhotonStall`, `ToronSector`, `OneStepZoom` (heat-kernel part) and `FluctSheet` (Gaussian part) are models.
