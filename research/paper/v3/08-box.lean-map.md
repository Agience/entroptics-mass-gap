# Section 8: theorem-to-Lean map

Declarations in the Lean library, namespace `MassGap.<Module>`. Hypotheses transcribed from the Lean signatures. "Open" means no theorem in the tree concludes it.

| Theorem | Lean declaration | Open hypotheses |
|---|---|---|
| 8.1 | `KnabeCriterion.knabe_bound` (file `KnabeEngine.lean`); `KnabeCriterion.PatchSystem.globalGap_of_localGap`; `KnabeCriterion.knabe_commuting` | none |
| 8.2 | `BoxPatch.knabeConst_box`, `BoxPatch.boxKnabe`, `BoxPatch.boxKnabe_pos_iff`; `WeightedProfile15.P15`, `WeightedProfile15.thr15`, `K15_pos`, `a15_ne` | none |
| 8.3 | `HeatBathGapDecay.lr_bound`, `HeatBathGapDecay.cov_bound_exp` | none |
| 8.4 | `HeatBathLocal.irGapAt_boxRate` (locality `HeatBathLocal.localityAt_holds`); `WeightedBox.irGapAt_weightedBox`; `BoxGapBE.weightedRate_le`, `BoxGapBE.exp_le_clusterRate`; fibre form `BoxGap.BoxFibreGap`, `BoxGap.boxLocalGap_of_fibreGap` | none; `BoxFibreGap` at every `β > 0` for the fibre form |
| 8.5 | `BoxGapBE.boxLocalGap15_su2` (from `boxPairCorr_su2_c`, `pairCheck_su2_single_c`, `pairCheck_su2_double_c`); `BoxGapBE.boxLocalGap15_su3` (from `PairCorrSharp.boxPairCorr_floor_su3`), `PairCorrSharp.floorBeta`; `BoxGapHS.boxLocalGap15_su2_hs`, `BoxGapHS.boxLocalGap15_su3_hs`; tools `BoxGapHS.boxLocalGap_of_singleFibre`, `n2_ne_four`, `tiltBounds_sharp`, `holleyStroock`, `holleyStroock_exp`, `link_action_osc` | none |
| 8.6 | `BoxLatticeGap.torusGap_of_boxLocalGap`, `torusGap_su2_at`, `torusGap_su2_le`, `torusGap_su3_at`, `torusGap_su3_le`, `heatGen`, `boxConst`; `BoxLatticeGap.transferGap_of_boxLocalGap`, `transferGap_su2_at`, `transferGap_su2_le`, `transferGap_su3_at`, `transferGap_su3_le`, `clusterRate_eq`; `BoxGapBE.irGapAt_weightedRate_strong` | none; at the one state `periodicState hN β`; `βsc` existential |
| 8.7 | `BoxGapBE.clay15_of_localGap`; `BoxGapBE.clay_of_uvStep_su2`, `BoxGapBE.clay_of_uvStep_su3`, `BoxGapHS.clay_of_uvStep_su2_hs`, `BoxGapHS.clay_of_uvStep_su3_hs`; conclusion `ClayRoutes.ClayContinuum` | (UV) `ClayRoutes.UVBelowIR` (file `RestoreShimsClay.lean`); (B1) `ContinuumSep.UniformBoundSep`; (B2) `ContinuumNontrivial.KernelConvergesSep`; (B3) `ShortDistanceY.AFShortDistance` |
| 8.8 | `UVStepMap.exists_uvBelowIR_iff_branchGap`, `UVStepMap.gapAt_branch_of_uvBelowIR`, `UVStepMap.uvBelowIR_of_branchGap`, `UVStepMap.uvBelowIR_iff_dyadic`, `UVStepMap.uvBelowIR_of_split` | `UVStepMap.BranchGap` |
| 8.9 | `UVStepMap.BoundedSeed`, `UVStepMap.branchGap_of_boundedSeed`, `UVStepMap.strongEnd_of_boundedSeed`, `UVStepMap.clay_of_boundedSeed` | `BoundedSeed`; (B1), (B2), (B3) |
| 8.10 | `OneCubeBridge.gapAt_of_cube`, `cubeRate`, `cubeRate_pos`, `branchGap_of_cube`, `uvBelowIR_of_cube`, `clay_of_cube`, `branchGap_of_cube_or_seed`, `cubeCond_zero` | `OneCubeBridge.CubeCond` / `CubeAlong`; (B1), (B2), (B3) |

`ClayRoutes.ClayContinuum` is $\mathcal C(L)$: a per-step gap and a non-trivial vacuum at the two-loop couplings; it is not `ClayStatement` and does not imply it. `WeightedProfile15.clay15` takes `BoxFibreGap` and is not used. `OneCubeBridge` ports a variant of the lattice step of [BBLR-v442] and checks compatibility with [BB] (`nogo_limit_zero`, `physical_factor`, `uniformGap_of_bounded_side`); no Lean statement depends on their work.
