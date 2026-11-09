# Section 7: theorem-to-Lean map

Declarations in the Lean library, prefix `MassGap.` omitted. Hypotheses copied from the Lean signatures. The basin results are Theorems 7.1 and 7.6. Conventions: `AnisoTorus.ZA N β βp n`, `AnisoTorus.DA N β βp w` are $Z(\beta,t,n)$, $D(\beta,t,w)$; `gapArea N β` is $\ell_N(\beta)$, `bulkExp N β` is the text's $E_N(\beta)$, `binCount N β` is the text's $J_N(\beta)$, `TwoDVanish.bk N β` is $b_N(\beta)$, `StripGapThm.areaG` is $A_{\mathrm{glue}}$, `StripGapThm.seedWindow` is $w_0$, `StripGapThm.stripMass` is the text's $\mu_\ast$, `StripWidth.tStar` is $t_{\mathrm{coh}}$, `StripGas.tOne` and `StripOsc.tTwo` are $t_1$, $t_2$; the text's $\mathcal Y(U)$ is `StripGas.YR`.

| Theorem | Lean declaration | Open hypotheses |
|---|---|---|
| 7.1 | `AnisoTorus.ZA_iso`, `AnisoTorus.DA_iso`; `MixAnchor.factRepC`, `MixAnchor.factRepA`, `MixAnchor.ZA_eq`, `MixAnchor.DA_nonneg`; `MixAnchor.continuous_DA`, `MixPlane.continuous_DA₂` | none |
| 7.2 | `DecoupledSplit.ZA_decoupled`, `DecoupledSplit.decoupledFactor`; `DecoupledSplit.linkEquiv`, `hol_embP`, `sum_inPlane`, `sin_split`, `splitEquiv`, `splitEquiv_measurePreserving`; `AnisoTorus.DA_decoupled`, `LayerSplit.layerDefect_eq` | none |
| face weight | `TwoDVanish.boltz_eq`, `TwoDVanish.wt`, `TwoDVanish.fl`, `TwoDVanish.sw`, `TwoDVanish.sw_nonneg`, `TwoDVanish.sw_le_one` | none |
| 7.3 | `TwoDVanish.integral_prod_proper`, `TwoDVanish.exists_free` | none |
| 7.4 | `TwoDVanish.ZT_eq`, `TwoDVanish.R_nonneg`, `TwoDVanish.R_le`, `TwoDVanish.abs_ratio_sub_one_le`, `TwoDVanish.twoD_vanishes` | none |
| 7.5 | `TwoDVanish.decoupled_vanishes`, `TwoDVanish.layer_vanishes` | none |
| 7.6 | `MixAnchor.DA_succ_le`, `MixAnchor.DA_contracts`, `MixAnchor.DA_decay`, `MixAnchor.tendsto_DA_of_seed`; `TwoDVanish.weakMixAnchor`, `AnisoTorus.WeakMixAnchor` | none; `b` existential |
| 7.7 | `TwoDVanish.strongEnd_of_aniso` (via `AnisoTorus.strongEnd_of_aniso`, `AnisoTorus.tendsto_of_anchor`, `BetaAnalytic.vitali_tendsto_zero`); `AnisoTorus.AnisoAnalytic` | `AnisoAnalytic N β`, frequently in `β` |
| 7.8 | `StripGap.walk_gap` | none |
| 7.9 | `StripGap.Fk_equil`, `StripGap.bk_ge`, `StripWidth.one_div_bk_le` | none |
| 7.10 | `MixPlane.mem_vanishSet_iff_seed`, `MixPlane.exists_open_vanishSet`, `MixPlane.isClosed_stallSet`, `MixPlane.strongEnd_iff_diag`, `MixPlane.first_stall_of_path`, `MixPlane.diag_first_stall`; `StripClose.axis_mem_vanishSet`, `StripClose.axis_subset`, `StripClose.axis_nhds`, `StripClose.segment_first_stall` | none; (iii) restates (S) |
| 7.11 | `StripWidth.DA_le`, `StripWidth.strip_of_seed` | none |
| 7.12 | `StripWidth.DA_zero_eq`, `StripRow.ratio_row`, `StripWiden.ratio_glue`, `StripWiden.seed_glue` | none |
| 7.13 | `StripWidth.strip_width`, `StripWidth.strip_width_area`, `StripWidth.strip_width_poly`, `StripWiden.strip_width_glue`, `StripWidth.strip_width_max`, `StripWidth.diag_small` | none |
| 7.14 | `StripWidth.tLow_le_tStar`, `StripWidth.tPoly_le`, `StripWiden.tPoly_le_tGlue`, `StripWiden.tGlue_le` | none |
| 7.15 | `CumulantStrip.logZA_ext` (with `ell`, `etaT`, `etaT_eq`); the gas identity `CumulantStrip.ZA_eq_gas` | none |
| 7.16 | `CumulantStrip.DA_le_quartic`, `strip_of_seed_quartic`, `strip_width_quartic`, `tQuart_ge`, `tGlue_le_tQuart` | none |
| 7.17 | `CumulantStrip.dependency_cgf` | none; real `z` only |
| 7.18 | `StripGapThm.strip_gap`, `StripGapThm.strip_cluster`, `StripGapThm.stripMass_ge`, `StripGapThm.seed_strip`, `StripGapThm.gap_core` | none; the vacuum of `strip_cluster` is not identified with `ψ` |
| 7.19 | `StripLift.TransferGapAt`, `StripLift.seedMass`, `StripLift.gap_of_seed`, `StripLift.gap_on_vanishSet`, `StripLift.tGlue_le_tLift`, `StripLift.tLift_le`, `StripLift.lift_gap`, `StripLift.beyond_gap`, `CumulantStrip.gap_quartic`, `StripLift.segment_gap` (via `StripLift.segment_seed`, `StripLift.seed_mono_lt`), `StripLift.diag_gap`, `MixPlane.diag_anchor`, the diagonal at $\beta\le1/500000$ by composing `StripWidth.diag_small` with `StripLift.gap_on_vanishSet`, `StripClose.segment_gap_dichotomy` (from `StripClose.segment_gap_of_noStall`, `StripClose.gap_below_first_stall`) | none; `ε`, `b` existential; no single rate up to the first stall |
| 7.20 | `StripTail.tail_closes`, `StripTail.tail_iff`, `StripTail.cost_le_of_mixCut`, `MixCut.hasDerivAt_DA_mix` | none |
| 7.21 | `StripGas.gasR_matchAt`, `StripGas.YR_pos`, `StripGas.log_YR_eq_sum`, `StripGas.abs_yR_le`, `StripGas.abs_yR_sub_le`, `StripGas.yRT_congr`, `StripGas.ratio_lt`, `StripGas.card_ball_le`, `StripGas.ZG_eq_integral_YR` | none |
| 7.22 | `StripOsc.log_YR_eq_sum_sym`, `StripOsc.yS_shift`, `StripOsc.abs_yS_le`, `StripOsc.osc_near`, `StripOsc.osc_far`, `StripOsc.osc_sum`, `StripOsc.yS_local` | none |
| 7.23 | `StripTail.plane_forget`, `StripTail.plane_compare`, `StripNest.conn_outT`, `StripNest.multi_forget`, `StripNest.multi_mean` | none |
| 7.24 | `StripClose.YR_pos`, `StripClose.exp_sum_yS`, `StripClose.ZA_ratio`, `StripClose.logZA_sub`, `StripClose.exp_sum_yR`, `StripClose.planeE_yR`, `StripClose.planeE` | none |
| 7.25 | `U1Strip.ZA`, `U1Strip.DA`, `U1Strip.ZA_iso`, `U1Strip.DA_iso`, `U1Strip.integral_zpow`, `U1Strip.integral_prod_zpow`, `U1Strip.integral_hol_zpow`, `U1Strip.integral_hol_zpow_sys4`, `U1Strip.faces_char`, `U1Strip.face_eq_hol`, `U1Strip.cube_bianchi` | none; the further steps are not declarations |

The conditional forms carrying `LayerSplit.TwoDCharacter` (`AnisoTorus.decoupled_vanishes`, `DecoupledSplit.decoupled_vanishes_of_twoD`, `MixAnchor.weakMixAnchor_of_twoD`, `MixAnchor.strongEnd_of_aniso_twoD`, `MixPlane.axis_mem_vanishSet`, `MixPlane.segment_first_stall`) are superseded and not used. "Uniform in the size" is for cubic tori of side `2^w`, `w ≥ w₀`. The orders of `tPoly`, `tGlue`, `tQuart`, `stripMass` are read off closed forms; only the one-sided bounds are theorems. The missing inequality of the constant-width strip is not a declaration.
