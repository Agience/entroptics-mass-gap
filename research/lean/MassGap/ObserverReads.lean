import Mathlib
import MassGap.ObserverConsistency

/-!
# MassGap.ObserverReads — the `SU(2)` inputs as the observer's readings

The `SU(2)` inputs regrouped in `ObserverConsistency` are `MultiScale W` (`uv`, `af`, `endpoint`),
`ObserverConsistency W r` (`scale`, `near`, `read`) and `low`, `ward`, `OS0C`, `CovC`, `CompNondeg`. This
module restates `af` as a statement on the observer's readings, puts the gap of the observer's transfer
(`cluster`) in place of `endpoint`, collects these with `uv`, `scale`, `near`, `read`, `low` into one
`Prop`, `ObserverReads W r`, and proves the capstone from it and four further inputs.

## 1. The statement

`ObserverReads W r` has seven clauses, each on the observer (the flow `energy0 W` of the symmetrised
plaquette class, or its field `obs 2` read at the factor `zOne`):

* `scale`: the observer reads at physical range `r` (`PhysRange r` of `energy0 W`).
* `uv`: `MultiScale.UVSplit W`, the one-site exponential moment of the observer's flowed fields in physical
  units (as in `MultiScale`).
* `cluster`: some `L > 0` with `FlowCapstone.FlowClusterAbs` of `energy0 W` at the plane `0` and margin
  `r`: at every step `m`, the observer's connected reflected reading of every pair of margin monomials,
  one shifted by `n` steps in time, is at most `C · e^{−(c/L) a_m n}`, with one physical rate `c/L` at
  every step.
* `af` (`ObsAF`): a kernel `G`, continuous on `(0, ∞)`, with the asymptotic-freedom coefficient
  (`AFCoefficient 2 G`), such that on every separated pair of continuous test functions the observer's
  connected two-point reading `(2/16)² · obsRead zOne k (f, g)` converges along `ultra` to
  `∫∫ f(x) g(y) G(|x − y|)`.
* `low`: `InputsTriage.ObsLower` at `zOne` (the observer's separated three-point reading bounded below).
* `near`, `read`: the clauses of `ObserverConsistency` (`NearFlow W`; `UniformFlowRead` at the constant
  family).

## 2. Which clauses translate (proved)

* **`endpoint` → `cluster`** (`cluster_of_multiScale`): `MultiScale W` and `scale` give `cluster` at
  `L = 1` (`MultiScale.endpoint_iff_run`, `ScaleControlRun.runSeed_two_of_scaleControlRun`,
  `LocalLink.observerClusterAbs_of_runSeed`). The capstone consumes only `cluster`:
  `gap_of_cluster` gives the gap of the observer's transfer at step `0`
  (`ObserverGapScale.flowClusterAbs_iff_gapAt`), and that gap is the only use of the run seed in the
  chain (`ClaySUFinal.clayStatementAt_SU_final` reads `RunSeed` only through
  `LocalLink.observerGapAt_of_runSeed`; `clayStatementAt_two_of_gap` is the chain with the gap in its
  place). `cluster` is the mass gap itself, read on the observer's kernel: `flowClusterAbs_iff_gapAt`
  makes it equivalent to the gap of the observer's transfer at step `0` that the capstone consumes.
  Conversely `ClayStatementAt` gives `cluster` at its own witness `(τ, r)` with `L = 1` and rate the
  witness's gap (`cluster_of_clayStatementAt`). So `ObserverReads` takes the gap conclusion as an input in
  place of `RunSeed`, which proves it (`LocalLink.observerClusterAbs_of_runSeed`). It is weaker than
  `endpoint`, not a translation of it.
* **`af` ↔ `ObsAF`**: the trace channel of `rhoD (fR 2) zOne` reads only the observer's field
  (`NonGaussLink.latT_trace_rhoD`), so `twoPointKernel_of_obsAF` gives `af` from `ObsAF` with no
  hypothesis, and `obsAF_of_twoPointKernel` gives `ObsAF` from `af` under `SepConv (rhoD (fR 2) zOne)`.
* `low` is already a statement on the observer's three-point reading (`InputsTriage.ObsLower`).
* `uv`, `scale`, `near`, `read`: unchanged.
* **`observerReads_of_multiScale_obs`**: `MultiScale W`, `ObserverConsistency W r` and `low` give
  `ObserverReads W r` (`SepConv` from `near` through `BoundC` and `CompReduce.sepConv_of_comp`). So
  `ObserverReads` asks no more than the inputs `MultiScale W`, `ObserverConsistency W r` and `low` it replaces; it
  asks no less than the gap conclusion, which `cluster` is.

## 3. The capstone (proved)

**`clayStatementAt_two_of_observerReads`**: `ObserverReads W r` with `WardT`, `OS0C`, `CovC`,
`CompNondeg` (of `rhoD (fR 2) zOne`, `CbR 2 zOne`) gives
`ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2)`.

## 4. What does not translate (argued from the definitions)

* `cluster` → `endpoint`: not in the tree. `endpoint` is a statement on finite Wilson slices (`trivKN`,
  `EigenLevels`, the loop-shell pair bound) at every large `β`; `cluster` reads the `ultra` limit of the
  flowed kernel at one flow. The limit forgets the finite volumes and every `β` outside a set of `ultra`.
  The capstone does not need the converse.
* `WardT`: an identity among limits of the stress channels `stressC κ μ ν` of `rhoD (fR 2) zOne` with
  derivatives of the test functions. Those channels are the tensor fields `fR 2`, not `obs 2`;
  `latT_trace_rhoD` collapses only the trace channel to the observer.
* `OS0C`, `CovC`, `CompNondeg`: clauses on every averaged composite `CbR 2 zOne`. The only tie of the
  composites to the observer is `read` (`ApproxK`): for each reflection vector at the plane `0` and each
  `ε`, a combination of the observer's vectors within `ε`. It covers reflection pairs at one plane with
  `ε`-dependent coefficients; `OS0C` asks a bound uniform in `n` and in the separation `d`, `CovC` asks
  all rotations (the observer's class fields are hypercubic scalars), `CompNondeg` asks non-vanishing,
  which a clause that places readings near other readings does not witness.

So `ObserverReads W r` is one statement on the observer's readings and covers `uv`, `af`, `endpoint`
(in its place `cluster`, the gap conclusion on the observer's kernel), `scale`, `near`, `read`, `low`; four clauses on the bare composites stay outside.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)` and the order of the two-point reading; `16` the trace coefficient of
`ClayData.coefC_mD`; `0` the plane, the reference step of the gap and the signs; `1` the window `L` of
`cluster_of_multiScale` and the factors of `zOne`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverReads

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP
open MassGap.ScaleControlFull (zOne)
open MassGap.FlowZero (UniformFlowRead)
open MassGap.ObserverConsistency (NearFlow boundC_of_near os1C_of_near approx_of_read)

/-! ## 1. The asymptotic-freedom clause on the observer's field -/

/-- **The observer's two-point reading has the asymptotic-freedom kernel**: a kernel `G`, continuous on
`(0, ∞)`, with `AFCoefficient 2 G`, and on every separated pair of continuous test functions the scaled
connected two-point reading `(2/16)² · obsRead zOne k (f, g)` of the observer's field converges along
`ultra` to `∫∫ f g G(|x − y|)`. DERIVED: `2` is `SU(2)` and the order; `16` the trace coefficient;
`0` the end of the half-line and the sign of the separation. -/
def ObsAF : Prop :=
  ∃ G : ℝ → ℝ, ContinuousOn G (Set.Ioi 0) ∧ AFCoefficient 2 G
    ∧ ∀ f g : TestFn, Continuous f.1 → Continuous g.1 → (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) →
      Tendsto (fun k => (((2 : ℕ) : ℝ) / 16) ^ 2
          * NonGaussLink.obsRead (ne_zero_of_two_le (le_refl 2)) zOne k ![f, g])
        (ultra : Filter ℕ) (𝓝 (∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)))

/-- **`ObsAF` gives the record's `af`**: the trace reading is `(2/16)²` times the observer's reading
(`NonGaussLink.latT_trace_rhoD`), and `contTr` is its `ultra` limit. No hypothesis.
DERIVED: `2` the order. -/
theorem twoPointKernel_of_obsAF (h : ObsAF) :
    ∃ G : ℝ → ℝ, TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) G
      ∧ AFCoefficient 2 G := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨G, hc, hAF, hT⟩ := h
  refine ⟨G, ⟨hc, fun f g hf hg hsep => ?_⟩, hAF⟩
  have e : (fun k => latT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) k
        (fun i => (trC, (![f, g] : Fin 2 → TestFn) i)))
      = fun k => (((2 : ℕ) : ℝ) / 16) ^ 2
          * NonGaussLink.obsRead (ne_zero_of_two_le (le_refl 2)) zOne k ![f, g] :=
    funext fun k => NonGaussLink.latT_trace_rhoD (ne_zero_of_two_le (le_refl 2)) (fR 2) zOne k ![f, g]
  show limUnder (ultra : Filter ℕ) (fun k => latT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) k
      (fun i => (trC, (![f, g] : Fin 2 → TestFn) i))) = _
  rw [e]
  exact (hT f g hf hg hsep).limUnder_eq

/-- A continuous separated pair, as a family of two trace insertions, is admissible.
DERIVED: `2` the number of insertions. -/
theorem adm_trace2 {f g : TestFn} (hf : Continuous f.1) (hg : Continuous g.1)
    (hsep : ∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) :
    Adm (fun i : Fin 2 => (trC, (![f, g] : Fin 2 → TestFn) i)) := by
  obtain ⟨d, hd, hfg⟩ := hsep
  refine ⟨fun i => ?_, d, hd, fun i j hij => ?_⟩
  · fin_cases i
    · exact hf
    · exact hg
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hfg
    · exact CompReduce.sepBy_symm hfg
    · exact absurd rfl hij

/-- **The record's `af` gives `ObsAF`** under `SepConv (rhoD (fR 2) zOne)`: the trace readings converge
to `contTr`, which the kernel identifies. DERIVED: `2` the order. -/
theorem obsAF_of_twoPointKernel (hS : SepConv (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne))
    (h : ∃ G : ℝ → ℝ, TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) G
      ∧ AFCoefficient 2 G) : ObsAF := by
  obtain ⟨G, ⟨hc, hK⟩, hAF⟩ := h
  refine ⟨G, hc, hAF, fun f g hf hg hsep => ?_⟩
  have hT := hS (Fin 2) (fun i => (trC, (![f, g] : Fin 2 → TestFn) i)) (adm_trace2 hf hg hsep)
  have e : (fun k => latT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) k
        (fun i => (trC, (![f, g] : Fin 2 → TestFn) i)))
      = fun k => (((2 : ℕ) : ℝ) / 16) ^ 2
          * NonGaussLink.obsRead (ne_zero_of_two_le (le_refl 2)) zOne k ![f, g] :=
    funext fun k => NonGaussLink.latT_trace_rhoD (ne_zero_of_two_le (le_refl 2)) (fR 2) zOne k ![f, g]
  have h2 : contT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne)
      (fun i => (trC, (![f, g] : Fin 2 → TestFn) i))
      = ∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y) := hK f g hf hg hsep
  rw [e, h2] at hT
  exact hT

/-! ## 2. The endpoint as the observer's clustering -/

/-- **The endpoint gives the observer's clustering** at the window `L = 1`: `endpoint` is
`ScaleControlRun` (`MultiScale.endpoint_iff_run`), which gives `RunSeed 2`, read on the observer's
flowed transfer (`LocalLink.observerClusterAbs_of_runSeed`). The bound of the observer comes from `uv`.
DERIVED: `1` the window; `0` the plane. -/
theorem cluster_of_multiScale {W : ConfFlow 2} {r : ℝ} (h : MultiScale W)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r) :
    ∃ L : ℝ, 0 < L ∧ FlowCapstone.FlowClusterAbs (ne_zero_of_two_le (le_refl 2))
      (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 r L := by
  obtain ⟨t, C, ht, hS⟩ := (MultiScale.uvSplit_iff W).1 h.uv
  have hU := ClaySUFinal.classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS
  exact ⟨1, one_pos, LocalLink.observerClusterAbs_of_runSeed (le_refl 2) (ne_zero_of_two_le (le_refl 2))
    (ScaleControlRun.runSeed_two_of_scaleControlRun (MultiScale.endpoint_iff_run.1 h.endpoint))
    _ (preB (ne_zero_of_two_le (le_refl 2)) W hU) hphys one_pos⟩

/-- **The observer's clustering gives the gap of its transfer at step `0`**
(`ObserverGapScale.flowClusterAbs_iff_gapAt`). DERIVED: `0` the plane and the step; `1` the top of `ρ`. -/
theorem gap_of_cluster {W : ConfFlow 2} {t C r : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r) {L : ℝ} (hL : 0 < L)
    (h : FlowCapstone.FlowClusterAbs (ne_zero_of_two_le (le_refl 2))
      (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 r L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (ObserverEnergyReductionsN.transferN
      (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
      (preB (ne_zero_of_two_le (le_refl 2)) W hU) 0 hphys 0) ρ :=
  (ObserverGapScale.flowClusterAbs_iff_gapAt (ne_zero_of_two_le (le_refl 2)) _
    (preB (ne_zero_of_two_le (le_refl 2)) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le (le_refl 2)) _ hphys 0) 0 hL).mp h

/-! ## 3. The chain with the gap in place of the run seed -/

/-- **The `SU(2)` capstone from a gap of the observer's transfer at step `0`**: the inputs of
`InputsTriage.clayStatementAt_SU_reflAvg_low` at `zOne`, with `hfar` replaced by `hρ0`, `hρ1`, `hg`. The
chain `clayStatementAt_SU_reflAvg_low → ClayData.clayStatementAt_SU_data →
CompositesBuild.clayStatementAt_SU_build → ClaySUFinal.clayStatementAt_SU_final` written out, ending in
`OneBridgeSU.clayStatementAt_SU_noNT_gap`, which takes the gap. DERIVED: `2` is `SU(2)`; `0` the plane;
`1` the factors of `zOne`. -/
theorem clayStatementAt_two_of_gap {W : ConfFlow 2} {t C r : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    {ρg : ℝ} (hρ0 : 0 < ρg) (hρ1 : ρg < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN (ne_zero_of_two_le (le_refl 2))
      (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) (preB (ne_zero_of_two_le (le_refl 2)) W hU) 0
      hphys 0) ρg)
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) G)
    (hAF : AFCoefficient 2 G)
    (hLow : InputsTriage.ObsLower (ne_zero_of_two_le (le_refl 2)) zOne)
    (hWard : WardT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne))
    (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (hA : ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) 0) (mixKR (le_refl 2) W zOne r)
      (gramF (le_refl 2) W r)) :
    ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2) := by
  have hMC := mixConvF_R (le_refl 2) W hU hphys zOne hCO
  obtain ⟨wC, hLC, hX⟩ := linkCPre_of_kernelsF (le_refl 2) W hU hphys (fR 2) (bR 2) zOne hCO
    (jointRPK_R (le_refl 2) W hU hphys zOne hCO hMC) hA hMC
  have hz : ∀ c k, zOne c k ≠ 0 :=
    ZCanon.zFix_ne (by norm_num) (fun _ => one_ne_zero) (fun _ => one_ne_zero)
  have hzS : Tendsto (fun k => zOne .sc k * dySpacing 2 k ^ 4) atTop (𝓝 2) :=
    ZCanon.tendsto_zFix_sc (by norm_num) _ _
  have hzP : Tendsto (fun k => zOne .ps k * dySpacing 2 k ^ 4) atTop (𝓝 2) :=
    ZCanon.tendsto_zFix_ps (by norm_num) _ _
  exact OneBridgeSU.clayStatementAt_SU_noNT_gap (le_refl 2) W ht hU hphys hρ0 hρ1 hg
    (rhoD (fR 2) zOne) (riemann_mixOfZ (opD (fR 2)) (mD 2) (ZD zOne) (coefRiemann_mD 2))
    (scalarTie_D (ne_zero_of_two_le (le_refl 2)) (fR 2) zOne hzS).2
    (CompReduce.tensorCov_of_comp _ (rhoD (fR 2) zOne) (CbR 2 zOne) eI
      (CompReduce.e_injective (CbR 2 zOne) eI (build_he1 _ _)) (build_he2 _ _) hCO.1 hCO.2.2.2.1
      (fun R _ α => build_hrep _ _ R α))
    (channelTie_D (fR 2) (bR 2) zOne hzP (tiedB_R (ne_zero_of_two_le (le_refl 2)))) G hK hAF
    (InputsTriage.nonGaussianT_rhoD_of_lower (ne_zero_of_two_le (le_refl 2)) (fR 2) zOne
      (InputsTriage.sepConv_build (ne_zero_of_two_le (le_refl 2)) (fR 2) (bareD (fR 2) (bR 2)) zOne
        hCO) hLow)
    hWard (CbR 2 zOne) wC eI (build_he1 _ _) (build_he2 _ _)
    (build_compData _ _ (tiedB_R (ne_zero_of_two_le (le_refl 2)))
      (renTensor_D (ne_zero_of_two_le (le_refl 2)) (fR 2) (bR 2) zOne hz)) hCO hLC hX

/-! ## 4. The statement and the capstone -/

/-- **The observer reads itself at every scale** (`SU(2)`, flow `W`, range `r`): module docstring, §1.
`cluster` is the gap conclusion (module docstring, §2). -/
structure _root_.MassGap.ObserverReads (W : ConfFlow 2) (r : ℝ) : Prop where
  /-- The observer reads at physical range `r`. -/
  scale : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r
  /-- The one-site exponential moment of the observer's flowed fields in physical units. -/
  uv : MultiScale.UVSplit W
  /-- The observer's connected reflected readings decay at one physical rate at every step: the gap of
  the observer's transfer (`ObserverGapScale.flowClusterAbs_iff_gapAt`), the conclusion's gap clause on
  the observer's kernel. -/
  cluster : ∃ L : ℝ, 0 < L ∧ FlowCapstone.FlowClusterAbs (ne_zero_of_two_le (le_refl 2))
    (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 r L
  /-- The observer's two-point reading converges to a kernel with the asymptotic-freedom coefficient. -/
  af : ObsAF
  /-- The observer's separated three-point reading is bounded below. -/
  low : InputsTriage.ObsLower (ne_zero_of_two_le (le_refl 2)) zOne
  /-- The bare readings are near the observer's readings, translation-stably. -/
  near : NearFlow W
  /-- The composites' reflection readings are read by the observer's margin monomials. -/
  read : UniformFlowRead (le_refl 2) (fun _ : Unit => W) zOne r

/-- **The `SU(2)` capstone from `ObserverReads`**, with `WardT`, `OS0C`, `CovC`, `CompNondeg`. `hU` from
`uv`; `BoundC`, `OS1C` from `near`; the gap at step `0` from `cluster` (`gap_of_cluster`); `af` from
`ObsAF` (`twoPointKernel_of_obsAF`); `approx` from `read`; then `clayStatementAt_two_of_gap`. `cluster` is the gap conclusion (module
docstring, §2). DERIVED: `2` is `SU(2)`. -/
theorem clayStatementAt_two_of_observerReads {W : ConfFlow 2} {r : ℝ} (h : ObserverReads W r)
    (hward : WardT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne))
    (hos0 : OS0C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (hcov : CovC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (hnd : CompNondeg (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)) :
    ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2) := by
  obtain ⟨t, C, ht, hS⟩ := (MultiScale.uvSplit_iff W).1 h.uv
  have hU := ClaySUFinal.classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS
  have hBd := boundC_of_near hU h.near
  have hos1 := os1C_of_near hU h.near
  have hCO : CompOS (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) :=
    ⟨(InputsTriage.convC_iff_boundC _ _).2 hBd, hos0, hos1, hcov, hnd⟩
  obtain ⟨L, hL, hcl⟩ := h.cluster
  obtain ⟨ρg, h0, h1, hg⟩ := gap_of_cluster hU h.scale hL hcl
  obtain ⟨G, hK, hAF⟩ := twoPointKernel_of_obsAF h.af
  exact clayStatementAt_two_of_gap ht hU h.scale h0 h1 hg G hK hAF h.low hward hCO
    (approx_of_read hU h.scale hCO h.read)

/-- **`ObserverReads` from the inputs it replaces**: `MultiScale W`, `ObserverConsistency W r` and `low`.
`cluster` from `endpoint` (`cluster_of_multiScale`); `ObsAF` from `af` under `SepConv`, which comes from
`near` (`boundC_of_near`, `CompReduce.sepConv_of_comp`). DERIVED: `2` is `SU(2)`. -/
theorem observerReads_of_multiScale_obs {W : ConfFlow 2} {r : ℝ} (h : MultiScale W)
    (hO : ObserverConsistency W r)
    (hlow : InputsTriage.ObsLower (ne_zero_of_two_le (le_refl 2)) zOne) :
    ObserverReads W r where
  scale := hO.scale
  uv := h.uv
  cluster := cluster_of_multiScale h hO.scale
  af := by
    obtain ⟨t, C, ht, hS⟩ := (MultiScale.uvSplit_iff W).1 h.uv
    have hU := ClaySUFinal.classMoments_of_siteExp (ne_zero_of_two_le (le_refl 2)) W ht hS
    have hconv := (InputsTriage.convC_iff_boundC _ _).2 (boundC_of_near hU hO.near)
    exact obsAF_of_twoPointKernel
      (CompReduce.sepConv_of_comp _ (rhoD (fR 2) zOne) (CbR 2 zOne) eI
        (fun k α => build_he2 (rhoD (fR 2) zOne) (bareD (fR 2) (bR 2)) k α) hconv) h.af
  low := hlow
  near := hO.near
  read := hO.read

/-! ## 5. The conclusion gives `cluster` -/

section ClusterOfClay

open MassGap.ContinuumCluster

/-- Time at `n · a` is the `n`-th power of time at `a`. DERIVED: `0` the sign of `a`. -/
theorem time_nat_mul (Y : OSDataS) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : Y.H) :
    Y.time (n * a) x = ((Y.time a)^[n]) x := by
  induction n generalizing x with
  | zero => simp [Y.time_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    have : ((n + 1 : ℕ) : ℝ) * a = a + n * a := by push_cast; ring
    rw [this, Y.time_add a (n * a) ha (by positivity)]
    rfl

/-- **The Clay conclusion at `W` gives the observer's clustering** at the witness's own `(τ, r)`, at
`L = 1`, with rate the witness's gap: the witness's observer vectors carry the margin kernel and its time
shift, so the connected reflected reading is an inner product against the vacuum-orthogonal part, which
the gap bounds. It holds at the `(τ, r)` the witness chooses, not at a given `r`. DERIVED: `1` the
window; `0` the step. -/
theorem cluster_of_clayStatementAt {W : ConfFlow 2}
    (h : ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2)) :
    ∃ (τ : Fin 4) (r : ℝ), FlowCapstone.FlowClusterAbs (ne_zero_of_two_le (le_refl 2))
      (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ r 1 := by
  obtain ⟨τ, r, X, ρ, G, w, C, wC, hD, -⟩ := h
  obtain ⟨-, hH, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hObs⟩ := hD
  obtain ⟨v, -, hin0, hsh, -⟩ := hObs
  have hin : ∀ P Q : MarginMono 2 τ r, inner ℂ (v P) (v Q)
      = (kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ P.1 Q.1 : ℂ) :=
    hin0
  refine ⟨τ, r, ObserverGapScale.flowClusterAbs_of_at _ _ τ 0 ?_⟩
  set a := dySpacing 2 0 with ha_def
  have ha : 0 < a := dySpacing_pos (by norm_num) 0
  have hshift : ∀ P : MarginMono 2 τ r,
      v (MarginMono.shift (ne_zero_of_two_le (le_refl 2)) τ 0 P) = X.base.time a (v P) :=
    fun P => hsh 0 P (MarginMono.shift (ne_zero_of_two_le (le_refl 2)) τ 0 P) rfl
  have hiter : ∀ (n : ℕ) (P : MarginMono 2 τ r),
      v ((MarginMono.shift (ne_zero_of_two_le (le_refl 2)) τ 0)^[n] P) = X.base.time (n * a) (v P) := by
    intro n P
    rw [time_nat_mul X.base ha.le n]
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hshift, ih]
  set e := v (emptyMargin 2 τ r) with he_def
  have hee : inner ℂ e e = (1 : ℂ) := by
    rw [hin, kernF_empty]; simp
  have hefix : X.base.time a e = e := by
    rw [← hshift, shift_emptyMargin]
  obtain ⟨c, hc⟩ := hH.2.2.2.2 a ha e hefix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    rw [hc, inner_zero_left] at hee
    exact zero_ne_one hee
  refine ⟨X.base.gap, X.base.gap_pos, fun P Q => ⟨‖v P‖ * ‖v Q - inner ℂ e (v Q) • e‖, fun n => ?_⟩⟩
  set u := v Q - inner ℂ e (v Q) • e with hu_def
  have heu : inner ℂ e u = 0 := by
    rw [hu_def, inner_sub_right, inner_smul_right, hee, mul_one, sub_self]
  have hvu : inner ℂ X.base.vac u = 0 := by
    have : inner ℂ e u = (starRingEnd ℂ) c * inner ℂ X.base.vac u := by rw [hc, inner_smul_left]
    rw [heu] at this
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact absurd ((map_eq_zero _).mp h1) hc0
    · exact h1
  have hte : ∀ t : ℝ, 0 ≤ t → X.base.time t e = e := fun t ht => by
    rw [hc, map_smul, X.base.time_vac t ht]
  have hnt : (0 : ℝ) ≤ n * a := by positivity
  have hkey : ((kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ P.1
        (Mono.shift (timeVec 2 0 τ n) Q.1)
      - kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ P.1
          (emptyMono 2)
        * kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ
          (emptyMono 2) Q.1 : ℝ) : ℂ) = inner ℂ (v P) (X.base.time (n * a) u) := by
    rw [← MarginMono.shift_iterate (ne_zero_of_two_le (le_refl 2)) τ 0 n Q]
    have h1 := hin P ((MarginMono.shift (ne_zero_of_two_le (le_refl 2)) τ 0)^[n] Q)
    have h2 := hin P (emptyMargin 2 τ r)
    have h3 := hin (emptyMargin 2 τ r) Q
    push_cast
    rw [← h1]
    erw [← h2, ← h3]
    rw [hiter, hu_def, map_sub, map_smul, hte _ hnt, inner_sub_right, inner_smul_right]
    ring
  have habs : |kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ P.1
        (Mono.shift (timeVec 2 0 τ n) Q.1)
      - kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ P.1
          (emptyMono 2)
        * kernF (ne_zero_of_two_le (le_refl 2)) (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) τ
          (emptyMono 2) Q.1| = ‖inner ℂ (v P) (X.base.time (n * a) u)‖ := by
    rw [← hkey, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  calc ‖inner ℂ (v P) (X.base.time (n * a) u)‖ ≤ ‖v P‖ * ‖X.base.time (n * a) u‖ := norm_inner_le_norm _ _
    _ ≤ ‖v P‖ * (Real.exp (-(X.base.gap * (n * a))) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (X.base.time_gap _ hnt u hvu) (norm_nonneg _)
    _ = ‖v P‖ * ‖u‖ * Real.exp (-(X.base.gap / 1) * (a * n)) := by
        rw [div_one]; ring_nf

end ClusterOfClay

end MassGap.ObserverReads

end

#print axioms MassGap.ObserverReads.twoPointKernel_of_obsAF
#print axioms MassGap.ObserverReads.adm_trace2
#print axioms MassGap.ObserverReads.obsAF_of_twoPointKernel
#print axioms MassGap.ObserverReads.cluster_of_multiScale
#print axioms MassGap.ObserverReads.gap_of_cluster
#print axioms MassGap.ObserverReads.clayStatementAt_two_of_gap
#print axioms MassGap.ObserverReads.clayStatementAt_two_of_observerReads
#print axioms MassGap.ObserverReads.observerReads_of_multiScale_obs
#print axioms MassGap.ObserverReads.time_nat_mul
#print axioms MassGap.ObserverReads.cluster_of_clayStatementAt
