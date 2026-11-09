import Mathlib
import MassGap.ObserverRunSeed

/-!
# MassGap.ObserverBundle — the shrunk bundle with every composite clause read on the observer's flow

`InputMerge.NarrowInputsAtMin` keeps three clauses in substrate form: the asymptotic-freedom field `af` of
`SubstrateCoreMin` (a two-point kernel of the trace on `contT (rhoD (fR N) z)` with `AFCoefficient`), `WardT`
at `rhoD (fR N) z`, and `∃ ℓ, ThreePointAtScale` (bare Wilson three-point readings at scale `ℓ`). This module
states each as a clause on the observer's flowed tensor readings `WardFromLattice.msT Wf cf k s` (the
multilinear expansion over `msLat Wf cf`, the flowed proxies), proves each equivalent to its substrate form
under the bundle, and states the bundle `NarrowInputsAtObs` with its capstone and its equivalence with
`NarrowInputsAtMin`. Declarations are in the namespace `MassGap.ObserverBundle`.

These are restatements. Each moves its clause's content onto the observer's flowed readings; none removes
content. The bundle is satisfiable exactly when `NarrowInputsAtMin` is (`narrowInputsAtObs_iff_min`).

## 1. What the bundle already gives (proved)

* `ConvC (CRen N z μ)` from `FinMom` and `ExpandR` (`InputMerge.convC_of_finMom`), hence `SepConv` of the
  tensor sector `rhoD (fR N) z` (`CompReduce.sepConv_of_comp`): `sepConv_of_finMom`. `SepConv` is therefore not
  an extra input for any equivalence below.
* `WardFromLattice.latT_smallFlow`: under `ExpandR`, on every admissible family, the lattice reading of the
  tensor sector is the flowed reading `msT` at small flow time.

## 2. The flowed approach (defined; equivalence proved)

* `FlowNear Wf cf G V`: for every `η > 0`, for all small `s > 0`, eventually along `ultra`,
  `|msT Wf cf k s G − V| ≤ η`. The same shape as `WardFromLattice.FlowWard` and `FlowCovN.FlowCovLim`.
* **`contT_eq_iff_flowNear`**: under `SepConv` and `ExpandR`, on every admissible family,
  `contT (rhoD (fR N) z) G = V ↔ FlowNear Wf cf G V` (`WardFromLattice.eq_neg_of_smallFlow`,
  `WardFromLattice.flowSum_of_eq_neg` against the constant reading `−V`).

## 3. The three observer forms (defined; equivalences proved)

* `FlowAF Wf cf`: a kernel `G`, continuous on `(0, ∞)`, with `AFCoefficient N G`, such that on every
  continuous separated pair `f, g` the flowed two-point reading of the trace approaches
  `∫∫ f(x) g(y) G(|x − y|)`. **`af_iff_flowAF`**: under `SepConv` and `ExpandR`,
  `(∃ G, TwoPointKernel (rhoD (fR N) z) G ∧ AFCoefficient N G) ↔ FlowAF Wf cf`.
* `WardFromLattice.FlowWard Wf cf` for `WardT` (`WardFromLattice.wardT_iff_flowWard`, under `SepConv` and
  `ExpandR`). The admissibility caveat of `InputMerge` §3 is closed there: `WardT` quantifies over admissible
  `F` with a `C¹` cut-off `h` constant near the supports, and `WardFromLattice.adm_stress`,
  `WardFromLattice.adm_deriv` prove that every stress and derivative family it reads is admissible.
* `FlowThreeLower Wf cf`: a continuous separated triple and `κ > 0` with, for all small `s > 0`, eventually
  along `ultra`, `κ ≤ |msT Wf cf k s ((trC, a), (trC, b), (trC, c))|`. **`obsLower_iff_flowThree`**: under
  `ExpandR` alone, `InputsTriage.ObsLower hN z ↔ FlowThreeLower Wf cf` (`NonGaussLink.latT_trace_rhoD`:
  the trace reading of `rhoD` is `(N/16)³` times `obsRead`). With `NonGaussFromScale.obsLower_zFix_iff`,
  **`threePoint_iff_flowThree`**: `(∃ ℓ > 0, ThreePointAtScale hN ℓ) ↔ FlowThreeLower Wf cf` at
  `z = zFix N zri zwe`. The clause is a lower bound along the step, not a statement about `NonGaussianT`;
  `SepConv` (now from the bundle) is what turns it into `NonGaussianT` (`InputsTriage.tendsto_trace3`), and
  that link is not needed for the equivalence.

## 4. The bundle (defined; capstone and equivalence proved)

* `ObserverCore W b Wf`: `SubstrateCoreMin` without `af`: `b > 0`, `Wf b = W`, the plaquette exponential at
  `s = b`, `FinMom b Wf`. `core_of_min`, `min_of_core` (with `af`).
* `NarrowInputsAtObs N hN2 W r`: `PhysRange r`; `ObserverCore`, `ExpandR`, `ClusterPM`, `FlowCovLim`,
  `FlowAF`, `FlowWard`, `ProxyNondeg`, the generation clause, `FlowThreeLower`, `ObserverRunSeed.ObsRunSeedW N`.
* **`narrowInputsAtObs_iff_min`**: `NarrowInputsAtObs N hN2 W r ↔ NarrowInputsAtMin N hN2 W r`.
* **`clayStatement_of_narrowAtObs`**: `∃ W r, NarrowInputsAtObs N hN2 W r` at every `N ≥ 2` gives
  `MassGap.ClayStatementDy`.

## 5. Where each clause stands (sides argued; reductions proved above)

| clause of `NarrowInputsAtObs` | reads |
|---|---|
| `PhysRange r`, `ObserverCore` | the observer `W`, its flow `Wf`, the flowed monomials in `stateK` |
| `ExpandR` | the comparison of the composites with `msLat Wf cf`; it is the bridge the equivalences use |
| `ClusterPM` | cumulants of the smeared flowed proxies `msProx Wf cf` in `stateK`: a statement about the observer's flowed proxies already; its content is clustering (uniformity in the number of separated insertions), which `OS0C` reads |
| `FlowCovLim`, `ProxyNondeg` | `msLat Wf cf` (`FlowCovN`, `NondegFromProxy`) |
| `FlowAF`, `FlowWard`, `FlowThreeLower` | `msT Wf cf` (this module) |
| generation clause | `kernC` and `mixKG` of `CRen N z μ`, as in `NarrowInputsAtMin`; `InputMerge` §3 classifies it observer (`GenerationCyclic.ObserverCyclicCL`); it is kept as stated |
| `ObsRunSeedW N` | the energy density per site on the doubling box (`ObserverRunSeed`); equivalent to `RunSeed N` |

The open content is unchanged: every clause above is open exactly where its substrate form was.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count and the two insertions; `3` the three insertions and the
split of the tolerance; `16` as in `NonGaussLink.latT_trace_rhoD`; `0` the limit point and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverBundle

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup MassGap.ContinuumReconstruction
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN MassGap.FlowCovN MassGap.ApproxJoint MassGap.ClayNarrow
  MassGap.ObserverMultigrid MassGap.ClayNarrowMG MassGap.ScalePC MassGap.ScalePM MassGap.ClusterRoute
  MassGap.ClayRunSeed MassGap.InputMerge MassGap.ObserverRunSeed
open MassGap.WardFromLattice (msT SmallFlow latT_smallFlow eq_neg_of_smallFlow flowSum_of_eq_neg FlowWard
  wardT_iff_flowWard)

variable {N : ℕ}

/-! ## 1. `SepConv` from the bundle -/

/-- **`SepConv` of the tensor sector from `FinMom` and `ExpandR`** (`InputMerge.convC_of_finMom`,
`CompReduce.sepConv_of_comp`). DERIVED: no numeral. -/
theorem sepConv_of_finMom [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hm : FinMom b Wf)
    (hE : ExpandR Wf cf z μ) : SepConv (NeZero.ne N) (rhoD (fR N) z) :=
  CompReduce.sepConv_of_comp (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) (convC_of_finMom hb hm hE)

/-! ## 2. The flowed approach -/

/-- **The flowed tensor reading approaches `V`**: for every `η > 0`, for all small `s > 0`, eventually along
`ultra`, `|msT Wf cf k s G − V| ≤ η`. DERIVED: `0` the limit point. -/
def FlowNear [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (G : ι → TDatum) (V : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ), |msT Wf cf k s G - V| ≤ η

/-- A constant reading is its own flowed reading. DERIVED: `0` the difference. -/
theorem smallFlow_const (V : ℝ) : SmallFlow (fun _ => -V) (fun _ _ => -V) := fun η hη =>
  Eventually.of_forall fun _ => Eventually.of_forall fun _ => by simp [hη.le]

/-- **The continuum reading of the tensor sector is `V` exactly when the flowed reading approaches `V`**,
under `SepConv` and `ExpandR`, on every admissible family. DERIVED: no numeral. -/
theorem contT_eq_iff_flowNear [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hE : ExpandR Wf cf z μ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → TDatum) (hG : Adm G) (V : ℝ) :
    contT (NeZero.ne N) (rhoD (fR N) z) G = V ↔ FlowNear Wf cf G V := by
  have hA := latT_smallFlow hE G hG
  have hT := hS ι G hG
  have hTB : Tendsto (fun _ : ℕ => -V) (ultra : Filter ℕ) (𝓝 (-V)) := tendsto_const_nhds
  constructor
  · intro h η hη
    have hF := flowSum_of_eq_neg hA (smallFlow_const V) hT hTB (by rw [h, neg_neg]) η hη
    filter_upwards [hF] with s hs
    filter_upwards [hs] with k hk
    simpa [sub_eq_add_neg] using hk
  · intro h
    have hW : ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
        |msT Wf cf k s G + -V| ≤ η := by
      intro η hη
      filter_upwards [h η hη] with s hs
      filter_upwards [hs] with k hk
      simpa [sub_eq_add_neg] using hk
    have := eq_neg_of_smallFlow hA (smallFlow_const V) hW hT hTB
    rw [this, neg_neg]

/-! ## 3. The three observer forms -/

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

/-- **The asymptotic-freedom clause on the observer's flow**: a kernel `G` continuous on `(0, ∞)` with the
asymptotic-freedom coefficient, such that on every continuous separated pair the flowed two-point reading
of the trace approaches `∫∫ f(x) g(y) G(|x − y|)`. DERIVED: `0` the sign of the separation and the end of
the half-line; `2` the order. -/
def FlowAF [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ G : ℝ → ℝ, ContinuousOn G (Set.Ioi 0)
    ∧ (∀ f g : TestFn, Continuous f.1 → Continuous g.1 → (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) →
        FlowNear Wf cf (fun i : Fin 2 => (trC, (![f, g] : Fin 2 → TestFn) i))
          (∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)))
    ∧ AFCoefficient N G

/-- **`af` is `FlowAF`** under `SepConv` and `ExpandR` (`contT_eq_iff_flowNear` on `adm_trace2`).
DERIVED: no numeral. -/
theorem af_iff_flowAF [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hE : ExpandR Wf cf z μ) :
    (∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G)
      ↔ FlowAF Wf cf := by
  constructor
  · rintro ⟨G, ⟨hGc, hK⟩, hAF⟩
    exact ⟨G, hGc, fun f g hf hg hsep =>
      (contT_eq_iff_flowNear hS hE _ (adm_trace2 hf hg hsep) _).1 (hK f g hf hg hsep), hAF⟩
  · rintro ⟨G, hGc, hK, hAF⟩
    exact ⟨G, ⟨hGc, fun f g hf hg hsep =>
      (contT_eq_iff_flowNear hS hE _ (adm_trace2 hf hg hsep) _).2 (hK f g hf hg hsep)⟩, hAF⟩

/-- **The three-point clause on the observer's flow**: a continuous separated triple and `κ > 0` with, for
all small `s > 0`, eventually along `ultra`, `κ ≤ |msT Wf cf k s ((trC, a), (trC, b), (trC, c))|`.
DERIVED: `3` the number of insertions; `0` the signs and the limit point. -/
def FlowThreeLower [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
    ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d a b ∧ ContinuumSep.sepBy d a c
        ∧ ContinuumSep.sepBy d b c)
    ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
        κ ≤ |msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))|

/-- **`ObsLower` is `FlowThreeLower`** under `ExpandR` (`latT_smallFlow` at `InputsTriage.adm_trace3`,
`NonGaussLink.latT_trace_rhoD`). DERIVED: `16`, `3` as in `NonGaussLink.latT_trace_rhoD`; `2` the halving. -/
theorem obsLower_iff_flowThree [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandR Wf cf z μ) :
    InputsTriage.ObsLower (NeZero.ne N) z ↔ FlowThreeLower Wf cf := by
  have hq : (0 : ℝ) < ((N : ℝ) / 16) ^ 3 :=
    pow_pos (div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))) (by norm_num)) 3
  have hlat : ∀ (a b c : TestFn) (k : ℕ),
      |latT (NeZero.ne N) (rhoD (fR N) z) k (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))|
        = ((N : ℝ) / 16) ^ 3 * |NonGaussLink.obsRead (NeZero.ne N) z k ![a, b, c]| := by
    intro a b c k
    rw [NonGaussLink.latT_trace_rhoD (NeZero.ne N) (fR N) z k ![a, b, c], abs_mul, abs_of_pos hq]
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hsep, κ, hκ, hev⟩
    have hA := latT_smallFlow hE _ (InputsTriage.adm_trace3 ha hb hc hsep)
    have hp : 0 < ((N : ℝ) / 16) ^ 3 * κ / 2 := by positivity
    refine ⟨a, b, c, ha, hb, hc, hsep, ((N : ℝ) / 16) ^ 3 * κ / 2, hp, ?_⟩
    filter_upwards [hA _ hp] with s hs
    filter_upwards [hs.filter_mono ultra_le, hev] with k hk1 hk2
    have h1 := hlat a b c k
    have h2 := abs_sub_abs_le_abs_sub
      (latT (NeZero.ne N) (rhoD (fR N) z) k (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
      (msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
    have h3 : ((N : ℝ) / 16) ^ 3 * κ ≤ ((N : ℝ) / 16) ^ 3 * |NonGaussLink.obsRead (NeZero.ne N) z k ![a, b, c]| :=
      mul_le_mul_of_nonneg_left hk2 hq.le
    have hk1' : |latT (NeZero.ne N) (rhoD (fR N) z) k
        (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))
        - msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))|
        ≤ ((N : ℝ) / 16) ^ 3 * κ / 2 := hk1
    linarith
  · rintro ⟨a, b, c, ha, hb, hc, hsep, κ, hκ, hev⟩
    have hA := latT_smallFlow hE _ (InputsTriage.adm_trace3 ha hb hc hsep)
    obtain ⟨s, hs1, hs2⟩ := ((hA (κ / 2) (half_pos hκ)).and hev).exists
    refine ⟨a, b, c, ha, hb, hc, hsep, κ / 2 / ((N : ℝ) / 16) ^ 3, div_pos (half_pos hκ) hq, ?_⟩
    filter_upwards [hs1.filter_mono ultra_le, hs2] with k hk1 hk2
    have h1 := hlat a b c k
    have h2 := abs_sub_abs_le_abs_sub
      (msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
      (latT (NeZero.ne N) (rhoD (fR N) z) k (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
    have hk1' : |latT (NeZero.ne N) (rhoD (fR N) z) k
        (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))
        - msT Wf cf k s (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i))| ≤ κ / 2 := hk1
    rw [abs_sub_comm] at h2
    rw [div_le_iff₀ hq]
    linarith

/-- **`∃ ℓ > 0, ThreePointAtScale` is `FlowThreeLower`** at `z = zFix N zri zwe`, under `ExpandR`
(`NonGaussFromScale.obsLower_zFix_iff`, `obsLower_iff_flowThree`). DERIVED: `0` the sign of `ℓ`. -/
theorem threePoint_iff_flowThree [NeZero N] {zri zwe : ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandR Wf cf (ZCanon.zFix N zri zwe) μ) :
    (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (NeZero.ne N) ℓ) ↔ FlowThreeLower Wf cf :=
  (obsLower_zFix_iff (NeZero.ne N) zri zwe).symm.trans (obsLower_iff_flowThree hE)

/-! ## 4. The bundle -/

/-- **The observer core**: `InputMerge.SubstrateCoreMin` without `af`. DERIVED: no numeral. -/
structure ObserverCore [NeZero N] (W : ConfFlow N) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- The plaquette class at the physical scale, exponentially. -/
  plaq : ∃ (γ : Ix0 → ℝ) (γP t C : ℝ), 0 < t ∧
    ∀ᶠ k in atTop, ∀ q, ScaleChan Wf t C γ γP k b (Sum.inr q)
  /-- Finite flowed moments at every scale in `(0, b]`. -/
  mom : FinMom b Wf

/-- DERIVED: no numeral. -/
theorem core_of_min [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreMin W z b Wf) : ObserverCore W b Wf :=
  ⟨S.b_pos, S.top, S.plaq, S.mom⟩

/-- DERIVED: no numeral. -/
theorem min_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : ObserverCore W b Wf)
    (haf : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G) :
    SubstrateCoreMin W z b Wf :=
  ⟨S.b_pos, S.top, S.plaq, S.mom, haf⟩

/-- **The per-`N` inputs on the observer's flow**: `InputMerge.NarrowInputsAtMin` with `af` replaced by
`FlowAF`, `WardT` by `FlowWard`, `∃ ℓ, ThreePointAtScale` by `FlowThreeLower` and `RunSeed N` by
`ObsRunSeedW N`. DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
def NarrowInputsAtObs (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    ObserverCore W b Wf
      ∧ ExpandR Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ FlowCovLim Wf cf
      ∧ FlowAF Wf cf
      ∧ FlowWard Wf cf
      ∧ ProxyNondeg Wf cf
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ FlowThreeLower Wf cf
      ∧ ObsRunSeedW N

/-- **`NarrowInputsAtObs` is `NarrowInputsAtMin`** at the same `W`, `r` (`sepConv_of_finMom`,
`af_iff_flowAF`, `WardFromLattice.wardT_iff_flowWard`, `threePoint_iff_flowThree`,
`ObserverRunSeed.obsRunSeedW_iff`). DERIVED: `2` the least colour count. -/
theorem narrowInputsAtObs_iff_min (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ} :
    NarrowInputsAtObs N hN2 W r ↔ NarrowInputsAtMin N hN2 W r := by
  haveI : NeZero N := ⟨by omega⟩
  constructor
  · rintro ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hAF, hW, hP, hB, h3, hOS⟩
    have hS := sepConv_of_finMom S.b_pos S.mom hE
    exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, min_of_core S ((af_iff_flowAF hS hE).2 hAF), hE,
      hcl, hV, (wardT_iff_flowWard hS hE).2 hW, hP, hB, (threePoint_iff_flowThree hE).2 h3,
      (obsRunSeedW_iff (by omega)).1 hOS⟩
  · rintro ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩
    have hS := sepConv_of_finMom S.b_pos S.mom hE
    exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, core_of_min S, hE, hcl, hV,
      (af_iff_flowAF hS hE).1 S.af, (wardT_iff_flowWard hS hE).1 hW, hP, hB,
      (threePoint_iff_flowThree hE).1 h3, (obsRunSeedW_iff (by omega)).2 hRS⟩

/-- **`ClayStatementDy` from `NarrowInputsAtObs` at some observer and margin, at every `N ≥ 2`**
(`InputMerge.clayStatement_of_narrowAtMin`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_narrowAtObs
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsAtObs N hN2 W r) :
    MassGap.ClayStatementDy :=
  clayStatement_of_narrowAtMin fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact ⟨W, r, (narrowInputsAtObs_iff_min hN2).1 hA⟩

end MassGap.ObserverBundle

end

#print axioms MassGap.ObserverBundle.sepConv_of_finMom
#print axioms MassGap.ObserverBundle.smallFlow_const
#print axioms MassGap.ObserverBundle.contT_eq_iff_flowNear
#print axioms MassGap.ObserverBundle.adm_trace2
#print axioms MassGap.ObserverBundle.af_iff_flowAF
#print axioms MassGap.ObserverBundle.obsLower_iff_flowThree
#print axioms MassGap.ObserverBundle.threePoint_iff_flowThree
#print axioms MassGap.ObserverBundle.core_of_min
#print axioms MassGap.ObserverBundle.min_of_core
#print axioms MassGap.ObserverBundle.narrowInputsAtObs_iff_min
#print axioms MassGap.ObserverBundle.clayStatement_of_narrowAtObs
