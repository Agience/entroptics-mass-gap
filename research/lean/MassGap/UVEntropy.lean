import Mathlib
import MassGap.ChiForest
import MassGap.UVIRSplit
import MassGap.KnabeCriterion
import MassGap.ClayRoutes

noncomputable section

/-!
# MassGap.UVEntropy — the ultraviolet step in entropy form, and its link to the uniform physical gap

## What it gives

The finite-size route (`ClayRoutes.clay_continuum_of_boxPatchGap`) carries the ultraviolet input as
`ClayRoutes.UVBelowIR`, the block step `UVIRSplit.UVLossStepBelow` clipped at the IR rate: a statement about `TransferGap.GapAt` of the periodic
transfer data, carried from a coupling `β` to a finer `β'` with a summable loss of physical rate. This
module states the same step as a `χ²` bound between observer laws and proves where it leads.

1. **Observer laws and the entropy step.** `PeriodicObserverLaws hN φ obs`: at every coupling `β`,
   `obs β` is the image, under a measurable block map `φ β` into one observer space `Y`, of a
   probability measure representing `PeriodicState.periodicState hN β` on continuous observables.
   `ChiStep P' P e`: finite `χ²` of `P'` against `P` with `√(χ²) ≤ e`. `UVEntropyStep N obs βUV ε`:
   every pair of couplings `β, β' ≥ βUV` one block step apart (`aRun N β / 2 ≤ aRun N β' ≤ aRun N β`,
   the admissibility of `UVIRSplit.LossStep`; the exact halving `aRun N β' = aRun N β / 2` is its
   extreme case) has `ChiStep (obs β') (obs β) (ε (aRun N β))`. Its summability along halvings is
   `UVIRSplit.LossBudget ε a₀ E`. `chiForest_of_uvEntropyStep`: along any dyadic tower of couplings the
   step and a budget give `ChiForest.ChiForest`, the producer of the `χ²` route.
2. **One step moves a connected pairing by a variance-relative amount.** `obsConn P a b` is the
   connected pairing `E_P[a b] − E_P a · E_P b`; `relCoef P P' a b = √Var_P(a b) + |E_{P'} b| √Var_P a
   + |E_P a| √Var_P b`. `abs_obsConn_sub_le`: under `ChiStep P' P e`,
   `|obsConn P' a b − obsConn P a b| ≤ e · relCoef P P' a b`.
3. **The window factor across the tower.** `ClassKappaUV`: on a class `S` of window pairs
   `(aw i, bw i)` and lag-zero pairs `(a0 i, b0 i)`, the lag-zero pairing is non-negative and both
   coefficients are at most `κ` times it, at every coupling from `βUV` on, with one `κ`.
   `factor_step`: a factor `q ∈ [0, 1]` and relative moves `η ≤ 1/2` give the factor `q + 4η` one step
   on; `factor_chain` sums it. `obsFactor_eventually_of_uvEntropy`: `UVEntropyStep`, `ClassKappaUV`, a
   budget `E` below `aRun N β₀`, and the factor `q₀` at `β₀` (`ObsIRFactor`) give at every large `β`
   the factor `q₀ + 4κE` on the class. The proof is the tower of `UVIRSplit.gapAt_eventually_of_uv_ir`:
   exact halvings from `β₀` and one partial step.
4. **Into the uniform physical gap.** `obsIRFactor_of_gapAt`, `obsIRFactor_of_irGapAt`: the lattice
   gap at `β₀` gives the observer factor `r^{m₀}` at `β₀` through `ObsReadback` (each class pair read
   by a lattice observable at lag `m₀`). `fixedWindowDecay_of_obsFactor`: an observer factor below `1`
   at every large `β` gives `WeakCouplingWindow.FixedWindowDecay` through `UVEntropyBridge`.
   `fixedWindowDecay_of_uvEntropy_ir` composes them, and `clay_continuum_of_boxPatchGap_entropy` is the
   continuum Clay statement from `BoxPatch.BoxPatchGap` at `β₀` with the ultraviolet input in entropy
   form (`EntropyBelowIR`).
5. **The effective-density side.** `DensityBand P' P D`: `P' ≪ P` and `e^{−D} ≤ dP'/dP ≤ e^{D}`
   `P`-almost everywhere. `chiStep_of_densityBand`: a band of width `D ≥ 0` gives `ChiStep` at
   `e^{D} − 1`. `ExtensiveDensityBand` (width `Eb · V`, fixed in the spacing) gives `UVEntropyStep` at a
   constant loss (`uvEntropyStep_of_extensive`), which has no finite budget (`not_lossBudget_const`).
   `LocalRemainderDecay` (width `C · V · aRun N β ^ γ`) gives `UVEntropyStep` at
   `ε(a) = e^{C V a^γ} − 1` (`uvEntropyStep_of_localRemainderDecay`) with the budget of
   `lossBudget_localRemainder`.

## Why the link runs into `FixedWindowDecay` and not into `UVLossStep`

`UVIRSplit.UVLossStep` concludes `GapAt` at `β'`, a bound on every vector of the periodic transfer
data, the whole lattice-scale class `gaugeInvHalfSpaceAlg`; an observer law at a fixed physical
resolution reads functions of the block field only, so `UVEntropyStep` bounds pairings of that class
only. And the block step asks one loss `ε(a)` for the rates it carries, while the `χ²` step moves the window
factor additively, `q ↦ q + 4κε` (`factor_step`): at the factor `q = e^{−Mℓ}` of a window of physical
length `ℓ` the rate loss is at most `4κε/(q ℓ) = 4κε e^{Mℓ}/ℓ` (`neg_log_add_ge`), a loss that grows
with `M`; clipped at the IR rate `M₀` it is at most `4κε e^{M₀ℓ}/ℓ`. So the proved link is the composition into `FixedWindowDecay`, where the factor is compared
with `1` at one window, and the lattice-scale class enters through two named carrier Props:
`ObsReadback` at the one coupling `β₀` and `UVEntropyBridge` at every large coupling.

## Balaban's bounds and the entropy step

Balaban's ultraviolet stability bounds (cited in `UVIRSplit`) band each block-spin effective density
`ρ_k` between `χ_k exp[−A/g_k² − E₋|T|]` and `exp(E₊|T|)`, with `|T|` the number of blocks of the
torus, uniformly in `k`, at small running coupling; they supply no correlation bound. Two things
separate such bounds from `UVEntropyStep`.

* **The ratio, not each density.** `UVEntropyStep` compares the observer laws at `β` and `β'`, the
  images of the two Wilson states under the block maps to one physical scale `ℓ`. A band on each
  effective density against its own leading term bands their ratio only after the leading terms are
  matched: the effective couplings at scale `ℓ` from spacings `a` and `a/2` agree, which is what the
  running spacing `aRun N` is chosen to express at two loops, and the remainders are compared.
* **Local and decaying, not extensive.** A band of width `Eb · V` constant in the spacing
  (`ExtensiveDensityBand`) gives only a constant loss, and a constant positive loss has no budget
  (`not_lossBudget_const`). The per-region, summable form is `LocalRemainderDecay`: the band width is
  `C · V · a^γ`, `V` the number of `ℓ`-blocks of the fixed physical observer region (a count fixed as
  `a → 0`, not the torus volume), and `a^γ`, `γ > 0`, the decay of the irrelevant terms. It asks two
  properties of the effective action at scale `ℓ` that Balaban's published bounds do not state: the
  marginal on the region depends on the configuration outside a collar of the region only through
  terms whose influence decays (locality of the remainder, which makes the width proportional to `V`
  and independent of the torus), and the difference between the effective actions reached from
  spacings `a` and `a/2`, at matched running coupling, is `O(a^γ)` per block (decay of the irrelevant
  terms). Neither is claimed here.

## Scope

`UVEntropyStep`, `ClassKappaUV`, `ObsReadback`, `UVEntropyBridge`, `EntropyBelowIR`,
`ExtensiveDensityBand` and `LocalRemainderDecay` are hypotheses of every theorem that takes them;
`PeriodicObserverLaws` is a hypothesis that `DLRLimit.gibbsMeasure` of the periodic state supplies at
measurable block maps. At a class whose pairings vanish, `UVEntropyBridge` asks
`torusConn … x m ≤ e` and `0 ≤ torusConn … x 0 + e` directly; the route's content is a class of
coarse observables for which the bridge is the coarse-graining statement and `ClassKappaUV` holds.
`PeriodicObserverLaws` does not tie `φ β` across couplings, so observer laws frozen in `β` satisfy
`UVEntropyStep` at zero loss; in such a model the conclusion comes from `ObsReadback` and
`UVEntropyBridge`, and the bridge carries the lattice-scale content. The entropy step carries weight
only at block maps of one physical size.
The block factor is `2`, as in `UVIRSplit`.
-/

namespace MassGap.UVEntropy

open MeasureTheory Filter MassGap MassGap.AsymptoticScaling MassGap.PeriodicState

variable {Y : Type} [MeasurableSpace Y] {ι : Type*}

/-! ## 1. Observer laws, the step, and one connected pairing -/

section Observer

/-- **Square-integrable under one law**: `f` and `f²` are `P`-integrable.

DERIVED: `2` is the square. -/
structure SqIntAt (P : Measure Y) (f : Y → ℝ) : Prop where
  /-- `f` is integrable. -/
  integrable : Integrable f P
  /-- `f²` is integrable. -/
  integrable_sq : Integrable (fun y => f y ^ 2) P

/-- **A square-integrable pair**: `a`, `b` and `a b` are square-integrable under `P`.

DERIVED: no numeral. -/
structure PairSqInt (P : Measure Y) (a b : Y → ℝ) : Prop where
  /-- `a` is square-integrable. -/
  left : SqIntAt P a
  /-- `b` is square-integrable. -/
  right : SqIntAt P b
  /-- `a b` is square-integrable. -/
  prod : SqIntAt P (fun y => a y * b y)

/-- **The connected pairing** of `a`, `b` under `P`: `E_P[a b] − E_P a · E_P b`.

DERIVED: no numeral. -/
def obsConn (P : Measure Y) (a b : Y → ℝ) : ℝ :=
  ∫ y, a y * b y ∂P - (∫ y, a y ∂P) * ∫ y, b y ∂P

/-- **The relative coefficient of one step** from `P` to `P'` for the pair `a`, `b`:
`√Var_P(a b) + |E_{P'} b| · √Var_P a + |E_P a| · √Var_P b`, with `Var_P = ChiForest.obsVar P`.

DERIVED: no numeral. -/
def relCoef (P P' : Measure Y) (a b : Y → ℝ) : ℝ :=
  Real.sqrt (ChiForest.obsVar P (fun y => a y * b y))
    + |∫ y, b y ∂P'| * Real.sqrt (ChiForest.obsVar P a)
    + |∫ y, a y ∂P| * Real.sqrt (ChiForest.obsVar P b)

/-- **One `χ²` step**: `P'` has finite `χ²` against `P` (`ChiForest.ChiFinite`) and
`√(ChiForest.chiSq P' P) ≤ e`.

DERIVED: no numeral. -/
structure ChiStep (P' P : Measure Y) (e : ℝ) : Prop where
  /-- Finite `χ²`. -/
  finite : ChiForest.ChiFinite P' P
  /-- The square root of `χ²` is at most `e`. -/
  le : Real.sqrt (ChiForest.chiSq P' P) ≤ e

/-- **A mean moves by at most `e` standard deviations.** At probability laws, under
`ChiStep P' P e`, for `f` square-integrable under `P` and integrable under `P'`:
`|E_{P'} f − E_P f| ≤ e · √Var_P f` (`ChiForest.abs_integral_sub_le_sqrt_chiSq_mul`).

DERIVED: no numeral. -/
theorem abs_mean_sub_le_of_chiStep {P' P : Measure Y} [IsProbabilityMeasure P']
    [IsProbabilityMeasure P] {e : ℝ} (h : ChiStep P' P e) {f : Y → ℝ} (hf : SqIntAt P f)
    (hf' : Integrable f P') :
    |∫ y, f y ∂P' - ∫ y, f y ∂P| ≤ e * Real.sqrt (ChiForest.obsVar P f) :=
  (ChiForest.abs_integral_sub_le_sqrt_chiSq_mul h.finite hf.integrable hf.integrable_sq hf').trans
    (mul_le_mul_of_nonneg_right h.le (Real.sqrt_nonneg _))

#print axioms abs_mean_sub_le_of_chiStep

/-- **One step moves the connected pairing by a variance-relative amount.** At probability laws,
under `ChiStep P' P e`, with `PairSqInt P a b` and `PairSqInt P' a b`:
`|obsConn P' a b − obsConn P a b| ≤ e · relCoef P P' a b`. The three means move by
`abs_mean_sub_le_of_chiStep`, and `ChiForest.abs_conn_sub_le_rel` combines them with
`B = |E_{P'} b|`, `A = |E_P a|`.

DERIVED: no numeral. -/
theorem abs_obsConn_sub_le {P' P : Measure Y} [IsProbabilityMeasure P'] [IsProbabilityMeasure P]
    {e : ℝ} (h : ChiStep P' P e) {a b : Y → ℝ} (hP : PairSqInt P a b) (hP' : PairSqInt P' a b) :
    |obsConn P' a b - obsConn P a b| ≤ e * relCoef P P' a b := by
  have hab := abs_mean_sub_le_of_chiStep h hP.prod hP'.prod.integrable
  have ha := abs_mean_sub_le_of_chiStep h hP.left hP'.left.integrable
  have hb := abs_mean_sub_le_of_chiStep h hP.right hP'.right.integrable
  have h1 := ChiForest.abs_conn_sub_le_rel hab ha hb (le_refl |∫ y, b y ∂P'|)
    (le_refl |∫ y, a y ∂P|)
  unfold obsConn relCoef
  refine h1.trans (le_of_eq ?_)
  ring

#print axioms abs_obsConn_sub_le

end Observer

/-! ## 2. The factor across a chain of relative moves -/

section Factor

/-- **One relative move of a factor.** If `c ≤ q s` with `0 ≤ q ≤ 1`, and one step moves the window
value by `c' ≤ c + η s` and the lag-zero value by `s ≤ s' + η s`, with `s, s' ≥ 0` and
`0 ≤ η ≤ 1/2`, then `c' ≤ (q + 4η) s'`: `s ≤ s' + 2η s'`, so
`c' ≤ (q + η)(1 + 2η) s' ≤ (q + 4η) s'`.

DERIVED: `4` is `1 + 2 + 1`, the coefficient of `η` in `(q + η)(1 + 2η) = q + η + 2qη + 2η²` at
`q ≤ 1` and `2η² ≤ η`; the `2` of `1 + 2η` is `1/(1 − η) ≤ 1 + 2η` at `η ≤ 1/2`; `0` and `1` are the
ends of `q`. CHOSEN: `1/2`, the bound on a single move; any bound below `1` serves with a larger
coefficient. -/
theorem factor_step {q η c c' s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : c ≤ q * s) (hc' : c' ≤ c + η * s)
    (hss : s ≤ s' + η * s) : c' ≤ (q + 4 * η) * s' := by
  have hηs : η * s ≤ 1 / 2 * s := mul_le_mul_of_nonneg_right hη hs
  have h1 : s ≤ 2 * s' := by linarith
  have h2 : η * s ≤ η * (2 * s') := mul_le_mul_of_nonneg_left h1 hη0
  have h3 : (q + η) * s ≤ (q + η) * (s' + 2 * η * s') :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a1 : q * (η * s') ≤ 1 * (η * s') := mul_le_mul_of_nonneg_right hq1 (mul_nonneg hη0 hs')
  have a2 : η * (η * s') ≤ 1 / 2 * (η * s') :=
    mul_le_mul_of_nonneg_right hη (mul_nonneg hη0 hs')
  have e1 : (q + η) * (s' + 2 * η * s')
      = q * s' + η * s' + 2 * (q * (η * s')) + 2 * (η * (η * s')) := by ring
  have e2 : (q + η) * s = q * s + η * s := by ring
  have e3 : (q + 4 * η) * s' = q * s' + 4 * (η * s') := by ring
  rw [e3]
  linarith

#print axioms factor_step

/-- **A chain of relative moves.** For values `c j`, `s j` and moves `η j` along `j ≤ K`: with
`0 ≤ q₀`, `s j ≥ 0`, `η j ≥ 0`, `η j ≤ 1/2`, `q₀ + 4 Σ_{i<K} η i ≤ 1`, the base `c 0 ≤ q₀ s 0` and the
moves `c (j+1) ≤ c j + η j s j`, `s j ≤ s (j+1) + η j s j`: at every `j ≤ K`,
`c j ≤ (q₀ + 4 Σ_{i<j} η i) s j`. Induction on `j` with `factor_step`.

DERIVED: `4` is `factor_step`'s; `1` is the upper end of the factor and the step to the next index;
`0` is the base index and the lower end of `q₀`, `s`, `η`. CHOSEN: `1/2` is `factor_step`'s. -/
theorem factor_chain (c s η : ℕ → ℝ) (q₀ : ℝ) (K : ℕ) (hq₀ : 0 ≤ q₀)
    (hs : ∀ j : ℕ, j ≤ K → 0 ≤ s j) (hη0 : ∀ j : ℕ, 0 ≤ η j)
    (hη : ∀ j : ℕ, j < K → η j ≤ 1 / 2) (hbud : q₀ + 4 * ∑ i ∈ Finset.range K, η i ≤ 1)
    (hbase : c 0 ≤ q₀ * s 0) (hc : ∀ j : ℕ, j < K → c (j + 1) ≤ c j + η j * s j)
    (hss : ∀ j : ℕ, j < K → s j ≤ s (j + 1) + η j * s j) :
    ∀ j : ℕ, j ≤ K → c j ≤ (q₀ + 4 * ∑ i ∈ Finset.range j, η i) * s j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Finset.sum_range_zero, mul_zero, add_zero]
    exact hbase
  | succ j ih =>
    intro hj
    have hjK : j < K := by omega
    have ih' := ih (by omega)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range j, η i := Finset.sum_nonneg (fun i _ => hη0 i)
    have hsumK : ∑ i ∈ Finset.range j, η i ≤ ∑ i ∈ Finset.range K, η i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hjK.le)
        (fun i _ _ => hη0 i)
    have hstep := factor_step (hs j (by omega)) (hs (j + 1) hj) (hη0 j) (hη j hjK)
      (by linarith) (by linarith) ih' (hc j hjK) (hss j hjK)
    have e : q₀ + 4 * ∑ i ∈ Finset.range (j + 1), η i
        = q₀ + 4 * ∑ i ∈ Finset.range j, η i + 4 * η j := by
      rw [Finset.sum_range_succ]
      ring
    rw [e]
    exact hstep

#print axioms factor_chain

/-- **Each loss of a non-negative budget is at most the budget.** `UVIRSplit.LossBudget ε a₀ E` with
`ε (a₀ / 2ⁱ) ≥ 0` at every `i` gives `ε (a₀ / 2ʲ) ≤ E` at every `j`: the sum over `range (j + 1)`.

DERIVED: `2` is `LossBudget`'s block factor; `0` is the sign of the losses; `1` is the step to the
next index. -/
theorem le_budget_of_nonneg {ε : ℝ → ℝ} {a₀ E : ℝ} (hbud : UVIRSplit.LossBudget ε a₀ E)
    (h0 : ∀ i : ℕ, 0 ≤ ε (a₀ / 2 ^ i)) (j : ℕ) : ε (a₀ / 2 ^ j) ≤ E := by
  have h := hbud (j + 1)
  rw [Finset.sum_range_succ] at h
  have hs : 0 ≤ ∑ i ∈ Finset.range j, ε (a₀ / 2 ^ i) := Finset.sum_nonneg (fun i _ => h0 i)
  linarith

#print axioms le_budget_of_nonneg

/-- **The rate loss of an additive factor loss.** At `0 < q` and `0 ≤ η`:
`−log q − η/q ≤ −log(q + η)`. A factor `q = e^{−Mℓ}` at a window of physical length `ℓ`, moved to
`q + η`, keeps the physical rate `M − η e^{Mℓ}/ℓ` or more; the loss grows with `M`.
`Real.log_le_sub_one_of_pos` at `(q + η)/q`.

DERIVED: `0` is the lower end of `q` and `η`; `1` is `log x ≤ x − 1`. -/
theorem neg_log_add_ge {q η : ℝ} (hq : 0 < q) (hη : 0 ≤ η) :
    -Real.log q - η / q ≤ -Real.log (q + η) := by
  have hqη : 0 < q + η := by linarith
  have h1 : Real.log ((q + η) / q) ≤ (q + η) / q - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hqη hq)
  rw [Real.log_div hqη.ne' hq.ne', add_div, div_self hq.ne'] at h1
  linarith

#print axioms neg_log_add_ge

end Factor

/-! ## 3. The entropy step at the periodic Wilson state -/

section Wilson

variable {N : ℕ}

/-- **The periodic Wilson state seen through a block map.** There are probability measures `μ β` on
the configurations with `∫ f dμ_β = periodicState hN β f` at every continuous `f`, the maps `φ β`
are measurable, and `obs β = (μ β).map (φ β)`. The intended `φ β` reads the configuration at the
spacing `aRun N β` through blocks of one physical size into the one observer space `Y`; the Prop places
no condition relating `φ β` at different couplings, so observer laws constant in `β` also satisfy it,
and in such a model `UVEntropyStep` holds at zero loss and the content sits in `UVEntropyBridge`. `DLRLimit.gibbsMeasure (periodicState hN β)` supplies
`μ β` (`DLRLimit.integral_gibbsMeasure`, `DLRLimit.instIsProbabilityMeasure`).

DERIVED: `0` is the excluded rank. -/
def PeriodicObserverLaws (hN : N ≠ 0) (φ : ℝ → MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → Y)
    (obs : ℝ → Measure Y) : Prop :=
  ∃ μ : ℝ → Measure (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
    (∀ β : ℝ, IsProbabilityMeasure (μ β)) ∧
    (∀ (β : ℝ) (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)),
      ∫ x, f x ∂(μ β) = periodicState hN β f) ∧
    (∀ β : ℝ, Measurable (φ β)) ∧ ∀ β : ℝ, obs β = (μ β).map (φ β)

/-- The observer laws of `PeriodicObserverLaws` are probability measures
(`Measure.isProbabilityMeasure_map`).

DERIVED: `0` is the excluded rank. -/
theorem isProbability_of_periodicObserverLaws (hN : N ≠ 0)
    {φ : ℝ → MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → Y} {obs : ℝ → Measure Y}
    (h : PeriodicObserverLaws hN φ obs) (β : ℝ) : IsProbabilityMeasure (obs β) := by
  obtain ⟨μ, hμ, -, hφ, hobs⟩ := h
  rw [hobs β]
  haveI := hμ β
  exact Measure.isProbabilityMeasure_map (hφ β).aemeasurable

#print axioms isProbability_of_periodicObserverLaws

/-- **THE UV STEP IN ENTROPY FORM.** For every two couplings `β, β' ≥ βUV` one block step apart,
`aRun N β / 2 ≤ aRun N β' ≤ aRun N β`, the finer observer law has finite `χ²` against the coarser one
and `√(χ²(obs β' ‖ obs β)) ≤ ε (aRun N β)`. The exact halving `aRun N β' = aRun N β / 2` is the case
the dyadic tower uses; summability along halvings is `UVIRSplit.LossBudget ε a₀ E`.

With `obs` from `PeriodicObserverLaws` and one physical block map at `β` and `β'`, this is a bound
between the periodic Wilson states at `β` and `β'` restricted to the observables of the block field.

DERIVED: `2` is the block factor of `UVIRSplit.LossStep`. -/
def UVEntropyStep (N : ℕ) (obs : ℝ → Measure Y) (βUV : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' → aRun N β' ≤ aRun N β →
    ChiStep (obs β') (obs β) (ε (aRun N β))

/-- **The entropy step gives the `χ²` forest along a dyadic tower.** Couplings `γ j ≥ βUV` with
`aRun N (γ j) = a₀ / 2ʲ`, `0 ≤ a₀`, `UVEntropyStep N obs βUV ε` and `LossBudget ε a₀ E` give
`ChiForest.ChiForest (fun j => obs (γ j)) (fun j => ε (a₀ / 2ʲ))`: the losses are non-negative
(each is at least a square root) with bounded partial sums, hence summable
(`summable_of_sum_range_le`).

DERIVED: `2` is the block factor; `0` is the lower end of `a₀` and the sign of the losses; `1` is the
step to the next index. -/
theorem chiForest_of_uvEntropyStep {obs : ℝ → Measure Y} {βUV a₀ E : ℝ} {ε : ℝ → ℝ}
    (hent : UVEntropyStep N obs βUV ε) (hbud : UVIRSplit.LossBudget ε a₀ E) (ha₀ : 0 ≤ a₀)
    {γ : ℕ → ℝ} (hγUV : ∀ j : ℕ, βUV ≤ γ j) (hγ : ∀ j : ℕ, aRun N (γ j) = a₀ / 2 ^ j) :
    ChiForest.ChiForest (fun j => obs (γ j)) (fun j => ε (a₀ / 2 ^ j)) := by
  have hadm1 : ∀ j : ℕ, aRun N (γ j) / 2 ≤ aRun N (γ (j + 1)) := fun j =>
    le_of_eq (by rw [hγ j, hγ (j + 1), pow_succ, div_div])
  have hadm2 : ∀ j : ℕ, aRun N (γ (j + 1)) ≤ aRun N (γ j) := fun j => by
    rw [hγ j, hγ (j + 1), pow_succ, ← div_div]
    have hnn : 0 ≤ a₀ / 2 ^ j := div_nonneg ha₀ (by positivity)
    linarith
  have hst : ∀ j : ℕ, ChiStep (obs (γ (j + 1))) (obs (γ j)) (ε (a₀ / 2 ^ j)) := fun j => by
    have h := hent (γ j) (γ (j + 1)) (hγUV j) (hγUV (j + 1)) (hadm1 j) (hadm2 j)
    rw [hγ j] at h
    exact h
  have h0 : ∀ j : ℕ, 0 ≤ ε (a₀ / 2 ^ j) := fun j => (Real.sqrt_nonneg _).trans (hst j).le
  exact ⟨summable_of_sum_range_le h0 hbud, fun j => (hst j).finite, fun j => (hst j).le⟩

#print axioms chiForest_of_uvEntropyStep

/-- **THE CLASS-UNIFORM RELATIVE REMAINDER ALONG THE COUPLINGS.** On a class `S` with window pairs
`(aw i, bw i)` and lag-zero pairs `(a0 i, b0 i)`: `κ ≥ 0`; at every coupling `β ≥ βUV` both pairs are
square-integrable under `obs β` and the lag-zero pairing is non-negative; and at every admissible
step `β → β'` both relative coefficients `relCoef (obs β) (obs β') …` are at most `κ` times the
lag-zero pairing at `β`, with the one `κ` for the class. The observer-level analogue, along the
couplings, of `ClayRoutes.ClassKappa`.

DERIVED: `0` is the lower end of `κ` and the sign of the lag-zero pairing; `2` is the block
factor. -/
structure ClassKappaUV (N : ℕ) (obs : ℝ → Measure Y) (βUV : ℝ) (S : Set ι)
    (aw bw a0 b0 : ι → Y → ℝ) (κ : ℝ) : Prop where
  /-- The constant is non-negative. -/
  kappa_nonneg : 0 ≤ κ
  /-- The window pairs are square-integrable from `βUV` on. -/
  sqInt_window : ∀ β : ℝ, βUV ≤ β → ∀ i ∈ S, PairSqInt (obs β) (aw i) (bw i)
  /-- The lag-zero pairs are square-integrable from `βUV` on. -/
  sqInt_zero : ∀ β : ℝ, βUV ≤ β → ∀ i ∈ S, PairSqInt (obs β) (a0 i) (b0 i)
  /-- The lag-zero pairing is non-negative from `βUV` on. -/
  zero_nonneg : ∀ β : ℝ, βUV ≤ β → ∀ i ∈ S, 0 ≤ obsConn (obs β) (a0 i) (b0 i)
  /-- The window coefficient is at most `κ` times the lag-zero pairing. -/
  coef_window : ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' →
    aRun N β' ≤ aRun N β → ∀ i ∈ S,
      relCoef (obs β) (obs β') (aw i) (bw i) ≤ κ * obsConn (obs β) (a0 i) (b0 i)
  /-- The lag-zero coefficient is at most `κ` times the lag-zero pairing. -/
  coef_zero : ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' →
    aRun N β' ≤ aRun N β → ∀ i ∈ S,
      relCoef (obs β) (obs β') (a0 i) (b0 i) ≤ κ * obsConn (obs β) (a0 i) (b0 i)

/-- **One admissible step on the class.** At probability laws, under `UVEntropyStep N obs βUV ε` and
`ClassKappaUV N obs βUV S aw bw a0 b0 κ`, for an admissible pair `β → β'` and `i ∈ S`, with
`s = obsConn (obs β) (a0 i) (b0 i)`: the window pairing moves up by at most `κ ε(aRun N β) s`, and
the lag-zero pairing down by at most `κ ε(aRun N β) s` (`abs_obsConn_sub_le`).

DERIVED: `2` is the block factor. -/
theorem pair_step {obs : ℝ → Measure Y} (hprob : ∀ β, IsProbabilityMeasure (obs β)) {βUV : ℝ}
    {ε : ℝ → ℝ} (hent : UVEntropyStep N obs βUV ε) {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ}
    {κ : ℝ} (hK : ClassKappaUV N obs βUV S aw bw a0 b0 κ) {β β' : ℝ} (h1 : βUV ≤ β)
    (h2 : βUV ≤ β') (h3 : aRun N β / 2 ≤ aRun N β') (h4 : aRun N β' ≤ aRun N β) {i : ι}
    (hi : i ∈ S) :
    obsConn (obs β') (aw i) (bw i) ≤ obsConn (obs β) (aw i) (bw i)
        + κ * ε (aRun N β) * obsConn (obs β) (a0 i) (b0 i) ∧
      obsConn (obs β) (a0 i) (b0 i) ≤ obsConn (obs β') (a0 i) (b0 i)
        + κ * ε (aRun N β) * obsConn (obs β) (a0 i) (b0 i) := by
  have hstep := hent β β' h1 h2 h3 h4
  have he0 : 0 ≤ ε (aRun N β) := (Real.sqrt_nonneg _).trans hstep.le
  haveI := hprob β
  haveI := hprob β'
  have hw := abs_obsConn_sub_le hstep (hK.sqInt_window β h1 i hi) (hK.sqInt_window β' h2 i hi)
  have h0 := abs_obsConn_sub_le hstep (hK.sqInt_zero β h1 i hi) (hK.sqInt_zero β' h2 i hi)
  have hcw := mul_le_mul_of_nonneg_left (hK.coef_window β β' h1 h2 h3 h4 i hi) he0
  have hc0 := mul_le_mul_of_nonneg_left (hK.coef_zero β β' h1 h2 h3 h4 i hi) he0
  have e1 : ε (aRun N β) * (κ * obsConn (obs β) (a0 i) (b0 i))
      = κ * ε (aRun N β) * obsConn (obs β) (a0 i) (b0 i) := by ring
  constructor
  · linarith [le_abs_self (obsConn (obs β') (aw i) (bw i) - obsConn (obs β) (aw i) (bw i))]
  · linarith [neg_abs_le (obsConn (obs β') (a0 i) (b0 i) - obsConn (obs β) (a0 i) (b0 i))]

#print axioms pair_step

/-- **The observer factor at one coupling.** Every `i ∈ S` has
`obsConn (obs β₀) (aw i) (bw i) ≤ q₀ · obsConn (obs β₀) (a0 i) (b0 i)`.

DERIVED: no numeral. -/
def ObsIRFactor (obs : ℝ → Measure Y) (β₀ : ℝ) (S : Set ι) (aw bw a0 b0 : ι → Y → ℝ)
    (q₀ : ℝ) : Prop :=
  ∀ i ∈ S, obsConn (obs β₀) (aw i) (bw i) ≤ q₀ * obsConn (obs β₀) (a0 i) (b0 i)

/-- **THE UV/IR COMPOSITION IN ENTROPY FORM.** At `1 ≤ N`, probability observer laws, `0 < β₀`,
`βUV ≤ β₀`, a loss budget `E` below `aRun N β₀`, `UVEntropyStep N obs βUV ε`,
`ClassKappaUV N obs βUV S aw bw a0 b0 κ`, `0 ≤ q₀`, `q₀ + 4κE ≤ 1` and `ObsIRFactor obs β₀ … q₀`:
for all large `β`, every `i ∈ S` has
`obsConn (obs β) (aw i) (bw i) ≤ (q₀ + 4κE) · obsConn (obs β) (a0 i) (b0 i)`.

The proof: couplings `γ j` with `aRun N (γ j) = aRun N β₀ / 2ʲ`, `γ 0 = β₀`; a large `β` sits in the
octave `aRun N β₀ / 2ⁿ⁺¹ < aRun N β ≤ aRun N β₀ / 2ⁿ`; `factor_chain` along the exact halvings
`γ 0 → … → γ n` with moves `η j = κ ε(aRun N β₀ / 2ʲ)` (`pair_step`) and one `factor_step` from `γ n`
to `β`. The losses are non-negative (each bounds a square root), each is at most `E`
(`le_budget_of_nonneg`), and `κE ≤ 1/4` keeps every move at most `1/2`.

DERIVED: `4` is `factor_step`'s coefficient; `1` is the least colour count, for `aRun_pos`, and the
upper end of the factor; `0` is the sign of `β₀` and the lower end of `q₀`; `2` is the block factor.
-/
theorem obsFactor_eventually_of_uvEntropy (hN1 : 1 ≤ N) {obs : ℝ → Measure Y}
    (hprob : ∀ β, IsProbabilityMeasure (obs β)) {βUV β₀ q₀ E κ : ℝ} {ε : ℝ → ℝ}
    {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hbudget : UVIRSplit.LossBudget ε (aRun N β₀) E) (hent : UVEntropyStep N obs βUV ε)
    (hK : ClassKappaUV N obs βUV S aw bw a0 b0 κ) (hq₀ : 0 ≤ q₀) (hQ : q₀ + 4 * κ * E ≤ 1)
    (hir : ObsIRFactor obs β₀ S aw bw a0 b0 q₀) :
    ∀ᶠ β in atTop, ∀ i ∈ S,
      obsConn (obs β) (aw i) (bw i) ≤ (q₀ + 4 * κ * E) * obsConn (obs β) (a0 i) (b0 i) := by
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  have hκ : 0 ≤ κ := hK.kappa_nonneg
  -- couplings at the dyadic spacings below `aRun N β₀`
  have hgex : ∀ i : ℕ, ∃ g : ℝ, β₀ ≤ g ∧ aRun N g = aRun N β₀ / 2 ^ (i + 1) := by
    intro i
    have hlt : aRun N β₀ / 2 ^ (i + 1) < aRun N β₀ :=
      div_lt_self ha₀ (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i))
    exact exists_beta_aRun_eq hN1 (div_pos ha₀ (by positivity)) hlt
  choose g hgβ hg using hgex
  obtain ⟨γ, hγ0, hγβ, hγ⟩ : ∃ γ : ℕ → ℝ, γ 0 = β₀ ∧ (∀ i : ℕ, β₀ ≤ γ i) ∧
      ∀ i : ℕ, aRun N (γ i) = aRun N β₀ / 2 ^ i :=
    ⟨(fun i => match i with | 0 => β₀ | k + 1 => g k),
     rfl,
     fun i => by
      cases i with
      | zero => exact le_rfl
      | succ k => exact hgβ k,
     fun i => by
      cases i with
      | zero =>
        show aRun N β₀ = aRun N β₀ / 2 ^ 0
        rw [pow_zero, div_one]
      | succ k =>
        show aRun N (g k) = aRun N β₀ / 2 ^ (k + 1)
        exact hg k⟩
  -- admissibility of the exact halvings
  have hadm1 : ∀ j : ℕ, aRun N (γ j) / 2 ≤ aRun N (γ (j + 1)) := fun j =>
    le_of_eq (by rw [hγ j, hγ (j + 1), pow_succ, div_div])
  have hadm2 : ∀ j : ℕ, aRun N (γ (j + 1)) ≤ aRun N (γ j) := fun j => by
    rw [hγ j, hγ (j + 1), pow_succ, ← div_div]
    have hnn : 0 ≤ aRun N β₀ / 2 ^ j := div_nonneg ha₀.le (by positivity)
    linarith
  -- the losses of the tower
  have hεj : ∀ j : ℕ, ChiStep (obs (γ (j + 1))) (obs (γ j)) (ε (aRun N β₀ / 2 ^ j)) := fun j => by
    have h := hent (γ j) (γ (j + 1)) (hUVβ₀.trans (hγβ j)) (hUVβ₀.trans (hγβ (j + 1)))
      (hadm1 j) (hadm2 j)
    rw [hγ j] at h
    exact h
  have hε0 : ∀ j : ℕ, 0 ≤ ε (aRun N β₀ / 2 ^ j) := fun j =>
    (Real.sqrt_nonneg _).trans (hεj j).le
  have hεE : ∀ j : ℕ, ε (aRun N β₀ / 2 ^ j) ≤ E := le_budget_of_nonneg hbudget hε0
  have hκE : 4 * (κ * E) ≤ 1 - q₀ := by linarith
  have hη : ∀ j : ℕ, κ * ε (aRun N β₀ / 2 ^ j) ≤ 1 / 2 := fun j => by
    have h := mul_le_mul_of_nonneg_left (hεE j) hκ
    linarith
  have hsumκ : ∀ n : ℕ, ∑ j ∈ Finset.range n, κ * ε (aRun N β₀ / 2 ^ j) ≤ κ * E := fun n => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbudget n) hκ
  -- one exact halving on the class
  have hpair : ∀ j : ℕ, ∀ i ∈ S,
      obsConn (obs (γ (j + 1))) (aw i) (bw i) ≤ obsConn (obs (γ j)) (aw i) (bw i)
          + κ * ε (aRun N β₀ / 2 ^ j) * obsConn (obs (γ j)) (a0 i) (b0 i) ∧
        obsConn (obs (γ j)) (a0 i) (b0 i) ≤ obsConn (obs (γ (j + 1))) (a0 i) (b0 i)
          + κ * ε (aRun N β₀ / 2 ^ j) * obsConn (obs (γ j)) (a0 i) (b0 i) := by
    intro j i hi
    have h := pair_step hprob hent hK (hUVβ₀.trans (hγβ j)) (hUVβ₀.trans (hγβ (j + 1)))
      (hadm1 j) (hadm2 j) hi
    rw [hγ j] at h
    exact h
  filter_upwards [WeakCouplingWindow.eventually_aRun_le hN1 ha₀,
    Filter.eventually_ge_atTop βUV, Filter.eventually_gt_atTop (0 : ℝ)] with β hβa hβUV hβ0
  intro i hi
  have ha : 0 < aRun N β := aRun_pos hN1 hβ0
  -- the octave of `β`
  have hex : ∃ n : ℕ, aRun N β₀ / 2 ^ (n + 1) < aRun N β := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (aRun N β₀ / aRun N β) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1)), pow_succ]
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [hn, mul_pos h2n ha]
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, aRun N β₀ / 2 ^ (n + 1) < aRun N β ∧
      ∀ k : ℕ, k < n → ¬ (aRun N β₀ / 2 ^ (k + 1) < aRun N β) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hle : aRun N β ≤ aRun N β₀ / 2 ^ n := by
    cases n with
    | zero =>
      rw [pow_zero, div_one]
      exact hβa
    | succ k => exact not_lt.mp (hmin k (Nat.lt_succ_self k))
  -- the chain of exact halvings to `γ n`
  have hbase : obsConn (obs (γ 0)) (aw i) (bw i) ≤ q₀ * obsConn (obs (γ 0)) (a0 i) (b0 i) := by
    rw [hγ0]
    exact hir i hi
  have hbudn : q₀ + 4 * ∑ j ∈ Finset.range n, κ * ε (aRun N β₀ / 2 ^ j) ≤ 1 := by
    have h := hsumκ n
    linarith
  have hchain : obsConn (obs (γ n)) (aw i) (bw i)
      ≤ (q₀ + 4 * ∑ j ∈ Finset.range n, κ * ε (aRun N β₀ / 2 ^ j))
        * obsConn (obs (γ n)) (a0 i) (b0 i) :=
    factor_chain (fun j => obsConn (obs (γ j)) (aw i) (bw i))
      (fun j => obsConn (obs (γ j)) (a0 i) (b0 i)) (fun j => κ * ε (aRun N β₀ / 2 ^ j)) q₀ n hq₀
      (fun j _ => hK.zero_nonneg (γ j) (hUVβ₀.trans (hγβ j)) i hi)
      (fun j => mul_nonneg hκ (hε0 j)) (fun j _ => hη j) hbudn hbase
      (fun j _ => (hpair j i hi).1) (fun j _ => (hpair j i hi).2) n le_rfl
  -- the last step, from `γ n` to `β`
  have hlast := pair_step hprob hent hK (hUVβ₀.trans (hγβ n)) hβUV
    (by
      rw [hγ n, div_div, ← pow_succ]
      exact hn.le)
    (by
      rw [hγ n]
      exact hle)
    hi
  rw [hγ n] at hlast
  have hS1 : ∑ j ∈ Finset.range n, κ * ε (aRun N β₀ / 2 ^ j) + κ * ε (aRun N β₀ / 2 ^ n)
      ≤ κ * E := by
    have h := hsumκ (n + 1)
    rw [Finset.sum_range_succ] at h
    exact h
  have hsn0 : 0 ≤ ∑ j ∈ Finset.range n, κ * ε (aRun N β₀ / 2 ^ j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg hκ (hε0 j))
  have hηn0 : 0 ≤ κ * ε (aRun N β₀ / 2 ^ n) := mul_nonneg hκ (hε0 n)
  have hsβ : 0 ≤ obsConn (obs β) (a0 i) (b0 i) := hK.zero_nonneg β hβUV i hi
  have hfin := factor_step (hK.zero_nonneg (γ n) (hUVβ₀.trans (hγβ n)) i hi) hsβ hηn0 (hη n)
    (by linarith) (by linarith) hchain hlast.1 hlast.2
  have hmono : (q₀ + 4 * ∑ j ∈ Finset.range n, κ * ε (aRun N β₀ / 2 ^ j)
        + 4 * (κ * ε (aRun N β₀ / 2 ^ n))) * obsConn (obs β) (a0 i) (b0 i)
      ≤ (q₀ + 4 * κ * E) * obsConn (obs β) (a0 i) (b0 i) :=
    mul_le_mul_of_nonneg_right (by linarith) hsβ
  exact hfin.trans hmono

#print axioms obsFactor_eventually_of_uvEntropy

/-- **THE READBACK AT ONE COUPLING.** Every `i ∈ S` is read by a lattice observable
`x ∈ gaugeInvHalfSpaceAlg τ p` at the lag `m₀`: for every `e > 0`, eventually along
`periodicUltra hN β₀`, the observer window pairing at `β₀` is at most the torus pairing of `x` at lag
`m₀` plus `e`, and the torus pairing of `x` at lag `0` is at most the observer lag-zero pairing plus
`e`. It carries the lattice gap at `β₀` to the observer class.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the contact lag and the sign of
`e`. -/
def ObsReadback (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (obs : ℝ → Measure Y) (β₀ : ℝ) (m₀ : ℕ)
    (S : Set ι) (aw bw a0 b0 : ι → Y → ℝ) : Prop :=
  ∀ i ∈ S, ∃ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ∀ e : ℝ, 0 < e →
      ∀ᶠ j in ((periodicUltra hN β₀ : Ultrafilter ℕ) : Filter ℕ),
        obsConn (obs β₀) (aw i) (bw i) ≤ MassGap.PeriodicReduce.torusConn τ p hN β₀ j x m₀ + e ∧
          MassGap.PeriodicReduce.torusConn τ p hN β₀ j x 0 ≤ obsConn (obs β₀) (a0 i) (b0 i) + e

/-- **The lattice gap at one coupling gives the observer factor there.** At `0 ≤ r ≤ 1`,
`TransferGap.GapAt (periodicGaugeInvData τ p hN β₀) r` and `ObsReadback τ p hN obs β₀ m₀ …`:
`ObsIRFactor obs β₀ S aw bw a0 b0 (r ^ m₀)`. `WeakCouplingWindow.torusLag_le_of_gapAt` bounds the
torus pairing of the reading observable at lag `m₀` by `rᵐ⁰` times its lag-zero value plus `e`; the
readback moves both ends to the observer (`Filter.Eventually.exists` on the ultrafilter), giving the
factor up to `3e`, and `e` is arbitrary.

DERIVED: `4` is the spacetime dimension; `0` and `1` are the ends of `r`. The `3` and `6` of the
proof are the slack count and its reciprocal split. -/
theorem obsIRFactor_of_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {obs : ℝ → Measure Y} {β₀ : ℝ}
    {m₀ : ℕ} {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hg : TransferGap.GapAt (periodicGaugeInvData τ p hN β₀) r)
    (hread : ObsReadback τ p hN obs β₀ m₀ S aw bw a0 b0) :
    ObsIRFactor obs β₀ S aw bw a0 b0 (r ^ m₀) := by
  intro i hi
  obtain ⟨x, hx, hxe⟩ := hread i hi
  have hq1 : r ^ m₀ ≤ 1 := pow_le_one₀ hr0 hr1
  have hq0 : 0 ≤ r ^ m₀ := pow_nonneg hr0 m₀
  have key : ∀ e : ℝ, 0 < e → obsConn (obs β₀) (aw i) (bw i)
      ≤ r ^ m₀ * obsConn (obs β₀) (a0 i) (b0 i) + 3 * e := by
    intro e he
    have hlag := WeakCouplingWindow.torusLag_le_of_gapAt τ p hN β₀ hr0 hg m₀ le_rfl x hx e he
    obtain ⟨j, hj1, hj2⟩ := (hlag.and (hxe e he)).exists
    obtain ⟨hA, hB⟩ := hj2
    have hC : r ^ m₀ * MassGap.PeriodicReduce.torusConn τ p hN β₀ j x 0
        ≤ r ^ m₀ * (obsConn (obs β₀) (a0 i) (b0 i) + e) := mul_le_mul_of_nonneg_left hB hq0
    have hD : r ^ m₀ * e ≤ e := mul_le_of_le_one_left he.le hq1
    have hE : r ^ m₀ * (obsConn (obs β₀) (a0 i) (b0 i) + e)
        = r ^ m₀ * obsConn (obs β₀) (a0 i) (b0 i) + r ^ m₀ * e := mul_add _ _ _
    linarith
  by_contra hne
  have hlt : r ^ m₀ * obsConn (obs β₀) (a0 i) (b0 i) < obsConn (obs β₀) (aw i) (bw i) :=
    not_le.mp hne
  have h := key ((obsConn (obs β₀) (aw i) (bw i) - r ^ m₀ * obsConn (obs β₀) (a0 i) (b0 i)) / 6)
    (by linarith)
  linarith

#print axioms obsIRFactor_of_gapAt

/-- **The IR gap at one coupling gives the observer factor there.** At `1 ≤ N`, `0 < β₀`,
`0 ≤ M₀`, `UVIRSplit.IRGapAt τ p hN β₀ M₀` and the readback at lag `m₀`: the observer factor
`(e^{−M₀·aRun N β₀})ᵐ⁰` at `β₀` (`obsIRFactor_of_gapAt` at `r = e^{−M₀·aRun N β₀} ∈ (0, 1]`).

DERIVED: `4` is the spacetime dimension; `1` is the least colour count, for `aRun_pos`; `0` is the
excluded rank and the sign of `β₀` and `M₀`. -/
theorem obsIRFactor_of_irGapAt (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0)
    {obs : ℝ → Measure Y} {β₀ M₀ : ℝ} {m₀ : ℕ} {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ}
    (hβ₀ : 0 < β₀) (hM₀ : 0 ≤ M₀) (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀)
    (hread : ObsReadback τ p hN obs β₀ m₀ S aw bw a0 b0) :
    ObsIRFactor obs β₀ S aw bw a0 b0 (Real.exp (-(M₀ * aRun N β₀)) ^ m₀) :=
  obsIRFactor_of_gapAt τ p hN (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hM₀ (aRun_pos hN1 hβ₀).le))) hir hread

#print axioms obsIRFactor_of_irGapAt

/-- **The bridge at one coupling.** Some lag `m ≠ 0` with `m · aRun N β ≤ L` has: every
`x ∈ gaugeInvHalfSpaceAlg τ p` is read by some `i ∈ S`, in the sense that for every `e > 0`,
eventually along `periodicUltra hN β`, the torus pairing of `x` at lag `m` is at most the observer
window pairing plus `e`, and the observer lag-zero pairing is at most the torus pairing of `x` at lag
`0` plus `e`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the excluded lag, the contact lag
and the sign of `e`. -/
def BridgeAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) (obs : ℝ → Measure Y) (S : Set ι)
    (aw bw a0 b0 : ι → Y → ℝ) (β : ℝ) : Prop :=
  ∃ m : ℕ, m ≠ 0 ∧ (m : ℝ) * aRun N β ≤ L ∧
    ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∃ i ∈ S, ∀ e : ℝ, 0 < e →
        ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x m ≤ obsConn (obs β) (aw i) (bw i) + e ∧
            obsConn (obs β) (a0 i) (b0 i) ≤ MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + e

/-- **THE CARRIER BRIDGE OF THE ENTROPY ROUTE.** `BridgeAt τ p hN L obs S aw bw a0 b0 β` at every
large `β`: the lattice-scale class `gaugeInvHalfSpaceAlg` on the periodic tori, at a lag inside the
window `L`, is dominated by the observer class `S` of block-field observables at the same coupling.
It is where the lattice-scale class enters; `UVEntropyStep` and `ClassKappaUV` concern the observer
class only.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
def UVEntropyBridge (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) (obs : ℝ → Measure Y) (S : Set ι)
    (aw bw a0 b0 : ι → Y → ℝ) : Prop :=
  ∀ᶠ β in atTop, BridgeAt τ p hN L obs S aw bw a0 b0 β

/-- **`FixedWindowDecay` from an observer factor below one.** At `0 ≤ Q < 1`, with the observer
lag-zero pairings non-negative and the factor `Q` on the class at every large `β`, and
`UVEntropyBridge τ p hN L obs S aw bw a0 b0`: `WeakCouplingWindow.FixedWindowDecay τ p hN L`, at the
factor `(1 + Q)/2`. At each `x` and `e`, the torus pairing at the bridge's lag is at most
`(1 + Q)/2 · (torus pairing at lag 0 + e/2) + e/2`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `Q`; `1` is
the upper end of `Q`. CHOSEN: `(1 + Q)/2`, a factor in `(Q, 1)`, and `e/2`, the slack handed to the
bridge; any factor in `[Q, 1)` that is positive, and any split of `e`, serve. -/
theorem fixedWindowDecay_of_obsFactor (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {L : ℝ}
    {obs : ℝ → Measure Y} {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ} {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ1 : Q < 1) (hnn : ∀ᶠ β in atTop, ∀ i ∈ S, 0 ≤ obsConn (obs β) (a0 i) (b0 i))
    (hfac : ∀ᶠ β in atTop, ∀ i ∈ S,
      obsConn (obs β) (aw i) (bw i) ≤ Q * obsConn (obs β) (a0 i) (b0 i))
    (hbr : UVEntropyBridge τ p hN L obs S aw bw a0 b0) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  have hbr' : ∀ᶠ β in atTop, BridgeAt τ p hN L obs S aw bw a0 b0 β := hbr
  refine ⟨(1 + Q) / 2, by linarith, by linarith, ?_⟩
  filter_upwards [hnn, hfac, hbr'] with β hn hf hb
  obtain ⟨m, hm, hmL, hx⟩ := hb
  refine ⟨m, hm, hmL, fun x hxS e he => ?_⟩
  obtain ⟨i, hi, hij⟩ := hx x hxS
  filter_upwards [hij (e / 2) (half_pos he)] with j hj
  obtain ⟨h1, h2⟩ := hj
  have h3 := hf i hi
  have h4 := hn i hi
  have h5 : Q * obsConn (obs β) (a0 i) (b0 i) ≤ (1 + Q) / 2 * obsConn (obs β) (a0 i) (b0 i) :=
    mul_le_mul_of_nonneg_right (by linarith) h4
  have h6 : (1 + Q) / 2 * obsConn (obs β) (a0 i) (b0 i)
      ≤ (1 + Q) / 2 * (MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + e / 2) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h7 : (1 + Q) / 2 * (e / 2) ≤ e / 2 :=
    mul_le_of_le_one_left (half_pos he).le (by linarith)
  have h8 : (1 + Q) / 2 * (MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + e / 2)
      = (1 + Q) / 2 * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + (1 + Q) / 2 * (e / 2) :=
    mul_add _ _ _
  linarith

#print axioms fixedWindowDecay_of_obsFactor

/-- **`FixedWindowDecay` from the IR gap at one coupling and the entropy step.** At `1 ≤ N`,
`PeriodicObserverLaws hN φ obs`, `0 < β₀`, `βUV ≤ β₀`, `0 ≤ M₀`, `UVIRSplit.IRGapAt τ p hN β₀ M₀`,
`ObsReadback τ p hN obs β₀ m₀ …`, a loss budget `E` below `aRun N β₀` with
`(e^{−M₀·aRun N β₀})ᵐ⁰ + 4κE < 1`, `UVEntropyStep N obs βUV ε`,
`ClassKappaUV N obs βUV S aw bw a0 b0 κ` and `UVEntropyBridge τ p hN L obs S aw bw a0 b0`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L`. `obsIRFactor_of_irGapAt`,
`obsFactor_eventually_of_uvEntropy` and `fixedWindowDecay_of_obsFactor`; the budget at `n = 0` gives
`E ≥ 0`.

DERIVED: `4` is the spacetime dimension and `factor_step`'s coefficient; `1` is the least colour
count and the factor the decay must beat; `0` is the excluded rank and the sign of `β₀`, `M₀`. -/
theorem fixedWindowDecay_of_uvEntropy_ir (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {L : ℝ}
    {φ : ℝ → MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → Y} {obs : ℝ → Measure Y}
    (hlaw : PeriodicObserverLaws hN φ obs) {βUV β₀ M₀ E κ : ℝ} {ε : ℝ → ℝ} {m₀ : ℕ}
    {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hM₀ : 0 ≤ M₀)
    (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀) (hread : ObsReadback τ p hN obs β₀ m₀ S aw bw a0 b0)
    (hbud : UVIRSplit.LossBudget ε (aRun N β₀) E)
    (hbelow : Real.exp (-(M₀ * aRun N β₀)) ^ m₀ + 4 * κ * E < 1)
    (hent : UVEntropyStep N obs βUV ε) (hK : ClassKappaUV N obs βUV S aw bw a0 b0 κ)
    (hbr : UVEntropyBridge τ p hN L obs S aw bw a0 b0) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  have hprob : ∀ β, IsProbabilityMeasure (obs β) := isProbability_of_periodicObserverLaws hN hlaw
  have hq := obsIRFactor_of_irGapAt τ p hN1 hN hβ₀ hM₀ hir hread
  have hq0 : 0 ≤ Real.exp (-(M₀ * aRun N β₀)) ^ m₀ := pow_nonneg (Real.exp_pos _).le m₀
  have hfac := obsFactor_eventually_of_uvEntropy hN1 hprob hβ₀ hUVβ₀ hbud hent hK hq0 hbelow.le hq
  have hE0 : 0 ≤ E := by
    have h := hbud 0
    rw [Finset.sum_range_zero] at h
    exact h
  have hκE : 0 ≤ κ * E := mul_nonneg hK.kappa_nonneg hE0
  have hnn : ∀ᶠ β in atTop, ∀ i ∈ S, 0 ≤ obsConn (obs β) (a0 i) (b0 i) :=
    (Filter.eventually_ge_atTop βUV).mono (fun β hβ i hi => hK.zero_nonneg β hβ i hi)
  exact fixedWindowDecay_of_obsFactor τ p hN (by linarith) hbelow hnn hfac hbr

#print axioms fixedWindowDecay_of_uvEntropy_ir

/-- **THE UV STEP IN ENTROPY FORM, BELOW THE RATE `M₀`.** Some loss function `ε` and budget `E` have
`UVIRSplit.LossBudget ε (aRun N β₀) E`, `(e^{−M₀·aRun N β₀})ᵐ⁰ + 4κE < 1` and
`UVEntropyStep N obs βUV ε`. The entropy analogue of `ClayRoutes.UVBelowIR` at the rate `M₀`.

DERIVED: `4` is the spacetime dimension and `factor_step`'s coefficient; `1` is the factor the decay
must beat; `0` is the excluded rank. -/
def EntropyBelowIR (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (obs : ℝ → Measure Y) (β₀ βUV : ℝ) (m₀ : ℕ)
    (κ M₀ : ℝ) : Prop :=
  ∃ (ε : ℝ → ℝ) (E : ℝ), UVIRSplit.LossBudget ε (aRun N β₀) E ∧
    Real.exp (-(M₀ * aRun N β₀)) ^ m₀ + 4 * κ * E < 1 ∧ UVEntropyStep N obs βUV ε

end Wilson

section Capstone

open MassGap.ContinuumField MassGap.ContinuumSchwinger

variable {N : ℕ}

/-- **THE CLAY CONTINUUM STATEMENT FROM ONE BOX AND THE ENTROPY STEP.** At `2 ≤ N`, a
reflection-invariant `Z`, the separated uniform bound `hB` (E), a window `L > 0`, a coupling
`0 < β₀` with `βUV ≤ β₀` and `βUV` past the peak of `aRun N`, `BoxPatch.BoxPatchGap hN β₀ n γ` (M-middle), observer laws of the periodic
state (`PeriodicObserverLaws`), the readback at `β₀` (`ObsReadback`), `ClassKappaUV` and the carrier
bridge (`UVEntropyBridge`), `ContinuumNontrivial.KernelConvergesSep` towards a radial `G` (N) and
`ShortDistanceY.AFShortDistance G` (Y), and the entropy step below the box's rate
(`EntropyBelowIR … (HeatBathLocal.boxRate N β₀ n γ)`, M-UV): `ClayRoutes.ClayContinuum hN Z τ hZ hB L`.
`HeatBathLocal.irGapAt_boxRate` gives the IR gap at that rate, `fixedWindowDecay_of_uvEntropy_ir` the
uniform physical gap, and `ClayRoutes.clay_continuum_of_fixedWindowDecay` the conclusion.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension; `1`
in the proof is the least colour count. `17N²/(88π²)` is the peak of `aRun N` (`AsymptoticScaling.aRun`, the peak `17N²/(44π²)` of `aRunStd` at
`β_std = 2β`). CHOSEN: the scope restriction `_hpeak`, not used by the proof, keeps every coupling of the UV step where `aRun N` decreases, so each step of the tower refines the spacing. The peak lies deep in strong coupling (about `0.078` at `N = 2`); the physical crossover (Lean `β ≈ 1.1` at `N = 2`, `≈ 2.85` at `N = 3`) lies at larger `β`, inside the UV step unless `β₀` is past it.
-/
theorem clay_continuum_of_boxPatchGap_entropy (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (_hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    {φ : ℝ → MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → Y} {obs : ℝ → Measure Y}
    (hlaw : PeriodicObserverLaws hN φ obs) {m₀ : ℕ} {S : Set ι} {aw bw a0 b0 : ι → Y → ℝ}
    {κ : ℝ} (hread : ObsReadback τ 0 hN obs β₀ m₀ S aw bw a0 b0)
    (hK : ClassKappaUV N obs βUV S aw bw a0 b0 κ)
    (hbelow : EntropyBelowIR τ 0 hN obs β₀ βUV m₀ κ (HeatBathLocal.boxRate N β₀ n γ))
    (hbr : UVEntropyBridge τ 0 hN L obs S aw bw a0 b0)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  obtain ⟨hM₀, hir⟩ := HeatBathLocal.irGapAt_boxRate τ 0 (by omega : 1 ≤ N) hN hβ₀ hbox
  obtain ⟨ε, E, hbud, hlt, hent⟩ := hbelow
  exact ClayRoutes.clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL
    (fixedWindowDecay_of_uvEntropy_ir τ 0 (by omega) hN hlaw hβ₀ hUVβ₀ hM₀.le hir hread hbud hlt
      hent hK hbr) O G hconv hY

#print axioms clay_continuum_of_boxPatchGap_entropy

end Capstone

/-! ## 4. The effective-density side -/

section Density

/-- **A density band of width `D`.** `P' ≪ P` and, `P`-almost everywhere,
`e^{−D} ≤ dP'/dP ≤ e^{D}`: the log-density of `P'` against `P` lies in `[−D, D]`.

DERIVED: no numeral. -/
structure DensityBand (P' P : Measure Y) (D : ℝ) : Prop where
  /-- `P'` is absolutely continuous with respect to `P`. -/
  ac : P' ≪ P
  /-- The density lies in `[e^{−D}, e^{D}]` almost everywhere. -/
  band : ∀ᵐ y ∂P, Real.exp (-D) ≤ (P'.rnDeriv P y).toReal ∧ (P'.rnDeriv P y).toReal ≤ Real.exp D

/-- **A density band bounds `χ²`.** At a probability measure `P`, `0 ≤ D` and `DensityBand P' P D`:
`ChiStep P' P (e^{D} − 1)`. The density minus one lies in `[e^{−D} − 1, e^{D} − 1]`, and
`e^{−D} + e^{D} ≥ 2` (`Real.add_one_le_exp` twice) puts it in `[−(e^{D} − 1), e^{D} − 1]`; the square
is bounded, hence integrable, and `χ² ≤ (e^{D} − 1)²`.

DERIVED: `1` is the density of `P` against itself; `2` is the square and `e^{−D} + e^{D} ≥ 2`; `0` is
the lower end of `D`. -/
theorem chiStep_of_densityBand {P' P : Measure Y} [IsProbabilityMeasure P] {D : ℝ} (hD : 0 ≤ D)
    (h : DensityBand P' P D) : ChiStep P' P (Real.exp D - 1) := by
  have hc0 : 0 ≤ Real.exp D - 1 := by linarith [Real.one_le_exp hD]
  have hsum : 2 ≤ Real.exp (-D) + Real.exp D := by
    linarith [Real.add_one_le_exp (-D), Real.add_one_le_exp D]
  have hpt : ∀ᵐ y ∂P, ((P'.rnDeriv P y).toReal - 1) ^ 2 ≤ (Real.exp D - 1) ^ 2 := by
    filter_upwards [h.band] with y hy
    obtain ⟨hlo, hhi⟩ := hy
    exact sq_le_sq' (by linarith) (by linarith)
  have hbd : ∀ᵐ y ∂P, ‖((P'.rnDeriv P y).toReal - 1) ^ 2‖ ≤ (Real.exp D - 1) ^ 2 := by
    filter_upwards [hpt] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hy
  have hmeas : AEStronglyMeasurable (fun y => ((P'.rnDeriv P y).toReal - 1) ^ 2) P :=
    (((Measure.measurable_rnDeriv P' P).ennreal_toReal.sub_const 1).pow_const 2).aestronglyMeasurable
  have hint : Integrable (fun y => ((P'.rnDeriv P y).toReal - 1) ^ 2) P :=
    Integrable.of_bound hmeas ((Real.exp D - 1) ^ 2) hbd
  have hchi : ChiForest.chiSq P' P ≤ (Real.exp D - 1) ^ 2 := by
    unfold ChiForest.chiSq
    calc ∫ y, ((P'.rnDeriv P y).toReal - 1) ^ 2 ∂P ≤ ∫ _y, (Real.exp D - 1) ^ 2 ∂P :=
          integral_mono_ae hint (integrable_const _) hpt
      _ = (Real.exp D - 1) ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  refine ⟨⟨h.ac, hint⟩, ?_⟩
  calc Real.sqrt (ChiForest.chiSq P' P) ≤ Real.sqrt ((Real.exp D - 1) ^ 2) :=
        Real.sqrt_le_sqrt hchi
    _ = Real.exp D - 1 := Real.sqrt_sq hc0

#print axioms chiStep_of_densityBand

/-- `e^{x} − 1 ≤ x e^{x}`: `1 − x ≤ e^{−x}` (`Real.add_one_le_exp`) times `e^{x}`.

DERIVED: `1` is the value of `e^{0}`. -/
theorem expm1_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos x).le
  linarith

#print axioms expm1_le_mul_exp

/-- **A budget for the band widths gives a budget for the `χ²` losses.** With `D (a₀ / 2ⁱ) ≥ 0` at
every `i` and `UVIRSplit.LossBudget D a₀ E`: `LossBudget (fun a => e^{D a} − 1) a₀ (E · e^{E})`.
Each width is at most `E` (`Finset.single_le_sum`), and `e^{D} − 1 ≤ D e^{D} ≤ D e^{E}`
(`expm1_le_mul_exp`).

DERIVED: `2` is the block factor; `0` is the sign of the widths; `1` is `e^{0}`. -/
theorem lossBudget_expm1 {D : ℝ → ℝ} {a₀ E : ℝ} (hD0 : ∀ i : ℕ, 0 ≤ D (a₀ / 2 ^ i))
    (hb : UVIRSplit.LossBudget D a₀ E) :
    UVIRSplit.LossBudget (fun a => Real.exp (D a) - 1) a₀ (E * Real.exp E) := by
  intro n
  show ∑ i ∈ Finset.range n, (Real.exp (D (a₀ / 2 ^ i)) - 1) ≤ E * Real.exp E
  have hterm : ∀ i ∈ Finset.range n,
      Real.exp (D (a₀ / 2 ^ i)) - 1 ≤ D (a₀ / 2 ^ i) * Real.exp E := by
    intro i hi
    have hs : D (a₀ / 2 ^ i) ≤ ∑ j ∈ Finset.range n, D (a₀ / 2 ^ j) :=
      Finset.single_le_sum (f := fun j => D (a₀ / 2 ^ j)) (fun j _ => hD0 j) hi
    have hle : D (a₀ / 2 ^ i) ≤ E := hs.trans (hb n)
    have h1 := expm1_le_mul_exp (D (a₀ / 2 ^ i))
    have h2 : D (a₀ / 2 ^ i) * Real.exp (D (a₀ / 2 ^ i)) ≤ D (a₀ / 2 ^ i) * Real.exp E :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (hD0 i)
    linarith
  calc ∑ i ∈ Finset.range n, (Real.exp (D (a₀ / 2 ^ i)) - 1)
      ≤ ∑ i ∈ Finset.range n, D (a₀ / 2 ^ i) * Real.exp E := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range n, D (a₀ / 2 ^ i)) * Real.exp E := (Finset.sum_mul _ _ _).symm
    _ ≤ E * Real.exp E := mul_le_mul_of_nonneg_right (hb n) (Real.exp_pos E).le

#print axioms lossBudget_expm1

/-- **Power-law widths have a budget.** At `0 ≤ C`, `0 < γ` and `0 < a₀`, the widths `C a^γ` at the
dyadic spacings below `a₀` sum to at most `C a₀^γ / (1 − 2^{−γ})`: `(a₀/2ⁱ)^γ = a₀^γ (2^{−γ})ⁱ`
(`Real.div_rpow`, `Real.rpow_pow_comm`) and the geometric sum (`geom_sum_Ico_le_of_lt_one`).

DERIVED: `2` is the block factor; `0` is the lower end of `C`, `γ`, `a₀`; `1` is the geometric
sum's numerator and the bound `2^{−γ} < 1`. -/
theorem lossBudget_rpow {C γ a₀ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) (ha₀ : 0 < a₀) :
    UVIRSplit.LossBudget (fun a => C * a ^ γ) a₀ (C * a₀ ^ γ / (1 - ((2 : ℝ) ^ γ)⁻¹)) := by
  intro n
  show ∑ i ∈ Finset.range n, C * (a₀ / 2 ^ i) ^ γ ≤ C * a₀ ^ γ / (1 - ((2 : ℝ) ^ γ)⁻¹)
  have h2γ : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  have hθ0 : 0 ≤ ((2 : ℝ) ^ γ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hθ1 : ((2 : ℝ) ^ γ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2γ
  have hterm : ∀ i : ℕ, C * (a₀ / 2 ^ i) ^ γ = C * a₀ ^ γ * ((2 : ℝ) ^ γ)⁻¹ ^ i := by
    intro i
    rw [Real.div_rpow ha₀.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i) γ,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), inv_pow]
    ring
  have hsum : ∑ i ∈ Finset.range n, ((2 : ℝ) ^ γ)⁻¹ ^ i ≤ 1 / (1 - ((2 : ℝ) ^ γ)⁻¹) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hθ0 hθ1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    exact h
  have hC0 : 0 ≤ C * a₀ ^ γ := mul_nonneg hC (Real.rpow_nonneg ha₀.le γ)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  calc C * a₀ ^ γ * ∑ i ∈ Finset.range n, ((2 : ℝ) ^ γ)⁻¹ ^ i
      ≤ C * a₀ ^ γ * (1 / (1 - ((2 : ℝ) ^ γ)⁻¹)) := mul_le_mul_of_nonneg_left hsum hC0
    _ = C * a₀ ^ γ / (1 - ((2 : ℝ) ^ γ)⁻¹) := by ring

#print axioms lossBudget_rpow

/-- **A constant positive loss has no budget.** At `0 < c`, `UVIRSplit.LossBudget (fun _ => c) a₀ E`
fails: `n` losses sum to `n c`, above every `E` (`exists_nat_gt`).

DERIVED: `0` is the sign of `c`. -/
theorem not_lossBudget_const {c a₀ E : ℝ} (hc : 0 < c) :
    ¬ UVIRSplit.LossBudget (fun _ => c) a₀ E := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (E / c)
  have h1 : ∑ i ∈ Finset.range n, c ≤ E := h n
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 : E < n * c := (div_lt_iff₀ hc).mp hn
  linarith

#print axioms not_lossBudget_const

variable {N : ℕ}

/-- **AN EXTENSIVE BAND.** Every admissible pair `β → β'` has `DensityBand (obs β') (obs β) (Eb · V)`:
a band on the log-density of the finer observer law against the coarser one whose width `Eb · V` is
fixed in the spacing — the form a uniform-in-`k` bound extensive in a block count `V` takes on the
ratio of two observer laws. Balaban's published bounds band each effective density against its own
leading term, not this ratio; the Prop is stated, not claimed.

DERIVED: `2` is the block factor. -/
def ExtensiveDensityBand (N : ℕ) (obs : ℝ → Measure Y) (βUV Eb V : ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' → aRun N β' ≤ aRun N β →
    DensityBand (obs β') (obs β) (Eb * V)

/-- **An extensive band gives the entropy step at a constant loss.** At probability observer laws and
`0 ≤ Eb · V`: `ExtensiveDensityBand N obs βUV Eb V` gives `UVEntropyStep N obs βUV` at the constant
loss `e^{Eb V} − 1` (`chiStep_of_densityBand`), which at `Eb · V > 0` has no finite budget
(`not_lossBudget_const`).

DERIVED: `0` is the lower end of the width; `1` is `chiStep_of_densityBand`'s. -/
theorem uvEntropyStep_of_extensive {obs : ℝ → Measure Y} (hprob : ∀ β, IsProbabilityMeasure (obs β))
    {βUV Eb V : ℝ} (hEV : 0 ≤ Eb * V) (h : ExtensiveDensityBand N obs βUV Eb V) :
    UVEntropyStep N obs βUV (fun _ => Real.exp (Eb * V) - 1) := by
  intro β β' h1 h2 h3 h4
  haveI := hprob β
  exact chiStep_of_densityBand hEV (h β β' h1 h2 h3 h4)

#print axioms uvEntropyStep_of_extensive

/-- **THE PER-REGION, SUMMABLE BAND.** Every admissible pair `β → β'` has
`DensityBand (obs β') (obs β) (C · V · aRun N β ^ γ)`: the log-density of the finer observer law
against the coarser one is at most `C · V · a^γ` in absolute value, `a = aRun N β`, with `V` the
number of blocks of the fixed physical observer region (fixed as `a → 0`) and `γ` the decay exponent
of the irrelevant terms. Its content is the locality of the effective action's remainder (the width
proportional to the region's block count, independent of the torus) and the decay of the difference
of the effective actions from spacings `a` and `a/2` at matched running coupling (`O(a^γ)` per
block). Stated, not claimed.

DERIVED: `2` is the block factor. -/
def LocalRemainderDecay (N : ℕ) (obs : ℝ → Measure Y) (βUV C V γ : ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' → aRun N β' ≤ aRun N β →
    DensityBand (obs β') (obs β) (C * V * aRun N β ^ γ)

/-- **The per-region band gives the entropy step.** At `1 ≤ N`, `0 < βUV`, probability observer
laws, `0 ≤ C`, `0 ≤ V` and `LocalRemainderDecay N obs βUV C V γ`:
`UVEntropyStep N obs βUV (fun a => e^{C V a^γ} − 1)` (`chiStep_of_densityBand`; the width is
non-negative since `aRun N β > 0` at `β ≥ βUV > 0`).

DERIVED: `1` is the least colour count, for `aRun_pos`, and `chiStep_of_densityBand`'s; `0` is the
sign of `βUV`, `C`, `V`. -/
theorem uvEntropyStep_of_localRemainderDecay (hN1 : 1 ≤ N) {obs : ℝ → Measure Y}
    (hprob : ∀ β, IsProbabilityMeasure (obs β)) {βUV C V γ : ℝ} (hUV : 0 < βUV) (hC : 0 ≤ C)
    (hV : 0 ≤ V) (h : LocalRemainderDecay N obs βUV C V γ) :
    UVEntropyStep N obs βUV (fun a => Real.exp (C * V * a ^ γ) - 1) := by
  intro β β' h1 h2 h3 h4
  haveI := hprob β
  have ha : 0 < aRun N β := aRun_pos hN1 (lt_of_lt_of_le hUV h1)
  exact chiStep_of_densityBand (mul_nonneg (mul_nonneg hC hV) (Real.rpow_nonneg ha.le γ))
    (h β β' h1 h2 h3 h4)

#print axioms uvEntropyStep_of_localRemainderDecay

/-- **The per-region band's losses have a budget.** At `0 ≤ C`, `0 ≤ V`, `0 < γ` and `0 < a₀`, the
losses `e^{C V a^γ} − 1` at the dyadic spacings below `a₀` sum to at most `B e^{B}`,
`B = C V a₀^γ / (1 − 2^{−γ})`: `lossBudget_rpow` and `lossBudget_expm1`. `B` is proportional to
`a₀^γ`, so the budget below a small spacing is small.

DERIVED: `2` is the block factor; `0` is the lower end of `C`, `V`, `γ`, `a₀`; `1` is
`lossBudget_rpow`'s. -/
theorem lossBudget_localRemainder {C V γ a₀ : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hγ : 0 < γ)
    (ha₀ : 0 < a₀) :
    UVIRSplit.LossBudget (fun a => Real.exp (C * V * a ^ γ) - 1) a₀
      (C * V * a₀ ^ γ / (1 - ((2 : ℝ) ^ γ)⁻¹)
        * Real.exp (C * V * a₀ ^ γ / (1 - ((2 : ℝ) ^ γ)⁻¹))) :=
  lossBudget_expm1 (D := fun a => C * V * a ^ γ)
    (fun i => mul_nonneg (mul_nonneg hC hV)
      (Real.rpow_nonneg (div_pos ha₀ (pow_pos (by norm_num : (0 : ℝ) < 2) i)).le γ))
    (lossBudget_rpow (mul_nonneg hC hV) hγ ha₀)

#print axioms lossBudget_localRemainder

end Density

end MassGap.UVEntropy
