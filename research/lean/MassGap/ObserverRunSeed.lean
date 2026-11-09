import Mathlib
import MassGap.InputMerge
import MassGap.EnergySeed

/-!
# MassGap.ObserverRunSeed — the run seed read on the observer's energy density

`InputMerge.NarrowInputsAtMin` keeps `WDeltaRun.RunSeed N` as its one input that reads neither the composites
nor the observer: a bound on `defectW N β n = 16 log ZR(n) − log ZR(2n)` at one physical side, eventually in
`β`. This module reads that bound on one local, centre-neutral observable, the energy density per site, as a
budget on how that reading changes when the box doubles, proves the budget form equivalent to the run seed,
records a no-go for the flat-budget form, and states the capstone with the budget form.

## 1. The box reading (defined; the identity proved)

* `boxRead N n β = ⟨S⟩_n / n⁴`: the mean Wilson action per site on the periodic box of side `n`
  (`EffectiveCoupling.meanAction`), the plaquette energy density averaged over the box.
* `finiteSize_eq_boxRead`: `EnergySeed.finiteSize N n β = 16 n⁴ (boxRead N (2n) β − boxRead N n β)` at `n ≠ 0`.
  The β-derivative of the defect (`EffectiveCoupling.hasDerivAt_defectW`) is the change of this reading when
  the box doubles, times the site count `16 n⁴` of the doubled box.

## 2. The budget form (defined; equivalence with the run seed proved)

* `ZoomSelfW N n β`: there is a budget `Φ` with `Φ 0 = 0`, `Φ β ≤ 1/1000`, derivative `φ` on `[0, β]`, and
  `16 n⁴ (boxRead N (2n) x − boxRead N n x) ≤ φ x` at every `x ∈ [0, β)`. The doubling change of the reading is
  bounded by a rate whose total over the couplings `[0, β]` is at most the sharp seed; for an integrable `φ`
  that total is `∫₀^β φ`. A weight concentrated near `β`, such as `φ(x) = (c/1000) e^{−c(β−x)}`, fits a reading
  whose change is concentrated near `β`.
* `ObsRunSeedW N`: there is `C > 0` such that, eventually in `β`, some power of two `n ≥ 2` with
  `n · aRun N β ≤ C` has `ZoomSelfW N n β`. The window is `RunSeed`'s.
* `defectW_le_of_zoomSelfW` (`EnergySeed.defectW_le_of_budget` from `defectW N 0 n = 0`) and
  `zoomSelfW_of_defectW` (the defect itself is a budget): `ZoomSelfW N n β ↔ defectW N β n ≤ 1/1000` at
  `0 ≤ β`, `n ≠ 0`.
* **`obsRunSeedW_iff`**: `ObsRunSeedW N ↔ WDeltaRun.RunSeed N` at `N ≠ 0`.

So `ObsRunSeedW` is the run seed restated on the observer's energy reading: it is satisfiable exactly when
`RunSeed N` holds, and it removes no content. Physically (argued, not a declaration) the integrand is
`∝ e^{−m n a(x)} (−d log a/dx)`, concentrated within `O(1)` of `β` when `n ≈ C/a(β)` with `C` many correlation
lengths; at boxes far below the correlation length the integrand is Coulomb-like, `≈ κ/x`
(`EnergySeed.defectW_log_growth`), so the side must be taken near `C/a`, not small.

## 3. The flat budget: a recorded no-go (proved, conditional)

* `ZoomSelfFlat N n β`: the doubling change of the reading at most `1/(16000 n⁴ β)` at every `x ∈ [0, β)`,
  a flat rate `1/(1000 β)` for `finiteSize`. `ObsRunSeedFlat N`: the same window.
* `finiteSize_le_of_zoomSelfFlat`: it bounds `finiteSize N n x ≤ 1/(1000 β)` on `[0, β)`.
* `not_obsRunSeedFlat`: if for every `C > 0` some `c₀ > 0` has, eventually in `β`, at every power-of-two side
  `n ≥ 2` with `n a ≤ C`, a coupling `x ∈ [0, β)` with `finiteSize N n x ≥ c₀`, then `¬ ObsRunSeedFlat N`.
  The constant `c₀` depends on `C`: in the scaling regime `finiteSize` near `β` at `n a ≈ L ≤ C` tends to a
  `β`-independent positive value (the `16 n⁴` cancels the `n⁴`, `d log a/dβ` tends to a constant), which
  decreases as `C` grows, and at small `L` it is `≈ κ/x`; that the hypothesis
  holds is argued, not proved. The flat rate discards the factor `β` that the concentration near `β` supplies.

## 4. Gauge covariance of the flow under central height twists (proved)

* `heightTwist ν z h U`: every link along `ν` at `x` multiplied by `z^{h(x_ν + 1) − h(x_ν)}`.
* `heightTwist_eq_igaugeTransform`: for central `z` it is the local gauge transformation `x ↦ (z^{h(x_ν)})⁻¹`.
* `flow_heightTwist`: every `ConfFlow` commutes with it (`ConfFlow.gauge`); `fieldMap_heightTwist`: every
  flowed reading `W.fieldMap k O` is unchanged by it.

These are gauge covariance on `ℤ⁴`. They say nothing about twisted boundary conditions or flux sectors on a
torus. That the flux half of `FluxCost.runSeed_iff_bindingPlane` (ratios of twisted to untwisted torus
partition functions) is not a reading of the observer's local flowed fields is argued from them, not proved.
The energy route of §1–§2 uses no centre data: the β-derivative of the whole defect is the box dependence of
the centre-neutral energy density.

## 5. The capstone

* `NarrowInputsObs N hN2 W r`: `InputMerge.NarrowInputsAtMin N hN2 W r` with `RunSeed N` replaced by
  `ObsRunSeedW N`; `narrowInputsAtMin_of_obs`, `narrowInputsObs_of_atMin` (the two bundles are equivalent).
* **`clayStatement_of_obsRunSeed`**: `∃ W r, NarrowInputsObs N hN2 W r` at every `N ≥ 2` gives
  `MassGap.ClayStatementDy`.

## What is open

`ObsRunSeedW N`, equivalently `RunSeed N`, is open for every `N`. Two comparisons are not built:

* `boxRead` is read on `RectWilson.sysR` at constant extent `n`. Its identification with the observer's bare
  reading in `PeriodicState.torusState hN (n − 1) β` (the plaquette field `ObserverEnergyMoments.plaqField`
  at one site, by translation invariance of the torus Gibbs state, and `RectWilson.rbd = WilsonHypercubic.bd`
  at constant extent) is a finite-volume identity, not built here.
* The observer reads flowed fields, `W.fieldMap k O`; `ZoomSelfW` reads the bare energy density. A flowed form
  gives `ZoomSelfW` only through a comparison of the box dependence of the bare and the flowed energy densities
  at every coupling below `β`, at growing side. No module relates them; an extensive error does not cancel in
  the defect, so a per-site closeness of the two readings does not give it.

DERIVED (module-wide): `16 = 2⁴` the copies of the side-`n` box in the side-`2n` box; `4` the dimension;
`2` the doubling and the least side; `1/1000` the sharp seed; `16000 = 16 · 1000`; `0` the coupling at which
the defect vanishes; `1` the unit step of a link.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverRunSeed

open Real Filter Set
open MassGap MassGap.ZoomSelfScale MassGap.EffectiveCoupling MassGap.EnergySeed

variable {N : ℕ}

/-! ## 1. The box reading -/

/-- **The box reading**: the mean Wilson action per site on the periodic box of side `n`.
DERIVED: `4` the dimension. -/
def boxRead (N n : ℕ) (β : ℝ) : ℝ := meanAction N (fun _ => n) β / (n : ℝ) ^ 4

/-- **The finite-size part is the change of the box reading under doubling**, times `16 n⁴`.
DERIVED: `16 = 2⁴`; `2` the doubling; `4` the dimension. -/
theorem finiteSize_eq_boxRead {n : ℕ} (hn : n ≠ 0) (β : ℝ) :
    finiteSize N n β = 16 * (n : ℝ) ^ 4 * (boxRead N (2 * n) β - boxRead N n β) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold finiteSize boxRead
  push_cast
  field_simp
  ring

/-! ## 2. The budget form -/

/-- **The doubling change of the box reading within a budget**: `Φ 0 = 0`, `Φ β ≤ 1/1000`, `Φ' = φ` on
`[0, β]`, and `16 n⁴ (boxRead N (2n) x − boxRead N n x) ≤ φ x` on `[0, β)`.
DERIVED: `16`, `4`, `2` as in `finiteSize_eq_boxRead`; `1/1000` the sharp seed; `0` the lower coupling. -/
def ZoomSelfW (N n : ℕ) (β : ℝ) : Prop :=
  ∃ Φ φ : ℝ → ℝ, Φ 0 = 0 ∧ Φ β ≤ 1 / 1000 ∧ (∀ x ∈ Icc (0 : ℝ) β, HasDerivAt Φ (φ x) x) ∧
    ∀ x ∈ Ico (0 : ℝ) β, 16 * (n : ℝ) ^ 4 * (boxRead N (2 * n) x - boxRead N n x) ≤ φ x

/-- **The observer-side run seed, budget form.** There is `C > 0` such that, eventually in `β`, some power of
two `n ≥ 2` with `n · aRun N β ≤ C` has `ZoomSelfW N n β`. DERIVED: `2` the least side. -/
def ObsRunSeedW (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    (n : ℝ) * AsymptoticScaling.aRun N β ≤ C ∧ ZoomSelfW N n β

/-- **A budget bounds the defect by the sharp seed** (`EnergySeed.defectW_le_of_budget`).
DERIVED: `1/1000` the sharp seed; `0` the lower coupling. -/
theorem defectW_le_of_zoomSelfW (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (h : ZoomSelfW N n β) : defectW N β n ≤ 1 / 1000 := by
  obtain ⟨Φ, φ, h0, hΦβ, hd, hf⟩ := h
  have hb := defectW_le_of_budget hN (n := n) (a := 0) (b := β) (Φ := Φ) (φ := φ)
    (by rw [defectW_zero, h0]) hd (fun x hx => by rw [finiteSize_eq_boxRead hn]; exact hf x hx)
    β ⟨hβ, le_rfl⟩
  linarith

/-- **The defect is a budget**: `defectW N β n ≤ 1/1000` gives `ZoomSelfW N n β` with `Φ = defectW N · n`.
DERIVED: `1/1000` the sharp seed. -/
theorem zoomSelfW_of_defectW (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) {β : ℝ}
    (h : defectW N β n ≤ 1 / 1000) : ZoomSelfW N n β :=
  ⟨fun x => defectW N x n, fun x => finiteSize N n x, defectW_zero N n, h,
    fun x _ => hasDerivAt_defectW' hN n x, fun x _ => (finiteSize_eq_boxRead hn x).ge⟩

/-- **The budget form gives the run seed.** DERIVED: `0` the excluded colour count and the sign. -/
theorem runSeed_of_obsRunSeedW (hN : N ≠ 0) (h : ObsRunSeedW N) : WDeltaRun.RunSeed N := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β ⟨n, hp, h2, hna, hz⟩ hβ
  exact ⟨n, hp, h2, hna, defectW_le_of_zoomSelfW hN (by omega) hβ hz⟩

/-- **The run seed gives the budget form.** DERIVED: `0` the excluded colour count. -/
theorem obsRunSeedW_of_runSeed (hN : N ≠ 0) (h : WDeltaRun.RunSeed N) : ObsRunSeedW N := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with β ⟨n, hp, h2, hna, hd⟩
  exact ⟨n, hp, h2, hna, zoomSelfW_of_defectW hN (by omega) hd⟩

/-- **The budget form is the run seed.** DERIVED: `0` the excluded colour count. -/
theorem obsRunSeedW_iff (hN : N ≠ 0) : ObsRunSeedW N ↔ WDeltaRun.RunSeed N :=
  ⟨runSeed_of_obsRunSeedW hN, obsRunSeedW_of_runSeed hN⟩

/-! ## 3. The flat budget: a recorded no-go -/

/-- **The flat budget**: the doubling change of the box reading at most `1/(16000 n⁴ β)` on `[0, β)`.
DERIVED: `16000 = 16 · 1000`; `2` the doubling; `4` the dimension; `0` the lower coupling. -/
def ZoomSelfFlat (N n : ℕ) (β : ℝ) : Prop :=
  ∀ x ∈ Ico (0 : ℝ) β, boxRead N (2 * n) x - boxRead N n x ≤ 1 / (16000 * (n : ℝ) ^ 4 * β)

/-- The flat budget in `RunSeed`'s window. DERIVED: `2` the least side. -/
def ObsRunSeedFlat (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    (n : ℝ) * AsymptoticScaling.aRun N β ≤ C ∧ ZoomSelfFlat N n β

/-- **The flat budget bounds `finiteSize` by `1/(1000 β)`** on `[0, β)`.
DERIVED: `1000` the sharp seed; `16`, `4` as above. -/
theorem finiteSize_le_of_zoomSelfFlat {n : ℕ} (hn : n ≠ 0) {β : ℝ} (h : ZoomSelfFlat N n β) :
    ∀ x ∈ Ico (0 : ℝ) β, finiteSize N n x ≤ 1 / (1000 * β) := by
  intro x hx
  have hβ : 0 < β := lt_of_le_of_lt hx.1 hx.2
  have hn' : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) 4
  rw [finiteSize_eq_boxRead hn]
  have h1 := mul_le_mul_of_nonneg_left (h x hx) (by positivity : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 4)
  have e : 16 * (n : ℝ) ^ 4 * (1 / (16000 * (n : ℝ) ^ 4 * β)) = 1 / (1000 * β) := by
    field_simp
    ring
  linarith

/-- **No-go for the flat budget.** If for every `C > 0` some `c₀ > 0` has, eventually in `β`, at every
power-of-two side `n ≥ 2` with `n · aRun N β ≤ C`, a coupling `x ∈ [0, β)` with `c₀ ≤ finiteSize N n x`, then
`ObsRunSeedFlat N` fails. DERIVED: `1000` the sharp seed; `2` the least side; `0` the sign. -/
theorem not_obsRunSeedFlat
    (hfs : ∀ C : ℝ, 0 < C → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n →
      2 ≤ n → (n : ℝ) * AsymptoticScaling.aRun N β ≤ C → ∃ x ∈ Ico (0 : ℝ) β, c₀ ≤ finiteSize N n x) :
    ¬ ObsRunSeedFlat N := by
  rintro ⟨C, hC, hev⟩
  obtain ⟨c₀, hc₀, H⟩ := hfs C hC
  obtain ⟨β, ⟨n, hp, h2, hna, hz⟩, hH, hβ⟩ :=
    (hev.and (H.and (eventually_gt_atTop (1 / (1000 * c₀))))).exists
  obtain ⟨x, hx, hc⟩ := hH n hp h2 hna
  have hle := finiteSize_le_of_zoomSelfFlat (by omega) hz x hx
  have hβ0 : 0 < β := lt_of_le_of_lt hx.1 hx.2
  have h1 : 1 < 1000 * c₀ * β := by
    rw [div_lt_iff₀ (by positivity)] at hβ
    linarith
  have h2' : 1 / (1000 * β) < c₀ := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-! ## 4. Gauge covariance of the flow under central height twists -/

section Centre

open MassGap.InfiniteLattice MassGap.GaugeInvariantAlgebra

/-- **The height twist**: every link along `ν` at `x` multiplied by `z^{h(x_ν + 1) − h(x_ν)}`, every other
link unchanged. DERIVED: `4` the dimension; `1` the unit step of a link. -/
def heightTwist {G : Type} [Group G] (ν : Fin 4) (z : G) (h : ℤ → ℤ) (U : IConf G) : IConf G :=
  fun l => if l.1 = ν then z ^ (h (l.2 ν + 1) - h (l.2 ν)) * U l else U l

variable {G : Type} [Group G]

/-- **A central height twist is a local gauge transformation**: `heightTwist ν z h = igaugeTransform
(x ↦ (z^{h(x_ν)})⁻¹)`. DERIVED: `4` the dimension; `1` the unit step. -/
theorem heightTwist_eq_igaugeTransform (ν : Fin 4) {z : G} (hz : z ∈ Subgroup.center G)
    (h : ℤ → ℤ) (U : IConf G) :
    heightTwist ν z h U = igaugeTransform (fun x => (z ^ h (x ν))⁻¹) U := by
  have hc : ∀ (k : ℤ) (g : G), g * z ^ k = z ^ k * g := fun k g =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hz k) g
  funext l
  obtain ⟨μ, x⟩ := l
  show (if μ = ν then z ^ (h (x ν + 1) - h (x ν)) * U (μ, x) else U (μ, x))
    = (z ^ h (x ν))⁻¹ * U (μ, x) * (z ^ h (ishift μ x ν))⁻¹⁻¹
  rw [inv_inv]
  by_cases hμ : μ = ν
  · have hs : ishift μ x ν = x ν + 1 := by
      rw [hμ]
      show Function.update x ν (x ν + 1) ν = x ν + 1
      exact Function.update_self ν (x ν + 1) x
    rw [if_pos hμ, hs, ← zpow_neg, mul_assoc, hc, ← mul_assoc, ← zpow_add, neg_add_eq_sub]
  · have hs : ishift μ x ν = x ν := by
      show Function.update x μ (x μ + 1) ν = x ν
      exact Function.update_of_ne (Ne.symm hμ) (x μ + 1) x
    rw [if_neg hμ, hs, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

end Centre

section CentreSU

open MassGap.InfiniteLattice MassGap.GaugeInvariantAlgebra MassGap.ContinuumFlow

/-- **Every flow commutes with every central height twist** (gauge covariance of the flow on `ℤ⁴`).
DERIVED: `4` the dimension. -/
theorem flow_heightTwist (W : ConfFlow N) (k : ℕ) (ν : Fin 4) {z : MassGap.SUN.SU N}
    (hz : z ∈ Subgroup.center (MassGap.SUN.SU N)) (h : ℤ → ℤ) (U : IConf (MassGap.SUN.SU N)) :
    W.V k (heightTwist ν z h U) = heightTwist ν z h (W.V k U) := by
  rw [heightTwist_eq_igaugeTransform ν hz h U, heightTwist_eq_igaugeTransform ν hz h (W.V k U)]
  exact W.gauge k _ U

/-- **Every flowed reading is unchanged by every central height twist** (gauge invariance of
`W.fieldMap k O` on `ℤ⁴`). DERIVED: `4` the dimension. -/
theorem fieldMap_heightTwist (W : ConfFlow N) (k : ℕ) (O : ContinuumField.LField (MassGap.SUN.SU N))
    (ν : Fin 4) {z : MassGap.SUN.SU N} (hz : z ∈ Subgroup.center (MassGap.SUN.SU N)) (h : ℤ → ℤ)
    (U : IConf (MassGap.SUN.SU N)) :
    (W.fieldMap k O).1 (heightTwist ν z h U) = (W.fieldMap k O).1 U := by
  rw [heightTwist_eq_igaugeTransform ν hz h U]
  exact (W.fieldMap k O).2.2 _ U

end CentreSU

/-! ## 5. The capstone -/

section Capstone

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
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
  MassGap.ClayRunSeed MassGap.InputMerge

/-- **The per-`N` inputs with the budget-form seed**: `InputMerge.NarrowInputsAtMin` with `RunSeed N`
replaced by `ObsRunSeedW N`. DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
def NarrowInputsObs (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreMin W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandR Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ FlowCovLim Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ ProxyNondeg Wf cf
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ ObsRunSeedW N

/-- **`NarrowInputsObs` gives `NarrowInputsAtMin`** at the same `W`, `r` (`runSeed_of_obsRunSeedW`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsAtMin_of_obs {N : ℕ} (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsObs N hN2 W r) : NarrowInputsAtMin N hN2 W r := by
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hOS⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3,
    runSeed_of_obsRunSeedW (by omega) hOS⟩

/-- **`NarrowInputsAtMin` gives `NarrowInputsObs`** at the same `W`, `r` (`obsRunSeedW_of_runSeed`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsObs_of_atMin {N : ℕ} (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtMin N hN2 W r) : NarrowInputsObs N hN2 W r := by
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hRS⟩ := h
  exact ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3,
    obsRunSeedW_of_runSeed (by omega) hRS⟩

/-- **`ClayStatementDy` from the budget-form seed**: `NarrowInputsObs` at some observer and margin, at
every `N ≥ 2` (`InputMerge.clayStatement_of_narrowAtMin`). DERIVED: `2` the least colour count. -/
theorem clayStatement_of_obsRunSeed
    (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), ∃ (W : ConfFlow N) (r : ℝ), NarrowInputsObs N hN2 W r) :
    MassGap.ClayStatementDy :=
  clayStatement_of_narrowAtMin fun N hN2 => by
    obtain ⟨W, r, hA⟩ := h N hN2
    exact ⟨W, r, narrowInputsAtMin_of_obs hN2 hA⟩

end Capstone

end MassGap.ObserverRunSeed

end

#print axioms MassGap.ObserverRunSeed.finiteSize_eq_boxRead
#print axioms MassGap.ObserverRunSeed.defectW_le_of_zoomSelfW
#print axioms MassGap.ObserverRunSeed.zoomSelfW_of_defectW
#print axioms MassGap.ObserverRunSeed.runSeed_of_obsRunSeedW
#print axioms MassGap.ObserverRunSeed.obsRunSeedW_of_runSeed
#print axioms MassGap.ObserverRunSeed.obsRunSeedW_iff
#print axioms MassGap.ObserverRunSeed.finiteSize_le_of_zoomSelfFlat
#print axioms MassGap.ObserverRunSeed.not_obsRunSeedFlat
#print axioms MassGap.ObserverRunSeed.heightTwist_eq_igaugeTransform
#print axioms MassGap.ObserverRunSeed.flow_heightTwist
#print axioms MassGap.ObserverRunSeed.fieldMap_heightTwist
#print axioms MassGap.ObserverRunSeed.narrowInputsAtMin_of_obs
#print axioms MassGap.ObserverRunSeed.narrowInputsObs_of_atMin
#print axioms MassGap.ObserverRunSeed.clayStatement_of_obsRunSeed
