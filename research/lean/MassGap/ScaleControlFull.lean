import Mathlib
import MassGap.ScaleControlRun
import MassGap.InputsTriage
import MassGap.ClaySUFinal
import MassGap.ObserverCarries
import MassGap.PlaquetteFloor
import MassGap.ZCanon

/-!
# MassGap.ScaleControlFull — the `SU(2)` inputs folded into one record at one flow

The `SU(2)` route through `MixConvRP.clayStatementAt_SU_reflAvg'` takes the gap from `hrun : ScaleControlRun`
and the existence inputs `hU`, `hphys`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hObs`, `hWard`, `hCO`,
`hA` at one configuration flow `W : ConfFlow 2`. This module classifies each existence input against
the fields of `ScaleControlRun`, folds them into one record `ScaleControlFullAt W r z`. No
`ClayStatementAt` capstone is stated from the record: its `run` field is `ScaleControlRun`, and
`InputAudit.not_scaleControlRun` refutes `ScaleControlRun` under the argued growth of the zero-flux level count.

The record is a repackaging, not a reduction: `run` is `hrun`; `phys`, `kern`, `ward` and `approx` are the
existence inputs unchanged; `comp` is `hCO` up to `convC_iff_boundC`; `low` is weaker than `hObs`; and `uv`
replaces `hU` by a sufficient condition. The record holds every open input of the `SU(2)` route.

## 1. The run alone gives neither the moments nor the capstone uniformly in the flow (proved: two no-go theorems)

`ScaleControlRun` does not mention a configuration flow: its fields are the zero-flux and odd-flux
levels of the slice kernels `trivKN`, `halfKN`, and the block contraction of observables `X` of the
infinite-volume `periodicState`, `X` unconstrained. `hU` and the capstone itself each fail at some
flow, so no derivation of either from the run can be uniform in `W`. The theorems do not exclude a
derivation `ScaleControlRun → hU` at one particular `W`, or one that also uses properties of that `W`; that
case is the argued paragraph below.

* `not_run_of_forall_classMoments`: if `ScaleControlRun` gave `ClassMoments … W (SymPlaqClass 2) t C`
  at some `t, C` for every `W`, then `ScaleControlRun` would be false
  (`PlaquetteFloor.not_classMoments_identity` at `ConfFlow.identity 2`).
* `not_run_of_forall_clay`: if `ScaleControlRun` gave `ClayStatementAt (le_refl 2) W (SymPlaqClass 2) _`
  for every `W`, then `ScaleControlRun` would be false
  (`ObserverCarries.not_clayStatementAt_flatFlow_symPlaq`).

So any master input from which the capstone follows uniformly in `W` has a field that reads `W`.

Why the block contraction does not give the moments `hU` at a given `W` either (argued, not a
declaration): `stateK k` is `periodicState` at `dyBeta k`, the state the block contraction speaks of,
so the objects meet. But `KernelNear Δ X δ` says `|wspec Δ X ω − c| ≤ δ` with `c` free: it bounds how
much the conditional expectation depends on the outside, and gives covariances
(`BoxFocusTest.cov_le_of_kernelNear`: `|Cov(X, Y)| ≤ 2 M δ`). It is unchanged when a constant is added
to `X`, while `ClassMoments` asks the size of `ν_k(E_R^{2p})`, which needs the mean of the flowed
density to be `O(a_k⁴)` (`FlowMoments.classMoments_mean_le`). Its constant `δ = B αᵐ V D` scales
with the Lipschitz bound `V` of the observable; for `e^{s a_k⁻⁴ O∘V_k}`, the observable of the one-site
moment, `V` grows like `a_k⁻⁴ e^{s a_k⁻⁴ M}`. A clustering bound on covariances is a statement about
dependence, not about size, and it does not reach the OS0 bounds of `hCO` (which are size bounds on
`n`-point functions) or the moments of `hU`. The same holds for every other existence input: they read
`energy0 W` (`hphys`), the composites `CbR 2 z`, the trace channel `rhoD (fR 2) z` or the observer kernels `mixKR`, `gramF` of
`W`, none of which appears in `ScaleControlRun`.

## 2. The table

| input | status | field of `ScaleControlFullAt` |
|---|---|---|
| `hfar` | derived | from `run` (`runSeed_two_of_scaleControlRun`) |
| `hU` | new field, sufficient for the input (converse not in the tree) | `uv`: `∃ t > 0, ∃ C, FlowUV.SiteExp … W (SymPlaqClass 2) (625 t) C` |
| `hphys` | the input (a property of the chosen `W`) | `phys` at the record's `r` |
| `z`, `hz`, `hzS`, `hzP` | choice; discharged at `ZCanon.zFix` | `hz`, `hzS`, `hzP` (`fullAt_zOne` discharges them) |
| `G`, `hK`, `hAF` | the input, `G` absorbed | `kern`: `∃ G, TwoPointKernel … G ∧ AFCoefficient 2 G` |
| `hObs` | weakened to the target clause | `low`: `InputsTriage.ObsLower` |
| `hWard` | the input | `ward` |
| `hCO` | the input, `ConvC` weakened to a bound | `comp`: `BoundC ∧ OS0C ∧ OS1C ∧ CovC ∧ CompNondeg` |
| `hA` | the input | `approx` at the record's `r` |

* `uv` is `FlowUV.SiteExp` at `s = (2·1 + 3)⁴ t`: one exponential moment of each flowed field of the
  class in physical units, uniform over the class, eventually in the step. It gives `hU`
  (`ClaySUFinal.classMoments_of_siteExp`); it is not `ClassMoments`; it is a statement on `stateK` of
  `e^{s a_k⁻⁴ O∘V_k}` alone. The Bałaban-type small-field/large-field split gives it
  (`uv_of_split`, through `ExistenceFlow.siteExp_of_split`), and so does a summable zoom stability
  (`uv_of_zoomStable`, through `ExistenceFlow.siteExp_of_zoomStable`). Physics, open.
* `low`: by `InputsTriage.nonGaussianT_rhoD_iff_lower`, given `comp`, `ObsLower` is the target clause
  `NonGaussianT` itself; `ObsThreePoint` gives it (`InputsTriage.obsLower_of_obsThreePoint`).
* `comp`: `BoundC` is equivalent to `ConvC` (`InputsTriage.convC_iff_boundC`).
* `hphys`, `kern`, `ward`, `approx`: no reduction of these to statements on other objects is in the
  tree. For `approx`, `ApproxObserver.exists_jointRPK_not_approxK` shows that positivity alone does not
  give it.

## 3. The record (proved)

* `ScaleControlFullAt W r z`: `run`, `uv`, `phys`, `hz`, `hzS`, `hzP`, `kern`, `low`, `ward`, `comp`,
  `approx`.
* `ScaleControlFull W`: `∃ r z, ScaleControlFullAt W r z`.
* `fullAt_zOne`: at `z = zOne = ZCanon.zFix 2 1 1` the fields `hz`, `hzS`, `hzP` are discharged.
* `fullAt_of_inputs`: `ScaleControlRun` and the existence inputs, with `uv` for `hU`, build
  the record; so the record asks no more than those inputs, except `uv` in place of `hU`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the least colour count and the limits of the scalar and
pseudoscalar factors; `2 · 1 + 3` and `4` the site count `625` of `classMoments_of_siteExp`; `1` the
free traceless-Ricci and Weyl factors of `zOne`; `0` the reflection plane and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScaleControlFull

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

/-! ## 1. No existence input follows from the run uniformly in the flow -/

/-- **A run giving the moments at every flow is false**: the moments fail at the identity flow
(`PlaquetteFloor.not_classMoments_identity`). It does not exclude a derivation at one fixed `W`. -/
theorem not_run_of_forall_classMoments
    (h : ∀ W : ConfFlow 2, ScaleControlRun →
      ∃ t C : ℝ, ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C) :
    ¬ ScaleControlRun := fun hr => by
  obtain ⟨t, C, hC⟩ := h (ConfFlow.identity 2) hr
  exact PlaquetteFloor.not_classMoments_identity (le_refl 2) (ne_zero_of_two_le (le_refl 2)) t C hC

/-- **A run giving the capstone at every flow is false**: the target fails at the flat flow
(`ObserverCarries.not_clayStatementAt_flatFlow_symPlaq`). It does not exclude a derivation at one fixed
`W`. -/
theorem not_run_of_forall_clay
    (h : ∀ W : ConfFlow 2, ScaleControlRun →
      ClayStatementAt (le_refl 2) W (SymPlaqClass 2) (symPlaq_refl 2)) :
    ¬ ScaleControlRun := fun hr =>
  ObserverCarries.not_clayStatementAt_flatFlow_symPlaq (le_refl 2) (h _ hr)

/-! ## 2. The master record -/

/-- **The master input at one flow `W`, one margin `r` and one channel factor `z`** (`SU(2)`).
Classification of each field: module docstring, §2. -/
structure ScaleControlFullAt (W : ConfFlow 2) (r : ℝ) (z : Chan → ℕ → ℝ) : Prop where
  /-- The gap half: odd-flux levels and zero-flux scale control (`ScaleControlRun`). -/
  run : ScaleControlRun
  /-- Physics, open: one exponential moment per site in physical units, uniform over the class. -/
  uv : ∃ t C : ℝ, 0 < t ∧
    FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C
  /-- A property of the chosen flow: physical range `r`. -/
  phys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r
  /-- Conditions on the channel factors alone. -/
  hz : ∀ c k, z c k ≠ 0
  hzS : Tendsto (fun k => z .sc k * dySpacing 2 k ^ 4) atTop (𝓝 2)
  hzP : Tendsto (fun k => z .ps k * dySpacing 2 k ^ 4) atTop (𝓝 2)
  /-- Open: a two-point kernel of the trace with the asymptotic-freedom coefficient. -/
  kern : ∃ G : ℝ → ℝ, TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) z) G
    ∧ AFCoefficient 2 G
  /-- Open: the lower half of the observer's three-point reading, along `ultra`. -/
  low : InputsTriage.ObsLower (ne_zero_of_two_le (le_refl 2)) z
  /-- Open: the translation Ward identity. -/
  ward : WardT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) z)
  /-- Open: the analytic clauses of the averaged composites, with the limit clause as a bound. -/
  comp : InputsTriage.BoundC (ne_zero_of_two_le (le_refl 2)) (CbR 2 z)
    ∧ OS0C (ne_zero_of_two_le (le_refl 2)) (CbR 2 z) ∧ OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 z)
    ∧ CovC (ne_zero_of_two_le (le_refl 2)) (CbR 2 z)
    ∧ CompNondeg (ne_zero_of_two_le (le_refl 2)) (CbR 2 z)
  /-- Open: the composites are approximated by the observer's margin monomials. -/
  approx : ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 z) 0) (mixKR (le_refl 2) W z r)
    (gramF (le_refl 2) W r)

/-- **The master input at one flow**: some margin `r` and channel factor `z` with the record. -/
def _root_.MassGap.ScaleControlFull (W : ConfFlow 2) : Prop :=
  ∃ (r : ℝ) (z : Chan → ℕ → ℝ), ScaleControlFull.ScaleControlFullAt W r z

/-! ## 3. Constructors -/

/-- **The canonical channel factor**: `ZCanon.zFix 2 1 1` (`2/a_k⁴` on `sc`, `ps`; `1` on `ri`, `we`). -/
def zOne : Chan → ℕ → ℝ := ZCanon.zFix 2 (fun _ => 1) (fun _ => 1)

/-- **At `zOne` the channel-factor fields are discharged.** -/
theorem fullAt_zOne {W : ConfFlow 2} {r : ℝ} (hrun : ScaleControlRun)
    (huv : ∃ t C : ℝ, 0 < t ∧
      FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hkern : ∃ G : ℝ → ℝ, TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) G
      ∧ AFCoefficient 2 G)
    (hlow : InputsTriage.ObsLower (ne_zero_of_two_le (le_refl 2)) zOne)
    (hward : WardT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne))
    (hcomp : InputsTriage.BoundC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ OS0C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ CovC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ CompNondeg (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (happrox : ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) 0)
      (mixKR (le_refl 2) W zOne r) (gramF (le_refl 2) W r)) :
    ScaleControlFullAt W r zOne where
  run := hrun
  uv := huv
  phys := hphys
  hz := ZCanon.zFix_ne (by norm_num) (fun _ => one_ne_zero) (fun _ => one_ne_zero)
  hzS := ZCanon.tendsto_zFix_sc (by norm_num) _ _
  hzP := ZCanon.tendsto_zFix_ps (by norm_num) _ _
  kern := hkern
  low := hlow
  ward := hward
  comp := hcomp
  approx := happrox

/-- **`ScaleControlRun` and the existence inputs build the record**, with `uv` in place of `hU`: `ObsThreePoint` gives `low`
(`InputsTriage.obsLower_of_obsThreePoint`), `CompOS` gives `comp` (`InputsTriage.convC_iff_boundC`). -/
theorem fullAt_of_inputs {W : ConfFlow 2} {r : ℝ} {z : Chan → ℕ → ℝ} (hrun : ScaleControlRun)
    (huv : ∃ t C : ℝ, 0 < t ∧
      FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing 2 k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing 2 k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) z) G)
    (hAF : AFCoefficient 2 G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le (le_refl 2)) z)
    (hWard : WardT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) z))
    (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) (CbR 2 z))
    (hA : ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 z) 0) (mixKR (le_refl 2) W z r)
      (gramF (le_refl 2) W r)) :
    ScaleControlFullAt W r z where
  run := hrun
  uv := huv
  phys := hphys
  hz := hz
  hzS := hzS
  hzP := hzP
  kern := ⟨G, hK, hAF⟩
  low := InputsTriage.obsLower_of_obsThreePoint _ z hObs
  ward := hWard
  comp := ⟨(InputsTriage.convC_iff_boundC _ _).1 hCO.1, hCO.2⟩
  approx := hA

/-- **`uv` from the small-field/large-field split** (`ExistenceFlow.siteExp_of_split`), on a class
bounded by `M`. -/
theorem uv_of_split {W : ConfFlow 2} {t M C₁ C₂ : ℝ} (ht : 0 < t)
    (hM : ∀ O ∈ SymPlaqClass 2, ∀ U, O.1 U ≤ M)
    (h : ExistenceFlow.SmallLargeSplit (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2)
      (t * (2 * 1 + 3) ^ 4) M C₁ C₂) :
    ∃ t C : ℝ, 0 < t ∧
      FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C :=
  ⟨t, C₁ + C₂, ht,
    ExistenceFlow.siteExp_of_split _ W (mul_pos ht (by norm_num)).le hM h⟩

/-- **`uv` from a summable zoom stability** (`ExistenceFlow.siteExp_of_zoomStable`). -/
theorem uv_of_zoomStable {W : ConfFlow 2} {t : ℝ} (ht : 0 < t) {ε : ℕ → ℝ} {K : ℕ}
    (hε : ∀ k, 0 ≤ ε k) (hsum : Summable ε)
    (h : ExistenceFlow.ZoomStable (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2)
      (t * (2 * 1 + 3) ^ 4) ε K) {X₀ : ℝ}
    (h0 : ∀ O ∈ SymPlaqClass 2,
      ExistenceFlow.physExp (ne_zero_of_two_le (le_refl 2)) W O (t * (2 * 1 + 3) ^ 4) K ≤ X₀) :
    ∃ t C : ℝ, 0 < t ∧
      FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C :=
  ⟨t, _, ht, ExistenceFlow.siteExp_of_zoomStable _ W hε hsum h h0⟩

end MassGap.ScaleControlFull

end

#print axioms MassGap.ScaleControlFull.not_run_of_forall_classMoments
#print axioms MassGap.ScaleControlFull.not_run_of_forall_clay
#print axioms MassGap.ScaleControlFull.fullAt_zOne
#print axioms MassGap.ScaleControlFull.fullAt_of_inputs
#print axioms MassGap.ScaleControlFull.uv_of_split
#print axioms MassGap.ScaleControlFull.uv_of_zoomStable
