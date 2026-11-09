import Mathlib
import MassGap.ZoomBase

/-!
# MassGap.CoefPin — the coefficient clause is not read by the expansion

`ZoomBase.CoreInputsAlongWZB` carries one clause on the coefficients alone, `MultiScaleOS.CoefBound cf`, next
to `ExpandMatch Wf cf z μ` on the same existential `cf`. This module proves that `ExpandMatch` cannot give
`CoefBound`: the expansion reads `cf` only through the flowed proxies `msProx Wf cf`, and the map from
coefficients to proxies has a kernel at every flow. Declarations are in the namespace `MassGap.CoefPin`.

## 1. The kernel of the proxy map (proved, every flow)

* `qDeg x = ((0, 0), x)`: the plaquette with both directions equal. Its boundary word is
  `U_l U_{l'} U_{l'}⁻¹ U_l⁻¹`, so `ihol_qDeg`: its holonomy is `1` at every configuration, and
  `symPlaq_qDeg_apply`: the symmetrised density `sym (plaqField (qDeg x))` is `0` at every configuration
  (`wilsonDensity 1 = 0`, each of the hypercubic images is again a degenerate plaquette).
* **`msFlow_qDeg`**: `msFlow Wf k s (inr (qDeg x)) = 0` at every flow `Wf`, step `k`, scale `s` and site `x`.
  The index set `MIx = Ix0 ⊕ IPlaq` contains these indices; no clause of the scale bundle removes them.

## 2. Two coefficient families with the same proxies

* `jDeg n = inr (qDeg (n, n, n, n))`, `cfSpread cf i s = cf i s + (1 − cf_{i, jDeg ⌊1/s⌋}(s)) e_{jDeg ⌊1/s⌋}`:
  `cf` with the coefficient on one degenerate plaquette set to `1`, the plaquette moving with the scale.
* **`msProx_spread`**: `msProx Wf (cfSpread cf) = msProx Wf cf`; `msLat_spread`, `proxB_spread`: the flowed
  readings and the proxy products agree.
* **`expandMatch_spread_iff`**: `ExpandMatch Wf (cfSpread cf) z μ ↔ ExpandMatch Wf cf z μ`, at every `Wf`, `z`,
  `μ`.
* **`not_coefBound_spread`**: `¬ CoefBound (cfSpread cf)` for every `cf`: the support at `s = 1/(n + 1)`
  contains `jDeg (n + 1)`, so no finite `S i` contains the supports on `(0, 1]`.

## 3. The obstruction

* **`expandMatch_not_coefBound`**: if `ExpandMatch Wf cf z μ`, then `cfSpread cf` meets `ExpandMatch` and
  fails `CoefBound`.
* **`coefBound_of_expandMatch_iff_empty`**: `ExpandMatch Wf · z μ → CoefBound ·` holds at a flow exactly when
  no coefficient family meets `ExpandMatch` there. So option (a), `CoefBound` from `ExpandMatch`, is
  impossible at every flow where the expansion holds; the implication is vacuous elsewhere.
* Both are copied over the coupling family (`#along_generalize_more`, 8 copies), so they hold at every
  coupling family `B`, in particular at the bundle's `cpl βs`, for the copy of `ExpandMatch` the bundle
  carries.
* Test at the unit: `cfLead` meets `CoefBound` (`FlowChoice.coefBound_cfLead`) and `cfSpread cfLead` has the
  same proxies (`msProx_spread`) and fails it (`not_coefBound_spread`).

The obstruction names its escape. `CoefBound` reads the coefficients; every clause of the bundle that reads
`cf` reads it through the proxies (by the definitions `msLat`, `proxB`, `msProx`). A clause implied by the
expansion must be invariant under the kernel of the proxy map, so it must be a statement about
`msProx Wf cf`, not about `cf`. The kernel is larger than §1 (the hypercubic orbit of a plaquette under
`sym` gives equal fields), so the same obstruction holds for any clause that pins the support or the size
of individual coefficients, `ProxyCov.CfParity` included (argued: `cfSpread` changes the support only).

`ProxyCov.CfParity` is not a field of `CoreInputsAlongWZB` (nor of `FreeBridge.CoreInputsAlongWFB`, which
extends `ExpandMatch.CoreInputsAlongWAM`, not `RoutePin.CoreInputsAlongWAMP`). The bundle has one clause
on `cf` alone, `CoefBound cf`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the repeated direction of the degenerate plaquette, the zero field and its
reading; `1` the unit coefficient, the step `n + 1` that keeps the scale in `(0, 1]` and the top of that
range.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CoefPin

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
  MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN MassGap.ScalePC MassGap.ScalePM MassGap.ClusterRoute MassGap.ObserverTowerCL
  MassGap.ExpandMatch

variable {N : ℕ}

/-! ## 1. The kernel of the proxy map -/

/-- **The degenerate plaquette** at `x`: both directions `0`. DERIVED: `0` the repeated direction. -/
def qDeg (x : MassGap.GibbsSpec.ISite) : MassGap.GibbsSpec.IPlaq := ((0, 0), x)

/-- The holonomy of a degenerate plaquette is `1`. DERIVED: `1` the identity. -/
theorem ihol_qDeg (x : MassGap.GibbsSpec.ISite) (U : Cfg N) :
    MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) (qDeg x) U = 1 := by
  unfold MassGap.GibbsSpec.ihol MassGap.WilsonLattice.wilsonHol MassGap.GibbsSpec.ibd qDeg
  simp

/-- The symmetrised density of a degenerate plaquette is `0`. DERIVED: `0` the zero field. -/
theorem symPlaq_qDeg_apply [NeZero N] (x : MassGap.GibbsSpec.ISite) (U : Cfg N) :
    (MassGap.ObserverSymField.sym (plaqField (N := N) (qDeg x))).1 U = 0 := by
  rw [MassGap.ObserverSymField.sym_apply]
  refine Finset.sum_eq_zero fun g _ => ?_
  show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol (qDeg x) _) = 0
  rw [ihol_qDeg, MassGap.WilsonAction.wilsonDensity_one (NeZero.ne N)]

/-- **The flowed degenerate plaquette is `0`**, at every flow, step and scale. DERIVED: `0` the zero
field and its reading. -/
theorem msFlow_qDeg [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (x : MassGap.GibbsSpec.ISite) :
    msFlow Wf k s (Sum.inr (qDeg x)) = 0 := by
  have h0 : ((Wf s).fieldMap k (mField (Sum.inr (qDeg x)))).1 = 0 := by
    ext U
    exact symPlaq_qDeg_apply x _
  unfold msFlow
  rw [h0, MassGap.DLRLimit.State.map_zero, zero_smul, sub_zero, smul_zero]

/-! ## 2. Two coefficient families with the same proxies -/

/-- The degenerate plaquette at the diagonal site `(n, n, n, n)`. DERIVED: no numeral. -/
def jDeg (n : ℕ) : MIx := Sum.inr (qDeg fun _ => (n : ℤ))

theorem jDeg_injective : Function.Injective jDeg := by
  intro a b h
  have h' := congrArg (fun j : MIx => Sum.elim (fun _ => (0 : ℤ)) (fun q => q.2 0) j) h
  simpa [jDeg, qDeg] using h'

theorem msFlow_jDeg [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (n : ℕ) :
    msFlow Wf k s (jDeg n) = 0 :=
  msFlow_qDeg Wf k s _

/-- **The spread coefficients**: `cf` with the coefficient on `jDeg ⌊1/s⌋` set to `1`. DERIVED: `1` the
unit coefficient. -/
def cfSpread (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Ix0 → ℝ → (MIx →₀ ℝ) := fun i s =>
  cf i s + Finsupp.single (jDeg ⌊s⁻¹⌋₊) (1 - cf i s (jDeg ⌊s⁻¹⌋₊))

/-- **The spread coefficients have the same proxies.** DERIVED: `0` the zero field. -/
theorem msProx_spread [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) :
    msProx Wf (cfSpread cf) = msProx Wf cf := by
  funext k s i
  show (cfSpread cf i s).sum (fun j a => a • msFlow Wf k s j)
    = (cf i s).sum (fun j a => a • msFlow Wf k s j)
  unfold cfSpread
  rw [Finsupp.sum_add_index' (h := fun j a => a • msFlow Wf k s j) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_single_index (h := fun j a => a • msFlow Wf k s j) (zero_smul _ _), msFlow_jDeg,
    smul_zero, add_zero]

theorem msLat_spread [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    {ι : Type} [Fintype ι] (F : ι → CDatum (CbR N ScaleControlFull.zOne)) :
    msLat Wf (cfSpread cf) k s F = msLat Wf cf k s F := by
  unfold msLat
  rw [msProx_spread]

theorem proxB_spread [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) :
    proxB Wf (cfSpread cf) = proxB Wf cf := by
  funext k s P
  unfold proxB
  rw [msProx_spread]

/-- **The expansion cannot tell the spread coefficients from `cf`.** DERIVED: no numeral. -/
theorem expandMatch_spread_iff [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (z : Chan → ℕ → ℝ) (μ : OffMix) :
    ExpandMatch Wf (cfSpread cf) z μ ↔ ExpandMatch Wf cf z μ := by
  unfold ExpandMatch ExpandFam.ExpandRF RPGerm
  simp only [msLat_spread, proxB_spread]

/-- **The spread coefficients fail `CoefBound`**, at every `cf`. DERIVED: `1` the step `n + 1` and the
top of the scale range; `0` the sign. -/
theorem not_coefBound_spread (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : ¬ CoefBound (cfSpread cf) := by
  rintro ⟨S, K, γ, h⟩
  let i : Ix0 := eI fun _ => 0
  have hmem : ∀ n : ℕ, jDeg (n + 1) ∈ S i := by
    intro n
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
    have hfl : ⌊((n : ℝ) + 1)⁻¹⁻¹⌋₊ = n + 1 := by
      rw [inv_inv, hcast, Nat.floor_natCast]
    apply (h i _ hpos hle).1
    rw [Finsupp.mem_support_iff]
    simp only [cfSpread, hfl, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_sub_cancel]
    exact one_ne_zero
  have hinj : Function.Injective fun n : ℕ => jDeg (n + 1) :=
    fun a b hab => Nat.succ_injective (jDeg_injective hab)
  exact Set.infinite_range_of_injective hinj
    ((S i).finite_toSet.subset (by rintro _ ⟨n, rfl⟩; exact hmem n))

/-! ## 3. The obstruction -/

/-- **`ExpandMatch` does not give `CoefBound`**: every coefficient family meeting the expansion has a
companion meeting it and failing the bound. DERIVED: no numeral. -/
theorem expandMatch_not_coefBound [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandMatch Wf cf z μ) :
    ExpandMatch Wf (cfSpread cf) z μ ∧ ¬ CoefBound (cfSpread cf) :=
  ⟨(expandMatch_spread_iff Wf cf z μ).2 hE, not_coefBound_spread cf⟩

/-- **The implication holds only where the expansion is empty.** DERIVED: no numeral. -/
theorem coefBound_of_expandMatch_iff_empty [NeZero N] (Wf : ℝ → ConfFlow N) (z : Chan → ℕ → ℝ)
    (μ : OffMix) :
    (∀ cf, ExpandMatch Wf cf z μ → CoefBound cf) ↔ ∀ cf, ¬ ExpandMatch Wf cf z μ := by
  refine ⟨fun h cf hE => (expandMatch_not_coefBound hE).2 (h _ (expandMatch_not_coefBound hE).1),
    fun h cf hE => absurd hE (h cf)⟩

/-- **At the unit**: `cfLead` meets `CoefBound`, its spread has the same proxies and fails it.
DERIVED: no numeral. -/
theorem cfLead_spread_test [NeZero N] (Wf : ℝ → ConfFlow N) :
    CoefBound cfLead ∧ msProx Wf (cfSpread cfLead) = msProx Wf cfLead ∧ ¬ CoefBound (cfSpread cfLead) :=
  ⟨coefBound_cfLead, msProx_spread Wf cfLead, not_coefBound_spread cfLead⟩

end MassGap.CoefPin

end

/-! ### The copy over a coupling family -/

namespace MassGap.CoefPin

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.CoefPin.expandMatch_not_coefBound
  MassGap.CoefPin.coefBound_of_expandMatch_iff_empty

end MassGap.CoefPin

#print axioms MassGap.CoefPin.ihol_qDeg
#print axioms MassGap.CoefPin.symPlaq_qDeg_apply
#print axioms MassGap.CoefPin.msFlow_qDeg
#print axioms MassGap.CoefPin.jDeg_injective
#print axioms MassGap.CoefPin.msProx_spread
#print axioms MassGap.CoefPin.expandMatch_spread_iff
#print axioms MassGap.CoefPin.not_coefBound_spread
#print axioms MassGap.CoefPin.expandMatch_not_coefBound
#print axioms MassGap.CoefPin.coefBound_of_expandMatch_iff_empty
#print axioms MassGap.CoefPin.cfLead_spread_test
#print axioms MassGap.CouplingGen.Along.CoefPin.expandMatch_not_coefBound
#print axioms MassGap.CouplingGen.Along.CoefPin.coefBound_of_expandMatch_iff_empty
