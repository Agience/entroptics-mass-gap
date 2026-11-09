import Mathlib
import MassGap.CovFromFlow
import MassGap.FlowZero

/-!
# MassGap.ObserverChoice — one fixed `SU(2)` observer, with `PhysRange` discharged

`ClayStatement` asks, at each `N ≥ 2`, for some observer `W`, some class `D` and a proof of
`ClayStatementAt hN2 W D hD`; the observer is the prover's choice. This module fixes it at `N = 2` and
proves its `PhysRange r` clause. Declarations are
in the namespace `MassGap.ObserverChoice`.

## 1. The observer

`obsW = FlowZero.apeFam (1/12) 1`, that is `ObserverFlow.obsConfFlow (1/12) n R` with
`n k = ⌊(1/a_k)²⌋₊` localised APE steps in midpoint boxes of half-width `R k = ⌊1/a_k⌋₊`: the APE observer
at physical smearing scale `1`, with APE weight `1/12` inside the dominance bound `[0, 1/6)`.

## 2. What is proved

* `obsW_physRange`: `(energy0 obsW (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r` for every `r > 1`
  (`FlowZero.apeFam_physRange` at `s = 1`; `Φ0 W` is `energy0 W (SymPlaqClass 2) (symPlaq_refl 2)` by
  definition).
* No `ClayStatementAt` capstone is stated at `obsW` from `MultiScaleStrongAt`: its `endpoint` field,
  `MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.

## 3. What the remaining inputs now say (read off the definitions)

With `W` fixed, the inputs that read `W` are statements about this one flow:
* `MultiScaleStrongAt obsW z μ b Wf cf`: its field `top` is `Wf b = obsW`, so the scale family must pass
  through `obsW` at `b`; `scale : ScaleControlAll b Wf` then asks the exponential moments of every
  monomial flowed by `Wf s` for `s ∈ [a_k, b]`, in particular by `obsW` at `s = b`. The family
  `Wf = FlowZero.apeFam (1/12)`, `b = 1` meets `top` by definition; `ScaleControlAll` for it, like
  `ClassMoments` for `apeFam` (the open input `hU` of `ExistenceFlow`), is not proved.
* `ProxyGen obsW b Wf cf r`: the flowed proxies are approximated in the reflection form by margin
  monomials of `obsW` at margin `r > 1`.
* `z`, `μ`, `ObsLower`, `WardT`, `CompNondeg`, `CoefBound`, `FlowCov` do not read `W`.

No declaration in this repository proves any of these inputs false at `obsW`. The exclusions that name an
observer do not apply to it. `ObserverCarries.not_clayStatementAt_flatFlow` is about `flatFlow L`, and
`obsW_ne_flatFlow` proves `obsW ≠ flatFlow L` for every `L`. `PlaquetteFloor.not_classMoments_identity` is
about `ConfFlow.identity 2`, and `obsW_ne_identity` proves `obsW ≠ ConfFlow.identity 2`; it also excludes
`ClassMoments`, which is not an input here. `FlowMoments.not_classMoments_of_reachBlowup` needs
`a_k · range k → 0`, while the reach of `obsW` is `a_k(⌊1/a_k⌋₊ + 3) ≥ 1 + 2a_k`.
`ObserverCarries.not_clayData_of_timeIndep` assumes that the continuum Schwinger functions of
`energy0 W D hD` are invariant under one time shift; nothing here decides that at `obsW`. Both inequalities
are read off the `range` field. ARGUED (not proved here): at every step with `a_k ≤ 1`, `obsW.V k` runs at
least one APE step with `c = 1/12 > 0` and is not `id`; only the finitely many steps with `a_k > 1` are `id`
(`FlowZero.apeFam_V_of_lt`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)` and the limits of the scalar and pseudoscalar factors; `1` the
physical smearing scale of the observer, and the bound below `r`; `1/12` an APE weight inside the
dominance bound `1/6`; `4` the dimension; `0` the lower end of the APE weight.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverChoice

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
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

/-- **The fixed `SU(2)` observer**: `FlowZero.apeFam` at APE weight `1/12` and physical smearing scale
`1`. DERIVED: `1/12` the APE weight; `1` the scale; `0`, `1/6` the dominance range. -/
def obsW : ConfFlow 2 :=
  FlowZero.apeFam (1 / 12) (by norm_num) (by norm_num) 1

/-- **`PhysRange r` of the fixed observer for every `r > 1`** (`FlowZero.apeFam_physRange` at `s = 1`).
DERIVED: `1` the smearing scale; `2` the rank. -/
theorem obsW_physRange {r : ℝ} (hr : 1 < r) :
    (energy0 obsW (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r :=
  FlowZero.apeFam_physRange (by norm_num) (by norm_num) zero_le_one hr

/-- **`obsW` is not the identity flow**: at `k = 0` its `range` is `⌊1/a_0⌋₊ + 3 ≠ 0`. DERIVED: `0` the
step read; `3` the range offset of `apeFam`; `2` the rank. -/
theorem obsW_ne_identity : obsW ≠ ConfFlow.identity 2 := by
  intro h
  have e : obsW.range 0 = (ConfFlow.identity 2).range 0 := by rw [h]
  have e2 : ⌊(1 : ℝ) / dySpacing 2 0⌋₊ + 3 = 0 := e
  omega

/-- **`obsW` is not a flat flow**: if `⌊1/a_k⌋₊ + 3 = 2 L k` for every `k`, then `⌊1/a_k⌋₊` is odd at
every `k`, so `⌊1/a_k⌋₊ + 1 = 2^k (⌊1/a_0⌋₊ + 1)`, which forces `1/a_0` to be an integer plus `1`, against
`1/a_0 < ⌊1/a_0⌋₊ + 1`. DERIVED: `2` the rank and the dyadic factor; `1`, `3` the range offsets. -/
theorem obsW_ne_flatFlow (L : ℕ → ℕ) : obsW ≠ MassGap.ExistenceFlow.flatFlow (N := 2) L := by
  intro h
  set x : ℕ → ℝ := fun k => 1 / dySpacing 2 k with hxdef
  have hpos : ∀ k, 0 < x k := fun k => one_div_pos.mpr (dySpacing_pos (by norm_num : 1 ≤ 2) k)
  have hx : ∀ k, x (k + 1) = 2 * x k := by
    intro k
    have hd : dySpacing 2 (k + 1) = dySpacing 2 k / 2 := by
      simp only [dySpacing, pow_succ]; field_simp
    have h0 := dySpacing_pos (by norm_num : 1 ≤ 2) k
    simp only [hxdef, hd]; field_simp
  have hodd : ∀ k, ⌊x k⌋₊ % 2 = 1 := by
    intro k
    have e : obsW.range k = (MassGap.ExistenceFlow.flatFlow (N := 2) L).range k := by rw [h]
    have e2 : ⌊x k⌋₊ + 3 = 2 * L k := e
    omega
  have hstep : ∀ k, ⌊x (k + 1)⌋₊ = 2 * ⌊x k⌋₊ + 1 := by
    intro k
    have h1 : 2 * ⌊x k⌋₊ ≤ ⌊x (k + 1)⌋₊ := by
      apply Nat.le_floor; rw [hx]; push_cast
      have := Nat.floor_le (hpos k).le; linarith
    have h2 : ⌊x (k + 1)⌋₊ < 2 * ⌊x k⌋₊ + 2 := by
      apply (Nat.floor_lt (hpos _).le).mpr; rw [hx]; push_cast
      have := Nat.lt_floor_add_one (x k); linarith
    have := hodd (k + 1); omega
  have hclosed : ∀ k, (⌊x k⌋₊ : ℝ) + 1 = 2 ^ k * ((⌊x 0⌋₊ : ℝ) + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ((2 * ⌊x k⌋₊ + 1 : ℕ) : ℝ) + 1 = 2 * ((⌊x k⌋₊ : ℝ) + 1) := by push_cast; ring
      rw [hstep k, e, ih, pow_succ]; ring
  have hxk : ∀ k, x k = 2 ^ k * x 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [hx, ih, pow_succ]; ring
  have hlt : x 0 < (⌊x 0⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / 2 : ℝ) ^ k < ((⌊x 0⌋₊ : ℝ) + 1) - x 0 :=
    exists_pow_lt_of_lt_one (by linarith) (by norm_num)
  have h3 : (⌊x k⌋₊ : ℝ) ≤ 2 ^ k * x 0 := (Nat.floor_le (hpos k).le).trans_eq (hxk k)
  have h4 := hclosed k
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h5 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
  nlinarith [mul_lt_mul_of_pos_left hk hp]

end MassGap.ObserverChoice

end

#print axioms MassGap.ObserverChoice.obsW_physRange
#print axioms MassGap.ObserverChoice.obsW_ne_identity
#print axioms MassGap.ObserverChoice.obsW_ne_flatFlow
