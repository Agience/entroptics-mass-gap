import Mathlib
import MassGap.TowerOpen
import MassGap.OneInput

/-!
# MassGap.ExistClose — the existence residual along the towers, with every proved clause removed

`OneInput.clayStatement_of_strongEnd` takes `StrongEnd N` and the residual `R`: at window couplings arbitrarily
close to `0⁺`, every coupling tower `βs` is a measured tower carrying `ConstantPhysicsLine.ExistAlong N βs`.
`ConsolidatedRoot.existAlong_of_open` reduces `ExistAlong` to `ConsolidatedRoot.OpenAlong N βs` at fixed
witnesses (observer `obsW`, mixing `rhoZ`, composites `csZ`). This module replaces the three link clauses
of `OpenAlong` (`wC`, `hLC`, `hX`), which `LinkAlongG.linkAlong` derives from the class moments, `ConvCG` and
`ApproxAlong`, by the single clause `ApproxAlong`, and restates the capstone of `OneInput` with that residual. The
link is reduced from three clauses to one; it is not discharged. `ApproxAlong` stays open, and so do `hU`, `hK`,
`hAF`, `hNG`, `hWard` and `hCO`. Declarations are in the namespace `MassGap.ExistClose`.

## The clauses of `OpenAlong`, one by one

* `wC`, `hLC`, `hX` (the link and the cross reading): derived along every tower from the class moments `hU`, the
  physical range, `ConvCG` of the composites (the first field of `hCO`) and `ApproxAlong` of the three kernels
  (`LinkAlongG.linkAlong`). Replaced by `ApproxAlong`, one clause in place of three.
* `hU` (the class moments, `ClassMomentsG`): kept. It is not a consequence of compactness of `SU(N)`. The cube
  sum `cubeSumG a_k R` adds the flowed reading over the sites of `[-R, R]⁴` at spacing `a_k`, about
  `(2R/a_k)⁴` of them, while the bound allows `((2R+1)⁴)^{2p}` with no `a_k`; so `hU` asks the plaquette
  reading to be of order `a_k⁴` in the state `periodicStateG (βs k)`. Boundedness of the reading gives only
  order one. This is an argument, not a proved theorem: at `p = 1` it uses `ν_k(E)² ≤ ν_k(E²)`. The scaling
  claim that `hU` needs order `a_k⁴` is likewise argued, not proved. The tree proves `hU` only from `SiteExpG` (`TowerOpen.classMomentsG_of_siteExpG`), which is
  stronger; `OpenClose` keeps the weaker `hU`.
* `hK`, `hAF` (`TwoPointKernelG`, `AFCoefficientG`), `hNG` (`NonGaussianTG`), `hWard` (`WardTG`), `hCO`
  (`CompOSG`): kept. Each reads the continuum readings `contTG` of the state; no theorem of the tree concludes
  any of them along a tower or at the frozen tower without a hypothesis of the same kind (`FlowWard`,
  `WardOff`, `ObsThreePoint`, `ObsLower`, `ExpandR`, `ExpandLim`, `GradientFlowProps`, `CompNondeg`).

## The statements

* `OpenClose N βs`: `OpenAlong` with `wC`, `hLC`, `hX` replaced by `ApproxAlong`.
* `openAlong_of_openClose`: `OpenClose ⇒ OpenAlong` (`LinkAlongG.linkAlong`).
* `openClose_of_openAlongR`: `TowerOpen.OpenAlongR ⇒ OpenClose`: `OpenClose` is implied by the reduced statement
  already in the tree (`SiteExpG ⇒ hU`), so it is no stronger than it.
* `existAlong_of_openClose`: `OpenClose ⇒ ExistAlong` (`ConsolidatedRoot.existAlong_of_open`).
* `clayStatement_of_strongEnd_open'`: `StrongEnd N` and the residual of `OneInput` with `ExistAlong` replaced by
  `OpenClose` give `ClayStatementOf (SU N)`.

## What remains, plainly

Along every tower near `0⁺`: the measured tower `MeasTowerG`, and in `OpenClose` the class moments `hU`, the
kernel with its asymptotic-freedom coefficient, non-Gaussianity, the Ward identity, `CompOSG` of the composites
and `ApproxAlong`. Each reads the state `periodicStateG (βs k)`. None of them is discharged here.

DERIVED (module-wide): `0` the plane, the limit `0⁺` and the signs; `2` the least rank; `π` in `π/N` the angle of
the centre of `SU(N)`; `12` a sufficient bound on the construction parameter `c` of the block step; `4` the
dimension; `(2·1 + 3)⁴` the site-count bound of the unit cube, inherited from `TowerOpen`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ExistClose

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.InputsG MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG MassGap.SUInputs
  MassGap.ClayGFinal Filter
open scoped Topology Matrix
open MassGap.MeasuredTower (schedAlongG MeasTowerG)
open MassGap.MeasuredSpacing (schedShiftInv_alongG)
open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.ConsolidatedRoot (obsW rhoZ csZ OpenAlong physRange_sunFam)
open MassGap.LinkAlongG (ApproxAlong linkAlong)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The existence residual along `βs`**: `ConsolidatedRoot.OpenAlong` with the link `wC`, `hLC`, `hX`
replaced by `ApproxAlong` of the three kernels. DERIVED: `0` the signs; `2` the least rank; `π` in `π/N` the
angle of the centre of `SU(N)`; `12` a sufficient bound on `c`. -/
def OpenClose (βs : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (t C₀ : ℝ) (_ : 0 < t)
    (_ : ClassMomentsG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqClassG (MassGap.SUN.SU N)) t C₀)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : CompositesRen.OffMix)
    (_ : ∃ Gk : ℝ → ℝ, TwoPointKernelG (schedAlongG _ βs) (rhoZ N zri zwe) Gk
      ∧ AFCoefficientG (constsG (MassGap.SUN.SU N)) Gk)
    (_ : NonGaussianTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : WardTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : CompOSG (schedAlongG _ βs) (csZ N zri zwe μ)),
    ApproxAlong N βs hc0 hc s₀ r zri zwe μ

/-- **`OpenClose ⇒ OpenAlong`**: the link from `ApproxAlong`, `ConvCG` (the first field of `CompOSG`) and the
class moments (`LinkAlongG.linkAlong`). DERIVED: no numeral. -/
theorem openAlong_of_openClose {βs : ℕ → ℝ} (h : OpenClose N βs) : OpenAlong N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, t, C₀, ht, hU, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, hA⟩ := h
  obtain ⟨wC, hLC, hX⟩ := linkAlong βs hc0 hc hs0 hr hU zri zwe μ hCO.1 hA
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, t, C₀, ht, hU, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, wC, hLC, hX⟩

/-- **`OpenAlongR ⇒ OpenClose`**: `SiteExpG` gives the class moments at `t = s / (2·1 + 3)⁴`
(`TowerOpen.classMomentsG_of_siteExpG`); every other clause is shared. DERIVED: `0` the sign of `t`;
`(2·1 + 3)⁴` the site-count bound of the unit cube, inherited from `TowerOpen`. -/
theorem openClose_of_openAlongR {βs : ℕ → ℝ} (h : TowerOpen.OpenAlongR N βs) : OpenClose N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, s, C₀, hs, hSE, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, hA⟩ := h
  have h625 : (0 : ℝ) < (2 * 1 + 3) ^ 4 := by norm_num
  have ht : 0 < s / (2 * 1 + 3) ^ 4 := div_pos hs h625
  have hSE' : TowerOpen.SiteExpG (schedAlongG _ βs) (obsW N hc0 hc s₀)
      (SymPlaqClassG (MassGap.SUN.SU N)) (s / (2 * 1 + 3) ^ 4 * (2 * 1 + 3) ^ 4) C₀ := by
    rw [div_mul_cancel₀ s h625.ne']
    exact hSE
  have hU := TowerOpen.classMomentsG_of_siteExpG (schedAlongG _ βs) (schedShiftInv_alongG _ βs)
    (obsW N hc0 hc s₀) (symPlaqG_nonneg (G := MassGap.SUN.SU N)) ht hSE'
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, _, _, ht, hU, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, hA⟩

/-- **`OpenClose ⇒ ExistAlong`** (`openAlong_of_openClose`, `ConsolidatedRoot.existAlong_of_open`).
DERIVED: no numeral. -/
theorem existAlong_of_openClose {βs : ℕ → ℝ} (h : OpenClose N βs) : ConstantPhysicsLine.ExistAlong N βs :=
  ConsolidatedRoot.existAlong_of_open (openAlong_of_openClose h)

/-- **The root at `SU(N)` from the bridge and the smaller residual.** `OneInput.clayStatement_of_strongEnd`
with `ExistAlong` in its residual replaced by `OpenClose` (`existAlong_of_openClose`). DERIVED: `0` the limit
`0⁺`; `2` the least rank. -/
theorem clayStatement_of_strongEnd_open' (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      MeasTowerG (MassGap.SUN.SU N) βs ∧ OpenClose N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  OneInput.clayStatement_of_strongEnd hS
    (hR.mono fun _ h βs hT => ⟨(h βs hT).1, existAlong_of_openClose (h βs hT).2⟩)

end MassGap.ExistClose

end

#print axioms MassGap.ExistClose.openAlong_of_openClose
#print axioms MassGap.ExistClose.openClose_of_openAlongR
#print axioms MassGap.ExistClose.existAlong_of_openClose
#print axioms MassGap.ExistClose.clayStatement_of_strongEnd_open'
