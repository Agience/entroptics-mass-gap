import Mathlib
import MassGap.MeasuredSpacing

/-!
# MassGap.ClayMeasDirect — the root statement from the clauses along a measured tower

The root `ClayStatementG.ClayStatementOf G` asks for a measured tower `βs` (`MeasuredTower.MeasTowerG`) and
every clause of `ClayStatementAtP` at the schedule along it, `schedAlongG G βs`. The wiring capstone
`ClayWiringG.clayStatementAtP_of_inputsG` holds at every schedule. This module reads it at `schedAlongG G βs`
and packs the result with the tower, so the root follows from the inputs stated along the tower itself, with no
hypothesis relating the tower to the two-loop schedule `dyBetaG` (the assumed `MeasuredSpacing.ScalingSU`).

* **`clayStatementOf_of_inputsAlongG`**: a measured tower `βs`, a reflection-closed class `D`, and the inputs of
  `clayStatementAtP_of_inputsG` at `schedAlongG G βs` and `constsG G`, give `ClayStatementOf G`. Two inputs of
  the wiring capstone are discharged at every tower: the translation invariance of the schedule
  (`MeasuredSpacing.schedTransInv_alongG`) and `0 < (constsG G).cAF` (`ClayStatementG.afConstG_pos`).

Every remaining input is a clause of the existence side read along `βs`: the basis convergence and its tie to
the trace constant, `OS0`, translation continuity, tensor covariance, the two-point kernel and its asymptotic
freedom coefficient, non-Gaussianity, non-degeneracy, the uniform bound and cut-off convergence of the energy
map, the link to the reconstructed space and its non-triviality, the composite channel, Ward, composite data and
`OS`, and generation, each stated at `schedAlongG G βs`; the tower `MeasTowerG G βs` is an input as well. None is
proved here.

Foundational footprint only (`#print axioms` at the end of each theorem).

DERIVED (module-wide): `4` the dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ClayMeasDirect

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring MassGap.ClayWiringG MassGap.MeasuredTower Filter
open scoped Topology Matrix

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]
variable {τ : Fin 4} {r : ℝ}

/-- **The root statement of `G` from the clauses along a measured tower.** A measured tower `βs`, a
reflection-closed class `D`, and the inputs of `ClayWiringG.clayStatementAtP_of_inputsG` at
`schedAlongG G βs` and `constsG G`, other than the translation invariance of the schedule and the sign of the
asymptotic freedom constant, give `ClayStatementOf G`.

DERIVED: `4` the dimension; `0` the vanishing pairing and the zero vector. -/
theorem clayStatementOf_of_inputsAlongG (βs : ℕ → ℝ) (hT : MeasTowerG G βs)
    (W : ConfFlowG G) (D : Set (LField G)) (hD : ∀ (τ' : Fin 4) (O : LField G), O.refl τ' ∈ D ↔ O ∈ D)
    (X : OSDataSLinkedG G D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG (schedAlongG G βs) W D O g)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.base.time))
    (hXO : X.O = symG (plaqFieldG ObserverEnergyMoments.q0))
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG (schedAlongG G βs) op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * (schedAlongG G βs).a k ^ 4) atTop
      (𝓝 (constsG G).cTr))
    (h0 : OS0OwnG (schedAlongG G βs) op Z)
    (hTC : TransContTG (schedAlongG G βs) (mixOfZG B op m Z))
    (hCov : TensorCovG (schedAlongG G βs) (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (schedAlongG G βs) (mixOfZG B op m Z) Gk)
    (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (schedAlongG G βs) (mixOfZG B op m Z))
    (hND : TensorNondegG (schedAlongG G βs) (mixOfZG B op m Z))
    (hUB : UniformBoundFG (schedAlongG G βs) (energyMapG (schedAlongG G βs) W D))
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG (schedAlongG G βs) (energyMapG (schedAlongG G βs) W D)
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG (schedAlongG G βs) W D O g)))
    (w : TSep τ → X.base.H) (hL : LinkHSG (schedAlongG G βs) W D X (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG (schedAlongG G βs) (constsG G) Zc)
    (hWard : WardTG (schedAlongG G βs) (mixOfZG B op m Z)) (hCD : CompDataG C)
    (hCO : CompOSG (schedAlongG G βs) C) (hLC : LinkCG (schedAlongG G βs) X C wC)
    (hTI : TInG (mixOfZG B op m Z) C X w wC) (hGen : ObsGenG (schedAlongG G βs) W D X) :
    ClayStatementOf G :=
  ⟨βs, hT, W, D, hD,
    clayStatementAtP_of_inputsG (schedAlongG G βs) (constsG G) (afConstG_pos G) W D X hSM hsa hXO op m Z
      hBC hRie b0 κ htr hop hZtie h0 (MeasuredSpacing.schedTransInv_alongG G βs) hTC hCov Gk hK hAF hNG hND
      hUB hCut w hL hnt C wC hCT hWard hCD hCO hLC hTI hGen⟩

#print axioms clayStatementOf_of_inputsAlongG

end Group

end MassGap.ClayMeasDirect

end
