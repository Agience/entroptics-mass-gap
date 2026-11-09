import Mathlib
import MassGap.ObserverEnergyBox
import MassGap.ObserverGapScale

noncomputable section

/-!
# MassGap.ObserverEnergyReductionsN — the observer route's E, M, N reductions at every `SU(N)`

The reductions of `ObserverEnergyMoments` are stated here for every `N ≠ 0` and every configuration
flow `W : ConfFlow N` (the class-scaled energy density `ObserverEnergyMoments.energyOn W D hD s hs`),
and, where the field plays no role, for every flow `Φ : Flow N`.

1. **A gap at one step for any flow** (`flowN_clay_of_gap`): for any `Φ : Flow N` with the uniform
   bound and a physical range bound, a gap of the transfer at one step with N gives the gap at every
   dyadic step and the non-trivial vacuum.
2. **E for the energy density of any configuration flow** (`energyBoundN`, `energyN_clay_of_smearedMoments`,
   `energyN_clay_of_moments`, `energyN_clay_of_cubeMoments`, `uniformBoundF_energyN_of_smearedZoomBand`).
3. **The capstone** (`energyN_clay_of_gap`): smeared moments on `D` (E), a physical range bound, the
   transfer at one step gapped (M) and `FlowConnectedNonzero` (N) give, at every dyadic step, the gap at
   physical rate `c'/L` and a non-zero vector orthogonal to the vacuum, for every `N ≠ 0` and every
   `W : ConfFlow N`.
4. **Uniform cell moments** (`CellMomentsN`): every even moment of every cell energy is bounded
   eventually in the step, uniformly over the cells.

## Scope

The flow interface `ContinuumFlow.Flow N` reads `SU(N)` link configurations and the periodic Wilson
states `stateK hN k`; nothing here leaves `SU(N)`. The inputs E (the moments), M (the gap at one
step) and N (the pairing) are hypotheses here.
-/

namespace MassGap.ObserverEnergyReductionsN

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments
  MassGap.ObserverEnergyBox
    Filter MeasureTheory
open MassGap.ContinuumNontrivial (stateK_transObs)
open scoped Topology

variable {N : ℕ}

/-! ## 1. A gap at one step, for any flow -/

section Flow

/-- The reconstructed transfer of a flow at step `m₀` under a physical range bound.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
noncomputable abbrev transferN (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) : Transfer.TransferData (MarginMono N τ r →₀ ℝ) :=
  flowTransfer hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ) m0

/-- **The continuum statement of any flow from one gap at one step.** For `Φ : Flow N` with the
uniform bound and a physical range bound, the transfer at one step `m₀` gapped at some `0 < ρ < 1`
(M) and `FlowConnectedNonzero` (N) give, at every dyadic step, the gap at physical rate `c'/L` on a
space with a non-zero vector orthogonal to the vacuum (`flowClusterAbs_iff_gapAt`,
`flow_clay_of_abs_cluster`).

DERIVED: `0` and `1` bracket the rate, `0` the lower end of `L` and `c'`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem flowN_clay_of_gap (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hg : TransferGap.GapAt (transferN hN Φ hB τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN Φ τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt (transferN hN Φ hB τ hphys m) (Real.exp (-(c' / L) * dySpacing N m))
        ∧ ContinuumClay.NontrivialVacuum (transferN hN Φ hB τ hphys m) :=
  flow_clay_of_abs_cluster hN Φ hB τ _ hL
    ((flowClusterAbs_iff_gapAt hN Φ hB τ _ m0 hL).mpr ⟨ρ, hρ0, hρ1, hg⟩) hNT

#print axioms flowN_clay_of_gap

end Flow

/-! ## 2. E for the energy density of any configuration flow -/

section Energy

/-- **E's smeared moments on `D` give the uniform bound** of the class-scaled flow of any
`W : ConfFlow N` (`smearedMomentBound_energyOn`, `uniformBoundF_of_smearedMomentBound`).

DERIVED: `2` makes the power even; `4` in `Fin 4` is the spacetime dimension. -/
theorem energyBoundN (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C) :
    UniformBoundF hN (energyOn W D hD s hs) :=
  uniformBoundF_of_smearedMomentBound hN _ (smearedMomentBound_energyOn hN W D hD s hs hM)

#print axioms energyBoundN

/-- **The class-scaled flow's continuum statement from smeared moments on the class**, at every
`N ≠ 0` and every `W : ConfFlow N`: E (bounded smeared moments of every field of `D`), a physical range
bound, M (`FlowClusterAbs` at a window `L > 0`) and N give the gap at every dyadic step and the
non-trivial vacuum.

DERIVED: `2` makes the power even; `0` the lower end of `L` and `c'`; `4` in `Fin 4` is the spacetime
dimension. -/
theorem energyN_clay_of_smearedMoments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (energyOn W D hD s hs).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hcl : FlowClusterAbs hN (energyOn W D hD s hs) τ r L)
    (hNT : FlowConnectedNonzero hN (energyOn W D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (transferN hN (energyOn W D hD s hs) (energyBoundN hN W D hD s hs hM) τ hphys m)
          (Real.exp (-(c' / L) * dySpacing N m))
        ∧ ContinuumClay.NontrivialVacuum
          (transferN hN (energyOn W D hD s hs) (energyBoundN hN W D hD s hs hM) τ hphys m) :=
  flow_clay_of_abs_cluster hN _ (energyBoundN hN W D hD s hs hM) τ _ hL hcl hNT

#print axioms energyN_clay_of_smearedMoments

/-- **The class-scaled flow's continuum statement from the unsmeared moments on the class**: every
even moment of `O ∘ V_k − s_k O` of order the cell volume, `ν_k((O ∘ V_k − s_k O)^{2p}) ≤ C a_k^{8p}`
(`flowMomentBound_energyOn`, `uniformBoundF_of_momentBound`).

DERIVED: `2` makes the power even; `8 = 4 · 2`; `1` the unit observable; `0` the lower end of `L`
and `c'`; `4` in `Fin 4` is the spacetime dimension. -/
theorem energyN_clay_of_moments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (((W.fieldMap k O).1 - s k O • (1 : C(Cfg N, ℝ))) ^ (2 * p))
        ≤ C * dySpacing N k ^ (8 * p))
    (τ : Fin 4) {r : ℝ} (hphys : (energyOn W D hD s hs).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hcl : FlowClusterAbs hN (energyOn W D hD s hs) τ r L)
    (hNT : FlowConnectedNonzero hN (energyOn W D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (transferN hN (energyOn W D hD s hs)
            (uniformBoundF_of_momentBound hN _ (flowMomentBound_energyOn hN W D hD s hs hM)) τ hphys m)
          (Real.exp (-(c' / L) * dySpacing N m))
        ∧ ContinuumClay.NontrivialVacuum
          (transferN hN (energyOn W D hD s hs)
            (uniformBoundF_of_momentBound hN _ (flowMomentBound_energyOn hN W D hD s hs hM)) τ hphys m) :=
  flow_clay_of_abs_cluster hN _
    (uniformBoundF_of_momentBound hN _ (flowMomentBound_energyOn hN W D hD s hs hM)) τ _ hL hcl hNT

#print axioms energyN_clay_of_moments

/-- **The class-scaled flow's continuum statement from its cube moments**: a reflection-closed class
`D` of non-negative fields with subtraction of the order of the cell volume and bounded moments of the
flowed energy in every physical cube (`uniformBoundF_energyOn_of_cubeMoments`).

DERIVED: `0` the sign of the fields and the lower end of `L` and `c'`; `4` in `Fin 4` is the spacetime
dimension. -/
theorem energyN_clay_of_cubeMoments (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound N s O)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energyOn W D hD s hs).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hcl : FlowClusterAbs hN (energyOn W D hD s hs) τ r L)
    (hNT : FlowConnectedNonzero hN (energyOn W D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (transferN hN (energyOn W D hD s hs)
            (uniformBoundF_energyOn_of_cubeMoments hN W D hD s hs hpos hsub hcube) τ hphys m)
          (Real.exp (-(c' / L) * dySpacing N m))
        ∧ ContinuumClay.NontrivialVacuum
          (transferN hN (energyOn W D hD s hs)
            (uniformBoundF_energyOn_of_cubeMoments hN W D hD s hs hpos hsub hcube) τ hphys m) :=
  flow_clay_of_abs_cluster hN _
    (uniformBoundF_energyOn_of_cubeMoments hN W D hD s hs hpos hsub hcube) τ _ hL hcl hNT

#print axioms energyN_clay_of_cubeMoments

/-- **E for the class-scaled flow from the smeared zoom on its class**, at every `N`
(`smearedMoments_of_zoomBand`).

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem uniformBoundF_energyN_of_smearedZoomBand (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (h : ∀ O ∈ D, ∀ f : TestFn, SmearedZoomBand hN (energyOn W D hD s hs) O f) :
    UniformBoundF hN (energyOn W D hD s hs) :=
  energyBoundN hN W D hD s hs (fun O hO f p => smearedMoments_of_zoomBand hN _ O f (h O hO f) p)

#print axioms uniformBoundF_energyN_of_smearedZoomBand

/-- **The capstone at every `SU(N)`: the energy density's continuum statement from one gap at one
step.** For every `N ≠ 0` and every configuration flow `W : ConfFlow N`: smeared moments on `D` (E), a
physical range bound, the transfer at one step `m₀` gapped at some `0 < ρ < 1` (M), and
`FlowConnectedNonzero` (N) give, at every dyadic step, the gap at physical rate `c'/L` on a space with a
non-zero vector orthogonal to the vacuum.

DERIVED: `2` makes the power even; `0` and `1` bracket the rate, `0` the lower end of `L` and `c'`;
`4` in `Fin 4` is the spacetime dimension. -/
theorem energyN_clay_of_gap (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (energyOn W D hD s hs).PhysRange r) (m0 : ℕ)
    {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt
      (transferN hN (energyOn W D hD s hs) (energyBoundN hN W D hD s hs hM) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energyOn W D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (transferN hN (energyOn W D hD s hs) (energyBoundN hN W D hD s hs hM) τ hphys m)
          (Real.exp (-(c' / L) * dySpacing N m))
        ∧ ContinuumClay.NontrivialVacuum
          (transferN hN (energyOn W D hD s hs) (energyBoundN hN W D hD s hs hM) τ hphys m) :=
  flowN_clay_of_gap hN _ (energyBoundN hN W D hD s hs hM) τ hphys m0 hL hρ0 hρ1 hg hNT

#print axioms energyN_clay_of_gap

end Energy

section NonTrivial

end NonTrivial

/-! ## 3. Uniform cell moments -/

section W1

/-- **Uniform cell moments**: every even moment of every cell energy is bounded eventually in the
step, uniformly over the cells.

DERIVED: `2` makes the power even. -/
def CellMomentsN (hN : N ≠ 0) {Cl : Type} (e : ℕ → Cl → C(Cfg N, ℝ)) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop, ∀ c, stateK hN k (e k c ^ (2 * p)) ≤ C

end W1

section Instances

end Instances

end MassGap.ObserverEnergyReductionsN
