import Mathlib
import MassGap.ClayGFinal
import MassGap.TowerParamFree

/-!
# MassGap.ConstantPhysicsLine — the root statement at `SU(N)` from one line of constant window coupling

The root `ClayStatementG.ClayStatementOf (SU N)` asks for a measured tower and every clause of `ClayStatementAtP`
along it. `ClayGFinal.clayStatementOf_of_noNTAlong` gives it from a measured tower, the observer's transfer gap at
step `0`, the existence clauses along the tower, and `AbelianGenG`. This module states one line of constant
window coupling carrying the existence clauses, and derives the root from it. Declarations are in the namespace
`MassGap.ConstantPhysicsLine`.

## The statements

* `ExistAlong N βs`: the existence clauses of `clayStatementOf_of_noNTAlong` along `βs`, with every witness
  existential: a configuration flow `W` with the class moments and physical range, a mixing `ρ` with the Riemann,
  scalar-tie, covariance and channel-tie clauses, a two-point kernel with its asymptotic-freedom coefficient,
  non-Gaussianity and the Ward identity, composites with their data, `OS` and pre-observer link, the index map,
  and the cross reading. Each clause is a clause of the target read along `βs` (a restatement, not a reduction).
* `LineOfConstantPhysics N` (written `M`): arbitrarily close to `0⁺` there are window couplings `u₀` with a
  coupling tower at `u₀` (`CouplingTower N u₀ βs id`: the window `2^k` reads `u₀` exactly at `βs k → ∞`), along
  which the window reading of the measured mass converges (`UVConverges`), and along which `ExistAlong` holds.
  `M` is a bundle of three inputs, not one statement: `StrongEnd N` (the tower part, `frequently_towers_iff`),
  (UV) along the towers, and `ExistAlong` along the towers (`line_of_reads`).

## What is derived from `M` (proved)

* `clayStatementOf_of_line`: `M ⇒ ClayStatementOf (SU N)`, for `N ≥ 2`. Derived on the way: the measured tower
  (`MeasTowerG`, from the tower, the proved confinement `GapReadsTensorProved.confinedAt` and the convergence),
  the observer's transfer gap at step `0` (`CouplingTower.observerGap_along`, under `u₀ ≤ …` along a coupling
  tower, whose existence near `0⁺` still requires `StrongEnd N`, open), `AbelianGenG (SU N)`
  (`AbelianGen.abelianGenG_SU`), and through `clayStatementOf_of_noNTAlong` the Hamiltonian and spectral gaps,
  the two non-triviality clauses, `OS2`/`OS4`, the link, observer generation and the remaining clauses of
  `ClayDataP`.
* `strongEnd_of_line`: `M ⇒ StrongEnd N`.
* `frequently_towers_iff`: the tower part of `M` alone is exactly `StrongEnd N` (no stronger, no weaker).
* `line_of_reads`: `StrongEnd N`, (UV) along the towers near `0⁺`, and `ExistAlong` along the towers near `0⁺`
  give `M`; `clayStatementOf_of_reads` is the root from these three.

## Tests (proved)

* `not_frequently_tower_const`: a reading that does not run (constant in `β` and in the window) has no tower at
  window couplings arbitrarily close to `0⁺`, whatever its value: the tower part of `M` fails for every
  scale-invariant reading. The massless free field and the Coulomb phase of `U(1)` read this way at weak coupling
  (argued: their window coupling tends to a non-zero constant, the Casimir coefficient of `CasimirStep`).
* `not_measTowerG_const`: a constant coupling schedule is no measured tower, while the ultralocal schedule meets
  the per-step gap (`CouplingTower.stepGap_at_zero`): the gap clause and the tower clause separate on the tree's
  own objects.

DERIVED (module-wide): `0` the limit `0⁺` of the window coupling, the time axis, the plane, the step and the
signs; `2` the least rank, the window base and the doubling of `dySpacingG`; `4` the dimension. Proof-internal:
`1/1000` the seed of `DoublingSharp`, in private lemmas only, used to pick one `u₀` from the frequent set; `log 2`
the window rate.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ConstantPhysicsLine

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
open MassGap.MeasuredSpacing (schedOS_alongG)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The existence clauses along `βs`**: the inputs of `ClayGFinal.clayStatementOf_of_noNTAlong` at
`G = SU(N)` other than the tower, the observer's transfer gap and `AbelianGenG`, every witness existential.

DERIVED: `0` the sign of `t`, the plane and the time axis; `2` the least rank; `4` the dimension (in `Idx4`). -/
def ExistAlong (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlowG (MassGap.SUN.SU N)) (t C₀ : ℝ) (_ : 0 < t)
    (hU : ClassMomentsG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)) t C₀) (r : ℝ)
    (hphys : (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))
      (symPlaqG_refl (MassGap.SUN.SU N))).PhysRange (schedAlongG _ βs) r)
    (ρ : RenormMixG (MassGap.SUN.SU N)) (_ : ρ.Riemann)
    (_ : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := MassGap.SUN.SU N) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (schedAlongG (MassGap.SUN.SU N) βs).a k ^ 4) atTop
          (𝓝 (constsG (MassGap.SUN.SU N)).cTr))
    (_ : TensorCovG (schedAlongG _ βs) ρ)
    (_ : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (schedAlongG (MassGap.SUN.SU N) βs).a k ^ 4) atTop
          (𝓝 (constsG (MassGap.SUN.SU N)).cTop))
    (Gk : ℝ → ℝ) (_ : TwoPointKernelG (schedAlongG _ βs) ρ Gk)
    (_ : AFCoefficientG (constsG (MassGap.SUN.SU N)) Gk)
    (_ : NonGaussianTG (schedAlongG _ βs) ρ) (_ : WardTG (schedAlongG _ βs) ρ)
    (Cs : CompositesG (MassGap.SUN.SU N))
    (wC : TSepG Cs.Ix 0 → preHGAlong βs W hU hphys)
    (e : Idx4 → Cs.Ix) (_ : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (_ : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (_ : CompDataG Cs) (_ : CompOSG (schedAlongG _ βs) Cs)
    (_ : LinkCPreG (schedAlongG _ βs) 0 (preVacGAlong βs W hU hphys) (preTimeGAlong βs W hU hphys)
      Cs wC),
    ∀ (P : TSep 0) (Q : MarginMonoDG (MassGap.SUN.SU N) (SymPlaqClassG (MassGap.SUN.SU N)) 0 r),
      Tendsto (fun k => mixLatTG (schedAlongG _ βs) ρ
          (energyMapG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N))) 0 k P.1 Q.1.1)
          (ultra : Filter ℕ)
          (𝓝 (mixTG (schedAlongG _ βs) ρ (energyMapG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)))
            0 P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (preCvecGAlong βs W hU hphys Q)
          = (mixTG (schedAlongG _ βs) ρ (energyMapG (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)))
              0 P.1 Q.1.1 : ℂ)

variable (N) in
/-- **`M`: a line of constant window coupling carrying the continuum limit.** Arbitrarily close to `0⁺` there are
window couplings `u₀` with a coupling tower `βs` at `u₀` along which the window reading of the measured mass
converges and the existence clauses hold. `M` bundles three inputs: `StrongEnd N` (`frequently_towers_iff`), (UV)
along the towers and `ExistAlong` along the towers (`line_of_reads`).

DERIVED: `0` the limit `0⁺`; `2` the least rank. -/
def LineOfConstantPhysics : Prop :=
  ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ,
    CouplingTower N u₀ βs id ∧ (∃ μ : ℝ, UVConverges N βs id μ) ∧ ExistAlong N βs

/-- The seed's half-line, positive part, near `0⁺`. Inherited: `1/1000` the seed. -/
theorem seed_near : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u ∧ u ≤ 1 / 1000 :=
  inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num)))

/-- The root from a measured tower, the tower in the basin and the existence clauses. Inherited: the seed `1/1000`. DERIVED: `1/1000` the seed; `2` the least rank. -/
theorem clayStatementOf_of_tower {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ}
    (hT : CouplingTower N u₀ βs id) (hM : MeasTowerG (MassGap.SUN.SU N) βs) (hE : ExistAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) := by
  obtain ⟨W, t, C₀, ht, hU, r, hphys, ρ, hRie, hTie, hCov, hCT, Gk, hK, hAF, hNG, hWard, Cs, wC, e, he1, he2,
    hCD, hCO, hLC, hX⟩ := hE
  obtain ⟨ρ₀, hρ0, hρ1, hg⟩ := CouplingTower.observerGap_along hu hT
    (energy0G (schedAlongG _ βs) W (SymPlaqClassG (MassGap.SUN.SU N)) (symPlaqG_refl (MassGap.SUN.SU N)))
    (preBGAlong βs W hU) hphys 0
  exact clayStatementOf_of_noNTAlong βs hM W ht hU hphys hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK hAF hNG hWard
    Cs wC e he1 he2 hCD hCO hLC hX (MassGap.AbelianGen.abelianGenG_SU N)

/-- **`M ⇒ ClayStatementOf (SU N)`.** The measured tower, the observer's transfer gap, `AbelianGenG` and every
clause of `ClayDataP` not in `ExistAlong` are derived; the transfer gap holds under `u₀ ≤ …` along a coupling
tower, whose existence near `0⁺` still requires `StrongEnd N` (open; `strongEnd_of_line`). DERIVED: `2` the
least rank. Proof-internal: `1/1000` the seed; `log 2` the window rate. -/
theorem clayStatementOf_of_line (hL : LineOfConstantPhysics N) : ClayStatementOf (MassGap.SUN.SU N) := by
  obtain ⟨u, ⟨βs, hT, ⟨μ, hμ⟩, hE⟩, -, hu⟩ := (hL.and_eventually seed_near).exists
  have hM : MeasTowerG (MassGap.SUN.SU N) βs :=
    CouplingTower.measTowerG_of_confinedAt_uv hT (Real.log_pos one_lt_two)
      (GapReadsTensorProved.confinedAt (Fact.out : 2 ≤ N) hu) hμ
  exact clayStatementOf_of_tower hu hT hM hE

/-- **The tower part of `M` is exactly the strong end.** DERIVED: `2` the least rank; `0` the limit `0⁺`.
Inherited: `1/1000` the seed. -/
theorem frequently_towers_iff :
    (∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id) ↔ StrongEnd N := by
  constructor
  · intro h
    obtain ⟨u, ⟨βs, hT⟩, -, hu⟩ := (h.and_eventually seed_near).exists
    exact CouplingTower.strongEnd_of_couplingTower (NeZero.ne N) hu hT
  · intro hS
    exact ((TowerParamFree.vanishing_iff_towers (Fact.out : 2 ≤ N)).mp
      ((StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mp hS)).frequently

/-- **`M ⇒ StrongEnd N`.** DERIVED: `2` the least rank. -/
theorem strongEnd_of_line (hL : LineOfConstantPhysics N) : StrongEnd N :=
  frequently_towers_iff.mp (hL.mono fun _ ⟨βs, hT, _, _⟩ => ⟨βs, hT⟩)

/-- **The strong end, (UV) and the existence clauses along the towers near `0⁺` give `M`.** DERIVED: `2` the
least rank; `0` the limit `0⁺`. -/
theorem line_of_reads (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ)
    (hE : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ExistAlong N βs) :
    LineOfConstantPhysics N := by
  have htow := (TowerParamFree.vanishing_iff_towers (Fact.out : 2 ≤ N)).mp
    ((StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mp hS)
  exact ((htow.and (hUV.and hE)).mono fun _ ⟨⟨βs, hT⟩, h1, h2⟩ => ⟨βs, hT, h1 βs hT, h2 βs hT⟩).frequently

/-- **The root from the strong end, (UV) and the existence clauses along the towers near `0⁺`.** DERIVED: `2`
the least rank; `0` the limit `0⁺`. -/
theorem clayStatementOf_of_reads (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ)
    (hE : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ExistAlong N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_line (line_of_reads hS hUV hE)

/-- **A reading that does not run has no tower near `0⁺`**: for every value `g₀`, window couplings arbitrarily
close to `0⁺` with a tower of the constant reading `g₀` do not exist. DERIVED: `0` the limit `0⁺`. -/
theorem not_frequently_tower_const (g₀ : ℝ) :
    ¬ ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ (βs : ℕ → ℝ) (ws : ℕ → ℕ),
      CouplingTower.TowerOf (fun _ _ => g₀) u₀ βs ws := by
  intro h
  have h' : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), u₀ = g₀ :=
    h.mono fun u hu => (CouplingTower.exists_towerOf_const_iff g₀ u).mp hu
  rcases le_or_gt g₀ 0 with hg | hg
  · have hpos : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u := self_mem_nhdsWithin
    obtain ⟨u, hu, hp⟩ := (h'.and_eventually hpos).exists
    rw [hu] at hp
    linarith
  · have hlt : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < g₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsGT hg) fun u hu => hu.2
    obtain ⟨u, hu, hl⟩ := (h'.and_eventually hlt).exists
    rw [hu] at hl
    exact lt_irrefl _ hl

/-- **A constant coupling schedule is no measured tower.** With `CouplingTower.stepGap_at_zero` (the ultralocal
schedule meets the per-step gap) the gap clause and the tower clause separate. DERIVED: `2` the least rank. -/
theorem not_measTowerG_const (c : ℝ) : ¬ MeasTowerG (MassGap.SUN.SU N) (fun _ => c) :=
  fun h => not_tendsto_const_atTop c atTop h.1

end MassGap.ConstantPhysicsLine

end

#print axioms MassGap.ConstantPhysicsLine.seed_near
#print axioms MassGap.ConstantPhysicsLine.clayStatementOf_of_tower
#print axioms MassGap.ConstantPhysicsLine.clayStatementOf_of_line
#print axioms MassGap.ConstantPhysicsLine.frequently_towers_iff
#print axioms MassGap.ConstantPhysicsLine.strongEnd_of_line
#print axioms MassGap.ConstantPhysicsLine.line_of_reads
#print axioms MassGap.ConstantPhysicsLine.clayStatementOf_of_reads
#print axioms MassGap.ConstantPhysicsLine.not_frequently_tower_const
#print axioms MassGap.ConstantPhysicsLine.not_measTowerG_const
