import Mathlib
import MassGap.SymPlaqG

/-!
# MassGap.AxisInvG — the axis-permutation invariance of the periodic Wilson state of a gauge group `G`

`SymPlaqG.SchedAxisInv S` asks that the state of every step be invariant under the axis
permutations: `S.ν k (iaxisObs e F) = S.ν k F`. At `SU(N)` it is `SymPlaqG.schedAxisInv_SU`, through
`ContinuumHypercubic.torusState_axis` / `periodicState_axis` and `SUN.su_expect_invariant` at
`WilsonHypercubic.axisSymmetry`. This module proves it at `canonSched G` for every `GaugeGroup G`
with `GaugeSimple G`, by the same route with `SU N` replaced by `G`:

| step | `SU(N)` | here (any `G`) |
|---|---|---|
| axis permutation as a `Symmetry` | `WilsonHypercubic.axisSymmetry` | `axisSymmetryG` |
| Gibbs expectation invariant | `SUN.su_expect_invariant` | `expect_axis_invariantG` |
| pullback intertwines the relabellings | `ContinuumHypercubic.pullback_iaxisConf` | `pullback_iaxisConfG` |
| torus state invariant | `ContinuumHypercubic.torusState_axis` | `torusStateG_axis` |
| every limit of torus states invariant | (inside `periodicState_axis`) | `axis_of_tendsto_torusG` |
| infinite-volume state invariant | `ContinuumHypercubic.periodicState_axis` | `periodicStateG_axis` |
| `SchedAxisInv` | `SymPlaqG.schedAxisInv_SU` | `schedAxisInv_canonSched` |

A plaquette of `WilsonHypercubic.Plaq` carries the ordered pair of its spanning directions, and the
axis relabelling `axisPlaq e` moves both entries by `e`; `WilsonHypercubic.bd_axis` states that the
boundary word of `axisPlaq e q` is the word of `q` with every link relabelled and every orientation
flag kept. So the relabelled holonomy of `q` is the holonomy of `axisPlaq e q`, with no inversion, and
the action is invariant by reindexing the plaquette sum (`LatticeGauge.Symmetry.action_invariant`).
The measure half is a relabelling of links, which uses only that `probHaar G` is a probability measure
(`LatticeGauge.Symmetry.reindex_measurePreserving`). No property of `wilsonDensityG G` enters.

`periodicStateG G β` is a `Classical.choose` of a limit of the torus states; no uniqueness of that
limit is used, since every limit of axis-invariant states is axis invariant (`axis_of_tendsto_torusG`).

`clayStatementAtG_of_inputsG''''` is `SymPlaqG.clayStatementAtG_of_inputsG'''` with the input
`SchedAxisInv (canonSched G)` discharged by `schedAxisInv_canonSched`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `1` in `M + 1` the successor of `finMod`; `2k + 1` the extent
index of the torus family.
-/

noncomputable section

namespace MassGap.AxisInvG

open MeasureTheory MassGap.CompactGauge MassGap.GaugeGroup

/-! ## 1. The axis permutations on the finite periodic lattice -/

section Finite

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {d n : ℕ} [NeZero n]

/-- **An axis permutation as a symmetry of the Wilson system of `G`**: `WilsonLattice.wilsonSymmetry`
from `axisLink e`, `axisPlaq e` and the boundary-word compatibility `WilsonHypercubic.bd_axis e`.

DERIVED: no numeral. -/
def axisSymmetryG (e : Equiv.Perm (Fin d)) :
    MassGap.LatticeGauge.Symmetry (GaugeWilson.sysWilsonG G d n) :=
  MassGap.WilsonLattice.wilsonSymmetry (G := G) (MassGap.WilsonHypercubic.bd (d := d) (n := n))
    (wilsonDensityG G) (MassGap.WilsonHypercubic.axisLink e) (MassGap.WilsonHypercubic.axisPlaq e)
    (MassGap.WilsonHypercubic.bd_axis e)

/-- **The Wilson Gibbs expectation of `G` is invariant under every axis permutation**:
`EWG G β (O ∘ reindex (axisSymmetryG G e).onLink) = EWG G β O`, at every real `β` and every
observable `O`.

DERIVED: no numeral. -/
theorem expect_axis_invariantG (e : Equiv.Perm (Fin d)) (β : ℝ)
    (O : (MassGap.WilsonHypercubic.Link d n → G) → ℝ) :
    GaugeWilson.EWG G (d := d) (n := n) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex (axisSymmetryG G (n := n) e).onLink U))
      = GaugeWilson.EWG G (d := d) (n := n) β O :=
  MassGap.LatticeGauge.Symmetry.expect_invariant (GaugeWilson.sysWilsonG G d n) (probHaar G)
    (axisSymmetryG G e) β O

end Finite

/-! ## 2. The torus states and their limits -/

section Torus

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The periodic pullback intertwines the relabellings**: `iaxisConf e (pullback M W)` is the
pullback of `W` reindexed by the link permutation of `axisSymmetryG G e`.

DERIVED: `4` the dimension; `1` in `M + 1` the successor of `finMod`. -/
theorem pullback_iaxisConfG (M : ℕ) (e : Equiv.Perm (Fin 4))
    (W : MassGap.WilsonHypercubic.Link 4 (M + 1) → G) :
    MassGap.ContinuumHypercubic.iaxisConf e (MassGap.InfiniteLattice.pullback M W)
      = MassGap.InfiniteLattice.pullback M (MassGap.LatticeGauge.Symmetry.reindex
          (axisSymmetryG G (d := 4) (n := M + 1) e).onLink W) := by
  funext l
  show W (MassGap.InfiniteLattice.linkMod M (MassGap.ContinuumHypercubic.iaxisLink e l))
    = W (MassGap.WilsonHypercubic.axisLink (n := M + 1) e (MassGap.InfiniteLattice.linkMod M l))
  rw [MassGap.ContinuumHypercubic.linkMod_iaxisLink]

/-- **Every torus state of `G` is invariant under the axis permutations**:
`torusStateG G M β (iaxisObs e f) = torusStateG G M β f` at every extent, coupling and `e`.

DERIVED: `4` the dimension; `1` in `M + 1` the successor of `finMod`. -/
theorem torusStateG_axis (M : ℕ) (β : ℝ) (e : Equiv.Perm (Fin 4))
    (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    GaugeWilson.torusStateG G M β (MassGap.ContinuumHypercubic.iaxisObs e f)
      = GaugeWilson.torusStateG G M β f := by
  have hobs : GaugeWilson.torusObsG G M (MassGap.ContinuumHypercubic.iaxisObs e f)
      = fun W => GaugeWilson.torusObsG G M f (MassGap.LatticeGauge.Symmetry.reindex
          (axisSymmetryG G (d := 4) (n := M + 1) e).onLink W) := by
    funext W
    show f (MassGap.ContinuumHypercubic.iaxisConf e (MassGap.InfiniteLattice.pullback M W))
      = f (MassGap.InfiniteLattice.pullback M (MassGap.LatticeGauge.Symmetry.reindex
          (axisSymmetryG G (d := 4) (n := M + 1) e).onLink W))
    rw [pullback_iaxisConfG]
  show GaugeWilson.EWG G (d := 4) (n := M + 1) β
      (GaugeWilson.torusObsG G M (MassGap.ContinuumHypercubic.iaxisObs e f))
    = GaugeWilson.EWG G (d := 4) (n := M + 1) β (GaugeWilson.torusObsG G M f)
  rw [hobs]
  exact expect_axis_invariantG G e β (GaugeWilson.torusObsG G M f)

/-- **Every limit of the torus states of `G` along a non-trivial filter is invariant under the axis
permutations.**

DERIVED: `2k + 1` the extent index; `4` the dimension. -/
theorem axis_of_tendsto_torusG (β : ℝ) (e : Equiv.Perm (Fin 4))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G)) {l : Filter ℕ} [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      Filter.Tendsto (fun k : ℕ => GaugeWilson.torusStateG G (2 * k + 1) β f) l (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      ν (MassGap.ContinuumHypercubic.iaxisObs e f) = ν f := by
  intro f
  refine tendsto_nhds_unique (htend (MassGap.ContinuumHypercubic.iaxisObs e f)) ?_
  exact (htend f).congr (fun k => (torusStateG_axis G (2 * k + 1) β e f).symm)

/-- **`periodicStateG G β` is invariant under every axis permutation**, at every real `β`: the
mirror of `ContinuumHypercubic.periodicState_axis`.

DERIVED: `4` the dimension. -/
theorem periodicStateG_axis (β : ℝ) (e : Equiv.Perm (Fin 4)) :
    ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      GaugeWilson.periodicStateG G β (MassGap.ContinuumHypercubic.iaxisObs e f)
        = GaugeWilson.periodicStateG G β f := by
  haveI : (((GaugeWilson.exists_periodic_limit_dvdG G β).choose : Ultrafilter ℕ) :
      Filter ℕ).NeBot := (GaugeWilson.exists_periodic_limit_dvdG G β).choose.neBot'
  exact axis_of_tendsto_torusG G β e (GaugeWilson.periodicStateG G β)
    (MassGap.ShiftInvG.tendsto_periodicStateG G β)

end Torus

/-! ## 3. `SchedAxisInv` at the canonical schedule -/

section Sched

open MassGap.ClayTreeG MassGap.SymPlaqG

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The canonical schedule of `G` is invariant under the axis permutations**:
`SchedAxisInv (canonSched G)`, from `periodicStateG_axis` at the coupling `dyBetaG G k` of each step.

DERIVED: no numeral. -/
theorem schedAxisInv_canonSched [GaugeSimple G] : SchedAxisInv (canonSched G) :=
  fun k e F => periodicStateG_axis G (dyBetaG G k) e F

end Sched

/-! ## 4. The capstone with `SchedAxisInv` discharged -/

section Capstone

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring MassGap.ClayWiringG MassGap.EnergyBoundG
  MassGap.SymPlaqG Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]
variable {τ : Fin 4} {r : ℝ}

/-- **`ClayStatementAtG G W (SymPlaqClassG G)` with `SchedAxisInv (canonSched G)` discharged**:
`SymPlaqG.clayStatementAtG_of_inputsG'''` with `hA := schedAxisInv_canonSched`; every other
hypothesis is the same.

DERIVED: no numeral. -/
theorem clayStatementAtG_of_inputsG'''' (W : ConfFlowG G)
    (X : OSDataSLinkedG G (SymPlaqClassG G) τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG (canonSched G) W (SymPlaqClassG G) O g)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.base.time))
    (hXO : X.O = symG (plaqFieldG ObserverEnergyMoments.q0))
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG (canonSched G) op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * (canonSched G).a k ^ 4) atTop
      (𝓝 (constsG G).cTr))
    (h0 : OS0OwnG (canonSched G) op Z)
    (hTC : TransContTG (canonSched G) (mixOfZG B op m Z))
    (hCov : TensorCovG (canonSched G) (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (canonSched G) (mixOfZG B op m Z) Gk)
    (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (canonSched G) (mixOfZG B op m Z))
    (hND : TensorNondegG (canonSched G) (mixOfZG B op m Z))
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG (canonSched G) W O)
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ SymPlaqClassG G) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG (canonSched G) (energyMapG (canonSched G) W (SymPlaqClassG G))
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG (canonSched G) W (SymPlaqClassG G) O g)))
    (w : TSep τ → X.base.H)
    (hL : LinkHSG (canonSched G) W (SymPlaqClassG G) X (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG (canonSched G) (constsG G) Zc)
    (hWard : WardTG (canonSched G) (mixOfZG B op m Z)) (hCD : CompDataG C)
    (hCO : CompOSG (canonSched G) C) (hLC : LinkCG (canonSched G) X C wC)
    (hTI : TInG (mixOfZG B op m Z) C X w wC) (hGen : ObsGenG (canonSched G) W (SymPlaqClassG G) X) :
    ClayStatementAtG G W (SymPlaqClassG G) :=
  clayStatementAtG_of_inputsG''' W X hSM hsa hXO op m Z hBC hRie b0 κ htr hop hZtie h0 hTC hCov
    Gk hK hAF hNG hND hW schedAxisInv_canonSched hcube hCut w hL hnt C wC hCT hWard hCD hCO hLC hTI
    hGen

end Capstone

end MassGap.AxisInvG

end

#print axioms MassGap.AxisInvG.axisSymmetryG
#print axioms MassGap.AxisInvG.expect_axis_invariantG
#print axioms MassGap.AxisInvG.pullback_iaxisConfG
#print axioms MassGap.AxisInvG.torusStateG_axis
#print axioms MassGap.AxisInvG.axis_of_tendsto_torusG
#print axioms MassGap.AxisInvG.periodicStateG_axis
#print axioms MassGap.AxisInvG.schedAxisInv_canonSched
#print axioms MassGap.AxisInvG.clayStatementAtG_of_inputsG''''
