import Mathlib
import MassGap.AxisInvG

/-!
# MassGap.ReflInvG — the reflection invariance of the periodic Wilson state of a gauge group `G`

At `SU(N)` the periodic state is reflection invariant about every constant `c : ℤ` in every direction
(`PeriodicState.periodicState_reflInvariant`), and `ContinuumFlow.stateK_refl_field` reads that at the
state of each step and the constant `0`. This module proves both for every `GaugeGroup G`, by the same
route with `SU N` replaced by `G`:

| step | `SU(N)` | here (any `G`) |
|---|---|---|
| coordinate map of the reflection | `ActionSplit.axisDagger` | `axisDaggerG` |
| it preserves Haar measure | `ActionSplit.axisDagger_measurePreserving` | `axisDaggerG_measurePreserving` |
| reflection as a twist | `ActionSplit.reflConf_eq_twist` | `reflConf_eq_twistG` |
| reflection preserves product Haar measure | `Reflect.reflConf_measurePreserving` | `reflConf_measurePreservingG` |
| reflection as a measurable equivalence | `Reflect.reflConfEquiv` | `reflConfEquivG` |
| Gibbs expectation invariant | `Reflect.expect_reflect_invariant` | `expect_reflect_invariantG` |
| pullback intertwines the reflections | `PeriodicState.pullback_ireflConf` | `pullback_ireflConfG` |
| torus observable of a reflected observable | `PeriodicState.torusObs_refl`, `torusObs_refl_mul` | `torusObsG_refl`, `torusObsG_refl_mul` |
| torus state invariant | `PeriodicState.torusState_reflInvariant` | `torusStateG_reflInvariant` |
| every limit of torus states invariant | `PeriodicState.reflInvariant_of_tendsto_torus` | `reflInvariant_of_tendsto_torusG` |
| infinite-volume state invariant | `PeriodicState.periodicState_reflInvariant` | `periodicStateG_reflInvariant` |
| field form at each step | `ContinuumFlow.stateK_refl_field` | `canonSched_refl_field` |

The measure half of a reflection is a relabelling of links together with inversion on the links along
the axis. The relabelling uses only that `probHaar G` is a probability measure; the inversion uses
`Reflect.isInvInvariant_probHaar`, which holds for every compact Borel group. The action half is
`ShiftInvG.reflect_action_invariantG`, where each mirrored holonomy is a conjugate of the image
plaquette's and `wilsonDensityG_conj` discards the conjugation.

`SchedReflInv S` asks that the state of every step of `S` be reflection invariant about every constant
in every direction; `schedReflInv_canonSched` proves it at `canonSched G`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `1` in `M + 1` the successor of `finMod`; `2k + 1` the extent
index of the torus family; `0` the reflection constant of the field form.
-/

noncomputable section

namespace MassGap.ReflInvG

open MeasureTheory MassGap.CompactGauge MassGap.GaugeGroup

/-! ## 1. The reflection on the finite periodic lattice -/

section Finite

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {d n : ℕ} [NeZero n]

/-- **The coordinate map of the reflection**: the group inverse on links along `τ`, the identity on
the others.

DERIVED: no numeral. -/
def axisDaggerG (τ : Fin d) : MassGap.WilsonHypercubic.Link d n → G → G :=
  fun l u => if l.1 = τ then u⁻¹ else u

omit [NeZero n] in
/-- Each coordinate map `axisDaggerG τ l` preserves `probHaar G`: it is inversion
(`Reflect.isInvInvariant_probHaar`) or the identity.

DERIVED: no numeral. -/
theorem axisDaggerG_measurePreserving (τ : Fin d) (l : MassGap.WilsonHypercubic.Link d n) :
    MeasurePreserving (axisDaggerG (G := G) τ l) (probHaar G) (probHaar G) := by
  by_cases h : l.1 = τ
  · have hinv : axisDaggerG (G := G) τ l = fun u => u⁻¹ := by
      funext u
      simp [axisDaggerG, h]
    rw [hinv]
    exact Measure.measurePreserving_inv (probHaar G)
  · have hid : axisDaggerG (G := G) τ l = id := by
      funext u
      simp [axisDaggerG, h]
    rw [hid]
    exact MeasurePreserving.id _

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- `reflConf τ c = twist (reflLinkPerm τ c) (axisDaggerG τ)`, by `rfl`.

DERIVED: no numeral. -/
theorem reflConf_eq_twistG (τ : Fin d) (c : Fin n) :
    MassGap.Reflect.reflConf (G := G) (d := d) (n := n) τ c
      = MassGap.ActionSplit.twist (MassGap.Reflect.reflLinkPerm τ c) (axisDaggerG τ) := by
  funext U
  rfl

/-- **The reflection preserves the product Haar measure of `G`**: `ActionSplit.twist_measurePreserving`
at `reflConf_eq_twistG`.

DERIVED: no numeral. -/
theorem reflConf_measurePreservingG (τ : Fin d) (c : Fin n) :
    MeasurePreserving (MassGap.Reflect.reflConf (G := G) (d := d) (n := n) τ c)
      (MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link d n) (probHaar G))
      (MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link d n) (probHaar G)) := by
  rw [reflConf_eq_twistG]
  exact MassGap.ActionSplit.twist_measurePreserving (probHaar G) _ _
    (fun l => axisDaggerG_measurePreserving τ l)

/-- `reflConf τ c` as a measurable equivalence, its own inverse (`Reflect.reflConf_involutive`).

DERIVED: no numeral. -/
def reflConfEquivG (τ : Fin d) (c : Fin n) :
    (MassGap.WilsonHypercubic.Link d n → G) ≃ᵐ (MassGap.WilsonHypercubic.Link d n → G) where
  toFun := MassGap.Reflect.reflConf τ c
  invFun := MassGap.Reflect.reflConf τ c
  left_inv := MassGap.Reflect.reflConf_involutive τ c
  right_inv := MassGap.Reflect.reflConf_involutive τ c
  measurable_toFun := (reflConf_measurePreservingG (G := G) τ c).measurable
  measurable_invFun := (reflConf_measurePreservingG (G := G) τ c).measurable

/-- **The Wilson Gibbs expectation of `G` is invariant under every reflection**:
`EWG G β (O ∘ reflConf τ c) = EWG G β O`, at every real `β` and every observable `O`.

DERIVED: no numeral. -/
theorem expect_reflect_invariantG (τ : Fin d) (c : Fin n) (β : ℝ)
    (O : (MassGap.WilsonHypercubic.Link d n → G) → ℝ) :
    GaugeWilson.EWG G (d := d) (n := n) β (fun U => O (MassGap.Reflect.reflConf τ c U))
      = GaugeWilson.EWG G (d := d) (n := n) β O :=
  MassGap.LatticeGauge.System.expect_invariant_of_mp (GaugeWilson.sysWilsonG G d n)
    (probHaar G) β O (reflConfEquivG τ c) (reflConf_measurePreservingG τ c)
    (fun U => by
      show (GaugeWilson.sysWilsonG G d n).boltz β (MassGap.Reflect.reflConf τ c U)
        = (GaugeWilson.sysWilsonG G d n).boltz β U
      unfold MassGap.LatticeGauge.System.boltz
      rw [MassGap.ShiftInvG.reflect_action_invariantG])

end Finite

/-! ## 2. The torus states and their limits -/

section Torus

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- `ireflConf τ c (pullback M W) = pullback M (reflConf τ (finMod M c) W)`, over any `G`.

DERIVED: `4` the dimension; `1` in `M + 1` the successor of `finMod`. -/
theorem pullback_ireflConfG (M : ℕ) (τ : Fin 4) (c : ℤ)
    (W : MassGap.WilsonHypercubic.Link 4 (M + 1) → G) :
    MassGap.LatticeReflection.ireflConf τ c (MassGap.InfiniteLattice.pullback M W)
      = MassGap.InfiniteLattice.pullback M
          (MassGap.Reflect.reflConf τ (MassGap.InfiniteLattice.finMod M c) W) := by
  funext l
  show (if l.1 = τ
      then (W (MassGap.InfiniteLattice.linkMod M (MassGap.LatticeReflection.ireflLink τ c l)))⁻¹
      else W (MassGap.InfiniteLattice.linkMod M (MassGap.LatticeReflection.ireflLink τ c l)))
    = (if (MassGap.InfiniteLattice.linkMod M l).1 = τ
        then (W (MassGap.Reflect.reflLink τ (MassGap.InfiniteLattice.finMod M c)
          (MassGap.InfiniteLattice.linkMod M l)))⁻¹
        else W (MassGap.Reflect.reflLink τ (MassGap.InfiniteLattice.finMod M c)
          (MassGap.InfiniteLattice.linkMod M l)))
  rw [MassGap.PeriodicState.linkMod_ireflLink]
  rfl

/-- `torusObsG G M (θ_c f)` is `torusObsG G M f` precomposed with the periodic reflection about
`finMod M c`.

DERIVED: `4` the dimension. -/
theorem torusObsG_refl (M : ℕ) (τ : Fin 4) (c : ℤ) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    GaugeWilson.torusObsG G M ((MassGap.LatticeReflection.latticeReflection (G := G) τ c).θ f)
      = fun W => GaugeWilson.torusObsG G M f
          (MassGap.Reflect.reflConf τ (MassGap.InfiniteLattice.finMod M c) W) := by
  funext W
  show f (MassGap.LatticeReflection.ireflConf τ c (MassGap.InfiniteLattice.pullback M W))
    = f (MassGap.InfiniteLattice.pullback M
        (MassGap.Reflect.reflConf τ (MassGap.InfiniteLattice.finMod M c) W))
  rw [pullback_ireflConfG]

/-- `torusObsG G M (θ_c f * f) = fun W => torusObsG G M f W * torusObsG G M f (reflConf τ (finMod M c) W)`.

DERIVED: `4` the dimension. -/
theorem torusObsG_refl_mul (M : ℕ) (τ : Fin 4) (c : ℤ) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    GaugeWilson.torusObsG G M
        ((MassGap.LatticeReflection.latticeReflection (G := G) τ c).θ f * f)
      = fun W => GaugeWilson.torusObsG G M f W * GaugeWilson.torusObsG G M f
          (MassGap.Reflect.reflConf τ (MassGap.InfiniteLattice.finMod M c) W) := by
  funext W
  show f (MassGap.LatticeReflection.ireflConf τ c (MassGap.InfiniteLattice.pullback M W))
      * f (MassGap.InfiniteLattice.pullback M W)
    = f (MassGap.InfiniteLattice.pullback M W) * f (MassGap.InfiniteLattice.pullback M
        (MassGap.Reflect.reflConf τ (MassGap.InfiniteLattice.finMod M c) W))
  rw [pullback_ireflConfG, mul_comm]

/-- **Every torus state of `G` is reflection invariant about every constant**:
`IsReflectionInvariant (latticeReflection τ c) (torusStateG G M β)` for every `τ` and `c : ℤ`.

DERIVED: `4` the dimension. -/
theorem torusStateG_reflInvariant (M : ℕ) (β : ℝ) (τ : Fin 4) (c : ℤ) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := G) τ c)
      (GaugeWilson.torusStateG G M β) := by
  intro f
  show GaugeWilson.EWG G (d := 4) (n := M + 1) β
      (GaugeWilson.torusObsG G M ((MassGap.LatticeReflection.latticeReflection (G := G) τ c).θ f))
    = GaugeWilson.EWG G (d := 4) (n := M + 1) β (GaugeWilson.torusObsG G M f)
  rw [torusObsG_refl]
  exact expect_reflect_invariantG τ (MassGap.InfiniteLattice.finMod M c) β
    (GaugeWilson.torusObsG G M f)

/-- **Every limit of the torus states of `G` along a non-trivial filter is reflection invariant about
every constant.**

DERIVED: `2k + 1` the extent index; `4` the dimension. -/
theorem reflInvariant_of_tendsto_torusG (β : ℝ) (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G)) {l : Filter ℕ} [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      Filter.Tendsto (fun k : ℕ => GaugeWilson.torusStateG G (2 * k + 1) β f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := G) τ c) ν :=
  MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun k => torusStateG_reflInvariant G (2 * k + 1) β τ c))

/-- **`periodicStateG G β` is reflection invariant about every constant `c`, in every direction `τ`**,
at every real `β`: the mirror of `PeriodicState.periodicState_reflInvariant`.

DERIVED: `4` the dimension. -/
theorem periodicStateG_reflInvariant (β : ℝ) (τ : Fin 4) (c : ℤ) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := G) τ c)
      (GaugeWilson.periodicStateG G β) := by
  haveI : (((GaugeWilson.exists_periodic_limit_dvdG G β).choose : Ultrafilter ℕ) :
      Filter ℕ).NeBot := (GaugeWilson.exists_periodic_limit_dvdG G β).choose.neBot'
  exact reflInvariant_of_tendsto_torusG G β τ c (GaugeWilson.periodicStateG G β)
    (MassGap.ShiftInvG.tendsto_periodicStateG G β)

end Torus

/-! ## 3. Reflection invariance over a schedule -/

section Sched

open MassGap.ClayTreeG MassGap.ContinuumField

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A schedule whose states are reflection invariant**: the state of every step is invariant under
the reflection about every constant `c : ℤ` in every direction `τ`.

DERIVED: `4` the dimension. -/
def SchedReflInv (S : Sched G) : Prop :=
  ∀ (k : ℕ) (τ : Fin 4) (c : ℤ),
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := G) τ c) (S.ν k)

/-- **The canonical schedule of `G` is reflection invariant**: `SchedReflInv (canonSched G)`, from
`periodicStateG_reflInvariant` at the coupling `dyBetaG G k` of each step.

DERIVED: no numeral. -/
theorem schedReflInv_canonSched [GaugeSimple G] : SchedReflInv (canonSched G) :=
  fun k τ c => periodicStateG_reflInvariant G (dyBetaG G k) τ c

/-- **The field form over a reflection-invariant schedule**: `S.ν k (O.refl τ).1 = S.ν k O.1`.

DERIVED: `0` the reflection constant of `LField.refl`. -/
theorem sched_refl_field {S : Sched G} (hS : SchedReflInv S) (k : ℕ) (τ : Fin 4) (O : LField G) :
    S.ν k (O.refl τ).1 = S.ν k O.1 :=
  hS k τ 0 O.1

/-- **The field form at the canonical schedule**, the mirror of `ContinuumFlow.stateK_refl_field`:
`(canonSched G).ν k (O.refl τ).1 = (canonSched G).ν k O.1`.

DERIVED: no numeral. -/
theorem canonSched_refl_field [GaugeSimple G] (k : ℕ) (τ : Fin 4) (O : LField G) :
    (canonSched G).ν k (O.refl τ).1 = (canonSched G).ν k O.1 :=
  sched_refl_field schedReflInv_canonSched k τ O

end Sched

end MassGap.ReflInvG

end

#print axioms MassGap.ReflInvG.axisDaggerG_measurePreserving
#print axioms MassGap.ReflInvG.reflConf_measurePreservingG
#print axioms MassGap.ReflInvG.reflConfEquivG
#print axioms MassGap.ReflInvG.expect_reflect_invariantG
#print axioms MassGap.ReflInvG.pullback_ireflConfG
#print axioms MassGap.ReflInvG.torusObsG_refl
#print axioms MassGap.ReflInvG.torusObsG_refl_mul
#print axioms MassGap.ReflInvG.torusStateG_reflInvariant
#print axioms MassGap.ReflInvG.reflInvariant_of_tendsto_torusG
#print axioms MassGap.ReflInvG.periodicStateG_reflInvariant
#print axioms MassGap.ReflInvG.schedReflInv_canonSched
#print axioms MassGap.ReflInvG.sched_refl_field
#print axioms MassGap.ReflInvG.canonSched_refl_field
