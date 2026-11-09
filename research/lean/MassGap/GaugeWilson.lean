import Mathlib
import MassGap.GaugeInstances
import MassGap.CompactGauge
import MassGap.WilsonHypercubic
import MassGap.ReflectPositive
import MassGap.GibbsSpec
import MassGap.InfiniteLattice
import MassGap.DLRLimit
import MassGap.PeriodicState

/-!
# MassGap.GaugeWilson — the Wilson lattice measure over a `GaugeGroup`, and its `SU(N)` specialisation

The `SU(N)` lattice measures of the tree are built in four layers, each from the one below:

1. the finite hypercubic system `WilsonHypercubic.sysWilson N d n` and its Gibbs expectation
   `ReflectPositive.EW N β`, against product Haar `probHaar (SU N)`;
2. the expectation as a positive normalised linear functional (`WilsonReal.wilsonSystem_expect_*`);
3. the periodic Wilson state on `ℤ⁴` observables, `PeriodicState.torusState hN M β`;
4. the infinite-volume periodic state `PeriodicState.periodicState hN β`, an ultrafilter limit of
   the torus states over dyadic extents; `ContinuumSchwinger.stateK` is it at the coupling of step
   `k`.

and the infinite-volume specification `GibbsSpec.spec` with its DLR consistency at the Wilson
density (`GibbsSpec.wilson_dlr_consistent`).

This module states each layer for an arbitrary `GaugeGroup G` (`sysWilsonG`, `EWG`, the
`wilsonSystemG_*` functional facts, `torusStateG`, `periodicStateG`, `wilsonG_dlr_consistent`) and
proves that at `G = SU N` each is the existing `SU(N)` object: `sysWilsonG_SU`, `EWG_SU`,
`torusStateG_SU` and `periodicStateG_SU` are `rfl`, and the DLR statement is the same `Prop`
(`dlrConsistent_SU`). So a theorem proved about the `SU(N)` objects is, verbatim, a theorem about the
generic objects at `SU N`; porting it means restating it with `G` for `SU N` and replaying its proof
against the generic lemmas here, which carry no `N ≠ 0` hypothesis because `GaugeGroup` has
`repDim_pos`.

The layer-2 proofs are the `WilsonReal` proofs with `wilsonDensity_nonneg hN` / `_le_two hN`
replaced by `wilsonDensityG_nonneg` / `_le_two`; layer 4 is `DLRLimit.exists_limit_state`, which
never read the group.

The three copies of the `ℤ⁴` lattice types (`GibbsSpec`, `InfiniteLattice`, `DLRLimit`) are
reducible abbreviations of the same terms; `iconf_gibbs_eq_infinite` and the lines beside it record
that they, and the two boundary words `GibbsSpec.ibd` and `InfiniteLattice.ibd`, agree by `rfl`.
-/

namespace MassGap.GaugeWilson

open MeasureTheory MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge
open MassGap.GaugeGroup

/-! ## The three copies of the `ℤ⁴` lattice types -/

theorem isite_gibbs_eq_infinite : MassGap.GibbsSpec.ISite = MassGap.InfiniteLattice.ISite := rfl
theorem isite_gibbs_eq_dlr : MassGap.GibbsSpec.ISite = MassGap.DLRLimit.ISite := rfl
theorem ilink_gibbs_eq_infinite : MassGap.GibbsSpec.ILink = MassGap.InfiniteLattice.ILink := rfl
theorem ilink_gibbs_eq_dlr : MassGap.GibbsSpec.ILink = MassGap.DLRLimit.ILink := rfl
theorem iplaq_gibbs_eq_infinite : MassGap.GibbsSpec.IPlaq = MassGap.InfiniteLattice.IPlaq := rfl
theorem iplaq_gibbs_eq_dlr : MassGap.GibbsSpec.IPlaq = MassGap.DLRLimit.IPlaq := rfl
theorem iconf_gibbs_eq_infinite (G : Type) :
    MassGap.GibbsSpec.IConf G = MassGap.InfiniteLattice.IConf G := rfl
theorem iconf_gibbs_eq_dlr (G : Type) : MassGap.GibbsSpec.IConf G = MassGap.DLRLimit.IConf G := rfl
theorem ishift_gibbs_eq_infinite : MassGap.GibbsSpec.ishift = MassGap.InfiniteLattice.ishift := rfl
theorem ibd_gibbs_eq_infinite : MassGap.GibbsSpec.ibd = MassGap.InfiniteLattice.ibd := rfl

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## Layer 1: the finite hypercubic system -/

/-- The hypercubic Wilson system over `G`: the boundary words of `WilsonHypercubic.bd` and the
density `wilsonDensityG G`.

DERIVED: no numeral. -/
noncomputable def sysWilsonG (d n : ℕ) [NeZero n] : System G :=
  wilsonSystem (G := G) (MassGap.WilsonHypercubic.bd (d := d) (n := n)) (wilsonDensityG G)

theorem sysWilsonG_SU (N d n : ℕ) [NeZero N] [NeZero n] :
    sysWilsonG (MassGap.SUN.SU N) d n = MassGap.WilsonHypercubic.sysWilson N d n := rfl

/-- The hypercubic Gibbs expectation over `G` against product `probHaar G`.

DERIVED: no numeral. -/
noncomputable def EWG {d n : ℕ} [NeZero n] (β : ℝ)
    (O : (wilsonSystem (MassGap.WilsonHypercubic.bd (d := d) (n := n))
      (wilsonDensityG G)).Config → ℝ) : ℝ :=
  (wilsonSystem (MassGap.WilsonHypercubic.bd (d := d) (n := n)) (wilsonDensityG G)).expect
    (probHaar G) β O

theorem EWG_SU (N : ℕ) [NeZero N] {d n : ℕ} [NeZero n] (β : ℝ)
    (O : (MassGap.WilsonHypercubic.Link d n → MassGap.SUN.SU N) → ℝ) :
    EWG (MassGap.SUN.SU N) (d := d) (n := n) β O = MassGap.ReflectPositive.EW N β O := rfl

/-! ## Layer 2: the expectation is a state, at every `GaugeGroup`

`WilsonReal`'s `SU(N)` chain with the hypothesis `N ≠ 0` gone. -/

variable {G}
variable {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

theorem wilsonSystemG_action_nonneg (bd : Pq → List (Lk × Bool))
    (U : (wilsonSystem bd (wilsonDensityG G)).Config) :
    0 ≤ (wilsonSystem bd (wilsonDensityG G)).action U :=
  Finset.sum_nonneg (fun _ _ => wilsonDensityG_nonneg _)

/-- DERIVED: `2` is `wilsonDensityG_le_two`'s bound, times the plaquette count. -/
theorem wilsonSystemG_action_le (bd : Pq → List (Lk × Bool))
    (U : (wilsonSystem bd (wilsonDensityG G)).Config) :
    (wilsonSystem bd (wilsonDensityG G)).action U ≤ 2 * (Fintype.card Pq : ℝ) := by
  have h : (wilsonSystem bd (wilsonDensityG G)).action U ≤ ∑ _p : Pq, (2 : ℝ) :=
    Finset.sum_le_sum (fun _ _ => wilsonDensityG_le_two _)
  have he : (∑ _p : Pq, (2 : ℝ)) = 2 * (Fintype.card Pq : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  linarith

theorem measurable_wilsonSystemG_action (bd : Pq → List (Lk × Bool)) :
    Measurable (wilsonSystem bd (wilsonDensityG G)).action :=
  Finset.measurable_sum _ (fun p _ =>
    measurable_wilsonDensityG.comp (measurable_wilsonHol (G := G) bd p))

theorem measurable_wilsonSystemG_boltz (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    Measurable ((wilsonSystem bd (wilsonDensityG G)).boltz β) :=
  Real.measurable_exp.comp (measurable_const.mul (measurable_wilsonSystemG_action bd))

theorem wilsonSystemG_boltz_pos (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : (wilsonSystem bd (wilsonDensityG G)).Config) :
    0 < (wilsonSystem bd (wilsonDensityG G)).boltz β U := by
  unfold System.boltz; exact Real.exp_pos _

/-- DERIVED: `2` is `wilsonDensityG`'s upper bound, times the plaquette count. -/
theorem wilsonSystemG_boltz_le (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : (wilsonSystem bd (wilsonDensityG G)).Config) :
    (wilsonSystem bd (wilsonDensityG G)).boltz β U
      ≤ Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))) := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : -β * (wilsonSystem bd (wilsonDensityG G)).action U
      ≤ |β| * (wilsonSystem bd (wilsonDensityG G)).action U :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) (wilsonSystemG_action_nonneg bd U)
  have h2 : |β| * (wilsonSystem bd (wilsonDensityG G)).action U
      ≤ |β| * (2 * (Fintype.card Pq : ℝ)) :=
    mul_le_mul_of_nonneg_left (wilsonSystemG_action_le bd U) (abs_nonneg β)
  linarith

instance isProbabilityMeasure_volG (bd : Pq → List (Lk × Bool)) :
    IsProbabilityMeasure ((wilsonSystem bd (wilsonDensityG G)).vol (probHaar G)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Lk => probHaar G)))

theorem wilsonSystemG_partition_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    0 < (wilsonSystem bd (wilsonDensityG G)).partition (probHaar G) β := by
  unfold System.partition
  have hint : Integrable ((wilsonSystem bd (wilsonDensityG G)).boltz β)
      ((wilsonSystem bd (wilsonDensityG G)).vol (probHaar G)) :=
    (integrable_const (Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))))).mono'
      (measurable_wilsonSystemG_boltz bd β).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => by
        rw [Real.norm_of_nonneg (wilsonSystemG_boltz_pos bd β U).le]
        exact wilsonSystemG_boltz_le bd β U))
  rw [integral_pos_iff_support_of_nonneg (fun U => (wilsonSystemG_boltz_pos bd β U).le) hint]
  have hsupp : Function.support ((wilsonSystem bd (wilsonDensityG G)).boltz β) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (wilsonSystemG_boltz_pos bd β U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

/-- DERIVED: `1` is the constant observable and its expectation. -/
theorem wilsonSystemG_expect_one (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β (fun _ => (1 : ℝ)) = 1 := by
  unfold System.expect System.corrNum
  simp only [one_mul]
  exact div_self (wilsonSystemG_partition_pos bd β).ne'

theorem wilsonSystemG_expect_nonneg (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensityG G)).Config → ℝ) (hO : ∀ U, 0 ≤ O U) :
    0 ≤ (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β O := by
  unfold System.expect
  refine div_nonneg ?_ (wilsonSystemG_partition_pos bd β).le
  unfold System.corrNum
  exact integral_nonneg (fun U => mul_nonneg (hO U) (wilsonSystemG_boltz_pos bd β U).le)

theorem wilsonSystemG_expect_smul (bd : Pq → List (Lk × Bool)) (β c : ℝ)
    (O : (wilsonSystem bd (wilsonDensityG G)).Config → ℝ) :
    (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β (fun U => c * O U)
      = c * (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β O := by
  unfold System.expect System.corrNum
  have h : (fun U => (c * O U) * (wilsonSystem bd (wilsonDensityG G)).boltz β U)
      = (fun U => c * (O U * (wilsonSystem bd (wilsonDensityG G)).boltz β U)) := by
    funext U; ring
  rw [h, integral_const_mul, mul_div_assoc]

theorem wilsonSystemG_expect_add (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O O' : (wilsonSystem bd (wilsonDensityG G)).Config → ℝ)
    (hint : Integrable (fun U => O U * (wilsonSystem bd (wilsonDensityG G)).boltz β U)
      ((wilsonSystem bd (wilsonDensityG G)).vol (probHaar G)))
    (hint' : Integrable (fun U => O' U * (wilsonSystem bd (wilsonDensityG G)).boltz β U)
      ((wilsonSystem bd (wilsonDensityG G)).vol (probHaar G))) :
    (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β (fun U => O U + O' U)
      = (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β O
        + (wilsonSystem bd (wilsonDensityG G)).expect (probHaar G) β O' := by
  unfold System.expect System.corrNum
  have h : (fun U => (O U + O' U) * (wilsonSystem bd (wilsonDensityG G)).boltz β U)
      = (fun U => O U * (wilsonSystem bd (wilsonDensityG G)).boltz β U
          + O' U * (wilsonSystem bd (wilsonDensityG G)).boltz β U) := by funext U; ring
  rw [h, integral_add hint hint', add_div]

/-- DERIVED: `M` is the caller's bound. -/
theorem wilsonSystemG_mul_boltz_integrable (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensityG G)).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Integrable (fun U => O U * (wilsonSystem bd (wilsonDensityG G)).boltz β U)
      ((wilsonSystem bd (wilsonDensityG G)).vol (probHaar G)) := by
  refine (integrable_const (M * Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))))).mono'
    ((hmeas.mul (measurable_wilsonSystemG_boltz bd β)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [norm_mul, Real.norm_of_nonneg (wilsonSystemG_boltz_pos bd β U).le]
  have hO : ‖O U‖ ≤ M := by rw [Real.norm_eq_abs]; exact hbound U
  exact mul_le_mul hO (wilsonSystemG_boltz_le bd β U) (wilsonSystemG_boltz_pos bd β U).le
    (le_trans (norm_nonneg _) hO)

/-! ## Layer 3: the periodic Wilson state on `ℤ⁴` observables -/

variable (G)

/-- A continuous `ℤ⁴` observable read on the periodic lattice of extent `M + 1`.

DERIVED: `4` is the spacetime dimension; `1` is `finMod`'s successor. -/
noncomputable def torusObsG (M : ℕ) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    (MassGap.WilsonHypercubic.Link 4 (M + 1) → G) → ℝ :=
  fun W => f (MassGap.InfiniteLattice.pullback M W)

theorem measurable_torusObsG (M : ℕ) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    Measurable (torusObsG G M f) :=
  f.continuous.measurable.comp
    (measurable_pi_lambda _ (fun l => measurable_pi_apply (MassGap.InfiniteLattice.linkMod M l)))

/-- **The periodic Wilson state of extent `M + 1` over `G`**, `f ↦ EWG G β (torusObsG G M f)`.

DERIVED: `4` is the spacetime dimension; `1` is `finMod`'s successor. -/
noncomputable def torusStateG (M : ℕ) (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G) where
  toFun f := EWG G (d := 4) (n := M + 1) β (torusObsG G M f)
  map_add' f g := by
    obtain ⟨Cf, hCf⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
    obtain ⟨Cg, hCg⟩ := MassGap.InfiniteLattice.bounded_of_continuous g.continuous
    exact wilsonSystemG_expect_add (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) β
      (torusObsG G M f) (torusObsG G M g)
      (wilsonSystemG_mul_boltz_integrable _ β _ (measurable_torusObsG G M f) Cf (fun W => hCf _))
      (wilsonSystemG_mul_boltz_integrable _ β _ (measurable_torusObsG G M g) Cg (fun W => hCg _))
  map_smul' c f :=
    wilsonSystemG_expect_smul (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) β c
      (torusObsG G M f)
  nonneg' f hf :=
    wilsonSystemG_expect_nonneg (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) β
      (torusObsG G M f) (fun W => hf _)
  one' := wilsonSystemG_expect_one (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) β

/-- At `SU(N)` the generic torus state is `PeriodicState.torusState`, by `rfl`.

DERIVED: no numeral. -/
theorem torusStateG_SU (N : ℕ) [NeZero N] (M : ℕ) (β : ℝ) :
    torusStateG (MassGap.SUN.SU N) M β = MassGap.PeriodicState.torusState (NeZero.ne N) M β := rfl

/-! ## Layer 4: the infinite-volume periodic state -/

/-- A limit of the periodic states over dyadic extents exists at every coupling, for every
`GaugeGroup`: `DLRLimit.exists_limit_state` (weak-* compactness), as at `SU(N)`.

DERIVED: the extent index `2k + 1` is the even-extent family. -/
theorem exists_periodic_limit_dvdG (β : ℝ) :
    ∃ (u : Ultrafilter ℕ) (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G)),
      (u : Filter ℕ) ≤ MassGap.PeriodicState.dyadicFilter ∧
        ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
          Filter.Tendsto (fun k : ℕ => torusStateG G (2 * k + 1) β f) (u : Filter ℕ)
            (nhds (ν f)) :=
  haveI := MassGap.PeriodicState.dyadicFilter_neBot
  MassGap.DLRLimit.exists_limit_state MassGap.PeriodicState.dyadicFilter
    (fun k : ℕ => torusStateG G (2 * k + 1) β)

/-- **The infinite-volume periodic Wilson state over `G`.**

DERIVED: no numeral. -/
noncomputable def periodicStateG (β : ℝ) : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G) :=
  (exists_periodic_limit_dvdG G β).choose_spec.choose

/-- At `SU(N)` the generic infinite-volume state is `PeriodicState.periodicState`, by `rfl`: the
existence statements agree definitionally (`torusStateG_SU`), so the two choices are one.

DERIVED: no numeral. -/
theorem periodicStateG_SU (N : ℕ) [NeZero N] (β : ℝ) :
    periodicStateG (MassGap.SUN.SU N) β = MassGap.PeriodicState.periodicState (NeZero.ne N) β :=
  rfl

/-! ## The infinite-volume specification -/

/-- The Wilson specification over `G` is DLR-consistent at every coupling.

DERIVED: the `[0, 2]` range of `wilsonDensityG` is `GibbsSpec.dlr_consistent`'s hypothesis. -/
theorem wilsonG_dlr_consistent (β : ℝ) :
    MassGap.GibbsSpec.DLRConsistent (wilsonDensityG G) β (probHaar G) :=
  MassGap.GibbsSpec.dlr_consistent measurable_wilsonDensityG wilsonDensityG_nonneg
    wilsonDensityG_le_two β _

theorem wilsonG_part_pos (β : ℝ) (Λ : Finset MassGap.GibbsSpec.ILink)
    (ω : MassGap.GibbsSpec.IConf G) :
    0 < MassGap.GibbsSpec.part (wilsonDensityG G) β Λ (probHaar G) ω :=
  MassGap.GibbsSpec.part_pos measurable_wilsonDensityG wilsonDensityG_nonneg
    wilsonDensityG_le_two β Λ _ ω

/-- At `SU(N)` the generic DLR statement is the `SU(N)` one.

DERIVED: no numeral. -/
theorem dlrConsistent_SU (N : ℕ) [NeZero N] (β : ℝ) :
    MassGap.GibbsSpec.DLRConsistent (wilsonDensityG (MassGap.SUN.SU N)) β
        (probHaar (MassGap.SUN.SU N))
      = MassGap.GibbsSpec.DLRConsistent (MassGap.WilsonAction.wilsonDensity (N := N)) β
        (probHaar (MassGap.SUN.SU N)) := rfl

/-! ## The other instances -/

/-- The periodic infinite-volume Wilson states (ultrafilter limits of torus states) exist for compact
`Sp(n)` and `SO(n)` as well, at every coupling; the Wilson specification is DLR-consistent there. That
these states satisfy the DLR equations is not proved here.

DERIVED: no numeral. -/
noncomputable def periodicStateUSp (n : ℕ) [NeZero n] (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.GaugeInstances.USp n)) :=
  periodicStateG _ β

noncomputable def periodicStateSO (n : ℕ) [NeZero n] (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.GaugeInstances.SO n)) :=
  periodicStateG _ β

theorem dlr_consistent_USp (n : ℕ) [NeZero n] (β : ℝ) :
    MassGap.GibbsSpec.DLRConsistent (wilsonDensityG (MassGap.GaugeInstances.USp n)) β
      (probHaar (MassGap.GaugeInstances.USp n)) :=
  wilsonG_dlr_consistent _ β

theorem dlr_consistent_SO (n : ℕ) [NeZero n] (β : ℝ) :
    MassGap.GibbsSpec.DLRConsistent (wilsonDensityG (MassGap.GaugeInstances.SO n)) β
      (probHaar (MassGap.GaugeInstances.SO n)) :=
  wilsonG_dlr_consistent _ β

#print axioms sysWilsonG_SU
#print axioms EWG_SU
#print axioms wilsonSystemG_partition_pos
#print axioms torusStateG
#print axioms torusStateG_SU
#print axioms periodicStateG_SU
#print axioms wilsonG_dlr_consistent
#print axioms dlrConsistent_SU

end MassGap.GaugeWilson
