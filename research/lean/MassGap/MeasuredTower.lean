import Mathlib
import MassGap.ClayTreeG
import MassGap.FocusZoom

/-!
# MassGap.MeasuredTower — the measured tower over a compact simple group `G`

The objects through which the target statement (`ClayStatementG.ClayStatementOf`) selects the coupling of each
step of its construction. Declarations are in the namespace `MassGap.MeasuredTower`.

* **The measured read over `G`.** `DecaysAtG`, `measMassOfG`: the decay rate of a reading's connected correlation
  in a state of `G`, and its supremum, in `[0, ∞]`. `tensorEnergyG G x`: the `(0, 1)`-plaquette density minus the
  `(2, 3)`-plaquette density of `plaqFieldG`. `measLenG G ν` (the measured spacing `1/ξ` at unit physical mass) is
  positive exactly at a finite lock (`measLenG_pos_iff`) and `0` exactly at the two degenerate reads
  (`measLenG_eq_zero_iff`). `mUG G β`: the tensor mass of the periodic Wilson state of `G` at `β`, in lattice units;
  `measSpacingG G β` its real value.
* **`UnitLockG G`**: `m′(β) → 0` and eventually `0 < m′(β)`. Under it `measSpacingG → 0` and is eventually
  positive.
* **`BandG G c k β`**: `ofReal (c a_k) ≤ m′(β) ≤ ofReal (2c a_k)`, `a_k = dySpacingG G k`. `MeasTowerG G βs`:
  `βs → ∞`, and some unit `c > 0` has `BandG G c k (βs k)` eventually. The band is the lock (`BandG.pos`,
  `BandG.ne_top`). Along a tower: `c a_k ≤ measSpacingG(βs k) ≤ 2c a_k` (`BandG.spacing`); the tensor channel's
  physical mass `measSpacingG/a_k ∈ [c, 2c]` (`MeasTowerG.physMass`); `measSpacingG(βs k) → 0`; the unit tie with
  constant `c` in the step's own spacing (`MeasTowerG.unitTie`).
* **`MeasSweepG G`**: one unit `c` with every band reached by couplings beyond any `B`; it gives a tower
  (`exists_measTowerG`).
* **`schedAlongG G βs : Sched G`**: spacing `dySpacingG G`, state `periodicStateG G (βs k)`;
  `canonSched G = schedAlongG G (dyBetaG G)` (`canonSched_eq_schedAlongG`, `rfl`).
* **`AsymScalingG G R`**: `measSpacingG(dyBetaG k)/a_k → R ∈ (0, ∞)`, asymptotic scaling of the tensor mass
  along the canonical schedule.

`snormG` is the sup-norm of a site (`StrongFiniteSize.snorm`, restated here so that the module reads only
`ClayTreeG` and `FocusZoom`).

DERIVED (module-wide): `2` the dyadic ratio; `0` the limits and the signs; `4` the dimension; `1` a finite
bound; `0`, `1`, `2`, `3` the two planes of the tensor reading.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.MeasuredTower

open Filter Topology
open scoped ENNReal NNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG
open MassGap.DLRLimit (State)

/-- **The sup-norm of a site.** DERIVED: `4` the dimension. -/
def snormG (x : ISite) : ℕ := Finset.univ.sup fun i : Fin 4 => (x i).natAbs

/-! ## 1. The measured read over `G` -/

section MeasuredG

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Decay at rate `m`** of a reading in a state of `G`. DERIVED: no numeral. -/
def DecaysAtG (ν : State (MassGap.GibbsSpec.IConf G)) (E : ISite → C(MassGap.GibbsSpec.IConf G, ℝ)) (m : ℝ) :
    Prop :=
  ∃ C : ℝ, ∀ x z : ISite, |FocusZoom.stateCov ν (E x) (E (x + z))|
    ≤ C * Real.exp (-(m * snormG z))

/-- **The measured mass of a reading** of `G`: the supremum of its decay rates, in `[0, ∞]`.
DERIVED: no numeral. -/
def measMassOfG (ν : State (MassGap.GibbsSpec.IConf G)) (E : ISite → C(MassGap.GibbsSpec.IConf G, ℝ)) :
    ℝ≥0∞ :=
  ⨆ (m : ℝ≥0) (_ : DecaysAtG G ν E m), (m : ℝ≥0∞)

/-- **The tensor reading of `G`**: the `(0, 1)`-plaquette density minus the `(2, 3)`-plaquette density at `x`.
DERIVED: `0`, `1`, `2`, `3` the two planes. -/
def tensorEnergyG (x : ISite) : C(MassGap.GibbsSpec.IConf G, ℝ) :=
  (plaqFieldG (G := G) (((0 : Fin 4), (1 : Fin 4)), x)).1
    - (plaqFieldG (G := G) (((2 : Fin 4), (3 : Fin 4)), x)).1

/-- **The measured spacing of a capture at unit physical mass**: `1/ξ`. DERIVED: no numeral. -/
def measLenG (ν : State (MassGap.GibbsSpec.IConf G)) : ℝ := (measMassOfG G ν (tensorEnergyG G)).toReal

/-- **The measured spacing is positive exactly at a finite, locking read.** DERIVED: `0` the sign. -/
theorem measLenG_pos_iff (ν : State (MassGap.GibbsSpec.IConf G)) :
    0 < measLenG G ν ↔ 0 < measMassOfG G ν (tensorEnergyG G) ∧ measMassOfG G ν (tensorEnergyG G) ≠ ⊤ := by
  unfold measLenG
  rw [ENNReal.toReal_pos_iff, lt_top_iff_ne_top]

/-- **The two degenerate reads give spacing `0`.** DERIVED: `0` the value. -/
theorem measLenG_eq_zero_iff (ν : State (MassGap.GibbsSpec.IConf G)) :
    measLenG G ν = 0 ↔ measMassOfG G ν (tensorEnergyG G) = 0 ∨ measMassOfG G ν (tensorEnergyG G) = ⊤ :=
  ENNReal.toReal_eq_zero_iff _

/-- **A vanishing correlation reads infinite mass.** DERIVED: `0` the vanishing correlation. -/
theorem measMassOfG_top_of_cov_zero {ν : State (MassGap.GibbsSpec.IConf G)}
    {E : ISite → C(MassGap.GibbsSpec.IConf G, ℝ)}
    (h : ∀ x z : ISite, FocusZoom.stateCov ν (E x) (E (x + z)) = 0) : measMassOfG G ν E = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  have hd : DecaysAtG G ν E r := ⟨0, fun x z => by rw [h, abs_zero, zero_mul]⟩
  unfold measMassOfG
  exact le_iSup₂ (f := fun (m : ℝ≥0) (_ : DecaysAtG G ν E m) => (m : ℝ≥0∞)) r hd

/-- **The unit read along the coupling family of `G`.** DERIVED: no numeral. -/
def mUG (β : ℝ) : ℝ≥0∞ := measMassOfG G (GaugeWilson.periodicStateG G β) (tensorEnergyG G)

/-- **The measured spacing along the coupling family of `G`.** DERIVED: no numeral. -/
def measSpacingG (β : ℝ) : ℝ := (mUG G β).toReal

/-- **The unit lock**: the unit mass tends to `0` and is eventually positive. DERIVED: `0` the limit and the
threshold. -/
def UnitLockG : Prop := Tendsto (mUG G) atTop (𝓝 0) ∧ ∀ᶠ β in atTop, 0 < mUG G β

end MeasuredG

/-! ## 2. The measured tower -/

section Tower

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-- **The band of step `k` at unit `c`**: the measured unit mass at `β` lies in `[c a_k, 2c a_k]`.
DERIVED: `2` the dyadic ratio. -/
def BandG (c : ℝ) (k : ℕ) (β : ℝ) : Prop :=
  ENNReal.ofReal (c * dySpacingG G k) ≤ mUG G β ∧ mUG G β ≤ ENNReal.ofReal (2 * c * dySpacingG G k)

/-- **A measured tower**: couplings tending to infinity and one unit `c > 0` such that the measured unit mass is
eventually in the band of its step. DERIVED: `0` the sign of the unit. -/
def MeasTowerG (βs : ℕ → ℝ) : Prop :=
  Tendsto βs atTop atTop ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, BandG G c k (βs k)

variable {G}

/-- DERIVED: `0` the sign. -/
theorem BandG.pos {c : ℝ} (hc : 0 < c) {k : ℕ} {β : ℝ} (h : BandG G c k β) : 0 < mUG G β :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (mul_pos hc (dySpacingG_pos G k))) h.1

/-- DERIVED: no numeral. -/
theorem BandG.ne_top {c : ℝ} {k : ℕ} {β : ℝ} (h : BandG G c k β) : mUG G β ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.2

/-- **In the band the measured spacing is within `[c a_k, 2c a_k]`.** DERIVED: `2` the ratio. -/
theorem BandG.spacing {c : ℝ} (hc : 0 < c) {k : ℕ} {β : ℝ} (h : BandG G c k β) :
    c * dySpacingG G k ≤ measSpacingG G β ∧ measSpacingG G β ≤ 2 * c * dySpacingG G k := by
  have ha := dySpacingG_pos G k
  constructor
  · have h1 := ENNReal.toReal_mono h.ne_top h.1
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  · have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1

/-- **The tower locks**: eventually the unit read is positive and finite. DERIVED: `0` the sign. -/
theorem MeasTowerG.lock {βs : ℕ → ℝ} (h : MeasTowerG G βs) :
    ∀ᶠ k in atTop, 0 < mUG G (βs k) ∧ mUG G (βs k) ≠ ⊤ := by
  obtain ⟨c, hc, hb⟩ := h.2
  exact hb.mono fun _ hk => ⟨hk.pos hc, hk.ne_top⟩

/-- **The physical unit mass of the tower is in `[c, 2c]`.** DERIVED: `2` the band. -/
theorem MeasTowerG.physMass {βs : ℕ → ℝ} (h : MeasTowerG G βs) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, c ≤ measSpacingG G (βs k) / dySpacingG G k
      ∧ measSpacingG G (βs k) / dySpacingG G k ≤ 2 * c := by
  obtain ⟨c, hc, hb⟩ := h.2
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb] with k hk
  have ha := dySpacingG_pos G k
  obtain ⟨h1, h2⟩ := hk.spacing hc
  exact ⟨(le_div_iff₀ ha).mpr h1, (div_le_iff₀ ha).mpr h2⟩

/-- **Along the tower the measured spacing tends to `0`.** DERIVED: `0` the limit; `2` the band. -/
theorem MeasTowerG.tendsto_measSpacing {βs : ℕ → ℝ} (h : MeasTowerG G βs) :
    Tendsto (fun k => measSpacingG G (βs k)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hb⟩ := h.2
  have h2 : Tendsto (fun k => 2 * c * dySpacingG G k) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacingG G).const_mul (2 * c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun k => ENNReal.toReal_nonneg) ?_
  filter_upwards [hb] with k hk using (hk.spacing hc).2

/-- **On a measured tower the unit tie holds**, with the tower's unit, in the step's own spacing. DERIVED: no
numeral. -/
theorem MeasTowerG.unitTie {βs : ℕ → ℝ} (h : MeasTowerG G βs) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ k in atTop, ENNReal.ofReal (c₁ * dySpacingG G k) ≤ mUG G (βs k) := by
  obtain ⟨c, hc, hb⟩ := h.2
  exact ⟨c, hc, hb.mono fun _ hk => hk.1⟩

variable (G)

/-! ### Existence -/

/-- **The measured mass sweeps every band**: one unit `c > 0` such that for every `B`, eventually in `k`, some
coupling `β ≥ B` is in the band of `k`. DERIVED: `0` the sign of the unit. -/
def MeasSweepG : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, ∀ᶠ k in atTop, ∃ β : ℝ, B ≤ β ∧ BandG G c k β

/-- **A sweep gives a measured tower.** DERIVED: `0` the first index and the default coupling. -/
theorem exists_measTowerG (h : MeasSweepG G) : ∃ βs : ℕ → ℝ, MeasTowerG G βs := by
  obtain ⟨c, hc, h⟩ := h
  have hK : ∀ j : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ∃ β : ℝ, (j : ℝ) ≤ β ∧ BandG G c k β :=
    fun j => eventually_atTop.mp (h j)
  choose K hK using hK
  have hJspec : ∀ k, K 0 ≤ k → K (Nat.findGreatest (fun j => K j ≤ k) k) ≤ k := fun k hk =>
    Nat.findGreatest_spec (P := fun j => K j ≤ k) (Nat.zero_le k) hk
  have hJle : ∀ j k, j ≤ k → K j ≤ k → j ≤ Nat.findGreatest (fun j => K j ≤ k) k :=
    fun j k h1 h2 => Nat.le_findGreatest (P := fun j => K j ≤ k) h1 h2
  have hsel : ∀ k, ∃ β : ℝ, K 0 ≤ k →
      ((Nat.findGreatest (fun j => K j ≤ k) k : ℝ) ≤ β ∧ BandG G c k β) := by
    intro k
    by_cases hk : K 0 ≤ k
    · obtain ⟨β, hβ⟩ := hK _ k (hJspec k hk)
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose βs hβs using hsel
  refine ⟨βs, ?_, c, hc, ?_⟩
  · refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (max (K 0) (max ⌈b⌉₊ (K ⌈b⌉₊)))] with k hk
    have h0 : K 0 ≤ k := le_trans (le_max_left _ _) hk
    have hj1 : ⌈b⌉₊ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hj2 : K ⌈b⌉₊ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have hJ := hJle _ _ hj1 hj2
    calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      _ ≤ (Nat.findGreatest (fun j => K j ≤ k) k : ℝ) := by exact_mod_cast hJ
      _ ≤ βs k := (hβs k h0).1
  · filter_upwards [eventually_ge_atTop (K 0)] with k hk using (hβs k hk).2

/-! ### The schedule along a tower -/

/-- **The schedule along a coupling tower**: spacing `dySpacingG G k`, state `periodicStateG G (βs k)`.
DERIVED: no numeral. -/
def schedAlongG (βs : ℕ → ℝ) : Sched G where
  a := dySpacingG G
  ν := fun k => GaugeWilson.periodicStateG G (βs k)
  a_pos := dySpacingG_pos G
  a_lim := tendsto_dySpacingG G

/-- **The canonical schedule is the schedule along `dyBetaG`.** DERIVED: no numeral. -/
theorem canonSched_eq_schedAlongG : canonSched G = schedAlongG G (dyBetaG G) :=
  rfl

/-- **Asymptotic scaling of the tensor mass along the canonical schedule**: `m′(dyBetaG k)/a_k → R ∈ (0, ∞)`.
DERIVED: `0` the sign of `R`. -/
def AsymScalingG (R : ℝ) : Prop :=
  0 < R ∧ Tendsto (fun k => measSpacingG G (dyBetaG G k) / dySpacingG G k) atTop (𝓝 R)

end Tower

end MassGap.MeasuredTower

end

#print axioms MassGap.MeasuredTower.measLenG_pos_iff
#print axioms MassGap.MeasuredTower.measLenG_eq_zero_iff
#print axioms MassGap.MeasuredTower.measMassOfG_top_of_cov_zero
#print axioms MassGap.MeasuredTower.BandG.spacing
#print axioms MassGap.MeasuredTower.MeasTowerG.lock
#print axioms MassGap.MeasuredTower.MeasTowerG.physMass
#print axioms MassGap.MeasuredTower.MeasTowerG.tendsto_measSpacing
#print axioms MassGap.MeasuredTower.MeasTowerG.unitTie
#print axioms MassGap.MeasuredTower.exists_measTowerG
#print axioms MassGap.MeasuredTower.canonSched_eq_schedAlongG
