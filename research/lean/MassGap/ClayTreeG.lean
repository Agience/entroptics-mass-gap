import Mathlib
import MassGap.ClayStatement
import MassGap.GaugeRunning
import MassGap.GaugeWilson

/-!
# MassGap.ClayTreeG — the lattice objects `ClayStatement` reads, over a `GaugeGroup`

`ClayStatement.ClayStatementAt` reads the `SU(N)` tree through a fixed list of objects: the state
and spacing of step `k` (`stateK`, `dySpacing`), the configuration flow `ConfFlow`, its energy
density `energy0`, the flowed Schwinger functions (`latSF`, `contSF`, `schwSFM`), the margin
monomials and the linked Euclidean data (`OSDataSLinked`), and the symmetrised plaquette field
`sym (plaqField q0)`. This module states each of them for a `GaugeGroup G`, with the same bodies and
`SU N` replaced by `G`.

## The schedule

`Sched G` is a spacing sequence `a k > 0`, `a k → 0`, and a state `ν k` on `IConf G` per step.
Every object below reads the step only through a schedule. Two schedules are named:

* `canonSched G`: `a k = aRunG G 1 / 2^(k+1)` (`dySpacingG`), `ν k` the infinite-volume periodic
  Wilson state of `G` (`GaugeWilson.periodicStateG`) at the coupling `dyBetaG G k ≥ 1` at which the
  two-loop running spacing of `G` is `a k` (`aRunG_dyBetaG`). Its existence (`exists_couplingG`) uses
  `aRunG_eq`: `aRunG G β = aRun 1 (λ_G β)`, `λ_G = 2T(ρ)/(h^∨ d)`.
* `schedSU N`: `a = dySpacing N`, `ν = stateK`, the schedule of `ClayStatement`.

`canonSched_SU`: at `SU(N)`, `N ≥ 2`, the two are equal.

## The Lie algebra of the plaquette representation

`GaugeLie G` adds to `GaugeSimple G` the predicate `lieGen` on `d × d` complex matrices cutting out
the Hermitian generators `X` of `ρ(𝔤)` (`ρ(exp(tX̃)) = exp(itX)`), and `0 < dim 𝔤`. Like the
constants of `GaugeSimple`, `lieGen` is entered per instance and not derived from `G`: deriving it
from `ρ(G)` at `SU(N)` needs `det ∘ exp = exp ∘ tr` on matrices, which Mathlib does not have. The
instances: `SU(N)`, `N ≥ 2`: Hermitian and traceless; `SO(n)`, `n ≥ 5`, and `SO(3)`: Hermitian and
antisymmetric (`i` times a real antisymmetric matrix); compact `Sp(n)`: Hermitian with
`X J + J Xᵀ = 0`.

## Equality at `SU(N)`

Every object here is, at `G = SU N` and `S = schedSU N`, definitionally the `SU(N)` object it
copies; `ClayStatementG.clayStatementAtP_SU_iff` uses this. The structures `ConfFlowG` and
`OSDataSLinkedG` carry the same fields as `ConfFlow N` and `OSDataSLinked N D τ r`; `ConfFlowG.toSU`,
`ConfFlow.toG`, `OSDataSLinkedG.toSU` and `OSDataSLinked.toG` pass between them field by field.

The flow `energy0 W D hD : Flow N` enters the statement only through its map; `energyMapG` is that
map.
-/

noncomputable section

namespace MassGap.ClayTreeG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial Filter
open scoped Topology Matrix

/-! ## 1. The Lie algebra of the plaquette representation -/

/-- **The Hermitian generators of `ρ(𝔤)`** as a predicate on `d × d` complex matrices, and the
positivity of `dim 𝔤`. Entered per instance, like the constants of `GaugeSimple`.

DERIVED: `0` the positivity every simple Lie algebra has. -/
class GaugeLie (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    [GaugeSimple G] where
  /-- The Hermitian generators of the plaquette representation's Lie algebra. -/
  lieGen : Matrix (Fin (GaugeGroup.dim G)) (Fin (GaugeGroup.dim G)) ℂ → Prop
  lieDim_pos : 0 < GaugeSimple.lieDim (G := G)

/-- `SU(N)`, `N ≥ 2`: Hermitian traceless matrices, `N² − 1 > 0`.

DERIVED: `0` the trace; `2` the least `N`; `4 = 2²`. -/
instance instGaugeLieSU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] : GaugeLie (MassGap.SUN.SU N) where
  lieGen M := M.IsHermitian ∧ M.trace = 0
  lieDim_pos := by
    have h2 : 2 ≤ N := Fact.out
    show 0 < N ^ 2 - 1
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    omega

/-- `SO(n)`, `n ≥ 5`: Hermitian antisymmetric matrices, `i` times `so(n)`; `n(n−1)/2 > 0`.

DERIVED: `5` the least `n` of `instGaugeSimpleSO`; `4 = 5 − 1`; `2` the halving. -/
instance instGaugeLieSO (n : ℕ) [NeZero n] [Fact (5 ≤ n)] :
    GaugeLie (MassGap.GaugeInstances.SO n) where
  lieGen M := M.IsHermitian ∧ M.transpose = -M
  lieDim_pos := by
    have h5 : 5 ≤ n := Fact.out
    show 0 < n * (n - 1) / 2
    have h1 : 4 ≤ n - 1 := by omega
    have h2 : 2 ≤ n * (n - 1) := le_trans (by norm_num) (Nat.mul_le_mul h5 h1)
    exact Nat.div_pos h2 (by norm_num)

/-- `SO(3)`: Hermitian antisymmetric matrices; `dim 𝔤 = 3`.

DERIVED: `3` the dimension. -/
instance instGaugeLieSO3 : GaugeLie (MassGap.GaugeInstances.SO 3) where
  lieGen M := M.IsHermitian ∧ M.transpose = -M
  lieDim_pos := by
    show 0 < 3
    norm_num

/-- Compact `Sp(n)`: Hermitian `X` with `X J + J Xᵀ = 0`; `n(2n+1) > 0`.

DERIVED: `0` the defining relation; `2`, `1` the dimension formula. -/
instance instGaugeLieUSp (n : ℕ) [NeZero n] : GaugeLie (MassGap.GaugeInstances.USp n) where
  lieGen M := M.IsHermitian
    ∧ M * MassGap.GaugeInstances.Jsp n + MassGap.GaugeInstances.Jsp n * M.transpose = 0
  lieDim_pos := by
    show 0 < n * (2 * n + 1)
    exact Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne n)) (Nat.succ_pos _)

/-! ## 2. The running spacing and the coupling of each step -/

section Running

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- `λ_G = 2T(ρ)/(h^∨ d)`, the rescaling of the coupling that carries `aRun 1` to `aRunG G`.

DERIVED: `2` from `48/24`, the ratio of the argument of `aRunStdG_eq` to that of `aRunStd`. -/
def lamG : ℝ :=
  2 * GaugeRunning.TG G / (GaugeRunning.hG G * GaugeRunning.dG G)

/-- DERIVED: `0` the sign. -/
theorem lamG_pos : 0 < lamG G := by
  unfold lamG
  have h1 := GaugeRunning.TG_pos (G := G)
  have h2 := GaugeRunning.hG_pos (G := G)
  have h3 := GaugeRunning.dG_pos (G := G)
  positivity

/-- **`aRunG G β = aRun 1 (λ_G β)`**: the running spacing of every simple `G` is that of `SU(1)`'s
formula at the rescaled coupling.

DERIVED: the numerals are those of `aRunStdG_eq` and `aRunStd`. -/
theorem aRunG_eq (β : ℝ) :
    GaugeRunning.aRunG G β = AsymptoticScaling.aRun 1 (lamG G * β) := by
  have hh := (GaugeRunning.hG_pos (G := G)).ne'
  have hd := (GaugeRunning.dG_pos (G := G)).ne'
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold GaugeRunning.aRunG AsymptoticScaling.aRun AsymptoticScaling.aRunStd
  rw [GaugeRunning.aRunStdG_eq]
  unfold lamG
  push_cast
  congr 1
  · congr 1
    field_simp
    try ring
  · congr 1
    field_simp
    try ring

/-- DERIVED: `0` the sign; `1` the colour count of `aRun 1`. -/
theorem aRunG_pos {β : ℝ} (hβ : 0 < β) : 0 < GaugeRunning.aRunG G β := by
  rw [aRunG_eq]
  exact AsymptoticScaling.aRun_pos le_rfl (mul_pos (lamG_pos G) hβ)

/-- **The dyadic spacing of `G`**: `aRunG G 1 / 2^(k+1)`.

DERIVED: `2` the halving; `1` the reference coupling and the first halving. -/
def dySpacingG (k : ℕ) : ℝ := GaugeRunning.aRunG G 1 / 2 ^ (k + 1)

/-- DERIVED: `0` the sign; `1` the reference coupling. -/
theorem dySpacingG_pos (k : ℕ) : 0 < dySpacingG G k :=
  div_pos (aRunG_pos G one_pos) (by positivity)

/-- DERIVED: `0` the limit; `1`, `2` as in `dySpacingG`. -/
theorem tendsto_dySpacingG : Tendsto (dySpacingG G) atTop (𝓝 0) := by
  have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ (k + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp (tendsto_add_atTop_nat 1)
  exact Tendsto.div_atTop tendsto_const_nhds h2

/-- **A coupling `≥ 1` at which the running spacing of `G` is `dySpacingG G k`.**

DERIVED: `1` the reference coupling; `2` the halving. -/
theorem exists_couplingG (k : ℕ) :
    ∃ β : ℝ, 1 ≤ β ∧ GaugeRunning.aRunG G β = dySpacingG G k := by
  have hpos := dySpacingG_pos G k
  have hlt : dySpacingG G k < AsymptoticScaling.aRun 1 (lamG G) := by
    have e := aRunG_eq G 1
    rw [mul_one] at e
    rw [← e]
    exact div_lt_self (aRunG_pos G one_pos)
      (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega))
  obtain ⟨β', h1, h2⟩ := AsymptoticScaling.exists_beta_aRun_eq le_rfl hpos hlt
  have hl := lamG_pos G
  refine ⟨β' / lamG G, ?_, ?_⟩
  · rw [le_div_iff₀ hl]
    linarith
  · rw [aRunG_eq]
    have hl' := hl.ne'
    have e : lamG G * (β' / lamG G) = β' := by
      field_simp
    rw [e]
    exact h2

/-- **The coupling of step `k`** for `G`. DERIVED: no numeral. -/
def dyBetaG (k : ℕ) : ℝ := (exists_couplingG G k).choose

/-- DERIVED: `1` the reference coupling. -/
theorem one_le_dyBetaG (k : ℕ) : 1 ≤ dyBetaG G k := (exists_couplingG G k).choose_spec.1

/-- **The spacing runs with the coupling**: `aRunG G (dyBetaG G k) = dySpacingG G k`.

DERIVED: no numeral. -/
theorem aRunG_dyBetaG (k : ℕ) : GaugeRunning.aRunG G (dyBetaG G k) = dySpacingG G k :=
  (exists_couplingG G k).choose_spec.2

end Running

/-! ## 3. Schedules -/

/-- **A schedule**: the spacing `a k > 0`, `a k → 0`, and the state `ν k` of each step.

DERIVED: `0` the sign and the limit of the spacing. -/
structure Sched (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] where
  /-- The spacing of step `k`. -/
  a : ℕ → ℝ
  /-- The state of step `k`. -/
  ν : ℕ → MassGap.DLRLimit.State (IConf G)
  a_pos : ∀ k, 0 < a k
  a_lim : Tendsto a atTop (𝓝 0)

/-- Two schedules with the same spacings and states are equal. DERIVED: no numeral. -/
theorem Sched.ext' {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    {S T : Sched G} (ha : S.a = T.a) (hν : S.ν = T.ν) : S = T := by
  cases S
  cases T
  cases ha
  cases hν
  rfl

/-- **The canonical schedule of `G`**: `dySpacingG G`, and the periodic Wilson state of `G` at
`dyBetaG G k`.

DERIVED: no numeral. -/
def canonSched (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    [GaugeSimple G] : Sched G where
  a := dySpacingG G
  ν := fun k => GaugeWilson.periodicStateG G (dyBetaG G k)
  a_pos := dySpacingG_pos G
  a_lim := tendsto_dySpacingG G

/-- **The schedule of `ClayStatement`**: `dySpacing N`, `stateK`.

DERIVED: `0` the excluded colour count. -/
def schedSU (N : ℕ) [NeZero N] : Sched (MassGap.SUN.SU N) where
  a := dySpacing N
  ν := stateK (NeZero.ne N)
  a_pos := dySpacing_pos (one_le_of_ne_zero (NeZero.ne N))
  a_lim := tendsto_dySpacing N

/-- `Classical.choose` respects equality of the predicate. DERIVED: no numeral. -/
theorem choose_congr {α : Sort*} {p q : α → Prop} (h : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    hp.choose = hq.choose := by
  subst h
  rfl

section SU

variable (N : ℕ) [NeZero N] [Fact (2 ≤ N)]

/-- DERIVED: no numeral. -/
theorem dySpacingG_SU : dySpacingG (MassGap.SUN.SU N) = dySpacing N := by
  funext k
  unfold dySpacingG dySpacing
  rw [GaugeRunning.aRunG_SU N 1]

/-- At `SU(N)` the coupling of step `k` is `ContinuumSchwinger.dyBeta`.

DERIVED: `1` the reference coupling. -/
theorem dyBetaG_SU (k : ℕ) :
    dyBetaG (MassGap.SUN.SU N) k = dyBeta (one_le_of_ne_zero (NeZero.ne N)) k := by
  unfold dyBetaG dyBeta
  have hp : (fun β : ℝ => 1 ≤ β ∧ GaugeRunning.aRunG (MassGap.SUN.SU N) β
        = dySpacingG (MassGap.SUN.SU N) k)
      = (fun β : ℝ => 1 ≤ β ∧ AsymptoticScaling.aRun N β = dySpacing N k) := by
    funext β
    rw [GaugeRunning.aRunG_SU N β, dySpacingG_SU N]
  exact choose_congr hp _ _

/-- **At `SU(N)`, `N ≥ 2`, the canonical schedule is the schedule of `ClayStatement`.**

DERIVED: no numeral. -/
theorem canonSched_SU : canonSched (MassGap.SUN.SU N) = schedSU N := by
  refine Sched.ext' (dySpacingG_SU N) ?_
  funext k
  show GaugeWilson.periodicStateG (MassGap.SUN.SU N) (dyBetaG (MassGap.SUN.SU N) k)
    = stateK (NeZero.ne N) k
  rw [dyBetaG_SU N k]
  rfl

end SU

#print axioms aRunG_eq
#print axioms exists_couplingG
#print axioms aRunG_dyBetaG
#print axioms canonSched_SU

/-! ## 4. Lattice Schwinger functions over a schedule -/

section Lattice

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- A smeared-field datum over `G`. DERIVED: no numeral. -/
abbrev SFieldG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] :
    Type :=
  LField G × TestFn

/-- **The lattice Schwinger function of step `k`**: `ν_k (∏ᵢ smear a_k Oᵢ fᵢ)`.

DERIVED: no numeral. -/
def latSG (S : Sched G) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SFieldG G) : ℝ :=
  S.ν k (∏ i, smear (S.a k) (F i).1.1 (F i).2)

/-- Reindexing a family does not change its lattice Schwinger function. DERIVED: no numeral. -/
theorem latSG_comp_equiv (S : Sched G) (k : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (F : ι → SFieldG G) : latSG S k (F ∘ e) = latSG S k F := by
  unfold latSG
  congr 1
  exact Equiv.prod_comp e (fun i => smear (S.a k) (F i).1.1 (F i).2)

/-- The dyadic time vector `a_m · n` in direction `τ`. DERIVED: `4` the dimension. -/
def timeVecG (S : Sched G) (m : ℕ) (τ : Fin 4) (n : ℤ) : Fin 4 → ℝ :=
  site (S.a m) (axisVec τ n)

/-- DERIVED: `0` the sign; `1` one step. -/
theorem timeVecG_nonneg (S : Sched G) (m : ℕ) (τ : Fin 4) : 0 ≤ timeVecG S m τ 1 τ := by
  show 0 ≤ S.a m * ((axisVec τ 1 τ : ℤ) : ℝ)
  simp [axisVec, (S.a_pos m).le]

/-- A monomial of smeared fields. DERIVED: no numeral. -/
abbrev MonoG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] :
    Type :=
  Σ n : ℕ, (Fin n → SFieldG G)

/-- Every factor of `P` vanishes below the time `d`. DERIVED: `4` the dimension. -/
def posAtG (τ : Fin 4) (d : ℝ) (P : MonoG G) : Prop :=
  ∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y τ

/-- **Margin monomials**. DERIVED: `0` the sign of the margin. -/
abbrev MarginMonoG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (τ : Fin 4) (r : ℝ) : Type :=
  {P : MonoG G // ∃ d : ℝ, 0 < d ∧ r < d ∧ posAtG τ d P}

end Lattice

/-! ## 5. Configuration flows and the energy density -/

section Flow

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A configuration flow over `G`**: the fields of `ContinuumFlow.ConfFlow` with `SU N` replaced
by `G`.

DERIVED: `4` the dimension; `0` the reflection constant. -/
structure ConfFlowG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    where
  /-- The flowed configuration at step `k`. -/
  V : ℕ → IConf G → IConf G
  continuous_V : ∀ k, Continuous (V k)
  gauge : ∀ (k : ℕ) (g : ISite → G) (U : IConf G),
    V k (GaugeInvariantAlgebra.igaugeTransform g U) = GaugeInvariantAlgebra.igaugeTransform g (V k U)
  refl : ∀ (k : ℕ) (τ : Fin 4) (U : IConf G),
    V k (LatticeReflection.ireflConf τ 0 U) = LatticeReflection.ireflConf τ 0 (V k U)
  /-- The lattice range at step `k`. -/
  range : ℕ → ℕ
  local_V : ∀ (k : ℕ) (l : ILink), ∃ T : Finset ILink,
    (∀ l' ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ (range k : ℤ)) ∧
      ∀ U U' : IConf G, (∀ l' ∈ T, U l' = U' l') → V k U l = V k U' l

/-- `ConfFlow N` as a `ConfFlowG (SU N)`. DERIVED: no numeral. -/
def _root_.MassGap.ContinuumFlow.ConfFlow.toG {N : ℕ} [NeZero N] (W : ConfFlow N) :
    ConfFlowG (MassGap.SUN.SU N) where
  V := W.V
  continuous_V := W.continuous_V
  gauge := W.gauge
  refl := W.refl
  range := W.range
  local_V := W.local_V

/-- `ConfFlowG (SU N)` as a `ConfFlow N`. DERIVED: no numeral. -/
def ConfFlowG.toSU {N : ℕ} [NeZero N] (W : ConfFlowG (MassGap.SUN.SU N)) : ConfFlow N where
  V := W.V
  continuous_V := W.continuous_V
  gauge := W.gauge
  refl := W.refl
  range := W.range
  local_V := W.local_V

omit [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- A configuration map of finite range carries local observables to local observables.

DERIVED: no numeral. -/
theorem isLocalOn_compG {R : ℕ} {W : IConf G → IConf G}
    (hW : ∀ l : ILink, ∃ T : Finset ILink, (∀ l' ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ)) ∧
      ∀ U U' : IConf G, (∀ l' ∈ T, U l' = U' l') → W U l = W U' l)
    {S : Finset ILink} {F : IConf G → ℝ} (hS : IsLocalOn S F) :
    ∃ S' : Finset ILink, IsLocalOn S' (fun U => F (W U)) ∧
      ∀ l' ∈ S', ∃ l ∈ S, ∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ) := by
  classical
  choose T hTr hTl using hW
  refine ⟨S.biUnion T, fun U U' h => hS _ _ (fun l hl => hTl l U U' (fun l' hl' =>
    h l' (Finset.mem_biUnion.mpr ⟨l, hl, hl'⟩))), fun l' hl' => ?_⟩
  obtain ⟨l, hl, hl'T⟩ := Finset.mem_biUnion.mp hl'
  exact ⟨l, hl, hTr l l' hl'T⟩

/-- The flowed field `O ∘ V k`. DERIVED: no numeral. -/
def ConfFlowG.fieldMap (W : ConfFlowG G) (k : ℕ) (O : LField G) : LField G :=
  ⟨O.1.comp ⟨W.V k, W.continuous_V k⟩,
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      obtain ⟨S', hS', -⟩ := isLocalOn_compG (W.local_V k) hS
      exact ⟨S', hS'⟩,
     fun g U => by
      show O.1 (W.V k (GaugeInvariantAlgebra.igaugeTransform g U)) = O.1 (W.V k U)
      rw [W.gauge]
      exact O.2.2 g (W.V k U)⟩⟩

/-- The field `s · O`. DERIVED: no numeral. -/
def scaleFieldG (O : LField G) (s : ℝ) : LField G :=
  ⟨s • O.1,
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      exact ⟨S, fun U V h => by
        show s * O.1 U = s * O.1 V
        rw [hS U V h]⟩,
     fun g U => by
      show s * O.1 (GaugeInvariantAlgebra.igaugeTransform g U) = s * O.1 U
      rw [O.2.2 g U]⟩⟩

open Classical in
/-- **The factor on a class `D`**: `a_k⁻⁴` on the fields of `D`, `1` elsewhere.

DERIVED: `4` the dimension; `1` the unscaled factor. -/
def zOnG (S : Sched G) (D : Set (LField G)) (k : ℕ) (O : LField G) : ℝ :=
  if O ∈ D then (S.a k ^ 4)⁻¹ else 1

open Classical in
/-- **The subtraction on a class `D`**: `s` on the fields of `D`, `0` elsewhere.

DERIVED: `0` the absent subtraction. -/
def sOnG (D : Set (LField G)) (s : ℕ → LField G → ℝ) (k : ℕ) (O : LField G) : ℝ :=
  if O ∈ D then s k O else 0

/-- **The energy density of the flow on the class `D`**: `a_k⁻⁴ (O ∘ V_k)` for `O ∈ D`, `O ∘ V_k`
otherwise; the map of `ObserverOS.energy0`.

DERIVED: `0` the zero subtraction. -/
def energyMapG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (k : ℕ) (O : LField G) :
    LField G :=
  scaleFieldG ((W.fieldMap k O).sub (sOnG D (fun _ _ => 0) k O)) (zOnG S D k O)

/-- **The flowed lattice Schwinger function of step `k`** for a field map `Φ`.

DERIVED: no numeral. -/
def latSFG (S : Sched G) (Φ : ℕ → LField G → LField G) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SFieldG G) : ℝ :=
  latSG S k (fun i => (Φ k (F i).1, (F i).2))

/-- **The flowed uniform bound**. DERIVED: no numeral. -/
def UniformBoundFG (S : Sched G) (Φ : ℕ → LField G → LField G) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SFieldG G), ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
    ∀ᶠ k in atTop,
      |latSFG S Φ k (fun i => ((F i).1, (F i).2.translate (site (S.a m) (n i))))| ≤ C

/-- **The flowed continuum Schwinger function**: the limit along `ultra`. DERIVED: no numeral. -/
def contSFG (S : Sched G) (Φ : ℕ → LField G → LField G) {ι : Type} [Fintype ι]
    (F : ι → SFieldG G) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latSFG S Φ k F)

/-- **The Schwinger functions of a family of fields on decaying functions**: the limit of those of
the cut-offs. DERIVED: no numeral. -/
def schwSFMG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) {ι : Type} [Fintype ι]
    (O : ι → LField G) (g : ι → Decaying) : ℝ :=
  limUnder atTop (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R)))

end Flow

/-! ## 6. Decaying monomials and the linked Euclidean data -/

section Linked

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- A monomial of decaying functions. DERIVED: no numeral. -/
abbrev DMonoG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] :
    Type :=
  Σ n : ℕ, (Fin n → LField G × Decaying)

/-- Every decaying function of the monomial vanishes below the time `d`.

DERIVED: `4` the dimension. -/
def posAtDG (τ : Fin 4) (d : ℝ) (P : DMonoG G) : Prop := ∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y τ

/-- Margin monomials of decaying functions. DERIVED: `0` the lower end of `d`. -/
abbrev DMarginMonoG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (τ : Fin 4) (r : ℝ) : Type :=
  {P : DMonoG G // ∃ d : ℝ, 0 < d ∧ r < d ∧ posAtDG τ d P}

/-- Decaying margin monomials with fields in `D`. DERIVED: no numeral. -/
abbrev DMarginMonoDG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (D : Set (LField G)) (τ : Fin 4) (r : ℝ) : Type :=
  {P : DMarginMonoG G τ r // ∀ i, (P.1.2 i).1 ∈ D}

/-- Compact margin monomials with fields in `D`. DERIVED: no numeral. -/
abbrev MarginMonoDG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (D : Set (LField G)) (τ : Fin 4) (r : ℝ) : Type :=
  {Q : MarginMonoG G τ r // ∀ i, (Q.1.2 i).1 ∈ D}

/-- The fields of the reflected pair `θP ∪ Q`. DERIVED: no numeral. -/
def pairFieldsG (τ : Fin 4) (P Q : DMonoG G) : Fin P.1 ⊕ Fin Q.1 → LField G :=
  Sum.elim (fun i => (P.2 i).1.refl τ) (fun j => (Q.2 j).1)

/-- The decaying functions of the reflected pair `θP ∪ Q`. DERIVED: no numeral. -/
def pairFunsG (τ : Fin 4) (P Q : DMonoG G) : Fin P.1 ⊕ Fin Q.1 → Decaying :=
  Sum.elim (fun i => decRefl τ (P.2 i).2) (fun j => (Q.2 j).2)

/-- A compact margin monomial as a decaying one. DERIVED: no numeral. -/
def ofMarginDG {D : Set (LField G)} {τ : Fin 4} {r : ℝ} (Q : MarginMonoDG G D τ r) :
    DMarginMonoDG G D τ r :=
  ⟨⟨⟨Q.1.1.1, fun i => ((Q.1.1.2 i).1, decOfTest (Q.1.1.2 i).2)⟩, by
      obtain ⟨d, hd, hrd, hQ⟩ := Q.1.2
      exact ⟨d, hd, hrd, fun i y hy => hQ i y hy⟩⟩, Q.2⟩

/-- **Schwartz-indexed Euclidean data linked to their reconstruction**, over `G`: the fields of
`ObserverOSLinked.OSDataSLinked` with `SU N` replaced by `G`.

DERIVED: `2` the Euclidean exponent; `4` the dimension. -/
structure OSDataSLinkedG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeGroup G] (D : Set (LField G)) (τ : Fin 4) (r : ℝ) where
  /-- The Euclidean data and the reconstructed space. -/
  base : OSDataS
  /-- The Schwinger functional on families of fields and decaying functions. -/
  SM : {ι : Type} → [Fintype ι] → (ι → LField G) → (ι → Decaying) → ℝ
  /-- The field of the Schwartz-class Schwinger functions. -/
  O : LField G
  S_eq : ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
    base.S n φ = SM (fun _ : Fin n => O) (fun i => ofE4 (φ i))
  /-- The vectors of decaying margin monomials. -/
  vec : DMarginMonoDG G D τ r → base.H
  inner_vec : ∀ P Q : DMarginMonoDG G D τ r,
    inner ℂ (vec P) (vec Q) = (SM (pairFieldsG τ P.1.1 Q.1.1) (pairFunsG τ P.1.1 Q.1.1) : ℂ)
  /-- The vectors of compact margin monomials. -/
  cvec : MarginMonoDG G D τ r → base.H
  vec_compact : ∀ Q : MarginMonoDG G D τ r, vec (ofMarginDG Q) = cvec Q
  closure_eq : closure (Set.range vec) = closure (Set.range cvec)

/-- `OSDataSLinked` as an `OSDataSLinkedG (SU N)`. DERIVED: no numeral. -/
def _root_.MassGap.ObserverOSLinked.OSDataSLinked.toG {N : ℕ} [NeZero N]
    {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ} (X : OSDataSLinked N D τ r) :
    OSDataSLinkedG (MassGap.SUN.SU N) D τ r where
  base := X.base
  SM := X.SM
  O := X.O
  S_eq := X.S_eq
  vec := X.vec
  inner_vec := X.inner_vec
  cvec := X.cvec
  vec_compact := X.vec_compact
  closure_eq := X.closure_eq

/-- `OSDataSLinkedG (SU N)` as an `OSDataSLinked`. DERIVED: no numeral. -/
def OSDataSLinkedG.toSU {N : ℕ} [NeZero N] {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4}
    {r : ℝ} (X : OSDataSLinkedG (MassGap.SUN.SU N) D τ r) : OSDataSLinked N D τ r where
  base := X.base
  SM := X.SM
  O := X.O
  S_eq := X.S_eq
  vec := X.vec
  inner_vec := X.inner_vec
  cvec := X.cvec
  vec_compact := X.vec_compact
  closure_eq := X.closure_eq

end Linked

/-! ## 7. The symmetrised plaquette field -/

section Sym

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A finite sum of local gauge-invariant fields.** DERIVED: no numeral. -/
def lsumG {ι : Type} [Fintype ι] (P : ι → LField G) : LField G :=
  ⟨∑ i, (P i).1, ⟨by
      classical
      choose S hS using fun i => (P i).2.1
      refine ⟨Finset.univ.biUnion S, fun U V h => ?_⟩
      simp only [ContinuousMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ =>
        hS i U V fun l hl => h l (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hl⟩),
    fun g U => by
      simp only [ContinuousMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => (P i).2.2 g U⟩⟩

/-- The field reflected in axis `τ` if `b`. DERIVED: no numeral. -/
def lrpowG : Bool → Fin 4 → LField G → LField G
  | true, τ, O => O.refl τ
  | false, _, O => O

/-- The field read through the reflections of `s`. DERIVED: `0`–`3` the axes. -/
def reflFieldG (s : Fin 4 → Bool) (O : LField G) : LField G :=
  lrpowG (s 3) 3 (lrpowG (s 2) 2 (lrpowG (s 1) 1 (lrpowG (s 0) 0 O)))

/-- **The symmetrised field**: `O` summed over the hypercubic group.

DERIVED: `4` the dimension. -/
def symG (O : LField G) : LField G :=
  lsumG (fun g : Equiv.Perm (Fin 4) × (Fin 4 → Bool) => lfieldAxis g.1 (reflFieldG g.2 O))

/-- **The plaquette density of `G` as a local gauge-invariant field**: the Wilson density
`1 − Re tr ρ(U_q)/d` of the plaquette holonomy.

DERIVED: no numeral. -/
def plaqFieldG (q : MassGap.GibbsSpec.IPlaq) : LField G :=
  ⟨⟨fun U => GaugeGroup.wilsonDensityG G (MassGap.GibbsSpec.ihol (G := G) q U),
      GaugeGroup.continuous_wilsonDensityG.comp (MassGap.WilsonDLR.continuous_ihol q)⟩,
    ⟨(MassGap.GibbsSpec.ilinks q).toFinset, fun U V h => by
      show GaugeGroup.wilsonDensityG G (MassGap.GibbsSpec.ihol q U)
        = GaugeGroup.wilsonDensityG G (MassGap.GibbsSpec.ihol q V)
      rw [MassGap.GibbsSpec.ihol_congr q U V (fun l hl => h l (List.mem_toFinset.mpr hl))]⟩,
    GaugeInvariantAlgebra.isIGaugeInvariant_of_classFun
      (fun h k => GaugeGroup.wilsonDensityG_conj h k) q (fun _ => rfl)⟩

end Sym

end MassGap.ClayTreeG

end
