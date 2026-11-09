import Mathlib
import MassGap.EnergyBoundG

/-!
# MassGap.SymPlaqG — the symmetrised plaquette class over a gauge group `G`

`EnergyBoundG.clayStatementAtG_of_inputsG''` takes, for its class `D`, the inputs `hpos` (every field
of `D` is non-negative) and `hcube` (`CubeMomentBoundG (canonSched G) W` on `D`). At `SU(N)`,
`ClayWiring` takes `D = SymPlaqClass N`, discharges `hpos` by `ObserverSymField.symPlaq_nonneg`, and
reduces `hcube` to the plaquette class by `ObserverSymField.symPlaq_cube`. This module carries both
steps to every `GaugeGroup G`:

| step | `SU(N)` | here (any `G`) |
|---|---|---|
| plaquette class | `ObserverEnergyBox.PlaqClass` | `PlaqClassG` |
| reflection closed | `ObserverEnergyBox.plaqClass_refl` | `plaqClassG_refl` |
| non-negative | `ObserverEnergyBox.plaqClass_nonneg` | `plaqClassG_nonneg` (`GaugeGroup.wilsonDensityG_nonneg`) |
| symmetrised class | `ObserverSymField.SymPlaqClass` | `SymPlaqClassG` |
| non-negative | `ObserverSymField.symPlaq_nonneg` | `symPlaqG_nonneg` |
| reflection closed | `ObserverSymField.symPlaq_refl` | `symPlaqG_refl` (`symG_refl`) |
| cube energy relabelled | `ObserverSymField.cubeSum_iaxis` | `cubeSumG_iaxis` |
| (E) relabelling invariant | `ObserverSymField.cubeMomentBound_axis` | `cubeMomentBoundG_axis` |
| (E) for a finite sum | `ObserverSymField.cubeMomentBound_lsum` | `cubeMomentBoundG_lsum` |
| (E) on the symmetrised class | `ObserverSymField.symPlaq_cube` | `symPlaqG_cube` |

`symPlaq_cube` uses two facts beyond the plaquette class: the flow commutes with the axis
permutations (`hW`), and the state of each step is invariant under them
(`ContinuumHypercubic.stateK_axis`). Over a schedule `S` of `G` the second is the hypothesis
`SchedAxisInv S`; at `schedSU N` it is `stateK_axis` (`schedAxisInv_SU`). Its proof at `SU(N)`
passes through `SUN.su_expect_invariant` for `WilsonHypercubic.axisSymmetry`, which is stated at
`SU(N)` only; at `canonSched G` for other `G` it is an input of `clayStatementAtG_of_inputsG'''`.

At `SU(N)`, `PlaqClassG` and `SymPlaqClassG` are `PlaqClass N` and `SymPlaqClass N`
(`plaqClassG_SU`, `symPlaqClassG_SU`), and `symG (plaqFieldG q)` is `sym (plaqField q)`
(`symG_plaqFieldG_SU`).

`clayStatementAtG_of_inputsG'''` is `clayStatementAtG_of_inputsG''` at `D = SymPlaqClassG G` with
`hpos` discharged and `hcube` replaced by `hW`, `SchedAxisInv (canonSched G)` and (E) on
`PlaqClassG G`. `clayStatementAtP_of_inputsG'''_at` is the same statement read at a schedule,
constants, class, plaquette class and field each given with an equation to the ones of
`clayStatementAtG_of_inputsG'''`. `clayStatementAt_of_inputs_viaG'''` has the hypotheses
of `ClayWiring.clayStatementAt_of_inputs` and proves its conclusion through
`clayStatementAtP_of_inputsG'''_at` at `schedSU N` (`ClayTreeG.canonSched_SU`) and `constsSU N`
(`ClayStatementG.constsG_SU`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `0` the reflection constant and the signs; `0`–`3` the
axes; `2` makes a power even.
-/

noncomputable section

namespace MassGap.SymPlaqG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverEnergyBox
  MassGap.LatticeReflection MassGap.ClayTreeG MassGap.EnergyBoundG Filter

/-! ## 1. The plaquette class over `G` -/

section Plaq

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- Reflection is an involution on local fields.

DERIVED: `0` the reflection constant. -/
theorem refl_reflG (τ : Fin 4) (O : LField G) : (O.refl τ).refl τ = O :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (LatticeReflection.ireflConf τ 0 (LatticeReflection.ireflConf τ 0 U)) = O.1 U
    rw [LatticeReflection.ireflConf_involutive τ 0 U]))

/-- Reflection preserves non-negativity.

DERIVED: `0` the sign and the reflection constant. -/
theorem refl_nonnegG {O : LField G} (hO : ∀ U, 0 ≤ O.1 U) (τ : Fin 4) :
    ∀ U, 0 ≤ (O.refl τ).1 U := fun U => by
  show 0 ≤ O.1 (LatticeReflection.ireflConf τ 0 U)
  exact hO _

/-- A field reflected along a list of directions.

DERIVED: `4` the dimension. -/
def reflListG (l : List (Fin 4)) (O : LField G) : LField G :=
  l.foldr (fun τ P => P.refl τ) O

variable (G) in
/-- **The plaquette class over `G`**: the plaquette densities `plaqFieldG q` and their reflections.

DERIVED: `4` the dimension. -/
def PlaqClassG : Set (LField G) :=
  {O | ∃ (q : MassGap.GibbsSpec.IPlaq) (l : List (Fin 4)), O = reflListG l (plaqFieldG q)}

variable (G) in
/-- **The plaquette class over `G` is reflection closed.**

DERIVED: `4` the dimension. -/
theorem plaqClassG_refl :
    ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ PlaqClassG G ↔ O ∈ PlaqClassG G := by
  intro τ O
  constructor
  · rintro ⟨q, l, h⟩
    refine ⟨q, τ :: l, ?_⟩
    calc O = (O.refl τ).refl τ := (refl_reflG τ O).symm
      _ = (reflListG l (plaqFieldG q)).refl τ := by rw [h]
      _ = reflListG (τ :: l) (plaqFieldG q) := rfl
  · rintro ⟨q, l, h⟩
    exact ⟨q, τ :: l, by rw [h]; rfl⟩

/-- **The plaquette class over `G` is non-negative**: `wilsonDensityG ≥ 0`, and reflection keeps the
sign.

DERIVED: `0` the sign. -/
theorem plaqClassG_nonneg : ∀ O ∈ PlaqClassG G, ∀ U, 0 ≤ O.1 U := by
  rintro O ⟨q, l, rfl⟩
  induction l with
  | nil =>
    intro U
    show 0 ≤ GaugeGroup.wilsonDensityG G (MassGap.GibbsSpec.ihol q U)
    exact GaugeGroup.wilsonDensityG_nonneg _
  | cons τ l ih => exact refl_nonnegG ih τ

end Plaq

/-! ## 2. The symmetrised field over `G` -/

section Sym

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- DERIVED: no numeral. -/
theorem lsumG_apply {ι : Type} [Fintype ι] (P : ι → LField G) (U : IConf G) :
    (lsumG P).1 U = ∑ i, (P i).1 U := by
  show (∑ i, (P i).1) U = _
  simp only [ContinuousMap.sum_apply]

/-- DERIVED: `4` the dimension. -/
theorem lfieldAxisG_apply (e : Equiv.Perm (Fin 4)) (O : LField G) (U : IConf G) :
    (lfieldAxis e O).1 U = O.1 (iaxisConf e U) := rfl

/-- DERIVED: `0` the reflection constant. -/
theorem lreflG_apply (τ : Fin 4) (O : LField G) (U : IConf G) :
    (LField.refl τ O).1 U = O.1 (ireflConf τ 0 U) := rfl

/-- A reflected plaquette field stays in the plaquette class.

DERIVED: no numeral. -/
theorem reflFieldG_mem (s : Fin 4 → Bool) {O : LField G} (hO : O ∈ PlaqClassG G) :
    reflFieldG s O ∈ PlaqClassG G := by
  have h : ∀ (b : Bool) (τ : Fin 4) (P : LField G), P ∈ PlaqClassG G →
      lrpowG b τ P ∈ PlaqClassG G := by
    intro b τ P hP
    cases b
    · exact hP
    · exact (plaqClassG_refl G τ P).mpr hP
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ hO)))

/-- The symmetrised field as a sum of pullbacks of the reflected fields.

DERIVED: `4` the dimension. -/
theorem symG_apply_pull (O : LField G) (U : IConf G) :
    (symG O).1 U
      = ∑ g : Equiv.Perm (Fin 4) × (Fin 4 → Bool), (reflFieldG g.2 O).1 (iaxisConf g.1 U) := by
  unfold symG
  rw [lsumG_apply]
  rfl

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- **A relabelling conjugates a reflection into the reflection of the relabelled axis**, on
configurations of `G`.

DERIVED: `0` the reflection constant. -/
theorem iaxisConf_ireflConfG (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (U : IConf G) :
    iaxisConf e (ireflConf τ 0 U) = ireflConf (e.symm τ) 0 (iaxisConf e U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  have hiff : (e μ = τ) ↔ (μ = e.symm τ) :=
    ⟨fun h => by rw [← h, Equiv.symm_apply_apply], fun h => by rw [h, Equiv.apply_symm_apply]⟩
  simp only [iaxisConf, ireflConf, iaxisLink, ireflLink, hiff]
  split_ifs <;> rw [ObserverSymField.iaxisSite_ireflSite]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- **Reflections of different axes commute on configurations of `G`.**

DERIVED: `4` the dimension. -/
theorem ireflConf_commG {τ τ' : Fin 4} (hτ : τ ≠ τ') (c : ℤ) (U : IConf G) :
    ireflConf τ c (ireflConf τ' c U) = ireflConf τ' c (ireflConf τ c U) := by
  funext l
  have hl := ObserverSymField.ireflLink_comm hτ c l
  by_cases h : l.1 = τ
  · have h' : l.1 ≠ τ' := fun h' => hτ (h.symm.trans h')
    simp only [ireflConf, ireflLink_fst, if_pos h, if_neg h', hl]
  · by_cases h' : l.1 = τ'
    · simp only [ireflConf, ireflLink_fst, if_pos h', if_neg h, hl]
    · simp only [ireflConf, ireflLink_fst, if_neg h', if_neg h, hl]

/-- The reflection of axis `τ` if `b`, the identity otherwise.

DERIVED: `0` the reflection constant. -/
def rpowG : Bool → Fin 4 → IConf G → IConf G
  | true, τ, V => ireflConf τ 0 V
  | false, _, V => V

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- DERIVED: `0` the reflection constant. -/
theorem rpowG_comm {τ τ' : Fin 4} (hτ : τ ≠ τ') (b : Bool) (V : IConf G) :
    rpowG b τ (ireflConf τ' 0 V) = ireflConf τ' 0 (rpowG b τ V) := by
  cases b
  · rfl
  · exact ireflConf_commG hτ 0 V

omit [MeasurableSpace G] [GaugeGroup G] in
/-- DERIVED: `0` the reflection constant. -/
theorem rpowG_self (b : Bool) (τ : Fin 4) (V : IConf G) :
    rpowG b τ (ireflConf τ 0 V) = rpowG (!b) τ V := by
  cases b
  · rfl
  · exact ireflConf_involutive τ 0 V

/-- The reflections of the axes in `s`, in the order `3, 2, 1, 0`.

DERIVED: `0`–`3` the axes. -/
def reflAllG (s : Fin 4 → Bool) (V : IConf G) : IConf G :=
  rpowG (s 0) 0 (rpowG (s 1) 1 (rpowG (s 2) 2 (rpowG (s 3) 3 V)))

omit [MeasurableSpace G] [GaugeGroup G] in
/-- DERIVED: `0`–`3` the axes. -/
theorem reflAllG_refl0 (s : Fin 4 → Bool) (V : IConf G) :
    reflAllG s (ireflConf 0 0 V) = reflAllG (ObserverSymField.flipB s 0) V := by
  simp only [reflAllG, rpowG_comm (show (3 : Fin 4) ≠ 0 by decide),
    rpowG_comm (show (2 : Fin 4) ≠ 0 by decide), rpowG_comm (show (1 : Fin 4) ≠ 0 by decide),
    rpowG_self]
  simp [ObserverSymField.flipB]

omit [MeasurableSpace G] [GaugeGroup G] in
/-- DERIVED: `0`–`3` the axes. -/
theorem reflAllG_refl1 (s : Fin 4 → Bool) (V : IConf G) :
    reflAllG s (ireflConf 1 0 V) = reflAllG (ObserverSymField.flipB s 1) V := by
  simp only [reflAllG, rpowG_comm (show (3 : Fin 4) ≠ 1 by decide),
    rpowG_comm (show (2 : Fin 4) ≠ 1 by decide), rpowG_self]
  simp [ObserverSymField.flipB]

omit [MeasurableSpace G] [GaugeGroup G] in
/-- DERIVED: `0`–`3` the axes. -/
theorem reflAllG_refl2 (s : Fin 4 → Bool) (V : IConf G) :
    reflAllG s (ireflConf 2 0 V) = reflAllG (ObserverSymField.flipB s 2) V := by
  simp only [reflAllG, rpowG_comm (show (3 : Fin 4) ≠ 2 by decide), rpowG_self]
  simp [ObserverSymField.flipB]

omit [MeasurableSpace G] [GaugeGroup G] in
/-- DERIVED: `0`–`3` the axes. -/
theorem reflAllG_refl3 (s : Fin 4 → Bool) (V : IConf G) :
    reflAllG s (ireflConf 3 0 V) = reflAllG (ObserverSymField.flipB s 3) V := by
  simp only [reflAllG, rpowG_self]
  simp [ObserverSymField.flipB]

omit [MeasurableSpace G] [GaugeGroup G] in
/-- **A reflection after the reflections of `s` is the reflections of `s` with that axis flipped.**

DERIVED: `0` the reflection constant. -/
theorem reflAllG_refl (s : Fin 4 → Bool) (t : Fin 4) (V : IConf G) :
    reflAllG s (ireflConf t 0 V) = reflAllG (ObserverSymField.flipB s t) V := by
  fin_cases t
  · exact reflAllG_refl0 s V
  · exact reflAllG_refl1 s V
  · exact reflAllG_refl2 s V
  · exact reflAllG_refl3 s V

/-- DERIVED: `0` the reflection constant. -/
theorem lrpowG_apply (b : Bool) (τ : Fin 4) (O : LField G) (V : IConf G) :
    (lrpowG b τ O).1 V = O.1 (rpowG b τ V) := by
  cases b <;> rfl

/-- DERIVED: `0`–`3` the axes. -/
theorem reflFieldG_apply (s : Fin 4 → Bool) (O : LField G) (V : IConf G) :
    (reflFieldG s O).1 V = O.1 (reflAllG s V) := by
  rw [reflFieldG, lrpowG_apply, lrpowG_apply, lrpowG_apply, lrpowG_apply]
  rfl

/-- DERIVED: `4` the dimension. -/
theorem symG_apply (O : LField G) (U : IConf G) :
    (symG O).1 U
      = ∑ g : Equiv.Perm (Fin 4) × (Fin 4 → Bool), O.1 (reflAllG g.2 (iaxisConf g.1 U)) := by
  rw [symG_apply_pull]
  exact Finset.sum_congr rfl fun g _ => reflFieldG_apply g.2 O (iaxisConf g.1 U)

/-- **The symmetrised field over `G` is invariant under the axis reflections.**

DERIVED: `0` the reflection constant. -/
theorem symG_refl (O : LField G) (τ₀ : Fin 4) : LField.refl τ₀ (symG O) = symG O := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  rw [lreflG_apply]
  rw [symG_apply, symG_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [iaxisConf_ireflConfG, reflAllG_refl]
  exact Fintype.sum_equiv (ObserverSymField.flipEquiv (e.symm τ₀)) _ _ (fun s => rfl)

variable (G) in
/-- **The symmetrised plaquette class over `G`**: each plaquette density `plaqFieldG q` summed over
its hypercubic images.

DERIVED: `4` the dimension. -/
def SymPlaqClassG : Set (LField G) :=
  {O | ∃ q : MassGap.GibbsSpec.IPlaq, O = symG (plaqFieldG q)}

/-- **The symmetrised class over `G` is non-negative**: each member is a sum of pullbacks of members
of `PlaqClassG G`.

DERIVED: `0` the sign. -/
theorem symPlaqG_nonneg : ∀ O ∈ SymPlaqClassG G, ∀ U, 0 ≤ O.1 U := by
  rintro O ⟨q, rfl⟩ U
  rw [symG_apply_pull]
  exact Finset.sum_nonneg fun g _ => plaqClassG_nonneg _ (reflFieldG_mem g.2 ⟨q, [], rfl⟩) _

variable (G) in
/-- **The symmetrised class over `G` is reflection closed**: its members are reflection invariant.

DERIVED: `4` the dimension. -/
theorem symPlaqG_refl :
    ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ SymPlaqClassG G ↔ O ∈ SymPlaqClassG G := by
  intro τ O
  constructor
  · rintro ⟨q, h⟩
    refine ⟨q, ?_⟩
    calc O = (O.refl τ).refl τ := (refl_reflG τ O).symm
      _ = (symG (plaqFieldG q)).refl τ := by rw [h]
      _ = symG (plaqFieldG q) := symG_refl _ τ
  · rintro ⟨q, rfl⟩
    exact ⟨q, symG_refl _ τ⟩

/-- **The class is non-empty**: the symmetrised plaquette density at the origin.

DERIVED: `q0` the `(0, 1)` plaquette at the origin. -/
theorem symPlaqG_q0 : symG (plaqFieldG ObserverEnergyMoments.q0) ∈ SymPlaqClassG G :=
  ⟨ObserverEnergyMoments.q0, rfl⟩

end Sym

/-! ## 3. (E) for the symmetrised class over a schedule -/

section Cube

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The states of a schedule are invariant under the axis permutations**: the hypothesis
`ContinuumHypercubic.stateK_axis` supplies at `SU(N)`.

DERIVED: `4` the dimension. -/
def SchedAxisInv (S : Sched G) : Prop :=
  ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (F : C(IConf G, ℝ)), S.ν k (iaxisObs e F) = S.ν k F

/-- **The cube energy of a relabelled reading** is the relabelled cube energy.

DERIVED: `4` the dimension. -/
theorem cubeSumG_iaxis (a R : ℝ) (e : Equiv.Perm (Fin 4)) (F : C(IConf G, ℝ)) (U : IConf G) :
    cubeSumG a R (iaxisObs e F) U = cubeSumG a R F (iaxisConf e U) := by
  rw [cubeSumG_apply, cubeSumG_apply]
  symm
  refine Finset.sum_equiv (iaxisSitePerm e) (fun x => ObserverSymField.mem_box_iaxis e _ x)
    (fun x _ => ?_)
  show cubeInd R (site a x) * F (transConf x (iaxisConf e U))
    = cubeInd R (site a (iaxisSite e x)) * F (iaxisConf e (transConf (iaxisSite e x) U))
  rw [ObserverSymField.cubeInd_iaxis, iaxisConf_transConf]

/-- A configuration flow commuting with the relabellings gives a field map commuting with them.

DERIVED: `4` the dimension. -/
theorem fieldMapG_axis (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (k : ℕ) (e : Equiv.Perm (Fin 4)) (O : LField G) :
    W.fieldMap k (lfieldAxis e O) = lfieldAxis e (W.fieldMap k O) :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (iaxisConf e (W.V k U)) = O.1 (W.V k (iaxisConf e U))
    rw [hW]))

/-- **(E) is relabelling invariant** over a schedule with `SchedAxisInv S`, for a configuration flow
commuting with the relabellings: the cube moments of `lfieldAxis e O` are those of `O`.

DERIVED: `2` the even power. -/
theorem cubeMomentBoundG_axis (S : Sched G) (hA : SchedAxisInv S) (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    {O : LField G} (hO : CubeMomentBoundG S W O) (e : Equiv.Perm (Fin 4)) :
    CubeMomentBoundG S W (lfieldAxis e O) := by
  intro R hR p
  obtain ⟨C, hC⟩ := hO R hR p
  refine ⟨C, hC.mono fun k hk => ?_⟩
  have h : cubeSumG (S.a k) R (W.fieldMap k (lfieldAxis e O)).1 ^ (2 * p)
      = iaxisObs e (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p)) := by
    ext U
    rw [ContinuousMap.pow_apply]
    show _ = (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p)) (iaxisConf e U)
    rw [ContinuousMap.pow_apply, fieldMapG_axis W hW k e O]
    exact congrArg (· ^ (2 * p)) (cubeSumG_iaxis _ R e _ U)
  rw [h, hA]
  exact hk

/-- **(E) for a finite sum of non-negative fields** from (E) for each, over any schedule.

DERIVED: `0` the sign; `2` the even power. -/
theorem cubeMomentBoundG_lsum (S : Sched G) (W : ConfFlowG G) {ι : Type} [Fintype ι] [Nonempty ι]
    (P : ι → LField G) (hpos : ∀ i U, 0 ≤ (P i).1 U)
    (hP : ∀ i, CubeMomentBoundG S W (P i)) : CubeMomentBoundG S W (lsumG P) := by
  intro R hR p
  choose C hC using fun i => hP i R hR p
  refine ⟨(Fintype.card ι : ℝ) ^ (2 * p) * ∑ i, |C i|, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hC] with k hk
  have hsplit : ∀ U, cubeSumG (S.a k) R (W.fieldMap k (lsumG P)).1 U
      = ∑ i, cubeSumG (S.a k) R (W.fieldMap k (P i)).1 U := by
    intro U
    simp only [cubeSumG_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact lsumG_apply P _
  have hX : ∀ i U, 0 ≤ cubeSumG (S.a k) R (W.fieldMap k (P i)).1 U :=
    fun i U => cubeSumG_nonneg (S.a k) R (F := (W.fieldMap k (P i)).1)
      (fun V => hpos i (W.V k V)) U
  calc S.ν k (cubeSumG (S.a k) R (W.fieldMap k (lsumG P)).1 ^ (2 * p))
      ≤ S.ν k ((Fintype.card ι : ℝ) ^ (2 * p)
          • ∑ i, cubeSumG (S.a k) R (W.fieldMap k (P i)).1 ^ (2 * p)) :=
        (S.ν k).mono fun U => by
          rw [ContinuousMap.pow_apply, hsplit, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
            smul_eq_mul]
          simp only [ContinuousMap.pow_apply]
          exact ObserverSymField.pow_sum_le_card_pow (fun i => hX i U) _
    _ = (Fintype.card ι : ℝ) ^ (2 * p)
          * ∑ i, S.ν k (cubeSumG (S.a k) R (W.fieldMap k (P i)).1 ^ (2 * p)) := by
        rw [(S.ν k).map_smul, (S.ν k).map_sum]
    _ ≤ (Fintype.card ι : ℝ) ^ (2 * p) * ∑ i, |C i| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hk i).trans (le_abs_self _))
          (by positivity)

/-- **(E) on the plaquette class over `G` gives (E) on the symmetrised class**, over a schedule
with `SchedAxisInv S` and a configuration flow commuting with the axis permutations.

DERIVED: no numeral. -/
theorem symPlaqG_cube (S : Sched G) (hA : SchedAxisInv S) (W : ConfFlowG G)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClassG G, CubeMomentBoundG S W O) :
    ∀ O ∈ SymPlaqClassG G, CubeMomentBoundG S W O := by
  rintro O ⟨q, rfl⟩
  have hq : plaqFieldG q ∈ PlaqClassG G := ⟨q, [], rfl⟩
  exact cubeMomentBoundG_lsum S W _
    (fun g U => plaqClassG_nonneg _ (reflFieldG_mem g.2 hq) _)
    (fun g => cubeMomentBoundG_axis S hA W hW (hcube _ (reflFieldG_mem g.2 hq)) g.1)

end Cube

/-! ## 4. At `SU(N)` -/

section SU

variable {N : ℕ} [NeZero N]

/-- At `SU(N)` the plaquette density over `G` is `ObserverEnergyMoments.plaqField`.

DERIVED: no numeral. -/
theorem plaqFieldG_SU (q : MassGap.GibbsSpec.IPlaq) :
    plaqFieldG (G := MassGap.SUN.SU N) q = ObserverEnergyMoments.plaqField q :=
  Subtype.ext (ContinuousMap.ext fun _ => rfl)

/-- DERIVED: no numeral. -/
theorem reflListG_SU (l : List (Fin 4)) (O : LField (MassGap.SUN.SU N)) :
    reflListG l O = reflList l O := rfl

omit [NeZero N] in
/-- DERIVED: no numeral. -/
theorem rpowG_SU (b : Bool) (τ : Fin 4) (V : IConf (MassGap.SUN.SU N)) :
    rpowG b τ V = ObserverSymField.rpow b τ V := by
  cases b <;> rfl

omit [NeZero N] in
/-- At `SU(N)` the reflections of `s` over `G` are `ObserverSymField.reflAll s`.

DERIVED: no numeral. -/
theorem reflAllG_SU (s : Fin 4 → Bool) (V : IConf (MassGap.SUN.SU N)) :
    reflAllG s V = ObserverSymField.reflAll s V := by
  simp only [reflAllG, ObserverSymField.reflAll, rpowG_SU]

/-- At `SU(N)` the symmetrised plaquette density over `G` is `ObserverSymField.sym (plaqField q)`.

DERIVED: no numeral. -/
theorem symG_plaqFieldG_SU (q : MassGap.GibbsSpec.IPlaq) :
    symG (plaqFieldG (G := MassGap.SUN.SU N) q)
      = ObserverSymField.sym (ObserverEnergyMoments.plaqField q) := by
  rw [plaqFieldG_SU]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  rw [symG_apply, ObserverSymField.sym_apply]
  exact Finset.sum_congr rfl fun g _ => by rw [reflAllG_SU]

variable (N) in
/-- At `SU(N)` the plaquette class over `G` is `PlaqClass N`.

DERIVED: no numeral. -/
theorem plaqClassG_SU : PlaqClassG (MassGap.SUN.SU N) = PlaqClass N := by
  unfold PlaqClassG PlaqClass
  simp only [plaqFieldG_SU, reflListG_SU]

variable (N) in
/-- At `SU(N)` the symmetrised class over `G` is `SymPlaqClass N`.

DERIVED: no numeral. -/
theorem symPlaqClassG_SU : SymPlaqClassG (MassGap.SUN.SU N) = ObserverSymField.SymPlaqClass N := by
  unfold SymPlaqClassG ObserverSymField.SymPlaqClass
  simp only [symG_plaqFieldG_SU]

variable (N) in
/-- **The schedule of `ClayStatement` is invariant under the axis permutations**:
`ContinuumHypercubic.stateK_axis`.

DERIVED: no numeral. -/
theorem schedAxisInv_SU : SchedAxisInv (schedSU N) :=
  fun k e F => stateK_axis (NeZero.ne N) k e F

end SU

/-! ## 5. The capstone at the symmetrised class -/

section Capstone

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring MassGap.ClayWiringG Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]
variable {τ : Fin 4} {r : ℝ}

/-- **`ClayStatementAtG G W (SymPlaqClassG G)` with `hpos` discharged and `hcube` reduced to the
plaquette class**: `EnergyBoundG.clayStatementAtG_of_inputsG''` at `D = SymPlaqClassG G` with
`hpos := symPlaqG_nonneg` and `hcube := symPlaqG_cube (canonSched G) hA W hW hcube`. In place of
`hpos` and `hcube` it takes `hW` (the flow commutes with the axis permutations), `hA`
(`SchedAxisInv (canonSched G)`) and `hcube` (`CubeMomentBoundG (canonSched G) W` on
`PlaqClassG G`); every other hypothesis is the same.

DERIVED: no numeral. -/
theorem clayStatementAtG_of_inputsG''' (W : ConfFlowG G)
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
    (hA : SchedAxisInv (canonSched G))
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
  clayStatementAtG_of_inputsG'' W (SymPlaqClassG G) X hSM hsa hXO op m Z hBC hRie b0 κ htr hop
    hZtie h0 hTC hCov Gk hK hAF hNG hND symPlaqG_nonneg
    (symPlaqG_cube (canonSched G) hA W hW hcube) hCut w hL hnt C wC hCT hWard hCD hCO hLC hTI
    hGen

/-- **`clayStatementAtG_of_inputsG'''` read at objects equal to its own**: the hypotheses and the
conclusion read at a schedule `S`, constants `K`, a class `D`, a plaquette class `P` and a field
`O₀`, with `S = canonSched G`, `K = constsG G`, `D = SymPlaqClassG G`, `P = PlaqClassG G` and
`O₀ = symG (plaqFieldG q0)`.

DERIVED: no numeral. -/
theorem clayStatementAtP_of_inputsG'''_at (S : Sched G) (hS : S = canonSched G) (K : ClayConsts)
    (hKc : K = constsG G) (D : Set (LField G)) (hDc : D = SymPlaqClassG G)
    (P : Set (LField G)) (hPc : P = PlaqClassG G)
    (O₀ : LField G) (hO₀ : O₀ = symG (plaqFieldG ObserverEnergyMoments.q0)) (W : ConfFlowG G)
    (X : OSDataSLinkedG G D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG S W D O g)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.base.time))
    (hXO : X.O = O₀)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = O₀)
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * S.a k ^ 4) atTop (𝓝 K.cTr))
    (h0 : OS0OwnG S op Z)
    (hTC : TransContTG S (mixOfZG B op m Z))
    (hCov : TensorCovG S (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG S (mixOfZG B op m Z) Gk)
    (hAF : AFCoefficientG K Gk)
    (hNG : NonGaussianTG S (mixOfZG B op m Z))
    (hND : TensorNondegG S (mixOfZG B op m Z))
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : IConf G),
      W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hA : SchedAxisInv S)
    (hcube : ∀ O ∈ P, CubeMomentBoundG S W O)
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG S (energyMapG S W D)
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG S W D O g)))
    (w : TSep τ → X.base.H)
    (hL : LinkHSG S W D X (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG S K Zc)
    (hWard : WardTG S (mixOfZG B op m Z)) (hCD : CompDataG C)
    (hCO : CompOSG S C) (hLC : LinkCG S X C wC)
    (hTI : TInG (mixOfZG B op m Z) C X w wC) (hGen : ObsGenG S W D X) :
    ClayStatementAtP S K W D := by
  subst hS
  subst hKc
  subst hDc
  subst hPc
  subst hO₀
  exact clayStatementAtG_of_inputsG''' W X hSM hsa hXO op m Z hBC hRie b0 κ htr hop hZtie h0 hTC
    hCov Gk hK hAF hNG hND hW hA hcube hCut w hL hnt C wC hCT hWard hCD hCO hLC hTI hGen

end Capstone

/-! ## 6. At `SU(N)`: `ClayWiring.clayStatementAt_of_inputs` through `G'''` -/

section SUCapstone

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring MassGap.ClayWiringG Filter
open scoped Topology Matrix

variable {N : ℕ}

set_option maxRecDepth 100000 in
/-- **`ClayWiring.clayStatementAt_of_inputs` through `clayStatementAtP_of_inputsG'''_at`**: the
hypotheses of `ClayWiring.clayStatementAt_of_inputs`, its conclusion, proved at `G = SU(N)`,
`S = schedSU N` (`= canonSched (SU N)`, `canonSched_SU`), `K = constsSU N` (`= constsG (SU N)`,
`constsG_SU`), `D = SymPlaqClass N` (`symPlaqClassG_SU`), `P = PlaqClass N` (`plaqClassG_SU`),
`O₀ = sym (plaqField q0)` (`symG_plaqFieldG_SU`) and `ClayStatementG.clayStatementAtP_SU_iff`. The
`G'''` inputs: `X = (obsX …).toG`, `hSM` = `obsX_SM`, `hsa` = the first clause of `obsX_gap`, `hXO`
by definition, `BasisConvG` = `basisConvG_SU` (`hZ`, `hD`), `hW` and `hcube` the `SU(N)` ones,
`SchedAxisInv` = `schedAxisInv_SU`.

DERIVED: `2` the least colour count; `0` the plane; `8` the bare normalisation `N/8` of
`ClayStatement.ScalarTie`; `4` the dimension. -/
theorem clayStatementAt_of_inputs_viaG''' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z) (hTC : TransContT hN (mixOfZ B op m Z))
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) Gk) (hAF : AFCoefficient N Gk)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)),
      (∀ i, O i ∈ SymPlaqClass N) → ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g)))
    (w : TSep 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hL : LinkHS hN W (SymPlaqClass N) (symPlaq_refl N)
      (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) (mixOfZ B op m Z) w)
    (hnt : ∃ u ∈ HLs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w,
      inner ℂ (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.vac u = 0 ∧ u ≠ 0)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) Cs wC)
    (hTI : TIn (mixOfZ B op m Z) Cs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  haveI : NeZero N := ⟨hN⟩
  haveI : Fact (2 ≤ N) := ⟨hN2⟩
  refine (clayStatementAtP_SU_iff hN2 W (SymPlaqClass N) (symPlaq_refl N)).1 ?_
  exact clayStatementAtP_of_inputsG'''_at (schedSU N) (canonSched_SU N).symm (constsSU N)
    (constsG_SU N).symm (SymPlaqClass N) (symPlaqClassG_SU N).symm (PlaqClass N)
    (plaqClassG_SU N).symm (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (symG_plaqFieldG_SU ObserverEnergyMoments.q0).symm W.toG
    (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).toG
    (obsX_SM hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)
    (obsX_gap hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).1 rfl op m Z
    (basisConvG_SU op Z hZ hD) hRie b0 κ htr hop hZtie h0 hTC hCov Gk hK hAF hNG hND
    hW (schedAxisInv_SU N) hcube hCut w hL hnt Cs.toG wC hCT hWard hCD hCO hLC hTI
    (obsX_obsGen hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)

end SUCapstone

end MassGap.SymPlaqG

end

#print axioms MassGap.SymPlaqG.plaqClassG_refl
#print axioms MassGap.SymPlaqG.plaqClassG_nonneg
#print axioms MassGap.SymPlaqG.reflFieldG_mem
#print axioms MassGap.SymPlaqG.iaxisConf_ireflConfG
#print axioms MassGap.SymPlaqG.ireflConf_commG
#print axioms MassGap.SymPlaqG.reflAllG_refl
#print axioms MassGap.SymPlaqG.symG_apply
#print axioms MassGap.SymPlaqG.symG_refl
#print axioms MassGap.SymPlaqG.symPlaqG_nonneg
#print axioms MassGap.SymPlaqG.symPlaqG_refl
#print axioms MassGap.SymPlaqG.symPlaqG_q0
#print axioms MassGap.SymPlaqG.cubeSumG_iaxis
#print axioms MassGap.SymPlaqG.fieldMapG_axis
#print axioms MassGap.SymPlaqG.cubeMomentBoundG_axis
#print axioms MassGap.SymPlaqG.cubeMomentBoundG_lsum
#print axioms MassGap.SymPlaqG.symPlaqG_cube
#print axioms MassGap.SymPlaqG.plaqFieldG_SU
#print axioms MassGap.SymPlaqG.reflAllG_SU
#print axioms MassGap.SymPlaqG.symG_plaqFieldG_SU
#print axioms MassGap.SymPlaqG.plaqClassG_SU
#print axioms MassGap.SymPlaqG.symPlaqClassG_SU
#print axioms MassGap.SymPlaqG.schedAxisInv_SU
#print axioms MassGap.SymPlaqG.clayStatementAtG_of_inputsG'''
#print axioms MassGap.SymPlaqG.clayStatementAtP_of_inputsG'''_at
#print axioms MassGap.SymPlaqG.clayStatementAt_of_inputs_viaG'''
