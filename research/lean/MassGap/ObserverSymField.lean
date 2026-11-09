import Mathlib
import MassGap.ObserverRotationDense

noncomputable section

/-!
# MassGap.ObserverSymField — a hypercubic-scalar energy density, and `SO(4)` for it

`ObserverRotationDense.observerSO4_energy0` holds at the `HypScalar` fields of the energy-density
class `D`. A single plaquette density is not invariant under the axis permutations, so
`PlaqClass N ∩ HypScalar` is empty, and that statement at `D = PlaqClass` is about no field. This
module gives the class a `HypScalar` member.

## The symmetrised field

`sym O` is the sum of `O` over the hypercubic group on configurations: for every axis permutation `e`
and every set of reflected axes `s : Fin 4 → Bool`,
`(sym O) U = ∑_{(e, s)} O (reflAll s (iaxisConf e U))` (`sym_apply`). It is a local gauge-invariant
field (`lsum`, a finite sum of fields). It is `HypScalar` (`sym_hypScalar`):
* relabelling: `iaxisConf e (iaxisConf e₀ U) = iaxisConf (e₀ e) U` (`iaxisConf_iaxisConf`), and
  `e ↦ e₀ e` permutes the sum;
* reflection: `iaxisConf e ∘ ireflConf τ = ireflConf (e⁻¹ τ) ∘ iaxisConf e` (`iaxisConf_ireflConf`),
  reflections of different axes commute (`ireflConf_comm`) and square to the identity, so
  `reflAll s ∘ ireflConf t = reflAll (s with t flipped)` (`reflAll_refl`), and flipping `t`
  permutes the sum.

`SymPlaqClass N = {sym (plaqField q)}`: the plaquette density summed over its 384 hypercubic images.
It is non-negative (`symPlaq_nonneg`), reflection closed (`symPlaq_refl`), every member is
`HypScalar` (`symPlaq_hypScalar`), and it is non-empty (`symPlaq_q0`).

## (E) for the symmetrised class from (E) for the plaquette class

`cubeMomentBound_axis`: for a configuration flow commuting with the axis permutations, the cube
moments of `lfieldAxis e O` equal those of `O` (the cube and the box are permutation symmetric,
`cubeSum_iaxis`, and the state is relabelling invariant, `stateK_axis`). `cubeMomentBound_lsum`: a
finite sum of non-negative fields with bounded cube moments has bounded cube moments,
`(∑ Xᵢ)^m ≤ n^m ∑ Xᵢ^m` for `Xᵢ ≥ 0` (`pow_sum_le_card_pow`). So `symPlaq_cube`: (E) on
`PlaqClass N` gives (E) on `SymPlaqClass N`.

## `SO(4)`

`observerSO4_symPlaq`: for a configuration flow commuting with the axis permutations, (E) on the
plaquette class and invariance under `pyth` on `SymPlaqClass` give `ObserverSO4` for the energy
density on `SymPlaqClass`; `observer2_so4_sym` (`SU(2)` APE observer) is the instance. The field `sym (plaqField q0)` is in the class it
covers. The one input not proved is invariance of the limit under `pyth`.

## Summary of the `SO(4)` reduction (state of the tree)

`ObserverRotation` proves the hypercubic group for the `SU(2)` observer, states `ObserverSO4` and
`OrbitContinuous`, proves `observerSO4_of_dense` and that `pyth` has infinite order. Its header says
the matrix-to-angle step, generation by plane rotations and orbit continuity are not formalised; they
are now: `SO4Planes.rot01_mem_closure`, `SO4Planes.so4_le_of_planes`,
`ObserverRotationDense.orbitContinuous_energy0`. `ObserverAxisN` carries the hypercubic group to every
block step and every `SU(N)`.
-/

namespace MassGap.ObserverSymField

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumHypercubic MassGap.ContinuumFlow MassGap.ObserverRotation MassGap.ObserverOS
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyBox MassGap.ObserverRotationDense
  MassGap.LatticeReflection Filter

variable {N : ℕ}

/-! ## 1. The hypercubic group on configurations -/

/-- Relabellings compose.

DERIVED: `4` the dimension. -/
theorem iaxisConf_iaxisConf (e e₀ : Equiv.Perm (Fin 4)) (U : Cfg N) :
    iaxisConf e (iaxisConf e₀ U) = iaxisConf (e₀ * e) U := by
  funext l
  rfl

#print axioms iaxisConf_iaxisConf

/-- The relabelled reflected site.

DERIVED: `4` the dimension. -/
theorem iaxisSite_ireflSite (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (c : ℤ) (x : ISite) :
    iaxisSite e (ireflSite (e.symm τ) c x) = ireflSite τ c (iaxisSite e x) := by
  funext j
  simp only [iaxisSite, ireflSite, Function.update_apply, Equiv.apply_eq_iff_eq]

#print axioms iaxisSite_ireflSite

/-- **A relabelling conjugates a reflection into the reflection of the relabelled axis.**

DERIVED: `0` the reflection constant. -/
theorem iaxisConf_ireflConf (e : Equiv.Perm (Fin 4)) (τ : Fin 4) (U : Cfg N) :
    iaxisConf e (ireflConf τ 0 U) = ireflConf (e.symm τ) 0 (iaxisConf e U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  have hiff : (e μ = τ) ↔ (μ = e.symm τ) :=
    ⟨fun h => by rw [← h, Equiv.symm_apply_apply], fun h => by rw [h, Equiv.apply_symm_apply]⟩
  simp only [iaxisConf, ireflConf, iaxisLink, ireflLink, hiff]
  split_ifs <;> first | rw [iaxisSite_ireflSite] | (exfalso; tauto)

#print axioms iaxisConf_ireflConf

/-- Reflections of different axes commute on sites.

DERIVED: `4` the dimension. -/
theorem ireflSite_comm {τ τ' : Fin 4} (hτ : τ ≠ τ') (a b : ℤ) (x : ISite) :
    ireflSite τ a (ireflSite τ' b x) = ireflSite τ' b (ireflSite τ a x) := by
  funext j
  simp only [ireflSite, Function.update_apply]
  by_cases h1 : j = τ
  · have h2 : j ≠ τ' := fun h => hτ (h1.symm.trans h)
    subst h1
    simp [h2, hτ, Ne.symm hτ]
  · by_cases h2 : j = τ'
    · subst h2
      simp [h1, hτ, Ne.symm hτ]
    · simp [h1, h2]

#print axioms ireflSite_comm

/-- Reflections of different axes commute on links.

DERIVED: `4` the dimension. -/
theorem ireflLink_comm {τ τ' : Fin 4} (hτ : τ ≠ τ') (c : ℤ) (l : ILink) :
    ireflLink τ c (ireflLink τ' c l) = ireflLink τ' c (ireflLink τ c l) := by
  obtain ⟨μ, x⟩ := l
  simp only [ireflLink]
  split_ifs <;> rw [ireflSite_comm hτ]

#print axioms ireflLink_comm

/-- **Reflections of different axes commute on configurations.**

DERIVED: `4` the dimension. -/
theorem ireflConf_comm {τ τ' : Fin 4} (hτ : τ ≠ τ') (c : ℤ) (U : Cfg N) :
    ireflConf τ c (ireflConf τ' c U) = ireflConf τ' c (ireflConf τ c U) := by
  funext l
  have hl := ireflLink_comm hτ c l
  by_cases h : l.1 = τ
  · have h' : l.1 ≠ τ' := fun h' => hτ (h.symm.trans h')
    simp only [ireflConf, ireflLink_fst, if_pos h, if_neg h', hl]
  · by_cases h' : l.1 = τ'
    · simp only [ireflConf, ireflLink_fst, if_pos h', if_neg h, hl]
    · simp only [ireflConf, ireflLink_fst, if_neg h', if_neg h, hl]

#print axioms ireflConf_comm

/-- The reflection of axis `τ` if `b`, the identity otherwise.

DERIVED: `0` the reflection constant. -/
def rpow : Bool → Fin 4 → Cfg N → Cfg N
  | true, τ, V => ireflConf τ 0 V
  | false, _, V => V

/-- DERIVED: `0` the reflection constant. -/
theorem rpow_comm {τ τ' : Fin 4} (hτ : τ ≠ τ') (b : Bool) (V : Cfg N) :
    rpow b τ (ireflConf τ' 0 V) = ireflConf τ' 0 (rpow b τ V) := by
  cases b
  · rfl
  · exact ireflConf_comm hτ 0 V

#print axioms rpow_comm

/-- DERIVED: `0` the reflection constant. -/
theorem rpow_self (b : Bool) (τ : Fin 4) (V : Cfg N) :
    rpow b τ (ireflConf τ 0 V) = rpow (!b) τ V := by
  cases b
  · rfl
  · exact ireflConf_involutive τ 0 V

#print axioms rpow_self

/-- The reflections of the axes in `s`, in the order `3, 2, 1, 0`.

DERIVED: `0`–`3` the axes. -/
def reflAll (s : Fin 4 → Bool) (V : Cfg N) : Cfg N :=
  rpow (s 0) 0 (rpow (s 1) 1 (rpow (s 2) 2 (rpow (s 3) 3 V)))

/-- `s` with the axis `t` flipped.

DERIVED: no numeral. -/
def flipB (s : Fin 4 → Bool) (t : Fin 4) : Fin 4 → Bool := Function.update s t (!s t)

/-- DERIVED: `0`–`3` the axes. -/
theorem reflAll_refl0 (s : Fin 4 → Bool) (V : Cfg N) :
    reflAll s (ireflConf 0 0 V) = reflAll (flipB s 0) V := by
  simp only [reflAll, rpow_comm (show (3 : Fin 4) ≠ 0 by decide),
    rpow_comm (show (2 : Fin 4) ≠ 0 by decide), rpow_comm (show (1 : Fin 4) ≠ 0 by decide),
    rpow_self]
  simp [flipB, Function.update_apply]

/-- DERIVED: `0`–`3` the axes. -/
theorem reflAll_refl1 (s : Fin 4 → Bool) (V : Cfg N) :
    reflAll s (ireflConf 1 0 V) = reflAll (flipB s 1) V := by
  simp only [reflAll, rpow_comm (show (3 : Fin 4) ≠ 1 by decide),
    rpow_comm (show (2 : Fin 4) ≠ 1 by decide), rpow_self]
  simp [flipB, Function.update_apply]

/-- DERIVED: `0`–`3` the axes. -/
theorem reflAll_refl2 (s : Fin 4 → Bool) (V : Cfg N) :
    reflAll s (ireflConf 2 0 V) = reflAll (flipB s 2) V := by
  simp only [reflAll, rpow_comm (show (3 : Fin 4) ≠ 2 by decide), rpow_self]
  simp [flipB, Function.update_apply]

/-- DERIVED: `0`–`3` the axes. -/
theorem reflAll_refl3 (s : Fin 4 → Bool) (V : Cfg N) :
    reflAll s (ireflConf 3 0 V) = reflAll (flipB s 3) V := by
  simp only [reflAll, rpow_self]
  simp [flipB, Function.update_apply]

/-- **A reflection after the reflections of `s` is the reflections of `s` with that axis flipped.**

DERIVED: `0` the reflection constant. -/
theorem reflAll_refl (s : Fin 4 → Bool) (t : Fin 4) (V : Cfg N) :
    reflAll s (ireflConf t 0 V) = reflAll (flipB s t) V := by
  fin_cases t
  · exact reflAll_refl0 s V
  · exact reflAll_refl1 s V
  · exact reflAll_refl2 s V
  · exact reflAll_refl3 s V

#print axioms reflAll_refl

/-- Flipping one axis is an involution of the sets of axes.

DERIVED: no numeral. -/
def flipEquiv (t : Fin 4) : Equiv.Perm (Fin 4 → Bool) :=
  Function.Involutive.toPerm (fun s => flipB s t) (fun s => by simp [flipB])

/-! ## 2. Sums of fields and the symmetrised field -/

/-- **A finite sum of local gauge-invariant fields.**

DERIVED: no numeral. -/
def lsum {ι : Type} [Fintype ι] (P : ι → LField (MassGap.SUN.SU N)) : LField (MassGap.SUN.SU N) :=
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

/-- DERIVED: no numeral. -/
theorem lsum_apply {ι : Type} [Fintype ι] (P : ι → LField (MassGap.SUN.SU N)) (U : Cfg N) :
    (lsum P).1 U = ∑ i, (P i).1 U := by
  show (∑ i, (P i).1) U = _
  simp only [ContinuousMap.sum_apply]

#print axioms lsum_apply

/-- The field reflected in axis `τ` if `b`.

DERIVED: no numeral. -/
def lrpow : Bool → Fin 4 → LField (MassGap.SUN.SU N) → LField (MassGap.SUN.SU N)
  | true, τ, O => O.refl τ
  | false, _, O => O

/-- DERIVED: `0` the reflection constant. -/
theorem lrpow_apply (b : Bool) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (V : Cfg N) :
    (lrpow b τ O).1 V = O.1 (rpow b τ V) := by
  cases b <;> rfl

#print axioms lrpow_apply

/-- The field read through the reflections of `s`.

DERIVED: `0`–`3` the axes. -/
def reflField (s : Fin 4 → Bool) (O : LField (MassGap.SUN.SU N)) : LField (MassGap.SUN.SU N) :=
  lrpow (s 3) 3 (lrpow (s 2) 2 (lrpow (s 1) 1 (lrpow (s 0) 0 O)))

/-- DERIVED: `0`–`3` the axes. -/
theorem reflField_apply (s : Fin 4 → Bool) (O : LField (MassGap.SUN.SU N)) (V : Cfg N) :
    (reflField s O).1 V = O.1 (reflAll s V) := by
  rw [reflField, lrpow_apply, lrpow_apply, lrpow_apply, lrpow_apply]
  rfl

#print axioms reflField_apply

/-- **The symmetrised field**: `O` summed over the hypercubic group.

DERIVED: `4` the dimension; `384 = 4! · 2⁴` terms. -/
def sym (O : LField (MassGap.SUN.SU N)) : LField (MassGap.SUN.SU N) :=
  lsum (fun g : Equiv.Perm (Fin 4) × (Fin 4 → Bool) => lfieldAxis g.1 (reflField g.2 O))

/-- DERIVED: `4` the dimension. -/
theorem sym_apply (O : LField (MassGap.SUN.SU N)) (U : Cfg N) :
    (sym O).1 U = ∑ g : Equiv.Perm (Fin 4) × (Fin 4 → Bool), O.1 (reflAll g.2 (iaxisConf g.1 U)) := by
  unfold sym
  rw [lsum_apply]
  exact Finset.sum_congr rfl fun g _ => reflField_apply g.2 O (iaxisConf g.1 U)

#print axioms sym_apply

/-- DERIVED: `4` the dimension. -/
theorem lfieldAxis_apply (e : Equiv.Perm (Fin 4)) (O : LField (MassGap.SUN.SU N)) (U : Cfg N) :
    (lfieldAxis e O).1 U = O.1 (iaxisConf e U) := rfl

/-- DERIVED: `0` the reflection constant. -/
theorem lrefl_apply (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (U : Cfg N) :
    (LField.refl τ O).1 U = O.1 (ireflConf τ 0 U) := rfl

/-- **The symmetrised field is invariant under the axis permutations.**

DERIVED: `4` the dimension. -/
theorem sym_axis (O : LField (MassGap.SUN.SU N)) (e₀ : Equiv.Perm (Fin 4)) :
    lfieldAxis e₀ (sym O) = sym O := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  rw [lfieldAxis_apply]
  rw [sym_apply, sym_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [iaxisConf_iaxisConf]
  exact Fintype.sum_equiv (Equiv.mulLeft e₀) _ _ (fun e => rfl)

#print axioms sym_axis

/-- **The symmetrised field is invariant under the axis reflections.**

DERIVED: `0` the reflection constant. -/
theorem sym_refl (O : LField (MassGap.SUN.SU N)) (τ₀ : Fin 4) : LField.refl τ₀ (sym O) = sym O := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  rw [lrefl_apply]
  rw [sym_apply, sym_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [iaxisConf_ireflConf, reflAll_refl]
  exact Fintype.sum_equiv (flipEquiv (e.symm τ₀)) _ _ (fun s => rfl)

#print axioms sym_refl

/-- **The symmetrised field is a hypercubic scalar.**

DERIVED: `4` the dimension. -/
theorem sym_hypScalar (O : LField (MassGap.SUN.SU N)) : HypScalar (sym O) :=
  ⟨fun e => sym_axis O e, fun τ => sym_refl O τ⟩

#print axioms sym_hypScalar

/-! ## 3. The symmetrised plaquette class -/

/-- **The symmetrised plaquette class**: each plaquette density summed over its hypercubic images.

DERIVED: `4` the dimension. -/
def SymPlaqClass (N : ℕ) : Set (LField (MassGap.SUN.SU N)) :=
  {O | ∃ q : MassGap.GibbsSpec.IPlaq, O = sym (plaqField q)}

/-- DERIVED: `4` the dimension. -/
theorem symPlaq_hypScalar : ∀ O ∈ SymPlaqClass N, HypScalar O := by
  rintro O ⟨q, rfl⟩
  exact sym_hypScalar _

#print axioms symPlaq_hypScalar

/-- **The symmetrised class is reflection closed**: its members are reflection invariant.

DERIVED: `4` the dimension. -/
theorem symPlaq_refl (N : ℕ) :
    ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ SymPlaqClass N ↔ O ∈ SymPlaqClass N := by
  intro τ O
  constructor
  · intro h
    have hO : O = O.refl τ := (refl_refl τ O).symm.trans ((symPlaq_hypScalar _ h).2 τ)
    rw [hO]
    exact h
  · intro h
    rw [(symPlaq_hypScalar O h).2 τ]
    exact h

#print axioms symPlaq_refl

/-- A reflected plaquette field stays in the plaquette class.

DERIVED: no numeral. -/
theorem reflField_mem (s : Fin 4 → Bool) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ PlaqClass N) :
    reflField s O ∈ PlaqClass N := by
  have h : ∀ (b : Bool) (τ : Fin 4) (P : LField (MassGap.SUN.SU N)), P ∈ PlaqClass N →
      lrpow b τ P ∈ PlaqClass N := by
    intro b τ P hP
    cases b
    · exact hP
    · exact (plaqClass_refl N τ P).mpr hP
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ hO)))

#print axioms reflField_mem

/-- **The symmetrised class is non-negative.**

DERIVED: `0` the excluded colour count and the sign. -/
theorem symPlaq_nonneg (hN : N ≠ 0) : ∀ O ∈ SymPlaqClass N, ∀ U, 0 ≤ O.1 U := by
  rintro O ⟨q, rfl⟩ U
  rw [sym_apply]
  exact Finset.sum_nonneg fun g _ => plaqClass_nonneg hN _ ⟨q, [], rfl⟩ _

#print axioms symPlaq_nonneg

/-- **The class is non-empty**: the symmetrised plaquette density at the origin, a hypercubic scalar.

DERIVED: `q0` the `(0, 1)` plaquette at the origin. -/
theorem symPlaq_q0 :
    sym (plaqField q0) ∈ {O : LField (MassGap.SUN.SU N) | O ∈ SymPlaqClass N ∧ HypScalar O} :=
  ⟨⟨q0, rfl⟩, sym_hypScalar _⟩

#print axioms symPlaq_q0

/-! ## 4. (E) for the symmetrised class -/

/-- The box is permutation symmetric.

DERIVED: `4` the dimension. -/
theorem mem_box_iaxis (e : Equiv.Perm (Fin 4)) (K : ℕ) (x : ISite) :
    x ∈ box K ↔ iaxisSite e x ∈ box K := by
  simp only [box, Fintype.mem_piFinset]
  constructor
  · intro h i
    exact h (e.symm i)
  · intro h i
    have := h (e i)
    simpa [iaxisSite] using this

#print axioms mem_box_iaxis

/-- The cube indicator is permutation symmetric.

DERIVED: `1`, `0` the indicator's values. -/
theorem cubeInd_iaxis (R a : ℝ) (e : Equiv.Perm (Fin 4)) (x : ISite) :
    cubeInd R (site a (iaxisSite e x)) = cubeInd R (site a x) := by
  have hiff : (∀ i, |site a (iaxisSite e x) i| ≤ R) ↔ (∀ i, |site a x i| ≤ R) := by
    constructor
    · intro h i
      have h' := h (e i)
      simp only [site, iaxisSite, Equiv.symm_apply_apply] at h'
      exact h'
    · intro h i
      exact h (e.symm i)
  unfold cubeInd
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

#print axioms cubeInd_iaxis

/-- **The cube energy of a relabelled reading** is the relabelled cube energy.

DERIVED: `4` the dimension. -/
theorem cubeSum_iaxis (a R : ℝ) (e : Equiv.Perm (Fin 4)) (F : C(Cfg N, ℝ)) (U : Cfg N) :
    cubeSum a R (iaxisObs e F) U = cubeSum a R F (iaxisConf e U) := by
  rw [cubeSum_apply, cubeSum_apply]
  symm
  refine Finset.sum_equiv (iaxisSitePerm e) (fun x => mem_box_iaxis e _ x) (fun x _ => ?_)
  show cubeInd R (site a x) * F (transConf x (iaxisConf e U))
    = cubeInd R (site a (iaxisSite e x)) * F (iaxisConf e (transConf (iaxisSite e x) U))
  rw [cubeInd_iaxis, iaxisConf_transConf]

#print axioms cubeSum_iaxis

/-- **(E) is relabelling invariant** for a configuration flow commuting with the relabellings: the
cube moments of `lfieldAxis e O` are those of `O`.

DERIVED: `0` the excluded colour count; `2` the even power. -/
theorem cubeMomentBound_axis (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    {O : LField (MassGap.SUN.SU N)} (hO : CubeMomentBound hN W O) (e : Equiv.Perm (Fin 4)) :
    CubeMomentBound hN W (lfieldAxis e O) := by
  intro R hR p
  obtain ⟨C, hC⟩ := hO R hR p
  refine ⟨C, hC.mono fun k hk => ?_⟩
  have h : cubeSum (dySpacing N k) R (W.fieldMap k (lfieldAxis e O)).1 ^ (2 * p)
      = iaxisObs e (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p)) := by
    ext U
    rw [ContinuousMap.pow_apply]
    show _ = (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p)) (iaxisConf e U)
    rw [ContinuousMap.pow_apply, ConfFlow.fieldMap_axis W hW k e O]
    exact congrArg (· ^ (2 * p)) (cubeSum_iaxis _ R e _ U)
  rw [h, stateK_axis]
  exact hk

#print axioms cubeMomentBound_axis

/-- `(∑ Xᵢ)^m ≤ n^m ∑ Xᵢ^m` for non-negative `Xᵢ`: the sum is at most `n` times the largest term.

DERIVED: no numeral. -/
theorem pow_sum_le_card_pow {ι : Type} [Fintype ι] [Nonempty ι] {X : ι → ℝ} (hX : ∀ i, 0 ≤ X i)
    (m : ℕ) : (∑ i, X i) ^ m ≤ (Fintype.card ι : ℝ) ^ m * ∑ i, X i ^ m := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ X Finset.univ_nonempty
  have h1 : ∑ i, X i ≤ Fintype.card ι * X j := by
    calc ∑ i, X i ≤ ∑ _i : ι, X j := Finset.sum_le_sum fun i _ => hj i (Finset.mem_univ i)
      _ = Fintype.card ι * X j := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (∑ i, X i) ^ m ≤ (Fintype.card ι * X j) ^ m :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hX i) h1 m
    _ = (Fintype.card ι : ℝ) ^ m * X j ^ m := mul_pow _ _ _
    _ ≤ (Fintype.card ι : ℝ) ^ m * ∑ i, X i ^ m :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => X i ^ m)
          (fun i _ => pow_nonneg (hX i) m) (Finset.mem_univ j)) (by positivity)

#print axioms pow_sum_le_card_pow

/-- **(E) for a finite sum of non-negative fields** from (E) for each.

DERIVED: `0` the excluded colour count and the sign; `2` the even power. -/
theorem cubeMomentBound_lsum (hN : N ≠ 0) (W : ConfFlow N) {ι : Type} [Fintype ι] [Nonempty ι]
    (P : ι → LField (MassGap.SUN.SU N)) (hpos : ∀ i U, 0 ≤ (P i).1 U)
    (hP : ∀ i, CubeMomentBound hN W (P i)) : CubeMomentBound hN W (lsum P) := by
  intro R hR p
  choose C hC using fun i => hP i R hR p
  refine ⟨(Fintype.card ι : ℝ) ^ (2 * p) * ∑ i, |C i|, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hC] with k hk
  have hsplit : ∀ U, cubeSum (dySpacing N k) R (W.fieldMap k (lsum P)).1 U
      = ∑ i, cubeSum (dySpacing N k) R (W.fieldMap k (P i)).1 U := by
    intro U
    simp only [cubeSum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact lsum_apply P _
  have hX : ∀ i U, 0 ≤ cubeSum (dySpacing N k) R (W.fieldMap k (P i)).1 U :=
    fun i U => cubeSum_nonneg (dySpacing N k) R (F := (W.fieldMap k (P i)).1) (fun V => hpos i (W.V k V)) U
  calc stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (lsum P)).1 ^ (2 * p))
      ≤ stateK hN k ((Fintype.card ι : ℝ) ^ (2 * p)
          • ∑ i, cubeSum (dySpacing N k) R (W.fieldMap k (P i)).1 ^ (2 * p)) :=
        (stateK hN k).mono fun U => by
          rw [ContinuousMap.pow_apply, hsplit, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
            smul_eq_mul]
          simp only [ContinuousMap.pow_apply]
          exact pow_sum_le_card_pow (fun i => hX i U) _
    _ = (Fintype.card ι : ℝ) ^ (2 * p)
          * ∑ i, stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (P i)).1 ^ (2 * p)) := by
        rw [(stateK hN k).map_smul, (stateK hN k).map_sum]
    _ ≤ (Fintype.card ι : ℝ) ^ (2 * p) * ∑ i, |C i| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hk i).trans (le_abs_self _))
          (by positivity)

#print axioms cubeMomentBound_lsum

/-- **(E) on the plaquette class gives (E) on the symmetrised class.**

DERIVED: `0` the excluded colour count. -/
theorem symPlaq_cube (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) :
    ∀ O ∈ SymPlaqClass N, CubeMomentBound hN W O := by
  rintro O ⟨q, rfl⟩
  have hq : plaqField q ∈ PlaqClass N := ⟨q, [], rfl⟩
  exact cubeMomentBound_lsum hN W _
    (fun g U => plaqClass_nonneg hN _ (reflField_mem g.2 hq) _)
    (fun g => cubeMomentBound_axis hN W hW (hcube _ (reflField_mem g.2 hq)) g.1)

#print axioms symPlaq_cube

/-! ## 5. `SO(4)` on the symmetrised class -/

/-- **`SO(4)` for the symmetrised energy density from (E) on the plaquette class and `pyth`.**

DERIVED: `0` the excluded colour count; `4` the dimension. -/
theorem observerSO4_symPlaq (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F) :
    ObserverSO4 hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      {O | O ∈ SymPlaqClass N ∧ HypScalar O} :=
  observerSO4_energy0 hN W hW (symPlaq_refl N) (symPlaq_nonneg hN) (symPlaq_cube hN W hW hcube) hpyth

#print axioms observerSO4_symPlaq

/-- **The `SU(2)` APE observer on the symmetrised class.**

DERIVED: `2` the rank; `1/6` the dominance bound. -/
theorem observer2_so4_sym {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (hcube : ∀ O ∈ PlaqClass 2,
      CubeMomentBound ObserverClay.two_ne (ObserverFlow.obsConfFlow c hc0 hc n R) O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField 2),
      (∀ i, (F i).1 ∈ SymPlaqClass 2 ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF ObserverClay.two_ne
            (energy0 (ObserverFlow.obsConfFlow c hc0 hc n R) (SymPlaqClass 2) (symPlaq_refl 2))
            (rotFam pyth F)
          = contSF ObserverClay.two_ne
            (energy0 (ObserverFlow.obsConfFlow c hc0 hc n R) (SymPlaqClass 2) (symPlaq_refl 2)) F) :
    ObserverSO4 ObserverClay.two_ne
      (energy0 (ObserverFlow.obsConfFlow c hc0 hc n R) (SymPlaqClass 2) (symPlaq_refl 2))
      {O | O ∈ SymPlaqClass 2 ∧ HypScalar O} :=
  observerSO4_symPlaq ObserverClay.two_ne _ (fun k e U => obsConfFlow_iaxis hc0 hc n R k e U) hcube
    hpyth

#print axioms observer2_so4_sym

end MassGap.ObserverSymField
