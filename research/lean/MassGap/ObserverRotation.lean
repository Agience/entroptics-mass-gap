import Mathlib
import MassGap.ContinuumHypercubic
import MassGap.ApeLattice
import MassGap.ContinuumFlow
import MassGap.LocalApe
import MassGap.ObserverFlow

noncomputable section

/-!
# MassGap.ObserverRotation — Euclidean invariance of the observer's continuum Schwinger functions

The observer's continuum theory is `ContinuumFlow.contSF` of a `ContinuumFlow.Flow`; its energy density
is the localised APE flow `ObserverFlow.obsConfFlow` with the canonical factor `a⁻⁴`. `ContinuumFlow` proves the dyadic translations (`contSF_translate`) and the axis reflections
(`contSF_reflect`) for every flow. This module adds the rest of the hypercubic group for the observer and
reduces what remains of `SO(4)` to two named statements.

## 1. The observer's step commutes with the axis permutations

`apeStaple_iaxis`: the staples of the relabelled configuration `ContinuumHypercubic.iaxisConf e U` at
`(μ, x)` are the staples of `U` at `(e μ, iaxisSite e x)`, the transverse directions relabelled by `e`.
`apeConf_iaxis`: one APE step commutes with the relabelling (`BlockSU2.blockLink_perm`; the six staples
are permuted by `stapleAxis`). `apeOnIter_iaxis` carries it to the step run on a set of links, and
`obsFlow_iaxis` to the observer: the midpoint boxes are relabelled onto midpoint boxes (`mid_iaxisLink`).
So `obsConfFlow` commutes with every axis permutation at every step (`obsConfFlow_iaxis`).

## 2. The hypercubic group on the observer's continuum theory

`Flow.AxisCov Φ`: the flow commutes with the axis permutations. Under it `latSF_axis` (every step) and
`contSF_axis` (the limit) give invariance under relabelling every field and test function; with
`contSF_reflect` every word in the generators (`contSF_hyp`), and at fields fixed by the lattice
hypercubic group, composing every test function with any signed permutation of `ℝ⁴` (`contSF_signed`).

## 3. `SO(4)` from a dense set and continuity

`rotTest A f` is `f ∘ A` for `Aᵀ A = 1` (support bound `rotTest_support`, through `y = Aᵀ (A y)`), and
`rotFam A F` the family with every test function rotated, fields kept. `ObserverSO4 hN Φ Φs` is the
rotation statement for the flowed theory: for every `A ∈ SO(4)` and every family of `Φs`-fields with
uniformly continuous test functions, `contSF (rotFam A F) = contSF F`. `OrbitContinuous hN Φ F`:
`A ↦ contSF (rotFam A F)` is continuous on `SO(4)`. `eq_on_of_dense`: a function continuous on a set
`S` and constant on a subset `D` with `S ⊆ closure D` is constant on `S`. `observerSO4_of_dense`: orbit
continuity plus invariance on a set `D ⊆ SO(4)` dense in `SO(4)` give `ObserverSO4`.

## 4. One rotation outside the hypercubic group

`pyth` is the rotation by `(3/5, 4/5)` in the plane of the first two axes. It lies in `SO(4)`
(`pyth_mem`), is not a signed permutation (`pyth_not_signed`), and has infinite order
(`pyth_pow_ne_one`): its powers are `(3 + 4i)ⁿ / 5ⁿ`, and `(3 + 4i)ⁿ ≡ 3 + 4i (mod 5)` (`pythInt_mod`),
so the imaginary part is never `0`. Its angle is therefore an irrational multiple of `2π`, and its powers
are dense in the rotations of that plane (`AddCircle.denseRange_zsmul_coe_iff`; the passage from
matrices to angles is not formalised here). No lattice identity carries `pyth`: it maps the axis vector
`e₀` to `(3/5, 4/5, 0, 0)`, which is not a lattice vector (`pyth_not_lattice`), so the lattice functions
at a fixed spacing are not related by it. Invariance of the limit under `pyth` is the first
non-hypercubic instance of `ObserverSO4`, and it is not proved.

## Scope

Proved: the hypercubic group for a flow commuting with the axis permutations, at every step and in the limit, and the reduction
of `SO(4)` to orbit continuity plus invariance on a dense subset. Stated, not proved here:
`OrbitContinuous` for the energy density, and invariance under any rotation that is not a signed
permutation. The first follows from (E) at non-negative fields (the plaquette class, `s = 0`) and
uniformly continuous test functions by an argument not formalised here: a smeared non-negative field
moves by at most the sup-norm change of its test function times the cube energy, so by Hölder the
lattice functions are Lipschitz in the sup norm uniformly in the step, with a constant from the cube
moments; and a uniformly continuous test function of bounded support moves little in the sup norm under
a small rotation. The second is the restoration of rotation symmetry, which no lattice identity gives.
-/

namespace MassGap.ObserverRotation

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumHypercubic MassGap.ContinuumFlow Filter
open scoped Topology Matrix

/-! ## 1. The observer's step commutes with the axis permutations -/

section Step

open MassGap.BlockLattice MassGap.BlockSU2 MassGap.ApeLattice MassGap.LocalApe MassGap.ObserverFlow

/-- The backward step commutes with the relabelling.

DERIVED: `1` is one lattice step, through `ishift` and `iback`. -/
theorem iback_iaxisSite (e : Equiv.Perm (Fin 4)) (ν : Fin 4) (x : ISite) :
    iaxisSite e (iback ν x) = iback (e ν) (iaxisSite e x) := by
  have h := ishift_iaxisSite e ν (iback ν x)
  rw [ishift_iback] at h
  rw [← h, ReflApe.iback_ishift]

#print axioms iback_iaxisSite

/-- **The staples of the relabelled configuration** at `(μ, x)` are the staples of `U` at
`(e μ, iaxisSite e x)`, with the transverse direction `other μ j` relabelled to `e (other μ j)`.

DERIVED: `0` names the upper side; `3 = 4 − 1` the directions transverse to `μ` (`other μ`). -/
theorem apeStaple_iaxis (e : Equiv.Perm (Fin 4)) (U : IConf G2) (μ : Fin 4) (x : ISite)
    (j j' : Fin 3) (sd : Fin 2) (h : other (e μ) j' = e (other μ j)) :
    apeStaple (iaxisConf e U) μ x (j, sd) = apeStaple U (e μ) (iaxisSite e x) (j', sd) := by
  simp only [apeStaple, h, iaxisConf, iaxisLink, ← ishift_iaxisSite, iback_iaxisSite]

#print axioms apeStaple_iaxis

/-- The relabelled transverse direction is a transverse direction of `e μ`.

DERIVED: `3` is the number of transverse directions. -/
theorem exists_other (e : Equiv.Perm (Fin 4)) (μ : Fin 4) (j : Fin 3) :
    ∃ j', other (e μ) j' = e (other μ j) :=
  Fin.exists_succAbove_eq (fun h => LocalApe.other_ne μ j (e.injective h).symm)

#print axioms exists_other

/-- The transverse relabelling `j ↦ j'`.

DERIVED: `3` is the number of transverse directions. -/
def otherMap (e : Equiv.Perm (Fin 4)) (μ : Fin 4) (j : Fin 3) : Fin 3 :=
  (exists_other e μ j).choose

/-- DERIVED: `3` is the number of transverse directions. -/
theorem other_otherMap (e : Equiv.Perm (Fin 4)) (μ : Fin 4) (j : Fin 3) :
    other (e μ) (otherMap e μ j) = e (other μ j) :=
  (exists_other e μ j).choose_spec

#print axioms other_otherMap

/-- The transverse relabelling is a permutation of the three transverse directions.

DERIVED: `3` is the number of transverse directions. -/
def otherPerm (e : Equiv.Perm (Fin 4)) (μ : Fin 4) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (otherMap e μ) (Finite.injective_iff_bijective.mp (fun j₁ j₂ h => by
    have h1 := other_otherMap e μ j₁
    have h2 := other_otherMap e μ j₂
    rw [h] at h1
    exact Fin.succAbove_right_injective (e.injective (h1.symm.trans h2))))

/-- The staple reindexing under the relabelling, as a permutation of the six staples.

DERIVED: `6 = 3 · 2` staples. -/
def stapleAxis (e : Equiv.Perm (Fin 4)) (μ : Fin 4) : Equiv.Perm (Fin 6) :=
  (finProdFinEquiv.symm.trans (Equiv.prodCongr (otherPerm e μ) (Equiv.refl (Fin 2)))).trans
    finProdFinEquiv

/-- **One APE step commutes with the axis permutations**: `apeConf (e · U) = e · (apeConf U)`.

DERIVED: `1/6` the dominance bound. -/
theorem apeConf_iaxis {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (e : Equiv.Perm (Fin 4))
    (U : IConf G2) : apeConf c hc0 hc (iaxisConf e U) = iaxisConf e (apeConf c hc0 hc U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  have hS : (fun i => apeStaple (iaxisConf e U) μ x (finProdFinEquiv.symm i))
      = (fun i => apeStaple U (e μ) (iaxisSite e x) (finProdFinEquiv.symm i)) ∘ stapleAxis e μ := by
    funext i
    simp only [Function.comp, stapleAxis, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
    exact apeStaple_iaxis e U μ x _ _ _ (other_otherMap e μ _)
  show blockLink c hc0 hc (iaxisConf e U (μ, x))
      (fun i => apeStaple (iaxisConf e U) μ x (finProdFinEquiv.symm i))
    = blockLink c hc0 hc (U (e μ, iaxisSite e x))
      (fun i => apeStaple U (e μ) (iaxisSite e x) (finProdFinEquiv.symm i))
  rw [hS, blockLink_perm]
  rfl

#print axioms apeConf_iaxis

/-- **The localised step commutes with the relabelling**, the set of links relabelled with it.

DERIVED: `1/6` the dominance bound. -/
theorem apeOn_iaxis {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (e : Equiv.Perm (Fin 4))
    (S T : Set ILink) (hT : ∀ l, iaxisLink e l ∈ T ↔ l ∈ S) (U : IConf G2) :
    apeOn c hc0 hc S (iaxisConf e U) = iaxisConf e (apeOn c hc0 hc T U) := by
  classical
  funext l
  have key := congrFun (apeConf_iaxis hc0 hc e U) l
  have hl := hT l
  simp only [apeOn, iaxisConf] at key ⊢
  by_cases h : l ∈ S
  · rw [if_pos h, if_pos (hl.mpr h)]
    exact key
  · rw [if_neg h, if_neg (fun h' => h (hl.mp h'))]

#print axioms apeOn_iaxis

/-- Iterates of the localised step commute with the relabelling.

DERIVED: `0` is the base of the induction; `6 = 3 · 2` the staples (`1/6` the dominance bound). -/
theorem apeOnIter_iaxis {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (e : Equiv.Perm (Fin 4))
    (S T : Set ILink) (hT : ∀ l, iaxisLink e l ∈ T ↔ l ∈ S) (n : ℕ) (U : IConf G2) :
    (apeOn c hc0 hc S)^[n] (iaxisConf e U) = iaxisConf e ((apeOn c hc0 hc T)^[n] U) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, apeOn_iaxis hc0 hc e S T hT, ih]

#print axioms apeOnIter_iaxis

/-- The midpoint of a relabelled link is the relabelled midpoint.

DERIVED: `2` and `1` as in `ObserverFlow.mid`. -/
theorem mid_iaxisLink (e : Equiv.Perm (Fin 4)) (l : ILink) (j : Fin 4) :
    mid (iaxisLink e l) j = mid l (e.symm j) := by
  obtain ⟨μ, x⟩ := l
  simp only [mid, iaxisLink, iaxisSite]
  congr 1
  by_cases h : e μ = j
  · rw [if_pos h, if_pos (by rw [← h, Equiv.symm_apply_apply])]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', Equiv.apply_symm_apply]))]

#print axioms mid_iaxisLink

/-- **The relabelling maps midpoint boxes onto midpoint boxes.**

DERIVED: `2` converts the half-width to doubled coordinates, as in `ObserverFlow.mbox`. -/
theorem mem_mbox_iaxis (e : Equiv.Perm (Fin 4)) (l0 l : ILink) (R : ℕ) :
    iaxisLink e l ∈ mbox (iaxisLink e l0) R ↔ l ∈ mbox l0 R := by
  simp only [mbox, Set.mem_setOf_eq, mid_iaxisLink]
  constructor
  · intro h i
    have := h (e i)
    rwa [Equiv.symm_apply_apply] at this
  · intro h j
    exact h (e.symm j)

#print axioms mem_mbox_iaxis

/-- **The observer flow commutes with the axis permutations.**

DERIVED: `1/6` the dominance bound. -/
theorem obsFlow_iaxis {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (e : Equiv.Perm (Fin 4))
    (U : IConf G2) : obsFlow c hc0 hc n R (iaxisConf e U) = iaxisConf e (obsFlow c hc0 hc n R U) := by
  funext l
  show (apeOn c hc0 hc (mbox l R))^[n] (iaxisConf e U) l
    = (apeOn c hc0 hc (mbox (iaxisLink e l) R))^[n] U (iaxisLink e l)
  rw [apeOnIter_iaxis hc0 hc e (mbox l R) (mbox (iaxisLink e l) R)
    (fun l' => mem_mbox_iaxis e l l' R)]
  rfl

#print axioms obsFlow_iaxis

/-- The observer's configuration flow commutes with the axis permutations at every step.

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
theorem obsConfFlow_iaxis {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) (k : ℕ)
    (e : Equiv.Perm (Fin 4)) (U : IConf G2) :
    (obsConfFlow c hc0 hc n R).V k (iaxisConf e U) = iaxisConf e ((obsConfFlow c hc0 hc n R).V k U) :=
  obsFlow_iaxis hc0 hc (n k) (R k) e U

#print axioms obsConfFlow_iaxis

end Step

/-! ## 2. The hypercubic group on the observer's continuum theory -/

section Hyp

variable {N : ℕ}

/-- **A flow commuting with the axis permutations.**

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def Flow.AxisCov (Φ : Flow N) : Prop :=
  ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (O : LField (MassGap.SUN.SU N)),
    Φ.map k (lfieldAxis e O) = lfieldAxis e (Φ.map k O)

/-- A configuration flow commuting with the relabelling gives a field map commuting with it.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem ConfFlow.fieldMap_axis (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (k : ℕ) (e : Equiv.Perm (Fin 4)) (O : LField (MassGap.SUN.SU N)) :
    W.fieldMap k (lfieldAxis e O) = lfieldAxis e (W.fieldMap k O) :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (iaxisConf e (W.V k U)) = O.1 (W.V k (iaxisConf e U))
    rw [hW]))

#print axioms ConfFlow.fieldMap_axis

/-- Scaling commutes with the relabelling.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem scaleField_axis (e : Equiv.Perm (Fin 4)) (O : LField (MassGap.SUN.SU N)) (s : ℝ) :
    lfieldAxis e (scaleField O s) = scaleField (lfieldAxis e O) s :=
  Subtype.ext (by
    show iaxisObs e (s • O.1) = s • iaxisObs e O.1
    rw [map_smul])

#print axioms scaleField_axis

/-- **The scaled configuration flow commutes with the relabelling** when the configuration flow does
and the factor and subtraction do not see it.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem ofConfScaled_axisCov (W : ConfFlow N) (z c : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (hc : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), c k (O.refl τ) = c k O)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hza : ∀ k e O, z k (lfieldAxis e O) = z k O) (hca : ∀ k e O, c k (lfieldAxis e O) = c k O) :
    Flow.AxisCov (Flow.ofConfScaled W z c hz hc) := by
  intro k e O
  show scaleField ((W.fieldMap k (lfieldAxis e O)).sub (c k (lfieldAxis e O))) (z k (lfieldAxis e O))
    = lfieldAxis e (scaleField ((W.fieldMap k O).sub (c k O)) (z k O))
  rw [scaleField_axis, lfieldAxis_sub, hza, hca, ConfFlow.fieldMap_axis W hW]

#print axioms ofConfScaled_axisCov

/-- **Relabelling invariance of the flowed lattice functions at every step.**

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSF_axis (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ) (k : ℕ) (e : Equiv.Perm (Fin 4))
    {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSF hN Φ k (fun i => sfieldAxis e (F i)) = latSF hN Φ k F := by
  have hfam : (fun i => Φ.field k (sfieldAxis e (F i))) = fun i => sfieldAxis e (Φ.field k (F i)) := by
    funext i
    show (Φ.map k (lfieldAxis e (F i).1), testPermute e (F i).2)
      = (lfieldAxis e (Φ.map k (F i).1), testPermute e (F i).2)
    rw [hΦ]
  show latSk hN k (fun i => Φ.field k (sfieldAxis e (F i))) = latSk hN k (fun i => Φ.field k (F i))
  rw [hfam, latSk_eq, latSk_eq]
  exact latS_axis (stateK hN k) e (stateK_axis hN k e) (dySpacing_pos (one_le_of_ne_zero hN) k) _

#print axioms latSF_axis

/-- **Relabelling invariance of the flowed continuum functions.**

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem contSF_axis (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ) (e : Equiv.Perm (Fin 4))
    {ι : Type} [Fintype ι] (F : ι → SField N) :
    contSF hN Φ (fun i => sfieldAxis e (F i)) = contSF hN Φ F := by
  unfold contSF
  congr 1
  funext k
  exact latSF_axis hN Φ hΦ k e F

#print axioms contSF_axis

/-- The reflection identity of `ContinuumFlow.contSF_reflect` at one lattice step.

DERIVED: `0` is the excluded colour count and the reflection constant; `4` is the dimension. -/
theorem latSF_reflect (hN : N ≠ 0) (Φ : Flow N) (k : ℕ) (τ : Fin 4) {ι : Type} [Fintype ι]
    (F : ι → SField N) :
    latSF hN Φ k (fun i => SField.refl τ (F i)) = latSF hN Φ k F := by
  have hfam : (fun i => Φ.field k (SField.refl τ (F i)))
      = fun i => SField.refl τ (Φ.field k (F i)) := by
    funext i
    show (Φ.map k ((F i).1.refl τ), (F i).2.reflect τ)
      = ((Φ.map k (F i).1).refl τ, (F i).2.reflect τ)
    rw [Φ.map_refl]
  show latSk hN k (fun i => Φ.field k (SField.refl τ (F i))) = latSk hN k (fun i => Φ.field k (F i))
  rw [hfam, latSk_eq, latSk_eq]
  exact latS_refl (stateK hN k) τ
    (PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0)
    (dySpacing_pos (one_le_of_ne_zero hN) k) (fun i => Φ.field k (F i))

#print axioms latSF_reflect

/-- **The hypercubic group at every lattice step**: every word in the axis permutations and axis
reflections leaves the flowed lattice function of step `k` unchanged.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSF_hyp (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ) (k : ℕ)
    (w : List (Equiv.Perm (Fin 4) ⊕ Fin 4)) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSF hN Φ k (fun i => hypField w (F i)) = latSF hN Φ k F := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g with
    | inl e => exact (latSF_axis hN Φ hΦ k e (fun i => hypField w (F i))).trans ih
    | inr τ => exact (latSF_reflect hN Φ k τ (fun i => hypField w (F i))).trans ih

#print axioms latSF_hyp

/-- **Signed permutations at every lattice step**, at `HypScalar` fields.

DERIVED: `0` is the excluded colour count; `1` and `-1` are the signs; `4` is the dimension. -/
theorem latSF_signed (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ) (k : ℕ)
    (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) {ι : Type} [Fintype ι]
    (F F' : ι → SField N) (hH : ∀ i, HypScalar (F i).1) (hfield : ∀ i, (F' i).1 = (F i).1)
    (htest : ∀ i y, (F' i).2.1 y = (F i).2.1 (fun j => s j * y (σ j))) :
    latSF hN Φ k F' = latSF hN Φ k F := by
  obtain ⟨w, hw⟩ := exists_word_signed σ s hs
  have hF' : F' = fun i => hypField w (F i) := by
    funext i
    refine Prod.ext ?_ (Subtype.ext (funext fun y => ?_))
    · rw [hfield i, hypField_fst w (F i) (hH i)]
    · rw [htest i y, hypField_test w (F i) y]
      exact congrArg (F i).2.1 (funext fun j => (hw y j).symm)
  rw [hF']
  exact latSF_hyp hN Φ hΦ k w F

#print axioms latSF_signed

/-- **Signed permutations in the limit**, at `HypScalar` fields: an identity of `limUnder` values
with no bound assumed.

DERIVED: `0` is the excluded colour count; `1` and `-1` are the signs; `4` is the dimension. -/
theorem contSF_signed (hN : N ≠ 0) (Φ : Flow N) (hΦ : Flow.AxisCov Φ) (σ : Equiv.Perm (Fin 4))
    (s : Fin 4 → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) {ι : Type} [Fintype ι] (F F' : ι → SField N)
    (hH : ∀ i, HypScalar (F i).1) (hfield : ∀ i, (F' i).1 = (F i).1)
    (htest : ∀ i y, (F' i).2.1 y = (F i).2.1 (fun j => s j * y (σ j))) :
    contSF hN Φ F' = contSF hN Φ F := by
  unfold contSF
  congr 1
  funext k
  exact latSF_signed hN Φ hΦ k σ s hs F F' hH hfield htest

#print axioms contSF_signed

end Hyp

section Observer

open MassGap.ObserverFlow

end Observer

/-! ## 3. `SO(4)` from a dense set and continuity -/

section Dense

variable {N : ℕ}

/-- The support bound of a rotated test function: `y = Aᵀ (A y)`, so a coordinate of `y` is at most
`∑ |Aᵀ|` times the largest coordinate of `A y`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem rotTest_support (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ * A = 1) (y : Fin 4 → ℝ) {R : ℝ}
    (hy : ∀ j, |A.mulVec y j| ≤ R) (i : Fin 4) : |y i| ≤ (∑ j, |A j i|) * R := by
  have hyy : y = Aᵀ.mulVec (A.mulVec y) := by
    rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  have e : y i = ∑ j, A j i * A.mulVec y j := by
    conv_lhs => rw [hyy]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [e, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)

#print axioms rotTest_support

/-- **The rotated test function** `y ↦ f (A y)` for `Aᵀ A = 1`; `f` itself otherwise.

DERIVED: `0` is the support bound's sign; `4` in `Fin 4` is the spacetime dimension. -/
def rotTest (A : Matrix (Fin 4) (Fin 4) ℝ) (f : TestFn) : TestFn := by
  classical
  exact if hA : Aᵀ * A = 1 then
    ⟨fun y => f.1 (A.mulVec y), by
      obtain ⟨R, M, hR, hM, hs⟩ := f.2
      refine ⟨(∑ i, ∑ j, |A j i|) * R, M,
        mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) hR,
        fun y => hM _, fun y hy i => ?_⟩
      refine (rotTest_support A hA y (fun j => hs _ hy j) i).trans
        (mul_le_mul_of_nonneg_right ?_ hR)
      exact Finset.single_le_sum (f := fun i => ∑ j, |A j i|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)⟩
  else f

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem rotTest_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ * A = 1) (f : TestFn) (y : Fin 4 → ℝ) :
    (rotTest A f).1 y = f.1 (A.mulVec y) := by
  classical
  unfold rotTest
  rw [dif_pos hA]

#print axioms rotTest_apply

/-- A member of `SO(4)` has `Aᵀ A = 1`.

DERIVED: `4` is the dimension; `1` the identity. -/
theorem transpose_mul_self_of_mem {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ) : Aᵀ * A = 1 := by
  have h := (Matrix.mem_specialOrthogonalGroup_iff.mp hA).1
  rw [Matrix.mem_orthogonalGroup_iff'] at h
  simpa using h

#print axioms transpose_mul_self_of_mem

/-- The family with every test function rotated by `A`, fields kept.

DERIVED: no numeral. -/
def rotFam (A : Matrix (Fin 4) (Fin 4) ℝ) {ι : Type} (F : ι → SField N) : ι → SField N :=
  fun i => ((F i).1, rotTest A (F i).2)

/-- **The rotation statement for a flowed theory (stated).** For every `A ∈ SO(4)` and every family of
`Φs`-fields with uniformly continuous test functions, composing every test function with `A` leaves the
flowed continuum Schwinger function unchanged. For the observer's energy density it is the Euclidean
invariance row of the Clay alignment.

DERIVED: `0` is the excluded colour count; `4` is the dimension, of `SO(4)`. -/
def ObserverSO4 (hN : N ≠ 0) (Φ : Flow N) (Φs : Set (LField (MassGap.SUN.SU N))) : Prop :=
  ∀ A ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ, ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
    (∀ i, (F i).1 ∈ Φs) → (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam A F) = contSF hN Φ F

/-- **Orbit continuity (stated)**: `A ↦ contSF (rotFam A F)` is continuous on `SO(4)`.

DERIVED: `0` is the excluded colour count; `4` is the dimension, of `SO(4)`. -/
def OrbitContinuous (hN : N ≠ 0) (Φ : Flow N) {ι : Type} [Fintype ι] (F : ι → SField N) : Prop :=
  ContinuousOn (fun A : Matrix (Fin 4) (Fin 4) ℝ => contSF hN Φ (rotFam A F))
    (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ))

/-- **Constancy from a dense subset**: a function continuous on `S` and equal to `v` on `D ⊆ S`, with
`S ⊆ closure D`, equals `v` on `S`.

DERIVED: no numeral. -/
theorem eq_on_of_dense {X : Type*} [TopologicalSpace X] {g : X → ℝ} {S D : Set X} {v : ℝ}
    (hg : ContinuousOn g S) (hDS : D ⊆ S) (hdense : S ⊆ closure D) (hD : ∀ x ∈ D, g x = v) :
    ∀ x ∈ S, g x = v := by
  intro x hx
  haveI : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense hx)
  have h1 : Tendsto g (𝓝[D] x) (𝓝 (g x)) := ((hg x hx).mono hDS).tendsto
  have h2 : Tendsto g (𝓝[D] x) (𝓝 v) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hD y hy).symm)
  exact tendsto_nhds_unique h1 h2

#print axioms eq_on_of_dense

/-- **`SO(4)` from orbit continuity and a dense set of invariances.** If `D ⊆ SO(4)` is dense in
`SO(4)`, every orbit is continuous, and the flowed theory is invariant under every `A ∈ D`, it is
invariant under all of `SO(4)`.

DERIVED: `0` is the excluded colour count; `4` is the dimension, of `SO(4)`. -/
theorem observerSO4_of_dense (hN : N ≠ 0) (Φ : Flow N) (Φs : Set (LField (MassGap.SUN.SU N)))
    (D : Set (Matrix (Fin 4) (Fin 4) ℝ))
    (hDS : D ⊆ (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)))
    (hdense : (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) ⊆ closure D)
    (hcont : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ Φs) →
      (∀ i, UniformContinuous (F i).2.1) → OrbitContinuous hN Φ F)
    (hD : ∀ A ∈ D, ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ Φs) →
      (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam A F) = contSF hN Φ F) :
    ObserverSO4 hN Φ Φs := by
  intro A hA ι _ F hΦ hU
  exact eq_on_of_dense (hcont ι F hΦ hU) hDS hdense (fun B hB => hD B hB ι F hΦ hU) A hA

#print axioms observerSO4_of_dense

end Dense

/-! ## 4. One rotation outside the hypercubic group -/

section Pyth

/-- **The Pythagorean rotation**: `(3/5, 4/5)` in the plane of the first two axes.

DERIVED: `3`, `4`, `5` are the Pythagorean triple `3² + 4² = 5²`; `0`, `1` the other entries of the
identity outside the plane; `4` in `Fin 4` the dimension. -/
def pyth : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3 / 5, -(4 / 5), 0, 0; 4 / 5, 3 / 5, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **`pyth ∈ SO(4)`.**

DERIVED: as in `pyth`. -/
theorem pyth_mem : pyth ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pyth, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  · first
      | (have h3 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
         simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, pyth, h3]
         norm_num)
      | (simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, pyth]
         simp [Fin.succAbove, Fin.lt_def]
         norm_num)

#print axioms pyth_mem

/-- **`pyth` is not a signed permutation**: its `(0, 0)` entry `3/5` is neither `0` nor `±1`.

DERIVED: `1` and `-1` are the signs; `3/5` the entry. -/
theorem pyth_not_signed : ¬ ∃ (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ), (∀ i, s i = 1 ∨ s i = -1) ∧
    ∀ y i, pyth.mulVec y i = s i * y (σ i) := by
  rintro ⟨σ, s, hs, h⟩
  have h0 := h (Pi.single 0 1) 0
  have h1 := h (Pi.single 1 1) 0
  simp [pyth, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply] at h0 h1
  by_cases hσ : σ 0 = 0
  · rw [if_pos hσ] at h0
    rcases hs 0 with h' | h' <;> rw [h'] at h0 <;> norm_num at h0
  · rw [if_neg hσ] at h0
    norm_num at h0

#print axioms pyth_not_signed

/-- **`pyth` moves the lattice**: the axis vector `e₀` goes to `(3/5, 4/5, 0, 0)`, whose first
coordinate is not an integer.

DERIVED: `3/5` the entry; `1` the axis vector. -/
theorem pyth_not_lattice : ¬ ∃ z : ℤ, pyth.mulVec (Pi.single 0 1) 0 = z := by
  rintro ⟨z, hz⟩
  simp [pyth, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply] at hz
  have h5 : (3 : ℝ) = 5 * z := by linarith
  have : (3 : ℤ) = 5 * z := by exact_mod_cast h5
  omega

#print axioms pyth_not_lattice

/-- The integer powers `(aₙ, bₙ)` of `3 + 4i`: `aₙ + i bₙ = (3 + 4i)ⁿ`.

DERIVED: `3` and `4` are the Gaussian integer `3 + 4i`; `1` and `0` the zeroth power. -/
def pythInt : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pythInt n).1 - 4 * (pythInt n).2, 4 * (pythInt n).1 + 3 * (pythInt n).2)

/-- **`(3 + 4i)ⁿ ≡ 3 + 4i (mod 5)`** for `n ≥ 1`: `(3 + 4i)² = −7 + 24i ≡ 3 + 4i`.

DERIVED: `5` the modulus, `3`, `4` the residues. -/
theorem pythInt_mod (n : ℕ) : (pythInt (n + 1)).1 % 5 = 3 ∧ (pythInt (n + 1)).2 % 5 = 4 := by
  induction n with
  | zero => simp [pythInt]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    show (3 * (pythInt (n + 1)).1 - 4 * (pythInt (n + 1)).2) % 5 = 3 ∧
      (4 * (pythInt (n + 1)).1 + 3 * (pythInt (n + 1)).2) % 5 = 4
    omega

#print axioms pythInt_mod

/-- The `(0, 0)` and `(1, 0)` entries of `pythⁿ` are `aₙ / 5ⁿ` and `bₙ / 5ⁿ`.

DERIVED: `5` the hypotenuse; `3`, `4` as in `pyth`. -/
theorem pyth_pow_col (n : ℕ) :
    (pyth ^ n) 0 0 = (pythInt n).1 / 5 ^ n ∧ (pyth ^ n) 1 0 = (pythInt n).2 / 5 ^ n ∧
      (pyth ^ n) 2 0 = 0 ∧ (pyth ^ n) 3 0 = 0 := by
  induction n with
  | zero => simp [pythInt, Matrix.one_apply]
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    rw [pow_succ']
    simp only [Matrix.mul_apply, Fin.sum_univ_four, h0, h1, h2, h3]
    simp [pyth, pythInt, pow_succ]
    refine ⟨?_, ?_⟩ <;> field_simp <;> ring

#print axioms pyth_pow_col

/-- **`pyth` has infinite order**: no positive power is the identity, since the `(1, 0)` entry of
`pythⁿ⁺¹` is `bₙ₊₁ / 5ⁿ⁺¹` with `bₙ₊₁ ≡ 4 (mod 5)`, never `0`.

DERIVED: `1` the identity; `0` its off-diagonal entry; `5`, `4` as in `pythInt_mod`. -/
theorem pyth_pow_ne_one (n : ℕ) : pyth ^ (n + 1) ≠ 1 := by
  intro h
  have hc := (pyth_pow_col (n + 1)).2.1
  rw [h, Matrix.one_apply_ne (by decide)] at hc
  have hb : (pythInt (n + 1)).2 = 0 := by
    have h5 : (5 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have : ((pythInt (n + 1)).2 : ℝ) = 0 := by
      field_simp at hc
      linarith
    exact_mod_cast this
  have := (pythInt_mod n).2
  rw [hb] at this
  norm_num at this

#print axioms pyth_pow_ne_one

end Pyth

end MassGap.ObserverRotation
