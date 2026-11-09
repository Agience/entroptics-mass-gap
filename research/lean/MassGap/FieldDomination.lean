import Mathlib
import MassGap.ContinuumCluster
import MassGap.ContinuumNontrivial
import MassGap.ExistencePos
import MassGap.NonTrivialCanonical
import MassGap.SmearedCubeLocal

noncomputable section

/-!
# MassGap.FieldDomination — single insertions of a second field against the cube reading of `O`

`SmearedCubeLocal.SmearCubeLocalAlong hN βs O s₀` bounds every monomial, whatever its fields, by powers
of `x(d) = refReadingAlong hN βs O d d`, the cube reading of the one field `O`. For one insertion of a
field `O' ≠ O` the comparison has two parts: the profile of `O'` against the cube of `O'`, and the cube
of `O'` against the cube of `O`. Reflection positivity orders readings of one field; it does not
compare two fields. The second part is the statement `FieldDomAlong`.

* `FieldDomAlong hN βs O O' s₀`: at every scale `0 < d < s₀`, one `C` with
  `refReadingAlong hN βs O' d d k ≤ C · refReadingAlong hN βs O d d k` eventually in the step.
* `sub_sub_state`, `latSkR_rho1_mono1_sub`, `refReadingAlong_sub`: the connected composites do not see
  a constant added to the field, so `O.sub r` reads exactly as `O`, and `fieldDomAlong_sub` gives the
  domination with `C = 1` both ways.
* `OneInsertionAlong hN βs O O' s₀`: the one-insertion clause of `SmearCubeLocalAlong hN βs O s₀` at
  the field `O'`. `oneInsertion_of_smearCubeLocal`: the capstone's hypothesis contains it at every
  `O'`. `oneInsertion_of_fieldDom`: the clause of `O'` against its own cube and `FieldDomAlong` give the
  clause at `O'` (the cube reading is eventually non-negative, `refReadingAlong_eventually_nonneg`).
  So the one-insertion part of `SmearCubeLocalAlong` follows from `FieldDomAlong` together with the
  bound of each field against its own cube.

What `FieldDomAlong` asks beyond these is a statement about the dynamics: two independent reflection
positive components with amplitude ratio growing along the tower are reflection positive, hypercubic and
gapped, and fail it.

DERIVED (module-wide): `0` the time axis, the reflection plane and the lower bound of a square; `1` one
insertion, the unit field strength and the constant of the self-domination; `2` the square of the
profile constant and the doubling in `⌈R/d⌉ + 2`.
-/

namespace MassGap.FieldDomination

open Filter MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical

variable {N : ℕ}

/-! ## 1. The statement -/

/-- **Field domination at the cube.** At every scale `0 < d < s₀` the cube reading of `O'` is at
most a constant times the cube reading of `O`, eventually in the step. -/
def FieldDomAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O O' : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → d < s₀ → ∃ C : ℝ, ∀ᶠ k in atTop,
    refReadingAlong hN βs O' d d k ≤ C * refReadingAlong hN βs O d d k

/-- Every field dominates itself. -/
theorem fieldDomAlong_self (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) :
    FieldDomAlong hN βs O O s₀ :=
  fun _ _ _ => ⟨1, Eventually.of_forall (fun _ => (one_mul _).ge)⟩

/-! ## 2. Time-profiled single insertions of a dominated field -/

/-! ## 3. A constant added to the field -/

/-- **The connected subtraction absorbs a constant.** For every state `ν`,
`(X − r) − ν(X − r) = X − ν(X)`. -/
theorem sub_sub_state (ν : MassGap.DLRLimit.State (Cfg N)) (X : LField (MassGap.SUN.SU N)) (r : ℝ) :
    (X.sub r).sub (ν (X.sub r).1) = X.sub (ν X.1) :=
  Subtype.ext (by
    show X.1 - r • (1 : C(Cfg N, ℝ)) - (ν (X.1 - r • (1 : C(Cfg N, ℝ)))) • (1 : C(Cfg N, ℝ))
      = X.1 - (ν X.1) • (1 : C(Cfg N, ℝ))
    rw [ν.map_sub, ν.map_smul, ν.map_one, mul_one, sub_smul]
    abel)

/-- **`O.sub r` reads as `O`**: every unit-strength reflected single-insertion reading is unchanged
when a constant is added to the field. -/
theorem latSkR_rho1_mono1_sub (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (r : ℝ)
    (f : TestFn) (k : ℕ) :
    latSkRAlong hN βs (rho1Along hN βs) k
        (pairFam 0 (ContinuumNontrivial.mono1 (O.sub r, f)) (ContinuumNontrivial.mono1 (O.sub r, f)))
      = latSkRAlong hN βs (rho1Along hN βs) k
        (pairFam 0 (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f))) := by
  unfold latSkRAlong
  congr 1
  unfold latSkAlong
  congr 1
  funext i
  rcases i with i | i
  · refine Prod.ext ?_ rfl
    show (((O.sub r).refl 0).sub (stateAlong hN βs k ((O.sub r).refl 0).1))
      = ((O.refl 0).sub (stateAlong hN βs k (O.refl 0).1))
    rw [LField.refl_sub, sub_sub_state]
  · refine Prod.ext ?_ rfl
    show ((O.sub r).sub (stateAlong hN βs k (O.sub r).1)) = (O.sub (stateAlong hN βs k O.1))
    exact sub_sub_state _ O r

/-- The cube reading of `O.sub r` is that of `O`. -/
theorem refReadingAlong_sub (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (r t ℓ : ℝ)
    (k : ℕ) : refReadingAlong hN βs (O.sub r) t ℓ k = refReadingAlong hN βs O t ℓ k :=
  latSkR_rho1_mono1_sub hN βs O r _ k

/-- `O` and `O.sub r` dominate each other with `C = 1`. -/
theorem fieldDomAlong_sub (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (r s₀ : ℝ) :
    FieldDomAlong hN βs O (O.sub r) s₀ ∧ FieldDomAlong hN βs (O.sub r) O s₀ :=
  ⟨fun _ _ _ => ⟨1, Eventually.of_forall (fun k => by
      rw [refReadingAlong_sub, one_mul])⟩,
   fun _ _ _ => ⟨1, Eventually.of_forall (fun k => by
      rw [refReadingAlong_sub, one_mul])⟩⟩

/-! ## 4. The one-insertion clause, split into a profile part and a field part -/

/-- **The one-insertion clause of `SmearCubeLocalAlong hN βs O s₀` at the field `O'`**: every
insertion `(O', f)` with `f` supported in `y₀ ≥ d`, `0 < d < s₀`, reads at most `C · x(d)` eventually,
`x(d)` the cube reading of `O`. -/
def OneInsertionAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O O' : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  ∀ (f : TestFn) (d : ℝ), 0 < d → d < s₀ → (∀ y, f.1 y ≠ 0 → d ≤ y 0) → ∃ C : ℝ, ∀ᶠ k in atTop,
    latSkRAlong hN βs (rho1Along hN βs) k
        (pairFam 0 (ContinuumNontrivial.mono1 (O', f)) (ContinuumNontrivial.mono1 (O', f)))
      ≤ C * refReadingAlong hN βs O d d k

/-- The cube reading is eventually non-negative: the cube is eventually in the half-space algebra,
where the reflected diagonal is a value of the reflection form. -/
theorem refReadingAlong_eventually_nonneg (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) : ∀ᶠ k in atTop, 0 ≤ refReadingAlong hN βs O t ℓ k := by
  filter_upwards [eventually_smear_sub_mem (one_le_of_ne_zero hN) 0 O _
    (ExistencePos.posTime_cube ht)] with k hk
  exact ContinuumSep.latSkR_pairFam_self_nonneg_along hN βs (rho1Along hN βs) 0
    (Renorm.connectedAlong_reflCompat hN βs _ 0 (fun _ _ => rfl)) k _
    (Yv_mem hN _ 0 k _ (fun _ r => hk r))

/-- **Each field's own bound and field domination give the clause at `O'`.** -/
theorem oneInsertion_of_fieldDom (hN : N ≠ 0) (βs : ℕ → ℝ) (O O' : LField (MassGap.SUN.SU N))
    {s₀ : ℝ} (hO' : OneInsertionAlong hN βs O' O' s₀) (hD : FieldDomAlong hN βs O O' s₀) :
    OneInsertionAlong hN βs O O' s₀ := by
  intro f d hd hds hsupp
  obtain ⟨C₁, h1⟩ := hO' f d hd hds hsupp
  obtain ⟨C₂, h2⟩ := hD d hd hds
  refine ⟨max C₁ 0 * C₂, ?_⟩
  filter_upwards [h1, h2, refReadingAlong_eventually_nonneg hN βs O' (ℓ := d) hd] with k hk1 hk2 hk3
  calc latSkRAlong hN βs (rho1Along hN βs) k
          (pairFam 0 (ContinuumNontrivial.mono1 (O', f)) (ContinuumNontrivial.mono1 (O', f)))
        ≤ C₁ * refReadingAlong hN βs O' d d k := hk1
    _ ≤ max C₁ 0 * refReadingAlong hN βs O' d d k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hk3
    _ ≤ max C₁ 0 * (C₂ * refReadingAlong hN βs O d d k) :=
        mul_le_mul_of_nonneg_left hk2 (le_max_right _ _)
    _ = max C₁ 0 * C₂ * refReadingAlong hN βs O d d k := by ring

/-- **`SmearCubeLocalAlong` contains the clause at every field.** -/
theorem oneInsertion_of_smearCubeLocal (hN : N ≠ 0) (βs : ℕ → ℝ) (O O' : LField (MassGap.SUN.SU N))
    {s₀ : ℝ} (h : SmearedCubeLocal.SmearCubeLocalAlong hN βs O s₀) : OneInsertionAlong hN βs O O' s₀ := by
  intro f d hd hds hsupp
  obtain ⟨C, hC⟩ := h (ContinuumNontrivial.mono1 (O', f)) d hd hds
    ⟨fun _ y hy => hsupp y hy, fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij⟩
  refine ⟨C, hC.mono (fun k hk => ?_)⟩
  have hk' : latSkRAlong hN βs (rho1Along hN βs) k
      (pairFam 0 (ContinuumNontrivial.mono1 (O', f)) (ContinuumNontrivial.mono1 (O', f)))
        ≤ C * refReadingAlong hN βs O d d k ^ 1 := hk
  rwa [pow_one] at hk'

end MassGap.FieldDomination

#print axioms MassGap.FieldDomination.fieldDomAlong_self
#print axioms MassGap.FieldDomination.sub_sub_state
#print axioms MassGap.FieldDomination.latSkR_rho1_mono1_sub
#print axioms MassGap.FieldDomination.refReadingAlong_sub
#print axioms MassGap.FieldDomination.fieldDomAlong_sub
#print axioms MassGap.FieldDomination.refReadingAlong_eventually_nonneg
#print axioms MassGap.FieldDomination.oneInsertion_of_fieldDom
#print axioms MassGap.FieldDomination.oneInsertion_of_smearCubeLocal
