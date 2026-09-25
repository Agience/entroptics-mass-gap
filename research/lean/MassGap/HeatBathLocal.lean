import Mathlib
import MassGap.HeatBathErgodic
import MassGap.BoxPatch
import MassGap.ContinuumField

noncomputable section

/-!
# MassGap.HeatBathLocal — the heat-bath locality hypothesis holds

## What it gives

1. **Null vectors of a symmetric non-negative form.** `fnull_pair`, `fnull_add`, `fnull_sub`,
   `fnull_proj` (a self-adjoint idempotent keeps null vectors null), `form_sub_null`, and
   `form_proj_unique`: two self-adjoint maps onto the same subspace `V`, each fixing `V` up to null
   vectors, agree up to a null vector.
2. **Every heat-bath system is the concrete one up to null vectors.** `condExp_sub_null`: for every
   `KnabeCriterion.WilsonHeatBath`, `condExp l x − HeatBath.torusCondExp l x` is `torusForm`-null
   (`form_proj_unique` with `V` the observables not reading `l`). `wilson_h_null`: `hₗ x` is null when
   `x` does not read `l` (`WilsonHeatBath.keeps`).
3. **Commutation off shared plaquettes.** `nbT j l`: `l` and the links sharing a plaquette with it,
   the diagonal plaquettes `μ = ν` included. `nbPlane j l ν`: the candidates through the plane of
   `l.1` and `ν`, at most `6`, and at most `3` at `ν = l.1` (`nbPlane_self_sub`). `card_nbT_le`: at
   most `21 = 3 + 3 · 6` of them at every extent.
   `condExp_comm_null`, `localCommute_wilson`: `LocalCommute (S.toPatchSystem) (nbT j) 21` for every
   heat-bath system `S` (`HeatBath.torusCondExp_comm`).
4. **Ergodicity at every extent.** `torus_poincare`: a Poincaré inequality for `torusForm` against the
   concrete heat baths (`HeatBathErgodic.heat_poincare`), its constant depending on the extent;
   `dirichlet_wilson` moves it to every heat-bath system; `ergodicLimit_wilson`: `ErgodicLimit S.toPatchSystem f g (μⱼ(f) μⱼ(g))`
   (`HeatBathErgodic.ergodicLimit_of_poincare`).
5. **Supports and separation.** `readsNot_of_isLocalOn`: an observable local on a finite set does not
   read the torus links off its image. `isLocalOn_ireflObs`, `isLocalOn_iterate_shift`: the reflected
   and shifted observables are local on the reflected and shifted sets. `far_of_potential`: a
   potential vanishing on `A` and growing by at most one per neighbour step gives `Far` at every level
   below it. `psiL`: the cyclic `τ`-offset from the window of `θx`, truncated at both ends;
   `psiL_lip` is its step bound along `nbT`.
6. **The result.** `heatBathLocality_holds`: `HeatBathGapDecay.HeatBathLocality τ p hN β` at every
   `τ`, `p`, `N ≠ 0` and real `β`, with `z = 21`, `a = b = |T|` for a finite support `T` of `x`,
   `M = ‖x‖²`, the separation holding for `j ≥ 3n + 2R + 3` (`R` the `τ`-depth of `T`).
   `heatBathDecay_holds`: `KnabeCriterion.HeatBathDecay τ p hN β`, the implication from a uniform
   heat-bath gap (`GlobalGap c` for all large `j`, a hypothesis inside `HeatBathDecay`) to decay.
   `localityAt_holds`: the locality body at `z = 21` for each family.
7. **The rate of a box.** `boxRate N β₀ n γ`, `irGapAt_boxRate`: a box patch gap gives the IR gap at
   `β₀` at `boxRate`, and `boxRate_eq` evaluates it as `min(boxKnabe n γ, 1)/(508 · aRun N β₀)`.
-/

namespace MassGap.HeatBathLocal

open MeasureTheory Filter
open MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathGapDecay MassGap.HeatBathErgodic
open MassGap.WilsonLattice (wilsonSystem)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.PeriodicState (torusObs torusState)

/-! ## 1. Null vectors of a symmetric non-negative form -/

section Null

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A null vector pairs to `0` with every vector (`HeatBathGapDecay.form_sq_le_mul`).

DERIVED: `0` is the null value; `2` is the square of Cauchy–Schwarz. -/
theorem fnull_pair (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) {z : E} (hz : B z z = 0) (w : E) : B w z = 0 := by
  have h := form_sq_le_mul B hsymm hnn w z
  rw [hz, mul_zero] at h
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _))

#print axioms fnull_pair

/-- The sum of two null vectors is null.

DERIVED: `0` is the null value. -/
theorem fnull_add (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) {a b : E} (ha : B a a = 0) (hb : B b b = 0) :
    B (a + b) (a + b) = 0 := by
  have h1 := fnull_pair B hsymm hnn hb a
  have h2 := fnull_pair B hsymm hnn ha b
  simp only [map_add, LinearMap.add_apply]
  linarith

#print axioms fnull_add

/-- The difference of two null vectors is null.

DERIVED: `0` is the null value. -/
theorem fnull_sub (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) {a b : E} (ha : B a a = 0) (hb : B b b = 0) :
    B (a - b) (a - b) = 0 := by
  have h1 := fnull_pair B hsymm hnn hb a
  have h2 := fnull_pair B hsymm hnn ha b
  simp only [map_sub, LinearMap.sub_apply]
  linarith

#print axioms fnull_sub

/-- **A self-adjoint idempotent keeps null vectors null**: `B(Pz, Pz) = B(z, Pz) = 0`.

DERIVED: `0` is the null value. -/
theorem fnull_proj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (P : E →ₗ[ℝ] E) (hP : ∀ x y, B (P x) y = B x (P y))
    (hid : ∀ x, P (P x) = P x) {z : E} (hz : B z z = 0) : B (P z) (P z) = 0 := by
  rw [hP z (P z), hid z, hsymm]
  exact fnull_pair B hsymm hnn hz (P z)

#print axioms fnull_proj

/-- **Removing a null vector keeps the form**: `B(a − d, a − d) = B(a, a)` for null `d`.

DERIVED: `0` is the null value. -/
theorem form_sub_null (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) {a d : E} (hd : B d d = 0) : B (a - d) (a - d) = B a a := by
  have h1 := fnull_pair B hsymm hnn hd a
  have h3 : B d a = 0 := by
    rw [hsymm]
    exact h1
  simp only [map_sub, LinearMap.sub_apply]
  linarith

#print axioms form_sub_null

/-- **Two projections onto one subspace agree up to a null vector.** Let `P`, `Q` be `B`-self-adjoint
with values in `V`, each fixing every vector of `V` up to a null vector. Then `Px − Qx` is null:
`x − Px` and `x − Qx` are `B`-orthogonal to `V`, and
`B(Px − Qx, Px − Qx) = −B(x − Px, Px) + B(x − Px, Qx) + B(x − Qx, Px) − B(x − Qx, Qx) = 0`.

DERIVED: `0` is the null value. -/
theorem form_proj_unique (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (V : E → Prop) (P Q : E →ₗ[ℝ] E)
    (hP : ∀ x y, B (P x) y = B x (P y)) (hQ : ∀ x y, B (Q x) y = B x (Q y))
    (hPV : ∀ x, V (P x)) (hQV : ∀ x, V (Q x))
    (hPk : ∀ v, V v → B (P v - v) (P v - v) = 0) (hQk : ∀ v, V v → B (Q v - v) (Q v - v) = 0)
    (x : E) : B (P x - Q x) (P x - Q x) = 0 := by
  have orthP : ∀ v, V v → B (x - P x) v = 0 := by
    intro v hv
    have h := fnull_pair B hsymm hnn (hPk v hv) x
    simp only [map_sub, LinearMap.sub_apply] at h ⊢
    rw [hP x v]
    linarith
  have orthQ : ∀ v, V v → B (x - Q x) v = 0 := by
    intro v hv
    have h := fnull_pair B hsymm hnn (hQk v hv) x
    simp only [map_sub, LinearMap.sub_apply] at h ⊢
    rw [hQ x v]
    linarith
  have a1 := orthP (P x) (hPV x)
  have a2 := orthP (Q x) (hQV x)
  have a3 := orthQ (P x) (hPV x)
  have a4 := orthQ (Q x) (hQV x)
  simp only [map_sub, LinearMap.sub_apply] at a1 a2 a3 a4 ⊢
  linarith

#print axioms form_proj_unique

end Null

/-! ## 2. The torus form and the heat-bath systems -/

section Torus

variable {N : ℕ}

/-- `torusState` reads an observable only through its torus reading.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` is the
excluded rank in `hN`. -/
theorem torusState_congr (hN : N ≠ 0) (M : ℕ) (β : ℝ) {F G : C(GibbsSpec.IConf (SU N), ℝ)}
    (h : ∀ W, torusObs M F W = torusObs M G W) : torusState hN M β F = torusState hN M β G :=
  congrArg (ReflectPositive.EW (d := 4) (n := M + 1) N β) (funext h)

#print axioms torusState_congr

/-- **An observable with zero torus reading is `torusForm`-orthogonal to everything.**

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN` and
the null value. -/
theorem torusForm_eq_zero_of_torusObs (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (w y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hw : ∀ W, torusObs (2 * j + 1) (w : C(GibbsSpec.IConf (SU N), ℝ)) W = 0) :
    torusForm hN β j w y = 0 := by
  have h : ∀ W, torusObs (2 * j + 1)
      ((w : C(GibbsSpec.IConf (SU N), ℝ)) * (y : C(GibbsSpec.IConf (SU N), ℝ))) W
      = torusObs (2 * j + 1) (0 : C(GibbsSpec.IConf (SU N), ℝ)) W := by
    intro W
    have h0 : (w : C(GibbsSpec.IConf (SU N), ℝ)) (InfiniteLattice.pullback (2 * j + 1) W) = 0 :=
      hw W
    show (w : C(GibbsSpec.IConf (SU N), ℝ)) (InfiniteLattice.pullback (2 * j + 1) W)
        * (y : C(GibbsSpec.IConf (SU N), ℝ)) (InfiniteLattice.pullback (2 * j + 1) W)
      = (0 : C(GibbsSpec.IConf (SU N), ℝ)) (InfiniteLattice.pullback (2 * j + 1) W)
    rw [h0, zero_mul, ContinuousMap.zero_apply]
  rw [torusForm_apply, torusState_congr hN (2 * j + 1) β h]
  exact DLRLimit.State.map_zero _

#print axioms torusForm_eq_zero_of_torusObs

/-- **Equal torus readings differ by a null vector.**

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN` and
the null value. -/
theorem null_of_torusObs_eq (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (a b : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (h : torusObs (2 * j + 1) (a : C(GibbsSpec.IConf (SU N), ℝ))
      = torusObs (2 * j + 1) (b : C(GibbsSpec.IConf (SU N), ℝ))) :
    torusForm hN β j (a - b) (a - b) = 0 :=
  torusForm_eq_zero_of_torusObs hN β j _ _ (fun W => by
    show (a : C(GibbsSpec.IConf (SU N), ℝ)) (InfiniteLattice.pullback (2 * j + 1) W)
        - (b : C(GibbsSpec.IConf (SU N), ℝ)) (InfiniteLattice.pullback (2 * j + 1) W) = 0
    exact sub_eq_zero.mpr (congrFun h W))

#print axioms null_of_torusObs_eq

/-- **`hₗ x` is null when `x` does not read `l`** (`WilsonHeatBath.keeps`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN` and the null value. -/
theorem wilson_h_null (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hx : ReadsNot j l (x : C(GibbsSpec.IConf (SU N), ℝ))) :
    torusForm hN β j (x - S.condExp l x) (x - S.condExp l x) = 0 :=
  null_of_torusObs_eq hN β j _ _ (S.keeps l x hx).symm

#print axioms wilson_h_null

/-- `wilson_h_null` stated on the patch system `S.toPatchSystem`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN` and the null value. -/
theorem wilson_h_null' (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (hx : ReadsNot j l (x : C(GibbsSpec.IConf (SU N), ℝ))) :
    S.toPatchSystem.B (S.toPatchSystem.h l x) (S.toPatchSystem.h l x) = 0 :=
  wilson_h_null hN β S l x hx

#print axioms wilson_h_null'

/-- **Every heat-bath system is the concrete heat bath up to null vectors**: both `S.condExp l` and
`HeatBath.torusCondExp` are `torusForm`-self-adjoint, take values not reading `l`, and fix every
observable not reading `l` up to a null vector (`form_proj_unique`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN` and the null value. -/
theorem condExp_sub_null (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (S.condExp l x - torusCondExp β (2 * j + 1) l x)
      (S.condExp l x - torusCondExp β (2 * j + 1) l x) = 0 :=
  form_proj_unique (torusForm hN β j) (torusForm_symm hN β j) (torusForm_nonneg hN β j)
    (fun v => ReadsNot j l (v : C(GibbsSpec.IConf (SU N), ℝ))) (S.condExp l)
    (torusCondExp β (2 * j + 1) l) (S.selfAdj l) (torusCondExp_selfAdj hN β j l)
    (S.reads_not l) (torusCondExp_readsNot β j l)
    (fun v hv => null_of_torusObs_eq hN β j _ _ (S.keeps l v hv))
    (fun v hv => null_of_torusObs_eq hN β j _ _ (torusCondExp_keeps β j l v hv)) x

#print axioms condExp_sub_null

/-- **Heat baths at links sharing no plaquette commute up to null vectors**: the commutator
`h_{l'}(hₗu) − hₗ(h_{l'}u)` of any heat-bath system is null (`condExp_sub_null`, `fnull_proj`,
`HeatBath.torusCondExp_comm`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN` and the null value. -/
theorem condExp_comm_null (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j)
    {l l' : WilsonHypercubic.Link 4 (2 * j + 1 + 1)} (hne : l' ≠ l)
    (hs : ¬ SharePlaq (bdT (2 * j + 1)) l l')
    (u : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j ((u - S.condExp l u) - S.condExp l' (u - S.condExp l u)
        - ((u - S.condExp l' u) - S.condExp l (u - S.condExp l' u)))
      ((u - S.condExp l u) - S.condExp l' (u - S.condExp l u)
        - ((u - S.condExp l' u) - S.condExp l (u - S.condExp l' u))) = 0 := by
  have hsym := torusForm_symm hN β j
  have hnn := torusForm_nonneg hN β j
  have hcomm : torusCondExp β (2 * j + 1) l' (torusCondExp β (2 * j + 1) l u)
      = torusCondExp β (2 * j + 1) l (torusCondExp β (2 * j + 1) l' u) :=
    torusCondExp_comm β (2 * j + 1) hne (not_sharePlaq_symm hs) u
  have e : (u - S.condExp l u) - S.condExp l' (u - S.condExp l u)
        - ((u - S.condExp l' u) - S.condExp l (u - S.condExp l' u))
      = ((S.condExp l' (S.condExp l u - torusCondExp β (2 * j + 1) l u))
          + (S.condExp l' (torusCondExp β (2 * j + 1) l u)
            - torusCondExp β (2 * j + 1) l' (torusCondExp β (2 * j + 1) l u)))
        - ((S.condExp l (S.condExp l' u - torusCondExp β (2 * j + 1) l' u))
          + (S.condExp l (torusCondExp β (2 * j + 1) l' u)
            - torusCondExp β (2 * j + 1) l (torusCondExp β (2 * j + 1) l' u))) := by
    rw [hcomm]
    simp only [map_sub]
    abel
  rw [e]
  refine fnull_sub _ hsym hnn (fnull_add _ hsym hnn ?_ ?_) (fnull_add _ hsym hnn ?_ ?_)
  · exact fnull_proj _ hsym hnn (S.condExp l') (S.selfAdj l') (S.idem l')
      (condExp_sub_null hN β S l u)
  · exact condExp_sub_null hN β S l' _
  · exact fnull_proj _ hsym hnn (S.condExp l) (S.selfAdj l) (S.idem l)
      (condExp_sub_null hN β S l' u)
  · exact condExp_sub_null hN β S l _

#print axioms condExp_comm_null

/-- The constant observable `1` in the periodic gauge-invariant observables.

DERIVED: `1` is the constant; `2 * j + 1` is the index of the even-extent family. -/
def oneT (j : ℕ) : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  ⟨1, show PeriodicGaugeInv (2 * j + 1) (1 : C(GibbsSpec.IConf (SU N), ℝ)) from fun _ _ => rfl⟩

/-- `torusForm v 1 = μⱼ(v)`.

DERIVED: `1` is the constant; `2 * j + 1` is the index of the even-extent family; `0` is the
excluded rank in `hN`. -/
theorem torusForm_one (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j v (oneT j) = torusState hN (2 * j + 1) β (v : C(GibbsSpec.IConf (SU N), ℝ)) := by
  rw [torusForm_apply]
  show torusState hN (2 * j + 1) β ((v : C(GibbsSpec.IConf (SU N), ℝ)) * 1) = _
  rw [mul_one]

#print axioms torusForm_one

/-- `torusForm 1 1 = 1` (`DLRLimit.State.map_one`).

DERIVED: `1` is the constant and its value; `0` is the excluded rank in `hN`. -/
theorem torusForm_one_one (hN : N ≠ 0) (β : ℝ) (j : ℕ) :
    torusForm hN β j (oneT (N := N) j) (oneT j) = 1 := by
  rw [torusForm_one]
  exact DLRLimit.State.map_one _

#print axioms torusForm_one_one

/-- The constant observable reads no link.

DERIVED: `4` is the spacetime dimension; `1` is the constant; `2 * j + 1` is the index of the
even-extent family and the `+ 1` its successor writing the extent. -/
theorem readsNot_one (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ReadsNot (N := N) j l (1 : C(GibbsSpec.IConf (SU N), ℝ)) := by
  unfold ReadsNot
  intro W g
  rfl

#print axioms readsNot_one

/-- **THE POINCARÉ INEQUALITY ON THE PERIODIC LATTICE.** At every extent index `j`, some `C ≥ 0` has
`torusForm(v, v) − torusForm(v, 1)² ≤ C Σ_l torusForm(v − Eₗv, v − Eₗv)` for every periodic
gauge-invariant `v`, with `Eₗ = HeatBath.torusCondExp` (`HeatBathErgodic.heat_poincare` at the
torus reading of `v`, `HeatBath.torusObs_heatLift`). `C` depends on `j`; `ergodicLimit_wilson` uses it
at one extent.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family; `0` is
the excluded rank in `hN` and the sign of `C`; `2` is the square. -/
theorem torus_poincare (hN : N ≠ 0) (β : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
      torusForm hN β j v v - torusForm hN β j v (oneT j) ^ 2
        ≤ C * ∑ l, torusForm hN β j (v - torusCondExp β (2 * j + 1) l v)
            (v - torusCondExp β (2 * j + 1) l v) := by
  obtain ⟨C, hC0, hC⟩ := heat_poincare (N := N) hN (bdT (2 * j + 1)) β
  refine ⟨C, hC0, fun v => ?_⟩
  have hφ := continuous_torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))
  have h := hC _ hφ
  have e1 : torusForm hN β j v v
      = (wilsonSystem (bdT (2 * j + 1)) (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (fun W => torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
            * torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W) := rfl
  have e2 : torusForm hN β j v (oneT j)
      = (wilsonSystem (bdT (2 * j + 1)) (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) := by
    rw [torusForm_one]
    rfl
  have e3 : ∀ l, torusForm hN β j (v - torusCondExp β (2 * j + 1) l v)
      (v - torusCondExp β (2 * j + 1) l v)
      = (wilsonSystem (bdT (2 * j + 1)) (wilsonDensity (N := N))).expect (probHaar (SU N)) β
          (fun W => (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
            - heatAvg (bdT (2 * j + 1)) β l
                (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) W) ^ 2) := by
    intro l
    have hW : ∀ W, torusObs (2 * j + 1)
        ((v - torusCondExp β (2 * j + 1) l v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) W
        = torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
          - heatAvg (bdT (2 * j + 1)) β l
              (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) W := by
      intro W
      exact congrArg (fun t => torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W - t)
        (congrFun (torusObs_heatLift β (2 * j + 1) l (v : C(GibbsSpec.IConf (SU N), ℝ))) W)
    have hf : (fun W => torusObs (2 * j + 1)
          ((v - torusCondExp β (2 * j + 1) l v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) W
          * torusObs (2 * j + 1)
          ((v - torusCondExp β (2 * j + 1) l v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
            : C(GibbsSpec.IConf (SU N), ℝ)) W)
        = fun W => (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ)) W
            - heatAvg (bdT (2 * j + 1)) β l
                (torusObs (2 * j + 1) (v : C(GibbsSpec.IConf (SU N), ℝ))) W) ^ 2 := by
      funext W
      rw [hW W, sq]
    exact congrArg (fun φ => (wilsonSystem (bdT (2 * j + 1)) (wilsonDensity (N := N))).expect
      (probHaar (SU N)) β φ) hf
  rw [e1, e2, Finset.sum_congr rfl (fun l _ => e3 l)]
  exact h

#print axioms torus_poincare

/-- **The Dirichlet form of any heat-bath system is the concrete one**:
`B(Hv, v) = Σ_l torusForm(v − Eₗv, v − Eₗv)` (`HeatBathErgodic.form_H_eq_sum`, `condExp_sub_null`,
`form_sub_null`).

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN`. -/
theorem dirichlet_wilson (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j)
    (v : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    S.toPatchSystem.B (S.toPatchSystem.H v) v
      = ∑ l, torusForm hN β j (v - torusCondExp β (2 * j + 1) l v)
          (v - torusCondExp β (2 * j + 1) l v) := by
  rw [form_H_eq_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  show torusForm hN β j (v - S.condExp l v) (v - S.condExp l v) = _
  have e : v - S.condExp l v = (v - torusCondExp β (2 * j + 1) l v)
      - (S.condExp l v - torusCondExp β (2 * j + 1) l v) := by abel
  rw [e]
  exact form_sub_null _ (torusForm_symm hN β j) (torusForm_nonneg hN β j)
    (condExp_sub_null hN β S l v)

#print axioms dirichlet_wilson

/-- **THE ERGODIC LIMIT AT EVERY EXTENT.** For every heat-bath system `S` at `β` and extent index
`j` and all periodic gauge-invariant `f`, `g`: `B(Tᴹ f, g) → μⱼ(f) μⱼ(g)` for the lazy heat bath at
`K = |ι| + 1` (`HeatBathErgodic.ergodicLimit_of_poincare` with `u = 1`, `torus_poincare`,
`dirichlet_wilson`, `wilson_h_null` at `1`).

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN`. -/
theorem ergodicLimit_wilson (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j)
    (f g : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    ErgodicLimit S.toPatchSystem f g
      (torusState hN (2 * j + 1) β (f : C(GibbsSpec.IConf (SU N), ℝ))
        * torusState hN (2 * j + 1) β (g : C(GibbsSpec.IConf (SU N), ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := torus_poincare hN β j
  refine ergodicLimit_of_poincare S.toPatchSystem (oneT j) (torusForm_one_one hN β j)
    (fun v => ?_) hC0 (fun v => ?_) f g ?_
  · exact form_H_left_zero S.toPatchSystem (oneT j)
      (fun l => wilson_h_null' hN β S l (oneT j) (readsNot_one j l)) v
  · rw [dirichlet_wilson hN β S v]
    exact hC v
  · show torusForm hN β j f (oneT j) * torusForm hN β j g (oneT j) = _
    rw [torusForm_one, torusForm_one]

#print axioms ergodicLimit_wilson

end Torus

/-! ## 3. The neighbour map -/

section Neighbours

/-- **The neighbours of a torus link**: the link itself and the links sharing a plaquette with it.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def nbT (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) := by
  classical
  exact Finset.univ.filter (fun l' => l' = l ∨ SharePlaq (bdT (2 * j + 1)) l l')

/-- Membership in `nbT`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem mem_nbT (j : ℕ) (l l' : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    l' ∈ nbT j l ↔ l' = l ∨ SharePlaq (bdT (2 * j + 1)) l l' := by
  unfold nbT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

#print axioms mem_nbT

/-- **The candidate neighbours of `l` through one plane.** For `l = (μ, x)` and a direction `ν`, the
links other than `l` of the plaquettes `((μ, ν), x)` and `((μ, ν), x − ν̂)`, the two through `l` in
that plane (the reversed pair `(ν, μ)` visits the same links): `(ν, x)`, `(ν, x + μ̂)`, `(μ, x + ν̂)`,
`(ν, x − ν̂)`, `(ν, x − ν̂ + μ̂)`, `(μ, x − ν̂)`, the step back being `StrongCoupling.unshift`. At
`ν = μ` the plaquettes are the diagonal ones and the list is `l`, `(μ, x + μ̂)`, `(μ, x − μ̂)`, with
repeats (`nbPlane_self_sub`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def nbPlane (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) (ν : Fin 4) :
    Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :=
  {(ν, l.2), (ν, WilsonHypercubic.shift l.1 l.2), (l.1, WilsonHypercubic.shift ν l.2),
    (ν, StrongCoupling.unshift ν l.2),
    (ν, WilsonHypercubic.shift l.1 (StrongCoupling.unshift ν l.2)),
    (l.1, StrongCoupling.unshift ν l.2)}

/-- **The plane of `l.1` gives three candidates**: `l`, `(μ, x + μ̂)` and `(μ, x − μ̂)`
(`PeriodicStrongCoupling.shift_unshift`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem nbPlane_self_sub (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    nbPlane j l l.1
      ⊆ {(l.1, l.2), (l.1, WilsonHypercubic.shift l.1 l.2),
          (l.1, StrongCoupling.unshift l.1 l.2)} := by
  intro a ha
  simp only [nbPlane, PeriodicStrongCoupling.shift_unshift, Finset.mem_insert,
    Finset.mem_singleton] at ha ⊢
  rcases ha with h | h | h | h | h | h <;> subst h <;> simp

#print axioms nbPlane_self_sub

/-- **At most `21` neighbours at every extent.** A neighbour of `l = (μ, x)` other than `l` shares a
plaquette `((a, b), y)` with it; the plaquettes run over ordered pairs of directions, the diagonal
`a = b` included (`HeatBath.SharePlaq`), and every link of such a plaquette lies in `nbPlane j l a` or
`nbPlane j l b` (`StrongCoupling.unshift_shift`). The plane of `μ` gives at most `3`
(`nbPlane_self_sub`), each of the other three planes at most `6`.

DERIVED: `21 = 3 + 3 · 6`: `3` candidates in the plane of `μ` (`l` and its two neighbours along `μ`,
through the diagonal plaquettes), `3` other directions, `6` candidates in each (two plaquettes, three
other links apiece); `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family
and the `+ 1` its successor writing the extent. At every extent from `3` on the `21` candidates are
distinct; the theorem states only the bound. -/
theorem card_nbT_le (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    (nbT j l).card ≤ 21 := by
  have hsub : nbT j l ⊆ (Finset.univ : Finset (Fin 4)).biUnion (nbPlane j l) := by
    intro l' hl'
    rw [Finset.mem_biUnion]
    rcases (mem_nbT j l l').mp hl' with h | ⟨⟨⟨a, b⟩, y⟩, hq, hq'⟩
    · refine ⟨l.1, Finset.mem_univ _, ?_⟩
      rw [h]
      simp [nbPlane]
    · simp only [bdT, WilsonHypercubic.bd, List.map_cons, List.map_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at hq hq'
      rcases hq with h | h | h | h <;> subst h <;>
        rcases hq' with h' | h' | h' | h' <;> subst h' <;>
        first
          | (refine ⟨a, Finset.mem_univ _, ?_⟩; simp [nbPlane, StrongCoupling.unshift_shift]; done)
          | (refine ⟨b, Finset.mem_univ _, ?_⟩; simp [nbPlane, StrongCoupling.unshift_shift])
  have h6 : ∀ ν, (nbPlane j l ν).card ≤ 6 := fun ν => by
    unfold nbPlane
    exact Finset.card_le_six
  have h3 : (nbPlane j l l.1).card ≤ 3 :=
    (Finset.card_le_card (nbPlane_self_sub j l)).trans Finset.card_le_three
  calc (nbT j l).card
      ≤ ((Finset.univ : Finset (Fin 4)).biUnion (nbPlane j l)).card := Finset.card_le_card hsub
    _ ≤ ∑ ν, (nbPlane j l ν).card := Finset.card_biUnion_le
    _ = (nbPlane j l l.1).card + ∑ ν ∈ Finset.univ.erase l.1, (nbPlane j l ν).card :=
        (Finset.add_sum_erase Finset.univ (fun ν => (nbPlane j l ν).card)
          (Finset.mem_univ l.1)).symm
    _ ≤ 3 + ∑ _ν ∈ Finset.univ.erase l.1, 6 :=
        add_le_add h3 (Finset.sum_le_sum fun ν _ => h6 ν)
    _ = 21 := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] <;> norm_num

#print axioms card_nbT_le

variable {N : ℕ}

/-- **LOCALITY OF EVERY HEAT-BATH SYSTEM**: `LocalCommute S.toPatchSystem (nbT j) 21`
(`card_nbT_le`, `condExp_comm_null`).

DERIVED: `21` is `card_nbT_le`'s bound; `2 * j + 1` is the index of the even-extent family; `0` is
the excluded rank in `hN`. -/
theorem localCommute_wilson (hN : N ≠ 0) (β : ℝ) {j : ℕ} (S : WilsonHeatBath hN β j) :
    LocalCommute S.toPatchSystem (nbT j) 21 := by
  refine ⟨fun l => card_nbT_le j l, fun l l' hl' u => ?_⟩
  have hne : l' ≠ l := fun h => hl' ((mem_nbT j l l').mpr (Or.inl h))
  have hs : ¬ SharePlaq (bdT (2 * j + 1)) l l' := fun h => hl' ((mem_nbT j l l').mpr (Or.inr h))
  exact condExp_comm_null hN β S hne hs u

#print axioms localCommute_wilson

end Neighbours

/-! ## 4. Supports -/

section Support

variable {N : ℕ}

/-- **An observable local on `T` does not read the torus links off the image of `T`**.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem readsNot_of_isLocalOn {T : Finset InfiniteLattice.ILink}
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : InfiniteLattice.IsLocalOn T ⇑F) (j : ℕ)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (hl : l ∉ T.image (InfiniteLattice.linkMod (2 * j + 1))) : ReadsNot j l F := by
  unfold ReadsNot
  intro W g
  refine hF _ _ (fun l0 hl0 => ?_)
  show Function.update W l g (InfiniteLattice.linkMod (2 * j + 1) l0)
    = W (InfiniteLattice.linkMod (2 * j + 1) l0)
  exact Function.update_of_ne (fun h => hl (Finset.mem_image.mpr ⟨l0, hl0, h⟩)) g W

#print axioms readsNot_of_isLocalOn

/-- **The reflected observable is local on the reflected set**.

DERIVED: `4` is the spacetime dimension. -/
theorem isLocalOn_ireflObs {T : Finset InfiniteLattice.ILink}
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : InfiniteLattice.IsLocalOn T ⇑F) (τ : Fin 4) (c : ℤ) :
    InfiniteLattice.IsLocalOn (T.image (LatticeReflection.ireflLink τ c))
      ⇑(LatticeReflection.ireflObs τ c F) := by
  intro U V hUV
  show F (LatticeReflection.ireflConf τ c U) = F (LatticeReflection.ireflConf τ c V)
  refine hF _ _ (fun l hl => ?_)
  have h := hUV _ (Finset.mem_image_of_mem (LatticeReflection.ireflLink τ c) hl)
  simp only [LatticeReflection.ireflConf, h]

#print axioms isLocalOn_ireflObs

/-- `(ishiftConf τ)ᵐ U` at `l` is `U` at `(ishiftLink τ)ᵐ l`.

DERIVED: `4` is the spacetime dimension. -/
theorem ishiftConf_iterate_apply (τ : Fin 4) (m : ℕ) (U : GibbsSpec.IConf (SU N))
    (l : InfiniteLattice.ILink) :
    ((InfiniteShift.ishiftConf τ)^[m] U) l = U ((InfiniteShift.ishiftLink τ)^[m] l) := by
  induction m generalizing U with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply (f := InfiniteShift.ishiftConf (G := SU N) τ), ih,
      Function.iterate_succ_apply' (f := InfiniteShift.ishiftLink τ)]
    rfl

#print axioms ishiftConf_iterate_apply

/-- `(ishiftObsL τ)ᵐ F` at `U` is `F` at `(ishiftConf τ)ᵐ U`.

DERIVED: `4` is the spacetime dimension. -/
theorem ishiftObsL_iterate_apply (τ : Fin 4) (m : ℕ) (F : C(GibbsSpec.IConf (SU N), ℝ))
    (U : GibbsSpec.IConf (SU N)) :
    ((⇑(ReflectionShift.ishiftObsL τ))^[m] F) U = F ((InfiniteShift.ishiftConf τ)^[m] U) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply (f := ⇑(ReflectionShift.ishiftObsL (G := SU N) τ)), ih,
      Function.iterate_succ_apply' (f := InfiniteShift.ishiftConf (G := SU N) τ)]
    rfl

#print axioms ishiftObsL_iterate_apply

/-- **The shifted observable is local on the shifted set**.

DERIVED: `4` is the spacetime dimension. -/
theorem isLocalOn_iterate_shift {T : Finset InfiniteLattice.ILink}
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : InfiniteLattice.IsLocalOn T ⇑F) (τ : Fin 4) (m : ℕ) :
    InfiniteLattice.IsLocalOn (T.image ((InfiniteShift.ishiftLink τ)^[m]))
      ⇑((⇑(ReflectionShift.ishiftObsL τ))^[m] F) := by
  intro U V hUV
  rw [ishiftObsL_iterate_apply, ishiftObsL_iterate_apply]
  refine hF _ _ (fun l hl => ?_)
  rw [ishiftConf_iterate_apply, ishiftConf_iterate_apply]
  exact hUV _ (Finset.mem_image_of_mem _ hl)

#print axioms isLocalOn_iterate_shift

/-- **The shifted observable stays gauge invariant** (`GaugeInvariantAlgebra.ishiftConf_igaugeTransform`).

DERIVED: `4` is the spacetime dimension. -/
theorem isIGaugeInvariant_iterate_shift {F : C(GibbsSpec.IConf (SU N), ℝ)}
    (hF : GaugeInvariantAlgebra.IsIGaugeInvariant F) (τ : Fin 4) (m : ℕ) :
    GaugeInvariantAlgebra.IsIGaugeInvariant ((⇑(ReflectionShift.ishiftObsL τ))^[m] F) := by
  induction m with
  | zero => exact hF
  | succ m ih =>
    rw [Function.iterate_succ_apply' (f := ⇑(ReflectionShift.ishiftObsL (G := SU N) τ))]
    intro g U
    show ((⇑(ReflectionShift.ishiftObsL τ))^[m] F)
        (InfiniteShift.ishiftConf τ (GaugeInvariantAlgebra.igaugeTransform g U))
      = ((⇑(ReflectionShift.ishiftObsL τ))^[m] F) (InfiniteShift.ishiftConf τ U)
    rw [GaugeInvariantAlgebra.ishiftConf_igaugeTransform]
    exact ih _ _

#print axioms isIGaugeInvariant_iterate_shift

/-- `‖x ∘ ·‖` bound: `μ(F · F) ≤ ‖G‖²` when `|F| ≤ ‖G‖` pointwise (`DLRLimit.State.le_norm`).

DERIVED: `2` is the square; `0` is the excluded rank in `hN`. -/
theorem torusState_sq_le (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F G : C(GibbsSpec.IConf (SU N), ℝ))
    (h : ∀ U, |F U| ≤ ‖G‖) : torusState hN M β (F * F) ≤ ‖G‖ ^ 2 := by
  refine (DLRLimit.State.le_norm _ _).trans
    ((ContinuousMap.norm_le _ (sq_nonneg _)).mpr (fun U => ?_))
  rw [ContinuousMap.mul_apply, norm_mul, Real.norm_eq_abs, sq]
  exact mul_le_mul (h U) (h U) (abs_nonneg _) (norm_nonneg _)

#print axioms torusState_sq_le

end Support

/-! ## 5. Separation along the neighbour map -/

section Separation

/-- **A potential gives separation**: `ψ` vanishing on `A` and growing by at most one per step of
`nb` gives `Far nb A k l` at every `k ≤ ψ l`.

DERIVED: `0` is the value on `A` and the base level; `1` is the step bound. -/
theorem far_of_potential {ι : Type*} (nb : ι → Finset ι) (A : Finset ι) (ψ : ι → ℕ)
    (hA : ∀ a ∈ A, ψ a = 0) (hlip : ∀ l, ∀ l' ∈ nb l, ψ l ≤ ψ l' + 1) :
    ∀ (k : ℕ) (l : ι), k ≤ ψ l → Far nb A k l := by
  intro k
  induction k with
  | zero =>
    intro l _
    exact trivial
  | succ k ih =>
    intro l hk
    refine (far_succ nb A k l).mpr ⟨fun hl => ?_, ih l (by omega), fun l' hl' => ih l' ?_⟩
    · have := hA l hl
      omega
    · have := hlip l l' hl'
      omega

#print axioms far_of_potential

/-- `(s + 1).val` is `s.val + 1`, or `0` at `s = M`.

DERIVED: `1` is the unit step and the successor writing the extent; `0` is the wrap value. -/
theorem val_add_one_cases {M : ℕ} (s : Fin (M + 1)) :
    ((s + 1 : Fin (M + 1)) : ℕ) = (s : ℕ) + 1 ∨ ((s : ℕ) = M ∧ ((s + 1 : Fin (M + 1)) : ℕ) = 0) := by
  have hs := s.isLt
  have e : ((s + 1 : Fin (M + 1)) : ℕ) = ((s : ℕ) + 1 % (M + 1)) % (M + 1) := by
    rw [Fin.val_add, Fin.val_one']
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    right
    have h1 := (s + 1 : Fin (0 + 1)).isLt
    omega
  · have h1 : 1 % (M + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1] at e
    rcases Nat.lt_or_ge ((s : ℕ) + 1) (M + 1) with h | h
    · left
      rw [e]
      exact Nat.mod_eq_of_lt h
    · right
      have hsM : (s : ℕ) = M := by omega
      refine ⟨hsM, ?_⟩
      rw [e, hsM]
      exact Nat.mod_self (M + 1)

#print axioms val_add_one_cases

/-- `(finMod M k).val = k` for `0 ≤ k ≤ M`.

DERIVED: `0` and `1` bound the residue range. -/
theorem finMod_val (M : ℕ) {k : ℤ} (h0 : 0 ≤ k) (h1 : k < (M : ℤ) + 1) :
    ((InfiniteLattice.finMod M k : Fin (M + 1)) : ℕ) = k.toNat := by
  show (k % ((M : ℤ) + 1)).toNat = k.toNat
  rw [Int.emod_eq_of_lt h0 h1]

#print axioms finMod_val

/-- The torus offset of `z` from `a₀` is `z − a₀` when `0 ≤ z − a₀ ≤ M` (`PeriodicState.finMod_sub`).

DERIVED: `0` and `1` bound the residue range. -/
theorem off_eq (M : ℕ) (z a0 : ℤ) (h0 : 0 ≤ z - a0) (h1 : z - a0 < (M : ℤ) + 1) :
    ((InfiniteLattice.finMod M z - InfiniteLattice.finMod M a0 : Fin (M + 1)) : ℕ)
      = (z - a0).toNat := by
  rw [← PeriodicState.finMod_sub, finMod_val M h0 h1]

#print axioms off_eq

/-- **The potential on offsets**: `min(o − (R + 1), M + 1 − o)`, the distance from the window
`[0, R + 1]` around the circle of length `M + 1`, truncated at `0`.

DERIVED: `1` is the window's end past `R` and the successor writing the circle's length. -/
def psiT (R M o : ℕ) : ℕ := min (o - (R + 1)) (M + 1 - o)

/-- The potential moves by at most one between an offset and its successor on the circle.

DERIVED: `1` is the step; `0` is the wrap value. -/
theorem psiT_lip {R M o o' : ℕ} (ho : o ≤ M) (ho' : o' ≤ M) (h : o' = o + 1 ∨ (o = M ∧ o' = 0)) :
    psiT R M o ≤ psiT R M o' + 1 ∧ psiT R M o' ≤ psiT R M o + 1 := by
  simp only [psiT, min_def]
  constructor <;> split_ifs <;> omega

#print axioms psiT_lip

/-- **The potential on torus links**: `psiT` at the `τ`-offset of the base site from `finMod a₀`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def psiL (j : ℕ) (τ : Fin 4) (a0 : ℤ) (R : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) : ℕ :=
  psiT R (2 * j + 1) ((l.2 τ - InfiniteLattice.finMod (2 * j + 1) a0 : Fin (2 * j + 1 + 1)) : ℕ)

/-- **The potential grows by at most one along `nbT`**: a neighbour's `τ`-coordinate differs by
`0`, `1` or `−1` (`BoxPatch.sharePlaq_disp`, `val_add_one_cases`, `psiT_lip`).

DERIVED: `4` is the spacetime dimension; `1` is the step; `0`, `1`, `−1` are the coordinate
steps; `2 * j + 1` is the index of the even-extent family and the `+ 1` its successor writing the
extent. -/
theorem psiL_lip (j : ℕ) (τ : Fin 4) (a0 : ℤ) (R : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :
    ∀ l' ∈ nbT j l, psiL j τ a0 R l ≤ psiL j τ a0 R l' + 1 := by
  intro l' hl'
  rcases (mem_nbT j l l').mp hl' with h | hs
  · rw [h]
    omega
  · obtain ⟨_, _, h01⟩ := BoxPatch.sharePlaq_disp hs
    have hd := h01.2 τ
    simp only [Pi.sub_apply] at hd
    obtain ⟨c0, hc0⟩ : ∃ c0 : Fin (2 * j + 1 + 1), c0 = InfiniteLattice.finMod (2 * j + 1) a0 :=
      ⟨_, rfl⟩
    have hs' : l'.2 τ - c0 = (l.2 τ - c0) + (l'.2 τ - l.2 τ) := by abel
    unfold psiL
    rw [← hc0]
    rcases hd with hd | hd | hd
    · rw [sub_eq_zero.mp hd]
      omega
    · have e : l'.2 τ - c0 = (l.2 τ - c0) + 1 := by rw [hs', hd]
      rw [e]
      have hb := (l.2 τ - c0).isLt
      have hb' := ((l.2 τ - c0) + 1).isLt
      exact (psiT_lip (by omega) (by omega) (val_add_one_cases (l.2 τ - c0))).1
    · have e : l.2 τ - c0 = (l'.2 τ - c0) + 1 := by
        rw [hs', hd]
        abel
      rw [e]
      have hb := (l'.2 τ - c0).isLt
      have hb' := ((l'.2 τ - c0) + 1).isLt
      exact (psiT_lip (by omega) (by omega) (val_add_one_cases (l'.2 τ - c0))).2

#print axioms psiL_lip

/-- The `τ`-coordinate of a reflected link's base: `c − 1 − x_τ` on a `τ`-link, `c − x_τ` otherwise.

DERIVED: `4` is the spacetime dimension; `1` is the length of a link. -/
theorem ireflLink_coord (τ : Fin 4) (c : ℤ) (l : InfiniteLattice.ILink) :
    (LatticeReflection.ireflLink τ c l).2 τ = if l.1 = τ then c - 1 - l.2 τ else c - l.2 τ := by
  by_cases h : l.1 = τ <;> simp [LatticeReflection.ireflLink, h]

#print axioms ireflLink_coord

/-- The `τ`-coordinate of a link's base after `m` unit shifts along `τ` is `x_τ + m`.

DERIVED: `4` is the spacetime dimension; `0` and `1` are the recursion's base and step. -/
theorem ishiftLink_iterate_coord (τ : Fin 4) (m : ℕ) (l : InfiniteLattice.ILink) :
    ((InfiniteShift.ishiftLink τ)^[m] l).2 τ = l.2 τ + (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply' (f := InfiniteShift.ishiftLink τ)]
    have e : ∀ l' : InfiniteLattice.ILink, (InfiniteShift.ishiftLink τ l').2 τ = l'.2 τ + 1 := by
      intro l'
      simp [InfiniteShift.ishiftLink, InfiniteLattice.ishift]
    rw [e, ih]
    omega

#print axioms ishiftLink_iterate_coord

end Separation

/-! ## 6. The locality hypothesis -/

section Wilson

variable {N : ℕ}

/-- **THE HEAT-BATH LOCALITY HOLDS AT `z = 21`.** At every `τ`, `p`, `N ≠ 0`, real `β` and family
`S` of heat-bath systems, `HeatBathGapDecay.LocalityAt τ p hN β S 21` (`localCommute_wilson`). For `x` local on `T` inside the half-space `x_τ ≥ p`, with `T`
of `τ`-depth `R`: `a = b = |T|`, `M = ‖x‖²`, and for `j ≥ 3n + 2R + 3` the neighbour map `nbT j`,
`f = θx`, `g = S^{2n}x`, `L = μⱼ(θx) μⱼ(S^{2n}x)`: the supports are the images of `T`
(`readsNot_of_isLocalOn`, `wilson_h_null`), separated at level `n` by the potential `psiL` with
window start `a₀ = p − 1 − R` (`far_of_potential`, `psiL_lip`), the norms are at most `‖x‖²`
(`torusState_sq_le`), the ergodic limit is `ergodicLimit_wilson`, and the connected pairing is
`B(f, g) − L` by definition.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`; `2` is the even lag and
the doubling of the reflection plane; `21` is `card_nbT_le`'s bound; `1` in `p − 1 − R` is the link
length of `ireflLink_coord`. CHOSEN: the threshold
`3n + 2R + 3`, large enough that the reflected window `[p − 1 − R, p]` and the shifted window
`[p + 2n, p + 2n + R]` sit at cyclic distance at least `n` on the circle of length `2j + 2`. -/
theorem localityAt_holds (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (S : ∀ j : ℕ, WilsonHeatBath hN β j) : LocalityAt τ p hN β S 21 := by
  intro x hx
  obtain ⟨T, hTsub, hTloc⟩ := (Submodule.mem_inf.mp hx).1
  have hxg : GaugeInvariantAlgebra.IsIGaugeInvariant x := (Submodule.mem_inf.mp hx).2
  have hTp : ∀ l ∈ T, p ≤ l.2 τ := fun l hl => hTsub (Finset.mem_coe.mpr hl)
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ l ∈ T, l.2 τ ≤ p + R := by
    refine ⟨T.sup (fun l => (l.2 τ - p).toNat), fun l hl => ?_⟩
    have h1 : (l.2 τ - p).toNat ≤ T.sup (fun l => (l.2 τ - p).toNat) :=
      Finset.le_sup (f := fun l => (l.2 τ - p).toNat) hl
    have h2 : (((l.2 τ - p).toNat : ℕ) : ℤ) = l.2 τ - p :=
      Int.toNat_of_nonneg (by linarith [hTp l hl])
    omega
  have hθg := ContinuumField.isIGaugeInvariant_ireflObs hxg τ (2 * p)
  refine ⟨T.card, T.card, ‖x‖ ^ 2, fun n => ?_⟩
  have hSg := isIGaugeInvariant_iterate_shift hxg τ (2 * n)
  filter_upwards [Filter.eventually_ge_atTop (3 * n + 2 * R + 3)] with j hj
  -- the potential vanishes on the reflected support
  have hA0 : ∀ a ∈ (T.image (LatticeReflection.ireflLink τ (2 * p))).image
      (InfiniteLattice.linkMod (2 * j + 1)), psiL j τ (p - 1 - R) R a = 0 := by
    intro a ha
    obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hl1
    have hp0 := hTp l0 hl0
    have hr0 := hR l0 hl0
    have hz := ireflLink_coord τ (2 * p) l0
    have hb : p - 1 - (R : ℤ) ≤ (LatticeReflection.ireflLink τ (2 * p) l0).2 τ
        ∧ (LatticeReflection.ireflLink τ (2 * p) l0).2 τ ≤ p := by
      rw [hz]
      split_ifs <;> constructor <;> omega
    have h0 : 0 ≤ (LatticeReflection.ireflLink τ (2 * p) l0).2 τ - (p - 1 - R) := by omega
    have h1 : (LatticeReflection.ireflLink τ (2 * p) l0).2 τ - (p - 1 - R)
        < ((2 * j + 1 : ℕ) : ℤ) + 1 := by
      omega
    have ht := Int.toNat_of_nonneg h0
    show psiT R (2 * j + 1)
        ((InfiniteLattice.finMod (2 * j + 1) ((LatticeReflection.ireflLink τ (2 * p) l0).2 τ)
          - InfiniteLattice.finMod (2 * j + 1) (p - 1 - R) : Fin (2 * j + 1 + 1)) : ℕ) = 0
    rw [off_eq (2 * j + 1) _ _ h0 h1]
    simp only [psiT, min_def]
    split_ifs <;> omega
  -- the potential is at least `n` on the shifted support
  have hCn : ∀ c ∈ (T.image ((InfiniteShift.ishiftLink τ)^[2 * n])).image
      (InfiniteLattice.linkMod (2 * j + 1)), n ≤ psiL j τ (p - 1 - R) R c := by
    intro c hc
    obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hl1
    have hp0 := hTp l0 hl0
    have hr0 := hR l0 hl0
    have hz := ishiftLink_iterate_coord τ (2 * n) l0
    have h0 : 0 ≤ ((InfiniteShift.ishiftLink τ)^[2 * n] l0).2 τ - (p - 1 - R) := by omega
    have h1 : ((InfiniteShift.ishiftLink τ)^[2 * n] l0).2 τ - (p - 1 - R)
        < ((2 * j + 1 : ℕ) : ℤ) + 1 := by
      omega
    have ht := Int.toNat_of_nonneg h0
    show n ≤ psiT R (2 * j + 1)
        ((InfiniteLattice.finMod (2 * j + 1) (((InfiniteShift.ishiftLink τ)^[2 * n] l0).2 τ)
          - InfiniteLattice.finMod (2 * j + 1) (p - 1 - R) : Fin (2 * j + 1 + 1)) : ℕ)
    rw [off_eq (2 * j + 1) _ _ h0 h1]
    simp only [psiT, min_def]
    split_ifs <;> omega
  refine ⟨nbT j, localCommute_wilson hN β (S j),
    ⟨LatticeReflection.ireflObs τ (2 * p) x,
      periodicGaugeInv_of_isIGaugeInvariant (2 * j + 1) hθg⟩,
    ⟨(⇑(ReflectionShift.ishiftObsL τ))^[2 * n] x,
      periodicGaugeInv_of_isIGaugeInvariant (2 * j + 1) hSg⟩,
    _, ?_, ?_, ?_, ergodicLimit_wilson hN β (S j) _ _, rfl⟩
  · refine ⟨((T.image (LatticeReflection.ireflLink τ (2 * p))).image
        (InfiniteLattice.linkMod (2 * j + 1)) : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))),
      ((T.image ((InfiniteShift.ishiftLink τ)^[2 * n])).image (InfiniteLattice.linkMod (2 * j + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))),
      (Finset.card_image_le.trans Finset.card_image_le :
        (((T.image (LatticeReflection.ireflLink τ (2 * p))).image (InfiniteLattice.linkMod (2 * j + 1))
          : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))).card ≤ T.card),
      (Finset.card_image_le.trans Finset.card_image_le :
        (((T.image ((InfiniteShift.ishiftLink τ)^[2 * n])).image (InfiniteLattice.linkMod (2 * j + 1))
          : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))).card ≤ T.card),
      fun l hl => wilson_h_null' hN β (S j) l _
        (readsNot_of_isLocalOn (isLocalOn_ireflObs hTloc τ (2 * p)) j l hl),
      fun l hl => wilson_h_null' hN β (S j) l _
        (readsNot_of_isLocalOn (isLocalOn_iterate_shift hTloc τ (2 * n)) j l hl),
      fun l hl => far_of_potential (nbT j) _ (psiL j τ (p - 1 - R) R) hA0
        (psiL_lip j τ (p - 1 - R) R) n l (hCn l hl)⟩
  · show torusState hN (2 * j + 1) β
        (LatticeReflection.ireflObs τ (2 * p) x * LatticeReflection.ireflObs τ (2 * p) x)
      ≤ ‖x‖ ^ 2
    exact torusState_sq_le hN (2 * j + 1) β _ x (fun U => by
      rw [LatticeReflection.ireflObs_apply, ← Real.norm_eq_abs]
      exact x.norm_coe_le_norm _)
  · show torusState hN (2 * j + 1) β
        ((⇑(ReflectionShift.ishiftObsL τ))^[2 * n] x * (⇑(ReflectionShift.ishiftObsL τ))^[2 * n] x)
      ≤ ‖x‖ ^ 2
    exact torusState_sq_le hN (2 * j + 1) β _ x (fun U => by
      rw [ishiftObsL_iterate_apply, ← Real.norm_eq_abs]
      exact x.norm_coe_le_norm _)

#print axioms localityAt_holds

/-- **THE HEAT-BATH LOCALITY HYPOTHESIS HOLDS.** At every `τ`, `p`, `N ≠ 0` and real `β`,
`HeatBathGapDecay.HeatBathLocality τ p hN β`, at `z = 21` (`localityAt_holds`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`; `21` is
`card_nbT_le`'s bound. -/
theorem heatBathLocality_holds (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) :
    HeatBathLocality τ p hN β :=
  fun S => ⟨21, localityAt_holds τ p hN β S⟩

#print axioms heatBathLocality_holds

/-- **`KnabeCriterion.HeatBathDecay` HOLDS** at every `τ`, `p`, `N ≠ 0` and real `β`: a uniform
heat-bath gap gives the single-lag input `ChessboardRead.TorusLagClear`
(`HeatBathGapDecay.heatBathDecay_of_locality`, `heatBathLocality_holds`). The gap is the hypothesis
`HeatBathDecay` quantifies over (`c > 0` with `GlobalGap c` for all large `j`); on the finite-size
route `BoxPatch.BoxPatchGap` supplies it through `KnabeCriterion.PatchGapCheck`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem heatBathDecay_holds (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) : HeatBathDecay τ p hN β :=
  heatBathDecay_of_locality τ p hN β (heatBathLocality_holds τ p hN β)

#print axioms heatBathDecay_holds

/-- **The IR rate of a box.** `BoxPatch.BoxPatchGap hN β₀ n γ` gives the heat-bath gap
`c₀ = boxKnabe n γ` (`BoxPatch.boxFamily_check`), clustering at `clusterRate 21 c₀`
(`torusClusterAt_of_localityAt`, `localityAt_holds`) and the IR gap at the rate
`−log(clusterRate 21 c₀)/aRun N β₀`; `boxRate_eq` evaluates it.

DERIVED: `21` is `card_nbT_le`'s bound. -/
def boxRate (N : ℕ) (β₀ : ℝ) (n : ℕ) (γ : ℝ) : ℝ :=
  -Real.log (clusterRate 21 (BoxPatch.boxKnabe n γ)) / MassGap.AsymptoticScaling.aRun N β₀

/-- **A box gives the IR gap at its rate.** At `1 ≤ N` and `0 < β₀`, `BoxPatch.BoxPatchGap hN β₀ n γ`
gives `0 < boxRate N β₀ n γ` and `UVIRSplit.IRGapAt τ p hN β₀ (boxRate N β₀ n γ)`
(`BoxPatch.boxFamily_check`, `torusClusterAt_of_localityAt`, `gapAt_of_torusClusterAt`).

DERIVED: `4` is the spacetime dimension; `1` is the least colour count; `0` is the excluded rank and
the sign of `β₀` and of the rate. -/
theorem irGapAt_boxRate (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ γ : ℝ} {n : ℕ}
    (hβ₀ : 0 < β₀) (hbox : BoxPatch.BoxPatchGap hN β₀ n γ) :
    0 < boxRate N β₀ n γ ∧ UVIRSplit.IRGapAt τ p hN β₀ (boxRate N β₀ n γ) := by
  obtain ⟨S, hS⟩ := BoxPatch.boxFamily_check hN hbox
  have hc₀ : 0 < BoxPatch.boxKnabe n γ := (BoxPatch.boxKnabe_pos_iff hbox.1 γ).mpr hbox.2.1
  have hG : ∀ᶠ j in Filter.atTop, (S j).toPatchSystem.GlobalGap (BoxPatch.boxKnabe n γ) :=
    hS.mono (fun j hj => (S j).toPatchSystem.globalGap_mono hj.2.1
      ((S j).toPatchSystem.globalGap_of_localGap hj.1 hj.2.2))
  obtain ⟨hr0, hr1, hcl⟩ :=
    torusClusterAt_of_localityAt τ p hN β₀ (localityAt_holds τ p hN β₀ S) hc₀ hG
  have hg := gapAt_of_torusClusterAt τ p hN β₀ hr0.le hcl
  have ha : 0 < MassGap.AsymptoticScaling.aRun N β₀ := MassGap.AsymptoticScaling.aRun_pos hN1 hβ₀
  refine ⟨div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) ha, ?_⟩
  unfold UVIRSplit.IRGapAt boxRate
  rw [div_mul_cancel₀ _ ha.ne', neg_neg, Real.exp_log hr0]
  exact hg

#print axioms irGapAt_boxRate

/-- **The box rate in closed form**: `boxRate N β₀ n γ = min(boxKnabe n γ, 1)/(508 · aRun N β₀)`.
The second argument of `clusterRate`'s maximum wins: `e^{−min(c,1)/254} ≥ 1 − 1/254 > e/3`
(`Real.add_one_le_exp`, `Real.exp_one_lt_d9`: `e/3 < 0.907 < 0.996`).

DERIVED: `508 = 4 · 127 = 4(6 · 21 + 1)`, the `2` of `gapRate`'s exponent times the `2` of the
square root times the levels per sweep `2zy + 1` at `z = 21`, `y = 3`; `127 = 6 · 21 + 1`, the `6`
being `2y`; `254 = 2 · 127`; the `3` of `e/3` is `y`; `1` caps `c`. -/
theorem boxRate_eq (N : ℕ) (β₀ : ℝ) (n : ℕ) (γ : ℝ) :
    boxRate N β₀ n γ
      = min (BoxPatch.boxKnabe n γ) 1 / (508 * MassGap.AsymptoticScaling.aRun N β₀) := by
  have hD : ((6 * 21 + 1 : ℕ) : ℝ) = 127 := by norm_num
  have hy1 : min (BoxPatch.boxKnabe n γ) 1 ≤ 1 := min_le_right _ _
  have hmax : max (Real.exp 1 / 3)
      (Real.exp (-(min (BoxPatch.boxKnabe n γ) 1 / (2 * ((6 * 21 + 1 : ℕ) : ℝ)))))
      = Real.exp (-(min (BoxPatch.boxKnabe n γ) 1 / 254)) := by
    rw [hD]
    have e1 : -(min (BoxPatch.boxKnabe n γ) 1 / (2 * 127))
        = -(min (BoxPatch.boxKnabe n γ) 1 / 254) := by ring
    rw [e1]
    apply max_eq_right
    have h1 := Real.add_one_le_exp (-(min (BoxPatch.boxKnabe n γ) 1 / 254))
    have h2 := Real.exp_one_lt_d9
    linarith
  unfold boxRate clusterRate
  rw [hmax, Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
  have e2 : -(-(min (BoxPatch.boxKnabe n γ) 1 / 254) / 2)
      = min (BoxPatch.boxKnabe n γ) 1 / 508 := by ring
  rw [e2, div_div]

#print axioms boxRate_eq

end Wilson

end MassGap.HeatBathLocal
