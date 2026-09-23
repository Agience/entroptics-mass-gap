import Mathlib
import MassGap.LatticeReflection
import MassGap.InfiniteShift

/-!
# MassGap.ReflectionShift — reflections and the time shift on `ℤ⁴`

The file supplies a backward shift on the infinite lattice and proves the identities relating it to
the reflections `ireflSite`, `ireflLink`, `ireflConf` and `ireflObs`. Three of them have the shapes
`SchwarzIteration.ShiftCompat` asks for: `ishiftObsL_mul` is `T_mul`, `ishiftObsL_iunshiftObs` is
`T_S`, and `ireflObs_ishiftObs` is `theta_T`. `nu_T_of_reflection_invariant` derives the fourth,
`nu_T`, from reflection invariance of the state at two adjacent constants, and
`reflection_invariant_succ_iff_nu_T` shows those two are equivalent given invariance at the first.

## The geometry

A step along the axis moves the reflection constant by one, `ireflSite τ c (ishift τ x) =
ireflSite τ (c - 1) x`, because `c - (x τ + 1) = (c - 1) - x τ`. On links the base shift of
`ireflLink` travels with the constant, so `ireflLink τ c ∘ ishiftLink τ = ireflLink τ (c - 1)` in
both cases of the direction split: `τ`-links reflect about `c - 1` and land on `c - 2`, the others
reflect about `c` and land on `c - 1`.

The inversion `ireflConf` applies on `τ`-links never has to be tracked. `ishiftLink` and
`iunshiftLink` preserve a link's direction, so both sides of every identity carry the same
`l.1 = τ` split and the inverses cancel case by case.

## Two reflections compose to one translation

`ireflSite_comp` computes the composite of reflections about `a` and `b` as a translation by `a - b`
in the `τ` coordinate. At separation one, `ireflSite_comp_succ`, `ireflLink_comp_succ` and
`ireflConf_comp_eq_shift` give the forward shift; `ireflObs_comp_eq_shiftObs` is the observable
form, where precomposition reverses the order of the two constants.

Scope: the axis type is `Fin 4` throughout and the coordinates are `ℤ`, so these are statements on
the infinite lattice, not the periodic torus. `WilsonTransfer.shiftConf_reflConf_shiftConf` is the
corresponding identity there. The order of the two constants is load-bearing:
`ireflConf τ a (ireflConf τ (a + 1) U)` is the forward shift, and the reversed composite is not
covered. The separation is one: a composite at separation `k` translates by `k`, but
`WilsonTransferReduction.shiftCompat_of_nu_T` fixes `T := ishiftObsL τ`, a single step.
`nu_T_of_reflection_invariant` takes both reflection invariances as hypotheses; one of the two
constants is always odd, hence the link reflection, and `IsReflectionInvariant` is an equality, so no
sign condition on the coupling enters.
-/

namespace MassGap.ReflectionShift

open MassGap.InfiniteLattice MassGap.LatticeReflection MassGap.InfiniteShift

/-! ## 1. Sites: a step along the axis moves the reflection constant by one -/

/-- `ireflSite τ c (ishift τ x) = ireflSite τ (c - 1) x`. Checked coordinatewise: at the axis `τ`
both sides reduce to `c - (x τ + 1) = (c - 1) - x τ`, and every other coordinate is untouched by both
maps.

This is `Reflect.reflSite_shift_axis` over `ℤ` rather than `Fin n`; the coordinates being integers,
no modular subtraction is involved.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the step, `ishift`'s own, and
the amount the reflection constant moves. -/
theorem ireflSite_ishift (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (ishift τ x) = ireflSite τ (c - 1) x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp only [ireflSite, ishift, Function.update_self]
    ring_nf
  · simp [ireflSite, ishift, Function.update_of_ne h]

#print axioms ireflSite_ishift

/-- `Function.update (ireflSite τ c x) τ ((ireflSite τ c x) τ - 1) = ireflSite τ (c - 1) x`:
lowering the `τ` coordinate of a reflected site by one is reflecting about the previous constant.
Checked coordinatewise, as for `ireflSite_ishift`.

Scope: the left side is written out rather than through `iunshift`, which is defined after it.

DERIVED: `4` is the spacetime dimension; `1` occurs twice — the amount subtracted from the
coordinate, and the amount the reflection constant moves. -/
theorem iunshift_ireflSite (τ : Fin 4) (c : ℤ) (x : ISite) :
    Function.update (ireflSite τ c x) τ ((ireflSite τ c x) τ - 1) = ireflSite τ (c - 1) x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp only [ireflSite, Function.update_self]
    ring_nf
  · simp [ireflSite, Function.update_of_ne h]

#print axioms iunshift_ireflSite

/-! ## 2. The backward shift on sites, links and configurations -/

/-- The backward shift on sites: `Function.update x τ (x τ - 1)`, lowering the `τ` coordinate by one
and leaving the rest. `InfiniteShift` carries only the forward translation `ishift`;
`SchwarzIteration.ShiftCompat` needs both directions.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the single lattice step
subtracted from the `τ` coordinate. -/
def iunshift (τ : Fin 4) (x : ISite) : ISite := Function.update x τ (x τ - 1)

/-- `ishift τ (iunshift τ x) = x`: the forward shift undoes the backward one on sites. Checked
coordinatewise; at `τ` the two updates cancel and elsewhere neither map acts.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. The single step lives inside
`ishift` and `iunshift`, not in this statement. -/
theorem ishift_iunshift (τ : Fin 4) (x : ISite) : ishift τ (iunshift τ x) = x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp [ishift, iunshift, Function.update_self]
  · simp [ishift, iunshift, Function.update_of_ne h]

#print axioms ishift_iunshift

/-- The backward shift on links: `(l.1, iunshift τ l.2)`. The direction component is untouched, as
for `ishiftLink`, which is what makes the `l.1 = τ` case split the same on both sides of every
identity below.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. The `.1` and `.2` are projection
notation, not numerals. -/
def iunshiftLink (τ : Fin 4) (l : ILink) : ILink := (l.1, iunshift τ l.2)

@[simp] theorem iunshiftLink_fst (τ : Fin 4) (l : ILink) : (iunshiftLink τ l).1 = l.1 := rfl

@[simp] theorem ishiftLink_fst' (τ : Fin 4) (l : ILink) : (ishiftLink τ l).1 = l.1 := rfl

theorem ishiftLink_iunshiftLink (τ : Fin 4) (l : ILink) :
    ishiftLink τ (iunshiftLink τ l) = l := by
  obtain ⟨μ, x⟩ := l
  simp [ishiftLink, iunshiftLink, ishift_iunshift]

#print axioms ishiftLink_iunshiftLink

/-! ## 3. Links: reflecting after a shift is reflecting about the previous constant -/

/-- `ireflLink τ c (ishiftLink τ l) = ireflLink τ (c - 1) l`. The proof splits on `l.1 = τ` and
closes both branches with `ireflSite_ishift`: a `τ`-link is reflected about `c - 1` and the step
sends it to `c - 2`, which is the `τ`-case of `ireflLink τ (c - 1)`; any other link is reflected
about `c` and the step sends it to `c - 1`, which is the other case. The base shift `ireflLink`
applies to `τ`-links moves with the constant, so one identity covers both branches.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the amount the reflection
constant moves, inherited from `ireflSite_ishift`. -/
theorem ireflLink_ishiftLink (τ : Fin 4) (c : ℤ) (l : ILink) :
    ireflLink τ c (ishiftLink τ l) = ireflLink τ (c - 1) l := by
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp only [ireflLink, ishiftLink, if_pos h, Prod.mk.injEq, true_and]
    rw [ireflSite_ishift]
  · simp only [ireflLink, ishiftLink, if_neg h, Prod.mk.injEq, true_and]
    rw [ireflSite_ishift]

#print axioms ireflLink_ishiftLink

/-- `iunshiftLink τ (ireflLink τ c l) = ireflLink τ (c - 1) l`: applying the backward shift after the
reflection also lowers the constant by one. The proof splits on `l.1 = τ` and closes both branches
with `iunshift_ireflSite`.

Scope: the conclusion coincides with `ireflLink_ishiftLink`'s, but the shift is on the other side of
the reflection — both compositions lower the constant.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the amount the reflection
constant moves. -/
theorem iunshiftLink_ireflLink (τ : Fin 4) (c : ℤ) (l : ILink) :
    iunshiftLink τ (ireflLink τ c l) = ireflLink τ (c - 1) l := by
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp only [ireflLink, iunshiftLink, if_pos h, Prod.mk.injEq, true_and]
    show iunshift τ (ireflSite τ (c - 1) x) = ireflSite τ (c - 1 - 1) x
    show Function.update (ireflSite τ (c - 1) x) τ ((ireflSite τ (c - 1) x) τ - 1) = _
    rw [iunshift_ireflSite]
  · simp only [ireflLink, iunshiftLink, if_neg h, Prod.mk.injEq, true_and]
    show iunshift τ (ireflSite τ c x) = ireflSite τ (c - 1) x
    show Function.update (ireflSite τ c x) τ ((ireflSite τ c x) τ - 1) = _
    rw [iunshift_ireflSite]

#print axioms iunshiftLink_ireflLink

/-! ## 4. Configurations, where `ireflConf` inverts on `τ`-links -/

section Conf

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]

/-- The backward shift on configurations: `fun l => U (iunshiftLink τ l)`, precomposition with the
backward link shift. Unlike `ireflConf` it applies no inversion.

Scope: stated for `G` a topological group with continuous inversion; only the group's carrier is
used here.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. -/
def iunshiftConf (τ : Fin 4) (U : IConf G) : IConf G := fun l => U (iunshiftLink τ l)

omit [ContinuousInv G] in
theorem ishiftConf_iunshiftConf (τ : Fin 4) (U : IConf G) :
    ishiftConf τ (iunshiftConf τ U) = U := by
  funext l
  show U (iunshiftLink τ (ishiftLink τ l)) = U l
  congr 1
  obtain ⟨μ, x⟩ := l
  simp only [iunshiftLink, ishiftLink, Prod.mk.injEq, true_and]
  funext j
  by_cases h : j = τ
  · subst h; simp [iunshift, ishift, Function.update_self]
  · simp [iunshift, ishift, Function.update_of_ne h]

#print axioms ishiftConf_iunshiftConf

/-- `ireflSite τ a (ireflSite τ b x) = Function.update x τ (a - b + x τ)`: reflecting about `b` and
then about `a` translates the `τ` coordinate by `a - b` and leaves every other coordinate alone.
Checked coordinatewise.

Scope: the translation distance is the difference of the two constants, with no constraint on either.
`ireflSite_comp_succ` is the case `a = b + 1`.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. No other numeral appears; `a` and `b`
are the caller's constants. -/
theorem ireflSite_comp (τ : Fin 4) (a b : ℤ) (x : ISite) :
    ireflSite τ a (ireflSite τ b x) = Function.update x τ (a - b + x τ) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, Function.update_self]
    abel
  · simp [ireflSite, Function.update_of_ne hj]

#print axioms ireflSite_comp

/-- `ireflSite τ (c + 1) (ireflSite τ c x) = ishift τ x`: reflecting about `c` and then about `c + 1`
is the forward shift. At the axis coordinate `(c + 1) - (c - x τ) = x τ + 1`; elsewhere neither map
acts.

`LatticeReflection.ireflSite_ireflSite_pred` is the same fact with the constants written `c` and
`c - 1`; this spelling is the one `ireflLink_comp_succ` uses at both of its cases.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants, which is what makes the composite a single step. -/
theorem ireflSite_comp_succ (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ (c + 1) (ireflSite τ c x) = ishift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, ishift, Function.update_self]
    ring
  · simp [ireflSite, ishift, Function.update_of_ne hj]

#print axioms ireflSite_comp_succ

/-- `ireflLink τ (a + 1) (ireflLink τ a l) = ishiftLink τ l`, the link form of `ireflSite_comp_succ`.
The proof splits on `l.1 = τ`, using `ireflLink_fst` to see that the direction is unchanged by the
inner reflection. On a `τ`-link both reflections act about their constant minus one, and that common
offset cancels in the difference, so both branches close on `ireflSite_comp_succ` — at `a - 1` in one
case and at `a` in the other.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. The `- 1` offset `ireflLink` applies to `τ`-links lives in its definition, not
in this statement. -/
theorem ireflLink_comp_succ (τ : Fin 4) (a : ℤ) (l : ILink) :
    ireflLink τ (a + 1) (ireflLink τ a l) = ishiftLink τ l := by
  refine Prod.ext rfl ?_
  by_cases h : l.1 = τ
  · show (if (ireflLink τ a l).1 = τ then ireflSite τ (a + 1 - 1) (ireflLink τ a l).2
            else ireflSite τ (a + 1) (ireflLink τ a l).2) = _
    rw [ireflLink_fst, if_pos h]
    show ireflSite τ (a + 1 - 1)
        (if l.1 = τ then ireflSite τ (a - 1) l.2 else ireflSite τ a l.2) = _
    rw [if_pos h, show a + 1 - 1 = (a - 1) + 1 from by ring]
    exact ireflSite_comp_succ τ (a - 1) l.2
  · show (if (ireflLink τ a l).1 = τ then ireflSite τ (a + 1 - 1) (ireflLink τ a l).2
            else ireflSite τ (a + 1) (ireflLink τ a l).2) = _
    rw [ireflLink_fst, if_neg h]
    show ireflSite τ (a + 1)
        (if l.1 = τ then ireflSite τ (a - 1) l.2 else ireflSite τ a l.2) = _
    rw [if_neg h]
    exact ireflSite_comp_succ τ a l.2

#print axioms ireflLink_comp_succ

/-- `ireflConf τ a (ireflConf τ (a + 1) U) = ishiftConf τ U`: on configurations, the composite of the
reflections about `a + 1` and `a` is the forward shift. It is the `ℤ⁴` counterpart of
`WilsonTransfer.shiftConf_eq_reflConf_comp`.

The proof splits on `l.1 = τ`. The inversion `ireflConf` applies to `τ`-links occurs twice there and
not at all elsewhere, and `ireflLink_fst` makes the inner and outer splits the same, so `inv_inv`
closes it; `ireflLink_comp_succ` supplies the link identity in both branches.

Scope: the order is load-bearing. The smaller constant is the outer application here, and the
reversed composite `ireflConf τ (a + 1) (ireflConf τ a U)` is the backward shift, which no statement
in this file covers. The separation is one; a composite at separation `k` translates by `k`, but
`WilsonTransferReduction.shiftCompat_of_nu_T` takes `T := ishiftObsL τ`, a single step, and
invariance under a `k`-step translation does not give invariance under one step. `Nat.iterate` does
not appear — `ishiftConf τ U` is written directly.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants, which is what makes the composite a single step. -/
theorem ireflConf_comp_eq_shift (τ : Fin 4) (a : ℤ) (U : IConf G) :
    ireflConf τ a (ireflConf τ (a + 1) U) = ishiftConf τ U := by
  funext l
  show (if l.1 = τ then (ireflConf τ (a + 1) U (ireflLink τ a l))⁻¹
          else ireflConf τ (a + 1) U (ireflLink τ a l))
      = U (ishiftLink τ l)
  by_cases h : l.1 = τ
  · rw [if_pos h]
    show (if (ireflLink τ a l).1 = τ then (U (ireflLink τ (a + 1) (ireflLink τ a l)))⁻¹
            else U (ireflLink τ (a + 1) (ireflLink τ a l)))⁻¹ = _
    rw [ireflLink_fst, if_pos h, inv_inv, ireflLink_comp_succ]
  · rw [if_neg h]
    show (if (ireflLink τ a l).1 = τ then (U (ireflLink τ (a + 1) (ireflLink τ a l)))⁻¹
            else U (ireflLink τ (a + 1) (ireflLink τ a l))) = _
    rw [ireflLink_fst, if_neg h, ireflLink_comp_succ]

#print axioms ireflConf_comp_eq_shift

/-- `ireflConf τ (a + 1) U = ireflConf τ a (ishiftConf τ U)`: the reflection at the next constant is
the one at `a` applied after a shift. Obtained from `ireflConf_comp_eq_shift` by applying
`ireflConf τ a` to both sides and cancelling with `LatticeReflection.ireflConf_involutive`.

Scope: an equality of configurations; `reflection_invariant_succ_iff_nu_T` is what uses it on states.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. -/
theorem ireflConf_succ_eq_ireflConf_shift (τ : Fin 4) (a : ℤ) (U : IConf G) :
    ireflConf τ (a + 1) U = ireflConf τ a (ishiftConf τ U) := by
  rw [← ireflConf_comp_eq_shift τ a U, ireflConf_involutive τ a]

#print axioms ireflConf_succ_eq_ireflConf_shift

/-- `ishiftConf τ (ireflConf τ c U) = ireflConf τ c (iunshiftConf τ U)`: the reflection conjugates
the forward shift into the backward one. It is the `ℤ⁴` form of
`WilsonTransfer.shiftConf_reflConf_shiftConf`.

The proof splits on `l.1 = τ` and rewrites with `ireflLink_ishiftLink` and `iunshiftLink_ireflLink`,
which lower the constant by one on either side. Both `ishiftLink` and `iunshiftLink` preserve a
link's direction, so the split is the same on both sides and the inversions on `τ`-links match case
by case.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. No other numeral appears in the
statement. -/
theorem ishiftConf_ireflConf (τ : Fin 4) (c : ℤ) (U : IConf G) :
    ishiftConf τ (ireflConf τ c U) = ireflConf τ c (iunshiftConf τ U) := by
  funext l
  by_cases h : l.1 = τ
  · simp only [ishiftConf, ireflConf, iunshiftConf, ishiftLink_fst', if_pos h,
      ireflLink_ishiftLink, iunshiftLink_ireflLink]
  · simp only [ishiftConf, ireflConf, iunshiftConf, ishiftLink_fst', if_neg h,
      ireflLink_ishiftLink, iunshiftLink_ireflLink]

#print axioms ishiftConf_ireflConf

end Conf

/-! ## 5. The same identities on observables, in `ShiftCompat`'s field shapes -/

section Obs

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

theorem continuous_iunshiftConf (τ : Fin 4) :
    Continuous (iunshiftConf (G := G) τ) :=
  continuous_pi fun l => continuous_apply (iunshiftLink τ l)

/-- The backward shift on observables, as an `ℝ`-linear endomorphism of `C(IConf G, ℝ)`:
`F ↦ F.comp ⟨iunshiftConf τ, _⟩`. Additivity and homogeneity are `rfl`, since precomposition is
pointwise. It is the map `SchwarzIteration.ShiftCompat` calls `S`.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. -/
def iunshiftObs (τ : Fin 4) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨iunshiftConf τ, continuous_iunshiftConf τ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The forward shift on observables, as an `ℝ`-linear endomorphism of `C(IConf G, ℝ)`:
`F ↦ F.comp ⟨ishiftConf τ, _⟩`, matching `HalfSpaceAlgebra.ishiftObsCM`. It is the map
`SchwarzIteration.ShiftCompat` calls `T`.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. -/
def ishiftObsL (τ : Fin 4) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨ishiftConf τ, continuous_ishiftConf τ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ishiftObsL τ (f * g) = ishiftObsL τ f * ishiftObsL τ g`, by `rfl`: precomposition is
multiplicative, since multiplication of continuous functions is pointwise. This is the `T_mul` field
of `SchwarzIteration.ShiftCompat`.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. -/
theorem ishiftObsL_mul (τ : Fin 4) (f g : C(IConf G, ℝ)) :
    ishiftObsL τ (f * g) = ishiftObsL τ f * ishiftObsL τ g := rfl

/-- `ishiftObsL τ (iunshiftObs τ f) = f`: the forward shift undoes the backward one on observables.
Evaluating at a configuration reduces it to `ishiftLink_iunshiftLink` on each link. This is the
`T_S` field of `SchwarzIteration.ShiftCompat`.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. -/
theorem ishiftObsL_iunshiftObs (τ : Fin 4) (f : C(IConf G, ℝ)) :
    ishiftObsL τ (iunshiftObs τ f) = f := by
  ext U
  show f (iunshiftConf τ (ishiftConf τ U)) = f U
  congr 1
  funext l
  show U (ishiftLink τ (iunshiftLink τ l)) = U l
  rw [ishiftLink_iunshiftLink]

#print axioms ishiftObsL_iunshiftObs

/-- `ireflObs τ c (ishiftObsL τ f) = iunshiftObs τ (ireflObs τ c f)`: the reflection conjugates the
forward shift on observables into the backward one. Evaluating at a configuration reduces it to
`ishiftConf_ireflConf`.

This is the `theta_T` field of `SchwarzIteration.ShiftCompat` with `R.θ = ireflObs τ c`,
`T = ishiftObsL τ` and `S = iunshiftObs τ`, and it is the identity that makes a reflection form
symmetric for the transfer operator.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. No other numeral appears in the
statement. -/
theorem ireflObs_ishiftObs (τ : Fin 4) (c : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ c (ishiftObsL τ f) = iunshiftObs τ (ireflObs τ c f) := by
  ext U
  show f (ishiftConf τ (ireflConf τ c U)) = f (ireflConf τ c (iunshiftConf τ U))
  rw [ishiftConf_ireflConf]

#print axioms ireflObs_ishiftObs


/-- `ireflObs τ (a + 1) (ireflObs τ a f) = ishiftObsL τ f`: the observable form of
`ireflConf_comp_eq_shift`. Evaluating at `U` turns the left side into
`f (ireflConf τ a (ireflConf τ (a + 1) U))`, which that theorem rewrites.

Scope: the two constants appear in the opposite order to the configuration form, because `ireflObs`
is precomposition and precomposition reverses composition. For the same forward shift, the larger
constant is outermost on observables and the smaller one outermost on configurations.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. -/
theorem ireflObs_comp_eq_shiftObs (τ : Fin 4) (a : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ (a + 1) (ireflObs τ a f) = ishiftObsL τ f := by
  ext U
  show f (ireflConf τ a (ireflConf τ (a + 1) U)) = f (ishiftConf τ U)
  rw [ireflConf_comp_eq_shift]

#print axioms ireflObs_comp_eq_shiftObs

/-- If a state `ν` is reflection-invariant at `a` and at `a + 1`, then it is translation-invariant:
`ν (ishiftObsL τ f) = ν f` at every observable `f`. The proof rewrites the shift as the composite of
the two reflections by `ireflObs_comp_eq_shiftObs` and applies the two invariances in turn.

This is the `hnu` hypothesis of `WilsonTransferReduction.transferData_of_state_facts`.

Scope: both invariances are hypotheses; nothing here exhibits a state satisfying either. One of the
two constants is always odd, hence the link reflection, but `IsReflectionInvariant` is an equality,
so no sign condition on the coupling enters. `reflection_invariant_succ_iff_nu_T` shows that, given
invariance at `a`, the second invariance and the conclusion are equivalent.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. -/
theorem nu_T_of_reflection_invariant (τ : Fin 4) (a : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (h0 : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ a) ν)
    (h1 : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (a + 1)) ν)
    (f : C(IConf G, ℝ)) :
    ν (ishiftObsL τ f) = ν f := by
  calc ν (ishiftObsL τ f)
      = ν (ireflObs τ (a + 1) (ireflObs τ a f)) := by rw [ireflObs_comp_eq_shiftObs]
    _ = ν (ireflObs τ a f) := h1 _
    _ = ν f := h0 f

#print axioms nu_T_of_reflection_invariant

/-- `ireflObs τ (a + 1) f = ishiftObsL τ (ireflObs τ a f)`, the observable form of
`ireflConf_succ_eq_ireflConf_shift`. Precomposition reverses the order, so the shift is outermost on
observables and innermost on configurations.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. -/
theorem ireflObs_succ_eq_shiftObs_ireflObs (τ : Fin 4) (a : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ (a + 1) f = ishiftObsL τ (ireflObs τ a f) := by
  ext U
  show f (ireflConf τ (a + 1) U) = f (ireflConf τ a (ishiftConf τ U))
  rw [ireflConf_succ_eq_ireflConf_shift]

#print axioms ireflObs_succ_eq_shiftObs_ireflObs

/-- `iunshiftObs τ (ishiftObsL τ f) = f`, the other composition order from
`ishiftObsL_iunshiftObs`. Evaluating at a configuration reduces it to `ishiftConf_iunshiftConf`. Both
directions hold because `ishiftLink` is a bijection of the link set.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`. No other numeral appears in the
statement. -/
theorem iunshiftObs_ishiftObsL (τ : Fin 4) (f : C(IConf G, ℝ)) :
    iunshiftObs τ (ishiftObsL τ f) = f := by
  ext U
  show f (ishiftConf τ (iunshiftConf τ U)) = f U
  rw [ishiftConf_iunshiftConf]

#print axioms iunshiftObs_ishiftObsL

/-- `ireflObs τ (c - 1) f = iunshiftObs τ (ireflObs τ c f)`: the reflection at the previous constant
is this one composed with the backward shift. It is `ireflObs_succ_eq_shiftObs_ireflObs` at `c - 1`,
cancelled with `iunshiftObs_ishiftObsL`.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. -/
theorem ireflObs_pred_eq_unshift (τ : Fin 4) (c : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ (c - 1) f = iunshiftObs τ (ireflObs τ c f) := by
  have h : ireflObs τ c f = ishiftObsL τ (ireflObs τ (c - 1) f) := by
    have h0 := ireflObs_succ_eq_shiftObs_ireflObs τ (c - 1) f
    rwa [sub_add_cancel] at h0
  rw [h, iunshiftObs_ishiftObsL]

#print axioms ireflObs_pred_eq_unshift

/-- Given reflection invariance of `ν` at `a`, reflection invariance at `a + 1` is EQUIVALENT to
translation invariance `∀ f, ν (ishiftObsL τ f) = ν f`. The forward direction is
`nu_T_of_reflection_invariant`; the reverse rewrites by `ireflObs_succ_eq_shiftObs_ireflObs`, applies
the translation invariance, and finishes with the invariance at `a`.

So the two formulations carry the same content: supplying either gives the other, and neither is
supplied here.

Scope: `ReflectionHalfSpace.eq_empty_of_stable_two_mirrors` shows a finite box stable under the
reflections at both `a` and `a + 1` is empty, since the two compose to one link shift by
`ireflLink_comp_succ` and a `Finset` cannot contain an orbit of it. That rules out one finite-volume
box family serving both invariances; it says nothing about routes to the second invariance that are
not box statements.

DERIVED: `4` is the spacetime dimension, the axis type of `τ`; `1` is the separation of the two
reflection constants. -/
theorem reflection_invariant_succ_iff_nu_T (τ : Fin 4) (a : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (h0 : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ a) ν) :
    MassGap.InfiniteReflection.IsReflectionInvariant
        (MassGap.LatticeReflection.latticeReflection τ (a + 1)) ν
      ↔ ∀ f : C(IConf G, ℝ), ν (ishiftObsL τ f) = ν f := by
  constructor
  · intro h1 f
    exact nu_T_of_reflection_invariant τ a ν h0 h1 f
  · intro hnu f
    show ν (ireflObs τ (a + 1) f) = ν f
    rw [ireflObs_succ_eq_shiftObs_ireflObs, hnu (ireflObs τ a f)]
    exact h0 f

#print axioms reflection_invariant_succ_iff_nu_T

end Obs

end MassGap.ReflectionShift
