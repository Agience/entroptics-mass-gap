import Mathlib
import MassGap.InfiniteReflection
import MassGap.InfiniteLattice

/-!
# MassGap.LatticeReflection — the reflection of `ℤ⁴`, as an `InfiniteReflection.Reflection`

`InfiniteReflection.Reflection (IConf G)` is a linear map on `C(IConf G, ℝ)` that is multiplicative,
fixes the constant `1`, and is involutive. This module constructs one from the geometric reflection
of the infinite lattice `InfiniteLattice.ISite = Fin 4 → ℤ`.

## The convention

Sites reflect by `x_τ ↦ c − x_τ` in one coordinate (`ireflSite`), where `c` is the reflection
constant: the fixed set of `x ↦ c − x` is `2x = c`, so the mirror plane sits at `c/2`.

Links reflect by `ireflLink`, which sends a `τ`-link's base to `ireflSite τ (c − 1)` and every other
link's base to `ireflSite τ c`. The offset of one is because a `τ`-link spans `[x_τ, x_τ + 1]`, so
its mirror spans `[c − 1 − x_τ, c − x_τ]` and is based at the lower end.

Configurations reflect by `ireflConf`, which additionally inverts the group element on every
`τ`-link — the dagger, because such a link is traversed in the reverse direction by the mirrored
loop. That inversion is why this module requires `[Group G]` and `[ContinuousInv G]`.

Plaquettes reflect by `ireflPlaq`, which transposes the plane when the plane contains `τ`, because
`InfiniteLattice.ibd` writes a reversed loop by swapping the two spanning directions.

## What is proved

* Involutivity at each level: `ireflSite_involutive`, `ireflLink_involutive`,
  `ireflPlaq_involutive`, `ireflConf_involutive`. `ireflPlaqPerm` is the plaquette reflection as an
  `Equiv.Perm`.
* The commutation identities with `ishift`: `ireflSite_ishift_of_ne`, `ireflSite_ishift_axis`,
  `ishift_ireflSite_axis`, `ireflSite_ireflSite_pred`.
* `ihol_ireflConf` — the holonomy of a plaquette in the reflected configuration is conjugate to the
  holonomy of the image plaquette, not equal to it. The mirrored boundary word is a cyclic rotation
  of the image word, and a rotated ordered product is a conjugated one; the conjugator is `1` exactly
  on the plaquettes transverse to the axis.
* `ireflObs`, `latticeReflection` — precomposition by `ireflConf` as a linear map, and the
  `Reflection` structure built from it, all four fields discharged.
* `ireflLink_moves_a_link` and `ireflObs_eq_id_of_subsingleton` — the link map is not the identity at
  `c = 1`, while `ireflObs` is the identity whenever `G` is a subsingleton, so the first does not by
  itself make the reflection nontrivial.

## Scope

Stated over `ℤ`, with no periodicity: the reflection needs only subtraction. No positivity statement
is made or transported — nothing here says any state is reflection positive for this reflection, and
`latticeReflection τ c` is defined at every `c : ℤ`, of either parity.

The output is a `Reflection`, from which `InfiniteReflection.stateReflForm` produces a
`Transfer.ReflForm` given a reflection-positive, reflection-invariant state and a submodule. A
`Transfer.TransferData` is a different structure with further fields and is not constructed here.
-/

namespace MassGap.LatticeReflection

open MassGap.InfiniteLattice MassGap.InfiniteReflection

/-! ## 1. Sites -/

/-- The site map `Function.update x τ (c - x τ)`: the `τ` coordinate becomes `c − x τ` and every
other coordinate is unchanged.

`c` is the reflection constant, not a position. The fixed set of `x ↦ c − x` is where `2x = c`, so
the mirror plane sits at `c/2` and `c` sweeps the family of reflections in direction `τ`; at odd `c`
the plane falls between two integer sites. `Reflect.reflSite` with `Fin n` replaced by `ℤ`.

DERIVED: `4` is the spacetime dimension, the constant `InfiniteLattice.ISite` and `ILink` are built
on — the range of the direction index, not an extent. `c` and `τ` are the caller's and the
subtraction is `ℤ`'s. -/
def ireflSite (τ : Fin 4) (c : ℤ) (x : ISite) : ISite := Function.update x τ (c - x τ)

@[simp] theorem ireflSite_axis (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c x τ = c - x τ := by simp [ireflSite]

/-- `ireflSite τ c` is involutive: `c − (c − a) = a` on the `τ` coordinate and the identity on the
others. Case split on whether the coordinate index is `τ`.

DERIVED: `4` is the dimension, as in `ireflSite`; the statement introduces no numeral of its own. -/
theorem ireflSite_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflSite τ c) := by
  intro x
  funext j
  by_cases h : j = τ
  · subst h
    simp [ireflSite, sub_sub_cancel]
  · simp [ireflSite, Function.update_of_ne h]

#print axioms ireflSite_involutive

/-! ## 2. Links, where the base shifts by one -/

/-- The link map: the direction is unchanged, and the base site reflects about `c - 1` for a
`τ`-link and about `c` for every other link.

A link in direction `τ` spans `[x_τ, x_τ + 1]`, so its mirror spans `[c − 1 − x_τ, c − x_τ]` and is
based at `c − 1 − x_τ`; a link in any other direction lies in a plane the mirror does not shorten and
is based at the mirror of its own base.

DERIVED: `1` is the length of a link in lattice steps — the offset between its two ends, exactly
`Reflect.reflLink`'s and for the same reason. `4` is the dimension, as in `ireflSite`. The `1` and
`2` in `l.1` and `l.2` are the projections of `ILink` onto its direction and its base site. -/
def ireflLink (τ : Fin 4) (c : ℤ) (l : ILink) : ILink :=
  (l.1, if l.1 = τ then ireflSite τ (c - 1) l.2 else ireflSite τ c l.2)

/-- `(ireflLink τ c l).1 = l.1`, by `rfl`: the reflection changes a link's base, never its direction.
Used wherever the dagger's case split has to be matched on both sides of an equation.

DERIVED: `4` is the dimension; the `1` in `l.1` is the projection onto the direction. -/
@[simp] theorem ireflLink_fst (τ : Fin 4) (c : ℤ) (l : ILink) :
    (ireflLink τ c l).1 = l.1 := rfl

/-- For a link in direction `τ`, `ireflLink τ c l = (l.1, ireflSite τ (c - 1) l.2)`: the axis branch
of `ireflLink`, written out. `if_pos` on the hypothesis `h`.

`ireflSite_axis` gives only the `τ` coordinate of the reflected site; this gives the whole site, so a
caller need not reopen the case split.

DERIVED: `1` is the length of a link in lattice steps, exactly `ireflLink`'s own; `4` is the
dimension; the `1` and `2` in `l.1`, `l.2` are the projections of `ILink`. -/
theorem ireflLink_eq_axis (τ : Fin 4) (c : ℤ) {l : ILink} (h : l.1 = τ) :
    ireflLink τ c l = (l.1, ireflSite τ (c - 1) l.2) := by
  simp only [ireflLink, if_pos h]

#print axioms ireflLink_eq_axis

/-- For a link whose direction is not `τ`, `ireflLink τ c l = (l.1, ireflSite τ c l.2)`: the
transverse branch, reflecting about `c` itself. `if_neg` on the hypothesis `h`.

DERIVED: no numeral of its own — the offset `1` of the axis branch does not appear. `4` is the
dimension; the `1` and `2` in `l.1`, `l.2` are the projections of `ILink`. -/
theorem ireflLink_eq_transverse (τ : Fin 4) (c : ℤ) {l : ILink} (h : l.1 ≠ τ) :
    ireflLink τ c l = (l.1, ireflSite τ c l.2) := by
  simp only [ireflLink, if_neg h]

#print axioms ireflLink_eq_transverse

/-- `ireflLink τ c` is involutive, hence a bijection of the link set. Case split on the direction,
with `ireflSite_involutive` at `c - 1` on the axis branch and at `c` on the transverse one.

Both branches reflect twice about the same constant, which is why no shift survives; composing two
mirrors one apart instead gives `ireflSite_ireflSite_pred`.

DERIVED: `1` is `ireflLink`'s link length, reached through the axis branch; `4` is the dimension. -/
theorem ireflLink_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflLink τ c) := by
  intro l
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp [ireflLink, h, ireflSite_involutive τ (c - 1) x]
  · simp [ireflLink, h, ireflSite_involutive τ c x]

#print axioms ireflLink_involutive

/-! ## 2′. Plaquettes, where the mirror reverses the loop -/

/-- For `ν ≠ τ`, `ireflSite τ c (ishift ν x) = ishift ν (ireflSite τ c x)`: a reflection commutes
with a shift transverse to its axis, because the two `Function.update`s touch different coordinates.

DERIVED: `4` is the dimension; the statement introduces no numeral, the shift's own step being inside
`ishift`. -/
theorem ireflSite_ishift_of_ne {τ ν : Fin 4} (h : ν ≠ τ) (c : ℤ) (x : ISite) :
    ireflSite τ c (ishift ν x) = ishift ν (ireflSite τ c x) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp [ireflSite, ishift, Function.update_of_ne (Ne.symm h)]
  · by_cases hν : j = ν
    · subst hν
      simp [ireflSite, ishift, Function.update_of_ne hj]
    · simp [ireflSite, ishift, Function.update_of_ne hj, Function.update_of_ne hν]

#print axioms ireflSite_ishift_of_ne

/-- `ireflSite τ c (ishift τ x) = ireflSite τ (c - 1) x`: a reflection absorbs a shift along its own
axis by moving the mirror one step. On the `τ` coordinate this is `c − (x + 1) = (c − 1) − x`, closed
by `abel`.

On `ℤ` this is plain subtraction; the torus counterpart `Reflect.reflSite_shift_axis` has to wrap.

DERIVED: `1` is the lattice step of `ishift`, transferred to the reflection constant; the two
occurrences are the same step. `4` is the dimension. -/
theorem ireflSite_ishift_axis (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (ishift τ x) = ireflSite τ (c - 1) x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, ishift, Function.update_self]
    abel
  · simp [ireflSite, ishift, Function.update_of_ne hj]

#print axioms ireflSite_ishift_axis

/-- `ishift τ (ireflSite τ (c - 1) x) = ireflSite τ c x`: the same arithmetic as
`ireflSite_ishift_axis`, with the shift on the outside. This is the orientation
`ihol_ireflConf` rewrites in.

DERIVED: `1` is the lattice step, appearing as the mirror offset; `4` is the dimension. -/
theorem ishift_ireflSite_axis (τ : Fin 4) (c : ℤ) (x : ISite) :
    ishift τ (ireflSite τ (c - 1) x) = ireflSite τ c x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, ishift, Function.update_self]
    abel
  · simp [ireflSite, ishift, Function.update_of_ne hj]

#print axioms ishift_ireflSite_axis

/-- `ireflSite τ c (ireflSite τ c x) = x`: reflecting twice about the same mirror is the identity.
`ireflSite_involutive` applied, in a form `rw` can use.

DERIVED: `4` is the dimension; no other numeral. -/
theorem ireflSite_ireflSite (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (ireflSite τ c x) = x := ireflSite_involutive τ c x

#print axioms ireflSite_ireflSite

/-- `ireflSite τ c (ireflSite τ (c - 1) x) = ishift τ x`: reflecting twice about mirrors one apart is
a shift by one along the axis. On the `τ` coordinate, `c − ((c − 1) − x) = x + 1`, closed by `abel`.

The arithmetic behind the `c` / `c − 1` distinction: a `τ`-link reflects about `c − 1` because it
occupies a segment rather than a point, and composing the two mirrors turns that offset into a
lattice step.

DERIVED: the two `1`s are the mirror offset and the lattice step, which this identity shows are the
same one; `4` is the dimension. -/
theorem ireflSite_ireflSite_pred (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (ireflSite τ (c - 1) x) = ishift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, ishift, Function.update_self]
    abel
  · simp [ireflSite, ishift, Function.update_of_ne hj]

#print axioms ireflSite_ireflSite_pred

/-- The plaquette map. A plaquette whose plane misses the axis keeps its ordered plane and reflects
its corner about `c`. One whose plane contains the axis has its loop traversed the other way round by
the mirror, and `InfiniteLattice.ibd` writes a reversed loop by transposing the two spanning
directions, so the image carries the transposed pair and a corner reflected about `c - 1`.

The three branches are: first direction is `τ`, second direction is `τ`, neither. A degenerate
plaquette with both directions equal to `τ` falls in the first.

DERIVED: `1` is the link-length offset of `ireflLink`, for the same reason — a plaquette touching
the axis spans a segment in it. `4` is the dimension. The `1`s and `2`s in `q.1.1`, `q.1.2`, `q.2`
are projections of `IPlaq` onto the two plane directions and the corner site. -/
def ireflPlaq (τ : Fin 4) (c : ℤ) (q : IPlaq) : IPlaq :=
  if q.1.1 = τ then ((q.1.2, τ), ireflSite τ (c - 1) q.2)
  else if q.1.2 = τ then ((τ, q.1.1), ireflSite τ (c - 1) q.2)
  else ((q.1.1, q.1.2), ireflSite τ c q.2)

/-- `ireflPlaq τ c` is involutive: the transposition of the plane undoes itself and
`ireflSite_involutive` returns the corner. Four-way case split on whether each of the two plane
directions is `τ`.

DERIVED: `1` is `ireflPlaq`'s own offset, reached through its axis branches; `4` is the
dimension. -/
theorem ireflPlaq_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflPlaq τ c) := by
  intro q
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  by_cases hμ : μ = τ
  · subst hμ
    by_cases hν : ν = μ
    · subst hν
      simp [ireflPlaq, ireflSite_involutive ν (c - 1) x]
    · simp [ireflPlaq, hν, ireflSite_involutive μ (c - 1) x]
  · by_cases hν : ν = τ
    · subst hν
      simp [ireflPlaq, hμ, ireflSite_involutive ν (c - 1) x]
    · simp [ireflPlaq, hμ, hν, ireflSite_involutive τ c x]

#print axioms ireflPlaq_involutive

/-- `ireflPlaq τ c` packaged as an `Equiv.Perm IPlaq`, via `Function.Involutive.toPerm`. This is what
carries a sum over plaquettes to a sum over their images.

DERIVED: `4` is the dimension; every other constant is `ireflPlaq`'s. -/
def ireflPlaqPerm (τ : Fin 4) (c : ℤ) : Equiv.Perm IPlaq :=
  (ireflPlaq_involutive τ c).toPerm _

@[simp] theorem ireflPlaqPerm_apply (τ : Fin 4) (c : ℤ) (q : IPlaq) :
    ireflPlaqPerm τ c q = ireflPlaq τ c q := rfl

#print axioms ireflPlaqPerm

/-! ## 3. Configurations, and the dagger -/

section Conf

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]

/-- The configuration map: `ireflLink` on the argument, with the value inverted on `τ`-links and left
alone on the others. `Reflect.reflConf` over `ℤ`.

The inversion is the dagger. A `τ`-link is traversed backwards by the mirrored loop, so its group
element must be inverted; without it `ihol_ireflConf`'s conjugacy fails and the Wilson action is not
invariant under the map. The inversion is why this section requires `[Group G]`.

DERIVED: `4` is the dimension. The `1` in `l.1` is the projection of `ILink` onto its direction, and
`⁻¹` is the group inverse; neither is a number. -/
def ireflConf (τ : Fin 4) (c : ℤ) (U : IConf G) : IConf G :=
  fun l => if l.1 = τ then (U (ireflLink τ c l))⁻¹ else U (ireflLink τ c l)

omit [ContinuousInv G] in
/-- `ireflConf τ c` is involutive. The double inverse cancels on `τ`-links, `ireflLink_involutive`
returns the link, and `ireflLink_fst` is what lets the inner and outer case splits line up.

`[ContinuousInv G]` is omitted: the identity is algebraic.

DERIVED: `4` is the dimension; no numeral of this declaration's own. -/
theorem ireflConf_involutive (τ : Fin 4) (c : ℤ) :
    Function.Involutive (ireflConf (G := G) τ c) := by
  intro U
  funext l
  by_cases h : l.1 = τ
  · simp only [ireflConf, ireflLink_fst, if_pos h, inv_inv, ireflLink_involutive τ c l]
  · simp only [ireflConf, ireflLink_fst, if_neg h, ireflLink_involutive τ c l]

#print axioms ireflConf_involutive

/-- On a `τ`-link that the link map leaves fixed, the configuration map inverts the value:
`ireflConf τ c U l = (U l)⁻¹`. `if_pos` on `hl`, then rewriting by `hfix`.

Which links are fixed depends on the parity of `c`: at even `c` the `τ`-links are all moved, at odd
`c` those straddling the mirror are fixed. This statement is about whichever links `hfix` names and
imposes no parity condition.

The `ℤ⁴` counterpart of `ActionSplit.reflConf_inverts_fixed_axis_link`.

DERIVED: `4` is the dimension. The `1` in `l.1` is the projection onto the direction and `⁻¹` the
group inverse; the statement carries no numeral. -/
theorem ireflConf_inverts_fixed_axis_link (τ : Fin 4) (c : ℤ) {l : ILink}
    (hl : l.1 = τ) (hfix : ireflLink τ c l = l) (U : IConf G) :
    ireflConf τ c U l = (U l)⁻¹ := by
  show (if l.1 = τ then (U (ireflLink τ c l))⁻¹ else U (ireflLink τ c l)) = (U l)⁻¹
  rw [if_pos hl, hfix]

#print axioms ireflConf_inverts_fixed_axis_link

/-- On a fixed link whose direction is not `τ`, the configuration map leaves the value alone:
`ireflConf τ c U l = U l`. `if_neg` on `hl`, then rewriting by `hfix`. The other half of
`ireflConf_inverts_fixed_axis_link`'s case split.

DERIVED: `4` is the dimension. The `1` in `l.1` is the projection onto the direction; the statement
carries no numeral. -/
theorem ireflConf_fixes_fixed_transverse_link (τ : Fin 4) (c : ℤ) {l : ILink}
    (hl : l.1 ≠ τ) (hfix : ireflLink τ c l = l) (U : IConf G) :
    ireflConf τ c U l = U l := by
  show (if l.1 = τ then (U (ireflLink τ c l))⁻¹ else U (ireflLink τ c l)) = U l
  rw [if_neg hl, hfix]

#print axioms ireflConf_fixes_fixed_transverse_link

/-- `ireflConf τ c` is continuous. `continuous_pi` reduces to one coordinate at a time, and each
output coordinate is an input coordinate, inverted or not; `[ContinuousInv G]` covers the inverted
branch.

DERIVED: `4` is the dimension; no other numeral. -/
theorem continuous_ireflConf (τ : Fin 4) (c : ℤ) :
    Continuous (ireflConf (G := G) τ c) := by
  refine continuous_pi fun l => ?_
  by_cases h : l.1 = τ
  · simp only [ireflConf, if_pos h]
    exact (continuous_apply (ireflLink τ c l)).inv
  · simp only [ireflConf, if_neg h]
    exact continuous_apply (ireflLink τ c l)

#print axioms continuous_ireflConf

/-- `ireflConf τ c` as a bundled `C(IConf G, IConf G)`, paired with `continuous_ireflConf`.

DERIVED: `4` is the dimension; the definition introduces no numeral of its own. -/
def ireflConfCM (τ : Fin 4) (c : ℤ) : C(IConf G, IConf G) :=
  ⟨ireflConf τ c, continuous_ireflConf τ c⟩

end Conf

/-! ## 3′. The mirrored holonomy is conjugate, never equal -/

section Conjugacy

open MassGap.WilsonLattice

variable {G : Type} [Group G]

/-- For every plaquette `q` and configuration `U` there is a `g : G` with

    wilsonHol ibd q (ireflConf τ c U) = g * wilsonHol ibd (ireflPlaq τ c q) U * g⁻¹.

An existential, not an equality of holonomies: the mirrored boundary word is a cyclic rotation of the
image plaquette's word, and a rotated ordered product is a conjugated one. The proof supplies `g`
explicitly in each of the four branches — `1` for the degenerate plaquette and for a plaquette
transverse to the axis, and the inverse of one link variable in the two branches where the plane
contains the axis.

The `ℤ⁴` counterpart of `Reflect.hol_reflConf`. Conjugacy rather than equality is the reason a
reflection is not a `LatticeGauge.Symmetry`: `Symmetry.onLink` is a bare permutation of links and
cannot carry the dagger. `WilsonAction.wilsonDensity_conj` — the Wilson density is a class function —
is what makes the difference invisible to the action.

DERIVED: `1` appears twice, as `ireflLink`'s link length inside the reflected plaquette and as the
group identity taken for `g` in the two branches where the rotation is trivial. `4` is the
dimension, and `⁻¹` is the group inverse. -/
theorem ihol_ireflConf (τ : Fin 4) (c : ℤ) (q : IPlaq) (U : IConf G) :
    ∃ g : G, wilsonHol ibd q (ireflConf τ c U)
      = g * wilsonHol ibd (ireflPlaq τ c q) U * g⁻¹ := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  by_cases hμ : μ = τ
  · subst hμ
    by_cases hν : ν = μ
    · -- both directions are the axis: a degenerate plaquette, holonomy `1` on either side
      subst hν
      refine ⟨1, ?_⟩
      rw [wilsonHol_ibd, wilsonHol_ibd]
      simp only [ireflPlaq, ireflConf, ireflLink, if_true]
      group
    · refine ⟨(U (μ, ireflSite μ (c - 1) x))⁻¹, ?_⟩
      rw [wilsonHol_ibd, wilsonHol_ibd]
      simp only [ireflPlaq, ireflConf, ireflLink, hν, if_false, if_true,
        ireflSite_ishift_of_ne hν, ireflSite_ishift_axis, ← ishift_ireflSite_axis μ c x]
      group
  · by_cases hν : ν = τ
    · subst hν
      refine ⟨(U (ν, ireflSite ν (c - 1) x))⁻¹, ?_⟩
      rw [wilsonHol_ibd, wilsonHol_ibd]
      simp only [ireflPlaq, ireflConf, ireflLink, hμ, if_false, if_true,
        ireflSite_ishift_of_ne hμ, ireflSite_ishift_axis, ← ishift_ireflSite_axis ν c x]
      group
    · refine ⟨1, ?_⟩
      rw [wilsonHol_ibd, wilsonHol_ibd]
      simp only [ireflPlaq, ireflConf, ireflLink, hμ, hν, if_false,
        ireflSite_ishift_of_ne hμ, ireflSite_ishift_of_ne hν]
      group

#print axioms ihol_ireflConf

end Conjugacy

/-! ## 4. Observables, and the `Reflection` -/

section Obs

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- Precomposition by `ireflConfCM τ c`, as a linear map `C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ)`.
Additivity and homogeneity are `rfl`, since precomposition is evaluated pointwise.

DERIVED: `4` is the dimension; the definition introduces no numeral of its own. -/
def ireflObs (τ : Fin 4) (c : ℤ) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp (ireflConfCM τ c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompactSpace G] in
@[simp] theorem ireflObs_apply (τ : Fin 4) (c : ℤ) (F : C(IConf G, ℝ)) (U : IConf G) :
    ireflObs τ c F U = F (ireflConf τ c U) := rfl

/-- The `InfiniteReflection.Reflection (IConf G)` whose map is `ireflObs τ c`. All four fields:
multiplicativity and `θ 1 = 1` are `rfl`, because precomposition respects the pointwise product and
fixes constants whatever it precomposes with; involutivity is `ireflConf_involutive`, which is where
the dagger is used.

Defined at every `τ : Fin 4` and every `c : ℤ`, of either parity, and for any group `G` with the
stated instances.

DERIVED: `4` is the dimension; the `1` fixed by `θ_one` is the constant function, the unit of
`C(IConf G, ℝ)`. -/
def latticeReflection (τ : Fin 4) (c : ℤ) : Reflection (IConf G) where
  θ := ireflObs τ c
  θ_mul _ _ := rfl
  θ_one := rfl
  θ_involutive F := by
    ext U
    show F (ireflConf τ c (ireflConf τ c U)) = F U
    rw [ireflConf_involutive τ c U]

#print axioms latticeReflection

/-! ## 5. The link map moves a link; the observable map need not move an observable -/

/-- For `μ ≠ τ`, `ireflLink τ 1 (μ, origin) ≠ (μ, origin)`: at `c = 1` the link based at the origin
in a direction other than `τ` is moved. From `ireflSite_axis`, its `τ` coordinate would have to
satisfy `1 - 0 = 0`, which `omega` refutes.

A transverse direction is used so that the dagger does not enter: this is a statement about the link
map alone, which is the same with or without the inversion.

CHOSEN: `c = 1` and the base site `0` are a witness, the simplest pair with `c − x_τ ≠ x_τ`.
`ireflSite_axis` gives the same conclusion at every `c` with `2·x_τ ≠ c`; neither value carries
another role. `4` is the dimension. -/
theorem ireflLink_moves_a_link {τ μ : Fin 4} (hμ : μ ≠ τ) :
    ireflLink τ 1 (μ, fun _ => (0 : ℤ)) ≠ (μ, fun _ => (0 : ℤ)) := by
  intro h
  have hsnd : ireflSite τ 1 (fun _ => (0 : ℤ)) = (fun _ => (0 : ℤ)) := by
    have hcomp : (ireflLink τ 1 (μ, fun _ => (0 : ℤ))).2
        = ireflSite τ 1 (fun _ => (0 : ℤ)) := by
      show (if μ = τ then _ else _) = _
      rw [if_neg hμ]
    rw [← hcomp, h]
  have hcoord := congrFun hsnd τ
  rw [ireflSite_axis] at hcoord
  omega

#print axioms ireflLink_moves_a_link

omit [CompactSpace G] in
/-- If `G` is a subsingleton then `ireflObs τ c F = F` for every observable `F`, at every `τ` and `c`.
A subsingleton group makes `IConf G` a subsingleton, so `ireflConf τ c U` and `U` are equal and every
observable is constant.

So `ireflLink_moves_a_link` does not by itself distinguish `latticeReflection` from
`InfiniteReflection.trivialReflection`: links move while the induced map on observables is the
identity. Separating the two needs a hypothesis on `G`. The same holds at `N = 1`, where the gauge
group is trivial.

DERIVED: `4` is the dimension; no magnitude appears, and `[CompactSpace G]` is omitted as unused. -/
theorem ireflObs_eq_id_of_subsingleton [Subsingleton G] (τ : Fin 4) (c : ℤ)
    (F : C(IConf G, ℝ)) : ireflObs (G := G) τ c F = F := by
  ext U
  show F (ireflConf τ c U) = F U
  congr 1
  funext l
  exact Subsingleton.elim _ _

#print axioms ireflObs_eq_id_of_subsingleton

end Obs

end MassGap.LatticeReflection
