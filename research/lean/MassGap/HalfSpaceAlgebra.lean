import Mathlib
import MassGap.InfiniteShift
import MassGap.InfiniteReflection
import MassGap.LatticeReflection

/-!
# MassGap.HalfSpaceAlgebra — observables supported in a positive half-space of `ℤ⁴`

Constructs `halfSpaceAlg τ c`, the submodule of `C(IConf G, ℝ)` of observables local on some finite
set of links inside `posHalf τ c = {l | c ≤ l.2 τ}`, and establishes its structural properties.

Contents:
* `posHalf`, `shift_strictly_shrinks_support`, `posHalf_succ_subset`, `shift_mem_posHalf` — the
  link set, and that `ishiftLink τ` carries `posHalf τ c` into `posHalf τ (c + 1) ⊆ posHalf τ c`.
* `halfSpaceAlg`, `mem_halfSpaceAlg` — the submodule and its membership criterion, a directed union
  over finite supports inside the half-space, in the manner of
  `InfiniteLattice.quasiLocalAlg`.
* `one_mem_halfSpaceAlg` — the unit observable is in it, on the empty support.
* `halfSpaceAlg_mul_mem`, `halfSpaceAlg_prod_mem` — closure under binary and finite products. The
  definition stays a `Submodule`; the multiplicative closure is supplied as lemmas rather than by
  changing the type.
* `isLocalOn_ireflObs`, `disjoint_image_ireflLink_posHalf` — the reflection of a local observable is
  local on the reflected support, and a support inside `posHalf τ p` reflected about `2 * p - 2` is
  disjoint from itself.
* `ishiftObsCM`, `halfSpaceAlg_shift_stable` — the shift as a linear endomorphism of
  `C(IConf G, ℝ)`, mapping `halfSpaceAlg τ c` into itself.
* `halfLinkObs`, `halfLinkObs_mem`, `shift_moves_halfLinkObs`, `ishiftObsCM_halfLinkObs`,
  `ishiftObsCM_iterate_halfLinkObs`, `shift_iterate_moves_halfLinkObs`,
  `shift_no_finite_order_on_halfSpaceAlg` — one-link observables inside the half-space, and that
  every positive number of shifts moves one of them, so no positive power of `ishiftObsCM τ` is the
  identity on `halfSpaceAlg τ p`.

Scope.
* No state on `IConf G` is constructed here, so nothing supplies
  `ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg τ c)`. The form-level reflection positivity
  the tree proves, `ReflectStrong.wilsonGibbsReflForm`'s `form_nonneg`, lives on a slab of a
  periodic lattice at an even reflection constant and requires `0 ≤ β`; this module's region is a
  half-space of `ℤ⁴`, `latticeReflection τ c` ranges over every `c : ℤ`, and no parity or coupling
  restriction is imposed.
* `shift_no_finite_order_on_halfSpaceAlg` is motion in the algebra, not in a GNS quotient: an
  `F` with `ishiftObsCM τ F ≠ F` can still have `T F - F` in the null space of a form.
* It requires a function on the group separating two elements. At `SU 0` and `SU 1` the group is a
  singleton and none exists; `CrossingIntegration.trace_gNeg` supplies one at `SU 3`.
  `ReflectionHalfSpace.halfSpaceAlg_has_nonconstant` is a different statement — it separates two
  configurations by an observable, not two group elements by a function.
* `ishiftObsCM` puts the shift on `C(IConf G, ℝ)`, the carrier `InfiniteReflection.stateReflForm`
  works over. Nothing here proves that `ireflObs` preserves a counterpart of `halfSpaceAlg`.
-/

namespace MassGap.HalfSpaceAlgebra

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.LatticeReflection

/-! ## 1. The half-space, as a set of links -/

/-- The positive half-space `{l | c ≤ l.2 τ}`: links whose base site is at or beyond the plane `c`
in direction `τ`. A link in direction `τ` based at `x` spans `[x_τ, x_τ + 1]`, so `c ≤ x_τ` places
the whole link at or beyond the plane.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension the direction index `τ`
ranges over. `c` is the caller's plane and `τ` the caller's time direction. -/
def posHalf (τ : Fin 4) (c : ℤ) : Set ILink := {l | c ≤ l.2 τ}

/-- `ishiftLink τ` carries `posHalf τ c` into `posHalf τ (c + 1)`: the shifted region is strictly
inside the original. Unfolds `ishift`, whose `Function.update` raises the `τ` coordinate, and
closes by `omega`.

Unlike a bounded block, whose shifted copies have empty intersection
(`HalfLineTransfer.orbitCore_eq_empty`), the shifted copies of a half-space are nested, so
`HalfLineTransfer.const_of_shift_stable` does not apply to `halfSpaceAlg`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `1` is one lattice step, the amount `ishift`
adds to the `τ` coordinate. -/
theorem shift_strictly_shrinks_support (τ : Fin 4) (c : ℤ) {l : ILink} (hl : l ∈ posHalf τ c) :
    ishiftLink τ l ∈ posHalf τ (c + 1) := by
  show c + 1 ≤ (ishiftLink τ l).2 τ
  show c + 1 ≤ (ishift τ l.2) τ
  rw [ishift, Function.update_self]
  have : c ≤ l.2 τ := hl
  omega

#print axioms shift_strictly_shrinks_support

/-- `posHalf τ (c + 1) ⊆ posHalf τ c`: the smaller half-space sits inside the larger, by `omega`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `1` is the one lattice step separating the two
planes. -/
theorem posHalf_succ_subset (τ : Fin 4) (c : ℤ) : posHalf τ (c + 1) ⊆ posHalf τ c := by
  intro l hl
  have : c + 1 ≤ l.2 τ := hl
  show c ≤ l.2 τ
  omega

#print axioms posHalf_succ_subset

/-- `ishiftLink τ l ∈ posHalf τ c` for `l ∈ posHalf τ c`: the composite of the previous two
lemmas, which is the form `halfSpaceAlg_shift_stable` consumes.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension; the `+ 1` of the
intermediate half-space has been composed away. -/
theorem shift_mem_posHalf (τ : Fin 4) (c : ℤ) {l : ILink} (hl : l ∈ posHalf τ c) :
    ishiftLink τ l ∈ posHalf τ c :=
  posHalf_succ_subset τ c (shift_strictly_shrinks_support τ c hl)

#print axioms shift_mem_posHalf

/-! ## 2. The algebra -/

section Alg

variable {G : Type} [TopologicalSpace G]

/-- The positive half-space algebra: the `Submodule ℝ C(IConf G, ℝ)` whose carrier is the set of
`F` admitting some `S : Finset ILink` with `↑S ⊆ posHalf τ c` and `IsLocalOn S F`. Closure under
addition takes the union of supports; the zero and scalar cases reuse one support.

A directed union, as `InfiniteLattice.quasiLocalAlg` is: the support must be finite and inside the
half-space, and is otherwise unconstrained, so it may move as the observable does.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
def halfSpaceAlg (τ : Fin 4) (c : ℤ) : Submodule ℝ C(IConf G, ℝ) where
  carrier := {F | ∃ S : Finset ILink, (↑S ⊆ posHalf τ c) ∧ IsLocalOn S (F : IConf G → ℝ)}
  add_mem' := by
    rintro F H ⟨S, hS, hFl⟩ ⟨T, hT, hHl⟩
    refine ⟨S ∪ T, ?_, fun U V h => ?_⟩
    · intro l hl
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hl) with h1 | h1
      · exact hS (Finset.mem_coe.mpr h1)
      · exact hT (Finset.mem_coe.mpr h1)
    · show F U + H U = F V + H V
      rw [(hFl.mono Finset.subset_union_left) U V h,
          (hHl.mono Finset.subset_union_right) U V h]
  zero_mem' := ⟨∅, by simp [posHalf], fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro r F ⟨S, hS, hFl⟩
    refine ⟨S, hS, fun U V h => ?_⟩
    show r * F U = r * F V
    rw [hFl U V h]

/-- Membership in `halfSpaceAlg τ c` unfolded: `F ∈ halfSpaceAlg τ c` iff there is a finite
`S : Finset ILink` with `↑S ⊆ posHalf τ c` and `IsLocalOn S F`. By `Iff.rfl`.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension. -/
theorem mem_halfSpaceAlg {τ : Fin 4} {c : ℤ} {F : C(IConf G, ℝ)} :
    F ∈ halfSpaceAlg (G := G) τ c
      ↔ ∃ S : Finset ILink, (↑S ⊆ posHalf τ c) ∧ IsLocalOn S (F : IConf G → ℝ) := Iff.rfl

#print axioms mem_halfSpaceAlg

/-- `(1 : C(IConf G, ℝ)) ∈ halfSpaceAlg τ c`, witnessed by the empty support. This is what lets
`InfiniteReflection.stateReflForm_vac_norm` apply to this carrier.

DERIVED: `4` is the spacetime dimension `τ` indexes; `1` is the unit observable, the constant
function. The empty support is forced, not chosen: a constant is local on any set. -/
theorem one_mem_halfSpaceAlg (τ : Fin 4) (c : ℤ) :
    (1 : C(IConf G, ℝ)) ∈ halfSpaceAlg (G := G) τ c :=
  ⟨∅, by simp [posHalf], fun _ _ _ => rfl⟩

#print axioms one_mem_halfSpaceAlg

/-- `halfSpaceAlg τ c` is closed under multiplication: `F * H` is local on the union of the two
supports, and that union is still inside `posHalf τ c`.

The definition remains a `Submodule`, which carries only additive and scalar closure; the
multiplicative closure is supplied as this lemma rather than by upgrading the type every consumer is
written against. A chessboard estimate bounds a product of local observables, and needs the product
to lie in the carrier the reflection forms are built on.

DERIVED: `4` is the spacetime dimension, the direction index `τ` ranges over; no other numeral. -/
theorem halfSpaceAlg_mul_mem (τ : Fin 4) (c : ℤ) {F H : C(IConf G, ℝ)}
    (hF : F ∈ halfSpaceAlg (G := G) τ c) (hH : H ∈ halfSpaceAlg (G := G) τ c) :
    F * H ∈ halfSpaceAlg (G := G) τ c := by
  classical
  obtain ⟨S, hS, hFl⟩ := hF
  obtain ⟨T, hT, hGl⟩ := hH
  refine ⟨S ∪ T, ?_, ?_⟩
  · intro l hl
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hl) with h1 | h1
    · exact hS (Finset.mem_coe.mpr h1)
    · exact hT (Finset.mem_coe.mpr h1)
  · exact hFl.mul hGl

#print axioms halfSpaceAlg_mul_mem

/-- A finite product stays in the algebra: if `F i ∈ halfSpaceAlg τ c` for every `i ∈ s`, then
`∏ i ∈ s, F i ∈ halfSpaceAlg τ c`. Induction on `s`, with `one_mem_halfSpaceAlg` for the empty
product and `halfSpaceAlg_mul_mem` at each insertion.

DERIVED: `4` is the spacetime dimension, the direction index `τ` ranges over; no other numeral. -/
theorem halfSpaceAlg_prod_mem (τ : Fin 4) (c : ℤ) {ι : Type*} (s : Finset ι)
    (F : ι → C(IConf G, ℝ)) (hF : ∀ i ∈ s, F i ∈ halfSpaceAlg (G := G) τ c) :
    (∏ i ∈ s, F i) ∈ halfSpaceAlg (G := G) τ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_halfSpaceAlg (G := G) τ c
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha]
    exact halfSpaceAlg_mul_mem τ c (hF a (Finset.mem_insert_self a s'))
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

#print axioms halfSpaceAlg_prod_mem



/-! ## 2b. The reflection moves the support off the half-space

The counterparts for the reflection of what `InfiniteShift.isLocalOn_ishiftObs` gives for the shift:
that reflecting a local observable moves its support to the reflected set, and that reflected about
`2 * p - 2`, a support inside `{x_τ ≥ p}` lands inside `{x_τ ≤ p - 2}`, disjoint from the
original. -/

/-- If `F` is local on `S`, then `ireflObs τ c F` is local on `S.image (ireflLink τ c)`. Reading
`ireflObs τ c F` at a link reads `F` at that link's mirror, so the support is the image of the
support under `ireflLink`. The dagger applied on `τ`-links changes the value read rather than the
link read, so it does not enter the support.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
theorem isLocalOn_ireflObs [Group G] [ContinuousInv G] [CompactSpace G] (τ : Fin 4) (c : ℤ)
    {S : Finset ILink} {F : C(IConf G, ℝ)} (hF : IsLocalOn S (⇑F)) :
    IsLocalOn (S.image (ireflLink τ c)) (⇑(ireflObs τ c F)) := by
  classical
  intro U V h
  show F (ireflConf τ c U) = F (ireflConf τ c V)
  refine hF _ _ (fun l hl => ?_)
  have hUV : U (ireflLink τ c l) = V (ireflLink τ c l) :=
    h (ireflLink τ c l) (Finset.mem_image_of_mem _ hl)
  simp only [ireflConf, hUV]

#print axioms isLocalOn_ireflObs

/-- For `S` inside `posHalf τ p`, the reflected image `S.image (ireflLink τ (2 * p - 2))` is
disjoint from `S`. A non-axis link based at `x` reflects to `2 * p - 2 - x_τ ≤ p - 2`, and a
`τ`-link reflects about `2 * p - 3` instead, landing at `≤ p - 3`; both cases are settled by
`omega`.

Scope: the reflection constant is `2 * p - 2`, not `2 * p`. At `2 * p` the statement is false,
because the two supports meet on the reflection plane.

DERIVED: `4` is the spacetime dimension `τ` indexes. The constant `2 * p - 2` is the reflection
plane placed two lattice steps below `2 * p`: the `2` multiplying `p` is the doubling any reflection
about a plane carries, and the subtracted `2` is the offset that makes the images disjoint. -/
theorem disjoint_image_ireflLink_posHalf (τ : Fin 4) (p : ℤ) {S : Finset ILink}
    (hS : (↑S : Set ILink) ⊆ posHalf τ p) :
    Disjoint (S.image (ireflLink τ (2 * p - 2))) S := by
  classical
  rw [Finset.disjoint_left]
  rintro l hl hlS
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
  have hmp : p ≤ m.2 τ := hS (Finset.mem_coe.mpr hm)
  have hlp : p ≤ (ireflLink τ (2 * p - 2) m).2 τ := hS (Finset.mem_coe.mpr hlS)
  by_cases h1 : m.1 = τ
  · rw [ireflLink_eq_axis τ (2 * p - 2) h1] at hlp
    simp only [ireflSite_axis] at hlp
    omega
  · have hne : (ireflLink τ (2 * p - 2) m).2 = ireflSite τ (2 * p - 2) m.2 := by
      simp only [ireflLink, if_neg h1]
    rw [hne] at hlp
    simp only [ireflSite_axis] at hlp
    omega

#print axioms disjoint_image_ireflLink_posHalf


/-! ## 3. ⭐ The shift preserves it -/

/-- The time shift on observables, as an `ℝ`-linear endomorphism of `C(IConf G, ℝ)`: precomposition
with `ishiftConf τ`, which is continuous. Additivity and homogeneity are `rfl`.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
def ishiftObsCM (τ : Fin 4) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨ishiftConf τ, continuous_ishiftConf τ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ishiftObsCM_apply (τ : Fin 4) (F : C(IConf G, ℝ)) (U : IConf G) :
    ishiftObsCM τ F U = F (ishiftConf τ U) := rfl

/-- `ishiftObsCM τ` maps `halfSpaceAlg τ c` into itself. `InfiniteShift.isLocalOn_ishiftObs` moves
the support from `S` to `S.image (ishiftLink τ)`, and `shift_mem_posHalf` places that image back
inside `posHalf τ c`.

Scope: the map is into, not onto — the shifted support lies in `posHalf τ (c + 1)`.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
theorem halfSpaceAlg_shift_stable (τ : Fin 4) (c : ℤ) {F : C(IConf G, ℝ)}
    (hF : F ∈ halfSpaceAlg (G := G) τ c) :
    ishiftObsCM τ F ∈ halfSpaceAlg (G := G) τ c := by
  classical
  obtain ⟨S, hS, hFl⟩ := hF
  refine ⟨S.image (ishiftLink τ), ?_, ?_⟩
  · intro l hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hl)
    exact shift_mem_posHalf τ c (hS (Finset.mem_coe.mpr hm))
  · exact isLocalOn_ishiftObs τ hFl

#print axioms halfSpaceAlg_shift_stable

/-! ## 4. It is not the trivial submodule -/

/-- A one-link observable: `f` composed with evaluation at the link `l`, which is continuous. Used
below as the witness that `halfSpaceAlg` contains more than the constants.

DERIVED: no numeral occurs; `l` and `f` are the caller's. -/
def halfLinkObs (l : ILink) (f : C(G, ℝ)) : C(IConf G, ℝ) :=
  f.comp ⟨fun U => U l, continuous_coord l⟩

/-- `halfLinkObs l f ∈ halfSpaceAlg τ c` for every link `l ∈ posHalf τ c` and every `f : C(G, ℝ)`,
witnessed by the singleton support `{l}`. So the algebra contains a one-link observable at every
link of the half-space and is not the submodule of constants.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
theorem halfLinkObs_mem (τ : Fin 4) (c : ℤ) {l : ILink} (hl : l ∈ posHalf τ c) (f : C(G, ℝ)) :
    halfLinkObs l f ∈ halfSpaceAlg (G := G) τ c := by
  classical
  refine ⟨{l}, ?_, fun U V h => ?_⟩
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_singleton] at hm
    exact hm ▸ hl
  · show f (U l) = f (V l)
    rw [h l (Finset.mem_singleton_self l)]

#print axioms halfLinkObs_mem

/-- `ishiftObsCM τ (halfLinkObs l f) ≠ halfLinkObs l f` whenever `f g₀ ≠ f g₁` for some pair of
group elements. The proof evaluates both sides at the configuration `fun j => if j = l then g₁ else g₀`,
using `ishiftLink τ l ≠ l` to select different group elements on the two sides.

Scope: the separating hypothesis `f g₀ ≠ f g₁` is a real requirement — at a singleton group no such
`f` exists.

DERIVED: `4` is the spacetime dimension `τ` indexes; `g₀`, `g₁` and `f` are the caller's separating
data and no numeral is a magnitude. -/
theorem shift_moves_halfLinkObs (τ : Fin 4) (l : ILink)
    {f : C(G, ℝ)} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) :
    ishiftObsCM τ (halfLinkObs l f) ≠ halfLinkObs l f := by
  classical
  intro h
  have hmoved : ishiftLink τ l ≠ l := by
    have := ishiftLink_iterate_ne τ Nat.one_pos l
    rwa [Function.iterate_one] at this
  have hval := congrFun (congrArg (fun F : C(IConf G, ℝ) => (F : IConf G → ℝ)) h)
    (fun j : ILink => if j = l then g₁ else g₀)
  simp only [ishiftObsCM_apply, halfLinkObs, ishiftConf, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, if_neg hmoved] at hval
  exact hf hval

#print axioms shift_moves_halfLinkObs

/-- `ishiftObsCM τ (halfLinkObs l f) = halfLinkObs (ishiftLink τ l) f`, by `rfl` after `ext`: one
shift of a one-link observable is the one-link observable one link along. The base step of the
iterated version below.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes. -/
theorem ishiftObsCM_halfLinkObs (τ : Fin 4) (l : ILink) (f : C(G, ℝ)) :
    ishiftObsCM τ (halfLinkObs l f) = halfLinkObs (ishiftLink τ l) f := by
  ext U
  rfl

#print axioms ishiftObsCM_halfLinkObs

/-- `(ishiftObsCM τ)^[k] (halfLinkObs l f) = halfLinkObs ((ishiftLink τ)^[k] l) f` at every `k : ℕ`,
by induction on `k` generalising `l`, from `ishiftObsCM_halfLinkObs`.

DERIVED: the one numeral is the `4` of `Fin 4`, the spacetime dimension `τ` indexes; `k` is the
caller's step count. -/
theorem ishiftObsCM_iterate_halfLinkObs (τ : Fin 4) (k : ℕ) (l : ILink) (f : C(G, ℝ)) :
    (ishiftObsCM τ)^[k] (halfLinkObs l f) = halfLinkObs ((ishiftLink τ)^[k] l) f := by
  induction k generalizing l with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply, ishiftObsCM_halfLinkObs, ih,
        Function.iterate_succ_apply]

#print axioms ishiftObsCM_iterate_halfLinkObs

/-- `(ishiftObsCM τ)^[k] (halfLinkObs l f) ≠ halfLinkObs l f` for every `0 < k`, given a separating
`f g₀ ≠ f g₁`. Rewrites by `ishiftObsCM_iterate_halfLinkObs` and uses
`InfiniteShift.ishiftLink_iterate_ne` for `(ishiftLink τ)^[k] l ≠ l`.
`shift_moves_halfLinkObs` is the case `k = 1`.

DERIVED: `4` is the spacetime dimension `τ` indexes; `0` is the excluded step count, since the
identity iterate does fix the observable. -/
theorem shift_iterate_moves_halfLinkObs (τ : Fin 4) {k : ℕ} (hk : 0 < k) (l : ILink)
    {f : C(G, ℝ)} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) :
    (ishiftObsCM τ)^[k] (halfLinkObs l f) ≠ halfLinkObs l f := by
  classical
  rw [ishiftObsCM_iterate_halfLinkObs]
  intro h
  have hmoved : (ishiftLink τ)^[k] l ≠ l := ishiftLink_iterate_ne τ hk l
  have hval := congrFun (congrArg (fun F : C(IConf G, ℝ) => (F : IConf G → ℝ)) h)
    (fun j : ILink => if j = l then g₁ else g₀)
  simp only [halfLinkObs, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    if_neg hmoved, if_pos rfl] at hval
  exact hf hval

#print axioms shift_iterate_moves_halfLinkObs

/-- No positive power of the shift is the identity on the half-space algebra: given a separating
`f g₀ ≠ f g₁` and `0 < k`, there is `F ∈ halfSpaceAlg τ p` with `(ishiftObsCM τ)^[k] F ≠ F`. The
witness is `halfLinkObs ((0 : Fin 4), fun _ => p) f`, which lies in the algebra by
`halfLinkObs_mem` at `le_refl p`, and is moved by `shift_iterate_moves_halfLinkObs`.

The hypothesis of `ClayAssembly.finite_order_contraction_is_isometry` — that `T ^ n = id` for some
`n ≥ 1` — is therefore not available for this shift, whereas on the periodic lattice
`HalfLineTransfer.shiftObs_pow_period` does supply it.

Scope.
* The witness is exhibited inside `halfSpaceAlg τ p`, not merely in the quasi-local algebra; a
  submodule could otherwise contain only observables the shift fixes.
* This is motion in the algebra, not in a GNS quotient: `opT [F] = [F]` whenever `T F - F` lies in
  the null space of the form, so `ClayAssembly.TransferMovesSomething` does not follow.
* The separating hypothesis is required. At `SU 0` and `SU 1` the group is a singleton and no such
  `f` exists; `CrossingIntegration.trace_gNeg` supplies one at `SU 3`, where `Re tr` separates
  `gNeg` from the identity. `ReflectionHalfSpace.halfSpaceAlg_has_nonconstant` does not serve here:
  it separates two configurations by an observable, where a function on the group separating two
  group elements is what is needed.

DERIVED: `4` is the spacetime dimension `τ` indexes, and also the direction index `0` of the
witness link; `0` is additionally the excluded step count in `0 < k`. `g₀`, `g₁` and `f` are the
caller's separating data. -/
theorem shift_no_finite_order_on_halfSpaceAlg (τ : Fin 4) (p : ℤ)
    {f : C(G, ℝ)} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) {k : ℕ} (hk : 0 < k) :
    ∃ F ∈ halfSpaceAlg (G := G) τ p, (ishiftObsCM τ)^[k] F ≠ F := by
  refine ⟨halfLinkObs ((0 : Fin 4), fun _ => p) f,
    halfLinkObs_mem τ p (le_refl p) f, ?_⟩
  exact shift_iterate_moves_halfLinkObs τ hk _ hf

#print axioms shift_no_finite_order_on_halfSpaceAlg

end Alg

end MassGap.HalfSpaceAlgebra
