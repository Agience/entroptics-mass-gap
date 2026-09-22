import Mathlib
import MassGap.InfiniteShift
import MassGap.InfiniteReflection
import MassGap.LatticeReflection

/-!
# MassGap.HalfSpaceAlgebra — the positive half-space algebra, and the shift preserves it

## The item this closes

`InfiniteReflection` shows reflection positivity is a statement about observables supported in ONE
HALF-SPACE — `reflection_positivity_fails_off_the_half_space` proves it is false otherwise — and so
takes the half-space algebra as a parameter it does not construct. **This constructs it, and proves
the one structural property the whole Osterwalder–Schrader argument turns on.**

## Why this is the step the slab could not take

`HalfLineTransfer.const_of_shift_stable` says a submodule of the FIXED-BLOCK slab algebra that the
shift preserves consists of constants: the shifted copies of one bounded block intersect in nothing,
so a stable observable is determined by nothing. **The positive half-space is not a bounded block.**
Shifting `{x_τ ≥ c}` in the `+τ` direction gives `{x_τ ≥ c+1}`, which is a SUBSET of it — the region
does not move off itself, it moves into itself — so an observable supported there stays supported
there and nothing forces it to be constant.

`halfSpaceAlg_shift_stable` is that statement, and with `InfiniteShift.ishiftObs_infinite_order` it
gives what no finite carrier in the tree has:

**a subalgebra the time translation maps into itself, on which that translation is neither the
identity nor of finite order.**

That is the Osterwalder–Seiler setup. Every finite carrier failed one of the two.

## What is proved

* `halfSpaceAlg` — the observables local on a finite subset of `{x_τ ≥ c}`, a `Submodule`.
* `halfSpaceAlg_shift_stable` — **the forward shift maps it into itself.**
* `one_mem_halfSpaceAlg` — the constant is in it, so `stateReflForm_vac_norm` applies and the
  vacuum exists.
* `halfLinkObs_mem` — it contains a one-link observable at every link of the half-space, so it is
  not the constants.
* `shift_moves_halfLinkObs` — the shift is not the identity ON THIS submodule, which had to be
  checked separately: a submodule could in principle contain only observables the shift fixes.
* `shift_strictly_shrinks_support` — the shift moves the supporting region strictly, which is what
  distinguishes this from the slab's shift-stability and is the reason `const_of_shift_stable` does
  not apply.

## ⚠ What is NOT proved

**No state**, and the gap is not a change of lattice.

Nothing here exhibits a reflection-positive, reflection-invariant state on `IConf G`, and without one
`stateReflForm` has no input. Supplying `ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg τ c)`
is NOT a transcription of an existing result:

* `Complete.wilson_reflection_positive_at` is not about a form at all — it asserts nonnegativity of
  the correlation SEQUENCE `wilsonCorrAt`. The form-level fact is `ReflectStrong.wilsonGibbsReflForm`'s
  `form_nonneg`.
* That one lives on a **slab** of a **periodic** lattice, at `n = 2*m`, at the EVEN reflection
  constant `a + a`. This file's region is a **half-space** of `ℤ⁴` and `latticeReflection τ c` ranges
  over every `c : ℤ`.
* `ReflectStrong` records that the even and odd reflection constants are different problems, that the
  odd one is `OddLagSplit`'s with a different three-block decomposition, and that it genuinely needs
  `0 ≤ β` — `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refuting it at `β < 0`. **This
  file imposes no parity restriction and no sign condition on `β`.**

**And `TransferData` is further off than two fields.** Beyond `T_symm` (the reflection must conjugate
the shift to its inverse) and `T_contract` (the Schwarz iteration), the shift and the form are not
yet on the same carrier: `InfiniteShift.ishiftObs` acts on plain functions and its results are stated
against `InfiniteLattice.quasiLocalAlg`, while `stateReflForm` needs a submodule of `C(IConf G, ℝ)`.
`ishiftObsCM` below bridges that for the shift; that `ireflObs` preserves `halfSpaceAlg`'s
counterpart is not proved anywhere.
-/

namespace MassGap.HalfSpaceAlgebra

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.LatticeReflection

/-! ## 1. The half-space, as a set of links -/

/-- **THE POSITIVE HALF-SPACE**: links whose base site is at or beyond the plane `c` in direction
`τ`. A link in direction `τ` based at `x` spans `[x_τ, x_τ+1]`, so requiring `c ≤ x_τ` puts the whole
link at or beyond the plane.

DERIVED: no numeral. `c` is the caller's plane and `τ` the caller's time direction. -/
def posHalf (τ : Fin 4) (c : ℤ) : Set ILink := {l | c ≤ l.2 τ}

/-- **THE SHIFT CARRIES THE HALF-SPACE STRICTLY INSIDE ITSELF.** `{x_τ ≥ c}` goes to `{x_τ ≥ c+1}`.

**This is the whole difference from the slab.** `HalfLineTransfer.orbitCore_eq_empty` empties the
intersection of a bounded block's shifted copies; the shifted copies of a half-space are nested and
their intersection is only empty in the limit, never at a finite depth, so
`const_of_shift_stable` has nothing to work with.

DERIVED: the `1` is one lattice step, `ishift`'s own. -/
theorem shift_strictly_shrinks_support (τ : Fin 4) (c : ℤ) {l : ILink} (hl : l ∈ posHalf τ c) :
    ishiftLink τ l ∈ posHalf τ (c + 1) := by
  show c + 1 ≤ (ishiftLink τ l).2 τ
  show c + 1 ≤ (ishift τ l.2) τ
  rw [ishift, Function.update_self]
  have : c ≤ l.2 τ := hl
  omega

#print axioms shift_strictly_shrinks_support

/-- And `{x_τ ≥ c+1} ⊆ {x_τ ≥ c}`, so the shift lands back in the original half-space.

DERIVED: the `1` is one lattice step. -/
theorem posHalf_succ_subset (τ : Fin 4) (c : ℤ) : posHalf τ (c + 1) ⊆ posHalf τ c := by
  intro l hl
  have : c + 1 ≤ l.2 τ := hl
  show c ≤ l.2 τ
  omega

#print axioms posHalf_succ_subset

/-- The composite, which is the form the algebra proof uses.

DERIVED: no numeral of its own. -/
theorem shift_mem_posHalf (τ : Fin 4) (c : ℤ) {l : ILink} (hl : l ∈ posHalf τ c) :
    ishiftLink τ l ∈ posHalf τ c :=
  posHalf_succ_subset τ c (shift_strictly_shrinks_support τ c hl)

#print axioms shift_mem_posHalf

/-! ## 2. The algebra -/

section Alg

variable {G : Type} [TopologicalSpace G]

/-- **THE POSITIVE HALF-SPACE ALGEBRA**: continuous observables local on SOME finite set of links
inside the half-space.

A directed union, exactly as `InfiniteLattice.quasiLocalAlg` is — the support must be finite and
inside the half-space, and is otherwise free to be anywhere and to move. That freedom is what
`HalfLineTransfer.const_of_shift_stable`'s hypothesis forbids and what makes this carrier different.

DERIVED: no numeral. -/
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

/-- Membership, unfolded. -/
theorem mem_halfSpaceAlg {τ : Fin 4} {c : ℤ} {F : C(IConf G, ℝ)} :
    F ∈ halfSpaceAlg (G := G) τ c
      ↔ ∃ S : Finset ILink, (↑S ⊆ posHalf τ c) ∧ IsLocalOn S (F : IConf G → ℝ) := Iff.rfl

#print axioms mem_halfSpaceAlg

/-- **THE CONSTANT IS IN IT**, on the empty support — so the vacuum exists and
`InfiniteReflection.stateReflForm_vac_norm` applies.

DERIVED: the `1` is the unit observable; the empty support is not a choice. -/
theorem one_mem_halfSpaceAlg (τ : Fin 4) (c : ℤ) :
    (1 : C(IConf G, ℝ)) ∈ halfSpaceAlg (G := G) τ c :=
  ⟨∅, by simp [posHalf], fun _ _ _ => rfl⟩

#print axioms one_mem_halfSpaceAlg

/-- **⭐ THE HALF-SPACE ALGEBRA IS CLOSED UNDER MULTIPLICATION.**

`halfSpaceAlg` is a `Submodule`, so it carried only additive and scalar closure. A product of two of
its elements is local on the UNION of their supports, and that union is still inside `posHalf`
because each piece already is — so the name was right and the closure was missing.

It stays a `Submodule` deliberately: upgrading the definition to a `Subalgebra` would move the type
every consumer is written against. The closure is supplied here as a lemma instead.

**Why it is wanted.** A chessboard estimate bounds a PRODUCT of local observables over a region.
Without this the product is not an element of the carrier the reflection forms are built on, so
`Transfer.ReflForm.cauchy_schwarz` has nothing to be applied to.

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

/-- **⭐ AND A FINITE PRODUCT OF HALF-SPACE OBSERVABLES STAYS IN THE ALGEBRA.**

`halfSpaceAlg_mul_mem` at a `Finset.prod`, with `one_mem_halfSpaceAlg` for the empty product. This
is the membership a chessboard argument needs of the object it bounds: a product over blocks, each
block's observable living on the positive half.

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



/-! ## 2b. ⭐ The reflection moves the support, and moves it OFF the half-space

`InfiniteShift.isLocalOn_ishiftObs` does this for the shift. The reflection needs the same two
facts, and the second is the one that matters: reflected about `2p-2`, a support inside
`{x_τ ≥ p}` lands inside `{x_τ ≤ p-2}`, which the original misses by two full lattice steps. -/

/-- **THE REFLECTION OF A LOCAL OBSERVABLE IS LOCAL ON THE REFLECTED SUPPORT.** Reading
`ireflObs τ c F` at a link reads `F` at that link's mirror, so the support is the image of the
support under `ireflLink`. The dagger on `τ`-links changes the VALUE read and not the LINK read, so
it does not enter.

DERIVED: `4` is the dimension. -/
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

/-- **⭐ AND THE REFLECTED SUPPORT MISSES THE HALF-SPACE ENTIRELY.**

A support inside `{x_τ ≥ p}`, reflected about `2p-2`, lands inside `{x_τ ≤ p-2}`: a non-axis link
based at `x` goes to `2p-2-x_τ ≤ p-2`, and a `τ`-link reflects about `2p-3` instead, landing at
`≤ p-3`. Either way the two sets are disjoint, with a step to spare.

DERIVED: the reflection constant `2p-2` is the one `gapAt_iff_subtracted_pairing` puts on the LEFT
of the gap inequality, not a choice; the `2` separating it from `2p` is what makes this disjoint at
all, and at `2p` the statement is FALSE — the supports meet on the reflection plane. `4` is the
dimension. -/
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

/-- The time shift on observables, as a linear map on continuous functions.

DERIVED: no numeral of its own. -/
def ishiftObsCM (τ : Fin 4) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨ishiftConf τ, continuous_ishiftConf τ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ishiftObsCM_apply (τ : Fin 4) (F : C(IConf G, ℝ)) (U : IConf G) :
    ishiftObsCM τ F U = F (ishiftConf τ U) := rfl

/-- **⭐ THE HALF-SPACE ALGEBRA IS SHIFT-STABLE.**

`InfiniteShift.isLocalOn_ishiftObs` moves the support from `S` to `S.image (ishiftLink τ)`, and
`shift_mem_posHalf` puts that image back inside the half-space. **So the forward time translation is
an endomorphism of this algebra.**

Together with `InfiniteShift.ishiftObs_infinite_order` — no positive power of the shift is the
identity — this is the pair of properties the Osterwalder–Seiler transfer operator needs and that
every finite carrier in the tree was proved to lack: the slab fails stability without triviality
(`shiftObs_eq_self_of_shift_stable`), the torus fails infinite order (`shiftObs_pow_period`).

DERIVED: no numeral. -/
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

/-- A one-link observable inside the half-space, used as the witness that the algebra has content.

DERIVED: no numeral. -/
def halfLinkObs (l : ILink) (f : C(G, ℝ)) : C(IConf G, ℝ) :=
  f.comp ⟨fun U => U l, continuous_coord l⟩

/-- **THE ALGEBRA CONTAINS A ONE-LINK OBSERVABLE AT EVERY LINK OF THE HALF-SPACE**, so it is not
the constants.

Without this the shift-stability above would be the slab's situation again — stable and worthless —
and the whole point is that here it is stable and not worthless.

DERIVED: no numeral. -/
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

/-- **AND THE SHIFT MOVES IT.** The one-link observable at `l` goes to the one-link observable at the
shifted link, and those differ whenever the group carries a function separating two elements.

So the shift is an endomorphism of this algebra that is not the identity ON IT — which
`InfiniteShift.ishiftObs_ne_id_of_separating` gives on the quasi-local algebra and which has to be
checked again here, because a submodule could in principle contain only observables the shift fixes.

DERIVED: no numeral. `g₀`, `g₁` and `f` are the caller's separating data. -/
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

/-- One shift of a one-link observable is the one-link observable one link along — the step the
induction below needs before its hypothesis can fire.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem ishiftObsCM_halfLinkObs (τ : Fin 4) (l : ILink) (f : C(G, ℝ)) :
    ishiftObsCM τ (halfLinkObs l f) = halfLinkObs (ishiftLink τ l) f := by
  ext U
  rfl

#print axioms ishiftObsCM_halfLinkObs

/-- **`k` SHIFTS OF A ONE-LINK OBSERVABLE IS THE ONE-LINK OBSERVABLE `k` LINKS ALONG.**

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem ishiftObsCM_iterate_halfLinkObs (τ : Fin 4) (k : ℕ) (l : ILink) (f : C(G, ℝ)) :
    (ishiftObsCM τ)^[k] (halfLinkObs l f) = halfLinkObs ((ishiftLink τ)^[k] l) f := by
  induction k generalizing l with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply, ishiftObsCM_halfLinkObs, ih,
        Function.iterate_succ_apply]

#print axioms ishiftObsCM_iterate_halfLinkObs

/-- **AND EVERY POSITIVE NUMBER OF SHIFTS MOVES IT.** `shift_moves_halfLinkObs` is the case `k = 1`.

DERIVED: the `0` is the excluded step count; `g₀`, `g₁` and `f` are the caller's separating data. -/
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

/-- **⭐⭐ THE SHIFT HAS INFINITE ORDER ON THE HALF-SPACE ALGEBRA — SO THE FINITE-ORDER NO-GO DOES
NOT REACH `ℤ⁴`.**

`ClayAssembly.finite_order_contraction_is_isometry` proves that a `TransferData` whose `T` satisfies
`T^n = id` for some `n ≥ 1` is a form-isometry, hence carries no decay, and that is the standing
reason "`I4` cannot come from the lattice". Its hypothesis is supplied on the PERIODIC lattice by
`HalfLineTransfer.shiftObs_pow_period`.

**On `ℤ⁴` there is no such `n`**, and this exhibits the witness inside the half-space algebra rather
than merely somewhere in the quasi-local one — which has to be checked separately, because a
submodule could in principle contain only observables the shift fixes.

**⛔ THIS DOES NOT PROVE `TransferMovesSomething`.** Motion in the ALGEBRA is not motion in the GNS
QUOTIENT: `opT [F] = [F]` whenever `T F - F` lies in the null space of the form. What it does is
remove the no-go, so the question is open rather than closed.

**⛔ AND IT NEEDS A SEPARATING FUNCTION**, which is a real hypothesis: at `SU 0` and `SU 1` the group
is a singleton and none exists. `CrossingIntegration.trace_gNeg` supplies one at `SU(3)`, where
`Re tr` separates `gNeg` from the identity. **⛔ `halfSpaceAlg_has_nonconstant` DOES NOT** — it
separates two CONFIGURATIONS by an observable, where this needs a function on the GROUP
separating two group elements.

DERIVED: the `0` is the excluded step count; `g₀`, `g₁` and `f` are the caller's separating data;
`4` is the dimension. -/
theorem shift_no_finite_order_on_halfSpaceAlg (τ : Fin 4) (p : ℤ)
    {f : C(G, ℝ)} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) {k : ℕ} (hk : 0 < k) :
    ∃ F ∈ halfSpaceAlg (G := G) τ p, (ishiftObsCM τ)^[k] F ≠ F := by
  refine ⟨halfLinkObs ((0 : Fin 4), fun _ => p) f,
    halfLinkObs_mem τ p (le_refl p) f, ?_⟩
  exact shift_iterate_moves_halfLinkObs τ hk _ hf

#print axioms shift_no_finite_order_on_halfSpaceAlg

end Alg

end MassGap.HalfSpaceAlgebra
