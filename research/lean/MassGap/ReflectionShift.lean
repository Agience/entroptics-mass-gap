import Mathlib
import MassGap.LatticeReflection
import MassGap.InfiniteShift

/-!
# MassGap.ReflectionShift — the reflection conjugates the time shift, on `ℤ⁴`

## What this closes

`SchwarzIteration.ShiftCompat` has four fields. Three of them are about the maps alone and are
settled here:

| field | settled by |
|---|---|
| `T_mul` | `ishiftObs_mul` — precomposition is multiplicative |
| `T_S` | `ishiftConf_iunshiftConf` — the backward shift is a right inverse |
| `theta_T` | `ireflObs_ishiftObs` — **the reflection conjugates the forward shift to the backward one** |

The fourth, `nu_T`, is translation invariance of the STATE and is not a property of these maps.

## It is a transcription, not a new idea

`WilsonTransfer.shiftConf_reflConf_shiftConf` proves the same identity on the finite periodic
lattice:

    shiftConf τ (reflConf τ c (shiftConf τ U)) = reflConf τ c U

and its docstring calls it *"the conjugation identity a transfer operator needs … `Θ ∘ S = S⁻¹ ∘ Θ`
written without an inverse, and it is exactly what makes the time translation self-adjoint for the
reflection form."* The tree already spends it on `WilsonTransfer.reflForm_shiftObs_symm`, which is
the finite-volume `T_symm` — the same role `theta_T` plays in `SchwarzIteration.form_shift_symm`.

**What was missing is the version on `InfiniteLattice`'s types.** `LatticeReflection` never mentions
`ishift`; `InfiniteShift` never mentions a reflection; and no backward shift existed on `IConf` at
all. `GibbsSpec` does define an `iunshift` on sites, but `GibbsSpec` is one of the import-isolated
duplicates of the lattice skeleton, so nothing on this side can reach it.

## The geometry, and why the constant moves

Over `ℤ` exactly as over `Fin n`: a step along the axis moves the reflection CONSTANT by one,

    ireflSite τ c (ishift τ x) = ireflSite τ (c−1) x,

because `c − (x_τ + 1) = (c−1) − x_τ`. On links the base shift of `ireflLink` travels with it, giving
`ireflLink τ c ∘ ishiftLink τ = ireflLink τ (c−1)` in BOTH cases of the direction split — the
`τ`-links reflect about `c−1` and land on `c−2`, the others about `c` and land on `c−1`, and those are
exactly `ireflLink τ (c−1)`'s two cases.

**The dagger survives because it never moves.** `ireflConf` inverts on `τ`-links, `ishiftLink`
preserves a link's direction (`ishiftLink_fst`), so both sides of every identity below carry the same
`l.1 = τ` split and the inverses cancel case by case rather than needing to be tracked.

## ⚠ What this does NOT close

**`nu_T`** — that the infinite-volume state does not see a translation. That is a property of the
state, and no Wilson state on `IConf` is exhibited with it.

**And `ShiftCompat` is still not constructible**, because it bundles `nu_T` with the three fields
settled here. What this file removes is the part that is about the lattice rather than the measure.
-/

namespace MassGap.ReflectionShift

open MassGap.InfiniteLattice MassGap.LatticeReflection MassGap.InfiniteShift

/-! ## 1. Sites: a step moves the reflection constant -/

/-- **A STEP ALONG THE AXIS MOVES THE REFLECTION CONSTANT BY ONE.** `c − (x_τ + 1) = (c−1) − x_τ`.

This is `Reflect.reflSite_shift_axis` over `ℤ` instead of `Fin n`. The `Fin n` proof used modular
subtraction; this one does not need it, which is why the transcription is available at all.

DERIVED: the `1` is one lattice step, `ishift`'s own; `4` is the spacetime dimension. -/
theorem ireflSite_ishift (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (ishift τ x) = ireflSite τ (c - 1) x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp only [ireflSite, ishift, Function.update_self]
    ring_nf
  · simp [ireflSite, ishift, Function.update_of_ne h]

#print axioms ireflSite_ishift

/-- **AND UNDOING A STEP MOVES IT THE OTHER WAY.**

DERIVED: the `1` is one lattice step; `4` is the dimension. -/
theorem iunshift_ireflSite (τ : Fin 4) (c : ℤ) (x : ISite) :
    Function.update (ireflSite τ c x) τ ((ireflSite τ c x) τ - 1) = ireflSite τ (c - 1) x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp only [ireflSite, Function.update_self]
    ring_nf
  · simp [ireflSite, Function.update_of_ne h]

#print axioms iunshift_ireflSite

/-! ## 2. The backward shift on the infinite lattice -/

/-- **UNDO ONE STEP.** `InfiniteShift` carries only the forward translation; `ShiftCompat` needs both.

DERIVED: the `1` is one lattice step; `4` is the dimension. -/
def iunshift (τ : Fin 4) (x : ISite) : ISite := Function.update x τ (x τ - 1)

/-- Undoing a step and taking it is doing nothing.

DERIVED: the `1` is one lattice step. -/
theorem ishift_iunshift (τ : Fin 4) (x : ISite) : ishift τ (iunshift τ x) = x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp [ishift, iunshift, Function.update_self]
  · simp [ishift, iunshift, Function.update_of_ne h]

#print axioms ishift_iunshift

/-- The backward shift on links; the direction is untouched, as for the forward one.

DERIVED: `4` is the spacetime dimension, `InfiniteLattice.ISite`'s own. -/
def iunshiftLink (τ : Fin 4) (l : ILink) : ILink := (l.1, iunshift τ l.2)

@[simp] theorem iunshiftLink_fst (τ : Fin 4) (l : ILink) : (iunshiftLink τ l).1 = l.1 := rfl

@[simp] theorem ishiftLink_fst' (τ : Fin 4) (l : ILink) : (ishiftLink τ l).1 = l.1 := rfl

theorem ishiftLink_iunshiftLink (τ : Fin 4) (l : ILink) :
    ishiftLink τ (iunshiftLink τ l) = l := by
  obtain ⟨μ, x⟩ := l
  simp [ishiftLink, iunshiftLink, ishift_iunshift]

#print axioms ishiftLink_iunshiftLink

/-! ## 3. ⭐ Links: the reflection conjugates the shift -/

/-- **⭐ REFLECTING AFTER A STEP IS REFLECTING ABOUT THE PREVIOUS PLANE.**

Both cases of the direction split land on `ireflLink τ (c−1)`'s corresponding case: a `τ`-link
reflects about `c−1` and a step sends it to `c−2`, which is `ireflLink τ (c−1)`'s `τ`-case; any other
link reflects about `c` and a step sends it to `c−1`, which is the other case. **The base shift of
`ireflLink` travels with the constant**, which is why one identity covers both.

DERIVED: the `1` is the constant's step, `ireflSite_ishift`'s; `4` is the dimension. -/
theorem ireflLink_ishiftLink (τ : Fin 4) (c : ℤ) (l : ILink) :
    ireflLink τ c (ishiftLink τ l) = ireflLink τ (c - 1) l := by
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp only [ireflLink, ishiftLink, if_pos h, Prod.mk.injEq, true_and]
    rw [ireflSite_ishift]
  · simp only [ireflLink, ishiftLink, if_neg h, Prod.mk.injEq, true_and]
    rw [ireflSite_ishift]

#print axioms ireflLink_ishiftLink

/-- **AND THE BACKWARD SHIFT UNDOES THE CONSTANT'S STEP.**

DERIVED: the `1` is the constant's step; `4` is the dimension. -/
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

/-! ## 4. ⭐ Configurations, with the dagger -/

section Conf

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]

/-- The backward shift on configurations.

DERIVED: `4` is the spacetime dimension, `InfiniteLattice.ISite`'s own. -/
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

/-- **⭐ THE CONJUGATION IDENTITY, ON CONFIGURATIONS.**
`shift ∘ reflect = reflect ∘ unshift` — the `ℤ⁴` transcription of
`WilsonTransfer.shiftConf_reflConf_shiftConf`.

**The dagger never has to be tracked.** `ishiftLink` and `iunshiftLink` both preserve a link's
direction, so the `l.1 = τ` split is the same on both sides and the inverses cancel case by case.

DERIVED: `4` is the dimension; no other numeral. -/
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

/-! ## 5. ⭐ And on observables — `theta_T`'s shape -/

section Obs

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

theorem continuous_iunshiftConf (τ : Fin 4) :
    Continuous (iunshiftConf (G := G) τ) :=
  continuous_pi fun l => continuous_apply (iunshiftLink τ l)

/-- The backward shift as a linear map on observables.

DERIVED: `4` is the spacetime dimension, `InfiniteLattice.ISite`'s own. -/
def iunshiftObs (τ : Fin 4) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨iunshiftConf τ, continuous_iunshiftConf τ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The forward shift as a linear map, matching `HalfSpaceAlgebra.ishiftObsCM`.

DERIVED: `4` is the spacetime dimension, `InfiniteLattice.ISite`'s own. -/
def ishiftObsL (τ : Fin 4) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨ishiftConf τ, continuous_ishiftConf τ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`T_mul`** — precomposition is multiplicative, whatever it precomposes with. -/
theorem ishiftObsL_mul (τ : Fin 4) (f g : C(IConf G, ℝ)) :
    ishiftObsL τ (f * g) = ishiftObsL τ f * ishiftObsL τ g := rfl

/-- **`T_S`** — translating back and then forward is doing nothing. -/
theorem ishiftObsL_iunshiftObs (τ : Fin 4) (f : C(IConf G, ℝ)) :
    ishiftObsL τ (iunshiftObs τ f) = f := by
  ext U
  show f (iunshiftConf τ (ishiftConf τ U)) = f U
  congr 1
  funext l
  show U (ishiftLink τ (iunshiftLink τ l)) = U l
  rw [ishiftLink_iunshiftLink]

#print axioms ishiftObsL_iunshiftObs

/-- **⭐ `theta_T` — THE REFLECTION CONJUGATES THE FORWARD SHIFT TO THE BACKWARD ONE.**

`θ(T f) = S(θ f)`, which is `SchwarzIteration.ShiftCompat.theta_T`'s field verbatim with
`R.θ = ireflObs τ c`, `T = ishiftObsL τ` and `S = iunshiftObs τ`.

This is the substantive field — the one the tree had on the periodic lattice
(`WilsonTransfer.shiftConf_reflConf_shiftConf`, spent on `reflForm_shiftObs_symm`) and nowhere on
`ℤ⁴`. It is what makes the reflection form symmetric for the transfer operator, which is the whole
reason Osterwalder–Schrader pairs a reflection with a translation.

DERIVED: `4` is the dimension; no other numeral. -/
theorem ireflObs_ishiftObs (τ : Fin 4) (c : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ c (ishiftObsL τ f) = iunshiftObs τ (ireflObs τ c f) := by
  ext U
  show f (ishiftConf τ (ireflConf τ c U)) = f (ireflConf τ c (iunshiftConf τ U))
  rw [ishiftConf_ireflConf]

#print axioms ireflObs_ishiftObs

end Obs

end MassGap.ReflectionShift
