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

The fourth, `nu_T`, is translation invariance of the STATE. It is REDUCED here, not assumed:

| field | settled by |
|---|---|
| `nu_T` | `nu_T_of_reflection_invariant` — **one translation is two reflections**, so translation invariance of the state is reflection invariance of the state at two ADJACENT constants |

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

**Reflection invariance of the INFINITE-VOLUME state.** `nu_T_of_reflection_invariant` needs
`IsReflectionInvariant` at `a` and at `a + 1`, so one of the two is always the LINK reflection. Both
are available at FINITE volume — `ReflectionHalfSpace.stateFree_reflection_invariant` holds at every
constant — and `InfiniteReflection.isReflectionInvariant_of_tendsto` carries either to a limit.

**What is missing is that the two limits are the same state.**
`ReflectionHalfSpace.eq_empty_of_stable_two_mirrors` proves no non-empty finite box is stable under
both mirrors, so the two finite-volume statements live on two box families and something must
identify what they converge to. That, and not `nu_T`, is what stands between here and a constructible
`ShiftCompat`; `ReflectionHalfSpace.wilson_transferData_of_thermodynamic_limit` parks it as a single
convergence hypothesis.

The odd constant needs no positivity, so the `0 ≤ β` restriction that makes the link reflection a
separate problem for `ReflPositiveOn` does not apply to it — `IsReflectionInvariant` is an equality,
not an inequality.
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

/-- **COMPOSING TWO REFLECTIONS TRANSLATES.** About `a` then `b`, the `τ` coordinate moves by
`a - b`; every other coordinate is untouched.

DERIVED: no numeral of its own; `4` is the dimension. -/
theorem ireflSite_comp (τ : Fin 4) (a b : ℤ) (x : ISite) :
    ireflSite τ a (ireflSite τ b x) = Function.update x τ (a - b + x τ) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, Function.update_self]
    abel
  · simp [ireflSite, Function.update_of_ne hj]

#print axioms ireflSite_comp

/-- **REFLECTING ABOUT `c` THEN `c + 1` TRANSLATES BY ONE**, in the `τ` coordinate only:
`(c + 1) - (c - x_τ) = x_τ + 1`. `LatticeReflection.ireflSite_ireflSite_pred` is the same fact with
the constants named `c` and `c - 1`; this spelling is the one the link lift needs at both of its
cases.

DERIVED: the `1` is the separation of the two mirrors, which is what makes the translation one step;
`4` is the dimension. -/
theorem ireflSite_comp_succ (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ (c + 1) (ireflSite τ c x) = ishift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, ishift, Function.update_self]
    ring
  · simp [ireflSite, ishift, Function.update_of_ne hj]

#print axioms ireflSite_comp_succ

/-- The same on links. A `τ`-link reflects about each constant MINUS ONE, and that offset cancels in
the difference of the two constants — which is why the translation comes out the same in every link
direction and the case split closes on the same lemma twice.

DERIVED: the `1`s are the mirror separation and `ireflLink`'s link length; `4` is the dimension. -/
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

/-- **⭐⭐ ONE TRANSLATION IS TWO REFLECTIONS, ON `ℤ⁴`.** The `ℤ⁴` counterpart of
`WilsonTransfer.shiftConf_eq_reflConf_comp`, which proves the same thing on the periodic torus and at
the same separation.

**⛔ THE ORDER IS LOAD-BEARING.** The SMALLER constant is applied first — outermost in the
expression. `ireflConf τ (a + 1) (ireflConf τ a U)` is the BACKWARD shift, and nothing below covers
it.

**⛔ AND THE SEPARATION IS ONE, NOT TWO.** A gap-`k` composite translates by `k` by the same
argument, but `WilsonTransferReduction.shiftCompat_of_nu_T` hardcodes `T := ishiftObsL τ` and
`transferData_of_state_facts` takes `hnu` at ONE step. Two-step invariance does not imply one-step,
so a gap-2 statement — however natural its even constants look — cannot feed the consumer. Parity
constrains `ReflPositiveOn` and `halfSpaceAlg`; it does not constrain `IsReflectionInvariant`, which
is all `nu_T` consumes, so there is no reason to pay for an even second constant here.

Two things cancel, and neither has to be tracked. The DAGGER cancels because it is applied twice on
a `τ`-link and not at all elsewhere — `ireflLink_fst` is what makes the two case splits the same
split. The `- 1` OFFSET on a `τ`-link cancels in the DIFFERENCE of the two constants.

`Nat.iterate` is not used: `ishiftConf τ U` appears directly.

DERIVED: the `1` is the separation of the two mirrors; `4` is the dimension. -/
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

/-- **⭐⭐ THE NEXT REFLECTION IS THIS ONE AFTER A SHIFT.** Apply `ireflConf τ a` to both sides of
`ireflConf_comp_eq_shift` and cancel with `ireflConf_involutive`.

This is the same fact read the other way round, and reading it this way is what shows the two-
reflection route does not make translation invariance cheaper — see
`reflection_invariant_succ_iff_nu_T`.

DERIVED: the `1` is the mirror separation; `4` is the dimension. -/
theorem ireflConf_succ_eq_ireflConf_shift (τ : Fin 4) (a : ℤ) (U : IConf G) :
    ireflConf τ (a + 1) U = ireflConf τ a (ishiftConf τ U) := by
  rw [← ireflConf_comp_eq_shift τ a U, ireflConf_involutive τ a]

#print axioms ireflConf_succ_eq_ireflConf_shift

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


/-- **⭐⭐ ONE TRANSLATION IS TWO REFLECTIONS, ON OBSERVABLES.**

**⛔ THE CONSTANTS COME IN THE OTHER ORDER HERE, and that is not a typo.** `ireflObs` is
PRECOMPOSITION, and precomposition reverses composition: `ireflObs τ (a+1) (ireflObs τ a f)` evaluated
at `U` is `f (ireflConf τ a (ireflConf τ (a+1) U))`. So the LARGER constant is outermost on
observables and the SMALLER one is outermost on configurations, for the same forward shift.

DERIVED: the `1` is the mirror separation; `4` is the dimension. -/
theorem ireflObs_comp_eq_shiftObs (τ : Fin 4) (a : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ (a + 1) (ireflObs τ a f) = ishiftObsL τ f := by
  ext U
  show f (ireflConf τ a (ireflConf τ (a + 1) U)) = f (ishiftConf τ U)
  rw [ireflConf_comp_eq_shift]

#print axioms ireflObs_comp_eq_shiftObs

/-- **⭐⭐⭐ `nu_T` FROM REFLECTION INVARIANCE AT TWO ADJACENT CONSTANTS.**

`WilsonTransferReduction.transferData_of_state_facts` takes three facts about the state and this
supplies the third, `hnu : ∀ f, ν (ishiftObsL τ f) = ν f`, from reflection invariance at two
ADJACENT constants: translation invariance of a state IS reflection invariance twice.

**⛔ IT IS A RESTATEMENT, NOT A REDUCTION, AND `reflection_invariant_succ_iff_nu_T` PROVES THAT.**
Given invariance at `a`, invariance at `a + 1` and `hnu` are EQUIVALENT. So this theorem does not
make translation invariance cheaper, and no one should read it as discharging `hnu`. What it changes
is the KIND of statement the remaining obligation is: two reflection invariances, each of the form
`ReflectionHalfSpace.stateFree_reflection_invariant` already proved at finite volume for the even
constant, instead of one reflection statement and one translation statement with no finite-volume
counterpart at all.

The second constant is ODD, hence the LINK reflection — but `IsReflectionInvariant` is an EQUALITY,
so the `0 ≤ β` restriction that makes the odd reflection a separate problem for `ReflPositiveOn`
does not touch it.

**⛔ WHAT IS STILL OPEN.** Nothing here exhibits a Wilson state invariant under either reflection,
and no box family gives both at once — see `reflection_invariant_succ_iff_nu_T` for why a finite box
cannot be stable under both mirrors.

DERIVED: the `1` is the mirror separation; `4` is the dimension. -/
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

/-- **THE OBSERVABLE FORM OF `ireflConf_succ_eq_ireflConf_shift`.** Precomposition again reverses the
order: the shift ends up OUTERMOST on observables and innermost on configurations.

DERIVED: the `1` is the mirror separation; `4` is the dimension. -/
theorem ireflObs_succ_eq_shiftObs_ireflObs (τ : Fin 4) (a : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ (a + 1) f = ishiftObsL τ (ireflObs τ a f) := by
  ext U
  show f (ireflConf τ (a + 1) U) = f (ireflConf τ a (ishiftConf τ U))
  rw [ireflConf_succ_eq_ireflConf_shift]

#print axioms ireflObs_succ_eq_shiftObs_ireflObs

/-- **UNDOING A STEP AFTER TAKING IT IS DOING NOTHING, ON OBSERVABLES.** The partner of
`ishiftObsL_iunshiftObs`; both directions hold because `ishiftLink` is a bijection of the link set.

DERIVED: no numeral; `4` is the dimension. -/
theorem iunshiftObs_ishiftObsL (τ : Fin 4) (f : C(IConf G, ℝ)) :
    iunshiftObs τ (ishiftObsL τ f) = f := by
  ext U
  show f (ishiftConf τ (iunshiftConf τ U)) = f U
  rw [ishiftConf_iunshiftConf]

#print axioms iunshiftObs_ishiftObsL

/-- **THE PRECEDING REFLECTION IS THIS ONE UNSHIFTED.** `ireflObs_succ_eq_shiftObs_ireflObs` read
backwards, which needs the cancellation above.

DERIVED: the `1` is the mirror separation; `4` is the dimension. -/
theorem ireflObs_pred_eq_unshift (τ : Fin 4) (c : ℤ) (f : C(IConf G, ℝ)) :
    ireflObs τ (c - 1) f = iunshiftObs τ (ireflObs τ c f) := by
  have h : ireflObs τ c f = ishiftObsL τ (ireflObs τ (c - 1) f) := by
    have h0 := ireflObs_succ_eq_shiftObs_ireflObs τ (c - 1) f
    rwa [sub_add_cancel] at h0
  rw [h, iunshiftObs_ishiftObsL]

#print axioms ireflObs_pred_eq_unshift

/-- **⛔⛔ AND SO THE TWO-REFLECTION ROUTE IS AN EQUIVALENCE, NOT A REDUCTION.**

Given invariance at `a`, invariance at `a + 1` and `nu_T` imply each other. `←` is
`nu_T_of_reflection_invariant`; `→` is `ireflObs_succ_eq_shiftObs_ireflObs` followed by the
hypothesis. **So nothing about translation invariance has been made cheaper by writing it as two
reflections** — whoever supplies either one gets the other, and neither is supplied here.

**The obstruction is a theorem, not a remark.** `ReflectionHalfSpace.eq_empty_of_stable_two_mirrors`
proves that a finite box stable under the reflections at BOTH `a` and `a + 1` is empty — the two
mirrors compose to one link shift by `ireflLink_comp_succ`, and a `Finset` cannot contain an orbit of
it. So no single box family delivers both finite-volume invariances, and the route asks instead for
TWO families, one symmetric about each mirror, shown to have a common limit. That is the same
boundary-independence argument translation invariance needed in the first place.

It rules out one FINITE-VOLUME box statement serving both; it says nothing against some other route
to the odd-constant invariance that is not a box statement at all.

**What the route does buy** is that both halves are then statements of the SAME kind, each one
`ReflectionHalfSpace.stateFree_reflection_invariant` at its own constant, rather than one reflection
statement and one translation statement with no finite-volume counterpart at all.

DERIVED: the `1` is the mirror separation; `4` is the dimension. -/
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
