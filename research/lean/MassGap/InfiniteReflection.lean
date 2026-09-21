import Mathlib
import MassGap.DLRLimit
import MassGap.Transfer

/-!
# MassGap.InfiniteReflection — reflection positivity is not lost in the thermodynamic limit

## What this is for

`InfiniteShift` puts a non-trivial, infinite-order time translation on the infinite lattice's
quasi-local algebra, which is what every finite carrier was proved to lack. What a
`Transfer.TransferData` still needs there is the FORM: a symmetric bilinear `⟨·,·⟩` with
`form_nonneg`, which is reflection positivity.

At finite volume that is `Complete.wilson_reflection_positive_at`, one of the tree's two named
axioms. **The question here is whether passing to the infinite volume costs anything beyond it, and
the answer is no.**

## ⚠ FIRST: reflection positivity is a statement about ONE HALF-SPACE

`0 ≤ ν(θF · F)` is **false** as a statement about all observables, for any reflection that moves
anything. `reflection_positivity_fails_off_the_half_space` proves it: whenever `θF = −F` — and an
antisymmetric observable like `σ(x) − σ(θx)` is one — the quantity is `−ν(F·F) ≤ 0`, and strictly
negative as soon as `ν(F·F) > 0`.

So the condition is asserted **on a submodule**, and the caller supplies it. That is not a technical
nicety: it is why `ReflectStrong.wilsonGibbsReflForm` is built on
`localObs (blkS τ a m) (blkR τ a m)` and not on the whole Wilson algebra. Stating the condition
unrestricted would make every theorem below vacuous — true of a hypothesis nothing satisfies — and
`reflection_positivity_fails_off_the_half_space` is here so that cannot happen silently.

## The transport, and it is three lines

`DLRLimit.le_of_eventually_le` says a uniform lower bound passes to the limit: if `c ≤ μ i f`
eventually then `c ≤ ν f`. Reflection positivity IS such a bound, at `c = 0` and the observable
`θF · F`, for each `F` in the half-space submodule. So `reflPositive_of_tendsto` is that lemma
applied once per observable, and reflection invariance transports through uniqueness of limits.

**Nothing there is deep and that is the point.** Positivity is a closed condition and limits preserve
closed conditions. The reason to write it down is that "does RP survive the limit" was open in the
goal document, and the answer changes what C1 still needs.

## What a reflection has to be

`Reflection` bundles the four properties the form construction consumes — `θ` is `ℝ`-linear,
multiplicative, unital and involutive. It is deliberately NOT tied to a lattice: the transport
argument never looks at what `θ` does to a site. `MassGap.LatticeReflection` builds the instance for
the infinite lattice; `MassGap.Reflect` is the finite-volume original the convention comes from.

## What is delivered

* `reflection_positivity_fails_off_the_half_space` — the restriction is necessary, not decorative.
* `reflPositive_of_tendsto` — RP on a submodule passes to any limit state. **No new axiom.**
* `isReflectionInvariant_of_tendsto` — so does invariance of the state.
* `stateReflForm` — given both, the state's reflection form is a `Transfer.ReflForm` **on that
  submodule**, so `GNSHilbert`'s apparatus applies: Hilbert space, vacuum, operator lift.
* `stateReflForm_vac_norm` — the constant observable is normalised, when it lies in the submodule.

## ⚠ What is NOT delivered

**No half-space submodule of the infinite lattice is constructed here**, and no Wilson state is shown
to satisfy `ReflPositiveOn` for one. Until both exist, nothing below applies to Yang–Mills: these are
theorems about a hypothesis, and supplying the hypothesis is the work that remains.

**And the transfer operator's own fields are untouched.** `TransferData` also needs `T_symm` and
`T_contract` for `InfiniteShift.ishiftObs` against this form, and `T_symm` is where the reflection
and the shift must be shown compatible — the step that makes reflection positivity do its work.

So C1's remaining list is more specific, not shorter: the limit is no longer one of its items, and
the half-space algebra has become one.
-/

namespace MassGap.InfiniteReflection

open Filter MassGap.DLRLimit
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ## 1. What the form construction consumes -/

/-- **A REFLECTION ON THE OBSERVABLES**: linear, multiplicative, unital, involutive.

These four are what `stateReflForm` uses and nothing more. No lattice, no sites and no half-space
appear — `LatticeReflection.latticeReflection` is the instance, and keeping the shape abstract is
what lets the transport theorem be proved without any of that.

DERIVED: the `1` is the unit observable, not a magnitude. -/
structure Reflection (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  /-- The reflection, as a linear map on observables. -/
  θ : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)
  /-- It respects the product — a reflection permutes coordinates, it does not mix them. -/
  θ_mul : ∀ f g : C(X, ℝ), θ (f * g) = θ f * θ g
  /-- It fixes the constant. -/
  θ_one : θ 1 = 1
  /-- Reflecting twice is doing nothing. -/
  θ_involutive : ∀ f : C(X, ℝ), θ (θ f) = f

/-- **REFLECTION POSITIVITY, ON A SUBMODULE.** `A` is the half-space algebra: the observables the
condition is asserted of. It is a parameter because the condition is FALSE without it — see
`reflection_positivity_fails_off_the_half_space`.

DERIVED: the `0` is the sign asserted, not a threshold. -/
def ReflPositiveOn (R : Reflection X) (A : Submodule ℝ C(X, ℝ)) (ν : State X) : Prop :=
  ∀ f ∈ A, 0 ≤ ν (R.θ f * f)

/-- **THE STATE DOES NOT SEE THE REFLECTION.** Needed for symmetry of the form, and true of any state
built from a reflection-symmetric measure. Asserted on all observables, where — unlike positivity —
it is the honest statement.

DERIVED: no numeral. -/
def IsReflectionInvariant (R : Reflection X) (ν : State X) : Prop :=
  ∀ f : C(X, ℝ), ν (R.θ f) = ν f

/-! ## 2. ⛔ Why the submodule is not optional -/

/-- **⛔ UNRESTRICTED REFLECTION POSITIVITY IS FALSE.**

If the reflection negates an observable — and an antisymmetric one like `σ(x) − σ(θx)` is negated by
construction — then `ν(θF · F) = −ν(F·F)`, which is at most zero and is strictly negative as soon as
`F` has positive second moment.

**So `∀ f, 0 ≤ ν(θf · f)` is not a strong hypothesis; it is an unsatisfiable one**, for every
reflection that moves anything and every state that is not concentrated on the reflection's fixed
set. A file asserting it would prove theorems about an empty class, and this is the guard against
that: reflection positivity is a statement about observables supported in ONE HALF-SPACE, which is
why `ReflectStrong.wilsonGibbsReflForm` is carried on `localObs (blkS τ a m) (blkR τ a m)` and not on
the Wilson algebra entire.

DERIVED: the `0` is the sign; the negation is `θF = −F`, the caller's hypothesis. -/
theorem reflection_positivity_fails_off_the_half_space (R : Reflection X) (ν : State X)
    {F : C(X, ℝ)} (hneg : R.θ F = -F) (hpos : 0 < ν (F * F)) :
    ν (R.θ F * F) < 0 := by
  rw [hneg]
  have : (-F) * F = (-1 : ℝ) • (F * F) := by
    ext x
    simp
  rw [this, ν.map_smul]
  linarith

#print axioms reflection_positivity_fails_off_the_half_space

/-! ## 3. ⭐ Both conditions transport to the limit -/

/-- **⭐⭐ REFLECTION POSITIVITY PASSES TO THE LIMIT STATE, ONE OBSERVABLE AT A TIME.**

`DLRLimit.le_of_eventually_le` at `c = 0` and the observable `θf · f`, once per `f` in the submodule.
Positivity is a closed condition and limits preserve closed conditions; there is nothing else in it.

**So the infinite volume costs no new positivity assumption.** Whatever supplies reflection
positivity at finite volume — at Wilson, `Complete.wilson_reflection_positive_at` — supplies it for
the limit, with no second axiom and no hypothesis on the filter beyond `NeBot`.

**⛔ THE HYPOTHESIS IS POINTWISE IN `f`, AND THAT IS WHAT REACHES A DIRECTED UNION.** The uniform
form `∀ᶠ i, ∀ f ∈ A` is `reflPositive_of_tendsto` below, and it is the special case, because this
proof specialises at `f` immediately and never uses uniformity over `f`.
`HalfSpaceAlgebra.halfSpaceAlg` is the union over ALL finite supports inside the half-space, so no
single volume contains every member's support and the uniform hypothesis is unsatisfiable by an
exhausting family — which is why the union looked unreachable. Each member separately carries a
FIXED finite support and therefore sits inside every large enough box.

The submodule `A` is held FIXED across the volumes either way: a half-space algebra that GREW with
the volume would not have a limit to transport to.

DERIVED: the `0` is the sign being transported. -/
theorem reflPositive_of_eventually_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R : Reflection X) (A : Submodule ℝ C(X, ℝ))
    (h : ∀ f ∈ A, ∀ᶠ i in l, 0 ≤ μ i (R.θ f * f)) :
    ReflPositiveOn R A ν :=
  fun f hf => le_of_eventually_le htend (R.θ f * f) 0 (h f hf)

#print axioms reflPositive_of_eventually_pointwise

/-- **⭐ THE UNIFORM FORM**, which is what a family of volumes each positive on all of `A` supplies.
It factors through the pointwise lemma by `Filter.Eventually.mono`, so the two are one fact.

DERIVED: the `0` is the sign being transported. -/
theorem reflPositive_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R : Reflection X) (A : Submodule ℝ C(X, ℝ))
    (h : ∀ᶠ i in l, ReflPositiveOn R A (μ i)) :
    ReflPositiveOn R A ν :=
  reflPositive_of_eventually_pointwise htend R A (fun f hf => h.mono fun _ hi => hi f hf)

#print axioms reflPositive_of_tendsto

/-- **⭐⭐⭐ A PAIRING INEQUALITY PASSES TO THE LIMIT STATE.**

Both sides are the state evaluated at a fixed observable, so both converge; a `≤` holding eventually
is a `≤` in the limit. Nothing here is deep — the point is which obligation it moves.

**⛔ THIS FORM IS UNUSABLE FOR THE GAP AND THE VARIANT BELOW IS THE ONE TO USE.**
`WilsonTransferReduction.gapAt_iff_pairing` restricts its inequality to the `F` whose pairing with
the vacuum VANISHES, and that restriction is not decoration: at `F = 1` both sides collapse to `1`
and `r²`, so an unrestricted hypothesis of this shape entails `1 ≤ r²` and
`TransferGap.gapAt_of_one_le_sq` then makes the conclusion free. Quantifying over all of `A` throws
away the whole content.

The hypothesis is pointwise in `F` for the same reason it is in
`reflPositive_of_eventually_pointwise`: a directed union has no single volume containing every
member's support, so a uniform hypothesis would be unsatisfiable by an exhausting family.

DERIVED: the `2` is the exponent on the caller's ratio `r`; no numeral is chosen. -/
theorem pairing_le_of_eventually_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R S : Reflection X) (A : Submodule ℝ C(X, ℝ)) (r : ℝ)
    (h : ∀ F ∈ A, ∀ᶠ i in l, μ i (S.θ F * F) ≤ r ^ 2 * μ i (R.θ F * F)) :
    ∀ F ∈ A, ν (S.θ F * F) ≤ r ^ 2 * ν (R.θ F * F) := by
  intro F hF
  exact le_of_tendsto_of_tendsto (htend (S.θ F * F))
    ((htend (R.θ F * F)).const_mul (r ^ 2)) (h F hF)

#print axioms pairing_le_of_eventually_pointwise

/-- **⭐ THE SAME, ON A SUBSET OF THE ALGEBRA.** The side condition `P` rides along untouched, which
is what lets a caller keep the vacuum-orthogonality restriction that makes the statement non-empty.

DERIVED: the `2` is the exponent on the caller's ratio `r`; no numeral is chosen. -/
theorem pairing_le_of_eventually_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R S : Reflection X) (A : Submodule ℝ C(X, ℝ)) (P : C(X, ℝ) → Prop) (r : ℝ)
    (h : ∀ F ∈ A, P F → ∀ᶠ i in l, μ i (S.θ F * F) ≤ r ^ 2 * μ i (R.θ F * F)) :
    ∀ F ∈ A, P F → ν (S.θ F * F) ≤ r ^ 2 * ν (R.θ F * F) := by
  intro F hF hP
  exact le_of_tendsto_of_tendsto (htend (S.θ F * F))
    ((htend (R.θ F * F)).const_mul (r ^ 2)) (h F hF hP)

#print axioms pairing_le_of_eventually_pointwise_on

/-- **⭐⭐ THE VACUUM-SUBTRACTED PAIRING IS THE CONNECTED CORRELATOR.**

    ν (θ (F - ν F • 1) · (F - ν F • 1)) = ν (θ F · F) - ν F · ν (θ F)

An identity, per state, with no limit in it. Expanding the product leaves `- c·νF + c²` with
`c = ν F`, and those cancel.

**⛔ THIS IS WHY THE SUBTRACTED STATEMENT HAS NO SIDE CONDITION.** The right-hand side is the
connected two-point function; at `F = 1` it is `1 - 1 · 1 = 0`, so the collapse that makes an
unsubtracted decay hypothesis contradictory simply does not arise.

DERIVED: no numeral is chosen; the `1` is the unit observable. -/
theorem state_pairing_subtracted (ν : State X) (R : Reflection X) (F : C(X, ℝ)) :
    ν (R.θ (F - ν F • (1 : C(X, ℝ))) * (F - ν F • (1 : C(X, ℝ))))
      = ν (R.θ F * F) - ν F * ν (R.θ F) := by
  have hθ : R.θ (F - ν F • (1 : C(X, ℝ))) = R.θ F - ν F • (1 : C(X, ℝ)) := by
    rw [map_sub, map_smul, R.θ_one]
  rw [hθ]
  have hexp : (R.θ F - ν F • (1 : C(X, ℝ))) * (F - ν F • (1 : C(X, ℝ)))
      = R.θ F * F - ν F • R.θ F - ν F • F + (ν F * ν F) • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [hexp, ν.map_add, ν.map_sub, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_smul, ν.one']
  ring

#print axioms state_pairing_subtracted

/-- **⭐⭐⭐ AND SO THE HYPOTHESIS NEED NOT MENTION THE LIMIT STATE AT ALL.**

Each volume subtracts ITS OWN mean. Both sides are then continuous functions of three convergent
evaluations, so a `≤` holding eventually is a `≤` between the limits — and by
`state_pairing_subtracted` those limits are the limit state's subtracted pairings.

**⛔ SO THE OBLIGATION IS PURELY FINITE-VOLUME.** No `ν` appears in `h`. That is what the previous
form could not do: its side condition selected observables by a property of the limit state.

DERIVED: the `2` is the exponent on the caller's ratio `r`; no numeral is chosen. -/
theorem connected_pairing_le_of_eventually {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R S : Reflection X) (A : Submodule ℝ C(X, ℝ)) (r : ℝ)
    (h : ∀ F ∈ A, ∀ᶠ i in l,
      μ i (S.θ F * F) - μ i F * μ i (S.θ F)
        ≤ r ^ 2 * (μ i (R.θ F * F) - μ i F * μ i (R.θ F))) :
    ∀ F ∈ A,
      ν (S.θ (F - ν F • (1 : C(X, ℝ))) * (F - ν F • (1 : C(X, ℝ))))
        ≤ r ^ 2 * ν (R.θ (F - ν F • (1 : C(X, ℝ))) * (F - ν F • (1 : C(X, ℝ)))) := by
  intro F hF
  rw [state_pairing_subtracted, state_pairing_subtracted]
  refine le_of_tendsto_of_tendsto ?_ ?_ (h F hF)
  · exact (htend _).sub ((htend _).mul (htend _))
  · exact ((htend _).sub ((htend _).mul (htend _))).const_mul _

#print axioms connected_pairing_le_of_eventually

/-- **AND SO DOES INVARIANCE.** An equality rather than an inequality, so uniqueness of limits does
the work in place of `ge_of_tendsto`.

DERIVED: no numeral. -/
theorem isReflectionInvariant_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R : Reflection X) (h : ∀ᶠ i in l, IsReflectionInvariant R (μ i)) :
    IsReflectionInvariant R ν := by
  intro f
  have h1 : Tendsto (fun i => μ i (R.θ f)) l (𝓝 (ν (R.θ f))) := htend (R.θ f)
  have h2 : Tendsto (fun i => μ i (R.θ f)) l (𝓝 (ν f)) :=
    (htend f).congr' (h.mono fun i hi => (hi f).symm)
  exact tendsto_nhds_unique h1 h2

#print axioms isReflectionInvariant_of_tendsto

/-! ## 4. The form on the half-space algebra, and it is a `Transfer.ReflForm` -/

/-- The reflection form of a state, on the half-space algebra: `⟨F, H⟩ = ν(θF · H)`.

DERIVED: no numeral. -/
def stateFormFun (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (F H : A) : ℝ := ν (R.θ (F : C(X, ℝ)) * (H : C(X, ℝ)))

/-- **THE FORM IS SYMMETRIC**, from involutivity, multiplicativity and invariance together:
`ν(θF·H) = ν(θ(θF·H)) = ν(F·θH) = ν(θH·F)`, the last step because observables commute.

DERIVED: no numeral. -/
theorem stateFormFun_symm (R : Reflection X) {ν : State X} (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (F H : A) :
    stateFormFun R ν A F H = stateFormFun R ν A H F := by
  unfold stateFormFun
  calc ν (R.θ (F : C(X, ℝ)) * (H : C(X, ℝ)))
      = ν (R.θ (R.θ (F : C(X, ℝ)) * (H : C(X, ℝ)))) := (hinv _).symm
    _ = ν (R.θ (R.θ (F : C(X, ℝ))) * R.θ (H : C(X, ℝ))) := by rw [R.θ_mul]
    _ = ν ((F : C(X, ℝ)) * R.θ (H : C(X, ℝ))) := by rw [R.θ_involutive]
    _ = ν (R.θ (H : C(X, ℝ)) * (F : C(X, ℝ))) := by rw [mul_comm]

#print axioms stateFormFun_symm

/-- **⭐ THE STATE'S REFLECTION FORM IS A `Transfer.ReflForm` ON THE HALF-SPACE ALGEBRA.**

Every field is discharged from the four properties of `Reflection` plus invariance and positivity of
the state. So `GNSHilbert` — the separated completion, the vacuum, `opT` with its contraction and
self-adjointness — applies to any reflection-positive state on any compact observable space, with no
lattice in sight.

The carrier is `↥A`, matching `ReflectStrong.wilsonGibbsReflForm`, which is carried on
`↥(localObs (blkS τ a m) (blkR τ a m))` for exactly this reason.

DERIVED: no numeral. -/
noncomputable def stateReflForm (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν) :
    MassGap.Transfer.ReflForm ↥A where
  form F H := stateFormFun R ν A F H
  form_symm F H := stateFormFun_symm R A hinv F H
  form_add_left F G H := by
    show ν (R.θ ((F : C(X, ℝ)) + (G : C(X, ℝ))) * (H : C(X, ℝ)))
      = ν (R.θ (F : C(X, ℝ)) * (H : C(X, ℝ))) + ν (R.θ (G : C(X, ℝ)) * (H : C(X, ℝ)))
    rw [map_add, add_mul, ν.map_add]
  form_smul_left r F H := by
    show ν (R.θ (r • (F : C(X, ℝ))) * (H : C(X, ℝ)))
      = r * ν (R.θ (F : C(X, ℝ)) * (H : C(X, ℝ)))
    rw [map_smul, smul_mul_assoc, ν.map_smul]
  form_nonneg F := hpos (F : C(X, ℝ)) F.2

#print axioms stateReflForm

/-- **THE VACUUM IS NORMALISED** — `⟨1,1⟩ = 1`, which is `Transfer.TransferData.vac_norm`, settled
outright rather than assumed, provided the constant lies in the half-space algebra.

That proviso is real and is why it is a hypothesis: a submodule of observables need not contain the
constant, and `GNSHilbert`'s vacuum is that constant.

DERIVED: the `1`s are the constant observable and the total mass of a state, from `θ_one` and
`State.map_one`. -/
theorem stateReflForm_vac_norm (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (hone : (1 : C(X, ℝ)) ∈ A) :
    (stateReflForm R ν A hinv hpos).form ⟨1, hone⟩ ⟨1, hone⟩ = 1 := by
  show ν (R.θ (1 : C(X, ℝ)) * (1 : C(X, ℝ))) = 1
  rw [R.θ_one, mul_one, ν.map_one]

#print axioms stateReflForm_vac_norm

/-! ## 5. Anti-vacuity, in both directions -/

/-- **THE IDENTITY IS A REFLECTION**, so `Reflection` is inhabited. It is degenerate — the form it
gives is `ν(F·H)`, with no half-space structure — and it is here only to show the structure is
satisfiable.

DERIVED: the `1` is the unit observable; nothing is chosen. -/
def trivialReflection (X : Type*) [TopologicalSpace X] [CompactSpace X] : Reflection X where
  θ := LinearMap.id
  θ_mul _ _ := rfl
  θ_one := rfl
  θ_involutive _ := rfl

#print axioms trivialReflection

/-- **AND AT THE TRIVIAL REFLECTION THE CONDITION IS EMPTY.** With `θ = id` it reads `0 ≤ ν(f·f)`,
which every state satisfies on every submodule — so that instance constrains nothing and is not
evidence that `ReflPositiveOn` is satisfiable in any useful sense.

Stated so `trivialReflection` cannot be mistaken for a witness. Read together with
`reflection_positivity_fails_off_the_half_space`, the two bracket the condition: trivial on one side,
false on the other, and the content is entirely in which submodule is chosen.

DERIVED: the `0` is the sign; nothing is chosen. -/
theorem trivialReflection_positive_always (ν : State X) (A : Submodule ℝ C(X, ℝ)) :
    ReflPositiveOn (trivialReflection X) A ν := by
  intro f _
  show 0 ≤ ν (f * f)
  refine ν.nonneg _ (fun x => ?_)
  show 0 ≤ f x * f x
  nlinarith [sq_nonneg (f x)]

#print axioms trivialReflection_positive_always

end MassGap.InfiniteReflection
