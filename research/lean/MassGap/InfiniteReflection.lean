import Mathlib
import MassGap.DLRLimit
import MassGap.Transfer

/-!
# MassGap.InfiniteReflection — reflection positivity on a submodule, and its transport to a limit

A `Transfer.TransferData` needs a symmetric bilinear form with `form_nonneg`, which is reflection
positivity. This module states that condition on a submodule, transports it and several related
inequalities from a family of states to a limit state, and builds the `Transfer.ReflForm` from the
result.

## Reflection positivity is asserted on a submodule

`0 ≤ ν (θF * F)` is false as a statement about all observables, for any reflection that moves
anything: `reflection_positivity_fails_off_the_half_space` shows that when `θF = -F` — as for an
antisymmetric observable such as `σ(x) - σ(θx)` — the quantity is `-ν (F * F)`, strictly negative
whenever `0 < ν (F * F)`.

`ReflPositiveOn R A ν` therefore quantifies over `f ∈ A` for a submodule `A` supplied by the caller.
`ReflectStrong.wilsonGibbsReflForm` is carried on `localObs (blkS τ a m) (blkR τ a m)` for the same
reason. The other direction is `trivialReflection_positive_always`: at `θ = id` the condition reads
`0 ≤ ν (f * f)` and holds for every state on every submodule, so the content lies entirely in which
submodule is chosen.

## The transport theorems

`DLRLimit.le_of_eventually_le` carries a lower bound through a limit: if `c ≤ μ i f` eventually then
`c ≤ ν f`. `reflPositive_of_eventually_pointwise` applies it at `c = 0` and the observable `θf * f`,
once per `f ∈ A`, and `reflPositive_of_tendsto` is the uniform form, which factors through the
pointwise one by `Filter.Eventually.mono`. `isReflectionInvariant_of_tendsto` transports invariance
by uniqueness of limits.

The hypotheses are pointwise in `f` rather than uniform because a directed union such as
`HalfSpaceAlgebra.halfSpaceAlg` has no single volume containing every member's support, while each
member separately has a fixed finite support and so sits inside every large enough box. The
submodule `A` is held fixed across the volumes in every statement.

`pairing_le_of_eventually_pointwise` and its variant `..._on` transport a ratio inequality
`ν (S.θ F * F) ≤ r^2 * ν (R.θ F * F)`. In that unsubtracted form, `F = 1` makes both sides `1` and
`r^2`, so a hypothesis quantified over all of `A` entails `1 ≤ r^2`;
`WilsonTransferReduction.gapAt_iff_pairing` restricts its inequality to `F` whose pairing with the
vacuum vanishes, and the `..._on` variant carries an arbitrary side condition `P` for that purpose.
`state_pairing_subtracted` is the identity
`ν (θ(F - νF • 1) * (F - νF • 1)) = ν (θF * F) - νF * ν (θF)`, whose right-hand side vanishes at
`F = 1`, and `connected_pairing_le_of_eventually` uses it to state a transport whose hypothesis
mentions only the finite-volume states, each subtracting its own mean.

## The form

`Reflection` bundles the four properties the construction consumes: `θ` is `ℝ`-linear,
multiplicative, unital and involutive. It refers to no lattice and no sites;
`MassGap.LatticeReflection` builds the instance for the infinite lattice and `MassGap.Reflect` is
the finite-volume original. `trivialReflection` shows the structure is inhabited.
`Reflection.theta_prod` extends multiplicativity to a `Finset.prod`.

`stateFormFun` is `⟨F, H⟩ = ν (θF * H)` on `↥A`, `stateFormFun_symm` its symmetry from involutivity,
multiplicativity and invariance, and `stateReflForm` the `Transfer.ReflForm ↥A` with every field
discharged from those plus `ReflPositiveOn`. `stateReflForm_vac_norm` gives `⟨1, 1⟩ = 1` when the
constant lies in `A`, which a submodule need not.

## Scope

`A`, `hinv` and `hpos` are hypotheses throughout. No half-space submodule of the infinite lattice is
constructed here, and no Wilson state is shown to satisfy `ReflPositiveOn` for one. The
`TransferData` fields `T_symm` and `T_contract` are not addressed in this module.

DERIVED: `0` is the sign asserted by `ReflPositiveOn` and the value the failure theorem's conclusion
falls below; `1` is the unit observable, which `θ_one` fixes and on which a state has value `1`; `2`
is the exponent on the caller's ratio `r`. No numeral is a magnitude.
-/

namespace MassGap.InfiniteReflection

open Filter MassGap.DLRLimit
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ## 1. What the form construction consumes -/

/-- A reflection on the observables of a compact space: an `ℝ`-linear map `θ : C(X,ℝ) →ₗ[ℝ] C(X,ℝ)`
that is multiplicative (`θ_mul`), fixes the constant (`θ_one`) and is involutive (`θ_involutive`).

These four fields are what `stateReflForm` consumes. No lattice, site or half-space appears in the
structure; `LatticeReflection.latticeReflection` is the instance for the infinite lattice, and
`trivialReflection` shows the structure is inhabited.

DERIVED: `1` is the unit observable that `θ_one` fixes, not a magnitude. -/
structure Reflection (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  /-- The reflection, as a linear map on observables. -/
  θ : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)
  /-- It respects the product — a reflection permutes coordinates, it does not mix them. -/
  θ_mul : ∀ f g : C(X, ℝ), θ (f * g) = θ f * θ g
  /-- It fixes the constant. -/
  θ_one : θ 1 = 1
  /-- Reflecting twice is doing nothing. -/
  θ_involutive : ∀ f : C(X, ℝ), θ (θ f) = f

/-- Reflection positivity of a state on a submodule: `0 ≤ ν (R.θ f * f)` for every `f ∈ A`. The
submodule is a parameter and not quantified away, since the condition is false when `A` is the whole
algebra — `reflection_positivity_fails_off_the_half_space`.

DERIVED: `0` is the sign asserted, not a threshold. -/
def ReflPositiveOn (R : Reflection X) (A : Submodule ℝ C(X, ℝ)) (ν : State X) : Prop :=
  ∀ f ∈ A, 0 ≤ ν (R.θ f * f)

/-- Invariance of a state under a reflection: `ν (R.θ f) = ν f` for every `f : C(X, ℝ)`. Unlike
`ReflPositiveOn`, this is asserted on the whole algebra, not on a submodule. It is what
`stateFormFun_symm` uses.

DERIVED: no numeral appears in the statement. -/
def IsReflectionInvariant (R : Reflection X) (ν : State X) : Prop :=
  ∀ f : C(X, ℝ), ν (R.θ f) = ν f

/-! ## 2. Why the condition is stated on a submodule -/

/-- `ν (R.θ F * F) < 0` whenever `R.θ F = -F` and `0 < ν (F * F)`. Rewriting by `hneg` makes the
product `(-1 : ℝ) • (F * F)`, and `ν.map_smul` turns the value into `-ν (F * F)`.

An antisymmetric observable such as `σ(x) - σ(θx)` satisfies `hneg` by construction, so
`∀ f, 0 ≤ ν (R.θ f * f)` over the whole algebra has no instance for a reflection that moves anything
and a state not concentrated on its fixed set. This is why `ReflPositiveOn` carries a submodule, and
why `ReflectStrong.wilsonGibbsReflForm` is built on `localObs (blkS τ a m) (blkR τ a m)`.

DERIVED: `0` is the sign in the hypothesis `0 < ν (F * F)` and the level the conclusion falls below.
The negation `θF = -F` is the caller's hypothesis. -/
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

/-- `R.θ (∏ i ∈ s, F i) = ∏ i ∈ s, R.θ (F i)` for any `Finset s` and family `F`. Since `θ_mul` and
`θ_one` are structure fields, `θ` is a monoid hom for the product on `C(X, ℝ)`; the proof is
`Finset.induction_on`.

A chessboard estimate works with a product over blocks rather than a factorisation `A * θA`, one
Schwarz step replacing it by quantities over doubled regions in which each block carries either
`F i` or its reflection; this is the distribution that step uses.

DERIVED: no numeral appears in the statement. -/
theorem Reflection.theta_prod (R : Reflection X) {ι : Type*} (s : Finset ι)
    (F : ι → C(X, ℝ)) : R.θ (∏ i ∈ s, F i) = ∏ i ∈ s, R.θ (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using R.θ_one
  · intro a s' ha ih
    rw [Finset.prod_insert ha, R.θ_mul, ih, Finset.prod_insert ha]

#print axioms Reflection.theta_prod


/-! ## 3. Transport to the limit state -/

/-- `ReflPositiveOn R A ν` from pointwise eventual positivity: given `htend`, convergence of
`μ i f` to `ν f` for every observable, and `h`, which for each `f ∈ A` gives
`0 ≤ μ i (R.θ f * f)` eventually along `l`. It is `DLRLimit.le_of_eventually_le` at `c = 0` and the
observable `R.θ f * f`, once per `f`.

The hypothesis is pointwise in `f`, which is what a directed union such as
`HalfSpaceAlgebra.halfSpaceAlg` can supply: no single volume contains every member's support, while
each member has a fixed finite support and so lies inside every large enough box. The submodule `A`
is fixed across the volumes, and the only condition on the filter is `NeBot`.

DERIVED: `0` is the sign being transported. -/
theorem reflPositive_of_eventually_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R : Reflection X) (A : Submodule ℝ C(X, ℝ))
    (h : ∀ f ∈ A, ∀ᶠ i in l, 0 ≤ μ i (R.θ f * f)) :
    ReflPositiveOn R A ν :=
  fun f hf => le_of_eventually_le htend (R.θ f * f) 0 (h f hf)

#print axioms reflPositive_of_eventually_pointwise

/-- `ReflPositiveOn R A ν` from the uniform hypothesis `∀ᶠ i in l, ReflPositiveOn R A (μ i)`. It
factors through `reflPositive_of_eventually_pointwise` by `Filter.Eventually.mono`, so it is the
special case in which one eventual set serves every `f ∈ A`.

DERIVED: no numeral appears in the statement; the sign being transported is inside
`ReflPositiveOn`. -/
theorem reflPositive_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (R : Reflection X) (A : Submodule ℝ C(X, ℝ))
    (h : ∀ᶠ i in l, ReflPositiveOn R A (μ i)) :
    ReflPositiveOn R A ν :=
  reflPositive_of_eventually_pointwise htend R A (fun f hf => h.mono fun _ hi => hi f hf)

#print axioms reflPositive_of_tendsto

/-- Transports the ratio inequality `ν (S.θ F * F) ≤ r ^ 2 * ν (R.θ F * F)` to the limit state, for
every `F ∈ A`, from the same inequality holding eventually at each `F` for the states `μ i`. Both
sides are the state at a fixed observable, so `le_of_tendsto_of_tendsto` applies.

The quantification is over all of `A`. At `F = 1` the two sides become `1` and `r ^ 2`, so a
hypothesis of this shape over the whole submodule entails `1 ≤ r ^ 2`, which
`TransferGap.gapAt_of_one_le_sq` makes a free conclusion;
`WilsonTransferReduction.gapAt_iff_pairing` restricts its inequality to `F` whose pairing with the
vacuum vanishes, and `pairing_le_of_eventually_pointwise_on` is the variant carrying such a
restriction. The hypothesis is pointwise in `F`, as in
`reflPositive_of_eventually_pointwise`.

DERIVED: `2` is the exponent on the caller's ratio `r`. -/
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

/-- `pairing_le_of_eventually_pointwise` with an arbitrary side condition `P : C(X, ℝ) → Prop`
carried through both hypothesis and conclusion. `P` is not used in the proof, so a caller may keep
any restriction — the vacuum-orthogonality one, for instance — across the limit.

DERIVED: `2` is the exponent on the caller's ratio `r`. -/
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

/-- The vacuum-subtracted pairing is the connected correlator:

    ν (R.θ (F - ν F • 1) * (F - ν F • 1)) = ν (R.θ F * F) - ν F * ν (R.θ F)

for any state, reflection and observable. An identity with no limit in it: `θ_one` and linearity
push the subtraction through `θ`, expanding the product leaves terms `-c * ν F` and `c ^ 2` with
`c = ν F`, and those cancel.

At `F = 1` the right-hand side is `1 - 1 * 1 = 0`, unlike the unsubtracted pairing, which is why
`connected_pairing_le_of_eventually` needs no side condition.

DERIVED: `1` is the unit observable, scaled by `ν F` and subtracted. -/
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

/-- Transports the connected ratio inequality to the limit state, with a hypothesis that mentions
only the finite-volume states: each `μ i` subtracts its own mean, so `h` reads
`μ i (S.θ F * F) - μ i F * μ i (S.θ F) ≤ r ^ 2 * (μ i (R.θ F * F) - μ i F * μ i (R.θ F))`
eventually, for each `F ∈ A`. The conclusion is the same inequality for `ν` written in the
vacuum-subtracted form, via `state_pairing_subtracted`.

Both sides are continuous functions of three convergent evaluations, so `le_of_tendsto_of_tendsto`
applies. `ν` does not occur in `h`, so the obligation the caller discharges is a finite-volume one.

DERIVED: `2` is the exponent on the caller's ratio `r`; `1` is the unit observable that the mean
subtraction scales. -/
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

/-- `IsReflectionInvariant R ν` from `IsReflectionInvariant R (μ i)` holding eventually along `l`.
Since the condition is an equality, `tendsto_nhds_unique` does the work: `μ i (R.θ f)` converges to
`ν (R.θ f)` by `htend`, and eventually equals `μ i f`, which converges to `ν f`.

DERIVED: no numeral appears in the statement. -/
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

/-- The reflection form of a state on a submodule: `⟨F, H⟩ = ν (R.θ F * H)`, defined on `↥A` by
coercing both arguments into `C(X, ℝ)`. No property of `A` beyond being a submodule is used at the
definition.

DERIVED: no numeral appears in the statement. -/
def stateFormFun (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (F H : A) : ℝ := ν (R.θ (F : C(X, ℝ)) * (H : C(X, ℝ)))

/-- `stateFormFun R ν A F H = stateFormFun R ν A H F` under `IsReflectionInvariant R ν`. The chain is
`ν (θF * H) = ν (θ (θF * H)) = ν (θθF * θH) = ν (F * θH) = ν (θH * F)`, using invariance,
`θ_mul`, `θ_involutive`, and commutativity of the product on `C(X, ℝ)`.

Invariance is needed and positivity is not; the hypothesis is exactly `hinv`.

DERIVED: no numeral appears in the statement. -/
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

/-- A `Transfer.ReflForm ↥A` built from a reflection `R`, a state `ν`, invariance `hinv` and
positivity `hpos`. `form` is `stateFormFun`, `form_symm` is `stateFormFun_symm`, `form_add_left` and
`form_smul_left` come from linearity of `θ` and of `ν`, and `form_nonneg` is `hpos` at the coerced
element together with its membership proof.

The carrier is `↥A`, matching `ReflectStrong.wilsonGibbsReflForm` on
`↥(localObs (blkS τ a m) (blkR τ a m))`, so `GNSHilbert` applies to the result: separated
completion, vacuum, and the operator lift. `X` is any compact topological space; no lattice appears.

DERIVED: the only numeral is the `2` of `F.2` in the `form_nonneg` field, the projection selecting a
subtype element's membership proof. -/
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

/-- `(stateReflForm R ν A hinv hpos).form ⟨1, hone⟩ ⟨1, hone⟩ = 1`, which is
`Transfer.TransferData.vac_norm` for this form. The proof is `θ_one`, `mul_one` and `ν.map_one`.

The hypothesis `hone : (1 : C(X, ℝ)) ∈ A` is required: a submodule of observables need not contain
the constant, and `GNSHilbert`'s vacuum is that constant.

DERIVED: the `1`s are the unit observable, twice as the form's arguments, and the value a state
takes on it. -/
theorem stateReflForm_vac_norm (R : Reflection X) (ν : State X) (A : Submodule ℝ C(X, ℝ))
    (hinv : IsReflectionInvariant R ν) (hpos : ReflPositiveOn R A ν)
    (hone : (1 : C(X, ℝ)) ∈ A) :
    (stateReflForm R ν A hinv hpos).form ⟨1, hone⟩ ⟨1, hone⟩ = 1 := by
  show ν (R.θ (1 : C(X, ℝ)) * (1 : C(X, ℝ))) = 1
  rw [R.θ_one, mul_one, ν.map_one]

#print axioms stateReflForm_vac_norm

/-! ## 5. The two extremes of the condition -/

/-- The identity map as a `Reflection X`: all four fields hold by `rfl`. It shows the structure is
inhabited. The form it produces is `ν (F * H)`, with no half-space structure, and
`trivialReflection_positive_always` shows the positivity condition is then automatic.

DERIVED: no numeral appears in the statement; the `1` of `θ_one` is the unit observable, fixed by
the identity. -/
def trivialReflection (X : Type*) [TopologicalSpace X] [CompactSpace X] : Reflection X where
  θ := LinearMap.id
  θ_mul _ _ := rfl
  θ_one := rfl
  θ_involutive _ := rfl

#print axioms trivialReflection

/-- `ReflPositiveOn (trivialReflection X) A ν` for every state `ν` and every submodule `A`. With
`θ = id` the condition reads `0 ≤ ν (f * f)`, which follows from positivity of the state at the
pointwise nonnegative `f * f`.

So this instance constrains neither the state nor the submodule. Together with
`reflection_positivity_fails_off_the_half_space` it brackets the condition: automatic at the trivial
reflection, false on the whole algebra for a reflection that moves anything, with the content in
which submodule is chosen.

DERIVED: no numeral appears in the statement; the sign `0` is inside `ReflPositiveOn`. -/
theorem trivialReflection_positive_always (ν : State X) (A : Submodule ℝ C(X, ℝ)) :
    ReflPositiveOn (trivialReflection X) A ν := by
  intro f _
  show 0 ≤ ν (f * f)
  refine ν.nonneg _ (fun x => ?_)
  show 0 ≤ f x * f x
  nlinarith [sq_nonneg (f x)]

#print axioms trivialReflection_positive_always

end MassGap.InfiniteReflection
