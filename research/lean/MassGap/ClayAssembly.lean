import Mathlib
import MassGap.MomentShape
import MassGap.GNSHilbert
import MassGap.LatticeTranslNoGo
import MassGap.LagTwoSix
import MassGap.CompactBeta
import MassGap.WeakArm
import MassGap.LagTwoEight

/-!
# MassGap.ClayAssembly — two hypotheses as a structure, and facts about what they do and do not give

`ClayRemaining` is a structure with two fields, each a `Prop` stated against named objects rather
than against a model or an opaque predicate:

* `I1_lagTwo` — a constant `K` with `0 < K < LagTwoSix.lagTwoThresholdSix` bounding the lag-two ratio
  of `wilsonCorrAt 5` at every `β ≥ 0`.
* `I2_clustering` — one constant `L` making `MassGap.d2At N` Lipschitz in `β`, at every aperture `N`.

`lagTwoRatioSix_of_clayRemaining` shows the first field is `LagTwoSix.LagTwoRatioSix` with an extra
`0 < K` conjunct, and `flagship_of_clayRemaining` carries it through
`LagTwoSix.confines_of_lagTwoRatioSix` to `ApertureRoute.FlagshipAt`. `I2_clustering` has no consumer
here.

## Facts about a fixed extent

`corr_at_max_lag_eq_lag_one` proves `ρ(N) = ρ(1)` at every aperture `N ≥ 1` and every real coupling:
`Moment.circLag ⟨N⟩ = min N 1 = 1 = circLag ⟨1⟩`, and
`MomentShape.wilsonCorrAt_circLag_congr` carries the values across.
`no_fixed_extent_decay_past_half_period` and `I1_is_not_clustering` are the same fact restated. So no
statement of the form "the correlation is below `ε` beyond separation `r`" holds at fixed extent with
`r` past the half period, whatever `ε` is.

`hilbert_space_half_of_C1_is_proved` records unconditionally that `GNSHilbert.ymOmega` is a unit
vector and `GNSHilbert.ymH` is nontrivial.

## The transfer operator

`TransferMovesSomething D` is `∃ x, GNSHilbert.opT D x ≠ x`. Two sufficient conditions:
`transferMovesSomething_of_seminorm_ne_zero`, from a nonzero seminorm of `cT z - z`, and
`transferMovesSomething_of_pairing_ne`, from one pairing that differs between `T z` and `z`. Neither
is a characterisation; the converses are not stated.

`form_iterate_antitone`, `finite_order_contraction_is_isometry` and its `pow` form, and
`no_decay_of_finite_order` show that on a `TransferData` finite order plus contractivity forces the
form to be preserved, so such a `T` is an isometry of the form and admits no geometric decay factor.
`HalfLineTransfer.shiftObs_pow_period` supplies that hypothesis on the periodic lattice.
`HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` shows the hypothesis fails on `ℤ⁴` given a
separating function on the group, which `HaarVariance.reTr_flipEl_ne_reTr_one` supplies at every
`SU (m+2)` and not below.

## Facts about the two candidate hypotheses

`scaling_as_stated_is_vacuous` exhibits `exp(−β)` satisfying "a positive function tending to zero",
so that statement is discharged without reference to a lattice or a gauge group.
`MassGap.AsymptoticScaling` states the version tying `a(β)` to a lattice mass.

`summable_clustering_is_weaker_than_a_gap` and `bounded_second_moment_clustering_is_weaker_than_a_gap`
exhibit `1/(d+1)²` and `1/(d+1)⁴`: nonnegative, with the stated summability, and dominated by no
geometric profile. So summability, and summability of the second moment, each hold of profiles no
geometric bound covers.

`CompactBeta.profile_to_moment_not_uniformly_lipschitz` shows that a volume-free bound on individual
correlators does not give `I2_clustering`, the lost factor being `((N+1)/2)²`, because
`d2At N β = ∑_d p_d · circLag(d)²` weights each lag by the square of its circle distance.

`flat_profile_admits_no_uniform_quartic_constant` refutes `∃ C ≥ 0, ∀ m ≥ 1, 1 ≤ C/m⁴`, by
`WeakArm.exists_lag_halving`. So an argument that never reads a profile's decay cannot produce a
uniform quartic constant, the flat profile being a counterexample.

`coreRate_lt_one_forces_small_beta` proves `coreRate K β < 1` forces `β < 0.12` at every `K`, because
`coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}` carries `e^{2β}−1` as a factor and the other two factors are
at least one.

`I2_needs_clustering_not_the_extensive_bound` restates
`CompactBeta.clay_covariance_constant_not_aperture_uniform`: for every candidate constant there is an
aperture at which `4M·#Plaq` exceeds it.

## Scope

Every theorem here is foundational-only. The structure type `ClayRemaining` is not: `I2_clustering`
quantifies over every aperture `N`, and `MassGap.d2At N β` at general `N` routes through
`Complete.wilson_reflection_positive_at`, while the proved version
`Complete.wilson_reflection_positive_at_even` covers even extent at least four. So
`flagship_of_clayRemaining` and `lagTwoRatioSix_of_clayRemaining` carry that axiom through the
structure, although `LagTwoSix.confines_extent_six_of_lag_two_ratio` — the route they run through —
is itself foundational-only, spending the proved `wilson_reflection_positive_at_even 5 3`.

Build: `python research/code/lean_build.py build MassGap.ClayAssembly`.
-/

namespace MassGap.ClayAssembly

open Filter

/-! ## 1. The correlation at the largest lag -/

/-- `wilsonCorrAt N β ⟨N⟩ = wilsonCorrAt N β ⟨1⟩` at every aperture `N ≥ 1` and every real coupling.
`Moment.circLag d = min d (N+1−d)`, so `circLag ⟨N⟩ = min N 1 = 1 = circLag ⟨1⟩`, and
`MomentShape.wilsonCorrAt_circLag_congr` carries the values across.

So on a periodic lattice the largest lag carries the lag-one value. A decay statement past the half
period is therefore not available at fixed extent; `Complete.ym_wilson_decay_to_half_period` reaches
the same point from the spectral side.

DERIVED: no numeral is chosen. `1` is the lower bound on `N` in `hN` and the lag whose circle
distance the largest lag shares — the two coincide, since `min N 1 = 1` exactly when `1 ≤ N` — and
`N` is the largest element of `Fin (N + 1)`. -/
theorem corr_at_max_lag_eq_lag_one (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    MassGap.wilsonCorrAt N β ⟨N, Nat.lt_succ_self N⟩
      = MassGap.wilsonCorrAt N β ⟨1, Nat.lt_succ_of_le hN⟩ := by
  refine MassGap.MomentShape.wilsonCorrAt_circLag_congr N β ?_
  show Moment.circLag (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
      = Moment.circLag (⟨1, Nat.lt_succ_of_le hN⟩ : Fin (N + 1))
  unfold Moment.circLag
  simp only []
  omega

/-- `¬ (wilsonCorrAt N β ⟨N⟩ < wilsonCorrAt N β ⟨1⟩)` at every aperture `N ≥ 1` and every real
coupling: `corr_at_max_lag_eq_lag_one` and `lt_irrefl`.

So the correlation is never smaller at the largest lag than at lag one, by any margin.

DERIVED: `1` is `corr_at_max_lag_eq_lag_one`'s — the lower bound on `N` and the lag compared
against. -/
theorem no_fixed_extent_decay_past_half_period (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    ¬ (MassGap.wilsonCorrAt N β ⟨N, Nat.lt_succ_self N⟩
        < MassGap.wilsonCorrAt N β ⟨1, Nat.lt_succ_of_le hN⟩) := by
  rw [corr_at_max_lag_eq_lag_one N hN β]
  exact lt_irrefl _

/-! ## 2. The half of C1 that is proved, restated so the structure need not carry it -/

/-- `‖GNSHilbert.ymOmega …‖ = 1` and `Nontrivial (GNSHilbert.ymH …)`, at `N ≠ 0`, even extent
`n = 2 * m` with `0 < m`, and every real `β`. The conjunction of `GNSHilbert.ymOmega_norm` and
`GNSHilbert.nontrivial_ymH`.

`ymH` is a complete complex inner-product space built from
`ReflectionStrong.wilsonGibbsReflForm`. No condition on the coupling.

DERIVED: `0` is the value `N` is required to differ from in `hN` and the strict lower bound on `m` in
`hm0`. `2` in `hm : n = 2 * m` is the reflection geometry's. `1` is the norm asserted of the vacuum,
`ymOmega_norm`'s normalisation. -/
theorem hilbert_space_half_of_C1_is_proved {d n N : ℕ} [NeZero n]
    (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    ‖MassGap.GNSHilbert.ymOmega hN τ a m hm hm0 β‖ = 1
      ∧ Nontrivial (MassGap.GNSHilbert.ymH hN τ a m hm hm0 β) :=
  ⟨MassGap.GNSHilbert.ymOmega_norm hN τ a m hm hm0 β,
    MassGap.GNSHilbert.nontrivial_ymH hN τ a m hm hm0 β⟩

/-- The `Prop` `∃ x : GNSHilbert.H D.toReflForm, GNSHilbert.opT D x ≠ x`: the operator induced by a
`TransferData` moves some vector of the GNS space.

Written so that the identity operator fails it. `GNSHilbert.ym_target_discharged_trivially` builds
`trivialTransfer`, an unconditional `TransferData` on the Wilson slab algebra discharging every
clause of "Hilbert space, unit vacuum, positive self-adjoint contraction with `TΩ = Ω`", together
with a sixth conjunct saying `T` is the identity.

On a periodic carrier every such operator fails this predicate: `GNSHilbert.shiftSlab_eq_id` makes
the lattice shift the identity on `SlabShiftStable`'s premise, and
`HalfLineTransfer.shiftObs_pow_period` gives the shift finite order, which
`finite_order_contraction_is_isometry` below turns into an isometry of the form.

On `ℤ⁴` at rank at least two neither direction is established here.
`ReflectionHalfSpace.transferData_T_ne_id_of_rank_two` gives `T ≠ 1` on the half-space algebra at
every `SU (m+2)`, which is about the map; motion in the algebra is not motion in the GNS quotient,
since `opT [F] = [F]` whenever `T F − F` lies in the null space of the form. The two lemmas below
give sufficient conditions for the predicate, not a characterisation. At `SU 0` and `SU 1` no
separating function is available and nothing is stated either way.

`-log T` requires `0 ∉ spectrum T` rather than injectivity, so this predicate is necessary for it and
not sufficient.

DERIVED: no numeral is chosen and none is a level. The literals reaching this statement are the
identities of the algebraic instances it quantifies over — the `0` and `1` of the scalar ring in
`AddCommGroup A` and `Module ℝ A` — and they enter through those instances. -/
def TransferMovesSomething {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) : Prop :=
  ∃ x : MassGap.GNSHilbert.H D.toReflForm, MassGap.GNSHilbert.opT D x ≠ x

/-- `TransferMovesSomething D` follows from `‖cT D z - z‖ ≠ 0` at a single `z : Pre D.toReflForm`.

`H` is the separated completion, so a class vanishes exactly when the seminorm of a representative
does, and `opT [z] = [z]` would make `‖cT z - z‖ = 0`.

Sufficient, not a characterisation: `opT = id` would force the seminorm to vanish at every `z` by
`UniformSpace.Completion.induction_on`, `opT` being a bundled `ContinuousLinearMap`, but that
converse is not stated here. The hypothesis is equivalent to
`transferMovesSomething_of_pairing_ne`'s, by Cauchy–Schwarz on `Pre`'s
`PreInnerProductSpace.Core` in one direction and `w := cT z - z` in the other; neither direction is
formalised.

DERIVED: `0` is the seminorm value the hypothesis excludes, which is the value separation quotients
away; it is the only numeral. -/
theorem transferMovesSomething_of_seminorm_ne_zero {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (z : MassGap.GNSHilbert.Pre D.toReflForm)
    (h : ‖MassGap.GNSHilbert.cT D z - z‖ ≠ 0) :
    TransferMovesSomething D := by
  refine ⟨(z : MassGap.GNSHilbert.H D.toReflForm), fun hc => h ?_⟩
  have h0 : ((MassGap.GNSHilbert.cT D z - z : MassGap.GNSHilbert.Pre D.toReflForm)
      : MassGap.GNSHilbert.H D.toReflForm) = 0 := by
    rw [UniformSpace.Completion.coe_sub]
    rw [← MassGap.GNSHilbert.cTL_apply, ← MassGap.GNSHilbert.opT_coe, hc, sub_self]
  rw [← UniformSpace.Completion.norm_coe
    (MassGap.GNSHilbert.cT D z - z : MassGap.GNSHilbert.Pre D.toReflForm), h0, norm_zero]

#print axioms transferMovesSomething_of_seminorm_ne_zero

/-- `TransferMovesSomething D` follows from a single pair `z`, `w` whose pairing differs between
`cT D z` and `z`: if `opT` fixed the class of `z` it would fix every pairing against it.

Taking `w = z` reads as the lag-one pairing at `z` differing from the lag-zero one.

Sufficient, not a characterisation, and about the form rather than the map —
`ReflectionHalfSpace.transferData_T_ne_id_of_rank_two` is about the map, and the two differ because
`H` is the separated completion. Its hypothesis is equivalent to
`transferMovesSomething_of_seminorm_ne_zero`'s, by Cauchy–Schwarz in one direction and
`w := cT z - z` in the other; neither direction is formalised.

At the constant observable the hypothesis fails: `InfiniteReflection.stateReflForm_vac_norm` gives
the lag-zero pairing `1` and `TransferData.T_vac` gives the lag-one pairing `1`.

The proof uses `GNSHilbert.opT_coe`, `cTL_apply` and `inner_coe`; no inequality and no positivity
enters that step, although `Pre`'s seminorm exists because `Transfer.ReflForm.form_nonneg` discharges
the core's nonnegativity.

DERIVED: no numeral. `D`, `z` and `w` are the caller's. -/
theorem transferMovesSomething_of_pairing_ne {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (z w : MassGap.GNSHilbert.Pre D.toReflForm)
    (h : MassGap.OSPositivity.cform D.toReflForm.toPreForm
          ((MassGap.GNSHilbert.cT D z : MassGap.GNSHilbert.Pre D.toReflForm) : A × A)
          ((w : MassGap.GNSHilbert.Pre D.toReflForm) : A × A)
        ≠ MassGap.OSPositivity.cform D.toReflForm.toPreForm
          ((z : MassGap.GNSHilbert.Pre D.toReflForm) : A × A)
          ((w : MassGap.GNSHilbert.Pre D.toReflForm) : A × A)) :
    TransferMovesSomething D := by
  refine ⟨(z : MassGap.GNSHilbert.H D.toReflForm), fun hc => h ?_⟩
  rw [MassGap.GNSHilbert.opT_coe, MassGap.GNSHilbert.cTL_apply] at hc
  have hinner := congrArg
    (fun x : MassGap.GNSHilbert.H D.toReflForm =>
      inner ℂ x ((w : MassGap.GNSHilbert.H D.toReflForm))) hc
  rw [MassGap.GNSHilbert.inner_coe, MassGap.GNSHilbert.inner_coe] at hinner
  exact hinner

#print axioms transferMovesSomething_of_pairing_ne

/-! ## 3. The two hypotheses -/

/-- A structure with two fields, each a `Prop` about named objects rather than about a model or an
opaque predicate:

* `I1_lagTwo` — a constant `K` with `0 < K < LagTwoSix.lagTwoThresholdSix` bounding
  `wilsonCorrAt 5 β 2` by `K * wilsonCorrAt 5 β 0` at every `β ≥ 0`.
* `I2_clustering` — one constant `L ≥ 0` making `MassGap.d2At N` Lipschitz in `β` with that constant,
  at every aperture `N`.

`CompactBeta.clay_covariance_constant_not_aperture_uniform` shows the unconditional constant
`4M·#Plaq` is not such an `L`.

Neither field mentions a spacing function or a `TransferData`. `scaling_as_stated_is_vacuous` shows
the obvious statement of a spacing is discharged by `exp(−β)`, and `MassGap.AsymptoticScaling` states
the version tying it to a lattice mass; the transfer-operator statement is
`TransferMovesSomething` above, which needs the `TransferData` it is about as a parameter.

DERIVED: `5` is the `N` of `wilsonCorrAt N`, so the lag index type is `Fin 6` — extent six, matching
`LagTwoSix.lagTwoThresholdSix`. `2` and `0` are lag indices, the lag-two ratio's numerator and
denominator. `0` is also the strict lower bound on `K`, the lower bound on `β`, and the lower bound
on `L`; `lagTwoThresholdSix` is a closed form and not a numeral. -/
structure ClayRemaining where
  /-- A single `K` strictly between `0` and `LagTwoSix.lagTwoThresholdSix` bounding the lag-two ratio
  of `wilsonCorrAt 5` at every nonnegative coupling. -/
  I1_lagTwo : ∃ K : ℝ, 0 < K ∧ K < MassGap.LagTwoSix.lagTwoThresholdSix ∧
    ∀ β : ℝ, 0 ≤ β →
      MassGap.wilsonCorrAt 5 β ⟨2, by omega⟩ ≤ K * MassGap.wilsonCorrAt 5 β ⟨0, by omega⟩
  /-- A single nonnegative `L` making `d2At N` Lipschitz in `β` at every aperture `N`. -/
  I2_clustering : ∃ L : ℝ, 0 ≤ L ∧
    ∀ (N : ℕ) (β₁ β₂ : ℝ),
      |MassGap.d2At N β₁ - MassGap.d2At N β₂| ≤ L * |β₁ - β₂|

#print axioms ClayRemaining
#print axioms TransferMovesSomething

/-! ## The consumers -/

/-- `ClayRemaining → LagTwoSix.LagTwoRatioSix`: destructuring `I1_lagTwo` and dropping its `0 < K`
conjunct, which `LagTwoRatioSix` does not carry.

So the first field is `LagTwoRatioSix` with one extra conjunct.

DERIVED: `5` is the `N` of `wilsonCorrAt N`, extent six; `2` and `0` are lag indices and `0` is also
the discarded lower bound on `K`. All are `ClayRemaining`'s. -/
theorem lagTwoRatioSix_of_clayRemaining (R : ClayRemaining) :
    MassGap.LagTwoSix.LagTwoRatioSix := by
  obtain ⟨K, _hK0, hKlt, hbound⟩ := R.I1_lagTwo
  exact ⟨K, hKlt, hbound⟩

#print axioms lagTwoRatioSix_of_clayRemaining

/-- `ClayRemaining → ApertureRoute.FlagshipAt (…)`:
`lagTwoRatioSix_of_clayRemaining` followed by `LagTwoSix.confines_of_lagTwoRatioSix` and
`ApertureRoute.flagship_of_confinement_at_an_aperture`.

It destructures `I1_lagTwo` alone; `I2_clustering` is not read here and has no consumer in this
module.

Scope. `#print axioms` reports `Complete.wilson_reflection_positive_at` on this and on
`lagTwoRatioSix_of_clayRemaining`, inherited from `ClayRemaining`, whose `I2_clustering` field is
stated on `d2At` at every aperture. The route itself does not need it:
`LagTwoSix.confines_extent_six_of_lag_two_ratio` is foundational-only, spending the proved
`Complete.wilson_reflection_positive_at_even 5 3`, so a caller holding
`LagTwoSix.LagTwoRatioSix` and using `confines_of_lagTwoRatioSix` directly reaches the same
conclusion without the axiom.

`FlagshipScope` records what `FlagshipAt` amounts to: `gap_summand_is_manufactured` shows its gap
clause's sum is `exp(−(κ₀ − μ))^τ`, one mode whose magnitude is its own bound, and
`flagship_for_bogus` discharges the whole conjunction for an object with no gauge content.

DERIVED: no numeral of its own; every constant is `ClayRemaining`'s or
`LagTwoSix.confines_of_lagTwoRatioSix`'s. -/
theorem flagship_of_clayRemaining (R : ClayRemaining) :
    MassGap.ApertureRoute.FlagshipAt
      (MassGap.LagTwoSix.confines_of_lagTwoRatioSix (lagTwoRatioSix_of_clayRemaining R)) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_clayRemaining

/-- There is a function `a : ℝ → ℝ` that is positive everywhere and tends to `0` along `atTop`. The
witness is `exp(−β)`, positive by `Real.exp_pos` and null by `Real.tendsto_exp_neg_atTop_nhds_zero`.

So "a spacing as a function of the coupling, positive, tending to zero" is satisfied by a function
mentioning no gauge group, no lattice and no beta function, which is why `ClayRemaining` carries no
such field.

`MassGap.AsymptoticScaling` states the version that ties `a(β)` to the theory, requiring the ratio
`m_lat(β)/a(β)` to converge to a finite nonzero limit; its
`free_spacing_scaling_is_also_vacuous` shows that leaving the spacing existential is satisfied by
taking `a := m_lat`, at ratio identically `1`, and `Running`'s `b₀ = 11N/3` and `b₁ = 34N²/3` pin the
spacing in `aRun`. `mLatAt` supplies the lattice mass, its value at zero coupling being `0` because
`Real.log 0 = 0`. `fixed_extent_pins_the_spacing` shows a lattice mass bounded away from zero
forbids a vanishing spacing. `Complete.ym_physical_gap_uniform` and its siblings take the spacing as
a parameter and relate it to no coupling.

DERIVED: `0` is the strict lower bound asserted of `a` and the limit point; it is the only numeral.
`exp(−β)` is a witness rather than a magnitude, and any positive null function does the same. -/
theorem scaling_as_stated_is_vacuous :
    ∃ a : ℝ → ℝ, (∀ β, 0 < a β) ∧ Tendsto a atTop (nhds 0) := by
  refine ⟨fun β => Real.exp (-β), fun β => Real.exp_pos _, ?_⟩
  simpa using Real.tendsto_exp_neg_atTop_nhds_zero

#print axioms scaling_as_stated_is_vacuous

/-! ## 4. Finite-order maps on a `TransferData`

On a `TransferData`, finite order plus contractivity forces the form to be preserved, so such a `T`
is an isometry of the form and admits no geometric decay factor.

The hypothesis is supplied by `HalfLineTransfer.shiftObs_pow_period`, which gives
`(shiftObs τ)ⁿ = id` on the periodic lattice with no condition on the module, the coupling or the
reflection. So every operator assembled from lattice translations on a periodic lattice satisfies it.

On `ℤ⁴` the hypothesis fails, given a separating function on the group:
`HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` exhibits, for every positive `k`, a member
of `halfSpaceAlg` that the `k`-fold shift moves.
`HaarVariance.reTr_flipEl_ne_reTr_one` supplies such a function at every `SU (m+2)`, bundled as
`ReflectionHalfSpace.reTrCM_separating`; `halfSpaceAlg_has_nonconstant` separates configurations
rather than group elements and does not have the type for it. At `SU 0` and `SU 1` no separating
function is available and nothing here applies in either direction. -/

/-- The form along the orbit of `T` is antitone: `k ↦ D.form (T^[k] x) (T^[k] x)` is nonincreasing.
`antitone_nat_of_succ_le` on `D.T_contract`, which says one step cannot expand the form.

The only place contractivity is used in this section.

DERIVED: no numeral. `D` and `x` are the caller's; the successor step belongs to
`antitone_nat_of_succ_le`. -/
theorem form_iterate_antitone {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (x : A) :
    Antitone (fun k : ℕ => D.form ((fun y => D.T y)^[k] x) ((fun y => D.T y)^[k] x)) := by
  refine antitone_nat_of_succ_le (fun k => ?_)
  have h := D.T_contract ((fun y => D.T y)^[k] x)
  simpa [Function.iterate_succ_apply'] using h

/-- If `T^[n] = id` for some `n ≥ 1`, then `D.form (T x) (T x) = D.form x x` at every `x`. A squeeze:
`form_iterate_antitone` makes the orbit values nonincreasing, and the order sends step `n` back to
step `0`, so every value between them is equal — in particular the one at step one.

So a `TransferData` whose `T` is assembled from translations of a periodic lattice has an isometric
`T`, hence an `opT` preserving norms and admitting no contraction factor below one anywhere, not
merely on the vacuum complement. `GNSHilbert.shiftSlab_eq_id` is the case where the order is one.

The hypothesis fails on `ℤ⁴` given a separating function
(`HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg`), so nothing here applies there.

DERIVED: `1` is the lower bound on the order in `hn`, needed so that step one lies between `0` and
`n`; `0` and `1` are the orbit steps the squeeze compares, and `n` is the caller's order. -/
theorem finite_order_contraction_is_isometry {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x : A) :
    D.form (D.T x) (D.T x) = D.form x x := by
  have hanti := form_iterate_antitone D x
  have h1 : D.form ((fun y => D.T y)^[n] x) ((fun y => D.T y)^[n] x)
      ≤ D.form ((fun y => D.T y)^[1] x) ((fun y => D.T y)^[1] x) := hanti hn
  have h0 : D.form ((fun y => D.T y)^[1] x) ((fun y => D.T y)^[1] x)
      ≤ D.form ((fun y => D.T y)^[0] x) ((fun y => D.T y)^[0] x) := hanti (Nat.zero_le 1)
  rw [hper x] at h1
  simp only [Function.iterate_one, Function.iterate_zero_apply] at h1 h0 ⊢
  linarith

/-- **The bridge to the tree's own idiom.** `HalfLineTransfer.shiftObs_pow_period` and
`no_rate_below_one_of_finite_order` state periodicity as `(D.T ^ p) x = x`, a power in the
endomorphism monoid, while the squeeze above runs on `Function.iterate`. Without this the theorem
would be orphaned from the two results it is about.

DERIVED: no numeral. `0` and `1` are the induction's base and step. -/
theorem pow_apply_eq_iterate {A : Type*} [AddCommGroup A] [Module ℝ A]
    (f : A →ₗ[ℝ] A) (k : ℕ) (x : A) : (f ^ k) x = (fun y => f y)^[k] x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      -- `Module.End`'s multiplication IS composition, so the last step is definitional. Spelled with
      -- `rfl` rather than a named `mul_apply` lemma because `LinearMap.mul_apply` does not exist at
      -- the v4.31.0 pin -- verified by this build refusing it.
      rw [Function.iterate_succ_apply, ← ih, pow_succ]
      rfl

/-- `finite_order_contraction_is_isometry` with `(D.T ^ n) y = y` as the hypothesis instead of the
`Function.iterate` form, through `pow_apply_eq_iterate`. This is the shape
`HalfLineTransfer.shiftObs_pow_period` states periodicity in.

DERIVED: `1` is the lower bound on the order in `hn`, carried from
`finite_order_contraction_is_isometry`; `n` is the caller's order. -/
theorem finite_order_contraction_is_isometry_pow {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (D.T ^ n) y = y) (x : A) :
    D.form (D.T x) (D.T x) = D.form x x :=
  finite_order_contraction_is_isometry D n hn
    (fun y => by rw [← pow_apply_eq_iterate D.T n y]; exact hper y) x

/-- If `T` has finite order `n ≥ 1` and `D.form (T x) (T x) ≤ ρ * D.form x x` for some `ρ ∈ [0, 1)`,
then `D.form x x = 0`. `finite_order_contraction_is_isometry` makes the left side `D.form x x`, and
`D.form_nonneg` closes the resulting inequality.

So a finite-order `T` admits a geometric decay factor only where the form already vanishes.

DERIVED: `1` is the lower bound on the order in `hn` and the strict upper bound on the decay factor
`ρ`, below which a geometric bound decays. `0` is the lower bound on `ρ` and the value concluded of
the form. -/
theorem no_decay_of_finite_order {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (ρ : ℝ) (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (x : A)
    (hdecay : D.form (D.T x) (D.T x) ≤ ρ * D.form x x) :
    D.form x x = 0 := by
  have hiso := finite_order_contraction_is_isometry D n hn hper x
  rw [hiso] at hdecay
  nlinarith [D.form_nonneg x]

/-! ## 5. Summability against a geometric bound

`WilsonAnalytic.cov_bound_summable` consumes a dominating profile whose total is bounded
independently of the volume — summable decay. A geometric bound is a stronger condition. The two
theorems below exhibit profiles satisfying the weaker one and no geometric bound, so summability,
and summability of the second moment, do not imply a geometric bound. -/

/-- There is a nonnegative summable `c : ℕ → ℝ` dominated by no geometric profile: no `C`, `r` with
`0 ≤ r < 1` satisfy `c d ≤ C * r ^ d` at every `d`.

The witness is `c d = 1/(d+1)²`, summable by comparison with the shifted `1/n²`. For the second
clause, `(d+1)²·c d` is identically one while `|C|·(2d²rᵈ + 2rᵈ)` tends to zero, so some `d`
refutes the domination; `(d+1)² ≤ 2d² + 2` is `(d−1)² ≥ 0`.

A power law steep enough is summable, so the separating case is not exceptional; it is the shape a
correlation falling like a power of the separation has.

DERIVED: the exponent `2` is the least integer power making `1/(d+1)^p` summable; `1` is the shift
keeping the denominator away from zero, and the strict upper bound on `r` below which a geometric
profile decays. `0` is the lower bound on each `c d` and on `r`. Neither is a level, and any summable
profile with no geometric bound witnesses the same separation. -/
theorem summable_clustering_is_weaker_than_a_gap :
    ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧ Summable c ∧
      ¬ ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ d, c d ≤ C * r ^ d := by
  refine ⟨fun d => 1 / ((d : ℝ) + 1) ^ 2, fun d => by positivity, ?_, ?_⟩
  · -- summability, by comparison with the shifted `1/n²`
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa using (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact h
  · rintro ⟨C, r, hr0, hr1, hdom⟩
    -- `(d+1)²·rᵈ → 0`, in the same two pieces `StrongArm.exists_geom_quartic_bound` splits into:
    -- `(d+1)² ≤ 2d² + 2` is `(d−1)² ≥ 0`, so the quadratic limit and the bare geometric one suffice.
    have h2 : Tendsto (fun d : ℕ => ((d : ℝ) ^ 2 * r ^ d)) atTop (nhds 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
    have h0 : Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hsum : Tendsto (fun d : ℕ => |C| * (2 * ((d : ℝ) ^ 2 * r ^ d) + 2 * r ^ d))
        atTop (nhds 0) := by
      simpa using (((h2.const_mul (2 : ℝ)).add (h0.const_mul (2 : ℝ))).const_mul |C|)
    obtain ⟨d, hd⟩ := (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
    have hrpow : (0 : ℝ) ≤ r ^ d := pow_nonneg hr0 d
    have hsq : ((d : ℝ) + 1) ^ 2 ≤ 2 * (d : ℝ) ^ 2 + 2 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
    have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 := by positivity
    have h1 : (1 : ℝ) ≤ C * r ^ d * ((d : ℝ) + 1) ^ 2 := by
      have hk := hdom d
      rw [div_le_iff₀ hpos] at hk
      linarith
    have step1 : C * r ^ d * ((d : ℝ) + 1) ^ 2 ≤ |C| * r ^ d * ((d : ℝ) + 1) ^ 2 := by
      have hnn : (0 : ℝ) ≤ r ^ d * ((d : ℝ) + 1) ^ 2 := by positivity
      nlinarith [le_abs_self C, hnn]
    have step2 : |C| * r ^ d * ((d : ℝ) + 1) ^ 2 ≤ |C| * r ^ d * (2 * (d : ℝ) ^ 2 + 2) := by
      have hnn : (0 : ℝ) ≤ |C| * r ^ d := by positivity
      nlinarith [hsq, hnn]
    have step3 : |C| * r ^ d * (2 * (d : ℝ) ^ 2 + 2)
        = |C| * (2 * ((d : ℝ) ^ 2 * r ^ d) + 2 * r ^ d) := by ring
    linarith [hd, h1, step1, step2, step3]

#print axioms summable_clustering_is_weaker_than_a_gap

/-- There is a nonnegative `c : ℕ → ℝ` whose second moment `d ↦ c d · d²` is summable and which is
dominated by no geometric profile.

The witness is `c d = 1/(d+1)⁴`, whose second moment is at most `1/(d+1)²` because `d² ≤ (d+1)²`.
The second clause runs as in `summable_clustering_is_weaker_than_a_gap`, with
`(d+1)⁴ ≤ 8d⁴ + 8`.

The weight matters because `d2At N β = ∑_d p_d · circLag(d)²` weights each lag by the square of its
circle distance: `CompactBeta.profile_to_moment_not_uniformly_lipschitz` exhibits, for every `L`, an
aperture and two reads whose raw profiles differ by at most `t` at every lag and whose moments differ
by more than `L·t`, the factor being `((N+1)/2)²`. That witness is a spike at the middle lag
(`ContactDominance.midLag`), so it is about arbitrary reads rather than about a decaying profile; on
profiles dominated by a `c` with `∑_k c k · k² < ∞` the moment is bounded uniformly in the aperture,
that sum being the moment.

DERIVED: the exponent `4` is `2 + 2` — two powers to beat the `circLag²` weight and two to leave a
summable remainder — and the exponent `2` is that weight. `1` is the shift keeping the denominator
from zero and the strict upper bound on `r`; `0` is the lower bound on each `c d` and on `r`. None is
a level, and any profile with a finite second moment and no geometric bound witnesses the same
separation. -/
theorem bounded_second_moment_clustering_is_weaker_than_a_gap :
    ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧ Summable (fun d => c d * ((d : ℝ)) ^ 2) ∧
      ¬ ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ d, c d ≤ C * r ^ d := by
  refine ⟨fun d => 1 / ((d : ℝ) + 1) ^ 4, fun d => by positivity, ?_, ?_⟩
  · -- second moment: `d²/(d+1)⁴ ≤ 1/(d+1)²`, and that is summable
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa using (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    refine hbase.of_nonneg_of_le (fun d => by positivity) (fun d => ?_)
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
    have hpos4 : (0 : ℝ) < ((d : ℝ) + 1) ^ 4 := by positivity
    -- `d²/(d+1)⁴ ≤ 1/(d+1)²` is `d² ≤ (d+1)²`, taken through a single subtraction so that only
    -- `div_nonneg` is named -- `div_le_div_iff` does not exist at the v4.31.0 pin.
    rw [← sub_nonneg]
    have hrw : 1 / ((d : ℝ) + 1) ^ 2 - 1 / ((d : ℝ) + 1) ^ 4 * ((d : ℝ)) ^ 2
        = (((d : ℝ) + 1) ^ 2 - ((d : ℝ)) ^ 2) / ((d : ℝ) + 1) ^ 4 := by
      field_simp
    rw [hrw]
    exact div_nonneg (by nlinarith [hd]) hpos4.le
  · rintro ⟨C, r, hr0, hr1, hdom⟩
    have h4 : Tendsto (fun d : ℕ => ((d : ℝ) ^ 4 * r ^ d)) atTop (nhds 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 4 hr0 hr1
    have h0 : Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hsum : Tendsto (fun d : ℕ => |C| * (8 * ((d : ℝ) ^ 4 * r ^ d) + 8 * r ^ d))
        atTop (nhds 0) := by
      simpa using (((h4.const_mul (8 : ℝ)).add (h0.const_mul (8 : ℝ))).const_mul |C|)
    obtain ⟨d, hd⟩ := (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
    have hrpow : (0 : ℝ) ≤ r ^ d := pow_nonneg hr0 d
    have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hq : ((d : ℝ) + 1) ^ 4 ≤ 8 * (d : ℝ) ^ 4 + 8 := by
      nlinarith [sq_nonneg ((d : ℝ) - 1), sq_nonneg ((d : ℝ) + 1), sq_nonneg ((d : ℝ) ^ 2 - 1), hdn]
    have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ 4 := by positivity
    have h1 : (1 : ℝ) ≤ C * r ^ d * ((d : ℝ) + 1) ^ 4 := by
      have hk := hdom d
      rw [div_le_iff₀ hpos] at hk
      linarith
    have step1 : C * r ^ d * ((d : ℝ) + 1) ^ 4 ≤ |C| * r ^ d * ((d : ℝ) + 1) ^ 4 := by
      have hnn : (0 : ℝ) ≤ r ^ d * ((d : ℝ) + 1) ^ 4 := by positivity
      nlinarith [le_abs_self C, hnn]
    have step2 : |C| * r ^ d * ((d : ℝ) + 1) ^ 4 ≤ |C| * r ^ d * (8 * (d : ℝ) ^ 4 + 8) := by
      have hnn : (0 : ℝ) ≤ |C| * r ^ d := by positivity
      nlinarith [hq, hnn]
    have step3 : |C| * r ^ d * (8 * (d : ℝ) ^ 4 + 8)
        = |C| * (8 * ((d : ℝ) ^ 4 * r ^ d) + 8 * r ^ d) := by ring
    linarith [hd, h1, step1, step2, step3]

#print axioms bounded_second_moment_clustering_is_weaker_than_a_gap

/-! ## 6. A uniform quartic constant against the flat profile

`NonnegArm.LawAbove b` asks for one `C`, at every aperture, with
`ρ(d) ≤ C·ρ(0)/circLag(d)⁴`. `NonnegArm.lawBelow_holds` gives the law on `[0, b]`
unconditionally, and `ApertureRoute.confinement_at_an_aperture_of_law_above_cut` carries `LawAbove b`
to `ConfinesAtAnAperture`.

The cut `b` comes from `ContactFloor.contact_relative_unconditional`, whose hypothesis is
`StrongCoupling.coreRate (16*4) b < 1` with `coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}` at `K = 64`;
solving `coreRate 64 b = 1` gives `b = 2.936e−5`. -/

/-- `¬ ∃ C ≥ 0, ∀ m ≥ 1, 1 ≤ C / m⁴`. `WeakArm.exists_lag_halving` produces, for every `C`, a lag `k`
past the cut with `C/k⁴ < 1/2`, which contradicts the requirement at `k`.

On the flat profile `ρ ≡ 1` the condition `ρ(d) ≤ C·ρ(0)/circLag(d)⁴` reads `1 ≤ C/circLag(d)⁴`, and
at extent `2m` the middle lag has `circLag = m`, so `C` would have to exceed `m⁴` at every `m`.

So an argument that never reads a profile's decay cannot give a uniform quartic constant: it would
apply to the flat profile, where the conclusion fails.
`FreeFieldLagTwo.flat_profile_meets_every_uniform_fact` exhibits the flat `r : Fin 4 → ℝ` satisfying
seven named coupling-uniform facts — nonnegativity, positive total, circle symmetry `r 3 = r 1`,
log-convexity `r 1² ≤ r 0 · r 2`, contact dominance `r 2 ≤ r 0`, `LinkGram`'s `r 2 ≤ r 1`, and
`SlabQuadratic`'s `2·r 1² ≤ r 2² + r 0·r 2` — at four components and extent four.

`WeakArm.no_uniform_quartic_constant_of_vanishing_rate` takes `hinf : ∀ ε > 0, ∃ i, M i < ε`, a rate
family whose infimum is zero, and shows such a family defeats a quartic constant.
`SubstrateArms.lawAbove_of_geometric_tail` is the positive direction: a geometric lag-decay rate,
uniform in the aperture and in the coupling above the cut, gives `LawAbove`, a geometric sequence
dominating a quartic.

DERIVED: the exponent `4` is `LawAbove`'s own; `NonnegArm` derives it as the integer above the
convergence threshold `3` for `∑ k²·C/k^s`, with
`ShareEnvelope.cubic_contact_relative_gives_no_bound` refuting `3` itself. `1` is the lower bound on
`m`, the lag cut excluding the contact term, and the value the quotient must reach. `0` is the lower
bound on `C`. Nothing here is chosen. -/
theorem flat_profile_admits_no_uniform_quartic_constant :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → (1 : ℝ) ≤ C / ((m : ℝ)) ^ 4 := by
  rintro ⟨C, _, h⟩
  -- The arithmetic is `WeakArm.exists_lag_halving`, at the level `1/2` it is already stated with.
  -- Re-proving it here would have been a second copy of the same ceiling construction.
  obtain ⟨k, _, hk1, hhalf⟩ := MassGap.WeakArm.exists_lag_halving C 1
  have := h k hk1
  linarith

#print axioms flat_profile_admits_no_uniform_quartic_constant

/-! ## 7. The coupling range `coreRate K β < 1` allows

`LagTwoBound.exists_cut_lag_two_ratio` and `LagTwoEight.exists_cut_lag_two_ratio_eight` both run
under `StrongCoupling.coreRate (16·4) β < 1`. `coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}` carries the
per-plaquette activity `e^{2β}−1` as a factor, and the other two factors are at least one at every
`K` and every `β ≥ 0`, so the condition forces `4(e^{2β}−1) < 1` with no `K` in it. -/

/-- At every `K : ℕ` and every `β ≥ 0`, `StrongCoupling.coreRate K β < 1` forces `β < 0.12`.

By contradiction: at `β ≥ 0.12`, `Real.add_one_le_exp` gives `e^{0.12} ≥ 1.12`, so
`e^{2β} ≥ 1.2544`; the factors `(K+1)² ≥ 1` and `e^{4βK} ≥ 1` then make `coreRate K β ≥ 1`.

The bound is on `coreRate`, hence on every route running under `coreRate K β < 1`, which is both
strong arms in this tree. It says nothing about a strong-coupling estimate of a different form.

DERIVED: `0.12` is a round rational above the true ceiling `log(5/4)/2 = 0.111572`, chosen so the
bound is loose in the safe direction; a tighter numeral would strengthen the statement. `0` is the
lower bound on `β` in `hβ` and `1` the strict upper bound on `coreRate` in `h`. `4`, `2` and the `+1`
are `coreRate`'s own constants; `1.12` and `1.2544 = 1.12²` are `Real.add_one_le_exp` at `0.12`,
squared, and appear in the proof rather than the statement. -/
theorem coreRate_lt_one_forces_small_beta {K : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (h : MassGap.StrongCoupling.coreRate K β < 1) : β < 0.12 := by
  by_contra hcon
  push_neg at hcon
  have h12 : (1.12 : ℝ) ≤ Real.exp 0.12 := by
    have := Real.add_one_le_exp (0.12 : ℝ); linarith
  have hsplit : Real.exp (2 * 0.12) = Real.exp 0.12 * Real.exp 0.12 := by
    rw [← Real.exp_add]; ring_nf
  have hexp024 : (1.2544 : ℝ) ≤ Real.exp (2 * 0.12) := by
    rw [hsplit]; nlinarith [h12, Real.exp_pos (0.12 : ℝ)]
  have hmono : Real.exp (2 * 0.12) ≤ Real.exp (2 * β) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE : (1.2544 : ℝ) ≤ Real.exp (2 * β) := le_trans hexp024 hmono
  have hK1 : (1 : ℝ) ≤ ((K : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  have hK : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := by nlinarith [hK1]
  have hEK : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := by
    refine Real.one_le_exp ?_
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith [hβ]
  unfold MassGap.StrongCoupling.coreRate at h
  -- three chained products; `nlinarith` will not find them, so each is supplied
  have hactnn : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by linarith
  have hKm1 : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 - 1 := by linarith
  have hb1 : (Real.exp (2 * β) - 1) ≤ ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) := by
    nlinarith [mul_nonneg hKm1 hactnn]
  have hX : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) := by
    nlinarith [hb1, hactnn]
  have hb2 : 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1)
      ≤ 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) * Real.exp (4 * β * (K : ℝ)) :=
    le_mul_of_one_le_right hX hEK
  linarith [h, hb1, hb2, hE]

#print axioms coreRate_lt_one_forces_small_beta

/-! ## 8. Two facts about the fields -/

/-- For every `M > 0` and every `B` there is an aperture `N` with
`B < 4 * M * card (WilsonHypercubic.Plaq 4 (N + 1))`. The body is
`CompactBeta.clay_covariance_constant_not_aperture_uniform`.

So `WilsonAnalytic.cov_bound_extensive`'s constant `4M·#Plaq` is not bounded over apertures, the
plaquette count being `16(N+1)⁴` at dimension four.

DERIVED: `0` is the strict lower bound on `M` in `hM`. `4` multiplying `M` is
`cov_bound_extensive`'s own coefficient, and `4` in `Plaq 4 (N + 1)` is the spatial dimension; `1` in
`N + 1` makes the aperture an extent. All are `clay_covariance_constant_not_aperture_uniform`'s. -/
theorem I2_needs_clustering_not_the_extensive_bound (M : ℝ) (hM : 0 < M) (B : ℝ) :
    ∃ N : ℕ, B < 4 * M * (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) :=
  MassGap.CompactBeta.clay_covariance_constant_not_aperture_uniform M hM B

/-- `corr_at_max_lag_eq_lag_one` restated beside the structure: `wilsonCorrAt N β ⟨N⟩` equals
`wilsonCorrAt N β ⟨1⟩` at every aperture `N ≥ 1` and every real coupling.

So whatever `I1_lagTwo` bounds at lag two, the correlation at the largest lag carries the lag-one
value, and no fixed-extent bound is a decay statement past the half period.

DERIVED: `1` is `corr_at_max_lag_eq_lag_one`'s — the lower bound on `N` and the lag compared
against. -/
theorem I1_is_not_clustering (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    MassGap.wilsonCorrAt N β ⟨N, Nat.lt_succ_self N⟩
      = MassGap.wilsonCorrAt N β ⟨1, Nat.lt_succ_of_le hN⟩ :=
  corr_at_max_lag_eq_lag_one N hN β

#print axioms form_iterate_antitone
#print axioms finite_order_contraction_is_isometry
#print axioms pow_apply_eq_iterate
#print axioms finite_order_contraction_is_isometry_pow
#print axioms no_decay_of_finite_order
#print axioms corr_at_max_lag_eq_lag_one
#print axioms no_fixed_extent_decay_past_half_period
#print axioms hilbert_space_half_of_C1_is_proved
#print axioms I2_needs_clustering_not_the_extensive_bound
#print axioms I1_is_not_clustering

end MassGap.ClayAssembly
