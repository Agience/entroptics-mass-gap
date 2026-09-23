import Mathlib
import MassGap.ReflectionHalfSpace
import MassGap.ContactValue

/-!
# MassGap.BoxNumericFloor — an explicit lower bound for the box's reflection form

`ReflectionHalfSpace.irefl_box_pairing_ge_variance` bounds the box's Wilson reflection form below by
the weight's floor times the variance of the conditional half-integral. That variance is an
integral; this module replaces it by an explicit number.

The test function is `linkTr ℓ`, the real trace at one shared-block link.
`ActionSplit.variance_ge_sq_mul_of_factor_floor` converts a variance into a number given computed
first and second moments for such a function together with a floor on the other factor.
`ContactValue` supplies the moments at `SU(3)`: `haar_re_chi_zero` gives mean `0` and
`haar_re_chi_sq` gives second moment `1 / 2`. The floor on the dressing is
`ReflectionHalfSpace.ihalfBoltz_lower_bound` through `ActionSplit.le_halfIntegral`.

Scope: colour group `SU(3)` throughout, since the value `1 / 2` is `ContactValue`'s, whose
evaluation is `SU(3)`-specific — the centre argument it runs on is vacuous at `SU(2)` — and
`ColourGeneral` records what carrying it to other ranks costs. Nothing here is stated at a general
rank. The bounds are for one box, one shared-block link and one observable; they bound a single
pairing below and do not compare two pairings at different reflection distances.

DERIVED: `3` is the rank `ContactValue` evaluates at; `4` is the dimension; `1 / 2` is the plane
trace's computed second moment; `0` is its computed mean and the lower bound on the Wilson density;
the `2` multiplying a plaquette count is the range of the Wilson density, as in
`iplaneWeight_abs_le`, and the `2` in `2 * p` is the even reflection constant; an exponent `2` is a
square; `1` is the all-identity `base` passed to `glue`.
-/

namespace MassGap.BoxNumericFloor

open MeasureTheory
open MassGap.CompactGauge

/-- `(ContactValue.chi g).re = HaarVariance.reTr g` at `SU(3)`, by `rfl`: both are the real part of
the matrix trace. It lets the two modules' lemmas compose.

DERIVED: `3` is the rank `ContactValue` evaluates at. -/
theorem re_chi_eq_reTr (g : MassGap.SUN.SU 3) :
    (MassGap.ContactValue.chi g).re = MassGap.HaarVariance.reTr g := rfl

#print axioms re_chi_eq_reTr

/-- `∫ g : SU 3, reTr g ∂(probHaar (SU 3)) = 0`: the real trace has Haar mean zero at `SU(3)`. It is
`ContactValue.haar_re_chi_zero` rewritten through `re_chi_eq_reTr`.

DERIVED: `0` is the computed mean; `3` is the rank. -/
theorem haar_reTr_zero :
    (∫ g : MassGap.SUN.SU 3, MassGap.HaarVariance.reTr g ∂(probHaar (MassGap.SUN.SU 3))) = 0 := by
  simpa only [re_chi_eq_reTr] using MassGap.ContactValue.haar_re_chi_zero

#print axioms haar_reTr_zero

/-- `∫ g : SU 3, (reTr g) ^ 2 ∂(probHaar (SU 3)) = 1 / 2`: the real trace's Haar second moment at
`SU(3)`. It is `ContactValue.haar_re_chi_sq` rewritten through `re_chi_eq_reTr`.

DERIVED: `1 / 2` is the computed second moment; the `2` in `^ 2` is the square; `3` is the rank. -/
theorem haar_reTr_sq :
    (∫ g : MassGap.SUN.SU 3, (MassGap.HaarVariance.reTr g) ^ 2
      ∂(probHaar (MassGap.SUN.SU 3))) = 1 / 2 := by
  simpa only [re_chi_eq_reTr] using MassGap.ContactValue.haar_re_chi_sq

#print axioms haar_reTr_sq

/-- There is a `C` with `|reTr g| ≤ C` for every `g : SU 3`. From compactness of `SU(3)` and
continuity of `reTr` through `IsCompact.exists_isMaxOn`; the bound is existential and no value is
computed.

DERIVED: `3` is the rank. -/
theorem exists_bound_reTr :
    ∃ C : ℝ, ∀ g : MassGap.SUN.SU 3, |MassGap.HaarVariance.reTr g| ≤ C := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    (Continuous.continuousOn (continuous_abs.comp MassGap.HaarVariance.continuous_reTr))
  exact ⟨|MassGap.HaarVariance.reTr x|, fun g => hx (Set.mem_univ g)⟩

#print axioms exists_bound_reTr

/-- The test function on configurations over a finite link set `Λ`: the real trace of the
configuration's value at one link `ℓ`.

DERIVED: `3` is the rank. -/
noncomputable def linkTr {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ℓ : ↥Λ) (U : ↥Λ → MassGap.SUN.SU 3) : ℝ :=
  MassGap.HaarVariance.reTr (U ℓ)

/-- `Continuous (linkTr ℓ)`, as `continuous_reTr` composed with evaluation at `ℓ`. Measurability
follows and is what the integrals below use.

DERIVED: `3` is the rank. -/
theorem continuous_linkTr {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥Λ) :
    Continuous (linkTr ℓ) :=
  MassGap.HaarVariance.continuous_reTr.comp (continuous_apply ℓ)

#print axioms continuous_linkTr

/-- `∫ U, linkTr ℓ U ∂(ActionSplit.cvol ↥Λ (probHaar (SU 3))) = 0`. The product measure's
single-link marginal is Haar, by `ActionSplit.integral_eval_cvol`, so the integral is
`haar_reTr_zero`.

DERIVED: `0` is the computed mean; `3` is the rank. -/
theorem integral_linkTr {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥Λ) :
    (∫ U, linkTr ℓ U
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU 3)))) = 0 := by
  rw [show (fun U : ↥Λ → MassGap.SUN.SU 3 => linkTr ℓ U)
      = fun U => MassGap.HaarVariance.reTr (U ℓ) from rfl,
    MassGap.ActionSplit.integral_eval_cvol (probHaar (MassGap.SUN.SU 3)) ℓ
      MassGap.HaarVariance.reTr MassGap.HaarVariance.measurable_reTr]
  exact haar_reTr_zero

#print axioms integral_linkTr

/-- `∫ U, (linkTr ℓ U) ^ 2 ∂(ActionSplit.cvol ↥Λ (probHaar (SU 3))) = 1 / 2`, by the same
single-link reduction applied to `haar_reTr_sq`.

DERIVED: `1 / 2` is `ContactValue`'s computed second moment; the `2` in `^ 2` is the square; `3` is
the rank. -/
theorem integral_linkTr_sq {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥Λ) :
    (∫ U, (linkTr ℓ U) ^ 2
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU 3)))) = 1 / 2 := by
  rw [show (fun U : ↥Λ → MassGap.SUN.SU 3 => (linkTr ℓ U) ^ 2)
      = fun U => (fun w => (MassGap.HaarVariance.reTr w) ^ 2) (U ℓ) from rfl,
    MassGap.ActionSplit.integral_eval_cvol (probHaar (MassGap.SUN.SU 3)) ℓ
      (fun w => (MassGap.HaarVariance.reTr w) ^ 2)
      (MassGap.HaarVariance.measurable_reTr.pow_const 2)]
  exact haar_reTr_sq

#print axioms integral_linkTr_sq

/-- The dressed observable: `linkTr ℓ U` times `ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω U`, the
real trace at one shared-block link multiplied by the half-space Boltzmann dressing. `φ`, `β`, `ω`
and the box data are all arguments.

DERIVED: `3` is the rank; `4` is the dimension the reflection axis `τ` ranges over. -/
noncomputable def traceDressed (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ℓ : ↥(MassGap.ReflectionHalfSpace.boxR τ p Λ))
    (φ : MassGap.SUN.SU 3 → ℝ) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3))
    (U : ↥Λ → MassGap.SUN.SU 3) : ℝ :=
  linkTr (ℓ : ↥Λ) U * MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω U

/-- The half-integral of `traceDressed` factorises: it equals `linkTr ℓ U` times the half-integral
of the dressing alone. Since `ℓ` lies in `boxR`, `ActionSplit.glue_agree_R` shows the trace factor
depends only on the `R`-component and is therefore constant under the `S`-integration, so
`ActionSplit.halfIntegral_mul_R_left` pulls it out.

DERIVED: `1` is the all-identity `base` passed to `glue`; `3` is the rank; `4` is the dimension the
reflection axis ranges over. -/
theorem halfIntegral_traceDressed (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ℓ : ↥(MassGap.ReflectionHalfSpace.boxR τ p Λ))
    (φ : MassGap.SUN.SU 3 → ℝ) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3))
    (U : ↥Λ → MassGap.SUN.SU 3) :
    MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
        (MassGap.ReflectionHalfSpace.boxS τ p Λ)
        (MassGap.ReflectionHalfSpace.boxR τ p Λ)
        MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
        (fun v w => traceDressed τ p Λ ℓ φ β ω
          (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
            (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U
      = linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
        (MassGap.ReflectionHalfSpace.boxS τ p Λ)
        (MassGap.ReflectionHalfSpace.boxR τ p Λ)
        MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
        (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
          (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
            (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U := by
  have hfun : (fun (v : ↥(MassGap.ReflectionHalfSpace.boxS τ p Λ) → MassGap.SUN.SU 3)
      (w : ↥(MassGap.ReflectionHalfSpace.boxR τ p Λ) → MassGap.SUN.SU 3) =>
        traceDressed τ p Λ ℓ φ β ω
          (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
            (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w))
      = fun v w => (fun w' => MassGap.HaarVariance.reTr (w' ℓ)) w
          * MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
              (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
                (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w) := by
    funext v w
    simp only [traceDressed, linkTr]
    rw [MassGap.ActionSplit.glue_agree_R _ _
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR _ v w ℓ.2]
  rw [hfun, MassGap.ActionSplit.halfIntegral_mul_R_left]
  rfl

#print axioms halfIntegral_traceDressed

/-- The variance of the half-integral of `traceDressed` is at least
`exp (-(|β| * (card (iplqPlus τ p Λ) * Cφ))) ^ 2 * (1 / 2)`, for any measurable `φ` bounded by `Cφ`,
any real `β` and any boundary condition `ω`.

`halfIntegral_traceDressed` makes the half-integral the product of `linkTr ℓ` with the dressing's
half-integral. The trace factor has mean `0` and second moment `1 / 2` (`integral_linkTr`,
`integral_linkTr_sq`); the dressing's half-integral is bounded below by
`exp (-(|β| * (card (iplqPlus τ p Λ) * Cφ)))` by `ActionSplit.le_halfIntegral` on
`ihalfBoltz_lower_bound`, and above by the corresponding positive exponential, which supplies the
integrability side conditions through `exists_bound_reTr`.
`ActionSplit.variance_ge_sq_mul_of_factor_floor` then produces the number.

The bound depends on `Λ` through the plaquette count, and on `β` and `Cφ`; it is not uniform in
those.

DERIVED: `1 / 2` is the plane trace's computed second moment; the exponents `2` are squares; `1` is
the all-identity `base` passed to `glue`; `3` is the rank; `4` is the dimension the reflection axis
ranges over. `Cφ` is the caller's bound and carries no literal. -/
theorem variance_halfIntegral_traceDressed_ge (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ℓ : ↥(MassGap.ReflectionHalfSpace.boxR τ p Λ))
    (φ : MassGap.SUN.SU 3 → ℝ) (hφm : Measurable φ) {Cφ : ℝ} (hφ : ∀ g, |φ g| ≤ Cφ)
    (β : ℝ) (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3)) :
    Real.exp (-(|β| * (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * Cφ))) ^ 2
        * (1 / 2)
      ≤ (∫ U, (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
              (MassGap.ReflectionHalfSpace.boxS τ p Λ)
              (MassGap.ReflectionHalfSpace.boxR τ p Λ)
              MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
              (fun v w => traceDressed τ p Λ ℓ φ β ω
                (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
                  (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U) ^ 2
            ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU 3))))
        - (∫ U, MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
              (MassGap.ReflectionHalfSpace.boxS τ p Λ)
              (MassGap.ReflectionHalfSpace.boxR τ p Λ)
              MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
              (fun v w => traceDressed τ p Λ ℓ φ β ω
                (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
                  (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U
            ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU 3)))) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_reTr
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 1)
  set ν := MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU 3)) with hν
  -- the dressing, glued
  have hmj : Measurable (fun q : ((↥(MassGap.ReflectionHalfSpace.boxS τ p Λ)
        → MassGap.SUN.SU 3) × (↥(MassGap.ReflectionHalfSpace.boxR τ p Λ)
        → MassGap.SUN.SU 3)) =>
      MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) q.1 q.2)) :=
    (MassGap.ReflectionHalfSpace.measurable_ihalfBoltz hφm β τ p Λ ω).comp
      (MassGap.ActionSplit.measurable_glue _ _ _)
  have hup : ∀ v w, |MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
      (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
        (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)|
      ≤ Real.exp (|β| * (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * Cφ)) :=
    fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz_upper_bound φ hφ β τ p Λ ω _
  have hlo : ∀ v w, Real.exp (-(|β| *
        (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * Cφ)))
      ≤ MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w) :=
    fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz_lower_bound φ hφ β τ p Λ ω _
  have hDlo : ∀ U, Real.exp (-(|β| *
        (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * Cφ))) ≤ MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U :=
    fun U => MassGap.ActionSplit.le_halfIntegral _ _ _ _ _ hmj hup hlo U
  have hDup : ∀ U, |MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U|
      ≤ Real.exp (|β| * (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * Cφ)) :=
    fun U => MassGap.ActionSplit.abs_halfIntegral_le _ _ _ _ _ hup U
  have hDm : Measurable (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w))) :=
    MassGap.ActionSplit.measurable_halfIntegral _ _ _ _ _ hmj
  set Ck := Real.exp (|β| * (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * Cφ))
    with hCk
  have hCk0 : (0 : ℝ) ≤ Ck := le_of_lt (Real.exp_pos _)
  have hgm : Measurable (linkTr (ℓ : ↥Λ)) := (continuous_linkTr (ℓ : ↥Λ)).measurable
  have hgb : ∀ U, |linkTr (ℓ : ↥Λ) U| ≤ C := fun U => hC _
  -- integrability
  have hg : Integrable (linkTr (ℓ : ↥Λ)) ν :=
    MassGap.ActionSplit.integrable_of_bounded _ hgm hgb
  have hg2 : Integrable (fun U => (linkTr (ℓ : ↥Λ) U) ^ 2) ν := by
    refine MassGap.ActionSplit.integrable_of_bounded _ (hgm.pow_const 2) (C := C ^ 2) (fun U => ?_)
    rw [abs_pow]
    nlinarith [abs_nonneg (linkTr (ℓ : ↥Λ) U), hgb U]
  have hgD : Integrable (fun U => linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U) ν := by
    refine MassGap.ActionSplit.integrable_of_bounded _ (hgm.mul hDm) (C := C * Ck) (fun U => ?_)
    rw [abs_mul]
    exact mul_le_mul (hgb U) (hDup U) (abs_nonneg _) hC0
  have hgDsq : Integrable (fun U => (linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U) ^ 2) ν := by
    refine MassGap.ActionSplit.integrable_of_bounded _ ((hgm.mul hDm).pow_const 2)
      (C := (C * Ck) ^ 2) (fun U => ?_)
    have hb : |linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U| ≤ C * Ck := by
      rw [abs_mul]
      exact mul_le_mul (hgb U) (hDup U) (abs_nonneg _) hC0
    rw [abs_pow]
    nlinarith [abs_nonneg (linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U), hb]
  have hgDg : Integrable (fun U => (linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U) * linkTr (ℓ : ↥Λ) U) ν := by
    refine MassGap.ActionSplit.integrable_of_bounded _ ((hgm.mul hDm).mul hgm)
      (C := (C * Ck) * C) (fun U => ?_)
    have hb : |linkTr (ℓ : ↥Λ) U * MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)) U| ≤ C * Ck := by
      rw [abs_mul]
      exact mul_le_mul (hgb U) (hDup U) (abs_nonneg _) hC0
    rw [abs_mul]
    exact mul_le_mul hb (hgb U) (abs_nonneg _) (mul_nonneg hC0 hCk0)
  -- the half-integral IS the product
  simp only [halfIntegral_traceDressed τ p Λ ℓ φ β ω]
  exact MassGap.ActionSplit.variance_ge_sq_mul_of_factor_floor ν (linkTr (ℓ : ↥Λ)) (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU 3))
      (MassGap.ReflectionHalfSpace.boxS τ p Λ)
      (MassGap.ReflectionHalfSpace.boxR τ p Λ)
      MassGap.ReflectionHalfSpace.boxS_disjoint_boxR
      (fun v w => MassGap.ReflectionHalfSpace.ihalfBoltz φ β τ p Λ ω
        (MassGap.ActionSplit.glue (MassGap.ReflectionHalfSpace.boxS τ p Λ)
          (MassGap.ReflectionHalfSpace.boxR τ p Λ) (fun _ => 1) v w)))
    (Real.exp_pos _) hDlo hg hg2 hgD hgDsq hgDg (integral_linkTr (ℓ : ↥Λ))
    (integral_linkTr_sq (ℓ : ↥Λ)) (by norm_num)

#print axioms variance_halfIntegral_traceDressed_ge

/-- The box's Wilson reflection pairing is bounded below by

    exp(-(|β| * (card (iplqZero τ p Λ) * 2)))
      * (exp(-(|β| * (card (iplqPlus τ p Λ) * 2))) ^ 2 * (1 / 2))

for every centring constant `k`, every real `β`, every boundary condition `ω`, and every
reflection-closed `Λ` — `hΛ` — carrying a shared-block link `ℓ`. The observable paired is
`traceDressed τ p Λ ℓ φ β ω`, with `φ` measurable and taking values in `[0, 2]`.

`ReflectionHalfSpace.irefl_box_pairing_ge_variance` gives the weight's floor times the
half-integral's variance, and `variance_halfIntegral_traceDressed_ge` replaces that variance by the
number.

This bounds one pairing below, at one box, one shared-block link and one observable. It does not
compare pairings at two reflection distances, and it says nothing about a quotient of two such
pairings. The value `1 / 2` is `ContactValue`'s, so the statement is at `SU(3)`.

DERIVED: the `2` in `2 * p` is the even reflection constant; the `2`s multiplying the plaquette
counts are the range of the Wilson density, as in `iplaneWeight_abs_le`, and also the upper bound
`hφ2` imposes on `φ`; the exponent `2` is the square of the dressing's floor; `1 / 2` is the plane
trace's computed second moment; `0` is the lower bound `hφ0` imposes on `φ`; `3` is the rank; `4` is
the dimension. -/
theorem box_reflection_form_ge_number (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (hΛ : ∀ l ∈ Λ, MassGap.LatticeReflection.ireflLink τ (2 * p) l ∈ Λ)
    (ℓ : ↥(MassGap.ReflectionHalfSpace.boxR τ p Λ))
    (φ : MassGap.SUN.SU 3 → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3)) (k : ℝ) :
    Real.exp (-(|β| * (((MassGap.ReflectionHalfSpace.iplqZero τ p Λ).card : ℝ) * 2)))
        * (Real.exp (-(|β| *
              (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * 2))) ^ 2 * (1 / 2))
      ≤ ∫ U, MassGap.ReflectionHalfSpace.iplaneWeight φ β τ p Λ ω U
          * (traceDressed τ p Λ ℓ φ β ω U - k)
          * (traceDressed τ p Λ ℓ φ β ω
              (MassGap.ActionSplit.twist (MassGap.ReflectionHalfSpace.ireflBoxPerm hΛ)
                (fun l : ↥Λ => MassGap.ReflectionHalfSpace.ilinkDagger
                  (G := MassGap.SUN.SU 3) τ l.1) U) - k)
          ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU 3))) := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_reTr
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 1)
  have hφb : ∀ g : MassGap.SUN.SU 3, |φ g| ≤ 2 := by
    intro g
    rw [abs_of_nonneg (hφ0 g)]
    exact hφ2 g
  set Ck := Real.exp (|β| * (((MassGap.ReflectionHalfSpace.iplqPlus τ p Λ).card : ℝ) * 2))
    with hCk
  have hCk0 : (0 : ℝ) ≤ Ck := le_of_lt (Real.exp_pos _)
  have hgm : Measurable (linkTr (ℓ : ↥Λ)) := (continuous_linkTr (ℓ : ↥Λ)).measurable
  have hOm : Measurable (traceDressed τ p Λ ℓ φ β ω) :=
    hgm.mul (MassGap.ReflectionHalfSpace.measurable_ihalfBoltz hφm β τ p Λ ω)
  have hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU 3,
      (∀ i ∈ MassGap.ReflectionHalfSpace.boxS τ p Λ, U i = V i) →
      (∀ i ∈ MassGap.ReflectionHalfSpace.boxR τ p Λ, U i = V i) →
      traceDressed τ p Λ ℓ φ β ω U = traceDressed τ p Λ ℓ φ β ω V := by
    intro U V hS hR
    simp only [traceDressed, linkTr, hR _ ℓ.2,
      MassGap.ReflectionHalfSpace.ihalfBoltz_local φ β τ p Λ ω U V hS hR]
  have hOb : ∀ U, |traceDressed τ p Λ ℓ φ β ω U| ≤ C * Ck := by
    intro U
    simp only [traceDressed]
    rw [abs_mul]
    exact mul_le_mul (hC _)
      (MassGap.ReflectionHalfSpace.ihalfBoltz_upper_bound φ hφb β τ p Λ ω U)
      (abs_nonneg _) hC0
  refine le_trans ?_
    (MassGap.ReflectionHalfSpace.irefl_box_pairing_ge_variance hΛ φ hφm hφ0 hφ2 β ω
      (traceDressed τ p Λ ℓ φ β ω) hOm hOloc (C * Ck) hOb k)
  exact mul_le_mul_of_nonneg_left
    (variance_halfIntegral_traceDressed_ge τ p Λ ℓ φ hφm hφb β ω)
    (le_of_lt (Real.exp_pos _))

#print axioms box_reflection_form_ge_number

/-- The hypotheses of `box_reflection_form_ge_number` are met at concrete data: for `ν ≠ τ` and
`-(n : ℤ) ≤ p ≤ (n : ℤ)` there exists an observable `O` on configurations over
`symCube τ (2 * p) n` satisfying the same lower bound, with the Wilson density itself as `φ`.

The witness is `traceDressed` at the link `planeLink ν p`, which lies in the cube by
`planeLink_mem_symCube` and in its shared block by `planeLink_mem_boxR`;
`symCube_refl_stable` supplies reflection closure, and `wilsonDensity_nonneg` with
`wilsonDensity_le_two` supply the `[0, 2]` bounds on `φ`.

It is still one box, one link and one observable, and it bounds a single pairing below.

DERIVED: the `2` in `2 * p` is the even reflection constant; the `2`s multiplying the plaquette
counts are the range of the Wilson density; the exponent `2` is the square of the dressing's floor;
`1 / 2` is the plane trace's computed second moment; `3` is the rank; `4` is the dimension. The
radius condition `-(n : ℤ) ≤ p ≤ (n : ℤ)` carries no literal. -/
theorem exists_box_reflection_form_ge_number (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) {n : ℕ}
    (hlo : -(n : ℤ) ≤ p) (hhi : p ≤ (n : ℤ)) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3)) (k : ℝ) :
    ∃ O : (↥(MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) → MassGap.SUN.SU 3) → ℝ,
      Real.exp (-(|β| *
            (((MassGap.ReflectionHalfSpace.iplqZero τ p (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n)).card : ℝ) * 2)))
          * (Real.exp (-(|β| *
                (((MassGap.ReflectionHalfSpace.iplqPlus τ p (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n)).card : ℝ) * 2))) ^ 2
              * (1 / 2))
        ≤ ∫ U, MassGap.ReflectionHalfSpace.iplaneWeight
            MassGap.WilsonAction.wilsonDensity β τ p (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) ω U
            * (O U - k)
            * (O (MassGap.ActionSplit.twist
                (MassGap.ReflectionHalfSpace.ireflBoxPerm
                  (MassGap.ReflectionHalfSpace.symCube_refl_stable τ (2 * p) n))
                (fun l : ↥(MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) => MassGap.ReflectionHalfSpace.ilinkDagger
                  (G := MassGap.SUN.SU 3) τ l.1) U) - k)
            ∂(MassGap.ActionSplit.cvol ↥(MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) (probHaar (MassGap.SUN.SU 3))) := by
  have hN : (3 : ℕ) ≠ 0 := by norm_num
  exact ⟨traceDressed τ p (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n)
      ⟨⟨MassGap.ReflectionHalfSpace.planeLink ν p,
        MassGap.ReflectionHalfSpace.planeLink_mem_symCube τ ν p hlo hhi⟩,
        MassGap.ReflectionHalfSpace.planeLink_mem_boxR τ ν hν p hlo hhi⟩
      MassGap.WilsonAction.wilsonDensity β ω,
    box_reflection_form_ge_number τ p (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n)
      (MassGap.ReflectionHalfSpace.symCube_refl_stable τ (2 * p) n) _
      MassGap.WilsonAction.wilsonDensity MassGap.WilsonAction.measurable_wilsonDensity
      (fun g => MassGap.WilsonAction.wilsonDensity_nonneg hN g)
      (fun g => MassGap.WilsonAction.wilsonDensity_le_two hN g) β ω k⟩

#print axioms exists_box_reflection_form_ge_number

end MassGap.BoxNumericFloor
