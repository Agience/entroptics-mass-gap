import Mathlib
import MassGap.GNSHilbert
import MassGap.TransferGap

/-!
# MassGap.GapToOperator — carrying `TransferGap.GapAt` to the completed Hilbert space

`TransferGap.GapAt D r` is a contraction bound stated on the pre-Hilbert form `A`: every vector of
`A` orthogonal to the vacuum has its image under the step map bounded by `r` times its norm.
`GNSHilbert.opT` is the induced operator on the completion `H`. This module carries the bound
across, derives powers, clustering and a rate from it, and reads it as a bound on the real spectrum
of `opT`.

## Contents

* `vacPre`, `inner_vacPre_re`, `inner_vacPre_im`, `orth_components`, `inner_vacPre_self` — the
  vacuum as a vector of `Pre`, the two components of the pairing with it, and orthogonality to it
  restated as the pair of real conditions `GapAt` consumes.
* `norm_cT_le_of_orth` — `GapAt` contracts the complexified step on the vacuum's complement in
  `Pre`, both components at once.
* `norm_opT_le_of_orth` — the same bound for every `x` in the completion orthogonal to the vacuum,
  not only for `x` in the dense image of `Pre`. `GapAt` constrains `A`, and a bound on a dense
  subspace is not a bound on the space until continuity is used; the argument runs on the projected
  vector `y ↦ y - ⟪Ω, y⟫ • Ω`, so the inequality is between two continuous functions of `y` and
  extends from the dense range of the coercion by `IsClosed.closure_subset_iff`.
* `orth_invariant_opT`, `norm_opT_pow_le`, `clustering_opT`, `clustering_opT_general` — invariance
  of the complement, the `rⁿ` decay of powers on it, and the two clustering forms. The same results
  on the real GNS quotient are `VolumeRate.inner_vac_Tq`, `SecondEigenvalue.vacPerp_invariant`,
  `VolumeRate.norm_Tq_pow_le`, `SecondEigenvalue.Tq_pow_norm_le_of_rayleigh` and
  `PeriodicRayleigh.inner_pow_le_of_rayleigh`; `GNSCompare` relates the two constructions on the
  real component but does not bundle the map as a `LinearIsometry`, so neither side's theorems apply
  to the other.
* `bound_is_free_of_one_le` — at `1 ≤ r` the contraction bound follows from
  `GNSHilbert.norm_opT_le_one` for every vector, with no `GapAt` and no orthogonality. Every
  conclusion in the file is therefore empty unless `r < 1`.
* `forgets_at_one_rate`, `tendsto_zero_of_intensive_radius` — the same decay written as
  `e^{-κ n}` with `κ = -log r`, and its limit form. Both take an index family, and in both the index
  is inert: `r` and `κ` are fixed before the index is introduced, so quantifying over it is
  arithmetic and not volume uniformity. Every `D F` lives on one fixed algebra `A`, where the
  tree's Wilson transfer data `OSPositivity.wilsonSlabTransfer` has a type that varies with the slab
  geometry.
* `vacPerpH`, `opTperp`, `norm_opTperp_le` — the vacuum's orthogonal complement as a submodule, the
  compression of `opT` to it, and the operator-norm bound `‖opTperp D‖ ≤ r`.
* `vacProjH`, `opTgap`, `norm_opTgap_le`, `isUnit_sub_opTgap`, `isUnit_one_sub_smul_vacProjH`,
  `spectrum_opT_subset` — the vacuum's rank-one projection and the complementary block as elements
  of `H →L[ℂ] H`, the factorisation
  `μ - opT D = (μ - opTgap D) * (1 - μ⁻¹ • vacProjH D)`, and the conclusion
  `spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (-r) r`.

## Scope

`GapAt D r` is a hypothesis throughout; nothing here produces one, and `r` is never constrained
below `1` except where a statement says so.

`spectrum_opT_subset` bounds the real spectrum of a self-adjoint operator and admits `0`. It is not
`OpTBridge.reconstruct_from_opT`'s `hsp`, which additionally asks for
`Set.Icc ε (Real.exp (-Δ))` with `0 < ε` — that `0` stay out of the spectrum —
and which `TransferInvertibility.isUnit_of_spectral_hypothesis` identifies with `IsUnit (opT D)`.
No functional calculus and no logarithm of `opT` is built anywhere below; `forgets_at_one_rate`
takes the logarithm of the real number `r`, not of an operator.
-/

namespace MassGap.GapToOperator

open MassGap.GNSHilbert MassGap.TransferGap MassGap.Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 1. The vacuum, and orthogonality to it -/

/-- The vacuum as a vector of `Pre D.toReflForm`, before completion: `D.vac` in the real component
and `0` in the imaginary one, assembled by `Pre.ofPair`.

DERIVED: the `0` is the imaginary component of a real observable, as in `GNSHilbert.Omega`. -/
noncomputable def vacPre (D : TransferData A) : Pre D.toReflForm :=
  Pre.ofPair D.toReflForm D.vac 0

/-- The vacuum of the completion is the image of `vacPre` under the coercion:
`(vacPre D : H D.toReflForm) = Omega D.toReflForm D.vac`. The proof is `rfl`.

DERIVED: no numeral. The `0` reaching this statement sits inside `vacPre`. -/
theorem coe_vacPre (D : TransferData A) :
    ((vacPre D : Pre D.toReflForm) : H D.toReflForm) = Omega D.toReflForm D.vac := rfl

/-- The real part of the pairing with the vacuum is the reflection form applied to `D.vac` and the
real component of `z`. The cross term drops through `Transfer.PreForm.form_zero_left`, because the
vacuum's imaginary component is `0`. A `simp` lemma.

DERIVED: no numeral of its own. The `0` this turns on is `vacPre`'s imaginary component, and
`(z : A × A).1` is the first projection of the pair, not a literal. -/
@[simp] theorem inner_vacPre_re (D : TransferData A) (z : Pre D.toReflForm) :
    (inner ℂ (vacPre D) z).re = D.form D.vac (z : A × A).1 := by
  rw [Pre.inner_def]
  simp [vacPre, Transfer.PreForm.form_zero_left]

/-- The imaginary part of the pairing with the vacuum is the reflection form applied to `D.vac` and
the imaginary component of `z`, by the same cancellation. A `simp` lemma.

DERIVED: no numeral of its own. The `0` this turns on is `vacPre`'s imaginary component, and
`(z : A × A).2` is the second projection of the pair, not a literal. -/
@[simp] theorem inner_vacPre_im (D : TransferData A) (z : Pre D.toReflForm) :
    (inner ℂ (vacPre D) z).im = D.form D.vac (z : A × A).2 := by
  rw [Pre.inner_def]
  simp [vacPre, Transfer.PreForm.form_zero_left]

/-- A vector of `Pre` orthogonal to the vacuum in the complex pairing has both its real and its
imaginary component orthogonal to `D.vac` in the reflection form. These two conditions are what
`TransferGap.GapAt` takes as hypotheses. The implication is stated in one direction only.
`D.form_symm` puts the arguments in the order `GapAt` wants.

DERIVED: the `0`s are the vanishing pairing assumed of `z` and the two vanishing form values
concluded of its components; all three are the orthogonality being asserted, not levels. -/
theorem orth_components (D : TransferData A) {z : Pre D.toReflForm}
    (h : inner ℂ (vacPre D) z = (0 : ℂ)) :
    D.form (z : A × A).1 D.vac = 0 ∧ D.form (z : A × A).2 D.vac = 0 := by
  have hre : D.form D.vac (z : A × A).1 = 0 := by
    rw [← inner_vacPre_re D z, h, Complex.zero_re]
  have him : D.form D.vac (z : A × A).2 = 0 := by
    rw [← inner_vacPre_im D z, h, Complex.zero_im]
  exact ⟨by rw [D.form_symm]; exact hre, by rw [D.form_symm]; exact him⟩

/-- The vacuum is a unit vector already before completion:
`inner ℂ (vacPre D) (vacPre D) = 1`. The real part is `D.vac_norm` and the imaginary part vanishes
by `Transfer.PreForm.form_zero_right`.

DERIVED: the `1` is `D.vac_norm`'s normalisation of the vacuum, not a level chosen here. -/
theorem inner_vacPre_self (D : TransferData A) :
    inner ℂ (vacPre D) (vacPre D) = (1 : ℂ) := by
  apply Complex.ext
  · rw [inner_vacPre_re]
    simpa [vacPre] using D.vac_norm
  · rw [inner_vacPre_im]
    simp [vacPre, Transfer.PreForm.form_zero_right]

/-! ## 2. The contraction on the pre-Hilbert space -/

/-- `GapAt D r` contracts the complexified step on the vacuum's complement in `Pre`:
`‖cT D z‖ ≤ r * ‖z‖` whenever `z` pairs to zero with `vacPre D`. Both components of `z` are
orthogonal to `D.vac` by `orth_components`, `GapAt` contracts each, and `Pre.norm_mul_norm` writes
the squared seminorm as the sum of the two component contributions. The hypothesis `0 ≤ r` is what
lets the squared inequality be taken back to the norms.

DERIVED: the `0`s are the sign tested in `hr : 0 ≤ r` and the vanishing pairing in `hz`. `r` is
`GapAt`'s rate and is the caller's. The squaring in the proof is the form's degree, as in `GapAt`,
and does not appear in the statement. -/
theorem norm_cT_le_of_orth (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    {z : Pre D.toReflForm} (hz : inner ℂ (vacPre D) z = (0 : ℂ)) :
    ‖cT D z‖ ≤ r * ‖z‖ := by
  obtain ⟨h1, h2⟩ := orth_components D hz
  have hsq : ‖cT D z‖ * ‖cT D z‖ ≤ (r * ‖z‖) * (r * ‖z‖) := by
    rw [Pre.norm_mul_norm]
    have e : (r * ‖z‖) * (r * ‖z‖) = r ^ 2 * (‖z‖ * ‖z‖) := by ring
    rw [e, Pre.norm_mul_norm, cT_fst, cT_snd]
    have g1 := hg (z : A × A).1 h1
    have g2 := hg (z : A × A).2 h2
    nlinarith
  nlinarith [norm_nonneg (cT D z), norm_nonneg z, mul_nonneg hr (norm_nonneg z)]

/-! ## 3. The bound on the completion -/

/-- `GapAt D r` gives `‖opT D x‖ ≤ r * ‖x‖` for every `x` in the completion `H` orthogonal to the
vacuum, not only for `x` in the dense image of `Pre`.

`GapAt` constrains `A`; `opT` lives on the completion. The inequality is carried by running it on
the projected vector `y ↦ y - ⟪Ω, y⟫ • Ω`, which makes both sides continuous functions of `y`; that
set is closed, contains the range of the coercion by `norm_cT_le_of_orth`, and the range is dense,
so it is everything. The projected form specialises to `x` itself when `x ⊥ Ω`.

The conclusion is a norm bound on the vacuum's complement. It says nothing about the spectrum or
about invertibility.

DERIVED: the `0`s are the sign tested in `hr : 0 ≤ r` and the vanishing pairing in `hx`. `r` is
`GapAt`'s rate and is the caller's. -/
theorem norm_opT_le_of_orth (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (x : H D.toReflForm) (hx : inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ)) :
    ‖opT D x‖ ≤ r * ‖x‖ := by
  have key : ∀ y : H D.toReflForm,
      ‖opT D (y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac)‖
        ≤ r * ‖y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac‖ := by
    have hfc : Continuous (fun y : H D.toReflForm =>
        y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac) :=
      continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)
    have hclosed : IsClosed {y : H D.toReflForm |
        ‖opT D (y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac)‖
          ≤ r * ‖y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac‖} :=
      isClosed_le (((opT D).continuous.comp hfc).norm) (continuous_const.mul hfc.norm)
    have hrange : Set.range ((↑) : Pre D.toReflForm → H D.toReflForm) ⊆ {y : H D.toReflForm |
        ‖opT D (y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac)‖
          ≤ r * ‖y - (inner ℂ (Omega D.toReflForm D.vac) y) • Omega D.toReflForm D.vac‖} := by
      rintro _ ⟨z, rfl⟩
      have hinner : inner ℂ (Omega D.toReflForm D.vac)
          ((z : Pre D.toReflForm) : H D.toReflForm) = inner ℂ (vacPre D) z :=
        UniformSpace.Completion.inner_coe _ _
      have hw : inner ℂ (vacPre D)
          (z - (inner ℂ (vacPre D) z) • vacPre D) = (0 : ℂ) := by
        rw [inner_sub_right, inner_smul_right, inner_vacPre_self]
        ring
      have hstep : ((z : Pre D.toReflForm) : H D.toReflForm)
            - (inner ℂ (Omega D.toReflForm D.vac) ((z : Pre D.toReflForm) : H D.toReflForm))
              • Omega D.toReflForm D.vac
          = ((z - (inner ℂ (vacPre D) z) • vacPre D : Pre D.toReflForm) : H D.toReflForm) := by
        rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul, hinner,
          coe_vacPre]
      simp only [Set.mem_setOf_eq, hstep]
      rw [opT_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe,
        cTL_apply]
      exact norm_cT_le_of_orth D hr hg hw
    have hsub := hclosed.closure_subset_iff.2 hrange
    rw [(UniformSpace.Completion.denseRange_coe
      (α := Pre D.toReflForm)).closure_eq] at hsub
    exact fun y => hsub (Set.mem_univ y)
  have hall := key x
  rwa [hx, zero_smul, sub_zero] at hall

/-! ## 4. The rate, and clustering -/

/-- The vacuum's complement is `opT`-invariant: if `x` pairs to zero with `Ω` then so does
`opT D x`. `isSelfAdjoint_opT` moves `opT` across the pairing and `opT_Omega` fixes the vacuum. No
hypothesis on `r` and no `GapAt`. It is the completion's counterpart of
`TransferGap.orth_invariant`.

DERIVED: the `0`s are the vanishing pairing assumed of `x` and the same vanishing concluded of
`opT D x`. -/
theorem orth_invariant_opT (D : TransferData A) {x : H D.toReflForm}
    (hx : inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ)) :
    inner ℂ (Omega D.toReflForm D.vac) (opT D x) = (0 : ℂ) := by
  have hsa : ContinuousLinearMap.adjoint (opT D) = opT D := isSelfAdjoint_opT D
  have := ContinuousLinearMap.adjoint_inner_left (opT D) x (Omega D.toReflForm D.vac)
  rw [hsa] at this
  rw [← this, opT_Omega]
  exact hx

/-- `n` steps contract by `rⁿ` on the vacuum's complement: `‖(opT D ^ n) x‖ ≤ r ^ n * ‖x‖` at every
`n : ℕ` and every `x` orthogonal to `Ω`. The induction uses `norm_opT_le_of_orth` for one step and
`orth_invariant_opT` to keep the image in the complement; `0 ≤ r` is what makes `r ^ k` a
nonnegative multiplier.

DERIVED: the `0`s are the sign tested in `hr : 0 ≤ r` and the vanishing pairing assumed of `x`. `n`
is the caller's step count and `r` is `GapAt`'s rate. -/
theorem norm_opT_pow_le (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    ∀ (n : ℕ) (x : H D.toReflForm), inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ) →
      ‖(opT D ^ n) x‖ ≤ r ^ n * ‖x‖ := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ k ih =>
      intro x hx
      have hstep : ‖opT D x‖ ≤ r * ‖x‖ := norm_opT_le_of_orth D hr hg x hx
      have hTx : inner ℂ (Omega D.toReflForm D.vac) (opT D x) = (0 : ℂ) :=
        orth_invariant_opT D hx
      have hk := ih (opT D x) hTx
      have happ : (opT D ^ (k + 1)) x = (opT D ^ k) (opT D x) := by
        rw [pow_succ]
        rfl
      rw [happ]
      calc ‖(opT D ^ k) (opT D x)‖ ≤ r ^ k * ‖opT D x‖ := hk
        _ ≤ r ^ k * (r * ‖x‖) := by
            exact mul_le_mul_of_nonneg_left hstep (pow_nonneg hr k)
        _ = r ^ (k + 1) * ‖x‖ := by ring

/-- Decay of the pairing when the right argument is orthogonal to the vacuum:
`‖⟪x, (opT D ^ n) y⟫‖ ≤ rⁿ · (‖x‖ · ‖y‖)`. It is `norm_inner_le_norm` on `norm_opT_pow_le`, and it
is the completion's counterpart of `PeriodicRayleigh.inner_pow_le_of_rayleigh`.

`x` carries no hypothesis. With `y ⊥ Ω` the disconnected term `⟪x, Ω⟫⟪Ω, y⟫` vanishes, so the left
side is already the connected pairing; `clustering_opT_general` is the form with neither argument
restricted.

DERIVED: the `0`s are the sign tested in `hr : 0 ≤ r` and the vanishing pairing assumed of `y`. `n`
is the caller's step count and `r` is `GapAt`'s rate. -/
theorem clustering_opT (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (n : ℕ) (x y : H D.toReflForm)
    (hy : inner ℂ (Omega D.toReflForm D.vac) y = (0 : ℂ)) :
    ‖inner ℂ x ((opT D ^ n) y)‖ ≤ r ^ n * (‖x‖ * ‖y‖) := by
  have hcs : ‖inner ℂ x ((opT D ^ n) y)‖ ≤ ‖x‖ * ‖(opT D ^ n) y‖ := norm_inner_le_norm _ _
  have hd := norm_opT_pow_le D hr hg n y hy
  calc ‖inner ℂ x ((opT D ^ n) y)‖ ≤ ‖x‖ * ‖(opT D ^ n) y‖ := hcs
    _ ≤ ‖x‖ * (r ^ n * ‖y‖) := by
        exact mul_le_mul_of_nonneg_left hd (norm_nonneg x)
    _ = r ^ n * (‖x‖ * ‖y‖) := by ring

/-! ## 5. The general clustering statement, and what the gap buys -/

/-- Every power of `opT` fixes the vacuum: `(opT D ^ n) Ω = Ω` at every `n : ℕ`, by induction on
`opT_Omega`. No hypothesis on `r`. It is the completion's counterpart of `TransferGap.pow_vac`.

DERIVED: no numeral. -/
theorem opT_pow_Omega (D : TransferData A) (n : ℕ) :
    (opT D ^ n) (Omega D.toReflForm D.vac) = Omega D.toReflForm D.vac := by
  induction n with
  | zero => simp
  | succ k ih =>
      have happ : (opT D ^ (k + 1)) (Omega D.toReflForm D.vac)
          = (opT D ^ k) (opT D (Omega D.toReflForm D.vac)) := by
        rw [pow_succ]; rfl
      rw [happ, opT_Omega, ih]

#print axioms opT_pow_Omega

/-- Exponential clustering with neither argument restricted, the disconnected part subtracted
explicitly:

    ‖⟪x, (opT D ^ n) y⟫ − ⟪x, Ω⟫·⟪Ω, y⟫‖ ≤ rⁿ · (‖x‖ · ‖y − ⟪Ω, y⟫ • Ω‖)

`y` is split into its vacuum component and the rest; `opT_pow_Omega` fixes the first, which
contributes exactly `⟪x, Ω⟫⟪Ω, y⟫`, and `norm_opT_pow_le` decays the second. The right-hand norm is
the projected `y`, not `y` itself. This is the shape `TransferGap.clustering_sq` has on the form.

DERIVED: the `0` is the sign tested in `hr : 0 ≤ r`. `n` is the caller's step count and `r` is
`GapAt`'s rate. -/
theorem clustering_opT_general (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (n : ℕ) (x y : H D.toReflForm) :
    ‖inner ℂ x ((opT D ^ n) y)
        - (inner ℂ x (Omega D.toReflForm D.vac)) * (inner ℂ (Omega D.toReflForm D.vac) y)‖
      ≤ r ^ n * (‖x‖ * ‖y - (inner ℂ (Omega D.toReflForm D.vac) y)
          • Omega D.toReflForm D.vac‖) := by
  set c : ℂ := inner ℂ (Omega D.toReflForm D.vac) y with hc
  set w : H D.toReflForm := y - c • Omega D.toReflForm D.vac with hw
  have hwperp : inner ℂ (Omega D.toReflForm D.vac) w = (0 : ℂ) := by
    rw [hw, inner_sub_right, inner_smul_right, ← hc]
    rw [inner_self_eq_norm_sq_to_K, norm_Omega_vac]
    simp
  have hsplit : y = c • Omega D.toReflForm D.vac + w := by
    rw [hw]; abel
  have hval : inner ℂ x ((opT D ^ n) y)
      = c * inner ℂ x (Omega D.toReflForm D.vac) + inner ℂ x ((opT D ^ n) w) := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, opT_pow_Omega, inner_add_right, inner_smul_right]
  have hdiff : inner ℂ x ((opT D ^ n) y)
      - (inner ℂ x (Omega D.toReflForm D.vac)) * c = inner ℂ x ((opT D ^ n) w) := by
    rw [hval]; ring
  rw [hdiff]
  calc ‖inner ℂ x ((opT D ^ n) w)‖ ≤ ‖x‖ * ‖(opT D ^ n) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (r ^ n * ‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_opT_pow_le D hr hg n w hwperp) (norm_nonneg x)
    _ = r ^ n * (‖x‖ * ‖w‖) := by ring

#print axioms clustering_opT_general

/-- The negative control. At `1 ≤ r`, `‖opT D x‖ ≤ r * ‖x‖` holds for every vector of `H`, with no
`GapAt` hypothesis and no orthogonality, because `GNSHilbert.norm_opT_le_one` already bounds the
operator norm by `1`. The conclusions above are therefore empty unless `r < 1`, which none of them
assumes. It is the counterpart of `TransferGap.identity_fails_gap` and
`OpTBridge.spectral_hypothesis_fails_at_identity`.

DERIVED: the `1` is `norm_opT_le_one`'s contraction constant, not a level chosen here. -/
theorem bound_is_free_of_one_le (D : TransferData A) {r : ℝ} (hr : 1 ≤ r)
    (x : H D.toReflForm) : ‖opT D x‖ ≤ r * ‖x‖ := by
  have h1 : ‖opT D x‖ ≤ ‖opT D‖ * ‖x‖ := (opT D).le_opNorm x
  have h2 : ‖opT D‖ * ‖x‖ ≤ 1 * ‖x‖ :=
    mul_le_mul_of_nonneg_right (norm_opT_le_one D) (norm_nonneg x)
  have h3 : (1 : ℝ) * ‖x‖ ≤ r * ‖x‖ :=
    mul_le_mul_of_nonneg_right hr (norm_nonneg x)
  linarith

#print axioms bound_is_free_of_one_le

/-! ## 6. The radius, read as a rate -/

/-- The contraction radius read as an exponential rate. At `0 < r < 1` and a family
`hg : ∀ F, GapAt (D F) r`, there is a `κ > 0` — namely `-Real.log r` — such that
`‖(opT (D F) ^ n) x‖ ≤ e^{-κ n}·‖x‖` at every index `F`, every `n` and every `x` orthogonal to that
index's vacuum. It is `norm_opT_pow_le` with `rⁿ` rewritten through `Real.exp_log`, so it is a
bound at every `n`, not a limit.

The index is inert. `r` is a parameter, so `κ` is a function of `r` alone and is fixed before `F` is
introduced; `∃κ ∀F` and `∀F ∃κ` have the same proof here. `ι` carries no volume structure — no
extent, no dimension, no inclusions — and every `D F` lives on one fixed algebra `A`, where the
tree's Wilson transfer data `OSPositivity.wilsonSlabTransfer` has a type that varies with the slab
geometry, so a volume family cannot be substituted for `ι`.
`CellSpectrum.cell_volume_bar_nonvacuous` and `VolumeRate`'s header record the same about their own
statements. `VolumeRate.gap_rate_uniform_in_volume_of_intensive` has the same hypotheses and the
same rate-form conclusion on the mode family.

`hg` is a hypothesis; this theorem consumes it and produces nothing of the kind.

DERIVED: `κ := -Real.log r` is forced by `rⁿ = e^{-κ n}`, not chosen. The `0` of `hr0` and the `1`
of `hr1` bracket `r` because `Real.exp_log` needs positivity and `Real.log_neg` needs `r < 1` to
make `κ` positive; the `0` of `0 < κ` is that positivity, and the `0` in `hx` is the vanishing
pairing with the vacuum. -/
theorem forgets_at_one_rate {ι : Type*} (D : ι → TransferData A) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hg : ∀ F, GapAt (D F) r) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (F : ι) (n : ℕ) (x : H (D F).toReflForm),
      inner ℂ (Omega (D F).toReflForm (D F).vac) x = (0 : ℂ) →
        ‖(opT (D F) ^ n) x‖ ≤ Real.exp (-(κ * n)) * ‖x‖ := by
  refine ⟨-Real.log r, by simpa using Real.log_neg hr0 hr1, ?_⟩
  intro F n x hx
  have hpow := norm_opT_pow_le (D F) hr0.le (hg F) n x hx
  have hexp : Real.exp (-(-Real.log r * n)) = r ^ n := by
    have : -(-Real.log r * (n : ℝ)) = (n : ℝ) * Real.log r := by ring
    rw [this, Real.exp_nat_mul, Real.exp_log hr0]
  rw [hexp]
  exact hpow

#print axioms forgets_at_one_rate

/-- The limit form: `‖(opT (D F) ^ n) x‖ → 0` as `n → ∞`, for `x` orthogonal to the vacuum. It is
`norm_opT_pow_le` majorised by `r ^ n * ‖x‖` and `squeeze_zero` against
`tendsto_pow_atTop_nhds_zero_of_lt_one`. Unlike `forgets_at_one_rate` it takes `0 ≤ r` rather than
`0 < r`, since no logarithm is formed.

The index family is inert here too: `D` is used only as `D F` and `hg` only as `hg F`, so the
statement holds verbatim for a single `TransferData` with no index.

DERIVED: the `0`s are the sign tested in `hr0`, the vanishing pairing in `hx`, and the limit value
the norms tend to; the `1` of `hr1` is the unit `r` must fall strictly below for the powers to
vanish. -/
theorem tendsto_zero_of_intensive_radius {ι : Type*} (D : ι → TransferData A) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hg : ∀ F, GapAt (D F) r)
    (F : ι) (x : H (D F).toReflForm)
    (hx : inner ℂ (Omega (D F).toReflForm (D F).vac) x = (0 : ℂ)) :
    Filter.Tendsto (fun n : ℕ => ‖(opT (D F) ^ n) x‖) Filter.atTop (nhds 0) := by
  have hbound : ∀ n : ℕ, ‖(opT (D F) ^ n) x‖ ≤ r ^ n * ‖x‖ :=
    fun n => norm_opT_pow_le (D F) hr0 (hg F) n x hx
  have hgo : Filter.Tendsto (fun n : ℕ => r ^ n * ‖x‖) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using this.mul_const ‖x‖
  exact squeeze_zero (fun n => norm_nonneg _) hbound hgo

#print axioms tendsto_zero_of_intensive_radius

/-! ## 7. Footprints -/

section Audit
#print axioms vacPre
#print axioms coe_vacPre
#print axioms inner_vacPre_re
#print axioms inner_vacPre_im
#print axioms orth_components
#print axioms inner_vacPre_self
#print axioms norm_cT_le_of_orth
#print axioms norm_opT_le_of_orth
#print axioms orth_invariant_opT
#print axioms norm_opT_pow_le
#print axioms clustering_opT
end Audit

/-! ## The vacuum's complement as an operator

`opT` fixes `Ω` and preserves `Ωᗮ`, and `GapAt` bounds it on the complement. This section packages
that complement as a `Submodule ℂ` and the restriction as a `ContinuousLinearMap` on it, so the
bound becomes a statement about an operator norm rather than about each vector separately. -/

section VacPerp

open ComplexConjugate

/-- The vacuum's orthogonal complement in the completion, as a `Submodule ℂ (H D.toReflForm)`: the
orthogonal of the span of `Omega D.toReflForm D.vac`. `SecondEigenvalue.vacPerp` is the same
construction on the real GNS quotient.

DERIVED: no numeral. -/
noncomputable def vacPerpH (D : TransferData A) : Submodule ℂ (H D.toReflForm) :=
  (ℂ ∙ Omega D.toReflForm D.vac)ᗮ

/-- Membership of `vacPerpH D` is the orthogonality equation the rest of the file states its
hypotheses in: `x ∈ vacPerpH D ↔ ⟪Ω, x⟫ = 0`. It is
`Submodule.mem_orthogonal_singleton_iff_inner_right`, and it is an iff in both directions.

DERIVED: the `0` is the vanishing pairing, which is what orthogonality means here. -/
theorem mem_vacPerpH (D : TransferData A) {x : H D.toReflForm} :
    x ∈ vacPerpH D ↔ inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ) :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

#print axioms mem_vacPerpH

/-- `opT` maps `vacPerpH D` into itself: applied to the inclusion of a member, the image is again a
member. It is `orth_invariant_opT` restated through `mem_vacPerpH`, in the form
`ContinuousLinearMap.codRestrict` takes.

DERIVED: no numeral. -/
theorem opT_mem_vacPerpH (D : TransferData A) (x : vacPerpH D) :
    (opT D) ((vacPerpH D).subtypeL x) ∈ vacPerpH D := by
  rw [mem_vacPerpH, Submodule.subtypeL_apply]
  exact orth_invariant_opT D ((mem_vacPerpH D).mp x.2)

#print axioms opT_mem_vacPerpH

/-- The compression of `opT` to the vacuum's complement, as a `ContinuousLinearMap`
`vacPerpH D →L[ℂ] vacPerpH D`. It is `(opT D).comp (vacPerpH D).subtypeL` corestricted along
`opT_mem_vacPerpH`. `opT` itself fixes `Ω` (`opT_Omega`), so no contraction bound below `1` can hold
for it on all of `H`; this is the restriction on which one can.

DERIVED: no numeral. -/
noncomputable def opTperp (D : TransferData A) : vacPerpH D →L[ℂ] vacPerpH D :=
  ((opT D).comp (vacPerpH D).subtypeL).codRestrict (vacPerpH D) (opT_mem_vacPerpH D)

/-- `opTperp` read back in the completion: the inclusion of `opTperp D x` is `opT D` applied to the
inclusion of `x`. A `simp` lemma, unfolding the corestriction.

DERIVED: no numeral. -/
@[simp] theorem coe_opTperp_apply (D : TransferData A) (x : vacPerpH D) :
    ((opTperp D x : vacPerpH D) : H D.toReflForm) = (opT D) (x : H D.toReflForm) := by
  rw [opTperp, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

#print axioms coe_opTperp_apply

/-- `GapAt D r` bounds the operator norm of the compression: `‖opTperp D‖ ≤ r`. It is
`norm_opT_le_of_orth` fed to `ContinuousLinearMap.opNorm_le_bound`, with `mem_vacPerpH` supplying
each vector's orthogonality.

This is a bound on an operator on a submodule; it is not a statement about `spectrum ℝ (opT D)`,
which `spectrum_opT_subset` below reaches by a different route. It is also not
`OpTBridge.reconstruct_from_opT`'s `hsp`, which asks for `Set.Icc ε (exp (-Δ))` with `ε > 0`, that
is, for `0` to stay out of the spectrum;
`TransferInvertibility.isUnit_of_spectral_hypothesis` identifies that with `IsUnit T`,
`spectral_hypothesis_fails_for_compact` shows it unsatisfiable for a compact operator in infinite
dimensions, and `energies_bounded_of_spectral_hypothesis` shows it bounds every energy above by
`max 0 (-log ε)`.

DERIVED: the `0` is the sign tested in `hr : 0 ≤ r`, which `ContinuousLinearMap.opNorm_le_bound`
requires of any bound on an operator norm; `r` is `GapAt`'s rate and is the caller's. -/
theorem norm_opTperp_le (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    ‖opTperp D‖ ≤ r := by
  refine ContinuousLinearMap.opNorm_le_bound _ hr (fun x => ?_)
  rw [Submodule.coe_norm, coe_opTperp_apply, Submodule.coe_norm]
  exact norm_opT_le_of_orth D hr hg (x : H D.toReflForm) ((mem_vacPerpH D).mp x.2)

#print axioms norm_opTperp_le

end VacPerp

/-! ## The spectrum of `opT`

`norm_opTperp_le` bounds an operator on a submodule. The section below works instead inside the
algebra `H →L[ℂ] H`, so that a resolvent can be assembled: `vacProjH` is the rank-one projection
onto the vacuum written as an operator, `opTgap` is what is left of `opT` once that block is
removed, and the factorisation

    μ - opT D = (μ - opTgap D) * (1 - μ⁻¹ • vacProjH D)

splits the resolvent into a Neumann series — legitimate because `GapAt` bounds `‖opTgap D‖` by `r`
and `μ` lies outside `[-r, r]` — and the inversion of an idempotent, which needs only `μ ≠ 1`. -/

section Spectrum

/-- The vacuum is a unit vector in the complex pairing: `⟪Ω, Ω⟫ = 1`. It is
`GNSHilbert.norm_Omega_vac` read through `inner_self_eq_norm_sq_to_K`.

DERIVED: the `1` is `norm_Omega_vac`'s, which is `D.vac_norm`; nothing is chosen here. -/
theorem inner_Omega_self (D : TransferData A) :
    inner ℂ (Omega D.toReflForm D.vac) (Omega D.toReflForm D.vac) = (1 : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, norm_Omega_vac]
  norm_num

/-- The vacuum's rank-one projection as an operator: `x ↦ ⟪Ω, x⟫ • Ω`, built as
`(innerSL ℂ Ω).smulRight Ω`. Bundling it as a `ContinuousLinearMap` is what lets it be multiplied
inside the algebra `H →L[ℂ] H`, which is where the factorisation below happens.

DERIVED: no numeral. -/
noncomputable def vacProjH (D : TransferData A) : H D.toReflForm →L[ℂ] H D.toReflForm :=
  (innerSL ℂ (Omega D.toReflForm D.vac)).smulRight (Omega D.toReflForm D.vac)

/-- `vacProjH D x = ⟪Ω, x⟫ • Ω`, by `rfl`. A `simp` lemma.

DERIVED: no numeral. -/
@[simp] theorem vacProjH_apply (D : TransferData A) (x : H D.toReflForm) :
    vacProjH D x = (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac := rfl

/-- `vacProjH` fixes the vacuum, since `inner_Omega_self` makes the scalar `1`.

DERIVED: no numeral. The `1` the proof passes through is `inner_Omega_self`'s and does not appear in
the statement. -/
theorem vacProjH_Omega (D : TransferData A) :
    vacProjH D (Omega D.toReflForm D.vac) = Omega D.toReflForm D.vac := by
  rw [vacProjH_apply, inner_Omega_self, one_smul]

/-- `vacProjH` is idempotent as an element of the operator algebra:
`vacProjH D * vacProjH D = vacProjH D`. It is what
`isUnit_one_sub_smul_vacProjH` runs on.

DERIVED: no numeral. -/
theorem vacProjH_mul_vacProjH (D : TransferData A) : vacProjH D * vacProjH D = vacProjH D := by
  ext x
  rw [mul_apply_eq_comp, vacProjH_apply, vacProjH_apply, inner_smul_right, inner_Omega_self, mul_one]

/-- `opT` with the vacuum's block subtracted: `opTgap D = opT D - vacProjH D`, as an element of
`H →L[ℂ] H`. `opT D` fixes `Ω`, so `1` is an eigenvalue and no contraction bound below `1` can hold
for it on all of `H`. `norm_opTgap_le` bounds this difference by `r` on the whole space rather than
only on `vacPerpH D`, which is what makes the Neumann series of `isUnit_sub_opTgap` available.

DERIVED: no numeral. -/
noncomputable def opTgap (D : TransferData A) : H D.toReflForm →L[ℂ] H D.toReflForm :=
  opT D - vacProjH D

/-- `opTgap D = opT D - vacProjH D`, by `rfl`, for rewriting.

DERIVED: no numeral. -/
theorem opTgap_def (D : TransferData A) : opTgap D = opT D - vacProjH D := rfl

/-- `opTgap D x = opT D x - ⟪Ω, x⟫ • Ω`, the pointwise form.

DERIVED: no numeral. -/
theorem opTgap_apply (D : TransferData A) (x : H D.toReflForm) :
    opTgap D x
      = opT D x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac := by
  rw [opTgap_def, sub_apply, vacProjH_apply]

/-- The two blocks reassemble the operator: `opTgap D + vacProjH D = opT D`.

DERIVED: no numeral. -/
theorem opTgap_add_vacProjH (D : TransferData A) : opTgap D + vacProjH D = opT D := by
  rw [opTgap_def]
  abel

/-- The blocks annihilate in one order: `opTgap D * vacProjH D = 0`. The projection's range is the
vacuum line and `opTgap D` kills `Ω`, since `opT_Omega` and `inner_Omega_self` make the two terms of
`opTgap` agree there. The reverse product is not stated. This is what makes the factorisation in
`spectrum_opT_subset` exact.

DERIVED: the `0` is the zero operator. -/
theorem opTgap_mul_vacProjH (D : TransferData A) : opTgap D * vacProjH D = 0 := by
  ext x
  rw [mul_apply_eq_comp, vacProjH_apply, opTgap_apply, ContinuousLinearMap.map_smul, opT_Omega,
    inner_smul_right, inner_Omega_self, mul_one, sub_self, zero_apply]

/-- `GapAt D r` bounds `opTgap` on the whole space: `‖opTgap D‖ ≤ r`.

`norm_opT_le_of_orth` bounds `opT` only on the vacuum's complement. Here the projection is
subtracted first, so an arbitrary `x` is carried to `opT` of its projected part: `opTgap D x` equals
`opT D (x - ⟪Ω,x⟫ • Ω)` by `opT_Omega`, that argument is orthogonal to `Ω` by construction, and
`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` gives `‖x - ⟪Ω,x⟫ • Ω‖ ≤ ‖x‖`. Unlike
`norm_opTperp_le`, this bounds an element of the operator algebra `H →L[ℂ] H`.

DERIVED: the `0` is the sign tested in `hr : 0 ≤ r`, which `ContinuousLinearMap.opNorm_le_bound`
requires of any bound on an operator norm; `r` is `GapAt`'s rate and is the caller's. -/
theorem norm_opTgap_le (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    ‖opTgap D‖ ≤ r := by
  refine ContinuousLinearMap.opNorm_le_bound _ hr (fun x => ?_)
  have hwperp : inner ℂ (Omega D.toReflForm D.vac)
      (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac) = (0 : ℂ) := by
    rw [inner_sub_right, inner_smul_right, inner_Omega_self, mul_one, sub_self]
  have hBx : opTgap D x
      = opT D (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac) := by
    rw [map_sub, ContinuousLinearMap.map_smul, opT_Omega, opTgap_apply]
  have hperp2 : inner ℂ ((inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac)
      (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac) = (0 : ℂ) := by
    rw [inner_smul_left, hwperp, mul_zero]
  have hsplit : (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac
      + (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac) = x := by
    abel
  have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac)
      (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac) hperp2
  rw [hsplit] at hsum
  have hnw : ‖x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac‖ ≤ ‖x‖ := by
    nlinarith [hsum, norm_nonneg x,
      norm_nonneg (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac),
      mul_self_nonneg ‖(inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac‖]
  rw [hBx]
  calc ‖opT D (x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac)‖
      ≤ r * ‖x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac‖ :=
        norm_opT_le_of_orth D hr hg _ hwperp
    _ ≤ r * ‖x‖ := mul_le_mul_of_nonneg_left hnw hr

/-- The gap block's resolvent, by Neumann series: for a real `μ` with `r < |μ|`,
`algebraMap ℝ _ μ - opTgap D` is a unit of `H →L[ℂ] H`.

`norm_opTgap_le` with `r < |μ|` makes `μ⁻¹ • opTgap D` a strict contraction, so `Units.oneSub`
inverts `1 - μ⁻¹ • opTgap D`; `r < |μ|` also forces `μ ≠ 0`, so `algebraMap ℝ _ μ` is a unit, and
the product of the two is `μ - opTgap D`.

The statement is about `opTgap D`, not about `opT D`, and `μ` ranges over values excluded from
`spectrum_opT_subset`'s conclusion.

DERIVED: the `0` is the sign tested in `hr : 0 ≤ r`; `r` and `μ` are the caller's, and `r < |μ|` is
what `Units.oneSub`'s contraction hypothesis becomes after the scalar is divided out. -/
theorem isUnit_sub_opTgap (D : TransferData A) {r μ : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (hrμ : r < |μ|) :
    IsUnit (algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm) μ - opTgap D) := by
  have hμabs : 0 < |μ| := lt_of_le_of_lt hr hrμ
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμabs
    exact lt_irrefl _ hμabs
  have hB : ‖opTgap D‖ ≤ r := norm_opTgap_le D hr hg
  have hlt : ‖(μ⁻¹ : ℝ) • opTgap D‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
    have h1 : ‖opTgap D‖ < |μ| := lt_of_le_of_lt hB hrμ
    have h2 : |μ|⁻¹ * ‖opTgap D‖ < |μ|⁻¹ * |μ| :=
      mul_lt_mul_of_pos_left h1 (inv_pos.mpr hμabs)
    rwa [inv_mul_cancel₀ (ne_of_gt hμabs)] at h2
  have hUn : IsUnit ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) - (μ⁻¹ : ℝ) • opTgap D) :=
    (Units.oneSub _ hlt).isUnit
  have hUa : IsUnit (algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm) μ) :=
    IsUnit.map (algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm)) (isUnit_iff_ne_zero.mpr hμ0)
  have hfac : algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm) μ - opTgap D
      = (algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm) μ)
        * ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) - (μ⁻¹ : ℝ) • opTgap D) := by
    rw [mul_sub, mul_one, mul_smul_comm, ← Algebra.smul_def, smul_smul,
      inv_mul_cancel₀ hμ0, one_smul]
  rw [hfac]
  exact hUa.mul hUn

/-- The vacuum block's resolvent, inverted by hand: for a real `μ` with `μ ≠ 0` and `μ ≠ 1`,
`1 - μ⁻¹ • vacProjH D` is a unit of `H →L[ℂ] H`.

For an idempotent `e`, `(1 - t • e) * (1 + s • e) = 1 + (s - t - s·t) • e`, so the inverse exists as
soon as `s(1 - t) = t` can be solved. At `t = μ⁻¹` the solution is `s = (μ - 1)⁻¹`, which needs
`μ ≠ 1`; the inverse is exhibited explicitly and both products are checked. Idempotence is
`vacProjH_mul_vacProjH`. No `GapAt` and no `r` appear.

DERIVED: the `1`s are the unit of the operator algebra and the value `μ` must avoid, which is the
vacuum's eigenvalue `opT D Ω = Ω`; the `0` is the value `μ` must avoid for `μ⁻¹` to exist. Both are
forced by the factorisation, not chosen. -/
theorem isUnit_one_sub_smul_vacProjH (D : TransferData A) {μ : ℝ} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) :
    IsUnit ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) - (μ⁻¹ : ℝ) • vacProjH D) := by
  have he2 : vacProjH D * vacProjH D = vacProjH D := vacProjH_mul_vacProjH D
  have hsub : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ1
  have hst : (μ - 1)⁻¹ - (μ - 1)⁻¹ * μ⁻¹ = μ⁻¹ := by
    field_simp
  have hA : ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) - (μ⁻¹ : ℝ) • vacProjH D)
      * ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) + (((μ - 1)⁻¹ : ℝ)) • vacProjH D) = 1 := by
    rw [mul_add, mul_one, mul_smul_comm, sub_mul, one_mul, smul_mul_assoc, he2,
      smul_sub, smul_smul, ← sub_smul, hst]
    abel
  have hB : ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) + (((μ - 1)⁻¹ : ℝ)) • vacProjH D)
      * ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) - (μ⁻¹ : ℝ) • vacProjH D) = 1 := by
    rw [add_mul, one_mul, smul_mul_assoc, mul_sub, mul_one, mul_smul_comm, he2,
      smul_sub, smul_smul, ← sub_smul, hst]
    abel
  exact ⟨⟨_, _, hA, hB⟩, rfl⟩

/-- From `GapAt D r` alone: `spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (-r) r`. Every real spectral value
of `opT D` is either the vacuum's `1` or within `r` of zero.

The proof is the factorisation named in this section's header. For `μ` outside `{1} ∪ [-r, r]`,
`μ - opT D = (μ - opTgap D) * (1 - μ⁻¹ • vacProjH D)` by `opTgap_mul_vacProjH` and
`opTgap_add_vacProjH`; the first factor is a unit by `isUnit_sub_opTgap` (Neumann, on `r < |μ|`) and
the second by `isUnit_one_sub_smul_vacProjH` (idempotent, on `μ ≠ 1`). `spectrum.mem_iff` turns that
into non-membership.

Scope. The conclusion is about `spectrum ℝ`, the real spectrum of a self-adjoint operator, which is
what `isSelfAdjoint_opT` supports. It permits `0`, so it is not
`OpTBridge.reconstruct_from_opT`'s `hsp`, which additionally asks for `Set.Icc ε (exp (-Δ))` with
`0 < ε`; `TransferInvertibility.isUnit_of_spectral_hypothesis` identifies that with
`IsUnit (opT D)`. `GapAt D r` is a hypothesis, and at `1 ≤ r` the right-hand side already contains
every value `norm_opT_le_one` allows, so the statement is empty unless `r < 1`, which it does not
assume — the same caveat `bound_is_free_of_one_le` records for the norm bounds.

DERIVED: the `1` is the vacuum's eigenvalue, fixed by `GNSHilbert.opT_Omega`, not a level chosen
here; the `0` is the sign tested in `hr : 0 ≤ r`, which `norm_opTgap_le` requires of any
operator-norm bound. `r` is `GapAt`'s rate and `[-r, r]` is its symmetric reach, since `spectrum ℝ`
of a self-adjoint operator is not sign-constrained. -/
theorem spectrum_opT_subset (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (-r) r := by
  intro μ hμ
  by_contra hcon
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Icc, not_or, not_and_or,
    not_le] at hcon
  obtain ⟨hμ1, hout⟩ := hcon
  have hrμ : r < |μ| := by
    rcases hout with h | h
    · have h1 : -μ ≤ |μ| := neg_le_abs μ
      linarith
    · have h1 : μ ≤ |μ| := le_abs_self μ
      linarith
  have hμabs : 0 < |μ| := lt_of_le_of_lt hr hrμ
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμabs
    exact lt_irrefl _ hμabs
  have hfac : algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm) μ - opT D
      = (algebraMap ℝ (H D.toReflForm →L[ℂ] H D.toReflForm) μ - opTgap D)
        * ((1 : H D.toReflForm →L[ℂ] H D.toReflForm) - (μ⁻¹ : ℝ) • vacProjH D) := by
    rw [mul_sub, mul_one, mul_smul_comm, sub_mul, opTgap_mul_vacProjH, sub_zero,
      ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hμ0, one_smul, sub_sub,
      opTgap_add_vacProjH]
  apply (spectrum.mem_iff.mp hμ)
  rw [hfac]
  exact (isUnit_sub_opTgap D hr hg hrμ).mul (isUnit_one_sub_smul_vacProjH D hμ0 hμ1)

#print axioms inner_Omega_self
#print axioms vacProjH_apply
#print axioms vacProjH_mul_vacProjH
#print axioms opTgap_mul_vacProjH
#print axioms norm_opTgap_le
#print axioms isUnit_sub_opTgap
#print axioms isUnit_one_sub_smul_vacProjH
#print axioms spectrum_opT_subset

end Spectrum

end MassGap.GapToOperator
