import Mathlib
import MassGap.GNSHilbert
import MassGap.TransferGap

/-!
# MassGap.GapToOperator — the gap, carried to the Hilbert space, WITHOUT inverting anything

## The endpoint this replaces

Chain B reached its conclusion through `Reconstruction.reconstruct_qm_core`, which needs

    0 < ε   and   spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))

and `TransferInvertibility.isUnit_of_spectral_hypothesis` shows what that costs: keeping `0` out of
the spectrum is exactly `IsUnit T`. `OpTBridge.reconstruct_from_opT` is the declaration that routes
`opT D` into that endpoint, and so is what this module offers an alternative to.

**⚠ WHY THAT ENDPOINT IS BELIEVED UNREACHABLE IS CITED, AND PROVED NOWHERE.** A compact operator on
an infinite-dimensional space is never invertible, and the Euclidean transfer operator of a lattice
gauge theory is described as compact on an infinite-dimensional slice space with energies unbounded
above, so that `0` lies in its spectrum. **No part of that is formalised, here or anywhere in this
tree** — `TransferInvertibility`'s own header says so in those words, and repeating it without the
warning would launder it. So this module is MOTIVATED by a citation and JUSTIFIED by none: what it
proves stands on its own, and the case that the ε-form had to be replaced does not.

`TransferGap.GapAt` is already the form that avoids this — its own docstring says it is "stated as a
contraction rather than as a logarithm precisely so that `-log T` … never has to exist". What was
missing is the bridge from `GapAt`, which lives on the PRE-Hilbert form `A`, to the completed
operator `GNSHilbert.opT` on `H`. This module is that bridge.

## ⭐ What is new, and what is a second copy

**NEW: `norm_opT_le_of_orth`** — `GapAt D r` gives `‖opT D x‖ ≤ r * ‖x‖` for every `x` in the
COMPLETION orthogonal to the vacuum, not merely for `x` in the dense image of `A`. This is the only
new mathematics in the file. `GapAt` constrains `A`; `opT` is defined on the completion, and a bound
on a dense subspace is not a bound on the space until continuity is used. The argument runs on the
PROJECTED vector `y ↦ y - ⟪Ω, y⟫ • Ω`, so the inequality being extended is between two continuous
functions of `y` and holds on the dense range of the coercion. Nothing in the tree linked `GapAt` to
`opT` before it; the only prior norm bound on `opT` is the unconditional `GNSHilbert.norm_opT_le_one`.

**A SECOND COPY: `orth_invariant_opT`, `norm_opT_pow_le`, `clustering_opT`.** Each is the
complex-completion counterpart of a result the tree already proves on the REAL GNS quotient, by the
same argument: `VolumeRate.inner_vac_Tq` and `SecondEigenvalue.vacPerp_invariant` for the first,
`VolumeRate.norm_Tq_pow_le` and `SecondEigenvalue.Tq_pow_norm_le_of_rayleigh` for the second,
`PeriodicRayleigh.inner_pow_le_of_rayleigh` for the third.

**⛔ AND THAT IS A DEFECT IN THE TREE, NOT A FEATURE OF THIS MODULE.** Two Hilbert constructions
descend from the same `Transfer.TransferData` — the real quotient (`Transfer.GNS`, `Tq`), which
`VolumeRate`, `SecondEigenvalue`, `PeriodicRayleigh` and `HalfLineTransfer` consume, and
the complex completion (`GNSHilbert.H`, `opT`), which `OpTBridge` consumes — and each carries its
own copy of the vacuum-complement decay law.

`GNSCompare` relates them on the real component: same norm, same inner product, same step map, and
the embedding kills exactly the null space the quotient divides by. **That is not yet enough to
delete the duplication**, because the map is not bundled as a `LinearIsometry` and so no theorem
proved on one side can be APPLIED on the other; what remains there is packaging rather than
mathematics.

## ⛔ What is NOT here

**No spectrum, no functional calculus, no logarithm, and no invertibility.** Nothing below asks
`0 ∉ spectrum (opT D)`, which is the whole point: contrast
`TransferInvertibility.isUnit_of_spectral_hypothesis`.

**And no gap is produced.** `GapAt D r` is a hypothesis throughout. `TransferGap`'s own header says
nothing there produces one, and nothing here does either — `CLAY-GOAL`'s B5 is untouched. What
changes is that the conclusion B5 would buy is now stated on an operator the physical theory could
supply, instead of on one it cannot.
-/

namespace MassGap.GapToOperator

open MassGap.GNSHilbert MassGap.TransferGap MassGap.Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 1. The vacuum, and orthogonality to it -/

/-- **THE VACUUM BEFORE COMPLETION.** `D.vac` in the real component and `0` in the imaginary one.

DERIVED: the `0` is the imaginary component of a real observable, as in `GNSHilbert.Omega`. -/
noncomputable def vacPre (D : TransferData A) : Pre D.toReflForm :=
  Pre.ofPair D.toReflForm D.vac 0

/-- The vacuum of `H` is the class of `vacPre`. -/
theorem coe_vacPre (D : TransferData A) :
    ((vacPre D : Pre D.toReflForm) : H D.toReflForm) = Omega D.toReflForm D.vac := rfl

/-- **THE REAL PART OF THE PAIRING WITH THE VACUUM IS THE FORM ON THE REAL COMPONENT.** The cross
term drops because the vacuum's imaginary component is `0`.

DERIVED: the `0`s are the vacuum's imaginary component and the form's value on it. -/
@[simp] theorem inner_vacPre_re (D : TransferData A) (z : Pre D.toReflForm) :
    (inner ℂ (vacPre D) z).re = D.form D.vac (z : A × A).1 := by
  rw [Pre.inner_def]
  simp [vacPre, Transfer.PreForm.form_zero_left]

/-- **AND THE IMAGINARY PART IS THE FORM ON THE IMAGINARY COMPONENT.**

DERIVED: as above. -/
@[simp] theorem inner_vacPre_im (D : TransferData A) (z : Pre D.toReflForm) :
    (inner ℂ (vacPre D) z).im = D.form D.vac (z : A × A).2 := by
  rw [Pre.inner_def]
  simp [vacPre, Transfer.PreForm.form_zero_left]

/-- **ORTHOGONALITY TO THE VACUUM IS ORTHOGONALITY OF BOTH COMPONENTS**, which is the hypothesis
`TransferGap.GapAt` consumes.

DERIVED: no numeral of its own. -/
theorem orth_components (D : TransferData A) {z : Pre D.toReflForm}
    (h : inner ℂ (vacPre D) z = (0 : ℂ)) :
    D.form (z : A × A).1 D.vac = 0 ∧ D.form (z : A × A).2 D.vac = 0 := by
  have hre : D.form D.vac (z : A × A).1 = 0 := by
    rw [← inner_vacPre_re D z, h, Complex.zero_re]
  have him : D.form D.vac (z : A × A).2 = 0 := by
    rw [← inner_vacPre_im D z, h, Complex.zero_im]
  exact ⟨by rw [D.form_symm]; exact hre, by rw [D.form_symm]; exact him⟩

/-- The vacuum is a unit vector already before completion. -/
theorem inner_vacPre_self (D : TransferData A) :
    inner ℂ (vacPre D) (vacPre D) = (1 : ℂ) := by
  apply Complex.ext
  · rw [inner_vacPre_re]
    simpa [vacPre] using D.vac_norm
  · rw [inner_vacPre_im]
    simp [vacPre, Transfer.PreForm.form_zero_right]

/-! ## 2. The contraction on the pre-Hilbert space -/

/-- **`GapAt` CONTRACTS THE COMPLEXIFIED STEP ON THE VACUUM'S COMPLEMENT.** Both components are
orthogonal to the vacuum, `GapAt` contracts each, and the seminorm is their sum.

DERIVED: the `2`s are the form's degree, as in `GapAt`; `r` is the caller's. -/
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

/-! ## 3. ⭐ The bound on the completion -/

/-- **⭐ THE GAP HOLDS ON THE WHOLE VACUUM COMPLEMENT OF `H`, not only on the dense image of `A`.**

The extension is where the work is. `GapAt` constrains `A`; `opT` lives on the completion. The
inequality is carried by running it on the PROJECTED vector `y ↦ y - ⟪Ω, y⟫ • Ω`, which makes both
sides continuous functions of `y` that agree with the pre-Hilbert bound on the dense range of the
coercion; the projected form then specialises to `x` itself when `x ⊥ Ω`.

**No spectrum and no invertibility.** Contrast `TransferInvertibility.isUnit_of_spectral_hypothesis`,
which is what the ε-form of this conclusion costs.

DERIVED: no numeral of its own; `r` is `GapAt`'s. -/
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

/-- **THE COMPLEMENT IS `opT`-INVARIANT.** Self-adjointness moves `opT` across the pairing and the
vacuum is fixed — the completion's copy of `TransferGap.orth_invariant`.

DERIVED: no numeral. -/
theorem orth_invariant_opT (D : TransferData A) {x : H D.toReflForm}
    (hx : inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ)) :
    inner ℂ (Omega D.toReflForm D.vac) (opT D x) = (0 : ℂ) := by
  have hsa : ContinuousLinearMap.adjoint (opT D) = opT D := isSelfAdjoint_opT D
  have := ContinuousLinearMap.adjoint_inner_left (opT D) x (Omega D.toReflForm D.vac)
  rw [hsa] at this
  rw [← this, opT_Omega]
  exact hx

/-- **⭐ THE MASS GAP AS A DECAY RATE.** `n` steps contract by `rⁿ` on the vacuum's complement.

DERIVED: `n` is the caller's step count; `r` is `GapAt`'s. -/
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

/-- **DECAY OF THE PAIRING WHEN THE RIGHT ARGUMENT IS ORTHOGONAL TO THE VACUUM.** Cauchy–Schwarz on
`norm_opT_pow_le`; the completion's counterpart of `PeriodicRayleigh.inner_pow_le_of_rayleigh`.

`x` carries no hypothesis, and that is a strength rather than an omission: with `y ⊥ Ω` the
disconnected term `⟪x, Ω⟫⟪Ω, y⟫` vanishes on its own, so the left side already IS the connected
pairing. `clustering_opT_general` is the form with neither argument restricted.

DERIVED: no numeral of its own. -/
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

/-- Every power fixes the vacuum — the completion's `TransferGap.pow_vac`. -/
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

/-- **⭐ EXPONENTIAL CLUSTERING, NEITHER ARGUMENT RESTRICTED** — the disconnected part subtracted
explicitly, which is the shape `TransferGap.clustering_sq` has on the form and the physical content
of a mass gap `Δ = -log r`.

Split `y` into its vacuum component and the rest: `opT ^ n` fixes the first, which contributes
exactly `⟪x, Ω⟫⟪Ω, y⟫`, and `norm_opT_pow_le` decays the second.

DERIVED: no numeral of its own. -/
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

/-- **⛔ THE NEGATIVE CONTROL: AT `1 ≤ r` THE BOUND IS FREE.** `GNSHilbert.norm_opT_le_one` gives it
for EVERY vector, with no `GapAt` and no orthogonality, so every conclusion above is empty unless
`r < 1`.

Stated because the module otherwise never mentions `r < 1` and a reader could take the theorems to
say more than they do — the counterpart of `TransferGap.identity_fails_gap` and
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

/-- **THE CONTRACTION RADIUS AS AN EXPONENTIAL RATE.** `r < 1` gives `κ = -log r > 0` with
`‖Tⁿ x‖ ≤ e^{-κ n}‖x‖` on the vacuum's complement — a bound, not merely a limit.

**⛔ AND IT IS NOT A VOLUME-UNIFORMITY RESULT, despite the shape of the hypothesis.** `r` is a
PARAMETER, so the single rate is handed in by `hg` rather than derived; `κ` is a function of `r`
alone and is fixed before the index is introduced, so `∃κ ∀F` and `∀F ∃κ` have the same proof here.
The index type carries no volume structure — no extent, no dimension, no inclusions — and every
`D F` lives on ONE fixed algebra `A`, while the tree's only Wilson transfer data
(`OSPositivity.wilsonSlabTransfer`) has a TYPE that varies with the slab geometry. **A genuine volume
family cannot be substituted here.** `CellSpectrum.cell_volume_bar_nonvacuous` and `VolumeRate`'s
header make the same point about their own statements: quantifying a constant over an index is
arithmetic, not uniformity.

**The honest prior art is `VolumeRate.gap_rate_uniform_in_volume_of_intensive`**, which has the same
hypotheses and the same rate-form conclusion on the mode family. Note that
`Certify.gap_uniform_in_volume_of_intensive` is NOT the right citation: its `κ` does not occur after
the conjunction, which is the vacuous shape `VolumeRate` was written to repair and says it
supersedes.

**⚠ The hypothesis is the whole content and is supplied nowhere.** `hg : ∀ F, GapAt (D F) r` is B5.
This theorem spends it; it does not earn it. And at `r = 3^{-1/4}` the rate is `κ₀` exactly — but
`CellSpectrum.gap_uniform_of_cell_intensive`, which names that radius, carries its OWN flag that the
input `∀F, m_hi(F) ≤ 3^{-1/4}` is **OPEN** and that its operator is the two-state truncation of the
single-plaquette Hamiltonian at `V = 1`, not the finite-volume Wilson transfer. Repeating the radius
without those two facts would launder them.

DERIVED: `κ := -Real.log r` is forced by `rⁿ = e^{-κ n}`, not chosen. `0` and `1` bracket `r` because
`log` needs positivity and a contraction needs `r < 1`. -/
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

/-- **AND THE CORRELATION FORGETS** — the limit form of `forgets_at_one_rate`.

**⚠ The index family here is decorative.** `D` is used only as `D F` and `hg` only as `hg F`, so
this holds verbatim for a single `TransferData` with no index at all. It is `norm_opT_pow_le` plus
`squeeze_zero`.

DERIVED: no numeral of its own. -/
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

end MassGap.GapToOperator
