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

**The closest prior art is `VolumeRate.gap_rate_uniform_in_volume_of_intensive`**, which has the same
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

/-! ## The vacuum's complement as an operator

`hsp` in `OpTBridge.reconstruct_from_opT` is a statement about `spectrum ℝ (opT D)`, and nothing in
the tree proves any spectral fact about `opT`. The block structure is what a spectral argument needs:
`opT` fixes `Ω` and preserves `Ωᗮ`, and `GapAt` bounds it there. A bound ON a subspace is not a
statement about an operator until that subspace carries one, which is what this section builds. -/

section VacPerp

open ComplexConjugate

/-- **The vacuum's orthogonal complement in the completion.**

`SecondEigenvalue.vacPerp` is the same idea on the REAL GNS quotient; this is the one `opT` acts on.

DERIVED: no numeral. -/
noncomputable def vacPerpH (D : TransferData A) : Submodule ℂ (H D.toReflForm) :=
  (ℂ ∙ Omega D.toReflForm D.vac)ᗮ

/-- **Membership is the orthogonality equation** the rest of the file states its hypotheses in.

DERIVED: the `0` is orthogonality. -/
theorem mem_vacPerpH (D : TransferData A) {x : H D.toReflForm} :
    x ∈ vacPerpH D ↔ inner ℂ (Omega D.toReflForm D.vac) x = (0 : ℂ) :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

#print axioms mem_vacPerpH

/-- **`opT` maps the complement into itself** — `orth_invariant_opT` in the form `codRestrict` wants.

DERIVED: no numeral. -/
theorem opT_mem_vacPerpH (D : TransferData A) (x : vacPerpH D) :
    (opT D) ((vacPerpH D).subtypeL x) ∈ vacPerpH D := by
  rw [mem_vacPerpH, Submodule.subtypeL_apply]
  exact orth_invariant_opT D ((mem_vacPerpH D).mp x.2)

#print axioms opT_mem_vacPerpH

/-- **⭐ THE COMPRESSION OF `opT` TO THE VACUUM'S COMPLEMENT.**

The operator a spectral argument runs on. `opT` itself has `1` in its spectrum — it fixes `Ω`
(`opT_Omega`) — so no contraction bound can hold for it globally; the decay lives entirely on this
complement, and this is that restriction as an operator in its own right.

DERIVED: no numeral. -/
noncomputable def opTperp (D : TransferData A) : vacPerpH D →L[ℂ] vacPerpH D :=
  ((opT D).comp (vacPerpH D).subtypeL).codRestrict (vacPerpH D) (opT_mem_vacPerpH D)

/-- **What it does, read in the completion.**

DERIVED: no numeral. -/
@[simp] theorem coe_opTperp_apply (D : TransferData A) (x : vacPerpH D) :
    ((opTperp D x : vacPerpH D) : H D.toReflForm) = (opT D) (x : H D.toReflForm) := by
  rw [opTperp, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

#print axioms coe_opTperp_apply

/-- **⭐⭐ AND `GapAt D r` BOUNDS ITS OPERATOR NORM BY `r`.**

`norm_opT_le_of_orth` gives `‖opT D x‖ ≤ r‖x‖` for each `x ⊥ Ω`. This is that bound as a statement
about `‖opTperp D‖`, which is what a resolvent argument can consume: for `‖opTperp D‖ ≤ r < 1` and
`r < |μ|`, `μ - opTperp D` is invertible by the Neumann series, and the only spectral value left is
the vacuum's `1`.

**⛔ AND IT IS NOT A STEP TOWARD `hsp`, WHICH IS THE POINT.** `hsp` asks for
`Set.Icc ε (exp (-Δ))` with `ε > 0`, i.e. that the spectrum stay away from `0`, and
`TransferInvertibility.isUnit_of_spectral_hypothesis` shows that is exactly `IsUnit T`.
`spectral_hypothesis_fails_for_compact` then makes it UNSATISFIABLE for a compact operator in
infinite dimensions, and `energies_bounded_of_spectral_hypothesis` shows it forces every energy
below `max 0 (-log ε)` — a Hamiltonian bounded ABOVE, which a quantum field theory's is not. So the
lower cut is not a gap to be closed; it is a hypothesis this route exists to avoid.

What a norm bound on `opTperp` IS good for is the contraction form: `‖opTperp D‖ ≤ r < 1` gives decay
on the vacuum's complement with no logarithm anywhere, which is what `norm_opT_pow_le` and
`clustering_opT` below consume. Assembling `spectrum ℝ (opT D)` itself would still need `ℂ ∙ Ω` and
`vacPerpH` as complementary subspaces, and no theorem here needs that.

DERIVED: the `0` is `0 ≤ r`, which `ContinuousLinearMap.opNorm_le_bound` requires of any bound on
an operator norm; `r` itself is `GapAt`'s rate and is the caller's. No numeral is chosen here. -/
theorem norm_opTperp_le (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    ‖opTperp D‖ ≤ r := by
  refine ContinuousLinearMap.opNorm_le_bound _ hr (fun x => ?_)
  rw [Submodule.coe_norm, coe_opTperp_apply, Submodule.coe_norm]
  exact norm_opT_le_of_orth D hr hg (x : H D.toReflForm) ((mem_vacPerpH D).mp x.2)

#print axioms norm_opTperp_le

end VacPerp

/-! ## The spectrum of `opT`

A norm bound ON a subspace is still not a statement about an operator, and `norm_opTperp_le` is
where that gap shows. What closes it is that `ℂ ∙ Ω` and `vacPerpH D` are complementary and `opT`
preserves both, so a resolvent can be assembled block by block. The route below does that without
naming either subspace as a type: `vacProjH` is the rank-one projection onto the vacuum written as an
operator, `opTgap` is what is left of `opT` once that block is removed, and the factorisation

    μ - opT D = (μ - opTgap D) * (1 - μ⁻¹ • vacProjH D)

splits the resolvent into a Neumann series — legitimate because `GapAt` bounds `‖opTgap D‖` by `r`
and `μ` lies outside `[-r, r]` — and the inversion of an idempotent, which needs only `μ ≠ 1`. -/

section Spectrum

/-- **THE VACUUM IS A UNIT VECTOR IN THE COMPLEX PAIRING.** `GNSHilbert.norm_Omega_vac` read
through `inner_self_eq_norm_sq_to_K`.

DERIVED: the `1` is `norm_Omega_vac`'s, which is `D.vac_norm`; nothing is chosen here. -/
theorem inner_Omega_self (D : TransferData A) :
    inner ℂ (Omega D.toReflForm D.vac) (Omega D.toReflForm D.vac) = (1 : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, norm_Omega_vac]
  norm_num

/-- **THE VACUUM'S RANK-ONE PROJECTION, AS AN OPERATOR.** `x ↦ ⟪Ω, x⟫ • Ω` is the orthogonal
projection onto `ℂ ∙ Ω`; bundling it as a `ContinuousLinearMap` is what lets it be MULTIPLIED inside
the algebra `H →L[ℂ] H`, which is where a resolvent argument has to happen.

DERIVED: no numeral. -/
noncomputable def vacProjH (D : TransferData A) : H D.toReflForm →L[ℂ] H D.toReflForm :=
  (innerSL ℂ (Omega D.toReflForm D.vac)).smulRight (Omega D.toReflForm D.vac)

/-- What it does.

DERIVED: no numeral. -/
@[simp] theorem vacProjH_apply (D : TransferData A) (x : H D.toReflForm) :
    vacProjH D x = (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac := rfl

/-- It fixes the vacuum.

DERIVED: no numeral. -/
theorem vacProjH_Omega (D : TransferData A) :
    vacProjH D (Omega D.toReflForm D.vac) = Omega D.toReflForm D.vac := by
  rw [vacProjH_apply, inner_Omega_self, one_smul]

/-- **AND IT IS IDEMPOTENT**, which is the whole content of the two-by-two inversion below.

DERIVED: no numeral. -/
theorem vacProjH_mul_vacProjH (D : TransferData A) : vacProjH D * vacProjH D = vacProjH D := by
  ext x
  rw [mul_apply_eq_comp, vacProjH_apply, vacProjH_apply, inner_smul_right, inner_Omega_self, mul_one]

/-- **⭐ `opT` WITH THE VACUUM'S BLOCK SUBTRACTED.**

`opT D` fixes `Ω`, so no contraction bound can hold for it globally — `1` is an eigenvalue. Removing
the projection removes exactly that eigenvalue, and what is left is bounded by `r` on the WHOLE
space rather than only on `vacPerpH D`. That is what makes a Neumann series available.

DERIVED: no numeral. -/
noncomputable def opTgap (D : TransferData A) : H D.toReflForm →L[ℂ] H D.toReflForm :=
  opT D - vacProjH D

/-- The definition, as a rewrite.

DERIVED: no numeral. -/
theorem opTgap_def (D : TransferData A) : opTgap D = opT D - vacProjH D := rfl

/-- What it does.

DERIVED: no numeral. -/
theorem opTgap_apply (D : TransferData A) (x : H D.toReflForm) :
    opTgap D x
      = opT D x - (inner ℂ (Omega D.toReflForm D.vac) x) • Omega D.toReflForm D.vac := by
  rw [opTgap_def, sub_apply, vacProjH_apply]

/-- The two blocks reassemble `opT`.

DERIVED: no numeral. -/
theorem opTgap_add_vacProjH (D : TransferData A) : opTgap D + vacProjH D = opT D := by
  rw [opTgap_def]
  abel

/-- **THE TWO BLOCKS ANNIHILATE EACH OTHER.** `opTgap D` kills `Ω`, and the projection's range is
the vacuum line, so the composite is zero — this is what makes the factorisation below exact rather
than approximate.

DERIVED: the `0` is the zero operator. -/
theorem opTgap_mul_vacProjH (D : TransferData A) : opTgap D * vacProjH D = 0 := by
  ext x
  rw [mul_apply_eq_comp, vacProjH_apply, opTgap_apply, ContinuousLinearMap.map_smul, opT_Omega,
    inner_smul_right, inner_Omega_self, mul_one, sub_self, zero_apply]

/-- **⭐⭐ AND `GapAt D r` BOUNDS IT ON THE WHOLE SPACE.**

`norm_opT_le_of_orth` bounds `opT` only on the vacuum's complement. Here the projection is
subtracted first, so an arbitrary `x` is carried to `opT` of its projected part: `opTgap D x` equals
`opT D (x - ⟪Ω,x⟫ • Ω)`, the argument is orthogonal to `Ω` by construction, and Pythagoras gives
`‖x - ⟪Ω,x⟫ • Ω‖ ≤ ‖x‖`. Contrast `norm_opTperp_le`, which is the same bound confined to a submodule
and therefore says nothing about any element of the operator algebra.

DERIVED: the `0` is `0 ≤ r`, which `ContinuousLinearMap.opNorm_le_bound` requires of any bound on an
operator norm; `r` is `GapAt`'s rate and is the caller's. -/
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

/-- **THE GAP BLOCK'S RESOLVENT, BY NEUMANN SERIES.**

`‖opTgap D‖ ≤ r < |μ|` makes `μ⁻¹ • opTgap D` a strict contraction, so `Units.oneSub` inverts
`1 - μ⁻¹ • opTgap D`, and multiplying by the unit `algebraMap ℝ _ μ` gives `μ - opTgap D`.

**⛔ THIS IS NOT `TransferInvertibility`'s HYPOTHESIS.** Nothing here asks `opT D` itself to be
invertible, and `μ` ranges over the values EXCLUDED from the conclusion, never over the spectrum.

DERIVED: the `0` is `0 ≤ r`; `r` and `μ` are the caller's, and the interval `|μ| > r` is what
`Units.oneSub`'s contraction hypothesis becomes after the scalar is divided out. -/
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

/-- **THE VACUUM BLOCK'S RESOLVENT, INVERTED BY HAND.**

For an idempotent `e`, `(1 - t • e) * (1 + s • e) = 1 + (s - t - s*t) • e`, so the inverse exists as
soon as `s(1 - t) = t` can be solved. At `t = μ⁻¹` the solution is `s = (μ - 1)⁻¹`, and the only
thing that can obstruct it is `μ = 1` — the vacuum's own eigenvalue.

DERIVED: the `1`s are the unit of the operator algebra and the vacuum's eigenvalue `opT D Ω = Ω`,
which is what `μ ≠ 1` excludes; the `0` is `μ ≠ 0`, needed because `μ⁻¹` is the contraction scale.
Both are forced by the factorisation, not chosen. -/
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

/-- **⭐⭐⭐ THE SPECTRUM OF THE TRANSFER OPERATOR, FROM `GapAt` ALONE.**

Every real spectral value of `opT D` is either the vacuum's `1` or within `r` of zero. This is the
first spectral fact about `opT` anywhere in the tree: `OpTBridge.reconstruct_from_opT` takes a
spectral hypothesis and discharges none of it, and `norm_opTperp_le` bounds a compression rather
than saying anything about `spectrum ℝ (opT D)`.

The proof is the factorisation named in this section's header. For `μ` outside `{1} ∪ [-r, r]`,
`μ - opT D = (μ - opTgap D) * (1 - μ⁻¹ • vacProjH D)`, whose first factor is a unit by
`isUnit_sub_opTgap` (Neumann, on `r < |μ|`) and whose second is a unit by
`isUnit_one_sub_smul_vacProjH` (idempotent, on `μ ≠ 1`). `spectrum.mem_iff` turns that into
non-membership.

**⛔ WHAT THIS IS NOT.** It is NOT `OpTBridge`'s `hsp`, which additionally asks
`Set.Icc ε (exp (-Δ))` with `0 < ε`, i.e. that `0` stay OUT of the spectrum —
`TransferInvertibility.isUnit_of_spectral_hypothesis` shows that is exactly `IsUnit (opT D)`, and
this conclusion permits `0` deliberately. It is also NOT a gap: `GapAt D r` is a hypothesis, nothing
in the tree supplies one, and at `1 ≤ r` the right-hand side already contains every value
`norm_opT_le_one` allows, so the statement is empty unless `r < 1` — the same caveat
`bound_is_free_of_one_le` records for the norm bounds. And it is a bound on `spectrum ℝ`, the REAL
spectrum of a self-adjoint operator, which is where `isSelfAdjoint_opT` is doing its work.

DERIVED: the `1` is the vacuum's eigenvalue, fixed by `GNSHilbert.opT_Omega`, not a level chosen
here; the `0` is `0 ≤ r`, which `norm_opTgap_le` requires of any operator-norm bound. `r` is
`GapAt`'s rate and the interval `[-r, r]` is its symmetric reach, since `spectrum ℝ` of a
self-adjoint operator is not sign-constrained. -/
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
