import Mathlib
import MassGap.DSBlockContract
import MassGap.ScaleStep
import MassGap.OverlapErgodic

noncomputable section

/-!
# MassGap.DSOllivier — contraction of the summed link metric gives the Poincaré inequality of the translates

`DSBlockContract` contracts the total Lipschitz vector of the averaged block dynamics `T = (1/|Z|) Σ_z E_z`
by `1 − κ` per step. This module turns that into the Poincaré inequality
`κ |Z| ‖u‖² ≤ Σ_z ‖u − E_z u‖²` on the vacuum complement of the periodic Wilson measure (Ollivier's
"coarse Ricci curvature bounds the spectral gap"), without a spectral theorem.

1. **Projection averages** (`avgT`, `avgT_contract`, `poincare_of_step`): for form-self-adjoint idempotents
   `P z` keeping the vacuum, `T` is a self-adjoint contraction, and `B(Tx, Tx) ≤ r² B(x, x)` gives
   `(1 − r) |Z| B(x, x) ≤ Σ_z B(x − P z x, x − P z x)`.
2. **Rate on a dense set gives the step** (`step_of_dense_rate`): if every `x` of a set `D` closed under
   removing the vacuum component and dense in the form seminorm decays as `B(Tⁿx, Tⁿx) ≤ K r²ⁿ` on the vacuum
   complement, then `B(Tx, Tx) ≤ r² B(x, x)` there. The one-step bound is `ScaleStep.step_le_of_rate`
   (log-convexity of `n ↦ B(Tⁿx, Tⁿx)`), and the extension is the triangle inequality of the seminorm.
3. **Lipschitz functions are dense** (`CostMetric`, `lipSub`, `lip_dense`): for a continuous separating
   metric cost on a compact single-link space, the functions with a finite Lipschitz vector form a subalgebra
   that separates points, and Stone–Weierstrass gives uniform density in `C(Lk → Ω, ℝ)`.
4. **The Wilson torus** (`formE`, `blkL`, `translate_poincare`): on all continuous observables of the
   infinite-lattice configuration space, with the form of the periodic Wilson state, the block averages of any
   family of torus link sets `S z` are self-adjoint idempotents keeping `1`. With the block influences of
   `DSBlockContract` and a column bound `κ |Z| ≤ Σ_z gain_z l`, the torus reading of `Tⁿ u` has oscillation
   `(1 − κ)ⁿ (Σ v) Dm`, its square is the decay rate, and items 1–3 give
   `κ |Z| torusForm(u, u) ≤ Σ_z torusForm(u − E_z u, u − E_z u)` for every periodic gauge-invariant `u ⊥ 1`.

Working on all of `C(IConf, ℝ)` rather than on the gauge-invariant subspace keeps the density argument free of
gauge averaging: the inequality is proved there and restricted.

DERIVED (module-wide): `0` the signs; `1` the vacuum and the contraction's unit; `2` the squares;
`2 * j + 1` the index of the even-extent family; `4` the spacetime dimension.
-/

namespace MassGap.DSOllivier

open MassGap MassGap.DSBlockContract
open MassGap.DobrushinMixed (LipD)
open Filter

/-! ## 1. The seminorm -/

section Seminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)

/-- The seminorm `√B(x, x)`. DERIVED: no numeral. -/
def nn (x : E) : ℝ := Real.sqrt (B x x)

variable {B}

/-- DERIVED: `2` the square. -/
theorem nn_sq (hnn : ∀ x, 0 ≤ B x x) (x : E) : nn B x ^ 2 = B x x := Real.sq_sqrt (hnn x)

/-- DERIVED: `0` the sign. -/
theorem nn_nonneg (x : E) : 0 ≤ nn B x := Real.sqrt_nonneg _

/-- **Cauchy–Schwarz in seminorm form.** DERIVED: `2` the square. -/
theorem abs_form_le (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (a b : E) :
    |B a b| ≤ nn B a * nn B b := by
  have h := MassGap.HeatBathGapDecay.form_sq_le_mul B hsymm hnn a b
  unfold nn
  rw [← Real.sqrt_mul (hnn a)]
  exact Real.abs_le_sqrt h

#print axioms abs_form_le

/-- **The triangle inequality.** DERIVED: `2` the cross term. -/
theorem nn_add_le (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (a b : E) :
    nn B (a + b) ≤ nn B a + nn B b := by
  have hab : B a b ≤ nn B a * nn B b := (le_abs_self _).trans (abs_form_le hsymm hnn a b)
  have e : B (a + b) (a + b) = B a a + 2 * B a b + B b b := by
    simp only [map_add, LinearMap.add_apply]
    rw [hsymm b a]
    ring
  have h2 : B (a + b) (a + b) ≤ (nn B a + nn B b) ^ 2 := by
    rw [e, add_sq, nn_sq hnn, nn_sq hnn]
    linarith
  calc nn B (a + b) ≤ Real.sqrt ((nn B a + nn B b) ^ 2) := Real.sqrt_le_sqrt h2
    _ = nn B a + nn B b := Real.sqrt_sq (add_nonneg (nn_nonneg a) (nn_nonneg b))

#print axioms nn_add_le

/-- DERIVED: `2` the square. -/
theorem nn_smul (c : ℝ) (a : E) : nn B (c • a) = |c| * nn B a := by
  unfold nn
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

#print axioms nn_smul

end Seminorm

/-! ## 2. Projection averages -/

section Proj

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}
variable {Z : Type} [Fintype Z]

/-- **The averaged projection** `(1/|Z|) Σ_z P z`. DERIVED: no numeral. -/
def avgT (P : Z → E →ₗ[ℝ] E) : E →ₗ[ℝ] E := (Fintype.card Z : ℝ)⁻¹ • ∑ z, P z

/-- DERIVED: no numeral. -/
theorem avgT_apply (P : Z → E →ₗ[ℝ] E) (x : E) :
    avgT P x = (Fintype.card Z : ℝ)⁻¹ • ∑ z, P z x := by
  unfold avgT
  rw [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

/-- `B(c • Σ a z, y) = c Σ B(a z, y)`. DERIVED: no numeral. -/
theorem form_smul_sum_left (c : ℝ) (a : Z → E) (y : E) :
    B (c • ∑ z, a z) y = c * ∑ z, B (a z) y := by
  rw [map_smul, map_sum, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, smul_eq_mul]

/-- `B(y, c • Σ a z) = c Σ B(y, a z)`. DERIVED: no numeral. -/
theorem form_smul_sum_right (c : ℝ) (a : Z → E) (y : E) :
    B y (c • ∑ z, a z) = c * ∑ z, B y (a z) := by
  rw [map_smul, map_sum, smul_eq_mul]

/-- `B(Px, Px) = B(Px, x)` for a self-adjoint idempotent. DERIVED: no numeral. -/
theorem proj_sq (hsymm : ∀ x y, B x y = B y x) {P : E →ₗ[ℝ] E} (hsa : ∀ x y, B (P x) y = B x (P y))
    (hid : ∀ x, P (P x) = P x) (x : E) : B (P x) (P x) = B (P x) x := by
  rw [hsa, hid, hsymm]

/-- `B(x − Px, x − Px) = B(x, x) − B(Px, x)`. DERIVED: no numeral. -/
theorem proj_compl (hsymm : ∀ x y, B x y = B y x) {P : E →ₗ[ℝ] E}
    (hsa : ∀ x y, B (P x) y = B x (P y)) (hid : ∀ x, P (P x) = P x) (x : E) :
    B (x - P x) (x - P x) = B x x - B (P x) x := by
  have h := proj_sq hsymm hsa hid x
  simp only [map_sub, LinearMap.sub_apply]
  rw [hsymm x (P x)]
  linarith

/-- DERIVED: `0` the sign. -/
theorem proj_contract (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) {P : E →ₗ[ℝ] E}
    (hsa : ∀ x y, B (P x) y = B x (P y)) (hid : ∀ x, P (P x) = P x) (x : E) :
    B (P x) (P x) ≤ B x x := by
  have h1 := proj_compl hsymm hsa hid x
  have h2 := proj_sq hsymm hsa hid x
  have h3 := hnn (x - P x)
  linarith

/-- **The average is self-adjoint.** DERIVED: no numeral. -/
theorem avgT_selfAdj (P : Z → E →ₗ[ℝ] E) (hsa : ∀ z x y, B (P z x) y = B x (P z y)) (x y : E) :
    B (avgT P x) y = B x (avgT P y) := by
  rw [avgT_apply, avgT_apply, form_smul_sum_left, form_smul_sum_right]
  congr 1
  exact Finset.sum_congr rfl fun z _ => hsa z x y

/-- **The average is a contraction.** DERIVED: `2` the cross term. -/
theorem avgT_contract (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x)
    (P : Z → E →ₗ[ℝ] E) (hsa : ∀ z x y, B (P z x) y = B x (P z y)) (hid : ∀ z x, P z (P z x) = P z x)
    (x : E) : B (avgT P x) (avgT P x) ≤ B x x := by
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · rw [avgT_apply]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, map_zero]
    exact hnn x
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (Fintype.card Z : ℝ)⁻¹ = c := ⟨_, rfl⟩
  have hZp : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hcZ : c * (Fintype.card Z : ℝ) = 1 := by rw [← hc]; exact inv_mul_cancel₀ hZp.ne'
  have hpair : ∀ z w, 2 * B (P z x) (P w x) ≤ B (P z x) (P z x) + B (P w x) (P w x) := by
    intro z w
    have h := hnn (P z x - P w x)
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [hsymm (P w x) (P z x)] at h
    linarith
  have e : B (avgT P x) (avgT P x) = c * c * ∑ z, ∑ w, B (P z x) (P w x) := by
    rw [avgT_apply, form_smul_sum_left, hc]
    simp only [form_smul_sum_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hsum : 2 * ∑ z, ∑ w, B (P z x) (P w x)
      ≤ 2 * ((Fintype.card Z : ℝ) * ∑ z, B (P z x) (P z x)) := by
    have : 2 * ∑ z, ∑ w, B (P z x) (P w x)
        ≤ ∑ z, ∑ w, (B (P z x) (P z x) + B (P w x) (P w x)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun z _ => by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun w _ => hpair z w
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun z _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hsum' : ∑ z, ∑ w, B (P z x) (P w x) ≤ (Fintype.card Z : ℝ) * ∑ z, B (P z x) (P z x) := by
    linarith
  have hdiag : ∑ z, B (P z x) (P z x) ≤ (Fintype.card Z : ℝ) * B x x := by
    calc ∑ z, B (P z x) (P z x) ≤ ∑ _z : Z, B x x :=
          Finset.sum_le_sum fun z _ => proj_contract hsymm hnn (hsa z) (hid z) x
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc0 : 0 ≤ c := by rw [← hc]; positivity
  rw [e]
  calc c * c * ∑ z, ∑ w, B (P z x) (P w x)
      ≤ c * c * ((Fintype.card Z : ℝ) * ∑ z, B (P z x) (P z x)) :=
        mul_le_mul_of_nonneg_left hsum' (mul_nonneg hc0 hc0)
    _ ≤ c * c * ((Fintype.card Z : ℝ) * ((Fintype.card Z : ℝ) * B x x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiag hZp.le) (mul_nonneg hc0 hc0)
    _ = (c * Fintype.card Z) * (c * Fintype.card Z) * B x x := by ring
    _ = B x x := by rw [hcZ]; ring

#print axioms avgT_contract

/-- **The step bound gives the Poincaré inequality of the projections.**

DERIVED: `2` the square; `1` the contraction's unit. -/
theorem poincare_of_step (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x)
    (P : Z → E →ₗ[ℝ] E) (hsa : ∀ z x y, B (P z x) y = B x (P z y)) (hid : ∀ z x, P z (P z x) = P z x)
    {r : ℝ} (hr : 0 ≤ r) (x : E) (hstep : B (avgT P x) (avgT P x) ≤ r ^ 2 * B x x) :
    (1 - r) * Fintype.card Z * B x x ≤ ∑ z, B (x - P z x) (x - P z x) := by
  have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul B hsymm hnn (avgT P x) x
  have hTx : B (avgT P x) x ≤ r * B x x := by
    have hb : 0 ≤ r * B x x := mul_nonneg hr (hnn x)
    have hsq : B (avgT P x) x ^ 2 ≤ (r * B x x) ^ 2 := by
      calc B (avgT P x) x ^ 2 ≤ B (avgT P x) (avgT P x) * B x x := hcs
        _ ≤ r ^ 2 * B x x * B x x := mul_le_mul_of_nonneg_right hstep (hnn x)
        _ = (r * B x x) ^ 2 := by ring
    by_contra h
    have h' := lt_of_not_ge h
    nlinarith
  have e : ∑ z, B (x - P z x) (x - P z x)
      = (Fintype.card Z : ℝ) * B x x - (Fintype.card Z : ℝ) * B (avgT P x) x := by
    rw [Finset.sum_congr rfl fun z _ => proj_compl hsymm (hsa z) (hid z) x, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, avgT_apply, form_smul_sum_left]
    rcases isEmpty_or_nonempty Z with hZ | hZ
    · simp
    · have hZp : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
      rw [← mul_assoc, mul_inv_cancel₀ hZp.ne', one_mul]
  rw [e]
  have hZ0 : (0 : ℝ) ≤ Fintype.card Z := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hTx hZ0]

#print axioms poincare_of_step

end Proj

/-! ## 3. A decay rate on a dense set gives the step -/

section Dense

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- **The transfer data of a self-adjoint contraction keeping a unit vacuum.**

DERIVED: `1` the normalisation. -/
def toTD (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (T : E →ₗ[ℝ] E)
    (hTs : ∀ x y, B (T x) y = B x (T y)) (hTc : ∀ x, B (T x) (T x) ≤ B x x) (vac : E)
    (hTv : T vac = vac) (hvac : B vac vac = 1) : Transfer.TransferData E where
  form x y := B x y
  form_symm := hsymm
  form_add_left x y z := by simp only [map_add, LinearMap.add_apply]
  form_smul_left r x y := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  form_nonneg := hnn
  T := T
  vac := vac
  T_symm := hTs
  T_contract := hTc
  T_vac := hTv
  vac_norm := hvac

/-- **A decay rate on a dense set closed under removing the vacuum gives the one-step bound on the vacuum
complement.**

DERIVED: `2` the square and the doubling of the approximation error; `1` the vacuum norm. -/
theorem step_of_dense_rate (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (T : E →ₗ[ℝ] E)
    (hTs : ∀ x y, B (T x) y = B x (T y)) (hTc : ∀ x, B (T x) (T x) ≤ B x x) (vac : E)
    (hTv : T vac = vac) (hvac : B vac vac = 1) {r : ℝ} (hr : 0 ≤ r) (D : Set E)
    (hDsub : ∀ x ∈ D, ∀ c : ℝ, x - c • vac ∈ D)
    (hrate : ∀ x ∈ D, B x vac = 0 → ∃ K : ℝ, ∀ n : ℕ, B ((T ^ n) x) ((T ^ n) x) ≤ K * r ^ (2 * n))
    (hdense : ∀ x : E, ∀ ε > 0, ∃ y ∈ D, B (x - y) (x - y) ≤ ε ^ 2)
    (x : E) (hx : B x vac = 0) : B (T x) (T x) ≤ r ^ 2 * B x x := by
  set D' := toTD hsymm hnn T hTs hTc vac hTv hvac
  -- the step on `D ∩ vac⊥`, in seminorm form
  have hstepD : ∀ y ∈ D, B y vac = 0 → nn B (T y) ≤ r * nn B y := by
    intro y hy hyv
    obtain ⟨K, hK⟩ := hrate y hy hyv
    have h := ScaleStep.step_le_of_rate D' hr (x := y) (K := K) hK
    have h' : B (T y) (T y) ≤ r ^ 2 * B y y := h
    unfold nn
    rw [← Real.sqrt_sq hr, ← Real.sqrt_mul (sq_nonneg r)]
    exact Real.sqrt_le_sqrt h'
  have hTnn : ∀ y, nn B (T y) ≤ nn B y := fun y => Real.sqrt_le_sqrt (hTc y)
  have hnv : nn B vac = 1 := by unfold nn; rw [hvac, Real.sqrt_one]
  have hneg : ∀ y, nn B (-y) = nn B y := fun y => by
    rw [show -y = (-1 : ℝ) • y by simp, nn_smul]; simp
  have hsub : ∀ a b, nn B (a - b) ≤ nn B a + nn B b := fun a b => by
    rw [sub_eq_add_neg]; exact (nn_add_le hsymm hnn a (-b)).trans (by rw [hneg])
  have key : ∀ ε > 0, nn B (T x) ≤ r * nn B x + (r + 1) * (2 * ε) := by
    intro ε hε
    obtain ⟨y, hyD, hy⟩ := hdense x ε hε
    have hxy : nn B (x - y) ≤ ε := by
      unfold nn
      calc Real.sqrt (B (x - y) (x - y)) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hy
        _ = ε := Real.sqrt_sq hε.le
    set c := B y vac with hc
    set y' := y - c • vac with hy'
    have hy'D : y' ∈ D := hDsub y hyD c
    have hy'v : B y' vac = 0 := by
      simp only [hy', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hvac]
      ring
    have hcabs : |c| ≤ ε := by
      have e : c = B (y - x) vac := by
        simp only [hc, map_sub, LinearMap.sub_apply, hx, sub_zero]
      rw [e]
      calc |B (y - x) vac| ≤ nn B (y - x) * nn B vac := abs_form_le hsymm hnn _ _
        _ = nn B (x - y) := by rw [hnv, mul_one, ← neg_sub, hneg]
        _ ≤ ε := hxy
    have hd : nn B (x - y') ≤ 2 * ε := by
      have e : x - y' = (x - y) + c • vac := by simp only [hy']; abel
      rw [e]
      calc nn B ((x - y) + c • vac) ≤ nn B (x - y) + nn B (c • vac) := nn_add_le hsymm hnn _ _
        _ = nn B (x - y) + |c| := by rw [nn_smul, hnv, mul_one]
        _ ≤ 2 * ε := by linarith
    have hy'n : nn B y' ≤ nn B x + nn B (x - y') := by
      have h := hsub x (x - y')
      rwa [sub_sub_cancel] at h
    have eT : T x = T y' + T (x - y') := by rw [← map_add]; congr 1; abel
    calc nn B (T x) = nn B (T y' + T (x - y')) := by rw [eT]
      _ ≤ nn B (T y') + nn B (T (x - y')) := nn_add_le hsymm hnn _ _
      _ ≤ r * nn B y' + nn B (x - y') := add_le_add (hstepD y' hy'D hy'v) (hTnn _)
      _ ≤ r * (nn B x + nn B (x - y')) + nn B (x - y') := by
          have := mul_le_mul_of_nonneg_left hy'n hr; linarith
      _ = r * nn B x + (r + 1) * nn B (x - y') := by ring
      _ ≤ r * nn B x + (r + 1) * (2 * ε) := by
          have := mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ r + 1); linarith
  have hfin : nn B (T x) ≤ r * nn B x := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hr1 : (0 : ℝ) < 2 * (r + 1) := by linarith
    have h := key (η / (2 * (r + 1))) (div_pos hη hr1)
    have e : (r + 1) * (2 * (η / (2 * (r + 1)))) = η := by field_simp
    linarith
  have h0 : 0 ≤ nn B (T x) := nn_nonneg _
  calc B (T x) (T x) = nn B (T x) ^ 2 := (nn_sq hnn _).symm
    _ ≤ (r * nn B x) ^ 2 := pow_le_pow_left₀ h0 hfin 2
    _ = r ^ 2 * B x x := by rw [mul_pow, nn_sq hnn]

#print axioms step_of_dense_rate

end Dense

/-! ## 4. Lipschitz functions are dense -/

section Lip

variable {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **A continuous separating metric cost at each link.**

DERIVED: `0` the diagonal and the separation. -/
structure CostMetric (d : Lk → Ω → Ω → ℝ) : Prop where
  cont : ∀ l, Continuous (fun p : Ω × Ω => d l p.1 p.2)
  nonneg : ∀ l a b, 0 ≤ d l a b
  refl : ∀ l a, d l a a = 0
  sep : ∀ l a b, d l a b = 0 → a = b
  symm : ∀ l a b, d l a b = d l b a
  tri : ∀ l a b c, d l a c ≤ d l a b + d l b c

/-- **The functions with a finite Lipschitz vector form a subalgebra.**

DERIVED: `0` the vector of a constant. -/
def lipSub (d : Lk → Ω → Ω → ℝ) : Subalgebra ℝ C(Lk → Ω, ℝ) where
  carrier := {g | ∃ v, LipD d (g : (Lk → Ω) → ℝ) v}
  mul_mem' := by
    rintro g h ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨fun k => ‖g‖ * w k + ‖h‖ * v k,
      ⟨fun k => add_nonneg (mul_nonneg (norm_nonneg _) (hw.1 k)) (mul_nonneg (norm_nonneg _) (hv.1 k)),
        fun W k x => ?_⟩⟩
    simp only [ContinuousMap.mul_apply]
    have hg := ContinuousMap.norm_coe_le_norm g (Function.update W k x)
    have hh := ContinuousMap.norm_coe_le_norm h W
    rw [Real.norm_eq_abs] at hg hh
    have e : g (Function.update W k x) * h (Function.update W k x) - g W * h W
        = g (Function.update W k x) * (h (Function.update W k x) - h W)
          + h W * (g (Function.update W k x) - g W) := by ring
    rw [e]
    calc _ ≤ |g (Function.update W k x) * (h (Function.update W k x) - h W)|
          + |h W * (g (Function.update W k x) - g W)| := abs_add_le _ _
      _ = |g (Function.update W k x)| * |h (Function.update W k x) - h W|
          + |h W| * |g (Function.update W k x) - g W| := by rw [abs_mul, abs_mul]
      _ ≤ ‖g‖ * (w k * d k x (W k)) + ‖h‖ * (v k * d k x (W k)) :=
          add_le_add (mul_le_mul hg (hw.2 W k x) (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul hh (hv.2 W k x) (abs_nonneg _) (norm_nonneg _))
      _ = (‖g‖ * w k + ‖h‖ * v k) * d k x (W k) := by ring
  add_mem' := by
    rintro g h ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨fun k => v k + w k, ⟨fun k => add_nonneg (hv.1 k) (hw.1 k), fun W k x => ?_⟩⟩
    simp only [ContinuousMap.add_apply]
    have e : g (Function.update W k x) + h (Function.update W k x) - (g W + h W)
        = (g (Function.update W k x) - g W) + (h (Function.update W k x) - h W) := by ring
    rw [e]
    calc _ ≤ |g (Function.update W k x) - g W| + |h (Function.update W k x) - h W| := abs_add_le _ _
      _ ≤ v k * d k x (W k) + w k * d k x (W k) := add_le_add (hv.2 W k x) (hw.2 W k x)
      _ = (v k + w k) * d k x (W k) := by ring
  algebraMap_mem' := by
    intro c
    refine ⟨fun _ => 0, ⟨fun _ => le_rfl, fun W k x => ?_⟩⟩
    simp

omit [Fintype Lk] in
/-- **The Lipschitz subalgebra separates points.** DERIVED: `1` the indicator vector. -/
theorem lipSub_separates {d : Lk → Ω → Ω → ℝ} (hd : CostMetric d) : (lipSub d).SeparatesPoints := by
  intro W W' hne
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have h2 : Continuous (fun U : Lk → Ω => (U k, W' k)) :=
    (continuous_apply k).prodMk continuous_const
  have hc : Continuous (fun U : Lk → Ω => d k (U k) (W' k)) := (hd.cont k).comp h2
  refine ⟨fun U => d k (U k) (W' k), ⟨⟨_, hc⟩, ⟨fun l => if l = k then 1 else 0, ⟨fun l => ?_, fun U l x => ?_⟩⟩,
    rfl⟩, ?_⟩
  · dsimp only; split_ifs <;> norm_num
  · show |d k (Function.update U l x k) (W' k) - d k (U k) (W' k)| ≤ _
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self]; dsimp only; rw [if_pos rfl, one_mul, abs_sub_le_iff]
      constructor
      · have := hd.tri l x (U l) (W' l); linarith
      · have h1 := hd.tri l (U l) x (W' l)
        rw [hd.symm l (U l) x] at h1
        linarith
    · rw [Function.update_of_ne (Ne.symm hl), sub_self, abs_zero]; dsimp only; rw [if_neg hl, zero_mul]
  · show d k (W k) (W' k) ≠ d k (W' k) (W' k)
    rw [hd.refl]
    exact fun h => hk (hd.sep k _ _ h)

#print axioms lipSub_separates

omit [Fintype Lk] in
/-- **Stone–Weierstrass for Lipschitz functions**: every continuous function is a uniform limit of functions
with a finite Lipschitz vector.

DERIVED: no numeral. -/
theorem lip_dense {d : Lk → Ω → Ω → ℝ} (hd : CostMetric d) (f : C(Lk → Ω, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(Lk → Ω, ℝ), (∃ v, LipD d (g : (Lk → Ω) → ℝ) v) ∧ ∀ W, |g W - f W| < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (lipSub d) (lipSub_separates hd) f f.continuous ε hε
  exact ⟨g, g.2, fun W => by have := hg W; rwa [Real.norm_eq_abs] at this⟩

#print axioms lip_dense

omit [DecidableEq Lk] in
/-- **A continuous cost on a compact space is bounded.** DERIVED: `0` the sign. -/
theorem CostMetric.bdd [Nonempty Ω] {d : Lk → Ω → Ω → ℝ} (hd : CostMetric d) :
    ∃ Dm : ℝ, 0 ≤ Dm ∧ ∀ l a b, d l a b ≤ Dm := by
  have h : ∀ l, ∃ C : ℝ, ∀ p : Ω × Ω, |d l p.1 p.2| ≤ C := fun l => HeatBath.exists_abs_le (hd.cont l)
  choose C hC using h
  refine ⟨∑ l, max (C l) 0, Finset.sum_nonneg fun l _ => le_max_right _ _, fun l a b => ?_⟩
  calc d l a b ≤ |d l a b| := le_abs_self _
    _ ≤ C l := hC l (a, b)
    _ ≤ max (C l) 0 := le_max_left _ _
    _ ≤ ∑ l, max (C l) 0 := Finset.single_le_sum (f := fun l => max (C l) 0)
        (fun l _ => le_max_right _ _) (Finset.mem_univ l)

#print axioms CostMetric.bdd

end Lip

/-! ## 5. The periodic Wilson state -/

section Wilson

open MassGap.KnabeCriterion MassGap.HeatBath MassGap.HeatBathLocal MassGap.BlockHeatBath
open MassGap.PeriodicState (torusObs torusState)
open MassGap.TileSweep (TE)
open MassGap.SUN (SU)

variable {N : ℕ}

/-- The configuration space of the infinite lattice. -/
local notation "IC" => GibbsSpec.IConf (SU N)

/-- **The form of the periodic state on all continuous observables.** DERIVED: `2 * j + 1` the index. -/
def formE (hN : N ≠ 0) (β : ℝ) (j : ℕ) : C(IC, ℝ) →ₗ[ℝ] C(IC, ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => torusState hN (2 * j + 1) β (x * y))
    (fun x₁ x₂ y => by simp only [add_mul, DLRLimit.State.map_add])
    (fun c x y => by simp only [smul_mul_assoc, DLRLimit.State.map_smul, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [mul_add, DLRLimit.State.map_add])
    (fun c x y => by simp only [mul_smul_comm, DLRLimit.State.map_smul, smul_eq_mul])

/-- DERIVED: no numeral. -/
theorem formE_apply (hN : N ≠ 0) (β : ℝ) (j : ℕ) (x y : C(IC, ℝ)) :
    formE hN β j x y = torusState hN (2 * j + 1) β (x * y) := rfl

/-- DERIVED: no numeral. -/
theorem formE_symm (hN : N ≠ 0) (β : ℝ) (j : ℕ) (x y : C(IC, ℝ)) :
    formE hN β j x y = formE hN β j y x := by
  rw [formE_apply, formE_apply, mul_comm x y]

/-- DERIVED: `0` the sign. -/
theorem formE_nonneg (hN : N ≠ 0) (β : ℝ) (j : ℕ) (x : C(IC, ℝ)) : 0 ≤ formE hN β j x x := by
  rw [formE_apply]
  exact DLRLimit.State.nonneg _ _ fun U => by
    simp only [ContinuousMap.mul_apply]; exact mul_self_nonneg _

/-- DERIVED: `1` the constant. -/
theorem formE_one_one (hN : N ≠ 0) (β : ℝ) (j : ℕ) : formE hN β j (1 : C(IC, ℝ)) 1 = 1 := by
  rw [formE_apply, mul_one]
  exact DLRLimit.State.map_one _

/-- **A torus function lifted to the infinite lattice.** DERIVED: `1` the successor writing the extent. -/
def liftT (M : ℕ) (g : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)) : C(IC, ℝ) :=
  ⟨fun U => g (restrictConf M U), g.continuous.comp (continuous_restrictConf M)⟩

/-- DERIVED: `1` the successor writing the extent. -/
theorem torusObs_liftT (M : ℕ) (g : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)) :
    torusObs M (liftT M g) = g := by
  funext W
  show g (restrictConf M (InfiniteLattice.pullback M W)) = g W
  rw [restrictConf_pullback]

/-- **The periodic state is bounded by a pointwise bound on the torus reading.**

DERIVED: `2 * j + 1` the index. -/
theorem state_le (hN : N ≠ 0) (β : ℝ) (j : ℕ) (F : C(IC, ℝ)) {K : ℝ}
    (hK : ∀ W, torusObs (2 * j + 1) F W ≤ K) : torusState hN (2 * j + 1) β F ≤ K := by
  set g : C(WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N, ℝ) :=
    ⟨torusObs (2 * j + 1) F, continuous_torusObs _ F⟩
  have e : torusState hN (2 * j + 1) β F = torusState hN (2 * j + 1) β (liftT (2 * j + 1) g) := by
    show ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β (torusObs (2 * j + 1) F)
      = ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β (torusObs (2 * j + 1) (liftT (2 * j + 1) g))
    rw [torusObs_liftT]
    rfl
  rw [e]
  calc torusState hN (2 * j + 1) β (liftT (2 * j + 1) g)
      ≤ torusState hN (2 * j + 1) β (K • (1 : C(IC, ℝ))) :=
        DLRLimit.State.mono _ fun U => by
          simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
          exact hK _
    _ = K := by rw [DLRLimit.State.map_smul, DLRLimit.State.map_one, mul_one]

#print axioms state_le

/-- **The block average as a linear map of all observables.** DERIVED: `1` the successor. -/
def blkL (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) : C(IC, ℝ) →ₗ[ℝ] C(IC, ℝ) where
  toFun F := blkLift β M S F
  map_add' x y := by
    apply ContinuousMap.ext
    intro U
    show blkAvg (bdT M) β S (torusObs M (x + y)) (restrictConf M U)
      = blkAvg (bdT M) β S (torusObs M x) (restrictConf M U)
        + blkAvg (bdT M) β S (torusObs M y) (restrictConf M U)
    exact blkAvg_add (bdT M) β S (continuous_torusObs M _) (continuous_torusObs M _) (restrictConf M U)
  map_smul' c x := by
    apply ContinuousMap.ext
    intro U
    show blkAvg (bdT M) β S (torusObs M (c • x)) (restrictConf M U)
      = c * blkAvg (bdT M) β S (torusObs M x) (restrictConf M U)
    exact blkAvg_const_mul (bdT M) β S c _ (restrictConf M U)

/-- DERIVED: `1` the successor. -/
theorem torusObs_blkL (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (F : C(IC, ℝ)) :
    torusObs M (blkL β M S F) = blkAvg (bdT M) β S (torusObs M F) :=
  torusObs_blkLift β M S F

/-- DERIVED: `2 * j + 1` the index. -/
theorem blkL_selfAdj (hN : N ≠ 0) (β : ℝ) (j : ℕ) (S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    (x y : C(IC, ℝ)) :
    formE hN β j (blkL β (2 * j + 1) S x) y = formE hN β j x (blkL β (2 * j + 1) S y) := by
  rw [formE_apply, formE_apply]
  show ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) (blkL β (2 * j + 1) S x) W * torusObs (2 * j + 1) y W)
    = ReflectPositive.EW (d := 4) (n := 2 * j + 1 + 1) N β
      (fun W => torusObs (2 * j + 1) x W * torusObs (2 * j + 1) (blkL β (2 * j + 1) S y) W)
  rw [torusObs_blkL, torusObs_blkL]
  exact expect_blkAvg_mul (bdT (2 * j + 1)) β S (continuous_torusObs _ _) (continuous_torusObs _ _)

#print axioms blkL_selfAdj

/-- DERIVED: `1` the successor. -/
theorem blkL_idem (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (x : C(IC, ℝ)) :
    blkL β M S (blkL β M S x) = blkL β M S x := by
  apply ContinuousMap.ext
  intro U
  show blkAvg (bdT M) β S (torusObs M (blkLift β M S x)) (restrictConf M U)
    = blkAvg (bdT M) β S (torusObs M x) (restrictConf M U)
  rw [torusObs_blkLift]
  exact blkAvg_of_readsNot (bdT M) β S (fun W V => blkAvg_glue (bdT M) β S _ W V) _

#print axioms blkL_idem

/-- DERIVED: `1` the constant. -/
theorem blkL_one (β : ℝ) (M : ℕ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) :
    blkL β M S (1 : C(IC, ℝ)) = 1 := by
  apply ContinuousMap.ext
  intro U
  show blkAvg (bdT M) β S (torusObs M (1 : C(IC, ℝ))) (restrictConf M U) = 1
  exact blkAvg_of_readsNot (bdT M) β S (f := torusObs M (1 : C(IC, ℝ))) (fun _ _ => rfl) _

#print axioms blkL_one

variable {Z : Type} [Fintype Z]

/-- **The torus reading of the averaged dynamics is the averaged block kernel.**

DERIVED: `1` the successor. -/
theorem torusObs_avgT (β : ℝ) (M : ℕ) (S : Z → Finset (WilsonHypercubic.Link 4 (M + 1))) (F : C(IC, ℝ)) :
    torusObs M (avgT (fun z => blkL β M (S z)) F)
      = avgQ (fun z => DSBlockContract.wilsonKer (N := N) (bdT M) β (S z)) (torusObs M F) := by
  funext W
  rw [avgT_apply]
  show ((Fintype.card Z : ℝ)⁻¹ • ∑ z, blkL β M (S z) F) (InfiniteLattice.pullback M W) = _
  rw [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]
  unfold avgQ
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  show blkAvg (bdT M) β (S z) (torusObs M F) (restrictConf M (InfiniteLattice.pullback M W))
    = blkAvg (bdT M) β (S z) (torusObs M F) W
  rw [restrictConf_pullback]

#print axioms torusObs_avgT

/-- DERIVED: `1` the successor. -/
theorem torusObs_avgT_pow (β : ℝ) (M : ℕ) (S : Z → Finset (WilsonHypercubic.Link 4 (M + 1)))
    (F : C(IC, ℝ)) : ∀ n : ℕ,
    torusObs M ((avgT (fun z => blkL β M (S z)) ^ n) F)
      = (avgQ (fun z => DSBlockContract.wilsonKer (N := N) (bdT M) β (S z)))^[n] (torusObs M F)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ', Module.End.mul_apply, torusObs_avgT, torusObs_avgT_pow β M S F n,
      Function.iterate_succ_apply']

#print axioms torusObs_avgT_pow

/-- **The translates' Poincaré inequality from the block influences.** Block averages over any family of torus
link sets `S z`, influence matrices `C z` in a continuous separating metric cost, and the column bound
`κ |Z| ≤ Σ_z gain_z l` at every link give `κ |Z| ‖u‖² ≤ Σ_z ‖u − E_z u‖²` on the vacuum complement.

DERIVED: `2 * j + 1` the index; `0`, `1` the range of `κ`; `2` the squares. -/
theorem translate_poincare (hN : N ≠ 0) (β : ℝ) (j : ℕ) [Nonempty Z]
    (S : Z → Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)))
    {d : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N → SU N → ℝ} (hd : CostMetric d)
    {C : Z → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ}
    (hC : ∀ z, BlkInfl (DSBlockContract.wilsonKer (bdT (2 * j + 1)) β (S z)) d (C z))
    (hC0 : ∀ z l k, 0 ≤ C z l k) {κ : ℝ} (hκ1 : κ ≤ 1)
    (hcol : ∀ l, κ * Fintype.card Z ≤ ∑ z, gain (S z) (C z) l)
    (u : TE N j) (hu : torusForm hN β j u (oneT j) = 0) :
    κ * Fintype.card Z * torusForm hN β j u u
      ≤ ∑ z, torusForm hN β j (u - torusBlkCondExp β (2 * j + 1) (S z) u)
          (u - torusBlkCondExp β (2 * j + 1) (S z) u) := by
  set B := formE (N := N) hN β j
  set P : Z → C(IC, ℝ) →ₗ[ℝ] C(IC, ℝ) := fun z => blkL β (2 * j + 1) (S z)
  set T := avgT P
  have hsymm := formE_symm (N := N) hN β j
  have hnn := formE_nonneg (N := N) hN β j
  have hsa : ∀ z x y, B (P z x) y = B x (P z y) := fun z x y => blkL_selfAdj hN β j (S z) x y
  have hid : ∀ z x, P z (P z x) = P z x := fun z x => blkL_idem β (2 * j + 1) (S z) x
  have hTs : ∀ x y, B (T x) y = B x (T y) := avgT_selfAdj P hsa
  have hTc : ∀ x, B (T x) (T x) ≤ B x x := avgT_contract hsymm hnn P hsa hid
  have hTv : T 1 = 1 := by
    show avgT P 1 = 1
    rw [avgT_apply]
    have hZp : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
    simp only [P, blkL_one, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hZp.ne', one_smul]
  have hvac : B 1 1 = 1 := formE_one_one hN β j
  obtain ⟨Dm, hDm0, hDm⟩ := hd.bdd
  -- the dense set: observables whose torus reading has a finite Lipschitz vector
  set D : Set C(IC, ℝ) := {F | ∃ v, LipD d (torusObs (2 * j + 1) F) v}
  have hDsub : ∀ x ∈ D, ∀ c : ℝ, x - c • (1 : C(IC, ℝ)) ∈ D := by
    rintro x ⟨v, hv⟩ c
    refine ⟨v, hv.1, fun W k y => ?_⟩
    have h := hv.2 W k y
    show |(x - c • 1) (InfiniteLattice.pullback _ (Function.update W k y))
      - (x - c • 1) (InfiniteLattice.pullback _ W)| ≤ _
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply]
    have e : x (InfiniteLattice.pullback (2 * j + 1) (Function.update W k y)) - c • (1 : ℝ)
        - (x (InfiniteLattice.pullback (2 * j + 1) W) - c • (1 : ℝ))
        = torusObs (2 * j + 1) x (Function.update W k y) - torusObs (2 * j + 1) x W := by
      simp only [torusObs]; ring
    rw [e]; exact h
  have hpowv : ∀ (x : C(IC, ℝ)) (n : ℕ), B ((T ^ n) x) 1 = B x 1 := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, hTs, hTv, ih]
  have hrate : ∀ x ∈ D, B x 1 = 0 →
      ∃ K : ℝ, ∀ n : ℕ, B ((T ^ n) x) ((T ^ n) x) ≤ K * (1 - κ) ^ (2 * n) := by
    rintro x ⟨v, hv⟩ hx
    refine ⟨((∑ k, v k) * Dm) ^ 2, fun n => ?_⟩
    set y := (T ^ n) x
    have hy1 : B y 1 = 0 := by rw [hpowv, hx]
    obtain ⟨W0⟩ : Nonempty (WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N) := inferInstance
    set c := torusObs (2 * j + 1) y W0
    have hexp : B y y ≤ B (y - c • 1) (y - c • 1) := by
      have e : B (y - c • 1) (y - c • 1) = B y y + c ^ 2 := by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hvac,
          hy1]
        rw [hsymm 1 y, hy1]
        ring
      rw [e]; nlinarith [sq_nonneg c]
    have hobs : torusObs (2 * j + 1) y
        = (avgQ (fun z => DSBlockContract.wilsonKer (N := N) (bdT (2 * j + 1)) β (S z)))^[n]
          (torusObs (2 * j + 1) x) := torusObs_avgT_pow β (2 * j + 1) S x n
    have hosc : ∀ W, |torusObs (2 * j + 1) y W - c| ≤ (1 - κ) ^ n * (∑ k, v k) * Dm := by
      intro W
      have h := osc_iter_le _ hd.nonneg hDm hDm0 hC hC0 hcol hκ1 n (continuous_torusObs _ x) hv W W0
      rw [← hobs] at h
      exact h
    have hb : B (y - c • 1) (y - c • 1) ≤ ((1 - κ) ^ n * (∑ k, v k) * Dm) ^ 2 := by
      rw [formE_apply]
      refine state_le hN β j _ fun W => ?_
      have h := hosc W
      have e : torusObs (2 * j + 1) ((y - c • 1) * (y - c • 1)) W
          = (torusObs (2 * j + 1) y W - c) ^ 2 := by
        simp only [torusObs, ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one]
        ring
      rw [e, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc B y y ≤ ((1 - κ) ^ n * (∑ k, v k) * Dm) ^ 2 := hexp.trans hb
      _ = ((∑ k, v k) * Dm) ^ 2 * (1 - κ) ^ (2 * n) := by rw [pow_mul']; ring
  have hdense : ∀ x : C(IC, ℝ), ∀ ε > 0, ∃ y ∈ D, B (x - y) (x - y) ≤ ε ^ 2 := by
    intro x ε hε
    obtain ⟨g, hgL, hg⟩ := lip_dense hd ⟨torusObs (2 * j + 1) x, continuous_torusObs _ x⟩ hε
    refine ⟨liftT (2 * j + 1) g, ?_, ?_⟩
    · show ∃ v, LipD d (torusObs (2 * j + 1) (liftT (2 * j + 1) g)) v
      rw [torusObs_liftT]; exact hgL
    · rw [formE_apply]
      refine state_le hN β j _ fun W => ?_
      have h := hg W
      have e : torusObs (2 * j + 1) ((x - liftT (2 * j + 1) g) * (x - liftT (2 * j + 1) g)) W
          = (g W - torusObs (2 * j + 1) x W) ^ 2 := by
        have h1 : liftT (2 * j + 1) g (InfiniteLattice.pullback (2 * j + 1) W) = g W := by
          have := congrFun (torusObs_liftT (2 * j + 1) g) W
          exact this
        simp only [torusObs, ContinuousMap.mul_apply, ContinuousMap.sub_apply, h1]
        ring
      rw [e, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
  have hr : (0 : ℝ) ≤ 1 - κ := by linarith
  have hstep := step_of_dense_rate hsymm hnn T hTs hTc 1 hTv hvac hr D hDsub hrate hdense (u : C(IC, ℝ))
    hu
  have hP := poincare_of_step hsymm hnn P hsa hid hr (u : C(IC, ℝ)) hstep
  have e1 : B (u : C(IC, ℝ)) (u : C(IC, ℝ)) = torusForm hN β j u u := rfl
  have e2 : ∀ z, B ((u : C(IC, ℝ)) - P z u) ((u : C(IC, ℝ)) - P z u)
      = torusForm hN β j (u - torusBlkCondExp β (2 * j + 1) (S z) u)
          (u - torusBlkCondExp β (2 * j + 1) (S z) u) := fun z => rfl
  rw [← e1, Finset.sum_congr rfl fun z _ => (e2 z).symm]
  have e3 : (1 - (1 - κ)) * (Fintype.card Z : ℝ) = κ * Fintype.card Z := by ring
  rw [e3] at hP
  exact hP

#print axioms translate_poincare

end Wilson

end MassGap.DSOllivier
