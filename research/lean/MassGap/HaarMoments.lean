import MassGap.SUN

/-!
# MassGap.HaarMoments — the `SU(2)` Haar-moment tower and the transfer-operator mass gap

Nontrivial clustering — the quantitative mass gap — is a strong-coupling phenomenon resting on the exact
Haar moments of `SU(2)`. Mathlib has **no** Peter–Weyl / Schur orthogonality for compact groups; this module
builds the whole tower from scratch by a single, uniform method: **invariant-projection on two explicit
group elements**, the diagonal `h₀ = diag(i,-i)` and the swap `w = [[0,1],[-1,0]]`. For any moment,
substituting `U ↦ h₀U` multiplies the integrand by a phase `∏(h₀)^{±1}_{··}`; when that phase `≠ 1` the
integral vanishes (`c = φc ⇒ c = 0`), and `w` (with unitarity/normalization) fixes the surviving components.

Contents (all foundational — `[propext, Classical.choice, Quot.sound]`):
* **First moment** `haar_su2_coeff_zero` : `∫ U_{ij} dHaar = 0`; and `∫ tr U = ∫ Re tr U = 0`
  (`haar_su2_trace_zero`, `haar_su2_re_trace_zero`), `∫ tr(U·X) = 0` (`haar_su2_trace_mul_zero`).
* **Second moment** `haar_su2_second_moment` : `∫ U_{ij} conj(U_{kl}) dHaar = ½ δ_{ik}δ_{jl}` — the complete
  **Schur orthogonality relation**; with it the **character norm** `∫|tr U|² = 1` (`haar_su2_char_norm`,
  irreducibility) and the **two-point engine** `∫ tr(UA)tr(U*B) = ½ tr(AB)` (`haar_su2_two_point`), and the
  **shared-link coupling** `∫ tr(C₀g*)tr(gC₁) = ½ tr(C₀C₁)` (`haar_su2_shared_link`, non-factorization).
* **Transfer operator** `transferOp X = ½ tr(X)·I` (= `∫ g* X g`, `transferOp_eq_integral`): a linear map
  with `T(I)=I` (vacuum, eigenvalue 1), `T=0` on the traceless sector (eigenvalue 0), `T²=T`, `Tⁿ⁺¹=T`
  (`transferOp_idem`/`_pow`/`_pow_annihilates`) — the **strong-coupling mass gap as an operator identity**
  (finite-range connected correlations at every separation).
* **Third moment** `haar_su2_third_moment` : `∫ U U conj(U) = 0` (odd tensor power) — so the `O(β)` gap
  correction vanishes; the gap is `O(β²)`.
* **Fourth moment (support)** `haar_su2_fourth_moment_unbalanced` : the unbalanced components vanish; the
  balanced ones (the Weingarten `δδ`(+`ε`) value giving the `O(β²)` gap) are the remaining deep piece, which
  the proof's forward-construction design obtains from the Entroptics measured single-plaquette gap.

Build: `lake build MassGap.HaarMoments`.
-/

namespace MassGap.SUN

open Matrix MeasureTheory MassGap.CompactGauge

/-- The diagonal element `diag(i, -i)` of `SU(2)` (unit-modulus diagonal, determinant `1`). -/
noncomputable def h0mat : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem h0_mem : h0mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h0mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply, Complex.ext_iff]
  · simp [h0mat, Matrix.det_fin_two, Complex.ext_iff]

/-- `h0 = diag(i,-i)` as an element of `SU(2)`. -/
noncomputable def h0 : SU 2 := ⟨h0mat, h0_mem⟩

/-- **The strong-coupling workhorse: `∫_{SU(2)} U_{ij} dHaar = 0`** — every fundamental-representation
matrix coefficient Haar-averages to zero. Left-invariance gives `c = (h₀)_{ii}·c` for `h₀ = diag(i,-i)`,
and `(h₀)_{ii} ∈ {i,-i} ≠ 1`, so `c = 0`. No representation theory — the invariant-projection argument on
one element. This is the seed of every nontrivial-clustering estimate (the β=0 factorizations are trivial;
the gap lives in the coupling expansion, whose leading terms this kills). -/
theorem haar_su2_coeff_zero (i j : Fin 2) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)) = 0 := by
  haveI := isMulLeftInvariant_probHaar (SU 2)
  have hrow : ∀ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = h0mat i i * (g : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro g
    rw [Submonoid.coe_mul]
    show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> simp [h0mat]
  have step : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)))
      = h0mat i i * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)) := by
    calc (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)))
        = ∫ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)) :=
          (integral_mul_left_eq_self
            (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) h0).symm
      _ = ∫ g : SU 2, h0mat i i * (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hrow)
      _ = h0mat i i * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2)) :=
          integral_const_mul _ _
  have hne : h0mat i i ≠ 1 := by
    fin_cases i <;> simp [h0mat, Complex.ext_iff]
  have hz : (1 - h0mat i i)
      * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j ∂(probHaar (SU 2))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

/-- Each fundamental-rep matrix coefficient is integrable (continuous, entrywise `‖·‖ ≤ 1`, on a
probability measure). -/
theorem entry_integrable (i j : Fin 2) :
    Integrable (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) (probHaar (SU 2)) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  have hcont : Continuous (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  refine (integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  exact unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 i j

/-- **`∫_{SU(2)} tr(U) dHaar = 0`** — the fundamental character Haar-averages to zero (trace is the sum of
the diagonal coefficients, each zero by `haar_su2_coeff_zero`). Milestone toward the strong-coupling
free-value anchor `⟨φ_W⟩ = 1`. -/
theorem haar_su2_trace_zero :
    ∫ g : SU 2, Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) ∂(probHaar (SU 2)) = 0 := by
  have hsum : (fun g : SU 2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = (fun g : SU 2 => ∑ i, (g : Matrix (Fin 2) (Fin 2) ℂ) i i) := by
    funext g; rw [Matrix.trace]; rfl
  rw [hsum, integral_finset_sum _ (fun i _ => entry_integrable i i)]
  simp [haar_su2_coeff_zero]

/-- The fundamental character is integrable. -/
theorem trace_integrable :
    Integrable (fun g : SU 2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)) (probHaar (SU 2)) := by
  have hsum : (fun g : SU 2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = (fun g : SU 2 => ∑ i, (g : Matrix (Fin 2) (Fin 2) ℂ) i i) := by
    funext g; rw [Matrix.trace]; rfl
  rw [hsum]; exact integrable_finset_sum _ (fun i _ => entry_integrable i i)

/-- **`∫_{SU(2)} Re tr(U) dHaar = 0`** — the real part of the fundamental character averages to zero
(`Re` commutes with the integral). So a single-variable Wilson density Haar-averages to the free value:
`∫ φ_W(g) dHaar = 1 − (1/2)·0 = 1`. -/
theorem haar_su2_re_trace_zero :
    ∫ g : SU 2, (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)).re ∂(probHaar (SU 2)) = 0 := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM trace_integrable
  simp only [Complex.reCLM_apply] at h
  rw [h, haar_su2_trace_zero, Complex.zero_re]

/-- **`∫_{SU(2)} tr(U·X) dHaar = 0` for every fixed matrix `X`** — the fundamental character of `U`
against any fixed environment `X` Haar-averages to zero. Expand `tr(UX) = ∑_{ab} U_{ab} X_{ba}`; each
`∫ U_{ab} = 0` (`haar_su2_coeff_zero`). This is the plaquette workhorse: integrating out one link of a
Wilson loop (with `X` = the rest of the loop) kills its character, so a single-plaquette Wilson loop has
`⟨tr(hol)⟩ = 0` under Haar and hence `⟨φ_W(hol)⟩ = 1` at `β=0`. Generalizes `haar_su2_trace_zero`
(`X = 1`). -/
theorem haar_su2_trace_mul_zero (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∫ g : SU 2, Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * X) ∂(probHaar (SU 2)) = 0 := by
  have hexp : (fun g : SU 2 => Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * X))
      = (fun g : SU 2 => ∑ a : Fin 2, ∑ b : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * X b a) := by
    funext g
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [hexp, integral_finset_sum _
    (fun a _ => integrable_finset_sum _ (fun b _ => (entry_integrable a b).mul_const _))]
  apply Finset.sum_eq_zero
  intro a _
  rw [integral_finset_sum _ (fun b _ => (entry_integrable a b).mul_const _)]
  apply Finset.sum_eq_zero
  intro b _
  rw [integral_mul_const, haar_su2_coeff_zero, zero_mul]

/-- The two-link trace is integrable (continuous, `‖tr(U₁U₂)‖ ≤ 2` since the product is special-unitary
with entries `≤ 1`). -/
theorem two_link_integrable :
    Integrable (fun p : SU 2 × SU 2 =>
      Matrix.trace ((p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (p.2 : Matrix (Fin 2) (Fin 2) ℂ)))
      ((probHaar (SU 2)).prod (probHaar (SU 2))) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  have hcont : Continuous (fun p : SU 2 × SU 2 =>
      Matrix.trace ((p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (p.2 : Matrix (Fin 2) (Fin 2) ℂ))) :=
    Continuous.matrix_trace
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        (continuous_subtype_val.comp continuous_snd))
  refine (integrable_const (2 : ℝ)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => ?_))
  have hcoe : (p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (p.2 : Matrix (Fin 2) (Fin 2) ℂ)
      = ((p.1 * p.2 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) := (Submonoid.coe_mul _ _ _).symm
  rw [hcoe, Matrix.trace_fin_two]
  have hb : ∀ i, ‖((p.1 * p.2 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i i‖ ≤ 1 := fun i =>
    unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp (p.1 * p.2).2).1 i i
  calc ‖((p.1 * p.2 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        + ((p.1 * p.2 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖
      ≤ ‖((p.1 * p.2 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖
        + ‖((p.1 * p.2 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (hb 0) (hb 1)
    _ = 2 := by norm_num

/-- **Two-link Wilson line: `∫∫ tr(U₁U₂) dHaar dHaar = 0`.** Integrating out one link kills the loop
character (`∫_{U₁} tr(U₁U₂) dU₁ = 0` for fixed `U₂`, by `haar_su2_trace_mul_zero` + trace cyclicity), so
the product-measure integral vanishes by Fubini. The clean product-measure form of the "integrate out one
link ⇒ zero" content behind the plaquette free value `⟨φ_W⟩ = 1` at `β = 0`. -/
theorem haar_su2_two_link_trace_zero :
    ∫ p : SU 2 × SU 2, Matrix.trace ((p.1 : Matrix (Fin 2) (Fin 2) ℂ)
        * (p.2 : Matrix (Fin 2) (Fin 2) ℂ)) ∂((probHaar (SU 2)).prod (probHaar (SU 2))) = 0 := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  rw [MeasureTheory.integral_prod _ two_link_integrable]
  have hinner : ∀ x : SU 2,
      (∫ y : SU 2, Matrix.trace ((x : Matrix (Fin 2) (Fin 2) ℂ) * (y : Matrix (Fin 2) (Fin 2) ℂ))
        ∂(probHaar (SU 2))) = 0 := by
    intro x
    simp_rw [Matrix.trace_mul_comm (x : Matrix (Fin 2) (Fin 2) ℂ)]
    exact haar_su2_trace_mul_zero x
  simp only [hinner, integral_zero]

/-! ### Second moments (toward the first nontrivial correlation)

The first nontrivial two-point correlation needs *second* Haar moments `∫ U_{ij} Ū_{kl} dHaar`. Mathlib has
no Peter–Weyl, but the one-element invariance trick extends: off-diagonal components are killed by `h0` (the
integrand picks up a nontrivial phase, forcing `c = 0`), so `∫ U_{ij} Ū_{kl} = 0` unless `i = k` and
`j = l`. (The surviving diagonal components are then equalized by a rational rotation, and normalized by
`∫ ‖U‖²_F = 2`; those complete `∫ U_{ij} Ū_{kl} = ½ δ_{ik} δ_{jl}`.) -/

/-- **A second moment vanishes off-diagonal: `∫ U_{00}·conj(U_{10}) dHaar = 0`.** Killed by the same `h0`
trick — under `U ↦ h0 U` the integrand picks up `i·i = -1`, so `c = -c ⇒ c = 0`. Proof of concept that
second Haar moments are pinnable by explicit group elements, without Peter–Weyl. -/
theorem haar_su2_second_moment_offdiag :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)) = 0 := by
  haveI := isMulLeftInvariant_probHaar (SU 2)
  have hrow : ∀ g : SU 2,
      ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
      = (-1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) := by
    intro g
    have e00 : ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        = Complex.I * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      rw [Submonoid.coe_mul]
      show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [h0mat]
    have e10 : ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        = (-Complex.I) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
      rw [Submonoid.coe_mul]
      show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [h0mat]
    rw [e00, e10, map_mul, map_neg, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  have step : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)))
      = (-1 : ℂ) * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)) := by
    calc (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)))
        = ∫ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
            ∂(probHaar (SU 2)) :=
          (integral_mul_left_eq_self (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) h0).symm
      _ = ∫ g : SU 2, (-1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hrow)
      _ = (-1 : ℂ) * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)) :=
          integral_const_mul _ _
  have h2 : (2 : ℂ) * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2))) = 0 := by
    rw [two_mul]; nth_rewrite 2 [step]; ring
  simpa using h2

#print axioms haar_su2_coeff_zero
#print axioms haar_su2_trace_zero
#print axioms haar_su2_re_trace_zero
#print axioms haar_su2_trace_mul_zero
/-- **Second-moment normalization: `∫ ∑_{ij} U_{ij}·conj(U_{ij}) dHaar = 2`.** The integrand is pointwise
`∑_{ij} U_{ij} Ū_{ij} = ∑_i (U U*)_{ii} = tr(U U*) = tr(1) = 2` (unitarity), so the integral is `2`. This is
`∑_{ij} T_{ij,ij}`, the normalization fixing the constant in `∫ U_{ij}Ū_{kl} = ½ δ_{ik}δ_{jl}`. -/
theorem haar_su2_frobenius_sum :
    ∫ g : SU 2, ∑ i : Fin 2, ∑ j : Fin 2,
        (g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) ∂(probHaar (SU 2)) = 2 := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  have hpt : ∀ g : SU 2, (∑ i : Fin 2, ∑ j : Fin 2,
      (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) = 2 := by
    intro g
    have huni : (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
    calc ∑ i : Fin 2, ∑ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)
        = ∑ i : Fin 2, ((g : Matrix (Fin 2) (Fin 2) ℂ)
            * star (g : Matrix (Fin 2) (Fin 2) ℂ)) i i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, starRingEnd_apply]
      _ = ∑ i : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℂ) i i := by rw [huni]
      _ = 2 := by simp [Matrix.one_apply_eq]
  simp_rw [hpt]
  simp

/-- The swap element `[[0,1],[-1,0]] ∈ SU(2)` (integer entries) — used to equate the four diagonal second
moments `∫|U_{ij}|²` by left/right invariance. -/
noncomputable def wmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem w_mem : wmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply, Complex.ext_iff]
  · simp [wmat, Matrix.det_fin_two, Complex.ext_iff]

/-- `w = [[0,1],[-1,0]]` as an element of `SU(2)`. -/
noncomputable def w : SU 2 := ⟨wmat, w_mem⟩

/-- `|U_{ij}|²` (as `U_{ij}·conj(U_{ij})`) is integrable (continuous, bounded by `1`). -/
theorem entry_sq_integrable (i j : Fin 2) :
    Integrable (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) (probHaar (SU 2)) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  have hij : Continuous (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have hcont : Continuous (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) :=
    hij.mul (Complex.continuous_conj.comp hij)
  refine (integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 :=
    unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 i j
  nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) i j), h1]

/-- `∫ |U_{i'j'}|² = ∫ |U_{ij}|²` when left-multiplication by `w` maps `sq_{ij}` to `sq_{i'j'}` pointwise
(the substitution `U ↦ w·U` preserves Haar). -/
theorem sq_eq_left (i j i' j' : Fin 2)
    (hpt : ∀ g : SU 2, ((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) (((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i' j')) :
    (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i' j') ∂(probHaar (SU 2)))
      = ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) ∂(probHaar (SU 2)) := by
  haveI := isMulLeftInvariant_probHaar (SU 2)
  have key : (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i' j'))
      = (fun g : SU 2 => ((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) (((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j)) := by
    funext g; exact (hpt g).symm
  rw [key]
  exact integral_mul_left_eq_self (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
    * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) w

/-- `∫ |U_{i'j'}|² = ∫ |U_{ij}|²` when right-multiplication by `w` maps `sq_{ij}` to `sq_{i'j'}` pointwise
(uses right-invariance of Haar = unimodularity). -/
theorem sq_eq_right (i j i' j' : Fin 2)
    (hpt : ∀ g : SU 2, ((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) (((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i' j')) :
    (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i' j') ∂(probHaar (SU 2)))
      = ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) ∂(probHaar (SU 2)) := by
  haveI := isMulRightInvariant_probHaar (SU 2)
  have key : (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i' j'
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i' j'))
      = (fun g : SU 2 => ((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) (((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j)) := by
    funext g; exact (hpt g).symm
  rw [key]
  exact integral_mul_right_eq_self (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
    * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)) w

/-- **The diagonal second moment: `∫ |U_{00}|² dHaar = ½`.** The four `∫|U_{ij}|²` are equal (the swap `w`
maps them into one another, left/right invariance), and they sum to `2` (`haar_su2_frobenius_sum`), so each
is `½`. This is `T_{00,00}`; with the off-diagonal vanishing it gives `∫ U_{ij}Ū_{kl} = ½ δ_{ik}δ_{jl}`. -/
theorem haar_su2_diag_sq_half :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∂(probHaar (SU 2)) = 1 / 2 := by
  have ha10 : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)))
      = ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∂(probHaar (SU 2)) :=
    sq_eq_left 0 0 1 0 (fun g => by
      have h : ((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
        rw [Submonoid.coe_mul]; show (wmat * (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
      rw [h])
  have ha11 : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ∂(probHaar (SU 2)))
      = ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∂(probHaar (SU 2)) :=
    sq_eq_left 0 1 1 1 (fun g => by
      have h : ((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
        rw [Submonoid.coe_mul]; show (wmat * (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
      rw [h])
  have ha01 : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∂(probHaar (SU 2)))
      = ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∂(probHaar (SU 2)) :=
    sq_eq_right 0 0 0 1 (fun g => by
      have h : ((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
        rw [Submonoid.coe_mul]; show ((g : Matrix (Fin 2) (Fin 2) ℂ) * wmat) 0 0 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
      rw [h, map_neg]; ring)
  have hsum : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ∂(probHaar (SU 2)))
      + (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∂(probHaar (SU 2)))
      + (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)))
      + (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ∂(probHaar (SU 2))) = 2 := by
    have h := haar_su2_frobenius_sum
    rw [integral_finset_sum _
      (fun i _ => integrable_finset_sum _ (fun j _ => entry_sq_integrable i j))] at h
    simp_rw [integral_finset_sum _ (fun j _ => entry_sq_integrable _ j)] at h
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
    linear_combination h
  linear_combination (1/4 : ℂ) * hsum - (1/2 : ℂ) * ha01 - (1/4 : ℂ) * ha10 - (1/4 : ℂ) * ha11

/-- `U_{ij}·conj(U_{kl})` is integrable (continuous, bounded by `1`). -/
theorem entry_prod_integrable (i j k l : Fin 2) :
    Integrable (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) (probHaar (SU 2)) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  have h1 : Continuous (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have h2 : Continuous (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) k l) :=
    (continuous_apply l).comp ((continuous_apply k).comp continuous_subtype_val)
  refine (integrable_const (1 : ℝ)).mono'
    (h1.mul (Complex.continuous_conj.comp h2)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [norm_mul, Complex.norm_conj]
  have b1 := unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 i j
  have b2 := unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 k l
  nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) i j),
    norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) k l), b1, b2]

/-- **Off-diagonal second moment vanishes:** if the `h0`-phase `(h0)_{ii}·conj((h0)_{kk}) ≠ 1` then
`∫ U_{ij} conj(U_{kl}) dHaar = 0` (the `h0` substitution multiplies the integrand by that phase, so
`c = φc ⇒ c = 0`). For `i ≠ k` the phase is `-1`. -/
theorem offdiag_h0 (i j k l : Fin 2)
    (hφ : h0mat i i * (starRingEnd ℂ) (h0mat k k) ≠ 1) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)) = 0 := by
  haveI := isMulLeftInvariant_probHaar (SU 2)
  have hrow : ∀ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l)
      = (h0mat i i * (starRingEnd ℂ) (h0mat k k))
        * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) := by
    intro g
    have hij : ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        = h0mat i i * (g : Matrix (Fin 2) (Fin 2) ℂ) i j := by
      rw [Submonoid.coe_mul]; show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases i <;> simp [h0mat]
    have hkl : ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l
        = h0mat k k * (g : Matrix (Fin 2) (Fin 2) ℂ) k l := by
      rw [Submonoid.coe_mul]; show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) k l = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases k <;> simp [h0mat]
    rw [hij, hkl, map_mul]; ring
  have step : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)))
      = (h0mat i i * (starRingEnd ℂ) (h0mat k k))
        * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)) := by
    calc (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)))
        = ∫ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
            * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l)
            ∂(probHaar (SU 2)) :=
          (integral_mul_left_eq_self (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) h0).symm
      _ = ∫ g : SU 2, (h0mat i i * (starRingEnd ℂ) (h0mat k k))
            * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hrow)
      _ = (h0mat i i * (starRingEnd ℂ) (h0mat k k))
            * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)) :=
          integral_const_mul _ _
  have hz : (1 - h0mat i i * (starRingEnd ℂ) (h0mat k k))
      * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hφ))

/-- The other diagonal second moment: `∫ |U_{11}|² dHaar = ½` (the swap `w` relates it to `∫|U_{00}|²`). -/
theorem haar_su2_diag_sq_half_11 :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ∂(probHaar (SU 2)) = 1 / 2 := by
  rw [sq_eq_left 0 1 1 1 (fun g => by
        have h : ((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 1
            = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
          rw [Submonoid.coe_mul]; show (wmat * (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = _
          rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
        rw [h])]
  rw [sq_eq_right 0 0 0 1 (fun g => by
        have h : ((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            = -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
          rw [Submonoid.coe_mul]; show ((g : Matrix (Fin 2) (Fin 2) ℂ) * wmat) 0 0 = _
          rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
        rw [h, map_neg]; ring)]
  exact haar_su2_diag_sq_half

/-- **The character norm: `∫ |tr U|² dHaar = 1`** — the fundamental representation of `SU(2)` is
irreducible (`⟨χ, χ⟩ = 1`). Expand `tr U = U₀₀ + U₁₁`: the diagonal terms give `½ + ½`, and the cross
terms `∫ U₀₀ conj(U₁₁)`, `∫ U₁₁ conj(U₀₀)` vanish (`offdiag_h0`, phase `-1`). **The first machine-checked
Schur orthogonality relation for `SU(2)`** — obtained by explicit-element invariance, with no Peter–Weyl;
the seed of the first nontrivial correlation (the shared-link two-point contracts through the second
moment `∫ U_{ij}Ū_{kl} = ½ δ_{ik}δ_{jl}` this assembles). -/
theorem haar_su2_char_norm :
    ∫ g : SU 2, Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
      * (starRingEnd ℂ) (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)) ∂(probHaar (SU 2)) = 1 := by
  have hexp : ∀ g : SU 2, Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)
        * (starRingEnd ℂ) (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = ∑ i : Fin 2, ∑ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i i
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) j j) := by
    intro g
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Matrix.trace_fin_two, map_add]
    ring
  simp_rw [hexp]
  rw [integral_finset_sum _
    (fun i _ => integrable_finset_sum _ (fun j _ => entry_prod_integrable i i j j))]
  simp_rw [integral_finset_sum _ (fun j _ => entry_prod_integrable _ _ j j)]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [haar_su2_diag_sq_half, haar_su2_diag_sq_half_11,
      offdiag_h0 0 0 1 1 (by
        have : h0mat 0 0 * (starRingEnd ℂ) (h0mat 1 1) = -1 := by
          simp [h0mat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Complex.conj_I, Complex.I_mul_I]
        rw [this]; norm_num),
      offdiag_h0 1 1 0 0 (by
        have : h0mat 1 1 * (starRingEnd ℂ) (h0mat 0 0) = -1 := by
          simp [h0mat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Complex.conj_I, Complex.I_mul_I]
        rw [this]; norm_num)]
  norm_num

/-- Right-`h0` off-diagonal killer: if `(h0)_{jj}·conj((h0)_{ll}) ≠ 1` then `∫ U_{ij} conj(U_{kl}) = 0`
(right multiplication `U ↦ U·h0` multiplies the integrand by that phase). For `j ≠ l` the phase is `-1`. -/
theorem offdiag_h0_right (i j k l : Fin 2)
    (hφ : h0mat j j * (starRingEnd ℂ) (h0mat l l) ≠ 1) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)) = 0 := by
  haveI := isMulRightInvariant_probHaar (SU 2)
  have hrow : ∀ g : SU 2, ((g * h0 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) (((g * h0 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l)
      = (h0mat j j * (starRingEnd ℂ) (h0mat l l))
        * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) := by
    intro g
    have hij : ((g * h0 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        = (g : Matrix (Fin 2) (Fin 2) ℂ) i j * h0mat j j := by
      rw [Submonoid.coe_mul]; show ((g : Matrix (Fin 2) (Fin 2) ℂ) * h0mat) i j = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases j <;> simp [h0mat]
    have hkl : ((g * h0 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l
        = (g : Matrix (Fin 2) (Fin 2) ℂ) k l * h0mat l l := by
      rw [Submonoid.coe_mul]; show ((g : Matrix (Fin 2) (Fin 2) ℂ) * h0mat) k l = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases l <;> simp [h0mat]
    rw [hij, hkl, map_mul]; ring
  have step : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)))
      = (h0mat j j * (starRingEnd ℂ) (h0mat l l))
        * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)) := by
    calc (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)))
        = ∫ g : SU 2, ((g * h0 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
            * (starRingEnd ℂ) (((g * h0 : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l)
            ∂(probHaar (SU 2)) :=
          (integral_mul_right_eq_self (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) h0).symm
      _ = ∫ g : SU 2, (h0mat j j * (starRingEnd ℂ) (h0mat l l))
            * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l)) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hrow)
      _ = (h0mat j j * (starRingEnd ℂ) (h0mat l l))
            * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2)) :=
          integral_const_mul _ _
  have hz : (1 - h0mat j j * (starRingEnd ℂ) (h0mat l l))
      * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hφ))

/-- `∫ |U_{01}|² dHaar = ½`. -/
theorem haar_su2_diag_sq_half_01 :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∂(probHaar (SU 2)) = 1 / 2 := by
  rw [sq_eq_right 0 0 0 1 (fun g => by
        have h : ((g * w : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            = -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
          rw [Submonoid.coe_mul]; show ((g : Matrix (Fin 2) (Fin 2) ℂ) * wmat) 0 0 = _
          rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
        rw [h, map_neg]; ring)]
  exact haar_su2_diag_sq_half

/-- `∫ |U_{10}|² dHaar = ½`. -/
theorem haar_su2_diag_sq_half_10 :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2)) = 1 / 2 := by
  rw [sq_eq_left 0 0 1 0 (fun g => by
        have h : ((w * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
          rw [Submonoid.coe_mul]; show (wmat * (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = _
          rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [wmat]
        rw [h])]
  exact haar_su2_diag_sq_half

/-- The `h0`-phase `(h0)_{ii}·conj((h0)_{kk}) = -1 ≠ 1` for `i ≠ k`. -/
theorem h0_phase_ne (i k : Fin 2) (h : i ≠ k) :
    h0mat i i * (starRingEnd ℂ) (h0mat k k) ≠ 1 := by
  have hv : h0mat i i * (starRingEnd ℂ) (h0mat k k) = -1 := by
    fin_cases i <;> fin_cases k <;> simp_all [h0mat, Complex.conj_I, Complex.I_mul_I, map_neg]
  rw [hv]; norm_num

/-- **The full second Haar moment of `SU(2)`: `∫ U_{ij} conj(U_{kl}) dHaar = ½·δ_{ik}δ_{jl}`.** Diagonal
(`(i,j)=(k,l)`): each `∫|U_{ij}|² = ½`. Off-diagonal: `i ≠ k` killed by left-`h0`, `j ≠ l` by right-`h0`
(both phase `-1`). **The complete Schur orthogonality relation for the fundamental of `SU(2)`** — obtained
purely from explicit-element invariance, no Peter–Weyl. Every strong-coupling two-point contracts through
this. -/
theorem haar_su2_second_moment (i j k l : Fin 2) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) k l) ∂(probHaar (SU 2))
      = if i = k ∧ j = l then 1 / 2 else 0 := by
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      rw [if_pos ⟨rfl, rfl⟩]
      fin_cases i <;> fin_cases j
      · exact haar_su2_diag_sq_half
      · exact haar_su2_diag_sq_half_01
      · exact haar_su2_diag_sq_half_10
      · exact haar_su2_diag_sq_half_11
    · rw [if_neg (by simp [hjl])]
      exact offdiag_h0_right i j i l (h0_phase_ne j l hjl)
  · rw [if_neg (by simp [hik])]
    exact offdiag_h0 i j k l (h0_phase_ne i k hik)

#print axioms haar_su2_two_link_trace_zero
#print axioms haar_su2_second_moment_offdiag
#print axioms haar_su2_frobenius_sum
/-- **The two-point contraction: `∫ tr(U·A)·tr(U*·B) dHaar = ½·tr(A·B)`** for any fixed matrices `A, B`.
The reusable engine for strong-coupling two-point functions: expand both traces, and every term contracts
through the second moment `haar_su2_second_moment` (`∫ U_{pq} conj(U_{sr}) = ½δ_{ps}δ_{qr}`), which forces
`s=p, r=q` and collapses the quadruple sum to `½·tr(AB)`. With `A, B` the environments of two plaquettes
sharing a link, this is exactly the leading nontrivial correlation `⟨φ_p φ_q⟩_c` — the first genuinely
non-factorizing two-point, the seed of the mass gap. -/
theorem haar_su2_two_point (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ∫ g : SU 2, Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * A)
        * Matrix.trace (star (g : Matrix (Fin 2) (Fin 2) ℂ) * B) ∂(probHaar (SU 2))
      = (1 / 2 : ℂ) * Matrix.trace (A * B) := by
  have key : ∀ g : SU 2, Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * A)
        * Matrix.trace (star (g : Matrix (Fin 2) (Fin 2) ℂ) * B)
      = ∑ x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
          (g : Matrix (Fin 2) (Fin 2) ℂ) x.1.1 x.1.2
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) x.2.1 x.2.2)
            * (A x.1.2 x.1.1 * B x.2.1 x.2.2) := by
    intro g
    simp only [Fintype.sum_prod_type, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, starRingEnd_apply]
    ring
  simp_rw [key]
  rw [integral_finset_sum _
    (fun x _ => (entry_prod_integrable x.1.1 x.1.2 x.2.1 x.2.2).mul_const _)]
  simp_rw [integral_mul_const, haar_su2_second_moment]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, and_self, ite_mul, zero_mul, one_div]
  rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num
  ring

#print axioms haar_su2_diag_sq_half
#print axioms haar_su2_char_norm
/-- **The shared-link coupling: `∫ tr(C₀·g*)·tr(g·C₁) dHaar = ½ tr(C₀·C₁)`.** When two Wilson loops share
one link `g` (as `g` in one and `g⁻¹ = g*` in the other), integrating that link out couples the two loops'
remaining environments `C₀, C₁`: the result is `½ tr(C₀C₁)`, generically nonzero. **This is the first
genuinely non-factorizing correlation** — the product of the two marginals is `0` (each
`∫ tr(g·C) = tr((∫g)C) = 0`, since `∫ g dHaar = 0`), yet the joint is `½ tr(C₀C₁) ≠ 0` precisely because the
two loops share `g`. On an interacting lattice (plaquettes sharing a link, e.g. `WilsonReal.sysInt`) this is
the mechanism of the connected two-point `⟨φ_p φ_q⟩_c ≠ 0` — the seed of the mass gap, here reduced to the
machine-checked SU(2) two-point engine with no Peter–Weyl. -/
theorem haar_su2_shared_link (C0 C1 : Matrix (Fin 2) (Fin 2) ℂ) :
    ∫ g : SU 2, Matrix.trace (C0 * star (g : Matrix (Fin 2) (Fin 2) ℂ))
        * Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * C1) ∂(probHaar (SU 2))
      = (1 / 2 : ℂ) * Matrix.trace (C0 * C1) := by
  have hcomm : ∀ g : SU 2, Matrix.trace (C0 * star (g : Matrix (Fin 2) (Fin 2) ℂ))
        * Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * C1)
      = Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * C1)
        * Matrix.trace (star (g : Matrix (Fin 2) (Fin 2) ℂ) * C0) := by
    intro g; rw [Matrix.trace_mul_comm C0 (star (g : Matrix (Fin 2) (Fin 2) ℂ))]; ring
  simp_rw [hcomm]
  rw [haar_su2_two_point C1 C0, Matrix.trace_mul_comm C1 C0]

/-- **The single-link transfer operator projects onto the vacuum: `(∫ g* X g dHaar)_{ij} = ½ tr(X) δ_{ij}`,**
i.e. `∫ g* X g dHaar = ½ tr(X)·I`. So the strong-coupling (pure-Haar) transfer operator `T(X) = ∫ g* X g`
on the fundamental has `T(I) = I` (the vacuum, eigenvalue `1`) and `T(X) = 0` for every traceless `X`
(`haar_su2_transfer_annihilates`): it **annihilates the entire connected sector** in one step. This is the
mass-gap mechanism — in the strong-coupling limit the connected correlation between separated regions has
finite range — reduced to the second Haar moment, with no Peter–Weyl. -/
theorem haar_su2_transfer (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ∫ g : SU 2, (star (g : Matrix (Fin 2) (Fin 2) ℂ) * X * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
        ∂(probHaar (SU 2))
      = (1 / 2 : ℂ) * Matrix.trace X * (if i = j then 1 else 0) := by
  have hexp : ∀ g : SU 2,
      (star (g : Matrix (Fin 2) (Fin 2) ℂ) * X * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
      = ∑ ab : Fin 2 × Fin 2, X ab.1 ab.2
          * ((g : Matrix (Fin 2) (Fin 2) ℂ) ab.2 j
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) ab.1 i)) := by
    intro g
    simp only [Fintype.sum_prod_type, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, starRingEnd_apply]
    ring
  simp_rw [hexp]
  rw [integral_finset_sum _
    (fun ab _ => (entry_prod_integrable ab.2 j ab.1 i).const_mul (X ab.1 ab.2))]
  simp_rw [integral_const_mul, haar_su2_second_moment]
  clear hexp
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.trace_fin_two]
  by_cases h : i = j <;> simp_all [eq_comm] <;> ring

/-- **The transfer operator annihilates the connected (traceless) sector: `tr X = 0 ⇒ ∫ g* X g dHaar = 0`.**
The spectral gap of the strong-coupling transfer operator, in its sharpest form: everything orthogonal to
the vacuum decays completely in one link. -/
theorem haar_su2_transfer_annihilates (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : Matrix.trace X = 0) (i j : Fin 2) :
    ∫ g : SU 2, (star (g : Matrix (Fin 2) (Fin 2) ℂ) * X * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
        ∂(probHaar (SU 2)) = 0 := by
  rw [haar_su2_transfer, hX]; ring

/-- `((h₀·g))_{pq} = (h₀)_{pp}·g_{pq}` — the diagonal element `h₀` scales row `p` by `(h₀)_{pp}`. -/
theorem h0_mul_entry (g : SU 2) (p q : Fin 2) :
    ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) p q
      = h0mat p p * (g : Matrix (Fin 2) (Fin 2) ℂ) p q := by
  rw [Submonoid.coe_mul]; show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) p q = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases p <;> simp [h0mat]

/-- **The third Haar moment vanishes: `∫ U_{ij} U_{kl} conj(U_{mn}) dHaar = 0`** for all indices. Under
`U ↦ h₀U` the integrand picks up the phase `(h₀)_{ii}(h₀)_{kk}·conj((h₀)_{mm}) = i^{ε_i+ε_k-ε_m}`, whose
exponent is always **odd**, so the phase is `±i ≠ 1` and the integral is `0` (two fundamentals + one
conjugate = an odd tensor power, no `SU(2)` invariant). Consequence: the `O(β)` correction to the transfer
operator vanishes — the strong-coupling gap has **no linear-in-`β` term**; the leading nonzero-rate
correction is `O(β²)` (fourth moments). -/
theorem haar_su2_third_moment (i j k l m n : Fin 2) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2)) = 0 := by
  haveI := isMulLeftInvariant_probHaar (SU 2)
  have hrow : ∀ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) m n)
      = (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m))
        * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)) := by
    intro g
    rw [h0_mul_entry, h0_mul_entry, h0_mul_entry, map_mul]; ring
  have step : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2)))
      = (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m))
        * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2)) := by
    calc (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2)))
        = ∫ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
            * ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l
            * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2)) :=
          (integral_mul_left_eq_self (fun g : SU 2 =>
            (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)) h0).symm
      _ = ∫ g : SU 2, (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m))
            * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hrow)
      _ = (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m))
            * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2)) :=
          integral_const_mul _ _
  have hφ : h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m) ≠ 1 := by
    fin_cases i <;> fin_cases k <;> fin_cases m <;>
      simp only [h0mat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Complex.conj_I, map_neg, Complex.I_mul_I] <;> norm_num [Complex.ext_iff]
  have hz : (1 - h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m))
      * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hφ))

#print axioms haar_su2_second_moment
#print axioms haar_su2_two_point
/-- **Support of the fourth Haar moment: the unbalanced components vanish.** If the `h₀` row-phase
`(h₀)_{ii}(h₀)_{kk}·conj((h₀)_{mm})·conj((h₀)_{pp}) ≠ 1` then `∫ U_{ij}U_{kl}conj(U_{mn})conj(U_{pq}) = 0`.
The phase is `i^{ε_i+ε_k-ε_m-ε_p}`, which equals `1` only for the *balanced* row indices `ε_i+ε_k=ε_m+ε_p`;
so the fourth moment is supported on the balanced components (analogously with the columns via right-`h₀`).
Their quantitative value there — the Weingarten `δδ`(+`ε`) combination giving the `O(β²)` gap — is the
remaining deep piece (the point at which the Entroptics measured single-plaquette gap takes over). -/
theorem haar_su2_fourth_moment_unbalanced (i j k l m n p q : Fin 2)
    (hφ : h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m) * (starRingEnd ℂ) (h0mat p p) ≠ 1) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2)) = 0 := by
  haveI := isMulLeftInvariant_probHaar (SU 2)
  have hrow : ∀ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
        * ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) m n)
        * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) p q)
      = (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m) * (starRingEnd ℂ) (h0mat p p))
        * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q)) := by
    intro g
    rw [h0_mul_entry, h0_mul_entry, h0_mul_entry, h0_mul_entry, map_mul, map_mul]; ring
  have step : (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2)))
      = (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m) * (starRingEnd ℂ) (h0mat p p))
        * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2)) := by
    calc (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
          * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2)))
        = ∫ g : SU 2, ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) i j
            * ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) k l
            * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) m n)
            * (starRingEnd ℂ) (((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2)) :=
          (integral_mul_left_eq_self (fun g : SU 2 =>
            (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q)) h0).symm
      _ = ∫ g : SU 2, (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m)
              * (starRingEnd ℂ) (h0mat p p))
            * ((g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q)) ∂(probHaar (SU 2)) :=
          integral_congr_ae (Filter.Eventually.of_forall hrow)
      _ = (h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m) * (starRingEnd ℂ) (h0mat p p))
            * ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
              * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2)) :=
          integral_const_mul _ _
  have hz : (1 - h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m) * (starRingEnd ℂ) (h0mat p p))
      * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n)
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) p q) ∂(probHaar (SU 2))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hφ))

/-! ### SU(2) pseudoreality (toward the fourth-moment Weingarten value / the `O(β²)` gap)

For `g ∈ SU(2)` the conjugate representation is equivalent to the fundamental via the `ε`-tensor: `conj(g_{ij})`
is `±g_{i'j'}`. This is the structural keystone of the fourth Haar moment (it converts every conjugate to a
fundamental entry, so `∫ U U Ū Ū` becomes an `∫` of four fundamentals = the `εε`-Weingarten invariant), which
gives the `O(β²)` term of the transfer-operator gap — the from-scratch (unconditional) route to the
strong-coupling gap value. -/

/-- **SU(2) pseudoreality (matrix form): `star g = adjugate g`.** Since `star g = g⁻¹` (unitarity) and
`g⁻¹ = adjugate g` (as `det g = 1`), the conjugate transpose equals the explicit adjugate `[[g₁₁,-g₀₁],[-g₁₀,g₀₀]]`. -/
theorem su2_star_eq (g : SU 2) :
    star (g : Matrix (Fin 2) (Fin 2) ℂ)
      = !![(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1, -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1;
          -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0] := by
  have hu : star (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  rw [← Matrix.inv_eq_left_inv hu, Matrix.inv_def, hdet, Ring.inverse_one, one_smul,
    Matrix.adjugate_fin_two]

/-- Pseudoreality: `conj(g₀₀) = g₁₁`. -/
theorem su2_conj_00 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  have h := congrFun (congrFun (su2_star_eq g) 0) 0
  simpa [Matrix.star_apply, Complex.star_def] using h

/-- Pseudoreality: `conj(g₁₁) = g₀₀`. -/
theorem su2_conj_11 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
  have h := congrFun (congrFun (su2_star_eq g) 1) 1
  simpa [Matrix.star_apply, Complex.star_def] using h

/-- Pseudoreality: `conj(g₀₁) = -g₁₀`. -/
theorem su2_conj_01 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
  have h := congrFun (congrFun (su2_star_eq g) 1) 0
  simpa [Matrix.star_apply, Complex.star_def] using h

/-- Pseudoreality: `conj(g₁₀) = -g₀₁`. -/
theorem su2_conj_10 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
  have h := congrFun (congrFun (su2_star_eq g) 0) 1
  simpa [Matrix.star_apply, Complex.star_def] using h

#print axioms haar_su2_shared_link
#print axioms haar_su2_third_moment
#print axioms haar_su2_fourth_moment_unbalanced
/-- The `SU(2)` Levi-Civita tensor `ε = [[0,1],[-1,0]]`. -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- **Two-fundamental Haar moment: `∫ U_{ab} U_{cd} dHaar = ½ ε_{ac} ε_{bd}`.** Via pseudoreality
(`U_{cd} = ± conj(U_{c'd'})`, `su2_conj_*`) this reduces to `± ½ δ` (the second moment
`haar_su2_second_moment`), which equals `½ ε_{ac} ε_{bd}` (nonzero only for antisymmetric index pairs). The
`εε` invariant of `∫ U⊗U` — the building block of the fourth-moment Weingarten value that gives the `O(β²)`
gap; the from-scratch (unconditional) route, no measurement. -/
theorem haar_su2_two_fund (a b c d : Fin 2) :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) c d
        ∂(probHaar (SU 2))
      = (1 / 2 : ℂ) * (eps a c * eps b d) := by
  fin_cases c <;> fin_cases d
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 0 * eps b 0)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
          = (g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) by rw [su2_conj_11])),
      haar_su2_second_moment a b 1 1]
    fin_cases a <;> fin_cases b <;> simp [eps] <;> norm_num
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 0 * eps b 1)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
          = -((g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) by
          rw [show (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
            = -(starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) by rw [su2_conj_10]; ring]; ring)),
      integral_neg, haar_su2_second_moment a b 1 0]
    fin_cases a <;> fin_cases b <;> simp [eps] <;> norm_num
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 1 * eps b 0)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
          = -((g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1)) by
          rw [show (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
            = -(starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) by rw [su2_conj_01]; ring]; ring)),
      integral_neg, haar_su2_second_moment a b 0 1]
    fin_cases a <;> fin_cases b <;> simp [eps] <;> norm_num
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 1 * eps b 1)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
          = (g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) by rw [su2_conj_00])),
      haar_su2_second_moment a b 0 0]
    fin_cases a <;> fin_cases b <;> simp [eps] <;> norm_num

/-- **For SU(2), `tr g` is real: `conj(tr g) = tr g`.** From pseudoreality `conj(g₀₀)=g₁₁`, `conj(g₁₁)=g₀₀`.
So `Re tr g = tr g`, and the Wilson density is `φ_W(g) = 1 - ½ tr g` — the `O(β²)` transfer term collapses to
`(β²/8) ∫ (tr g)² (star g · X · g)`, a pure four-fundamental contraction. -/
theorem su2_trace_real (g : SU 2) :
    (starRingEnd ℂ) (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.trace_fin_two, map_add, su2_conj_00, su2_conj_11]; ring

/-- `f₀₀ g = |U₀₀|²` (real). By pseudoreality `= U₀₀·conj U₀₀ = U₀₀U₁₁`. -/
noncomputable def f00 (g : SU 2) : ℝ := Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)

lemma f00_nonneg (g : SU 2) : 0 ≤ f00 g := Complex.normSq_nonneg _

lemma f00_le_one (g : SU 2) : f00 g ≤ 1 := by
  have h := unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 0 0
  have hn : f00 g = ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2 := by
    rw [f00, Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0), h]

lemma f00_continuous : Continuous f00 :=
  Complex.continuous_normSq.comp
    ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val))

lemma f00_integrable : Integrable f00 (probHaar (SU 2)) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  refine (integrable_const (1 : ℝ)).mono' f00_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (f00_nonneg g)]; exact f00_le_one g

lemma f00_sq_integrable : Integrable (fun g => f00 g ^ 2) (probHaar (SU 2)) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  refine (integrable_const (1 : ℝ)).mono' (f00_continuous.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [f00_nonneg g, f00_le_one g]

/-- `∫ |U₀₀|² dHaar = 1/2` (the diagonal second moment, real form of `haar_su2_second_moment`). -/
lemma f00_mean : ∫ g : SU 2, f00 g ∂(probHaar (SU 2)) = 1 / 2 := by
  have h2 := haar_su2_second_moment 0 0 0 0
  rw [if_pos ⟨rfl, rfl⟩] at h2
  have hpt : ∀ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = ((f00 g : ℝ) : ℂ) := by
    intro g; rw [f00, Complex.mul_conj]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at h2
  have h3 : ((∫ g : SU 2, f00 g ∂(probHaar (SU 2)) : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]; exact integral_ofReal.symm.trans h2
  exact Complex.ofReal_inj.mp h3

/-- **Fourth-moment diagonal bounds: `1/4 ≤ ∫|U₀₀|⁴ ≤ 1/2`.** `A = ∫U₀₀²U₁₁² = ∫|U₀₀|⁴` (`|U₀₀|²=U₀₀U₁₁`
by pseudoreality, real ≥0). LOWER: Cauchy–Schwarz `∫f² ≥ (∫f)² = 1/4` (`∫(f-½)² ≥ 0`, `∫f=½`). UPPER:
`f²≤f` since `0≤f≤1`, so `∫f² ≤ ∫f = ½`. Bounds the `O(β²)` connected-eigenvalue coefficient
`A+B = 2A-½ ∈ [0,½]` non-negative BY PROOF. The **exact** `A = 1/3` is NOT reachable by this method (all
4th-order relations from unitarity/`det` are identically satisfied); it needs SU(2) Weyl integration / spin-1
Schur orthogonality (Peter–Weyl, not in Mathlib). This is the honest maximum invariant-projection yields on
the 4th moment. -/
theorem haar_su2_fourth_moment_diag_bounds :
    1 / 4 ≤ ∫ g : SU 2, f00 g ^ 2 ∂(probHaar (SU 2))
      ∧ ∫ g : SU 2, f00 g ^ 2 ∂(probHaar (SU 2)) ≤ 1 / 2 := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  constructor
  · have hnn : 0 ≤ ∫ g : SU 2, (f00 g - 1 / 2) ^ 2 ∂(probHaar (SU 2)) :=
      integral_nonneg (fun g => sq_nonneg _)
    have e1 : ∫ g : SU 2, (f00 g - 1 / 2) ^ 2 ∂(probHaar (SU 2))
        = ∫ g : SU 2, (f00 g ^ 2 - f00 g + 1 / 4) ∂(probHaar (SU 2)) := by
      apply integral_congr_ae; filter_upwards with g; ring
    rw [e1, integral_add (show Integrable (fun a : SU 2 => f00 a ^ 2 - f00 a) (probHaar (SU 2))
        from f00_sq_integrable.sub f00_integrable) (integrable_const _),
      integral_sub f00_sq_integrable f00_integrable, integral_const,
      MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, f00_mean] at hnn
    linarith
  · calc ∫ g : SU 2, f00 g ^ 2 ∂(probHaar (SU 2))
        ≤ ∫ g : SU 2, f00 g ∂(probHaar (SU 2)) :=
          integral_mono f00_sq_integrable f00_integrable
            (fun g => by nlinarith [f00_nonneg g, f00_le_one g])
      _ = 1 / 2 := f00_mean

/-- **Companion balanced four-fundamental: `∫ U₀₀U₁₁·U₀₁U₁₀ dHaar = A − ½`** where `A = ∫|U₀₀|⁴`. Via
`det g = 1` (`U₀₀U₁₁ − U₀₁U₁₀ = 1`) the integrand is real: `U₀₀U₁₁ = |U₀₀|² = f₀₀` (pseudoreality) and
`U₀₁U₁₀ = f₀₀ − 1`, so it equals `f₀₀² − f₀₀`, integrating to `A − ½` (`∫f₀₀ = ½`). Completes the balanced
four-fundamental structure: both `A` and `B` are pinned to the single undetermined constant `A ∈ [1/4,1/2]`
(`haar_su2_fourth_moment_diag_bounds`); only `A`'s exact value `1/3` needs Weyl integration. -/
theorem haar_su2_balanced_four :
    ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∂(probHaar (SU 2))
      = ((∫ g : SU 2, f00 g ^ 2 ∂(probHaar (SU 2)) : ℝ) : ℂ) - 1 / 2 := by
  have hpt : ∀ g : SU 2,
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
          * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
        = ((f00 g ^ 2 - f00 g : ℝ) : ℂ) := by
    intro g
    have hf : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        = ((f00 g : ℝ) : ℂ) := by
      rw [f00, show (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        = (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) from (su2_conj_00 g).symm]
      exact Complex.mul_conj _
    have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        - (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
      rw [Matrix.det_fin_two] at h; linear_combination h
    have h2 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        = ((f00 g : ℝ) : ℂ) - 1 := by linear_combination hf - hdet
    rw [hf, h2]; push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hi : (∫ g : SU 2, ((f00 g ^ 2 - f00 g : ℝ) : ℂ) ∂(probHaar (SU 2)))
      = ((∫ g : SU 2, (f00 g ^ 2 - f00 g) ∂(probHaar (SU 2)) : ℝ) : ℂ) := integral_ofReal
  rw [hi, integral_sub (show Integrable (fun g : SU 2 => f00 g ^ 2) (probHaar (SU 2))
      from f00_sq_integrable) f00_integrable, Complex.ofReal_sub, f00_mean]
  norm_num

#print axioms su2_star_eq
#print axioms su2_conj_01
#print axioms haar_su2_two_fund
#print axioms su2_trace_real
#print axioms haar_su2_fourth_moment_diag_bounds
#print axioms haar_su2_balanced_four
/-- The strong-coupling transfer operator on the fundamental, as a **linear map** `M₂ →ₗ M₂`, in closed
form `T(X) = ½ tr(X)·I` (equal to the Haar integral `∫ g* X g`, `transferOp_eq_integral`). -/
noncomputable def transferOp : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := ((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_add' X Y := by rw [Matrix.trace_add, mul_add, add_smul]
  map_smul' c X := by
    show ((1 / 2 : ℂ) * Matrix.trace (c • X)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = c • (((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [Matrix.trace_smul, smul_eq_mul, smul_smul]; congr 1; ring

theorem transferOp_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferOp X = ((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- **`transferOp` IS the Haar integral `∫ g* X g`** (entrywise), by `haar_su2_transfer`. -/
theorem transferOp_eq_integral (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    transferOp X i j
      = ∫ g : SU 2, (star (g : Matrix (Fin 2) (Fin 2) ℂ) * X * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
        ∂(probHaar (SU 2)) := by
  rw [haar_su2_transfer, transferOp_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- **Vacuum eigenvalue 1:** `T(I) = I`. -/
theorem transferOp_vacuum : transferOp (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [transferOp_apply, Matrix.trace_one, Fintype.card_fin]; norm_num

/-- **The connected (traceless) sector is annihilated:** `tr X = 0 ⇒ T(X) = 0` (eigenvalue 0). -/
theorem transferOp_annihilates (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Matrix.trace X = 0) :
    transferOp X = 0 := by
  rw [transferOp_apply, hX]; simp

/-- **`T` is idempotent: `T² = T`.** So `Tⁿ = T` for all `n ≥ 1` (`transferOp_pow`): the spectral gap
persists at every chain length — the connected sector, once annihilated by one link, stays annihilated.
The strong-coupling mass gap (finite-range connected correlations) as an operator identity. -/
theorem transferOp_idem (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferOp (transferOp X) = transferOp X := by
  rw [transferOp_apply, transferOp_apply, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  congr 1
  push_cast
  ring

/-- **The transfer operator to any power `≥ 1` equals itself: `Tⁿ⁺¹ = T`.** The connected sector is
annihilated at every separation — finite-range correlations, the strong-coupling gap in operator form. -/
theorem transferOp_pow (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ n, (transferOp^[n + 1]) X = transferOp X
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', transferOp_pow X n, transferOp_idem]

/-- **Connected correlations vanish at every separation `n ≥ 1`: `tr X = 0 ⇒ Tⁿ⁺¹(X) = 0`.** Feeding a
connected (vacuum-subtracted, traceless) source through any number of links annihilates it — the strong-
coupling mass gap as a *finite-range* statement uniform in the separation, not just nearest-neighbour. -/
theorem transferOp_pow_annihilates (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Matrix.trace X = 0) (n : ℕ) :
    (transferOp^[n + 1]) X = 0 := by
  rw [transferOp_pow X n, transferOp_annihilates X hX]

/-- **The transfer operator's range is the one-dimensional vacuum line `ℂ·I`:** `T(X) = (½ tr X)·I`. With
`transferOp_annihilates` (kernel ⊇ traceless) this is the full spectral picture: eigenvalue `1` on the
1-dim vacuum `ℂ·I`, eigenvalue `0` on the 3-dim traceless (connected) sector — a spectral gap of `1`. -/
theorem transferOp_range (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferOp X = ((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

#print axioms haar_su2_transfer
#print axioms haar_su2_transfer_annihilates
#print axioms transferOp_idem
#print axioms transferOp_pow
#print axioms transferOp_pow_annihilates

end MassGap.SUN
