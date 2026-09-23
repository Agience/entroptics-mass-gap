import MassGap.SUN

/-!
# MassGap.HaarMoments — Haar moments of `SU(2)`, and the map `X ↦ ½ tr(X)·I`

Mathlib has no Peter–Weyl theorem and no Schur orthogonality for compact groups. This module derives the
low moments of the Haar probability measure on `SU 2` from scratch by one method: substituting a single
explicit group element into the integral. The two elements are the diagonal `h0 = diag(i,-i)` and the swap
`w = [[0,1],[-1,0]]`. Substituting `U ↦ h0·U`, or `U ↦ U·h0`, multiplies the integrand by a fixed phase;
when that phase is not `1`, invariance gives `c = φ·c` and hence `c = 0`. The swap `w` and the
normalization `∫ ∑_{ij} |U_{ij}|² = 2` fix the components that survive.

Contents (every result carries `[propext, Classical.choice, Quot.sound]` only):
* First moment — `haar_su2_coeff_zero` (`∫ U_{ij} dHaar = 0`), `haar_su2_trace_zero`,
  `haar_su2_re_trace_zero`, `haar_su2_trace_mul_zero` (`∫ tr(U·X) = 0` for fixed `X`), and the
  product-measure form `haar_su2_two_link_trace_zero`.
* Second moment — `haar_su2_second_moment` : `∫ U_{ij} conj(U_{kl}) dHaar = ½ δ_{ik}δ_{jl}`, assembled from
  `haar_su2_diag_sq_half` and the two phase-killing lemmas `offdiag_h0` and `offdiag_h0_right`. Downstream:
  `haar_su2_char_norm` (`∫ |tr U|² = 1`), `haar_su2_two_point` (`∫ tr(UA)·tr(U*B) = ½ tr(AB)`) and
  `haar_su2_shared_link` (`∫ tr(C₀g*)·tr(gC₁) = ½ tr(C₀C₁)`).
* Third moment — `haar_su2_third_moment` : `∫ U U conj(U) dHaar = 0`, for every index choice and with no
  hypothesis; two fundamentals against one conjugate is an odd tensor power.
* Fourth moment — `haar_su2_fourth_moment_unbalanced` vanishes under an explicit phase hypothesis on the
  row indices; `haar_su2_fourth_moment_diag_bounds` brackets `∫ |U₀₀|⁴` in `[1/4, 1/2]`, and
  `haar_su2_balanced_four` expresses the companion balanced moment as that integral minus `½`. The exact
  value of `∫ |U₀₀|⁴` is not determined in this file.
* `transferOp` — the linear map `M₂(ℂ) →ₗ[ℂ] M₂(ℂ)`, `X ↦ (½ tr X)·I`. `transferOp_eq_integral` identifies
  it entrywise with `∫ g* X g`; `transferOp_vacuum` (`T I = I`), `transferOp_annihilates` (`T = 0` on the
  traceless matrices), `transferOp_idem` (`T² = T`), `transferOp_pow` (`Tⁿ⁺¹ = T`) and
  `transferOp_pow_annihilates` describe its iterates.

Every result here is an integral over `SU 2` against `probHaar`, or an algebraic identity about
`transferOp` as a map on `2 × 2` matrices. No lattice, coupling `β`, separation or correlation length
appears anywhere in the file.

Build: `lake build MassGap.HaarMoments`.
-/

namespace MassGap.SUN

open Matrix MeasureTheory MassGap.CompactGauge

/-- The diagonal complex matrix `diag(i, -i)`. `h0_mem` proves it lies in
`Matrix.specialUnitaryGroup (Fin 2) ℂ`: its rows are orthonormal and its determinant is `1`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`; the two `0` entries make it diagonal, and `i`, `-i` are unit-modulus with product `1`, which is what membership requires. -/
noncomputable def h0mat : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem h0_mem : h0mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h0mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [h0mat, Matrix.det_fin_two]

/-- `h0mat` bundled with `h0_mem` as an element of `SU 2`. Left- and right-multiplication by it are the
substitutions that every phase argument in this file uses.
DERIVED: the `2` is the fundamental representation of `SU(2)`. -/
noncomputable def h0 : SU 2 := ⟨h0mat, h0_mem⟩

/-- Every matrix coefficient of the fundamental representation Haar-averages to zero:
`∫_{SU(2)} U_{ij} dHaar = 0`, with both indices universally quantified.

Left-invariance under `h0` gives `c = (h0)_{ii}·c`, and `(h0)_{ii}` is `i` or `-i`, neither of which is
`1`, so `1 - (h0)_{ii}` is invertible in `ℂ` and `c = 0`. The argument uses one explicit group element;
no representation theory enters.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`; the `0` on the right is forced, not a bound. -/
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

/-- Each matrix coefficient of the fundamental is integrable against `probHaar (SU 2)`: it is continuous
in `g`, `unitary_entry_norm_le_one` bounds it by `1` entrywise, and the measure is a probability measure.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
theorem entry_integrable (i j : Fin 2) :
    Integrable (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) (probHaar (SU 2)) := by
  haveI := isProbabilityMeasure_probHaar (SU 2)
  have hcont : Continuous (fun g : SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  refine (integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => ?_))
  exact unitary_entry_norm_le_one 2 (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1 i j

/-- The fundamental character Haar-averages to zero: `∫_{SU(2)} tr(U) dHaar = 0`. The trace is the sum of
the two diagonal coefficients, each of which integrates to zero by `haar_su2_coeff_zero`;
`integral_finsetSum` moves the integral inside, using `entry_integrable`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`; the `0` is the sum of two zeros. -/
theorem haar_su2_trace_zero :
    ∫ g : SU 2, Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) ∂(probHaar (SU 2)) = 0 := by
  have hsum : (fun g : SU 2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = (fun g : SU 2 => ∑ i, (g : Matrix (Fin 2) (Fin 2) ℂ) i i) := by
    funext g; rw [Matrix.trace]; rfl
  rw [hsum, integral_finsetSum _ (fun i _ => entry_integrable i i)]
  simp [haar_su2_coeff_zero]

/-- The fundamental character is integrable against `probHaar (SU 2)`, as a finite sum of the integrable
diagonal coefficients supplied by `entry_integrable`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
theorem trace_integrable :
    Integrable (fun g : SU 2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)) (probHaar (SU 2)) := by
  have hsum : (fun g : SU 2 => Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = (fun g : SU 2 => ∑ i, (g : Matrix (Fin 2) (Fin 2) ℂ) i i) := by
    funext g; rw [Matrix.trace]; rfl
  rw [hsum]; exact integrable_finsetSum _ (fun i _ => entry_integrable i i)

/-- The real part of the fundamental character Haar-averages to zero: `∫_{SU(2)} Re tr(U) dHaar = 0`.
`Complex.reCLM` is continuous linear, so `ContinuousLinearMap.integral_comp_comm` moves it through the
integral and `haar_su2_trace_zero` finishes. The integral here is real-valued, unlike
`haar_su2_trace_zero`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`; the `0` is `Complex.zero_re` applied to the vanishing complex integral. -/
theorem haar_su2_re_trace_zero :
    ∫ g : SU 2, (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)).re ∂(probHaar (SU 2)) = 0 := by
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM trace_integrable
  simp only [Complex.reCLM_apply] at h
  rw [h, haar_su2_trace_zero, Complex.zero_re]

/-- For every fixed matrix `X`, `∫_{SU(2)} tr(U·X) dHaar = 0`. Expanding `tr(UX) = ∑_{ab} U_{ab}·X_{ba}`
leaves a finite sum of integrals `∫ U_{ab}`, each zero by `haar_su2_coeff_zero`.

`X` is an arbitrary `2 × 2` complex matrix: it need not be unitary, and it is held fixed rather than
integrated. `haar_su2_trace_zero` is the case `X = 1`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`; the `0` is the sum of the four vanishing coefficient integrals. -/
theorem haar_su2_trace_mul_zero (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∫ g : SU 2, Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * X) ∂(probHaar (SU 2)) = 0 := by
  have hexp : (fun g : SU 2 => Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * X))
      = (fun g : SU 2 => ∑ a : Fin 2, ∑ b : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * X b a) := by
    funext g
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [hexp, integral_finsetSum _
    (fun a _ => integrable_finsetSum _ (fun b _ => (entry_integrable a b).mul_const _))]
  apply Finset.sum_eq_zero
  intro a _
  rw [integral_finsetSum _ (fun b _ => (entry_integrable a b).mul_const _)]
  apply Finset.sum_eq_zero
  intro b _
  rw [integral_mul_const, haar_su2_coeff_zero, zero_mul]

/-- `(U₁, U₂) ↦ tr(U₁·U₂)` is integrable against the product measure
`(probHaar (SU 2)).prod (probHaar (SU 2))`. The product of two special-unitary matrices is again special
unitary, so each of its two diagonal entries has norm at most `1` and the trace has norm at most `2`,
which dominates the constant function used by `Integrable.mono'`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
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

/-- The integral of `tr(U₁·U₂)` over the product measure
`(probHaar (SU 2)).prod (probHaar (SU 2))` is `0`.
`MeasureTheory.integral_prod` splits it into an iterated integral, trace cyclicity turns the inner one
into `haar_su2_trace_mul_zero` with the outer link as the fixed matrix, and the outer integral is then an
integral of `0`. The product-measure form of the one-variable result, over two independent links.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`; the `0` comes from the inner integral vanishing for every fixed outer link. -/
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

/-! ### Second moments

The moments `∫ U_{ij} Ū_{kl} dHaar` are reached by the same one-element substitution. Under `U ↦ h0·U` the
integrand picks up the phase `(h0)_{ii}·conj((h0)_{kk})`, which is `-1` when `i ≠ k`, so those components
vanish (`offdiag_h0`); the right-hand substitution `U ↦ U·h0` does the same for `j ≠ l`
(`offdiag_h0_right`). The four surviving components `∫ |U_{ij}|²` are carried into one another by the swap
`w` (`sq_eq_left`, `sq_eq_right`), and unitarity fixes their sum at `2` (`haar_su2_frobenius_sum`), so each
is `½`. Together these give `∫ U_{ij} Ū_{kl} = ½ δ_{ik} δ_{jl}`. -/

/-- One off-diagonal second moment vanishes: `∫ U₀₀·conj(U₁₀) dHaar = 0`. Under `U ↦ h0·U` the first factor
picks up `i` and the conjugated second factor picks up `conj(-i) = i`, so the integrand is multiplied by
`-1` and `c = -c` forces `c = 0`. This is the single component `(0,0)` against `(1,0)`; `offdiag_h0` below
generalises it to arbitrary indices with a nontrivial phase.
DERIVED: the `2`s are the size of the fundamental; the indices `0 0` and `1 0` name this component, and their differing rows are what make the phase `-1`; the `0` on the right follows from `2c = 0` in `ℂ`. -/
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
/-- The second-moment normalization: `∫ ∑_{ij} U_{ij}·conj(U_{ij}) dHaar = 2`. The integrand is the same at
every `g`, since `∑_{ij} U_{ij} Ū_{ij} = ∑_i (U·U*)_{ii} = tr(1)` by unitarity, so the integral over a
probability measure is that constant. This fixes the scale of `haar_su2_second_moment`.
DERIVED: the 2s in the types are the size of the fundamental, and the `2` on the right is `tr(1)` for the `2 × 2` identity — the number of diagonal entries, not a fitted constant. -/
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

/-- The swap matrix `!![0, 1; -1, 0]` over `ℂ`. `w_mem` proves it lies in
`Matrix.specialUnitaryGroup (Fin 2) ℂ`. Multiplying by it permutes the four components `∫ |U_{ij}|²` into
one another, which is what `sq_eq_left` and `sq_eq_right` use.
DERIVED: the `2`s are the size of the fundamental; the entries `0, 1, -1, 0` are the antisymmetric unit tensor in two dimensions, whose rows are orthonormal and whose determinant is `1`. -/
noncomputable def wmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem w_mem : wmat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · simp [wmat, Matrix.det_fin_two]

/-- `wmat` bundled with `w_mem` as an element of `SU 2`.
DERIVED: the `2` is the fundamental representation of `SU(2)`. -/
noncomputable def w : SU 2 := ⟨wmat, w_mem⟩

/-- `g ↦ U_{ij}·conj(U_{ij})` is integrable against `probHaar (SU 2)`: it is continuous and its norm is at
most `1`, since each entry of a unitary matrix is.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
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

/-- Transfers one squared-modulus moment to another along left multiplication by `w`. The hypothesis
`hpt` is the pointwise identity `|(w·g)_{ij}|² = |g_{i'j'}|²`, which the caller must supply; the
conclusion is `∫ |U_{i'j'}|² = ∫ |U_{ij}|²`, by `integral_mul_left_eq_self` and
`isMulLeftInvariant_probHaar`. The group element is fixed to `w`, so a different element needs its own
`hpt` and its own lemma.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
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

/-- The right-multiplication counterpart of `sq_eq_left`: given the pointwise identity
`|(g·w)_{ij}|² = |g_{i'j'}|²` as `hpt`, it concludes `∫ |U_{i'j'}|² = ∫ |U_{ij}|²`. It goes through
`isMulRightInvariant_probHaar`, so it rests on `SU(2)` being unimodular rather than on left invariance
alone.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
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

/-- The diagonal second moment at the top-left entry: `∫ |U₀₀|² dHaar = 1/2`. Three applications of
`sq_eq_left` and `sq_eq_right` with the swap `w` make the four components `∫ |U_{ij}|²` equal, and
`haar_su2_frobenius_sum` fixes their sum at `2`; `linear_combination` then solves that linear system.
DERIVED: the `2`s are the size of the fundamental; `0 0` names the component; `1 / 2` is `2 / 4`, the total from `haar_su2_frobenius_sum` divided among four equal components. -/
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
    rw [integral_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => entry_sq_integrable i j))] at h
    simp_rw [integral_finsetSum _ (fun j _ => entry_sq_integrable _ j)] at h
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two] at h
    linear_combination h
  linear_combination (1/4 : ℂ) * hsum - (1/2 : ℂ) * ha01 - (1/4 : ℂ) * ha10 - (1/4 : ℂ) * ha11

/-- `g ↦ U_{ij}·conj(U_{kl})` is integrable against `probHaar (SU 2)`, for any four indices: it is
continuous, and each of the two factors has norm at most `1`.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
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

/-- A second moment vanishes whenever the left `h0`-phase is nontrivial: from
`(h0)_{ii}·conj((h0)_{kk}) ≠ 1` it concludes `∫ U_{ij}·conj(U_{kl}) dHaar = 0`. The substitution
`U ↦ h0·U` multiplies the integrand by that phase, so `c = φ·c` with `φ ≠ 1` gives `c = 0`.

The phase condition is a hypothesis, not a conclusion: `h0_phase_ne` discharges it exactly when `i ≠ k`,
where the phase is `-1`. The column indices `j` and `l` are unconstrained and play no part.
DERIVED: the `2`s are the size of the fundamental; the `1` is the phase value the hypothesis excludes, and the `0` follows from `1 - φ` being invertible in `ℂ`. -/
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

/-- The bottom-right diagonal second moment: `∫ |U₁₁|² dHaar = 1/2`, obtained from
`haar_su2_diag_sq_half` by a `sq_eq_left` transfer followed by a `sq_eq_right` transfer, both with `w`.
DERIVED: the `2`s are the size of the fundamental; `1 1` names the component; `1 / 2` is carried over unchanged from `haar_su2_diag_sq_half`. -/
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

/-- The fundamental character has unit norm: `∫ |tr U|² dHaar = 1`. Expanding `tr U = U₀₀ + U₁₁` gives four
terms: the two diagonal ones contribute `½ + ½` by `haar_su2_diag_sq_half` and `haar_su2_diag_sq_half_11`,
and the two cross terms vanish by `offdiag_h0` with the phase computed to `-1` inline. In
representation-theoretic language this is `⟨χ, χ⟩ = 1` for the fundamental, reached here from
explicit-element invariance rather than from Schur orthogonality.
DERIVED: the `2`s are the size of the fundamental; the `1` on the right is `½ + ½ + 0 + 0`. -/
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
  rw [integral_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => entry_prod_integrable i i j j))]
  simp_rw [integral_finsetSum _ (fun j _ => entry_prod_integrable _ _ j j)]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [haar_su2_diag_sq_half, haar_su2_diag_sq_half_11,
      offdiag_h0 0 0 1 1 (by
        have : h0mat 0 0 * (starRingEnd ℂ) (h0mat 1 1) = -1 := by
          simp [h0mat, Matrix.cons_val_zero, Matrix.cons_val_one, 
            Complex.conj_I, Complex.I_mul_I]
        rw [this]; norm_num),
      offdiag_h0 1 1 0 0 (by
        have : h0mat 1 1 * (starRingEnd ℂ) (h0mat 0 0) = -1 := by
          simp [h0mat, Matrix.cons_val_zero, Matrix.cons_val_one, 
            Complex.conj_I, Complex.I_mul_I]
        rw [this]; norm_num)]
  norm_num

/-- The right-multiplication counterpart of `offdiag_h0`: from the column phase condition
`(h0)_{jj}·conj((h0)_{ll}) ≠ 1` it concludes `∫ U_{ij}·conj(U_{kl}) dHaar = 0`. The substitution is
`U ↦ U·h0` and the lemma goes through `isMulRightInvariant_probHaar`. `h0_phase_ne` discharges the
hypothesis exactly when `j ≠ l`, where the phase is `-1`; the row indices `i` and `k` are unconstrained.
DERIVED: the `2`s are the size of the fundamental; the `1` is the phase value the hypothesis excludes, and the `0` follows from `1 - φ` being invertible in `ℂ`. -/
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

/-- `∫ |U₀₁|² dHaar = 1/2`, transferred from `haar_su2_diag_sq_half` by one right multiplication by the
swap `w`.
DERIVED: the `2`s are the size of the fundamental; `0 1` names the component; `1 / 2` is carried over unchanged from `haar_su2_diag_sq_half`. -/
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

/-- `∫ |U₁₀|² dHaar = 1/2`, transferred from `haar_su2_diag_sq_half` by one left multiplication by the
swap `w`.
DERIVED: the `2`s are the size of the fundamental; `1 0` names the component; `1 / 2` is carried over unchanged from `haar_su2_diag_sq_half`. -/
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

/-- For distinct indices the `h0`-phase is not `1`: given `i ≠ k`, `(h0)_{ii}·conj((h0)_{kk}) ≠ 1`, because
`fin_cases` evaluates it to `-1` in both remaining cases. This is what discharges the hypotheses of
`offdiag_h0` and `offdiag_h0_right`. The hypothesis `i ≠ k` is needed: at `i = k` the phase is `1` and the
conclusion is false.
DERIVED: the `2`s are the size of the fundamental; the `1` is the value excluded, and the intermediate `-1` is `i · conj(-i) = i · i`. -/
theorem h0_phase_ne (i k : Fin 2) (h : i ≠ k) :
    h0mat i i * (starRingEnd ℂ) (h0mat k k) ≠ 1 := by
  have hv : h0mat i i * (starRingEnd ℂ) (h0mat k k) = -1 := by
    fin_cases i <;> fin_cases k <;> simp_all [h0mat, Complex.conj_I, Complex.I_mul_I, map_neg]
  rw [hv]; norm_num

/-- The full second Haar moment of `SU(2)`, for all four indices:
`∫ U_{ij}·conj(U_{kl}) dHaar = if i = k ∧ j = l then 1/2 else 0`, that is `½·δ_{ik}·δ_{jl}`.

The diagonal case splits by `fin_cases` into the four `haar_su2_diag_sq_half*` lemmas. `i ≠ k` goes to
`offdiag_h0` and `j ≠ l` to `offdiag_h0_right`, with `h0_phase_ne` supplying each phase condition. This is
Schur orthogonality for the fundamental, assembled from explicit-element invariance. It is stated for
`SU(2)` alone; nothing here carries it to other `Nc`.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` is the `2` of `haar_su2_frobenius_sum` shared among four equal components; the `0` is what the phase argument gives off the diagonal. -/
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
/-- The two-point contraction: `∫ tr(U·A)·tr(U*·B) dHaar = ½·tr(A·B)`, for arbitrary fixed `2 × 2` complex
`A` and `B`. Both traces expand into a quadruple sum, every term of which contracts through
`haar_su2_second_moment`; that forces the two index pairs to agree and collapses the sum to `½·tr(AB)`.

`A` and `B` are unconstrained matrices, held fixed. The conclusion is an identity, not a non-vanishing
claim: `tr(AB)` is `0` for many choices.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` is the second moment's own `1 / 2`, carried through the contraction unchanged. -/
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
  rw [integral_finsetSum _
    (fun x _ => (entry_prod_integrable x.1.1 x.1.2 x.2.1 x.2.2).mul_const _)]
  simp_rw [integral_mul_const, haar_su2_second_moment]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, and_self, ite_mul, zero_mul, one_div]
  rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num
  ring

#print axioms haar_su2_diag_sq_half
#print axioms haar_su2_char_norm
/-- Averaging over a group element that appears in one factor as `g*` and in the other as `g`:
`∫ tr(C₀·g*)·tr(g·C₁) dHaar = ½·tr(C₀·C₁)`, for arbitrary fixed `2 × 2` complex `C₀` and `C₁`. It follows
from `haar_su2_two_point` after one trace commutation, with the two matrices in the other order.

The conclusion is an identity. Each separate average `∫ tr(g·C) dHaar` is `0` by
`haar_su2_trace_mul_zero`, so the right-hand side differs from the product of the two separate averages
whenever `tr(C₀C₁) ≠ 0` — but the statement does not assert that it ever does, and it vanishes whenever
`tr(C₀C₁) = 0`.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` comes from `haar_su2_two_point`. -/
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

/-- The entrywise single-element average: `∫ (g*·X·g)_{ij} dHaar = ½·tr(X)·δ_{ij}`, for arbitrary fixed
`2 × 2` complex `X` and both indices free. Expanding the triple product turns each term into a second
moment, replaced by `haar_su2_second_moment`.

Read as a map on matrices, `X ↦ ∫ g*·X·g` therefore sends `X` to `½·tr(X)·I`: it keeps the trace and
discards everything else, so a traceless `X` maps to `0` (`haar_su2_transfer_annihilates`). That is a
statement about this one integral over `SU 2`; no lattice or separation enters it.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` is the second moment's; the `1` and `0` are the two values of `δ_{ij}`, written here as an `if`. -/
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
  rw [integral_finsetSum _
    (fun ab _ => (entry_prod_integrable ab.2 j ab.1 i).const_mul (X ab.1 ab.2))]
  simp_rw [integral_const_mul, haar_su2_second_moment]
  clear hexp
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.trace_fin_two]
  by_cases h : i = j <;> simp_all [eq_comm] <;> ring

/-- If `tr X = 0` then `∫ (g*·X·g)_{ij} dHaar = 0`, for both indices. Immediate from `haar_su2_transfer`,
whose right-hand side carries `tr X` as a factor.
DERIVED: the `2`s are the size of the fundamental; the hypothesis's `0` and the conclusion's `0` are the same scalar, multiplied through by `½·δ_{ij}`. -/
theorem haar_su2_transfer_annihilates (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : Matrix.trace X = 0) (i j : Fin 2) :
    ∫ g : SU 2, (star (g : Matrix (Fin 2) (Fin 2) ℂ) * X * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
        ∂(probHaar (SU 2)) = 0 := by
  rw [haar_su2_transfer, hX]; ring

/-- Left multiplication by the diagonal `h0` scales a whole row: `(h0·g)_{pq} = (h0)_{pp}·g_{pq}`, for
every `g : SU 2` and both indices. The shared step behind the third- and fourth-moment phase computations.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
theorem h0_mul_entry (g : SU 2) (p q : Fin 2) :
    ((h0 * g : SU 2) : Matrix (Fin 2) (Fin 2) ℂ) p q
      = h0mat p p * (g : Matrix (Fin 2) (Fin 2) ℂ) p q := by
  rw [Submonoid.coe_mul]; show (h0mat * (g : Matrix (Fin 2) (Fin 2) ℂ)) p q = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]; fin_cases p <;> simp [h0mat]

/-- The third Haar moment vanishes for every index choice, with no hypothesis:
`∫ U_{ij}·U_{kl}·conj(U_{mn}) dHaar = 0`, all six indices universally quantified.

Under `U ↦ h0·U` the integrand picks up `(h0)_{ii}(h0)_{kk}·conj((h0)_{mm}) = i^{s_i+s_k-s_m}`, where each
`s` is `1` or `-1`. A sum of three odd numbers is odd, so the phase is `±i` and never `1`, and `c = φ·c`
gives `c = 0`. Two fundamentals against one conjugate is an odd tensor power, which carries no invariant.
Unlike `offdiag_h0`, no phase condition has to be assumed — `fin_cases` checks all eight row choices.
DERIVED: the `2`s are the size of the fundamental; the `0` on the right is forced, since the phase differs from `1` for every row-index choice. -/
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
      simp only [h0mat, 
        Complex.conj_I] <;> norm_num [Complex.ext_iff]
  have hz : (1 - h0mat i i * h0mat k k * (starRingEnd ℂ) (h0mat m m))
      * (∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) i j * (g : Matrix (Fin 2) (Fin 2) ℂ) k l
        * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) m n) ∂(probHaar (SU 2))) = 0 := by
    rw [sub_mul, one_mul, ← step, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hφ))

#print axioms haar_su2_second_moment
#print axioms haar_su2_two_point
/-- A fourth moment vanishes under an explicit phase hypothesis on its row indices: from
`(h0)_{ii}(h0)_{kk}·conj((h0)_{mm})·conj((h0)_{pp}) ≠ 1` it concludes
`∫ U_{ij}U_{kl}conj(U_{mn})conj(U_{pq}) dHaar = 0`. The proof is the same `U ↦ h0·U` substitution as
`haar_su2_third_moment`, but here the phase is `i^{s_i+s_k-s_m-s_p}` with each `s` equal to `1` or `-1`,
so the exponent is even, the phase can be `1`, and the condition has to be assumed rather than checked.

Scope: the hypothesis is strictly stronger than "the row indices are unbalanced". The exponent ranges over
`-4, -2, 0, 2, 4`, and `i^{±4} = 1` as well as `i^0 = 1`: at `i = k = 0` and `m = p = 1` the exponent is
`4`, the phase is `1`, and the hypothesis fails even though `s_i + s_k ≠ s_m + s_p`. The column indices
`j`, `l`, `n`, `q` are unconstrained.
DERIVED: the `2`s are the size of the fundamental; the `1` is the phase value the hypothesis excludes, and the `0` follows from `1 - φ` being invertible in `ℂ`. -/
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

/-! ### `SU(2)` pseudoreality

For `g ∈ SU(2)` the conjugate of an entry is again an entry, up to sign: `star g = adjugate g`
(`su2_star_eq`), which gives `conj(g₀₀) = g₁₁`, `conj(g₁₁) = g₀₀`, `conj(g₀₁) = -g₁₀` and
`conj(g₁₀) = -g₀₁`. Every conjugate can therefore be rewritten as a plain fundamental entry, which is what
turns `∫ U·U` into a second moment in `haar_su2_two_fund`, and what lets the fourth-moment lemmas below
work with the real function `f00`. This is specific to `SU(2)`: it uses `det g = 1` together with the
`2 × 2` adjugate formula. -/

/-- Pseudoreality in matrix form: for `g : SU 2`, `star g = !![g₁₁, -g₀₁; -g₁₀, g₀₀]`. Unitarity gives
`star g = g⁻¹` and `det g = 1` turns `g⁻¹` into the adjugate, which for a `2 × 2` matrix is that explicit
swap-and-negate. Both inputs are read off `Matrix.mem_specialUnitaryGroup_iff`, so the determinant
condition is load-bearing: this fails for a merely unitary `g`.
DERIVED: the `2`s are the size of the fundamental; the index literals `0` and `1` are the four positions of a `2 × 2` matrix, and the entry pattern is `Matrix.adjugate_fin_two`. -/
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

/-- Pseudoreality at one entry: `conj(g₀₀) = g₁₁` for every `g : SU 2`. Read off `su2_star_eq` at
position `(0, 0)`.
DERIVED: the `2`s are the size of the fundamental; `0 0` and `1 1` are the two positions `su2_star_eq` relates. -/
theorem su2_conj_00 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  have h := congrFun (congrFun (su2_star_eq g) 0) 0
  simpa [Matrix.star_apply, Complex.star_def] using h

/-- Pseudoreality at one entry: `conj(g₁₁) = g₀₀` for every `g : SU 2`. Read off `su2_star_eq` at
position `(1, 1)`.
DERIVED: the `2`s are the size of the fundamental; `1 1` and `0 0` are the two positions `su2_star_eq` relates. -/
theorem su2_conj_11 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
  have h := congrFun (congrFun (su2_star_eq g) 1) 1
  simpa [Matrix.star_apply, Complex.star_def] using h

/-- Pseudoreality at one entry: `conj(g₀₁) = -g₁₀` for every `g : SU 2`. Read off `su2_star_eq` at
position `(1, 0)`; the sign is the one carried by the `2 × 2` adjugate.
DERIVED: the `2`s are the size of the fundamental; `0 1` and `1 0` are the two positions `su2_star_eq` relates, and the minus sign is the adjugate's. -/
theorem su2_conj_01 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
  have h := congrFun (congrFun (su2_star_eq g) 1) 0
  simpa [Matrix.star_apply, Complex.star_def] using h

/-- Pseudoreality at one entry: `conj(g₁₀) = -g₀₁` for every `g : SU 2`. Read off `su2_star_eq` at
position `(0, 1)`; the sign is the one carried by the `2 × 2` adjugate.
DERIVED: the `2`s are the size of the fundamental; `1 0` and `0 1` are the two positions `su2_star_eq` relates, and the minus sign is the adjugate's. -/
theorem su2_conj_10 (g : SU 2) :
    (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = -(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
  have h := congrFun (congrFun (su2_star_eq g) 0) 1
  simpa [Matrix.star_apply, Complex.star_def] using h

#print axioms haar_su2_shared_link
#print axioms haar_su2_third_moment
#print axioms haar_su2_fourth_moment_unbalanced
/-- The `2 × 2` Levi-Civita tensor `ε = !![0, 1; -1, 0]` over `ℂ`. Entrywise identical to `wmat` above,
but introduced as a tensor rather than as a group element, and not `noncomputable`.
DERIVED: the `2`s are the size of the fundamental; the entries `0, 1, -1, 0` are the antisymmetric unit tensor in two dimensions. -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The two-fundamental Haar moment, with no conjugate: `∫ U_{ab}·U_{cd} dHaar = ½·(ε_{ac}·ε_{bd})`, for
all four indices. Pseudoreality (`su2_conj_00` through `su2_conj_10`) rewrites the second factor as
`±conj(U_{c'd'})`, turning the integral into `haar_su2_second_moment`; `fin_cases` over `c` and `d` then
matches the resulting `±½·δ` against `ε_{ac}·ε_{bd}`. Both sides vanish unless `a ≠ c` and `b ≠ d`.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` is the second moment's own `1 / 2`, and the signs come from `eps`, not from a sign convention chosen here. -/
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
    fin_cases a <;> fin_cases b <;> simp [eps]
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 0 * eps b 1)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
          = -((g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) by
          rw [show (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
            = -(starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) by rw [su2_conj_10]; ring]; ring)),
      integral_neg, haar_su2_second_moment a b 1 0]
    fin_cases a <;> fin_cases b <;> simp [eps]
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 1 * eps b 0)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
          = -((g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1)) by
          rw [show (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
            = -(starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) by rw [su2_conj_01]; ring]; ring)),
      integral_neg, haar_su2_second_moment a b 0 1]
    fin_cases a <;> fin_cases b <;> simp [eps]
  · show ∫ g : SU 2, (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        ∂(probHaar (SU 2)) = (1 / 2 : ℂ) * (eps a 1 * eps b 1)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun g : SU 2 =>
        show (g : Matrix (Fin 2) (Fin 2) ℂ) a b * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
          = (g : Matrix (Fin 2) (Fin 2) ℂ) a b
            * (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) by rw [su2_conj_00])),
      haar_su2_second_moment a b 0 0]
    fin_cases a <;> fin_cases b <;> simp [eps]

/-- The trace of the fundamental is real on `SU(2)`: `conj(tr g) = tr g`, for every `g : SU 2`.
Conjugation exchanges the two diagonal entries (`su2_conj_00`, `su2_conj_11`), so their sum is fixed.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
theorem su2_trace_real (g : SU 2) :
    (starRingEnd ℂ) (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ))
      = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.trace_fin_two, map_add, su2_conj_00, su2_conj_11]; ring

/-- `f00 g = |g₀₀|²`, as a real number via `Complex.normSq`. By pseudoreality (`su2_conj_00`) it also
equals `g₀₀·g₁₁`, which is what lets the fourth-moment lemmas below stay inside `ℝ`.
DERIVED: the `2` is the fundamental representation of `SU(2)`, and `0 0` is the top-left entry. -/
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

/-- `∫ f00 dHaar = 1/2`: the diagonal second moment in real form. `haar_su2_second_moment 0 0 0 0` gives
the complex statement, `Complex.mul_conj` identifies the integrand with `f00`, and `Complex.ofReal_inj`
brings the value back to `ℝ`.
DERIVED: the `2` is the fundamental representation of `SU(2)`; `1 / 2` is carried over from `haar_su2_second_moment`. -/
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

/-- Two-sided bounds on the fourth diagonal moment: `1/4 ≤ ∫ (f00)² dHaar ≤ 1/2`, stated as a conjunction.

The lower bound expands `∫ (f00 - 1/2)² ≥ 0` and uses `f00_mean`. The upper bound uses `f00² ≤ f00`, which
holds because `0 ≤ f00 ≤ 1` (`f00_nonneg`, `f00_le_one`), integrated with `integral_mono` against
`f00_mean`. Both directions need `probHaar` to be a probability measure, supplied by
`isProbabilityMeasure_probHaar`.

Scope: this brackets the value. No exact value for `∫ (f00)²` is proved anywhere in this file.
DERIVED: the `2` is the fundamental representation of `SU(2)`; `1 / 4` is `(∫ f00)² = (1/2)²` from `f00_mean`, and `1 / 2` is `∫ f00` itself, reachable because `f00² ≤ f00` on `[0, 1]`. -/
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

/-- The companion balanced four-fundamental moment, expressed through the same integral:
`∫ U₀₀U₁₁·U₀₁U₁₀ dHaar = ∫ (f00)² dHaar - 1/2`.

Pointwise, `U₀₀U₁₁ = f00` by pseudoreality and `U₀₁U₁₀ = f00 - 1` because `det g = 1`, so the integrand is
the real function `f00² - f00`; `f00_mean` supplies the `-½`.

The right-hand side still contains an integral, so this relates the two balanced fourth moments rather
than evaluating either. `haar_su2_fourth_moment_diag_bounds` puts the remaining integral in `[1/4, 1/2]`.
DERIVED: the `2` is the fundamental representation of `SU(2)`; the index literals `0 0`, `1 1`, `0 1` and `1 0` name the four entries of a `2 × 2` matrix; the `1 / 2` is `∫ f00` from `f00_mean`. -/
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
/-- The `ℂ`-linear map `M₂(ℂ) →ₗ[ℂ] M₂(ℂ)` given by `X ↦ (½·tr X)·I`, bundled with its additivity and
homogeneity proofs. `transferOp_eq_integral` identifies it entrywise with the Haar integral `∫ g*·X·g`, so
the closed form is a theorem about that integral rather than an extra assumption. This is a definition on
`2 × 2` matrices; nothing about a lattice enters it.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` is `1 / tr(1)` for the `2 × 2` identity, the normalization that makes `transferOp 1 = 1`. -/
noncomputable def transferOp : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := ((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_add' X Y := by rw [Matrix.trace_add, mul_add, add_smul]
  map_smul' c X := by
    show ((1 / 2 : ℂ) * Matrix.trace (c • X)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = c • (((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [Matrix.trace_smul, smul_eq_mul, smul_smul]; congr 1; ring

theorem transferOp_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferOp X = ((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

/-- `transferOp X` agrees entrywise with `∫ (g*·X·g)_{ij} dHaar`, by `haar_su2_transfer` and
`transferOp_apply`. This is what ties the closed-form definition to the group average.
DERIVED: the `2`s are the size of the fundamental representation of `SU(2)`. -/
theorem transferOp_eq_integral (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    transferOp X i j
      = ∫ g : SU 2, (star (g : Matrix (Fin 2) (Fin 2) ℂ) * X * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j
        ∂(probHaar (SU 2)) := by
  rw [haar_su2_transfer, transferOp_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- `transferOp` fixes the identity matrix: `transferOp 1 = 1`, so `I` is an eigenvector with eigenvalue
`1`. `Matrix.trace_one` gives `tr 1 = Fintype.card (Fin 2) = 2`, which the `½` cancels.
DERIVED: the `2`s are the size of the fundamental; both `1`s are the identity matrix, and they agree because `½ · tr(1) = ½ · 2 = 1`. -/
theorem transferOp_vacuum : transferOp (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [transferOp_apply, Matrix.trace_one, Fintype.card_fin]; norm_num

/-- `transferOp` sends every traceless matrix to `0`: `tr X = 0 → transferOp X = 0`. Immediate from
`transferOp_apply`, since `tr X` is a factor of the value, so the traceless matrices are contained in the
kernel and carry eigenvalue `0`.
DERIVED: the `2`s are the size of the fundamental; the hypothesis's `0` and the conclusion's `0` are the same scalar, scaled by `½` and applied to `I`. -/
theorem transferOp_annihilates (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Matrix.trace X = 0) :
    transferOp X = 0 := by
  rw [transferOp_apply, hX]; simp

/-- `transferOp` is idempotent: `transferOp (transferOp X) = transferOp X`, for every `X`. The inner value
is a multiple of `I`, whose trace is `2`, and the outer `½` cancels that, returning the same multiple.
`transferOp_pow` iterates this.
DERIVED: the `2`s are the size of the fundamental; the statement carries no other numeral, the cancelling `½` and `tr(1) = 2` living in the proof. -/
theorem transferOp_idem (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferOp (transferOp X) = transferOp X := by
  rw [transferOp_apply, transferOp_apply, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  congr 1
  push_cast
  ring

/-- Every positive iterate of `transferOp` equals `transferOp`: `transferOp^[n + 1] X = transferOp X`, for
all `n : ℕ`, by induction with `transferOp_idem` at each step. The exponent is written `n + 1` because the
case `n = 0` is excluded: `transferOp^[0]` is the identity map, and the equation fails for any `X` that is
not already a multiple of `I`.
DERIVED: the `2`s are the size of the fundamental; the `1` in `n + 1` is what keeps the exponent positive; the `0` opening the first match arm is the base case `transferOp^[0 + 1] X = transferOp X`, closed by `rfl`. -/
theorem transferOp_pow (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ n, (transferOp^[n + 1]) X = transferOp X
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', transferOp_pow X n, transferOp_idem]

/-- A traceless matrix is sent to `0` by every positive iterate: `tr X = 0 → transferOp^[n + 1] X = 0`,
for all `n : ℕ`. It composes `transferOp_pow` with `transferOp_annihilates`, so it adds no strength beyond
the single-step result — the iterate collapses to one application before the hypothesis is used.
DERIVED: the `2`s are the size of the fundamental; the hypothesis's `0` and the conclusion's `0` are the same scalar; the `1` in `n + 1` keeps the exponent positive. -/
theorem transferOp_pow_annihilates (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Matrix.trace X = 0) (n : ℕ) :
    (transferOp^[n + 1]) X = 0 := by
  rw [transferOp_pow X n, transferOp_annihilates X hX]

/-- The closed form again: `transferOp X = (½·tr X)·I`. The statement is identical to `transferOp_apply`
above and its proof is likewise `rfl`; the name points at the reading that every value lies on the line
`ℂ·I`, but what is stated is the defining formula, not a claim about the range as a submodule.
DERIVED: the `2`s are the size of the fundamental; the `1 / 2` is the normalization in `transferOp`'s own definition. -/
theorem transferOp_range (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferOp X = ((1 / 2 : ℂ) * Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

#print axioms haar_su2_transfer
#print axioms haar_su2_transfer_annihilates
#print axioms transferOp_idem
#print axioms transferOp_pow
#print axioms transferOp_pow_annihilates

end MassGap.SUN
