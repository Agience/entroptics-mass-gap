import Mathlib
import MassGap.GaugeGroup
import MassGap.PurityCharCoeff

/-!
# MassGap.PurityRepCharacter — the temporal character coefficients are nonnegative for every representation

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
uses `a_σ = (1/d_σ) ∫ e^{b g} χ_σ ≥ 0`, `g = Re Tr ρ_F / d`, from the expansion of `e^{b g}` as a
positive sum of characters. For a compact gauge group `G` (`GaugeGroup`) with defining
representation `ρ_F = repM G` of dimension `d`, and every continuous matrix representation
`σ : G →* Matrix ι ι ℂ`:

* `proj`, `proj_mul`, `proj_mul_self`: `P_σ = ∫ σ(g) dg` satisfies `P_σ σ(h) = P_σ = P_σ²`
  (right invariance of Haar measure).
* `integral_trace`, `re_integral_trace_nonneg`: `∫ Tr σ = rank P_σ`, a natural number.
* `kron`, `conjRep`: the tensor product `σ ⊗ τ` and the conjugate `σ̄` are continuous
  representations, with `Tr (σ ⊗ τ) = Tr σ · Tr τ` and `Tr σ̄ = conj (Tr σ)`.
* `re_integral_pow_mul_trace_nonneg`: `Re ∫ (2 Re Tr ρ_F)ⁿ Tr σ ≥ 0`, by induction on `n` through
  `(2 Re Tr ρ_F) Tr σ = Tr (ρ_F ⊗ σ) + Tr (ρ̄_F ⊗ σ)`.
* `repHom`, `abs_g_le`: `ρ_F` as a monoid hom; `|g| ≤ 1`.
* `moment_nonneg`: `∫ gⁿ Re Tr σ ≥ 0`.
* `integral_exp_mul_nonneg`, `charCoeff_nonneg`: `∫ e^{b g} Re Tr σ ≥ 0` and `a_σ ≥ 0` at `b ≥ 0`,
  every `d_σ > 0` (in particular `d_σ = dim σ`), through `PurityCharCoeff.integral_exp_mul_nonneg_of_moment`.

No fusion rule, orthogonality relation or classification of irreducibles enters: `moment_nonneg`
proves the conclusion of `PurityCharCoeff.moment_nonneg` for the characters `Re Tr σ` of continuous
representations of every compact gauge group, `SU(N)` at every `N` included, without its hypotheses
`hfus`, `h0`.

DERIVED (module-wide): `2` in `2 Re Tr ρ_F = Tr ρ_F + conj (Tr ρ_F)`.
-/

namespace MassGap.PurityRepCharacter

open MeasureTheory Module MassGap MassGap.CompactGauge MassGap.GaugeGroup

open scoped Matrix Kronecker

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

theorem integrable_cont {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    {f : G → E} (hf : Continuous f) : Integrable f (probHaar G) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-! ## The projection `∫ σ` -/

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `P_σ = ∫ σ(g) dg`, entrywise. -/
noncomputable def proj (σ : G →* Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ g, σ g i j ∂probHaar G

/-- `P_σ σ(h) = P_σ` (right invariance). -/
theorem proj_mul {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (h : G) : proj σ * σ h = proj σ := by
  ext i j
  have hs : ∀ g : G, ∑ k, σ g i k * σ h k j = σ (g * h) i j := fun g => by
    rw [map_mul, Matrix.mul_apply]
  calc (proj σ * σ h) i j
      = ∑ k, ∫ g, σ g i k * σ h k j ∂probHaar G := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => (integral_mul_const _ _).symm
    _ = ∫ g, ∑ k, σ g i k * σ h k j ∂probHaar G :=
        (integral_finsetSum _ fun k _ => (integrable_cont (hσ.matrix_elem i k)).mul_const _).symm
    _ = ∫ g, σ (g * h) i j ∂probHaar G := by simp_rw [hs]
    _ = proj σ i j := integral_mul_right_eq_self (fun g => σ g i j) h

/-- `P_σ² = P_σ`. -/
theorem proj_mul_self {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) : proj σ * proj σ = proj σ := by
  ext i j
  have hs : ∀ g : G, ∑ k, proj σ i k * σ g k j = proj σ i j := fun g => by
    have := congrFun (congrFun (proj_mul hσ g) i) j
    rwa [Matrix.mul_apply] at this
  calc (proj σ * proj σ) i j
      = ∑ k, ∫ g, proj σ i k * σ g k j ∂probHaar G := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    _ = ∫ g, ∑ k, proj σ i k * σ g k j ∂probHaar G :=
        (integral_finsetSum _ fun k _ => (integrable_cont (hσ.matrix_elem k j)).const_mul _).symm
    _ = proj σ i j := by simp_rw [hs]; simp

/-- `∫ Tr σ = rank P_σ`. -/
theorem integral_trace {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) :
    ∫ g, Matrix.trace (σ g) ∂probHaar G =
      (finrank ℂ (LinearMap.range (Matrix.toLin' (proj σ))) : ℂ) := by
  have hid : IsIdempotentElem (Matrix.toLin' (proj σ)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, proj_mul_self hσ]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [Matrix.trace_toLin'_eq] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag]
  exact integral_finsetSum _ fun i _ => integrable_cont (hσ.matrix_elem i i)

/-- `Re ∫ Tr σ ≥ 0`. -/
theorem re_integral_trace_nonneg {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) :
    0 ≤ (∫ g, Matrix.trace (σ g) ∂probHaar G).re := by
  rw [integral_trace hσ, Complex.natCast_re]
  exact Nat.cast_nonneg _

end Proj

/-! ## Tensor products and conjugates -/

section Constructions

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The tensor product `σ ⊗ τ`. -/
def kron (σ : G →* Matrix ι ι ℂ) (τ : G →* Matrix κ κ ℂ) : G →* Matrix (ι × κ) (ι × κ) ℂ where
  toFun g := σ g ⊗ₖ τ g
  map_one' := by simp only [map_one, Matrix.one_kronecker_one]
  map_mul' g h := by simp only [map_mul, Matrix.mul_kronecker_mul]

theorem kron_apply (σ : G →* Matrix ι ι ℂ) (τ : G →* Matrix κ κ ℂ) (g : G) :
    kron σ τ g = σ g ⊗ₖ τ g := rfl

theorem continuous_kron {σ : G →* Matrix ι ι ℂ} {τ : G →* Matrix κ κ ℂ} (hσ : Continuous σ)
    (hτ : Continuous τ) : Continuous (kron σ τ) :=
  continuous_pi fun a => continuous_pi fun b => by
    show Continuous fun g => σ g a.1 b.1 * τ g a.2 b.2
    exact (hσ.matrix_elem a.1 b.1).mul (hτ.matrix_elem a.2 b.2)

theorem trace_kron (σ : G →* Matrix ι ι ℂ) (τ : G →* Matrix κ κ ℂ) (g : G) :
    Matrix.trace (kron σ τ g) = Matrix.trace (σ g) * Matrix.trace (τ g) := by
  rw [kron_apply, Matrix.trace_kronecker]

/-- The conjugate representation `σ̄`. -/
noncomputable def conjRep (σ : G →* Matrix ι ι ℂ) : G →* Matrix ι ι ℂ :=
  (starRingEnd ℂ).mapMatrix.toMonoidHom.comp σ

theorem conjRep_apply (σ : G →* Matrix ι ι ℂ) (g : G) :
    conjRep σ g = (σ g).map (starRingEnd ℂ) := rfl

theorem continuous_conjRep {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) :
    Continuous (conjRep σ) := by
  have he : (conjRep σ : G → Matrix ι ι ℂ) = fun g => (σ g).map (starRingEnd ℂ) := rfl
  rw [he]
  exact hσ.matrix_map Complex.continuous_conj

theorem trace_conjRep (σ : G →* Matrix ι ι ℂ) (g : G) :
    Matrix.trace (conjRep σ g) = starRingEnd ℂ (Matrix.trace (σ g)) := by
  simp only [conjRep_apply, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

end Constructions

/-! ## The defining representation as a hom -/

variable (G) in
/-- `ρ_F = repM G` as a monoid hom. -/
def repHom : G →* Matrix (Fin (dim G)) (Fin (dim G)) ℂ where
  toFun := repM G
  map_one' := repM_one
  map_mul' := repM_mul

theorem repHom_apply (g : G) : repHom G g = repM G g := rfl

theorem continuous_repHom : Continuous (repHom G) := continuous_repM

/-! ## Moment positivity -/

section Moments

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_pow_mul_trace {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (n : ℕ) :
    Continuous fun g => (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) * Matrix.trace (σ g) :=
  (Complex.continuous_ofReal.comp ((continuous_const.mul
    (Complex.continuous_re.comp continuous_repM.matrix_trace)).pow n)).mul hσ.matrix_trace

/-- `(2 Re Tr ρ_F)ⁿ⁺¹ Tr σ = (2 Re Tr ρ_F)ⁿ (Tr (ρ_F ⊗ σ) + Tr (ρ̄_F ⊗ σ))`. -/
theorem pow_succ_mul_trace (σ : G →* Matrix ι ι ℂ) (n : ℕ) (g : G) :
    (((2 * (Matrix.trace (repM G g)).re) ^ (n + 1) : ℝ) : ℂ) * Matrix.trace (σ g) =
      (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) * Matrix.trace (kron (repHom G) σ g) +
      (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) *
        Matrix.trace (kron (conjRep (repHom G)) σ g) := by
  rw [trace_kron, trace_kron, trace_conjRep, repHom_apply]
  have h2 : (2 * ((Matrix.trace (repM G g)).re : ℂ)) =
      Matrix.trace (repM G g) + starRingEnd ℂ (Matrix.trace (repM G g)) := by
    apply Complex.ext <;> simp <;> ring
  push_cast
  rw [pow_succ, h2]
  ring

/-- `Re ∫ (2 Re Tr ρ_F)ⁿ Tr σ ≥ 0` for every continuous representation `σ`. -/
theorem re_integral_pow_mul_trace_nonneg (n : ℕ) :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {σ : G →* Matrix ι ι ℂ}, Continuous σ →
      0 ≤ (∫ g, (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) * Matrix.trace (σ g)
        ∂probHaar G).re := by
  induction n with
  | zero =>
    intro ι _ _ σ hσ
    simpa using re_integral_trace_nonneg hσ
  | succ n ih =>
    intro ι _ _ σ hσ
    have h1 := continuous_kron continuous_repHom hσ
    have h2 := continuous_kron (continuous_conjRep continuous_repHom) hσ
    simp_rw [pow_succ_mul_trace σ n]
    rw [integral_add (integrable_cont (continuous_pow_mul_trace h1 n))
      (integrable_cont (continuous_pow_mul_trace h2 n)), Complex.add_re]
    exact add_nonneg (ih h1) (ih h2)

/-- `∫ gⁿ Re Tr σ ≥ 0`, `g = Re Tr ρ_F / d`. -/
theorem moment_nonneg {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (n : ℕ) :
    0 ≤ ∫ g, ((Matrix.trace (repM G g)).re / dim G) ^ n * (Matrix.trace (σ g)).re
      ∂probHaar G := by
  have hd : (dim G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (dim_pos (G := G)).ne'
  have h := re_integral_pow_mul_trace_nonneg n hσ
  have hre : ∫ g, ((((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) *
      Matrix.trace (σ g)).re ∂probHaar G =
      (∫ g, (((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) * Matrix.trace (σ g)
        ∂probHaar G).re :=
    integral_re (integrable_cont (continuous_pow_mul_trace hσ n))
  rw [← hre] at h
  have he : ∀ g : G, ((Matrix.trace (repM G g)).re / dim G) ^ n * (Matrix.trace (σ g)).re =
      ((2 * dim G : ℝ) ^ n)⁻¹ *
        ((((2 * (Matrix.trace (repM G g)).re) ^ n : ℝ) : ℂ) * Matrix.trace (σ g)).re := fun g => by
    rw [Complex.re_ofReal_mul, div_pow, mul_pow, mul_pow, ← mul_assoc]
    congr 1
    field_simp
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_nonneg (by positivity) h

theorem abs_g_le (g : G) : |(Matrix.trace (repM G g)).re / dim G| ≤ 1 := by
  have hd : (0 : ℝ) < dim G := Nat.cast_pos.mpr dim_pos
  rw [abs_div, abs_of_pos hd, div_le_one hd]
  exact abs_re_trace_repM_le g

/-- `∫ e^{b g} Re Tr σ ≥ 0` at `b ≥ 0`. -/
theorem integral_exp_mul_nonneg {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) {b : ℝ}
    (hb : 0 ≤ b) :
    0 ≤ ∫ g, Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) * (Matrix.trace (σ g)).re
      ∂probHaar G := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hσ.matrix_trace.continuousOn
  exact PurityCharCoeff.integral_exp_mul_nonneg_of_moment
    ((Complex.continuous_re.comp continuous_repM.matrix_trace).div_const _).measurable abs_g_le
    (Complex.continuous_re.comp hσ.matrix_trace).measurable
    (fun g => (Complex.abs_re_le_norm _).trans (hB g (Set.mem_univ g))) (moment_nonneg hσ) hb

/-- `(1/d_σ) ∫ e^{b g} Re Tr σ ≥ 0` at `b ≥ 0`, for every `d_σ > 0` (in particular `d_σ = dim σ`). -/
theorem charCoeff_nonneg {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) {b : ℝ} (hb : 0 ≤ b)
    {dσ : ℝ} (hd : 0 < dσ) :
    0 ≤ (∫ g, Real.exp (b * ((Matrix.trace (repM G g)).re / dim G)) *
      (Matrix.trace (σ g)).re ∂probHaar G) / dσ :=
  div_nonneg (integral_exp_mul_nonneg hσ hb) hd.le

end Moments

end MassGap.PurityRepCharacter

#print axioms MassGap.PurityRepCharacter.integrable_cont
#print axioms MassGap.PurityRepCharacter.proj_mul
#print axioms MassGap.PurityRepCharacter.proj_mul_self
#print axioms MassGap.PurityRepCharacter.integral_trace
#print axioms MassGap.PurityRepCharacter.re_integral_trace_nonneg
#print axioms MassGap.PurityRepCharacter.continuous_kron
#print axioms MassGap.PurityRepCharacter.trace_kron
#print axioms MassGap.PurityRepCharacter.continuous_conjRep
#print axioms MassGap.PurityRepCharacter.trace_conjRep
#print axioms MassGap.PurityRepCharacter.continuous_repHom
#print axioms MassGap.PurityRepCharacter.continuous_pow_mul_trace
#print axioms MassGap.PurityRepCharacter.pow_succ_mul_trace
#print axioms MassGap.PurityRepCharacter.re_integral_pow_mul_trace_nonneg
#print axioms MassGap.PurityRepCharacter.moment_nonneg
#print axioms MassGap.PurityRepCharacter.abs_g_le
#print axioms MassGap.PurityRepCharacter.integral_exp_mul_nonneg
#print axioms MassGap.PurityRepCharacter.charCoeff_nonneg
