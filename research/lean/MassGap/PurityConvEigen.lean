import Mathlib
import MassGap.PurityRepCharacter

/-!
# MassGap.PurityConvEigen — Schur's lemma, Schur orthogonality and the convolution eigenvalue `a_π`

Appendix C of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
states: "Orthogonality gives the convolution eigenvalue `a_π` with multiplicity `d_π²`". For a
compact gauge group `G` (`GaugeGroup`) with normalized Haar measure, a continuous matrix
representation `σ : G →* Matrix ι ι ℂ`, `d = card ι`:

* `mint`: the entrywise Haar integral of a matrix-valued function; `mint_mul_right`,
  `mint_mul_left`, `trace_mint`, `mint_left`, `mint_right`, `mint_conj`: linearity and invariance.
* `Irred`: every subspace of `ι → ℂ` invariant under all `σ g` is `⊥` or `⊤`.
* `schur`, `eq_trace_smul`: for irreducible `σ`, a matrix commuting with every `σ g` is
  `(Tr A / d) • 1`.
* `mint_comm`: `∫ F` commutes with `σ` when `F (x h x⁻¹) = σ x F(h) σ x⁻¹`.
* `conjAvg_eq`: `∫ σ(g) E σ(g⁻¹) dg = (Tr E / d) • 1` for irreducible `σ`.
* `orthogonality`: `∫ σ(g)ᵢⱼ σ(g⁻¹)ₗₖ dg = δᵢₖ δⱼₗ / d`; `orthogonality_unitary`: for unitary `σ`,
  `∫ σ(g)ᵢⱼ conj σ(g)ₖₗ dg = δᵢₖ δⱼₗ / d`.
* `linearIndependent_coeff`, `finrank_span_coeff`: the `d²` matrix coefficients `g ↦ σ(g)ᵢⱼ` are
  linearly independent and span a space of dimension `d²`.
* `mint_kernel`: `∫ k(h) σ(h⁻¹) dh = a_σ · 1` for irreducible `σ` and a continuous class
  function `k`.
* `conv_coeff`: for a continuous class function `k`, the convolution
  `(k ⋆ f)(g) = ∫ k(h) f(h⁻¹ g) dh` maps every matrix coefficient `σᵢⱼ` to `a_σ σᵢⱼ`,
  `a_σ = (1/d) ∫ k(h) Tr σ(h⁻¹) dh`; `conv_eigen_multiplicity`: the `a_σ`-eigenspace of
  `k ⋆ ·` contains `d²` linearly independent functions.

`PurityL2.eq_zero_of_inner_coeff` gives completeness of the irreducible coefficients in `L²(G)`;
`PurityKernelSeries.hasSum_dim_sq_eigenval` gives `Σ_π d_π² a_π = k(1)` for the Wilson kernel
`k(g) = exp(b Re Tr g / N)`.
-/

namespace MassGap.PurityConvEigen

open MeasureTheory Module MassGap MassGap.CompactGauge MassGap.GaugeGroup
  MassGap.PurityRepCharacter

open scoped Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Entrywise Haar integrals of matrix-valued functions -/

/-- `∫ F(g) dg`, entrywise. -/
noncomputable def mint (F : G → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ g, F g i j ∂probHaar G

theorem mint_mul_right {F : G → Matrix ι ι ℂ} (hF : Continuous F) (A : Matrix ι ι ℂ) :
    mint F * A = mint (fun g => F g * A) := by
  ext i j
  simp only [mint, Matrix.mul_apply]
  symm
  rw [integral_finsetSum _ fun l _ => (integrable_cont (hF.matrix_elem i l)).mul_const (A l j)]
  exact Finset.sum_congr rfl fun l _ => integral_mul_const _ _

theorem mint_mul_left {F : G → Matrix ι ι ℂ} (hF : Continuous F) (A : Matrix ι ι ℂ) :
    A * mint F = mint (fun g => A * F g) := by
  ext i j
  simp only [mint, Matrix.mul_apply]
  symm
  rw [integral_finsetSum _ fun l _ => (integrable_cont (hF.matrix_elem l j)).const_mul (A i l)]
  exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _

theorem trace_mint {F : G → Matrix ι ι ℂ} (hF : Continuous F) :
    Matrix.trace (mint F) = ∫ g, Matrix.trace (F g) ∂probHaar G := by
  simp only [Matrix.trace, Matrix.diag, mint]
  exact (integral_finsetSum _ fun i _ => integrable_cont (hF.matrix_elem i i)).symm

theorem mint_left (F : G → Matrix ι ι ℂ) (x : G) : mint (fun h => F (x * h)) = mint F := by
  ext i j
  exact integral_mul_left_eq_self (fun h => F h i j) x

theorem mint_right (F : G → Matrix ι ι ℂ) (x : G) : mint (fun h => F (h * x)) = mint F := by
  ext i j
  exact integral_mul_right_eq_self (fun h => F h i j) x

theorem mint_conj (F : G → Matrix ι ι ℂ) (x : G) : mint (fun h => F (x * h * x⁻¹)) = mint F :=
  (mint_left (fun h => F (h * x⁻¹)) x).trans (mint_right F x⁻¹)

/-! ## Schur's lemma -/

/-- Every subspace of `ι → ℂ` invariant under all `σ g` is `⊥` or `⊤`. -/
def Irred (σ : G →* Matrix ι ι ℂ) : Prop :=
  ∀ W : Submodule ℂ (ι → ℂ), (∀ g, ∀ v ∈ W, σ g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

theorem inv_mul_rep (σ : G →* Matrix ι ι ℂ) (x : G) : σ x⁻¹ * σ x = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem mul_inv_rep (σ : G →* Matrix ι ι ℂ) (x : G) : σ x * σ x⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

/-- Schur's lemma: for irreducible `σ`, a matrix commuting with every `σ g` is scalar. -/
theorem schur [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hirr : Irred σ) {A : Matrix ι ι ℂ}
    (hA : ∀ g, A * σ g = σ g * A) : ∃ c : ℂ, A = c • 1 := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hinv : ∀ g, ∀ w ∈ Module.End.eigenspace (Matrix.toLin' A) c,
      σ g *ᵥ w ∈ Module.End.eigenspace (Matrix.toLin' A) c := by
    intro g w hw
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec, hA g, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have hne : Module.End.eigenspace (Matrix.toLin' A) c ≠ ⊥ := by
    intro h
    have hmem : v ∈ Module.End.eigenspace (Matrix.toLin' A) c :=
      Module.End.mem_eigenspace_iff.mpr hv.apply_eq_smul
    rw [h, Submodule.mem_bot] at hmem
    exact hv.2 hmem
  have htop := (hirr _ hinv).resolve_left hne
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun w => ?_)⟩
  have hw : w ∈ Module.End.eigenspace (Matrix.toLin' A) c := htop ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hw
  rw [hw, map_smul, Matrix.toLin'_one, LinearMap.smul_apply, LinearMap.id_apply]

/-- The scalar in Schur's lemma is `Tr A / d`. -/
theorem eq_trace_smul [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hirr : Irred σ) {A : Matrix ι ι ℂ}
    (hA : ∀ g, A * σ g = σ g * A) :
    A = (Matrix.trace A / Fintype.card ι) • (1 : Matrix ι ι ℂ) := by
  obtain ⟨c, rfl⟩ := schur hirr hA
  have hd : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_div_cancel_right₀ c hd]

/-- `∫ F` commutes with `σ` when `F` is `σ`-equivariant under conjugation. -/
theorem mint_comm {σ : G →* Matrix ι ι ℂ} {F : G → Matrix ι ι ℂ} (hF : Continuous F)
    (heq : ∀ x h, F (x * h * x⁻¹) = σ x * F h * σ x⁻¹) (x : G) :
    mint F * σ x = σ x * mint F := by
  have hconj : mint F = σ x * mint F * σ x⁻¹ := by
    calc mint F = mint (fun h => F (x * h * x⁻¹)) := (mint_conj F x).symm
      _ = mint (fun h => σ x * F h * σ x⁻¹) := by simp_rw [heq]
      _ = σ x * mint F * σ x⁻¹ := by
        rw [mint_mul_left hF, mint_mul_right (continuous_const.matrix_mul hF)]
  calc mint F * σ x = σ x * mint F * σ x⁻¹ * σ x := by rw [← hconj]
    _ = σ x * mint F := by rw [Matrix.mul_assoc (σ x * mint F), inv_mul_rep, Matrix.mul_one]

/-! ## Schur orthogonality -/

/-- `∫ σ(g) E σ(g⁻¹) dg`. -/
noncomputable def conjAvg (σ : G →* Matrix ι ι ℂ) (E : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  mint (fun g => σ g * E * σ g⁻¹)

theorem continuous_conj {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (E : Matrix ι ι ℂ) :
    Continuous fun g => σ g * E * σ g⁻¹ :=
  (hσ.matrix_mul continuous_const).matrix_mul (hσ.comp continuous_inv)

theorem conjAvg_comm {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (E : Matrix ι ι ℂ) (x : G) :
    conjAvg σ E * σ x = σ x * conjAvg σ E := by
  unfold conjAvg
  rw [mint_mul_right (continuous_conj hσ E), mint_mul_left (continuous_conj hσ E),
    ← mint_left (fun g => σ g * E * σ g⁻¹ * σ x) x]
  congr 1
  funext g
  simp only [map_mul, mul_inv_rev, Matrix.mul_assoc, inv_mul_rep, Matrix.mul_one]

theorem trace_conjAvg {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (E : Matrix ι ι ℂ) :
    Matrix.trace (conjAvg σ E) = Matrix.trace E := by
  unfold conjAvg
  rw [trace_mint (continuous_conj hσ E)]
  have h : ∀ g : G, Matrix.trace (σ g * E * σ g⁻¹) = Matrix.trace E := fun g => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, inv_mul_rep, Matrix.one_mul]
  simp_rw [h]
  simp

/-- `∫ σ(g) E σ(g⁻¹) dg = (Tr E / d) • 1` for irreducible `σ`. -/
theorem conjAvg_eq [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (hirr : Irred σ)
    (E : Matrix ι ι ℂ) :
    conjAvg σ E = (Matrix.trace E / Fintype.card ι) • (1 : Matrix ι ι ℂ) := by
  rw [eq_trace_smul hirr (conjAvg_comm hσ E), trace_conjAvg hσ E]

/-- Schur orthogonality: `∫ σ(g)ᵢⱼ σ(g⁻¹)ₗₖ dg = δᵢₖ δⱼₗ / d`. -/
theorem orthogonality [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (hirr : Irred σ)
    (i j k l : ι) :
    ∫ g, σ g i j * σ g⁻¹ l k ∂probHaar G =
      if (i, j) = (k, l) then (Fintype.card ι : ℂ)⁻¹ else 0 := by
  have h := congrFun (congrFun (conjAvg_eq hσ hirr (Matrix.single j l 1)) i) k
  have hentry : ∀ g : G, (σ g * Matrix.single j l (1 : ℂ) * σ g⁻¹ : Matrix ι ι ℂ) i k = σ g i j * σ g⁻¹ l k :=
    fun g => by
      simp [Matrix.mul_apply, Matrix.single, Finset.sum_ite_eq, ite_and]
  simp only [conjAvg, mint, hentry] at h
  rw [h]
  by_cases hjl : j = l
  · subst hjl
    rw [Matrix.trace_single_eq_same]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Matrix.one_apply_ne hik]
  · rw [Matrix.trace_single_eq_of_ne j l (1 : ℂ) hjl]
    simp [hjl]

/-- For unitary `σ`: `∫ σ(g)ᵢⱼ conj σ(g)ₖₗ dg = δᵢₖ δⱼₗ / d`. -/
theorem orthogonality_unitary [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hirr : Irred σ) (hu : ∀ g, σ g⁻¹ = (σ g)ᴴ) (i j k l : ι) :
    ∫ g, σ g i j * starRingEnd ℂ (σ g k l) ∂probHaar G =
      if (i, j) = (k, l) then (Fintype.card ι : ℂ)⁻¹ else 0 := by
  rw [← orthogonality hσ hirr i j k l]
  congr 1
  funext g
  rw [hu g, Matrix.conjTranspose_apply, RCLike.star_def]

/-! ## The matrix coefficients -/

/-- The matrix coefficient `g ↦ σ(g)ᵢⱼ`. -/
def coeff (σ : G →* Matrix ι ι ℂ) (p : ι × ι) : G → ℂ := fun g => σ g p.1 p.2

/-- The `d²` matrix coefficients of an irreducible `σ` are linearly independent. -/
theorem linearIndependent_coeff [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hirr : Irred σ) : LinearIndependent ℂ (coeff σ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have h0 : ∀ g : G, ∑ p, c p * σ g p.1 p.2 = 0 := fun g => by
    have := congrFun hc g
    simpa [coeff, Finset.sum_apply] using this
  have hd : (Fintype.card ι : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hint : ∫ g, (∑ p, c p * σ g p.1 p.2) * σ g⁻¹ q.2 q.1 ∂probHaar G =
      c q * (Fintype.card ι : ℂ)⁻¹ := by
    simp_rw [Finset.sum_mul, mul_assoc]
    have hterm : ∀ p : ι × ι, Continuous fun g => c p * (σ g p.1 p.2 * σ g⁻¹ q.2 q.1) := fun p =>
      continuous_const.mul ((hσ.matrix_elem p.1 p.2).mul
        ((hσ.comp continuous_inv).matrix_elem q.2 q.1))
    rw [integral_finsetSum _ fun p _ => integrable_cont (hterm p)]
    simp_rw [integral_const_mul]
    simp_rw [orthogonality hσ hirr _ _ q.1 q.2]
    simp [Prod.mk.eta]
  simp_rw [h0, zero_mul, integral_zero] at hint
  exact (mul_eq_zero.mp hint.symm).resolve_right hd

theorem finrank_span_coeff [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hirr : Irred σ) :
    finrank ℂ (Submodule.span ℂ (Set.range (coeff σ))) = Fintype.card ι ^ 2 := by
  rw [finrank_span_eq_card (linearIndependent_coeff hσ hirr), Fintype.card_prod, sq]

/-! ## The convolution eigenvalue -/

/-- `(k ⋆ f)(g) = ∫ k(h) f(h⁻¹ g) dh`. -/
noncomputable def conv (k f : G → ℂ) (g : G) : ℂ := ∫ h, k h * f (h⁻¹ * g) ∂probHaar G

/-- `a_σ = (1/d) ∫ k(h) Tr σ(h⁻¹) dh`. -/
noncomputable def eigenval (k : G → ℂ) (σ : G →* Matrix ι ι ℂ) : ℂ :=
  (∫ h, k h * Matrix.trace (σ h⁻¹) ∂probHaar G) / Fintype.card ι

/-- `∫ k(h) σ(h⁻¹) dh = a_σ · 1` for continuous irreducible `σ` and a continuous class
function `k`. -/
theorem mint_kernel [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (hirr : Irred σ)
    {k : G → ℂ} (hk : Continuous k) (hkc : ∀ x h, k (x * h * x⁻¹) = k h) :
    mint (fun h => k h • σ h⁻¹) = eigenval k σ • (1 : Matrix ι ι ℂ) := by
  have hF : Continuous fun h => k h • σ h⁻¹ := hk.smul (hσ.comp continuous_inv)
  have heq : ∀ x h, k (x * h * x⁻¹) • σ (x * h * x⁻¹)⁻¹ = σ x * (k h • σ h⁻¹) * σ x⁻¹ := by
    intro x h
    rw [hkc, Matrix.mul_smul, Matrix.smul_mul, mul_inv_rev, mul_inv_rev, inv_inv, map_mul,
      map_mul, Matrix.mul_assoc]
  rw [eq_trace_smul hirr (mint_comm hF heq), trace_mint hF, eigenval]
  simp only [Matrix.trace_smul, smul_eq_mul]

/-- For a continuous class function `k` and irreducible `σ`, `k ⋆ σᵢⱼ = a_σ σᵢⱼ`. -/
theorem conv_coeff [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ) (hirr : Irred σ)
    {k : G → ℂ} (hk : Continuous k) (hkc : ∀ x h, k (x * h * x⁻¹) = k h) (p : ι × ι) :
    conv k (coeff σ p) = eigenval k σ • coeff σ p := by
  have hF : Continuous fun h => k h • σ h⁻¹ := hk.smul (hσ.comp continuous_inv)
  funext g
  have h1 : conv k (coeff σ p) g = (mint (fun h => k h • σ h⁻¹) * σ g) p.1 p.2 := by
    rw [mint_mul_right hF]
    simp only [conv, coeff, mint, Matrix.smul_mul, ← map_mul, Matrix.smul_apply, smul_eq_mul]
  rw [h1, mint_kernel hσ hirr hk hkc, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply]
  rfl

/-- The `a_σ`-eigenspace of `k ⋆ ·` contains the `d²` linearly independent coefficients of `σ`. -/
theorem conv_eigen_multiplicity [Nonempty ι] {σ : G →* Matrix ι ι ℂ} (hσ : Continuous σ)
    (hirr : Irred σ) {k : G → ℂ} (hk : Continuous k) (hkc : ∀ x h, k (x * h * x⁻¹) = k h) :
    (∀ f ∈ Submodule.span ℂ (Set.range (coeff σ)), conv k f = eigenval k σ • f) ∧
      finrank ℂ (Submodule.span ℂ (Set.range (coeff σ))) = Fintype.card ι ^ 2 := by
  refine ⟨fun f hf => ?_, finrank_span_coeff hσ hirr⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  funext g
  have hterm : ∀ p : ι × ι, Continuous fun h => k h * (c p * σ (h⁻¹ * g) p.1 p.2) := fun p =>
    hk.mul (continuous_const.mul
      ((hσ.comp (continuous_inv.mul continuous_const)).matrix_elem p.1 p.2))
  calc conv k (∑ p, c p • coeff σ p) g = ∑ p, c p * conv k (coeff σ p) g := by
        simp only [conv, coeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [integral_finsetSum _ fun p _ => integrable_cont (hterm p)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← integral_const_mul]
        congr 1
        funext h
        ring
    _ = (eigenval k σ • ∑ p, c p • coeff σ p) g := by
        simp only [conv_coeff hσ hirr hk hkc, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring

end MassGap.PurityConvEigen

#print axioms MassGap.PurityConvEigen.schur
#print axioms MassGap.PurityConvEigen.eq_trace_smul
#print axioms MassGap.PurityConvEigen.mint_comm
#print axioms MassGap.PurityConvEigen.conjAvg_eq
#print axioms MassGap.PurityConvEigen.orthogonality
#print axioms MassGap.PurityConvEigen.orthogonality_unitary
#print axioms MassGap.PurityConvEigen.linearIndependent_coeff
#print axioms MassGap.PurityConvEigen.finrank_span_coeff
#print axioms MassGap.PurityConvEigen.mint_kernel
#print axioms MassGap.PurityConvEigen.conv_coeff
#print axioms MassGap.PurityConvEigen.conv_eigen_multiplicity
