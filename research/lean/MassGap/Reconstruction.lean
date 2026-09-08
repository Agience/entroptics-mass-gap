import Mathlib

/-!
# OS reconstruction, operator-theoretic core: the positive gapped Hamiltonian and GNS separation

Osterwalder–Schrader reconstruction takes reflection-positive Euclidean data to a quantum theory
(Hilbert space, Hamiltonian `H ≥ 0`, vacuum). This module formalises two operator-theoretic segments
of it.

**GNS separation** (`gns_cauchy_schwarz`, `gns_radical_of_self_zero`). The reflection-positive form
is a symmetric, positive-semidefinite `ℝ`-bilinear form `B`. Cauchy–Schwarz `(B x y)² ≤ (B x x)(B y y)`
holds, and its null cone `{v | B v v = 0}` coincides with the radical `{v | B v = 0}` — so `B`
descends to a positive-DEFINITE inner product on `V / ker B`. This is the step of reconstruction that
consumes reflection positivity (OS2) and produces the physical inner product; Mathlib's
`PreInnerProductSpace.Core` / `InnerProductSpace.ofCore` / `SeparationQuotient` package the quotient
and its completion into the GNS Hilbert space.

**The positive gapped Hamiltonian with a vacuum** (`hamiltonian_nonneg`, `hamiltonian_spectrum_ge_gap`,
`hamiltonian_vacuum_energy`, `hamiltonian_mass_gap`, and the packaged `reconstruct_qm_core`). Given the
Euclidean-time transfer operator `T` — a self-adjoint positive contraction — the Hamiltonian `H := -log T`
(continuous functional calculus) is self-adjoint and `H ≥ 0`. With the vacuum eigenvalue `1` in the spectrum
of `T`, the ground-state energy `0` is attained; and when the rest of the spectrum sits below `e^{-Δ}` (the
transfer-matrix gap, `Δ` the mass gap), the spectrum of `H` lies in `{0} ∪ [Δ, ∞)`: a vacuum at `0` and no
spectrum in the open gap `(0, Δ)`. `reconstruct_qm_core` bundles these — self-adjointness, `H ≥ 0`, the vacuum
energy, and the mass gap — a standalone operator-theoretic core, for a given gapped transfer operator.

The Minkowski continuation of the Schwinger functions to the Wightman functions (tube domains /
Bargmann–Hall–Wightman, Poincaré covariance) is the classical Osterwalder–Schrader theorem, cited as the
named axiom `os_reconstruction`.

Foundational axioms only.
-/

namespace MassGap.Reconstruction

open scoped NNReal

/-! ## GNS separation: the reflection-positive form becomes a definite inner product -/

section GNS

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- **Cauchy–Schwarz for the reflection-positive form.** A symmetric, positive-semidefinite `ℝ`-bilinear
form `B` satisfies `(B x y)² ≤ (B x x)(B y y)`. Proof: the quadratic `t ↦ B(t·x+y, t·x+y) ≥ 0` has
nonpositive discriminant. This is the inequality that makes the GNS form an inner product. -/
theorem gns_cauchy_schwarz (hsymm : ∀ x y, B x y = B y x) (hpos : ∀ v, 0 ≤ B v v) (x y : V) :
    (B x y) ^ 2 ≤ B x x * B y y := by
  have key : ∀ t : ℝ, 0 ≤ (B x x) * (t * t) + (2 * B x y) * t + B y y := by
    intro t
    have h := hpos (t • x + y)
    have hexp : B (t • x + y) (t • x + y)
        = (B x x) * (t * t) + (2 * B x y) * t + B y y := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm y x]; ring
    rwa [hexp] at h
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

/-- **The null cone of the reflection-positive form is exactly its radical.** If `B v v = 0` then, by
Cauchy–Schwarz, `B v w = 0` for every `w` — so `v ∈ ker B`. Hence `B` is positive-definite on the
quotient `V / ker B`: the GNS separation step. -/
theorem gns_radical_of_self_zero (hsymm : ∀ x y, B x y = B y x) (hpos : ∀ v, 0 ≤ B v v)
    {v : V} (hv : B v v = 0) : B v = 0 := by
  ext w
  have cs := gns_cauchy_schwarz B hsymm hpos v w
  rw [hv, zero_mul] at cs
  have h0 : (B v w) ^ 2 = 0 := le_antisymm cs (sq_nonneg _)
  simp only [LinearMap.zero_apply]
  exact pow_eq_zero_iff (by norm_num) |>.mp h0

end GNS

/-! ## The reconstructed Hamiltonian `H = -log T` -/

variable {A : Type*} [CStarAlgebra A]

/-- **The reconstructed Hamiltonian** of a Euclidean-time transfer operator `T`: `H := -log T`
(continuous functional calculus). For a gapped transfer operator (spectrum in `[ε,1]`, `ε>0`) the map
`x ↦ -log x` is continuous on the spectrum, so this is the genuine `-log T`, not a junk value. -/
noncomputable def hamiltonian (T : A) : A := cfc (fun x : ℝ => -Real.log x) T

/-- **The reconstructed Hamiltonian is self-adjoint** (the real functional calculus of any element lands in
the self-adjoint part). -/
theorem hamiltonian_isSelfAdjoint (T : A) : IsSelfAdjoint (hamiltonian T) :=
  cfc_predicate (fun x : ℝ => -Real.log x) T

/-- **The reconstructed Hamiltonian is nonnegative — `H ≥ 0`.** For a gapped positive-contraction transfer
operator (`spectrum T ⊆ [ε,1]`, `ε>0`), `H = -log T ≥ 0` because `-log x ≥ 0` for `x ∈ (0,1]`. This is the
positivity of the Hamiltonian in OS reconstruction (foundational axioms only). -/
theorem hamiltonian_nonneg [PartialOrder A] [StarOrderedRing A] (T : A) {ε : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ Set.Icc ε 1) : 0 ≤ hamiltonian T := by
  apply cfc_nonneg
  intro x hx
  obtain ⟨hxε, hx1⟩ := hsp hx
  simpa [hamiltonian] using Real.log_nonpos (le_trans hε.le hxε) hx1

/-- **The reconstructed Hamiltonian has a mass gap `Δ`.** If the transfer operator `T` is self-adjoint with
spectrum in `[ε, e^{-Δ}]` (`ε>0`) — the vacuum removed, everything below the gap `e^{-Δ}` — then the
spectrum of `H = -log T` lies in `[Δ, ∞)`. This is the transfer-matrix gap becoming the mass gap of the
reconstructed Hamiltonian, `Δ = κ₀ - μ` in the entropic reading (foundational axioms only). -/
theorem hamiltonian_spectrum_ge_gap (T : A) {ε Δ : ℝ} (hT : IsSelfAdjoint T) (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ Set.Icc ε (Real.exp (-Δ))) :
    spectrum ℝ (hamiltonian T) ⊆ Set.Ici Δ := by
  have hcont : ContinuousOn (fun x : ℝ => -Real.log x) (spectrum ℝ T) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.mono
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hε (hsp hx).1
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hx0.ne'
  unfold hamiltonian
  rw [cfc_map_spectrum (fun x : ℝ => -Real.log x) T]
  rintro μ ⟨x, hx, rfl⟩
  obtain ⟨hxε, hxr⟩ := hsp hx
  have hx0 : 0 < x := lt_of_lt_of_le hε hxε
  have hlog : Real.log x ≤ -Δ := by
    have := Real.log_le_log hx0 hxr
    rwa [Real.log_exp] at this
  simp only [Set.mem_Ici]
  linarith

/-- **The reconstructed vacuum energy is `0`.** If the transfer operator `T` has `1` in its spectrum (the
top eigenvalue of a positive contraction — the vacuum) and its spectrum is positive, then `0` lies in the
spectrum of `H = -log T`: the ground-state energy is attained at the vacuum. -/
theorem hamiltonian_vacuum_energy (T : A) (hT : IsSelfAdjoint T)
    (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) (h1 : (1 : ℝ) ∈ spectrum ℝ T) :
    (0 : ℝ) ∈ spectrum ℝ (hamiltonian T) := by
  have hcont : ContinuousOn (fun x : ℝ => -Real.log x) (spectrum ℝ T) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hpos x hx).ne'
  unfold hamiltonian
  rw [cfc_map_spectrum (fun x : ℝ => -Real.log x) T]
  exact ⟨1, h1, by simp [Real.log_one]⟩

/-- **The reconstructed Hamiltonian has a mass gap `Δ` above the vacuum.** If the transfer operator `T` is
self-adjoint with spectrum in `{1} ∪ [ε, e^{-Δ}]` (`ε>0`) — the vacuum eigenvalue `1` and, below the gap
`e^{-Δ}`, the excited spectrum — then the spectrum of `H = -log T` lies in `{0} ∪ [Δ, ∞)`: ground-state
energy `0`, and no spectrum in the open gap `(0, Δ)`. This is the mass gap of the reconstructed Hamiltonian,
`Δ = κ₀ - μ` in the entropic reading. -/
theorem hamiltonian_mass_gap (T : A) {ε Δ : ℝ} (hT : IsSelfAdjoint T) (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    spectrum ℝ (hamiltonian T) ⊆ {0} ∪ Set.Ici Δ := by
  have hpos : ∀ x ∈ spectrum ℝ T, 0 < x := by
    intro x hx
    rcases hsp hx with h | h
    · rw [Set.mem_singleton_iff] at h; rw [h]; norm_num
    · exact lt_of_lt_of_le hε h.1
  have hcont : ContinuousOn (fun x : ℝ => -Real.log x) (spectrum ℝ T) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hpos x hx).ne'
  unfold hamiltonian
  rw [cfc_map_spectrum (fun x : ℝ => -Real.log x) T]
  rintro μ ⟨x, hx, rfl⟩
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici]
  rcases hsp hx with h | h
  · left; rw [Set.mem_singleton_iff] at h; rw [h]; simp [Real.log_one]
  · right
    obtain ⟨hxε, hxr⟩ := h
    have hx0 : 0 < x := lt_of_lt_of_le hε hxε
    have hlog : Real.log x ≤ -Δ := by
      have := Real.log_le_log hx0 hxr
      rwa [Real.log_exp] at this
    linarith

/-- **The reconstructed quantum-mechanical core.** From a gapped Euclidean-time transfer operator `T`
(self-adjoint, spectrum `{1} ∪ [ε, e^{-Δ}]`, `ε>0`, `Δ>0`), the Hamiltonian `H = -log T` is (i) self-adjoint,
(ii) nonnegative `H ≥ 0`, (iii) has its ground-state energy `0` attained — the vacuum, and (iv) has a mass gap
`Δ`: no spectrum in `(0, Δ)`. This is the operator-theoretic output of OS reconstruction — a Hilbert-space
Hamiltonian with a vacuum and a positive mass gap — assembled from the CFC lemmas above, foundational axioms
only. The Minkowski continuation to the Wightman functions is the classical Osterwalder–Schrader theorem
(`os_reconstruction`). -/
theorem reconstruct_qm_core [PartialOrder A] [StarOrderedRing A] (T : A) {ε Δ : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (hΔ : 0 < Δ) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))) :
    IsSelfAdjoint (hamiltonian T) ∧ 0 ≤ hamiltonian T ∧
      (0 : ℝ) ∈ spectrum ℝ (hamiltonian T) ∧
      spectrum ℝ (hamiltonian T) ⊆ {0} ∪ Set.Ici Δ := by
  have hpos : ∀ x ∈ spectrum ℝ T, 0 < x := by
    intro x hx
    rcases hsp hx with h | h
    · rw [Set.mem_singleton_iff] at h; rw [h]; norm_num
    · exact lt_of_lt_of_le hε h.1
  refine ⟨hamiltonian_isSelfAdjoint T, ?_, hamiltonian_vacuum_energy T hT hpos h1,
    hamiltonian_mass_gap T hT hε hsp⟩
  apply cfc_nonneg
  intro x hx
  have hx0 : 0 < x := hpos x hx
  have hx1 : x ≤ 1 := by
    rcases hsp hx with h | h
    · rw [Set.mem_singleton_iff] at h; exact h.le
    · refine le_trans h.2 ?_
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  simpa using Real.log_nonpos hx0.le hx1

end MassGap.Reconstruction
