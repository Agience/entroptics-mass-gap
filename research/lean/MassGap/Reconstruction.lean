import Mathlib

/-!
# Operator-theoretic ingredients of OS reconstruction: GNS separation and `H = -log T`

Two independent groups of results, both stated over abstract algebraic data.

## GNS separation (`gns_cauchy_schwarz`, `gns_radical_of_self_zero`)

For a symmetric `ℝ`-bilinear form `B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` that is positive semidefinite on the
diagonal, `(B x y)² ≤ (B x x)(B y y)`, and `B v v = 0` implies `B v = 0` as a linear functional. The
second says the null cone and the radical coincide, which is what lets `B` descend to a definite form
on `V / ker B`. Symmetry and diagonal nonnegativity are hypotheses of both theorems; neither is
supplied here, and neither theorem builds the quotient or its completion.

## The Hamiltonian `H = -log T` (`hamiltonian` and the six theorems after it)

`hamiltonian T` is `cfc (fun x => -Real.log x) T` in a C\*-algebra `A`. The theorems fix its
properties under spectral hypotheses on `T`: self-adjointness unconditionally; `0 ≤ H` from
`spectrum T ⊆ [ε, 1]` with `ε > 0`; `spectrum H ⊆ [Δ, ∞)` from `spectrum T ⊆ [ε, e^{-Δ}]`;
`0 ∈ spectrum H` from `1 ∈ spectrum T` together with strict positivity of the spectrum; and
`spectrum H ⊆ {0} ∪ [Δ, ∞)` from `spectrum T ⊆ {1} ∪ [ε, e^{-Δ}]`. `reconstruct_qm_core` conjoins
four of these conclusions under one hypothesis set.

Scope: `T` is an arbitrary element of an abstract `CStarAlgebra A`. Nothing in this file constructs a
transfer operator, a Euclidean measure, a lattice or a Hilbert space, and the spectral containments
are hypotheses in every case. The Minkowski continuation of the Schwinger functions to the Wightman
functions is the classical Osterwalder–Schrader theorem and appears elsewhere in the tree as the
named axiom `WightmanData.os_reconstruction_wightman`; it is not used here.
-/

namespace MassGap.Reconstruction

open scoped NNReal

/-! ## GNS separation: null cone and radical of a positive semidefinite symmetric form -/

section GNS

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Cauchy–Schwarz. For an `ℝ`-bilinear `B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` that is symmetric (`B x y = B y x`
for all `x`, `y`) and nonnegative on the diagonal (`0 ≤ B v v` for all `v`), every pair `x`, `y`
satisfies `(B x y) ^ 2 ≤ B x x * B y y`. The proof expands `B (t • x + y) (t • x + y)` as a quadratic
in `t` that is nonnegative everywhere, so its discriminant is nonpositive.

Scope: `V` is any `ℝ`-module; no topology, completeness or definiteness is assumed, and symmetry and
diagonal nonnegativity are hypotheses rather than instances.

DERIVED: `0` is the lower bound in the diagonal-positivity hypothesis; the exponent `2` is the square
on the left of Cauchy–Schwarz. -/
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

/-- The null cone of a symmetric, diagonally nonnegative `B` is contained in its radical: `B v v = 0`
implies `B v = 0` as a linear map. From `gns_cauchy_schwarz`, `(B v w) ^ 2 ≤ 0 * B w w = 0` for every
`w`, and a square that is `≤ 0` is `0`. The reverse containment is immediate from linearity and is
not stated.

DERIVED: `0` is the lower bound in the diagonal-positivity hypothesis, the value of `B v v` assumed,
and the zero linear map concluded. -/
theorem gns_radical_of_self_zero (hsymm : ∀ x y, B x y = B y x) (hpos : ∀ v, 0 ≤ B v v)
    {v : V} (hv : B v v = 0) : B v = 0 := by
  ext w
  have cs := gns_cauchy_schwarz B hsymm hpos v w
  rw [hv, zero_mul] at cs
  have h0 : (B v w) ^ 2 = 0 := le_antisymm cs (sq_nonneg _)
  simp only [LinearMap.zero_apply]
  exact pow_eq_zero_iff (by norm_num) |>.mp h0

end GNS

/-! ## `hamiltonian T = -log T` by continuous functional calculus, and its spectral properties -/

variable {A : Type*} [CStarAlgebra A]

/-- `-log T` for an element `T` of a C\*-algebra `A`, defined as the continuous functional calculus
`cfc (fun x : ℝ => -Real.log x) T`.

Scope: the definition is total — it accepts any `T : A`. `cfc` returns `0` unless `T` satisfies the
`ℝ`-calculus predicate and `x ↦ -Real.log x` is continuous on `spectrum ℝ T`, which requires `0` to
be outside that spectrum. Callers that need the value to be the actual `-log T` supply a spectral
hypothesis such as `spectrum ℝ T ⊆ Set.Icc ε 1` with `0 < ε`.

DERIVED: no numeral appears in the statement. -/
noncomputable def hamiltonian (T : A) : A := cfc (fun x : ℝ => -Real.log x) T

/-- `hamiltonian T` is self-adjoint, for every `T : A`, with no spectral hypothesis. The `ℝ`-valued
continuous functional calculus lands in the self-adjoint part by `cfc_predicate`, and this holds even
in the degenerate case where `cfc` returns `0`.

DERIVED: no numeral appears in the statement. -/
theorem hamiltonian_isSelfAdjoint (T : A) : IsSelfAdjoint (hamiltonian T) :=
  cfc_predicate (fun x : ℝ => -Real.log x) T

/-- In an ordered C\*-algebra (`PartialOrder A`, `StarOrderedRing A`), if `0 < ε` and
`spectrum ℝ T ⊆ Set.Icc ε 1`, then `0 ≤ hamiltonian T`. Every spectral value lies in `(0, 1]`, where
`Real.log` is nonpositive, so `-Real.log` is nonnegative there and `cfc_nonneg` applies.

Scope: the upper endpoint `1` is what makes the logarithm nonpositive — the statement is about
contractions. `ε` bounds the spectrum away from `0` and is otherwise unconstrained.

DERIVED: `0` is the positivity threshold of `ε` and the lower bound on `hamiltonian T`; `1` is the
upper endpoint of the spectral interval, the contraction bound. -/
theorem hamiltonian_nonneg [PartialOrder A] [StarOrderedRing A] (T : A) {ε : ℝ} (hε : 0 < ε)
    (hsp : spectrum ℝ T ⊆ Set.Icc ε 1) : 0 ≤ hamiltonian T := by
  apply cfc_nonneg
  intro x hx
  obtain ⟨hxε, hx1⟩ := hsp hx
  simpa [hamiltonian] using Real.log_nonpos (le_trans hε.le hxε) hx1

/-- If `T` is self-adjoint, `0 < ε`, and `spectrum ℝ T ⊆ Set.Icc ε (Real.exp (-Δ))`, then
`spectrum ℝ (hamiltonian T) ⊆ Set.Ici Δ`. `cfc_map_spectrum` turns the spectrum of `-log T` into the
image of `spectrum ℝ T`, and `x ≤ e^{-Δ}` gives `log x ≤ -Δ`, hence `-log x ≥ Δ`.

Scope: `Δ` is not assumed positive, and the interval `Set.Icc ε (Real.exp (-Δ))` excludes the value
`1`, so this covers a spectrum with no vacuum eigenvalue. If `ε > e^{-Δ}` the interval is empty and
the hypothesis forces the spectrum to be empty; the conclusion is then vacuous.

DERIVED: `0` is the positivity threshold of `ε`. No other numeral appears; `ε`, `Δ` and the endpoint
`Real.exp (-Δ)` are all bound variables or expressions in them. -/
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

/-- If `T` is self-adjoint, every point of `spectrum ℝ T` is strictly positive, and
`(1 : ℝ) ∈ spectrum ℝ T`, then `(0 : ℝ) ∈ spectrum ℝ (hamiltonian T)`. Strict positivity of the
spectrum makes `-Real.log` continuous there, so `cfc_map_spectrum` applies, and `-log 1 = 0`.

Scope: the hypothesis is `0 < x` pointwise on the spectrum, not a bound away from `0`; it carries no
upper bound, so `T` need not be a contraction for this statement.

DERIVED: `0` is the pointwise lower bound on spectral values and the energy asserted to lie in the
spectrum of `hamiltonian T`; `1` is the spectral value of `T` assumed present, whose image under
`-log` is that `0`. -/
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

/-- If `T` is self-adjoint, `0 < ε`, and `spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))`, then
`spectrum ℝ (hamiltonian T) ⊆ {0} ∪ Set.Ici Δ`. The two pieces map separately: `1 ↦ 0`, and a point
of `[ε, e^{-Δ}]` maps into `[Δ, ∞)` as in `hamiltonian_spectrum_ge_gap`. Splitting on the union also
supplies the strict positivity the functional calculus needs.

Scope: this is a containment of the spectrum of `hamiltonian T`, not a statement that `0` or any
point of `[Δ, ∞)` is attained — `hamiltonian_vacuum_energy` is the separate statement that `0` is
attained. `Δ` is not assumed positive, so for `Δ ≤ 0` the conclusion places no gap.

DERIVED: `0` is the positivity threshold of `ε` and the left piece of the concluded union, the image
of `1` under `-log`; `1` is the singleton in the spectral hypothesis, the vacuum eigenvalue. -/
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

/-- Four conclusions conjoined under one hypothesis set. In an ordered C\*-algebra,
given `T` self-adjoint, `0 < ε`, `0 < Δ`, `(1 : ℝ) ∈ spectrum ℝ T` and
`spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-Δ))`, the element `hamiltonian T` satisfies:
`IsSelfAdjoint`, `0 ≤ hamiltonian T`, `(0 : ℝ) ∈ spectrum ℝ (hamiltonian T)`, and
`spectrum ℝ (hamiltonian T) ⊆ {0} ∪ Set.Ici Δ`.

The first conjunct is `hamiltonian_isSelfAdjoint`, the third `hamiltonian_vacuum_energy`, the fourth
`hamiltonian_mass_gap`; the second is proved inline via `cfc_nonneg`, using `0 < Δ` to get `x ≤ 1` on
the `[ε, e^{-Δ}]` branch.

Scope: `hΔ` is used only for that contraction bound. The spectral containment `hsp` and the vacuum
membership `h1` are hypotheses; `T` is an arbitrary element of an abstract `CStarAlgebra A`, so
nothing here identifies it with a Euclidean-time transfer operator.

DERIVED: `0` is the positivity threshold of `ε`, the positivity threshold of `Δ`, the lower bound in
`0 ≤ hamiltonian T`, the energy asserted to lie in the spectrum, and the singleton in the concluded
union; `1` is the spectral value assumed present in `h1` and the singleton in `hsp`. -/
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
