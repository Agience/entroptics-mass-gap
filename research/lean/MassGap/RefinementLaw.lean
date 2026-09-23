import Mathlib
import MassGap.Aperture
import MassGap.Reconstruction
import MassGap.ApertureRoute

/-!
# MassGap.RefinementLaw — the refinement law for an operator, and two hypotheses compared

## Background

`MassGap.gap_refinement_invariant` (`Aperture.lean:141`) is the identity

    -(s/δ) * log (m ^ (1/s))  =  -(1/δ) * log m         for `0 < δ`, `0 < s`, `0 < m`

proved by `Real.log_rpow` and `field_simp`, with `hδ` and `hs` entering as side conditions on the
division. It quantifies over a bare positive real `m`: no gap, no lattice and no correlator appear in
it, and nothing in its statement ties `m` to the spectrum of an operator.

The reading attached to it is that refining the time step by `s` sends the per-step transfer operator
`A_δ` to `A_{δ/s}` with `A_{δ/s}^s = A_δ`, hence the dominant eigenvalue `μ₁` to `μ₁^{1/s}`, leaving
the rate `-(1/δ) log μ₁` unchanged. That semigroup property is cited to `[E, §9]` in `Aperture.lean`'s
section comment.

## Section 1

For a self-adjoint `T` with positive spectrum in a C⋆-algebra, the refinement law is proved of the
continuous functional calculus, which is where `Reconstruction.hamiltonian` (`Reconstruction.lean:83`)
encodes `H = -log T`:

* `refined s T = cfc (· ^ (1/s)) T`, and `refined_pow` : `(refined n T) ^ n = T` at integer `n ≠ 0`,
  which is the semigroup property `A_{δ/s}^s = A_δ`;
* `spectrum_refined` : `spectrum (refined s T) = (· ^ (1/s)) '' spectrum T`, and `isGreatest_refined`,
  which carries a greatest spectral point `m` to `m ^ (1/s)`;
* `hamiltonian_refined` : `H (refined s T) = (1/s) • H T`, and
  `physical_hamiltonian_refinement_invariant` : `(s/δ) • H (refined s T) = (1/δ) • H T`, an identity
  between operators;
* `refinement_law_at_spectrum`, which states for `m ∈ spectrum T` both that `m ^ (1/s)` lies in the
  spectrum of the refined operator and that `gap_refinement_invariant` holds at `m`;
* `reconstructed_gap_refinement_invariant`: from `spectrum T ⊆ {1} ∪ [ε, e^{-δΔ}]`,
  `Reconstruction.reconstruct_qm_core` returns a Hamiltonian that is self-adjoint and nonnegative,
  attains `0`, and has no spectrum in `(0, (δ/s)·Δ)`. That gap is in units of the refined step `δ/s`,
  so `Δ` is the same symbol at every `s`.

Section 1 is about `Reconstruction.hamiltonian` and the functional calculus. It says nothing about
which operator the Wilson measure supplies, and nothing here builds one. The producers of
`Transfer.TransferData` in the tree are `OSPositivity.wilsonSlabTransfer`, which proves `T_symm`
(`WilsonTransfer.reflForm_shiftObs_symm`) and `T_vac` and carries the two premises `SlabShiftStable`
and `SlabShiftContractive`, and `WilsonState.wilsonTransferData` on the infinite-volume half-space
algebra, which takes three facts about the state as arguments. Two further scope points: `Transfer.GNS`
is a real inner-product space, while the `cfc` over `ℝ` that `Reconstruction.hamiltonian` uses is
stated for a complex C⋆-algebra; and `Transfer.TqL` would have to reach a `CStarAlgebra` before
Section 1 applied to it.

## Section 2

Two hypotheses are compared. `Complete.ym_physical_gap_uniform_exact` (`Complete.lean:1097`) assumes a
uniform cosine floor `γ > 3^{−1/4}` holding at every aperture from `N₀` up and every coupling;
`ApertureRoute.ConfinesAtAnAperture` (`ApertureRoute.lean:209`) assumes a strict inequality at one
aperture, with no modulus. `confinesAtAnAperture_of_uniform_cosAvg` derives the second from the first.
`one_aperture_does_not_give_a_uniform_floor` refutes the converse implication as a schema over
`ℕ → ℝ → ℝ`; it does not settle the question for `cosAvgYMAt` itself.

All declarations below are `sorry`-free and introduce no axiom; `#print axioms` follows each one.
-/

namespace MassGap.RefinementLaw

open MassGap.Reconstruction

/-! ## 1. The refinement law for the reconstructed dynamics -/

section Operator

variable {A : Type*} [CStarAlgebra A]

/-- The refined operator: `cfc (· ^ (1/s)) T`, the `1/s` power of `T` in the continuous functional
calculus. For a propagator `A_δ = e^{-δH}`, refining the step by `s` replaces it by `A_δ^{1/s}`, which
is this. No hypothesis is imposed on `s` or `T` here; the theorems below add them.

DERIVED: the exponent is `1/s` and nothing else; `s` is the caller's refinement factor. -/
noncomputable def refined (s : ℝ) (T : A) : A := cfc (fun x : ℝ => x ^ ((1 : ℝ) / s)) T

#print axioms refined

/-- The refined operator is self-adjoint, at every `s` and every `T`. It is `cfc_predicate`: the
calculus returns an element satisfying the predicate it is taken over.

DERIVED: no numeral. -/
theorem isSelfAdjoint_refined (s : ℝ) (T : A) : IsSelfAdjoint (refined s T) :=
  cfc_predicate (fun x : ℝ => x ^ ((1 : ℝ) / s)) T

#print axioms isSelfAdjoint_refined

/-- For positive `s` and self-adjoint `T`, `spectrum (refined s T) = (· ^ (1/s)) '' spectrum T`. It is
`cfc_map_spectrum`; the side condition is continuity of `x ↦ x^{1/s}`, which holds on all of `ℝ`
because `0 < s` makes the exponent nonnegative.

DERIVED: the `0` is the positivity of `s`, which is what gives the nonnegative exponent; the `1` is
the numerator of the refinement exponent `1/s`. -/
theorem spectrum_refined {s : ℝ} (hs : 0 < s) (T : A) (hT : IsSelfAdjoint T) :
    spectrum ℝ (refined s T) = (fun x : ℝ => x ^ ((1 : ℝ) / s)) '' spectrum ℝ T := by
  have hinv : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  exact cfc_map_spectrum (fun x : ℝ => x ^ ((1 : ℝ) / s)) T hT
    (Real.continuous_rpow_const hinv).continuousOn

#print axioms spectrum_refined

/-- At integer refinement `n ≠ 0`, for self-adjoint `T` with spectrum in the positives,
`(refined n T) ^ n = T`: taking `n` steps of the refined operator returns the original. It is
`cfc_pow` together with `(x^{1/n})^n = x` on the spectrum, which needs `0 < x` there. This is the
semigroup relation `A_{δ/s}^s = A_δ` at integer `s`, cited to `[E, §9]` in `Aperture.lean`.

DERIVED: the `0` in `n ≠ 0` is the refinement factor being a factor at all, and the `0` in `hpos` is
the lower bound on the spectrum that `Real.rpow_mul` needs. `n` is the caller's refinement factor. -/
theorem refined_pow {n : ℕ} (hn : n ≠ 0) (T : A) (hT : IsSelfAdjoint T)
    (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) :
    (refined (n : ℝ) T) ^ n = T := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := ne_of_gt hn0
  have hinv : (0 : ℝ) ≤ 1 / (n : ℝ) := le_of_lt (div_pos one_pos hn0)
  have hf : ContinuousOn (fun x : ℝ => x ^ ((1 : ℝ) / (n : ℝ))) (spectrum ℝ T) :=
    (Real.continuous_rpow_const hinv).continuousOn
  have hpow := cfc_pow (fun x : ℝ => x ^ ((1 : ℝ) / (n : ℝ))) n T hf hT
  have hcg : cfc (fun x : ℝ => (x ^ ((1 : ℝ) / (n : ℝ))) ^ n) T = cfc (fun x : ℝ => x) T := by
    refine cfc_congr ?_
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have hmul : (1 : ℝ) / (n : ℝ) * (n : ℝ) = 1 := by field_simp
    show (x ^ ((1 : ℝ) / (n : ℝ))) ^ n = x
    rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / (n : ℝ))) n, ← Real.rpow_mul hx0.le, hmul,
      Real.rpow_one]
  have hid : cfc (fun x : ℝ => x) T = T := cfc_id' ℝ T hT
  show (cfc (fun x : ℝ => x ^ ((1 : ℝ) / (n : ℝ))) T) ^ n = T
  rw [← hpow]
  exact hcg.trans hid

#print axioms refined_pow

/-- If `m` is the greatest element of `spectrum T`, then `m ^ (1/s)` is the greatest element of
`spectrum (refined s T)`, for positive `s` and self-adjoint `T` with positive spectrum. It combines
`spectrum_refined` with monotonicity of `x ↦ x^{1/s}` on the nonnegatives. The statement is about a
greatest element, which `hm` assumes to exist.

DERIVED: the `0` in `0 < s` gives the nonnegative exponent, the `0` in `hpos` is the lower bound on
the spectrum that `Real.rpow_le_rpow` needs, and the `1` is the numerator of `1/s`. -/
theorem isGreatest_refined {s : ℝ} (hs : 0 < s) (T : A) (hT : IsSelfAdjoint T)
    (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) {m : ℝ} (hm : IsGreatest (spectrum ℝ T) m) :
    IsGreatest (spectrum ℝ (refined s T)) (m ^ ((1 : ℝ) / s)) := by
  have hinv : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  rw [spectrum_refined hs T hT]
  refine ⟨⟨m, hm.1, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact Real.rpow_le_rpow (hpos x hx).le (hm.2 hx) hinv

#print axioms isGreatest_refined

/-- The Hamiltonian of the refined operator is `1/s` times the original:

    H (T ^ {1/s})  =  (1/s) • H T,       H = -log T

for positive `s` and self-adjoint `T` with positive spectrum. `-log` intertwines the `1/s` power with
scalar multiplication by `1/s`, by `cfc_comp` and `Real.log_rpow`; the positivity of the spectrum is
what makes both continuous where they are applied.

DERIVED: the `0` in `0 < s` gives the nonnegative exponent, the `0` in `hpos` keeps the spectrum off
the singularity of `log`, and the `1`s are the numerator of `1/s` in the exponent and in the
scalar. -/
theorem hamiltonian_refined {s : ℝ} (hs : 0 < s) (T : A) (hT : IsSelfAdjoint T)
    (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) :
    hamiltonian (refined s T) = (1 / s) • hamiltonian T := by
  have hinv : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  have hf : ContinuousOn (fun x : ℝ => x ^ ((1 : ℝ) / s)) (spectrum ℝ T) :=
    (Real.continuous_rpow_const hinv).continuousOn
  have hlogT : ContinuousOn (fun x : ℝ => -Real.log x) (spectrum ℝ T) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hpos x hx).ne'
  have hg : ContinuousOn (fun x : ℝ => -Real.log x)
      ((fun x : ℝ => x ^ ((1 : ℝ) / s)) '' spectrum ℝ T) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.mono
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (Real.rpow_pos_of_pos (hpos x hx) _).ne'
  have hcomp := cfc_comp (fun x : ℝ => -Real.log x) (fun x : ℝ => x ^ ((1 : ℝ) / s)) T hT hg hf
  have hconst : cfc (fun x : ℝ => 1 / s * (-Real.log x)) T
      = (1 / s) • cfc (fun x : ℝ => -Real.log x) T :=
    cfc_const_mul (1 / s) (fun x : ℝ => -Real.log x) T hlogT
  show cfc (fun x : ℝ => -Real.log x) (cfc (fun x : ℝ => x ^ ((1 : ℝ) / s)) T)
      = (1 / s) • cfc (fun x : ℝ => -Real.log x) T
  rw [← hcomp, ← hconst]
  refine cfc_congr ?_
  intro x hx
  have hx0 : 0 < x := hpos x hx
  show -Real.log (x ^ ((1 : ℝ) / s)) = 1 / s * (-Real.log x)
  rw [Real.log_rpow hx0]
  ring

#print axioms hamiltonian_refined

/-- Scaling by the refined step gives back the original:

    (s/δ) • H (T ^ {1/s})  =  (1/δ) • H T

for positive `δ` and `s` and self-adjoint `T` with positive spectrum. It is `hamiltonian_refined`
followed by `smul_smul` and `(s/δ)·(1/s) = 1/δ`. The identity is between operators, not between two
real numbers.

DERIVED: the `0`s are the positivity of `δ` and `s`, which the division and `field_simp` need, and the
lower bound on the spectrum that `hamiltonian_refined` carries; the `1` is the numerator of `1/δ`, the
single unrefined step the rate is read per. -/
theorem physical_hamiltonian_refinement_invariant {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (T : A) (hT : IsSelfAdjoint T) (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) :
    (s / δ) • hamiltonian (refined s T) = (1 / δ) • hamiltonian T := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have hscal : s / δ * (1 / s) = 1 / δ := by field_simp
  rw [hamiltonian_refined hs T hT hpos, smul_smul, hscal]

#print axioms physical_hamiltonian_refinement_invariant

/-- For `m` in the spectrum of `T`, two statements together: `m ^ (1/s)` lies in the spectrum of the
refined operator, and `-(s/δ)·log(m^{1/s}) = -(1/δ)·log m`. The first is `spectrum_refined`, the second
is `MassGap.gap_refinement_invariant` at `m`, whose positivity hypothesis comes from `hpos`.

The identity in `Aperture.lean` quantifies over an arbitrary positive real; here the real it is
applied to is a spectral value of `T`.

DERIVED: the `0`s are the positivity of `δ`, of `s` and of the spectrum; the `1`s are the numerators
of the refinement exponent `1/s` and of `1/δ`. -/
theorem refinement_law_at_spectrum {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (T : A) (hT : IsSelfAdjoint T) (hpos : ∀ x ∈ spectrum ℝ T, 0 < x)
    {m : ℝ} (hm : m ∈ spectrum ℝ T) :
    m ^ ((1 : ℝ) / s) ∈ spectrum ℝ (refined s T) ∧
      -(s / δ) * Real.log (m ^ ((1 : ℝ) / s)) = -(1 / δ) * Real.log m := by
  refine ⟨?_, MassGap.gap_refinement_invariant hδ hs (hpos m hm)⟩
  rw [spectrum_refined hs T hT]
  exact ⟨m, hm, rfl⟩

#print axioms refinement_law_at_spectrum

/-- If the spectrum of `T` is inside `{1} ∪ [ε, e^{-δΔ}]` — a point at `1` and everything else between
a floor `ε` and `e^{-δΔ}` — then the spectrum of `refined s T` is inside
`{1} ∪ [ε^{1/s}, e^{-(δ/s)Δ}]`. The point at `1` is fixed because `1^{1/s} = 1`, and the interval is
carried by monotonicity of `x ↦ x^{1/s}`. `Δ` is the same symbol on both sides; the step has changed.
The hypothesis is containment, so the conclusion is containment too.

DERIVED: the `0`s are the positivity of `s`, which gives the nonnegative exponent, and of the floor
`ε`, which `Real.rpow_le_rpow` needs; each `1` is the vacuum point of the spectrum, except the `1` in
`1/s`, which is the numerator of the refinement exponent. `δ * Δ` is the gap in units of the step,
which is what an exponent of the propagator has to be, and `ε` is the caller's floor. -/
theorem spectrum_refined_gap {s δ Δ ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (T : A)
    (hT : IsSelfAdjoint T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-(δ * Δ)))) :
    spectrum ℝ (refined s T)
      ⊆ {1} ∪ Set.Icc (ε ^ ((1 : ℝ) / s)) (Real.exp (-(δ / s * Δ))) := by
  have hinv : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  rw [spectrum_refined hs T hT]
  rintro y ⟨x, hx, rfl⟩
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Icc]
  rcases hsp hx with h | h
  · left
    rw [Set.mem_singleton_iff] at h
    rw [h, Real.one_rpow]
  · right
    obtain ⟨hxε, hxr⟩ := h
    have hval : (Real.exp (-(δ * Δ))) ^ ((1 : ℝ) / s) = Real.exp (-(δ / s * Δ)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    refine ⟨Real.rpow_le_rpow hε.le hxε hinv, ?_⟩
    have hstep : x ^ ((1 : ℝ) / s) ≤ (Real.exp (-(δ * Δ))) ^ ((1 : ℝ) / s) :=
      Real.rpow_le_rpow (le_trans hε.le hxε) hxr hinv
    rwa [hval] at hstep

#print axioms spectrum_refined_gap

/-- Feeding the refined operator to `Reconstruction.reconstruct_qm_core`: given positive `s`, `δ`, `ε`
and `Δ`, a self-adjoint `T` with `1` in its spectrum and spectrum inside `{1} ∪ [ε, e^{-δΔ}]`, the
Hamiltonian of `refined s T` is self-adjoint and nonnegative, attains `0`, and has spectrum inside
`{0} ∪ [(δ/s)·Δ, ∞)`.

The gap `(δ/s)·Δ` is in units of the refined step `δ/s`, so multiplying by the step count per unit
gives `Δ` at every `s`. The hypotheses `spectrum_refined_gap` and `isSelfAdjoint_refined` supply what
`reconstruct_qm_core` consumes.

DERIVED: the `0`s in the hypotheses are the positivity of `s`, `δ`, `ε` and `Δ`; the `1`s are the
vacuum point of the spectrum of `T`; the `0`s in the conclusion are the lower bound on `H`, the
attained vacuum energy, and the isolated point of its spectrum. -/
theorem reconstructed_gap_refinement_invariant [PartialOrder A] [StarOrderedRing A]
    {s δ Δ ε : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hε : 0 < ε) (hΔ : 0 < Δ) (T : A)
    (hT : IsSelfAdjoint T) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (Real.exp (-(δ * Δ)))) :
    IsSelfAdjoint (hamiltonian (refined s T)) ∧ 0 ≤ hamiltonian (refined s T) ∧
      (0 : ℝ) ∈ spectrum ℝ (hamiltonian (refined s T)) ∧
      spectrum ℝ (hamiltonian (refined s T)) ⊆ {0} ∪ Set.Ici (δ / s * Δ) := by
  have h1' : (1 : ℝ) ∈ spectrum ℝ (refined s T) := by
    rw [spectrum_refined hs T hT]
    exact ⟨1, h1, Real.one_rpow _⟩
  exact reconstruct_qm_core (refined s T) (isSelfAdjoint_refined s T)
    (Real.rpow_pos_of_pos hε ((1 : ℝ) / s)) (mul_pos (div_pos hδ hs) hΔ) h1'
    (spectrum_refined_gap hs hε T hT hsp)

#print axioms reconstructed_gap_refinement_invariant

end Operator

/-! ## 2. Two aperture hypotheses, compared

`Complete.ym_physical_gap_uniform_exact` (`Complete.lean:1097`) assumes

    hcos : ∀ (i : ℕ) (β : ℝ), γ ≤ cosAvgYMAt (N₀ + i) β,      3^{−1/4} < γ

— one modulus `γ`, at every aperture from `N₀` up and every coupling.
`ApertureRoute.ConfinesAtAnAperture` (`ApertureRoute.lean:209`) assumes

    ∃ a : EvenAp, ∀ β, 3^{−1/4} < cosAvgEven a β

— one aperture, and a strict inequality with no modulus. The two differ in two ways: the aperture is
universally quantified in the first and existentially in the second, and the first supplies a uniform
floor where the second supplies only strictness.

`confinesAtAnAperture_of_uniform_cosAvg` derives the second from the first.
`one_aperture_does_not_give_a_uniform_floor` refutes the converse as a schema over `ℕ → ℝ → ℝ`, which
leaves the question open for `cosAvgYMAt` itself. The modulus is the one
`ApertureFamily.UniformSurplus` (`ApertureFamily.lean:~425`) names on the tension side, and the
aperture quantifier differs again from the `∀β∃a → ∃a∀β` swap that
`ApertureFamily.forall_exists_aperture_does_not_give_exists_forall` refutes. -/

section Aperture

open MassGap.EvenAperture
open MassGap.ApertureRoute

/-- `cosAvgEven a β = cosAvgYMAt a.1 (max β 0)`: the even-aperture cosine average is the general one at
the clamped coupling. The two reads are the same `readA` of the same correlation
(`readEven_eq_readYMAt_max`), so the sums are equal, as in `EvenAperture.d2Even_eq` and
`EvenAperture.μEven_eq`. It is stated separately because it mentions `readYMAt` and so reports the
Wilson reflection-positivity axiom in its footprint.

DERIVED: the `0` is the clamp `max β 0` that `readEven` applies to the coupling; the `.1` is the
projection of an `EvenAp` onto its extent. -/
theorem cosAvgEven_eq (a : EvenAp) (β : ℝ) :
    cosAvgEven a β = MassGap.cosAvgYMAt a.1 (max β 0) := by
  show ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d) = _
  rw [readEven_eq_readYMAt_max]
  rfl

#print axioms cosAvgEven_eq

/-- A uniform cosine floor `γ > 3^{−1/4}` holding at every aperture from `N₀` up and every coupling
yields `ApertureRoute.ConfinesAtAnAperture`. `EvenAperture.exists_evenAp_of_eventually` supplies an
even extent past `N₀`, and the clamped coupling `max β 0` is among the couplings `hcos` covers, so the
witness aperture is that extent.

The implication is stated in this direction only. `one_aperture_does_not_give_a_uniform_floor` refutes
the converse as a schema.

DERIVED: `3^{−1/4}`, written `(3 : ℝ) ^ (-(1 : ℝ) / 4)`, is `ConfinesAtAnAperture`'s own floor,
carried in unchanged — the `3` its base, the `1` and the `4` its exponent `−1/4`. `γ` is the caller's
modulus. -/
theorem confinesAtAnAperture_of_uniform_cosAvg {γ : ℝ} {N₀ : ℕ}
    (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (hcos : ∀ (i : ℕ) (β : ℝ), γ ≤ MassGap.cosAvgYMAt (N₀ + i) β) :
    ConfinesAtAnAperture := by
  obtain ⟨a, ha⟩ :=
    exists_evenAp_of_eventually (P := fun N => N₀ ≤ N) (Filter.eventually_ge_atTop N₀)
  show ∃ a : EvenAp, ∀ β : ℝ, (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgEven a β
  refine ⟨a, fun β => ?_⟩
  have hle : γ ≤ MassGap.cosAvgYMAt a.1 (max β 0) := by
    have h := hcos (a.1 - N₀) (max β 0)
    rwa [Nat.add_sub_cancel' ha] at h
  rw [cosAvgEven_eq]
  linarith

#print axioms confinesAtAnAperture_of_uniform_cosAvg

/-- The schema

    (∃ N, ∀ β, c < f N β)  →  (∃ N₀ γ, c < γ ∧ ∀ i β, γ ≤ f (N₀ + i) β)

is false over `ℕ → ℝ → ℝ`. The refuting family is the indicator that is one at a single aperture and
zero at every other, with `c = 1/2`: it meets the antecedent and refutes the consequent at `i = 1`.

The statement quantifies over all `f` and `c`, so it refutes the shape, not the corresponding
statement for `cosAvgYMAt`, which no declaration in the tree settles either way. It also differs from
`ApertureFamily.forall_exists_aperture_does_not_give_exists_forall`, which refutes a swap
`∀β∃a → ∃a∀β` with the aperture existential on the right; here the aperture moves from existential to
universal and a modulus is added, and neither result implies the other.

DERIVED: no numeral. -/
theorem one_aperture_does_not_give_a_uniform_floor :
    ¬ (∀ (f : ℕ → ℝ → ℝ) (c : ℝ), (∃ N : ℕ, ∀ β : ℝ, c < f N β) →
        ∃ (N₀ : ℕ) (γ : ℝ), c < γ ∧ ∀ (i : ℕ) (β : ℝ), γ ≤ f (N₀ + i) β) := by
  intro hshape
  obtain ⟨N₀, γ, hγ, hu⟩ :=
    hshape (fun N _ => if N = 0 then (1 : ℝ) else 0) (1 / 2) ⟨0, fun β => by norm_num⟩
  have hne : ¬ (N₀ + 1 = 0) := by omega
  have h1 : γ ≤ 0 := by simpa [hne] using hu 1 0
  linarith

#print axioms one_aperture_does_not_give_a_uniform_floor

end Aperture

/-! ## 3. Footprints -/

section Audit

#print axioms refined
#print axioms isSelfAdjoint_refined
#print axioms spectrum_refined
#print axioms refined_pow
#print axioms isGreatest_refined
#print axioms hamiltonian_refined
#print axioms physical_hamiltonian_refinement_invariant
#print axioms refinement_law_at_spectrum
#print axioms spectrum_refined_gap
#print axioms reconstructed_gap_refinement_invariant
#print axioms cosAvgEven_eq
#print axioms confinesAtAnAperture_of_uniform_cosAvg
#print axioms one_aperture_does_not_give_a_uniform_floor

end Audit

end MassGap.RefinementLaw
