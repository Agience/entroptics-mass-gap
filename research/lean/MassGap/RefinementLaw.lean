import Mathlib
import MassGap.Aperture
import MassGap.Reconstruction
import MassGap.ApertureRoute

/-!
# MassGap.RefinementLaw — the refinement law as a statement about an OPERATOR

## What Clay row B6 has, and what it does not

Row B6 ("the gap survives the continuum limit") is credited to `MassGap.gap_refinement_invariant`
(`Aperture.lean:141`). That theorem is

    -(s/δ) * log (m ^ (1/s))  =  -(1/δ) * log m         for `0 < δ`, `0 < s`, `0 < m`

and it is true, in two lines, by `Real.log_rpow` and `field_simp`. `hδ` and `hs` enter only as
`field_simp` side conditions. It quantifies over a bare real `m`: no gap, no lattice, no correlator,
no limit. `m` is *called* the dominant eigenvalue in the surrounding prose, but nothing in its
statement ties it to the spectrum of anything, and it is the only declaration in the tree whose
statement is about refinement at all.

The physics the prose attaches to it is that refining the time step by `s` sends the per-step
transfer operator `A_δ` to `A_{δ/s}` with `A_{δ/s}^s = A_δ`, hence sends the dominant eigenvalue
`μ₁` to `μ₁^{1/s}`, so that the physical rate `-(1/δ) log μ₁` is unchanged. That semigroup property
is cited to `[E, §9]` in `Aperture.lean`'s section comment and is formalised nowhere.

## What this file adds

The semigroup property is not a physical postulate for a transfer operator that is genuinely
`exp(-δH)`; it is a fact about the continuous functional calculus, and `Reconstruction.hamiltonian`
(`Reconstruction.lean:83`) already encodes the relation `H = -log T` in exactly that calculus. So the
whole of the refinement law can be proved of the ACTUAL reconstructed dynamics, for a self-adjoint
`T` with positive spectrum in a C⋆-algebra:

* `refined s T = cfc (· ^ (1/s)) T` is the refined transfer operator, and
  `refined_pow` proves **`(refined n T) ^ n = T`** — the semigroup property `A_{δ/s}^s = A_δ` itself,
  at integer refinement, with no citation.
* `spectrum_refined` is the spectral mapping `spectrum (refined s T) = (· ^ (1/s)) '' spectrum T`,
  and `isGreatest_refined` proves the sentence the docstring asserts: **the dominant spectral point
  goes to `|μ₁| ↦ |μ₁|^{1/s}`**.
* `hamiltonian_refined` : **`H(refined s T) = (1/s) • H(T)`**, and hence
  `physical_hamiltonian_refinement_invariant` : `(s/δ) • H(refined s T) = (1/δ) • H(T)`. The
  refinement-invariance of the physical rate is therefore an identity between OPERATORS, not between
  two real numbers.
* `refinement_law_at_spectrum` puts the two together: for `m` in the spectrum of `T`, the point
  `m ^ (1/s)` really is in the spectrum of the refined operator, and there
  `gap_refinement_invariant` applies. That is the arithmetic identity given a domain.
* `reconstructed_gap_refinement_invariant` carries it to the gap: if `spectrum T ⊆ {1} ∪ [ε, e^{-δΔ}]`
  — a vacuum and a lattice gap `δΔ` at step `δ` — then the refined operator satisfies the same with
  `δ/s` in place of `δ`, and `Reconstruction.reconstruct_qm_core` returns a Hamiltonian whose gap is
  `(δ/s)·Δ`. Divided by its own step that is `Δ` at every `s`: the mass gap in physical units does
  not move under refinement.

## The remaining physical input, named exactly

**A transfer operator IS constructed from the Wilson measure**: `OSPositivity.wilsonSlabTransfer` produces a `Transfer.TransferData` on the slab algebra, with `T_symm` (`WilsonTransfer.reflForm_shiftObs_symm`) and `T_vac` PROVED and only two premises carried, `SlabShiftStable` and `SlabShiftContractive`. What follows is about the REFINEMENT law, not about the existence of an operator.
`Transfer.TransferData` (`Transfer.lean:445`) is the structure that would carry one — the `ReflForm`
parent plus a step map `T`, a vacuum, `T_symm`, `T_contract`, `T_vac` and `vac_norm` — and no
declaration produces a term of it. Every occurrence outside `Transfer.lean` CONSUMES one as a
hypothesis: `VolumeRate.rp_sub_geometric` (`VolumeRate.lean:380`) and `rp_gap_of_one_cut` (`:395`)
derive the geometric decay law on the vacuum-orthogonal subspace from a GIVEN `D : TransferData A`.

**Which `ReflForm` to build it on, and why not the other one.** Two are built from the Wilson
measure. `LogConvex.wilsonReflForm` (`LogConvex.lean:321`) has `form := LogConvex.pairing`, and
`pairing` (`LogConvex.lean:171`) is the UNNORMALISED integral `∫ wPlane · F · (G ∘ θ)`; at
`F = G = 1` it is the plane weight's own total mass, which is `1` at `β = 0` because the measure is a
probability measure and which nothing in the tree normalises otherwise. So `vac_norm` — the field
`form 1 1 = 1` — is not a lemma waiting to be proved about that form. `ReflectionStrong`'s
`wilsonGibbsReflForm` (`ReflectionStrong.lean:480`) is the one to use: its `form` is
`Transfer.reflForm`, a Gibbs EXPECTATION of a probability state, so `vac_norm` falls out of
`Transfer.reflForm_one_one` (`Transfer.lean:151`) and is discharged outright at
`ReflectionStrong.wilsonGibbsReflForm_vac_norm` (`:517`). Its `form_nonneg` carries no sign condition
on `β`, routed through `reflForm_eq_pairing` (`:436`), which divides the dressed split pairing by the
partition function.

So `ReflForm`, `vac_norm`, and `vac := ⟨1, ReflectionStrong.one_mem_localObs⟩` (`:143`) are all in
hand; what is missing is `T`, and with it `T_symm`, `T_contract` and `T_vac`. That gap is
STRUCTURAL, not merely unproved. `T` must be an endomorphism of
`LogConvex.localObs (blkS τ a m) (blkR τ a m)`, and reading the block definitions
(`ActionSplit.lean:1083-1095`): `blkR` is the transverse links at level `0` or level `m`, `blkS` the
transverse links strictly between them, and `blkT` everything transverse with `m < lv`. One step
along `τ` carries a transverse link at level `m` to level `m + 1`, which is in `blkT` and in neither
of the other two. The reflection's "half-space" on a periodic lattice is a SLAB of width `m` capped
by the mirror plane, and a transfer operator wants a half-line. A shift operator on the observable module DOES
exist: `WilsonTransfer.shiftObs` is a linear endomorphism of the observables, and
`OSPositivity.shiftSlab` restricts it to `localObs (blkS τ a m) (blkR τ a m)` on the premise
`OSPositivity.SlabShiftStable`. What is a reading of the definitions rather than a Lean theorem is
only that the shift fails to be an endomorphism WITHOUT that premise.

What this file therefore needs, stated as a request rather than built here:

1. an observable module on which the one-step time shift IS an endomorphism — a half-line rather
   than a slab — carrying `ReflForm` the way `wilsonGibbsReflForm` does, and then `T_symm`,
   `T_contract` and `T_vac` on it. That completes a `Transfer.TransferData`, and `Transfer.TqL` is
   then a self-adjoint contraction on the GNS space;
2. a complexification. `Transfer.GNS` is a REAL inner-product space, and Mathlib's `cfc` over `ℝ`
   that `Reconstruction.hamiltonian` uses is stated for a complex C⋆-algebra, so `TqL` has to reach
   a `CStarAlgebra` before Section 1 applies to it.

Both are named rather than assumed, and neither is attempted here. Neither is needed for Section 1,
which is a statement about `Reconstruction.hamiltonian` and the functional calculus alone.

Consequently: what B6 has after this file is the refinement law proved for the reconstructed
dynamics, and the claim that the Wilson ensemble HAS such dynamics still resting on the two
unbuilt objects above. What B6 has in `gap_refinement_invariant` alone is the arithmetic identity
`log (m^{1/s}) = (1/s) log m`, which is true and empty.

## What B6 should cite instead, and whether B5 discharges it

The refinement-uniform statements in `Complete.lean` that do mention the constructed read are
`ym_physical_gap_uniform` (`Complete.lean:992`) and `ym_physical_gap_uniform_exact`
(`Complete.lean:1097`). Their hypotheses are aperture-uniform measured reads, and Section 2 below
settles their relation to the live B5 hypothesis: `ApertureRoute.ConfinesAtAnAperture` does NOT imply
`ym_physical_gap_uniform_exact`'s `hcos`; the implication runs the other way
(`confinesAtAnAperture_of_uniform_cosAvg`), so B6's hypothesis is strictly the stronger of the two
and B6 does not reduce to B5.

All declarations below are `sorry`-free and introduce no axiom; `#print axioms` follows each one.
-/

namespace MassGap.RefinementLaw

open MassGap.Reconstruction

/-! ## 1. The refinement law for the reconstructed dynamics -/

section Operator

variable {A : Type*} [CStarAlgebra A]

/-- **THE REFINED TRANSFER OPERATOR.** Refining the Euclidean time step by a factor `s` replaces the
per-step propagator `A_δ` by `A_{δ/s}`. For a propagator generated by a Hamiltonian, `A_δ = e^{-δH}`,
that is `A_δ^{1/s}` — which is what the continuous functional calculus computes.

DERIVED: the exponent is `1/s` and nothing else; `s` is the caller's refinement factor. -/
noncomputable def refined (s : ℝ) (T : A) : A := cfc (fun x : ℝ => x ^ ((1 : ℝ) / s)) T

#print axioms refined

/-- The refined operator is self-adjoint, so it is again a transfer operator in the sense
`Reconstruction` consumes. -/
theorem isSelfAdjoint_refined (s : ℝ) (T : A) : IsSelfAdjoint (refined s T) :=
  cfc_predicate (fun x : ℝ => x ^ ((1 : ℝ) / s)) T

#print axioms isSelfAdjoint_refined

/-- **THE SPECTRAL MAPPING FOR REFINEMENT.** `spectrum (refined s T) = (· ^ (1/s)) '' spectrum T`.
This is `cfc_map_spectrum`; the only work is the continuity of `x ↦ x^{1/s}`, which holds on all of
`ℝ` because the exponent is nonnegative. -/
theorem spectrum_refined {s : ℝ} (hs : 0 < s) (T : A) (hT : IsSelfAdjoint T) :
    spectrum ℝ (refined s T) = (fun x : ℝ => x ^ ((1 : ℝ) / s)) '' spectrum ℝ T := by
  have hinv : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  exact cfc_map_spectrum (fun x : ℝ => x ^ ((1 : ℝ) / s)) T hT
    (Real.continuous_rpow_const hinv).continuousOn

#print axioms spectrum_refined

/-- **THE SEMIGROUP PROPERTY `A_{δ/s}^s = A_δ`, PROVED.** At integer refinement `s = n ≥ 1`, taking
`n` steps of the refined propagator is one step of the original. This is the relation
`Aperture.lean`'s section comment cites to `[E, §9]` and which nothing in the tree stated; it is a
theorem about the functional calculus, needing only that the spectrum is positive.

DERIVED: no magnitude. `n` is the caller's refinement factor and `hn` is the statement that it
refines at all. -/
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

/-- **REFINEMENT SENDS THE DOMINANT SPECTRAL POINT TO ITS `1/s` POWER.** `|μ₁| ↦ |μ₁|^{1/s}` — the
sentence `Aperture.lean`'s section comment asserts, now about the spectrum of an actual operator.
It holds because `x ↦ x^{1/s}` is monotone on the nonnegatives, so it carries the greatest element of
the spectrum to the greatest element of the image. -/
theorem isGreatest_refined {s : ℝ} (hs : 0 < s) (T : A) (hT : IsSelfAdjoint T)
    (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) {m : ℝ} (hm : IsGreatest (spectrum ℝ T) m) :
    IsGreatest (spectrum ℝ (refined s T)) (m ^ ((1 : ℝ) / s)) := by
  have hinv : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  rw [spectrum_refined hs T hT]
  refine ⟨⟨m, hm.1, rfl⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact Real.rpow_le_rpow (hpos x hx).le (hm.2 hx) hinv

#print axioms isGreatest_refined

/-- **THE HAMILTONIAN OF THE REFINED OPERATOR IS `(1/s)` TIMES THE ORIGINAL.**

    H (T ^ {1/s})  =  (1/s) • H T,       H = -log T

This is the whole content of refinement-invariance, at the level of the operator rather than of a
real number: `-log` intertwines the `1/s` power with scalar multiplication by `1/s`, by `cfc_comp`
and `Real.log_rpow`. Everything else in this section is a corollary. -/
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

/-- **THE PHYSICAL HAMILTONIAN IS REFINEMENT-INVARIANT — as an identity between operators.**

    (s/δ) • H (T ^ {1/s})  =  (1/δ) • H T

Reading the rate at the refined step `δ/s` off the refined operator gives back, on the nose, the rate
read at step `δ` off the original. This is `Aperture.gap_refinement_invariant` with `m` replaced by
the operator it was standing for, and `log` by the functional calculus. -/
theorem physical_hamiltonian_refinement_invariant {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (T : A) (hT : IsSelfAdjoint T) (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) :
    (s / δ) • hamiltonian (refined s T) = (1 / δ) • hamiltonian T := by
  have hs' : s ≠ 0 := ne_of_gt hs
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have hscal : s / δ * (1 / s) = 1 / δ := by field_simp
  rw [hamiltonian_refined hs T hT hpos, smul_smul, hscal]

#print axioms physical_hamiltonian_refinement_invariant

/-- **THE ARITHMETIC IDENTITY, GIVEN A DOMAIN.** For `m` in the spectrum of `T`, the refined point
`m ^ {1/s}` is genuinely in the spectrum of the refined operator, and there
`Aperture.gap_refinement_invariant` says the rate is unchanged.

Stating the two together is the point: the identity in `Aperture.lean` quantifies over an arbitrary
positive real and is therefore compatible with `m` being unrelated to any operator. Here `m` is a
spectral value and `m ^ {1/s}` is the spectral value it becomes. -/
theorem refinement_law_at_spectrum {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (T : A) (hT : IsSelfAdjoint T) (hpos : ∀ x ∈ spectrum ℝ T, 0 < x)
    {m : ℝ} (hm : m ∈ spectrum ℝ T) :
    m ^ ((1 : ℝ) / s) ∈ spectrum ℝ (refined s T) ∧
      -(s / δ) * Real.log (m ^ ((1 : ℝ) / s)) = -(1 / δ) * Real.log m := by
  refine ⟨?_, MassGap.gap_refinement_invariant hδ hs (hpos m hm)⟩
  rw [spectrum_refined hs T hT]
  exact ⟨m, hm, rfl⟩

#print axioms refinement_law_at_spectrum

/-- **THE LATTICE GAP AT STEP `δ` BECOMES THE LATTICE GAP AT STEP `δ/s`.** If the spectrum of the
step-`δ` transfer operator is `{1} ∪ [ε, e^{-δΔ}]` — a vacuum at `1`, everything else below the gap
`Δ` in physical units — then the refined operator has spectrum inside `{1} ∪ [ε^{1/s}, e^{-(δ/s)Δ}]`.
The physical gap `Δ` is the SAME symbol on both sides; only the step has changed.

DERIVED: no magnitude. `δ * Δ` is the gap in units of the step, which is what an exponent of the
propagator has to be, and `ε` is the caller's spectral floor. -/
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

/-- **THE RECONSTRUCTED GAP SURVIVES REFINEMENT.** Feed the refined operator to
`Reconstruction.reconstruct_qm_core`: it returns a self-adjoint `H ≥ 0` with the vacuum energy `0`
attained and no spectrum in `(0, (δ/s)·Δ)`. That gap is `(δ/s)·Δ` in units of the REFINED step, so
in physical units it is `(s/δ)·(δ/s)·Δ = Δ` — the same number at every `s`.

This is what row B6 has to say and `gap_refinement_invariant` does not: refining the lattice does not
erode the gap of the reconstructed Hamiltonian, because the refined dynamics is the same dynamics. -/
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

/-! ## 2. What B6's own refinement-uniform statements assume, against B5

`Complete.ym_physical_gap_uniform_exact` (`Complete.lean:1097`) is the strongest form of B6 that
mentions the constructed read. Its hypothesis is

    hcos : ∀ (i : ℕ) (β : ℝ), γ ≤ cosAvgYMAt (N₀ + i) β,      3^{−1/4} < γ

— one modulus `γ`, holding at EVERY aperture from `N₀` up and at every coupling. The live B5
hypothesis is `ApertureRoute.ConfinesAtAnAperture` (`ApertureRoute.lean:209`),

    ∃ a : EvenAp, ∀ β, 3^{−1/4} < cosAvgEven a β

— ONE aperture, and a strict inequality with no modulus. `hcos` is therefore stronger in two
independent ways at once: it universally quantifies the aperture where B5 existentially quantifies
it, and it supplies a uniform floor where B5 supplies only strictness. The implication runs from
B6's hypothesis to B5's, which is what `confinesAtAnAperture_of_uniform_cosAvg` proves; the converse
is not available, and `one_aperture_does_not_give_a_uniform_floor` shows it is not available from
the quantifier shape either.

So **B6 does not reduce to B5**. The missing modulus is the same one
`ApertureFamily.UniformSurplus` (`ApertureFamily.lean:~425`) names on the tension side, and the
aperture quantifier is a separate gap again, distinct from the `∀β∃a → ∃a∀β` swap that
`ApertureFamily.forall_exists_aperture_does_not_give_exists_forall` already refutes. -/

section Aperture

open MassGap.EvenAperture
open MassGap.ApertureRoute

/-- **THE BRIDGE ON THE COSINE AVERAGE.** `cosAvgEven` is `cosAvgYMAt` at the clamped coupling, by
the same argument `EvenAperture.d2Even_eq` and `EvenAperture.μEven_eq` use: the two reads are the
same `readA` of the same correlation, so the sums are the same sum. Stated separately because it
mentions `readYMAt` and therefore reports the Wilson reflection-positivity axiom. -/
theorem cosAvgEven_eq (a : EvenAp) (β : ℝ) :
    cosAvgEven a β = MassGap.cosAvgYMAt a.1 (max β 0) := by
  show ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d) = _
  rw [readEven_eq_readYMAt_max]
  rfl

#print axioms cosAvgEven_eq

/-- **B6's HYPOTHESIS IMPLIES B5's, AND THAT IS THE DIRECTION THAT HOLDS.**

`ym_physical_gap_uniform_exact`'s `hcos` — a uniform cosine floor `γ > 3^{−1/4}` at every aperture
from `N₀` up — yields `ApertureRoute.ConfinesAtAnAperture`, because some even extent of at least four
lies past `N₀` (`EvenAperture.exists_evenAp_of_eventually`) and the clamped coupling `max β 0` is one
of the couplings `hcos` covers.

The consequence for the Clay table is that B6 is not discharged by B5: citing B6 to
`ym_physical_gap_uniform_exact` leaves `hcos` undischarged, and `hcos` is strictly more than B5's
`ConfinesAtAnAperture`.

DERIVED: no numeral. `3^{−1/4} = e^{−κ₀}` is `ConfinesAtAnAperture`'s own floor and `γ` is the
caller's modulus. -/
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

/-- **NO SCHEMATIC CONVERSE.** Nothing about the quantifier shape recovers a uniform aperture floor
from confinement at one aperture: over `ℕ → ℝ → ℝ` the implication

    (∃ N, ∀ β, c < f N β)  →  (∃ N₀ γ, c < γ ∧ ∀ i β, γ ≤ f (N₀ + i) β)

fails. The witness is the family that is `1` at one aperture and `0` at every other, which meets the
antecedent and refutes the consequent at `i = 1`.

This refutes the SHAPE and not the statement for `cosAvgYMAt`: whether the actual Wilson read happens
to satisfy `hcos` is exactly the measured question `ym_physical_gap_uniform_exact` leaves open, and
no declaration in the tree settles it in either direction.

It is a different failure from `ApertureFamily.forall_exists_aperture_does_not_give_exists_forall`,
which refutes a swap `∀β∃a → ∃a∀β` with the aperture existential on the right. Here the aperture
moves from existential to UNIVERSAL and a modulus is added; neither result implies the other.

DERIVED: no magnitude. `1` and `0` are the two values of an indicator and `1/2` is any point strictly
between them; the argument does not depend on which. -/
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
