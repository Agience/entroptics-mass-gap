import MassGap.GappedTheory

/-!
# A worked instance of `reconstruct_gapped`: the diagonal element `![1, 3^{-1/4}]` of `ℂ²`

`reconstruct_gapped` (in `MassGap.GappedTheory`) turns a self-adjoint element whose `ℝ`-spectrum sits
in `{1} ∪ [ε, e^{-Δ}]` into a `GappedQuantumTheory` of gap `Δ`. This file supplies one concrete
argument for it and one abstract specialisation.

The concrete argument is `Tc : Fin 2 → ℂ = ![1, 3^{-1/4}]`. Its spectral obligations are discharged
against the `Pi` unit criterion (`Pi.isUnit_iff`): `one_mem` gives `1 ∈ spectrum ℝ Tc`, and
`spectrum_subset` gives `spectrum ℝ Tc ⊆ {1} ∪ Icc (3^{-1/4}) (3^{-1/4})`. Membership of `3^{-1/4}`
in the spectrum is not proved and is not needed: `reconstruct_gapped` consumes the inclusion and the
vacuum eigenvalue only.

The abstract specialisation `gapped_of_aperture_margin` fixes the gap at `κ₀` and the interval's right
endpoint at `3^{-1/4}`, leaving the C\*-algebra `A`, the element `T` and the left endpoint `ε` free.

The order on `Fin 2 → ℂ` is the scoped `ComplexOrder` lifted pointwise by `Pi.instStarOrderedRing`;
`open scoped ComplexOrder` is what puts that instance in scope.
-/

namespace MassGap.Reconstruction

open scoped ComplexOrder

/-- `κ₀ = ¼ · log 3`, the gap value used throughout this file.

DERIVED: `3` is the base whose negative fourth power is the excited entry of `Tc`; `1 / 4` is that
power's exponent, chosen so `exp (-κ₀) = 3^{-1/4}` (`exp_neg_κ0`). -/
noncomputable def κ0 : ℝ := (1 / 4) * Real.log 3

theorem κ0_pos : 0 < κ0 := by
  have h : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold κ0; positivity

theorem rpow_pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by positivity

/-- `Real.exp (-κ₀) = (3 : ℝ) ^ (-1/4 : ℝ)`, by `Real.rpow_def_of_pos` and `ring` on the exponent.
This identity lets a spectral bound written as a power of `3` be passed where `reconstruct_gapped`
expects `exp (-Δ)`.

DERIVED: `3`, `1` and `4` are `κ0`'s own `(1 / 4) * Real.log 3`, re-expressed as an `rpow`. -/
theorem exp_neg_κ0 : Real.exp (-κ0) = (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), κ0]
  congr 1
  ring

/-- The element `![1, 3^{-1/4}]` of `Fin 2 → ℂ`, the second entry being the real `3^{-1/4}` coerced
into `ℂ`. It is the test argument for `reconstruct_gapped` below.

DERIVED: `2` is the number of entries, one vacuum and one excited; `1` is the vacuum entry; `3`, `1`
and `4` are the excited entry `3^{-1/4} = exp (-κ0)`. -/
noncomputable def Tc : Fin 2 → ℂ := ![1, (((3 : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)]

theorem Tc_zero : Tc 0 = 1 := by simp [Tc]
theorem Tc_one : Tc 1 = (((3 : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) := by simp [Tc]

theorem Tc_selfAdjoint : IsSelfAdjoint Tc := by
  show star Tc = Tc
  funext i
  fin_cases i <;> simp [Tc, Pi.star_apply, Complex.conj_ofReal]

/-- `(1 : ℝ) ∈ spectrum ℝ Tc`. Via `Pi.isUnit_iff`: `Tc - 1` vanishes in coordinate `0`, and zero is
not a unit, so `algebraMap 1 - Tc` is not a unit.

DERIVED: `1` is `Tc 0`, so `1` is the spectral value that coordinate contributes. -/
theorem one_mem : (1 : ℝ) ∈ spectrum ℝ Tc := by
  rw [spectrum.mem_iff, map_one]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h0 := hu 0
  rw [Pi.sub_apply, Pi.one_apply, Tc_zero, sub_self] at h0
  exact not_isUnit_zero h0

/-- `spectrum ℝ Tc ⊆ {1} ∪ Set.Icc (3^{-1/4}) (3^{-1/4})`. The interval is degenerate, so the
right-hand side is the two-point set `{1, 3^{-1/4}}`; it is written as an `Icc` to match the shape
`reconstruct_gapped` expects. Proved contrapositively through `Pi.isUnit_iff` and
`Fin.forall_fin_two`: if `r` is neither entry, both coordinates of `algebraMap r - Tc` are nonzero
and hence units. Only the inclusion is established; equality with `{1, 3^{-1/4}}` is not.

DERIVED: `1` is `Tc 0`; `3`, `1` and `4` are `Tc 1 = 3^{-1/4}`, appearing as both endpoints of the
degenerate interval. -/
theorem spectrum_subset :
    spectrum ℝ Tc ⊆ {1} ∪ Set.Icc ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ((3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
  intro r hr
  rw [spectrum.mem_iff] at hr
  have key : r = 1 ∨ r = (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨hr1, hr2⟩ := hc
    apply hr
    rw [Pi.isUnit_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero, sub_ne_zero,
        Tc_zero]
      exact fun h => hr1 (by exact_mod_cast h)
    · rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero, sub_ne_zero,
        Tc_one]
      exact fun h => hr2 (by exact_mod_cast h)
  rw [Set.mem_union, Set.mem_singleton_iff]
  rcases key with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_Icc.mpr ⟨le_of_eq h.symm, le_of_eq h⟩)

/-- `reconstruct_gapped` applied to `Tc`, with `ε := 3^{-1/4}` and `Δ := κ₀`. Its five obligations are
supplied by `Tc_selfAdjoint`, `rpow_pos`, `κ0_pos`, `one_mem`, and `spectrum_subset` rewritten through
`exp_neg_κ0`. The result is a `GappedQuantumTheory (Fin 2 → ℂ)` carrying no remaining hypothesis.

DERIVED: `2` is `Tc`'s index type `Fin 2`. -/
noncomputable def concreteGapped : GappedQuantumTheory (Fin 2 → ℂ) :=
  reconstruct_gapped Tc (ε := (3 : ℝ) ^ (-(1 : ℝ) / 4)) (Δ := κ0)
    Tc_selfAdjoint rpow_pos κ0_pos one_mem (by rw [exp_neg_κ0]; exact spectrum_subset)

/-- `concreteGapped.gap = κ0`, by `rfl`: `reconstruct_gapped` stores its `Δ` argument in the `gap`
field unchanged.

DERIVED: no numeral. -/
theorem concreteGapped_gap : concreteGapped.gap = κ0 := rfl

-- Reports the axiom footprint of the constructed theory.
#print axioms concreteGapped

section AbstractAperture

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `reconstruct_gapped` with `Δ` fixed at `κ₀` and the spectral interval's right endpoint fixed at
`3^{-1/4}`. Given a self-adjoint `T` in a C\*-algebra `A` with `StarOrderedRing A`, a positive `ε`,
the eigenvalue `1 ∈ spectrum ℝ T`, and `spectrum ℝ T ⊆ {1} ∪ Set.Icc ε (3^{-1/4})`, it produces a
`GappedQuantumTheory A`. `ε` remains free, so the hypothesis is inclusion in a band with an arbitrary
positive floor and the fixed ceiling `3^{-1/4}`. `concreteGapped` witnesses that the hypotheses are
satisfiable.

DERIVED: `0` is the positivity demanded of `ε`; `1` is the eigenvalue asked for in `h1` and the
singleton in `hsp`; `3`, `1` and `4` are the fixed ceiling `3^{-1/4} = exp (-κ0)`, which is what pins
the reconstructed gap to `κ0`. -/
noncomputable def gapped_of_aperture_margin (T : A) {ε : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε ((3 : ℝ) ^ (-(1 : ℝ) / 4))) :
    GappedQuantumTheory A :=
  reconstruct_gapped T hT hε κ0_pos h1 (by rw [exp_neg_κ0]; exact hsp)

/-- The theory built by `gapped_of_aperture_margin` has `gap = κ0`, by `rfl`, for every `A`, `T`, `ε`
and choice of proofs.

DERIVED: `0` is `hε`'s positivity bound; `1` is the eigenvalue in `h1` and the singleton in `hsp`;
`3`, `1` and `4` are the fixed ceiling `3^{-1/4}`. The conclusion itself carries no numeral. -/
theorem gapped_of_aperture_margin_gap (T : A) {ε : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε ((3 : ℝ) ^ (-(1 : ℝ) / 4))) :
    (gapped_of_aperture_margin T hT hε h1 hsp).gap = κ0 := rfl

-- Reports the axiom footprint of the abstract margin-to-theory construction.
#print axioms gapped_of_aperture_margin

end AbstractAperture

end MassGap.Reconstruction
