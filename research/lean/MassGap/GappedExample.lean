import MassGap.GappedTheory

/-!
# A concrete gapped quantum theory: the finite-aperture transfer operator diag(1, 3^{-1/4}) on ℂ²

`reconstruct_gapped` builds a gapped quantum theory from any gapped transfer operator. Here the transfer
operator is the CONCRETE `Tc : Fin 2 → ℂ = ![1, 3^{-1/4}]` — the vacuum eigenvalue `1` and, below the gap
`e^{-κ₀} = 3^{-1/4}`, the single excited mode. Its `ℝ`-spectrum `{1, 3^{-1/4}}` is computed from `Pi` units,
so the mass gap `κ₀ = ¼ log 3` is discharged **by computation**: a fully CONSTRUCTED gapped quantum theory,
not a hypothesis. The C\*-positivity order on `Fin 2 → ℂ` is the scoped `ComplexOrder` lifted by
`Pi.instStarOrderedRing`. Foundational axioms only.
-/

namespace MassGap.Reconstruction

open scoped ComplexOrder

/-- `κ₀ = ¼ log 3`, the entropy floor / mass gap. -/
noncomputable def κ0 : ℝ := (1 / 4) * Real.log 3

theorem κ0_pos : 0 < κ0 := by
  have h : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold κ0; positivity

theorem rpow_pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by positivity

/-- `e^{-κ₀} = 3^{-1/4}`. -/
theorem exp_neg_κ0 : Real.exp (-κ0) = (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), κ0]
  congr 1
  ring

/-- The concrete finite-aperture transfer operator on `ℂ²`: vacuum `1`, excited mode `3^{-1/4} = e^{-κ₀}`. -/
noncomputable def Tc : Fin 2 → ℂ := ![1, (((3 : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ)]

theorem Tc_zero : Tc 0 = 1 := by simp [Tc]
theorem Tc_one : Tc 1 = (((3 : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) := by simp [Tc]

theorem Tc_selfAdjoint : IsSelfAdjoint Tc := by
  show star Tc = Tc
  funext i
  fin_cases i <;> simp [Tc, Pi.star_apply, Complex.conj_ofReal]

/-- `1` is in the spectrum of `Tc` — the vacuum eigenvalue. -/
theorem one_mem : (1 : ℝ) ∈ spectrum ℝ Tc := by
  rw [spectrum.mem_iff, map_one]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h0 := hu 0
  rw [Pi.sub_apply, Pi.one_apply, Tc_zero, sub_self] at h0
  exact not_isUnit_zero h0

/-- The `ℝ`-spectrum of `Tc` is contained in `{1, 3^{-1/4}}`. -/
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

/-- **A concrete gapped quantum theory.** The finite-aperture transfer operator `Tc = diag(1, 3^{-1/4})`,
with its computed `ℝ`-spectrum, feeds `reconstruct_gapped` to build a `GappedQuantumTheory` whose mass gap is
`κ₀ = ¼ log 3` — discharged by computation, not assumed. -/
noncomputable def concreteGapped : GappedQuantumTheory (Fin 2 → ℂ) :=
  reconstruct_gapped Tc (ε := (3 : ℝ) ^ (-(1 : ℝ) / 4)) (Δ := κ0)
    Tc_selfAdjoint rpow_pos κ0_pos one_mem (by rw [exp_neg_κ0]; exact spectrum_subset)

/-- The concrete theory's mass gap is `κ₀ = ¼ log 3`. -/
theorem concreteGapped_gap : concreteGapped.gap = κ0 := rfl

-- Footprint of the constructed concrete gapped theory: foundational axioms only (inherits
-- `reconstruct_qm_core`'s footprint; the concrete operator, its spectrum, and the gap add none).
#print axioms concreteGapped

section AbstractAperture

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The finite-aperture margin reconstructs a gapped quantum theory with gap `κ₀`.** Any Euclidean-time
transfer operator `T` whose spectrum meets the finite-aperture margin `spectrum T ⊆ {1} ∪ [ε, 3^{-1/4}]` — the
SU(N) read `m_hi ≤ 3^{-1/4} = e^{-κ₀}`, with the vacuum eigenvalue `1` — reconstructs to a `GappedQuantumTheory`
with mass gap `κ₀ = ¼ log 3`, discharged from the margin. With `concreteGapped` as a witness that the margin is
inhabited, this is the finite-aperture read carried end-to-end to a constructed gapped quantum theory. -/
noncomputable def gapped_of_aperture_margin (T : A) {ε : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε ((3 : ℝ) ^ (-(1 : ℝ) / 4))) :
    GappedQuantumTheory A :=
  reconstruct_gapped T hT hε κ0_pos h1 (by rw [exp_neg_κ0]; exact hsp)

/-- The gap reconstructed from the aperture margin is exactly `κ₀ = ¼ log 3`. -/
theorem gapped_of_aperture_margin_gap (T : A) {ε : ℝ}
    (hT : IsSelfAdjoint T) (hε : 0 < ε) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε ((3 : ℝ) ^ (-(1 : ℝ) / 4))) :
    (gapped_of_aperture_margin T hT hε h1 hsp).gap = κ0 := rfl

-- Footprint of the end-to-end margin-to-theory chain: foundational axioms only.
#print axioms gapped_of_aperture_margin

end AbstractAperture

end MassGap.Reconstruction
