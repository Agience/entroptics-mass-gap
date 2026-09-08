import Mathlib
import MassGap.CompactGauge

/-!
# MassGap.SUN — the compact topological-group instances for `SU(N)` (step A2b)

Discharges the topological hypotheses that `CompactGauge` (step A2a) leaves open for the concrete
gauge group `Matrix.specialUnitaryGroup (Fin n) ℂ`. Mathlib v4.31 gives `specialUnitaryGroup` only
its *algebraic* structure (`Group`); here we supply the missing topological instances so that the
canonical probability Haar measure `CompactGauge.probHaar` exists on `SU(N)`, and hence the derived
correlation invariance `CompactGauge.expect_invariant_haar` lands on the actual gauge group:

* `Nonempty` — the identity is special-unitary;
* `IsTopologicalGroup` — `ContinuousMul` is free (`Submonoid.continuousMul`), `ContinuousInv` is the
  continuity of the conjugate transpose (group inverse `= star = ᴴ`);
* `CompactSpace` — `SU(N)` is closed in `Matrix` (`M * Mᴴ = 1 ∧ det = 1` are closed conditions) and
  contained in the product of unit balls (each unitary entry has `‖M i j‖ ≤ 1`), hence compact by
  Tychonoff + Heine–Borel-free closed-subset-of-compact;
* `MeasurableSpace`/`BorelSpace` — the Borel σ-algebra of the subspace topology (no competing
  instance on `Matrix`, so no diamond).

With these, `A1`'s Haar-derived Osterwalder–Schrader invariances hold on a genuine `SU(N)` measure.
Foundational footprint only. Build: `lake build MassGap.SUN`.
-/

namespace MassGap.SUN

open Matrix MeasureTheory

/-- Shorthand for `SU(N)` over `ℂ`. -/
abbrev SU (n : ℕ) : Type := Matrix.specialUnitaryGroup (Fin n) ℂ

variable (n : ℕ)

instance : Nonempty (SU n) := ⟨1⟩

/-! ### Topological group structure -/

instance : IsTopologicalGroup (SU n) where
  continuous_mul := continuous_induced_rng.mpr <|
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_conjTranspose

/-! ### Compactness -/

/-- Every entry of a unitary matrix has norm `≤ 1`: from `star M * M = 1`, the `j`-th diagonal gives
`∑ₖ ‖M k j‖² = 1`, so each `‖M i j‖² ≤ 1`. -/
theorem unitary_entry_norm_le_one {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) : ‖M i j‖ ≤ 1 := by
  have hMM : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  have h1 : ∑ k, (star M) j k * M k j = (1 : ℂ) := by
    have h0 : (star M * M) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by rw [hMM]
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h0
  have hsum : ((∑ k, ‖M k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, ← h1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ← starRingEnd_apply,
      RCLike.conj_mul]
    norm_cast
  have hdiag : ∑ k, ‖M k j‖ ^ 2 = 1 := by exact_mod_cast hsum
  have hle : ‖M i j‖ ^ 2 ≤ 1 := by
    rw [← hdiag]
    exact Finset.single_le_sum (f := fun k => ‖M k j‖ ^ 2)
      (fun k _ => sq_nonneg (‖M k j‖)) (Finset.mem_univ i)
  nlinarith [hle, norm_nonneg (M i j), sq_nonneg (‖M i j‖ - 1)]

/-- The carrier of `SU(N)` is compact in `Matrix`: closed (unitary + `det = 1`) and inside the
compact product of unit balls. -/
theorem isCompact_coe :
    IsCompact (↑(Matrix.specialUnitaryGroup (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  -- closed: intersection of `{M | M * Mᴴ = 1}` and `{M | det M = 1}`
  have hset : (↑(Matrix.specialUnitaryGroup (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ))
      = {M | M * star M = 1} ∩ {M | M.det = 1} := by
    ext M
    constructor
    · intro hM
      rw [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff] at hM
      exact ⟨Matrix.mem_unitaryGroup_iff.mp hM.1, hM.2⟩
    · rintro ⟨h1, h2⟩
      rw [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff]
      exact ⟨Matrix.mem_unitaryGroup_iff.mpr h1, h2⟩
  have hclosed : IsClosed (↑(Matrix.specialUnitaryGroup (Fin n) ℂ) :
      Set (Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hset]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ continuous_const)
    · exact continuous_id.mul continuous_id.matrix_conjTranspose
    · exact Continuous.matrix_det continuous_id
  -- compact superset: product of closed unit balls
  have hKcompact : IsCompact
      {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1} := by
    have hpi : {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1}
        = Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n =>
          Metric.closedBall (0 : ℂ) 1)) := by
      ext M
      constructor
      · intro h i _ j _; exact h i j
      · intro h i j; exact h i (Set.mem_univ i) j (Set.mem_univ j)
    rw [hpi]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hsubset : (↑(Matrix.specialUnitaryGroup (Fin n) ℂ) :
      Set (Matrix (Fin n) (Fin n) ℂ))
      ⊆ {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1} := by
    intro M hM
    rw [SetLike.mem_coe] at hM
    have hu : M ∈ Matrix.unitaryGroup (Fin n) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp hM).1
    intro i j
    rw [Metric.mem_closedBall, dist_zero_right]
    exact unitary_entry_norm_le_one n hu i j
  exact hKcompact.of_isClosed_subset hclosed hsubset

instance : CompactSpace (SU n) :=
  isCompact_iff_compactSpace.mp (isCompact_coe n)

/-! ### Borel measurable structure -/

noncomputable instance : MeasurableSpace (SU n) := borel _
instance : BorelSpace (SU n) := ⟨rfl⟩

/-- `Matrix` (a finite product of `ℂ`) is second-countable — so `SU(N) ⊂ Matrix` is too
(`Subtype.secondCountableTopology`). -/
instance : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

instance : SecondCountableTopology (SU n) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

/-- `SU(N)` has measurable multiplication and inversion (continuity + Borel structure) — needed for the
measurability of the Wilson holonomy. -/
instance : MeasurableInv (SU n) := ⟨continuous_inv.measurable⟩
instance : MeasurableMul₂ (SU n) := ⟨(continuous_fst.mul continuous_snd).measurable⟩

/-! ### The Haar-derived invariance lands on `SU(N)` -/

/-- **The Osterwalder–Schrader invariance, derived on the actual `SU(N)` gauge measure.** With all
topological instances now in place, `CompactGauge.probHaar (SU(N))` is the canonical probability Haar
measure, and A1's derived invariance `⟨O ∘ reindex⟩ = ⟨O⟩` holds for the Gibbs expectation of any
`SU(N)` lattice gauge system against it. This is step A's invariance face, discharged on the physical
gauge group rather than an inert label. -/
theorem su_expect_invariant {n : ℕ} {sys : MassGap.LatticeGauge.System (SU n)}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar (SU n)) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar (SU n)) β O :=
  MassGap.CompactGauge.expect_invariant_haar (SU n) sym β O

#print axioms isCompact_coe
#print axioms su_expect_invariant

end MassGap.SUN
