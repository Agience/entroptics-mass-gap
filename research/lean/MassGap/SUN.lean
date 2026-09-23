import Mathlib
import MassGap.CompactGauge

/-!
# MassGap.SUN — topological, compactness and Borel instances for `SU(N)`

Mathlib supplies `Matrix.specialUnitaryGroup (Fin n) ℂ` with algebraic structure only. This module
adds the topological and measure-theoretic instances that `MassGap.CompactGauge` requires of a gauge
group, so that `CompactGauge.probHaar` and `CompactGauge.expect_invariant_haar` apply at
`SU n := Matrix.specialUnitaryGroup (Fin n) ℂ`:

* `Nonempty (SU n)` — witnessed by the identity matrix.
* `IsTopologicalGroup (SU n)` — multiplication from the induced topology on the subtype;
  inversion from continuity of the conjugate transpose, since the group inverse is `star`.
* `CompactSpace (SU n)` — via `isCompact_coe`: the carrier is closed in `Matrix (Fin n) (Fin n) ℂ`
  as the intersection of `{M | M * star M = 1}` and `{M | M.det = 1}`, and is contained in a product
  of closed unit balls, which is compact by `isCompact_univ_pi`.
* `MeasurableSpace` and `BorelSpace` — the Borel σ-algebra of the subspace topology, defined as
  `borel _` with `BorelSpace` witnessed by `rfl`.
* `SecondCountableTopology`, `MeasurableInv`, `MeasurableMul₂` — inherited from the product topology
  on `Fin n → Fin n → ℂ` and from continuity.

`su_expect_invariant` is the one theorem: `CompactGauge.expect_invariant_haar` instantiated at
`SU n`.

Scope: `n` is an arbitrary natural number, so `SU 0` and `SU 1` are included; no lower bound on the
rank is imposed anywhere in this module.
-/

namespace MassGap.SUN

open Matrix MeasureTheory

/-- Abbreviation for `Matrix.specialUnitaryGroup (Fin n) ℂ`, the `n × n` complex special unitary
group. Reducible, so instances stated for either name apply to both.

DERIVED: no numeral occurs; `n` is the caller's matrix size. -/
abbrev SU (n : ℕ) : Type := Matrix.specialUnitaryGroup (Fin n) ℂ

variable (n : ℕ)

instance : Nonempty (SU n) := ⟨1⟩

/-! ### Topological group structure -/

instance : IsTopologicalGroup (SU n) where
  continuous_mul := continuous_induced_rng.mpr <|
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_conjTranspose

/-! ### Compactness -/

/-- Every entry of a unitary matrix has norm at most one: for `M ∈ Matrix.unitaryGroup (Fin n) ℂ`
and indices `i j`, `‖M i j‖ ≤ 1`. The proof reads the `(j, j)` entry of `star M * M = 1` as
`∑ k, ‖M k j‖ ^ 2 = 1`, bounds the single term by the sum with `Finset.single_le_sum`, and removes
the square by `nlinarith`.

DERIVED: the `1` is the value of the diagonal entry of the identity matrix, which is what the sum of
squared column norms equals; the bound on a single entry is that same `1` because every other term
of the sum is nonnegative. -/
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

/-- The carrier of `Matrix.specialUnitaryGroup (Fin n) ℂ`, as a subset of
`Matrix (Fin n) (Fin n) ℂ`, is compact. The proof rewrites the carrier as
`{M | M * star M = 1} ∩ {M | M.det = 1}`, shows each factor closed as a preimage of a point under a
continuous map, exhibits the set of matrices with every entry in `Metric.closedBall (0 : ℂ) 1` as an
iterated `Set.univ.pi` and hence compact, and applies `IsCompact.of_isClosed_subset`. The inclusion
uses `unitary_entry_norm_le_one`.

DERIVED: no numeral appears in the statement — it names a set and asserts `IsCompact` of it. -/
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

/-- `Matrix (Fin n) (Fin n) ℂ` is second-countable, by transfer from the product type
`Fin n → Fin n → ℂ`. The instance below it carries this to the subtype `SU n` along the inducing
subtype inclusion.

DERIVED: no numeral occurs; `n` is the caller's matrix size. -/
instance : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

instance : SecondCountableTopology (SU n) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

/-- `MeasurableInv` and `MeasurableMul₂` for `SU n`, each obtained as the measurability of the
corresponding continuous map against the Borel structure declared above.

DERIVED: no numeral occurs; `n` is the caller's matrix size. -/
instance : MeasurableInv (SU n) := ⟨continuous_inv.measurable⟩
instance : MeasurableMul₂ (SU n) := ⟨(continuous_fst.mul continuous_snd).measurable⟩

/-! ### Haar invariance at `SU(N)` -/

/-- Reindexing invariance of the Gibbs expectation at `SU n`. For a lattice gauge system
`sys : LatticeGauge.System (SU n)`, a symmetry `sym` of it, a coupling `β` and an observable
`O : sys.Config → ℝ`, the expectation of `O ∘ Symmetry.reindex sym.onLink` against
`CompactGauge.probHaar (SU n)` equals the expectation of `O`. The proof is
`CompactGauge.expect_invariant_haar` applied at `SU n`; the instances declared above are what make
that application typecheck.

Scope: `n` is arbitrary; `sym` and `sys` are the caller's.

DERIVED: no numeral occurs in the statement. -/
theorem su_expect_invariant {n : ℕ} {sys : MassGap.LatticeGauge.System (SU n)}
    (sym : MassGap.LatticeGauge.Symmetry sys) (β : ℝ) (O : sys.Config → ℝ) :
    sys.expect (MassGap.CompactGauge.probHaar (SU n)) β
        (fun U => O (MassGap.LatticeGauge.Symmetry.reindex sym.onLink U))
      = sys.expect (MassGap.CompactGauge.probHaar (SU n)) β O :=
  MassGap.CompactGauge.expect_invariant_haar (SU n) sym β O

#print axioms isCompact_coe
#print axioms su_expect_invariant

end MassGap.SUN
