import Mathlib
import MassGap.GaugeGroup
import MassGap.SUN
import MassGap.WilsonAction

/-!
# MassGap.GaugeInstances — `SU(N)`, `SO(n)` and compact `Sp(n)` as `GaugeGroup`s

Each instance is a compact matrix group with the plaquette representation being its defining
matrices, viewed in `U(d)`:

* `SU(N)` (`SUN.SU N`, `N ≠ 0`): the inclusion `SU(N) ⊆ U(N)`. `wilsonDensityG_SU` shows the
  generic density is `WilsonAction.wilsonDensity` by `rfl`, so every `SU(N)` statement about
  `wilsonDensity` is literally a statement about `GaugeGroup.wilsonDensityG (SU N)`.
* `SO(n)` (`Matrix.specialOrthogonalGroup (Fin n) ℝ`, `n ≠ 0`): the topological and measurable
  instances, built as for `SU(N)`, and the representation `M ↦ M.map ofReal` into `U(n)`.
  Its density is `1 − tr M / n` (`wilsonDensityG_SO`).
* compact `Sp(n)` (`USp n`, `n ≠ 0`): the subgroup `{U ∈ U(2n) | U J Uᵀ = J}` with `J` Mathlib's
  `Matrix.J` reindexed to `Fin (n + n)`; `mem_USpSub_iff` identifies it with
  `U(2n) ∩ Sp(2n, ℂ)` for Mathlib's `Matrix.symplecticGroup`. It is compact as a closed subgroup of
  the compact `U(2n)`.

`GaugeSimple` is declared where the Lie algebra is simple: `SU(N)`, `N ≥ 2` (`h^∨ = N`,
`T(fund) = 1/2`, `dim = N² − 1`); `SO(n)`, `n ≥ 5` (`h^∨ = n − 2`, `T(vector) = 1`,
`dim = n(n−1)/2`); `SO(3)` (`so(3) ≅ su(2)`, so `h^∨ = 2`, and the vector is the adjoint of
`su(2)`, `T = 2`); compact `Sp(n)`, `n ≥ 1` (`h^∨ = n + 1`, `T(fund) = 1/2`, `dim = n(2n+1)`).
Not declared: `U(1)` and `SO(2)` (abelian), `SO(4)` (`so(4) ≅ su(2) ⊕ su(2)`), `SU(1)` (trivial).

The centre of `SU(N)` contains the scalars `ω · 1`, `ω^N = 1` (`centreElt_mem_center`), on which the
Wilson density is `1 − Re ω` (`wilsonDensityG_centreElt`).
-/

namespace MassGap.GaugeInstances

open Matrix MeasureTheory MassGap.GaugeGroup

/-! ## `SU(N)` -/

section SU

variable (N : ℕ)

/-- The inclusion `SU(N) → U(N)` as a monoid hom.

DERIVED: no numeral. -/
def suRep : MassGap.SUN.SU N →* Matrix.unitaryGroup (Fin N) ℂ where
  toFun g := ⟨(g : Matrix (Fin N) (Fin N) ℂ), (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable instance instGaugeGroupSU [NeZero N] : GaugeGroup (MassGap.SUN.SU N) where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := N
  repDim_pos := Nat.pos_of_ne_zero (NeZero.ne N)
  rep := suRep N
  continuous_rep := continuous_subtype_val
  rep_injective := fun _ _ h => Subtype.ext (by
    have h' := congrArg
      (fun U : Matrix.unitaryGroup (Fin N) ℂ => (U : Matrix (Fin N) (Fin N) ℂ)) h
    exact h')

/-- The generic Wilson density at `SU(N)` is `WilsonAction.wilsonDensity`, definitionally.

DERIVED: no numeral. -/
theorem wilsonDensityG_SU [NeZero N] :
    wilsonDensityG (MassGap.SUN.SU N) = MassGap.WilsonAction.wilsonDensity (N := N) := rfl

theorem dim_SU [NeZero N] : GaugeGroup.dim (MassGap.SUN.SU N) = N := rfl

/-- `SU(N)`, `N ≥ 2`: `dim 𝔤 = N² − 1`, `h^∨ = N`, `T(fund) = 1/2`.

DERIVED: `2` is the least `N` with `su(N)` simple; `N² − 1`, `N` and `1/2` are the classification
values in the normalisation of `GaugeSimple`. -/
noncomputable instance instGaugeSimpleSU [NeZero N] [Fact (2 ≤ N)] :
    GaugeSimple (MassGap.SUN.SU N) where
  lieDim := N ^ 2 - 1
  dualCoxeter := N
  dynkinIndex := 1 / 2
  dualCoxeter_pos := Nat.pos_of_ne_zero (NeZero.ne N)
  dynkinIndex_pos := by norm_num

variable {N}

/-- The scalar `ω · 1` with `ω^N = 1` is in `SU(N)`.

DERIVED: `1` is the unit norm a root of unity has. -/
theorem centreScalar_mem (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) :
    Matrix.diagonal (fun _ : Fin N => ω) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  have hn : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hN
  have hωω : star ω * ω = 1 := by
    rw [← starRingEnd_apply, RCLike.conj_mul, hn]
    norm_num
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hωω
  · rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hω]

/-- The centre element `ω · 1 ∈ SU(N)`.

DERIVED: no numeral. -/
def centreElt (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) : MassGap.SUN.SU N :=
  ⟨Matrix.diagonal (fun _ => ω), centreScalar_mem hN hω⟩

theorem centreElt_mem_center (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) :
    centreElt hN hω ∈ Subgroup.center (MassGap.SUN.SU N) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  show (g : Matrix (Fin N) (Fin N) ℂ) * Matrix.diagonal (fun _ => ω)
    = Matrix.diagonal (fun _ => ω) * (g : Matrix (Fin N) (Fin N) ℂ)
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

/-- The Wilson density of the centre element `ω · 1` is `1 − Re ω`.

DERIVED: `Re tr (ω · 1) = N Re ω`, divided by `N`. -/
theorem wilsonDensityG_centreElt [NeZero N] {ω : ℂ} (hω : ω ^ N = 1) :
    wilsonDensityG (MassGap.SUN.SU N) (centreElt (NeZero.ne N) hω) = 1 - ω.re := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  show 1 - (1 / (N : ℝ)) * (Matrix.trace (Matrix.diagonal (fun _ : Fin N => ω))).re = 1 - ω.re
  rw [Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  field_simp

end SU

/-! ## `SO(n)` -/

section SO

variable (n : ℕ)

/-- `SO(n)`, Mathlib's `Matrix.specialOrthogonalGroup (Fin n) ℝ`. -/
abbrev SO : Type := Matrix.specialOrthogonalGroup (Fin n) ℝ

instance : Nonempty (SO n) := ⟨1⟩

instance : IsTopologicalGroup (SO n) where
  continuous_mul := continuous_induced_rng.mpr <|
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_conjTranspose

/-- The carrier of `SO(n)` is compact: closed (unitary and `det = 1`) inside the compact
`O(n) = unitaryGroup (Fin n) ℝ`.

DERIVED: the `1` is the determinant condition. -/
theorem isCompact_SO :
    IsCompact (↑(Matrix.specialOrthogonalGroup (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have hset : (↑(Matrix.specialOrthogonalGroup (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ))
      = (↑(Matrix.unitaryGroup (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ)) ∩ {M | M.det = 1} := by
    ext M
    exact Matrix.mem_specialUnitaryGroup_iff
  rw [hset]
  have hclosed : IsClosed ((↑(Matrix.unitaryGroup (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ))
      ∩ {M | M.det = 1}) :=
    isClosed_unitary.inter (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  exact (isCompact_unitaryGroup (Fin n) ℝ).of_isClosed_subset hclosed Set.inter_subset_left

instance : CompactSpace (SO n) := isCompact_iff_compactSpace.mp (isCompact_SO n)

noncomputable instance : MeasurableSpace (SO n) := borel _
instance : BorelSpace (SO n) := ⟨rfl⟩

instance secondCountable_matrix_real : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

instance : SecondCountableTopology (SO n) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

variable {n}

/-- A real orthogonal matrix, read in `ℂ`, is unitary.

DERIVED: no numeral beyond the `1` of the unitarity condition. -/
theorem soRep_mem (g : SO n) :
    (g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hu : star (g : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  rw [Matrix.mem_unitaryGroup_iff']
  have hs : star ((g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom)
      = (star (g : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofRealHom := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    exact (Matrix.conjTranspose_map _ (fun a => by simp)).symm
  rw [hs, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]

variable (n)

/-- The defining representation `SO(n) → U(n)`, `M ↦ M.map ofReal`.

DERIVED: no numeral. -/
noncomputable def soRep : SO n →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun g := ⟨(g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom, soRep_mem g⟩
  map_one' := Subtype.ext (by
    show ((1 : SO n) : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom = 1
    rw [Submonoid.coe_one]
    exact Matrix.map_one _ (map_zero _) (map_one _))
  map_mul' g h := Subtype.ext (by
    show ((g * h : SO n) : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom
      = (g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom
        * (h : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom
    rw [Submonoid.coe_mul, Matrix.map_mul])

noncomputable instance instGaugeGroupSO [NeZero n] : GaugeGroup (SO n) where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := n
  repDim_pos := Nat.pos_of_ne_zero (NeZero.ne n)
  rep := soRep n
  continuous_rep := continuous_subtype_val.matrix_map Complex.continuous_ofReal
  rep_injective := by
    intro g h hgh
    apply Subtype.ext
    ext i j
    have := congrArg (fun U : Matrix.unitaryGroup (Fin n) ℂ => (U : Matrix (Fin n) (Fin n) ℂ) i j) hgh
    exact Complex.ofReal_injective this

/-- The generic Wilson density at `SO(n)`: `1 − tr M / n`, a real trace.

DERIVED: no numeral beyond the density's own `1`. -/
theorem wilsonDensityG_SO [NeZero n] (g : SO n) :
    wilsonDensityG (SO n) g = 1 - (1 / (n : ℝ)) * Matrix.trace (g : Matrix (Fin n) (Fin n) ℝ) := by
  show 1 - (1 / (n : ℝ)) * (Matrix.trace ((g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofRealHom)).re
    = _
  congr 2
  simp [Matrix.trace, Complex.re_sum]

/-- `SO(n)`, `n ≥ 5`: `dim 𝔤 = n(n−1)/2`, `h^∨ = n − 2`, `T(vector) = 1`.

DERIVED: `5` is the least `n` at which `so(n)` is simple and not isomorphic to a lower-rank
algebra with a different normalisation of the vector (`so(3) ≅ su(2)`, `so(4)` not simple);
`n − 2` and `1` are the classification values. -/
noncomputable instance instGaugeSimpleSO [NeZero n] [Fact (5 ≤ n)] : GaugeSimple (SO n) where
  lieDim := n * (n - 1) / 2
  dualCoxeter := n - 2
  dynkinIndex := 1
  dualCoxeter_pos := by have := (Fact.out : 5 ≤ n); omega
  dynkinIndex_pos := one_pos

/-- `SO(3)`: `so(3) ≅ su(2)`, `h^∨ = 2`, and the vector representation is the adjoint of `su(2)`,
`T = 2`; `dim 𝔤 = 3`.

DERIVED: `2`, `2`, `3` are the `su(2)` values carried by the isomorphism. -/
noncomputable instance instGaugeSimpleSO3 : GaugeSimple (SO 3) where
  lieDim := 3
  dualCoxeter := 2
  dynkinIndex := 2
  dualCoxeter_pos := by norm_num
  dynkinIndex_pos := by norm_num

end SO

/-! ## Compact `Sp(n)` -/

section Sp

variable (n : ℕ)

/-- Mathlib's symplectic form `Matrix.J (Fin n) ℂ` reindexed to `Fin (n + n)`.

DERIVED: no numeral. -/
noncomputable def Jsp : Matrix (Fin (n + n)) (Fin (n + n)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.J (Fin n) ℂ)

/-- Compact `Sp(n)`: the unitaries of `U(2n)` preserving `J`, `U J Uᵀ = J`. Closure under inverse
uses unitarity only: `U* J (U*)ᵀ = U* (U J Uᵀ) (U*)ᵀ = (U* U) J (U* U)ᵀ = J`.

DERIVED: no numeral. -/
noncomputable def USpSub : Subgroup (Matrix.unitaryGroup (Fin (n + n)) ℂ) where
  carrier := {U | U.1 * Jsp n * U.1ᵀ = Jsp n}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    show (a.1 * b.1) * Jsp n * (a.1 * b.1)ᵀ = Jsp n
    rw [Matrix.transpose_mul]
    calc a.1 * b.1 * Jsp n * (b.1ᵀ * a.1ᵀ) = a.1 * (b.1 * Jsp n * b.1ᵀ) * a.1ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Jsp n := by rw [hb, ha]
  one_mem' := by
    show (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) * Jsp n
      * (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)ᵀ = Jsp n
    rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    set A : Matrix (Fin (n + n)) (Fin (n + n)) ℂ := a.1 with hAdef
    have hinv : (a⁻¹ : Matrix.unitaryGroup (Fin (n + n)) ℂ).1 = star A := rfl
    have hA1 : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp a.2
    rw [hinv]
    calc star A * Jsp n * (star A)ᵀ = star A * (A * Jsp n * Aᵀ) * (star A)ᵀ := by rw [ha]
      _ = (star A * A) * Jsp n * (Aᵀ * (star A)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = Jsp n := by
        rw [hA1, ← Matrix.transpose_mul, hA1, Matrix.transpose_one, Matrix.one_mul,
          Matrix.mul_one]

/-- Compact `Sp(n)` as a type. -/
abbrev USp : Type := ↥(USpSub n)

/-- Membership in `USpSub n` is membership of the reindexed matrix in Mathlib's
`Matrix.symplecticGroup (Fin n) ℂ`: `USp(n) = U(2n) ∩ Sp(2n, ℂ)`.

DERIVED: no numeral. -/
theorem mem_USpSub_iff (U : Matrix.unitaryGroup (Fin (n + n)) ℂ) :
    U ∈ USpSub n ↔ Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm U.1
      ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  rw [SymplecticGroup.mem_iff]
  change U.1 * Jsp n * U.1ᵀ = Jsp n ↔ _
  have hJ : Matrix.J (Fin n) ℂ = (Jsp n).submatrix finSumFinEquiv finSumFinEquiv := by
    simp [Jsp, Matrix.reindex_apply, Matrix.submatrix_submatrix]
  have key : U.1.submatrix finSumFinEquiv finSumFinEquiv
      * (Jsp n).submatrix finSumFinEquiv finSumFinEquiv
      * (U.1.submatrix finSumFinEquiv finSumFinEquiv)ᵀ
      = (U.1 * Jsp n * U.1ᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [hJ, key]
  constructor
  · intro h; rw [h]
  · intro h
    have h' := congrArg (fun M => M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) h
    simpa [Matrix.submatrix_submatrix] using h'

theorem isClosed_USpSub :
    IsClosed (USpSub n : Set (Matrix.unitaryGroup (Fin (n + n)) ℂ)) :=
  isClosed_eq ((continuous_subtype_val.mul continuous_const).mul
    continuous_subtype_val.matrix_transpose) continuous_const

instance : CompactSpace (USp n) := isCompact_iff_compactSpace.mp (isClosed_USpSub n).isCompact

noncomputable instance : MeasurableSpace (USp n) := borel _
instance : BorelSpace (USp n) := ⟨rfl⟩

instance secondCountable_unitaryGroup (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

instance : SecondCountableTopology (USp n) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

noncomputable instance instGaugeGroupUSp [NeZero n] : GaugeGroup (USp n) where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := n + n
  repDim_pos := by have := NeZero.ne n; omega
  rep := (USpSub n).subtype
  continuous_rep := continuous_subtype_val.comp continuous_subtype_val
  rep_injective := Subgroup.subtype_injective _

/-- Compact `Sp(n)`, `n ≥ 1`: `dim 𝔤 = n(2n+1)`, `h^∨ = n + 1`, `T(fund) = 1/2`.

DERIVED: classification values; `Sp(1) = SU(2)` gives `3`, `2`, `1/2`, agreeing with
`instGaugeSimpleSU` at `N = 2`. -/
noncomputable instance instGaugeSimpleUSp [NeZero n] : GaugeSimple (USp n) where
  lieDim := n * (2 * n + 1)
  dualCoxeter := n + 1
  dynkinIndex := 1 / 2
  dualCoxeter_pos := Nat.succ_pos n
  dynkinIndex_pos := by norm_num

end Sp

#print axioms instGaugeGroupSU
#print axioms wilsonDensityG_SU
#print axioms centreElt_mem_center
#print axioms wilsonDensityG_centreElt
#print axioms isCompact_SO
#print axioms instGaugeGroupSO
#print axioms wilsonDensityG_SO
#print axioms mem_USpSub_iff
#print axioms instGaugeGroupUSp

end MassGap.GaugeInstances
