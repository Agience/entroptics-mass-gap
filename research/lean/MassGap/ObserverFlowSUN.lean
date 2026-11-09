import Mathlib
import MassGap.ObserverFlow
import MassGap.FlowCapstone
import MassGap.CompositeLink

/-!
# MassGap.ObserverFlowSUN — a block step for `SU(N)` and its observer flow

The observer reads the gauge field through one block step per link: the link `W` and its six staples
`Sᵢ`, summed as `X = W + c Σ Sᵢ`, returned to the group. For `SU(2)` such a sum is a real multiple of a
group element (`BlockSU2`); for general `N` this module returns it to `SU(N)` in two moves.

* **Unitary polar part** (`polar X = X (√(XᴴX))⁻¹`, the square root by `CFC.sqrt`). For `det X ≠ 0` it is
  unitary with `(polar X)ᴴ X` positive semidefinite (`polar_spec`), and it is the only unitary with that
  property (`polar_unique`). From uniqueness: `polar (g X hᴴ) = g (polar X) hᴴ` for unitary `g, h`
  (`polar_mul_mul`) and `polar Xᴴ = (polar X)ᴴ` (`polar_conjTranspose`); from uniqueness and the
  compactness of the unitary group: `polar ∘ X` is continuous wherever `det X` never vanishes
  (`continuous_polar_comp`).
* **Determinant phase.** `projMat X = e^{-i arg(det X)/N} • polar X` has determinant `1`
  (`det_projMat`) and is unitary (`projMat_mem_unitary`). It is gauge covariant under `SU(N)`
  (`projMat_gauge`) and commutes with the adjoint when `det X` lies off the negative real axis
  (`projMat_conjTranspose`), where `arg` is continuous.

**The determinant bound** (`det_blockMatN_mem_slitPlane`): for `0 ≤ c` with `12 c < sin(π/N)` and
`N ≥ 2`, `det (W + c Σ Sᵢ)` lies in the slit plane for every `W, Sᵢ ∈ SU(N)`. Proof: `X = W (1 + A)`
with `A = c Wᴴ Σ Sᵢ` of operator norm at most `6c`; every eigenvalue `μ` of `1 + A` has `|μ − 1| ≤ 6c`,
so `|arg μ| ≤ arcsin(12c) < π/N`; `det X` is the product of the at most `N` eigenvalues, so
`|arg det X| < π`. Such `c > 0` exist at every `N ≥ 2` (`exists_coupling`).

`sunBlockStep hN c hc0 hc : BlockStep (SU N)` is the resulting block step: continuous, gauge covariant,
compatible with inversion and blind to the staple order. For `c > 0` it moves a link: the link
`diag(i, -i, 1, …, 1)` with six identity staples is not returned to itself (`sunStep_moves`).

**The flow.** `BlockStep`, the smearing step, its localisation, the observer flow `obsFlowG`, its
`ConfFlow` `obsConfFlowN`, `physRange_ofN` and `observer_clayN` are copied from the earlier module
`MassGap/ObserverFlowN.lean` (in this repository's git history); they use only the four properties of
a block step. `sunFam hN c hc0 hc s` is the `SU(N)` family built like `FlowZero.apeFam`:
`⌊(s/a_k)²⌋₊` block steps in boxes of half-width `⌊s/a_k⌋₊`. Proved: it is the identity at steps with
`0 ≤ s < a_k` (`sunFam_V_of_lt`), eventually the identity at each fixed step as `s → 0⁺`
(`sunFam_eventually_id`), and `PhysRange r` of `CompositeLink.Φ0 (sunFam … s)` at every `r > s ≥ 0`
(`sunFam_physRange`). Not proved here: that the family's configuration map moves a configuration
(`V k ≠ id` at `s ≥ a_k`; only the single block step is shown to move a link), and `ClassMoments` of the
family.

Foundational footprint only (`#print axioms` throughout).
-/

noncomputable section

namespace MassGap.ObserverFlowSUN

open MassGap.SUN (SU)

/-! ## 1. The unitary polar part -/

section Polar

open Matrix
open scoped MatrixOrder ComplexOrder Topology

variable {N : ℕ}

/-- **The positive part** `√(XᴴX)`.

DERIVED: no numeral. -/
def posPart (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := CFC.sqrt (Xᴴ * X)

/-- **The unitary polar part** `X (√(XᴴX))⁻¹`.

DERIVED: no numeral. -/
def polar (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := X * (posPart X)⁻¹

/-- DERIVED: `0` the order's base point. -/
theorem posPart_nonneg (X : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ posPart X := CFC.sqrt_nonneg _

/-- DERIVED: no numeral. -/
theorem posPart_mul_self (X : Matrix (Fin N) (Fin N) ℂ) : posPart X * posPart X = Xᴴ * X :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self X).nonneg

/-- DERIVED: no numeral. -/
theorem posPart_herm (X : Matrix (Fin N) (Fin N) ℂ) : (posPart X)ᴴ = posPart X :=
  (posPart_nonneg X).posSemidef.isHermitian.eq

/-- DERIVED: `0` the excluded determinant. -/
theorem posPart_det_ne_zero {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0) :
    (posPart X).det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det (posPart_mul_self X)
  rw [det_mul, det_mul, h, zero_mul, det_conjTranspose] at h2
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · exact hX (star_eq_zero.mp h3)
  · exact hX h3

/-- **The polar part is unitary and `(polar X)ᴴ X = √(XᴴX)` is positive semidefinite**, for
`det X ≠ 0`.

DERIVED: `0` the excluded determinant. -/
theorem polar_spec {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0) :
    polar X ∈ unitaryGroup (Fin N) ℂ ∧ ((polar X)ᴴ * X).PosSemidef := by
  have hu : IsUnit (posPart X).det := isUnit_iff_ne_zero.mpr (posPart_det_ne_zero hX)
  have hc : (polar X)ᴴ = (posPart X)⁻¹ * Xᴴ := by
    rw [polar, conjTranspose_mul, conjTranspose_nonsing_inv, posPart_herm]
  have hPX : (polar X)ᴴ * X = posPart X := by
    rw [hc, Matrix.mul_assoc, ← posPart_mul_self, ← Matrix.mul_assoc, nonsing_inv_mul _ hu,
      Matrix.one_mul]
  refine ⟨?_, by rw [hPX]; exact (posPart_nonneg X).posSemidef⟩
  rw [mem_unitaryGroup_iff']
  calc star (polar X) * polar X = (polar X)ᴴ * (X * (posPart X)⁻¹) := rfl
    _ = ((polar X)ᴴ * X) * (posPart X)⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = 1 := by rw [hPX, mul_nonsing_inv _ hu]

#print axioms polar_spec

/-- **Uniqueness of the polar part**: a unitary `V` with `Vᴴ X` positive semidefinite is `polar X`,
for `det X ≠ 0`.

DERIVED: `0` the excluded determinant. -/
theorem polar_unique {X V : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0)
    (hV : V ∈ unitaryGroup (Fin N) ℂ) (hVX : (Vᴴ * X).PosSemidef) : V = polar X := by
  have hVV : V * Vᴴ = 1 := mem_unitaryGroup_iff.mp hV
  have hVV' : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp hV
  have hXQ : X = V * (Vᴴ * X) := by rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hQQ : (Vᴴ * X) * (Vᴴ * X) = Xᴴ * X := by
    calc (Vᴴ * X) * (Vᴴ * X) = (Vᴴ * X)ᴴ * (Vᴴ * X) := by rw [hVX.isHermitian.eq]
      _ = Xᴴ * (V * Vᴴ) * X := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
      _ = Xᴴ * X := by rw [hVV, Matrix.mul_one]
  have hP : posPart X = Vᴴ * X := CFC.sqrt_unique hQQ hVX.nonneg
  have hdQ : IsUnit (Vᴴ * X).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hX ?_
    rw [hXQ, det_mul, h0, mul_zero]
  have e2 : polar X = V * (Vᴴ * X) * (Vᴴ * X)⁻¹ := by
    rw [polar, hP]
    exact congrArg (· * (Vᴴ * X)⁻¹) hXQ
  rw [e2, Matrix.mul_assoc, mul_nonsing_inv _ hdQ, Matrix.mul_one]

#print axioms polar_unique

/-- **Left and right unitary covariance of the polar part.**

DERIVED: `0` the excluded determinant. -/
theorem polar_mul_mul {X g h : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0)
    (hg : g ∈ unitaryGroup (Fin N) ℂ) (hh : h ∈ unitaryGroup (Fin N) ℂ) :
    polar (g * X * hᴴ) = g * polar X * hᴴ := by
  have hdet : (g * X * hᴴ).det ≠ 0 := by
    rw [det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (UnitaryGroup.det_isUnit ⟨g, hg⟩).ne_zero hX)
      (star_ne_zero.mpr (UnitaryGroup.det_isUnit ⟨h, hh⟩).ne_zero)
  have hgg : gᴴ * g = 1 := mem_unitaryGroup_iff'.mp hg
  symm
  refine polar_unique hdet (mul_mem (mul_mem hg (polar_spec hX).1) (Unitary.star_mem hh)) ?_
  have e : (g * polar X * hᴴ)ᴴ * (g * X * hᴴ) = h * ((polar X)ᴴ * X) * hᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ g, hgg, Matrix.one_mul]
  rw [e]
  exact (polar_spec hX).2.mul_mul_conjTranspose_same h

#print axioms polar_mul_mul

/-- **The polar part commutes with the adjoint.**

DERIVED: `0` the excluded determinant. -/
theorem polar_conjTranspose {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0) :
    polar Xᴴ = (polar X)ᴴ := by
  have hdet : Xᴴ.det ≠ 0 := by rw [det_conjTranspose]; exact star_ne_zero.mpr hX
  obtain ⟨hU, hP⟩ := polar_spec hX
  have hUU : polar X * (polar X)ᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have hH : Xᴴ * polar X = (polar X)ᴴ * X := by
    have := hP.isHermitian.eq
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at this
  symm
  refine polar_unique hdet (Unitary.star_mem hU) ?_
  have e : ((polar X)ᴴ)ᴴ * Xᴴ = polar X * ((polar X)ᴴ * X) * (polar X)ᴴ := by
    rw [conjTranspose_conjTranspose, ← hH, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one]
  rw [e]
  exact hP.mul_mul_conjTranspose_same _

#print axioms polar_conjTranspose

/-- The unitary matrices form a compact set.

DERIVED: `1` the radius of the entry ball. -/
theorem isCompact_unitary (N : ℕ) :
    IsCompact (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hclosed : IsClosed (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
    have hset : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))
        = {M | star M * M = 1} := by
      ext M; exact mem_unitaryGroup_iff'
    rw [hset]
    exact isClosed_eq (continuous_id.matrix_conjTranspose.mul continuous_id) continuous_const
  have hK : IsCompact
      {M : Matrix (Fin N) (Fin N) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1} := by
    have hpi : {M : Matrix (Fin N) (Fin N) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1}
        = Set.univ.pi (fun _ : Fin N => Set.univ.pi (fun _ : Fin N =>
          Metric.closedBall (0 : ℂ) 1)) := by
      ext M
      constructor
      · intro h i _ j _; exact h i j
      · intro h i j; exact h i (Set.mem_univ i) j (Set.mem_univ j)
    rw [hpi]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  refine hK.of_isClosed_subset hclosed ?_
  intro M hM i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact MassGap.SUN.unitary_entry_norm_le_one N hM i j

#print axioms isCompact_unitary

/-- The positive semidefinite matrices form a closed set.

DERIVED: `0` the order's base point. -/
theorem isClosed_posSemidef (N : ℕ) :
    IsClosed {M : Matrix (Fin N) (Fin N) ℂ | M.PosSemidef} := by
  have hIci : IsClosed (Set.Ici (0 : ℂ)) := isClosed_Ici
  have hset : {M : Matrix (Fin N) (Fin N) ℂ | M.PosSemidef}
      = {M | Mᴴ = M} ∩ ⋂ x : Fin N → ℂ,
        (fun M : Matrix (Fin N) (Fin N) ℂ => star x ⬝ᵥ (M *ᵥ x)) ⁻¹' Set.Ici 0 := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
    exact posSemidef_iff_dotProduct_mulVec
  rw [hset]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => hIci.preimage ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

#print axioms isClosed_posSemidef

/-- **The polar part is continuous along any continuous family of invertible matrices.** The values lie
in the compact unitary group, and every cluster point `V` at `p` is unitary with `Vᴴ X p` positive
semidefinite (a closed condition), hence `V = polar (X p)` by uniqueness.

DERIVED: `0` the excluded determinant. -/
theorem continuous_polar_comp {D : Type*} [TopologicalSpace D] {X : D → Matrix (Fin N) (Fin N) ℂ}
    (hX : Continuous X) (hdet : ∀ q, (X q).det ≠ 0) : Continuous (fun q => polar (X q)) := by
  rw [continuous_iff_continuousAt]
  intro p
  refine (isCompact_unitary N).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun q => (polar_spec (hdet q)).1) ?_
  intro V hV hcl
  refine polar_unique (hdet p) hV ?_
  by_contra hneg
  have hΦ : Continuous (fun r : D × Matrix (Fin N) (Fin N) ℂ => r.2ᴴ * X r.1) :=
    continuous_snd.matrix_conjTranspose.mul (hX.comp continuous_fst)
  have hmem : (fun r : D × Matrix (Fin N) (Fin N) ℂ => r.2ᴴ * X r.1) ⁻¹'
      {M : Matrix (Fin N) (Fin N) ℂ | M.PosSemidef}ᶜ ∈ 𝓝 (p, V) :=
    hΦ.continuousAt.preimage_mem_nhds ((isClosed_posSemidef N).isOpen_compl.mem_nhds hneg)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨q, hqB, hqA⟩ := (((mapClusterPt_iff_frequently.mp hcl) B hB).and_eventually hA).exists
  exact hAB (Set.mk_mem_prod hqA hqB) (polar_spec (hdet q)).2

#print axioms continuous_polar_comp

end Polar

/-! ## 2. The determinant of the block matrix stays off the negative axis -/

section Det

open Matrix
open scoped ComplexOrder

variable {N : ℕ}

/-- **The block matrix**: the link plus `c` times the six staples.

DERIVED: `6` the staple count. -/
def blockMatN (c : ℝ) (W : SU N) (S : Fin 6 → SU N) : Matrix (Fin N) (Fin N) ℂ :=
  (W : Matrix (Fin N) (Fin N) ℂ) + (c : ℂ) • ∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)

/-- The staple part relative to the link, `c Wᴴ Σ Sᵢ`.

DERIVED: `6` the staple count. -/
def stapleRel (c : ℝ) (W : SU N) (S : Fin 6 → SU N) : Matrix (Fin N) (Fin N) ℂ :=
  (c : ℂ) • ((W : Matrix (Fin N) (Fin N) ℂ)ᴴ * ∑ i, (S i : Matrix (Fin N) (Fin N) ℂ))

/-- `W + c Σ Sᵢ = W (1 + c Wᴴ Σ Sᵢ)`.

DERIVED: `1` the identity; `6` the staple count. -/
theorem blockMatN_eq (c : ℝ) (W : SU N) (S : Fin 6 → SU N) :
    blockMatN c W S = (W : Matrix (Fin N) (Fin N) ℂ) * (1 + stapleRel c W S) := by
  have hWW : (W : Matrix (Fin N) (Fin N) ℂ) * (W : Matrix (Fin N) (Fin N) ℂ)ᴴ = 1 :=
    mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp W.2).1
  rw [blockMatN, stapleRel, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hWW,
    Matrix.one_mul]

open scoped Matrix.Norms.L2Operator in
/-- **Every eigenvalue of the relative staple part has modulus at most `6c`**: in the operator norm a
unitary matrix has norm `1`, so `‖c Wᴴ Σ Sᵢ‖ ≤ 6c`, and the spectrum lies in the ball of that radius.

DERIVED: `6` the staple count; `1` the norm of a unitary matrix and the least `N`. -/
theorem norm_spectrum_stapleRel_le (hN : 1 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (W : SU N)
    (S : Fin 6 → SU N) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (stapleRel c W S)) : ‖μ‖ ≤ 6 * c := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  haveI : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℂ _
  have h1 := spectrum.norm_le_norm_mul_of_mem hμ
  rw [CStarRing.norm_one, mul_one] at h1
  have hW : ‖(W : Matrix (Fin N) (Fin N) ℂ)ᴴ‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Unitary.star_mem (mem_specialUnitaryGroup_iff.mp W.2).1)
  have hS : ‖∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖ ≤ 6 := by
    calc ‖∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖
        ≤ ∑ i, ‖(S i : Matrix (Fin N) (Fin N) ℂ)‖ := norm_sum_le _ _
      _ = ∑ _i : Fin 6, (1 : ℝ) := Finset.sum_congr rfl fun i _ =>
          CStarRing.norm_of_mem_unitary (mem_specialUnitaryGroup_iff.mp (S i).2).1
      _ = 6 := by simp
  have h2 : ‖stapleRel c W S‖ ≤ 6 * c := by
    rw [stapleRel, norm_smul, Complex.norm_of_nonneg hc0]
    calc c * ‖(W : Matrix (Fin N) (Fin N) ℂ)ᴴ * ∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖
        ≤ c * (‖(W : Matrix (Fin N) (Fin N) ℂ)ᴴ‖ * ‖∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) hc0
      _ ≤ c * (1 * 6) := by rw [hW]; exact mul_le_mul_of_nonneg_left (by linarith) hc0
      _ = 6 * c := by ring
  linarith

#print axioms norm_spectrum_stapleRel_le

/-- **Every eigenvalue of `1 + A` lies within `6c` of `1`.**

DERIVED: `6` the staple count; `1` the identity and the least `N`. -/
theorem norm_sub_one_le_of_root (hN : 1 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (W : SU N) (S : Fin 6 → SU N)
    {z : ℂ} (hz : z ∈ (charpoly (1 + stapleRel c W S)).roots) : ‖z - 1‖ ≤ 6 * c := by
  have h1 : z ∈ spectrum ℂ (1 + stapleRel c W S) :=
    mem_spectrum_iff_isRoot_charpoly.mpr ((Polynomial.mem_roots (charpoly_monic _).ne_zero).mp hz)
  have h2 : z - 1 ∈ spectrum ℂ (stapleRel c W S) := by
    rw [spectrum.mem_iff] at h1 ⊢
    have e : algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) (z - 1) - stapleRel c W S
        = algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) z - (1 + stapleRel c W S) := by
      rw [map_sub, map_one]; abel
    rw [e]; exact h1
  exact norm_spectrum_stapleRel_le hN hc0 W S h2

#print axioms norm_sub_one_le_of_root

/-- **A number within `δ ≤ 1/2` of `1` is non-zero with argument at most `arcsin (2δ)`.**

DERIVED: `1/2` the radius bound; `2` the ratio `δ/(1-δ) ≤ 2δ`. -/
theorem arg_bound {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / 2) (hz : ‖z - 1‖ ≤ δ) :
    z ≠ 0 ∧ |Complex.arg z| ≤ Real.arcsin (2 * δ) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hz
  have hre : 1 - δ ≤ z.re := by
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [(abs_le.mp (this.trans hz)).1]
  have him : |z.im| ≤ δ := by
    have := Complex.abs_im_le_norm (z - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hnorm : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hpos : 0 < ‖z‖ := by linarith
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [Complex.arg_of_re_nonneg (by linarith)]
  have hy : |z.im / ‖z‖| ≤ 2 * δ := by
    rw [abs_div, abs_norm, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr (hre.trans hnorm)),
      mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ 1 - 2 * δ)]
  have hy' := abs_le.mp hy
  rw [abs_le]
  constructor
  · rw [← Real.arcsin_neg]; exact Real.arcsin_le_arcsin hy'.1
  · exact Real.arcsin_le_arcsin hy'.2

#print axioms arg_bound

/-- **Arguments add when their sum stays inside `(-π, π)`.**

DERIVED: `2π` the period. -/
theorem arg_mul_of_abs_lt {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : |Complex.arg a + Complex.arg b| < Real.pi) :
    Complex.arg (a * b) = Complex.arg a + Complex.arg b := by
  have e : a * b = ((‖a‖ * ‖b‖ : ℝ) : ℂ)
      * Complex.exp (((Complex.arg a + Complex.arg b : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a, ← Complex.norm_mul_exp_arg_mul_I b]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  rw [e, Complex.arg_real_mul _ (mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)),
    Complex.arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> linarith [(abs_lt.mp h).1, (abs_lt.mp h).2]

#print axioms arg_mul_of_abs_lt

/-- **A product of `m` non-zero numbers of argument at most `α`, with `m α < π`, is non-zero with
argument at most `m α`.**

DERIVED: `0` the empty product's argument; `1` the step. -/
theorem multiset_prod_arg {α : ℝ} (hα : 0 ≤ α) (s : Multiset ℂ)
    (hs : ∀ z ∈ s, z ≠ 0 ∧ |Complex.arg z| ≤ α)
    (hcard : (Multiset.card s : ℝ) * α < Real.pi) :
    s.prod ≠ 0 ∧ |Complex.arg s.prod| ≤ (Multiset.card s : ℝ) * α := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Nat.cast_add, Nat.cast_one] at hcard ⊢
    have ha := hs a (Multiset.mem_cons.mpr (Or.inl rfl))
    have ih' := ih (fun z hz => hs z (Multiset.mem_cons.mpr (Or.inr hz))) (by nlinarith)
    rw [Multiset.prod_cons]
    have hsum : |Complex.arg a + Complex.arg s.prod| ≤ α + (Multiset.card s : ℝ) * α :=
      (abs_add_le _ _).trans (add_le_add ha.2 ih'.2)
    refine ⟨mul_ne_zero ha.1 ih'.1, ?_⟩
    rw [arg_mul_of_abs_lt ha.1 ih'.1 (by nlinarith)]
    nlinarith

#print axioms multiset_prod_arg

/-- **The determinant of the block matrix lies in the slit plane** for `N ≥ 2`, `0 ≤ c` and
`12 c < sin (π / N)`: it is the product of the at most `N` eigenvalues of `1 + c Wᴴ Σ Sᵢ`, each of
argument at most `arcsin (12 c) < π / N`.

DERIVED: `2` the least rank; `12 = 2 · 6` the ratio bound times the staple count; `π / N` the share of
the half-turn per eigenvalue. -/
theorem det_blockMatN_mem_slitPlane (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (W : SU N) (S : Fin 6 → SU N) :
    (blockMatN c W S).det ∈ Complex.slitPlane := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsin1 : Real.sin (Real.pi / N) ≤ 1 := Real.sin_le_one _
  have hδ : 6 * c ≤ 1 / 2 := by linarith
  have hπN : Real.pi / N ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hN2
  have hπN0 : 0 < Real.pi / N := div_pos Real.pi_pos hN0
  have hα0 : 0 ≤ Real.arcsin (2 * (6 * c)) := Real.arcsin_nonneg.mpr (by linarith)
  have hαlt : Real.arcsin (2 * (6 * c)) < Real.pi / N := by
    rw [Real.arcsin_lt_iff_lt_sin ⟨by linarith, by linarith⟩ ⟨by linarith, hπN⟩]
    linarith
  have hroots : ∀ z ∈ (charpoly (1 + stapleRel c W S)).roots,
      z ≠ 0 ∧ |Complex.arg z| ≤ Real.arcsin (2 * (6 * c)) :=
    fun z hz => arg_bound hδ (norm_sub_one_le_of_root (by omega) hc0 W S hz)
  have hcard : (Multiset.card (charpoly (1 + stapleRel c W S)).roots : ℝ) ≤ N := by
    have := Polynomial.card_roots' (charpoly (1 + stapleRel c W S))
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  have hlt : (Multiset.card (charpoly (1 + stapleRel c W S)).roots : ℝ)
      * Real.arcsin (2 * (6 * c)) < Real.pi := by
    calc _ ≤ (N : ℝ) * Real.arcsin (2 * (6 * c)) := mul_le_mul_of_nonneg_right hcard hα0
      _ < N * (Real.pi / N) := mul_lt_mul_of_pos_left hαlt hN0
      _ = Real.pi := by field_simp
  obtain ⟨hne, harg⟩ := multiset_prod_arg hα0 _ hroots hlt
  have hdet : (blockMatN c W S).det = (charpoly (1 + stapleRel c W S)).roots.prod := by
    rw [blockMatN_eq, det_mul, (mem_specialUnitaryGroup_iff.mp W.2).2, one_mul,
      det_eq_prod_roots_charpoly]
  rw [hdet, Complex.mem_slitPlane_iff_arg]
  refine ⟨fun hπ => ?_, hne⟩
  rw [hπ, abs_of_pos Real.pi_pos] at harg
  linarith

#print axioms det_blockMatN_mem_slitPlane

/-- **Admissible couplings exist**: at every `N ≥ 2` some `c > 0` has `12 c < sin (π / N)`.

DERIVED: `2` the least rank; `24 = 2 · 12` halves the bound. -/
theorem exists_coupling (hN : 2 ≤ N) : ∃ c : ℝ, 0 < c ∧ 12 * c < Real.sin (Real.pi / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hs : 0 < Real.sin (Real.pi / N) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hN0) (div_lt_self Real.pi_pos hN1)
  exact ⟨Real.sin (Real.pi / N) / 24, by positivity, by linarith⟩

#print axioms exists_coupling

end Det

/-! ## 3. The projection to `SU(N)` -/

section Proj

open Matrix
open scoped MatrixOrder ComplexOrder

variable {N : ℕ}

/-- **The determinant phase** `e^{-i arg(det X)/N}`.

DERIVED: no numeral. -/
def phase (X : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  Complex.exp ((((-(Complex.arg X.det / N)) : ℝ) : ℂ) * Complex.I)

/-- **The projection** `e^{-i arg(det X)/N} • polar X`.

DERIVED: no numeral. -/
def projMat (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := phase X • polar X

/-- DERIVED: `1` the modulus. -/
theorem star_phase_mul (X : Matrix (Fin N) (Fin N) ℂ) : star (phase X) * phase X = 1 := by
  rw [phase, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, neg_add_cancel, Complex.exp_zero]

/-- **The projection is unitary**, for `det X ≠ 0`.

DERIVED: `0` the excluded determinant. -/
theorem projMat_mem_unitary {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0) :
    projMat X ∈ unitaryGroup (Fin N) ℂ := by
  rw [mem_unitaryGroup_iff', projMat, star_smul, smul_mul_smul_comm, star_phase_mul, one_smul]
  exact mem_unitaryGroup_iff'.mp (polar_spec hX).1

#print axioms projMat_mem_unitary

/-- **The projection has determinant `1`**, for `N ≠ 0` and `det X ≠ 0`: `det (polar X)` has modulus
`1` and the argument of `det X`, since `det X = det (polar X) · det √(XᴴX)` with the second factor
positive.

DERIVED: `0` the excluded rank and determinant; `1` the determinant. -/
theorem det_projMat (hN : N ≠ 0) {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0) :
    (projMat X).det = 1 := by
  obtain ⟨hU, hP⟩ := polar_spec hX
  have hUU : polar X * (polar X)ᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have hXUP : X = polar X * ((polar X)ᴴ * X) := by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hdetX : X.det = (polar X).det * ((polar X)ᴴ * X).det := by
    conv_lhs => rw [hXUP]
    rw [det_mul]
  have hr0 : ((polar X)ᴴ * X).det ≠ 0 := by
    intro h0; apply hX; rw [hdetX, h0, mul_zero]
  have hnn := Complex.nonneg_iff.mp hP.det_nonneg
  have hrpos : 0 < ((polar X)ᴴ * X).det.re := by
    rcases hnn.1.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext (by rw [Complex.zero_re]; exact heq.symm)
        (by rw [Complex.zero_im]; exact hnn.2.symm)) hr0
  have hreal : ((polar X)ᴴ * X).det = ((((polar X)ᴴ * X).det.re : ℝ) : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact hnn.2.symm)
  have hθ : Complex.arg X.det = Complex.arg (polar X).det := by
    rw [hdetX, hreal, Complex.arg_mul_real hrpos]
  have hU1 : (polar X).det = Complex.exp (Complex.arg (polar X).det * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (polar X).det]
    rw [CStarRing.norm_of_mem_unitary (det_of_mem_unitary hU), Complex.ofReal_one, one_mul]
  rw [projMat, det_smul, Fintype.card_fin, phase, hθ]
  generalize Complex.arg (polar X).det = θ at hU1 ⊢
  rw [hU1, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e : (N : ℂ) * ((((-(θ / N)) : ℝ) : ℂ) * Complex.I) + (θ : ℂ) * Complex.I = 0 := by
    push_cast
    field_simp
    ring
  rw [e, Complex.exp_zero]

#print axioms det_projMat

/-- **The projection is `SU(N)` covariant on both sides**, for `det X ≠ 0`.

DERIVED: `0` the excluded determinant. -/
theorem projMat_gauge {X g h : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ≠ 0)
    (hg : g ∈ specialUnitaryGroup (Fin N) ℂ) (hh : h ∈ specialUnitaryGroup (Fin N) ℂ) :
    projMat (g * X * hᴴ) = g * projMat X * hᴴ := by
  have hdet : (g * X * hᴴ).det = X.det := by
    rw [det_mul, det_mul, (mem_specialUnitaryGroup_iff.mp hg).2, det_conjTranspose,
      (mem_specialUnitaryGroup_iff.mp hh).2, star_one, one_mul, mul_one]
  simp only [projMat, phase]
  rw [hdet, polar_mul_mul hX (mem_specialUnitaryGroup_iff.mp hg).1
    (mem_specialUnitaryGroup_iff.mp hh).1, Matrix.mul_smul, Matrix.smul_mul]

#print axioms projMat_gauge

/-- **The projection commutes with the adjoint** when `det X` lies in the slit plane.

DERIVED: no numeral. -/
theorem projMat_conjTranspose {X : Matrix (Fin N) (Fin N) ℂ} (hX : X.det ∈ Complex.slitPlane) :
    projMat Xᴴ = (projMat X)ᴴ := by
  have hX0 : X.det ≠ 0 := Complex.slitPlane_ne_zero hX
  have harg : Complex.arg Xᴴ.det = -Complex.arg X.det := by
    rw [det_conjTranspose, Complex.star_def, Complex.arg_conj,
      if_neg (Complex.mem_slitPlane_iff_arg.mp hX).1]
  have hd : Complex.exp ((((-(-Complex.arg X.det / N)) : ℝ) : ℂ) * Complex.I)
      = star (Complex.exp ((((-(Complex.arg X.det / N)) : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  simp only [projMat, phase]
  rw [harg, polar_conjTranspose hX0, conjTranspose_smul, hd]

#print axioms projMat_conjTranspose

end Proj

/-! ## 4. The `SU(N)` block step -/

section Step

open Matrix

variable {N : ℕ}

/-- DERIVED: no numeral. -/
theorem coe_inv_SU (h : SU N) :
    ((h⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) = (h : Matrix (Fin N) (Fin N) ℂ)ᴴ := rfl

/-- The block matrix of gauge-transformed inputs is the gauge-transformed block matrix.

DERIVED: `6` the staple count. -/
theorem blockMatN_gauge (c : ℝ) (g h W : SU N) (S : Fin 6 → SU N) :
    blockMatN c (g * W * h⁻¹) (fun i => g * S i * h⁻¹)
      = (g : Matrix (Fin N) (Fin N) ℂ) * blockMatN c W S * ((h⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  unfold blockMatN
  simp only [Submonoid.coe_mul]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul]

#print axioms blockMatN_gauge

/-- The block matrix of inverted inputs is the adjoint of the block matrix.

DERIVED: `6` the staple count. -/
theorem blockMatN_inv (c : ℝ) (W : SU N) (S : Fin 6 → SU N) :
    blockMatN c W⁻¹ (fun i => (S i)⁻¹) = star (blockMatN c W S) := by
  unfold blockMatN
  rw [star_add, star_smul, star_sum, Complex.star_def, Complex.conj_ofReal]
  rfl

#print axioms blockMatN_inv

/-- **The `SU(N)` block step**: the projection of `W + c Σ Sᵢ`.

DERIVED: `2` the least rank; `12`, `6` as in `det_blockMatN_mem_slitPlane`. -/
def sunStep (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (W : SU N)
    (S : Fin 6 → SU N) : SU N :=
  ⟨projMat (blockMatN c W S), mem_specialUnitaryGroup_iff.mpr
    ⟨projMat_mem_unitary (Complex.slitPlane_ne_zero (det_blockMatN_mem_slitPlane hN hc0 hc W S)),
     det_projMat (by omega) (Complex.slitPlane_ne_zero (det_blockMatN_mem_slitPlane hN hc0 hc W S))⟩⟩

/-- **The `SU(N)` block step is continuous.**

DERIVED: `2` the least rank; `12`, `6` as in `det_blockMatN_mem_slitPlane`. -/
theorem continuous_sunStep (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) :
    Continuous (fun p : SU N × (Fin 6 → SU N) => sunStep hN c hc0 hc p.1 p.2) := by
  have hX : Continuous (fun p : SU N × (Fin 6 → SU N) => blockMatN c p.1 p.2) := by
    unfold blockMatN
    refine (continuous_subtype_val.comp continuous_fst).add (continuous_const.smul ?_)
    exact continuous_finsetSum _ (fun i _ =>
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  have hslit := fun p : SU N × (Fin 6 → SU N) => det_blockMatN_mem_slitPlane hN hc0 hc p.1 p.2
  have hpolar := continuous_polar_comp hX (fun p => Complex.slitPlane_ne_zero (hslit p))
  have harg : Continuous (fun p : SU N × (Fin 6 → SU N) => Complex.arg (blockMatN c p.1 p.2).det) :=
    continuous_iff_continuousAt.mpr fun p =>
      (Complex.continuousAt_arg (hslit p)).comp
        (f := fun p : SU N × (Fin 6 → SU N) => (blockMatN c p.1 p.2).det)
        hX.matrix_det.continuousAt
  have hphase : Continuous (fun p : SU N × (Fin 6 → SU N) => phase (blockMatN c p.1 p.2)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (harg.div_const (N : ℝ)).neg).mul continuous_const)
  exact (hphase.smul hpolar).subtype_mk _

#print axioms continuous_sunStep

/-- **The `SU(N)` block step is gauge covariant.**

DERIVED: `2` the least rank; `12`, `6` as in `det_blockMatN_mem_slitPlane`. -/
theorem sunStep_gauge (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (g h W : SU N) (S : Fin 6 → SU N) :
    sunStep hN c hc0 hc (g * W * h⁻¹) (fun i => g * S i * h⁻¹) = g * sunStep hN c hc0 hc W S * h⁻¹ := by
  apply Subtype.ext
  show projMat (blockMatN c (g * W * h⁻¹) (fun i => g * S i * h⁻¹))
    = (g : Matrix (Fin N) (Fin N) ℂ) * projMat (blockMatN c W S)
      * ((h⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ)
  rw [blockMatN_gauge, coe_inv_SU,
    projMat_gauge (Complex.slitPlane_ne_zero (det_blockMatN_mem_slitPlane hN hc0 hc W S)) g.2 h.2]

#print axioms sunStep_gauge

/-- **The `SU(N)` block step commutes with inversion.**

DERIVED: `2` the least rank; `12`, `6` as in `det_blockMatN_mem_slitPlane`. -/
theorem sunStep_inv (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (W : SU N) (S : Fin 6 → SU N) :
    sunStep hN c hc0 hc W⁻¹ (fun i => (S i)⁻¹) = (sunStep hN c hc0 hc W S)⁻¹ := by
  apply Subtype.ext
  show projMat (blockMatN c W⁻¹ (fun i => (S i)⁻¹)) = star (projMat (blockMatN c W S))
  rw [blockMatN_inv]
  exact projMat_conjTranspose (det_blockMatN_mem_slitPlane hN hc0 hc W S)

#print axioms sunStep_inv

/-- **The `SU(N)` block step does not depend on the order of the staples.**

DERIVED: `2` the least rank; `6` the staple count; `12` as in `det_blockMatN_mem_slitPlane`. -/
theorem sunStep_perm (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (W : SU N) (S : Fin 6 → SU N) (σ : Equiv.Perm (Fin 6)) :
    sunStep hN c hc0 hc W (S ∘ σ) = sunStep hN c hc0 hc W S := by
  have hM : blockMatN c W (S ∘ σ) = blockMatN c W S := by
    unfold blockMatN
    congr 2
    exact Equiv.sum_comp σ (fun i => (S i : Matrix (Fin N) (Fin N) ℂ))
  apply Subtype.ext
  show projMat (blockMatN c W (S ∘ σ)) = projMat (blockMatN c W S)
  rw [hM]

#print axioms sunStep_perm

end Step

/-! ## 5. The step moves a link -/

section Nondeg

open Matrix
open scoped MatrixOrder ComplexOrder

variable {N : ℕ}

/-- The diagonal of the witness `diag(i, -i, 1, …, 1)` in rank `m + 2`.

DERIVED: `2` the least rank; `1` the remaining entries. -/
def witnessVec (m : ℕ) : Fin (m + 2) → ℂ :=
  Fin.cons Complex.I (Fin.cons (-Complex.I) (fun _ => 1))

/-- `diag(i, -i, 1, …, 1) ∈ SU(m + 2)`.

DERIVED: `2` the least rank; `1` the determinant. -/
theorem witness_mem (m : ℕ) : diagonal (witnessVec m) ∈ specialUnitaryGroup (Fin (m + 2)) ℂ := by
  refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [witnessVec]
  · rw [det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [witnessVec]

#print axioms witness_mem

/-- **The block step moves a link**: for `N ≥ 2` and an admissible `c > 0`, the link
`D = diag(i, -i, 1, …, 1)` with six identity staples is not returned to itself. If it were,
`polar (D + 6c) = e^{iφ} D` for a unit `e^{iφ}`, and the positive semidefinite
`(polar X)ᴴ X` would have diagonal entries `e^{-iφ}(1 - 6ci)` and `e^{-iφ}(1 + 6ci)`, both real and
non-negative, which forces `e^{-iφ} = 0`.

DERIVED: `2` the least rank; `6` the staple count; `0` the lower end of `c`; `12` as in
`det_blockMatN_mem_slitPlane`. -/
theorem sunStep_moves (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) :
    ∃ (W : SU N) (S : Fin 6 → SU N), sunStep hN c hc0 hc W S ≠ W := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  refine ⟨⟨diagonal (witnessVec m), witness_mem m⟩, fun _ => 1, fun h => ?_⟩
  have hM : projMat (blockMatN c ⟨diagonal (witnessVec m), witness_mem m⟩ (fun _ => 1))
      = diagonal (witnessVec m) := congrArg Subtype.val h
  set X := blockMatN c ⟨diagonal (witnessVec m), witness_mem m⟩ (fun _ => 1) with hXdef
  have hX0 : X.det ≠ 0 :=
    Complex.slitPlane_ne_zero (det_blockMatN_mem_slitPlane hN hc0 hc _ _)
  set d := phase X with hd
  have hdd : star d * d = 1 := star_phase_mul X
  have hU : polar X = star d • diagonal (witnessVec m) := by
    rw [← hM, projMat, smul_smul, ← hd, hdd, one_smul]
  have hP := (polar_spec hX0).2
  rw [hU, conjTranspose_smul, star_star, smul_mul, diagonal_conjTranspose] at hP
  have hentry : ∀ j : Fin (m + 2), (d • (diagonal (star (witnessVec m)) * X)) j j
      = d * (star (witnessVec m j) * (witnessVec m j + 6 * c)) := by
    intro j
    rw [Matrix.smul_apply, diagonal_mul, smul_eq_mul, hXdef]
    congr 2
    simp [blockMatN, Matrix.ofNat_apply, mul_comm]
  have h0 := Complex.nonneg_iff.mp (hP.diag_nonneg (i := 0))
  have h1 := Complex.nonneg_iff.mp (hP.diag_nonneg (i := 1))
  rw [hentry] at h0 h1
  simp [witnessVec, Complex.mul_im, Complex.mul_re] at h0 h1
  have hn : d.re * d.re + d.im * d.im = 1 := by
    have := congrArg Complex.re hdd
    simpa [Complex.mul_re] using this
  have hre : d.re = 0 := by
    have h12 : 12 * c * d.re = 0 := by linarith [h0.2, h1.2]
    rcases mul_eq_zero.mp h12 with h | h
    · linarith
    · exact h
  have him : d.im = 0 := by nlinarith [h0.2, h1.2]
  rw [hre, him] at hn
  norm_num at hn

#print axioms sunStep_moves

end Nondeg

/-! ## 6. The observer flow for any block step

Copied from the earlier `MassGap.ObserverFlowN` (in this repository's git history). -/

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.BlockLattice
  MassGap.LocalApe MassGap.ReflApe MassGap.LatticeReflection
  MassGap.GaugeInvariantAlgebra MassGap.ObserverFlow

/-- **A block step on a group `G`**: a map from a link and its six staples back to the group,
continuous, gauge covariant, compatible with inversion and blind to the staple order.

DERIVED: `6` is the number of staples beside a link in four dimensions (three transverse directions,
two sides each). -/
structure BlockStep (G : Type) [Group G] [TopologicalSpace G] where
  /-- The step. -/
  step : G → (Fin 6 → G) → G
  /-- Continuity in the link and the staples. -/
  continuous_step : Continuous (fun p : G × (Fin 6 → G) => step p.1 p.2)
  /-- Gauge covariance. -/
  gauge : ∀ (g h W : G) (S : Fin 6 → G),
    step (g * W * h⁻¹) (fun i => g * S i * h⁻¹) = g * step W S * h⁻¹
  /-- Inversion. -/
  inv : ∀ (W : G) (S : Fin 6 → G), step W⁻¹ (fun i => (S i)⁻¹) = (step W S)⁻¹
  /-- Staple order. -/
  perm : ∀ (W : G) (S : Fin 6 → G) (σ : Equiv.Perm (Fin 6)), step W (S ∘ σ) = step W S

/-- **The `SU(N)` block step as a `BlockStep`**, for `N ≥ 2`, `0 ≤ c` and `12 c < sin (π / N)`.

DERIVED: `2` the least rank; `12` as in `det_blockMatN_mem_slitPlane`. -/
def sunBlockStep {N : ℕ} (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) : BlockStep (SU N) where
  step := sunStep hN c hc0 hc
  continuous_step := continuous_sunStep hN hc0 hc
  gauge g h W S := sunStep_gauge hN hc0 hc g h W S
  inv W S := sunStep_inv hN hc0 hc W S
  perm W S σ := sunStep_perm hN hc0 hc W S σ

section Flow

variable {G : Type} [Group G] [TopologicalSpace G]

/-- **A same-lattice staple** beside the link `(μ, x)`: transverse direction `other μ p.1`, side `p.2`.

DERIVED: `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
def stapleG (U : IConf G) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) : G :=
  if p.2 = 0 then
    U (other μ p.1, x) * U (μ, ishift (other μ p.1) x) * (U (other μ p.1, ishift μ x))⁻¹
  else
    (U (other μ p.1, iback (other μ p.1) x))⁻¹ * U (μ, iback (other μ p.1) x)
      * U (other μ p.1, ishift μ (iback (other μ p.1) x))

/-- **One smearing step**: every link replaced by the block step of itself and its six staples.

DERIVED: `6 = 3 · 2` staples. -/
def stepConf (B : BlockStep G) (U : IConf G) : IConf G :=
  fun l => B.step (U l) (fun i => stapleG U l.1 l.2 (finProdFinEquiv.symm i))

omit [TopologicalSpace G] in
/-- A staple of a gauge-transformed configuration.

DERIVED: `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
theorem stapleG_gauge (g : ISite → G) (U : IConf G) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    stapleG (igaugeTransform g U) μ x p = g x * stapleG U μ x p * (g (ishift μ x))⁻¹ := by
  have hup : ishift μ (ishift (other μ p.1) x) = ishift (other μ p.1) (ishift μ x) :=
    ishift_comm μ (other μ p.1) x
  have hdn : ishift (other μ p.1) (iback (other μ p.1) x) = x := ishift_iback _ _
  have hdn2 : ishift (other μ p.1) (ishift μ (iback (other μ p.1) x)) = ishift μ x := by
    rw [ishift_comm (other μ p.1) μ, hdn]
  unfold stapleG
  split_ifs with h
  · simp only [igaugeTransform]
    rw [hup]
    group
  · simp only [igaugeTransform]
    rw [hdn, hdn2]
    group

#print axioms stapleG_gauge

/-- **The smearing step is gauge covariant.**

DERIVED: no numeral. -/
theorem stepConf_gauge (B : BlockStep G) (g : ISite → G) (U : IConf G) :
    stepConf B (igaugeTransform g U) = igaugeTransform g (stepConf B U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  simp only [stepConf]
  have hS : (fun i => stapleG (igaugeTransform g U) μ x (finProdFinEquiv.symm i))
      = fun i => g x * stapleG U μ x (finProdFinEquiv.symm i) * (g (ishift μ x))⁻¹ :=
    funext (fun i => stapleG_gauge g U μ x _)
  rw [hS]
  show B.step (g x * U (μ, x) * (g (ishift μ x))⁻¹) _ = _
  rw [B.gauge]
  rfl

#print axioms stepConf_gauge

/-- A staple is continuous in the configuration.

DERIVED: `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
theorem continuous_stapleG [IsTopologicalGroup G] (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    Continuous (fun U : IConf G => stapleG U μ x p) := by
  by_cases h : p.2 = 0
  · simp only [stapleG, h, if_true]
    fun_prop
  · simp only [stapleG, h, if_false]
    fun_prop

#print axioms continuous_stapleG

/-- **The smearing step is continuous** in the product topology.

DERIVED: no numeral. -/
theorem continuous_stepConf [IsTopologicalGroup G] (B : BlockStep G) : Continuous (stepConf B) := by
  refine continuous_pi (fun l => ?_)
  have hs : Continuous (fun U : IConf G => fun i : Fin 6 => stapleG U l.1 l.2 (finProdFinEquiv.symm i)) :=
    continuous_pi (fun i => continuous_stapleG l.1 l.2 _)
  exact B.continuous_step.comp ((continuous_apply l).prodMk hs)

#print axioms continuous_stepConf

/-- **One smearing step on the links of `S`**, the identity elsewhere.

DERIVED: no numeral. -/
def stepOn (B : BlockStep G) (S : Set ILink) (U : IConf G) : IConf G := by
  classical
  exact fun l => if l ∈ S then stepConf B U l else U l

/-- **The localised step is gauge covariant.**

DERIVED: no numeral. -/
theorem stepOn_gauge (B : BlockStep G) (S : Set ILink) (g : ISite → G) (U : IConf G) :
    stepOn B S (igaugeTransform g U) = igaugeTransform g (stepOn B S U) := by
  classical
  funext l
  have key := congrFun (stepConf_gauge B g U) l
  simp only [stepOn, igaugeTransform] at key ⊢
  split_ifs with h
  · exact key
  · rfl

#print axioms stepOn_gauge

/-- Iterates of the localised step stay gauge covariant.

DERIVED: `0` is the base of the induction. -/
theorem stepOnIter_gauge (B : BlockStep G) (S : Set ILink) (n : ℕ) (g : ISite → G) (U : IConf G) :
    (stepOn B S)^[n] (igaugeTransform g U) = igaugeTransform g ((stepOn B S)^[n] U) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepOn_gauge, ih]

#print axioms stepOnIter_gauge

/-- **The localised step is continuous.**

DERIVED: no numeral. -/
theorem continuous_stepOn [IsTopologicalGroup G] (B : BlockStep G) (S : Set ILink) : Continuous (stepOn B S) := by
  classical
  refine continuous_pi (fun l => ?_)
  simp only [stepOn]
  split_ifs with h
  · exact (continuous_apply l).comp (continuous_stepConf B)
  · exact continuous_apply l

#print axioms continuous_stepOn

/-- **The smearing step at a link reads only near links.**

DERIVED: `0` names the upper side. -/
theorem stepConf_local (B : BlockStep G) (μ : Fin 4) (x : ISite) {U U' : IConf G}
    (h : ∀ ν y, Near y x → U (ν, y) = U' (ν, y)) : stepConf B U (μ, x) = stepConf B U' (μ, x) := by
  have hS : ∀ p : Fin 3 × Fin 2, stapleG U μ x p = stapleG U' μ x p := by
    intro p
    have hne := other_ne μ p.1
    unfold stapleG
    split_ifs
    · rw [h _ _ (near_self x), h _ _ (near_ishift _ x), h _ _ (near_ishift _ x)]
    · rw [h _ _ (near_iback _ x), h _ _ (near_iback _ x), h _ _ (near_ishift_iback hne x)]
  simp only [stepConf]
  rw [h _ _ (near_self x)]
  congr 1
  funext i
  exact hS _

#print axioms stepConf_local

/-- **Agreement is preserved by the localised step** on any set containing `S` and every link near it.

DERIVED: no numeral. -/
theorem stepOn_agree (B : BlockStep G) {S A : Set ILink}
    (hSA : ∀ l ∈ S, ∀ ν y, Near y l.2 → (ν, y) ∈ A) {U U' : IConf G}
    (h : ∀ l ∈ A, U l = U' l) : ∀ l ∈ A, stepOn B S U l = stepOn B S U' l := by
  classical
  intro l hl
  simp only [stepOn]
  split_ifs with hS
  · obtain ⟨μ, x⟩ := l
    exact stepConf_local B μ x (fun ν y hy => h _ (hSA _ hS ν y hy))
  · exact h l hl

#print axioms stepOn_agree

/-- Agreement is preserved by any number of localised steps.

DERIVED: `0` is the base of the induction. -/
theorem stepOnIter_agree (B : BlockStep G) {S A : Set ILink}
    (hSA : ∀ l ∈ S, ∀ ν y, Near y l.2 → (ν, y) ∈ A) (n : ℕ) {U U' : IConf G}
    (h : ∀ l ∈ A, U l = U' l) : ∀ l ∈ A, (stepOn B S)^[n] U l = (stepOn B S)^[n] U' l := by
  induction n generalizing U U' with
  | zero => exact h
  | succ n ih =>
    intro l hl
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (stepOn_agree B hSA h) l hl

#print axioms stepOnIter_agree

omit [TopologicalSpace G] in
/-- **Staples of the reflected configuration at a link not along `τ`**: the original staples at the
reflected site, sides swapped for the `τ` direction.

DERIVED: `0` the reflection constant; `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
theorem stapleG_refl_ne {τ μ : Fin 4} (hμ : μ ≠ τ) (U : IConf G) (x : ISite) (p : Fin 3 × Fin 2) :
    stapleG (ireflConf τ 0 U) μ x p = stapleG U μ (ireflSite τ 0 x) (sideSwap μ τ p) := by
  obtain ⟨j, sd⟩ := p
  have Rμ : ∀ z, ireflConf τ 0 U (μ, z) = U (μ, ireflSite τ 0 z) := by
    intro z; simp [ireflConf, ireflLink, hμ]
  have Rτ : ∀ z, ireflConf τ 0 U (τ, z) = (U (τ, iback τ (ireflSite τ 0 z)))⁻¹ := by
    intro z; simp [ireflConf, ireflLink, refl_pred_neg]
  obtain rfl | rfl : sd = 0 ∨ sd = 1 := by fin_cases sd <;> simp
  · by_cases hν : other μ j = τ
    · simp only [stapleG, sideSwap, hν, if_true, Equiv.swap_apply_left, Rμ, Rτ, inv_inv,
        refl_ishift_eq, refl_ishift_ne hμ]
      simp [← ishift_iback_comm]
    · have Rν : ∀ z, ireflConf τ 0 U (other μ j, z) = U (other μ j, ireflSite τ 0 z) := by
        intro z; simp [ireflConf, ireflLink, hν]
      simp [stapleG, sideSwap, hν, Rμ, Rν, refl_ishift_ne hν, refl_ishift_ne hμ]
  · by_cases hν : other μ j = τ
    · simp only [stapleG, sideSwap, hν, if_true, Equiv.swap_apply_right, Rμ, Rτ, inv_inv,
        refl_iback_eq, refl_ishift_ne hμ]
      simp [← ishift_iback_comm, ishift_iback]
    · have Rν : ∀ z, ireflConf τ 0 U (other μ j, z) = U (other μ j, ireflSite τ 0 z) := by
        intro z; simp [ireflConf, ireflLink, hν]
      simp [stapleG, sideSwap, hν, Rμ, Rν, refl_iback_ne hν, refl_ishift_ne hμ]

#print axioms stapleG_refl_ne

omit [TopologicalSpace G] in
/-- **Staples of the reflected configuration at a `τ`-link**: the inverses of the original staples at
the reflected link, side for side.

DERIVED: `0` the reflection constant; `3 = 4 − 1` the transverse directions. -/
theorem stapleG_refl_eq (τ : Fin 4) (U : IConf G) (x : ISite) (p : Fin 3 × Fin 2) :
    stapleG (ireflConf τ 0 U) τ x p = (stapleG U τ (ireflSite τ (0 - 1) x) p)⁻¹ := by
  obtain ⟨j, sd⟩ := p
  have hν : other τ j ≠ τ := Fin.succAbove_ne τ j
  have Rτ : ∀ z, ireflConf τ 0 U (τ, z) = (U (τ, iback τ (ireflSite τ 0 z)))⁻¹ := by
    intro z; simp [ireflConf, ireflLink, refl_pred_neg]
  have Rν : ∀ z, ireflConf τ 0 U (other τ j, z) = U (other τ j, ireflSite τ 0 z) := by
    intro z; simp [ireflConf, ireflLink, hν]
  obtain rfl | rfl : sd = 0 ∨ sd = 1 := by fin_cases sd <;> simp
  · simp [stapleG, Rτ, Rν, refl_pred_neg, refl_ishift_ne hν, refl_ishift_eq, mul_inv_rev,
      ishift_iback, ishift_iback_comm, mul_assoc]
  · simp [stapleG, Rτ, Rν, refl_pred_neg, refl_iback_ne hν, refl_ishift_eq, mul_inv_rev,
      ishift_iback, ishift_iback_comm, iback_comm, mul_assoc]

#print axioms stapleG_refl_eq

/-- **The smearing step commutes with the time reflection.**

DERIVED: `0` is the reflection constant. -/
theorem stepConf_refl (B : BlockStep G) (τ : Fin 4) (U : IConf G) :
    stepConf B (ireflConf τ 0 U) = ireflConf τ 0 (stepConf B U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = τ
  · subst hμ
    have hS : (fun i => stapleG (ireflConf μ 0 U) μ x (finProdFinEquiv.symm i))
        = fun i => (stapleG U μ (ireflSite μ (0 - 1) x) (finProdFinEquiv.symm i))⁻¹ :=
      funext (fun i => stapleG_refl_eq μ U x _)
    have hW : ireflConf μ 0 U (μ, x) = (U (μ, ireflSite μ (0 - 1) x))⁻¹ := by
      simp only [ireflConf, ireflLink, if_true]
    have hR : ireflConf μ 0 (stepConf B U) (μ, x) = (stepConf B U (μ, ireflSite μ (0 - 1) x))⁻¹ := by
      simp only [ireflConf, ireflLink, if_true]
    show B.step (ireflConf μ 0 U (μ, x))
        (fun i => stapleG (ireflConf μ 0 U) μ x (finProdFinEquiv.symm i)) = _
    rw [hS, hW, hR, B.inv]
    rfl
  · have hS : (fun i => stapleG (ireflConf τ 0 U) μ x (finProdFinEquiv.symm i))
        = (fun i => stapleG U μ (ireflSite τ 0 x) (finProdFinEquiv.symm i)) ∘ stapleSwap μ τ := by
      funext i
      simp only [Function.comp, stapleSwap, Equiv.trans_apply, Equiv.symm_apply_apply,
        Function.Involutive.coe_toPerm]
      exact stapleG_refl_ne hμ U x _
    have hW : ireflConf τ 0 U (μ, x) = U (μ, ireflSite τ 0 x) := by
      simp only [ireflConf, ireflLink, hμ, if_false]
    have hR : ireflConf τ 0 (stepConf B U) (μ, x) = stepConf B U (μ, ireflSite τ 0 x) := by
      simp only [ireflConf, ireflLink, hμ, if_false]
    show B.step (ireflConf τ 0 U (μ, x))
        (fun i => stapleG (ireflConf τ 0 U) μ x (finProdFinEquiv.symm i)) = _
    rw [hS, hW, hR, B.perm]
    rfl

#print axioms stepConf_refl

/-- **The localised step commutes with the reflection**, the box reflected with it.

DERIVED: `0` the reflection constant. -/
theorem stepOn_refl (B : BlockStep G) (τ : Fin 4) (S : Set ILink) (U : IConf G) :
    stepOn B S (ireflConf τ 0 U) = ireflConf τ 0 (stepOn B {l | ireflLink τ 0 l ∈ S} U) := by
  classical
  funext l
  have key := congrFun (stepConf_refl B τ U) l
  have hinv := ireflLink_involutive τ 0 l
  simp only [stepOn, ireflConf, Set.mem_setOf_eq, hinv] at key ⊢
  split_ifs <;> simp_all

#print axioms stepOn_refl

/-- Iterates of the localised step commute with the reflection.

DERIVED: `0` is the base of the induction and the reflection constant. -/
theorem stepOnIter_refl (B : BlockStep G) (τ : Fin 4) (S : Set ILink) (n : ℕ) (U : IConf G) :
    (stepOn B S)^[n] (ireflConf τ 0 U)
      = ireflConf τ 0 ((stepOn B {l | ireflLink τ 0 l ∈ S})^[n] U) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepOn_refl, ih]

#print axioms stepOnIter_refl

/-- **The observer flow**: `n` smearing steps inside the midpoint box of half-width `R` around each
output link.

DERIVED: no numeral. -/
def obsFlowG (B : BlockStep G) (n R : ℕ) (U : IConf G) : IConf G :=
  fun l => (stepOn B (mbox l R))^[n] U l

/-- **The observer flow commutes with the time reflection.**

DERIVED: `0` the reflection constant. -/
theorem obsFlowG_refl (B : BlockStep G) (n R : ℕ) (τ : Fin 4) (U : IConf G) :
    obsFlowG B n R (ireflConf τ 0 U) = ireflConf τ 0 (obsFlowG B n R U) := by
  funext l
  have hset : {l' | ireflLink τ 0 l' ∈ mbox l R} = mbox (ireflLink τ 0 l) R := by
    ext l'; exact mem_mbox_refl τ l l' R
  show (stepOn B (mbox l R))^[n] (ireflConf τ 0 U) l = ireflConf τ 0 (obsFlowG B n R U) l
  rw [stepOnIter_refl, hset]
  simp only [ireflConf, obsFlowG]

#print axioms obsFlowG_refl

/-- **The observer flow is gauge covariant.**

DERIVED: no numeral. -/
theorem obsFlowG_gauge (B : BlockStep G) (n R : ℕ) (g : ISite → G) (U : IConf G) :
    obsFlowG B n R (igaugeTransform g U) = igaugeTransform g (obsFlowG B n R U) := by
  funext l
  simp only [obsFlowG]
  rw [stepOnIter_gauge]
  rfl

#print axioms obsFlowG_gauge

/-- **The observer flow is continuous.**

DERIVED: no numeral. -/
theorem continuous_obsFlowG [IsTopologicalGroup G] (B : BlockStep G) (n R : ℕ) : Continuous (obsFlowG B n R) :=
  continuous_pi (fun l => (continuous_apply l).comp ((continuous_stepOn B _).iterate n))

#print axioms continuous_obsFlowG

/-- **The observer flow reads only the box of half-width `R + 2`**, whatever the number of steps.

DERIVED: `2` is the widening. -/
theorem obsFlowG_local (B : BlockStep G) (n R : ℕ) (l : ILink) {U U' : IConf G}
    (h : ∀ l' ∈ mbox l (R + 2), U l' = U' l') : obsFlowG B n R U l = obsFlowG B n R U' l := by
  have hl : l ∈ mbox l (R + 2) := fun i => by constructor <;> omega
  exact stepOnIter_agree B (mbox_near l R) n h l hl

#print axioms obsFlowG_local

end Flow

/-- **The observer as a configuration flow for `SU(N)`**: at step `k`, `n k` block steps inside
midpoint boxes of half-width `R k`; range `R k + 3`.

DERIVED: `3` the range beyond the box. -/
def obsConfFlowN {N : ℕ} (B : BlockStep (SU N)) (n R : ℕ → ℕ) :
    MassGap.ContinuumFlow.ConfFlow N where
  V k := obsFlowG B (n k) (R k)
  continuous_V k := continuous_obsFlowG B (n k) (R k)
  gauge k g U := obsFlowG_gauge B (n k) (R k) g U
  refl k τ U := obsFlowG_refl B (n k) (R k) τ U
  range k := R k + 3
  local_V k l := ⟨baseBox l.2 (R k + 3), fun l' hl' i => by
      rw [mem_baseBox] at hl'
      have := hl' i
      rw [abs_le]
      push_cast at this ⊢
      constructor <;> omega,
    fun U U' h => obsFlowG_local B (n k) (R k) l
      (fun l' hl' => h l' (mbox_sub_baseBox l (R k) hl'))⟩

/-! ## 7. The continuum statement for any block step -/

open MassGap.FlowCapstone MassGap.ContinuumFlow MassGap.ContinuumSchwinger Filter

/-- The observer's flow.

DERIVED: no numeral. -/
abbrev obsFlowFN {N : ℕ} (B : BlockStep (SU N)) (n R : ℕ → ℕ) : Flow N :=
  Flow.ofConf (obsConfFlowN B n R)

/-- The observer's range at step `k` is `R k + 3`; a physical bound on it is `Flow.PhysRange`.

DERIVED: `3` the range beyond the box. -/
theorem physRange_ofN {N : ℕ} (B : BlockStep (SU N)) (n R : ℕ → ℕ) {r : ℝ}
    (h : ∀ᶠ k in atTop, dySpacing N k * ((R k + 3 : ℕ) : ℝ) ≤ r) : (obsFlowFN B n R).PhysRange r := h

#print axioms physRange_ofN

/-- **The smeared `SU(N)` observer's continuum statement**, for any block step. For the localised
observer whose range has a physical bound `r`, the observer's absolute clustering at a window `L > 0`
and one non-zero connected pairing of its view give, at every dyadic step, the flowed transfer gapped
at physical rate `c'/L` on a space with a non-zero vector orthogonal to the vacuum.

DERIVED: `0` the excluded rank and the lower end of `L` and `c'`. -/
theorem observer_clayN {N : ℕ} (hN : N ≠ 0) (B : BlockStep (SU N)) (n R : ℕ → ℕ)
    (τ : Fin 4) {r : ℝ} (hphys : (obsFlowFN B n R).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hcl : FlowClusterAbs hN (obsFlowFN B n R) τ r L)
    (hNT : FlowConnectedNonzero hN (obsFlowFN B n R) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer hN (obsFlowFN B n R)
            (uniformBoundF_of_bounded hN _ (Flow.ofConf_bounded _)) τ
            (Flow.posPreserving_of_physRange hN _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing N m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer hN (obsFlowFN B n R)
            (uniformBoundF_of_bounded hN _ (Flow.ofConf_bounded _)) τ
            (Flow.posPreserving_of_physRange hN _ hphys τ) m) :=
  flow_clay_of_bounded_abs_cluster hN (obsFlowFN B n R) (Flow.ofConf_bounded _) τ
    (Flow.posPreserving_of_physRange hN _ hphys τ) hL hcl hNT

#print axioms observer_clayN

/-! ## 8. The `SU(N)` family -/

/-- **The `SU(N)` family** (`N ≥ 2`): `⌊(s/a_k)²⌋₊` block steps of `sunBlockStep` in boxes of half-width
`⌊s/a_k⌋₊`, built like `FlowZero.apeFam`.

DERIVED: `2` the least rank and the square; `12` as in `det_blockMatN_mem_slitPlane`. -/
def sunFam {N : ℕ} (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (s : ℝ) : ConfFlow N :=
  obsConfFlowN (sunBlockStep hN c hc0 hc) (fun k => ⌊(s / dySpacing N k) ^ 2⌋₊)
    (fun k => ⌊s / dySpacing N k⌋₊)

/-- **At a fixed step, a member with `0 ≤ s < a_k` is the identity** (no block step).

DERIVED: `0` the step count; `1` the floor threshold and the least `N` of the spacing; `2` the
square; `12` as in `det_blockMatN_mem_slitPlane`. -/
theorem sunFam_V_of_lt {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s : ℝ} {k : ℕ} (hs0 : 0 ≤ s)
    (hs : s < dySpacing N k) : (sunFam hN c hc0 hc s).V k = id := by
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have h1 : s / dySpacing N k < 1 := (div_lt_one ha).mpr hs
  have h0 : 0 ≤ s / dySpacing N k := div_nonneg hs0 ha.le
  have hn : ⌊(s / dySpacing N k) ^ 2⌋₊ = 0 := Nat.floor_eq_zero.mpr (by nlinarith)
  funext U
  show obsFlowG (sunBlockStep hN c hc0 hc) ⌊(s / dySpacing N k) ^ 2⌋₊ ⌊s / dySpacing N k⌋₊ U = U
  rw [hn]
  rfl

#print axioms sunFam_V_of_lt

/-- **`PhysRange r` of the member's observer flow `Φ0` at every `r > s ≥ 0`**: the reach is
`a_k (⌊s/a_k⌋₊ + 3) ≤ s + 3 a_k`.

DERIVED: `3` the range beyond the box; `1` the least `N` of the spacing; `12` as in
`det_blockMatN_mem_slitPlane`. -/
theorem sunFam_physRange {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s r : ℝ} (hs0 : 0 ≤ s) (hr : s < r) :
    (MassGap.CompositeLink.Φ0 (sunFam hN c hc0 hc s)).PhysRange r := by
  have hev : ∀ᶠ k in atTop, dySpacing N k < (r - s) / 3 :=
    (tendsto_dySpacing N).eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hev] with k hk
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hfl : (⌊s / dySpacing N k⌋₊ : ℝ) ≤ s / dySpacing N k := Nat.floor_le (div_nonneg hs0 ha.le)
  show dySpacing N k * (((⌊s / dySpacing N k⌋₊ + 3 : ℕ)) : ℝ) ≤ r
  push_cast
  have e : dySpacing N k * (s / dySpacing N k) = s := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfl ha.le]

#print axioms sunFam_physRange

open scoped Topology in
/-- **At each fixed step the member is eventually the identity as `s → 0⁺`.**

DERIVED: `0` the limit; `1` the least `N` of the spacing; `12` as in `det_blockMatN_mem_slitPlane`. -/
theorem sunFam_eventually_id {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (k : ℕ) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ), (sunFam hN c hc0 hc s).V k = (ConfFlow.identity N).V k := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (dySpacing_pos (by omega : 1 ≤ N) k))] with s hs0 hs
  exact sunFam_V_of_lt hN hc0 hc (Set.mem_Ici.mp hs0) hs

#print axioms sunFam_eventually_id

end MassGap.ObserverFlowSUN
