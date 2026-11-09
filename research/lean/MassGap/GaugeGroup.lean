import Mathlib

/-!
# MassGap.GaugeGroup — the lattice gauge group as an interface

The lattice layer of the tree reads the gauge group through a small number of facts: a compact
topological group with a Borel probability Haar measure, and a plaquette density
`1 − Re tr ρ(g) / d` for a faithful continuous unitary representation `ρ : G → U(d)`. Everything
else is lattice combinatorics, already stated for an arbitrary group `G`
(`LatticeGauge.System`, `WilsonLattice.wilsonSystem`, `GibbsSpec.spec`, `CompactGauge.probHaar`).
`GaugeGroup G` packages those facts once, so that a statement proved at `SU(N)` through them is
stated again with `SU N` replaced by `G`.

## The interface

* `GaugeGroup G`: over a group with a topology and a measurable structure, the Prop mixins the
  lattice layer uses (topological group, compact, Borel, second countable, nonempty) and the
  data of one faithful continuous unitary representation `rep : G →* U(repDim)`, `repDim > 0`.
  The mixins are fields, not parameters, and are re-exported as instances; all are Props, so an
  instance at a type that already carries them (such as `SU N`) adds no diamond.
* `GaugeSimple G`: the constants of the simple Lie algebra of `G` that the running coupling reads,
  in the normalisation where long roots have squared length two: `lieDim = dim 𝔤`,
  `dualCoxeter = h^∨ = C₂(adj)`, and `dynkinIndex = T(ρ)` of the representation in the
  plaquette density (`tr ρ(X)ρ(Y) = T(ρ) · ⟨X, Y⟩`). In that normalisation `SU(N)` has
  `C₂(adj) = N` and `T(fund) = 1/2`. The tree has no Lie algebra of `G`, so these are entered per
  instance from the classification and are not derived from `G` here; `GaugeSimple` is declared
  only at groups whose Lie algebra is simple.

## The Wilson density

`wilsonDensityG G g = 1 − (1/d) Re tr ρ(g)`. The five facts the lattice layer consumes
(`_one`, `_conj`, `_nonneg`, `_le_two`, measurability) hold for every `GaugeGroup`, with the same
proofs as at `SU(N)`: each entry of a unitary matrix has norm at most one
(`unitary_entry_norm_le_one`, over any `RCLike` field and any finite index type).

## Compactness of `U(ι)`

`isCompact_unitaryGroup`: the unitary group of `ι × ι` matrices over an `RCLike` field is compact,
closed by `isClosed_unitary` and inside the product of closed unit balls. Every instance built in
`GaugeInstances` is compact through it.
-/

namespace MassGap

open Matrix MeasureTheory

/-! ## Unitary matrices -/

namespace GaugeGroup

/-- Every entry of a unitary matrix over an `RCLike` field has norm at most one. The `(j, j)` entry of
`star M * M = 1` reads `∑ₖ ‖M k j‖² = 1`, and one term is at most the sum.

DERIVED: the `1` is the diagonal entry of the identity matrix. -/
theorem unitary_entry_norm_le_one {ι 𝕜 : Type} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    {M : Matrix ι ι 𝕜} (hM : M ∈ Matrix.unitaryGroup ι 𝕜) (i j : ι) : ‖M i j‖ ≤ 1 := by
  have hMM : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  have h1 : ∑ k, (star M) j k * M k j = (1 : 𝕜) := by
    have h0 : (star M * M) j j = (1 : Matrix ι ι 𝕜) j j := by rw [hMM]
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h0
  have hsum : ((∑ k, ‖M k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [RCLike.ofReal_sum, ← h1]
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

/-- The unitary group of `ι × ι` matrices over an `RCLike` field is compact: closed
(`isClosed_unitary`) and contained in the product of closed unit balls, by
`unitary_entry_norm_le_one`.

DERIVED: the radius `1` is `unitary_entry_norm_le_one`'s bound. -/
theorem isCompact_unitaryGroup (ι 𝕜 : Type) [Fintype ι] [DecidableEq ι] [RCLike 𝕜] :
    IsCompact (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by
  have hclosed : IsClosed (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := isClosed_unitary
  have hK : IsCompact {M : Matrix ι ι 𝕜 | ∀ i j, M i j ∈ Metric.closedBall (0 : 𝕜) 1} := by
    have hpi : {M : Matrix ι ι 𝕜 | ∀ i j, M i j ∈ Metric.closedBall (0 : 𝕜) 1}
        = Set.univ.pi (fun _ : ι => Set.univ.pi (fun _ : ι => Metric.closedBall (0 : 𝕜) 1)) := by
      ext M
      constructor
      · intro h i _ j _; exact h i j
      · intro h i j; exact h i (Set.mem_univ i) j (Set.mem_univ j)
    rw [hpi]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  refine hK.of_isClosed_subset hclosed ?_
  intro M hM i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact unitary_entry_norm_le_one hM i j

instance compactSpace_unitaryGroup (ι 𝕜 : Type) [Fintype ι] [DecidableEq ι] [RCLike 𝕜] :
    CompactSpace (Matrix.unitaryGroup ι 𝕜) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup ι 𝕜)

/-- `|Re tr M| ≤ card ι` for a unitary `M`: each diagonal entry has real part of absolute value at
most its norm, which is at most one.

DERIVED: the bound is the number of diagonal entries. -/
theorem abs_re_trace_le_card {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) : |(Matrix.trace M).re| ≤ (Fintype.card ι : ℝ) := by
  have hentry : ∀ i, |(M i i).re| ≤ 1 := fun i =>
    le_trans (Complex.abs_re_le_norm _) (unitary_entry_norm_le_one hM i i)
  have htr : (Matrix.trace M).re = ∑ i, (M i i).re := by
    rw [show Matrix.trace M = ∑ i, M i i from rfl, Complex.re_sum]
  rw [htr]
  calc |∑ i, (M i i).re| ≤ ∑ i, |(M i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hentry i)
    _ = (Fintype.card ι : ℝ) := by simp

end GaugeGroup

/-! ## The interface -/

/-- A lattice gauge group: a compact, second-countable, Borel topological group `G` with one faithful
continuous unitary representation `rep : G →* U(repDim)`, `repDim > 0`. The plaquette density built
from it is `wilsonDensityG`. Connectedness and simplicity are not fields: no lattice statement of the
tree reads them; the constants that depend on simplicity are in `GaugeSimple`.

DERIVED: the `0` of `repDim_pos` excludes the empty representation, at which `1/d` is `0`. -/
class GaugeGroup (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] where
  isTopologicalGroup : IsTopologicalGroup G
  compactSpace : CompactSpace G
  borelSpace : BorelSpace G
  secondCountable : SecondCountableTopology G
  nonempty : Nonempty G
  /-- The dimension `d` of the representation in the plaquette density. -/
  repDim : ℕ
  repDim_pos : 0 < repDim
  /-- The representation `ρ : G →* U(d)`. -/
  rep : G →* Matrix.unitaryGroup (Fin repDim) ℂ
  continuous_rep :
    Continuous (fun g : G => ((rep g : Matrix.unitaryGroup (Fin repDim) ℂ) :
      Matrix (Fin repDim) (Fin repDim) ℂ))
  rep_injective : Function.Injective rep

attribute [instance] GaugeGroup.isTopologicalGroup GaugeGroup.compactSpace GaugeGroup.borelSpace
  GaugeGroup.secondCountable GaugeGroup.nonempty

/-- The constants of the simple Lie algebra `𝔤` of `G` that the two-loop running reads, normalised
so that long roots have squared length two: `lieDim = dim 𝔤`, `dualCoxeter = h^∨ = C₂(adj)`, and
`dynkinIndex = T(ρ)` for the representation of `GaugeGroup.rep`. At `SU(N)`: `N² − 1`, `N`, `1/2`.
These are entered per instance from the classification; nothing in the tree derives them from `G`.

DERIVED: the two `0`s are the positivity every simple Lie algebra has. -/
class GaugeSimple (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeGroup G] where
  lieDim : ℕ
  dualCoxeter : ℕ
  dynkinIndex : ℝ
  dualCoxeter_pos : 0 < dualCoxeter
  dynkinIndex_pos : 0 < dynkinIndex

namespace GaugeGroup

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The dimension of the plaquette representation, with `G` explicit.

DERIVED: no numeral. -/
abbrev dim : ℕ := GaugeGroup.repDim (G := G)

/-- The representation as a matrix-valued map. -/
abbrev repM (g : G) : Matrix (Fin (dim G)) (Fin (dim G)) ℂ :=
  ((GaugeGroup.rep g : Matrix.unitaryGroup (Fin (dim G)) ℂ) : Matrix (Fin (dim G)) (Fin (dim G)) ℂ)

variable {G}

theorem repM_mul (g h : G) : repM G (g * h) = repM G g * repM G h := by
  unfold repM
  rw [map_mul, Submonoid.coe_mul]

theorem repM_one : repM G 1 = 1 := by
  unfold repM
  rw [map_one]
  exact Submonoid.coe_one _

theorem repM_mem (g : G) : repM G g ∈ Matrix.unitaryGroup (Fin (dim G)) ℂ :=
  (GaugeGroup.rep g).2

theorem continuous_repM : Continuous (repM G) := GaugeGroup.continuous_rep

theorem repM_injective : Function.Injective (repM G) := fun _ _ h =>
  GaugeGroup.rep_injective (Subtype.ext h)

/-! ## The Wilson density -/

variable (G)

/-- The Wilson plaquette density of `g ∈ G` in the representation `rep`:
`1 − (1/d) · Re tr ρ(g)`.

DERIVED: the leading `1` normalises the identity holonomy to cost nothing (`Re tr 1 = d`). -/
noncomputable def wilsonDensityG (g : G) : ℝ :=
  1 - (1 / (dim G : ℝ)) * (Matrix.trace (repM G g)).re

variable {G}

theorem dim_pos : 0 < dim G := GaugeGroup.repDim_pos

theorem abs_re_trace_repM_le (g : G) : |(Matrix.trace (repM G g)).re| ≤ (dim G : ℝ) := by
  have h := abs_re_trace_le_card (repM_mem g)
  rwa [Fintype.card_fin] at h

/-- `wilsonDensityG G 1 = 0`.

DERIVED: `Re tr 1 = d` and `d ≠ 0`. -/
theorem wilsonDensityG_one : wilsonDensityG G 1 = 0 := by
  have hd : (dim G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (dim_pos (G := G)).ne'
  unfold wilsonDensityG
  rw [repM_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, one_div,
    inv_mul_cancel₀ hd, sub_self]

/-- `wilsonDensityG` is a class function: `φ(h g h⁻¹) = φ(g)`, by trace cyclicity.

DERIVED: no numeral. -/
theorem wilsonDensityG_conj (h g : G) : wilsonDensityG G (h * g * h⁻¹) = wilsonDensityG G g := by
  have hinv : repM G h⁻¹ * repM G h = 1 := by rw [← repM_mul, inv_mul_cancel, repM_one]
  have key : Matrix.trace (repM G (h * g * h⁻¹)) = Matrix.trace (repM G g) := by
    rw [repM_mul, repM_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  unfold wilsonDensityG
  rw [key]

/-- `wilsonDensityG` is invariant under inversion: `Re tr ρ(g⁻¹) = Re tr ρ(g)^* = Re tr ρ(g)`.

DERIVED: no numeral. -/
theorem wilsonDensityG_inv (g : G) : wilsonDensityG G g⁻¹ = wilsonDensityG G g := by
  have hstar : repM G g⁻¹ = star (repM G g) := by
    have h1 : repM G g⁻¹ * repM G g = 1 := by rw [← repM_mul, inv_mul_cancel, repM_one]
    have h2 : star (repM G g) * repM G g = 1 := Matrix.mem_unitaryGroup_iff'.mp (repM_mem g)
    have hu : repM G g * star (repM G g) = 1 := Matrix.mem_unitaryGroup_iff.mp (repM_mem g)
    calc repM G g⁻¹ = repM G g⁻¹ * (repM G g * star (repM G g)) := by rw [hu, Matrix.mul_one]
      _ = (repM G g⁻¹ * repM G g) * star (repM G g) := by rw [Matrix.mul_assoc]
      _ = star (repM G g) := by rw [h1, Matrix.one_mul]
  have htr : (Matrix.trace (repM G g⁻¹)).re = (Matrix.trace (repM G g)).re := by
    rw [hstar, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def,
      Complex.conj_re]
  unfold wilsonDensityG
  rw [htr]

theorem wilsonDensityG_nonneg (g : G) : 0 ≤ wilsonDensityG G g := by
  have hpos : (0 : ℝ) < dim G := Nat.cast_pos.mpr dim_pos
  have hle : (Matrix.trace (repM G g)).re ≤ dim G := (abs_le.mp (abs_re_trace_repM_le g)).2
  unfold wilsonDensityG
  rw [sub_nonneg, div_mul_eq_mul_div, one_mul, div_le_one hpos]
  exact hle

/-- `wilsonDensityG ≤ 2`.

DERIVED: `2 = 1 − (−1)`, the extreme `Re tr ρ(g) = −d`. -/
theorem wilsonDensityG_le_two (g : G) : wilsonDensityG G g ≤ 2 := by
  have hpos : (0 : ℝ) < dim G := Nat.cast_pos.mpr dim_pos
  have hge : -(dim G : ℝ) ≤ (Matrix.trace (repM G g)).re := (abs_le.mp (abs_re_trace_repM_le g)).1
  have hbd : -1 ≤ (1 / (dim G : ℝ)) * (Matrix.trace (repM G g)).re := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos, neg_one_mul]
    exact hge
  unfold wilsonDensityG
  linarith [hbd]

theorem continuous_wilsonDensityG : Continuous (wilsonDensityG G) := by
  unfold wilsonDensityG
  exact continuous_const.sub (continuous_const.mul
    (Complex.continuous_re.comp (continuous_repM.matrix_trace)))

theorem measurable_wilsonDensityG [OpensMeasurableSpace G] : Measurable (wilsonDensityG G) :=
  continuous_wilsonDensityG.measurable

/-- `wilsonDensityG` vanishes exactly at the kernel of the representation, hence, `rep` being
faithful, exactly at the identity: `Re tr U = d` for a unitary `U` forces `U = 1`.
This is the statement that the Wilson action has the identity as its unique minimum, for every
`GaugeGroup`, and it is the place faithfulness is used.

DERIVED: no numeral beyond the `0` of the density's minimum. -/
theorem wilsonDensityG_eq_zero_iff (g : G) : wilsonDensityG G g = 0 ↔ g = 1 := by
  constructor
  · intro h0
    have hd : (0 : ℝ) < dim G := Nat.cast_pos.mpr dim_pos
    set M := repM G g with hMdef
    have hd' : (dim G : ℝ) ≠ 0 := hd.ne'
    have hre : (Matrix.trace M).re = dim G := by
      unfold wilsonDensityG at h0
      rw [← hMdef] at h0
      have h1 : (1 / (dim G : ℝ)) * (Matrix.trace M).re = 1 := by linarith
      calc (Matrix.trace M).re = (dim G : ℝ) * ((1 / (dim G : ℝ)) * (Matrix.trace M).re) := by
            field_simp
        _ = dim G := by rw [h1, mul_one]
    -- every diagonal entry has real part one
    have hentry : ∀ i, (M i i).re ≤ 1 := fun i =>
      le_trans (le_abs_self _)
        (le_trans (Complex.abs_re_le_norm _) (unitary_entry_norm_le_one (repM_mem g) i i))
    have hsum : ∑ i, (M i i).re = ∑ _i : Fin (dim G), (1 : ℝ) := by
      rw [show ∑ i, (M i i).re = (Matrix.trace M).re by
        rw [show Matrix.trace M = ∑ i, M i i from rfl, Complex.re_sum], hre]
      simp
    have hdiag1 : ∀ i, (M i i).re = 1 := by
      intro i
      have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hentry i)).mp hsum i (Finset.mem_univ i)
      exact this
    -- column `i` has squared norms summing to one, and `‖M i i‖ ≥ Re M i i = 1`
    have hcol : ∀ j, ∑ k, ‖M k j‖ ^ 2 = 1 := by
      intro j
      have hMM : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp (repM_mem g)
      have h1 : ∑ k, (star M) j k * M k j = (1 : ℂ) := by
        have h0' : (star M * M) j j = (1 : Matrix (Fin (dim G)) (Fin (dim G)) ℂ) j j := by
          rw [hMM]
        rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h0'
      have hs : ((∑ k, ‖M k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_sum, ← h1]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ← starRingEnd_apply,
          RCLike.conj_mul]
        norm_cast
      exact_mod_cast hs
    have hdiagEq : ∀ i, M i i = 1 := by
      intro i
      have hn : ‖M i i‖ ≤ 1 := unitary_entry_norm_le_one (repM_mem g) i i
      have hre1 := hdiag1 i
      have hsq : (M i i).re ^ 2 + (M i i).im ^ 2 = ‖M i i‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have him : (M i i).im = 0 := by
        have hn2 : ‖M i i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (M i i)]
        have him2 : (M i i).im ^ 2 ≤ 0 := by rw [hre1] at hsq; nlinarith
        exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm him2 (sq_nonneg _))
      exact Complex.ext (by simpa using hre1) (by simpa using him)
    have hoff : ∀ k j, k ≠ j → M k j = 0 := by
      intro k j hkj
      have hc := hcol j
      have hjj : ‖M j j‖ ^ 2 = 1 := by rw [hdiagEq j]; simp
      have hrest : ∑ k ∈ Finset.univ.erase j, ‖M k j‖ ^ 2 = 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hjj] at hc
        linarith
      have hk : ‖M k j‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hrest k
          (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hk)
    have hM1 : M = 1 := by
      ext k j
      by_cases hkj : k = j
      · subst hkj; rw [hdiagEq k, Matrix.one_apply_eq]
      · rw [hoff k j hkj, Matrix.one_apply_ne hkj]
    apply repM_injective
    rw [← hMdef, hM1, repM_one]
  · rintro rfl; exact wilsonDensityG_one

end GaugeGroup

#print axioms GaugeGroup.isCompact_unitaryGroup
#print axioms GaugeGroup.wilsonDensityG_one
#print axioms GaugeGroup.wilsonDensityG_conj
#print axioms GaugeGroup.wilsonDensityG_inv
#print axioms GaugeGroup.wilsonDensityG_nonneg
#print axioms GaugeGroup.wilsonDensityG_le_two
#print axioms GaugeGroup.measurable_wilsonDensityG
#print axioms GaugeGroup.wilsonDensityG_eq_zero_iff

end MassGap
