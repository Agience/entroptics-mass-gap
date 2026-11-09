import Mathlib
import MassGap.OneBridge
import MassGap.WilsonSlab
import MassGap.FiniteInformation

/-!
# MassGap.CellLinks — the three links of (B): cells of one physical side on the Wilson box

`UniformAperture` derives (B) from `EdgeCells`: pieces of a mean-zero reading, one per cell, with a
cell rate `ρc` and cross terms `c_ij ≤ Ke q^{d(i,j)}`. Its hypotheses fix no cells: one cell with
`c ≡ 0` satisfies them (`UniformAperture.edgeCells_of_contr`). The owner's answer to "why do cells of
the fixed length couple only through the edge cost" was three links: (1) finite information — only
what crosses a cell face passes, and the face costs `σℓ`; (2) no long edges — every long-range link
is a flux edge costing per length, with no free carrier; (3) the fixed length screens — beyond it the
substrate reads coarse. This module states each on the Wilson box of `WilsonSlab` and proves what
each gives.

## 1. The cells are fixed (sections 1–3)

* `ProjChain e n`: symmetric operators `Q 0, …, Q n` with `Q j Q i = Q i` for `i ≤ j`, `Q 0 = 0` on
  `e⊥`, `Q n = id`. `piece g i = Q (i+1) g − Q i g`. `sum_piece`: the pieces of `g ⊥ e` sum to `g`;
  `piece_orth`: they are pairwise orthogonal. `ChainGram P C ρc c` is the cell rate and the cross
  bound on these pieces; `cellGramH_of_chainGram` gives `OneBridgeSU.CellGramH`.
* `condChain S F`: on a slab `S`, `Q 0` the projection on the constants and `Q i` (`i ≥ 1`) the
  orthogonal projection of `L²(π)` on the `F i`-measurable functions (`lpMeas`), the conditional
  expectation onto the σ-algebra `F i`. For `F` monotone, below the ambient σ-algebra and equal to
  it at `n`, this is a `ProjChain`: the pieces are the martingale differences
  `E[g | F (i+1)] − E[g | F i]`.
* The Wilson box (`BoxParams`, `BoxParams.box`): the `OneBridgeSU.WilsonBox` whose transverse extents
  are `WilsonSlab.boxT μ m k`, `m 2ᵏ` sites per side, so the slab at `(m, k)` is the Doob slab of `2ᵏ`
  steps of the slice transfer of the periodic box of physical side `m a₀` at spacing `a_k = a₀/2ᵏ`.
* The cells: at level `r ≤ k` a cell is a cube of `2^{k−r}` sites per side, `cellOf_eq_iff`;
  `cellSide_phys`: its physical side is `ℓ = 2^{k−r} a_k = a₀/2ʳ`, the same at every zoom;
  `cellOf_lt`: there are `m 2ʳ` cells per side, so `cellCount_eq`: `(m 2ʳ)³` cells, fixed in `k` and
  growing with the aperture. A link `(ν, y)` belongs to the cell of its base site `y`
  (`linkCell`), so the cells cover every link of the slice. `cellEnum` lists the cells;
  `cellEnum_cover` proves that every link lies in a listed cell.
* `linkSigma A`: the σ-algebra of the links in `A`. `cellFilt i`: the links of the first `i` cells.
  `cellChain X hN r m k`: `condChain` of the box slab along `cellFilt`. Its pieces are fixed by the
  box, the level `r` and the order of `cellEnum`: nothing in it is chosen per hypothesis.
* `boxDist`: the periodic `ℓ∞` distance of two cells, in cell units (`cellDist_comm`).

So the vacuity of `EdgeCells` (one cell) does not arise here: at aperture `m` there are `(m 2ʳ)³`
cells and the pieces are their conditional martingale differences. What a hypothesis can still choose
is the coupling `c` (bounded by the cross terms of those pieces), `ρc`, and the shell constants
`(A, p)` of `ShellCount` for `boxDist`, which is a combinatorial fact taken as a hypothesis (counted
in `research/code/cell_links_checks.py`, not proved here).

The pieces are mean-zero, so any slab rate `‖P g‖ ≤ ρ ‖g‖` bounds them: `ρc` may be read as the slab
rate itself, and then the cell decomposition adds nothing; its content is that `ρc` and the cross
terms are cell-scale quantities. The order of `cellEnum` comes from `Fintype.equivFin`, a classical
choice: fixed, so no hypothesis can choose it, but not geometric. For the non-product Doob state the
pieces, and so `ρc` and `c`, depend on it.

The piece `vⱼ = E[g | cells 0..j] − E[g | cells 0..j−1]` is measurable for the links of cells
`0, …, j`, not of cell `j` alone. So decay of `⟪P vᵢ, P vⱼ⟫` in `boxDist i j` is a statement about
these martingale differences, not clustering of observables localised in cells `i` and `j`.

## 2. Link (3): the fixed length screens (section 5)

* `Screens P v d Ke ξ ℓ`: `|⟪P vᵢ, P vⱼ⟫| ≤ Ke e^{−d(i,j) ℓ/ξ} ‖vᵢ‖ ‖vⱼ‖`. With `ℓ = a₀/2ʳ` the
  physical side of a cell, `d ℓ` is the physical distance of the cells and `ξ` a screening length.
* `screen_eq`: `e^{−d ℓ/ξ} = (edgeRate (1/ξ) 0 ℓ)^d`. `cross_of_screens`: screening is the cross bound
  with `c_ij = Ke q^{d(i,j)}`, `q = edgeRate (1/ξ) 0 ℓ`, which is `FaceEdgeCost c d Ke q` with equality
  in the coefficient: (3) is the face-edge cost read as a screening length, `σ − h = 1/ξ`.
* `ScreenedCells`: the cell rate and screening for the pieces of `cellChain` at `(m, k)`.
  `edgeCellsM_of_screened`: with `ShellCount boxDist A p` it is `OneBridgeSU.EdgeCellsM` on the box
  slab. `relFloorM_of_screened`: at every `m > 0`, `k ≥ K₀ ≥ r`, one `(ρc, Ke, ξ, A, p)` and
  `ρc² + Ke A edgeSum p (edgeRate (1/ξ) 0 ℓ) < 1` give `RelFloorM` on the box slabs with one rate and
  one zoom — fields (A) and (B) of `OneBridgeData`. `oneBridge_of_screened`: with `2 ≤ N`,
  `β m k > 0` (so `ratio_pos` is `WilsonSlab.ratio_mem_box`), an observer reading and the volume link,
  `OneBridge`.
* Residual: `ξ` and `Ke` the same at every aperture and zoom. That is exponential clustering at
  the cell scale of the conditional state (the Doob state given the earlier cells) for the slab
  transfer, read on the martingale differences of the cell filtration (each depending on all
  earlier cells): a clustering-type statement at one length.

## 3. Link (1): finite information through a face (section 4)

* `chainOp A d = A_{d−1} ∘ ⋯ ∘ A_0`; `norm_chainOp_le`: `‖chainOp A d‖ ≤ ∏_{t<d} θ_t` when
  `‖A_t‖ ≤ θ_t`.
* `ShellFactor P v d θ`: for `i ≠ j` the cross term is `⟪u, chainOp A (d i j) w⟫` with `‖u‖ ≤ ‖vᵢ‖`,
  `‖w‖ ≤ ‖vⱼ‖` and `‖A_t‖ ≤ θ_t`. This is the Markov form of "only what crosses a face passes": the
  correlation of cell `i` with cell `j` is carried through the separating surfaces at radii
  `ℓ, 2ℓ, …` around cell `i`, and `θ_t` is the `L²` (maximal correlation) coefficient from surface
  `t` to surface `t+1`. For a field with a nearest-neighbour Gibbs–Markov property the
  factorisation holds (script: the bound `ρ(core, S_d) ≤ ∏ θ_t` on a Dirichlet Gaussian field).
  The state of a transfer slab is not such a field: its slice marginal (the Doob state, for the free
  field the covariance `1/(2 sinh ε)`) is non-local in the slice, and the script finds the bound
  violated on the massless slice. So `ShellFactor` is a hypothesis on the Wilson slab, not a
  consequence of the locality of the Wilson action.
* `abs_cross_of_shellFactor`: with `θ_t ≤ θ₀` the cross term is at most `θ₀^{d} ‖vᵢ‖ ‖vⱼ‖`.
  `screens_of_shellFactor`: for `θ₀ ∈ (0, 1]` that is `Screens` with `Ke = 1`,
  `ξ = ℓ / (−log θ₀)` (`pow_eq_screen`). `screened_of_shellLinked`: on the box, (1) gives (3).
* Uniformity, the photon's failure point. Two readings of "the face costs":
  - the finite-alphabet (Dobrushin/Doeblin) coefficient of `FiniteInformation` does not survive
    refinement. `prodChan K M` is `M` independent copies of a per-link channel (a face of `M` links
    read letter by letter); `prodChan_floor`, `minor_prodChan`: its Doeblin floor is
    `(|Y| ε)^M`; `floor_le_one`: `|Y| ε ≤ 1` for every channel; `faceFloor_tendsto_zero`,
    `faceArea_tendsto`: with face area `M_k = (2^{k−r})²` growing in the zoom, the floor tends to
    `0` and the coefficient bound `1 − (|Y| ε)^{M_k}` to `1`, for every field, massive or not, unless
    the per-link channel passes nothing (`|Y| ε = 1`). The finite-alphabet route through a face is
    not uniform in `a`.
  - the `L²` coefficient of a product of independent per-link channels is the largest of theirs,
    not a product (script: `BSC(p)^{⊗M}` keeps maximal correlation `|1 − 2p|` while its TV
    coefficient tends to `1`), so it is the form `ShellFactor` uses. Across a shared face it still
    degrades under refinement, for the massive field as well (script, 2D Gaussian at fixed
    physical geometry, cell side `2, 4, 8` sites: `0.61, 0.79, 0.89` massive, `0.80, 0.91, 0.96`
    massless): touching sets carry the short modes at the face. Between separating surfaces one
    cell length `ℓ` apart it is stable under refinement (spread under `0.02`). For the massless
    field it degrades instead with the radius `t` (2D, `t = 1 … 12`: `0.76 → 0.95`, and the
    correlation of the core with surface `d` falls like `d^{−0.35}`); for the massive one it settles
    (`0.38`) and the correlation falls geometrically. `not_uniform_of_tendsto_one`: a coefficient
    tending to `1` has no uniform bound `θ₀ < 1`. The residual of (1) is therefore
    `θ_t ≤ θ₀ < 1` between surfaces one cell length apart, uniformly in the radius `t`, the aperture
    and the zoom, for the slab's conditional state.

## 4. Link (2): no long edges (section 6)

* `PathSum c d Np w`: `c_ij ≤ Σ_{n ≥ d(i,j)} Np n · wⁿ` (summable): the coupling of two cells is a sum
  over flux paths of `n ≥ d` cell steps, `Np n` of them, each step costing the weight `w`.
  `faceEdgeCost_of_pathSum`: `Np n ≤ zⁿ`, `z w < 1` give `FaceEdgeCost c d (1 − z w)⁻¹ (z w)`.
  `pathRate_eq_edgeRate`: `z e^{−σℓ} = edgeRate σ (log z / ℓ) ℓ`, so `h = log z / ℓ` is the path
  entropy per length. `edgeCellsM_of_pathCells`: on the box, (2) gives `EdgeCellsM`.
* `areaWeight_eq`: an area-law weight `e^{−σlat (ℓ/a)(τ/a)}` of a flux sheet of length `ℓ` across a
  slab of thickness `τ` is `edgeRate (σlat/a² · τ) 0 ℓ`: the `σ` of `edgeRate` is the tension in
  aperture units, `EdgeCost.sigmaPhys`, times `τ`. `tension_floor_of_stringScaling`:
  `EdgeCost.StringScalingAt N σlat` gives a floor `σ₁ > 0` on `sigmaPhys σlat (aRun N)` eventually in
  `β`, which is the tension floor `relFloorM_of_edgeCost` consumes. `σlat` is still a function
  argument: no declaration defines it from Wilson-loop expectations of the measure.
* Controls: `not_summable_of_free`, `not_pathSum_of_free`: with a free carrier (`z w ≥ 1`, `Np n ≥ zⁿ`)
  the path sum diverges and `PathSum` has no instance with two cells.
* Residual: the path expansion itself — a convergent polymer/flux-path expansion of the conditional
  cross terms at the cell scale with a per-step weight `w` and entropy `z`, `z w < 1`, the same at
  every aperture and zoom. At the lattice scale such expansions converge only at strong coupling; the
  lattice character coefficient tends to `1` at weak coupling for `SU(2)`, `U(1)` and `Z_N` alike
  (script), so the weight must be a cell-scale (coarse) quantity, which is where (3) enters.

## 5. Controls (power law, section 7)

`powerLaw_beats`: for `c₀ > 0`, `q < 1`, eventually `Ke qᵈ < c₀/dᵖ`. `not_screens_of_powerLaw`: cross
terms with a power-law floor at large cell distance violate `Screens` for every `Ke`, `ξ`; the same
bound excludes `FaceEdgeCost` and a uniform `ShellFactor`. A free massless field (the 4D photon proxy)
has power-law cross terms, so it fails all three; the script exhibits `θ_t → 1` and power-law cross
terms for the massless Gaussian proxy and uniform `θ_t` for the massive one. Not formalised: 4D
`Z_N` (finite centre) has a weak-coupling phase separated by a transition (for `N ≥ 5` with a massless
photon, Fröhlich–Spencer 1982; for small `N` a gapped deconfined phase without area law,
Creutz–Jacobs–Rebbi 1979), so finite centre alone gives none of the links, and a gapped deconfined
phase can satisfy (1) and (3) with `σ = 0`: their rates are free rates, not the tension. 2D `SU(2)`
(and 2D `U(1)`): every gauge-invariant function of the slice is a class function of the holonomy, and
by Haar invariance its conditional expectation on any proper set of links is its mean, so every piece
but the last vanishes, `c ≡ 0`, and all three hold trivially (script, exact on `Z_3` and on the binary
tetrahedral subgroup of `SU(2)`).

## 6. Strength

Each link gives (B) through `EdgeCellsM`; none is proved for the Wilson measure. (3) is equivalent in
form to `FaceEdgeCost` on the realised cross terms. Formally (1) and (2) are restatements of (3):
`ShellFactor` with `θ_t ≤ θ₀` is equivalent to `Screens` at `Ke = 1`, `ξ = ℓ/(−log θ₀)` (one
direction is `screens_of_shellFactor`; conversely `A_t = θ₀ • id` with `u`, `w` rescaled realises any
cross term of size at most `θ₀^d ‖vᵢ‖ ‖vⱼ‖`, since `ShellFactor` does not tie `A_t` to conditional
expectations between surface σ-algebras); and `PathSum` with `Np n = zⁿ` is exactly
`FaceEdgeCost` at `Ke = (1 − z w)⁻¹`, `q = z w` (the sum is `(z w)^d/(1 − z w)`). The face, Markov and
flux-path mechanisms are in this docstring, not in the definitions. The residuals are a uniform
shell-to-shell `L²` coefficient, a convergent cell-scale path expansion and a uniform screening
length; all three are clustering-type statements for the conditional state at the cell scale,
uniform in the aperture and the zoom. That no combination makes (B) strictly weaker than the gap is
a finding of this module (no such reduction is found), not a theorem. The box couplings `β m k` remain free
(as in `OneBridge` section 5): no declaration ties them to a running coupling, so the content of
`OneBridge` still sits in the volume link.

DERIVED (module-wide): `0` the index of the constants in the chain, the mean of a reading and the
sign of every bound; `1` the step of a chain and of a cell index, the top of every coefficient and
the unit coupling `Ke = 1` of (1); `2` the block factor of a zoom step, the `L²` exponent and the
face dimension in `(2^{k−r})²`; `3` the number of transverse directions; `4` the spacetime dimension.
-/

noncomputable section

namespace MassGap.CellLinks

open MeasureTheory Filter Topology
open MassGap.SlabKernelOperator
open scoped BigOperators

/-! ## 1. A chain of projections -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A chain of nested symmetric projections** from the constants (`Q 0 = 0` on `e⊥`) to the
identity (`Q n = id`). -/
structure ProjChain (e : E) (n : ℕ) where
  /-- The projections. -/
  Q : ℕ → E →L[ℝ] E
  symm : ∀ i u v, inner ℝ (Q i u) v = inner ℝ u (Q i v)
  nest : ∀ i j, i ≤ j → ∀ x, Q j (Q i x) = Q i x
  first : ∀ g, inner ℝ g e = 0 → Q 0 g = 0
  last : ∀ x, Q n x = x

namespace ProjChain

variable {e : E} {n : ℕ} (C : ProjChain e n)

/-- `Q i Q j = Q i` for `i ≤ j`. -/
theorem nest' {i j : ℕ} (h : i ≤ j) (x : E) : C.Q i (C.Q j x) = C.Q i x := by
  refine ext_inner_right ℝ fun y => ?_
  rw [C.symm i (C.Q j x) y, C.symm j x (C.Q i y), C.nest i j h y, C.symm i x y]

/-- **The piece of cell `i`**: `Q (i+1) g − Q i g`. -/
def piece (g : E) (i : Fin n) : E := C.Q ((i : ℕ) + 1) g - C.Q (i : ℕ) g

/-- **The pieces of a mean-zero `g` sum to `g`.** -/
theorem sum_piece {g : E} (hg : inner ℝ g e = 0) : ∑ i, C.piece g i = g := by
  have h1 : ∑ i, C.piece g i = ∑ i ∈ Finset.range n, (C.Q (i + 1) g - C.Q i g) :=
    Fin.sum_univ_eq_sum_range (fun i => C.Q (i + 1) g - C.Q i g) n
  have h2 : ∑ i ∈ Finset.range n, (C.Q (i + 1) g - C.Q i g) = C.Q n g - C.Q 0 g :=
    Finset.sum_range_sub (fun i => C.Q i g) n
  rw [h1, h2, C.last, C.first g hg, sub_zero]

theorem Q_piece {g : E} {i : Fin n} {j : ℕ} (h : (i : ℕ) + 1 ≤ j) :
    C.Q j (C.piece g i) = C.piece g i := by
  unfold piece
  rw [map_sub, C.nest _ _ h, C.nest _ _ (by omega)]

theorem Q_piece_self (g : E) (j : Fin n) : C.Q j (C.piece g j) = 0 := by
  unfold piece
  rw [map_sub, C.nest' (Nat.le_succ _), C.nest _ _ le_rfl, sub_self]

theorem piece_orth_lt {g : E} {i j : Fin n} (h : i < j) :
    inner ℝ (C.piece g i) (C.piece g j) = 0 := by
  have hij : (i : ℕ) + 1 ≤ j := h
  rw [← C.Q_piece hij, C.symm, C.Q_piece_self, inner_zero_right]

/-- **The pieces are pairwise orthogonal.** -/
theorem piece_orth {g : E} {i j : Fin n} (h : i ≠ j) :
    inner ℝ (C.piece g i) (C.piece g j) = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · exact C.piece_orth_lt h
  · rw [real_inner_comm]
    exact C.piece_orth_lt h

end ProjChain

/-- **The cell rate and the cross bound on the pieces of a chain.** -/
def ChainGram {e : E} {n : ℕ} (P : E →L[ℝ] E) (C : ProjChain e n) (ρc : ℝ)
    (c : Fin n → Fin n → ℝ) : Prop :=
  ∀ g : E, inner ℝ g e = 0 →
    (∀ i, ‖P (C.piece g i)‖ ^ 2 ≤ ρc ^ 2 * ‖C.piece g i‖ ^ 2) ∧
    ∀ i j, i ≠ j → inner ℝ (P (C.piece g i)) (P (C.piece g j)) ^ 2
      ≤ c i j ^ 2 * ‖C.piece g i‖ ^ 2 * ‖C.piece g j‖ ^ 2

/-- **A chain with a Gram bound is a cell decomposition** in the sense of `OneBridgeSU.CellGramH`. -/
theorem cellGramH_of_chainGram {e : E} {n : ℕ} {P : E →L[ℝ] E} {C : ProjChain e n} {ρc : ℝ}
    {c : Fin n → Fin n → ℝ} (h : ChainGram P C ρc c) : OneBridgeSU.CellGramH P e ρc c :=
  fun g hg => ⟨C.piece g, (C.sum_piece hg).symm, fun _ _ hij => C.piece_orth hij, (h g hg).1,
    (h g hg).2⟩

/-- `|x| ≤ c (a b)` gives `x² ≤ c² a² b²`. -/
theorem sq_le_of_abs_le {x c a b : ℝ} (h : |x| ≤ c * (a * b)) : x ^ 2 ≤ c ^ 2 * a ^ 2 * b ^ 2 :=
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ (c * (a * b)) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2
    _ = c ^ 2 * a ^ 2 * b ^ 2 := by ring

end Chain

/-! ## 2. Conditional expectations on a slab -/

section Cond

variable (S : SlabMeasure.SlabM)

theorem oneLp_mem_lpMeas (F : ℕ → MeasurableSpace S.Ω) (i : ℕ) :
    oneLp S.π ∈ lpMeas ℝ ℝ (F i) 2 S.π := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact ⟨fun _ => (1 : ℝ), stronglyMeasurable_const, (memLp_const (1 : ℝ)).coeFn_toLp⟩

theorem lpMeas_mono (F : ℕ → MeasurableSpace S.Ω) {i j : ℕ} (h : F i ≤ F j) :
    lpMeas ℝ ℝ (F i) 2 S.π ≤ lpMeas ℝ ℝ (F j) 2 S.π := fun f hf => by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  exact hf.mono h

/-- **The conditional projections**: `Q 0` onto the constants, `Q i` (`i ≥ 1`) onto the
`F i`-measurable functions. -/
def condQ (F : ℕ → MeasurableSpace S.Ω) (hle : ∀ i, F i ≤ S.ms) :
    ℕ → (Lp ℝ 2 S.π →L[ℝ] Lp ℝ 2 S.π)
  | 0 => (ℝ ∙ oneLp S.π).starProjection
  | i + 1 =>
    haveI : Fact (F (i + 1) ≤ S.ms) := ⟨hle (i + 1)⟩
    (lpMeas ℝ ℝ (F (i + 1)) 2 S.π).starProjection

variable {S}

theorem condQ_symm (F : ℕ → MeasurableSpace S.Ω) (hle : ∀ i, F i ≤ S.ms) (i : ℕ)
    (u v : Lp ℝ 2 S.π) : inner ℝ (condQ S F hle i u) v = inner ℝ u (condQ S F hle i v) := by
  cases i with
  | zero => exact Submodule.inner_starProjection_left_eq_right (ℝ ∙ oneLp S.π) u v
  | succ i =>
    haveI : Fact (F (i + 1) ≤ S.ms) := ⟨hle (i + 1)⟩
    exact Submodule.inner_starProjection_left_eq_right (lpMeas ℝ ℝ (F (i + 1)) 2 S.π) u v

theorem condQ_nest (F : ℕ → MeasurableSpace S.Ω) (hle : ∀ i, F i ≤ S.ms) (hF : Monotone F)
    (i j : ℕ) (hij : i ≤ j) (x : Lp ℝ 2 S.π) :
    condQ S F hle j (condQ S F hle i x) = condQ S F hle i x := by
  cases j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact (Submodule.starProjection_eq_self_iff (K := ℝ ∙ oneLp S.π)).2
      (Submodule.starProjection_apply_mem _ x)
  | succ j =>
    haveI : Fact (F (j + 1) ≤ S.ms) := ⟨hle (j + 1)⟩
    refine (Submodule.starProjection_eq_self_iff (K := lpMeas ℝ ℝ (F (j + 1)) 2 S.π)).2 ?_
    cases i with
    | zero =>
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (oneLp_mem_lpMeas S F (j + 1))
        (Submodule.starProjection_apply_mem (ℝ ∙ oneLp S.π) x)
    | succ i =>
      haveI : Fact (F (i + 1) ≤ S.ms) := ⟨hle (i + 1)⟩
      exact lpMeas_mono S F (hF (by omega : i + 1 ≤ j + 1))
        (Submodule.starProjection_apply_mem (lpMeas ℝ ℝ (F (i + 1)) 2 S.π) x)

theorem condQ_first (F : ℕ → MeasurableSpace S.Ω) (hle : ∀ i, F i ≤ S.ms) (g : Lp ℝ 2 S.π)
    (hg : inner ℝ g (oneLp S.π) = 0) : condQ S F hle 0 g = 0 := by
  show (ℝ ∙ oneLp S.π).starProjection g = 0
  rw [Submodule.starProjection_singleton ℝ g, real_inner_comm, hg, zero_div, zero_smul]

theorem condQ_last (F : ℕ → MeasurableSpace S.Ω) (hle : ∀ i, F i ≤ S.ms) {n : ℕ} (hn0 : 0 < n)
    (hn : S.ms ≤ F n) (x : Lp ℝ 2 S.π) : condQ S F hle n x = x := by
  cases n with
  | zero => exact absurd hn0 (lt_irrefl 0)
  | succ n =>
    haveI : Fact (F (n + 1) ≤ S.ms) := ⟨hle (n + 1)⟩
    exact (Submodule.starProjection_eq_self_iff (K := lpMeas ℝ ℝ (F (n + 1)) 2 S.π)).2
      (mem_lpMeas_iff_aestronglyMeasurable.2 ((Lp.aestronglyMeasurable x).mono hn))

/-- **The martingale chain of a filtration** `F` on the slab: monotone, below the ambient σ-algebra,
equal to it at `n`. -/
def condChain (F : ℕ → MeasurableSpace S.Ω) (hle : ∀ i, F i ≤ S.ms) (hF : Monotone F) {n : ℕ}
    (hn0 : 0 < n) (hn : S.ms ≤ F n) : ProjChain (oneLp S.π) n where
  Q := condQ S F hle
  symm := condQ_symm F hle
  nest := condQ_nest F hle hF
  first := condQ_first F hle
  last := condQ_last F hle hn0 hn

end Cond

/-! ## 3. Cells of one physical side on the Wilson box -/

section Links

variable {L G : Type*} [MeasurableSpace G]

/-- **The σ-algebra of the links in `A`.** -/
@[reducible] def linkSigma (A : Set L) : MeasurableSpace (L → G) :=
  ⨆ l ∈ A, MeasurableSpace.comap (fun ω : L → G => ω l) ‹MeasurableSpace G›

theorem linkSigma_mono {A A' : Set L} (h : A ⊆ A') :
    (linkSigma A : MeasurableSpace (L → G)) ≤ linkSigma A' :=
  iSup₂_le fun l hl => le_iSup₂_of_le l (h hl) le_rfl

theorem linkSigma_le (A : Set L) : (linkSigma A : MeasurableSpace (L → G)) ≤ MeasurableSpace.pi :=
  iSup₂_le fun l _ =>
    le_iSup (fun a => MeasurableSpace.comap (fun b : L → G => b a) ‹MeasurableSpace G›) l

theorem pi_le_linkSigma_univ :
    (MeasurableSpace.pi : MeasurableSpace (L → G)) ≤ linkSigma Set.univ :=
  iSup_le fun l => le_iSup₂_of_le l (Set.mem_univ l) le_rfl

end Links

section Box

open MassGap.RectWilson

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- The cell of a site: its coordinates divided by the cell side `s` (in sites). -/
def cellOf (s : ℕ) (y : TT μ T) : {j : Fin 4 // j ≠ μ} → ℕ := fun j => (y j : ℕ) / s

/-- The cell of a link: the cell of its base site. -/
def linkCell (s : ℕ) (l : SpT μ T) : {j : Fin 4 // j ≠ μ} → ℕ := cellOf s l.2

theorem div_eq_iff' {s a d : ℕ} (hs : 0 < s) : a / s = d ↔ s * d ≤ a ∧ a < s * (d + 1) := by
  constructor
  · rintro rfl
    exact ⟨by rw [mul_comm]; exact Nat.div_mul_le_self a s, Nat.lt_mul_div_succ a hs⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le (by rw [mul_comm]; exact h1) (by rw [mul_comm]; exact h2)

/-- **A cell is a cube of `s` sites per side.** -/
theorem cellOf_eq_iff {s : ℕ} (hs : 0 < s) (y : TT μ T) (i : {j : Fin 4 // j ≠ μ} → ℕ) :
    cellOf s y = i ↔ ∀ j, s * i j ≤ (y j : ℕ) ∧ (y j : ℕ) < s * (i j + 1) := by
  rw [funext_iff]
  exact forall_congr' fun j => div_eq_iff' hs

/-- **The physical side of a cell is fixed**: `2^{k−r}` sites at spacing `a_k = a₀/2ᵏ` is
`a₀/2ʳ`. -/
theorem cellSide_phys {a₀ : ℝ} {r k : ℕ} (h : r ≤ k) :
    (2 ^ (k - r) : ℝ) * FixedAperture.aZ a₀ k = a₀ / 2 ^ r := by
  have h2 : (2 : ℝ) ^ k = 2 ^ (k - r) * 2 ^ r := (pow_sub_mul_pow 2 h).symm
  unfold FixedAperture.aZ
  rw [h2, mul_div_assoc']
  exact mul_div_mul_left a₀ (2 ^ r) (by positivity)

/-- **There are `m 2ʳ` cells per side of the box** at every zoom `k ≥ r`. -/
theorem cellOf_lt {m k r : ℕ} (h : r ≤ k) (y : TT μ (WilsonSlab.boxT μ m k))
    (j : {j : Fin 4 // j ≠ μ}) : cellOf (2 ^ (k - r)) y j < m * 2 ^ r := by
  have hy : (y j : ℕ) < m * 2 ^ k := (y j).isLt
  refine (Nat.div_lt_iff_lt_mul (by positivity)).2 ?_
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le h]
  exact hy

/-- The number of cells of the box at level `r`. -/
def cellCount (μ : Fin 4) (m r : ℕ) : ℕ := Fintype.card ({j : Fin 4 // j ≠ μ} → Fin (m * 2 ^ r))

/-- Three directions transverse to `μ`. An alias of `CentreSectorSeed.card_transverse`. -/
alias card_transverse' := MassGap.CentreSectorSeed.card_transverse

/-- **`(m 2ʳ)³` cells**, independent of the zoom. -/
theorem cellCount_eq (μ : Fin 4) (m r : ℕ) : cellCount μ m r = (m * 2 ^ r) ^ 3 := by
  unfold cellCount
  rw [Fintype.card_fun, Fintype.card_fin, card_transverse']

theorem cellCount_pos (μ : Fin 4) {m : ℕ} (hm : 0 < m) (r : ℕ) : 0 < cellCount μ m r :=
  Fintype.card_pos_iff.2 ⟨fun _ => ⟨0, Nat.mul_pos hm (pow_pos two_pos r)⟩⟩

/-- **The list of the cells** (by `Fintype.equivFin`), `0` past the end. -/
def cellEnum (μ : Fin 4) (M t : ℕ) : {j : Fin 4 // j ≠ μ} → ℕ :=
  if h : t < Fintype.card ({j : Fin 4 // j ≠ μ} → Fin M) then
    fun j => ((Fintype.equivFin ({j : Fin 4 // j ≠ μ} → Fin M)).symm ⟨t, h⟩ j : ℕ)
  else fun _ => 0

/-- **Every link of the box lies in a listed cell.** -/
theorem cellEnum_cover {m k r : ℕ} (h : r ≤ k) (l : SpT μ (WilsonSlab.boxT μ m k)) :
    ∃ t < cellCount μ m r, linkCell (2 ^ (k - r)) l = cellEnum μ (m * 2 ^ r) t := by
  let I : {j : Fin 4 // j ≠ μ} → Fin (m * 2 ^ r) := fun j => ⟨cellOf (2 ^ (k - r)) l.2 j, cellOf_lt h l.2 j⟩
  refine ⟨Fintype.equivFin _ I, (Fintype.equivFin _ I).isLt, ?_⟩
  unfold cellEnum
  rw [dif_pos (Fintype.equivFin _ I).isLt]
  funext j
  simp only [Fin.eta, Equiv.symm_apply_apply, I, linkCell]

variable (μ T) in
/-- **The links of the first `i` cells**, as a σ-algebra on the slice configurations. -/
@[reducible] def cellFilt (N s M i : ℕ) : MeasurableSpace (SpT μ T → MassGap.SUN.SU N) :=
  linkSigma {l : SpT μ T | ∃ t < i, linkCell s l = cellEnum μ M t}

theorem cellFilt_mono (N s M : ℕ) : Monotone (cellFilt μ T N s M) := fun _ _ hij =>
  linkSigma_mono fun _ ⟨t, ht, hl⟩ => ⟨t, lt_of_lt_of_le ht hij, hl⟩

/-- The periodic distance on `ℤ/M`, from `|a − b|` in `ℕ`. -/
def pdist (M a b : ℕ) : ℕ := min (a - b + (b - a)) (M - (a - b + (b - a)))

theorem pdist_comm (M a b : ℕ) : pdist M a b = pdist M b a := by
  unfold pdist
  rw [Nat.add_comm (a - b)]

/-- **The periodic `ℓ∞` distance of two cells**, in cell units. -/
def cellDist (μ : Fin 4) (M : ℕ) (i i' : {j : Fin 4 // j ≠ μ} → ℕ) : ℕ :=
  Finset.univ.sup fun j => pdist M (i j) (i' j)

theorem cellDist_comm (μ : Fin 4) (M : ℕ) (i i' : {j : Fin 4 // j ≠ μ} → ℕ) :
    cellDist μ M i i' = cellDist μ M i' i := by
  unfold cellDist
  congr 1
  funext j
  exact pdist_comm _ _ _

/-- The cell distance on the listed cells of the box at level `r`. -/
def boxDist (μ : Fin 4) (m r : ℕ) (t t' : Fin (cellCount μ m r)) : ℕ :=
  cellDist μ (m * 2 ^ r) (cellEnum μ (m * 2 ^ r) t) (cellEnum μ (m * 2 ^ r) t')

theorem boxDist_comm (μ : Fin 4) (m r : ℕ) (t t' : Fin (cellCount μ m r)) :
    boxDist μ m r t t' = boxDist μ m r t' t :=
  cellDist_comm _ _ _ _

end Box

/-- **The Wilson box of `FixedAperture`**: a time direction, couplings `β m k ≥ 0`, a unit `a₀ > 0`;
the transverse extents are `boxT μ m k` (`m 2ᵏ` sites). -/
structure BoxParams (N : ℕ) where
  μ : Fin 4
  β : ℕ → ℕ → ℝ
  hβ : ∀ m k, 0 ≤ β m k
  a₀ : ℝ
  ha₀ : 0 < a₀

namespace BoxParams

variable {N : ℕ} (X : BoxParams N) (hN : N ≠ 0)

/-- The `OneBridgeSU.WilsonBox` of the parameters, with `T m k = boxT μ m k`. -/
def box : OneBridgeSU.WilsonBox N :=
  ⟨X.μ, fun m k => WilsonSlab.boxT X.μ m k, X.β, X.hβ, X.a₀, X.ha₀⟩

/-- The Doob slab of `2ᵏ` steps at aperture `m`, zoom `k`. -/
abbrev slab (m k : ℕ) : SlabMeasure.SlabM := X.box.slab hN m k

/-- **The cell chain of the box slab at level `r`**: conditional expectations onto the links of the
first `i` cells of side `2^{k−r}` sites (physical side `a₀/2ʳ`), in the order of `cellEnum`. -/
def cellChain (r m k : ℕ) (hrk : r ≤ k) (hm : 0 < m) :
    ProjChain (oneLp (X.slab hN m k).π) (cellCount X.μ m r) :=
  condChain (S := X.slab hN m k)
    (cellFilt X.μ (WilsonSlab.boxT X.μ m k) N (2 ^ (k - r)) (m * 2 ^ r))
    (fun _ => linkSigma_le _) (cellFilt_mono N _ _) (cellCount_pos X.μ hm r)
    (pi_le_linkSigma_univ.trans (linkSigma_mono fun l _ => cellEnum_cover hrk l))

end BoxParams

/-! ## 4. Link (1): finite information through the shells -/

section Shell

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `A_{d−1} ∘ ⋯ ∘ A_0`. -/
def chainOp (A : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | t + 1 => (A t).comp (chainOp A t)

theorem norm_chainOp_le {A : ℕ → E →L[ℝ] E} {θ : ℕ → ℝ} (hA : ∀ t, ‖A t‖ ≤ θ t)
    (hθ : ∀ t, 0 ≤ θ t) : ∀ d, ‖chainOp A d‖ ≤ ∏ t ∈ Finset.range d, θ t
  | 0 => by simpa [chainOp] using ContinuousLinearMap.norm_id_le
  | d + 1 => by
    rw [Finset.prod_range_succ]
    calc ‖chainOp A (d + 1)‖ = ‖(A d).comp (chainOp A d)‖ := rfl
      _ ≤ ‖A d‖ * ‖chainOp A d‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ θ d * ∏ t ∈ Finset.range d, θ t :=
          mul_le_mul (hA d) (norm_chainOp_le hA hθ d) (norm_nonneg _) (hθ d)
      _ = (∏ t ∈ Finset.range d, θ t) * θ d := mul_comm _ _

theorem prod_le_pow {θ : ℕ → ℝ} {θ₀ : ℝ} (hθ0 : ∀ t, 0 ≤ θ t) (hθ : ∀ t, θ t ≤ θ₀) (d : ℕ) :
    ∏ t ∈ Finset.range d, θ t ≤ θ₀ ^ d :=
  calc ∏ t ∈ Finset.range d, θ t ≤ ∏ _t ∈ Finset.range d, θ₀ :=
        Finset.prod_le_prod (fun t _ => hθ0 t) (fun t _ => hθ t)
    _ = θ₀ ^ d := by rw [Finset.prod_const, Finset.card_range]

variable {n : ℕ}

/-- **Only what crosses the shells passes**: the cross term of cells `i ≠ j` is a matrix element of
a composition of `d(i,j)` shell-to-shell channels of `L²` coefficients `θ_t`. -/
def ShellFactor (P : E →L[ℝ] E) (v : Fin n → E) (d : Fin n → Fin n → ℕ) (θ : ℕ → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ (A : ℕ → E →L[ℝ] E) (u w : E), ‖u‖ ≤ ‖v i‖ ∧ ‖w‖ ≤ ‖v j‖ ∧
    (∀ t, ‖A t‖ ≤ θ t) ∧ inner ℝ (P (v i)) (P (v j)) = inner ℝ u (chainOp A (d i j) w)

/-- **Uniform shell coefficients give geometric decay**: `|⟪P vᵢ, P vⱼ⟫| ≤ θ₀^{d} ‖vᵢ‖ ‖vⱼ‖`. -/
theorem abs_cross_of_shellFactor {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ}
    {θ : ℕ → ℝ} {θ₀ : ℝ} (hθ0 : ∀ t, 0 ≤ θ t) (hθ : ∀ t, θ t ≤ θ₀) (h : ShellFactor P v d θ)
    {i j : Fin n} (hij : i ≠ j) :
    |inner ℝ (P (v i)) (P (v j))| ≤ θ₀ ^ d i j * (‖v i‖ * ‖v j‖) := by
  obtain ⟨A, u, w, hu, hw, hA, heq⟩ := h i j hij
  have hθ₀ : 0 ≤ θ₀ := (hθ0 0).trans (hθ 0)
  have hT : ‖chainOp A (d i j)‖ ≤ θ₀ ^ d i j :=
    (norm_chainOp_le hA hθ0 _).trans (prod_le_pow hθ0 hθ _)
  rw [heq]
  calc |inner ℝ u (chainOp A (d i j) w)| ≤ ‖u‖ * ‖chainOp A (d i j) w‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖v i‖ * (θ₀ ^ d i j * ‖v j‖) :=
        mul_le_mul hu (((chainOp A (d i j)).le_opNorm w).trans
          (mul_le_mul hT hw (norm_nonneg _) (pow_nonneg hθ₀ _))) (norm_nonneg _) (norm_nonneg _)
    _ = θ₀ ^ d i j * (‖v i‖ * ‖v j‖) := by ring

/-- **A shell coefficient tending to `1` has no uniform bound below `1`.** -/
theorem not_uniform_of_tendsto_one {θ : ℕ → ℝ} (h : Tendsto θ atTop (𝓝 1)) {θ₀ : ℝ}
    (hθ₀ : θ₀ < 1) : ¬ ∀ t, θ t ≤ θ₀ := by
  intro hall
  obtain ⟨t, ht⟩ := (h.eventually (lt_mem_nhds hθ₀)).exists
  exact absurd (hall t) (not_le.2 ht)

end Shell

section Face

open MassGap.FiniteInformation

variable {X Y : Type*} [Fintype Y]

/-- **A face of `M` links read letter by letter**: `M` independent copies of a per-link channel. -/
def prodChan (K : Chan X Y) (M : ℕ) : Chan (Fin M → X) (Fin M → Y) where
  P x y := ∏ t, K.P (x t) (y t)
  nonneg _ _ := Finset.prod_nonneg fun _ _ => K.nonneg _ _
  sum_one x := by
    have h := Finset.prod_univ_sum (fun _ : Fin M => (Finset.univ : Finset Y))
      (fun t y' => K.P (x t) y')
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    exact Finset.prod_eq_one fun t _ => K.sum_one (x t)

/-- The entry floor of the face channel is the `M`-th power of the per-link floor. -/
theorem prodChan_floor {K : Chan X Y} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ x y, ε ≤ K.P x y) (M : ℕ)
    (x : Fin M → X) (y : Fin M → Y) : ε ^ M ≤ (prodChan K M).P x y :=
  calc ε ^ M = ∏ _t : Fin M, ε := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ t, K.P (x t) (y t) := Finset.prod_le_prod (fun _ _ => hε0) (fun t _ => hε _ _)

/-- **The Doeblin floor of the face is `(|Y| ε)^M`.** -/
theorem minor_prodChan {K : Chan X Y} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ x y, ε ≤ K.P x y) (M : ℕ) :
    Minor (prodChan K M) (((Fintype.card Y : ℝ) * ε) ^ M) := by
  have h := minor_of_floor (prodChan_floor hε0 hε M)
  rwa [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← mul_pow] at h

/-- **A floor is at most the uniform one**: `|Y| ε ≤ 1`.

DERIVED: `1` the mass of a row. -/
theorem floor_le_one [Nonempty X] {K : Chan X Y} {ε : ℝ} (hε : ∀ x y, ε ≤ K.P x y) :
    (Fintype.card Y : ℝ) * ε ≤ 1 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  calc (Fintype.card Y : ℝ) * ε = ∑ _y : Y, ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ y, K.P x y := Finset.sum_le_sum fun y _ => hε x y
    _ = 1 := K.sum_one x

/-- **The face floor vanishes as the face grows**: for `|Y| ε < 1` and areas `M_k → ∞`. -/
theorem faceFloor_tendsto_zero {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) {M : ℕ → ℕ}
    (hM : Tendsto M atTop atTop) : Tendsto (fun k => c ^ M k) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp hM

/-- **The face of a cell grows with the zoom**: `(2^{k−r})² → ∞`.

DERIVED: `2` the dimension of a face of a 3D cell. -/
theorem faceArea_tendsto (r : ℕ) : Tendsto (fun k : ℕ => (2 ^ (k - r)) ^ 2) atTop atTop := by
  have h1 : Tendsto (fun k : ℕ => 2 ^ (k - r)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) one_lt_two).comp (tendsto_sub_atTop_nat r)
  exact tendsto_atTop_mono (fun k => le_self_pow Nat.one_le_two_pow two_ne_zero) h1

end Face

/-! ## 5. Link (3): screening at the fixed length -/

section Screen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **The fixed length screens**: cross terms decay as `e^{−(cell distance)·ℓ/ξ}`. -/
def Screens (P : E →L[ℝ] E) (v : Fin n → E) (d : Fin n → Fin n → ℕ) (Ke ξ ℓ : ℝ) : Prop :=
  ∀ i j, i ≠ j →
    |inner ℝ (P (v i)) (P (v j))| ≤ Ke * Real.exp (-(d i j * ℓ / ξ)) * (‖v i‖ * ‖v j‖)

/-- `e^{−d ℓ/ξ} = (edgeRate (1/ξ) 0 ℓ)^d`. -/
theorem screen_eq (d : ℕ) (ℓ ξ : ℝ) :
    Real.exp (-(d * ℓ / ξ)) = NonAbelianForget.edgeRate (1 / ξ) 0 ℓ ^ d := by
  unfold NonAbelianForget.edgeRate
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **Screening is the face-edge cross bound** with `c_ij = Ke q^{d}`, `q = edgeRate (1/ξ) 0 ℓ`. -/
theorem cross_of_screens {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ} {Ke ξ ℓ : ℝ}
    (h : Screens P v d Ke ξ ℓ) {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (P (v i)) (P (v j)) ^ 2 ≤ (Ke * NonAbelianForget.edgeRate (1 / ξ) 0 ℓ ^ d i j) ^ 2
      * ‖v i‖ ^ 2 * ‖v j‖ ^ 2 := by
  have h1 := h i j hij
  rw [screen_eq] at h1
  exact sq_le_of_abs_le h1

/-- `θ₀^d = e^{−d ℓ / ξ}` at `ξ = ℓ/(−log θ₀)`. -/
theorem pow_eq_screen {θ₀ ℓ : ℝ} (hθ : 0 < θ₀) (hℓ : 0 < ℓ) (d : ℕ) :
    θ₀ ^ d = Real.exp (-(d * ℓ / (ℓ / -Real.log θ₀))) := by
  have h1 : (d : ℝ) * ℓ / (ℓ / -Real.log θ₀) = d * -Real.log θ₀ := by
    rw [div_div_eq_mul_div, mul_right_comm, mul_div_cancel_right₀ _ hℓ.ne']
  rw [h1, show -((d : ℝ) * -Real.log θ₀) = d * Real.log θ₀ by ring, Real.exp_nat_mul,
    Real.exp_log hθ]

/-- **(1) gives (3)**: uniform shell coefficients `θ_t ≤ θ₀` with `θ₀ > 0` give screening with
`Ke = 1` and `ξ = ℓ/(−log θ₀)`. -/
theorem screens_of_shellFactor {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ}
    {θ : ℕ → ℝ} {θ₀ ℓ : ℝ} (hθ0 : ∀ t, 0 ≤ θ t) (hθ : ∀ t, θ t ≤ θ₀) (hθ₀ : 0 < θ₀) (hℓ : 0 < ℓ)
    (h : ShellFactor P v d θ) : Screens P v d 1 (ℓ / -Real.log θ₀) ℓ := fun i j hij => by
  rw [one_mul, ← pow_eq_screen hθ₀ hℓ]
  exact abs_cross_of_shellFactor hθ0 hθ h hij

end Screen

namespace BoxParams

variable {N : ℕ} (X : BoxParams N) (hN : N ≠ 0)

/-- **(3) on the box**: the pieces of the cell chain at `(m, k)`, level `r`, have the cell rate `ρc`
and screen at length `ξ` with the cell side `ℓ = a₀/2ʳ`. DERIVED: `(3)` labels the third link of
the module docstring, not a value; `2` the block factor of a zoom step; `L²` the exponent `2`. -/
def ScreenedCells (r m k : ℕ) (hrk : r ≤ k) (hm : 0 < m) (ρc Ke ξ : ℝ) : Prop :=
  ∀ g : Lp ℝ 2 (X.slab hN m k).π, inner ℝ g (oneLp (X.slab hN m k).π) = 0 →
    (∀ i, ‖(X.slab hN m k).P ((X.cellChain hN r m k hrk hm).piece g i)‖ ^ 2
      ≤ ρc ^ 2 * ‖(X.cellChain hN r m k hrk hm).piece g i‖ ^ 2) ∧
    Screens (X.slab hN m k).P ((X.cellChain hN r m k hrk hm).piece g) (boxDist X.μ m r) Ke ξ
      (X.a₀ / 2 ^ r)

/-- **(1) on the box**: the cell rate and uniform shell factorisation. -/
def ShellLinked (r m k : ℕ) (hrk : r ≤ k) (hm : 0 < m) (ρc : ℝ) (θ : ℕ → ℝ) : Prop :=
  ∀ g : Lp ℝ 2 (X.slab hN m k).π, inner ℝ g (oneLp (X.slab hN m k).π) = 0 →
    (∀ i, ‖(X.slab hN m k).P ((X.cellChain hN r m k hrk hm).piece g i)‖ ^ 2
      ≤ ρc ^ 2 * ‖(X.cellChain hN r m k hrk hm).piece g i‖ ^ 2) ∧
    ShellFactor (X.slab hN m k).P ((X.cellChain hN r m k hrk hm).piece g) (boxDist X.μ m r) θ

/-- **(1) gives (3) on the box.** -/
theorem screened_of_shellLinked {r m k : ℕ} {hrk : r ≤ k} {hm : 0 < m} {ρc θ₀ : ℝ} {θ : ℕ → ℝ}
    (hθ0 : ∀ t, 0 ≤ θ t) (hθ : ∀ t, θ t ≤ θ₀) (hθ₀ : 0 < θ₀)
    (h : X.ShellLinked hN r m k hrk hm ρc θ) :
    X.ScreenedCells hN r m k hrk hm ρc 1 (X.a₀ / 2 ^ r / -Real.log θ₀) := fun g hg =>
  ⟨(h g hg).1, screens_of_shellFactor hθ0 hθ hθ₀ (by have := X.ha₀; positivity) (h g hg).2⟩

/-- **(3) gives the edge cells of the box slab**, with `q = edgeRate (1/ξ) 0 (a₀/2ʳ)` and the shells
of `boxDist`. -/
theorem edgeCellsM_of_screened {r m k : ℕ} {hrk : r ≤ k} {hm : 0 < m} {ρc Ke ξ A : ℝ} {p : ℕ}
    (hKe : 0 ≤ Ke) (hD : UniformAperture.ShellCount (boxDist X.μ m r) A p)
    (h : X.ScreenedCells hN r m k hrk hm ρc Ke ξ) :
    OneBridgeSU.EdgeCellsM (X.slab hN m k) ρc Ke A p
      (NonAbelianForget.edgeRate (1 / ξ) 0 (X.a₀ / 2 ^ r)) := by
  set q := NonAbelianForget.edgeRate (1 / ξ) 0 (X.a₀ / 2 ^ r)
  have hq : 0 ≤ q := NonAbelianForget.edgeRate_nonneg _ _ _
  refine ⟨cellCount X.μ m r, fun i j => Ke * q ^ boxDist X.μ m r i j, boxDist X.μ m r,
    fun i j => mul_nonneg hKe (pow_nonneg hq _),
    fun i j => congrArg (fun x => Ke * q ^ x) (boxDist_comm _ _ _ i j), hD,
    fun i j _ => le_rfl, cellGramH_of_chainGram fun g hg => ⟨(h g hg).1, fun i j hij => ?_⟩⟩
  exact cross_of_screens (h g hg).2 hij

/-- **(B) from screening on the Wilson box.** At every aperture `m > 0` and zoom `k ≥ K₀ ≥ r`, the
cell chain at level `r` has the cell rate `ρc` and screens at `(Ke, ξ)`, the cell shells obey
`ShellCount (A, p)`, and `ρc² + Ke A edgeSum p (edgeRate (1/ξ) 0 (a₀/2ʳ)) < 1`. Then the box Doob
slabs have `RelFloorM` with one rate and one zoom: fields (A) and (B) of `OneBridgeData`. -/
theorem relFloorM_of_screened {r K₀ : ℕ} (hrK : r ≤ K₀) {ρc Ke ξ A : ℝ} {p : ℕ}
    (hρc : 0 < ρc) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (h1 : ρc ^ 2 + Ke * A * UniformAperture.edgeSum p
      (NonAbelianForget.edgeRate (1 / ξ) 0 (X.a₀ / 2 ^ r)) < 1)
    (hD : ∀ m, 0 < m → UniformAperture.ShellCount (boxDist X.μ m r) A p)
    (hS : ∀ m (hm : 0 < m) k (hk : K₀ ≤ k), X.ScreenedCells hN r m k (hrK.trans hk) hm ρc Ke ξ) :
    SlabMeasure.RelFloorM (X.box.slab hN) (fun _ => UniformAperture.cellRate ρc
      (Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate (1 / ξ) 0 (X.a₀ / 2 ^ r))))
      (fun _ => K₀) :=
  OneBridgeSU.relFloorM_of_edgeCost (σ := fun _ _ => 1 / ξ) hρc hKe hA
    (by have := X.ha₀; positivity) (by positivity) (fun _ _ _ _ => le_rfl) h1
    fun m hm k hk => X.edgeCellsM_of_screened hN hKe (hD m hm) (hS m hm k hk)

/-- **The one bridge from screening.** With `2 ≤ N` and couplings `β m k > 0` the finite-volume
input `ratio_pos` is `WilsonSlab.ratio_mem_box`; with the hypotheses of `relFloorM_of_screened`, an
observer reading in `(0, R]` and the volume link, `OneBridge` holds. -/
theorem oneBridge_of_screened {W : MassGap.ContinuumFlow.ConfFlow N} {t C : ℝ}
    {hU : MassGap.ObserverOSEuclidS.ClassMoments hN W (MassGap.ObserverSymField.SymPlaqClass N) t C}
    {rr : ℝ}
    {hphys : (MassGap.ObserverOS.energy0 W (MassGap.ObserverSymField.SymPlaqClass N)
      (MassGap.ObserverSymField.symPlaq_refl N)).PhysRange rr}
    (hN2 : 2 ≤ N) (hβ : ∀ m k, 0 < X.β m k)
    {rLat : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R)
    {r K₀ : ℕ} (hrK : r ≤ K₀) {ρc Ke ξ A : ℝ} {p : ℕ}
    (hρc : 0 < ρc) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (h1 : ρc ^ 2 + Ke * A * UniformAperture.edgeSum p
      (NonAbelianForget.edgeRate (1 / ξ) 0 (X.a₀ / 2 ^ r)) < 1)
    (hD : ∀ m, 0 < m → UniformAperture.ShellCount (boxDist X.μ m r) A p)
    (hS : ∀ m (hm : 0 < m) k (hk : K₀ ≤ k), X.ScreenedCells hN r m k (hrK.trans hk) hm ρc Ke ξ)
    (hV : FixedAperture.VolumeLink (X.box.gL hN) (OneBridgeSU.gObs hN W hU hphys) rLat) :
    OneBridgeSU.OneBridge hN W hU hphys :=
  OneBridgeSU.oneBridge_of_edgeCost X.box
    (fun m k hm => (WilsonSlab.ratio_mem_box X.μ hN hN2 (hβ m k) hm k).1) hR hr
    (σ := fun _ _ => 1 / ξ) (h := 0) hρc hKe hA (by have := X.ha₀; positivity) (by positivity)
    (fun _ _ _ _ => le_rfl) h1
    (fun m hm k hk => X.edgeCellsM_of_screened hN hKe (hD m hm) (hS m hm k hk)) hV

end BoxParams

/-! ## 6. Link (2): no long edges -/

section Path

variable {ι : Type*}

/-- **Every long-range link is a flux path**: `c_ij ≤ Σ_{n ≥ d(i,j)} Np n · wⁿ`, a convergent sum over
paths of `n` cell steps (`Np n` of them), each step of weight `w`. -/
def PathSum (c : ι → ι → ℝ) (d : ι → ι → ℕ) (Np : ℕ → ℝ) (w : ℝ) : Prop :=
  ∀ i j, i ≠ j → Summable (fun t : ℕ => Np (d i j + t) * w ^ (d i j + t)) ∧
    c i j ≤ ∑' t : ℕ, Np (d i j + t) * w ^ (d i j + t)

/-- **Path sums give the face-edge cost**: `Np n ≤ zⁿ`, `z w < 1` give
`c_ij ≤ (1 − z w)⁻¹ (z w)^{d(i,j)}`. -/
theorem faceEdgeCost_of_pathSum {c : ι → ι → ℝ} {d : ι → ι → ℕ} {Np : ℕ → ℝ} {z w : ℝ}
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hzw : z * w < 1) (hN : ∀ n, Np n ≤ z ^ n)
    (h : PathSum c d Np w) : UniformAperture.FaceEdgeCost c d (1 - z * w)⁻¹ (z * w) := by
  intro i j hij
  obtain ⟨hs, hc⟩ := h i j hij
  have hq0 : 0 ≤ z * w := mul_nonneg hz hw
  have hg : Summable (fun t : ℕ => (z * w) ^ (d i j + t)) := by
    simp_rw [pow_add]
    exact (summable_geometric_of_lt_one hq0 hzw).mul_left _
  calc c i j ≤ ∑' t, Np (d i j + t) * w ^ (d i j + t) := hc
    _ ≤ ∑' t, (z * w) ^ (d i j + t) :=
        Summable.tsum_le_tsum (fun t => by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (hN _) (pow_nonneg hw _)) hs hg
    _ = (z * w) ^ d i j * (1 - z * w)⁻¹ := by
        simp_rw [pow_add]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hzw]
    _ = (1 - z * w)⁻¹ * (z * w) ^ d i j := mul_comm _ _

/-- **The path entropy is a rate per length**: `z e^{−σℓ} = edgeRate σ (log z / ℓ) ℓ`. -/
theorem pathRate_eq_edgeRate {z σ ℓ : ℝ} (hz : 0 < z) (hℓ : 0 < ℓ) :
    z * Real.exp (-(σ * ℓ)) = NonAbelianForget.edgeRate σ (Real.log z / ℓ) ℓ := by
  unfold NonAbelianForget.edgeRate
  have : -((σ - Real.log z / ℓ) * ℓ) = Real.log z + -(σ * ℓ) := by
    rw [sub_mul, div_mul_cancel₀ _ hℓ.ne']
    ring
  rw [this, Real.exp_add, Real.exp_log hz]

/-- **A flux sheet's area-law weight is an edge rate**: `e^{−σlat (ℓ/a)(τ/a)}` is
`edgeRate (σlat/a² · τ) 0 ℓ`, the tension in aperture units times the slab thickness. -/
theorem areaWeight_eq {σlat a ℓ τ : ℝ} (ha : a ≠ 0) :
    Real.exp (-(σlat * (ℓ / a) * (τ / a))) = NonAbelianForget.edgeRate (σlat / a ^ 2 * τ) 0 ℓ := by
  unfold NonAbelianForget.edgeRate
  rw [EdgeCost.area_exponent_phys ha]
  congr 1
  ring

/-- **String scaling gives a tension floor** on `sigmaPhys σlat (aRun N)`, eventually in `β`. -/
theorem tension_floor_of_stringScaling {N : ℕ} {σlat : ℝ → ℝ} (h : EdgeCost.StringScalingAt N σlat) :
    ∃ σ₁ : ℝ, 0 < σ₁ ∧ ∀ᶠ β in atTop, σ₁ ≤ EdgeCost.sigmaPhys σlat (AsymptoticScaling.aRun N) β := by
  obtain ⟨σ₀, hσ₀, hlim⟩ := h
  exact ⟨σ₀ / 2, by positivity,
    (hlim.eventually (lt_mem_nhds (by linarith : σ₀ / 2 < σ₀))).mono fun _ hb => hb.le⟩

/-- **A free carrier makes the path sum diverge**: `z w ≥ 1` and `Np n ≥ zⁿ`. -/
theorem not_summable_of_free {Np : ℕ → ℝ} {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) (hzw : 1 ≤ z * w)
    (hN : ∀ n, z ^ n ≤ Np n) (d : ℕ) :
    ¬ Summable (fun t : ℕ => Np (d + t) * w ^ (d + t)) := by
  intro hs
  have hg : Summable (fun t : ℕ => (z * w) ^ (t + d)) :=
    Summable.of_nonneg_of_le (fun t => pow_nonneg (mul_nonneg hz hw) _)
      (fun t => by
        rw [mul_pow, add_comm t d]
        exact mul_le_mul_of_nonneg_right (hN _) (pow_nonneg hw _)) hs
  have h2 := summable_geometric_iff_norm_lt_one.1
    ((summable_nat_add_iff (f := fun n : ℕ => (z * w) ^ n) d).1 hg)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz hw)] at h2
  linarith

/-- **No path sum with a free carrier**, as soon as there are two cells. -/
theorem not_pathSum_of_free {c : ι → ι → ℝ} {d : ι → ι → ℕ} {Np : ℕ → ℝ} {z w : ℝ} (hz : 0 ≤ z)
    (hw : 0 ≤ w) (hzw : 1 ≤ z * w) (hN : ∀ n, z ^ n ≤ Np n) {i j : ι} (hij : i ≠ j) :
    ¬ PathSum c d Np w := fun h => not_summable_of_free hz hw hzw hN (d i j) (h i j hij).1

end Path

namespace BoxParams

variable {N : ℕ} (X : BoxParams N) (hN : N ≠ 0)

/-- **(2) on the box**: the cell rate, and cross terms of the cell-chain pieces bounded by a
coupling `c` that is a path sum over the cell distance. -/
def PathCells (r m k : ℕ) (hrk : r ≤ k) (hm : 0 < m) (ρc : ℝ)
    (c : Fin (cellCount X.μ m r) → Fin (cellCount X.μ m r) → ℝ) (Np : ℕ → ℝ) (w : ℝ) : Prop :=
  ChainGram (X.slab hN m k).P (X.cellChain hN r m k hrk hm) ρc c ∧
    PathSum c (boxDist X.μ m r) Np w

/-- **(2) gives the edge cells of the box slab** with `Ke = (1 − z w)⁻¹`, `q = z w`. -/
theorem edgeCellsM_of_pathCells {r m k : ℕ} {hrk : r ≤ k} {hm : 0 < m} {ρc A z w : ℝ} {p : ℕ}
    {c : Fin (cellCount X.μ m r) → Fin (cellCount X.μ m r) → ℝ} {Np : ℕ → ℝ}
    (hc0 : ∀ i j, 0 ≤ c i j) (hcs : ∀ i j, c i j = c j i) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hzw : z * w < 1) (hNp : ∀ n, Np n ≤ z ^ n) (hD : UniformAperture.ShellCount (boxDist X.μ m r) A p)
    (h : X.PathCells hN r m k hrk hm ρc c Np w) :
    OneBridgeSU.EdgeCellsM (X.slab hN m k) ρc (1 - z * w)⁻¹ A p (z * w) :=
  ⟨cellCount X.μ m r, c, boxDist X.μ m r, hc0, hcs, hD,
    faceEdgeCost_of_pathSum hz hw hzw hNp h.2, cellGramH_of_chainGram h.1⟩

end BoxParams

/-! ## 7. Controls: a power law beats every geometric bound -/

/-- **Geometric decay falls below every power law**: for `c₀ > 0`, `0 ≤ q < 1`, eventually
`Ke qᵈ < c₀ / dᵖ`.

DERIVED: `1` the least distance at which `dᵖ > 0`. -/
theorem powerLaw_beats {c₀ Ke q : ℝ} (hc₀ : 0 < c₀) (hq0 : 0 ≤ q) (hq1 : q < 1) (p : ℕ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → Ke * q ^ d < c₀ / (d : ℝ) ^ p := by
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one p
    (by rw [abs_of_nonneg hq0]; exact hq1)).const_mul |Ke|
  rw [mul_zero] at ht
  obtain ⟨D, hD⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hc₀))
  refine ⟨max D 1, fun d hd => ?_⟩
  have hd1 : (0 : ℝ) < (d : ℝ) ^ p :=
    pow_pos (Nat.cast_pos.2 (lt_of_lt_of_le one_pos (le_of_max_le_right hd))) p
  have h := hD d (le_of_max_le_left hd)
  rw [lt_div_iff₀ hd1]
  calc Ke * q ^ d * (d : ℝ) ^ p ≤ |Ke| * q ^ d * (d : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Ke) (pow_nonneg hq0 d))
          hd1.le
    _ = |Ke| * ((d : ℝ) ^ p * q ^ d) := by ring
    _ < c₀ := h

/-- **A power-law cross term violates screening**: for every `Ke` and `ξ > 0`, `ℓ > 0` there is a
cell distance `D` beyond which a pair with nonzero pieces and
`|⟪P vᵢ, P vⱼ⟫| ≥ c₀ d^{−p} ‖vᵢ‖ ‖vⱼ‖` contradicts `Screens`. -/
theorem not_screens_of_powerLaw {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    {c₀ Ke ξ ℓ : ℝ} (hc₀ : 0 < c₀) (hξ : 0 < ξ) (hℓ : 0 < ℓ) (p : ℕ) :
    ∃ D : ℕ, ∀ (P : E →L[ℝ] E) (v : Fin n → E) (d : Fin n → Fin n → ℕ) (i j : Fin n), i ≠ j →
      D ≤ d i j → 0 < ‖v i‖ * ‖v j‖ →
      c₀ / (d i j : ℝ) ^ p * (‖v i‖ * ‖v j‖) ≤ |inner ℝ (P (v i)) (P (v j))| →
      ¬ Screens P v d Ke ξ ℓ := by
  have hq1 : NonAbelianForget.edgeRate (1 / ξ) 0 ℓ < 1 :=
    NonAbelianForget.edgeRate_lt_one (by positivity) hℓ
  obtain ⟨D, hD⟩ := powerLaw_beats (Ke := Ke) hc₀ (NonAbelianForget.edgeRate_nonneg _ _ _) hq1 p
  refine ⟨D, fun P v d i j hij hd hv hlow hS => ?_⟩
  have h1 := hS i j hij
  rw [screen_eq] at h1
  have h2 := mul_lt_mul_of_pos_right (hD (d i j) hd) hv
  linarith

#print axioms ProjChain.sum_piece
#print axioms ProjChain.piece_orth
#print axioms cellGramH_of_chainGram
#print axioms condChain
#print axioms cellOf_eq_iff
#print axioms cellSide_phys
#print axioms cellOf_lt
#print axioms cellCount_eq
#print axioms cellEnum_cover
#print axioms BoxParams.cellChain
#print axioms norm_chainOp_le
#print axioms abs_cross_of_shellFactor
#print axioms not_uniform_of_tendsto_one
#print axioms minor_prodChan
#print axioms floor_le_one
#print axioms faceFloor_tendsto_zero
#print axioms faceArea_tendsto
#print axioms cross_of_screens
#print axioms screens_of_shellFactor
#print axioms BoxParams.screened_of_shellLinked
#print axioms BoxParams.edgeCellsM_of_screened
#print axioms BoxParams.relFloorM_of_screened
#print axioms BoxParams.oneBridge_of_screened
#print axioms faceEdgeCost_of_pathSum
#print axioms pathRate_eq_edgeRate
#print axioms areaWeight_eq
#print axioms tension_floor_of_stringScaling
#print axioms not_pathSum_of_free
#print axioms BoxParams.edgeCellsM_of_pathCells
#print axioms powerLaw_beats
#print axioms not_screens_of_powerLaw

end MassGap.CellLinks
