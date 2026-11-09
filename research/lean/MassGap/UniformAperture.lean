import Mathlib
import MassGap.RelativeGap
import MassGap.EdgeCost

/-!
# MassGap.UniformAperture — (B) from cells of one fixed physical length

`FixedAperture` splits the fine end into (A) a floor on the box gap at fixed aperture `L_m = m a₀`,
(B) uniformity of those floors in `m`, and a volume link. `RelativeGap.uniformInAperture_of_relFloor`
reduces (B) to: eventually in `m`, `ρ_m ≤ ρ₀ < 1`, `τ_m ≤ T`, `K_m ≤ K₀`. The owner's reading of (B):
the diffraction limit is a fixed physical length. Here the box of side `L_m` is cut into cells of one
fixed physical side `ℓ` (their number grows like `(L_m/ℓ)³` across the slab), and the slab rate is
bounded by the cell rate and a coupling between cells that does not grow with the number of cells.

The hypotheses record no cell size or locality: with one cell, any uniform slab rate `Contr ρc`
satisfies them (`slabCells_of_contr`, `edgeCells_of_contr`). Their content lies in the intended
reading, the pieces as martingale differences of a cell filtration at side `ℓ`, which no declaration
enforces.

Everything is finite-dimensional, in the norms of `GapL2`: `L²(π)` of the box state `π`, on mean-zero
functions.

## 1. Cells combine by a Gram row sum

* `CellGram π K ρc c` (over a finite index `ι` of cells): every mean-zero `g` is a sum `Σ_i v_i` of
  pieces that are pairwise orthogonal in `L²(π)`, each piece obeys `‖K v_i‖² ≤ ρc² ‖v_i‖²` (the cell
  rate), and the images of two different pieces have cross term
  `⟨K v_i, K v_j⟩² ≤ c_ij² ‖v_i‖² ‖v_j‖²`. For any `π` the martingale differences of `g` along an
  ordering of the cells (`v_i = E[g | cells ≤ i] − E[g | cells < i]`) are such a pairwise orthogonal
  sum, provided the cells cover every variable (in a gauge theory the links between cells and the
  gauge constraint must be assigned to cells, which nothing here does). That reading is the intended
  one and is not built here. For a non-product `π` the piece `v_i` depends on all cells `≤ i`, not on
  cell `i` alone, so `ρc` is a conditional rate (it depends on the order and on the rest of the box),
  and decay of `c_ij` in the distance needs conditional decorrelation (screening) of `π` as well as
  clustering of the transfer.
* `RowSum c η`: `c ≥ 0`, symmetric, and `Σ_{j ≠ i} c_ij ≤ η` at every cell `i`.
* `contr_of_gram`: `CellGram ∧ RowSum ⇒ Contr π K √(ρc² + η)`. So `f(η) = √(ρc² + η) − ρc`, and
  `sqrt_add_le`: `f(η) ≤ √η`. The rate is below `1` when `ρc² + η < 1` (`sqrt_lt_one_of`).
  The proof is the Schur test on the Gram matrix `⟨K v_i, K v_j⟩`: `2 c √(ab) ≤ c (a + b)`
  (`ip_le_of_sq`), then the symmetric off-diagonal sum is at most `η Σ ‖v_i‖²` (`offdiag_sum_le`).
* `contr_of_orthCells`: at `c ≡ 0` the rate is `ρc` itself: the pieces combine by `max`. It
  generalises the conclusion of `RelativeGap.contr_of_split` (two pieces) to any number of pieces and
  has the shape of the conclusion of `GapL2.Contr.kron`; the product-state decomposition that would
  derive `Contr.kron` from it is not built.

The additive route of `GapL2.contr_of_cellInput` (`‖(K − K_c^{⊗N}) g‖ ≤ ε ‖g‖`, rate `ρc + ε`, so
`f(ε) = ε`) needs `ε` uniform in the number of cells `N` and the product state; `GapL2` section 5
records that the triangle inequality over the transverse bonds makes that `ε` grow with `N`. The row
sum is the form in which far cells do not add: only `max_i Σ_j c_ij` enters.

## 2. (B) from cells

* `SlabCells S ρc η`: the slab `S` has some finite set of cells (`Fin n`, `n` free) with `CellGram`
  rate `ρc` and `RowSum η`. `contr_of_slabCells`: `Contr S.π S.K (cellRate ρc η)`,
  `cellRate ρc η = √(ρc² + η)`. `slabCells_of_contr`: a single cell with `η = 0` is `Contr ρc`.
* `relFloor_of_cells`: if at every aperture `m > 0` and zoom `k ≥ K₀` the slab has `SlabCells` with
  one `ρc > 0` and one `η₀ ≥ 0`, `ρc² + η₀ < 1`, then `RelFloor S (cellRate ρc η₀) K₀`.
* `uniformInAperture_of_cells`: with slab thickness eventually in `(0, T]`, the floors of
  `fixedApertureFloor_of_relFloor` satisfy (B). `noFade_of_cells`: with `ReadsSlab`, an observer
  reading in `(0, R]` and `VolumeLink`, `NoFadeAtFineEnd gLat rLat`.

The number of cells does not appear in any of these statements; `ρc` and `η₀` are the same at every
`m`. `SlabCells` does not record the size of the cells: `slabCells_of_contr` shows that one cell (the
whole box) with `η = 0` is `Contr ρc` itself, so with one cell the hypothesis of `relFloor_of_cells`
is the hypothesis of `RelativeGap.relFloor_of_contr` with a constant rate. The intended reading puts
the pieces at one fixed physical side `ℓ`, so that `ρc` is the (conditional) rate of a cell of that
size given the cells before it and `η₀` its coupling to the other cells, both read at the scale `ℓ`
whatever the aperture; that reading is not a declaration, and for a non-product state `ρc` is not
the rate of the cell in isolation (section 1).

## 3. The coupling from the edge cost

* `ShellCount d A p`: a cell distance `d i j ≥ 1` for `i ≠ j` (in cell units), and at most `A nᵖ`
  cells at distance `n` from any cell (`p = 2`, `A = 26` for the `ℓ∞` shells of a 3D cross-section).
* `FaceEdgeCost c d Ke q`: `c_ij ≤ Ke qᵈ⁽ⁱʲ⁾`. With `q = NonAbelianForget.edgeRate σ h ℓ =
  e^{−(σ − h) ℓ}`, `σ − h` is a decay rate per unit length. In the edge picture it reads: the
  coupling of two cells of side `ℓ` at distance `d` cells is carried by flux edges of length at least
  `d ℓ` across the faces between them, each length costing a tension `σ` less a shape entropy `h`.
  No declaration identifies `σ` with the string tension of a measure (section 5).
* `edgeSum p q = Σ_n nᵖ qⁿ` (summable for `0 ≤ q < 1`). `rowSum_le_of_edgeCost`: `ShellCount` and
  `FaceEdgeCost` give `Σ_{j ≠ i} c_ij ≤ Ke A edgeSum p q` at every cell, independent of the number of
  cells.
* `edgeSum_le_scale`, `exists_small_edge`: `edgeSum p q ≤ (q/q₀) edgeSum p q₀` for `p ≥ 1`, so the row
  sum is as small as wanted for `q` small. `edgeRate_le_of_sigma`: `σ ≥ h + (−log q₁)/ℓ` gives
  `edgeRate σ h ℓ ≤ q₁`. `exists_sigma_threshold`: for `ρc < 1` there is `σ₁ > h` such that every
  `σ₀ ≥ σ₁` gives `ρc² + Ke A edgeSum p (edgeRate σ₀ h ℓ) < 1`.
* `EdgeCells S ρc Ke A p q`: `CellGram` with a symmetric `c ≥ 0` obeying `ShellCount` and
  `FaceEdgeCost` at `q`. `slabCells_of_edgeCells`: it gives `SlabCells S ρc (Ke A edgeSum p q)`.
  `edgeCells_mono`: a larger `q` keeps it. `EdgeCells` carries no locality: the pieces are tied to no
  region and `d` is any function into `ℕ`. `edgeCells_of_contr`: one cell with `A = 0` turns a slab
  rate `Contr ρc` into `EdgeCells` at every `Ke`, `p`, `q` (orthogonal pieces with `c ≡ 0`, for
  example along an eigenbasis of `KᵀK`, do the same with many pieces). So the hypothesis of
  `uniformAperture_of_edgeCost` follows from a slab rate uniform in the aperture, and "independent of
  the number of cells" has content only under the intended reading (pieces the martingale differences
  of one cell filtration at side `ℓ`, `d` the cell metric), which no declaration enforces.
* `uniformAperture_of_edgeCost`: at every aperture `m > 0` and zoom `k ≥ K₀`, `EdgeCells` with
  `q = edgeRate (σ m k) h ℓ` and one `(ρc, Ke, A, p, ℓ, h)`, a rate floor `σ m k ≥ σ₀ > h` (there), and
  `ρc² + Ke A edgeSum p (edgeRate σ₀ h ℓ) < 1`, give `RelFloor` and (B). The tension floor enters
  through `EdgeCost.edgeRate_le_of_sigma_ge`, the same monotonicity that `EdgeCost.uniform_edgeRate`
  uses for the time direction.
* Control without edge cost: `rowSum_ge_of_floor`, `free_edge_no_uniform`. If the cross terms do not
  decay, `c_ij ≥ c₀ > 0` for all `i ≠ j`, the row sum is at least `c₀ (n − 1)` on `n` cells, and no
  `η` serves every number of cells. At `σ = h` (`NonAbelianForget.edgeRate_self`) `FaceEdgeCost`
  carries no decay. The control covers a coupling with a floor at every distance; it says nothing
  about slow (power-law) decay or about other decompositions.

## 4. Numerics

`research/code/uniform_aperture_checks.py` (under 10 s, exact linear algebra, no Monte Carlo).

* Lattice Gaussian fields at spacing `a = 1`, periodic spatial box of side `L`, slab thickness `τ = 2`,
  cells of side `ℓ = 2`, first chaos (for a Gaussian field the maximal correlation is the largest
  canonical correlation, Lancaster, cited). The pieces are the martingale differences along the
  lexicographic order of the cells (Cholesky in the state's norm, cell by cell);
  `ρc² = max_i ‖Q_iᵀ T² Q_i‖`, `c_ij = ‖Q_iᵀ T² Q_j‖`, `η = max_i Σ_{j≠i} c_ij`. These are computed on
  the first chaos (linear functionals) only: Lancaster gives `ρ` there, not `ρc` or `η` over all of
  `L²(π)`. The script asserts `ρ² ≤ ρc² + η` at every row, which checks the implementation of the
  Schur bound, not a property of the field.
  4D, massive scalar `m = 1`, `L = 4 … 12` (`8 … 216` cells): `ρ² = 0.0213` at every `L`,
  `η = 0.0229, 0.0268, 0.0288, 0.0304, 0.0312` (increments `0.0039, 0.0020, 0.0016, 0.0008`),
  `ρc² + η ≤ 0.0345`; `ρc²` itself moves with `L` (`0.0066 → 0.0033`), being a conditional rate. The
  largest cross term at cell distance `1, 2, 3` from the row that sets `η` falls by factors `0.30`, then `0.23`
  (at `L = 12` distance `3` is the periodic antipode). Five sizes do not show that `η` is bounded.
  4D, massless with the spatial zero mode removed (a massless scalar with the photon's dispersion, one
  polarisation; not gauge-invariant photon observables): `ρ² = 0.005 … 0.129` rising toward `1`,
  `η = 0.006, 0.049, 0.135, 0.265, 0.422`; the shell sums of the cross term do not fall with distance
  (`0.146, 0.150, 0.126` at distances `1, 2, 3`, `L = 12`). 2D (one spatial dimension), `L = 8 … 256`:
  massive `ρc² + η → 0.0258` (constant from `L = 32`); massless
  `ρc² + η = 0.08, 0.37, 0.91, 1.59, 2.33, 3.06`, above `1` from `L = 64`.
* 2D `U(1)` and `SU(2)` heat kernel on the periodic box: at fixed time the gauge-invariant states are
  class functions of the one holonomy around the box, so the slab transfer acts on the holonomy alone
  and the cell bound is not exercised. Its maximal correlation is `e^{−κ L τ}` (`U(1)`, charge `1`,
  Casimir `n²`) and `e^{−3κ L τ}` (`SU(2)`, Casimir `n² − 1` in the dimension `n = 2`, the
  normalisation of `FixedAperture.su2_control`); the discretised kernels agree to `10⁻⁶`. Both fall as
  `L` grows, so (B) holds, 2D `U(1)` included; the level is a flux (torelon) energy growing with `L`,
  which fails `VolumeLink` (`FixedAperture.su2_not_volumeLink`).

## 5. What remains

Nothing here proves `EdgeCells` (or `SlabCells`) for the 4D `SU(N)` Wilson slab, and no declaration
ties `Slab`, the cells or `σ` to the Wilson measure. In the owner's terms the remaining statement is:
the coupling between two cells of the fixed length `ℓ` (the pieces the martingale differences of one
cell filtration of side `ℓ`, covering the links), measured as the `L²` cross term of the slab transfer
between their pieces, is bounded by the cost of the flux edges that join them,
`Ke e^{−(σ − h) ℓ d}`, with `σ − h ≥ σ₀ − h > 0` in aperture units, `(ρc, Ke, A, ℓ)` the same at
every aperture and zoom, and `ρc² + Ke A edgeSum p (e^{−(σ₀ − h) ℓ}) < 1`.

The hypotheses of `relFloor_of_cells` and `uniformAperture_of_edgeCost` record no cell size or
locality: with one cell any uniform `Contr ρc` satisfies them (`slabCells_of_contr`,
`edgeCells_of_contr`), and their content lies in the intended reading above, which no declaration
enforces.

What it amounts to. The hypothesis is at least as strong as (B): the theorems derive (B) from it.
Its relation to the gap (clustering of local observables) is not built here. The pieces `v_i` are
conditional martingale differences, so a conditional cross term decaying at a fixed rate is a
clustering-type statement for the conditional state; its decay needs conditional decorrelation
(screening) of `π` as well as decay of the transfer. What the reduction adds is the shape of the
input: a per-cell coupling at one length `ℓ` whose far terms do not add, in place of a bound on the
whole box.

Relation to the string tension (`EdgeCost`); prose, not proved. `σ − h` here is a decay rate, and no
declaration identifies it with the tension. In the flux-tube picture a loop joining two cells spans
an area of order `d ℓ × 2τ`, so the tension would enter through that geometry, and `σ > 0`
(`EdgeCost.StringScalingAt`, confinement) would give the hypothesis only through an edge or polymer
expansion of the measure (the `EdgeExpansion` input of `NonAbelianForget`), which is not proved.
Conversely a gapped theory without area law (a Higgs phase) is expected to satisfy it with `σ` read
as a free rate, in which case it would not imply confinement. Neither comparison is a declaration.

DERIVED (module-wide): `0` the mean that selects the readings orthogonal to the vacuum, the sign of
every bound and the off-diagonal convention of `offd`; `1` the least cell distance, the top of every
rate and the least shell exponent; `2` in `c (a + b)/2` from `(a + b)² ≥ 4ab`, the degree of the norm
and the factor `2 q` in `exists_small_edge`; `1/2` the reference ratio `q₀` in `exists_small_edge`.
-/

noncomputable section

namespace MassGap.UniformAperture

open Filter Topology Matrix GapL2
open MassGap.NoTransition MassGap.FixedAperture MassGap.RelativeGap MassGap.NonAbelianForget

/-! ## 1. Cells combine by a Gram row sum -/

section Gram

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem ip_comm (π f g : α → ℝ) : ip π f g = ip π g f :=
  Finset.sum_congr rfl fun _ _ => by ring

theorem ip_sum_left (π g : α → ℝ) (v : ι → α → ℝ) :
    ip π (∑ i, v i) g = ∑ i, ip π (v i) g := by
  simp only [ip, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem ip_sum_right (π f : α → ℝ) (v : ι → α → ℝ) :
    ip π f (∑ i, v i) = ∑ i, ip π f (v i) := by
  rw [ip_comm, ip_sum_left]
  exact Finset.sum_congr rfl fun i _ => ip_comm _ _ _

theorem nsq_sum (π : α → ℝ) (v : ι → α → ℝ) :
    nsq π (∑ i, v i) = ∑ i, ∑ j, ip π (v i) (v j) := by
  rw [nsq_eq_ip, ip_sum_left]
  exact Finset.sum_congr rfl fun i _ => ip_sum_right _ _ _

/-- **Pairwise orthogonal pieces add their squared norms.** -/
theorem nsq_sum_orth (π : α → ℝ) (v : ι → α → ℝ) (h : ∀ i j, i ≠ j → ip π (v i) (v j) = 0) :
    nsq π (∑ i, v i) = ∑ i, nsq π (v i) := by
  rw [nsq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => h i j (Ne.symm hj))
    (fun hi => absurd (Finset.mem_univ i) hi), nsq_eq_ip]

/-- `a² ≤ c² x y` with `c, x, y ≥ 0` gives `a ≤ c (x + y)/2`.

DERIVED: `2` from `(x + y)² ≥ 4 x y`. -/
theorem ip_le_of_sq {a c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : a ^ 2 ≤ c ^ 2 * x * y) : a ≤ c * (x + y) / 2 := by
  have hb : 0 ≤ c * (x + y) / 2 := by positivity
  have h2 : a ^ 2 ≤ (c * (x + y) / 2) ^ 2 := by nlinarith [sq_nonneg (c * (x - y))]
  exact (abs_le_of_sq_le_sq' h2 hb).2

variable [DecidableEq ι]

/-- The off-diagonal part of `c`: `0` on the diagonal.

DERIVED: `0` the diagonal convention. -/
def offd (c : ι → ι → ℝ) (i j : ι) : ℝ := if i = j then 0 else c i j

omit [Fintype ι] in
theorem offd_symm {c : ι → ι → ℝ} (hsymm : ∀ i j, c i j = c j i) (i j : ι) :
    offd c i j = offd c j i := by
  unfold offd
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), hsymm]

theorem sum_erase_eq_ite (i : ι) (F : ι → ℝ) :
    ∑ j ∈ Finset.univ.erase i, F j = ∑ j, if i = j then 0 else F j := by
  have h : (if i = i then (0 : ℝ) else F i) + ∑ j ∈ Finset.univ.erase i, (if i = j then 0 else F j)
      = ∑ j, if i = j then 0 else F j :=
    Finset.add_sum_erase Finset.univ (fun j => if i = j then (0 : ℝ) else F j) (Finset.mem_univ i)
  rw [← h, if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]

theorem offd_row (c : ι → ι → ℝ) (i : ι) :
    ∑ j, offd c i j = ∑ j ∈ Finset.univ.erase i, c i j :=
  (sum_erase_eq_ite i (c i)).symm

/-- **The symmetric off-diagonal sum is at most `η Σ nᵢ`** when every row of `c` off the diagonal
sums to at most `η`. -/
theorem offdiag_sum_le {n : ι → ℝ} (hn : ∀ i, 0 ≤ n i) (c : ι → ι → ℝ) {η : ℝ}
    (hsymm : ∀ i j, c i j = c j i) (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ η) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (n i + n j) / 2 ≤ η * ∑ i, n i := by
  have hE : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j * (n i + n j) / 2
      = ∑ j, (offd c i j * n i + offd c i j * n j) / 2 := fun i => by
    rw [sum_erase_eq_ite i (fun j => c i j * (n i + n j) / 2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold offd
    split_ifs <;> ring
  have hA : ∑ i, ∑ j, offd c i j * n i ≤ η * ∑ i, n i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul, offd_row]
    exact mul_le_mul_of_nonneg_right (hrow i) (hn i)
  have hB : ∑ i, ∑ j, offd c i j * n j = ∑ i, ∑ j, offd c i j * n i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [offd_symm hsymm j i]
  have hsplit : ∑ i, ∑ j, (offd c i j * n i + offd c i j * n j) / 2
      = (∑ i, ∑ j, offd c i j * n i + ∑ i, ∑ j, offd c i j * n j) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [Finset.sum_congr rfl fun i _ => hE i, hsplit, hB]
  linarith

/-- **The Schur test on the Gram matrix.** A diagonal bound `‖w_i‖² ≤ D ‖u_i‖²` and cross terms
`⟨w_i, w_j⟩² ≤ c_ij² ‖u_i‖² ‖u_j‖²` with `c ≥ 0` symmetric of off-diagonal row sums at most `η` give
`‖Σ w_i‖² ≤ (D + η) Σ ‖u_i‖²`. -/
theorem nsq_sum_le_gram {π : α → ℝ} (w u : ι → α → ℝ) {D η : ℝ} (hn : ∀ i, 0 ≤ nsq π (u i))
    (c : ι → ι → ℝ) (hc0 : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ η)
    (hdiag : ∀ i, nsq π (w i) ≤ D * nsq π (u i))
    (hoff : ∀ i j, i ≠ j → ip π (w i) (w j) ^ 2 ≤ c i j ^ 2 * nsq π (u i) * nsq π (u j)) :
    nsq π (∑ i, w i) ≤ (D + η) * ∑ i, nsq π (u i) := by
  rw [nsq_sum]
  have hi : ∀ i, ∑ j, ip π (w i) (w j) ≤ D * nsq π (u i)
      + ∑ j ∈ Finset.univ.erase i, c i j * (nsq π (u i) + nsq π (u j)) / 2 := by
    intro i
    have e := Finset.add_sum_erase Finset.univ (fun j => ip π (w i) (w j)) (Finset.mem_univ i)
    rw [← e]
    refine add_le_add ?_ (Finset.sum_le_sum fun j hj => ?_)
    · have h := hdiag i
      rw [nsq_eq_ip] at h
      exact h
    · exact ip_le_of_sq (hc0 i j) (hn i) (hn j) (hoff i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  calc ∑ i, ∑ j, ip π (w i) (w j)
      ≤ ∑ i, (D * nsq π (u i)
          + ∑ j ∈ Finset.univ.erase i, c i j * (nsq π (u i) + nsq π (u j)) / 2) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = D * ∑ i, nsq π (u i)
          + ∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (nsq π (u i) + nsq π (u j)) / 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ D * ∑ i, nsq π (u i) + η * ∑ i, nsq π (u i) :=
        add_le_add le_rfl (offdiag_sum_le hn c hsymm hrow)
    _ = (D + η) * ∑ i, nsq π (u i) := by ring

/-- **Cells with a Gram bound.** Every mean-zero `g` is a sum of pairwise `L²(π)`-orthogonal pieces
`v_i`, one per cell, with cell rate `‖K v_i‖² ≤ ρc² ‖v_i‖²` and cross terms
`⟨K v_i, K v_j⟩² ≤ c_ij² ‖v_i‖² ‖v_j‖²`. -/
def CellGram (π : α → ℝ) (K : Matrix α α ℝ) (ρc : ℝ) (c : ι → ι → ℝ) : Prop :=
  ∀ g, mean π g = 0 → ∃ v : ι → α → ℝ, g = ∑ i, v i ∧
    (∀ i j, i ≠ j → ip π (v i) (v j) = 0) ∧
    (∀ i, nsq π (K *ᵥ v i) ≤ ρc ^ 2 * nsq π (v i)) ∧
    (∀ i j, i ≠ j → ip π (K *ᵥ v i) (K *ᵥ v j) ^ 2 ≤ c i j ^ 2 * nsq π (v i) * nsq π (v j))

/-- **A coupling of row sum at most `η`**: `c ≥ 0`, symmetric, `Σ_{j ≠ i} c_ij ≤ η` at every cell. -/
def RowSum (c : ι → ι → ℝ) (η : ℝ) : Prop :=
  (∀ i j, 0 ≤ c i j) ∧ (∀ i j, c i j = c j i) ∧ ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ η

/-- **The slab rate from the cell rate and the coupling**: `Contr π K √(ρc² + η)`. -/
theorem contr_of_gram {π : α → ℝ} {K : Matrix α α ℝ} (hπ : ∀ x, 0 ≤ π x) {ρc η : ℝ}
    {c : ι → ι → ℝ} (hG : CellGram π K ρc c) (hR : RowSum c η) (hρη : 0 ≤ ρc ^ 2 + η) :
    Contr π K (Real.sqrt (ρc ^ 2 + η)) := by
  obtain ⟨hc0, hsymm, hrow⟩ := hR
  refine ⟨Real.sqrt_nonneg _, fun g hg => ?_⟩
  obtain ⟨v, rfl, horth, hdiag, hoff⟩ := hG g hg
  rw [Real.sq_sqrt hρη, Matrix.mulVec_sum, nsq_sum_orth π v horth]
  exact nsq_sum_le_gram (fun i => K *ᵥ v i) v (fun i => nsq_nonneg hπ _) c hc0 hsymm hrow hdiag hoff

/-- **Uncoupled cells combine by `max`**: at `c ≡ 0` the slab rate is the cell rate. -/
theorem contr_of_orthCells {π : α → ℝ} {K : Matrix α α ℝ} (hπ : ∀ x, 0 ≤ π x) {ρc : ℝ}
    (hρc : 0 ≤ ρc) (hG : CellGram π K ρc (fun _ _ : ι => (0 : ℝ))) : Contr π K ρc := by
  have h := contr_of_gram hπ hG ⟨fun _ _ => le_rfl, fun _ _ => rfl, fun i => by simp⟩
    (by positivity : 0 ≤ ρc ^ 2 + 0)
  rwa [add_zero, Real.sqrt_sq hρc] at h

/-- **`f(η) ≤ √η`**: `√(ρc² + η) ≤ ρc + √η`. -/
theorem sqrt_add_le {ρc η : ℝ} (hρ : 0 ≤ ρc) (hη : 0 ≤ η) :
    Real.sqrt (ρc ^ 2 + η) ≤ ρc + Real.sqrt η := by
  have hs := Real.sq_sqrt hη
  have h0 := Real.sqrt_nonneg η
  calc Real.sqrt (ρc ^ 2 + η) ≤ Real.sqrt ((ρc + Real.sqrt η) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hρ h0])
    _ = ρc + Real.sqrt η := Real.sqrt_sq (by positivity)

theorem sqrt_lt_one_of {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : Real.sqrt x < 1 := by
  have h := Real.sqrt_lt_sqrt hx0 hx
  rwa [Real.sqrt_one] at h

end Gram

/-! ## 2. (B) from cells -/

/-- The slab rate `√(ρc² + η)` of cells with rate `ρc` and coupling row sum `η`. -/
def cellRate (ρc η : ℝ) : ℝ := Real.sqrt (ρc ^ 2 + η)

theorem cellRate_pos {ρc η : ℝ} (hρc : 0 < ρc) (hη : 0 ≤ η) : 0 < cellRate ρc η :=
  Real.sqrt_pos.2 (by positivity)

theorem cellRate_lt_one {ρc η : ℝ} (hη : 0 ≤ η) (h1 : ρc ^ 2 + η < 1) : cellRate ρc η < 1 :=
  sqrt_lt_one_of (by positivity) h1

/-- **The slab splits into cells**: some finite set of cells with `CellGram` rate `ρc` and a coupling
of row sum at most `η`. -/
def SlabCells (S : Slab) (ρc η : ℝ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → Fin n → ℝ), RowSum c η ∧ CellGram S.π S.K ρc c

theorem contr_of_slabCells {S : Slab} {ρc η : ℝ} (hη : 0 ≤ η) (h : SlabCells S ρc η) :
    Contr S.π S.K (cellRate ρc η) := by
  obtain ⟨n, c, hR, hG⟩ := h
  exact contr_of_gram S.markov.pi_nonneg hG hR (by positivity)

/-- **One cell is the slab itself**: `Contr S.π S.K ρc` gives `SlabCells S ρc 0` with a single cell.
`SlabCells` does not record the size of the cells. -/
theorem slabCells_of_contr {S : Slab} {ρc : ℝ} (h : Contr S.π S.K ρc) : SlabCells S ρc 0 := by
  refine ⟨1, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun _ _ => rfl, fun _ => by simp⟩,
    fun g hg => ⟨fun _ => g, by simp, fun i j hij => absurd (Subsingleton.elim i j) hij,
      fun _ => h.2 g hg, fun i j hij => absurd (Subsingleton.elim i j) hij⟩⟩

/-- **(A_L²) from cells**: one `ρc > 0`, one `η₀ ≥ 0` with `ρc² + η₀ < 1`, at every aperture `m > 0`
and zoom `k ≥ K₀`. `SlabCells` records no cell size or locality: with one cell any uniform
`Contr ρc` satisfies the hypothesis (`slabCells_of_contr`); the content lies in the intended reading
as martingale differences of a cell filtration at side `ℓ`. -/
theorem relFloor_of_cells {S : ℕ → ℕ → Slab} {ρc η₀ : ℝ} {K₀ : ℕ} (hρc : 0 < ρc) (hη : 0 ≤ η₀)
    (h1 : ρc ^ 2 + η₀ < 1) (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k → SlabCells (S m k) ρc η₀) :
    RelFloor S (fun _ => cellRate ρc η₀) (fun _ => K₀) :=
  relFloor_of_contr (fun _ _ => ⟨cellRate_pos hρc hη, cellRate_lt_one hη h1⟩)
    fun m hm k hk => contr_of_slabCells hη (hS m hm k hk)

/-- **(B) from cells**: the same hypotheses and a slab thickness eventually in `(0, T]` give
`RelFloor` and `UniformInAperture` for the floors `relValue (cellRate ρc η₀) τ R`. With one cell any
uniform `Contr ρc` satisfies the hypothesis (`slabCells_of_contr`): it records no cell size or
locality, and the content lies in the intended reading as martingale differences of a cell
filtration at side `ℓ`. -/
theorem uniformInAperture_of_cells {S : ℕ → ℕ → Slab} {ρc η₀ : ℝ} {K₀ : ℕ} (hρc : 0 < ρc)
    (hη : 0 ≤ η₀) (h1 : ρc ^ 2 + η₀ < 1)
    (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k → SlabCells (S m k) ρc η₀) {τ : ℕ → ℝ} {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hτ : ∀ᶠ m in atTop, 0 < τ m ∧ τ m ≤ T) :
    RelFloor S (fun _ => cellRate ρc η₀) (fun _ => K₀) ∧
      UniformInAperture (relValue (fun _ => cellRate ρc η₀) τ R) (fun _ => K₀) := by
  refine ⟨relFloor_of_cells hρc hη h1 hS, ?_⟩
  refine uniformInAperture_of_relFloor K₀ hR (cellRate_pos hρc hη) (cellRate_lt_one hη h1) hT ?_
  filter_upwards [hτ] with m hm
  exact ⟨cellRate_pos hρc hη, le_rfl, hm.1, hm.2, le_rfl⟩

/-- **The fine end from cells**: with the reading of the slab, an observer reading in `(0, R]` and
the volume link, `NoFadeAtFineEnd gLat rLat`. -/
theorem noFade_of_cells {gL : ℕ → ℕ → ℝ} {gLat rLat : ℕ → ℝ} {S : ℕ → ℕ → Slab}
    {ρc η₀ : ℝ} {K₀ : ℕ} (hρc : 0 < ρc) (hη : 0 ≤ η₀) (h1 : ρc ^ 2 + η₀ < 1)
    (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k → SlabCells (S m k) ρc η₀) {τ : ℕ → ℝ} {R T : ℝ}
    (hRead : ReadsSlab gL S τ) (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R) (hT : 0 < T)
    (hτ : ∀ᶠ m in atTop, 0 < τ m ∧ τ m ≤ T) (hV : VolumeLink gL gLat rLat) :
    NoFadeAtFineEnd gLat rLat := by
  refine noFade_of_relFloor K₀ hRead (relFloor_of_cells hρc hη h1 hS) hR hr
    (cellRate_pos hρc hη) (cellRate_lt_one hη h1) hT ?_ hV
  filter_upwards [hτ] with m hm
  exact ⟨cellRate_pos hρc hη, le_rfl, hm.1, hm.2, le_rfl⟩

/-! ## 3. The coupling from the edge cost -/

section Edge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Polynomial shells**: distinct cells are at cell distance at least `1`, and at most `A nᵖ` cells
lie at distance `n` from any cell.

DERIVED: `1` the least distance of two distinct cells. -/
def ShellCount (d : ι → ι → ℕ) (A : ℝ) (p : ℕ) : Prop :=
  (∀ i j, i ≠ j → 1 ≤ d i j) ∧
    ∀ i n, ((((Finset.univ.erase i).filter fun j => d i j = n).card : ℕ) : ℝ) ≤ A * (n : ℝ) ^ p

/-- **The coupling of two cells is bounded by the cost of the flux edges joining them**:
`c_ij ≤ Ke q^{d i j}`, read at `q = edgeRate σ h ℓ`. -/
def FaceEdgeCost (c : ι → ι → ℝ) (d : ι → ι → ℕ) (Ke q : ℝ) : Prop :=
  ∀ i j, i ≠ j → c i j ≤ Ke * q ^ d i j

/-- `Σ_n nᵖ qⁿ`. -/
def edgeSum (p : ℕ) (q : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ p * q ^ n

theorem edgeSum_summable (p : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun n : ℕ => (n : ℝ) ^ p * q ^ n :=
  summable_pow_mul_geometric_of_norm_lt_one p (by rwa [Real.norm_eq_abs, abs_of_nonneg h0])

theorem edgeSum_nonneg (p : ℕ) {q : ℝ} (h0 : 0 ≤ q) : 0 ≤ edgeSum p q :=
  tsum_nonneg fun _ => by positivity

/-- **The edge cost bounds the row sum, independently of the number of cells.** -/
theorem rowSum_le_of_edgeCost {c : ι → ι → ℝ} {d : ι → ι → ℕ} {Ke A q : ℝ} {p : ℕ}
    (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1) (hd : ShellCount d A p)
    (hE : FaceEdgeCost c d Ke q) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, c i j ≤ Ke * A * edgeSum p q := by
  calc ∑ j ∈ Finset.univ.erase i, c i j
      ≤ ∑ j ∈ Finset.univ.erase i, Ke * q ^ d i j :=
        Finset.sum_le_sum fun j hj => hE i j (Ne.symm (Finset.ne_of_mem_erase hj))
    _ = Ke * ∑ j ∈ Finset.univ.erase i, q ^ d i j := by rw [Finset.mul_sum]
    _ = Ke * ∑ n ∈ (Finset.univ.erase i).image (d i),
          ((((Finset.univ.erase i).filter fun j => d i j = n).card : ℕ) : ℝ) * q ^ n := by
        rw [Finset.sum_comp (fun n => q ^ n) (d i)]
        simp only [nsmul_eq_mul]
    _ ≤ Ke * ∑ n ∈ (Finset.univ.erase i).image (d i), A * ((n : ℝ) ^ p * q ^ n) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hKe
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hd.2 i n) (pow_nonneg hq0 n)
    _ = Ke * A * ∑ n ∈ (Finset.univ.erase i).image (d i), (n : ℝ) ^ p * q ^ n := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ Ke * A * edgeSum p q :=
        mul_le_mul_of_nonneg_left
          ((edgeSum_summable p hq0 hq1).sum_le_tsum _ fun n _ => by positivity)
          (mul_nonneg hKe hA)

/-- **The edge sum scales with `q`**: `q₀ edgeSum p q ≤ q edgeSum p q₀` for `p ≥ 1`, `0 ≤ q ≤ q₀ < 1`.

DERIVED: `1` the least shell exponent, so that the `n = 0` term vanishes. -/
theorem edgeSum_le_scale {p : ℕ} (hp : 1 ≤ p) {q q₀ : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q₀)
    (hq₀1 : q₀ < 1) : q₀ * edgeSum p q ≤ q * edgeSum p q₀ := by
  have hq₀ : 0 ≤ q₀ := hq0.trans hqq
  unfold edgeSum
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((edgeSum_summable p hq0 (hqq.trans_lt hq₀1)).mul_left _)
    ((edgeSum_summable p hq₀ hq₀1).mul_left _)
  rcases n with _ | n
  · simp [zero_pow (show p ≠ 0 by omega)]
  · have h : q ^ n ≤ q₀ ^ n := pow_le_pow_left₀ hq0 hqq n
    have hnp : 0 ≤ (((n + 1 : ℕ) : ℝ)) ^ p := by positivity
    rw [pow_succ, pow_succ]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hq0 hq₀) hnp) (sub_nonneg.2 h)]

/-- **A small enough `q` makes the row sum as small as wanted.**

DERIVED: `1/2` the reference ratio `q₀`; `2` its inverse. -/
theorem exists_small_edge {p : ℕ} (hp : 1 ≤ p) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ q₁ : ℝ, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q, 0 ≤ q → q ≤ q₁ → C * edgeSum p q ≤ ε := by
  have hE : 0 ≤ edgeSum p (1 / 2) := edgeSum_nonneg p (by norm_num)
  have hCE : 0 ≤ C * edgeSum p (1 / 2) := mul_nonneg hC hE
  refine ⟨min (1 / 2) (ε / (2 * (C * edgeSum p (1 / 2) + 1))), lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num), fun q hq0 hq => ?_⟩
  have hq2 : q ≤ 1 / 2 := hq.trans (min_le_left _ _)
  have hqε : q ≤ ε / (2 * (C * edgeSum p (1 / 2) + 1)) := hq.trans (min_le_right _ _)
  have hs := edgeSum_le_scale hp hq0 hq2 (by norm_num)
  have h1 : C * edgeSum p q ≤ 2 * q * (C * edgeSum p (1 / 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left hs hC]
  have hq' : q * (2 * (C * edgeSum p (1 / 2) + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).1 hqε
  have h2 : 2 * q * (C * edgeSum p (1 / 2)) ≤ ε := by
    nlinarith [mul_nonneg hq0 hCE]
  linarith

/-- **A large enough tension makes the edge factor small**: `σ ≥ h + (−log q₁)/ℓ` gives
`edgeRate σ h ℓ ≤ q₁`. -/
theorem edgeRate_le_of_sigma {σ h ℓ q₁ : ℝ} (hℓ : 0 < ℓ) (hq₁ : 0 < q₁)
    (hσ : h + -Real.log q₁ / ℓ ≤ σ) : edgeRate σ h ℓ ≤ q₁ := by
  unfold edgeRate
  rw [← Real.exp_log hq₁]
  refine Real.exp_le_exp.2 ?_
  have h1 : -Real.log q₁ / ℓ ≤ σ - h := by linarith
  rw [div_le_iff₀ hℓ] at h1
  linarith

/-- **A tension threshold closes the cell bound**: for `ρc < 1`, `p ≥ 1`, `ℓ > 0` there is `σ₁ > h`
such that every `σ₀ ≥ σ₁` gives `ρc² + Ke A edgeSum p (edgeRate σ₀ h ℓ) < 1`.

DERIVED: `2` the half of the margin `1 − ρc²` given to the coupling. -/
theorem exists_sigma_threshold {ρc Ke A h ℓ : ℝ} {p : ℕ} (hp : 1 ≤ p) (hρ0 : 0 ≤ ρc)
    (hρ1 : ρc < 1) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hℓ : 0 < ℓ) :
    ∃ σ₁ : ℝ, h < σ₁ ∧ ∀ σ₀, σ₁ ≤ σ₀ → ρc ^ 2 + Ke * A * edgeSum p (edgeRate σ₀ h ℓ) < 1 := by
  have hm : 0 < (1 - ρc ^ 2) / 2 := by nlinarith
  obtain ⟨q₁, hq₁0, hq₁1, hsmall⟩ := exists_small_edge hp (mul_nonneg hKe hA) hm
  have hlog : 0 < -Real.log q₁ := neg_pos.2 (Real.log_neg hq₁0 hq₁1)
  refine ⟨h + -Real.log q₁ / ℓ, by linarith [div_pos hlog hℓ], fun σ₀ hσ₀ => ?_⟩
  have hq := edgeRate_le_of_sigma hℓ hq₁0 hσ₀
  have := hsmall _ (edgeRate_nonneg σ₀ h ℓ) hq
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A larger edge factor keeps the face bound. -/
theorem faceEdgeCost_mono {c : ι → ι → ℝ} {d : ι → ι → ℕ} {Ke q q' : ℝ} (hKe : 0 ≤ Ke)
    (hq0 : 0 ≤ q) (hqq : q ≤ q') (h : FaceEdgeCost c d Ke q) : FaceEdgeCost c d Ke q' :=
  fun i j hij => (h i j hij).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hqq _) hKe)

/-- **A cross-term floor gives a row sum growing with the number of cells**: `c_ij ≥ c₀` for all
`i ≠ j` on `n` cells gives `Σ_{j ≠ i} c_ij ≥ c₀ (n − 1)`.

DERIVED: `1` the cell itself, left out of its row. -/
theorem rowSum_ge_of_floor {n : ℕ} {c : Fin n → Fin n → ℝ} {c₀ : ℝ}
    (h : ∀ i j, i ≠ j → c₀ ≤ c i j) (i : Fin n) :
    c₀ * ((n : ℝ) - 1) ≤ ∑ j ∈ Finset.univ.erase i, c i j := by
  have hn : 1 ≤ n := Fin.pos i
  have hcard : (((Finset.univ.erase i).card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hn, Nat.cast_one]
  calc c₀ * ((n : ℝ) - 1) = ∑ _j ∈ Finset.univ.erase i, c₀ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
    _ ≤ ∑ j ∈ Finset.univ.erase i, c i j :=
        Finset.sum_le_sum fun j hj => h i j (Ne.symm (Finset.ne_of_mem_erase hj))

/-- **Without decay no coupling bound serves every number of cells**: for `c₀ > 0` and every `η`,
from some number of cells on, no coupling with cross terms at least `c₀` has row sum at most `η`.

DERIVED: `2` so that `n − 1 ≥ ⌈η/c₀⌉ + 1 > η/c₀`. -/
theorem free_edge_no_uniform {c₀ : ℝ} (hc₀ : 0 < c₀) (η : ℝ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ c : Fin n → Fin n → ℝ, (∀ i j, i ≠ j → c₀ ≤ c i j) →
      ¬ RowSum c η := by
  refine ⟨⌈η / c₀⌉₊ + 2, fun n hn c hc hR => ?_⟩
  have hn1 : 0 < n := by omega
  have h := (rowSum_ge_of_floor hc ⟨0, hn1⟩).trans (hR.2.2 ⟨0, hn1⟩)
  have hceil : η / c₀ ≤ (⌈η / c₀⌉₊ : ℝ) := Nat.le_ceil _
  have hnR : ((⌈η / c₀⌉₊ + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hnR
  have hlt : η / c₀ < (n : ℝ) - 1 := by linarith
  rw [div_lt_iff₀ hc₀] at hlt
  nlinarith

end Edge

/-- **The edge cells of a slab**: a finite set of cells with `CellGram` rate `ρc`, a symmetric
coupling `c ≥ 0`, polynomial shells `ShellCount d A p`, and the face bound `FaceEdgeCost c d Ke q`. -/
def EdgeCells (S : Slab) (ρc Ke A : ℝ) (p : ℕ) (q : ℝ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → Fin n → ℝ) (d : Fin n → Fin n → ℕ), (∀ i j, 0 ≤ c i j) ∧
    (∀ i j, c i j = c j i) ∧ ShellCount d A p ∧ FaceEdgeCost c d Ke q ∧ CellGram S.π S.K ρc c

/-- **Edge cells are cells** with row sum `Ke A edgeSum p q`. -/
theorem slabCells_of_edgeCells {S : Slab} {ρc Ke A q : ℝ} {p : ℕ} (hKe : 0 ≤ Ke) (hA : 0 ≤ A)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (h : EdgeCells S ρc Ke A p q) :
    SlabCells S ρc (Ke * A * edgeSum p q) := by
  obtain ⟨n, c, d, hc0, hsymm, hd, hE, hG⟩ := h
  exact ⟨n, c, ⟨hc0, hsymm, fun i => rowSum_le_of_edgeCost hKe hA hq0 hq1 hd hE i⟩, hG⟩

/-- **One cell carries no edge structure**: a slab rate `Contr ρc` gives `EdgeCells S ρc Ke 0 p q` at
every `Ke`, `p`, `q`, with one cell and empty shells. `EdgeCells` carries no locality. -/
theorem edgeCells_of_contr {S : Slab} {ρc : ℝ} (h : Contr S.π S.K ρc) (Ke : ℝ) (p : ℕ) (q : ℝ) :
    EdgeCells S ρc Ke 0 p q := by
  refine ⟨1, fun _ _ => 0, fun _ _ => 1, fun _ _ => le_rfl, fun _ _ => rfl,
    ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, fun i n => ?_⟩,
    fun i j hij => absurd (Subsingleton.elim i j) hij,
    fun g hg => ⟨fun _ => g, by simp, fun i j hij => absurd (Subsingleton.elim i j) hij,
      fun _ => h.2 g hg, fun i j hij => absurd (Subsingleton.elim i j) hij⟩⟩
  rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun j hj =>
    absurd (Subsingleton.elim j i) (Finset.ne_of_mem_erase hj))]
  simp

/-- A larger edge factor keeps the edge cells. -/
theorem edgeCells_mono {S : Slab} {ρc Ke A q q' : ℝ} {p : ℕ} (hKe : 0 ≤ Ke) (hq0 : 0 ≤ q)
    (hqq : q ≤ q') (h : EdgeCells S ρc Ke A p q) : EdgeCells S ρc Ke A p q' := by
  obtain ⟨n, c, d, hc0, hsymm, hd, hE, hG⟩ := h
  exact ⟨n, c, d, hc0, hsymm, hd, faceEdgeCost_mono hKe hq0 hqq hE, hG⟩

/-- **(B) from the edge cost.** At every aperture `m > 0` and zoom `k ≥ K₀` the slab has edge cells
with `q = edgeRate (σ m k) h ℓ` and one `(ρc, Ke, A, p, ℓ, h)`; the tension has the floor
`σ m k ≥ σ₀ > h`; and `ρc² + Ke A edgeSum p (edgeRate σ₀ h ℓ) < 1`. Then `RelFloor` holds and the
floors satisfy (B). `EdgeCells` records no cell size or locality: with one cell and `A = 0` any
uniform `Contr ρc` satisfies the hypothesis (`edgeCells_of_contr`); the content lies in the intended
reading as martingale differences of a cell filtration at side `ℓ`, with `d` the cell metric. -/
theorem uniformAperture_of_edgeCost {S : ℕ → ℕ → Slab} {σ : ℕ → ℕ → ℝ} {ρc Ke A σ₀ h ℓ : ℝ}
    {p K₀ : ℕ} (hρc : 0 < ρc) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hℓ : 0 < ℓ) (hσ₀ : h < σ₀)
    (hσ : ∀ m, 0 < m → ∀ k, K₀ ≤ k → σ₀ ≤ σ m k) (h1 : ρc ^ 2 + Ke * A * edgeSum p (edgeRate σ₀ h ℓ) < 1)
    (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k → EdgeCells (S m k) ρc Ke A p (edgeRate (σ m k) h ℓ))
    {τ : ℕ → ℝ} {R T : ℝ} (hR : 0 < R) (hT : 0 < T) (hτ : ∀ᶠ m in atTop, 0 < τ m ∧ τ m ≤ T) :
    RelFloor S (fun _ => cellRate ρc (Ke * A * edgeSum p (edgeRate σ₀ h ℓ))) (fun _ => K₀) ∧
      UniformInAperture
        (relValue (fun _ => cellRate ρc (Ke * A * edgeSum p (edgeRate σ₀ h ℓ))) τ R)
        (fun _ => K₀) := by
  have hq0 := edgeRate_nonneg σ₀ h ℓ
  have hq1 := edgeRate_lt_one hσ₀ hℓ
  have hη : 0 ≤ Ke * A * edgeSum p (edgeRate σ₀ h ℓ) :=
    mul_nonneg (mul_nonneg hKe hA) (edgeSum_nonneg p hq0)
  refine uniformInAperture_of_cells hρc hη h1 (fun m hm k hk => ?_) hR hT hτ
  exact slabCells_of_edgeCells hKe hA hq0 hq1
    (edgeCells_mono hKe (edgeRate_nonneg _ _ _)
      (MassGap.EdgeCost.edgeRate_le_of_sigma_ge (hσ m hm k hk) hℓ.le) (hS m hm k hk))

#print axioms nsq_sum_orth
#print axioms ip_le_of_sq
#print axioms offdiag_sum_le
#print axioms nsq_sum_le_gram
#print axioms contr_of_gram
#print axioms contr_of_orthCells
#print axioms sqrt_add_le
#print axioms sqrt_lt_one_of
#print axioms contr_of_slabCells
#print axioms slabCells_of_contr
#print axioms relFloor_of_cells
#print axioms uniformInAperture_of_cells
#print axioms noFade_of_cells
#print axioms rowSum_le_of_edgeCost
#print axioms edgeSum_le_scale
#print axioms exists_small_edge
#print axioms edgeRate_le_of_sigma
#print axioms exists_sigma_threshold
#print axioms rowSum_ge_of_floor
#print axioms free_edge_no_uniform
#print axioms slabCells_of_edgeCells
#print axioms edgeCells_of_contr
#print axioms edgeCells_mono
#print axioms uniformAperture_of_edgeCost

end MassGap.UniformAperture
