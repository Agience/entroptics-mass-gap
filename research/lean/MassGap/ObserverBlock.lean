import Mathlib
import MassGap.ObserverMultigrid

/-!
# MassGap.ObserverBlock — the ray-averaged multigrid observer

`ObserverMultigrid.mgFam` smooths with global strided steps whose stride-`d` staple is one thin `d × 1`
rectangle: per transverse direction two support points at distance `±d`, no average across the block, and
at the coarsest level one long thin loop carries the full edge weight. This module replaces that staple by
an average along each transverse ray: the `t × 1` staples at offsets `t = 1, …, d`. There is no average
along `μ`, over transverse blocks, or within the legs, so each staple is still a thin `t × 1` loop. Declarations are in the namespace `MassGap.ObserverBlock`.

## 1. The averaged block step

`blockMatI e W S = W + e Σᵢ Sᵢ` for a finite family `S : ι → SU(N)`; with `2 · #ι · e < sin(π/N)` its
determinant lies in the slit plane (`det_blockMatI_mem_slitPlane`, the proof of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane` with `6` replaced by `#ι`), and `avgStepI` projects it to
`SU(N)` by `ObserverFlowSUN.projMat`. It is continuous (`continuous_avgStepI`), gauge covariant
(`avgStepI_gauge`), compatible with inversion (`avgStepI_inv`) and blind to the order of the family
(`avgStepI_perm`).

## 2. The block step at stride `d`

`blStaples U d l` is the family indexed by `Fin 6 × Fin d`: for each transverse direction and side
(`Fin 6 = Fin 3 × Fin 2`) and each transverse offset `t = 1, …, d`, the `t × 1` staple
`ObserverMultigrid.stapleD U t`. `blStep … d` replaces every link `l` by
`avgStepI (U l) (blStaples U d l)` with weight `e_d = c/d` per staple, so the total staple weight is `6c`
at every stride (`avg_coupling`: `2 · 6d · (c/d) = 12c < sin(π/N)`). No link is held fixed. Proved: gauge
covariance (`blStep_gauge`; every averaged staple is a gauge-covariant path from `x` to `x + μ̂`), time
reflection covariance (`blStep_refl`; sides swapped by `ReflApe.stapleSwap` in the first factor of the
index, offsets unchanged), continuity (`continuous_blStep`), and the output at a link reads only links
whose base lies within `d` of it in every coordinate (`blStep_reads`; offsets are at most `d`).

## 3. The multigrid map and the family

`blMap m J = (blStep 2^{J−1})^[m] ∘ ⋯ ∘ (blStep 1)^[m]` reads within `ObserverMultigrid.mgRange m J`
(`blMap_reads`), and is gauge covariant, reflection covariant and continuous. `blConfFlow` is the
`ContinuumFlow.ConfFlow` with `V k = blMap m (J k)`; `blFam hN c hc0 hc m s` takes the level count
`J_k = ObserverMultigrid.mgLevels N m s k = log₂ ⌊s/(m a_k)⌋`, as `mgFam` does. Proved:

* **`blFam_physRange`**: `(CompositeLink.Φ0 (blFam … m s)).PhysRange r` at every `r ≥ s ≥ 0`
  (`ObserverMultigrid.spacing_mul_mgRange_le`).
* `blFam_V_of_lt`: the identity at a step with `0 ≤ s < 2 m a_k`.
* **`blFam_moves`**: for `c > 0`, `m ≥ 1` and a step with `J_k ≥ 1`, `V k` moves a configuration.
* **`blFam_not_eventually_id`**: for `c > 0`, `m ≥ 1`, `s > 0`: `¬ ∀ᶠ k, (blFam … m s).V k = id`
  (eventually `J_k ≥ 1`, since `a_k → 0`). `ScaleIdentityNoGo.not_substrateCoreAt_of_id` refutes the
  substrate core at any observer with `∀ᶠ k, V k = id`; that hypothesis is false at `blFam`.

**How the non-identity is proved.** On a configuration whose links are `D(z) = diag(z, z̄, 1, …, 1)`,
`z ∈ U(1)`, every staple is again of that form and the block matrix is `diag(w, w̄, r, …, r)` with `r > 0`,
whose projection is `D(w/|w|)` (`projMat_dv`, `avgStepI_dg`): the step acts as the compact `U(1)` average
`z ↦ (z + e Σ zᵢ)/|z + e Σ zᵢ|` (`blStep_dg`). On the slice configurations `zeta f` (direction-`1` links
`D(f(x₀))`, every other link `1`) the staples of a direction-`1` link are values of `f`, and the staples of
any other link come in inverse pairs (`stapleD_zeta_inv`), so its block matrix is real positive and it stays
`1` (`u1Step_zeta`). The step is then a one-dimensional average `f ↦ Fz e d f`. It keeps every `f(y)` in the
closed first quadrant (`Fz_quad`) and keeps `Re f(0) > 0` (`Fz_pos`), and at stride `1` it makes
`Re f(0) > 0` from `f(1) = 1` (`Fz_first`). The configuration `f₀ = i` off `y = 1`, `f₀(1) = 1` has
`Re f₀(0) = 0`; every `blMap m J` with `J ≥ 1`, `m ≥ 1` sends it to a slice configuration with
`Re f(0) > 0` (`blMap_moves`), so not to itself.

## 4. Why the averaged staple smooths at width `s` (argued, not a declaration)

Linearise at the unit configuration, `U = exp(i a A)`. One step at stride `d` replaces `A_μ(x)` by
`(A_μ(x) + (c/d) Σ_{ν,±} Σ_{t=1}^{d} [A_μ(x ± tν̂) + (leg terms)]) / (1 + 6c)` to first order: the field is
convolved with a sum over the three transverse axes of one-axis box kernels on offsets `±1, …, ±d` (mass `2c`
each),
mixed with weight `6c/(1+6c)`. The variance added per step is `≍ c d²` lattice units; `m` steps at strides
`2^j`, `j < J`, add `≍ m c Σ_j 4^j ≍ m c 4^{J}` — a geometric sum dominated by the coarsest level, with
`2^J ≤ s/(m a)`, so the physical width is `≍ s √(c/m)`, of order `s` and never more than the light cone `s`.
The thin staple of `mgFam` has the same weight on two points at `±d` only: its linear kernel at the coarsest
level is a sparse two-point comb, not a block average. Along the link direction the field `A_μ` is not
averaged by its own staples; it is the staples of the transverse links that average along `μ`, and the leg
terms couple the directions. None of this is proved here: no declaration bounds the kernel, the non-linear
step, or its fluctuations.

## 5. The scale input at this observer (stated, open)

`blFam_mw_iff`: a family with `Wf 1 = blFam …` meeting `ScaleControlAll 1` exists iff
`ObserverMultigrid.MW (blFam …)`, the observer's moment condition `(M_W)`. Because one constant covers
the channels of every dimension, `MW` is a deterministic bound on the flowed origin plaquette at every input
(`BulkBound.facV_le_of_MW`), and it is false at `blFam`: the π-flux slice is a fixed point of every level
(`BulkBound.not_MW_blFam`). The structural obstruction of `ScaleIdentityNoGo`
(an observer that is eventually the identity) does not apply, by `blFam_not_eventually_id`.
`SunFamLeak.not_substrateCoreAt_of_plaqLeak` refutes the substrate core at `blFam` if `PlaqLeak (blFam …)`
holds; that is not decided here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the origin, the reflection plane, the empty sum; `1` the unit configuration, the
least stride and offset, the direction of the slice links; `2` the stride ratio and the least rank; `4` the
dimension; `6 = 3 · 2` the staple directions and sides; `12 = 2 · 6` the coupling bound; `π/2` the angle of
`i`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverBlock

open MassGap.SUN (SU)
open MassGap.InfiniteLattice MassGap.BlockLattice MassGap.ReflApe MassGap.LatticeReflection
  MassGap.GaugeInvariantAlgebra MassGap.ObserverFlow MassGap.ObserverFlowSUN MassGap.ObserverMultigrid

/-! ## 1. The averaged block step -/

section Avg

open Matrix
open scoped ComplexOrder

variable {N : ℕ} {ι : Type} [Fintype ι]

/-- **The averaged block matrix**: the link plus `e` times the sum of a finite family of staples.
DERIVED: no numeral. -/
def blockMatI (e : ℝ) (W : SU N) (S : ι → SU N) : Matrix (Fin N) (Fin N) ℂ :=
  (W : Matrix (Fin N) (Fin N) ℂ) + (e : ℂ) • ∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)

/-- The staple part relative to the link, `e Wᴴ Σ Sᵢ`. DERIVED: no numeral. -/
def stapleRelI (e : ℝ) (W : SU N) (S : ι → SU N) : Matrix (Fin N) (Fin N) ℂ :=
  (e : ℂ) • ((W : Matrix (Fin N) (Fin N) ℂ)ᴴ * ∑ i, (S i : Matrix (Fin N) (Fin N) ℂ))

/-- `W + e Σ Sᵢ = W (1 + e Wᴴ Σ Sᵢ)`. DERIVED: `1` the identity. -/
theorem blockMatI_eq (e : ℝ) (W : SU N) (S : ι → SU N) :
    blockMatI e W S = (W : Matrix (Fin N) (Fin N) ℂ) * (1 + stapleRelI e W S) := by
  have hWW : (W : Matrix (Fin N) (Fin N) ℂ) * (W : Matrix (Fin N) (Fin N) ℂ)ᴴ = 1 :=
    mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp W.2).1
  rw [blockMatI, stapleRelI, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hWW,
    Matrix.one_mul]

open scoped Matrix.Norms.L2Operator in
/-- **Every eigenvalue of the relative staple part has modulus at most `#ι · e`.**
DERIVED: `1` the norm of a unitary matrix and the least `N`. -/
theorem norm_spectrum_stapleRelI_le (hN : 1 ≤ N) {e : ℝ} (he0 : 0 ≤ e) (W : SU N)
    (S : ι → SU N) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (stapleRelI e W S)) :
    ‖μ‖ ≤ (Fintype.card ι : ℝ) * e := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  haveI : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℂ _
  have h1 := spectrum.norm_le_norm_mul_of_mem hμ
  rw [CStarRing.norm_one, mul_one] at h1
  have hW : ‖(W : Matrix (Fin N) (Fin N) ℂ)ᴴ‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Unitary.star_mem (mem_specialUnitaryGroup_iff.mp W.2).1)
  have hS : ‖∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖ ≤ Fintype.card ι := by
    calc ‖∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖
        ≤ ∑ i, ‖(S i : Matrix (Fin N) (Fin N) ℂ)‖ := norm_sum_le _ _
      _ = ∑ _i : ι, (1 : ℝ) := Finset.sum_congr rfl fun i _ =>
          CStarRing.norm_of_mem_unitary (mem_specialUnitaryGroup_iff.mp (S i).2).1
      _ = Fintype.card ι := by simp
  have h2 : ‖stapleRelI e W S‖ ≤ (Fintype.card ι : ℝ) * e := by
    rw [stapleRelI, norm_smul, Complex.norm_of_nonneg he0]
    calc e * ‖(W : Matrix (Fin N) (Fin N) ℂ)ᴴ * ∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖
        ≤ e * (‖(W : Matrix (Fin N) (Fin N) ℂ)ᴴ‖ * ‖∑ i, (S i : Matrix (Fin N) (Fin N) ℂ)‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) he0
      _ ≤ e * (1 * Fintype.card ι) := by
          rw [hW]; exact mul_le_mul_of_nonneg_left (by linarith) he0
      _ = (Fintype.card ι : ℝ) * e := by ring
  linarith

/-- **Every eigenvalue of `1 + A` lies within `#ι · e` of `1`.** DERIVED: `1` the identity. -/
theorem norm_sub_one_le_of_rootI (hN : 1 ≤ N) {e : ℝ} (he0 : 0 ≤ e) (W : SU N) (S : ι → SU N)
    {z : ℂ} (hz : z ∈ (charpoly (1 + stapleRelI e W S)).roots) :
    ‖z - 1‖ ≤ (Fintype.card ι : ℝ) * e := by
  have h1 : z ∈ spectrum ℂ (1 + stapleRelI e W S) :=
    mem_spectrum_iff_isRoot_charpoly.mpr ((Polynomial.mem_roots (charpoly_monic _).ne_zero).mp hz)
  have h2 : z - 1 ∈ spectrum ℂ (stapleRelI e W S) := by
    rw [spectrum.mem_iff] at h1 ⊢
    have e' : algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) (z - 1) - stapleRelI e W S
        = algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ) z - (1 + stapleRelI e W S) := by
      rw [map_sub, map_one]; abel
    rw [e']; exact h1
  exact norm_spectrum_stapleRelI_le hN he0 W S h2

/-- **The determinant of the averaged block matrix lies in the slit plane** for `N ≥ 2`, `0 ≤ e` and
`2 · #ι · e < sin(π/N)`: the proof of `ObserverFlowSUN.det_blockMatN_mem_slitPlane` with the staple count
`#ι`.
DERIVED: `2` the least rank and the ratio bound; `π / N` the share of the half-turn per eigenvalue. -/
theorem det_blockMatI_mem_slitPlane (hN : 2 ≤ N) {e : ℝ} (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / N)) (W : SU N) (S : ι → SU N) :
    (blockMatI e W S).det ∈ Complex.slitPlane := by
  have hK0 : 0 ≤ (Fintype.card ι : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsin1 : Real.sin (Real.pi / N) ≤ 1 := Real.sin_le_one _
  have hδ : (Fintype.card ι : ℝ) * e ≤ 1 / 2 := by linarith
  have hπN : Real.pi / N ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hN2
  have hπN0 : 0 < Real.pi / N := div_pos Real.pi_pos hN0
  have hα0 : 0 ≤ Real.arcsin (2 * ((Fintype.card ι : ℝ) * e)) :=
    Real.arcsin_nonneg.mpr (by linarith)
  have hαlt : Real.arcsin (2 * ((Fintype.card ι : ℝ) * e)) < Real.pi / N := by
    rw [Real.arcsin_lt_iff_lt_sin ⟨by linarith, by linarith⟩ ⟨by linarith, hπN⟩]
    linarith
  have hroots : ∀ z ∈ (charpoly (1 + stapleRelI e W S)).roots,
      z ≠ 0 ∧ |Complex.arg z| ≤ Real.arcsin (2 * ((Fintype.card ι : ℝ) * e)) :=
    fun z hz => arg_bound hδ (norm_sub_one_le_of_rootI (by omega) he0 W S hz)
  have hcard : (Multiset.card (charpoly (1 + stapleRelI e W S)).roots : ℝ) ≤ N := by
    have := Polynomial.card_roots' (charpoly (1 + stapleRelI e W S))
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  have hlt : (Multiset.card (charpoly (1 + stapleRelI e W S)).roots : ℝ)
      * Real.arcsin (2 * ((Fintype.card ι : ℝ) * e)) < Real.pi := by
    calc _ ≤ (N : ℝ) * Real.arcsin (2 * ((Fintype.card ι : ℝ) * e)) :=
          mul_le_mul_of_nonneg_right hcard hα0
      _ < N * (Real.pi / N) := mul_lt_mul_of_pos_left hαlt hN0
      _ = Real.pi := by field_simp
  obtain ⟨hne, harg⟩ := multiset_prod_arg hα0 _ hroots hlt
  have hdet : (blockMatI e W S).det = (charpoly (1 + stapleRelI e W S)).roots.prod := by
    rw [blockMatI_eq, det_mul, (mem_specialUnitaryGroup_iff.mp W.2).2, one_mul,
      det_eq_prod_roots_charpoly]
  rw [hdet, Complex.mem_slitPlane_iff_arg]
  refine ⟨fun hπ => ?_, hne⟩
  rw [hπ, abs_of_pos Real.pi_pos] at harg
  linarith

/-- **The averaged block step**: the projection of `W + e Σ Sᵢ` to `SU(N)`.
DERIVED: `2` the least rank and the ratio bound. -/
def avgStepI (hN : 2 ≤ N) (e : ℝ) (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / N)) (W : SU N) (S : ι → SU N) : SU N :=
  ⟨projMat (blockMatI e W S), mem_specialUnitaryGroup_iff.mpr
    ⟨projMat_mem_unitary (Complex.slitPlane_ne_zero (det_blockMatI_mem_slitPlane hN he0 he W S)),
     det_projMat (by omega) (Complex.slitPlane_ne_zero (det_blockMatI_mem_slitPlane hN he0 he W S))⟩⟩

/-- **The averaged block step is continuous** in the link and the family.
DERIVED: `2` the least rank. -/
theorem continuous_avgStepI (hN : 2 ≤ N) {e : ℝ} (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / N)) :
    Continuous (fun p : SU N × (ι → SU N) => avgStepI hN e he0 he p.1 p.2) := by
  have hX : Continuous (fun p : SU N × (ι → SU N) => blockMatI e p.1 p.2) := by
    unfold blockMatI
    refine (continuous_subtype_val.comp continuous_fst).add (continuous_const.smul ?_)
    exact continuous_finsetSum _ (fun i _ =>
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  have hslit := fun p : SU N × (ι → SU N) => det_blockMatI_mem_slitPlane hN he0 he p.1 p.2
  have hpolar := continuous_polar_comp hX (fun p => Complex.slitPlane_ne_zero (hslit p))
  have harg : Continuous (fun p : SU N × (ι → SU N) => Complex.arg (blockMatI e p.1 p.2).det) :=
    continuous_iff_continuousAt.mpr fun p =>
      (Complex.continuousAt_arg (hslit p)).comp
        (f := fun p : SU N × (ι → SU N) => (blockMatI e p.1 p.2).det)
        hX.matrix_det.continuousAt
  have hphase : Continuous (fun p : SU N × (ι → SU N) => phase (blockMatI e p.1 p.2)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (harg.div_const (N : ℝ)).neg).mul continuous_const)
  exact (hphase.smul hpolar).subtype_mk _

/-- The averaged block matrix of gauge-transformed inputs. DERIVED: no numeral. -/
theorem blockMatI_gauge (e : ℝ) (g h W : SU N) (S : ι → SU N) :
    blockMatI e (g * W * h⁻¹) (fun i => g * S i * h⁻¹)
      = (g : Matrix (Fin N) (Fin N) ℂ) * blockMatI e W S * ((h⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  unfold blockMatI
  simp only [Submonoid.coe_mul]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul]

/-- The averaged block matrix of inverted inputs is the adjoint. DERIVED: no numeral. -/
theorem blockMatI_inv (e : ℝ) (W : SU N) (S : ι → SU N) :
    blockMatI e W⁻¹ (fun i => (S i)⁻¹) = star (blockMatI e W S) := by
  unfold blockMatI
  rw [star_add, star_smul, star_sum, Complex.star_def, Complex.conj_ofReal]
  rfl

/-- **The averaged block step is gauge covariant.** DERIVED: `2` the least rank. -/
theorem avgStepI_gauge (hN : 2 ≤ N) {e : ℝ} (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / N)) (g h W : SU N) (S : ι → SU N) :
    avgStepI hN e he0 he (g * W * h⁻¹) (fun i => g * S i * h⁻¹) = g * avgStepI hN e he0 he W S * h⁻¹ := by
  apply Subtype.ext
  show projMat (blockMatI e (g * W * h⁻¹) (fun i => g * S i * h⁻¹))
    = (g : Matrix (Fin N) (Fin N) ℂ) * projMat (blockMatI e W S)
      * ((h⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ)
  rw [blockMatI_gauge, coe_inv_SU,
    projMat_gauge (Complex.slitPlane_ne_zero (det_blockMatI_mem_slitPlane hN he0 he W S)) g.2 h.2]

/-- **The averaged block step commutes with inversion.** DERIVED: `2` the least rank. -/
theorem avgStepI_inv (hN : 2 ≤ N) {e : ℝ} (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / N)) (W : SU N) (S : ι → SU N) :
    avgStepI hN e he0 he W⁻¹ (fun i => (S i)⁻¹) = (avgStepI hN e he0 he W S)⁻¹ := by
  apply Subtype.ext
  show projMat (blockMatI e W⁻¹ (fun i => (S i)⁻¹)) = star (projMat (blockMatI e W S))
  rw [blockMatI_inv]
  exact projMat_conjTranspose (det_blockMatI_mem_slitPlane hN he0 he W S)

/-- **The averaged block step does not depend on the order of the family.** DERIVED: `2` the least
rank. -/
theorem avgStepI_perm (hN : 2 ≤ N) {e : ℝ} (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / N)) (W : SU N) (S : ι → SU N)
    (σ : Equiv.Perm ι) : avgStepI hN e he0 he W (S ∘ σ) = avgStepI hN e he0 he W S := by
  have hM : blockMatI e W (S ∘ σ) = blockMatI e W S := by
    unfold blockMatI
    congr 2
    exact Equiv.sum_comp σ (fun i => (S i : Matrix (Fin N) (Fin N) ℂ))
  apply Subtype.ext
  show projMat (blockMatI e W (S ∘ σ)) = projMat (blockMatI e W S)
  rw [hM]

end Avg

/-! ## 2. Block staples -/

section Staples

variable {G : Type} [Group G]

/-- **The block staples at stride `d`**: for each transverse direction and side (`Fin 6`) and each
transverse offset `t = 1, …, d` (`Fin d`), the `t × 1` staple `stapleD U t`.
DERIVED: `1` the least offset; `6 = 3 · 2` directions and sides. -/
def blStaples (U : IConf G) (d : ℕ) (l : ILink) : Fin 6 × Fin d → G :=
  fun q => stapleD U ((q.2 : ℕ) + 1) l.1 l.2 (finProdFinEquiv.symm q.1)

/-- **Block staples of a gauge transform.** DERIVED: no numeral. -/
theorem blStaples_gauge (g : ISite → G) (U : IConf G) (d : ℕ) (μ : Fin 4) (x : ISite) :
    blStaples (igaugeTransform g U) d (μ, x)
      = fun q => g x * blStaples U d (μ, x) q * (g (ishift μ x))⁻¹ :=
  funext fun _ => stapleD_gauge g U _ μ x _

/-- **Block staples are continuous in the configuration.** DERIVED: no numeral. -/
theorem continuous_blStaples [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) (l : ILink) :
    Continuous (fun U : IConf G => blStaples U d l) :=
  continuous_pi fun _ => continuous_stapleD _ l.1 l.2 _

/-- **Block staples of the reflected configuration at a link not along `τ`**: the original block staples
at the reflected site, sides swapped by `stapleSwap`, offsets unchanged.
DERIVED: `0` the reflection constant. -/
theorem blStaples_refl_ne {τ μ : Fin 4} (hμ : μ ≠ τ) (U : IConf G) (d : ℕ) (x : ISite) :
    blStaples (ireflConf τ 0 U) d (μ, x)
      = blStaples U d (μ, ireflSite τ 0 x) ∘ Equiv.prodCongr (stapleSwap μ τ) (Equiv.refl (Fin d)) := by
  funext q
  simp only [Function.comp_apply, blStaples, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, stapleSwap, Equiv.trans_apply, Equiv.symm_apply_apply,
    Function.Involutive.coe_toPerm]
  exact stapleD_refl_ne hμ U _ x _

/-- **Block staples of the reflected configuration at a `τ`-link**: the inverses of the original block
staples at the reflected link. DERIVED: `0`, `-1` the reflection constants. -/
theorem blStaples_refl_eq (τ : Fin 4) (U : IConf G) (d : ℕ) (x : ISite) :
    blStaples (ireflConf τ 0 U) d (τ, x) = fun q => (blStaples U d (τ, ireflSite τ (-1) x) q)⁻¹ :=
  funext fun _ => stapleD_refl_eq τ U _ x _

/-- **A `t × 1` staple with `t ≤ d` reads only links within `d`.** DERIVED: `0` names the upper side;
`3` the transverse directions in four dimensions. -/
theorem stapleD_local {d t : ℕ} (ht : t ≤ d) (U U' : IConf G) (μ : Fin 4) (x : ISite)
    (h : ∀ (ν : Fin 4) (z : ISite), (∀ i, |z i - x i| ≤ (d : ℤ)) → U (ν, z) = U' (ν, z))
    (p : Fin 3 × Fin 2) : stapleD U t μ x p = stapleD U' t μ x p := by
  unfold stapleD
  split_ifs
  · rw [ptr_agree U U' (other μ p.1) t x (fun i hi => h _ _ (by dist_tac)),
      ptr_agree U U' (other μ p.1) t (ishift μ x) (fun i hi => h _ _ (by dist_tac)),
      h μ (sh (other μ p.1) t x) (by dist_tac)]
  · rw [ptr_agree U U' (other μ p.1) t (sh (other μ p.1) (-(t : ℤ)) x)
        (fun i hi => h _ _ (by dist_tac)),
      ptr_agree U U' (other μ p.1) t (ishift μ (sh (other μ p.1) (-(t : ℤ)) x))
        (fun i hi => h _ _ (by dist_tac)),
      h μ (sh (other μ p.1) (-(t : ℤ)) x) (by dist_tac)]

/-- **Block staples at stride `d` read only links within `d`**: every offset is at most `d`.
DERIVED: `1` the least offset; `6 = 3 · 2` the staple directions and sides. -/
theorem blStaples_local {d : ℕ} (U U' : IConf G) (μ : Fin 4) (x : ISite)
    (h : ∀ (ν : Fin 4) (z : ISite), (∀ i, |z i - x i| ≤ (d : ℤ)) → U (ν, z) = U' (ν, z))
    (q : Fin 6 × Fin d) : blStaples U d (μ, x) q = blStaples U' d (μ, x) q :=
  stapleD_local (Nat.succ_le_of_lt q.2.isLt) U U' μ x h _

end Staples

/-! ## 3. The block step and the multigrid map -/

section Step

variable {N : ℕ}

/-- **The averaged coupling**: `2 · #(Fin 6 × Fin d) · (c/d) < sin(π/N)` at every stride `d`.
DERIVED: `2` the least rank; `12 = 2 · 6`; `6` the directions and sides; `0` the empty family. -/
theorem avg_coupling (hN : 2 ≤ N) {c : ℝ} (hc : 12 * c < Real.sin (Real.pi / N))
    (d : ℕ) : 2 * ((Fintype.card (Fin 6 × Fin d) : ℝ) * (c / d)) < Real.sin (Real.pi / N) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    simpa using Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hN0) (div_lt_self Real.pi_pos hN1)
  · have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    rw [mul_assoc (6 : ℝ), mul_div_cancel₀ c hd']
    linarith

/-- The weight per staple at stride `d` is non-negative. DERIVED: no numeral. -/
theorem avg_weight_nonneg {c : ℝ} (hc0 : 0 ≤ c) (d : ℕ) : 0 ≤ c / d :=
  div_nonneg hc0 (Nat.cast_nonneg d)

/-- **One ray-averaged step at stride `d`**: every link replaced by the averaged block step of itself
and its `6d` block staples, weight `c/d` each. Applied at every link of `ℤ⁴`.
DERIVED: `2` the least rank; `12` the coupling bound. -/
def blStep (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (d : ℕ)
    (U : IConf (SU N)) : IConf (SU N) :=
  fun l => avgStepI hN (c / d) (avg_weight_nonneg hc0 d) (avg_coupling hN hc d) (U l)
    (blStaples U d l)

variable (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))

/-- **The block step is gauge covariant.** DERIVED: no numeral. -/
theorem blStep_gauge (d : ℕ) (g : ISite → SU N) (U : IConf (SU N)) :
    blStep hN c hc0 hc d (igaugeTransform g U) = igaugeTransform g (blStep hN c hc0 hc d U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  show avgStepI hN _ _ _ (g x * U (μ, x) * (g (ishift μ x))⁻¹)
    (blStaples (igaugeTransform g U) d (μ, x)) = _
  rw [blStaples_gauge, avgStepI_gauge]
  rfl

/-- **The block step is continuous.** DERIVED: no numeral. -/
theorem continuous_blStep (d : ℕ) : Continuous (blStep hN c hc0 hc d) := by
  refine continuous_pi (fun l => ?_)
  have hA := continuous_avgStepI (ι := Fin 6 × Fin d) hN (avg_weight_nonneg hc0 d) (avg_coupling hN hc d)
  have hB : Continuous (fun U : IConf (SU N) => (U l, blStaples U d l)) :=
    (continuous_apply l).prodMk (continuous_blStaples (G := SU N) d l)
  have h := hA.comp hB
  exact h

/-- **The block step commutes with the time reflection.**
DERIVED: `0`, `-1` the reflection constants. -/
theorem blStep_refl (d : ℕ) (τ : Fin 4) (U : IConf (SU N)) :
    blStep hN c hc0 hc d (ireflConf τ 0 U) = ireflConf τ 0 (blStep hN c hc0 hc d U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = τ
  · subst hμ
    have hW : ireflConf μ 0 U (μ, x) = (U (μ, ireflSite μ (-1) x))⁻¹ := reflConf_eq μ U x
    have hR : ireflConf μ 0 (blStep hN c hc0 hc d U) (μ, x)
        = (blStep hN c hc0 hc d U (μ, ireflSite μ (-1) x))⁻¹ := reflConf_eq μ _ x
    show avgStepI hN _ _ _ (ireflConf μ 0 U (μ, x)) (blStaples (ireflConf μ 0 U) d (μ, x)) = _
    rw [blStaples_refl_eq, hW, hR, avgStepI_inv]
    rfl
  · have hW : ireflConf τ 0 U (μ, x) = U (μ, ireflSite τ 0 x) := reflConf_ne hμ U x
    have hR : ireflConf τ 0 (blStep hN c hc0 hc d U) (μ, x)
        = blStep hN c hc0 hc d U (μ, ireflSite τ 0 x) := reflConf_ne hμ _ x
    show avgStepI hN _ _ _ (ireflConf τ 0 U (μ, x)) (blStaples (ireflConf τ 0 U) d (μ, x)) = _
    rw [blStaples_refl_ne hμ, hW, hR, avgStepI_perm]
    rfl

/-- **The block step at stride `d` reads within `d`.** DERIVED: no numeral. -/
theorem blStep_reads (d : ℕ) : ReadsWithin (blStep hN c hc0 hc d) d := by
  intro U U' l h
  obtain ⟨μ, x⟩ := l
  have h' : ∀ (ν : Fin 4) (z : ISite), (∀ i, |z i - x i| ≤ (d : ℤ)) → U (ν, z) = U' (ν, z) :=
    fun ν z hz => h (ν, z) hz
  show avgStepI hN _ _ _ (U (μ, x)) (blStaples U d (μ, x))
    = avgStepI hN _ _ _ (U' (μ, x)) (blStaples U' d (μ, x))
  rw [h' μ x (fun i => by simp), funext (blStaples_local U U' μ x h')]

/-- **The ray-averaged multigrid map**: `m` block steps at stride `1`, then `m` at stride `2`, …, then
`m` at stride `2^{J−1}`.
DERIVED: `0` no level; `2` the stride ratio. -/
def blMap (m : ℕ) : ℕ → IConf (SU N) → IConf (SU N)
  | 0 => id
  | J + 1 => (blStep hN c hc0 hc (2 ^ J))^[m] ∘ blMap m J

/-- **The ray-averaged multigrid map reads within `mgRange m J`.** DERIVED: `0` no level. -/
theorem blMap_reads (m J : ℕ) : ReadsWithin (blMap hN hc0 hc m J) (mgRange m J) := by
  induction J with
  | zero => intro U U' l h; exact h l (fun i => by simp [mgRange])
  | succ J ih => exact ih.comp ((blStep_reads hN hc0 hc (2 ^ J)).iterate m)

/-- **The ray-averaged multigrid map is gauge covariant.** DERIVED: no numeral. -/
theorem blMap_gauge (m J : ℕ) (g : ISite → SU N) :
    Function.Commute (blMap hN hc0 hc m J) (igaugeTransform g) := by
  induction J with
  | zero => intro U; rfl
  | succ J ih =>
    have hcm : Function.Commute (blStep hN c hc0 hc (2 ^ J)) (igaugeTransform g) :=
      fun U => blStep_gauge hN hc0 hc _ g U
    exact Function.Commute.comp_left (hcm.iterate_left m) ih

/-- **The ray-averaged multigrid map commutes with the time reflection.**
DERIVED: `0` the reflection constant. -/
theorem blMap_refl (m J : ℕ) (τ : Fin 4) :
    Function.Commute (blMap hN hc0 hc m J) (ireflConf τ 0) := by
  induction J with
  | zero => intro U; rfl
  | succ J ih =>
    have hcm : Function.Commute (blStep hN c hc0 hc (2 ^ J)) (ireflConf τ 0) :=
      fun U => blStep_refl hN hc0 hc _ τ U
    exact Function.Commute.comp_left (hcm.iterate_left m) ih

/-- **The ray-averaged multigrid map is continuous.** DERIVED: no numeral. -/
theorem continuous_blMap (m J : ℕ) : Continuous (blMap hN hc0 hc m J) := by
  induction J with
  | zero => exact continuous_id
  | succ J ih => exact ((continuous_blStep hN hc0 hc _).iterate m).comp ih

end Step

open MassGap.ContinuumFlow MassGap.ContinuumSchwinger Filter

/-- **The ray-averaged observer as a configuration flow**: `V k = blMap m (J k)`, range
`mgRange m (J k)`.
DERIVED: `2` the least rank; `12 = 2 · 6` the coupling bound of `avg_coupling`. -/
def blConfFlow {N : ℕ} (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (m : ℕ) (J : ℕ → ℕ) : ConfFlow N where
  V k := blMap hN hc0 hc m (J k)
  continuous_V k := continuous_blMap hN hc0 hc m (J k)
  gauge k g U := blMap_gauge hN hc0 hc m (J k) g U
  refl k τ U := blMap_refl hN hc0 hc m (J k) τ U
  range k := mgRange m (J k)
  local_V k l := ⟨baseBox l.2 (mgRange m (J k)), fun l' hl' i => by
      rw [mem_baseBox] at hl'
      have := hl' i
      rw [abs_le]
      constructor <;> omega,
    fun U U' h => blMap_reads hN hc0 hc m (J k) U U' l (fun l' hl' => h l' (by
      rw [mem_baseBox]
      intro i
      have := hl' i
      rw [abs_le] at this
      constructor <;> omega))⟩

/-- **The `SU(N)` ray-averaged family**: `m` block steps per level, `mgLevels N m s k` levels at step
`k`. DERIVED: `2` the least rank; `12` the coupling bound. -/
def blFam {N : ℕ} (hN : 2 ≤ N) (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ)
    (s : ℝ) : ConfFlow N :=
  blConfFlow hN c hc0 hc m (mgLevels N m s)

/-- **`PhysRange r` of the member's observer flow `Φ0` at every `r ≥ s ≥ 0`**, at every step.
DERIVED: `0` the lower end of `s`; `2` the least rank; `12 = 2 · 6` the coupling bound of
`avg_coupling`. -/
theorem blFam_physRange {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s r : ℝ} (hs0 : 0 ≤ s) (hr : s ≤ r) :
    (MassGap.CompositeLink.Φ0 (blFam hN c hc0 hc m s)).PhysRange r :=
  Filter.Eventually.of_forall fun k => by
    show dySpacing N k * ((mgRange m (mgLevels N m s k) : ℕ) : ℝ) ≤ r
    exact (spacing_mul_mgRange_le (by omega) hs0 k).trans hr

/-- **At a step with `0 ≤ s < 2 m a_k` the member is the identity** (no level).
DERIVED: `0` no level; `1` the least `N` of the spacing; `2` the least rank and the stride ratio;
`12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blFam_V_of_lt {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) {s : ℝ} {k : ℕ} (hs0 : 0 ≤ s)
    (hs : s < 2 * (m * dySpacing N k)) : (blFam hN c hc0 hc m s).V k = id := by
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hx : s / ((m : ℝ) * dySpacing N k) < 2 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · exact (div_lt_iff₀ (mul_pos (by exact_mod_cast hm) ha)).2 (by linarith)
  have hfl : ⌊s / ((m : ℝ) * dySpacing N k)⌋₊ < 2 :=
    (Nat.floor_lt (div_nonneg hs0 (mul_nonneg (Nat.cast_nonneg m) ha.le))).2 (by exact_mod_cast hx)
  have hJ : mgLevels N m s k = 0 := Nat.log_eq_zero_iff.2 (Or.inl hfl)
  show blMap hN hc0 hc m (mgLevels N m s k) = id
  rw [hJ]
  rfl

/-! ## 4. The step on diagonal `U(1)` configurations -/

section Abelian

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- **The diagonal `(a, ā, r, …, r)`** in rank `n + 2`. DERIVED: `2` the least rank. -/
def dv (a r : ℂ) : Fin (n + 2) → ℂ := Fin.cons a (Fin.cons ((starRingEnd ℂ) a) (fun _ => r))

/-- `D(z) = diag(z, z̄, 1, …, 1) ∈ SU(n + 2)` for `z` on the unit circle.
DERIVED: `1` the remaining entries and the determinant. -/
theorem dg_mem (z : Circle) : diagonal (dv (n := n) (z : ℂ) 1) ∈ specialUnitaryGroup (Fin (n + 2)) ℂ := by
  have hz : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  have hz' : (z : ℂ) * (starRingEnd ℂ) z = 1 := by rw [mul_comm, hz]
  refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [dv, hz, hz']
  · rw [det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [dv, hz']

/-- **The diagonal embedding `U(1) → SU(n + 2)`**, `z ↦ diag(z, z̄, 1, …, 1)`.
DERIVED: `1` the unit. -/
def dgHom : Circle →* SU (n + 2) where
  toFun z := ⟨diagonal (dv (z : ℂ) 1), dg_mem z⟩
  map_one' := by
    apply Subtype.ext
    show diagonal (dv (n := n) ((1 : Circle) : ℂ) 1) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [dv]
  map_mul' z w := by
    apply Subtype.ext
    show diagonal (dv (n := n) ((z * w : Circle) : ℂ) 1) = diagonal (dv (z : ℂ) 1) * diagonal (dv (w : ℂ) 1)
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [dv, map_mul]

/-- DERIVED: `1` the remaining entries. -/
theorem dgHom_coe (z : Circle) :
    ((dgHom (n := n) z : SU (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) = diagonal (dv (z : ℂ) 1) :=
  rfl

/-- **The first entry of `D(z)` is `z`.** DERIVED: `0` the first index. -/
theorem dg_entry (z : Circle) :
    ((dgHom (n := n) z : SU (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) 0 0 = z := by
  rw [dgHom_coe, diagonal_apply_eq]
  simp [dv]

/-- **The phase of a non-zero number**, `w/|w|` (`coe_nz`), as a point of the circle.
DERIVED: no numeral. -/
def nz (w : ℂ) : Circle := Circle.exp (Complex.arg w)

/-- DERIVED: `0` the excluded value. -/
theorem coe_nz {w : ℂ} (hw : w ≠ 0) : (nz w : ℂ) = w / (‖w‖ : ℂ) := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  rw [nz, Circle.coe_exp, eq_div_iff hn]
  calc Complex.exp ((Complex.arg w : ℂ) * Complex.I) * (‖w‖ : ℂ)
      = (‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I) := mul_comm _ _
    _ = w := Complex.norm_mul_exp_arg_mul_I w

/-- **The projection of `diag(w, w̄, r, …, r)`** (`w ≠ 0`, `r > 0`) is `diag(w/|w|, w̄/|w|, 1, …, 1)`: that
diagonal is unitary with `Vᴴ X = diag(|w|, |w|, r, …, r) ≥ 0`, so it is the polar part, and the determinant
`|w|² rⁿ` is positive, so the phase is `1`.
DERIVED: `0` the excluded value and the sign; `1` the remaining entries; `2` the squared modulus. -/
theorem projMat_dv {w : ℂ} (hw : w ≠ 0) {r : ℝ} (hr : 0 < r) :
    projMat (diagonal (dv (n := n) w (r : ℂ))) = diagonal (dv (w / (‖w‖ : ℂ)) 1) := by
  have hnr : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hnr.ne'
  have hcw : (starRingEnd ℂ) w * w = (‖w‖ : ℂ) * ‖w‖ := by rw [Complex.conj_mul', sq]
  have hwc : w * (starRingEnd ℂ) w = (‖w‖ : ℂ) * ‖w‖ := by rw [Complex.mul_conj', sq]
  have huu : (starRingEnd ℂ) (w / (‖w‖ : ℂ)) * (w / (‖w‖ : ℂ)) = 1 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, hcw, div_self (mul_ne_zero hn hn)]
  have huu' : (w / (‖w‖ : ℂ)) * (starRingEnd ℂ) (w / (‖w‖ : ℂ)) = 1 := by rw [mul_comm, huu]
  have he0 : (starRingEnd ℂ) (w / (‖w‖ : ℂ)) * w = (‖w‖ : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, hcw, mul_div_assoc, div_self hn, mul_one]
  have he1 : (w / (‖w‖ : ℂ)) * (starRingEnd ℂ) w = (‖w‖ : ℂ) := by
    rw [div_mul_eq_mul_div, hwc, mul_div_assoc, div_self hn, mul_one]
  have hdet : (diagonal (dv (n := n) w (r : ℂ))).det = ((‖w‖ ^ 2 * r ^ n : ℝ) : ℂ) := by
    rw [det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [dv, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← mul_assoc, hwc]
    push_cast
    ring
  have hpos : (0 : ℝ) < ‖w‖ ^ 2 * r ^ n := mul_pos (pow_pos hnr 2) (pow_pos hr n)
  have hX0 : (diagonal (dv (n := n) w (r : ℂ))).det ≠ 0 := by
    rw [hdet]; exact_mod_cast hpos.ne'
  have hU : diagonal (dv (n := n) (w / (‖w‖ : ℂ)) 1) ∈ unitaryGroup (Fin (n + 2)) ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [dv, Fin.cons_zero, Pi.star_apply, Complex.star_def]; exact huu
    · simp only [dv, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
      exact huu'
    · simp [dv]
  have hP : ((diagonal (dv (n := n) (w / (‖w‖ : ℂ)) 1))ᴴ * diagonal (dv w (r : ℂ))).PosSemidef := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    refine PosSemidef.diagonal (Pi.le_def.mpr (fun i => ?_))
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [dv, Fin.cons_zero, Pi.star_apply, Complex.star_def, Pi.zero_apply]
      rw [he0]; exact Complex.zero_le_real.mpr (norm_nonneg w)
    · simp only [dv, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, Complex.star_def, Complex.conj_conj,
        Pi.zero_apply]
      rw [he1]; exact Complex.zero_le_real.mpr (norm_nonneg w)
    · simp only [dv, Fin.cons_succ, Pi.star_apply, Complex.star_def, Pi.zero_apply, map_one, one_mul]
      exact Complex.zero_le_real.mpr hr.le
  have hpolar : diagonal (dv (n := n) (w / (‖w‖ : ℂ)) 1) = polar (diagonal (dv w (r : ℂ))) :=
    polar_unique hX0 hU hP
  have harg : Complex.arg (diagonal (dv (n := n) w (r : ℂ))).det = 0 := by
    rw [hdet]; exact Complex.arg_ofReal_of_nonneg hpos.le
  rw [projMat, phase, harg, ← hpolar]
  simp

variable {ι : Type} [Fintype ι]

/-- **The averaged block matrix of diagonal inputs** is `diag(w, w̄, r, …, r)` with
`w = z + e Σ vᵢ` and `r = 1 + e #ι`. DERIVED: `1` the remaining entries. -/
theorem blockMatI_dg (e : ℝ) (z : Circle) (v : ι → Circle) :
    blockMatI e (dgHom (n := n) z) (fun q => dgHom (v q))
      = diagonal (dv ((z : ℂ) + (e : ℂ) * ∑ q, (v q : ℂ)) ((1 + e * Fintype.card ι : ℝ) : ℂ)) := by
  have hs : ∑ q, diagonal (dv (n := n) (v q : ℂ) 1) = diagonal (∑ q, dv (v q : ℂ) 1) :=
    (map_sum (diagonalAddMonoidHom (Fin (n + 2)) ℂ) _ _).symm
  simp only [blockMatI, dgHom_coe]
  rw [hs, ← diagonal_smul, diagonal_add]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
    simp [dv, Finset.sum_apply, map_sum]

/-- **The averaged step on diagonal inputs is the `U(1)` average**: `D(z)` with staples `D(vᵢ)` goes to
`D((z + e Σ vᵢ)/|z + e Σ vᵢ|)`. DERIVED: `0` the excluded value; `1` the remaining entries. -/
theorem avgStepI_dg (hN : 2 ≤ n + 2) {e : ℝ} (he0 : 0 ≤ e)
    (he : 2 * ((Fintype.card ι : ℝ) * e) < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (z : Circle)
    (v : ι → Circle) :
    avgStepI hN e he0 he (dgHom z) (fun q => dgHom (v q))
      = dgHom (nz ((z : ℂ) + (e : ℂ) * ∑ q, (v q : ℂ))) := by
  have hr : (0 : ℝ) < 1 + e * Fintype.card ι := by
    have := mul_nonneg he0 (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)); linarith
  have key : ∀ (a b : ℂ), (diagonal (dv (n := n) a b)).det ∈ Complex.slitPlane → a ≠ 0 := by
    intro a b h ha
    subst ha
    apply Complex.slitPlane_ne_zero h
    rw [det_diagonal, Fin.prod_univ_succ]
    simp [dv]
  have hX := det_blockMatI_mem_slitPlane hN he0 he (dgHom (n := n) z) (fun q => dgHom (v q))
  rw [blockMatI_dg] at hX
  have hw := key _ _ hX
  apply Subtype.ext
  show projMat (blockMatI e (dgHom (n := n) z) (fun q => dgHom (v q)))
    = diagonal (dv ((nz ((z : ℂ) + (e : ℂ) * ∑ q, (v q : ℂ)) : Circle) : ℂ) 1)
  rw [blockMatI_dg, projMat_dv hw hr, coe_nz hw]

end Abelian

/-! ## 5. Circle configurations and the slice family -/

section Slice

variable {n : ℕ}

/-- **A circle configuration embedded diagonally.** DERIVED: no numeral. -/
def dgConf (Z : IConf Circle) : IConf (SU (n + 2)) := fun l => dgHom (Z l)

/-- **Transporters commute with a group homomorphism.** DERIVED: no numeral. -/
theorem ptr_map {G H : Type} [Group G] [Group H] (φ : G →* H) (U : IConf G) (ν : Fin 4) (t : ℕ)
    (x : ISite) : ptr (fun l => φ (U l)) ν t x = φ (ptr U ν t x) := by
  induction t generalizing x with
  | zero => rw [ptr_zero, ptr_zero, map_one]
  | succ t ih => rw [ptr_succ, ptr_succ, ih, map_mul]

/-- **Strided staples commute with a group homomorphism.** DERIVED: `0` names the upper side; `3` the
transverse directions in four dimensions. -/
theorem stapleD_map {G H : Type} [Group G] [Group H] (φ : G →* H) (U : IConf G) (t : ℕ) (μ : Fin 4)
    (x : ISite) (p : Fin 3 × Fin 2) : stapleD (fun l => φ (U l)) t μ x p = φ (stapleD U t μ x p) := by
  unfold stapleD
  split_ifs <;> simp only [ptr_map, map_mul, map_inv]

/-- **The `U(1)` block average**: every link replaced by the phase of itself plus `e` times the sum of its
block staples. DERIVED: no numeral. -/
def u1Step (e : ℝ) (d : ℕ) (Z : IConf Circle) : IConf Circle :=
  fun l => nz ((Z l : ℂ) + (e : ℂ) * ∑ q, ((blStaples Z d l q : Circle) : ℂ))

/-- **On diagonal configurations the block step is the `U(1)` block average.**
DERIVED: `2` the least rank; `12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blStep_dg (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (d : ℕ) (Z : IConf Circle) :
    blStep hN c hc0 hc d (dgConf Z) = dgConf (u1Step (c / d) d Z) := by
  funext l
  have hS : blStaples (dgConf (n := n) Z) d l = fun q => dgHom (blStaples Z d l q) :=
    funext fun q => stapleD_map dgHom Z _ _ _ _
  show avgStepI hN _ _ _ (dgHom (Z l)) (blStaples (dgConf Z) d l) = dgHom (u1Step (c / d) d Z l)
  rw [hS, avgStepI_dg]
  rfl

/-- **The slice configuration**: the direction-`1` link at `x` is `f(x₀)`, every other link is `1`.
DERIVED: `1` the slice direction and the unit; `0` the slice coordinate. -/
def zeta (f : ℤ → Circle) : IConf Circle := fun l => if l.1 = 1 then f (l.2 0) else 1

/-- DERIVED: `1` the slice direction; `0` the slice coordinate. -/
theorem ptr_zeta (f : ℤ → Circle) (ν : Fin 4) (t : ℕ) (y : ISite) :
    ptr (zeta f) ν t y = if ν = 1 then f (y 0) ^ t else 1 := by
  induction t generalizing y with
  | zero => rw [ptr_zero]; split_ifs <;> simp
  | succ t ih =>
    rw [ptr_succ, ih]
    by_cases h : ν = 1
    · subst h
      have hy : ishift 1 y 0 = y 0 := by simp [ishift_apply']
      simp only [zeta, if_true, hy]
      rw [pow_succ']
    · simp [zeta, h]

/-- A transporter of a slice configuration does not see a shift along its own direction.
DERIVED: `1` the slice direction; `0` the slice coordinate. -/
theorem ptr_zeta_sh (f : ℤ → Circle) (ν : Fin 4) (t : ℕ) (k : ℤ) (y : ISite) :
    ptr (zeta f) ν t (sh ν k y) = ptr (zeta f) ν t y := by
  rw [ptr_zeta, ptr_zeta]
  split_ifs with h
  · subst h; simp [sh_apply]
  · rfl

/-- **The staples of a direction-`1` link of a slice configuration are values of `f`.**
DERIVED: `1` the slice direction; `0` the slice coordinate and the upper side; `3` the transverse
directions in four dimensions. -/
theorem stapleD_zeta_one (f : ℤ → Circle) (t : ℕ) (x : ISite) (p : Fin 3 × Fin 2) :
    stapleD (zeta f) t 1 x p
      = f ((sh (other 1 p.1) (if p.2 = 0 then (t : ℤ) else -(t : ℤ)) x) 0) := by
  have hν : other 1 p.1 ≠ 1 := Fin.succAbove_ne 1 p.1
  unfold stapleD
  split_ifs with h <;> simp [ptr_zeta, hν, zeta]

/-- **The two sides of a staple of any other link of a slice configuration are inverse.**
DERIVED: `1` the slice direction; `0`, `1` the sides; `3` the transverse directions in four
dimensions. -/
theorem stapleD_zeta_inv {μ : Fin 4} (hμ : μ ≠ 1) (f : ℤ → Circle) (t : ℕ) (x : ISite) (j : Fin 3) :
    stapleD (zeta f) t μ x (j, 1) = (stapleD (zeta f) t μ x (j, 0))⁻¹ := by
  have hz : ∀ z, zeta f (μ, z) = 1 := fun z => by simp [zeta, hμ]
  have e1 := ptr_zeta_sh f (other μ j) t (-(t : ℤ)) x
  have e2 : ptr (zeta f) (other μ j) t (ishift μ (sh (other μ j) (-(t : ℤ)) x))
      = ptr (zeta f) (other μ j) t (ishift μ x) := by
    rw [ishift_sh]; exact ptr_zeta_sh f _ t _ _
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [stapleD, h10, if_true, if_false]
  rw [e1, e2, hz, hz, mul_one, mul_one, mul_inv_rev, inv_inv, mul_comm]

/-- **The block-staple sum of a non-slice link of a slice configuration is real**: the side swap pairs
each staple with its inverse, the complex conjugate.
DERIVED: `0`, `1` the sides; `6 = 3 · 2`. -/
theorem sum_zeta_im {μ : Fin 4} (hμ : μ ≠ 1) (f : ℤ → Circle) (d : ℕ) (x : ISite) :
    (∑ q : Fin 6 × Fin d, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)).im = 0 := by
  let e6 : Equiv.Perm (Fin 6) :=
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.swap (0 : Fin 2) 1))).trans
      finProdFinEquiv
  let σ : Equiv.Perm (Fin 6 × Fin d) := Equiv.prodCongr e6 (Equiv.refl (Fin d))
  have hsw : ∀ (t : ℕ) (j : Fin 3) (s : Fin 2),
      ((stapleD (zeta f) t μ x (j, Equiv.swap (0 : Fin 2) 1 s) : Circle) : ℂ)
        = (starRingEnd ℂ) ((stapleD (zeta f) t μ x (j, s) : Circle) : ℂ) := by
    intro t j s
    obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
    · rw [Equiv.swap_apply_left, stapleD_zeta_inv hμ, Circle.coe_inv_eq_conj]
    · rw [Equiv.swap_apply_right, stapleD_zeta_inv hμ f t x j, Circle.coe_inv_eq_conj,
        Complex.conj_conj]
  have hσ : ∀ q, ((blStaples (zeta f) d (μ, x) (σ q) : Circle) : ℂ)
      = (starRingEnd ℂ) ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ) := by
    intro q
    have hq : (finProdFinEquiv.symm (e6 q.1) : Fin 3 × Fin 2)
        = ((finProdFinEquiv.symm q.1 : Fin 3 × Fin 2).1,
          Equiv.swap (0 : Fin 2) 1 (finProdFinEquiv.symm q.1 : Fin 3 × Fin 2).2) := by
      refine Prod.ext ?_ ?_ <;> simp [e6]
    show ((stapleD (zeta f) ((q.2 : ℕ) + 1) μ x (finProdFinEquiv.symm (e6 q.1)) : Circle) : ℂ) = _
    rw [hq]
    exact hsw _ _ _
  have hS : (starRingEnd ℂ) (∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ))
      = ∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ) := by
    rw [map_sum]
    calc ∑ q, (starRingEnd ℂ) ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)
        = ∑ q, ((blStaples (zeta f) d (μ, x) (σ q) : Circle) : ℂ) :=
          Finset.sum_congr rfl (fun q _ => (hσ q).symm)
      _ = ∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ) :=
          Equiv.sum_comp σ (fun q => ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ))
  exact Complex.conj_eq_iff_im.mp hS

/-- **The offset of a block staple of a direction-`1` link along the slice coordinate**: `±t` for the
direction-`0` staples, `0` for the others. DERIVED: `0` the slice coordinate and the upper side; `1` the
slice direction and the least offset; `6 = 3 · 2` the staple directions and sides. -/
def off (d : ℕ) (q : Fin 6 × Fin d) : ℤ :=
  (sh (other 1 (finProdFinEquiv.symm q.1 : Fin 3 × Fin 2).1)
    (if (finProdFinEquiv.symm q.1 : Fin 3 × Fin 2).2 = 0 then (((q.2 : ℕ) + 1 : ℕ) : ℤ)
      else -((((q.2 : ℕ) + 1 : ℕ)) : ℤ))
    0) 0

/-- DERIVED: `0` the slice coordinate. -/
theorem sh_coord0 (ν : Fin 4) (k : ℤ) (x : ISite) : (sh ν k x) 0 = x 0 + (sh ν k 0) 0 := by
  simp only [sh_apply]
  split_ifs <;> simp

/-- **The one-dimensional block average** on the slice values.
DERIVED: no numeral. -/
def Fz (e : ℝ) (d : ℕ) (f : ℤ → Circle) (y : ℤ) : Circle :=
  nz ((f y : ℂ) + (e : ℂ) * ∑ q : Fin 6 × Fin d, (f (y + off d q) : ℂ))

/-- **The `U(1)` block average keeps slice configurations**: direction-`1` links follow `Fz`, every
other link stays `1` (`e · 6d < 1`).
DERIVED: `1` the slice direction and the unit; `0` the slice coordinate; `6 = 3 · 2` the staple
directions and sides. -/
theorem u1Step_zeta {e : ℝ} (he0 : 0 ≤ e) {d : ℕ} (he : (Fintype.card (Fin 6 × Fin d) : ℝ) * e < 1)
    (f : ℤ → Circle) : u1Step e d (zeta f) = zeta (Fz e d f) := by
  funext l
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = 1
  · subst hμ
    have h1 : zeta (Fz e d f) (1, x) = Fz e d f (x 0) := by simp [zeta]
    have h2 : zeta f (1, x) = f (x 0) := by simp [zeta]
    have hsum : ∑ q, ((blStaples (zeta f) d (1, x) q : Circle) : ℂ) = ∑ q : Fin 6 × Fin d, (f (x 0 + off d q) : ℂ) := by
      refine Finset.sum_congr rfl (fun q _ => ?_)
      show ((stapleD (zeta f) ((q.2 : ℕ) + 1) 1 x (finProdFinEquiv.symm q.1) : Circle) : ℂ) = _
      rw [stapleD_zeta_one]
      exact congrArg (fun y => ((f y : Circle) : ℂ)) (sh_coord0 _ _ x)
    show nz ((zeta f (1, x) : ℂ) + (e : ℂ) * ∑ q, ((blStaples (zeta f) d (1, x) q : Circle) : ℂ)) = _
    rw [h1, h2, hsum]
    rfl
  · have h1 : zeta (Fz e d f) (μ, x) = 1 := by simp [zeta, hμ]
    have h2 : zeta f (μ, x) = 1 := by simp [zeta, hμ]
    show nz ((zeta f (μ, x) : ℂ) + (e : ℂ) * ∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)) = _
    rw [h1, h2, Circle.coe_one]
    have hSim := sum_zeta_im hμ f d x
    have hle : ∀ q, -1 ≤ ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ).re := fun q => by
      have h := Complex.abs_re_le_norm ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)
      rw [Circle.norm_coe] at h
      linarith [neg_abs_le (((blStaples (zeta f) d (μ, x) q : Circle) : ℂ).re)]
    have hSre : -(Fintype.card (Fin 6 × Fin d) : ℝ)
        ≤ (∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)).re := by
      rw [Complex.re_sum]
      calc -(Fintype.card (Fin 6 × Fin d) : ℝ) = ∑ _q : Fin 6 × Fin d, (-1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun q _ => hle q)
    have hre : 0 ≤ (1 + (e : ℂ) * ∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)).re := by
      rw [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul]
      nlinarith [mul_le_mul_of_nonneg_left hSre he0]
    have him : (1 + (e : ℂ) * ∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ)).im = 0 := by
      rw [Complex.add_im, Complex.one_im, Complex.im_ofReal_mul, hSim, mul_zero, add_zero]
    show Circle.exp (Complex.arg (1 + (e : ℂ) * ∑ q, ((blStaples (zeta f) d (μ, x) q : Circle) : ℂ))) = 1
    rw [Complex.arg_eq_zero_iff.mpr ⟨hre, him⟩, Circle.exp_zero]

/-- **The block step keeps slice configurations.** DERIVED: `2` the least rank; `1` the sine bound;
`12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blStep_zeta (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (d : ℕ) (f : ℤ → Circle) :
    blStep hN c hc0 hc d (dgConf (zeta f)) = dgConf (zeta (Fz (c / d) d f)) := by
  have hK := avg_coupling hN hc d
  have hK0 : 0 ≤ (Fintype.card (Fin 6 × Fin d) : ℝ) * (c / d) :=
    mul_nonneg (Nat.cast_nonneg _) (avg_weight_nonneg hc0 d)
  have h1 : (Fintype.card (Fin 6 × Fin d) : ℝ) * (c / d) < 1 := by
    linarith [Real.sin_le_one (Real.pi / ((n + 2 : ℕ) : ℝ))]
  rw [blStep_dg, u1Step_zeta (avg_weight_nonneg hc0 d) h1]

/-! ### The quadrant invariant -/

/-- **Every slice value in the closed first quadrant.** DERIVED: `0` the lower ends. -/
def Quad (f : ℤ → Circle) : Prop := ∀ y, 0 ≤ (f y : ℂ).re ∧ 0 ≤ (f y : ℂ).im

/-- DERIVED: `0` the lower end. -/
theorem nz_re_nonneg {w : ℂ} (h : 0 ≤ w.re) : 0 ≤ (nz w : ℂ).re := by
  rw [nz, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  by_cases hw : w = 0
  · simp [hw]
  · rw [Complex.cos_arg hw]; exact div_nonneg h (norm_nonneg _)

/-- DERIVED: `0` the lower end. -/
theorem nz_im_nonneg {w : ℂ} (h : 0 ≤ w.im) : 0 ≤ (nz w : ℂ).im := by
  rw [nz, Circle.coe_exp, Complex.exp_ofReal_mul_I_im, Complex.sin_arg]
  exact div_nonneg h (norm_nonneg _)

/-- DERIVED: `0` the lower end. -/
theorem nz_re_pos {w : ℂ} (h : 0 < w.re) : 0 < (nz w : ℂ).re := by
  have hw : w ≠ 0 := fun h0 => by simp [h0] at h
  rw [nz, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.cos_arg hw]
  exact div_pos h (norm_pos_iff.mpr hw)

/-- **The block average keeps the closed first quadrant.** DERIVED: `0` the lower ends. -/
theorem Fz_quad {e : ℝ} (he0 : 0 ≤ e) (d : ℕ) {f : ℤ → Circle} (hf : Quad f) : Quad (Fz e d f) := by
  intro y
  unfold Fz
  constructor
  · apply nz_re_nonneg
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
    exact add_nonneg (hf y).1 (mul_nonneg he0 (Finset.sum_nonneg fun q _ => (hf _).1))
  · apply nz_im_nonneg
    rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_sum]
    exact add_nonneg (hf y).2 (mul_nonneg he0 (Finset.sum_nonneg fun q _ => (hf _).2))

/-- **The block average keeps `Re f(0) > 0`** on the quadrant. DERIVED: `0` the slice site and the
lower ends. -/
theorem Fz_pos {e : ℝ} (he0 : 0 ≤ e) (d : ℕ) {f : ℤ → Circle} (hf : Quad f) (h0 : 0 < (f 0 : ℂ).re) :
    0 < (Fz e d f 0 : ℂ).re := by
  unfold Fz
  apply nz_re_pos
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
  exact add_pos_of_pos_of_nonneg h0 (mul_nonneg he0 (Finset.sum_nonneg fun q _ => (hf _).1))

/-- **At stride `1` the block average makes `Re f(0) > 0` from `f(1) = 1`**: the direction-`0` staple on
the upper side at offset `1` of the slice-`0` link reads `f(1)`.
DERIVED: `0` the slice site, the direction, the upper side and the lower ends; `1` the stride, the
offset and the unit. -/
theorem Fz_first {e : ℝ} (he : 0 < e) {f : ℤ → Circle} (hf : Quad f) (h1 : f 1 = 1) :
    0 < (Fz e 1 f 0 : ℂ).re := by
  unfold Fz
  apply nz_re_pos
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
  let q₀ : Fin 6 × Fin 1 := (finProdFinEquiv ((0 : Fin 3), (0 : Fin 2)), 0)
  have ho : other 1 (0 : Fin 3) = 0 := by decide
  have hq₀ : off 1 q₀ = 1 := by
    simp [off, q₀, ho, sh_apply]
  have hle : ((f (0 + off 1 q₀) : Circle) : ℂ).re
      ≤ ∑ q : Fin 6 × Fin 1, ((f (0 + off 1 q) : Circle) : ℂ).re :=
    Finset.single_le_sum (f := fun q : Fin 6 × Fin 1 => ((f (0 + off 1 q) : Circle) : ℂ).re)
      (fun q _ => (hf _).1) (Finset.mem_univ q₀)
  rw [hq₀, zero_add, h1, Circle.coe_one, Complex.one_re] at hle
  have := (hf 0).1
  nlinarith [mul_le_mul_of_nonneg_left hle he.le]

/-- **Iterates of the block step keep slice configurations with `Re f(0) > 0`.**
DERIVED: `0` the slice site and the lower ends; `2` the least rank; `12 = 2 · 6` the coupling bound
of `avg_coupling`. -/
theorem blStep_iter_zeta (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (d k : ℕ) (f : ℤ → Circle) (hf : Quad f)
    (h0 : 0 < (f 0 : ℂ).re) :
    ∃ g : ℤ → Circle, Quad g ∧ 0 < (g 0 : ℂ).re
      ∧ (blStep hN c hc0 hc d)^[k] (dgConf (zeta f)) = dgConf (zeta g) := by
  induction k generalizing f with
  | zero => exact ⟨f, hf, h0, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply, blStep_zeta]
    exact ih _ (Fz_quad (avg_weight_nonneg hc0 d) d hf) (Fz_pos (avg_weight_nonneg hc0 d) d hf h0)

/-- **The witness slice**: `f₀(1) = 1`, `f₀(y) = i` otherwise. DERIVED: `1` the marked slice and the
unit; `π/2` the angle of `i`. -/
def f₀ : ℤ → Circle := fun y => if y = 1 then 1 else Circle.exp (Real.pi / 2)

/-- DERIVED: `0`, `1` the values' coordinates; `π/2` the angle of `i`. -/
theorem f₀_quad : Quad f₀ := by
  intro y
  by_cases h : y = 1
  · simp [f₀, h]
  · simp only [f₀, h, if_false]
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    exact ⟨le_refl 0, zero_le_one⟩

/-- `Re f₀(0) = 0`. DERIVED: `0` the slice site; `π/2` the angle of `i`. -/
theorem f₀_re_zero : (f₀ 0 : ℂ).re = 0 := by
  simp only [f₀, show (0 : ℤ) ≠ 1 by decide, if_false]
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two]

/-- **Every ray-averaged multigrid map with at least one level and step moves the witness slice
configuration to a slice configuration with `Re f(0) > 0`.**
DERIVED: `1` the least level and step count, the first stride; `0` the slice site; `2` the least
rank; `12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blMap_moves (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) {m : ℕ} (hm : 1 ≤ m) (J : ℕ) :
    ∃ g : ℤ → Circle, Quad g ∧ 0 < (g 0 : ℂ).re
      ∧ blMap hN hc0 hc m (J + 1) (dgConf (zeta f₀)) = dgConf (zeta g) := by
  induction J with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e1 : blMap hN hc0 hc (k + 1) (0 + 1) (dgConf (zeta f₀))
        = (blStep hN c hc0 hc (2 ^ 0))^[k] (dgConf (zeta (Fz (c / ((2 ^ 0 : ℕ) : ℝ)) (2 ^ 0) f₀))) := by
      show (blStep hN c hc0 hc (2 ^ 0))^[k + 1] (dgConf (zeta f₀)) = _
      rw [Function.iterate_succ_apply, blStep_zeta]
    have hpos : 0 < c / ((2 ^ 0 : ℕ) : ℝ) := by simpa using hcpos
    have hF : 0 < (Fz (c / ((2 ^ 0 : ℕ) : ℝ)) (2 ^ 0) f₀ 0 : ℂ).re :=
      Fz_first hpos f₀_quad (by simp [f₀])
    obtain ⟨g, hg, hg0, hk⟩ := blStep_iter_zeta hN hc0 hc (2 ^ 0) k _
      (Fz_quad hpos.le _ f₀_quad) hF
    exact ⟨g, hg, hg0, e1.trans hk⟩
  | succ J ih =>
    obtain ⟨g, hg, hg0, hJ⟩ := ih
    obtain ⟨g', hg', hg0', hk⟩ := blStep_iter_zeta hN hc0 hc (2 ^ (J + 1)) m g hg hg0
    refine ⟨g', hg', hg0', ?_⟩
    show (blStep hN c hc0 hc (2 ^ (J + 1)))^[m] (blMap hN hc0 hc m (J + 1) (dgConf (zeta f₀))) = _
    rw [hJ, hk]

end Slice

/-! ## 6. Non-identity of the family -/

open MassGap.ContinuumFlow MassGap.ContinuumSchwinger Filter

/-- **At `c > 0`, `m ≥ 1` and a step with at least one level the member moves a configuration.**
DERIVED: `1` the least level and step count; `2` the least rank; `0` the lower end of `c`;
`12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blFam_moves {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {m : ℕ} (hm : 1 ≤ m) {s : ℝ} {k : ℕ}
    (hJ : 1 ≤ mgLevels N m s k) : ∃ U : Cfg N, (blFam hN c hc0 hc m s).V k U ≠ U := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  obtain ⟨J, hJ'⟩ : ∃ J, mgLevels (n + 2) m s k = J + 1 := ⟨mgLevels (n + 2) m s k - 1, by omega⟩
  obtain ⟨g, _, hg0, hmap⟩ := blMap_moves hN hc0 hcpos hc hm J
  refine ⟨dgConf (zeta f₀), fun h => ?_⟩
  have h2 : blMap hN hc0 hc m (J + 1) (dgConf (zeta f₀)) = dgConf (zeta f₀) := by
    rw [← hJ']; exact h
  have h3 : dgConf (n := n) (zeta g) = dgConf (zeta f₀) := hmap.symm.trans h2
  have h4 := congrArg (fun A : SU (n + 2) => (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) 0 0)
    (congrFun h3 ((1 : Fin 4), (0 : ISite)))
  simp only [dgConf, dg_entry, zeta, if_true, Pi.zero_apply] at h4
  rw [h4, f₀_re_zero] at hg0
  exact lt_irrefl _ hg0

/-- **The ray-averaged family is not eventually the identity** (`c > 0`, `m ≥ 1`, `s > 0`): eventually
`a_k < s/(2m)`, so `J_k ≥ 1`, and `blFam_moves` applies.
DERIVED: `0` the limit and the lower ends; `1` the least level and step count; `2` the stride ratio and
the least rank; `12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blFam_not_eventually_id {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hcpos : 0 < c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 0 < s) :
    ¬ ∀ᶠ k in atTop, (blFam hN c hc0 hc m s).V k = id := by
  intro hev
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h2m : (0 : ℝ) < 2 * m := mul_pos two_pos hm'
  have hpos : 0 < s / (2 * m) := div_pos hs h2m
  have hlev : ∀ᶠ k in atTop, 1 ≤ mgLevels N m s k := by
    filter_upwards [(tendsto_dySpacing N).eventually (gt_mem_nhds hpos)] with k hk
    have ha := dySpacing_pos (by omega : 1 ≤ N) k
    rw [lt_div_iff₀ h2m] at hk
    have h2 : (2 : ℝ) ≤ s / (m * dySpacing N k) := by
      rw [le_div_iff₀ (mul_pos hm' ha)]
      nlinarith
    have h3 : 2 ≤ ⌊s / ((m : ℝ) * dySpacing N k)⌋₊ := Nat.le_floor (by exact_mod_cast h2)
    exact Nat.le_log_of_pow_le one_lt_two (by simpa using h3)
  obtain ⟨k, hk1, hk2⟩ := (hev.and hlev).exists
  obtain ⟨U, hU⟩ := blFam_moves hN hc0 hcpos hc hm hk2
  exact hU (congrFun hk1 U)

/-! ## 7. The scale input at this observer (stated, open) -/

section Scale

open MassGap.ClayStatement MassGap.ClayData MassGap.ReflAvg MassGap.MultiScaleAll MassGap.SU2Best

/-- **`(M_W)` at the ray-averaged family is the scale and top fields at `b = 1`**
(`ObserverMultigrid.mw_iff`). `MW (blFam …)` is false (`BulkBound.not_MW_blFam`).
DERIVED: `1` the scale; `2` the least rank; `12 = 2 · 6` the coupling bound of `avg_coupling`. -/
theorem blFam_mw_iff {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s : ℝ) :
    (∃ Wf : ℝ → ConfFlow N, Wf 1 = blFam hN c hc0 hc m s ∧ ScaleControlAll 1 Wf)
      ↔ MW (blFam hN c hc0 hc m s) :=
  mw_iff _

end Scale

end MassGap.ObserverBlock

end

#print axioms MassGap.ObserverBlock.det_blockMatI_mem_slitPlane
#print axioms MassGap.ObserverBlock.continuous_avgStepI
#print axioms MassGap.ObserverBlock.avgStepI_gauge
#print axioms MassGap.ObserverBlock.avgStepI_inv
#print axioms MassGap.ObserverBlock.avgStepI_perm
#print axioms MassGap.ObserverBlock.blStaples_refl_ne
#print axioms MassGap.ObserverBlock.blStaples_local
#print axioms MassGap.ObserverBlock.avg_coupling
#print axioms MassGap.ObserverBlock.blStep_gauge
#print axioms MassGap.ObserverBlock.continuous_blStep
#print axioms MassGap.ObserverBlock.blStep_refl
#print axioms MassGap.ObserverBlock.blStep_reads
#print axioms MassGap.ObserverBlock.blMap_reads
#print axioms MassGap.ObserverBlock.blConfFlow
#print axioms MassGap.ObserverBlock.blFam_physRange
#print axioms MassGap.ObserverBlock.blFam_V_of_lt
#print axioms MassGap.ObserverBlock.projMat_dv
#print axioms MassGap.ObserverBlock.avgStepI_dg
#print axioms MassGap.ObserverBlock.blStep_dg
#print axioms MassGap.ObserverBlock.stapleD_zeta_inv
#print axioms MassGap.ObserverBlock.sum_zeta_im
#print axioms MassGap.ObserverBlock.u1Step_zeta
#print axioms MassGap.ObserverBlock.Fz_first
#print axioms MassGap.ObserverBlock.blMap_moves
#print axioms MassGap.ObserverBlock.blFam_moves
#print axioms MassGap.ObserverBlock.blFam_not_eventually_id
#print axioms MassGap.ObserverBlock.blFam_mw_iff
