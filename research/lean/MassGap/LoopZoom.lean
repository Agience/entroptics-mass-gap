import Mathlib
import MassGap.ElectricLoops
import MassGap.Chessboard
import MassGap.SlabTransferAdjoint
import MassGap.FiniteReadingFlux

/-!
# MassGap.LoopZoom — the zoom from a contractible loop of size `R` to the torus, and what it reaches of (E2')

`ElectricLoops.zeroFluxGap_of_electricCost` reduces the gap at `SU(2)` to (E1) and (E2'): on the loop
shells of radii `R_k`, a diagonal block cost `b_kk ≤ μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}` and off-diagonal
row sums `≤ μ_{g₀}² η`. Winding loops are priced by (V); contractible loops are not. The idea tested here
(the author's aperture picture: the observer at scale `R` sees a box of size `R`) is that a contractible loop
of size `R` in the box of size `L` behaves like a winding loop on a torus of size about `R`.

## Evaluation

1. **Is there a lattice comparison?** One, and it runs the other way. `Chessboard.chain_full` is the
   reflection-doubling chain on the rectangular `SU(2)` torus: with the flux operator of a sheet inserted,
   `|⟨F W(m × n)⟩|^{2^{p+q}} ≤ ⟨F W_full⟩` for `L_a = 2^p m`, `L_b = 2^q n`, where `W_full` is the loop
   once around the whole `(b, a)` torus, holonomy `P_b P_a P_b⁻¹ P_a⁻¹` (the commutator of two Polyakov
   lines). **`zoom_root`** states it as the root: the loop of size `m × n` is bounded by the
   `mn/(L_a L_b)`-th power of the full-torus object, i.e. by its share per tile. This is the
   contractible-to-torus comparison of the chessboard estimate; the tiles of size `R` are glued into the
   torus of size `L`, so it compares scale `R` with scale `L`, not with a torus of size `R`. No module in
   the tree compares a box of side `L` with a torus of side `R` (`GapSideFluxChessboard` doubles an electric-flux ratio in time, `elecRatio_conv_le`; its own reading
   is that the doubling transports a small ratio and does not create one).
   The endpoint of the chain is not the winding state (V) prices. It is `Chessboard.FullLoopFlux`,
   equivalently the sign condition `0 ≤ ⟨F · wd(P_b P_a P_b⁻¹ P_a⁻¹)⟩` (`Chessboard.fullLoopFlux_iff`),
   which is not proved and fails in some geometries (`Chessboard`); through `TomboulisYaffe` the bound it
   would give is the magnetic twist ratio `(1 − zR)/2` of the same torus, with the factor `2`.
2. **Circular or unconditional?** The chain is unconditional: reflection positivity and Cauchy–Schwarz,
   no decay. It bounds an expectation, at one time, of an uncentred observable. The (E2') diagonal is a
   transfer element of a centred state, and two facts proved here separate the two:
   * **`loopTransfer_centred`** (real objects): for `Ω = φ_{g₀}` and `T` the operator of `trivKN`,
     `‖T ψ_C‖² = ‖T (W_C Ω)‖² − μ_{g₀}² ⟨W_C⟩²` and `‖ψ_C‖² = ‖W_C Ω‖² − ⟨W_C⟩²`. The diagonal element
     is the raw element minus the disconnected part. A reflection estimate reaches the raw element
     (`centred_le_raw`: bounding it bounds the centred one), but **`vev_sq_le_of_raw`**: a raw bound
     `‖T (W_C Ω)‖² ≤ μ_{g₀}² B` forces `⟨W_C⟩² ≤ B`. So the raw route at the diagonal's rate
     `B = e^{−(c σ R + c'/R) t}` needs the loop expectation to be at least that small already. Argued, not
     a declaration: under an area law `⟨W_C⟩ ≈ e^{−σ_A R²}` this holds only for `R` of order `t` and above,
     and the chessboard chain itself gives the area law only through `FullLoopFlux`.
   * **`block_rayleigh`**: the diagonal clause is a bound on a whole shell, not on one loop. For any family
     `x_j` in a shell with block constant `d`, `Σ_{j,k} ⟪T x_j, T x_k⟫ ≤ d Σ_{j,k} ⟪x_j, x_k⟫`. Argued:
     the shell of radius `R` contains the states of every translate of a loop of size `R`; the cross terms
     are the connected loop–loop correlators at spatial separation `d` and time `t`; at fixed physical `R`
     uniformly in `β` the number of translates grows like `(L/a)³`. So the block constant asks summable
     spatial decay of a connected correlator beyond `R`: clustering, which is the content of the gap. That
     part of (E2') diagonal is circular. Reflection positivity does not give the decay of a connected
     correlator (`ChessboardRead.gapAt_iff_lag`: the single-lag bound is the gap restated;
     `lag_forces_null_of_T_eq_id`: positivity alone gives no rate below one).
3. **The off-diagonal coupling `η` is not a separate input** (proved). On mutually orthogonal shells,
   Cauchy–Schwarz gives `|⟪T x, T y⟫| ≤ ‖T x‖ ‖T y‖`, so the diagonal block bounds `s_k` alone give the
   Schur test with `b_kl = s_k s_l`, row sums `s_k Σ_l s_l ≤ D²`. **`zeroFluxGap_of_shellDiag`**: diagonal
   shell bounds `‖T x‖ ≤ s_k ‖x‖` with every partial sum `Σ s_l ≤ |μ_{g₀}| e^{−m t/2}` give
   `ZeroFluxGap g₀ E m`. **`zeroFluxGap_of_electricDiag`**: the diagonal clause of
   `zeroFluxGap_of_electricCost`, with radii `R_k ≥ (k + 1) δ`, `c σ δ > 0`, and nothing else, gives the
   gap at `diagRate c c' σ δ t`, where `e^{−m t/2} = e^{−√(c c' σ) t/2} · q/(1 − q)`,
   `q = e^{−c σ δ t/4}` (`diagRate_pos`: positive when that product is below one). The η clause and the
   chessboard route are therefore not needed for the off-diagonal; what remains of (E2') is the diagonal
   shell block alone.

## What remains of (E2')

The diagonal shell bound `‖T x‖² ≤ μ_{g₀}² e^{−(c σ R_k + c'/R_k) t} ‖x‖²` on every shell, with
radii `R_k ≥ (k+1) δ`, and `c, c', σ, δ` fixed uniformly in `β` at fixed physical lengths. Its single-loop part is reached by a raw
reflection bound only together with a decay of `⟨W_C⟩` at the same rate (`vev_sq_le_of_raw`); its
within-shell part is spatial clustering of connected loop correlators (argued above). Neither is proved.
(E1) is as in `ElectricLoops`.

## What is proved

* §1 (any real inner product space, `T` symmetric, `T Ω = μ Ω`, `‖Ω‖ = 1`): `inner_T_vac`,
  `norm_sq_centred`, `norm_sq_T_centred`, `centred_le_raw`, `vev_sq_le_of_raw`.
* §2 (real objects): `loopTransfer_centred` on the slice of step `i` at side `n`, `T = kernelCLM` of
  `trivKN 2 β n i` (self-adjoint by `SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm` and
  `FiniteReadingFlux.symm_trivKN`), `0 ≤ β`.
* §3: `block_rayleigh`; `bound_on_diagShells` (abstract); `zeroFluxGap_of_shellDiag`, `diagRate`,
  `diagRate_pos`, `zeroFluxGap_of_electricDiag` (real objects).
* §4: `zoom_root` on `RectWilson.RSite L`, from `Chessboard.chain_full`, with no further hypothesis.

DERIVED (module-wide): `2` is the `L²` exponent, the square of a norm, the doubling base `2^{p+q}` and the
half time `t/2`; `4` in `t/4` splits the half rate `a/2` into two quarters, one carrying
`AttractCost.two_sqrt_le_cost` and one the geometric decay in `k`; `k + 1` makes the first radius
`δ`; `1 − q` is the geometric sum.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.LoopZoom

open MeasureTheory Filter Finset
open MassGap.ElectricLoops

/-! ## 1. Centred and raw transfer elements -/

section Centred

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a symmetric `T` with `T Ω = μ Ω`: `⟪T u, Ω⟫ = μ ⟪Ω, u⟫`. -/
theorem inner_T_vac {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) {Ω : E} {μ : ℝ}
    (hΩ : T Ω = μ • Ω) (u : E) : inner ℝ (T u) Ω = μ * inner ℝ Ω u := by
  rw [hT, hΩ, inner_smul_right, real_inner_comm]

/-- The centred vector `u − ⟪Ω, u⟫ Ω` has `‖·‖² = ‖u‖² − ⟪Ω, u⟫²` (`‖Ω‖ = 1`). -/
theorem norm_sq_centred {Ω : E} (h1 : ‖Ω‖ = 1) (u : E) :
    ‖u - inner ℝ Ω u • Ω‖ ^ 2 = ‖u‖ ^ 2 - inner ℝ Ω u ^ 2 := by
  rw [@norm_sub_sq_real, norm_smul, h1, inner_smul_right, real_inner_comm u Ω, Real.norm_eq_abs,
    mul_one, sq_abs]
  ring

/-- **The centred transfer element is the raw one minus the disconnected part**:
`‖T (u − ⟪Ω, u⟫ Ω)‖² = ‖T u‖² − μ² ⟪Ω, u⟫²`. -/
theorem norm_sq_T_centred {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) {Ω : E}
    {μ : ℝ} (hΩ : T Ω = μ • Ω) (h1 : ‖Ω‖ = 1) (u : E) :
    ‖T (u - inner ℝ Ω u • Ω)‖ ^ 2 = ‖T u‖ ^ 2 - μ ^ 2 * inner ℝ Ω u ^ 2 := by
  rw [map_sub, map_smul, hΩ, smul_smul, @norm_sub_sq_real, norm_smul, h1, inner_smul_right,
    inner_T_vac hT hΩ, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- The centred transfer element is at most the raw one. -/
theorem centred_le_raw {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) {Ω : E}
    {μ : ℝ} (hΩ : T Ω = μ • Ω) (h1 : ‖Ω‖ = 1) (u : E) :
    ‖T (u - inner ℝ Ω u • Ω)‖ ^ 2 ≤ ‖T u‖ ^ 2 := by
  rw [norm_sq_T_centred hT hΩ h1]
  nlinarith [sq_nonneg μ, sq_nonneg (inner ℝ Ω u), mul_nonneg (sq_nonneg μ) (sq_nonneg (inner ℝ Ω u))]

/-- **A raw bound pays the expectation**: `‖T u‖² ≤ μ² B` with `μ ≠ 0` forces `⟪Ω, u⟫² ≤ B`. -/
theorem vev_sq_le_of_raw {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) {Ω : E}
    {μ : ℝ} (hΩ : T Ω = μ • Ω) (h1 : ‖Ω‖ = 1) (hμ : μ ≠ 0) {u : E} {B : ℝ}
    (hraw : ‖T u‖ ^ 2 ≤ μ ^ 2 * B) : inner ℝ Ω u ^ 2 ≤ B := by
  have h := norm_sq_T_centred hT hΩ h1 u
  have h0 : 0 ≤ ‖T (u - inner ℝ Ω u • Ω)‖ ^ 2 := sq_nonneg _
  have hμ2 : 0 < μ ^ 2 := by positivity
  have : μ ^ 2 * inner ℝ Ω u ^ 2 ≤ μ ^ 2 * B := by linarith
  exact le_of_mul_le_mul_left this hμ2

end Centred

/-! ## 2. The loop states on the slice -/

section Slice

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.CentreSectorSeed (Tr)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.SlabKernelOperator (kernelCLM)

/-- **The diagonal transfer element of a loop state, on the real slice.** With `Ω = φ_{g₀}` and `T` the
operator of `trivKN 2 β n i` (`0 ≤ β`): there are `L²` vectors `u = W_C Ω` and `ψ = ψ_C` (the loop state)
with `‖T ψ‖² = ‖T u‖² − μ_{g₀}² ⟨W_C⟩²` and `‖ψ‖² = ‖u‖² − ⟨W_C⟩²`. -/
theorem loopTransfer_centred {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C) (Cl : Loop i (Tr n i)) :
    ∃ u ψ : Lp ℝ 2 (hSN 2 n i),
      (u : Slice n i → ℝ) =ᵐ[hSN 2 n i] (fun V => Cl.wl V * φ g₀ V) ∧
      (ψ : Slice n i → ℝ) =ᵐ[hSN 2 n i] loopState (hSN 2 n i) (φ g₀) Cl ∧
      ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) ψ‖ ^ 2
        = ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) u‖ ^ 2
          - μv g₀ ^ 2 * vev (hSN 2 n i) (φ g₀) Cl ^ 2 ∧
      ‖ψ‖ ^ 2 = ‖u‖ ^ 2 - vev (hSN 2 n i) (φ g₀) Cl ^ 2 := by
  have hφ := memLp_of_norm (hm g₀) (hL.norm g₀)
  have hu : MemLp (fun V => Cl.wl V * φ g₀ V) 2 (hSN 2 n i) :=
    hφ.of_le_mul (c := 2) ((continuous_wl Cl).measurable.mul (hm g₀)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun V => by
        rw [norm_mul, Real.norm_eq_abs (Cl.wl V)]
        exact mul_le_mul_of_nonneg_right (abs_wl_le Cl V) (norm_nonneg _))
  set Ω : Lp ℝ 2 (hSN 2 n i) := vecOf (hm g₀) (hL.norm g₀) with hΩdef
  set u : Lp ℝ 2 (hSN 2 n i) := hu.toLp _ with hudef
  set T := kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) with hTdef
  have hv : inner ℝ Ω u = vev (hSN 2 n i) (φ g₀) Cl := by
    rw [L2.inner_def]
    unfold vev
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp, hu.coeFn_toLp] with x hx hx'
    rw [hΩdef, vecOf, hx, hudef, hx']
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hsa : IsSelfAdjoint T :=
    SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i)
      (FiniteReadingFlux.symm_trivKN hβ n i)
  have hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y) := fun x y =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa x y
  have hΩ : T Ω = μv g₀ • Ω := trivKN_vecOf hL hm hkm hC0 hkb g₀
  have h1 : ‖Ω‖ = 1 := norm_vecOf (hm g₀) (hL.norm g₀)
  refine ⟨u, u - inner ℝ Ω u • Ω, hu.coeFn_toLp, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub u (inner ℝ Ω u • Ω), Lp.coeFn_smul (inner ℝ Ω u) Ω,
      hu.coeFn_toLp, hφ.coeFn_toLp] with x h1x h2x h3x h4x
    rw [h1x, Pi.sub_apply, h2x, Pi.smul_apply, smul_eq_mul, hv, hudef, h3x, hΩdef, vecOf, h4x]
    unfold loopState
    ring
  · rw [norm_sq_T_centred hT hΩ h1, hv]
  · rw [norm_sq_centred h1, hv]

end Slice

/-! ## 3. Shell blocks: the Rayleigh form, and the diagonal carries the off-diagonal -/

section Blocks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The block constant of a shell bounds the summed cross terms of any family in it.** -/
theorem block_rayleigh {T : E →L[ℝ] E} {S : Submodule ℝ E} {d : ℝ}
    (hdiag : ∀ x ∈ S, ‖T x‖ ^ 2 ≤ d * ‖x‖ ^ 2) {κ : Type*} (F : Finset κ) (x : κ → E)
    (hx : ∀ j ∈ F, x j ∈ S) :
    ∑ j ∈ F, ∑ k ∈ F, inner ℝ (T (x j)) (T (x k)) ≤ d * ∑ j ∈ F, ∑ k ∈ F, inner ℝ (x j) (x k) := by
  have hf : ∑ j ∈ F, x j ∈ S := Submodule.sum_mem S hx
  have h := hdiag _ hf
  have e1 : ‖T (∑ j ∈ F, x j)‖ ^ 2 = ∑ j ∈ F, ∑ k ∈ F, inner ℝ (T (x j)) (T (x k)) := by
    rw [← real_inner_self_eq_norm_sq, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
  have e2 : ‖∑ j ∈ F, x j‖ ^ 2 = ∑ j ∈ F, ∑ k ∈ F, inner ℝ (x j) (x k) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
  rw [← e1, ← e2]
  exact h

/-- **Diagonal shell bounds suffice**: on mutually orthogonal shells, `‖T x‖ ≤ s_k ‖x‖` on shell `k`
and every partial sum `Σ s_l ≤ D` bound `T` by `D` on the closure of the span of the shells. The
off-diagonal blocks are bounded by `s_k s_l` (Cauchy–Schwarz). -/
theorem bound_on_diagShells {ι : Type*} {T : E →L[ℝ] E} (S : ι → Submodule ℝ E)
    (horth : ∀ k l, k ≠ l → ∀ x ∈ S k, ∀ y ∈ S l, inner ℝ x y = 0)
    (s : ι → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hdiag : ∀ k, ∀ x ∈ S k, ‖T x‖ ≤ s k * ‖x‖)
    {D : ℝ} (hsum : ∀ F : Finset ι, ∑ l ∈ F, s l ≤ D) :
    ∀ f ∈ closure ((⨆ k, S k : Submodule ℝ E) : Set E), ‖T f‖ ≤ D * ‖f‖ := by
  classical
  have hD0 : 0 ≤ D := by simpa using hsum ∅
  have hsD : ∀ k, s k ≤ D := fun k => by simpa using hsum {k}
  refine bound_on_shells S horth (fun k l => s k * s l) (fun k l => mul_nonneg (hs0 k) (hs0 l))
    (fun k l => mul_comm _ _) ?_ hD0 ?_
  · intro k l x hx y hy
    calc |inner ℝ (T x) (T y)| ≤ ‖T x‖ * ‖T y‖ := abs_real_inner_le_norm _ _
      _ ≤ (s k * ‖x‖) * (s l * ‖y‖) :=
        mul_le_mul (hdiag k x hx) (hdiag l y hy) (norm_nonneg _)
          (mul_nonneg (hs0 k) (norm_nonneg _))
      _ = s k * s l * (‖x‖ * ‖y‖) := by ring
  · intro k F
    rw [← Finset.mul_sum, sq]
    exact mul_le_mul (hsD k) (hsum F) (Finset.sum_nonneg fun l _ => hs0 l) hD0

end Blocks

section SliceGap

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.GlueballArea (ZeroFluxGap)
open MassGap.SlabKernelOperator (kernelCLM)

/-- **The gap from diagonal shell bounds alone.** On the zero-flux slice with `Ω = φ_{g₀}`: (E1), and on
each loop shell `k` the diagonal bound `‖T x‖ ≤ s_k ‖x‖`, with every partial sum of the `s_l` at most
`|μ_{g₀}| e^{−m t/2}`: then `ZeroFluxGap g₀ E m`. No off-diagonal clause is asked. -/
theorem zeroFluxGap_of_shellDiag {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (hgen : ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))))
    (s : ℕ → ℝ) (hs0 : ∀ k, 0 ≤ s k)
    (hdiag : ∀ k, ∀ x ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k,
      ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x‖ ≤ s k * ‖x‖)
    {m : ℝ} (hsum : ∀ F : Finset ℕ, ∑ l ∈ F, s l
      ≤ |μv g₀| * Real.exp (-(m * ((n : ℝ) * aRun 2 β)) / 2)) :
    ZeroFluxGap g₀ E m := by
  have ha : 0 < aRun 2 β := aRun_pos (by norm_num) hβ
  refine zeroFluxGap_of_levelBound hβ hn hL hm hkm hC0 hkb fun j hj => ?_
  exact bound_on_diagShells (shell (hSN 2 n i) (φ g₀) (aRun 2 β) R) (shell_orth _ _ hR) s hs0 hdiag
    hsum _ (closure_mono (span_allLoops_le (φ g₀) ha hR hreach) (hgen j hj))

/-- The rate of `zeroFluxGap_of_electricDiag`: `e^{−m t/2} = e^{−√(c c' σ) t/2} · q/(1 − q)`,
`q = e^{−c σ δ t/4}`. -/
def diagRate (c c' σ δ t : ℝ) : ℝ :=
  -2 * Real.log (Real.exp (-(Real.sqrt (c * c' * σ) * t / 2))
    * (Real.exp (-(c * σ * δ * t / 4)) / (1 - Real.exp (-(c * σ * δ * t / 4))))) / t

/-- `diagRate` is positive when `e^{−√(c c' σ) t/2} · q/(1 − q) < 1`. -/
theorem diagRate_pos {c c' σ δ t : ℝ} (ht : 0 < t) (hq : 0 < c * σ * δ * t)
    (h : Real.exp (-(Real.sqrt (c * c' * σ) * t / 2))
      * (Real.exp (-(c * σ * δ * t / 4)) / (1 - Real.exp (-(c * σ * δ * t / 4)))) < 1) :
    0 < diagRate c c' σ δ t := by
  have hq1 : Real.exp (-(c * σ * δ * t / 4)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hX : 0 < Real.exp (-(Real.sqrt (c * c' * σ) * t / 2))
      * (Real.exp (-(c * σ * δ * t / 4)) / (1 - Real.exp (-(c * σ * δ * t / 4)))) :=
    mul_pos (Real.exp_pos _) (div_pos (Real.exp_pos _) (by linarith))
  have hl := Real.log_neg hX h
  unfold diagRate
  exact div_pos (by linarith) ht

/-- **The electric diagonal alone gives the gap.** The diagonal clause of
`ElectricLoops.zeroFluxGap_of_electricCost`, `‖T x‖² ≤ μ_{g₀}² e^{−(c σ R_k + c'/R_k) t} ‖x‖²` on shell
`k`, with radii `R_k ≥ (k + 1) δ` and `c σ δ > 0`, gives `ZeroFluxGap g₀ E (diagRate c c' σ δ t)`. The
off-diagonal clause `η` of `zeroFluxGap_of_electricCost` is not asked. -/
theorem zeroFluxGap_of_electricDiag {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (hgen : ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))))
    {c c' σ δ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hδ : 0 < c * σ * δ)
    (hR0 : ∀ k, 0 < R k) (hRδ : ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k)
    (hdiag : ∀ k, ∀ x ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k,
      ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x‖ ^ 2
        ≤ μv g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))) * ‖x‖ ^ 2) :
    ZeroFluxGap g₀ E (diagRate c c' σ δ ((n : ℝ) * aRun 2 β)) := by
  set t := (n : ℝ) * aRun 2 β with ht
  have htpos : 0 < t := mul_pos (by exact_mod_cast hn) (aRun_pos (by norm_num) hβ)
  set q := Real.exp (-(c * σ * δ * t / 4)) with hqdef
  set A := Real.exp (-(Real.sqrt (c * c' * σ) * t / 2)) with hAdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hqdef, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith)
  set X := A * (q / (1 - q)) with hXdef
  have hX : 0 < X := mul_pos (Real.exp_pos _) (div_pos (Real.exp_pos _) (by linarith))
  set s : ℕ → ℝ := fun k => |μv g₀| * Real.exp (-((c * σ * R k + c' / R k) * t) / 2) with hsdef
  have hs0 : ∀ k, 0 ≤ s k := fun k => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  -- the diagonal bound in norm form
  have hdiag' : ∀ k, ∀ x ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k,
      ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x‖ ≤ s k * ‖x‖ := by
    intro k x hx
    have h := hdiag k x hx
    have he : Real.exp (-((c * σ * R k + c' / R k) * t) / 2) ^ 2
        = Real.exp (-((c * σ * R k + c' / R k) * t)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h2 : ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x‖ ^ 2
        ≤ (s k * ‖x‖) ^ 2 := by
      rw [hsdef]
      simp only
      rw [mul_pow, mul_pow, sq_abs, he]
      exact h
    exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (hs0 k) (norm_nonneg _)) h2
  -- each term against the geometric weight
  have hterm : ∀ k : ℕ, s k ≤ |μv g₀| * A * q ^ (k + 1) := by
    intro k
    have h1 := AttractCost.two_sqrt_le_cost hc hc' hσ (hR0 k)
    have h2 : c * σ * (((k : ℝ) + 1) * δ) ≤ c * σ * R k :=
      mul_le_mul_of_nonneg_left (hRδ k) (mul_nonneg hc hσ)
    have h3 : 0 ≤ c' / R k := div_nonneg hc' (hR0 k).le
    have hk : Real.sqrt (c * c' * σ) * t / 2 + ((k : ℝ) + 1) * (c * σ * δ * t / 4)
        ≤ (c * σ * R k + c' / R k) * t / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h1 htpos.le, mul_le_mul_of_nonneg_right h2 htpos.le,
        mul_nonneg h3 htpos.le]
    have hqk : q ^ (k + 1) = Real.exp (((k : ℝ) + 1) * (-(c * σ * δ * t / 4))) := by
      rw [hqdef, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [hsdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [hAdef, hqk, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [hk]
  -- the partial sums
  have hsum : ∀ F : Finset ℕ, ∑ l ∈ F, s l
      ≤ |μv g₀| * Real.exp (-(diagRate c c' σ δ t * t) / 2) := by
    intro F
    have hgeom : Summable fun l : ℕ => q ^ (l + 1) := by
      have := (summable_geometric_of_lt_one hq0 hq1).mul_left q
      refine this.congr fun l => ?_
      ring
    have htsum : ∑' l : ℕ, q ^ (l + 1) = q / (1 - q) := by
      have e : (fun l : ℕ => q ^ (l + 1)) = fun l => q * q ^ l := funext fun l => by ring
      rw [e, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
    have hF : ∑ l ∈ F, q ^ (l + 1) ≤ q / (1 - q) := by
      rw [← htsum]
      exact hgeom.sum_le_tsum F (fun l _ => pow_nonneg hq0 _)
    have hrate : Real.exp (-(diagRate c c' σ δ t * t) / 2) = X := by
      unfold diagRate
      rw [← hqdef, ← hAdef, ← hXdef]
      have : -(-2 * Real.log X / t * t) / 2 = Real.log X := by field_simp
      rw [this, Real.exp_log hX]
    rw [hrate]
    calc ∑ l ∈ F, s l ≤ ∑ l ∈ F, |μv g₀| * A * q ^ (l + 1) := Finset.sum_le_sum fun l _ => hterm l
      _ = |μv g₀| * A * ∑ l ∈ F, q ^ (l + 1) := by rw [Finset.mul_sum]
      _ ≤ |μv g₀| * A * (q / (1 - q)) :=
          mul_le_mul_of_nonneg_left hF (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      _ = |μv g₀| * X := by rw [hXdef]; ring
  exact zeroFluxGap_of_shellDiag hβ hn hL hm hkm hC0 hkb hR hreach hgen s hs0 hdiag' hsum

end SliceGap

/-! ## 4. The zoom on the rectangular torus: a loop of size `m × n` against the whole torus -/

section Zoom

open MassGap.RectWilson MassGap.TomboulisYaffe MassGap.Chessboard

variable (L : Fin 4 → ℕ)

/-- **The zoom, as a root.** On the rectangular `SU(2)` torus, with `L_a = 2^p m`, `L_b = 2^q n` and the
flux operator of the inside sheet: the `m × n` loop is bounded by the `mn/(L_a L_b)`-th power of the
loop once around the whole `(b, a)` torus (holonomy `P_b P_a P_b⁻¹ P_a⁻¹`). No hypothesis beyond
admissibility (`Chessboard.chain_full`). -/
theorem zoom_root {a b : Fin 4} (hab : a ≠ b) (o : RSite L) {m n p q : ℕ}
    (hA : VortexCondense.Adm (L a) (L b) m n) (hp : L a = 2 ^ p * m) (hq : L b = 2 ^ q * n) (β : ℝ) :
    |ev L β (fun U => fluxOp L β (sIn L a b m o) U
        * wObs L (VortexCondense.rectWord L a b m n o) U)|
      ≤ (ev L β (fun U => fluxOp L β (sIn L b a (L b) o) U
          * wObs L (VortexCondense.rectWord L b a (L b) (L a) o) U))
        ^ (((m : ℝ) * n) / ((L a : ℝ) * L b)) := by
  have h := chain_full L hab o hA hp hq β
  obtain ⟨hm, hn⟩ := adm_pos hA
  generalize ev L β (fun U => fluxOp L β (sIn L a b m o) U
    * wObs L (VortexCondense.rectWord L a b m n o) U) = x at h ⊢
  generalize ev L β (fun U => fluxOp L β (sIn L b a (L b) o) U
    * wObs L (VortexCondense.rectWord L b a (L b) (L a) o) U) = Y at h ⊢
  have hN : (2 ^ (p + q) : ℕ) ≠ 0 := by positivity
  have hY : 0 ≤ Y := (pow_nonneg (abs_nonneg x) _).trans h
  have hexp : ((m : ℝ) * n) / ((L a : ℝ) * L b) = (((2 ^ (p + q) : ℕ) : ℝ))⁻¹ := by
    rw [hp, hq]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    rw [pow_add]
    field_simp
  rw [hexp]
  calc |x| = (|x| ^ (2 ^ (p + q))) ^ ((((2 ^ (p + q) : ℕ) : ℝ))⁻¹) := by
        rw [Real.pow_rpow_inv_natCast (abs_nonneg x) hN]
    _ ≤ Y ^ ((((2 ^ (p + q) : ℕ) : ℝ))⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (abs_nonneg x) _) h (by positivity)

end Zoom

end MassGap.LoopZoom
