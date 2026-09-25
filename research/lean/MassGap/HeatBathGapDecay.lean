import Mathlib
import MassGap.KnabeCriterion
import MassGap.ContinuumSep
import MassGap.WeakCouplingWindow

noncomputable section

/-!
# MassGap.HeatBathGapDecay — a uniform heat-bath gap and locality give exponential clustering

## What it gives

1. **The seminorm of a patch system.** `nrm S x = √B(x, x)` on a `KnabeCriterion.PatchSystem`:
   Cauchy–Schwarz (`form_sq_le_mul`, `abs_form_le_nrm`), the triangle inequality (`nrm_add_le`,
   `nrm_sub_le`, `nrm_sum_le`), homogeneity (`nrm_smul`), and the contraction `nrm_h_le` of every
   `B`-self-adjoint idempotent `hᵢ`.
2. **The lazy heat bath.** `Tstep S K v = v − K⁻¹ · H v`, iterated by `Titer`. At any `0 < K` with
   `B(Hv, Hv) ≤ K · B(Hv, v)` (`H_form_le_card` gives it at `K = |ι|`, so at `Kc = |ι| + 1`) it is a
   contraction (`nrm_Tstep_le`), and at `c ≤ K` `GlobalGap c` contracts it on the range of `H` by
   `gapRate c K = 1 − cK⁻¹/2` (`range_gap`, `nrm_Tstep_range`, `nrm_Titer_H`). `range_gap` is the
   gap moved one step up the moment ladder: `c·B(Hx, x) ≤ B(Hx, Hx)` gives
   `c·B(Hx, Hx) ≤ B(H²x, Hx)` through Cauchy–Schwarz for the form `B(H·, ·)`.
3. **Finite speed of propagation.** A neighbour map `nb` with `|nb l| ≤ z` and `hₗ, hₗ'`
   commuting up to `B`-null vectors off `nb l`. `Far nb A k l`: every link within `k − 1`
   neighbour steps of `l` lies outside `A`. `lr_bound`: if `hₗ f` is null off `A`, then
   `‖hₗ Tᵐ f‖ ≤ ‖f‖ · y⁻ᵏ · (1 + 2zy/K)ᵐ` at every `Far k` link and every `y ≥ 1` — a
   Lieb–Robinson bound for the lazy heat bath, proved through the commutator identity `h_Tstep`.
4. **Clustering.** `cov_bound`: for `f` read on `A`, `g` read on `C`, `C` at level `k` from `A`,
   and `B(Tᴺ f, g) → L`: `|B(f, g) − L|` is at most a near part
   `n K⁻¹ |C| ‖f‖ y⁻ᵏ (1 + 2zy/K)ⁿ ‖g‖` (`near_part`) plus a far part
   `(2/c) gapRate c Kⁿ |A| ‖f‖ ‖g‖` (`far_part`, `tail_part`). `cov_bound_exp` takes `n = sK`:
   the bound reads `s |C| ‖f‖ y⁻ᵏ e^{2zys} ‖g‖ + (2/c) e^{−cs/2} |A| ‖f‖ ‖g‖`, free of `K`, so of
   the volume.
5. **At the periodic Wilson state.** `TorusClusterAt τ p hN β r`: every gauge-invariant half-space
   observable has a constant `K` with `torusConn j x (2n) ≤ K r^{2n}` for all large `j`.
   `gapAt_of_torusClusterAt`, `torusLagClear_of_torusClusterAt` (through
   `ContinuumSep.gapAt_of_per_vector_form_decay` and `WeakCouplingWindow.torusLagClear_of_gapAt`).
   `HeatBathCluster`: the uniform heat-bath gap gives `TorusClusterAt` at some rate below one;
   `heatBathDecay_of_heatBathCluster`: it gives `KnabeCriterion.HeatBathDecay`.
6. **The reduction.** `HeatBathLocality τ p hN β`: for every family of heat-bath systems, a uniform
   neighbour bound `z`, and for every observable `x` support bounds `a, b` and a norm bound `M` fixed
   before the lag, such that at every lag `2n`, for all large `j`, a pair `f, g` of the patch system
   (intended: `θx` and `S^{2n}x`) has supports of sizes at most `a, b` separated at level `n`,
   `B`-norms squared at most `M`, the ergodic limit `B(Tᴺ f, g) → L` of the lazy heat bath at
   `K = |ι| + 1`, and `torusConn j x (2n) = B(f, g) − L`. `LocalityAt τ p hN β S z` is its body for one
   family at one bound, and `torusClusterAt_of_localityAt` gives clustering at the explicit rate
   `clusterRate z c = √max(e/3, e^{−min(c,1)/(2(6z+1))})`. `heatBathCluster_of_locality` proves
   `HeatBathCluster` from it, and `heatBathDecay_of_locality` proves `KnabeCriterion.HeatBathDecay`.

## What `HeatBathLocality` asks

Its fields are of two kinds. Bookkeeping: `θx` and `S^{2n}x` are periodic gauge-invariant
observables, each reading at most as many torus links as `x` reads; `hₗ f` null off the torus links
`θx` reads (`WilsonHeatBath.keeps`); commutation up to null vectors off `SharePlaq` (any `condExp` agrees with
`HeatBath.torusCondExp` up to `torusForm`-null vectors, both being `torusForm`-orthogonal projections
onto the same subspace, and `HeatBath.torusCondExp_comm`); a neighbour count uniform in the extent;
the level-`n` separation of `θx` from `S^{2n}x` along `SharePlaq` steps, for torus extents large
against `n`; `B(θx, θx) ≤ ‖x‖²_∞`. Analytic: the fixed-volume ergodic limit
`B(Tᴺ θx, S^{2n}x) → μⱼ(θx) μⱼ(S^{2n}x)` of the lazy random-scan heat bath. The rate of that limit
is not used, so its constant may depend on the volume.

## The literature

A. Guionnet, B. Zegarlinski, Sém. Probab. XXXVI, LNM 1801 (2003), Theorem 8.8 and Remark 5: decay
of covariances from a spectral gap uniform in the volume through approximate locality of the
semigroup. Here the semigroup is replaced by the lazy chain `Tⁿ`, whose locality is the
Lieb–Robinson estimate `lr_bound` (E. Lieb, D. Robinson, Commun. Math. Phys. 28 (1972) 251–257;
the commutator form used is that of B. Nachtergaele, R. Sims, Commun. Math. Phys. 265 (2006)
119–130), and whose contraction on the range of `H` comes from `GlobalGap` alone.
-/

namespace MassGap.HeatBathGapDecay

open MassGap MassGap.KnabeCriterion Filter

/-! ## 1. The seminorm of a patch system -/

section Seminorm

/-- **The seminorm** `‖x‖ = √B(x, x)` of a patch system.

DERIVED: no numeral. -/
def nrm (S : PatchSystem) (x : S.E) : ℝ := Real.sqrt (S.B x x)

/-- `‖x‖ ≥ 0`.

DERIVED: `0` is the sign asserted. -/
theorem nrm_nonneg (S : PatchSystem) (x : S.E) : 0 ≤ nrm S x := Real.sqrt_nonneg _

#print axioms nrm_nonneg

/-- `‖x‖² = B(x, x)`.

DERIVED: `2` is the square. -/
theorem nrm_sq (S : PatchSystem) (x : S.E) : nrm S x ^ 2 = S.B x x := Real.sq_sqrt (S.nonneg x)

#print axioms nrm_sq

/-- **Cauchy–Schwarz for a symmetric non-negative bilinear form**: `Q(x, y)² ≤ Q(x, x) Q(y, y)`,
from the non-positive discriminant of `t ↦ Q(x + t y, x + t y)` (`discrim_le_zero`).

DERIVED: `2` is the square; `0` is the sign of the form. -/
theorem form_sq_le_mul {E : Type*} [AddCommGroup E] [Module ℝ E] (Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, Q x y = Q y x) (hnn : ∀ x, 0 ≤ Q x x) (x y : E) :
    Q x y ^ 2 ≤ Q x x * Q y y := by
  have h : ∀ t : ℝ, 0 ≤ Q y y * (t * t) + 2 * Q x y * t + Q x x := by
    intro t
    have h0 := hnn (x + t • y)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h0
    rw [hsymm y x] at h0
    linarith
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

#print axioms form_sq_le_mul

/-- **Cauchy–Schwarz in the seminorm**: `|B(x, y)| ≤ ‖x‖ ‖y‖`.

DERIVED: no numeral. -/
theorem abs_form_le_nrm (S : PatchSystem) (x y : S.E) : |S.B x y| ≤ nrm S x * nrm S y := by
  have h := form_sq_le_mul S.B S.symm S.nonneg x y
  show |S.B x y| ≤ Real.sqrt (S.B x x) * Real.sqrt (S.B y y)
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (S.nonneg x)]
  exact Real.sqrt_le_sqrt h

#print axioms abs_form_le_nrm

/-- **The triangle inequality** `‖x + y‖ ≤ ‖x‖ + ‖y‖`.

DERIVED: `2` is the cross term of the expanded square. -/
theorem nrm_add_le (S : PatchSystem) (x y : S.E) : nrm S (x + y) ≤ nrm S x + nrm S y := by
  have hxy := abs_form_le_nrm S x y
  have hexp : S.B (x + y) (x + y) = S.B x x + 2 * S.B x y + S.B y y := by
    simp only [map_add, LinearMap.add_apply]
    rw [S.symm y x]
    ring
  have h2 : S.B (x + y) (x + y) ≤ (nrm S x + nrm S y) ^ 2 := by
    rw [hexp]
    nlinarith [nrm_sq S x, nrm_sq S y, le_abs_self (S.B x y)]
  show Real.sqrt (S.B (x + y) (x + y)) ≤ nrm S x + nrm S y
  exact (Real.sqrt_le_left (add_nonneg (nrm_nonneg S x) (nrm_nonneg S y))).mpr h2

#print axioms nrm_add_le

/-- `‖x − y‖ ≤ ‖x‖ + ‖y‖`.

DERIVED: `2` is the cross term of the expanded square. -/
theorem nrm_sub_le (S : PatchSystem) (x y : S.E) : nrm S (x - y) ≤ nrm S x + nrm S y := by
  have hxy := abs_form_le_nrm S x y
  have hexp : S.B (x - y) (x - y) = S.B x x - 2 * S.B x y + S.B y y := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [S.symm y x]
    ring
  have h2 : S.B (x - y) (x - y) ≤ (nrm S x + nrm S y) ^ 2 := by
    rw [hexp]
    nlinarith [nrm_sq S x, nrm_sq S y, neg_abs_le (S.B x y)]
  show Real.sqrt (S.B (x - y) (x - y)) ≤ nrm S x + nrm S y
  exact (Real.sqrt_le_left (add_nonneg (nrm_nonneg S x) (nrm_nonneg S y))).mpr h2

#print axioms nrm_sub_le

/-- `‖a • x‖ = |a| ‖x‖`.

DERIVED: `2` is the square of the scalar. -/
theorem nrm_smul (S : PatchSystem) (a : ℝ) (x : S.E) : nrm S (a • x) = |a| * nrm S x := by
  show Real.sqrt (S.B (a • x) (a • x)) = |a| * Real.sqrt (S.B x x)
  have h : S.B (a • x) (a • x) = a ^ 2 * S.B x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

#print axioms nrm_smul

/-- `‖0‖ = 0`.

DERIVED: `0` is the vector and the value. -/
theorem nrm_zero (S : PatchSystem) : nrm S 0 = 0 := by
  show Real.sqrt (S.B 0 0) = 0
  simp only [map_zero, LinearMap.zero_apply, Real.sqrt_zero]

#print axioms nrm_zero

/-- A `B`-null vector has seminorm `0`.

DERIVED: `0` is the null value. -/
theorem nrm_eq_zero_of_null (S : PatchSystem) {z : S.E} (hz : S.B z z = 0) : nrm S z = 0 := by
  show Real.sqrt (S.B z z) = 0
  rw [hz, Real.sqrt_zero]

#print axioms nrm_eq_zero_of_null

/-- A `B`-null vector pairs to `0` with every vector (`abs_form_le_nrm`).

DERIVED: `0` is the null value. -/
theorem form_eq_zero_of_null (S : PatchSystem) {z : S.E} (hz : S.B z z = 0) (w : S.E) :
    S.B w z = 0 := by
  have h := abs_form_le_nrm S w z
  rw [nrm_eq_zero_of_null S hz, mul_zero] at h
  exact abs_nonpos_iff.mp h

#print axioms form_eq_zero_of_null

/-- **The triangle inequality over a finite sum** (`Finset.le_sum_of_subadditive`).

DERIVED: no numeral. -/
theorem nrm_sum_le (S : PatchSystem) {α : Type*} (s : Finset α) (v : α → S.E) :
    nrm S (∑ i ∈ s, v i) ≤ ∑ i ∈ s, nrm S (v i) :=
  Finset.le_sum_of_subadditive (nrm S) (le_of_eq (nrm_zero S)) (nrm_add_le S) s v

#print axioms nrm_sum_le

/-- **Each `hᵢ` is a contraction**: `B(x, x) = B(hᵢx, hᵢx) + B(x − hᵢx, x − hᵢx)`, the cross term
vanishing by `form_proj_self`.

DERIVED: no numeral. -/
theorem nrm_h_le (S : PatchSystem) (l : S.ι) (x : S.E) : nrm S (S.h l x) ≤ nrm S x := by
  have e := form_proj_self S.B (S.h l) (S.selfAdj l) (S.idem l) x
  have n := S.nonneg (x - S.h l x)
  simp only [map_sub, LinearMap.sub_apply] at n
  have hs := S.symm x (S.h l x)
  show Real.sqrt (S.B (S.h l x) (S.h l x)) ≤ Real.sqrt (S.B x x)
  exact Real.sqrt_le_sqrt (by linarith)

#print axioms nrm_h_le

end Seminorm

/-! ## 2. The lazy heat bath -/

section Lazy

/-- **One step of the lazy heat bath** `T v = v − K⁻¹ · H v`.

DERIVED: no numeral. -/
def Tstep (S : PatchSystem) (K : ℝ) (v : S.E) : S.E := v - K⁻¹ • S.H v

/-- **The iterated lazy heat bath** `Tᵐ`.

DERIVED: `0` and `1` are the recursion's base and step. -/
def Titer (S : PatchSystem) (K : ℝ) : ℕ → S.E → S.E
  | 0, v => v
  | m + 1, v => Tstep S K (Titer S K m v)

/-- `T⁰ v = v`.

DERIVED: `0` is the base of the recursion. -/
theorem Titer_zero (S : PatchSystem) (K : ℝ) (v : S.E) : Titer S K 0 v = v := rfl

#print axioms Titer_zero

/-- `Tᵐ⁺¹ v = T (Tᵐ v)`.

DERIVED: `1` is the step of the recursion. -/
theorem Titer_succ (S : PatchSystem) (K : ℝ) (m : ℕ) (v : S.E) :
    Titer S K (m + 1) v = Tstep S K (Titer S K m v) := rfl

#print axioms Titer_succ

/-- `H` is `B`-symmetric: `B(Hx, y) = B(x, Hy)`.

DERIVED: no numeral. -/
theorem H_symm (S : PatchSystem) (x y : S.E) : S.B (S.H x) y = S.B x (S.H y) := by
  show S.B (totalOp S.h x) y = S.B x (totalOp S.h y)
  simp only [totalOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => S.selfAdj i x y)

#print axioms H_symm

/-- `Σᵢ Σⱼ (aᵢ + aⱼ)/2 = |ι| Σᵢ aᵢ`.

DERIVED: `2` is the halving. -/
theorem sum_sum_half {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∑ i, ∑ j, (a i + a j) / 2 = (Fintype.card ι : ℝ) * ∑ i, a i := by
  have e : ∀ i, ∑ j, (a i + a j) / 2 = ((Fintype.card ι : ℝ) * a i + ∑ j, a j) / 2 := by
    intro i
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  ring

#print axioms sum_sum_half

/-- **`H` is bounded by the number of terms on its range**: `B(Hv, Hv) ≤ |ι| · B(Hv, v)`
(`abs_form_le` on every pair).

DERIVED: `2` is the halving of `abs_form_le`. -/
theorem H_form_le_card (S : PatchSystem) (v : S.E) :
    S.B (S.H v) (S.H v) ≤ (Fintype.card S.ι : ℝ) * S.B (S.H v) v := by
  have hD : S.B (S.H v) v = ∑ i, S.B (S.h i v) (S.h i v) := by
    show S.B (totalOp S.h v) v = _
    rw [totalOp_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => form_proj_self S.B (S.h i) (S.selfAdj i) (S.idem i) v)
  have hHH : S.B (S.H v) (S.H v) = ∑ i, ∑ j, S.B (S.h i v) (S.h j v) := by
    show S.B (totalOp S.h v) (totalOp S.h v) = _
    rw [totalOp_apply]
    exact form_sum_sum S.B (fun i => S.h i v) (fun j => S.h j v)
  have hle : ∑ i, ∑ j, S.B (S.h i v) (S.h j v)
      ≤ ∑ i, ∑ j, (S.B (S.h i v) (S.h i v) + S.B (S.h j v) (S.h j v)) / 2 :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      (le_abs_self _).trans (abs_form_le S.B S.symm S.nonneg _ _)))
  have hsum : ∑ i, ∑ j, (S.B (S.h i v) (S.h i v) + S.B (S.h j v) (S.h j v)) / 2
      = (Fintype.card S.ι : ℝ) * ∑ i, S.B (S.h i v) (S.h i v) :=
    sum_sum_half (fun i => S.B (S.h i v) (S.h i v))
  rw [hHH, hD]
  linarith

#print axioms H_form_le_card

/-- `H` commutes with a lazy step.

DERIVED: no numeral. -/
theorem H_Tstep (S : PatchSystem) (K : ℝ) (v : S.E) : S.H (Tstep S K v) = Tstep S K (S.H v) := by
  simp only [Tstep, map_sub, map_smul]

#print axioms H_Tstep

/-- `H` commutes with the iterated lazy heat bath.

DERIVED: no numeral. -/
theorem H_Titer (S : PatchSystem) (K : ℝ) (m : ℕ) (v : S.E) :
    S.H (Titer S K m v) = Titer S K m (S.H v) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Titer_succ, Titer_succ, H_Tstep, ih]

#print axioms H_Titer

/-- **The lazy step lowers the form by the Dirichlet form**: at `0 < K` with
`B(Hv, Hv) ≤ K · B(Hv, v)`, `B(Tv, Tv) ≤ B(v, v) − K⁻¹ · B(Hv, v)`.

DERIVED: `0` is the sign of `K`; `2` is the cross term. -/
theorem Tstep_form (S : PatchSystem) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (v : S.E) :
    S.B (Tstep S K v) (Tstep S K v) ≤ S.B v v - K⁻¹ * S.B (S.H v) v := by
  have hexp : S.B (Tstep S K v) (Tstep S K v)
      = S.B v v - 2 * K⁻¹ * S.B (S.H v) v + K⁻¹ * K⁻¹ * S.B (S.H v) (S.H v) := by
    have hs := S.symm v (S.H v)
    simp only [Tstep, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination (-K⁻¹) * hs
  have h1 : K⁻¹ * K⁻¹ * S.B (S.H v) (S.H v) ≤ K⁻¹ * K⁻¹ * (K * S.B (S.H v) v) :=
    mul_le_mul_of_nonneg_left (hK v)
      (mul_nonneg (inv_nonneg.mpr hK0.le) (inv_nonneg.mpr hK0.le))
  have h2 : K⁻¹ * K⁻¹ * (K * S.B (S.H v) v) = K⁻¹ * S.B (S.H v) v := by
    rw [show K⁻¹ * K⁻¹ * (K * S.B (S.H v) v) = K⁻¹ * (K⁻¹ * K) * S.B (S.H v) v by ring,
      inv_mul_cancel₀ hK0.ne', mul_one]
  rw [hexp]
  linarith

#print axioms Tstep_form

/-- **The lazy step is a contraction.**

DERIVED: `0` is the sign of `K`. -/
theorem nrm_Tstep_le (S : PatchSystem) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (v : S.E) :
    nrm S (Tstep S K v) ≤ nrm S v := by
  have h1 := Tstep_form S hK0 hK v
  have h2 : 0 ≤ K⁻¹ * S.B (S.H v) v := mul_nonneg (inv_nonneg.mpr hK0.le) (S.H_form_nonneg v)
  show Real.sqrt (S.B (Tstep S K v) (Tstep S K v)) ≤ Real.sqrt (S.B v v)
  exact Real.sqrt_le_sqrt (by linarith)

#print axioms nrm_Tstep_le

/-- **The iterated lazy heat bath is a contraction.**

DERIVED: `0` is the sign of `K`. -/
theorem nrm_Titer_le (S : PatchSystem) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (m : ℕ) (v : S.E) :
    nrm S (Titer S K m v) ≤ nrm S v := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Titer_succ]
    exact (nrm_Tstep_le S hK0 hK _).trans ih

#print axioms nrm_Titer_le

/-- **The gap one step up the moment ladder.** `GlobalGap c` (`c·B(Hx, x) ≤ B(Hx, Hx)`) gives
`c·B(Hw, Hw) ≤ B(H(Hw), Hw)`: Cauchy–Schwarz for the form `B(H·, ·)` at `w` and `Hw` is
`B(Hw, Hw)² ≤ B(Hw, w)·B(H(Hw), Hw)`, and the gap at `w` divides out `B(Hw, w)`.

DERIVED: `0` is the sign of the forms; `2` is the square of Cauchy–Schwarz. -/
theorem range_gap (S : PatchSystem) {c : ℝ} (hgap : S.GlobalGap c) (w : S.E) :
    c * S.B (S.H w) (S.H w) ≤ S.B (S.H (S.H w)) (S.H w) := by
  have hQs : ∀ u v : S.E, (S.B.comp S.H) u v = (S.B.comp S.H) v u := by
    intro u v
    show S.B (S.H u) v = S.B (S.H v) u
    rw [H_symm S u v, S.symm u (S.H v)]
  have hQn : ∀ u : S.E, 0 ≤ (S.B.comp S.H) u u := fun u => S.H_form_nonneg u
  have hcs : S.B (S.H w) (S.H w) ^ 2 ≤ S.B (S.H w) w * S.B (S.H (S.H w)) (S.H w) :=
    form_sq_le_mul (S.B.comp S.H) hQs hQn w (S.H w)
  have hX0 : 0 ≤ S.B (S.H w) w := S.H_form_nonneg w
  have hY0 : 0 ≤ S.B (S.H w) (S.H w) := S.nonneg _
  have hZ0 : 0 ≤ S.B (S.H (S.H w)) (S.H w) := S.H_form_nonneg (S.H w)
  have h1 : c * S.B (S.H w) w ≤ S.B (S.H w) (S.H w) := hgap w
  rcases eq_or_lt_of_le hX0 with hX | hX
  · rw [← hX, zero_mul] at hcs
    have hY : S.B (S.H w) (S.H w) = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hcs (sq_nonneg _))
    rw [hY, mul_zero]
    exact hZ0
  · by_contra hne
    push_neg at hne
    have h3 := mul_lt_mul_of_pos_left hne hX
    have h4 := mul_le_mul_of_nonneg_right h1 hY0
    nlinarith [hcs, h3, h4]

#print axioms range_gap

/-- **The contraction rate on the range of `H`**: `1 − cK⁻¹/2`.

DERIVED: `1` is the identity's rate; `2` is the square root step `√(1 − a) ≤ 1 − a/2`. -/
def gapRate (c K : ℝ) : ℝ := 1 - c * K⁻¹ / 2

/-- `0 ≤ gapRate c K` at `c ≤ K`.

DERIVED: `0` is the sign asserted and the sign of `K`. -/
theorem gapRate_nonneg {c K : ℝ} (hK0 : 0 < K) (hcK : c ≤ K) : 0 ≤ gapRate c K := by
  unfold gapRate
  have : c * K⁻¹ ≤ 1 := by
    calc c * K⁻¹ ≤ K * K⁻¹ := mul_le_mul_of_nonneg_right hcK (inv_nonneg.mpr hK0.le)
      _ = 1 := mul_inv_cancel₀ hK0.ne'
  linarith

#print axioms gapRate_nonneg

/-- `1 − gapRate c K = cK⁻¹/2`.

DERIVED: `1` and `2` are those of `gapRate`. -/
theorem one_sub_gapRate (c K : ℝ) : 1 - gapRate c K = c * K⁻¹ / 2 := by
  unfold gapRate
  ring

#print axioms one_sub_gapRate

/-- **The lazy step contracts the range of `H`**: under `GlobalGap c`, `0 < K`, `c ≤ K` and
`B(Hv, Hv) ≤ K·B(Hv, v)`: `‖T(Hw)‖ ≤ gapRate c K · ‖Hw‖` (`Tstep_form`, `range_gap`).

DERIVED: `0` is the sign of `K`; `2` is the square. -/
theorem nrm_Tstep_range (S : PatchSystem) {K c : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (hcK : c ≤ K)
    (hgap : S.GlobalGap c) (w : S.E) :
    nrm S (Tstep S K (S.H w)) ≤ gapRate c K * nrm S (S.H w) := by
  have hT := Tstep_form S hK0 hK (S.H w)
  have hg := range_gap S hgap w
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  have hg' := mul_le_mul_of_nonneg_left hg hKi
  have hY0 : 0 ≤ S.B (S.H w) (S.H w) := S.nonneg _
  have hsq : S.B (Tstep S K (S.H w)) (Tstep S K (S.H w)) ≤ (gapRate c K * nrm S (S.H w)) ^ 2 := by
    rw [mul_pow, nrm_sq]
    unfold gapRate
    nlinarith [hT, hg', mul_nonneg (sq_nonneg (c * K⁻¹)) hY0]
  show Real.sqrt (S.B (Tstep S K (S.H w)) (Tstep S K (S.H w))) ≤ gapRate c K * nrm S (S.H w)
  exact (Real.sqrt_le_left (mul_nonneg (gapRate_nonneg hK0 hcK) (nrm_nonneg S _))).mpr hsq

#print axioms nrm_Tstep_range

/-- **The iterated lazy heat bath contracts the range of `H` geometrically**: under `GlobalGap c`,
`0 < K`, `c ≤ K` and `B(Hv, Hv) ≤ K·B(Hv, v)`: `‖Tᵐ(Hf)‖ ≤ gapRate c Kᵐ · ‖Hf‖`
(`nrm_Tstep_range`, `H_Titer`).

DERIVED: `0` is the sign of `K`. -/
theorem nrm_Titer_H (S : PatchSystem) {K c : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (hcK : c ≤ K)
    (hgap : S.GlobalGap c) (f : S.E) (m : ℕ) :
    nrm S (Titer S K m (S.H f)) ≤ gapRate c K ^ m * nrm S (S.H f) := by
  have hρ := gapRate_nonneg hK0 hcK
  induction m with
  | zero =>
    rw [pow_zero, one_mul]
    exact le_rfl
  | succ m ih =>
    rw [Titer_succ, ← H_Titer, pow_succ]
    calc nrm S (Tstep S K (S.H (Titer S K m f)))
        ≤ gapRate c K * nrm S (S.H (Titer S K m f)) :=
          nrm_Tstep_range S hK0 hK hcK hgap _
      _ = gapRate c K * nrm S (Titer S K m (S.H f)) := by rw [H_Titer]
      _ ≤ gapRate c K * (gapRate c K ^ m * nrm S (S.H f)) := mul_le_mul_of_nonneg_left ih hρ
      _ = gapRate c K ^ m * gapRate c K * nrm S (S.H f) := by ring

#print axioms nrm_Titer_H

/-- **The step difference** `B(u, g) − B(Tu, g) = K⁻¹ · B(Hu, g)`.

DERIVED: no numeral. -/
theorem step_diff (S : PatchSystem) (K : ℝ) (u g : S.E) :
    S.B u g - S.B (Tstep S K u) g = K⁻¹ * S.B (S.H u) g := by
  simp only [Tstep, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

#print axioms step_diff

end Lazy

/-! ## 3. Finite speed of propagation -/

section Speed

/-- **Separation level.** `Far nb A k l`: every link reached from `l` in at most `k − 1` steps along
the neighbour map `nb` lies outside `A`. Level `0` asks nothing.

DERIVED: `0` and `1` are the recursion's base and step. -/
def Far {ι : Type*} (nb : ι → Finset ι) (A : Finset ι) : ℕ → ι → Prop
  | 0, _ => True
  | k + 1, l => l ∉ A ∧ Far nb A k l ∧ ∀ l' ∈ nb l, Far nb A k l'

/-- `Far` at a successor level, unfolded.

DERIVED: `1` is the step of the recursion. -/
theorem far_succ {ι : Type*} (nb : ι → Finset ι) (A : Finset ι) (k : ℕ) (l : ι) :
    Far nb A (k + 1) l ↔ (l ∉ A ∧ Far nb A k l ∧ ∀ l' ∈ nb l, Far nb A k l') := Iff.rfl

#print axioms far_succ

/-- **The propagation factor per lazy step**: `1 + 2zy/K`.

DERIVED: `1` is the identity's factor; `2` counts the two terms of a commutator. -/
def lrRate (z : ℕ) (y K : ℝ) : ℝ := 1 + 2 * (z : ℝ) * y / K

/-- `1 ≤ lrRate z y K` at `0 < K`, `0 ≤ y`.

DERIVED: `0` is the sign of `K` and `y`; `1` is the bound. -/
theorem one_le_lrRate {z : ℕ} {y K : ℝ} (hK0 : 0 < K) (hy : 0 ≤ y) : 1 ≤ lrRate z y K := by
  unfold lrRate
  have : 0 ≤ 2 * (z : ℝ) * y / K :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg z)) hy) hK0.le
  linarith

#print axioms one_le_lrRate

/-- **The commutator identity**
`hₗ(Tu) = T(hₗu) + K⁻¹ · Σ_{l'} (h_{l'}(hₗu) − hₗ(h_{l'}u))`.

DERIVED: no numeral. -/
theorem h_Tstep (S : PatchSystem) (K : ℝ) (l : S.ι) (u : S.E) :
    S.h l (Tstep S K u)
      = Tstep S K (S.h l u) + K⁻¹ • ∑ l', (S.h l' (S.h l u) - S.h l (S.h l' u)) := by
  simp only [Tstep, PatchSystem.H, totalOp_apply, map_sub, map_smul, map_sum,
    Finset.sum_sub_distrib, smul_sub]
  abel

#print axioms h_Tstep

/-- **One lazy step moves `hₗ` by its neighbours only.** If `hₗ` and `h_{l'}` commute up to
`B`-null vectors whenever `l' ∉ nb l`:
`‖hₗ(Tu)‖ ≤ ‖hₗu‖ + K⁻¹ Σ_{l' ∈ nb l} (‖hₗu‖ + ‖h_{l'}u‖)` (`h_Tstep`, `nrm_Tstep_le`, `nrm_h_le`).

DERIVED: `0` is the sign of `K` and the null value. -/
theorem nrm_h_Tstep (S : PatchSystem) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (nb : S.ι → Finset S.ι)
    (hcomm : ∀ l l', l' ∉ nb l → ∀ u : S.E,
      S.B (S.h l' (S.h l u) - S.h l (S.h l' u)) (S.h l' (S.h l u) - S.h l (S.h l' u)) = 0)
    (l : S.ι) (u : S.E) :
    nrm S (S.h l (Tstep S K u))
      ≤ nrm S (S.h l u) + K⁻¹ * ∑ l' ∈ nb l, (nrm S (S.h l u) + nrm S (S.h l' u)) := by
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  have hsub : ∑ l' ∈ nb l, nrm S (S.h l' (S.h l u) - S.h l (S.h l' u))
      = ∑ l', nrm S (S.h l' (S.h l u) - S.h l (S.h l' u)) :=
    Finset.sum_subset (Finset.subset_univ (nb l))
      (fun l' _ hl' => nrm_eq_zero_of_null S (hcomm l l' hl' u))
  have hsum : nrm S (∑ l', (S.h l' (S.h l u) - S.h l (S.h l' u)))
      ≤ ∑ l' ∈ nb l, (nrm S (S.h l u) + nrm S (S.h l' u)) := by
    calc nrm S (∑ l', (S.h l' (S.h l u) - S.h l (S.h l' u)))
        ≤ ∑ l', nrm S (S.h l' (S.h l u) - S.h l (S.h l' u)) := nrm_sum_le S Finset.univ _
      _ = ∑ l' ∈ nb l, nrm S (S.h l' (S.h l u) - S.h l (S.h l' u)) := hsub.symm
      _ ≤ ∑ l' ∈ nb l, (nrm S (S.h l u) + nrm S (S.h l' u)) := Finset.sum_le_sum (fun l' _ =>
          (nrm_sub_le S _ _).trans (add_le_add (nrm_h_le S l' _) (nrm_h_le S l _)))
  rw [h_Tstep S K l u]
  calc nrm S (Tstep S K (S.h l u) + K⁻¹ • ∑ l', (S.h l' (S.h l u) - S.h l (S.h l' u)))
      ≤ nrm S (Tstep S K (S.h l u))
          + nrm S (K⁻¹ • ∑ l', (S.h l' (S.h l u) - S.h l (S.h l' u))) := nrm_add_le S _ _
    _ = nrm S (Tstep S K (S.h l u))
          + K⁻¹ * nrm S (∑ l', (S.h l' (S.h l u) - S.h l (S.h l' u))) := by
        rw [nrm_smul, abs_of_nonneg hKi]
    _ ≤ nrm S (S.h l u) + K⁻¹ * ∑ l' ∈ nb l, (nrm S (S.h l u) + nrm S (S.h l' u)) :=
        add_le_add (nrm_Tstep_le S hK0 hK _) (mul_le_mul_of_nonneg_left hsum hKi)

#print axioms nrm_h_Tstep

/-- **THE LIEB–ROBINSON BOUND FOR THE LAZY HEAT BATH.** With `|nb l| ≤ z`, commutation up to null
vectors off `nb`, `y ≥ 1`, and `hₗ f` null for every `l ∉ A`: at every link `l` with
`Far nb A k l`, `‖hₗ Tᵐ f‖ ≤ ‖f‖ · y⁻ᵏ · lrRate z y Kᵐ`. Induction on `m`: the base is `hₗ f` null
off `A` and `nrm_h_le`; the step is `nrm_h_Tstep`, where the level-`(k + 1)` link keeps its
factor `y⁻ᵏ⁻¹` and each neighbour, at level `k`, contributes `y` times it, and
`z(1 + y) ≤ 2zy`.

DERIVED: `0` is the sign of `K` and the null value; `1` is the lower bound on `y`. -/
theorem lr_bound (S : PatchSystem) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (nb : S.ι → Finset S.ι)
    {z : ℕ} (hz : ∀ l, (nb l).card ≤ z)
    (hcomm : ∀ l l', l' ∉ nb l → ∀ u : S.E,
      S.B (S.h l' (S.h l u) - S.h l (S.h l' u)) (S.h l' (S.h l u) - S.h l (S.h l' u)) = 0)
    {y : ℝ} (hy : 1 ≤ y) (A : Finset S.ι) (f : S.E)
    (hf : ∀ l, l ∉ A → S.B (S.h l f) (S.h l f) = 0) (m : ℕ) :
    ∀ (k : ℕ) (l : S.ι), Far nb A k l →
      nrm S (S.h l (Titer S K m f)) ≤ nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ m) := by
  have hy0 : 0 < y := by linarith
  have hyi : 0 ≤ y⁻¹ := inv_nonneg.mpr hy0.le
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  have hq1 : 1 ≤ lrRate z y K := one_le_lrRate hK0 hy0.le
  have hq0 : 0 ≤ lrRate z y K := by linarith
  have hnf := nrm_nonneg S f
  induction m with
  | zero =>
    intro k l hkl
    cases k with
    | zero =>
      simp only [pow_zero, mul_one]
      rw [Titer_zero]
      exact nrm_h_le S l f
    | succ k =>
      have hl : l ∉ A := ((far_succ nb A k l).mp hkl).1
      rw [Titer_zero, nrm_eq_zero_of_null S (hf l hl)]
      exact mul_nonneg hnf (mul_nonneg (pow_nonneg hyi _) (pow_nonneg hq0 _))
  | succ m ih =>
    intro k l hkl
    cases k with
    | zero =>
      rw [pow_zero, one_mul]
      calc nrm S (S.h l (Titer S K (m + 1) f)) ≤ nrm S (Titer S K (m + 1) f) := nrm_h_le S l _
        _ ≤ nrm S f := nrm_Titer_le S hK0 hK (m + 1) f
        _ ≤ nrm S f * lrRate z y K ^ (m + 1) := le_mul_of_one_le_right hnf (one_le_pow₀ hq1)
    | succ k =>
      obtain ⟨_, _, hnb⟩ := (far_succ nb A k l).mp hkl
      obtain ⟨P, hP⟩ : ∃ P : ℝ, P = nrm S f * ((y⁻¹) ^ (k + 1) * lrRate z y K ^ m) := ⟨_, rfl⟩
      have hP0 : 0 ≤ P := by
        rw [hP]
        exact mul_nonneg hnf (mul_nonneg (pow_nonneg hyi _) (pow_nonneg hq0 _))
      have hself : nrm S (S.h l (Titer S K m f)) ≤ P := by
        rw [hP]
        exact ih (k + 1) l hkl
      have hyk : nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ m) = y * P := by
        have hy1 : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
        rw [hP, pow_succ]
        linear_combination (-(nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ m))) * hy1
      have hnbb : ∀ l' ∈ nb l, nrm S (S.h l' (Titer S K m f)) ≤ y * P := by
        intro l' hl'
        rw [← hyk]
        exact ih k l' (hnb l' hl')
      have hsumb : ∑ l' ∈ nb l, (nrm S (S.h l (Titer S K m f)) + nrm S (S.h l' (Titer S K m f)))
          ≤ (z : ℝ) * (P + y * P) := by
        calc ∑ l' ∈ nb l, (nrm S (S.h l (Titer S K m f)) + nrm S (S.h l' (Titer S K m f)))
            ≤ ∑ l' ∈ nb l, (P + y * P) :=
              Finset.sum_le_sum (fun l' hl' => add_le_add hself (hnbb l' hl'))
          _ = ((nb l).card : ℝ) * (P + y * P) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (z : ℝ) * (P + y * P) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hz l)
                (add_nonneg hP0 (mul_nonneg hy0.le hP0))
      have hstep := nrm_h_Tstep S hK0 hK nb hcomm l (Titer S K m f)
      have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
      have key : 0 ≤ P * z * (y - 1) * K⁻¹ :=
        mul_nonneg (mul_nonneg (mul_nonneg hP0 hz0) (by linarith)) hKi
      have e : nrm S f * ((y⁻¹) ^ (k + 1) * lrRate z y K ^ (m + 1))
          = P + 2 * P * z * y * K⁻¹ := by
        rw [hP]
        unfold lrRate
        ring
      rw [Titer_succ, e]
      have h2 := mul_le_mul_of_nonneg_left hsumb hKi
      linarith [hstep, hself, h2, key]

#print axioms lr_bound

end Speed

/-! ## 4. Clustering -/

section Cluster

/-- **`B(Hu, g)` reads only the links `g` reads.** If `hₗ g` is null for every `l ∉ C`:
`|B(Hu, g)| ≤ Σ_{l ∈ C} ‖hₗu‖ ‖g‖`.

DERIVED: `0` is the null value. -/
theorem form_H_local (S : PatchSystem) (C : Finset S.ι) (g : S.E)
    (hg : ∀ l, l ∉ C → S.B (S.h l g) (S.h l g) = 0) (u : S.E) :
    |S.B (S.H u) g| ≤ ∑ l ∈ C, nrm S (S.h l u) * nrm S g := by
  have hsub : ∑ l ∈ C, S.B (S.h l u) g = ∑ l, S.B (S.h l u) g :=
    Finset.sum_subset (Finset.subset_univ C) (fun l _ hl => by
      rw [S.selfAdj l u g]
      exact form_eq_zero_of_null S (hg l hl) u)
  have hsplit : S.B (S.H u) g = ∑ l ∈ C, S.B (S.h l u) g := by
    rw [hsub]
    show S.B (totalOp S.h u) g = _
    rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  rw [hsplit]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun l _ => abs_form_le_nrm S _ _))

#print axioms form_H_local

/-- **`‖Hf‖ ≤ |A| ‖f‖`** when `hₗ f` is null for every `l ∉ A`.

DERIVED: `0` is the null value. -/
theorem nrm_H_local (S : PatchSystem) (A : Finset S.ι) (f : S.E)
    (hf : ∀ l, l ∉ A → S.B (S.h l f) (S.h l f) = 0) :
    nrm S (S.H f) ≤ A.card * nrm S f := by
  have h1 : nrm S (S.H f) ≤ ∑ l, nrm S (S.h l f) := by
    show nrm S (totalOp S.h f) ≤ _
    rw [totalOp_apply]
    exact nrm_sum_le S Finset.univ _
  have h2 : ∑ l ∈ A, nrm S (S.h l f) = ∑ l, nrm S (S.h l f) :=
    Finset.sum_subset (Finset.subset_univ A) (fun l _ hl => nrm_eq_zero_of_null S (hf l hl))
  have h3 : ∑ l ∈ A, nrm S (S.h l f) ≤ ∑ l ∈ A, nrm S f :=
    Finset.sum_le_sum (fun l _ => nrm_h_le S l f)
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  linarith

#print axioms nrm_H_local

/-- **The near part.** Under the hypotheses of `lr_bound`, with `hₗ g` null off `C` and every link of
`C` at level `k` from `A`: `|B(f, g) − B(Tⁿf, g)| ≤ n K⁻¹ |C| ‖f‖ y⁻ᵏ lrRate z y Kⁿ ‖g‖`. Each step
is `K⁻¹ B(H Tᵐ f, g)` (`step_diff`), read on `C` (`form_H_local`) and bounded by `lr_bound`.

DERIVED: `0` is the sign of `K` and the null value; `1` is the lower bound on `y`. -/
theorem near_part (S : PatchSystem) {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (nb : S.ι → Finset S.ι)
    {z : ℕ} (hz : ∀ l, (nb l).card ≤ z)
    (hcomm : ∀ l l', l' ∉ nb l → ∀ u : S.E,
      S.B (S.h l' (S.h l u) - S.h l (S.h l' u)) (S.h l' (S.h l u) - S.h l (S.h l' u)) = 0)
    {y : ℝ} (hy : 1 ≤ y) (A C : Finset S.ι) (f g : S.E)
    (hf : ∀ l, l ∉ A → S.B (S.h l f) (S.h l f) = 0)
    (hg : ∀ l, l ∉ C → S.B (S.h l g) (S.h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far nb A k l) (n : ℕ) :
    |S.B f g - S.B (Titer S K n f) g|
      ≤ n * K⁻¹ * C.card * (nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n)) * nrm S g := by
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  have hnf := nrm_nonneg S f
  have hng := nrm_nonneg S g
  have hY : 0 ≤ (y⁻¹) ^ k := pow_nonneg (inv_nonneg.mpr (by linarith)) k
  have hq1 : 1 ≤ lrRate z y K := one_le_lrRate hK0 (by linarith)
  induction n with
  | zero => simp only [Titer_zero, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have hstep : |S.B (Titer S K n f) g - S.B (Titer S K (n + 1) f) g|
        ≤ K⁻¹ * C.card * (nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n)) * nrm S g := by
      rw [Titer_succ, step_diff, abs_mul, abs_of_nonneg hKi]
      have h1 := form_H_local S C g hg (Titer S K n f)
      have h2 : ∑ l ∈ C, nrm S (S.h l (Titer S K n f)) * nrm S g
          ≤ ∑ l ∈ C, nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n) * nrm S g :=
        Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_right
          (lr_bound S hK0 hK nb hz hcomm hy A f hf n k l (hfar l hl)) hng)
      rw [Finset.sum_const, nsmul_eq_mul] at h2
      calc K⁻¹ * |S.B (S.H (Titer S K n f)) g|
          ≤ K⁻¹ * (C.card * (nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n) * nrm S g)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hKi
        _ = K⁻¹ * C.card * (nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n)) * nrm S g := by ring
    have hmono : nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n)
        ≤ nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (Nat.le_succ n)) hY) hnf
    have hpre : 0 ≤ ((n : ℝ) + 1) * K⁻¹ * C.card :=
      mul_nonneg (mul_nonneg (by positivity) hKi) (Nat.cast_nonneg _)
    have hm2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hpre) hng
    have htri := abs_sub_le (S.B f g) (S.B (Titer S K n f) g) (S.B (Titer S K (n + 1) f) g)
    push_cast
    linarith [ih, hstep, hm2, htri]

#print axioms near_part

/-- **The tail of the lazy chain.** Under `GlobalGap c`, `0 < c ≤ K` and
`B(Hv, Hv) ≤ K·B(Hv, v)`: `|B(Tⁿf, g) − B(Tⁿ⁺ᵈf, g)| ≤ (2/c)(ρⁿ − ρⁿ⁺ᵈ) ‖Hf‖ ‖g‖`,
`ρ = gapRate c K`. Each step is `K⁻¹ B(Tᵐ Hf, g)` (`step_diff`, `H_Titer`), at most
`K⁻¹ ρᵐ ‖Hf‖ ‖g‖` (`nrm_Titer_H`), and `K⁻¹ ρᵐ = (2/c)(ρᵐ − ρᵐ⁺¹)` (`one_sub_gapRate`).

DERIVED: `0` is the sign of `K` and `c`; `2` is that of `gapRate`. -/
theorem tail_part (S : PatchSystem) {K c : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (hc : 0 < c) (hcK : c ≤ K)
    (hgap : S.GlobalGap c) (f g : S.E) (n : ℕ) :
    ∀ d : ℕ, |S.B (Titer S K n f) g - S.B (Titer S K (n + d) f) g|
      ≤ 2 / c * (gapRate c K ^ n - gapRate c K ^ (n + d)) * nrm S (S.H f) * nrm S g := by
  have hKi : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  intro d
  induction d with
  | zero => simp only [Nat.add_zero, sub_self, abs_zero, mul_zero, zero_mul, le_refl]
  | succ d ih =>
    have hterm : |S.B (Titer S K (n + d) f) g - S.B (Titer S K (n + d + 1) f) g|
        ≤ K⁻¹ * gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g := by
      rw [Titer_succ, step_diff, abs_mul, abs_of_nonneg hKi]
      have h1 : |S.B (S.H (Titer S K (n + d) f)) g|
          ≤ gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g := by
        calc |S.B (S.H (Titer S K (n + d) f)) g|
            ≤ nrm S (S.H (Titer S K (n + d) f)) * nrm S g := abs_form_le_nrm S _ _
          _ = nrm S (Titer S K (n + d) (S.H f)) * nrm S g := by rw [H_Titer]
          _ ≤ gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g :=
              mul_le_mul_of_nonneg_right (nrm_Titer_H S hK0 hK hcK hgap f (n + d))
                (nrm_nonneg S g)
      calc K⁻¹ * |S.B (S.H (Titer S K (n + d) f)) g|
          ≤ K⁻¹ * (gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g) :=
            mul_le_mul_of_nonneg_left h1 hKi
        _ = K⁻¹ * gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g := by ring
    have hid : K⁻¹ * gapRate c K ^ (n + d)
        = 2 / c * (gapRate c K ^ (n + d) - gapRate c K ^ (n + d + 1)) := by
      have e1 := one_sub_gapRate c K
      have e2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
      rw [pow_succ]
      linear_combination (-(K⁻¹ * gapRate c K ^ (n + d))) * e2
        + (-(2 * c⁻¹ * gapRate c K ^ (n + d))) * e1
    have htri := abs_sub_le (S.B (Titer S K n f) g) (S.B (Titer S K (n + d) f) g)
      (S.B (Titer S K (n + d + 1) f) g)
    have hfin : 2 / c * (gapRate c K ^ n - gapRate c K ^ (n + d)) * nrm S (S.H f) * nrm S g
          + K⁻¹ * gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g
        = 2 / c * (gapRate c K ^ n - gapRate c K ^ (n + d + 1)) * nrm S (S.H f) * nrm S g := by
      rw [hid]
      ring
    rw [← add_assoc]
    linarith [htri, ih, hterm, hfin]

#print axioms tail_part

/-- **The far part.** If `B(Tᴺf, g) → L`: `|B(Tⁿf, g) − L| ≤ (2/c) ρⁿ ‖Hf‖ ‖g‖`
(`tail_part`, `le_of_tendsto`, `ge_of_tendsto`).

DERIVED: `0` is the sign of `K` and `c`; `2` is that of `gapRate`. -/
theorem far_part (S : PatchSystem) {K c : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (hc : 0 < c) (hcK : c ≤ K)
    (hgap : S.GlobalGap c) (f g : S.E) {L : ℝ}
    (herg : Tendsto (fun M => S.B (Titer S K M f) g) atTop (nhds L)) (n : ℕ) :
    |S.B (Titer S K n f) g - L| ≤ 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g := by
  have hev : ∀ᶠ M in atTop, |S.B (Titer S K n f) g - S.B (Titer S K M f) g|
      ≤ 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g := by
    filter_upwards [eventually_ge_atTop n] with M hM
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    have h := tail_part S hK0 hK hc hcK hgap f g n d
    have hpos : 0 ≤ 2 / c * gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g :=
      mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg zero_le_two hc.le)
        (pow_nonneg (gapRate_nonneg hK0 hcK) _)) (nrm_nonneg S _)) (nrm_nonneg S g)
    have he : 2 / c * (gapRate c K ^ n - gapRate c K ^ (n + d)) * nrm S (S.H f) * nrm S g
        = 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g
          - 2 / c * gapRate c K ^ (n + d) * nrm S (S.H f) * nrm S g := by ring
    linarith
  have hup : L ≤ S.B (Titer S K n f) g + 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g :=
    le_of_tendsto herg (hev.mono (fun M hM => by
      show S.B (Titer S K M f) g
        ≤ S.B (Titer S K n f) g + 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g
      linarith [(abs_le.mp hM).1]))
  have hlo : S.B (Titer S K n f) g - 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g ≤ L :=
    ge_of_tendsto herg (hev.mono (fun M hM => by
      show S.B (Titer S K n f) g - 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g
        ≤ S.B (Titer S K M f) g
      linarith [(abs_le.mp hM).2]))
  rw [abs_le]
  constructor <;> linarith

#print axioms far_part

/-- **THE CLUSTERING BOUND.** On a patch system with `B(Hv, Hv) ≤ K·B(Hv, v)`, `GlobalGap c`,
`0 < c ≤ K`; a neighbour map `nb` with `|nb l| ≤ z` and commutation up to null vectors off `nb`;
`y ≥ 1`; `hₗ f` null off `A`, `hₗ g` null off `C`, every link of `C` at level `k` from `A`; and
`B(Tᴺf, g) → L`: for every `n`,

    |B(f, g) − L| ≤ n K⁻¹ |C| ‖f‖ y⁻ᵏ lrRate z y Kⁿ ‖g‖ + (2/c) gapRate c Kⁿ |A| ‖f‖ ‖g‖

(`near_part`, `far_part`, `nrm_H_local`).

DERIVED: `0` is the sign of `K`, `c` and the null value; `1` is the lower bound on `y`; `2` is that
of `gapRate`. -/
theorem cov_bound (S : PatchSystem) {K c : ℝ} (hK0 : 0 < K)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ K * S.B (S.H v) v) (hc : 0 < c) (hcK : c ≤ K)
    (hgap : S.GlobalGap c) (nb : S.ι → Finset S.ι) {z : ℕ} (hz : ∀ l, (nb l).card ≤ z)
    (hcomm : ∀ l l', l' ∉ nb l → ∀ u : S.E,
      S.B (S.h l' (S.h l u) - S.h l (S.h l' u)) (S.h l' (S.h l u) - S.h l (S.h l' u)) = 0)
    {y : ℝ} (hy : 1 ≤ y) (A C : Finset S.ι) (f g : S.E)
    (hf : ∀ l, l ∉ A → S.B (S.h l f) (S.h l f) = 0)
    (hg : ∀ l, l ∉ C → S.B (S.h l g) (S.h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far nb A k l) {L : ℝ}
    (herg : Tendsto (fun M => S.B (Titer S K M f) g) atTop (nhds L)) (n : ℕ) :
    |S.B f g - L|
      ≤ n * K⁻¹ * C.card * (nrm S f * ((y⁻¹) ^ k * lrRate z y K ^ n)) * nrm S g
        + 2 / c * gapRate c K ^ n * (A.card * nrm S f) * nrm S g := by
  have h1 := near_part S hK0 hK nb hz hcomm hy A C f g hf hg k hfar n
  have h2 := far_part S hK0 hK hc hcK hgap f g herg n
  have h3 := nrm_H_local S A f hf
  have h4 : 2 / c * gapRate c K ^ n * nrm S (S.H f) * nrm S g
      ≤ 2 / c * gapRate c K ^ n * (A.card * nrm S f) * nrm S g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3
      (mul_nonneg (div_nonneg zero_le_two hc.le) (pow_nonneg (gapRate_nonneg hK0 hcK) n)))
      (nrm_nonneg S g)
  calc |S.B f g - L| ≤ |S.B f g - S.B (Titer S K n f) g| + |S.B (Titer S K n f) g - L| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 (h2.trans h4)

#print axioms cov_bound

/-- `(1 + a)ᴺ ≤ e^{N a}` at `0 ≤ 1 + a` (`Real.add_one_le_exp`).

DERIVED: `0` and `1` are the base's sign and unit. -/
theorem pow_le_exp_mul {a : ℝ} (ha : 0 ≤ 1 + a) (N : ℕ) : (1 + a) ^ N ≤ Real.exp (N * a) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ ha (by linarith [Real.add_one_le_exp a]) N

#print axioms pow_le_exp_mul

/-- **THE CLUSTERING BOUND AT `n = sK`, FREE OF THE VOLUME.** With `K = Kn` a positive integer and
`n = s·Kn` lazy steps:

    |B(f, g) − L| ≤ s |C| ‖f‖ y⁻ᵏ e^{2zys} ‖g‖ + (2/c) e^{−cs/2} |A| ‖f‖ ‖g‖

(`cov_bound`, `pow_le_exp_mul`). `Kn` enters the hypotheses (`B(Hv, Hv) ≤ Kn·B(Hv, v)`, `c ≤ Kn`
and the lazy chain whose limit is `L`) and not the bound.

DERIVED: `0` is the sign of `Kn`, `c` and the null value; `1` is the lower bound on `y`; `2` is that
of `gapRate` and `lrRate`. -/
theorem cov_bound_exp (S : PatchSystem) {Kn : ℕ} (hKn : 0 < Kn)
    (hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ (Kn : ℝ) * S.B (S.H v) v) {c : ℝ} (hc : 0 < c)
    (hcK : c ≤ (Kn : ℝ)) (hgap : S.GlobalGap c) (nb : S.ι → Finset S.ι) {z : ℕ}
    (hz : ∀ l, (nb l).card ≤ z)
    (hcomm : ∀ l l', l' ∉ nb l → ∀ u : S.E,
      S.B (S.h l' (S.h l u) - S.h l (S.h l' u)) (S.h l' (S.h l u) - S.h l (S.h l' u)) = 0)
    {y : ℝ} (hy : 1 ≤ y) (A C : Finset S.ι) (f g : S.E)
    (hf : ∀ l, l ∉ A → S.B (S.h l f) (S.h l f) = 0)
    (hg : ∀ l, l ∉ C → S.B (S.h l g) (S.h l g) = 0)
    (k : ℕ) (hfar : ∀ l ∈ C, Far nb A k l) {L : ℝ}
    (herg : Tendsto (fun M => S.B (Titer S (Kn : ℝ) M f) g) atTop (nhds L)) (s : ℕ) :
    |S.B f g - L|
      ≤ s * C.card * (nrm S f * ((y⁻¹) ^ k * Real.exp (2 * z * y * s))) * nrm S g
        + 2 / c * Real.exp (-(c * s / 2)) * (A.card * nrm S f) * nrm S g := by
  have hK0 : (0 : ℝ) < Kn := Nat.cast_pos.mpr hKn
  have hKK : (Kn : ℝ) * (Kn : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK0.ne'
  have h := cov_bound S hK0 hK hc hcK hgap nb hz hcomm hy A C f g hf hg k hfar herg (s * Kn)
  have e1 : ((s * Kn : ℕ) : ℝ) * (Kn : ℝ)⁻¹ = s := by
    push_cast
    linear_combination (s : ℝ) * hKK
  have hq : lrRate z y Kn ^ (s * Kn) ≤ Real.exp (2 * z * y * s) := by
    unfold lrRate
    have h0 : 0 ≤ 2 * (z : ℝ) * y / Kn :=
      div_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg z)) (by linarith)) hK0.le
    calc (1 + 2 * (z : ℝ) * y / Kn) ^ (s * Kn)
        ≤ Real.exp (((s * Kn : ℕ) : ℝ) * (2 * (z : ℝ) * y / Kn)) :=
          pow_le_exp_mul (by linarith) (s * Kn)
      _ = Real.exp (2 * z * y * s) := by
          congr 1
          push_cast
          rw [div_eq_mul_inv]
          linear_combination (2 * (z : ℝ) * y * s) * hKK
  have hρ : gapRate c Kn ^ (s * Kn) ≤ Real.exp (-(c * s / 2)) := by
    have hg0 := gapRate_nonneg hK0 hcK
    calc gapRate c Kn ^ (s * Kn) = (1 + (-(c * (Kn : ℝ)⁻¹ / 2))) ^ (s * Kn) := by
          unfold gapRate
          rw [sub_eq_add_neg]
      _ ≤ Real.exp (((s * Kn : ℕ) : ℝ) * (-(c * (Kn : ℝ)⁻¹ / 2))) :=
          pow_le_exp_mul (by unfold gapRate at hg0; linarith) (s * Kn)
      _ = Real.exp (-(c * s / 2)) := by
          congr 1
          push_cast
          linear_combination (-(c * s / 2)) * hKK
  rw [e1] at h
  have hnf := nrm_nonneg S f
  have hng := nrm_nonneg S g
  have hY : 0 ≤ (y⁻¹) ^ k := pow_nonneg (inv_nonneg.mpr (by linarith)) k
  have t1 : (s : ℝ) * C.card * (nrm S f * ((y⁻¹) ^ k * lrRate z y Kn ^ (s * Kn))) * nrm S g
      ≤ s * C.card * (nrm S f * ((y⁻¹) ^ k * Real.exp (2 * z * y * s))) * nrm S g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hY) hnf) (by positivity)) hng
  have t2 : 2 / c * gapRate c Kn ^ (s * Kn) * (A.card * nrm S f) * nrm S g
      ≤ 2 / c * Real.exp (-(c * s / 2)) * (A.card * nrm S f) * nrm S g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hρ (div_nonneg zero_le_two hc.le))
      (mul_nonneg (Nat.cast_nonneg _) hnf)) hng
  linarith [h, t1, t2]

#print axioms cov_bound_exp

end Cluster

/-! ## 5. At the periodic Wilson state -/

section Wilson

variable {N : ℕ}

/-- **Clustering on the periodic lattices at rate `r`.** Every gauge-invariant half-space observable
`x` has a constant `K` such that, at every `n`, for all large `j`,
`torusConn τ p hN β j x (2n) ≤ K r^{2n}`: the connected reflected pairing at lag `2n` in the periodic
Wilson state of extent `2(j + 1)`. The constant is chosen after the observable.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`; `2` is the even lag of
`ContinuumSep.gapAt_of_per_vector_form_decay`. -/
def TorusClusterAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β r : ℝ) : Prop :=
  ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ∃ K : ℝ, ∀ n : ℕ, ∀ᶠ j in Filter.atTop,
      MassGap.PeriodicReduce.torusConn τ p hN β j x (2 * n) ≤ K * r ^ (2 * n)

/-- **Clustering gives the gap at the periodic state.** At `0 ≤ r`, `TorusClusterAt τ p hN β r`
gives `TransferGap.GapAt (periodicGaugeInvData τ p hN β) r`. For `x` orthogonal to the vacuum,
`ν(θx) = 0` (`PeriodicReduce.periodic_form_vac`), the torus pairings converge to
`ν(θx · S^{2n}x) = D.form x (T^{2n} x)` along `periodicUltra hN β`
(`PeriodicReduce.tendsto_torusConn`, `PeriodicReduce.periodic_form_pow`), so the bound passes to
the limit, and `ContinuumSep.gapAt_of_per_vector_form_decay` closes it.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `r` and the
vacuum pairing; `2` is the even lag and the reflection plane's doubling. -/
theorem gapAt_of_torusClusterAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : TorusClusterAt τ p hN β r) :
    MassGap.TransferGap.GapAt (MassGap.PeriodicState.periodicGaugeInvData τ p hN β) r := by
  refine MassGap.ContinuumSep.gapAt_of_per_vector_form_decay _ hr (fun x hx => ?_)
  obtain ⟨K, hK⟩ := h (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) x.2
  refine ⟨K, fun n => ?_⟩
  have hθ : MassGap.PeriodicState.periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
      (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = 0 :=
    (MassGap.PeriodicReduce.periodic_form_vac τ p hN β x).symm.trans hx
  haveI : ((MassGap.PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (MassGap.PeriodicState.periodicUltra hN β).neBot'
  have hlim := le_of_tendsto
    (MassGap.PeriodicReduce.tendsto_torusConn τ p hN β
      (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (2 * n))
    ((hK n).filter_mono (MassGap.PeriodicState.periodicUltra_le hN β))
  rw [hθ, zero_mul, sub_zero] at hlim
  rw [MassGap.PeriodicReduce.periodic_form_pow τ p hN β x (2 * n)]
  exact hlim

#print axioms gapAt_of_torusClusterAt

/-- **Clustering gives the single-lag input at every lag.** At `0 ≤ r`,
`TorusClusterAt τ p hN β r` gives `ChessboardRead.TorusLagClear τ p hN β m r` for every `m`
(`gapAt_of_torusClusterAt`, `WeakCouplingWindow.torusLagClear_of_gapAt`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `r`. -/
theorem torusLagClear_of_torusClusterAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {r : ℝ}
    (hr : 0 ≤ r) (h : TorusClusterAt τ p hN β r) (m : ℕ) :
    MassGap.ChessboardRead.TorusLagClear τ p hN β m r :=
  MassGap.WeakCouplingWindow.torusLagClear_of_gapAt τ p hN β hr
    (gapAt_of_torusClusterAt τ p hN β hr h) m

#print axioms torusLagClear_of_torusClusterAt

/-- **A uniform heat-bath gap gives clustering.** For every family `S j` of heat-bath systems at `β`
and every `c > 0` with `GlobalGap c` at `(S j).toPatchSystem` for all large `j`: some rate
`0 < r < 1` has `TorusClusterAt τ p hN β r`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the sign of `c` and `r`; `1`
is the rate the clustering must beat. -/
def HeatBathCluster (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) : Prop :=
  ∀ (S : ∀ j : ℕ, WilsonHeatBath hN β j) (c : ℝ), 0 < c →
    (∀ᶠ j in Filter.atTop, (S j).toPatchSystem.GlobalGap c) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ TorusClusterAt τ p hN β r

/-- **`HeatBathCluster` gives `KnabeCriterion.HeatBathDecay`**, at lag `1`
(`torusLagClear_of_torusClusterAt`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and lag and the sign of `r`; `1`
is the lag chosen and the rate bound. CHOSEN: lag `1`; every lag gives the same conclusion. -/
theorem heatBathDecay_of_heatBathCluster (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (h : HeatBathCluster τ p hN β) : HeatBathDecay τ p hN β := by
  intro S c hc hG
  obtain ⟨r, hr0, hr1, hcl⟩ := h S c hc hG
  exact ⟨1, one_ne_zero, r, hr0, hr1, torusLagClear_of_torusClusterAt τ p hN β hr0.le hcl 1⟩

#print axioms heatBathDecay_of_heatBathCluster

/-- **Locality of a patch system**: every neighbour set has at most `z` links, and `hₗ`, `h_{l'}`
commute up to `B`-null vectors whenever `l' ∉ nb l`.

DERIVED: `0` is the null value. -/
def LocalCommute (S : PatchSystem) (nb : S.ι → Finset S.ι) (z : ℕ) : Prop :=
  (∀ l, (nb l).card ≤ z) ∧ ∀ l l', l' ∉ nb l → ∀ u : S.E,
    S.B (S.h l' (S.h l u) - S.h l (S.h l' u)) (S.h l' (S.h l u) - S.h l (S.h l' u)) = 0

/-- **A separated pair**: `f` is read on `A` with `|A| ≤ a`, `g` on `C` with `|C| ≤ b` (`hₗ` of each
is null off its support), and every link of `C` is at level `k` from `A` along `nb`.

DERIVED: `0` is the null value. -/
def SeparatedPair (S : PatchSystem) (nb : S.ι → Finset S.ι) (f g : S.E) (k a b : ℕ) : Prop :=
  ∃ A C : Finset S.ι, A.card ≤ a ∧ C.card ≤ b ∧
    (∀ l, l ∉ A → S.B (S.h l f) (S.h l f) = 0) ∧
    (∀ l, l ∉ C → S.B (S.h l g) (S.h l g) = 0) ∧ ∀ l ∈ C, Far nb A k l

/-- **The laziness constant** `|ι| + 1`.

DERIVED: `1` makes it exceed `|ι|`, so it is positive and at least any `c ≤ 1`. -/
def Kc (S : PatchSystem) : ℕ := Fintype.card S.ι + 1

/-- **The ergodic limit of the lazy heat bath** at `K = |ι| + 1`: `B(Tᴺf, g) → L`.

DERIVED: no numeral beyond `Kc`'s. -/
def ErgodicLimit (S : PatchSystem) (f g : S.E) (L : ℝ) : Prop :=
  Tendsto (fun M => S.B (Titer S (Kc S : ℝ) M f) g) atTop (nhds L)

/-- **Locality of one heat-bath family at neighbour bound `z`**: the body of `HeatBathLocality` for the
family `S` and the bound `z`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`; `2` is the even lag. -/
def LocalityAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (S : ∀ j : ℕ, WilsonHeatBath hN β j)
    (z : ℕ) : Prop :=
  ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ∃ a b : ℕ, ∃ M : ℝ, ∀ n : ℕ, ∀ᶠ j in Filter.atTop,
      ∃ nb : (S j).toPatchSystem.ι → Finset (S j).toPatchSystem.ι,
        LocalCommute (S j).toPatchSystem nb z ∧
        ∃ f g : (S j).toPatchSystem.E, ∃ L : ℝ,
          SeparatedPair (S j).toPatchSystem nb f g n a b ∧
          (S j).toPatchSystem.B f f ≤ M ∧ (S j).toPatchSystem.B g g ≤ M ∧
          ErgodicLimit (S j).toPatchSystem f g L ∧
          MassGap.PeriodicReduce.torusConn τ p hN β j x (2 * n)
            = (S j).toPatchSystem.B f g - L

/-- **The clustering rate** at neighbour bound `z` and heat-bath gap `c`:
`√max(e/3, e^{−min(c, 1)/(2(6z + 1))})`.

DERIVED: `1` caps `c`, is the exponent of `e` and the `+ 1` of the sweep length; `2` is `gapRate`'s,
in `e^{−cs/2}`; the square root takes the even lag `2n` to the rate; `6 = 2y`. CHOSEN: `3` is the
sweep parameter `y`, the least integer above `e`, so that `e/3 < 1`; `6z + 1 = 2zy + 1` levels per
sweep. -/
def clusterRate (z : ℕ) (c : ℝ) : ℝ :=
  Real.sqrt (max (Real.exp 1 / 3) (Real.exp (-(min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ))))))

/-- **THE WILSON INSTANTIATION.** For every family `S j` of heat-bath systems at `β`: a neighbour
bound `z`, and for every gauge-invariant half-space observable `x` support bounds `a`, `b` and a
norm bound `M`, such that at every `n`, for all large `j`, some neighbour map `nb` has
`LocalCommute _ nb z`, and some `f`, `g` in the periodic gauge-invariant observables and `L` have:
`SeparatedPair _ nb f g n a b`, `B(f, f) ≤ M`, `B(g, g) ≤ M`, `ErgodicLimit _ f g L`, and
`torusConn τ p hN β j x (2n) = B(f, g) − L`. The intended witness: `nb l` the links sharing a
plaquette with `l`, `f = θx`, `g = S^{2n}x`, `L = μⱼ(θx)·μⱼ(S^{2n}x)` (module docstring).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`; `2` is the even lag. -/
def HeatBathLocality (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) : Prop :=
  ∀ S : ∀ j : ℕ, WilsonHeatBath hN β j, ∃ z : ℕ, LocalityAt τ p hN β S z

/-- **Locality and a uniform heat-bath gap give clustering at an explicit rate.** For a family `S`
with `LocalityAt τ p hN β S z` and `GlobalGap c` for all large `j`, `c > 0`: `TorusClusterAt` at
`clusterRate z c ∈ (0, 1)`. At `c' = min c 1` (`PatchSystem.globalGap_mono`), `K = |ι| + 1`
(`H_form_le_card`), `y = 3`, and `s = ⌊n/(6z + 1)⌋` lazy sweeps, `cov_bound_exp` bounds the lag-`2n`
pairing by `max(M, 0) (b + (2/c') e^{c'/2} a) r₀ⁿ`, `r₀ = max(e/3, e^{−c'/(2(6z+1))}) < 1`, since
`s e^{6zs} ≤ eⁿ` and `e^{−c's/2} ≤ e^{c'/2} (e^{−c'/(2(6z+1))})ⁿ`. The rate is `r = √r₀`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the sign of `c`; `1` caps
`c'`; `2` is the even lag and `gapRate`'s, in `2/c'` and `c'/2`; `6 = 2y`. CHOSEN: `y = 3`, the least
integer above `e`, so that `e/3 < 1` (`Real.exp_one_lt_d9`); `6z + 1 = 2zy + 1` levels per sweep, so
that `e^{2zys} s ≤ eⁿ`. -/
theorem torusClusterAt_of_localityAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    {S : ∀ j : ℕ, WilsonHeatBath hN β j} {z : ℕ} (hz : LocalityAt τ p hN β S z) {c : ℝ}
    (hc : 0 < c) (hG : ∀ᶠ j in Filter.atTop, (S j).toPatchSystem.GlobalGap c) :
    0 < clusterRate z c ∧ clusterRate z c < 1 ∧ TorusClusterAt τ p hN β (clusterRate z c) := by
  have hc'0 : 0 < min c 1 := lt_min hc one_pos
  have hc'1 : min c 1 ≤ 1 := min_le_right c 1
  have h2c : 0 ≤ 2 / min c 1 := div_nonneg zero_le_two hc'0.le
  have hG' : ∀ᶠ j in atTop, (S j).toPatchSystem.GlobalGap (min c 1) :=
    hG.mono (fun j hj => (S j).toPatchSystem.globalGap_mono (min_le_left c 1) hj)
  have hD : (0 : ℝ) < ((6 * z + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hDval : ((6 * z + 1 : ℕ) : ℝ) = 6 * (z : ℝ) + 1 := by norm_num
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = max (Real.exp 1 / 3)
      (Real.exp (-(min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ))))) := ⟨_, rfl⟩
  have hr0a : Real.exp 1 / 3 ≤ r0 := by rw [hr0]; exact le_max_left _ _
  have hr0b : Real.exp (-(min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ)))) ≤ r0 := by
    rw [hr0]; exact le_max_right _ _
  have hr0pos : 0 < r0 := lt_of_lt_of_le (by positivity) hr0a
  have hr0lt : r0 < 1 := by
    rw [hr0]
    refine max_lt ?_ ?_
    · have := Real.exp_one_lt_d9
      linarith
    · have hpos : 0 < min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ)) := div_pos hc'0 (mul_pos two_pos hD)
      calc Real.exp (-(min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ)))) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
  have hrate : clusterRate z c = Real.sqrt r0 := by rw [hr0]; rfl
  rw [hrate]
  refine ⟨Real.sqrt_pos.mpr hr0pos, ?_, ?_⟩
  · calc Real.sqrt r0 < Real.sqrt 1 := Real.sqrt_lt_sqrt hr0pos.le hr0lt
      _ = 1 := Real.sqrt_one
  intro x hx
  obtain ⟨a, b, M, hx'⟩ := hz x hx
  refine ⟨max M 0 * (b + 2 / min c 1 * Real.exp (min c 1 / 2) * a), fun n => ?_⟩
  filter_upwards [hx' n, hG'] with j hj hgj
  obtain ⟨nb, ⟨hzb, hcomm⟩, f, g, L, ⟨A, C, hA, hC, hf, hg, hfar⟩, hff, hgg, herg, hconn⟩ := hj
  rw [hconn]
  -- the patch system and its laziness constant
  have hKn : 0 < Kc (S j).toPatchSystem := by unfold Kc; omega
  have hKc : ((Kc (S j).toPatchSystem : ℕ) : ℝ)
      = (Fintype.card (S j).toPatchSystem.ι : ℝ) + 1 := by
    unfold Kc
    exact Nat.cast_succ _
  have hK : ∀ v : (S j).toPatchSystem.E,
      (S j).toPatchSystem.B ((S j).toPatchSystem.H v) ((S j).toPatchSystem.H v)
        ≤ ((Kc (S j).toPatchSystem : ℕ) : ℝ)
          * (S j).toPatchSystem.B ((S j).toPatchSystem.H v) v := by
    intro v
    rw [hKc]
    have h1 := H_form_le_card (S j).toPatchSystem v
    have h2 := (S j).toPatchSystem.H_form_nonneg v
    nlinarith
  have hcK : min c 1 ≤ ((Kc (S j).toPatchSystem : ℕ) : ℝ) := by
    rw [hKc]
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card (S j).toPatchSystem.ι)
    linarith
  -- the number of sweeps
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = n / (6 * z + 1) := ⟨_, rfl⟩
  have hdm : ((6 * z + 1 : ℕ) : ℝ) * s + ((n % (6 * z + 1) : ℕ) : ℝ) = n := by
    rw [hs]
    exact_mod_cast Nat.div_add_mod n (6 * z + 1)
  have hml : ((n % (6 * z + 1) : ℕ) : ℝ) < ((6 * z + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mod_lt n (by omega : 6 * z + 1 > 0)
  have hm0 : (0 : ℝ) ≤ ((n % (6 * z + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsD : ((6 * z + 1 : ℕ) : ℝ) * s ≤ n := by linarith
  have hnD : (n : ℝ) ≤ ((6 * z + 1 : ℕ) : ℝ) * s + ((6 * z + 1 : ℕ) : ℝ) := by linarith
  -- the abstract bound
  have hbound := cov_bound_exp (S j).toPatchSystem hKn hK hc'0 hcK hgj nb hzb hcomm (y := 3)
    (by norm_num) A C f g hf hg n hfar herg s
  -- the near factor
  have i1 : (s : ℝ) * Real.exp (2 * z * 3 * s) ≤ Real.exp n := by
    calc (s : ℝ) * Real.exp (2 * z * 3 * s) ≤ Real.exp s * Real.exp (2 * z * 3 * s) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (s : ℝ)])
            (Real.exp_pos _).le
      _ = Real.exp (((6 * z + 1 : ℕ) : ℝ) * s) := by
          rw [← Real.exp_add, hDval]
          congr 1
          ring
      _ ≤ Real.exp n := Real.exp_le_exp.mpr hsD
  have p1 : (s : ℝ) * Real.exp (2 * z * 3 * s) * (3 : ℝ)⁻¹ ^ n ≤ r0 ^ n := by
    calc (s : ℝ) * Real.exp (2 * z * 3 * s) * (3 : ℝ)⁻¹ ^ n ≤ Real.exp n * (3 : ℝ)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right i1 (pow_nonneg (by norm_num) n)
      _ = (Real.exp 1 / 3) ^ n := by
          rw [div_eq_mul_inv, mul_pow, ← Real.exp_nat_mul, mul_one]
      _ ≤ r0 ^ n := pow_le_pow_left₀ (by positivity) hr0a n
  -- the far factor
  have i2 : Real.exp (-(min c 1 * s / 2))
      ≤ Real.exp (min c 1 / 2)
        * Real.exp (-(min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ)))) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hDD : ((6 * z + 1 : ℕ) : ℝ) * ((6 * z + 1 : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hD.ne'
    have hm := mul_le_mul_of_nonneg_right hnD
      (le_of_lt (div_pos hc'0 (mul_pos two_pos hD)))
    have he : (((6 * z + 1 : ℕ) : ℝ) * s + ((6 * z + 1 : ℕ) : ℝ))
          * (min c 1 / (2 * ((6 * z + 1 : ℕ) : ℝ)))
        = min c 1 * s / 2 + min c 1 / 2 := by
      linear_combination (min c 1 * s / 2 + min c 1 / 2) * hDD
    linarith
  have p2 : Real.exp (-(min c 1 * s / 2)) ≤ Real.exp (min c 1 / 2) * r0 ^ n :=
    i2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hr0b n)
      (Real.exp_pos _).le)
  -- the norms
  have hnf := nrm_nonneg (S j).toPatchSystem f
  have hng := nrm_nonneg (S j).toPatchSystem g
  have hnfM : nrm (S j).toPatchSystem f ≤ Real.sqrt (max M 0) :=
    Real.sqrt_le_sqrt (hff.trans (le_max_left M 0))
  have hngM : nrm (S j).toPatchSystem g ≤ Real.sqrt (max M 0) :=
    Real.sqrt_le_sqrt (hgg.trans (le_max_left M 0))
  have hu : nrm (S j).toPatchSystem f * nrm (S j).toPatchSystem g ≤ max M 0 := by
    calc nrm (S j).toPatchSystem f * nrm (S j).toPatchSystem g
        ≤ Real.sqrt (max M 0) * Real.sqrt (max M 0) :=
          mul_le_mul hnfM hngM hng (Real.sqrt_nonneg _)
      _ = max M 0 := Real.mul_self_sqrt (le_max_right M 0)
  have hcb : (C.card : ℝ) ≤ b := by exact_mod_cast hC
  have hca : (A.card : ℝ) ≤ a := by exact_mod_cast hA
  have huv : 0 ≤ nrm (S j).toPatchSystem f * nrm (S j).toPatchSystem g := mul_nonneg hnf hng
  have T1le : (s : ℝ) * C.card * (nrm (S j).toPatchSystem f
        * ((3 : ℝ)⁻¹ ^ n * Real.exp (2 * z * 3 * s))) * nrm (S j).toPatchSystem g
      ≤ r0 ^ n * (b * max M 0) := by
    calc (s : ℝ) * C.card * (nrm (S j).toPatchSystem f
          * ((3 : ℝ)⁻¹ ^ n * Real.exp (2 * z * 3 * s))) * nrm (S j).toPatchSystem g
        = ((s : ℝ) * Real.exp (2 * z * 3 * s) * (3 : ℝ)⁻¹ ^ n)
          * (C.card * (nrm (S j).toPatchSystem f * nrm (S j).toPatchSystem g)) := by ring
      _ ≤ r0 ^ n * (b * max M 0) :=
          mul_le_mul p1 (mul_le_mul hcb hu huv (Nat.cast_nonneg b))
            (mul_nonneg (Nat.cast_nonneg _) huv) (pow_nonneg hr0pos.le n)
  have T2le : 2 / min c 1 * Real.exp (-(min c 1 * s / 2))
        * (A.card * nrm (S j).toPatchSystem f) * nrm (S j).toPatchSystem g
      ≤ 2 / min c 1 * (Real.exp (min c 1 / 2) * r0 ^ n) * (a * max M 0) := by
    calc 2 / min c 1 * Real.exp (-(min c 1 * s / 2))
          * (A.card * nrm (S j).toPatchSystem f) * nrm (S j).toPatchSystem g
        = 2 / min c 1 * Real.exp (-(min c 1 * s / 2))
          * (A.card * (nrm (S j).toPatchSystem f * nrm (S j).toPatchSystem g)) := by ring
      _ ≤ 2 / min c 1 * (Real.exp (min c 1 / 2) * r0 ^ n) * (a * max M 0) :=
          mul_le_mul (mul_le_mul_of_nonneg_left p2 h2c)
            (mul_le_mul hca hu huv (Nat.cast_nonneg a))
            (mul_nonneg (Nat.cast_nonneg _) huv)
            (mul_nonneg h2c (mul_nonneg (Real.exp_pos _).le (pow_nonneg hr0pos.le n)))
  have hfinal : r0 ^ n * (b * max M 0)
        + 2 / min c 1 * (Real.exp (min c 1 / 2) * r0 ^ n) * (a * max M 0)
      = max M 0 * (b + 2 / min c 1 * Real.exp (min c 1 / 2) * a) * Real.sqrt r0 ^ (2 * n) := by
    rw [pow_mul, Real.sq_sqrt hr0pos.le]
    ring
  linarith [le_abs_self ((S j).toPatchSystem.B f g - L), hbound, T1le, T2le, hfinal]

#print axioms torusClusterAt_of_localityAt

/-- **Locality and a uniform heat-bath gap give clustering.** `HeatBathLocality τ p hN β` gives
`HeatBathCluster τ p hN β`, at the rate `clusterRate z c` (`torusClusterAt_of_localityAt`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem heatBathCluster_of_locality (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (hloc : HeatBathLocality τ p hN β) : HeatBathCluster τ p hN β := by
  intro S c hc hG
  obtain ⟨z, hz⟩ := hloc S
  exact ⟨clusterRate z c, torusClusterAt_of_localityAt τ p hN β hz hc hG⟩

#print axioms heatBathCluster_of_locality

/-- **`HeatBathLocality` gives `KnabeCriterion.HeatBathDecay`** (`heatBathCluster_of_locality`,
`heatBathDecay_of_heatBathCluster`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem heatBathDecay_of_locality (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (hloc : HeatBathLocality τ p hN β) : HeatBathDecay τ p hN β :=
  heatBathDecay_of_heatBathCluster τ p hN β (heatBathCluster_of_locality τ p hN β hloc)

#print axioms heatBathDecay_of_locality

end Wilson

end MassGap.HeatBathGapDecay
