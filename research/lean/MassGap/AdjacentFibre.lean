import Mathlib
import MassGap.WeightedHeatBath
import MassGap.PairWeight
import MassGap.PairFibreDens

noncomputable section

/-!
# MassGap.AdjacentFibre — the adjacent-coupled pair weight is a tilted bilinear exponential times a small factor

## What it gives

On the periodic lattice, at a frozen configuration and a link pair `l ≠ m`, every plaquette density
is affine in the two free features: `d(p) = c_p − φ_p(X h, X g)` with
`φ_p(x, y) = ⟪x, T_p y⟫ + ⟪w_p, x⟫ + ⟪v_p, y⟫`, at most one of `T_p, w_p, v_p` nonzero and of norm at
most `1` (`dens_form`). The product of two densities is then a constant, an affine part, and
`φ_p φ_q`. When `p` and `q` do not both visit `l` and do not both visit `m`, `φ_p φ_q` is itself a
bilinear pairing `⟪x, S y⟫` (`phi_mul_of_sep`), so it joins the tilted family of
`PairFibreAbstract.fibreBound_of_tiltBounds`. Only the pairs sharing a free link leave the family, and
each contributes at most `|λ|` (`abs_phi_le`).

`wtAdj_fibre_eq` assembles this for `wtAdj = wt · e^{−λ Σ_{adjSet} d d'}`: a tilted bilinear
exponential with `‖T‖ ≤ β n2 + |λ|(192 n2 + 96(12 − n2))`, `‖α‖, ‖γ‖ ≤ (β + 192|λ|)(12 − n2)`, times
`e^V` with `|V| ≤ 288 |λ|` (`card_share_le`). `torus_fibreHyp_adj_sharp` turns a `FibreBound` on that
family into the fibre hypothesis at `e^ε (c + 2(e^ε − 1))`, `ε = 288|λ|`. On the box
`0 ≤ β ≤ 1/200`, `|λ| ≤ 1/20000` the `SU(2)` constants are `503/10000` (single pair) and `557/10000`
(double pair) (`fibreHyp_adj_single`, `fibreHyp_adj_double`), so `max(18 δ₁, 12 δ₁ + 3 δ₂) ≤ 0.9054`
over the pairs through a common plaquette. A pair through no common plaquette is coupled only through
adjacent plaquettes; there `V` splits into single-link parts that do not couple it, and the additive
cost `torus_fibreHyp_adj_sharp` charges is not the right bound for it.

Normalisation: `wt` sums over ordered plaquettes (`β = β_std/2`), and `adjSet` over ordered pairs of
distinct ordered plaquettes sharing a link. Each geometric adjacent pair appears `8` times, so a
coupling `λ_std q q'` per geometric pair (`q = 1 − d`) is `λ = −λ_std/8` here. The two orientations of
one plaquette also share its links, so the weight carries `2λ d(P)²` per geometric plaquette as well.

## The route

`PairWeight.reTr_hol_single`, `PairWeight.reTr_hol_pair` give the affine forms of the plaquettes
visiting the pair; `PairCount.wilsonHol_diag` sends a diagonal plaquette to density `0`;
`WeightedHeatBath.dens_update_of_not_mem` freezes the rest.
-/

namespace MassGap.AdjacentFibre

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.HeatBath (bdT)
open MassGap.WilsonLattice (wilsonHol)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two wilsonDensity_one)
open MassGap.PairInterface (FE realFeature)
open MassGap.PairCount (wilsonHol_diag)
open MassGap.WeightedHeatBath (dens dens_update_of_not_mem)

/-! ## 1. The algebra of two affine forms -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The free part of a plaquette density on the pair fibre: `⟪x, T y⟫ + ⟪w, x⟫ + ⟪v, y⟫`. -/
def phi (T : E →L[ℝ] E) (w v : E) (x y : E) : ℝ :=
  inner ℝ x (T y) + inner ℝ w x + inner ℝ v y

/-- The cross pairing `y ↦ ⟪v', y⟫ w + ⟪v, y⟫ w'`. -/
def cross (w v w' v' : E) : E →L[ℝ] E :=
  (innerSL ℝ v').smulRight w + (innerSL ℝ v).smulRight w'

/-- The cross pairing as a sum of products.

DERIVED: no numeral. -/
theorem inner_cross (w v w' v' x y : E) :
    inner ℝ x (cross w v w' v' y) = inner ℝ w x * inner ℝ v' y + inner ℝ v y * inner ℝ w' x := by
  simp only [cross, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_add_right, real_inner_smul_right, real_inner_comm x w,
    real_inner_comm x w']
  ring

#print axioms inner_cross

/-- The norm of the cross pairing.

DERIVED: no numeral. -/
theorem norm_cross_le (w v w' v' : E) : ‖cross w v w' v'‖ ≤ ‖v'‖ * ‖w‖ + ‖v‖ * ‖w'‖ := by
  unfold cross
  refine (norm_add_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, innerSL_apply_norm]

#print axioms norm_cross_le

/-- Two free parts are separable when one vanishes, or neither has a pairing and they share no
feature.

DERIVED: no numeral. -/
def Sep (T : E →L[ℝ] E) (w v : E) (T' : E →L[ℝ] E) (w' v' : E) : Prop :=
  (T = 0 ∧ w = 0 ∧ v = 0) ∨ (T' = 0 ∧ w' = 0 ∧ v' = 0) ∨
    (T = 0 ∧ T' = 0 ∧ (w = 0 ∨ w' = 0) ∧ (v = 0 ∨ v' = 0))

/-- **A separable product is a bilinear pairing.**

DERIVED: no numeral. -/
theorem phi_mul_of_sep {T : E →L[ℝ] E} {w v : E} {T' : E →L[ℝ] E} {w' v' : E}
    (hs : Sep T w v T' w' v') (x y : E) :
    phi T w v x y * phi T' w' v' x y = inner ℝ x (cross w v w' v' y) := by
  rw [inner_cross]
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hw, hv⟩
  · simp [phi]
  · simp [phi]
  · rcases hw with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [phi] <;> ring

#print axioms phi_mul_of_sep

/-- **The product of two affine densities**: the constant, the affine part (a free part with
coefficients `c T' + c' T`, `c w' + c' w`, `c v' + c' v`) and the product of the free parts.

DERIVED: no numeral. -/
theorem affine_mul (c c' : ℝ) (T : E →L[ℝ] E) (w v : E) (T' : E →L[ℝ] E) (w' v' : E) (x y : E) :
    (c - phi T w v x y) * (c' - phi T' w' v' x y)
      = c * c' - phi (c • T' + c' • T) (c • w' + c' • w) (c • v' + c' • v) x y
        + phi T w v x y * phi T' w' v' x y := by
  simp only [phi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right,
    inner_add_left, real_inner_smul_right, real_inner_smul_left]
  ring

#print axioms affine_mul

/-- The free part on unit features is bounded by its three norms.

DERIVED: `1` is the feature norm bound. -/
theorem abs_phi_le (T : E →L[ℝ] E) (w v : E) {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |phi T w v x y| ≤ ‖T‖ + ‖w‖ + ‖v‖ := by
  unfold phi
  have h1 : |inner ℝ x (T y)| ≤ ‖T‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖x‖ * ‖T y‖ ≤ 1 * (‖T‖ * ‖y‖) :=
          mul_le_mul hx (T.le_opNorm y) (norm_nonneg _) zero_le_one
      _ ≤ ‖T‖ := by nlinarith [norm_nonneg T]
  have h2 : |inner ℝ w x| ≤ ‖w‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [norm_nonneg w, norm_nonneg x]
  have h3 : |inner ℝ v y| ≤ ‖v‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [norm_nonneg v, norm_nonneg y]
  calc _ ≤ |inner ℝ x (T y) + inner ℝ w x| + |inner ℝ v y| := abs_add_le _ _
    _ ≤ |inner ℝ x (T y)| + |inner ℝ w x| + |inner ℝ v y| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

#print axioms abs_phi_le

/-- The free part is additive over a finite family.

DERIVED: no numeral. -/
theorem phi_sum {ι : Type*} (s : Finset ι) (T : ι → E →L[ℝ] E) (w v : ι → E) (x y : E) :
    phi (∑ i ∈ s, T i) (∑ i ∈ s, w i) (∑ i ∈ s, v i) x y = ∑ i ∈ s, phi (T i) (w i) (v i) x y := by
  simp only [phi, ContinuousLinearMap.sum_apply, inner_sum, sum_inner, Finset.sum_add_distrib]

#print axioms phi_sum

/-- The free part is additive in the pairing.

DERIVED: no numeral. -/
theorem phi_sub_op (A S : E →L[ℝ] E) (a b x y : E) :
    phi (A - S) a b x y = phi A a b x y - inner ℝ x (S y) := by
  simp only [phi, ContinuousLinearMap.sub_apply, inner_sub_right]
  ring

#print axioms phi_sub_op

/-- The free part scales.

DERIVED: no numeral. -/
theorem phi_smul (r : ℝ) (A : E →L[ℝ] E) (a b x y : E) :
    r * phi A a b x y = phi (r • A) (r • a) (r • b) x y := by
  simp only [phi, ContinuousLinearMap.smul_apply, real_inner_smul_right, real_inner_smul_left]
  ring

#print axioms phi_smul

section Pairs

variable {ι : Type*} (c : ι → ℝ) (T : ι → E →L[ℝ] E) (w v : ι → E)

open Classical in
/-- The pairing coefficient of one ordered pair: the affine pairings and, when separable, the
product's cross pairing. -/
def pairOp (pq : ι × ι) : E →L[ℝ] E :=
  c pq.1 • T pq.2 + c pq.2 • T pq.1
    - (if Sep (T pq.1) (w pq.1) (v pq.1) (T pq.2) (w pq.2) (v pq.2)
        then cross (w pq.1) (v pq.1) (w pq.2) (v pq.2) else 0)

/-- The `x`-tilt of one ordered pair. -/
def pairA (pq : ι × ι) : E := c pq.1 • w pq.2 + c pq.2 • w pq.1

/-- The `y`-tilt of one ordered pair. -/
def pairB (pq : ι × ι) : E := c pq.1 • v pq.2 + c pq.2 • v pq.1

open Classical in
/-- The remainder of one ordered pair: the product of the free parts when not separable. -/
def pairR (pq : ι × ι) (x y : E) : ℝ :=
  if Sep (T pq.1) (w pq.1) (v pq.1) (T pq.2) (w pq.2) (v pq.2)
    then 0 else phi (T pq.1) (w pq.1) (v pq.1) x y * phi (T pq.2) (w pq.2) (v pq.2) x y

/-- **The product of two affine densities in the family form**: constant, free part of the pair's
coefficients, remainder.

DERIVED: no numeral. -/
theorem pair_mul (pq : ι × ι) (x y : E) :
    (c pq.1 - phi (T pq.1) (w pq.1) (v pq.1) x y) * (c pq.2 - phi (T pq.2) (w pq.2) (v pq.2) x y)
      = c pq.1 * c pq.2 - phi (pairOp c T w v pq) (pairA c w pq) (pairB c v pq) x y
        + pairR T w v pq x y := by
  rw [affine_mul]
  unfold pairOp pairA pairB pairR
  split_ifs with hs
  · rw [phi_sub_op, phi_mul_of_sep hs]
    ring
  · rw [sub_zero]

#print axioms pair_mul

/-- **The adjacent sum in the family form.**

DERIVED: no numeral. -/
theorem sum_pair_mul (s : Finset (ι × ι)) (x y : E) :
    ∑ pq ∈ s, (c pq.1 - phi (T pq.1) (w pq.1) (v pq.1) x y)
        * (c pq.2 - phi (T pq.2) (w pq.2) (v pq.2) x y)
      = ∑ pq ∈ s, c pq.1 * c pq.2
        - phi (∑ pq ∈ s, pairOp c T w v pq) (∑ pq ∈ s, pairA c w pq) (∑ pq ∈ s, pairB c v pq) x y
        + ∑ pq ∈ s, pairR T w v pq x y := by
  rw [phi_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun pq _ => pair_mul c T w v pq x y

#print axioms sum_pair_mul

open Classical in
/-- The pairing coefficient of one ordered pair is bounded by the affine and cross terms.

DERIVED: `0` is the sign of the constants. -/
theorem norm_pairOp_le (hc : ∀ i, 0 ≤ c i) (pq : ι × ι) :
    ‖pairOp c T w v pq‖ ≤ (c pq.1 * ‖T pq.2‖ + ‖v pq.2‖ * ‖w pq.1‖)
      + (c pq.2 * ‖T pq.1‖ + ‖v pq.1‖ * ‖w pq.2‖) := by
  unfold pairOp
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖c pq.1 • T pq.2 + c pq.2 • T pq.1‖ ≤ c pq.1 * ‖T pq.2‖ + c pq.2 * ‖T pq.1‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (hc _), Real.norm_of_nonneg (hc _)]
  have h2 : ‖(if Sep (T pq.1) (w pq.1) (v pq.1) (T pq.2) (w pq.2) (v pq.2)
      then cross (w pq.1) (v pq.1) (w pq.2) (v pq.2) else 0)‖
        ≤ ‖v pq.2‖ * ‖w pq.1‖ + ‖v pq.1‖ * ‖w pq.2‖ := by
    split_ifs
    · exact norm_cross_le _ _ _ _
    · rw [norm_zero]
      positivity
  linarith

#print axioms norm_pairOp_le

/-- The `x`-tilt of one ordered pair.

DERIVED: `0` is the sign of the constants. -/
theorem norm_pairA_le (hc : ∀ i, 0 ≤ c i) (pq : ι × ι) :
    ‖pairA c w pq‖ ≤ c pq.1 * ‖w pq.2‖ + c pq.2 * ‖w pq.1‖ := by
  unfold pairA
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (hc _), Real.norm_of_nonneg (hc _)]

#print axioms norm_pairA_le

/-- The `y`-tilt of one ordered pair.

DERIVED: `0` is the sign of the constants. -/
theorem norm_pairB_le (hc : ∀ i, 0 ≤ c i) (pq : ι × ι) :
    ‖pairB c v pq‖ ≤ c pq.1 * ‖v pq.2‖ + c pq.2 * ‖v pq.1‖ := by
  unfold pairB
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (hc _), Real.norm_of_nonneg (hc _)]

#print axioms norm_pairB_le

open Classical in
/-- The remainder of one ordered pair on unit features.

DERIVED: `1` is the feature norm bound; `0` is the separable value. -/
theorem abs_pairR_le (pq : ι × ι) {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |pairR T w v pq x y|
      ≤ if Sep (T pq.1) (w pq.1) (v pq.1) (T pq.2) (w pq.2) (v pq.2) then 0
        else (‖T pq.1‖ + ‖w pq.1‖ + ‖v pq.1‖) * (‖T pq.2‖ + ‖w pq.2‖ + ‖v pq.2‖) := by
  unfold pairR
  split_ifs
  · simp
  · rw [abs_mul]
    exact mul_le_mul (abs_phi_le _ _ _ hx hy) (abs_phi_le _ _ _ hx hy) (abs_nonneg _)
      (by positivity)

#print axioms abs_pairR_le

/-- The remainder is continuous in the two features.

DERIVED: no numeral. -/
theorem continuous_pairR {Ω : Type*} [TopologicalSpace Ω] {X : Ω → E} (hX : Continuous X)
    (pq : ι × ι) : Continuous fun z : Ω × Ω => pairR T w v pq (X z.1) (X z.2) := by
  have hphi : ∀ i, Continuous fun z : Ω × Ω => phi (T i) (w i) (v i) (X z.1) (X z.2) := fun i => by
    unfold phi
    exact (((hX.comp continuous_fst).inner ((T i).continuous.comp (hX.comp continuous_snd))).add
      (continuous_const.inner (hX.comp continuous_fst))).add
      (continuous_const.inner (hX.comp continuous_snd))
  unfold pairR
  split_ifs
  · exact continuous_const
  · exact (hphi pq.1).mul (hphi pq.2)

#print axioms continuous_pairR

open Classical in
/-- The remainder of a pair whose free parts read `y` only (no pairing, no `x`-functional). -/
def pairRg (pq : ι × ι) (x y : E) : ℝ :=
  if T pq.1 = 0 ∧ T pq.2 = 0 ∧ w pq.1 = 0 ∧ w pq.2 = 0 then pairR T w v pq x y else 0

open Classical in
/-- The remainder of a pair whose free parts read `x` only. -/
def pairRh (pq : ι × ι) (x y : E) : ℝ :=
  if T pq.1 = 0 ∧ T pq.2 = 0 ∧ v pq.1 = 0 ∧ v pq.2 = 0 then pairR T w v pq x y else 0

/-- The mixed remainder: what `pairRg` and `pairRh` leave of `pairR`. -/
def pairRm (pq : ι × ι) (x y : E) : ℝ :=
  pairR T w v pq x y - pairRg T w v pq x y - pairRh T w v pq x y

/-- `pairRg` does not read `x`.

DERIVED: no numeral. -/
theorem pairRg_left (pq : ι × ι) (x x' y : E) : pairRg T w v pq x y = pairRg T w v pq x' y := by
  by_cases hc : T pq.1 = 0 ∧ T pq.2 = 0 ∧ w pq.1 = 0 ∧ w pq.2 = 0
  · obtain ⟨h1, h2, h3, h4⟩ := hc
    simp [pairRg, pairR, phi, h1, h2, h3, h4]
  · rw [pairRg, pairRg, if_neg hc, if_neg hc]

#print axioms pairRg_left

/-- `pairRh` does not read `y`.

DERIVED: no numeral. -/
theorem pairRh_right (pq : ι × ι) (x y y' : E) : pairRh T w v pq x y = pairRh T w v pq x y' := by
  by_cases hc : T pq.1 = 0 ∧ T pq.2 = 0 ∧ v pq.1 = 0 ∧ v pq.2 = 0
  · obtain ⟨h1, h2, h3, h4⟩ := hc
    simp [pairRh, pairR, phi, h1, h2, h3, h4]
  · rw [pairRh, pairRh, if_neg hc, if_neg hc]

#print axioms pairRh_right

/-- The split pieces are continuous in the features.

DERIVED: no numeral. -/
theorem continuous_pairRg {Ω : Type*} [TopologicalSpace Ω] {X : Ω → E} (hX : Continuous X)
    (pq : ι × ι) : Continuous fun z : Ω × Ω => pairRg T w v pq (X z.1) (X z.2) := by
  unfold pairRg
  split_ifs
  · exact continuous_pairR T w v hX pq
  · exact continuous_const

#print axioms continuous_pairRg

/-- DERIVED: no numeral. -/
theorem continuous_pairRh {Ω : Type*} [TopologicalSpace Ω] {X : Ω → E} (hX : Continuous X)
    (pq : ι × ι) : Continuous fun z : Ω × Ω => pairRh T w v pq (X z.1) (X z.2) := by
  unfold pairRh
  split_ifs
  · exact continuous_pairR T w v hX pq
  · exact continuous_const

#print axioms continuous_pairRh

/-- DERIVED: no numeral. -/
theorem continuous_pairRm {Ω : Type*} [TopologicalSpace Ω] {X : Ω → E} (hX : Continuous X)
    (pq : ι × ι) : Continuous fun z : Ω × Ω => pairRm T w v pq (X z.1) (X z.2) :=
  ((continuous_pairR T w v hX pq).sub (continuous_pairRg T w v hX pq)).sub
    (continuous_pairRh T w v hX pq)

#print axioms continuous_pairRm

end Pairs

end Algebra

/-! ## 2. The affine form of every plaquette density -/

section Torus

variable {N : ℕ}

/-- The plaquette visits the link (non-diagonal). -/
def Vis {M : ℕ} (p : WilsonHypercubic.Plaq 4 (M + 1)) (k : WilsonHypercubic.Link 4 (M + 1)) : Prop :=
  p.1.1 ≠ p.1.2 ∧ k ∈ (bdT M p).map Prod.fst

instance {M : ℕ} (p : WilsonHypercubic.Plaq 4 (M + 1)) (k : WilsonHypercubic.Link 4 (M + 1)) :
    Decidable (Vis p k) :=
  instDecidableAnd

/-- **Every plaquette density is affine on the pair fibre**: `d(p) = c − φ(X h, X g)` with
`0 ≤ c ≤ 2`, `c = 0` on a diagonal plaquette, and the pairing `T`, the `m`-functional `w`, the
`l`-functional `v` of norm at most `1` and zero off the plaquettes visiting both, `m` only, `l` only.

DERIVED: `4` is the spacetime dimension; `1` is the least `M`, the successor writing the extent and
the norm bound; `0`, `2` are the density range; `1`, `2` in `p.1.1`, `p.1.2` are projections. -/
theorem dens_form (hN : N ≠ 0) {M : ℕ} (hM : 1 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (p : WilsonHypercubic.Plaq 4 (M + 1)) :
    ∃ (c : ℝ) (T : FE N →L[ℝ] FE N) (w v : FE N),
      (0 ≤ c ∧ c ≤ 2 ∧ (p.1.1 = p.1.2 → c = 0)) ∧
      (‖T‖ ≤ 1 ∧ (¬ (Vis p l ∧ Vis p m) → T = 0)) ∧
      (‖w‖ ≤ 1 ∧ (¬ (Vis p m ∧ ¬ Vis p l) → w = 0)) ∧
      (‖v‖ ≤ 1 ∧ (¬ (Vis p l ∧ ¬ Vis p m) → v = 0)) ∧
      ∀ h g : SU N, dens (bdT M) p (Function.update (Function.update W m h) l g)
        = c - phi T w v (realFeature N h) (realFeature N g) := by
  have hwd : ∀ U : SU N,
      wilsonDensity U = 1 - (Matrix.trace (U : Matrix (Fin N) (Fin N) ℂ)).re / (N : ℝ) := by
    intro U
    unfold wilsonDensity
    ring
  by_cases hd : p.1.1 = p.1.2
  · -- a diagonal plaquette: density `0` everywhere
    have hnv : ∀ k, ¬ Vis p k := fun k hk => hk.1 hd
    refine ⟨0, 0, 0, 0, ⟨le_rfl, by norm_num, fun _ => rfl⟩, ⟨by simp, fun _ => rfl⟩,
      ⟨by simp, fun _ => rfl⟩, ⟨by simp, fun _ => rfl⟩, fun h g => ?_⟩
    unfold dens
    rw [wilsonHol_diag M p hd, wilsonDensity_one hN]
    simp [phi]
  by_cases hl : l ∈ (bdT M p).map Prod.fst <;> by_cases hm : m ∈ (bdT M p).map Prod.fst
  · -- visits both: a pairing
    obtain ⟨T, hT1, hT⟩ := MassGap.PairWeight.reTr_hol_pair hN hM p hd hlm hl hm W
    refine ⟨1, T, 0, 0, ⟨zero_le_one, by norm_num, fun h => absurd h hd⟩,
      ⟨hT1, fun hn => absurd ⟨⟨hd, hl⟩, ⟨hd, hm⟩⟩ hn⟩, ⟨by simp, fun _ => rfl⟩,
      ⟨by simp, fun _ => rfl⟩, fun h g => ?_⟩
    unfold dens
    rw [hwd, hT h g]
    simp [phi]
  · -- visits `l` only: a functional of `X g`
    obtain ⟨v, hv1, hv⟩ := MassGap.PairWeight.reTr_hol_single hN hM p hd hl hm W
    refine ⟨1, 0, 0, v, ⟨zero_le_one, by norm_num, fun h => absurd h hd⟩,
      ⟨by simp, fun _ => rfl⟩, ⟨by simp, fun _ => rfl⟩,
      ⟨hv1, fun hn => absurd ⟨⟨hd, hl⟩, fun h' => hm h'.2⟩ hn⟩, fun h g => ?_⟩
    unfold dens
    rw [hwd, hv h g]
    simp [phi]
  · -- visits `m` only: a functional of `X h`
    obtain ⟨w, hw1, hw⟩ :=
      MassGap.PairWeight.reTr_hol_single hN hM p hd (l := m) (m := l) hm hl W
    refine ⟨1, 0, w, 0, ⟨zero_le_one, by norm_num, fun h => absurd h hd⟩,
      ⟨by simp, fun _ => rfl⟩, ⟨hw1, fun hn => absurd ⟨⟨hd, hm⟩, fun h' => hl h'.2⟩ hn⟩,
      ⟨by simp, fun _ => rfl⟩, fun h g => ?_⟩
    unfold dens
    rw [Function.update_comm hlm.symm h g W, hwd, hw g h]
    simp [phi]
  · -- visits neither: frozen
    have hnl : ¬ Vis p l := fun h => hl h.2
    have hnm : ¬ Vis p m := fun h => hm h.2
    refine ⟨dens (bdT M) p W, 0, 0, 0,
      ⟨wilsonDensity_nonneg hN _, wilsonDensity_le_two hN _, fun h => absurd h hd⟩,
      ⟨by simp, fun _ => rfl⟩, ⟨by simp, fun _ => rfl⟩, ⟨by simp, fun _ => rfl⟩, fun h g => ?_⟩
    rw [dens_update_of_not_mem (bdT M) p hl, dens_update_of_not_mem (bdT M) p hm]
    simp [phi]

#print axioms dens_form

/-! ## 3. Counting the adjacent pairs -/

/-- A sum of an indicator is its constant times the count.

DERIVED: `0` is the off value. -/
theorem sum_ite_eq {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (K : ℝ) :
    ∑ a ∈ s, (if P a then K else 0) = K * (s.filter P).card := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

#print axioms sum_ite_eq

/-- **At most `48` non-diagonal plaquettes share a link with a given plaquette**: `4` links,
`PairCount.card_visit_nondiag_le` each.

DERIVED: `48 = 4 · 12`; `4` is the spacetime dimension and the word length; `1` is the successor
writing the extent; `12` is `card_visit_nondiag_le`'s bound. -/
theorem card_partners_le (M : ℕ) (q : WilsonHypercubic.Plaq 4 (M + 1)) :
    (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ ∃ x ∈ (bdT M p).map Prod.fst, x ∈ (bdT M q).map Prod.fst)).card ≤ 48 := by
  have hsub : Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ ∃ x ∈ (bdT M p).map Prod.fst, x ∈ (bdT M q).map Prod.fst)
      ⊆ ((bdT M q).map Prod.fst).toFinset.biUnion (fun x =>
          Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ x ∈ (bdT M p).map Prod.fst)) := by
    intro p hp
    obtain ⟨-, hd, x, hxp, hxq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨x, List.mem_toFinset.mpr hxq,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hxp⟩⟩
  have hlen : ((bdT M q).map Prod.fst).toFinset.card ≤ 4 := by
    refine (List.toFinset_card_le _).trans ?_
    simp [WilsonHypercubic.bd]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ ((bdT M q).map Prod.fst).toFinset,
          (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ x ∈ (bdT M p).map Prod.fst)).card := Finset.card_biUnion_le
    _ ≤ ((bdT M q).map Prod.fst).toFinset.card • 12 :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => MassGap.PairCount.card_visit_nondiag_le M x
    _ ≤ 48 := by
        rw [smul_eq_mul]
        omega

#print axioms card_partners_le

open MassGap.WeightedHeatBath (adjSet)

/-- **Adjacent pairs with a non-diagonal first plaquette and a second in `B`**: at most `48 · #B`.

DERIVED: `48` is `card_partners_le`'s bound; `4` is the spacetime dimension; `1` is the successor
writing the extent and `1`, `2` are projections. -/
theorem card_adj_left_le (M : ℕ) (B : WilsonHypercubic.Plaq 4 (M + 1) → Prop) [DecidablePred B] :
    ((adjSet (bdT M)).filter (fun pq => pq.1.1.1 ≠ pq.1.1.2 ∧ B pq.2)).card
      ≤ 48 * (Finset.univ.filter B).card := by
  have hsub : (adjSet (bdT M)).filter (fun pq => pq.1.1.1 ≠ pq.1.1.2 ∧ B pq.2)
      ⊆ (Finset.univ.filter B).biUnion (fun q =>
          (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ ∃ x ∈ (bdT M p).map Prod.fst, x ∈ (bdT M q).map Prod.fst)).image
            (fun p => (p, q))) := by
    intro pq hpq
    obtain ⟨hadj, hd, hB⟩ := Finset.mem_filter.mp hpq
    simp only [adjSet, Finset.mem_filter, Finset.mem_univ, true_and] at hadj
    obtain ⟨-, hx⟩ := hadj
    exact Finset.mem_biUnion.mpr ⟨pq.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩,
      Finset.mem_image.mpr ⟨pq.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hx⟩, rfl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Finset.univ.filter B, ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ ∃ x ∈ (bdT M p).map Prod.fst, x ∈ (bdT M q).map Prod.fst)).image
            (fun p => (p, q))).card := Finset.card_biUnion_le
    _ ≤ (Finset.univ.filter B).card • 48 :=
        Finset.sum_le_card_nsmul _ _ _ fun q _ => Finset.card_image_le.trans (card_partners_le M q)
    _ = 48 * (Finset.univ.filter B).card := by rw [smul_eq_mul, mul_comm]

#print axioms card_adj_left_le

/-- The mirror of `card_adj_left_le`: a non-diagonal second plaquette, a first in `B`.

DERIVED: as `card_adj_left_le`; `48` is `card_partners_le`'s bound. -/
theorem card_adj_right_le (M : ℕ) (B : WilsonHypercubic.Plaq 4 (M + 1) → Prop) [DecidablePred B] :
    ((adjSet (bdT M)).filter (fun pq => pq.2.1.1 ≠ pq.2.1.2 ∧ B pq.1)).card
      ≤ 48 * (Finset.univ.filter B).card := by
  have hsub : (adjSet (bdT M)).filter (fun pq => pq.2.1.1 ≠ pq.2.1.2 ∧ B pq.1)
      ⊆ (Finset.univ.filter B).biUnion (fun q =>
          (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ ∃ x ∈ (bdT M p).map Prod.fst, x ∈ (bdT M q).map Prod.fst)).image
            (fun p => (q, p))) := by
    intro pq hpq
    obtain ⟨hadj, hd, hB⟩ := Finset.mem_filter.mp hpq
    simp only [adjSet, Finset.mem_filter, Finset.mem_univ, true_and] at hadj
    obtain ⟨-, x, hx1, hx2⟩ := hadj
    exact Finset.mem_biUnion.mpr ⟨pq.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩,
      Finset.mem_image.mpr ⟨pq.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, x, hx2, hx1⟩, rfl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Finset.univ.filter B, ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ ∃ x ∈ (bdT M p).map Prod.fst, x ∈ (bdT M q).map Prod.fst)).image
            (fun p => (q, p))).card := Finset.card_biUnion_le
    _ ≤ (Finset.univ.filter B).card • 48 :=
        Finset.sum_le_card_nsmul _ _ _ fun q _ => Finset.card_image_le.trans (card_partners_le M q)
    _ = 48 * (Finset.univ.filter B).card := by rw [smul_eq_mul, mul_comm]

#print axioms card_adj_right_le

/-- **Adjacent pairs sharing a free link**: at most `288 = 2 · 12²`.

DERIVED: `288 = 12 · 12 + 12 · 12`; `12` is `card_visit_nondiag_le`'s bound; `4` is the spacetime
dimension; `1` is the successor writing the extent. -/
theorem card_share_le (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    ((adjSet (bdT M)).filter (fun pq => (Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m))).card
      ≤ 288 := by
  have hsub : (adjSet (bdT M)).filter
        (fun pq => (Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m))
      ⊆ (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)
          ×ˢ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst))
        ∪ (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst)
          ×ˢ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst)) := by
    intro pq hpq
    rcases (Finset.mem_filter.mp hpq).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩)
  have hl := MassGap.PairCount.card_visit_nondiag_le M l
  have hm := MassGap.PairCount.card_visit_nondiag_le M m
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 12 * 12 + 12 * 12 := by
        rw [Finset.card_product, Finset.card_product]
        exact Nat.add_le_add (Nat.mul_le_mul hl hl) (Nat.mul_le_mul hm hm)
    _ = 288 := by norm_num

#print axioms card_share_le

/-- The plaquettes visiting both links number `n2`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem card_both_eq (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l ∧ Vis q m)).card
      = MassGap.PairCount.n2 M l m := by
  unfold MassGap.PairCount.n2
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Vis]
  tauto

#print axioms card_both_eq

/-- The plaquettes visiting `l` and not `m` number at most `12 − n2`.

DERIVED: `12` is `card_visit_nondiag_le`'s bound; `4` is the spacetime dimension; `1` is the
successor writing the extent. -/
theorem card_only_add_le (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l ∧ ¬ Vis q m)).card
      + MassGap.PairCount.n2 M l m ≤ 12 := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst))
    (fun p : WilsonHypercubic.Plaq 4 (M + 1) => m ∈ (bdT M p).map Prod.fst)
  have e1 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).filter
        (fun p : WilsonHypercubic.Plaq 4 (M + 1) => m ∈ (bdT M p).map Prod.fst)
      = Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l ∧ Vis q m) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Vis]
    tauto
  have e2 : (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).filter
        (fun p : WilsonHypercubic.Plaq 4 (M + 1) => ¬ m ∈ (bdT M p).map Prod.fst)
      = Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l ∧ ¬ Vis q m) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Vis]
    tauto
  rw [e1, e2, card_both_eq] at h1
  have h2 := MassGap.PairCount.card_visit_nondiag_le M l
  omega

#print axioms card_only_add_le

/-! ## 4. The adjacent-coupled pair weight -/

open MassGap.WeightedHeatBath (wtAdj adjAct)
open MassGap.PairInterface (fibreWeight continuous_realFeature norm_realFeature)
open MassGap.PairCount (n2)

/-- **The adjacent-coupled weight on the pair fibre is a tilted bilinear exponential times
`e^V`, `|V| ≤ 288 |λ|`.** The tilted part has `‖T‖ ≤ β n2 + |λ| (192 n2 + 96 (12 − n2))` and
`‖α‖, ‖γ‖ ≤ (β + 192 |λ|)(12 − n2)`: the Wilson pair weight (`PairWeight.wt_fibre_eq`) with the
adjacent pairs that read at most one free link, or the two free links once each, folded in
(`dens_form`, `sum_pair_mul`); `V` collects the pairs sharing a free link (`card_share_le`).

DERIVED: `4` is the spacetime dimension; `1` is the least `M`, the successor writing the extent and
the feature norm; `0` is the excluded rank and the lower end of `β`; `12` is the non-diagonal
plaquette count per link; `288` is `card_share_le`'s bound; `192 = 2 · 2 · 48` and `96 = 2 · 48`
are the density bound `2`, the two orders of a pair and `card_partners_le`'s `48`. -/
theorem wtAdj_fibre_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) (lam : ℝ)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    ∃ (K : ℝ) (T : FE N →L[ℝ] FE N) (α γ : FE N) (V : SU N → SU N → ℝ), 0 < K ∧
      ‖T‖ ≤ β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ) + 96 * (12 - (n2 M l m : ℝ))) ∧
      ‖α‖ ≤ (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ∧
      ‖γ‖ ≤ (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ∧
      Continuous (Function.uncurry V) ∧ (∀ h g, |V h g| ≤ 288 * |lam|) ∧
      ∀ h g : SU N, wtAdj (bdT M) β lam (Function.update (Function.update W m h) l g)
        = fibreWeight (realFeature N) K T α γ h g * Real.exp (V h g) := by
  obtain ⟨K₀, T₀, α₀, γ₀, hK, hT0, hα0, hγ0, hw⟩ := MassGap.PairWeight.wt_fibre_eq hN hβ hM hlm W
  choose c Tf wf vf hc hTf hwf hvf hform using dens_form hN hM hlm W
  have hc0 : ∀ p, 0 ≤ c p := fun p => (hc p).1
  have zT : ∀ p, ¬ Vis p l ∨ ¬ Vis p m → Tf p = 0 := fun p h =>
    (hTf p).2 fun h' => h.elim (· h'.1) (· h'.2)
  have zw : ∀ p, ¬ Vis p m ∨ Vis p l → wf p = 0 := fun p h =>
    (hwf p).2 fun h' => h.elim (· h'.1) (h'.2 ·)
  have zv : ∀ p, ¬ Vis p l ∨ Vis p m → vf p = 0 := fun p h =>
    (hvf p).2 fun h' => h.elim (· h'.1) (h'.2 ·)
  have zd : ∀ p : WilsonHypercubic.Plaq 4 (M + 1), ∀ k, ¬ p.1.1 ≠ p.1.2 → ¬ Vis p k :=
    fun p k hd hv => hd hv.1
  -- each free part has total norm at most `1`
  have hone : ∀ p, ‖Tf p‖ + ‖wf p‖ + ‖vf p‖ ≤ 1 := by
    intro p
    by_cases hl : Vis p l <;> by_cases hm : Vis p m
    · rw [zw p (Or.inr hl), zv p (Or.inr hm)]
      simpa using (hTf p).1
    · rw [zT p (Or.inr hm), zw p (Or.inl hm)]
      simpa using (hvf p).1
    · rw [zT p (Or.inl hl), zv p (Or.inl hl)]
      simpa using (hwf p).1
    · rw [zT p (Or.inl hl), zw p (Or.inl hm), zv p (Or.inl hl)]
      simp
  -- a pair sharing no free link is separable
  have hsep : ∀ p q, ¬ ((Vis p l ∧ Vis q l) ∨ (Vis p m ∧ Vis q m)) →
      Sep (Tf p) (wf p) (vf p) (Tf q) (wf q) (vf q) := by
    intro p q hn
    by_cases hpl : Vis p l <;> by_cases hpm : Vis p m
    · have hql : ¬ Vis q l := fun h => hn (Or.inl ⟨hpl, h⟩)
      have hqm : ¬ Vis q m := fun h => hn (Or.inr ⟨hpm, h⟩)
      exact Or.inr (Or.inl ⟨zT q (Or.inl hql), zw q (Or.inl hqm), zv q (Or.inl hql)⟩)
    · have hql : ¬ Vis q l := fun h => hn (Or.inl ⟨hpl, h⟩)
      by_cases hqm : Vis q m
      · exact Or.inr (Or.inr ⟨zT p (Or.inr hpm), zT q (Or.inl hql), Or.inl (zw p (Or.inl hpm)),
          Or.inr (zv q (Or.inl hql))⟩)
      · exact Or.inr (Or.inl ⟨zT q (Or.inl hql), zw q (Or.inl hqm), zv q (Or.inl hql)⟩)
    · have hqm : ¬ Vis q m := fun h => hn (Or.inr ⟨hpm, h⟩)
      by_cases hql : Vis q l
      · exact Or.inr (Or.inr ⟨zT p (Or.inl hpl), zT q (Or.inr hqm), Or.inr (zw q (Or.inl hqm)),
          Or.inl (zv p (Or.inl hpl))⟩)
      · exact Or.inr (Or.inl ⟨zT q (Or.inl hql), zw q (Or.inl hqm), zv q (Or.inl hql)⟩)
    · exact Or.inl ⟨zT p (Or.inl hpl), zw p (Or.inl hpm), zv p (Or.inl hpl)⟩
  -- the pointwise bounds
  have b1 : ∀ p q, c p * ‖Tf q‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q l ∧ Vis q m)) then 2 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hc p).2.1, (hTf q).1, hc0 p, norm_nonneg (Tf q)]
    · rcases not_and_or.mp h with hd | hq
      · rw [(hc p).2.2 (not_not.mp hd)]
        simp
      · rw [(hTf q).2 hq]
        simp
  have b2 : ∀ p q, ‖vf q‖ * ‖wf p‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q l ∧ ¬ Vis q m)) then 1 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hvf q).1, (hwf p).1, norm_nonneg (vf q), norm_nonneg (wf p)]
    · rcases not_and_or.mp h with hd | hq
      · rw [zw p (Or.inl (zd p m hd))]
        simp
      · rw [(hvf q).2 hq]
        simp
  have b3 : ∀ p q, c p * ‖wf q‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q m ∧ ¬ Vis q l)) then 2 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hc p).2.1, (hwf q).1, hc0 p, norm_nonneg (wf q)]
    · rcases not_and_or.mp h with hd | hq
      · rw [(hc p).2.2 (not_not.mp hd)]
        simp
      · rw [(hwf q).2 hq]
        simp
  have b4 : ∀ p q, c p * ‖vf q‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q l ∧ ¬ Vis q m)) then 2 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hc p).2.1, (hvf q).1, hc0 p, norm_nonneg (vf q)]
    · rcases not_and_or.mp h with hd | hq
      · rw [(hc p).2.2 (not_not.mp hd)]
        simp
      · rw [(hvf q).2 hq]
        simp
  have bR : ∀ pq : WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1),
      ∀ x y : FE N, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |pairR Tf wf vf pq x y|
        ≤ if ((Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m)) then 1 else 0 := by
    intro pq x y hx hy
    refine (abs_pairR_le Tf wf vf pq hx hy).trans ?_
    by_cases hs : Sep (Tf pq.1) (wf pq.1) (vf pq.1) (Tf pq.2) (wf pq.2) (vf pq.2)
    · rw [if_pos hs]
      split_ifs <;> norm_num
    · rw [if_neg hs]
      by_cases hsh : (Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m)
      · rw [if_pos hsh]
        have h1 := hone pq.1
        have h2 := hone pq.2
        have n1 : 0 ≤ ‖Tf pq.1‖ + ‖wf pq.1‖ + ‖vf pq.1‖ := by positivity
        have n2' : 0 ≤ ‖Tf pq.2‖ + ‖wf pq.2‖ + ‖vf pq.2‖ := by positivity
        nlinarith
      · exact absurd (hsep pq.1 pq.2 hsh) hs
  -- the counts, as reals
  have cBoth := card_both_eq M l m
  have cLo := card_only_add_le M l m
  have cMo := card_only_add_le M m l
  rw [MassGap.PairCount.n2_symm M m l] at cMo
  have cLoR : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
      Vis q l ∧ ¬ Vis q m)).card : ℝ) ≤ 12 - (n2 M l m : ℝ) := by
    have : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
        Vis q l ∧ ¬ Vis q m)).card : ℝ) + (n2 M l m : ℝ) ≤ 12 := by exact_mod_cast cLo
    linarith
  have cMoR : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
      Vis q m ∧ ¬ Vis q l)).card : ℝ) ≤ 12 - (n2 M l m : ℝ) := by
    have : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
        Vis q m ∧ ¬ Vis q l)).card : ℝ) + (n2 M l m : ℝ) ≤ 12 := by exact_mod_cast cMo
    linarith
  have L1 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ Vis pq.2 m))).card : ℝ)
        ≤ 48 * (n2 M l m : ℝ) := by
    have h := card_adj_left_le M (fun q => Vis q l ∧ Vis q m)
    rw [cBoth] at h
    exact_mod_cast h
  have R1 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ Vis pq.1 m))).card : ℝ)
        ≤ 48 * (n2 M l m : ℝ) := by
    have h := card_adj_right_le M (fun q => Vis q l ∧ Vis q m)
    rw [cBoth] at h
    exact_mod_cast h
  have L2 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_left_le M (fun q => Vis q l ∧ ¬ Vis q m)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q l ∧ ¬ Vis q m)).card : ℝ) := by exact_mod_cast h
    linarith
  have R2 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_right_le M (fun q => Vis q l ∧ ¬ Vis q m)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q l ∧ ¬ Vis q m)).card : ℝ) := by exact_mod_cast h
    linarith
  have L3 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_left_le M (fun q => Vis q m ∧ ¬ Vis q l)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q m ∧ ¬ Vis q l)).card : ℝ) := by exact_mod_cast h
    linarith
  have R3 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_right_le M (fun q => Vis q m ∧ ¬ Vis q l)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q m ∧ ¬ Vis q l)).card : ℝ) := by exact_mod_cast h
    linarith
  have cS : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) =>
        (Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m))).card : ℝ) ≤ 288 := by
    exact_mod_cast card_share_le M l m
  -- the family coefficients
  obtain ⟨A, hA⟩ : ∃ A : FE N →L[ℝ] FE N, A = ∑ pq ∈ adjSet (bdT M), pairOp c Tf wf vf pq :=
    ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : FE N, a = ∑ pq ∈ adjSet (bdT M), pairA c wf pq := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : FE N, b = ∑ pq ∈ adjSet (bdT M), pairB c vf pq := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ pq ∈ adjSet (bdT M), c pq.1 * c pq.2 := ⟨_, rfl⟩
  have hAn : ‖A‖ ≤ 192 * (n2 M l m : ℝ) + 96 * (12 - (n2 M l m : ℝ)) := by
    rw [hA]
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), ‖pairOp c Tf wf vf pq‖ := norm_sum_le _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            ((if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ Vis pq.2 m)) then (2 : ℝ) else 0)
              + (if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m)) then (1 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ Vis pq.1 m)) then (2 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m)) then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum fun pq _ => (norm_pairOp_le c Tf wf vf hc0 pq).trans (by
            linarith [b1 pq.1 pq.2, b2 pq.1 pq.2, b1 pq.2 pq.1, b2 pq.2 pq.1])
      _ = 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ Vis pq.2 m))).card
              : ℝ)
            + 1 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card : ℝ)
            + 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ Vis pq.1 m))).card
              : ℝ)
            + 1 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_eq,
            sum_ite_eq, sum_ite_eq, sum_ite_eq]
      _ ≤ _ := by linarith
  have han : ‖a‖ ≤ 192 * (12 - (n2 M l m : ℝ)) := by
    rw [ha]
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), ‖pairA c wf pq‖ := norm_sum_le _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            ((if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l)) then (2 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l)) then (2 : ℝ) else 0)) :=
          Finset.sum_le_sum fun pq _ => (norm_pairA_le c wf hc0 pq).trans (by
            linarith [b3 pq.1 pq.2, b3 pq.2 pq.1])
      _ = 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l))).card : ℝ)
            + 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l))).card : ℝ) := by
          rw [Finset.sum_add_distrib, sum_ite_eq, sum_ite_eq]
      _ ≤ _ := by linarith
  have hbn : ‖b‖ ≤ 192 * (12 - (n2 M l m : ℝ)) := by
    rw [hb]
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), ‖pairB c vf pq‖ := norm_sum_le _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            ((if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m)) then (2 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m)) then (2 : ℝ) else 0)) :=
          Finset.sum_le_sum fun pq _ => (norm_pairB_le c vf hc0 pq).trans (by
            linarith [b4 pq.1 pq.2, b4 pq.2 pq.1])
      _ = 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card : ℝ)
            + 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card : ℝ) := by
          rw [Finset.sum_add_distrib, sum_ite_eq, sum_ite_eq]
      _ ≤ _ := by linarith
  refine ⟨K₀ * Real.exp (-lam * C), T₀ + lam • A, α₀ + lam • a, γ₀ + lam • b,
    fun h g => -lam * ∑ pq ∈ adjSet (bdT M),
      pairR Tf wf vf pq (realFeature N h) (realFeature N g),
    mul_pos hK (Real.exp_pos _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hAn (abs_nonneg lam)
    linarith
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left han (abs_nonneg lam)
    nlinarith
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hbn (abs_nonneg lam)
    nlinarith
  · exact continuous_const.mul (continuous_finset_sum _ fun pq _ =>
      continuous_pairR Tf wf vf (continuous_realFeature N) pq)
  · intro h g
    have hx : ‖realFeature N h‖ ≤ 1 := (norm_realFeature hN h).le
    have hy : ‖realFeature N g‖ ≤ 1 := (norm_realFeature hN g).le
    show |-lam * _| ≤ _
    rw [abs_mul, abs_neg, mul_comm (288 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), |pairR Tf wf vf pq (realFeature N h) (realFeature N g)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            (if ((Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m)) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun pq _ => bR pq _ _ hx hy
      _ = 1 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                (Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m))).card : ℝ) := sum_ite_eq _ _ _
      _ ≤ 288 := by linarith
  · intro h g
    have hadj : adjAct (bdT M) (Function.update (Function.update W m h) l g)
        = C - phi A a b (realFeature N h) (realFeature N g)
          + ∑ pq ∈ adjSet (bdT M), pairR Tf wf vf pq (realFeature N h) (realFeature N g) := by
      rw [hC, hA, ha, hb, ← sum_pair_mul]
      unfold adjAct
      exact Finset.sum_congr rfl fun pq _ => by rw [hform pq.1 h g, hform pq.2 h g]
    unfold wtAdj
    rw [hw h g, hadj]
    have key : ∀ e1 e2 e3 e4 e5 : ℝ, e1 + e2 = e3 + e4 + e5 →
        K₀ * Real.exp e1 * Real.exp e2 = K₀ * Real.exp e3 * Real.exp e4 * Real.exp e5 := by
      intro e1 e2 e3 e4 e5 he
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add, Real.exp_add]
      ring
    unfold fibreWeight
    apply key
    simp only [phi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right,
      inner_add_left, real_inner_smul_right, real_inner_smul_left]
    ring

#print axioms wtAdj_fibre_eq

open MassGap.CompactGauge (probHaar)
open MassGap.PairInterface (FibreBound)
open MassGap.FibrePerturb (CovBoundOn covBoundOn_perturb_cont)
open MassGap.WeightedHeatBath (FibreHyp fibreHyp_iff)

/-- **The torus fibre hypothesis for the adjacent-coupled weight, sharp form**: a fibre bound at
`c` on the enlarged tilted family (`wtAdj_fibre_eq`'s `τ`, `κ`) gives the fibre hypothesis at
`e^ε (c + 2 (e^ε − 1))` with `ε = 288 |λ|` (`FibrePerturb.covBoundOn_perturb_cont`). Only the
adjacent pairs sharing a free link cost; the rest moves the tilts.

DERIVED: `4` is the spacetime dimension; `1` is the least `M` and the successor writing the extent
and `e^0`; `0` is the excluded rank and the lower end of `β`, `c`; `12`, `192`, `96`, `288` are
`wtAdj_fibre_eq`'s; `2` is the perturbation lemma's two additive terms. -/
theorem torus_fibreHyp_adj_sharp (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (lam : ℝ) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) {c τ κ : ℝ} (hc : 0 ≤ c)
    (hτ : β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ) + 96 * (12 - (n2 M l m : ℝ))) ≤ τ)
    (hκ : (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ≤ κ)
    (hB : FibreBound (probHaar (SU N)) (realFeature N) c τ κ) :
    FibreHyp (MassGap.WeightedHeatBath.wtAdj (N := N) (bdT M) β lam) l m
      (Real.exp (288 * |lam|) * (c + 2 * (Real.exp (288 * |lam|) - 1))) := by
  rw [fibreHyp_iff _ hlm]
  intro W
  obtain ⟨K, T, α, γ, V, hK, hT, hα, hγ, hVc, hVb, heq⟩ := wtAdj_fibre_eq hN hβ hM hlm lam W
  have hcov : CovBoundOn (fun a : SU N → ℝ => Continuous a ∧ ∃ C, ∀ x, |a x| ≤ C)
      (probHaar (SU N)) (fibreWeight (realFeature N) K T α γ) c := fun a b ha hb hz =>
    hB K T α γ hK (hT.trans hτ) (hα.trans hκ) (hγ.trans hκ) a b ha.1 hb.1 hz
  have hX := continuous_realFeature N
  have hwc : Continuous (Function.uncurry (fibreWeight (realFeature N) K T α γ)) := by
    show Continuous fun z : SU N × SU N => fibreWeight (realFeature N) K T α γ z.1 z.2
    unfold fibreWeight
    exact continuous_const.mul (Real.continuous_exp.comp
      ((((hX.comp continuous_fst).inner (T.continuous.comp (hX.comp continuous_snd))).add
        (continuous_const.inner (hX.comp continuous_fst))).add
        (continuous_const.inner (hX.comp continuous_snd))))
  have hwG : MassGap.FibrePerturb.Good (fibreWeight (realFeature N) K T α γ) := by
    obtain ⟨C, hC⟩ := MassGap.HeatBath.exists_abs_le hwc
    exact ⟨hwc.measurable, C, fun h g => hC (h, g)⟩
  have hw0 : ∀ h g, 0 ≤ fibreWeight (realFeature N) K T α γ h g := fun h g => by
    unfold fibreWeight
    positivity
  have hp := covBoundOn_perturb_cont (probHaar (SU N)) hc (by positivity) hwG hw0 hVc.measurable
    hVb hcov
  have e : (fun h g => fibreWeight (realFeature N) K T α γ h g * Real.exp (V h g))
      = fun h g => MassGap.WeightedHeatBath.wtAdj (bdT M) β lam
          (Function.update (Function.update W m h) l g) := by
    funext h g
    exact (heq h g).symm
  rw [e] at hp
  exact hp

#print axioms torus_fibreHyp_adj_sharp

/-! ## 5. The observer's box: `SU(2)`, `β ≤ 1/200`, `|λ| ≤ 1/20000` -/

open MassGap.PairCorrSharp (PairCheck fibreBound_of_pairCheck)

/-- The fibre hypothesis is monotone in its constant for a nonnegative weight.

DERIVED: `0` is the sign of the weight; `2` is the halving. -/
theorem fibreHyp_mono {Lk : Type} [Fintype Lk] [DecidableEq Lk] {Φ : (Lk → SU N) → ℝ} (hΦ : ∀ W, 0 ≤ Φ W) {l m : Lk}
    {c c' : ℝ} (H : FibreHyp Φ l m c) (hcc : c ≤ c') : FibreHyp Φ l m c' := by
  intro W a b ha hb hz
  refine (H W a b ha hb hz).trans ?_
  have hq : 0 ≤ ∫ h, a h ^ 2 * MassGap.HeatBathErgodic.havg l Φ (Function.update W m h)
      ∂(probHaar (SU N)) :=
    integral_nonneg fun h => mul_nonneg (sq_nonneg _)
      (integral_nonneg fun g => hΦ _)
  have hp : 0 ≤ ∫ g, b g ^ 2 * MassGap.HeatBathErgodic.havg m Φ (Function.update W l g)
      ∂(probHaar (SU N)) :=
    integral_nonneg fun g => mul_nonneg (sq_nonneg _)
      (integral_nonneg fun h => hΦ _)
  have hs := add_nonneg hq hp
  nlinarith

#print axioms fibreHyp_mono

/-- **The perturbation factor at `|λ| ≤ 1/20000`**: `e^{288|λ|} ≤ 1/(1 − 9/625) = 625/616`
(`Real.exp_bound_div_one_sub_of_interval`).

DERIVED: `288` is `card_share_le`'s bound; `9/625 = 288/20000`; `625/616 = 1/(1 − 9/625)`;
`9/616 = 625/616 − 1`; `2` is the perturbation lemma's two additive terms; `0`, `1` are the
interval's ends. CHOSEN: `1/20000`, the observer box's coupling bound. -/
theorem pert_le {lam : ℝ} (hl : |lam| ≤ 1 / 20000) {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.exp (288 * |lam|) * (δ + 2 * (Real.exp (288 * |lam|) - 1))
      ≤ 625 / 616 * (δ + 2 * (9 / 616)) := by
  have hx0 : 0 ≤ 288 * |lam| := by positivity
  have hx1 : 288 * |lam| ≤ 9 / 625 := by linarith
  have he : Real.exp (288 * |lam|) ≤ 625 / 616 := by
    refine (Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have he1 : 1 ≤ Real.exp (288 * |lam|) := Real.one_le_exp hx0
  have h2 : δ + 2 * (Real.exp (288 * |lam|) - 1) ≤ δ + 2 * (9 / 616) := by linarith
  calc _ ≤ 625 / 616 * (δ + 2 * (Real.exp (288 * |lam|) - 1)) :=
        mul_le_mul_of_nonneg_right he (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by norm_num)

#print axioms pert_le

/-- **`SU(2)`, single pair, observer box**: `dstar ≤ 203/10000` at
`τ = 2/200 + 1344/20000 = 772/10000`, `κ = 10 (1/200 + 192/20000) = 146/1000`.

DERIVED: `4`, `1/8`, `0` are `HaarMomentsSU2.haarConsts_su2`'s `D`, `q4`, `t3`; `772/10000`,
`146/1000` are `wtAdj_fibre_eq`'s `τ`, `κ` at `n2 = 2`, `β = 1/200`, `|λ| = 1/20000`.
CHOSEN: `1768/10000 ≥ √(1/32)`, `5014/10000 ≥ √M₂ = √0.251400…`; `203/10000` rounds the computed
`0.0202373…` up. -/
theorem pairCheck_adj_single :
    PairCheck 4 (1 / 8) 0 (1768 / 10000) (5014 / 10000) (772 / 10000) (146 / 1000) (203 / 10000) := by
  norm_num [PairCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms pairCheck_adj_single

/-- **`SU(2)`, double pair, observer box**: `dstar ≤ 256/10000` at
`τ = 4/200 + 1536/20000 = 968/10000`, `κ = 8 (1/200 + 192/20000) = 1168/10000`.

DERIVED: as `pairCheck_adj_single` at `n2 = 4`. CHOSEN: `1768/10000 ≥ √(1/32)`,
`5009/10000 ≥ √M₂ = √0.250887…`; `256/10000` rounds the computed `0.0255768…` up.
COMPUTED: `968/10000 = 4/200 + 1536/20000` and `1168/10000 = 8 (1/200 + 192/20000)`, the
`wtAdj_fibre_eq` `τ`, `κ` at `n2 = 4`; `8 = 12 − n2`. -/
theorem pairCheck_adj_double :
    PairCheck 4 (1 / 8) 0 (1768 / 10000) (5009 / 10000) (968 / 10000) (1168 / 10000) (256 / 10000) := by
  norm_num [PairCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms pairCheck_adj_double

/-- **The `SU(2)` fibre hypothesis on the observer box, single pair** (`n2 = 2`): constant
`503/10000` for `0 ≤ β ≤ 1/200`, `|λ| ≤ 1/20000` (`torus_fibreHyp_adj_sharp`, `pairCheck_adj_single`,
`pert_le`).

DERIVED: `2` is the rank and the single pair's `n2`; `503/10000` rounds
`(625/616)(203/10000 + 18/616) = 0.0502443…` up; the rest as in `pairCheck_adj_single`.
CHOSEN: `1/200` (`β` ceiling) and `1/20000` (`|λ|` ceiling) are the coupling window
`pairCheck_adj_single` is evaluated at; `200`, `20000` are their denominators. -/
theorem fibreHyp_adj_single {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) {lam : ℝ}
    (hl : |lam| ≤ 1 / 20000) {M : ℕ} (hM : 1 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) (hn : n2 M l m = 2) :
    FibreHyp (MassGap.WeightedHeatBath.wtAdj (N := 2) (bdT M) β lam) l m (503 / 10000) := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hB := fibreBound_of_pairCheck h2 MassGap.HaarMomentsSU2.haarConsts_su2 pairCheck_adj_single
  have hn' : (n2 M l m : ℝ) = 2 := by exact_mod_cast hn
  have H := torus_fibreHyp_adj_sharp h2 hβ0 lam hM hlm (by norm_num : (0 : ℝ) ≤ 203 / 10000)
    (by rw [hn']; nlinarith [abs_nonneg lam]) (by rw [hn']; nlinarith [abs_nonneg lam]) hB
  refine fibreHyp_mono (Lk := WilsonHypercubic.Link 4 (M + 1)) (fun W => (mul_pos (MassGap.HeatBath.wt_pos _ _ _) (Real.exp_pos _)).le) H ?_
  refine (pert_le hl (by norm_num)).trans ?_
  norm_num

#print axioms fibreHyp_adj_single

/-- **The `SU(2)` fibre hypothesis on the observer box, double pair** (`n2 = 4`): constant
`557/10000`.

DERIVED: `4` is the double pair's `n2`; `557/10000` rounds `(625/616)(256/10000 + 18/616) =
0.0556217…` up; the rest as in `fibreHyp_adj_single`, including the window `β ≤ 1/200`,
`|λ| ≤ 1/20000` (`200`, `20000`). -/
theorem fibreHyp_adj_double {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) {lam : ℝ}
    (hl : |lam| ≤ 1 / 20000) {M : ℕ} (hM : 1 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) (hn : n2 M l m = 4) :
    FibreHyp (MassGap.WeightedHeatBath.wtAdj (N := 2) (bdT M) β lam) l m (557 / 10000) := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hB := fibreBound_of_pairCheck h2 MassGap.HaarMomentsSU2.haarConsts_su2 pairCheck_adj_double
  have hn' : (n2 M l m : ℝ) = 4 := by exact_mod_cast hn
  have H := torus_fibreHyp_adj_sharp h2 hβ0 lam hM hlm (by norm_num : (0 : ℝ) ≤ 256 / 10000)
    (by rw [hn']; nlinarith [abs_nonneg lam]) (by rw [hn']; nlinarith [abs_nonneg lam]) hB
  refine fibreHyp_mono (Lk := WilsonHypercubic.Link 4 (M + 1)) (fun W => (mul_pos (MassGap.HeatBath.wt_pos _ _ _) (Real.exp_pos _)).le) H ?_
  refine (pert_le hl (by norm_num)).trans ?_
  norm_num

#print axioms fibreHyp_adj_double

/-! ## 6. The single-link parts of the remainder -/

/-- The adjacent pairs `(p, q)` with `p` through `m` only and `q` through `l` only: the cross pairs
whose product is the bilinear pairing `⟪w_p, X h⟫⟪v_q, X g⟫`. -/
def crossSet (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    Finset (WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1)) :=
  (adjSet (bdT M)).filter fun pq => (Vis pq.1 m ∧ ¬ Vis pq.1 l) ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m)

/-- **Adjacent pairs both through one link**: at most `144 = 12²`.

DERIVED: `144 = 12 · 12`; `12` is `card_visit_nondiag_le`'s bound; `4` is the spacetime dimension;
`1` is the successor writing the extent. -/
theorem card_vis_pair_le (M : ℕ) (k : WilsonHypercubic.Link 4 (M + 1)) :
    ((adjSet (bdT M)).filter (fun pq => Vis pq.1 k ∧ Vis pq.2 k)).card ≤ 144 := by
  have hsub : (adjSet (bdT M)).filter (fun pq => Vis pq.1 k ∧ Vis pq.2 k)
      ⊆ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ k ∈ (bdT M p).map Prod.fst)
          ×ˢ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
            p.1.1 ≠ p.1.2 ∧ k ∈ (bdT M p).map Prod.fst) := by
    intro pq hpq
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hpq).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
  have hk := MassGap.PairCount.card_visit_nondiag_le M k
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ 12 * 12 := by
        rw [Finset.card_product]
        exact Nat.mul_le_mul hk hk
    _ = 144 := by norm_num

#print axioms card_vis_pair_le

/-- **Adjacent pairs with a plaquette through both links and the other through either**: at most
`48 n2`.

DERIVED: `48 = 2 · 24`, the two orders and `24 = 12 + 12` plaquettes through `l` or `m`; `12` is
`card_visit_nondiag_le`'s bound; `4` is the spacetime dimension; `1` is the successor writing the
extent. -/
theorem card_mix_le (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    ((adjSet (bdT M)).filter (fun pq =>
      ((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
        ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m)))).card ≤ 48 * n2 M l m := by
  set B := Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l ∧ Vis q m) with hB
  set U := Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)
    ∪ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ m ∈ (bdT M p).map Prod.fst) with hU
  have hUm : ∀ q, (Vis q l ∨ Vis q m) → q ∈ U := fun q hq => by
    rcases hq with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hsub : (adjSet (bdT M)).filter (fun pq =>
      ((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
        ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m))) ⊆ (B ×ˢ U) ∪ (U ×ˢ B) := by
    intro pq hpq
    rcases (Finset.mem_filter.mp hpq).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, hUm _ h2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨hUm _ h2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩)
  have hBc : B.card = n2 M l m := card_both_eq M l m
  have hUc : U.card ≤ 24 := by
    refine (Finset.card_union_le _ _).trans ?_
    have := MassGap.PairCount.card_visit_nondiag_le M l
    have := MassGap.PairCount.card_visit_nondiag_le M m
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (B ×ˢ U).card + (U ×ˢ B).card := Finset.card_union_le _ _
    _ = B.card * U.card + U.card * B.card := by rw [Finset.card_product, Finset.card_product]
    _ ≤ n2 M l m * 24 + 24 * n2 M l m := by
        rw [hBc]
        exact Nat.add_le_add (Nat.mul_le_mul le_rfl hUc) (Nat.mul_le_mul hUc le_rfl)
    _ = 48 * n2 M l m := by ring

#print axioms card_mix_le

/-- The links visited by a plaquette number at most `4`.

DERIVED: `4` is the word length; `1` is the successor writing the extent. -/
theorem card_links_le (M : ℕ) (p : WilsonHypercubic.Plaq 4 (M + 1)) :
    (Finset.univ.filter (fun k : WilsonHypercubic.Link 4 (M + 1) =>
      k ∈ (bdT M p).map Prod.fst)).card ≤ 4 := by
  have hsub : Finset.univ.filter (fun k : WilsonHypercubic.Link 4 (M + 1) =>
      k ∈ (bdT M p).map Prod.fst) ⊆ ((bdT M p).map Prod.fst).toFinset := fun k hk =>
    List.mem_toFinset.mpr (Finset.mem_filter.mp hk).2
  refine (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans ?_)
  simp [WilsonHypercubic.bd]

#print axioms card_links_le

/-- **The cross pairs of one link, summed over its partners**: `Σ_m #crossSet l m ≤ 2304`. Each
adjacent pair `(p, q)` with `q` through `l` is counted once for every link of `p`.

DERIVED: `2304 = 4 · 48 · 12`: `4` links of `p` (`card_links_le`), `48` partners
(`card_adj_left_le`), `12` plaquettes through `l` (`card_visit_nondiag_le`); `1` is the successor
writing the extent. -/
theorem sum_cross_le (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ m, (crossSet M l m).card ≤ 2304 := by
  have hS := card_adj_left_le M (fun q => Vis q l)
  have hV : (Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l)).card ≤ 12 :=
    le_trans (Finset.card_le_card fun q hq => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩)
      (MassGap.PairCount.card_visit_nondiag_le M l)
  unfold crossSet
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ pq ∈ adjSet (bdT M), ∑ m : WilsonHypercubic.Link 4 (M + 1),
        (if (Vis pq.1 m ∧ ¬ Vis pq.1 l) ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m) then 1 else 0)
      ≤ ∑ pq ∈ adjSet (bdT M), (if (pq.1.1.1 ≠ pq.1.1.2 ∧ Vis pq.2 l) then 4 else 0) := by
        refine Finset.sum_le_sum fun pq _ => ?_
        rw [← Finset.card_filter]
        split_ifs with h
        · refine le_trans (Finset.card_le_card fun k hk => ?_) (card_links_le M pq.1)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.1.1.2⟩
        · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro k _ hk
          exact h ⟨hk.1.1.1, hk.2.1⟩
    _ = 4 * ((adjSet (bdT M)).filter (fun pq => pq.1.1.1 ≠ pq.1.1.2 ∧ Vis pq.2 l)).card := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 4 * (48 * 12) := Nat.mul_le_mul_left 4 (hS.trans (Nat.mul_le_mul_left 48 hV))
    _ = 2304 := by norm_num

#print axioms sum_cross_le

/-- **The mirror**: `Σ_m #crossSet m l ≤ 2304`.

DERIVED: as `sum_cross_le`, with `card_adj_right_le`; `2304 = 4 · 48 · 12`. -/
theorem sum_cross_le' (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ m, (crossSet M m l).card ≤ 2304 := by
  have hS := card_adj_right_le M (fun q => Vis q l)
  have hV : (Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) => Vis q l)).card ≤ 12 :=
    le_trans (Finset.card_le_card fun q hq => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩)
      (MassGap.PairCount.card_visit_nondiag_le M l)
  unfold crossSet
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ pq ∈ adjSet (bdT M), ∑ m : WilsonHypercubic.Link 4 (M + 1),
        (if (Vis pq.1 l ∧ ¬ Vis pq.1 m) ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l) then 1 else 0)
      ≤ ∑ pq ∈ adjSet (bdT M), (if (pq.2.1.1 ≠ pq.2.1.2 ∧ Vis pq.1 l) then 4 else 0) := by
        refine Finset.sum_le_sum fun pq _ => ?_
        rw [← Finset.card_filter]
        split_ifs with h
        · refine le_trans (Finset.card_le_card fun k hk => ?_) (card_links_le M pq.2)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.2.1.2⟩
        · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro k _ hk
          exact h ⟨hk.2.1.1, hk.1.1⟩
    _ = 4 * ((adjSet (bdT M)).filter (fun pq => pq.2.1.1 ≠ pq.2.1.2 ∧ Vis pq.1 l)).card := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 4 * (48 * 12) := Nat.mul_le_mul_left 4 (hS.trans (Nat.mul_le_mul_left 48 hV))
    _ = 2304 := by norm_num

#print axioms sum_cross_le'

open MassGap.PairInterface (dstar dstarNum dstarDen dstarE dstarZ cR) in
/-- **The pair bound is at most linear in the coupling below a checked one**: for
`0 ≤ τ ≤ τ₀`, `dstar τ ≤ (τ/τ₀) dstar τ₀` (with `c₂ = cR τ`). The numerator is `τ` times a
quantity increasing in `τ`, and the denominator decreases. So defects at small coupling add like
their couplings.

DERIVED: `0` is the lower end of `τ`, `M₂`, `σ`, `mb`; `2` is the square and the halving in
`dstarE`; `1` is the normalisation in `dstarZ`, `dstarDen`. -/
theorem dstar_le_linear {τ τ₀ M₂ σ mb : ℝ} (hτ : 0 ≤ τ) (hττ : τ ≤ τ₀) (hτ₀ : 0 < τ₀)
    (hM : 0 ≤ M₂) (hσ : 0 ≤ σ) (hmb : 0 ≤ mb) (hZ : 0 < dstarZ τ₀ mb)
    (hden : 0 < dstarDen τ₀ M₂ σ mb (cR τ₀)) :
    dstar τ M₂ σ mb (cR τ) ≤ τ / τ₀ * dstar τ₀ M₂ σ mb (cR τ₀) := by
  have hc0 : ∀ t, 0 ≤ t → 0 ≤ cR t := fun t ht => by unfold cR; positivity
  have hc : cR τ ≤ cR τ₀ := by unfold cR; gcongr
  have hZτ : dstarZ τ₀ mb ≤ dstarZ τ mb := by
    unfold dstarZ
    nlinarith [sq_nonneg mb]
  have hZτ0 : 0 < dstarZ τ mb := lt_of_lt_of_le hZ hZτ
  -- `E t = t e t`
  have he : ∀ t, dstarE t M₂ σ mb (cR t) = t * (σ * mb + cR t * t * M₂ / 2) := fun t => by
    unfold dstarE
    ring
  have he0 : ∀ t, 0 ≤ t → 0 ≤ σ * mb + cR t * t * M₂ / 2 := fun t ht => by
    have := hc0 t ht
    positivity
  have hcm : cR τ * τ * M₂ ≤ cR τ₀ * τ₀ * M₂ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hc hττ hτ (hc0 τ₀ hτ₀.le)) hM
  have hemono : σ * mb + cR τ * τ * M₂ / 2 ≤ σ * mb + cR τ₀ * τ₀ * M₂ / 2 := by linarith
  -- the bracket `N t = M₂ + cR t · t M₂ + t e² / Z`
  have hnum : ∀ t, 0 < dstarZ t mb → dstarNum t M₂ σ mb (cR t)
      = t * (M₂ + cR t * t * M₂ + t * (σ * mb + cR t * t * M₂ / 2) ^ 2 / dstarZ t mb) := by
    intro t hZt
    unfold dstarNum
    rw [he t]
    field_simp
  have hN : M₂ + cR τ * τ * M₂ + τ * (σ * mb + cR τ * τ * M₂ / 2) ^ 2 / dstarZ τ mb
      ≤ M₂ + cR τ₀ * τ₀ * M₂ + τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 / dstarZ τ₀ mb := by
    have h1 := hcm
    have h2 : τ * (σ * mb + cR τ * τ * M₂ / 2) ^ 2 ≤ τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 :=
      mul_le_mul hττ (pow_le_pow_left₀ (he0 τ hτ) hemono 2) (sq_nonneg _) hτ₀.le
    have h3 : τ * (σ * mb + cR τ * τ * M₂ / 2) ^ 2 / dstarZ τ mb
        ≤ τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 / dstarZ τ₀ mb := by
      have := he0 τ hτ
      calc _ ≤ τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 / dstarZ τ mb :=
            div_le_div_of_nonneg_right h2 hZτ0.le
        _ ≤ _ := div_le_div_of_nonneg_left (by have := he0 τ₀ hτ₀.le; positivity) hZ hZτ
    linarith
  -- the denominator decreases
  have hD : dstarDen τ₀ M₂ σ mb (cR τ₀) ≤ dstarDen τ M₂ σ mb (cR τ) := by
    unfold dstarDen
    rw [he τ, he τ₀]
    have h1 : (τ * (σ * mb + cR τ * τ * M₂ / 2)) ^ 2 ≤ (τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hτ (he0 τ hτ)) (mul_le_mul hττ hemono (he0 τ hτ) hτ₀.le) 2
    have h2 : (τ * (σ * mb + cR τ * τ * M₂ / 2)) ^ 2 / dstarZ τ mb
        ≤ (τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2)) ^ 2 / dstarZ τ₀ mb :=
      calc _ ≤ (τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2)) ^ 2 / dstarZ τ mb :=
            div_le_div_of_nonneg_right h1 hZτ0.le
        _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hZ hZτ
    have h3 : τ * mb ≤ τ₀ * mb := mul_le_mul_of_nonneg_right hττ hmb
    linarith
  have hDτ : 0 < dstarDen τ M₂ σ mb (cR τ) := lt_of_lt_of_le hden hD
  have hNτ0 : 0 ≤ M₂ + cR τ * τ * M₂ + τ * (σ * mb + cR τ * τ * M₂ / 2) ^ 2 / dstarZ τ mb := by
    have := hc0 τ hτ
    positivity
  unfold dstar
  rw [hnum τ hZτ0, hnum τ₀ hZ]
  rw [div_le_iff₀ hDτ]
  calc τ * (M₂ + cR τ * τ * M₂ + τ * (σ * mb + cR τ * τ * M₂ / 2) ^ 2 / dstarZ τ mb)
      ≤ τ * (M₂ + cR τ₀ * τ₀ * M₂ + τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 / dstarZ τ₀ mb) :=
        mul_le_mul_of_nonneg_left hN hτ
    _ = τ / τ₀ * (τ₀ * (M₂ + cR τ₀ * τ₀ * M₂
          + τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 / dstarZ τ₀ mb)
          / dstarDen τ₀ M₂ σ mb (cR τ₀)) * dstarDen τ₀ M₂ σ mb (cR τ₀) := by
        field_simp
    _ ≤ _ := by
        have hR : 0 ≤ τ / τ₀ * (τ₀ * (M₂ + cR τ₀ * τ₀ * M₂
            + τ₀ * (σ * mb + cR τ₀ * τ₀ * M₂ / 2) ^ 2 / dstarZ τ₀ mb)
            / dstarDen τ₀ M₂ σ mb (cR τ₀)) := by
          have := hc0 τ₀ hτ₀.le
          have := he0 τ₀ hτ₀.le
          positivity
        exact mul_le_mul_of_nonneg_left hD hR

#print axioms dstar_le_linear

set_option maxHeartbeats 1000000 in
/-- **The adjacent-coupled weight with the remainder split by what it reads.** As
`wtAdj_fibre_eq`, with `V = V_h(h) + V_g(g) + V_m(h, g)`: `|V_h|, |V_g| ≤ 144 |λ|` (pairs both through
`m`, or both through `l`, reading that link only), `|V_m| ≤ 48 n2 |λ|` (pairs with a plaquette through
both links), and the coupling bounded by the pair's own cross pairs:
`‖T‖ ≤ β n2 + |λ| (192 n2 + #crossSet l m + #crossSet m l)`. At `n2 = 0` the mixed part vanishes and
the single-link parts are density factors (`PairFibreDens`).

DERIVED: `4` is the spacetime dimension; `1` is the least `M`, the successor writing the extent and
the feature norm; `0` is the excluded rank, the lower end of `β` and the frozen feature; `12`, `192`
as in `wtAdj_fibre_eq`; `144` is `card_vis_pair_le`'s and `48` `card_mix_le`'s bound. -/
theorem wtAdj_dens_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) (lam : ℝ)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    ∃ (K : ℝ) (T : FE N →L[ℝ] FE N) (α γ : FE N) (Vh Vg : SU N → ℝ) (Vm : SU N → SU N → ℝ),
      0 < K ∧
      ‖T‖ ≤ β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
        + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))) ∧
      ‖α‖ ≤ (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ∧
      ‖γ‖ ≤ (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ∧
      Continuous Vh ∧ Continuous Vg ∧ Continuous (Function.uncurry Vm) ∧
      (∀ h, |Vh h| ≤ 144 * |lam|) ∧ (∀ g, |Vg g| ≤ 144 * |lam|) ∧
      (∀ h g, |Vm h g| ≤ 48 * (n2 M l m : ℝ) * |lam|) ∧
      ∀ h g : SU N, wtAdj (bdT M) β lam (Function.update (Function.update W m h) l g)
        = fibreWeight (realFeature N) K T α γ h g * Real.exp (Vh h + Vg g + Vm h g) := by
  obtain ⟨K₀, T₀, α₀, γ₀, hK, hT0, hα0, hγ0, hw⟩ := MassGap.PairWeight.wt_fibre_eq hN hβ hM hlm W
  choose c Tf wf vf hc hTf hwf hvf hform using dens_form hN hM hlm W
  have hc0 : ∀ p, 0 ≤ c p := fun p => (hc p).1
  have zT : ∀ p, ¬ Vis p l ∨ ¬ Vis p m → Tf p = 0 := fun p h =>
    (hTf p).2 fun h' => h.elim (· h'.1) (· h'.2)
  have zw : ∀ p, ¬ Vis p m ∨ Vis p l → wf p = 0 := fun p h =>
    (hwf p).2 fun h' => h.elim (· h'.1) (h'.2 ·)
  have zv : ∀ p, ¬ Vis p l ∨ Vis p m → vf p = 0 := fun p h =>
    (hvf p).2 fun h' => h.elim (· h'.1) (h'.2 ·)
  have hone : ∀ p, ‖Tf p‖ + ‖wf p‖ + ‖vf p‖ ≤ 1 := by
    intro p
    by_cases hl : Vis p l <;> by_cases hm : Vis p m
    · rw [zw p (Or.inr hl), zv p (Or.inr hm)]
      simpa using (hTf p).1
    · rw [zT p (Or.inr hm), zw p (Or.inl hm)]
      simpa using (hvf p).1
    · rw [zT p (Or.inl hl), zv p (Or.inl hl)]
      simpa using (hwf p).1
    · rw [zT p (Or.inl hl), zw p (Or.inl hm), zv p (Or.inl hl)]
      simp
  have hsep : ∀ p q, ¬ ((Vis p l ∧ Vis q l) ∨ (Vis p m ∧ Vis q m)) →
      Sep (Tf p) (wf p) (vf p) (Tf q) (wf q) (vf q) := by
    intro p q hn
    by_cases hpl : Vis p l <;> by_cases hpm : Vis p m
    · have hql : ¬ Vis q l := fun h => hn (Or.inl ⟨hpl, h⟩)
      have hqm : ¬ Vis q m := fun h => hn (Or.inr ⟨hpm, h⟩)
      exact Or.inr (Or.inl ⟨zT q (Or.inl hql), zw q (Or.inl hqm), zv q (Or.inl hql)⟩)
    · have hql : ¬ Vis q l := fun h => hn (Or.inl ⟨hpl, h⟩)
      by_cases hqm : Vis q m
      · exact Or.inr (Or.inr ⟨zT p (Or.inr hpm), zT q (Or.inl hql), Or.inl (zw p (Or.inl hpm)),
          Or.inr (zv q (Or.inl hql))⟩)
      · exact Or.inr (Or.inl ⟨zT q (Or.inl hql), zw q (Or.inl hqm), zv q (Or.inl hql)⟩)
    · have hqm : ¬ Vis q m := fun h => hn (Or.inr ⟨hpm, h⟩)
      by_cases hql : Vis q l
      · exact Or.inr (Or.inr ⟨zT p (Or.inl hpl), zT q (Or.inr hqm), Or.inr (zw q (Or.inl hqm)),
          Or.inl (zv p (Or.inl hpl))⟩)
      · exact Or.inr (Or.inl ⟨zT q (Or.inl hql), zw q (Or.inl hqm), zv q (Or.inl hql)⟩)
    · exact Or.inl ⟨zT p (Or.inl hpl), zw p (Or.inl hpm), zv p (Or.inl hpl)⟩
  -- the pointwise bounds of the family coefficients
  have b1 : ∀ p q, c p * ‖Tf q‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q l ∧ Vis q m)) then 2 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hc p).2.1, (hTf q).1, hc0 p, norm_nonneg (Tf q)]
    · rcases not_and_or.mp h with hd | hq
      · rw [(hc p).2.2 (not_not.mp hd)]
        simp
      · rw [(hTf q).2 hq]
        simp
  have b2 : ∀ p q, ‖vf q‖ * ‖wf p‖
      ≤ if ((Vis p m ∧ ¬ Vis p l) ∧ (Vis q l ∧ ¬ Vis q m)) then 1 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hvf q).1, (hwf p).1, norm_nonneg (vf q), norm_nonneg (wf p)]
    · rcases not_and_or.mp h with hp | hq
      · rw [(hwf p).2 hp]
        simp
      · rw [(hvf q).2 hq]
        simp
  have b2' : ∀ p q, ‖vf p‖ * ‖wf q‖
      ≤ if ((Vis p l ∧ ¬ Vis p m) ∧ (Vis q m ∧ ¬ Vis q l)) then 1 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hvf p).1, (hwf q).1, norm_nonneg (vf p), norm_nonneg (wf q)]
    · rcases not_and_or.mp h with hp | hq
      · rw [(hvf p).2 hp]
        simp
      · rw [(hwf q).2 hq]
        simp
  have b3 : ∀ p q, c p * ‖wf q‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q m ∧ ¬ Vis q l)) then 2 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hc p).2.1, (hwf q).1, hc0 p, norm_nonneg (wf q)]
    · rcases not_and_or.mp h with hd | hq
      · rw [(hc p).2.2 (not_not.mp hd)]
        simp
      · rw [(hwf q).2 hq]
        simp
  have b4 : ∀ p q, c p * ‖vf q‖ ≤ if (p.1.1 ≠ p.1.2 ∧ (Vis q l ∧ ¬ Vis q m)) then 2 else 0 := by
    intro p q
    split_ifs with h
    · nlinarith [(hc p).2.1, (hvf q).1, hc0 p, norm_nonneg (vf q)]
    · rcases not_and_or.mp h with hd | hq
      · rw [(hc p).2.2 (not_not.mp hd)]
        simp
      · rw [(hvf q).2 hq]
        simp
  -- the remainder of one pair is at most `1`, and `0` off the shared pairs
  have bR : ∀ pq : WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1),
      ∀ x y : FE N, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → |pairR Tf wf vf pq x y| ≤ 1 := by
    intro pq x y hx hy
    refine (abs_pairR_le Tf wf vf pq hx hy).trans ?_
    split_ifs
    · norm_num
    · have h1 := hone pq.1
      have h2 := hone pq.2
      have n1 : 0 ≤ ‖Tf pq.1‖ + ‖wf pq.1‖ + ‖vf pq.1‖ := by positivity
      have n2' : 0 ≤ ‖Tf pq.2‖ + ‖wf pq.2‖ + ‖vf pq.2‖ := by positivity
      nlinarith
  have sR : ∀ pq : WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1),
      ∀ x y : FE N, Sep (Tf pq.1) (wf pq.1) (vf pq.1) (Tf pq.2) (wf pq.2) (vf pq.2) →
      pairR Tf wf vf pq x y = 0 := fun pq x y hs => by
    unfold pairR
    rw [if_pos hs]
  have bRg : ∀ pq : WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1),
      ∀ x y : FE N, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |pairRg Tf wf vf pq x y| ≤ if (Vis pq.1 l ∧ Vis pq.2 l) then 1 else 0 := by
    intro pq x y hx hy
    by_cases hcg : Tf pq.1 = 0 ∧ Tf pq.2 = 0 ∧ wf pq.1 = 0 ∧ wf pq.2 = 0
    · rw [pairRg, if_pos hcg]
      by_cases hs : Vis pq.1 l ∧ Vis pq.2 l
      · rw [if_pos hs]
        exact bR pq x y hx hy
      · rw [if_neg hs]
        have hv : vf pq.1 = 0 ∨ vf pq.2 = 0 := by
          rcases not_and_or.mp hs with h | h
          · exact Or.inl (zv _ (Or.inl h))
          · exact Or.inr (zv _ (Or.inl h))
        have hS : Sep (Tf pq.1) (wf pq.1) (vf pq.1) (Tf pq.2) (wf pq.2) (vf pq.2) := by
          rcases hv with h | h
          · exact Or.inl ⟨hcg.1, hcg.2.2.1, h⟩
          · exact Or.inr (Or.inl ⟨hcg.2.1, hcg.2.2.2, h⟩)
        rw [sR pq x y hS, abs_zero]
    · rw [pairRg, if_neg hcg, abs_zero]
      split_ifs <;> norm_num
  have bRh : ∀ pq : WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1),
      ∀ x y : FE N, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |pairRh Tf wf vf pq x y| ≤ if (Vis pq.1 m ∧ Vis pq.2 m) then 1 else 0 := by
    intro pq x y hx hy
    by_cases hch : Tf pq.1 = 0 ∧ Tf pq.2 = 0 ∧ vf pq.1 = 0 ∧ vf pq.2 = 0
    · rw [pairRh, if_pos hch]
      by_cases hs : Vis pq.1 m ∧ Vis pq.2 m
      · rw [if_pos hs]
        exact bR pq x y hx hy
      · rw [if_neg hs]
        have hw' : wf pq.1 = 0 ∨ wf pq.2 = 0 := by
          rcases not_and_or.mp hs with h | h
          · exact Or.inl (zw _ (Or.inl h))
          · exact Or.inr (zw _ (Or.inl h))
        have hS : Sep (Tf pq.1) (wf pq.1) (vf pq.1) (Tf pq.2) (wf pq.2) (vf pq.2) := by
          rcases hw' with h | h
          · exact Or.inl ⟨hch.1, h, hch.2.2.1⟩
          · exact Or.inr (Or.inl ⟨hch.2.1, h, hch.2.2.2⟩)
        rw [sR pq x y hS, abs_zero]
    · rw [pairRh, if_neg hch, abs_zero]
      split_ifs <;> norm_num
  have bRm : ∀ pq : WilsonHypercubic.Plaq 4 (M + 1) × WilsonHypercubic.Plaq 4 (M + 1),
      ∀ x y : FE N, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |pairRm Tf wf vf pq x y|
        ≤ if (((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
            ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m))) then 1 else 0 := by
    intro pq x y hx hy
    have hite0 : (0 : ℝ) ≤ if (((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
        ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m))) then 1 else 0 := by
      split_ifs <;> norm_num
    by_cases hcg : Tf pq.1 = 0 ∧ Tf pq.2 = 0 ∧ wf pq.1 = 0 ∧ wf pq.2 = 0
    · by_cases hch : Tf pq.1 = 0 ∧ Tf pq.2 = 0 ∧ vf pq.1 = 0 ∧ vf pq.2 = 0
      · have hS : Sep (Tf pq.1) (wf pq.1) (vf pq.1) (Tf pq.2) (wf pq.2) (vf pq.2) :=
          Or.inl ⟨hcg.1, hcg.2.2.1, hch.2.2.1⟩
        rw [pairRm, pairRg, pairRh, if_pos hcg, if_pos hch, sR pq x y hS]
        simpa using hite0
      · rw [pairRm, pairRg, pairRh, if_pos hcg, if_neg hch]
        simpa using hite0
    · by_cases hch : Tf pq.1 = 0 ∧ Tf pq.2 = 0 ∧ vf pq.1 = 0 ∧ vf pq.2 = 0
      · rw [pairRm, pairRg, pairRh, if_neg hcg, if_pos hch]
        simpa using hite0
      · rw [pairRm, pairRg, pairRh, if_neg hcg, if_neg hch, sub_zero, sub_zero]
        by_cases hS : Sep (Tf pq.1) (wf pq.1) (vf pq.1) (Tf pq.2) (wf pq.2) (vf pq.2)
        · rw [sR pq x y hS, abs_zero]
          exact hite0
        · -- not separable: a pairing is present and the pair shares a free link
          have hsh : (Vis pq.1 l ∧ Vis pq.2 l) ∨ (Vis pq.1 m ∧ Vis pq.2 m) := by
            by_contra hn
            exact hS (hsep pq.1 pq.2 hn)
          have hT : Tf pq.1 ≠ 0 ∨ Tf pq.2 ≠ 0 := by
            by_contra hT
            push_neg at hT
            apply hS
            refine Or.inr (Or.inr ⟨hT.1, hT.2, ?_, ?_⟩)
            · by_contra hw'
              push_neg at hw'
              have h1 : Vis pq.1 m ∧ ¬ Vis pq.1 l := by
                by_contra h
                exact hw'.1 ((hwf pq.1).2 h)
              have h2 : Vis pq.2 m ∧ ¬ Vis pq.2 l := by
                by_contra h
                exact hw'.2 ((hwf pq.2).2 h)
              exact hch ⟨hT.1, hT.2, zv _ (Or.inr h1.1), zv _ (Or.inr h2.1)⟩
            · by_contra hv'
              push_neg at hv'
              have h1 : Vis pq.1 l ∧ ¬ Vis pq.1 m := by
                by_contra h
                exact hv'.1 ((hvf pq.1).2 h)
              have h2 : Vis pq.2 l ∧ ¬ Vis pq.2 m := by
                by_contra h
                exact hv'.2 ((hvf pq.2).2 h)
              exact hcg ⟨hT.1, hT.2, zw _ (Or.inr h1.1), zw _ (Or.inr h2.1)⟩
          have hcond : ((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
              ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m)) := by
            rcases hT with h | h
            · have hv : Vis pq.1 l ∧ Vis pq.1 m := by
                by_contra hn
                exact h ((hTf pq.1).2 hn)
              refine Or.inl ⟨hv, ?_⟩
              rcases hsh with h' | h'
              · exact Or.inl h'.2
              · exact Or.inr h'.2
            · have hv : Vis pq.2 l ∧ Vis pq.2 m := by
                by_contra hn
                exact h ((hTf pq.2).2 hn)
              refine Or.inr ⟨hv, ?_⟩
              rcases hsh with h' | h'
              · exact Or.inl h'.1
              · exact Or.inr h'.1
          rw [if_pos hcond]
          exact bR pq x y hx hy
  -- the counts, as reals
  have cBoth := card_both_eq M l m
  have cLo := card_only_add_le M l m
  have cMo := card_only_add_le M m l
  rw [MassGap.PairCount.n2_symm M m l] at cMo
  have cMoR : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
      Vis q m ∧ ¬ Vis q l)).card : ℝ) ≤ 12 - (n2 M l m : ℝ) := by
    have : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
        Vis q m ∧ ¬ Vis q l)).card : ℝ) + (n2 M l m : ℝ) ≤ 12 := by exact_mod_cast cMo
    linarith
  have cLoR : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
      Vis q l ∧ ¬ Vis q m)).card : ℝ) ≤ 12 - (n2 M l m : ℝ) := by
    have : ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
        Vis q l ∧ ¬ Vis q m)).card : ℝ) + (n2 M l m : ℝ) ≤ 12 := by exact_mod_cast cLo
    linarith
  have L1 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ Vis pq.2 m))).card : ℝ)
        ≤ 48 * (n2 M l m : ℝ) := by
    have h := card_adj_left_le M (fun q => Vis q l ∧ Vis q m)
    rw [cBoth] at h
    exact_mod_cast h
  have R1 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ Vis pq.1 m))).card : ℝ)
        ≤ 48 * (n2 M l m : ℝ) := by
    have h := card_adj_right_le M (fun q => Vis q l ∧ Vis q m)
    rw [cBoth] at h
    exact_mod_cast h
  have L3 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_left_le M (fun q => Vis q m ∧ ¬ Vis q l)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q m ∧ ¬ Vis q l)).card : ℝ) := by exact_mod_cast h
    linarith
  have R3 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_right_le M (fun q => Vis q m ∧ ¬ Vis q l)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q m ∧ ¬ Vis q l)).card : ℝ) := by exact_mod_cast h
    linarith
  have L4 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_left_le M (fun q => Vis q l ∧ ¬ Vis q m)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q l ∧ ¬ Vis q m)).card : ℝ) := by exact_mod_cast h
    linarith
  have R4 : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card : ℝ)
        ≤ 48 * (12 - (n2 M l m : ℝ)) := by
    have h := card_adj_right_le M (fun q => Vis q l ∧ ¬ Vis q m)
    have h' : ((((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
        × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card
          : ℕ) : ℝ) ≤ 48 * ((Finset.univ.filter (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
            Vis q l ∧ ¬ Vis q m)).card : ℝ) := by exact_mod_cast h
    linarith
  have cG : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => Vis pq.1 l ∧ Vis pq.2 l)).card : ℝ) ≤ 144 := by
    exact_mod_cast card_vis_pair_le M l
  have cH : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) => Vis pq.1 m ∧ Vis pq.2 m)).card : ℝ) ≤ 144 := by
    exact_mod_cast card_vis_pair_le M m
  have cX : (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
      × WilsonHypercubic.Plaq 4 (M + 1) =>
        ((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
          ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m)))).card : ℝ)
        ≤ 48 * (n2 M l m : ℝ) := by
    exact_mod_cast card_mix_le M l m
  -- the family coefficients
  obtain ⟨A, hA⟩ : ∃ A : FE N →L[ℝ] FE N, A = ∑ pq ∈ adjSet (bdT M), pairOp c Tf wf vf pq :=
    ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : FE N, a = ∑ pq ∈ adjSet (bdT M), pairA c wf pq := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : FE N, b = ∑ pq ∈ adjSet (bdT M), pairB c vf pq := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ pq ∈ adjSet (bdT M), c pq.1 * c pq.2 := ⟨_, rfl⟩
  have hAn : ‖A‖ ≤ 192 * (n2 M l m : ℝ)
      + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ)) := by
    rw [hA]
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), ‖pairOp c Tf wf vf pq‖ := norm_sum_le _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            ((if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ Vis pq.2 m)) then (2 : ℝ) else 0)
              + (if ((Vis pq.1 m ∧ ¬ Vis pq.1 l) ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m)) then (1 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ Vis pq.1 m)) then (2 : ℝ) else 0)
              + (if ((Vis pq.1 l ∧ ¬ Vis pq.1 m) ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l)) then (1 : ℝ)
                  else 0)) :=
          Finset.sum_le_sum fun pq _ => (norm_pairOp_le c Tf wf vf hc0 pq).trans (by
            linarith [b1 pq.1 pq.2, b2 pq.1 pq.2, b1 pq.2 pq.1, b2' pq.1 pq.2])
      _ = 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) => pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ Vis pq.2 m))).card
              : ℝ)
            + 1 * ((crossSet M l m).card : ℝ)
            + 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) => pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ Vis pq.1 m))).card
              : ℝ)
            + 1 * ((crossSet M m l).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_eq,
            sum_ite_eq, sum_ite_eq, sum_ite_eq]
          rfl
      _ ≤ _ := by linarith
  have han : ‖a‖ ≤ 192 * (12 - (n2 M l m : ℝ)) := by
    rw [ha]
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), ‖pairA c wf pq‖ := norm_sum_le _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            ((if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l)) then (2 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l)) then (2 : ℝ) else 0)) :=
          Finset.sum_le_sum fun pq _ => (norm_pairA_le c wf hc0 pq).trans (by
            linarith [b3 pq.1 pq.2, b3 pq.2 pq.1])
      _ = 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 m ∧ ¬ Vis pq.2 l))).card : ℝ)
            + 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 m ∧ ¬ Vis pq.1 l))).card : ℝ) := by
          rw [Finset.sum_add_distrib, sum_ite_eq, sum_ite_eq]
      _ ≤ _ := by linarith
  have hbn : ‖b‖ ≤ 192 * (12 - (n2 M l m : ℝ)) := by
    rw [hb]
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), ‖pairB c vf pq‖ := norm_sum_le _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            ((if (pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m)) then (2 : ℝ) else 0)
              + (if (pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m)) then (2 : ℝ) else 0)) :=
          Finset.sum_le_sum fun pq _ => (norm_pairB_le c vf hc0 pq).trans (by
            linarith [b4 pq.1 pq.2, b4 pq.2 pq.1])
      _ = 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.1.1.1 ≠ pq.1.1.2 ∧ (Vis pq.2 l ∧ ¬ Vis pq.2 m))).card : ℝ)
            + 2 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                pq.2.1.1 ≠ pq.2.1.2 ∧ (Vis pq.1 l ∧ ¬ Vis pq.1 m))).card : ℝ) := by
          rw [Finset.sum_add_distrib, sum_ite_eq, sum_ite_eq]
      _ ≤ _ := by linarith
  have h0 : ‖(0 : FE N)‖ ≤ 1 := by simp
  refine ⟨K₀ * Real.exp (-lam * C), T₀ + lam • A, α₀ + lam • a, γ₀ + lam • b,
    fun h => -lam * ∑ pq ∈ adjSet (bdT M), pairRh Tf wf vf pq (realFeature N h) 0,
    fun g => -lam * ∑ pq ∈ adjSet (bdT M), pairRg Tf wf vf pq 0 (realFeature N g),
    fun h g => -lam * ∑ pq ∈ adjSet (bdT M),
      pairRm Tf wf vf pq (realFeature N h) (realFeature N g),
    mul_pos hK (Real.exp_pos _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hAn (abs_nonneg lam)
    linarith
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left han (abs_nonneg lam)
    linarith
  · refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hbn (abs_nonneg lam)
    linarith
  · have hX := continuous_realFeature N
    refine continuous_const.mul (continuous_finset_sum _ fun pq _ => ?_)
    have h1 := (continuous_pairRh Tf wf vf hX pq).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : SU N => (1 : SU N)))
    refine h1.congr fun h => ?_
    show pairRh Tf wf vf pq (realFeature N h) (realFeature N 1)
      = pairRh Tf wf vf pq (realFeature N h) 0
    exact pairRh_right Tf wf vf pq _ _ _
  · have hX := continuous_realFeature N
    refine continuous_const.mul (continuous_finset_sum _ fun pq _ => ?_)
    have h1 := (continuous_pairRg Tf wf vf hX pq).comp
      ((continuous_const : Continuous fun _ : SU N => (1 : SU N)).prodMk continuous_id)
    refine h1.congr fun g => ?_
    show pairRg Tf wf vf pq (realFeature N 1) (realFeature N g)
      = pairRg Tf wf vf pq 0 (realFeature N g)
    exact pairRg_left Tf wf vf pq _ _ _
  · exact continuous_const.mul (continuous_finset_sum _ fun pq _ =>
      continuous_pairRm Tf wf vf (continuous_realFeature N) pq)
  · intro h
    have hx : ‖realFeature N h‖ ≤ 1 := (norm_realFeature hN h).le
    show |-lam * _| ≤ _
    rw [abs_mul, abs_neg, mul_comm (144 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), |pairRh Tf wf vf pq (realFeature N h) 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M), (if (Vis pq.1 m ∧ Vis pq.2 m) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun pq _ => bRh pq _ _ hx h0
      _ = 1 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) => Vis pq.1 m ∧ Vis pq.2 m)).card : ℝ) :=
          sum_ite_eq _ _ _
      _ ≤ 144 := by linarith
  · intro g
    have hy : ‖realFeature N g‖ ≤ 1 := (norm_realFeature hN g).le
    show |-lam * _| ≤ _
    rw [abs_mul, abs_neg, mul_comm (144 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), |pairRg Tf wf vf pq 0 (realFeature N g)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M), (if (Vis pq.1 l ∧ Vis pq.2 l) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun pq _ => bRg pq _ _ h0 hy
      _ = 1 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) => Vis pq.1 l ∧ Vis pq.2 l)).card : ℝ) :=
          sum_ite_eq _ _ _
      _ ≤ 144 := by linarith
  · intro h g
    have hx : ‖realFeature N h‖ ≤ 1 := (norm_realFeature hN h).le
    have hy : ‖realFeature N g‖ ≤ 1 := (norm_realFeature hN g).le
    show |-lam * _| ≤ _
    rw [abs_mul, abs_neg, mul_comm (48 * (n2 M l m : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    calc _ ≤ ∑ pq ∈ adjSet (bdT M), |pairRm Tf wf vf pq (realFeature N h) (realFeature N g)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ pq ∈ adjSet (bdT M),
            (if (((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
              ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m))) then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun pq _ => bRm pq _ _ hx hy
      _ = 1 * (((adjSet (bdT M)).filter (fun pq : WilsonHypercubic.Plaq 4 (M + 1)
              × WilsonHypercubic.Plaq 4 (M + 1) =>
                ((Vis pq.1 l ∧ Vis pq.1 m) ∧ (Vis pq.2 l ∨ Vis pq.2 m))
                  ∨ ((Vis pq.2 l ∧ Vis pq.2 m) ∧ (Vis pq.1 l ∨ Vis pq.1 m)))).card : ℝ) :=
          sum_ite_eq _ _ _
      _ ≤ 48 * (n2 M l m : ℝ) := by linarith
  · intro h g
    have hsplitR : ∑ pq ∈ adjSet (bdT M), pairR Tf wf vf pq (realFeature N h) (realFeature N g)
        = ∑ pq ∈ adjSet (bdT M), pairRh Tf wf vf pq (realFeature N h) 0
          + ∑ pq ∈ adjSet (bdT M), pairRg Tf wf vf pq 0 (realFeature N g)
          + ∑ pq ∈ adjSet (bdT M), pairRm Tf wf vf pq (realFeature N h) (realFeature N g) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun pq _ => ?_
      rw [pairRh_right Tf wf vf pq (realFeature N h) 0 (realFeature N g),
        pairRg_left Tf wf vf pq 0 (realFeature N h) (realFeature N g), pairRm]
      ring
    have hadj : adjAct (bdT M) (Function.update (Function.update W m h) l g)
        = C - phi A a b (realFeature N h) (realFeature N g)
          + ∑ pq ∈ adjSet (bdT M), pairR Tf wf vf pq (realFeature N h) (realFeature N g) := by
      rw [hC, hA, ha, hb, ← sum_pair_mul]
      unfold adjAct
      exact Finset.sum_congr rfl fun pq _ => by rw [hform pq.1 h g, hform pq.2 h g]
    unfold wtAdj
    rw [hw h g, hadj, hsplitR]
    have key : ∀ e1 e2 e3 e4 e5 : ℝ, e1 + e2 = e3 + e4 + e5 →
        K₀ * Real.exp e1 * Real.exp e2 = K₀ * Real.exp e3 * Real.exp e4 * Real.exp e5 := by
      intro e1 e2 e3 e4 e5 he
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add, Real.exp_add]
      ring
    unfold fibreWeight
    apply key
    simp only [phi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right,
      inner_add_left, real_inner_smul_right, real_inner_smul_left]
    ring

#print axioms wtAdj_dens_eq

open MassGap.PairFibreDens (Dens nearTilt DensFibreBound densWeight)

/-- **The torus fibre hypothesis with the single-link parts as densities**: a `DensFibreBound` at
`c` on the coupling `τ` and the densities within `e^{±144|λ|}` of a tilt of norm `κ`
(`wtAdj_dens_eq`'s single-link parts) gives the fibre hypothesis at `e^ε (c + 2 (e^ε − 1))` with
`ε = 48 n2 |λ|`: only the mixed part, present when a plaquette reads both links, costs additively.
At `n2 = 0` the constant is `c`.

DERIVED: `4` is the spacetime dimension; `1` is the least `M` and the successor writing the extent;
`0` is the excluded rank and the lower end of `β`, `c`; `12`, `192`, `144`, `48` are
`wtAdj_dens_eq`'s; `2` is the perturbation lemma's two additive terms. -/
theorem torus_fibreHyp_adj_dens (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (lam : ℝ) {M : ℕ} (hM : 1 ≤ M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) {c τ κ : ℝ} (hc : 0 ≤ c)
    (hτ : β * (n2 M l m : ℝ) + |lam| * (192 * (n2 M l m : ℝ)
      + (((crossSet M l m).card : ℝ) + ((crossSet M m l).card : ℝ))) ≤ τ)
    (hκ : (β + 192 * |lam|) * (12 - (n2 M l m : ℝ)) ≤ κ)
    (hB : DensFibreBound (probHaar (SU N)) (realFeature N) c τ
      (nearTilt (realFeature N) κ (144 * |lam|))) :
    FibreHyp (MassGap.WeightedHeatBath.wtAdj (N := N) (bdT M) β lam) l m
      (Real.exp (48 * (n2 M l m : ℝ) * |lam|)
        * (c + 2 * (Real.exp (48 * (n2 M l m : ℝ) * |lam|) - 1))) := by
  rw [fibreHyp_iff _ hlm]
  intro W
  obtain ⟨K, T, α, γ, Vh, Vg, Vm, hK, hT, hα, hγ, hVh, hVg, hVm, bVh, bVg, bVm, heq⟩ :=
    wtAdj_dens_eq hN hβ hM hlm lam W
  have hX := continuous_realFeature N
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ : Dens (SU N),
      ∀ h, θ.f h = Real.exp (inner ℝ α (realFeature N h) + Vh h) :=
    ⟨⟨fun h => Real.exp (inner ℝ α (realFeature N h) + Vh h),
      Real.continuous_exp.comp ((continuous_const.inner hX).add hVh), fun h => Real.exp_pos _⟩,
      fun h => rfl⟩
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ : Dens (SU N),
      ∀ g, θ.f g = Real.exp (inner ℝ γ (realFeature N g) + Vg g) :=
    ⟨⟨fun g => Real.exp (inner ℝ γ (realFeature N g) + Vg g),
      Real.continuous_exp.comp ((continuous_const.inner hX).add hVg), fun g => Real.exp_pos _⟩,
      fun g => rfl⟩
  have near : ∀ (θ : Dens (SU N)) (δ : FE N) (V : SU N → ℝ), ‖δ‖ ≤ κ →
      (∀ x, |V x| ≤ 144 * |lam|) →
      (∀ x, θ.f x = Real.exp (inner ℝ δ (realFeature N x) + V x)) →
      θ ∈ nearTilt (realFeature N) κ (144 * |lam|) := fun θ δ V hδ hV hθ =>
    ⟨δ, hδ, fun x => by
      rw [hθ x, ← Real.exp_add, ← Real.exp_add]
      have := abs_le.mp (hV x)
      exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩⟩
  have h₁ := near θ₁ α Vh (hα.trans hκ) bVh hθ₁
  have h₂ := near θ₂ γ Vg (hγ.trans hκ) bVg hθ₂
  have hcov : CovBoundOn (fun a : SU N → ℝ => Continuous a ∧ ∃ C, ∀ x, |a x| ≤ C)
      (probHaar (SU N)) (densWeight (realFeature N) K T θ₁ θ₂) c := fun a b ha hb hz =>
    hB K T θ₁ θ₂ hK (hT.trans hτ) h₁ h₂ a b ha.1 hb.1 hz
  have hwc : Continuous (Function.uncurry (densWeight (realFeature N) K T θ₁ θ₂)) := by
    show Continuous fun z : SU N × SU N => densWeight (realFeature N) K T θ₁ θ₂ z.1 z.2
    unfold densWeight
    exact ((continuous_const.mul (Real.continuous_exp.comp
      ((hX.comp continuous_fst).inner (T.continuous.comp (hX.comp continuous_snd))))).mul
      (θ₁.cont.comp continuous_fst)).mul (θ₂.cont.comp continuous_snd)
  have hwG : MassGap.FibrePerturb.Good (densWeight (realFeature N) K T θ₁ θ₂) := by
    obtain ⟨C, hC⟩ := MassGap.HeatBath.exists_abs_le hwc
    exact ⟨hwc.measurable, C, fun h g => hC (h, g)⟩
  have hw0 : ∀ h g, 0 ≤ densWeight (realFeature N) K T θ₁ θ₂ h g := fun h g => by
    unfold densWeight
    exact mul_nonneg (mul_nonneg (mul_nonneg hK.le (Real.exp_pos _).le) (θ₁.pos h).le)
      (θ₂.pos g).le
  have hε : 0 ≤ 48 * (n2 M l m : ℝ) * |lam| := by positivity
  have hp := covBoundOn_perturb_cont (probHaar (SU N)) hc hε hwG hw0 hVm.measurable bVm hcov
  have e : (fun h g => densWeight (realFeature N) K T θ₁ θ₂ h g * Real.exp (Vm h g))
      = fun h g => MassGap.WeightedHeatBath.wtAdj (bdT M) β lam
          (Function.update (Function.update W m h) l g) := by
    funext h g
    rw [heq h g]
    unfold densWeight fibreWeight
    rw [hθ₁ h, hθ₂ g]
    simp only [Real.exp_add]
    ring
  rw [e] at hp
  exact hp

#print axioms torus_fibreHyp_adj_dens

end Torus

end MassGap.AdjacentFibre
