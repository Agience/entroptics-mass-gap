import Mathlib
import MassGap.ApeLattice
import MassGap.ContinuumClay
import MassGap.ContinuumFlow
import MassGap.FlowCapstone
import MassGap.LocalApe
import MassGap.ObserverClay

noncomputable section

/-!
# MassGap.ObserverEnergyMoments — the uniform bound on a flow from the moments of one site

`ContinuumFlow.UniformBoundF hN Φ` asks, for every family of smeared flowed fields, overlapping
supports included, one constant bounding the flowed lattice Schwinger functions eventually in the
step, uniformly over dyadic translations. This file reduces it to a statement about one site.

## The reduction

`FlowMomentBound hN Φ`: for every local field `O` and every `p`, the even moment
`ν_k((Φ_k O)^{2p})` of the flowed field at one site is bounded eventually in the step.
`uniformBoundF_of_momentBound` proves `FlowMomentBound → UniformBoundF`, with no other input:

* `abs_prod_le_one_add_sum_pow`: `|∏ᵢ yᵢ| ≤ 1 + ∑ᵢ yᵢ^{2n}`, `n` the number of factors;
* `moment_smear_le`: in a translation-invariant state, at `0 < a ≤ 1`, the smeared field has
  `ν((smear a F f)^{2p}) ≤ (M (2R + 3)⁴)^{2p} ν(F^{2p})` (Jensen on the smearing weights, which sum
  to at most `M (2R + 3)⁴`);
* `abs_latS_le_moments`: hence every lattice Schwinger function of a translated family is at most
  `1 + ∑ᵢ (Mᵢ (2Rᵢ + 3)⁴)^{2n} ν(Gᵢ^{2n})`.

Coincident and overlapping supports cost nothing: the bound reads only single-site moments.

## The observer's energy density

For `Flow.ofConfScaled W canonZ s` the flowed field at one site is `a⁻⁴ (O ∘ V_k − s_k O)`, so
`FlowMomentBound` is `ν_k((O ∘ V_k − s_k O)^{2p}) ≤ C a_k^{8p}` (`flowMomentBound_canon`): every moment
of the smoothed configuration's local reading about `s` is of the order of the cell volume `a⁴`. For
the localised APE observer this is `EnergyMomentBound`.

Applying the canonical factor `a⁻⁴` to every local field is not the statement to ask. A
field that is not smooth at the identity (`√(1 − ½ Re tr U_p)`, of order `a²` on a configuration smooth
at the observer's radius) has `a⁻⁴`-scaled moments growing like `a⁻⁴` in a non-trivial limit, so the
bound over every field is not the statement to ask. `energyOn W D` scales only the fields of a
reflection-closed class `D` and leaves the others bounded; `flowMomentBound_energyOn` needs the moment
bound on `D` alone, and `observer_energyOn_clay_of_moments` is the capstone for it.

## The moments from the zoom

`ZoomBandAt hN Φ O`: a summable `δ ≥ 0` with `ν_{k+1}((Φ_{k+1} O)^{2p}) ≤ e^{δ_k} ν_k((Φ_k O)^{2p})`, the
form a density band between successive single-site laws takes on even moments. `moments_of_zoomBandAt` bounds every moment by `e^{∑ δ}` times its value at step `0`, so
`uniformBoundF_of_zoomBand` and `uniformBoundF_energyOn_of_zoomBand` give E from the zoom alone: the observer's single-site reading has
the same moments at every substrate, up to a summable factor.

## The smeared moments

A single site reads the lattice cell: a plaquette near `−1` contributes `a^{−8p}` to the `2p`-th
single-site moment of `a⁻⁴(1 − plaq)`, so the single-site bound is not the target. The Schwinger
functions read the field only smeared over a physical support. `SmearedMomentBound hN Φ` bounds
`ν_k((smear a_k (Φ_k O) f)^{2p})` eventually in the step, for every field, test function and `p`;
`uniformBoundF_of_smearedMomentBound` gives `UniformBoundF` from it (translations free by
`ContinuumNontrivial.stateK_transObs`), `smearedMomentBound_energyOn` needs it on the class `D` only, and
`observer_energyOn_clay_of_smearedMoments` is the capstone. `SmearedZoomBand` (successive smeared
moments within a summable factor) gives it (`uniformBoundF_energyOn_of_smearedZoomBand`).

## Centre-valued configurations

Every configuration with links in the centre `{±1}` of `SU(2)` is fixed by the dominance-normalised
APE step (`apeConf_central`), hence by the observer flow (`obsFlow_central`); the flat configuration
and the one with a single `−1` link are both centre valued, and the plaquette density reads `0` on the
first and `2` on the second (`plaq_flat`, `plaq_tw`). So the uniform bound has to come from the
state, through the moments, not from a pointwise cap.
-/

namespace MassGap.ObserverEnergyMoments

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
   Filter
open scoped Topology

/-! ## 1. Products by moments -/

section Products

/-- **A product of `n` reals is at most one plus the sum of their `2n`-th powers.** The largest factor
`|y_j|` bounds every factor, so the product is at most `|y_j|ⁿ`; that is at most `1` when `|y_j| ≤ 1`
and at most `y_j^{2n}` otherwise.

DERIVED: `2` makes the power even; `1` the case split at unit size. -/
theorem abs_prod_le_one_add_sum_pow {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    |∏ i, y i| ≤ 1 + ∑ i, y i ^ (2 * Fintype.card ι) := by
  classical
  have hq : Even (2 * Fintype.card ι) := even_two_mul _
  have hsum0 : 0 ≤ ∑ i, y i ^ (2 * Fintype.card ι) :=
    Finset.sum_nonneg (fun i _ => hq.pow_nonneg _)
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |y i|) Finset.univ_nonempty
    have h1 : |∏ i, y i| ≤ |y j| ^ Fintype.card ι := by
      rw [Finset.abs_prod]
      calc ∏ i, |y i| ≤ ∏ _i : ι, |y j| :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => hj i hi)
        _ = |y j| ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
    have h2 : |y j| ^ Fintype.card ι ≤ 1 + y j ^ (2 * Fintype.card ι) := by
      rcases le_or_gt |y j| 1 with h | h
      · have := pow_le_one₀ (n := Fintype.card ι) (abs_nonneg (y j)) h
        linarith [hq.pow_nonneg (y j)]
      · calc |y j| ^ Fintype.card ι ≤ |y j| ^ (2 * Fintype.card ι) :=
              pow_le_pow_right₀ h.le (by omega)
          _ = y j ^ (2 * Fintype.card ι) := hq.pow_abs _
          _ ≤ 1 + y j ^ (2 * Fintype.card ι) := by linarith
    have h3 : y j ^ (2 * Fintype.card ι) ≤ ∑ i, y i ^ (2 * Fintype.card ι) :=
      Finset.single_le_sum (fun i _ => hq.pow_nonneg (y i)) (Finset.mem_univ j)
    linarith

#print axioms abs_prod_le_one_add_sum_pow

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **A pointwise absolute bound passes through a state**: `|g| ≤ h` everywhere gives `|ν g| ≤ ν h`.

DERIVED: no numeral. -/
theorem abs_state_le_of_abs_le (ν : MassGap.DLRLimit.State X) (g h : C(X, ℝ))
    (hgh : ∀ U, |g U| ≤ h U) : |ν g| ≤ ν h := by
  rw [abs_le]
  constructor
  · have h1 : ν (-h) ≤ ν g := ν.mono (fun U => by
      have := hgh U
      rw [ContinuousMap.neg_apply]
      linarith [neg_abs_le (g U)])
    rw [ν.map_neg] at h1
    linarith
  · exact ν.mono (fun U => (le_abs_self _).trans (hgh U))

#print axioms abs_state_le_of_abs_le

end Products

/-! ## 2. The moments of a smeared field -/

section Smear

variable {N : ℕ}

/-- Translation commutes with powers, being precomposition.

DERIVED: `0` is the base of the induction. -/
theorem transObs_pow (x : ISite) (F : C(Cfg N, ℝ)) (q : ℕ) :
    transObs x (F ^ q) = transObs x F ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero]; exact transObs_one x
  | succ q ih => rw [pow_succ, pow_succ, transObs_mul, ih]

#print axioms transObs_pow

/-- **The even moments of a smeared field**: in a translation-invariant state, at every spacing
`0 < a ≤ 1`, `ν((smear a F f)^{2p}) ≤ (M (2R + 3)⁴)^{2p} ν(F^{2p})` for `f` bounded by `M` with support
in `[-R, R]⁴`. With `wₓ = a⁴ f(a x)` and `W = ∑ |wₓ|`, pointwise
`(∑ wₓ zₓ)^{2p} ≤ (∑ (|wₓ|/W) · W|zₓ|)^{2p} ≤ W^{2p} ∑ (|wₓ|/W) zₓ^{2p}` (Jensen for the convex power), each
`ν(T_x F^{2p})` is `ν(F^{2p})`, and `W ≤ M (2R + 3)⁴` (`ContinuumNontrivial.riemann_le`).

DERIVED: `0` is the sign of `a` and of `W`; `1` bounds `a` and normalises the Jensen weights; `2`
makes the power even; `3` and `4` are `ContinuumNontrivial.riemann_le`'s. -/
theorem moment_smear_le (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (F : C(Cfg N, ℝ)) (f : TestFn) {R M : ℝ} (hf : IsTest f.1 R M) (p : ℕ) :
    ν (smear a F f ^ (2 * p)) ≤ (M * (2 * R + 3) ^ 4) ^ (2 * p) * ν (F ^ (2 * p)) := by
  classical
  set s := box ⌈R / a⌉₊ with hs
  set w : ISite → ℝ := fun x => a ^ 4 * f.1 (site a x) with hw
  set W : ℝ := ∑ x ∈ s, |w x| with hW
  have hq : Even (2 * p) := even_two_mul p
  have hsm : smear a F f = ∑ x ∈ s, w x • transObs x F := smear_eq_sum ha F f hf (subset_refl _)
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have hWle : W ≤ M * (2 * R + 3) ^ 4 := by
    have hg : IsTest (fun y => |f.1 y|) R M :=
      ⟨hf.1, fun y => by rw [abs_abs]; exact hf.2.1 y,
        fun y hy i => hf.2.2 y (fun h => hy (by simp [h])) i⟩
    have h := ContinuumNontrivial.riemann_le ha ha1 hg
    have e : W = ∑ x ∈ s, a ^ 4 * |f.1 (site a x)| := by
      rw [hW]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hw, abs_mul, abs_of_nonneg (pow_nonneg ha.le 4)]
    rw [e]
    exact h
  have hFq : 0 ≤ ν (F ^ (2 * p)) :=
    ν.nonneg _ (fun U => by rw [ContinuousMap.pow_apply]; exact hq.pow_nonneg _)
  have hval : ∀ U : Cfg N, smear a F f U = ∑ x ∈ s, w x * F (transConf x U) := by
    intro U
    rw [hsm]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
      smul_eq_mul]
  have key : ν (smear a F f ^ (2 * p)) ≤ W ^ (2 * p) * ν (F ^ (2 * p)) := by
    rcases hW0.lt_or_eq with hWpos | hWz
    · have hbound : ν (smear a F f ^ (2 * p))
          ≤ ν (W ^ (2 * p) • ∑ x ∈ s, (|w x| / W) • transObs x (F ^ (2 * p))) := by
        refine ν.mono (fun U => ?_)
        rw [ContinuousMap.pow_apply, hval U]
        simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
          transObs_apply, ContinuousMap.pow_apply, smul_eq_mul]
        have hv0 : ∀ x ∈ s, 0 ≤ |w x| / W := fun x _ => div_nonneg (abs_nonneg _) hWpos.le
        have hv1 : ∑ x ∈ s, |w x| / W = 1 := by
          rw [← Finset.sum_div, ← hW, div_self hWpos.ne']
        have habs : |∑ x ∈ s, w x * F (transConf x U)|
            ≤ ∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|) := by
          calc |∑ x ∈ s, w x * F (transConf x U)|
              ≤ ∑ x ∈ s, |w x * F (transConf x U)| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|) :=
                Finset.sum_congr rfl (fun x _ => by
                  rw [abs_mul]
                  field_simp)
        have hj := Real.pow_arith_mean_le_arith_mean_pow s (fun x => |w x| / W)
          (fun x => W * |F (transConf x U)|) hv0 hv1
          (fun x _ => mul_nonneg hWpos.le (abs_nonneg _)) (2 * p)
        calc (∑ x ∈ s, w x * F (transConf x U)) ^ (2 * p)
            = |∑ x ∈ s, w x * F (transConf x U)| ^ (2 * p) := (hq.pow_abs _).symm
          _ ≤ (∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|)) ^ (2 * p) :=
              pow_le_pow_left₀ (abs_nonneg _) habs _
          _ ≤ ∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|) ^ (2 * p) := hj
          _ = W ^ (2 * p) * ∑ x ∈ s, |w x| / W * F (transConf x U) ^ (2 * p) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [mul_pow, hq.pow_abs]
              ring
      have hrhs : ν (W ^ (2 * p) • ∑ x ∈ s, (|w x| / W) • transObs x (F ^ (2 * p)))
          = W ^ (2 * p) * ν (F ^ (2 * p)) := by
        rw [ν.map_smul, ν.map_sum]
        have : ∀ x ∈ s, ν ((|w x| / W) • transObs x (F ^ (2 * p))) = |w x| / W * ν (F ^ (2 * p)) :=
          fun x _ => by rw [ν.map_smul, htr]
        rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Finset.sum_div, ← hW,
          div_self hWpos.ne', one_mul]
      exact hbound.trans hrhs.le
    · have hw0 : ∀ x ∈ s, w x = 0 := fun x hx =>
        abs_eq_zero.mp (le_antisymm
          ((Finset.single_le_sum (fun y _ => abs_nonneg (w y)) hx).trans hWz.symm.le)
          (abs_nonneg _))
      have hS0 : smear a F f = 0 := by
        rw [hsm]
        exact Finset.sum_eq_zero (fun x hx => by rw [hw0 x hx, zero_smul])
      rw [hS0, ← hWz]
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · rw [zero_pow (by omega), ν.map_zero, zero_pow (by omega), zero_mul]
  calc ν (smear a F f ^ (2 * p)) ≤ W ^ (2 * p) * ν (F ^ (2 * p)) := key
    _ ≤ (M * (2 * R + 3) ^ 4) ^ (2 * p) * ν (F ^ (2 * p)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hW0 hWle _) hFq

#print axioms moment_smear_le

/-- **A lattice Schwinger function from single-site moments**: in a translation-invariant state, at
`0 < a ≤ 1`, a product of `n` smeared fields, each translated by its own lattice vector, has
`|ν(∏ᵢ smear a Gᵢ (fᵢ translated))| ≤ 1 + ∑ᵢ (Mᵢ (2Rᵢ + 3)⁴)^{2n} ν(Gᵢ^{2n})`.

DERIVED: `1` and `2` are `abs_prod_le_one_add_sum_pow`'s; `3` and `4` are `moment_smear_le`'s; `0`
is the sign of `a`. -/
theorem abs_latS_le_moments (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) {ι : Type} [Fintype ι] (G : ι → C(Cfg N, ℝ)) (f : ι → TestFn) (R M : ι → ℝ)
    (hRM : ∀ i, IsTest (f i).1 (R i) (M i)) (v : ι → ISite) :
    |ν (∏ i, smear a (G i) ((f i).translate (site a (v i))))|
      ≤ 1 + ∑ i, (M i * (2 * R i + 3) ^ 4) ^ (2 * Fintype.card ι) * ν (G i ^ (2 * Fintype.card ι)) := by
  have hpt := abs_state_le_of_abs_le ν (∏ i, smear a (G i) ((f i).translate (site a (v i))))
    (1 + ∑ i, smear a (G i) ((f i).translate (site a (v i))) ^ (2 * Fintype.card ι))
    (fun U => by
      simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.sum_apply,
        ContinuousMap.prod_apply, ContinuousMap.pow_apply]
      exact abs_prod_le_one_add_sum_pow _)
  rw [ν.map_add, ν.map_one, ν.map_sum] at hpt
  refine hpt.trans (add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ?_)))
  rw [smear_translate ha, ← transObs_pow, htr]
  exact moment_smear_le ν htr ha ha1 (G i) (f i) (hRM i) (Fintype.card ι)

#print axioms abs_latS_le_moments

end Smear

/-! ## 3. The uniform bound from the moments -/

section Uniform

variable {N : ℕ}

/-- **The single-site moment bound of a flow**: for every local field `O` and every `p`, the even
moment `ν_k((Φ_k O)^{2p})` of the flowed field at one site is bounded eventually in the step.

DERIVED: `0` is the excluded colour count; `2` makes the power even. -/
def FlowMomentBound (hN : N ≠ 0) (Φ : Flow N) : Prop :=
  ∀ (O : LField (MassGap.SUN.SU N)) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
    stateK hN k ((Φ.map k O).1 ^ (2 * p)) ≤ C

/-- **The uniform bound from the single-site moments.** `FlowMomentBound hN Φ` gives
`ContinuumFlow.UniformBoundF hN Φ`: for a family of `n` fields the constant is
`1 + ∑ᵢ (Mᵢ (2Rᵢ + 3)⁴)^{2n} Cᵢ`, `Cᵢ` the eventual bound on the `2n`-th moment of the `i`-th flowed
field, whatever dyadic translation is applied to each factor.

DERIVED: `0` is the excluded colour count; `1`, `2`, `3`, `4` are `abs_latS_le_moments`'s; the
spacing bound `1` enters where `dySpacing N k` falls below one. -/
theorem uniformBoundF_of_momentBound (hN : N ≠ 0) (Φ : Flow N) (h : FlowMomentBound hN Φ) :
    UniformBoundF hN Φ := by
  intro ι _ F
  have hex : ∀ i, ∃ R M : ℝ, IsTest (F i).2.1 R M := fun i => (F i).2.2
  choose R M hRM using hex
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k ((Φ.map k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => h (F i).1 (Fintype.card ι)
  choose C hC using hC
  refine ⟨1 + ∑ i, (M i * (2 * R i + 3) ^ 4) ^ (2 * Fintype.card ι) * C i, fun m n => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop m,
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos), Filter.eventually_all.mpr hC]
    with k hk hk1 hCk
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hfam : (fun i => Φ.field k ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))
      = (fun i => ((Φ.field k (F i)).1, (Φ.field k (F i)).2.translate
          (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))) := by
    funext i
    show (Φ.map k (F i).1, (F i).2.translate (site (dySpacing N m) (n i)))
      = (Φ.map k (F i).1, (F i).2.translate (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))
    rw [site_dySpacing N hk]
  show |latSk hN k (fun i => Φ.field k ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))|
    ≤ _
  rw [latSk_eq, hfam]
  show |stateK hN k (∏ i, smear (dySpacing N k) (Φ.map k (F i).1).1
      ((F i).2.translate (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i)))))| ≤ _
  refine (abs_latS_le_moments (stateK hN k) (fun x G => ContinuumNontrivial.stateK_transObs hN k x G)
    ha hk1.le (fun i => (Φ.map k (F i).1).1) (fun i => (F i).2) R M hRM
    (fun i => scaleSite (2 ^ (k - m)) (n i))).trans ?_
  refine add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ?_))
  exact mul_le_mul_of_nonneg_left (hCk i) ((even_two_mul _).pow_nonneg _)

#print axioms uniformBoundF_of_momentBound

/-- **One moment at the canonical factor**: if `ν_k(X^{2p}) ≤ C a_k^{8p}`, then
`ν_k((a_k⁻⁴ X)^{2p}) ≤ C`.

DERIVED: `0` is the excluded colour count; `4` is the canonical dimension; `8 = 4 · 2` the power of
the spacing in a `2p`-th moment of a dimension-four field; `2` makes the power even. -/
theorem canon_moment_le (hN : N ≠ 0) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (X : C(Cfg N, ℝ))
    (p : ℕ) {C : ℝ} (hk : stateK hN k (X ^ (2 * p)) ≤ C * dySpacing N k ^ (8 * p)) :
    stateK hN k ((canonZ N k O • X) ^ (2 * p)) ≤ C := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [smul_pow, (stateK hN k).map_smul]
  have e : canonZ N k O ^ (2 * p) * dySpacing N k ^ (8 * p) = 1 := by
    unfold canonZ
    rw [inv_pow, ← pow_mul, show 4 * (2 * p) = 8 * p by ring]
    exact inv_mul_cancel₀ (pow_ne_zero _ ha.ne')
  have hz : 0 ≤ canonZ N k O ^ (2 * p) := pow_nonneg (by unfold canonZ; positivity) _
  calc canonZ N k O ^ (2 * p) * stateK hN k (X ^ (2 * p))
      ≤ canonZ N k O ^ (2 * p) * (C * dySpacing N k ^ (8 * p)) := mul_le_mul_of_nonneg_left hk hz
    _ = C := by rw [mul_left_comm, e, mul_one]

#print axioms canon_moment_le

/-- **The canonically scaled configuration flow from its moments.** If every moment of
`O ∘ V_k − s_k(O)` is of order `a_k^{8p}`, the flow `Flow.ofConfScaled W canonZ s` has
`FlowMomentBound`.

DERIVED: `0` is the excluded colour count; `8` and `2` as in `canon_moment_le`; `1` is the unit
observable. -/
theorem flowMomentBound_canon (hN : N ≠ 0) (W : ConfFlow N)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (h : ∀ (O : LField (MassGap.SUN.SU N)) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (((W.fieldMap k O).1 - s k O • (1 : C(Cfg N, ℝ))) ^ (2 * p))
        ≤ C * dySpacing N k ^ (8 * p)) :
    FlowMomentBound hN (Flow.ofConfScaled W (canonZ N) s (canonZ_refl N) hs) := by
  intro O p
  obtain ⟨C, hC⟩ := h O p
  refine ⟨C, ?_⟩
  filter_upwards [hC] with k hk
  exact canon_moment_le hN k O _ p hk

#print axioms flowMomentBound_canon

end Uniform

/-! ## 4. The observer's energy density -/

section Observer

/-- **The energy moment bound of the localised APE observer**: for every local field `O` and every
`p`, eventually in the step `ν_k((O ∘ V_k − s_k O)^{2p}) ≤ C a_k^{8p}`, `V_k` the localised APE smearing
of step `k`: the smoothed configuration's reading of `O` fluctuates about `s_k O` at the order of the
cell volume `a_k⁴` in every moment.

DERIVED: `2` is the rank and makes the power even; `8 = 4 · 2`; `1/6` the dominance bound; `1` the
unit observable. -/
def EnergyMomentBound (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ) : Prop :=
  ∀ (O : LField (MassGap.SUN.SU 2)) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
    stateK two_ne k ((((obsConfFlow c hc0 hc n R).fieldMap k O).1
      - s k O • (1 : C(Cfg 2, ℝ))) ^ (2 * p)) ≤ C * dySpacing 2 k ^ (8 * p)

end Observer

/-! ## 5. Scaling one class of fields -/

section Class

variable {N : ℕ}

open Classical in
/-- **The factor on a class `D`**: `a_k⁻⁴` on the fields of `D`, `1` elsewhere.

DERIVED: `1` is the unscaled factor. -/
noncomputable def zOn (D : Set (LField (MassGap.SUN.SU N))) (k : ℕ)
    (O : LField (MassGap.SUN.SU N)) : ℝ :=
  if O ∈ D then canonZ N k O else 1

open Classical in
/-- **The subtraction on a class `D`**: `s` on the fields of `D`, `0` elsewhere.

DERIVED: `0` is the absent subtraction. -/
noncomputable def sOn (D : Set (LField (MassGap.SUN.SU N))) (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (k : ℕ) (O : LField (MassGap.SUN.SU N)) : ℝ :=
  if O ∈ D then s k O else 0

/-- DERIVED: no numeral. -/
theorem zOn_of_mem {D : Set (LField (MassGap.SUN.SU N))} {O : LField (MassGap.SUN.SU N)}
    (h : O ∈ D) (k : ℕ) : zOn D k O = canonZ N k O := by
  unfold zOn; rw [if_pos h]

/-- DERIVED: `1` is the unscaled factor. -/
theorem zOn_of_not_mem {D : Set (LField (MassGap.SUN.SU N))} {O : LField (MassGap.SUN.SU N)}
    (h : O ∉ D) (k : ℕ) : zOn D k O = 1 := by
  unfold zOn; rw [if_neg h]

/-- DERIVED: no numeral. -/
theorem sOn_of_mem {D : Set (LField (MassGap.SUN.SU N))} {s : ℕ → LField (MassGap.SUN.SU N) → ℝ}
    {O : LField (MassGap.SUN.SU N)} (h : O ∈ D) (k : ℕ) : sOn D s k O = s k O := by
  unfold sOn; rw [if_pos h]

/-- DERIVED: `0` is the absent subtraction. -/
theorem sOn_of_not_mem {D : Set (LField (MassGap.SUN.SU N))} {s : ℕ → LField (MassGap.SUN.SU N) → ℝ}
    {O : LField (MassGap.SUN.SU N)} (h : O ∉ D) (k : ℕ) : sOn D s k O = 0 := by
  unfold sOn; rw [if_neg h]

/-- The class factor is reflection compatible when `D` is reflection closed.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem zOn_refl {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) : zOn D k (O.refl τ) = zOn D k O := by
  by_cases h : O ∈ D
  · rw [zOn_of_mem ((hD τ O).mpr h), zOn_of_mem h]; rfl
  · rw [zOn_of_not_mem (fun h' => h ((hD τ O).mp h')), zOn_of_not_mem h]

#print axioms zOn_refl

/-- The class subtraction is reflection compatible when `D` is reflection closed and `s` is.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem sOn_refl {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    {s : ℕ → LField (MassGap.SUN.SU N) → ℝ}
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) : sOn D s k (O.refl τ) = sOn D s k O := by
  by_cases h : O ∈ D
  · rw [sOn_of_mem ((hD τ O).mpr h), sOn_of_mem h, hs]
  · rw [sOn_of_not_mem (fun h' => h ((hD τ O).mp h')), sOn_of_not_mem h]

#print axioms sOn_refl

/-- **The flow scaled on a class**: `a⁻⁴ (O ∘ V_k − s_k O)` for `O ∈ D`, `O ∘ V_k` otherwise.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def energyOn (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O) :
    Flow N :=
  Flow.ofConfScaled W (zOn D) (sOn D s) (zOn_refl hD) (sOn_refl hD hs)

/-- **The moment bound of the class-scaled flow** needs the moments on `D` only: off `D` the flowed
field `O ∘ V_k` is bounded by `‖O‖`.

DERIVED: `0` is the excluded colour count; `8` and `2` as in `canon_moment_le`; `1` is the unit
observable. -/
theorem flowMomentBound_energyOn (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (h : ∀ O ∈ D, ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (((W.fieldMap k O).1 - s k O • (1 : C(Cfg N, ℝ))) ^ (2 * p))
        ≤ C * dySpacing N k ^ (8 * p)) :
    FlowMomentBound hN (energyOn W D hD s hs) := by
  intro O p
  by_cases hO : O ∈ D
  · obtain ⟨C, hC⟩ := h O hO p
    refine ⟨C, ?_⟩
    filter_upwards [hC] with k hk
    show stateK hN k ((zOn D k O • ((W.fieldMap k O).1 - sOn D s k O • (1 : C(Cfg N, ℝ))))
      ^ (2 * p)) ≤ C
    rw [zOn_of_mem hO, sOn_of_mem hO]
    exact canon_moment_le hN k O _ p hk
  · refine ⟨‖O.1‖ ^ (2 * p), Filter.Eventually.of_forall (fun k => ?_)⟩
    show stateK hN k ((zOn D k O • ((W.fieldMap k O).1 - sOn D s k O • (1 : C(Cfg N, ℝ))))
      ^ (2 * p)) ≤ _
    rw [zOn_of_not_mem hO, sOn_of_not_mem hO, zero_smul, sub_zero, one_smul]
    calc stateK hN k ((W.fieldMap k O).1 ^ (2 * p))
        ≤ stateK hN k (‖O.1‖ ^ (2 * p) • (1 : C(Cfg N, ℝ))) := (stateK hN k).mono (fun U => by
          rw [ContinuousMap.pow_apply]
          simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
          have hU : |(W.fieldMap k O).1 U| ≤ ‖O.1‖ := by
            have := O.1.norm_coe_le_norm (W.V k U)
            rw [Real.norm_eq_abs] at this
            exact this
          rw [← (even_two_mul p).pow_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hU _)
      _ = ‖O.1‖ ^ (2 * p) := by rw [(stateK hN k).map_smul, (stateK hN k).map_one, mul_one]

#print axioms flowMomentBound_energyOn

/-- **The observer's energy density on a class.**

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
noncomputable abbrev obsEnergyOn (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O) : Flow 2 :=
  energyOn (obsConfFlow c hc0 hc n R) D hD s hs

/-- **The class-scaled observer's continuum statement from the moments on the class.** For the
localised APE observer scaled by `a⁻⁴` on a reflection-closed class `D`, the moment bound on `D`, a
physical range bound, absolute clustering at a window `L > 0` and one non-zero connected pairing give,
at every dyadic step, the reconstructed transfer gapped at physical rate `c'/L` on a space with a
non-zero vector orthogonal to the vacuum.

DERIVED: `2` is the rank; `0` the lower end of `L` and `c'`; `8` as in `canon_moment_le`; `1/6` the
dominance bound; `1` the unit observable. -/
theorem observer_energyOn_clay_of_moments {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK two_ne k ((((obsConfFlow c hc0 hc n R).fieldMap k O).1
        - s k O • (1 : C(Cfg 2, ℝ))) ^ (2 * p)) ≤ C * dySpacing 2 k ^ (8 * p))
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) {L : ℝ}
    (hL : 0 < L) (hcl : FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L)
    (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_momentBound two_ne _
              (flowMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_momentBound two_ne _
              (flowMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  flow_clay_of_abs_cluster two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
    (uniformBoundF_of_momentBound two_ne _
      (flowMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) hL hcl hNT

#print axioms observer_energyOn_clay_of_moments

end Class

/-! ## 6. No configuration-wise cap -/

section NoCap

open MassGap.BlockSU2 MassGap.ApeLattice MassGap.LocalApe MassGap.BlockLattice

/-- **A centre element of `SU(2)`**: its matrix is `±1`.

DERIVED: `2` is the rank and the matrix size; `1` and `-1` the two centre elements. -/
def IsCentral (g : MassGap.SUN.SU 2) : Prop :=
  ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ (g : Matrix (Fin 2) (Fin 2) ℂ) = (e : ℂ) • 1

/-- DERIVED: `2` is the rank; `1` and `-1` the centre. -/
theorem central_mul {g h : MassGap.SUN.SU 2} (hg : IsCentral g) (hh : IsCentral h) :
    IsCentral (g * h) := by
  obtain ⟨e, he, hge⟩ := hg
  obtain ⟨f, hf, hhf⟩ := hh
  refine ⟨e * f, ?_, ?_⟩
  · rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> norm_num
  · show (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [hge, hhf, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1
    push_cast
    ring

#print axioms central_mul

/-- A centre element is its own inverse.

DERIVED: `2` is the rank; `1` and `-1` the centre. -/
theorem central_inv {g : MassGap.SUN.SU 2} (hg : IsCentral g) : IsCentral g⁻¹ := by
  have hgg : g * g = 1 := by
    obtain ⟨e, he, hge⟩ := hg
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1
    rw [hge, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rcases he with rfl | rfl <;> simp
  rw [inv_eq_of_mul_eq_one_right hgg]
  exact hg

#print axioms central_inv

/-- **A block step of centre elements returns the link**: `W = e₀ 1`, `Sᵢ = eᵢ 1` give the block matrix
`λ 1` with `λ = e₀ + c ∑ eᵢ` of the sign of `e₀` (`|c ∑ eᵢ| ≤ 6c < 1`), normalised to `e₀ 1 = W`.

DERIVED: `6` is the staple count; `1/6` the dominance bound; `2` the rank and the square in the
determinant; `0` the sign. -/
theorem blockLink_central {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (W : MassGap.SUN.SU 2)
    (S : Fin 6 → MassGap.SUN.SU 2) (hW : IsCentral W) (hS : ∀ i, IsCentral (S i)) :
    blockLink c hc0 hc W S = W := by
  obtain ⟨e0, he0, hWe⟩ := hW
  choose e he hSe using hS
  set lam : ℝ := e0 + c * ∑ i, e i with hlam
  have hB : blockMat c W S = ((lam : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold blockMat mat
    rw [hWe]
    simp only [hSe]
    rw [← Finset.sum_smul, smul_smul, ← add_smul]
    congr 1
    rw [hlam]
    push_cast
    ring
  have hsum : |∑ i, e i| ≤ 6 := by
    calc |∑ i, e i| ≤ ∑ i, |e i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin 6, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => by
          rcases he i with h | h <;> rw [h] <;> norm_num)
      _ = 6 := by simp
  have hs1 := abs_le.mp hsum
  have hc6 : -(6 * c) ≤ c * ∑ i, e i ∧ c * ∑ i, e i ≤ 6 * c :=
    ⟨by nlinarith [mul_le_mul_of_nonneg_left hs1.1 hc0],
     by nlinarith [mul_le_mul_of_nonneg_left hs1.2 hc0]⟩
  have hdet : (blockMat c W S).det.re = lam ^ 2 := by
    rw [hB, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    norm_cast
  have hsign : lam / |lam| = e0 := by
    rcases he0 with rfl | rfl
    · have hp : 0 < lam := by rw [hlam]; linarith [hc6.1]
      rw [abs_of_pos hp, div_self hp.ne']
    · have hn : lam < 0 := by rw [hlam]; linarith [hc6.2]
      rw [abs_of_neg hn, div_neg, div_self hn.ne]
  apply Subtype.ext
  show ((Real.sqrt (blockMat c W S).det.re)⁻¹ : ℂ) • blockMat c W S = (W : Matrix (Fin 2) (Fin 2) ℂ)
  rw [hdet, Real.sqrt_sq_eq_abs, hB, hWe, smul_smul]
  congr 1
  rw [← hsign]
  simp only [Complex.ofReal_div, Complex.ofReal_inv]
  ring

#print axioms blockLink_central

/-- The staples of a centre-valued configuration are central.

DERIVED: `0` names the upper side; `3` the transverse directions of `other` in four dimensions. -/
theorem apeStaple_central {U : IConf G2} (hU : ∀ l, IsCentral (U l)) (μ : Fin 4) (x : ISite)
    (p : Fin 3 × Fin 2) : IsCentral (apeStaple U μ x p) := by
  unfold apeStaple
  split_ifs
  · exact central_mul (central_mul (hU _) (hU _)) (central_inv (hU _))
  · exact central_mul (central_mul (central_inv (hU _)) (hU _)) (hU _)

#print axioms apeStaple_central

/-- **A centre-valued configuration is fixed by the APE step.**

DERIVED: `1/6` the dominance bound. -/
theorem apeConf_central {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) {U : IConf G2}
    (hU : ∀ l, IsCentral (U l)) : apeConf c hc0 hc U = U :=
  funext fun l => blockLink_central hc0 hc (U l) _ (hU l) (fun i => apeStaple_central hU _ _ _)

#print axioms apeConf_central

/-- A centre-valued configuration is fixed by the APE step on any set of links.

DERIVED: `1/6` the dominance bound. -/
theorem apeOn_central {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) {U : IConf G2}
    (hU : ∀ l, IsCentral (U l)) (S : Set ILink) : apeOn c hc0 hc S U = U := by
  funext l
  simp only [apeOn]
  split_ifs
  · rw [apeConf_central hc0 hc hU]
  · rfl

#print axioms apeOn_central

/-- **A centre-valued configuration is fixed by the observer flow**, at every number of steps and
every box.

DERIVED: `1/6` the dominance bound. -/
theorem obsFlow_central {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) {U : IConf G2}
    (hU : ∀ l, IsCentral (U l)) : obsFlow c hc0 hc n R U = U := by
  funext l
  show (apeOn c hc0 hc (mbox l R))^[n] U l = U l
  rw [Function.iterate_fixed (apeOn_central hc0 hc hU _) n]

#print axioms obsFlow_central

/-- **The centre element `−1` of `SU(2)`.**

DERIVED: `2` is the rank; `-1` the centre element. -/
def negOne : MassGap.SUN.SU 2 :=
  ⟨-1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      simp
    · rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
      norm_num⟩

/-- DERIVED: `2` is the rank; `-1` the centre element. -/
theorem central_negOne : IsCentral negOne :=
  ⟨-1, Or.inr rfl, by
    show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = ((-1 : ℝ) : ℂ) • 1
    simp⟩

/-- DERIVED: `2` is the rank; `1` the identity. -/
theorem central_one : IsCentral (1 : MassGap.SUN.SU 2) :=
  ⟨1, Or.inl rfl, by
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) = ((1 : ℝ) : ℂ) • 1
    simp⟩

/-- DERIVED: `2` is the rank; `-1` the centre element. -/
theorem negOne_inv : negOne⁻¹ = negOne :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by
    show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1
    simp))

/-- **The plaquette density as a local gauge-invariant field**: the Wilson density of the plaquette
holonomy, local on the plaquette's links, gauge invariant because the density is a class function.

DERIVED: no numeral. -/
noncomputable def plaqField {N : ℕ} (q : MassGap.GibbsSpec.IPlaq) : LField (MassGap.SUN.SU N) :=
  ⟨GaugeInvariantAlgebra.iplaqObs q,
    ⟨(MassGap.GibbsSpec.ilinks q).toFinset, fun U V h => by
      show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q U)
        = MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q V)
      rw [MassGap.GibbsSpec.ihol_congr q U V (fun l hl => h l (List.mem_toFinset.mpr hl))]⟩,
    GaugeInvariantAlgebra.isIGaugeInvariant_of_classFun
      (fun h k => MassGap.WilsonAction.wilsonDensity_conj h k) q (fun _ => rfl)⟩

/-- The plaquette in the `(0, 1)` plane at the origin.

DERIVED: `0` and `1` are the first two directions; `0` the origin. -/
def q0 : MassGap.GibbsSpec.IPlaq := ((0, 1), 0)

/-- The configuration with the single link `(0, e₁)` at `−1` and every other link at `1`.

DERIVED: `0` the direction and the origin; `1` the step to the link's base; `-1` the centre. -/
def Utw : IConf G2 := fun l =>
  if l = ((0 : Fin 4), MassGap.GibbsSpec.ishift 1 (0 : ISite)) then negOne else 1

/-- DERIVED: `1` the identity. -/
theorem central_flat : ∀ l : ILink, IsCentral ((fun _ => (1 : G2)) l) := fun _ => central_one

/-- DERIVED: `-1` the centre element. -/
theorem central_tw : ∀ l : ILink, IsCentral (Utw l) := by
  intro l
  unfold Utw
  split_ifs
  · exact central_negOne
  · exact central_one

/-- **The plaquette density reads `0` on the flat configuration.**

DERIVED: `2` is the rank; `0` the density of the identity. -/
theorem plaq_flat : (plaqField (N := 2) q0).1 (fun _ => 1) = 0 := by
  show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q0 (fun _ => (1 : G2))) = 0
  have : MassGap.GibbsSpec.ihol q0 (fun _ => (1 : G2)) = 1 := by
    simp [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd]
  rw [this]
  exact MassGap.WilsonAction.wilsonDensity_one two_ne

#print axioms plaq_flat

/-- **The plaquette density reads `2` on the configuration with one `−1` link.** The plaquette at the
origin in the `(0, 1)` plane reads that link once, so its holonomy is `−1`, of density
`1 − ½ Re tr(−1) = 2`.

DERIVED: `2` is the rank and the density of `−1`; `0`, `1` the plane and the origin. -/
theorem plaq_tw : (plaqField (N := 2) q0).1 Utw = 2 := by
  show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q0 Utw) = 2
  have h0 : ¬ ((0 : ISite) = MassGap.GibbsSpec.ishift 1 (0 : ISite)) := by
    intro h
    have := congrFun h 1
    simp [MassGap.GibbsSpec.ishift] at this
  have hf : ¬ ((1 : Fin 4) = 0) := by decide
  have hhol : MassGap.GibbsSpec.ihol q0 Utw = negOne := by
    simp [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd, q0, Utw,
      h0, hf, negOne_inv]
  rw [hhol]
  unfold MassGap.WilsonAction.wilsonDensity
  have : ((negOne : MassGap.SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl
  rw [this, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin, Complex.neg_re,
    Complex.natCast_re]
  norm_num

#print axioms plaq_tw

end NoCap

/-! ## 7. The moments from the zoom -/

section Zoom

variable {N : ℕ}

/-- **The zoom band of one field**: there is a summable `δ ≥ 0` with
`ν_{k+1}((Φ_{k+1} O)^{2p}) ≤ e^{δ_k} ν_k((Φ_k O)^{2p})` for every `p` and `k`. The flowed field's
single-site law at one substrate dominates the next one's up to the factor `e^{δ_k}` on every even
power: the form a density band `dP'/dP ≤ e^{D}` takes on the even moments, with a summable budget.

DERIVED: `0` is the excluded colour count and the sign of `δ`; `1` the next step; `2` makes the power
even. -/
def ZoomBandAt (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ δ : ℕ → ℝ, Summable δ ∧ (∀ k, 0 ≤ δ k) ∧ ∀ (p k : ℕ),
    stateK hN (k + 1) ((Φ.map (k + 1) O).1 ^ (2 * p))
      ≤ Real.exp (δ k) * stateK hN k ((Φ.map k O).1 ^ (2 * p))

/-- **The zoom band bounds every moment uniformly**: `ν_k((Φ_k O)^{2p}) ≤ e^{∑ δ} ν_0((Φ_0 O)^{2p})` at
every step. The step-`0` field is a continuous function on a compact space, so the right side is finite.

DERIVED: `0` is the excluded colour count and the first step; `2` makes the power even. -/
theorem moments_of_zoomBandAt (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N))
    (h : ZoomBandAt hN Φ O) (p : ℕ) :
    ∃ C : ℝ, ∀ᶠ k in atTop, stateK hN k ((Φ.map k O).1 ^ (2 * p)) ≤ C := by
  obtain ⟨δ, hsum, hδ0, hstep⟩ := h
  have hnn : ∀ k, 0 ≤ stateK hN k ((Φ.map k O).1 ^ (2 * p)) := fun k =>
    (stateK hN k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _)
  have hind : ∀ k, stateK hN k ((Φ.map k O).1 ^ (2 * p))
      ≤ Real.exp (∑ i ∈ Finset.range k, δ i) * stateK hN 0 ((Φ.map 0 O).1 ^ (2 * p)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc stateK hN (k + 1) ((Φ.map (k + 1) O).1 ^ (2 * p))
          ≤ Real.exp (δ k) * stateK hN k ((Φ.map k O).1 ^ (2 * p)) := hstep p k
        _ ≤ Real.exp (δ k) * (Real.exp (∑ i ∈ Finset.range k, δ i)
              * stateK hN 0 ((Φ.map 0 O).1 ^ (2 * p))) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (∑ i ∈ Finset.range (k + 1), δ i) * stateK hN 0 ((Φ.map 0 O).1 ^ (2 * p)) := by
            rw [Finset.sum_range_succ, Real.exp_add]
            ring
  refine ⟨Real.exp (∑' i, δ i) * stateK hN 0 ((Φ.map 0 O).1 ^ (2 * p)),
    Filter.Eventually.of_forall (fun k => (hind k).trans ?_)⟩
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (hsum.sum_le_tsum _ (fun i _ => hδ0 i))) (hnn 0)

#print axioms moments_of_zoomBandAt

/-- **The uniform bound from the zoom**: a zoom band for every field gives `UniformBoundF`.

DERIVED: `0` is the excluded colour count. -/
theorem uniformBoundF_of_zoomBand (hN : N ≠ 0) (Φ : Flow N)
    (h : ∀ O : LField (MassGap.SUN.SU N), ZoomBandAt hN Φ O) : UniformBoundF hN Φ :=
  uniformBoundF_of_momentBound hN Φ (fun O p => moments_of_zoomBandAt hN Φ O (h O) p)

#print axioms uniformBoundF_of_zoomBand

/-- **The class-scaled flow from the zoom on its class**: a zoom band for every field of `D` gives
`FlowMomentBound` for `energyOn W D`; off `D` the field is bounded by `‖O‖`.

DERIVED: `0` is the excluded colour count; `1` the unit observable; `2` makes the power even. -/
theorem flowMomentBound_energyOn_of_zoomBand (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (h : ∀ O ∈ D, ZoomBandAt hN (energyOn W D hD s hs) O) :
    FlowMomentBound hN (energyOn W D hD s hs) := by
  intro O p
  by_cases hO : O ∈ D
  · exact moments_of_zoomBandAt hN _ O (h O hO) p
  · refine ⟨‖O.1‖ ^ (2 * p), Filter.Eventually.of_forall (fun k => ?_)⟩
    show stateK hN k ((zOn D k O • ((W.fieldMap k O).1 - sOn D s k O • (1 : C(Cfg N, ℝ))))
      ^ (2 * p)) ≤ _
    rw [zOn_of_not_mem hO, sOn_of_not_mem hO, zero_smul, sub_zero, one_smul]
    calc stateK hN k ((W.fieldMap k O).1 ^ (2 * p))
        ≤ stateK hN k (‖O.1‖ ^ (2 * p) • (1 : C(Cfg N, ℝ))) := (stateK hN k).mono (fun U => by
          rw [ContinuousMap.pow_apply]
          simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
          have hU : |(W.fieldMap k O).1 U| ≤ ‖O.1‖ := by
            have := O.1.norm_coe_le_norm (W.V k U)
            rw [Real.norm_eq_abs] at this
            exact this
          rw [← (even_two_mul p).pow_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hU _)
      _ = ‖O.1‖ ^ (2 * p) := by rw [(stateK hN k).map_smul, (stateK hN k).map_one, mul_one]

#print axioms flowMomentBound_energyOn_of_zoomBand

/-- **E for the class-scaled observer from the zoom on its class.**

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
theorem uniformBoundF_energyOn_of_zoomBand {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (h : ∀ O ∈ D, ZoomBandAt two_ne (obsEnergyOn c hc0 hc n R D hD s hs) O) :
    UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs) :=
  uniformBoundF_of_momentBound two_ne _
    (flowMomentBound_energyOn_of_zoomBand two_ne (obsConfFlow c hc0 hc n R) D hD s hs h)

#print axioms uniformBoundF_energyOn_of_zoomBand

end Zoom

/-! ## 8. The uniform bound from the moments of smeared fields -/

section Smeared

variable {N : ℕ}

/-- **The smeared moment bound of a flow**: for every local field `O`, every test function `f` and
every `p`, the even moment `ν_k((smear a_k (Φ_k O) f)^{2p})` of the smeared flowed field is bounded
eventually in the step. The field is read over the physical support of `f`, not at one site.

DERIVED: `0` is the excluded colour count; `2` makes the power even. -/
def SmearedMomentBound (hN : N ≠ 0) (Φ : Flow N) : Prop :=
  ∀ (O : LField (MassGap.SUN.SU N)) (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
    stateK hN k (smear (dySpacing N k) (Φ.map k O).1 f ^ (2 * p)) ≤ C

/-- **Translating the test function does not change a smeared moment**: `stateK` is invariant under
the lattice translations (`ContinuumNontrivial.stateK_transObs`).

DERIVED: `0` is the excluded colour count and the sign of the spacing; `2` makes the power even. -/
theorem smear_moment_translate (hN : N ≠ 0) (k : ℕ) (G : C(Cfg N, ℝ)) (f : TestFn) (v : ISite)
    (q : ℕ) :
    stateK hN k (smear (dySpacing N k) G (f.translate (site (dySpacing N k) v)) ^ q)
      = stateK hN k (smear (dySpacing N k) G f ^ q) := by
  rw [smear_translate (dySpacing_pos (one_le_of_ne_zero hN) k), ← transObs_pow,
    ContinuumNontrivial.stateK_transObs]

#print axioms smear_moment_translate

/-- **The uniform bound from the smeared moments.** `SmearedMomentBound hN Φ` gives
`ContinuumFlow.UniformBoundF hN Φ`: for a family of `n` fields the constant is `1 + ∑ᵢ Cᵢ`, `Cᵢ` the
eventual bound on the `2n`-th moment of the `i`-th smeared flowed field; translations are free by the
translation invariance of `stateK`.

DERIVED: `0` is the excluded colour count; `1` and `2` are `abs_prod_le_one_add_sum_pow`'s. -/
theorem uniformBoundF_of_smearedMomentBound (hN : N ≠ 0) (Φ : Flow N)
    (h : SmearedMomentBound hN Φ) : UniformBoundF hN Φ := by
  intro ι _ F
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) (Φ.map k (F i).1).1 (F i).2 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => h (F i).1 (F i).2 (Fintype.card ι)
  choose C hC using hC
  refine ⟨1 + ∑ i, C i, fun m n => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop m, Filter.eventually_all.mpr hC] with k hk hCk
  have hfam : (fun i => Φ.field k ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))
      = (fun i => ((Φ.field k (F i)).1, (Φ.field k (F i)).2.translate
          (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))) := by
    funext i
    show (Φ.map k (F i).1, (F i).2.translate (site (dySpacing N m) (n i)))
      = (Φ.map k (F i).1, (F i).2.translate (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))
    rw [site_dySpacing N hk]
  show |latSk hN k (fun i => Φ.field k ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))|
    ≤ _
  rw [latSk_eq, hfam]
  show |stateK hN k (∏ i, smear (dySpacing N k) (Φ.map k (F i).1).1
      ((F i).2.translate (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i)))))| ≤ _
  set S : ι → C(Cfg N, ℝ) := fun i => smear (dySpacing N k) (Φ.map k (F i).1).1
      ((F i).2.translate (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i)))) with hS
  have hpt := abs_state_le_of_abs_le (stateK hN k) (∏ i, S i)
    (1 + ∑ i, S i ^ (2 * Fintype.card ι))
    (fun U => by
      simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.sum_apply,
        ContinuousMap.prod_apply, ContinuousMap.pow_apply]
      exact abs_prod_le_one_add_sum_pow _)
  rw [(stateK hN k).map_add, (stateK hN k).map_one, (stateK hN k).map_sum] at hpt
  refine hpt.trans (add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ?_)))
  rw [hS]
  simp only
  rw [smear_moment_translate hN k]
  exact hCk i

#print axioms uniformBoundF_of_smearedMomentBound

/-- **The smeared moments of a bounded field**: at `0 < a ≤ 1`, `ν((smear a G f)^{2p}) ≤
(B M (2R + 3)⁴)^{2p}` when `‖G‖ ≤ B` (`ContinuumField.norm_smear_le`).

DERIVED: `0` is the sign of `a`; `1` bounds `a`; `2`, `3`, `4` are `norm_smear_le`'s and the even
power's. -/
theorem smear_moment_le_of_norm (ν : MassGap.DLRLimit.State (Cfg N)) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (G : C(Cfg N, ℝ)) {B : ℝ} (hG : ‖G‖ ≤ B) (f : TestFn) {R M : ℝ}
    (hf : IsTest f.1 R M) (p : ℕ) :
    ν (smear a G f ^ (2 * p)) ≤ (B * (M * (2 * R + 3) ^ 4)) ^ (2 * p) := by
  have hn := (norm_smear_le ha ha1 G f hf).trans
    (mul_le_mul_of_nonneg_right hG (mul_nonneg hf.M_nonneg (by have := hf.1; positivity)))
  calc ν (smear a G f ^ (2 * p))
      ≤ ν ((B * (M * (2 * R + 3) ^ 4)) ^ (2 * p) • (1 : C(Cfg N, ℝ))) := ν.mono (fun U => by
        rw [ContinuousMap.pow_apply]
        simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
        have hU : |smear a G f U| ≤ B * (M * (2 * R + 3) ^ 4) := by
          have := (smear a G f).norm_coe_le_norm U
          rw [Real.norm_eq_abs] at this
          exact this.trans hn
        rw [← (even_two_mul p).pow_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hU _)
    _ = (B * (M * (2 * R + 3) ^ 4)) ^ (2 * p) := by rw [ν.map_smul, ν.map_one, mul_one]

#print axioms smear_moment_le_of_norm

/-- **The smeared moment bound of the class-scaled flow** needs the smeared moments on `D` only: off
`D` the flowed field `O ∘ V_k` is bounded by `‖O‖`, and its smeared field by `‖O‖ M (2R + 3)⁴` once the
spacing is below one.

DERIVED: `0` is the excluded colour count; `1` the unit observable and the spacing bound; `2` makes the
power even. -/
theorem smearedMomentBound_energyOn (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (h : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) ((energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C) :
    SmearedMomentBound hN (energyOn W D hD s hs) := by
  intro O f p
  by_cases hO : O ∈ D
  · exact h O hO f p
  · obtain ⟨R, M, hf⟩ := f.2
    refine ⟨(‖O.1‖ * (M * (2 * R + 3) ^ 4)) ^ (2 * p), ?_⟩
    filter_upwards [(tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk1
    have hG : ‖((energyOn W D hD s hs).map k O).1‖ ≤ ‖O.1‖ := by
      show ‖zOn D k O • ((W.fieldMap k O).1 - sOn D s k O • (1 : C(Cfg N, ℝ)))‖ ≤ ‖O.1‖
      rw [zOn_of_not_mem hO, sOn_of_not_mem hO, zero_smul, sub_zero, one_smul]
      exact (ContinuousMap.norm_le _ (norm_nonneg O.1)).mpr
        (fun U => O.1.norm_coe_le_norm (W.V k U))
    exact smear_moment_le_of_norm (stateK hN k) (dySpacing_pos (one_le_of_ne_zero hN) k) hk1.le
      _ hG f hf p

#print axioms smearedMomentBound_energyOn

/-- **The class-scaled observer's continuum statement from smeared moments on the class.** For the
localised APE observer scaled by `a⁻⁴` on a reflection-closed class `D`: bounded smeared moments of
every field of `D`, a physical range bound, absolute clustering at a window `L > 0` and one non-zero
connected pairing give, at every dyadic step, the reconstructed transfer gapped at physical rate `c'/L`
on a space with a non-zero vector orthogonal to the vacuum.

DERIVED: `2` is the rank and makes the power even; `0` the lower end of `L` and `c'`; `1/6` the
dominance bound. -/
theorem observer_energyOn_clay_of_smearedMoments {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6)
    (n R : ℕ → ℕ) (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK two_ne k (smear (dySpacing 2 k)
        ((obsEnergyOn c hc0 hc n R D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) {L : ℝ}
    (hL : 0 < L) (hcl : FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L)
    (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  flow_clay_of_abs_cluster two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
    (uniformBoundF_of_smearedMomentBound two_ne _
      (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) hL hcl hNT

#print axioms observer_energyOn_clay_of_smearedMoments

/-- **A sequence within a summable factor of its predecessor is bounded**: `0 ≤ x`,
`x_{k+1} ≤ e^{δ_k} x_k` with `δ ≥ 0` summable give `x_k ≤ e^{∑ δ} x_0`.

DERIVED: `0` is the sign and the first index; `1` the next index. -/
theorem le_of_zoomRatio (x δ : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k) (hsum : Summable δ)
    (hδ0 : ∀ k, 0 ≤ δ k) (hstep : ∀ k, x (k + 1) ≤ Real.exp (δ k) * x k) (k : ℕ) :
    x k ≤ Real.exp (∑' i, δ i) * x 0 := by
  have hind : ∀ k, x k ≤ Real.exp (∑ i ∈ Finset.range k, δ i) * x 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x (k + 1) ≤ Real.exp (δ k) * x k := hstep k
        _ ≤ Real.exp (δ k) * (Real.exp (∑ i ∈ Finset.range k, δ i) * x 0) :=
            mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (∑ i ∈ Finset.range (k + 1), δ i) * x 0 := by
            rw [Finset.sum_range_succ, Real.exp_add]; ring
  exact (hind k).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (hsum.sum_le_tsum _ (fun i _ => hδ0 i))) (hx 0))

#print axioms le_of_zoomRatio

/-- **The smeared zoom band of one field and one test function**: a summable `δ ≥ 0` with
`ν_{k+1}((smear a_{k+1} (Φ_{k+1} O) f)^{2p}) ≤ e^{δ_k} ν_k((smear a_k (Φ_k O) f)^{2p})` for every `p`
and `k`: the observer's reading over the physical support of `f` has the same moments at successive
substrates up to a summable factor.

DERIVED: `0` is the excluded colour count and the sign of `δ`; `1` the next step; `2` makes the power
even. -/
def SmearedZoomBand (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) (f : TestFn) : Prop :=
  ∃ δ : ℕ → ℝ, Summable δ ∧ (∀ k, 0 ≤ δ k) ∧ ∀ (p k : ℕ),
    stateK hN (k + 1) (smear (dySpacing N (k + 1)) (Φ.map (k + 1) O).1 f ^ (2 * p))
      ≤ Real.exp (δ k) * stateK hN k (smear (dySpacing N k) (Φ.map k O).1 f ^ (2 * p))

/-- **The smeared zoom band bounds every smeared moment uniformly.**

DERIVED: `0` is the excluded colour count and the first step; `2` makes the power even. -/
theorem smearedMoments_of_zoomBand (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N))
    (f : TestFn) (h : SmearedZoomBand hN Φ O f) (p : ℕ) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k) (Φ.map k O).1 f ^ (2 * p)) ≤ C := by
  obtain ⟨δ, hsum, hδ0, hstep⟩ := h
  exact ⟨_, Filter.Eventually.of_forall (le_of_zoomRatio
    (fun k => stateK hN k (smear (dySpacing N k) (Φ.map k O).1 f ^ (2 * p))) δ
    (fun k => (stateK hN k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _))
    hsum hδ0 (hstep p))⟩

#print axioms smearedMoments_of_zoomBand

/-- **E for the class-scaled observer from the smeared zoom on its class.**

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
theorem uniformBoundF_energyOn_of_smearedZoomBand {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6)
    (n R : ℕ → ℕ) (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (h : ∀ O ∈ D, ∀ f : TestFn, SmearedZoomBand two_ne (obsEnergyOn c hc0 hc n R D hD s hs) O f) :
    UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs) :=
  uniformBoundF_of_smearedMomentBound two_ne _
    (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs
      (fun O hO f p => smearedMoments_of_zoomBand two_ne _ O f (h O hO f) p))

#print axioms uniformBoundF_energyOn_of_smearedZoomBand

end Smeared

end MassGap.ObserverEnergyMoments
