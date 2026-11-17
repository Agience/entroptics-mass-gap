import Mathlib
import MassGap.OpenAIBridgeNearCubic

/-!
# MassGap.OpenAIBridgeShortMom — the reflected moment of a dominated insertion

For a nonnegative symmetric transfer kernel `k` and an insertion dominated by a power of it,
`|F| ≤ B k^{∗(m+1)}`, the reflected torus moment is at most `B²` on every torus long enough to hold
the insertion and its reflection:

    |E_L[f · θf]| = |Tr(F K^{2a+2} Fᵀ K^{2b+2})| / Tr K^{L} ≤ B²,   L = 2(m + a + b + 3).

The domination passes through each composition (`abs_conv_iter_le`, `abs_conv_dom_le`) and the
trace (`abs_trc_le_dom`), so the numerator is at most `B²` times the trace of the full power
(`abs_trK_le_dom`). The bound holds for every volume and every shortening in time.

* `iter_nonneg_of` — powers of a nonnegative kernel are nonnegative.
* `abs_trK_le_dom` — `|Tr(F R^{p+1} G R^{q+1})| ≤ A B Tr R^{…}` for dominated `F`, `G`.
* `abs_torusMom_le` — the reflected moment of a dominated insertion is at most `B²`.
* `abs_torusMom_slab_le` — the slab insertions of `OpenAIBridgeSlab.slabKer` with `|G| ≤ B`.
* `thermRem_nearCubic_dom` — the thermal remainder on near-cubic tori below
  `(1/2)^{2⌊√⌊m/n⌋⌋} · 2B²`.

The bound `B` bounds the insertion's integrand; its uniformity in the spacing is an input.
-/

namespace MassGap.OpenAIBridgeShortMom

open MeasureTheory Real
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCubic
  MassGap.OpenAIBridgeThermal MassGap.OpenAIBridgeNearCubic

section Moment

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Powers of a nonnegative kernel are nonnegative.

DERIVED: `0` is the sign. -/
theorem iter_nonneg_of {k : X → X → ℝ} (hk0 : ∀ x y, 0 ≤ k x y) :
    ∀ (m : ℕ) (x y : X), 0 ≤ iter μ k m x y
  | 0, x, y => hk0 x y
  | m + 1, x, y => by
    show 0 ≤ ∫ z, k x z * iter μ k m z y ∂μ
    exact integral_nonneg fun z => mul_nonneg (hk0 x z) (iter_nonneg_of hk0 m z y)

omit [IsProbabilityMeasure μ] in
/-- A power of a nonnegative kernel is its own absolute value.

DERIVED: no numeral appears in the statement. -/
theorem abs_iter_eq {k : X → X → ℝ} (hk0 : ∀ x y, 0 ≤ k x y) (m : ℕ) :
    (fun x y => |iter μ k m x y|) = iter μ k m := by
  funext x y
  exact abs_of_nonneg (iter_nonneg_of hk0 m x y)

/-- **A dominated insertion composed with a power**: `|F| ≤ A k^{∗(mF+1)}` gives
`|F ∗ k^{∗(p+1)}| ≤ A k^{∗(mF+p+2)}`.

DERIVED: `1` is the offset of `iter`; `0` the sign of the kernel. -/
theorem abs_conv_iter_le {k F : X → X → ℝ} (hk : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y) (hF : Bdd F)
    {A : ℝ} {mF : ℕ} (hFd : ∀ x y, |F x y| ≤ A * iter μ k mF x y) (p : ℕ) (x z : X) :
    |conv μ F (iter μ k p) x z| ≤ A * iter μ k (mF + p + 1) x z := by
  have h := abs_conv_le_left (μ := μ) hF (hk.iter (μ := μ) p) (hk.iter (μ := μ) mF) hFd x z
  rw [abs_iter_eq hk0, ← iter_add hk] at h
  exact h

/-- **Two dominated kernels composed**: `|P| ≤ A k^{∗(a+1)}`, `|Q| ≤ B k^{∗(b+1)}` and `A ≥ 0` give
`|P ∗ Q| ≤ A B k^{∗(a+b+2)}`.

DERIVED: `1` is the offset of `iter`; `0` the signs. -/
theorem abs_conv_dom_le {k P Q : X → X → ℝ} (hk : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y) (hP : Bdd P)
    (hQ : Bdd Q) {A B : ℝ} (hA : 0 ≤ A) {a b : ℕ} (hPd : ∀ x y, |P x y| ≤ A * iter μ k a x y)
    (hQd : ∀ x y, |Q x y| ≤ B * iter μ k b x y) (x z : X) :
    |conv μ P Q x z| ≤ A * (B * iter μ k (a + b + 1) x z) := by
  have h1 := abs_conv_le_left (μ := μ) hP hQ (hk.iter (μ := μ) a) hPd x z
  have h2 := abs_conv_le_right (μ := μ) (bdd_abs hQ) (hk.iter (μ := μ) a) (hk.iter (μ := μ) b)
    (fun x y => by rw [abs_abs]; exact hQd x y) x z
  rw [abs_iter_eq hk0, ← iter_add hk] at h2
  exact h1.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hA)

/-- **The trace of a dominated kernel**: `|M| ≤ A P` gives `|trc M| ≤ A trc P`.

DERIVED: no numeral appears in the statement. -/
theorem abs_trc_le_dom {M P : X → X → ℝ} (hM : Bdd M) (hP : Bdd P) {A : ℝ}
    (h : ∀ x z, |M x z| ≤ A * P x z) : |trc μ M| ≤ A * trc μ P := by
  obtain ⟨CM, hCM⟩ := hM.bdd
  obtain ⟨CP, hCP⟩ := hP.bdd
  have hd : Measurable (fun x : X => (x, x)) := measurable_id.prodMk measurable_id
  unfold trc
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono ?_ ?_ (fun x => h x x))
  · exact (integrable_of_bdd (f := fun x => M x x) (hM.meas.comp hd) (C := CM)
      (fun x => hCM x x)).abs
  · refine integrable_of_bdd (f := fun x => A * P x x) (measurable_const.mul (hP.meas.comp hd))
      (C := |A| * CP) (fun x => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hCP x x) (abs_nonneg _)

/-- **The reflected numerator of dominated insertions**: `|F| ≤ A k^{∗(mF+1)}`,
`|G| ≤ B k^{∗(mG+1)}` and `A ≥ 0` give
`|Tr(F K^{p+1} G K^{q+1})| ≤ A B Tr K^{mF+p+mG+q+4}`.

DERIVED: `1` is the offset of `iter`, so the power is `(mF + p + 1) + (mG + q + 1) + 1` plus the
offset; `0` the signs. -/
theorem abs_trK_le_dom {k F G : X → X → ℝ} (hk : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y) (hF : Bdd F)
    (hG : Bdd G) {A B : ℝ} (hA : 0 ≤ A) {mF mG : ℕ}
    (hFd : ∀ x y, |F x y| ≤ A * iter μ k mF x y) (hGd : ∀ x y, |G x y| ≤ B * iter μ k mG x y)
    (p q : ℕ) :
    |trK μ k F G p q| ≤ A * B * trPow μ k (mF + p + 1 + (mG + q + 1) + 1) := by
  have hX := hF.conv (μ := μ) (hk.iter (μ := μ) p)
  have hY := hG.conv (μ := μ) (hk.iter (μ := μ) q)
  have h := abs_conv_dom_le hk hk0 hX hY hA (abs_conv_iter_le hk hk0 hF hFd p)
    (abs_conv_iter_le hk hk0 hG hGd q)
  exact abs_trc_le_dom (hX.conv hY) (hk.iter (μ := μ) _) (fun x z => by rw [mul_assoc]; exact h x z)

/-- **The reflected moment of a dominated insertion is at most `B²`**: for a nonnegative symmetric
bounded `k`, `B ≥ 0` and `|F| ≤ B k^{∗(m+1)}`, on the torus of `2(m + a + b + 3)` steps,

    |torusMom μ k F a b (m + a + b + 2)| ≤ B².

`Fᵀ` has the same domination (`tp_iter`), `abs_trK_le_dom` bounds the numerator by `B²` times the
trace of `k^{∗2(m+a+b+3)}`, which is the denominator, and the denominator is nonnegative.

DERIVED: `2` is the square and the offset `a + b + 2`; `0` the signs. -/
theorem abs_torusMom_le {k F : X → X → ℝ} (hk : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y)
    (hsym : ∀ x y, k x y = k y x) (hF : Bdd F) {B : ℝ} (hB : 0 ≤ B) {m : ℕ}
    (hFd : ∀ x y, |F x y| ≤ B * iter μ k m x y) (a b : ℕ) :
    |torusMom μ k F a b (m + a + b + 2)| ≤ B ^ 2 := by
  have hFt : ∀ x y, |tp F x y| ≤ B * iter μ k m x y := fun x y => by
    have e := congrFun (congrFun (tp_iter (μ := μ) hk hsym m) x) y
    show |F y x| ≤ _
    rw [← e]
    exact hFd y x
  have h := abs_trK_le_dom hk hk0 hF (bdd_tp hF) hB hFd hFt (a + a + 1) (b + b + 1)
  have hidx : m + (a + a + 1) + 1 + (m + (b + b + 1) + 1) + 1
      = m + a + b + 2 + (m + a + b + 2) + 1 := by omega
  rw [hidx] at h
  have hT0 : 0 ≤ trPow μ k (m + a + b + 2 + (m + a + b + 2) + 1) :=
    integral_nonneg fun x => iter_nonneg_of hk0 _ x x
  unfold torusMom
  rw [abs_div, abs_of_nonneg hT0]
  rcases hT0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  · rw [div_le_iff₀ hpos, sq]; exact h

end Moment

/-! ## Slab insertions -/

section Slab

open HiddenChain

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {w : X → Y → X → ℝ}

/-- **The reflected moment of a slab insertion is at most `B²`**: for nonnegative bounded step
weights with symmetric `k = HiddenChain.kern ν w` and an integrand `|G| ≤ B`, the insertion
`slabKer μ ν w m G` over `m + 1` steps has

    |torusMom μ k (slabKer m G) a b (m + a + b + 2)| ≤ B²

on every torus of `2(m + a + b + 3)` steps (`slabKer_le_iter`, `abs_torusMom_le`).

DERIVED: `2` is the square and the offset of the window; `0` the signs. -/
theorem abs_torusMom_slab_le (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C)
    (hw0 : ∀ x a y, 0 ≤ w x a y) (hsym : ∀ x y, kern ν w x y = kern ν w y x) (m : ℕ)
    {G : (ℕ → X) → (ℕ → Y) → ℝ} (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2))
    {B : ℝ} (hB : 0 ≤ B) (hGb : ∀ V A, |G V A| ≤ B) (a b : ℕ) :
    |torusMom μ (kern ν w) (slabKer μ ν w m G) a b (m + a + b + 2)| ≤ B ^ 2 :=
  abs_torusMom_le (bdd_kern (ν := ν) hw hwb) (fun x y => integral_nonneg fun a => hw0 x a y) hsym
    (bdd_slabKer (μ := μ) (ν := ν) hw hwb m hG hGb) hB (slabKer_le_iter hw hwb hw0 m hGb) a b

end Slab

/-! ## The thermal remainder of a dominated insertion -/

section Shorten

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

variable (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) {n : ℕ}
  (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖
      ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖)

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The thermal remainder of a dominated insertion on near-cubic tori**: for a nonnegative `k`,
an insertion `|F| ≤ B k^{∗(m'+1)}` over `w = m' + 1` steps and the window data of
`OpenAIBridgeNearCubic.thermRem_nearCubic_slab`,

    D_L(f; p + 1, p' + q' + 1) ≤ (1/2)^{2⌊√⌊m/n⌋⌋} · 2B².

`thermRem_nearCubic_slab` bounds the remainder by the reflected moment on the shortened torus and
`abs_torusMom_le` bounds that moment by `B²`.

DERIVED: `4` and `8` are the slab condition, `4` also the offsets `2 + 2` of the two separations;
`3` the window exponent; `1/2` the contraction; `2` the doubled half-side, the squares and the bound
`1 + σ₀' ≤ 2`; `1` the least `j0`, the offsets of `iter` and `q' + 1`, and `w = m' + 1`; `0` the
signs. -/
theorem thermRem_nearCubic_dom (hc0 : c ≠ 0) (hn : 0 < n) (hk0 : ∀ x y, 0 ≤ k x y)
    {F : X → X → ℝ} (hF : Bdd F) {B : ℝ} (hB : 0 ≤ B) {m' : ℕ}
    (hFd : ∀ x y, |F x y| ≤ B * iter μ k m' x y)
    {a j0 : ℕ} (hj0 : 1 ≤ j0) (p p' q' m : ℕ) (hL4 : 2 * (2 * j0) ≤ 2 * m)
    (hhi : 2 * m ≤ 2 ^ (a + 3) * n) (hexc : excited μ k c φ j0 ≤ (1 / 2) ^ (2 ^ a))
    (hm : m' + 1 + p + p' + q' + 4 = m) (hW : 4 * (2 * q' + 4) + 8 * n ≤ 2 * m)
    (hq : q' + 1 = shortSteps n m) :
    thermRem μ k c φ F (m' + 1) (p + 1) (p' + q' + 1)
      ≤ ((1 / 2) ^ Nat.sqrt (m / n)) ^ 2 * (2 * B ^ 2) := by
  have h := thermRem_nearCubic_slab hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hn hF hj0
    (m' + 1) p p' q' m hL4 hhi hexc hm hW hq
  have e : m' + 1 + p + p' + 1 = m' + p + p' + 2 := by omega
  rw [e] at h
  have hT := abs_torusMom_le (μ := μ) ⟨hkm, C, hkb⟩ hk0 hsym hF hB hFd p p'
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith [le_abs_self (torusMom μ k F p p' (m' + p + p' + 2))]

end Shorten

end MassGap.OpenAIBridgeShortMom

#print axioms MassGap.OpenAIBridgeShortMom.iter_nonneg_of
#print axioms MassGap.OpenAIBridgeShortMom.abs_iter_eq
#print axioms MassGap.OpenAIBridgeShortMom.abs_conv_iter_le
#print axioms MassGap.OpenAIBridgeShortMom.abs_conv_dom_le
#print axioms MassGap.OpenAIBridgeShortMom.abs_trc_le_dom
#print axioms MassGap.OpenAIBridgeShortMom.abs_trK_le_dom
#print axioms MassGap.OpenAIBridgeShortMom.abs_torusMom_le
#print axioms MassGap.OpenAIBridgeShortMom.abs_torusMom_slab_le
#print axioms MassGap.OpenAIBridgeShortMom.thermRem_nearCubic_dom
