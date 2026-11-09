import Mathlib
import MassGap.TorusDoubling
import MassGap.BetaFlow

/-!
# MassGap.LayerSplit — a closed-form anchor at every coupling from the layered torus

The bridge is `CouplingTower.StrongEnd N`: frequently as `β → ∞`, `D(β, w) = windowCoupling N β w → 0` along the
windows `w`. This module gives the layered model an anchor at every `β`, closed form, and states the transport
from the layered model to the Wilson model as a named input. Declarations are in `MassGap.LayerSplit`.

## The layered model (argued geometry, proved bookkeeping)

Give the plaquettes of orientations `(0,1)` and `(2,3)` coupling `β` and the four mixed orientations coupling
`β_⊥`. At `β_⊥ = 0` a link of direction `0` or `1` enters only `(0,1)` plaquettes, and those of directions `2`, `3`
only `(2,3)` plaquettes. The `(0,1)` plaquettes at fixed `(x₂, x₃)` form one 2D torus of side `n`, so the side-`n`
4-torus splits into `n²` independent `(0,1)` tori and `n²` independent `(2,3)` tori, and by Fubini over the product
Haar measure `log Z_n(β, 0) = 2 n² log Z₂(β, n)`, `Z₂ = TorusDoubling.ZT (SU N) 2 wilsonDensity`. The tree's `ZR`
carries one coupling for every orientation, so the anisotropic system is not built here; `logZLayer` is defined
as the right-hand side of the factorization, and the identification of the anisotropic family is part of the
named input `LayerTransport`.

* `layerDefect_eq`: the layered window defect `16 log Z_n − log Z_{2n}` at `n = 2^w` is `8 n² D₂(n)`, with
  `D₂(n) = 4 log Z₂(n) − log Z₂(2n)`. `16 · 2n² = 32 n²` and `2 (2n)² = 8 n²`.

## The 2D torus (cited input, proved consequences)

`TwoDCharacter N β`, cited (Migdal 1975; Rusakov 1990; Drouffe–Zuber 1983, §2): the 2D Wilson torus is
`Z₂(n) = b^{n²} (1 + Σ_{r ≠ 0} m_r a_r^{n²})`, a genus-1 surface (no dimension factors), with `b = λ₀ > 0` the
trivial coefficient of the face weight `e^{−β(φ(U) + φ(U⁻¹))}` (the tree counts each face as two ordered
plaquettes, and the diagonal plaquettes read `φ(1) = 0`), `a_r = λ_r / (d_r λ₀)`, `m_r = 1`. The abstract tail is
`CharTail`: `m_r ≥ 0`, `|a_r| ≤ q < 1`, `Σ m_r |a_r| < ∞`.

* `abs_tail_le`: `|Σ m_r a_r^k| ≤ (Σ m_r |a_r|) q^{k−1}` for `k ≥ 1`.
* `tendsto_mul_tail`: `k · tail(k) → 0`.
* `abs_log_one_add_le`, `tendsto_mul_log`: `k log(1 + tail k) → 0`.
* `closedForm_defect`: `n² (4 log Z(n) − log Z(2n)) → 0` for any `Z` of the closed form; the bulk `b` cancels
  (`4 n² − (2n)² = 0`).
* `layer_vanishes`: under `TwoDCharacter N β`, the layered window defect tends to `0` along the windows, at that
  `β`, whatever its size.

## The transport (named input, proved consequence)

`LayerTransport N`: a family `D(β, β_⊥, w)` equal to the layered defect at `β_⊥ = 0` and to the window coupling at
`β_⊥ = β`, and, frequently as `β → ∞`, differentiable in `β_⊥` on `[0, β]` with BetaFlow's Osgood form in the
variable `β_⊥` (base `0`, a `K` continuous on `[0, ∞)`). `strongEnd_of_layerTransport`: `TwoDCharacter` at every
`β` and `LayerTransport N` give `StrongEnd N`. BetaFlow's obstruction at `β = 0`
(`osgoodFlow_at_zero_trivial`, from `D(0, w) = 0`) does not arise: the layered defect at `β_⊥ = 0` is not
identically `0`.

## U(1) (argued)

For `U(1)` the same character form holds (`a_r = I_r(2β)/I₀(2β)`), so the layered anchor holds for `U(1)` too: the
anchor does not separate the groups. At large `β` and `β_⊥ = β` the 4D `U(1)` theory is in its Coulomb phase
(Guth; Fröhlich–Spencer) and its window coupling stalls (`PhotonStall`), so the transport must fail for `U(1)`.
The non-abelian content sits entirely in `LayerTransport`.
-/

namespace MassGap.LayerSplit

open Filter Topology Set MassGap.CouplingTower

/-! ## 1. The character tail -/

/-- **The tail of a character expansion**: weights `m_r ≥ 0`, normalized coefficients `|a_r| ≤ q < 1`, with
`Σ m_r |a_r|` summable (part of the cited input). DERIVED: `0` the signs; `1` the trivial coefficient `a₀ = 1` that the tail excludes. -/
structure CharTail (ι : Type) where
  m : ι → ℝ
  a : ι → ℝ
  q : ℝ
  m_nonneg : ∀ r, 0 ≤ m r
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  a_le : ∀ r, |a r| ≤ q
  summable : Summable fun r => m r * |a r|

variable {ι : Type}

/-- The tail `Σ_r m_r a_r^k` at area `k`. No numeral. -/
noncomputable def tail (T : CharTail ι) (k : ℕ) : ℝ := ∑' r, T.m r * T.a r ^ k

/-- One term against the summable majorant. DERIVED: `1` the least area. -/
theorem norm_term_le (T : CharTail ι) {k : ℕ} (hk : 1 ≤ k) (r : ι) :
    ‖T.m r * T.a r ^ k‖ ≤ T.m r * |T.a r| * T.q ^ (k - 1) := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (T.m_nonneg r)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have h1 : |T.a r| ^ j ≤ T.q ^ j := pow_le_pow_left₀ (abs_nonneg _) (T.a_le r) j
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (T.m_nonneg r) (abs_nonneg (T.a r)))
  calc T.m r * (|T.a r| ^ j * |T.a r|) = T.m r * |T.a r| * |T.a r| ^ j := by ring
    _ ≤ T.m r * |T.a r| * T.q ^ j := h2

/-- **The tail decays geometrically**: `|tail k| ≤ (Σ m_r |a_r|) q^{k−1}`. DERIVED: `1` the least area. -/
theorem abs_tail_le (T : CharTail ι) {k : ℕ} (hk : 1 ≤ k) :
    |tail T k| ≤ (∑' r, T.m r * |T.a r|) * T.q ^ (k - 1) := by
  rw [← Real.norm_eq_abs]
  exact tsum_of_norm_bounded (T.summable.hasSum.mul_right _) (norm_term_le T hk)

/-- `(j + 1) q^j → 0`. DERIVED: `1` the shift; `0` the limit. -/
theorem tendsto_succ_mul_pow {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Tendsto (fun j : ℕ => ((j : ℝ) + 1) * q ^ j) atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one h0 h1).add (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)
  rw [zero_add] at h
  exact h.congr fun j => by ring

/-- **The area-weighted tail vanishes**: `k · tail k → 0`. DERIVED: `1` the least area and the shift; `0` the
limit. -/
theorem tendsto_mul_tail (T : CharTail ι) :
    Tendsto (fun k : ℕ => (k : ℝ) * tail T k) atTop (𝓝 0) := by
  set S := ∑' r, T.m r * |T.a r|
  have hg : Tendsto (fun k : ℕ => S * ((((k - 1 : ℕ) : ℝ) + 1) * T.q ^ (k - 1))) atTop (𝓝 0) := by
    have h := ((tendsto_succ_mul_pow T.q_nonneg T.q_lt_one).comp (tendsto_sub_atTop_nat 1)).const_mul S
    rw [mul_zero] at h
    exact h
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hb := abs_tail_le T hk
  have hk' : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by rw [Nat.cast_sub hk]; ring
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (k : ℝ) * |tail T k| ≤ k * (S * T.q ^ (k - 1)) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k)
    _ = S * ((((k - 1 : ℕ) : ℝ) + 1) * T.q ^ (k - 1)) := by rw [hk']; ring

/-- The tail itself vanishes. DERIVED: `1` the least area; `0` the limit. -/
theorem tendsto_tail (T : CharTail ι) : Tendsto (tail T) atTop (𝓝 0) := by
  have h := (tendsto_mul_tail T).abs
  rw [abs_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [abs_nonneg (tail T k)]

/-! ## 2. The logarithm -/

/-- **`|log(1 + x)| ≤ 2|x|` on `|x| ≤ 1/2`.** DERIVED: `1/2` keeps `1 + x ≥ 1/2`, and `2` is its inverse. -/
theorem abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x)| ≤ 2 * |x| := by
  have hxl := neg_abs_le x
  have hxu := le_abs_self x
  have hpos : 0 < 1 + x := by linarith
  have hup := Real.log_le_sub_one_of_pos hpos
  have hlo := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (1 + x)⁻¹ * (1 + x) = 1 := inv_mul_cancel₀ hpos.ne'
  have hprod : 1 ≤ (1 + x) * (1 + 2 * |x|) := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, h'⟩ <;> rw [h] <;> nlinarith
  have hy : (1 + x)⁻¹ ≤ 1 + 2 * |x| := by
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul_of_pos_right hlt hpos]
  rw [abs_le]
  constructor <;> linarith

/-- **The area-weighted logarithm vanishes**: `k E(k) → 0` and `E → 0` give `k log(1 + E(k)) → 0`.
DERIVED: `1/2` the range of `abs_log_one_add_le`; `2` its constant; `0` the limit. -/
theorem tendsto_mul_log {E : ℕ → ℝ} (h : Tendsto (fun k : ℕ => (k : ℝ) * E k) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (k : ℝ) * Real.log (1 + E k)) atTop (𝓝 0) := by
  have ha := (h.abs).const_mul 2
  rw [abs_zero, mul_zero] at ha
  refine squeeze_zero_norm' ?_ ha
  filter_upwards [Metric.tendsto_nhds.1 hE (1 / 2) (by norm_num)] with k hk
  rw [Real.dist_eq, sub_zero] at hk
  have hl := abs_log_one_add_le hk.le
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast]
  calc (k : ℝ) * |Real.log (1 + E k)| ≤ k * (2 * |E k|) := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg k)
    _ = 2 * ((k : ℝ) * |E k|) := by ring

/-! ## 3. The closed-form 2D doubling defect -/

/-- **The 2D doubling defect of a closed-form torus vanishes, area-weighted**: if
`Z(n) = b^{n²} (1 + tail(n²))` with `b > 0` for `n ≥ 1`, then `n² (4 log Z(n) − log Z(2n)) → 0`. The bulk `b`
cancels. DERIVED: `4 = 2²` the side-`n` copies in the side-`2n` 2D torus; `2` the doubling; `1` the least side;
`0` the limit. -/
theorem closedForm_defect (T : CharTail ι) {Z : ℕ → ℝ} {b : ℝ} (hb : 0 < b)
    (hZ : ∀ n : ℕ, 1 ≤ n → Z n = b ^ (n ^ 2) * (1 + tail T (n ^ 2))) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (4 * Real.log (Z n) - Real.log (Z (2 * n)))) atTop (𝓝 0) := by
  set F : ℕ → ℝ := fun k => (k : ℝ) * Real.log (1 + tail T k) with hF
  have hFt : Tendsto F atTop (𝓝 0) := tendsto_mul_log (tendsto_mul_tail T) (tendsto_tail T)
  have hsq : Tendsto (fun n : ℕ => n ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hsq2 : Tendsto (fun n : ℕ => (2 * n) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.pow_le_pow_left (by omega) 2) hsq
  have hlim : Tendsto (fun n : ℕ => 4 * F (n ^ 2) - F ((2 * n) ^ 2) / 4) atTop (𝓝 0) := by
    have h := ((hFt.comp hsq).const_mul 4).sub ((hFt.comp hsq2).div_const 4)
    simp only [mul_zero, zero_div, sub_zero] at h
    exact h
  have hpos : ∀ᶠ k in atTop, 0 < 1 + tail T k := by
    filter_upwards [(tendsto_tail T).eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with k hk
    linarith
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hsq.eventually hpos, hsq2.eventually hpos] with n hn h1 h2
  rw [hZ n hn, hZ (2 * n) (by omega), Real.log_mul (pow_ne_zero _ hb.ne') h1.ne',
    Real.log_mul (pow_ne_zero _ hb.ne') h2.ne', Real.log_pow, Real.log_pow]
  simp only [hF]
  push_cast
  ring

/-! ## 4. The 2D Wilson torus and the layered model -/

/-- `log Z₂(n)`, the 2D Wilson torus of the tree (`TorusDoubling.ZT` at `d = 2`). DERIVED: `2` the dimension. -/
noncomputable def logZ2 (N : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  Real.log (TorusDoubling.ZT (SUN.SU N) 2 WilsonAction.wilsonDensity β n)

/-- **The 2D doubling defect** `D₂(n) = 4 log Z₂(n) − log Z₂(2n)`. DERIVED: `4 = 2²` the copies; `2` the
doubling. -/
noncomputable def D2 (N : ℕ) (β : ℝ) (n : ℕ) : ℝ := 4 * logZ2 N β n - logZ2 N β (2 * n)

/-- **`TwoDCharacter N β`, a cited input, not proved here**: the character expansion of the 2D Wilson torus,
genus 1, `Z₂(n) = b^{n²} (1 + Σ_{r≠0} m_r a_r^{n²})` with `b > 0` and a `CharTail`. Cited: Migdal (1975),
Rusakov (1990), Drouffe–Zuber (1983). DERIVED: `2` the dimension; `n²` the faces of the side-`n` 2D torus; `1` the
trivial representation and the least side; `0` the sign. -/
def TwoDCharacter (N : ℕ) (β : ℝ) : Prop :=
  ∃ (ι : Type) (T : CharTail ι) (b : ℝ), 0 < b ∧ ∀ n : ℕ, 1 ≤ n →
    TorusDoubling.ZT (SUN.SU N) 2 WilsonAction.wilsonDensity β n = b ^ (n ^ 2) * (1 + tail T (n ^ 2))

/-- **The 2D defect vanishes, area-weighted**, at every `β` where the character form holds. DERIVED: `2` the
exponent of the area; `0` the limit. -/
theorem twoD_vanishes {N : ℕ} {β : ℝ} (h : TwoDCharacter N β) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * D2 N β n) atTop (𝓝 0) := by
  obtain ⟨ι, T, b, hb, hZ⟩ := h
  exact closedForm_defect T hb hZ

/-- **The layered 4D log-partition function** at `β_⊥ = 0`: `2 n²` independent 2D tori, `n²` per complementary
plane `(0,1)`, `(2,3)` (the Fubini factorization of the module docstring, argued). DERIVED: `2` the complementary
planes; `n²` the transverse sites of each. -/
noncomputable def logZLayer (N : ℕ) (β : ℝ) (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 2 * logZ2 N β n

/-- **The layered window defect**, in the form of `windowCoupling`: `16 log Z(2^w) − log Z(2 · 2^w)`.
DERIVED: `16 = 2⁴` the copies; `2` the doubling. -/
noncomputable def layerDefect (N : ℕ) (β : ℝ) (w : ℕ) : ℝ :=
  16 * logZLayer N β (2 ^ w) - logZLayer N β (2 * 2 ^ w)

/-- **The doubling bookkeeping**: `D_layer(w) = 8 n² D₂(n)` at `n = 2^w`. DERIVED: `8 = 16 · 2 / 4`, from
`16 · 2n² = 32 n² = 4 · 8 n²` and `2 (2n)² = 8 n²`. -/
theorem layerDefect_eq (N : ℕ) (β : ℝ) (w : ℕ) :
    layerDefect N β w = 8 * ((2 : ℝ) ^ w) ^ 2 * D2 N β (2 ^ w) := by
  unfold layerDefect logZLayer D2
  push_cast
  ring

/-- **The layered anchor**: at every `β` where the 2D character form holds, the layered window defect tends to
`0` along the windows. No threshold on `β`. DERIVED: `8` from `layerDefect_eq`; `2` the doubling; `0` the
limit. -/
theorem layer_vanishes {N : ℕ} {β : ℝ} (h : TwoDCharacter N β) :
    Tendsto (layerDefect N β) atTop (𝓝 0) := by
  have hw : Tendsto (fun w : ℕ => 2 ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h8 := ((twoD_vanishes h).comp hw).const_mul 8
  rw [mul_zero] at h8
  refine h8.congr fun w => ?_
  rw [layerDefect_eq]
  simp only [Function.comp]
  push_cast
  ring

/-! ## 5. The transport -/

/-- **`LayerTransport N`, a named input, not proved**: an anisotropic family `D(β, β_⊥, w)` that is the layered
defect at `β_⊥ = 0` and the window coupling at `β_⊥ = β` (the identification of the anisotropic Wilson torus,
which the tree cannot express), and, frequently as `β → ∞`, differentiable in `β_⊥` on `[0, β]` at windows
`w ≥ 1` with BetaFlow's Osgood form in `β_⊥` from base `0`, `K` continuous on `[0, ∞)`. Expected to fail for
`U(1)` (Coulomb phase at `β_⊥ = β` large). This is not `StrongEnd` restated: it is stronger. Because `K` does
not depend on `w`, it asks that the window coupling decay at a rate comparable to the layered defect,
`log(1/D(β, β, w)) ≳ c·4^w`, and not only that it tend to `0`; a window coupling vanishing like `1/w` meets
`StrongEnd` and fails this input. A mass gap is expected to give only `log(1/D) ≈ m·2^w` (argued), so this input
is likely false for `SU(N)` as stated; a usable transport needs a `K` that may grow with the window. No part of
it is proved here. DERIVED: `0` the decoupled end; `1` the least window. -/
def LayerTransport (N : ℕ) : Prop :=
  ∃ D : ℝ → ℝ → ℕ → ℝ, (∀ β w, D β 0 w = layerDefect N β w) ∧
    (∀ β w, D β β w = windowCoupling N β w) ∧
    ∃ᶠ β in atTop, ∃ K : ℝ → ℝ, ContinuousOn K (Ici 0) ∧
      (∀ w : ℕ, 1 ≤ w → ∀ t ∈ Icc 0 β, DifferentiableAt ℝ (fun s => D β s w) t) ∧
      BetaFlow.OsgoodForm (fun t w => D β t w) 0 K

/-- **The transport gives the strong end**: the 2D character form at every `β` and `LayerTransport N` give
`StrongEnd N`. DERIVED: `0` the decoupled end, the lower coupling and the limit; `1` the least window. -/
theorem strongEnd_of_layerTransport {N : ℕ} (hN : N ≠ 0) (hC : ∀ β, TwoDCharacter N β)
    (hT : LayerTransport N) : StrongEnd N := by
  obtain ⟨D, h0, hd, hfr⟩ := hT
  refine (hfr.and_eventually (eventually_ge_atTop (0 : ℝ))).mono ?_
  rintro β ⟨⟨K, hK, hdiff, hF⟩, hβ⟩
  have hV := layer_vanishes (hC β)
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  obtain ⟨ℓ, hℓ, hlt⟩ := BetaFlow.exists_level (Real.exp_pos (-∫ x in (0 : ℝ)..β, K x)) hη
  filter_upwards [hV.eventually (eventually_lt_nhds (BetaFlow.bose_pos hℓ)), eventually_ge_atTop 1]
    with w hw hw1
  have hb := BetaFlow.osgood_bound_integral (u := fun s => D β s w)
    (u' := deriv fun s => D β s w) hβ hK (fun x hx => (hdiff w hw1 x hx).hasDerivAt) hℓ
    (by show D β 0 w ≤ _; rw [h0]; exact hw.le) (fun x hx h1 => hF w hw1 x hx.1 h1)
  have hnn := windowCoupling_nonneg hN hβ hw1
  simp only [hd] at hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hb.trans_lt hlt

end MassGap.LayerSplit

#print axioms MassGap.LayerSplit.norm_term_le
#print axioms MassGap.LayerSplit.abs_tail_le
#print axioms MassGap.LayerSplit.tendsto_succ_mul_pow
#print axioms MassGap.LayerSplit.tendsto_mul_tail
#print axioms MassGap.LayerSplit.tendsto_tail
#print axioms MassGap.LayerSplit.abs_log_one_add_le
#print axioms MassGap.LayerSplit.tendsto_mul_log
#print axioms MassGap.LayerSplit.closedForm_defect
#print axioms MassGap.LayerSplit.twoD_vanishes
#print axioms MassGap.LayerSplit.layerDefect_eq
#print axioms MassGap.LayerSplit.layer_vanishes
#print axioms MassGap.LayerSplit.strongEnd_of_layerTransport
