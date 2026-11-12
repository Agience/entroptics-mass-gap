import Mathlib
import MassGap.OpenAIBridgeSlab

/-!
# MassGap.OpenAIBridgeRP — slab clustering in reflection form

`OpenAIBridgeSlab` bounds the connected correlation of two slab observables by `6 A B` times the
gap factors, with `A`, `B` the sup bounds of the observables. A renormalized insertion has no sup
bound uniform in the spacing. This module bounds the whole connected correlation by readings of
the insertions themselves: reflected two-point readings at a separation `s = 2a + 2 > 0`, their
Hilbert–Schmidt form, and the vacuum one-point readings.

## The reflection

The time reflection of a slab observable `f` reads the slab backwards with the time links
inverted; its slab kernel is the transpose `F̂ᵀ = tp F̂` of the slab kernel of `f`
(`slabKer_rev`). With the transfer kernel split at its vacuum, `K = c φ⊗φ + R`
(`R = rem k c φ`), the reflected reading of `f` at separation `s` is

    R_f(s) = c^{−(2w+s)} ⟨F̂ᵀφ, R^s F̂ᵀφ⟩ = ‖R^{s/2} F̂ᵀφ‖² / |c|^{2w+s},

the connected correlation of `f` with its reflection `θf` at separation `s`, in transfer terms
(`connK_refl_read`), and its Hilbert–Schmidt form is
`H_f(s) = Tr(F̂ R^s F̂ᵀ R^s) / |c|^{2(w+s)} = ‖R^{s/2} F̂ R^{s/2}‖²_HS / |c|^{2(w+s)}`
(`hs_sand_eq`).

## 1. Reflected readings

* `kf_iter_add` — `R^{m+l+2} u = R^{m+1}(R^{l+1} u)`;
* `pair_symm` — `⟨g, S u⟩ = ⟨S g, u⟩` for a bounded symmetric kernel `S`;
* `rpRead`, `rpRead_nonneg`, `rpRead_eq` — `‖R^{a+1} u‖²`, and it is the reflected pairing
  `⟨u, R^{2a+2} u⟩`;
* `refl`, `refl_nonneg`, `sqrt_refl` — the normalized reflected reading `R_f(2a+2)` of a kernel
  insertion `F` covering `w` steps;
* `vacRead` — the vacuum reading `⟨φ, Fφ⟩ / |c|^w`;
* `hsRead`, `hsRead_nonneg`, `sqrt_hsRead`, `hs_sand_eq` — the Hilbert–Schmidt reflected reading
  `‖R^{a+1} F R^{a+1}‖²_HS / |c|^{2(w+2a+2)}`, and its numerator is `Tr(F R^{2a+2} Fᵀ R^{2a+2})`;
* `hs_sand_eq2` — with unequal sides, `‖R^{b+1} F R^{a+1}‖²_HS = Tr(F R^{2a+2} Fᵀ R^{2b+2})`;
* `abs_trc_le`, `trc_sand`, `trK_sand` — `|Tr(PQ)| ≤ ‖P‖_HS ‖Q‖_HS`, and the one- and two-point
  traces rewritten around the sandwiches `R^{a+1} F R^{a+1}`.

## 2. The connected ratio in reflection form

* `abs_pair_rp` — `|⟨g, R^{2a+j+3} u⟩| ≤ (1/2)^⌊(j+1)/n⌋ |c|^{j+1} ‖R^{a+1} g‖ ‖R^{a+1} u‖`;
* `abs_cross_rp` — the same for the normalized cross terms of the trace ratio;
* `conn_alg3`, `excited_le_of_le`, `connK_split` — the connected ratio is its separated term
  divided by `1 + σ₀`, up to the opposite cross term and `5 A B σ`, `σ` the excited weight;
* `connK_rp` — `|connK| ≤ (1/2)^⌊(j+1)/n⌋ √(R_F R_{Gᵀ}) + (1/2)^⌊(j'+1)/n⌋ √(R_{Fᵀ} R_G)
  + 5 A B σ` for `p = 2a + j + 2`, `q = 2a + j' + 2`;
* `connK_rp_slab` — the same from the window of the seed, `σ ≤ (1/2)^⌊((p+q)/2+1)/n⌋`;
* `connK_refl_read` — the torus correlation of `F` with its reflection `Fᵀ` at separation
  `2a + 2` is `R_F(2a+2)` up to `A² ((1/2)^⌊(q+1)/n⌋ + 6σ)`;
* `hs_conv_rem_le` — the gap bound in Hilbert–Schmidt form, row by row from
  `OpenAIBridgeCluster.sq_integral_remFun_le`:
  `hs(P R^{m+1}) ≤ ((1/2)^⌊(m+1)/n⌋ |c|^{m+1})² hs(P)`;
* `abs_trK_hs`, `abs_trOne_hs` — the excited–excited trace is at most
  `(1/2)^⌊(j+1)/n⌋ (1/2)^⌊(j'+1)/n⌋ √(H_F H_G)` and a one-point excited trace at most
  `√H_F √σ`, normalized;
* `conn_alg4` — the bookkeeping of the trace ratio without sup bounds;
* `connK_rp_full` — the whole connected ratio:
  `|connK| ≤ (1/2)^⌊(j+1)/n⌋ √(R_F R_{Gᵀ}) + (1/2)^⌊(j'+1)/n⌋ √(R_{Fᵀ} R_G)
  + (1/2)^⌊(j+1)/n⌋ (1/2)^⌊(j'+1)/n⌋ √(H_F H_G)
  + (|α_F||α_G| + |α_F| √H_G + |α_G| √H_F + √(H_F H_G)) √σ`, for bounded measurable `F`, `G`
  with no sup bound in the constant;
* `connK_rp_full_slab` — the same from the window of the seed.

## 2b. The reflected readings below the torus moment

* `reflMoment_le_torus` — `α_F² + R_F(2a+2) ≤ Tr(F K^{2a+2} Fᵀ K^{2b+2}) / |c|^L`,
  `L = 2w + (2a+2) + (2b+2)`, for every `a`, `b`: the vacuum and reflected readings are bounded by
  the torus moment of the insertion with its reflection, with no sup bound and no wrap-around error;
* `reflMoment_le_torus_ratio` — the same as `(1 + σ₀) E_L[f · θf]`, `σ₀` the excited weight of the
  torus (`trPow_even`).

## 3. On the Wilson torus

* `wilson_slab_conn_rp` (`SU(N)`) and `wilson_slab_conn_rpG` (every `GaugeGroup G`) — from the
  seed, on the cubic torus of every even side `L ≥ 2n`, for bounded measurable slab observables:
  `|⟨f_0 g_t⟩ − ⟨f_0⟩⟨g_t⟩| ≤ (1/2)^⌊(j+1)/n⌋ √(R_f R_{θg}) + (1/2)^⌊(j'+1)/n⌋ √(R_{θf} R_g)
  + 5 A B (1/2)^⌊((p+q)/2+1)/n⌋`, the readings taken from the slab kernels.

## 4. The reflected slab

* `swap_int`, `swap_pair` — Fubini for bounded measurable functions of one and two pairs;
* `cutV`, `backG`, `revG` — a cut sequence, the insertion read from the far end of the chain, and
  the reflected observable `θG(V, A) = G(V_{m+1−i}, ι A_{m−i})`;
* `slabKer_back` — the slab kernel peeled from its last step;
* `slabKer_rev` — if `w(x, a, y) = w(y, ι a, x)` with `ι` measure preserving, then
  `slabKer m (revG ι m G) = tp (slabKer m G)`;
* `slabKer_rev_wtR` (`SU(N)`) and `slabKer_rev_wtG` (every `GaugeGroup G`) — on the Wilson torus,
  with `ι` the inversion of the time links: the slab kernel of `θf` is `tp (slabKer f)`, so
  `R_{θf} = refl (slabKer θf)` is the reading of the Wilson function of the reflected slab.

## 5. The whole connected correlation on the Wilson torus

* `wilson_slab_conn_rp_full` (`SU(N)`) and `wilson_slab_conn_rp_fullG` (every `GaugeGroup G`) —
  from the seed, on the cubic torus of every even side `L ≥ 2n`, for bounded measurable slab
  observables `f`, `g` and their reflections `θf`, `θg`:
  `|⟨f_0 g_t⟩ − ⟨f_0⟩⟨g_t⟩| ≤ (1/2)^⌊(j+1)/n⌋ √(R_f R_{θg}) + (1/2)^⌊(j'+1)/n⌋ √(R_{θf} R_g)
  + (1/2)^⌊(j+1)/n⌋ (1/2)^⌊(j'+1)/n⌋ √(H_f H_g)
  + (|α_f||α_g| + |α_f| √H_g + |α_g| √H_f + √(H_f H_g)) √((1/2)^⌊((p+q)/2+1)/n⌋)`.

## Scope

In `connK_rp_full` and the capstones of §5 no sup bound enters the constant: every term is a
reflected reading (`R`, `H`) or a vacuum reading (`α`) of the insertions. The vacuum readings enter
only with the wrap-around factor `√σ`, and they vanish for observables centred at their vacuum
value. The readings are transfer-matrix (vacuum) quantities of the same slice: `R_f` is the
correlation of `f` with `θf` up to the wrap-around (`connK_refl_read`), and `H_f` is the
excited part of that correlation on the chain of `2w + 4a + 4` steps (`hs_sand_eq`).
-/

namespace MassGap.OpenAIBridgeRP

open MeasureTheory Real
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeUniform MassGap.OpenAIBridgeSlab

/-! ## 1. Reflected readings -/

section Read

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **Powers of a kernel compose on functions**: `R^{m+l+2} u = R^{m+1}(R^{l+1} u)` pointwise, for a
bounded kernel `r` and a bounded measurable `u` (`KernelPower.iter_add` and one Fubini swap).

DERIVED: `1` is the offset of `iter`. -/
theorem kf_iter_add {r : X → X → ℝ} (hr : Bdd r) {u : X → ℝ} (hu : Measurable u) {Cu : ℝ}
    (hub : ∀ x, |u x| ≤ Cu) (m l : ℕ) (x : X) :
    kernelFun (iter μ r (m + l + 1)) μ u x
      = kernelFun (iter μ r m) μ (kernelFun (iter μ r l) μ u) x := by
  rw [iter_add hr m l]
  obtain ⟨Cm, hCm⟩ := (hr.iter (μ := μ) m).bdd
  obtain ⟨Cl, hCl⟩ := (hr.iter (μ := μ) l).bdd
  have hF : Measurable (Function.uncurry fun y z => iter μ r m x z * iter μ r l z y * u y) :=
    ((((hr.iter (μ := μ) m).row x).comp measurable_snd).mul
      ((hr.iter (μ := μ) l).meas.comp measurable_swap)).mul (hu.comp measurable_fst)
  have hFb : ∀ y z, |iter μ r m x z * iter μ r l z y * u y| ≤ Cm * Cl * Cu := fun y z =>
    HiddenChain.abs_mul_le_of (HiddenChain.abs_mul_le_of (hCm x z) (hCl z y)) (hub y)
  unfold kernelFun conv
  calc ∫ y, (∫ z, iter μ r m x z * iter μ r l z y ∂μ) * u y ∂μ
      = ∫ y, ∫ z, iter μ r m x z * iter μ r l z y * u y ∂μ ∂μ := by
        congr 1; funext y; rw [integral_mul_const]
    _ = ∫ z, ∫ y, iter μ r m x z * iter μ r l z y * u y ∂μ ∂μ := swap_bdd hF hFb
    _ = ∫ z, iter μ r m x z * ∫ y, iter μ r l z y * u y ∂μ ∂μ := by
        congr 1; funext z; rw [← integral_const_mul]; congr 1; funext y; ring

/-- **A symmetric kernel moves across the pairing**: `∫ g (S u) = ∫ (S g) u` for a bounded symmetric
kernel `S` and bounded measurable `u`, `g` (one Fubini swap).

DERIVED: no numeral appears in the statement. -/
theorem pair_symm {S : X → X → ℝ} (hS : Bdd S) (hss : ∀ x y, S x y = S y x) {u g : X → ℝ}
    (hu : Measurable u) (hg : Measurable g) {Cu Cg : ℝ} (hub : ∀ x, |u x| ≤ Cu)
    (hgb : ∀ x, |g x| ≤ Cg) :
    ∫ x, g x * kernelFun S μ u x ∂μ = ∫ x, kernelFun S μ g x * u x ∂μ := by
  obtain ⟨CS, hCS⟩ := hS.bdd
  have hF : Measurable (Function.uncurry fun x y => g x * (S x y * u y)) :=
    (hg.comp measurable_fst).mul (hS.meas.mul (hu.comp measurable_snd))
  have hFb : ∀ x y, |g x * (S x y * u y)| ≤ Cg * (CS * Cu) := fun x y =>
    HiddenChain.abs_mul_le_of (hgb x) (HiddenChain.abs_mul_le_of (hCS x y) (hub y))
  unfold kernelFun
  calc ∫ x, g x * ∫ y, S x y * u y ∂μ ∂μ = ∫ x, ∫ y, g x * (S x y * u y) ∂μ ∂μ := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y, ∫ x, g x * (S x y * u y) ∂μ ∂μ := swap_bdd hF hFb
    _ = ∫ y, (∫ x, S y x * g x ∂μ) * u y ∂μ := by
        congr 1; funext y; rw [← integral_mul_const]; congr 1; funext x; rw [hss y x]; ring

/-- **The reflected reading** of a function `u` at half-separation `a + 1`:
`rpRead μ r a u = ∫ (R^{a+1} u)² = ‖R^{a+1} u‖²`, `R^{a+1} = iter μ r a`.

DERIVED: `2` is the square; `1` the offset of `iter`. -/
noncomputable def rpRead (μ : Measure X) (r : X → X → ℝ) (a : ℕ) (u : X → ℝ) : ℝ :=
  ∫ x, kernelFun (iter μ r a) μ u x ^ 2 ∂μ

omit [IsProbabilityMeasure μ] in
/-- The reflected reading is nonnegative.

DERIVED: `0` is the sign. -/
theorem rpRead_nonneg (r : X → X → ℝ) (a : ℕ) (u : X → ℝ) : 0 ≤ rpRead μ r a u :=
  integral_nonneg fun _ => sq_nonneg _

/-- **The reflected reading is the reflected pairing**: for a bounded symmetric `r`,
`‖R^{a+1} u‖² = ⟨u, R^{2a+2} u⟩` (`kf_iter_add`, `pair_symm`, `CyclicKernel.iter_symm`).

DERIVED: `1` and `2` are the offsets of `iter`, so `a + a + 1` is the power `2a + 2`. -/
theorem rpRead_eq {r : X → X → ℝ} (hr : Bdd r) (hrs : ∀ x y, r x y = r y x) {u : X → ℝ}
    (hu : Measurable u) {Cu : ℝ} (hub : ∀ x, |u x| ≤ Cu) (a : ℕ) :
    rpRead μ r a u = ∫ x, u x * kernelFun (iter μ r (a + a + 1)) μ u x ∂μ := by
  obtain ⟨Ca, hCa⟩ := (hr.iter (μ := μ) a).bdd
  have hv := measurable_kf (μ := μ) (hr.iter (μ := μ) a) hu
  have hvb := abs_kf_le (μ := μ) hCa hub
  have e : ∀ x, kernelFun (iter μ r (a + a + 1)) μ u x
      = kernelFun (iter μ r a) μ (kernelFun (iter μ r a) μ u) x := kf_iter_add hr hu hub a a
  simp_rw [e]
  rw [pair_symm (hr.iter (μ := μ) a) (CyclicKernel.iter_symm (μ := μ) hr hrs a) hv hu hvb hub]
  unfold rpRead
  congr 1; funext x; ring

/-- **The normalized reflected reading of a kernel insertion**: for `F` covering `w` steps and the
split `K = c φ⊗φ + R`, `refl μ k c φ F w a = ‖R^{a+1} Fᵀφ‖² / |c|^{2(w+a+1)}`, i.e.
`c^{−(2w+s)} ⟨Fᵀφ, R^s Fᵀφ⟩` at separation `s = 2a + 2` (`rpRead_eq`): the connected correlation of
the insertion with its time reflection `Fᵀ`, in transfer terms.

DERIVED: `2` is the square of the norm; `1` the offset of `iter`. -/
noncomputable def refl (μ : Measure X) (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ)
    (w a : ℕ) : ℝ :=
  rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ) / |c| ^ (2 * (w + a + 1))

omit [IsProbabilityMeasure μ] in
/-- The normalized reflected reading is nonnegative.

DERIVED: `0` is the sign; `1` and `2` as in `refl`. -/
theorem refl_nonneg (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w a : ℕ) :
    0 ≤ refl μ k c φ F w a :=
  div_nonneg (rpRead_nonneg _ _ _) (pow_nonneg (abs_nonneg c) _)

omit [IsProbabilityMeasure μ] in
/-- The square root of the normalized reflected reading:
`√(refl F w a) = ‖R^{a+1} Fᵀφ‖ / |c|^{w+a+1}`.

DERIVED: `1` is the offset of `iter`; `2` the square. -/
theorem sqrt_refl (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w a : ℕ) :
    √(refl μ k c φ F w a)
      = √(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1) := by
  unfold refl
  rw [show |c| ^ (2 * (w + a + 1)) = (|c| ^ (w + a + 1)) ^ 2 by ring,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (pow_nonneg (abs_nonneg c) _)]

/-- **The vacuum reading of a kernel insertion**: `vacRead μ c φ F w = ⟨φ, Fφ⟩ / |c|^w`, the vacuum
expectation of the observable whose kernel `F` covers `w` steps. It is zero for an observable
centred at its vacuum value.

DERIVED: no numeral appears in the statement. -/
noncomputable def vacRead (μ : Measure X) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w : ℕ) : ℝ :=
  (∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w

/-- **The Hilbert–Schmidt reflected reading of a kernel insertion**: for `F` covering `w` steps,
`hsRead μ k c φ F w a = ‖R^{a+1} F R^{a+1}‖²_HS / |c|^{2(w+2a+2)}`. By `hs_sand_eq` the numerator is
`Tr(F R^s Fᵀ R^s)` at `s = 2a + 2`: the excited part of the torus correlation of the insertion with
its time reflection.

DERIVED: `2` is the square of the norm and the two sides `a + 1` of the sandwich; `1` the offset of
`iter`. -/
noncomputable def hsRead (μ : Measure X) (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ)
    (w a : ℕ) : ℝ :=
  hs μ (conv μ (iter μ (rem k c φ) a) (conv μ F (iter μ (rem k c φ) a)))
    / |c| ^ (2 * (w + a + a + 2))

omit [IsProbabilityMeasure μ] in
/-- The Hilbert–Schmidt reflected reading is nonnegative.

DERIVED: `0` is the sign; `1` and `2` as in `hsRead`. -/
theorem hsRead_nonneg (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w a : ℕ) :
    0 ≤ hsRead μ k c φ F w a :=
  div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg c) _)

omit [IsProbabilityMeasure μ] in
/-- The square root of the Hilbert–Schmidt reflected reading:
`√(hsRead F w a) = ‖R^{a+1} F R^{a+1}‖_HS / |c|^{w+2a+2}`.

DERIVED: `2` is the square and the two sides of the sandwich; `1` the offset of `iter`. -/
theorem sqrt_hsRead (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (F : X → X → ℝ) (w a : ℕ) :
    √(hsRead μ k c φ F w a)
      = √(hs μ (conv μ (iter μ (rem k c φ) a) (conv μ F (iter μ (rem k c φ) a))))
        / |c| ^ (w + a + a + 2) := by
  unfold hsRead
  rw [show |c| ^ (2 * (w + a + a + 2)) = (|c| ^ (w + a + a + 2)) ^ 2 by ring,
    Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (pow_nonneg (abs_nonneg c) _)]

/-- **Cauchy–Schwarz for the trace in square-root form**:
`|trc(P ∗ Q)| ≤ ‖P‖_HS ‖Q‖_HS` (`OpenAIBridgeSlab.sq_trc_conv_le`).

DERIVED: no numeral appears in the statement. -/
theorem abs_trc_le {P Q : X → X → ℝ} (hP : Bdd P) (hQ : Bdd Q) :
    |trc μ (conv μ P Q)| ≤ √(hs μ P) * √(hs μ Q) := by
  rw [← Real.sqrt_mul (hs_nonneg _)]
  exact Real.abs_le_sqrt (sq_trc_conv_le hP hQ)

/-- **A one-point trace as a sandwich**: `Tr(F R^{2a+l+3}) = Tr((R^{a+1} F R^{a+1}) R^{l+1})`
(`iter_add`, associativity and cyclicity).

DERIVED: `1`, `2` are the offsets of `iter` (`(a+1) + (l+1) + (a+1)`). -/
theorem trc_sand {r : X → X → ℝ} (hr : Bdd r) {F : X → X → ℝ} (hF : Bdd F) (a l : ℕ) :
    trc μ (conv μ F (iter μ r (a + l + a + 2)))
      = trc μ (conv μ (conv μ (iter μ r a) (conv μ F (iter μ r a))) (iter μ r l)) := by
  have hA : Bdd (iter μ r a) := hr.iter a
  have hK : Bdd (iter μ r l) := hr.iter l
  have hFA : Bdd (conv μ F (iter μ r a)) := hF.conv hA
  have hKA : Bdd (conv μ (iter μ r l) (iter μ r a)) := hK.conv hA
  have hFAK : Bdd (conv μ (conv μ F (iter μ r a)) (iter μ r l)) := hFA.conv hK
  rw [show a + l + a + 2 = a + (l + a + 1) + 1 by omega, iter_add hr a (l + a + 1),
    iter_add hr l a, conv_assoc hF hA hKA, conv_assoc hFA hK hA, trc_conv_comm hFAK hA,
    conv_assoc hA hFA hK]

/-- **A two-point trace as two sandwiches**: for `p = 2a + j + 2`, `q = 2a + j' + 2`,
`Tr(F R^{p+1} G R^{q+1}) = Tr((Q R^{j'+1})(P R^{j+1}))` with `P = R^{a+1} F R^{a+1}` and
`Q = R^{a+1} G R^{a+1}` (`iter_add`, associativity and cyclicity).

DERIVED: `1`, `2` are the offsets of `iter`. -/
theorem trK_sand {r : X → X → ℝ} (hr : Bdd r) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G)
    (a j j' : ℕ) :
    trK μ r F G (a + j + a + 2) (a + j' + a + 2)
      = trc μ (conv μ (conv μ (conv μ (iter μ r a) (conv μ G (iter μ r a))) (iter μ r j'))
          (conv μ (conv μ (iter μ r a) (conv μ F (iter μ r a))) (iter μ r j))) := by
  have hA : Bdd (iter μ r a) := hr.iter a
  have hJ : Bdd (iter μ r j) := hr.iter j
  have hJ' : Bdd (iter μ r j') := hr.iter j'
  have hJA : Bdd (conv μ (iter μ r j) (iter μ r a)) := hJ.conv hA
  have hJ'A : Bdd (conv μ (iter μ r j') (iter μ r a)) := hJ'.conv hA
  have hFA : Bdd (conv μ F (iter μ r a)) := hF.conv hA
  have hGA : Bdd (conv μ G (iter μ r a)) := hG.conv hA
  have hZ : Bdd (conv μ (conv μ F (iter μ r a)) (iter μ r j)) := hFA.conv hJ
  have hY : Bdd (conv μ (conv μ G (iter μ r a)) (conv μ (iter μ r j') (iter μ r a))) :=
    hGA.conv hJ'A
  have hQ : Bdd (conv μ (iter μ r a) (conv μ G (iter μ r a))) := hA.conv hGA
  have hQJ : Bdd (conv μ (conv μ (iter μ r a) (conv μ G (iter μ r a))) (iter μ r j')) :=
    hQ.conv hJ'
  have hAY : Bdd (conv μ (iter μ r a)
      (conv μ (conv μ G (iter μ r a)) (conv μ (iter μ r j') (iter μ r a)))) := hA.conv hY
  unfold trK
  rw [show a + j + a + 2 = a + (j + a + 1) + 1 by omega,
    show a + j' + a + 2 = a + (j' + a + 1) + 1 by omega, iter_add hr a (j + a + 1),
    iter_add hr a (j' + a + 1), iter_add hr j a, iter_add hr j' a,
    conv_assoc hF hA hJA, conv_assoc hFA hJ hA, conv_assoc hG hA hJ'A,
    ← conv_assoc hZ hA hY, trc_conv_comm hZ hAY, conv_assoc hA hGA hJ'A,
    conv_assoc hQ hJ' hA, ← conv_assoc hQJ hA hZ, conv_assoc hA hFA hJ]

/-- **The Hilbert–Schmidt reading is the reflected trace**: for a bounded symmetric `r`,
`‖R^{a+1} F R^{a+1}‖²_HS = Tr(F R^{2a+2} Fᵀ R^{2a+2})` (`hs_eq_trc`, `tp_conv`, `tp_iter`,
associativity and cyclicity).

DERIVED: `1` and `2` are the offsets of `iter`, so `a + a + 1` is the power `2a + 2`; `2` the
square. -/
theorem hs_sand_eq {r : X → X → ℝ} (hr : Bdd r) (hrs : ∀ x y, r x y = r y x) {F : X → X → ℝ}
    (hF : Bdd F) (a : ℕ) :
    hs μ (conv μ (iter μ r a) (conv μ F (iter μ r a)))
      = trK μ r F (tp F) (a + a + 1) (a + a + 1) := by
  have hA : Bdd (iter μ r a) := hr.iter a
  have hFt : Bdd (tp F) := bdd_tp hF
  have hFA : Bdd (conv μ F (iter μ r a)) := hF.conv hA
  have hAA : Bdd (conv μ (iter μ r a) (iter μ r a)) := hA.conv hA
  have hAFt : Bdd (conv μ (iter μ r a) (tp F)) := hA.conv hFt
  have hY2 : Bdd (conv μ (conv μ (iter μ r a) (tp F)) (iter μ r a)) := hAFt.conv hA
  have hFAY : Bdd (conv μ (conv μ F (iter μ r a))
      (conv μ (conv μ (iter μ r a) (tp F)) (iter μ r a))) := hFA.conv hY2
  have hFtAA : Bdd (conv μ (tp F) (conv μ (iter μ r a) (iter μ r a))) := hFt.conv hAA
  rw [hs_eq_trc, tp_conv, tp_conv, tp_iter hr hrs a]
  unfold trK
  rw [iter_add hr a a, ← conv_assoc hA hFA hY2, trc_conv_comm hA hFAY,
    ← conv_assoc hFA hY2 hA, ← conv_assoc hAFt hA hA, ← conv_assoc hA hFt hAA,
    conv_assoc hF hA hA, ← conv_assoc hFA hA hFtAA]


/-- **The Hilbert–Schmidt sandwich with unequal sides is a reflected trace**: for a bounded symmetric
`r`, `‖R^{b+1} F R^{a+1}‖²_HS = Tr(F R^{2a+2} Fᵀ R^{2b+2})` (`hs_eq_trc`, `tp_conv`, `tp_iter`,
associativity and cyclicity). At `a = b` it is `hs_sand_eq`.

DERIVED: `1` and `2` are the offsets of `iter`, so `a + a + 1` and `b + b + 1` are the powers
`2a + 2` and `2b + 2`; `2` the square. -/
theorem hs_sand_eq2 {r : X → X → ℝ} (hr : Bdd r) (hrs : ∀ x y, r x y = r y x) {F : X → X → ℝ}
    (hF : Bdd F) (a b : ℕ) :
    hs μ (conv μ (iter μ r b) (conv μ F (iter μ r a)))
      = trK μ r F (tp F) (a + a + 1) (b + b + 1) := by
  have hA : Bdd (iter μ r a) := hr.iter a
  have hB : Bdd (iter μ r b) := hr.iter b
  have hFt : Bdd (tp F) := bdd_tp hF
  have hFA : Bdd (conv μ F (iter μ r a)) := hF.conv hA
  have hAFt : Bdd (conv μ (iter μ r a) (tp F)) := hA.conv hFt
  have hY : Bdd (conv μ (conv μ (iter μ r a) (tp F)) (iter μ r b)) := hAFt.conv hB
  have hZ : Bdd (conv μ (conv μ F (iter μ r a))
      (conv μ (conv μ (iter μ r a) (tp F)) (iter μ r b))) := hFA.conv hY
  have hFtB : Bdd (conv μ (tp F) (iter μ r b)) := hFt.conv hB
  have hFtBB : Bdd (conv μ (conv μ (tp F) (iter μ r b)) (iter μ r b)) := hFtB.conv hB
  have lhs : hs μ (conv μ (iter μ r b) (conv μ F (iter μ r a)))
      = trc μ (conv μ (conv μ (conv μ F (iter μ r a))
          (conv μ (conv μ (iter μ r a) (tp F)) (iter μ r b))) (iter μ r b)) := by
    rw [hs_eq_trc, tp_conv, tp_conv, tp_iter hr hrs a, tp_iter hr hrs b,
      ← conv_assoc hB hFA hY, trc_conv_comm hB hZ]
  have rhs : trK μ r F (tp F) (a + a + 1) (b + b + 1)
      = trc μ (conv μ (conv μ (conv μ F (iter μ r a))
          (conv μ (conv μ (iter μ r a) (tp F)) (iter μ r b))) (iter μ r b)) := by
    unfold trK
    rw [iter_add hr a a, iter_add hr b b, conv_assoc hF hA hA, conv_assoc hFt hB hB,
      ← conv_assoc hFA hA hFtBB, conv_assoc hA hFtB hB, conv_assoc hA hFt hB,
      conv_assoc hFA hY hB]
  rw [lhs, rhs]

end Read

/-! ## 2. The connected ratio in reflection form -/

section CorrRP

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
/-- **The separated pairing in reflection form**: for bounded measurable `u`, `g`,

    |⟨g, R^{2a+j+3} u⟩| ≤ (1/2)^⌊(j+1)/n⌋ |c|^{j+1} ‖R^{a+1} g‖ ‖R^{a+1} u‖.

`R^{2a+j+3} = R^{a+1} R^{j+1} R^{a+1}` (`kf_iter_add`), one `R^{a+1}` moves across the pairing
(`pair_symm`), and the middle power is the gap bound
`OpenAIBridgeCluster.abs_integral_remFun_le` with the `L²` norms `√rpRead`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1`, `2`, `3` are the offsets of `iter`
(`(a+1) + (j+1) + (a+1)`). -/
theorem abs_pair_rp (a j : ℕ) {u g : X → ℝ} (hum : Measurable u) (hgm : Measurable g)
    {Cu Cg : ℝ} (hub : ∀ x, |u x| ≤ Cu) (hgb : ∀ x, |g x| ≤ Cg) :
    |∫ x, g x * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ u x ∂μ|
      ≤ (1 / 2) ^ ((j + 1) / n) * |c| ^ (j + 1) * √(rpRead μ (rem k c φ) a g)
        * √(rpRead μ (rem k c φ) a u) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  obtain ⟨Ca, hCa⟩ := (hr.iter (μ := μ) a).bdd
  obtain ⟨Cj, hCj⟩ := (hr.iter (μ := μ) j).bdd
  have hum' := measurable_kf (μ := μ) (hr.iter (μ := μ) a) hum
  have hub' := abs_kf_le (μ := μ) hCa hub
  have hgm' := measurable_kf (μ := μ) (hr.iter (μ := μ) a) hgm
  have hgb' := abs_kf_le (μ := μ) hCa hgb
  have hjm := measurable_kf (μ := μ) (hr.iter (μ := μ) j) hum'
  have hjb := abs_kf_le (μ := μ) hCj hub'
  have e2 : kernelFun (iter μ (rem k c φ) (j + a + 1)) μ u
      = kernelFun (iter μ (rem k c φ) j) μ (kernelFun (iter μ (rem k c φ) a) μ u) :=
    funext (kf_iter_add hr hum hub j a)
  have e1 : ∀ x, kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ u x
      = kernelFun (iter μ (rem k c φ) a) μ
          (kernelFun (iter μ (rem k c φ) j) μ (kernelFun (iter μ (rem k c φ) a) μ u)) x := by
    intro x
    rw [show a + j + a + 2 = a + (j + a + 1) + 1 by omega, kf_iter_add hr hum hub a (j + a + 1) x,
      e2]
  simp_rw [e1]
  rw [pair_symm (hr.iter (μ := μ) a) (CyclicKernel.iter_symm (μ := μ) hr hrs a) hjm hgm hjb hgb]
  exact abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap j hgm' hum' hgb' hub'
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (rpRead_nonneg _ _ _)]; exact le_rfl)
    (by rw [Real.sq_sqrt (rpRead_nonneg _ _ _)]; exact le_rfl)

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **A normalized cross term of the trace ratio in reflection form**: if `L = e + (j+1) + W + W'`,

    |c^e ⟨g, R^{2a+j+3} u⟩ / |c|^L| ≤ (1/2)^⌊(j+1)/n⌋ (‖R^{a+1} g‖/|c|^W) (‖R^{a+1} u‖/|c|^{W'}).

`abs_pair_rp`, with the powers of `|c|` distributed.

DERIVED: `1/2` is the contraction; `1`, `2` the offsets of `iter`; `0` the excluded eigenvalue. -/
theorem abs_cross_rp (hc0 : c ≠ 0) (a j : ℕ) {e W W' L : ℕ} (hL : L = e + (j + 1) + W + W')
    {u g : X → ℝ} (hum : Measurable u) (hgm : Measurable g) {Cu Cg : ℝ} (hub : ∀ x, |u x| ≤ Cu)
    (hgb : ∀ x, |g x| ≤ Cg) :
    |c ^ e * (∫ x, g x * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ u x ∂μ) / |c| ^ L|
      ≤ (1 / 2) ^ ((j + 1) / n) * (√(rpRead μ (rem k c φ) a g) / |c| ^ W)
        * (√(rpRead μ (rem k c φ) a u) / |c| ^ W') := by
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcL : 0 < |c| ^ L := pow_pos hc L
  have hX := abs_pair_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap a j hum hgm hub hgb
  have hW : |c| ^ W ≠ 0 := (pow_pos hc W).ne'
  have hW' : |c| ^ W' ≠ 0 := (pow_pos hc W').ne'
  have hLp : |c| ^ L = |c| ^ e * |c| ^ (j + 1) * |c| ^ W * |c| ^ W' := by
    rw [hL, pow_add, pow_add, pow_add]
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hcL, div_le_iff₀ hcL]
  calc |c| ^ e * |∫ x, g x * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ u x ∂μ|
      ≤ |c| ^ e * ((1 / 2) ^ ((j + 1) / n) * |c| ^ (j + 1) * √(rpRead μ (rem k c φ) a g)
        * √(rpRead μ (rem k c φ) a u)) := mul_le_mul_of_nonneg_left hX (pow_nonneg hc.le _)
    _ = (1 / 2) ^ ((j + 1) / n) * (√(rpRead μ (rem k c φ) a g) / |c| ^ W)
        * (√(rpRead μ (rem k c φ) a u) / |c| ^ W') * |c| ^ L := by
        rw [hLp]; field_simp
        try ring

/-- The real-number bookkeeping of `OpenAIBridgeSlab.conn_alg2` with the separated term `M` pulled
out: under the hypotheses of `conn_alg2`, the connected ratio minus `M / (1 + σ₀)` is within
`|e| + 4ABσ` of zero.

DERIVED: `4` is the constant of `conn_alg2`; `1` the vacuum's own weight in `Z` and the cap on
`σ`; `0` the signs. -/
theorem conn_alg3 {Λ σ0 σ α β ea eb e M A B : ℝ} (hΛ : 0 < Λ) (hσ0 : 0 ≤ σ0) (hσ0σ : σ0 ≤ σ)
    (hσ1 : σ ≤ 1) (hα : |α| ≤ A) (hβ : |β| ≤ B) (hea : |ea| ≤ A * σ) (heb : |eb| ≤ B * σ) :
    |Λ * (α * β + (e + M)) / (Λ * (1 + σ0))
        - Λ * (α + ea) / (Λ * (1 + σ0)) * (Λ * (β + eb) / (Λ * (1 + σ0))) - M / (1 + σ0)|
      ≤ |e| + 4 * (A * B) * σ := by
  have h := conn_alg2 hΛ hσ0 hσ0σ hσ1 hα hβ hea heb (e := e)
  have hD : 0 < 1 + σ0 := by linarith
  have hΛ' : Λ ≠ 0 := hΛ.ne'
  have hD' : 1 + σ0 ≠ 0 := hD.ne'
  have e1 : Λ * (α * β + (e + M)) / (Λ * (1 + σ0))
      = Λ * (α * β + e) / (Λ * (1 + σ0)) + M / (1 + σ0) := by
    field_simp; ring
  rw [e1, show Λ * (α * β + e) / (Λ * (1 + σ0)) + M / (1 + σ0)
      - Λ * (α + ea) / (Λ * (1 + σ0)) * (Λ * (β + eb) / (Λ * (1 + σ0))) - M / (1 + σ0)
    = Λ * (α * β + e) / (Λ * (1 + σ0))
      - Λ * (α + ea) / (Λ * (1 + σ0)) * (Λ * (β + eb) / (Λ * (1 + σ0))) by ring]
  exact h

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- The excited weight decreases along the levels: `σ_{j+l} ≤ σ_j` for `j ≥ 1`
(`OpenAIBridgeUniform.excited_add_le`).

DERIVED: `1` is the least level; `1/2` the contraction, at most `1`. -/
theorem excited_le_of_le (hc0 : c ≠ 0) (j l : ℕ) (hj : 1 ≤ j) :
    excited μ k c φ (j + l) ≤ excited μ k c φ j := by
  have hexc0 : 0 ≤ excited μ k c φ j := by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  rcases Nat.eq_zero_or_pos l with h0 | hl
  · simp [h0]
  · exact (excited_add_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 j l hj hl).trans
      (mul_le_of_le_one_left hexc0 (pow_le_one₀ (by norm_num) (by norm_num)))

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The connected ratio is its separated term up to the wrap-around.** Under the hypotheses of
`OpenAIBridgeSlab.connK_le_excited`, with `L = p + q + 2 + w + w'`, `σ = σ_{(p+q)/2+1}` and
`σ₀ = σ_{(p+q+w+w')/2+1}` the excited weight of the partition function,

    |connK − M_p / (1 + σ₀)| ≤ |M_q| + 5 A B σ,

`M_p = c^{q+1} ⟨Gφ, R^{p+1} Fᵀφ⟩ / |c|^L` the term of separation `p + 1` and
`M_q = c^{p+1} ⟨Fφ, R^{q+1} Gᵀφ⟩ / |c|^L` the term of separation `q + 1`. The proof of
`connK_le_excited` with `M_p` pulled out (`conn_alg3`).

DERIVED: `5 = 1 + 4` counts the excited–excited term and the four terms of `conn_alg2`; `1` and
`2` are the offsets of `iter` and the halving of the even `p + q` and widths; `0` the excluded
eigenvalue. -/
theorem connK_split (hc0 : c ≠ 0) {F G : X → X → ℝ} {A B : ℝ} {w w' : ℕ}
    (hF : OpBd μ F (A * |c| ^ w)) (hG : OpBd μ G (B * |c| ^ w')) (hw : Even w) (hw' : Even w')
    (p q : ℕ) (hpq : Even (p + q)) (hσ1 : excited μ k c φ ((p + q) / 2 + 1) ≤ 1) :
    |connK μ k F G w w' p q
        - c ^ (q + 1) * (∫ x, kernelFun G μ φ x
            * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
          / |c| ^ (p + q + w + w' + 2) / (1 + excited μ k c φ ((p + q + w + w') / 2 + 1))|
      ≤ |c ^ (p + 1) * (∫ x, kernelFun F μ φ x
            * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)|
          / |c| ^ (p + q + w + w' + 2)
        + 5 * (A * B) * excited μ k c φ ((p + q) / 2 + 1) := by
  obtain ⟨i, hi⟩ := hpq
  obtain ⟨v, hv⟩ := hw
  obtain ⟨v', hv'⟩ := hw'
  have hi2 : (p + q) / 2 = i := by omega
  rw [hi2] at hσ1 ⊢
  rw [show (p + q + w + w') / 2 + 1 = i + 1 + (v + v') by omega]
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcne : |c| ≠ 0 := hc.ne'
  have hcw : 0 < |c| ^ w := pow_pos hc w
  have hcw' : 0 < |c| ^ w' := pow_pos hc w'
  have hcwne : |c| ^ w ≠ 0 := hcw.ne'
  have hcwne' : |c| ^ w' ≠ 0 := hcw'.ne'
  have hcL : 0 < |c| ^ (p + q + w + w' + 2) := pow_pos hc _
  have hcLne : |c| ^ (p + q + w + w' + 2) ≠ 0 := hcL.ne'
  have hA0 : 0 ≤ A := nonneg_of_mul_pow hc0 hF.nonneg
  have hB0 : 0 ≤ B := nonneg_of_mul_pow hc0 hG.nonneg
  -- the excited weights
  have hσdef : ∀ j, hs μ (iter μ (rem k c φ) j)
      = excited μ k c φ (j + 1) * |c| ^ (2 * (j + 1)) := by
    intro j; unfold excited; rw [Nat.add_sub_cancel, div_mul_cancel₀ _ (pow_ne_zero _ hcne)]
  have hexc0 : ∀ j, 0 ≤ excited μ k c φ j := fun j => by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have hmono : ∀ l, excited μ k c φ (i + 1 + l) ≤ excited μ k c φ (i + 1) := fun l =>
    excited_le_of_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 (i + 1) l (by omega)
  -- the partition function
  have hZ : trPow μ k (p + q + w + w' + 1)
      = |c| ^ (p + q + w + w' + 2) * (1 + excited μ k c φ (i + 1 + (v + v'))) := by
    have e1 : p + q + w + w' + 1 = (i + v + v') + (i + v + v') + 1 := by omega
    have hev : Even (i + v + v' + (i + v + v') + 2) := ⟨i + v + v' + 1, by ring⟩
    rw [e1, trPow_even hφm hφb hφ1 hkm hkb hsym heig (i + v + v'), hσdef (i + v + v'),
      ← hev.pow_abs c, show p + q + w + w' + 2 = i + v + v' + (i + v + v') + 2 by omega,
      show 2 * (i + v + v' + 1) = i + v + v' + (i + v + v') + 2 by ring,
      show i + v + v' + 1 = i + 1 + (v + v') by ring]
    ring
  -- the one-point traces
  have hOF : trOne μ k F (p + q + w' + 1) = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w
        + trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / |c| ^ (p + q + w + w' + 2)) := by
    have hev : Even (p + q + w' + 1 + 1) := ⟨i + v' + 1, by omega⟩
    have hΛF : |c| ^ (p + q + w + w' + 2) = |c| ^ (p + q + w' + 1 + 1) * |c| ^ w := by
      rw [← pow_add]; congr 1; omega
    rw [trOne_decomp hφm hφb hφ1 hkm hkb hsym heig hF.bdd, ← hev.pow_abs c, hΛF]
    field_simp
    try ring
  have hOG : trOne μ k G (p + q + w + 1) = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w'
        + trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / |c| ^ (p + q + w + w' + 2)) := by
    have hev : Even (p + q + w + 1 + 1) := ⟨i + v + 1, by omega⟩
    have hΛG : |c| ^ (p + q + w + w' + 2) = |c| ^ (p + q + w + 1 + 1) * |c| ^ w' := by
      rw [← pow_add]; congr 1; omega
    rw [trOne_decomp hφm hφb hφ1 hkm hkb hsym heig hG.bdd, ← hev.pow_abs c, hΛG]
    field_simp
    try ring
  have heF : |trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / |c| ^ (p + q + w + w' + 2)|
      ≤ A * excited μ k c φ (i + 1) := by
    have h := abs_trc_conv_iter_le hr hF (i + v')
    rw [show i + v' + (i + v') + 1 = p + q + w' + 1 by omega, hσdef (i + v')] at h
    have hm := hmono v'
    rw [show i + 1 + v' = i + v' + 1 by ring] at hm
    rw [abs_div, abs_of_pos hcL, div_le_iff₀ hcL]
    calc _ ≤ A * |c| ^ w * (excited μ k c φ (i + v' + 1) * |c| ^ (2 * (i + v' + 1))) := h
      _ ≤ A * |c| ^ w * (excited μ k c φ (i + 1) * |c| ^ (2 * (i + v' + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (pow_nonneg hc.le _))
            (mul_nonneg hA0 hcw.le)
      _ = A * excited μ k c φ (i + 1) * |c| ^ (p + q + w + w' + 2) := by
          rw [show p + q + w + w' + 2 = w + 2 * (i + v' + 1) by omega, pow_add]; ring
  have heG : |trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / |c| ^ (p + q + w + w' + 2)|
      ≤ B * excited μ k c φ (i + 1) := by
    have h := abs_trc_conv_iter_le hr hG (i + v)
    rw [show i + v + (i + v) + 1 = p + q + w + 1 by omega, hσdef (i + v)] at h
    have hm := hmono v
    rw [show i + 1 + v = i + v + 1 by ring] at hm
    rw [abs_div, abs_of_pos hcL, div_le_iff₀ hcL]
    calc _ ≤ B * |c| ^ w' * (excited μ k c φ (i + v + 1) * |c| ^ (2 * (i + v + 1))) := h
      _ ≤ B * |c| ^ w' * (excited μ k c φ (i + 1) * |c| ^ (2 * (i + v + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (pow_nonneg hc.le _))
            (mul_nonneg hB0 hcw'.le)
      _ = B * excited μ k c φ (i + 1) * |c| ^ (p + q + w + w' + 2) := by
          rw [show p + q + w + w' + 2 = w' + 2 * (i + v + 1) by omega, pow_add]; ring
  have hα : |(∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w| ≤ A := by
    rw [abs_div, abs_of_pos hcw, div_le_iff₀ hcw]; exact abs_vac_le hφm hφb hφ1 hF
  have hβ : |(∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w'| ≤ B := by
    rw [abs_div, abs_of_pos hcw', div_le_iff₀ hcw']; exact abs_vac_le hφm hφb hφ1 hG
  -- the two-point trace, with the separated term apart
  have hev2 : Even (p + 1 + (q + 1)) := ⟨i + 1, by omega⟩
  have hcc : c ^ (p + 1) * c ^ (q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add, ← pow_add, hev2.pow_abs c]
  have hΛ2 : |c| ^ (p + q + w + w' + 2)
      = |c| ^ (p + 1) * |c| ^ (q + 1) * |c| ^ w * |c| ^ w' := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hT : trK μ k F G p q = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w
          * ((∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w')
        + ((c ^ (p + 1) * (∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2)
          + c ^ (q + 1) * (∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
            / |c| ^ (p + q + w + w' + 2))) := by
    rw [trK_decomp hφm hφb hφ1 hkm hkb hsym heig hF.bdd hG.bdd p q, hcc, hΛ2]
    field_simp
    try ring
  have I4 := abs_trK_le hr hrs hF hG p q i hi
  rw [hσdef i] at I4
  have hTb : |trK μ (rem k c φ) F G p q| / |c| ^ (p + q + w + w' + 2)
      ≤ A * B * excited μ k c φ (i + 1) := by
    rw [div_le_iff₀ hcL]
    calc _ ≤ _ := I4
      _ = A * B * excited μ k c φ (i + 1) * |c| ^ (p + q + w + w' + 2) := by
          rw [show p + q + w + w' + 2 = w + w' + 2 * (i + 1) by omega, pow_add, pow_add]; ring
  have he : |(c ^ (p + 1) * (∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2)|
      ≤ |c ^ (p + 1) * (∫ x, kernelFun F μ φ x
            * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)|
          / |c| ^ (p + q + w + w' + 2) + A * B * excited μ k c φ (i + 1) := by
    rw [add_div]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_div, abs_of_pos hcL]
    linarith
  -- assemble
  have key := conn_alg3 hcL (hexc0 _) (hmono (v + v')) hσ1 hα hβ heF heG
    (e := (c ^ (p + 1) * (∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2))
    (M := c ^ (q + 1) * (∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
            / |c| ^ (p + q + w + w' + 2))
  unfold connK
  rw [hT, hOF, hOG, hZ]
  calc _ ≤ _ := key
    _ ≤ _ := by linarith

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **Clustering of two kernel insertions in reflection form.** Under the hypotheses of
`OpenAIBridgeSlab.connK_le_excited`, with separations `p = 2a + j + 2`, `q = 2a + j' + 2`
(`j + j'` even) and `σ = σ_{(p+q)/2+1}`,

    |connK μ k F G w w' p q| ≤ (1/2)^⌊(j+1)/n⌋ √(R_F R_{Gᵀ}) + (1/2)^⌊(j'+1)/n⌋ √(R_{Fᵀ} R_G)
                                + 5 A B σ,

`R_F = refl μ k c φ F w a` the reflected reading of `F` at separation `2a + 2`. The two cross terms
of `connK_split` are `abs_cross_rp`; `1/(1+σ₀) ≤ 1`.

DERIVED: `5` is the constant of `connK_split`; `1/2` the contraction; `1` and `2` the offsets of
`iter`; `0` the excluded eigenvalue. -/
theorem connK_rp (hc0 : c ≠ 0) {F G : X → X → ℝ} {A B : ℝ} {w w' : ℕ}
    (hF : OpBd μ F (A * |c| ^ w)) (hG : OpBd μ G (B * |c| ^ w')) (hw : Even w) (hw' : Even w')
    (a j j' : ℕ) (hjj : Even (j + j'))
    (hσ1 : excited μ k c φ ((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) ≤ 1) :
    |connK μ k F G w w' (a + j + a + 2) (a + j' + a + 2)|
      ≤ (1 / 2) ^ ((j + 1) / n) * √(refl μ k c φ F w a * refl μ k c φ (tp G) w' a)
        + (1 / 2) ^ ((j' + 1) / n) * √(refl μ k c φ (tp F) w a * refl μ k c φ G w' a)
        + 5 * (A * B) * excited μ k c φ ((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) := by
  obtain ⟨CF, hCF⟩ := hF.bdd.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd.bdd
  have hpq : Even (a + j + a + 2 + (a + j' + a + 2)) := by
    obtain ⟨t, ht⟩ := hjj; exact ⟨2 * a + t + 2, by omega⟩
  have hsp := connK_split hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF hG hw hw'
    (a + j + a + 2) (a + j' + a + 2) hpq hσ1
  have hM : |c ^ (a + j' + a + 2 + 1) * (∫ x, kernelFun G μ φ x
        * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ (kernelFun (tp F) μ φ) x ∂μ)
        / |c| ^ (a + j + a + 2 + (a + j' + a + 2) + w + w' + 2)|
      ≤ (1 / 2) ^ ((j + 1) / n)
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1))
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1)) :=
    abs_cross_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 a j (by omega)
      (measurable_kf (μ := μ) (bdd_tp hF.bdd) hφm) (measurable_kf (μ := μ) hG.bdd hφm)
      (abs_kf_le (μ := μ) (fun x y => hCF y x) hφb) (abs_kf_le (μ := μ) hCG hφb)
  have hMq : |c ^ (a + j + a + 2 + 1) * (∫ x, kernelFun F μ φ x
        * kernelFun (iter μ (rem k c φ) (a + j' + a + 2)) μ (kernelFun (tp G) μ φ) x ∂μ)|
        / |c| ^ (a + j + a + 2 + (a + j' + a + 2) + w + w' + 2)
      ≤ (1 / 2) ^ ((j' + 1) / n)
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1))
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1)) := by
    have h : |c ^ (a + j + a + 2 + 1) * (∫ x, kernelFun F μ φ x
          * kernelFun (iter μ (rem k c φ) (a + j' + a + 2)) μ (kernelFun (tp G) μ φ) x ∂μ)
          / |c| ^ (a + j + a + 2 + (a + j' + a + 2) + w + w' + 2)|
        ≤ (1 / 2) ^ ((j' + 1) / n)
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1))
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1)) :=
      abs_cross_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 a j' (by omega)
        (measurable_kf (μ := μ) (bdd_tp hG.bdd) hφm) (measurable_kf (μ := μ) hF.bdd hφm)
        (abs_kf_le (μ := μ) (fun x y => hCG y x) hφb) (abs_kf_le (μ := μ) hCF hφb)
    rwa [abs_div, abs_of_pos (pow_pos (abs_pos.mpr hc0) _)] at h
  have hσ0 : 0 ≤ excited μ k c φ
      ((a + j + a + 2 + (a + j' + a + 2) + w + w') / 2 + 1) := by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  set M := c ^ (a + j' + a + 2 + 1) * (∫ x, kernelFun G μ φ x
        * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ (kernelFun (tp F) μ φ) x ∂μ)
        / |c| ^ (a + j + a + 2 + (a + j' + a + 2) + w + w' + 2) with hMdef
  have hdiv : |M / (1 + excited μ k c φ ((a + j + a + 2 + (a + j' + a + 2) + w + w') / 2 + 1))|
      ≤ |M| := by
    have hD : 0 < 1 + excited μ k c φ ((a + j + a + 2 + (a + j' + a + 2) + w + w') / 2 + 1) := by
      linarith
    rw [abs_div, abs_of_pos hD]
    exact div_le_self (abs_nonneg _) (by linarith)
  rw [Real.sqrt_mul (refl_nonneg _ _ _ _ _ _), Real.sqrt_mul (refl_nonneg _ _ _ _ _ _),
    sqrt_refl, sqrt_refl, sqrt_refl, sqrt_refl]
  calc |connK μ k F G w w' (a + j + a + 2) (a + j' + a + 2)|
      = |(connK μ k F G w w' (a + j + a + 2) (a + j' + a + 2)
          - M / (1 + excited μ k c φ ((a + j + a + 2 + (a + j' + a + 2) + w + w') / 2 + 1)))
        + M / (1 + excited μ k c φ ((a + j + a + 2 + (a + j' + a + 2) + w + w') / 2 + 1))| := by
        rw [sub_add_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hsp hdiv
    _ ≤ _ := add_le_add (add_le_add hMq le_rfl) hM
    _ = _ := by ring

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **Clustering of two slab insertions in reflection form, from the window of the seed.** With
the gap data and a level `j0` as in `OpenAIBridgeSlab.excited_le_slab`, for bounded measurable
kernels with `|F| ≤ A k^{∗w}`, `|G| ≤ B k^{∗w'}` (`w = 2v + 2`, `w' = 2v' + 2`), on the chain of
even length `L = p + q + 2 + w + w'` with `p = 2a + j + 2`, `q = 2a + j' + 2` and
`4(w + w') + 8n ≤ L`,

    |connK μ k F G w w' p q| ≤ (1/2)^⌊(j+1)/n⌋ √(R_F R_{Gᵀ}) + (1/2)^⌊(j'+1)/n⌋ √(R_{Fᵀ} R_G)
                                + 5 A B (1/2)^⌊((p+q)/2+1)/n⌋.

`opBd_of_le`, `excited_le_slab` and `connK_rp`.

DERIVED: `5` is the constant of `connK_split`; `4` and `8` the slab condition of
`excited_le_slab`; `3` the window exponent; `1/2` the contraction; `2` the doubled widths and the
offsets of `iter`; `1` the offset of `iter` and the least `j0`; `0` the signs and the excluded
eigenvalue. -/
theorem connK_rp_slab (hc0 : c ≠ 0) (hn0 : 0 < n) {a0 j0 L : ℕ} (hj0 : 1 ≤ j0)
    (hL4 : 2 * (2 * j0) ≤ L) (hhi : L ≤ 2 ^ (a0 + 3) * n)
    (hexc : excited μ k c φ j0 ≤ (1 / 2) ^ (2 ^ a0)) (hLe : Even L)
    {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (v v' : ℕ)
    (hFk : ∀ x y, |F x y| ≤ A * iter μ k (v + v + 1) x y)
    (hGk : ∀ x y, |G x y| ≤ B * iter μ k (v' + v' + 1) x y) (a j j' : ℕ)
    (hpq : a + j + a + 2 + (a + j' + a + 2) + 2 + (v + v + 2) + (v' + v' + 2) = L)
    (hW : 4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L) :
    |connK μ k F G (v + v + 2) (v' + v' + 2) (a + j + a + 2) (a + j' + a + 2)|
      ≤ (1 / 2) ^ ((j + 1) / n)
          * √(refl μ k c φ F (v + v + 2) a * refl μ k c φ (tp G) (v' + v' + 2) a)
        + (1 / 2) ^ ((j' + 1) / n)
          * √(refl μ k c φ (tp F) (v + v + 2) a * refl μ k c φ G (v' + v' + 2) a)
        + 5 * (A * B) * (1 / 2) ^ (((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) / n) := by
  have hF' : OpBd μ F (A * |c| ^ (v + v + 2)) := by
    have h := opBd_of_le hkm hC0 hkb hsym hF hA (v + v + 1) hFk
    rw [← hnorm, show v + v + 1 + 1 = v + v + 2 by omega] at h
    exact h
  have hG' : OpBd μ G (B * |c| ^ (v' + v' + 2)) := by
    have h := opBd_of_le hkm hC0 hkb hsym hG hB (v' + v' + 1) hGk
    rw [← hnorm, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at h
    exact h
  obtain ⟨L', hL'⟩ := hLe
  have hjj : Even (j + j') := ⟨L' - 2 * a - v - v' - 5, by omega⟩
  have hσ := excited_le_slab hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hn0 hj0 hL4 hhi hexc
    (ℓ := (a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) (W := (v + v + 2) + (v' + v' + 2))
    (by omega) hW
  have hσ1 := hσ.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have h := connK_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF' hG'
    ⟨v + 1, by ring⟩ ⟨v' + 1, by ring⟩ a j j' hjj hσ1
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have := mul_le_mul_of_nonneg_left hσ (by positivity : (0 : ℝ) ≤ 5 * (A * B))
  linarith

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The reflected reading is the torus correlation of an insertion with its reflection, up to
the wrap-around.** Under the hypotheses of `OpenAIBridgeSlab.connK_le_excited` for `F` and its
reflection `Fᵀ` (`OpBd.transpose`), at separation `p + 1 = 2a + 2` and `σ = σ_{(p+q)/2+1}`,

    |connK μ k F Fᵀ w w (2a+1) q − R_F(2a+2)| ≤ A² ((1/2)^⌊(q+1)/n⌋ + 6σ).

The separated term of `connK_split` is exactly `R_F` (`rpRead_eq`; `q + 1` is even); the factor
`1/(1+σ₀)` costs `R_F σ₀ ≤ A² σ` (`abs_integral_remFun_le` bounds `R_F ≤ A²`, and
`excited_le_of_le`); the opposite cross term is at most `A² (1/2)^⌊(q+1)/n⌋`.

DERIVED: `6 = 5 + 1` is the constant of `connK_split` and the factor `1/(1+σ₀)`; `1/2` the
contraction; `1` and `2` the offsets of `iter` and the square `A²`; `0` the excluded eigenvalue. -/
theorem connK_refl_read (hc0 : c ≠ 0) {F : X → X → ℝ} {A : ℝ} {w : ℕ}
    (hF : OpBd μ F (A * |c| ^ w)) (hw : Even w) (a q : ℕ) (hpq : Even (a + a + 1 + q))
    (hσ1 : excited μ k c φ ((a + a + 1 + q) / 2 + 1) ≤ 1) :
    |connK μ k F (tp F) w w (a + a + 1) q - refl μ k c φ F w a|
      ≤ A ^ 2 * ((1 / 2) ^ ((q + 1) / n) + 6 * excited μ k c φ ((a + a + 1 + q) / 2 + 1)) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hA0 : 0 ≤ A := nonneg_of_mul_pow hc0 hF.nonneg
  have hT := hF.transpose
  obtain ⟨CF, hCF⟩ := hF.bdd.bdd
  have hum := measurable_kf (μ := μ) (bdd_tp hF.bdd) hφm
  have hub : ∀ x, |kernelFun (tp F) μ φ x| ≤ CF * Bφ := abs_kf_le (fun x y => hCF y x) hφb
  have hsp := connK_split hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF hT hw hw
    (a + a + 1) q hpq hσ1
  obtain ⟨t, ht⟩ := hpq
  obtain ⟨v, hv⟩ := hw
  -- the separated term is the reflected reading
  have hq1 : Even (q + 1) := ⟨t - a, by omega⟩
  have hρ := rpRead_eq (μ := μ) hr hrs hum hub a
  have hM : c ^ (q + 1) * (∫ x, kernelFun (tp F) μ φ x
        * kernelFun (iter μ (rem k c φ) (a + a + 1)) μ (kernelFun (tp F) μ φ) x ∂μ)
        / |c| ^ (a + a + 1 + q + w + w + 2) = refl μ k c φ F w a := by
    unfold refl
    rw [← hρ, ← hq1.pow_abs c,
      show a + a + 1 + q + w + w + 2 = (q + 1) + 2 * (w + a + 1) by omega,
      pow_add |c| (q + 1) (2 * (w + a + 1)), mul_div_mul_left _ _ (pow_ne_zero _ hc.ne')]
  rw [hM] at hsp
  -- `R_F ≤ A²`
  have hρle : refl μ k c φ F w a ≤ A ^ 2 := by
    have h := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap (a + a + 1)
      hum hum hub hub hT.nonneg hT.nonneg (sq_kf_le hφm hφb hφ1 hT) (sq_kf_le hφm hφb hφ1 hT)
    rw [← hρ] at h
    have hcp : 0 < |c| ^ (2 * (w + a + 1)) := pow_pos hc _
    unfold refl
    rw [div_le_iff₀ hcp]
    have h1 : (1 / 2 : ℝ) ^ ((a + a + 1 + 1) / n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpos : 0 ≤ |c| ^ (a + a + 1 + 1) * (A * |c| ^ w) * (A * |c| ^ w) := by positivity
    calc rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)
        ≤ |rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)| := le_abs_self _
      _ ≤ (1 / 2) ^ ((a + a + 1 + 1) / n) * |c| ^ (a + a + 1 + 1) * (A * |c| ^ w)
          * (A * |c| ^ w) := h
      _ ≤ 1 * |c| ^ (a + a + 1 + 1) * (A * |c| ^ w) * (A * |c| ^ w) := by
          have := mul_le_mul_of_nonneg_right h1 hpos
          linarith
      _ = A ^ 2 * |c| ^ (2 * (w + a + 1)) := by
          rw [show 2 * (w + a + 1) = (a + a + 1 + 1) + w + w by omega, pow_add, pow_add]; ring
  have hρ0 := refl_nonneg (μ := μ) k c φ F w a
  -- the factor `1 / (1 + σ₀)`
  set σ := excited μ k c φ ((a + a + 1 + q) / 2 + 1) with hσdef
  set σ0 := excited μ k c φ ((a + a + 1 + q + w + w) / 2 + 1) with hσ0def
  have hσ00 : 0 ≤ σ0 := by
    rw [hσ0def]; unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have hσ0σ : σ0 ≤ σ := by
    have h := excited_le_of_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0
      ((a + a + 1 + q) / 2 + 1) (v + v) (by omega)
    rw [hσ0def, hσdef, show (a + a + 1 + q + w + w) / 2 + 1 = (a + a + 1 + q) / 2 + 1 + (v + v)
      by omega]
    exact h
  have hfac : |refl μ k c φ F w a / (1 + σ0) - refl μ k c φ F w a| ≤ A ^ 2 * σ := by
    have hD : 0 < 1 + σ0 := by linarith
    have hD' : 1 + σ0 ≠ 0 := hD.ne'
    rw [show refl μ k c φ F w a / (1 + σ0) - refl μ k c φ F w a
      = -(refl μ k c φ F w a * σ0 / (1 + σ0)) by field_simp; ring, abs_neg,
      abs_of_nonneg (div_nonneg (mul_nonneg hρ0 hσ00) hD.le)]
    calc refl μ k c φ F w a * σ0 / (1 + σ0) ≤ refl μ k c φ F w a * σ0 :=
          div_le_self (mul_nonneg hρ0 hσ00) (by linarith)
      _ ≤ A ^ 2 * σ := mul_le_mul hρle hσ0σ hσ00 (sq_nonneg _)
  -- the opposite cross term
  have hq : |c ^ (a + a + 1 + 1) * (∫ x, kernelFun F μ φ x
        * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp (tp F)) μ φ) x ∂μ)|
        / |c| ^ (a + a + 1 + q + w + w + 2) ≤ A ^ 2 * (1 / 2) ^ ((q + 1) / n) := by
    have I2 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap q
      (measurable_kf (μ := μ) hF.bdd hφm) (measurable_kf (μ := μ) (bdd_tp hT.bdd) hφm)
      (abs_kf_le (μ := μ) hCF hφb) (abs_kf_le (μ := μ) (fun x y => hCF x y) hφb)
      hF.nonneg hT.nonneg (sq_kf_le hφm hφb hφ1 hF) (sq_kf_le hφm hφb hφ1 hT.transpose)
    have hcL : 0 < |c| ^ (a + a + 1 + q + w + w + 2) := pow_pos hc _
    rw [div_le_iff₀ hcL, abs_mul, abs_pow]
    calc |c| ^ (a + a + 1 + 1) * |∫ x, kernelFun F μ φ x
          * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp (tp F)) μ φ) x ∂μ|
        ≤ |c| ^ (a + a + 1 + 1) * ((1 / 2) ^ ((q + 1) / n) * |c| ^ (q + 1) * (A * |c| ^ w)
          * (A * |c| ^ w)) := mul_le_mul_of_nonneg_left I2 (pow_nonneg hc.le _)
      _ = A ^ 2 * (1 / 2) ^ ((q + 1) / n) * |c| ^ (a + a + 1 + q + w + w + 2) := by
          rw [show a + a + 1 + q + w + w + 2 = (a + a + 1 + 1) + (q + 1) + w + w by omega,
            pow_add, pow_add, pow_add]
          ring
  have hs' : |connK μ k F (tp F) w w (a + a + 1) q - refl μ k c φ F w a / (1 + σ0)|
      ≤ A ^ 2 * (1 / 2) ^ ((q + 1) / n) + 5 * (A * A) * σ := by
    linarith [hsp, hq]
  calc |connK μ k F (tp F) w w (a + a + 1) q - refl μ k c φ F w a|
      = |(connK μ k F (tp F) w w (a + a + 1) q - refl μ k c φ F w a / (1 + σ0))
          + (refl μ k c φ F w a / (1 + σ0) - refl μ k c φ F w a)| := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := abs_add_le _ _
    _ ≤ A ^ 2 * (1 / 2) ^ ((q + 1) / n) + 5 * (A * A) * σ + A ^ 2 * σ := add_le_add hs' hfac
    _ = _ := by ring

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The gap bound in Hilbert–Schmidt form**: `hs(P ∗ R^{m+1}) ≤ ((1/2)^⌊(m+1)/n⌋ |c|^{m+1})² hs(P)`
for a bounded kernel `P`, row by row (`OpenAIBridgeCluster.sq_integral_remFun_le`, `R^{m+1}`
symmetric).

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter`; `2` the
squares. -/
theorem hs_conv_rem_le {P : X → X → ℝ} (hP : Bdd P) (m : ℕ) :
    hs μ (conv μ P (iter μ (rem k c φ) m))
      ≤ ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * hs μ P := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hJ : Bdd (iter μ (rem k c φ) m) := hr.iter m
  have hJs := CyclicKernel.iter_symm (μ := μ) hr hrs m
  obtain ⟨CP, hCP⟩ := hP.bdd
  have hPJ : Bdd (conv μ P (iter μ (rem k c φ) m)) := hP.conv hJ
  obtain ⟨CPJ, hCPJ⟩ := hPJ.bdd
  have hpt : ∀ x z, conv μ P (iter μ (rem k c φ) m) x z
      = kernelFun (iter μ (rem k c φ) m) μ (P x) z := by
    intro x z; unfold conv kernelFun; congr 1; funext y; rw [hJs y z, mul_comm]
  have hrow : ∀ x, ∫ z, conv μ P (iter μ (rem k c φ) m) x z ^ 2 ∂μ
      ≤ ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * ∫ z, P x z ^ 2 ∂μ := by
    intro x
    simp_rw [hpt x]
    exact sq_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap m (hP.row x) (hCP x)
  unfold hs
  rw [← integral_const_mul]
  refine integral_mono ?_ ?_ hrow
  · exact integrable_of_bdd (measurable_integral_right (hPJ.meas.pow_const 2)) (C := CPJ ^ 2)
      (fun x => abs_integral_le fun y => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCPJ x y) 2)
  · exact (integrable_of_bdd (measurable_integral_right (hP.meas.pow_const 2)) (C := CP ^ 2)
      (fun x => abs_integral_le fun y => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCP x y) 2)).const_mul _

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The excited–excited trace in reflection form**: if `L = (j+1) + (j'+1) + W + W'` with
`W = w + 2a + 2`, `W' = w' + 2a + 2`,

    |Tr(F R^{2a+j+3} G R^{2a+j'+3})| / |c|^L ≤ (1/2)^⌊(j+1)/n⌋ (1/2)^⌊(j'+1)/n⌋ √H_F √H_G,

`H_F = hsRead F w a`. `trK_sand`, `abs_trc_le`, `hs_conv_rem_le`.

DERIVED: `1/2` is the contraction; `1`, `2` the offsets of `iter`; `0` the excluded eigenvalue. -/
theorem abs_trK_hs (hc0 : c ≠ 0) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) (a j j' : ℕ)
    {w w' L : ℕ} (hL : L = (j + 1) + (j' + 1) + (w + a + a + 2) + (w' + a + a + 2)) :
    |trK μ (rem k c φ) F G (a + j + a + 2) (a + j' + a + 2)| / |c| ^ L
      ≤ (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n) * √(hsRead μ k c φ F w a)
        * √(hsRead μ k c φ G w' a) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcL : 0 < |c| ^ L := pow_pos hc L
  have hA : Bdd (iter μ (rem k c φ) a) := hr.iter a
  have hP : Bdd (conv μ (iter μ (rem k c φ) a) (conv μ F (iter μ (rem k c φ) a))) :=
    hA.conv (hF.conv hA)
  have hQ : Bdd (conv μ (iter μ (rem k c φ) a) (conv μ G (iter μ (rem k c φ) a))) :=
    hA.conv (hG.conv hA)
  have hPJ : Bdd (conv μ (conv μ (iter μ (rem k c φ) a) (conv μ F (iter μ (rem k c φ) a)))
      (iter μ (rem k c φ) j)) := hP.conv (hr.iter j)
  have hQJ : Bdd (conv μ (conv μ (iter μ (rem k c φ) a) (conv μ G (iter μ (rem k c φ) a)))
      (iter μ (rem k c φ) j')) := hQ.conv (hr.iter j')
  have h1 := abs_trc_le (μ := μ) hQJ hPJ
  have hsq : ∀ {Y : X → X → ℝ} (hY : Bdd Y) (m : ℕ),
      √(hs μ (conv μ Y (iter μ (rem k c φ) m)))
        ≤ (1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1) * √(hs μ Y) := by
    intro Y hY m
    have h := Real.sqrt_le_sqrt (hs_conv_rem_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hY m)
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h
  have h2 := hsq hQ j'
  have h3 := hsq hP j
  rw [trK_sand hr hF hG a j j', sqrt_hsRead, sqrt_hsRead, div_le_iff₀ hcL]
  have hγ : 0 ≤ (1 / 2 : ℝ) ^ ((j' + 1) / n) * |c| ^ (j' + 1) := by positivity
  calc _ ≤ _ := h1
    _ ≤ ((1 / 2) ^ ((j' + 1) / n) * |c| ^ (j' + 1)
          * √(hs μ (conv μ (iter μ (rem k c φ) a) (conv μ G (iter μ (rem k c φ) a)))))
        * ((1 / 2) ^ ((j + 1) / n) * |c| ^ (j + 1)
          * √(hs μ (conv μ (iter μ (rem k c φ) a) (conv μ F (iter μ (rem k c φ) a))))) :=
        mul_le_mul h2 h3 (Real.sqrt_nonneg _) (mul_nonneg hγ (Real.sqrt_nonneg _))
    _ = _ := by
        have hW : |c| ^ (w + a + a + 2) ≠ 0 := pow_ne_zero _ hc.ne'
        have hW' : |c| ^ (w' + a + a + 2) ≠ 0 := pow_ne_zero _ hc.ne'
        rw [hL, pow_add |c| ((j + 1) + (j' + 1) + (w + a + a + 2)) (w' + a + a + 2),
          pow_add |c| ((j + 1) + (j' + 1)) (w + a + a + 2), pow_add |c| (j + 1) (j' + 1)]
        field_simp
        try ring

include hφm hφb hkm hkb in
/-- **A one-point excited trace in reflection form**: if `L = (w + 2a + 2) + (l + 1)`,

    |Tr(F R^{2a+l+3})| / |c|^L ≤ √H_F √σ_{l+1},

`trc_sand`, `abs_trc_le`, and `hs(R^{l+1}) = σ_{l+1} |c|^{2(l+1)}`.

DERIVED: `1`, `2` are the offsets of `iter` and the square; `0` the excluded eigenvalue. -/
theorem abs_trOne_hs (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (a l : ℕ) {w L : ℕ}
    (hL : L = (w + a + a + 2) + (l + 1)) :
    |trc μ (conv μ F (iter μ (rem k c φ) (a + l + a + 2)))| / |c| ^ L
      ≤ √(hsRead μ k c φ F w a) * √(excited μ k c φ (l + 1)) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcL : 0 < |c| ^ L := pow_pos hc L
  have hA : Bdd (iter μ (rem k c φ) a) := hr.iter a
  have hP : Bdd (conv μ (iter μ (rem k c φ) a) (conv μ F (iter μ (rem k c φ) a))) :=
    hA.conv (hF.conv hA)
  have h1 := abs_trc_le (μ := μ) hP (hr.iter (μ := μ) l)
  have hσ : hs μ (iter μ (rem k c φ) l) = excited μ k c φ (l + 1) * (|c| ^ (l + 1)) ^ 2 := by
    unfold excited
    rw [Nat.add_sub_cancel, ← pow_mul, mul_comm (l + 1) 2,
      div_mul_cancel₀ _ (pow_ne_zero _ hc.ne')]
  have hσ0 : 0 ≤ excited μ k c φ (l + 1) := by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  rw [hσ, Real.sqrt_mul hσ0, Real.sqrt_sq (pow_nonneg hc.le _)] at h1
  rw [trc_sand hr hF a l, sqrt_hsRead, div_le_iff₀ hcL]
  calc _ ≤ _ := h1
    _ = _ := by
        have hW : |c| ^ (w + a + a + 2) ≠ 0 := pow_ne_zero _ hc.ne'
        rw [hL, pow_add |c| (w + a + a + 2) (l + 1)]
        field_simp

/-- The real-number bookkeeping of the trace ratio without sup bounds: with
`Z = Λ(1+σ₀)`, `Λ > 0`, `σ₀ ≥ 0`, the connected ratio is within
`|e| + |α||β|σ₀ + |α||e_b| + |β||e_a| + |e_a||e_b|` of zero.

DERIVED: `1` is the vacuum's own weight in `Z`; `2` the square of `1 + σ₀`; `0` the signs. -/
theorem conn_alg4 {Λ σ0 α β ea eb e : ℝ} (hΛ : 0 < Λ) (hσ0 : 0 ≤ σ0) :
    |Λ * (α * β + e) / (Λ * (1 + σ0))
        - Λ * (α + ea) / (Λ * (1 + σ0)) * (Λ * (β + eb) / (Λ * (1 + σ0)))|
      ≤ |e| + |α| * |β| * σ0 + |α| * |eb| + |β| * |ea| + |ea| * |eb| := by
  have hD : 0 < 1 + σ0 := by linarith
  have hΛ' : Λ ≠ 0 := hΛ.ne'
  have hD' : 1 + σ0 ≠ 0 := hD.ne'
  have key : Λ * (α * β + e) / (Λ * (1 + σ0))
        - Λ * (α + ea) / (Λ * (1 + σ0)) * (Λ * (β + eb) / (Λ * (1 + σ0)))
      = e / (1 + σ0) + (α * β * σ0 - α * eb - β * ea - ea * eb) / (1 + σ0) ^ 2 := by
    field_simp; ring
  rw [key]
  have h1 : |e / (1 + σ0)| ≤ |e| := by
    rw [abs_div, abs_of_pos hD]; exact div_le_self (abs_nonneg _) (by linarith)
  have h2 : |α * β * σ0 - α * eb - β * ea - ea * eb|
      ≤ |α| * |β| * σ0 + |α| * |eb| + |β| * |ea| + |ea| * |eb| := by
    have s1 := abs_sub (α * β * σ0 - α * eb - β * ea) (ea * eb)
    have s2 := abs_sub (α * β * σ0 - α * eb) (β * ea)
    have s3 := abs_sub (α * β * σ0) (α * eb)
    have t1 : |α * β * σ0| = |α| * |β| * σ0 := by rw [abs_mul, abs_mul, abs_of_nonneg hσ0]
    have t2 : |α * eb| = |α| * |eb| := abs_mul _ _
    have t3 : |β * ea| = |β| * |ea| := abs_mul _ _
    have t4 : |ea * eb| = |ea| * |eb| := abs_mul _ _
    linarith
  have h3 : |(α * β * σ0 - α * eb - β * ea - ea * eb) / (1 + σ0) ^ 2|
      ≤ |α| * |β| * σ0 + |α| * |eb| + |β| * |ea| + |ea| * |eb| := by
    rw [abs_div, abs_of_pos (pow_pos hD 2)]
    exact (div_le_self (abs_nonneg _) (one_le_pow₀ (by linarith))).trans h2
  calc _ ≤ |e / (1 + σ0)| + |(α * β * σ0 - α * eb - β * ea - ea * eb) / (1 + σ0) ^ 2| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The connected correlation of two kernel insertions in reflection form, wrap-around
included.** For bounded measurable kernels `F`, `G` covering `w`, `w'` steps (`w`, `w'` even), on
the periodic chain of `L = p + q + 2 + w + w'` copies of `k` with `p = 2a + j + 2`,
`q = 2a + j' + 2`, `p + q` even and `σ = σ_{(p+q)/2+1} ≤ 1`,

    |connK μ k F G w w' p q|
      ≤ (1/2)^⌊(j+1)/n⌋ √(R_F R_{Gᵀ}) + (1/2)^⌊(j'+1)/n⌋ √(R_{Fᵀ} R_G)
        + (1/2)^⌊(j+1)/n⌋ (1/2)^⌊(j'+1)/n⌋ √(H_F H_G)
        + (|α_F||α_G| + |α_F| √H_G + |α_G| √H_F + √(H_F H_G)) √σ,

`R = refl` the reflected readings, `H = hsRead` the Hilbert–Schmidt reflected readings and
`α = vacRead` the vacuum readings. No sup bound of `F` or `G` enters. The trace ratio splits at the
vacuum (`trK_decomp`, `trOne_decomp`, `trPow_even`, `conn_alg4`): the two separated terms are
`abs_cross_rp`, the excited–excited trace is `abs_trK_hs`, the one-point excited traces are
`abs_trOne_hs`, and `σ₀ ≤ σ ≤ √σ`.

DERIVED: `1/2` is the contraction; `1` and `2` the offsets of `iter`, the halving of the even
`p + q` and the cap on `σ`; `0` the excluded eigenvalue. -/
theorem connK_rp_full (hc0 : c ≠ 0) {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {w w' : ℕ}
    (hw : Even w) (hw' : Even w') (a j j' : ℕ) {p q : ℕ} (hp : p = a + j + a + 2)
    (hq : q = a + j' + a + 2) (hpq : Even (p + q))
    (hσ1 : excited μ k c φ ((p + q) / 2 + 1) ≤ 1) :
    |connK μ k F G w w' p q|
      ≤ (1 / 2) ^ ((j + 1) / n) * √(refl μ k c φ F w a * refl μ k c φ (tp G) w' a)
        + (1 / 2) ^ ((j' + 1) / n) * √(refl μ k c φ (tp F) w a * refl μ k c φ G w' a)
        + (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n)
          * √(hsRead μ k c φ F w a * hsRead μ k c φ G w' a)
        + (|vacRead μ c φ F w| * |vacRead μ c φ G w'|
            + |vacRead μ c φ F w| * √(hsRead μ k c φ G w' a)
            + |vacRead μ c φ G w'| * √(hsRead μ k c φ F w a)
            + √(hsRead μ k c φ F w a * hsRead μ k c φ G w' a))
          * √(excited μ k c φ ((p + q) / 2 + 1)) := by
  obtain ⟨i, hi⟩ := hpq
  obtain ⟨v, hv⟩ := hw
  obtain ⟨v', hv'⟩ := hw'
  have hi2 : (p + q) / 2 = i := by omega
  rw [hi2] at hσ1 ⊢
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcne : |c| ≠ 0 := hc.ne'
  have hcw : 0 < |c| ^ w := pow_pos hc w
  have hcw' : 0 < |c| ^ w' := pow_pos hc w'
  have hcwne : |c| ^ w ≠ 0 := hcw.ne'
  have hcwne' : |c| ^ w' ≠ 0 := hcw'.ne'
  have hcL : 0 < |c| ^ (p + q + w + w' + 2) := pow_pos hc _
  have hcLne : |c| ^ (p + q + w + w' + 2) ≠ 0 := hcL.ne'
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  have hσdef : ∀ j, hs μ (iter μ (rem k c φ) j)
      = excited μ k c φ (j + 1) * |c| ^ (2 * (j + 1)) := by
    intro j; unfold excited; rw [Nat.add_sub_cancel, div_mul_cancel₀ _ (pow_ne_zero _ hcne)]
  have hexc0 : ∀ j, 0 ≤ excited μ k c φ j := fun j => by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have hmono : ∀ l, excited μ k c φ (i + 1 + l) ≤ excited μ k c φ (i + 1) := fun l =>
    excited_le_of_le hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 (i + 1) l (by omega)
  -- `σ₀ ≤ σ ≤ √σ`
  have hsq1 : √(excited μ k c φ (i + 1)) ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ1
  have hσsq : excited μ k c φ (i + 1) ≤ √(excited μ k c φ (i + 1)) :=
    calc excited μ k c φ (i + 1)
        = √(excited μ k c φ (i + 1)) * √(excited μ k c φ (i + 1)) :=
          (Real.mul_self_sqrt (hexc0 _)).symm
      _ ≤ √(excited μ k c φ (i + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hσ0le : excited μ k c φ (i + 1 + (v + v')) ≤ √(excited μ k c φ (i + 1)) :=
    (hmono _).trans hσsq
  -- the partition function
  have hZ : trPow μ k (p + q + w + w' + 1)
      = |c| ^ (p + q + w + w' + 2) * (1 + excited μ k c φ (i + 1 + (v + v'))) := by
    have e1 : p + q + w + w' + 1 = (i + v + v') + (i + v + v') + 1 := by omega
    have hev : Even (i + v + v' + (i + v + v') + 2) := ⟨i + v + v' + 1, by ring⟩
    rw [e1, trPow_even hφm hφb hφ1 hkm hkb hsym heig (i + v + v'), hσdef (i + v + v'),
      ← hev.pow_abs c, show p + q + w + w' + 2 = i + v + v' + (i + v + v') + 2 by omega,
      show 2 * (i + v + v' + 1) = i + v + v' + (i + v + v') + 2 by ring,
      show i + v + v' + 1 = i + 1 + (v + v') by ring]
    ring
  -- the one-point traces
  have hOF : trOne μ k F (p + q + w' + 1) = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w
        + trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / |c| ^ (p + q + w + w' + 2)) := by
    have hev : Even (p + q + w' + 1 + 1) := ⟨i + v' + 1, by omega⟩
    have hΛF : |c| ^ (p + q + w + w' + 2) = |c| ^ (p + q + w' + 1 + 1) * |c| ^ w := by
      rw [← pow_add]; congr 1; omega
    rw [trOne_decomp hφm hφb hφ1 hkm hkb hsym heig hF, ← hev.pow_abs c, hΛF]
    field_simp
    try ring
  have hOG : trOne μ k G (p + q + w + 1) = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w'
        + trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / |c| ^ (p + q + w + w' + 2)) := by
    have hev : Even (p + q + w + 1 + 1) := ⟨i + v + 1, by omega⟩
    have hΛG : |c| ^ (p + q + w + w' + 2) = |c| ^ (p + q + w + 1 + 1) * |c| ^ w' := by
      rw [← pow_add]; congr 1; omega
    rw [trOne_decomp hφm hφb hφ1 hkm hkb hsym heig hG, ← hev.pow_abs c, hΛG]
    field_simp
    try ring
  -- the two-point trace
  have hev2 : Even (p + 1 + (q + 1)) := ⟨i + 1, by omega⟩
  have hcc : c ^ (p + 1) * c ^ (q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add, ← pow_add, hev2.pow_abs c]
  have hΛ2 : |c| ^ (p + q + w + w' + 2)
      = |c| ^ (p + 1) * |c| ^ (q + 1) * |c| ^ w * |c| ^ w' := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hT : trK μ k F G p q = |c| ^ (p + q + w + w' + 2)
      * ((∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w
          * ((∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w')
        + (c ^ (p + 1) * (∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
            + c ^ (q + 1) * (∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2)) := by
    rw [trK_decomp hφm hφb hφ1 hkm hkb hsym heig hF hG p q, hcc, hΛ2]
    field_simp
    try ring
  -- the separated terms
  have hMp : |c ^ (q + 1) * (∫ x, kernelFun G μ φ x
        * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ)
        / |c| ^ (p + q + w + w' + 2)|
      ≤ (1 / 2) ^ ((j + 1) / n)
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1))
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1)) := by
    have h : |c ^ (q + 1) * (∫ x, kernelFun G μ φ x
          * kernelFun (iter μ (rem k c φ) (a + j + a + 2)) μ (kernelFun (tp F) μ φ) x ∂μ)
          / |c| ^ (p + q + w + w' + 2)|
        ≤ (1 / 2) ^ ((j + 1) / n)
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1))
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1)) :=
      abs_cross_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 a j (by omega)
        (measurable_kf (μ := μ) (bdd_tp hF) hφm) (measurable_kf (μ := μ) hG hφm)
        (abs_kf_le (μ := μ) (fun x y => hCF y x) hφb) (abs_kf_le (μ := μ) hCG hφb)
    rw [← hp] at h
    exact h
  have hMq : |c ^ (p + 1) * (∫ x, kernelFun F μ φ x
        * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ)
        / |c| ^ (p + q + w + w' + 2)|
      ≤ (1 / 2) ^ ((j' + 1) / n)
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1))
        * (√(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1)) := by
    have h : |c ^ (p + 1) * (∫ x, kernelFun F μ φ x
          * kernelFun (iter μ (rem k c φ) (a + j' + a + 2)) μ (kernelFun (tp G) μ φ) x ∂μ)
          / |c| ^ (p + q + w + w' + 2)|
        ≤ (1 / 2) ^ ((j' + 1) / n)
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1))
          * (√(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1)) :=
      abs_cross_rp hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 a j' (by omega)
        (measurable_kf (μ := μ) (bdd_tp hG) hφm) (measurable_kf (μ := μ) hF hφm)
        (abs_kf_le (μ := μ) (fun x y => hCG y x) hφb) (abs_kf_le (μ := μ) hCF hφb)
    rw [← hq] at h
    exact h
  -- the excited–excited trace
  have hTb : |trK μ (rem k c φ) F G p q| / |c| ^ (p + q + w + w' + 2)
      ≤ (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n) * √(hsRead μ k c φ F w a)
        * √(hsRead μ k c φ G w' a) := by
    have h := abs_trK_hs hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF hG a j j'
      (w := w) (w' := w') (L := p + q + w + w' + 2) (by omega)
    rw [← hp, ← hq] at h
    exact h
  -- the one-point excited traces
  have hea : |trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / |c| ^ (p + q + w + w' + 2)|
      ≤ √(hsRead μ k c φ F w a) * √(excited μ k c φ (i + 1)) := by
    have h := abs_trOne_hs (μ := μ) hφm hφb hkm hkb hc0 hF a
      (p + q + w' - 2 * a - 1) (w := w) (L := p + q + w + w' + 2) (by omega)
    rw [show a + (p + q + w' - 2 * a - 1) + a + 2 = p + q + w' + 1 by omega] at h
    have hm := hmono (p + q + w' - 2 * a - 1 - i)
    rw [show i + 1 + (p + q + w' - 2 * a - 1 - i) = p + q + w' - 2 * a - 1 + 1 by omega] at hm
    rw [abs_div, abs_of_pos hcL]
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _))
  have heb : |trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / |c| ^ (p + q + w + w' + 2)|
      ≤ √(hsRead μ k c φ G w' a) * √(excited μ k c φ (i + 1)) := by
    have h := abs_trOne_hs (μ := μ) hφm hφb hkm hkb hc0 hG a
      (p + q + w - 2 * a - 1) (w := w') (L := p + q + w + w' + 2) (by omega)
    rw [show a + (p + q + w - 2 * a - 1) + a + 2 = p + q + w + 1 by omega] at h
    have hm := hmono (p + q + w - 2 * a - 1 - i)
    rw [show i + 1 + (p + q + w - 2 * a - 1 - i) = p + q + w - 2 * a - 1 + 1 by omega] at hm
    rw [abs_div, abs_of_pos hcL]
    exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _))
  -- assemble
  unfold connK vacRead
  rw [hT, hOF, hOG, hZ, Real.sqrt_mul (refl_nonneg _ _ _ _ _ _),
    Real.sqrt_mul (refl_nonneg _ _ _ _ _ _), Real.sqrt_mul (hsRead_nonneg _ _ _ _ _ _),
    sqrt_refl, sqrt_refl, sqrt_refl, sqrt_refl]
  refine (conn_alg4 hcL (hexc0 _)).trans ?_
  set Λ := |c| ^ (p + q + w + w' + 2) with hΛ
  set α := (∫ x, kernelFun F μ φ x * φ x ∂μ) / |c| ^ w with hα
  set β := (∫ x, kernelFun G μ φ x * φ x ∂μ) / |c| ^ w' with hβ
  set Xq := ∫ x, kernelFun F μ φ x
      * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ with hXq
  set Xp := ∫ x, kernelFun G μ φ x
      * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ with hXp
  set T := trK μ (rem k c φ) F G p q with hTdef
  set ea := trc μ (conv μ F (iter μ (rem k c φ) (p + q + w' + 1))) / Λ with hea'
  set eb := trc μ (conv μ G (iter μ (rem k c φ) (p + q + w + 1))) / Λ with heb'
  set s := √(excited μ k c φ (i + 1)) with hs'
  set σ0 := excited μ k c φ (i + 1 + (v + v')) with hσ0'
  set hF' := √(hsRead μ k c φ F w a) with hhF
  set hG' := √(hsRead μ k c φ G w' a) with hhG
  set rF := √(rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)) / |c| ^ (w + a + 1) with hrF
  set rTG := √(rpRead μ (rem k c φ) a (kernelFun (tp (tp G)) μ φ)) / |c| ^ (w' + a + 1)
    with hrTG
  set rTF := √(rpRead μ (rem k c φ) a (kernelFun (tp (tp F)) μ φ)) / |c| ^ (w + a + 1)
    with hrTF
  set rG := √(rpRead μ (rem k c φ) a (kernelFun (tp G) μ φ)) / |c| ^ (w' + a + 1) with hrG
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hF0 : 0 ≤ hF' := Real.sqrt_nonneg _
  have hG0 : 0 ≤ hG' := Real.sqrt_nonneg _
  have he : |(c ^ (p + 1) * Xq + c ^ (q + 1) * Xp + T) / Λ|
      ≤ |c ^ (p + 1) * Xq / Λ| + |c ^ (q + 1) * Xp / Λ| + |T| / Λ := by
    rw [add_div, add_div]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_div T, abs_of_pos hcL]
  have P1 : |α| * |β| * σ0 ≤ |α| * |β| * s :=
    mul_le_mul_of_nonneg_left hσ0le (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have P2 : |α| * |eb| ≤ |α| * (hG' * s) := mul_le_mul_of_nonneg_left heb (abs_nonneg _)
  have P3 : |β| * |ea| ≤ |β| * (hF' * s) := mul_le_mul_of_nonneg_left hea (abs_nonneg _)
  have P4 : |ea| * |eb| ≤ hF' * hG' * s := by
    calc |ea| * |eb| ≤ (hF' * s) * (hG' * s) :=
          mul_le_mul hea heb (abs_nonneg _) (mul_nonneg hF0 hs0)
      _ = hF' * hG' * (s * s) := by ring
      _ ≤ hF' * hG' * (s * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq1 hs0) (mul_nonneg hF0 hG0)
      _ = hF' * hG' * s := by ring
  have key : |(c ^ (p + 1) * Xq + c ^ (q + 1) * Xp + T) / Λ| + |α| * |β| * σ0 + |α| * |eb|
        + |β| * |ea| + |ea| * |eb|
      ≤ (1 / 2) ^ ((j' + 1) / n) * rTF * rG + (1 / 2) ^ ((j + 1) / n) * rTG * rF
        + (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n) * hF' * hG'
        + |α| * |β| * s + |α| * (hG' * s) + |β| * (hF' * s) + hF' * hG' * s := by
    linarith
  refine key.trans (le_of_eq ?_)
  ring

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The connected correlation of two slab insertions in reflection form, from the window of the
seed, wrap-around included.** With the gap data and a level `j0` as in
`OpenAIBridgeSlab.excited_le_slab`, for bounded measurable kernels `F`, `G` covering
`w = 2v + 2`, `w' = 2v' + 2` steps, on the chain of even length `L = p + q + 2 + w + w'` with
`p = 2a + j + 2`, `q = 2a + j' + 2` and `4(w + w') + 8n ≤ L`, the bound of `connK_rp_full` holds
with `√σ` replaced by `√((1/2)^⌊((p+q)/2+1)/n⌋)`. No sup bound enters.

DERIVED: `4` and `8` are the slab condition of `excited_le_slab`; `3` the window exponent; `1/2`
the contraction; `2` the doubled widths and the offsets of `iter`; `1` the offset of `iter` and
the least `j0`; `0` the signs and the excluded eigenvalue. -/
theorem connK_rp_full_slab (hc0 : c ≠ 0) (hn0 : 0 < n) {a0 j0 L : ℕ} (hj0 : 1 ≤ j0)
    (hL4 : 2 * (2 * j0) ≤ L) (hhi : L ≤ 2 ^ (a0 + 3) * n)
    (hexc : excited μ k c φ j0 ≤ (1 / 2) ^ (2 ^ a0)) (hLe : Even L)
    {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) (v v' a j j' : ℕ)
    (hpq : a + j + a + 2 + (a + j' + a + 2) + 2 + (v + v + 2) + (v' + v' + 2) = L)
    (hW : 4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L) :
    |connK μ k F G (v + v + 2) (v' + v' + 2) (a + j + a + 2) (a + j' + a + 2)|
      ≤ (1 / 2) ^ ((j + 1) / n)
          * √(refl μ k c φ F (v + v + 2) a * refl μ k c φ (tp G) (v' + v' + 2) a)
        + (1 / 2) ^ ((j' + 1) / n)
          * √(refl μ k c φ (tp F) (v + v + 2) a * refl μ k c φ G (v' + v' + 2) a)
        + (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n)
          * √(hsRead μ k c φ F (v + v + 2) a * hsRead μ k c φ G (v' + v' + 2) a)
        + (|vacRead μ c φ F (v + v + 2)| * |vacRead μ c φ G (v' + v' + 2)|
            + |vacRead μ c φ F (v + v + 2)| * √(hsRead μ k c φ G (v' + v' + 2) a)
            + |vacRead μ c φ G (v' + v' + 2)| * √(hsRead μ k c φ F (v + v + 2) a)
            + √(hsRead μ k c φ F (v + v + 2) a * hsRead μ k c φ G (v' + v' + 2) a))
          * √((1 / 2) ^ (((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) / n)) := by
  obtain ⟨L', hL'⟩ := hLe
  have hσ := excited_le_slab hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hn0 hj0 hL4 hhi hexc
    (ℓ := (a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) (W := (v + v + 2) + (v' + v' + 2))
    (by omega) hW
  have hσ1 := hσ.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have h := connK_rp_full hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF hG
    (w := v + v + 2) (w' := v' + v' + 2) ⟨v + 1, by ring⟩ ⟨v' + 1, by ring⟩ a j j' rfl rfl ⟨L' - v - v' - 3, by omega⟩ hσ1
  have hcoef : 0 ≤ |vacRead μ c φ F (v + v + 2)| * |vacRead μ c φ G (v' + v' + 2)|
      + |vacRead μ c φ F (v + v + 2)| * √(hsRead μ k c φ G (v' + v' + 2) a)
      + |vacRead μ c φ G (v' + v' + 2)| * √(hsRead μ k c φ F (v + v + 2) a)
      + √(hsRead μ k c φ F (v + v + 2) a * hsRead μ k c φ G (v' + v' + 2) a) := by positivity
  have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hσ) hcoef
  linarith

end CorrRP

/-! ## 2b. The reflected readings below the torus moment -/

section ReflTorus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k))
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **The vacuum and reflected readings are below the reflected torus moment, with no sup bound**:
for a bounded kernel insertion `F` covering `w` steps and every `a`, `b`,

    α_F² + R_F(2a+2) ≤ Tr(F K^{2a+2} Fᵀ K^{2b+2}) / |c|^L,   L = 2w + (2a+2) + (2b+2).

`Tr(F K^{2a+2} Fᵀ K^{2b+2})` is the torus moment of the insertion with its time reflection at
separation `2a + 2` on the torus of `L` steps (`trK`). The trace splits at the vacuum
(`trK_decomp`): the vacuum–vacuum term is `|c|^{L−2w} α_F²` (`vac_tp`), one cross term is
`|c|^{2b+2} R_F` (`rpRead_eq`), the other is `|c|^{2a+2} ‖R^{b+1} Fφ‖² ≥ 0`, and the
excited–excited term is `‖R^{b+1} F R^{a+1}‖²_HS ≥ 0` (`hs_sand_eq2`). Even powers of `c` are
powers of `|c|`. No bound on `F` enters the inequality, and there is no wrap-around error
(compare `connK_refl_read`).

DERIVED: `1` and `2` are the offsets of `iter`, so `a + a + 2` and `b + b + 2` are the separations;
`2` the square of the vacuum reading. -/
theorem reflMoment_le_torus (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    vacRead μ c φ F w ^ 2 + refl μ k c φ F w a
      ≤ trK μ k F (tp F) (a + a + 1) (b + b + 1) / |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hc : 0 < |c| := abs_pos.mpr hc0
  obtain ⟨CF, hCF⟩ := hF.bdd
  have hfm := measurable_kf (μ := μ) hF hφm
  have hfb : ∀ x, |kernelFun F μ φ x| ≤ CF * Bφ := abs_kf_le hCF hφb
  have hum := measurable_kf (μ := μ) (bdd_tp hF) hφm
  have hub : ∀ x, |kernelFun (tp F) μ φ x| ≤ CF * Bφ := abs_kf_le (fun x y => hCF y x) hφb
  have hdec := trK_decomp hφm hφb hφ1 hkm hkb hsym heig hF (bdd_tp hF) (a + a + 1) (b + b + 1)
  have hV : ∫ x, kernelFun (tp F) μ φ x * φ x ∂μ = ∫ x, kernelFun F μ φ x * φ x ∂μ :=
    vac_tp hφm hφb hF
  have hT2 : 0 ≤ ∫ x, kernelFun F μ φ x
      * kernelFun (iter μ (rem k c φ) (b + b + 1)) μ (kernelFun (tp (tp F)) μ φ) x ∂μ := by
    have e := rpRead_eq (μ := μ) hr hrs hfm hfb b
    rw [show tp (tp F) = F from rfl, ← e]
    exact rpRead_nonneg _ _ _
  have hT3 : ∫ x, kernelFun (tp F) μ φ x
      * kernelFun (iter μ (rem k c φ) (a + a + 1)) μ (kernelFun (tp F) μ φ) x ∂μ
      = rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ) := (rpRead_eq hr hrs hum hub a).symm
  have hT4 : 0 ≤ trK μ (rem k c φ) F (tp F) (a + a + 1) (b + b + 1) := by
    rw [← hs_sand_eq2 hr hrs hF a b]
    exact hs_nonneg _
  rw [hV, hT3] at hdec
  have hPa : |c| ^ (a + a + 2) = c ^ (a + a + 1 + 1) := Even.pow_abs ⟨a + 1, by ring⟩ c
  have hPb : |c| ^ (b + b + 2) = c ^ (b + b + 1 + 1) := Even.pow_abs ⟨b + 1, by ring⟩ c
  have hL : |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      = |c| ^ w * |c| ^ w * |c| ^ (a + a + 2) * |c| ^ (b + b + 2) := by
    rw [pow_add, pow_add, pow_add]
  have h2 : |c| ^ (2 * (w + a + 1)) = |c| ^ w * |c| ^ w * |c| ^ (a + a + 2) := by
    rw [show 2 * (w + a + 1) = w + w + (a + a + 2) by ring, pow_add, pow_add]
  have hw0 : 0 < |c| ^ w := pow_pos hc w
  have ha0 : 0 < |c| ^ (a + a + 2) := pow_pos hc _
  have hb0 : 0 < |c| ^ (b + b + 2) := pow_pos hc _
  unfold vacRead refl
  rw [le_div_iff₀ (pow_pos hc _), hdec, ← hPa, ← hPb, hL, h2]
  set V := ∫ x, kernelFun F μ φ x * φ x ∂μ
  set ρ := rpRead μ (rem k c φ) a (kernelFun (tp F) μ φ)
  set T2 := ∫ x, kernelFun F μ φ x
      * kernelFun (iter μ (rem k c φ) (b + b + 1)) μ (kernelFun (tp (tp F)) μ φ) x ∂μ
  set T4 := trK μ (rem k c φ) F (tp F) (a + a + 1) (b + b + 1)
  have key : ((V / |c| ^ w) ^ 2 + ρ / (|c| ^ w * |c| ^ w * |c| ^ (a + a + 2)))
        * (|c| ^ w * |c| ^ w * |c| ^ (a + a + 2) * |c| ^ (b + b + 2))
      = V ^ 2 * |c| ^ (a + a + 2) * |c| ^ (b + b + 2) + ρ * |c| ^ (b + b + 2) := by
    field_simp
  rw [key]
  nlinarith [mul_nonneg ha0.le hT2, hT4]

include hφm hφb hφ1 hkm hkb hsym heig in
/-- **The same against the normalized torus moment**: with `L = 2(w + a + b + 2)`,
`Tr K^L = |c|^L (1 + σ₀)` with `σ₀ = excited (w + a + b + 2)` the excited weight of the torus
(`trPow_even`), so

    α_F² + R_F(2a+2) ≤ (1 + σ₀) · E_L[f · θf],   E_L[f · θf] = Tr(F K^{2a+2} Fᵀ K^{2b+2}) / Tr K^L.

DERIVED: `1` is the vacuum's own weight in `Tr K^L`; `1` and `2` the offsets of `iter` and of the
excited weight. -/
theorem reflMoment_le_torus_ratio (hc0 : c ≠ 0) {F : X → X → ℝ} (hF : Bdd F) (w a b : ℕ) :
    vacRead μ c φ F w ^ 2 + refl μ k c φ F w a
      ≤ (1 + excited μ k c φ (w + a + b + 2))
        * (trK μ k F (tp F) (a + a + 1) (b + b + 1)
          / trPow μ k (w + a + b + 1 + (w + a + b + 1) + 1)) := by
  have h := reflMoment_le_torus hφm hφb hφ1 hkm hkb hsym heig hc0 hF w a b
  have ht := trPow_even hφm hφb hφ1 hkm hkb hsym heig (w + a + b + 1)
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcL : c ^ (w + a + b + 1 + (w + a + b + 1) + 2)
      = |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := by
    rw [show w + a + b + 1 + (w + a + b + 1) + 2 = w + w + (a + a + 2) + (b + b + 2) by ring]
    exact (Even.pow_abs ⟨w + a + b + 2, by ring⟩ c).symm
  have h2L : |c| ^ (2 * (w + a + b + 2)) = |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := by
    rw [show 2 * (w + a + b + 2) = w + w + (a + a + 2) + (b + b + 2) by ring]
  have hP : 0 < |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := pow_pos hc _
  have hH : 0 ≤ hs μ (iter μ (rem k c φ) (w + a + b + 1)) := hs_nonneg _
  have hPH : |c| ^ (w + w + (a + a + 2) + (b + b + 2))
      + hs μ (iter μ (rem k c φ) (w + a + b + 1)) ≠ 0 := (add_pos_of_pos_of_nonneg hP hH).ne'
  have hP0 : |c| ^ (w + w + (a + a + 2) + (b + b + 2)) ≠ 0 := hP.ne'
  have heq : (1 + excited μ k c φ (w + a + b + 2))
        * (trK μ k F (tp F) (a + a + 1) (b + b + 1)
          / trPow μ k (w + a + b + 1 + (w + a + b + 1) + 1))
      = trK μ k F (tp F) (a + a + 1) (b + b + 1)
          / |c| ^ (w + w + (a + a + 2) + (b + b + 2)) := by
    rw [ht, hcL]
    unfold excited
    rw [show w + a + b + 2 - 1 = w + a + b + 1 by omega, h2L]
    field_simp
  rw [heq]
  exact h

end ReflTorus

/-! ## 4. The reflected slab -/

section Swap

/-- Fubini for a bounded measurable function on a product of finite measures.

DERIVED: no numeral appears in the statement. -/
theorem swap_int {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α}
    {μb : Measure β} [IsFiniteMeasure μa] [IsFiniteMeasure μb] {F : α → β → ℝ}
    (hF : Measurable (fun p : α × β => F p.1 p.2)) {C : ℝ} (hb : ∀ a b, |F a b| ≤ C) :
    ∫ a, ∫ b, F a b ∂μb ∂μa = ∫ b, ∫ a, F a b ∂μa ∂μb :=
  integral_integral_swap (integrable_of_bdd hF (fun p => hb p.1 p.2))

/-- **Fubini for two pairs of variables**: for a bounded measurable `Φ` on `(α × β) × (α × β)`
over probability measures, `∫∫∫∫ Φ(a, b, a', b')` may integrate the pair `(a', b')` first or last.

DERIVED: no numeral appears in the statement. -/
theorem swap_pair {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α}
    {μb : Measure β} [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    {Φ : α → β → α → β → ℝ}
    (hΦ : Measurable (fun q : (α × β) × (α × β) => Φ q.1.1 q.1.2 q.2.1 q.2.2)) {C : ℝ}
    (hb : ∀ a b a' b', |Φ a b a' b'| ≤ C) :
    ∫ a, ∫ b, ∫ a', ∫ b', Φ a b a' b' ∂μb ∂μa ∂μb ∂μa
      = ∫ a', ∫ b', ∫ a, ∫ b, Φ a b a' b' ∂μb ∂μa ∂μb ∂μa := by
  have hin1 : ∀ a b, ∫ a', ∫ b', Φ a b a' b' ∂μb ∂μa
      = ∫ r, Φ a b r.1 r.2 ∂(μa.prod μb) := fun a b =>
    (integral_prod (fun r : α × β => Φ a b r.1 r.2)
      (integrable_of_bdd (hΦ.comp ((measurable_const : Measurable fun _ : α × β => (a, b)).prodMk
        measurable_id))
        (fun r => hb _ _ _ _))).symm
  have hin2 : ∀ a' b', ∫ a, ∫ b, Φ a b a' b' ∂μb ∂μa
      = ∫ p, Φ p.1 p.2 a' b' ∂(μa.prod μb) := fun a' b' =>
    (integral_prod (fun p : α × β => Φ p.1 p.2 a' b')
      (integrable_of_bdd (hΦ.comp (measurable_id.prodMk
        (measurable_const : Measurable fun _ : α × β => (a', b'))))
        (fun p => hb _ _ _ _))).symm
  simp_rw [hin1, hin2]
  have hI1 : Integrable (fun p : α × β => ∫ r, Φ p.1 p.2 r.1 r.2 ∂(μa.prod μb))
      (μa.prod μb) :=
    integrable_of_bdd (hΦ.stronglyMeasurable.integral_prod_right' (ν := μa.prod μb)).measurable
      (fun p => abs_integral_le fun r => hb _ _ _ _)
  have hI2 : Integrable (fun r : α × β => ∫ p, Φ p.1 p.2 r.1 r.2 ∂(μa.prod μb))
      (μa.prod μb) :=
    integrable_of_bdd (hΦ.stronglyMeasurable.integral_prod_left' (μ := μa.prod μb)).measurable
      (fun r => abs_integral_le fun p => hb _ _ _ _)
  calc ∫ a, ∫ b, ∫ r, Φ a b r.1 r.2 ∂(μa.prod μb) ∂μb ∂μa
      = ∫ p, ∫ r, Φ p.1 p.2 r.1 r.2 ∂(μa.prod μb) ∂(μa.prod μb) := (integral_prod _ hI1).symm
    _ = ∫ r, ∫ p, Φ p.1 p.2 r.1 r.2 ∂(μa.prod μb) ∂(μa.prod μb) :=
        swap_int (F := fun (p r : α × β) => Φ p.1 p.2 r.1 r.2) hΦ (fun p r => hb _ _ _ _)
    _ = _ := integral_prod _ hI2

end Swap

section Reverse

open HiddenChain

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Y]

/-- A sequence cut after index `k` and continued by the constant `z`.

DERIVED: no numeral appears in the statement. -/
def cutV (k : ℕ) (V : ℕ → X) (z : X) : ℕ → X := fun i => if i ≤ k then V i else z

/-- **The insertion read from the far end of the chain**: the last step, from the `(m+1)`-st slice
to `z` through the hidden variable `b`, is pinned, and `G` reads the first `m + 1` steps.

DERIVED: `1` is the offset of the number of steps. -/
noncomputable def backG (m : ℕ) (G : (ℕ → X) → (ℕ → Y) → ℝ) (z : X) (b : Y) :
    (ℕ → X) → (ℕ → Y) → ℝ :=
  fun V A => G (cutV (m + 1) V z) (Function.update A (m + 1) b)

/-- **The reflected slab observable**: `revG ι m G` reads the slices `0, …, m + 1` in reverse order
and the hidden variables `0, …, m` in reverse order through `ι` (on the Wilson torus, the inverted
time links): `(θG)(V, A) = G(V_{m+1−i}, ι A_{m−i})`.

DERIVED: `1` is the offset of the number of steps. -/
noncomputable def revG (ι : Y → Y) (m : ℕ) (G : (ℕ → X) → (ℕ → Y) → ℝ) :
    (ℕ → X) → (ℕ → Y) → ℝ :=
  fun V A => G (fun i => V (m + 1 - i))
    (fun i => if i ≤ m then ι (A (m - i)) else Classical.arbitrary Y)

omit [MeasurableSpace X] in
/-- Cutting commutes with prepending a point.

DERIVED: `1` is the shift of `scons`. -/
theorem cutV_scons (k : ℕ) (x : X) (V : ℕ → X) (z : X) :
    cutV (k + 1) (scons x V) z = scons x (cutV k V z) := by
  funext i
  cases i with
  | zero => simp [cutV, scons]
  | succ i => simp [cutV, scons]

omit [MeasurableSpace X] in
/-- A constant sequence cut at `0`.

DERIVED: `0` is the cut. -/
theorem cutV_zero_const (y z : X) : cutV 0 (fun _ => y) z = scons y (fun _ => z) := by
  funext i
  cases i with
  | zero => simp [cutV, scons]
  | succ i => simp [cutV, scons]

omit [MeasurableSpace Y] [Nonempty Y] in
/-- Updating commutes with prepending a point.

DERIVED: `1` is the shift of `scons`. -/
theorem update_scons (k : ℕ) (a : Y) (A : ℕ → Y) (b : Y) :
    Function.update (scons a A) (k + 1) b = scons a (Function.update A k b) := by
  funext i
  cases i with
  | zero => simp [scons]
  | succ i => simp [scons, Function.update_apply]

omit [MeasurableSpace Y] [Nonempty Y] in
/-- A constant sequence updated at `0`.

DERIVED: `0` is the updated index. -/
theorem update_const_zero (e b : Y) :
    Function.update (fun _ : ℕ => e) 0 b = scons b (fun _ => e) := by
  funext i
  cases i with
  | zero => simp [scons]
  | succ i => simp [scons]

/-- The cut is measurable in the sequence and the continuation.

DERIVED: no numeral appears in the statement. -/
theorem measurable_cutV (k : ℕ) : Measurable (fun p : (ℕ → X) × X => cutV k p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ≤ k
  · simp only [cutV, if_pos h]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [cutV, if_neg h]; exact measurable_snd

omit [Nonempty Y] in
/-- The update at a fixed index is measurable in the sequence and the value.

DERIVED: no numeral appears in the statement. -/
theorem measurable_updateAt (k : ℕ) :
    Measurable (fun p : (ℕ → Y) × Y => Function.update p.1 k p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i = k
  · simp only [Function.update_apply, if_pos h]; exact measurable_snd
  · simp only [Function.update_apply, if_neg h]; exact (measurable_pi_apply i).comp measurable_fst

variable {μ : Measure X} {ν : Measure Y} {w : X → Y → X → ℝ}

/-- **The slab kernel peeled from its far end**:
`slabKer (m+1) G (x, z) = ∫∫ slabKer m (backG m G z b)(x, y) w(y, b, z) dν(b) dμ(y)`. By induction,
with one exchange of the pair of the first step and the pair of the last step (`swap_pair`).

DERIVED: `1` is the offset of the number of steps. -/
theorem slabKer_back [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hw : WMeas w) {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2) → ∀ {B : ℝ}, (∀ V A, |G V A| ≤ B) →
      ∀ x z, slabKer μ ν w (m + 1) G x z
        = ∫ y, ∫ b, slabKer μ ν w m (backG m G z b) x y * w y b z ∂ν ∂μ
  | 0, G, hG, B, hGb, x, z => by
    show ∫ y, ∫ a, w x a y * ∫ b, w y b z * G (scons x (scons y (fun _ => z)))
        (scons a (scons b (fun _ => Classical.arbitrary Y))) ∂ν ∂ν ∂μ
      = ∫ y, ∫ b, (∫ a, w x a y * G (cutV (0 + 1) (scons x (fun _ => y)) z)
        (Function.update (scons a (fun _ => Classical.arbitrary Y)) (0 + 1) b) ∂ν) * w y b z
          ∂ν ∂μ
    simp only [cutV_scons, cutV_zero_const, update_scons, update_const_zero]
    congr 1; funext y
    have hm : Measurable (fun p : Y × Y => w x p.1 y * (w y p.2 z
        * G (scons x (scons y (fun _ => z)))
          (scons p.1 (scons p.2 (fun _ => Classical.arbitrary Y))))) :=
      ((measurable_w_mid hw x y).comp measurable_fst).mul
        (((measurable_w_mid hw y z).comp measurable_snd).mul
          (hG.comp (measurable_const.prodMk (measurable_scons.comp (measurable_fst.prodMk
            (measurable_scons.comp (measurable_snd.prodMk measurable_const)))))))
    calc ∫ a, w x a y * ∫ b, w y b z * G (scons x (scons y (fun _ => z)))
          (scons a (scons b (fun _ => Classical.arbitrary Y))) ∂ν ∂ν
        = ∫ a, ∫ b, w x a y * (w y b z * G (scons x (scons y (fun _ => z)))
          (scons a (scons b (fun _ => Classical.arbitrary Y)))) ∂ν ∂ν := by
          congr 1; funext a; rw [integral_const_mul]
      _ = ∫ b, ∫ a, w x a y * (w y b z * G (scons x (scons y (fun _ => z)))
          (scons a (scons b (fun _ => Classical.arbitrary Y)))) ∂ν ∂ν :=
          swap_int hm (C := C * (C * B)) (fun a b =>
            abs_mul_le_of (hwb _ _ _) (abs_mul_le_of (hwb _ _ _) (hGb _ _)))
      _ = _ := by
          congr 1; funext b; rw [← integral_mul_const]; congr 1; funext a; ring
  | m + 1, G, hG, B, hGb, x, z => by
    have hG1 : ∀ a0 : Y,
        Measurable (fun q : (ℕ → X) × (ℕ → Y) => G (scons x q.1) (scons a0 q.2)) := fun a0 =>
      hG.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))
    have ih : ∀ y1 a0, slabKer μ ν w (m + 1) (fun V A => G (scons x V) (scons a0 A)) y1 z
        = ∫ y, ∫ b, slabKer μ ν w m (backG m (fun V A => G (scons x V) (scons a0 A)) z b) y1 y
          * w y b z ∂ν ∂μ :=
      fun y1 a0 => slabKer_back hw hwb m (hG1 a0) (fun _ _ => hGb _ _) y1 z
    have hfun : ∀ (a0 : Y) (b : Y),
        (fun V A => backG (m + 1) G z b (scons x V) (scons a0 A))
          = backG m (fun V A => G (scons x V) (scons a0 A)) z b := by
      intro a0 b; funext V A
      simp only [backG, cutV_scons, update_scons]
    show ∫ y1, ∫ a0, w x a0 y1 * slabKer μ ν w (m + 1) (fun V A => G (scons x V) (scons a0 A))
        y1 z ∂ν ∂μ
      = ∫ y, ∫ b, (∫ y1, ∫ a0, w x a0 y1 * slabKer μ ν w m
          (fun V A => backG (m + 1) G z b (scons x V) (scons a0 A)) y1 y ∂ν ∂μ) * w y b z ∂ν ∂μ
    have hGp : Measurable (fun q : (Y × Y) × (ℕ → X) × (ℕ → Y) =>
        G (scons x (cutV (m + 1) q.2.1 z)) (scons q.1.1 (Function.update q.2.2 (m + 1) q.1.2))) :=
      hG.comp ((measurable_scons.comp (measurable_const.prodMk
        ((measurable_cutV (m + 1)).comp (measurable_snd.fst.prodMk measurable_const)))).prodMk
        (measurable_scons.comp (measurable_fst.fst.prodMk
          ((measurable_updateAt (m + 1)).comp (measurable_snd.snd.prodMk measurable_fst.snd)))))
    have hSm := measurable_slabKer (μ := μ) (ν := ν) hw m (P := Y × Y)
      (G := fun p => backG m (fun V A => G (scons x V) (scons p.1 A)) z p.2) hGp
    have hΦ : Measurable (fun q : (X × Y) × (X × Y) => w x q.1.2 q.1.1
        * (slabKer μ ν w m (backG m (fun V A => G (scons x V) (scons q.1.2 A)) z q.2.2)
            q.1.1 q.2.1 * w q.2.1 q.2.2 z)) :=
      (hw.comp (measurable_const.prodMk (measurable_fst.snd.prodMk measurable_fst.fst))).mul
        ((hSm.comp ((measurable_fst.snd.prodMk measurable_snd.snd).prodMk
          (measurable_fst.fst.prodMk measurable_snd.fst))).mul
          (hw.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_const))))
    have hb : ∀ y1 a0 y b, |w x a0 y1
        * (slabKer μ ν w m (backG m (fun V A => G (scons x V) (scons a0 A)) z b) y1 y
          * w y b z)| ≤ C * (C ^ (m + 1) * B * C) := fun y1 a0 y b =>
      abs_mul_le_of (hwb _ _ _) (abs_mul_le_of
        (abs_slabKer_le hwb m (G := backG m (fun V A => G (scons x V) (scons a0 A)) z b)
          (fun _ _ => hGb _ _) y1 y) (hwb _ _ _))
    calc ∫ y1, ∫ a0, w x a0 y1 * slabKer μ ν w (m + 1) (fun V A => G (scons x V) (scons a0 A))
          y1 z ∂ν ∂μ
        = ∫ y1, ∫ a0, ∫ y, ∫ b, w x a0 y1 * (slabKer μ ν w m
          (backG m (fun V A => G (scons x V) (scons a0 A)) z b) y1 y * w y b z) ∂ν ∂μ ∂ν ∂μ := by
          congr 1; funext y1; congr 1; funext a0
          rw [ih y1 a0, ← integral_const_mul]; congr 1; funext y; rw [← integral_const_mul]
      _ = ∫ y, ∫ b, ∫ y1, ∫ a0, w x a0 y1 * (slabKer μ ν w m
          (backG m (fun V A => G (scons x V) (scons a0 A)) z b) y1 y * w y b z) ∂ν ∂μ ∂ν ∂μ :=
          swap_pair hΦ hb
      _ = _ := by
          congr 1; funext y; congr 1; funext b
          rw [← integral_mul_const]; congr 1; funext y1; rw [← integral_mul_const]
          congr 1; funext a0; rw [hfun a0 b]; ring

/-- **The reflected slab has the transposed slab kernel.** If the step weight is symmetric under
reversal, `w(x, a, y) = w(y, ι a, x)`, with `ι` a measure-preserving equivalence of the hidden
variables, then for every bounded measurable insertion `G`,

    slabKer m (revG ι m G)(x, z) = slabKer m G(z, x),

i.e. the slab kernel of the reflected observable `θG` is `tp (slabKer m G)`. By induction: the
first step of the reflected chain is the last step of the original one (`slabKer_back`), and `ι`
changes variables in the hidden integral.

DERIVED: `1` is the offset of the number of steps. -/
theorem slabKer_rev [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hw : WMeas w) {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν)
    (hwι : ∀ x a y, w x a y = w y (ι a) x) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2) → ∀ {B : ℝ}, (∀ V A, |G V A| ≤ B) →
      ∀ x z, slabKer μ ν w m (revG ι m G) x z = slabKer μ ν w m G z x
  | 0, G, hG, B, hGb, x, z => by
    have e : ∀ a, revG ι 0 G (scons x (fun _ => z)) (scons a (fun _ => Classical.arbitrary Y))
        = G (scons z (fun _ => x)) (scons (ι a) (fun _ => Classical.arbitrary Y)) := by
      intro a
      show G _ _ = G _ _
      congr 1
      · funext i
        cases i with
        | zero => rfl
        | succ i => rw [show 0 + 1 - (i + 1) = 0 by omega]; rfl
      · funext i
        cases i with
        | zero => simp [scons]
        | succ i => simp [scons]
    show ∫ a, w x a z * revG ι 0 G (scons x (fun _ => z))
        (scons a (fun _ => Classical.arbitrary Y)) ∂ν
      = ∫ b, w z b x * G (scons z (fun _ => x)) (scons b (fun _ => Classical.arbitrary Y)) ∂ν
    calc ∫ a, w x a z * revG ι 0 G (scons x (fun _ => z))
          (scons a (fun _ => Classical.arbitrary Y)) ∂ν
        = ∫ a, (fun b => w z b x * G (scons z (fun _ => x))
          (scons b (fun _ => Classical.arbitrary Y))) (ι a) ∂ν := by
          congr 1; funext a; rw [e a, hwι x a z]
      _ = _ := hι.integral_comp' (fun b => w z b x * G (scons z (fun _ => x))
          (scons b (fun _ => Classical.arbitrary Y)))
  | m + 1, G, hG, B, hGb, x, z => by
    have e : ∀ a, (fun V A => revG ι (m + 1) G (scons x V) (scons a A))
        = revG ι m (backG m G x (ι a)) := by
      intro a; funext V A
      show G _ _ = G _ _
      congr 1
      · funext i
        simp only [cutV]
        split_ifs with h
        · rw [show m + 1 + 1 - i = (m + 1 - i) + 1 by omega]; rfl
        · rw [show m + 1 + 1 - i = 0 by omega]; rfl
      · funext i
        rw [Function.update_apply]
        by_cases h1 : i = m + 1
        · subst h1; simp [scons]
        · by_cases h2 : i ≤ m
          · rw [if_pos (by omega : i ≤ m + 1), if_neg h1, if_pos h2,
              show m + 1 - i = (m - i) + 1 by omega]
            rfl
          · rw [if_neg (by omega : ¬ i ≤ m + 1), if_neg h1, if_neg h2]
    have hGb' : ∀ b : Y, Measurable (fun q : (ℕ → X) × (ℕ → Y) => backG m G x b q.1 q.2) :=
      fun b => hG.comp (((measurable_cutV (m + 1)).comp (measurable_fst.prodMk measurable_const)).prodMk
        ((measurable_updateAt (m + 1)).comp (measurable_snd.prodMk measurable_const)))
    have e' : ∀ y a, slabKer μ ν w m (fun V A => revG ι (m + 1) G (scons x V) (scons a A)) y z
        = slabKer μ ν w m (backG m G x (ι a)) z y := by
      intro y a
      rw [e a]
      exact slabKer_rev hw hwb ι hι hwι m (hGb' (ι a)) (fun _ _ => hGb _ _) y z
    show ∫ y, ∫ a, w x a y * slabKer μ ν w m
        (fun V A => revG ι (m + 1) G (scons x V) (scons a A)) y z ∂ν ∂μ
      = slabKer μ ν w (m + 1) G z x
    rw [slabKer_back hw hwb m hG hGb z x]
    congr 1; funext y
    calc ∫ a, w x a y * slabKer μ ν w m
          (fun V A => revG ι (m + 1) G (scons x V) (scons a A)) y z ∂ν
        = ∫ a, (fun b => slabKer μ ν w m (backG m G x b) z y * w y b x) (ι a) ∂ν := by
          congr 1; funext a; rw [e' y a, hwι x a y]; exact mul_comm _ _
      _ = _ := hι.integral_comp' (fun b => slabKer μ ν w m (backG m G x b) z y * w y b x)

end Reverse

/-! ## 3. On the Wilson torus, at `SU(N)` and over every gauge group -/

section WilsonRP

open MassGap.RectWilson MassGap.RectTransfer MassGap.RectTorusState MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingWilson MassGap.OpenAIBridgeSides

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **Clustering of two slab observables on the `SU(N)` Wilson torus in reflection form, uniform in
the torus, from the seed.** If one torus of even side `n ≥ 2` has
`16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic torus of every even side
`L ≥ 2n` there are a normalized eigenfunction `φ` of the slice kernel `kT` and its eigenvalue
`c ≠ 0` such that for bounded measurable functions `f`, `g` of slabs (`|f| ≤ A`, `|g| ≤ B`) of
widths `w = 2v + 2`, `w' = 2v' + 2`, with slab kernels `F̂ = slabKer f`, `Ĝ = slabKer g`, read at
times `0` and `w + p + 1` of `L = p + q + 2 + w + w'`, `p = 2a + j + 2`, `q = 2a + j' + 2`,
`4(w + w') + 8n ≤ L`,

    |⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩|
      ≤ (1/2)^⌊(j+1)/n⌋ √(R_f R_{θg}) + (1/2)^⌊(j'+1)/n⌋ √(R_{θf} R_g)
        + 5 A B (1/2)^⌊((p+q)/2+1)/n⌋,

`R_f = refl hS kT c φ F̂ w a` the reflected reading of `f` at separation `2a + 2` and
`R_{θg} = refl hS kT c φ Ĝᵀ w' a` that of the reflected slab kernel. The cross terms carry no sup
bound; `A B` stays on the wrap-around weight. `OpenAIBridgeUniform.gap_side_excited`,
`connK_rp_slab` on the slab kernels, `OpenAIBridgeSlab.connK_eq_expect_slab`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `5` the constant of `connK_split`;
`4` and `8` the slab condition of `excited_le_slab`, and `4` the spacetime dimension; `1/2` the
contraction; `2` the doubled side, the least seed side, the least ratio `L / n`, the doubled
widths and separations and the offsets of `iter`; `0` the time direction, the first slice and the
sign of the coupling; `1` the offsets of `iter`, the separation and the unit norm. -/
theorem wilson_slab_conn_rp
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (fun _ : Fin 4 => L) 0) N β z y * φ y
        ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = c * φ z) ∧
      ∀ (f g : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N)
          → (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) → ℝ),
      Measurable (fun r : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N)
        × (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) => f r.1 r.2) →
      Measurable (fun r : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N)
        × (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) => g r.1 r.2) →
      ∀ A B : ℝ, (∀ V A', |f V A'| ≤ A) → (∀ V A', |g V A'| ≤ B) → ∀ v v' : ℕ,
      LocalUpTo (v + v + 2) f → LocalUpTo (v' + v' + 2) g → ∀ a j j' : ℕ,
      a + j + a + 2 + (a + j' + a + 2) + 2 + (v + v + 2) + (v' + v' + 2) = L →
      4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L →
      |(sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
          (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U)
            * g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))
        - (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
            (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U))
          * (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
            (fun U => g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))|
        ≤ (1 / 2) ^ ((j + 1) / n)
            * √(refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ
                  (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N)
                    (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2) a
                * refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ
                  (tp (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
                    (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β)
                    (v' + v' + 1) g)) (v' + v' + 2) a)
          + (1 / 2) ^ ((j' + 1) / n)
            * √(refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ
                  (tp (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
                    (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β)
                    (v + v + 1) f)) (v + v + 2) a
                * refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ
                  (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N)
                    (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2) a)
          + 5 * (A * B) * (1 / 2) ^ (((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) / n) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    OpenAIBridgeUniform.gap_side_excited hN hβ hn he h0 a' L hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig,
    fun f g hfm hgm A B hfb hgb v v' hf hg a j j' hpq hW => ?_⟩
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hfb (fun _ _ => 1) (fun _ _ => 1))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgb (fun _ _ => 1) (fun _ _ => 1))
  have hw := wmeas_wtR (μ := 0) (T := tr (fun _ : Fin 4 => L) 0) (N := N) β
  have hwb := abs_wtR_le (μ := 0) (T := tr (fun _ : Fin 4 => L) 0) hN hβ
  have hw0 : ∀ x a y, 0 ≤ wtR 0 (tr (fun _ : Fin 4 => L) 0) N β x a y := wtR_nonneg β
  have hFk : ∀ x y, |slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N)
      (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f x y|
      ≤ A * iter (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
        (v + v + 1) x y := fun x y => by
    have h := slabKer_le_iter (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N)
      (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb hw0 (v + v + 1) hfb x y
    rwa [kern_wtR] at h
  have hGk : ∀ x y, |slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N)
      (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g x y|
      ≤ B * iter (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
        (v' + v' + 1) x y := fun x y => by
    have h := slabKer_le_iter (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N)
      (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb hw0 (v' + v' + 1) hgb x y
    rwa [kern_wtR] at h
  have h := connK_rp_slab hφm hφb hφ1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc hLe
    (bdd_slabKer (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N)
      (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N)
      (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb (v' + v' + 1) hgm hgb)
    hA0 hB0 v v' hFk hGk a j j' hpq hW
  have heq := connK_eq_expect_slab hN hβ (L := fun _ : Fin 4 => L) (m := v + v + 1)
    (m' := v' + v' + 1) (p := a + j + a + 2) (q := a + j' + a + 2) (by show L = _; omega)
    hfm hgm hfb hgb (hf.mono (by omega)) (hg.mono (by omega))
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end WilsonRP

section WilsonRPG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingWilson MassGap.DoublingWilsonG MassGap.GaugeGroup
  MassGap.OpenAIBridgeSides MassGap.OpenAIBridgeGroups

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
/-- **Clustering of two slab observables on the Wilson torus of every gauge group in reflection
form, uniform in the torus, from the seed** (`wilson_slab_conn_rp` over a `GaugeGroup G`). If one
torus of even side `n ≥ 2` has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the
cubic torus of `G` of every even side `L = M + 1 ≥ 2n` there are a normalized eigenfunction `φ` of
`kTG` and its eigenvalue `c ≠ 0` such that, for bounded measurable slab observables `f`, `g` as in
`wilson_slab_conn_rp`,

    |⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩|
      ≤ (1/2)^⌊(j+1)/n⌋ √(R_f R_{θg}) + (1/2)^⌊(j'+1)/n⌋ √(R_{θf} R_g)
        + 5 A B (1/2)^⌊((p+q)/2+1)/n⌋.

`OpenAIBridgeGroups.gap_side_excitedG`, `connK_rp_slab`, `OpenAIBridgeSlab.connK_eq_expect_slabG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `5` the constant of `connK_split`;
`4` and `8` the slab condition of `excited_le_slab`, and `4` the spacetime dimension; `1/2` the
contraction; `2` the doubled side, the least seed side, the least ratio `L / n`, the doubled
widths and separations and the offsets of `iter`; `0` the time direction, the first slice and the
sign of the coupling; `1` the offsets of `iter`, the separation, the unit norm and the side
`M + 1`. -/
theorem wilson_slab_conn_rpG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (M : ℕ) (hLe : Even (M + 1)) (hL : 2 * n ≤ M + 1) :
    ∃ φ : (SpT 0 (TorusChain.Tc M) → G) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG G 0 (TorusChain.Tc M)) = 1 ∧
      (∀ z, ∫ y, kTG G 0 (TorusChain.Tc M) β z y * φ y ∂(hSG G 0 (TorusChain.Tc M)) = c * φ z) ∧
      ∀ (f g : (ℕ → SpT 0 (TorusChain.Tc M) → G) → (ℕ → TT 0 (TorusChain.Tc M) → G) → ℝ),
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc M) → G)
        × (ℕ → TT 0 (TorusChain.Tc M) → G) => f r.1 r.2) →
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc M) → G)
        × (ℕ → TT 0 (TorusChain.Tc M) → G) => g r.1 r.2) →
      ∀ A B : ℝ, (∀ V A', |f V A'| ≤ A) → (∀ V A', |g V A'| ≤ B) → ∀ v v' : ℕ,
      LocalUpTo (v + v + 2) f → LocalUpTo (v' + v' + 2) g → ∀ a j j' : ℕ,
      a + j + a + 2 + (a + j' + a + 2) + 2 + (v + v + 2) + (v' + v' + 2) = M + 1 →
      4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ M + 1 →
      |(sysRG G (fun _ : Fin 4 => M + 1)).expect (probHaar G) β
          (fun U => f (slabV (fun _ : Fin 4 => M + 1) 0 0 U) (slabA (fun _ : Fin 4 => M + 1) 0 0 U)
            * g (slabV (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))
        - (sysRG G (fun _ : Fin 4 => M + 1)).expect (probHaar G) β
            (fun U => f (slabV (fun _ : Fin 4 => M + 1) 0 0 U)
              (slabA (fun _ : Fin 4 => M + 1) 0 0 U))
          * (sysRG G (fun _ : Fin 4 => M + 1)).expect (probHaar G) β
            (fun U => g (slabV (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))|
        ≤ (1 / 2) ^ ((j + 1) / n)
            * √(refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ
                  (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
                    (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2) a
                * refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ
                  (tp (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
                    (TorusChainG.wtG G M β) (v' + v' + 1) g)) (v' + v' + 2) a)
          + (1 / 2) ^ ((j' + 1) / n)
            * √(refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ
                  (tp (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
                    (TorusChainG.wtG G M β) (v + v + 1) f)) (v + v + 2) a
                * refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ
                  (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
                    (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2) a)
          + 5 * (A * B) * (1 / 2) ^ (((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) / n) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    gap_side_excitedG hβ hn he h0 a' (M + 1) hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig,
    fun f g hfm hgm A B hfb hgb v v' hf hg a j j' hpq hW => ?_⟩
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hfb (fun _ _ => 1) (fun _ _ => 1))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgb (fun _ _ => 1) (fun _ _ => 1))
  have hw := TorusChainG.wmeas_wtG (G := G) (M := M) β
  have hwb := TorusChainG.abs_wtG_le (G := G) (M := M) hβ
  have hw0 : ∀ x a y, 0 ≤ TorusChainG.wtG G M β x a y := TorusChainG.wtG_nonneg β
  have hFk : ∀ x y, |slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
      (TorusChainG.wtG G M β) (v + v + 1) f x y|
      ≤ A * iter (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) (v + v + 1) x y :=
    fun x y => by
      have h := slabKer_le_iter (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M))
        hw hwb hw0 (v + v + 1) hfb x y
      rwa [TorusChainG.kern_wtG] at h
  have hGk : ∀ x y, |slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
      (TorusChainG.wtG G M β) (v' + v' + 1) g x y|
      ≤ B * iter (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) (v' + v' + 1) x y :=
    fun x y => by
      have h := slabKer_le_iter (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M))
        hw hwb hw0 (v' + v' + 1) hgb x y
      rwa [TorusChainG.kern_wtG] at h
  have h := connK_rp_slab hφm hφb hφ1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc hLe
    (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb
      (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb
      (v' + v' + 1) hgm hgb)
    hA0 hB0 v v' hFk hGk a j j' hpq hW
  have heq := connK_eq_expect_slabG hβ (M := M) (m := v + v + 1) (m' := v' + v' + 1)
    (p := a + j + a + 2) (q := a + j' + a + 2) (by omega) hfm hgm hfb hgb (hf.mono (by omega))
    (hg.mono (by omega))
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end WilsonRPG

section WilsonRev

open MassGap.RectWilson MassGap.RectTransfer MassGap.RectTorusState MassGap.CompactGauge
  MassGap.HiddenChain

/-- **The reflected Wilson slab has the transposed slab kernel** (`SU(N)`). For a bounded
measurable function `f` of a slab of `m + 2` slices and `m + 1` time links, the function `θf` that
reads the slices in reverse order and the time links inverted (`revG` with `ι = (·)⁻¹` on each
link) has slab kernel `tp (slabKer f)`: `slabKer_rev` with `wtR x A y = wtR y A⁻¹ x`
(`RectTransfer.tp_inv`) and the inversion invariance of the Haar measure
(`RectTransfer.measurePreserving_invAx`).

DERIVED: `0` is the time direction; `1` and `2` the offsets of the number of steps and slices. -/
theorem slabKer_rev_wtR {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    {T : {j : Fin 4 // j ≠ 0} → ℕ} (m : ℕ) {f : (ℕ → SlR 0 T N) → (ℕ → AxR 0 T N) → ℝ}
    (hfm : Measurable (fun r : (ℕ → SlR 0 T N) × (ℕ → AxR 0 T N) => f r.1 r.2)) {B : ℝ}
    (hfb : ∀ V A, |f V A| ≤ B) :
    slabKer (hS 0 T N) (hA 0 T N) (wtR 0 T N β) m
        (revG (MeasurableEquiv.piCongrRight (fun _ : TT 0 T => MeasurableEquiv.inv (SUN.SU N)))
          m f)
      = tp (slabKer (hS 0 T N) (hA 0 T N) (wtR 0 T N β) m f) := by
  funext x z
  exact slabKer_rev (wmeas_wtR β) (abs_wtR_le hN hβ) _ measurePreserving_invAx
    (fun x a y => by
      show wtR 0 T N β x a y = wtR 0 T N β y (fun t => (a t)⁻¹) x
      unfold wtR; rw [tp_inv]; ring) m hfm hfb x z

end WilsonRev

section WilsonRevG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.GaugeGroup

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The reflected Wilson slab has the transposed slab kernel** (every `GaugeGroup G`):
`slabKer_rev_wtR` over `G`, with `RectTransferG.tpG_inv` and
`RectTransferG.measurePreserving_invAxG`.

DERIVED: `0` is the time direction; `1` and `2` the offsets of the number of steps and slices. -/
theorem slabKer_rev_wtG {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (m : ℕ)
    {f : (ℕ → TorusChainG.SlG G M) → (ℕ → TorusChainG.AxG G M) → ℝ}
    (hfm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      f r.1 r.2)) {B : ℝ} (hfb : ∀ V A, |f V A| ≤ B) :
    slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) m
        (revG (MeasurableEquiv.piCongrRight
          (fun _ : TT 0 (TorusChain.Tc M) => MeasurableEquiv.inv G)) m f)
      = tp (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
          (TorusChainG.wtG G M β) m f) := by
  funext x z
  exact slabKer_rev (TorusChainG.wmeas_wtG β) (TorusChainG.abs_wtG_le hβ) _
    measurePreserving_invAxG
    (fun x a y => by
      show TorusChainG.wtG G M β x a y = TorusChainG.wtG G M β y (fun t => (a t)⁻¹) x
      unfold TorusChainG.wtG; rw [tpG_inv]; ring) m hfm hfb x z

end WilsonRevG

/-! ## 5. The whole connected correlation on the Wilson torus in reflection form -/

section WilsonFull

open MassGap.RectWilson MassGap.RectTransfer MassGap.RectTorusState MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingWilson MassGap.OpenAIBridgeSides

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **The connected correlation of two slab observables on the `SU(N)` Wilson torus, bounded by
reflected readings alone, uniform in the torus, from the seed.** If one torus of even side
`n ≥ 2` has `16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic torus of every
even side `L ≥ 2n` there are a normalized eigenfunction `φ` of `kT` and its eigenvalue `c ≠ 0` such
that for bounded measurable slab observables `f`, `g` of widths `w = 2v + 2`, `w' = 2v' + 2`,
read at times `0` and `w + p + 1` of `L = p + q + 2 + w + w'`, `p = 2a + j + 2`,
`q = 2a + j' + 2`, `4(w + w') + 8n ≤ L`,

    |⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩|
      ≤ (1/2)^⌊(j+1)/n⌋ √(R_f R_{θg}) + (1/2)^⌊(j'+1)/n⌋ √(R_{θf} R_g)
        + (1/2)^⌊(j+1)/n⌋ (1/2)^⌊(j'+1)/n⌋ √(H_f H_g)
        + (|α_f||α_g| + |α_f| √H_g + |α_g| √H_f + √(H_f H_g)) √((1/2)^⌊((p+q)/2+1)/n⌋),

with `R` the reflected readings (`refl`), `θf = revG (·)⁻¹ f` the observable of the reflected slab,
`H` the Hilbert–Schmidt reflected readings (`hsRead`) and `α` the vacuum readings (`vacRead`) of
the slab kernels. The sup bounds of `f`, `g` do not enter the constant. `gap_side_excited`,
`connK_rp_full_slab`, `slabKer_rev_wtR`, `OpenAIBridgeSlab.connK_eq_expect_slab`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `4` and `8` the slab condition of
`excited_le_slab`, and `4` the spacetime dimension; `1/2` the contraction; `2` the doubled side,
the least seed side, the least ratio `L / n`, the doubled widths and separations and the offsets
of `iter`; `0` the time direction, the first slice and the sign of the coupling; `1` the offsets
of `iter`, the separation and the unit norm. -/
theorem wilson_slab_conn_rp_full
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = 1 ∧
      (∀ z, ∫ y, (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) z y * φ y ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = c * φ z) ∧
      ∀ (f g : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N) → (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) → ℝ),
      Measurable (fun r : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N) × (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) => f r.1 r.2) →
      Measurable (fun r : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N) × (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) => g r.1 r.2) →
      ∀ A B : ℝ, (∀ V A', |f V A'| ≤ A) → (∀ V A', |g V A'| ≤ B) → ∀ v v' : ℕ,
      LocalUpTo (v + v + 2) f → LocalUpTo (v' + v' + 2) g → ∀ a j j' : ℕ,
      a + j + a + 2 + (a + j' + a + 2) + 2 + (v + v + 2) + (v' + v' + 2) = L →
      4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L →
      |(sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
          (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U)
            * g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))
        - (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
            (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U))
          * (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
            (fun U => g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))|
        ≤ (1 / 2) ^ ((j + 1) / n)
            * √(refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2) a
              * refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) (revG (MeasurableEquiv.piCongrRight (fun _ : TT 0 (tr (fun _ : Fin 4 => L) 0) => MeasurableEquiv.inv (SUN.SU N))) (v' + v' + 1) g)) (v' + v' + 2) a)
          + (1 / 2) ^ ((j' + 1) / n)
            * √(refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) (revG (MeasurableEquiv.piCongrRight (fun _ : TT 0 (tr (fun _ : Fin 4 => L) 0) => MeasurableEquiv.inv (SUN.SU N))) (v + v + 1) f)) (v + v + 2) a
              * refl (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2) a)
          + (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n)
            * √(hsRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2) a
              * hsRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2) a)
          + (|vacRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2)| * |vacRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2)|
              + |vacRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2)| * √(hsRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2) a)
              + |vacRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2)| * √(hsRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2) a)
              + √(hsRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) f) (v + v + 2) a
                * hsRead (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ (slabKer (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hA 0 (tr (fun _ : Fin 4 => L) 0) N) (wtR 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) g) (v' + v' + 2) a))
            * √((1 / 2) ^ (((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) / n)) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    OpenAIBridgeUniform.gap_side_excited hN hβ hn he h0 a' L hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig,
    fun f g hfm hgm A B hfb hgb v v' hf hg a j j' hpq hW => ?_⟩
  have hw := wmeas_wtR (μ := 0) (T := (tr (fun _ : Fin 4 => L) 0)) (N := N) β
  have hwb := abs_wtR_le (μ := 0) (T := (tr (fun _ : Fin 4 => L) 0)) hN hβ
  rw [slabKer_rev_wtR hN hβ (v + v + 1) hfm hfb, slabKer_rev_wtR hN hβ (v' + v' + 1) hgm hgb]
  have h := connK_rp_full_slab hφm hφb hφ1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (kT_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc hLe
    (bdd_slabKer (μ := (hS 0 (tr (fun _ : Fin 4 => L) 0) N)) (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := (hS 0 (tr (fun _ : Fin 4 => L) 0) N)) (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb (v' + v' + 1) hgm hgb)
    v v' a j j' hpq hW
  have heq := connK_eq_expect_slab hN hβ (L := fun _ : Fin 4 => L) (m := v + v + 1)
    (m' := v' + v' + 1) (p := a + j + a + 2) (q := a + j' + a + 2) (by show L = _; omega)
    hfm hgm hfb hgb (hf.mono (by omega)) (hg.mono (by omega))
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end WilsonFull

section WilsonFullG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingWilson MassGap.DoublingWilsonG MassGap.GaugeGroup
  MassGap.OpenAIBridgeSides MassGap.OpenAIBridgeGroups

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
/-- **The connected correlation of two slab observables on the Wilson torus of every gauge group,
bounded by reflected readings alone, uniform in the torus, from the seed**
(`wilson_slab_conn_rp_full` over a `GaugeGroup G`, side `M + 1`). `gap_side_excitedG`,
`connK_rp_full_slab`, `slabKer_rev_wtG`, `OpenAIBridgeSlab.connK_eq_expect_slabG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `4` and `8` the slab condition of
`excited_le_slab`, and `4` the spacetime dimension; `1/2` the contraction; `2` the doubled side,
the least seed side, the least ratio `L / n`, the doubled widths and separations and the offsets
of `iter`; `0` the time direction, the first slice and the sign of the coupling; `1` the offsets
of `iter`, the separation, the unit norm and the side `M + 1`. -/
theorem wilson_slab_conn_rp_fullG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (M : ℕ) (hLe : Even (M + 1)) (hL : 2 * n ≤ M + 1) :
    ∃ φ : (SpT 0 (TorusChain.Tc M) → G) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG G 0 (TorusChain.Tc M)) = 1 ∧
      (∀ z, ∫ y, (kTG G 0 (TorusChain.Tc M) β) z y * φ y ∂(hSG G 0 (TorusChain.Tc M)) = c * φ z) ∧
      ∀ (f g : (ℕ → SpT 0 (TorusChain.Tc M) → G) → (ℕ → TT 0 (TorusChain.Tc M) → G) → ℝ),
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc M) → G) × (ℕ → TT 0 (TorusChain.Tc M) → G) => f r.1 r.2) →
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc M) → G) × (ℕ → TT 0 (TorusChain.Tc M) → G) => g r.1 r.2) →
      ∀ A B : ℝ, (∀ V A', |f V A'| ≤ A) → (∀ V A', |g V A'| ≤ B) → ∀ v v' : ℕ,
      LocalUpTo (v + v + 2) f → LocalUpTo (v' + v' + 2) g → ∀ a j j' : ℕ,
      a + j + a + 2 + (a + j' + a + 2) + 2 + (v + v + 2) + (v' + v' + 2) = M + 1 →
      4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ M + 1 →
      |(sysRG G (fun _ : Fin 4 => M + 1)).expect (probHaar G) β
          (fun U => f (slabV (fun _ : Fin 4 => M + 1) 0 0 U) (slabA (fun _ : Fin 4 => M + 1) 0 0 U)
            * g (slabV (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))
        - (sysRG G (fun _ : Fin 4 => M + 1)).expect (probHaar G) β
            (fun U => f (slabV (fun _ : Fin 4 => M + 1) 0 0 U)
              (slabA (fun _ : Fin 4 => M + 1) 0 0 U))
          * (sysRG G (fun _ : Fin 4 => M + 1)).expect (probHaar G) β
            (fun U => g (slabV (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U)
              (slabA (fun _ : Fin 4 => M + 1) 0 (v + v + 2 + (a + j + a + 2 + 1)) U))|
        ≤ (1 / 2) ^ ((j + 1) / n)
            * √(refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2) a
              * refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) (revG (MeasurableEquiv.piCongrRight (fun _ : TT 0 (TorusChain.Tc M) => MeasurableEquiv.inv G)) (v' + v' + 1) g)) (v' + v' + 2) a)
          + (1 / 2) ^ ((j' + 1) / n)
            * √(refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) (revG (MeasurableEquiv.piCongrRight (fun _ : TT 0 (TorusChain.Tc M) => MeasurableEquiv.inv G)) (v + v + 1) f)) (v + v + 2) a
              * refl (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2) a)
          + (1 / 2) ^ ((j + 1) / n) * (1 / 2) ^ ((j' + 1) / n)
            * √(hsRead (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2) a
              * hsRead (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2) a)
          + (|vacRead (hSG G 0 (TorusChain.Tc M)) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2)| * |vacRead (hSG G 0 (TorusChain.Tc M)) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2)|
              + |vacRead (hSG G 0 (TorusChain.Tc M)) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2)| * √(hsRead (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2) a)
              + |vacRead (hSG G 0 (TorusChain.Tc M)) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2)| * √(hsRead (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2) a)
              + √(hsRead (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v + v + 1) f) (v + v + 2) a
                * hsRead (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β) c φ (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M)) (TorusChainG.wtG G M β) (v' + v' + 1) g) (v' + v' + 2) a))
            * √((1 / 2) ^ (((a + j + a + 2 + (a + j' + a + 2)) / 2 + 1) / n)) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    gap_side_excitedG hβ hn he h0 a' (M + 1) hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig,
    fun f g hfm hgm A B hfb hgb v v' hf hg a j j' hpq hW => ?_⟩
  have hw := TorusChainG.wmeas_wtG (G := G) (M := M) β
  have hwb := TorusChainG.abs_wtG_le (G := G) (M := M) hβ
  rw [slabKer_rev_wtG hβ (v + v + 1) hfm hfb, slabKer_rev_wtG hβ (v' + v' + 1) hgm hgb]
  have h := connK_rp_full_slab hφm hφb hφ1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (kTG_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc hLe
    (bdd_slabKer (μ := (hSG G 0 (TorusChain.Tc M))) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := (hSG G 0 (TorusChain.Tc M))) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb (v' + v' + 1) hgm hgb)
    v v' a j j' hpq hW
  have heq := connK_eq_expect_slabG hβ (M := M) (m := v + v + 1) (m' := v' + v' + 1)
    (p := a + j + a + 2) (q := a + j' + a + 2) (by omega) hfm hgm hfb hgb (hf.mono (by omega))
    (hg.mono (by omega))
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end WilsonFullG

end MassGap.OpenAIBridgeRP

#print axioms MassGap.OpenAIBridgeRP.kf_iter_add
#print axioms MassGap.OpenAIBridgeRP.pair_symm
#print axioms MassGap.OpenAIBridgeRP.rpRead_nonneg
#print axioms MassGap.OpenAIBridgeRP.rpRead_eq
#print axioms MassGap.OpenAIBridgeRP.refl_nonneg
#print axioms MassGap.OpenAIBridgeRP.sqrt_refl
#print axioms MassGap.OpenAIBridgeRP.hsRead_nonneg
#print axioms MassGap.OpenAIBridgeRP.sqrt_hsRead
#print axioms MassGap.OpenAIBridgeRP.abs_trc_le
#print axioms MassGap.OpenAIBridgeRP.trc_sand
#print axioms MassGap.OpenAIBridgeRP.trK_sand
#print axioms MassGap.OpenAIBridgeRP.hs_sand_eq
#print axioms MassGap.OpenAIBridgeRP.hs_sand_eq2
#print axioms MassGap.OpenAIBridgeRP.abs_pair_rp
#print axioms MassGap.OpenAIBridgeRP.abs_cross_rp
#print axioms MassGap.OpenAIBridgeRP.conn_alg3
#print axioms MassGap.OpenAIBridgeRP.excited_le_of_le
#print axioms MassGap.OpenAIBridgeRP.connK_split
#print axioms MassGap.OpenAIBridgeRP.connK_rp
#print axioms MassGap.OpenAIBridgeRP.connK_rp_slab
#print axioms MassGap.OpenAIBridgeRP.connK_refl_read
#print axioms MassGap.OpenAIBridgeRP.hs_conv_rem_le
#print axioms MassGap.OpenAIBridgeRP.abs_trK_hs
#print axioms MassGap.OpenAIBridgeRP.abs_trOne_hs
#print axioms MassGap.OpenAIBridgeRP.conn_alg4
#print axioms MassGap.OpenAIBridgeRP.connK_rp_full
#print axioms MassGap.OpenAIBridgeRP.connK_rp_full_slab
#print axioms MassGap.OpenAIBridgeRP.reflMoment_le_torus
#print axioms MassGap.OpenAIBridgeRP.reflMoment_le_torus_ratio
#print axioms MassGap.OpenAIBridgeRP.swap_int
#print axioms MassGap.OpenAIBridgeRP.swap_pair
#print axioms MassGap.OpenAIBridgeRP.cutV_scons
#print axioms MassGap.OpenAIBridgeRP.cutV_zero_const
#print axioms MassGap.OpenAIBridgeRP.update_scons
#print axioms MassGap.OpenAIBridgeRP.update_const_zero
#print axioms MassGap.OpenAIBridgeRP.measurable_cutV
#print axioms MassGap.OpenAIBridgeRP.measurable_updateAt
#print axioms MassGap.OpenAIBridgeRP.slabKer_back
#print axioms MassGap.OpenAIBridgeRP.slabKer_rev
#print axioms MassGap.OpenAIBridgeRP.wilson_slab_conn_rp
#print axioms MassGap.OpenAIBridgeRP.wilson_slab_conn_rpG
#print axioms MassGap.OpenAIBridgeRP.slabKer_rev_wtR
#print axioms MassGap.OpenAIBridgeRP.slabKer_rev_wtG
#print axioms MassGap.OpenAIBridgeRP.wilson_slab_conn_rp_full
#print axioms MassGap.OpenAIBridgeRP.wilson_slab_conn_rp_fullG
