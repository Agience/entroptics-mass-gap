import Mathlib
import MassGap.OpenAIBridgeSides
import MassGap.RectTorusState
import MassGap.SecondEigenvalue
import MassGap.SectorDefect
import MassGap.ReadsSlabWilson

/-!
# MassGap.OpenAIBridgeUniform — the periodic trace ratio with a constant uniform in the torus, and the trace identity with insertions

`OpenAIBridgeCluster.connTorus_decay` bounds the connected periodic trace ratio by
`A B (1 + 9 σ_1) ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋)`, `σ_1 = hs(k − c φ⊗φ)/c²`. `σ_1` counts every
excited state of the slice, so that constant grows with the spatial volume. It enters only through
the wrap-around term `Tr(A R^t B R^{L−t})`, `R` the excited part of the transfer, which that module
bounds by Cauchy–Schwarz. This module bounds it by Hölder and removes `σ_1`.

## 1. A trace Hölder inequality, at the kernel level

For a symmetric bounded measurable kernel `r` on a probability space and bounded measurable `a`, `b`
(`|a| ≤ A`, `|b| ≤ B`), with `trPair r a b p q = Tr(A R^{p+1} B R^{q+1})`:

* `abs_trPair_le` — if `p + q = 2i`, then `|Tr(A R^{p+1} B R^{q+1})| ≤ A B hs(r^{∗(i+1)})`, i.e.
  `|Tr(A R^s B R^u)| ≤ A B Tr R^{s+u}` for `s + u` even.

No trace class, Schatten norm or spectral theorem is used; Mathlib has none of them for kernels.
The proof is a Cauchy–Schwarz step iterated: for `u = s + 2d`, `R^u = R^d R^h` gives
`T² ≤ A² Tr R^{2h} · Tr(B R^{2s} B R^{2d})` (`trPair_sq_le`, through `trPair_split`,
`hs_conv_mulR`, `diag_conv_comm`), a pair again summing to `2h`; the balanced pair is bounded
directly (`abs_trPair_balanced`). `trPair_pow_le` iterates `j` times:
`|T|^{2^j} ≤ (AB)^{2^j} (Tr R^{2h})^{2^j − 1} W`, with `W` a finite sum of Hilbert–Schmidt norms, and
`SecondEigenvalue.le_of_pow_two_pow_le` removes `W`.

## 2. The connected trace ratio with a uniform constant

* `connTorus_le_excited` — `|connTorus| ≤ A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋ + 5 σ_{L/2})`: the
  wrap-around term is now `A B σ_{L/2}`, and `σ_1` is gone.
* `connTorus_uniform` — if `σ_{L/2} ≤ (1/2)^⌊(L/2)/n⌋`, then
  `|connTorus| ≤ 6 A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋)`.
* `hs_iter_rem_add_le`, `excited_add_le` — the gap moves the excited weight down:
  `σ_{j+l} ≤ (1/2)^{2⌊l/n⌋} σ_j`.
* `wilson_gap_excited`, `gap_side_excited` — the gap of `DoublingSharp.wilson_gap_sharp` and of
  `OpenAIBridgeSides.gap_side`, kept together with the excited weight the dyadic climb bounds.
* `wilson_connTorus_uniform` (side `2^k n`) and `connTorus_even_side_uniform` (every even side
  `L ≥ 2n`) — `|connTorus| ≤ 6 A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋)`, constant `6`, from the seed.

## 3. The trace identity with insertions

* `Zc_trPair` — the closed slice chain of `RectTorusState.ZcR` with `a` at slice `0` and `b` at slice
  `p + 1` is `trPair (Haar) kT a b p q`;
* `spSlice L μ t U` — the spatial links of slice `t` of a torus configuration;
  `corrNum_slab` — `∫ a(U|₀) b(U|_{p+1}) e^{−β S(U)} dU = trPair (Haar) kT a b p q` on the torus of
  time extent `p + q + 2` (`RectTorusState.corrNumR`);
* `trPair_one_right`, `trPair_one_left` — one insertion is `trIns`;
* `connTorus_eq_expect` — `connTorus (Haar) kT a b p q = ⟨a_0 b_{p+1}⟩ − ⟨a_0⟩⟨b_{p+1}⟩` for the
  Wilson Gibbs expectation of the torus;
* `wilson_conn_even_side` — on the cubic torus of every even side `L ≥ 2n`, from the seed,
  `|⟨a_0 b_{p+1}⟩ − ⟨a_0⟩⟨b_{p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋)` for bounded
  measurable functions `a`, `b` of the spatial links of one slice.

## Scope

The observables are functions of the spatial links of one time slice (the transfer's state space);
an observable reading axis links or several slices is not covered. The bound is on the torus of
side `L` at every even `L ≥ 2n`; the thermodynamic limit is not taken here.
-/

namespace MassGap.OpenAIBridgeUniform

open MeasureTheory Real
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster

/-! ## 1. A trace Hölder inequality -/

section Holder

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **Cauchy–Schwarz for iterated integrals of bounded kernels**:
`(∫∫ F G)² ≤ hs(F) hs(G)`. The quadratic `∫∫ (F − l G)² = hs F − 2 l ∫∫ F G + l² hs G` is
nonnegative at every `l` (`ReadsSlabWilson.sq_le_of_quad`).

DERIVED: `2` is the square and the cross term of the quadratic. -/
theorem sq_iint_mul_le {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) :
    (∫ x, ∫ y, F x y * G x y ∂μ ∂μ) ^ 2 ≤ hs μ F * hs μ G := by
  refine ReadsSlabWilson.sq_le_of_quad (hs_nonneg _) (fun l => ?_)
  have h1 : Bdd (fun x y => F x y ^ 2) := SectorDefect.bdd_sq hF
  have h2 : Bdd (fun x y => -2 * l * (F x y * G x y)) :=
    FluxSectorBound.bdd_mul (bdd_const _) (FluxSectorBound.bdd_mul hF hG)
  have h3 : Bdd (fun x y => l ^ 2 * G x y ^ 2) :=
    FluxSectorBound.bdd_mul (bdd_const _) (SectorDefect.bdd_sq hG)
  have e : hs μ F - 2 * l * (∫ x, ∫ y, F x y * G x y ∂μ ∂μ) + l ^ 2 * hs μ G
      = ∫ x, ∫ y, ((F x y ^ 2 + -2 * l * (F x y * G x y)) + l ^ 2 * G x y ^ 2) ∂μ ∂μ := by
    rw [iint_add (h1.add h2) h3, iint_add h1 h2]
    simp_rw [integral_const_mul]
    unfold hs
    ring
  rw [e]
  exact integral_nonneg fun x => integral_nonneg fun y => by
    show (0 : ℝ) ≤ _
    nlinarith [sq_nonneg (F x y - l * G x y)]

/-- **A bounded weight costs its square in Hilbert–Schmidt norm**: `|w| ≤ A` pointwise gives
`hs(w R) ≤ A² hs(R)`.

DERIVED: `2` is the square of the Hilbert–Schmidt norm. -/
theorem hs_weight_le {w R : X → X → ℝ} (hw : Bdd w) (hR : Bdd R) {A : ℝ}
    (hA : ∀ x y, |w x y| ≤ A) : hs μ (fun x y => w x y * R x y) ≤ A ^ 2 * hs μ R := by
  have hwR := SectorDefect.bdd_sq (FluxSectorBound.bdd_mul hw hR)
  have hR2 : Bdd (fun x y => A ^ 2 * R x y ^ 2) :=
    FluxSectorBound.bdd_mul (bdd_const _) (SectorDefect.bdd_sq hR)
  calc hs μ (fun x y => w x y * R x y) ≤ |hs μ (fun x y => w x y * R x y)| := le_abs_self _
    _ ≤ ∫ x, ∫ y, A ^ 2 * R x y ^ 2 ∂μ ∂μ :=
        abs_iint_le hwR hR2 (fun x y => by
          rw [abs_of_nonneg (sq_nonneg _), mul_pow]
          exact mul_le_mul_of_nonneg_right
            (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA x y) 2) (sq_nonneg _))
    _ = A ^ 2 * hs μ R := by simp_rw [integral_const_mul]; rfl

/-- **The trace is cyclic on bounded kernels**: `∫ (P ∗ Q)(x, x) = ∫ (Q ∗ P)(x, x)`, one Fubini swap.

DERIVED: no numeral appears in the statement. -/
theorem diag_conv_comm {P Q : X → X → ℝ} (hP : Bdd P) (hQ : Bdd Q) :
    ∫ x, conv μ P Q x x ∂μ = ∫ x, conv μ Q P x x ∂μ := by
  obtain ⟨CQ, hCQ⟩ := hQ.bdd
  have hQt : Bdd (fun x y => Q y x) := ⟨hQ.meas.comp measurable_swap, CQ, fun x y => hCQ y x⟩
  have hB : Bdd (fun x y => P x y * Q y x) := FluxSectorBound.bdd_mul hP hQt
  obtain ⟨C, hC⟩ := hB.bdd
  simp only [conv]
  rw [swap_bdd hB.meas hC]
  congr 1; funext y; congr 1; funext x; ring

variable {r : X → X → ℝ} (hr : Bdd r) (hrs : ∀ x y, r x y = r y x)
  {a b : X → ℝ} (ham : Measurable a) (hbm : Measurable b) {A B : ℝ}
  (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B)

include hr hrs in
/-- `trPair` of a symmetric kernel with both powers read in the same order:
`Tr(A R^{p+1} B R^{q+1}) = ∫∫ (a(x) r^{∗(p+1)}(x,y)) (b(y) r^{∗(q+1)}(x,y))`.

DERIVED: no numeral appears in the statement. -/
theorem trPair_eq_sym (a b : X → ℝ) (p q : ℕ) :
    trPair μ r a b p q = ∫ x, ∫ y, (a x * iter μ r p x y) * (b y * iter μ r q x y) ∂μ ∂μ := by
  unfold trPair
  congr 1; funext x; congr 1; funext y
  rw [CyclicKernel.iter_symm hr hrs q y x]; ring

include hr hrs ham hbm hab hbb in
/-- **Cyclicity of the two-insertion trace**: `Tr(A R^{p+1} B R^{q+1}) = Tr(B R^{q+1} A R^{p+1})`.

DERIVED: no numeral appears in the statement. -/
theorem trPair_comm (p q : ℕ) : trPair μ r a b p q = trPair μ r b a q p := by
  rw [trPair_eq_sym hr hrs a b p q, trPair_eq_sym hr hrs b a q p]
  have hB : Bdd (fun x y => (a x * iter μ r p x y) * (b y * iter μ r q x y)) :=
    FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul (bdd_left ham hab) (hr.iter (μ := μ) p))
      (FluxSectorBound.bdd_mul (bdd_right hbm hbb) (hr.iter (μ := μ) q))
  obtain ⟨C, hC⟩ := hB.bdd
  rw [swap_bdd hB.meas hC]
  congr 1; funext y; congr 1; funext x
  rw [CyclicKernel.iter_symm hr hrs p x y, CyclicKernel.iter_symm hr hrs q x y]; ring

include hr hrs ham hbm hab hbb in
/-- **The balanced pair**: `|Tr(A R^{i+1} B R^{i+1})| ≤ A B hs(r^{∗(i+1)})`, pointwise, since the
two powers coincide and `r^{∗(i+1)}(x,y)² ≥ 0`.

DERIVED: no numeral appears in the statement. -/
theorem abs_trPair_balanced (i : ℕ) :
    |trPair μ r a b i i| ≤ A * B * hs μ (iter μ r i) := by
  rw [trPair_eq_sym hr hrs a b i i]
  have hRi := hr.iter (μ := μ) i
  refine (abs_iint_le
    (FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul (bdd_left ham hab) hRi)
      (FluxSectorBound.bdd_mul (bdd_right hbm hbb) hRi))
    (FluxSectorBound.bdd_mul (bdd_const (A * B)) (FluxSectorBound.bdd_mul hRi hRi))
    (fun x y => ?_)).trans (le_of_eq ?_)
  · have e : a x * iter μ r i x y * (b y * iter μ r i x y)
        = (a x * b y) * (iter μ r i x y * iter μ r i x y) := by ring
    rw [e, abs_mul, abs_of_nonneg (mul_self_nonneg (iter μ r i x y))]
    exact mul_le_mul_of_nonneg_right (HiddenChain.abs_mul_le_of (hab x) (hbb y)) (mul_self_nonneg _)
  · unfold hs; simp_rw [integral_const_mul, sq]

include hr hrs ham hbm hab hbb in
/-- **The crude bound**: if `hs(r^{∗(p+1)}) ≤ W` and `hs(r^{∗(q+1)}) ≤ W`, then
`|Tr(A R^{p+1} B R^{q+1})| ≤ A B W`, by `sq_iint_mul_le` and `hs_weight_le`. It is the starting
point of the iteration, where `W` may grow with the volume.

DERIVED: no numeral appears in the statement. -/
theorem abs_trPair_le_sum {W : ℝ} {p q : ℕ} (hp : hs μ (iter μ r p) ≤ W)
    (hq : hs μ (iter μ r q) ≤ W) : |trPair μ r a b p q| ≤ A * B * W := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure μ
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hab x0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbb x0)
  have hW0 : 0 ≤ W := (hs_nonneg _).trans hp
  have hsq := sq_iint_mul_le (μ := μ)
    (FluxSectorBound.bdd_mul (bdd_left ham hab) (hr.iter (μ := μ) p))
    (FluxSectorBound.bdd_mul (bdd_right hbm hbb) (hr.iter (μ := μ) q))
  have h1 := hs_weight_le (μ := μ) (bdd_left ham hab) (hr.iter (μ := μ) p) (fun x _ => hab x)
  have h2 := hs_weight_le (μ := μ) (bdd_right hbm hbb) (hr.iter (μ := μ) q) (fun _ y => hbb y)
  rw [← trPair_eq_sym hr hrs a b p q] at hsq
  have key : trPair μ r a b p q ^ 2 ≤ (A * B * W) ^ 2 := by
    calc _ ≤ _ := hsq
      _ ≤ (A ^ 2 * hs μ (iter μ r p)) * (B ^ 2 * hs μ (iter μ r q)) :=
          mul_le_mul h1 h2 (hs_nonneg _) (mul_nonneg (sq_nonneg _) (hs_nonneg _))
      _ ≤ (A ^ 2 * W) * (B ^ 2 * W) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp (sq_nonneg A))
            (mul_le_mul_of_nonneg_left hq (sq_nonneg B)) (mul_nonneg (sq_nonneg _) (hs_nonneg _))
            (mul_nonneg (sq_nonneg _) hW0)
      _ = (A * B * W) ^ 2 := by ring
  rw [← sq_abs] at key
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (mul_nonneg hA0 hB0) hW0)
    two_ne_zero).mp key

include hr hrs hbm hab hbb in
/-- **The wrap-around trace, split at the middle power**: with `h = p + d + 1`,
`Tr(A R^{p+1} B R^{2h − p − 1}) = ∫∫ (a(x) r^{∗(h+1)}(x,z)) Y(x,z)`, `Y = (r^{∗(p+1)} b) ∗ r^{∗(d+1)}`.
`R^{q+1} = R^{d+1} R^{h+1}` (`iter_add`) and one Fubini swap.

DERIVED: `1` is the offset of `iter`. -/
theorem trPair_split (p d : ℕ) :
    trPair μ r a b p (d + (p + d + 1) + 1)
      = ∫ x, ∫ z, (a x * iter μ r (p + d + 1) x z)
          * conv μ (fun x y => iter μ r p x y * b y) (iter μ r d) x z ∂μ ∂μ := by
  unfold trPair
  congr 1; funext x
  have hRp := hr.iter (μ := μ) p
  have hRd := hr.iter (μ := μ) d
  have hRH := hr.iter (μ := μ) (p + d + 1)
  obtain ⟨Cp, hCp⟩ := hRp.bdd
  obtain ⟨CH, hCH⟩ := hRH.bdd
  have hB : Bdd (fun y z => (a x * iter μ r p x y * b y)
      * (iter μ r d y z * iter μ r (p + d + 1) z x)) :=
    FluxSectorBound.bdd_mul
      (bdd_left (a := fun y => a x * iter μ r p x y * b y)
        ((measurable_const.mul (hRp.row x)).mul hbm)
        (fun y => HiddenChain.abs_mul_le_of (HiddenChain.abs_mul_le_of (hab x) (hCp x y)) (hbb y)))
      (FluxSectorBound.bdd_mul hRd
        (bdd_right (a := fun z => iter μ r (p + d + 1) z x) (hRH.col x) (fun z => hCH z x)))
  obtain ⟨CB, hCB⟩ := hB.bdd
  calc ∫ y, a x * iter μ r p x y * b y * iter μ r (d + (p + d + 1) + 1) y x ∂μ
      = ∫ y, ∫ z, (a x * iter μ r p x y * b y)
          * (iter μ r d y z * iter μ r (p + d + 1) z x) ∂μ ∂μ := by
        congr 1; funext y
        rw [iter_add hr d (p + d + 1)]
        simp only [conv]
        rw [integral_const_mul]
    _ = ∫ z, ∫ y, (a x * iter μ r p x y * b y)
          * (iter μ r d y z * iter μ r (p + d + 1) z x) ∂μ ∂μ := swap_bdd hB.meas hCB
    _ = ∫ z, (a x * iter μ r (p + d + 1) x z)
          * conv μ (fun x y => iter μ r p x y * b y) (iter μ r d) x z ∂μ := by
        congr 1; funext z
        simp only [conv]
        rw [← integral_const_mul]
        congr 1; funext y
        rw [CyclicKernel.iter_symm hr hrs (p + d + 1) z x]; ring

include hr hrs hbm hbb in
/-- **The Hilbert–Schmidt norm of `R^{p+1} B R^{d+1}` is a trace with two insertions**:
`hs((r^{∗(p+1)} b) ∗ r^{∗(d+1)}) = Tr(B R^{2p+2} B R^{2d+2})`. With `M = r^{∗(p+1)} b` and its transpose
`Mᵀ = b r^{∗(p+1)}`: `hs(M ∗ R^{d+1}) = Tr(M ∗ R^{2d+2} ∗ Mᵀ) = Tr(R^{2d+2} ∗ Mᵀ ∗ M)` (`conv_assoc`,
`diag_conv_comm`), and `Mᵀ ∗ M = b r^{∗(2p+2)} b`.

DERIVED: `1` is the offset of `iter`; `2` the square of the Hilbert–Schmidt norm. -/
theorem hs_conv_mulR (p d : ℕ) :
    hs μ (conv μ (fun x y => iter μ r p x y * b y) (iter μ r d))
      = trPair μ r b b (p + p + 1) (d + d + 1) := by
  have hRp := hr.iter (μ := μ) p
  have hRd := hr.iter (μ := μ) d
  have hM : Bdd (fun x y => iter μ r p x y * b y) := FluxSectorBound.bdd_mul hRp (bdd_right hbm hbb)
  have hMt : Bdd (fun x y => b x * iter μ r p x y) := FluxSectorBound.bdd_mul (bdd_left hbm hbb) hRp
  have hD2 := hr.iter (μ := μ) (d + d + 1)
  have hYt : ∀ x z, conv μ (fun x y => iter μ r p x y * b y) (iter μ r d) x z
      = conv μ (iter μ r d) (fun x y => b x * iter μ r p x y) z x := by
    intro x z
    simp only [conv]
    congr 1; funext y
    rw [CyclicKernel.iter_symm hr hrs d y z, CyclicKernel.iter_symm hr hrs p x y]; ring
  have h1 : hs μ (conv μ (fun x y => iter μ r p x y * b y) (iter μ r d))
      = ∫ x, conv μ (conv μ (fun x y => iter μ r p x y * b y) (iter μ r d))
          (conv μ (iter μ r d) (fun x y => b x * iter μ r p x y)) x x ∂μ := by
    unfold hs
    congr 1; funext x
    show _ = ∫ z, conv μ (fun x y => iter μ r p x y * b y) (iter μ r d) x z
      * conv μ (iter μ r d) (fun x y => b x * iter μ r p x y) z x ∂μ
    congr 1; funext z
    rw [← hYt x z, sq]
  have h2 : conv μ (conv μ (fun x y => iter μ r p x y * b y) (iter μ r d))
        (conv μ (iter μ r d) (fun x y => b x * iter μ r p x y))
      = conv μ (fun x y => iter μ r p x y * b y)
        (conv μ (iter μ r (d + d + 1)) (fun x y => b x * iter μ r p x y)) := by
    rw [← conv_assoc hM hRd (hRd.conv (μ := μ) hMt), conv_assoc hRd hRd hMt, ← iter_add hr d d]
  have h3 : ∫ x, conv μ (fun x y => iter μ r p x y * b y)
        (conv μ (iter μ r (d + d + 1)) (fun x y => b x * iter μ r p x y)) x x ∂μ
      = ∫ x, conv μ (conv μ (iter μ r (d + d + 1)) (fun x y => b x * iter μ r p x y))
        (fun x y => iter μ r p x y * b y) x x ∂μ :=
    diag_conv_comm hM (hD2.conv (μ := μ) hMt)
  have h4 : conv μ (conv μ (iter μ r (d + d + 1)) (fun x y => b x * iter μ r p x y))
        (fun x y => iter μ r p x y * b y)
      = conv μ (iter μ r (d + d + 1))
        (conv μ (fun x y => b x * iter μ r p x y) (fun x y => iter μ r p x y * b y)) :=
    (conv_assoc hD2 hMt hM).symm
  have h5 : ∀ w y, conv μ (fun x y => b x * iter μ r p x y) (fun x y => iter μ r p x y * b y) w y
      = b w * iter μ r (p + p + 1) w y * b y := by
    intro w y
    rw [iter_add hr p p]
    simp only [conv]
    rw [← integral_const_mul, ← integral_mul_const]
    congr 1; funext x; ring
  have h6 : ∫ y, conv μ (iter μ r (d + d + 1))
        (conv μ (fun x y => b x * iter μ r p x y) (fun x y => iter μ r p x y * b y)) y y ∂μ
      = trPair μ r b b (p + p + 1) (d + d + 1) := by
    unfold trPair
    congr 1; funext y
    show ∫ w, iter μ r (d + d + 1) y w
      * conv μ (fun x y => b x * iter μ r p x y) (fun x y => iter μ r p x y * b y) w y ∂μ = _
    congr 1; funext w
    rw [h5 w y, CyclicKernel.iter_symm hr hrs (d + d + 1) y w,
      CyclicKernel.iter_symm hr hrs (p + p + 1) w y]
    ring
  rw [h1, h2, h3, h4, h6]

include hr hrs ham hbm hab hbb in
/-- **One Cauchy–Schwarz step on the wrap-around trace**: with `h = p + d + 1`,
`Tr(A R^{p+1} B R^{2h−p−1})² ≤ A² hs(r^{∗(h+1)}) · Tr(B R^{2p+2} B R^{2d+2})`. The new pair of
powers again sums to `2h + 2`, with `b` at both ends. It is `trPair_split`, `sq_iint_mul_le`,
`hs_weight_le` and `hs_conv_mulR`.

DERIVED: `1` is the offset of `iter`; `2` the square. -/
theorem trPair_sq_le (p d : ℕ) :
    trPair μ r a b p (d + (p + d + 1) + 1) ^ 2
      ≤ A ^ 2 * hs μ (iter μ r (p + d + 1)) * trPair μ r b b (p + p + 1) (d + d + 1) := by
  rw [trPair_split (μ := μ) hr hrs hbm hab hbb p d, ← hs_conv_mulR (μ := μ) hr hrs hbm hbb p d]
  have hRH := hr.iter (μ := μ) (p + d + 1)
  have hY : Bdd (conv μ (fun x y => iter μ r p x y * b y) (iter μ r d)) :=
    (FluxSectorBound.bdd_mul (hr.iter (μ := μ) p) (bdd_right hbm hbb)).conv (hr.iter (μ := μ) d)
  calc _ ≤ hs μ (fun x z => a x * iter μ r (p + d + 1) x z)
        * hs μ (conv μ (fun x y => iter μ r p x y * b y) (iter μ r d)) :=
        sq_iint_mul_le (FluxSectorBound.bdd_mul (bdd_left ham hab) hRH) hY
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (hs_weight_le (bdd_left ham hab) hRH (fun x _ => hab x)) (hs_nonneg _)

include hr hrs in
/-- **The iterated Cauchy–Schwarz bound**: for every pair `p + q = 2i` and every `j`,
`|Tr(A R^{p+1} B R^{q+1})|^{2^j} ≤ (AB)^{2^j} hs(r^{∗(i+1)})^{2^j − 1} W`, with
`W = Σ_{m ≤ 2i} hs(r^{∗(m+1)})`. At `j = 0` it is `abs_trPair_le_sum`; a step squares, applies
`trPair_sq_le` (or `abs_trPair_balanced` at `p = q`, or `trPair_comm` when `p > q`) and uses the
statement at `j` on the new pair with `b` at both ends.

DERIVED: `2` is the dyadic base of the iteration and the square; `1` the offset of `iter` and the
range bound. -/
theorem trPair_pow_le (i j : ℕ) :
    ∀ {a b : X → ℝ}, Measurable a → Measurable b → ∀ {A B : ℝ}, (∀ x, |a x| ≤ A) →
      (∀ x, |b x| ≤ B) → ∀ p q : ℕ, p + q = i + i →
      |trPair μ r a b p q| ^ (2 ^ j)
        ≤ (A * B) ^ (2 ^ j) * hs μ (iter μ r i) ^ (2 ^ j - 1)
          * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) := by
  induction j with
  | zero =>
    intro a b ham hbm A B hab hbb p q hpq
    simp only [pow_zero, pow_one, Nat.sub_self, mul_one]
    exact abs_trPair_le_sum hr hrs ham hbm hab hbb
      (Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega)))
      (Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega)))
  | succ j ih =>
    obtain ⟨K, hK⟩ : ∃ K, 2 ^ j = K + 1 := ⟨2 ^ j - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
    have eA : 2 ^ (j + 1) - 1 = 2 * K + 1 := by rw [e2, hK]; omega
    have eB : 2 ^ (j + 1) = 2 * K + 2 := by rw [e2, hK]; ring
    have ih' : ∀ {b : X → ℝ}, Measurable b → ∀ {B : ℝ}, (∀ x, |b x| ≤ B) → ∀ p q : ℕ,
        p + q = i + i → |trPair μ r b b p q| ^ (K + 1)
          ≤ (B * B) ^ (K + 1) * hs μ (iter μ r i) ^ K
            * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) := by
      intro b hbm B hbb p q hpq
      have h := ih hbm hbm hbb hbb p q hpq
      rwa [show 2 ^ j - 1 = K by rw [hK]; omega, hK] at h
    have key : ∀ {a b : X → ℝ}, Measurable a → Measurable b → ∀ {A B : ℝ}, (∀ x, |a x| ≤ A) →
        (∀ x, |b x| ≤ B) → ∀ p q : ℕ, p + q = i + i → p ≤ q →
        |trPair μ r a b p q| ^ (2 * K + 2)
          ≤ (A * B) ^ (2 * K + 2) * hs μ (iter μ r i) ^ (2 * K + 1)
            * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) := by
      intro a b ham hbm A B hab hbb p q hpq hle
      obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure μ
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hab x0)
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbb x0)
      have hτ0 : 0 ≤ hs μ (iter μ r i) := hs_nonneg _
      have hτW : hs μ (iter μ r i) ≤ ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) :=
        Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega))
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq]
        have hpi : p = i := by omega
        have hT : |trPair μ r a b p p| ≤ A * B * hs μ (iter μ r i) := by
          rw [← hpi]; exact abs_trPair_balanced hr hrs ham hbm hab hbb p
        calc |trPair μ r a b p p| ^ (2 * K + 2) ≤ (A * B * hs μ (iter μ r i)) ^ (2 * K + 2) :=
              pow_le_pow_left₀ (abs_nonneg _) hT _
          _ = (A * B) ^ (2 * K + 2) * hs μ (iter μ r i) ^ (2 * K + 1) * hs μ (iter μ r i) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hτW
              (mul_nonneg (pow_nonneg (mul_nonneg hA0 hB0) _) (pow_nonneg hτ0 _))
      · obtain ⟨d, rfl⟩ : ∃ d, q = d + (p + d + 1) + 1 := ⟨(q - p - 2) / 2, by omega⟩
        have hi : p + d + 1 = i := by omega
        subst hi
        have hstep := trPair_sq_le (μ := μ) hr hrs ham hbm hab hbb p d
        have hT'0 : 0 ≤ trPair μ r b b (p + p + 1) (d + d + 1) := by
          rw [← hs_conv_mulR (μ := μ) hr hrs hbm hbb p d]; exact hs_nonneg _
        have hT' := ih' hbm hbb (p + p + 1) (d + d + 1) (by omega)
        rw [abs_of_nonneg hT'0] at hT'
        calc |trPair μ r a b p (d + (p + d + 1) + 1)| ^ (2 * K + 2)
            = (trPair μ r a b p (d + (p + d + 1) + 1) ^ 2) ^ (K + 1) := by
              rw [← sq_abs]; ring
          _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hstep _
          _ = (A ^ 2) ^ (K + 1) * hs μ (iter μ r (p + d + 1)) ^ (K + 1)
                * trPair μ r b b (p + p + 1) (d + d + 1) ^ (K + 1) := by ring
          _ ≤ (A ^ 2) ^ (K + 1) * hs μ (iter μ r (p + d + 1)) ^ (K + 1) * _ :=
              mul_le_mul_of_nonneg_left hT'
                (mul_nonneg (pow_nonneg (sq_nonneg A) _) (pow_nonneg hτ0 _))
          _ = _ := by ring
    intro a b ham hbm A B hab hbb p q hpq
    rw [eA, eB]
    rcases le_total p q with h | h
    · exact key ham hbm hab hbb p q hpq h
    · rw [trPair_comm (μ := μ) hr hrs ham hbm hab hbb p q, mul_comm A B]
      exact key hbm ham hbb hab q p (by omega) h

include hr hrs ham hbm hab hbb in
/-- **Hölder for the two-insertion trace** (the trace-class inequality
`|Tr(A R^s B R^u)| ≤ ‖A‖ ‖B‖ Tr |R|^{s+u}` at even `s + u`, for a symmetric bounded kernel): if
`p + q = 2i`, then `|Tr(A R^{p+1} B R^{q+1})| ≤ A B hs(r^{∗(i+1)})`. From `trPair_pow_le`, the
`2^j`-th power of the left side is at most `(W / hs(r^{∗(i+1)}))` times that of the right side for
every `j`, and `SecondEigenvalue.le_of_pow_two_pow_le` drops the factor; when
`hs(r^{∗(i+1)}) = 0` the step `j = 1` already gives `0`.

DERIVED: `2` is the dyadic base of the iteration and the square; `1` the offset of `iter`, the
first step and the range bound; `0` the vanishing case. -/
theorem abs_trPair_le (p q i : ℕ) (hpq : p + q = i + i) :
    |trPair μ r a b p q| ≤ A * B * hs μ (iter μ r i) := by
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure μ
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hab x0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbb x0)
  have hτ0 : 0 ≤ hs μ (iter μ r i) := hs_nonneg _
  have hτW : hs μ (iter μ r i) ≤ ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) :=
    Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega))
  rcases hτ0.lt_or_eq with hτ | hτ
  · have hτne := hτ.ne'
    refine SecondEigenvalue.le_of_pow_two_pow_le (abs_nonneg _)
      (mul_nonneg (mul_nonneg hA0 hB0) hτ0) (div_pos (hτ.trans_le hτW) hτ) (fun j => ?_)
    have h := trPair_pow_le (μ := μ) hr hrs i j ham hbm hab hbb p q hpq
    obtain ⟨K, hK⟩ : ∃ K, 2 ^ j = K + 1 :=
      ⟨2 ^ j - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    rw [show 2 ^ j - 1 = K by rw [hK]; omega, hK] at h
    rw [hK]
    calc _ ≤ _ := h
      _ = (A * B) ^ (K + 1) * hs μ (iter μ r i) ^ K
          * ((∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m)) / hs μ (iter μ r i)
            * hs μ (iter μ r i)) := by rw [div_mul_cancel₀ _ hτne]
      _ = _ := by ring
  · have h := trPair_pow_le (μ := μ) hr hrs i 1 ham hbm hab hbb p q hpq
    have e0 : (A * B) ^ 2 ^ 1 * hs μ (iter μ r i) ^ (2 ^ 1 - 1)
        * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) = 0 := by
      rw [← hτ]; norm_num
    rw [e0] at h
    have h3 : |trPair μ r a b p q| ^ 2 = 0 := le_antisymm (by simpa using h) (sq_nonneg _)
    rw [(pow_eq_zero_iff two_ne_zero).mp h3, ← hτ]
    simp

end Holder

/-! ## 2. The connected trace ratio with a uniform constant -/

section Corr

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) {n : ℕ}
  (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖
      ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖)

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The connected two-slice torus correlation with the wrap-around term bounded by Hölder**: on
the periodic chain of `L = p + q + 2` copies of `k` (`L` even), with insertions `|a| ≤ A`, `|b| ≤ B`
at time separation `t = p + 1`,

    |connTorus μ k a b p q| ≤ A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋ + 5 σ_{L/2}),

`σ_j = excited μ k c φ j`. It is `OpenAIBridgeCluster.connTorus_le` with the excited–excited term
`Tr(A R^t B R^{L−t})` bounded by `abs_trPair_le` (`≤ A B hs(r^{∗(L/2)}) = A B |c|^L σ_{L/2}`)
instead of by Cauchy–Schwarz: only the excited weight at half the torus enters, not `σ_t`,
`σ_{L−t}`.

DERIVED: `5 = 1 + 4` counts `σ_{L/2}` from the wrap-around term and `4 σ_{L/2}` from
`OpenAIBridgeCluster.conn_alg`; `1/2` is the contraction of the gap hypothesis; `1` and `2` are the
offsets of `iter`, so `t = p + 1`, `L − t = q + 1` and `L/2 = (p + q)/2 + 1`; `0` the excluded
eigenvalue. -/
theorem connTorus_le_excited (hc0 : c ≠ 0) {a b : X → ℝ} (ham : Measurable a) (hbm : Measurable b)
    {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (p q : ℕ) (hpq : Even (p + q)) :
    |connTorus μ k a b p q| ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
      + 5 * excited μ k c φ ((p + q) / 2 + 1)) := by
  obtain ⟨i, hi⟩ := hpq
  have hi2 : (p + q) / 2 = i := by omega
  rw [hi2]
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hrp := hr.iter (μ := μ) p
  have hrq := hr.iter (μ := μ) q
  have hri := hr.iter (μ := μ) i
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hu0 : 0 < |c| ^ (p + 1) := pow_pos hc _
  have hv0 : 0 < |c| ^ (q + 1) := pow_pos hc _
  have hΛ : 0 < |c| ^ (p + 1) * |c| ^ (q + 1) := mul_pos hu0 hv0
  have hev : Even (p + 1 + (q + 1)) := ⟨i + 1, by omega⟩
  have hcc : c ^ (p + 1) * c ^ (q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add, ← pow_add, hev.pow_abs c]
  have hune := hu0.ne'
  have hvne := hv0.ne'
  have hσ : ∀ j : ℕ, excited μ k c φ (j + 1) = hs μ (iter μ (rem k c φ) j) / |c| ^ (2 * (j + 1)) :=
    fun j => by unfold excited; rw [Nat.add_sub_cancel]
  have hsqi : |c| ^ (2 * (i + 1)) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add]; congr 1; omega
  have hφsq : Integrable (fun x => φ x ^ 2) μ := integrable_of_bdd (hφm.pow_const 2) (C := Bφ ^ 2)
    (fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2)
  have hφφ : Integrable (fun x => φ x * φ x) μ := by simpa [sq] using hφsq
  have hφ1' : ∫ x, φ x * φ x ∂μ = 1 := by simpa [sq] using hφ1
  -- the one-insertion trace
  have hone : ∀ (f : X → ℝ), Measurable f → ∀ F : ℝ, (∀ x, |f x| ≤ F) →
      trIns μ k f (p + q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) * (∫ x, f x * (φ x * φ x) ∂μ
        + (∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ) / (|c| ^ (p + 1) * |c| ^ (q + 1)))
      ∧ |∫ x, f x * (φ x * φ x) ∂μ| ≤ F
      ∧ |(∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ) / (|c| ^ (p + 1) * |c| ^ (q + 1))|
        ≤ F * excited μ k c φ (i + 1) := by
    intro f hfm F hfb
    obtain ⟨Ci, hCi⟩ := hri.bdd
    have hD0 : ∀ x, 0 ≤ ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ :=
      fun x => integral_nonneg fun y => sq_nonneg _
    have hDb : ∀ x, |∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ| ≤ Ci ^ 2 := fun x =>
      abs_integral_le fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCi x y) 2
    have hDm : Measurable fun x => ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ :=
      measurable_integral_right (hri.meas.pow_const 2)
    have i1 : Integrable (fun x => f x * (φ x * φ x)) μ :=
      integrable_of_bdd (hfm.mul (hφm.mul hφm)) (C := F * (Bφ * Bφ))
        (fun x => HiddenChain.abs_mul_le_of (hfb x) (HiddenChain.abs_mul_le_of (hφb x) (hφb x)))
    have i2 : Integrable (fun x => f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ) μ :=
      integrable_of_bdd (hfm.mul hDm) (C := F * Ci ^ 2)
        (fun x => HiddenChain.abs_mul_le_of (hfb x) (hDb x))
    have hDint : Integrable (fun x => ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ) μ :=
      integrable_of_bdd hDm hDb
    have hD : ∀ x, iter μ (rem k c φ) (p + q + 1) x x = ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ :=
      fun x => by rw [hi]; exact iter_rem_diag hkm hkb hsym hφm hφb i x
    have e : ∀ x, f x * iter μ k (p + q + 1) x x
        = |c| ^ (p + 1) * |c| ^ (q + 1) * (f x * (φ x * φ x))
          + f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ := by
      intro x
      rw [iter_decomp hk hsym hφm hφb hφ1 heig (p + q + 1) x x, hD x, ← hcc]
      ring
    refine ⟨?_, ?_, ?_⟩
    · unfold trIns
      simp_rw [e]
      rw [integral_add (i1.const_mul _) i2, integral_const_mul]
      field_simp
    · calc |∫ x, f x * (φ x * φ x) ∂μ| ≤ ∫ x, |f x * (φ x * φ x)| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ x, F * (φ x * φ x) ∂μ := integral_mono i1.abs (hφφ.const_mul F) (fun x => by
            rw [abs_mul, abs_of_nonneg (mul_self_nonneg (φ x))]
            exact mul_le_mul_of_nonneg_right (hfb x) (mul_self_nonneg _))
        _ = F := by rw [integral_const_mul, hφ1', mul_one]
    · have h1 : |∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ|
          ≤ F * hs μ (iter μ (rem k c φ) i) := by
        calc |∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ|
            ≤ ∫ x, |f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ x, F * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ :=
              integral_mono i2.abs (hDint.const_mul F) (fun x => by
                rw [abs_mul, abs_of_nonneg (hD0 x)]
                exact mul_le_mul_of_nonneg_right (hfb x) (hD0 x))
          _ = F * hs μ (iter μ (rem k c φ) i) := by rw [integral_const_mul]; rfl
      rw [abs_div, abs_of_pos hΛ, hσ i, hsqi, mul_div_assoc']
      exact div_le_div_of_nonneg_right h1 hΛ.le
  obtain ⟨hNa, hα, hea⟩ := hone a ham A hab
  obtain ⟨hNb, hβ', heb⟩ := hone b hbm B hbb
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hα
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hβ'
  -- the partition function
  have hZ : trPow μ k (p + q + 1)
      = |c| ^ (p + 1) * |c| ^ (q + 1) * (1 + excited μ k c φ (i + 1)) := by
    have h := (hone (fun _ => 1) measurable_const 1 (fun _ => by simp)).1
    have h1 : trIns μ k (fun _ => 1) (p + q + 1) = trPow μ k (p + q + 1) := by
      unfold trIns trPow; simp
    rw [← h1, h]
    simp only [one_mul]
    rw [hφ1', hσ i, hsqi]
    rfl
  -- the two-insertion trace, term by term
  have Ba : ∀ x, |a x * φ x| ≤ A * Bφ := fun x => HiddenChain.abs_mul_le_of (hab x) (hφb x)
  have Bb : ∀ x, |b x * φ x| ≤ B * Bφ := fun x => HiddenChain.abs_mul_le_of (hbb x) (hφb x)
  have hG1 : Bdd (fun x y => c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x))
      * (b y * (φ y * φ y))) :=
    FluxSectorBound.bdd_mul
      (bdd_left (measurable_const.mul (ham.mul (hφm.mul hφm)))
        (fun x => HiddenChain.abs_mul_le_of (le_refl _)
          (HiddenChain.abs_mul_le_of (hab x) (HiddenChain.abs_mul_le_of (hφb x) (hφb x)))))
      (bdd_right (hbm.mul (hφm.mul hφm))
        (fun y => HiddenChain.abs_mul_le_of (hbb y) (HiddenChain.abs_mul_le_of (hφb y) (hφb y))))
  have hG2 : Bdd (fun x y => c ^ (p + 1) * (a x * φ x)
      * (iter μ (rem k c φ) q x y * (b y * φ y))) :=
    FluxSectorBound.bdd_mul
      (bdd_left (measurable_const.mul (ham.mul hφm))
        (fun x => HiddenChain.abs_mul_le_of (le_refl _) (Ba x)))
      (FluxSectorBound.bdd_mul hrq (bdd_right (hbm.mul hφm) Bb))
  have hG3 : Bdd (fun x y => c ^ (q + 1) * (a x * φ x)
      * (iter μ (rem k c φ) p x y * (b y * φ y))) :=
    FluxSectorBound.bdd_mul
      (bdd_left (measurable_const.mul (ham.mul hφm))
        (fun x => HiddenChain.abs_mul_le_of (le_refl _) (Ba x)))
      (FluxSectorBound.bdd_mul hrp (bdd_right (hbm.mul hφm) Bb))
  have hG4 : Bdd (fun x y => a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y) :=
    FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul
      (bdd_left ham hab) hrp) (bdd_right hbm hbb)) hrq
  have e2 : ∀ x y, a x * iter μ k p x y * b y * iter μ k q y x
      = c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y))
        + c ^ (p + 1) * (a x * φ x) * (iter μ (rem k c φ) q x y * (b y * φ y))
        + c ^ (q + 1) * (a x * φ x) * (iter μ (rem k c φ) p x y * (b y * φ y))
        + a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y := by
    intro x y
    rw [iter_decomp hk hsym hφm hφb hφ1 heig p x y, iter_decomp hk hsym hφm hφb hφ1 heig q y x,
      CyclicKernel.iter_symm hr hrs q y x]
    ring
  have hsplit : trPair μ k a b p q
      = ∫ x, ∫ y, c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y)) ∂μ ∂μ
        + ∫ x, ∫ y, c ^ (p + 1) * (a x * φ x) * (iter μ (rem k c φ) q x y * (b y * φ y)) ∂μ ∂μ
        + ∫ x, ∫ y, c ^ (q + 1) * (a x * φ x) * (iter μ (rem k c φ) p x y * (b y * φ y)) ∂μ ∂μ
        + ∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ := by
    rw [← iint_add hG1 hG2, ← iint_add (hG1.add hG2) hG3, ← iint_add ((hG1.add hG2).add hG3) hG4]
    unfold trPair
    congr 1; funext x; congr 1; funext y; exact e2 x y
  have v1 : ∫ x, ∫ y, c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y)) ∂μ ∂μ
      = |c| ^ (p + 1) * |c| ^ (q + 1) * ((∫ x, a x * (φ x * φ x) ∂μ)
        * ∫ y, b y * (φ y * φ y) ∂μ) := by
    have h1 : ∀ x, ∫ y, c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y)) ∂μ
        = c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * ∫ y, b y * (φ y * φ y) ∂μ :=
      fun x => integral_const_mul _ _
    simp_rw [h1]
    rw [integral_mul_const, integral_const_mul, hcc]
    ring
  have v2 : ∫ x, ∫ y, c ^ (p + 1) * (a x * φ x) * (iter μ (rem k c φ) q x y * (b y * φ y)) ∂μ ∂μ
      = c ^ (p + 1) * ∫ x, a x * φ x
          * kernelFun (iter μ (rem k c φ) q) μ (fun y => b y * φ y) x ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [integral_const_mul]; simp only [kernelFun]; ring
  have v3 : ∫ x, ∫ y, c ^ (q + 1) * (a x * φ x) * (iter μ (rem k c φ) p x y * (b y * φ y)) ∂μ ∂μ
      = c ^ (q + 1) * ∫ x, a x * φ x
          * kernelFun (iter μ (rem k c φ) p) μ (fun y => b y * φ y) x ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [integral_const_mul]; simp only [kernelFun]; ring
  -- the vacuum-to-excited terms
  have hsq2 : ∀ (f : X → ℝ), Measurable f → ∀ F : ℝ, (∀ x, |f x| ≤ F) →
      ∫ x, (f x * φ x) ^ 2 ∂μ ≤ F ^ 2 := by
    intro f hfm F hfb
    calc ∫ x, (f x * φ x) ^ 2 ∂μ ≤ ∫ x, F ^ 2 * φ x ^ 2 ∂μ :=
          integral_mono (integrable_of_bdd ((hfm.mul hφm).pow_const 2) (C := (F * Bφ) ^ 2)
            (fun x => by
              rw [abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) (HiddenChain.abs_mul_le_of (hfb x) (hφb x)) 2))
            (hφsq.const_mul _) (fun x => by
              rw [mul_pow]
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2)
      _ = F ^ 2 := by rw [integral_const_mul, hφ1, mul_one]
  have I2 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap q
    (ham.mul hφm) (hbm.mul hφm) Ba Bb hA0 hB0 (hsq2 a ham A hab) (hsq2 b hbm B hbb)
  have I3 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap p
    (ham.mul hφm) (hbm.mul hφm) Ba Bb hA0 hB0 (hsq2 a ham A hab) (hsq2 b hbm B hbb)
  -- the excited–excited term, by Hölder
  have I4 : |∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ|
      ≤ A * B * hs μ (iter μ (rem k c φ) i) := by
    have e : ∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ
        = trPair μ (rem k c φ) a b p q := by
      unfold trPair; congr 1; funext x; congr 1; funext y
      rw [CyclicKernel.iter_symm hr hrs q y x]
    rw [e]
    exact abs_trPair_le hr hrs ham hbm hab hbb p q i hi
  -- assemble
  set I2v := ∫ x, a x * φ x * kernelFun (iter μ (rem k c φ) q) μ (fun y => b y * φ y) x ∂μ
  set I3v := ∫ x, a x * φ x * kernelFun (iter μ (rem k c φ) p) μ (fun y => b y * φ y) x ∂μ
  set T4 := ∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ
  set Λ := |c| ^ (p + 1) * |c| ^ (q + 1) with hΛdef
  have hΛne : Λ ≠ 0 := hΛ.ne'
  have hN2 : trPair μ k a b p q = Λ * ((∫ x, a x * (φ x * φ x) ∂μ) * ∫ y, b y * (φ y * φ y) ∂μ
      + (c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4) / Λ) := by
    rw [hsplit, v1, v2, v3]
    field_simp
    ring
  have hsum : |c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4|
      ≤ Λ * (A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + excited μ k c φ (i + 1))) := by
    have a2 : |c ^ (p + 1) * I2v|
        ≤ |c| ^ (p + 1) * ((1 / 2) ^ ((q + 1) / n) * |c| ^ (q + 1) * A * B) := by
      rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left I2 hu0.le
    have a3 : |c ^ (q + 1) * I3v|
        ≤ |c| ^ (q + 1) * ((1 / 2) ^ ((p + 1) / n) * |c| ^ (p + 1) * A * B) := by
      rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left I3 hv0.le
    have eq : |c| ^ (p + 1) * ((1 / 2) ^ ((q + 1) / n) * |c| ^ (q + 1) * A * B)
        + |c| ^ (q + 1) * ((1 / 2) ^ ((p + 1) / n) * |c| ^ (p + 1) * A * B)
        + A * B * hs μ (iter μ (rem k c φ) i)
        = Λ * (A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
          + excited μ k c φ (i + 1))) := by
      rw [hσ i, hsqi, hΛdef]
      field_simp
      ring
    calc |c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4|
        ≤ |c ^ (p + 1) * I2v| + |c ^ (q + 1) * I3v| + |T4| := abs_add_three _ _ _
      _ ≤ _ := add_le_add (add_le_add a2 a3) I4
      _ = _ := eq
  have he : |(c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4) / Λ|
      ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + excited μ k c φ (i + 1)) := by
    rw [abs_div, abs_of_pos hΛ, div_le_iff₀ hΛ]
    exact le_of_le_of_eq hsum (mul_comm _ _)
  have hσ0 : 0 ≤ excited μ k c φ (i + 1) := by
    rw [hσ i]; exact div_nonneg (hs_nonneg _) (by positivity)
  have key := conn_alg hΛ hσ0 hα hβ' hea heb
    (e := (c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4) / Λ)
  unfold connTorus
  rw [hN2, hZ, hNa, hNb]
  calc _ ≤ _ := key
    _ ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n) + excited μ k c φ (i + 1))
        + 4 * (A * B) * excited μ k c φ (i + 1) := add_le_add he le_rfl
    _ = _ := by ring

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **Exponential clustering of the torus correlation with a constant uniform in the torus**: under
the hypotheses of `connTorus_le_excited`, if the excited weight at half the torus is at most the
decay at half the torus, `σ_{L/2} ≤ (1/2)^⌊(L/2)/n⌋`, then

    |connTorus μ k a b p q| ≤ 6 A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋).

The smaller of `t`, `L − t` is at most `L/2`, so `(1/2)^⌊(L/2)/n⌋` is at most the sum of the two
decaying terms.

DERIVED: `6 = 1 + 5` is the gap terms plus the constant `5` of `connTorus_le_excited`; `1/2` is the
contraction of the gap hypothesis; `1` and `2` are the offsets of `iter`; `0` the excluded
eigenvalue. -/
theorem connTorus_uniform (hc0 : c ≠ 0) {a b : X → ℝ} (ham : Measurable a) (hbm : Measurable b)
    {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (p q : ℕ) (hpq : Even (p + q))
    (hσ : excited μ k c φ ((p + q) / 2 + 1) ≤ (1 / 2) ^ (((p + q) / 2 + 1) / n)) :
    |connTorus μ k a b p q| ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  have h := connTorus_le_excited hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 ham hbm hab hbb
    p q hpq
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure μ
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hab x0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbb x0)
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ ((p + 1) / n) := by positivity
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ ((q + 1) / n) := by positivity
  have hmin : (1 / 2 : ℝ) ^ (((p + q) / 2 + 1) / n)
      ≤ (1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n) := by
    rcases le_total p q with h' | h'
    · have : (1 / 2 : ℝ) ^ (((p + q) / 2 + 1) / n) ≤ (1 / 2) ^ ((p + 1) / n) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_div_right (by omega))
      linarith
    · have : (1 / 2 : ℝ) ^ (((p + q) / 2 + 1) / n) ≤ (1 / 2) ^ ((q + 1) / n) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_div_right (by omega))
      linarith
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  calc |connTorus μ k a b p q| ≤ _ := h
    _ ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + 5 * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n))) := by
        refine mul_le_mul_of_nonneg_left ?_ hAB
        linarith
    _ = _ := by ring

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The gap moves the excited weight down by whole blocks**:
`hs(r^{∗(i+m+2)}) ≤ ((1/2)^⌊(m+1)/n⌋ |c|^(m+1))² hs(r^{∗(i+1)})`, `r = k − c φ⊗φ`. Row `x` of
`r^{∗(i+m+2)}` is `r^{∗(m+1)}` applied to row `x` of `r^{∗(i+1)}` (`iter_add`, symmetry), and
`OpenAIBridgeCluster.sq_integral_remFun_le` bounds each row. At `i = 0` it is
`OpenAIBridgeCluster.hs_iter_rem_le`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter`; `2` the square. -/
theorem hs_iter_rem_add_le (i m : ℕ) :
    hs μ (iter μ (rem k c φ) (i + m + 1))
      ≤ ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * hs μ (iter μ (rem k c φ) i) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hri := hr.iter (μ := μ) i
  obtain ⟨Ci, hCi⟩ := hri.bdd
  have hrow : ∀ x z, iter μ (rem k c φ) (i + m + 1) x z
      = kernelFun (iter μ (rem k c φ) m) μ (iter μ (rem k c φ) i x) z := by
    intro x z
    rw [iter_add hr i m]
    show ∫ y, iter μ (rem k c φ) i x y * iter μ (rem k c φ) m y z ∂μ
      = ∫ y, iter μ (rem k c φ) m z y * iter μ (rem k c φ) i x y ∂μ
    congr 1; funext y; rw [CyclicKernel.iter_symm hr (rem_symm hsym) m y z, mul_comm]
  have hrm := hr.iter (μ := μ) (i + m + 1)
  obtain ⟨Cm, hCm⟩ := hrm.bdd
  unfold hs
  calc ∫ x, ∫ z, iter μ (rem k c φ) (i + m + 1) x z ^ 2 ∂μ ∂μ
      ≤ ∫ x, ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2
          * ∫ z, iter μ (rem k c φ) i x z ^ 2 ∂μ ∂μ := by
        refine integral_mono
          (integrable_of_bdd (measurable_integral_right (hrm.meas.pow_const 2)) (C := Cm ^ 2)
            (fun x => abs_integral_le fun z => by
              rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCm x z) 2))
          ((integrable_of_bdd (measurable_integral_right (hri.meas.pow_const 2)) (C := Ci ^ 2)
            (fun x => abs_integral_le fun z => by
              rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCi x z) 2)).const_mul _)
          (fun x => ?_)
        simp only [hrow x]
        exact sq_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap m (hri.row x)
          (fun y => hCi x y)
    _ = _ := by rw [integral_const_mul]

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The relative excited weight decays along the torus**: `σ_{j+l} ≤ (1/2)^{2⌊l/n⌋} σ_j` for
`j, l ≥ 1`, `σ_j = excited μ k c φ j`. It is `hs_iter_rem_add_le` divided by `|c|^{2(j+l)}`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `2` the square; `1` the least `j` and `l`
and the offset of `iter`; `0` the excluded eigenvalue. -/
theorem excited_add_le (hc0 : c ≠ 0) (j l : ℕ) (hj : 1 ≤ j) (hl : 1 ≤ l) :
    excited μ k c φ (j + l) ≤ (1 / 2) ^ (2 * (l / n)) * excited μ k c φ j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hc : 0 < |c| := abs_pos.mpr hc0
  have H := hs_iter_rem_add_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap j' l'
  unfold excited
  rw [show j' + 1 + (l' + 1) - 1 = j' + l' + 1 by omega, Nat.add_sub_cancel]
  have hC1 : |c| ^ (2 * (j' + 1)) ≠ 0 := pow_ne_zero _ hc.ne'
  rw [div_le_iff₀ (pow_pos hc _)]
  calc hs μ (iter μ (rem k c φ) (j' + l' + 1))
      ≤ ((1 / 2) ^ ((l' + 1) / n) * |c| ^ (l' + 1)) ^ 2 * hs μ (iter μ (rem k c φ) j') := H
    _ = (1 / 2) ^ (2 * ((l' + 1) / n)) * |c| ^ (2 * (l' + 1))
          * (hs μ (iter μ (rem k c φ) j') / |c| ^ (2 * (j' + 1)) * |c| ^ (2 * (j' + 1))) := by
        rw [div_mul_cancel₀ _ hC1]; ring
    _ = (1 / 2) ^ (2 * ((l' + 1) / n)) * (hs μ (iter μ (rem k c φ) j') / |c| ^ (2 * (j' + 1)))
          * |c| ^ (2 * (j' + 1 + (l' + 1))) := by ring

end Corr

/-! ## 3. On the Wilson torus -/

section Wilson

open MassGap.RectWilson MassGap.RectTransfer MassGap.DoublingRecursion MassGap.DoublingWilson
  MassGap.OpenAIBridgeSides

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **The gap of `DoublingSharp.wilson_gap_sharp` with its excited weight**: on the torus of side
`2^k n`, the normalized bounded eigenfunction `φ` of the slice kernel, its eigenvalue `c ≠ 0`,
`|c| = ‖K‖`, the gap `‖Kⁿ f‖ ≤ ½ ‖K‖ⁿ ‖f‖` off `φ`, and the excited weight at half the torus,
`σ_{2^k n/2} ≤ (1/2)^{2^k}` (`DoublingSharp.excited_le_corner_sharp`). The proof is that of
`wilson_gap_sharp`, which keeps only the gap.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `1/2` its contraction; `2` the
doubled side, the least seed side, the `L²` exponent and the half torus; `0` the time direction of
the slice, the sign of the coupling and the excluded eigenvalue; `1` the kernel bound and the unit
norm. -/
theorem wilson_gap_excited
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ φ : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ, ∃ hφm : Measurable φ, ∃ Bφ : ℝ,
      ∃ hφb : ∀ x, |φ x| ≤ Bφ, ∫ x, φ x ^ 2 ∂(hS 0 (tr (ext n (corner k)) 0) N) = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧
      (∀ z, ∫ y, kT 0 (tr (ext n (corner k)) 0) N β z y * φ y ∂(hS 0 (tr (ext n (corner k)) 0) N)
        = c * φ z) ∧
      |c| = ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)‖ ∧
      (∀ f : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N),
        inner ℝ f (KernelGap.vac (μ := hS 0 (tr (ext n (corner k)) 0) N) hφm hφb) = 0 →
        ‖((kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
            zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
            (hS 0 (tr (ext n (corner k)) 0) N)‖ ^ n * ‖f‖) ∧
      excited (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) c φ
        (2 ^ k * n / 2) ≤ (1 / 2) ^ (2 ^ k) := by
  set T := tr (ext n (corner k)) 0
  have hfr := factRep hN hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xW N n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact h0
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 T]
  obtain ⟨n', hn'⟩ := he
  set j := 2 ^ k * n' with hjdef
  have hj : 1 ≤ j := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hjdef]; exact Nat.mul_le_mul h1 h2
  have hpf := powerFacts (μ := hS 0 T N) (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (kT_symm β) hφm hφb hφ1 heig hc hc0 j hj
  have hm : ext n (corner k) 0 = 2 * j := by simp only [ext, corner, hjdef, hn']; ring
  have h1 : xW N n β (corner k) = Real.log (F N β 0 T (2 * j)) := by
    rw [xW_eq hN hβ hn ⟨n', hn'⟩ (corner k) 0, hm]
  have h2 : xW N n β (corner k + E 0) = Real.log (F N β 0 T (2 * (2 * j))) := by
    rw [xW_eq hN hβ hn ⟨n', hn'⟩ (corner k + E 0) 0, tr_ext_add, ext_add_self, hm]
  have hexc := DoublingSharp.excited_le_corner_sharp hx hp hΔ k hpf h1 h2
  have hidx : 2 ^ k * n / 2 = j := by
    rw [hn', hjdef, show 2 ^ k * (n' + n') = 2 * (2 ^ k * n') by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  refine ⟨φ, hφm, B, hφb, hφ1, c, hc0, heig, hc, fun f hf => ?_, by rw [hidx]; exact hexc⟩
  exact KernelGap.gap_of_excited (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) hφm hφb hφ1 heig hc hc0 k n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

include hN hβ hn he in
/-- **The gap of `OpenAIBridgeSides.gap_side` with its excited weight**: on the cubic torus of
even side `L`, `2^(a+1) n ≤ L ≤ 2^(a+3) n`, the normalized bounded eigenfunction `φ` of the slice
kernel, its eigenvalue `c ≠ 0`, `|c| = ‖K‖`, the gap off `φ`, and a level `j0 ≥ 1` with
`4 j0 ≤ L` at which the excited weight is at most `(1/2)^{2^a}`. The proof is that of `gap_side`,
which keeps only the gap.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `3` is the exponent of the largest
ratio of `gap_side`; `2` the doubled side, the least seed side, the `L²` exponent, the contraction
`1/2` and the two doublings in `2 (2 j0) ≤ L`; `0` the time direction of the slice, the sign of
the coupling and the excluded eigenvalue; `1` the unit norm, the kernel bound, the first level and
the least `j0`. -/
theorem gap_side_excited
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (a L : ℕ) (hLe : Even L) (hlo : 2 ^ (a + 1) * n ≤ L) (hhi : L ≤ 2 ^ (a + 3) * n) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ, ∃ hφm : Measurable φ, ∃ Bφ : ℝ,
      ∃ hφb : ∀ x, |φ x| ≤ Bφ, ∫ x, φ x ^ 2 ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧
      (∀ z, ∫ y, kT 0 (tr (fun _ : Fin 4 => L) 0) N β z y * φ y
        ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = c * φ z) ∧
      |c| = ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
          (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ∧
      (∀ f : Lp ℝ 2 (hS 0 (tr (fun _ : Fin 4 => L) 0) N),
        inner ℝ f (KernelGap.vac (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N) hφm hφb) = 0 →
        ‖((kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
          (hS 0 (tr (fun _ : Fin 4 => L) 0) N)) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) 1
            (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
            (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (hS 0 (tr (fun _ : Fin 4 => L) 0) N)‖ ^ n
            * ‖f‖) ∧
      ∃ j0 : ℕ, 1 ≤ j0 ∧ 2 * (2 * j0) ≤ L ∧
        excited (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ j0
          ≤ (1 / 2) ^ (2 ^ a) := by
  set T := tr (fun _ : Fin 4 => L) 0 with hTdef
  -- the dyadic climb to corner `a`
  have hfr := factRep hN hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hxs := DoublingSharp.positiveS_of_facts hfr
  have hΔ0 : Δ (xW N n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact h0
  have hit := DoublingSharp.iterate_sharp hxs hp (by linarith) a
  have hq1 : ((1 : ℝ) / 4) ^ (2 ^ a) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := a))
    simpa using this
  have hq0 : 0 ≤ ((1 : ℝ) / 4) ^ (2 ^ a) := by positivity
  -- the levels
  obtain ⟨n', hn'⟩ := he
  set j0 := 2 ^ a * n' with hj0def
  have hj0 : 1 ≤ j0 := by
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hj0def]; exact Nat.mul_le_mul h1 h2
  have hm0 : 2 * j0 = 2 ^ a * n := by rw [hj0def, hn']; ring
  have hL4 : 2 * (2 * j0) ≤ L := by
    have : 2 * (2 * j0) = 2 ^ (a + 1) * n := by rw [hm0, pow_succ]; ring
    omega
  have hL8 : L ≤ 4 * (2 * (2 * j0)) := by
    have : 4 * (2 * (2 * j0)) = 2 ^ (a + 3) * n := by rw [hm0, pow_add]; ring
    omega
  have hM : (0 : ℝ) < 2 * ((2 * j0 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((2 * j0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j0)
    linarith
  set ρ : ℝ := (L : ℝ) / (2 * ((2 * j0 : ℕ) : ℝ)) with hρdef
  have hρ : ρ * (2 * ((2 * j0 : ℕ) : ℝ)) = L := by rw [hρdef]; field_simp
  have hρ1 : 1 ≤ ρ := by
    rw [hρdef, le_div_iff₀ hM, one_mul]
    exact_mod_cast hL4
  have hρ4 : ρ ≤ 4 := by
    rw [hρdef, div_le_iff₀ hM]
    exact_mod_cast hL8
  have hx := climb_yW hN hβ hj0 hLe hL4 hρ hρ1 hρ4
  -- the base of the mixed lattice is the dyadic corner `a`
  have hbase : Δ (yW N (2 * j0) L β) ![0, 0, 0, 0] = Δ (xW N n β) (corner a) := by
    obtain ⟨s0, s1⟩ := sides_base n a L hm0
    unfold Δ yW xW
    rw [s0, s1]
  have hD : Δ (yW N (2 * j0) L β) ![0, 0, 0, 0] ≤ 1 / 1000 := by rw [hbase]; linarith
  have hcl := climb hx hρ4 hD
  rw [hbase] at hcl
  -- the eigenvector on the slice of side `L`
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 T N) (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) (K_pos hN hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 T]
  have hpf : DoublingPower.PowerFacts (F N β 0 T) |c|
      (excited (hS 0 T N) (kT 0 T N β) c φ j0) (2 * j0) :=
    powerFacts (μ := hS 0 T N) (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (kT_symm β) hφm hφb hφ1 heig hc hc0 j0 hj0
  have hL2 : 2 ≤ L := by omega
  have hpd : p (yW N (2 * j0) L β) 0 ![0, 2, 2, 2]
      = DoublingPower.defect (F N β 0 T) (2 * j0) := by
    have hv : (![0, 2, 2, 2] : Pt) 0 = 0 := rfl
    have l0 : lev (2 * j0) L 0 = 2 * j0 := by simp [lev]
    have l1 : lev (2 * j0) L (0 + 1) = 2 * (2 * j0) := by simp [lev]
    rw [p, yW_at hN hβ hj0 hLe hL2 ![0, 2, 2, 2] 0, yW_next hN hβ hj0 hLe hL2 ![0, 2, 2, 2] 0,
      tr_sides_top, hv, l0, l1]
    rfl
  rw [hpd] at hcl
  have hd14 : DoublingPower.defect (F N β 0 T) (2 * j0) ≤ 1 / 4 := by nlinarith
  have hexc0 := DoublingPower.excited_le_two_defect hpf hd14
  have hhalf : ((1 : ℝ) / 4) ^ (2 ^ a) ≤ (1 / 2) ^ (2 ^ a) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hexc : excited (hS 0 T N) (kT 0 T N β) c φ j0 ≤ (1 / 2) ^ (2 ^ a) := by nlinarith
  have hidx : 2 ^ a * n / 2 = j0 := by rw [← hm0]; omega
  refine ⟨φ, hφm, B, hφb, hφ1, c, hc0, heig, hc, fun f hf => ?_, j0, hj0, hL4, hexc⟩
  exact KernelGap.gap_of_excited (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) hφm hφb hφ1 heig hc hc0 a n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

include hN hβ hn he in
/-- **The connected periodic trace ratio on the torus of side `2^k n`, with a constant uniform in
the torus.** At every even seed side `n ≥ 2` with the seed of `wilson_gap_sharp` at `β ≥ 0`, on the
torus `ext n (corner k)` (side and time extent `L = 2^k n`) there are a normalized bounded
eigenfunction `φ` of the slice kernel `kT` and its eigenvalue `c ≠ 0` such that for all bounded
measurable `a`, `b` of the slice (`|a| ≤ A`, `|b| ≤ B`) and all `p + q + 2 = L`,

    |connTorus a b p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

It is `connTorus_uniform` with `σ_{L/2} ≤ (1/2)^{2^k} ≤ (1/2)^⌊(L/2)/n⌋` from `wilson_gap_excited`.
The constant `6` does not depend on `k`, the coupling or the spatial volume:
`OpenAIBridgeCluster.wilson_connTorus_decay` with `σ_1` removed.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of
`connTorus_uniform`; `1/2` the contraction; `2` the doubled side, the least seed side and the
offset of `iter` on the torus of `p + q + 2` steps; `0` the time direction of the slice, the sign of
the coupling and the excluded eigenvalue; `1` the offset of `iter` and the unit norm. -/
theorem wilson_connTorus_uniform
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ φ : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (ext n (corner k)) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (ext n (corner k)) 0) N β z y * φ y ∂(hS 0 (tr (ext n (corner k)) 0) N)
        = c * φ z) ∧
      ∀ (a b : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ p q : ℕ, p + q + 2 = ext n (corner k) 0 →
        |connTorus (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) a b p q|
          ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, hexc⟩ :=
    wilson_gap_excited hN hβ hn he h0 k
  refine ⟨φ, c, hc0, hφ1, heig, fun a b ham hbm A B hab hbb p q hpq => ?_⟩
  obtain ⟨n', hn'⟩ := he
  have h2 : ext n (corner k) 0 = 2 * (2 ^ k * n') := by simp only [ext, corner, hn']; ring
  have hidx : 2 ^ k * n / 2 = 2 ^ k * n' := by
    rw [hn', show 2 ^ k * (n' + n') = 2 * (2 ^ k * n') by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have hh : (p + q) / 2 + 1 = 2 ^ k * n / 2 := by
    rw [hidx]
    have h' := hpq
    rw [h2] at h'
    generalize 2 ^ k * n' = J at h' ⊢
    omega
  have hev : Even (p + q) := by
    have h' := hpq
    rw [h2] at h'
    generalize 2 ^ k * n' = J at h'
    exact ⟨J - 1, by omega⟩
  have hdiv : 2 ^ k * n / 2 / n ≤ 2 ^ k :=
    calc 2 ^ k * n / 2 / n ≤ 2 ^ k * n / n := Nat.div_le_div_right (Nat.div_le_self _ _)
      _ = 2 ^ k := Nat.mul_div_cancel _ (by omega)
  have hσ : excited (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) c φ
      ((p + q) / 2 + 1) ≤ (1 / 2) ^ (((p + q) / 2 + 1) / n) := by
    rw [hh]
    exact hexc.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hdiv)
  exact connTorus_uniform (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    hφm hφb hφ1 heig hc hgap hc0 ham hbm hab hbb p q hev hσ

include hN hβ hn he in
/-- **The connected periodic trace ratio on the cubic torus of every even side `L ≥ 2n`, with a
constant uniform in the torus.** There are a normalized bounded eigenfunction `φ` of the slice
kernel `kT` of the torus of side `L` and its eigenvalue `c ≠ 0` such that for all bounded measurable
`a`, `b` of the slice (`|a| ≤ A`, `|b| ≤ B`) and all `p + q + 2 = L`,

    |connTorus a b p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

`gap_side_excited` gives `σ_{j0} ≤ (1/2)^{2^a} ≤ 1/2` at a level `4 j0 ≤ L`; `excited_add_le` moves
it to half the torus, `σ_{L/2} ≤ (1/2)^{2⌊(L/2 − j0)/n⌋ + 1} ≤ (1/2)^⌊(L/2)/n⌋` since
`L/2 ≤ 2 (L/2 − j0)`; `connTorus_uniform` closes. It is
`OpenAIBridgeSides.connTorus_even_side` with `σ_1` removed.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of
`connTorus_uniform`; `1/2` the contraction; `2` the doubled side, the least seed side, the least
ratio `L / n` and the offset of `iter` on the torus of `p + q + 2` steps; `0` the time direction of
the slice, the sign of the coupling and the excluded eigenvalue; `1` the offset of `iter` and the
unit norm. -/
theorem connTorus_even_side_uniform
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (fun _ : Fin 4 => L) 0) N β z y * φ y
        ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = c * φ z) ∧
      ∀ (a b : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ p q : ℕ, p + q + 2 = L →
        |connTorus (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
            a b p q|
          ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    gap_side_excited hN hβ hn he h0 a' L hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig, fun a b ham hbm A B hab hbb p q hpq => ?_⟩
  have hev : Even (p + q) := by
    obtain ⟨L', hL'⟩ := hLe
    exact ⟨L' - 1, by omega⟩
  have hn0 : 0 < n := by omega
  have hl : 1 ≤ (p + q) / 2 + 1 - j0 := by omega
  have hadd := excited_add_le (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    hφm hφb hφ1 heig hc hgap hc0 j0 ((p + q) / 2 + 1 - j0) hj0 hl
  rw [show j0 + ((p + q) / 2 + 1 - j0) = (p + q) / 2 + 1 by omega] at hadd
  have hexc' : excited (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
      c φ j0 ≤ 1 / 2 := by
    refine hexc.trans ?_
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := a'))
    simpa using this
  have hfl : ((p + q) / 2 + 1) / n ≤ 2 * (((p + q) / 2 + 1 - j0) / n) + 1 := by
    have h1 : (p + q) / 2 + 1 - j0 < ((p + q) / 2 + 1 - j0) / n * n + n := Nat.lt_div_mul_add hn0
    have key : (p + q) / 2 + 1 < (2 * (((p + q) / 2 + 1 - j0) / n) + 2) * n := by
      have e : (2 * (((p + q) / 2 + 1 - j0) / n) + 2) * n
          = 2 * (((p + q) / 2 + 1 - j0) / n * n) + 2 * n := by ring
      rw [e]
      generalize ((p + q) / 2 + 1 - j0) / n * n = u at h1 ⊢
      omega
    have := (Nat.div_lt_iff_lt_mul hn0).2 key
    generalize ((p + q) / 2 + 1) / n = s at this ⊢
    generalize ((p + q) / 2 + 1 - j0) / n = s' at this ⊢
    omega
  have hσ : excited (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) c φ
      ((p + q) / 2 + 1) ≤ (1 / 2) ^ (((p + q) / 2 + 1) / n) :=
    calc _ ≤ (1 / 2) ^ (2 * (((p + q) / 2 + 1 - j0) / n))
          * excited (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
            c φ j0 := hadd
      _ ≤ (1 / 2) ^ (2 * (((p + q) / 2 + 1 - j0) / n)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hexc' (by positivity)
      _ = (1 / 2) ^ (2 * (((p + q) / 2 + 1 - j0) / n) + 1) := by rw [pow_succ]
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hfl
  exact connTorus_uniform (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    hφm hφb hφ1 heig hc hgap hc0 ham hbm hab hbb p q hev hσ

end Wilson

/-! ## 4. The trace identity with insertions -/

section Insertion

open MassGap.RectWilson MassGap.RectTransfer MassGap.CompactGauge

variable {N : ℕ} {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- A `Fin`-indexed sequence extended to `ℕ` reads its entries: `extX V i = V i` for `i ≤ m`.

DERIVED: `1` is the length offset of `Fin (m + 1)`. -/
theorem extX_apply {X : Type} [MeasurableSpace X] {m : ℕ} (V : Fin (m + 1) → X) {i : ℕ}
    (hi : i < m + 1) : HiddenChain.extX V i = V ⟨i, hi⟩ := by
  simp only [HiddenChain.extX]
  rw [dif_pos hi]

/-- **The closed slice chain with two slices inserted, at any separation**: for bounded measurable
`a`, `b` of the spatial links of one slice,
`ZcR (a(V 0) b(V (p+1))) = ∫∫ a(x) kT^{∗(p+1)}(x,y) b(y) kT^{∗(q+1)}(y,x) = trPair (Haar) kT a b p q`
on the chain of `p + q + 2` steps. The proof is that of `RectTorusState.Zc_pairR` (the case `p = q`
with one continuous insertion), with the two halves of the chain of different lengths:
`HiddenChain.chain_split` at `p + 1`, `HiddenChain.chain_end_kern` on the second part and
`HiddenChain.chain_end_iter` on the first.

DERIVED: `0` is the first slice; `1` the offset of `iter` and the second slice `p + 1`. -/
theorem Zc_trPair (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (p q : ℕ)
    {a b : (SpT μ T → SUN.SU N) → ℝ} (hbm : Measurable b) {A B : ℝ}
    (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) :
    RectTorusState.ZcR μ T N β (p + 1 + q) (fun V _ => a (V 0) * b (V (p + 1)))
      = trPair (hS μ T N) (kT μ T N β) a b p q := by
  unfold RectTorusState.ZcR trPair
  congr 1; funext x
  have step1 : HiddenChain.chain (hS μ T N) (hA μ T N) (RectTorusState.wtR μ T N β) (p + 1 + q)
      (fun V _ => a (V 0) * b (V (p + 1)) * kT μ T N β (V (p + 1 + q)) x) x
      = HiddenChain.chain (hS μ T N) (hA μ T N) (RectTorusState.wtR μ T N β) (p + 1 + q)
      (fun V _ => a (V 0) * b (V (p + 1))
        * HiddenChain.kern (hA μ T N) (RectTorusState.wtR μ T N β)
          (HiddenChain.sshift V (p + 1) q) x) x := by
    congr 1; funext V A
    rw [RectTorusState.kern_wtR]
    show _ = a (V 0) * b (V (p + 1)) * kT μ T N β (V (q + (p + 1))) x
    rw [show q + (p + 1) = p + 1 + q by omega]
  have hsplit := HiddenChain.chain_split (μ := hS μ T N) (ν := hA μ T N)
    (w := RectTorusState.wtR μ T N β) (p + 1) q
    (G1 := fun V (_ : ℕ → RectTorusState.AxR μ T N) => a (V 0) * b (V (p + 1)))
    (fun V (_ : ℕ → RectTorusState.AxR μ T N) =>
      HiddenChain.kern (hA μ T N) (RectTorusState.wtR μ T N β) (V q) x) x
    (fun V V' A A' hV _ => by
      show a (V 0) * b (V (p + 1)) = a (V' 0) * b (V' (p + 1))
      rw [hV 0 (Nat.zero_le _), hV (p + 1) le_rfl])
  refine step1.trans (hsplit.trans ?_)
  have hend : ∀ z, HiddenChain.chain (hS μ T N) (hA μ T N) (RectTorusState.wtR μ T N β) q
      (fun V (_ : ℕ → RectTorusState.AxR μ T N) =>
        HiddenChain.kern (hA μ T N) (RectTorusState.wtR μ T N β) (V q) x) z
      = iter (hS μ T N) (kT μ T N β) q z x := by
    intro z; rw [HiddenChain.chain_end_kern x q z, RectTorusState.kern_wtR]
  simp only [hend]
  obtain ⟨Cq, hCq⟩ := ((bdd_kT hN hβ).iter (μ := hS μ T N) q).bdd
  set g' : (SpT μ T → SUN.SU N) → ℝ := fun z => a x * b z * iter (hS μ T N) (kT μ T N β) q z x
    with hg'
  have hg'm : Measurable g' :=
    (measurable_const.mul hbm).mul (((bdd_kT hN hβ).iter (μ := hS μ T N) q).col x)
  have hg'b : ∀ z, |g' z| ≤ A * B * Cq := fun z =>
    HiddenChain.abs_mul_le_of (HiddenChain.abs_mul_le_of (hab x) (hbb z)) (hCq z x)
  have step3 : HiddenChain.chain (hS μ T N) (hA μ T N) (RectTorusState.wtR μ T N β) (p + 1)
      (fun V _ => a (V 0) * b (V (p + 1)) * iter (hS μ T N) (kT μ T N β) q (V (p + 1)) x) x
      = HiddenChain.chain (hS μ T N) (hA μ T N) (RectTorusState.wtR μ T N β) (p + 1)
        (fun V _ => g' (V (p + 1))) x :=
    HiddenChain.chain_congr (p + 1) (fun V A hV => by rw [hg']; dsimp only; rw [hV])
  refine step3.trans ?_
  rw [HiddenChain.chain_end_iter (μ := hS μ T N) (ν := hA μ T N) (RectTorusState.wmeas_wtR β)
    (RectTorusState.abs_wtR_le hN hβ) hg'm hg'b p x, RectTorusState.kern_wtR]
  congr 1; funext z
  rw [hg']
  dsimp only
  ring

/-- **The spatial links of one time slice** of a configuration of the rectangular torus: slice `t`
along `μ`, link `(ν, y)` read at the site `join t y`.

DERIVED: `4` is the spacetime dimension. -/
def spSlice (L : Fin 4 → ℕ) (μ : Fin 4) (t : Fin (L μ)) (U : RLink L → SUN.SU N) :
    SpIdx L μ → SUN.SU N :=
  fun l => U (l.1.1, join L μ t l.2)

/-- `spSlice L μ t` is measurable.

DERIVED: `4` is the spacetime dimension. -/
theorem measurable_spSlice (L : Fin 4 → ℕ) (μ : Fin 4) (t : Fin (L μ)) :
    Measurable (spSlice (N := N) L μ t) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- On a configuration assembled from slices (`RectWilson.Φ` of `RectTorusState.joinR A V`), the
spatial links of slice `t` are `V t` (`RectWilson.Φ_sp`).

DERIVED: no numeral appears in the statement. -/
theorem spSlice_joinR {L : Fin 4 → ℕ} (A : Fin (L μ) → RectTorusState.AxR μ (tr L μ) N)
    (V : Fin (L μ) → RectTorusState.SlR μ (tr L μ) N) (t : Fin (L μ)) :
    spSlice L μ t (Φ L μ (RectTorusState.joinR A V)) = V t := by
  funext l
  exact Φ_sp (RectTorusState.joinR A V) t l.2 l.1

/-- **The Wilson correlation numerator of two slice observables is the trace with insertions**: on
the rectangular torus with time extent `L μ = p + q + 2` along `μ`, for bounded measurable `a`, `b`
of the spatial links of one slice,
`∫ a(U|_0) b(U|_{p+1}) e^{−β S(U)} dU = trPair (Haar) kT a b p q`, the insertion form of
`RectTransfer.ZR_eq_cyc`. It is `RectTorusState.corrNumR` and `Zc_trPair`.

DERIVED: `0` is the first slice; `1` the offset of `iter`, the second slice `p + 1` and the time
extent `p + q + 2`. -/
theorem corrNum_slab (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ} {μ : Fin 4} {p q : ℕ}
    (hL : L μ = p + 1 + q + 1) {a b : (SpIdx L μ → SUN.SU N) → ℝ} (ham : Measurable a)
    (hbm : Measurable b) {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) :
    (sysR L N).corrNum (probHaar (SUN.SU N)) β
        (fun U => a (spSlice L μ ⟨0, by omega⟩ U) * b (spSlice L μ ⟨p + 1, by omega⟩ U))
      = trPair (hS μ (tr L μ) N) (kT μ (tr L μ) N β) a b p q := by
  have hO : Measurable (fun U : RLink L → SUN.SU N =>
      a (spSlice L μ ⟨0, by omega⟩ U) * b (spSlice L μ ⟨p + 1, by omega⟩ U)) :=
    (ham.comp (measurable_spSlice L μ _)).mul (hbm.comp (measurable_spSlice L μ _))
  refine (RectTorusState.corrNumR hN hβ hL hO (BO := A * B)
    (fun U => HiddenChain.abs_mul_le_of (hab _) (hbb _))
    (F := fun V _ => a (V 0) * b (V (p + 1)))
    ((ham.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      (hbm.comp ((measurable_pi_apply (p + 1)).comp measurable_fst)))
    (BF := A * B) (fun V _ => HiddenChain.abs_mul_le_of (hab _) (hbb _)) ?_).trans
    (Zc_trPair hN hβ p q hbm hab hbb)
  · intro A' V
    simp only [spSlice_joinR]
    rw [extX_apply _ (show 0 < p + 1 + q + 1 by omega),
      extX_apply _ (show p + 1 < p + 1 + q + 1 by omega)]
    rfl

section Ones

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- **A trivial second insertion closes the trace**: `Tr(A K^{p+1} K^{q+1}) = Tr(A K^{p+q+2})`
(`iter_add`).

DERIVED: `1` is the offset of `iter`. -/
theorem trPair_one_right {k : X → X → ℝ} (hk : Bdd k) (a : X → ℝ) (p q : ℕ) :
    trPair ν k a (fun _ => 1) p q = trIns ν k a (p + q + 1) := by
  unfold trPair trIns
  congr 1; funext x
  rw [iter_add hk p q]
  simp only [conv]
  rw [← integral_const_mul]
  congr 1; funext y; ring

/-- **A trivial first insertion closes the trace**, by cyclicity: for symmetric `k`,
`Tr(K^{p+1} B K^{q+1}) = Tr(B K^{p+q+2})` (one Fubini swap and `iter_add`).

DERIVED: `1` is the offset of `iter`. -/
theorem trPair_one_left {k : X → X → ℝ} (hk : Bdd k) (hks : ∀ x y, k x y = k y x) {b : X → ℝ}
    (hbm : Measurable b) {B : ℝ} (hbb : ∀ x, |b x| ≤ B) (p q : ℕ) :
    trPair ν k (fun _ => 1) b p q = trIns ν k b (p + q + 1) := by
  have e1 : trPair ν k (fun _ => 1) b p q
      = ∫ x, ∫ y, iter ν k p x y * (b y * iter ν k q x y) ∂ν ∂ν := by
    unfold trPair; congr 1; funext x; congr 1; funext y
    rw [CyclicKernel.iter_symm hk hks q y x]; simp only [one_mul]; ring
  have hB : Bdd (fun x y => iter ν k p x y * (b y * iter ν k q x y)) :=
    FluxSectorBound.bdd_mul (hk.iter (μ := ν) p)
      (FluxSectorBound.bdd_mul (bdd_right hbm hbb) (hk.iter (μ := ν) q))
  obtain ⟨C, hC⟩ := hB.bdd
  rw [e1, swap_bdd hB.meas hC]
  unfold trIns
  congr 1; funext y
  rw [show p + q + 1 = q + p + 1 by ring, iter_add hk q p]
  simp only [conv]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [CyclicKernel.iter_symm hk hks q y x]; ring

end Ones

/-- **The connected trace ratio is the connected Wilson correlation**: on the rectangular torus
with time extent `L 0 = p + q + 2`, for bounded measurable `a`, `b` of the spatial links of one
slice, with `⟨·⟩` the Wilson Gibbs expectation `System.expect` of the torus,

    connTorus (Haar) kT a b p q = ⟨a(U|_0) b(U|_{p+1})⟩ − ⟨a(U|_0)⟩ ⟨b(U|_{p+1})⟩.

Numerators by `corrNum_slab` (with `1` for the absent insertion, `trPair_one_right`,
`trPair_one_left`), the partition function by `OpenAIBridgeCluster.ZR_eq_trPow`.

DERIVED: `0` is the time direction and the first slice; `1` the offset of `iter`, the second slice
`p + 1` and the time extent `p + q + 2`. -/
theorem connTorus_eq_expect (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ} {p q : ℕ}
    (hL : L 0 = p + 1 + q + 1) {a b : (SpIdx L 0 → SUN.SU N) → ℝ} (ham : Measurable a)
    (hbm : Measurable b) {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) :
    connTorus (hS 0 (tr L 0) N) (kT 0 (tr L 0) N β) a b p q
      = (sysR L N).expect (probHaar (SUN.SU N)) β
          (fun U => a (spSlice L 0 ⟨0, by omega⟩ U) * b (spSlice L 0 ⟨p + 1, by omega⟩ U))
        - (sysR L N).expect (probHaar (SUN.SU N)) β (fun U => a (spSlice L 0 ⟨0, by omega⟩ U))
          * (sysR L N).expect (probHaar (SUN.SU N)) β
            (fun U => b (spSlice L 0 ⟨p + 1, by omega⟩ U)) := by
  have hab' := corrNum_slab hN hβ hL ham hbm hab hbb
  have hab1 := corrNum_slab hN hβ hL (b := fun _ => (1 : ℝ)) ham measurable_const hab
    (fun _ => abs_one.le)
  have h1b := corrNum_slab hN hβ hL (a := fun _ => (1 : ℝ)) measurable_const hbm
    (fun _ => abs_one.le) hbb
  simp only [mul_one, one_mul] at hab1 h1b
  have hZ : (sysR L N).partition (probHaar (SUN.SU N)) β
      = trPow (hS 0 (tr L 0) N) (kT 0 (tr L 0) N β) (p + q + 1) :=
    ZR_eq_trPow hN hβ L (p + q + 1) (by omega)
  unfold connTorus LatticeGauge.System.expect
  rw [hab', hab1, h1b, hZ, trPair_one_right (bdd_kT hN hβ) a p q,
    trPair_one_left (bdd_kT hN hβ) (kT_symm β) hbm hbb p q]

end Insertion

/-! ## 5. The connected Wilson correlation, uniform in the torus -/

section Capstone

open MassGap.RectWilson MassGap.RectTransfer MassGap.DoublingRecursion MassGap.DoublingWilson
  MassGap.CompactGauge

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **Exponential clustering of the Wilson torus correlation, uniform in the torus, from the
seed.** If one torus of even side `n ≥ 2` has `16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then
on the cubic `SU(N)` Wilson torus of every even side `L ≥ 2n`, for bounded measurable functions `a`,
`b` of the spatial links of one time slice (`|a| ≤ A`, `|b| ≤ B`), read at slices `0` and `p + 1`
of the time extent `L = p + q + 2`,

    |⟨a_0 b_{p+1}⟩ − ⟨a_0⟩⟨b_{p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋),

`⟨·⟩` the Wilson Gibbs expectation of the torus. The constant `6` and the rate `log 2 / n` do not
depend on `L`, the coupling or the observables. It is `connTorus_even_side_uniform` read through
`connTorus_eq_expect`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of
`connTorus_uniform`; `1/2` the contraction; `2` the doubled side, the least seed side and the least
ratio `L / n`; `0` the time direction, the first slice and the sign of the coupling; `1` the offset
of `iter`, the second slice `p + 1` and the time extent `p + q + 2`; `4` the spacetime dimension. -/
theorem wilson_conn_even_side
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L)
    (a b : (SpIdx (fun _ : Fin 4 => L) 0 → SUN.SU N) → ℝ) (ham : Measurable a)
    (hbm : Measurable b) (A B : ℝ) (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (p q : ℕ)
    (hpq : p + 1 + q + 1 = L) :
    |(sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
        (fun U => a (spSlice (fun _ : Fin 4 => L) 0 ⟨0, by show 0 < L; omega⟩ U)
          * b (spSlice (fun _ : Fin 4 => L) 0 ⟨p + 1, by show p + 1 < L; omega⟩ U))
      - (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
          (fun U => a (spSlice (fun _ : Fin 4 => L) 0 ⟨0, by show 0 < L; omega⟩ U))
        * (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
          (fun U => b (spSlice (fun _ : Fin 4 => L) 0 ⟨p + 1, by show p + 1 < L; omega⟩ U))|
      ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨φ, c, hc0, hφ1, heig, hcl⟩ := connTorus_even_side_uniform hN hβ hn he h0 L hLe hL
  have h := hcl a b ham hbm A B hab hbb p q (by omega)
  rw [connTorus_eq_expect hN hβ (L := fun _ : Fin 4 => L) (p := p) (q := q) hpq.symm ham hbm hab
    hbb] at h
  exact h

end Capstone

end MassGap.OpenAIBridgeUniform

#print axioms MassGap.OpenAIBridgeUniform.sq_iint_mul_le
#print axioms MassGap.OpenAIBridgeUniform.hs_weight_le
#print axioms MassGap.OpenAIBridgeUniform.diag_conv_comm
#print axioms MassGap.OpenAIBridgeUniform.trPair_eq_sym
#print axioms MassGap.OpenAIBridgeUniform.trPair_comm
#print axioms MassGap.OpenAIBridgeUniform.abs_trPair_balanced
#print axioms MassGap.OpenAIBridgeUniform.abs_trPair_le_sum
#print axioms MassGap.OpenAIBridgeUniform.trPair_split
#print axioms MassGap.OpenAIBridgeUniform.hs_conv_mulR
#print axioms MassGap.OpenAIBridgeUniform.trPair_sq_le
#print axioms MassGap.OpenAIBridgeUniform.trPair_pow_le
#print axioms MassGap.OpenAIBridgeUniform.abs_trPair_le
#print axioms MassGap.OpenAIBridgeUniform.connTorus_le_excited
#print axioms MassGap.OpenAIBridgeUniform.connTorus_uniform
#print axioms MassGap.OpenAIBridgeUniform.hs_iter_rem_add_le
#print axioms MassGap.OpenAIBridgeUniform.excited_add_le
#print axioms MassGap.OpenAIBridgeUniform.wilson_gap_excited
#print axioms MassGap.OpenAIBridgeUniform.gap_side_excited
#print axioms MassGap.OpenAIBridgeUniform.wilson_connTorus_uniform
#print axioms MassGap.OpenAIBridgeUniform.connTorus_even_side_uniform
#print axioms MassGap.OpenAIBridgeUniform.extX_apply
#print axioms MassGap.OpenAIBridgeUniform.Zc_trPair
#print axioms MassGap.OpenAIBridgeUniform.measurable_spSlice
#print axioms MassGap.OpenAIBridgeUniform.spSlice_joinR
#print axioms MassGap.OpenAIBridgeUniform.corrNum_slab
#print axioms MassGap.OpenAIBridgeUniform.trPair_one_right
#print axioms MassGap.OpenAIBridgeUniform.trPair_one_left
#print axioms MassGap.OpenAIBridgeUniform.connTorus_eq_expect
#print axioms MassGap.OpenAIBridgeUniform.wilson_conn_even_side
