import Mathlib
import MassGap.OpenAIBridgeUniform
import MassGap.OpenAIBridgeGroups

/-!
# MassGap.OpenAIBridgeSlab — the uniform clustering bound for kernel insertions

`OpenAIBridgeUniform` and `OpenAIBridgeGroups` bound the connected correlation of two functions of
the spatial links of one time slice. An observable that reads a time slab — `w + 1` consecutive
slices and the time links between them — enters the transfer-matrix trace as a kernel `F(x, y)`
from slice `0` to slice `w`, not as a multiplication operator. Bounded by `A` pointwise, its kernel
is at most `A k^{∗w}` in absolute value. This module redoes the trace calculus of
`OpenAIBridgeUniform` §1 for kernel insertions.

## 1. Kernel insertions

* `tp`, `trc` — the transpose and the trace of a kernel; `trc_conv_comm` (cyclicity),
  `sq_trc_conv_le` (Cauchy–Schwarz), `hs_tp`, `hs_eq_trc`;
* `OpBd μ F A` — `F` has operator norm at most `A`, in Hilbert–Schmidt form:
  `hs(F ∗ M) ≤ A² hs(M)` and `hs(M ∗ F) ≤ A² hs(M)` for every bounded `M`; `OpBd.transpose`;
* `opBd_of_le` — a pointwise bound `|F| ≤ A k^{∗(m+1)}` gives `OpBd F (A ‖K‖^{m+1})`;
* `trK μ r F G p q = Tr(F R^{p+1} G R^{q+1})`;
* `abs_trK_le` — Hölder for kernel insertions: if `p + q = 2i`, then
  `|Tr(F R^{p+1} G R^{q+1})| ≤ A B hs(r^{∗(i+1)})`. The Cauchy–Schwarz iteration of
  `OpenAIBridgeUniform.abs_trPair_le`, with the pair `(Gᵀ, G)` in place of `(b, b)`;
* `abs_trc_conv_iter_le` — `|Tr(F R^{2i+2})| ≤ A hs(r^{∗(i+1)})`.

## 2. The connected trace ratio for kernel insertions

* `trOne`, `connK` — `Tr(F K^{m+1})` and the connected ratio on the chain of
  `L = p + q + 2 + w + w'` steps, `F` covering `w` steps and `G` covering `w'`;
* `trK_decomp`, `trOne_decomp`, `trPow_even` — the traces split at the vacuum `φ`;
* `sq_kf_le`, `abs_vac_le` — `‖Fφ‖ ≤ A` and `|⟨φ, Fφ⟩| ≤ A` for `OpBd F A`;
* `conn_alg2` — the real bookkeeping, with the excited weight of the partition function below the
  others;
* `connK_le_excited` — `|connK| ≤ A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋ + 5 σ_{(p+q)/2+1})` for
  `OpBd F (A |c|^w)`, `OpBd G (B |c|^{w'})`, `w`, `w'`, `p + q` even;
* `connK_uniform` — `|connK| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋)` when
  `σ_{(p+q)/2+1} ≤ (1/2)^⌊((p+q)/2+1)/n⌋`; the separations are counted from the slab edges;
* `excited_le_slab`, `connK_slab` — the excited weight from the window of the seed, for slab
  pairs with `4(w + w') + 8n ≤ L`, and the bound for pointwise-bounded kernels `|F| ≤ A k^{∗w}`.

## 3. On the Wilson torus

* `wilson_connK_slab` (`SU(N)`) and `wilson_connK_slabG` (every `GaugeGroup G`) — on the cubic
  torus of every even side `L ≥ 2n`, from the seed, for bounded measurable kernels on the slice
  with `|F| ≤ A kT^{∗w}`, `|G| ≤ B kT^{∗w'}` (`w`, `w'` even and positive) and
  `4(w + w') + 8n ≤ L`: `|connK F G w w' p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋)`.

## 4. The slab kernel and the trace identity on the chain

* `slabKer μ ν w m G` — the kernel of an insertion `G` reading `m + 2` slices and the `m + 1`
  hidden variables between them: the chain `HiddenChain.chain` with its last point pinned;
  `measurable_slabKer`, `abs_slabKer_le`, `bdd_slabKer`, `slabKer_le_iter` (`|slabKer m G| ≤
  B k^{∗(m+1)}` for nonnegative weights), `slabKer_one`, `chain_slab`;
* `chain_two` — the closed chain with two slab insertions is `trK` of their slab kernels;
  `trK_iter_right`, `trK_iter_left` — a trivial insertion closes the trace to `trOne`.

## 5. Slab observables on the Wilson torus

* `slabV`, `slabA` — the slices and the time links of the slab starting at time `t`;
* `corrNum_slabK`, `connK_eq_expect_slab` (`SU(N)`) and `corrNum_slabKG`, `connK_eq_expect_slabG`
  (every `GaugeGroup G`) — `connK` of the slab kernels is `⟨f_0 g_s⟩ − ⟨f_0⟩⟨g_s⟩`, the slab
  form of `OpenAIBridgeUniform.corrNum_slab` and `OpenAIBridgeUniform.connTorus_eq_expect`.

## 6. The capstone

* `wilson_slab_conn` (`SU(N)`) and `wilson_slab_connG` (every `GaugeGroup G`) — from the seed, on
  the cubic torus of every even side `L ≥ 2n`, for bounded measurable functions `f`, `g` of slabs
  of `w + 1`, `w' + 1` slices and their time links (`w`, `w'` even and positive), read at times
  `0` and `w + p + 1` of `L = p + q + 2 + w + w'` with `4(w + w') + 8n ≤ L`:
  `|⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋)`.

## Scope

An odd slab width is made even by reading one more slice. The condition `4(w + w') + 8n ≤ L`
places the excited weight of the wrap-around term at a level the window of
`OpenAIBridgeUniform.gap_side_excited` controls; at fixed widths it holds on every large torus.
-/

namespace MassGap.OpenAIBridgeSlab

open MeasureTheory Real
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeUniform

/-! ## 1. Kernel insertions -/

section Calculus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The transpose of a kernel, `Pᵀ(x, y) = P(y, x)`.

DERIVED: no numeral appears in the statement. -/
def tp (P : X → X → ℝ) : X → X → ℝ := fun x y => P y x

/-- The trace of a kernel, `trc μ M = ∫ M(x, x) dμ(x)`.

DERIVED: no numeral appears in the statement. -/
noncomputable def trc (μ : Measure X) (M : X → X → ℝ) : ℝ := ∫ x, M x x ∂μ

/-- **A kernel insertion of operator norm at most `A`**, in Hilbert–Schmidt form: `F` is bounded and
measurable, `A ≥ 0`, and composing with `F` on either side multiplies every Hilbert–Schmidt norm by
at most `A²`.

DERIVED: `2` is the square of the Hilbert–Schmidt norm; `0` the sign of the bound. -/
structure OpBd (μ : Measure X) (F : X → X → ℝ) (A : ℝ) : Prop where
  bdd : Bdd F
  nonneg : 0 ≤ A
  left : ∀ M : X → X → ℝ, Bdd M → hs μ (conv μ F M) ≤ A ^ 2 * hs μ M
  right : ∀ M : X → X → ℝ, Bdd M → hs μ (conv μ M F) ≤ A ^ 2 * hs μ M

/-- `Tr(F R^{p+1} G R^{q+1})` for kernel insertions `F`, `G`:
`trK μ r F G p q = trc((F ∗ r^{∗(p+1)}) ∗ (G ∗ r^{∗(q+1)}))`.

DERIVED: `1` is the offset of `iter`. -/
noncomputable def trK (μ : Measure X) (r F G : X → X → ℝ) (p q : ℕ) : ℝ :=
  trc μ (conv μ (conv μ F (iter μ r p)) (conv μ G (iter μ r q)))

/-- The transpose of a bounded kernel is bounded.

DERIVED: no numeral appears in the statement. -/
theorem bdd_tp {P : X → X → ℝ} (hP : Bdd P) : Bdd (tp P) := by
  obtain ⟨C, hC⟩ := hP.bdd
  exact ⟨hP.meas.comp measurable_swap, C, fun x y => hC y x⟩

omit [IsProbabilityMeasure μ] in
/-- The transpose of a composition: `(P ∗ Q)ᵀ = Qᵀ ∗ Pᵀ`.

DERIVED: no numeral appears in the statement. -/
theorem tp_conv (P Q : X → X → ℝ) : tp (conv μ P Q) = conv μ (tp Q) (tp P) := by
  funext x z
  simp only [tp, conv]
  congr 1; funext y; ring

/-- A power of a symmetric bounded kernel is its own transpose.

DERIVED: no numeral appears in the statement. -/
theorem tp_iter {r : X → X → ℝ} (hr : Bdd r) (hrs : ∀ x y, r x y = r y x) (p : ℕ) :
    tp (iter μ r p) = iter μ r p := by
  funext x y
  exact CyclicKernel.iter_symm hr hrs p y x

/-- Transposing keeps the Hilbert–Schmidt norm: `hs(Pᵀ) = hs(P)`, one Fubini swap.

DERIVED: `2` is the square of the Hilbert–Schmidt norm. -/
theorem hs_tp {P : X → X → ℝ} (hP : Bdd P) : hs μ (tp P) = hs μ P := by
  obtain ⟨C, hC⟩ := hP.bdd
  have hm : Measurable (Function.uncurry (fun x y => P y x ^ 2)) :=
    (hP.meas.comp measurable_swap).pow_const 2
  simp only [hs, tp]
  exact swap_bdd hm (C := C ^ 2) (fun x y => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC y x) 2)

/-- **The trace is cyclic**: `trc(P ∗ Q) = trc(Q ∗ P)` (`OpenAIBridgeUniform.diag_conv_comm`).

DERIVED: no numeral appears in the statement. -/
theorem trc_conv_comm {P Q : X → X → ℝ} (hP : Bdd P) (hQ : Bdd Q) :
    trc μ (conv μ P Q) = trc μ (conv μ Q P) :=
  diag_conv_comm hP hQ

/-- **Cauchy–Schwarz for the trace**: `trc(P ∗ Q)² ≤ hs(P) hs(Q)`. It is
`OpenAIBridgeUniform.sq_iint_mul_le` on `P` and `Qᵀ`, with `hs_tp`.

DERIVED: `2` is the square. -/
theorem sq_trc_conv_le {P Q : X → X → ℝ} (hP : Bdd P) (hQ : Bdd Q) :
    trc μ (conv μ P Q) ^ 2 ≤ hs μ P * hs μ Q := by
  have h := sq_iint_mul_le (μ := μ) hP (bdd_tp hQ)
  rw [hs_tp hQ] at h
  exact h

omit [IsProbabilityMeasure μ] in
/-- The Hilbert–Schmidt norm is a trace: `hs(Y) = trc(Y ∗ Yᵀ)`.

DERIVED: `2` is the square of the Hilbert–Schmidt norm. -/
theorem hs_eq_trc (Y : X → X → ℝ) : hs μ Y = trc μ (conv μ Y (tp Y)) := by
  simp only [hs, trc, conv, tp, sq]

/-- `OpBd` is closed under transposition: `(F ∗ M)` for `Fᵀ` is the transpose of `Mᵀ ∗ F`.

DERIVED: no numeral appears in the statement. -/
theorem OpBd.transpose {F : X → X → ℝ} {A : ℝ} (hF : OpBd μ F A) : OpBd μ (tp F) A := by
  refine ⟨bdd_tp hF.bdd, hF.nonneg, fun M hM => ?_, fun M hM => ?_⟩
  · have e : conv μ (MassGap.OpenAIBridgeSlab.tp F) M
        = MassGap.OpenAIBridgeSlab.tp (conv μ (MassGap.OpenAIBridgeSlab.tp M) F) := by
      rw [tp_conv]; rfl
    calc hs μ (conv μ (MassGap.OpenAIBridgeSlab.tp F) M)
        = hs μ (conv μ (MassGap.OpenAIBridgeSlab.tp M) F) := by
          rw [e, hs_tp ((bdd_tp hM).conv (μ := μ) hF.bdd)]
      _ ≤ A ^ 2 * hs μ (MassGap.OpenAIBridgeSlab.tp M) := hF.right _ (bdd_tp hM)
      _ = A ^ 2 * hs μ M := by rw [hs_tp hM]
  · have e : conv μ M (MassGap.OpenAIBridgeSlab.tp F)
        = MassGap.OpenAIBridgeSlab.tp (conv μ F (MassGap.OpenAIBridgeSlab.tp M)) := by
      rw [tp_conv]; rfl
    calc hs μ (conv μ M (MassGap.OpenAIBridgeSlab.tp F))
        = hs μ (conv μ F (MassGap.OpenAIBridgeSlab.tp M)) := by
          rw [e, hs_tp (hF.bdd.conv (μ := μ) (bdd_tp hM))]
      _ ≤ A ^ 2 * hs μ (MassGap.OpenAIBridgeSlab.tp M) := hF.left _ (bdd_tp hM)
      _ = A ^ 2 * hs μ M := by rw [hs_tp hM]

omit [IsProbabilityMeasure μ] in
/-- A scalar multiple scales the Hilbert–Schmidt norm by its square.

DERIVED: `2` is the square. -/
theorem hs_const_mul (a : ℝ) (Q : X → X → ℝ) :
    hs μ (fun x z => a * Q x z) = a ^ 2 * hs μ Q := by
  simp only [hs, mul_pow, integral_const_mul]

/-- The absolute value of a bounded kernel is bounded, with the same Hilbert–Schmidt norm.

DERIVED: no numeral appears in the statement. -/
theorem bdd_abs {M : X → X → ℝ} (hM : Bdd M) : Bdd (fun x y => |M x y|) := by
  obtain ⟨C, hC⟩ := hM.bdd
  exact ⟨hM.meas.abs, C, fun x y => by rw [abs_abs]; exact hC x y⟩

omit [IsProbabilityMeasure μ] in
/-- `hs(|M|) = hs(M)`.

DERIVED: no numeral appears in the statement. -/
theorem hs_abs (M : X → X → ℝ) : hs μ (fun x y => |M x y|) = hs μ M := by
  simp only [hs, sq_abs]

/-- **A pointwise bound passes to the Hilbert–Schmidt norm**: `|P| ≤ Q` gives `hs(P) ≤ hs(Q)`.

DERIVED: `2` is the square of the Hilbert–Schmidt norm. -/
theorem hs_le_of_abs_le {P Q : X → X → ℝ} (hP : Bdd P) (hQ : Bdd Q)
    (h : ∀ x y, |P x y| ≤ Q x y) : hs μ P ≤ hs μ Q := by
  obtain ⟨CP, hCP⟩ := hP.bdd
  obtain ⟨CQ, hCQ⟩ := hQ.bdd
  have bP : ∀ x z, |P x z ^ 2| ≤ CP ^ 2 := fun x z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCP x z) 2
  have bQ : ∀ x z, |Q x z ^ 2| ≤ CQ ^ 2 := fun x z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCQ x z) 2
  unfold hs
  refine integral_mono
    (integrable_of_bdd (measurable_integral_right (hP.meas.pow_const 2)) (C := CP ^ 2)
      (fun x => abs_integral_le fun z => bP x z))
    (integrable_of_bdd (measurable_integral_right (hQ.meas.pow_const 2)) (C := CQ ^ 2)
      (fun x => abs_integral_le fun z => bQ x z)) (fun x => ?_)
  refine integral_mono (integrable_of_bdd ((hP.row x).pow_const 2) (bP x))
    (integrable_of_bdd ((hQ.row x).pow_const 2) (bQ x)) (fun z => ?_)
  show P x z ^ 2 ≤ Q x z ^ 2
  rw [← sq_abs (P x z)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h x z) 2

/-- **A pointwise kernel bound on the left factor of a composition**: `|F| ≤ A P` gives
`|F ∗ M| ≤ A (P ∗ |M|)`.

DERIVED: no numeral appears in the statement. -/
theorem abs_conv_le_left {F M P : X → X → ℝ} (hF : Bdd F) (hM : Bdd M) (hP : Bdd P) {A : ℝ}
    (h : ∀ x y, |F x y| ≤ A * P x y) (x z : X) :
    |conv μ F M x z| ≤ A * conv μ P (fun x y => |M x y|) x z := by
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CM, hCM⟩ := hM.bdd
  obtain ⟨CP, hCP⟩ := hP.bdd
  unfold conv
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono ?_ ?_ (fun y => ?_))
  · exact (integrable_of_bdd ((hF.row x).mul (hM.col z)) (C := CF * CM)
      (fun y => HiddenChain.abs_mul_le_of (hCF x y) (hCM y z))).abs
  · refine integrable_of_bdd (measurable_const.mul ((hP.row x).mul (hM.col z).abs))
      (C := |A| * (CP * CM)) (fun y => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (HiddenChain.abs_mul_le_of (hCP x y)
      (by rw [abs_abs]; exact hCM y z)) (abs_nonneg _)
  · show |F x y * M y z| ≤ A * (P x y * |M y z|)
    rw [abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h x y) (abs_nonneg _)

/-- **A pointwise kernel bound on the right factor of a composition**: `|F| ≤ A P` gives
`|M ∗ F| ≤ A (|M| ∗ P)`.

DERIVED: no numeral appears in the statement. -/
theorem abs_conv_le_right {F M P : X → X → ℝ} (hF : Bdd F) (hM : Bdd M) (hP : Bdd P) {A : ℝ}
    (h : ∀ x y, |F x y| ≤ A * P x y) (x z : X) :
    |conv μ M F x z| ≤ A * conv μ (fun x y => |M x y|) P x z := by
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CM, hCM⟩ := hM.bdd
  obtain ⟨CP, hCP⟩ := hP.bdd
  unfold conv
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono ?_ ?_ (fun y => ?_))
  · exact (integrable_of_bdd ((hM.row x).mul (hF.col z)) (C := CM * CF)
      (fun y => HiddenChain.abs_mul_le_of (hCM x y) (hCF y z))).abs
  · refine integrable_of_bdd (measurable_const.mul ((hM.row x).abs.mul (hP.col z)))
      (C := |A| * (CM * CP)) (fun y => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (HiddenChain.abs_mul_le_of
      (by rw [abs_abs]; exact hCM x y) (hCP y z)) (abs_nonneg _)
  · show |M x y * F y z| ≤ A * (|M x y| * P y z)
    rw [abs_mul]
    calc |M x y| * |F y z| ≤ |M x y| * (A * P y z) :=
          mul_le_mul_of_nonneg_left (h y z) (abs_nonneg _)
      _ = A * (|M x y| * P y z) := by ring

section Norm

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)

include hkm hC0 hkb in
/-- `hs(k^{∗(m+1)} ∗ N) ≤ ‖K‖^{2(m+1)} hs(N)`, by `KernelPower.hs_conv_le_norm` `m + 1` times.

DERIVED: `2` is the square of the norm; `1` the offset of `iter`. -/
theorem hs_iter_conv_le {N : X → X → ℝ} (hN : Bdd N) : ∀ m : ℕ,
    hs μ (conv μ (iter μ k m) N) ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * (m + 1)) * hs μ N
  | 0 => le_of_le_of_eq (hs_conv_le_norm hkm hC0 hkb hN) (by norm_num)
  | m + 1 => by
    have hk : Bdd k := ⟨hkm, C, hkb⟩
    change hs μ (conv μ (conv μ k (iter μ k m)) N) ≤ _
    rw [← conv_assoc hk (hk.iter (μ := μ) m) hN]
    calc hs μ (conv μ k (conv μ (iter μ k m) N))
        ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 * hs μ (conv μ (iter μ k m) N) :=
          hs_conv_le_norm hkm hC0 hkb ((hk.iter (μ := μ) m).conv (μ := μ) hN)
      _ ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2
          * (‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * (m + 1)) * hs μ N) :=
          mul_le_mul_of_nonneg_left (hs_iter_conv_le hN m) (by positivity)
      _ = _ := by ring

include hkm hC0 hkb hsym in
/-- `hs(N ∗ k^{∗(m+1)}) ≤ ‖K‖^{2(m+1)} hs(N)` for symmetric `k`: transpose and `hs_iter_conv_le`.

DERIVED: `2` is the square of the norm; `1` the offset of `iter`. -/
theorem hs_conv_iter_le {N : X → X → ℝ} (hN : Bdd N) (m : ℕ) :
    hs μ (conv μ N (iter μ k m)) ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * (m + 1)) * hs μ N := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  rw [← hs_tp (hN.conv (μ := μ) (hk.iter m)), tp_conv, tp_iter hk hsym, ← hs_tp hN]
  exact hs_iter_conv_le hkm hC0 hkb (bdd_tp hN) m

include hkm hC0 hkb hsym in
/-- **A kernel bounded by a power of `k` has operator norm at most that power**: if `F` is bounded
measurable with `|F(x, y)| ≤ A k^{∗(m+1)}(x, y)`, `A ≥ 0`, then `OpBd F (A ‖K‖^{m+1})`. By
`abs_conv_le_left`, `abs_conv_le_right` and `hs_iter_conv_le`, `hs_conv_iter_le`.

DERIVED: `1` is the offset of `iter`; `0` the sign of `A`. -/
theorem opBd_of_le {F : X → X → ℝ} (hF : Bdd F) {A : ℝ} (hA : 0 ≤ A) (m : ℕ)
    (h : ∀ x y, |F x y| ≤ A * iter μ k m x y) :
    OpBd μ F (A * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (m + 1)) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hkm' := hk.iter (μ := μ) m
  refine ⟨hF, mul_nonneg hA (by positivity), fun M hM => ?_, fun M hM => ?_⟩
  · have hQ : Bdd (conv μ (iter μ k m) (fun x y => |M x y|)) := hkm'.conv (bdd_abs hM)
    calc hs μ (conv μ F M)
        ≤ hs μ (fun x z => A * conv μ (iter μ k m) (fun x y => |M x y|) x z) :=
          hs_le_of_abs_le (hF.conv (μ := μ) hM) (FluxSectorBound.bdd_mul (bdd_const A) hQ)
            (fun x z => abs_conv_le_left hF hM hkm' h x z)
      _ = A ^ 2 * hs μ (conv μ (iter μ k m) (fun x y => |M x y|)) := hs_const_mul _ _
      _ ≤ A ^ 2 * (‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * (m + 1))
            * hs μ (fun x y => |M x y|)) :=
          mul_le_mul_of_nonneg_left (hs_iter_conv_le hkm hC0 hkb (bdd_abs hM) m) (sq_nonneg _)
      _ = _ := by rw [hs_abs]; ring
  · have hQ : Bdd (conv μ (fun x y => |M x y|) (iter μ k m)) := (bdd_abs hM).conv hkm'
    calc hs μ (conv μ M F)
        ≤ hs μ (fun x z => A * conv μ (fun x y => |M x y|) (iter μ k m) x z) :=
          hs_le_of_abs_le (hM.conv (μ := μ) hF) (FluxSectorBound.bdd_mul (bdd_const A) hQ)
            (fun x z => abs_conv_le_right hF hM hkm' h x z)
      _ = A ^ 2 * hs μ (conv μ (fun x y => |M x y|) (iter μ k m)) := hs_const_mul _ _
      _ ≤ A ^ 2 * (‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (2 * (m + 1))
            * hs μ (fun x y => |M x y|)) :=
          mul_le_mul_of_nonneg_left (hs_conv_iter_le hkm hC0 hkb hsym (bdd_abs hM) m)
            (sq_nonneg _)
      _ = _ := by rw [hs_abs]; ring

end Norm

variable {r : X → X → ℝ} (hr : Bdd r) (hrs : ∀ x y, r x y = r y x)

include hr in
/-- **Cyclicity of the two-insertion trace**: `Tr(F R^{p+1} G R^{q+1}) = Tr(G R^{q+1} F R^{p+1})`.

DERIVED: no numeral appears in the statement. -/
theorem trK_comm {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) (p q : ℕ) :
    trK μ r F G p q = trK μ r G F q p := by
  unfold trK
  exact trc_conv_comm (hF.conv (μ := μ) (hr.iter (μ := μ) p)) (hG.conv (μ := μ) (hr.iter (μ := μ) q))

include hr in
/-- **The crude bound**: if `hs(r^{∗(p+1)}) ≤ W` and `hs(r^{∗(q+1)}) ≤ W`, then
`|Tr(F R^{p+1} G R^{q+1})| ≤ A B W`, by `sq_trc_conv_le` and `OpBd`.

DERIVED: no numeral appears in the statement. -/
theorem abs_trK_le_sum {F G : X → X → ℝ} {A B : ℝ} (hF : OpBd μ F A) (hG : OpBd μ G B) {W : ℝ}
    {p q : ℕ} (hp : hs μ (iter μ r p) ≤ W) (hq : hs μ (iter μ r q) ≤ W) :
    |trK μ r F G p q| ≤ A * B * W := by
  have hRp := hr.iter (μ := μ) p
  have hRq := hr.iter (μ := μ) q
  have hW0 : 0 ≤ W := (hs_nonneg _).trans hp
  have hsq := sq_trc_conv_le (μ := μ) (hF.bdd.conv (μ := μ) hRp) (hG.bdd.conv (μ := μ) hRq)
  have h1 := hF.left _ hRp
  have h2 := hG.left _ hRq
  have key : trK μ r F G p q ^ 2 ≤ (A * B * W) ^ 2 := by
    calc trK μ r F G p q ^ 2
        ≤ hs μ (conv μ F (iter μ r p)) * hs μ (conv μ G (iter μ r q)) := hsq
      _ ≤ (A ^ 2 * hs μ (iter μ r p)) * (B ^ 2 * hs μ (iter μ r q)) :=
          mul_le_mul h1 h2 (hs_nonneg _) (mul_nonneg (sq_nonneg _) (hs_nonneg _))
      _ ≤ (A ^ 2 * W) * (B ^ 2 * W) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp (sq_nonneg A))
            (mul_le_mul_of_nonneg_left hq (sq_nonneg B)) (mul_nonneg (sq_nonneg _) (hs_nonneg _))
            (mul_nonneg (sq_nonneg _) hW0)
      _ = (A * B * W) ^ 2 := by ring
  rw [← sq_abs] at key
  exact (pow_le_pow_iff_left₀ (abs_nonneg _)
    (mul_nonneg (mul_nonneg hF.nonneg hG.nonneg) hW0) two_ne_zero).mp key

include hr hrs in
/-- **The Hilbert–Schmidt norm of `R^{p+1} G R^{d+1}` is a two-insertion trace**:
`hs(r^{∗(p+1)} ∗ (G ∗ r^{∗(d+1)})) = Tr(Gᵀ R^{2p+2} G R^{2d+2})`. `hs(Y) = Tr(Y Yᵀ)` (`hs_eq_trc`),
`Yᵀ = R^{d+1} Gᵀ R^{p+1}` (`tp_conv`, `tp_iter`), then cyclicity and associativity.

DERIVED: `1` is the offset of `iter`; `2` the square of the Hilbert–Schmidt norm. -/
theorem hs_conv_tp {G : X → X → ℝ} (hG : Bdd G) (p d : ℕ) :
    hs μ (conv μ (iter μ r p) (conv μ G (iter μ r d)))
      = trK μ r (tp G) G (p + p + 1) (d + d + 1) := by
  have hRp := hr.iter (μ := μ) p
  have hRd := hr.iter (μ := μ) d
  have hGt := bdd_tp hG
  have hGRd : Bdd (conv μ G (iter μ r d)) := hG.conv hRd
  have hY : Bdd (conv μ (iter μ r p) (conv μ G (iter μ r d))) := hRp.conv hGRd
  have hRdGt : Bdd (conv μ (iter μ r d) (tp G)) := hRd.conv hGt
  have hZ : Bdd (conv μ (conv μ (iter μ r d) (tp G)) (iter μ r p)) := hRdGt.conv hRp
  have hRRGRd : Bdd (conv μ (iter μ r p) (conv μ (iter μ r p) (conv μ G (iter μ r d)))) :=
    hRp.conv hY
  have hGtV : Bdd (conv μ (tp G)
      (conv μ (iter μ r p) (conv μ (iter μ r p) (conv μ G (iter μ r d))))) := hGt.conv hRRGRd
  have hR2p := hr.iter (μ := μ) (p + p + 1)
  have hGtR2p : Bdd (conv μ (tp G) (iter μ r (p + p + 1))) := hGt.conv hR2p
  unfold trK
  rw [hs_eq_trc, tp_conv, tp_conv, tp_iter hr hrs p, tp_iter hr hrs d,
    trc_conv_comm hY hZ,
    ← conv_assoc hRdGt hRp hY,
    ← conv_assoc hRd hGt hRRGRd,
    trc_conv_comm hRd hGtV,
    conv_assoc hRp hRp hGRd, ← iter_add hr p p,
    conv_assoc hGt hR2p hGRd,
    ← conv_assoc hGtR2p hGRd hRd,
    ← conv_assoc hG hRd hRd, ← iter_add hr d d]

include hr hrs in
/-- **One Cauchy–Schwarz step on the wrap-around trace**: with `h = p + d + 1`,
`Tr(F R^{p+1} G R^{2h−p−1})² ≤ A² hs(r^{∗(h+1)}) · Tr(Gᵀ R^{2p+2} G R^{2d+2})`. The new pair of
powers again sums to `2h + 2`, with `Gᵀ` and `G`. `R^{q+1} = R^{d+1} R^{h+1}` (`iter_add`),
cyclicity and associativity give `Tr((R^{h+1} F)(R^{p+1} G R^{d+1}))`; then `sq_trc_conv_le`,
`OpBd.right` and `hs_conv_tp`.

DERIVED: `1` is the offset of `iter`; `2` the square. -/
theorem trK_sq_le {F G : X → X → ℝ} {A B : ℝ} (hF : OpBd μ F A) (hG : OpBd μ G B) (p d : ℕ) :
    trK μ r F G p (d + (p + d + 1) + 1) ^ 2
      ≤ A ^ 2 * hs μ (iter μ r (p + d + 1)) * trK μ r (tp G) G (p + p + 1) (d + d + 1) := by
  have hRp := hr.iter (μ := μ) p
  have hRd := hr.iter (μ := μ) d
  have hRh := hr.iter (μ := μ) (p + d + 1)
  have hFb := hF.bdd
  have hGb := hG.bdd
  have hFRp : Bdd (conv μ F (iter μ r p)) := hFb.conv hRp
  have hGRd : Bdd (conv μ G (iter μ r d)) := hGb.conv hRd
  have hRhF : Bdd (conv μ (iter μ r (p + d + 1)) F) := hRh.conv hFb
  have hPQ : Bdd (conv μ (conv μ F (iter μ r p)) (conv μ G (iter μ r d))) := hFRp.conv hGRd
  have hY : Bdd (conv μ (iter μ r p) (conv μ G (iter μ r d))) := hRp.conv hGRd
  have eT : trK μ r F G p (d + (p + d + 1) + 1)
      = trc μ (conv μ (conv μ (iter μ r (p + d + 1)) F)
          (conv μ (iter μ r p) (conv μ G (iter μ r d)))) := by
    unfold trK
    rw [iter_add hr d (p + d + 1), conv_assoc hGb hRd hRh, conv_assoc hFRp hGRd hRh,
      trc_conv_comm hPQ hRh, conv_assoc hRh hFRp hGRd, conv_assoc hRh hFb hRp,
      ← conv_assoc hRhF hRp hGRd]
  rw [eT, ← hs_conv_tp hr hrs hGb p d]
  calc _ ≤ hs μ (conv μ (iter μ r (p + d + 1)) F)
        * hs μ (conv μ (iter μ r p) (conv μ G (iter μ r d))) := sq_trc_conv_le hRhF hY
    _ ≤ _ := mul_le_mul_of_nonneg_right (hF.right _ hRh) (hs_nonneg _)

include hr hrs in
/-- **The iterated Cauchy–Schwarz bound for kernel insertions**: for every pair `p + q = 2i` and
every `j`, `|Tr(F R^{p+1} G R^{q+1})|^{2^j} ≤ (AB)^{2^j} hs(r^{∗(i+1)})^{2^j − 1} W`, with
`W = Σ_{m ≤ 2i} hs(r^{∗(m+1)})`. At `j = 0` it is `abs_trK_le_sum`; a step squares, applies
`trK_sq_le` (or the crude bound at `p = q`, or `trK_comm` when `p > q`) and uses the statement at
`j` on the new pair `(Gᵀ, G)` (`OpBd.transpose`).

DERIVED: `2` is the dyadic base of the iteration and the square; `1` the offset of `iter` and the
range bound. -/
theorem trK_pow_le (i j : ℕ) :
    ∀ {F G : X → X → ℝ} {A B : ℝ}, OpBd μ F A → OpBd μ G B → ∀ p q : ℕ, p + q = i + i →
      |trK μ r F G p q| ^ (2 ^ j)
        ≤ (A * B) ^ (2 ^ j) * hs μ (iter μ r i) ^ (2 ^ j - 1)
          * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) := by
  induction j with
  | zero =>
    intro F G A B hF hG p q hpq
    simp only [pow_zero, pow_one, Nat.sub_self, mul_one]
    exact abs_trK_le_sum hr hF hG
      (Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega)))
      (Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega)))
  | succ j ih =>
    obtain ⟨K, hK⟩ : ∃ K, 2 ^ j = K + 1 :=
      ⟨2 ^ j - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
    have eA : 2 ^ (j + 1) - 1 = 2 * K + 1 := by rw [e2, hK]; omega
    have eB : 2 ^ (j + 1) = 2 * K + 2 := by rw [e2, hK]; ring
    have ih' : ∀ {G : X → X → ℝ} {B : ℝ}, OpBd μ G B → ∀ p q : ℕ, p + q = i + i →
        |trK μ r (tp G) G p q| ^ (K + 1)
          ≤ (B * B) ^ (K + 1) * hs μ (iter μ r i) ^ K
            * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) := by
      intro G B hG p q hpq
      have h := ih hG.transpose hG p q hpq
      rwa [show 2 ^ j - 1 = K by rw [hK]; omega, hK] at h
    have key : ∀ {F G : X → X → ℝ} {A B : ℝ}, OpBd μ F A → OpBd μ G B → ∀ p q : ℕ,
        p + q = i + i → p ≤ q →
        |trK μ r F G p q| ^ (2 * K + 2)
          ≤ (A * B) ^ (2 * K + 2) * hs μ (iter μ r i) ^ (2 * K + 1)
            * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) := by
      intro F G A B hF hG p q hpq hle
      have hA0 := hF.nonneg
      have hB0 := hG.nonneg
      have hτ0 : 0 ≤ hs μ (iter μ r i) := hs_nonneg _
      have hτW : hs μ (iter μ r i) ≤ ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) :=
        Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega))
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq]
        have hpi : p = i := by omega
        have hT : |trK μ r F G p p| ≤ A * B * hs μ (iter μ r i) := by
          rw [hpi]; exact abs_trK_le_sum hr hF hG le_rfl le_rfl
        calc |trK μ r F G p p| ^ (2 * K + 2) ≤ (A * B * hs μ (iter μ r i)) ^ (2 * K + 2) :=
              pow_le_pow_left₀ (abs_nonneg _) hT _
          _ = (A * B) ^ (2 * K + 2) * hs μ (iter μ r i) ^ (2 * K + 1) * hs μ (iter μ r i) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hτW
              (mul_nonneg (pow_nonneg (mul_nonneg hA0 hB0) _) (pow_nonneg hτ0 _))
      · obtain ⟨d, rfl⟩ : ∃ d, q = d + (p + d + 1) + 1 := ⟨(q - p - 2) / 2, by omega⟩
        have hi : p + d + 1 = i := by omega
        subst hi
        have hstep := trK_sq_le hr hrs hF hG p d
        have hT'0 : 0 ≤ trK μ r (tp G) G (p + p + 1) (d + d + 1) := by
          rw [← hs_conv_tp hr hrs hG.bdd p d]; exact hs_nonneg _
        have hT' := ih' hG (p + p + 1) (d + d + 1) (by omega)
        rw [abs_of_nonneg hT'0] at hT'
        calc |trK μ r F G p (d + (p + d + 1) + 1)| ^ (2 * K + 2)
            = (trK μ r F G p (d + (p + d + 1) + 1) ^ 2) ^ (K + 1) := by
              rw [← sq_abs]; ring
          _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hstep _
          _ = (A ^ 2) ^ (K + 1) * hs μ (iter μ r (p + d + 1)) ^ (K + 1)
                * trK μ r (tp G) G (p + p + 1) (d + d + 1) ^ (K + 1) := by ring
          _ ≤ (A ^ 2) ^ (K + 1) * hs μ (iter μ r (p + d + 1)) ^ (K + 1) * _ :=
              mul_le_mul_of_nonneg_left hT'
                (mul_nonneg (pow_nonneg (sq_nonneg A) _) (pow_nonneg hτ0 _))
          _ = _ := by ring
    intro F G A B hF hG p q hpq
    rw [eA, eB]
    rcases le_total p q with h | h
    · exact key hF hG p q hpq h
    · rw [trK_comm hr hF.bdd hG.bdd p q, mul_comm A B]
      exact key hG hF q p (by omega) h

include hr hrs in
/-- **Hölder for the two-insertion trace with kernel insertions**: if `p + q = 2i`, then
`|Tr(F R^{p+1} G R^{q+1})| ≤ A B hs(r^{∗(i+1)})` for `OpBd F A`, `OpBd G B` and a symmetric
bounded kernel `r`. From `trK_pow_le`, as `OpenAIBridgeUniform.abs_trPair_le` from
`OpenAIBridgeUniform.trPair_pow_le`.

DERIVED: `2` is the dyadic base of the iteration and the square; `1` the offset of `iter`, the
first step and the range bound; `0` the vanishing case. -/
theorem abs_trK_le {F G : X → X → ℝ} {A B : ℝ} (hF : OpBd μ F A) (hG : OpBd μ G B)
    (p q i : ℕ) (hpq : p + q = i + i) :
    |trK μ r F G p q| ≤ A * B * hs μ (iter μ r i) := by
  have hA0 := hF.nonneg
  have hB0 := hG.nonneg
  have hτ0 : 0 ≤ hs μ (iter μ r i) := hs_nonneg _
  have hτW : hs μ (iter μ r i) ≤ ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) :=
    Finset.single_le_sum (fun m _ => hs_nonneg _) (Finset.mem_range.mpr (by omega))
  rcases hτ0.lt_or_eq with hτ | hτ
  · have hτne := hτ.ne'
    refine SecondEigenvalue.le_of_pow_two_pow_le (abs_nonneg _)
      (mul_nonneg (mul_nonneg hA0 hB0) hτ0) (div_pos (hτ.trans_le hτW) hτ) (fun j => ?_)
    have h := trK_pow_le hr hrs i j hF hG p q hpq
    obtain ⟨K, hK⟩ : ∃ K, 2 ^ j = K + 1 :=
      ⟨2 ^ j - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    rw [show 2 ^ j - 1 = K by rw [hK]; omega, hK] at h
    rw [hK]
    calc _ ≤ _ := h
      _ = (A * B) ^ (K + 1) * hs μ (iter μ r i) ^ K
          * ((∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m)) / hs μ (iter μ r i)
            * hs μ (iter μ r i)) := by rw [div_mul_cancel₀ _ hτne]
      _ = _ := by ring
  · have h := trK_pow_le hr hrs i 1 hF hG p q hpq
    have e0 : (A * B) ^ 2 ^ 1 * hs μ (iter μ r i) ^ (2 ^ 1 - 1)
        * ∑ m ∈ Finset.range (i + i + 1), hs μ (iter μ r m) = 0 := by
      rw [← hτ]; norm_num
    rw [e0] at h
    have h3 : |trK μ r F G p q| ^ 2 = 0 := le_antisymm (by simpa using h) (sq_nonneg _)
    rw [(pow_eq_zero_iff two_ne_zero).mp h3, ← hτ]
    simp


include hr in
/-- **The one-insertion trace at an even power**: `|Tr(F R^{2i+2})| ≤ A hs(r^{∗(i+1)})` for
`OpBd F A`. `R^{2i+2} = R^{i+1} R^{i+1}` (`iter_add`), then `sq_trc_conv_le` and `OpBd.left`.

DERIVED: `1` is the offset of `iter`; `2` the square. -/
theorem abs_trc_conv_iter_le {F : X → X → ℝ} {A : ℝ} (hF : OpBd μ F A) (i : ℕ) :
    |trc μ (conv μ F (iter μ r (i + i + 1)))| ≤ A * hs μ (iter μ r i) := by
  have hRi := hr.iter (μ := μ) i
  rw [iter_add hr i i, conv_assoc hF.bdd hRi hRi]
  have hsq := sq_trc_conv_le (μ := μ) (hF.bdd.conv (μ := μ) hRi) hRi
  have h1 := hF.left _ hRi
  have key : trc μ (conv μ (conv μ F (iter μ r i)) (iter μ r i)) ^ 2
      ≤ (A * hs μ (iter μ r i)) ^ 2 := by
    calc _ ≤ hs μ (conv μ F (iter μ r i)) * hs μ (iter μ r i) := hsq
      _ ≤ (A ^ 2 * hs μ (iter μ r i)) * hs μ (iter μ r i) :=
          mul_le_mul_of_nonneg_right h1 (hs_nonneg _)
      _ = (A * hs μ (iter μ r i)) ^ 2 := by ring
  rw [← sq_abs] at key
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg hF.nonneg (hs_nonneg _))
    two_ne_zero).mp key

end Calculus

/-! ## 2. The connected trace ratio for kernel insertions -/

section CorrK

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- `Tr(F K^{m+1})` for a kernel insertion `F`: `trOne μ k F m = trc(F ∗ k^{∗(m+1)})`.

DERIVED: `1` is the offset of `iter`. -/
noncomputable def trOne (μ : Measure X) (k F : X → X → ℝ) (m : ℕ) : ℝ :=
  trc μ (conv μ F (iter μ k m))

/-- **The connected torus correlation of two kernel insertions**: on the periodic chain of
`L = p + q + 2 + w + w'` copies of `k`, with `F` covering `w` steps, then `p + 1` free steps, `G`
covering `w'` steps and `q + 1` free steps,
`Tr(F K^{p+1} G K^{q+1})/Tr K^L − (Tr(F K^{L−w})/Tr K^L)(Tr(G K^{L−w'})/Tr K^L)`.

DERIVED: `1` and `2` are the offsets of `iter`, so the chain has `p + q + 2 + w + w'` steps. -/
noncomputable def connK (μ : Measure X) (k F G : X → X → ℝ) (w w' p q : ℕ) : ℝ :=
  trK μ k F G p q / trPow μ k (p + q + w + w' + 1)
    - trOne μ k F (p + q + w' + 1) / trPow μ k (p + q + w + w' + 1)
      * (trOne μ k G (p + q + w + 1) / trPow μ k (p + q + w + w' + 1))

/-- A bounded kernel applied to a bounded measurable function is measurable.

DERIVED: no numeral appears in the statement. -/
theorem measurable_kf {K : X → X → ℝ} (hK : Bdd K) {g : X → ℝ} (hg : Measurable g) :
    Measurable (kernelFun K μ g) :=
  measurable_integral_right (F := fun x y => K x y * g y) (hK.meas.mul (hg.comp measurable_snd))

/-- A kernel bounded by `CK` applied to a function bounded by `Cg` is bounded by `CK Cg`.

DERIVED: no numeral appears in the statement. -/
theorem abs_kf_le {K : X → X → ℝ} {CK : ℝ} (hK : ∀ x y, |K x y| ≤ CK) {g : X → ℝ} {Cg : ℝ}
    (hg : ∀ x, |g x| ≤ Cg) (x : X) : |kernelFun K μ g x| ≤ CK * Cg := by
  unfold kernelFun
  exact abs_integral_le fun y => HiddenChain.abs_mul_le_of (hK x y) (hg y)

/-- The Hilbert–Schmidt norm of a kernel constant in its second variable is the `L²` norm squared.

DERIVED: `2` is the square. -/
theorem hs_left (h : X → ℝ) : hs μ (fun x (_ : X) => h x) = ∫ x, h x ^ 2 ∂μ := by
  unfold hs
  congr 1; funext x
  simp

/-- `∫ f (a g + h) = a ∫ f g + ∫ f h` for bounded measurable `f`, `g`, `h`.

DERIVED: no numeral appears in the statement. -/
theorem integral_mul_split {f g h : X → ℝ} (a : ℝ) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) {Cf Cg Ch : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg)
    (hhb : ∀ x, |h x| ≤ Ch) :
    ∫ x, f x * (a * g x + h x) ∂μ = a * ∫ x, f x * g x ∂μ + ∫ x, f x * h x ∂μ := by
  have e : (fun x => f x * (a * g x + h x)) = fun x => a * (f x * g x) + f x * h x := by
    funext x; ring
  rw [e, integral_add ((integrable_mul_of_bdd hf hg hfb hgb).const_mul a)
    (integrable_mul_of_bdd hf hh hfb hhb), integral_const_mul]

variable {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)

include hφm hφb hφ1 in
/-- **`F φ` has `L²` norm at most `A`** for `OpBd F A` and `‖φ‖ = 1`: `OpBd.left` on the kernel
`φ(u)` constant in its second variable (`hs_left`).

DERIVED: `2` is the square of the norm; `1` the unit norm. -/
theorem sq_kf_le {F : X → X → ℝ} {A : ℝ} (hF : OpBd μ F A) :
    ∫ x, kernelFun F μ φ x ^ 2 ∂μ ≤ A ^ 2 := by
  have h := hF.left (fun u (_ : X) => φ u) (bdd_left hφm hφb)
  have e1 : conv μ F (fun u (_ : X) => φ u) = fun x (_ : X) => kernelFun F μ φ x := rfl
  simp only [e1, hs_left, hφ1, mul_one] at h
  exact h

include hφm hφb hφ1 in
/-- **The vacuum matrix element of an insertion is at most its norm**: `|⟨φ, F φ⟩| ≤ A` for
`OpBd F A`, by Cauchy–Schwarz and `sq_kf_le`.

DERIVED: `1` is the unit norm; `2` the square. -/
theorem abs_vac_le {F : X → X → ℝ} {A : ℝ} (hF : OpBd μ F A) :
    |∫ x, kernelFun F μ φ x * φ x ∂μ| ≤ A := by
  obtain ⟨CF, hCF⟩ := hF.bdd.bdd
  have hfm := measurable_kf (μ := μ) hF.bdd hφm
  have hfb : ∀ x, |kernelFun F μ φ x| ≤ CF * Bφ := abs_kf_le hCF hφb
  have hcs := sq_integral_mul_le (ν := μ) (f := kernelFun F μ φ) (g := φ)
    (integrable_of_bdd (hfm.pow_const 2) (C := (CF * Bφ) ^ 2) (fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2))
    (integrable_of_bdd (hφm.pow_const 2) (C := Bφ ^ 2) (fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2))
    (integrable_mul_of_bdd hfm hφm hfb hφb)
  rw [hφ1, mul_one] at hcs
  have h2 := hcs.trans (sq_kf_le hφm hφb hφ1 hF)
  rw [← sq_abs] at h2
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hF.nonneg two_ne_zero).mp h2

include hφm hφb in
/-- **Reading `φ` against the first variable of a composition**:
`∫ φ(y) (G ∗ M)(y, x) dy = ∫ (Gᵀ φ)(v) M(v, x) dv`, one Fubini swap.

DERIVED: no numeral appears in the statement. -/
theorem row_conv {G M : X → X → ℝ} (hG : Bdd G) (hM : Bdd M) (x : X) :
    ∫ y, φ y * conv μ G M y x ∂μ = ∫ v, kernelFun (tp G) μ φ v * M v x ∂μ := by
  obtain ⟨CM, hCM⟩ := hM.bdd
  have hB : Bdd (fun y v => φ y * (G y v * M v x)) :=
    FluxSectorBound.bdd_mul (bdd_left hφm hφb)
      (FluxSectorBound.bdd_mul hG (bdd_right (hM.col x) (fun v => hCM v x)))
  obtain ⟨CB, hCB⟩ := hB.bdd
  simp only [conv, kernelFun, tp]
  calc ∫ y, φ y * ∫ v, G y v * M v x ∂μ ∂μ = ∫ y, ∫ v, φ y * (G y v * M v x) ∂μ ∂μ := by
        congr 1; funext y; rw [integral_const_mul]
    _ = ∫ v, ∫ y, φ y * (G y v * M v x) ∂μ ∂μ := swap_bdd hB.meas hCB
    _ = ∫ v, (∫ y, G y v * φ y ∂μ) * M v x ∂μ := by
        congr 1; funext v; rw [← integral_mul_const]; congr 1; funext y; ring

include hφm hφb in
/-- **The vacuum element does not see a transpose**: `⟨φ, Gᵀ φ⟩ = ⟨φ, G φ⟩`, one Fubini swap.

DERIVED: no numeral appears in the statement. -/
theorem vac_tp {G : X → X → ℝ} (hG : Bdd G) :
    ∫ v, kernelFun (tp G) μ φ v * φ v ∂μ = ∫ x, kernelFun G μ φ x * φ x ∂μ := by
  have hB : Bdd (fun v y => G y v * φ y * φ v) :=
    FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul (bdd_tp hG) (bdd_right hφm hφb))
      (bdd_left hφm hφb)
  obtain ⟨CB, hCB⟩ := hB.bdd
  simp only [kernelFun, tp]
  calc ∫ v, (∫ y, G y v * φ y ∂μ) * φ v ∂μ = ∫ v, ∫ y, G y v * φ y * φ v ∂μ ∂μ := by
        congr 1; funext v; rw [integral_mul_const]
    _ = ∫ y, ∫ v, G y v * φ y * φ v ∂μ ∂μ := swap_bdd hB.meas hCB
    _ = ∫ x, (∫ y, G x y * φ y ∂μ) * φ x ∂μ := by
        congr 1; funext y; rw [← integral_mul_const]; congr 1; funext v; ring

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hkm hkb hsym hφm hφb hφ1 heig in
/-- **A kernel insertion composed with a power of `k`**, split at the vacuum:
`(F ∗ k^{∗(p+1)})(x, y) = c^{p+1} (F φ)(x) φ(y) + (F ∗ r^{∗(p+1)})(x, y)`, `r = k − c φ⊗φ`
(`KernelPower.iter_decomp`).

DERIVED: `1` is the offset of `iter`. -/
theorem conv_iter_eq {F : X → X → ℝ} (hF : Bdd F) (p : ℕ) (x y : X) :
    conv μ F (iter μ k p) x y
      = c ^ (p + 1) * (kernelFun F μ φ x * φ y) + conv μ F (iter μ (rem k c φ) p) x y := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hRp := (Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) p
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨Cr, hCr⟩ := hRp.bdd
  have e : (fun u => F x u * iter μ k p u y)
      = fun u => c ^ (p + 1) * φ y * (F x u * φ u) + F x u * iter μ (rem k c φ) p u y := by
    funext u; rw [iter_decomp hk hsym hφm hφb hφ1 heig p u y]; ring
  simp only [conv, kernelFun]
  rw [e, integral_add ((integrable_mul_of_bdd (hF.row x) hφm (hCF x) hφb).const_mul _)
    (integrable_mul_of_bdd (hF.row x) (hRp.col y) (hCF x) (fun u => hCr u y)), integral_const_mul]
  ring

include hkm hkb hsym hφm hφb hφ1 heig in
/-- **`φ` read against `G ∗ k^{∗(q+1)}`**: `∫ φ(y) (G ∗ k^{∗(q+1)})(y, x) dy
= c^{q+1} ⟨Gᵀφ, φ⟩ φ(x) + (r^{∗(q+1)} Gᵀφ)(x)`, by `row_conv`, `KernelPower.iter_decomp` and the
symmetry of `r^{∗(q+1)}`.

DERIVED: `1` is the offset of `iter`. -/
theorem row_conv_iter {G : X → X → ℝ} (hG : Bdd G) (q : ℕ) (x : X) :
    ∫ y, φ y * conv μ G (iter μ k q) y x ∂μ
      = c ^ (q + 1) * (∫ v, kernelFun (tp G) μ φ v * φ v ∂μ) * φ x
        + kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hRq := hr.iter (μ := μ) q
  obtain ⟨Cr, hCr⟩ := hRq.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  have hgm := measurable_kf (μ := μ) (bdd_tp hG) hφm
  have hgb : ∀ v, |kernelFun (tp G) μ φ v| ≤ CG * Bφ := abs_kf_le (fun a b => hCG b a) hφb
  rw [row_conv hφm hφb hG (hk.iter (μ := μ) q) x]
  have e : (fun v => kernelFun (tp G) μ φ v * iter μ k q v x)
      = fun v => c ^ (q + 1) * φ x * (kernelFun (tp G) μ φ v * φ v)
        + iter μ (rem k c φ) q x v * kernelFun (tp G) μ φ v := by
    funext v
    rw [iter_decomp hk hsym hφm hφb hφ1 heig q v x,
      CyclicKernel.iter_symm hr (rem_symm hsym) q v x]
    ring
  rw [e, integral_add ((integrable_mul_of_bdd hgm hφm hgb hφb).const_mul _)
    (integrable_mul_of_bdd (hRq.row x) hgm (hCr x) hgb), integral_const_mul]
  show _ = _ + ∫ v, iter μ (rem k c φ) q x v * kernelFun (tp G) μ φ v ∂μ
  ring

include hkm hkb hsym hφm hφb in
/-- **`φ` read against `F ∗ r^{∗(p+1)}`**: `∫ φ(y) (F ∗ r^{∗(p+1)})(y, x) dy = (r^{∗(p+1)} Fᵀφ)(x)`.

DERIVED: `1` is the offset of `iter`. -/
theorem row_conv_rem {F : X → X → ℝ} (hF : Bdd F) (p : ℕ) (x : X) :
    ∫ y, φ y * conv μ F (iter μ (rem k c φ) p) y x ∂μ
      = kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := Bdd.rem hk hφm hφb (c := c)
  rw [row_conv hφm hφb hF (hr.iter (μ := μ) p) x]
  show _ = ∫ v, iter μ (rem k c φ) p x v * kernelFun (tp F) μ φ v ∂μ
  congr 1; funext v
  rw [CyclicKernel.iter_symm hr (rem_symm hsym) p v x]; ring

include hkm hkb hsym hφm hφb hφ1 heig in
/-- **The trace with the first factor split at the vacuum**:
`Tr((F K^{p+1}) Q) = c^{p+1} ∫ (Fφ)(x) ∫ φ(y) Q(y, x) + Tr((F R^{p+1}) Q)` (`conv_iter_eq`).

DERIVED: `1` is the offset of `iter`. -/
theorem trc_split {F Q : X → X → ℝ} (hF : Bdd F) (hQ : Bdd Q) (p : ℕ) :
    trc μ (conv μ (conv μ F (iter μ k p)) Q)
      = c ^ (p + 1) * ∫ x, kernelFun F μ φ x * ∫ y, φ y * Q y x ∂μ ∂μ
        + trc μ (conv μ (conv μ F (iter μ (rem k c φ) p)) Q) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hRp := (Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) p
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CQ, hCQ⟩ := hQ.bdd
  have hFR : Bdd (conv μ F (iter μ (rem k c φ) p)) := hF.conv hRp
  obtain ⟨CR, hCR⟩ := hFR.bdd
  have hFRQ : Bdd (conv μ (conv μ F (iter μ (rem k c φ) p)) Q) := hFR.conv hQ
  obtain ⟨CRQ, hCRQ⟩ := hFRQ.bdd
  have hfm := measurable_kf (μ := μ) hF hφm
  have hfb : ∀ x, |kernelFun F μ φ x| ≤ CF * Bφ := abs_kf_le hCF hφb
  have hhm : Measurable (fun x => ∫ y, φ y * Q y x ∂μ) :=
    measurable_integral_right (F := fun x y => φ y * Q y x)
      ((hφm.comp measurable_snd).mul (hQ.meas.comp measurable_swap))
  have hhb : ∀ x, |∫ y, φ y * Q y x ∂μ| ≤ Bφ * CQ := fun x =>
    abs_integral_le fun y => HiddenChain.abs_mul_le_of (hφb y) (hCQ y x)
  have hpt : ∀ x, conv μ (conv μ F (iter μ k p)) Q x x
      = c ^ (p + 1) * (kernelFun F μ φ x * ∫ y, φ y * Q y x ∂μ)
        + conv μ (conv μ F (iter μ (rem k c φ) p)) Q x x := by
    intro x
    have e : (fun y => conv μ F (iter μ k p) x y * Q y x)
        = fun y => c ^ (p + 1) * kernelFun F μ φ x * (φ y * Q y x)
          + conv μ F (iter μ (rem k c φ) p) x y * Q y x := by
      funext y; rw [conv_iter_eq hφm hφb hφ1 hkm hkb hsym heig hF p x y]; ring
    show ∫ y, conv μ F (iter μ k p) x y * Q y x ∂μ = _
    rw [e, integral_add
      ((integrable_mul_of_bdd hφm (hQ.col x) hφb (fun y => hCQ y x)).const_mul _)
      (integrable_mul_of_bdd (hFR.row x) (hQ.col x) (hCR x) (fun y => hCQ y x)),
      integral_const_mul]
    show _ = _ + ∫ y, conv μ F (iter μ (rem k c φ) p) x y * Q y x ∂μ
    ring
  have hdiag : Integrable (fun x => conv μ (conv μ F (iter μ (rem k c φ) p)) Q x x) μ :=
    integrable_of_bdd (hFRQ.meas.comp (measurable_id.prodMk measurable_id)) (fun x => hCRQ x x)
  unfold trc
  simp_rw [hpt]
  rw [integral_add ((integrable_mul_of_bdd hfm hhm hfb hhb).const_mul _) hdiag,
    integral_const_mul]

include hkm hkb hsym hφm hφb hφ1 heig in
/-- **The two-insertion trace split at the vacuum**:
`Tr(F K^{p+1} G K^{q+1}) = c^{p+1} c^{q+1} ⟨φ, Fφ⟩⟨φ, Gφ⟩ + c^{p+1} ⟨Fφ, R^{q+1} Gᵀφ⟩
+ c^{q+1} ⟨Gφ, R^{p+1} Fᵀφ⟩ + Tr(F R^{p+1} G R^{q+1})`. `trc_split` on `F`, cyclicity, `trc_split`
on `G`, with `row_conv_iter`, `row_conv_rem`, `vac_tp` and `trK_comm`.

DERIVED: `1` is the offset of `iter`. -/
theorem trK_decomp {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) (p q : ℕ) :
    trK μ k F G p q
      = c ^ (p + 1) * c ^ (q + 1)
          * ((∫ x, kernelFun F μ φ x * φ x ∂μ) * ∫ x, kernelFun G μ φ x * φ x ∂μ)
        + c ^ (p + 1) * ∫ x, kernelFun F μ φ x
            * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ
        + c ^ (q + 1) * ∫ x, kernelFun G μ φ x
            * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ
        + trK μ (rem k c φ) F G p q := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hGKq : Bdd (conv μ G (iter μ k q)) := hG.conv (hk.iter q)
  have hFRp : Bdd (conv μ F (iter μ (rem k c φ) p)) := hF.conv (hr.iter p)
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  obtain ⟨Cq, hCq⟩ := (hr.iter (μ := μ) q).bdd
  have hfm := measurable_kf (μ := μ) hF hφm
  have hfb : ∀ x, |kernelFun F μ φ x| ≤ CF * Bφ := abs_kf_le hCF hφb
  have hgtm := measurable_kf (μ := μ) (bdd_tp hG) hφm
  have hgtb : ∀ v, |kernelFun (tp G) μ φ v| ≤ CG * Bφ := abs_kf_le (fun a b => hCG b a) hφb
  have hKm := measurable_kf (μ := μ) (hr.iter (μ := μ) q) hgtm
  have hKb := abs_kf_le (μ := μ) hCq hgtb
  have s1 := trc_split hφm hφb hφ1 hkm hkb hsym heig hF hGKq p
  have s2 : ∫ x, kernelFun F μ φ x * ∫ y, φ y * conv μ G (iter μ k q) y x ∂μ ∂μ
      = c ^ (q + 1) * (∫ v, kernelFun (tp G) μ φ v * φ v ∂μ) * ∫ x, kernelFun F μ φ x * φ x ∂μ
        + ∫ x, kernelFun F μ φ x
            * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ := by
    simp_rw [row_conv_iter hφm hφb hφ1 hkm hkb hsym heig hG q]
    exact integral_mul_split _ hfm hφm hKm hfb hφb hKb
  have s3 := trc_split hφm hφb hφ1 hkm hkb hsym heig hG hFRp q
  simp_rw [row_conv_rem hφm hφb hkm hkb hsym hF p] at s3
  have s4 : trK μ (rem k c φ) G F q p = trK μ (rem k c φ) F G p q :=
    trK_comm hr hG hF q p
  unfold trK at s4 ⊢
  rw [s1, s2, trc_conv_comm hFRp hGKq, s3, s4, vac_tp hφm hφb hG]
  ring


include hkm hkb hsym hφm hφb hφ1 heig in
/-- **The one-insertion trace split at the vacuum**:
`Tr(F K^{m+1}) = c^{m+1} ⟨φ, Fφ⟩ + Tr(F R^{m+1})` (`conv_iter_eq` on the diagonal).

DERIVED: `1` is the offset of `iter`. -/
theorem trOne_decomp {F : X → X → ℝ} (hF : Bdd F) (m : ℕ) :
    trOne μ k F m = c ^ (m + 1) * ∫ x, kernelFun F μ φ x * φ x ∂μ
      + trc μ (conv μ F (iter μ (rem k c φ) m)) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hFR : Bdd (conv μ F (iter μ (rem k c φ) m)) :=
    hF.conv ((Bdd.rem hk hφm hφb (c := c)).iter m)
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CR, hCR⟩ := hFR.bdd
  have hfm := measurable_kf (μ := μ) hF hφm
  have hfb : ∀ x, |kernelFun F μ φ x| ≤ CF * Bφ := abs_kf_le hCF hφb
  have hdiag : Integrable (fun x => conv μ F (iter μ (rem k c φ) m) x x) μ :=
    integrable_of_bdd (hFR.meas.comp (measurable_id.prodMk measurable_id)) (fun x => hCR x x)
  unfold trOne trc
  simp_rw [conv_iter_eq hφm hφb hφ1 hkm hkb hsym heig hF m]
  rw [integral_add ((integrable_mul_of_bdd hfm hφm hfb hφb).const_mul _) hdiag,
    integral_const_mul]

include hkm hkb hsym hφm hφb hφ1 heig in
/-- **The partition function at an even power**: `Tr K^{2i+2} = c^{2i+2} + hs(r^{∗(i+1)})`
(`KernelPower.iter_decomp`, `OpenAIBridgeCluster.iter_rem_diag`).

DERIVED: `1` and `2` are the offsets of `iter`. -/
theorem trPow_even (i : ℕ) :
    trPow μ k (i + i + 1) = c ^ (i + i + 2) + hs μ (iter μ (rem k c φ) i) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hRi := (Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) i
  obtain ⟨Ci, hCi⟩ := hRi.bdd
  have hpt : ∀ x, iter μ k (i + i + 1) x x
      = c ^ (i + i + 2) * (φ x * φ x) + ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ := by
    intro x
    rw [iter_decomp hk hsym hφm hφb hφ1 heig (i + i + 1) x x,
      iter_rem_diag hkm hkb hsym hφm hφb i x]
    ring
  have hD : Integrable (fun x => ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ) μ :=
    integrable_of_bdd (measurable_integral_right (hRi.meas.pow_const 2)) (C := Ci ^ 2)
      (fun x => abs_integral_le fun y => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCi x y) 2)
  have hφ1' : ∫ x, φ x * φ x ∂μ = 1 := by simpa [sq] using hφ1
  unfold trPow
  simp_rw [hpt]
  rw [integral_add ((integrable_mul_of_bdd hφm hφm hφb hφb).const_mul _) hD, integral_const_mul,
    hφ1', mul_one]
  rfl

/-- The real-number bookkeeping of the trace ratio with the excited weights at three levels. With
`Z = Λ(1+σ₀)`, `Tr(F K^{L−w}) = Λ(α + e_a)`, `Tr(G K^{L−w'}) = Λ(β + e_b)`,
`Tr(F K^{t} G K^{L−t−w−w'}) = Λ(αβ + e)`, `Λ > 0`, `0 ≤ σ₀ ≤ σ ≤ 1`, `|α| ≤ A`, `|β| ≤ B`,
`|e_a| ≤ Aσ` and `|e_b| ≤ Bσ`, the connected ratio is within `|e| + 4ABσ` of zero. It is
`OpenAIBridgeCluster.conn_alg` with the excited weight of the partition function below the others.

DERIVED: `4` counts the four terms of the second numerator, each at most `ABσ` (`σ² ≤ σ` by
`σ ≤ 1`); `1` is the vacuum's own weight in `Z` and the cap on `σ`; `2` the square of `1+σ₀`; `0`
the signs. -/
theorem conn_alg2 {Λ σ0 σ α β ea eb e A B : ℝ} (hΛ : 0 < Λ) (hσ0 : 0 ≤ σ0) (hσ0σ : σ0 ≤ σ)
    (hσ1 : σ ≤ 1) (hα : |α| ≤ A) (hβ : |β| ≤ B) (hea : |ea| ≤ A * σ) (heb : |eb| ≤ B * σ) :
    |Λ * (α * β + e) / (Λ * (1 + σ0))
        - Λ * (α + ea) / (Λ * (1 + σ0)) * (Λ * (β + eb) / (Λ * (1 + σ0)))|
      ≤ |e| + 4 * (A * B) * σ := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hα
  have hB : 0 ≤ B := (abs_nonneg _).trans hβ
  have hσ : 0 ≤ σ := hσ0.trans hσ0σ
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
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have t1 : |α * β * σ0| ≤ A * B * σ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ0]
    exact mul_le_mul (mul_le_mul hα hβ (abs_nonneg _) hA) hσ0σ hσ0 hAB
  have t2 : |α * eb| ≤ A * B * σ := by
    rw [abs_mul]
    calc |α| * |eb| ≤ A * (B * σ) := mul_le_mul hα heb (abs_nonneg _) hA
      _ = A * B * σ := by ring
  have t3 : |β * ea| ≤ A * B * σ := by
    rw [abs_mul]
    calc |β| * |ea| ≤ B * (A * σ) := mul_le_mul hβ hea (abs_nonneg _) hB
      _ = A * B * σ := by ring
  have t4 : |ea * eb| ≤ A * B * σ := by
    rw [abs_mul]
    calc |ea| * |eb| ≤ A * σ * (B * σ) := mul_le_mul hea heb (abs_nonneg _) (by positivity)
      _ = A * B * σ * σ := by ring
      _ ≤ A * B * σ * 1 := mul_le_mul_of_nonneg_left hσ1 (mul_nonneg hAB hσ)
      _ = A * B * σ := mul_one _
  have h2 : |α * β * σ0 - α * eb - β * ea - ea * eb| ≤ 4 * (A * B) * σ := by
    have s1 := abs_sub (α * β * σ0 - α * eb - β * ea) (ea * eb)
    have s2 := abs_sub (α * β * σ0 - α * eb) (β * ea)
    have s3 := abs_sub (α * β * σ0) (α * eb)
    linarith
  have h3 : |(α * β * σ0 - α * eb - β * ea - ea * eb) / (1 + σ0) ^ 2| ≤ 4 * (A * B) * σ := by
    rw [abs_div, abs_of_pos (pow_pos hD 2)]
    exact (div_le_self (abs_nonneg _) (one_le_pow₀ (by linarith))).trans h2
  calc |e / (1 + σ0) + (α * β * σ0 - α * eb - β * ea - ea * eb) / (1 + σ0) ^ 2|
      ≤ |e / (1 + σ0)| + |(α * β * σ0 - α * eb - β * ea - ea * eb) / (1 + σ0) ^ 2| :=
        abs_add_le _ _
    _ ≤ |e| + 4 * (A * B) * σ := add_le_add h1 h3

/-- A multiplier of a positive power is nonnegative when the product is.

DERIVED: `0` is the sign. -/
theorem nonneg_of_mul_pow {A c : ℝ} {w : ℕ} (hc0 : c ≠ 0) (h : 0 ≤ A * |c| ^ w) : 0 ≤ A := by
  by_contra hneg
  linarith [mul_neg_of_neg_of_pos (not_le.mp hneg) (pow_pos (abs_pos.mpr hc0) w)]

variable (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) {n : ℕ}
  (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖
      ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖)

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The connected torus correlation of two kernel insertions, with the wrap-around term bounded
by Hölder.** On the periodic chain of `L = p + q + 2 + w + w'` copies of `k` (`w`, `w'`, `p + q`
even), for kernel insertions with `OpBd F (A |c|^w)` and `OpBd G (B |c|^{w'})` — the norms of
`|F| ≤ A k^{∗w}` and `|G| ≤ B k^{∗w'}` (`opBd_of_le`) — and `σ_{(p+q)/2+1} ≤ 1`,

    |connK μ k F G w w' p q| ≤ A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋ + 5 σ_{(p+q)/2+1}),

`σ_j = excited μ k c φ j`. `trK_decomp` splits the two-point trace: the vacuum term, two
vacuum-to-excited terms (`OpenAIBridgeCluster.abs_integral_remFun_le`, with the `L²` norms of
`sq_kf_le`), and the excited–excited term `Tr(F R^{p+1} G R^{q+1})` (`abs_trK_le`). The one-point
traces (`trOne_decomp`, `abs_trc_conv_iter_le`) and the partition function (`trPow_even`) carry the
excited weight at higher levels, which `OpenAIBridgeUniform.excited_add_le` brings down to
`σ_{(p+q)/2+1}`; `conn_alg2` closes.

DERIVED: `5 = 1 + 4` counts the excited–excited term and the four terms of `conn_alg2`; `1/2` is
the contraction of the gap hypothesis; `1` and `2` are the offsets of `iter` and the halving of the
even `p + q`; `0` the excluded eigenvalue. -/
theorem connK_le_excited (hc0 : c ≠ 0) {F G : X → X → ℝ} {A B : ℝ} {w w' : ℕ}
    (hF : OpBd μ F (A * |c| ^ w)) (hG : OpBd μ G (B * |c| ^ w')) (hw : Even w) (hw' : Even w')
    (p q : ℕ) (hpq : Even (p + q)) (hσ1 : excited μ k c φ ((p + q) / 2 + 1) ≤ 1) :
    |connK μ k F G w w' p q| ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
      + 5 * excited μ k c φ ((p + q) / 2 + 1)) := by
  obtain ⟨i, hi⟩ := hpq
  obtain ⟨v, hv⟩ := hw
  obtain ⟨v', hv'⟩ := hw'
  have hi2 : (p + q) / 2 = i := by omega
  rw [hi2] at hσ1 ⊢
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
  obtain ⟨CF, hCF⟩ := hF.bdd.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd.bdd
  -- the excited weights
  have hσdef : ∀ j, hs μ (iter μ (rem k c φ) j)
      = excited μ k c φ (j + 1) * |c| ^ (2 * (j + 1)) := by
    intro j; unfold excited; rw [Nat.add_sub_cancel, div_mul_cancel₀ _ (pow_ne_zero _ hcne)]
  have hexc0 : ∀ j, 0 ≤ excited μ k c φ j := fun j => by
    unfold excited; exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have hmono : ∀ l, excited μ k c φ (i + 1 + l) ≤ excited μ k c φ (i + 1) := by
    intro l
    rcases Nat.eq_zero_or_pos l with h0 | hl
    · simp [h0]
    · exact (excited_add_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 (i + 1) l
        (by omega) hl).trans
        (mul_le_of_le_one_left (hexc0 _) (pow_le_one₀ (by norm_num) (by norm_num)))
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
        + (c ^ (p + 1) * ∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ
            + c ^ (q + 1) * ∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2)) := by
    rw [trK_decomp hφm hφb hφ1 hkm hkb hsym heig hF.bdd hG.bdd p q, hcc, hΛ2]
    field_simp
    try ring
  have I2 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap q
    (measurable_kf (μ := μ) hF.bdd hφm) (measurable_kf (μ := μ) (bdd_tp hG.bdd) hφm)
    (abs_kf_le (μ := μ) hCF hφb) (abs_kf_le (μ := μ) (fun a b => hCG b a) hφb)
    hF.nonneg hG.nonneg (sq_kf_le hφm hφb hφ1 hF) (sq_kf_le hφm hφb hφ1 hG.transpose)
  have I3 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap p
    (measurable_kf (μ := μ) hG.bdd hφm) (measurable_kf (μ := μ) (bdd_tp hF.bdd) hφm)
    (abs_kf_le (μ := μ) hCG hφb) (abs_kf_le (μ := μ) (fun a b => hCF b a) hφb)
    hG.nonneg hF.nonneg (sq_kf_le hφm hφb hφ1 hG) (sq_kf_le hφm hφb hφ1 hF.transpose)
  have I4 := abs_trK_le hr hrs hF hG p q i hi
  rw [hσdef i] at I4
  have he : |(c ^ (p + 1) * ∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ
            + c ^ (q + 1) * ∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2)|
      ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + excited μ k c φ (i + 1)) := by
    rw [abs_div, abs_of_pos hcL, div_le_iff₀ hcL]
    have a2 : |c ^ (p + 1) * ∫ x, kernelFun F μ φ x
          * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ|
        ≤ |c| ^ (p + 1) * ((1 / 2) ^ ((q + 1) / n) * |c| ^ (q + 1) * (A * |c| ^ w)
          * (B * |c| ^ w')) := by
      rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left I2 (pow_nonneg hc.le _)
    have a3 : |c ^ (q + 1) * ∫ x, kernelFun G μ φ x
          * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ|
        ≤ |c| ^ (q + 1) * ((1 / 2) ^ ((p + 1) / n) * |c| ^ (p + 1) * (B * |c| ^ w')
          * (A * |c| ^ w)) := by
      rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left I3 (pow_nonneg hc.le _)
    calc _ ≤ _ := abs_add_three _ _ _
      _ ≤ _ := add_le_add (add_le_add a2 a3) I4
      _ = A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
            + excited μ k c φ (i + 1)) * |c| ^ (p + q + w + w' + 2) := by
          rw [hΛ2, show 2 * (i + 1) = (p + 1) + (q + 1) by omega, pow_add |c| (p + 1) (q + 1)]; ring
  -- assemble
  have key := conn_alg2 hcL (hexc0 _) (hmono (v + v')) hσ1 hα hβ heF heG
    (e := (c ^ (p + 1) * ∫ x, kernelFun F μ φ x
              * kernelFun (iter μ (rem k c φ) q) μ (kernelFun (tp G) μ φ) x ∂μ
            + c ^ (q + 1) * ∫ x, kernelFun G μ φ x
              * kernelFun (iter μ (rem k c φ) p) μ (kernelFun (tp F) μ φ) x ∂μ
            + trK μ (rem k c φ) F G p q) / |c| ^ (p + q + w + w' + 2))
  unfold connK
  rw [hT, hOF, hOG, hZ]
  calc _ ≤ _ := key
    _ ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n) + excited μ k c φ (i + 1))
        + 4 * (A * B) * excited μ k c φ (i + 1) := add_le_add he le_rfl
    _ = _ := by ring

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **Exponential clustering of two kernel insertions with a constant uniform in the torus**: under
the hypotheses of `connK_le_excited`, if `σ_{(p+q)/2+1} ≤ (1/2)^⌊((p+q)/2+1)/n⌋`, then

    |connK μ k F G w w' p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

The smaller of `p + 1`, `q + 1` is at most `(p+q)/2 + 1`. It is
`OpenAIBridgeUniform.connTorus_uniform` for kernel insertions, with the gap counted from the slab
edges.

DERIVED: `6 = 1 + 5` is the gap terms plus the constant `5` of `connK_le_excited`; `1/2` is the
contraction of the gap hypothesis; `1` and `2` are the offsets of `iter` and the halving of the
even `p + q`; `0` the excluded eigenvalue. -/
theorem connK_uniform (hc0 : c ≠ 0) {F G : X → X → ℝ} {A B : ℝ} {w w' : ℕ}
    (hF : OpBd μ F (A * |c| ^ w)) (hG : OpBd μ G (B * |c| ^ w')) (hw : Even w) (hw' : Even w')
    (p q : ℕ) (hpq : Even (p + q))
    (hσ : excited μ k c φ ((p + q) / 2 + 1) ≤ (1 / 2) ^ (((p + q) / 2 + 1) / n)) :
    |connK μ k F G w w' p q| ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  have hσ1 : excited μ k c φ ((p + q) / 2 + 1) ≤ 1 :=
    hσ.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have h := connK_le_excited hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF hG hw hw' p q hpq
    hσ1
  have hA0 : 0 ≤ A := nonneg_of_mul_pow hc0 hF.nonneg
  have hB0 : 0 ≤ B := nonneg_of_mul_pow hc0 hG.nonneg
  have hmin : (1 / 2 : ℝ) ^ (((p + q) / 2 + 1) / n)
      ≤ (1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n) := by
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ ((p + 1) / n) := by positivity
    have hq0 : 0 ≤ (1 / 2 : ℝ) ^ ((q + 1) / n) := by positivity
    rcases le_total p q with h' | h'
    · have : (1 / 2 : ℝ) ^ (((p + q) / 2 + 1) / n) ≤ (1 / 2) ^ ((p + 1) / n) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_div_right (by omega))
      linarith
    · have : (1 / 2 : ℝ) ^ (((p + q) / 2 + 1) / n) ≤ (1 / 2) ^ ((q + 1) / n) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_div_right (by omega))
      linarith
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  calc |connK μ k F G w w' p q| ≤ _ := h
    _ ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + 5 * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n))) := by
        refine mul_le_mul_of_nonneg_left ?_ hAB
        linarith
    _ = _ := by ring


include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **The excited weight below a short slab pair is controlled by the window of the seed**: if
`σ_{j0} ≤ (1/2)^{2^a}` at a level with `4 j0 ≤ L ≤ 2^(a+3) n` (the output of
`OpenAIBridgeUniform.gap_side_excited`), then every level `ℓ` with `2ℓ + W = L` and
`4W + 8n ≤ L` has `σ_ℓ ≤ (1/2)^⌊ℓ/n⌋`. `OpenAIBridgeUniform.excited_add_le` from `j0` to `ℓ`, and
`⌊ℓ/n⌋ ≤ 2⌊(ℓ − j0)/n⌋ + 2^a` since `2^a n ≥ L/8 ≥ W/2 + n`.

DERIVED: `3` is the exponent of the largest ratio of the window, `8 = 2^3`; `4` bounds the slab
widths against the torus (`4W ≤ L − 8n`) and is the two doublings in `4 j0 ≤ L`; `1/2` the
contraction; `2` the square of the gap step and the halving `2ℓ + W = L`; `1` the least `j0`; `0`
the excluded eigenvalue and the sign of `n`. -/
theorem excited_le_slab (hc0 : c ≠ 0) (hn0 : 0 < n) {a j0 ℓ L W : ℕ} (hj0 : 1 ≤ j0)
    (hL4 : 2 * (2 * j0) ≤ L) (hhi : L ≤ 2 ^ (a + 3) * n)
    (hexc : excited μ k c φ j0 ≤ (1 / 2) ^ (2 ^ a)) (hℓ : 2 * ℓ + W = L)
    (hW : 4 * W + 8 * n ≤ L) :
    excited μ k c φ ℓ ≤ (1 / 2) ^ (ℓ / n) := by
  have hℓj : j0 + 1 ≤ ℓ := by omega
  have hadd := excited_add_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 j0 (ℓ - j0) hj0
    (by omega)
  rw [show j0 + (ℓ - j0) = ℓ by omega] at hadd
  have ht : L ≤ 8 * (2 ^ a * n) := by
    rw [show 2 ^ (a + 3) * n = 8 * (2 ^ a * n) by ring] at hhi; exact hhi
  have hfl : ℓ / n ≤ 2 * ((ℓ - j0) / n) + 2 ^ a := by
    have h1 : ℓ - j0 < (ℓ - j0) / n * n + n := Nat.lt_div_mul_add hn0
    have key : ℓ < (2 * ((ℓ - j0) / n) + 2 ^ a + 1) * n := by
      have e : (2 * ((ℓ - j0) / n) + 2 ^ a + 1) * n
          = 2 * ((ℓ - j0) / n * n) + 2 ^ a * n + n := by ring
      rw [e]
      generalize (ℓ - j0) / n * n = u at h1 ⊢
      generalize 2 ^ a * n = t at ht ⊢
      omega
    have := (Nat.div_lt_iff_lt_mul hn0).2 key
    generalize ℓ / n = s at this ⊢
    generalize (ℓ - j0) / n = s' at this ⊢
    generalize 2 ^ a = t' at this ⊢
    omega
  calc excited μ k c φ ℓ ≤ (1 / 2) ^ (2 * ((ℓ - j0) / n)) * excited μ k c φ j0 := hadd
    _ ≤ (1 / 2) ^ (2 * ((ℓ - j0) / n)) * (1 / 2) ^ (2 ^ a) :=
        mul_le_mul_of_nonneg_left hexc (by positivity)
    _ = (1 / 2) ^ (2 * ((ℓ - j0) / n) + 2 ^ a) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hfl

include hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap in
/-- **Clustering of two slab insertions from the window of the seed, uniform in the torus.** With
the gap data and a level `j0` as in `excited_le_slab`, for bounded measurable kernels with
`|F| ≤ A k^{∗w}`, `|G| ≤ B k^{∗w'}` (`w = 2v + 2`, `w' = 2v' + 2`), `A, B ≥ 0`, on the chain of
even length `L = p + q + 2 + w + w'` with `4(w + w') + 8n ≤ L`,

    |connK μ k F G w w' p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

`opBd_of_le` turns the pointwise bounds into `OpBd F (A |c|^w)` (`|c| = ‖K‖`), `excited_le_slab`
gives the excited weight, `connK_uniform` closes.

DERIVED: `6` is the constant of `connK_uniform`; `4` and `8` the slab condition of
`excited_le_slab`; `3` the window exponent; `1/2` the contraction; `2` the doubled widths
`2v + 2` and the offsets of `iter`; `1` the offset of `iter` and the least `j0`; `0` the signs and
the excluded eigenvalue. -/
theorem connK_slab (hc0 : c ≠ 0) (hn0 : 0 < n) {a j0 L : ℕ} (hj0 : 1 ≤ j0)
    (hL4 : 2 * (2 * j0) ≤ L) (hhi : L ≤ 2 ^ (a + 3) * n)
    (hexc : excited μ k c φ j0 ≤ (1 / 2) ^ (2 ^ a)) (hLe : Even L)
    {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (v v' : ℕ)
    (hFk : ∀ x y, |F x y| ≤ A * iter μ k (v + v + 1) x y)
    (hGk : ∀ x y, |G x y| ≤ B * iter μ k (v' + v' + 1) x y) (p q : ℕ)
    (hpq : p + q + 2 + (v + v + 2) + (v' + v' + 2) = L)
    (hW : 4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L) :
    |connK μ k F G (v + v + 2) (v' + v' + 2) p q|
      ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  have hF' : OpBd μ F (A * |c| ^ (v + v + 2)) := by
    have h := opBd_of_le hkm hC0 hkb hsym hF hA (v + v + 1) hFk
    rw [← hnorm, show v + v + 1 + 1 = v + v + 2 by omega] at h
    exact h
  have hG' : OpBd μ G (B * |c| ^ (v' + v' + 2)) := by
    have h := opBd_of_le hkm hC0 hkb hsym hG hB (v' + v' + 1) hGk
    rw [← hnorm, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at h
    exact h
  obtain ⟨L', hL'⟩ := hLe
  have hpqe : Even (p + q) := ⟨L' - v - v' - 3, by omega⟩
  have hσ := excited_le_slab hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hn0 hj0 hL4 hhi hexc
    (ℓ := (p + q) / 2 + 1) (W := (v + v + 2) + (v' + v' + 2)) (by omega) hW
  exact connK_uniform hφm hφb hφ1 hkm hC0 hkb hsym heig hnorm hgap hc0 hF' hG'
    ⟨v + 1, by ring⟩ ⟨v' + 1, by ring⟩ p q hpqe hσ

end CorrK

/-! ## 3. On the Wilson torus, at `SU(N)` and over every gauge group -/

section Wilson

open MassGap.RectWilson MassGap.RectTransfer MassGap.DoublingRecursion MassGap.DoublingWilson
  MassGap.OpenAIBridgeSides

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **Clustering of two slab insertions on the `SU(N)` Wilson torus of every even side, uniform in
the torus, from the seed.** If one torus of even side `n ≥ 2` has
`16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic torus of every even side
`L ≥ 2n` there are a normalized eigenfunction `φ` of the slice kernel `kT` and its eigenvalue
`c ≠ 0` such that for all bounded measurable kernels `F`, `G` on the slice with
`|F| ≤ A kT^{∗w}`, `|G| ≤ B kT^{∗w'}` (`w = 2v + 2`, `w' = 2v' + 2`, `A, B ≥ 0`) and all
`p + q + 2 + w + w' = L` with `4(w + w') + 8n ≤ L`,

    |connK F G w w' p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

The separations `p + 1`, `q + 1` are counted from the slab edges. It is
`OpenAIBridgeUniform.gap_side_excited` at the window of `OpenAIBridgeSides.exists_window`, read
through `connK_slab`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of `connK_uniform`;
`4` and `8` the slab condition of `excited_le_slab`; `1/2` the contraction; `2` the doubled side,
the least seed side, the least ratio `L / n`, the doubled widths and the offsets of `iter`; `0` the
time direction of the slice, the sign of the coupling and the excluded eigenvalue; `1` the offset
of `iter` and the unit norm. -/
theorem wilson_connK_slab
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (fun _ : Fin 4 => L) 0) N β z y * φ y
        ∂(hS 0 (tr (fun _ : Fin 4 => L) 0) N) = c * φ z) ∧
      ∀ (F G : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N)
          → (SpT 0 (tr (fun _ : Fin 4 => L) 0) → SUN.SU N) → ℝ), Bdd F → Bdd G →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ v v' : ℕ,
      (∀ x y, |F x y| ≤ A * iter (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
        (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) (v + v + 1) x y) →
      (∀ x y, |G x y| ≤ B * iter (hS 0 (tr (fun _ : Fin 4 => L) 0) N)
        (kT 0 (tr (fun _ : Fin 4 => L) 0) N β) (v' + v' + 1) x y) →
      ∀ p q : ℕ, p + q + 2 + (v + v + 2) + (v' + v' + 2) = L →
        4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L →
        |connK (hS 0 (tr (fun _ : Fin 4 => L) 0) N) (kT 0 (tr (fun _ : Fin 4 => L) 0) N β)
            F G (v + v + 2) (v' + v' + 2) p q|
          ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    OpenAIBridgeUniform.gap_side_excited hN hβ hn he h0 a' L hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig, fun F G hF hG A B hA hB v v' hFk hGk p q hpq hW => ?_⟩
  exact connK_slab hφm hφb hφ1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (kT_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc hLe hF hG hA hB v v' hFk hGk p q
    hpq hW

end Wilson

section WilsonG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.DoublingRecursion
  MassGap.DoublingWilson MassGap.DoublingWilsonG MassGap.GaugeGroup MassGap.CompactGauge
  MassGap.OpenAIBridgeSides MassGap.OpenAIBridgeGroups

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
/-- **Clustering of two slab insertions on the Wilson torus of every gauge group, uniform in the
torus, from the seed** (`wilson_connK_slab` over a `GaugeGroup G`). If one torus of even side
`n ≥ 2` has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic torus of `G` of
every even side `L ≥ 2n`, for bounded measurable kernels `F`, `G'` on the slice with
`|F| ≤ A kTG^{∗w}`, `|G'| ≤ B kTG^{∗w'}` (`w = 2v + 2`, `w' = 2v' + 2`, `A, B ≥ 0`) and all
`p + q + 2 + w + w' = L` with `4(w + w') + 8n ≤ L`,

    |connK F G' w w' p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

It is `OpenAIBridgeGroups.gap_side_excitedG` read through `connK_slab`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of `connK_uniform`;
`4` and `8` the slab condition of `excited_le_slab`; `1/2` the contraction; `2` the doubled side,
the least seed side, the least ratio `L / n`, the doubled widths and the offsets of `iter`; `0` the
time direction of the slice, the sign of the coupling and the excluded eigenvalue; `1` the offset
of `iter` and the unit norm. -/
theorem wilson_connK_slabG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → G) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG G 0 (tr (fun _ : Fin 4 => L) 0)) = 1 ∧
      (∀ z, ∫ y, kTG G 0 (tr (fun _ : Fin 4 => L) 0) β z y * φ y
        ∂(hSG G 0 (tr (fun _ : Fin 4 => L) 0)) = c * φ z) ∧
      ∀ (F G' : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → G)
          → (SpT 0 (tr (fun _ : Fin 4 => L) 0) → G) → ℝ), Bdd F → Bdd G' →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → ∀ v v' : ℕ,
      (∀ x y, |F x y| ≤ A * iter (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
        (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) (v + v + 1) x y) →
      (∀ x y, |G' x y| ≤ B * iter (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
        (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) (v' + v' + 1) x y) →
      ∀ p q : ℕ, p + q + 2 + (v + v + 2) + (v' + v' + 2) = L →
        4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L →
        |connK (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β)
            F G' (v + v + 2) (v' + v' + 2) p q|
          ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    gap_side_excitedG hβ hn he h0 a' L hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig, fun F G' hF hG A B hA hB v v' hFk hGk p q hpq hW => ?_⟩
  exact connK_slab hφm hφb hφ1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) heig hc hgap hc0 (by omega) hj0 hL4 hhi hexc hLe hF hG hA hB v v' hFk hGk p q
    hpq hW

end WilsonG


/-! ## 4. The slab kernel and the trace identity on the chain -/

section SlabChain

open HiddenChain

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Y]

/-- **The kernel of a slab insertion**: `slabKer μ ν w m G x z` integrates the insertion `G` against
the step weights of `m + 1` steps from `x` to `z`, over the `m` intermediate slices and the `m + 1`
hidden variables. It is the chain `HiddenChain.chain` with its last point pinned at `z`
(`chain_slab`).

DERIVED: `1` is the offset of the number of steps, as for `KernelPower.iter`. -/
noncomputable def slabKer (μ : Measure X) (ν : Measure Y) (w : X → Y → X → ℝ) :
    ℕ → ((ℕ → X) → (ℕ → Y) → ℝ) → X → X → ℝ
  | 0, G, x, z =>
      ∫ a, w x a z * G (scons x (fun _ => z)) (scons a (fun _ => Classical.arbitrary Y)) ∂ν
  | m + 1, G, x, z =>
      ∫ y, ∫ a, w x a y * slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z ∂ν ∂μ

variable {μ : Measure X} {ν : Measure Y} {w : X → Y → X → ℝ}

omit [Nonempty Y] in
/-- The step weight is measurable in its hidden variable.

DERIVED: no numeral appears in the statement. -/
theorem measurable_w_mid (hw : WMeas w) (x z : X) : Measurable (fun a => w x a z) :=
  hw.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))

/-- **The slab kernel is jointly measurable**, with a measurable parameter in the insertion; the
proof is that of `HiddenChain.measurable_chain`.

DERIVED: no numeral appears in the statement. -/
theorem measurable_slabKer [SFinite μ] [SFinite ν] (hw : WMeas w) :
    ∀ (m : ℕ) {P : Type} [MeasurableSpace P] {G : P → (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : P × (ℕ → X) × (ℕ → Y) => G q.1 q.2.1 q.2.2) →
      Measurable (fun q : P × X × X => slabKer μ ν w m (G q.1) q.2.1 q.2.2)
  | 0, P, _, G, hG => by
    have h : Measurable (fun r : (P × X × X) × Y => w r.1.2.1 r.2 r.1.2.2
        * G r.1.1 (scons r.1.2.1 (fun _ => r.1.2.2))
          (scons r.2 (fun _ => Classical.arbitrary Y))) := by
      refine (hw.comp (measurable_fst.snd.fst.prodMk
        (measurable_snd.prodMk measurable_fst.snd.snd))).mul ?_
      exact hG.comp (measurable_fst.fst.prodMk
        ((measurable_scons.comp (measurable_fst.snd.fst.prodMk
          (measurable_pi_lambda _ fun _ => measurable_fst.snd.snd))).prodMk
        (measurable_scons.comp (measurable_snd.prodMk measurable_const))))
    exact (h.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  | m + 1, P, _, G, hG => by
    have hG' : Measurable (fun s : ((P × X) × Y) × (ℕ → X) × (ℕ → Y) =>
        G s.1.1.1 (scons s.1.1.2 s.2.1) (scons s.1.2 s.2.2)) :=
      hG.comp (measurable_fst.fst.fst.prodMk
        ((measurable_scons.comp (measurable_fst.fst.snd.prodMk measurable_snd.fst)).prodMk
          (measurable_scons.comp (measurable_fst.snd.prodMk measurable_snd.snd))))
    have ih := measurable_slabKer hw m (P := (P × X) × Y)
      (G := fun r V A => G r.1.1 (scons r.1.2 V) (scons r.2 A)) hG'
    have h1 : Measurable (fun r : ((P × X × X) × X) × Y => w r.1.1.2.1 r.2 r.1.2
        * slabKer μ ν w m (fun V A => G r.1.1.1 (scons r.1.1.2.1 V) (scons r.2 A))
          r.1.2 r.1.1.2.2) := by
      refine (hw.comp (measurable_fst.fst.snd.fst.prodMk
        (measurable_snd.prodMk measurable_fst.snd))).mul ?_
      exact ih.comp (((measurable_fst.fst.fst.prodMk measurable_fst.fst.snd.fst).prodMk
        measurable_snd).prodMk (measurable_fst.snd.prodMk measurable_fst.fst.snd.snd))
    have h2 := (h1.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    exact (h2.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- **The slab kernel is bounded**: `|slabKer m G| ≤ C^{m+1} B` for `|w| ≤ C`, `|G| ≤ B`.

DERIVED: `1` is the offset of the number of steps. -/
theorem abs_slabKer_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ}, (∀ V A, |G V A| ≤ B) →
      ∀ x z, |slabKer μ ν w m G x z| ≤ C ^ (m + 1) * B
  | 0, G, B, hG, x, z => by
    show |∫ a, w x a z * G (scons x (fun _ => z)) (scons a (fun _ => Classical.arbitrary Y)) ∂ν|
      ≤ C ^ (0 + 1) * B
    rw [zero_add, pow_one]
    exact abs_integral_le fun a => abs_mul_le_of (hwb x a z) (hG _ _)
  | m + 1, G, B, hG, x, z => by
    show |∫ y, ∫ a, w x a y * slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z ∂ν ∂μ|
      ≤ C ^ (m + 1 + 1) * B
    refine abs_integral_le fun y => abs_integral_le fun a => ?_
    have h1 := abs_slabKer_le hwb m (G := fun V A => G (scons x V) (scons a A))
      (fun V A => hG _ _) y z
    calc |w x a y * slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z|
        ≤ C * (C ^ (m + 1) * B) := abs_mul_le_of (hwb x a y) h1
      _ = C ^ (m + 1 + 1) * B := by ring

/-- The slab kernel of a bounded measurable insertion is a bounded measurable kernel.

DERIVED: `1` is the offset of the number of steps. -/
theorem bdd_slabKer [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hw : WMeas w) {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ}
    (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2)) {B : ℝ}
    (hGb : ∀ V A, |G V A| ≤ B) : Bdd (slabKer μ ν w m G) := by
  have h := measurable_slabKer (μ := μ) (ν := ν) hw m (P := Unit) (G := fun _ => G)
    (hG.comp measurable_snd)
  exact ⟨h.comp ((measurable_const : Measurable (fun _ : X × X => ())).prodMk measurable_id),
    C ^ (m + 1) * B, abs_slabKer_le hwb m hGb⟩

/-- **The slab kernel is bounded by the transfer power**: for nonnegative weights and `|G| ≤ B`,
`|slabKer m G(x, z)| ≤ B k^{∗(m+1)}(x, z)`, `k = HiddenChain.kern ν w`.

DERIVED: `1` is the offset of `iter`; `0` the sign of the weights. -/
theorem slabKer_le_iter [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hw : WMeas w) {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) (hw0 : ∀ x a y, 0 ≤ w x a y) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ}, (∀ V A, |G V A| ≤ B) →
      ∀ x z, |slabKer μ ν w m G x z| ≤ B * iter μ (kern ν w) m x z
  | 0, G, B, hG, x, z => by
    show |∫ a, w x a z * G (scons x (fun _ => z)) (scons a (fun _ => Classical.arbitrary Y)) ∂ν|
      ≤ B * ∫ a, w x a z ∂ν
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le
      ((integrable_of_bdd (measurable_w_mid hw x z) (fun a => hwb x a z)).const_mul B)
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x a z), mul_comm B]
    exact mul_le_mul_of_nonneg_left (hG _ _) (hw0 x a z)
  | m + 1, G, B, hG, x, z => by
    have hk := bdd_kern (ν := ν) hw hwb
    have hki := hk.iter (μ := μ) m
    obtain ⟨Ci, hCi⟩ := hki.bdd
    obtain ⟨Ck, hCk⟩ := hk.bdd
    show |∫ y, ∫ a, w x a y * slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z ∂ν ∂μ|
      ≤ B * ∫ y, kern ν w x y * iter μ (kern ν w) m y z ∂μ
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le
      (integrable_of_bdd (measurable_const.mul ((hk.row x).mul (hki.col z)))
        (C := |B| * (Ck * Ci)) (fun y => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_mul_le_of (hCk x y) (hCi y z)) (abs_nonneg _)))
      (Filter.Eventually.of_forall fun y => ?_)
    have e : B * (kern ν w x y * iter μ (kern ν w) m y z)
        = ∫ a, w x a y * (B * iter μ (kern ν w) m y z) ∂ν := by
      rw [integral_mul_const]; simp only [kern]; ring
    rw [e]
    refine norm_integral_le_of_norm_le
      ((integrable_of_bdd (measurable_w_mid hw x y) (fun a => hwb x a y)).mul_const _)
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x a y)]
    exact mul_le_mul_of_nonneg_left
      (slabKer_le_iter hw hwb hw0 m (G := fun V A => G (scons x V) (scons a A))
        (fun V A => hG _ _) y z) (hw0 x a y)

/-- **The slab kernel of the trivial insertion is the transfer power**:
`slabKer m 1 = k^{∗(m+1)}`.

DERIVED: `1` is the trivial insertion and the offset of `iter`. -/
theorem slabKer_one : ∀ m : ℕ, slabKer μ ν w m (fun _ _ => 1) = iter μ (kern ν w) m
  | 0 => by
    funext x z
    simp only [slabKer, mul_one]
    rfl
  | m + 1 => by
    funext x z
    show ∫ y, ∫ a, w x a y * slabKer μ ν w m (fun _ _ => 1) y z ∂ν ∂μ
      = conv μ (kern ν w) (iter μ (kern ν w) m) x z
    rw [slabKer_one m]
    simp only [conv, kern]
    congr 1; funext y
    rw [integral_mul_const]

/-- **A chain with an insertion and a function of its end point is the slab kernel applied to the
function**: `chain (m+1) (G · g(V_{m+1})) x = ∫ slabKer m G(x, z) g(z) dz`. By induction, with two
Fubini swaps per step (`measurable_slabKer`, `abs_slabKer_le`).

DERIVED: `1` is the offset of the number of steps. -/
theorem chain_slab [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hw : WMeas w) {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ}, Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2) →
      ∀ {B : ℝ}, (∀ V A, |G V A| ≤ B) → ∀ {g : X → ℝ}, Measurable g → ∀ {Bg : ℝ},
      (∀ x, |g x| ≤ Bg) → ∀ x, chain μ ν w (m + 1) (fun V A => G V A * g (V (m + 1))) x
        = ∫ z, slabKer μ ν w m G x z * g z ∂μ
  | 0, G, _, B, _, g, _, Bg, _, x => by
    show ∫ y, ∫ a, w x a y * (G (scons x (fun _ => y)) (scons a (fun _ => Classical.arbitrary Y))
        * g y) ∂ν ∂μ
      = ∫ z, (∫ a, w x a z * G (scons x (fun _ => z))
          (scons a (fun _ => Classical.arbitrary Y)) ∂ν) * g z ∂μ
    congr 1; funext y
    rw [← integral_mul_const]; congr 1; funext a; ring
  | m + 1, G, hG, B, hGb, g, hg, Bg, hgb, x => by
    have hGa : Measurable (fun q : Y × (ℕ → X) × (ℕ → Y) => G (scons x q.2.1) (scons q.1 q.2.2)) :=
      hG.comp ((measurable_scons.comp (measurable_const.prodMk measurable_snd.fst)).prodMk
        (measurable_scons.comp (measurable_fst.prodMk measurable_snd.snd)))
    have hS := measurable_slabKer (μ := μ) (ν := ν) hw m (P := Y)
      (G := fun a V A => G (scons x V) (scons a A)) hGa
    have hSb : ∀ a y z, |slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z|
        ≤ C ^ (m + 1) * B := fun a y z => abs_slabKer_le hwb m (fun V A => hGb _ _) y z
    have hGa' : ∀ a, Measurable (fun q : (ℕ → X) × (ℕ → Y) => G (scons x q.1) (scons a q.2)) :=
      fun a => hG.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))
    have e : ∀ y a, chain μ ν w (m + 1)
        (fun V A => G (scons x V) (scons a A) * g (scons x V (m + 1 + 1))) y
        = ∫ z, slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z ∂μ :=
      fun y a => chain_slab hw hwb m (hGa' a) (fun V A => hGb _ _) hg hgb y
    show ∫ y, ∫ a, w x a y * chain μ ν w (m + 1)
        (fun V A => G (scons x V) (scons a A) * g (scons x V (m + 1 + 1))) y ∂ν ∂μ
      = ∫ z, (∫ y, ∫ a, w x a y * slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z
          ∂ν ∂μ) * g z ∂μ
    simp_rw [e]
    have hF1 : ∀ y, Measurable (Function.uncurry (fun a z => w x a y
        * (slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z))) := fun y =>
      ((measurable_w_mid hw x y).comp measurable_fst).mul
        ((hS.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).mul
          (hg.comp measurable_snd))
    have hb1 : ∀ y a z, |w x a y
        * (slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z)|
        ≤ C * (C ^ (m + 1) * B * Bg) := fun y a z =>
      abs_mul_le_of (hwb x a y) (abs_mul_le_of (hSb a y z) (hgb z))
    have hF2 : Measurable (Function.uncurry (fun y z => ∫ a, w x a y
        * (slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z) ∂ν)) := by
      have h : Measurable (fun r : (X × X) × Y => w x r.2 r.1.1
          * (slabKer μ ν w m (fun V A => G (scons x V) (scons r.2 A)) r.1.1 r.1.2 * g r.1.2)) :=
        (hw.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst.fst))).mul
          ((hS.comp (measurable_snd.prodMk (measurable_fst.fst.prodMk measurable_fst.snd))).mul
            (hg.comp measurable_fst.snd))
      exact (h.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    calc ∫ y, ∫ a, w x a y
          * ∫ z, slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z ∂μ ∂ν ∂μ
        = ∫ y, ∫ a, ∫ z, w x a y
            * (slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z) ∂μ ∂ν ∂μ := by
          congr 1; funext y; congr 1; funext a; rw [integral_const_mul]
      _ = ∫ y, ∫ z, ∫ a, w x a y
            * (slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z) ∂ν ∂μ ∂μ := by
          congr 1; funext y; exact swap2 (hF1 y) (hb1 y)
      _ = ∫ z, ∫ y, ∫ a, w x a y
            * (slabKer μ ν w m (fun V A => G (scons x V) (scons a A)) y z * g z) ∂ν ∂μ ∂μ :=
          swap_bdd hF2 (C := C * (C ^ (m + 1) * B * Bg))
            (fun y z => abs_integral_le fun a => hb1 y a z)
      _ = _ := by
          congr 1; funext z
          rw [← integral_mul_const]; congr 1; funext y
          rw [← integral_mul_const]; congr 1; funext a; ring

/-- **The trace identity on the chain for two slab insertions**: with `f` reading `m + 2` slices
and their `m + 1` hidden variables from slice `0`, `g` reading `m' + 2` slices from slice
`s = m + 1 + p + 1`, on the closed chain of `L = s + m' + 1 + q + 1` steps,
`∫ chain(f · g∘shift_s · k(V_{L−1}, x)) dx = Tr(F̂ K^{p+1} Ĝ K^{q+1})` with `F̂ = slabKer m f`,
`Ĝ = slabKer m' g`. `HiddenChain.chain_split` at `s`, at `m' + 1` and at `m + 1`,
`HiddenChain.chain_end_kern`, `HiddenChain.chain_end_iter` and `chain_slab`.

DERIVED: `1` and `2` are the offsets of `iter` and of the slab widths `m + 1`, `m' + 1`. -/
theorem chain_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hw : WMeas w) {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) {f g : (ℕ → X) → (ℕ → Y) → ℝ}
    (hfm : Measurable (fun r : (ℕ → X) × (ℕ → Y) => f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → X) × (ℕ → Y) => g r.1 r.2)) {Bf Bg : ℝ}
    (hfb : ∀ V A, |f V A| ≤ Bf) (hgb : ∀ V A, |g V A| ≤ Bg) {m m' p q : ℕ}
    (hf : LocalUpTo (m + 1) f) (hg : LocalUpTo (m' + 1) g) :
    ∫ x, chain μ ν w (m + 1 + (p + 1) + (m' + 1 + q))
        (fun V A => f V A * g (sshift V (m + 1 + (p + 1))) (sshift A (m + 1 + (p + 1)))
          * kern ν w (V (m + 1 + (p + 1) + (m' + 1 + q))) x) x ∂μ
      = trK μ (kern ν w) (slabKer μ ν w m f) (slabKer μ ν w m' g) p q := by
  have hk := bdd_kern (ν := ν) hw hwb
  have hF := bdd_slabKer (μ := μ) (ν := ν) hw hwb m hfm hfb
  have hG := bdd_slabKer (μ := μ) (ν := ν) hw hwb m' hgm hgb
  have hKp := hk.iter (μ := μ) p
  have hKq := hk.iter (μ := μ) q
  obtain ⟨Cq, hCq⟩ := hKq.bdd
  have hGKq : Bdd (conv μ (slabKer μ ν w m' g) (iter μ (kern ν w) q)) := hG.conv hKq
  obtain ⟨CN, hCN⟩ := hGKq.bdd
  have hN : Bdd (conv μ (iter μ (kern ν w) p)
      (conv μ (slabKer μ ν w m' g) (iter μ (kern ν w) q))) := hKp.conv hGKq
  obtain ⟨CN', hCN'⟩ := hN.bdd
  unfold trK trc
  congr 1; funext x
  have hB : ∀ y, chain μ ν w (m' + 1 + q) (fun V A => g V A * kern ν w (V (m' + 1 + q)) x) y
      = conv μ (slabKer μ ν w m' g) (iter μ (kern ν w) q) y x := by
    intro y
    have hs := chain_split (μ := μ) (ν := ν) (w := w) (m' + 1) q (G1 := g)
      (fun V (_ : ℕ → Y) => kern ν w (V q) x) y hg
    refine (chain_congr (m' + 1 + q) (fun V A _ => ?_)).trans (hs.trans ?_)
    · show g V A * kern ν w (V (m' + 1 + q)) x = g V A * kern ν w (V (q + (m' + 1))) x
      rw [Nat.add_comm q (m' + 1)]
    · simp_rw [chain_end_kern x q]
      exact chain_slab hw hwb m' hgm hgb (hKq.col x) (fun z => hCq z x) y
  have hs1 := chain_split (μ := μ) (ν := ν) (w := w) (m + 1 + (p + 1)) (m' + 1 + q) (G1 := f)
    (fun V A => g V A * kern ν w (V (m' + 1 + q)) x) x (hf.mono (by omega))
  refine (chain_congr _ (fun V A _ => ?_)).trans (hs1.trans ?_)
  · show f V A * g (sshift V (m + 1 + (p + 1))) (sshift A (m + 1 + (p + 1)))
        * kern ν w (V (m + 1 + (p + 1) + (m' + 1 + q))) x
      = f V A * (g (sshift V (m + 1 + (p + 1))) (sshift A (m + 1 + (p + 1)))
        * kern ν w (V (m' + 1 + q + (m + 1 + (p + 1)))) x)
    rw [Nat.add_comm (m' + 1 + q) (m + 1 + (p + 1)), mul_assoc]
  · simp_rw [hB]
    have hs2 := chain_split (μ := μ) (ν := ν) (w := w) (m + 1) (p + 1) (G1 := f)
      (fun V (_ : ℕ → Y) => conv μ (slabKer μ ν w m' g) (iter μ (kern ν w) q) (V (p + 1)) x) x hf
    refine (chain_congr _ (fun V A _ => ?_)).trans (hs2.trans ?_)
    · show f V A * conv μ (slabKer μ ν w m' g) (iter μ (kern ν w) q) (V (m + 1 + (p + 1))) x
        = f V A * conv μ (slabKer μ ν w m' g) (iter μ (kern ν w) q) (V (p + 1 + (m + 1))) x
      rw [Nat.add_comm (p + 1) (m + 1)]
    · simp_rw [chain_end_iter hw hwb (hGKq.col x) (fun z => hCN z x) p]
      rw [← conv_assoc hF hKp hGKq]
      exact chain_slab hw hwb m hfm hfb (hN.col x) (fun z => hCN' z x) x

end SlabChain

section TraceOne

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ}

/-- **A transfer power in the second slot closes the trace**:
`Tr(F K^{p+1} K^{m'+1} K^{q+1}) = Tr(F K^{p+m'+q+3})`.

DERIVED: `1` is the offset of `iter`. -/
theorem trK_iter_right (hk : Bdd k) {F : X → X → ℝ} (hF : Bdd F) (m' p q : ℕ) :
    trK μ k F (iter μ k m') p q = trOne μ k F (p + (m' + q + 1) + 1) := by
  unfold trK trOne
  rw [← iter_add hk m' q, ← conv_assoc hF (hk.iter (μ := μ) p) (hk.iter (μ := μ) (m' + q + 1)),
    ← iter_add hk p (m' + q + 1)]

/-- **A transfer power in the first slot closes the trace**, by cyclicity:
`Tr(K^{m+1} K^{p+1} G K^{q+1}) = Tr(G K^{q+m+p+3})`.

DERIVED: `1` is the offset of `iter`. -/
theorem trK_iter_left (hk : Bdd k) {G : X → X → ℝ} (hG : Bdd G) (m p q : ℕ) :
    trK μ k (iter μ k m) G p q = trOne μ k G (q + (m + p + 1) + 1) := by
  unfold trK trOne
  rw [← iter_add hk m p,
    trc_conv_comm (hk.iter (μ := μ) (m + p + 1)) (hG.conv (μ := μ) (hk.iter (μ := μ) q)),
    ← conv_assoc hG (hk.iter (μ := μ) q) (hk.iter (μ := μ) (m + p + 1)),
    ← iter_add hk q (m + p + 1)]

end TraceOne

/-! ## 5. Slab observables on the Wilson torus -/

section SlabTorus

open MassGap.RectWilson MassGap.RectTransfer MassGap.RectTorusState MassGap.CompactGauge
  MassGap.HiddenChain

/-- **The spatial links of the slices of a slab**: `slabV L μ t U i` is slice `t + i` along `μ`
of the configuration `U` (`OpenAIBridgeUniform.spSlice`), and the identity beyond the torus.

DERIVED: `4` is the spacetime dimension; `1` the identity of the group. -/
def slabV {Gr : Type} [One Gr] (L : Fin 4 → ℕ) (μ : Fin 4) (t : ℕ) (U : RLink L → Gr) :
    ℕ → SpIdx L μ → Gr :=
  fun i => if h : t + i < L μ then fun l => U (l.1.1, join L μ ⟨t + i, h⟩ l.2) else fun _ => 1

/-- **The time links of a slab**: `slabA L μ t U i` is the axis link from slice `t + i` to the next,
at every transverse site, and the identity beyond the torus.

DERIVED: `4` is the spacetime dimension; `1` the identity of the group. -/
def slabA {Gr : Type} [One Gr] (L : Fin 4 → ℕ) (μ : Fin 4) (t : ℕ) (U : RLink L → Gr) :
    ℕ → TS L μ → Gr :=
  fun i => if h : t + i < L μ then fun y => U (μ, join L μ ⟨t + i, h⟩ y) else fun _ => 1

/-- `slabV L μ t` is measurable.

DERIVED: `4` is the spacetime dimension. -/
theorem measurable_slabV {Gr : Type} [One Gr] [MeasurableSpace Gr] (L : Fin 4 → ℕ) (μ : Fin 4)
    (t : ℕ) : Measurable (slabV (Gr := Gr) L μ t) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : t + i < L μ
  · simp only [slabV, dif_pos h]; exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
  · simp only [slabV, dif_neg h]; exact measurable_const

/-- `slabA L μ t` is measurable.

DERIVED: `4` is the spacetime dimension. -/
theorem measurable_slabA {Gr : Type} [One Gr] [MeasurableSpace Gr] (L : Fin 4 → ℕ) (μ : Fin 4)
    (t : ℕ) : Measurable (slabA (Gr := Gr) L μ t) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : t + i < L μ
  · simp only [slabA, dif_pos h]; exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
  · simp only [slabA, dif_neg h]; exact measurable_const

/-- A `Fin`-indexed sequence of hidden variables extended to `ℕ` reads its entries.

DERIVED: no numeral appears in the statement. -/
theorem extY_apply {Y : Type} [MeasurableSpace Y] [Nonempty Y] {m : ℕ} (A : Fin m → Y) {i : ℕ}
    (hi : i < m) : extY A i = A ⟨i, hi⟩ := by
  simp only [extY]
  rw [dif_pos hi]

variable {N : ℕ}

/-- On a configuration assembled from slices, the slab slices are the slices:
`slabV L μ t (Φ (joinR A V)) i = V (t + i)` (`OpenAIBridgeUniform.spSlice_joinR`).

DERIVED: no numeral appears in the statement. -/
theorem slabV_joinR {L : Fin 4 → ℕ} {μ : Fin 4} (A : Fin (L μ) → AxR μ (tr L μ) N)
    (V : Fin (L μ) → SlR μ (tr L μ) N) (t i : ℕ) (h : t + i < L μ) :
    slabV L μ t (Φ L μ (joinR A V)) i = V ⟨t + i, h⟩ := by
  simp only [slabV, dif_pos h]
  exact spSlice_joinR A V ⟨t + i, h⟩

/-- On a configuration assembled from slices, the slab time links are the hidden variables:
`slabA L μ t (Φ (joinR A V)) i = A (t + i)` (`RectWilson.Φ_axis`).

DERIVED: no numeral appears in the statement. -/
theorem slabA_joinR {L : Fin 4 → ℕ} {μ : Fin 4} (A : Fin (L μ) → AxR μ (tr L μ) N)
    (V : Fin (L μ) → SlR μ (tr L μ) N) (t i : ℕ) (h : t + i < L μ) :
    slabA L μ t (Φ L μ (joinR A V)) i = A ⟨t + i, h⟩ := by
  funext y
  simp only [slabA, dif_pos h]
  exact Φ_axis (joinR A V) ⟨t + i, h⟩ y

/-- **The Wilson correlation numerator of two slab observables is the trace of their slab
kernels.** On the rectangular torus with time extent `L μ = m + 1 + (p + 1) + (m' + 1 + q) + 1`,
for bounded measurable `f`, `g` of a sequence of slices and time links, `f` reading slices
`0, …, m + 1` and the time links between them (`HiddenChain.LocalUpTo (m + 1)`), `g` likewise up
to `m' + 1`, read at times `0` and `s = m + 1 + p + 1`,
`∫ f(U|_{[0, m+1]}) g(U|_{[s, s+m'+1]}) e^{−β S(U)} dU = Tr(F̂ K^{p+1} Ĝ K^{q+1})`, `F̂ = slabKer m f`,
`Ĝ = slabKer m' g` over the step weight `wtR`. It is `RectTorusState.corrNumR` and `chain_two`; the
slab analogue of `OpenAIBridgeUniform.corrNum_slab`.

DERIVED: `0` is the first slice; `1` and `2` the offsets of the widths and of `iter`, so the time
extent is `m + m' + p + q + 5`. -/
theorem corrNum_slabK (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ} {μ : Fin 4}
    {m m' p q : ℕ} (hL : L μ = m + 1 + (p + 1) + (m' + 1 + q) + 1)
    {f g : (ℕ → SlR μ (tr L μ) N) → (ℕ → AxR μ (tr L μ) N) → ℝ}
    (hfm : Measurable (fun r : (ℕ → SlR μ (tr L μ) N) × (ℕ → AxR μ (tr L μ) N) => f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → SlR μ (tr L μ) N) × (ℕ → AxR μ (tr L μ) N) => g r.1 r.2))
    {Bf Bg : ℝ} (hfb : ∀ V A, |f V A| ≤ Bf) (hgb : ∀ V A, |g V A| ≤ Bg)
    (hf : LocalUpTo (m + 1) f) (hg : LocalUpTo (m' + 1) g) :
    (sysR L N).corrNum (probHaar (SUN.SU N)) β
        (fun U => f (slabV L μ 0 U) (slabA L μ 0 U)
          * g (slabV L μ (m + 1 + (p + 1)) U) (slabA L μ (m + 1 + (p + 1)) U))
      = trK (hS μ (tr L μ) N) (kT μ (tr L μ) N β)
          (slabKer (hS μ (tr L μ) N) (hA μ (tr L μ) N) (wtR μ (tr L μ) N β) m f)
          (slabKer (hS μ (tr L μ) N) (hA μ (tr L μ) N) (wtR μ (tr L μ) N β) m' g) p q := by
  have hO : Measurable (fun U : RLink L → SUN.SU N => f (slabV L μ 0 U) (slabA L μ 0 U)
      * g (slabV L μ (m + 1 + (p + 1)) U) (slabA L μ (m + 1 + (p + 1)) U)) :=
    (hfm.comp ((measurable_slabV L μ 0).prodMk (measurable_slabA L μ 0))).mul
      (hgm.comp ((measurable_slabV L μ _).prodMk (measurable_slabA L μ _)))
  have hFm : Measurable (fun r : (ℕ → SlR μ (tr L μ) N) × (ℕ → AxR μ (tr L μ) N) =>
      f r.1 r.2 * g (sshift r.1 (m + 1 + (p + 1))) (sshift r.2 (m + 1 + (p + 1)))) :=
    hfm.mul (hgm.comp (((measurable_sshift _).comp measurable_fst).prodMk
      ((measurable_sshift _).comp measurable_snd)))
  refine (corrNumR hN hβ hL hO (BO := Bf * Bg) (fun U => abs_mul_le_of (hfb _ _) (hgb _ _))
    (F := fun V A => f V A * g (sshift V (m + 1 + (p + 1))) (sshift A (m + 1 + (p + 1)))) hFm
    (BF := Bf * Bg) (fun V A => abs_mul_le_of (hfb _ _) (hgb _ _)) ?_).trans ?_
  · intro A V
    show f _ _ * g _ _ = f _ _ * g _ _
    congr 1
    · apply hf
      · intro i hi
        rw [slabV_joinR A V 0 i (by omega),
          extX_apply _ (show i < m + 1 + (p + 1) + (m' + 1 + q) + 1 by omega)]
        exact congrArg V (Fin.ext (Nat.zero_add i))
      · intro i hi
        rw [slabA_joinR A V 0 i (by omega),
          extY_apply _ (show i < m + 1 + (p + 1) + (m' + 1 + q) by omega)]
        exact congrArg A (Fin.ext (Nat.zero_add i))
    · apply hg
      · intro i hi
        show _ = extX _ (i + (m + 1 + (p + 1)))
        rw [slabV_joinR A V (m + 1 + (p + 1)) i (by omega),
          extX_apply _ (show i + (m + 1 + (p + 1)) < m + 1 + (p + 1) + (m' + 1 + q) + 1 by omega)]
        exact congrArg V (Fin.ext (Nat.add_comm _ _))
      · intro i hi
        show _ = extY _ (i + (m + 1 + (p + 1)))
        rw [slabA_joinR A V (m + 1 + (p + 1)) i (by omega),
          extY_apply _ (show i + (m + 1 + (p + 1)) < m + 1 + (p + 1) + (m' + 1 + q) by omega)]
        exact congrArg A (Fin.ext (Nat.add_comm _ _))
  · unfold ZcR
    rw [← kern_wtR β]
    exact chain_two (wmeas_wtR β) (abs_wtR_le hN hβ) hfm hgm hfb hgb hf hg

/-- **The connected trace ratio of two slab kernels is the connected Wilson correlation of the
slab observables** (`OpenAIBridgeUniform.connTorus_eq_expect` for slabs): on the rectangular torus
with `L 0 = m + 1 + (p + 1) + (m' + 1 + q) + 1`,
`connK F̂ Ĝ (m+1) (m'+1) p q = ⟨f_0 g_s⟩ − ⟨f_0⟩⟨g_s⟩`, `s = m + 1 + p + 1`. Numerators by
`corrNum_slabK` (with `1` for the absent insertion, `slabKer_one`, `trK_iter_right`,
`trK_iter_left`), the partition function by `OpenAIBridgeCluster.ZR_eq_trPow`.

DERIVED: `0` is the time direction and the first slice; `1` and `2` the offsets of the widths and
of `iter`. -/
theorem connK_eq_expect_slab (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ}
    {m m' p q : ℕ} (hL : L 0 = m + 1 + (p + 1) + (m' + 1 + q) + 1)
    {f g : (ℕ → SlR 0 (tr L 0) N) → (ℕ → AxR 0 (tr L 0) N) → ℝ}
    (hfm : Measurable (fun r : (ℕ → SlR 0 (tr L 0) N) × (ℕ → AxR 0 (tr L 0) N) => f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → SlR 0 (tr L 0) N) × (ℕ → AxR 0 (tr L 0) N) => g r.1 r.2))
    {Bf Bg : ℝ} (hfb : ∀ V A, |f V A| ≤ Bf) (hgb : ∀ V A, |g V A| ≤ Bg)
    (hf : LocalUpTo (m + 1) f) (hg : LocalUpTo (m' + 1) g) :
    connK (hS 0 (tr L 0) N) (kT 0 (tr L 0) N β)
        (slabKer (hS 0 (tr L 0) N) (hA 0 (tr L 0) N) (wtR 0 (tr L 0) N β) m f)
        (slabKer (hS 0 (tr L 0) N) (hA 0 (tr L 0) N) (wtR 0 (tr L 0) N β) m' g) (m + 1) (m' + 1) p q
      = (sysR L N).expect (probHaar (SUN.SU N)) β
          (fun U => f (slabV L 0 0 U) (slabA L 0 0 U)
            * g (slabV L 0 (m + 1 + (p + 1)) U) (slabA L 0 (m + 1 + (p + 1)) U))
        - (sysR L N).expect (probHaar (SUN.SU N)) β (fun U => f (slabV L 0 0 U) (slabA L 0 0 U))
          * (sysR L N).expect (probHaar (SUN.SU N)) β
            (fun U => g (slabV L 0 (m + 1 + (p + 1)) U) (slabA L 0 (m + 1 + (p + 1)) U)) := by
  have hk := bdd_kT (μ := 0) (T := tr L 0) hN hβ
  have hw := wmeas_wtR (μ := 0) (T := tr L 0) (N := N) β
  have hwb := abs_wtR_le (μ := 0) (T := tr L 0) hN hβ
  have h2 := corrNum_slabK hN hβ hL hfm hgm hfb hgb hf hg
  have h1 := corrNum_slabK hN hβ hL hfm (g := fun _ _ => (1 : ℝ)) measurable_const hfb
    (fun _ _ => abs_one.le) hf (localUpTo_const _ 1)
  have h3 := corrNum_slabK hN hβ hL (f := fun _ _ => (1 : ℝ)) measurable_const hgm
    (fun _ _ => abs_one.le) hgb (localUpTo_const _ 1) hg
  simp only [mul_one] at h1
  simp only [one_mul] at h3
  rw [slabKer_one, kern_wtR, trK_iter_right (μ := hS 0 (tr L 0) N) hk
      (bdd_slabKer (μ := hS 0 (tr L 0) N) (ν := hA 0 (tr L 0) N) hw hwb m hfm hfb),
    show p + (m' + q + 1) + 1 = p + q + (m' + 1) + 1 by omega] at h1
  rw [slabKer_one, kern_wtR, trK_iter_left (μ := hS 0 (tr L 0) N) hk
      (bdd_slabKer (μ := hS 0 (tr L 0) N) (ν := hA 0 (tr L 0) N) hw hwb m' hgm hgb),
    show q + (m + p + 1) + 1 = p + q + (m + 1) + 1 by omega] at h3
  have hZ : (sysR L N).partition (probHaar (SUN.SU N)) β
      = trPow (hS 0 (tr L 0) N) (kT 0 (tr L 0) N β) (p + q + (m + 1) + (m' + 1) + 1) :=
    ZR_eq_trPow hN hβ L _ (by omega)
  unfold connK LatticeGauge.System.expect
  rw [h2, h1, h3, hZ]

end SlabTorus


section SlabTorusG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.OpenAIBridgeGroups

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- On a configuration of the cubic torus of `G` assembled from slices, the slab slices are the
slices (`RectWilsonG.ΦG_sp`).

DERIVED: `0` is the slicing direction; `1` the successor of the extent `M + 1`. -/
theorem slabV_joinWG {M : ℕ} (A : Fin (M + 1) → TorusChainG.AxG G M)
    (V : Fin (M + 1) → TorusChainG.SlG G M) (t i : ℕ) (h : t + i < M + 1) :
    slabV (TorusChain.Lc M) 0 t (ΦG (TorusChain.Lc M) 0 (TorusChainG.joinWG A V)) i
      = V ⟨t + i, h⟩ := by
  funext l
  simp only [slabV, dif_pos (show t + i < TorusChain.Lc M 0 from h)]
  exact ΦG_sp (TorusChainG.joinWG A V) ⟨t + i, h⟩ l.2 l.1

/-- On a configuration of the cubic torus of `G` assembled from slices, the slab time links are
the hidden variables (`RectWilsonG.ΦG_axis`).

DERIVED: `0` is the slicing direction; `1` the successor of the extent `M + 1`. -/
theorem slabA_joinWG {M : ℕ} (A : Fin (M + 1) → TorusChainG.AxG G M)
    (V : Fin (M + 1) → TorusChainG.SlG G M) (t i : ℕ) (h : t + i < M + 1) :
    slabA (TorusChain.Lc M) 0 t (ΦG (TorusChain.Lc M) 0 (TorusChainG.joinWG A V)) i
      = A ⟨t + i, h⟩ := by
  funext y
  simp only [slabA, dif_pos (show t + i < TorusChain.Lc M 0 from h)]
  exact ΦG_axis (TorusChainG.joinWG A V) ⟨t + i, h⟩ y

/-- **The Wilson correlation numerator of two slab observables of `G` is the trace of their slab
kernels** (`corrNum_slabK` over `G`, on the cubic torus of side `M + 1`). It is
`TorusChainG.corrNum_eqG` and `chain_two`.

DERIVED: `0` is the time direction and the first slice; `1` and `2` the offsets of the widths and
of `iter`. -/
theorem corrNum_slabKG {β : ℝ} (hβ : 0 ≤ β) {M m m' p q : ℕ}
    (hM : M = m + 1 + (p + 1) + (m' + 1 + q))
    {f g : (ℕ → TorusChainG.SlG G M) → (ℕ → TorusChainG.AxG G M) → ℝ}
    (hfm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      g r.1 r.2))
    {Bf Bg : ℝ} (hfb : ∀ V A, |f V A| ≤ Bf) (hgb : ∀ V A, |g V A| ≤ Bg)
    (hf : LocalUpTo (m + 1) f) (hg : LocalUpTo (m' + 1) g) :
    (sysRG G (TorusChain.Lc M)).corrNum (probHaar G) β
        (fun U => f (slabV (TorusChain.Lc M) 0 0 U) (slabA (TorusChain.Lc M) 0 0 U)
          * g (slabV (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U)
            (slabA (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U))
      = trK (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β)
          (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
            (TorusChainG.wtG G M β) m f)
          (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
            (TorusChainG.wtG G M β) m' g) p q := by
  subst hM
  have hO : Measurable (fun U : RLink (TorusChain.Lc (m + 1 + (p + 1) + (m' + 1 + q))) → G =>
      f (slabV (TorusChain.Lc (m + 1 + (p + 1) + (m' + 1 + q))) 0 0 U)
        (slabA (TorusChain.Lc (m + 1 + (p + 1) + (m' + 1 + q))) 0 0 U)
      * g (slabV (TorusChain.Lc (m + 1 + (p + 1) + (m' + 1 + q))) 0 (m + 1 + (p + 1)) U)
        (slabA (TorusChain.Lc (m + 1 + (p + 1) + (m' + 1 + q))) 0 (m + 1 + (p + 1)) U)) :=
    (hfm.comp ((measurable_slabV _ 0 0).prodMk (measurable_slabA _ 0 0))).mul
      (hgm.comp ((measurable_slabV _ 0 _).prodMk (measurable_slabA _ 0 _)))
  have hFm : Measurable (fun r : (ℕ → TorusChainG.SlG G (m + 1 + (p + 1) + (m' + 1 + q)))
      × (ℕ → TorusChainG.AxG G (m + 1 + (p + 1) + (m' + 1 + q))) =>
      f r.1 r.2 * g (sshift r.1 (m + 1 + (p + 1))) (sshift r.2 (m + 1 + (p + 1)))) :=
    hfm.mul (hgm.comp (((measurable_sshift _).comp measurable_fst).prodMk
      ((measurable_sshift _).comp measurable_snd)))
  refine (TorusChainG.corrNum_eqG hβ hO (BO := Bf * Bg)
    (fun U => abs_mul_le_of (hfb _ _) (hgb _ _))
    (F := fun V A => f V A * g (sshift V (m + 1 + (p + 1))) (sshift A (m + 1 + (p + 1)))) hFm
    (BF := Bf * Bg) (fun V A => abs_mul_le_of (hfb _ _) (hgb _ _)) ?_).trans ?_
  · intro A V
    show f _ _ * g _ _ = f _ _ * g _ _
    congr 1
    · apply hf
      · intro i hi
        rw [slabV_joinWG A V 0 i (by omega),
          extX_apply V (show i < m + 1 + (p + 1) + (m' + 1 + q) + 1 by omega)]
        exact congrArg V (Fin.ext (Nat.zero_add i))
      · intro i hi
        rw [slabA_joinWG A V 0 i (by omega),
          extY_apply _ (show i < m + 1 + (p + 1) + (m' + 1 + q) by omega)]
        exact congrArg A (Fin.ext (Nat.zero_add i))
    · apply hg
      · intro i hi
        show _ = extX V (i + (m + 1 + (p + 1)))
        rw [slabV_joinWG A V (m + 1 + (p + 1)) i (by omega),
          extX_apply V
            (show i + (m + 1 + (p + 1)) < m + 1 + (p + 1) + (m' + 1 + q) + 1 by omega)]
        exact congrArg V (Fin.ext (Nat.add_comm _ _))
      · intro i hi
        show _ = extY _ (i + (m + 1 + (p + 1)))
        rw [slabA_joinWG A V (m + 1 + (p + 1)) i (by omega),
          extY_apply _ (show i + (m + 1 + (p + 1)) < m + 1 + (p + 1) + (m' + 1 + q) by omega)]
        exact congrArg A (Fin.ext (Nat.add_comm _ _))
  · unfold TorusChainG.ZcG
    rw [← TorusChainG.kern_wtG β]
    exact chain_two (TorusChainG.wmeas_wtG β) (TorusChainG.abs_wtG_le hβ) hfm hgm hfb hgb hf hg

/-- **The connected trace ratio of two slab kernels of `G` is the connected Wilson correlation of
the slab observables** (`connK_eq_expect_slab` over `G`, on the cubic torus of side `M + 1`).

DERIVED: `0` is the time direction and the first slice; `1` and `2` the offsets of the widths and
of `iter`. -/
theorem connK_eq_expect_slabG {β : ℝ} (hβ : 0 ≤ β) {M m m' p q : ℕ}
    (hM : M = m + 1 + (p + 1) + (m' + 1 + q))
    {f g : (ℕ → TorusChainG.SlG G M) → (ℕ → TorusChainG.AxG G M) → ℝ}
    (hfm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → TorusChainG.SlG G M) × (ℕ → TorusChainG.AxG G M) =>
      g r.1 r.2))
    {Bf Bg : ℝ} (hfb : ∀ V A, |f V A| ≤ Bf) (hgb : ∀ V A, |g V A| ≤ Bg)
    (hf : LocalUpTo (m + 1) f) (hg : LocalUpTo (m' + 1) g) :
    connK (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β)
        (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
          (TorusChainG.wtG G M β) m f)
        (slabKer (hSG G 0 (TorusChain.Tc M)) (hAG G 0 (TorusChain.Tc M))
          (TorusChainG.wtG G M β) m' g) (m + 1) (m' + 1) p q
      = (sysRG G (TorusChain.Lc M)).expect (probHaar G) β
          (fun U => f (slabV (TorusChain.Lc M) 0 0 U) (slabA (TorusChain.Lc M) 0 0 U)
            * g (slabV (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U)
              (slabA (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U))
        - (sysRG G (TorusChain.Lc M)).expect (probHaar G) β
            (fun U => f (slabV (TorusChain.Lc M) 0 0 U) (slabA (TorusChain.Lc M) 0 0 U))
          * (sysRG G (TorusChain.Lc M)).expect (probHaar G) β
            (fun U => g (slabV (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U)
              (slabA (TorusChain.Lc M) 0 (m + 1 + (p + 1)) U)) := by
  have hk := bdd_kTG (G := G) (μ := 0) (T := TorusChain.Tc M) hβ
  have hw := TorusChainG.wmeas_wtG (G := G) (M := M) β
  have hwb := TorusChainG.abs_wtG_le (G := G) (M := M) hβ
  have h2 := corrNum_slabKG hβ hM hfm hgm hfb hgb hf hg
  have h1 := corrNum_slabKG hβ hM hfm (g := fun _ _ => (1 : ℝ)) measurable_const hfb
    (fun _ _ => abs_one.le) hf (localUpTo_const _ 1)
  have h3 := corrNum_slabKG hβ hM (f := fun _ _ => (1 : ℝ)) measurable_const hgm
    (fun _ _ => abs_one.le) hgb (localUpTo_const _ 1) hg
  simp only [mul_one] at h1
  simp only [one_mul] at h3
  rw [slabKer_one, TorusChainG.kern_wtG, trK_iter_right (μ := hSG G 0 (TorusChain.Tc M)) hk
      (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb m
        hfm hfb),
    show p + (m' + q + 1) + 1 = p + q + (m' + 1) + 1 by omega] at h1
  rw [slabKer_one, TorusChainG.kern_wtG, trK_iter_left (μ := hSG G 0 (TorusChain.Tc M)) hk
      (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb m'
        hgm hgb),
    show q + (m + p + 1) + 1 = p + q + (m + 1) + 1 by omega] at h3
  have hZ : (sysRG G (TorusChain.Lc M)).partition (probHaar G) β
      = trPow (hSG G 0 (TorusChain.Tc M)) (kTG G 0 (TorusChain.Tc M) β)
          (p + q + (m + 1) + (m' + 1) + 1) :=
    ZRG_eq_trPowG G hβ _ _ (by show M + 1 = _; omega)
  unfold connK LatticeGauge.System.expect
  rw [h2, h1, h3, hZ]

end SlabTorusG

/-! ## 6. The connected correlation of two slab observables, uniform in the torus -/

section SlabCapstone

open MassGap.RectWilson MassGap.RectTransfer MassGap.RectTorusState MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingRecursion MassGap.DoublingWilson

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **Exponential clustering of two slab observables on the `SU(N)` Wilson torus, uniform in the
torus, from the seed.** If one torus of even side `n ≥ 2` has `16 log Z(n⁴) − log Z((2n)⁴) ≤ 1/1000`
at `β ≥ 0`, then on the cubic torus of every even side `L ≥ 2n`, for bounded measurable functions
`f`, `g` of a sequence of slices and time links (`|f| ≤ A`, `|g| ≤ B`), `f` reading the slices
`0, …, w` and the time links between them, `g` the slices `0, …, w'` (`w = 2v + 2`,
`w' = 2v' + 2`), read at time `0` and at time `w + p + 1` of the time extent
`L = p + q + 2 + w + w'` with `4(w + w') + 8n ≤ L`,

    |⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋),

`⟨·⟩` the Wilson Gibbs expectation. The separations `p + 1`, `q + 1` are counted from the slab
edges. It is `wilson_connK_slab` on the slab kernels (`bdd_slabKer`, `slabKer_le_iter`) read
through `connK_eq_expect_slab`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of `connK_uniform`;
`4` and `8` the slab condition of `excited_le_slab`, and `4` the spacetime dimension; `1/2` the
contraction; `2` the doubled side, the least seed side, the least ratio `L / n`, the doubled widths
and the offsets of `iter`; `0` the time direction, the first slice and the sign of the coupling;
`1` the offsets of `iter` and the separation. -/
theorem wilson_slab_conn
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L)
    (f g : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N) → (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N)
      → ℝ)
    (hfm : Measurable (fun r : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N)
      × (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) => f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → SlR 0 (tr (fun _ : Fin 4 => L) 0) N)
      × (ℕ → AxR 0 (tr (fun _ : Fin 4 => L) 0) N) => g r.1 r.2))
    (A B : ℝ) (hfb : ∀ V A', |f V A'| ≤ A) (hgb : ∀ V A', |g V A'| ≤ B) (v v' : ℕ)
    (hf : LocalUpTo (v + v + 2) f) (hg : LocalUpTo (v' + v' + 2) g) (p q : ℕ)
    (hpq : p + q + 2 + (v + v + 2) + (v' + v' + 2) = L)
    (hW : 4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L) :
    |(sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
        (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U)
          * g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U)
            (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U))
      - (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
          (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U))
        * (sysR (fun _ : Fin 4 => L) N).expect (probHaar (SUN.SU N)) β
          (fun U => g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U)
            (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U))|
      ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨φ, c, hc0, hφ1, heig, hcl⟩ := wilson_connK_slab hN hβ hn he h0 L hLe hL
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
  have h := hcl _ _
    (bdd_slabKer (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N)
      (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := hS 0 (tr (fun _ : Fin 4 => L) 0) N)
      (ν := hA 0 (tr (fun _ : Fin 4 => L) 0) N) hw hwb (v' + v' + 1) hgm hgb)
    A B hA0 hB0 v v' hFk hGk p q hpq hW
  have heq := connK_eq_expect_slab hN hβ (L := fun _ : Fin 4 => L) (m := v + v + 1)
    (m' := v' + v' + 1) (p := p) (q := q) (by show L = _; omega) hfm hgm hfb hgb
    (hf.mono (by omega)) (hg.mono (by omega))
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end SlabCapstone

section SlabCapstoneG

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.DoublingWilsonG
  MassGap.GaugeGroup MassGap.OpenAIBridgeGroups

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
/-- **Exponential clustering of two slab observables on the Wilson torus of every gauge group,
uniform in the torus, from the seed** (`wilson_slab_conn` over a `GaugeGroup G`). If one torus of
even side `n ≥ 2` has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic torus
of `G` of every even side `L ≥ 2n`, for bounded measurable functions `f`, `g` of a sequence of
slices and time links (`|f| ≤ A`, `|g| ≤ B`) reading slabs of widths `w = 2v + 2`, `w' = 2v' + 2`,
at times `0` and `w + p + 1` of `L = p + q + 2 + w + w'` with `4(w + w') + 8n ≤ L`,

    |⟨f_0 g_{w+p+1}⟩ − ⟨f_0⟩⟨g_{w+p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

It is `wilson_connK_slabG` read through `connK_eq_expect_slabG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of `connK_uniform`;
`4` and `8` the slab condition of `excited_le_slab`, and `4` the spacetime dimension; `1/2` the
contraction; `2` the doubled side, the least seed side, the least ratio `L / n`, the doubled widths
and the offsets of `iter`; `0` the time direction, the first slice and the sign of the coupling;
`1` the offsets of `iter`, the separation and the side `M + 1`. -/
theorem wilson_slab_connG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L)
    (f g : (ℕ → SpT 0 (tr (fun _ : Fin 4 => L) 0) → G) → (ℕ → TT 0 (tr (fun _ : Fin 4 => L) 0) → G)
      → ℝ)
    (hfm : Measurable (fun r : (ℕ → SpT 0 (tr (fun _ : Fin 4 => L) 0) → G)
      × (ℕ → TT 0 (tr (fun _ : Fin 4 => L) 0) → G) => f r.1 r.2))
    (hgm : Measurable (fun r : (ℕ → SpT 0 (tr (fun _ : Fin 4 => L) 0) → G)
      × (ℕ → TT 0 (tr (fun _ : Fin 4 => L) 0) → G) => g r.1 r.2))
    (A B : ℝ) (hfb : ∀ V A', |f V A'| ≤ A) (hgb : ∀ V A', |g V A'| ≤ B) (v v' : ℕ)
    (hf : LocalUpTo (v + v + 2) f) (hg : LocalUpTo (v' + v' + 2) g) (p q : ℕ)
    (hpq : p + q + 2 + (v + v + 2) + (v' + v' + 2) = L)
    (hW : 4 * ((v + v + 2) + (v' + v' + 2)) + 8 * n ≤ L) :
    |(sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
        (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U)
          * g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U)
            (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U))
      - (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
          (fun U => f (slabV (fun _ : Fin 4 => L) 0 0 U) (slabA (fun _ : Fin 4 => L) 0 0 U))
        * (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
          (fun U => g (slabV (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U)
            (slabA (fun _ : Fin 4 => L) 0 (v + v + 2 + (p + 1)) U))|
      ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨φ, c, hc0, hφ1, heig, hcl⟩ := wilson_connK_slabG hβ hn he h0 L hLe hL
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
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
  have h := hcl _ _
    (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb
      (v + v + 1) hfm hfb)
    (bdd_slabKer (μ := hSG G 0 (TorusChain.Tc M)) (ν := hAG G 0 (TorusChain.Tc M)) hw hwb
      (v' + v' + 1) hgm hgb)
    A B hA0 hB0 v v' hFk hGk p q hpq hW
  have heq := connK_eq_expect_slabG hβ (M := M) (m := v + v + 1) (m' := v' + v' + 1) (p := p)
    (q := q) (by omega) hfm hgm hfb hgb (hf.mono (by omega)) (hg.mono (by omega))
  rw [show v + v + 1 + 1 = v + v + 2 by omega, show v' + v' + 1 + 1 = v' + v' + 2 by omega] at heq
  exact (congrArg abs heq).symm.le.trans h

end SlabCapstoneG

end MassGap.OpenAIBridgeSlab

#print axioms MassGap.OpenAIBridgeSlab.bdd_tp
#print axioms MassGap.OpenAIBridgeSlab.tp_conv
#print axioms MassGap.OpenAIBridgeSlab.tp_iter
#print axioms MassGap.OpenAIBridgeSlab.hs_tp
#print axioms MassGap.OpenAIBridgeSlab.trc_conv_comm
#print axioms MassGap.OpenAIBridgeSlab.sq_trc_conv_le
#print axioms MassGap.OpenAIBridgeSlab.hs_eq_trc
#print axioms MassGap.OpenAIBridgeSlab.OpBd.transpose
#print axioms MassGap.OpenAIBridgeSlab.hs_const_mul
#print axioms MassGap.OpenAIBridgeSlab.bdd_abs
#print axioms MassGap.OpenAIBridgeSlab.hs_abs
#print axioms MassGap.OpenAIBridgeSlab.hs_le_of_abs_le
#print axioms MassGap.OpenAIBridgeSlab.abs_conv_le_left
#print axioms MassGap.OpenAIBridgeSlab.abs_conv_le_right
#print axioms MassGap.OpenAIBridgeSlab.hs_iter_conv_le
#print axioms MassGap.OpenAIBridgeSlab.hs_conv_iter_le
#print axioms MassGap.OpenAIBridgeSlab.opBd_of_le
#print axioms MassGap.OpenAIBridgeSlab.trK_comm
#print axioms MassGap.OpenAIBridgeSlab.abs_trK_le_sum
#print axioms MassGap.OpenAIBridgeSlab.hs_conv_tp
#print axioms MassGap.OpenAIBridgeSlab.trK_sq_le
#print axioms MassGap.OpenAIBridgeSlab.trK_pow_le
#print axioms MassGap.OpenAIBridgeSlab.abs_trK_le
#print axioms MassGap.OpenAIBridgeSlab.abs_trc_conv_iter_le
#print axioms MassGap.OpenAIBridgeSlab.measurable_kf
#print axioms MassGap.OpenAIBridgeSlab.abs_kf_le
#print axioms MassGap.OpenAIBridgeSlab.hs_left
#print axioms MassGap.OpenAIBridgeSlab.integral_mul_split
#print axioms MassGap.OpenAIBridgeSlab.sq_kf_le
#print axioms MassGap.OpenAIBridgeSlab.abs_vac_le
#print axioms MassGap.OpenAIBridgeSlab.row_conv
#print axioms MassGap.OpenAIBridgeSlab.vac_tp
#print axioms MassGap.OpenAIBridgeSlab.conv_iter_eq
#print axioms MassGap.OpenAIBridgeSlab.row_conv_iter
#print axioms MassGap.OpenAIBridgeSlab.row_conv_rem
#print axioms MassGap.OpenAIBridgeSlab.trc_split
#print axioms MassGap.OpenAIBridgeSlab.trK_decomp
#print axioms MassGap.OpenAIBridgeSlab.trOne_decomp
#print axioms MassGap.OpenAIBridgeSlab.trPow_even
#print axioms MassGap.OpenAIBridgeSlab.conn_alg2
#print axioms MassGap.OpenAIBridgeSlab.nonneg_of_mul_pow
#print axioms MassGap.OpenAIBridgeSlab.connK_le_excited
#print axioms MassGap.OpenAIBridgeSlab.connK_uniform
#print axioms MassGap.OpenAIBridgeSlab.excited_le_slab
#print axioms MassGap.OpenAIBridgeSlab.connK_slab
#print axioms MassGap.OpenAIBridgeSlab.wilson_connK_slab
#print axioms MassGap.OpenAIBridgeSlab.wilson_connK_slabG
#print axioms MassGap.OpenAIBridgeSlab.measurable_w_mid
#print axioms MassGap.OpenAIBridgeSlab.measurable_slabKer
#print axioms MassGap.OpenAIBridgeSlab.abs_slabKer_le
#print axioms MassGap.OpenAIBridgeSlab.bdd_slabKer
#print axioms MassGap.OpenAIBridgeSlab.slabKer_le_iter
#print axioms MassGap.OpenAIBridgeSlab.slabKer_one
#print axioms MassGap.OpenAIBridgeSlab.chain_slab
#print axioms MassGap.OpenAIBridgeSlab.chain_two
#print axioms MassGap.OpenAIBridgeSlab.trK_iter_right
#print axioms MassGap.OpenAIBridgeSlab.trK_iter_left
#print axioms MassGap.OpenAIBridgeSlab.measurable_slabV
#print axioms MassGap.OpenAIBridgeSlab.measurable_slabA
#print axioms MassGap.OpenAIBridgeSlab.extY_apply
#print axioms MassGap.OpenAIBridgeSlab.slabV_joinR
#print axioms MassGap.OpenAIBridgeSlab.slabA_joinR
#print axioms MassGap.OpenAIBridgeSlab.corrNum_slabK
#print axioms MassGap.OpenAIBridgeSlab.connK_eq_expect_slab
#print axioms MassGap.OpenAIBridgeSlab.slabV_joinWG
#print axioms MassGap.OpenAIBridgeSlab.slabA_joinWG
#print axioms MassGap.OpenAIBridgeSlab.corrNum_slabKG
#print axioms MassGap.OpenAIBridgeSlab.connK_eq_expect_slabG
#print axioms MassGap.OpenAIBridgeSlab.wilson_slab_conn
#print axioms MassGap.OpenAIBridgeSlab.wilson_slab_connG
