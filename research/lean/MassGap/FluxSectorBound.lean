import Mathlib
import MassGap.KernelPower

/-!
# MassGap.FluxSectorBound — the doubled trace splits over the two sectors of an involution

Let `(X, μ)` be a probability space, `σ` a measurable involution of `X` preserving `μ`, and `a` a
bounded measurable kernel on `X` that is symmetric and `σ`-invariant: `a(σx, σy) = a(x, y)`.

`a` is the transfer over half the time extent, read as a kernel on slice configurations, and `σ` is a
centre flip. `hs μ a = ∫∫ a²` is the trace over the full extent and `hs μ (conv μ a a)` the trace over
twice it (`CyclicKernel.cyc_even`). The flip splits the slice functions into even and odd parts, the
two electric-flux sectors of one direction. Each sector's doubled trace is at most the square of its
trace.

* `twist μ a σ = ∫∫ a(x,y) a(x,σy)`: the trace with the flip inserted, the temporally twisted
  partition function.
* `hs_conv_le_sector`: `hs(a ∗ a) ≤ (hs(a)² + twist²)/2`.

The proof writes `a ∗ a` as the sum of the Gram kernels of the even part `(a(x,y) + a(x,σy))/2` and of
the odd part `(a(x,y) − a(x,σy))/2`. The cross term integrates to zero because the odd Gram kernel
changes sign under `z ↦ σz` and the even one does not. Each Gram kernel obeys the pointwise
Cauchy–Schwarz bound, so its squared integral is at most the square of its diagonal integral. The two
diagonal integrals sum to `hs(a)` and differ by `twist`.

DERIVED (module-wide): `2` is the even/odd halving and the square; `0` is the cross term.
-/

namespace MassGap.FluxSectorBound

open MeasureTheory MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The twisted trace** `∫∫ a(x,y) a(x,σy)`. -/
noncomputable def twist (μ : Measure X) (a : X → X → ℝ) (σ : X → X) : ℝ :=
  ∫ x, ∫ y, a x y * a x (σ y) ∂μ ∂μ

/-- A measurable involution preserving `μ`. -/
structure Flip (μ : Measure X) (σ : X → X) : Prop where
  meas : Measurable σ
  invol : ∀ x, σ (σ x) = x
  mp : MeasurePreserving σ μ μ

/-- The involution as a measurable equivalence. -/
def Flip.equiv {σ : X → X} (h : Flip μ σ) : X ≃ᵐ X where
  toFun := σ
  invFun := σ
  left_inv := h.invol
  right_inv := h.invol
  measurable_toFun := h.meas
  measurable_invFun := h.meas

theorem Flip.integral_comp {σ : X → X} (h : Flip μ σ) (f : X → ℝ) :
    ∫ y, f (σ y) ∂μ = ∫ y, f y ∂μ := by
  have hmp : MeasurePreserving h.equiv μ μ := h.mp
  exact hmp.integral_comp' f

variable (μ) in
/-- The Gram kernel `∫ h(x,y) h(z,y) dμ(y)`. -/
noncomputable def gram (h : X → X → ℝ) : X → X → ℝ := fun x z => ∫ y, h x y * h z y ∂μ

/-- The even part `(a(x,y) + a(x,σy))/2`. -/
noncomputable def ev (a : X → X → ℝ) (σ : X → X) : X → X → ℝ := fun x y => (a x y + a x (σ y)) / 2

/-- The odd part `(a(x,y) − a(x,σy))/2`. -/
noncomputable def od (a : X → X → ℝ) (σ : X → X) : X → X → ℝ := fun x y => (a x y - a x (σ y)) / 2

/-! ## Bookkeeping -/

theorem irow {h : X → X → ℝ} (hh : Bdd h) (x : X) : Integrable (fun y => h x y) μ := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact integrable_of_bdd (hh.row x) (fun y => hC x y)

theorem idiag {h : X → X → ℝ} (hh : Bdd h) : Integrable (fun x => h x x) μ := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact integrable_of_bdd (hh.meas.comp (measurable_id.prodMk measurable_id)) (fun x => hC x x)

theorem bdd_mul {h k : X → X → ℝ} (hh : Bdd h) (hk : Bdd k) : Bdd (fun x y => h x y * k x y) := by
  obtain ⟨C, hC⟩ := hh.bdd
  obtain ⟨D, hD⟩ := hk.bdd
  refine ⟨hh.meas.mul hk.meas, C * D, fun x y => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x y) (hD x y) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))

theorem bdd_rows {h k : X → X → ℝ} (hh : Bdd h) (hk : Bdd k) (x z : X) :
    Integrable (fun y => h x y * k z y) μ := by
  obtain ⟨C, hC⟩ := hh.bdd
  obtain ⟨D, hD⟩ := hk.bdd
  refine integrable_of_bdd ((hh.row x).mul (hk.row z)) (C := C * D) (fun y => ?_)
  rw [abs_mul]
  exact mul_le_mul (hC x y) (hD z y) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))

theorem bdd_flip {a : X → X → ℝ} {σ : X → X} (ha : Bdd a) (hf : Flip μ σ) :
    Bdd (fun x y => a x (σ y)) := by
  obtain ⟨C, hC⟩ := ha.bdd
  exact ⟨ha.meas.comp (measurable_fst.prodMk (hf.meas.comp measurable_snd)), C,
    fun x y => hC x (σ y)⟩

theorem bdd_ev {a : X → X → ℝ} {σ : X → X} (ha : Bdd a) (hf : Flip μ σ) : Bdd (ev a σ) := by
  obtain ⟨C, hC⟩ := ha.bdd
  refine ⟨(ha.meas.add (bdd_flip ha hf).meas).div_const 2, C, fun x y => ?_⟩
  have h1 := abs_le.mp (hC x y)
  have h2 := abs_le.mp (hC x (σ y))
  simp only [ev]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem bdd_od {a : X → X → ℝ} {σ : X → X} (ha : Bdd a) (hf : Flip μ σ) : Bdd (od a σ) := by
  obtain ⟨C, hC⟩ := ha.bdd
  refine ⟨(ha.meas.sub (bdd_flip ha hf).meas).div_const 2, C, fun x y => ?_⟩
  have h1 := abs_le.mp (hC x y)
  have h2 := abs_le.mp (hC x (σ y))
  simp only [od]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem bdd_gram {h : X → X → ℝ} (hh : Bdd h) : Bdd (gram μ h) := by
  obtain ⟨C, hC⟩ := hh.bdd
  refine ⟨?_, C * C, fun x z => ?_⟩
  · have hm : Measurable (fun p : (X × X) × X => h p.1.1 p.2 * h p.1.2 p.2) :=
      (hh.meas.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hh.meas.comp (measurable_fst.snd.prodMk measurable_snd))
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  · apply abs_integral_le
    intro y
    rw [abs_mul]
    exact mul_le_mul (hC x y) (hC z y) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))

/-! ## The sector identities -/

variable {a : X → X → ℝ} {σ : X → X}

/-- `a ∗ a` is the sum of the even and odd Gram kernels. -/
theorem conv_eq_gram (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ) (x z : X) :
    conv μ a a x z = gram μ (ev a σ) x z + gram μ (od a σ) x z := by
  have hσ := bdd_flip ha hf
  unfold gram conv
  rw [← integral_add (bdd_rows (bdd_ev ha hf) (bdd_ev ha hf) x z)
    (bdd_rows (bdd_od ha hf) (bdd_od ha hf) x z)]
  have e1 : (fun y => ev a σ x y * ev a σ z y + od a σ x y * od a σ z y)
      = fun y => (a x y * a z y + a x (σ y) * a z (σ y)) / 2 := by
    funext y; simp only [ev, od]; ring
  rw [e1, integral_div, integral_add (bdd_rows ha ha x z) (bdd_rows hσ hσ x z)]
  have e2 : ∫ y, a x (σ y) * a z (σ y) ∂μ = ∫ y, a x y * a z y ∂μ :=
    hf.integral_comp (fun y => a x y * a z y)
  have e3 : ∫ y, a x y * a y z ∂μ = ∫ y, a x y * a z y ∂μ := by
    congr 1; funext y; rw [hsym y z]
  rw [e2, e3]; ring

theorem a_flip_left (hf : Flip μ σ) (hinv : ∀ x y, a (σ x) (σ y) = a x y) (z y : X) :
    a (σ z) y = a z (σ y) := by
  have := hinv z (σ y)
  rwa [hf.invol] at this

theorem ev_flip (hf : Flip μ σ) (hinv : ∀ x y, a (σ x) (σ y) = a x y) (z y : X) :
    ev a σ (σ z) y = ev a σ z y := by
  simp only [ev]
  rw [a_flip_left hf hinv, hinv]; ring

theorem od_flip (hf : Flip μ σ) (hinv : ∀ x y, a (σ x) (σ y) = a x y) (z y : X) :
    od a σ (σ z) y = -od a σ z y := by
  simp only [od]
  rw [a_flip_left hf hinv, hinv]; ring

theorem gram_ev_flip (hf : Flip μ σ) (hinv : ∀ x y, a (σ x) (σ y) = a x y) (x z : X) :
    gram μ (ev a σ) x (σ z) = gram μ (ev a σ) x z := by
  unfold gram
  congr 1; funext y; rw [ev_flip hf hinv]

theorem gram_od_flip (hf : Flip μ σ) (hinv : ∀ x y, a (σ x) (σ y) = a x y) (x z : X) :
    gram μ (od a σ) x (σ z) = -gram μ (od a σ) x z := by
  unfold gram
  rw [← integral_neg]
  congr 1; funext y; rw [od_flip hf hinv]; ring

/-- The cross term vanishes. -/
theorem integral_cross (hf : Flip μ σ) (hinv : ∀ x y, a (σ x) (σ y) = a x y) (x : X) :
    ∫ z, gram μ (ev a σ) x z * gram μ (od a σ) x z ∂μ = 0 := by
  have h := hf.integral_comp (fun z => gram μ (ev a σ) x z * gram μ (od a σ) x z)
  simp only [gram_ev_flip hf hinv, gram_od_flip hf hinv] at h
  have h2 : ∫ z, gram μ (ev a σ) x z * -gram μ (od a σ) x z ∂μ
      = -∫ z, gram μ (ev a σ) x z * gram μ (od a σ) x z ∂μ := by
    rw [← integral_neg]; congr 1; funext z; ring
  linarith

/-- Pointwise Cauchy–Schwarz for a Gram kernel. -/
theorem sq_gram_le {h : X → X → ℝ} (hh : Bdd h) (x z : X) :
    gram μ h x z ^ 2 ≤ gram μ h x x * gram μ h z z := by
  have i1 : Integrable (fun y => h x y ^ 2) μ := by
    have := bdd_rows (μ := μ) hh hh x x; simpa [sq] using this
  have i2 : Integrable (fun y => h z y ^ 2) μ := by
    have := bdd_rows (μ := μ) hh hh z z; simpa [sq] using this
  have := sq_integral_mul_le (ν := μ) (f := fun y => h x y) (g := fun y => h z y) i1 i2
    (bdd_rows hh hh x z)
  have ex : gram μ h x x = ∫ y, h x y ^ 2 ∂μ := by unfold gram; congr 1; funext y; ring
  have ez : gram μ h z z = ∫ y, h z y ^ 2 ∂μ := by unfold gram; congr 1; funext y; ring
  rw [ex, ez]
  exact this

theorem gram_diag_nonneg (h : X → X → ℝ) (x : X) : 0 ≤ gram μ h x x := by
  unfold gram
  exact integral_nonneg fun y => mul_self_nonneg _

/-- The two diagonal Gram integrals sum to `∫ a(x,·)²`. -/
theorem diag_add (ha : Bdd a) (hf : Flip μ σ) (x : X) :
    gram μ (ev a σ) x x + gram μ (od a σ) x x = ∫ y, a x y ^ 2 ∂μ := by
  have hσ := bdd_flip ha hf
  unfold gram
  rw [← integral_add (bdd_rows (bdd_ev ha hf) (bdd_ev ha hf) x x)
    (bdd_rows (bdd_od ha hf) (bdd_od ha hf) x x)]
  have e1 : (fun y => ev a σ x y * ev a σ x y + od a σ x y * od a σ x y)
      = fun y => (a x y * a x y + a x (σ y) * a x (σ y)) / 2 := by
    funext y; simp only [ev, od]; ring
  rw [e1, integral_div, integral_add (bdd_rows ha ha x x) (bdd_rows hσ hσ x x)]
  have e2 : ∫ y, a x (σ y) * a x (σ y) ∂μ = ∫ y, a x y * a x y ∂μ :=
    hf.integral_comp (fun y => a x y * a x y)
  rw [e2]
  have e3 : ∫ y, a x y * a x y ∂μ = ∫ y, a x y ^ 2 ∂μ := by congr 1; funext y; ring
  rw [e3]; ring

/-- The two diagonal Gram integrals differ by the twisted row. -/
theorem diag_sub (ha : Bdd a) (hf : Flip μ σ) (x : X) :
    gram μ (ev a σ) x x - gram μ (od a σ) x x = ∫ y, a x y * a x (σ y) ∂μ := by
  unfold gram
  rw [← integral_sub (bdd_rows (bdd_ev ha hf) (bdd_ev ha hf) x x)
    (bdd_rows (bdd_od ha hf) (bdd_od ha hf) x x)]
  congr 1; funext y; simp only [ev, od]; ring

/-! ## The sector bound -/

/-- **The doubled trace is at most the sum of the squared sector traces**:
`hs(a ∗ a) ≤ (hs(a)² + twist²)/2`. -/
theorem hs_conv_le_sector (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) :
    hs μ (conv μ a a) ≤ (hs μ a ^ 2 + twist μ a σ ^ 2) / 2 := by
  set Ge := gram μ (ev a σ) with hGe
  set Go := gram μ (od a σ) with hGo
  have bE : Bdd Ge := bdd_gram (bdd_ev ha hf)
  have bO : Bdd Go := bdd_gram (bdd_od ha hf)
  set cE := ∫ x, Ge x x ∂μ with hcE
  set cO := ∫ x, Go x x ∂μ with hcO
  -- inner integral, pointwise in `x`
  have hin : ∀ x, ∫ z, conv μ a a x z ^ 2 ∂μ ≤ Ge x x * cE + Go x x * cO := by
    intro x
    have e1 : (fun z => conv μ a a x z ^ 2)
        = fun z => Ge x z ^ 2 + Go x z ^ 2 + 2 * (Ge x z * Go x z) := by
      funext z; rw [conv_eq_gram ha hsym hf x z]; ring
    have iE : Integrable (fun z => Ge x z ^ 2) μ := by
      have := bdd_rows (μ := μ) bE bE x x; simpa [sq] using this
    have iO : Integrable (fun z => Go x z ^ 2) μ := by
      have := bdd_rows (μ := μ) bO bO x x; simpa [sq] using this
    have iEO : Integrable (fun z => Ge x z * Go x z) μ := bdd_rows bE bO x x
    have iEpO : Integrable (fun z => Ge x z ^ 2 + Go x z ^ 2) μ := iE.add iO
    have iEO2 : Integrable (fun z => 2 * (Ge x z * Go x z)) μ := iEO.const_mul 2
    rw [e1, integral_add iEpO iEO2, integral_add iE iO, integral_const_mul,
      integral_cross hf hinv x, mul_zero, add_zero]
    have hE : ∫ z, Ge x z ^ 2 ∂μ ≤ Ge x x * cE := by
      rw [hcE, ← integral_const_mul]
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
        ((idiag bE).const_mul _) (Filter.Eventually.of_forall fun z => sq_gram_le (bdd_ev ha hf) x z)
    have hO : ∫ z, Go x z ^ 2 ∂μ ≤ Go x x * cO := by
      rw [hcO, ← integral_const_mul]
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
        ((idiag bO).const_mul _) (Filter.Eventually.of_forall fun z => sq_gram_le (bdd_od ha hf) x z)
    linarith
  -- outer integral
  have hout : hs μ (conv μ a a) ≤ cE * cE + cO * cO := by
    unfold hs
    have hg : Integrable (fun x => Ge x x * cE + Go x x * cO) μ :=
      ((idiag bE).mul_const _).add ((idiag bO).mul_const _)
    calc ∫ x, ∫ z, conv μ a a x z ^ 2 ∂μ ∂μ ≤ ∫ x, (Ge x x * cE + Go x x * cO) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            integral_nonneg fun z => sq_nonneg _) hg (Filter.Eventually.of_forall hin)
      _ = cE * cE + cO * cO := by
          rw [integral_add ((idiag bE).mul_const _) ((idiag bO).mul_const _), integral_mul_const,
            integral_mul_const]
  -- the two diagonal integrals
  have hsum : cE + cO = hs μ a := by
    rw [hcE, hcO, ← integral_add (idiag bE) (idiag bO)]
    unfold hs
    congr 1; funext x; exact diag_add ha hf x
  have hdiff : cE - cO = twist μ a σ := by
    rw [hcE, hcO, ← integral_sub (idiag bE) (idiag bO)]
    unfold twist
    congr 1; funext x; exact diag_sub ha hf x
  have : cE * cE + cO * cO = (hs μ a ^ 2 + twist μ a σ ^ 2) / 2 := by
    rw [← hsum, ← hdiff]; ring
  linarith

/-! ## Two flips -/

/-- **One twisted row.** If `a(x,y) a(x,σy) ≤ ε + χ(y)(a(x,y)² + a(x,σy)²)/2` pointwise, with
`0 ≤ χ ≤ 1` measurable and `σ`-invariant, then `∫ a(x,y) a(x,σy) dy ≤ ε + ∫ χ(y) a(x,y)² dy`. -/
theorem row_twist_le (ha : Bdd a) (hf : Flip μ σ) {χ : X → ℝ} (hχ : Measurable χ)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hχσ : ∀ y, χ (σ y) = χ y) {ε : ℝ}
    (h : ∀ x y, a x y * a x (σ y) ≤ ε + χ y * ((a x y ^ 2 + a x (σ y) ^ 2) / 2)) (x : X) :
    ∫ y, a x y * a x (σ y) ∂μ ≤ ε + ∫ y, χ y * a x y ^ 2 ∂μ := by
  obtain ⟨C, hC⟩ := ha.bdd
  have hσ := bdd_flip ha hf
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x x)
  have bχa : Bdd (fun x y => χ y * a x y ^ 2) := by
    refine ⟨(hχ.comp measurable_snd).mul (ha.meas.pow_const 2), C ^ 2, fun x y => ?_⟩
    rw [abs_mul, abs_of_nonneg (hχb y).1, abs_of_nonneg (sq_nonneg _)]
    have h1 : a x y ^ 2 ≤ C ^ 2 := by
      have := hC x y; nlinarith [abs_nonneg (a x y), sq_abs (a x y)]
    nlinarith [(hχb y).1, (hχb y).2, sq_nonneg (a x y)]
  have bχaσ : Bdd (fun x y => χ y * a x (σ y) ^ 2) := by
    refine ⟨(hχ.comp measurable_snd).mul (hσ.meas.pow_const 2), C ^ 2, fun x y => ?_⟩
    rw [abs_mul, abs_of_nonneg (hχb y).1, abs_of_nonneg (sq_nonneg _)]
    have h1 : a x (σ y) ^ 2 ≤ C ^ 2 := by
      have := hC x (σ y); nlinarith [abs_nonneg (a x (σ y)), sq_abs (a x (σ y))]
    nlinarith [(hχb y).1, (hχb y).2, sq_nonneg (a x (σ y))]
  have iR : Integrable (fun y => ε + χ y * ((a x y ^ 2 + a x (σ y) ^ 2) / 2)) μ := by
    have e : (fun y => ε + χ y * ((a x y ^ 2 + a x (σ y) ^ 2) / 2))
        = fun y => ε + ((χ y * a x y ^ 2) / 2 + (χ y * a x (σ y) ^ 2) / 2) := by
      funext y; ring
    rw [e]
    exact (integrable_const ε).add (((irow bχa x).div_const 2).add ((irow bχaσ x).div_const 2))
  have hle : ∫ y, a x y * a x (σ y) ∂μ
      ≤ ∫ y, ε + χ y * ((a x y ^ 2 + a x (σ y) ^ 2) / 2) ∂μ :=
    integral_mono (bdd_rows ha hσ x x) iR (fun y => h x y)
  have hflip : ∫ y, χ y * a x (σ y) ^ 2 ∂μ = ∫ y, χ y * a x y ^ 2 ∂μ := by
    have := hf.integral_comp (fun y => χ y * a x y ^ 2)
    simp only [hχσ] at this
    exact this
  have e2 : ∫ y, ε + χ y * ((a x y ^ 2 + a x (σ y) ^ 2) / 2) ∂μ
      = ε + ((∫ y, χ y * a x y ^ 2 ∂μ) / 2 + (∫ y, χ y * a x (σ y) ^ 2 ∂μ) / 2) := by
    have e : (fun y => ε + χ y * ((a x y ^ 2 + a x (σ y) ^ 2) / 2))
        = fun y => ε + ((χ y * a x y ^ 2) / 2 + (χ y * a x (σ y) ^ 2) / 2) := by
      funext y; ring
    have i1 : Integrable (fun y => χ y * a x y ^ 2 / 2) μ := (irow bχa x).div_const 2
    have i2 : Integrable (fun y => χ y * a x (σ y) ^ 2 / 2) μ := (irow bχaσ x).div_const 2
    have i12 : Integrable (fun y => χ y * a x y ^ 2 / 2 + χ y * a x (σ y) ^ 2 / 2) μ := i1.add i2
    rw [e, integral_add (integrable_const ε) i12, integral_add i1 i2, integral_const,
      integral_div, integral_div]
    simp
  rw [e2, hflip] at hle
  linarith

/-- **Two twisted traces nearly exhaust the trace.** With the pointwise hypotheses of
`row_twist_le` for `σ₁` (weight `χ₁`) and `σ₂` (weight `χ₂`), and
`(χ₁(y) + χ₂(y)) a(x,y)² ≤ a(x,y)² + η` pointwise:
`twist σ₁ + twist σ₂ ≤ hs(a) + 2ε + η`. -/
theorem twist_add_le (ha : Bdd a) {σ₁ σ₂ : X → X} (hf₁ : Flip μ σ₁) (hf₂ : Flip μ σ₂)
    {χ₁ χ₂ : X → ℝ} (hχ₁ : Measurable χ₁) (hχ₂ : Measurable χ₂)
    (hχ₁b : ∀ y, 0 ≤ χ₁ y ∧ χ₁ y ≤ 1) (hχ₂b : ∀ y, 0 ≤ χ₂ y ∧ χ₂ y ≤ 1)
    (hχ₁σ : ∀ y, χ₁ (σ₁ y) = χ₁ y) (hχ₂σ : ∀ y, χ₂ (σ₂ y) = χ₂ y) {ε η : ℝ}
    (h1 : ∀ x y, a x y * a x (σ₁ y) ≤ ε + χ₁ y * ((a x y ^ 2 + a x (σ₁ y) ^ 2) / 2))
    (h2 : ∀ x y, a x y * a x (σ₂ y) ≤ ε + χ₂ y * ((a x y ^ 2 + a x (σ₂ y) ^ 2) / 2))
    (h3 : ∀ x y, (χ₁ y + χ₂ y) * a x y ^ 2 ≤ a x y ^ 2 + η) :
    twist μ a σ₁ + twist μ a σ₂ ≤ hs μ a + 2 * ε + η := by
  obtain ⟨C, hC⟩ := ha.bdd
  have bsq : Bdd (fun x y => a x y ^ 2) := by
    have := bdd_mul ha ha; simpa [sq] using this
  have bχ : ∀ {χ : X → ℝ}, Measurable χ → (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) →
      Bdd (fun x y => χ y * a x y ^ 2) := by
    intro χ hχ hχb
    refine ⟨(hχ.comp measurable_snd).mul (ha.meas.pow_const 2), C ^ 2, fun x y => ?_⟩
    rw [abs_mul, abs_of_nonneg (hχb y).1, abs_of_nonneg (sq_nonneg _)]
    have : a x y ^ 2 ≤ C ^ 2 := by
      have := hC x y; nlinarith [abs_nonneg (a x y), sq_abs (a x y)]
    nlinarith [(hχb y).1, (hχb y).2, sq_nonneg (a x y)]
  have b1 := bχ hχ₁ hχ₁b
  have b2 := bχ hχ₂ hχ₂b
  have hx : ∀ x, ∫ y, a x y * a x (σ₁ y) ∂μ + ∫ y, a x y * a x (σ₂ y) ∂μ
      ≤ ∫ y, a x y ^ 2 ∂μ + 2 * ε + η := by
    intro x
    have r1 := row_twist_le ha hf₁ hχ₁ hχ₁b hχ₁σ h1 x
    have r2 := row_twist_le ha hf₂ hχ₂ hχ₂b hχ₂σ h2 x
    have hsum : ∫ y, χ₁ y * a x y ^ 2 ∂μ + ∫ y, χ₂ y * a x y ^ 2 ∂μ
        ≤ ∫ y, a x y ^ 2 ∂μ + η := by
      rw [← integral_add (irow b1 x) (irow b2 x)]
      have i3 : Integrable (fun y => a x y ^ 2 + η) μ := (irow bsq x).add (integrable_const η)
      calc ∫ y, (χ₁ y * a x y ^ 2 + χ₂ y * a x y ^ 2) ∂μ ≤ ∫ y, (a x y ^ 2 + η) ∂μ :=
            integral_mono ((irow b1 x).add (irow b2 x)) i3 (fun y => by
              have := h3 x y; nlinarith)
        _ = ∫ y, a x y ^ 2 ∂μ + η := by
            rw [integral_add (irow bsq x) (integrable_const η), integral_const]; simp
    linarith
  have hσ₁ := bdd_flip ha hf₁
  have hσ₂ := bdd_flip ha hf₂
  have m1 : Integrable (fun x => ∫ y, a x y * a x (σ₁ y) ∂μ) μ := by
    have bb := bdd_mul ha hσ₁
    refine integrable_of_bdd (measurable_integral_right bb.meas) (C := C * C) (fun x => ?_)
    apply abs_integral_le
    intro y; rw [abs_mul]
    exact mul_le_mul (hC x y) (hC x (σ₁ y)) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))
  have m2 : Integrable (fun x => ∫ y, a x y * a x (σ₂ y) ∂μ) μ := by
    have bb := bdd_mul ha hσ₂
    refine integrable_of_bdd (measurable_integral_right bb.meas) (C := C * C) (fun x => ?_)
    apply abs_integral_le
    intro y; rw [abs_mul]
    exact mul_le_mul (hC x y) (hC x (σ₂ y)) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))
  have i0 : Integrable (fun x => ∫ y, a x y ^ 2 ∂μ) μ := by
    refine integrable_of_bdd (measurable_integral_right bsq.meas) (C := C * C) (fun x => ?_)
    apply abs_integral_le
    intro y; rw [abs_of_nonneg (sq_nonneg _), sq]
    have := hC x y
    nlinarith [abs_nonneg (a x y), sq_abs (a x y)]
  have i0e : Integrable (fun x => ∫ y, a x y ^ 2 ∂μ + 2 * ε) μ := i0.add (integrable_const _)
  have m3 : Integrable (fun x => ∫ y, a x y ^ 2 ∂μ + 2 * ε + η) μ := i0e.add (integrable_const _)
  have m12 : Integrable (fun x => ∫ y, a x y * a x (σ₁ y) ∂μ + ∫ y, a x y * a x (σ₂ y) ∂μ) μ :=
    m1.add m2
  unfold twist hs
  rw [← integral_add m1 m2]
  calc ∫ x, (∫ y, a x y * a x (σ₁ y) ∂μ + ∫ y, a x y * a x (σ₂ y) ∂μ) ∂μ
      ≤ ∫ x, (∫ y, a x y ^ 2 ∂μ + 2 * ε + η) ∂μ := integral_mono m12 m3 hx
    _ = ∫ x, ∫ z, a x z ^ 2 ∂μ ∂μ + 2 * ε + η := by
        rw [integral_add i0e (integrable_const _), integral_add i0 (integrable_const _),
          integral_const, integral_const]
        simp

/-- **Two twisted traces summing to at most `(3/2) hs(a)` push the doubled trace below the squared
trace**: `hs(a ∗ a) ≤ (25/32) hs(a)²`, for a nonnegative symmetric kernel invariant under both flips.
DERIVED: `25/32 = (1 + (3/4)²)/2`, the sector bound at the smaller twisted trace, which is at most
`(3/4) hs(a)`. -/
theorem hs_conv_le_of_twist_add (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y)
    (hsym : ∀ x y, a x y = a y x) {σ₁ σ₂ : X → X} (hf₁ : Flip μ σ₁) (hf₂ : Flip μ σ₂)
    (hinv₁ : ∀ x y, a (σ₁ x) (σ₁ y) = a x y) (hinv₂ : ∀ x y, a (σ₂ x) (σ₂ y) = a x y)
    (hT : twist μ a σ₁ + twist μ a σ₂ ≤ 3 / 2 * hs μ a) :
    hs μ (conv μ a a) ≤ 25 / 32 * hs μ a ^ 2 := by
  have t1 : 0 ≤ twist μ a σ₁ :=
    integral_nonneg fun x => integral_nonneg fun y => mul_nonneg (ha0 _ _) (ha0 _ _)
  have t2 : 0 ≤ twist μ a σ₂ :=
    integral_nonneg fun x => integral_nonneg fun y => mul_nonneg (ha0 _ _) (ha0 _ _)
  have hh : 0 ≤ hs μ a := hs_nonneg a
  rcases le_total (twist μ a σ₁) (twist μ a σ₂) with h | h
  · have hs1 := hs_conv_le_sector ha hsym hf₁ hinv₁
    have : twist μ a σ₁ ≤ 3 / 4 * hs μ a := by linarith
    have : twist μ a σ₁ ^ 2 ≤ (3 / 4 * hs μ a) ^ 2 := pow_le_pow_left₀ t1 this 2
    nlinarith
  · have hs2 := hs_conv_le_sector ha hsym hf₂ hinv₂
    have : twist μ a σ₂ ≤ 3 / 4 * hs μ a := by linarith
    have : twist μ a σ₂ ^ 2 ≤ (3 / 4 * hs μ a) ^ 2 := pow_le_pow_left₀ t2 this 2
    nlinarith

/-- **The doubled trace drops below the squared trace.** For a nonnegative symmetric kernel invariant
under two flips, with the hypotheses of `twist_add_le` and `2ε + η ≤ hs(a)/2`:
`hs(a ∗ a) ≤ (25/32) hs(a)²` (`hs_conv_le_of_twist_add`). -/
theorem hs_conv_le_of_two_flips (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y)
    (hsym : ∀ x y, a x y = a y x) {σ₁ σ₂ : X → X} (hf₁ : Flip μ σ₁) (hf₂ : Flip μ σ₂)
    (hinv₁ : ∀ x y, a (σ₁ x) (σ₁ y) = a x y) (hinv₂ : ∀ x y, a (σ₂ x) (σ₂ y) = a x y)
    {χ₁ χ₂ : X → ℝ} (hχ₁ : Measurable χ₁) (hχ₂ : Measurable χ₂)
    (hχ₁b : ∀ y, 0 ≤ χ₁ y ∧ χ₁ y ≤ 1) (hχ₂b : ∀ y, 0 ≤ χ₂ y ∧ χ₂ y ≤ 1)
    (hχ₁σ : ∀ y, χ₁ (σ₁ y) = χ₁ y) (hχ₂σ : ∀ y, χ₂ (σ₂ y) = χ₂ y) {ε η : ℝ}
    (h1 : ∀ x y, a x y * a x (σ₁ y) ≤ ε + χ₁ y * ((a x y ^ 2 + a x (σ₁ y) ^ 2) / 2))
    (h2 : ∀ x y, a x y * a x (σ₂ y) ≤ ε + χ₂ y * ((a x y ^ 2 + a x (σ₂ y) ^ 2) / 2))
    (h3 : ∀ x y, (χ₁ y + χ₂ y) * a x y ^ 2 ≤ a x y ^ 2 + η)
    (hsmall : 2 * ε + η ≤ hs μ a / 2) :
    hs μ (conv μ a a) ≤ 25 / 32 * hs μ a ^ 2 := by
  have hT := twist_add_le ha hf₁ hf₂ hχ₁ hχ₂ hχ₁b hχ₂b hχ₁σ hχ₂σ h1 h2 h3
  exact hs_conv_le_of_twist_add ha ha0 hsym hf₁ hf₂ hinv₁ hinv₂ (by linarith)

end MassGap.FluxSectorBound

#print axioms MassGap.FluxSectorBound.hs_conv_le_sector
#print axioms MassGap.FluxSectorBound.twist_add_le
#print axioms MassGap.FluxSectorBound.hs_conv_le_of_two_flips
#print axioms MassGap.FluxSectorBound.hs_conv_le_of_twist_add
