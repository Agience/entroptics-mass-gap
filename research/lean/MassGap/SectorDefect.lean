import Mathlib
import MassGap.FluxSectorBound

/-!
# MassGap.SectorDefect — the doubling defect of a kernel splits over the sectors of commuting flips

Let `(X, μ)` be a probability space and `a` a bounded, symmetric kernel, invariant under a list `l` of
pairwise commuting measure-preserving involutions, and bounded below by a constant `c > 0`. `a` is the
transfer over half the time extent, `hs μ a` the trace over the full extent, and `hs μ (a ∗ a)` the
trace over twice it. The doubling defect of `a` is `dd μ a = 2 log hs(a) − log hs(a ∗ a)`.

Each flip `σ` splits `a` into its even part `ev a σ` and its odd part `od a σ`
(`FluxSectorBound`). The even part is again a kernel of the same kind for the remaining flips, so the
flips of `l` can be applied one after another: `evL a l` is the kernel of the sector that is even
under every flip of `l`. On the lattice it is the trivial electric-flux sector.

* `hs_conv_split`: `hs(a ∗ a) = hs(ev ∗ ev) + hs(od ∗ od)`. The doubled trace is the sum of the two
  sectors' doubled traces; the cross term vanishes.
* `hs_ev`, `hs_od`: `hs(ev) = (hs(a) + twist)/2`, `hs(od) = (hs(a) − twist)/2`.
* `dd_le_evL`: `dd(a) ≤ dd(evL a l) + 2 (log hs(a) − log hs(evL a l))`. The defect is at most the
  defect of the even sector plus twice the log of the inverse of that sector's share of the trace.
* `hs_conv_le_evL`: `hs(a ∗ a) ≤ hs(e ∗ e) + (hs(a) − hs(e))²`, `e = evL a l`. With
  `hs(e ∗ e) ≤ hs(e)²` this bounds the share of the other sectors by the defect, and read the other way
  it bounds the even sector's doubled trace from below by the full one.
* `hs_evL_ge`: for a nonnegative kernel, `hs(a)/2^{|l|} ≤ hs(evL a l)`: every twisted trace is
  nonnegative, so the even sector carries at least half the trace at each flip.

So the doubling defect is small exactly when two things hold: the sectors odd under some flip carry a
small share of the trace, and the even sector has a small defect of its own.

DERIVED (module-wide): `2` is the even/odd halving and the square in `hs`; `0` is the cross term.
-/

namespace MassGap.SectorDefect

open MeasureTheory MassGap.KernelPower MassGap.FluxSectorBound

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable (μ) in
/-- **The doubling defect of a kernel**: `2 log hs(a) − log hs(a ∗ a)`. -/
noncomputable def dd (a : X → X → ℝ) : ℝ :=
  2 * Real.log (hs μ a) - Real.log (hs μ (conv μ a a))

/-! ## Bookkeeping -/

/-- The row integral of a bounded kernel is integrable. -/
theorem int_row {F : X → X → ℝ} (hF : Bdd F) : Integrable (fun x => ∫ y, F x y ∂μ) μ := by
  obtain ⟨C, hC⟩ := hF.bdd
  exact integrable_of_bdd (measurable_integral_right hF.meas) (C := C)
    (fun x => abs_integral_le fun y => hC x y)

theorem bdd_sq {h : X → X → ℝ} (hh : Bdd h) : Bdd (fun x y => h x y ^ 2) := by
  have := bdd_mul hh hh; simpa [sq] using this

/-- A symmetric kernel composed with itself is its Gram kernel. -/
theorem conv_self_eq_gram {b : X → X → ℝ} (hsym : ∀ x y, b x y = b y x) :
    conv μ b b = gram μ b := by
  funext x z
  unfold conv gram
  congr 1; funext y; rw [hsym y z]

theorem hs_eq_gram_diag (b : X → X → ℝ) : hs μ b = ∫ x, gram μ b x x ∂μ := by
  unfold hs gram
  congr 1; funext x; congr 1; funext y; ring

/-! ## One flip -/

variable {a : X → X → ℝ} {σ τ : X → X}

theorem ev_symm (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) (x y : X) : ev a σ x y = ev a σ y x := by
  have h1 : a y (σ x) = a x (σ y) := by
    rw [hsym y (σ x)]; exact a_flip_left hf hinv x y
  simp only [ev]
  rw [h1, hsym x y]

theorem od_symm (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) (x y : X) : od a σ x y = od a σ y x := by
  have h1 : a y (σ x) = a x (σ y) := by
    rw [hsym y (σ x)]; exact a_flip_left hf hinv x y
  simp only [od]
  rw [h1, hsym x y]

/-- The even part is invariant under a second flip that commutes with the first and leaves `a`
invariant. -/
theorem ev_inv_other (hcomm : ∀ x, σ (τ x) = τ (σ x)) (hinvτ : ∀ x y, a (τ x) (τ y) = a x y)
    (x y : X) : ev a σ (τ x) (τ y) = ev a σ x y := by
  have e1 : a (τ x) (τ y) = a x y := hinvτ x y
  have e2 : a (τ x) (σ (τ y)) = a x (σ y) := by rw [hcomm y]; exact hinvτ x (σ y)
  simp only [ev]
  rw [e1, e2]

theorem ev_ge {c : ℝ} (hc : ∀ x y, c ≤ a x y) (x y : X) : c ≤ ev a σ x y := by
  simp only [ev]
  linarith [hc x y, hc x (σ y)]

/-- **The even sector's trace**: `hs(ev) = (hs(a) + twist)/2`. -/
theorem hs_ev (ha : Bdd a) (hf : Flip μ σ) : hs μ (ev a σ) = (hs μ a + twist μ a σ) / 2 := by
  have hpt : ∀ x, gram μ (ev a σ) x x
      = ((∫ y, a x y ^ 2 ∂μ) + ∫ y, a x y * a x (σ y) ∂μ) / 2 := by
    intro x
    have h1 := diag_add ha hf x
    have h2 := diag_sub ha hf x
    linarith
  have i1 : Integrable (fun x => ∫ y, a x y ^ 2 ∂μ) μ := int_row (bdd_sq ha)
  have i2 : Integrable (fun x => ∫ y, a x y * a x (σ y) ∂μ) μ := int_row (bdd_mul ha (bdd_flip ha hf))
  rw [hs_eq_gram_diag (ev a σ)]
  simp_rw [hpt]
  rw [integral_div, integral_add i1 i2]
  rfl

/-- **The odd sector's trace**: `hs(od) = (hs(a) − twist)/2`. -/
theorem hs_od (ha : Bdd a) (hf : Flip μ σ) : hs μ (od a σ) = (hs μ a - twist μ a σ) / 2 := by
  have hpt : ∀ x, gram μ (od a σ) x x
      = ((∫ y, a x y ^ 2 ∂μ) - ∫ y, a x y * a x (σ y) ∂μ) / 2 := by
    intro x
    have h1 := diag_add ha hf x
    have h2 := diag_sub ha hf x
    linarith
  have i1 : Integrable (fun x => ∫ y, a x y ^ 2 ∂μ) μ := int_row (bdd_sq ha)
  have i2 : Integrable (fun x => ∫ y, a x y * a x (σ y) ∂μ) μ := int_row (bdd_mul ha (bdd_flip ha hf))
  rw [hs_eq_gram_diag (od a σ)]
  simp_rw [hpt]
  rw [integral_div, integral_sub i1 i2]
  rfl

theorem hs_ev_add_od (ha : Bdd a) (hf : Flip μ σ) : hs μ (ev a σ) + hs μ (od a σ) = hs μ a := by
  rw [hs_ev ha hf, hs_od ha hf]; ring

theorem hs_ev_le (ha : Bdd a) (hf : Flip μ σ) : hs μ (ev a σ) ≤ hs μ a := by
  have := hs_ev_add_od ha hf
  linarith [hs_nonneg (μ := μ) (od a σ)]

/-- For a nonnegative kernel the twisted trace is nonnegative, so the even sector carries at least
half the trace. -/
theorem hs_ev_ge_half (ha : Bdd a) (hf : Flip μ σ) (ha0 : ∀ x y, 0 ≤ a x y) :
    hs μ a / 2 ≤ hs μ (ev a σ) := by
  rw [hs_ev ha hf]
  have : 0 ≤ twist μ a σ :=
    integral_nonneg fun x => integral_nonneg fun y => mul_nonneg (ha0 _ _) (ha0 _ _)
  linarith

/-- **The doubled trace splits over the two sectors**: `hs(a ∗ a) = hs(ev ∗ ev) + hs(od ∗ od)`. -/
theorem hs_conv_split (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) :
    hs μ (conv μ a a) = hs μ (conv μ (ev a σ) (ev a σ)) + hs μ (conv μ (od a σ) (od a σ)) := by
  rw [conv_self_eq_gram (ev_symm hsym hf hinv), conv_self_eq_gram (od_symm hsym hf hinv)]
  set Ge := gram μ (ev a σ) with hGe
  set Go := gram μ (od a σ) with hGo
  have bE : Bdd Ge := bdd_gram (bdd_ev ha hf)
  have bO : Bdd Go := bdd_gram (bdd_od ha hf)
  have hin : ∀ x, ∫ z, conv μ a a x z ^ 2 ∂μ = ∫ z, Ge x z ^ 2 ∂μ + ∫ z, Go x z ^ 2 ∂μ := by
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
  unfold hs
  simp_rw [hin]
  exact integral_add (int_row (bdd_sq bE)) (int_row (bdd_sq bO))

/-- **One flip, upper bound**: the defect is at most the even sector's defect plus twice the log of
its inverse share. -/
theorem dd_le_ev (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) (hpos : 0 < hs μ (conv μ (ev a σ) (ev a σ))) :
    dd μ a ≤ dd μ (ev a σ) + 2 * (Real.log (hs μ a) - Real.log (hs μ (ev a σ))) := by
  have hsplit := hs_conv_split ha hsym hf hinv
  have hle : hs μ (conv μ (ev a σ) (ev a σ)) ≤ hs μ (conv μ a a) := by
    rw [hsplit]; linarith [hs_nonneg (μ := μ) (conv μ (od a σ) (od a σ))]
  have := Real.log_le_log hpos hle
  unfold dd
  linarith

/-- **One flip, the odd sector's doubled trace**: `hs(a ∗ a) ≤ hs(ev ∗ ev) + (hs(a) − hs(ev))²`. -/
theorem hs_conv_le_ev_add (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) :
    hs μ (conv μ a a) ≤ hs μ (conv μ (ev a σ) (ev a σ)) + (hs μ a - hs μ (ev a σ)) ^ 2 := by
  have hsplit := hs_conv_split ha hsym hf hinv
  have hod : hs μ (conv μ (od a σ) (od a σ)) ≤ hs μ (od a σ) * hs μ (od a σ) :=
    hs_conv_le_mul (bdd_od ha hf) (bdd_od ha hf)
  have heq : hs μ a - hs μ (ev a σ) = hs μ (od a σ) := by
    have := hs_ev_add_od ha hf; linarith
  rw [hsplit, heq, sq]
  linarith

/-! ## Lower bounds -/

theorem sq_le_hs {b : X → X → ℝ} {c : ℝ} (hb : Bdd b) (hc : 0 ≤ c) (hlow : ∀ x y, c ≤ b x y) :
    c ^ 2 ≤ hs μ b := by
  have hin : ∀ x, c ^ 2 ≤ ∫ z, b x z ^ 2 ∂μ := by
    intro x
    have : ∫ _z, c ^ 2 ∂μ ≤ ∫ z, b x z ^ 2 ∂μ :=
      integral_mono (integrable_const _) (irow (bdd_sq hb) x)
        (fun z => pow_le_pow_left₀ hc (hlow x z) 2)
    have e : ∫ _z, c ^ 2 ∂μ = c ^ 2 := by simp
    linarith
  have : ∫ _x, c ^ 2 ∂μ ≤ ∫ x, ∫ z, b x z ^ 2 ∂μ ∂μ :=
    integral_mono (integrable_const _) (int_row (bdd_sq hb)) hin
  have e : ∫ _x, c ^ 2 ∂μ = c ^ 2 := by simp
  unfold hs
  linarith

theorem conv_low {b : X → X → ℝ} {c : ℝ} (hb : Bdd b) (hc : 0 ≤ c) (hlow : ∀ x y, c ≤ b x y)
    (x z : X) : c * c ≤ conv μ b b x z := by
  obtain ⟨C, hC⟩ := hb.bdd
  have hint : Integrable (fun y => b x y * b y z) μ := by
    refine integrable_of_bdd ((hb.row x).mul (hb.col z)) (C := C * C) (fun y => ?_)
    rw [abs_mul]
    exact mul_le_mul (hC x y) (hC y z) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))
  have : ∫ _y, c * c ∂μ ≤ ∫ y, b x y * b y z ∂μ :=
    integral_mono (integrable_const _) hint
      (fun y => mul_le_mul (hlow x y) (hlow y z) hc (hc.trans (hlow x y)))
  have e : ∫ _y, c * c ∂μ = c * c := by simp
  unfold conv
  linarith

/-- An iterate of a kernel bounded below by `c ≥ 0` is bounded below by `c^{i+1}`. -/
theorem iter_low {k : X → X → ℝ} {c : ℝ} (hk : Bdd k) (hc : 0 ≤ c) (hlow : ∀ x y, c ≤ k x y) :
    ∀ i x y, c ^ (i + 1) ≤ iter μ k i x y
  | 0, x, y => by
    show c ^ (0 + 1) ≤ k x y
    rw [zero_add, pow_one]; exact hlow x y
  | i + 1, x, y => by
    have ih := iter_low hk hc hlow i
    obtain ⟨C, hC⟩ := hk.bdd
    obtain ⟨D, hD⟩ := (hk.iter (μ := μ) i).bdd
    change c ^ (i + 1 + 1) ≤ ∫ z, k x z * iter μ k i z y ∂μ
    have hint : Integrable (fun z => k x z * iter μ k i z y) μ := by
      refine integrable_of_bdd ((hk.row x).mul ((hk.iter (μ := μ) i).col y)) (C := C * D)
        (fun z => ?_)
      rw [abs_mul]
      exact mul_le_mul (hC x z) (hD z y) (abs_nonneg _) ((abs_nonneg _).trans (hC x z))
    have : ∫ _z, c * c ^ (i + 1) ∂μ ≤ ∫ z, k x z * iter μ k i z y ∂μ :=
      integral_mono (integrable_const _) hint
        (fun z => mul_le_mul (hlow x z) (ih z y) (by positivity) (hc.trans (hlow x z)))
    have e : ∫ _z, c * c ^ (i + 1) ∂μ = c * c ^ (i + 1) := by simp
    rw [pow_succ']
    linarith

/-! ## A list of commuting flips -/

/-- The kernel of the sector even under every flip of the list. -/
noncomputable def evL : (X → X → ℝ) → List (X → X) → X → X → ℝ
  | a, [] => a
  | a, σ :: l => evL (ev a σ) l

theorem evL_nil (a : X → X → ℝ) : evL a [] = a := rfl

theorem evL_cons (a : X → X → ℝ) (σ : X → X) (l : List (X → X)) :
    evL a (σ :: l) = evL (ev a σ) l := rfl

variable (μ) in
/-- Measure-preserving involutions that commute pairwise. -/
def Flips (l : List (X → X)) : Prop :=
  (∀ σ ∈ l, Flip μ σ) ∧ ∀ σ ∈ l, ∀ τ ∈ l, ∀ x, σ (τ x) = τ (σ x)

theorem Flips.tail {σ : X → X} {l : List (X → X)} (h : Flips μ (σ :: l)) : Flips μ l :=
  ⟨fun τ hτ => h.1 τ (List.mem_cons_of_mem σ hτ),
    fun τ hτ ρ hρ => h.2 τ (List.mem_cons_of_mem σ hτ) ρ (List.mem_cons_of_mem σ hρ)⟩

/-- A bounded symmetric kernel, invariant under every flip of `l`, bounded below by `c`. -/
structure Adm (l : List (X → X)) (c : ℝ) (a : X → X → ℝ) : Prop where
  bdd : Bdd a
  symm : ∀ x y, a x y = a y x
  inv : ∀ σ ∈ l, ∀ x y, a (σ x) (σ y) = a x y
  low : ∀ x y, c ≤ a x y

theorem Adm.ev {σ : X → X} {l : List (X → X)} {c : ℝ} (hl : Flips μ (σ :: l))
    (ha : Adm (σ :: l) c a) : Adm l c (ev a σ) where
  bdd := bdd_ev ha.bdd (hl.1 σ List.mem_cons_self)
  symm := ev_symm ha.symm (hl.1 σ List.mem_cons_self) (ha.inv σ List.mem_cons_self)
  inv := fun τ hτ => ev_inv_other (hl.2 σ List.mem_cons_self τ (List.mem_cons_of_mem σ hτ))
    (ha.inv τ (List.mem_cons_of_mem σ hτ))
  low := ev_ge ha.low

theorem adm_evL {c : ℝ} : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l → Adm l c a →
    Adm ([] : List (X → X)) c (evL a l)
  | [], a, _, ha => ⟨ha.bdd, ha.symm, fun _ h => by simp at h, ha.low⟩
  | σ :: l, a, hl, ha => adm_evL l (ev a σ) hl.tail (Adm.ev hl ha)

theorem hs_evL_le {c : ℝ} : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l → Adm l c a →
    hs μ (evL a l) ≤ hs μ a
  | [], _, _, _ => le_rfl
  | σ :: l, a, hl, ha =>
    (hs_evL_le l (ev a σ) hl.tail (Adm.ev hl ha)).trans (hs_ev_le ha.bdd (hl.1 σ List.mem_cons_self))

/-- For a kernel bounded below by `c ≥ 0`, the fully even sector carries at least `2^{−|l|}` of the
trace. -/
theorem hs_evL_ge {c : ℝ} (hc : 0 ≤ c) : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l →
    Adm l c a → hs μ a / 2 ^ l.length ≤ hs μ (evL a l)
  | [], a, _, _ => by simp [evL]
  | σ :: l, a, hl, ha => by
    have h1 : hs μ a / 2 ≤ hs μ (ev a σ) :=
      hs_ev_ge_half ha.bdd (hl.1 σ List.mem_cons_self) (fun x y => hc.trans (ha.low x y))
    have h2 := hs_evL_ge hc l (ev a σ) hl.tail (Adm.ev hl ha)
    rw [evL_cons, List.length_cons, pow_succ]
    calc hs μ a / (2 ^ l.length * 2) = (hs μ a / 2) / 2 ^ l.length := by ring
      _ ≤ hs μ (ev a σ) / 2 ^ l.length := by gcongr
      _ ≤ _ := h2

/-- **The defect is at most the fully even sector's defect plus twice the log of its inverse share.** -/
theorem dd_le_evL {c : ℝ} (hc : 0 < c) : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l →
    Adm l c a →
    dd μ a ≤ dd μ (evL a l) + 2 * (Real.log (hs μ a) - Real.log (hs μ (evL a l)))
  | [], a, _, _ => by simp [evL]
  | σ :: l, a, hl, ha => by
    have hf := hl.1 σ List.mem_cons_self
    have hb := Adm.ev hl ha
    have hpos : 0 < hs μ (conv μ (ev a σ) (ev a σ)) := by
      have hlow := conv_low (μ := μ) hb.bdd hc.le hb.low
      have := sq_le_hs (μ := μ) (hb.bdd.conv hb.bdd) (mul_nonneg hc.le hc.le) hlow
      have : 0 < (c * c) ^ 2 := by positivity
      linarith
    have h1 := dd_le_ev ha.bdd ha.symm hf (ha.inv σ List.mem_cons_self) hpos
    have h2 := dd_le_evL hc l (ev a σ) hl.tail hb
    rw [evL_cons]
    linarith

/-- **The doubled trace against the fully even sector**:
`hs(a ∗ a) ≤ hs(e ∗ e) + (hs(a) − hs(e))²`, `e = evL a l`. -/
theorem hs_conv_le_evL {c : ℝ} : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l → Adm l c a →
    hs μ (conv μ a a) ≤ hs μ (conv μ (evL a l) (evL a l)) + (hs μ a - hs μ (evL a l)) ^ 2
  | [], a, _, _ => by simp [evL]
  | σ :: l, a, hl, ha => by
    have hf := hl.1 σ List.mem_cons_self
    have hb := Adm.ev hl ha
    have h1 := hs_conv_le_ev_add ha.bdd ha.symm hf (ha.inv σ List.mem_cons_self)
    have h2 := hs_conv_le_evL l (ev a σ) hl.tail hb
    have hu : 0 ≤ hs μ a - hs μ (ev a σ) := by linarith [hs_ev_le (μ := μ) ha.bdd hf]
    have hv : 0 ≤ hs μ (ev a σ) - hs μ (evL (ev a σ) l) := by
      linarith [hs_evL_le (μ := μ) l (ev a σ) hl.tail hb]
    rw [evL_cons]
    nlinarith [mul_nonneg hu hv]

end MassGap.SectorDefect

#print axioms MassGap.SectorDefect.hs_conv_split
#print axioms MassGap.SectorDefect.hs_ev
#print axioms MassGap.SectorDefect.hs_od
#print axioms MassGap.SectorDefect.dd_le_evL
#print axioms MassGap.SectorDefect.hs_conv_le_evL
#print axioms MassGap.SectorDefect.hs_evL_ge
#print axioms MassGap.SectorDefect.iter_low
