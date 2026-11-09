import Mathlib
import MassGap.HiddenChain
import MassGap.KernelGap

/-!
# MassGap.ChainClosing — closing a hidden-variable chain into a torus, and the gap read on it

Piece 3 of the finite-volume dyadic step, in the abstract setting of `HiddenChain`: a step weight
`0 ≤ w ≤ 1`, symmetric under `x ↔ y`, `a ↦ ι a`, with step kernel `k = kern ν w`, a normalised
eigenfunction `φ` of `k` at eigenvalue `c`, `|c| = ‖K‖`.

The torus of length `2h` (`h = m + 1`) with an insertion `F` local on the first `h` steps is
`Zh m F = ∫ x, chain (m+1+m) (F · k(V_{2h−1}, x)) x`. Splitting at `h` and writing
`k^{∗h} = c^h φ⊗φ + r^{∗h}` (`KernelPower.iter_decomp`):

* `Zh_decomp` — `(Zh F − c^h · Ih F)² ≤ B² · hs(k^{∗h}) · hs(r^{∗h})`, with
  `Ih F = ∫ φ(x) chain h (F · φ(V_h)) x` and `|F| ≤ B`. The closing error is controlled by the
  excited weight of the torus itself, `hs(r^{∗h}) / |c|^{2h}`: no operator norm and no trace class.
* `Ih_sq_le` — `(Ih F)² ≤ B² · hs(k^{∗h})`.
* `Ih_one`, `Ih_single`, `Ih_shift`, `Ih_pair0`, `Ih_pairn` — the vacuum sandwich of the five window
  insertions of the connected pairing, in terms of the half-space vector
  `v(z) = chain R (F₂ · φ(V_R)) z`; the reflected insertion `F₁` is `F₂` read backwards.
* `gap_ineq` — on `L²`, the gap `‖Kⁿ f‖ ≤ ½‖K‖ⁿ‖f‖` on `φ^⊥` gives
  `⟨Kⁿ v, v⟩ ≤ ‖K‖ⁿ (⟨φ,v⟩² + ½(⟨v,v⟩ − ⟨φ,v⟩²))`.
-/

namespace MassGap.ChainClosing

open MeasureTheory Real MassGap.KernelPower MassGap.HiddenChain MassGap.SlabKernelOperator

set_option linter.unusedSectionVars false

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {w : X → Y → X → ℝ}

/-- `Measurable.comp` in applied form. -/
theorem mcomp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (fun x => g (f x)) := hg.comp hf

/-- A jointly measurable two-argument function of two measurable functions. -/
theorem mcomp2 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {g : β → γ → ℝ} (hg : Measurable (Function.uncurry g)) {f₁ : α → β} {f₂ : α → γ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) : Measurable (fun x => g (f₁ x) (f₂ x)) :=
  hg.comp (h₁.prodMk h₂)

/-- The step weight: measurable, `0 ≤ w ≤ 1`. -/
structure Step (w : X → Y → X → ℝ) : Prop where
  meas : WMeas w
  nonneg : ∀ x a y, 0 ≤ w x a y
  le_one : ∀ x a y, |w x a y| ≤ 1

/-- A bounded measurable insertion. -/
structure Ins (F : (ℕ → X) → (ℕ → Y) → ℝ) (B : ℝ) : Prop where
  meas : Measurable (fun q : (ℕ → X) × (ℕ → Y) => F q.1 q.2)
  bdd : ∀ V A, |F V A| ≤ B

theorem Ins.nonneg {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (h : Ins F B) : 0 ≤ B :=
  (abs_nonneg _).trans (h.bdd (fun _ => Classical.arbitrary X) (fun _ => Classical.arbitrary Y))

theorem Ins.mul {F G : (ℕ → X) → (ℕ → Y) → ℝ} {B C : ℝ} (hF : Ins F B) (hG : Ins G C) :
    Ins (fun V A => F V A * G V A) (B * C) :=
  ⟨hF.meas.mul hG.meas, fun V A => abs_mul_le_of (hF.bdd V A) (hG.bdd V A)⟩

theorem Ins.shift {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B) (d : ℕ) :
    Ins (fun V A => F (sshift V d) (sshift A d)) B :=
  ⟨mcomp hF.meas (((measurable_sshift d).comp measurable_fst).prodMk
    ((measurable_sshift d).comp measurable_snd)), fun V A => hF.bdd _ _⟩

theorem Ins.endpt (m : ℕ) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hgb : ∀ z, |g z| ≤ C) :
    Ins (fun V (_ : ℕ → Y) => g (V m)) C :=
  ⟨mcomp hg ((measurable_pi_apply m).comp measurable_fst), fun V _ => hgb _⟩

theorem Ins.one : Ins (X := X) (Y := Y) (fun _ _ => 1) 1 :=
  ⟨measurable_const, fun _ _ => by simp⟩

/-! ## Chains reading their end point -/

section Ends

variable (hS : Step w)

include hS in
theorem measurable_chain_diag (m : ℕ) {G : X → (ℕ → X) → (ℕ → Y) → ℝ}
    (hG : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) => G q.1 q.2.1 q.2.2)) :
    Measurable (fun x => chain μ ν w m (G x) x) :=
  mcomp (measurable_chain (μ := μ) (ν := ν) hS.meas m hG) (measurable_id.prodMk measurable_id)

include hS in
/-- `|chain (m+1) (F · g(V_{m+1})) x| ≤ B ∫ k^{∗(m+1)}(x,z) |g z|`. -/
theorem chain_abs_end (m : ℕ) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B) {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hgb : ∀ z, |g z| ≤ C) (x : X) :
    |chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1))) x|
      ≤ B * ∫ z, iter μ (kern ν w) m x z * |g z| ∂μ := by
  have hB := hF.nonneg
  have hI := hF.mul (Ins.endpt (m + 1) hg hgb)
  have hBg : Measurable (fun z => B * |g z|) := measurable_const.mul hg.abs
  have hA : Ins (fun V (_ : ℕ → Y) => B * |g (V (m + 1))|) (B * C) :=
    ⟨mcomp (g := fun z => B * |g z|) hBg ((measurable_pi_apply (m + 1)).comp measurable_fst),
      fun V _ => by
        rw [abs_mul, abs_of_nonneg hB, abs_abs]
        exact mul_le_mul_of_nonneg_left (hgb _) hB⟩
  have h1 := abs_chain_le_chain_abs (μ := μ) (ν := ν) hS.meas hS.le_one hS.nonneg (m + 1) hI.meas
    hI.bdd x
  have h2 := chain_mono (μ := μ) (ν := ν) hS.meas hS.le_one hS.nonneg (m + 1)
    (G := fun V A => |F V A * g (V (m + 1))|) (H := fun V (_ : ℕ → Y) => B * |g (V (m + 1))|)
    hI.meas.abs hA.meas (fun V A => by rw [abs_abs]; exact hI.bdd V A) hA.bdd
    (fun V A => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hF.bdd V A) (abs_nonneg _)) x
  rw [chain_const_mul] at h2
  have h3 := chain_end_iter (μ := μ) (ν := ν) hS.meas hS.le_one (g := fun z => |g z|) hg.abs
    (Bg := C) (fun z => by rw [abs_abs]; exact hgb z) m x
  rw [h3] at h2
  exact h1.trans h2

end Ends

/-- Cauchy–Schwarz for iterated integrals of bounded kernels. -/
theorem cs_iter {P Q : X → X → ℝ} (hP : Measurable (Function.uncurry P))
    (hQ : Measurable (Function.uncurry Q)) {CP CQ : ℝ} (hPb : ∀ x z, |P x z| ≤ CP)
    (hQb : ∀ x z, |Q x z| ≤ CQ) :
    (∫ x, ∫ z, P x z * Q x z ∂μ ∂μ) ^ 2
      ≤ (∫ x, ∫ z, P x z ^ 2 ∂μ ∂μ) * (∫ x, ∫ z, Q x z ^ 2 ∂μ ∂μ) := by
  have i1 : Integrable (fun p : X × X => P p.1 p.2 * Q p.1 p.2) (μ.prod μ) :=
    integrable_of_bdd (hP.mul hQ) (C := CP * CQ) (fun p => abs_mul_le_of (hPb _ _) (hQb _ _))
  have i2 : Integrable (fun p : X × X => P p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hP.pow_const 2) (C := CP ^ 2) (fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hPb _ _) 2)
  have i3 : Integrable (fun p : X × X => Q p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hQ.pow_const 2) (C := CQ ^ 2) (fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hQb _ _) 2)
  have e1 : ∫ x, ∫ z, P x z * Q x z ∂μ ∂μ = ∫ p, P p.1 p.2 * Q p.1 p.2 ∂(μ.prod μ) :=
    (integral_prod _ i1).symm
  have e2 : ∫ x, ∫ z, P x z ^ 2 ∂μ ∂μ = ∫ p, P p.1 p.2 ^ 2 ∂(μ.prod μ) := (integral_prod _ i2).symm
  have e3 : ∫ x, ∫ z, Q x z ^ 2 ∂μ ∂μ = ∫ p, Q p.1 p.2 ^ 2 ∂(μ.prod μ) := (integral_prod _ i3).symm
  rw [e1, e2, e3]
  exact sq_integral_mul_le i2 i3 i1

section Insert

variable (hS : Step w)

include hS in
/-- **An insertion read at the end of a half-torus, paired with a kernel.** -/
theorem insert_sq_le (m : ℕ) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B)
    {g : X → X → ℝ} (hg : Measurable (Function.uncurry g)) {Cg : ℝ} (hgb : ∀ z x, |g z x| ≤ Cg) :
    (∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ) ^ 2
      ≤ B ^ 2 * hs μ (iter μ (kern ν w) m) * ∫ x, ∫ z, g z x ^ 2 ∂μ ∂μ := by
  have hB := hF.nonneg
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hki := hk.iter (μ := μ) m
  obtain ⟨Ci, hCi⟩ := hki.bdd
  have hgx : ∀ x, Measurable (fun z => g z x) := fun x =>
    mcomp2 hg measurable_id measurable_const
  have hpt : ∀ x, |chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x|
      ≤ B * ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ :=
    fun x => chain_abs_end hS m hF (hgx x) (fun z => hgb z x) x
  have hGm : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) => F q.2.1 q.2.2 * g (q.2.1 (m + 1)) q.1) :=
    (mcomp hF.meas measurable_snd).mul (mcomp2 hg
      ((measurable_pi_apply (m + 1)).comp (measurable_fst.comp measurable_snd)) measurable_fst)
  have hmc := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => F V A * g (V (m + 1)) x) hGm
  have hint1 : Integrable (fun x => chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x) μ :=
    integrable_of_bdd hmc (C := 1 ^ (m + 1) * (B * Cg)) (fun x =>
      abs_chain_le hS.le_one (m + 1) (fun V A => abs_mul_le_of (hF.bdd V A) (hgb _ _)) x)
  have hgs : Measurable (fun p : X × X => g p.2 p.1) := mcomp2 hg measurable_snd measurable_fst
  have hJm : Measurable (Function.uncurry (fun x z => iter μ (kern ν w) m x z * |g z x|)) :=
    hki.meas.mul hgs.abs
  have hJ : Measurable (fun x => ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ) :=
    measurable_integral_right hJm
  have hJb : ∀ x, |B * ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ| ≤ B * (Ci * Cg) := fun x => by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left (abs_integral_le fun z => by
      rw [abs_mul, abs_abs]
      exact mul_le_mul (hCi x z) (hgb z x) (abs_nonneg _) ((abs_nonneg _).trans (hCi x z))) hB
  have habs : |∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ|
      ≤ B * ∫ x, ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ ∂μ := by
    calc _ ≤ ∫ x, |chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, B * ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ ∂μ :=
          integral_mono hint1.abs (integrable_of_bdd (measurable_const.mul hJ) hJb) hpt
      _ = _ := integral_const_mul _ _
  have hcs := cs_iter (μ := μ) (P := fun x z => iter μ (kern ν w) m x z) (Q := fun x z => |g z x|)
    hki.meas hgs.abs hCi (fun x z => by rw [abs_abs]; exact hgb z x)
  have e2 : ∫ x, ∫ z, |g z x| ^ 2 ∂μ ∂μ = ∫ x, ∫ z, g z x ^ 2 ∂μ ∂μ := by simp_rw [sq_abs]
  rw [e2] at hcs
  set S := ∫ x, ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ ∂μ
  calc (∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ) ^ 2
      = |∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (B * S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = B ^ 2 * S ^ 2 := by ring
    _ ≤ B ^ 2 * ((∫ x, ∫ z, iter μ (kern ν w) m x z ^ 2 ∂μ ∂μ) * ∫ x, ∫ z, g z x ^ 2 ∂μ ∂μ) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg B)
    _ = B ^ 2 * hs μ (iter μ (kern ν w) m) * ∫ x, ∫ z, g z x ^ 2 ∂μ ∂μ := by unfold hs; ring

end Insert

/-! ## The torus and its vacuum sandwich -/

/-- The torus of `L + 1` steps with insertion `F`, closed by one step kernel. -/
noncomputable def Zh (μ : Measure X) (ν : Measure Y) (w : X → Y → X → ℝ) (L : ℕ)
    (F : (ℕ → X) → (ℕ → Y) → ℝ) : ℝ :=
  ∫ x, chain μ ν w L (fun V A => F V A * kern ν w (V L) x) x ∂μ

/-- The vacuum sandwich of an insertion over `m + 1` steps. -/
noncomputable def Ih (μ : Measure X) (ν : Measure Y) (w : X → Y → X → ℝ) (φ : X → ℝ) (m : ℕ)
    (F : (ℕ → X) → (ℕ → Y) → ℝ) : ℝ :=
  ∫ x, φ x * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x ∂μ

section Sandwich

variable (hS : Step w) (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν) (hinv : ∀ a, ι (ι a) = a)
  (hsym : ∀ x a y, w x a y = w y (ι a) x)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z)

include hS ι hι hsym in
theorem kern_symm (x y : X) : kern ν w x y = kern ν w y x := by
  unfold kern
  rw [← hι.integral_comp' (fun a => w y a x)]
  congr 1; funext a; rw [hsym]

include hS ι hι hsym hφm hφb hφ1 heig in
/-- **The closing error is the torus's own excited weight.** -/
theorem Zh_decomp (m : ℕ) {L : ℕ} (hL : L = m + 1 + m) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ}
    (hF : Ins F B) (hl : LocalUpTo (m + 1) F) :
    (Zh μ ν w L F - c ^ (m + 1) * Ih μ ν w φ m F) ^ 2
      ≤ B ^ 2 * hs μ (iter μ (kern ν w) m) * hs μ (iter μ (rem (kern ν w) c φ) m) := by
  subst hL
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hks := kern_symm hS ι hι hsym
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hri := hr.iter (μ := μ) m
  obtain ⟨Cr, hCr⟩ := hri.bdd
  -- split at `m + 1`
  have hsplit : ∀ x, chain μ ν w (m + 1 + m) (fun V A => F V A * kern ν w (V (m + 1 + m)) x) x
      = chain μ ν w (m + 1) (fun V A => F V A * iter μ (kern ν w) m (V (m + 1)) x) x := by
    intro x
    have e : (fun V A => F V A * kern ν w (V (m + 1 + m)) x)
        = fun V A => F V A * kern ν w (sshift V (m + 1) m) x := by
      funext V A; simp only [sshift]; rw [show m + (m + 1) = m + 1 + m by omega]
    rw [e, chain_split (m + 1) m (fun (V' : ℕ → X) (_ : ℕ → Y) => kern ν w (V' m) x) x hl]
    simp_rw [chain_end_kern]
  -- the decomposition of the closing kernel
  have hdec : ∀ x, chain μ ν w (m + 1) (fun V A => F V A * iter μ (kern ν w) m (V (m + 1)) x) x
      = (c ^ (m + 1) * φ x) * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x
        + chain μ ν w (m + 1) (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) x := by
    intro x
    have e : (fun V A => F V A * iter μ (kern ν w) m (V (m + 1)) x)
        = fun V A => (c ^ (m + 1) * φ x) * (F V A * φ (V (m + 1)))
          + F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x := by
      funext V A
      rw [iter_decomp hk hks hφm hφb hφ1 heig m]; ring
    have i1 : Ins (fun V A => (c ^ (m + 1) * φ x) * (F V A * φ (V (m + 1)))) (|c ^ (m + 1) * φ x| * (B * Bφ)) :=
      ⟨measurable_const.mul (hF.mul (Ins.endpt (m + 1) hφm hφb)).meas, fun V A => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hF.mul (Ins.endpt (m + 1) hφm hφb)).bdd V A)
          (abs_nonneg _)⟩
    have i2 : Ins (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) (B * Cr) :=
      hF.mul (Ins.endpt (m + 1) (hri.col x) (fun z => hCr z x))
    rw [e, chain_add hS.meas hS.le_one (m + 1) i1.meas i2.meas i1.bdd i2.bdd x, chain_const_mul]
  -- integrate
  have hm1 : Measurable (fun x => (c ^ (m + 1) * φ x)
      * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x) :=
    (measurable_const.mul hφm).mul (measurable_chain' hS.meas (m + 1)
      (hF.mul (Ins.endpt (m + 1) hφm hφb)).meas)
  have hGr : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) =>
      F q.2.1 q.2.2 * iter μ (rem (kern ν w) c φ) m (q.2.1 (m + 1)) q.1) :=
    (mcomp hF.meas measurable_snd).mul (mcomp2 hri.meas
      ((measurable_pi_apply (m + 1)).comp (measurable_fst.comp measurable_snd)) measurable_fst)
  have hm2 := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) hGr
  have hB := hF.nonneg
  have int1 : Integrable (fun x => (c ^ (m + 1) * φ x)
      * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x) μ :=
    integrable_of_bdd hm1 (C := (|c ^ (m + 1)| * Bφ) * (1 ^ (m + 1) * (B * Bφ))) (fun x => by
      refine abs_mul_le_of ?_ (abs_chain_le hS.le_one (m + 1)
        (hF.mul (Ins.endpt (m + 1) hφm hφb)).bdd x)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb x) (abs_nonneg _))
  have int2 : Integrable (fun x => chain μ ν w (m + 1)
      (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) x) μ :=
    integrable_of_bdd hm2 (C := 1 ^ (m + 1) * (B * Cr)) (fun x =>
      abs_chain_le hS.le_one (m + 1) (fun V A => abs_mul_le_of (hF.bdd V A) (hCr _ _)) x)
  have hZ : Zh μ ν w (m + 1 + m) F = c ^ (m + 1) * Ih μ ν w φ m F
      + ∫ x, chain μ ν w (m + 1) (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) x ∂μ := by
    unfold Zh Ih
    simp_rw [hsplit, hdec]
    rw [integral_add int1 int2, ← integral_const_mul]
    congr 1; congr 1; funext x; ring
  rw [hZ, add_sub_cancel_left]
  have hb := insert_sq_le (μ := μ) (ν := ν) hS m hF (g := iter μ (rem (kern ν w) c φ) m) hri.meas hCr
  have hswap : ∫ x, ∫ z, iter μ (rem (kern ν w) c φ) m z x ^ 2 ∂μ ∂μ
      = hs μ (iter μ (rem (kern ν w) c φ) m) := by
    unfold hs
    exact (swap_bdd (F := fun x z => iter μ (rem (kern ν w) c φ) m z x ^ 2)
      ((hri.meas.comp measurable_swap).pow_const 2) (C := Cr ^ 2) (fun x z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCr _ _) 2))
  rw [hswap] at hb
  exact hb

include hS hφm hφb hφ1 in
/-- **The vacuum sandwich is bounded by the torus trace.** -/
theorem Ih_sq_le (m : ℕ) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B) :
    (Ih μ ν w φ m F) ^ 2 ≤ B ^ 2 * hs μ (iter μ (kern ν w) m) := by
  have hg : Measurable (Function.uncurry (fun z x : X => φ z * φ x)) :=
    (hφm.comp measurable_fst).mul (hφm.comp measurable_snd)
  have hb := insert_sq_le (μ := μ) (ν := ν) hS m hF (g := fun z x => φ z * φ x) hg
    (Cg := Bφ * Bφ) (fun z x => abs_mul_le_of (hφb z) (hφb x))
  have e1 : ∫ x, chain μ ν w (m + 1) (fun V A => F V A * (φ (V (m + 1)) * φ x)) x ∂μ
      = Ih μ ν w φ m F := by
    unfold Ih
    congr 1; funext x
    rw [← chain_const_mul]
    congr 1; funext V A; ring
  have e2 : ∫ x, ∫ z, (φ z * φ x) ^ 2 ∂μ ∂μ = 1 := by
    have : ∀ x, ∫ z, (φ z * φ x) ^ 2 ∂μ = φ x ^ 2 := fun x => by
      simp_rw [mul_pow]; rw [integral_mul_const, hφ1, one_mul]
    simp_rw [this]; exact hφ1
  rw [e1, e2, mul_one] at hb
  exact hb

end Sandwich

#print axioms insert_sq_le
#print axioms Zh_decomp
#print axioms Ih_sq_le

end MassGap.ChainClosing
