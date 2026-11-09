import Mathlib
import MassGap.ChainClosing

/-!
# MassGap.ChainReduce — the connected pairing on a closed chain, and its decay from the gap

Continues `ChainClosing`. With `F₂` an insertion local on `R` steps, `F₁` the same insertion read
backwards (`F₁ V A = F₂ (revX R V) (revY ι R A)`), and the half-space vector
`v z = chain R (F₂ · φ(V_R)) z`:

* `Ih_one`, `Ih_single`, `Ih_shift`, `Ih_pair0`, `Ih_pairn` — the vacuum sandwiches over `h` steps of
  `1`, `F₁`, `F₂` shifted by `d`, `F₁ · F₂` shifted by `R`, and `F₁ · F₂` shifted by `n + R`, as
  `c^{…} ⟨φ, v⟩`, `c^{…} ⟨v, v⟩`, `c^{…} ⟨Kⁿ v, v⟩`.
* `gap_ineq` — `⟨Kⁿ v, v⟩ ≤ |c|ⁿ (⟨φ,v⟩² + ½(⟨v,v⟩ − ⟨φ,v⟩²))` from `‖Kⁿ f‖ ≤ ½‖K‖ⁿ‖f‖` on `φ^⊥`.
* `chain_decay` — on the torus of `2h` steps, with `E G = Zh G / Zh 1`:
  `E(F₁·F₂∘S^{n+R}) − E F₁ · E(F₂∘S^{n+R}) ≤ ½ (E(F₁·F₂∘S^R) − E F₁ · E(F₂∘S^R)) + 100 B² √(2s)`,
  `s` the excited weight of the torus, `|F₂| ≤ B`.
-/

namespace MassGap.ChainReduce

open MeasureTheory Real MassGap.KernelPower MassGap.HiddenChain MassGap.SlabKernelOperator
  MassGap.ChainClosing

set_option linter.unusedSectionVars false

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {w : X → Y → X → ℝ}

section Tails

variable {φ : X → ℝ} {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z)

include heig in
theorem chain_tail {r : ℕ} {F : (ℕ → X) → (ℕ → Y) → ℝ} (hl : LocalUpTo r F) {p : ℕ}
    (hrp : r ≤ p) (z : X) :
    chain μ ν w p (fun V A => F V A * φ (V p)) z
      = c ^ (p - r) * chain μ ν w r (fun V A => F V A * φ (V r)) z := by
  obtain ⟨d, rfl⟩ : ∃ d, p = r + d := ⟨p - r, by omega⟩
  have e : (fun V A => F V A * φ (V (r + d)))
      = fun V A => F V A * φ (sshift V r d) := by
    funext V A; simp only [sshift]; rw [Nat.add_comm d r]
  rw [e, chain_split r d (fun (V' : ℕ → X) (_ : ℕ → Y) => φ (V' d)) z hl, Nat.add_sub_cancel_left]
  simp_rw [chain_end_eig heig]
  rw [← chain_const_mul]
  congr 1; funext V A; ring

include heig in
theorem chain_tail_shift {R : ℕ} {F : (ℕ → X) → (ℕ → Y) → ℝ} (hl : LocalUpTo R F) {d p : ℕ}
    (hp : d + R ≤ p) (z : X) :
    chain μ ν w p (fun V A => F (sshift V d) (sshift A d) * φ (V p)) z
      = c ^ (p - d - R) * chain μ ν w d
          (fun V _ => chain μ ν w R (fun V' A' => F V' A' * φ (V' R)) (V d)) z := by
  obtain ⟨q, rfl⟩ : ∃ q, p = d + q := ⟨p - d, by omega⟩
  have e : (fun V A => F (sshift V d) (sshift A d) * φ (V (d + q)))
      = fun V A => (1 : ℝ) * (F (sshift V d) (sshift A d) * φ (sshift V d q)) := by
    funext V A; simp only [sshift, one_mul]; rw [Nat.add_comm q d]
  rw [e, chain_split d q (fun V' A' => F V' A' * φ (V' q)) z (localUpTo_const d 1)]
  have ht : ∀ y, chain μ ν w q (fun V' A' => F V' A' * φ (V' q)) y
      = c ^ (q - R) * chain μ ν w R (fun V' A' => F V' A' * φ (V' R)) y :=
    fun y => chain_tail heig hl (by omega) y
  simp_rw [ht, one_mul]
  rw [chain_const_mul, show d + q - d - R = q - R by omega]

end Tails

/-! ## The pairing identities -/

section Pairing

variable (hS : Step w) (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν) (hinv : ∀ a, ι (ι a) = a)
  (hsym : ∀ x a y, w x a y = w y (ι a) x)

include hS ι hι hinv hsym in
/-- A free chain pairs symmetrically. -/
theorem pair_free (d : ℕ) {g₁ g₂ : X → ℝ} (h₁ : Measurable g₁) (h₂ : Measurable g₂) {B₁ B₂ : ℝ}
    (hb₁ : ∀ z, |g₁ z| ≤ B₁) (hb₂ : ∀ z, |g₂ z| ≤ B₂) :
    ∫ x, g₁ x * chain μ ν w d (fun V _ => g₂ (V d)) x ∂μ
      = ∫ x, g₂ x * chain μ ν w d (fun V _ => g₁ (V d)) x ∂μ := by
  have h := chain_rev (μ := μ) hS.meas hS.le_one ι hι hinv hsym d
    (G := fun _ _ => (1 : ℝ)) (G' := fun _ _ => (1 : ℝ)) measurable_const measurable_const
    (B := 1) (fun _ _ => by simp) (fun _ _ => by simp) (localUpTo_const d 1) (fun _ _ => rfl)
    h₂ h₁ hb₂ hb₁
  simp only [one_mul] at h
  exact h

end Pairing

section Values

variable (hS : Step w) (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν) (hinv : ∀ a, ι (ι a) = a)
  (hsym : ∀ x a y, w x a y = w y (ι a) x)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z)
  {R : ℕ} {F₁ F₂ : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF₁ : Ins F₁ B) (hF₂ : Ins F₂ B)
  (hl₁ : LocalUpTo R F₁) (hl₂ : LocalUpTo R F₂)
  (hrev : ∀ V A, F₁ V A = F₂ (revX R V) (revY ι R A))

/-- The half-space vector. -/
noncomputable def vec (μ : Measure X) (ν : Measure Y) (w : X → Y → X → ℝ) (φ : X → ℝ) (R : ℕ)
    (F : (ℕ → X) → (ℕ → Y) → ℝ) : X → ℝ :=
  fun z => chain μ ν w R (fun V A => F V A * φ (V R)) z

include hS hφm hφb hF₂ in
theorem measurable_vec : Measurable (vec μ ν w φ R F₂) :=
  measurable_chain' hS.meas R (hF₂.mul (Ins.endpt R hφm hφb)).meas

include hS hφm hφb hF₂ in
theorem abs_vec_le (z : X) : |vec μ ν w φ R F₂ z| ≤ B * Bφ := by
  have := abs_chain_le (μ := μ) (ν := ν) hS.le_one R (hF₂.mul (Ins.endpt R hφm hφb)).bdd z
  unfold vec; simpa using this

include hS ι hι hinv hsym hφm hφb hF₁ hF₂ hl₂ hrev in
/-- Reading the reflected insertion backwards. -/
theorem pair_rev {g : X → ℝ} (hg : Measurable g) {Bg : ℝ} (hgb : ∀ z, |g z| ≤ Bg) :
    ∫ x, φ x * chain μ ν w R (fun V A => F₁ V A * g (V R)) x ∂μ
      = ∫ x, g x * vec μ ν w φ R F₂ x ∂μ := by
  have h := chain_rev (μ := μ) hS.meas hS.le_one ι hι hinv hsym R (G := F₂) (G' := F₁)
    hF₂.meas hF₁.meas hF₂.bdd hF₁.bdd hl₂ hrev (g := φ) (h := g) hφm hg hφb hgb
  exact h.symm

include heig in
theorem Ih_one (hφ1' : ∫ x, φ x ^ 2 ∂μ = 1) (m : ℕ) :
    Ih μ ν w φ m (fun _ _ => 1) = c ^ (m + 1) := by
  unfold Ih
  simp_rw [one_mul, chain_end_eig heig]
  have : (fun x => φ x * (c ^ (m + 1) * φ x)) = fun x => c ^ (m + 1) * φ x ^ 2 := by
    funext x; ring
  rw [this, integral_const_mul, hφ1', mul_one]

include hS ι hι hinv hsym hφm hφb heig hF₁ hF₂ hl₁ hl₂ hrev in
theorem Ih_single (m : ℕ) (hR : R ≤ m + 1) :
    Ih μ ν w φ m F₁ = c ^ (m + 1 - R) * ∫ x, φ x * vec μ ν w φ R F₂ x ∂μ := by
  unfold Ih
  simp_rw [chain_tail heig hl₁ hR]
  have e : (fun x => φ x * (c ^ (m + 1 - R) * chain μ ν w R (fun V A => F₁ V A * φ (V R)) x))
      = fun x => c ^ (m + 1 - R) * (φ x * chain μ ν w R (fun V A => F₁ V A * φ (V R)) x) := by
    funext x; ring
  rw [e, integral_const_mul, pair_rev hS ι hι hinv hsym hφm hφb hF₁ hF₂ hl₂ hrev hφm hφb]

include hS ι hι hinv hsym hφm hφb heig hF₂ hl₂ in
theorem Ih_shift (m d : ℕ) (hd : d + R ≤ m + 1) :
    Ih μ ν w φ m (fun V A => F₂ (sshift V d) (sshift A d))
      = c ^ (m + 1 - R) * ∫ x, φ x * vec μ ν w φ R F₂ x ∂μ := by
  unfold Ih
  simp_rw [chain_tail_shift heig hl₂ hd]
  have e : ∀ x, φ x * (c ^ (m + 1 - d - R) * chain μ ν w d
        (fun V _ => chain μ ν w R (fun V' A' => F₂ V' A' * φ (V' R)) (V d)) x)
      = c ^ (m + 1 - d - R) * (φ x * chain μ ν w d (fun V _ => vec μ ν w φ R F₂ (V d)) x) := by
    intro x; unfold vec; ring
  simp_rw [e]
  rw [integral_const_mul, pair_free hS ι hι hinv hsym d hφm (measurable_vec hS hφm hφb hF₂) hφb
    (abs_vec_le hS hφm hφb hF₂)]
  simp_rw [chain_end_eig heig]
  have e2 : (fun x => vec μ ν w φ R F₂ x * (c ^ d * φ x))
      = fun x => c ^ d * (φ x * vec μ ν w φ R F₂ x) := by funext x; ring
  rw [e2, integral_const_mul, ← mul_assoc, ← pow_add, show m + 1 - d - R + d = m + 1 - R by omega]

include hS ι hι hinv hsym hφm hφb heig hF₁ hF₂ hl₁ hl₂ hrev in
theorem Ih_pair0 (m : ℕ) (hR : R + R ≤ m + 1) :
    Ih μ ν w φ m (fun V A => F₁ V A * F₂ (sshift V R) (sshift A R))
      = c ^ (m + 1 - R - R) * ∫ x, vec μ ν w φ R F₂ x * vec μ ν w φ R F₂ x ∂μ := by
  unfold Ih
  obtain ⟨q, hq⟩ : ∃ q, m + 1 = R + q := ⟨m + 1 - R, by omega⟩
  have e : (fun V A => F₁ V A * F₂ (sshift V R) (sshift A R) * φ (V (m + 1)))
      = fun V A => F₁ V A * (F₂ (sshift V R) (sshift A R) * φ (sshift V R q)) := by
    funext V A
    have : φ (V (m + 1)) = φ (sshift V R q) := by simp only [sshift]; rw [hq, Nat.add_comm q R]
    rw [this]; ring
  have hs : ∀ x, chain μ ν w (m + 1) (fun V A => F₁ V A * F₂ (sshift V R) (sshift A R)
        * φ (V (m + 1))) x
      = c ^ (q - R) * chain μ ν w R (fun V A => F₁ V A * vec μ ν w φ R F₂ (V R)) x := by
    intro x
    rw [e, hq, chain_split R q (fun V' A' => F₂ V' A' * φ (V' q)) x hl₁]
    have ht : ∀ y, chain μ ν w q (fun V' A' => F₂ V' A' * φ (V' q)) y
        = c ^ (q - R) * vec μ ν w φ R F₂ y := fun y => chain_tail heig hl₂ (by omega) y
    simp_rw [ht]
    rw [← chain_const_mul]
    congr 1; funext V A; ring
  simp_rw [hs]
  have e2 : (fun x => φ x * (c ^ (q - R) * chain μ ν w R
        (fun V A => F₁ V A * vec μ ν w φ R F₂ (V R)) x))
      = fun x => c ^ (q - R) * (φ x * chain μ ν w R
        (fun V A => F₁ V A * vec μ ν w φ R F₂ (V R)) x) := by funext x; ring
  rw [e2, integral_const_mul, pair_rev hS ι hι hinv hsym hφm hφb hF₁ hF₂ hl₂ hrev
    (measurable_vec hS hφm hφb hF₂) (abs_vec_le hS hφm hφb hF₂), show q - R = m + 1 - R - R by omega]

include hS ι hι hinv hsym hφm hφb heig hF₁ hF₂ hl₁ hl₂ hrev in
theorem Ih_pairn (m n : ℕ) (hR : R + n + R ≤ m + 1) :
    Ih μ ν w φ m (fun V A => F₁ V A * F₂ (sshift V (n + R)) (sshift A (n + R)))
      = c ^ (m + 1 - R - n - R) * ∫ x, chain μ ν w n (fun V _ => vec μ ν w φ R F₂ (V n)) x
          * vec μ ν w φ R F₂ x ∂μ := by
  unfold Ih
  obtain ⟨q, hq⟩ : ∃ q, m + 1 = R + q := ⟨m + 1 - R, by omega⟩
  have e : (fun V A => F₁ V A * F₂ (sshift V (n + R)) (sshift A (n + R)) * φ (V (m + 1)))
      = fun V A => F₁ V A * (F₂ (sshift (sshift V R) n) (sshift (sshift A R) n)
          * φ (sshift V R q)) := by
    funext V A
    have : φ (V (m + 1)) = φ (sshift V R q) := by simp only [sshift]; rw [hq, Nat.add_comm q R]
    rw [this, sshift_sshift, sshift_sshift]; ring
  have hKm : Measurable (fun y => chain μ ν w n (fun V _ => vec μ ν w φ R F₂ (V n)) y) :=
    measurable_chain' hS.meas n (Ins.endpt n (measurable_vec hS hφm hφb hF₂)
      (abs_vec_le hS hφm hφb hF₂)).meas
  have hKb : ∀ y, |chain μ ν w n (fun V _ => vec μ ν w φ R F₂ (V n)) y| ≤ 1 ^ n * (B * Bφ) :=
    fun y => abs_chain_le hS.le_one n (Ins.endpt n (measurable_vec hS hφm hφb hF₂)
      (abs_vec_le hS hφm hφb hF₂)).bdd y
  have hs : ∀ x, chain μ ν w (m + 1) (fun V A => F₁ V A * F₂ (sshift V (n + R)) (sshift A (n + R))
        * φ (V (m + 1))) x
      = c ^ (q - n - R) * chain μ ν w R (fun V A => F₁ V A
          * chain μ ν w n (fun V' _ => vec μ ν w φ R F₂ (V' n)) (V R)) x := by
    intro x
    rw [e, hq, chain_split R q (fun V' A' => F₂ (sshift V' n) (sshift A' n) * φ (V' q)) x hl₁]
    have ht : ∀ y, chain μ ν w q (fun V' A' => F₂ (sshift V' n) (sshift A' n) * φ (V' q)) y
        = c ^ (q - n - R) * chain μ ν w n (fun V' _ => vec μ ν w φ R F₂ (V' n)) y :=
      fun y => chain_tail_shift heig hl₂ (by omega) y
    simp_rw [ht]
    rw [← chain_const_mul]
    congr 1; funext V A; ring
  simp_rw [hs]
  have e2 : (fun x => φ x * (c ^ (q - n - R) * chain μ ν w R (fun V A => F₁ V A
        * chain μ ν w n (fun V' _ => vec μ ν w φ R F₂ (V' n)) (V R)) x))
      = fun x => c ^ (q - n - R) * (φ x * chain μ ν w R (fun V A => F₁ V A
        * chain μ ν w n (fun V' _ => vec μ ν w φ R F₂ (V' n)) (V R)) x) := by funext x; ring
  rw [e2, integral_const_mul, pair_rev hS ι hι hinv hsym hφm hφb hF₁ hF₂ hl₂ hrev hKm hKb,
    show q - n - R = m + 1 - R - n - R by omega]

end Values

/-! ## The gap on the half-space vector -/

section Gap

variable (hS : Step w)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z)

/-- The step kernel's operator. -/
noncomputable def Kop (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hS : Step (X := X) (Y := Y) w) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  kernelCLM (kern ν w) 1 (measurable_kern hS.meas) zero_le_one (abs_kern_le hS.le_one) μ μ

include hS in
theorem Kpow_coe {v : X → ℝ} (hv : Measurable v) {Bv : ℝ} (hvb : ∀ z, |v z| ≤ Bv) :
    ∀ n : ℕ, (((Kop μ ν hS) ^ n) ((MemLp.of_bound hv.aestronglyMeasurable Bv
        (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hvb z)).toLp v)
        : X → ℝ) =ᵐ[μ] fun x => chain μ ν w n (fun V _ => v (V n)) x
  | 0 => by
    rw [pow_zero, ContinuousLinearMap.one_apply]
    exact (MemLp.of_bound hv.aestronglyMeasurable Bv
        (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hvb z)).coeFn_toLp
  | n + 1 => by
    have ih := Kpow_coe hv hvb n
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    filter_upwards [coeFn_kernelCLM (kern ν w) 1 (measurable_kern hS.meas) zero_le_one
      (abs_kern_le hS.le_one) μ μ (((Kop μ ν hS) ^ n) ((MemLp.of_bound hv.aestronglyMeasurable Bv
        (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hvb z)).toLp v))]
      with x hx
    rw [show (Kop μ ν hS) = kernelCLM (kern ν w) 1 (measurable_kern hS.meas) zero_le_one
      (abs_kern_le hS.le_one) μ μ from rfl] at *
    rw [hx, KernelPower.kernelFun_congr ih x, chain_end_succ]
    rfl

include hS hφm hφb hφ1 heig in
/-- **The gap read on the half-space vector.** -/
theorem gap_ineq (hsym : ∀ x y, kern ν w x y = kern ν w y x) {n : ℕ} (hne : Even n)
    (hnorm : |c| = ‖Kop μ ν hS‖)
    (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
      ‖((Kop μ ν hS) ^ n) f‖ ≤ 1 / 2 * ‖Kop μ ν hS‖ ^ n * ‖f‖)
    {v : X → ℝ} (hv : Measurable v) {Bv : ℝ} (hvb : ∀ z, |v z| ≤ Bv) :
    ∫ x, chain μ ν w n (fun V _ => v (V n)) x * v x ∂μ
      ≤ |c| ^ n * ((∫ x, φ x * v x ∂μ) ^ 2
        + 1 / 2 * (∫ x, v x * v x ∂μ - (∫ x, φ x * v x ∂μ) ^ 2)) := by
  set K := Kop μ ν hS
  have hmem : MemLp v 2 μ := MemLp.of_bound hv.aestronglyMeasurable Bv
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hvb z)
  set Vv : Lp ℝ 2 μ := hmem.toLp v
  set Φ : Lp ℝ 2 μ := KernelGap.vac (μ := μ) hφm hφb
  have hΦ1 : ‖Φ‖ = 1 := KernelGap.norm_vac hφm hφb hφ1
  have hsa : ∀ u w', inner ℝ (K u) w' = inner ℝ u (K w') := fun u w' =>
    (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm (kern ν w) 1
      (measurable_kern hS.meas) zero_le_one (abs_kern_le hS.le_one) μ hsym).isSymmetric u w'
  have hKΦ : K Φ = c • Φ := KernelGap.K_vac _ _ _ hφm hφb heig
  have hKnΦ : (K ^ n) Φ = |c| ^ n • Φ := by
    have : ∀ p : ℕ, (K ^ p) Φ = c ^ p • Φ := by
      intro p
      induction p with
      | zero => simp
      | succ p ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hKΦ, smul_smul,
          pow_succ]
    rw [this n, ← Even.pow_abs hne c]
  -- the three integrals as inner products
  have ha : inner ℝ Vv Φ = ∫ x, φ x * v x ∂μ := by
    rw [KernelGap.inner_vac]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
  have hA : inner ℝ Vv Vv = ∫ x, v x * v x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]; simp; ring
  have hB : inner ℝ Vv ((K ^ n) Vv) = ∫ x, chain μ ν w n (fun V _ => v (V n)) x * v x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp, Kpow_coe (μ := μ) (ν := ν) hS hv hvb n] with x hx hy
    rw [hx]
    change inner ℝ (v x) ((((K ^ n) Vv : Lp ℝ 2 μ) : X → ℝ) x) = _
    rw [hy]; simp [mul_comm]
  set a := inner ℝ Vv Φ
  set f := Vv - a • Φ
  have hΦΦ : inner ℝ Φ Φ = 1 := by rw [real_inner_self_eq_norm_sq, hΦ1, one_pow]
  have hf : inner ℝ f Φ = 0 := by
    simp only [f, inner_sub_left, real_inner_smul_left, hΦΦ, a]; ring
  have hfΦ : inner ℝ Φ f = 0 := by rw [real_inner_comm]; exact hf
  have hKf : inner ℝ Φ ((K ^ n) f) = 0 := by
    rw [← KernelGap.pow_symm hsa n, hKnΦ, real_inner_smul_left, hfΦ, mul_zero]
  have hdecomp : inner ℝ Vv ((K ^ n) Vv) = inner ℝ f ((K ^ n) f) + a ^ 2 * |c| ^ n := by
    have hV : Vv = f + a • Φ := by simp [f]
    rw [hV, map_add, map_smul, hKnΦ, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, hf, hKf, hΦΦ]
    ring
  have hnormf : ‖f‖ ^ 2 = inner ℝ Vv Vv - a ^ 2 := by
    have hV : Vv = f + a • Φ := by simp [f]
    rw [← real_inner_self_eq_norm_sq]
    conv_rhs => rw [hV]
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, hf, hfΦ, hΦΦ]
    ring
  have hgf := hgap f hf
  have hle : inner ℝ f ((K ^ n) f) ≤ |c| ^ n * (1 / 2 * ‖f‖ ^ 2) := by
    calc inner ℝ f ((K ^ n) f) ≤ ‖f‖ * ‖(K ^ n) f‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * (1 / 2 * ‖K‖ ^ n * ‖f‖) := mul_le_mul_of_nonneg_left hgf (norm_nonneg _)
      _ = |c| ^ n * (1 / 2 * ‖f‖ ^ 2) := by rw [← hnorm]; ring
  rw [← hB, hdecomp, ← ha, ← hA]
  rw [hnormf] at hle
  nlinarith [hle]

end Gap

#print axioms Ih_pairn
#print axioms Ih_shift
#print axioms gap_ineq

end MassGap.ChainReduce
