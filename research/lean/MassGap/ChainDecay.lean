import Mathlib
import MassGap.ChainReduce

/-!
# MassGap.ChainDecay — the connected pairing on a closed chain decays by the gap

`chain_decay`: on the closed chain of `2h` steps (`h = m + 1` even), with `E G = Zh G / Zh 1`, an
insertion `F₂` local on `R` steps (`R` even, `2R + n ≤ h`, `|F₂| ≤ B`, `B ≥ 1`) and its reflection
`F₁`, and the transfer gap `‖Kⁿ f‖ ≤ ½‖K‖ⁿ‖f‖` on the vacuum complement (`n` even):

    E(F₁·F₂∘Sⁿ⁺ᴿ) − E F₁·E(F₂∘Sⁿ⁺ᴿ) ≤ ½ (E(F₁·F₂∘Sᴿ) − E F₁·E(F₂∘Sᴿ)) + 100 B² √(2s),

where `s` is the excited weight of the chain, `hs(r^{∗h}) = s |c|^{2h}`, `s ≤ 1/8`.
-/

namespace MassGap.ChainDecay

open MeasureTheory Real MassGap.KernelPower MassGap.HiddenChain MassGap.SlabKernelOperator
  MassGap.ChainClosing MassGap.ChainReduce

set_option linter.unusedSectionVars false

/-! ## Real-number bookkeeping -/

theorem ratio_close {Z₁ Z M Λ e₁ e η B : ℝ} (hΛ : 0 < Λ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hZ₁ : Z₁ = Λ + e₁) (hZ : Z = Λ * M + e) (he₁ : |e₁| ≤ Λ * η) (he : |e| ≤ B * (Λ * η))
    (hM : |M| ≤ 2 * B) : |Z / Z₁ - M| ≤ 6 * B * η := by
  have hB : 0 ≤ B := by have := (abs_nonneg M).trans hM; linarith
  have hZ₁pos : Λ / 2 ≤ Z₁ := by
    rw [hZ₁]; have := neg_abs_le e₁; nlinarith
  have hZ₁p : 0 < Z₁ := by linarith
  have key : Z / Z₁ - M = (e - M * e₁) / Z₁ := by
    rw [eq_div_iff hZ₁p.ne', sub_mul, div_mul_cancel₀ _ hZ₁p.ne', hZ, hZ₁]; ring
  rw [key, abs_div, abs_of_pos hZ₁p, div_le_iff₀ hZ₁p]
  have h1 : |e - M * e₁| ≤ 3 * B * (Λ * η) := by
    calc |e - M * e₁| ≤ |e| + |M * e₁| := abs_sub _ _
      _ ≤ B * (Λ * η) + 2 * B * (Λ * η) := by
          rw [abs_mul]
          exact add_le_add he (mul_le_mul hM he₁ (abs_nonneg _) (by positivity))
      _ = 3 * B * (Λ * η) := by ring
  have h2 : 3 * B * (Λ * η) ≤ 6 * B * η * Z₁ := by
    have := mul_le_mul_of_nonneg_left hZ₁pos (by positivity : (0 : ℝ) ≤ 6 * B * η)
    nlinarith
  linarith

theorem combine {a A Bv E12 E1 E2 E10 E0 B η : ℝ} (hB : 0 ≤ B) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hgap : Bv ≤ a ^ 2 + 1 / 2 * (A - a ^ 2)) (ha : |a| ≤ 2 * B)
    (d12 : |E12 - Bv| ≤ 6 * (B * B) * η) (d10 : |E10 - A| ≤ 6 * (B * B) * η)
    (d1 : |E1 - a| ≤ 6 * B * η) (d2 : |E2 - a| ≤ 6 * B * η) (d0 : |E0 - a| ≤ 6 * B * η) :
    E12 - E1 * E2 ≤ 1 / 2 * (E10 - E1 * E0) + 100 * B ^ 2 * η := by
  have key : E12 - E1 * E2 - 1 / 2 * (E10 - E1 * E0)
      = (Bv - a ^ 2 - 1 / 2 * (A - a ^ 2)) + (E12 - Bv) - 1 / 2 * (E10 - A) - a * (E2 - a)
        - 1 / 2 * ((E1 - a) * a) - (E1 - a) * (E2 - a) + 1 / 2 * (a * (E0 - a))
        + 1 / 2 * ((E1 - a) * (E0 - a)) := by ring
  have pb : ∀ {u v U V : ℝ}, |u| ≤ U → |v| ≤ V → |u * v| ≤ U * V := fun hu hv =>
    abs_mul_le_of hu hv
  have q1 := pb ha d2
  have q2 := pb d1 ha
  have q3 := pb d1 d2
  have q4 := pb ha d0
  have q5 := pb d1 d0
  have hη2 : η * η ≤ 1 / 2 * η := by nlinarith
  have r3 : 6 * B * η * (6 * B * η) ≤ 18 * B ^ 2 * η := by nlinarith [sq_nonneg B]
  have a1 := le_abs_self (E12 - Bv)
  have a2 := neg_abs_le (E10 - A)
  have a3 := neg_abs_le (a * (E2 - a))
  have a4 := neg_abs_le ((E1 - a) * a)
  have a5 := neg_abs_le ((E1 - a) * (E2 - a))
  have a6 := le_abs_self (a * (E0 - a))
  have a7 := le_abs_self ((E1 - a) * (E0 - a))
  have e1 : 2 * B * (6 * B * η) = 12 * B ^ 2 * η := by ring
  have e2 : 6 * B * η * (2 * B) = 12 * B ^ 2 * η := by ring
  have e3 : 6 * (B * B) * η = 6 * B ^ 2 * η := by ring
  have hpos : 0 ≤ B ^ 2 * η := by positivity
  linarith

/-! ## The decay on a closed chain -/

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {w : X → Y → X → ℝ}

theorem LocalUpTo.shift {R : ℕ} {F : (ℕ → X) → (ℕ → Y) → ℝ} (h : LocalUpTo R F) (d : ℕ) :
    LocalUpTo (d + R) (fun V A => F (sshift V d) (sshift A d)) :=
  fun V V' A A' hV hA => h _ _ _ _ (fun i hi => hV (i + d) (by omega))
    (fun i hi => hA (i + d) (by omega))

/-- The torus expectation of an insertion. -/
noncomputable def Eh (μ : Measure X) (ν : Measure Y) (w : X → Y → X → ℝ) (L : ℕ)
    (G : (ℕ → X) → (ℕ → Y) → ℝ) : ℝ :=
  Zh μ ν w L G / Zh μ ν w L (fun _ _ => 1)

section Decay

variable (hS : Step w) (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν) (hinv : ∀ a, ι (ι a) = a)
  (hsym : ∀ x a y, w x a y = w y (ι a) x)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z)
  (hc0 : c ≠ 0) (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs8 : s ≤ 1 / 8)
  (hsdef : hs μ (iter μ (rem (kern ν w) c φ) m) = s * |c| ^ (2 * (m + 1)))
  (hhe : Even (m + 1)) {L : ℕ} (hL : L = m + 1 + m)

include hS ι hι hsym hφm hφb hφ1 heig hc0 hs0 hs8 hsdef hhe hL in
/-- Each insertion's torus expectation is its normalised vacuum sandwich up to `6 B √(2s)`. -/
theorem E_close {G : (ℕ → X) → (ℕ → Y) → ℝ} {BG : ℝ} (hG : Ins G BG)
    (hl : LocalUpTo (m + 1) G) :
    |Eh μ ν w L G - c ^ (m + 1) * Ih μ ν w φ m G / |c| ^ (2 * (m + 1))|
      ≤ 6 * BG * Real.sqrt (2 * s) ∧
    |c ^ (m + 1) * Ih μ ν w φ m G / |c| ^ (2 * (m + 1))| ≤ 2 * BG := by
  set h := m + 1 with hh
  set lam := |c| with hlam
  have hlp : 0 < lam := abs_pos.mpr hc0
  have hBG := hG.nonneg
  set η := Real.sqrt (2 * s) with hηdef
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hηsq : η ^ 2 = 2 * s := Real.sq_sqrt (by linarith)
  have hη : η ≤ 1 / 2 := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hks := kern_symm hS ι hι hsym
  have hpow : c ^ (2 * h) = lam ^ (2 * h) := (Even.pow_abs ⟨h, by ring⟩ c).symm
  have hsI : hs μ (iter μ (kern ν w) m) = lam ^ (2 * h) * (1 + s) := by
    rw [hs_iter_decomp (μ := μ) hk hks hφm hφb hφ1 heig m, ← hh, hpow, hsdef]; ring
  have hL2 : 0 < lam ^ (2 * h) := pow_pos hlp _
  have hL2' : lam ^ (2 * h) ≠ 0 := hL2.ne'
  have hch : c ^ h * c ^ h = lam ^ (2 * h) := by rw [← pow_add, ← two_mul, hpow]
  have hlh : lam ^ h * lam ^ h = lam ^ (2 * h) := by rw [← pow_add, ← two_mul]
  -- the error of `G` and of `1`
  have errOf : ∀ {G' : (ℕ → X) → (ℕ → Y) → ℝ} {B' : ℝ}, Ins G' B' → LocalUpTo (m + 1) G' →
      |Zh μ ν w L G' - c ^ h * Ih μ ν w φ m G'| ≤ B' * (lam ^ (2 * h) * η) := by
    intro G' B' hG' hl'
    have hB' := hG'.nonneg
    have hd := Zh_decomp hS ι hι hsym hφm hφb hφ1 heig m hL hG' hl'
    rw [hsI, hsdef] at hd
    have hle : B' ^ 2 * (lam ^ (2 * h) * (1 + s)) * (s * lam ^ (2 * h))
        ≤ (B' * (lam ^ (2 * h) * η)) ^ 2 := by
      have : (B' * (lam ^ (2 * h) * η)) ^ 2 = B' ^ 2 * (lam ^ (2 * h)) ^ 2 * (2 * s) := by
        rw [← hηsq]; ring
      rw [this]
      have hss : (1 + s) * s ≤ 2 * s := by nlinarith
      have := mul_le_mul_of_nonneg_left hss (by positivity : (0 : ℝ) ≤ B' ^ 2 * (lam ^ (2 * h)) ^ 2)
      nlinarith
    have := hd.trans hle
    rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ B' * (lam ^ (2 * h) * η))] at this
    exact this
  have ihOf : ∀ {G' : (ℕ → X) → (ℕ → Y) → ℝ} {B' : ℝ}, Ins G' B' →
      |Ih μ ν w φ m G'| ≤ 2 * B' * lam ^ h := by
    intro G' B' hG'
    have hB' := hG'.nonneg
    have hd := Ih_sq_le hS hφm hφb hφ1 m hG' (μ := μ) (ν := ν)
    rw [hsI] at hd
    have hle : B' ^ 2 * (lam ^ (2 * h) * (1 + s)) ≤ (2 * B' * lam ^ h) ^ 2 := by
      have : (2 * B' * lam ^ h) ^ 2 = 4 * B' ^ 2 * lam ^ (2 * h) := by rw [← hlh]; ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (show 1 + s ≤ 4 by linarith)
        (by positivity : (0 : ℝ) ≤ B' ^ 2 * lam ^ (2 * h))
      nlinarith
    have := hd.trans hle
    rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * B' * lam ^ h)] at this
    exact this
  have hM : |c ^ h * Ih μ ν w φ m G / lam ^ (2 * h)| ≤ 2 * BG := by
    rw [abs_div, abs_mul, abs_pow, ← hlam, abs_of_pos hL2, div_le_iff₀ hL2]
    have := mul_le_mul_of_nonneg_left (ihOf hG) (pow_nonneg (abs_nonneg c) h)
    rw [← hlam] at this
    calc lam ^ h * |Ih μ ν w φ m G| ≤ lam ^ h * (2 * BG * lam ^ h) := this
      _ = 2 * BG * lam ^ (2 * h) := by rw [← hlh]; ring
  refine ⟨?_, hM⟩
  have hI1 := Ih_one heig hφ1 m (μ := μ) (ν := ν)
  unfold Eh
  refine ratio_close hL2 hη0 hη (e₁ := Zh μ ν w L (fun _ _ => 1) - lam ^ (2 * h))
    (e := Zh μ ν w L G - c ^ h * Ih μ ν w φ m G) (by ring) ?_ ?_ ?_ hM
  · field_simp; ring
  · have := errOf Ins.one (localUpTo_const (m + 1) 1)
    rw [hI1, ← pow_add, ← two_mul, hpow, one_mul] at this
    exact this
  · exact errOf hG hl

include hS ι hι hinv hsym hφm hφb hφ1 heig hc0 hs0 hs8 hsdef hhe hL in
/-- **The connected pairing on a closed chain decays by the gap.** -/
theorem chain_decay {n : ℕ} (hne : Even n) (hnorm : |c| = ‖Kop μ ν hS‖)
    (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
      ‖((Kop μ ν hS) ^ n) f‖ ≤ 1 / 2 * ‖Kop μ ν hS‖ ^ n * ‖f‖)
    {R : ℕ} (hRe : Even R) (hwin : R + n + R ≤ m + 1)
    {F₁ F₂ : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF₁ : Ins F₁ B) (hF₂ : Ins F₂ B)
    (hl₁ : LocalUpTo R F₁) (hl₂ : LocalUpTo R F₂)
    (hrev : ∀ V A, F₁ V A = F₂ (revX R V) (revY ι R A)) :
    Eh μ ν w L (fun V A => F₁ V A * F₂ (sshift V (n + R)) (sshift A (n + R)))
        - Eh μ ν w L F₁ * Eh μ ν w L (fun V A => F₂ (sshift V (n + R)) (sshift A (n + R)))
      ≤ 1 / 2 * (Eh μ ν w L (fun V A => F₁ V A * F₂ (sshift V R) (sshift A R))
          - Eh μ ν w L F₁ * Eh μ ν w L (fun V A => F₂ (sshift V R) (sshift A R)))
        + 100 * B ^ 2 * Real.sqrt (2 * s) := by
  have hB := hF₂.nonneg
  have hlp : 0 < |c| := abs_pos.mpr hc0
  have hl0 : |c| ≠ 0 := hlp.ne'
  have hη0 : 0 ≤ Real.sqrt (2 * s) := Real.sqrt_nonneg _
  have hη : Real.sqrt (2 * s) ≤ 1 / 2 := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hks := kern_symm hS ι hι hsym (ν := ν)
  obtain ⟨r, hr⟩ := hRe
  obtain ⟨n2, hn2⟩ := hne
  obtain ⟨h2, hh2⟩ := hhe
  -- locality and bounds of the five insertions
  have lS : ∀ d, d + R ≤ m + 1 → LocalUpTo (m + 1) (fun V A => F₂ (sshift V d) (sshift A d)) :=
    fun d hd => (LocalUpTo.shift hl₂ d).mono hd
  have l1 : LocalUpTo (m + 1) F₁ := hl₁.mono (by omega)
  have l12 : LocalUpTo (m + 1) (fun V A => F₁ V A * F₂ (sshift V (n + R)) (sshift A (n + R))) :=
    l1.mul (lS (n + R) (by omega))
  have l10 : LocalUpTo (m + 1) (fun V A => F₁ V A * F₂ (sshift V R) (sshift A R)) :=
    l1.mul (lS R (by omega))
  have i12 := hF₁.mul (hF₂.shift (n + R))
  have i10 := hF₁.mul (hF₂.shift R)
  have EC := fun {G : (ℕ → X) → (ℕ → Y) → ℝ} {BG : ℝ} (hG : Ins G BG) (hl : LocalUpTo (m + 1) G) =>
    E_close hS ι hι hsym hφm hφb hφ1 heig hc0 m hs0 hs8 hsdef ⟨h2, hh2⟩ hL hG hl
  obtain ⟨d12, -⟩ := EC i12 l12
  obtain ⟨d10, -⟩ := EC i10 l10
  obtain ⟨d1, m1⟩ := EC hF₁ l1
  obtain ⟨d2, -⟩ := EC (hF₂.shift (n + R)) (lS (n + R) (by omega))
  obtain ⟨d0, -⟩ := EC (hF₂.shift R) (lS R (by omega))
  -- the vacuum sandwiches
  set P := ∫ x, φ x * vec μ ν w φ R F₂ x ∂μ
  set Q := ∫ x, vec μ ν w φ R F₂ x * vec μ ν w φ R F₂ x ∂μ
  set Bn := ∫ x, chain μ ν w n (fun V _ => vec μ ν w φ R F₂ (V n)) x * vec μ ν w φ R F₂ x ∂μ
  have ev : ∀ (e q : ℕ) (Z : ℝ), Even e → e + q = 2 * (m + 1) →
      c ^ e * Z / |c| ^ (2 * (m + 1)) = Z / |c| ^ q := by
    intro e q Z he hsum
    rw [← hsum, pow_add, ← Even.pow_abs he]
    field_simp
  have hM1 : c ^ (m + 1) * Ih μ ν w φ m F₁ / |c| ^ (2 * (m + 1)) = P / |c| ^ R := by
    rw [Ih_single hS ι hι hinv hsym hφm hφb heig hF₁ hF₂ hl₁ hl₂ hrev m (by omega), ← mul_assoc,
      ← pow_add]
    exact ev _ _ _ ⟨m + 1 - r, by omega⟩ (by omega)
  have hMs : ∀ d, d + R ≤ m + 1 → c ^ (m + 1)
      * Ih μ ν w φ m (fun V A => F₂ (sshift V d) (sshift A d)) / |c| ^ (2 * (m + 1)) = P / |c| ^ R := by
    intro d hd
    rw [Ih_shift hS ι hι hinv hsym hφm hφb heig hF₂ hl₂ m d hd, ← mul_assoc, ← pow_add]
    exact ev _ _ _ ⟨m + 1 - r, by omega⟩ (by omega)
  have hM10 : c ^ (m + 1) * Ih μ ν w φ m (fun V A => F₁ V A * F₂ (sshift V R) (sshift A R))
      / |c| ^ (2 * (m + 1)) = Q / |c| ^ (R + R) := by
    rw [Ih_pair0 hS ι hι hinv hsym hφm hφb heig hF₁ hF₂ hl₁ hl₂ hrev m (by omega), ← mul_assoc,
      ← pow_add]
    exact ev _ _ _ ⟨m + 1 - R, by omega⟩ (by omega)
  have hM12 : c ^ (m + 1) * Ih μ ν w φ m
      (fun V A => F₁ V A * F₂ (sshift V (n + R)) (sshift A (n + R))) / |c| ^ (2 * (m + 1))
        = Bn / |c| ^ (R + n + R) := by
    rw [Ih_pairn hS ι hι hinv hsym hφm hφb heig hF₁ hF₂ hl₁ hl₂ hrev m n (by omega), ← mul_assoc,
      ← pow_add]
    exact ev _ _ _ ⟨m + 1 - R - n2, by omega⟩ (by omega)
  rw [hM1] at d1 m1
  rw [hMs (n + R) (by omega)] at d2
  rw [hMs R (by omega)] at d0
  rw [hM10] at d10
  rw [hM12] at d12
  -- the gap
  have hg := gap_ineq hS hφm hφb hφ1 heig hks ⟨n2, hn2⟩ hnorm hgap
    (measurable_vec (μ := μ) (ν := ν) (R := R) hS hφm hφb hF₂)
    (abs_vec_le (μ := μ) (ν := ν) (R := R) hS hφm hφb hF₂)
  have hgv : Bn / |c| ^ (R + n + R) ≤ (P / |c| ^ R) ^ 2
      + 1 / 2 * (Q / |c| ^ (R + R) - (P / |c| ^ R) ^ 2) := by
    have e1 : |c| ^ (R + n + R) = |c| ^ R * |c| ^ n * |c| ^ R := by rw [pow_add, pow_add]
    have e2 : |c| ^ (R + R) = |c| ^ R * |c| ^ R := pow_add _ _ _
    have hpR : 0 < |c| ^ R := pow_pos hlp R
    have hpn : 0 < |c| ^ n := pow_pos hlp n
    rw [e1, e2, div_le_iff₀ (by positivity)]
    have : ((P / |c| ^ R) ^ 2 + 1 / 2 * (Q / (|c| ^ R * |c| ^ R) - (P / |c| ^ R) ^ 2))
        * (|c| ^ R * |c| ^ n * |c| ^ R) = |c| ^ n * (P ^ 2 + 1 / 2 * (Q - P ^ 2)) := by
      field_simp
    rw [this]; exact hg
  exact combine hB hη0 hη hgv m1 d12 d10 d1 d2 d0

end Decay

#print axioms ratio_close
#print axioms combine
#print axioms E_close
#print axioms chain_decay

end MassGap.ChainDecay
