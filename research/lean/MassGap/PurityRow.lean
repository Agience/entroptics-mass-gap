import Mathlib

/-!
# MassGap.PurityRow — the normalized-row estimate, Lemma 5.1 of the purity paper

Lemma 5.1 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`).

For a finite measure `w` with `w ≠ 0` and measurable `f, g` with values in `[a, b]`, `0 < a ≤ b`,
the probability measures `P ∝ f dw`, `Q ∝ g dw` satisfy `|P(E) − Q(E)| ≤ (b − a)/(b + a)` for every
measurable `E`, so their total variation `sup_E |P(E) − Q(E)|` is at most `(b − a)/(b + a)`; the
constant is attained within the class, by two points of equal mass.

The proof here differs from the paper's likelihood-ratio chord argument. With `x = w(E)`,
`y = w(Eᶜ)`, the integrals of `f` over `E` and `Eᶜ` lie in `[a x, b x]` and `[a y, b y]`, so
`P(E) ≤ b x/(b x + a y)` and `Q(E) ≥ a x/(a x + b y)`, and
`b x/(b x + a y) − a x/(a x + b y) ≤ (b − a)/(b + a)` is
`(b − a)(x y (a + b)² − (b x + a y)(a x + b y)) = −a b (b − a)(x − y)² ≤ 0`.

* `corner_le`: the scalar inequality; `corner_attained`: equality at `x = y`.
* `frac_le_corner`, `corner_le_frac`: the two monotone steps.
* `row_le`: the one-sided bound `P(E) − Q(E) ≤ (b − a)/(b + a)`.
* `row_abs_le`: paper, (5.1), `|P(E) − Q(E)| ≤ (b − a)/(b + a)`.
* `row_sharp`: the constant is attained by two-valued densities on a set of half the mass.
* `row_sharp_bool`: the paper's witness, two points of equal mass (`Bool` with counting measure).
* `avg_abs_le`: the bounded-function form used in the proof of Theorem 5.2, for measurable `h`
  with values in `[m, M]`, `|∫ h dP − ∫ h dQ| ≤ (b − a)/(b + a) · (M − m)`; `avg_sub_le` is the
  one-sided form. With `D = f/∫f − g/∫g` and `E = {D > 0}`, `∫ h D = ∫ (h − m) D ≤ (M − m)(P(E) − Q(E))`.
-/

namespace MassGap.PurityRow

open MeasureTheory Set

/-- `b x/(b x + a y) − a x/(a x + b y) ≤ (b − a)/(b + a)` for `x, y ≥ 0`, `x + y > 0`. -/
theorem corner_le {a b x y : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) :
    b * x / (b * x + a * y) - a * x / (a * x + b * y) ≤ (b - a) / (b + a) := by
  have hb : 0 < b := ha.trans_le hab
  have h1 : 0 < b * x + a * y := by nlinarith
  have h2 : 0 < a * x + b * y := by nlinarith
  rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (mul_pos h1 h2) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg (sub_nonneg.2 hab) (sq_nonneg (x - y)))]

/-- Equality at `x = y`. -/
theorem corner_attained {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    b * x / (b * x + a * x) - a * x / (a * x + b * x) = (b - a) / (b + a) := by
  have hb : 0 < b := ha.trans_le hab
  have h : b * x + a * x ≠ 0 := by positivity
  have h' : a * x + b * x ≠ 0 := by positivity
  have h'' : b + a ≠ 0 := by positivity
  field_simp
  ring

/-- `F₁ ≤ b x`, `a y ≤ F₂` give `F₁/(F₁ + F₂) ≤ b x/(b x + a y)`. -/
theorem frac_le_corner {a b x y F₁ F₂ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) (h1l : a * x ≤ F₁) (h1u : F₁ ≤ b * x) (h2l : a * y ≤ F₂) :
    F₁ / (F₁ + F₂) ≤ b * x / (b * x + a * y) := by
  have hb : 0 < b := ha.trans_le hab
  have hd1 : 0 < F₁ + F₂ := by nlinarith
  have hd2 : 0 < b * x + a * y := by nlinarith
  rw [div_le_div_iff₀ hd1 hd2]
  have hF1 : 0 ≤ F₁ := (mul_nonneg ha.le hx).trans h1l
  nlinarith [mul_le_mul_of_nonneg_left h1u (mul_nonneg ha.le hy), mul_le_mul_of_nonneg_left h2l hF1]

/-- `a x ≤ G₁`, `G₂ ≤ b y` give `a x/(a x + b y) ≤ G₁/(G₁ + G₂)`. -/
theorem corner_le_frac {a b x y G₁ G₂ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) (h1l : a * x ≤ G₁) (h2l : a * y ≤ G₂) (h2u : G₂ ≤ b * y) :
    a * x / (a * x + b * y) ≤ G₁ / (G₁ + G₂) := by
  have hb : 0 < b := ha.trans_le hab
  have hd1 : 0 < G₁ + G₂ := by nlinarith
  have hd2 : 0 < a * x + b * y := by nlinarith
  rw [div_le_div_iff₀ hd2 hd1]
  have hG2 : 0 ≤ G₂ := (mul_nonneg ha.le hy).trans h2l
  nlinarith [mul_le_mul_of_nonneg_left h1l hG2, mul_le_mul_of_nonneg_left h2u (mul_nonneg ha.le hx)]

variable {X : Type*} [MeasurableSpace X]

/-- The normalized mass `P(E) = ∫_E f dw / ∫ f dw`. -/
noncomputable def row (w : Measure X) (f : X → ℝ) (E : Set X) : ℝ :=
  (∫ x in E, f x ∂w) / ∫ x, f x ∂w

theorem setIntegral_mem {w : Measure X} [IsFiniteMeasure w] {f : X → ℝ} {a b : ℝ}
    (hf : Measurable f) (hfa : ∀ x, a ≤ f x) (hfb : ∀ x, f x ≤ b) (E : Set X) :
    a * w.real E ≤ ∫ x in E, f x ∂w ∧ ∫ x in E, f x ∂w ≤ b * w.real E := by
  have hi : IntegrableOn f E w :=
    (Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs (hfa x) (hfb x))).integrableOn
  have l := setIntegral_mono (integrable_const a).integrableOn hi hfa
  have u := setIntegral_mono hi (integrable_const b).integrableOn hfb
  rw [setIntegral_const, smul_eq_mul, mul_comm] at l u
  exact ⟨l, u⟩

/-- The one-sided bound `P(E) − Q(E) ≤ (b − a)/(b + a)`. -/
theorem row_le {w : Measure X} [IsFiniteMeasure w] (hw : w ≠ 0) {f g : X → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : Measurable f) (hg : Measurable g)
    (hfa : ∀ x, a ≤ f x) (hfb : ∀ x, f x ≤ b) (hga : ∀ x, a ≤ g x) (hgb : ∀ x, g x ≤ b)
    {E : Set X} (hE : MeasurableSet E) :
    row w f E - row w g E ≤ (b - a) / (b + a) := by
  have hb : ∀ h : X → ℝ, Measurable h → (∀ x, a ≤ h x) → (∀ x, h x ≤ b) →
      Integrable h w := fun h hh hha hhb =>
    Integrable.of_bound hh.aestronglyMeasurable (max |a| |b|) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (hha x) (hhb x))
  have hsplit : ∀ h : X → ℝ, Integrable h w →
      ∫ x, h x ∂w = (∫ x in E, h x ∂w) + ∫ x in Eᶜ, h x ∂w := fun h hh =>
    (integral_add_compl hE hh).symm
  have hxy : 0 < w.real E + w.real Eᶜ := by
    rw [measureReal_add_measureReal_compl hE]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hw) (measure_ne_top _ _)
  have hx := measureReal_nonneg (μ := w) (s := E)
  have hy := measureReal_nonneg (μ := w) (s := Eᶜ)
  obtain ⟨f1l, f1u⟩ := setIntegral_mem (w := w) hf hfa hfb E
  obtain ⟨f2l, -⟩ := setIntegral_mem (w := w) hf hfa hfb Eᶜ
  obtain ⟨g1l, -⟩ := setIntegral_mem (w := w) hg hga hgb E
  obtain ⟨g2l, g2u⟩ := setIntegral_mem (w := w) hg hga hgb Eᶜ
  have hP := frac_le_corner ha hab hx hy hxy f1l f1u f2l
  have hQ := corner_le_frac ha hab hx hy hxy g1l g2l g2u
  rw [row, row, hsplit f (hb f hf hfa hfb), hsplit g (hb g hg hga hgb)]
  linarith [corner_le ha hab hx hy hxy]

/-- Paper, (5.1): `|P(E) − Q(E)| ≤ (b − a)/(b + a)` for every measurable `E`. -/
theorem row_abs_le {w : Measure X} [IsFiniteMeasure w] (hw : w ≠ 0) {f g : X → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : Measurable f) (hg : Measurable g)
    (hfa : ∀ x, a ≤ f x) (hfb : ∀ x, f x ≤ b) (hga : ∀ x, a ≤ g x) (hgb : ∀ x, g x ≤ b)
    {E : Set X} (hE : MeasurableSet E) :
    |row w f E - row w g E| ≤ (b - a) / (b + a) := by
  rw [abs_le]
  refine ⟨?_, row_le hw ha hab hf hg hfa hfb hga hgb hE⟩
  linarith [row_le hw ha hab hg hf hga hgb hfa hfb hE]

/-- The constant is attained: on a set `E` with `w(E) = w(Eᶜ) > 0`, the densities
`f = b` on `E`, `a` off it and `g = a` on `E`, `b` off it give `P(E) − Q(E) = (b − a)/(b + a)`. -/
theorem row_sharp {w : Measure X} [IsFiniteMeasure w] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {E : Set X} (hE : MeasurableSet E) (hhalf : w.real E = w.real Eᶜ) (hpos : 0 < w.real E) :
    row w (E.indicator (fun _ => b) + Eᶜ.indicator (fun _ => a)) E -
      row w (E.indicator (fun _ => a) + Eᶜ.indicator (fun _ => b)) E = (b - a) / (b + a) := by
  have key : ∀ c d : ℝ, row w (E.indicator (fun _ => c) + Eᶜ.indicator (fun _ => d)) E =
      c * w.real E / (c * w.real E + d * w.real Eᶜ) := by
    intro c d
    have hfull : ∫ x, (E.indicator (fun _ => c) + Eᶜ.indicator (fun _ => d)) x ∂w =
        c * w.real E + d * w.real Eᶜ := by
      show ∫ x, (E.indicator (fun _ => c) x + Eᶜ.indicator (fun _ => d) x) ∂w = _
      rw [integral_add ((integrable_const c).indicator hE) ((integrable_const d).indicator hE.compl),
        integral_indicator hE, integral_indicator hE.compl, setIntegral_const, setIntegral_const,
        smul_eq_mul, smul_eq_mul, mul_comm, mul_comm (w.real Eᶜ)]
    have hset : ∫ x in E, (E.indicator (fun _ => c) + Eᶜ.indicator (fun _ => d)) x ∂w =
        c * w.real E := by
      rw [setIntegral_congr_fun hE (g := fun _ => c) (fun x hx => by simp [hx]),
        setIntegral_const, smul_eq_mul, mul_comm]
    rw [row, hset, hfull]
  rw [key, key, ← hhalf]
  exact corner_attained ha hab hpos

/-- The paper's witness: two points of equal mass, `Bool` with counting measure, `E = {true}`. -/
theorem row_sharp_bool {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    row (Measure.count : Measure Bool)
        (({true} : Set Bool).indicator (fun _ => b) + ({true} : Set Bool)ᶜ.indicator (fun _ => a))
        {true} -
      row (Measure.count : Measure Bool)
        (({true} : Set Bool).indicator (fun _ => a) + ({true} : Set Bool)ᶜ.indicator (fun _ => b))
        {true} = (b - a) / (b + a) := by
  have hc : ({true} : Set Bool)ᶜ = {false} := by ext x; cases x <;> simp
  refine row_sharp ha hab (measurableSet_singleton _) ?_ ?_
  · rw [hc]; simp [Measure.real]
  · simp [Measure.real]

/-- The normalized mean `avg w f h = ∫ h f dw / ∫ f dw`, which is `∫ h dP` for `P ∝ f dw`. -/
noncomputable def avg (w : Measure X) (f h : X → ℝ) : ℝ :=
  (∫ x, h x * f x ∂w) / ∫ x, f x ∂w

/-- The one-sided bounded-function form: for measurable `h` with values in `[m, M]`,
`∫ h dP − ∫ h dQ ≤ (b − a)/(b + a) · (M − m)`. -/
theorem avg_sub_le {w : Measure X} [IsFiniteMeasure w] (hw : w ≠ 0) {f g h : X → ℝ}
    {a b m M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hfa : ∀ x, a ≤ f x) (hfb : ∀ x, f x ≤ b) (hga : ∀ x, a ≤ g x)
    (hgb : ∀ x, g x ≤ b) (hhm : ∀ x, m ≤ h x) (hhM : ∀ x, h x ≤ M) :
    avg w f h - avg w g h ≤ (b - a) / (b + a) * (M - m) := by
  unfold avg
  have bnd : ∀ u : X → ℝ, Measurable u → ∀ C, (∀ x, |u x| ≤ C) → Integrable u w :=
    fun u hu C hC => Integrable.of_bound hu.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hfi := bnd f hf _ fun x => abs_le_max_abs_abs (hfa x) (hfb x)
  have hgi := bnd g hg _ fun x => abs_le_max_abs_abs (hga x) (hgb x)
  have hC : ∀ u : X → ℝ, (∀ x, a ≤ u x) → (∀ x, u x ≤ b) →
      ∀ x, |h x * u x| ≤ max |m| |M| * max |a| |b| := fun u hua hub x => by
    rw [abs_mul]
    exact mul_le_mul (abs_le_max_abs_abs (hhm x) (hhM x)) (abs_le_max_abs_abs (hua x) (hub x))
      (abs_nonneg _) ((abs_nonneg _).trans (le_max_left _ _))
  have hhf := bnd (fun x => h x * f x) (hh.mul hf) _ (hC f hfa hfb)
  have hhg := bnd (fun x => h x * g x) (hh.mul hg) _ (hC g hga hgb)
  have hpos : 0 < w.real univ :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hw) (measure_ne_top _ _)
  have hZf : 0 < ∫ x, f x ∂w := by
    have := (setIntegral_mem (w := w) hf hfa hfb univ).1
    rw [setIntegral_univ] at this
    nlinarith
  have hZg : 0 < ∫ x, g x ∂w := by
    have := (setIntegral_mem (w := w) hg hga hgb univ).1
    rw [setIntegral_univ] at this
    nlinarith
  obtain ⟨x₀, -⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.2 hw)
  have hmM : m ≤ M := (hhm x₀).trans (hhM x₀)
  set Zf := ∫ x, f x ∂w with hZfd
  set Zg := ∫ x, g x ∂w with hZgd
  have hDi : Integrable (fun x => f x / Zf - g x / Zg) w := (hfi.div_const Zf).sub (hgi.div_const Zg)
  have hDm : Measurable (fun x => f x / Zf - g x / Zg) := (hf.div_const Zf).sub (hg.div_const Zg)
  have hE : MeasurableSet {x | 0 < f x / Zf - g x / Zg} := measurableSet_lt measurable_const hDm
  have e : (fun x => (h x - m) * (f x / Zf - g x / Zg)) =
      fun x => (h x * f x / Zf - m / Zf * f x) - (h x * g x / Zg - m / Zg * g x) := by
    funext x; ring
  have hu : Integrable (fun x => (h x - m) * (f x / Zf - g x / Zg)) w := by
    rw [e]
    exact ((hhf.div_const Zf).sub (hfi.const_mul _)).sub ((hhg.div_const Zg).sub (hgi.const_mul _))
  have e1 : (∫ x, h x * f x ∂w) / Zf - (∫ x, h x * g x ∂w) / Zg =
      ∫ x, (h x - m) * (f x / Zf - g x / Zg) ∂w := by
    have i1 : ∫ x, (h x * f x / Zf - m / Zf * f x) ∂w = (∫ x, h x * f x ∂w) / Zf - m / Zf * Zf := by
      rw [integral_sub (hhf.div_const Zf) (hfi.const_mul _), integral_div, integral_const_mul]
    have i2 : ∫ x, (h x * g x / Zg - m / Zg * g x) ∂w = (∫ x, h x * g x ∂w) / Zg - m / Zg * Zg := by
      rw [integral_sub (hhg.div_const Zg) (hgi.const_mul _), integral_div, integral_const_mul]
    rw [e, integral_sub (f := fun x => h x * f x / Zf - m / Zf * f x)
        (g := fun x => h x * g x / Zg - m / Zg * g x)
        ((hhf.div_const Zf).sub (hfi.const_mul _)) ((hhg.div_const Zg).sub (hgi.const_mul _)),
      i1, i2]
    field_simp
    ring
  have hle : ∀ x, (h x - m) * (f x / Zf - g x / Zg) ≤
      {x | 0 < f x / Zf - g x / Zg}.indicator (fun x => (M - m) * (f x / Zf - g x / Zg)) x := by
    intro x
    rw [Set.indicator_apply]
    split_ifs with hx
    · exact mul_le_mul_of_nonneg_right (by linarith [hhM x])
        (le_of_lt (show 0 < f x / Zf - g x / Zg from hx))
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hhm x])
        (not_lt.1 (show ¬ (0 < f x / Zf - g x / Zg) from hx))
  have e3 : ∫ x, {x | 0 < f x / Zf - g x / Zg}.indicator
        (fun x => (M - m) * (f x / Zf - g x / Zg)) x ∂w =
      (M - m) * (row w f {x | 0 < f x / Zf - g x / Zg} - row w g {x | 0 < f x / Zf - g x / Zg}) := by
    rw [integral_indicator hE, integral_const_mul,
      integral_sub (hfi.div_const Zf).integrableOn (hgi.div_const Zg).integrableOn,
      integral_div, integral_div]
    rfl
  rw [e1]
  refine (integral_mono hu ((hDi.const_mul (M - m)).indicator hE) hle).trans ?_
  rw [e3, mul_comm]
  exact mul_le_mul_of_nonneg_right (row_le hw ha hab hf hg hfa hfb hga hgb hE) (by linarith)

/-- The bounded-function form used in the proof of Theorem 5.2: for measurable `h` with values in
`[m, M]`, `|∫ h dP − ∫ h dQ| ≤ (b − a)/(b + a) · (M − m)`. -/
theorem avg_abs_le {w : Measure X} [IsFiniteMeasure w] (hw : w ≠ 0) {f g h : X → ℝ}
    {a b m M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hfa : ∀ x, a ≤ f x) (hfb : ∀ x, f x ≤ b) (hga : ∀ x, a ≤ g x)
    (hgb : ∀ x, g x ≤ b) (hhm : ∀ x, m ≤ h x) (hhM : ∀ x, h x ≤ M) :
    |avg w f h - avg w g h| ≤ (b - a) / (b + a) * (M - m) := by
  rw [abs_le]
  refine ⟨?_, avg_sub_le hw ha hab hf hg hh hfa hfb hga hgb hhm hhM⟩
  linarith [avg_sub_le hw ha hab hg hf hh hga hgb hfa hfb hhm hhM]

end MassGap.PurityRow

#print axioms MassGap.PurityRow.corner_le
#print axioms MassGap.PurityRow.corner_attained
#print axioms MassGap.PurityRow.frac_le_corner
#print axioms MassGap.PurityRow.corner_le_frac
#print axioms MassGap.PurityRow.setIntegral_mem
#print axioms MassGap.PurityRow.row_le
#print axioms MassGap.PurityRow.row_abs_le
#print axioms MassGap.PurityRow.row_sharp
#print axioms MassGap.PurityRow.row_sharp_bool
#print axioms MassGap.PurityRow.avg_sub_le
#print axioms MassGap.PurityRow.avg_abs_le
