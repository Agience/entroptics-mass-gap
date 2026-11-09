import Mathlib

/-!
# MassGap.FibrePerturb — the fibre covariance bound survives a bounded perturbation of the weight

The box gap bounds, for the conditional law of a link pair, the covariance of a centred test
function of one link against any test function of the other (`PairInterface.FibreBound`). That bound
is proved for the Wilson weight family. An observer's coarse theory carries further couplings, such as
products of adjacent plaquettes, which multiply the pair's weight by `e^V` with `V` bounded but not of
the Wilson form. This module proves the bound is stable under any such factor, for a single weight on
any finite measure space.

## What it gives

`covBoundOn_perturb`: for any class `Adm` of test functions that are measurable and bounded and closed
under subtracting a constant, if `w ≥ 0` satisfies `CovBoundOn Adm P w c` and `|V| ≤ ε`, then `w e^V`
satisfies it with `e^ε (c + 2 (e^ε − 1))`. `covBound_perturb` is the bounded measurable class
(`covBound_iff_on`); `covBoundOn_perturb_cont` is the continuous bounded class that
`PairInterface.FibreBound` quantifies over.

## The route

With `k = e^ε`, `w' = w e^V` lies between `w / k` and `k w`, so `|w' − w| ≤ (k − 1) w` and the marginals
`q, q'` and `p, p'` obey the same bounds. For `a` centred under `q'`:

* the cross term `∫∫ a b (w' − w)` is at most `(k − 1)/2 (A + B)`, from `|a b| ≤ (a² + b²)/2`, where
  `A = ∫ a² q` and `B = ∫ b² p`;
* the re-centring: with `m = ∫ a q / Z`, `Z = ∫∫ w`, the function `a − m` is centred under `q`, so the
  hypothesis bounds `∫∫ (a − m) b w`, and `∫ (a − m)² q ≤ A`. The shift `m ∫ b p` is at most
  `(k − 1)/2 (A + B)`: `|∫ a q| = |∫ a (q − q')| ≤ (k − 1) ∫ |a| q`, and `(∫ |a| q)(∫ |b| p)` is a double
  integral bounded by `|a(h)| |b(g)| ≤ (a(h)² + b(g)²)/2` — no Cauchy–Schwarz;
* `A ≤ k A'` and `B ≤ k B'` convert to the perturbed marginals.

The additive `2 (e^ε − 1)` is not slack in the method: a product weight (`c = 0`) times a rank-one
`e^{ε f(h) f(g)}` has correlation of order `ε`.
-/

namespace MassGap.FibrePerturb

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first marginal of a pair weight: `q(h) = ∫ w(h, g) dg`. -/
noncomputable def qW (P : Measure Ω) (w : Ω → Ω → ℝ) (h : Ω) : ℝ := ∫ g, w h g ∂P

/-- The second marginal of a pair weight: `p(g) = ∫ w(h, g) dh`. -/
noncomputable def pW (P : Measure Ω) (w : Ω → Ω → ℝ) (g : Ω) : ℝ := ∫ h, w h g ∂P

/-- **The fibre covariance bound at constant `c`** for one weight, in the shape of
`PairInterface.FibreBound`: for bounded measurable `a, b` with `a` centred under `q`,
`∫∫ a b w ≤ (c/2)(∫ a² q + ∫ b² p)`.

DERIVED: `0` is the vanishing mean; `2` is the square and the halving. -/
def CovBound (P : Measure Ω) (w : Ω → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ a b : Ω → ℝ, Measurable a → Measurable b → (∃ C, ∀ x, |a x| ≤ C) → (∃ C, ∀ x, |b x| ≤ C) →
    ∫ h, a h * qW P w h ∂P = 0 →
    ∫ h, ∫ g, a h * b g * w h g ∂P ∂P
      ≤ c / 2 * (∫ h, a h ^ 2 * qW P w h ∂P + ∫ g, b g ^ 2 * pW P w g ∂P)

/-- **The fibre covariance bound over a class `Adm` of test functions.** `CovBound` is the class of
bounded measurable functions (`covBound_iff_on`); `PairInterface.FibreBound` uses continuous ones.

DERIVED: `0` is the vanishing mean; `2` is the square and the halving. -/
def CovBoundOn (Adm : (Ω → ℝ) → Prop) (P : Measure Ω) (w : Ω → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ a b : Ω → ℝ, Adm a → Adm b → ∫ h, a h * qW P w h ∂P = 0 →
    ∫ h, ∫ g, a h * b g * w h g ∂P ∂P
      ≤ c / 2 * (∫ h, a h ^ 2 * qW P w h ∂P + ∫ g, b g ^ 2 * pW P w g ∂P)

/-- `CovBound` is `CovBoundOn` the bounded measurable functions.

DERIVED: no numeral. -/
theorem covBound_iff_on (P : Measure Ω) (w : Ω → Ω → ℝ) (c : ℝ) :
    CovBound P w c ↔ CovBoundOn (fun a => Measurable a ∧ ∃ C, ∀ x, |a x| ≤ C) P w c :=
  ⟨fun H a b ha hb hc => H a b ha.1 hb.1 ha.2 hb.2 hc,
    fun H a b ha hb haB hbB hc => H a b ⟨ha, haB⟩ ⟨hb, hbB⟩ hc⟩

#print axioms covBound_iff_on

/-- **The bound is unchanged by a positive constant factor on the weight**: both sides and the
centring are linear in `w`.

DERIVED: `0` is the sign of `C` and the vanishing mean; `2` is the square and the halving. -/
theorem covBoundOn_const_mul (Adm : (Ω → ℝ) → Prop) (P : Measure Ω) {w : Ω → Ω → ℝ} {c C : ℝ}
    (hC : 0 < C) (H : CovBoundOn Adm P w c) : CovBoundOn Adm P (fun h g => C * w h g) c := by
  intro a b ha hb hcent
  have hq : ∀ h, qW P (fun h g => C * w h g) h = C * qW P w h := fun h => by
    unfold qW; exact integral_const_mul C (w h)
  have hp : ∀ g, pW P (fun h g => C * w h g) g = C * pW P w g := fun g => by
    unfold pW; exact integral_const_mul C (fun h => w h g)
  simp only [hq, hp] at hcent ⊢
  have hcent' : ∫ h, a h * qW P w h ∂P = 0 := by
    have e : ∫ h, a h * (C * qW P w h) ∂P = C * ∫ h, a h * qW P w h ∂P := by
      rw [← integral_const_mul]; congr 1; funext h; ring
    rw [e] at hcent
    exact (mul_eq_zero.mp hcent).resolve_left hC.ne'
  have key := H a b ha hb hcent'
  have eL : ∫ h, ∫ g, a h * b g * (C * w h g) ∂P ∂P = C * ∫ h, ∫ g, a h * b g * w h g ∂P ∂P := by
    rw [← integral_const_mul]; congr 1; funext h
    rw [← integral_const_mul]; congr 1; funext g; ring
  have eA : ∫ h, a h ^ 2 * (C * qW P w h) ∂P = C * ∫ h, a h ^ 2 * qW P w h ∂P := by
    rw [← integral_const_mul]; congr 1; funext h; ring
  have eB : ∫ g, b g ^ 2 * (C * pW P w g) ∂P = C * ∫ g, b g ^ 2 * pW P w g ∂P := by
    rw [← integral_const_mul]; congr 1; funext g; ring
  rw [eL, eA, eB]
  have := mul_le_mul_of_nonneg_left key hC.le
  linarith [this]

#print axioms covBoundOn_const_mul

/-! ## The toolkit: jointly measurable bounded pair functions -/

section Toolkit

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- A bounded measurable function is integrable for a finite measure. -/
theorem int_of_bdd {β : Type*} [MeasurableSpace β] (μ : Measure β) [IsFiniteMeasure μ] {f : β → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- A pair function that is jointly measurable and bounded. -/
def Good (F : Ω → Ω → ℝ) : Prop := Measurable (Function.uncurry F) ∧ ∃ C, ∀ h g, |F h g| ≤ C

/-- A one-variable function that is measurable and bounded. -/
def Good1 (f : Ω → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C

theorem Good.inner {F : Ω → Ω → ℝ} (hF : Good F) (h : Ω) : Integrable (F h) P := by
  obtain ⟨hm, C, hC⟩ := hF
  exact int_of_bdd P (hm.comp measurable_prodMk_left) (hC h)

theorem Good.innerMeas {F : Ω → Ω → ℝ} (hF : Good F) : Measurable fun h => ∫ g, F h g ∂P :=
  (hF.1.stronglyMeasurable.integral_prod_right (ν := P)).measurable

theorem Good.innerMeas' {F : Ω → Ω → ℝ} (hF : Good F) : Measurable fun g => ∫ h, F h g ∂P :=
  (hF.1.stronglyMeasurable.integral_prod_left (μ := P)).measurable

theorem Good.innerBdd {F : Ω → Ω → ℝ} (hF : Good F) :
    ∃ C, (∀ h, |∫ g, F h g ∂P| ≤ C) ∧ ∀ g, |∫ h, F h g ∂P| ≤ C := by
  obtain ⟨_, C, hC⟩ := hF
  refine ⟨|C| * P.real Set.univ, fun h => ?_, fun g => ?_⟩
  · have := norm_integral_le_of_norm_le_const (μ := P) (f := F h) (C := |C|)
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs]; exact (hC h g).trans (le_abs_self C))
    simpa [Real.norm_eq_abs] using this
  · have := norm_integral_le_of_norm_le_const (μ := P) (f := fun h => F h g) (C := |C|)
      (Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs]; exact (hC h g).trans (le_abs_self C))
    simpa [Real.norm_eq_abs] using this

theorem Good.outer {F : Ω → Ω → ℝ} (hF : Good F) : Integrable (fun h => ∫ g, F h g ∂P) P := by
  obtain ⟨C, hC, _⟩ := hF.innerBdd P
  exact int_of_bdd P (hF.innerMeas P) hC

theorem Good.swap {F : Ω → Ω → ℝ} (hF : Good F) :
    ∫ h, ∫ g, F h g ∂P ∂P = ∫ g, ∫ h, F h g ∂P ∂P := by
  obtain ⟨hm, C, hC⟩ := hF
  exact integral_integral_swap (int_of_bdd (P.prod P) hm (fun z => hC z.1 z.2))

theorem Good.add {F G : Ω → Ω → ℝ} (hF : Good F) (hG : Good G) : Good fun h g => F h g + G h g := by
  obtain ⟨hFm, CF, hCF⟩ := hF
  obtain ⟨hGm, CG, hCG⟩ := hG
  exact ⟨hFm.add hGm, CF + CG, fun h g => (abs_add_le _ _).trans (add_le_add (hCF h g) (hCG h g))⟩

theorem Good.mul {F G : Ω → Ω → ℝ} (hF : Good F) (hG : Good G) : Good fun h g => F h g * G h g := by
  obtain ⟨hFm, CF, hCF⟩ := hF
  obtain ⟨hGm, CG, hCG⟩ := hG
  refine ⟨hFm.mul hGm, |CF| * |CG|, fun h g => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hCF h g).trans (le_abs_self _)) ((hCG h g).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

theorem Good.of_eq {F G : Ω → Ω → ℝ} (hF : Good F) (hFG : ∀ x y, F x y = G x y) : Good G := by
  have : F = G := funext fun x => funext fun y => hFG x y
  exact this ▸ hF

theorem Good.const (r : ℝ) : Good fun (_ _ : Ω) => r :=
  ⟨measurable_const, |r|, fun _ _ => le_rfl⟩

theorem Good1.left {f : Ω → ℝ} (hf : Good1 f) : Good fun h (_ : Ω) => f h :=
  ⟨hf.1.comp measurable_fst, hf.2.choose, fun h _ => hf.2.choose_spec h⟩

theorem Good1.right {f : Ω → ℝ} (hf : Good1 f) : Good fun (_ : Ω) g => f g :=
  ⟨hf.1.comp measurable_snd, hf.2.choose, fun _ g => hf.2.choose_spec g⟩

theorem Good1.int {f : Ω → ℝ} (hf : Good1 f) : Integrable f P :=
  int_of_bdd P hf.1 hf.2.choose_spec

theorem Good1.mul {f g : Ω → ℝ} (hf : Good1 f) (hg : Good1 g) : Good1 fun x => f x * g x := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, |Cf| * |Cg|, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hCf x).trans (le_abs_self _)) ((hCg x).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

theorem Good1.const (r : ℝ) : Good1 fun _ : Ω => r := ⟨measurable_const, |r|, fun _ => le_rfl⟩

theorem Good1.sub {f g : Ω → ℝ} (hf : Good1 f) (hg : Good1 g) : Good1 fun x => f x - g x := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun x => (abs_sub _ _).trans (add_le_add (hCf x) (hCg x))⟩

theorem Good.qW {w : Ω → Ω → ℝ} (hw : Good w) : Good1 (qW P w) := by
  obtain ⟨C, hC, _⟩ := hw.innerBdd P
  exact ⟨hw.innerMeas P, C, hC⟩

theorem Good.pW {w : Ω → Ω → ℝ} (hw : Good w) : Good1 (pW P w) := by
  obtain ⟨C, _, hC⟩ := hw.innerBdd P
  exact ⟨hw.innerMeas' P, C, hC⟩

theorem iint_add {F G : Ω → Ω → ℝ} (hF : Good F) (hG : Good G) :
    ∫ h, ∫ g, (F h g + G h g) ∂P ∂P = ∫ h, ∫ g, F h g ∂P ∂P + ∫ h, ∫ g, G h g ∂P ∂P := by
  rw [← integral_add (hF.outer P) (hG.outer P)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun h =>
    integral_add (hF.inner P h) (hG.inner P h))

theorem iint_mono {F G : Ω → Ω → ℝ} (hF : Good F) (hG : Good G) (hle : ∀ h g, F h g ≤ G h g) :
    ∫ h, ∫ g, F h g ∂P ∂P ≤ ∫ h, ∫ g, G h g ∂P ∂P :=
  integral_mono (hF.outer P) (hG.outer P) fun h =>
    integral_mono (hF.inner P h) (hG.inner P h) fun g => hle h g

/-- A function of the first variable leaves the inner integral: `∫∫ f(h) w(h,g) = ∫ f q`. -/
theorem iint_left (f : Ω → ℝ) (w : Ω → Ω → ℝ) :
    ∫ h, ∫ g, f h * w h g ∂P ∂P = ∫ h, f h * qW P w h ∂P := by
  unfold qW
  exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_const_mul (f h) (w h))

/-- A function of the second variable, after exchanging the order: `∫∫ f(g) w(h,g) = ∫ f p`. -/
theorem iint_right {f : Ω → ℝ} {w : Ω → Ω → ℝ} (hf : Good1 f) (hw : Good w) :
    ∫ h, ∫ g, f g * w h g ∂P ∂P = ∫ g, f g * pW P w g ∂P := by
  rw [(hf.right.mul hw).swap P]
  unfold pW
  exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
    integral_const_mul (f g) (fun h => w h g))

/-- A separable double integral is a product: `∫∫ f(h) u(g) = (∫ f)(∫ u)`. -/
theorem iint_sep (f u : Ω → ℝ) :
    ∫ h, ∫ g, f h * u g ∂P ∂P = (∫ h, f h ∂P) * ∫ g, u g ∂P := by
  rw [← integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_const_mul (f h) u)

end Toolkit

/-! ## The perturbation bound -/

section Perturb

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- The pointwise comparison of the perturbed weight: `w/k ≤ w e^V ≤ k w` and
`|w e^V − w| ≤ (k − 1) w`, with `k = e^ε`.

DERIVED: `1` is the unit of `e^0`. -/
theorem weight_bounds {x v ε : ℝ} (hx : 0 ≤ x) (hv : |v| ≤ ε) :
    x * Real.exp v ≤ Real.exp ε * x ∧ x ≤ Real.exp ε * (x * Real.exp v) ∧
      |x * Real.exp v - x| ≤ (Real.exp ε - 1) * x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hv
  have hev : Real.exp v ≤ Real.exp ε := Real.exp_le_exp.mpr hhi
  have hprod : 1 ≤ Real.exp ε * Real.exp v := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hk : 0 < Real.exp ε := Real.exp_pos ε
  have hev0 : 0 < Real.exp v := Real.exp_pos v
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [show x * Real.exp v - x = x * (Real.exp v - 1) by ring, abs_mul, abs_of_nonneg hx]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ hx
  rw [abs_le]
  constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- **The fibre covariance bound is stable under a bounded perturbation of the weight.** If `w ≥ 0` is
jointly measurable and bounded and satisfies `CovBound P w c` with `0 ≤ c`, and `V` is jointly
measurable with `|V| ≤ ε`, then `w e^V` satisfies the bound with `e^ε (c + 2 (e^ε − 1))`.

DERIVED: `2` is the square, the halving and the two additive terms (cross term and re-centring);
`1` is `e^0`; `0` is the sign of `c`, `ε`, `w` and the vanishing mean. -/
theorem covBoundOn_perturb (Adm : (Ω → ℝ) → Prop)
    (hAdm : ∀ a, Adm a → Measurable a ∧ ∃ C, ∀ x, |a x| ≤ C)
    (hshift : ∀ a (m : ℝ), Adm a → Adm fun h => a h - m)
    {w V : Ω → Ω → ℝ} {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hw : Good w) (hw0 : ∀ h g, 0 ≤ w h g) (hVm : Measurable (Function.uncurry V))
    (hVb : ∀ h g, |V h g| ≤ ε) (H : CovBoundOn Adm P w c) :
    CovBoundOn Adm P (fun h g => w h g * Real.exp (V h g))
      (Real.exp ε * (c + 2 * (Real.exp ε - 1))) := by
  intro a b hAa hAb hcent
  obtain ⟨ha, haB⟩ := hAdm a hAa
  obtain ⟨hb, hbB⟩ := hAdm b hAb
  set k := Real.exp ε with hkdef
  have hk1 : 1 ≤ k := Real.one_le_exp hε
  set w' : Ω → Ω → ℝ := fun h g => w h g * Real.exp (V h g) with hw'def
  have hwb := fun h g => weight_bounds (hw0 h g) (hVb h g)
  -- goodness of the pieces
  have hE : Good fun h g => Real.exp (V h g) :=
    ⟨Real.measurable_exp.comp hVm, Real.exp ε, fun h g => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (abs_le.mp (hVb h g)).2⟩
  have hw' : Good w' := hw.mul hE
  have ha1 : Good1 a := ⟨ha, haB⟩
  have hb1 : Good1 b := ⟨hb, hbB⟩
  have hq := hw.qW P
  have hp := hw.pW P
  have hq' := hw'.qW P
  have hp' := hw'.pW P
  have hq0 : ∀ h, 0 ≤ qW P w h := fun h => integral_nonneg fun g => hw0 h g
  have hp0 : ∀ g, 0 ≤ pW P w g := fun g => integral_nonneg fun h => hw0 h g
  -- the marginals compare
  have hqq' : ∀ h, qW P w h ≤ k * qW P w' h := fun h => by
    unfold qW; rw [← integral_const_mul]
    exact integral_mono (hw.inner P h) ((hw'.mul (Good.const k)).inner P h |>.congr
      (Filter.Eventually.of_forall fun g => by simp [mul_comm])) fun g => (hwb h g).2.1
  have hpp' : ∀ g, pW P w g ≤ k * pW P w' g := fun g => by
    unfold pW; rw [← integral_const_mul]
    have hi : Integrable (fun h => w h g) P :=
      int_of_bdd P (hw.1.comp (measurable_id.prodMk measurable_const)) fun h => hw.2.choose_spec h g
    have hi' : Integrable (fun h => k * w' h g) P :=
      int_of_bdd P (measurable_const.mul (hw'.1.comp (measurable_id.prodMk measurable_const)))
        (C := |k| * |hw'.2.choose|) fun h => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left
            ((hw'.2.choose_spec h g).trans (le_abs_self _)) (abs_nonneg _)
    exact integral_mono hi hi' fun h => (hwb h g).2.1
  have hqd : ∀ h, |qW P w' h - qW P w h| ≤ (k - 1) * qW P w h := fun h => by
    unfold qW
    rw [← integral_sub (hw'.inner P h) (hw.inner P h), ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono ((hw'.inner P h).sub (hw.inner P h)).abs
      ((hw.inner P h).const_mul _) fun g => (hwb h g).2.2
  -- the one-variable pieces
  have ha2 : Good1 fun x => a x ^ 2 := by simpa [sq] using ha1.mul ha1
  have hb2 : Good1 fun x => b x ^ 2 := by simpa [sq] using hb1.mul hb1
  have haA : Good1 fun x => |a x| := ⟨ha.abs, haB.choose, fun x => by
    rw [abs_abs]; exact haB.choose_spec x⟩
  have hbA : Good1 fun x => |b x| := ⟨hb.abs, hbB.choose, fun x => by
    rw [abs_abs]; exact hbB.choose_spec x⟩
  set A := ∫ h, a h ^ 2 * qW P w h ∂P with hAdef
  set B := ∫ g, b g ^ 2 * pW P w g ∂P with hBdef
  set A' := ∫ h, a h ^ 2 * qW P w' h ∂P with hA'def
  set B' := ∫ g, b g ^ 2 * pW P w' g ∂P with hB'def
  set Z := ∫ h, qW P w h ∂P with hZdef
  set S := ∫ h, a h * qW P w h ∂P with hSdef
  set T := ∫ g, b g * pW P w g ∂P with hTdef
  have hA0 : 0 ≤ A := integral_nonneg fun h => mul_nonneg (sq_nonneg _) (hq0 h)
  have hB0 : 0 ≤ B := integral_nonneg fun g => mul_nonneg (sq_nonneg _) (hp0 g)
  have hZ0 : 0 ≤ Z := integral_nonneg hq0
  have hZp : ∫ g, pW P w g ∂P = Z := by
    rw [hZdef]; unfold qW pW; exact (hw.swap P).symm
  -- A ≤ k A' and B ≤ k B'
  have hAA : A ≤ k * A' := by
    rw [hAdef, hA'def, ← integral_const_mul]
    exact integral_mono ((ha2.mul hq).int P) ((ha2.mul hq').int P |>.const_mul k) fun h => by
      nlinarith [mul_le_mul_of_nonneg_left (hqq' h) (sq_nonneg (a h))]
  have hBB : B ≤ k * B' := by
    rw [hBdef, hB'def, ← integral_const_mul]
    exact integral_mono ((hb2.mul hp).int P) ((hb2.mul hp').int P |>.const_mul k) fun g => by
      nlinarith [mul_le_mul_of_nonneg_left (hpp' g) (sq_nonneg (b g))]
  -- the cross term: ∫∫ a b (w' − w) ≤ (k − 1)/2 (A + B)
  have hcross : ∫ h, ∫ g, a h * b g * (w' h g - w h g) ∂P ∂P ≤ (k - 1) / 2 * (A + B) := by
    have hD : Good fun h g => w' h g - w h g :=
      (hw'.add ((Good.const (-1)).mul hw)).of_eq fun h g => by ring
    have hL : Good fun h g => a h * b g * (w' h g - w h g) := (ha1.left.mul hb1.right).mul hD
    have hR1 : Good fun h g => (k - 1) / 2 * a h ^ 2 * w h g :=
      ((Good.const ((k - 1) / 2)).mul ha2.left).mul hw
    have hR2 : Good fun h g => (k - 1) / 2 * b g ^ 2 * w h g :=
      ((Good.const ((k - 1) / 2)).mul hb2.right).mul hw
    have hpt : ∀ h g, a h * b g * (w' h g - w h g)
        ≤ (k - 1) / 2 * a h ^ 2 * w h g + (k - 1) / 2 * b g ^ 2 * w h g := by
      intro h g
      have hd := (hwb h g).2.2
      have hW := hw0 h g
      have h1 : a h * b g * (w' h g - w h g) ≤ |a h * b g| * |w' h g - w h g| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |a h * b g| ≤ (a h ^ 2 + b g ^ 2) / 2 := by
        rw [abs_mul]; nlinarith [sq_nonneg (|a h| - |b g|), sq_abs (a h), sq_abs (b g)]
      have h3 : |a h * b g| * |w' h g - w h g| ≤ |a h * b g| * ((k - 1) * w h g) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      have h4 : |a h * b g| * ((k - 1) * w h g) ≤ (a h ^ 2 + b g ^ 2) / 2 * ((k - 1) * w h g) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg (by linarith) hW)
      nlinarith
    calc ∫ h, ∫ g, a h * b g * (w' h g - w h g) ∂P ∂P
        ≤ ∫ h, ∫ g, ((k - 1) / 2 * a h ^ 2 * w h g + (k - 1) / 2 * b g ^ 2 * w h g) ∂P ∂P :=
          iint_mono P hL (hR1.add hR2) hpt
      _ = (k - 1) / 2 * A + (k - 1) / 2 * B := by
          rw [iint_add P hR1 hR2, iint_left P (fun h => (k - 1) / 2 * a h ^ 2) w,
            iint_right P (f := fun g => (k - 1) / 2 * b g ^ 2)
              ((Good1.const ((k - 1) / 2)).mul hb2) hw]
          simp only [mul_assoc]
          rw [integral_const_mul, integral_const_mul]
      _ = (k - 1) / 2 * (A + B) := by ring
  -- re-centring under q
  set m : ℝ := if Z = 0 then 0 else S / Z with hmdef
  have hSa : |S| ≤ (k - 1) * ∫ h, |a h| * qW P w h ∂P := by
    have hcent' : ∫ h, a h * qW P w' h ∂P = 0 := hcent
    have hdiff : S = -∫ h, a h * (qW P w' h - qW P w h) ∂P := by
      rw [hSdef]
      have := integral_sub ((ha1.mul hq').int P) ((ha1.mul hq).int P)
      simp only [mul_sub]
      rw [this, hcent']; ring
    rw [hdiff, abs_neg, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      ((ha1.mul (hq'.sub hq)).int P |>.abs) ((haA.mul hq).int P |>.const_mul _) ?_)
    intro h
    dsimp only
    rw [abs_mul]
    nlinarith [hqd h, abs_nonneg (a h), mul_le_mul_of_nonneg_left (hqd h) (abs_nonneg (a h))]
  -- S = m Z
  have hSZ : S = m * Z := by
    by_cases hZ : Z = 0
    · have hm0 : m = 0 := by simp [hmdef, hZ]
      rw [hm0, zero_mul]
      have hle : |S| ≤ |haB.choose| * Z := by
        rw [hSdef, hZdef, ← integral_const_mul]
        refine (abs_integral_le_integral_abs).trans (integral_mono ((ha1.mul hq).int P).abs
          ((hq.int P).const_mul _) fun h => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (hq0 h)]
        exact mul_le_mul_of_nonneg_right ((haB.choose_spec h).trans (le_abs_self _)) (hq0 h)
      rw [hZ, mul_zero] at hle
      exact abs_nonpos_iff.mp hle
    · have hm : m = S / Z := by simp [hmdef, hZ]
      rw [hm]; field_simp
  -- a − m is centred under q
  have hcm : ∫ h, (a h - m) * qW P w h ∂P = 0 := by
    have e : ∫ h, (a h - m) * qW P w h ∂P = S - m * Z := by
      simp only [sub_mul]
      rw [integral_sub ((ha1.mul hq).int P) ((hq.int P).const_mul m), integral_const_mul]
    rw [e, hSZ]; ring
  have ham : Good1 fun h => a h - m := ha1.sub (Good1.const m)
  have hH := H (fun h => a h - m) b (hshift a m hAa) hAb hcm
  -- ∫ (a − m)² q ≤ A
  have hAm : ∫ h, (a h - m) ^ 2 * qW P w h ∂P ≤ A := by
    have e : ∀ h, (a h - m) ^ 2 * qW P w h
        = a h ^ 2 * qW P w h - (2 * m) * (a h * qW P w h) + m ^ 2 * qW P w h := fun h => by ring
    have hi1 : Integrable (fun h => a h ^ 2 * qW P w h) P := (ha2.mul hq).int P
    have hi2 : Integrable (fun h => a h * qW P w h) P := (ha1.mul hq).int P
    have hi3 : Integrable (fun h => qW P w h) P := hq.int P
    have hval : ∫ h, (a h - m) ^ 2 * qW P w h ∂P = A - 2 * m * S + m ^ 2 * Z := by
      calc ∫ h, (a h - m) ^ 2 * qW P w h ∂P
          = ∫ h, (a h ^ 2 * qW P w h - 2 * m * (a h * qW P w h) + m ^ 2 * qW P w h) ∂P := by
            simp only [e]
        _ = ∫ h, (a h ^ 2 * qW P w h - 2 * m * (a h * qW P w h)) ∂P
              + ∫ h, m ^ 2 * qW P w h ∂P := integral_add (hi1.sub (hi2.const_mul _)) (hi3.const_mul _)
        _ = A - 2 * m * S + m ^ 2 * Z := by
            rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul, integral_const_mul]
    rw [hval, hSZ]
    nlinarith [mul_nonneg (sq_nonneg m) hZ0]
  -- ∫∫ a b w = ∫∫ (a − m) b w + m T
  have hF1 : Good fun h g => (a h - m) * b g * w h g := (ham.left.mul hb1.right).mul hw
  have hF2 : Good fun h g => m * (b g * w h g) := (Good.const m).mul (hb1.right.mul hw)
  have hsplit : ∫ h, ∫ g, a h * b g * w h g ∂P ∂P
      = ∫ h, ∫ g, (a h - m) * b g * w h g ∂P ∂P + m * T := by
    have e : ∀ h g, a h * b g * w h g = (a h - m) * b g * w h g + m * (b g * w h g) :=
      fun h g => by ring
    simp only [e]
    rw [iint_add P hF1 hF2]
    congr 1
    simp only [integral_const_mul]
    rw [iint_right P hb1 hw]
  -- the shift: m T ≤ (k − 1)/2 (A + B)
  have hshift : m * T ≤ (k - 1) / 2 * (A + B) := by
    by_cases hZ : Z = 0
    · have hm0 : m = 0 := by simp [hmdef, hZ]
      rw [hm0, zero_mul]
      exact mul_nonneg (by linarith) (by linarith)
    · have hZpos : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZ)
      have hm : m = S / Z := by simp [hmdef, hZ]
      have hIa0 : 0 ≤ ∫ h, |a h| * qW P w h ∂P :=
        integral_nonneg fun h => mul_nonneg (abs_nonneg _) (hq0 h)
      have hIb0 : 0 ≤ ∫ g, |b g| * pW P w g ∂P :=
        integral_nonneg fun g => mul_nonneg (abs_nonneg _) (hp0 g)
      have hT : |T| ≤ ∫ g, |b g| * pW P w g ∂P := by
        rw [hTdef]
        refine (abs_integral_le_integral_abs).trans (integral_mono ((hb1.mul hp).int P).abs
          ((hbA.mul hp).int P) fun g => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (hp0 g)]
      have hG1 : Good fun h g => |a h| * qW P w h * (|b g| * pW P w g) :=
        (haA.mul hq).left.mul (hbA.mul hp).right
      have hG2 : Good fun h g => a h ^ 2 * qW P w h * (pW P w g / 2) :=
        (ha2.mul hq).left.mul (hp.mul (Good1.const (1 / 2))).right |>.of_eq fun h g => by ring
      have hG3 : Good fun h g => qW P w h / 2 * (b g ^ 2 * pW P w g) :=
        (hq.mul (Good1.const (1 / 2))).left.mul (hb2.mul hp).right |>.of_eq fun h g => by ring
      have hprod : (∫ h, |a h| * qW P w h ∂P) * (∫ g, |b g| * pW P w g ∂P) ≤ (A + B) / 2 * Z := by
        rw [← iint_sep P]
        calc ∫ h, ∫ g, |a h| * qW P w h * (|b g| * pW P w g) ∂P ∂P
            ≤ ∫ h, ∫ g, (a h ^ 2 * qW P w h * (pW P w g / 2)
                + qW P w h / 2 * (b g ^ 2 * pW P w g)) ∂P ∂P := by
              refine iint_mono P hG1 (hG2.add hG3) fun h g => ?_
              have hxy : |a h| * |b g| ≤ (a h ^ 2 + b g ^ 2) / 2 := by
                have t := two_mul_le_add_sq (|a h|) (|b g|)
                rw [sq_abs, sq_abs] at t
                linarith
              have t2 := mul_le_mul_of_nonneg_right hxy (mul_nonneg (hq0 h) (hp0 g))
              calc |a h| * qW P w h * (|b g| * pW P w g)
                  = |a h| * |b g| * (qW P w h * pW P w g) := by ring
                _ ≤ (a h ^ 2 + b g ^ 2) / 2 * (qW P w h * pW P w g) := t2
                _ = a h ^ 2 * qW P w h * (pW P w g / 2) + qW P w h / 2 * (b g ^ 2 * pW P w g) := by
                    ring
          _ = A * (Z / 2) + Z / 2 * B := by
              rw [iint_add P hG2 hG3, iint_sep P, iint_sep P, integral_div, hZp,
                integral_div]
          _ = (A + B) / 2 * Z := by ring
      have h1 : |S| * |T| ≤ (k - 1) * (∫ h, |a h| * qW P w h ∂P) * (∫ g, |b g| * pW P w g ∂P) :=
        mul_le_mul hSa hT (abs_nonneg _) (mul_nonneg (by linarith) hIa0)
      have h2 : (k - 1) * (∫ h, |a h| * qW P w h ∂P) * (∫ g, |b g| * pW P w g ∂P)
          ≤ (k - 1) * ((A + B) / 2 * Z) := by
        have t := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ k - 1 by linarith)
        calc (k - 1) * (∫ h, |a h| * qW P w h ∂P) * (∫ g, |b g| * pW P w g ∂P)
            = (k - 1) * ((∫ h, |a h| * qW P w h ∂P) * (∫ g, |b g| * pW P w g ∂P)) := by ring
          _ ≤ (k - 1) * ((A + B) / 2 * Z) := t
      calc m * T ≤ |m * T| := le_abs_self _
        _ = |S| * |T| / Z := by rw [hm, abs_mul, abs_div, abs_of_pos hZpos]; ring
        _ ≤ (k - 1) * ((A + B) / 2 * Z) / Z := by
            apply div_le_div_of_nonneg_right (h1.trans h2) hZpos.le
        _ = (k - 1) / 2 * (A + B) := by field_simp
  -- assemble
  have hD : Good fun h g => w' h g - w h g :=
    (hw'.add ((Good.const (-1)).mul hw)).of_eq fun h g => by ring
  have hL : Good fun h g => a h * b g * (w' h g - w h g) := (ha1.left.mul hb1.right).mul hD
  have hLw : Good fun h g => a h * b g * w h g := (ha1.left.mul hb1.right).mul hw
  have hsum : ∫ h, ∫ g, a h * b g * w' h g ∂P ∂P
      = ∫ h, ∫ g, a h * b g * w h g ∂P ∂P
        + ∫ h, ∫ g, a h * b g * (w' h g - w h g) ∂P ∂P := by
    rw [← iint_add P hLw hL]
    have e : ∀ h g, a h * b g * w' h g = a h * b g * w h g + a h * b g * (w' h g - w h g) :=
      fun h g => by ring
    simp only [e]
  have hHb : ∫ h, ∫ g, (a h - m) * b g * w h g ∂P ∂P ≤ c / 2 * (A + B) :=
    hH.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have hmain : ∫ h, ∫ g, a h * b g * w' h g ∂P ∂P ≤ (c + 2 * (k - 1)) / 2 * (A + B) := by
    rw [hsum, hsplit]
    linarith [hcross, hshift, hHb]
  calc ∫ h, ∫ g, a h * b g * w' h g ∂P ∂P ≤ (c + 2 * (k - 1)) / 2 * (A + B) := hmain
    _ ≤ (c + 2 * (k - 1)) / 2 * (k * (A' + B')) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = k * (c + 2 * (k - 1)) / 2 * (A' + B') := by ring

#print axioms covBoundOn_perturb

/-- **The perturbation bound for bounded measurable test functions** (`covBoundOn_perturb` at that
class, through `covBound_iff_on`).

DERIVED: `2` is the two additive terms; `1` is `e^0`; `0` is the sign of `c` and `ε`. -/
theorem covBound_perturb {w V : Ω → Ω → ℝ} {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hw : Good w) (hw0 : ∀ h g, 0 ≤ w h g) (hVm : Measurable (Function.uncurry V))
    (hVb : ∀ h g, |V h g| ≤ ε) (H : CovBound P w c) :
    CovBound P (fun h g => w h g * Real.exp (V h g))
      (Real.exp ε * (c + 2 * (Real.exp ε - 1))) :=
  (covBound_iff_on _ _ _).2 (covBoundOn_perturb P _ (fun _ h => h)
    (fun a m ha => ⟨ha.1.sub measurable_const, |ha.2.choose| + |m|, fun x =>
      (abs_sub _ _).trans (add_le_add ((ha.2.choose_spec x).trans (le_abs_self _)) le_rfl)⟩)
    hc hε hw hw0 hVm hVb ((covBound_iff_on _ _ _).1 H))

#print axioms covBound_perturb

/-- **The perturbation bound for continuous bounded test functions**, the class
`PairInterface.FibreBound` quantifies over.

DERIVED: `2` is the two additive terms; `1` is `e^0`; `0` is the sign of `c` and `ε`. -/
theorem covBoundOn_perturb_cont [TopologicalSpace Ω] [OpensMeasurableSpace Ω] {w V : Ω → Ω → ℝ}
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (hw : Good w) (hw0 : ∀ h g, 0 ≤ w h g)
    (hVm : Measurable (Function.uncurry V)) (hVb : ∀ h g, |V h g| ≤ ε)
    (H : CovBoundOn (fun a => Continuous a ∧ ∃ C, ∀ x, |a x| ≤ C) P w c) :
    CovBoundOn (fun a => Continuous a ∧ ∃ C, ∀ x, |a x| ≤ C) P
      (fun h g => w h g * Real.exp (V h g)) (Real.exp ε * (c + 2 * (Real.exp ε - 1))) :=
  covBoundOn_perturb P _ (fun _ h => ⟨h.1.measurable, h.2⟩)
    (fun a m ha => ⟨ha.1.sub continuous_const, |ha.2.choose| + |m|, fun x =>
      (abs_sub _ _).trans (add_le_add ((ha.2.choose_spec x).trans (le_abs_self _)) le_rfl)⟩)
    hc hε hw hw0 hVm hVb H

#print axioms covBoundOn_perturb_cont

end Perturb

end MassGap.FibrePerturb
