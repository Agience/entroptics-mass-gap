import Mathlib
import MassGap.StripGap

/-!
# MassGap.StripRow — the 2D torus ratio from the plaquette walk, one row at a time

`StripGap` bounds the convolution powers of the plaquette walk. This module carries that to the 2D torus ratio
`ρ(n) = Z₂(n)/b^{n²}`. Declarations are in `MassGap.StripRow`.

* `oc_eq`: an open chain `∫ ∏ p(a_t v_{t+1} e_t v_t⁻¹)` of class weights through `m` free points is `F_m(Y u⁻¹ Z)`, with
  `Y`, `Z` independent of the start `u`.
* `row_bound`: so a cyclic row of class weights is within `sup |F_m − 1|` of `1`, whatever the insertions.
* `splitR`, `splitR_mp`: the configurations split, measure preserving, into horizontal links and one tuple of vertical
  links per row. `boltz_split`: the Boltzmann weight in those variables; the vertical links of a row enter only that
  row's faces.
* `ratio_row`: `(1 − η)^n ≤ ρ(n) ≤ (1 + η)^n` on side `n = m + 1`, when `|F_m − 1| ≤ η ≤ 1`.

DERIVED (module-wide): `0`, `1` the two directions and the first point; `2` the dimension. No computed or chosen
constant.

## What does not follow

`ratio_row` uses each row only through a sup bound, so it reads decay in the side `n` of the row. The rows are not
glued: the exact statement `ρ(n) = ∫∫ F_{n²−1}([a, b])`, which would give decay in the area `n²`, is not proved here.
-/

namespace MassGap.StripRow

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.TorusDoubling MassGap.StripGap
open MassGap.SUN (SU)

variable {N : ℕ}

/-- Product Haar on `m` points. No numeral. -/
noncomputable abbrev hmv (N m : ℕ) : Measure (Fin m → SU N) := Measure.pi fun _ => hm N

/-! ## 1. An open chain of class weights is one convolution power -/

theorem cont_cons {X : Type*} [TopologicalSpace X] {m : ℕ} {f : X → SU N} {g : X → Fin m → SU N}
    (hf : Continuous f) (hg : Continuous g) (t : Fin (m + 1)) :
    Continuous fun q => Fin.cons (α := fun _ => SU N) (f q) (g q) t := by
  refine Fin.cases ?_ (fun s => ?_) t
  · simpa using hf
  · have h := (continuous_apply s).comp hg
    simpa [Function.comp_def] using h

theorem cont_snoc {X : Type*} [TopologicalSpace X] {m : ℕ} {f : X → SU N} {g : X → Fin m → SU N}
    (hf : Continuous f) (hg : Continuous g) (t : Fin (m + 1)) :
    Continuous fun q => Fin.snoc (α := fun _ => SU N) (g q) (f q) t := by
  refine Fin.lastCases ?_ (fun s => ?_) t
  · simpa using hf
  · have h := (continuous_apply s).comp hg
    simpa [Function.comp_def] using h

/-- **The open chain** from `u` to `w` through `m` free points, with insertions `a`, `e`. No numeral. -/
noncomputable def oc (p : SU N → ℝ) (m : ℕ) (a e : Fin (m + 1) → SU N) (u w : SU N) : ℝ :=
  ∫ V : Fin m → SU N, ∏ t : Fin (m + 1),
    p (a t * Fin.snoc (α := fun _ => SU N) V w t * e t * (Fin.cons (α := fun _ => SU N) u V t)⁻¹)
    ∂hmv N m

theorem oc_zero (p : SU N → ℝ) (a e : Fin 1 → SU N) (u w : SU N) :
    oc p 0 a e u w = p (a 0 * w * e 0 * u⁻¹) := by
  unfold oc
  have hc : ∀ V : Fin 0 → SU N, Fin.cons (α := fun _ => SU N) u V 0 = u := fun V => Fin.cons_zero _ _
  have hs : ∀ V : Fin 0 → SU N, Fin.snoc (α := fun _ => SU N) V w 0 = w := fun V => by
    simpa using (Fin.snoc_last (α := fun _ => SU N) w V)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, hc, hs]
  rw [integral_const]
  simp

theorem oc_succ {p : SU N → ℝ} (hp : Continuous p) (m : ℕ) (a e : Fin (m + 2) → SU N) (u w : SU N) :
    oc p (m + 1) a e u w
      = ∫ y, p (a 0 * y * e 0 * u⁻¹) * oc p m (a ∘ Fin.succ) (e ∘ Fin.succ) y w ∂hm N := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hp.continuousOn
  have hC' : ∀ g, |p g| ≤ C := fun g => by
    have := hC g (mem_univ g)
    rwa [Real.norm_eq_abs] at this
  unfold oc
  have hmeas : Measurable fun V : Fin (m + 1) → SU N => ∏ t : Fin (m + 2),
      p (a t * Fin.snoc (α := fun _ => SU N) V w t * e t * (Fin.cons (α := fun _ => SU N) u V t)⁻¹) := by
    refine Continuous.measurable (continuous_finsetProd _ fun t _ => hp.comp ?_)
    exact ((continuous_const.mul (cont_snoc continuous_const continuous_id t)).mul
      continuous_const).mul (cont_cons continuous_const continuous_id t).inv
  rw [CyclicKernel.integral_cons hmeas (C := C ^ Fintype.card (Fin (m + 2)))
    (fun W => CyclicKernel.abs_prod_le fun t => hC' _)]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext V
  rw [Fin.prod_univ_succ]
  simp [← Fin.cons_snoc_eq_snoc_cons]

/-- **An open chain is a convolution power**: `∫ ∏ p(a_t v_{t+1} e_t v_t⁻¹) = F_m(Y u⁻¹ Z)`, with `Y`, `Z`
independent of the start `u`. The free point is moved onto the argument of `F` by two-sided invariance, inversion and
the class property. DERIVED: `0` the first point. -/
theorem oc_eq {p : SU N → ℝ} (hp : Dens p) (m : ℕ) :
    ∀ (a e : Fin (m + 1) → SU N) (w : SU N), ∃ Y Z : SU N, ∀ u, oc p m a e u w = Fk p m (Y * u⁻¹ * Z) := by
  induction m with
  | zero =>
    intro a e w
    refine ⟨a 0 * w * e 0, 1, fun u => ?_⟩
    rw [oc_zero, mul_one]
    rfl
  | succ m ih =>
    intro a e w
    obtain ⟨Y, Z, hYZ⟩ := ih (a ∘ Fin.succ) (e ∘ Fin.succ) w
    refine ⟨Y * e 0, a 0 * Z, fun u => ?_⟩
    rw [oc_succ hp.cont]
    simp_rw [hYZ]
    set X : SU N := Y * e 0 * u⁻¹ * (a 0 * Z) with hX
    set B : SU N := X⁻¹ * Y with hB
    set G : SU N → ℝ := fun y => p (a 0 * y * e 0 * u⁻¹) * Fk p m (Y * y⁻¹ * Z) with hG
    have hsub : ∫ y, G y ∂hm N = ∫ z, G (Z * z⁻¹ * B) ∂hm N := by
      have h1 := integral_inv_eq_self (fun z => G (Z * z * B)) (hm N)
      have h2 := HeatBath.integral_twoSided G Z B
      exact (h1.trans h2).symm
    show ∫ y, G y ∂hm N = Pop p (Fk p m) X
    rw [hsub]
    unfold Pop
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hG]
    have e1 : Y * (Z * z⁻¹ * B)⁻¹ * Z = X * z := by
      rw [hB]; group
    have e2 : a 0 * (Z * z⁻¹ * B) * e 0 * u⁻¹ = (a 0 * Z) * (z⁻¹ * (a 0 * Z)⁻¹) := by
      rw [hB, hX]; group
    rw [e1, e2, hp.cyc, mul_assoc, inv_mul_cancel, mul_one, hp.inv, mul_comm]

/-- **A cyclic row of class weights is close to one**: if `|F_m − 1| ≤ η`, the integral of the cyclic product over
the `m + 1` free links of a row is within `η` of `1`, whatever the insertions. DERIVED: `1` the mass. -/
theorem row_bound {p : SU N → ℝ} (hp : Dens p) {m : ℕ} {η : ℝ} (hη : ∀ x, |Fk p m x - 1| ≤ η)
    (a e : Fin (m + 1) → SU N) :
    |∫ v : Fin (m + 1) → SU N, ∏ t, p (a t * v (finRotate (m + 1) t) * e t * (v t)⁻¹) ∂hmv N (m + 1) - 1|
      ≤ η := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hp.cont.continuousOn
  have hC' : ∀ g, |p g| ≤ C := fun g => by
    have := hC g (mem_univ g)
    rwa [Real.norm_eq_abs] at this
  have hcont : Continuous fun v : Fin (m + 1) → SU N =>
      ∏ t, p (a t * v (finRotate (m + 1) t) * e t * (v t)⁻¹) := by
    refine continuous_finsetProd _ fun t _ => hp.cont.comp ?_
    exact ((continuous_const.mul (continuous_apply _)).mul continuous_const).mul (continuous_apply _).inv
  rw [CyclicKernel.integral_cons hcont.measurable (C := C ^ Fintype.card (Fin (m + 1)))
    (fun W => CyclicKernel.abs_prod_le fun t => hC' _)]
  have hJ : ∀ y, ∫ V : Fin m → SU N, ∏ t, p (a t * (Fin.cons (α := fun _ => SU N) y V
        (finRotate (m + 1) t)) * e t * (Fin.cons (α := fun _ => SU N) y V t)⁻¹) ∂hmv N m
      = oc p m a e y y := by
    intro y
    unfold oc
    refine integral_congr_ae (Eventually.of_forall fun V => ?_)
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Fin.snoc_eq_cons_rotate]
  simp_rw [hJ]
  have hbd : ∀ y, |oc p m a e y y - 1| ≤ η := by
    intro y
    obtain ⟨Y, Z, h⟩ := oc_eq hp m a e y
    rw [h]
    exact hη _
  have hcJ : Continuous fun y => oc p m a e y y := by
    have hf : Continuous (Function.uncurry fun (y : SU N) (V : Fin m → SU N) => ∏ t : Fin (m + 1),
        p (a t * Fin.snoc (α := fun _ => SU N) V y t * e t * (Fin.cons (α := fun _ => SU N) y V t)⁻¹)) := by
      refine continuous_finsetProd _ fun t _ => hp.cont.comp ?_
      exact ((continuous_const.mul (cont_snoc (f := fun q : SU N × (Fin m → SU N) => q.1)
        (g := fun q => q.2) continuous_fst continuous_snd t)).mul continuous_const).mul
        (cont_cons (f := fun q : SU N × (Fin m → SU N) => q.1)
        (g := fun q => q.2) continuous_fst continuous_snd t).inv
    have h := continuous_parametric_integral_of_continuous (μ := hmv N m) hf isCompact_univ
    simp only [Measure.restrict_univ] at h
    exact h
  have e0 : ∫ y, oc p m a e y y ∂hm N - 1 = ∫ y, (oc p m a e y y - 1) ∂hm N := by
    rw [isub hcJ continuous_const, const_prob]
  rw [e0]
  calc |∫ y, (oc p m a e y y - 1) ∂hm N| ≤ ∫ y, |oc p m a e y y - 1| ∂hm N :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y : SU N, η ∂hm N :=
        integral_mono (int_of_cont (hcJ.sub continuous_const).abs) (integrable_const _) hbd
    _ = η := const_prob _

/-! ## 2. Splitting the torus into horizontal links and rows of vertical links -/

variable {n : ℕ}

/-- The site with coordinates `c`, `r`. No numeral. -/
def pt (c r : Fin n) : TSite 2 n := ![c, r]

variable (n) in
/-- The links: a horizontal link is its site; a vertical link is a row and a column. DERIVED: `0`, `1` the two
directions. -/
def linkE : TSite 2 n ⊕ (Fin n × Fin n) ≃ TLink 2 n where
  toFun := Sum.elim (fun x => (0, x)) (fun q => (1, pt q.2 q.1))
  invFun l := if l.1 = 0 then Sum.inl l.2 else Sum.inr (l.2 1, l.2 0)
  left_inv := by
    rintro (x | ⟨r, c⟩)
    · simp
    · simp [pt]
  right_inv := by
    rintro ⟨i, x⟩
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Sum.elim_inr]
      refine Prod.ext rfl ?_
      funext j
      fin_cases j <;> simp [pt]

/-- The configurations of the rows split: horizontal links, and for each row its vertical links. No numeral. -/
abbrev RowCfg (n N : ℕ) : Type := (TSite 2 n → SU N) × (Fin n → Fin n → SU N)

/-- **The row splitting** of the 2D torus. No numeral. -/
noncomputable def splitR (n N : ℕ) : (TLink 2 n → SU N) ≃ᵐ RowCfg n N :=
  (MeasurableEquiv.piCongrLeft (fun _ : TLink 2 n => SU N) (linkE n)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : TSite 2 n ⊕ (Fin n × Fin n) => SU N)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin n) (Fin n) (SU N))))

theorem splitR_mp : MeasurePreserving (splitR n N) (Measure.pi fun _ : TLink 2 n => hm N)
    ((Measure.pi fun _ : TSite 2 n => hm N).prod (Measure.pi fun _ : Fin n => hmv N n)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : TLink 2 n => SU N) (linkE n))
      (Measure.pi fun _ : TSite 2 n ⊕ (Fin n × Fin n) => hm N) (Measure.pi fun _ : TLink 2 n => hm N) :=
    measurePreserving_piCongrLeft (μ := fun _ : TLink 2 n => hm N) (linkE n)
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : TSite 2 n ⊕ (Fin n × Fin n) => hm N)
  have hmap := Measure.infinitePi_map_curry (X := SU N) (ι := Fin n) (κ := Fin n) (fun _ _ => hm N)
  simp only [Measure.infinitePi_eq_pi] at hmap
  have h3 : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin n) (SU N))
      (Measure.pi fun _ : Fin n × Fin n => hm N) (Measure.pi fun _ : Fin n => hmv N n) :=
    ⟨(MeasurableEquiv.curry (Fin n) (Fin n) (SU N)).measurable, hmap⟩
  have h4 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (TSite 2 n → SU N))
      (MeasurableEquiv.curry (Fin n) (Fin n) (SU N)))
      ((Measure.pi fun _ : TSite 2 n => hm N).prod (Measure.pi fun _ : Fin n × Fin n => hm N))
      ((Measure.pi fun _ : TSite 2 n => hm N).prod (Measure.pi fun _ : Fin n => hmv N n)) :=
    (MeasurePreserving.id _).prod h3
  exact h4.comp (h2.comp (MeasurePreserving.symm _ h1))

theorem splitR_fst (U : TLink 2 n → SU N) (x : TSite 2 n) : (splitR n N U).1 x = U (0, x) := rfl

theorem splitR_snd (U : TLink 2 n → SU N) (r c : Fin n) : (splitR n N U).2 r c = U (1, pt c r) := rfl

theorem tshift_pt0 (c r : Fin n) : tshift 0 (pt c r) = pt (finRotate n c) r := by
  funext j
  fin_cases j <;> simp [pt, tshift]

theorem tshift_pt1 (c r : Fin n) : tshift 1 (pt c r) = pt c (finRotate n r) := by
  funext j
  fin_cases j <;> simp [pt, tshift]

theorem prod_sites (f : TSite 2 n → ℝ) : ∏ x, f x = ∏ r, ∏ c, f (pt c r) := by
  rw [← (finTwoArrowEquiv (Fin n)).symm.prod_comp, Fintype.prod_prod_type, Finset.prod_comm]
  rfl

/-- The weight of a row split: one face in row `r`, column `c`. No numeral. -/
noncomputable def faceR (β : ℝ) (A : TSite 2 n → SU N) (r : Fin n) (v : Fin n → SU N) (c : Fin n) : ℝ :=
  TwoDVanish.wt β (A (pt c r) * v (finRotate n c) * (A (pt c (finRotate n r)))⁻¹ * (v c)⁻¹)

theorem boltz_split (β : ℝ) (U : TLink 2 n → SU N) :
    ∏ x, TwoDVanish.wt β (TwoDVanish.face x U)
      = ∏ r, ∏ c, faceR β (splitR n N U).1 r ((splitR n N U).2 r) c := by
  rw [prod_sites]
  refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun c _ => ?_
  unfold faceR TwoDVanish.face
  rw [tshift_pt0, tshift_pt1]
  rfl

theorem cont_faceR (β : ℝ) (r c : Fin n) : Continuous fun q : RowCfg n N =>
    faceR β q.1 r (q.2 r) c := by
  unfold faceR
  refine (continuous_wt β).comp ?_
  have e1 : Continuous fun q : RowCfg n N => q.1 (pt c r) := (continuous_apply _).comp continuous_fst
  have e3 : Continuous fun q : RowCfg n N => q.1 (pt c (finRotate n r)) :=
    (continuous_apply _).comp continuous_fst
  have e2 : ∀ d : Fin n, Continuous fun q : RowCfg n N => q.2 r d := fun d =>
    (continuous_apply d).comp ((continuous_apply r).comp continuous_snd)
  exact ((e1.mul (e2 _)).mul e3.inv).mul (e2 c).inv

/-- **The ratio, row by row**: on a side `m + 1`, `|F_m − 1| ≤ η ≤ 1` gives
`(1 − η)^{m+1} ≤ ρ(m + 1) ≤ (1 + η)^{m+1}`. Each row's vertical links enter only that row's faces, so the row
integrals factor, and each is within `η` of `b^{m+1}` whatever the horizontal links (`row_bound`). DERIVED: `1` the
ratio at equilibrium; `2` the dimension. -/
theorem ratio_row (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {m : ℕ} {η : ℝ} (hη1 : η ≤ 1)
    (hη : ∀ x, |Fk (pW N β) m x - 1| ≤ η) :
    (1 - η) ^ (m + 1) ≤ TwoDVanish.ratio N β (m + 1)
      ∧ TwoDVanish.ratio N β (m + 1) ≤ (1 + η) ^ (m + 1) := by
  set n : ℕ := m + 1 with hn
  have hb := TwoDVanish.bk_pos hN hβ
  set b : ℝ := TwoDVanish.bk N β with hbdef
  have hpd := pW_dens hN hβ
  set Fq : RowCfg n N → ℝ := fun q => ∏ r, ∏ c, faceR β q.1 r (q.2 r) c with hFq
  have hFc : Continuous Fq :=
    continuous_finsetProd _ fun r _ => continuous_finsetProd _ fun c _ => cont_faceR β r c
  have hFi : Integrable Fq
      ((Measure.pi fun _ : TSite 2 n => hm N).prod (Measure.pi fun _ : Fin n => hmv N n)) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hFc.continuousOn
    exact ContactFloor.integrable_of_bounded hFc.measurable M fun z => by
      have hz := hM z (mem_univ z)
      rwa [Real.norm_eq_abs] at hz
  have hZ : TorusDoubling.ZT (SU N) 2 WilsonAction.wilsonDensity β n
      = ∫ A, ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin n => hmv N n)
          ∂(Measure.pi fun _ : TSite 2 n => hm N) := by
    have h1 : TorusDoubling.ZT (SU N) 2 WilsonAction.wilsonDensity β n
        = ∫ U, Fq (splitR n N U) ∂(Measure.pi fun _ : TLink 2 n => hm N) := by
      unfold TorusDoubling.ZT LatticeGauge.System.partition LatticeGauge.System.vol
      refine integral_congr_ae (Eventually.of_forall fun U => ?_)
      show _ = Fq (splitR n N U)
      rw [TwoDVanish.boltz_eq hN β U, boltz_split]
    rw [h1, (splitR_mp (n := n) (N := N)).integral_comp' Fq, integral_prod _ hFi]
  have hrow : ∀ (A : TSite 2 n → SU N) (r : Fin n),
      ∃ J : ℝ, ∫ v, ∏ c, faceR β A r v c ∂hmv N n = b ^ n * J ∧ |J - 1| ≤ η := by
    intro A r
    refine ⟨_, ?_, row_bound (m := m) hpd hη (fun c => A (pt c r)) (fun c => (A (pt c (finRotate n r)))⁻¹)⟩
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    show ∏ c, faceR β A r v c = _
    have e : ∀ c, faceR β A r v c
        = b * pW N β (A (pt c r) * v (finRotate n c) * (A (pt c (finRotate n r)))⁻¹ * (v c)⁻¹) := by
      intro c
      unfold faceR pW
      rw [mul_div_cancel₀ _ hb.ne']
    simp_rw [e]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 1)
  have hΨ : ∀ A : TSite 2 n → SU N,
      (b ^ n * (1 - η)) ^ n ≤ ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin n => hmv N n)
        ∧ ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin n => hmv N n) ≤ (b ^ n * (1 + η)) ^ n := by
    intro A
    have e : ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin n => hmv N n)
        = ∏ r, ∫ v, ∏ c, faceR β A r v c ∂hmv N n :=
      integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun r v => ∏ c, faceR β A r v c)
    rw [e]
    have hpw : 0 ≤ b ^ n := by positivity
    have h1 : ∀ r, b ^ n * (1 - η) ≤ ∫ v, ∏ c, faceR β A r v c ∂hmv N n := by
      intro r
      obtain ⟨J, hJ, hJ1⟩ := hrow A r
      rw [hJ]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 hJ1).1]) hpw
    have h2 : ∀ r, ∫ v, ∏ c, faceR β A r v c ∂hmv N n ≤ b ^ n * (1 + η) := by
      intro r
      obtain ⟨J, hJ, hJ1⟩ := hrow A r
      rw [hJ]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 hJ1).2]) hpw
    have hlow : 0 ≤ b ^ n * (1 - η) := mul_nonneg hpw (by linarith)
    constructor
    · calc (b ^ n * (1 - η)) ^ n = ∏ _r : Fin n, b ^ n * (1 - η) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlow) fun r _ => h1 r
    · calc ∏ r, ∫ v, ∏ c, faceR β A r v c ∂hmv N n ≤ ∏ _r : Fin n, b ^ n * (1 + η) :=
            Finset.prod_le_prod (fun r _ => hlow.trans (h1 r)) fun r _ => h2 r
        _ = _ := by simp
  have hint := hFi.integral_prod_left
  have hbn : 0 < b ^ (n ^ 2) := by positivity
  have hpow : ∀ c : ℝ, (b ^ n * c) ^ n = b ^ (n ^ 2) * c ^ n := by
    intro c
    rw [mul_pow, ← pow_mul, pow_two]
  have hlo : (b ^ n * (1 - η)) ^ n ≤ TorusDoubling.ZT (SU N) 2 WilsonAction.wilsonDensity β n := by
    rw [hZ]
    calc (b ^ n * (1 - η)) ^ n
        = ∫ _A : TSite 2 n → SU N, (b ^ n * (1 - η)) ^ n ∂(Measure.pi fun _ : TSite 2 n => hm N) := by
          simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun A => (hΨ A).1
  have hhi : TorusDoubling.ZT (SU N) 2 WilsonAction.wilsonDensity β n ≤ (b ^ n * (1 + η)) ^ n := by
    rw [hZ]
    calc _ ≤ ∫ _A : TSite 2 n → SU N, (b ^ n * (1 + η)) ^ n ∂(Measure.pi fun _ : TSite 2 n => hm N) :=
          integral_mono hint (integrable_const _) fun A => (hΨ A).2
      _ = _ := by simp
  unfold TwoDVanish.ratio
  rw [hpow] at hlo hhi
  constructor
  · rw [le_div_iff₀ hbn]; linarith
  · rw [div_le_iff₀ hbn]; linarith

end MassGap.StripRow

#print axioms MassGap.StripRow.oc_eq
#print axioms MassGap.StripRow.row_bound
#print axioms MassGap.StripRow.splitR_mp
#print axioms MassGap.StripRow.boltz_split
#print axioms MassGap.StripRow.ratio_row
