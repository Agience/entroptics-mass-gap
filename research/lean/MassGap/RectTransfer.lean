import Mathlib
import MassGap.RectWilson
import MassGap.CyclicKernel

/-!
# MassGap.RectTransfer — the gauge-projected transfer kernel of the rectangular Wilson torus

Direction `μ`, transverse extents fixed. With `Ax = TS → SU(N)` (the axis links of one slice) and
`Sp = SpIdx → SU(N)` (its spatial links), both with product Haar measure:

* `gk V V' = ∫ exp(−2β tp(A, V, V')) dA` — integrating the axis links of one slice is the
  Gauss-law projection of the temporal-gauge kernel;
* `kT V V' = e^{−β sp(V)/2} gk(V,V') e^{−β sp(V')/2}`, the symmetric transfer kernel.

Proved:

* `ZR_eq_cyc` — `ZR L N β = cyc (Haar on Sp) kT (L μ)` at every real `β` (`N ≠ 0`);
* `gk_symm`, `kT_symm` — symmetry, by `A ↦ A⁻¹` (`Reflect.isInvInvariant_probHaar`) and the
  plaquette identity `ρ(a⁻¹ v b w⁻¹) = ρ(a w b⁻¹ v⁻¹)`;
* `continuous_kT` — joint continuity (`continuous_parametric_integral_of_continuous`);
* `kT_le_one`, `kT_lower` — `0 < ε ≤ kT ≤ 1` at `β ≥ 0`;
* `ZR_eq_traceSeq` — for `L μ = 2j`, `j ≥ 1`: `ZR = KernelPower.traceSeq (Haar) kT (L μ)`.
-/

namespace MassGap.RectTransfer

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.KernelPower
  MassGap.CyclicKernel

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-- Haar measure on axis configurations of one slice. -/
noncomputable abbrev hA (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) : Measure (TT μ T → SUN.SU N) :=
  Measure.pi fun _ : TT μ T => probHaar (SUN.SU N)

/-- Haar measure on spatial configurations of one slice. -/
noncomputable abbrev hS (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) : Measure (SpT μ T → SUN.SU N) :=
  Measure.pi fun _ : SpT μ T => probHaar (SUN.SU N)

variable (μ T N) in
/-- The axis-integrated temporal factor. -/
noncomputable def gk (β : ℝ) (V V' : SpT μ T → SUN.SU N) : ℝ :=
  ∫ A, Real.exp (-β * (2 * tpT μ T A V V')) ∂(hA μ T N)

variable (μ T N) in
/-- The symmetric transfer kernel. -/
noncomputable def kT (β : ℝ) (V V' : SpT μ T → SUN.SU N) : ℝ :=
  Real.exp (-β * spT μ T V / 2) * gk μ T N β V V' * Real.exp (-β * spT μ T V' / 2)

/-! ## Continuity -/

theorem continuous_tp {Y : Type*} [TopologicalSpace Y] {f : Y → TT μ T → SUN.SU N}
    {g h : Y → SpT μ T → SUN.SU N} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun q => tpT μ T (f q) (g q) (h q) := by
  unfold tpT
  refine continuous_finset_sum _ fun ν _ => continuous_finset_sum _ fun y _ => ?_
  refine WilsonAction.continuous_wilsonDensity.comp ?_
  have e1 : Continuous fun q => f q y := (continuous_apply y).comp hf
  have e2 : Continuous fun q => h q (ν, y) := (continuous_apply (ν, y)).comp hh
  have e3 : Continuous fun q => f q (tsh μ T ν y) := (continuous_apply _).comp hf
  have e4 : Continuous fun q => g q (ν, y) := (continuous_apply (ν, y)).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_sp {Y : Type*} [TopologicalSpace Y] {g : Y → SpT μ T → SUN.SU N}
    (hg : Continuous g) : Continuous fun q => spT μ T (g q) := by
  unfold spT
  refine continuous_finset_sum _ fun ν _ => continuous_finset_sum _ fun ν' _ =>
    continuous_finset_sum _ fun y _ => ?_
  refine WilsonAction.continuous_wilsonDensity.comp ?_
  have e1 : Continuous fun q => g q (ν, y) := (continuous_apply _).comp hg
  have e2 : Continuous fun q => g q (ν', tsh μ T ν y) := (continuous_apply _).comp hg
  have e3 : Continuous fun q => g q (ν, tsh μ T ν' y) := (continuous_apply _).comp hg
  have e4 : Continuous fun q => g q (ν', y) := (continuous_apply _).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_gk (β : ℝ) :
    Continuous (Function.uncurry (gk μ T N β)) := by
  have hf0 : Continuous fun q : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × (TT μ T → SUN.SU N) => Real.exp (-β * (2 * tpT μ T q.2 q.1.1 q.1.2)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_tp continuous_snd continuous_fst.fst continuous_fst.snd)))
  have hf : Continuous (Function.uncurry fun (p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      (A : TT μ T → SUN.SU N) => Real.exp (-β * (2 * tpT μ T A p.1 p.2))) := hf0
  have h := continuous_parametric_integral_of_continuous (μ := hA μ T N) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

theorem continuous_kT (β : ℝ) : Continuous (Function.uncurry (kT μ T N β)) := by
  unfold kT
  have h1 : Continuous fun p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      Real.exp (-β * spT μ T p.1 / 2) :=
    Real.continuous_exp.comp (((continuous_const.mul (continuous_sp continuous_fst))).div_const _)
  have h2 : Continuous fun p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      Real.exp (-β * spT μ T p.2 / 2) :=
    Real.continuous_exp.comp (((continuous_const.mul (continuous_sp continuous_snd))).div_const _)
  exact (h1.mul (continuous_gk β)).mul h2

/-! ## Symmetry -/

theorem tp_inv (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    tpT μ T (fun y => (A y)⁻¹) V' V = tpT μ T A V V' := by
  unfold tpT
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y _ => ?_
  set a := A y
  set b := A (tsh μ T ν y)
  set v := V (ν, y)
  set w := V' (ν, y)
  have e : a⁻¹ * v * (b⁻¹)⁻¹ * w⁻¹ = a⁻¹ * (a * w * b⁻¹ * v⁻¹)⁻¹ * a⁻¹⁻¹ := by group
  rw [e, WilsonAction.wilsonDensity_conj, wilsonDensity_inv]

theorem measurePreserving_invAx :
    MeasurePreserving (fun (A : TT μ T → SUN.SU N) y => (A y)⁻¹) (hA μ T N) (hA μ T N) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU N)) (fun _ => probHaar (SUN.SU N))
    (fun _ => Measure.measurePreserving_inv (probHaar (SUN.SU N)))

theorem gk_symm (β : ℝ) (V V' : SpT μ T → SUN.SU N) : gk μ T N β V V' = gk μ T N β V' V := by
  set e := MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv (SUN.SU N))
  have hmp : MeasurePreserving e (hA μ T N) (hA μ T N) := measurePreserving_invAx
  unfold gk
  rw [← hmp.integral_comp' (fun A => Real.exp (-β * (2 * tpT μ T A V' V)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  have hA' : (e A) = fun y => (A y)⁻¹ := rfl
  show Real.exp (-β * (2 * tpT μ T A V V')) = Real.exp (-β * (2 * tpT μ T (e A) V' V))
  rw [hA', tp_inv]

theorem kT_symm (β : ℝ) (V V' : SpT μ T → SUN.SU N) : kT μ T N β V V' = kT μ T N β V' V := by
  unfold kT; rw [gk_symm]; ring

/-! ## Bounds -/

theorem tp_nonneg (hN : N ≠ 0) (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    0 ≤ tpT μ T A V V' :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => WilsonAction.wilsonDensity_nonneg hN _

theorem sp_nonneg (hN : N ≠ 0) (V : SpT μ T → SUN.SU N) : 0 ≤ spT μ T V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    WilsonAction.wilsonDensity_nonneg hN _

variable (μ T) in
/-- A bound for `tp`. -/
def tpMax : ℝ := 2 * (Fintype.card {j : Fin 4 // j ≠ μ} * Fintype.card (TT μ T))

variable (μ T) in
/-- A bound for `sp`. -/
def spMax : ℝ := 2 * (Fintype.card {j : Fin 4 // j ≠ μ} * Fintype.card {j : Fin 4 // j ≠ μ}
  * Fintype.card (TT μ T))

theorem tp_le (hN : N ≠ 0) (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    tpT μ T A V V' ≤ tpMax μ T := by
  unfold tpT tpMax
  calc _ ≤ ∑ _ν : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, (2 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => WilsonAction.wilsonDensity_le_two hN _
    _ = _ := by simp; ring

theorem sp_le (hN : N ≠ 0) (V : SpT μ T → SUN.SU N) : spT μ T V ≤ spMax μ T := by
  unfold spT spMax
  calc _ ≤ ∑ _ν : {j : Fin 4 // j ≠ μ}, ∑ _ν' : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, (2 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
          WilsonAction.wilsonDensity_le_two hN _
    _ = _ := by simp; ring

theorem gk_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → SUN.SU N) :
    gk μ T N β V V' ≤ 1 := by
  unfold gk
  calc _ ≤ ∫ _A, (1 : ℝ) ∂(hA μ T N) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun A => (Real.exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall fun A => ?_)
        rw [Real.exp_le_one_iff]
        have := tp_nonneg hN A V V'
        nlinarith
    _ = 1 := by simp

theorem gk_ge (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → SUN.SU N) :
    Real.exp (-β * (2 * tpMax μ T)) ≤ gk μ T N β V V' := by
  unfold gk
  have hm : Measurable fun A : TT μ T → SUN.SU N => Real.exp (-β * (2 * tpT μ T A V V')) := by
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_tp continuous_id continuous_const continuous_const)))).measurable
  calc Real.exp (-β * (2 * tpMax μ T)) = ∫ _A, Real.exp (-β * (2 * tpMax μ T)) ∂(hA μ T N) := by
        simp
    _ ≤ _ := by
        refine integral_mono (integrable_const _) ?_ (fun A => ?_)
        · exact integrable_of_bdd hm (C := 1) (fun A => by
            rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
            have := tp_nonneg hN A V V'; nlinarith)
        · rw [Real.exp_le_exp]
          have := tp_le hN A V V'
          nlinarith

theorem kT_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → SUN.SU N) :
    kT μ T N β V V' ≤ 1 := by
  unfold kT
  have h1 : Real.exp (-β * spT μ T V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg hN V; nlinarith
  have h2 : Real.exp (-β * spT μ T V' / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg hN V'; nlinarith
  have h3 := gk_le_one hN hβ V V'
  have h0 : 0 ≤ gk μ T N β V V' := (Real.exp_pos _).le.trans (gk_ge hN hβ V V')
  exact mul_le_one₀ (mul_le_one₀ h1 h0 h3) (Real.exp_pos _).le h2

variable (μ T) in
/-- The lower bound for `kT`. -/
noncomputable def kTmin (β : ℝ) : ℝ := Real.exp (-β * spMax μ T) * Real.exp (-β * (2 * tpMax μ T))

theorem kTmin_pos (β : ℝ) : 0 < kTmin μ T β := by unfold kTmin; positivity

theorem kT_lower (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → SUN.SU N) :
    kTmin μ T β ≤ kT μ T N β V V' := by
  unfold kT kTmin
  have h1 : Real.exp (-β * spMax μ T / 2) ≤ Real.exp (-β * spT μ T V / 2) := by
    rw [Real.exp_le_exp]; have := sp_le hN V; nlinarith
  have h2 : Real.exp (-β * spMax μ T / 2) ≤ Real.exp (-β * spT μ T V' / 2) := by
    rw [Real.exp_le_exp]; have := sp_le hN V'; nlinarith
  have h3 := gk_ge hN hβ V V'
  have e : Real.exp (-β * spMax μ T) = Real.exp (-β * spMax μ T / 2) * Real.exp (-β * spMax μ T / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  calc Real.exp (-β * spMax μ T / 2) * Real.exp (-β * spMax μ T / 2) * Real.exp (-β * (2 * tpMax μ T))
      = Real.exp (-β * spMax μ T / 2) * Real.exp (-β * (2 * tpMax μ T)) * Real.exp (-β * spMax μ T / 2) := by ring
    _ ≤ _ := by
        have h0 : 0 ≤ gk μ T N β V V' := (Real.exp_pos _).le.trans h3
        exact mul_le_mul (mul_le_mul h1 h3 (Real.exp_pos _).le (Real.exp_pos _).le) h2
          (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le h0)

theorem abs_kT_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → SUN.SU N) :
    |kT μ T N β V V'| ≤ 1 := by
  rw [abs_of_nonneg ((kTmin_pos β).le.trans (kT_lower hN hβ V V'))]
  exact kT_le_one hN hβ V V'

/-! ## The partition function as a cyclic kernel integral -/

variable {L : Fin 4 → ℕ}

theorem ZR_eq_cyc (hN : N ≠ 0) (β : ℝ) :
    ZR L N β = cyc (hS μ (tr L μ) N) (kT μ (tr L μ) N β) (L μ) := by
  rw [ZR_eq_integral (μ := μ) hN β]
  -- split each slice into axis and spatial parts
  have hmp1 : MeasurePreserving
      (fun (W : Fin (L μ) → SlIdx L μ → SUN.SU N) t =>
        MeasurableEquiv.sumPiEquivProdPi (fun _ : SlIdx L μ => SUN.SU N) (W t))
      (Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))
      (Measure.pi fun _ : Fin (L μ) => (hA μ (tr L μ) N).prod (hS μ (tr L μ) N)) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_sumPiEquivProdPi _
  have hmp2 := measurePreserving_arrowProdEquivProdArrow (TS L μ → SUN.SU N)
    (SpIdx L μ → SUN.SU N) (Fin (L μ)) (fun _ => hA μ (tr L μ) N) (fun _ => hS μ (tr L μ) N)
  have hmp := hmp2.comp hmp1
  set G : (Fin (L μ) → TS L μ → SUN.SU N) × (Fin (L μ) → SpIdx L μ → SUN.SU N) → ℝ :=
    fun p => ∏ t, Real.exp (-β * (sp L μ (p.2 t)
      + 2 * tp L μ (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))))
  have hG : Continuous G := by
    refine continuous_finset_prod _ fun t _ => Real.continuous_exp.comp
      (continuous_const.mul ((continuous_sp ((continuous_apply t).comp continuous_snd)).add
        (continuous_const.mul (continuous_tp ((continuous_apply t).comp continuous_fst)
          ((continuous_apply t).comp continuous_snd)
          ((continuous_apply (finRotate (L μ) t)).comp continuous_snd)))))
  have h1 : ∫ W : Fin (L μ) → SlIdx L μ → SUN.SU N, ∏ t, Real.exp (-β * (sp L μ (spOf (W t))
      + 2 * tp L μ (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))
      = ∫ p, G p ∂((Measure.pi fun _ : Fin (L μ) => hA μ (tr L μ) N).prod
          (Measure.pi fun _ : Fin (L μ) => hS μ (tr L μ) N)) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [h1]
  have hGb : ∀ p, |G p| ≤ (Real.exp (|β| * (spMax μ (tr L μ) + 2 * tpMax μ (tr L μ)))) ^ Fintype.card (Fin (L μ)) := by
    intro p
    refine abs_prod_le fun t => ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have a1 := sp_nonneg hN (p.2 t)
    have a2 := sp_le hN (p.2 t)
    have a3 := tp_nonneg hN (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))
    have a4 := tp_le hN (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))
    have : -β * (sp L μ (p.2 t) + 2 * tp L μ (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t)))
        ≤ |β| * (sp L μ (p.2 t) + 2 * tp L μ (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))) := by
      have := neg_abs_le β
      nlinarith [abs_nonneg β]
    nlinarith [abs_nonneg β]
  rw [integral_prod_symm _ (integrable_of_bdd hG.measurable hGb)]
  unfold cyc
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  -- integrate out the axis links slice by slice
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin (L μ) => hA μ (tr L μ) N)
    (fun t (a : TS L μ → SUN.SU N) => Real.exp (-β * (sp L μ (V t)
      + 2 * tp L μ a (V t) (V (finRotate (L μ) t)))))
  show ∫ A, ∏ t, Real.exp (-β * (sp L μ (V t)
      + 2 * tp L μ (A t) (V t) (V (finRotate (L μ) t)))) ∂(Measure.pi fun _ : Fin (L μ) => hA μ (tr L μ) N) = _
  rw [hprod]
  have hfac : ∀ t, ∫ a, Real.exp (-β * (sp L μ (V t) + 2 * tp L μ a (V t) (V (finRotate (L μ) t))))
      ∂(hA μ (tr L μ) N) = Real.exp (-β * sp L μ (V t)) * gk μ (tr L μ) N β (V t) (V (finRotate (L μ) t)) := by
    intro t
    unfold gk
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]; ring_nf
  simp_rw [hfac]
  unfold kT
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hrot : ∏ t, Real.exp (-β * sp L μ (V (finRotate (L μ) t)) / 2)
      = ∏ t, Real.exp (-β * sp L μ (V t) / 2) :=
    Fintype.prod_equiv (finRotate (L μ)) _ _ (fun t => rfl)
  rw [hrot]
  have hhalf : ∏ t, Real.exp (-β * sp L μ (V t))
      = (∏ t, Real.exp (-β * sp L μ (V t) / 2)) * ∏ t, Real.exp (-β * sp L μ (V t) / 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Real.exp_add]; ring_nf
  rw [hhalf]; ring

theorem bdd_kT (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : Bdd (kT μ T N β) :=
  ⟨(continuous_kT β).measurable, 1, abs_kT_le hN hβ⟩

/-- For even time extent, the partition function is the trace sequence of the transfer kernel. -/
theorem ZR_eq_traceSeq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (hj : 1 ≤ j)
    (hL : L μ = 2 * j) :
    ZR L N β = traceSeq (hS μ (tr L μ) N) (kT μ (tr L μ) N β) (L μ) := by
  rw [ZR_eq_cyc (μ := μ) hN β, hL]
  exact cyc_even (bdd_kT hN hβ) (kT_symm β) j hj

#print axioms ZR_eq_cyc
#print axioms kT_symm
#print axioms continuous_kT
#print axioms kT_lower
#print axioms ZR_eq_traceSeq

end MassGap.RectTransfer
