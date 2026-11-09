import Mathlib
import MassGap.RectWilsonG
import MassGap.RectTransfer

/-!
# MassGap.RectTransferG — the gauge-projected transfer kernel of the rectangular torus, over `G`

`RectTransfer` with `SUN.SU N` replaced by a `GaugeGroup G`. With `Ax = TS → G` and `Sp = SpIdx → G`,
both with product Haar measure:

* `gkG V V' = ∫ exp(−2β tp(A, V, V')) dA`;
* `kTG V V' = e^{−β sp(V)/2} gkG(V,V') e^{−β sp(V')/2}`.

Proved: `ZRG_eq_cyc` (`ZRG = cyc (Haar on Sp) kTG (L μ)` at every real `β`), `kTG_symm`,
`continuous_kTG`, `kTG_lower`, `abs_kTG_le` (`0 < kTmin ≤ kTG ≤ 1` at `β ≥ 0`), and
`ZRG_eq_traceSeq` (for `L μ = 2j`, `j ≥ 1`, `ZRG = traceSeq (Haar) kTG (L μ)`).

The proofs use of the density only `wilsonDensityG_conj`, `wilsonDensityG_inv`, `wilsonDensityG_nonneg`,
`wilsonDensityG_le_two` and its continuity, and of Haar measure its inversion invariance.

DERIVED (module-wide): `4` the dimension; `2` the range of `wilsonDensityG` and the two orientations of
each temporal plaquette.
-/

namespace MassGap.RectTransferG

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG
  MassGap.KernelPower MassGap.CyclicKernel MassGap.GaugeGroup

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- Haar measure on axis configurations of one slice. -/
noncomputable abbrev hAG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) : Measure (TT μ T → G) :=
  Measure.pi fun _ : TT μ T => probHaar G

/-- Haar measure on spatial configurations of one slice. -/
noncomputable abbrev hSG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) : Measure (SpT μ T → G) :=
  Measure.pi fun _ : SpT μ T => probHaar G

variable (G μ T) in
/-- The axis-integrated temporal factor. -/
noncomputable def gkG (β : ℝ) (V V' : SpT μ T → G) : ℝ :=
  ∫ A, Real.exp (-β * (2 * tpTG G μ T A V V')) ∂(hAG G μ T)

variable (G μ T) in
/-- The symmetric transfer kernel. -/
noncomputable def kTG (β : ℝ) (V V' : SpT μ T → G) : ℝ :=
  Real.exp (-β * spTG G μ T V / 2) * gkG G μ T β V V' * Real.exp (-β * spTG G μ T V' / 2)

/-! ## Continuity -/

theorem continuous_tpG {Y : Type*} [TopologicalSpace Y] {f : Y → TT μ T → G}
    {g h : Y → SpT μ T → G} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun q => tpTG G μ T (f q) (g q) (h q) := by
  unfold tpTG
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun y _ => ?_
  refine continuous_wilsonDensityG.comp ?_
  have e1 : Continuous fun q => f q y := (continuous_apply y).comp hf
  have e2 : Continuous fun q => h q (ν, y) := (continuous_apply (ν, y)).comp hh
  have e3 : Continuous fun q => f q (tsh μ T ν y) := (continuous_apply _).comp hf
  have e4 : Continuous fun q => g q (ν, y) := (continuous_apply (ν, y)).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_spG {Y : Type*} [TopologicalSpace Y] {g : Y → SpT μ T → G}
    (hg : Continuous g) : Continuous fun q => spTG G μ T (g q) := by
  unfold spTG
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun ν' _ =>
    continuous_finsetSum _ fun y _ => ?_
  refine continuous_wilsonDensityG.comp ?_
  have e1 : Continuous fun q => g q (ν, y) := (continuous_apply _).comp hg
  have e2 : Continuous fun q => g q (ν', tsh μ T ν y) := (continuous_apply _).comp hg
  have e3 : Continuous fun q => g q (ν, tsh μ T ν' y) := (continuous_apply _).comp hg
  have e4 : Continuous fun q => g q (ν', y) := (continuous_apply _).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_gkG (β : ℝ) :
    Continuous (Function.uncurry (gkG G μ T β)) := by
  have hf0 : Continuous fun q : ((SpT μ T → G) × (SpT μ T → G))
      × (TT μ T → G) => Real.exp (-β * (2 * tpTG G μ T q.2 q.1.1 q.1.2)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_tpG continuous_snd continuous_fst.fst continuous_fst.snd)))
  have hf : Continuous (Function.uncurry fun (p : (SpT μ T → G) × (SpT μ T → G))
      (A : TT μ T → G) => Real.exp (-β * (2 * tpTG G μ T A p.1 p.2))) := hf0
  have h := continuous_parametric_integral_of_continuous (μ := hAG G μ T) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

theorem continuous_kTG (β : ℝ) : Continuous (Function.uncurry (kTG G μ T β)) := by
  unfold kTG
  have h1 : Continuous fun p : (SpT μ T → G) × (SpT μ T → G) =>
      Real.exp (-β * spTG G μ T p.1 / 2) :=
    Real.continuous_exp.comp (((continuous_const.mul (continuous_spG continuous_fst))).div_const _)
  have h2 : Continuous fun p : (SpT μ T → G) × (SpT μ T → G) =>
      Real.exp (-β * spTG G μ T p.2 / 2) :=
    Real.continuous_exp.comp (((continuous_const.mul (continuous_spG continuous_snd))).div_const _)
  exact (h1.mul (continuous_gkG β)).mul h2

/-! ## Symmetry -/

theorem tpG_inv (A : TT μ T → G) (V V' : SpT μ T → G) :
    tpTG G μ T (fun y => (A y)⁻¹) V' V = tpTG G μ T A V V' := by
  unfold tpTG
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y _ => ?_
  set a := A y
  set b := A (tsh μ T ν y)
  set v := V (ν, y)
  set w := V' (ν, y)
  have e : a⁻¹ * v * (b⁻¹)⁻¹ * w⁻¹ = a⁻¹ * (a * w * b⁻¹ * v⁻¹)⁻¹ * a⁻¹⁻¹ := by group
  rw [e, wilsonDensityG_conj, wilsonDensityG_inv]

theorem measurePreserving_invAxG :
    MeasurePreserving (fun (A : TT μ T → G) y => (A y)⁻¹) (hAG G μ T) (hAG G μ T) :=
  measurePreserving_pi (fun _ => probHaar G) (fun _ => probHaar G)
    (fun _ => Measure.measurePreserving_inv (probHaar G))

theorem gkG_symm (β : ℝ) (V V' : SpT μ T → G) : gkG G μ T β V V' = gkG G μ T β V' V := by
  set e := MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv G)
  have hmp : MeasurePreserving e (hAG G μ T) (hAG G μ T) := measurePreserving_invAxG
  unfold gkG
  rw [← hmp.integral_comp' (fun A => Real.exp (-β * (2 * tpTG G μ T A V' V)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  have hA' : (e A) = fun y => (A y)⁻¹ := rfl
  show Real.exp (-β * (2 * tpTG G μ T A V V')) = Real.exp (-β * (2 * tpTG G μ T (e A) V' V))
  rw [hA', tpG_inv]

theorem kTG_symm (β : ℝ) (V V' : SpT μ T → G) : kTG G μ T β V V' = kTG G μ T β V' V := by
  unfold kTG; rw [gkG_symm]; ring

/-! ## Bounds -/

theorem tpG_nonneg (A : TT μ T → G) (V V' : SpT μ T → G) : 0 ≤ tpTG G μ T A V V' :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => wilsonDensityG_nonneg _

theorem spG_nonneg (V : SpT μ T → G) : 0 ≤ spTG G μ T V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    wilsonDensityG_nonneg _

theorem tpG_le (A : TT μ T → G) (V V' : SpT μ T → G) :
    tpTG G μ T A V V' ≤ RectTransfer.tpMax μ T := by
  unfold tpTG RectTransfer.tpMax
  calc _ ≤ ∑ _ν : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, (2 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => wilsonDensityG_le_two _
    _ = _ := by simp; ring

theorem spG_le (V : SpT μ T → G) : spTG G μ T V ≤ RectTransfer.spMax μ T := by
  unfold spTG RectTransfer.spMax
  calc _ ≤ ∑ _ν : {j : Fin 4 // j ≠ μ}, ∑ _ν' : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, (2 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
          wilsonDensityG_le_two _
    _ = _ := by simp; ring

theorem gkG_le_one {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) : gkG G μ T β V V' ≤ 1 := by
  unfold gkG
  calc _ ≤ ∫ _A, (1 : ℝ) ∂(hAG G μ T) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun A => (Real.exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall fun A => ?_)
        rw [Real.exp_le_one_iff]
        have := tpG_nonneg A V V'
        nlinarith
    _ = 1 := by simp

theorem gkG_ge {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) :
    Real.exp (-β * (2 * RectTransfer.tpMax μ T)) ≤ gkG G μ T β V V' := by
  unfold gkG
  have hm : Measurable fun A : TT μ T → G => Real.exp (-β * (2 * tpTG G μ T A V V')) := by
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_tpG continuous_id continuous_const continuous_const)))).measurable
  calc Real.exp (-β * (2 * RectTransfer.tpMax μ T))
        = ∫ _A, Real.exp (-β * (2 * RectTransfer.tpMax μ T)) ∂(hAG G μ T) := by simp
    _ ≤ _ := by
        refine integral_mono (integrable_const _) ?_ (fun A => ?_)
        · exact integrable_of_bdd hm (C := 1) (fun A => by
            rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
            have := tpG_nonneg A V V'; nlinarith)
        · rw [Real.exp_le_exp]
          have := tpG_le A V V'
          nlinarith

theorem kTG_le_one {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) : kTG G μ T β V V' ≤ 1 := by
  unfold kTG
  have h1 : Real.exp (-β * spTG G μ T V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := spG_nonneg V; nlinarith
  have h2 : Real.exp (-β * spTG G μ T V' / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := spG_nonneg V'; nlinarith
  have h3 := gkG_le_one hβ V V'
  have h0 : 0 ≤ gkG G μ T β V V' := (Real.exp_pos _).le.trans (gkG_ge hβ V V')
  exact mul_le_one₀ (mul_le_one₀ h1 h0 h3) (Real.exp_pos _).le h2

theorem kTG_lower {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) :
    RectTransfer.kTmin μ T β ≤ kTG G μ T β V V' := by
  unfold kTG RectTransfer.kTmin
  have h1 : Real.exp (-β * RectTransfer.spMax μ T / 2) ≤ Real.exp (-β * spTG G μ T V / 2) := by
    rw [Real.exp_le_exp]; have := spG_le V; nlinarith
  have h2 : Real.exp (-β * RectTransfer.spMax μ T / 2) ≤ Real.exp (-β * spTG G μ T V' / 2) := by
    rw [Real.exp_le_exp]; have := spG_le V'; nlinarith
  have h3 := gkG_ge hβ V V'
  have e : Real.exp (-β * RectTransfer.spMax μ T)
      = Real.exp (-β * RectTransfer.spMax μ T / 2) * Real.exp (-β * RectTransfer.spMax μ T / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  calc Real.exp (-β * RectTransfer.spMax μ T / 2) * Real.exp (-β * RectTransfer.spMax μ T / 2)
        * Real.exp (-β * (2 * RectTransfer.tpMax μ T))
      = Real.exp (-β * RectTransfer.spMax μ T / 2) * Real.exp (-β * (2 * RectTransfer.tpMax μ T))
        * Real.exp (-β * RectTransfer.spMax μ T / 2) := by ring
    _ ≤ _ := by
        have h0 : 0 ≤ gkG G μ T β V V' := (Real.exp_pos _).le.trans h3
        exact mul_le_mul (mul_le_mul h1 h3 (Real.exp_pos _).le (Real.exp_pos _).le) h2
          (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le h0)

theorem abs_kTG_le {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) : |kTG G μ T β V V'| ≤ 1 := by
  rw [abs_of_nonneg ((RectTransfer.kTmin_pos β).le.trans (kTG_lower hβ V V'))]
  exact kTG_le_one hβ V V'

/-! ## The partition function as a cyclic kernel integral -/

variable {L : Fin 4 → ℕ}

theorem ZRG_eq_cyc (β : ℝ) :
    ZRG G L β = cyc (hSG G μ (tr L μ)) (kTG G μ (tr L μ) β) (L μ) := by
  rw [ZRG_eq_integral (μ := μ) β]
  have hmp1 : MeasurePreserving
      (fun (W : Fin (L μ) → SlIdx L μ → G) t =>
        MeasurableEquiv.sumPiEquivProdPi (fun _ : SlIdx L μ => G) (W t))
      (Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar G)
      (Measure.pi fun _ : Fin (L μ) => (hAG G μ (tr L μ)).prod (hSG G μ (tr L μ))) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_sumPiEquivProdPi _
  have hmp2 := measurePreserving_arrowProdEquivProdArrow (TS L μ → G)
    (SpIdx L μ → G) (Fin (L μ)) (fun _ => hAG G μ (tr L μ)) (fun _ => hSG G μ (tr L μ))
  have hmp := hmp2.comp hmp1
  set F : (Fin (L μ) → TS L μ → G) × (Fin (L μ) → SpIdx L μ → G) → ℝ :=
    fun p => ∏ t, Real.exp (-β * (spG L μ (p.2 t)
      + 2 * tpG L μ (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))))
  have hF : Continuous F := by
    refine continuous_finsetProd _ fun t _ => Real.continuous_exp.comp
      (continuous_const.mul ((continuous_spG ((continuous_apply t).comp continuous_snd)).add
        (continuous_const.mul (continuous_tpG ((continuous_apply t).comp continuous_fst)
          ((continuous_apply t).comp continuous_snd)
          ((continuous_apply (finRotate (L μ) t)).comp continuous_snd)))))
  have h1 : ∫ W : Fin (L μ) → SlIdx L μ → G, ∏ t, Real.exp (-β * (spG L μ (spOfG (W t))
      + 2 * tpG L μ (axisOfG (W t)) (spOfG (W t)) (spOfG (W (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar G)
      = ∫ p, F p ∂((Measure.pi fun _ : Fin (L μ) => hAG G μ (tr L μ)).prod
          (Measure.pi fun _ : Fin (L μ) => hSG G μ (tr L μ))) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]
    rfl
  rw [h1]
  have hFb : ∀ p, |F p| ≤ (Real.exp (|β| * (RectTransfer.spMax μ (tr L μ)
      + 2 * RectTransfer.tpMax μ (tr L μ)))) ^ Fintype.card (Fin (L μ)) := by
    intro p
    refine abs_prod_le fun t => ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have a1 := spG_nonneg (p.2 t)
    have a2 := spG_le (p.2 t)
    have a3 := tpG_nonneg (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))
    have a4 := tpG_le (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))
    have : -β * (spG L μ (p.2 t) + 2 * tpG L μ (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t)))
        ≤ |β| * (spG L μ (p.2 t) + 2 * tpG L μ (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))) := by
      have := neg_abs_le β
      nlinarith [abs_nonneg β]
    nlinarith [abs_nonneg β]
  rw [integral_prod_symm _ (integrable_of_bdd hF.measurable hFb)]
  unfold cyc
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin (L μ) => hAG G μ (tr L μ))
    (fun t (a : TS L μ → G) => Real.exp (-β * (spG L μ (V t)
      + 2 * tpG L μ a (V t) (V (finRotate (L μ) t)))))
  show ∫ A, ∏ t, Real.exp (-β * (spG L μ (V t)
      + 2 * tpG L μ (A t) (V t) (V (finRotate (L μ) t))))
      ∂(Measure.pi fun _ : Fin (L μ) => hAG G μ (tr L μ)) = _
  rw [hprod]
  have hfac : ∀ t, ∫ a, Real.exp (-β * (spG L μ (V t) + 2 * tpG L μ a (V t) (V (finRotate (L μ) t))))
      ∂(hAG G μ (tr L μ))
      = Real.exp (-β * spG L μ (V t)) * gkG G μ (tr L μ) β (V t) (V (finRotate (L μ) t)) := by
    intro t
    unfold gkG
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]; ring_nf
  simp_rw [hfac]
  unfold kTG
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hrot : ∏ t, Real.exp (-β * spG L μ (V (finRotate (L μ) t)) / 2)
      = ∏ t, Real.exp (-β * spG L μ (V t) / 2) :=
    Fintype.prod_equiv (finRotate (L μ)) _ _ (fun t => rfl)
  rw [hrot]
  have hhalf : ∏ t, Real.exp (-β * spG L μ (V t))
      = (∏ t, Real.exp (-β * spG L μ (V t) / 2)) * ∏ t, Real.exp (-β * spG L μ (V t) / 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Real.exp_add]; ring_nf
  rw [hhalf]; ring

theorem bdd_kTG {β : ℝ} (hβ : 0 ≤ β) : Bdd (kTG G μ T β) :=
  ⟨(continuous_kTG β).measurable, 1, abs_kTG_le hβ⟩

/-- For even time extent, the partition function is the trace sequence of the transfer kernel. -/
theorem ZRG_eq_traceSeq {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (hj : 1 ≤ j) (hL : L μ = 2 * j) :
    ZRG G L β = traceSeq (hSG G μ (tr L μ)) (kTG G μ (tr L μ) β) (L μ) := by
  rw [ZRG_eq_cyc (μ := μ) β, hL]
  exact cyc_even (bdd_kTG hβ) (kTG_symm β) j hj

end MassGap.RectTransferG

#print axioms MassGap.RectTransferG.ZRG_eq_cyc
#print axioms MassGap.RectTransferG.kTG_symm
#print axioms MassGap.RectTransferG.continuous_kTG
#print axioms MassGap.RectTransferG.kTG_lower
#print axioms MassGap.RectTransferG.ZRG_eq_traceSeq
