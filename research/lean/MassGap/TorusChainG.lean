import Mathlib
import MassGap.TorusChain
import MassGap.RectTransferG

/-!
# MassGap.TorusChainG — the periodic Wilson state of `G` as a hidden-variable chain

`TorusChain` with `SUN.SU N` replaced by a `GaugeGroup G`, `PeriodicState.torusState` by
`GaugeWilson.torusStateG G` and `RectTransfer` by `RectTransferG`. The cubic torus of side `M + 1` is
sliced along direction `0`: a slice is its spatial links (`SlG G M`), a step its axis links
(`AxG G M`), and the step weight is the symmetric

    wtG V A V' = e^{−β sp(V)/2} · e^{−2β tp(A,V,V')} · e^{−β sp(V')/2},

whose hidden-variable integral is `RectTransferG.kTG` (`kern_wtG`), symmetric under `V ↔ V'`,
`A ↦ A⁻¹` (`wtG_symm`).

* `torusStateG_winF`: for `f` reading only the links of the time window `[0, w]` (`WinLocalG w f`)
  and `w ≤ M`: `torusStateG G M β f = ZcG (winFG f) / ZcG 1`.
* `winFG_shift`, `winFG_refl`: on window functions the unit shift is `sshift` and the reflection at
  `x₀ = 0` followed by `w` shifts is `revX w`, `revY invAG w`.
* `winLocalG_shift`, `winLocalG_refl`, `WinLocalG.mul`, `winLocalG_of_mem`: the window predicate is
  carried by shifts, the reflection, products, and holds for every half-space observable.

The geometry (`TorusChain.Lc`, `Tc`, `InWin`, `perpI`, `shD_ishiftLink`) does not mention the group
and is reused.

DERIVED (module-wide): `4` the dimension; `0` the slicing direction and the reflection plane; `1` the
successor of the extent `M + 1`; `2` the two orientations of each temporal plaquette and the halves of
the spatial weight.
-/

namespace MassGap.TorusChainG

open MeasureTheory MassGap MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.HiddenChain MassGap.CompactGauge MassGap.LatticeGauge MassGap.WilsonLattice
  MassGap.KernelPower MassGap.TorusChain MassGap.GaugeGroup

set_option linter.unusedSectionVars false

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## The sliced cubic torus -/

/-- Spatial links of one slice. -/
abbrev SlG (M : ℕ) : Type := SpT 0 (Tc M) → G
/-- Axis links of one step. -/
abbrev AxG (M : ℕ) : Type := TT 0 (Tc M) → G

/-- The symmetric step weight. -/
noncomputable def wtG (M : ℕ) (β : ℝ) (V : SlG G M) (A : AxG G M) (V' : SlG G M) : ℝ :=
  Real.exp (-β * spTG G 0 (Tc M) V / 2) * Real.exp (-β * (2 * tpTG G 0 (Tc M) A V V'))
    * Real.exp (-β * spTG G 0 (Tc M) V' / 2)

variable {G} {M : ℕ}

theorem continuous_wtG' (β : ℝ) {Z : Type*} [TopologicalSpace Z] {f h : Z → SlG G M}
    {g : Z → AxG G M} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun q => wtG G M β (f q) (g q) (h q)) := by
  unfold wtG
  have h1 : Continuous (fun q => spTG G 0 (Tc M) (f q)) := continuous_spG hf
  have h2 : Continuous (fun q => spTG G 0 (Tc M) (h q)) := continuous_spG hh
  have h3 : Continuous (fun q => tpTG G 0 (Tc M) (g q) (f q) (h q)) := continuous_tpG hg hf hh
  exact ((Real.continuous_exp.comp ((continuous_const.mul h1).div_const _)).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul h3)))).mul
    (Real.continuous_exp.comp ((continuous_const.mul h2).div_const _))

theorem continuous_wtG (β : ℝ) :
    Continuous (fun p : SlG G M × AxG G M × SlG G M => wtG G M β p.1 p.2.1 p.2.2) :=
  continuous_wtG' β continuous_fst (continuous_fst.comp continuous_snd)
    (continuous_snd.comp continuous_snd)

theorem wmeas_wtG (β : ℝ) : WMeas (wtG G M β) := (continuous_wtG β).measurable

theorem wtG_nonneg (β : ℝ) (V : SlG G M) (A : AxG G M) (V' : SlG G M) : 0 ≤ wtG G M β V A V' := by
  unfold wtG; positivity

theorem wtG_le_one {β : ℝ} (hβ : 0 ≤ β) (V : SlG G M) (A : AxG G M) (V' : SlG G M) :
    wtG G M β V A V' ≤ 1 := by
  unfold wtG
  have a1 := spG_nonneg V
  have a2 := spG_nonneg V'
  have a3 := tpG_nonneg A V V'
  have e1 : Real.exp (-β * spTG G 0 (Tc M) V / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : Real.exp (-β * (2 * tpTG G 0 (Tc M) A V V')) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have e3 : Real.exp (-β * spTG G 0 (Tc M) V' / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have p1 := Real.exp_pos (-β * spTG G 0 (Tc M) V / 2)
  have p2 := Real.exp_pos (-β * (2 * tpTG G 0 (Tc M) A V V'))
  have p3 := Real.exp_pos (-β * spTG G 0 (Tc M) V' / 2)
  have h12 : Real.exp (-β * spTG G 0 (Tc M) V / 2) * Real.exp (-β * (2 * tpTG G 0 (Tc M) A V V'))
      ≤ 1 := by nlinarith
  nlinarith [mul_pos p1 p2]

theorem abs_wtG_le {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (V : SlG G M) (A : AxG G M) (V' : SlG G M), |wtG G M β V A V'| ≤ 1 := fun V A V' => by
  rw [abs_of_nonneg (wtG_nonneg β V A V')]; exact wtG_le_one hβ V A V'

theorem kern_wtG (β : ℝ) : kern (hAG G 0 (Tc M)) (wtG G M β) = kTG G 0 (Tc M) β := by
  funext x y
  simp only [kern, wtG, kTG, gkG]
  rw [integral_mul_const, integral_const_mul]

/-- Pointwise inversion of the axis links. -/
noncomputable def invAG : AxG G M ≃ᵐ AxG G M :=
  MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.inv G)

theorem invAG_apply (A : AxG G M) : invAG A = fun y => (A y)⁻¹ := rfl

theorem invAG_invAG (A : AxG G M) : invAG (invAG A) = A := by
  funext y; simp [invAG_apply]

theorem mp_invAG : MeasurePreserving (invAG (G := G) (M := M)) (hAG G 0 (Tc M)) (hAG G 0 (Tc M)) :=
  measurePreserving_invAxG

theorem wtG_symm (β : ℝ) (V : SlG G M) (A : AxG G M) (V' : SlG G M) :
    wtG G M β V A V' = wtG G M β V' (invAG A) V := by
  unfold wtG; rw [invAG_apply, tpG_inv]; ring

/-! ## The torus as a chain -/

variable (G M) in
/-- The torus integral of an insertion, closed by one transfer kernel. -/
noncomputable def ZcG (β : ℝ) (F : (ℕ → SlG G M) → (ℕ → AxG G M) → ℝ) : ℝ :=
  ∫ x, chain (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M
    (fun V A => F V A * kTG G 0 (Tc M) β (V M) x) x ∂(hSG G 0 (Tc M))

/-- A cyclic sequence of slice configurations from its axis and spatial parts. -/
def joinWG (A : Fin (M + 1) → AxG G M) (V : Fin (M + 1) → SlG G M) :
    Fin (Lc M 0) → SlIdx (Lc M) 0 → G := fun t => Sum.elim (A t) (V t)

theorem measurable_joinWG :
    Measurable (fun p : (Fin (M + 1) → AxG G M) × (Fin (M + 1) → SlG G M) => joinWG p.1 p.2) := by
  refine measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun s => ?_
  cases s with
  | inl y => exact (measurable_pi_apply y).comp ((measurable_pi_apply t).comp measurable_fst)
  | inr q => exact (measurable_pi_apply q).comp ((measurable_pi_apply t).comp measurable_snd)

theorem prod_exp_wtG (β : ℝ) (A : Fin (M + 1) → AxG G M) (V : Fin (M + 1) → SlG G M) :
    ∏ t, Real.exp (-β * (spTG G 0 (Tc M) (V t)
        + 2 * tpTG G 0 (Tc M) (A t) (V t) (V (finRotate (M + 1) t))))
      = ∏ t, wtG G M β (V t) (A t) (V (finRotate (M + 1) t)) := by
  have h1 : ∀ t, Real.exp (-β * (spTG G 0 (Tc M) (V t)
        + 2 * tpTG G 0 (Tc M) (A t) (V t) (V (finRotate (M + 1) t))))
      = Real.exp (-β * spTG G 0 (Tc M) (V t) / 2)
        * Real.exp (-β * (2 * tpTG G 0 (Tc M) (A t) (V t) (V (finRotate (M + 1) t))))
        * Real.exp (-β * spTG G 0 (Tc M) (V t) / 2) := fun t => by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hrot : ∏ t, Real.exp (-β * spTG G 0 (Tc M) (V (finRotate (M + 1) t)) / 2)
      = ∏ t, Real.exp (-β * spTG G 0 (Tc M) (V t) / 2) :=
    Fintype.prod_equiv (finRotate (M + 1)) _ _ (fun t => rfl)
  simp only [h1, wtG, Finset.prod_mul_distrib, hrot]

theorem continuous_prod_wtG (β : ℝ) :
    Continuous (fun p : (Fin (M + 1) → AxG G M) × (Fin (M + 1) → SlG G M) =>
      ∏ t, wtG G M β (p.2 t) (p.1 t) (p.2 (finRotate (M + 1) t))) := by
  refine continuous_finsetProd _ fun t _ => ?_
  exact continuous_wtG' β ((continuous_apply t).comp continuous_snd)
    ((continuous_apply t).comp continuous_fst)
    ((continuous_apply (finRotate (M + 1) t)).comp continuous_snd)

theorem abs_prod_wtG_le {β : ℝ} (hβ : 0 ≤ β) (A : Fin (M + 1) → AxG G M)
    (V : Fin (M + 1) → SlG G M) :
    |∏ t, wtG G M β (V t) (A t) (V (finRotate (M + 1) t))| ≤ 1 := by
  have := CyclicKernel.abs_prod_le (u := fun t => wtG G M β (V t) (A t) (V (finRotate (M + 1) t)))
    (C := 1) (fun t => abs_wtG_le hβ _ _ _)
  simpa using this

/-- Peel the last axis slice, which no insertion reads. -/
theorem peelG {β : ℝ} (hβ : 0 ≤ β) (V : Fin (M + 1) → SlG G M)
    {g : (Fin M → AxG G M) → ℝ} (hg : Measurable g) {Bg : ℝ} (hgb : ∀ A, |g A| ≤ Bg) :
    ∫ A : Fin (M + 1) → AxG G M, g (fun t : Fin M => A t.castSucc)
        * ∏ t, wtG G M β (V t) (A t) (V (finRotate (M + 1) t))
        ∂(Measure.pi fun _ => hAG G 0 (Tc M))
      = ∫ A' : Fin M → AxG G M, g A' * pathW (wtG G M β) V A'
          * kTG G 0 (Tc M) β (V (Fin.last M)) (V 0) ∂(Measure.pi fun _ => hAG G 0 (Tc M)) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => hAG G 0 (Tc M)) (Fin.last M)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => AxG G M) (Fin.last M)
  set f : (Fin (M + 1) → AxG G M) → ℝ := fun A => g (fun t : Fin M => A t.castSucc)
    * ∏ t, wtG G M β (V t) (A t) (V (finRotate (M + 1) t))
  have hfm : Measurable f := by
    simp only [f]
    have hc : Measurable (fun A : Fin (M + 1) → AxG G M => fun t : Fin M => A t.castSucc) :=
      measurable_pi_lambda _ fun t => measurable_pi_apply t.castSucc
    have hp : Measurable (fun A : Fin (M + 1) → AxG G M =>
        ∏ t, wtG G M β (V t) (A t) (V (finRotate (M + 1) t))) :=
      Finset.measurable_prod _ fun t _ =>
        (continuous_wtG' β continuous_const (continuous_apply t) continuous_const).measurable
    exact (hg.comp hc).mul hp
  have hfb : ∀ A, |f A| ≤ Bg := fun A => by
    simp only [f]
    have := abs_mul_le_of (hgb (fun t : Fin M => A t.castSucc)) (abs_prod_wtG_le hβ A V)
    rwa [mul_one] at this
  have he : ∀ (a : AxG G M) (A' : Fin M → AxG G M), e.symm (a, A') = Fin.snoc A' a :=
    fun a A' => Fin.insertNth_last' a A'
  have h1 : ∫ A, f A ∂(Measure.pi fun _ => hAG G 0 (Tc M))
      = ∫ q, f (e.symm q) ∂((hAG G 0 (Tc M)).prod (Measure.pi fun _ : Fin M => hAG G 0 (Tc M))) := by
    rw [← hmp.integral_comp' (g := fun q => f (e.symm q))]
    simp
  have hint : Integrable (fun q => f (e.symm q))
      ((hAG G 0 (Tc M)).prod (Measure.pi fun _ : Fin M => hAG G 0 (Tc M))) :=
    integrable_of_bdd (hfm.comp e.symm.measurable) (fun q => hfb _)
  have hpt : ∀ (A' : Fin M → AxG G M) (a : AxG G M),
      f (Fin.snoc A' a) = (g A' * pathW (wtG G M β) V A') * wtG G M β (V (Fin.last M)) a (V 0) := by
    intro A' a
    simp only [f]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, finRotate_last]
    have hrot : ∀ t : Fin M, finRotate (M + 1) t.castSucc = t.succ := fun t => by
      rw [finRotate_apply, Fin.coeSucc_eq_succ]
    simp only [hrot]
    unfold pathW; ring
  change ∫ A, f A ∂(Measure.pi fun _ => hAG G 0 (Tc M)) = _
  rw [h1, integral_prod_symm _ hint]
  congr 1; funext A'
  simp_rw [he, hpt]
  rw [integral_const_mul]
  congr 1
  exact congrFun (congrFun (kern_wtG (G := G) (M := M) β) _) _

set_option maxHeartbeats 800000 in
/-- **The Wilson correlation numerator of the cubic torus of `G` as a closed chain.** -/
theorem corrNum_eqG {β : ℝ} (hβ : 0 ≤ β) {O : (RLink (Lc M) → G) → ℝ}
    (hO : Measurable O) {BO : ℝ} (hOb : ∀ U, |O U| ≤ BO)
    {F : (ℕ → SlG G M) → (ℕ → AxG G M) → ℝ}
    (hF : Measurable (fun q : (ℕ → SlG G M) × (ℕ → AxG G M) => F q.1 q.2)) {BF : ℝ}
    (hFb : ∀ V A, |F V A| ≤ BF)
    (hOF : ∀ A V, O (ΦG (Lc M) 0 (joinWG A V))
      = F (extX V) (extY (fun t : Fin M => A t.castSucc))) :
    (sysRG G (Lc M)).corrNum (probHaar G) β O = ZcG G M β F := by
  have hmp := measurePreserving_ΦG G (L := Lc M) (μ := 0)
  unfold System.corrNum System.vol
  change ∫ U : RLink (Lc M) → G, O U * (sysRG G (Lc M)).boltz β U
      ∂(Measure.pi fun _ : RLink (Lc M) => probHaar G) = _
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (hO.mul (continuous_boltzRG G (Lc M) β).measurable).aestronglyMeasurable]
  set φ := (⇑(MeasurableEquiv.arrowProdEquivProdArrow (TS (Lc M) 0 → G)
      (SpIdx (Lc M) 0 → G) (Fin (M + 1)))) ∘
    fun (W : Fin (M + 1) → SlIdx (Lc M) 0 → G) t =>
      MeasurableEquiv.sumPiEquivProdPi (fun _ : SlIdx (Lc M) 0 => G) (W t) with hφdef
  have hφ : MeasurePreserving φ
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : SlIdx (Lc M) 0 => probHaar G)
      ((Measure.pi fun _ : Fin (M + 1) => hAG G 0 (Tc M)).prod
        (Measure.pi fun _ : Fin (M + 1) => hSG G 0 (Tc M))) := by
    have hmp1 : MeasurePreserving
        (fun (W : Fin (M + 1) → SlIdx (Lc M) 0 → G) t =>
          MeasurableEquiv.sumPiEquivProdPi (fun _ : SlIdx (Lc M) 0 => G) (W t))
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : SlIdx (Lc M) 0 => probHaar G)
        (Measure.pi fun _ : Fin (M + 1) => (hAG G 0 (Tc M)).prod (hSG G 0 (Tc M))) :=
      measurePreserving_pi _ _ fun _ => measurePreserving_sumPiEquivProdPi _
    have hmp2 := measurePreserving_arrowProdEquivProdArrow (TS (Lc M) 0 → G)
      (SpIdx (Lc M) 0 → G) (Fin (M + 1)) (fun _ => hAG G 0 (Tc M)) (fun _ => hSG G 0 (Tc M))
    exact hmp2.comp hmp1
  set H : (Fin (M + 1) → AxG G M) × (Fin (M + 1) → SlG G M) → ℝ :=
    fun p => O (ΦG (Lc M) 0 (joinWG p.1 p.2))
      * ∏ t, wtG G M β (p.2 t) (p.1 t) (p.2 (finRotate (M + 1) t))
  have hHm : Measurable H := by
    simp only [H]
    exact (meas_comp' hO (meas_comp' hmp.measurable measurable_joinWG)).mul
      (continuous_prod_wtG β).measurable
  have hHb : ∀ p, |H p| ≤ BO := fun p => by
    simp only [H]
    have := abs_mul_le_of (hOb (ΦG (Lc M) 0 (joinWG p.1 p.2))) (abs_prod_wtG_le hβ p.1 p.2)
    rwa [mul_one] at this
  have hjoin : ∀ W, joinWG (φ W).1 (φ W).2 = W := by
    intro W; funext t s; cases s <;> rfl
  have hHW : ∀ W, O (ΦG (Lc M) 0 W) * (sysRG G (Lc M)).boltz β (ΦG (Lc M) 0 W) = H (φ W) := by
    intro W
    simp only [H]
    rw [hjoin W]
    congr 1
    unfold System.boltz
    rw [action_ΦG W, Finset.mul_sum, Real.exp_sum]
    exact prod_exp_wtG β _ _
  have step1 : ∫ W, O (ΦG (Lc M) 0 W) * (sysRG G (Lc M)).boltz β (ΦG (Lc M) 0 W)
      ∂(Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : SlIdx (Lc M) 0 => probHaar G)
      = ∫ p, H p ∂((Measure.pi fun _ : Fin (M + 1) => hAG G 0 (Tc M)).prod
          (Measure.pi fun _ : Fin (M + 1) => hSG G 0 (Tc M))) := by
    simp_rw [hHW]
    rw [← hφ.map_eq, integral_map hφ.measurable.aemeasurable hHm.aestronglyMeasurable]
  rw [step1, integral_prod_symm H (integrable_of_bdd hHm hHb)]
  have hFV : ∀ V : Fin (M + 1) → SlG G M,
      Measurable (fun A' : Fin M → AxG G M => F (extX V) (extY A')) :=
    fun V => hF.comp (measurable_const.prodMk measurable_extY)
  have step2 : ∀ V : Fin (M + 1) → SlG G M, ∫ A, H (A, V) ∂(Measure.pi fun _ => hAG G 0 (Tc M))
      = ∫ A' : Fin M → AxG G M, F (extX V) (extY A') * pathW (wtG G M β) V A'
          * kTG G 0 (Tc M) β (V (Fin.last M)) (V 0) ∂(Measure.pi fun _ => hAG G 0 (Tc M)) := by
    intro V
    simp only [H, hOF]
    exact peelG hβ V (hFV V) (fun A' => hFb _ _)
  simp_rw [step2]
  have hG : Measurable (fun q : (ℕ → SlG G M) × (ℕ → AxG G M) =>
      F q.1 q.2 * kTG G 0 (Tc M) β (q.1 M) (q.1 0)) := by
    refine hF.mul ?_
    have hk : Measurable (Function.uncurry (kTG G 0 (Tc M) β)) :=
      (continuous_kTG (G := G) (μ := 0) (T := Tc M) β).measurable
    exact meas_comp2 hk ((measurable_pi_apply M).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_fst)
  have hGb : ∀ V A, |F V A * kTG G 0 (Tc M) β (V M) (V 0)| ≤ BF * 1 := fun V A =>
    abs_mul_le_of (hFb V A) (abs_kTG_le hβ _ _)
  have hbr := bridge (μ := hSG G 0 (Tc M)) (ν := hAG G 0 (Tc M)) (wmeas_wtG β)
    (fun V A V' => abs_wtG_le hβ V A V') M
    (G := fun V A => F V A * kTG G 0 (Tc M) β (V M) (V 0)) hG hGb
  unfold ZcG
  have hcl : ∀ x, chain (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M
      (fun V A => F V A * kTG G 0 (Tc M) β (V M) x) x
      = chain (hSG G 0 (Tc M)) (hAG G 0 (Tc M)) (wtG G M β) M
        (fun V A => F V A * kTG G 0 (Tc M) β (V M) (V 0)) x :=
    fun x => chain_congr M (fun V A hV => by rw [hV])
  simp_rw [hcl]
  rw [← hbr]
  congr 1; funext V; congr 1; funext A'
  rw [extX_last, extX_zero]; ring

/-- The hypercubic and the rectangular Wilson systems of `G` on the cubic torus have the same
expectation. -/
theorem expect_cubicG (β : ℝ) (O : (RLink (Lc M) → G) → ℝ) :
    GaugeWilson.EWG G (d := 4) (n := M + 1) β O
      = (sysRG G (Lc M)).expect (probHaar G) β O := by
  have key : ∀ b : RPlaq (Lc M) → List (RLink (Lc M) × Bool),
      b = WilsonHypercubic.bd (d := 4) (n := M + 1) →
      (wilsonSystem (G := G) b (wilsonDensityG G)).expect (probHaar G) β O
        = (wilsonSystem (G := G) (WilsonHypercubic.bd (d := 4) (n := M + 1))
            (wilsonDensityG G)).expect (probHaar G) β O := by
    rintro b rfl; rfl
  exact (key (rbd (Lc M)) (TorusIdentify.rbd_cubic M)).symm

/-! ## Observables read on a time window -/

variable (G M) in
/-- The `ℤ⁴` configuration with slices `V` and steps `A` at non-negative times, `1` elsewhere. -/
noncomputable def cfgG (V : ℕ → SlG G M) (A : ℕ → AxG G M) : GibbsSpec.IConf G :=
  fun l => if 0 ≤ l.2 0 then
      (if h : l.1 = 0 then A (l.2 0).toNat (perpI M l.2)
        else V (l.2 0).toNat (⟨l.1, h⟩, perpI M l.2))
    else 1

theorem cfgG_axis {V : ℕ → SlG G M} {A : ℕ → AxG G M} {l : GibbsSpec.ILink} (h : l.1 = 0)
    (h0 : 0 ≤ l.2 0) : cfgG G M V A l = A (l.2 0).toNat (perpI M l.2) := by
  simp only [cfgG, if_pos h0, dif_pos h]

theorem cfgG_sp {V : ℕ → SlG G M} {A : ℕ → AxG G M} {l : GibbsSpec.ILink} (h : l.1 ≠ 0)
    (h0 : 0 ≤ l.2 0) : cfgG G M V A l = V (l.2 0).toNat (⟨l.1, h⟩, perpI M l.2) := by
  simp only [cfgG, if_pos h0, dif_neg h]

theorem measurable_cfgG :
    Measurable (fun q : (ℕ → SlG G M) × (ℕ → AxG G M) => cfgG G M q.1 q.2) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h0 : 0 ≤ l.2 0
  · by_cases h : l.1 = 0
    · simp only [cfgG, if_pos h0, dif_pos h]
      exact (measurable_pi_apply (perpI M l.2)).comp
        ((measurable_pi_apply (l.2 0).toNat).comp measurable_snd)
    · simp only [cfgG, if_pos h0, dif_neg h]
      exact (measurable_pi_apply ((⟨l.1, h⟩ : {j : Fin 4 // j ≠ 0}), perpI M l.2)).comp
        ((measurable_pi_apply (l.2 0).toNat).comp measurable_fst)
  · simp only [cfgG, if_neg h0]; exact measurable_const

/-- An observable read on the chain variables. -/
noncomputable def winFG (f : C(GibbsSpec.IConf G, ℝ)) : (ℕ → SlG G M) → (ℕ → AxG G M) → ℝ :=
  fun V A => f (cfgG G M V A)

theorem measurable_winFG (f : C(GibbsSpec.IConf G, ℝ)) :
    Measurable (fun q : (ℕ → SlG G M) × (ℕ → AxG G M) => winFG f q.1 q.2) :=
  f.continuous.measurable.comp measurable_cfgG

theorem winFG_bdd (f : C(GibbsSpec.IConf G, ℝ)) :
    ∃ B, ∀ V A, |winFG (M := M) f V A| ≤ B := by
  obtain ⟨C, hC⟩ := InfiniteLattice.bounded_of_continuous f.continuous
  exact ⟨C, fun V A => hC _⟩

/-- `f` reads only links of the time window `[0, w]`. -/
def WinLocalG (w : ℕ) (f : GibbsSpec.IConf G → ℝ) : Prop :=
  ∀ U U' : GibbsSpec.IConf G, (∀ l, InWin w l → U l = U' l) → f U = f U'

theorem WinLocalG.mono {w w' : ℕ} {f : GibbsSpec.IConf G → ℝ} (h : WinLocalG w f)
    (hw : w ≤ w') : WinLocalG w' f :=
  fun U U' hUU => h U U' fun l ⟨h0, h1, h2⟩ =>
    hUU l ⟨h0, by omega, fun hl => by have := h2 hl; omega⟩

theorem WinLocalG.mul {w : ℕ} {f g : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f)
    (hg : WinLocalG w g) : WinLocalG w (f * g) := fun U U' h => by
  simp only [ContinuousMap.mul_apply]; rw [hf U U' h, hg U U' h]

theorem localUpTo_winFG {w : ℕ} {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f) :
    LocalUpTo w (winFG (M := M) f) := by
  intro V V' A A' hV hA
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, hw, hax⟩
  dsimp only at h0 hw hax
  by_cases h : d0 = 0
  · rw [cfgG_axis h h0, cfgG_axis h h0]
    dsimp only
    rw [hA _ (by have := hax h; omega)]
  · rw [cfgG_sp h h0, cfgG_sp h h0]
    dsimp only
    rw [hV _ (by omega)]

/-- Every half-space observable reads a finite time window. -/
theorem winLocalG_of_mem {x : C(GibbsSpec.IConf G, ℝ)}
    (hx : x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) 0 0) : ∃ R : ℕ, WinLocalG R x := by
  obtain ⟨S, hS, hloc⟩ := hx
  set R0 : ℕ := S.sup (fun l : InfiniteLattice.ILink => (l.2 0).toNat) with hR0
  refine ⟨R0 + 1, fun U U' hUU => hloc U U' fun l hl => hUU l ?_⟩
  have h0 : (0 : ℤ) ≤ l.2 0 := hS hl
  have hle : (l.2 0).toNat ≤ R0 :=
    Finset.le_sup (f := fun l : InfiniteLattice.ILink => (l.2 0).toNat) hl
  refine ⟨h0, ?_, fun _ => ?_⟩
  · show l.2 0 ≤ ((R0 + 1 : ℕ) : ℤ)
    push_cast; omega
  · show l.2 0 < ((R0 + 1 : ℕ) : ℤ)
    push_cast; omega

/-! ## Shift and reflection on window functions -/

theorem shiftObsG_iter (d : ℕ) (f : C(GibbsSpec.IConf G, ℝ)) (U : GibbsSpec.IConf G) :
    ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] f) U
      = f (fun l => U (l.1, Function.update l.2 0 (l.2 0 + d))) := by
  induction d generalizing f with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih]
    show f (InfiniteShift.ishiftConf 0 (fun l => U (l.1, Function.update l.2 0 (l.2 0 + d)))) = _
    congr 1; funext l
    exact congrArg U (shD_ishiftLink d l)

theorem ireflG_axis (U : GibbsSpec.IConf G) (s : Fin 4 → ℤ) :
    LatticeReflection.ireflConf 0 0 U (0, s) = (U (0, Function.update s 0 (-1 - s 0)))⁻¹ := by
  simp [LatticeReflection.ireflConf, LatticeReflection.ireflLink, LatticeReflection.ireflSite]

theorem ireflG_sp (U : GibbsSpec.IConf G) {d0 : Fin 4} (h : d0 ≠ 0) (s : Fin 4 → ℤ) :
    LatticeReflection.ireflConf 0 0 U (d0, s) = U (d0, Function.update s 0 (-s 0)) := by
  simp [LatticeReflection.ireflConf, LatticeReflection.ireflLink, LatticeReflection.ireflSite, h]

theorem winLocalG_shift {w : ℕ} {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f)
    (d : ℕ) : WinLocalG (w + d) ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] f) := by
  intro U U' hUU
  rw [shiftObsG_iter, shiftObsG_iter]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2 ⊢
  apply hUU
  have hx : (Function.update s 0 (s 0 + (d : ℤ))) 0 = s 0 + d := by simp
  refine ⟨?_, ?_, fun hd => ?_⟩
  · show 0 ≤ (Function.update s 0 (s 0 + (d : ℤ))) 0
    rw [hx]; omega
  · show (Function.update s 0 (s 0 + (d : ℤ))) 0 ≤ ((w + d : ℕ) : ℤ)
    rw [hx]; push_cast; omega
  · show (Function.update s 0 (s 0 + (d : ℤ))) 0 < ((w + d : ℕ) : ℤ)
    have := h2 hd
    rw [hx]; push_cast; omega

theorem winLocalG_refl {w : ℕ} {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f) :
    WinLocalG w ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[w]
      (LatticeReflection.ireflObs 0 0 f)) := by
  intro U U' hUU
  rw [shiftObsG_iter, shiftObsG_iter, LatticeReflection.ireflObs_apply,
    LatticeReflection.ireflObs_apply]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  by_cases h : d0 = 0
  · subst h
    have ht := h2 rfl
    rw [ireflG_axis, ireflG_axis]
    dsimp only
    congr 1
    apply hUU
    have hx : (Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0 = -1 - s 0 + w := by simp
    refine ⟨?_, ?_, fun _ => ?_⟩
    · show 0 ≤ (Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0
      rw [hx]; omega
    · show (Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0 ≤ (w : ℤ)
      rw [hx]; omega
    · show (Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0 < (w : ℤ)
      rw [hx]; omega
  · rw [ireflG_sp _ h, ireflG_sp _ h]
    dsimp only
    apply hUU
    have hx : (Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0 = -s 0 + w := by simp
    refine ⟨?_, ?_, fun hd => absurd hd h⟩
    · show 0 ≤ (Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0
      rw [hx]; omega
    · show (Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0 ≤ (w : ℤ)
      rw [hx]; omega

theorem winFG_shift {w : ℕ} {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f) (d : ℕ)
    (V : ℕ → SlG G M) (A : ℕ → AxG G M) :
    winFG ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[d] f) V A
      = winFG f (sshift V d) (sshift A d) := by
  unfold winFG
  rw [shiftObsG_iter]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, -, -⟩
  dsimp only at h0 ⊢
  have h1 : 0 ≤ (Function.update s 0 (s 0 + (d : ℤ))) 0 := by simp; omega
  have hx : ((Function.update s 0 (s 0 + (d : ℤ))) 0).toNat = (s 0).toNat + d := by simp; omega
  by_cases h : d0 = 0
  · rw [cfgG_axis (l := (d0, Function.update s 0 (s 0 + (d : ℤ)))) h h1,
      cfgG_axis (l := (d0, s)) h h0]
    dsimp only
    rw [perpI_update, hx]; rfl
  · rw [cfgG_sp (l := (d0, Function.update s 0 (s 0 + (d : ℤ)))) h h1,
      cfgG_sp (l := (d0, s)) h h0]
    dsimp only
    rw [perpI_update, hx]; rfl

theorem winFG_refl {w : ℕ} {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f)
    (V : ℕ → SlG G M) (A : ℕ → AxG G M) :
    winFG ((⇑(ReflectionShift.ishiftObsL (G := G) 0))^[w] (LatticeReflection.ireflObs 0 0 f))
        V A
      = winFG f (revX w V) (revY (fun a : AxG G M => invAG a) w A) := by
  unfold winFG
  rw [shiftObsG_iter, LatticeReflection.ireflObs_apply]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  by_cases h : d0 = 0
  · subst h
    have ht := h2 rfl
    rw [ireflG_axis]
    dsimp only
    have hy : 0 ≤ (Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0 := by simp; omega
    rw [cfgG_axis (l := (0, Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ)))) rfl hy, cfgG_axis (l := (0, s)) rfl h0]
    dsimp only
    rw [perpI_update, perpI_update]
    have hx : ((Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0).toNat = w - 1 - (s 0).toNat := by
      simp; omega
    rw [hx]
    simp only [revY, invAG_apply]
  · rw [ireflG_sp _ h]
    dsimp only
    have hy : 0 ≤ (Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0 := by simp; omega
    rw [cfgG_sp (l := (d0, Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ)))) h hy, cfgG_sp (l := (d0, s)) h h0]
    dsimp only
    rw [perpI_update, perpI_update]
    have hx : ((Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0).toNat = w - (s 0).toNat := by
      simp; omega
    rw [hx]
    rfl

/-! ## The torus state on window observables -/

theorem pullback_ΦG (W : Fin (M + 1) → SlIdx (Lc M) 0 → G) (l : InfiniteLattice.ILink) :
    InfiniteLattice.pullback M (ΦG (Lc M) 0 W) l
      = W (InfiniteLattice.finMod M (l.2 0)) (sIdx (L := Lc M) (μ := 0) l.1 (perpI M l.2)) := rfl

theorem torus_windowG {w : ℕ} {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f)
    (hwM : w ≤ M) (A : Fin (M + 1) → AxG G M) (V : Fin (M + 1) → SlG G M) :
    f (InfiniteLattice.pullback M (ΦG (Lc M) 0 (joinWG A V)))
      = winFG f (extX V) (extY (fun t : Fin M => A t.castSucc)) := by
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  rw [pullback_ΦG]
  dsimp only
  have hfm : InfiniteLattice.finMod M (s 0) = ⟨(s 0).toNat, by omega⟩ := by
    apply Fin.ext
    show ((s 0) % ((M : ℤ) + 1)).toNat = (s 0).toNat
    rw [Int.emod_eq_of_lt h0 (by omega)]
  rw [hfm]
  by_cases h : d0 = 0
  · subst h
    have ht := h2 rfl
    rw [cfgG_axis (l := (0, s)) rfl h0]
    have hs : sIdx (L := Lc M) (μ := 0) 0 (perpI M s) = Sum.inl (perpI M s) := by simp [sIdx]
    rw [hs]
    show A ⟨(s 0).toNat, _⟩ (perpI M s)
      = extY (fun t : Fin M => A t.castSucc) (s 0).toNat (perpI M s)
    simp only [extY, dif_pos (show (s 0).toNat < M by omega)]
    rfl
  · rw [cfgG_sp (l := (d0, s)) h h0]
    have hs : sIdx (L := Lc M) (μ := 0) d0 (perpI M s) = Sum.inr (⟨d0, h⟩, perpI M s) := by
      simp [sIdx, h]
    rw [hs]
    show V ⟨(s 0).toNat, _⟩ (⟨d0, h⟩, perpI M s) = extX V (s 0).toNat (⟨d0, h⟩, perpI M s)
    simp only [extX, dif_pos (show (s 0).toNat < M + 1 by omega)]

/-- **The periodic Wilson state of `G` on a window observable is a ratio of closed chains.** -/
theorem torusStateG_winF {β : ℝ} (hβ : 0 ≤ β) {w : ℕ}
    {f : C(GibbsSpec.IConf G, ℝ)} (hf : WinLocalG w f) (hwM : w ≤ M) :
    GaugeWilson.torusStateG G M β f = ZcG G M β (winFG f) / ZcG G M β (fun _ _ => 1) := by
  have e : GaugeWilson.torusStateG G M β f
      = (sysRG G (Lc M)).expect (probHaar G) β (GaugeWilson.torusObsG G M f) := by
    show GaugeWilson.EWG G (d := 4) (n := M + 1) β (GaugeWilson.torusObsG G M f) = _
    exact expect_cubicG β _
  obtain ⟨Bf, hBf⟩ := InfiniteLattice.bounded_of_continuous f.continuous
  obtain ⟨BF, hBF⟩ := winFG_bdd (M := M) f
  have hnum := corrNum_eqG hβ (O := GaugeWilson.torusObsG G M f)
    (GaugeWilson.measurable_torusObsG G M f) (fun U => hBf _) (measurable_winFG f) hBF
    (fun A V => torus_windowG hf hwM A V)
  have hden := corrNum_eqG (G := G) (M := M) hβ (O := fun _ => 1) measurable_const (BO := 1)
    (fun _ => by simp) (F := fun _ _ => 1) measurable_const (BF := 1) (fun _ _ => by simp)
    (fun _ _ => rfl)
  rw [e, System.expect, hnum, ← hden]
  congr 1
  simp [System.partition, System.corrNum]

end MassGap.TorusChainG

#print axioms MassGap.TorusChainG.corrNum_eqG
#print axioms MassGap.TorusChainG.torusStateG_winF
#print axioms MassGap.TorusChainG.winFG_refl
#print axioms MassGap.TorusChainG.winFG_shift
