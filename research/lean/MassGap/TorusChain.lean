import Mathlib
import MassGap.HiddenChain
import MassGap.ChainClosing
import MassGap.RectTransfer
import MassGap.TorusIdentify
import MassGap.PeriodicState
import MassGap.HalfSpaceAlgebra

/-!
# MassGap.TorusChain — the periodic Wilson state as a hidden-variable chain

Piece 2 of the finite-volume dyadic step. The cubic torus of side `M + 1` is sliced along direction
`0`: a slice is its spatial links (`Sl M N`), a step its axis links (`Ax M N`), and the step weight is
the symmetric

    wt V A V' = e^{−β sp(V)/2} · e^{−2β tp(A,V,V')} · e^{−β sp(V')/2},

whose hidden-variable integral is the transfer kernel `RectTransfer.kT` (`kern_wt`), symmetric under
`V ↔ V'`, `A ↦ A⁻¹` (`wt_symm`).

* `torusState_winF` — for an observable `f` reading only the links of the time window `[0, w]`
  (`WinLocal w f`, axis links at times below `w`) and `w ≤ M`:
  `torusState hN M β f = Zc (winF f) / Zc 1`, where `winF f V A = f (cfg V A)` reads `f` on the
  configuration with slices `V` and steps `A` at non-negative times, and
  `Zc F = ∫ x, chain M (F · kT(V_M, x)) dx` closes the torus with one transfer kernel.
* `winF_shift`, `winF_refl` — on the window functions, the unit shift is `sshift` and the reflection
  at the plane `x₀ = 0` followed by `w` shifts is `revX w`, `revY invA w`.
* `winLocal_shift`, `winLocal_refl`, `WinLocal.mul`, `winLocal_of_mem` — the window predicate is
  carried by shifts, the reflection, products, and holds for every half-space observable.
-/

namespace MassGap.TorusChain

open MeasureTheory MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.HiddenChain
  MassGap.CompactGauge MassGap.LatticeGauge MassGap.WilsonLattice MassGap.KernelPower

set_option linter.unusedSectionVars false

/-! ## The sliced cubic torus -/

/-- Cubic extents. -/
abbrev Lc (M : ℕ) : Fin 4 → ℕ := fun _ => M + 1
/-- Transverse extents in direction `0`. -/
abbrev Tc (M : ℕ) : {j : Fin 4 // j ≠ 0} → ℕ := tr (Lc M) 0
/-- Spatial links of one slice. -/
abbrev Sl (M N : ℕ) : Type := SpT 0 (Tc M) → SUN.SU N
/-- Axis links of one step. -/
abbrev Ax (M N : ℕ) : Type := TT 0 (Tc M) → SUN.SU N

/-- `Measurable.comp` in applied form: unifying a composite with a concrete heavy definition can
unfold that definition, the applied form cannot. An alias of `ChainClosing.mcomp`. -/
alias meas_comp' := MassGap.ChainClosing.mcomp

/-- A jointly measurable two-argument function of two measurable functions. An alias of
`ChainClosing.mcomp2`. -/
alias meas_comp2 := MassGap.ChainClosing.mcomp2

/-- The symmetric step weight. -/
noncomputable def wt (M N : ℕ) (β : ℝ) (V : Sl M N) (A : Ax M N) (V' : Sl M N) : ℝ :=
  Real.exp (-β * spT 0 (Tc M) V / 2) * Real.exp (-β * (2 * tpT 0 (Tc M) A V V'))
    * Real.exp (-β * spT 0 (Tc M) V' / 2)

variable {M N : ℕ}

theorem continuous_wt (β : ℝ) :
    Continuous (fun p : Sl M N × Ax M N × Sl M N => wt M N β p.1 p.2.1 p.2.2) := by
  unfold wt
  have h1 : Continuous (fun p : Sl M N × Ax M N × Sl M N => spT 0 (Tc M) p.1) :=
    continuous_sp continuous_fst
  have h2 : Continuous (fun p : Sl M N × Ax M N × Sl M N => spT 0 (Tc M) p.2.2) :=
    continuous_sp (continuous_snd.comp continuous_snd)
  have h3 : Continuous (fun p : Sl M N × Ax M N × Sl M N => tpT 0 (Tc M) p.2.1 p.1 p.2.2) :=
    continuous_tp (continuous_fst.comp continuous_snd) continuous_fst
      (continuous_snd.comp continuous_snd)
  exact ((Real.continuous_exp.comp ((continuous_const.mul h1).div_const _)).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul h3)))).mul
    (Real.continuous_exp.comp ((continuous_const.mul h2).div_const _))

theorem wmeas_wt (β : ℝ) : WMeas (wt M N β) := (continuous_wt β).measurable

/-- Continuity of the step weight along continuous arguments. -/
theorem continuous_wt' (β : ℝ) {Z : Type*} [TopologicalSpace Z] {f h : Z → Sl M N}
    {g : Z → Ax M N} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun q => wt M N β (f q) (g q) (h q)) := by
  unfold wt
  have h1 : Continuous (fun q => spT 0 (Tc M) (f q)) := continuous_sp hf
  have h2 : Continuous (fun q => spT 0 (Tc M) (h q)) := continuous_sp hh
  have h3 : Continuous (fun q => tpT 0 (Tc M) (g q) (f q) (h q)) := continuous_tp hg hf hh
  exact ((Real.continuous_exp.comp ((continuous_const.mul h1).div_const _)).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul h3)))).mul
    (Real.continuous_exp.comp ((continuous_const.mul h2).div_const _))

theorem wt_nonneg (β : ℝ) (V : Sl M N) (A : Ax M N) (V' : Sl M N) : 0 ≤ wt M N β V A V' := by
  unfold wt; positivity

theorem wt_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V : Sl M N) (A : Ax M N) (V' : Sl M N) :
    wt M N β V A V' ≤ 1 := by
  unfold wt
  have a1 := sp_nonneg hN V
  have a2 := sp_nonneg hN V'
  have a3 := tp_nonneg hN A V V'
  have e1 : Real.exp (-β * spT 0 (Tc M) V / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : Real.exp (-β * (2 * tpT 0 (Tc M) A V V')) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e3 : Real.exp (-β * spT 0 (Tc M) V' / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have p1 := Real.exp_pos (-β * spT 0 (Tc M) V / 2)
  have p2 := Real.exp_pos (-β * (2 * tpT 0 (Tc M) A V V'))
  have p3 := Real.exp_pos (-β * spT 0 (Tc M) V' / 2)
  have h12 : Real.exp (-β * spT 0 (Tc M) V / 2) * Real.exp (-β * (2 * tpT 0 (Tc M) A V V')) ≤ 1 := by
    nlinarith
  nlinarith [mul_pos p1 p2]

theorem abs_wt_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (V : Sl M N) (A : Ax M N) (V' : Sl M N), |wt M N β V A V'| ≤ 1 := fun V A V' => by
  rw [abs_of_nonneg (wt_nonneg β V A V')]; exact wt_le_one hN hβ V A V'

theorem kern_wt (β : ℝ) : kern (hA 0 (Tc M) N) (wt M N β) = kT 0 (Tc M) N β := by
  funext x y
  simp only [kern, wt, kT, gk]
  rw [integral_mul_const, integral_const_mul]

/-- Pointwise inversion of the axis links. -/
noncomputable def invA : Ax M N ≃ᵐ Ax M N :=
  MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.inv (SUN.SU N))

theorem invA_apply (A : Ax M N) : invA A = fun y => (A y)⁻¹ := rfl

theorem invA_invA (A : Ax M N) : invA (invA A) = A := by
  funext y; simp [invA_apply]

theorem mp_invA : MeasurePreserving (invA (M := M) (N := N)) (hA 0 (Tc M) N) (hA 0 (Tc M) N) :=
  measurePreserving_invAx

theorem wt_symm (β : ℝ) (V : Sl M N) (A : Ax M N) (V' : Sl M N) :
    wt M N β V A V' = wt M N β V' (invA A) V := by
  unfold wt; rw [invA_apply, tp_inv]; ring

/-! ## The torus as a chain -/

/-- The torus integral of an insertion, closed by one transfer kernel. -/
noncomputable def Zc (M N : ℕ) (β : ℝ) (F : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ) : ℝ :=
  ∫ x, chain (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
    (fun V A => F V A * kT 0 (Tc M) N β (V M) x) x ∂(hS 0 (Tc M) N)

/-- A cyclic sequence of slice configurations from its axis and spatial parts. -/
def joinW (A : Fin (M + 1) → Ax M N) (V : Fin (M + 1) → Sl M N) :
    Fin (Lc M 0) → SlIdx (Lc M) 0 → SUN.SU N := fun t => Sum.elim (A t) (V t)

theorem measurable_joinW :
    Measurable (fun p : (Fin (M + 1) → Ax M N) × (Fin (M + 1) → Sl M N) => joinW p.1 p.2) := by
  refine measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun s => ?_
  cases s with
  | inl y => exact (measurable_pi_apply y).comp ((measurable_pi_apply t).comp measurable_fst)
  | inr q => exact (measurable_pi_apply q).comp ((measurable_pi_apply t).comp measurable_snd)

theorem prod_exp_wt (β : ℝ) (A : Fin (M + 1) → Ax M N) (V : Fin (M + 1) → Sl M N) :
    ∏ t, Real.exp (-β * (spT 0 (Tc M) (V t)
        + 2 * tpT 0 (Tc M) (A t) (V t) (V (finRotate (M + 1) t))))
      = ∏ t, wt M N β (V t) (A t) (V (finRotate (M + 1) t)) := by
  have h1 : ∀ t, Real.exp (-β * (spT 0 (Tc M) (V t)
        + 2 * tpT 0 (Tc M) (A t) (V t) (V (finRotate (M + 1) t))))
      = Real.exp (-β * spT 0 (Tc M) (V t) / 2)
        * Real.exp (-β * (2 * tpT 0 (Tc M) (A t) (V t) (V (finRotate (M + 1) t))))
        * Real.exp (-β * spT 0 (Tc M) (V t) / 2) := fun t => by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hrot : ∏ t, Real.exp (-β * spT 0 (Tc M) (V (finRotate (M + 1) t)) / 2)
      = ∏ t, Real.exp (-β * spT 0 (Tc M) (V t) / 2) :=
    Fintype.prod_equiv (finRotate (M + 1)) _ _ (fun t => rfl)
  simp only [h1, wt, Finset.prod_mul_distrib, hrot]

theorem continuous_prod_wt (β : ℝ) :
    Continuous (fun p : (Fin (M + 1) → Ax M N) × (Fin (M + 1) → Sl M N) =>
      ∏ t, wt M N β (p.2 t) (p.1 t) (p.2 (finRotate (M + 1) t))) := by
  refine continuous_finset_prod _ fun t _ => ?_
  exact continuous_wt' β ((continuous_apply t).comp continuous_snd)
    ((continuous_apply t).comp continuous_fst)
    ((continuous_apply (finRotate (M + 1) t)).comp continuous_snd)

theorem abs_prod_wt_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (A : Fin (M + 1) → Ax M N)
    (V : Fin (M + 1) → Sl M N) :
    |∏ t, wt M N β (V t) (A t) (V (finRotate (M + 1) t))| ≤ 1 := by
  have := CyclicKernel.abs_prod_le (u := fun t => wt M N β (V t) (A t) (V (finRotate (M + 1) t)))
    (C := 1) (fun t => abs_wt_le hN hβ _ _ _)
  simpa using this

/-- Peel the last axis slice, which no insertion reads. -/
theorem peel (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V : Fin (M + 1) → Sl M N)
    {g : (Fin M → Ax M N) → ℝ} (hg : Measurable g) {Bg : ℝ} (hgb : ∀ A, |g A| ≤ Bg) :
    ∫ A : Fin (M + 1) → Ax M N, g (fun t : Fin M => A t.castSucc)
        * ∏ t, wt M N β (V t) (A t) (V (finRotate (M + 1) t)) ∂(Measure.pi fun _ => hA 0 (Tc M) N)
      = ∫ A' : Fin M → Ax M N, g A' * pathW (wt M N β) V A'
          * kT 0 (Tc M) N β (V (Fin.last M)) (V 0) ∂(Measure.pi fun _ => hA 0 (Tc M) N) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => hA 0 (Tc M) N) (Fin.last M)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => Ax M N) (Fin.last M)
  set f : (Fin (M + 1) → Ax M N) → ℝ := fun A => g (fun t : Fin M => A t.castSucc)
    * ∏ t, wt M N β (V t) (A t) (V (finRotate (M + 1) t))
  have hfm : Measurable f := by
    simp only [f]
    have hc : Measurable (fun A : Fin (M + 1) → Ax M N => fun t : Fin M => A t.castSucc) :=
      measurable_pi_lambda _ fun t => measurable_pi_apply t.castSucc
    have hp : Measurable (fun A : Fin (M + 1) → Ax M N =>
        ∏ t, wt M N β (V t) (A t) (V (finRotate (M + 1) t))) :=
      Finset.measurable_prod _ fun t _ =>
        (continuous_wt' β continuous_const (continuous_apply t) continuous_const).measurable
    exact (hg.comp hc).mul hp
  have hfb : ∀ A, |f A| ≤ Bg := fun A => by
    simp only [f]
    have := abs_mul_le_of (hgb (fun t : Fin M => A t.castSucc)) (abs_prod_wt_le hN hβ A V)
    rwa [mul_one] at this
  have he : ∀ (a : Ax M N) (A' : Fin M → Ax M N), e.symm (a, A') = Fin.snoc A' a :=
    fun a A' => Fin.insertNth_last' a A'
  have h1 : ∫ A, f A ∂(Measure.pi fun _ => hA 0 (Tc M) N)
      = ∫ q, f (e.symm q) ∂((hA 0 (Tc M) N).prod (Measure.pi fun _ : Fin M => hA 0 (Tc M) N)) := by
    rw [← hmp.integral_comp' (g := fun q => f (e.symm q))]
    simp
  have hint : Integrable (fun q => f (e.symm q))
      ((hA 0 (Tc M) N).prod (Measure.pi fun _ : Fin M => hA 0 (Tc M) N)) :=
    integrable_of_bdd (hfm.comp e.symm.measurable) (fun q => hfb _)
  have hpt : ∀ (A' : Fin M → Ax M N) (a : Ax M N),
      f (Fin.snoc A' a) = (g A' * pathW (wt M N β) V A') * wt M N β (V (Fin.last M)) a (V 0) := by
    intro A' a
    simp only [f]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, finRotate_last]
    have hrot : ∀ t : Fin M, finRotate (M + 1) t.castSucc = t.succ := fun t => by
      rw [finRotate_apply, Fin.coeSucc_eq_succ]
    simp only [hrot]
    unfold pathW; ring
  change ∫ A, f A ∂(Measure.pi fun _ => hA 0 (Tc M) N) = _
  rw [h1, integral_prod_symm _ hint]
  congr 1; funext A'
  simp_rw [he, hpt]
  rw [integral_const_mul]
  congr 1
  exact congrFun (congrFun (kern_wt (M := M) (N := N) β) _) _

set_option maxHeartbeats 800000 in
/-- **The Wilson correlation numerator of the cubic torus as a closed chain.** -/
theorem corrNum_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {O : (RLink (Lc M) → SUN.SU N) → ℝ}
    (hO : Measurable O) {BO : ℝ} (hOb : ∀ U, |O U| ≤ BO)
    {F : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ}
    (hF : Measurable (fun q : (ℕ → Sl M N) × (ℕ → Ax M N) => F q.1 q.2)) {BF : ℝ}
    (hFb : ∀ V A, |F V A| ≤ BF)
    (hOF : ∀ A V, O (Φ (Lc M) 0 (joinW A V)) = F (extX V) (extY (fun t : Fin M => A t.castSucc))) :
    (sysR (Lc M) N).corrNum (probHaar (SUN.SU N)) β O = Zc M N β F := by
  have hmp := measurePreserving_Φ (L := Lc M) (μ := 0) N
  unfold System.corrNum System.vol
  change ∫ U : RLink (Lc M) → SUN.SU N, O U * (sysR (Lc M) N).boltz β U
      ∂(Measure.pi fun _ : RLink (Lc M) => probHaar (SUN.SU N)) = _
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (hO.mul (measurable_boltzR (L := Lc M) N β)).aestronglyMeasurable]
  -- the axis/spatial split of each slice
  set φ := (⇑(MeasurableEquiv.arrowProdEquivProdArrow (TS (Lc M) 0 → SUN.SU N)
      (SpIdx (Lc M) 0 → SUN.SU N) (Fin (M + 1)))) ∘
    fun (W : Fin (M + 1) → SlIdx (Lc M) 0 → SUN.SU N) t =>
      MeasurableEquiv.sumPiEquivProdPi (fun _ : SlIdx (Lc M) 0 => SUN.SU N) (W t) with hφdef
  have hφ : MeasurePreserving φ
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : SlIdx (Lc M) 0 => probHaar (SUN.SU N))
      ((Measure.pi fun _ : Fin (M + 1) => hA 0 (Tc M) N).prod
        (Measure.pi fun _ : Fin (M + 1) => hS 0 (Tc M) N)) := by
    have hmp1 : MeasurePreserving
        (fun (W : Fin (M + 1) → SlIdx (Lc M) 0 → SUN.SU N) t =>
          MeasurableEquiv.sumPiEquivProdPi (fun _ : SlIdx (Lc M) 0 => SUN.SU N) (W t))
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : SlIdx (Lc M) 0 => probHaar (SUN.SU N))
        (Measure.pi fun _ : Fin (M + 1) => (hA 0 (Tc M) N).prod (hS 0 (Tc M) N)) :=
      measurePreserving_pi _ _ fun _ => measurePreserving_sumPiEquivProdPi _
    have hmp2 := measurePreserving_arrowProdEquivProdArrow (TS (Lc M) 0 → SUN.SU N)
      (SpIdx (Lc M) 0 → SUN.SU N) (Fin (M + 1)) (fun _ => hA 0 (Tc M) N) (fun _ => hS 0 (Tc M) N)
    exact hmp2.comp hmp1
  set H : (Fin (M + 1) → Ax M N) × (Fin (M + 1) → Sl M N) → ℝ :=
    fun p => O (Φ (Lc M) 0 (joinW p.1 p.2)) * ∏ t, wt M N β (p.2 t) (p.1 t) (p.2 (finRotate (M + 1) t))
  have hHm : Measurable H := by
    simp only [H]
    exact (meas_comp' hO (meas_comp' hmp.measurable measurable_joinW)).mul
      (continuous_prod_wt β).measurable
  have hHb : ∀ p, |H p| ≤ BO := fun p => by
    simp only [H]
    have := abs_mul_le_of (hOb (Φ (Lc M) 0 (joinW p.1 p.2))) (abs_prod_wt_le hN hβ p.1 p.2)
    rwa [mul_one] at this
  have hjoin : ∀ W, joinW (φ W).1 (φ W).2 = W := by
    intro W; funext t s; cases s <;> rfl
  have hHW : ∀ W, O (Φ (Lc M) 0 W) * (sysR (Lc M) N).boltz β (Φ (Lc M) 0 W) = H (φ W) := by
    intro W
    simp only [H]
    rw [hjoin W]
    congr 1
    unfold System.boltz
    rw [action_Φ hN W, Finset.mul_sum, Real.exp_sum]
    exact prod_exp_wt β _ _
  have step1 : ∫ W, O (Φ (Lc M) 0 W) * (sysR (Lc M) N).boltz β (Φ (Lc M) 0 W)
      ∂(Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : SlIdx (Lc M) 0 => probHaar (SUN.SU N))
      = ∫ p, H p ∂((Measure.pi fun _ : Fin (M + 1) => hA 0 (Tc M) N).prod
          (Measure.pi fun _ : Fin (M + 1) => hS 0 (Tc M) N)) := by
    simp_rw [hHW]
    rw [← hφ.map_eq, integral_map hφ.measurable.aemeasurable hHm.aestronglyMeasurable]
  rw [step1, integral_prod_symm H (integrable_of_bdd hHm hHb)]
  -- peel the last axis slice
  have hFV : ∀ V : Fin (M + 1) → Sl M N, Measurable (fun A' : Fin M → Ax M N => F (extX V) (extY A')) :=
    fun V => hF.comp (measurable_const.prodMk measurable_extY)
  have step2 : ∀ V : Fin (M + 1) → Sl M N, ∫ A, H (A, V) ∂(Measure.pi fun _ => hA 0 (Tc M) N)
      = ∫ A' : Fin M → Ax M N, F (extX V) (extY A') * pathW (wt M N β) V A'
          * kT 0 (Tc M) N β (V (Fin.last M)) (V 0) ∂(Measure.pi fun _ => hA 0 (Tc M) N) := by
    intro V
    simp only [H, hOF]
    exact peel hN hβ V (hFV V) (fun A' => hFb _ _)
  simp_rw [step2]
  -- the bridge
  have hG : Measurable (fun q : (ℕ → Sl M N) × (ℕ → Ax M N) =>
      F q.1 q.2 * kT 0 (Tc M) N β (q.1 M) (q.1 0)) := by
    refine hF.mul ?_
    have hk : Measurable (Function.uncurry (kT 0 (Tc M) N β)) :=
      (continuous_kT (μ := 0) (T := Tc M) (N := N) β).measurable
    exact meas_comp2 hk ((measurable_pi_apply M).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_fst)
  have hGb : ∀ V A, |F V A * kT 0 (Tc M) N β (V M) (V 0)| ≤ BF * 1 := fun V A =>
    abs_mul_le_of (hFb V A) (abs_kT_le hN hβ _ _)
  have hbr := bridge (μ := hS 0 (Tc M) N) (ν := hA 0 (Tc M) N) (wmeas_wt β)
    (fun V A V' => abs_wt_le hN hβ V A V') M
    (G := fun V A => F V A * kT 0 (Tc M) N β (V M) (V 0)) hG hGb
  unfold Zc
  have hcl : ∀ x, chain (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
      (fun V A => F V A * kT 0 (Tc M) N β (V M) x) x
      = chain (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
        (fun V A => F V A * kT 0 (Tc M) N β (V M) (V 0)) x :=
    fun x => chain_congr M (fun V A hV => by rw [hV])
  simp_rw [hcl]
  rw [← hbr]
  congr 1; funext V; congr 1; funext A'
  rw [extX_last, extX_zero]; ring

/-- The two Wilson systems on the cubic torus have the same expectation. -/
theorem expect_cubic (β : ℝ) (O : (RLink (Lc M) → SUN.SU N) → ℝ) :
    ReflectPositive.EW (d := 4) (n := M + 1) N β O
      = (sysR (Lc M) N).expect (probHaar (SUN.SU N)) β O := by
  have key : ∀ b : RPlaq (Lc M) → List (RLink (Lc M) × Bool),
      b = WilsonHypercubic.bd (d := 4) (n := M + 1) →
      (wilsonSystem (G := SUN.SU N) b (WilsonAction.wilsonDensity (N := N))).expect
          (probHaar (SUN.SU N)) β O
        = (wilsonSystem (G := SUN.SU N) (WilsonHypercubic.bd (d := 4) (n := M + 1))
            (WilsonAction.wilsonDensity (N := N))).expect (probHaar (SUN.SU N)) β O := by
    rintro b rfl; rfl
  exact (key (rbd (Lc M)) (TorusIdentify.rbd_cubic M)).symm

/-! ## Observables read on a time window -/

/-- Transverse coordinates of a site, reduced modulo `M + 1`. -/
noncomputable def perpI (M : ℕ) (s : Fin 4 → ℤ) : TT 0 (Tc M) :=
  fun j => InfiniteLattice.finMod M (s j.1)

theorem perpI_update (s : Fin 4 → ℤ) (v : ℤ) : perpI M (Function.update s 0 v) = perpI M s := by
  funext j; simp only [perpI, Function.update_of_ne j.2]

/-- The `ℤ⁴` configuration with slices `V` and steps `A` at non-negative times, `1` elsewhere. -/
noncomputable def cfg (M N : ℕ) (V : ℕ → Sl M N) (A : ℕ → Ax M N) : GibbsSpec.IConf (SUN.SU N) :=
  fun l => if 0 ≤ l.2 0 then
      (if h : l.1 = 0 then A (l.2 0).toNat (perpI M l.2)
        else V (l.2 0).toNat (⟨l.1, h⟩, perpI M l.2))
    else 1

theorem cfg_axis {V : ℕ → Sl M N} {A : ℕ → Ax M N} {l : GibbsSpec.ILink} (h : l.1 = 0)
    (h0 : 0 ≤ l.2 0) : cfg M N V A l = A (l.2 0).toNat (perpI M l.2) := by
  simp only [cfg, if_pos h0, dif_pos h]

theorem cfg_sp {V : ℕ → Sl M N} {A : ℕ → Ax M N} {l : GibbsSpec.ILink} (h : l.1 ≠ 0)
    (h0 : 0 ≤ l.2 0) : cfg M N V A l = V (l.2 0).toNat (⟨l.1, h⟩, perpI M l.2) := by
  simp only [cfg, if_pos h0, dif_neg h]

theorem measurable_cfg : Measurable (fun q : (ℕ → Sl M N) × (ℕ → Ax M N) => cfg M N q.1 q.2) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h0 : 0 ≤ l.2 0
  · by_cases h : l.1 = 0
    · simp only [cfg, if_pos h0, dif_pos h]
      exact (measurable_pi_apply (perpI M l.2)).comp
        ((measurable_pi_apply (l.2 0).toNat).comp measurable_snd)
    · simp only [cfg, if_pos h0, dif_neg h]
      exact (measurable_pi_apply ((⟨l.1, h⟩ : {j : Fin 4 // j ≠ 0}), perpI M l.2)).comp
        ((measurable_pi_apply (l.2 0).toNat).comp measurable_fst)
  · simp only [cfg, if_neg h0]; exact measurable_const

/-- An observable read on the chain variables. -/
noncomputable def winF (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ :=
  fun V A => f (cfg M N V A)

theorem measurable_winF (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    Measurable (fun q : (ℕ → Sl M N) × (ℕ → Ax M N) => winF f q.1 q.2) :=
  f.continuous.measurable.comp measurable_cfg

theorem winF_bdd (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    ∃ B, ∀ V A, |winF (M := M) f V A| ≤ B := by
  obtain ⟨C, hC⟩ := InfiniteLattice.bounded_of_continuous f.continuous
  exact ⟨C, fun V A => hC _⟩

/-- A link of the time window `[0, w]`: spatial at times `0..w`, axis at times `0..w−1`. -/
def InWin (w : ℕ) (l : GibbsSpec.ILink) : Prop :=
  0 ≤ l.2 0 ∧ l.2 0 ≤ w ∧ (l.1 = 0 → l.2 0 < w)

/-- `f` reads only links of the time window `[0, w]`. -/
def WinLocal (w : ℕ) (f : GibbsSpec.IConf (SUN.SU N) → ℝ) : Prop :=
  ∀ U U' : GibbsSpec.IConf (SUN.SU N), (∀ l, InWin w l → U l = U' l) → f U = f U'

theorem WinLocal.mono {w w' : ℕ} {f : GibbsSpec.IConf (SUN.SU N) → ℝ} (h : WinLocal w f)
    (hw : w ≤ w') : WinLocal w' f :=
  fun U U' hUU => h U U' fun l ⟨h0, h1, h2⟩ =>
    hUU l ⟨h0, by omega, fun hl => by have := h2 hl; omega⟩

theorem WinLocal.mul {w : ℕ} {f g : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f)
    (hg : WinLocal w g) : WinLocal w (f * g) := fun U U' h => by
  simp only [ContinuousMap.mul_apply]; rw [hf U U' h, hg U U' h]

theorem localUpTo_winF {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f) :
    LocalUpTo w (winF (M := M) f) := by
  intro V V' A A' hV hA
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, hw, hax⟩
  dsimp only at h0 hw hax
  by_cases h : d0 = 0
  · rw [cfg_axis h h0, cfg_axis h h0]
    dsimp only
    rw [hA _ (by have := hax h; omega)]
  · rw [cfg_sp h h0, cfg_sp h h0]
    dsimp only
    rw [hV _ (by omega)]

/-- Every half-space observable reads a finite time window. -/
theorem winLocal_of_mem {x : C(GibbsSpec.IConf (SUN.SU N), ℝ)}
    (hx : x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := SUN.SU N) 0 0) : ∃ R : ℕ, WinLocal R x := by
  obtain ⟨S, hS, hloc⟩ := hx
  set R0 : ℕ := S.sup (fun l : InfiniteLattice.ILink => (l.2 0).toNat) with hR0
  refine ⟨R0 + 1, fun U U' hUU => hloc U U' fun l hl => hUU l ?_⟩
  have h0 : (0 : ℤ) ≤ l.2 0 := hS hl
  have hle : (l.2 0).toNat ≤ R0 := Finset.le_sup (f := fun l : InfiniteLattice.ILink => (l.2 0).toNat) hl
  refine ⟨h0, ?_, fun _ => ?_⟩
  · show l.2 0 ≤ ((R0 + 1 : ℕ) : ℤ)
    push_cast; omega
  · show l.2 0 < ((R0 + 1 : ℕ) : ℤ)
    push_cast; omega

/-! ## Shift and reflection on window functions -/

theorem shD_ishiftLink (d : ℕ) (l : InfiniteLattice.ILink) :
    ((InfiniteShift.ishiftLink 0 l).1,
      Function.update (InfiniteShift.ishiftLink 0 l).2 0 ((InfiniteShift.ishiftLink 0 l).2 0 + d))
      = (l.1, Function.update l.2 0 (l.2 0 + ((d + 1 : ℕ) : ℤ))) := by
  simp only [InfiniteShift.ishiftLink, InfiniteLattice.ishift, Function.update_self,
    Function.update_idem]
  congr 2; push_cast; ring

theorem shiftObs_iter (d : ℕ) (f : C(GibbsSpec.IConf (SUN.SU N), ℝ))
    (U : GibbsSpec.IConf (SUN.SU N)) :
    ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] f) U
      = f (fun l => U (l.1, Function.update l.2 0 (l.2 0 + d))) := by
  induction d generalizing f with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply, ih]
    show f (InfiniteShift.ishiftConf 0 (fun l => U (l.1, Function.update l.2 0 (l.2 0 + d)))) = _
    congr 1; funext l
    exact congrArg U (shD_ishiftLink d l)

theorem irefl_axis (U : GibbsSpec.IConf (SUN.SU N)) (s : Fin 4 → ℤ) :
    LatticeReflection.ireflConf 0 0 U (0, s) = (U (0, Function.update s 0 (-1 - s 0)))⁻¹ := by
  simp [LatticeReflection.ireflConf, LatticeReflection.ireflLink, LatticeReflection.ireflSite]

theorem irefl_sp (U : GibbsSpec.IConf (SUN.SU N)) {d0 : Fin 4} (h : d0 ≠ 0) (s : Fin 4 → ℤ) :
    LatticeReflection.ireflConf 0 0 U (d0, s) = U (d0, Function.update s 0 (-s 0)) := by
  simp [LatticeReflection.ireflConf, LatticeReflection.ireflLink, LatticeReflection.ireflSite, h]

theorem winLocal_shift {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f)
    (d : ℕ) : WinLocal (w + d) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] f) := by
  intro U U' hUU
  rw [shiftObs_iter, shiftObs_iter]
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

theorem winLocal_refl {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f) :
    WinLocal w ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[w]
      (LatticeReflection.ireflObs 0 0 f)) := by
  intro U U' hUU
  rw [shiftObs_iter, shiftObs_iter, LatticeReflection.ireflObs_apply,
    LatticeReflection.ireflObs_apply]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  by_cases h : d0 = 0
  · subst h
    have ht := h2 rfl
    rw [irefl_axis, irefl_axis]
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
  · rw [irefl_sp _ h, irefl_sp _ h]
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

theorem winF_shift {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f) (d : ℕ)
    (V : ℕ → Sl M N) (A : ℕ → Ax M N) :
    winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[d] f) V A
      = winF f (sshift V d) (sshift A d) := by
  unfold winF
  rw [shiftObs_iter]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, -, -⟩
  dsimp only at h0 ⊢
  have h1 : 0 ≤ (Function.update s 0 (s 0 + (d : ℤ))) 0 := by simp; omega
  have hx : ((Function.update s 0 (s 0 + (d : ℤ))) 0).toNat = (s 0).toNat + d := by simp; omega
  by_cases h : d0 = 0
  · rw [cfg_axis (l := (d0, Function.update s 0 (s 0 + (d : ℤ)))) h h1,
      cfg_axis (l := (d0, s)) h h0]
    dsimp only
    rw [perpI_update, hx]; rfl
  · rw [cfg_sp (l := (d0, Function.update s 0 (s 0 + (d : ℤ)))) h h1,
      cfg_sp (l := (d0, s)) h h0]
    dsimp only
    rw [perpI_update, hx]; rfl

theorem winF_refl {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f)
    (V : ℕ → Sl M N) (A : ℕ → Ax M N) :
    winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[w] (LatticeReflection.ireflObs 0 0 f))
        V A
      = winF f (revX w V) (revY (fun a : Ax M N => invA a) w A) := by
  unfold winF
  rw [shiftObs_iter, LatticeReflection.ireflObs_apply]
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  by_cases h : d0 = 0
  · subst h
    have ht := h2 rfl
    rw [irefl_axis]
    dsimp only
    have hy : 0 ≤ (Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0 := by simp; omega
    rw [cfg_axis (l := (0, Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ)))) rfl hy, cfg_axis (l := (0, s)) rfl h0]
    dsimp only
    rw [perpI_update, perpI_update]
    have hx : ((Function.update (Function.update s 0 (-1 - s 0)) 0
        ((Function.update s 0 (-1 - s 0)) 0 + (w : ℤ))) 0).toNat = w - 1 - (s 0).toNat := by
      simp; omega
    rw [hx]
    simp only [revY, invA_apply]
  · rw [irefl_sp _ h]
    dsimp only
    have hy : 0 ≤ (Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0 := by simp; omega
    rw [cfg_sp (l := (d0, Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ)))) h hy, cfg_sp (l := (d0, s)) h h0]
    dsimp only
    rw [perpI_update, perpI_update]
    have hx : ((Function.update (Function.update s 0 (-s 0)) 0
        ((Function.update s 0 (-s 0)) 0 + (w : ℤ))) 0).toNat = w - (s 0).toNat := by
      simp; omega
    rw [hx]
    rfl

/-! ## The torus state on window observables -/

theorem pullback_Φ (W : Fin (M + 1) → SlIdx (Lc M) 0 → SUN.SU N) (l : InfiniteLattice.ILink) :
    InfiniteLattice.pullback M (Φ (Lc M) 0 W) l
      = W (InfiniteLattice.finMod M (l.2 0)) (sIdx (L := Lc M) (μ := 0) l.1 (perpI M l.2)) := rfl

theorem torus_window {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f)
    (hwM : w ≤ M) (A : Fin (M + 1) → Ax M N) (V : Fin (M + 1) → Sl M N) :
    f (InfiniteLattice.pullback M (Φ (Lc M) 0 (joinW A V)))
      = winF f (extX V) (extY (fun t : Fin M => A t.castSucc)) := by
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  rw [pullback_Φ]
  dsimp only
  have hfm : InfiniteLattice.finMod M (s 0) = ⟨(s 0).toNat, by omega⟩ := by
    apply Fin.ext
    show ((s 0) % ((M : ℤ) + 1)).toNat = (s 0).toNat
    rw [Int.emod_eq_of_lt h0 (by omega)]
  rw [hfm]
  by_cases h : d0 = 0
  · subst h
    have ht := h2 rfl
    rw [cfg_axis (l := (0, s)) rfl h0]
    have hs : sIdx (L := Lc M) (μ := 0) 0 (perpI M s) = Sum.inl (perpI M s) := by simp [sIdx]
    rw [hs]
    show A ⟨(s 0).toNat, _⟩ (perpI M s) = extY (fun t : Fin M => A t.castSucc) (s 0).toNat (perpI M s)
    simp only [extY, dif_pos (show (s 0).toNat < M by omega)]
    rfl
  · rw [cfg_sp (l := (d0, s)) h h0]
    have hs : sIdx (L := Lc M) (μ := 0) d0 (perpI M s) = Sum.inr (⟨d0, h⟩, perpI M s) := by
      simp [sIdx, h]
    rw [hs]
    show V ⟨(s 0).toNat, _⟩ (⟨d0, h⟩, perpI M s) = extX V (s 0).toNat (⟨d0, h⟩, perpI M s)
    simp only [extX, dif_pos (show (s 0).toNat < M + 1 by omega)]

/-- **The periodic Wilson state on a window observable is a ratio of closed chains.** -/
theorem torusState_winF (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ}
    {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocal w f) (hwM : w ≤ M) :
    PeriodicState.torusState hN M β f = Zc M N β (winF f) / Zc M N β (fun _ _ => 1) := by
  have e : PeriodicState.torusState hN M β f
      = (sysR (Lc M) N).expect (probHaar (SUN.SU N)) β (PeriodicState.torusObs M f) := by
    show ReflectPositive.EW (d := 4) (n := M + 1) N β (PeriodicState.torusObs M f) = _
    exact expect_cubic β _
  obtain ⟨Bf, hBf⟩ := InfiniteLattice.bounded_of_continuous f.continuous
  obtain ⟨BF, hBF⟩ := winF_bdd (M := M) f
  have hnum := corrNum_eq hN hβ (O := PeriodicState.torusObs M f)
    (PeriodicState.measurable_torusObs M f) (fun U => hBf _) (measurable_winF f) hBF
    (fun A V => torus_window hf hwM A V)
  have hden := corrNum_eq (M := M) hN hβ (O := fun _ => 1) measurable_const (BO := 1)
    (fun _ => by simp) (F := fun _ _ => 1) measurable_const (BF := 1) (fun _ _ => by simp)
    (fun _ _ => rfl)
  rw [e, System.expect, hnum, ← hden]
  congr 1
  simp [System.partition, System.corrNum]

#print axioms corrNum_eq
#print axioms torusState_winF
#print axioms winF_refl
#print axioms winF_shift

end MassGap.TorusChain
