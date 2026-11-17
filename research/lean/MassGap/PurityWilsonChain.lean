import Mathlib
import MassGap.PurityTwoLift
import MassGap.PurityPlaqCount

/-!
# MassGap.PurityWilsonChain — (8.1) for the Wilson plaquette action

(8.1) of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
for `G = SU(N)`, `μ_t` the product Haar measure on the links of the 4-torus and `A_t` the plaquette
action `PurityPlaqCount.plaqAction`.

The torus is a cycle of time slices in direction `μ`. A slice variable `V : E T`,
`E T = (TT μ T ⊕ SpT μ T) → SU(N)`, holds the axis links leaving the slice (`Sum.inl`) and the
spatial links in it (`Sum.inr`); its law is product Haar. The bond weight between consecutive
slices is
`bondW μ T V V' = 6 ∏_j T_j − (spT(V) + 2 tpT(V, V'))/2`
(`sliceAct`), so that `plaqAction L N (Φ L μ W) = Σ_t bondW (W t) (W (t+1))` (`plaqAction_Φ`,
from `RectWilson.action_Φ` and `PurityPlaqCount.action_eq`).

* `L μ = m+1`: the configuration `Φ L μ (Y ∘ finCongr)` gives `plaqAction = chain bondW Y`
  (`plaqAction_chain`).
* `L μ = 2(m+1)`: the slices `t` correspond to `(x, e) : Fin (m+1) × Bool` through `kEquiv`,
  `t = x + (m+1)[e]`, and `t ↦ t+1` is the cover step `(x, e) ↦ (x+1, e ⊕ flip x)` (`kEquiv_walk`);
  the configuration built from the sheets of `Z : Fin (m+1) → E × E` gives
  `plaqAction = cover bondW Z` (`plaqAction_cover`).

Both maps carry the product Haar measure to the product Haar measure on the links
(`measurePreserving_reindex`, `measurePreserving_sheets`, `RectWilson.measurePreserving_Φ`), so the
moment generating functions agree (`complexMGF_chain`, `complexMGF_cover`). `bondW` is measurable
and bounded (`RectTransfer.sp_le`, `RectTransfer.tp_le`), and `PurityTwoLift.hvan_cover` gives (8.1)
(`hvan_wilson`). `corollary_window_wilson` is Corollary 8.2's bound
`|Ψ_T(x)| ≤ V/(161(48T)³)` for the Wilson action with (8.1) discharged.
-/

namespace MassGap.PurityWilsonChain

open MeasureTheory ProbabilityTheory MassGap MassGap.RectWilson MassGap.CompactGauge
  MassGap.PurityPlaqCount

/-! ## The bond weight -/

section Bond

variable {N : ℕ} (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ)

/-- The spatial links of a slice variable. -/
def sl (V : TT μ T ⊕ SpT μ T → SUN.SU N) : SpT μ T → SUN.SU N := fun p => V (Sum.inr p)

/-- The axis links of a slice variable. -/
def ax (V : TT μ T ⊕ SpT μ T → SUN.SU N) : TT μ T → SUN.SU N := fun y => V (Sum.inl y)

/-- The Wilson action of a slice and of the temporal plaquettes to the next slice. -/
noncomputable def sliceAct (V V' : TT μ T ⊕ SpT μ T → SUN.SU N) : ℝ :=
  spT μ T (sl μ T V) + 2 * tpT μ T (ax μ T V) (sl μ T V) (sl μ T V')

/-- The plaquette action of a slice and of the temporal plaquettes to the next slice. DERIVED:
`6 = C(4,2)` the unoriented plaquettes per site in four dimensions; `2` because `spT` sums ordered
pairs `(ν, ν')` and counts each spatial plaquette twice, as in `PurityPlaqCount.action_eq`. -/
noncomputable def bondW (V V' : TT μ T ⊕ SpT μ T → SUN.SU N) : ℝ :=
  6 * ∏ j, (T j : ℝ) - sliceAct μ T V V' / 2

variable {μ T}

theorem abs_bondW_le (hN : N ≠ 0) (V V' : TT μ T ⊕ SpT μ T → SUN.SU N) :
    |bondW μ T V V'| ≤ 6 * ∏ j, (T j : ℝ) + (RectTransfer.spMax μ T + 2 * RectTransfer.tpMax μ T) / 2 := by
  have hP : 0 ≤ ∏ j, (T j : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  have a1 := RectTransfer.sp_nonneg hN (sl μ T V)
  have a2 := RectTransfer.sp_le hN (sl μ T V)
  have a3 := RectTransfer.tp_nonneg hN (ax μ T V) (sl μ T V) (sl μ T V')
  have a4 := RectTransfer.tp_le hN (ax μ T V) (sl μ T V) (sl μ T V')
  unfold bondW sliceAct
  rw [abs_le]
  constructor <;> linarith

theorem measurable_sliceAct :
    Measurable fun p : (TT μ T ⊕ SpT μ T → SUN.SU N) × (TT μ T ⊕ SpT μ T → SUN.SU N) =>
      sliceAct μ T p.1 p.2 := by
  have h1 : ∀ k, Measurable fun p : (TT μ T ⊕ SpT μ T → SUN.SU N)
      × (TT μ T ⊕ SpT μ T → SUN.SU N) => p.1 k :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have h2 : ∀ k, Measurable fun p : (TT μ T ⊕ SpT μ T → SUN.SU N)
      × (TT μ T ⊕ SpT μ T → SUN.SU N) => p.2 k :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  unfold sliceAct spT tpT sl ax
  refine Measurable.add ?_ (measurable_const.mul ?_)
  · exact Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
      Finset.measurable_sum _ fun _ _ => WilsonAction.measurable_wilsonDensity.comp
        ((((h1 _).mul (h1 _)).mul (h1 _).inv).mul (h1 _).inv)
  · exact Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
      WilsonAction.measurable_wilsonDensity.comp
        ((((h1 _).mul (h2 _)).mul (h1 _).inv).mul (h1 _).inv)

theorem measurable_bondW : Measurable (Function.uncurry (bondW (N := N) μ T)) := by
  show Measurable fun p : (TT μ T ⊕ SpT μ T → SUN.SU N) × (TT μ T ⊕ SpT μ T → SUN.SU N) =>
    6 * ∏ j, (T j : ℝ) - sliceAct μ T p.1 p.2 / 2
  exact measurable_const.sub (measurable_sliceAct.div_const 2)

end Bond

/-! ## The plaquette action as a sum over consecutive slices -/

variable {N : ℕ} {L : Fin 4 → ℕ} {μ : Fin 4}

theorem prod_tr (L : Fin 4 → ℕ) (μ : Fin 4) :
    ∏ j, ((tr L μ j : ℕ) : ℝ) = ∏ i ∈ Finset.univ.erase μ, (L i : ℝ) :=
  (Finset.prod_subtype (Finset.univ.erase μ) (p := (· ≠ μ)) (fun i => by simp)
    fun i => (L i : ℝ)).symm

theorem plaqAction_Φ (hN : N ≠ 0) (W : Fin (L μ) → SlIdx L μ → SUN.SU N) :
    plaqAction L N (Φ L μ W) = ∑ t, bondW μ (tr L μ) (W t) (W (finRotate (L μ) t)) := by
  have h1 := action_eq hN (Φ L μ W)
  rw [action_Φ hN W, prod_eq μ] at h1
  have h1' : ∑ t, sliceAct μ (tr L μ) (W t) (W (finRotate (L μ) t))
      = 12 * ((∏ i ∈ Finset.univ.erase μ, (L i : ℝ)) * L μ) - 2 * plaqAction L N (Φ L μ W) := h1
  simp only [bondW, prod_tr]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div]
  linear_combination h1' / 2

theorem cast_rot {a b : ℕ} (h : a = b) (t : Fin a) :
    finCongr h (finRotate a t) = finRotate b (finCongr h t) := by
  subst h; rfl

/-! ## The cycle of circumference `T` -/

variable {m : ℕ}

theorem plaqAction_chain (hN : N ≠ 0) (hm : L μ = m + 1) (Y : Fin (m + 1) → SlIdx L μ → SUN.SU N) :
    plaqAction L N (Φ L μ fun t => Y (finCongr hm t)) = PurityTwoLift.chain (bondW μ (tr L μ)) Y := by
  rw [plaqAction_Φ hN, ← (finCongr hm).symm.sum_comp]
  unfold PurityTwoLift.chain
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [cast_rot, Equiv.apply_symm_apply]
  simp only [finRotate_apply]

/-! ## The cycle of circumference `2T` -/

/-- Slice `x + (m+1)[e]` of the cycle of circumference `2(m+1)`. -/
def toK (s : Fin (m + 1) × Bool) : Fin (2 * m + 1 + 1) :=
  ⟨s.1 + if s.2 then m + 1 else 0, by have := s.1.isLt; split <;> omega⟩

/-- The inverse of `toK`. -/
def ofK (t : Fin (2 * m + 1 + 1)) : Fin (m + 1) × Bool :=
  if h : (t : ℕ) < m + 1 then (⟨t, h⟩, false) else (⟨t - (m + 1), by have := t.isLt; omega⟩, true)

/-- The slices of the cycle of circumference `2(m+1)` as the sheets over the cycle of
circumference `m+1`. -/
def kEquiv : Fin (m + 1) × Bool ≃ Fin (2 * m + 1 + 1) where
  toFun := toK
  invFun := ofK
  left_inv s := by
    obtain ⟨⟨x, hx⟩, e⟩ := s
    cases e
    · simp [toK, ofK, hx]
    · have : ¬ x + (m + 1) < m + 1 := by omega
      simp [toK, ofK, this]
  right_inv t := by
    obtain ⟨t, ht⟩ := t
    unfold ofK
    split_ifs with h
    · simp [toK]
    · apply Fin.ext
      dsimp only at h
      simp [toK]
      omega

/-- The step `t ↦ t+1` of the cycle of circumference `2(m+1)` is the step of the connected double
cover. -/
theorem kEquiv_walk (s : Fin (m + 1) × Bool) :
    kEquiv.symm (kEquiv s + 1) = (s.1 + 1, xor s.2 (PurityTwoLift.flip s.1)) := by
  apply kEquiv.injective
  rw [Equiv.apply_symm_apply]
  obtain ⟨⟨x, hx⟩, e⟩ := s
  apply Fin.ext
  rw [Fin.val_add_one]
  simp only [kEquiv, Equiv.coe_fn_mk, toK, PurityTwoLift.flip, Fin.ext_iff, Fin.val_last,
    Fin.val_add_one]
  by_cases h : x = m <;> cases e <;> simp [h] <;> (try split_ifs) <;> omega

variable {E : Type*}

/-- The `2(m+1)` slice variables of a configuration on the double cover. -/
def sheets (Z : Fin (m + 1) → E × E) (s : Fin (m + 1) × Bool) : E := PurityTwoLift.get (Z s.1) s.2

theorem plaqAction_cover (hN : N ≠ 0) (hm₂ : L μ = 2 * m + 1 + 1)
    (Z : Fin (m + 1) → (SlIdx L μ → SUN.SU N) × (SlIdx L μ → SUN.SU N)) :
    plaqAction L N (Φ L μ fun t => sheets Z (kEquiv.symm (finCongr hm₂ t)))
      = PurityTwoLift.cover (bondW μ (tr L μ)) Z := by
  rw [plaqAction_Φ hN, ← (kEquiv.trans (finCongr hm₂).symm).sum_comp]
  unfold PurityTwoLift.cover PurityTwoLift.coverBond
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Equiv.trans_apply, cast_rot, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  simp only [finRotate_apply, kEquiv_walk, sheets]

/-! ## The measures -/

/-- Reindexing the links by an equivalence preserves the product measure: Mathlib's
`measurePreserving_arrowCongr'` for a constant family, in the composition form used below. -/
theorem measurePreserving_reindex {α β X : Type*} [Fintype α] [Fintype β] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (e : α ≃ β) :
    MeasurePreserving (fun (f : α → X) (b : β) => f (e.symm b))
      (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
  measurePreserving_arrowCongr' (fun _ => ν) (fun _ => ν) e (MeasurableEquiv.refl X)
    fun _ => MeasurePreserving.id _

theorem measurePreserving_sheets [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] :
    MeasurePreserving (sheets (E := E) (m := m)) (Measure.pi fun _ => ν.prod ν)
      (Measure.pi fun _ => ν) := by
  have hmeas : Measurable (sheets (E := E) (m := m)) :=
    measurable_pi_lambda _ fun s => PurityTwoLift.measurable_get (E := E) s.1 s.2
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : sheets ⁻¹' Set.univ.pi s = Set.univ.pi fun x => s (x, false) ×ˢ s (x, true) := by
    ext Z
    simp [sheets, PurityTwoLift.get, Prod.forall, Bool.forall_bool]
  rw [hpre, Measure.pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun x _ => by rw [Measure.prod_prod, Fintype.prod_bool, mul_comm]

/-- The complex MGF of `A ∘ f` under `μa` equals that of `A` under `μb` when `f` carries `μa` to
`μb`: Mathlib's `complexMGF_id_map` on both sides of `μb = μa.map f`. -/
theorem complexMGF_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α}
    {μb : Measure β} {f : α → β} (hf : MeasurePreserving f μa μb) {A : β → ℝ} (hA : Measurable A)
    (z : ℂ) : complexMGF (fun a => A (f a)) μa z = complexMGF A μb z := by
  change complexMGF (A ∘ f) μa z = _
  rw [← complexMGF_id_map (hA.comp hf.measurable).aemeasurable, ← Measure.map_map hA hf.measurable,
    hf.map_eq, complexMGF_id_map hA.aemeasurable]

theorem complexMGF_chain (hN : N ≠ 0) (hm : L μ = m + 1) (z : ℂ) :
    complexMGF (plaqAction L N) (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) z
      = complexMGF (PurityTwoLift.chain (bondW μ (tr L μ)))
        (Measure.pi fun _ : Fin (m + 1) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)) z := by
  have hmp : MeasurePreserving
      (fun Y : Fin (m + 1) → SlIdx L μ → SUN.SU N => Φ L μ fun t => Y (finCongr hm t))
      (Measure.pi fun _ : Fin (m + 1) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) :=
    (measurePreserving_Φ N).comp (measurePreserving_reindex _ (finCongr hm).symm)
  have hf : (fun Y : Fin (m + 1) → SlIdx L μ → SUN.SU N => plaqAction L N (Φ L μ fun t => Y (finCongr hm t)))
      = PurityTwoLift.chain (bondW μ (tr L μ)) := funext fun Y => plaqAction_chain hN hm Y
  rw [← hf]
  exact (complexMGF_comp hmp (measurable_plaqAction N) z).symm

theorem complexMGF_cover (hN : N ≠ 0) (hm₂ : L μ = 2 * m + 1 + 1) (z : ℂ) :
    complexMGF (plaqAction L N) (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) z
      = complexMGF (PurityTwoLift.cover (bondW μ (tr L μ)))
        (Measure.pi fun _ : Fin (m + 1) => (Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)).prod
          (Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))) z := by
  have hmp : MeasurePreserving
      (fun Z : Fin (m + 1) → (SlIdx L μ → SUN.SU N) × (SlIdx L μ → SUN.SU N) =>
        Φ L μ fun t => sheets Z (kEquiv.symm (finCongr hm₂ t)))
      (Measure.pi fun _ : Fin (m + 1) => (Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)).prod
          (Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) :=
    (measurePreserving_Φ N).comp ((measurePreserving_reindex _ (kEquiv.trans (finCongr hm₂).symm)).comp
      (measurePreserving_sheets _))
  have hf : (fun Z : Fin (m + 1) → (SlIdx L μ → SUN.SU N) × (SlIdx L μ → SUN.SU N) =>
        plaqAction L N (Φ L μ fun t => sheets Z (kEquiv.symm (finCongr hm₂ t))))
      = PurityTwoLift.cover (bondW μ (tr L μ)) := funext fun Z => plaqAction_cover hN hm₂ Z
  rw [← hf]
  exact (complexMGF_comp hmp (measurable_plaqAction N) z).symm

/-- `complexMGF_cover` with the transverse extents of `L` given as `T`. -/
theorem complexMGF_cover_tr (hN : N ≠ 0) (hm₂ : L μ = 2 * m + 1 + 1)
    {T : {j : Fin 4 // j ≠ μ} → ℕ} (hT : tr L μ = T) (z : ℂ) :
    complexMGF (plaqAction L N) (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) z
      = complexMGF (PurityTwoLift.cover (bondW μ T))
        (Measure.pi fun _ : Fin (m + 1) => (Measure.pi fun _ : TT μ T ⊕ SpT μ T => probHaar (SUN.SU N)).prod
          (Measure.pi fun _ : TT μ T ⊕ SpT μ T => probHaar (SUN.SU N))) z := by
  subst hT
  exact complexMGF_cover hN hm₂ z

/-! ## (8.1) and Corollary 8.2 -/

/-- (8.1) for the Wilson plaquette action with product Haar measure: the derivatives of
`2 log Z_T − log Z_{2T}` of order `< T = L₁ μ` vanish at `0`, `L₂` being `L₁` with the extent in
direction `μ` doubled. -/
theorem hvan_wilson (hN : N ≠ 0) {L₁ L₂ : Fin 4 → ℕ} (μ : Fin 4)
    (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ) :
    ∀ n < L₁ μ, iteratedDeriv n (PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N)) 0 = 0 := by
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, L₁ μ = m + 1 := ⟨L₁ μ - 1, by omega⟩
  have hm₂ : L₂ μ = 2 * m + 1 + 1 := by omega
  have hT : tr L₂ μ = tr L₁ μ := funext fun j => hL j.1 j.2
  have key : PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N)
      = PurityCancel.psi
        (Measure.pi fun _ : Fin (m + 1) => Measure.pi fun _ : SlIdx L₁ μ => probHaar (SUN.SU N))
        (PurityTwoLift.chain (bondW μ (tr L₁ μ)))
        (Measure.pi fun _ : Fin (m + 1) =>
          (Measure.pi fun _ : SlIdx L₁ μ => probHaar (SUN.SU N)).prod
            (Measure.pi fun _ : SlIdx L₁ μ => probHaar (SUN.SU N)))
        (PurityTwoLift.cover (bondW μ (tr L₁ μ))) := by
    funext z
    unfold PurityCancel.psi
    rw [complexMGF_chain hN hm z, complexMGF_cover_tr hN hm₂ hT z]
  rw [key]
  exact PurityTwoLift.hvan_cover _ measurable_bondW (abs_bondW_le hN) n (by omega)

/-- Corollary 8.2 for the Wilson plaquette action with product Haar measure:
`|Ψ_T(x)| ≤ V/(161(48T)³)` for `T = L₁ μ ≥ 3`, `(2T)³ ≤ V < (48T)³` and
`0 ≤ x ≤ log(3/2)/(12000·48³ T⁴)`, `L₂` being `L₁` with the extent in direction `μ` doubled. -/
theorem corollary_window_wilson (hN : N ≠ 0) {L₁ L₂ : Fin 4 → ℕ} (μ : Fin 4)
    (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ) {x : ℝ} (hT : 3 ≤ L₁ μ)
    (hVlo : (2 * L₁ μ : ℝ) ^ 3 ≤ ∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ))
    (hVhi : ∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ) < (48 * L₁ μ : ℝ) ^ 3)
    (hx0 : 0 ≤ x) (hx : x ≤ Real.log (3 / 2) / (12000 * 48 ^ 3 * (L₁ μ : ℝ) ^ 4)) :
    ‖PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N) x‖
      ≤ (∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ)) / (161 * (48 * L₁ μ) ^ 3) :=
  PurityPlaqCount.corollary_window_wilson μ hL h2 hT hVlo hVhi (hvan_wilson hN μ hL h2) hx0 hx

#print axioms plaqAction_Φ
#print axioms plaqAction_chain
#print axioms kEquiv_walk
#print axioms plaqAction_cover
#print axioms measurePreserving_sheets
#print axioms complexMGF_chain
#print axioms complexMGF_cover
#print axioms hvan_wilson
#print axioms corollary_window_wilson

end MassGap.PurityWilsonChain
