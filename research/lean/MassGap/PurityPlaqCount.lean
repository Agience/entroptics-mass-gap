import MassGap.RectWilson
import MassGap.PurityCancel
import MassGap.DoublingWilson

/-!
# MassGap.PurityPlaqCount — the plaquette action `A_t` of §8 of the purity paper on the 4-torus

The action `A_t = (1/d) Σ_p Re Tr U_p` of §8 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood,
T. Romanov, I. J. Sessford and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak
Coupling* (research draft, 15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit
8e01510, `Paper-2/Paper-2.pdf`), at `G = SU(N)`, `d = N`, on the rectangular 4-torus of
`RectWilson` with extents `L`. A plaquette `p` is a pair of directions `i < j` and a site, and `U_p`
is the holonomy of `RectWilson.sysR` around it.

* `dirs`: the six direction pairs `i < j`; `plaqs L = dirs ×ˢ univ`.
* `card_plaqs`: there are `6 ∏_i L_i` plaquettes.
* `plaqAction L N U = Σ_{p ∈ plaqs L} (1/N) Re Tr U_p`.
* `abs_plaqAction_le`: `|A| ≤ 6 ∏_i L_i`, from `|Re Tr g| ≤ N`.
* `action_eq`: `S(U) = 12 ∏_i L_i − 2 A(U)` for `N ≠ 0`, `S` the action of `sysR` (ordered pairs
  with the diagonal: `U_{ii} = 1` and `U_{ji} = U_{ij}⁻¹`). The paper's coupling `βW`, the
  coefficient of `A_t`, is `2β` for `RectWilson.ZR L N β = ∫ e^{−β S}` (`psi_eq_log_ZR`).
* `abs_plaqAction_le_slab`: `|A| ≤ 6 V t` with `t = L_μ` and `V = ∏_{i ≠ μ} L_i`.
* `measurable_plaqAction`.
* `corollary_window_wilson`: the bound `|Ψ_T(x)| ≤ V/(161(48T)³)` of `PurityCancel.corollary_window` with `μ_t` the product Haar measure
  on the links of `L₁` and of `L₂`, `L₂` being `L₁` with the extent in direction `μ` doubled, and
  `A_t` the plaquette action; the bounds `|A_T| ≤ 6VT`, `|A_{2T}| ≤ 12VT` and the measurability
  are discharged here, (8.1) is the hypothesis `hvan` (discharged in
  `PurityWilsonChain.corollary_window_wilson`). The window enters through
  `(2T)³ ≤ V < (48T)³`.
* `integrable_exp`: `e^{tA}` is integrable for product Haar.
* `ZR_eq`: `Z(β) = e^{−12β ∏_i L_i} E[e^{2βA}]`, `Z = RectWilson.ZR`.
* `psi_eq_log_ZR`: `Ψ_T(2β) = 2 log Z_{L₁}(β) − log Z_{L₂}(β)`.
* `log_ZR_double_nonneg`, `psi_nonneg_wilson`: `Ψ_T(2β) ≥ 0` at even `T`, `β ≥ 0`, the lower
  bound of Corollary 8.2, from the transfer-kernel trace facts (`DoublingWilson.facts`).

DERIVED (module-wide): `4` the dimension; `6 = C(4, 2)` the planes; `12 = 2 · 6`, the two
orientations of each plane in `sysR`, and the doubled circumference.
-/

namespace MassGap.PurityPlaqCount

open MeasureTheory MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge
  MassGap.RectWilson

/-- The six direction pairs `i < j`. -/
def dirs : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun ij => ij.1 < ij.2

theorem card_dirs : dirs.card = 6 := by decide

variable (L : Fin 4 → ℕ)

/-- The unoriented plaquettes: a pair `i < j` and a site. -/
def plaqs : Finset (RPlaq L) := dirs ×ˢ Finset.univ

theorem card_plaqs : (plaqs L).card = 6 * ∏ i, L i := by
  rw [plaqs, Finset.card_product, card_dirs, Finset.card_univ, Fintype.card_pi]
  simp

/-- `A(U) = Σ_p (1/N) Re Tr U_p`. -/
noncomputable def plaqAction (N : ℕ) (U : RLink L → SUN.SU N) : ℝ :=
  ∑ q ∈ plaqs L, 1 / (N : ℝ) * (Matrix.trace ((sysR L N).hol q U : Matrix (Fin N) (Fin N) ℂ)).re

variable {L}

theorem term_eq {N : ℕ} (g : SUN.SU N) :
    1 / (N : ℝ) * (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re
      = 1 - WilsonAction.wilsonDensity g := by
  unfold WilsonAction.wilsonDensity; ring

theorem abs_term_le {N : ℕ} (g : SUN.SU N) :
    |1 / (N : ℝ) * (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / N)]
  calc 1 / (N : ℝ) * |(Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re|
      ≤ 1 / (N : ℝ) * N := mul_le_mul_of_nonneg_left (WilsonAction.abs_re_trace_le g) (by positivity)
    _ ≤ 1 := by
        by_cases hN : (N : ℝ) = 0
        · simp [hN]
        · rw [one_div_mul_cancel hN]

theorem abs_plaqAction_le {N : ℕ} (U : RLink L → SUN.SU N) :
    |plaqAction L N U| ≤ 6 * ∏ i, (L i : ℝ) := by
  calc |plaqAction L N U|
      ≤ ∑ q ∈ plaqs L, |1 / (N : ℝ)
          * (Matrix.trace ((sysR L N).hol q U : Matrix (Fin N) (Fin N) ℂ)).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ plaqs L, (1 : ℝ) := Finset.sum_le_sum fun q _ => abs_term_le _
    _ = 6 * ∏ i, (L i : ℝ) := by
        rw [Finset.sum_const, card_plaqs, nsmul_eq_mul, mul_one]; push_cast; ring

/-- A function on ordered direction pairs, zero on the diagonal and symmetric, sums to twice its sum
over `i < j`. -/
theorem sum_pairs {g : Fin 4 × Fin 4 → ℝ} (hd : ∀ i, g (i, i) = 0) (hs : ∀ i j, g (j, i) = g (i, j)) :
    ∑ ij, g ij = 2 * ∑ ij ∈ dirs, g ij := by
  have h : dirs = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  rw [h, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  linarith [hd 0, hd 1, hd 2, hd 3, hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]

theorem hol_swap {N : ℕ} (U : RLink L → SUN.SU N) (i j : Fin 4) (x : RSite L) :
    (sysR L N).hol ((j, i), x) U = ((sysR L N).hol ((i, j), x) U)⁻¹ := by
  rw [hol_eq, hol_eq]; group

/-- `S(U) = 12 ∏_i L_i − 2 A(U)`. -/
theorem action_eq {N : ℕ} (hN : N ≠ 0) (U : RLink L → SUN.SU N) :
    (sysR L N).action U = 12 * ∏ i, (L i : ℝ) - 2 * plaqAction L N U := by
  have hS : (sysR L N).action U
      = ∑ ij : Fin 4 × Fin 4, ∑ x : RSite L, WilsonAction.wilsonDensity ((sysR L N).hol (ij, x) U) := by
    show ∑ q : RPlaq L, WilsonAction.wilsonDensity ((sysR L N).hol q U) = _
    exact Fintype.sum_prod_type _
  have hA : plaqAction L N U
      = ∑ ij ∈ dirs, ∑ x : RSite L, (1 - WilsonAction.wilsonDensity ((sysR L N).hol (ij, x) U)) := by
    rw [plaqAction, plaqs, Finset.sum_product]
    simp only [term_eq]
  rw [hS, sum_pairs (g := fun ij => ∑ x : RSite L,
      WilsonAction.wilsonDensity ((sysR L N).hol (ij, x) U)), hA]
  · simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
      Fintype.card_fin, card_dirs, nsmul_eq_mul]
    push_cast; ring
  · intro i
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [hol_eq, show U (i, x) * U (i, rshift L i x) * (U (i, rshift L i x))⁻¹ * (U (i, x))⁻¹ = 1 by
      group]
    exact WilsonAction.wilsonDensity_one hN
  · intro i j
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hol_swap, wilsonDensity_inv]

theorem measurable_plaqAction (N : ℕ) : Measurable (plaqAction L N) := by
  refine Finset.measurable_sum _ fun q _ => ?_
  simp only [term_eq]
  exact measurable_const.sub
    (WilsonAction.measurable_wilsonDensity.comp (measurable_wilsonHol (rbd L) q))

theorem prod_eq (μ : Fin 4) : ∏ i, (L i : ℝ) = (∏ i ∈ Finset.univ.erase μ, (L i : ℝ)) * L μ :=
  (Finset.prod_erase_mul _ _ (Finset.mem_univ μ)).symm

/-- `|A_t| ≤ 6 V t` with `t = L_μ`, `V = ∏_{i ≠ μ} L_i`. -/
theorem abs_plaqAction_le_slab {N : ℕ} (μ : Fin 4) (U : RLink L → SUN.SU N) :
    |plaqAction L N U| ≤ 6 * (∏ i ∈ Finset.univ.erase μ, (L i : ℝ)) * L μ := by
  rw [mul_assoc, ← prod_eq]; exact abs_plaqAction_le U

/-- The bound `|Ψ_T(x)| ≤ V/(161(48T)³)` of Corollary 8.2 with `μ_t` the product Haar measure on the links and `A_t` the plaquette action,
`L₂` being `L₁` with the extent in direction `μ` doubled; (8.1) is `hvan`
(`PurityWilsonChain.hvan_wilson`). -/
theorem corollary_window_wilson {N : ℕ} {L₁ L₂ : Fin 4 → ℕ} (μ : Fin 4)
    (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ) {x : ℝ} (hT : 3 ≤ L₁ μ)
    (hVlo : (2 * L₁ μ : ℝ) ^ 3 ≤ ∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ))
    (hVhi : ∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ) < (48 * L₁ μ : ℝ) ^ 3)
    (hvan : ∀ n < L₁ μ, iteratedDeriv n (PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N)) 0 = 0)
    (hx0 : 0 ≤ x) (hx : x ≤ Real.log (3 / 2) / (12000 * 48 ^ 3 * (L₁ μ : ℝ) ^ 4)) :
    ‖PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N) x‖
      ≤ (∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ)) / (161 * (48 * L₁ μ) ^ 3) := by
  have hV : ∏ i ∈ Finset.univ.erase μ, (L₂ i : ℝ) = ∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ) :=
    Finset.prod_congr rfl fun i hi => by rw [hL i (Finset.ne_of_mem_erase hi)]
  refine PurityCancel.corollary_window hT hVlo hVhi (measurable_plaqAction N).aemeasurable
    (measurable_plaqAction N).aemeasurable
    (ae_of_all _ fun U => abs_plaqAction_le_slab μ U)
    (ae_of_all _ fun U => ?_) hvan hx0 hx
  have h := abs_plaqAction_le_slab (L := L₂) μ U
  rw [hV, h2] at h
  push_cast at h
  linarith

/-- `e^{tA}` is integrable for product Haar: `|A| ≤ 6 ∏_i L_i`. -/
theorem integrable_exp {N : ℕ} (t : ℝ) :
    Integrable (fun U => Real.exp (t * plaqAction L N U))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  refine Integrable.of_bound ((measurable_plaqAction (L := L) N).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * (6 * ∏ i, (L i : ℝ)))) (ae_of_all _ fun U => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  calc t * plaqAction L N U ≤ |t * plaqAction L N U| := le_abs_self _
    _ = |t| * |plaqAction L N U| := abs_mul _ _
    _ ≤ |t| * (6 * ∏ i, (L i : ℝ)) :=
        mul_le_mul_of_nonneg_left (abs_plaqAction_le (L := L) U) (abs_nonneg t)

/-- `Z(β) = e^{−12β ∏_i L_i} E[e^{2βA}]` for `N ≠ 0`. -/
theorem ZR_eq {N : ℕ} (hN : N ≠ 0) (β : ℝ) :
    ZR L N β = Real.exp (-(12 * β * ∏ i, (L i : ℝ)))
      * ProbabilityTheory.mgf (plaqAction L N)
          (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) (2 * β) := by
  rw [ZR, System.partition, System.vol, ProbabilityTheory.mgf, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [System.boltz]
  rw [action_eq (L := L) hN, ← Real.exp_add]
  congr 1
  ring

/-- `Ψ_T(2β) = 2 log Z_{L₁}(β) − log Z_{L₂}(β)`, `L₂` being `L₁` with `L_μ` doubled: the paper's
`βW` is `2β`, and the four-volume term cancels. -/
theorem psi_eq_log_ZR {N : ℕ} (hN : N ≠ 0) {L₁ L₂ : Fin 4 → ℕ} (μ : Fin 4)
    (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ) (β : ℝ) :
    PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N) ((2 * β : ℝ) : ℂ)
      = ((2 * Real.log (ZR L₁ N β) - Real.log (ZR L₂ N β) : ℝ) : ℂ) := by
  have hV' : ∏ i ∈ Finset.univ.erase μ, (L₂ i : ℝ) = ∏ i ∈ Finset.univ.erase μ, (L₁ i : ℝ) :=
    Finset.prod_congr rfl fun i hi => by rw [hL i (Finset.ne_of_mem_erase hi)]
  have hV : ∏ i, (L₂ i : ℝ) = 2 * ∏ i, (L₁ i : ℝ) := by
    rw [prod_eq (L := L₂) μ, prod_eq (L := L₁) μ, hV', h2]
    push_cast
    ring
  have hm₁ := ProbabilityTheory.mgf_pos (integrable_exp (L := L₁) (N := N) (2 * β))
  have hm₂ := ProbabilityTheory.mgf_pos (integrable_exp (L := L₂) (N := N) (2 * β))
  rw [PurityCancel.psi, ProbabilityTheory.complexMGF_ofReal, ProbabilityTheory.complexMGF_ofReal,
    ← Complex.ofReal_log hm₁.le, ← Complex.ofReal_log hm₂.le, ZR_eq (L := L₁) hN,
    ZR_eq (L := L₂) hN, Real.log_mul (Real.exp_pos _).ne' hm₁.ne',
    Real.log_mul (Real.exp_pos _).ne' hm₂.ne', Real.log_exp, Real.log_exp, hV]
  push_cast
  ring

/-- `2 log Z_{L₁}(β) − log Z_{L₂}(β) ≥ 0` for `L₁ μ = 2j`, `L₂` being `L₁` with `L_μ` doubled,
`β ≥ 0`: `Z` is the trace sequence of the transfer kernel (`RectTransfer.ZR_eq_traceSeq`), whose
trace facts (`DoublingWilson.facts`) give `DoublingPower.defect_nonneg`. -/
theorem log_ZR_double_nonneg {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L₁ L₂ : Fin 4 → ℕ}
    (μ : Fin 4) (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ) (j : ℕ) (hj : 1 ≤ j)
    (hT : L₁ μ = 2 * j) :
    0 ≤ 2 * Real.log (ZR L₁ N β) - Real.log (ZR L₂ N β) := by
  have htr : RectWilson.tr L₂ μ = RectWilson.tr L₁ μ := funext fun i => hL i.1 i.2
  have hT2 : L₂ μ = 2 * (2 * j) := by rw [h2, hT]
  obtain ⟨lam, s, h⟩ := DoublingWilson.facts hN hβ μ (RectWilson.tr L₁ μ) j hj
  have d := DoublingPower.defect_nonneg h
  unfold DoublingPower.defect DoublingWilson.F at d
  rw [RectTransfer.ZR_eq_traceSeq (μ := μ) (L := L₁) hN hβ j hj hT,
    RectTransfer.ZR_eq_traceSeq (μ := μ) (L := L₂) hN hβ (2 * j) (by omega) hT2, htr, hT, hT2]
  exact d

/-- The lower bound `Ψ_T(2β) ≥ 0` of Corollary 8.2 on the Wilson lattice at even `T = L₁ μ`,
`β ≥ 0`: `Ψ_T(2β)` is real (`psi_eq_log_ZR`) and nonnegative (`log_ZR_double_nonneg`). -/
theorem psi_nonneg_wilson {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L₁ L₂ : Fin 4 → ℕ}
    (μ : Fin 4) (hL : ∀ i, i ≠ μ → L₂ i = L₁ i) (h2 : L₂ μ = 2 * L₁ μ) (j : ℕ) (hj : 1 ≤ j)
    (hT : L₁ μ = 2 * j) :
    0 ≤ (PurityCancel.psi
      (Measure.pi fun _ : RLink L₁ => probHaar (SUN.SU N)) (plaqAction L₁ N)
      (Measure.pi fun _ : RLink L₂ => probHaar (SUN.SU N)) (plaqAction L₂ N)
      ((2 * β : ℝ) : ℂ)).re := by
  rw [psi_eq_log_ZR hN μ hL h2 β, Complex.ofReal_re]
  exact log_ZR_double_nonneg hN hβ μ hL h2 j hj hT

end MassGap.PurityPlaqCount

#print axioms MassGap.PurityPlaqCount.card_plaqs
#print axioms MassGap.PurityPlaqCount.abs_plaqAction_le
#print axioms MassGap.PurityPlaqCount.action_eq
#print axioms MassGap.PurityPlaqCount.measurable_plaqAction
#print axioms MassGap.PurityPlaqCount.abs_plaqAction_le_slab
#print axioms MassGap.PurityPlaqCount.corollary_window_wilson
#print axioms MassGap.PurityPlaqCount.integrable_exp
#print axioms MassGap.PurityPlaqCount.ZR_eq
#print axioms MassGap.PurityPlaqCount.psi_eq_log_ZR
#print axioms MassGap.PurityPlaqCount.log_ZR_double_nonneg
#print axioms MassGap.PurityPlaqCount.psi_nonneg_wilson
