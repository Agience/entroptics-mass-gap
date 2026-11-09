import Mathlib
import MassGap.SU2DiskLaw
import MassGap.MovedTorusDecimation
import MassGap.ElectricStepChain
import MassGap.WilsonChainExists
import MassGap.HeatBathErgodic

/-!
# MassGap.ElectricExactProof — the electric half is exact on every flat Wilson chain

## What is proved

* **The chain on the group** (`P_eq`, `W_succ_eq`, `W_succ_eq_K4`). With `w_k = W_k(τ ·)⁴`, at every `g ∈ SU(2)`:
  - `P_k(τ g) = μ_k π (w_k ⋆ w_k)(g)`;
  - `W_{k+1}(τ g) = ν_k π (μ_k π)² ((w_k ⋆ w_k) ⋆ (w_k ⋆ w_k))(g)`.

  The two sides agree where `τ g ∈ (−1, 1)` (`SU2DiskLaw.convT_eq_pi_conv`). Both are continuous, so they agree
  everywhere (`eq_of_eq_on_Ioo`). `W_pos`: every `W_k > 0` on `[−1, 1]`.
* `fAct_moved`: on the side-`2n` torus, for an inverse-invariant density `h`,
  `fAct (mkField h) U = 64 n⁴ h(1) + Σ_X Σ_p 8 Σ_{a,b} h(hol_{p, 2X + a eᵢ + b eⱼ})`.
* `Zmk_eq`: `Zmk C i (2n) = e^{−64 n⁴ h_i(1)} J_i(n)`.
* `Zh_eq`: `Zh C (i+1) n = e^{−4 n⁴ h_{i+1}(1)} (ν_i π (μ_i π)²)^{6n⁴} J_i(n)`.
  - `J_i(n) = ∫ ∏_{X,p} K4(hol) > 0` on the side-`n` torus (`Jc_pos`), and `h_k = halfField W_k τ`.
  - The two integrals are equal by `MovedTorusDecimation.decimation`.
* **`electricExact`**: `ElectricExact C i` for every `WilsonChain C` and every `i`, with
  `κ = −64 h_i(1) + 4 h_{i+1}(1) − 6 log(ν_i π (μ_i π)²)`.
* `electricExact_wilsonChainOf`: `∀ β i, ElectricExact (wilsonChainOf (2β)) i`.

## What is open

`MagneticSlack` on the constructed chain, frequently in `β`. Nothing here bounds the Hölder excess.

## Controls

The decimation holds for every compact group (`decimation`). The `SU(2)` content is the Weyl formula
(`convT_eq_pi_conv`), which carries the chain's radial step to the group convolution. Its constant `π`, one per group
convolution and three per coarse plaquette, enters only `κ`. Under `ElectricExact`, `HalfStep` and `MagneticStep` are
equivalent, so the reduction to `MagneticSlack` changes no truth value: a false half step is a false magnetic step.

DERIVED (module-wide):
- `64 = 4 · 2 · 2³`: four directions, two surviving parities per diagonal pair and coarse site, and the weight `2³`.
- `8 = 2 · 2²`: the two orders of a plaquette, times the weight `2^{d−2}` of a surviving one.
- `6` the planes `i < j`; `4 n⁴` the tree's diagonal count (`fAct_halfField_suTau`); `π` one per group convolution.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.ElectricExactProof

open MeasureTheory Set Real Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ConvolutionTransfer MassGap.ChainCoarseSeed
  MassGap.ChainFirstCrossing MassGap.ElectricStep MassGap.ElectricStepChain
  MassGap.SU2DiskLaw MassGap.MovedTorusDecimation

/-! ## 1. Convolutions of non-negative and positive functions -/

section Conv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [SecondCountableTopology G] in
theorem conv_nonneg {u v : G → ℝ} (hu : ∀ g, 0 ≤ u g) (hv : ∀ g, 0 ≤ v g) (g : G) :
    0 ≤ conv u v g :=
  integral_nonneg fun h => mul_nonneg (hu h) (hv _)

omit [SecondCountableTopology G] in
theorem conv_pos {u v : G → ℝ} (hu : Continuous u) (hv : Continuous v) (hu0 : ∀ g, 0 < u g)
    (hv0 : ∀ g, 0 < v g) (g : G) : 0 < conv u v g := by
  unfold conv
  have hc : Continuous fun h => u h * v (h⁻¹ * g) := hu.mul (hv.comp (continuous_inv.mul continuous_const))
  rw [integral_pos_iff_support_of_nonneg (fun h => (mul_pos (hu0 h) (hv0 _)).le)
    (integrable_of_continuous hc)]
  have : Function.support (fun h => u h * v (h⁻¹ * g)) = univ :=
    Set.eq_univ_of_forall fun h => (mul_pos (hu0 h) (hv0 _)).ne'
  rw [this, measure_univ]
  exact one_pos

omit [SecondCountableTopology G] in
theorem conv_smul (a b : ℝ) (u v : G → ℝ) (g : G) :
    conv (fun x => a * u x) (fun x => b * v x) g = a * b * conv u v g := by
  unfold conv
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  ring

end Conv

/-! ## 2. The chain on `SU(2)`: the radial step is the group step -/

section Chain

variable {β : ℝ} (C : WilsonChain β)

theorem suTau_conj (k x : SU 2) : suTau (k * x * k⁻¹) = suTau x := by
  unfold suTau; rw [WilsonAction.wilsonDensity_conj]

theorem continuous_W : ∀ k, Continuous (C.W k)
  | 0 => by rw [C.hW0]; fun_prop
  | k + 1 => C.hWc k

/-- **The plaquette weight of the power step**, `g ↦ W_k(½ Re tr g)⁴`. -/
def wk (k : ℕ) (g : SU 2) : ℝ := C.W k (suTau g) ^ 4

theorem continuous_wk (k : ℕ) : Continuous (wk C k) :=
  ((continuous_W C k).comp continuous_suTau).pow 4

theorem wk_nonneg (k : ℕ) (g : SU 2) : 0 ≤ wk C k g :=
  Even.pow_nonneg (by decide) _

theorem wk_class (k : ℕ) (x y : SU 2) : wk C k (x * y * x⁻¹) = wk C k y := by
  unfold wk; rw [suTau_conj]

/-- **The first convolution on the group.** `P_k(τ g) = μ_k π (w_k ⋆ w_k)(g)` at every `g`. -/
theorem P_eq (k : ℕ) (g : SU 2) : C.P k (suTau g) = C.μ k * π * conv (wk C k) (wk C k) g := by
  refine eq_of_eq_on_Ioo (F₁ := fun g => C.P k (suTau g))
    (F₂ := fun g => C.μ k * π * conv (wk C k) (wk C k) g)
    ((C.hPc k).comp continuous_suTau)
    (continuous_const.mul (continuous_conv (continuous_wk C k) (continuous_wk C k))) (fun g hg => ?_) g
  rw [C.hPeq k (suTau g) hg, convT_eq_pi_conv (fun t => C.W k t ^ 4)
    ((continuous_W C k).pow 4) (fun t _ => Even.pow_nonneg (by decide) _) g hg]
  rw [mul_assoc]
  rfl

theorem P_nonneg (k : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 0 ≤ C.P k t := by
  have hg : suTau (dmat (Real.arccos t)) = t := by rw [suTau_dmat, Real.cos_arccos ht.1 ht.2]
  rw [← hg, P_eq]
  exact mul_nonneg (mul_nonneg (C.hμ k).le pi_pos.le) (conv_nonneg (wk_nonneg C k) (wk_nonneg C k) _)

/-- **The second convolution on the group.** `W_{k+1}(τ g) = ν_k π (P_k ∘ τ ⋆ P_k ∘ τ)(g)`. -/
theorem W_succ_eq (k : ℕ) (g : SU 2) :
    C.W (k + 1) (suTau g) = C.ν k * π * conv (C.P k ∘ suTau) (C.P k ∘ suTau) g := by
  have hPτ : Continuous (C.P k ∘ suTau) := (C.hPc k).comp continuous_suTau
  refine eq_of_eq_on_Ioo (F₁ := fun g => C.W (k + 1) (suTau g))
    (F₂ := fun g => C.ν k * π * conv (C.P k ∘ suTau) (C.P k ∘ suTau) g)
    ((C.hWc k).comp continuous_suTau) (continuous_const.mul (continuous_conv hPτ hPτ))
    (fun g hg => ?_) g
  rw [C.hWeq k (suTau g) hg, convT_eq_pi_conv (C.P k) (C.hPc k) (fun t ht => P_nonneg C k ht) g hg,
    mul_assoc]

/-- **The step on the group**: `W_{k+1}(τ g) = ν_k π (μ_k π)² ((w_k ⋆ w_k) ⋆ (w_k ⋆ w_k))(g)`. -/
theorem W_succ_eq_K4 (k : ℕ) (g : SU 2) :
    C.W (k + 1) (suTau g) = C.ν k * π * (C.μ k * π) ^ 2
      * conv (conv (wk C k) (wk C k)) (conv (wk C k) (wk C k)) g := by
  rw [W_succ_eq]
  have hP : C.P k ∘ suTau = fun g => (C.μ k * π) * conv (wk C k) (wk C k) g := by
    funext g; exact P_eq C k g
  rw [hP, conv_smul]
  ring

/-- **The chain weights are positive** on `[−1, 1]`. -/
theorem W_pos : ∀ k, ∀ t ∈ Icc (-1 : ℝ) 1, 0 < C.W k t
  | 0, t, _ => by rw [C.hW0]; exact Real.exp_pos _
  | k + 1, t, ht => by
    have hg : suTau (dmat (Real.arccos t)) = t := by rw [suTau_dmat, Real.cos_arccos ht.1 ht.2]
    rw [← hg, W_succ_eq_K4]
    have hw : ∀ g, 0 < wk C k g := fun g => pow_pos (W_pos k _ (suTau_mem g)) 4
    have hw2 : ∀ g, 0 < conv (wk C k) (wk C k) g :=
      conv_pos (continuous_wk C k) (continuous_wk C k) hw hw
    have hc2 := continuous_conv (continuous_wk C k) (continuous_wk C k)
    have := conv_pos hc2 hc2 hw2 hw2 (dmat (Real.arccos t))
    have hμ := C.hμ k
    have hν := C.hν k
    positivity

end Chain

/-! ## 3. The moved action, block by block -/

section Action

variable {N : ℕ}

theorem mkField_unif (h : SU 2 → ℝ) (q : TPlaq 4 N) (g : SU 2) :
    mkField (uniformField (d := 4) (n := N) h) q g
      = if Survives q then 2 ^ (Finset.univ.filter fun κ : Fin 4 => ¬ inK κ q).card * h g else 0 := by
  unfold mkField
  rw [moveIter_eq _ _ 4 le_rfl]
  simp only [Finset.mem_univ, true_implies, Fin.is_lt, true_and]
  rfl

theorem mkField_unif_swap (h : SU 2 → ℝ) (i j : Fin 4) (x : TSite 4 N) (g : SU 2) :
    mkField (uniformField (d := 4) (n := N) h) ((j, i), x) g
      = mkField (uniformField (d := 4) (n := N) h) ((i, j), x) g := by
  rw [mkField_unif, mkField_unif]
  simp only [Survives, inK, evenAt, or_comm]

theorem card_diag (i : Fin 4) (x : TSite 4 N) :
    (Finset.univ.filter fun κ : Fin 4 => ¬ inK κ (((i, i), x) : TPlaq 4 N)).card = 3 := by
  unfold inK
  simp only [or_self]
  revert i
  decide

variable {n : ℕ}

theorem survives_emb (i j : Fin 4) (X : TSite 4 n) (ε : Fin 4 → Fin 2) :
    Survives (((i, j), emb X ε) : TPlaq 4 (2 * n)) ↔ ∀ κ, ¬ (i = κ ∨ j = κ) → ε κ = 0 := by
  unfold Survives inK evenAt
  simp only [emb_even_iff]

/-- **The parities that survive in a plane** are the four `a eᵢ + b eⱼ`. -/
theorem sum_survive {i j : Fin 4} (hij : i ≠ j) (F : (Fin 4 → Fin 2) → ℝ) :
    ∑ ε : Fin 4 → Fin 2, (if ∀ κ, ¬ (i = κ ∨ j = κ) → ε κ = 0 then F ε else 0)
      = ∑ a : Fin 2, ∑ b : Fin 2, F (par i j a b) := by
  rw [← Finset.sum_filter, ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun ε => (ε i, ε j)) (fun ab => par i j ab.1 ab.2) (fun _ _ => Finset.mem_univ _)
    (fun ab _ => ?_) (fun ε hε => ?_) (fun ab _ => ?_) (fun ε hε => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro κ hκ
    push Not at hκ
    simp [par, Ne.symm hκ.1, Ne.symm hκ.2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hε
    funext κ
    by_cases h1 : κ = i
    · subst h1; simp [par]
    · by_cases h2 : κ = j
      · subst h2; simp [par, h1]
      · simp [par, h1, h2, hε κ (by push Not; exact ⟨Ne.symm h1, Ne.symm h2⟩)]
  · simp [par_i, par_j hij]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hε
    congr 1
    funext κ
    by_cases h1 : κ = i
    · subst h1; simp [par]
    · by_cases h2 : κ = j
      · subst h2; simp [par, h1]
      · simp [par, h1, h2, hε κ (by push Not; exact ⟨Ne.symm h1, Ne.symm h2⟩)]

/-- The diagonal pairs that survive: two parities for each direction. -/
theorem card_survive_diag (i : Fin 4) :
    (Finset.univ.filter fun ε : Fin 4 → Fin 2 => ∀ κ, ¬ (i = κ ∨ i = κ) → ε κ = 0).card = 2 := by
  revert i
  decide

/-- **The moved action in blocks.** On the side-`2n` torus, for an inverse-invariant density `h`,
`fAct (mkField h) U = 64 n⁴ h(1) + Σ_X Σ_p 8 Σ_{a,b} h(hol of the plaquette at 2X + a eᵢ + b eⱼ)`.
DERIVED: `64 n⁴ = 4 · 2n · n³ · 2³`, the surviving diagonal pairs times their weight `2³`; `8 = 2 · 2²`,
the two orders of a plaquette times the weight `2^{d−2}` of a surviving one. -/
theorem fAct_moved (h : SU 2 → ℝ) (hinv : ∀ g, h g⁻¹ = h g) (U : TLink 4 (2 * n) → SU 2) :
    fAct (mkField (uniformField (d := 4) (n := 2 * n) h)) U
      = (64 * (n : ℝ) ^ 4) * h 1 + ∑ X : TSite 4 n, ∑ p : Plane, 8 * ∑ a : Fin 2, ∑ b : Fin 2,
          h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b)) U) := by
  set Φ := mkField (uniformField (d := 4) (n := 2 * n) h) with hΦ
  unfold fAct
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hx : ∀ x : TSite 4 (2 * n), ∑ q : Fin 4 × Fin 4, Φ (q, x) (thol (q, x) U)
      = ∑ i : Fin 4, Φ ((i, i), x) 1
        + 2 * ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), Φ (q, x) (thol (q, x) U) := by
    intro x
    rw [sum_pairs_of_symm (fun q => Φ (q, x) (thol (q, x) U)) (fun i j => by
      show Φ ((j, i), x) (thol ((j, i), x) U) = Φ ((i, j), x) (thol ((i, j), x) U)
      rw [hΦ, mkField_unif_swap, thol_swap, mkField_unif, mkField_unif, hinv])]
    simp only [thol_diag]
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_add_distrib]
  congr 1
  · -- the diagonal pairs
    rw [sum_fine]
    have e : ∀ (X : TSite 4 n) (ε : Fin 4 → Fin 2), ∑ i : Fin 4, Φ ((i, i), emb X ε) 1
        = ∑ i : Fin 4, if (∀ κ, ¬ (i = κ ∨ i = κ) → ε κ = 0) then 8 * h 1 else 0 := by
      intro X ε
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΦ, mkField_unif, card_diag]
      simp only [survives_emb]
      norm_num
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4 → Fin 2))) (t := Finset.univ),
      ← Finset.sum_filter, Finset.sum_const, card_survive_diag]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, nsmul_eq_mul]
    push_cast
    ring
  · -- the pairs `i < j`
    have e1 : ∀ x : TSite 4 (2 * n),
        2 * ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), Φ (q, x) (thol (q, x) U)
        = ∑ p : Plane, 2 * Φ (p.1, x) (thol (p.1, x) U) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_subtype _ (by simp) (fun q => 2 * Φ (q, x) (thol (q, x) U))
    simp_rw [e1]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun (p : Plane) _ =>
      sum_fine (fun x => 2 * Φ (p.1, x) (thol (p.1, x) U))]
    have e2 : ∀ (p : Plane) (X : TSite 4 n), ∑ ε : Fin 4 → Fin 2,
        2 * Φ (p.1, emb X ε) (thol (p.1, emb X ε) U)
        = 8 * ∑ a : Fin 2, ∑ b : Fin 2, h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 a b)) U) := by
      intro p X
      have hne := plane_ne p
      have e3 : ∀ ε : Fin 4 → Fin 2, 2 * Φ (p.1, emb X ε) (thol (p.1, emb X ε) U)
          = if ∀ κ, ¬ (p.1.1 = κ ∨ p.1.2 = κ) → ε κ = 0
            then 8 * h (thol ((p.1.1, p.1.2), emb X ε) U) else 0 := by
        intro ε
        rw [hΦ, mkField_offDiag _ hne]
        simp only [uniformField]
        rw [show (p.1, emb X ε) = ((p.1.1, p.1.2), emb X ε) from rfl]
        simp only [survives_emb]
        split_ifs
        · norm_num; ring
        · norm_num
      simp_rw [e3]
      rw [sum_survive hne, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
    simp_rw [e2]
    rw [Finset.sum_comm]

end Action

/-! ## 4. The two partition functions -/

section Partition

variable {β : ℝ} (C : WilsonChain β) (i : ℕ)

/-- The fourfold group convolution of the power-step weight. -/
def K4 (g : SU 2) : ℝ := conv (conv (wk C i) (wk C i)) (conv (wk C i) (wk C i)) g

theorem continuous_K4 : Continuous (K4 C i) :=
  continuous_conv (continuous_conv (continuous_wk C i) (continuous_wk C i))
    (continuous_conv (continuous_wk C i) (continuous_wk C i))

theorem K4_pos (g : SU 2) : 0 < K4 C i g := by
  have hw : ∀ g, 0 < wk C i g := fun g => pow_pos (W_pos C i _ (suTau_mem g)) 4
  have hc := continuous_conv (continuous_wk C i) (continuous_wk C i)
  have hw2 := conv_pos (continuous_wk C i) (continuous_wk C i) hw hw
  exact conv_pos hc hc hw2 hw2 g

/-- **The coarse integral**: product Haar on the side-`n` torus, one `K4` per coarse plaquette. -/
def Jc (n : ℕ) : ℝ := ∫ V, ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (thol ((p.1.1, p.1.2), X) V)
    ∂(Measure.pi fun _ : TLink 4 n => probHaar (SU 2))

theorem Jc_pos (n : ℕ) : 0 < Jc C i n := by
  unfold Jc
  have hc : Continuous fun V : TLink 4 n → SU 2 =>
      ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (thol ((p.1.1, p.1.2), X) V) :=
    continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ =>
      (continuous_K4 C i).comp (continuous_thol _)
  have hpos : ∀ V : TLink 4 n → SU 2,
      0 < ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (thol ((p.1.1, p.1.2), X) V) :=
    fun V => Finset.prod_pos fun X _ => Finset.prod_pos fun p _ => K4_pos C i _
  rw [integral_pos_iff_support_of_nonneg (fun V => (hpos V).le) (integrable_of_continuous hc)]
  rw [show Function.support (fun V : TLink 4 n → SU 2 =>
      ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (thol ((p.1.1, p.1.2), X) V)) = univ from
    Set.eq_univ_of_forall fun V => (hpos V).ne', measure_univ]
  exact one_pos

theorem halfField_inv (k : ℕ) (g : SU 2) :
    halfField (C.W k) suTau g⁻¹ = halfField (C.W k) suTau g := by
  simp only [halfField, chainField, suTau_inv]

theorem exp_neg_eight_half (k : ℕ) (g : SU 2) :
    Real.exp (-(8 * halfField (C.W k) suTau g)) = wk C k g := by
  unfold halfField chainField wk
  have hpos := W_pos C k _ (suTau_mem g)
  rw [show -(8 * (-Real.log (C.W k (suTau g)) / 2)) = ((4 : ℕ) : ℝ) * Real.log (C.W k (suTau g)) by
    push_cast; ring, Real.exp_nat_mul, Real.exp_log hpos]

/-- **The moved side-`2n` torus** is a constant per coarse site times the coarse integral.
DERIVED: `64 n⁴` the surviving diagonal pairs with their weight, `fAct_moved`. -/
theorem Zmk_eq (n : ℕ) :
    Zmk C i (2 * n) = Real.exp (-(64 * (n : ℝ) ^ 4 * halfField (C.W i) suTau 1)) * Jc C i n := by
  unfold Zmk ZF
  have hU : ∀ U : TLink 4 (2 * n) → SU 2,
      Real.exp (-fAct (mkField (uniformField (d := 4) (n := 2 * n) (halfField (C.W i) suTau))) U)
      = Real.exp (-(64 * (n : ℝ) ^ 4 * halfField (C.W i) suTau 1))
        * ∏ X : TSite 4 n, ∏ p : Plane, blockW (wk C i) U X p := by
    intro U
    rw [fAct_moved _ (halfField_inv C i) U, neg_add, Real.exp_add, ← Finset.sum_neg_distrib,
      Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun X _ => ?_
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_two]
    set h := halfField (C.W i) suTau
    rw [show -(8 * (h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 0)) U)
        + h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 1)) U)
        + (h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 0)) U)
        + h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 1)) U))))
      = -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 0)) U))
        + -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 0)) U))
        + -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 1)) U))
        + -(8 * h (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 1)) U)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, exp_neg_eight_half, exp_neg_eight_half,
      exp_neg_eight_half, exp_neg_eight_half]
    rfl
  simp_rw [hU]
  rw [integral_const_mul]
  congr 1
  exact decimation (wk C i) (continuous_wk C i) (wk_class C i)

/-- The coarse constant per plaquette, `ν π (μ π)²`. DERIVED: `π` once per group convolution
(`convT_eq_pi_conv`); three convolutions. -/
def cK (C : WilsonChain β) (i : ℕ) : ℝ := C.ν i * π * (C.μ i * π) ^ 2

theorem cK_pos : 0 < cK C i := by
  unfold cK
  have := C.hμ i; have := C.hν i; have := pi_pos
  positivity

theorem card_planes :
    (Finset.univ.filter fun q : Fin 4 × Fin 4 => q.1 < q.2).card = 6 := by decide

/-- **The side-`n` torus at `W_{i+1}`** is a constant per coarse site times the coarse integral. -/
theorem Zh_eq (n : ℕ) :
    Zh C (i + 1) n = Real.exp (-(((4 * n ^ 4 : ℕ) : ℝ) * halfField (C.W (i + 1)) suTau 1))
      * cK C i ^ (6 * n ^ 4) * Jc C i n := by
  unfold Zh ZF
  have hV : ∀ V : TLink 4 n → SU 2,
      Real.exp (-fAct (uniformField (d := 4) (n := n) (halfField (C.W (i + 1)) suTau)) V)
      = Real.exp (-(((4 * n ^ 4 : ℕ) : ℝ) * halfField (C.W (i + 1)) suTau 1)) * cK C i ^ (6 * n ^ 4)
        * ∏ X : TSite 4 n, ∏ p : Plane, K4 C i (thol ((p.1.1, p.1.2), X) V) := by
    intro V
    rw [fAct_halfField_suTau, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum, mul_assoc]
    congr 1
    have e : ∀ X : TSite 4 n,
        Real.exp (-∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2),
          chainField (C.W (i + 1)) suTau (thol (q, X) V))
        = cK C i ^ 6 * ∏ p : Plane, K4 C i (thol ((p.1.1, p.1.2), X) V) := by
      intro X
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      have e1 : ∀ q : Fin 4 × Fin 4, Real.exp (-chainField (C.W (i + 1)) suTau (thol (q, X) V))
          = cK C i * K4 C i (thol (q, X) V) := by
        intro q
        unfold chainField
        rw [neg_neg, Real.exp_log (W_pos C (i + 1) _ (suTau_mem _)), W_succ_eq_K4]
        rfl
      simp_rw [e1]
      rw [Finset.prod_mul_distrib, Finset.prod_const, card_planes]
      congr 1
    simp_rw [e]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    simp only [TSite, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_mul, mul_comm 6]
  simp_rw [hV]
  rw [integral_const_mul]
  rfl

end Partition

/-! ## 5. The exact electric half -/

/-- **The electric half is exact on every flat Wilson chain.** -/
theorem electricExact {β : ℝ} (C : WilsonChain β) (i : ℕ) : ElectricExact C i := by
  refine ⟨-64 * halfField (C.W i) suTau 1 + 4 * halfField (C.W (i + 1)) suTau 1
    - 6 * Real.log (cK C i), fun n _ => ?_⟩
  have hJ := Jc_pos C i n
  have hK := cK_pos C i
  rw [Zmk_eq, Zh_eq, Real.log_mul (Real.exp_pos _).ne' hJ.ne', Real.log_exp,
    Real.log_mul (mul_pos (Real.exp_pos _) (pow_pos hK _)).ne' hJ.ne',
    Real.log_mul (Real.exp_pos _).ne' (pow_pos hK _).ne', Real.log_exp, Real.log_pow]
  push_cast
  ring

/-- **`ElectricExact` on the constructed chain**, for every `β` and every `i`. -/
theorem electricExact_wilsonChainOf (β : ℝ) (i : ℕ) :
    ElectricExact (WilsonChainExists.wilsonChainOf (2 * β)) i :=
  electricExact _ i

end MassGap.ElectricExactProof

#print axioms MassGap.ElectricExactProof.W_succ_eq_K4
#print axioms MassGap.ElectricExactProof.fAct_moved
#print axioms MassGap.ElectricExactProof.Zmk_eq
#print axioms MassGap.ElectricExactProof.Zh_eq
#print axioms MassGap.ElectricExactProof.electricExact
#print axioms MassGap.ElectricExactProof.electricExact_wilsonChainOf
