import Mathlib
import MassGap.GapSideCrossover
import MassGap.ChainCoarseSeed
import MassGap.ChainFirstCrossing
import MassGap.ElectricStepChain
import MassGap.GapSideTwistFlat
import MassGap.GapSideVortexAntiDiagonal
import MassGap.GapSideVortexStepSign

/-!
# MassGap.GapSideSheetPolymer — the sheet cost at strong coupling: area localisation and the polymer form

The vortex free energy `vortexF C i P n = −log(Z^tw/Z)` of the chain torus differs from the untwisted
torus only on the plaquettes of the centre sheet. This module states that difference two ways.

* **Area localisation (first order, every coupling).** Two plaquette fields that agree off a set `S` and
  differ by at most `δ` on it have `|log Z_Ψ − log Z_Φ| ≤ |S| δ` (`log_ZF_sub_abs_le`), on any torus and any
  link measure. The sheet in a plane of the side-`n` 4-torus has at most `2 n²` entries
  (`card_sheetSet_le`), so with `oddOsc C i = sup_g |h_i(−g) − h_i(g)|`, `h_i` the half field of `W_i`,

      |vortexF C i P n| ≤ 2 n² · oddOsc C i          (abs_vortexF_le_area, abs_vortexF_le_oddOsc)

  uniform in the volume `n⁴`, proportional to the sheet area. In the weight,
  `oddOsc C i ≤ ½ sup_{|t| ≤ 1} |log W_i(t) − log W_i(−t)|` (`halfField_odd_le`), giving
  `|vortexF C i P n| ≤ n² sup |log (W_i(t)/W_i(−t))|` (`abs_vortexF_le_weight`).
* **The split of the step net.** For a threshold `δ*`, `VortexStepNetSplit ε δ*` states that the
  remainders of the steps with `oddOsc > δ*` plus the sheet costs `2 m_i² oddOsc C i` of the others sum
  to at most `ε`.
* **The polymer form (exact, every coupling).** A centre-valued link field `χ` is a Haar-preserving
  relabelling that multiplies every plaquette holonomy by `dχ` (`integral_twist_coboundary`). So every
  polymer activity `act Φ ζ X = ∫ ∏_{q ∈ X} (e^{−Φ_q(ζ_q U_q)} − 1)` depends on the twist `ζ` only through
  its class (`act_coboundary`), and equals the untwisted activity whenever some `ζ · dχ` is trivial on
  `X` (`act_untwist`). With the subset expansion `Z^ζ = Σ_X act Φ ζ X` (`ZF_eq_sum_act`),

      Z^ζ − Z = Σ_{X obstructing} (act Φ ζ X − act Φ 1 X)            (ZF_twist_sub_eq)

  over the activated sets that no centre relabelling clears (`Obstructs`). This is the cancellation a convergent cluster expansion of the sheet cost runs on.

Scope: the area bound is first order. It is not small at any pre-crossing step (the sheet costs exceed
the step-net budget there, argued), and the polymer form is an identity, not yet a bound: the
size of an obstructing set, the connected-cluster expansion of `log`, and the activity bound remain.

DERIVED (module-wide): `2` in `2 n²` is the two orientations `(a, b)`, `(b, a)` the tree's action counts per
plaquette, and `n²` the transverse positions `x_a = x_b = 0` of the 4-torus (`4 − 2 = 2` free coordinates);
`32 = 2 · 4²` is the chain-end side `4`; `1/2` is the half field `h = −½ log W`.
-/

noncomputable section

namespace MassGap.GapSideSheetPolymer

open MeasureTheory Set Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing MassGap.ElectricStep
  MassGap.ElectricStepChain MassGap.MovedTorusDecimation MassGap.ElectricExactProof
  MassGap.GapSideVortexAntiDiagonal MassGap.GapSideVortexStepSign MassGap.WilsonChainExists
  MassGap.GapSideCrossover
open MassGap.TwistedTraceBound (negOne coe_negOne)

/-! ## 1. Two fields that agree off a set -/

section Compare

variable {G : Type} [Group G] [MeasurableSpace G] {d N : ℕ}

omit [MeasurableSpace G] in
/-- **The actions differ by at most `|S| δ`** when the fields agree off `S` and differ by at most `δ` on it. -/
theorem fAct_sub_abs_le (Φ Ψ : TPlaq d N → G → ℝ) (S : Finset (TPlaq d N))
    (hoff : ∀ q ∉ S, Ψ q = Φ q) {δ : ℝ} (hon : ∀ q ∈ S, ∀ g, |Ψ q g - Φ q g| ≤ δ)
    (U : TLink d N → G) : |fAct Ψ U - fAct Φ U| ≤ S.card * δ := by
  unfold fAct
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_subset (Finset.subset_univ S) (fun q _ hq => by rw [hoff q hq, sub_self])]
  calc |∑ q ∈ S, (Ψ q (thol q U) - Φ q (thol q U))|
      ≤ ∑ q ∈ S, |Ψ q (thol q U) - Φ q (thol q U)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ S, δ := Finset.sum_le_sum fun q hq => hon q hq _
    _ = S.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Area localisation of a log ratio**: fields that agree off `S` and differ by at most `δ` on it have
`|log Z_Ψ − log Z_Φ| ≤ |S| δ`, whatever the volume. -/
theorem log_ZF_sub_abs_le (μ : Measure G) [SigmaFinite μ] (Φ Ψ : TPlaq d N → G → ℝ)
    (S : Finset (TPlaq d N)) (hoff : ∀ q ∉ S, Ψ q = Φ q) {δ : ℝ}
    (hon : ∀ q ∈ S, ∀ g, |Ψ q g - Φ q g| ≤ δ)
    (hiΦ : Integrable (fun U => Real.exp (-fAct Φ U)) (Measure.pi fun _ : TLink d N => μ))
    (hiΨ : Integrable (fun U => Real.exp (-fAct Ψ U)) (Measure.pi fun _ : TLink d N => μ))
    (hpos : 0 < ZF μ Φ) :
    |Real.log (ZF μ Ψ) - Real.log (ZF μ Φ)| ≤ S.card * δ := by
  have hpt : ∀ U, |fAct Ψ U - fAct Φ U| ≤ S.card * δ := fAct_sub_abs_le Φ Ψ S hoff hon
  set c : ℝ := S.card * δ with hc
  have h1 : ZF μ Ψ ≤ Real.exp c * ZF μ Φ := by
    unfold ZF
    rw [← integral_const_mul]
    refine integral_mono hiΨ (hiΦ.const_mul _) fun U => ?_
    show Real.exp (-fAct Ψ U) ≤ Real.exp c * Real.exp (-fAct Φ U)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hpt U)).1])
  have h2 : ZF μ Φ ≤ Real.exp c * ZF μ Ψ := by
    unfold ZF
    rw [← integral_const_mul]
    refine integral_mono hiΦ (hiΨ.const_mul _) fun U => ?_
    show Real.exp (-fAct Φ U) ≤ Real.exp c * Real.exp (-fAct Ψ U)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hpt U)).2])
  have hΨ : 0 < ZF μ Ψ := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith [Real.exp_pos c]
  have l1 : Real.log (ZF μ Ψ) ≤ c + Real.log (ZF μ Φ) := by
    have h := Real.log_le_log hΨ h1
    rwa [Real.log_mul (Real.exp_pos c).ne' hpos.ne', Real.log_exp] at h
  have l2 : Real.log (ZF μ Φ) ≤ c + Real.log (ZF μ Ψ) := by
    have h := Real.log_le_log hpos h2
    rwa [Real.log_mul (Real.exp_pos c).ne' hΨ.ne', Real.log_exp] at h
  rw [abs_le]
  constructor <;> linarith

end Compare

/-! ## 2. The sheet and its area -/

section Sheet

variable {N : ℕ}

/-- The plaquette entries carrying the centre sheet in the plane `(a, b)`: the `(a, b)` and `(b, a)`
entries at `x_a = x_b = 0`, the support of `GapSideTwistFlat.sheet a b z`. -/
def sheetSet (a b : Fin 4) : Finset (TPlaq 4 N) :=
  Finset.univ.filter fun q => (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ (q.2 a).val = 0 ∧ (q.2 b).val = 0

theorem card_transverse_le {a b : Fin 4} (hab : a ≠ b) :
    (Finset.univ.filter fun x : TSite 4 N => (x a).val = 0 ∧ (x b).val = 0).card ≤ N ^ 2 := by
  have hc : ∀ a b : Fin 4, a ≠ b → Fintype.card {j : Fin 4 // j ≠ a ∧ j ≠ b} = 2 := by decide
  calc _ ≤ (Finset.univ : Finset ({j : Fin 4 // j ≠ a ∧ j ≠ b} → Fin N)).card := by
        refine Finset.card_le_card_of_injOn (fun x j => x j.1) (fun _ _ => Finset.mem_univ _) ?_
        intro x hx y hy hxy
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
        funext j
        by_cases hja : j = a
        · rw [hja]; exact Fin.ext (hx.1.trans hy.1.symm)
        by_cases hjb : j = b
        · rw [hjb]; exact Fin.ext (hx.2.trans hy.2.symm)
        exact congrFun hxy ⟨j, hja, hjb⟩
    _ = N ^ 2 := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hc a b hab]

/-- **The sheet has at most `2 N²` entries** on the side-`N` 4-torus. -/
theorem card_sheetSet_le {a b : Fin 4} (hab : a ≠ b) : (sheetSet (N := N) a b).card ≤ 2 * N ^ 2 := by
  set T := Finset.univ.filter fun x : TSite 4 N => (x a).val = 0 ∧ (x b).val = 0
  have hsub : sheetSet (N := N) a b ⊆ ({(a, b), (b, a)} : Finset (Fin 4 × Fin 4)) ×ˢ T := by
    intro q hq
    simp only [sheetSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, T, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hq.1, hq.2⟩
  calc (sheetSet (N := N) a b).card
      ≤ (({(a, b), (b, a)} : Finset (Fin 4 × Fin 4)) ×ˢ T).card := Finset.card_le_card hsub
    _ = ({(a, b), (b, a)} : Finset (Fin 4 × Fin 4)).card * T.card := Finset.card_product _ _
    _ ≤ 2 * N ^ 2 := Nat.mul_le_mul Finset.card_le_two (card_transverse_le hab)

end Sheet

/-! ## 3. The vortex free energy of the chain torus is area-priced -/

section Chain

variable {β : ℝ} (C : WilsonChain β)

/-- **The vortex free energy is at most the sheet count times the odd oscillation**, at every side. -/
theorem abs_vortexF_le (i : ℕ) (P : Plane) (n : ℕ) {δ : ℝ}
    (hδ : ∀ g : SU 2, |halfField (C.W i) suTau (negOne * g) - halfField (C.W i) suTau g| ≤ δ) :
    |vortexF C i P n| ≤ (sheetSet (N := n) P.1.1 P.1.2).card * δ := by
  have hZ := Zh_pos C i n
  have hT := Ztw_pos C i P n
  unfold vortexF
  rw [Real.log_div hT.ne' hZ.ne', abs_neg]
  show |Real.log (ZF (probHaar (SU 2))
      (twistField 1 (halfField (C.W i) suTau) (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne)))
    - Real.log (ZF (probHaar (SU 2)) (uniformField (d := 4) (n := n) (halfField (C.W i) suTau)))| ≤ _
  refine log_ZF_sub_abs_le (probHaar (SU 2)) _ _ (sheetSet P.1.1 P.1.2) ?_ ?_ ?_ ?_ hZ
  · intro q hq
    simp only [sheetSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    funext g
    show 1 * halfField (C.W i) suTau (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne q * g)
      = halfField (C.W i) suTau g
    unfold GapSideTwistFlat.sheet
    rw [if_neg hq, one_mul, one_mul]
  · intro q hq g
    simp only [sheetSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    show |1 * halfField (C.W i) suTau (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne q * g)
      - halfField (C.W i) suTau g| ≤ δ
    unfold GapSideTwistFlat.sheet
    rw [if_pos hq, one_mul]
    exact hδ g
  · exact integrable_of_continuous (Real.continuous_exp.comp
      (continuous_fAct_of (fun _ => continuous_halfField C i)).neg)
  · exact integrable_of_continuous (Real.continuous_exp.comp
      (continuous_fAct_of (fun _ => continuous_const.mul ((continuous_halfField C i).comp
        (continuous_const.mul continuous_id)))).neg)

/-- **Area form**: `|vortexF C i P n| ≤ 2 n² δ`, uniform in the volume. -/
theorem abs_vortexF_le_area (i : ℕ) (P : Plane) (n : ℕ) {δ : ℝ}
    (hδ : ∀ g : SU 2, |halfField (C.W i) suTau (negOne * g) - halfField (C.W i) suTau g| ≤ δ)
    (hδ0 : 0 ≤ δ) : |vortexF C i P n| ≤ 2 * (n : ℝ) ^ 2 * δ := by
  have hc : ((sheetSet (N := n) P.1.1 P.1.2).card : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    exact_mod_cast card_sheetSet_le (N := n) (ne_of_lt P.2)
  exact (abs_vortexF_le C i P n hδ).trans (mul_le_mul_of_nonneg_right hc hδ0)

/-- The centre flip reverses the class coordinate: `½ Re tr(−g) = −½ Re tr g`. -/
theorem suTau_negOne_mul (g : SU 2) : suTau (negOne * g) = -suTau g := by
  have e : ((negOne * g : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = -(g : Matrix (Fin 2) (Fin 2) ℂ) := by
    show (negOne : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [coe_negOne, neg_one_mul]
  unfold suTau WilsonAction.wilsonDensity
  rw [e, Matrix.trace_neg, Complex.neg_re]
  ring

/-- **The odd oscillation in the weight**: `|h(−g) − h(g)| ≤ η/2` when `|log W(t) − log W(−t)| ≤ η` on `[−1, 1]`. -/
theorem halfField_odd_le (i : ℕ) {η : ℝ}
    (hη : ∀ t ∈ Icc (-1 : ℝ) 1, |Real.log (C.W i t) - Real.log (C.W i (-t))| ≤ η) (g : SU 2) :
    |halfField (C.W i) suTau (negOne * g) - halfField (C.W i) suTau g| ≤ η / 2 := by
  have h := hη _ (suTau_mem g)
  unfold halfField chainField
  rw [suTau_negOne_mul,
    show -Real.log (C.W i (-suTau g)) / 2 - -Real.log (C.W i (suTau g)) / 2
      = (Real.log (C.W i (suTau g)) - Real.log (C.W i (-suTau g))) / 2 by ring,
    abs_div, abs_two]
  linarith

/-- **The sheet cost in the weight**: `|vortexF C i P n| ≤ n² η` when `|log (W_i(t)/W_i(−t))| ≤ η` on `[−1, 1]`. -/
theorem abs_vortexF_le_weight (i : ℕ) (P : Plane) (n : ℕ) {η : ℝ}
    (hη : ∀ t ∈ Icc (-1 : ℝ) 1, |Real.log (C.W i t) - Real.log (C.W i (-t))| ≤ η) (hη0 : 0 ≤ η) :
    |vortexF C i P n| ≤ (n : ℝ) ^ 2 * η := by
  have h := abs_vortexF_le_area C i P n (halfField_odd_le C i hη) (by linarith)
  linarith

theorem continuous_oddDiff (i : ℕ) :
    Continuous fun g : SU 2 => |halfField (C.W i) suTau (negOne * g) - halfField (C.W i) suTau g| :=
  (((continuous_halfField C i).comp (continuous_const.mul continuous_id)).sub
    (continuous_halfField C i)).abs

/-- **The odd oscillation** of the half field of `W_i`: `sup_g |h_i(−g) − h_i(g)|`. -/
def oddOsc (i : ℕ) : ℝ :=
  sSup (Set.range fun g : SU 2 => |halfField (C.W i) suTau (negOne * g) - halfField (C.W i) suTau g|)

theorem le_oddOsc (i : ℕ) (g : SU 2) :
    |halfField (C.W i) suTau (negOne * g) - halfField (C.W i) suTau g| ≤ oddOsc C i :=
  le_csSup (isCompact_range (continuous_oddDiff C i)).bddAbove ⟨g, rfl⟩

theorem oddOsc_nonneg (i : ℕ) : 0 ≤ oddOsc C i :=
  (abs_nonneg _).trans (le_oddOsc C i 1)

/-- **The sheet cost by the odd oscillation**: `|vortexF C i P n| ≤ 2 n² oddOsc C i`. -/
theorem abs_vortexF_le_oddOsc (i : ℕ) (P : Plane) (n : ℕ) :
    |vortexF C i P n| ≤ 2 * (n : ℝ) ^ 2 * oddOsc C i :=
  abs_vortexF_le_area C i P n (le_oddOsc C i) (oddOsc_nonneg C i)

/-- **At the chain end**: `vortexF C k P 4 ≤ 32 oddOsc C k`. -/
theorem vortexF_chainEnd_le_oddOsc (k : ℕ) (P : Plane) : vortexF C k P 4 ≤ 32 * oddOsc C k := by
  have h := abs_vortexF_le_oddOsc C k P 4
  have := le_abs_self (vortexF C k P 4)
  norm_num at h
  linarith

end Chain

/-! ## 4. The step net, split at a threshold -/

/-- **The step net with the sheet cost spent on the strong steps**: at threshold `δ*`, the remainders of
the steps whose odd oscillation exceeds `δ*`, plus the sheet costs `2 m_i² oddOsc` of the others, sum to at
most `ε`.

DERIVED: `1/1000` the sharp seed of `DoublingSharp`, the first-crossing threshold; `2` in `2 β` and
`2^{k+2−i}` as in `GapSideVortexAntiDiagonal.VortexStepNet`; `2` in `2 m²` the two orientations. -/
def VortexStepNetSplit (ε δs : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ P : Plane,
      ∑ i ∈ (Finset.range k).filter (fun i => δs < oddOsc (wilsonChainOf (2 * β)) i),
          (holderExcessTw (wilsonChainOf (2 * β)) i P (2 ^ (k + 2 - i))
            - holderExcess (wilsonChainOf (2 * β)) i (2 ^ (k + 2 - i)))
        + ∑ i ∈ (Finset.range k).filter (fun i => ¬ δs < oddOsc (wilsonChainOf (2 * β)) i),
          2 * ((2 ^ (k + 2 - i) : ℕ) : ℝ) ^ 2 * oddOsc (wilsonChainOf (2 * β)) i ≤ ε

/-! ## 5. The polymer form of the twist -/

section Polymer

variable {d n : ℕ}

/-- **A centre relabelling moves the twist by a coboundary**: for every function `F` of the twisted
holonomies and every centre-valued link field `χ`, `∫ F(ζ · hol U) = ∫ F(ζ · dχ · hol U)`. -/
theorem integral_twist_coboundary (F : (TPlaq d n → SU 2) → ℝ) (ζ : TPlaq d n → SU 2)
    (χ : TLink d n → SU 2) (hχ : ∀ l g, χ l * g = g * χ l) :
    ∫ U, F (fun q => ζ q * thol q U) ∂(Measure.pi fun _ : TLink d n => probHaar (SU 2))
      = ∫ U, F (fun q => ζ q * thol q χ * thol q U)
          ∂(Measure.pi fun _ : TLink d n => probHaar (SU 2)) := by
  let e : (TLink d n → SU 2) ≃ᵐ (TLink d n → SU 2) :=
    MeasurableEquiv.piCongrRight fun l => MeasurableEquiv.mulLeft (χ l)
  have mp : MeasurePreserving e (Measure.pi fun _ : TLink d n => probHaar (SU 2))
      (Measure.pi fun _ : TLink d n => probHaar (SU 2)) :=
    measurePreserving_pi _ _ fun l => measurePreserving_mul_left (probHaar (SU 2)) (χ l)
  calc ∫ U, F (fun q => ζ q * thol q U) ∂(Measure.pi fun _ : TLink d n => probHaar (SU 2))
      = ∫ U, F (fun q => ζ q * thol q (e U)) ∂(Measure.pi fun _ : TLink d n => probHaar (SU 2)) :=
        (mp.integral_comp' (fun U => F (fun q => ζ q * thol q U))).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        show F (fun q => ζ q * thol q (fun l => χ l * U l)) = F (fun q => ζ q * thol q χ * thol q U)
        congr 1
        funext q
        rw [thol_mul_central χ U hχ q, mul_assoc]

/-- **The polymer activity** of an activated set `X` under the twist `ζ`. -/
def act (Φ : TPlaq d n → SU 2 → ℝ) (ζ : TPlaq d n → SU 2) (X : Finset (TPlaq d n)) : ℝ :=
  ∫ U, ∏ q ∈ X, (Real.exp (-Φ q (ζ q * thol q U)) - 1)
    ∂(Measure.pi fun _ : TLink d n => probHaar (SU 2))

/-- **Every activity sees only the class of the twist.** -/
theorem act_coboundary (Φ : TPlaq d n → SU 2 → ℝ) (ζ : TPlaq d n → SU 2) (χ : TLink d n → SU 2)
    (hχ : ∀ l g, χ l * g = g * χ l) (X : Finset (TPlaq d n)) :
    act Φ ζ X = act Φ (fun q => ζ q * thol q χ) X :=
  integral_twist_coboundary (fun h => ∏ q ∈ X, (Real.exp (-Φ q (h q)) - 1)) ζ χ hχ

/-- **A set that a relabelling clears carries the untwisted activity.** -/
theorem act_untwist (Φ : TPlaq d n → SU 2 → ℝ) (ζ : TPlaq d n → SU 2) (χ : TLink d n → SU 2)
    (hχ : ∀ l g, χ l * g = g * χ l) (X : Finset (TPlaq d n)) (hX : ∀ q ∈ X, ζ q * thol q χ = 1) :
    act Φ ζ X = act Φ (fun _ => 1) X := by
  rw [act_coboundary Φ ζ χ hχ X]
  unfold act
  refine integral_congr_ae (Eventually.of_forall fun U => Finset.prod_congr rfl fun q hq => ?_)
  show Real.exp (-Φ q (ζ q * thol q χ * thol q U)) - 1 = Real.exp (-Φ q (1 * thol q U)) - 1
  rw [hX q hq]

/-- **An obstructing set**: no centre relabelling clears the twist on it. -/
def Obstructs (ζ : TPlaq d n → SU 2) (X : Finset (TPlaq d n)) : Prop :=
  ∀ χ : TLink d n → SU 2, (∀ l g, χ l * g = g * χ l) → ∃ q ∈ X, ζ q * thol q χ ≠ 1

theorem integrable_act (Φ : TPlaq d n → SU 2 → ℝ) (hΦ : ∀ q, Continuous (Φ q))
    (ζ : TPlaq d n → SU 2) (X : Finset (TPlaq d n)) :
    Integrable (fun U : TLink d n → SU 2 => ∏ q ∈ X, (Real.exp (-Φ q (ζ q * thol q U)) - 1))
      (Measure.pi fun _ : TLink d n => probHaar (SU 2)) :=
  integrable_of_continuous (continuous_finsetProd _ fun q _ =>
    (Real.continuous_exp.comp ((hΦ q).comp (continuous_const.mul (continuous_thol q))).neg).sub
      continuous_const)

/-- **The subset expansion**: `Z^ζ = Σ_X act Φ ζ X`, an identity at every coupling. -/
theorem ZF_eq_sum_act (Φ : TPlaq d n → SU 2 → ℝ) (hΦ : ∀ q, Continuous (Φ q)) (ζ : TPlaq d n → SU 2) :
    ZF (probHaar (SU 2)) (fun q g => Φ q (ζ q * g))
      = ∑ X ∈ (Finset.univ : Finset (TPlaq d n)).powerset, act Φ ζ X := by
  unfold ZF act
  rw [← integral_finsetSum _ fun X _ => integrable_act Φ hΦ ζ X]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show Real.exp (-∑ q, Φ q (ζ q * thol q U))
    = ∑ X ∈ (Finset.univ : Finset (TPlaq d n)).powerset,
        ∏ q ∈ X, (Real.exp (-Φ q (ζ q * thol q U)) - 1)
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  have hone : ∏ q : TPlaq d n, Real.exp (-Φ q (ζ q * thol q U))
      = ∏ q : TPlaq d n, ((Real.exp (-Φ q (ζ q * thol q U)) - 1) + 1) :=
    Finset.prod_congr rfl fun q _ => by ring
  rw [hone, Finset.prod_add]
  exact Finset.sum_congr rfl fun X _ => by simp

open Classical in
/-- **The twist ratio in polymer form**: `Z^ζ − Z` is the sum, over the obstructing activated sets only,
of the difference of the twisted and untwisted activities. Every set some relabelling clears cancels. -/
theorem ZF_twist_sub_eq (Φ : TPlaq d n → SU 2 → ℝ) (hΦ : ∀ q, Continuous (Φ q)) (ζ : TPlaq d n → SU 2) :
    ZF (probHaar (SU 2)) (fun q g => Φ q (ζ q * g)) - ZF (probHaar (SU 2)) (fun q g => Φ q (1 * g))
      = ∑ X ∈ (Finset.univ : Finset (TPlaq d n)).powerset.filter (fun X => Obstructs ζ X),
          (act Φ ζ X - act Φ (fun _ => 1) X) := by
  classical
  rw [ZF_eq_sum_act Φ hΦ ζ, ZF_eq_sum_act Φ hΦ (fun _ => 1), ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not _ (fun X => Obstructs ζ X)]
  have h0 : ∑ X ∈ (Finset.univ : Finset (TPlaq d n)).powerset.filter (fun X => ¬ Obstructs ζ X),
      (act Φ ζ X - act Φ (fun _ => 1) X) = 0 := by
    refine Finset.sum_eq_zero fun X hX => ?_
    have hn := (Finset.mem_filter.mp hX).2
    unfold Obstructs at hn
    push Not at hn
    obtain ⟨χ, hχ, hcl⟩ := hn
    rw [act_untwist Φ ζ χ hχ X hcl, sub_self]
  rw [h0, add_zero]

end Polymer

#print axioms fAct_sub_abs_le
#print axioms log_ZF_sub_abs_le
#print axioms card_transverse_le
#print axioms card_sheetSet_le
#print axioms abs_vortexF_le
#print axioms abs_vortexF_le_area
#print axioms suTau_negOne_mul
#print axioms halfField_odd_le
#print axioms abs_vortexF_le_weight
#print axioms le_oddOsc
#print axioms abs_vortexF_le_oddOsc
#print axioms vortexF_chainEnd_le_oddOsc
#print axioms integral_twist_coboundary
#print axioms act_coboundary
#print axioms act_untwist
#print axioms ZF_eq_sum_act
#print axioms ZF_twist_sub_eq

end MassGap.GapSideSheetPolymer
