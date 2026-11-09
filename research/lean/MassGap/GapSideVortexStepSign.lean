import Mathlib
import MassGap.GapSideVortexAntiDiagonal

/-!
# MassGap.GapSideVortexStepSign — the twisted Hölder excess is non-negative: an in-plane move of the sheet is a centre change of variables

`GapSideVortexAntiDiagonal.holderExcessTw C i P m = log Zmktw − log Ztw` compares the sheet-twisted torus with
its image under the bond moves of every direction (`HolderBondMoving.mkField`). The untwisted twin
`ElectricStepChain.holderExcess_nonneg` is `zF_le_moveIter`, whose move along `κ` needs the field invariant
under the unit shift along `κ`. The sheet `GapSideTwistFlat.sheet a b z` is invariant along the transverse
directions only (`HolderBondMoving.sheetTwist_shift`); along `a` the shift carries it one step over.

## The escape

The move along `κ` needs less than invariance. Its proof splits the action as `E + O + K` (plaquettes off `κ`
at even and odd `x_κ`, and the plaquettes containing `κ`), applies AM–GM pointwise, and closes with a
measure-preserving map `τ` carrying `E` to `O` and fixing `K`. Any `τ` with

    Φ_q(hol_q(τ U)) = Φ_{σq}(hol_{σq}(U))        for every q, U        (GaugeShift κ τ Φ)

does this (`σ` the unit shift along `κ`). For a shift-invariant field `τ` is the shift (`gaugeShift_of_shiftInv`).
For the sheet along `a`, `τ` is the shift after a centre change of variables: multiply by `z` the `b`-links
at `x_a = 1`, `x_b = 0` (`gaugeLink`). On the `(a, b)` plaquettes at `x_b = 0` this multiplies the holonomy
by `z` at `x_a ∈ {0, 1}` and by nothing elsewhere; on every other plaquette the factors cancel. So the shifted
sheet times the gauge factor is the sheet (`sheet_gauge`), exactly, for every side `N` and every `z` with
`z² = 1`; centrality enters only to pull the gauge factor out of the holonomy (`thol_mul_central`). Haar measure is invariant under the multiplication (`gaugeEquiv_mp`).

## What is proved

* `zF_le_moveField_gauge`: on an even side, `ZF μ Φ ≤ ZF μ (moveField κ Φ)` for a bounded measurable field with
  `GaugeShift κ τ Φ` for some measure-preserving `τ`.
* `gaugeShift_moveIter`: a move along `κ' ≠ κ` keeps `GaugeShift κ τ`; so `zF_le_moveIter_gauge`:
  `ZF μ Φ ≤ ZF μ (moveIter S Φ k)` when every direction of `S` has such a `τ`.
* `sheet_gauge`: `sheet a b z q · hol_{σ_a q}(m) = sheet a b z (σ_a q)` for the gauge pattern `m = gaugeLink a b z`.
* `gaugeShift_sheet`: every twist field on the sheet has `GaugeShift a` with
  `τ = shift_a ∘ (multiplication by gaugeLink a b z)`.
* **`Ztw_le_Zmktw`**, **`holderExcessTw_nonneg`**: `0 ≤ holderExcessTw C i P m` for every even `m`, every chain,
  every step, every plane. No admissibility hypothesis: the chain weight is continuous on a compact group.
* `vortexF_step_ge`: `vortexF C (i+1) P n − holderExcess C i (2n) ≤ vortexF C i P (2n)`, and
  `vortex_antiDiagonal_ge`: `vortexF C k P 4 − Σ_{i<k} holderExcess C i (2^{k+2−i}) ≤ vortexF C 0 P (2^{k+2})`.

## Scope

The sign is the lower side of the vortex step: it bounds `vortexF` at the Wilson end from below. The sector seed
(`GapSideVortexAntiDiagonal.VortexStepNet`) asks for an upper bound on `Σ (E^tw − E)`; that is not touched here.

Controls: the move lemma and `sheet_gauge` hold for every group and every central `z` with `z² = 1`,
`U(1)` included (`z = −1`); they are inequalities between partition functions at one side and carry no
group-specific sign. Nothing here moves `U(1)` toward confinement.

DERIVED (module-wide): `2` per move and the parity flip on an even side, as in `HolderBondMoving`; `1` and `0`
the coordinates `x_a = 1`, `x_b = 0` of the gauged `b`-links, the sheet sitting at `x_a = x_b = 0`
(`GapSideTwistFlat.sheet`); `4` the dimension; `2^{k+2}` and `4` as in `vortex_antiDiagonal_crossing`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.GapSideVortexStepSign

open MeasureTheory MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling MassGap.HolderBondMoving
  MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing MassGap.ElectricStepChain MassGap.MovedTorusDecimation
  MassGap.GapSideVortexAntiDiagonal
open MassGap.TwistedTraceBound (negOne coe_negOne negOne_mul_self)

/-! ## 1. The move up to a change of variables -/

section Move

variable {d N : ℕ} {G : Type} [Group G] [MeasurableSpace G]

/-- **Shift invariance up to a change of variables**: evaluating the field on the configuration `τ U` is
evaluating it on `U` at the shifted plaquette. -/
def GaugeShift (κ : Fin d) (τ : (TLink d N → G) → (TLink d N → G)) (Φ : TPlaq d N → G → ℝ) : Prop :=
  ∀ q U, Φ q (thol q (τ U)) = Φ (plaqShift κ q) (thol (plaqShift κ q) U)

/-- A shift-invariant field has `GaugeShift` with the shift itself. -/
theorem gaugeShift_of_shiftInv {κ : Fin d} {Φ : TPlaq d N → G → ℝ} (hΦ : ShiftInv κ Φ) :
    GaugeShift κ (shiftCfg κ) Φ := by
  intro q U
  rw [thol_shiftCfg, hΦ]

omit [MeasurableSpace G] in
/-- A move along `κ' ≠ κ` keeps `GaugeShift κ τ`. -/
theorem gaugeShift_moveField {κ κ' : Fin d} (h : κ' ≠ κ) {τ : (TLink d N → G) → (TLink d N → G)}
    {Φ : TPlaq d N → G → ℝ} (hg : GaugeShift κ τ Φ) : GaugeShift κ τ (moveField κ' Φ) := by
  intro q U
  simp only [moveField, hg q U, inK_plaqShift, evenAt_plaqShift_ne h]

omit [MeasurableSpace G] in
/-- `GaugeShift κ τ` survives the moves along the directions below `κ`. -/
theorem gaugeShift_moveIter {S : Finset (Fin d)} {κ : Fin d} {τ : (TLink d N → G) → (TLink d N → G)}
    {Φ : TPlaq d N → G → ℝ} (hg : GaugeShift κ τ Φ) (k : ℕ) (hk : k ≤ κ.val) :
    GaugeShift κ τ (moveIter S Φ k) := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    have hne : ∀ h : k < d, (⟨k, h⟩ : Fin d) ≠ κ := fun h e => by
      rw [← e] at hk; simp at hk
    simp only [moveIter]
    split_ifs with h1 h2
    · exact gaugeShift_moveField (hne h1) (ih (by omega))
    · exact ih (by omega)
    · exact ih (by omega)

omit [MeasurableSpace G] in
/-- The even part off `κ` of the changed configuration is the odd part off `κ`. -/
theorem evenPart_gauge (hN : Even N) (κ : Fin d) {τ : (TLink d N → G) → (TLink d N → G)}
    {Φ : TPlaq d N → G → ℝ} (hg : GaugeShift κ τ Φ) (U : TLink d N → G) :
    evenPart κ Φ (τ U) = ∑ q, if ¬ inK κ q ∧ ¬ evenAt κ q then Φ q (thol q U) else 0 := by
  unfold evenPart
  simp only [hg _ U]
  rw [← Equiv.sum_comp (plaqShift κ) (fun q => if ¬ inK κ q ∧ ¬ evenAt κ q then
    Φ q (thol q U) else 0)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have e : (¬ inK κ (plaqShift κ q) ∧ ¬ evenAt κ (plaqShift κ q)) ↔ (¬ inK κ q ∧ evenAt κ q) := by
    rw [evenAt_plaqShift_self hN κ q, not_not]; exact Iff.rfl
  exact (if_congr e rfl rfl).symm

omit [MeasurableSpace G] in
/-- The part on `κ` is unchanged. -/
theorem kPart_gauge (κ : Fin d) {τ : (TLink d N → G) → (TLink d N → G)}
    {Φ : TPlaq d N → G → ℝ} (hg : GaugeShift κ τ Φ) (U : TLink d N → G) :
    kPart κ Φ (τ U) = kPart κ Φ U := by
  unfold kPart
  simp only [hg _ U]
  rw [← Equiv.sum_comp (plaqShift κ) (fun q => if inK κ q then Φ q (thol q U) else 0)]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact (if_congr (inK_plaqShift κ κ q) rfl rfl).symm

omit [MeasurableSpace G] in
/-- **The split of the action**: `fAct Φ = E + E∘τ + K`. -/
theorem fAct_split_gauge (hN : Even N) (κ : Fin d) {τ : (TLink d N → G) → (TLink d N → G)}
    {Φ : TPlaq d N → G → ℝ} (hg : GaugeShift κ τ Φ) (U : TLink d N → G) :
    fAct Φ U = evenPart κ Φ U + evenPart κ Φ (τ U) + kPart κ Φ U := by
  rw [evenPart_gauge hN κ hg U]
  unfold fAct evenPart kPart
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hk : inK κ q
  · simp [hk]
  · by_cases he : evenAt κ q <;> simp [hk, he]

variable [MeasurableMul₂ G] [MeasurableInv G]

/-- **One move is an upper bound, up to a change of variables.** On an even side, for a bounded measurable
field with `GaugeShift κ τ Φ` for a measure-preserving `τ`, `ZF μ Φ ≤ ZF μ (moveField κ Φ)`. -/
theorem zF_le_moveField_gauge (μ : Measure G) [IsProbabilityMeasure μ] (hN : Even N) (κ : Fin d)
    {Φ : TPlaq d N → G → ℝ} {K : ℝ} (hb : BddField Φ K) (τ : (TLink d N → G) ≃ᵐ (TLink d N → G))
    (hτ : MeasurePreserving τ (Measure.pi fun _ : TLink d N => μ) (Measure.pi fun _ : TLink d N => μ))
    (hg : GaugeShift κ τ Φ) :
    ZF μ Φ ≤ ZF μ (moveField κ Φ) := by
  unfold ZF
  have hL : (fun U => Real.exp (-fAct Φ U)) = fun U => Real.exp (-(evenPart κ Φ U
      + evenPart κ Φ (τ U) + kPart κ Φ U)) := by
    funext U; rw [fAct_split_gauge hN κ hg U]
  have hR : (fun U => Real.exp (-fAct (moveField κ Φ) U)) = fun U => Real.exp (-(2 * evenPart κ Φ U
      + kPart κ Φ U)) := by
    funext U; rw [fAct_moveField]
  rw [hL, hR]
  exact integral_exp_move_le τ hτ (measurable_evenPart κ hb.1) (measurable_kPart κ hb.1)
    (abs_evenPart_le κ hb.2) (abs_kPart_le κ hb.2) (kPart_gauge κ hg)

/-- **The iterated move is an upper bound, up to changes of variables.** -/
theorem zF_le_moveIter_gauge (μ : Measure G) [IsProbabilityMeasure μ] (hN : Even N)
    {S : Finset (Fin d)} {Φ : TPlaq d N → G → ℝ} {K : ℝ} (hb : BddField Φ K)
    (hτ : ∀ κ ∈ S, ∃ τ : (TLink d N → G) ≃ᵐ (TLink d N → G),
      MeasurePreserving τ (Measure.pi fun _ : TLink d N => μ) (Measure.pi fun _ : TLink d N => μ)
        ∧ GaugeShift κ τ Φ)
    (k : ℕ) : ZF μ Φ ≤ ZF μ (moveIter S Φ k) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine ih.trans ?_
    simp only [moveIter]
    split_ifs with h1 h2
    · obtain ⟨τ, hmp, hg⟩ := hτ ⟨k, h1⟩ h2
      exact zF_le_moveField_gauge μ hN ⟨k, h1⟩ (bddField_moveIter hb k) τ hmp
        (gaugeShift_moveIter hg k le_rfl)
    · exact le_rfl
    · exact le_rfl

end Move

/-! ## 2. The centre change of variables that moves the sheet back -/

section Gauge

variable {d N : ℕ} {G : Type} [Group G]

/-- **The gauge pattern**: `z` on the `b`-links at `x_a = 1`, `x_b = 0` (written `R⁻¹ x_a = 0`, `R` the unit
rotation, so no `NeZero` is needed), `1` elsewhere. -/
def gaugeLink (a b : Fin d) (z : G) (l : TLink d N) : G :=
  if l.1 = b ∧ ((finRotate N).symm (l.2 a)).val = 0 ∧ (l.2 b).val = 0 then z else 1

theorem central_mul_comm {A V c w : G} (hc : ∀ g, c * g = g * c) :
    A * V * (c * w) = A * c * (V * w) := by
  rw [mul_assoc A V, ← mul_assoc V c w, ← hc V, mul_assoc c V w, ← mul_assoc A c]

theorem inv_central {c : G} (hc : ∀ g, c * g = g * c) (g : G) : c⁻¹ * g = g * c⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g, mul_inv_cancel_right]

theorem four_central {a1 a2 a3 a4 : G} (u1 u2 u3 u4 : G) (h2 : ∀ g, a2 * g = g * a2)
    (h3 : ∀ g, a3 * g = g * a3) (h4 : ∀ g, a4 * g = g * a4) :
    a1 * u1 * (a2 * u2) * (a3 * u3)⁻¹ * (a4 * u4)⁻¹
      = a1 * a2 * a3⁻¹ * a4⁻¹ * (u1 * u2 * u3⁻¹ * u4⁻¹) := by
  have e3 : (a3 * u3)⁻¹ = a3⁻¹ * u3⁻¹ := by rw [mul_inv_rev, inv_central h3]
  have e4 : (a4 * u4)⁻¹ = a4⁻¹ * u4⁻¹ := by rw [mul_inv_rev, inv_central h4]
  calc a1 * u1 * (a2 * u2) * (a3 * u3)⁻¹ * (a4 * u4)⁻¹
      = a1 * u1 * (a2 * u2) * (a3⁻¹ * u3⁻¹) * (a4⁻¹ * u4⁻¹) := by rw [e3, e4]
    _ = a1 * a2 * (u1 * u2) * (a3⁻¹ * u3⁻¹) * (a4⁻¹ * u4⁻¹) := by rw [central_mul_comm h2]
    _ = a1 * a2 * a3⁻¹ * (u1 * u2 * u3⁻¹) * (a4⁻¹ * u4⁻¹) := by
        rw [central_mul_comm (inv_central h3)]
    _ = a1 * a2 * a3⁻¹ * a4⁻¹ * (u1 * u2 * u3⁻¹ * u4⁻¹) := by
        rw [central_mul_comm (inv_central h4)]

/-- **The holonomy of a centrally multiplied configuration** is the holonomy of the multiplier times the
holonomy of the configuration. -/
theorem thol_mul_central (m U : TLink d N → G) (hm : ∀ l g, m l * g = g * m l) (q : TPlaq d N) :
    thol q (fun l => m l * U l) = thol q m * thol q U := by
  unfold thol
  exact four_central _ _ _ _ (hm _) (hm _) (hm _)

omit [Group G] in
theorem tshift_self (κ : Fin d) (x : TSite d N) : tshift κ x κ = finRotate N (x κ) := by
  simp [tshift]

/-- **The sheet moved one step along `a` and gauged back is the sheet.** For every side `N`, every
`a ≠ b`, every `z` with `z² = 1` and every plaquette `q` (the values lie in `{1, z}`, which commute):
`sheet a b z q · hol_{σ_a q}(gaugeLink a b z) = sheet a b z (σ_a q)`. -/
theorem sheet_gauge {a b : Fin d} (hab : a ≠ b) {z : G} (hzz : z * z = 1)
    (q : TPlaq d N) :
    GapSideTwistFlat.sheet a b z q * thol (plaqShift a q) (gaugeLink a b z)
      = GapSideTwistFlat.sheet a b z (plaqShift a q) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hba : b ≠ a := Ne.symm hab
  obtain ⟨⟨i, j⟩, x⟩ := q
  by_cases hij : i = j
  · subst hij
    rw [show plaqShift a ((i, i), x) = (((i, i), tshift a x) : TPlaq d N) from rfl, thol_diag,
      mul_one]
    have hd : ¬ ((i, i) = (a, b) ∨ (i, i) = (b, a)) := by
      rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> exact hab (by rw [← h.1, ← h.2])
    simp only [GapSideTwistFlat.sheet, hd, false_and, if_false]
  simp only [plaqShift_apply, thol, gaugeLink, GapSideTwistFlat.sheet]
  by_cases hia : i = a
  · subst hia
    by_cases hjb : j = b
    · subst hjb
      simp only [tshift_self, tshift_apply_ne hba, tshift_apply_ne hab, Equiv.symm_apply_apply,
        hab, true_or, true_and, false_and, if_false, inv_one, mul_one, one_mul]
      split_ifs <;> simp [hzi, hzz]
    · have hjb' : ¬ (j = b) := hjb
      have hd : ¬ ((i, j) = (i, b) ∨ (i, j) = (b, i)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hjb h.2
        · exact hab h.1
      simp only [hd, false_and, if_false, hjb', hab, inv_one, mul_one]
  by_cases hib : i = b
  · subst hib
    by_cases hja : j = a
    · subst hja
      simp only [tshift_self, tshift_apply_ne hba, tshift_apply_ne hab, Equiv.symm_apply_apply,
        hab, or_true, true_and, false_and, if_false, inv_one, mul_one]
      split_ifs <;> simp [hzi, hzz]
    · have hjb : j ≠ i := Ne.symm hij
      have hd : ¬ ((i, j) = (a, i) ∨ (i, j) = (i, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hba h.1
        · exact hja h.2
      simp only [hd, false_and, if_false, hjb, inv_one, mul_one, one_mul, true_and,
        tshift_apply_ne (Ne.symm hja) , tshift_apply_ne hjb.symm]
      split_ifs <;> simp
  · by_cases hjb : j = b
    · subst hjb
      have hd : ¬ ((i, j) = (a, j) ∨ (i, j) = (j, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hia h.1
        · exact hib h.1
      simp only [hd, false_and, if_false, hib, inv_one, mul_one, one_mul, true_and,
        tshift_apply_ne (Ne.symm hia), tshift_apply_ne (Ne.symm hib)]
      split_ifs <;> simp
    · have hd : ¬ ((i, j) = (a, b) ∨ (i, j) = (b, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hia h.1
        · exact hib h.1
      simp only [hd, false_and, if_false, hib, hjb, inv_one, mul_one]

/-- The sheet does not see the order of its plane. -/
theorem sheet_comm (a b : Fin d) (z : G) :
    (GapSideTwistFlat.sheet a b z : TPlaq d N → G) = GapSideTwistFlat.sheet b a z := by
  funext q
  unfold GapSideTwistFlat.sheet
  exact if_congr (by tauto) rfl rfl

/-- The sheet is invariant along every direction transverse to it. -/
theorem sheet_shift {a b κ : Fin d} (ha : κ ≠ a) (hb : κ ≠ b) (z : G) (q : TPlaq d N) :
    GapSideTwistFlat.sheet a b z (plaqShift κ q) = GapSideTwistFlat.sheet a b z q := by
  simp only [GapSideTwistFlat.sheet, plaqShift_apply, tshift_apply_ne (Ne.symm ha),
    tshift_apply_ne (Ne.symm hb)]

variable [MeasurableSpace G] [MeasurableMul G]

/-- Multiplication of every link by a fixed pattern, as a measurable equivalence. -/
def gaugeEquiv (m : TLink d N → G) : (TLink d N → G) ≃ᵐ (TLink d N → G) :=
  MeasurableEquiv.piCongrRight fun l => MeasurableEquiv.mulLeft (m l)

theorem gaugeEquiv_apply (m U : TLink d N → G) : gaugeEquiv m U = fun l => m l * U l := rfl

/-- Haar measure does not see the multiplication. -/
theorem gaugeEquiv_mp (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (m : TLink d N → G) :
    MeasurePreserving (gaugeEquiv m) (Measure.pi fun _ : TLink d N => μ)
      (Measure.pi fun _ : TLink d N => μ) :=
  measurePreserving_pi (fun _ : TLink d N => μ) (fun _ => μ)
    (fun l => measurePreserving_mul_left μ (m l))

/-- **The sheet field has `GaugeShift a`**, with the shift after the centre change of variables. -/
theorem gaugeShift_sheet {a b : Fin d} (hab : a ≠ b) {z : G} (hz : ∀ g, z * g = g * z)
    (hzz : z * z = 1) (β : ℝ) (h : G → ℝ) :
    GaugeShift a ((gaugeEquiv (gaugeLink a b z)).trans (shiftCfg a))
      (twistField β h (GapSideTwistFlat.sheet a b z : TPlaq d N → G)) := by
  intro q U
  have hm : ∀ (l : TLink d N) g, gaugeLink a b z l * g = g * gaugeLink a b z l := fun l g => by
    unfold gaugeLink
    split_ifs
    · exact hz g
    · simp
  show β * h (GapSideTwistFlat.sheet a b z q * thol q (shiftCfg a (gaugeEquiv (gaugeLink a b z) U)))
    = β * h (GapSideTwistFlat.sheet a b z (plaqShift a q) * thol (plaqShift a q) U)
  rw [thol_shiftCfg, gaugeEquiv_apply, thol_mul_central _ _ hm, ← mul_assoc,
    sheet_gauge hab hzz q]

/-- **Every direction of the sheet's twist field has a measure-preserving `τ`.** -/
theorem sheet_gaugeShift_all [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    {a b : Fin d} (hab : a ≠ b) {z : G} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1) (β : ℝ) (h : G → ℝ)
    (κ : Fin d) :
    ∃ τ : (TLink d N → G) ≃ᵐ (TLink d N → G),
      MeasurePreserving τ (Measure.pi fun _ : TLink d N => probHaar G)
        (Measure.pi fun _ : TLink d N => probHaar G)
        ∧ GaugeShift κ τ (twistField β h (GapSideTwistFlat.sheet a b z : TPlaq d N → G)) := by
  by_cases ha : κ = a
  · subst ha
    exact ⟨(gaugeEquiv (gaugeLink κ b z)).trans (shiftCfg κ),
      (shiftCfg_measurePreserving _ κ).comp (gaugeEquiv_mp _ _), gaugeShift_sheet hab hz hzz β h⟩
  by_cases hb : κ = b
  · subst hb
    rw [sheet_comm a κ z]
    exact ⟨(gaugeEquiv (gaugeLink κ a z)).trans (shiftCfg κ),
      (shiftCfg_measurePreserving _ κ).comp (gaugeEquiv_mp _ _), gaugeShift_sheet (Ne.symm hab) hz hzz β h⟩
  · exact ⟨shiftCfg κ, shiftCfg_measurePreserving _ κ,
      gaugeShift_of_shiftInv (shiftInv_twistField fun q => sheet_shift ha hb z q)⟩

end Gauge

/-! ## 3. The twisted Hölder excess is non-negative -/

section Sign

variable {β : ℝ} (C : WilsonChain β)

theorem negOne_central (g : SU 2) : negOne * g = g * negOne :=
  Subtype.ext (by simp [coe_negOne])

/-- **The sheet-twisted torus is dominated by its moved field**, every direction moved, on an even side. -/
theorem Ztw_le_Zmktw (i : ℕ) (P : Plane) {m : ℕ} (hm : Even m) : Ztw C i P m ≤ Zmktw C i P m := by
  obtain ⟨K, hK⟩ := (isCompact_range (continuous_halfField C i)).isBounded.exists_norm_le
  have hb : BddField (twistField 1 (halfField (C.W i) suTau)
      (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne : TPlaq 4 m → SU 2)) K := by
    refine ⟨fun q => (continuous_const.mul ((continuous_halfField C i).comp
      (continuous_const.mul continuous_id))).measurable, fun q g => ?_⟩
    unfold twistField
    rw [one_mul, ← Real.norm_eq_abs]
    exact hK _ ⟨_, rfl⟩
  unfold Ztw Zmktw mkField
  exact zF_le_moveIter_gauge (probHaar (SU 2)) hm hb
    (fun κ _ => sheet_gaugeShift_all (ne_of_lt P.2) negOne_central negOne_mul_self 1 _ κ) 4

/-- **The twisted Hölder excess is non-negative** on every even side. -/
theorem holderExcessTw_nonneg (i : ℕ) (P : Plane) {m : ℕ} (hm : Even m) :
    0 ≤ holderExcessTw C i P m := by
  unfold holderExcessTw
  have := Real.log_le_log (Ztw_pos C i P m) (Ztw_le_Zmktw C i P hm)
  linarith

/-- **The vortex step from below**: `F(W_{i+1}, n) − E_i(2n) ≤ F(W_i, 2n)`. -/
theorem vortexF_step_ge (P : Plane) (i n : ℕ) :
    vortexF C (i + 1) P n - holderExcess C i (2 * n) ≤ vortexF C i P (2 * n) := by
  rw [vortexStep_eq C P i n]
  have := holderExcessTw_nonneg C i P (even_two_mul n)
  linarith

/-- **The vortex anti-diagonal from below**: the Wilson-side vortex free energy at side `2^{k+2}` is at least
the chain end at side `4` minus the summed untwisted Hölder excesses. -/
theorem vortex_antiDiagonal_ge (P : Plane) (k : ℕ) :
    vortexF C k P 4 - ∑ i ∈ Finset.range k, holderExcess C i (2 ^ (k + 2 - i))
      ≤ vortexF C 0 P (2 ^ (k + 2)) := by
  rw [vortex_antiDiagonal_crossing C P k, Finset.sum_sub_distrib]
  have h : 0 ≤ ∑ i ∈ Finset.range k, holderExcessTw C i P (2 ^ (k + 2 - i)) :=
    Finset.sum_nonneg fun i hi => holderExcessTw_nonneg C i P
      (Nat.even_pow.mpr ⟨even_two, by have := Finset.mem_range.mp hi; omega⟩)
  linarith

end Sign

end MassGap.GapSideVortexStepSign

end

#print axioms MassGap.GapSideVortexStepSign.zF_le_moveField_gauge
#print axioms MassGap.GapSideVortexStepSign.zF_le_moveIter_gauge
#print axioms MassGap.GapSideVortexStepSign.thol_mul_central
#print axioms MassGap.GapSideVortexStepSign.sheet_gauge
#print axioms MassGap.GapSideVortexStepSign.gaugeEquiv_mp
#print axioms MassGap.GapSideVortexStepSign.gaugeShift_sheet
#print axioms MassGap.GapSideVortexStepSign.sheet_gaugeShift_all
#print axioms MassGap.GapSideVortexStepSign.Ztw_le_Zmktw
#print axioms MassGap.GapSideVortexStepSign.holderExcessTw_nonneg
#print axioms MassGap.GapSideVortexStepSign.vortexF_step_ge
#print axioms MassGap.GapSideVortexStepSign.vortex_antiDiagonal_ge
