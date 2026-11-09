import Mathlib
import MassGap.TorusDoubling

/-!
# MassGap.HolderBondMoving — the chain's power step as an upper bound on the Wilson measure

The Migdal–Kadanoff step `w ↦ N[(w^m)^{*4}]`, `m = 2^{d−2}`, has two halves. This module proves the
first half, the power, as an inequality on the tree's periodic torus (`TorusDoubling`), for every
group, every dimension and every plaquette density field, twisted fields included.

## The objects

* `thol q U` is the boundary word of the plaquette `q` (`TorusDoubling.hol_eq`).
* A *field* `Φ : TPlaq d N → G → ℝ` gives each plaquette its own density; `fAct Φ U = Σ_q Φ q (thol q U)`
  and `ZF μ Φ = ∫ exp(−fAct Φ U)` over product `μ` on the links. `ZT_eq_ZF`: the tree's `ZT G d φ β N`
  is `ZF (probHaar G)` at the uniform field `β φ`. A central twist on a set of plaquettes is the field
  `twistField β φ ζ`, `q ↦ β φ(ζ_q ·)`.
* `plaqShift κ` moves a plaquette one step in direction `κ`; `ShiftInv κ Φ` says the field is invariant.

## The move (Kadanoff's bond moving, Tomboulis III.1, here by AM–GM)

`moveField κ Φ` keeps the plaquettes containing `κ`, doubles the others at even `x_κ`, and removes them
at odd `x_κ`. For a side `N` that is even and a field invariant along `κ`,

    ZF μ Φ ≤ ZF μ (moveField κ Φ)                                  (zF_le_moveField)

Proof: split the action as `a + a∘σ + c`, `σ` the unit translation along `κ`, `c∘σ = c`; then
`e^{−a−a∘σ−c} ≤ ½(e^{−2a−c} + e^{−2a∘σ−c})` pointwise, and `σ` preserves the product measure
(`integral_exp_move_le`). No constant appears: the bound carries no bulk factor.

## The iterated move and the power `2^{d−2}`

`moveIter S Φ` moves along each direction of `S` in turn. A move along `κ` keeps invariance along
every other direction (`shiftInv_moveField`), so `zF_le_moveIter` needs invariance along `S` only.
`moveIter_eq` is the closed form: the final density of `q` is `2^{#{κ ∈ S, κ ∉ q}} Φ_q` when `x_κ` is
even for every `κ ∈ S` not in `q`, and `0` otherwise. With `S` all directions, a non-degenerate
plaquette gets exactly `2^{d−2} = m` (`mkField_offDiag`): the chain's power step.

* `zT_le_mkField`: `ZT G d φ β N ≤ ZF (probHaar G) (mkField (β φ))` for every compact `G`, every `d`,
  every even `N`, every measurable bounded `φ`.
* `zF_twist_le`: for a twist field invariant along a set `S` of directions, `ZF(twisted) ≤
  ZF(moveIter S twisted)`, with the twist carried on the surviving plaquettes. `zF_sheet_le` is the
  't Hooft sheet in the `(a, b)` planes (`sheetTwist`), moved along the `d − 2` transverse directions:
  a surviving sheet plaquette carries `2^{d−2} β φ(z ·)`, the twisted power.
* `mkField_two`: in two dimensions the power field is the field itself on every non-degenerate
  plaquette (`m = 1`); only the constant diagonal terms move.

## What it does not give

Both bounds are upper bounds at the same field, so a ratio (twist ratio, flux share, zero-flux defect)
is bounded by nothing here. The convolution half (integrating the links inside each coarse face) is not
built. The comparison the seed needs runs the other way for the twisted partition function; see the
findings, section "From the Wilson measure to the chain".

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.HolderBondMoving

open MeasureTheory Finset MassGap.TorusDoubling MassGap.LatticeGauge MassGap.WilsonLattice
  MassGap.CompactGauge

/-! ## 1. The abstract move -/

section Abstract

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- `exp(−f)` is integrable for measurable `f` bounded below by `−B`. -/
theorem integrable_exp_neg {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, -B ≤ f x) :
    Integrable (fun x => Real.exp (-f x)) μ := by
  refine Integrable.of_bound (Real.measurable_exp.comp hf.neg).aestronglyMeasurable
    (Real.exp B) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [hB x])

/-- **The move, abstractly.** For a measure-preserving `σ`, bounded measurable `a, c` and `c ∘ σ = c`:
`∫ e^{−(a + a∘σ + c)} ≤ ∫ e^{−(2a + c)}`. Pointwise AM–GM, then the change of variables `σ`. -/
theorem integral_exp_move_le (σ : X ≃ᵐ X) (hσ : MeasurePreserving σ μ μ) {a c : X → ℝ}
    (ha : Measurable a) (hc : Measurable c) {K : ℝ} (haK : ∀ x, |a x| ≤ K) (hcK : ∀ x, |c x| ≤ K)
    (hcσ : ∀ x, c (σ x) = c x) :
    ∫ x, Real.exp (-(a x + a (σ x) + c x)) ∂μ ≤ ∫ x, Real.exp (-(2 * a x + c x)) ∂μ := by
  have haσ : Measurable (fun x => a (σ x)) := ha.comp σ.measurable
  have hb := fun x => abs_le.mp (haK x)
  have hbσ := fun x => abs_le.mp (haK (σ x))
  have hcb := fun x => abs_le.mp (hcK x)
  have iL : Integrable (fun x => Real.exp (-(a x + a (σ x) + c x))) μ :=
    integrable_exp_neg ((ha.add haσ).add hc) (B := 3 * K) fun x => by
      linarith [(hb x).1, (hbσ x).1, (hcb x).1]
  have iA : Integrable (fun x => Real.exp (-(2 * a x + c x))) μ :=
    integrable_exp_neg ((measurable_const.mul ha).add hc) (B := 3 * K) fun x => by
      linarith [(hb x).1, (hcb x).1]
  have iB : Integrable (fun x => Real.exp (-(2 * a (σ x) + c x))) μ :=
    integrable_exp_neg ((measurable_const.mul haσ).add hc) (B := 3 * K) fun x => by
      linarith [(hbσ x).1, (hcb x).1]
  have key : ∀ x, Real.exp (-(a x + a (σ x) + c x))
      ≤ (Real.exp (-(2 * a x + c x)) + Real.exp (-(2 * a (σ x) + c x))) / 2 := by
    intro x
    set u := Real.exp (-a x - c x / 2)
    set v := Real.exp (-a (σ x) - c x / 2)
    have h1 : Real.exp (-(a x + a (σ x) + c x)) = u * v := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(2 * a x + c x)) = u ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(2 * a (σ x) + c x)) = v ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1, h2, h3]
    nlinarith [sq_nonneg (u - v)]
  have hBeq : ∫ x, Real.exp (-(2 * a (σ x) + c x)) ∂μ = ∫ x, Real.exp (-(2 * a x + c x)) ∂μ := by
    have h := hσ.integral_comp' (fun y => Real.exp (-(2 * a y + c y)))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hcσ x]
  calc ∫ x, Real.exp (-(a x + a (σ x) + c x)) ∂μ
      ≤ ∫ x, (Real.exp (-(2 * a x + c x)) + Real.exp (-(2 * a (σ x) + c x))) / 2 ∂μ :=
        integral_mono iL ((iA.add iB).div_const 2) key
    _ = ((∫ x, Real.exp (-(2 * a x + c x)) ∂μ) + ∫ x, Real.exp (-(2 * a (σ x) + c x)) ∂μ) / 2 := by
        rw [integral_div, integral_add iA iB]
    _ = ∫ x, Real.exp (-(2 * a x + c x)) ∂μ := by rw [hBeq]; ring

end Abstract

/-! ## 2. Fields on the torus -/

section Field

variable {G : Type} [Group G] [MeasurableSpace G]
variable {d N : ℕ}

/-- The boundary word of a plaquette: `U_i(x) U_j(x+i) U_i(x+j)⁻¹ U_j(x)⁻¹`. -/
def thol (q : TPlaq d N) (U : TLink d N → G) : G :=
  U (q.1.1, q.2) * U (q.1.2, tshift q.1.1 q.2) * (U (q.1.1, tshift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹

/-- `thol` is the holonomy of `TorusDoubling.sysT`. -/
theorem hol_sysT (φ : G → ℝ) (q : TPlaq d N) (U : TLink d N → G) :
    (sysT G d N φ).hol q U = thol q U := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  exact hol_eq φ U i j x

/-- The action of a field. -/
noncomputable def fAct (Φ : TPlaq d N → G → ℝ) (U : TLink d N → G) : ℝ :=
  ∑ q, Φ q (thol q U)

/-- The partition function of a field, product `μ` on the links. -/
noncomputable def ZF (μ : Measure G) (Φ : TPlaq d N → G → ℝ) : ℝ :=
  ∫ U, Real.exp (-fAct Φ U) ∂(Measure.pi fun _ : TLink d N => μ)

/-- A central twist `ζ` on the plaquettes, at coupling `β` and density `φ`: `q ↦ β φ(ζ_q ·)`. At
`ζ ≡ 1` it is the uniform field. -/
def twistField (β : ℝ) (φ : G → ℝ) (ζ : TPlaq d N → G) : TPlaq d N → G → ℝ :=
  fun q g => β * φ (ζ q * g)

/-- **The tree's `ZT` is the uniform field.** -/
theorem ZT_eq_ZF [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    (φ : G → ℝ) (β : ℝ) :
    ZT G d φ β N = ZF (probHaar G) (fun (_ : TPlaq d N) g => β * φ g) := by
  unfold ZT System.partition System.vol ZF
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show Real.exp (-β * ∑ p : TPlaq d N, φ ((sysT G d N φ).hol p U))
    = Real.exp (-fAct (fun (_ : TPlaq d N) g => β * φ g) U)
  unfold fAct
  rw [neg_mul, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hol_sysT]

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_thol (q : TPlaq d N) : Measurable (fun U : TLink d N → G => thol q U) := by
  have h1 : Measurable fun U : TLink d N → G => U (q.1.1, q.2) := measurable_pi_apply _
  have h2 : Measurable fun U : TLink d N → G => U (q.1.2, tshift q.1.1 q.2) := measurable_pi_apply _
  have h3 : Measurable fun U : TLink d N → G => U (q.1.1, tshift q.1.2 q.2) := measurable_pi_apply _
  have h4 : Measurable fun U : TLink d N → G => U (q.1.2, q.2) := measurable_pi_apply _
  unfold thol
  exact ((h1.mul h2).mul h3.inv).mul h4.inv

end Field

/-! ## 3. Translations -/

section Shift

variable {d N : ℕ}

/-- `tshift` along two directions commutes. -/
theorem tshift_comm (κ i : Fin d) (x : TSite d N) :
    tshift κ (tshift i x) = tshift i (tshift κ x) := by
  by_cases h : κ = i
  · subst h; rfl
  · unfold tshift
    rw [Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
    exact Function.update_comm (Ne.symm h) _ _ _

/-- A shift along `ν ≠ κ` leaves the `κ` coordinate. -/
theorem tshift_apply_ne {κ ν : Fin d} (h : κ ≠ ν) (x : TSite d N) : tshift ν x κ = x κ := by
  unfold tshift; exact Function.update_of_ne h _ _

/-- The unit shift along `κ` as a permutation of sites. -/
def siteShift (κ : Fin d) : Equiv.Perm (TSite d N) where
  toFun := tshift κ
  invFun := fun x => Function.update x κ ((finRotate N).symm (x κ))
  left_inv := fun x => by
    simp only [tshift, Function.update_self, Equiv.symm_apply_apply, Function.update_idem,
      Function.update_eq_self]
  right_inv := fun x => by
    simp only [tshift, Function.update_self, Equiv.apply_symm_apply, Function.update_idem,
      Function.update_eq_self]

@[simp] theorem siteShift_apply (κ : Fin d) (x : TSite d N) : siteShift κ x = tshift κ x := rfl

/-- The unit shift on links. -/
def linkShift (κ : Fin d) : Equiv.Perm (TLink d N) := Equiv.prodCongr (Equiv.refl _) (siteShift κ)

/-- The unit shift on plaquettes. -/
def plaqShift (κ : Fin d) : Equiv.Perm (TPlaq d N) := Equiv.prodCongr (Equiv.refl _) (siteShift κ)

@[simp] theorem linkShift_apply (κ : Fin d) (l : TLink d N) :
    linkShift κ l = (l.1, tshift κ l.2) := rfl

@[simp] theorem plaqShift_apply (κ : Fin d) (q : TPlaq d N) :
    plaqShift κ q = (q.1, tshift κ q.2) := rfl

variable {G : Type} [MeasurableSpace G]

/-- The shifted configuration `U ∘ linkShift κ`. -/
noncomputable def shiftCfg (κ : Fin d) : (TLink d N → G) ≃ᵐ (TLink d N → G) :=
  (MeasurableEquiv.piCongrLeft (fun _ : TLink d N => G) (linkShift κ)).symm

@[simp] theorem shiftCfg_apply (κ : Fin d) (U : TLink d N → G) (l : TLink d N) :
    shiftCfg κ U l = U (linkShift κ l) := rfl

theorem shiftCfg_measurePreserving (μ : Measure G) [IsProbabilityMeasure μ] (κ : Fin d) :
    MeasurePreserving (shiftCfg (N := N) (G := G) κ) (Measure.pi fun _ : TLink d N => μ)
      (Measure.pi fun _ : TLink d N => μ) := by
  have h : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : TLink d N => G) (linkShift κ))
      (Measure.pi fun _ : TLink d N => μ) (Measure.pi fun _ : TLink d N => μ) :=
    measurePreserving_piCongrLeft (μ := fun _ : TLink d N => μ) (linkShift κ)
  exact MeasurePreserving.symm _ h

/-- **The holonomy of the shifted configuration** is the holonomy of the shifted plaquette. -/
theorem thol_shiftCfg [Group G] (κ : Fin d) (q : TPlaq d N) (U : TLink d N → G) :
    thol q (shiftCfg κ U) = thol (plaqShift κ q) U := by
  simp only [thol, shiftCfg_apply, linkShift_apply, plaqShift_apply]
  rw [tshift_comm κ q.1.1, tshift_comm κ q.1.2]

end Shift

/-! ## 4. Parity along a direction -/

section Parity

/-- On an even side, one step flips the parity. -/
theorem parity_finRotate {N : ℕ} (hN : Even N) (i : Fin N) :
    (finRotate N i).val % 2 = 0 ↔ ¬ (i.val % 2 = 0) := by
  obtain ⟨k, hk⟩ := hN
  cases N with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    have hm : m % 2 = 1 := by omega
    by_cases h : i = Fin.last m
    · rw [if_pos h, h, Fin.val_last]; omega
    · rw [if_neg h]; omega

end Parity

/-! ## 5. One move -/

section Move

variable {d N : ℕ}

/-- `q` contains the direction `κ`. -/
def inK (κ : Fin d) (q : TPlaq d N) : Prop := q.1.1 = κ ∨ q.1.2 = κ

/-- `q` sits at even `x_κ`. -/
def evenAt (κ : Fin d) (q : TPlaq d N) : Prop := (q.2 κ).val % 2 = 0

instance (κ : Fin d) : DecidablePred (inK (N := N) κ) := fun q => by unfold inK; infer_instance

instance (κ : Fin d) : DecidablePred (evenAt (N := N) κ) := fun q => by
  unfold evenAt; infer_instance

theorem inK_plaqShift (κ ν : Fin d) (q : TPlaq d N) : inK κ (plaqShift ν q) ↔ inK κ q := Iff.rfl

theorem evenAt_plaqShift_ne {κ ν : Fin d} (h : κ ≠ ν) (q : TPlaq d N) :
    evenAt κ (plaqShift ν q) ↔ evenAt κ q := by
  simp only [evenAt, plaqShift_apply, tshift_apply_ne h]

theorem evenAt_plaqShift_self (hN : Even N) (κ : Fin d) (q : TPlaq d N) :
    evenAt κ (plaqShift κ q) ↔ ¬ evenAt κ q := by
  simp only [evenAt, plaqShift_apply, tshift, Function.update_self]
  exact parity_finRotate hN _

variable {G : Type} [Group G] [MeasurableSpace G]

/-- The field is invariant under the unit shift along `κ`. -/
def ShiftInv (κ : Fin d) (Φ : TPlaq d N → G → ℝ) : Prop := ∀ q g, Φ (plaqShift κ q) g = Φ q g

/-- **The moved field**: plaquettes containing `κ` keep their density; the others are doubled at
even `x_κ` and removed at odd `x_κ`. DERIVED: `2` is the number of parallel plaquettes merged. -/
def moveField (κ : Fin d) (Φ : TPlaq d N → G → ℝ) : TPlaq d N → G → ℝ := fun q g =>
  if inK κ q then Φ q g else if evenAt κ q then 2 * Φ q g else 0

omit [Group G] [MeasurableSpace G] in
/-- A move along `κ` keeps invariance along every other direction. -/
theorem shiftInv_moveField {κ ν : Fin d} (h : κ ≠ ν) {Φ : TPlaq d N → G → ℝ}
    (hΦ : ShiftInv ν Φ) : ShiftInv ν (moveField κ Φ) := by
  intro q g
  unfold moveField
  rw [if_congr (inK_plaqShift κ ν q) rfl rfl, hΦ q g]
  by_cases hk : inK κ q
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, if_congr (evenAt_plaqShift_ne h q) rfl rfl]

/-- The even part `a`, off `κ`. -/
noncomputable def evenPart (κ : Fin d) (Φ : TPlaq d N → G → ℝ) (U : TLink d N → G) : ℝ :=
  ∑ q, if ¬ inK κ q ∧ evenAt κ q then Φ q (thol q U) else 0

/-- The part on `κ`. -/
noncomputable def kPart (κ : Fin d) (Φ : TPlaq d N → G → ℝ) (U : TLink d N → G) : ℝ :=
  ∑ q, if inK κ q then Φ q (thol q U) else 0

/-- The odd part off `κ` is the even part of the shifted configuration. -/
theorem evenPart_shiftCfg (hN : Even N) (κ : Fin d) {Φ : TPlaq d N → G → ℝ} (hΦ : ShiftInv κ Φ)
    (U : TLink d N → G) :
    evenPart κ Φ (shiftCfg κ U)
      = ∑ q, if ¬ inK κ q ∧ ¬ evenAt κ q then Φ q (thol q U) else 0 := by
  unfold evenPart
  simp_rw [thol_shiftCfg]
  rw [← Equiv.sum_comp (plaqShift κ) (fun q => if ¬ inK κ q ∧ ¬ evenAt κ q then
    Φ q (thol q U) else 0)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [if_congr (and_congr (not_congr (inK_plaqShift κ κ q))
    (by rw [evenAt_plaqShift_self hN κ q, not_not])) rfl rfl, hΦ q]

/-- The part on `κ` is shift invariant. -/
theorem kPart_shiftCfg (κ : Fin d) {Φ : TPlaq d N → G → ℝ} (hΦ : ShiftInv κ Φ)
    (U : TLink d N → G) : kPart κ Φ (shiftCfg κ U) = kPart κ Φ U := by
  unfold kPart
  simp_rw [thol_shiftCfg]
  rw [← Equiv.sum_comp (plaqShift κ) (fun q => if inK κ q then Φ q (thol q U) else 0)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [if_congr (inK_plaqShift κ κ q) rfl rfl, hΦ q]

/-- **The split of the action**: `fAct Φ = a + a∘σ + c`. -/
theorem fAct_split (hN : Even N) (κ : Fin d) {Φ : TPlaq d N → G → ℝ} (hΦ : ShiftInv κ Φ)
    (U : TLink d N → G) :
    fAct Φ U = evenPart κ Φ U + evenPart κ Φ (shiftCfg κ U) + kPart κ Φ U := by
  rw [evenPart_shiftCfg hN κ hΦ U]
  unfold fAct evenPart kPart
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hk : inK κ q
  · simp [hk]
  · by_cases he : evenAt κ q <;> simp [hk, he]

omit [MeasurableSpace G] in
/-- **The moved action**: `fAct (moveField κ Φ) = 2a + c`. -/
theorem fAct_moveField (κ : Fin d) (Φ : TPlaq d N → G → ℝ) (U : TLink d N → G) :
    fAct (moveField κ Φ) U = 2 * evenPart κ Φ U + kPart κ Φ U := by
  unfold fAct evenPart kPart moveField
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hk : inK κ q
  · simp [hk]
  · by_cases he : evenAt κ q <;> simp [hk, he]

theorem abs_ite_zero_le {p : Prop} [Decidable p] (v : ℝ) : |(if p then v else 0)| ≤ |v| := by
  split_ifs <;> simp

theorem measurable_ite_zero {α : Type*} [MeasurableSpace α] {p : Prop} [Decidable p] {f : α → ℝ}
    (hf : Measurable f) : Measurable (fun x => if p then f x else 0) := by
  by_cases h : p <;> simp [h, hf]

/-- A bounded measurable field. -/
def BddField (Φ : TPlaq d N → G → ℝ) (K : ℝ) : Prop :=
  (∀ q, Measurable (Φ q)) ∧ ∀ q g, |Φ q g| ≤ K

omit [Group G] in
theorem bddField_moveField {κ : Fin d} {Φ : TPlaq d N → G → ℝ} {K : ℝ} (h : BddField Φ K) :
    BddField (moveField κ Φ) (2 * K) := by
  refine ⟨fun q => ?_, fun q g => ?_⟩
  · unfold moveField
    by_cases hk : inK κ q
    · simp only [hk, if_true]; exact h.1 q
    · by_cases he : evenAt κ q
      · simp only [hk, he, if_true, if_false]; exact measurable_const.mul (h.1 q)
      · simp only [hk, he, if_false]; exact measurable_const
  · have hK := h.2 q g
    have h0 : 0 ≤ K := le_trans (abs_nonneg _) hK
    unfold moveField
    by_cases hk : inK κ q
    · simp only [hk, if_true]; linarith
    · by_cases he : evenAt κ q
      · simp only [hk, he, if_true, if_false]; rw [abs_mul]; norm_num; linarith
      · simp only [hk, he, if_false, abs_zero]; linarith

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_evenPart (κ : Fin d) {Φ : TPlaq d N → G → ℝ} (hΦ : ∀ q, Measurable (Φ q)) :
    Measurable (evenPart κ Φ) :=
  Finset.measurable_sum _ fun q _ => measurable_ite_zero ((hΦ q).comp (measurable_thol q))

theorem measurable_kPart (κ : Fin d) {Φ : TPlaq d N → G → ℝ} (hΦ : ∀ q, Measurable (Φ q)) :
    Measurable (kPart κ Φ) :=
  Finset.measurable_sum _ fun q _ => measurable_ite_zero ((hΦ q).comp (measurable_thol q))

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem abs_evenPart_le (κ : Fin d) {Φ : TPlaq d N → G → ℝ} {K : ℝ} (hK : ∀ q g, |Φ q g| ≤ K)
    (U : TLink d N → G) : |evenPart κ Φ U| ≤ Fintype.card (TPlaq d N) * K := by
  unfold evenPart
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q, |(if ¬ inK κ q ∧ evenAt κ q then Φ q (thol q U) else 0)|
      ≤ ∑ _q : TPlaq d N, K := Finset.sum_le_sum fun q _ => (abs_ite_zero_le _).trans (hK q _)
    _ = Fintype.card (TPlaq d N) * K := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem abs_kPart_le (κ : Fin d) {Φ : TPlaq d N → G → ℝ} {K : ℝ} (hK : ∀ q g, |Φ q g| ≤ K)
    (U : TLink d N → G) : |kPart κ Φ U| ≤ Fintype.card (TPlaq d N) * K := by
  unfold kPart
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q, |(if inK κ q then Φ q (thol q U) else 0)|
      ≤ ∑ _q : TPlaq d N, K := Finset.sum_le_sum fun q _ => (abs_ite_zero_le _).trans (hK q _)
    _ = Fintype.card (TPlaq d N) * K := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **One move is an upper bound.** On an even side, for a bounded measurable field invariant along
`κ`, `ZF μ Φ ≤ ZF μ (moveField κ Φ)`. -/
theorem zF_le_moveField (μ : Measure G) [IsProbabilityMeasure μ] (hN : Even N) (κ : Fin d)
    {Φ : TPlaq d N → G → ℝ} {K : ℝ} (hb : BddField Φ K) (hΦ : ShiftInv κ Φ) :
    ZF μ Φ ≤ ZF μ (moveField κ Φ) := by
  unfold ZF
  have hL : (fun U => Real.exp (-fAct Φ U)) = fun U => Real.exp (-(evenPart κ Φ U
      + evenPart κ Φ (shiftCfg κ U) + kPart κ Φ U)) := by
    funext U; rw [fAct_split hN κ hΦ U]
  have hR : (fun U => Real.exp (-fAct (moveField κ Φ) U)) = fun U => Real.exp (-(2 * evenPart κ Φ U
      + kPart κ Φ U)) := by
    funext U; rw [fAct_moveField]
  rw [hL, hR]
  exact integral_exp_move_le (shiftCfg κ) (shiftCfg_measurePreserving μ κ)
    (measurable_evenPart κ hb.1) (measurable_kPart κ hb.1) (abs_evenPart_le κ hb.2)
    (abs_kPart_le κ hb.2) (kPart_shiftCfg κ hΦ)

end Move

/-! ## 6. The iterated move -/

section Iter

variable {d N : ℕ} {G : Type} [Group G] [MeasurableSpace G]

/-- Move along each direction of `S`, in the order `0, 1, …, k − 1`. -/
def moveIter (S : Finset (Fin d)) (Φ : TPlaq d N → G → ℝ) : ℕ → TPlaq d N → G → ℝ
  | 0 => Φ
  | k + 1 =>
    if h : k < d then
      (if (⟨k, h⟩ : Fin d) ∈ S then moveField ⟨k, h⟩ (moveIter S Φ k) else moveIter S Φ k)
    else moveIter S Φ k

omit [Group G] [MeasurableSpace G] in
/-- Invariance along the directions of `S` not yet moved survives. -/
theorem shiftInv_moveIter {S : Finset (Fin d)} {Φ : TPlaq d N → G → ℝ}
    (hΦ : ∀ κ ∈ S, ShiftInv κ Φ) (k : ℕ) : ∀ κ ∈ S, k ≤ κ.val → ShiftInv κ (moveIter S Φ k) := by
  induction k with
  | zero => intro κ hκ _; exact hΦ κ hκ
  | succ k ih =>
    intro κ hκ hk
    have hne : (∀ h : k < d, (⟨k, h⟩ : Fin d) ≠ κ) := fun h e => by
      rw [← e] at hk; simp at hk
    simp only [moveIter]
    split_ifs with h1 h2
    · exact shiftInv_moveField (hne h1) (ih κ hκ (by omega))
    · exact ih κ hκ (by omega)
    · exact ih κ hκ (by omega)


/-- The direction `⟨k, h⟩` is the only one with value `k`. -/
theorem fin_eq_of_val {k : ℕ} (h : k < d) {κ : Fin d} (hκ : κ.val = k) : κ = ⟨k, h⟩ := Fin.ext hκ

omit [Group G] [MeasurableSpace G] in
/-- **The closed form of the iterated move.** After the moves along the directions of `S` below `k`,
the density of `q` is `2^{#{κ ∈ S, κ < k, κ ∉ q}} Φ_q` if `x_κ` is even for each such `κ`, else `0`.
DERIVED: `2` per move, as in `moveField`. -/
theorem moveIter_eq (S : Finset (Fin d)) (Φ : TPlaq d N → G → ℝ) (k : ℕ) (hk : k ≤ d)
    (q : TPlaq d N) (g : G) :
    moveIter S Φ k q g =
      if (∀ κ ∈ S, κ.val < k → ¬ inK κ q → evenAt κ q) then
        2 ^ (S.filter fun κ => κ.val < k ∧ ¬ inK κ q).card * Φ q g
      else 0 := by
  induction k with
  | zero =>
    have hF : (S.filter fun κ : Fin d => κ.val < 0 ∧ ¬ inK κ q) = ∅ := by
      ext κ; simp
    rw [if_pos (fun κ _ h => absurd h (Nat.not_lt_zero _)), hF, Finset.card_empty, pow_zero, one_mul]
    rfl
  | succ k ih =>
    have h : k < d := by omega
    have ih' := ih (by omega)
    set κ0 : Fin d := ⟨k, h⟩ with hκ0
    have hstep : moveIter S Φ (k + 1) =
        (if κ0 ∈ S then moveField κ0 (moveIter S Φ k) else moveIter S Φ k) := by
      simp only [moveIter, dif_pos h, hκ0]
    rw [hstep]
    -- the sets and conditions at `k + 1` against those at `k`
    have hlt : ∀ κ : Fin d, κ.val < k + 1 ↔ κ.val < k ∨ κ = κ0 := by
      intro κ
      constructor
      · intro hκ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hκ with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (fin_eq_of_val h h1)
      · rintro (h1 | h1)
        · omega
        · rw [h1]; simp [κ0]
    have hk0 : ¬ (κ0.val < k) := by simp [κ0]
    by_cases hS : κ0 ∈ S
    · rw [if_pos hS]
      unfold moveField
      by_cases hin : inK κ0 q
      · rw [if_pos hin, ih']
        have hC : (∀ κ ∈ S, κ.val < k + 1 → ¬ inK κ q → evenAt κ q)
            ↔ (∀ κ ∈ S, κ.val < k → ¬ inK κ q → evenAt κ q) := by
          constructor
          · intro H κ hκ h1 h2; exact H κ hκ (by omega) h2
          · intro H κ hκ h1 h2
            rcases (hlt κ).mp h1 with h3 | h3
            · exact H κ hκ h3 h2
            · exact absurd (h3 ▸ hin) h2
        have hF : (S.filter fun κ => κ.val < k + 1 ∧ ¬ inK κ q)
            = (S.filter fun κ => κ.val < k ∧ ¬ inK κ q) := by
          refine Finset.filter_congr fun κ _ => ?_
          constructor
          · rintro ⟨h1, h2⟩
            rcases (hlt κ).mp h1 with h3 | h3
            · exact ⟨h3, h2⟩
            · exact absurd (h3 ▸ hin) h2
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        rw [if_congr hC rfl rfl, hF]
      · rw [if_neg hin]
        by_cases hev : evenAt κ0 q
        · rw [if_pos hev, ih']
          have hC : (∀ κ ∈ S, κ.val < k + 1 → ¬ inK κ q → evenAt κ q)
              ↔ (∀ κ ∈ S, κ.val < k → ¬ inK κ q → evenAt κ q) := by
            constructor
            · intro H κ hκ h1 h2; exact H κ hκ (by omega) h2
            · intro H κ hκ h1 h2
              rcases (hlt κ).mp h1 with h3 | h3
              · exact H κ hκ h3 h2
              · rw [h3]; exact hev
          have hF : (S.filter fun κ => κ.val < k + 1 ∧ ¬ inK κ q)
              = insert κ0 (S.filter fun κ => κ.val < k ∧ ¬ inK κ q) := by
            ext κ
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hκ, h1, h2⟩
              rcases (hlt κ).mp h1 with h3 | h3
              · exact Or.inr ⟨hκ, h3, h2⟩
              · exact Or.inl h3
            · rintro (h3 | ⟨hκ, h1, h2⟩)
              · rw [h3]; exact ⟨hS, by simp [κ0], hin⟩
              · exact ⟨hκ, by omega, h2⟩
          have hnot : κ0 ∉ (S.filter fun κ => κ.val < k ∧ ¬ inK κ q) := by
            simp only [Finset.mem_filter, not_and]
            intro _ h1; exact absurd h1 hk0
          rw [if_congr hC rfl rfl, hF, Finset.card_insert_of_notMem hnot, pow_succ]
          split_ifs <;> ring
        · rw [if_neg hev]
          have hC : ¬ (∀ κ ∈ S, κ.val < k + 1 → ¬ inK κ q → evenAt κ q) :=
            fun H => hev (H κ0 hS (by simp [κ0]) hin)
          rw [if_neg hC]
    · rw [if_neg hS, ih']
      have hC : (∀ κ ∈ S, κ.val < k + 1 → ¬ inK κ q → evenAt κ q)
          ↔ (∀ κ ∈ S, κ.val < k → ¬ inK κ q → evenAt κ q) := by
        constructor
        · intro H κ hκ h1 h2; exact H κ hκ (by omega) h2
        · intro H κ hκ h1 h2
          rcases (hlt κ).mp h1 with h3 | h3
          · exact H κ hκ h3 h2
          · exact absurd (h3 ▸ hκ) hS
      have hF : (S.filter fun κ => κ.val < k + 1 ∧ ¬ inK κ q)
          = (S.filter fun κ => κ.val < k ∧ ¬ inK κ q) := by
        refine Finset.filter_congr fun κ hκ => ?_
        constructor
        · rintro ⟨h1, h2⟩
          rcases (hlt κ).mp h1 with h3 | h3
          · exact ⟨h3, h2⟩
          · exact absurd (h3 ▸ hκ) hS
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      rw [if_congr hC rfl rfl, hF]

omit [Group G] in
theorem bddField_two_mul {Φ : TPlaq d N → G → ℝ} {K : ℝ} (h : BddField Φ K) :
    BddField Φ (2 * K) :=
  ⟨h.1, fun q g => by
    have h1 := h.2 q g
    have h0 : 0 ≤ K := le_trans (abs_nonneg _) h1
    linarith⟩

variable [MeasurableMul₂ G] [MeasurableInv G]

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem bddField_moveIter {S : Finset (Fin d)} {Φ : TPlaq d N → G → ℝ} {K : ℝ}
    (hb : BddField Φ K) (k : ℕ) : BddField (moveIter S Φ k) (2 ^ k * K) := by
  induction k with
  | zero => rw [pow_zero, one_mul]; exact hb
  | succ k ih =>
    have he : (2 : ℝ) ^ (k + 1) * K = 2 * (2 ^ k * K) := by ring
    rw [he]
    simp only [moveIter]
    split_ifs
    · exact bddField_moveField ih
    · exact bddField_two_mul ih
    · exact bddField_two_mul ih

/-- **The iterated move is an upper bound.** On an even side, for a bounded measurable field
invariant along every direction of `S`, `ZF μ Φ ≤ ZF μ (moveIter S Φ k)` for every `k`. -/
theorem zF_le_moveIter (μ : Measure G) [IsProbabilityMeasure μ] (hN : Even N)
    {S : Finset (Fin d)} {Φ : TPlaq d N → G → ℝ} {K : ℝ} (hb : BddField Φ K)
    (hΦ : ∀ κ ∈ S, ShiftInv κ Φ) (k : ℕ) : ZF μ Φ ≤ ZF μ (moveIter S Φ k) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine ih.trans ?_
    simp only [moveIter]
    split_ifs with h1 h2
    · exact zF_le_moveField μ hN ⟨k, h1⟩ (bddField_moveIter hb k)
        (shiftInv_moveIter hΦ k ⟨k, h1⟩ h2 le_rfl)
    · exact le_rfl
    · exact le_rfl

end Iter

/-! ## 7. The power step of the chain -/

section Power

variable {d N : ℕ} {G : Type} [Group G] [MeasurableSpace G]

/-- **The Migdal–Kadanoff power field**: the moves along every direction. -/
def mkField (Φ : TPlaq d N → G → ℝ) : TPlaq d N → G → ℝ := moveIter Finset.univ Φ d

/-- `q` survives the moves: `x_κ` is even for every direction `κ` not in `q`. -/
def Survives (q : TPlaq d N) : Prop := ∀ κ : Fin d, ¬ inK κ q → evenAt κ q

instance (q : TPlaq d N) : Decidable (Survives q) := by unfold Survives; infer_instance

/-- The directions not in a non-degenerate plaquette number `d − 2`. -/
theorem card_not_inK {q : TPlaq d N} (hq : q.1.1 ≠ q.1.2) :
    (Finset.univ.filter fun κ : Fin d => κ.val < d ∧ ¬ inK κ q).card = d - 2 := by
  have hF : (Finset.univ.filter fun κ : Fin d => κ.val < d ∧ ¬ inK κ q) = {q.1.1, q.1.2}ᶜ := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_singleton, inK]
    constructor
    · rintro ⟨_, h⟩ h'; exact h (h'.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
    · intro h
      exact ⟨κ.isLt, fun h' => h (h'.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))⟩
  rw [hF, Finset.card_compl, Finset.card_pair hq, Fintype.card_fin]

omit [Group G] [MeasurableSpace G] in
/-- **The power is `2^{d−2}`.** For a non-degenerate plaquette, the power field is `2^{d−2} Φ_q` if
`q` survives and `0` otherwise. DERIVED: `2` per move; `d − 2` the directions transverse to `q`. -/
theorem mkField_offDiag (Φ : TPlaq d N → G → ℝ) {q : TPlaq d N} (hq : q.1.1 ≠ q.1.2) (g : G) :
    mkField Φ q g = if Survives q then 2 ^ (d - 2) * Φ q g else 0 := by
  unfold mkField
  rw [moveIter_eq _ _ d le_rfl, card_not_inK hq]
  refine if_congr ⟨fun H κ h => H κ (Finset.mem_univ _) κ.isLt h,
    fun H κ _ _ h => H κ h⟩ rfl rfl

omit [Group G] [MeasurableSpace G] in
/-- **In two dimensions the power is trivial**: every non-degenerate plaquette survives with its own
density. -/
theorem mkField_two (Φ : TPlaq 2 N → G → ℝ) {q : TPlaq 2 N} (hq : q.1.1 ≠ q.1.2) (g : G) :
    mkField Φ q g = Φ q g := by
  rw [mkField_offDiag Φ hq, if_pos]
  · simp
  · intro κ h
    exfalso
    apply h
    have h1 := q.1.1.isLt
    have h2 := q.1.2.isLt
    have h3 := κ.isLt
    have hne : q.1.1.val ≠ q.1.2.val := fun e => hq (Fin.ext e)
    unfold inK
    by_cases e : q.1.1.val = κ.val
    · exact Or.inl (Fin.ext e)
    · exact Or.inr (Fin.ext (by omega))

omit [MeasurableSpace G] in
/-- A twist field is invariant along `κ` when its twist pattern is. -/
theorem shiftInv_twistField {κ : Fin d} {β : ℝ} {φ : G → ℝ} {ζ : TPlaq d N → G}
    (hζ : ∀ q, ζ (plaqShift κ q) = ζ q) : ShiftInv κ (twistField β φ ζ) := by
  intro q g; unfold twistField; rw [hζ q]

variable [MeasurableMul₂ G] [MeasurableInv G]

/-- **The Wilson torus is dominated by the power field** (the first half of the chain step). For a
compact group `G`, any dimension `d`, an even side `N`, a measurable density `φ` with `|φ| ≤ Kφ`
and any `β`: `ZT G d φ β N ≤ ZF (probHaar G) (mkField (β φ))`, and the power field puts
`2^{d−2} β φ` on the surviving plaquettes (`mkField_offDiag`). -/
theorem zT_le_mkField [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
    (hN : Even N) {φ : G → ℝ} (hφ : Measurable φ) {Kφ : ℝ} (hK : ∀ g, |φ g| ≤ Kφ) (β : ℝ) :
    ZT G d φ β N ≤ ZF (probHaar G) (mkField (fun (_ : TPlaq d N) g => β * φ g)) := by
  rw [ZT_eq_ZF]
  refine zF_le_moveIter (probHaar G) hN (K := |β| * Kφ) ⟨fun _ => measurable_const.mul hφ,
    fun _ g => ?_⟩ (fun κ _ q g => rfl) d
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hK g) (abs_nonneg β)

omit [MeasurableInv G] in
theorem bddField_twistField {β : ℝ} {φ : G → ℝ} (hφ : Measurable φ) {Kφ : ℝ}
    (hK : ∀ g, |φ g| ≤ Kφ) (ζ : TPlaq d N → G) : BddField (twistField β φ ζ) (|β| * Kφ) := by
  refine ⟨fun q => measurable_const.mul (hφ.comp (measurable_const_mul (ζ q))), fun q g => ?_⟩
  unfold twistField
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg β)

/-- **The twisted torus is dominated by the moves along the directions its twist winds through.**
For a twist pattern `ζ` invariant along every direction of `S`, on an even side,
`ZF μ (twistField β φ ζ) ≤ ZF μ (moveIter S (twistField β φ ζ) d)`. The twist rides along: by
`moveIter_eq` the surviving plaquettes keep `β φ(ζ_q ·)` multiplied by `2^{#{κ ∈ S, κ ∉ q}}`. -/
theorem zF_twist_le (μ : Measure G) [IsProbabilityMeasure μ] (hN : Even N) {S : Finset (Fin d)}
    {β : ℝ} {φ : G → ℝ} (hφ : Measurable φ) {Kφ : ℝ} (hK : ∀ g, |φ g| ≤ Kφ) {ζ : TPlaq d N → G}
    (hζ : ∀ κ ∈ S, ∀ q, ζ (plaqShift κ q) = ζ q) :
    ZF μ (twistField β φ ζ) ≤ ZF μ (moveIter S (twistField β φ ζ) d) :=
  zF_le_moveIter μ hN (bddField_twistField hφ hK ζ) (fun κ hκ => shiftInv_twistField (hζ κ hκ)) d

/-- The 't Hooft sheet in the `(a, b)` planes at in-plane position `u`, twisted by `z`: every
`(a, b)` and `(b, a)` plaquette at `(x_a, x_b) = u`, for every transverse position. The same `z` sits on
both orientations, so this is the 't Hooft sheet when `z² = 1` (the `SU(2)` centre, the case used); for a
`Z_N` centre with `N ≥ 3` it is the field as defined, and the inequality below holds for it.

DERIVED: `3` the least `N` whose centre `Z_N` has an element with `z² ≠ 1`; `2` the order of the `SU(2)`
centre. -/
def sheetTwist (a b : Fin d) (u : Fin N × Fin N) (z : G) (q : TPlaq d N) : G :=
  if (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ q.2 a = u.1 ∧ q.2 b = u.2 then z else 1

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The sheet is invariant along every direction transverse to it. -/
theorem sheetTwist_shift {a b κ : Fin d} (ha : κ ≠ a) (hb : κ ≠ b) (u : Fin N × Fin N) (z : G)
    (q : TPlaq d N) : sheetTwist a b u z (plaqShift κ q) = sheetTwist a b u z q := by
  simp only [sheetTwist, plaqShift_apply, tshift_apply_ne (Ne.symm ha), tshift_apply_ne (Ne.symm hb)]

/-- **The sheet-twisted torus is dominated by the transverse moves.** With `S` the directions other
than `a, b`, the twisted partition function is at most that of the moved twisted field; an `(a, b)`
plaquette of the sheet that survives carries `2^{d−2} β φ(z ·)`. -/
theorem zF_sheet_le (μ : Measure G) [IsProbabilityMeasure μ] (hN : Even N) (a b : Fin d)
    (u : Fin N × Fin N) (z : G) {β : ℝ} {φ : G → ℝ} (hφ : Measurable φ) {Kφ : ℝ}
    (hK : ∀ g, |φ g| ≤ Kφ) :
    ZF μ (twistField β φ (sheetTwist a b u z))
      ≤ ZF μ (moveIter (Finset.univ.filter fun κ => κ ≠ a ∧ κ ≠ b)
          (twistField β φ (sheetTwist a b u z)) d) :=
  zF_twist_le μ hN hφ hK fun κ hκ q => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hκ
    exact sheetTwist_shift hκ.1 hκ.2 u z q

end Power

end MassGap.HolderBondMoving

#print axioms MassGap.HolderBondMoving.integral_exp_move_le
#print axioms MassGap.HolderBondMoving.ZT_eq_ZF
#print axioms MassGap.HolderBondMoving.thol_shiftCfg
#print axioms MassGap.HolderBondMoving.parity_finRotate
#print axioms MassGap.HolderBondMoving.fAct_split
#print axioms MassGap.HolderBondMoving.zF_le_moveField
#print axioms MassGap.HolderBondMoving.moveIter_eq
#print axioms MassGap.HolderBondMoving.zF_le_moveIter
#print axioms MassGap.HolderBondMoving.mkField_offDiag
#print axioms MassGap.HolderBondMoving.mkField_two
#print axioms MassGap.HolderBondMoving.zT_le_mkField
#print axioms MassGap.HolderBondMoving.zF_twist_le
#print axioms MassGap.HolderBondMoving.zF_sheet_le
