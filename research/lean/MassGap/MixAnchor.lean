import Mathlib
import MassGap.DecoupledSplit
import MassGap.DoublingSharp
import MassGap.DeltaLengthTower

/-!
# MassGap.MixAnchor — the mixed-coupling anchor from the decoupled end and the doubling basin

`AnisoTorus.WeakMixAnchor N β` asks that `DA N β β_⊥ · → 0` along the windows for every `β_⊥` in some
`(0, b)`. This module proves it at every `β ≥ 0` from the vanishing at the decoupled end `β_⊥ = 0`. That
vanishing is proved unconditionally in `TwoDVanish.decoupled_vanishes`; the forms here that take
`LayerSplit.TwoDCharacter N β` are kept for that input. Declarations are in `MassGap.MixAnchor`.

## What the squaring reads

`CouplingTower.windowCoupling_succ_le` is `DoublingSharp.rec_sharp` applied to the corner function
`v ↦ log ZR(2^{v₀} n, …, 2^{v₃} n)`. `rec_sharp` reads only `DoublingSharp.PositiveS`, which
`positiveS_of_facts` derives from `DoublingPower.FactRep`: in every direction `μ` and at every corner `v`,
the partition function of the rectangular torus is the trace sequence `KernelPower.traceSeq` of one
symmetric, continuous, bounded, strictly positive transfer kernel on the slice transverse to `μ`
(`RectTransfer.ZR_eq_traceSeq`), whose top eigenfunction gives the four trace facts
(`KernelPower.powerFacts`). That is reflection positivity in each of the four directions separately, on
rectangular tori with independently doubled extents. Isotropy is not read: the corner function is already
anisotropic in its extents, and nothing compares directions.

The transfer kernel in direction `μ` survives an orientation-dependent coupling `c : Fin 4 → Fin 4 → ℝ`
with `c ≥ 0` and `c i j = c j i`: the spatial plaquettes of a slice carry `c ν ν'`, the temporal ones
`c μ ν`, and the reflection `A ↦ A⁻¹` of the axis links reads only the class-function and inversion
properties of `wilsonDensity`. So the squaring holds for the anisotropic torus with the inherited
constants.

## Contents

* `actC`, `ZC c L N`: the rectangular torus with plaquette `((i, j), x)` weighted by `c i j`.
* `ZA_eq`: `AnisoTorus.ZA N β β_⊥ n = ZC (cA β β_⊥) (fun _ => n) N`, `cA` the coupling `β` in-plane and
  `β_⊥` mixed.
* `actC_Φ`, `ZC_eq_cyc`, `ZC_eq_traceSeq`: slicing along any `μ`; the kernel `kC` is symmetric
  (`kC_symm`), continuous (`continuous_kC`), and `0 < kCmin ≤ kC ≤ 1` (`kC_lower`, `abs_kC_le`).
* `factRepC`: `DoublingPower.FactRep` for `v ↦ log ZC(c, ext n v)`.
* `DA_succ_le`: for `β, β_⊥ ≥ 0`, `w ≥ 1`, `DA(w) ≤ 1/1000 ⇒ DA(w+1) ≤ 250 DA(w)²` (inherited constants);
  `DA_nonneg`, `DA_decay`, `tendsto_DA_of_seed`.
* `continuous_DA`: at a fixed window, `β_⊥ ↦ DA N β β_⊥ w` is continuous on `ℝ`.
* `weakMixAnchor_of_decoupled`: at `β ≥ 0`, `DA N β 0 · → 0` gives `WeakMixAnchor N β`. Mechanism: some
  window `w₀ ≥ 1` has `DA(β, 0, w₀) < 1/1000`; continuity in `β_⊥` at that fixed window keeps the seed on
  `[0, b)`; the basin squaring sends every such `β_⊥` to `0` along the windows. The uniformity in the window
  that `AnisoTorus` §4 names is supplied by the basin, which is an open condition at one window.
* `weakMixAnchor_of_twoD`: `TwoDCharacter N β ⇒ WeakMixAnchor N β` at `β ≥ 0`.
* `strongEnd_of_aniso_twoD`: frequently in `β`, `AnisoAnalytic N β ∧ TwoDCharacter N β` gives
  `CouplingTower.StrongEnd N`.

DERIVED (module-wide): `16 = 2⁴` the copies; `2` the doubling and the two orientations of a plane; `0` the
decoupled end and the limits; `1` the least window. Inherited: `1/1000` the seed of `DoublingSharp` and `250`
its squaring constant; `1/4 = 250 · 1/1000` the contraction.

## What does not follow

`AnisoAnalytic N β` (holomorphy in `β_⊥` on a preconnected domain containing `(0, ε)` and `β`, locally bounded
uniformly in the window) stays open. `LayerSplit.TwoDCharacter N β` is not needed for the anchor: `TwoDVanish.weakMixAnchor`. The anchor
interval `(0, b)` is not quantified: `b` depends on `β`, `N` and the first basin window at `β_⊥ = 0`. Nothing
here says the basin is reached at `β_⊥ = β`; that is the content of the Vitali transport through
`AnisoAnalytic`.
-/

namespace MassGap.MixAnchor

open MeasureTheory Filter Topology Set MassGap MassGap.LatticeGauge MassGap.CompactGauge
  MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower MassGap.CyclicKernel
  MassGap.SlabKernelOperator MassGap.DoublingRecursion

/-! ## 1. The orientation-weighted rectangular torus -/

section Torus

variable {N : ℕ} (c : Fin 4 → Fin 4 → ℝ) (L : Fin 4 → ℕ)

/-- **The orientation-weighted action**: the plaquette `((i, j), x)` weighted by `c i j`. No numeral. -/
noncomputable def actC (U : RLink L → SUN.SU N) : ℝ :=
  ∑ q : RPlaq L, c q.1.1 q.1.2 * WilsonAction.wilsonDensity ((sysR L N).hol q U)

variable (N) in
/-- **The orientation-weighted partition function** `ZC = ∫ e^{−S_c}` against product Haar. No numeral. -/
noncomputable def ZC : ℝ :=
  ∫ U, Real.exp (-actC c L U) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))

variable {L}

theorem continuous_hol (q : RPlaq L) : Continuous fun U : RLink L → SUN.SU N => (sysR L N).hol q U := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  simp only [hol_eq]
  fun_prop

variable (L) in
theorem continuous_actC : Continuous fun U : RLink L → SUN.SU N => actC c L U :=
  continuous_finsetSum _ fun q _ =>
    continuous_const.mul (WilsonAction.continuous_wilsonDensity.comp (continuous_hol q))

variable (L N) in
/-- `ZC > 0`, for every coupling. DERIVED: `0` the sign. -/
theorem ZC_pos : 0 < ZC N c L := by
  have hc : Continuous fun U : RLink L → SUN.SU N => Real.exp (-actC c L U) :=
    Real.continuous_exp.comp (continuous_actC c L).neg
  exact integral_exp_pos (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

end Torus

/-! ## 2. The anisotropic coupling -/

/-- **The anisotropic coupling**: `β` on the in-plane orientations, `β_⊥` on the mixed ones. No numeral. -/
def cA (β βp : ℝ) (i j : Fin 4) : ℝ := if AnisoTorus.inPlane (i, j) then β else βp

theorem inPlane_swap : ∀ i j : Fin 4, AnisoTorus.inPlane (j, i) = AnisoTorus.inPlane (i, j) := by decide

theorem cA_symm (β βp : ℝ) (i j : Fin 4) : cA β βp i j = cA β βp j i := by
  unfold cA; rw [inPlane_swap]

theorem cA_nonneg {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) (i j : Fin 4) : 0 ≤ cA β βp i j := by
  unfold cA; split <;> assumption

/-- **The anisotropic torus is the orientation-weighted torus at `cA`.** DERIVED: `0` the excluded terms. -/
theorem ZA_eq (N : ℕ) (β βp : ℝ) (n : ℕ) :
    AnisoTorus.ZA N β βp n = ZC N (cA β βp) (fun _ => n) := by
  unfold AnisoTorus.ZA ZC
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show Real.exp _ = Real.exp _
  congr 1
  unfold AnisoTorus.Sin AnisoTorus.Smix actC
  rw [neg_inj, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, j⟩, x⟩ := q
  have e : (AnisoTorus.sys4 N n).φ ((AnisoTorus.sys4 N n).hol ((i, j), x) U)
      = WilsonAction.wilsonDensity ((sysR (fun _ => n) N).hol ((i, j), x) U) := rfl
  rw [e]
  unfold cA
  by_cases h : AnisoTorus.inPlane (i, j) = true <;> simp [h]

/-! ## 3. Slicing along a direction -/

section Slice

variable (c : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) {N : ℕ}

/-- Spatial plaquette action of one slice, weighted by `c ν ν'`. No numeral. -/
noncomputable def spC (V : SpT μ T → SUN.SU N) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ ν' : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
    c ν.1 ν'.1 * WilsonAction.wilsonDensity (V (ν, y) * V (ν', tsh μ T ν y) * (V (ν, tsh μ T ν' y))⁻¹
      * (V (ν', y))⁻¹)

/-- Temporal plaquette action between two slices, weighted by `c μ ν`. No numeral. -/
noncomputable def tpC (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
    c μ ν.1 * WilsonAction.wilsonDensity (A y * V' (ν, y) * (A (tsh μ T ν y))⁻¹ * (V (ν, y))⁻¹)

end Slice

section SliceSum

variable {c : Fin 4 → Fin 4 → ℝ} {L : Fin 4 → ℕ} {μ : Fin 4} {N : ℕ}

/-- **One slice of the weighted action**: the four orientation classes of `μ` give `sp + 2 tp`.
DERIVED: `2` the two orientations `(μ, ν)`, `(ν, μ)` of a temporal plane. -/
theorem slice_sumC (hN : N ≠ 0) (hsym : ∀ i j, c i j = c j i)
    (W : Fin (L μ) → SlIdx L μ → SUN.SU N) (t : Fin (L μ)) :
    ∑ i : Fin 4, ∑ j : Fin 4, ∑ y : TS L μ,
      c i j * WilsonAction.wilsonDensity ((sysR L N).hol ((i, j), join L μ t y) (Φ L μ W))
      = spC c μ (tr L μ) (spOf (W t))
        + 2 * tpC c μ (tr L μ) (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t))) := by
  have hs : ∀ ν : {j : Fin 4 // j ≠ μ}, c ν.1 μ = c μ ν.1 := fun ν => hsym _ _
  rw [Fintype.sum_eq_add_sum_subtype_ne _ μ, Fintype.sum_eq_add_sum_subtype_ne _ μ]
  simp_rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => ∑ y : TS L μ,
    c _ j * WilsonAction.wilsonDensity ((sysR L N).hol ((_, j), join L μ t y) (Φ L μ W))) μ]
  simp only [hol_μμ, WilsonAction.wilsonDensity_one hN, mul_zero, Finset.sum_const_zero, zero_add,
    hol_μν, hol_νμ, wilsonDensity_inv, hol_νν, Finset.sum_add_distrib, hs]
  unfold spC tpC
  ring

/-- **The weighted action in slice variables.** DERIVED: `2` the temporal orientations. -/
theorem actC_Φ (hN : N ≠ 0) (hsym : ∀ i j, c i j = c j i) (W : Fin (L μ) → SlIdx L μ → SUN.SU N) :
    actC c L (Φ L μ W) = ∑ t, (spC c μ (tr L μ) (spOf (W t))
      + 2 * tpC c μ (tr L μ) (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t)))) := by
  have hsite : ∀ (F : RSite L → ℝ), ∑ x, F x = ∑ t : Fin (L μ), ∑ y : TS L μ, F (join L μ t y) := by
    intro F
    rw [← Fintype.sum_prod_type', ← (siteEquiv (L := L) (μ := μ)).sum_comp]
    rfl
  set D : Fin 4 → Fin 4 → RSite L → ℝ := fun i j x =>
    c i j * WilsonAction.wilsonDensity ((sysR L N).hol ((i, j), x) (Φ L μ W))
  calc actC c L (Φ L μ W) = ∑ i, ∑ j, ∑ x, D i j x := by
        unfold actC
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = ∑ i, ∑ j, ∑ t, ∑ y, D i j (join L μ t y) := by simp_rw [hsite]
    _ = ∑ i, ∑ t, ∑ j, ∑ y, D i j (join L μ t y) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, ∑ y, D i j (join L μ t y) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun t _ => slice_sumC hN hsym W t

/-- `ZC` as an integral over cyclic sequences of slice configurations. DERIVED: `2` the temporal
orientations. -/
theorem ZC_eq_integral (hN : N ≠ 0) (hsym : ∀ i j, c i j = c j i) :
    ZC N c L = ∫ W : Fin (L μ) → SlIdx L μ → SUN.SU N, ∏ t, Real.exp (-(spC c μ (tr L μ) (spOf (W t))
      + 2 * tpC c μ (tr L μ) (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)) := by
  have hmp := measurePreserving_Φ (L := L) (μ := μ) N
  have hc : Continuous fun U : RLink L → SUN.SU N => Real.exp (-actC c L U) :=
    Real.continuous_exp.comp (continuous_actC c L).neg
  unfold ZC
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hc.aestronglyMeasurable]
  congr 1; funext W
  rw [actC_Φ hN hsym W, ← Finset.sum_neg_distrib, Real.exp_sum]

end SliceSum

/-! ## 4. The weighted transfer kernel -/

section Kernel

variable (c : Fin 4 → Fin 4 → ℝ) {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

variable (μ T N) in
/-- The axis-integrated temporal factor. DERIVED: `2` the temporal orientations. -/
noncomputable def gkC (V V' : SpT μ T → SUN.SU N) : ℝ :=
  ∫ A, Real.exp (-(2 * tpC c μ T A V V')) ∂(hA μ T N)

variable (μ T N) in
/-- **The weighted transfer kernel** `e^{−sp(V)/2} gk(V, V') e^{−sp(V')/2}`. DERIVED: `2` the halves. -/
noncomputable def kC (V V' : SpT μ T → SUN.SU N) : ℝ :=
  Real.exp (-spC c μ T V / 2) * gkC c μ T N V V' * Real.exp (-spC c μ T V' / 2)

theorem continuous_tpC {Y : Type*} [TopologicalSpace Y] {f : Y → TT μ T → SUN.SU N}
    {g h : Y → SpT μ T → SUN.SU N} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun q => tpC c μ T (f q) (g q) (h q) := by
  unfold tpC
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun y _ => ?_
  refine continuous_const.mul (WilsonAction.continuous_wilsonDensity.comp ?_)
  have e1 : Continuous fun q => f q y := (continuous_apply y).comp hf
  have e2 : Continuous fun q => h q (ν, y) := (continuous_apply (ν, y)).comp hh
  have e3 : Continuous fun q => f q (tsh μ T ν y) := (continuous_apply _).comp hf
  have e4 : Continuous fun q => g q (ν, y) := (continuous_apply (ν, y)).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_spC {Y : Type*} [TopologicalSpace Y] {g : Y → SpT μ T → SUN.SU N}
    (hg : Continuous g) : Continuous fun q => spC c μ T (g q) := by
  unfold spC
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun ν' _ =>
    continuous_finsetSum _ fun y _ => ?_
  refine continuous_const.mul (WilsonAction.continuous_wilsonDensity.comp ?_)
  have e1 : Continuous fun q => g q (ν, y) := (continuous_apply _).comp hg
  have e2 : Continuous fun q => g q (ν', tsh μ T ν y) := (continuous_apply _).comp hg
  have e3 : Continuous fun q => g q (ν, tsh μ T ν' y) := (continuous_apply _).comp hg
  have e4 : Continuous fun q => g q (ν', y) := (continuous_apply _).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_gkC : Continuous (Function.uncurry (gkC c μ T N)) := by
  have hf0 : Continuous fun q : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × (TT μ T → SUN.SU N) => Real.exp (-(2 * tpC c μ T q.2 q.1.1 q.1.2)) :=
    Real.continuous_exp.comp (continuous_const.mul
      (continuous_tpC c continuous_snd continuous_fst.fst continuous_fst.snd)).neg
  have hf : Continuous (Function.uncurry fun (p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      (A : TT μ T → SUN.SU N) => Real.exp (-(2 * tpC c μ T A p.1 p.2))) := hf0
  have h := continuous_parametric_integral_of_continuous (μ := hA μ T N) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

theorem continuous_kC : Continuous (Function.uncurry (kC c μ T N)) := by
  unfold kC
  have h1 : Continuous fun p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      Real.exp (-spC c μ T p.1 / 2) :=
    Real.continuous_exp.comp ((continuous_spC c continuous_fst).neg.div_const _)
  have h2 : Continuous fun p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      Real.exp (-spC c μ T p.2 / 2) :=
    Real.continuous_exp.comp ((continuous_spC c continuous_snd).neg.div_const _)
  exact (h1.mul (continuous_gkC c)).mul h2

theorem tpC_inv (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) :
    tpC c μ T (fun y => (A y)⁻¹) V' V = tpC c μ T A V V' := by
  unfold tpC
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y _ => ?_
  set a := A y
  set b := A (tsh μ T ν y)
  set v := V (ν, y)
  set w := V' (ν, y)
  have e : a⁻¹ * v * (b⁻¹)⁻¹ * w⁻¹ = a⁻¹ * (a * w * b⁻¹ * v⁻¹)⁻¹ * a⁻¹⁻¹ := by group
  rw [e, WilsonAction.wilsonDensity_conj, wilsonDensity_inv]

theorem gkC_symm (V V' : SpT μ T → SUN.SU N) : gkC c μ T N V V' = gkC c μ T N V' V := by
  set e := MeasurableEquiv.piCongrRight (fun _ : TT μ T => MeasurableEquiv.inv (SUN.SU N))
  have hmp : MeasurePreserving e (hA μ T N) (hA μ T N) := measurePreserving_invAx
  unfold gkC
  rw [← hmp.integral_comp' (fun A => Real.exp (-(2 * tpC c μ T A V' V)))]
  refine integral_congr_ae (Eventually.of_forall fun A => ?_)
  have hA' : (e A) = fun y => (A y)⁻¹ := rfl
  show Real.exp (-(2 * tpC c μ T A V V')) = Real.exp (-(2 * tpC c μ T (e A) V' V))
  rw [hA', tpC_inv]

/-- **The weighted kernel is symmetric**, by the reflection `A ↦ A⁻¹` of the axis links. -/
theorem kC_symm (V V' : SpT μ T → SUN.SU N) : kC c μ T N V V' = kC c μ T N V' V := by
  unfold kC; rw [gkC_symm]; ring

variable {c}

theorem tpC_nonneg (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (A : TT μ T → SUN.SU N)
    (V V' : SpT μ T → SUN.SU N) : 0 ≤ tpC c μ T A V V' :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (hc _ _) (WilsonAction.wilsonDensity_nonneg hN _)

theorem spC_nonneg (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V : SpT μ T → SUN.SU N) : 0 ≤ spC c μ T V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (hc _ _) (WilsonAction.wilsonDensity_nonneg hN _)

variable (c μ T) in
/-- A bound for `tpC`. DERIVED: `2` the maximum of `wilsonDensity`. -/
def tpCMax : ℝ := ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, c μ ν.1 * 2

variable (c μ T) in
/-- A bound for `spC`. DERIVED: `2` the maximum of `wilsonDensity`. -/
def spCMax : ℝ := ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ ν' : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, c ν.1 ν'.1 * 2

theorem tpC_le (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (A : TT μ T → SUN.SU N)
    (V V' : SpT μ T → SUN.SU N) : tpC c μ T A V V' ≤ tpCMax c μ T :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_left (WilsonAction.wilsonDensity_le_two hN _) (hc _ _)

theorem spC_le (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V : SpT μ T → SUN.SU N) :
    spC c μ T V ≤ spCMax c μ T :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_left (WilsonAction.wilsonDensity_le_two hN _) (hc _ _)

theorem gkC_le_one (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V V' : SpT μ T → SUN.SU N) :
    gkC c μ T N V V' ≤ 1 := by
  unfold gkC
  calc _ ≤ ∫ _A, (1 : ℝ) ∂(hA μ T N) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun A => (Real.exp_pos _).le)
          (integrable_const _) (Eventually.of_forall fun A => ?_)
        rw [Real.exp_le_one_iff]
        have := tpC_nonneg hN hc A V V'
        linarith
    _ = 1 := by simp

theorem gkC_ge (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V V' : SpT μ T → SUN.SU N) :
    Real.exp (-(2 * tpCMax c μ T)) ≤ gkC c μ T N V V' := by
  unfold gkC
  have hm : Measurable fun A : TT μ T → SUN.SU N => Real.exp (-(2 * tpC c μ T A V V')) :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_tpC c continuous_id continuous_const continuous_const)).neg).measurable
  calc Real.exp (-(2 * tpCMax c μ T)) = ∫ _A, Real.exp (-(2 * tpCMax c μ T)) ∂(hA μ T N) := by
        simp
    _ ≤ _ := by
        refine integral_mono (integrable_const _) ?_ (fun A => ?_)
        · exact integrable_of_bdd hm (C := 1) (fun A => by
            rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
            have := tpC_nonneg hN hc A V V'; linarith)
        · rw [Real.exp_le_exp]
          have := tpC_le hN hc A V V'
          linarith

theorem kC_le_one (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V V' : SpT μ T → SUN.SU N) :
    kC c μ T N V V' ≤ 1 := by
  unfold kC
  have h1 : Real.exp (-spC c μ T V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := spC_nonneg hN hc V; linarith
  have h2 : Real.exp (-spC c μ T V' / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := spC_nonneg hN hc V'; linarith
  have h3 := gkC_le_one hN hc V V'
  have h0 : 0 ≤ gkC c μ T N V V' := (Real.exp_pos _).le.trans (gkC_ge hN hc V V')
  exact mul_le_one₀ (mul_le_one₀ h1 h0 h3) (Real.exp_pos _).le h2

variable (c μ T) in
/-- The lower bound for `kC`. No numeral. -/
noncomputable def kCmin : ℝ := Real.exp (-spCMax c μ T) * Real.exp (-(2 * tpCMax c μ T))

variable (c) in
theorem kCmin_pos : 0 < kCmin c μ T := by unfold kCmin; positivity

theorem kC_lower (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V V' : SpT μ T → SUN.SU N) :
    kCmin c μ T ≤ kC c μ T N V V' := by
  unfold kC kCmin
  have h1 : Real.exp (-spCMax c μ T / 2) ≤ Real.exp (-spC c μ T V / 2) := by
    rw [Real.exp_le_exp]; have := spC_le hN hc V; linarith
  have h2 : Real.exp (-spCMax c μ T / 2) ≤ Real.exp (-spC c μ T V' / 2) := by
    rw [Real.exp_le_exp]; have := spC_le hN hc V'; linarith
  have h3 := gkC_ge hN hc V V'
  have e : Real.exp (-spCMax c μ T)
      = Real.exp (-spCMax c μ T / 2) * Real.exp (-spCMax c μ T / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  calc Real.exp (-spCMax c μ T / 2) * Real.exp (-spCMax c μ T / 2) * Real.exp (-(2 * tpCMax c μ T))
      = Real.exp (-spCMax c μ T / 2) * Real.exp (-(2 * tpCMax c μ T))
          * Real.exp (-spCMax c μ T / 2) := by ring
    _ ≤ _ := by
        have h0 : 0 ≤ gkC c μ T N V V' := (Real.exp_pos _).le.trans h3
        exact mul_le_mul (mul_le_mul h1 h3 (Real.exp_pos _).le (Real.exp_pos _).le) h2
          (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le h0)

theorem abs_kC_le (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (V V' : SpT μ T → SUN.SU N) :
    |kC c μ T N V V'| ≤ 1 := by
  rw [abs_of_nonneg ((kCmin_pos c).le.trans (kC_lower hN hc V V'))]
  exact kC_le_one hN hc V V'

end Kernel

/-! ## 5. The weighted torus as a trace sequence -/

section Trace

variable {c : Fin 4 → Fin 4 → ℝ} {μ : Fin 4} {N : ℕ} {L : Fin 4 → ℕ}

/-- **The weighted torus is the cyclic integral of the weighted kernel** in direction `μ`. DERIVED: `2` the
temporal orientations and the halves. -/
theorem ZC_eq_cyc (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i) :
    ZC N c L = cyc (hS μ (tr L μ) N) (kC c μ (tr L μ) N) (L μ) := by
  rw [ZC_eq_integral (μ := μ) hN hsym]
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
    fun p => ∏ t, Real.exp (-(spC c μ (tr L μ) (p.2 t)
      + 2 * tpC c μ (tr L μ) (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))))
  have hG : Continuous G := by
    refine continuous_finsetProd _ fun t _ => Real.continuous_exp.comp (Continuous.neg ?_)
    exact (continuous_spC c ((continuous_apply t).comp continuous_snd)).add
      (continuous_const.mul (continuous_tpC c ((continuous_apply t).comp continuous_fst)
        ((continuous_apply t).comp continuous_snd)
        ((continuous_apply (finRotate (L μ) t)).comp continuous_snd)))
  have h1 : ∫ W : Fin (L μ) → SlIdx L μ → SUN.SU N, ∏ t, Real.exp (-(spC c μ (tr L μ) (spOf (W t))
      + 2 * tpC c μ (tr L μ) (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))
      = ∫ p, G p ∂((Measure.pi fun _ : Fin (L μ) => hA μ (tr L μ) N).prod
          (Measure.pi fun _ : Fin (L μ) => hS μ (tr L μ) N)) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [h1]
  have hGb : ∀ p, |G p| ≤ (1 : ℝ) ^ Fintype.card (Fin (L μ)) := by
    intro p
    refine abs_prod_le fun t => ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have a1 := spC_nonneg hN hc (p.2 t)
    have a3 := tpC_nonneg hN hc (p.1 t) (p.2 t) (p.2 (finRotate (L μ) t))
    linarith
  rw [integral_prod_symm _ (integrable_of_bdd hG.measurable hGb)]
  unfold cyc
  refine integral_congr_ae (Eventually.of_forall fun V => ?_)
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin (L μ) => hA μ (tr L μ) N)
    (fun t (a : TS L μ → SUN.SU N) => Real.exp (-(spC c μ (tr L μ) (V t)
      + 2 * tpC c μ (tr L μ) a (V t) (V (finRotate (L μ) t)))))
  show ∫ A, ∏ t, Real.exp (-(spC c μ (tr L μ) (V t)
      + 2 * tpC c μ (tr L μ) (A t) (V t) (V (finRotate (L μ) t))))
      ∂(Measure.pi fun _ : Fin (L μ) => hA μ (tr L μ) N) = _
  rw [hprod]
  have hfac : ∀ t, ∫ a, Real.exp (-(spC c μ (tr L μ) (V t)
      + 2 * tpC c μ (tr L μ) a (V t) (V (finRotate (L μ) t)))) ∂(hA μ (tr L μ) N)
      = Real.exp (-spC c μ (tr L μ) (V t)) * gkC c μ (tr L μ) N (V t) (V (finRotate (L μ) t)) := by
    intro t
    unfold gkC
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [hfac]
  unfold kC
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hrot : ∏ t, Real.exp (-spC c μ (tr L μ) (V (finRotate (L μ) t)) / 2)
      = ∏ t, Real.exp (-spC c μ (tr L μ) (V t) / 2) :=
    Fintype.prod_equiv (finRotate (L μ)) _ _ (fun t => rfl)
  rw [hrot]
  have hhalf : ∏ t, Real.exp (-spC c μ (tr L μ) (V t))
      = (∏ t, Real.exp (-spC c μ (tr L μ) (V t) / 2)) * ∏ t, Real.exp (-spC c μ (tr L μ) (V t) / 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Real.exp_add]; congr 1; ring
  rw [hhalf]; ring

/-- **For even extent in direction `μ`, the weighted torus is the trace sequence of the weighted kernel.**
DERIVED: `2` the even extent; `1` the least half-extent. -/
theorem ZC_eq_traceSeq (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i) (j : ℕ)
    (hj : 1 ≤ j) (hL : L μ = 2 * j) :
    ZC N c L = traceSeq (hS μ (tr L μ) N) (kC c μ (tr L μ) N) (L μ) := by
  rw [ZC_eq_cyc (μ := μ) hN hc hsym, hL]
  exact cyc_even ⟨(continuous_kC c).measurable, 1, abs_kC_le hN hc⟩ (kC_symm c) j hj

end Trace

/-! ## 6. The four trace facts and the corner function -/

section Facts

variable {c : Fin 4 → Fin 4 → ℝ} {N : ℕ}

variable (c N) in
/-- The trace sequence of the weighted transverse kernel. No numeral. -/
noncomputable def FC (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (m : ℕ) : ℝ :=
  traceSeq (hS μ T N) (kC c μ T N) m

variable (c N) in
/-- **The weighted corner function** `v ↦ log ZC(c, 2^{v₀} n, …, 2^{v₃} n)`. No numeral. -/
noncomputable def xC (n : ℕ) (v : Pt) : ℝ := Real.log (ZC N c (DoublingWilson.ext n v))

theorem K_posC (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) :
    0 < ‖kernelCLM (kC c μ T N) 1 (continuous_kC c).measurable zero_le_one (abs_kC_le hN hc)
      (hS μ T N) (hS μ T N)‖ :=
  norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _ (kCmin_pos c) (kC_lower hN hc))

/-- **The four trace facts for the weighted kernel**, at every even `m = 2j ≥ 2`. DERIVED: `2` the even
length; `1` the least half-length. -/
theorem factsC (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (j : ℕ)
    (hj : 1 ≤ j) : ∃ lam s : ℝ, DoublingPower.PowerFacts (FC c N μ T) lam s (2 * j) := by
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, e, he, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS μ T N) (continuous_kC c) zero_le_one (abs_kC_le hN hc)
      (kC_symm c) (K_posC hN hc μ T)
  have he0 : e ≠ 0 := by
    intro h; rw [h, abs_zero] at he; linarith [K_posC hN hc μ T]
  exact ⟨|e|, _, powerFacts (continuous_kC c).measurable zero_le_one (abs_kC_le hN hc)
    (kC_symm c) hφm hφb hφ1 heig he he0 j hj⟩

theorem xC_eq (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) (v : Pt) (μ : Fin 4) :
    xC c N n v = Real.log (FC c N μ (tr (DoublingWilson.ext n v) μ) (DoublingWilson.ext n v μ)) := by
  obtain ⟨n', rfl⟩ := he
  have hj : 1 ≤ 2 ^ (v μ) * n' := by
    have : 1 ≤ 2 ^ (v μ) := Nat.one_le_two_pow; nlinarith
  unfold xC FC
  rw [ZC_eq_traceSeq (μ := μ) hN hc hsym (2 ^ (v μ) * n') hj
    (by simp only [DoublingWilson.ext]; ring)]

/-- **`FactRep` for the weighted corner function**: the hypothesis of `DoublingSharp.positiveS_of_facts`,
for every symmetric nonnegative orientation coupling. DERIVED: `2` the least even side. -/
theorem factRepC (hN : N ≠ 0) (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) : DoublingPower.FactRep (xC c N n) := by
  intro μ v
  obtain ⟨n', rfl⟩ := he
  set j := 2 ^ (v μ) * n' with hjdef
  have hj : 1 ≤ j := by
    have : 1 ≤ 2 ^ (v μ) := Nat.one_le_two_pow; rw [hjdef]; nlinarith
  have hm : DoublingWilson.ext (n' + n') v μ = 2 * j := by
    simp only [DoublingWilson.ext, hjdef]; ring
  obtain ⟨lam, s, hf⟩ := factsC hN hc μ (tr (DoublingWilson.ext (n' + n') v) μ) j hj
  refine ⟨FC c N μ (tr (DoublingWilson.ext (n' + n') v) μ), lam, s, 2 * j, hf, ?_, ?_, ?_⟩
  · rw [xC_eq hN hc hsym hn ⟨n', rfl⟩ v μ, hm]
  · rw [xC_eq hN hc hsym hn ⟨n', rfl⟩ (v + E μ) μ, DoublingWilson.tr_ext_add,
      DoublingWilson.ext_add_self, hm]
  · rw [xC_eq hN hc hsym hn ⟨n', rfl⟩ (v + E μ + E μ) μ, DoublingWilson.tr_ext_add,
      DoublingWilson.tr_ext_add, DoublingWilson.ext_add_self, DoublingWilson.ext_add_self, hm]

end Facts

/-! ## 7. The anisotropic window defect: squaring, decay, continuity -/

section Window

variable {N : ℕ}

/-- **The corner function reads the anisotropic window defect**: at side `2^w`, corner `k`,
`Δ = DA N β β_⊥ (w + k)`. DERIVED: `2` the doubling; `1` the next window. -/
theorem Δ_xA (β βp : ℝ) (w k : ℕ) :
    Δ (xC (cA β βp) N (2 ^ w)) (corner k) = AnisoTorus.DA N β βp (w + k) := by
  have h1 : DoublingWilson.ext (2 ^ w) (corner k) = fun _ => 2 ^ (w + k) := by
    funext i; simp only [DoublingWilson.ext, corner]; ring
  have h2 : DoublingWilson.ext (2 ^ w) (corner k + one) = fun _ => 2 ^ (w + k + 1) := by
    rw [← corner_succ]; funext i; simp only [DoublingWilson.ext, corner]; ring
  unfold Δ xC AnisoTorus.DA AnisoTorus.logZA
  rw [h1, h2, ZA_eq, ZA_eq]

theorem factRepA (hN : N ≠ 0) {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) {w : ℕ} (hw : 1 ≤ w) :
    DoublingPower.FactRep (xC (cA β βp) N (2 ^ w)) :=
  factRepC hN (cA_nonneg hβ hβp) (cA_symm β βp) (DeltaLengthTower.two_le_two_pow hw)
    (DeltaLengthTower.even_two_pow hw)

/-- `DA ≥ 0` at `β, β_⊥ ≥ 0`, `w ≥ 1`. DERIVED: `0` the sign; `1` the least window. -/
theorem DA_nonneg (hN : N ≠ 0) {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) {w : ℕ} (hw : 1 ≤ w) :
    0 ≤ AnisoTorus.DA N β βp w := by
  have h := Δ_nonneg (DoublingPower.positive_of_facts (factRepA hN hβ hβp hw)) (corner 0)
  rwa [Δ_xA, add_zero] at h

/-- **One doubling squares the anisotropic reading in the basin**: `DA(w+1) ≤ 250 DA(w)²`. Inherited: `1/1000`
the seed and `250` the squaring constant of `DoublingSharp.rec_sharp`. DERIVED: `1` the least window and the
step; `1/1000`, `250` as inherited above. -/
theorem DA_succ_le (hN : N ≠ 0) {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) {w : ℕ} (hw : 1 ≤ w)
    (h : AnisoTorus.DA N β βp w ≤ 1 / 1000) :
    AnisoTorus.DA N β βp (w + 1) ≤ 250 * AnisoTorus.DA N β βp w ^ 2 := by
  have hx := DoublingSharp.positiveS_of_facts (factRepA hN hβ hβp hw)
  have e0 : Δ (xC (cA β βp) N (2 ^ w)) (corner 0) = AnisoTorus.DA N β βp w := by
    rw [Δ_xA, add_zero]
  have e1 : Δ (xC (cA β βp) N (2 ^ w)) (corner 0 + one) = AnisoTorus.DA N β βp (w + 1) := by
    rw [← corner_succ, Δ_xA, zero_add]
  have hr := DoublingSharp.rec_sharp hx (corner 0) (by rw [e0]; exact h)
  rwa [e1, e0] at hr

/-- **The basin contracts**: `DA(w+1) ≤ DA(w)/4`. Inherited: `1/4 = 250 · 1/1000`. DERIVED: `1` the least
window and the step; `1/1000` the seed of `DoublingSharp.rec_sharp`. -/
theorem DA_contracts (hN : N ≠ 0) {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) {w : ℕ} (hw : 1 ≤ w)
    (h : AnisoTorus.DA N β βp w ≤ 1 / 1000) :
    AnisoTorus.DA N β βp (w + 1) ≤ AnisoTorus.DA N β βp w / 4 := by
  have hs := DA_succ_le hN hβ hβp hw h
  have hnn := DA_nonneg hN hβ hβp hw
  nlinarith [mul_le_mul_of_nonneg_left h hnn]

/-- **Decay in the basin**: `DA(w+i) ≤ 4^{−i}/1000`. Inherited: `1/1000`, `1/4`. -/
theorem DA_decay (hN : N ≠ 0) {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) {w : ℕ} (hw : 1 ≤ w)
    (h : AnisoTorus.DA N β βp w ≤ 1 / 1000) (i : ℕ) :
    AnisoTorus.DA N β βp (w + i) ≤ (1 / 1000) * (1 / 4) ^ i := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have hp : (1 / 4 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hle : AnisoTorus.DA N β βp (w + i) ≤ 1 / 1000 := by nlinarith
    have hc := DA_contracts hN hβ hβp (show 1 ≤ w + i by omega) hle
    rw [show w + (i + 1) = w + i + 1 by omega, pow_succ]
    linarith

/-- **A basin window makes the anisotropic reading vanish** along the windows. Inherited: `1/1000`, `1/4`.
DERIVED: `0` the limit; `1` the least window; `1/1000` the seed of `DoublingSharp.rec_sharp`. -/
theorem tendsto_DA_of_seed (hN : N ≠ 0) {β βp : ℝ} (hβ : 0 ≤ β) (hβp : 0 ≤ βp) {c : ℕ} (hc : 1 ≤ c)
    (h : AnisoTorus.DA N β βp c ≤ 1 / 1000) :
    Tendsto (fun w => AnisoTorus.DA N β βp w) atTop (𝓝 0) := by
  have hu : Tendsto (fun b : ℕ => (1 / 1000 : ℝ) * (1 / 4) ^ (b - c)) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).comp (tendsto_sub_atTop_nat c)
    simpa using hp.const_mul (1 / 1000 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_ge_atTop c] with b hb
    exact DA_nonneg hN hβ hβp (hc.trans hb)
  · filter_upwards [eventually_ge_atTop c] with b hb
    have hd := DA_decay hN hβ hβp hc h (b - c)
    rwa [Nat.add_sub_of_le hb] at hd

/-- `β_⊥ ↦ ZC(cA β β_⊥)` is continuous, at every extent. No numeral. -/
theorem continuous_ZC_cA (β : ℝ) (L : Fin 4 → ℕ) : Continuous fun βp => ZC N (cA β βp) L := by
  have hcA : ∀ i j : Fin 4, Continuous fun p : ℝ × (RLink L → SUN.SU N) => cA β p.1 i j := by
    intro i j
    unfold cA
    exact continuous_if_const _ (fun _ => continuous_const) (fun _ => continuous_fst)
  have hf0 : Continuous fun p : ℝ × (RLink L → SUN.SU N) => Real.exp (-actC (cA β p.1) L p.2) := by
    refine Real.continuous_exp.comp (Continuous.neg ?_)
    unfold actC
    exact continuous_finsetSum _ fun q _ => (hcA q.1.1 q.1.2).mul
      (WilsonAction.continuous_wilsonDensity.comp ((continuous_hol q).comp continuous_snd))
  have hf : Continuous (Function.uncurry fun (βp : ℝ) (U : RLink L → SUN.SU N) =>
      Real.exp (-actC (cA β βp) L U)) := hf0
  have h := continuous_parametric_integral_of_continuous
    (μ := Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

/-- **At a fixed window, the anisotropic reading is continuous in `β_⊥`.** DERIVED: `16 = 2⁴` the copies;
`1` the next window. -/
theorem continuous_DA (β : ℝ) (w : ℕ) : Continuous fun βp => AnisoTorus.DA N β βp w := by
  have e : (fun βp => AnisoTorus.DA N β βp w) = fun βp =>
      16 * Real.log (ZC N (cA β βp) (fun _ => 2 ^ w))
        - Real.log (ZC N (cA β βp) (fun _ => 2 ^ (w + 1))) := by
    funext βp; unfold AnisoTorus.DA AnisoTorus.logZA; rw [ZA_eq, ZA_eq]
  rw [e]
  exact (continuous_const.mul ((continuous_ZC_cA β _).log fun _ => (ZC_pos N _ _).ne')).sub
    ((continuous_ZC_cA β _).log fun _ => (ZC_pos N _ _).ne')

end Window

/-! ## 8. The anchor -/

/-- **The decoupled end anchors the mixed coupling**: at `β ≥ 0`, `DA N β 0 · → 0` gives
`WeakMixAnchor N β`. A window `w₀ ≥ 1` with `DA(β, 0, w₀) < 1/1000`; continuity in `β_⊥` at `w₀`;
`tendsto_DA_of_seed` on `(0, b)`. Inherited: `1/1000` the seed. DERIVED: `0` the decoupled end; `1` the least
window. -/
theorem weakMixAnchor_of_decoupled {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (h0 : Tendsto (fun w => AnisoTorus.DA N β 0 w) atTop (𝓝 0)) : AnisoTorus.WeakMixAnchor N β := by
  obtain ⟨w₀, hlt, hw₀⟩ :=
    ((h0.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))).and
      (eventually_ge_atTop 1)).exists
  have hev : ∀ᶠ βp in 𝓝 (0 : ℝ), AnisoTorus.DA N β βp w₀ < 1 / 1000 :=
    ((continuous_DA β w₀).tendsto 0).eventually (eventually_lt_nhds hlt)
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨b, hb, fun βp hβp hβpb => ?_⟩
  have hd : dist βp 0 < b := by rw [Real.dist_0_eq_abs, abs_of_pos hβp]; exact hβpb
  exact tendsto_DA_of_seed hN hβ hβp.le hw₀ (hball hd).le

/-- **The 2D character expansion gives the mixed anchor**: `TwoDCharacter N β ⇒ WeakMixAnchor N β`, at
`β ≥ 0`. DERIVED: `0` the sign. -/
theorem weakMixAnchor_of_twoD {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hC : LayerSplit.TwoDCharacter N β) : AnisoTorus.WeakMixAnchor N β :=
  weakMixAnchor_of_decoupled hN hβ (DecoupledSplit.decoupled_vanishes_of_twoD hC)

/-- **The strong end from analyticity in `β_⊥` and the cited 2D character expansion**: frequently in `β`,
`AnisoAnalytic N β ∧ TwoDCharacter N β` gives `StrongEnd N`. DERIVED: `0` the sign. -/
theorem strongEnd_of_aniso_twoD {N : ℕ} (hN : N ≠ 0)
    (h : ∃ᶠ β in atTop, AnisoTorus.AnisoAnalytic N β ∧ LayerSplit.TwoDCharacter N β) :
    CouplingTower.StrongEnd N := by
  refine AnisoTorus.strongEnd_of_aniso ?_
  refine (h.and_eventually (eventually_ge_atTop 0)).mono ?_
  rintro β ⟨⟨hA, hC⟩, hβ⟩
  exact ⟨hA, weakMixAnchor_of_twoD hN hβ hC⟩

end MassGap.MixAnchor

#print axioms MassGap.MixAnchor.ZC_pos
#print axioms MassGap.MixAnchor.ZA_eq
#print axioms MassGap.MixAnchor.actC_Φ
#print axioms MassGap.MixAnchor.kC_symm
#print axioms MassGap.MixAnchor.kC_lower
#print axioms MassGap.MixAnchor.ZC_eq_cyc
#print axioms MassGap.MixAnchor.ZC_eq_traceSeq
#print axioms MassGap.MixAnchor.factRepC
#print axioms MassGap.MixAnchor.Δ_xA
#print axioms MassGap.MixAnchor.DA_nonneg
#print axioms MassGap.MixAnchor.DA_succ_le
#print axioms MassGap.MixAnchor.DA_decay
#print axioms MassGap.MixAnchor.tendsto_DA_of_seed
#print axioms MassGap.MixAnchor.continuous_DA
#print axioms MassGap.MixAnchor.weakMixAnchor_of_decoupled
#print axioms MassGap.MixAnchor.weakMixAnchor_of_twoD
#print axioms MassGap.MixAnchor.strongEnd_of_aniso_twoD
