import Mathlib
import MassGap.GapSideTwistFlat
import MassGap.CyclicKernel
import MassGap.CentreSectorSeedTwo

/-!
# MassGap.GapSideTwistBridge — the transfer-form twisted trace is the twisted torus partition function

The flux share `CentreSectorSeedN.fluxShareN` is written in the transfer formalism: the half-time
transfer `halfKN = kT^{∗(n/2)}` on the slice of a corner step, its trace `hs(halfKN)` and the twisted
traces `Z_g = FluxSectorBound.twist (halfKN) (act g) = ∫∫ a(x,y) a(x, g·y)`, `g ∈ Z_N³` the centre
acting on one slice (`SliceCentreAction.act`). The zero-action fact of `GapSideTwistFlat` is about
the twisted Wilson action of the full torus (`HolderBondMoving.twistField`). This module identifies
the two.

## The torus side

On the rectangular torus of extents `L`, sliced along `μ`, `tw L g` is the 't Hooft twist of `g`: the
plaquette `((μ, ν), x)` with `x_μ = L_μ − 1` and `x_ν = 0` carries the centre element `e(g_ν)`, the
plaquette `((ν, μ), x)` at the same site carries its inverse, every other plaquette `1`. `ZRtw L μ N β g`
is the Wilson partition function with the twist inserted, `∫ exp(−β Σ_q ρ(tw_q · U_q)) dU` (product
Haar on the links), so that `ZRtw` at `g = 0` is `RectWilson.ZR`.

## The bridge

* `cycTw_succ`, `twist_iter_eq_cycTw` (abstract): for a bounded symmetric kernel `a` and a measurable
  `σ`, `twist(a^{∗(j+1)}, σ)` is the periodic chain of `2j + 2` copies of `a` whose closing link is
  `a(x, σ y)`.
* `slice_sum_tw`, `action_tw`, `ZRtw_eq_integral`, `ZRtw_eq_cycTw`: in slice variables the twist
  sits on the temporal plaquettes between the last slice and the first, and equals the centre action on
  the first slice's spatial links (`e(g_ν)` is central; the `(ν, μ)` orientation is the inverse
  holonomy, so it carries the inverse element). Integrating the axis links gives `kT(V, g·V')` on
  that link, `kT(V, V')` elsewhere: `ZRtw = cycTw (Haar) kT (act g) L_μ`.
* **`twist_halfKN_eq`**: `twist(halfKN N β n i, act g) = ZRtw (ext n (pathV i)) i N β g`, and
  `hs_halfKN_eq`: `hs(halfKN N β n i) = ZR (ext n (pathV i)) N β`, at every `N ≥ 1`, `β ≥ 0`, even
  `n ≥ 2`, every corner step `i` and every `g ∈ Z_N³`. No normalisation constant appears: both sides
  use product Haar probability measure and the same Wilson density.
* **`twistRatioN_eq`**, **`fluxShareN_eq_ZRtw`**: `Z_g/Z = ZRtw/ZR`, and
  `fluxShareN = 1 − N⁻³ Σ_g ZRtw_g/ZR`.

## The cubic step and the `SU(2)` sheet

Step `0` is the cubic torus of side `n` (`ext_pathV_zero`), the torus of `HolderBondMoving`.
`twistRatioN_cubic`, `fluxShareN_cubic`: the same identities with `HolderBondMoving.ZF` of
`twistField β ρ (tw g)` over `ZF` of the uniform field. For `SU(2)` and `g` the basis vector at `ν`,
the twist is the 't Hooft sheet `sheetTwist 0 ν (0, 0) (−1)` moved one step along `0`
(`tw_single`); a translation of the twist leaves `ZF` unchanged (`ZF_comp_plaqShift`), so

    twistRatioN 2 β n 0 (e_ν) = ZF (twistField β ρ (sheetTwist 0 ν (0, 0) (−1))) / ZF (β ρ)
                                                                        (twistRatioN_sheet)

and that twisted action vanishes at `GapSideTwistFlat.flatCfg 0 ν (iσ₃) (iσ₂)`
(`twistedAction_sheetTwist_flat`, through `sheet_eq_sheetTwist`). So the zero-action configuration is a
configuration of the action whose partition function is the flux share's twisted trace.

Scope: an identity between two formalisms; no bound on any ratio. `ZRtw` puts `e(g_ν)` on the
`(μ, ν)` orientation and its inverse on `(ν, μ)`; `HolderBondMoving.sheetTwist` puts the same element on
both, so the two agree where `z² = 1`, the `SU(2)` case `twistRatioN_sheet` states.

DERIVED (module-wide): `L_μ − 1` is the last slice (the closing link of the cycle); `0` is the
coordinate of the multiplied links (`SliceCentreAction.lc`) and of the sheet; `2` is the size of
`SU(2)` and the halving `n = 2(n/2)`; `3` is the number of transverse directions (`N³`).
-/

noncomputable section

namespace MassGap.GapSideTwistBridge

open MeasureTheory MassGap MassGap.CompactGauge MassGap.KernelPower MassGap.CyclicKernel
open MassGap.RectWilson MassGap.RectTransfer
open MassGap.SliceCentreAction (Cen act lc mp_act sp_act)
open MassGap.TwistedTraceBoundN (cz coe_cz cz_zero)

local notation "wd" => WilsonAction.wilsonDensity

/-! ## 1. The twisted cycle of a kernel -/

/-- The closing step of a cycle of length `m`: `σ` at the last index, the identity elsewhere. -/
def twStep {X : Type*} (σ : X → X) (m : ℕ) (t : Fin m) (x : X) : X :=
  if t.val + 1 = m then σ x else x

section Cycle

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsProbabilityMeasure ρ]

/-- The periodic chain of `m` copies of `a` whose closing link is `a(x, σ y)`. -/
def cycTw (ρ : Measure X) (a : X → X → ℝ) (σ : X → X) (m : ℕ) : ℝ :=
  ∫ W : Fin m → X, ∏ t, a (W t) (twStep σ m t (W (finRotate m t))) ∂(Measure.pi fun _ => ρ)

/-- **The twisted cycle is a twisted diagonal of the iterate**: `cycTw (m+1) = ∫ a^{∗(m+1)}(y, σy)`. -/
theorem cycTw_succ {a : X → X → ℝ} (ha : Bdd a) {σ : X → X} (hσ : Measurable σ) (m : ℕ) :
    cycTw ρ a σ (m + 1) = ∫ y, iter ρ a m y (σ y) ∂ρ := by
  obtain ⟨C, hC⟩ := ha.bdd
  unfold cycTw
  have hmeas : Measurable fun W : Fin (m + 1) → X =>
      ∏ t, a (W t) (twStep σ (m + 1) t (W (finRotate (m + 1) t))) :=
    Finset.measurable_prod _ fun t _ => by
      have h1 : Measurable fun W : Fin (m + 1) → X => W t := measurable_pi_apply t
      have h2 : Measurable fun W : Fin (m + 1) → X => twStep σ (m + 1) t (W (finRotate (m + 1) t)) := by
        unfold twStep
        split_ifs
        · exact hσ.comp (measurable_pi_apply _)
        · exact measurable_pi_apply _
      simpa [Function.comp_def] using ha.meas.comp (h1.prodMk h2)
  rw [integral_cons hmeas (C := C ^ Fintype.card (Fin (m + 1))) (fun W => abs_prod_le fun t => hC _ _)]
  congr 1; funext y
  rw [← chain_eq_iter ha m y (σ y)]
  unfold chain
  congr 1; funext V
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  rcases Fin.eq_castSucc_or_eq_last t with ⟨s, rfl⟩ | rfl
  · have hs : ¬ ((Fin.castSucc s).val + 1 = m + 1) := by
      simp only [Fin.val_castSucc]; omega
    unfold twStep
    rw [if_neg hs, Fin.snoc_castSucc]
    have e := congrFun (Fin.snoc_eq_cons_rotate V y) (Fin.castSucc s)
    rw [Fin.snoc_castSucc] at e
    exact e.symm
  · unfold twStep
    rw [if_pos (by simp), finRotate_last, Fin.cons_zero, Fin.snoc_last]

/-- The twisted trace of an iterate is a twisted diagonal of the doubled iterate. -/
theorem twist_iter {a : X → X → ℝ} (ha : Bdd a) (hsy : ∀ x y, a x y = a y x) {σ : X → X}
    (hσ : Measurable σ) (j : ℕ) :
    FluxSectorBound.twist ρ (iter ρ a j) σ = ∫ y, iter ρ a (j + j + 1) y (σ y) ∂ρ := by
  have hb : Bdd (iter ρ a j) := ha.iter j
  obtain ⟨C, hC⟩ := hb.bdd
  have hF : Measurable (Function.uncurry fun x y => iter ρ a j x y * iter ρ a j x (σ y)) :=
    hb.meas.mul (hb.meas.comp (measurable_fst.prodMk (hσ.comp measurable_snd)))
  have hFb : ∀ x y, |iter ρ a j x y * iter ρ a j x (σ y)| ≤ C * C := fun x y => by
    rw [abs_mul]
    exact mul_le_mul (hC x y) (hC x (σ y)) (abs_nonneg _) ((abs_nonneg _).trans (hC x y))
  unfold FluxSectorBound.twist
  rw [swap_bdd hF hFb, iter_add ha j j]
  congr 1; funext y
  unfold conv
  congr 1; funext x
  rw [iter_symm (μ := ρ) ha hsy j y x]

/-- **The twisted trace is the twisted cycle**: `twist(a^{∗(j+1)}, σ) = cycTw (2j + 2)`. -/
theorem twist_iter_eq_cycTw {a : X → X → ℝ} (ha : Bdd a) (hsy : ∀ x y, a x y = a y x) {σ : X → X}
    (hσ : Measurable σ) (j : ℕ) :
    FluxSectorBound.twist ρ (iter ρ a j) σ = cycTw ρ a σ (j + j + 1 + 1) := by
  rw [cycTw_succ ha hσ, twist_iter ha hsy hσ]

end Cycle

/-! ## 2. The twisted torus -/

section Torus

variable {L : Fin 4 → ℕ} {μ : Fin 4} {N : ℕ} [NeZero N]

/-- The centre element commutes with every element. -/
theorem cz_comm (k : ZMod N) (h : SUN.SU N) : cz k * h = h * cz k := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, coe_cz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

/-- A central element on a temporal plaquette moves onto its later spatial link. -/
theorem wd_cz_time (k : ZMod N) (a v' b v : SUN.SU N) :
    wd (cz k * (a * v' * b⁻¹ * v⁻¹)) = wd (a * (cz k * v') * b⁻¹ * v⁻¹) := by
  have e : cz k * (a * v' * b⁻¹ * v⁻¹) = a * (cz k * v') * b⁻¹ * v⁻¹ := by
    simp only [mul_assoc]
    rw [← mul_assoc (cz k) a, cz_comm k a, mul_assoc]
  rw [e]

variable (L) in
/-- **The 't Hooft twist of `g ∈ Z_N³`** at the last slice along `μ`: `e(g_ν)` on `((μ, ν), x)` and its
inverse on `((ν, μ), x)` for `x_μ = L_μ − 1`, `x_ν = 0`; `1` elsewhere. -/
def tw (g : Cen μ N) (q : RPlaq L) : SUN.SU N :=
  if h : q.1.1 = μ ∧ q.1.2 ≠ μ then
    (if (q.2 μ).val + 1 = L μ then cz (lc g ((⟨q.1.2, h.2⟩, perp L μ q.2) : SpIdx L μ)) else 1)
  else if h' : q.1.2 = μ ∧ q.1.1 ≠ μ then
    (if (q.2 μ).val + 1 = L μ then (cz (lc g ((⟨q.1.1, h'.2⟩, perp L μ q.2) : SpIdx L μ)))⁻¹ else 1)
  else 1

variable (L μ N) in
/-- **The twisted Wilson partition function** of the rectangular torus. -/
def ZRtw (β : ℝ) (g : Cen μ N) : ℝ :=
  ∫ U : RLink L → SUN.SU N, Real.exp (-β * ∑ q, wd (tw L g q * (sysR L N).hol q U))
    ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))

theorem tw_μμ (g : Cen μ N) (x : RSite L) : tw L g ((μ, μ), x) = 1 := by
  simp [tw]

theorem tw_μν (g : Cen μ N) (t : Fin (L μ)) (y : TS L μ) (ν : {j : Fin 4 // j ≠ μ}) :
    tw L g ((μ, ν.1), join L μ t y) = if t.val + 1 = L μ then cz (lc g (ν, y)) else 1 := by
  simp [tw, ν.2]

theorem tw_νμ (g : Cen μ N) (t : Fin (L μ)) (y : TS L μ) (ν : {j : Fin 4 // j ≠ μ}) :
    tw L g ((ν.1, μ), join L μ t y) = if t.val + 1 = L μ then (cz (lc g (ν, y)))⁻¹ else 1 := by
  simp [tw, ν.2]

theorem tw_νν (g : Cen μ N) (x : RSite L) (ν ν' : {j : Fin 4 // j ≠ μ}) :
    tw L g ((ν.1, ν'.1), x) = 1 := by
  simp [tw, ν.2, ν'.2]

section Slice

variable (g : Cen μ N) (W : Fin (L μ) → SlIdx L μ → SUN.SU N) (t : Fin (L μ)) (y : TS L μ)
  (ν : {j : Fin 4 // j ≠ μ})

theorem d_μμ (U : RLink L → SUN.SU N) (x : RSite L) :
    wd (tw L g ((μ, μ), x) * (sysR L N).hol ((μ, μ), x) U) = 0 := by
  rw [tw_μμ, one_mul, hol_μμ, WilsonAction.wilsonDensity_one (NeZero.ne N)]

theorem d_μν :
    wd (tw L g ((μ, ν.1), join L μ t y) * (sysR L N).hol ((μ, ν.1), join L μ t y) (Φ L μ W))
      = wd (axisOf (W t) y * twStep (act g) (L μ) t (spOf (W (finRotate (L μ) t))) (ν, y)
        * (axisOf (W t) (tshift L μ ν y))⁻¹ * (spOf (W t) (ν, y))⁻¹) := by
  rw [tw_μν, hol_μν]
  unfold twStep
  split_ifs with h
  · exact wd_cz_time _ _ _ _ _
  · rw [one_mul]

theorem d_νμ :
    wd (tw L g ((ν.1, μ), join L μ t y) * (sysR L N).hol ((ν.1, μ), join L μ t y) (Φ L μ W))
      = wd (axisOf (W t) y * twStep (act g) (L μ) t (spOf (W (finRotate (L μ) t))) (ν, y)
        * (axisOf (W t) (tshift L μ ν y))⁻¹ * (spOf (W t) (ν, y))⁻¹) := by
  rw [tw_νμ, hol_νμ]
  unfold twStep
  split_ifs with h
  · rw [← mul_inv_rev, wilsonDensity_inv, ← cz_comm]
    exact wd_cz_time _ _ _ _ _
  · rw [one_mul, wilsonDensity_inv]

theorem d_νν (ν' : {j : Fin 4 // j ≠ μ}) :
    wd (tw L g ((ν.1, ν'.1), join L μ t y) * (sysR L N).hol ((ν.1, ν'.1), join L μ t y) (Φ L μ W))
      = wd (spOf (W t) (ν, y) * spOf (W t) (ν', tshift L μ ν y)
        * (spOf (W t) (ν, tshift L μ ν' y))⁻¹ * (spOf (W t) (ν', y))⁻¹) := by
  rw [tw_νν, one_mul, hol_νν]

/-- **The twisted action of one slice**: the twist acts on the next slice's spatial links in the
temporal plaquettes of the last slice. -/
theorem slice_sum_tw :
    ∑ i : Fin 4, ∑ j : Fin 4, ∑ y : TS L μ,
      wd (tw L g ((i, j), join L μ t y) * (sysR L N).hol ((i, j), join L μ t y) (Φ L μ W))
      = sp L μ (spOf (W t)) + 2 * tp L μ (axisOf (W t)) (spOf (W t))
          (twStep (act g) (L μ) t (spOf (W (finRotate (L μ) t)))) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ μ, Fintype.sum_eq_add_sum_subtype_ne _ μ]
  simp_rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => ∑ y : TS L μ,
    wd (tw L g ((_, j), join L μ t y) * (sysR L N).hol ((_, j), join L μ t y) (Φ L μ W))) μ]
  simp only [d_μμ, d_μν, d_νμ, d_νν, Finset.sum_const_zero, zero_add, Finset.sum_add_distrib]
  unfold sp tp spT tpT
  ring

end Slice

theorem action_tw (g : Cen μ N) (W : Fin (L μ) → SlIdx L μ → SUN.SU N) :
    ∑ q, wd (tw L g q * (sysR L N).hol q (Φ L μ W)) = ∑ t, (sp L μ (spOf (W t))
      + 2 * tp L μ (axisOf (W t)) (spOf (W t))
          (twStep (act g) (L μ) t (spOf (W (finRotate (L μ) t))))) := by
  have hsite : ∀ (F : RSite L → ℝ), ∑ x, F x = ∑ t : Fin (L μ), ∑ y : TS L μ, F (join L μ t y) := by
    intro F
    rw [← Fintype.sum_prod_type', ← (siteEquiv (L := L) (μ := μ)).sum_comp]
    rfl
  set D : Fin 4 → Fin 4 → RSite L → ℝ := fun i j x =>
    wd (tw L g ((i, j), x) * (sysR L N).hol ((i, j), x) (Φ L μ W))
  calc ∑ q, wd (tw L g q * (sysR L N).hol q (Φ L μ W)) = ∑ i, ∑ j, ∑ x, D i j x := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = ∑ i, ∑ j, ∑ t, ∑ y, D i j (join L μ t y) := by simp_rw [hsite]
    _ = ∑ i, ∑ t, ∑ j, ∑ y, D i j (join L μ t y) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, ∑ y, D i j (join L μ t y) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun t _ => slice_sum_tw g W t

omit [NeZero N] in
theorem continuous_hol (q : RPlaq L) : Continuous fun U : RLink L → SUN.SU N => (sysR L N).hol q U :=
  GibbsPositive.continuous_hol (G := SUN.SU N) (rbd L) q

theorem ZRtw_eq_integral (β : ℝ) (g : Cen μ N) :
    ZRtw L μ N β g = ∫ W : Fin (L μ) → SlIdx L μ → SUN.SU N, ∏ t, Real.exp (-β * (sp L μ (spOf (W t))
      + 2 * tp L μ (axisOf (W t)) (spOf (W t))
          (twStep (act g) (L μ) t (spOf (W (finRotate (L μ) t))))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)) := by
  have hmp := measurePreserving_Φ (L := L) (μ := μ) N
  have hc : Continuous fun U : RLink L → SUN.SU N =>
      Real.exp (-β * ∑ q, wd (tw L g q * (sysR L N).hol q U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun q _ =>
      WilsonAction.continuous_wilsonDensity.comp (continuous_const.mul (continuous_hol q))))
  unfold ZRtw
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hc.aestronglyMeasurable]
  congr 1; funext W
  rw [action_tw g W, Finset.mul_sum, Real.exp_sum]

theorem continuous_twStep (g : Cen μ N) {m : ℕ} (t : Fin m) {Y : Type*} [TopologicalSpace Y]
    {f : Y → SpIdx L μ → SUN.SU N} (hf : Continuous f) :
    Continuous fun q => twStep (act g) m t (f q) := by
  unfold twStep
  split_ifs
  · show Continuous fun q => fun l => cz (lc g l) * f q l
    exact continuous_pi fun l => continuous_const.mul ((continuous_apply l).comp hf)
  · exact hf

theorem spT_twStep (g : Cen μ N) {m : ℕ} (t : Fin m) (V : SpIdx L μ → SUN.SU N) :
    spT μ (tr L μ) (twStep (act g) m t V) = spT μ (tr L μ) V := by
  unfold twStep
  split_ifs
  · exact sp_act g V
  · rfl

/-- **The twisted torus is the twisted cycle of the transfer kernel.** -/
theorem ZRtw_eq_cycTw (hN : N ≠ 0) (β : ℝ) (g : Cen μ N) :
    ZRtw L μ N β g = cycTw (hS μ (tr L μ) N) (kT μ (tr L μ) N β) (act g) (L μ) := by
  rw [ZRtw_eq_integral β g]
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
    fun p => ∏ t, Real.exp (-β * (spT μ (tr L μ) (p.2 t)
      + 2 * tpT μ (tr L μ) (p.1 t) (p.2 t) (twStep (act g) (L μ) t (p.2 (finRotate (L μ) t)))))
  have hG : Continuous G := by
    refine continuous_finsetProd _ fun t _ => Real.continuous_exp.comp
      (continuous_const.mul ((continuous_sp ((continuous_apply t).comp continuous_snd)).add
        (continuous_const.mul (continuous_tp ((continuous_apply t).comp continuous_fst)
          ((continuous_apply t).comp continuous_snd)
          (continuous_twStep g t ((continuous_apply (finRotate (L μ) t)).comp continuous_snd))))))
  have h1 : ∫ W : Fin (L μ) → SlIdx L μ → SUN.SU N, ∏ t, Real.exp (-β * (sp L μ (spOf (W t))
      + 2 * tp L μ (axisOf (W t)) (spOf (W t))
          (twStep (act g) (L μ) t (spOf (W (finRotate (L μ) t))))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))
      = ∫ p, G p ∂((Measure.pi fun _ : Fin (L μ) => hA μ (tr L μ) N).prod
          (Measure.pi fun _ : Fin (L μ) => hS μ (tr L μ) N)) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [h1]
  have hGb : ∀ p, |G p| ≤ (Real.exp (|β| * (spMax μ (tr L μ) + 2 * tpMax μ (tr L μ))))
      ^ Fintype.card (Fin (L μ)) := by
    intro p
    refine abs_prod_le fun t => ?_
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have a1 := sp_nonneg hN (p.2 t)
    have a2 := sp_le hN (p.2 t)
    have a3 := tp_nonneg hN (p.1 t) (p.2 t) (twStep (act g) (L μ) t (p.2 (finRotate (L μ) t)))
    have a4 := tp_le hN (p.1 t) (p.2 t) (twStep (act g) (L μ) t (p.2 (finRotate (L μ) t)))
    have : -β * (spT μ (tr L μ) (p.2 t) + 2 * tpT μ (tr L μ) (p.1 t) (p.2 t)
          (twStep (act g) (L μ) t (p.2 (finRotate (L μ) t))))
        ≤ |β| * (spT μ (tr L μ) (p.2 t) + 2 * tpT μ (tr L μ) (p.1 t) (p.2 t)
          (twStep (act g) (L μ) t (p.2 (finRotate (L μ) t)))) := by
      have := neg_abs_le β
      nlinarith [abs_nonneg β]
    nlinarith [abs_nonneg β]
  rw [integral_prod_symm _ (integrable_of_bdd hG.measurable hGb)]
  unfold cycTw
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  have hprod := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin (L μ) => hA μ (tr L μ) N)
    (fun t (a : TS L μ → SUN.SU N) => Real.exp (-β * (spT μ (tr L μ) (V t)
      + 2 * tpT μ (tr L μ) a (V t) (twStep (act g) (L μ) t (V (finRotate (L μ) t))))))
  show ∫ A, ∏ t, Real.exp (-β * (spT μ (tr L μ) (V t)
      + 2 * tpT μ (tr L μ) (A t) (V t) (twStep (act g) (L μ) t (V (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => hA μ (tr L μ) N) = _
  rw [hprod]
  have hfac : ∀ t, ∫ a, Real.exp (-β * (spT μ (tr L μ) (V t)
      + 2 * tpT μ (tr L μ) a (V t) (twStep (act g) (L μ) t (V (finRotate (L μ) t)))))
      ∂(hA μ (tr L μ) N) = Real.exp (-β * spT μ (tr L μ) (V t))
        * gk μ (tr L μ) N β (V t) (twStep (act g) (L μ) t (V (finRotate (L μ) t))) := by
    intro t
    unfold gk
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]; ring_nf
  simp_rw [hfac]
  unfold kT
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hrot : ∏ t, Real.exp (-β * spT μ (tr L μ) (twStep (act g) (L μ) t (V (finRotate (L μ) t))) / 2)
      = ∏ t, Real.exp (-β * spT μ (tr L μ) (V t) / 2) := by
    simp only [spT_twStep]
    exact Fintype.prod_equiv (finRotate (L μ)) _ _ (fun t => rfl)
  rw [hrot]
  have hhalf : ∏ t, Real.exp (-β * spT μ (tr L μ) (V t))
      = (∏ t, Real.exp (-β * spT μ (tr L μ) (V t) / 2)) * ∏ t, Real.exp (-β * spT μ (tr L μ) (V t) / 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Real.exp_add]; ring_nf
  rw [hhalf]; ring

end Torus

/-! ## 3. The corner steps: twisted traces are twisted tori -/

section Corner

open MassGap.CentreSectorSeedN

variable {N : ℕ} [NeZero N]

theorem ext_pathV_self (n : ℕ) (i : Fin 4) :
    DoublingWilson.ext n (CentreSectorSeed.pathV i) i = n := by
  simp [DoublingWilson.ext, CentreSectorSeed.pathV_self]

/-- **The bridge**: the transfer-form twisted trace of a corner step is the twisted torus. -/
theorem twist_halfKN_eq {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (g : Cen i N) :
    FluxSectorBound.twist (hSN N n i) (halfKN N β n i) (act g)
      = ZRtw (DoublingWilson.ext n (CentreSectorSeed.pathV i)) i N β g := by
  have hN : N ≠ 0 := NeZero.ne N
  unfold halfKN
  rw [twist_iter_eq_cycTw (bdd_kT hN hβ) (kT_symm β) (mp_act g).measurable, ZRtw_eq_cycTw hN β g,
    ext_pathV_self]
  congr 1
  obtain ⟨k, rfl⟩ := he
  omega

/-- The trace of a corner step is the torus partition function. -/
theorem hs_halfKN_eq {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4) :
    hs (hSN N n i) (halfKN N β n i) = ZR (DoublingWilson.ext n (CentreSectorSeed.pathV i)) N β := by
  have hN : N ≠ 0 := NeZero.ne N
  have hL : DoublingWilson.ext n (CentreSectorSeed.pathV i) i = 2 * (n / 2) := by
    rw [ext_pathV_self]; obtain ⟨k, rfl⟩ := he; omega
  rw [ZR_eq_traceSeq (μ := i) (L := DoublingWilson.ext n (CentreSectorSeed.pathV i)) hN hβ (n / 2)
    (by omega) hL, ext_pathV_self]
  rfl

/-- **The twisted ratio is the ratio of twisted to untwisted torus partition functions.** -/
theorem twistRatioN_eq {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (g : Cen i N) :
    twistRatioN N β n i g = ZRtw (DoublingWilson.ext n (CentreSectorSeed.pathV i)) i N β g
      / ZR (DoublingWilson.ext n (CentreSectorSeed.pathV i)) N β := by
  unfold twistRatioN
  rw [twist_halfKN_eq hβ hn he i g, hs_halfKN_eq hβ hn he i]

/-- **The flux share in torus form**: `fluxShareN = 1 − N⁻³ Σ_g ZRtw_g / ZR`. -/
theorem fluxShareN_eq_ZRtw {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4) :
    fluxShareN N β n i = 1 - ((N : ℝ) ^ 3)⁻¹ * ∑ g : Cen i N,
      ZRtw (DoublingWilson.ext n (CentreSectorSeed.pathV i)) i N β g
        / ZR (DoublingWilson.ext n (CentreSectorSeed.pathV i)) N β := by
  rw [fluxShareN_eq_mean hβ n i]
  simp_rw [twistRatioN_eq hβ hn he i]

end Corner

/-! ## 4. The cubic step in the `HolderBondMoving` formalism, and the `SU(2)` sheet -/

section Cubic

open MassGap.HolderBondMoving MassGap.CentreSectorSeedN

theorem ext_pathV_zero (n : ℕ) : DoublingWilson.ext n (CentreSectorSeed.pathV 0) = fun _ => n := by
  funext j
  fin_cases j <;> simp [DoublingWilson.ext, CentreSectorSeed.pathV]

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem ZR_cubic (n : ℕ) (β : ℝ) :
    ZR (fun _ => n) N β = ZF (d := 4) (N := n) (probHaar (SUN.SU N)) (fun _ g => β * wd g) := by
  rw [← TorusDoubling.ZT_four_eq, ZT_eq_ZF]

theorem fAct_tw_cubic (n : ℕ) (β : ℝ) (g : Cen 0 N) (U : TorusDoubling.TLink 4 n → SUN.SU N) :
    ∑ q : TorusDoubling.TPlaq 4 n, β * wd (tw (fun _ => n) g q * thol q U)
      = β * ∑ q : RPlaq (fun _ => n), wd (tw (fun _ => n) g q * (sysR (fun _ => n) N).hol q U) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, j⟩, x⟩ := q
  rw [RectWilson.hol_eq]
  rfl

/-- The twisted torus of step `0` is `HolderBondMoving.ZF` of the twisted field. -/
theorem ZRtw_cubic (n : ℕ) (β : ℝ) (g : Cen 0 N) :
    ZRtw (fun _ => n) 0 N β g
      = ZF (d := 4) (N := n) (probHaar (SUN.SU N)) (twistField β wd (tw (fun _ => n) g)) := by
  unfold ZRtw ZF fAct twistField
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [fAct_tw_cubic, neg_mul]

theorem twistRatioN_cubic {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (g : Cen 0 N) :
    twistRatioN N β n 0 g
      = ZF (d := 4) (N := n) (probHaar (SUN.SU N)) (twistField β wd (tw (fun _ => n) g))
        / ZF (d := 4) (N := n) (probHaar (SUN.SU N)) (fun _ g => β * wd g) := by
  rw [twistRatioN_eq hβ hn he 0 g, ext_pathV_zero, ZRtw_cubic, ZR_cubic]

/-- **The flux share of step `0` in the `HolderBondMoving` formalism.** -/
theorem fluxShareN_cubic {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    fluxShareN N β n 0 = 1 - ((N : ℝ) ^ 3)⁻¹ * ∑ g : Cen 0 N,
      ZF (d := 4) (N := n) (probHaar (SUN.SU N)) (twistField β wd (tw (fun _ => n) g))
        / ZF (d := 4) (N := n) (probHaar (SUN.SU N)) (fun _ g => β * wd g) := by
  rw [fluxShareN_eq_mean hβ n 0]
  simp_rw [twistRatioN_cubic hβ hn he]

/-- A translation of the field leaves `ZF` unchanged. -/
theorem ZF_comp_plaqShift {G : Type} [Group G] [MeasurableSpace G] (ρ : Measure G)
    [IsProbabilityMeasure ρ] {d n : ℕ} (κ : Fin d) (Ψ : TorusDoubling.TPlaq d n → G → ℝ) :
    ZF ρ (fun q => Ψ (plaqShift κ q)) = ZF ρ Ψ := by
  unfold ZF
  rw [← (shiftCfg_measurePreserving ρ κ).integral_comp'
    (fun U => Real.exp (-fAct (fun q => Ψ (plaqShift κ q)) U))]
  congr 1; funext U
  show Real.exp (-fAct (fun q => Ψ (plaqShift κ q)) (shiftCfg κ U)) = Real.exp (-fAct Ψ U)
  unfold fAct
  simp only [thol_shiftCfg]
  rw [Equiv.sum_comp (plaqShift κ) (fun p => Ψ p (thol p U))]

theorem finRotate_eq_zero_iff {n : ℕ} [NeZero n] (y : Fin n) : finRotate n y = 0 ↔ y.val + 1 = n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  by_cases h : y = Fin.last m
  · subst h; simp
  · rw [Fin.ext_iff, coe_finRotate_of_ne_last h, Fin.val_zero]
    have hy : y.val ≠ m := fun e => h (Fin.ext (by rw [Fin.val_last]; exact e))
    omega

open MassGap.TwistedTraceBound (negOne) in
theorem cz_one_two : cz (1 : ZMod 2) = negOne := by
  apply Subtype.ext
  rw [coe_cz, TwistedTraceBound.coe_negOne, CentreSectorSeedTwo.stdAddChar_one_two, neg_one_smul]

open MassGap.TwistedTraceBound (negOne) in
/-- **For `SU(2)` the twist of a basis vector is the 't Hooft sheet**, moved one step along `0`. -/
theorem tw_single {n : ℕ} [NeZero n] (ν : {j : Fin 4 // j ≠ 0}) (q : TorusDoubling.TPlaq 4 n) :
    tw (fun _ => n) (μ := 0) (Pi.single ν (1 : ZMod 2)) q
      = sheetTwist 0 ν.1 ((0, 0) : Fin n × Fin n) negOne (plaqShift 0 q) := by
  obtain ⟨⟨a, b⟩, x⟩ := q
  have hr : TorusDoubling.tshift (0 : Fin 4) x 0 = 0 ↔ (x 0).val + 1 = n := by
    unfold TorusDoubling.tshift
    rw [Function.update_self]
    exact finRotate_eq_zero_iff (x 0)
  have hν : TorusDoubling.tshift (0 : Fin 4) x ν.1 = x ν.1 := tshift_apply_ne ν.2 x
  have hz : ∀ s : Fin n, s = 0 ↔ s.val = 0 := fun s => by rw [Fin.ext_iff, Fin.val_zero]
  have hninv : negOne⁻¹ = negOne := GapSideTwistFlat.negOne_inv
  simp only [sheetTwist, plaqShift_apply, hν]
  unfold tw
  by_cases h : a = 0 ∧ b ≠ 0
  · rw [dif_pos h]
    obtain ⟨rfl, hb⟩ := h
    by_cases hbν : b = ν.1
    · subst hbν
      have hsub : (⟨ν.1, hb⟩ : {j : Fin 4 // j ≠ 0}) = ν := rfl
      simp only [lc, perp, hsub, Pi.single_eq_same, true_or, true_and, hr, hz]
      by_cases h0 : (x 0).val + 1 = n <;> by_cases hx : (x ν.1).val = 0 <;>
        simp [h0, hx, cz_one_two, cz_zero]
    · have hne : (⟨b, hb⟩ : {j : Fin 4 // j ≠ 0}) ≠ ν := fun e => hbν (congrArg Subtype.val e)
      have hc : ¬ (((0 : Fin 4), b) = (0, ν.1) ∨ ((0 : Fin 4), b) = (ν.1, 0)) := by
        rintro (e | e)
        · exact hbν (Prod.mk.inj e).2
        · exact ν.2 (Prod.mk.inj e).1.symm
      simp only [lc, perp, Pi.single_eq_of_ne hne, ite_self, cz_zero, hc, false_and, if_false]
  · rw [dif_neg h]
    by_cases h' : b = 0 ∧ a ≠ 0
    · rw [dif_pos h']
      obtain ⟨rfl, ha⟩ := h'
      by_cases haν : a = ν.1
      · subst haν
        have hsub : (⟨ν.1, ha⟩ : {j : Fin 4 // j ≠ 0}) = ν := rfl
        simp only [lc, perp, hsub, Pi.single_eq_same, or_true, true_and, hr, hz]
        by_cases h0 : (x 0).val + 1 = n <;> by_cases hx : (x ν.1).val = 0 <;>
          simp [h0, hx, cz_one_two, cz_zero, hninv]
      · have hne : (⟨a, ha⟩ : {j : Fin 4 // j ≠ 0}) ≠ ν := fun e => haν (congrArg Subtype.val e)
        have hc : ¬ ((a, (0 : Fin 4)) = (0, ν.1) ∨ (a, (0 : Fin 4)) = (ν.1, 0)) := by
          rintro (e | e)
          · exact ν.2 (Prod.mk.inj e).2.symm
          · exact haν (Prod.mk.inj e).1
        simp only [lc, perp, Pi.single_eq_of_ne hne, ite_self, cz_zero, inv_one, hc, false_and,
          if_false]
    · rw [dif_neg h']
      have hc : ¬ ((a, b) = (0, ν.1) ∨ (a, b) = (ν.1, 0)) := by
        rintro (e | e)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
          exact h ⟨rfl, ν.2⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
          exact h' ⟨rfl, ν.2⟩
      simp only [hc, false_and, if_false]

open MassGap.TwistedTraceBound (negOne) in
/-- **The `SU(2)` twisted ratio of a basis vector is the sheet-twisted `ZF` ratio.** The twist is the
't Hooft sheet in the planes `(0, ν)` at `x₀ = x_ν = 0`, `−1` on both orientations. -/
theorem twistRatioN_sheet {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n] (hn : 2 ≤ n) (he : Even n)
    (ν : {j : Fin 4 // j ≠ 0}) :
    twistRatioN 2 β n 0 (Pi.single ν 1)
      = ZF (d := 4) (N := n) (probHaar (SUN.SU 2))
          (twistField β wd (sheetTwist 0 ν.1 ((0, 0) : Fin n × Fin n) negOne))
        / ZF (d := 4) (N := n) (probHaar (SUN.SU 2)) (fun _ g => β * wd g) := by
  rw [twistRatioN_cubic hβ hn he]
  congr 1
  rw [← ZF_comp_plaqShift (probHaar (SUN.SU 2)) (0 : Fin 4)
    (twistField β wd (sheetTwist 0 ν.1 ((0, 0) : Fin n × Fin n) negOne))]
  congr 1
  funext q g
  show β * wd (tw (fun _ => n) (μ := 0) (Pi.single ν (1 : ZMod 2)) q * g)
    = β * wd (sheetTwist 0 ν.1 ((0, 0) : Fin n × Fin n) negOne (plaqShift 0 q) * g)
  rw [tw_single ν q]

/-- `GapSideTwistFlat.sheet` is `sheetTwist` at in-plane position `(0, 0)`. -/
theorem sheet_eq_sheetTwist {G : Type} [Group G] {d n : ℕ} [NeZero n] (i j : Fin d) (z : G)
    (q : TorusDoubling.TPlaq d n) :
    GapSideTwistFlat.sheet i j z q = sheetTwist i j ((0, 0) : Fin n × Fin n) z q := by
  unfold GapSideTwistFlat.sheet sheetTwist
  simp only [Fin.ext_iff, Fin.val_zero]

open MassGap.TwistedTraceBound (negOne) in
/-- **The twisted action of the flux share's sheet vanishes at the flat `SU(2)` configuration.** -/
theorem twistedAction_sheetTwist_flat {d n : ℕ} [NeZero n] {i j : Fin d} (hij : i ≠ j) (β : ℝ) :
    fAct (twistField β wd (sheetTwist i j ((0, 0) : Fin n × Fin n) negOne))
      (GapSideTwistFlat.flatCfg (N := n) i j GapSideTwistFlat.sigA GapSideTwistFlat.sigB) = 0 := by
  have e : sheetTwist i j ((0, 0) : Fin n × Fin n) negOne = GapSideTwistFlat.sheet i j negOne :=
    funext fun q => (sheet_eq_sheetTwist i j negOne q).symm
  rw [e]
  exact GapSideTwistFlat.twistedAction_flat_SU2 hij β

end Cubic

end MassGap.GapSideTwistBridge

#print axioms MassGap.GapSideTwistBridge.cycTw_succ
#print axioms MassGap.GapSideTwistBridge.twist_iter_eq_cycTw
#print axioms MassGap.GapSideTwistBridge.slice_sum_tw
#print axioms MassGap.GapSideTwistBridge.action_tw
#print axioms MassGap.GapSideTwistBridge.ZRtw_eq_cycTw
#print axioms MassGap.GapSideTwistBridge.twist_halfKN_eq
#print axioms MassGap.GapSideTwistBridge.hs_halfKN_eq
#print axioms MassGap.GapSideTwistBridge.twistRatioN_eq
#print axioms MassGap.GapSideTwistBridge.fluxShareN_eq_ZRtw
#print axioms MassGap.GapSideTwistBridge.twistRatioN_cubic
#print axioms MassGap.GapSideTwistBridge.fluxShareN_cubic
#print axioms MassGap.GapSideTwistBridge.ZF_comp_plaqShift
#print axioms MassGap.GapSideTwistBridge.tw_single
#print axioms MassGap.GapSideTwistBridge.twistRatioN_sheet
#print axioms MassGap.GapSideTwistBridge.twistedAction_sheetTwist_flat
