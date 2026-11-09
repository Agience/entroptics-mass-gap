import Mathlib
import MassGap.GenerationN
import MassGap.PlaquetteFloor

/-!
# MassGap.ScaleIdentityNoGo — the scale clause fails at the identity flow

`ConstFlowN` shows that its field-level obstruction `NonMemConstF (sunFam … s₀)` fails at `c = 0` and at
`s₀ = 0`, where the observer `sunFam … s₀` is the identity at every step. This module closes that escape
through the `scale` field of `SU2Best.SubstrateCoreAt`: a substrate whose physical-scale flow `Wf b` is the
identity at every step does not exist. This excludes the identity observer from this route's
`SubstrateCoreAt` bundle; it says nothing about the observer of the target statement. Declarations are in the namespace `MassGap.ScaleIdentityNoGo`.

## 1. The plaquette mean in physical units diverges (proved)

**`tendsto_plaq_div`**: at `N ≥ 2`, `ν_k(1 − Re tr U_q / N) / a_k⁴ → ∞` at the plaquette
`q = ((0, 1), 0)` (`PlaquetteFloor.qo`). The floor is `PlaquetteFloor.stateK_plaq_ge`,
`ν_k(1 − Re tr U_q / N) ≥ c / β_k²` with `c > 0` (a single-link heat-bath bound at every volume and
boundary condition, passed to the periodic state by the DLR equations). `ExistenceFlow.exp_le_inv_pow` puts
`c / β_k²` above `c e^{−λ β_k}` at `λ = 48π²/(11N²)`, and `FlowMoments.rate_of_expFloor` compares that with
`a_k⁴ = aRun N (β_k)⁴`, whose exponential rate is `96π²/(11N²)`.

## 2. The scale clause at an identity step (proved)

**`one_add_le_of_scaleAt`**: if `(Wf s).V k = id`, `t > 0`, `s > 0` and `ScaleAt Wf t C γ γP k s`, then at
every plaquette `q`

  `1 + μ(s) a_k⁻⁴ · ν_k(1 − Re tr U_q / N) ≤ C`,  `μ(s) = t s⁴ / (1 + |log s|)^{γP}`.

The plaquette channel `Sum.inr q` of `ScaleAt` reads `ν_k(exp(μ(s) a_k⁻⁴ |sym plaq_q ∘ V_k|))`. At
`V_k = id` the field is `sym plaq_q` (`fieldMap_apply_of_id`), which dominates `plaq_q ≥ 0` (`FlowMoments.plaq_le_sym`), and
`1 + x ≤ eˣ`. No Jensen step and no exponential-moment estimate is needed: the first-order term already
diverges.

## 3. The no-go (proved)

* **`not_scaleControlAll_of_id`**: at `N ≥ 2`, `b > 0` and `(Wf b).V k = id` for all large `k`,
  `ScaleControlAll b Wf` is false. `ScaleControlAll` gives `ScaleAt` at `s = b` once `a_k ≤ b`, and
  §2 with §1 makes the left side unbounded.
* **`not_substrateCoreAt_of_id`**: `SubstrateCoreAt W z b Wf` is false whenever `W.V k = id` for all large
  `k` (through `top : Wf b = W`).
* **`not_substrateCoreAt_identity`**: at `W = ConfFlow.identity N`.
* **`not_substrateCoreAt_sunFam_zero`**: at `W = sunFam hN2 c hc0 hc 0`, every `c`
  (`ObserverFlowSUN.sunFam_V_of_lt`: `0 < a_k`).
* At `c = 0` and any `s₀`, `ConstFlowN.sunFam_V_of_c_zero` gives `(sunFam hN2 c hc0 hc s₀).V k = id` at
  every step, so `not_substrateCoreAt_of_id` applies there as well. This module does not import the
  unrooted `ConstFlowN`; the corollary is `not_substrateCoreAt_of_id hN2 (Eventually.of_forall fun k =>
  ConstFlowN.sunFam_V_of_c_zero hN2 hc0 hc h s₀ k) z b Wf`.

So the escape of `ConstFlowN` §5 is closed: a `ClayNarrow.NarrowInputsN` witness (any `Wf`) needs `c > 0` and
`s₀ > 0`, the region where `NonMemConstF` is open. Whether `ScaleControlAll` holds for any non-identity flow
is not shown here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plaquette's directions and site, the scale and the coupling; `1` the second
direction, the unit observable and the floor threshold; `2` the least colour count and the power of `β`;
`4` the dimension of the plaquette density; `48 = 96/2` half the exponential rate of `a⁴`, `96` and `11`
`aRun`'s; `16` the factor of the plaquette floor.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScaleIdentityNoGo

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverEnergyMoments MassGap.ObserverSymField MassGap.ObserverEnergyBox
  MassGap.MultiScaleAll MassGap.SU2Best MassGap.ObserverFlowSUN MassGap.CompositesBuild MassGap.ClayData

variable {N : ℕ}

/-! ## 1. The plaquette mean in physical units -/

/-- **The plaquette mean in physical units diverges**: `ν_k(1 − Re tr U_q / N) / a_k⁴ → ∞` at
`q = ((0, 1), 0)`, `N ≥ 2`. DERIVED: `2` the least colour count and the power of `β`; `4` the dimension;
`48 = 96/2`, `96`, `11` `aRun`'s; `16` the floor's. -/
theorem tendsto_plaq_div (hN2 : 2 ≤ N) [NeZero N] :
    Tendsto (fun k => stateK (NeZero.ne N) k (plaqField (N := N) PlaquetteFloor.qo).1
      / dySpacing N k ^ 4) atTop atTop := by
  have hN : N ≠ 0 := NeZero.ne N
  have hq : PlaquetteFloor.qo.1.1 ≠ PlaquetteFloor.qo.1.2 := by decide
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hc : 0 < Real.exp (-(((MassGap.GibbsSpec.boundaryPlaqs
      {(PlaquetteFloor.qo.1.1, PlaquetteFloor.qo.2)}).card : ℝ) * (16 / N + 2))) / N :=
    div_pos (Real.exp_pos _) hN0
  have hlam : (0 : ℝ) < 48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) := by positivity
  have hlt : 48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) < 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) := by
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith [Real.pi_pos]
  refine FlowMoments.rate_of_expFloor hN hc hlt ?_
  filter_upwards [(tendsto_dyBeta (one_le_of_ne_zero hN)).eventually
    (ExistenceFlow.exp_le_inv_pow hlam 2)] with k hk2
  refine le_trans ?_ (PlaquetteFloor.stateK_plaq_ge hN2 hN PlaquetteFloor.qo hq k)
  calc _ ≤ Real.exp (-(((MassGap.GibbsSpec.boundaryPlaqs
          {(PlaquetteFloor.qo.1.1, PlaquetteFloor.qo.2)}).card : ℝ) * (16 / N + 2))) / N
          * (1 / dyBeta (one_le_of_ne_zero hN) k ^ 2) := mul_le_mul_of_nonneg_left hk2 hc.le
    _ = _ := by ring

/-! ## 2. The scale clause at an identity step -/

/-- **An identity step reads the field itself.** DERIVED: no numeral. -/
theorem fieldMap_apply_of_id (W : ConfFlow N) (k : ℕ) (hid : W.V k = id)
    (O : LField (MassGap.SUN.SU N)) (U : Cfg N) : (W.fieldMap k O).1 U = O.1 U := by
  show O.1 (W.V k U) = O.1 U
  rw [hid]
  rfl

/-- **The plaquette channel of `ScaleAt` at an identity step**: `1 + μ(s) a_k⁻⁴ ν_k(plaq_q) ≤ C`.
DERIVED: `0` the signs; `1` the unit observable; `4` the dimension. -/
theorem one_add_le_of_scaleAt [NeZero N] {Wf : ℝ → ConfFlow N} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    {k : ℕ} {s : ℝ} (ht : 0 < t) (hs : 0 < s) (hid : (Wf s).V k = id)
    (h : ScaleAt Wf t C γ γP k s) (q : MassGap.GibbsSpec.IPlaq) :
    1 + msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4 * stateK (NeZero.ne N) k (plaqField (N := N) q).1
      ≤ C := by
  have hN : N ≠ 0 := NeZero.ne N
  have hlam0 : 0 ≤ msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4 :=
    div_nonneg (msMu_pos ht γ γP hs (Sum.inr q)).le
      (pow_pos (dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k) 4).le
  have hj := h (Sum.inr q)
  have hd : mDim (Sum.inr q) = 4 := mDim_inr q
  rw [hd] at hj
  have hmono : stateK hN k ((1 : C(Cfg N, ℝ))
        + (msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4) • (plaqField (N := N) q).1)
      ≤ stateK hN k (expC ((msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4)
          • msAbs ((Wf s).fieldMap k (mField (Sum.inr q))).1)) := by
    refine (stateK hN k).mono fun U => ?_
    have hf : ((Wf s).fieldMap k (mField (Sum.inr q))).1 U = (sym (plaqField (N := N) q)).1 U := by
      rw [fieldMap_apply_of_id (Wf s) k hid, mField_inr]
    have hp : (plaqField (N := N) q).1 U ≤ |(sym (plaqField (N := N) q)).1 U| :=
      (FlowMoments.plaq_le_sym hN q U).trans (le_abs_self _)
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul,
      expC_apply, msAbs_apply, hf]
    have := Real.add_one_le_exp
      (msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4 * |(sym (plaqField (N := N) q)).1 U|)
    nlinarith [mul_le_mul_of_nonneg_left hp hlam0]
  rw [(stateK hN k).map_add, (stateK hN k).map_smul, (stateK hN k).map_one] at hmono
  exact hmono.trans hj

/-! ## 3. The no-go -/

/-- **`ScaleControlAll` fails when the flow to the physical scale is eventually the identity**, `N ≥ 2`.
DERIVED: `0` the scale; `1` the unit observable; `2` the least colour count; `4` the dimension. -/
theorem not_scaleControlAll_of_id (hN2 : 2 ≤ N) [NeZero N] {b : ℝ} (hb : 0 < b)
    {Wf : ℝ → ConfFlow N} (hid : ∀ᶠ k in atTop, (Wf b).V k = id) : ¬ ScaleControlAll b Wf := by
  rintro ⟨t, C, γ, γP, ht, hev⟩
  have hmu : 0 < msMu t γ γP (Sum.inr PlaquetteFloor.qo) b := msMu_pos ht γ γP hb _
  have hsmall : ∀ᶠ k in atTop, dySpacing N k ≤ b :=
    (tendsto_dySpacing N).eventually (eventually_le_nhds hb)
  have hbig := (tendsto_plaq_div (N := N) hN2).const_mul_atTop hmu
  have hbig' := hbig.eventually (eventually_gt_atTop C)
  obtain ⟨k, hk, hid, hsm, hgt⟩ := (hev.and (hid.and (hsmall.and hbig'))).exists
  have h := one_add_le_of_scaleAt ht hb hid (hk b hsm le_rfl) PlaquetteFloor.qo
  have hnn : 0 ≤ stateK (NeZero.ne N) k (plaqField (N := N) PlaquetteFloor.qo).1 :=
    (stateK (NeZero.ne N) k).nonneg' _ fun U =>
      MassGap.WilsonAction.wilsonDensity_nonneg (NeZero.ne N) _
  have e : msMu t γ γP (Sum.inr PlaquetteFloor.qo) b / dySpacing N k ^ 4
        * stateK (NeZero.ne N) k (plaqField (N := N) PlaquetteFloor.qo).1
      = msMu t γ γP (Sum.inr PlaquetteFloor.qo) b
        * (stateK (NeZero.ne N) k (plaqField (N := N) PlaquetteFloor.qo).1 / dySpacing N k ^ 4) := by
    ring
  have hgt2 : C < msMu t γ γP (Sum.inr PlaquetteFloor.qo) b
      * (stateK (NeZero.ne N) k (plaqField (N := N) PlaquetteFloor.qo).1 / dySpacing N k ^ 4) := hgt
  linarith

/-- **No substrate core at an eventually-identity observer**: `SubstrateCoreAt W z b Wf` is false when
`W.V k = id` for all large `k`, `N ≥ 2`. DERIVED: `2` the least colour count. -/
theorem not_substrateCoreAt_of_id (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N}
    (hW : ∀ᶠ k in atTop, W.V k = id) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    ¬ SubstrateCoreAt W z b Wf := fun S =>
  not_scaleControlAll_of_id hN2 S.b_pos (by rw [S.top]; exact hW) S.scale

/-- **No substrate core at the identity flow.** DERIVED: `2` the least colour count. -/
theorem not_substrateCoreAt_identity (hN2 : 2 ≤ N) [NeZero N] (z : Chan → ℕ → ℝ) (b : ℝ)
    (Wf : ℝ → ConfFlow N) : ¬ SubstrateCoreAt (ConfFlow.identity N) z b Wf :=
  not_substrateCoreAt_of_id hN2 (Eventually.of_forall fun _ => rfl) z b Wf

/-- **No substrate core at `sunFam … 0`**, every `c`. DERIVED: `0` the scale of the observer; `1` the least
colour count of the spacing; `2` the least colour count; `12` as in
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_substrateCoreAt_sunFam_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    ¬ SubstrateCoreAt (sunFam hN2 c hc0 hc 0) z b Wf :=
  not_substrateCoreAt_of_id hN2 (Eventually.of_forall fun k =>
    sunFam_V_of_lt hN2 hc0 hc le_rfl (dySpacing_pos (by omega) k)) z b Wf

end MassGap.ScaleIdentityNoGo

end

#print axioms MassGap.ScaleIdentityNoGo.tendsto_plaq_div
#print axioms MassGap.ScaleIdentityNoGo.fieldMap_apply_of_id
#print axioms MassGap.ScaleIdentityNoGo.one_add_le_of_scaleAt
#print axioms MassGap.ScaleIdentityNoGo.not_scaleControlAll_of_id
#print axioms MassGap.ScaleIdentityNoGo.not_substrateCoreAt_of_id
#print axioms MassGap.ScaleIdentityNoGo.not_substrateCoreAt_identity
#print axioms MassGap.ScaleIdentityNoGo.not_substrateCoreAt_sunFam_zero
