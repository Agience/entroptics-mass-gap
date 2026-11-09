import Mathlib
import MassGap.ScaleSatisfiable
import MassGap.ObserverChoice

/-!
# MassGap.SunFamLeak — the scale clause reduces to one plaquette rate at any observer

`ScaleSatisfiable.scaleControlAll_one_iff` shows that, through the `top` field, the `scale` field of the
substrate reads the observer `W` itself. This module isolates the one statement on `W` that decides the
`scale` field negatively, at any observer and any `b`, `Wf`: a plaquette whose flowed mean is not
`O(a_k⁴)`. Declarations are in the namespace `MassGap.SunFamLeak`.

## 1. The plaquette channel at any flow (proved)

**`one_add_le_of_scaleAt`**: if `ScaleAt Wf t C γ γP k s` with `t > 0`, `s > 0`, then at every plaquette `q`

  `1 + μ(s) a_k⁻⁴ · ν_k(sym plaq_q ∘ (Wf s).V k) ≤ C`,  `μ(s) = t s⁴ / (1 + |log s|)^{γP}`,

by `x ≤ |x|` and `1 + x ≤ eˣ`. `ScaleIdentityNoGo.one_add_le_of_scaleAt` is the case `(Wf s).V k = id`.

## 2. The leak predicate and the no-go (proved)

* **`PlaqLeak W`**: some plaquette `q` has `ν_k(sym plaq_q ∘ W.V k) / a_k⁴` unbounded above along the
  steps (for every `K`, frequently `> K`).
* **`not_scaleControlAll_of_plaqLeak`**: `b > 0` and `PlaqLeak (Wf b)` give `¬ ScaleControlAll b Wf`.
* **`not_substrateCoreAt_of_plaqLeak`**: `PlaqLeak W` gives `¬ SU2Best.SubstrateCoreAt W z b Wf` for every
  `z`, `b`, `Wf` (through `top`).
* **`not_multiScaleStrongAt_of_plaqLeak`**: the same for the `SU(2)` bundle
  `StrongExpand.MultiScaleStrongAt W z μ b Wf cf` (fields `b_pos`, `top`, `scale`).
* **`plaqLeak_of_id`**: an eventually-identity flow leaks (`ScaleIdentityNoGo.tendsto_plaq_div`), so
  `ScaleIdentityNoGo.not_substrateCoreAt_of_id` is the case `W.V k = id` of §2.
* **`not_substrateCoreAt_sunFam_of_leak`**, **`not_multiScaleStrongAt_obsW_of_leak`**: the two observers of
  the capstones, `ObserverFlowSUN.sunFam hN2 c hc0 hc s₀` (`ClayNarrow.NarrowInputsN`) and
  `ObserverChoice.obsW = FlowZero.apeFam (1/12) 1` (the `SU(2)` capstones).

Conversely `¬ PlaqLeak W` is necessary for the bundle at every `b` (the contrapositive of
`not_substrateCoreAt_of_plaqLeak` and `not_multiScaleStrongAt_of_plaqLeak`); at `b = 1` `(M_W)`
(`ScaleSatisfiable.scaleControlAll_one_iff`) gives the explicit bound `(C − 1) a_k⁴ / t` on every plaquette mean. `PlaqLeak` is the plaquette channel only;
the monomial channels add further conditions.

## 3. The open statement

`PlaqLeak (sunFam hN2 c hc0 hc s₀)` at `c > 0`, `s₀ > 0`, and `PlaqLeak obsW`, are not proved. Both observers
are `n = ⌊(s/a_k)²⌋` smearing steps (polar block steps for `sunFam`, APE steps for `obsW`) inside the midpoint box of half-width `R = ⌊s/a_k⌋` around each output link,
the links outside the box held at their bare values (`ObserverFlowSUN.obsFlowG`, `ObserverFlow.obsFlow`). The
estimate in the docstring of `ScaleSatisfiable` §3 gives the held boundary a weight of order
`e^{−(1+6c)/(4c)}` in each output link (`e^{−9/2}` at `c = 1/12`), independent of `a_k`, and a flowed
plaquette of order `a_k³` from the boundary fluctuations, which is `PlaqLeak`. That estimate sums `R³`
boundary contributions of size `R⁻³` each; a single boundary link moves an output link by order
`R⁻³ ∝ a_k³`, so the single-link heat-bath bound of `PlaquetteFloor.stateK_plaq_ge` (conditional spread
`≥ c/β_k²` of one link) gives at most order `a_k⁶ β_k⁻²` in the flowed plaquette, below `a_k⁴`. A proof of
`PlaqLeak` at these observers needs the joint spread of the `R³` boundary links under `ν_k` passed through
the iterated polar map, a lower bound on the variance of a weighted boundary sum; no declaration in the tree
provides it. The `a_k³` order also assumes the boundary terms do not cancel across the four links of a
plaquette (neighbouring links' boxes differ by a face layer of independent bare links); a boundary-induced
field smooth on the scale `R` would give a plaquette of order `a_k⁵`, which is not a leak. `PlaqLeak` at
these observers is therefore open in both directions.

## 4. Observers without a held boundary (argued; a proposal)

`PhysRange r` caps the reach `a_k (R_k + 3)` by a fixed `r` (`obsConfFlow`, `obsConfFlowN`: `range k := R k + 3`;
`apeFam_physRange` needs `s < r`). Widening the box to `R = ⌊λ s/a_k⌋` with `λ ~ √log(1/a_k)`, so that the
held-boundary weight falls below `a_k⁴`, makes the reach grow without bound; keeping the box at fixed physical
size and shrinking the smoothing radius to `σ ~ r/√log(1/a_k)` leaves a bulk flowed plaquette of order
`a_k⁴ log(1/a_k)`. A diffusive kernel cut off by a box with bounded reach is therefore not expected to meet
`(M_W)`. The proposal is an observer that holds no boundary: a multigrid flow with about `log₂(s₀/a_k)` levels,
level `j` acting at stride `2^j a_k` with a fixed number of steps, whose total reach is a geometric sum of
order `s₀` and whose update is applied everywhere. For it `(M_W)` reduces to the bulk bound
`ν_k(sym plaq ∘ V_k) = O(a_k⁴)` with its exponential tail.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs; `1` the unit observable, the smearing scale of `obsW`; `2` the least
colour count and the rank; `4` the dimension of the plaquette density; `1/12`, `1/6` the APE weight of
`obsW` and its dominance range.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SunFamLeak

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverEnergyMoments MassGap.ObserverSymField MassGap.ObserverEnergyBox
  MassGap.MultiScaleAll MassGap.SU2Best MassGap.ObserverFlowSUN MassGap.CompositesBuild MassGap.ClayData

variable {N : ℕ}

/-! ## 1. The plaquette channel at any flow -/

/-- **The plaquette channel of `ScaleAt` at any flow**: `1 + μ(s) a_k⁻⁴ ν_k(sym plaq_q ∘ (Wf s).V k) ≤ C`.
DERIVED: `0` the signs; `1` the unit observable; `4` the dimension. -/
theorem one_add_le_of_scaleAt [NeZero N] {Wf : ℝ → ConfFlow N} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    {k : ℕ} {s : ℝ} (ht : 0 < t) (hs : 0 < s) (h : ScaleAt Wf t C γ γP k s)
    (q : MassGap.GibbsSpec.IPlaq) :
    1 + msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4
        * stateK (NeZero.ne N) k ((Wf s).fieldMap k (mField (Sum.inr q))).1 ≤ C := by
  have hN : N ≠ 0 := NeZero.ne N
  have hlam0 : 0 ≤ msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4 :=
    div_nonneg (msMu_pos ht γ γP hs (Sum.inr q)).le
      (pow_pos (dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k) 4).le
  have hj := h (Sum.inr q)
  have hd : mDim (Sum.inr q) = 4 := mDim_inr q
  rw [hd] at hj
  have hmono : stateK hN k ((1 : C(Cfg N, ℝ))
        + (msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4) • ((Wf s).fieldMap k (mField (Sum.inr q))).1)
      ≤ stateK hN k (expC ((msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4)
          • msAbs ((Wf s).fieldMap k (mField (Sum.inr q))).1)) := by
    refine (stateK hN k).mono fun U => ?_
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul,
      expC_apply, msAbs_apply]
    have := Real.add_one_le_exp (msMu t γ γP (Sum.inr q) s / dySpacing N k ^ 4
      * |((Wf s).fieldMap k (mField (Sum.inr q))).1 U|)
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self (((Wf s).fieldMap k (mField (Sum.inr q))).1 U))
      hlam0]
  rw [(stateK hN k).map_add, (stateK hN k).map_smul, (stateK hN k).map_one] at hmono
  exact hmono.trans hj

/-! ## 2. The leak predicate and the no-go -/

/-- **A plaquette leak**: some plaquette's flowed mean in physical units, `ν_k(sym plaq_q ∘ W.V k) / a_k⁴`,
is unbounded above along the steps. DERIVED: `4` the dimension. -/
def PlaqLeak [NeZero N] (W : ConfFlow N) : Prop :=
  ∃ q : MassGap.GibbsSpec.IPlaq, ∀ K : ℝ, ∃ᶠ k in atTop,
    K < stateK (NeZero.ne N) k (W.fieldMap k (mField (Sum.inr q))).1 / dySpacing N k ^ 4

/-- **A leak at the physical-scale flow excludes `ScaleControlAll`.** DERIVED: `4` the dimension. -/
theorem not_scaleControlAll_of_plaqLeak [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    (hL : PlaqLeak (Wf b)) : ¬ ScaleControlAll b Wf := by
  rintro ⟨t, C, γ, γP, ht, hev⟩
  obtain ⟨q, hq⟩ := hL
  have hmu : 0 < msMu t γ γP (Sum.inr q) b := msMu_pos ht γ γP hb _
  have hsmall : ∀ᶠ k in atTop, dySpacing N k ≤ b :=
    (tendsto_dySpacing N).eventually (eventually_le_nhds hb)
  obtain ⟨k, hgt, hk, hsm⟩ :=
    ((hq (C / msMu t γ γP (Sum.inr q) b)).and_eventually (hev.and hsmall)).exists
  have h := one_add_le_of_scaleAt ht hb (hk b hsm le_rfl) q
  rw [div_lt_iff₀ hmu] at hgt
  have e : msMu t γ γP (Sum.inr q) b / dySpacing N k ^ 4
        * stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1
      = stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 / dySpacing N k ^ 4
        * msMu t γ γP (Sum.inr q) b := by
    ring
  linarith

/-- **No substrate core at a leaking observer**, any `z`, `b`, `Wf`. DERIVED: no numeral. -/
theorem not_substrateCoreAt_of_plaqLeak [NeZero N] {W : ConfFlow N} (hL : PlaqLeak W)
    (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : ¬ SubstrateCoreAt W z b Wf := fun S =>
  not_scaleControlAll_of_plaqLeak S.b_pos (by rw [S.top]; exact hL) S.scale

/-- **No `SU(2)` multiscale bundle at a leaking observer**, any `z`, `μ`, `b`, `Wf`, `cf`.
DERIVED: `2` the rank. -/
theorem not_multiScaleStrongAt_of_plaqLeak {W : ConfFlow 2} (hL : PlaqLeak W) (z : Chan → ℕ → ℝ)
    (μ : MassGap.CompositesRen.OffMix) (b : ℝ) (Wf : ℝ → ConfFlow 2)
    (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : ¬ MassGap.StrongExpand.MultiScaleStrongAt W z μ b Wf cf := fun S =>
  not_scaleControlAll_of_plaqLeak S.b_pos (by rw [S.top]; exact hL) S.scale

/-- **An eventually-identity flow leaks** (`N ≥ 2`), at `q = ((0, 1), 0)`. DERIVED: `0` the signs;
`2` the least colour count; `4` the dimension. -/
theorem plaqLeak_of_id (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} (hW : ∀ᶠ k in atTop, W.V k = id) :
    PlaqLeak W := by
  refine ⟨PlaquetteFloor.qo, fun K => ?_⟩
  have hbig := (ScaleIdentityNoGo.tendsto_plaq_div (N := N) hN2).eventually (eventually_gt_atTop K)
  refine (hbig.and hW).frequently.mono ?_
  rintro k ⟨hk, hid⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hle : stateK hN k (plaqField (N := N) PlaquetteFloor.qo).1
      ≤ stateK hN k (W.fieldMap k (mField (Sum.inr PlaquetteFloor.qo))).1 := by
    refine (stateK hN k).mono fun U => ?_
    rw [ScaleIdentityNoGo.fieldMap_apply_of_id W k hid, mField_inr]
    exact FlowMoments.plaq_le_sym hN _ U
  have ha : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k) 4
  exact hk.trans_le (div_le_div_of_nonneg_right hle ha.le)

/-- **No substrate core at `sunFam … s₀` if it leaks.** DERIVED: `2` the least colour count; `12 = 2 · 6`
the block-step coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_substrateCoreAt_sunFam_of_leak (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ : ℝ} (hL : PlaqLeak (sunFam hN2 c hc0 hc s₀))
    (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : ¬ SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) z b Wf :=
  not_substrateCoreAt_of_plaqLeak hL z b Wf

/-- **No `SU(2)` multiscale bundle at `obsW` if it leaks.** DERIVED: `2` the rank. -/
theorem not_multiScaleStrongAt_obsW_of_leak (hL : PlaqLeak ObserverChoice.obsW) (z : Chan → ℕ → ℝ)
    (μ : MassGap.CompositesRen.OffMix) (b : ℝ) (Wf : ℝ → ConfFlow 2) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) :
    ¬ MassGap.StrongExpand.MultiScaleStrongAt ObserverChoice.obsW z μ b Wf cf :=
  not_multiScaleStrongAt_of_plaqLeak hL z μ b Wf cf

end MassGap.SunFamLeak

end

#print axioms MassGap.SunFamLeak.one_add_le_of_scaleAt
#print axioms MassGap.SunFamLeak.not_scaleControlAll_of_plaqLeak
#print axioms MassGap.SunFamLeak.not_substrateCoreAt_of_plaqLeak
#print axioms MassGap.SunFamLeak.not_multiScaleStrongAt_of_plaqLeak
#print axioms MassGap.SunFamLeak.plaqLeak_of_id
#print axioms MassGap.SunFamLeak.not_substrateCoreAt_sunFam_of_leak
#print axioms MassGap.SunFamLeak.not_multiScaleStrongAt_obsW_of_leak
