import Mathlib
import MassGap.PeriodicDyadic
import MassGap.ClayRoutes
import MassGap.WeakCouplingWindow
import MassGap.PeriodicReduce
import MassGap.TorusDecay

/-!
# MassGap.DoublingClay2 — the doubling route on the dyadic periodic state, with power-of-two seed

`PeriodicState.periodicUltra` is finer than the dyadic filter, so the doubling family of a
power-of-two seed is a set of it (`PeriodicDyadic.periodicUltra_seed_mem`): no volume comparison is
needed. The remaining input is a finite-volume statement on the dyadic tori, written directly in the
tree's own terms:

* `DyadicTorusDecay hN`: at every `β ≥ 0` and power-of-two `n ≥ 2` with the sharp seed
  `16 log ZR(n⁴) − log ZR((2n)⁴) ≤ 1/1000`, for every `x` in the gauge-invariant half-space algebra and
  `ε > 0`, `torusConn 0 0 hN β j x n ≤ ½ · torusConn 0 0 hN β j x 0 + ε` eventually along
  `periodicUltra hN β`. Proved (`dyadicTorusDecay`, from `TorusDecay.dyadic_torus_decay`): the transfer gap
  read on the torus observables, the torus closing controlled by the excited weight of the torus itself.
* `WDelta2 N ℓ₀` — (W_Δ) at the power-of-two seed `nP ℓ₀ β = 2^{⌈log₂⌈2ℓ₀/a⌉⌉}`, the least power of two at
  least `2ℓ₀/a`: eventually `16 log ZR(nP⁴) − log ZR((2nP)⁴) ≤ 1/1000`.

`fixedWindowDecay_of_WDelta2`: (W_Δ) at the power-of-two seed gives `WeakCouplingWindow.FixedWindowDecay 0 0 hN (5ℓ₀)` (lag `m = nP`,
`m · a ≤ 4ℓ₀ + 2a ≤ 5ℓ₀`, ratio `½`). `clay_of_WDelta2`: with E, N, Y, `ClayRoutes.ClayContinuum` at
window `5ℓ₀`; its inputs are `WDelta2` and E, N, Y.
-/

namespace MassGap.DoublingClay2

open Real Filter MassGap

variable {N : ℕ}

/-- **The finite-volume dyadic step.** See the module docstring.

DERIVED: `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the least side and the
doubling; `1/2` the decay ratio of `TorusDecay.dyadic_torus_decay`; `0` the plane and the time axis.
Inherited: `1/1000` the seed threshold of `DoublingSharp.rec_sharp`. -/
def DyadicTorusDecay (hN : N ≠ 0) : Prop :=
  ∀ (β : ℝ), 0 ≤ β → ∀ (n : ℕ), PeriodicState.IsPow2 n → 2 ≤ n →
    16 * Real.log (RectWilson.ZR (fun _ => n) N β) - Real.log (RectWilson.ZR (fun _ => 2 * n) N β)
      ≤ 1 / 1000 →
    ∀ x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := SUN.SU N) 0 0, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
        PeriodicReduce.torusConn 0 0 hN β j x n ≤ 1 / 2 * PeriodicReduce.torusConn 0 0 hN β j x 0 + ε

/-- The power-of-two seed: the least power of two at least `2ℓ₀/a`. -/
noncomputable def nP (N : ℕ) (ℓ₀ β : ℝ) : ℕ :=
  2 ^ Nat.clog 2 ⌈2 * ℓ₀ / AsymptoticScaling.aRun N β⌉₊

/-- **(W_Δ) at the power-of-two seed (named hypothesis).**

DERIVED: `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the doubling.
Inherited: `1/1000` the seed threshold of `DoublingSharp.rec_sharp`. -/
def WDelta2 (N : ℕ) (ℓ₀ : ℝ) : Prop :=
  ∀ᶠ β in atTop, 16 * Real.log (RectWilson.ZR (fun _ => nP N ℓ₀ β) N β)
    - Real.log (RectWilson.ZR (fun _ => 2 * nP N ℓ₀ β) N β) ≤ 1 / 1000

theorem nP_isPow2 (ℓ₀ β : ℝ) : PeriodicState.IsPow2 (nP N ℓ₀ β) := ⟨_, rfl⟩

/-- At `0 < a ≤ ℓ₀/2`: `2 ≤ 2^{clog ⌈2ℓ₀/a⌉}` and `2^{clog ⌈2ℓ₀/a⌉} · a ≤ 4ℓ₀ + 2a`. -/
theorem nP_bounds {ℓ₀ a : ℝ} (hℓ : 0 < ℓ₀) (ha : 0 < a) (hale : a ≤ ℓ₀ / 2) :
    2 ≤ 2 ^ Nat.clog 2 ⌈2 * ℓ₀ / a⌉₊ ∧
      ((2 ^ Nat.clog 2 ⌈2 * ℓ₀ / a⌉₊ : ℕ) : ℝ) * a ≤ 4 * ℓ₀ + 2 * a := by
  set c := ⌈2 * ℓ₀ / a⌉₊ with hc
  have hratio : (4 : ℝ) ≤ 2 * ℓ₀ / a := by rw [le_div_iff₀ ha]; linarith
  have hcR : (4 : ℝ) ≤ c := hratio.trans (Nat.le_ceil _)
  have hc4 : 4 ≤ c := by exact_mod_cast hcR
  have hpos : 0 < Nat.clog 2 c := Nat.clog_pos (by norm_num) (by omega)
  have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := c) (by omega)
  have hpow : 2 ^ Nat.clog 2 c = 2 * 2 ^ (Nat.clog 2 c).pred := by
    rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hpos).symm
  refine ⟨?_, ?_⟩
  · rw [hpow]; have := Nat.one_le_two_pow (n := (Nat.clog 2 c).pred); omega
  · have h2c : 2 ^ Nat.clog 2 c ≤ 2 * c := by rw [hpow]; omega
    have h2cR : ((2 ^ Nat.clog 2 c : ℕ) : ℝ) ≤ 2 * c := by exact_mod_cast h2c
    have hclt : (c : ℝ) < 2 * ℓ₀ / a + 1 := Nat.ceil_lt_add_one (by positivity)
    have : (c : ℝ) * a < 2 * ℓ₀ + a := by
      have := mul_lt_mul_of_pos_right hclt ha
      rwa [add_mul, div_mul_cancel₀ _ ha.ne', one_mul] at this
    nlinarith

/-- **The finite-volume dyadic step, proved.** -/
theorem dyadicTorusDecay (hN : N ≠ 0) : DyadicTorusDecay hN :=
  fun β hβ n hp hn hs x hx ε hε => TorusDecay.dyadic_torus_decay hN β hβ n hp hn hs x hx ε hε

/-- **(W_Δ) at the power-of-two seed gives `FixedWindowDecay`** at window `5ℓ₀`, ratio `½`,
lag `nP`. -/
theorem fixedWindowDecay_of_WDelta2 (hN : N ≠ 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : WDelta2 N ℓ₀) :
    WeakCouplingWindow.FixedWindowDecay 0 0 hN (5 * ℓ₀) := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hW, eventually_gt_atTop (0 : ℝ),
    WeakCouplingWindow.eventually_aRun_le hN1 (b := ℓ₀ / 2) (by positivity)] with β hβW hβ0 haLe
  set a := AsymptoticScaling.aRun N β
  have ha : 0 < a := AsymptoticScaling.aRun_pos hN1 hβ0
  obtain ⟨h2, hna⟩ := nP_bounds hℓ ha haLe
  have he : Even (nP N ℓ₀ β) := by
    obtain ⟨b, hb⟩ := nP_isPow2 (N := N) ℓ₀ β
    have hb1 : 1 ≤ b := by
      by_contra hb0
      have : b = 0 := by omega
      have h2' : 2 ≤ nP N ℓ₀ β := h2
      rw [hb, this] at h2'; norm_num at h2'
    exact ⟨2 ^ (b - 1), by rw [hb, ← two_mul, ← pow_succ', Nat.sub_add_cancel hb1]⟩
  have h2' : 2 ≤ nP N ℓ₀ β := h2
  refine ⟨nP N ℓ₀ β, by omega, ?_, fun x hx ε hε =>
    dyadicTorusDecay hN β hβ0.le _ (nP_isPow2 ℓ₀ β) h2 hβW x hx ε hε⟩
  show ((nP N ℓ₀ β : ℕ) : ℝ) * a ≤ 5 * ℓ₀
  have : ((nP N ℓ₀ β : ℕ) : ℝ) * a ≤ 4 * ℓ₀ + 2 * a := hna
  linarith

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The Clay statement from (W_Δ) at the power-of-two seed**, at window `5ℓ₀`, through
`ClayRoutes.clay_continuum_of_fixedWindowDecay` with E, N, Y. -/
theorem clay_of_WDelta2 (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z))
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : WDelta2 N ℓ₀)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) 0 O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z 0 hZ hB (5 * ℓ₀) :=
  ClayRoutes.clay_continuum_of_fixedWindowDecay hN2 hN Z 0 hZ hB (by positivity)
    (fixedWindowDecay_of_WDelta2 hN hℓ hW) O G hconvK hY

#print axioms dyadicTorusDecay
#print axioms fixedWindowDecay_of_WDelta2
#print axioms clay_of_WDelta2

end MassGap.DoublingClay2
