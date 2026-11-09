import Mathlib
import MassGap.DoublingClay2
import MassGap.ZoomSelfScale
import MassGap.DoublingSharp

/-!
# MassGap.WDeltaRun — the gap seed at the power-of-two side, with the side freed

`DoublingClay2.WDelta2 N ℓ₀` asks the sharp seed `defectW N β n ≤ 1/1000` at exactly one side,
`n = nP N ℓ₀ β = 2^{⌈log₂⌈2ℓ₀/aRun N β⌉⌉}`, eventually in `β`. This module shows that the side and
`ℓ₀` carry no content of their own.

* `Δ_corner`: the Wilson corner function at the diagonal corner `k𝟙` is the defect at side `2ᵏ n`.
* `defectW_pow_le`: at `β ≥ 0`, a seed at an even side `n ≥ 2` gives the seed at every side `2ᵏ n`
  (`DoublingSharp.iterate_sharp`, no hypothesis beyond the seed).
* `RunSeed N`: there is `C > 0` such that, eventually in `β`, some power of two `n ≥ 2` with
  `n · aRun N β ≤ C` meets the seed. This is (A) at a power-of-two side together with R in the form
  `n · aRun ≤ C`.
* `wDelta2_of_seed_le`: that statement at a constant `C` gives `WDelta2 N ℓ₀` for every `ℓ₀` with
  `C ≤ 2ℓ₀`.
* `runSeed_of_wDelta2`: `WDelta2 N ℓ₀` at one `ℓ₀ > 0` gives `RunSeed N` with `C = 5ℓ₀`
  (`nP · a ≤ 4ℓ₀ + 2a`, `DoublingClay2.nP_bounds`).
* `exists_wDelta2_iff`: `(∃ ℓ₀ > 0, WDelta2 N ℓ₀) ↔ RunSeed N`.

`RunSeed` is stated on the Wilson `SU(N)` partition function `RectWilson.ZR` only. Read on another
lattice family with the same doubling structure it fails for each control: 4D `U(1)` in its Coulomb
phase and Georgi–Glashow in its Coulomb phase (a massless photon keeps the defect of order one at every
side), 4D `Z₂` above `β_c ≈ 0.44` (the odd electric-flux states are nearly degenerate with the vacuum),
Banks–Zaks (conformal, the defect is of order one at every side), and the reflection-positive Gaussian
with `μ² = β_c − β` (the defect at every fixed side grows without bound as `β → β_c`, and the family
ends there). At `β = 0` the seed holds at every side (`SeedZeroCoupling.seed_at_zero`), which says
nothing about `RunSeed`, an eventual statement in `β`.

DERIVED: `16`, `2` and `1/1000` are the seed's; `5` is `nP_bounds`' `4ℓ₀ + 2a` at `a ≤ ℓ₀/2`; `2` in
`C ≤ 2ℓ₀` is the `2ℓ₀` of `nP`.
-/

namespace MassGap.WDeltaRun

open Real Filter MassGap MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.ZoomSelfScale

variable {N : ℕ}

/-- The Wilson corner function at the diagonal corner `k𝟙` is the defect at side `2ᵏ n`.
DERIVED: `2` the doubling of each side per corner step. -/
theorem Δ_corner (n k : ℕ) (β : ℝ) : Δ (xW N n β) (corner k) = defectW N β (2 ^ k * n) := by
  have h1 : ext n (corner k) = fun _ => 2 ^ k * n := by funext i; rfl
  have h2 : ext n (corner k + one) = fun _ => 2 * (2 ^ k * n) := by
    rw [← corner_succ]; funext i
    show 2 ^ (k + 1) * n = 2 * (2 ^ k * n)
    ring
  unfold Δ xW defectW; rw [h1, h2]

/-- **The seed climbs the dyadic sides at one coupling.** A seed at an even side `n ≥ 2` gives the
seed at every side `2ᵏ n`. DERIVED: `1/1000` the sharp seed; `250` and `1/4` are `iterate_sharp`'s. -/
theorem defectW_pow_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h0 : defectW N β n ≤ 1 / 1000) (k : ℕ) : defectW N β (2 ^ k * n) ≤ 1 / 1000 := by
  have hfr := factRep hN hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xW N n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact h0
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) k
  have hq : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := k))
    simpa using this
  rw [← Δ_corner]
  linarith

/-- **The run seed.** There is `C > 0` such that, eventually in `β`, some power of two `n ≥ 2` with
`n · aRun N β ≤ C` has `defectW N β n ≤ 1/1000`.

DERIVED: `1/1000` the sharp seed threshold of `DoublingSharp.rec_sharp`; `2` the least side. -/
def RunSeed (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    (n : ℝ) * AsymptoticScaling.aRun N β ≤ C ∧ defectW N β n ≤ 1 / 1000

/-- **`WDelta2` from a seed at a power of two below `C / aRun`**, for every `ℓ₀` with `C ≤ 2ℓ₀`.
The power of two `nP N ℓ₀ β` is at least `2ℓ₀/a ≥ C/a ≥ n`, so it is `2ᵏ n`, and `defectW_pow_le`
carries the seed there. -/
theorem wDelta2_of_seed_le (hN : N ≠ 0) {C : ℝ}
    (hev : ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ) * AsymptoticScaling.aRun N β ≤ C ∧ defectW N β n ≤ 1 / 1000)
    {ℓ₀ : ℝ} (hℓ : C ≤ 2 * ℓ₀) : DoublingClay2.WDelta2 N ℓ₀ := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β ⟨n, ⟨b, hb⟩, hn2, hna, hd⟩ hβ
  have ha : 0 < AsymptoticScaling.aRun N β := AsymptoticScaling.aRun_pos hN1 hβ
  have h1 : (n : ℝ) ≤ 2 * ℓ₀ / AsymptoticScaling.aRun N β := by
    rw [le_div_iff₀ ha]; linarith
  have h2 : (n : ℝ) ≤ (⌈2 * ℓ₀ / AsymptoticScaling.aRun N β⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
  have h3 : n ≤ ⌈2 * ℓ₀ / AsymptoticScaling.aRun N β⌉₊ := by exact_mod_cast h2
  have h4 : n ≤ DoublingClay2.nP N ℓ₀ β := h3.trans (Nat.le_pow_clog (by norm_num) _)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [hb] at hn2
    norm_num at hn2
  have he : Even n := by rw [hb]; exact Nat.even_pow.mpr ⟨even_two, hb0⟩
  set c := Nat.clog 2 ⌈2 * ℓ₀ / AsymptoticScaling.aRun N β⌉₊ with hc
  have hnP : DoublingClay2.nP N ℓ₀ β = 2 ^ c := rfl
  rw [hnP, hb] at h4
  have hbc : b ≤ c := (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
  have hk := defectW_pow_le hN hβ.le hn2 he hd (c - b)
  have e : 2 ^ (c - b) * n = DoublingClay2.nP N ℓ₀ β := by
    rw [hnP, hb, ← pow_add, Nat.sub_add_cancel hbc]
  rw [e] at hk
  exact hk

/-- **`WDelta2` at every large `ℓ₀` from the run seed.** -/
theorem wDelta2_of_runSeed (hN : N ≠ 0) (h : RunSeed N) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ₀ : ℝ, C ≤ 2 * ℓ₀ → DoublingClay2.WDelta2 N ℓ₀ := by
  obtain ⟨C, hC, hev⟩ := h
  exact ⟨C, hC, fun ℓ₀ hℓ => wDelta2_of_seed_le hN hev hℓ⟩

/-- **The run seed from `WDelta2`** at one `ℓ₀ > 0`, with `C = 5ℓ₀`. -/
theorem runSeed_of_wDelta2 (hN : N ≠ 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hW : DoublingClay2.WDelta2 N ℓ₀) : RunSeed N := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  refine ⟨5 * ℓ₀, by positivity, ?_⟩
  filter_upwards [hW, eventually_gt_atTop (0 : ℝ),
    WeakCouplingWindow.eventually_aRun_le hN1 (b := ℓ₀ / 2) (by positivity)] with β hβW hβ0 haLe
  have ha : 0 < AsymptoticScaling.aRun N β := AsymptoticScaling.aRun_pos hN1 hβ0
  obtain ⟨h2, hna⟩ := DoublingClay2.nP_bounds hℓ ha haLe
  refine ⟨DoublingClay2.nP N ℓ₀ β, DoublingClay2.nP_isPow2 ℓ₀ β, h2, ?_, hβW⟩
  have : ((DoublingClay2.nP N ℓ₀ β : ℕ) : ℝ) * AsymptoticScaling.aRun N β
      ≤ 4 * ℓ₀ + 2 * AsymptoticScaling.aRun N β := hna
  linarith

/-- **`WDelta2` at some `ℓ₀` is exactly the run seed.** -/
theorem exists_wDelta2_iff (hN : N ≠ 0) :
    (∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ DoublingClay2.WDelta2 N ℓ₀) ↔ RunSeed N := by
  constructor
  · rintro ⟨ℓ₀, hℓ, hW⟩
    exact runSeed_of_wDelta2 hN hℓ hW
  · intro h
    obtain ⟨C, hC, hW⟩ := wDelta2_of_runSeed hN h
    exact ⟨C / 2, by positivity, hW (C / 2) (by linarith)⟩

end MassGap.WDeltaRun

#print axioms MassGap.WDeltaRun.Δ_corner
#print axioms MassGap.WDeltaRun.defectW_pow_le
#print axioms MassGap.WDeltaRun.wDelta2_of_seed_le
#print axioms MassGap.WDeltaRun.wDelta2_of_runSeed
#print axioms MassGap.WDeltaRun.runSeed_of_wDelta2
#print axioms MassGap.WDeltaRun.exists_wDelta2_iff
