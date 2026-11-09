import Mathlib
import MassGap.ScaleAlong

noncomputable section

/-!
# MassGap.BlockDynamicStep — the UV step through a block dynamics at fixed physical block size

A block heat-bath dynamics resamples blocks of fixed physical size `ℓ` from their conditional law. Its gap
`γ β` (per block update) carries no dynamic exponent in the lattice spacing: a block of fixed physical size
holds a fixed physical content, and an exact block resample creates and removes topological charge inside the
block with its equilibrium weight (SCALE-STEP-FINDINGS, "Block dynamics"). Through a polynomial (Chebyshev)
filter the dynamics gap gives a transfer gap per block of order `√γ`, i.e. per lattice step of order
`√γ · a/ℓ`; in units of the scale `s = a/ℓ` that is a physical rate `c₀ √γ`.

## What it gives

1. `BlockStep γ s βUV C`: for two admissible couplings (one dyadic step apart in `s`),
   `(1 − C (s β)²) γ β ≤ γ β'`: the block-dynamics gap falls by at most the fraction `C s²` per step.
2. `gamma_eventually_ge`: a scale function `s` from `β₀`, `0 ≤ γ β₀`, `C ≥ 0`, `C s² ≤ 1` from `βUV` on, and
   `BlockStep`: at every large `β`, `γ β ≥ γ β₀ (1 − (4/3) C (s β₀)²)`. The losses telescope along the dyadic
   tower with a clipped chain (`clip_step`), the sum bounded by `ScaleAlong.lossBudget_artifact`.
3. `ChebyshevConversion D γ s c₀ βUV`: at every coupling from `βUV` on, `GapAt (D β) (e^{−c₀ √(γ β) s β})`.
   `gapAt_eventually_of_blockStep`: with item 2, the gap at the physical rate `c₀ √(γ β₀ (1 − (4/3) C (s β₀)²))`
   in `s`-units at every large `β`.
4. At the periodic data: `uniformPhysGapAlong_of_blockStep` (`ConstantPhysics.UniformPhysGapAlong` along `s`)
   and `clay_continuum_of_blockDynamics`: `γ β₀ > 0`, `BlockStep` with `(4/3) C (s β₀)² < 1`,
   `ChebyshevConversion` with `c₀ > 0`, `ScaleAlong.ScaleDominatesRun s N`, and E, N, Y give
   `ClayRoutes.ClayContinuum`. No transfer gap at a base coupling is asked: the base is the block-dynamics gap.

## What is assumed

Here `γ` is an arbitrary function. With `γ` constant, `BlockStep` holds at `C = 0` and `ChebyshevConversion` is
the uniform transfer gap itself (`BlockGapDef.chebyshevConversion_const_iff`, `BlockGapDef.blockStep_const`):
in this form the capstone restates its conclusion, and the module is the arithmetic of the tower only.
`BlockGapDef` defines `γ` as the block heat-bath gap of the Wilson measure at fixed physical block size
(`gammaWilson`), which makes `BlockStep` and the base statements about that dynamics; the conversion
(`BlockGapDef.WilsonConversion`) is then the theorem to prove, not proved in either module.

DERIVED (module-wide): `2` the block factor and the order `s²`; `4/3` the geometric budget; `0` the signs;
`1` the whole gap; `4` in `Fin 4` the spacetime dimension.
-/

namespace MassGap.BlockDynamicStep

open MassGap Filter
open scoped Topology

/-- **The block-dynamics step.** See the module docstring, item 1.

DERIVED: `2` the block factor and the order. -/
def BlockStep (γ s : ℝ → ℝ) (βUV C : ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → s β / 2 ≤ s β' → s β' ≤ s β →
    (1 - C * s β ^ 2) * γ β ≤ γ β'

/-- **One clipped step.** `0 ≤ x ≤ 1`, `0 ≤ g₀`, `L ≤ min y g₀`, `(1 − x) y ≤ y'`:
`L − x g₀ ≤ min y' g₀`.

DERIVED: `0`, `1` bracket `x`. -/
theorem clip_step {x g₀ y y' L : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg₀ : 0 ≤ g₀)
    (hL : L ≤ min y g₀) (hstep : (1 - x) * y ≤ y') : L - x * g₀ ≤ min y' g₀ := by
  have hLg : L ≤ g₀ := hL.trans (min_le_right _ _)
  have hLy : L ≤ y := hL.trans (min_le_left _ _)
  refine le_min ?_ (by nlinarith)
  rcases le_total y g₀ with h | h
  · nlinarith
  · nlinarith

#print axioms clip_step

/-- **The block-dynamics gap stays up along the tower.** See the module docstring, item 2.

DERIVED: `4/3` the geometric budget; `2` the block factor; `0`, `1` the signs and the whole gap. -/
theorem gamma_eventually_ge {γ s : ℝ → ℝ} {β₀ βUV C : ℝ} (hs : ScaleAlong.ScaleFunction s β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 ≤ γ β₀) (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ^ 2 ≤ 1)
    (hstep : BlockStep γ s βUV C) :
    ∀ᶠ β in atTop, γ β₀ * (1 - 4 / 3 * C * s β₀ ^ 2) ≤ γ β := by
  have hs₀ := hs.pos β₀ le_rfl
  set g₀ := γ β₀ with hg₀def
  have hgex : ∀ i : ℕ, ∃ g : ℝ, β₀ ≤ g ∧ s g = s β₀ / 2 ^ (i + 1) := by
    intro i
    have hlt : s β₀ / 2 ^ (i + 1) < s β₀ :=
      div_lt_self hs₀ (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i))
    exact hs.reach _ (div_pos hs₀ (by positivity)) hlt
  choose g hgβ hg using hgex
  obtain ⟨σ, hσ0, hσβ, hσ⟩ : ∃ σ : ℕ → ℝ, σ 0 = β₀ ∧ (∀ i : ℕ, β₀ ≤ σ i) ∧
      ∀ i : ℕ, s (σ i) = s β₀ / 2 ^ i :=
    ⟨(fun i => match i with | 0 => β₀ | k + 1 => g k),
     rfl,
     fun i => by
      cases i with
      | zero => exact le_rfl
      | succ k => exact hgβ k,
     fun i => by
      cases i with
      | zero =>
        show s β₀ = s β₀ / 2 ^ 0
        rw [pow_zero, div_one]
      | succ k =>
        show s (g k) = s β₀ / 2 ^ (k + 1)
        exact hg k⟩
  -- the clipped chain along the exact halvings
  have hchain : ∀ n : ℕ, g₀ - (∑ i ∈ Finset.range n, C * (s β₀ / 2 ^ i) ^ 2) * g₀
      ≤ min (γ (σ n)) g₀ := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, sub_zero]
      rw [hσ0]
      exact le_min le_rfl le_rfl
    | succ n ih =>
      have hx0 : 0 ≤ C * (s β₀ / 2 ^ n) ^ 2 := by positivity
      have hx1 : C * (s β₀ / 2 ^ n) ^ 2 ≤ 1 := by
        have := hCs (σ n) (hUVβ₀.trans (hσβ n))
        rwa [hσ n] at this
      have hst := hstep (σ n) (σ (n + 1)) (hUVβ₀.trans (hσβ n)) (hUVβ₀.trans (hσβ (n + 1)))
        (le_of_eq (by rw [hσ n, hσ (n + 1), pow_succ, div_div]))
        (by
          rw [hσ n, hσ (n + 1), pow_succ, ← div_div]
          have hnn : 0 ≤ s β₀ / 2 ^ n := div_nonneg hs₀.le (by positivity)
          linarith)
      rw [hσ n] at hst
      have h := clip_step hx0 hx1 hg₀ ih hst
      rw [Finset.sum_range_succ]
      linarith
  have hbud := ScaleAlong.lossBudget_artifact (ε := fun t => C * t ^ 2) (a₀ := s β₀) hC
    (fun _ => le_rfl)
  filter_upwards [hs.eventually_le, Filter.eventually_ge_atTop βUV] with β hβs hβUV
  obtain ⟨ha, hβa⟩ := hβs
  have hex : ∃ n : ℕ, s β₀ / 2 ^ (n + 1) < s β := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s β₀ / s β) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1)), pow_succ]
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [hn, mul_pos h2n ha]
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, s β₀ / 2 ^ (n + 1) < s β ∧
      ∀ k : ℕ, k < n → ¬ (s β₀ / 2 ^ (k + 1) < s β) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hle : s β ≤ s β₀ / 2 ^ n := by
    cases n with
    | zero =>
      rw [pow_zero, div_one]
      exact hβa
    | succ k => exact not_lt.mp (hmin k (Nat.lt_succ_self k))
  have hlast := hstep (σ n) β (hUVβ₀.trans (hσβ n)) hβUV
    (by
      rw [hσ n, div_div, ← pow_succ]
      exact hn.le)
    (by
      rw [hσ n]
      exact hle)
  rw [hσ n] at hlast
  have hx0 : 0 ≤ C * (s β₀ / 2 ^ n) ^ 2 := by positivity
  have hx1 : C * (s β₀ / 2 ^ n) ^ 2 ≤ 1 := by
    have := hCs (σ n) (hUVβ₀.trans (hσβ n))
    rwa [hσ n] at this
  have hfin := clip_step hx0 hx1 hg₀ (hchain n) hlast
  have hsum := hbud (n + 1)
  rw [Finset.sum_range_succ] at hsum
  have hmul := mul_le_mul_of_nonneg_right hsum hg₀
  have : g₀ - (∑ i ∈ Finset.range n, C * (s β₀ / 2 ^ i) ^ 2) * g₀ - C * (s β₀ / 2 ^ n) ^ 2 * g₀
      ≤ γ β := hfin.trans (min_le_left _ _)
  nlinarith [this, hmul]

#print axioms gamma_eventually_ge

section Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The Chebyshev conversion, as a hypothesis**: at every coupling from `βUV` on, the transfer has the gap
`e^{−c₀ √(γ β) s β}`. See the module docstring, "What is assumed".

DERIVED: no numeral. -/
def ChebyshevConversion (D : ℝ → Transfer.TransferData A) (γ s : ℝ → ℝ) (c₀ βUV : ℝ) : Prop :=
  ∀ β : ℝ, βUV ≤ β → TransferGap.GapAt (D β) (Real.exp (-(c₀ * Real.sqrt (γ β) * s β)))

/-- **The transfer gap at a uniform rate in `s`-units.**

DERIVED: `4/3` the geometric budget; `0` the signs. -/
theorem gapAt_eventually_of_blockStep (D : ℝ → Transfer.TransferData A) {γ s : ℝ → ℝ}
    {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 ≤ γ β₀)
    (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ^ 2 ≤ 1) (hc₀ : 0 ≤ c₀)
    (hstep : BlockStep γ s βUV C) (hconv : ChebyshevConversion D γ s c₀ βUV) :
    ∀ᶠ β in atTop, TransferGap.GapAt (D β)
      (Real.exp (-(c₀ * Real.sqrt (γ β₀ * (1 - 4 / 3 * C * s β₀ ^ 2)) * s β))) := by
  filter_upwards [gamma_eventually_ge hs hUVβ₀ hg₀ hC hCs hstep, hs.eventually_le,
    Filter.eventually_ge_atTop βUV] with β hγ hsβ hβ
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ (hconv β hβ)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hsq := Real.sqrt_le_sqrt hγ
  have h1 := mul_le_mul_of_nonneg_left hsq hc₀
  exact mul_le_mul_of_nonneg_right h1 hsβ.1.le

#print axioms gapAt_eventually_of_blockStep

end Transfer

section Periodic

variable {N : ℕ}

/-- **The uniform physical gap along `s` from the block dynamics.**

DERIVED: `2` the least rank with a non-zero Haar variance; `4/3` the budget; `0`, `1` the signs. -/
theorem uniformPhysGapAlong_of_blockStep (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {γ s : ℝ → ℝ} {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < γ β₀) (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ^ 2 ≤ 1)
    (hb : 4 / 3 * C * s β₀ ^ 2 < 1) (hc₀ : 0 < c₀)
    (hstep : BlockStep γ s βUV C)
    (hconv : ChebyshevConversion (fun β => PeriodicState.periodicGaugeInvData τ p hN β) γ s c₀ βUV) :
    ConstantPhysics.UniformPhysGapAlong τ p hN s := by
  set M := c₀ * Real.sqrt (γ β₀ * (1 - 4 / 3 * C * s β₀ ^ 2)) with hM
  have hMpos : 0 < M := mul_pos hc₀ (Real.sqrt_pos.mpr (mul_pos hg₀ (by linarith)))
  refine ⟨M, hMpos, ?_⟩
  filter_upwards [gapAt_eventually_of_blockStep _ hs hUVβ₀ hg₀.le hC hCs hc₀.le hstep hconv,
    hs.eventually_le, Filter.eventually_ge_atTop β₀] with β hg hsβ hββ
  obtain ⟨hpos, _⟩ := hsβ
  have hβ0 : 0 ≤ β := (hβ₀.trans_le hββ).le
  have hr0 : 0 < Real.exp (-(M * s β)) := Real.exp_pos _
  have hr1 : Real.exp (-(M * s β)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0 hr0 hr1 hg, ?_⟩
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self hpos.ne', mul_one]

#print axioms uniformPhysGapAlong_of_blockStep

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the block dynamics.** The block-dynamics gap at one coupling, the
block step along a scale function with `(4/3) C (s β₀)² < 1`, the Chebyshev conversion, `ScaleDominatesRun`,
and E, N, Y: `ClayRoutes.ClayContinuum`.

DERIVED: `2` the least rank; `0` the excluded colour count, the reflection plane and the signs; `4` the
spacetime dimension; `4/3` the budget; `1` the least colour count. -/
theorem clay_continuum_of_blockDynamics (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {γ s : ℝ → ℝ} {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < γ β₀) (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ^ 2 ≤ 1)
    (hb : 4 / 3 * C * s β₀ ^ 2 < 1) (hc₀ : 0 < c₀)
    (hstep : BlockStep γ s βUV C)
    (hconv : ChebyshevConversion (fun β => PeriodicState.periodicGaugeInvData τ 0 hN β) γ s c₀ βUV)
    (hdomR : ScaleAlong.ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  have hS := uniformPhysGapAlong_of_blockStep τ 0 hN2 hN hs hβ₀ hUVβ₀ hg₀ hC hCs hb hc₀ hstep hconv
  obtain ⟨κ, hκ, hdom⟩ := hdomR
  have hR : ConstantPhysics.UniformPhysGapAlong τ 0 hN (AsymptoticScaling.aRun N) :=
    ScaleAlong.uniformPhysGapAlong_of_dominates τ 0 hN hκ hdom
      (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
      (hs.eventually_le.mono (fun _ h => h.1)) hS
  have hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L :=
    (ConstantPhysics.fixedWindowDecayAlong_aRun τ 0 hN L).mp
      (ConstantPhysics.fixedWindowDecayAlong_of_uniformPhysGapAlong τ 0 hN hL
        (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
        (fun b hb => WeakCouplingWindow.eventually_aRun_le hN1 hb) hR)
  exact ClayRoutes.clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL hW O G hconvK hY

#print axioms clay_continuum_of_blockDynamics

end Periodic

end MassGap.BlockDynamicStep
