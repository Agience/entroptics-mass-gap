import Mathlib
import MassGap.ScaleStep
import MassGap.ConstantPhysics

noncomputable section

/-!
# MassGap.ScaleAlong — the UV step in the units of a scale of the family, at the order of a lattice artifact

The finite-box route measures every rate in units of the two-loop spacing `aRun N`
(`UVIRSplit.UVLossStep`, `IRGapAt`, `RestoreShimsClay.UVBelowIR`, `WeakCouplingWindow.FixedWindowDecay`).
In those units the physical rate of SU(2) drifts by a term of order `g²` (SCALE-STEP-FINDINGS, "Sizing the
loss"): one dyadic step moves `g²` by about `0.063 g⁴`, the drift per step is `O(g⁴)` and telescopes,
and it sums exactly when two-loop asymptotic scaling holds. This module restates the chain in the units
of any scale function `s` of the family (the observer's own scale, or r0), where the change of a physical
rate per step is a cutoff effect, and shows that a loss of that order sums.

## What it gives

1. **The composition along any scale.** `gapAt_eventually_along`: on any family of transfer data, a
   scale `s` positive at `β₀`, reaching every level below `s β₀` from `β₀` on and eventually in
   `(0, s β₀]`, the clipped step `UVIRSplit.LossStepBelow D s βUV ε M₀` with non-negative losses and
   budget `E` along the dyadic tower below `s β₀`, and the base gap at rate `e^{−M₀ s β₀}`: the gap at
   rate `e^{−(M₀ − E) s β}` at every large `β`. The proof of `UVIRSplit.gapAt_eventually_of_uv_ir_below`
   with `s` in place of `aRun N`.
2. **Which losses sum.** `lossBudget_artifact`: a loss `ε t ≤ C t²` (a cutoff effect of order `a²`) has
   budget `(4/3) C a₀²` below `a₀`; `vanishingLoss_artifact`: it vanishes with `a₀`.
   `not_lossBudget_harmonic`: a loss at least `κ/(i + 1)` at the `i`-th dyadic spacing, `κ > 0`, has no
   finite budget. A loss of order `g²` per step is of that kind, since `g²` at the `i`-th step is of
   order `1/(b i)`.
3. **The scale function.** `ScaleFunction s β₀`: continuous on `[β₀, ∞)`, positive there, tending to
   `0`. `ScaleFunction.reach` (intermediate values, `ConstantPhysics.exists_level`) and
   `ScaleFunction.eventually_le` supply the two hypotheses of item 1.
4. **The periodic chain along `s`.** `IRGapAlong`, `UVBelowIRAlong`; `uniformPhysGapAlong_of_uv_ir`:
   `ConstantPhysics.UniformPhysGapAlong τ p hN s` (the periodic Clay gap at every large `β`, physical
   rate in `s`-units at least `M₀ − E`); `fixedWindowDecayAlong_of_uv_ir`: `FixedWindowDecayAlong s`.
5. **The cutoff-effect form, on the view.** `uvBelowIRAlong_of_artifact_view`: the observer's view dense
   and vacuum-orthogonal at every coupling from `βUV`, and the clipped view step
   (`ScaleStep.ViewLossStepBelow`) with loss `C t²` and `(4/3) C (s β₀)² < M₀`, give `UVBelowIRAlong`.
   `uniformPhysGapAlong_of_artifact_view` composes it with the base.
6. **Back to the two-loop units.** `uniformPhysGapAlong_of_dominates`: a uniform gap along `s` and
   `κ · a β ≤ s β` eventually (`κ > 0`) give it along `a`. `ScaleDominatesRun s N`: some `κ > 0` with
   `κ · aRun N β ≤ s β` eventually: `s`, read in two-loop units, stays bounded below.
   `clay_continuum_of_boxPatchGap_scale`: `BoxPatch.BoxPatchGap` at `β₀`, a scale function, the view
   step at the order of a cutoff effect, `ScaleDominatesRun`, and E, N, Y give
   `ClayRoutes.ClayContinuum`.

## What is open, and what it encodes

* **The cutoff-effect bound itself**: `ViewLossStepBelow … s βUV (fun t => C * t ^ 2) M₀`. In the units of
  a scale `s` of the same family, the gap is a ratio of two physical scales; between spacings `a` and
  `a/2` it changes by the difference of the lattice artifacts of the two, of order `(a/ℓ)²` with `ℓ` the
  observer's resolution (Symanzik's description of cutoff effects for the Wilson action). Escape: the
  `O(a²)` form fails if the artifacts carry a non-analytic or logarithmic factor large enough that their
  differences along the tower stop summing below the base rate; the bound must hold uniformly over the
  view, not for one observable.
* **`ScaleDominatesRun s N`** is needed only to return to the tree's continuum layer, which is built on
  `aRun N` (`ContinuumSchwinger.dySpacing`). It is one-sided asymptotic scaling of `s`, a statement of
  perturbative type. Restating the continuum layer with `s` removes it.

DERIVED (module-wide): `2` is the block factor and the order `t²` of the cutoff effect; `4/3 = Σ 4^{−i}`;
`1` in `i + 1` shifts the harmonic index; `0` the sign of losses, scales and rates; `4` in `Fin 4` the
spacetime dimension.
-/

namespace MassGap.ScaleAlong

open MassGap Filter
open scoped Topology

/-! ## 1. The composition along any scale -/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The UV/IR composition along a scale `s`.** See the module docstring, item 1.

DERIVED: `2` is the block factor; `0` the sign of the losses and the scale. -/
theorem gapAt_eventually_along (D : ℝ → Transfer.TransferData A) (s : ℝ → ℝ)
    {βUV β₀ M₀ E : ℝ} {ε : ℝ → ℝ} (hs₀ : 0 < s β₀) (hUVβ₀ : βUV ≤ β₀)
    (hreach : ∀ t : ℝ, 0 < t → t < s β₀ → ∃ g : ℝ, β₀ ≤ g ∧ s g = t)
    (hev : ∀ᶠ β in atTop, 0 < s β ∧ s β ≤ s β₀)
    (hbudget : UVIRSplit.LossBudget ε (s β₀) E) (hε : ∀ x : ℝ, 0 ≤ ε x)
    (huv : UVIRSplit.LossStepBelow D s βUV ε M₀)
    (hir : TransferGap.GapAt (D β₀) (Real.exp (-(M₀ * s β₀)))) :
    ∀ᶠ β in atTop, TransferGap.GapAt (D β) (Real.exp (-((M₀ - E) * s β))) := by
  have hgex : ∀ i : ℕ, ∃ g : ℝ, β₀ ≤ g ∧ s g = s β₀ / 2 ^ (i + 1) := by
    intro i
    have hlt : s β₀ / 2 ^ (i + 1) < s β₀ :=
      div_lt_self hs₀ (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i))
    exact hreach _ (div_pos hs₀ (by positivity)) hlt
  choose g hgβ hg using hgex
  obtain ⟨γ, hγ0, hγβ, hγ⟩ : ∃ γ : ℕ → ℝ, γ 0 = β₀ ∧ (∀ i : ℕ, β₀ ≤ γ i) ∧
      ∀ i : ℕ, s (γ i) = s β₀ / 2 ^ i :=
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
  have hstep : ∀ j : ℕ, ∀ M : ℝ, M ≤ M₀ →
      TransferGap.GapAt (D (γ j)) (Real.exp (-(M * s (γ j)))) →
      TransferGap.GapAt (D (γ (j + 1)))
        (Real.exp (-((M - ε (s β₀ / 2 ^ j)) * s (γ (j + 1))))) := by
    intro j M hM hgj
    have h := huv (γ j) (γ (j + 1)) (hUVβ₀.trans (hγβ j)) (hUVβ₀.trans (hγβ (j + 1)))
      (le_of_eq (by rw [hγ j, hγ (j + 1), pow_succ, div_div]))
      (by
        rw [hγ j, hγ (j + 1), pow_succ, ← div_div]
        have hnn : 0 ≤ s β₀ / 2 ^ j := div_nonneg hs₀.le (by positivity)
        linarith)
      M hM hgj
    rw [hγ j] at h
    exact h
  have hbase0 : TransferGap.GapAt (D (γ 0)) (Real.exp (-(M₀ * s (γ 0)))) := by
    rw [hγ0]
    exact hir
  filter_upwards [hev, Filter.eventually_ge_atTop βUV] with β hβs hβUV
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
  have hchain : TransferGap.GapAt (D (γ n))
      (Real.exp (-((M₀ - ∑ i ∈ Finset.range n, ε (s β₀ / 2 ^ i)) * s (γ n)))) :=
    UVIRSplit.gapAt_chain_below (fun i => D (γ i)) (fun i => s (γ i))
      (fun i => ε (s β₀ / 2 ^ i)) M₀ n (fun i => hε _) hbase0
      (fun j _ M hM hgj => hstep j M hM hgj) n le_rfl
  have hlast := huv (γ n) β (hUVβ₀.trans (hγβ n)) hβUV
    (by
      rw [hγ n, div_div, ← pow_succ]
      exact hn.le)
    (by
      rw [hγ n]
      exact hle)
    (M₀ - ∑ i ∈ Finset.range n, ε (s β₀ / 2 ^ i))
    (sub_le_self _ (Finset.sum_nonneg (fun i _ => hε _))) hchain
  rw [hγ n] at hlast
  have hS : ∑ i ∈ Finset.range n, ε (s β₀ / 2 ^ i) + ε (s β₀ / 2 ^ n) ≤ E := by
    have hb := hbudget (n + 1)
    rw [Finset.sum_range_succ] at hb
    exact hb
  have hmono : Real.exp (-((M₀ - ∑ i ∈ Finset.range n, ε (s β₀ / 2 ^ i)
        - ε (s β₀ / 2 ^ n)) * s β))
      ≤ Real.exp (-((M₀ - E) * s β)) := by
    rw [Real.exp_le_exp]
    have hm := mul_le_mul_of_nonneg_right
      (show M₀ - E ≤ M₀ - ∑ i ∈ Finset.range n, ε (s β₀ / 2 ^ i)
        - ε (s β₀ / 2 ^ n) by linarith) ha.le
    linarith
  exact GapStep.gapAt_mono _ (Real.exp_pos _).le hmono hlast

#print axioms gapAt_eventually_along

end Abstract

/-! ## 2. Which losses sum -/

/-- **A cutoff-effect loss sums.** `0 ≤ ε t ≤ C t²` at the dyadic spacings below `a₀` gives the budget
`(4/3) C a₀²`: `Σ C a₀² 4^{−i} ≤ (4/3) C a₀²`.

DERIVED: `2` the order of the effect; `4 = 2²` the ratio per step; `4/3 = 1/(1 − 1/4)`. -/
theorem lossBudget_artifact {ε : ℝ → ℝ} {C a₀ : ℝ} (hC : 0 ≤ C)
    (hε : ∀ i : ℕ, ε (a₀ / 2 ^ i) ≤ C * (a₀ / 2 ^ i) ^ 2) :
    UVIRSplit.LossBudget ε a₀ (4 / 3 * C * a₀ ^ 2) := by
  intro n
  have hterm : ∀ i : ℕ, C * (a₀ / 2 ^ i) ^ 2 = C * a₀ ^ 2 * (1 / 4) ^ i := by
    intro i
    have h4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [div_pow, h4, one_div_pow, div_eq_mul_one_div (a₀ ^ 2) (4 ^ i)]
    ring
  have hgeom : ∑ i ∈ Finset.range n, ((1 : ℝ) / 4) ^ i ≤ 4 / 3 := by
    have h := geom_sum_eq (show ((1 : ℝ) / 4) ≠ 1 by norm_num) n
    rw [h]
    have hp : 0 ≤ ((1 : ℝ) / 4) ^ n := by positivity
    have : ((1 : ℝ) / 4) ^ n * (4 / 3) ≥ 0 := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith
  calc ∑ i ∈ Finset.range n, ε (a₀ / 2 ^ i) ≤ ∑ i ∈ Finset.range n, C * (a₀ / 2 ^ i) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hε i)
    _ = C * a₀ ^ 2 * ∑ i ∈ Finset.range n, ((1 : ℝ) / 4) ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ C * a₀ ^ 2 * (4 / 3) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 4 / 3 * C * a₀ ^ 2 := by ring

#print axioms lossBudget_artifact

/-- **A cutoff-effect loss vanishes in the continuum**: `ε t = C t²` has `UVIRSplit.VanishingLoss`.

DERIVED: `2` the order; `4/3` as in `lossBudget_artifact`; `3/4` its inverse. -/
theorem vanishingLoss_artifact {C : ℝ} (hC : 0 ≤ C) :
    UVIRSplit.VanishingLoss (fun t => C * t ^ 2) := by
  intro δ hδ
  refine ⟨Real.sqrt (3 / 4 * δ / (C + 1)), Real.sqrt_pos.mpr (by positivity), fun a ha hle => ?_⟩
  have hb := lossBudget_artifact (ε := fun t => C * t ^ 2) (a₀ := a) hC (fun i => le_rfl)
  intro n
  refine (hb n).trans ?_
  have ha2 : a ^ 2 ≤ 3 / 4 * δ / (C + 1) := by
    have h := pow_le_pow_left₀ ha.le hle 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hC1 : C ≤ C + 1 := by linarith
  have : C * a ^ 2 ≤ (C + 1) * (3 / 4 * δ / (C + 1)) :=
    mul_le_mul hC1 ha2 (sq_nonneg a) (by linarith)
  rw [mul_div_cancel₀ _ (by linarith : C + 1 ≠ 0)] at this
  linarith

#print axioms vanishingLoss_artifact

/-- **A harmonic loss has no budget.** If the loss at the `i`-th dyadic spacing is at least
`κ/(i + 1)` with `κ > 0`, no `E` bounds its partial sums. A loss of order `g²` per step is of this kind:
along the tower `g²` at step `i` is of order `1/(b i)`.

DERIVED: `1` in `i + 1` shifts the harmonic index; `0` the sign of `κ`. -/
theorem not_lossBudget_harmonic {ε : ℝ → ℝ} {κ a₀ : ℝ} (hκ : 0 < κ)
    (hε : ∀ i : ℕ, κ / ((i : ℝ) + 1) ≤ ε (a₀ / 2 ^ i)) (E : ℝ) :
    ¬ UVIRSplit.LossBudget ε a₀ E := by
  intro hb
  have ht := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨n, hn⟩ := (ht.eventually (Filter.eventually_gt_atTop (E / κ))).exists
  have hsum : κ * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) ≤ E := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (hb n)
    have := hε i
    rw [mul_one_div]
    exact this
  rw [div_lt_iff₀ hκ] at hn
  linarith

#print axioms not_lossBudget_harmonic

/-! ## 3. The scale function -/

/-- **A scale function from `β₀`**: continuous on `[β₀, ∞)`, positive there, tending to `0`.

DERIVED: `0` the sign and the limit. -/
structure ScaleFunction (s : ℝ → ℝ) (β₀ : ℝ) : Prop where
  cont : ContinuousOn s (Set.Ici β₀)
  pos : ∀ β : ℝ, β₀ ≤ β → 0 < s β
  vanish : Tendsto s atTop (𝓝 0)

/-- Every level below `s β₀` is reached from `β₀` on (`ConstantPhysics.exists_level`).

DERIVED: `0` the sign. -/
theorem ScaleFunction.reach {s : ℝ → ℝ} {β₀ : ℝ} (h : ScaleFunction s β₀) :
    ∀ t : ℝ, 0 < t → t < s β₀ → ∃ g : ℝ, β₀ ≤ g ∧ s g = t :=
  fun _ ht hlt => ConstantPhysics.exists_level h.cont h.vanish ht hlt.le

#print axioms ScaleFunction.reach

/-- Eventually `0 < s β ≤ s β₀`.

DERIVED: `0` the sign. -/
theorem ScaleFunction.eventually_le {s : ℝ → ℝ} {β₀ : ℝ} (h : ScaleFunction s β₀) :
    ∀ᶠ β in atTop, 0 < s β ∧ s β ≤ s β₀ := by
  have hs₀ := h.pos β₀ le_rfl
  filter_upwards [h.vanish.eventually (Iic_mem_nhds hs₀), Filter.eventually_ge_atTop β₀] with β h1 h2
  exact ⟨h.pos β h2, h1⟩

#print axioms ScaleFunction.eventually_le

/-- Eventually `s β ≤ b`, for every `b > 0`.

DERIVED: `0` the sign. -/
theorem ScaleFunction.eventually_small {s : ℝ → ℝ} {β₀ : ℝ} (h : ScaleFunction s β₀) :
    ∀ b : ℝ, 0 < b → ∀ᶠ β in atTop, s β ≤ b :=
  fun _ hb => h.vanish.eventually (Iic_mem_nhds hb)

#print axioms ScaleFunction.eventually_small

/-! ## 4. The periodic chain along `s` -/

section Periodic

variable {N : ℕ}

/-- **The base gap in `s`-units**: `GapAt` at `e^{−M₀ s β₀}` at the periodic data.

DERIVED: `4` the spacetime dimension; `0` the excluded rank. -/
def IRGapAlong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (s : ℝ → ℝ) (β₀ M₀ : ℝ) : Prop :=
  TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β₀) (Real.exp (-(M₀ * s β₀)))

/-- **The UV step below `M₀` in `s`-units**: non-negative losses with a budget `E < M₀` along the
dyadic tower below `s β₀`, and the clipped step `LossStepBelow` along `s` from `βUV` on.

DERIVED: `4` the spacetime dimension; `0` the excluded rank and the sign of the losses. -/
def UVBelowIRAlong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (s : ℝ → ℝ) (β₀ βUV M₀ : ℝ) : Prop :=
  ∃ (ε : ℝ → ℝ) (E : ℝ), (∀ t, 0 ≤ ε t) ∧ UVIRSplit.LossBudget ε (s β₀) E ∧ E < M₀ ∧
    UVIRSplit.LossStepBelow (fun β => PeriodicState.periodicGaugeInvData τ p hN β) s βUV ε M₀

/-- **The base gap in `aRun`-units read in `s`-units**: `IRGapAt β₀ M` is `IRGapAlong s β₀` at
`M · aRun β₀ / s β₀`.

DERIVED: `0` the sign of `s β₀`. -/
theorem irGapAlong_of_irGapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {s : ℝ → ℝ} {β₀ M : ℝ}
    (hs : 0 < s β₀) (h : UVIRSplit.IRGapAt τ p hN β₀ M) :
    IRGapAlong τ p hN s β₀ (M * AsymptoticScaling.aRun N β₀ / s β₀) := by
  unfold IRGapAlong
  unfold UVIRSplit.IRGapAt at h
  have e : M * AsymptoticScaling.aRun N β₀ / s β₀ * s β₀ = M * AsymptoticScaling.aRun N β₀ := by
    field_simp
  rw [e]
  exact h

#print axioms irGapAlong_of_irGapAt

/-- **The uniform physical gap in `s`-units** from the base and the step along a scale function.

DERIVED: `2` the least rank with a non-zero Haar variance; `0` the excluded rank and the signs. -/
theorem uniformPhysGapAlong_of_uv_ir (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {s : ℝ → ℝ} {β₀ βUV M₀ : ℝ} (hs : ScaleFunction s β₀) (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hir : IRGapAlong τ p hN s β₀ M₀) (huv : UVBelowIRAlong τ p hN s β₀ βUV M₀) :
    ConstantPhysics.UniformPhysGapAlong τ p hN s := by
  obtain ⟨ε, E, hε, hbud, hEM, hstep⟩ := huv
  have hev := gapAt_eventually_along (fun β => PeriodicState.periodicGaugeInvData τ p hN β) s
    (hs.pos β₀ le_rfl) hUVβ₀ hs.reach hs.eventually_le hbud hε hstep hir
  refine ⟨M₀ - E, by linarith, ?_⟩
  filter_upwards [hev, hs.eventually_le, Filter.eventually_ge_atTop β₀] with β hg hsβ hββ
  obtain ⟨hpos, _⟩ := hsβ
  have hβ0 : 0 ≤ β := (hβ₀.trans_le hββ).le
  have hx : 0 < (M₀ - E) * s β := mul_pos (by linarith) hpos
  have hr0 : 0 < Real.exp (-((M₀ - E) * s β)) := Real.exp_pos _
  have hr1 : Real.exp (-((M₀ - E) * s β)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0 hr0 hr1 hg, ?_⟩
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self hpos.ne', mul_one]

#print axioms uniformPhysGapAlong_of_uv_ir

/-- **The window along `s`** (`ConstantPhysics.fixedWindowDecayAlong_of_uniformPhysGapAlong`).

DERIVED: as `uniformPhysGapAlong_of_uv_ir`. -/
theorem fixedWindowDecayAlong_of_uv_ir (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {s : ℝ → ℝ} {β₀ βUV M₀ L : ℝ} (hL : 0 < L) (hs : ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hir : IRGapAlong τ p hN s β₀ M₀)
    (huv : UVBelowIRAlong τ p hN s β₀ βUV M₀) :
    ConstantPhysics.FixedWindowDecayAlong τ p hN s L :=
  ConstantPhysics.fixedWindowDecayAlong_of_uniformPhysGapAlong τ p hN hL
    (hs.eventually_le.mono (fun _ h => h.1)) hs.eventually_small
    (uniformPhysGapAlong_of_uv_ir τ p hN2 hN hs hβ₀ hUVβ₀ hir huv)

#print axioms fixedWindowDecayAlong_of_uv_ir

/-! ## 5. The cutoff-effect form, on the view -/

/-- **The UV input from a cutoff-effect step on the view.** A view `S β`, vacuum-orthogonal and dense at
every coupling from `βUV`, the clipped view step along `s` with loss `C t²`, and
`(4/3) C (s β₀)² < M₀`: `UVBelowIRAlong`.

DERIVED: `2` the order of the effect; `4/3` as in `lossBudget_artifact`; `4` the spacetime
dimension. -/
theorem uvBelowIRAlong_of_artifact_view (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {s : ℝ → ℝ}
    {β₀ βUV M₀ C : ℝ} (hC : 0 ≤ C)
    (S : ℝ → Set ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (horth : ∀ β, βUV ≤ β → ∀ x ∈ S β,
      (PeriodicState.periodicGaugeInvData τ p hN β).form x
        (PeriodicState.periodicGaugeInvData τ p hN β).vac = 0)
    (hdense : ∀ β, βUV ≤ β →
      ScaleStep.ViewDense (PeriodicState.periodicGaugeInvData τ p hN β) (S β))
    (hview : ScaleStep.ViewLossStepBelow (fun β => PeriodicState.periodicGaugeInvData τ p hN β) S
      s βUV (fun t => C * t ^ 2) M₀)
    (hsmall : 4 / 3 * C * s β₀ ^ 2 < M₀) :
    UVBelowIRAlong τ p hN s β₀ βUV M₀ :=
  ⟨fun t => C * t ^ 2, 4 / 3 * C * s β₀ ^ 2, fun t => mul_nonneg hC (sq_nonneg t),
    lossBudget_artifact hC (fun _ => le_rfl), hsmall,
    ScaleStep.lossStepBelow_of_viewLossStepBelow _ S s βUV _ M₀ horth hdense hview⟩

#print axioms uvBelowIRAlong_of_artifact_view

/-- **The uniform gap in `s`-units from a cutoff-effect step on the view.**

DERIVED: as `uvBelowIRAlong_of_artifact_view` and `uniformPhysGapAlong_of_uv_ir`; `2` the order of the
effect; `4/3 = 1/(1 − 1/4)` the budget factor of `lossBudget_artifact`. -/
theorem uniformPhysGapAlong_of_artifact_view (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {s : ℝ → ℝ} {β₀ βUV M₀ C : ℝ} (hs : ScaleFunction s β₀) (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hC : 0 ≤ C) (hir : IRGapAlong τ p hN s β₀ M₀)
    (S : ℝ → Set ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (horth : ∀ β, βUV ≤ β → ∀ x ∈ S β,
      (PeriodicState.periodicGaugeInvData τ p hN β).form x
        (PeriodicState.periodicGaugeInvData τ p hN β).vac = 0)
    (hdense : ∀ β, βUV ≤ β →
      ScaleStep.ViewDense (PeriodicState.periodicGaugeInvData τ p hN β) (S β))
    (hview : ScaleStep.ViewLossStepBelow (fun β => PeriodicState.periodicGaugeInvData τ p hN β) S
      s βUV (fun t => C * t ^ 2) M₀)
    (hsmall : 4 / 3 * C * s β₀ ^ 2 < M₀) :
    ConstantPhysics.UniformPhysGapAlong τ p hN s :=
  uniformPhysGapAlong_of_uv_ir τ p hN2 hN hs hβ₀ hUVβ₀ hir
    (uvBelowIRAlong_of_artifact_view τ p hN hC S horth hdense hview hsmall)

#print axioms uniformPhysGapAlong_of_artifact_view

/-! ## 6. Back to the two-loop units -/

/-- **A scale that dominates `a` carries the uniform gap to `a`.** `UniformPhysGapAlong s` and
`κ · a β ≤ s β` eventually, `κ > 0`, `a` eventually positive: `UniformPhysGapAlong a` at `κ M`.

DERIVED: `0` the signs. -/
theorem uniformPhysGapAlong_of_dominates (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {s a : ℝ → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hdom : ∀ᶠ β in atTop, κ * a β ≤ s β)
    (hapos : ∀ᶠ β in atTop, 0 < a β) (hspos : ∀ᶠ β in atTop, 0 < s β)
    (h : ConstantPhysics.UniformPhysGapAlong τ p hN s) :
    ConstantPhysics.UniformPhysGapAlong τ p hN a := by
  obtain ⟨M, hM, hev⟩ := h
  refine ⟨κ * M, mul_pos hκ hM, ?_⟩
  filter_upwards [hev, hdom, hapos, hspos] with β hβ hd ha hs
  obtain ⟨r, hgap, hrate⟩ := hβ
  refine ⟨r, hgap, ?_⟩
  rw [le_div_iff₀ hs] at hrate
  rw [le_div_iff₀ ha]
  have hMn : 0 ≤ M := hM.le
  nlinarith [mul_le_mul_of_nonneg_left hd hMn]

#print axioms uniformPhysGapAlong_of_dominates

/-- **`s` dominates the two-loop spacing**: some `κ > 0` with `κ · aRun N β ≤ s β` at every large
`β`. One-sided asymptotic scaling of `s`.

DERIVED: `0` the sign of `κ`. -/
def ScaleDominatesRun (s : ℝ → ℝ) (N : ℕ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ β in atTop, κ * AsymptoticScaling.aRun N β ≤ s β

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from one box and a cutoff-effect step in the units of a scale of
the family.** `BoxPatch.BoxPatchGap` at `β₀`, a scale function `s` from `β₀`, a view dense and
vacuum-orthogonal from `βUV`, the clipped view step along `s` at loss `C t²` below the box rate read
in `s`-units, `ScaleDominatesRun s N`, and E, N, Y: `ClayRoutes.ClayContinuum`.

DERIVED: `2` the least rank with a non-zero Haar variance; `0` the excluded colour count, the
reflection plane and the signs; `4` the spacetime dimension; `4/3` as in `lossBudget_artifact`;
`1` the least colour count. -/
theorem clay_continuum_of_boxPatchGap_scale (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ C : ℝ} {n : ℕ} {s : ℝ → ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ) (hs : ScaleFunction s β₀) (hC : 0 ≤ C)
    (S : ℝ → Set ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0))
    (horth : ∀ β, βUV ≤ β → ∀ x ∈ S β,
      (PeriodicState.periodicGaugeInvData τ 0 hN β).form x
        (PeriodicState.periodicGaugeInvData τ 0 hN β).vac = 0)
    (hdense : ∀ β, βUV ≤ β →
      ScaleStep.ViewDense (PeriodicState.periodicGaugeInvData τ 0 hN β) (S β))
    (hview : ScaleStep.ViewLossStepBelow (fun β => PeriodicState.periodicGaugeInvData τ 0 hN β) S
      s βUV (fun t => C * t ^ 2)
      (HeatBathLocal.boxRate N β₀ n γ * AsymptoticScaling.aRun N β₀ / s β₀))
    (hsmall : 4 / 3 * C * s β₀ ^ 2
      < HeatBathLocal.boxRate N β₀ n γ * AsymptoticScaling.aRun N β₀ / s β₀)
    (hdomR : ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  have hir := irGapAlong_of_irGapAt τ 0 hN (hs.pos β₀ le_rfl)
    (HeatBathLocal.irGapAt_boxRate τ 0 (by omega) hN hβ₀ hbox).2
  have hS := uniformPhysGapAlong_of_artifact_view τ 0 hN2 hN hs hβ₀ hUVβ₀ hC hir S horth hdense
    hview hsmall
  obtain ⟨κ, hκ, hdom⟩ := hdomR
  have hR : ConstantPhysics.UniformPhysGapAlong τ 0 hN (AsymptoticScaling.aRun N) :=
    uniformPhysGapAlong_of_dominates τ 0 hN hκ hdom
      (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
      (hs.eventually_le.mono (fun _ h => h.1)) hS
  have hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L :=
    (ConstantPhysics.fixedWindowDecayAlong_aRun τ 0 hN L).mp
      (ConstantPhysics.fixedWindowDecayAlong_of_uniformPhysGapAlong τ 0 hN hL
        (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
        (fun b hb => WeakCouplingWindow.eventually_aRun_le hN1 hb) hR)
  exact ClayRoutes.clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL hW O G hconv hY

#print axioms clay_continuum_of_boxPatchGap_scale

end Periodic

end MassGap.ScaleAlong
