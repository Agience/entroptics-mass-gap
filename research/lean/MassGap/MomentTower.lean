import Mathlib
import MassGap.WeakCouplingWindow
import MassGap.ZoomStep

/-!
# MassGap.MomentTower — the exponential-moment tower of the transfer correlator is the gap

## What it gives

At a positive transfer, the reflected pairing of an observable with its translates is the moment
sequence of a positive finite measure on `[0, 1]`: `C(t) = ∫ λᵗ dν(λ)` (`lagProfile_eq_moment`, with
`ν = ZoomStep.specMeasure` of the observable's vector under `GNSHilbert.opT`). `ExpMomentTower b μ`
says the series `∑ₜ b t · e^{σ t}` converges (`Summable`) at every `σ < μ`; with `s = e^σ` it is the
series `∑ₜ b t · sᵗ` at every `0 < s < e^μ`. At a rate `r > 0` and `μ = −log r`:

1. One finite measure (`null_above_iff_expMomentTower`, `null_above_iff_decay`). For `b t = ∫ λᵗ dν`
   the following are equivalent: `ν {λ | r < λ} = 0`; `ExpMomentTower b (−log r)`; `b t ≤ rᵗ · b 0`
   at every `t`. Positivity of `ν` carries the two steps that are not bookkeeping. Weight on
   `[r + ε, 1]` puts every term of the series at `σ = −log (r + ε) < −log r` at or above that
   weight, so the series diverges (`null_above_of_expMomentTower`); no weight above `r` gives
   `λᵗ ≤ rᵗ` almost everywhere (`moment_le_of_null_above`). Decay by `rᵗ` makes the series geometric below
   `−log r` (`expMomentTower_of_decay`).
2. One observable of a `TransferData D` under `PositiveTransfer D`
   (`outWeight_eq_zero_iff_expMomentTower`, `lagProfile_expMomentTower_iff_decay`): the same three
   for `C(t) = ChessboardRead.lagProfile D x t`, with `ν` the spectral measure of `x`, whose weight
   on `(r, 1]` is `ZoomStep.outWeight`.
3. The whole form (`gapAt_iff_expMomentTower`): under `PositiveTransfer D` and `0 < r`,
   `TransferGap.GapAt D r` holds exactly when every
   `x` with `D.form x D.vac = 0` has `ExpMomentTower (lagProfile D x) (−log r)`. Forward:
   `ChessboardRead.lag_of_gapAt` and the geometric step. Back: the tower gives the decay at lag one
   (item 2), and `ChessboardRead.gapAt_of_lag` at `m = 1`.
4. The periodic Wilson state. `periodicConn τ p hN β x t = ν(θx · Sᵗx) − ν(θx) · ν(Sᵗx)`, with
   `ν = periodicState hN β`, is the limit of `PeriodicReduce.torusConn` along `periodicUltra hN β`
   (`PeriodicReduce.tendsto_torusConn`). At `0 ≤ β`, every gauge-invariant half-space observable
   has a finite measure on `[0, 1]` whose moments are its `periodicConn`, and for it the three of
   item 1 are equivalent (`periodicConn_moment_equivalences`). Over the algebra,
   `periodic_gapAt_iff_expMomentTower`: `GapAt (periodicGaugeInvData τ p hN β) r` holds exactly when
   every observable's `periodicConn` has the tower at `−log r` (`AlgebraTower τ p hN β (−log r)`).
5. Physical units (`fixedWindowDecay_iff_momentTower`). At `2 ≤ N` and `0 < L`,
   `WeakCouplingWindow.FixedWindowDecay τ p hN L` holds exactly when some `M > 0` has, at every
   large `β`, the tower of every observable's `periodicConn` at `μ = M · aRun N β`
   (`AlgebraTower τ p hN β (M · aRun N β)`). Through
   `WeakCouplingWindow.fixedWindowDecay_iff`: forward with `M = c / L`, back with the rate
   `r = e^{−M · aRun N β}` and `c = M · L`.

## Scope

The tower carries no constant, so no normalisation of `C(0)` enters and item 5 needs no hypothesis
beyond those of `WeakCouplingWindow.fixedWindowDecay_iff`; the only quantity uniform in `β` is the
physical rate `M`. A bound with a constant, `∑ₜ C(t) e^{σ t} ≤ K`, could not be uniform over the
algebra: `x ↦ c · x` multiplies `C` by `c²`. The decay form `C(t) ≤ rᵗ C(0)` is normalised by `C(0)`
itself. The right side of item 5 does not mention `L`, and neither does `FixedWindowDecay` in effect
(`WeakCouplingWindow.fixedWindowDecay_window_free`). Item 5 is an equivalence between two open
inputs: nothing here proves either at any coupling. It restates the uniform gap as a statement about
the exponential moments of the correlator and does not weaken it. `not_expMomentTower_const`: a
constant correlator `C ≡ c ≠ 0` has the tower at no `μ > 0`; at `c > 0` it is the moment sequence
of the point mass `c` at `λ = 1`.
-/

namespace MassGap.MomentTower

open MeasureTheory MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.PeriodicState

/-! ## 1. The tower -/

section Tower

/-- **The exponential-moment tower** of a lag sequence `b` at rate `μ`: at every `σ < μ` the series
`∑ₜ b t · e^{σ t}` converges. With `s = e^σ` it is convergence of `∑ₜ b t · sᵗ` at every
`0 < s < e^μ`.

DERIVED: no numeral occurs; `μ` is the caller's rate. -/
def ExpMomentTower (b : ℕ → ℝ) (μ : ℝ) : Prop :=
  ∀ σ : ℝ, σ < μ → Summable (fun t : ℕ => b t * Real.exp (σ * (t : ℝ)))

/-- **The tower is monotone in the rate.** From `μ' ≤ μ` and the tower at `μ`, the tower at `μ'`:
every `σ < μ'` is below `μ`.

DERIVED: no numeral occurs. -/
theorem expMomentTower_mono {b : ℕ → ℝ} {μ μ' : ℝ} (h : μ' ≤ μ) (hb : ExpMomentTower b μ) :
    ExpMomentTower b μ' :=
  fun σ hσ => hb σ (lt_of_lt_of_le hσ h)

#print axioms expMomentTower_mono

/-- **Decay gives the tower.** For `b` nonnegative, `0 < r` and `b t ≤ rᵗ · b 0` at every `t`:
`ExpMomentTower b (−log r)`. At `σ < −log r`, `r · e^σ < 1`, and `b t · e^{σ t}` is at most
`b 0 · (r e^σ)ᵗ`, a convergent geometric series (`summable_geometric_of_lt_one`).

DERIVED: `0` is the lower bound on each term, the lower end of `r`, and the base lag. -/
theorem expMomentTower_of_decay {b : ℕ → ℝ} (hb : ∀ t, 0 ≤ b t) {r : ℝ} (hr : 0 < r)
    (hdec : ∀ t : ℕ, b t ≤ r ^ t * b 0) : ExpMomentTower b (-Real.log r) := by
  intro σ hσ
  have hE : Real.exp σ < r⁻¹ := by
    calc Real.exp σ < Real.exp (-Real.log r) := Real.exp_lt_exp.mpr hσ
      _ = r⁻¹ := by rw [Real.exp_neg, Real.exp_log hr]
  have hq0 : 0 ≤ r * Real.exp σ := (mul_pos hr (Real.exp_pos σ)).le
  have hq1 : r * Real.exp σ < 1 := by
    calc r * Real.exp σ < r * r⁻¹ := mul_lt_mul_of_pos_left hE hr
      _ = 1 := mul_inv_cancel₀ hr.ne'
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (hb t) (Real.exp_pos _).le) (fun t => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (b 0))
  show b t * Real.exp (σ * (t : ℝ)) ≤ b 0 * (r * Real.exp σ) ^ t
  rw [mul_comm σ, Real.exp_nat_mul, mul_pow]
  calc b t * Real.exp σ ^ t ≤ (r ^ t * b 0) * Real.exp σ ^ t :=
        mul_le_mul_of_nonneg_right (hdec t) (pow_nonneg (Real.exp_pos σ).le t)
    _ = b 0 * (r ^ t * Real.exp σ ^ t) := by ring

#print axioms expMomentTower_of_decay

/-- **A constant correlator has no tower.** At `c ≠ 0` and `0 < μ`, `ExpMomentTower (fun _ => c) μ`
fails: at `σ = 0` every term is `c`, and the terms of a convergent series tend to `0`
(`Summable.tendsto_atTop_zero`). At `c > 0` the sequence is the moment sequence of the point mass
`c` at `λ = 1`.

DERIVED: `0` is the excluded value of `c` and the lower end of `μ`. -/
theorem not_expMomentTower_const {c : ℝ} (hc : c ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    ¬ ExpMomentTower (fun _ => c) μ := by
  intro h
  have hs := (h 0 hμ).tendsto_atTop_zero
  simp only [zero_mul, Real.exp_zero, mul_one] at hs
  exact hc (tendsto_nhds_unique tendsto_const_nhds hs)

#print axioms not_expMomentTower_const

end Tower

/-! ## 2. One finite measure: no weight above `r`, the tower, and the decay -/

section Measure

variable (ν : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure ν]

omit [IsFiniteMeasure ν] in
/-- The moments of a measure on `[0, 1]` are nonnegative: `λᵗ ≥ 0` there.

DERIVED: `0` and `1` are the interval's ends; `0` is the lower bound concluded. -/
theorem nonneg_of_moments {b : ℕ → ℝ} (hν : ∀ t : ℕ, b t = ∫ l, (l : ℝ) ^ t ∂ν) (t : ℕ) :
    0 ≤ b t := by
  rw [hν t]
  exact integral_nonneg (fun l => pow_nonneg l.2.1 t)

#print axioms nonneg_of_moments

/-- **No weight above `r` gives the decay.** For `b t = ∫ λᵗ dν` and `ν {λ | r < λ} = 0`:
`b t ≤ rᵗ · b 0` at every `t`. Almost everywhere `λ ≤ r`, and `0 ≤ λ` on `[0, 1]`, so
`λᵗ ≤ rᵗ = rᵗ · λ⁰` (`integral_mono_ae`). No sign of `r` is assumed: at `r < 0` the hypothesis makes
`ν` zero.

DERIVED: `0` and `1` are the interval's ends; `0` is the null weight and the base lag. -/
theorem moment_le_of_null_above {b : ℕ → ℝ} (hν : ∀ t : ℕ, b t = ∫ l, (l : ℝ) ^ t ∂ν) {r : ℝ}
    (hnull : ν {l : Set.Icc (0 : ℝ) 1 | r < (l : ℝ)} = 0) (t : ℕ) :
    b t ≤ r ^ t * b 0 := by
  have hae : ∀ᵐ l : Set.Icc (0 : ℝ) 1 ∂ν, (l : ℝ) ≤ r := by
    rw [ae_iff]
    simpa only [not_le] using hnull
  rw [hν t, hν 0, ← integral_const_mul]
  refine integral_mono_ae
    (SpectralRep.integrable_of_continuous ν (continuous_subtype_val.pow t))
    (SpectralRep.integrable_of_continuous ν
      (f := fun l : Set.Icc (0 : ℝ) 1 => r ^ t * (l : ℝ) ^ 0)
      (continuous_const.mul (continuous_subtype_val.pow 0))) ?_
  filter_upwards [hae] with l hl
  show (l : ℝ) ^ t ≤ r ^ t * (l : ℝ) ^ 0
  rw [pow_zero, mul_one]
  exact pow_le_pow_left₀ l.2.1 hl t

#print axioms moment_le_of_null_above

/-- **The tower leaves no weight above `r`.** For `b t = ∫ λᵗ dν`, `0 < r` and
`ExpMomentTower b (−log r)`: `ν {λ | r < λ} = 0`. Otherwise some `[a, 1]` with
`a = r + 1/(n + 1)` carries weight `w > 0` (`(r, 1]` is their countable union,
`measure_iUnion_null`). At `σ = −log a < −log r`, `b t · e^{σ t} ≥ aᵗ · w · a⁻ᵗ = w` at every `t`,
while the terms of the convergent series tend to `0`.

DERIVED: `0` and `1` are the interval's ends; `0` is the lower end of `r` and the null weight. -/
theorem null_above_of_expMomentTower {b : ℕ → ℝ} (hν : ∀ t : ℕ, b t = ∫ l, (l : ℝ) ^ t ∂ν)
    {r : ℝ} (hr : 0 < r) (h : ExpMomentTower b (-Real.log r)) :
    ν {l : Set.Icc (0 : ℝ) 1 | r < (l : ℝ)} = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ν {l : Set.Icc (0 : ℝ) 1 | r + 1 / ((n : ℝ) + 1) ≤ (l : ℝ)} ≠ 0 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    apply hne
    refine measure_mono_null (fun l hl => ?_)
      (measure_iUnion_null (s := fun n : ℕ =>
        {l : Set.Icc (0 : ℝ) 1 | r + 1 / ((n : ℝ) + 1) ≤ (l : ℝ)}) hall)
    have hl' : r < (l : ℝ) := hl
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hl')
    exact Set.mem_iUnion.mpr ⟨m, show r + 1 / ((m : ℝ) + 1) ≤ (l : ℝ) by linarith⟩
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  set a : ℝ := r + 1 / ((n : ℝ) + 1) with ha_def
  have ha0 : 0 < a := by linarith
  have hra : r < a := by linarith
  set S : Set (Set.Icc (0 : ℝ) 1) := {l : Set.Icc (0 : ℝ) 1 | a ≤ (l : ℝ)} with hS_def
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_subtype_coe
  have hc : 0 < ν.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hn (measure_ne_top ν S)
  have hsum := h (-Real.log a) (neg_lt_neg (Real.log_lt_log hr hra))
  have hlow : ∀ t : ℕ, ν.real S ≤ b t * Real.exp (-Real.log a * (t : ℝ)) := by
    intro t
    have hint : a ^ t * ν.real S ≤ b t := by
      rw [hν t]
      calc a ^ t * ν.real S = ∫ l, S.indicator (fun _ => a ^ t) l ∂ν := by
            rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]
        _ ≤ ∫ l, (l : ℝ) ^ t ∂ν := by
            refine integral_mono ((integrable_const _).indicator hS)
              (SpectralRep.integrable_of_continuous ν (continuous_subtype_val.pow t)) ?_
            intro l
            show S.indicator (fun _ => a ^ t) l ≤ (l : ℝ) ^ t
            by_cases hl : l ∈ S
            · rw [Set.indicator_of_mem hl]
              exact pow_le_pow_left₀ ha0.le hl t
            · rw [Set.indicator_of_notMem hl]
              exact pow_nonneg l.2.1 t
    have hexp : Real.exp (-Real.log a * (t : ℝ)) = a⁻¹ ^ t := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log ha0]
    have hinv : a ^ t * a⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ ha0.ne', one_pow]
    rw [hexp]
    calc ν.real S = (a ^ t * ν.real S) * a⁻¹ ^ t := by
          rw [mul_comm (a ^ t), mul_assoc, hinv, mul_one]
      _ ≤ b t * a⁻¹ ^ t :=
          mul_le_mul_of_nonneg_right hint (pow_nonneg (inv_nonneg.mpr ha0.le) t)
  have hle := ge_of_tendsto' hsum.tendsto_atTop_zero hlow
  linarith

#print axioms null_above_of_expMomentTower

/-- **No weight above `r` is the tower.** For `b t = ∫ λᵗ dν` and `0 < r`:
`ν {λ | r < λ} = 0 ↔ ExpMomentTower b (−log r)`. Forward: `moment_le_of_null_above`, then
`expMomentTower_of_decay`. Back: `null_above_of_expMomentTower`.

DERIVED: `0` and `1` are the interval's ends; `0` is the lower end of `r` and the null weight. -/
theorem null_above_iff_expMomentTower {b : ℕ → ℝ} (hν : ∀ t : ℕ, b t = ∫ l, (l : ℝ) ^ t ∂ν)
    {r : ℝ} (hr : 0 < r) :
    ν {l : Set.Icc (0 : ℝ) 1 | r < (l : ℝ)} = 0 ↔ ExpMomentTower b (-Real.log r) :=
  ⟨fun h => expMomentTower_of_decay (nonneg_of_moments ν hν) hr
      (moment_le_of_null_above ν hν h),
    null_above_of_expMomentTower ν hν hr⟩

#print axioms null_above_iff_expMomentTower

/-- **No weight above `r` is the decay.** For `b t = ∫ λᵗ dν` and `0 < r`:
`ν {λ | r < λ} = 0 ↔ ∀ t, b t ≤ rᵗ · b 0`. Forward: `moment_le_of_null_above`. Back:
`expMomentTower_of_decay`, then `null_above_of_expMomentTower`.

DERIVED: `0` and `1` are the interval's ends; `0` is the lower end of `r`, the null weight, and the
base lag. -/
theorem null_above_iff_decay {b : ℕ → ℝ} (hν : ∀ t : ℕ, b t = ∫ l, (l : ℝ) ^ t ∂ν) {r : ℝ}
    (hr : 0 < r) :
    ν {l : Set.Icc (0 : ℝ) 1 | r < (l : ℝ)} = 0 ↔ ∀ t : ℕ, b t ≤ r ^ t * b 0 :=
  ⟨moment_le_of_null_above ν hν,
    fun h => null_above_of_expMomentTower ν hν hr
      (expMomentTower_of_decay (nonneg_of_moments ν hν) hr h)⟩

#print axioms null_above_iff_decay

end Measure

/-! ## 3. One observable, and the whole form -/

section Observable

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The profile of an observable is a moment sequence.** Under `PositiveTransfer D`, for every
`x` and `t`, `lagProfile D x t = ∫ λᵗ dν` with `ν = ZoomStep.specMeasure` of the class of `(x, 0)`
under `opT D`: `ZoomStep.specMeasure_rep` at `λ ↦ λᵗ` (`cfc_pow_id`), and
`FloorRead.re_inner_opT_pow_ofPair`. The spectrum lies in `[0, 1]` by
`ZoomStep.spec_unit_of_positive`.

DERIVED: `0` and `1` are the interval's ends; `0` is the imaginary component of the pair. -/
theorem lagProfile_eq_moment (D : TransferData A) (hP : PositiveTransfer D) (x : A) (t : ℕ) :
    ChessboardRead.lagProfile D x t
      = ∫ l, (l : ℝ) ^ t ∂(ZoomStep.specMeasure (opT D) (isSelfAdjoint_opT D)
          ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm)) := by
  have h := ZoomStep.specMeasure_rep (opT D) (isSelfAdjoint_opT D)
    (ZoomStep.spec_unit_of_positive D hP)
    ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm)
    (fun s : ℝ => s ^ t) (continuous_pow t)
  rw [cfc_pow_id (R := ℝ) (opT D) t (isSelfAdjoint_opT D),
    FloorRead.re_inner_opT_pow_ofPair D x t] at h
  exact h

#print axioms lagProfile_eq_moment

/-- **For one observable, no spectral weight above `r` is the tower.** Under `PositiveTransfer D`
and `0 < r`: the weight `ZoomStep.outWeight` of the class of `(x, 0)` on `(r, 1]` is `0` exactly
when `ExpMomentTower (lagProfile D x) (−log r)`. `null_above_iff_expMomentTower` at the measure of
`lagProfile_eq_moment`.

DERIVED: `0` is the imaginary component of the pair, the lower end of `r`, and the null weight. -/
theorem outWeight_eq_zero_iff_expMomentTower (D : TransferData A) (hP : PositiveTransfer D)
    (x : A) {r : ℝ} (hr : 0 < r) :
    ZoomStep.outWeight (opT D) (isSelfAdjoint_opT D)
        ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm) r = 0
      ↔ ExpMomentTower (ChessboardRead.lagProfile D x) (-Real.log r) := by
  haveI := ZoomStep.specMeasure_isFinite (opT D) (isSelfAdjoint_opT D)
    ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm)
  exact null_above_iff_expMomentTower _ (lagProfile_eq_moment D hP x) hr

#print axioms outWeight_eq_zero_iff_expMomentTower

/-- **For one observable, the tower is the decay.** Under `PositiveTransfer D` and `0 < r`:
`ExpMomentTower (lagProfile D x) (−log r)` holds exactly when
`lagProfile D x t ≤ rᵗ · lagProfile D x 0` at every `t`. Both are `ν {λ | r < λ} = 0` for the
measure of `lagProfile_eq_moment` (`null_above_iff_expMomentTower`, `null_above_iff_decay`).

DERIVED: `0` is the lower end of `r` and the base lag. -/
theorem lagProfile_expMomentTower_iff_decay (D : TransferData A) (hP : PositiveTransfer D)
    (x : A) {r : ℝ} (hr : 0 < r) :
    ExpMomentTower (ChessboardRead.lagProfile D x) (-Real.log r)
      ↔ ∀ t : ℕ, ChessboardRead.lagProfile D x t ≤ r ^ t * ChessboardRead.lagProfile D x 0 := by
  haveI := ZoomStep.specMeasure_isFinite (opT D) (isSelfAdjoint_opT D)
    ((Pre.ofPair D.toReflForm x (0 : A) : Pre D.toReflForm) : H D.toReflForm)
  exact (null_above_iff_expMomentTower _ (lagProfile_eq_moment D hP x) hr).symm.trans
    (null_above_iff_decay _ (lagProfile_eq_moment D hP x) hr)

#print axioms lagProfile_expMomentTower_iff_decay

/-- **The gap is the tower on the vacuum complement.** Under `PositiveTransfer D` and `0 < r`:
`TransferGap.GapAt D r` holds exactly when every `x` with `D.form x D.vac = 0` has
`ExpMomentTower (lagProfile D x) (−log r)`. Forward: `ChessboardRead.lag_of_gapAt` gives the decay
at every lag, and `expMomentTower_of_decay` with `ChessboardRead.lagProfile_nonneg`. Back: the
tower gives the decay at lag `1` (`lagProfile_expMomentTower_iff_decay`), and
`ChessboardRead.gapAt_of_lag` at `m = 1` gives `GapAt`.

DERIVED: `0` is the lower end of `r` and the vacuum pairing. -/
theorem gapAt_iff_expMomentTower (D : TransferData A) (hP : PositiveTransfer D) {r : ℝ}
    (hr : 0 < r) :
    TransferGap.GapAt D r ↔
      ∀ x : A, D.form x D.vac = 0 →
        ExpMomentTower (ChessboardRead.lagProfile D x) (-Real.log r) := by
  have h0 : ∀ x : A, ChessboardRead.lagProfile D x 0 = D.form x x := fun x => by
    show D.form x ((D.T ^ 0) x) = D.form x x
    rw [pow_zero, Module.End.one_apply]
  constructor
  · intro hg x hx
    refine expMomentTower_of_decay (ChessboardRead.lagProfile_nonneg D hP x) hr (fun t => ?_)
    rw [h0 x]
    exact ChessboardRead.lag_of_gapAt D hr.le hg t x hx
  · intro h
    refine ChessboardRead.gapAt_of_lag D hP (m := 1) one_ne_zero hr.le (fun x hx => ?_)
    have hd := (lagProfile_expMomentTower_iff_decay D hP x hr).mp (h x hx) 1
    rw [h0 x] at hd
    exact hd

#print axioms gapAt_iff_expMomentTower

end Observable

/-! ## 4. The periodic Wilson state -/

section Periodic

variable {N : ℕ}

/-- **The connected reflected-shifted pairing at the periodic state**:
`periodicConn τ p hN β x c = ν(θx · Sᶜx) − ν(θx) · ν(Sᶜx)`, `ν = periodicState hN β`,
`θ = ireflObs τ (2p)`, `S` the unit shift along `τ`. It is the limit of
`PeriodicReduce.torusConn τ p hN β j x c` along `periodicUltra hN β`
(`PeriodicReduce.tendsto_torusConn`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane. -/
noncomputable def periodicConn (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (c : ℕ) : ℝ :=
  periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
      * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
    - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
      * periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)

/-- **On the vacuum complement the connected pairing is the profile.** For `y` in the
gauge-invariant algebra with `D.form y D.vac = 0` (`D = periodicGaugeInvData τ p hN β`):
`periodicConn τ p hN β y c = lagProfile D y c`. `ν(θy) = D.form y D.vac = 0`
(`PeriodicReduce.periodic_form_vac`), and `ν(θy · Sᶜy) = D.form y (Tᶜ y)`
(`PeriodicReduce.periodic_form_pow`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the vacuum pairing. -/
theorem periodicConn_of_orth (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (hy : (periodicGaugeInvData τ p hN β).form y (periodicGaugeInvData τ p hN β).vac = 0)
    (c : ℕ) :
    periodicConn τ p hN β (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) c
      = ChessboardRead.lagProfile (periodicGaugeInvData τ p hN β) y c := by
  have hθ : periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
      (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = 0 := by
    rw [← PeriodicReduce.periodic_form_vac τ p hN β y]
    exact hy
  unfold periodicConn
  rw [hθ, zero_mul, sub_zero]
  exact (PeriodicReduce.periodic_form_pow τ p hN β y c).symm

#print axioms periodicConn_of_orth

/-- **Every observable's connected pairing is the profile of an orthogonal element.** For `x` in
the gauge-invariant half-space algebra, `y = x − ν(θx) · 1` (`ν = periodicState hN β`) lies in the
algebra, has `D.form y D.vac = 0`, and `periodicConn τ p hN β x c = lagProfile D y c` at every `c`
(`D = periodicGaugeInvData τ p hN β`). The centring of
`WeakCouplingWindow.torusLag_le_of_gapAt`: `PeriodicReduce.periodic_form_vac`,
`PeriodicReduce.periodic_form_pow`, `GaugeInvariantAlgebra.iterate_shift_sub_smul_one`,
`PeriodicReduce.state_centred_mul`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the vacuum pairing. -/
theorem exists_orth_periodicConn (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hx : x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p) :
    ∃ y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p),
      (periodicGaugeInvData τ p hN β).form y (periodicGaugeInvData τ p hN β).vac = 0
        ∧ ∀ c : ℕ, periodicConn τ p hN β x c
          = ChessboardRead.lagProfile (periodicGaugeInvData τ p hN β) y c := by
  have hθ1 : MassGap.LatticeReflection.ireflObs τ (2 * p)
      (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 := by
    ext U; rfl
  have hθy : MassGap.LatticeReflection.ireflObs τ (2 * p)
        (x - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
      = MassGap.LatticeReflection.ireflObs τ (2 * p) x
        - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
    rw [map_sub, map_smul, hθ1]
  have hy : x - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
        • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
    Submodule.sub_mem _ hx
      (Submodule.smul_mem _ _ (MassGap.GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg τ p))
  obtain ⟨y, hyv⟩ : ∃ y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p),
      (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        = x - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :=
    ⟨⟨_, hy⟩, rfl⟩
  refine ⟨y, ?_, fun c => ?_⟩
  · rw [PeriodicReduce.periodic_form_vac τ p hN β y, hyv, hθy,
      MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_smul,
      MassGap.DLRLimit.State.map_one]
    ring
  · show periodicConn τ p hN β x c
      = (periodicGaugeInvData τ p hN β).form y (((periodicGaugeInvData τ p hN β).T ^ c) y)
    rw [PeriodicReduce.periodic_form_pow τ p hN β y c, hyv, hθy,
      MassGap.GaugeInvariantAlgebra.iterate_shift_sub_smul_one τ c x
        (periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x))]
    unfold periodicConn
    exact (PeriodicReduce.state_centred_mul (periodicState hN β) _ _).symm

#print axioms exists_orth_periodicConn

/-- **One observable at the periodic state: weight, tower and decay.** At `0 ≤ β`, `0 < r` and `x`
in the gauge-invariant half-space algebra, there is a finite measure `ν` on `[0, 1]` with
`periodicConn τ p hN β x t = ∫ λᵗ dν` at every `t`, and for it
`ν {λ | r < λ} = 0 ↔ ExpMomentTower (periodicConn τ p hN β x) (−log r)` and
`ExpMomentTower (periodicConn τ p hN β x) (−log r) ↔ ∀ t, periodicConn … t ≤ rᵗ · periodicConn … 0`.
The measure is `ZoomStep.specMeasure` of the orthogonal element of `exists_orth_periodicConn`
(`lagProfile_eq_moment`, `PeriodicState.periodic_positiveTransfer`); the equivalences are
`null_above_iff_expMomentTower` and `null_above_iff_decay`.

DERIVED: `4` is the spacetime dimension; `0` and `1` are the interval's ends; `0` is the excluded
gauge rank, the lower end of `β` and `r`, the null weight, and the base lag. -/
theorem periodicConn_moment_equivalences (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hx : x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)
    {r : ℝ} (hr : 0 < r) :
    ∃ ν : Measure (Set.Icc (0 : ℝ) 1), IsFiniteMeasure ν
      ∧ (∀ t : ℕ, periodicConn τ p hN β x t = ∫ l, (l : ℝ) ^ t ∂ν)
      ∧ (ν {l : Set.Icc (0 : ℝ) 1 | r < (l : ℝ)} = 0
          ↔ ExpMomentTower (periodicConn τ p hN β x) (-Real.log r))
      ∧ (ExpMomentTower (periodicConn τ p hN β x) (-Real.log r)
          ↔ ∀ t : ℕ, periodicConn τ p hN β x t ≤ r ^ t * periodicConn τ p hN β x 0) := by
  obtain ⟨y, -, hy⟩ := exists_orth_periodicConn τ p hN β x hx
  haveI := ZoomStep.specMeasure_isFinite (opT (periodicGaugeInvData τ p hN β))
    (isSelfAdjoint_opT (periodicGaugeInvData τ p hN β))
    ((Pre.ofPair (periodicGaugeInvData τ p hN β).toReflForm y 0
      : Pre (periodicGaugeInvData τ p hN β).toReflForm)
      : H (periodicGaugeInvData τ p hN β).toReflForm)
  have hν : ∀ t : ℕ, periodicConn τ p hN β x t
      = ∫ l, (l : ℝ) ^ t ∂(ZoomStep.specMeasure (opT (periodicGaugeInvData τ p hN β))
          (isSelfAdjoint_opT (periodicGaugeInvData τ p hN β))
          ((Pre.ofPair (periodicGaugeInvData τ p hN β).toReflForm y 0
            : Pre (periodicGaugeInvData τ p hN β).toReflForm)
            : H (periodicGaugeInvData τ p hN β).toReflForm)) :=
    fun t => (hy t).trans
      (lagProfile_eq_moment _ (periodic_positiveTransfer τ p hN hβ) y t)
  refine ⟨_, ?_, hν, null_above_iff_expMomentTower _ hν hr,
    (null_above_iff_expMomentTower _ hν hr).symm.trans (null_above_iff_decay _ hν hr)⟩
  infer_instance

#print axioms periodicConn_moment_equivalences

/-- **The tower of the whole algebra at one coupling**: every `x` in the gauge-invariant half-space
algebra has `ExpMomentTower (periodicConn τ p hN β x) μ`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank. `μ` is the caller's
rate. -/
def AlgebraTower (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β μ : ℝ) : Prop :=
  ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ExpMomentTower (periodicConn τ p hN β x) μ

/-- **At the periodic state the gap is the tower of every observable.** At `0 ≤ β` and `0 < r`:
`TransferGap.GapAt (periodicGaugeInvData τ p hN β) r` holds exactly when every `x` in the
gauge-invariant half-space algebra has `ExpMomentTower (periodicConn τ p hN β x) (−log r)`
(`AlgebraTower τ p hN β (−log r)`). `gapAt_iff_expMomentTower` under
`PeriodicState.periodic_positiveTransfer`; forward through `exists_orth_periodicConn`, back through
`periodicConn_of_orth`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the lower end of `β` and
`r`. -/
theorem periodic_gapAt_iff_expMomentTower (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    {r : ℝ} (hr : 0 < r) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) r ↔ AlgebraTower τ p hN β (-Real.log r) := by
  rw [gapAt_iff_expMomentTower _ (periodic_positiveTransfer τ p hN hβ) hr]
  unfold AlgebraTower
  constructor
  · intro h x hx
    obtain ⟨y, hy0, hy⟩ := exists_orth_periodicConn τ p hN β x hx
    rw [show periodicConn τ p hN β x
        = ChessboardRead.lagProfile (periodicGaugeInvData τ p hN β) y from funext hy]
    exact h y hy0
  · intro h y hy
    have hy' := h (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) y.2
    rw [show periodicConn τ p hN β (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        = ChessboardRead.lagProfile (periodicGaugeInvData τ p hN β) y
        from funext (periodicConn_of_orth τ p hN β y hy)] at hy'
    exact hy'

#print axioms periodic_gapAt_iff_expMomentTower

/-! ## 5. Physical units -/

/-- **`FixedWindowDecay` is the tower at a fixed physical rate.** At `2 ≤ N` and `0 < L`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L` holds exactly when some `M > 0` has, at every large
`β`, `ExpMomentTower (periodicConn τ p hN β x) (M · aRun N β)` for every `x` in the gauge-invariant
half-space algebra (`AlgebraTower τ p hN β (M · aRun N β)`).

Through `WeakCouplingWindow.fixedWindowDecay_iff`. Forward: a rate `r` with `PeriodicClayGapAt` and
`c / L ≤ −log r / aRun N β` gives `GapAt` at `r` (`WeakCouplingWindow.gapAt_of_periodicClayGapAt`),
hence the tower at `−log r` (`periodic_gapAt_iff_expMomentTower`), hence at
`(c / L) · aRun N β ≤ −log r` (`expMomentTower_mono`); `M = c / L`. Back: at `β > 0` the rate
`r = e^{−M · aRun N β}` lies in `(0, 1)` and has `−log r = M · aRun N β`, so the tower is `GapAt` at
`r` (`periodic_gapAt_iff_expMomentTower`), hence `PeriodicClayGapAt` at `r`
(`GapStep.periodic_clayGapAt_of_gapAt`), with `c = M · L` and physical rate exactly `M`. No
normalisation of the lag-zero pairing is assumed: the tower carries no constant.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the lower end of `L` and `M`. -/
theorem fixedWindowDecay_iff_momentTower (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L ↔
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ β in Filter.atTop,
        AlgebraTower τ p hN β (M * MassGap.AsymptoticScaling.aRun N β) := by
  have hN1 : 1 ≤ N := by omega
  rw [WeakCouplingWindow.fixedWindowDecay_iff τ p hN2 hN hL]
  constructor
  · rintro ⟨c, hc, hev⟩
    refine ⟨c / L, div_pos hc hL, ?_⟩
    filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with β hβ hβ0
    obtain ⟨r, hcl, hrate⟩ := hβ
    have hg := WeakCouplingWindow.gapAt_of_periodicClayGapAt τ p hN hcl
    obtain ⟨hr0, -, -, -, -, -, -⟩ := hcl
    have ha : 0 < MassGap.AsymptoticScaling.aRun N β :=
      MassGap.AsymptoticScaling.aRun_pos hN1 hβ0
    have hle : c / L * MassGap.AsymptoticScaling.aRun N β ≤ -Real.log r :=
      (le_div_iff₀ ha).mp hrate
    unfold AlgebraTower
    intro x hx
    exact expMomentTower_mono hle
      ((periodic_gapAt_iff_expMomentTower τ p hN hβ0.le hr0).mp hg x hx)
  · rintro ⟨M, hM, hev⟩
    refine ⟨M * L, mul_pos hM hL, ?_⟩
    filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with β hβ hβ0
    have ha : 0 < MassGap.AsymptoticScaling.aRun N β :=
      MassGap.AsymptoticScaling.aRun_pos hN1 hβ0
    have hμ : 0 < M * MassGap.AsymptoticScaling.aRun N β := mul_pos hM ha
    have hr0 : 0 < Real.exp (-(M * MassGap.AsymptoticScaling.aRun N β)) := Real.exp_pos _
    have hr1 : Real.exp (-(M * MassGap.AsymptoticScaling.aRun N β)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    have hlog : -Real.log (Real.exp (-(M * MassGap.AsymptoticScaling.aRun N β)))
        = M * MassGap.AsymptoticScaling.aRun N β := by
      rw [Real.log_exp, neg_neg]
    have hg : TransferGap.GapAt (periodicGaugeInvData τ p hN β)
        (Real.exp (-(M * MassGap.AsymptoticScaling.aRun N β))) :=
      (periodic_gapAt_iff_expMomentTower τ p hN hβ0.le hr0).mpr (by rw [hlog]; exact hβ)
    refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0.le hr0 hr1 hg, ?_⟩
    exact le_of_eq (by
      rw [hlog, mul_div_cancel_right₀ M hL.ne', mul_div_cancel_right₀ M ha.ne'])

#print axioms fixedWindowDecay_iff_momentTower

end Periodic

end MassGap.MomentTower
