import Mathlib
import MassGap.ChessboardRead
import MassGap.AsymptoticScaling
import MassGap.GapStep

/-!
# MassGap.WeakCouplingWindow — the weak-coupling gap from one inequality at a fixed physical window

## What it gives

The target along `β → ∞` is `TransferGap.GapAt` at `PeriodicState.periodicGaugeInvData τ p hN β`, at a
rate `r` whose physical value `−log r / aRun N β` is bounded below by one constant over all large `β`
(`aRun N` the two-loop running spacing of `AsymptoticScaling`). This module composes the tree's pieces
into that statement from one input, `FixedWindowDecay τ p hN L`, and proves the input necessary as well.

1. `GapStep.periodic_clayGapAt_of_gapAt`: at `2 ≤ N`, `0 ≤ β`, `0 < r < 1`, `GapAt` at the periodic
   data gives `PeriodicContent.PeriodicClayGapAt τ p hN β r` at the same rate;
   `gapAt_of_periodicClayGapAt` is the way back.
2. `torusLag_le_of_gapAt`, `torusLagClear_of_gapAt`, `torusLagClear_iff_gapAt`: at `0 ≤ r`, `GapAt` at
   rate `r` gives
   the single-lag inequality on the periodic lattices at every lag `m`, with any factor `q ≥ rᵐ`. Each
   observable is centred at its reflected mean, as in `PeriodicReduce.periodic_torusReads_of_localReads`;
   the centred observable is orthogonal to the vacuum, `ChessboardRead.lag_of_gapAt` bounds its profile,
   and `PeriodicReduce.slack_of_nonneg_filter` returns the state inequality to the lattices with slack.
   With `ChessboardRead.gapAt_of_lag`, at `0 ≤ β`, `m ≠ 0`, `0 ≤ r`:
   `ChessboardRead.TorusLagClear τ p hN β m r ↔ GapAt … r`.
3. `stepRate q m = q^{1/m}`: a factor `q` at lag `m` is the rate `q^{1/m}` per lattice step
   (`stepRate_pow`), and at `0 < q < 1`, `m ≠ 0`, `0 < a`, `0 < L` and `m · a ≤ L` its physical rate is
   at least `−log q / L` (`physical_rate_ge`); the spacing cancels as in
   `ZeroMode.gap_phys_of_fixed_screen`.
4. `gapAt_physical_of_fixedWindowDecay`: at `2 ≤ N` and `0 < L`, from `FixedWindowDecay τ p hN L` there
   is `c > 0` such that at every large `β`, `GapAt` and `PeriodicClayGapAt` hold at a rate `r` with
   `c / L ≤ −log r / aRun N β` (the proof takes `c = −log q`).
   `su3_gapAt_physical_of_fixedWindowDecay` states it at `N = 3`, spacing `aRun 3`, with a threshold
   `β₀`.
5. `fixedWindowDecay_of_physical_gap`, `fixedWindowDecay_iff`: the converse. At `1 ≤ N` and `0 < L`, the
   Clay gap at every large `β` with physical rate at least `c/L`, `c > 0`, gives `FixedWindowDecay`; the
   proof takes the factor `e^{−c/2}` at the lag `⌊L / aRun N β⌋₊` (`window_lag_exists`,
   `eventually_aRun_le`). Since `c` is existential the window sets no scale:
   `fixedWindowDecay_window_free` carries `FixedWindowDecay` from one `L > 0` to every `L' > 0`, and the
   input is the uniform physical gap.

## The input

`FixedWindowDecay τ p hN L`: one factor `q ∈ (0, 1)` such that at every large `β` there is a lag `m ≥ 1`
of physical length `m · aRun N β ≤ L` at which, for every gauge-invariant half-space observable, the
connected reflected pairing on the periodic lattices at lag `m` is at most `q` times its lag-zero value,
with every slack, along `periodicUltra hN β`.

The tree bounds `PeriodicReduce.torusConn` at `β > 0` only on the strong-coupling interval
(`PeriodicStrongCoupling.torusState_connected_abs_le_of_cubes`); outside this module and that one,
`torusConn`, `torusState` and `periodicState` occur in code only in `PeriodicState`, `PeriodicReduce`,
`PeriodicContent`, `ChessboardRead` and `ThreePointN` (the last under `WilsonThreePointSeparation`, a
hypothesis), this module bounds `torusConn` only under `GapAt` taken as a
hypothesis, and `GapStep` takes `ChessboardRead.TorusLagClear` and its step between couplings
(`GapStep.PhysStep`) as hypotheses; none of these bounds a connected pairing from above. The cluster
expansion (`StrongCoupling`, `StrongCouplingGap.norm_Tq_le_of_orth`) needs `coreRate 64 β < 1`, an
interval `(0, b)` of couplings (`FreeLimit.exists_strong_coupling_region`), at the free-boundary limit
state and at the periodic state (`PeriodicStrongCoupling.periodic_gapAt_strong_coupling`). `CosAvgStability` moves a read between two couplings only under a
multiplicative or `L¹` control of the profile that it takes as a hypothesis. `RefinementLaw` relates an
operator to its own functional-calculus root and never identifies the Wilson transfer operator at one
coupling with a root of the one at another. The block-repeat identities of `Entroptics.Diffraction` take
the repetition as a hypothesis. `AsymptoticScaling` and `Running` fix the spacing function and carry no
dynamics. `ArmAtEachCoupling`, `NonnegArm`, `SubstrateArms`, `ApertureRoute`, `ApertureFamily`,
`ClayFromConfinement` and `Complete` hold under `NonnegArm.LawAbove`,
`ArmAtEachCoupling.LawAboveAtCoupling`, `SubstrateArms.LawAboveAt` or
`ApertureRoute.ConfinesAtAnAperture`, taken as hypotheses, about the `wilsonCorrAt` ensemble, not the
periodic state. `Capacity`, `Condensation`, `Margin` and `Apriori` hold under inequalities with no Wilson
producer.

## Scope

`FixedWindowDecay` is a hypothesis of every forward theorem here. At one `β ≥ 0`, `m ≠ 0` and `0 ≤ q`,
the input's inequality at lag `m` and factor `q` is `GapAt` at `q^{1/m}` (`torusLagClear_iff_gapAt`,
`stepRate_pow`); along `β → ∞` it is the Clay gap with physical rate bounded below
(`fixedWindowDecay_iff`, at `2 ≤ N` and `0 < L`), so it is the weak-coupling gap restated on the
periodic lattices. What the pieces remove is every other lag (log-convexity,
`ChessboardRead.lagProfile_log_convex`), the reads, and the spacing (`physical_rate_ge`).
Four-dimensional `U(1)` lattice gauge theory with the Villain action has a massless phase at large `β`
(Guth, Phys. Rev. D 21 (1980) 2291; Fröhlich–Spencer, Commun. Math. Phys. 83 (1982) 411), so the input
needs a non-abelian estimate.
-/

namespace MassGap.WeakCouplingWindow

open MassGap MassGap.GNSHilbert MassGap.PeriodicState

variable {N : ℕ}

/-! ## 1. The Clay gap at the periodic state and `GapAt` -/

section Assemble

/-- **`GapAt` from the Clay gap at the periodic state.** The way back from
`GapStep.periodic_clayGapAt_of_gapAt`. The contraction conjunct of
`PeriodicContent.PeriodicClayGapAt τ p hN β r` is `GapAt` at `r` on the completion
(`GNSCompare.gapAt_iff_opT_contracts` at `0 ≤ r`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
theorem gapAt_of_periodicClayGapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β r : ℝ}
    (h : MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β r) :
    MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r := by
  obtain ⟨hr0, -, -, -, -, hcon, -⟩ := h
  exact (MassGap.GNSCompare.gapAt_iff_opT_contracts (periodicGaugeInvData τ p hN β) hr0.le).mpr
    hcon

#print axioms gapAt_of_periodicClayGapAt

end Assemble

/-! ## 2. The single-lag inequality on the periodic lattices from `GapAt` -/

section Converse

/-- **`GapAt` gives the single-lag inequality on the periodic lattices, with any factor above `rᵐ`.**
At rate `0 ≤ r`, lag `m` and `rᵐ ≤ q`: for every gauge-invariant half-space observable `x` and every
`ε > 0`, eventually along `periodicUltra hN β`,
`torusConn τ p hN β j x m ≤ q · torusConn τ p hN β j x 0 + ε`.

`y = x − ν(θx)·1` (`ν = periodicState hN β`) lies in the algebra and is orthogonal to the vacuum
(`PeriodicReduce.periodic_form_vac`); its profile `D.form y (Tᶜ y)` is the connected pairing of `x` at
lag `c` (`PeriodicReduce.periodic_form_pow`, `GaugeInvariantAlgebra.iterate_shift_sub_smul_one`,
`PeriodicReduce.state_centred_mul`), the construction of
`PeriodicReduce.periodic_torusReads_of_localReads`. `ChessboardRead.lag_of_gapAt` bounds the lag-`m`
pairing by `rᵐ` times the lag-zero one, which is `D.form y y ≥ 0`, so by `q` times it; the lattice
pairings converge to the state's (`PeriodicReduce.tendsto_torusConn`), and
`PeriodicReduce.slack_of_nonneg_filter` gives the slack form.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `r`, the sign
of the slack, and the contact lag; `2` in the proof's `2 * p` is the doubling of the reflection plane,
and `1` there is the constant observable. -/
theorem torusLag_le_of_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r) (m : ℕ) {q : ℝ}
    (hq : r ^ m ≤ q) :
    ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x m
            ≤ q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε := by
  intro x hx ε hε
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
  have hvac : (periodicGaugeInvData τ p hN β).form y (periodicGaugeInvData τ p hN β).vac = 0 := by
    rw [MassGap.PeriodicReduce.periodic_form_vac τ p hN β y, hyv, hθy,
      MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_smul,
      MassGap.DLRLimit.State.map_one]
    ring
  have hprof : ∀ c : ℕ,
      (periodicGaugeInvData τ p hN β).form y (((periodicGaugeInvData τ p hN β).T ^ c) y)
        = periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
          - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
            * periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x) := by
    intro c
    rw [MassGap.PeriodicReduce.periodic_form_pow τ p hN β y c, hyv, hθy,
      MassGap.GaugeInvariantAlgebra.iterate_shift_sub_smul_one τ c x
        (periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x))]
    exact MassGap.PeriodicReduce.state_centred_mul (periodicState hN β) _ _
  have hlag := MassGap.ChessboardRead.lag_of_gapAt (periodicGaugeInvData τ p hN β) hr hg m y hvac
  have hnn : 0 ≤ (periodicGaugeInvData τ p hN β).form y y :=
    (periodicGaugeInvData τ p hN β).form_nonneg y
  have h0 : (periodicGaugeInvData τ p hN β).form y y
      = (periodicGaugeInvData τ p hN β).form y (((periodicGaugeInvData τ p hN β).T ^ 0) y) := by
    rw [pow_zero, Module.End.one_apply]
  rw [h0, hprof 0] at hnn
  rw [h0, hprof m, hprof 0] at hlag
  have hstate := le_trans hlag (mul_le_mul_of_nonneg_right hq hnn)
  have hu := ((MassGap.PeriodicReduce.tendsto_torusConn τ p hN β x 0).const_mul q).sub
    (MassGap.PeriodicReduce.tendsto_torusConn τ p hN β x m)
  filter_upwards [MassGap.PeriodicReduce.slack_of_nonneg_filter hu (sub_nonneg.mpr hstate) ε hε]
    with j hj
  have hj' : -ε ≤ q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0
      - MassGap.PeriodicReduce.torusConn τ p hN β j x m := hj
  show MassGap.PeriodicReduce.torusConn τ p hN β j x m
      ≤ q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε
  linarith

#print axioms torusLag_le_of_gapAt

/-- **`GapAt` gives `TorusLagClear` at every lag, at the same rate.** `torusLag_le_of_gapAt` at
`q = rᵐ`. `ChessboardRead.gapAt_of_lag` with `ChessboardRead.periodic_form_lag_of_torusLagClear` gives the other
direction; together they are `torusLagClear_iff_gapAt`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `r`. -/
theorem torusLagClear_of_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hg : MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r) (m : ℕ) :
    MassGap.ChessboardRead.TorusLagClear τ p hN β m r :=
  torusLag_le_of_gapAt τ p hN β hr hg m le_rfl

#print axioms torusLagClear_of_gapAt

/-- **On the periodic lattices the single lag is the gap.** At `0 ≤ β`, a lag `m ≠ 0` and `0 ≤ r`:
`ChessboardRead.TorusLagClear τ p hN β m r ↔ TransferGap.GapAt (periodicGaugeInvData τ p hN β) r`.
Forward: `ChessboardRead.periodic_form_lag_of_torusLagClear`, then `ChessboardRead.gapAt_of_lag` with
`PeriodicState.periodic_positiveTransfer`. Back: `torusLagClear_of_gapAt`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β` and `r`, and
the excluded lag. -/
theorem torusLagClear_iff_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {m : ℕ}
    (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    MassGap.ChessboardRead.TorusLagClear τ p hN β m r
      ↔ MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r :=
  ⟨fun h => MassGap.ChessboardRead.gapAt_of_lag (periodicGaugeInvData τ p hN β)
      (periodic_positiveTransfer τ p hN hβ) hm hr
      (fun x hx => MassGap.ChessboardRead.periodic_form_lag_of_torusLagClear τ p hN β m r h x hx),
    fun hg => torusLagClear_of_gapAt τ p hN β hr hg m⟩

#print axioms torusLagClear_iff_gapAt

end Converse

/-! ## 3. A factor at one lag as a rate per step, and in physical units -/

section Rate

/-- The rate per lattice step of a factor `q` over `m` steps: `q^{1/m}`.

DERIVED: `1` is the numerator of the exponent `1/m`, the `m`-th root. -/
noncomputable def stepRate (q : ℝ) (m : ℕ) : ℝ := q ^ ((1 : ℝ) / (m : ℝ))

/-- `(q^{1/m})ᵐ = q` at `0 ≤ q` and `m ≠ 0`: `Real.rpow_natCast`, `Real.rpow_mul`,
`one_div_mul_cancel`.

DERIVED: `0` is the lower end of `q` and the excluded lag. -/
theorem stepRate_pow {q : ℝ} (hq : 0 ≤ q) {m : ℕ} (hm : m ≠ 0) : stepRate q m ^ m = q := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  unfold stepRate
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq, one_div_mul_cancel hm', Real.rpow_one]

#print axioms stepRate_pow

/-- `0 < q^{1/m}` at `0 < q`.

DERIVED: `0` is the lower end of `q` and of the rate. -/
theorem stepRate_pos {q : ℝ} (hq : 0 < q) (m : ℕ) : 0 < stepRate q m := by
  unfold stepRate
  exact Real.rpow_pos_of_pos hq _

#print axioms stepRate_pos

/-- `q^{1/m} < 1` at `0 ≤ q < 1` and `m ≠ 0`: `Real.rpow_lt_one` at the positive exponent `1/m`.

DERIVED: `0` is the lower end of `q` and the excluded lag; `1` is the upper end of `q` and of the
rate. -/
theorem stepRate_lt_one {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) {m : ℕ} (hm : m ≠ 0) :
    stepRate q m < 1 := by
  unfold stepRate
  exact Real.rpow_lt_one hq hq1 (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)))

#print axioms stepRate_lt_one

/-- `−log q^{1/m} = −log q / m` at `0 < q`: `Real.log_rpow`.

DERIVED: `0` is the lower end of `q`. -/
theorem neg_log_stepRate {q : ℝ} (hq : 0 < q) (m : ℕ) :
    -Real.log (stepRate q m) = -Real.log q / (m : ℝ) := by
  unfold stepRate
  rw [Real.log_rpow hq]
  ring

#print axioms neg_log_stepRate

/-- **The physical rate of a factor at a fixed window.** At `0 < q < 1`, `m ≠ 0`, spacing `a > 0` and a
window `L > 0` with `m · a ≤ L`: `−log q / L ≤ −log q^{1/m} / a`. The rate per step is `−log q / m`
(`neg_log_stepRate`), so its physical value is `−log q / (m · a)`, at least `−log q / L`. The spacing
cancels, as in `ZeroMode.gap_phys_of_fixed_screen`.

DERIVED: `0` is the lower end of `q`, `a`, `L`, and the excluded lag; `1` is the upper end of `q`. -/
theorem physical_rate_ge {q a L : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : m ≠ 0)
    (ha : 0 < a) (hL : 0 < L) (hwin : (m : ℝ) * a ≤ L) :
    -Real.log q / L ≤ -Real.log (stepRate q m) / a := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hlogq : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  rw [neg_log_stepRate hq0 m, div_div, div_le_div_iff₀ hL (mul_pos hm0 ha)]
  exact mul_le_mul_of_nonneg_left hwin hlogq.le

#print axioms physical_rate_ge

/-- At `0 ≤ q` and `m ≠ 0`, the single-lag inequality with factor `q` at lag `m` gives
`ChessboardRead.TorusLagClear` at the rate `q^{1/m}` (`stepRate_pow`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `q`, the
excluded lag, the sign of the slack, and the contact lag. -/
theorem torusLagClear_stepRate (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {q : ℝ} (hq : 0 ≤ q)
    {m : ℕ} (hm : m ≠ 0)
    (h : ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x m
            ≤ q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε) :
    MassGap.ChessboardRead.TorusLagClear τ p hN β m (stepRate q m) := by
  intro x hx ε hε
  rw [stepRate_pow hq hm]
  exact h x hx ε hε

#print axioms torusLagClear_stepRate

end Rate

/-! ## 4. The input, and the weak-coupling gap from it -/

section Window

/-- **THE INPUT: decay by a fixed factor across a fixed physical window, at every large coupling.**
There is one factor `q ∈ (0, 1)` such that for all large `β` there is a lag `m ≥ 1` of physical length
`m · aRun N β` at most `L` at which, for every gauge-invariant half-space observable `x` and every slack
`ε > 0`, eventually along `periodicUltra hN β`,

    torusConn τ p hN β j x m  ≤  q · torusConn τ p hN β j x 0 + ε

— the connected reflected-shifted pairing of `x` across the window, in the periodic Wilson state of
extent `2(j + 1)`, at most `q` times its lag-zero value. `q` and `L` do not depend on `β`.
`fixedWindowDecay_iff`: at `2 ≤ N` and `0 < L` this holds exactly when the Clay gap at the periodic
state holds at every large `β` with physical rate bounded below by a positive constant; the constant
is written `c/L` with `c` existential, so the condition is the same at every `L > 0`
(`fixedWindowDecay_window_free`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `q`, the
excluded lag, the sign of the slack, and the contact lag; `1` is the upper end of `q`, the factor the
decay must beat. `L` is the caller's window. -/
def FixedWindowDecay (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ᶠ β in Filter.atTop, ∃ m : ℕ, m ≠ 0 ∧
    (m : ℝ) * MassGap.AsymptoticScaling.aRun N β ≤ L ∧
    ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x m
            ≤ q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε

/-- **THE WEAK-COUPLING GAP FROM THE INPUT.** At `2 ≤ N`, a window `L > 0` and
`FixedWindowDecay τ p hN L`: there is `c > 0` such that at every large `β`
some rate `r` has `TransferGap.GapAt (periodicGaugeInvData τ p hN β) r`,
`PeriodicContent.PeriodicClayGapAt τ p hN β r` (spectrum in `{1} ∪ [0, r]`, the vacuum complement
contracted by `r < 1` and non-zero), and physical rate `−log r / aRun N β ≥ c/L`.

The proof takes `c = −log q` for the input's factor `q`, and at each large `β` the rate `r = q^{1/m}`: the lag inequality is `ChessboardRead.TorusLagClear` at
`r` (`torusLagClear_stepRate`), hence `GapAt` at `r` (`torusLagClear_iff_gapAt`), hence the Clay gap
(`GapStep.periodic_clayGapAt_of_gapAt`), and `m · aRun N β ≤ L` puts the physical rate at `−log q / L` or above
(`physical_rate_ge`, `AsymptoticScaling.aRun_pos`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance of the
real trace; `0` is the excluded rank, the lower end of `L` and of `c`. -/
theorem gapAt_physical_of_fixedWindowDecay (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) (h : FixedWindowDecay τ p hN L) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in Filter.atTop, ∃ r : ℝ,
      MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r
        ∧ MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β r
        ∧ c / L ≤ -Real.log r / MassGap.AsymptoticScaling.aRun N β := by
  obtain ⟨q, hq0, hq1, hev⟩ := h
  have hN1 : 1 ≤ N := by omega
  refine ⟨-Real.log q, neg_pos.mpr (Real.log_neg hq0 hq1), ?_⟩
  filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with β hβ hβ0
  obtain ⟨m, hm, hwin, hlag⟩ := hβ
  have ha : 0 < MassGap.AsymptoticScaling.aRun N β :=
    MassGap.AsymptoticScaling.aRun_pos hN1 hβ0
  have hr0 : 0 < stepRate q m := stepRate_pos hq0 m
  have hr1 : stepRate q m < 1 := stepRate_lt_one hq0.le hq1 hm
  have hg : MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) (stepRate q m) :=
    (torusLagClear_iff_gapAt τ p hN hβ0.le hm hr0.le).mp
      (torusLagClear_stepRate τ p hN β hq0.le hm hlag)
  exact ⟨stepRate q m, hg,
    MassGap.GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0.le hr0 hr1 hg,
    physical_rate_ge hq0 hq1 hm ha hL hwin⟩

#print axioms gapAt_physical_of_fixedWindowDecay

/-- **The same at `SU(3)`, along the `SU(3)` running spacing, with a threshold.** Under
`FixedWindowDecay τ p hN L` at `N = 3` and `L > 0`: there are `c > 0` and `β₀` such that every
`β ≥ β₀` has a rate `r` with `GapAt` and `PeriodicClayGapAt` at `r` and `c/L ≤ −log r / aRun 3 β`.
`gapAt_physical_of_fixedWindowDecay` and `Filter.eventually_atTop`.

DERIVED: `4` is the spacetime dimension; `3` is the colour count of `SU(3)`, the `N` of the spacing `aRun 3`; `2` in the
discharged `2 ≤ 3` is the least rank with a non-zero Haar variance; `0` is the lower end of `L` and
of `c`, and the excluded rank. -/
theorem su3_gapAt_physical_of_fixedWindowDecay (τ : Fin 4) (p : ℤ) (hN : (3 : ℕ) ≠ 0) {L : ℝ}
    (hL : 0 < L) (h : FixedWindowDecay τ p hN L) :
    ∃ c : ℝ, 0 < c ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → ∃ r : ℝ,
      MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r
        ∧ MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β r
        ∧ c / L ≤ -Real.log r / MassGap.AsymptoticScaling.aRun 3 β := by
  obtain ⟨c, hc, hev⟩ := gapAt_physical_of_fixedWindowDecay τ p (by norm_num) hN hL h
  obtain ⟨β₀, hβ₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨c, hc, β₀, hβ₀⟩

#print axioms su3_gapAt_physical_of_fixedWindowDecay

end Window

/-! ## 5. The input is necessary -/

section Necessary

/-- **The running spacing is eventually below any positive bound.** At `1 ≤ N` and `0 < b`, for all
large `β`, `aRun N β ≤ b`: `aRun N β = aRunStd N (2β)`, and at a standard coupling `β'` past
`11N²/(24π²)` `AsymptoticScaling.aRunStd_le_inv_of_base_ge_one` bounds `aRunStd N β'` by `22N²/(3π²β')`,
which is at most `b` once `β' ≥ 22N²/(3π²b)`; `β' = 2β` runs to infinity with `β`.

DERIVED: `1` is the least colour count, which keeps `N²` non-zero; `0` is the sign of `b`. The `11`,
`24`, `22`, `3` and the `2`s of `N²` and `π²` in the proof are `aRunStd`'s own constants, carried from
`AsymptoticScaling.aRunStd_le_inv_of_base_ge_one`; `2` is `aRun`'s factor. -/
theorem eventually_aRun_le (hN : 1 ≤ N) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ β in Filter.atTop, MassGap.AsymptoticScaling.aRun N β ≤ b := by
  suffices hstd : ∀ᶠ β in Filter.atTop, MassGap.AsymptoticScaling.aRunStd N β ≤ b from
    (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually hstd
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (0 : ℝ) < 11 * (N : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hN0 2)
  have hπ : (0 : ℝ) < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have h24 : (0 : ℝ) < 24 * Real.pi ^ 2 := mul_pos (by norm_num) hπ
  have h3b : (0 : ℝ) < 3 * Real.pi ^ 2 * b := mul_pos (mul_pos (by norm_num) hπ) hb
  filter_upwards [Filter.eventually_ge_atTop (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2)),
    Filter.eventually_ge_atTop (22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * b)),
    Filter.eventually_gt_atTop (0 : ℝ)] with β h1 h2 h3
  have hbase : (1 : ℝ) ≤ (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ hN2]
    rw [div_le_iff₀ h24] at h1
    linarith
  have h3β : (0 : ℝ) < 3 * Real.pi ^ 2 * β := mul_pos (mul_pos (by norm_num) hπ) h3
  refine le_trans (MassGap.AsymptoticScaling.aRunStd_le_inv_of_base_ge_one hN h3 hbase) ?_
  rw [div_le_iff₀ h3β]
  rw [div_le_iff₀ h3b] at h2
  linarith

#print axioms eventually_aRun_le

/-- **A lag filling at least half the window.** At spacing `0 < a ≤ L/2` there is a lag `m ≠ 0` with
`L/2 ≤ m · a ≤ L`: `m = ⌊L/a⌋₊`, which is non-zero because `L/a ≥ 2` (`Nat.lt_floor_add_one`,
`Nat.floor_le`).

DERIVED: `0` is the lower end of `a` and the excluded lag. CHOSEN: `2` in `L/2`, the fraction of the
window the lag is asked to fill; any fixed fraction in `(0, 1)` serves, and it sets the factor
`e^{−c/2}` of `fixedWindowDecay_of_physical_gap`. -/
theorem window_lag_exists {a L : ℝ} (ha : 0 < a) (ha2 : a ≤ L / 2) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : ℝ) * a ≤ L ∧ L / 2 ≤ (m : ℝ) * a := by
  have hL : 0 < L := by linarith
  have hfl : L / a < (⌊L / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (L / a)
  have hle : (⌊L / a⌋₊ : ℝ) ≤ L / a := Nat.floor_le (div_nonneg hL.le ha.le)
  have hfl' : L < ((⌊L / a⌋₊ : ℝ) + 1) * a := (div_lt_iff₀ ha).mp hfl
  have hle' : (⌊L / a⌋₊ : ℝ) * a ≤ L := (le_div_iff₀ ha).mp hle
  have h2 : (2 : ℝ) ≤ L / a := (le_div_iff₀ ha).mpr (by linarith)
  have hpos : (0 : ℝ) < (⌊L / a⌋₊ : ℝ) := by linarith
  exact ⟨⌊L / a⌋₊, (Nat.cast_pos.mp hpos).ne', hle', by linarith⟩

#print axioms window_lag_exists

/-- **The input from the weak-coupling gap.** At `1 ≤ N` and `L > 0`: if some `c > 0` has, at every
large `β`, a rate `r` with `PeriodicContent.PeriodicClayGapAt τ p hN β r` and
`c/L ≤ −log r / aRun N β`, then `FixedWindowDecay τ p hN L`; the proof takes the factor `e^{−c/2}`.

Once `aRun N β ≤ L/2` (`eventually_aRun_le`), the lag `m` of `window_lag_exists` has
`L/2 ≤ m · aRun N β ≤ L`, so `m · (−log r) ≥ c/2` and `rᵐ ≤ e^{−c/2}`; the contraction conjunct is
`GapAt` at `r` (`gapAt_of_periodicClayGapAt`), and `torusLag_le_of_gapAt` at the factor `e^{−c/2}`
gives the lag inequality.

DERIVED: `4` is the spacetime dimension; `1` is the least colour count; `0` is the excluded rank and the lower end of `L` and `c`.
The `2` of `e^{−c/2}` and of `L/2` is `window_lag_exists`'s CHOSEN half-window. -/
theorem fixedWindowDecay_of_physical_gap (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in Filter.atTop, ∃ r : ℝ,
      MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β r
        ∧ c / L ≤ -Real.log r / MassGap.AsymptoticScaling.aRun N β) :
    FixedWindowDecay τ p hN L := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨Real.exp (-(c / 2)), Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  filter_upwards [hev, eventually_aRun_le hN1 (half_pos hL), Filter.eventually_gt_atTop (0 : ℝ)]
    with β hβ ha2 hβ0
  obtain ⟨r, hgap, hrate⟩ := hβ
  have ha : 0 < MassGap.AsymptoticScaling.aRun N β := MassGap.AsymptoticScaling.aRun_pos hN1 hβ0
  obtain ⟨m, hm, hwin, hhalf⟩ := window_lag_exists ha ha2
  have hg : MassGap.TransferGap.GapAt (periodicGaugeInvData τ p hN β) r :=
    gapAt_of_periodicClayGapAt τ p hN hgap
  obtain ⟨hr0, -, -, -, -, -, -⟩ := hgap
  have hA : c * MassGap.AsymptoticScaling.aRun N β ≤ -Real.log r * L :=
    (div_le_div_iff₀ hL ha).mp hrate
  have h1 : c * (L / 2) ≤ c * ((m : ℝ) * MassGap.AsymptoticScaling.aRun N β) :=
    mul_le_mul_of_nonneg_left hhalf hc.le
  have h2 : (m : ℝ) * (c * MassGap.AsymptoticScaling.aRun N β) ≤ (m : ℝ) * (-Real.log r * L) :=
    mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg m)
  have h3 : c / 2 * L ≤ (m : ℝ) * -Real.log r * L := by linarith
  have h4 : c / 2 ≤ (m : ℝ) * -Real.log r := le_of_mul_le_mul_right h3 hL
  have hq : r ^ m ≤ Real.exp (-(c / 2)) := by
    rw [← Real.exp_log hr0, ← Real.exp_nat_mul, Real.exp_le_exp]
    linarith
  exact ⟨m, hm, hwin, torusLag_le_of_gapAt τ p hN β hr0.le hg m hq⟩

#print axioms fixedWindowDecay_of_physical_gap

/-- **The input is the weak-coupling gap at the window.** At `2 ≤ N` and `L > 0`,
`FixedWindowDecay τ p hN L` holds exactly when some `c > 0` has, at every large `β`, a rate `r` with
`PeriodicContent.PeriodicClayGapAt τ p hN β r` and `c/L ≤ −log r / aRun N β`.
`gapAt_physical_of_fixedWindowDecay` and `fixedWindowDecay_of_physical_gap`. With `c` existential the
right side does not depend on `L` (`fixedWindowDecay_window_free`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the lower end of `L` and `c`. -/
theorem fixedWindowDecay_iff (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) :
    FixedWindowDecay τ p hN L ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in Filter.atTop, ∃ r : ℝ,
      MassGap.PeriodicContent.PeriodicClayGapAt τ p hN β r
        ∧ c / L ≤ -Real.log r / MassGap.AsymptoticScaling.aRun N β := by
  constructor
  · intro h
    obtain ⟨c, hc, hev⟩ := gapAt_physical_of_fixedWindowDecay τ p hN2 hN hL h
    refine ⟨c, hc, hev.mono (fun β hβ => ?_)⟩
    obtain ⟨r, _, hcl, hrate⟩ := hβ
    exact ⟨r, hcl, hrate⟩
  · exact fixedWindowDecay_of_physical_gap τ p (by omega) hN hL

#print axioms fixedWindowDecay_iff

/-- **The window sets no scale.** At `2 ≤ N`, `0 < L` and `0 < L'`, `FixedWindowDecay τ p hN L` gives
`FixedWindowDecay τ p hN L'`: through `fixedWindowDecay_iff`, the constant `c` at `L` becomes
`c·L'/L` at `L'`, with `c/L` unchanged.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the lower end of `L` and `L'`. -/
theorem fixedWindowDecay_window_free (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L L' : ℝ}
    (hL : 0 < L) (hL' : 0 < L') (h : FixedWindowDecay τ p hN L) : FixedWindowDecay τ p hN L' := by
  obtain ⟨c, hc, hev⟩ := (fixedWindowDecay_iff τ p hN2 hN hL).mp h
  refine (fixedWindowDecay_iff τ p hN2 hN hL').mpr ⟨c * L' / L, by positivity, ?_⟩
  refine hev.mono (fun β hβ => ?_)
  obtain ⟨r, hcl, hr⟩ := hβ
  refine ⟨r, hcl, ?_⟩
  have e : c * L' / L / L' = c / L := by field_simp
  rw [e]
  exact hr

#print axioms fixedWindowDecay_window_free

end Necessary

end MassGap.WeakCouplingWindow
