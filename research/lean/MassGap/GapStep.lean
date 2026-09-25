import Mathlib
import MassGap.ChessboardRead
import MassGap.AsymptoticScaling

/-!
# MassGap.GapStep — the renormalisation step for the transfer gap at the periodic state

The Clay input at the periodic state is `TransferGap.GapAt` at `periodicGaugeInvData τ p hN β`, or on
the lattices `ChessboardRead.TorusLagClear` (`ChessboardRead.periodic_clayGapAt_of_torusLag`). This
module states the step that carries it from a coupling `β` to a coupling `β'` at a finer spacing,
with the physical rate `−log r / aRun N β` kept, and composes it along a sequence of couplings.

## The step, and what it must say

* `physStep` : `PhysStep τ p hN β β' M` is the implication
  `GapAt D_β (e^{−M·aRun N β}) → GapAt D_{β'} (e^{−M·aRun N β'})`: the physical rate `M` at `β`
  survives at `β'`. `phys_rate_le_iff`: for spacings `a, a' > 0` and rates `r, r' > 0`,
  `−log r / a ≤ −log r' / a'` exactly when `r' ≤ r^{a'/a}`; `gapAt_mono` makes a faster rate at `β'`
  a slower one too.
* `gapAt_sqrt_iff_lag_double`: under `PositiveTransfer` and `0 ≤ r`, `GapAt D (√r)` holds exactly when every
  observable orthogonal to the vacuum has `D.form x (T^{2m} x) ≤ r^m · D.form x x`, at any one
  `m ≠ 0` (`ChessboardRead.gapAt_iff_lag` at the lag `2m`). `physStep_iff_lag`: at `0 ≤ β'` and halved spacing
  (`aRun N β' = aRun N β / 2`) the step is: a gap at rate `e^{−M a}` at `β` gives, at `β'`, the
  single-lag bound at lag `2m` with ratio `e^{−M a m}`: every observable's connected reflected pairing
  at `β'`, over the same physical separation `m·a = 2m·a'`, decays by the same factor. The algebra
  and the transfer map (the shift) are the same at every coupling; only the state changes, so the
  step compares the two states `periodicState hN β` and `periodicState hN β'` on one algebra.

## The tower

* `gapAt_tower`: a gap at rate `e^{−M a_0}` at `j = 0` and the step at every `j` give the gap at rate
  `e^{−M a_j}` at every `j`.
* `periodic_clay_tower`: at `2 ≤ N`, `0 < M`, couplings `β_j > 0`, the base gap and `PhysStep` at every
  level give `PeriodicContent.PeriodicClayGapAt` at every `β_j` with `ρ_j = e^{−M·aRun N β_j}` and
  physical rate `−log ρ_j / aRun N β_j = M`: one physical gap along the whole sequence.
* `periodic_clay_tower_of_torus`: on the lattices, `TorusLagClear` at `(β_0, m_0, r_0)` and the
  lattice step `TorusLagClear (β_j, m_j, r_j) → TorusLagClear (β_{j+1}, m_{j+1}, r_{j+1})` give
  `PeriodicClayGapAt β_j r_j` at every `j`. Separately, with `r_{j+1} = √r_j` and `a_{j+1} = a_j/2`
  the physical rate `−log r_j / a_j` is one number (`phys_rate_const`), and with `m_{j+1} = 2 m_j`
  the ratio `r_j^{m_j}` is one number (`sqrt_pow_double`).

The spacing is `aRun N β`, the two-loop running spacing of `SU(N)`, so `M` is the `SU(N)` physical
rate.

## Scope

`PhysStep`, the lattice step and the base are hypotheses. Given the base, `gapAt_tower` turns
`PhysStep` at every level into the gap at rate `M` at every level, and the gap at every level makes
every `PhysStep` true, since its conclusion holds: the step carries the whole content of the gap, one
coupling at a time. At strong coupling the base holds at `periodicState`:
`PeriodicStrongCoupling.periodic_tower_base` gives `GapAt` at `e^{−M·aRun N β_0}` at every small
`β_0 > 0` for every `M ≤ −log(coreRate 64 β_0) / aRun N β_0`.
-/

namespace MassGap.GapStep

open MassGap MassGap.GNSHilbert

/-! ## 1. On the transfer form -/

section Form

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- `GapAt` is monotone in the rate: for `0 ≤ r ≤ r'`, `GapAt D r` gives `GapAt D r'`.

DERIVED: `0` is the lower end of `r`. -/
theorem gapAt_mono (D : Transfer.TransferData A) {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r')
    (hg : TransferGap.GapAt D r) : TransferGap.GapAt D r' := by
  intro x hx
  have h := hg x hx
  have hsq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr hrr 2
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  have hm := mul_le_mul_of_nonneg_right hsq hxx
  linarith

#print axioms gapAt_mono

/-- `(√r)^{2m} = r^m` for `0 ≤ r`: halving the step and doubling the lag keep the ratio.

DERIVED: `2` is the doubling of the lag and the square of the root; `0` is the lower end of `r`. -/
theorem sqrt_pow_double {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : Real.sqrt r ^ (2 * m) = r ^ m := by
  rw [pow_mul, Real.sq_sqrt hr]

/-- **The halved spacing, as one lag.** Under `PositiveTransfer D`, `m ≠ 0` and `0 ≤ r`:
`GapAt D (√r)` holds exactly when every `x` orthogonal to the vacuum has
`D.form x (T^{2m} x) ≤ r^m · D.form x x` (`ChessboardRead.gapAt_iff_lag` at the lag `2m`,
`sqrt_pow_double`).

DERIVED: `2` is the doubling of the lag; `0` is the excluded lag, the lower end of `r` and the vacuum
pairing. -/
theorem gapAt_sqrt_iff_lag_double (D : Transfer.TransferData A) (hP : PositiveTransfer D) {m : ℕ}
    (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    TransferGap.GapAt D (Real.sqrt r) ↔
      ∀ x : A, D.form x D.vac = 0 → D.form x ((D.T ^ (2 * m)) x) ≤ r ^ m * D.form x x := by
  have hm2 : 2 * m ≠ 0 := by omega
  rw [ChessboardRead.gapAt_iff_lag D hP hm2 (Real.sqrt_nonneg r), sqrt_pow_double hr m]

#print axioms gapAt_sqrt_iff_lag_double

/-- **The tower of gaps.** For transfer data `D j` on one algebra, spacings `a j` and a physical rate
`M`: the gap at rate `e^{−M a_0}` at `j = 0` and the step
`GapAt (D j) (e^{−M a_j}) → GapAt (D (j + 1)) (e^{−M a_{j+1}})` at every `j` give the gap at rate
`e^{−M a_j}` at every `j`.

DERIVED: `0` is the base index; `1` is the step. -/
theorem gapAt_tower (D : ℕ → Transfer.TransferData A) (a : ℕ → ℝ) (M : ℝ)
    (hbase : TransferGap.GapAt (D 0) (Real.exp (-(M * a 0))))
    (hstep : ∀ j, TransferGap.GapAt (D j) (Real.exp (-(M * a j))) →
      TransferGap.GapAt (D (j + 1)) (Real.exp (-(M * a (j + 1))))) :
    ∀ j, TransferGap.GapAt (D j) (Real.exp (-(M * a j))) := by
  intro j
  induction j with
  | zero => exact hbase
  | succ j ih => exact hstep j ih

#print axioms gapAt_tower

end Form

/-! ## 2. Physical units -/

/-- **The rate condition in physical units.** For spacings `0 < a, a'` and rates `0 < r, r'`:
`−log r / a ≤ −log r' / a'` exactly when `r' ≤ r^{a'/a}`.

DERIVED: `0` is the sign of the spacings and rates. -/
theorem phys_rate_le_iff {a a' r r' : ℝ} (ha : 0 < a) (ha' : 0 < a') (hr : 0 < r) (hr' : 0 < r') :
    -Real.log r / a ≤ -Real.log r' / a' ↔ r' ≤ r ^ (a' / a) := by
  have h1 : -Real.log r / a ≤ -Real.log r' / a' ↔ -Real.log r * a' ≤ -Real.log r' * a :=
    div_le_div_iff₀ ha ha'
  have h2 : r' ≤ r ^ (a' / a) ↔ Real.log r' ≤ a' / a * Real.log r := by
    rw [← Real.log_rpow hr, Real.log_le_log_iff hr' (Real.rpow_pos_of_pos hr _)]
  have e : a' / a * Real.log r = (a' * Real.log r) / a := by ring
  rw [h1, h2, e, le_div_iff₀ ha]
  constructor <;> intro h <;> linarith

#print axioms phys_rate_le_iff

/-- Halving the spacing and taking the root of the rate keep the physical rate:
`−log √r / (a/2) = −log r / a` for `0 < r`.

DERIVED: `2` is the halving and the root's exponent `1/2`; `0` is the sign of `r`. -/
theorem phys_rate_sqrt_half {r : ℝ} (hr : 0 < r) (a : ℝ) :
    -Real.log (Real.sqrt r) / (a / 2) = -Real.log r / a := by
  rw [Real.log_sqrt hr.le]
  ring

/-- **One physical rate along the halving sequence.** With `r_{j+1} = √r_j`, `a_{j+1} = a_j / 2` and
`0 < r_0`: every `r_j` is positive and `−log r_j / a_j = −log r_0 / a_0`.

DERIVED: `0` is the base index and the sign of `r_0`; `1` is the step to the next index; `2` is the halving. -/
theorem phys_rate_const (r a : ℕ → ℝ) (hr0 : 0 < r 0) (hr : ∀ j, r (j + 1) = Real.sqrt (r j))
    (ha : ∀ j, a (j + 1) = a j / 2) :
    ∀ j, 0 < r j ∧ -Real.log (r j) / a j = -Real.log (r 0) / a 0 := by
  intro j
  induction j with
  | zero => exact ⟨hr0, rfl⟩
  | succ j ih =>
    obtain ⟨hpos, heq⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [hr j]
      exact Real.sqrt_pos.mpr hpos
    · rw [hr j, ha j, phys_rate_sqrt_half hpos, heq]

#print axioms phys_rate_const

/-! ## 3. At the periodic state -/

section Wilson

variable {N : ℕ}

/-- **The renormalisation input `H(β, β')` at physical rate `M`.** At the periodic state: the transfer
gap at rate `e^{−M·aRun N β}` at coupling `β` gives the transfer gap at rate `e^{−M·aRun N β'}` at
`β'`. By `phys_rate_le_iff` its conclusion is the physical rate `M` at `β'`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
def PhysStep (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β β' M : ℝ) : Prop :=
  TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
      (Real.exp (-(M * AsymptoticScaling.aRun N β))) →
    TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β')
      (Real.exp (-(M * AsymptoticScaling.aRun N β')))

/-- **The step at halved spacing, as one lag at `β'`.** At `0 ≤ β'` with
`aRun N β' = aRun N β / 2` and any lag `m ≠ 0`: `PhysStep τ p hN β β' M` holds exactly when the gap at
rate `e^{−M a}` at `β` (`a = aRun N β`) gives, at `β'`, every observable `x` orthogonal to the vacuum
the bound `D'.form x (T^{2m} x) ≤ (e^{−M a})^m · D'.form x x`: the same decay over the same physical
separation `m·a = 2m·(a/2)` (`gapAt_sqrt_iff_lag_double`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β'`, the excluded
lag and the vacuum pairing; `2` is the halving and the doubled lag. -/
theorem physStep_iff_lag (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' M : ℝ} (hβ' : 0 ≤ β')
    (hhalf : AsymptoticScaling.aRun N β' = AsymptoticScaling.aRun N β / 2) {m : ℕ} (hm : m ≠ 0) :
    PhysStep τ p hN β β' M ↔
      (TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
          (Real.exp (-(M * AsymptoticScaling.aRun N β))) →
        ∀ x, (PeriodicState.periodicGaugeInvData τ p hN β').form x
              (PeriodicState.periodicGaugeInvData τ p hN β').vac = 0 →
          (PeriodicState.periodicGaugeInvData τ p hN β').form x
              (((PeriodicState.periodicGaugeInvData τ p hN β').T ^ (2 * m)) x)
            ≤ Real.exp (-(M * AsymptoticScaling.aRun N β)) ^ m
              * (PeriodicState.periodicGaugeInvData τ p hN β').form x x) := by
  have hsq : Real.exp (-(M * AsymptoticScaling.aRun N β'))
      = Real.sqrt (Real.exp (-(M * AsymptoticScaling.aRun N β))) := by
    rw [hhalf]
    have he : Real.exp (-(M * AsymptoticScaling.aRun N β))
        = Real.exp (-(M * (AsymptoticScaling.aRun N β / 2))) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  unfold PhysStep
  rw [hsq, gapAt_sqrt_iff_lag_double _ (PeriodicState.periodic_positiveTransfer τ p hN hβ') hm
    (Real.exp_pos (-(M * AsymptoticScaling.aRun N β))).le]

#print axioms physStep_iff_lag

/-- **The Clay statement at the periodic state from a gap at rate `r`.** At `2 ≤ N`, `0 ≤ β`,
`0 < r < 1` and `GapAt` at `periodicGaugeInvData τ p hN β` at `r`: `PeriodicClayGapAt τ p hN β r`
(the proof of `ChessboardRead.periodic_clayGapAt_of_torusLag` from its `GapAt` step on).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance of the
real trace; `0` is the excluded rank and the lower end of `β` and `r`; `1` is the upper end of `r`. -/
theorem periodic_clayGapAt_of_gapAt (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hg : TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β) r) :
    PeriodicContent.PeriodicClayGapAt τ p hN β r := by
  have hP := PeriodicState.periodic_positiveTransfer τ p hN hβ
  obtain ⟨hsa, _, hspec, hgreat⟩ := ClayCapstone.clay_gap_of_gapAt
    (PeriodicState.periodicGaugeInvData τ p hN β) hr0 hr1 hP hg
  exact ⟨hr0, hr1, hsa, hspec, hgreat,
    (GNSCompare.gapAt_iff_opT_contracts (PeriodicState.periodicGaugeInvData τ p hN β) hr0.le).mp hg,
    PeriodicContent.periodic_exists_ne_zero_orth_vacuum τ p hN2 hN hβ⟩

#print axioms periodic_clayGapAt_of_gapAt

/-- **One physical gap along a sequence of couplings.** At `2 ≤ N`, `0 < M` and couplings `β_j > 0`:
the gap at rate `e^{−M·aRun N β_0}` at `β_0` and `PhysStep` from each `β_j` to `β_{j+1}` give, at
every `j`, `PeriodicClayGapAt τ p hN β_j ρ_j` with `ρ_j = e^{−M·aRun N β_j}` and physical rate
`−log ρ_j / aRun N β_j = M` (`gapAt_tower`, `periodic_clayGapAt_of_gapAt`,
`AsymptoticScaling.aRun_pos`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank, the base index and the sign of `M` and of each `β_j`; `1` is the step to the next index. -/
theorem periodic_clay_tower (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) (β : ℕ → ℝ)
    (hβ : ∀ j, 0 < β j) (M : ℝ) (hM : 0 < M)
    (hbase : TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN (β 0))
      (Real.exp (-(M * AsymptoticScaling.aRun N (β 0)))))
    (hstep : ∀ j, PhysStep τ p hN (β j) (β (j + 1)) M) :
    ∀ j, PeriodicContent.PeriodicClayGapAt τ p hN (β j)
          (Real.exp (-(M * AsymptoticScaling.aRun N (β j))))
      ∧ -Real.log (Real.exp (-(M * AsymptoticScaling.aRun N (β j))))
          / AsymptoticScaling.aRun N (β j) = M := by
  have hgaps := gapAt_tower (fun j => PeriodicState.periodicGaugeInvData τ p hN (β j))
    (fun j => AsymptoticScaling.aRun N (β j)) M hbase hstep
  intro j
  have ha : 0 < AsymptoticScaling.aRun N (β j) := AsymptoticScaling.aRun_pos (by omega) (hβ j)
  have hr0 : 0 < Real.exp (-(M * AsymptoticScaling.aRun N (β j))) := Real.exp_pos _
  have hr1 : Real.exp (-(M * AsymptoticScaling.aRun N (β j))) < 1 := by
    have h := Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hM ha))
    rwa [Real.exp_zero] at h
  refine ⟨periodic_clayGapAt_of_gapAt τ p hN2 hN (hβ j).le hr0 hr1 (hgaps j), ?_⟩
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self ha.ne', mul_one]

#print axioms periodic_clay_tower

/-- **The lattice tower.** At `2 ≤ N`, couplings `β_j ≥ 0`, lags `m_j ≠ 0` and rates `0 < r_j < 1`:
`ChessboardRead.TorusLagClear` at `(β_0, m_0, r_0)` and the lattice step
`TorusLagClear (β_j, m_j, r_j) → TorusLagClear (β_{j+1}, m_{j+1}, r_{j+1})` at every `j` give
`PeriodicClayGapAt τ p hN β_j r_j` at every `j` (`ChessboardRead.periodic_clayGapAt_of_torusLag`).
Separately, along `m_{j+1} = 2 m_j`, `r_{j+1} = √r_j` and `aRun N β_{j+1} = aRun N β_j / 2`, the ratio
`r_j^{m_j}` (`sqrt_pow_double`) and `−log r_j / aRun N β_j` (`phys_rate_const`) are constant; this
theorem takes arbitrary `r_j` and `m_j`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank, the base index, the excluded lag and the lower end of `β_j` and `r_j`; `1` is the
upper end of `r_j` and the step `j + 1`. -/
theorem periodic_clay_tower_of_torus (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j) (m : ℕ → ℕ) (hm : ∀ j, m j ≠ 0) (r : ℕ → ℝ)
    (hr0 : ∀ j, 0 < r j) (hr1 : ∀ j, r j < 1)
    (hbase : ChessboardRead.TorusLagClear τ p hN (β 0) (m 0) (r 0))
    (hstep : ∀ j, ChessboardRead.TorusLagClear τ p hN (β j) (m j) (r j) →
      ChessboardRead.TorusLagClear τ p hN (β (j + 1)) (m (j + 1)) (r (j + 1))) :
    ∀ j, PeriodicContent.PeriodicClayGapAt τ p hN (β j) (r j) := by
  have hlag : ∀ j, ChessboardRead.TorusLagClear τ p hN (β j) (m j) (r j) := by
    intro j
    induction j with
    | zero => exact hbase
    | succ j ih => exact hstep j ih
  intro j
  exact ChessboardRead.periodic_clayGapAt_of_torusLag τ p hN2 hN (hβ j) (hm j) (hr0 j) (hr1 j)
    (hlag j)

#print axioms periodic_clay_tower_of_torus

end Wilson

end MassGap.GapStep
