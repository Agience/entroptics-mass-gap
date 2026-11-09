import Mathlib
import MassGap.ObserverClay

/-!
# MassGap.ObserverGapScale — the observer's clustering is a statement at one time step

`FlowCapstone.FlowClusterAbs` asks, at every dyadic step `m`, for decay of the observer's connected
flowed kernel along the time grid of spacing `aₘ = dySpacing N m`, at one physical rate `c/L`. The
kernel `kernF` does not depend on `m`; only the grid does, and the grids are nested (`aₘ = 2^(m'−m) aₘ'`).
This module proves that the whole family is one statement at one grid:

* `flowClusterAbs_of_at`: decay along the grid of any single step `m₀` (`FlowClusterAt … m₀`) gives
  `FlowClusterAbs`. A time `aₘ n` is `aₘ₀ q + s · a_{m₀+m}` with `0 ≤ s < 2^m`; the remainder shifts
  the second monomial forward (still a margin monomial), and the finitely many remainders contribute
  one constant. `flowClusterAbs_iff_at` is the equivalence.
* `flowClusterAt_of_gapAt`: the gap of the observer's transfer at the single step `m₀`, any rate
  `0 < ρ < 1`, gives `FlowClusterAt … m₀` (`TransferGap.clustering_sq` on two basis vectors).
* `flowClusterAbs_iff_gapAt`: for a bounded flow keeping the half-space beyond its margin, `FlowClusterAbs`
  holds if and only if the observer's transfer at one step `m₀` is `GapAt` some `ρ < 1`.
* `observer_M_iff_gap`, `observer_clay_of_gap`: the same for the smeared `SU(2)` observer
  `ObserverClay.obsFlowF`; its continuum statement follows from that one gap and `FlowConnectedNonzero`.

So M for the observer is one inequality on one transfer: at the time step `a₀`, every vector of the
observer's reconstructed space orthogonal to the vacuum contracts by a fixed factor `ρ < 1`.
-/

namespace MassGap.ObserverGapScale

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumReconstruction
  MassGap.ContinuumCluster MassGap.ContinuumFlow MassGap.FlowCapstone Filter

variable {N : ℕ}

/-- Translating the empty monomial leaves it unchanged.

DERIVED: `0` is the number of factors; `4` in `Fin 4 → ℝ` is the spacetime dimension. -/
theorem mono_shift_empty (v : Fin 4 → ℝ) : Mono.shift v (emptyMono N) = emptyMono N :=
  congrArg (Sigma.mk 0) (funext fun i => i.elim0)

#print axioms mono_shift_empty

/-- **The one-point function is translation invariant along the time grid**:
`S(θ∅ ∪ shift (aₘ s) Q) = S(θ∅ ∪ Q)`.

DERIVED: `0` is the base of the induction and the excluded colour count; `1` the unit step; `4` in
`Fin 4` is the spacetime dimension. -/
theorem kernF_vac_shift (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (m s : ℕ) (Q : Mono N) :
    kernF hN Φ τ (emptyMono N) (Mono.shift (timeVec N m τ s) Q)
      = kernF hN Φ τ (emptyMono N) Q := by
  induction s with
  | zero => rw [Nat.cast_zero, timeVec_zero, Mono.shift_zero]
  | succ s ih =>
    have h : Mono.shift (timeVec N m τ ((s + 1 : ℕ) : ℤ)) Q
        = Mono.shift (timeVec N m τ 1) (Mono.shift (timeVec N m τ s) Q) := by
      rw [Mono.shift_shift, timeVec_add, Nat.cast_succ]
    rw [h, ← kernF_shift, mono_shift_empty, ih]

#print axioms kernF_vac_shift

/-- **The observer's clustering along the grid of one step `m₀`**: some `c > 0` such that every pair
of margin monomials has a constant `C` with the connected flowed kernel at time `aₘ₀ n` at most
`C e^{−(c/L) aₘ₀ n}`. `FlowClusterAbs` is this at every step at once.

DERIVED: `0` the lower end of `c`; `4` in `Fin 4` is the spacetime dimension. -/
def FlowClusterAt (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r L : ℝ) (m0 : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P Q : MarginMono N τ r, ∃ C : ℝ, ∀ n : ℕ,
    |kernF hN Φ τ P.1 (Mono.shift (timeVec N m0 τ n) Q.1)
        - kernF hN Φ τ P.1 (emptyMono N) * kernF hN Φ τ (emptyMono N) Q.1|
      ≤ C * Real.exp (-(c / L) * (dySpacing N m0 * n))

/-- `FlowClusterAbs` contains the statement at each single step.

DERIVED: no numeral. -/
theorem flowClusterAt_of_abs (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) {r L : ℝ} (m0 : ℕ)
    (h : FlowClusterAbs hN Φ τ r L) : FlowClusterAt hN Φ τ r L m0 := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun P Q => h m0 P Q⟩

#print axioms flowClusterAt_of_abs

/-- **Decay along one grid gives decay along every grid.** From `FlowClusterAt … m₀`, at step `m` a
time `aₘ n` is written `aₘ₀ q + a_{m₀+m} s` with `s < 2^m`; the remainder shifts `Q` forward by
`a_{m₀+m} s` (a margin monomial again, with the same one-point function, `kernF_vac_shift`), and the
constant is the sum over the `2^m` remainders of `|C_s| e^{|c/L| aₘ₀}`.

DERIVED: `2` is the dyadic ratio of the grids; `0` the lower end of the remainder; `4` in `Fin 4` is
the spacetime dimension. -/
theorem flowClusterAbs_of_at (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) {r L : ℝ} (m0 : ℕ)
    (h : FlowClusterAt hN Φ τ r L m0) : FlowClusterAbs hN Φ τ r L := by
  classical
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun m P Q => ?_⟩
  let Qs : ℕ → MarginMono N τ r := fun s =>
    ⟨Mono.shift (timeVec N (m0 + m) τ s) Q.1, by
      obtain ⟨d, hd, hrd, hP⟩ := Q.2
      exact ⟨d, hd, hrd, posAt_shift hP (ContinuumSep.timeVec_nonneg hN (m0 + m) τ s)⟩⟩
  let Cf : ℕ → ℝ := fun s => Classical.choose (h P (Qs s))
  have hCf : ∀ s q : ℕ, |kernF hN Φ τ P.1 (Mono.shift (timeVec N m0 τ q) (Qs s).1)
        - kernF hN Φ τ P.1 (emptyMono N) * kernF hN Φ τ (emptyMono N) (Qs s).1|
      ≤ Cf s * Real.exp (-(c / L) * (dySpacing N m0 * q)) :=
    fun s => Classical.choose_spec (h P (Qs s))
  have haM : 0 < dySpacing N (m0 + m) := dySpacing_pos (one_le_of_ne_zero hN) (m0 + m)
  have hm : dySpacing N (m0 + m) * 2 ^ m0 = dySpacing N m := by
    have := dySpacing_mul_pow N (show m ≤ m0 + m by omega)
    rwa [show m0 + m - m = m0 by omega] at this
  have hm0 : dySpacing N (m0 + m) * 2 ^ m = dySpacing N m0 := by
    have := dySpacing_mul_pow N (show m0 ≤ m0 + m by omega)
    rwa [show m0 + m - m0 = m by omega] at this
  refine ⟨∑ s ∈ Finset.range (2 ^ m), |Cf s| * Real.exp (|c / L| * dySpacing N m0), fun n => ?_⟩
  obtain ⟨q, s, hpqs, hslt⟩ : ∃ q s : ℕ, 2 ^ m * q + s = 2 ^ m0 * n ∧ s < 2 ^ m :=
    ⟨(2 ^ m0 * n) / 2 ^ m, (2 ^ m0 * n) % 2 ^ m, Nat.div_add_mod _ _,
      Nat.mod_lt _ (by positivity)⟩
  have hpqsR : (2 : ℝ) ^ m * q + s = 2 ^ m0 * n := by exact_mod_cast hpqs
  have hreal : dySpacing N m * n = dySpacing N m0 * q + dySpacing N (m0 + m) * s := by
    rw [← hm, ← hm0]
    linear_combination (-(dySpacing N (m0 + m))) * hpqsR
  have hvec : timeVec N m τ (n : ℤ)
      = timeVec N (m0 + m) τ (s : ℤ) + timeVec N m0 τ (q : ℤ) := by
    funext i
    simp only [timeVec, site, axisVec, Pi.add_apply]
    split_ifs
    · push_cast
      linarith [hreal]
    · simp
  have hshift : Mono.shift (timeVec N m τ n) Q.1
      = Mono.shift (timeVec N m0 τ q) (Qs s).1 := by
    show _ = Mono.shift (timeVec N m0 τ q) (Mono.shift (timeVec N (m0 + m) τ s) Q.1)
    rw [Mono.shift_shift, hvec]
  have hvac : kernF hN Φ τ (emptyMono N) (Qs s).1 = kernF hN Φ τ (emptyMono N) Q.1 :=
    kernF_vac_shift hN Φ τ (m0 + m) s Q.1
  rw [hshift, ← hvac]
  refine (hCf s q).trans ?_
  have h1 : 0 ≤ dySpacing N (m0 + m) * s := by positivity
  have h2 : dySpacing N (m0 + m) * s ≤ dySpacing N m0 := by
    rw [← hm0]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hslt.le) haM.le
  have h3 : c / L * (dySpacing N (m0 + m) * s) ≤ |c / L| * dySpacing N m0 :=
    calc c / L * (dySpacing N (m0 + m) * s) ≤ |c / L| * (dySpacing N (m0 + m) * s) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h1
      _ ≤ |c / L| * dySpacing N m0 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hexp : Real.exp (-(c / L) * (dySpacing N m0 * q))
      ≤ Real.exp (|c / L| * dySpacing N m0) * Real.exp (-(c / L) * (dySpacing N m * n)) := by
    rw [← Real.exp_add, hreal]
    apply Real.exp_le_exp.mpr
    nlinarith [h3]
  have hterm : |Cf s| * Real.exp (|c / L| * dySpacing N m0)
      ≤ ∑ s' ∈ Finset.range (2 ^ m), |Cf s'| * Real.exp (|c / L| * dySpacing N m0) :=
    Finset.single_le_sum (f := fun s' => |Cf s'| * Real.exp (|c / L| * dySpacing N m0))
      (fun s' _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (Finset.mem_range.mpr hslt)
  calc Cf s * Real.exp (-(c / L) * (dySpacing N m0 * q))
      ≤ |Cf s| * Real.exp (-(c / L) * (dySpacing N m0 * q)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |Cf s| * (Real.exp (|c / L| * dySpacing N m0)
          * Real.exp (-(c / L) * (dySpacing N m * n))) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = (|Cf s| * Real.exp (|c / L| * dySpacing N m0))
          * Real.exp (-(c / L) * (dySpacing N m * n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le

#print axioms flowClusterAbs_of_at

/-- **`FlowClusterAbs` is a statement at one step**, any step `m₀`.

DERIVED: no numeral. -/
theorem flowClusterAbs_iff_at (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) {r L : ℝ} (m0 : ℕ) :
    FlowClusterAbs hN Φ τ r L ↔ FlowClusterAt hN Φ τ r L m0 :=
  ⟨flowClusterAt_of_abs hN Φ τ m0, flowClusterAbs_of_at hN Φ τ m0⟩

#print axioms flowClusterAbs_iff_at

/-- **The gap at one step gives clustering along that step's grid.** `GapAt` of the observer's
transfer at step `m₀` with `0 < ρ < 1` gives `FlowClusterAt … m₀` at `c = L (−log ρ)/aₘ₀`, with the
constant `√(S(θP ∪ P) · ‖Q − S(Q)Ω‖²)` (`TransferGap.clustering_sq` on the basis vectors of `P`, `Q`).

DERIVED: `0` and `1` bracket the rate; `2` is the square; `4` in `Fin 4` is the spacetime dimension. -/
theorem flowClusterAt_of_gapAt (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m0 : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (flowTransfer hN Φ hB τ hpos m0) ρ) {L : ℝ} (hL : 0 < L) :
    FlowClusterAt hN Φ τ r L m0 := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) m0
  have hlog : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ0 hρ1)
  refine ⟨L * (-Real.log ρ) / dySpacing N m0, by positivity, fun P Q => ?_⟩
  set D := flowTransfer hN Φ hB τ hpos m0 with hD
  refine ⟨Real.sqrt (kernF hN Φ τ P.1 P.1
    * D.form (TransferGap.vacProj D (Finsupp.single Q 1))
        (TransferGap.vacProj D (Finsupp.single Q 1))), fun n => ?_⟩
  have hexpo : -(L * (-Real.log ρ) / dySpacing N m0 / L) * (dySpacing N m0 * n)
      = n * Real.log ρ := by
    field_simp
  have hexp : Real.exp (-(L * (-Real.log ρ) / dySpacing N m0 / L) * (dySpacing N m0 * n))
      = ρ ^ n := by
    rw [hexpo, Real.exp_nat_mul, Real.exp_log hρ0]
  rw [hexp]
  have hcs := TransferGap.clustering_sq D hρ0.le hg n (Finsupp.single Q 1) (Finsupp.single P 1)
  have e1 : D.form (Finsupp.single P 1) ((D.T ^ n) (Finsupp.single Q 1))
      = kernF hN Φ τ P.1 (Mono.shift (timeVec N m0 τ n) Q.1) := by
    rw [Module.End.pow_apply]
    show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (Finsupp.single P 1)
      ((⇑(gT (MarginMono.shift hN τ m0)))^[n] (Finsupp.single Q 1)) = _
    rw [gT_iterate, Finsupp.mapDomain_single, gForm_single, one_mul, one_mul,
      MarginMono.shift_iterate]
  have e2 : D.form (Finsupp.single P 1) D.vac = kernF hN Φ τ P.1 (emptyMono N) := by
    show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (Finsupp.single P 1)
      (Finsupp.single (emptyMargin N τ r) 1) = _
    rw [gForm_single, one_mul, one_mul]
    rfl
  have e3 : D.form D.vac (Finsupp.single Q 1) = kernF hN Φ τ (emptyMono N) Q.1 := by
    show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
      (Finsupp.single (emptyMargin N τ r) 1) (Finsupp.single Q 1) = _
    rw [gForm_single, one_mul, one_mul]
    rfl
  have e4 : D.form (Finsupp.single P 1) (Finsupp.single P 1) = kernF hN Φ τ P.1 P.1 := by
    show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (Finsupp.single P 1)
      (Finsupp.single P 1) = _
    rw [gForm_single, one_mul, one_mul]
  rw [e1, e2, e3, e4, show ρ ^ (2 * n) = (ρ ^ n) ^ 2 by rw [← pow_mul, mul_comm]] at hcs
  have hfin := ContinuumSep.abs_le_mul_sqrt_of_sq_le_sep (pow_nonneg hρ0.le n) hcs
  linarith [hfin, mul_comm (ρ ^ n) (Real.sqrt (kernF hN Φ τ P.1 P.1
    * D.form (TransferGap.vacProj D (Finsupp.single Q 1))
        (TransferGap.vacProj D (Finsupp.single Q 1))))]

#print axioms flowClusterAt_of_gapAt

/-- **M for a flow is one gap at one step.** For a flow with the uniform bound keeping the positive
half-space beyond its margin, at a window `L > 0` and any step `m₀`: `FlowClusterAbs` holds if and
only if the flowed transfer at step `m₀` is `GapAt` some `ρ` with `0 < ρ < 1`.

DERIVED: `0` and `1` bracket the rate and `0` is the lower end of `L`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem flowClusterAbs_iff_gapAt (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) :
    FlowClusterAbs hN Φ τ r L
      ↔ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (flowTransfer hN Φ hB τ hpos m0) ρ := by
  constructor
  · intro h
    obtain ⟨c, hc, hg⟩ := flow_gap_of_abs_cluster hN Φ hB τ hpos h
    refine ⟨Real.exp (-(c / L) * dySpacing N m0), Real.exp_pos _, ?_, hg m0⟩
    rw [Real.exp_lt_one_iff, neg_mul]
    exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (dySpacing_pos (one_le_of_ne_zero hN) m0))
  · rintro ⟨ρ, hρ0, hρ1, hg⟩
    exact flowClusterAbs_of_at hN Φ τ m0 (flowClusterAt_of_gapAt hN Φ hB τ hpos m0 hρ0 hρ1 hg hL)

#print axioms flowClusterAbs_iff_gapAt

open MassGap.ObserverFlow MassGap.ObserverClay

/-- **M for the smeared `SU(2)` observer is one gap at one step.** For the localised APE observer with
a physical bound on its range, at any step `m₀`: its clustering `FlowClusterAbs` holds if and only if
its reconstructed transfer at step `m₀` contracts the vacuum's complement by some `ρ < 1`.

DERIVED: `2` is the rank; `0` and `1` bracket the rate and `0` is the lower end of `L`; `1/6` the
dominance bound. -/
theorem observer_M_iff_gap {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) (τ : Fin 4)
    {r : ℝ} (hphys : (obsFlowF c hc0 hc n R).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) :
    FlowClusterAbs two_ne (obsFlowF c hc0 hc n R) τ r L
      ↔ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt
          (flowTransfer two_ne (obsFlowF c hc0 hc n R)
            (uniformBoundF_of_bounded two_ne _ (Flow.ofConf_bounded _)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m0) ρ :=
  flowClusterAbs_iff_gapAt two_ne _ _ τ _ m0 hL

#print axioms observer_M_iff_gap

/-- **The smeared observer's continuum statement from one gap at one step.** The transfer at step
`m₀` contracting the vacuum's complement by some `ρ < 1`, with `FlowConnectedNonzero`, gives at every
dyadic step the gap at physical rate `c'/L` on a space with a non-zero vector orthogonal to the
vacuum.

DERIVED: `2` is the rank; `0` and `1` bracket the rate and `0` is the lower end of `L` and `c'`;
`1/6` the dominance bound. -/
theorem observer_clay_of_gap {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) (τ : Fin 4)
    {r : ℝ} (hphys : (obsFlowF c hc0 hc n R).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt
      (flowTransfer two_ne (obsFlowF c hc0 hc n R)
        (uniformBoundF_of_bounded two_ne _ (Flow.ofConf_bounded _)) τ
        (Flow.posPreserving_of_physRange two_ne _ hphys τ) m0) ρ)
    (hNT : FlowConnectedNonzero two_ne (obsFlowF c hc0 hc n R) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsFlowF c hc0 hc n R)
            (uniformBoundF_of_bounded two_ne _ (Flow.ofConf_bounded _)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsFlowF c hc0 hc n R)
            (uniformBoundF_of_bounded two_ne _ (Flow.ofConf_bounded _)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  observer_clay hc0 hc n R τ hphys hL
    ((observer_M_iff_gap hc0 hc n R τ hphys m0 hL).mpr ⟨ρ, hρ0, hρ1, hg⟩) hNT

#print axioms observer_clay_of_gap

/-- The smeared observer's reconstructed transfer at step `m₀`.

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
noncomputable abbrev obsTransfer {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) (τ : Fin 4)
    {r : ℝ} (hphys : (obsFlowF c hc0 hc n R).PhysRange r) (m0 : ℕ) :
    Transfer.TransferData (MarginMono 2 τ r →₀ ℝ) :=
  flowTransfer two_ne (obsFlowF c hc0 hc n R)
    (uniformBoundF_of_bounded two_ne _ (Flow.ofConf_bounded _)) τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) m0

end MassGap.ObserverGapScale
