import Mathlib
import MassGap.ObserverFlow
import MassGap.FlowCapstone

/-!
# MassGap.ObserverClay — the continuum statement for the smeared `SU(2)` observer

The observer of `ObserverFlow.obsConfFlow` (localised APE smearing, `0 ≤ c < 1/6`, `n k` steps in
midpoint boxes of half-width `R k`) is a bounded flow (`ContinuumFlow.Flow.ofConf_bounded`), and when its
range shrinks to a fixed physical size `r` (`dySpacing 2 k · (R k + 3) ≤ r` eventually) it keeps the
positive half-space beyond `r` (`ContinuumFlow.Flow.posPreserving_of_physRange`). So
`FlowCapstone.flow_clay_of_abs_cluster` applies to it: its continuum theory has, at every dyadic step,
a gapped transfer on a space with a non-zero vector orthogonal to the vacuum, given the observer's
clustering and one non-zero connected pairing of its view.
-/

namespace MassGap.ObserverClay

open MassGap.ObserverFlow MassGap.FlowCapstone MassGap.ContinuumFlow MassGap.ContinuumSchwinger
  Filter

/-- `2 ≠ 0`, named once so every occurrence is the same proof term.

DERIVED: `2` is the rank. -/
theorem two_ne : (2 : ℕ) ≠ 0 := by norm_num

/-- The observer's flow.

DERIVED: `2` is the rank; `1/6` the dominance bound. -/
noncomputable abbrev obsFlowF (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) : Flow 2 :=
  Flow.ofConf (obsConfFlow c hc0 hc n R)

/-- The observer's range at step `k` is `R k + 3`; a physical bound on it is `Flow.PhysRange`.

DERIVED: `3` the range beyond the box; `1/6` the dominance bound. -/
theorem physRange_of {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) {r : ℝ}
    (h : ∀ᶠ k in atTop, dySpacing 2 k * ((R k + 3 : ℕ) : ℝ) ≤ r) :
    (obsFlowF c hc0 hc n R).PhysRange r := h

#print axioms physRange_of

/-- **The smeared observer's continuum statement.** For the localised APE observer whose range has a
physical bound `r`, the observer's absolute clustering at a window `L > 0` and one non-zero connected
pairing of its view give, at every dyadic step, the flowed transfer gapped at physical rate `c'/L` on a
space with a non-zero vector orthogonal to the vacuum.

DERIVED: `2` is the rank; `0` the lower end of `L` and `c'`; `1/6` the dominance bound. -/
theorem observer_clay {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) (τ : Fin 4) {r : ℝ}
    (hphys : (obsFlowF c hc0 hc n R).PhysRange r) {L : ℝ} (hL : 0 < L)
    (hcl : FlowClusterAbs two_ne (obsFlowF c hc0 hc n R) τ r L)
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
  flow_clay_of_bounded_abs_cluster two_ne (obsFlowF c hc0 hc n R) (Flow.ofConf_bounded _) τ
    (Flow.posPreserving_of_physRange two_ne _ hphys τ) hL hcl hNT

#print axioms observer_clay

end MassGap.ObserverClay
