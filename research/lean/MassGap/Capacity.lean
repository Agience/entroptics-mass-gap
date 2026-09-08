import MassGap.Margin
import MassGap.Condensation
import MassGap.Model

/-!
# Capacity.lean — deriving `hread` for free modes, and naming the open residuals

`Margin.margin_of_contraction` (in the aggregate) assembles the read margin `hread` (`‖m_k‖ ≤ e^{-(κ₀-μ)}`)
from three inputs: `κ₀ ≤ κ` (`Floor`, PROVED from the directed-cube count) and two OPEN hypotheses —
`κ − μ ≤ c` (the junction) and `c ≤ Δ` (the contraction rate lower-bounds the transfer gap;
`ReachFreeze.gap_from_contraction` proves only that an abstract `σ` with an assumed contraction decays at rate
`c`, it does NOT supply `c ≤ Δ`, and has no call site). `Condensation.vortex_free_energy_per_step` proves —
deterministically from the count — that the per-step log-weight increment of the directed-cube LOWER-BOUND
vortex count is exactly `4(κ₀ − μ)` (an identity about that count, NOT the physical partition function's free
energy).

So the remaining physical content of the gap is TWO open deterministic inequalities:

    κ − μ ≤ c   and   c ≤ Δ

(plus identifying the abstract excess `σ` with a concrete gauge quantity satisfying the contraction). The first
is the quantitative 't Hooft / Greensite centre-vortex duality; the second ties the contraction rate to the
actual transfer gap. This module composes the pieces into `hread_of_junction`, which derives `hread` for FREE
modes `m` and a free magnitude — removing the flagship witness's definitional discharge `m := e^{-(κ₀-μ)}`, so
the object is arbitrary modes, not the answer written in. This module IS now imported by the aggregate
`MassGap.lean` (2026-07-13), so `existence_and_gap_of_junction` is machine-checked (foundation-only). The
flagship `ym_mass_gap` still uses the definitional witness; routing IT through this junction — and
discharging the two residuals — is the open step.

**To make the proof stand fully on its own:** discharge `κ₀ − μ ≤ c` and `c ≤ Δ` deterministically (the duality
between the counted condensate growth rate, `Condensation`, and a contraction rate `c` tied to the actual gap,
`ReachFreeze`), and wire the bridge into the flagship. No sampling enters; the objects are deterministic.
-/

namespace MassGap.Capacity

open MassGap

/-- **`hread` from the two open inputs, for FREE modes.** Given the dominant transfer magnitude bound
`‖m_k‖ ≤ e^{-Δ}` (`hdom`, the mode decay at gap `Δ = -log r`), the entropy floor `κ₀ ≤ κ` (`Floor`, PROVED),
and the two OPEN inputs `c ≤ Δ` (`hgap`) and `κ − μ ≤ c` (`hfe`), every active mode clears the entropy-floor
margin — the read field `hread` that `mass_gap_of_model` consumes. The modes `m` and the gap `Δ` are arbitrary;
`hgap` and `hfe` are BOTH hypotheses (`ReachFreeze.gap_from_contraction` proves only abstract-`σ` decay, it does
NOT supply `c ≤ Δ`). This displays the mode-decay assumption as an explicit hypothesis over arbitrary modes
rather than a definitional discharge — but it is not logically lighter than `hread`: at `κ = κ₀` the trio
`hdom ∧ hfe ∧ hgap` recombines to `‖m_k‖ ≤ e^{-(κ₀-μ)}` (the free `c` cancels). -/
theorem hread_of_junction {ι : Type*} (s : Finset ι) (m : ι → ℂ) {κ₀ κ μ c Δ : ℝ}
    (hdom : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-Δ))
    (hfloor : κ₀ ≤ κ) (hfe : κ - μ ≤ c) (hgap : c ≤ Δ) :
    ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ)) :=
  fun k hk => le_trans (hdom k hk) (margin_of_contraction hfloor hfe hgap)

/-- **The junction's LHS is the counted free-energy density `κ₀ − μ`.** Re-exposing `Condensation`: the vortex
log-weight increases by exactly `4(κ₀ − μ)` per length step, so the free-energy density per plaquette is
`κ₀ − μ` — from the directed-cube-path count, with no limit and no sampling. The junction `κ − μ ≤ c` (at the
floor `κ = κ₀`) thus reads: the self-sourcing contraction rate `c` is at least this deterministically-counted
free-energy density. This is the deterministic object the remaining proof must bound. -/
theorem free_energy_density_per_step (μ : ℝ) (n : ℕ) :
    Real.log (Condensation.vortexTerm μ (n + 1)) - Real.log (Condensation.vortexTerm μ n)
      = 4 * ((1 / 4) * Real.log 3 - μ) :=
  Condensation.vortex_free_energy_per_step n

/-- **The residual named as a Prop.** `SelfSourcingJunction κ μ c` is the single open input `κ − μ ≤ c`: the
self-sourcing screen contracts the entropy-rate excess at a rate at least the vortex free-energy density. -/
def SelfSourcingJunction (κ μ c : ℝ) : Prop := κ - μ ≤ c

/-- **The junction `κ₀−μ ≤ c` from count-domination + the cited scale-duality — entropy-bound half discharged
(2026-07-13).** Given (i) a physical vortex weight `Z` dominating the directed-cube count
(`vortexTerm μ n ≤ Z n`, the `Floor` injection) and (ii) the cited condensation⟹contraction duality in SCALE
form `∀ n>0, log(Z n)/(4n+2) ≤ c` (the contraction rate `c` bounds the finite-scale vortex free-energy
density), the self-sourcing junction `κ₀−μ ≤ c` holds. Proof: `Condensation.density_ratio_ge` sandwiches
`(n·log3)/(4n+2) − μ ≤ log(Z n)/(4n+2) ≤ c` for every `n>0`, and `Condensation.lower_ratio_tendsto` takes
`n→∞` to `κ₀−μ ≤ c`. So the entropy-bound half (`κ₀−μ ≤ ρ`) is PROVED from the count; `SelfSourcingJunction`
at the floor reduces to the cited scale-duality + the `Floor` count injection into the physical measure (the
`wilsonCorr` fidelity residual, shared with step 3). -/
theorem junction_of_scale_duality {μ c : ℝ} {Z : ℕ → ℝ}
    (hZ : ∀ n, Condensation.vortexTerm μ n ≤ Z n)
    (hdual : ∀ n, 0 < n → Real.log (Z n) / (4 * n + 2) ≤ c) :
    SelfSourcingJunction ((1 / 4) * Real.log 3) μ c := by
  show (1 / 4) * Real.log 3 - μ ≤ c
  refine le_of_tendsto Condensation.lower_ratio_tendsto ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact le_trans (Condensation.density_ratio_ge hZ hn) (hdual n hn)

/-- **A lattice-YM model whose read margin is DERIVED from the residuals — no definitional mode.** Given a
FREE mode family `m` (the actual DMD magnitudes, not `e^{−(κ₀−μ)}` written in) whose dominant magnitude decays
at the transfer gap `‖m_k‖ ≤ e^{−Δ}` (`hdom`), the proved entropy floor `κ₀ ≤ κ`, and the two OPEN residuals
`κ − μ ≤ c` (`hfe`, the centre-vortex free-energy junction) and `c ≤ Δ` (`hgap`, the contraction rate
lower-bounds the gap), the read field `hread` is discharged at every coupling by `hread_of_junction`. The mode
family is arbitrary, constrained only by the named residuals — the flagship's model with the definitional
witness retired. -/
noncomputable def modelOfJunction {Idx Dir : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ)
    (R : Dir → ℝ) (κ₀ κ : ℝ) (μ Δ c : ℝ → ℝ) (hfloor : κ₀ ≤ κ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ - μ β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : LatticeYM where
  Idx := Idx
  Dir := Dir
  s := s
  P := P
  m := m
  μ := μ
  R := R
  κ₀ := κ₀
  κ := κ
  hfloor := hfloor
  hread := fun β => hread_of_junction (s β) (m β) (hdom β) hfloor (hfe β) (hgap β)

/-- **The result for the actual modes, from the two named residuals — the flagship without the witness.**
`mass_gap_of_model` applied to `modelOfJunction`: for a free mode family `m` decaying at the gap (`hdom`), with
confinement (`hconf : μ < κ₀`, A1) and isotropy (`hiso`, A2), the two OPEN residuals `κ − μ ≤ c` and `c ≤ Δ`
deliver the mass gap (`C(τ) → 0`), non-triviality (`μ − κ < 0`), and `SO(4)`. The decaying mode is a
hypothesis over arbitrary `m`, not `e^{−(κ₀−μ)}` supplied definitionally. Foundational axioms only; the
residuals `hfe`, `hgap` and the decay `hdom` are explicit inputs, not discharged here. -/
theorem existence_and_gap_of_junction {Idx Dir : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ)
    (R : Dir → ℝ) (κ₀ κ : ℝ) (μ Δ c : ℝ → ℝ) (hfloor : κ₀ ≤ κ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ - μ β ≤ c β) (hgap : ∀ β, c β ≤ Δ β)
    (hconf : ∀ β, μ β < κ₀) (hiso : ∀ d d', R d = R d') :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, μ β - κ < 0) ∧
      (∀ d d', R d = R d') :=
  mass_gap_of_model (modelOfJunction s P m R κ₀ κ μ Δ c hfloor hdom hfe hgap) hconf hiso

#print axioms hread_of_junction
#print axioms existence_and_gap_of_junction

end MassGap.Capacity
