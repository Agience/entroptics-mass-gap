import MassGap.Margin
import MassGap.Condensation
import MassGap.Model

/-!
# MassGap.Capacity — the read margin `hread` from three named inequalities

`LatticeYM` carries a field `hread`, the statement that every active mode's magnitude is at most
`e^{-(κ₀ - μ)}`. This module builds that field from separately stated inequalities instead of from a
mode family chosen to satisfy it, and assembles a `LatticeYM` and a result around the construction.

The chain. `hread_of_junction` chains `hdom : ‖m k‖ ≤ e^{-Δ}` with `Margin.margin_of_contraction`,
which turns `κ₀ ≤ κ`, `κ - μ ≤ c` and `c ≤ Δ` into `e^{-Δ} ≤ e^{-(κ₀ - μ)}`. So the mode family `m`
and the rate `Δ` are universally quantified; nothing is discharged by defining `m` to be the answer.

`free_energy_density_per_step` re-exports `Condensation.vortex_free_energy_per_step`: the log-weight
of the directed-cube vortex count increases by exactly `4·((1/4)·log 3 - μ)` per length step. That is an
identity about the counted lower bound, not about a partition function.

`SelfSourcingJunction κ μ c` names the inequality `κ - μ ≤ c` as a `Prop`.
`junction_of_scale_duality` discharges it at `κ = (1/4)·log 3` from two hypotheses: `hZ`, that a weight
`Z` dominates `Condensation.vortexTerm` pointwise, and `hdual`, that `log (Z n) / (4n + 2) ≤ c` at
every positive `n`. The proof sandwiches the ratio with `Condensation.density_ratio_ge` and passes to
the limit with `Condensation.lower_ratio_tendsto`.

`modelOfJunction` packages the inputs into a `LatticeYM`, and `existence_and_gap_of_junction` applies
`mass_gap_of_model` to it.

Scope: `hfe` and `hgap` are hypotheses everywhere below, never conclusions. The conclusion delivered by
`existence_and_gap_of_junction` is `C(τ) → 0` together with `μ β - κ < 0` and equality of the `R`
values, which is what `mass_gap_of_model` gives; it is not a spectral statement. The objects are
deterministic throughout — no measure or sample enters any statement in this file.
-/

namespace MassGap.Capacity

open MassGap

/-- Every mode of `m` indexed by the finite set `s` satisfies `‖m k‖ ≤ exp (-(κ₀ - μ))`, given
`hdom : ‖m k‖ ≤ exp (-Δ)` on `s`, `hfloor : κ₀ ≤ κ`, `hfe : κ - μ ≤ c` and `hgap : c ≤ Δ`.

This is the `hread` field of `LatticeYM` in hypothesis form. The mode family `m : ι → ℂ`, the index
type `ι`, and the five reals `κ₀`, `κ`, `μ`, `c`, `Δ` are all arbitrary; the three inequalities compose
through `Margin.margin_of_contraction` to `exp (-Δ) ≤ exp (-(κ₀ - μ))`, and `hdom` is chained onto it.

Scope: the three inequalities are equivalent in strength to the conclusion when `κ = κ₀`, since `c` then
cancels between `hfe` and `hgap`. What the statement changes is the quantification — `m` and `Δ` are
bound universally rather than instantiated at the value that makes the conclusion hold. -/
theorem hread_of_junction {ι : Type*} (s : Finset ι) (m : ι → ℂ) {κ₀ κ μ c Δ : ℝ}
    (hdom : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-Δ))
    (hfloor : κ₀ ≤ κ) (hfe : κ - μ ≤ c) (hgap : c ≤ Δ) :
    ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ)) :=
  fun k hk => le_trans (hdom k hk) (margin_of_contraction hfloor hfe hgap)

/-- The log of `Condensation.vortexTerm μ` increases by exactly `4 * ((1 / 4) * Real.log 3 - μ)` when the
length argument goes from `n` to `n + 1`, for every real `μ` and every natural `n`.

A re-export of `Condensation.vortex_free_energy_per_step`. It is an equality, at every `n`, with no
limit taken: the increment is the same at every step, so the per-plaquette density is
`(1 / 4) * Real.log 3 - μ`.

Scope: the statement is about `vortexTerm`, the directed-cube path count, not about a partition
function. `μ` is unconstrained in sign, and no positivity of `vortexTerm` is asserted here — the
logarithm is Mathlib's, total on `ℝ`.

DERIVED: `1 / 4` and `3` are the entropy floor `κ₀ = (1 / 4) * Real.log 3`, fixed by the directed-cube
count. The outer `4` is the number of plaquettes a single length step contributes, which is what turns
the per-step increment into the per-plaquette density. The `1` in `n + 1` is that single step. -/
theorem free_energy_density_per_step (μ : ℝ) (n : ℕ) :
    Real.log (Condensation.vortexTerm μ (n + 1)) - Real.log (Condensation.vortexTerm μ n)
      = 4 * ((1 / 4) * Real.log 3 - μ) :=
  Condensation.vortex_free_energy_per_step n

/-- `SelfSourcingJunction κ μ c` unfolds to `κ - μ ≤ c`: the rate `c` is at least the excess of `κ` over
`μ`. A named `Prop` over three reals, with no positivity assumed of any of them. -/
def SelfSourcingJunction (κ μ c : ℝ) : Prop := κ - μ ≤ c

/-- `SelfSourcingJunction ((1 / 4) * Real.log 3) μ c`, that is `(1 / 4) * Real.log 3 - μ ≤ c`, from two
hypotheses: `hZ`, that `Condensation.vortexTerm μ n ≤ Z n` at every natural `n`, and `hdual`, that
`Real.log (Z n) / (4 * n + 2) ≤ c` at every positive `n`.

The proof sandwiches the scale ratio — `Condensation.density_ratio_ge` gives
`(n·log 3)/(4n + 2) - μ ≤ log (Z n)/(4n + 2)` from `hZ` at each positive `n`, `hdual` caps the right
side by `c`, and `Condensation.lower_ratio_tendsto` passes the left side to its limit.

Scope: the junction is obtained only at `κ = (1 / 4) * Real.log 3`, not at general `κ`. `Z` is an
arbitrary sequence of reals — no positivity, monotonicity or interpretation is imposed on it beyond
dominating `vortexTerm`, and `hdual` is a hypothesis about `Z`, not a consequence of `hZ`.

DERIVED: `1 / 4` and `3` are the entropy floor `(1 / 4) * Real.log 3`. `4 * n + 2` is the plaquette
count of a directed-cube path of length `n`: `4` per step, plus the `2` that close it. `0` is the strict
lower bound on `n` in `hdual`, which excludes the scale at which the denominator would be `2` and the
count empty. -/
theorem junction_of_scale_duality {μ c : ℝ} {Z : ℕ → ℝ}
    (hZ : ∀ n, Condensation.vortexTerm μ n ≤ Z n)
    (hdual : ∀ n, 0 < n → Real.log (Z n) / (4 * n + 2) ≤ c) :
    SelfSourcingJunction ((1 / 4) * Real.log 3) μ c := by
  show (1 / 4) * Real.log 3 - μ ≤ c
  refine le_of_tendsto Condensation.lower_ratio_tendsto ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact le_trans (Condensation.density_ratio_ge hZ hn) (hdual n hn)

/-- A `LatticeYM` assembled from a mode family and four families of inequalities.

The data are index and direction types, a coupling-indexed active set `s`, amplitude and mode families
`P` and `m`, a direction response `R`, the two constants `κ₀` and `κ`, and the coupling-indexed `μ`, `Δ`
and `c`. The hypotheses are `hfloor : κ₀ ≤ κ`, and, at every coupling `β`, `hdom` (`‖m β k‖ ≤ exp (-Δ β)`
on `s β`), `hfe` (`κ - μ β ≤ c β`) and `hgap` (`c β ≤ Δ β`).

The `hread` field is filled by `hread_of_junction` at each `β`. The mode family `m` is a parameter, so
it is constrained only by `hdom`; no mode is defined to be `exp (-(κ₀ - μ β))`.

Scope: `κ₀` and `κ` are constants in `β` while `μ`, `Δ` and `c` vary with it. `Idx` and `Dir` are
`Type`, not `Type*`. The construction is `noncomputable` and asserts nothing about `P`. -/
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

/-- Three conclusions at once, for the model `modelOfJunction` builds: at every coupling `β` the
correlator norm `‖∑_{k ∈ s β} P β k * (m β k) ^ τ‖` tends to `0` as `τ → ∞`; at every `β`,
`μ β - κ < 0`; and `R` is constant across directions.

`mass_gap_of_model` applied to `modelOfJunction`. Beyond that model's hypotheses it takes `hconf`
(`μ β < κ₀` at every `β`) and `hiso` (`R d = R d'` for all directions).

Scope: `hdom`, `hfe` and `hgap` are inputs here, not discharged; the third conclusion is `hiso`
restated, and the second is a strict inequality between reals, not a statement about a spectrum. The
first conclusion is convergence of the correlator norm to zero, with no rate.

DERIVED: `0` is the limit of the correlator norm and the strict upper bound in `μ β - κ < 0`. It is the
only numeral in the statement. -/
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
