import MassGap.Model
import MassGap.Measure

/-!
# MassGap.FullModel — the gap statement and the continuum-measure statement, conjoined

A `FullModel` bundles two structures: `gap : LatticeYM` with its obligations `h1 : A1_YM gap` and
`h2 : A2_YM gap`, which `Model.mass_gap_of_model` and `Model.mass_gap_rate_of_model` consume, and
`measure : LatticeYMFamily`, which `Measure.continuum_of_family` consumes. The three theorems here
conjoin the two results at three strengths:

* `mass_gap_rate_and_continuum` — `0 < κ₀ - μ β` with the geometric bound
  `‖C(τ)‖ ≤ (∑ ‖P k‖) · exp (-(κ₀ - μ β)) ^ τ`, paired with the measure half;
* `existence_and_gap_of_model` — `C(τ) → 0` at every coupling, `μ β - κ < 0`, and constancy of `R`,
  paired with the measure half;
* `existence_and_gap_of_wilson` — the same conjunction for the `FullModel` inside a
  `WilsonRealization`.

The measure half is the same existential in all three: a strictly monotone `φ : ℕ → ℕ` and a limit
`q : J → ℝ` with `Q j (φ k) → q j` at every `j`, the bound `|q j| ≤ ⌈c⌉₊ · B`, non-negativity, and
invariance of `q` under the two actions `actE` and `actP`.

Scope. The structures' fields are data supplied by whoever builds a `FullModel`; no theorem here
discharges `A1_YM`, `A2_YM` or any `LatticeYMFamily` field. The rate in the first theorem is at the
single coupling `β` in its binder and carries no lattice spacing. The two halves share no variable:
nothing in any statement relates `q` to the mode data. `q` is a real-valued function on the index
type `J`, with no bilinear form and no test space, so it is not the `OSData` that
`WightmanData.os_reconstruction_wightman` consumes, and no theorem here composes with that axiom.

The last section records physical parameters: `WilsonParams` (`N`, `L`, `kstar` with their
positivity), `WilsonParams.irCutoff` (`kstar · L / (2π)`), and `WilsonRealization`, which pairs a
`FullModel` with parameters under `measure.c = irCutoff`.
-/

namespace MassGap

open MassGap.Measure Filter

/-- Four fields: the reduction data `gap : LatticeYM`, its two obligations `h1 : A1_YM gap` and
`h2 : A2_YM gap`, and the finite-spacing data `measure : LatticeYMFamily`.

Bundling them is what lets one theorem state both conclusions. No field of the structure relates
`gap` to `measure`; that they describe one theory is an identification the builder of the structure
makes, and nothing in the type records it. -/
structure FullModel where
  /-- The reduction data at each coupling (for the mass gap). -/
  gap : LatticeYM
  /-- A1 (confinement) for the reduction data. `MassGap.Complete` supplies instances of it from the
  character bound, asymptotic freedom, and the entropy-response identification. -/
  h1 : A1_YM gap
  /-- A2 (isotropy) for the reduction data: equality of the direction responses `R d`. -/
  h2 : A2_YM gap
  /-- The finite-spacing Osterwalder–Schrader data across spacings (for the continuum measure). -/
  measure : LatticeYMFamily

/-- Two conclusions for one `FullModel` at one coupling `β`, conjoined.

The gap half, `Model.mass_gap_rate_of_model` applied to `M.gap` and `M.h1`: the rate is positive,
`0 < M.gap.κ₀ - M.gap.μ β`, and at every `τ : ℕ` the correlator obeys
`‖∑_{k ∈ s β} P β k * (m β k) ^ τ‖ ≤ (∑_{k ∈ s β} ‖P β k‖) * exp (-(κ₀ - μ β)) ^ τ`.

The measure half, `Measure.continuum_of_family` applied to `M.measure`: a strictly monotone
`φ : ℕ → ℕ` and a `q : M.measure.J → ℝ` with `Q j (φ k) → q j` at every `j`,
`|q j| ≤ ⌈M.measure.c⌉₊ * M.measure.B`, `0 ≤ q j`, and `q` fixed by `actE g` and by `actP σ`.

Scope. The rate is for the single coupling in the binder: it is not uniform in `β`, and it is a
lattice quantity with no spacing appearing in the statement. `M.h2` is not used by this theorem. The
prefactor is the sum of the amplitude norms, so the bound is geometric but not normalised at `τ = 0`
to anything smaller. The two halves are independent statements sharing no variable.

DERIVED: `0` is the strict lower bound on the rate `κ₀ - μ β` and the lower bound on the limit values
`q j`. It is the only numeral in the statement; `κ₀`, `μ`, `c` and `B` are fields of the model. -/
theorem mass_gap_rate_and_continuum (M : FullModel) (β : ℝ) :
    (0 < M.gap.κ₀ - M.gap.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ M.gap.s β, M.gap.P β k * (M.gap.m β k) ^ τ‖
        ≤ (∑ k ∈ M.gap.s β, ‖M.gap.P β k‖)
            * Real.exp (-(M.gap.κ₀ - M.gap.μ β)) ^ τ) ∧
      (∃ (q : M.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => M.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈M.measure.c⌉₊ : ℝ) * M.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (M.measure.actE g j) = q j) ∧
        (∀ σ j, q (M.measure.actP σ j) = q j)) :=
  ⟨mass_gap_rate_of_model M.gap M.h1 β, continuum_of_family M.measure⟩

#print axioms mass_gap_rate_and_continuum

/-- Two conclusions for one `FullModel`, the gap half quantified over all couplings.

The gap half, `Model.mass_gap_of_model` applied to `M.gap`, `M.h1` and `M.h2`: at every `β` the
correlator norm `‖∑_{k ∈ s β} P β k * (m β k) ^ τ‖` tends to `0` as `τ → ∞`; at every `β`,
`μ β - κ < 0`; and `R d = R d'` for every pair of directions.

The measure half, `Measure.continuum_of_family` applied to `M.measure`: the subsequence `φ`, the
limit `q`, the bound `|q j| ≤ ⌈c⌉₊ * B`, `0 ≤ q j`, and invariance of `q` under `actE` and `actP`.

Scope. The gap half gives convergence with no rate; `mass_gap_rate_and_continuum` is the version that
carries one, at a fixed coupling. `A1_YM`, `A2_YM` and the `LatticeYMFamily` fields are the structure's
data, so they are obligations on whoever supplies `M` rather than hypotheses of this theorem. The
third conjunct of the gap half is `A2_YM` restated. The two halves share no variable.

DERIVED: `0` is the limit of the correlator norm, the strict upper bound in `μ β - κ < 0`, and the
lower bound on `q j`. It is the only numeral in the statement. -/
theorem existence_and_gap_of_model (M : FullModel) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ M.gap.s β, M.gap.P β k * (M.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, M.gap.μ β - M.gap.κ < 0) ∧ (∀ d d', M.gap.R d = M.gap.R d')) ∧
      (∃ (q : M.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => M.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈M.measure.c⌉₊ : ℝ) * M.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (M.measure.actE g j) = q j) ∧
        (∀ σ j, q (M.measure.actP σ j) = q j)) :=
  ⟨mass_gap_of_model M.gap M.h1 M.h2, continuum_of_family M.measure⟩

-- Issuing the command, rather than quoting it in prose, is what makes the build report this
-- declaration's axiom footprint and what records it in `data/13_dat_axiom_footprints.csv`.
#print axioms existence_and_gap_of_model

/-! ### Physical parameters and the infrared cutoff

`WilsonParams` records the gauge order `N`, the box size `L` and the confinement momentum scale
`kstar`, each with its positivity as a field. `WilsonParams.irCutoff` is `kstar * L / (2 * π)`.
`WilsonRealization` pairs a `FullModel` with such parameters under the single constraint
`model.measure.c = params.irCutoff`.

The cutoff is built from the box size and the confinement scale alone: no lattice spacing and no `N`
appear in it, which is what makes `⌈c⌉₊` — the resolved-dimension bound carried by
`LatticeYMFamily` — independent of both. -/

/-- Three physical parameters with their positivity: the gauge order `N` with `2 ≤ N`, the box size
`L` with `0 < L`, and the confinement momentum scale `kstar` with `0 < kstar`.

The three proofs are fields, so the structure cannot be built without them. Nothing else is imposed:
`N` is a natural number and `L`, `kstar` are reals in no particular units. -/
structure WilsonParams where
  /-- Gauge group order (`SU(N)`, `N ≥ 2`). -/
  N : ℕ
  hN : 2 ≤ N
  /-- Physical box size. -/
  L : ℝ
  hL : 0 < L
  /-- Confinement / correlation momentum scale (finite by A1). -/
  kstar : ℝ
  hk : 0 < kstar

/-- `kstar * L / (2 * Real.pi)`, the infrared cutoff.

It is a function of the box size and the confinement scale only. No lattice spacing and no `N` enters,
so `⌈irCutoff⌉₊` is independent of both. -/
noncomputable def WilsonParams.irCutoff (W : WilsonParams) : ℝ := W.kstar * W.L / (2 * Real.pi)

theorem WilsonParams.irCutoff_pos (W : WilsonParams) : 0 < W.irCutoff :=
  div_pos (mul_pos W.hk W.hL) (by positivity)

/-- A `FullModel` together with `WilsonParams`, constrained by `hc : model.measure.c =
params.irCutoff`.

That equation is the only link between the parameters and the model: no field derives any part of the
`FullModel` from `N`, `L` or `kstar`, and the structure records no relation between the gauge order and
the reduction data. -/
structure WilsonRealization where
  params : WilsonParams
  model : FullModel
  /-- The construction's infrared cutoff is the physical `k⋆L/(2π)`. -/
  hc : model.measure.c = params.irCutoff

/-- `existence_and_gap_of_model` restated for the `FullModel` carried by a `WilsonRealization`: the
correlator norms tend to `0` at every coupling, `μ β - κ < 0`, `R` is constant across directions, and
the measure half holds for `W.model.measure`.

Scope. The proof is `existence_and_gap_of_model W.model`, so `W.params` and `W.hc` are not used. The
physical parameters therefore constrain nothing in the conclusion; they are available to a reader of
`W`, not to this statement.

DERIVED: `0` is the limit of the correlator norm, the strict upper bound in `μ β - κ < 0`, and the
lower bound on `q j`. It is the only numeral in the statement. -/
theorem existence_and_gap_of_wilson (W : WilsonRealization) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ W.model.gap.s β,
          W.model.gap.P β k * (W.model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, W.model.gap.μ β - W.model.gap.κ < 0) ∧ (∀ d d', W.model.gap.R d = W.model.gap.R d')) ∧
      (∃ (q : W.model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => W.model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈W.model.measure.c⌉₊ : ℝ) * W.model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (W.model.measure.actE g j) = q j) ∧
        (∀ σ j, q (W.model.measure.actP σ j) = q j)) :=
  existence_and_gap_of_model W.model

end MassGap
