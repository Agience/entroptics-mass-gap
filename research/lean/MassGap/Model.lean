import Mathlib
import MassGap.Apriori

/-!
# The lattice Yang-Mills model interface (Phase 0)

`MassGap.Apriori` derives the requirements from two propositions `A1`, `A2` stated over abstract
data (`s, P, m, μ, R, κ₀, κ`). This file names that data as the objects of a lattice `SU(N)` gauge
theory and packages the reduction as a single structure, so the two obligations `A1`, `A2` have a
typed home and the cited inputs are separated from them.

**What this file is.** An *interface*. The fields of `LatticeYM` are the inputs the Osterwalder-Seiler
finite-spacing construction supplies (a bounded, positive, self-adjoint transfer matrix at every
spacing) together with the two entropy-matched reads of the companion instrument [E]: the centre-vortex
tension `μ` and the directional read `R`. `hfloor` is the entropy floor `κ₀ = ¼ log 3 ≤ κ` (`Floor.lean`);
`hread` is the read margin, the bound on the DMD dominant magnitude the aperture returns
(`Apriori.hread_of_dominant`, `Apriori.margin_of_dominant_rate`).

**What this file supplies, and what it leaves open.** The physical realisation of `Idx, Dir, s, P, m,
μ, R` from the `SU(N)` Wilson measure is the modelling identification stated in §2-§3 of the paper and
cited to Osterwalder-Seiler; it is not re-derived here. `A1_YM` and `A2_YM` are the two obligations.
`Apriori.lean` and `Certify.lean` prove them in part and reduce the remainder to one established input
each. A1: the strong- and weak-coupling ends (`apriori_A1_strong`, `apriori_A1_weak`); the crossover
interior reduces to one aperture-independent bound on the substrate's lag moment
(`Complete.confinement_of_bounded_substrate`), and the uniform-in-`a` continuum to
refinement-invariance, so A1's sole
remaining input is that finite correlation length. A2: the discrete point group and the spatial Gram rotations
(`A2_hypercubic_holds`, `gram_read_rotation_invariant`, `continuumRotationCongruence_of_gram`); the
continuum axis-role `SO(4)` reduces to the Nyquist-Shannon sampling isometry (`A2_continuum_of_sampling`,
`orthogonal_of_preserves_dotProduct`), A2's sole remaining input. Both remaining inputs are established
results, cited, not re-derived here. `mass_gap_of_model` derives the mass gap, non-triviality, and `SO(4)`
from `A1_YM ∧ A2_YM`; the two obligations remain hypotheses of that theorem.
-/

namespace MassGap

/-- **The lattice Yang-Mills model interface.** The abstract data of `existence_and_gap_from_apriori`, named as
the objects of a lattice `SU(N)` gauge theory at every coupling `β`. -/
structure LatticeYM where
  /-- Mode index type of the entropy-matched correlation read. -/
  Idx : Type
  /-- Orientation type of the directional read. -/
  Dir : Type
  /-- Active modes above the noise floor at coupling `β`. -/
  s : ℝ → Finset Idx
  /-- Mode weights `P_k(β)` of the finite exponential sum `C(τ) = ∑ P_k m_k^τ`. -/
  P : ℝ → Idx → ℂ
  /-- Mode magnitudes `m_k(β)` (DMD / transfer-matrix eigenvalues). -/
  m : ℝ → Idx → ℂ
  /-- The centre-vortex tension read `μ(β)`. -/
  μ : ℝ → ℝ
  /-- The directional (orientation) read `R`. -/
  R : Dir → ℝ
  /-- The entropy floor `κ₀ = ¼ log 3` (`Floor.floor_pos`). -/
  κ₀ : ℝ
  /-- The vortex multiplicity density `κ`, with the floor below it. -/
  κ : ℝ
  /-- The entropy floor sits below the multiplicity density. -/
  hfloor : κ₀ ≤ κ
  /-- The read margin: every active mode magnitude clears the free-energy margin `e^{-(κ₀-μ)}`
  (`Apriori.hread_of_dominant`; the DMD dominant magnitude the aperture returns). -/
  hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))

/-- **A1 for the model: confinement.** The centre-vortex tension stays below the floor at every
coupling. Proved in part (`apriori_A1_strong`, `apriori_A1_weak`); the crossover interior reduces to the
aperture-independent bound on the lag moment (`Complete.confinement_of_bounded_substrate`), and
the uniform-in-`a` continuum to refinement-invariance, so A1's sole remaining input is that finite
correlation length. -/
def A1_YM (M : LatticeYM) : Prop := A1 M.μ M.κ₀

/-- **A2 for the model: isotropy.** The directional read is direction-independent. Proved in part
(`A2_hypercubic_holds`, `gram_read_rotation_invariant`, `continuumRotationCongruence_of_gram`); the
continuum axis-role `SO(4)` reduces to the Nyquist-Shannon sampling isometry
(`A2_continuum_of_sampling`). A2's sole remaining input is that sampling isometry. -/
def A2_YM (M : LatticeYM) : Prop := A2 M.R

/-- **A finite mode expansion whose magnitudes are bounded decays geometrically.**

The whole content of an exponential mass gap, separated from every structure that might carry it: if
`‖m_k‖ ≤ E` for the active modes, then `‖∑ P_k m_k^τ‖ ≤ (∑‖P_k‖) E^τ`. Whether that is a GAP depends
entirely on `E < 1`, which this does not assume and cannot supply -- it is the caller's `κ₀ - μ > 0`.

Stated once, for the model level and the Wilson level both. The two differ only in where the bound on
the magnitudes comes from (`LatticeYM.hread` there, the `hdom` hypothesis here), which is a difference
in what is assumed, not in what is proved.

DERIVED: no literal decides anything. The `τ` is the lag and `E` the caller's bound. -/
theorem geometric_bound_of_mode_bound {Idx : Type*} (s : Finset Idx) (P m : Idx → ℂ) (E : ℝ)
    (hE : 0 ≤ E) (hm : ∀ k ∈ s, ‖m k‖ ≤ E) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (m k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * E ^ τ := by
  calc ‖∑ k ∈ s, P k * (m k) ^ τ‖ ≤ ∑ k ∈ s, ‖P k * (m k) ^ τ‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖P k‖ * E ^ τ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hm k hk) τ) (norm_nonneg _)
    _ = (∑ k ∈ s, ‖P k‖) * E ^ τ := by rw [← Finset.sum_mul]

#print axioms geometric_bound_of_mode_bound

/-- **THE GAP, WITH ITS RATE: `Δ = κ₀ - μ`.**

`mass_gap_of_model` concludes that the correlation tends to zero. That is weaker than a mass gap and
deliberately so -- a power law tends to zero too -- and it is not the statement the problem asks for,
which is a POSITIVE `Δ` with `C(τ)` bounded by `e^{-Δτ}`.

The rate was already in the structure. `LatticeYM.hread` bounds every active mode magnitude by
`e^{-(κ₀ - μ β)}`, and A1 puts `μ β < κ₀`, so that factor is strictly below one. Summing the finite
mode expansion against it gives geometric decay at an explicit rate, and the rate is the MARGIN
BETWEEN THE ENTROPY FLOOR AND THE MEASURED TENSION -- not a fitted constant, not an existential, and
not a limit: a difference of two named quantities, one proved (`Floor.lean`) and one measured.

    |C(τ)|  ≤  (∑_k ‖P_k‖) · e^{-(κ₀ - μ)τ}

WHAT THIS DOES AND DOES NOT SETTLE. It settles the SHAPE: the conclusion is now exponential with a
named positive rate rather than convergence to zero. It does not by itself make `Δ` uniform in the
lattice spacing -- that is `ZeroMode.gap_phys_of_fixed_screen`, which needs the aperture held at a
fixed physical extent -- nor does it discharge `hread`, which is the structure's own hypothesis and
carries the modelling content.

DERIVED: every constant is a hypothesis of the structure. `κ₀` is the proved entropy floor and `μ β`
the measured tension; nothing here introduces a number of its own. -/
theorem mass_gap_rate_of_model (M : LatticeYM) (h1 : A1_YM M) (β : ℝ) :
    0 < M.κ₀ - M.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖
        ≤ (∑ k ∈ M.s β, ‖M.P β k‖) * Real.exp (-(M.κ₀ - M.μ β)) ^ τ := by
  exact ⟨sub_pos.mpr (h1 β),
    fun τ => geometric_bound_of_mode_bound (M.s β) (M.P β) (M.m β) _
      (Real.exp_pos _).le (fun k hk => M.hread β k hk) τ⟩

#print axioms mass_gap_rate_of_model

/-- **The rate, as a decay constant.** `e^{-Δ}` with `Δ = κ₀ - μ > 0` is strictly inside the unit
interval, which is the form a transfer-matrix gap is usually stated in and the one
`ZeroMode.gap_phys_of_fixed_screen` consumes. -/
theorem mass_gap_ratio_lt_one (M : LatticeYM) (h1 : A1_YM M) (β : ℝ) :
    Real.exp (-(M.κ₀ - M.μ β)) < 1 := by
  have hgap : 0 < M.κ₀ - M.μ β := sub_pos.mpr (h1 β)
  exact Real.exp_lt_one_iff.mpr (by linarith)

#print axioms mass_gap_ratio_lt_one

/-- **The result for the model.** Given the two obligations `A1_YM` (confinement) and `A2_YM`
(isotropy) for a lattice Yang-Mills model `M`, the correlation's decay to zero (`C(τ) → 0` at every coupling -- for the RATE, which is what a
mass gap asserts, see `mass_gap_rate_of_model` above),
non-triviality (`μ - κ < 0`, the area law), and Euclidean `SO(4)` invariance all follow. This is
`existence_and_gap_from_apriori` applied to the named model data; the two obligations are the open input, each
reduced to one input (for A1 an aperture-independent bound on the lag moment, via
`Complete.confinement_of_bounded_substrate`; for A2 the Nyquist-Shannon sampling isometry). -/
theorem mass_gap_of_model (M : LatticeYM) (h1 : A1_YM M) (h2 : A2_YM M) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, M.μ β - M.κ < 0) ∧
      (∀ d d', M.R d = M.R d') :=
  existence_and_gap_from_apriori M.s M.P M.m M.κ₀ M.κ M.μ M.R M.hfloor h1 h2 M.hread

end MassGap
