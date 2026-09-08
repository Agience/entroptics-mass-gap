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
interior reduces to the finite correlation length `d2_le_bound` (`⟨d²⟩ ≤ 1`, `Complete.lean`, via
`ym_crossover_confinement`), and the uniform-in-`a` continuum to refinement-invariance, so A1's sole
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
finite correlation length `d2_le_bound` (`⟨d²⟩ ≤ 1`, `Complete.lean`, via `ym_crossover_confinement`), and
the uniform-in-`a` continuum to refinement-invariance, so A1's sole remaining input is that finite
correlation length. -/
def A1_YM (M : LatticeYM) : Prop := A1 M.μ M.κ₀

/-- **A2 for the model: isotropy.** The directional read is direction-independent. Proved in part
(`A2_hypercubic_holds`, `gram_read_rotation_invariant`, `continuumRotationCongruence_of_gram`); the
continuum axis-role `SO(4)` reduces to the Nyquist-Shannon sampling isometry
(`A2_continuum_of_sampling`). A2's sole remaining input is that sampling isometry. -/
def A2_YM (M : LatticeYM) : Prop := A2 M.R

/-- **The result for the model.** Given the two obligations `A1_YM` (confinement) and `A2_YM`
(isotropy) for a lattice Yang-Mills model `M`, the mass gap (`C(τ) → 0` at every coupling),
non-triviality (`μ - κ < 0`, the area law), and Euclidean `SO(4)` invariance all follow. This is
`existence_and_gap_from_apriori` applied to the named model data; the two obligations are the open input, each
reduced to one input (for A1 the finite correlation length `d2_le_bound`, `⟨d²⟩ ≤ 1`, via
`Complete.ym_crossover_confinement`; for A2 the Nyquist-Shannon sampling isometry). -/
theorem mass_gap_of_model (M : LatticeYM) (h1 : A1_YM M) (h2 : A2_YM M) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ M.s β, M.P β k * (M.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, M.μ β - M.κ < 0) ∧
      (∀ d d', M.R d = M.R d') :=
  existence_and_gap_from_apriori M.s M.P M.m M.κ₀ M.κ M.μ M.R M.hfloor h1 h2 M.hread

end MassGap
