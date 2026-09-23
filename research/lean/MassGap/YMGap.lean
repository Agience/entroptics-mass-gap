import MassGap.GapOfDecay
import MassGap.Complete

/-!
# MassGap.YMGap — a gapped quantum theory for `SU(N)` from the confinement inequality

This module instantiates `GapOfDecay.gapped_of_positive_decay` at a two-mode transfer datum and states
the resulting spectral containment.

The input is `hconf : μYMAt N β < κ₀YM`. `gap_pos_iff_confinement_at` turns it into `0 < ΔYMAt N β`,
where `ΔYMAt N β = κ₀YM - μYMAt N β`. The datum supplied is eigenvalues `![1, exp (-(ΔYMAt N β))]`,
weights `![0, 1]`, excited set `{1}`, prefactor `M = 1` and floor `ε = exp (-(ΔYMAt N β))`: index `0`
carries the vacuum eigenvalue `1` and weight `0`, index `1` is a single excited mode sitting exactly at
the margin. The decay hypothesis is then the equality `∑_{k ∈ {1}} w_k λ_k^τ = (e^{-Δ})^τ`.

The spectral-support bound is not an argument to this module. `gapped_of_positive_decay` obtains it
from the decay through `MomentSupport.le_of_positive_weight_decay`; what is supplied here is the decay
and the positivity side conditions.

Scope: `ΔYMAt`, `κ₀YM` and `μYMAt` are defined in `MassGap.Complete`. This module adds no lattice input
of its own and says nothing about how `hconf` is obtained. The carrier is finite-dimensional,
`Fin 2 → ℂ`.
-/

namespace MassGap

open scoped ComplexOrder
open MassGap.Reconstruction

/-- The two-mode gapped quantum theory on `Fin 2 → ℂ` built from `hconf : μYMAt N β < κ₀YM`.

`N : ℕ` and `β : ℝ` are arbitrary: no positivity, integrality beyond `ℕ`, or range is imposed on
either, and `hconf` is the only hypothesis. The transfer datum is `diag(1, e^{-ΔYMAt N β})` with weight
`0` on the vacuum index and weight `1` on the excited index; `gap_pos_iff_confinement_at` converts
`hconf` into the positivity of `ΔYMAt N β` that `gapped_of_positive_decay` requires. The gap of the
resulting structure is `ΔYMAt N β`.

DERIVED: `2` is the carrier dimension `Fin 2` — one vacuum index and one excited index, the smallest
state space on which the excited/non-excited split of `gapped_of_positive_decay` is inhabited on both
sides. It is the only numeral in the statement. -/
noncomputable def ymGapped (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    GappedQuantumTheory (Fin 2 → ℂ) :=
  gapped_of_positive_decay
    (lam := ![1, Real.exp (-(ΔYMAt N β))]) (w := ![0, 1]) (s := {1})
    (M := 1) (ε := Real.exp (-(ΔYMAt N β))) (Δ := ΔYMAt N β)
    (Real.exp_pos _)
    ((gap_pos_iff_confinement_at N β).mpr hconf)
    (by                                        -- hvac: non-excited mode 0 is the vacuum λ=1
      intro k hk
      simp only [Finset.mem_singleton] at hk
      fin_cases k
      · simp
      · exact absurd rfl hk)
    ⟨0, by decide⟩                             -- hvacpt: 0 ∉ {1}
    (by                                        -- hεlam: ε = e^{-Δ} ≤ λ_1 = e^{-Δ}
      intro k hk
      simp only [Finset.mem_singleton] at hk
      subst hk
      simp)
    (by                                        -- hwnn: 0 ≤ w_1 = 1
      intro k hk
      simp only [Finset.mem_singleton] at hk
      subst hk
      simp)
    (by                                        -- hwpos: 0 < w_1 = 1
      intro k hk
      simp only [Finset.mem_singleton] at hk
      subst hk
      simp)
    (by                                        -- hdecay: ∑_{k∈{1}} w_k λ_k^τ = (e^{-Δ})^τ ≤ 1·(e^{-Δ})^τ
      intro τ
      rw [Finset.sum_singleton]
      simp)

/-- The gap field of `ymGapped N β hconf` is `ΔYMAt N β`, by `rfl`: the reconstruction carries the
decay rate through definitionally rather than recomputing it. -/
theorem ymGapped_gap (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    (ymGapped N β hconf).gap = ΔYMAt N β := rfl

/-- Four properties of the Hamiltonian `(ymGapped N β hconf).ham`: it is self-adjoint, it is
non-negative, `0` lies in its `ℝ`-spectrum, and that spectrum is contained in
`{0} ∪ Set.Ici (ΔYMAt N β)`.

The conjuncts are the `GappedQuantumTheory` fields `selfAdjoint`, `nonneg`, `vacuum` and
`spectral_gap`, the last rewritten along `ymGapped_gap`. Scope: the spectrum is taken over `ℝ` on the
finite-dimensional carrier `Fin 2 → ℂ`, and the containment is one-directional — it does not assert
that any point of `Set.Ici (ΔYMAt N β)` is attained, nor that `ΔYMAt N β` is positive (that comes from
`hconf`, used to build the structure).

DERIVED: `0` is the vacuum energy. It is the lower bound in `0 ≤ ham`, the spectral point asserted to
be present, and the isolated point of the containing set. It is the only numeral in the statement. -/
theorem ym_spectral_gap (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    IsSelfAdjoint (ymGapped N β hconf).ham ∧ 0 ≤ (ymGapped N β hconf).ham ∧
      (0 : ℝ) ∈ spectrum ℝ (ymGapped N β hconf).ham ∧
      spectrum ℝ (ymGapped N β hconf).ham ⊆ {0} ∪ Set.Ici (ΔYMAt N β) :=
  ⟨(ymGapped N β hconf).selfAdjoint, (ymGapped N β hconf).nonneg, (ymGapped N β hconf).vacuum,
    ymGapped_gap N β hconf ▸ (ymGapped N β hconf).spectral_gap⟩

#print axioms ym_spectral_gap

end MassGap
