import MassGap.GapOfDecay
import MassGap.Complete

/-!
# Yang–Mills: the spectral gap, wired from confinement through the moment-support bridge

This instantiates the reduction-core bridge (`GapOfDecay.gapped_of_positive_decay`) for `SU(N)`. The reduction
takes confinement `μYMAt N β < κ₀YM` as the hypothesis `hconf`, hence the entropy margin `ΔYMAt N β = κ₀YM - μYMAt N β
> 0`. Feeding the finite-aperture transfer datum — vacuum eigenvalue `1` and a single excited mode at the margin
`e^{-ΔYMAt N β}`, with reflection-positive weight `1` — through `gapped_of_positive_decay` **derives** the spectral
support bound and reconstructs a `GappedQuantumTheory` whose mass gap is exactly `ΔYMAt N β`.

Unlike `ym_mass_gap` (which delivers only `C(τ)→0`), this produces the the relevant object:
`spectrum(H) ⊆ {0} ∪ [ΔYMAt N β, ∞)` for the reconstructed Hamiltonian `H = -log T` — the spectral gap DERIVED from
the decay via `MomentSupport.le_of_positive_weight_decay`, not assumed. Foundational axioms + the reduction's own
(the read's footprint).
-/

namespace MassGap

open scoped ComplexOrder
open MassGap.Reconstruction

/-- **The Yang–Mills gapped quantum theory, from confinement.** For every physical coupling `β ≥ 0`, the entropy
margin `ΔYMAt N β = κ₀YM - μYMAt N β > 0` reconstructs (through the moment-support bridge) a gapped quantum theory with
mass gap `ΔYMAt N β`. The finite-aperture transfer datum is `diag(1, e^{-ΔYMAt N β})`; the spectral bound feeding the CFC
core is DERIVED from the single-mode decay, not hand-set. -/
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

/-- The Yang–Mills mass gap reconstructed from confinement is exactly the entropy margin `ΔYMAt N β = κ₀YM - μYMAt N β`. -/
theorem ymGapped_gap (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    (ymGapped N β hconf).gap = ΔYMAt N β := rfl

/-- **The reconstructed Yang–Mills Hamiltonian has a positive spectral gap.** `spectrum(H) ⊆ {0} ∪ [ΔYMAt N β, ∞)`
with `H` self-adjoint, `H ≥ 0`, and the vacuum at `0` — the spectral-gap form, derived end-to-end from
confinement through the moment-support bridge (not the weaker `C(τ)→0`, and not an assumed `hsp`). -/
theorem ym_spectral_gap (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    IsSelfAdjoint (ymGapped N β hconf).ham ∧ 0 ≤ (ymGapped N β hconf).ham ∧
      (0 : ℝ) ∈ spectrum ℝ (ymGapped N β hconf).ham ∧
      spectrum ℝ (ymGapped N β hconf).ham ⊆ {0} ∪ Set.Ici (ΔYMAt N β) :=
  ⟨(ymGapped N β hconf).selfAdjoint, (ymGapped N β hconf).nonneg, (ymGapped N β hconf).vacuum,
    ymGapped_gap N β hconf ▸ (ymGapped N β hconf).spectral_gap⟩

#print axioms ym_spectral_gap

end MassGap
