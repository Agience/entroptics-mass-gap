import MassGap.GappedTheory
import MassGap.MomentSupport

/-!
# The spectral gap from the correlator's decay — the reduction-core bridge, wired end-to-end

`GappedExample` builds a gapped theory from the HAND-SET operator `Tc = diag(1, 3^{-1/4})`, computing its
spectrum by hand. This module instead **derives** the transfer operator's spectral-support bound (`hsp`) from
the PROVED decay of the connected correlator, closing the gap the reduction-core audit found (the reduction
delivers `C(τ)→0`; the spectral gap was a disconnected conditional assuming `hsp`).

The finite-volume transfer operator `T` is self-adjoint (reflection positivity, Osterwalder–Seiler), hence
unitarily a real diagonal `diag(λ_k)` with `λ_k ∈ (0,1]`, and the connected correlator is the positive-weight
sum `C_conn(τ) = ∑_{k excited} w_k λ_k^τ`, `w_k = |⟨v,e_k⟩|² ≥ 0`. The proof supplies `C_conn(τ) ≤ M e^{-Δτ}`.
`MomentSupport.le_of_positive_weight_decay` then forces every excited `λ_k ≤ e^{-Δ}`, so
`spectrum ⊆ {1} ∪ [ε, e^{-Δ}] = hsp`, which feeds `reconstruct_gapped` to yield the mass gap `Δ`.

The physics inputs are named hypotheses, each grounded: `hwnn` (positive weights = RP), `hwpos` (cyclicity =
a good `0⁺⁺` operator overlapping the excited modes, R1), `hεlam` (`T ≥ ε > 0`, bounded action, R2),
`hvac` (the non-excited modes are the vacuum `λ=1`). The gap `Δ` is the DECAY RATE, derived — not assumed.
-/

namespace MassGap.Reconstruction

open scoped ComplexOrder
open MassGap

variable {ι : Type*}

/-- The real diagonal transfer operator `diag(λ_k)` on `ι → ℂ`. Self-adjoint. -/
noncomputable def diagOp (lam : ι → ℝ) : ι → ℂ := fun k => ((lam k : ℝ) : ℂ)

theorem diagOp_selfAdjoint (lam : ι → ℝ) : IsSelfAdjoint (diagOp lam) := by
  show star (diagOp lam) = diagOp lam
  funext k
  simp [diagOp, Pi.star_apply, Complex.conj_ofReal]

/-- Every point of the `ℝ`-spectrum of `diag(λ)` is some eigenvalue `λ_k`. -/
theorem mem_spectrum_diagOp {lam : ι → ℝ} {r : ℝ} (hr : r ∈ spectrum ℝ (diagOp lam)) :
    ∃ k, r = lam k := by
  by_contra hc
  simp only [not_exists] at hc
  rw [spectrum.mem_iff] at hr
  apply hr
  rw [Pi.isUnit_iff]
  intro k
  rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero, sub_ne_zero]
  simp only [diagOp]
  intro h
  exact hc k (by exact_mod_cast h)

/-- The vacuum eigenvalue `1` is in the spectrum whenever some mode has `λ_{k₀} = 1`. -/
theorem one_mem_spectrum_diagOp {lam : ι → ℝ} (k0 : ι) (hk0 : lam k0 = 1) :
    (1 : ℝ) ∈ spectrum ℝ (diagOp lam) := by
  rw [spectrum.mem_iff, map_one]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h0 := hu k0
  rw [Pi.sub_apply, Pi.one_apply] at h0
  simp only [diagOp, hk0, Complex.ofReal_one, sub_self] at h0
  exact not_isUnit_zero h0

/-- `spectrum ⊆ {1} ∪ [ε, ρ]` from: non-excited modes are the vacuum `1`, excited modes lie in `[ε, ρ]`. -/
theorem spectrum_diagOp_subset {lam : ι → ℝ} (s : Finset ι) {ε ρ : ℝ}
    (hvac : ∀ k, k ∉ s → lam k = 1) (hexc : ∀ k ∈ s, ε ≤ lam k ∧ lam k ≤ ρ) :
    spectrum ℝ (diagOp lam) ⊆ {1} ∪ Set.Icc ε ρ := by
  intro r hr
  obtain ⟨k, rfl⟩ := mem_spectrum_diagOp hr
  by_cases hk : k ∈ s
  · exact Or.inr (Set.mem_Icc.mpr (hexc k hk))
  · exact Or.inl (Set.mem_singleton_iff.mpr (hvac k hk))

/-- **The spectral gap, derived from the connected correlator's decay.** Given the finite-volume transfer
spectral data — real eigenvalues `lam`, positive weights `w` — with reflection positivity (`hwnn`), cyclicity
of a good operator (`hwpos`, R1), strict positivity `T ≥ ε` (`hεlam`, R2), the non-excited modes the vacuum
(`hvac`), and the PROVED connected-correlator decay `∑_{k∈s} w_k λ_k^τ ≤ M e^{-Δτ}` (`hdecay`), the
reconstruction yields a `GappedQuantumTheory` with mass gap exactly the decay rate `Δ`. The spectral bound
`hsp` is DERIVED here (via `MomentSupport.le_of_positive_weight_decay`), not assumed. -/
noncomputable def gapped_of_positive_decay [Fintype ι]
    (lam w : ι → ℝ) (s : Finset ι) (M ε Δ : ℝ)
    (hε : 0 < ε) (hΔ : 0 < Δ)
    (hvac : ∀ k, k ∉ s → lam k = 1) (hvacpt : ∃ k, k ∉ s)
    (hεlam : ∀ k ∈ s, ε ≤ lam k)
    (hwnn : ∀ k ∈ s, 0 ≤ w k) (hwpos : ∀ k ∈ s, 0 < w k)
    (hdecay : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * (Real.exp (-Δ)) ^ τ) :
    GappedQuantumTheory (ι → ℂ) :=
  let ρ := Real.exp (-Δ)
  have hρ : 0 < ρ := Real.exp_pos _
  have hlamnn : ∀ k ∈ s, 0 ≤ lam k := fun k hk => le_trans (le_of_lt hε) (hεlam k hk)
  have hupper : ∀ k ∈ s, lam k ≤ ρ := fun k hk =>
    le_of_positive_weight_decay s w lam M ρ hwnn hlamnn hρ hdecay k hk (hwpos k hk)
  have hsp : spectrum ℝ (diagOp lam) ⊆ {1} ∪ Set.Icc ε ρ :=
    spectrum_diagOp_subset s hvac (fun k hk => ⟨hεlam k hk, hupper k hk⟩)
  have h1 : (1 : ℝ) ∈ spectrum ℝ (diagOp lam) :=
    hvacpt.elim (fun k0 hk0 => one_mem_spectrum_diagOp k0 (hvac k0 hk0))
  reconstruct_gapped (diagOp lam) (diagOp_selfAdjoint lam) hε hΔ h1 hsp

/-- The gap reconstructed from the decay is exactly the decay rate `Δ`. -/
theorem gapped_of_positive_decay_gap [Fintype ι]
    (lam w : ι → ℝ) (s : Finset ι) (M ε Δ : ℝ)
    (hε : 0 < ε) (hΔ : 0 < Δ)
    (hvac : ∀ k, k ∉ s → lam k = 1) (hvacpt : ∃ k, k ∉ s)
    (hεlam : ∀ k ∈ s, ε ≤ lam k)
    (hwnn : ∀ k ∈ s, 0 ≤ w k) (hwpos : ∀ k ∈ s, 0 < w k)
    (hdecay : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * (Real.exp (-Δ)) ^ τ) :
    (gapped_of_positive_decay lam w s M ε Δ hε hΔ hvac hvacpt hεlam hwnn hwpos hdecay).gap = Δ := rfl

#print axioms gapped_of_positive_decay

/-- **A genuine multi-mode witness.** Vacuum `1` plus three excited modes `1/2, 1/4, 1/8` with positive weights.
Here the moment-support lemma does real work: it bounds ALL THREE excited eigenvalues below `e^{-Δ}=1/2`, and the
decay hypothesis is a TRUE inequality `∑_k λ_k^τ ≤ 3·(1/2)^τ` (each mode `≤ 1/2`), not the equality of a single
hand-placed mode. The reconstructed mass gap is `Δ = log 2 > 0`. -/
noncomputable def multiModeGapped : GappedQuantumTheory (Fin 4 → ℂ) :=
  gapped_of_positive_decay (ι := Fin 4)
    ![1, 1/2, 1/4, 1/8] ![0, 1, 1, 1] {1, 2, 3} 3 (1/8) (Real.log 2)
    (by norm_num) (Real.log_pos (by norm_num))
    (by intro k hk; fin_cases k <;> simp_all [Finset.mem_insert, Finset.mem_singleton])
    ⟨0, by decide⟩
    (by intro k hk; fin_cases k <;> simp_all [Finset.mem_insert, Finset.mem_singleton] <;> norm_num)
    (by intro k hk; fin_cases k <;> simp_all [Finset.mem_insert, Finset.mem_singleton])
    (by intro k hk; fin_cases k <;> simp_all [Finset.mem_insert, Finset.mem_singleton])
    (by
      intro τ
      have e : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
      rw [e]
      have hb : ∀ k ∈ ({1, 2, 3} : Finset (Fin 4)),
          ![0, 1, 1, 1] k * ![1, 1/2, 1/4, 1/8] k ^ τ ≤ (1 / 2 : ℝ) ^ τ := by
        intro k hk
        fin_cases hk <;> simp <;> gcongr <;> norm_num
      calc ∑ k ∈ ({1, 2, 3} : Finset (Fin 4)), ![0, 1, 1, 1] k * ![1, 1/2, 1/4, 1/8] k ^ τ
          ≤ ∑ _k ∈ ({1, 2, 3} : Finset (Fin 4)), (1 / 2 : ℝ) ^ τ := Finset.sum_le_sum hb
        _ = 3 * (1 / 2 : ℝ) ^ τ := by
              rw [Finset.sum_const, show ({1, 2, 3} : Finset (Fin 4)).card = 3 from by decide]
              norm_num [nsmul_eq_mul])

/-- The multi-mode witness reconstructs a gap `log 2`. -/
theorem multiModeGapped_gap : multiModeGapped.gap = Real.log 2 := rfl

#print axioms multiModeGapped

end MassGap.Reconstruction
