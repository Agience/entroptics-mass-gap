import MassGap.GappedTheory
import MassGap.MomentSupport

/-!
# MassGap.GapOfDecay — a gapped theory built from a diagonal transfer operator and a decay bound

This module works with a diagonal operator on `ι → ℂ` whose entries are real, and derives its
spectral-support bound from a decay hypothesis rather than taking that bound as an argument.

The setting it is written for: a finite-volume transfer operator is self-adjoint under reflection
positivity, hence unitarily a real diagonal `diag(λ_k)`, and the connected correlator is a
positive-weight sum `∑_{k excited} w_k λ_k^τ` with `w_k = |⟨v, e_k⟩|²`. The module takes the
eigenvalues `lam`, the weights `w`, and the excited set `s` as data.

The chain. `diagOp` is the operator; `mem_spectrum_diagOp` shows every real spectral point is one of
the `λ_k`; `one_mem_spectrum_diagOp` places the vacuum eigenvalue in the spectrum;
`spectrum_diagOp_subset` assembles `spectrum ⊆ {1} ∪ Icc ε ρ` from a vacuum clause and a two-sided
bound on the excited modes. `gapped_of_positive_decay` supplies the upper bound `ρ = exp (-Δ)` by
calling `MomentSupport.le_of_positive_weight_decay` on the decay hypothesis, then hands the result to
`reconstruct_gapped`.

The hypotheses are named for what they correspond to: `hwnn` and `hwpos` for non-negative and strictly
positive weights on the excited set, `hεlam` for a strictly positive floor on the excited eigenvalues,
`hvac` for the non-excited modes being at eigenvalue `1`, and `hdecay` for the bound
`∑_{k ∈ s} w_k λ_k^τ ≤ M (e^{-Δ})^τ` at every natural `τ`.

Scope: `ι` is required to be a `Fintype` for the reconstruction, the operator is diagonal by
construction rather than diagonalised here, and the gap delivered is exactly the `Δ` that appears in
`hdecay`. `multiModeGapped` is a worked instance with three excited modes.
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

/-- If some index `k0` has `lam k0 = 1`, then `1` lies in the `ℝ`-spectrum of `diagOp lam`.

No finiteness or positivity is needed; the witness index is supplied explicitly.

DERIVED: `1` is the vacuum eigenvalue, both as the hypothesis on `lam k0` and as the spectral point
concluded. It is the only numeral in the statement. -/
theorem one_mem_spectrum_diagOp {lam : ι → ℝ} (k0 : ι) (hk0 : lam k0 = 1) :
    (1 : ℝ) ∈ spectrum ℝ (diagOp lam) := by
  rw [spectrum.mem_iff, map_one]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h0 := hu k0
  rw [Pi.sub_apply, Pi.one_apply] at h0
  simp only [diagOp, hk0, Complex.ofReal_one, sub_self] at h0
  exact not_isUnit_zero h0

/-- The `ℝ`-spectrum of `diagOp lam` is contained in `{1} ∪ Set.Icc ε ρ`, given that every index
outside the finite set `s` has `lam k = 1` and every index in `s` has `ε ≤ lam k ≤ ρ`.

`ε` and `ρ` are arbitrary reals bound outside both hypotheses: neither is required to be positive, and
`ε ≤ ρ` is not assumed — if the excited set is empty the interval clause is vacuous.

DERIVED: `1` is the vacuum eigenvalue, appearing as the value `hvac` assigns outside `s` and as the
isolated point of the containing set. It is the only numeral in the statement. -/
theorem spectrum_diagOp_subset {lam : ι → ℝ} (s : Finset ι) {ε ρ : ℝ}
    (hvac : ∀ k, k ∉ s → lam k = 1) (hexc : ∀ k ∈ s, ε ≤ lam k ∧ lam k ≤ ρ) :
    spectrum ℝ (diagOp lam) ⊆ {1} ∪ Set.Icc ε ρ := by
  intro r hr
  obtain ⟨k, rfl⟩ := mem_spectrum_diagOp hr
  by_cases hk : k ∈ s
  · exact Or.inr (Set.mem_Icc.mpr (hexc k hk))
  · exact Or.inl (Set.mem_singleton_iff.mpr (hvac k hk))

/-- A `GappedQuantumTheory (ι → ℂ)` built from diagonal spectral data and a decay bound, with gap `Δ`.

Inputs: real eigenvalues `lam` and weights `w` on a `Fintype` index `ι`, a finite excited set `s`, a
prefactor `M`, a floor `ε` with `0 < ε`, and a rate `Δ` with `0 < Δ`. The hypotheses are `hvac` (every
index outside `s` has eigenvalue `1`), `hvacpt` (at least one index lies outside `s`, so the vacuum is
actually present), `hεlam` (`ε ≤ lam k` on `s`), `hwnn` and `hwpos` (`0 ≤ w k` and `0 < w k` on `s`),
and `hdecay` (`∑_{k ∈ s} w k * lam k ^ τ ≤ M * (exp (-Δ)) ^ τ` for every `τ : ℕ`).

The spectral-support bound is computed, not supplied: `MomentSupport.le_of_positive_weight_decay` turns
`hdecay` plus strict positivity of the weights into `lam k ≤ exp (-Δ)` on `s`, and
`spectrum_diagOp_subset` assembles `spectrum ⊆ {1} ∪ Icc ε (exp (-Δ))` for `reconstruct_gapped`.

Scope: `M` is unconstrained — it need not be positive, because the pointwise bound is what the
moment-support lemma consumes. The construction is `noncomputable`.

DERIVED: `0` is the strict lower bound in `hε : 0 < ε`, `hΔ : 0 < Δ`, `hwnn : 0 ≤ w k` and
`hwpos : 0 < w k`. `1` is the vacuum eigenvalue that `hvac` assigns off the excited set. No other
numeral appears in the statement. -/
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

/-- The gap field of `gapped_of_positive_decay` is the rate `Δ` appearing in `hdecay`, by `rfl`.

The binders repeat those of `gapped_of_positive_decay`; nothing further is assumed.

DERIVED: `0` is the strict lower bound in `hε`, `hΔ`, `hwnn` and `hwpos`; `1` is the vacuum eigenvalue
assigned by `hvac`. Both reach the statement only through those repeated binders. -/
theorem gapped_of_positive_decay_gap [Fintype ι]
    (lam w : ι → ℝ) (s : Finset ι) (M ε Δ : ℝ)
    (hε : 0 < ε) (hΔ : 0 < Δ)
    (hvac : ∀ k, k ∉ s → lam k = 1) (hvacpt : ∃ k, k ∉ s)
    (hεlam : ∀ k ∈ s, ε ≤ lam k)
    (hwnn : ∀ k ∈ s, 0 ≤ w k) (hwpos : ∀ k ∈ s, 0 < w k)
    (hdecay : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * (Real.exp (-Δ)) ^ τ) :
    (gapped_of_positive_decay lam w s M ε Δ hε hΔ hvac hvacpt hεlam hwnn hwpos hdecay).gap = Δ := rfl

#print axioms gapped_of_positive_decay

/-- A four-mode instance of `gapped_of_positive_decay`: vacuum eigenvalue `1` at index `0`, and excited
eigenvalues `1/2, 1/4, 1/8` at indices `1, 2, 3`, each with weight `1`.

The arguments supplied are `M = 3`, `ε = 1/8` and `Δ = log 2`, so `exp (-Δ) = 1/2` and the decay
hypothesis is the inequality `∑_{k ∈ {1,2,3}} λ_k^τ ≤ 3·(1/2)^τ`, which holds termwise because each
excited eigenvalue is at most `1/2`. Two of the three excited eigenvalues are strictly below the bound,
so `MomentSupport.le_of_positive_weight_decay` is applied at a genuine inequality rather than at an
equality. The gap of the result is `log 2`.

DERIVED: `4` is the carrier dimension `Fin 4` — one vacuum index and three excited indices. It is the
only numeral in the statement; the eigenvalues, weights, `M`, `ε` and `Δ` are all arguments in the
term, not part of the type. -/
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

/-- The gap field of `multiModeGapped` is `Real.log 2`, by `rfl`.

DERIVED: `2` is the argument of the logarithm, fixed by `exp (-log 2) = 1/2` being the bound the four
eigenvalues of `multiModeGapped` were chosen against. It is the only numeral in the statement. -/
theorem multiModeGapped_gap : multiModeGapped.gap = Real.log 2 := rfl

#print axioms multiModeGapped

end MassGap.Reconstruction
