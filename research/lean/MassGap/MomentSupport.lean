import Mathlib

/-!
# Moment-support lemma — the `C(τ)→0` ⟹ spectral-support bridge (finite-dim core, PAPER §11/§13)

Closes the reduction-core gap: it connects the PROVED decay of the connected correlator to the transfer
operator's spectral-support bound `hsp` (the hypothesis `Complete.ym_reconstructed_gap` currently assumes).

Reflection positivity (Osterwalder–Seiler) gives a self-adjoint transfer operator `T`, `0 ≤ T ≤ 1`, on the
finite-volume physical Hilbert space, and the connected correlator is a **positive-weight** exponential sum
`C_conn(τ) = ∑_k w_k λ_k^τ` with `w_k = |⟨v, e_k⟩|² ≥ 0` and `λ_k ∈ [0,1)` the excited transfer eigenvalues.
The proof already delivers `C_conn(τ) ≤ M ρ^τ` with `ρ = e^{-Δ} < 1`.

This file proves the elementary, load-bearing step: **a positive-weight exponential sum bounded by a decaying
total forces every weighted mode below the decay rate.** Positivity of the weights is essential — it makes each
term a lower bound on the sum. With `ρ = e^{-Δ}` this places every excited eigenvalue carrying nonzero overlap
in `[0, e^{-Δ}]`, the support half of `hsp`.
-/

namespace MassGap

open Finset Filter

/-- **Moment-support lemma (positive-weight core).** If `∑_{k∈s} w_k λ_k^τ ≤ M ρ^τ` for every `τ ∈ ℕ`, with
`w_k ≥ 0`, `λ_k ≥ 0`, `ρ > 0`, then every mode carrying positive weight sits at or below the decay rate:
`w_k > 0 ⟹ λ_k ≤ ρ`. (Reflection positivity supplies `w_k ≥ 0`; the proof supplies the decaying bound.) -/
theorem le_of_positive_weight_decay {ι : Type*} (s : Finset ι) (w lam : ι → ℝ) (M ρ : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hρ : 0 < ρ)
    (hbound : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * ρ ^ τ) :
    ∀ k ∈ s, 0 < w k → lam k ≤ ρ := by
  intro k hk hwk
  by_contra hcon
  rw [not_le] at hcon                               -- `hcon : ρ < lam k`
  -- Each single term is ≤ the whole (nonnegative) sum ≤ `M ρ^τ`.
  have key : ∀ τ : ℕ, w k * lam k ^ τ ≤ M * ρ ^ τ := fun τ =>
    le_trans (single_le_sum (fun i hi => mul_nonneg (hw i hi) (pow_nonneg (hlam i hi) τ)) hk) (hbound τ)
  set r := lam k / ρ with hrdef
  have hne : ρ ≠ 0 := ne_of_gt hρ
  have hr1 : 1 < r := by rw [hrdef]; rw [lt_div_iff₀ hρ, one_mul]; exact hcon
  have hrρ : r * ρ = lam k := by rw [hrdef]; field_simp
  -- `w k * r^τ ≤ M` for every `τ`: divide the moment bound by `ρ^τ > 0`.
  have hbdd : ∀ τ : ℕ, w k * r ^ τ ≤ M := by
    intro τ
    have hρτ : (0 : ℝ) < ρ ^ τ := pow_pos hρ τ
    have hlk : r ^ τ * ρ ^ τ = lam k ^ τ := by rw [← mul_pow, hrρ]
    have h1 : (w k * r ^ τ) * ρ ^ τ ≤ M * ρ ^ τ := by
      rw [mul_assoc, hlk]; exact key τ
    exact le_of_mul_le_mul_right h1 hρτ
  -- But `r > 1` makes `r^τ` unbounded, so `w k * r^τ` cannot stay `≤ M`.
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_gt_atTop (M / w k)).exists
  rw [div_lt_iff₀ hwk] at hn                          -- `hn : M < r^n * w k`
  have hle := hbdd n                                   -- `hle : w k * r^n ≤ M`
  rw [mul_comm] at hle                                 -- `hle : r^n * w k ≤ M`
  linarith [hn, hle]

/-- **Assembling `hsp` (interface).** `le_of_positive_weight_decay` gives the spectral bound *as seen by the
observable* `v`: every excited eigenvalue with `⟨v,e_k⟩ ≠ 0` is `≤ ρ = e^{-Δ}`. To lift "seen by `v`" to a
statement about `T` itself (`spectrum ⊆ {1} ∪ [ε, e^{-Δ}]`, the `ym_reconstructed_gap` input) the honest
assembly needs three companion facts (independently reviewed):
* **R1 (cyclicity/totality — load-bearing).** The decay bound holds for a family `{v_a}` total in `Ω^⊥`
  (equivalently every excited `e_k` has nonzero overlap with some `v_a`). This closes the zero-overlap hole — a
  single correlator can *overestimate* the gap — and in particular covers the slowest excited mode. Reeh–Schlieder
  / vacuum-cyclicity for the local algebra supplies it.
* **R3 (vacuum eigenspace).** The subtracted vacuum is exactly the full `λ=1` eigenspace `Ω` (the decay itself
  forces `v`'s connected part `⊥ Ω`). With `ρ<1` this gives isolation (no spectrum in `(ρ,1)`) — the gap. Vacuum
  *simplicity* (`dim Ω = 1`) is an extra input (Perron–Frobenius/clustering), needed only if a *unique* vacuum is
  claimed, not for `H ≥ Δ` on `Ω^⊥`.
* **R2 (ε>0) — optional.** Needed only if the assembly routes through `H = -log T` via CFC (log is discontinuous
  at 0); then `ε = λ_min > 0` comes from strict positivity `T = e^{-aH_latt} > 0` (bounded action), NOT from the
  decay. Otherwise drop `ε` and target `{1} ∪ [0, ρ]`, i.e. the norm bound `‖T|_{Ω^⊥}‖ ≤ ρ`, which is all the gap needs.

Setting check: `τ` must range over `ℕ` (the OS/GNS half-infinite reconstructed time — finite spatial volume, time
unbounded), NOT a finite time-torus (where `C(τ)` is a KMS trace and the clean `∑ w_k λ_k^τ` at unbounded `τ` is
unavailable). Continuum limit: the finite-dim lemma is the correct per-volume target; the measure-theoretic port
`∫ λ^τ dμ_v ≤ Mρ^τ ⟹ supp μ_v ⊆ [0,ρ]` is a straightforward re-run, and volume/spacing UNIFORMITY of `(M,ρ)` is
the separate obligation of the estimates / existence half. -/
example {ι : Type*} (s : Finset ι) (w lam : ι → ℝ) (M ρ : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hρ : 0 < ρ)
    (hbound : ∀ τ : ℕ, (∑ k ∈ s, w k * lam k ^ τ) ≤ M * ρ ^ τ)
    (k : ι) (hk : k ∈ s) (hwk : 0 < w k) : lam k ≤ ρ :=
  le_of_positive_weight_decay s w lam M ρ hw hlam hρ hbound k hk hwk

end MassGap
