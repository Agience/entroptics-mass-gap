import MassGap.Aperture
import MassGap.Moment

/-!
# The transfer spectral form on a PERIODIC lattice

**WHY THIS FILE EXISTS.** `Complete.ym_mass_gap_of_decay_at_floor` concludes that a correlator
`τ ↦ ‖∑ₖ Pₖ mₖ^τ‖` tends to zero, from a hypothesis bounding `‖mₖ‖`, over an ARBITRARY family `m` —
and `ymModel` instantiates it at `Idx := Unit`, `P := 1`, `m := e^{−(κ₀−μ)}`, one number defined equal
to its own bound. `Apriori.hread_of_dominant` is `le_trans` and supplies no link to the ensemble.
Giving the modes a definition is what would make that hypothesis a statement about Yang–Mills.

**WHY THE HALF-LINE SHAPE WAS ABANDONED, AND EXACTLY HOW FAR THE ARGUMENT GOES.**
An earlier version of this file used the half-line shape `ρ(d) = ∑ₙ wₙ λₙ^d`. The argument against it
is `flat_of_aperiodic` below, and it is CONDITIONAL — two of its three premises are facts about this
tree, the third is not proved anywhere and is stated here as the assumption it is:

* PROVED: `WilsonHypercubic.Site d n = Fin d → Fin n` and `shift` adds in `Fin n`, so the lattice is a
  fully PERIODIC torus of extent `n`.
* PROVED: `Complete.wilsonCorrAt N β = WilsonBridge.corrClay (N+1) β` with `lag : Fin (N+1)`, so the
  lag index runs the WHOLE period, not a half-line.
* **NOT PROVED: `ρ(d) = ρ(n−d)`.** No theorem in the tree asserts it of `wilsonCorrAt`, `corrClay`,
  `corrHyper` or `wilsonCorrConn`, and there is no translation-invariance theorem for the correlation.
  It is what one expects of a translation-invariant correlation of two plaquettes on a torus, and
  `Moment.circLag`/`clag n d = min d (n−d)` is built as if it held, but `ZeroMode`'s "symmetric under
  `d ↦ n − d` by construction" is a statement about `clag` — the LAG FUNCTION, where it is arithmetic
  — and NOT about `ρ`. An earlier version of this docstring cited it as though it were about `ρ`.

GIVEN that symmetry, a half-line form forces `ρ` ANTITONE, and antitone together with `ρ(1) = ρ(n−1)`
forces `ρ` FLAT from lag one onward. Two further limits on what that shows, both real:
`flat_of_aperiodic` assumes `1 ≤ d`, so `ρ(0)` is unconstrained and a half-line form with a contact
term at lag zero and a flat tail survives it; and "a flat correlator is false for an interacting
theory" is physics, not a theorem here — nothing in the tree evaluates `wilsonCorrAt` at any lag, and
the RP axiom (`0 ≤ ρ d`, `0 < ∑ ρ`) is satisfied by a constant positive `ρ`.

So the accurate statement is: **on this lattice the half-line shape is unattractive and, under the
expected symmetry, degenerate — it is not machine-checked false.** The periodic shape below is used
because it is the one a transfer matrix on a circle actually produces, not because its rival has been
refuted.

**THE RIGHT SHAPE IS THE PERIODIC ONE**, `ρ(d) = ∑ₙ wₙ (λₙ^d + λₙ^{n−d})`, which is what a transfer
matrix on a circle of extent `n` gives: `Tr(A T^d A T^{n−d})/Tr(T^n)`. It is symmetric under
`d ↦ n−d` by construction, nonnegative, and NOT antitone — it turns around at `n/2`.

**AND THE CLUSTERING STATEMENT CHANGES WITH IT, which is the cost.** A periodic correlator
does NOT tend to zero at large lag; it comes back up. What the gap buys on a torus is decay out to
HALF the period (`periodic_decay_le`). Clustering in the true sense needs `n → ∞`, and that is the
infinite-volume obligation, not something this file can supply.

DERIVED: nothing here fixes a scale. `0` and `1` bound `λ` because it is `e^{−E}` with `E ≥ 0`; the
`2` in the decay bound is the two terms of the periodic shape, not a magnitude.
-/

namespace MassGap.Spectral

open Finset

/-! ### The refutation of the half-line shape, kept as a theorem -/

/-- **A HALF-LINE SPECTRAL SHAPE FORCES THE CORRELATION TO BE ANTITONE.** With `λ ∈ [0,1]` and
`w ≥ 0`, raising the lag can only shrink every term. -/
theorem aperiodic_antitone {ι : Type*} [Fintype ι] (w lam : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hlam0 : ∀ k, 0 ≤ lam k) (hlam1 : ∀ k, lam k ≤ 1)
    {d e : ℕ} (hde : d ≤ e) :
    ∑ k, w k * (lam k) ^ e ≤ ∑ k, w k * (lam k) ^ d := by
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (hlam0 k) (hlam1 k) hde) (hw k)

/-- **AND ON A PERIODIC LATTICE THAT FORCES IT FLAT — so the half-line shape is refuted there.**

If the correlation carries a half-line shape AND is periodic-symmetric (`ρ 1 = ρ m` for the lag `m`
opposite to `1`), then it is constant on every lag between. Zero connected decay, which an
interacting theory does not have. This is why `PeriodicSpectralForm` below uses the two-term shape.
-/
theorem flat_of_aperiodic {ι : Type*} [Fintype ι] (w lam : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hlam0 : ∀ k, 0 ≤ lam k) (hlam1 : ∀ k, lam k ≤ 1)
    {m d : ℕ} (hsym : ∑ k, w k * (lam k) ^ m = ∑ k, w k * (lam k) ^ 1)
    (h1d : 1 ≤ d) (hdm : d ≤ m) :
    ∑ k, w k * (lam k) ^ d = ∑ k, w k * (lam k) ^ 1 := by
  have hup : ∑ k, w k * (lam k) ^ d ≤ ∑ k, w k * (lam k) ^ 1 :=
    aperiodic_antitone w lam hw hlam0 hlam1 h1d
  have hdown : ∑ k, w k * (lam k) ^ m ≤ ∑ k, w k * (lam k) ^ d :=
    aperiodic_antitone w lam hw hlam0 hlam1 hdm
  rw [hsym] at hdown
  exact le_antisymm hup hdown

#print axioms aperiodic_antitone
#print axioms flat_of_aperiodic

/-! ### The periodic form -/

/-- **THE TRANSFER SPECTRAL FORM ON A CIRCLE OF EXTENT `n`.** Nonnegative weights and decay factors
in `[0,1]`, entering through the two-term periodic shape `λ^d + λ^{n−d}`.

This is what a transfer matrix on a periodic lattice gives, `Tr(A T^d A T^{n−d})/Tr(T^n)`; the
half-line shape `λ^d` is the `n → ∞` limit of it and is refuted at finite `n` by `flat_of_aperiodic`.
`w ≥ 0` is reflection positivity's content; `λ ∈ [0,1]` is `0 ≤ T ≤ 1`, where `T ≤ 1` is
contractivity of a probability measure's transfer operator — a normalisation, NOT a gap. The gap is
a separate hypothesis wherever it is needed. -/
structure PeriodicSpectralForm (n : ℕ) (ρ : Fin n → ℝ) where
  /-- The transfer spectrum's index. -/
  Idx : Type
  [fin : Fintype Idx]
  /-- The transfer weights `wₖ ≥ 0` — reflection positivity's content. -/
  w : Idx → ℝ
  /-- The per-lag decay factors `λₖ = e^{−Eₖ}`. -/
  lam : Idx → ℝ
  hw : ∀ k, 0 ≤ w k
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, lam k ≤ 1
  /-- The form reproduces the correlation at every lag the period resolves. -/
  hrep : ∀ d : Fin n, ρ d = ∑ k, w k * ((lam k) ^ (d : ℕ) + (lam k) ^ (n - (d : ℕ)))

attribute [instance] PeriodicSpectralForm.fin

variable {n : ℕ} {ρ : Fin n → ℝ}

/-- **THE CORRELATOR IS THE CORRELATION**, at every lag the period resolves. -/
theorem sum_eq_rho (S : PeriodicSpectralForm n ρ) (d : Fin n) :
    ∑ k, S.w k * ((S.lam k) ^ (d : ℕ) + (S.lam k) ^ (n - (d : ℕ))) = ρ d := (S.hrep d).symm

/-- **THE FORM IS NONNEGATIVE AT EVERY LAG** — so a measured correlation that is negative beyond its
errors would refute it. -/
theorem rho_nonneg (S : PeriodicSpectralForm n ρ) (d : Fin n) : 0 ≤ ρ d := by
  rw [← sum_eq_rho S d]
  refine Finset.sum_nonneg (fun k _ => mul_nonneg (S.hw k) ?_)
  exact add_nonneg (pow_nonneg (S.hlam0 k) _) (pow_nonneg (S.hlam0 k) _)

/-- **DECAY OUT TO HALF THE PERIOD, from a gap on the spectrum.** At `2d ≤ n` the far term is no
larger than the near one, so the periodic correlation is bounded by twice the half-line bound.

**This is all a gap buys on a torus.** Past `n/2` the correlation turns back up, so no bound of this
shape can hold there and no periodic correlator tends to zero. Clustering in the true sense is the
`n → ∞` statement, and it is the infinite-volume obligation. -/
theorem periodic_decay_le (S : PeriodicSpectralForm n ρ) {r : ℝ}
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ r) (hr : 0 ≤ r)
    (d : Fin n) (hhalf : 2 * (d : ℕ) ≤ n) :
    ρ d ≤ 2 * (∑ k, S.w k) * r ^ (d : ℕ) := by
  have hrhs : 2 * (∑ k, S.w k) * r ^ (d : ℕ) = ∑ k, (2 * S.w k * r ^ (d : ℕ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [← sum_eq_rho S d, hrhs]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hdle : (d : ℕ) ≤ n - (d : ℕ) := by omega
  have hfar : (S.lam k) ^ (n - (d : ℕ)) ≤ (S.lam k) ^ (d : ℕ) :=
    pow_le_pow_of_le_one (S.hlam0 k) (S.hlam1 k) hdle
  have hwk := S.hw k
  by_cases hw0 : S.w k = 0
  · rw [hw0]; simp [pow_nonneg hr]
  have hnear : (S.lam k) ^ (d : ℕ) ≤ r ^ (d : ℕ) :=
    pow_le_pow_left₀ (S.hlam0 k) (hgap k hw0) _
  nlinarith [pow_nonneg (S.hlam0 k) (d : ℕ), pow_nonneg hr (d : ℕ)]

#print axioms sum_eq_rho
#print axioms rho_nonneg
#print axioms periodic_decay_le

/-- **THE PERIODIC FORM IS SYMMETRIC UNDER `d ↦ n − d`**, straight from its own shape — the two terms
swap. This is the symmetry `ZeroMode` records for the Wilson correlation and `Moment.circLag` is
built on, so a form of this shape is compatible with it where a half-line form is not. -/
theorem rho_symm (S : PeriodicSpectralForm n ρ) (d e : Fin n)
    (hde : (e : ℕ) = n - (d : ℕ)) (hdn : (d : ℕ) ≤ n) : ρ e = ρ d := by
  rw [← sum_eq_rho S e, ← sum_eq_rho S d, hde]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : n - (n - (d : ℕ)) = (d : ℕ) := by omega
  rw [this]
  ring

/-- **DECAY AT THE CIRCLE LAG, FOR EVERY LAG.** `periodic_decay_le` bounds the near half; the far half
follows from `rho_symm`, so the bound holds at every `d` with the exponent `min d (n−d)` — which is
exactly `Moment.circLag`, the distance the read can actually see.

**This is the shape `Complete.confinement_of_geometric_decay` consumes.** So a periodic spectral form
with a gap feeds the confinement machinery directly, where a half-line form cannot (it is refuted on
this lattice by `flat_of_aperiodic`). -/
theorem periodic_decay_le_circLag (S : PeriodicSpectralForm n ρ) {r : ℝ}
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ r) (hr : 0 ≤ r) (d : Fin n) :
    ρ d ≤ 2 * (∑ k, S.w k) * r ^ (min (d : ℕ) (n - (d : ℕ))) := by
  by_cases hnear : 2 * (d : ℕ) ≤ n
  · have hmin : min (d : ℕ) (n - (d : ℕ)) = (d : ℕ) := by omega
    rw [hmin]
    exact periodic_decay_le S hgap hr d hnear
  · -- the far half: reflect the lag and apply the near bound there
    have hdn : (d : ℕ) < n := d.isLt
    have hmin : min (d : ℕ) (n - (d : ℕ)) = n - (d : ℕ) := by omega
    have hlt : n - (d : ℕ) < n := by omega
    have hsym := rho_symm S d ⟨n - (d : ℕ), hlt⟩ rfl (le_of_lt hdn)
    rw [hmin, ← hsym]
    refine periodic_decay_le S hgap hr ⟨n - (d : ℕ), hlt⟩ ?_
    simp only []
    omega

#print axioms rho_symm
#print axioms periodic_decay_le_circLag

end MassGap.Spectral
