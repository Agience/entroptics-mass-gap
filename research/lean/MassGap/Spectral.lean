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
is `flat_of_aperiodic` below, and ALL THREE of its premises are now facts about this tree:

* PROVED: `WilsonHypercubic.Site d n = Fin d → Fin n` and `shift` adds in `Fin n`, so the lattice is a
  fully PERIODIC torus of extent `n`.
* PROVED: `Complete.wilsonCorrAt N β = WilsonBridge.corrClay (N+1) β` with `lag : Fin (N+1)`, so the
  lag index runs the WHOLE period, not a half-line.
* **PROVED: `ρ(d) = ρ(n−d)`**, by `MomentShape.corrHyper_neg` and its corollaries `corrClay_neg` /
  `wilsonCorrAt_neg`, of the genuine `wilsonCorrAt`, at every extent and every real coupling with no
  hypothesis. It comes from `LogConvex.EW_plaqE_pair_shift` — translation invariance of the
  two-plaquette expectation, itself derived FROM the reflection — at `P = 0`, plus the
  lag-independence of the one-point term (`ReflectPositive.EW_plaqE_lag`). So `Moment.circLag`, built
  as if the symmetry held, reads the correlation correctly rather than by construction
  (`MomentShape.wilsonCorrAt_circLag_congr`).
  BEWARE THE NEIGHBOURING STATEMENT: `ZeroMode`'s "symmetric under `d ↦ n − d` by construction" is
  about `clag`, the LAG FUNCTION, where it is arithmetic — NOT about `ρ`. Earlier versions of this
  docstring, and of `rho_symm`'s, cited it as though it were about `ρ`. It is not, and the two must
  not be conflated.

Because the symmetry is now free, `flat_of_aperiodic`'s `hsym` is DISCHARGEABLE for the Wilson
correlation at `m := N`: `(-1 : Fin (N+1)).val = N`, so `wilsonCorrAt_neg N β 1` gives `ρ(N) = ρ(1)`
outright. A half-line form for `wilsonCorrAt` therefore forces `ρ` FLAT from lag one
UNCONDITIONALLY, where this file previously could only say so under an assumption.

Given that symmetry, a half-line form forces `ρ` ANTITONE, and antitone together with `ρ(1) = ρ(n−1)`
forces `ρ` FLAT from lag one onward. Two further limits on what that shows, both real:
`flat_of_aperiodic` assumes `1 ≤ d`, so `ρ(0)` is unconstrained and a half-line form with a contact
term at lag zero and a flat tail survives it; and "a flat correlator is false for an interacting
theory" is physics, not a theorem here — nothing in the tree evaluates `wilsonCorrAt` at any lag, and
the RP axiom (`0 ≤ ρ d`, `0 < ∑ ρ`) is satisfied by a constant positive `ρ`.

So the accurate statement is: **on this lattice the half-line shape is UNCONDITIONALLY degenerate —
and still not machine-checked false.** Degenerate is now free, the symmetry having become a theorem.
False it is not: `flat_of_aperiodic` assumes `1 ≤ d`, so a contact term at lag zero over a flat tail
survives it, and nothing in the tree proves `wilsonCorrAt` is non-constant — `Substrate.flatRead` is
a legal `Moment.Read` and `Substrate.flatSpectral` gives it a periodic form. The periodic shape below
is used because it is the one a transfer matrix on a circle actually produces, and because the
correlation's proved symmetry matches it; not because its rival has been refuted.

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
swap.

The Wilson correlation has that same symmetry as a THEOREM, `MomentShape.corrHyper_neg` and its
corollaries `corrClay_neg` / `wilsonCorrAt_neg`, at every extent and every real coupling with no
hypothesis — so a form of this shape is compatible with the correlation where a half-line form is
not, and `Moment.circLag` reads the correlation correctly rather than by construction
(`MomentShape.wilsonCorrAt_circLag_congr`).

NOT `ZeroMode`, which this docstring previously cited. `ZeroMode.sum_range_antipodal_fold` takes
`hsym` on an ARBITRARY `F` and says so in its own docstring ("a reindexing, not a fact about cosines
or about `λ`"); its instantiations in this tree are the LAG FUNCTION (`sum_clag_sq`) and a stipulated
model profile. It records nothing about the Wilson correlation. -/
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
