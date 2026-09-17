import MassGap.Aperture
import MassGap.Moment

/-!
# The transfer spectral form — what makes the modes a DEFINED object

**WHY THIS FILE EXISTS, stated as the defect it repairs.** `Complete.ym_mass_gap_of_junction` and
`ym_mass_gap_of_decay_at_floor` conclude that a correlator `τ ↦ ‖∑ₖ Pₖ mₖ^τ‖` tends to zero, from a
hypothesis bounding `‖mₖ‖`. Both quantify over an ARBITRARY family `m`, and `ymModel` instantiates it
at `Idx := Unit`, `P := 1`, `m := e^{−(κ₀−μ)}` — one number, defined equal to its own bound. So the
conclusion, read literally, is that a single complex number of modulus below one has powers tending
to zero, and the hypothesis is about a free parameter with no proved link to the Wilson measure.
`Apriori.hread_of_dominant` is `le_trans`; it does not supply that link, and nothing else does.

**WHAT THE LINK IS.** Reflection positivity gives the Wilson correlation the transfer-matrix form

    ρ(d) = Σₙ wₙ λₙ^d,    wₙ ≥ 0,   λₙ = e^{−Eₙ} ∈ [0, 1],

which is exactly the statement the `wilson_reflection_positive_at` docstring gives as its reason.
The AXIOM itself asserts only `0 ≤ ρ d` and `0 < ∑ ρ` — the consequence, not the form. That is the
gap: with the form, `P` and `m` are not free, they ARE `w` and `λ`, the correlator `∑ₖ Pₖ mₖ^τ` IS
`ρ(τ)`, and `‖mₖ‖ ≤ e^{−(κ₀−μ)}` IS the statement that every transfer energy clears `κ₀ − μ`.

**WHAT THIS FILE DOES AND DOES NOT DO.** It defines the form, proves that carrying it makes the
correlator the read's own `ρ` (`sum_eq_rho`), and derives clustering OF THAT CORRELATION from the
gap condition (`clustering_of_spectral`). It does NOT prove that the Wilson correlation has the form
— that is reflection positivity, and it stays open. What changes is that the open obligation is now
about a defined object: `SpectralForm` for `wilsonCorrAt`, rather than a bound on a free family.

**WHY THE FINITE-APERTURE FOURIER MODES ARE NOT THE ANSWER**, so that route is not tried again. A
read on a periodic aperture of `N+1` lags has `ρ(d) = Σ_j c_j e^{iθ_j d}` with `|e^{iθ_j}| = 1`; its
correlator is almost periodic and does NOT tend to zero, so it cannot satisfy the gap hypothesis. The
modes that can are the transfer spectrum, whose `λₙ` are strictly inside the disc. The two
decompositions are different objects and only the second carries a gap.

DERIVED: nothing here fixes a scale. `0` and `1` bound `λ` because it is `e^{−E}` with `E ≥ 0`;
`κ₀ − μ` is the counted free-energy density, already derived elsewhere.
-/

namespace MassGap.Spectral

open Finset

/-- **THE TRANSFER SPECTRAL FORM OF A CORRELATION.** A finite family of nonnegative weights `w` and
decay factors `λ ∈ [0, 1]` reproducing `ρ` at every lag the aperture resolves.

This is what reflection positivity is for: `wₙ ≥ 0` is the positivity of the transfer weights and
`λₙ = e^{−Eₙ}` their energies. Carrying it as a structure rather than an axiom means a theorem can
say which of its parts it uses. -/
structure SpectralForm (N : ℕ) (ρ : Fin (N + 1) → ℝ) where
  /-- The transfer spectrum's index. -/
  Idx : Type
  [fin : Fintype Idx]
  [dec : DecidableEq Idx]
  /-- The transfer weights `wₙ ≥ 0` — reflection positivity's content. -/
  w : Idx → ℝ
  /-- The per-lag decay factors `λₙ = e^{−Eₙ}`. -/
  lam : Idx → ℝ
  hw : ∀ n, 0 ≤ w n
  hlam0 : ∀ n, 0 ≤ lam n
  hlam1 : ∀ n, lam n ≤ 1
  /-- The form reproduces the correlation at every resolved lag. -/
  hrep : ∀ d : Fin (N + 1), ρ d = ∑ n, w n * (lam n) ^ (d : ℕ)

attribute [instance] SpectralForm.fin SpectralForm.dec

variable {N : ℕ} {ρ : Fin (N + 1) → ℝ}

/-- **THE CORRELATOR IS THE CORRELATION.** With the form in hand, the abstract object the gap
theorems are about — `∑ₙ Pₙ mₙ^τ` at `P := w`, `m := λ` — is the read's own `ρ` at that lag, not a
free family. This is the identification the flagship never had. -/
theorem sum_eq_rho (S : SpectralForm N ρ) (d : Fin (N + 1)) :
    ∑ n, S.w n * (S.lam n) ^ (d : ℕ) = ρ d := (S.hrep d).symm

/-- The same over `ℂ`, in the shape `Aperture.gap_of_confinement` consumes. -/
theorem sum_complex_eq_rho (S : SpectralForm N ρ) (d : Fin (N + 1)) :
    ∑ n, ((S.w n : ℂ)) * ((S.lam n : ℂ)) ^ (d : ℕ) = ((ρ d : ℝ) : ℂ) := by
  rw [← sum_eq_rho S d, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun n _ => by push_cast; ring)

/-- **CLUSTERING OF THE CORRELATION ITSELF, from the gap condition on the transfer spectrum.**

`Aperture.gap_of_confinement` instantiated at `P := w`, `m := λ` — but now those are the read's own
transfer data rather than a supplied family, so the conclusion is about `ρ` and the hypothesis
`hgap` is the statement that every transfer energy clears the counted free-energy density
`κ₀ − μ`. That IS the mass gap, said about a defined object. -/
theorem clustering_of_spectral (S : SpectralForm N ρ) {κ₀ μ : ℝ}
    (hconf : μ < κ₀) (hgap : ∀ n, S.lam n ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto
      (fun τ => ‖∑ n, ((S.w n : ℂ)) * ((S.lam n : ℂ)) ^ τ‖) Filter.atTop (nhds 0) := by
  refine MassGap.gap_of_confinement (Finset.univ : Finset S.Idx)
    (fun n => ((S.w n : ℂ))) (fun n => ((S.lam n : ℂ))) κ₀ μ hconf ?_
  intro n _
  rw [Complex.norm_real, Real.norm_of_nonneg (S.hlam0 n)]
  exact hgap n

#print axioms sum_eq_rho
#print axioms sum_complex_eq_rho
#print axioms clustering_of_spectral

/-- **THE GAP CONDITION, AS A STATEMENT ABOUT ENERGIES.** `λₙ ≤ e^{−(κ₀−μ)}` is `Eₙ ≥ κ₀ − μ` for
every transfer energy, which is what "the transfer gap is at least the counted free-energy density"
means. Stated so the two readings cannot drift apart. -/
theorem lam_le_iff_energy_ge {lam κ₀ μ : ℝ} (hlam : 0 < lam) :
    lam ≤ Real.exp (-(κ₀ - μ)) ↔ κ₀ - μ ≤ -Real.log lam := by
  constructor
  · intro h
    have hlog := Real.log_le_log hlam h
    rw [Real.log_exp] at hlog
    linarith
  · intro h
    have hlog : Real.log lam ≤ -(κ₀ - μ) := by linarith
    calc lam = Real.exp (Real.log lam) := (Real.exp_log hlam).symm
      _ ≤ Real.exp (-(κ₀ - μ)) := Real.exp_le_exp.mpr hlog

#print axioms lam_le_iff_energy_ge

end MassGap.Spectral
