import MassGap.Aperture
import MassGap.Moment

/-!
# MassGap.Spectral — the two-term periodic spectral form, and what a half-line form forces

Two independent groups of results about finite sums `∑ₖ wₖ λₖ^d` over a `Fintype` index, with
`0 ≤ wₖ` and `λₖ ∈ [0, 1]`.

## The one-term (half-line) shape

`aperiodic_antitone` — a one-term sum `∑ₖ wₖ λₖ^d` is antitone in `d`, since each `λₖ ≤ 1`.
`flat_of_aperiodic` — if in addition the value at some `m` equals the value at `1`, then the sum is
constant on every `d` with `1 ≤ d ≤ m`. The hypothesis `1 ≤ d` leaves the value at `d = 0`
unconstrained. Both are statements about the sums themselves; neither mentions a lattice or a
correlation, and neither concludes that such a shape is impossible.

## The two-term (periodic) shape

`PeriodicSpectralForm n ρ` bundles a finite index type, weights `w`, factors `lam`, the three range
hypotheses, and `hrep : ρ d = ∑ₖ wₖ (λₖ^d + λₖ^{n−d})` for every `d : Fin n`. It is the shape a
transfer matrix on a circle of extent `n` produces, `Tr(A T^d A T^{n−d})/Tr(T^n)`. From it:

* `sum_eq_rho` — `hrep` read right-to-left;
* `rho_nonneg` — `0 ≤ ρ d` at every lag;
* `rho_symm` — `ρ e = ρ d` whenever `e = n − d`, from the two terms swapping;
* `periodic_decay_le` — given `r` bounding `lam k` wherever `w k ≠ 0`, and `2d ≤ n`, the bound
  `ρ d ≤ 2 (∑ₖ wₖ) r^d`. The hypothesis `2d ≤ n` restricts it to the near half of the period;
* `periodic_decay_le_circLag` — the same bound at every `d`, with exponent `min d (n − d)`, by
  reflecting the far half through `rho_symm`.

`r` is only required nonnegative, so these are geometric bounds in `r` and say nothing on their own
about decay unless a caller supplies `r < 1`. No statement here takes `n → ∞`.

DERIVED: nothing here fixes a scale. `0` and `1` bound `λ` as the range of `e^{−E}` with `E ≥ 0`; the
`2` in the decay bound is the number of terms of the periodic shape, not a magnitude.
-/

namespace MassGap.Spectral

open Finset

/-! ### The one-term shape -/

/-- A one-term sum `∑ₖ wₖ λₖ^d` is antitone in the exponent: with `0 ≤ w k`, `0 ≤ lam k` and
`lam k ≤ 1` for every `k`, and `d ≤ e`, the value at `e` is at most the value at `d`. Termwise, by
`pow_le_pow_of_le_one` and `mul_le_mul_of_nonneg_left`. The index type need only be a `Fintype`.

DERIVED: the two `0`s are the nonnegativity of the weights and of the factors, the first needed for
the termwise multiplication and the second for `pow_le_pow_of_le_one`; `1` is the ceiling on each
factor, which is what makes higher powers smaller. -/
theorem aperiodic_antitone {ι : Type*} [Fintype ι] (w lam : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hlam0 : ∀ k, 0 ≤ lam k) (hlam1 : ∀ k, lam k ≤ 1)
    {d e : ℕ} (hde : d ≤ e) :
    ∑ k, w k * (lam k) ^ e ≤ ∑ k, w k * (lam k) ^ d := by
  refine Finset.sum_le_sum (fun k _ => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (hlam0 k) (hlam1 k) hde) (hw k)

/-- A one-term sum that takes the same value at exponents `1` and `m` is constant on every exponent
between. Two applications of `aperiodic_antitone` sandwich the value at `d` between the values at `1`
and at `m`, and `hsym` identifies those two; `le_antisymm` closes it.

The conclusion is an equality of sums on `1 ≤ d ≤ m`. The exponent `0` is excluded by `h1d`, so a
sum whose value at `0` differs from a constant tail satisfies every hypothesis here. Nothing in the
statement rules the one-term shape out.

DERIVED: the two `0`s are the nonnegativity of the weights and of the factors; `1` in `hlam1` is the
ceiling on each factor; the `1`s in `hsym`, `h1d` and the conclusion are the same base exponent, the
one the sandwich is anchored at, and `h1d` is what excludes exponent `0`. -/
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

/-- A witness that `ρ : Fin n → ℝ` has the two-term periodic spectral shape. It carries a `Fintype`
index `Idx`, weights `w : Idx → ℝ`, factors `lam : Idx → ℝ`, the three range hypotheses `0 ≤ w k`,
`0 ≤ lam k`, `lam k ≤ 1`, and `hrep`, which states `ρ d = ∑ₖ wₖ (λₖ^d + λₖ^{n−d})` at every
`d : Fin n`.

This is the shape a transfer matrix on a circle of extent `n` gives,
`Tr(A T^d A T^{n−d})/Tr(T^n)`. `lam k ≤ 1` is contractivity — a normalisation, not a gap; the gap is
supplied separately as the `hgap` hypothesis of `periodic_decay_le`. The structure has no field
relating distinct `lam k`, so nothing here forces the factors apart.

DERIVED: `0` in `hw` is the floor on the weights and `0` in `hlam0` the floor on the factors; `1` in
`hlam1` is the ceiling on the factors, the range of `e^{−E}` for `E ≥ 0`. -/
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

/-- `hrep` read right-to-left: the two-term sum equals `ρ d` at every `d : Fin n`.

DERIVED: no numeral. -/
theorem sum_eq_rho (S : PeriodicSpectralForm n ρ) (d : Fin n) :
    ∑ k, S.w k * ((S.lam k) ^ (d : ℕ) + (S.lam k) ^ (n - (d : ℕ))) = ρ d := (S.hrep d).symm

/-- `0 ≤ ρ d` at every `d : Fin n`, for any `ρ` carrying a `PeriodicSpectralForm`. Each summand is a
nonnegative weight times a sum of two nonnegative powers.

DERIVED: `0` is the lower bound, inherited from `hw` and `hlam0`. -/
theorem rho_nonneg (S : PeriodicSpectralForm n ρ) (d : Fin n) : 0 ≤ ρ d := by
  rw [← sum_eq_rho S d]
  refine Finset.sum_nonneg (fun k _ => mul_nonneg (S.hw k) ?_)
  exact add_nonneg (pow_nonneg (S.hlam0 k) _) (pow_nonneg (S.hlam0 k) _)

/-- With `r` bounding `lam k` at every `k` whose weight is nonzero, `0 ≤ r`, and a lag in the near
half of the period (`2d ≤ n`), `ρ d ≤ 2 (∑ₖ wₖ) r^d`. At such a `d` the far exponent `n − d` is at
least `d`, so the far term is at most the near one; both are then bounded by `r^d`.

Stated on `2d ≤ n` only, and `r` is required merely nonnegative: the bound is geometric in `r`, and
a caller wanting decay must supply `r < 1`. `periodic_decay_le_circLag` extends it to every lag with
the exponent `min d (n − d)`.

DERIVED: `0` in `hgap` selects the weights the bound must cover, and `0` in `hr` is the floor `r`
needs for `r^d` to be nonnegative; `2` in `hhalf` marks the near half of the period, and `2` on the
right is the number of terms in the periodic shape, each bounded by `wₖ r^d`. -/
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

/-- `ρ e = ρ d` whenever `(e : ℕ) = n − d` and `d ≤ n`: the periodic form is symmetric under
`d ↦ n − d`. The two terms `λ^d` and `λ^{n−d}` exchange, using `n − (n − d) = d`, which is where
`hdn` is needed. It follows from the structure's own shape and assumes nothing about `ρ` beyond
carrying a `PeriodicSpectralForm`.

DERIVED: no numeral. -/
theorem rho_symm (S : PeriodicSpectralForm n ρ) (d e : Fin n)
    (hde : (e : ℕ) = n - (d : ℕ)) (hdn : (d : ℕ) ≤ n) : ρ e = ρ d := by
  rw [← sum_eq_rho S e, ← sum_eq_rho S d, hde]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : n - (n - (d : ℕ)) = (d : ℕ) := by omega
  rw [this]
  ring

/-- `periodic_decay_le` extended to every lag: `ρ d ≤ 2 (∑ₖ wₖ) r^(min d (n − d))`. On the near half
this is `periodic_decay_le` with `min d (n − d) = d`; on the far half the lag is reflected through
`rho_symm` and the near bound applied at `n − d`. The exponent `min d (n − d)` is the circle
distance. As in `periodic_decay_le`, `r` is only required nonnegative.

DERIVED: `0` in `hgap` selects the weights the bound must cover and `0` in `hr` is the floor on `r`;
`2` is the number of terms in the periodic shape. -/
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
