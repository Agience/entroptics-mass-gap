import Mathlib
import MassGap.Complete
import MassGap.Spectral2
import MassGap.TailRatio

/-!
# MassGap.SpectralFour — the extent-four representable region, exactly

`Complete.WilsonSpectral N β` is `Nonempty (Spectral.PeriodicSpectralForm (N+1) (wilsonCorrAt N β))`.
At the Clay aperture `N = 3` the period is four, and `PeriodicSpectralForm.hrep` unfolds to three
independent equations in the three numbers `ρ(0), ρ(1), ρ(2)` (lag three repeats lag one, since
`4 − 3 = 1` and `4 − 1 = 3`):

    ρ(0) = ∑ₖ wₖ (1 + λₖ⁴),   ρ(1) = ∑ₖ wₖ (λₖ + λₖ³),   ρ(2) = ∑ₖ wₖ · 2λₖ².

So at this extent the object is not a spectral decomposition of an operator — it is a finite conic
representation of a triple, and the question is purely whether the triple lies in the cone generated
by the curve `λ ↦ (1 + λ⁴, λ + λ³, 2λ²)`.

## The characterisation

`four_iff`: a form exists for `ρ : Fin 4 → ℝ` exactly when `ρ 3 = ρ 1` and

    0 ≤ ρ(0),   0 ≤ ρ(2),   ρ(2) ≤ ρ(1),   2·ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2).

That is `FourRepresentable`. Necessity is two pointwise facts and one Cauchy–Schwarz; sufficiency is
an explicit TWO-mode witness, one mode at `λ = 0` carrying the contact term and one at
`λ = c − √(c²−1)` with `c = ρ(1)/ρ(2)`, so two modes always suffice and the third free parameter is
never needed. `Nonempty` is therefore decided by a semialgebraic condition on the triple.

Three structural readings of that region, all machine-checked here:

* **The two-term ansatz is not the obstruction.** `fourRepresentable_of_pairs` proves that every
  finite transfer-matrix periodic correlator lands in the region:
  `Tr(A Tᵈ A T⁴⁻ᵈ) = ∑ᵢⱼ |Aᵢⱼ|² λᵢᵈ λⱼ⁴⁻ᵈ`, one term `c (aᵈ b⁴⁻ᵈ + bᵈ a⁴⁻ᵈ)` per unordered pair, and
  each such pair lands exactly ON the boundary surface `2ρ₁² = ρ₂² + ρ₀ρ₂` — at the ray the
  one-parameter curve reaches at `λ = a/b`. So `FourRepresentable` is what "this triple came from a
  finite transfer matrix" says about three numbers, and the missing inequalities are that content and
  no more.

* **`λ ≤ 1` is INERT at this extent.** `fourRepresentable_of_sums` proves the necessary conditions
  from `0 ≤ w` and `0 ≤ λ` ALONE, and `nonempty_of_fourRepresentable` produces a witness that does
  satisfy `λ ≤ 1`. So dropping the upper bound enlarges nothing (`unit_bound_inert`). The reason is
  that the triple depends on `λ` only through `λ + 1/λ`, which is invariant under `λ ↦ 1/λ`. The
  binding constraints are `w ≥ 0` and `λ ≥ 0`.
* **The region is strictly inside log-convexity.** `fourRepresentable_le` derives
  `ρ(2) ≤ ρ(1) ≤ ρ(0)` and `ρ(1)² ≤ ρ(0)·ρ(2)` from `FourRepresentable`, so the representable region
  implies every field of `TailRatio.TripleFacts` except the strictness `0 < ρ(0)` and the uniform
  bound `≤ 4`, neither of which is a shape fact — and the converse fails.

## What this does NOT establish, stated because it is the point

The tree does not prove `FourRepresentable` of the Wilson triple, and the gap is exact rather than
technical. `TailRatio.TripleFacts` collects the tree's shape facts about `(ρ0, ρ1, ρ2)` at extent
four — `TailRatio.triple_wilsonCorrAt` proves it of the Wilson triple at every `0 ≤ β`, citing
`PlaqVariance.corrClay_zero_pos`, `Complete.wilson_reflection_positive_at_even`,
`ReflectionStrong.corrClay_nonneg_even_lag`, `LogConvex.corrClay_log_convex_at_extent_four` and
`InfiniteVolume.wilsonCorrAt_abs_le_four` — and `tripleFacts_not_ordered` / `tripleFacts_not_quadratic` exhibit
conforming triples that are NOT representable — one violating `ρ(2) ≤ ρ(1)`, one violating the
quadratic. Neither missing inequality follows from the other
(`missing_inequalities_independent`), so both are open.

Neither is reachable by strengthening the positivity input either. `circle_psd_not_sufficient` shows
both witnesses are positive-definite as functions on `ℤ₄` — strictly more than the tree proves — and
`ordered_is_what_nonneg_lam_buys` identifies why: `(4, 0, 4)` IS a periodic spectral form at
`λ = (1, −1)`, failing only `hlam0 : 0 ≤ lam`. So `ρ(2) ≤ ρ(1)` is the positivity of the transfer
spectrum, not an estimate on a correlation.

`WilsonFourRepresentable β` names exactly that residue, and `wilsonSpectral_of_representable` is the
conditional: it is the only hypothesis `WilsonSpectral 3 β` needs at this extent. **IT IS NOW
DISCHARGED**, at every `0 ≤ β`, by `LinkGram.wilson_lag_two_le_lag_one` and
`SlabQuadratic.wilson_quadratic`, and `SlabQuadratic.wilsonSpectral` is the composite. What produces
it — and the answer is reflection positivity, exactly as the analysis below predicts:

* `ρ(2) ≤ ρ(1)` is antitonicity of the correlation across ONE lag step, from an even lag to the odd
  lag below it. The tree's two antitonicity results are both the wrong shape for it as well as
  unavailable at this extent: `MomentShape.corrClay_even_antitone` carries `hm3 : 3 ≤ m` and compares
  `ev Nap c₂` with `ev Nap c₁`, i.e. EVEN lags only, so it never relates lag two to lag one;
  `WeakArm.corrClay_le_at_zero` carries the same `3 ≤ m` and bounds every lag by lag ZERO, which is
  `ρ(2) ≤ ρ(0)`, not this. The half-extent here is `m = 2`, so neither applies in any case.
  `TailRatio.no_lag_two_bound_from_triple` closes the remaining direction: the proved set bounds
  `ρ(2)/ρ(0)` by no constant at all, so it cannot deliver an upper bound on `ρ(2)` either.
* `2ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2)` is the Cauchy–Schwarz pairing of the lag-one vector against the
  lag-zero-plus-lag-two vector, which is what a transfer operator supplies for free and what
  reflection positivity at this extent does not: `TripleFacts`'s log-convexity is the `2 × 2` minor
  `ρ(1)² ≤ ρ(0)·ρ(2)`, and the required inequality is strictly stronger wherever `ρ(2) < ρ(0)`.

Neither is a threshold and neither carries a constant, so neither is B5's inequality and this file
does not attempt it — `TailRatio.no_lag_two_bound_from_triple` already settles that the shape facts
bound no ratio, and `FourRepresentable` bounds none either: it is satisfied by the constant triple
`(c, c, c)` at every `c ≥ 0` (`fourRepresentable_const`), where `ρ(2)/ρ(0) = 1`.

Build: `python research/code/lean_build.py build MassGap.SpectralFour`.
-/

namespace MassGap.SpectralFour

open MassGap

/-! ## 0. Lag indices at extent four

DERIVED: `0`, `1`, `2`, `3` are the four lag indices of `Fin 4` and `4` is the period, which is
`N + 1` at the Clay aperture `N = 3`. No numeral in this section is a value. -/

private lemma val0 : ((0 : Fin 4) : ℕ) = 0 := rfl
private lemma val1 : ((1 : Fin 4) : ℕ) = 1 := rfl
private lemma val2 : ((2 : Fin 4) : ℕ) = 2 := rfl
private lemma val3 : ((3 : Fin 4) : ℕ) = 3 := rfl

/-! ## 1. The region -/

/-- **THE REPRESENTABLE REGION AT EXTENT FOUR.**

Exactly the triples `(ρ0, ρ1, ρ2)` for which a `Spectral.PeriodicSpectralForm 4` exists — necessary
by `fourRepresentable_of_form` and sufficient by `nonempty_of_fourRepresentable`, so `four_iff` is
an equivalence and not a one-way sufficient condition.

Geometrically it is the convex cone on the curve `λ ↦ (1 + λ⁴, λ + λ³, 2λ²)`. In the normalised
coordinates `x = ρ1/ρ0`, `y = ρ2/ρ0` that curve is the arc `2x² = y² + y` from `(0,0)` to `(1,1)`,
which AS A FUNCTION OF `x` is `y = (√(1 + 8x²) − 1)/2`, convex. So the arc lies below the chord
`y = x` and the hull of the two is the region between them — the chord giving `ρ2 ≤ ρ1` and the arc
giving `2ρ1² ≤ ρ2² + ρ0·ρ2`. (Read the other way round, `x` as a function of `y`, the same arc is
concave; it is the region that is convex, and which variable is named matters for the word.)

DERIVED: `2` is the number of terms in `λ^d + λ^{n−d}` at the self-paired lag `d = 2`, where
`4 − 2 = 2`; it is the shape's own multiplicity, not a level. `0` is a sign and the exponent `2` is a
square. No magnitude is chosen and no threshold appears. -/
def FourRepresentable (r₀ r₁ r₂ : ℝ) : Prop :=
  0 ≤ r₀ ∧ 0 ≤ r₂ ∧ r₂ ≤ r₁ ∧ 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂

/-- **THE REGION IS ORDERED AND LOG-CONVEX.** `ρ(2) ≤ ρ(1) ≤ ρ(0)` and `ρ(1)² ≤ ρ(0)·ρ(2)`.

So representability implies every field of `TailRatio.TripleFacts` except the strictness at lag zero
and the uniform bound `≤ 4`, which are separate facts about the Wilson correlation and not about the
shape. The converse fails — see `tripleFacts_not_ordered` and `tripleFacts_not_quadratic`.

DERIVED: no numeral here is a value; `2` is an exponent and `0` a sign. -/
theorem fourRepresentable_le {r₀ r₁ r₂ : ℝ} (h : FourRepresentable r₀ r₁ r₂) :
    r₂ ≤ r₁ ∧ r₁ ≤ r₀ ∧ r₁ ^ 2 ≤ r₀ * r₂ := by
  obtain ⟨h0, h2, hord, hq⟩ := h
  have h1 : 0 ≤ r₁ := le_trans h2 hord
  have hsq : r₂ ^ 2 ≤ r₀ * r₂ := by nlinarith [sq_nonneg r₂, sq_nonneg (r₁ - r₂)]
  have hlc : r₁ ^ 2 ≤ r₀ * r₂ := by nlinarith
  have hle : r₁ ≤ r₀ := by nlinarith [sq_nonneg (r₁ - r₀), sq_nonneg (r₁ + r₀)]
  exact ⟨hord, hle, hlc⟩

/-- **THE CONSTANT TRIPLE IS REPRESENTABLE, AT EVERY LEVEL.** So `FourRepresentable` bounds no ratio:
`ρ(2)/ρ(0) = 1` here. It is a shape condition, not a decay condition, and cannot be read as one.

DERIVED: `c` is a variable, not a level; the statement quantifies over it. -/
theorem fourRepresentable_const {c : ℝ} (hc : 0 ≤ c) : FourRepresentable c c c :=
  ⟨hc, hc, le_rfl, by nlinarith⟩

/-! ## 2. Necessity -/

/-- **THE REGION CONTAINS EVERY FINITE TRANSFER-MATRIX PERIODIC CORRELATOR.**

For `T` diagonalised with nonnegative eigenvalues `λᵢ` and `A` self-adjoint in that basis,
`Tr(A Tᵈ A T⁴⁻ᵈ) = ∑ᵢⱼ Aᵢⱼ Aⱼᵢ λᵢᵈ λⱼ⁴⁻ᵈ = ∑ᵢⱼ |Aᵢⱼ|² λᵢᵈ λⱼ⁴⁻ᵈ`, and grouping `(i,j)` with `(j,i)`
leaves one term `c (aᵈ b⁴⁻ᵈ + bᵈ a⁴⁻ᵈ)` per unordered pair. The coefficient `c = |Aᵢⱼ|² ≥ 0` is
entrywise nonnegative with no semidefiniteness needed, because it is a squared modulus — and the
self-adjointness of `A` is what turns `Aᵢⱼ Aⱼᵢ` into it. Those two, and diagonalisability of `T` with
`λ ≥ 0`, are the standing assumptions of that motivating calculation; they are NOT hypotheses of this
theorem, which is about bare sums and carries only `0 ≤ c`, `0 ≤ a`, `0 ≤ b`. The three sums below are
the lags `0`, `1`, `2` of such a correlator, and they land in `FourRepresentable`.

**So the two-term ansatz is NOT the obstruction.** `PeriodicSpectralForm`'s shape
`λᵈ + λ⁴⁻ᵈ` is the `b = 1` case — a mode paired with the vacuum — and it looks narrower than the
general two-index transfer form, but at extent four it is not: every unordered pair `(a, b)` lands
on the boundary surface `2ρ₁² = ρ₂² + ρ₀ρ₂` exactly, at the cone ray the one-parameter curve reaches
at `λ = a/b`. That is why `fourRepresentable_of_sums` and this theorem have the same three
conclusions and the same Cauchy–Schwarz proof.

The consequence for the obligation: `FourRepresentable` is what "the triple came from a finite
transfer matrix" says about three numbers, so the two inequalities the tree does not prove are
exactly that content and no more.

DERIVED: `4` is the period, `0, 1, 2, 3` are lags and their reflections `4 − d`, and `2` is the pair
multiplicity at the self-paired lag. No magnitude is chosen. -/
theorem fourRepresentable_of_pairs {κ : Type*} [Fintype κ] (c a b : κ → ℝ)
    (hc : ∀ k, 0 ≤ c k) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) :
    FourRepresentable (∑ k, c k * (a k ^ 4 + b k ^ 4))
      (∑ k, c k * (a k * b k ^ 3 + b k * a k ^ 3))
      (∑ k, c k * (a k ^ 2 * b k ^ 2 + b k ^ 2 * a k ^ 2)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (by positivity)
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (by positivity)
  · refine Finset.sum_le_sum fun k _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hc k)
    nlinarith [mul_nonneg (mul_nonneg (ha k) (hb k)) (sq_nonneg (a k - b k))]
  · -- Cauchy–Schwarz against `(√c · ab, √c · (a² + b²))`.
    set T : ℝ := ∑ k, c k * (a k ^ 2 * b k ^ 2) with hT
    set U : ℝ := ∑ k, c k * (a k ^ 4 + b k ^ 4) with hU
    have hsq : ∀ k, Real.sqrt (c k) * Real.sqrt (c k) = c k :=
      fun k => Real.mul_self_sqrt (hc k)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => Real.sqrt (c k) * (a k * b k))
      (fun k => Real.sqrt (c k) * (a k ^ 2 + b k ^ 2))
    have hA : (∑ k, (Real.sqrt (c k) * (a k * b k)) * (Real.sqrt (c k) * (a k ^ 2 + b k ^ 2)))
        = ∑ k, c k * (a k * b k ^ 3 + b k * a k ^ 3) :=
      Finset.sum_congr rfl fun k _ => by
        linear_combination (a k * b k * (a k ^ 2 + b k ^ 2)) * hsq k
    have hB : (∑ k, (Real.sqrt (c k) * (a k * b k)) ^ 2) = T := by
      rw [hT]
      exact Finset.sum_congr rfl fun k _ => by
        linear_combination (a k ^ 2 * b k ^ 2) * hsq k
    have hC : (∑ k, (Real.sqrt (c k) * (a k ^ 2 + b k ^ 2)) ^ 2) = U + 2 * T := by
      rw [hT, hU, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        linear_combination ((a k ^ 2 + b k ^ 2) ^ 2) * hsq k
    have h2T : (∑ k, c k * (a k ^ 2 * b k ^ 2 + b k ^ 2 * a k ^ 2)) = 2 * T := by
      rw [hT, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hA, hB, hC] at hcs
    rw [h2T]
    nlinarith [hcs]

/-- **THE NECESSARY CONDITIONS, FROM `w ≥ 0` AND `λ ≥ 0` ALONE.**

Stated on bare sums rather than on a form, with NO upper bound on `λ`, because that is the content:
the extent-four region does not use `λ ≤ 1`. The triple depends on `λ` only through `λ + 1/λ`, which
`λ ↦ 1/λ` fixes, so the unit bound cannot cut anything away — `unit_bound_inert` is the consequence.

This is `fourRepresentable_of_pairs` at `b = 1`: the periodic two-term shape is a mode paired with
the vacuum.

DERIVED: the exponents `1, 2, 3, 4` are the lags and their reflections `4 − d`; `1` is the vacuum's
decay factor. Nothing is chosen. -/
theorem fourRepresentable_of_sums {ι : Type*} [Fintype ι] (w lam : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hlam : ∀ k, 0 ≤ lam k) :
    FourRepresentable (∑ k, w k * (1 + lam k ^ 4)) (∑ k, w k * (lam k ^ 1 + lam k ^ 3))
      (∑ k, w k * (lam k ^ 2 + lam k ^ 2)) := by
  have h := fourRepresentable_of_pairs w lam (fun _ => (1 : ℝ)) hw hlam (fun _ => zero_le_one)
  have e0 : (∑ k, w k * (lam k ^ 4 + (1 : ℝ) ^ 4)) = ∑ k, w k * (1 + lam k ^ 4) :=
    Finset.sum_congr rfl fun k _ => by ring
  have e1 : (∑ k, w k * (lam k * (1 : ℝ) ^ 3 + (1 : ℝ) * lam k ^ 3))
      = ∑ k, w k * (lam k ^ 1 + lam k ^ 3) :=
    Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ k, w k * (lam k ^ 2 * (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 * lam k ^ 2))
      = ∑ k, w k * (lam k ^ 2 + lam k ^ 2) :=
    Finset.sum_congr rfl fun k _ => by ring
  rwa [e0, e1, e2] at h

/-- **EVERY FORM AT EXTENT FOUR LANDS IN THE REGION.** Its `hrep` at the three independent lags,
read against `fourRepresentable_of_sums`. `hlam1` is not used.

DERIVED: `0`, `1`, `2` are lag indices and `4` the period. -/
theorem fourRepresentable_of_form {ρ : Fin 4 → ℝ} (S : Spectral.PeriodicSpectralForm 4 ρ) :
    FourRepresentable (ρ 0) (ρ 1) (ρ 2) := by
  have e0 : ρ 0 = ∑ k, S.w k * (1 + S.lam k ^ 4) := by
    have h := S.hrep 0
    rw [val0] at h
    simpa using h
  have e1 : ρ 1 = ∑ k, S.w k * (S.lam k ^ 1 + S.lam k ^ 3) := by
    have h := S.hrep 1
    rw [val1] at h
    norm_num at h
    simpa using h
  have e2 : ρ 2 = ∑ k, S.w k * (S.lam k ^ 2 + S.lam k ^ 2) := by
    have h := S.hrep 2
    rw [val2] at h
    norm_num at h
    simpa using h
  rw [e0, e1, e2]
  exact fourRepresentable_of_sums S.w S.lam S.hw S.hlam0

/-- **LAG THREE IS LAG ONE, from the shape.** `4 − 3 = 1` and `4 − 1 = 3`, so the two summands swap.

DERIVED: `1` and `3` are lag indices; `4` is the period. -/
theorem rho_three_eq_one {ρ : Fin 4 → ℝ} (S : Spectral.PeriodicSpectralForm 4 ρ) :
    ρ 3 = ρ 1 := by
  have h3 := S.hrep 3
  have h1 := S.hrep 1
  rw [val3] at h3
  rw [val1] at h1
  norm_num at h3 h1
  rw [h3, h1]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## 3. Sufficiency — an explicit two-mode witness -/

/-- **THE TWO-MODE FORM.** One mode at `λ = 0` carrying the contact term, one at `λ = l`, assembled
into a `Spectral.PeriodicSpectralForm 4` from the four lag identities. The arithmetic that produces
`w₀, w₁, l` is `exists_two_mode`; this lemma is only the assembly, and is stated on plain reals so
that the index algebra is separated from the root algebra.

DERIVED: `2` is the number of modes; `0` is the contact mode's decay factor, forced as in
`Spectral2.contactForm`; `0, 1, 2, 3` are lag indices and `4` the period. -/
private lemma two_mode_form {ρ : Fin 4 → ℝ} (w₀ w₁ l : ℝ)
    (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (e0 : ρ 0 = w₀ + w₁ * (1 + l ^ 4))
    (e1 : ρ 1 = w₁ * (l ^ 1 + l ^ 3))
    (e2 : ρ 2 = w₁ * (l ^ 2 + l ^ 2))
    (e3 : ρ 3 = w₁ * (l ^ 3 + l ^ 1)) :
    Nonempty (Spectral.PeriodicSpectralForm 4 ρ) := by
  refine ⟨{ Idx := Fin 2
            w := ![w₀, w₁]
            lam := ![0, l]
            hw := ?_
            hlam0 := ?_
            hlam1 := ?_
            hrep := ?_ }⟩
  · intro k; fin_cases k
    · simpa using hw₀
    · simpa using hw₁
  · intro k; fin_cases k
    · simp
    · simpa using hl0
  · intro k; fin_cases k
    · simp
    · simpa using hl1
  · intro d
    fin_cases d
    · rw [show ((⟨0, by omega⟩ : Fin 4)) = (0 : Fin 4) from rfl, e0, Fin.sum_univ_two]
      norm_num
      try ring
    · rw [show ((⟨1, by omega⟩ : Fin 4)) = (1 : Fin 4) from rfl, e1, Fin.sum_univ_two]
      norm_num
      try ring
    · rw [show ((⟨2, by omega⟩ : Fin 4)) = (2 : Fin 4) from rfl, e2, Fin.sum_univ_two]
      norm_num
      try ring
    · rw [show ((⟨3, by omega⟩ : Fin 4)) = (3 : Fin 4) from rfl, e3, Fin.sum_univ_two]
      norm_num
      try ring

/-- **THE TWO MODES, FROM THE TWO INEQUALITIES.**

`c = r₁/r₂ ≥ 1` is exactly `r₂ ≤ r₁`, and it puts the smaller root `l = c − √(c² − 1)` of
`l² − 2cl + 1 = 0` in `(0, 1]`. That root's own equation is the only algebra used below: it turns
`l + l³` into `2c·l²` and `1 + l⁴` into `(4c² − 2)·l²`, so the mode at `l` carries exactly
`((2c² − 1)r₂, r₁, r₂)` and the contact weight is `w₀ = r₀ − (2c² − 1)r₂`. That weight is
nonnegative exactly when `2r₁² ≤ r₂² + r₀r₂`.

`hord` is what makes the square root real and what puts the root at or below one; `hq` is exactly
`w₀ ≥ 0`. Neither can be weakened. Two modes always suffice; the third free parameter a three-mode
form would offer is never needed.

`_h0` is carried only to match `FourRepresentable`'s field order and is not used: on `r₂ > 0` the
other two hypotheses already force `r₀r₂ ≥ 2r₁² − r₂² ≥ r₂² > 0`.

DERIVED: `2` in `2c²−1` and `2cl` is the root equation's own coefficient, `4` in `l⁴` is the period,
`1` is the constant term of the root equation. No magnitude is chosen. -/
private lemma exists_two_mode {r₀ r₁ r₂ : ℝ} (_h0 : 0 ≤ r₀) (hpos : 0 < r₂)
    (hord : r₂ ≤ r₁) (hq : 2 * r₁ ^ 2 ≤ r₂ ^ 2 + r₀ * r₂) :
    ∃ w₀ w₁ l : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ l ∧ l ≤ 1 ∧
      r₀ = w₀ + w₁ * (1 + l ^ 4) ∧ r₁ = w₁ * (l ^ 1 + l ^ 3)
        ∧ r₂ = w₁ * (l ^ 2 + l ^ 2) := by
  have hr2ne : r₂ ≠ 0 := ne_of_gt hpos
  set c : ℝ := r₁ / r₂ with hc
  have hcr : c * r₂ = r₁ := by rw [hc]; field_simp
  have hc1 : 1 ≤ c := by rw [hc, le_div_iff₀ hpos]; linarith
  have hcc : 0 ≤ c ^ 2 - 1 := by nlinarith
  set s : ℝ := Real.sqrt (c ^ 2 - 1) with hs
  have hs2 : s ^ 2 = c ^ 2 - 1 := Real.sq_sqrt hcc
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set lam : ℝ := c - s with hlamdef
  have hlamc : lam * (c + s) = 1 := by rw [hlamdef]; nlinarith [hs2]
  have hcs0 : 0 < c + s := by nlinarith
  have hlam0 : 0 < lam := by nlinarith [hlamc, hcs0]
  have hlam1 : lam ≤ 1 := by
    have hsq : (c - 1) ^ 2 ≤ c ^ 2 - 1 := by nlinarith
    have hle : c - 1 ≤ s := by
      rw [hs]
      calc c - 1 = Real.sqrt ((c - 1) ^ 2) := (Real.sqrt_sq (by linarith)).symm
        _ ≤ Real.sqrt (c ^ 2 - 1) := Real.sqrt_le_sqrt hsq
    rw [hlamdef]; linarith
  -- the root's own equation, which is all the algebra below uses
  have hkey : lam ^ 2 + 1 = 2 * c * lam := by rw [hlamdef]; nlinarith [hs2]
  have hlamsq : 0 < lam ^ 2 := by positivity
  set w₁ : ℝ := r₂ / (2 * lam ^ 2) with hw1
  have hw1pos : 0 ≤ w₁ := by rw [hw1]; exact div_nonneg hpos.le (by linarith)
  have hE2 : w₁ * (lam ^ 2 + lam ^ 2) = r₂ := by rw [hw1]; field_simp; ring
  have hE1 : w₁ * (lam ^ 1 + lam ^ 3) = r₁ := by
    have hstep : w₁ * (lam ^ 1 + lam ^ 3) = (w₁ * (lam ^ 2 + lam ^ 2)) * c := by
      rw [hw1]; field_simp; nlinarith [hkey]
    rw [hstep, hE2]
    linarith [hcr]
  have hE0 : w₁ * (1 + lam ^ 4) = (2 * c ^ 2 - 1) * r₂ := by
    have hfour : 1 + lam ^ 4 = (4 * c ^ 2 - 2) * lam ^ 2 := by nlinarith [hkey]
    rw [hfour, hw1]; field_simp; ring
  have hw0pos : 0 ≤ r₀ - (2 * c ^ 2 - 1) * r₂ := by
    have hcsq : c ^ 2 * r₂ ^ 2 = r₁ ^ 2 := by rw [← hcr]; ring
    nlinarith [hcsq]
  clear_value w₁ lam s c
  exact ⟨r₀ - (2 * c ^ 2 - 1) * r₂, w₁, lam, hw0pos, hw1pos, hlam0.le, hlam1,
    by rw [hE0]; ring, hE1.symm, hE2.symm⟩

/-- **THE REGION IS ATTAINED.**

`FourRepresentable` together with the circle symmetry `ρ(3) = ρ(1)` produces a genuine
`Spectral.PeriodicSpectralForm 4`, with TWO modes: one at `λ = 0` and one at
`λ = c − √(c² − 1)`, `c = ρ(1)/ρ(2)`. Where `ρ(2) = 0` the quadratic forces `ρ(1) = 0` and the form
degenerates to the pure contact term of `Spectral2.contactForm`, recovered here as the `w₁ = 0`
member of the same two-mode family.

DERIVED: `0`, `1`, `2`, `3` are lag indices; `2` is the number of modes the proof produces, not a
budget anyone set. No magnitude is chosen. -/
theorem nonempty_of_fourRepresentable {ρ : Fin 4 → ℝ}
    (h : FourRepresentable (ρ 0) (ρ 1) (ρ 2)) (h3 : ρ 3 = ρ 1) :
    Nonempty (Spectral.PeriodicSpectralForm 4 ρ) := by
  obtain ⟨h0, h2, hord, hq⟩ := h
  rcases eq_or_lt_of_le h2 with hz | hpos
  · -- `ρ(2) = 0` forces `ρ(1) = 0`: the contact term, as the `w₁ = 0` member of the family.
    have hr1 : ρ 1 = 0 := by nlinarith [sq_nonneg (ρ 1)]
    refine two_mode_form (ρ := ρ) (ρ 0) 0 0 h0 le_rfl le_rfl zero_le_one ?_ ?_ ?_ ?_
    · norm_num
    · rw [hr1]; norm_num
    · rw [← hz]; norm_num
    · rw [h3, hr1]; norm_num
  · obtain ⟨w₀, w₁, l, hw₀, hw₁, hl0, hl1, e0, e1, e2⟩ :=
      exists_two_mode h0 hpos hord hq
    exact two_mode_form w₀ w₁ l hw₀ hw₁ hl0 hl1 e0 e1 e2 (by rw [h3, e1]; ring)

/-- **THE CHARACTERISATION.** At extent four, a periodic spectral form exists exactly on
`FourRepresentable` together with the circle symmetry — a semialgebraic condition on three numbers.

DERIVED: `0`, `1`, `2`, `3` are lag indices; `4` is the period. -/
theorem four_iff {ρ : Fin 4 → ℝ} :
    Nonempty (Spectral.PeriodicSpectralForm 4 ρ)
      ↔ (FourRepresentable (ρ 0) (ρ 1) (ρ 2) ∧ ρ 3 = ρ 1) :=
  ⟨fun ⟨S⟩ => ⟨fourRepresentable_of_form S, rho_three_eq_one S⟩,
    fun h => nonempty_of_fourRepresentable h.1 h.2⟩

/-- **THE UNIT BOUND ON `λ` IS INERT AT EXTENT FOUR.** Sums built from `w ≥ 0` and `λ ≥ 0` with NO
upper bound on `λ` still yield a genuine form — one whose own decay factors satisfy `λ ≤ 1`.

So `hlam1` cuts nothing away at this extent, and the binding constraints are `w ≥ 0` and `λ ≥ 0`.
The mechanism: the triple depends on `λ` only through `λ + 1/λ`, invariant under `λ ↦ 1/λ`.

DERIVED: the exponents are the lags `1, 2, 3` and the reflection `4 − 0 = 4`. -/
theorem unit_bound_inert {ι : Type*} [Fintype ι] (w lam : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hlam : ∀ k, 0 ≤ lam k) {ρ : Fin 4 → ℝ}
    (h0 : ρ 0 = ∑ k, w k * (1 + lam k ^ 4))
    (h1 : ρ 1 = ∑ k, w k * (lam k ^ 1 + lam k ^ 3))
    (h2 : ρ 2 = ∑ k, w k * (lam k ^ 2 + lam k ^ 2))
    (h3 : ρ 3 = ρ 1) :
    Nonempty (Spectral.PeriodicSpectralForm 4 ρ) := by
  refine nonempty_of_fourRepresentable ?_ h3
  rw [h0, h1, h2]
  exact fourRepresentable_of_sums w lam hw hlam

/-! ## 4. What the tree proves is not enough, and exactly where -/

/-- **A CONFORMING TRIPLE THAT IS NOT ORDERED.** `TailRatio.TripleFacts` holds at `(4, 0, 4)` and
`ρ(2) ≤ ρ(1)` fails, so `ρ(2) ≤ ρ(1)` does not follow from the proved facts.

This is the same direction `TailRatio.no_lag_two_bound_from_triple` closes: `TailRatio.triple_raise`
says the premise set is upward-closed in `ρ(2)` UP TO THE UNIFORM BOUND — it carries `ht : t ≤ 4` and
is not closed past it — and `ρ(2) ≤ ρ(1)` is an upper bound on `ρ(2)`. The witness below sits exactly
at `t = 4`, which is why that lemma's range suffices here.

**AND `λ ≥ 0` IS EXACTLY WHAT THIS INEQUALITY BUYS.** `(4, 0, 4)` is a periodic spectral form in
every respect but one: `ordered_is_what_nonneg_lam_buys` shows it is `w = (1, 1)` at `λ = (1, −1)`,
reproducing all three lags. It fails `PeriodicSpectralForm` only on `hlam0 : 0 ≤ lam k`. So `ρ(2) ≤ ρ(1)`
is not an extra analytic estimate on top of the shape — it is the positivity of the decay factors.

DERIVED: `4` is `InfiniteVolume.wilsonCorrAt_abs_le_four`'s own uniform bound, quoted so the witness
sits inside the proved premise set rather than outside it. CHOSEN: `0` at lag one, the smallest value
the proved nonnegativity permits, which makes the separation as wide as the premise set allows.
Neither is a threshold and neither is a constant of the theory. -/
theorem tripleFacts_not_ordered :
    MassGap.TailRatio.TripleFacts 4 0 4 ∧ ¬ FourRepresentable 4 0 4 := by
  refine ⟨⟨by norm_num, le_rfl, by norm_num, by norm_num, le_rfl, by norm_num, le_rfl⟩, ?_⟩
  rintro ⟨-, -, hord, -⟩
  norm_num at hord

/-- **A CONFORMING, ORDERED TRIPLE THAT FAILS THE QUADRATIC.** `TailRatio.TripleFacts` holds at
`(4, 2, 1)`, `ρ(2) ≤ ρ(1)` holds, log-convexity holds with EQUALITY — and
`2ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2)` reads `8 ≤ 5` and fails.

So the second missing inequality is independent of the first and of everything the tree proves: it is
strictly stronger than the log-convexity `LogConvex.corrClay_log_convex_at_extent_four` supplies,
and the gap is already open on the log-convex boundary.

DERIVED: `4` is `InfiniteVolume.wilsonCorrAt_abs_le_four`'s uniform bound, carried not chosen.
CHOSEN: `2` and `1` at lags one and two, picked to put the triple exactly on the log-convex boundary
`ρ(1)² = ρ(0)·ρ(2)` so that the separation is against the proved facts at their own extreme. They set
no level and the statement is not about their magnitude. -/
theorem tripleFacts_not_quadratic :
    MassGap.TailRatio.TripleFacts 4 2 1 ∧ (1 : ℝ) ≤ 2 ∧ (2 : ℝ) ^ 2 = 4 * 1
      ∧ ¬ FourRepresentable 4 2 1 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, le_rfl, by norm_num,
    by norm_num⟩, by norm_num, by norm_num, ?_⟩
  rintro ⟨-, -, -, hq⟩
  norm_num at hq

/-- **THE TWO MISSING INEQUALITIES ARE INDEPENDENT.** `(4, 0, 4)` satisfies the quadratic and fails
the order; `(4, 2, 1)` satisfies the order and fails the quadratic. So neither implies the other over
the proved premise set and both are open.

DERIVED: the numerals are `tripleFacts_not_ordered`'s and `tripleFacts_not_quadratic`'s, carried. -/
theorem missing_inequalities_independent :
    (2 * (0 : ℝ) ^ 2 ≤ (4 : ℝ) ^ 2 + 4 * 4 ∧ ¬ ((4 : ℝ) ≤ 0))
      ∧ ((1 : ℝ) ≤ 2 ∧ ¬ (2 * (2 : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 + 4 * 1)) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- **`ρ(2) ≤ ρ(1)` IS THE POSITIVITY OF THE DECAY FACTORS, NOT AN ANALYTIC ESTIMATE.**

`(4, 0, 4)` satisfies `hrep` at all three independent lags with `w = (1, 1)` and `λ = (1, −1)`. Every
field of `Spectral.PeriodicSpectralForm 4` holds of it except `hlam0 : 0 ≤ lam k`. So the first
missing inequality is not something on top of the periodic shape — it IS `λ ≥ 0`, and a route to it
must be a route to positivity of the transfer spectrum rather than to a bound on a correlation.

DERIVED: `1` and `−1` are the two square roots of one — the only real `λ` with `λ⁴ = 1`, which is what
the period forces on a mode that is flat in `|ρ|`; `4` and `0` are `tripleFacts_not_ordered`'s
witness, carried. No magnitude is chosen. -/
theorem ordered_is_what_nonneg_lam_buys :
    (4 : ℝ) = 1 * ((1 : ℝ) ^ (0 : ℕ) + (1 : ℝ) ^ 4) + 1 * ((-1 : ℝ) ^ (0 : ℕ) + (-1 : ℝ) ^ 4)
      ∧ (0 : ℝ) = 1 * ((1 : ℝ) ^ (1 : ℕ) + (1 : ℝ) ^ 3) + 1 * ((-1 : ℝ) ^ (1 : ℕ) + (-1 : ℝ) ^ 3)
      ∧ (4 : ℝ) = 1 * ((1 : ℝ) ^ (2 : ℕ) + (1 : ℝ) ^ 2)
          + 1 * ((-1 : ℝ) ^ (2 : ℕ) + (-1 : ℝ) ^ 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **FULL POSITIVE-DEFINITENESS ON THE CIRCLE WOULD NOT SUPPLY EITHER INEQUALITY EITHER.**

`ρ` on `ℤ₄` with `ρ(3) = ρ(1)` has the four Fourier coefficients `ρ₀ + 2ρ₁ + ρ₂`, `ρ₀ − ρ₂` (twice)
and `ρ₀ − 2ρ₁ + ρ₂`. Positive-definiteness of `ρ` as a function on the group is all four being
nonnegative — strictly MORE than the tree proves, since `ρ₀ − ρ₂ ≥ 0` is `ρ(2) ≤ ρ(0)`, which
`TailRatio.no_lag_two_bound_from_triple` shows is unavailable. Both witnesses satisfy it anyway.

So the residue is not reachable by strengthening reflection positivity to the whole circle. That is
consistent with `ordered_is_what_nonneg_lam_buys`: `(4, 0, 4)` is positive-definite on `ℤ₄` precisely
because it is the `λ = −1` mode, and `λ = −1` is what `hlam0` excludes.

DERIVED: the coefficients `1, 2, 1` and the signs are the `ℤ₄` characters at `p = 0, π/2, π`, and the
values are the two witnesses', carried. No magnitude is chosen. -/
theorem circle_psd_not_sufficient :
    ((0 : ℝ) ≤ 4 + 2 * 0 + 4 ∧ (0 : ℝ) ≤ 4 - 4 ∧ (0 : ℝ) ≤ 4 - 2 * 0 + 4)
      ∧ ((0 : ℝ) ≤ 4 + 2 * 2 + 1 ∧ (0 : ℝ) ≤ 4 - 1 ∧ (0 : ℝ) ≤ 4 - 2 * 2 + 1) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩⟩

/-! ## 5. The Wilson correlation — the residue, named -/

/-- **THE OPEN OBLIGATION AT THE CLAY APERTURE, REDUCED TO THREE NUMBERS.**

`Complete.WilsonSpectral 3 β` is equivalent to this together with the circle symmetry — and the
symmetry is PROVED (`MomentShape.wilsonCorrAt_neg`). So this Prop is the WHOLE residue, and it is a
semialgebraic condition on `(ρ(0), ρ(1), ρ(2))` rather than a statement about an operator.

**THIS IS PROVED**, at every `0 ≤ β`, by `LinkGram.wilson_lag_two_le_lag_one` and
`SlabQuadratic.wilson_quadratic`. The analysis in this file is what stood: `TailRatio.triple_wilsonCorrAt`
proves `TripleFacts` at every `0 ≤ β` and `tripleFacts_not_ordered` / `tripleFacts_not_quadratic`
show `TripleFacts` does NOT imply either inequality — which is precisely why the proof could not come
from shape and had to come from reflection positivity. `ordered_is_what_nonneg_lam_buys` named the
content correctly too: the order relation is `λ ≥ 0`, and LINK-reflection positivity is what supplies
it, where site-reflection positivity does not.

DERIVED: `3` is the Clay aperture, `0`, `1`, `2` the lag indices its extent-four period resolves. -/
def WilsonFourRepresentable (β : ℝ) : Prop :=
  FourRepresentable (MassGap.wilsonCorrAt 3 β 0) (MassGap.wilsonCorrAt 3 β 1)
    (MassGap.wilsonCorrAt 3 β 2)

/-- **CIRCLE SYMMETRY AT EXTENT FOUR**, the half of the characterisation that IS proved.
`MomentShape.wilsonCorrAt_neg` at `−1 = 3`, as `ConfinesSharp.sym_four` reads it.

DERIVED: `3` is both the aperture and the lag `−1`; `1` is the lag it folds onto. -/
theorem wilson_lag_three (β : ℝ) :
    MassGap.wilsonCorrAt 3 β 3 = MassGap.wilsonCorrAt 3 β 1 := by
  have h := MassGap.MomentShape.wilsonCorrAt_neg 3 β (1 : Fin 4)
  have hneg : (-(1 : Fin 4)) = (3 : Fin 4) := by decide
  rwa [hneg] at h

/-- **`WilsonSpectral 3 β` FROM THE NAMED RESIDUE, AND FROM NOTHING ELSE.**

The hypothesis is `WilsonFourRepresentable β`. **It is now DISCHARGED**, at every `0 ≤ β`, by
`LinkGram.wilson_lag_two_le_lag_one` and `SlabQuadratic.wilson_quadratic`. What `tripleFacts_not_ordered`
and `tripleFacts_not_quadratic` establish is unchanged and was never about that: they show the
SHAPE facts do not imply it, which is why the proof had to come from reflection positivity.

What this does settle is the SHAPE of the remaining obligation. The route to the form needs no
operator, no GNS space and no `FiniteDimensional` hypothesis — which is the point, since
`Transfer.periodicSpectralForm_of_transfer` requires one and `SliceTrace` records that a slab
configuration is a point of a compact group of positive dimension. What is left is three real
numbers and the two of `FourRepresentable`'s four conjuncts SHAPE does not give — `ρ(2) ≤ ρ(1)`
and `2ρ(1)² ≤ ρ(2)² + ρ(0)·ρ(2)` — both of which reflection positivity now supplies. The other two, `0 ≤ ρ(0)` and `0 ≤ ρ(2)`, are already proved
(`PlaqVariance.corrClay_zero_pos` and `ReflectionStrong.corrClay_nonneg_even_lag`, through
`TailRatio.triple_wilsonCorrAt`). By `fourRepresentable_of_pairs` the two that remain are exactly
what a finite transfer matrix would supply, so the obligation is not weakened by the route — it is
the same physics with the functional analysis removed.

DERIVED: `3` is the Clay aperture. -/
theorem wilsonSpectral_of_representable {β : ℝ} (h : WilsonFourRepresentable β) :
    MassGap.WilsonSpectral 3 β :=
  nonempty_of_fourRepresentable h (wilson_lag_three β)

/-- **AND THE CONVERSE**, so the residue is exact rather than merely sufficient: at the Clay aperture
`WilsonSpectral 3 β` holds if and only if the triple is representable.

DERIVED: `3` is the Clay aperture. -/
theorem wilsonSpectral_iff {β : ℝ} :
    MassGap.WilsonSpectral 3 β ↔ WilsonFourRepresentable β :=
  ⟨fun h => fourRepresentable_of_form h.some, wilsonSpectral_of_representable⟩

/-- **THE FREE POINT IS INSIDE THE REGION.**

This is NOT an independent check of anything: it is `Spectral2.wilsonSpectral_at_zero_coupling`
transported through `wilsonSpectral_iff`, so it adds no producer. What it does confirm is that the
equivalence is not degenerate in the direction that would make it useless — the one coupling at which
`WilsonSpectral 3 β` is known does land inside `FourRepresentable`, so the characterisation is not
excluding the only case the tree can reach.

DERIVED: `3` is the Clay aperture and `0` the free coupling. -/
theorem wilsonFourRepresentable_at_zero : WilsonFourRepresentable 0 :=
  (wilsonSpectral_iff).mp (MassGap.Spectral2.wilsonSpectral_at_zero_coupling 2)

section Audit
#print axioms FourRepresentable
#print axioms fourRepresentable_le
#print axioms fourRepresentable_const
#print axioms fourRepresentable_of_pairs
#print axioms fourRepresentable_of_sums
#print axioms fourRepresentable_of_form
#print axioms rho_three_eq_one
#print axioms nonempty_of_fourRepresentable
#print axioms four_iff
#print axioms unit_bound_inert
#print axioms tripleFacts_not_ordered
#print axioms tripleFacts_not_quadratic
#print axioms missing_inequalities_independent
#print axioms ordered_is_what_nonneg_lam_buys
#print axioms circle_psd_not_sufficient
#print axioms WilsonFourRepresentable
#print axioms wilson_lag_three
#print axioms wilsonSpectral_of_representable
#print axioms wilsonSpectral_iff
#print axioms wilsonFourRepresentable_at_zero
end Audit

end MassGap.SpectralFour
