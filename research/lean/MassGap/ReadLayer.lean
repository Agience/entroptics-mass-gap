import Mathlib
import MassGap.EvenAperture
import MassGap.Substrate

/-!
# MassGap.ReadLayer — certified intervals and entropy bounds for `Moment.Read`

Three interval theorems — `attenuation_weyl_certified`, `resolved_count_certified`,
`separated_of_disjoint_intervals` — two monotonicity statements, two entropy bounds and two
congruence-invariance statements, joined to `Moment.Read` and to `EvenAperture.μEven`.

## Sections

1. The interval layer. `attenuation_interval_bounds` propagates two-sided brackets on `λ₁` and `r`
   through `log λ₁ − log r`; `attenuation_weyl_certified` composes that with a two-sided error bar
   `ε` on each read value; `resolved_count_certified` does the same for the count above an edge; and
   `separated_of_disjoint_intervals` orders two means whose certified intervals do not overlap.
   `noise_floor_monotone` and `resolved_dim_antitone` are the two monotonicity facts a count above a
   floor is read with.
2. The entropy layer, stated for an arbitrary probability vector on `Fin n`: `ratio_bounds`,
   `entropy_nonneg_le_log` and `fill_fraction_entropy_bounds`. `spectral_read_congruence` and
   `spectral_read_orthogonal` say that an arbitrary function of the characteristic polynomial is
   unchanged under the corresponding congruence of matrices over a commutative ring.
3. The join. `Moment.Read.tension` is `−log ⟨cos θ⟩_p` and `p` is `ρ` normalised, so
   `tension_eq_log_sub` rewrites the tension as `log (Σ ρ) − log (Σ ρ cos θ)` under the guard
   `0 < Σ ρ cos θ`. Writing `S(0) = Σ ρ` and `S(2π/(N+1)) = Σ ρ cos θ`, that is the attenuation
   `attenuation_weyl_certified` brackets, and `tension_certified_interval` is the composition.
4. The landing. `μEven a β` is `(readEven a β).tension` definitionally, so
   `confines_at_an_aperture_of_certified` produces `∃ a : EvenAp, ∀ β, μEven a β < κ₀YM` from two
   read functions of the coupling, one error bar `ε` bound outside the quantifier over couplings, and
   a certified upper endpoint below `κ₀YM` at every coupling.
5. The read's own entropy: `0 ≤ H(p) ≤ log (N+1)` and the fill fraction
   `2^{H₂}/(N+1) ∈ [1/(N+1), 1]`, both from `Moment.Read.p`'s `p_nonneg` and `p_sum`.
6. `Real.log` is even, so `Moment.Read.tension` is `−log |⟨cos θ⟩_p|` (`tension_eq_neg_log_abs`).
   A read with `⟨cos θ⟩_p < −3^{−1/4}` therefore satisfies `tension < κ₀YM`
   (`reads_confined_of_cosAvg_lt_neg`), and `Substrate.antipodeRead` is such a read: cosine average
   `−1`, tension `0` and entropy `0`.

`#print axioms` follows every declaration, and §7 repeats the whole list.
-/

namespace MassGap.ReadLayer

open scoped BigOperators Matrix
open MassGap.EvenAperture

/-! ## 1. The certified-interval layer

Three interval statements, plus the two monotonicity statements a noise floor and a count above it
are read with. All five are stated over arbitrary index types and carry no lattice content. -/

/-- Monotone propagation of two-sided brackets through an attenuation.
Given `lo1 ≤ lam1 ≤ hi1` and `lor ≤ r ≤ hir` with `lo1` and `lor` positive, the difference
`log lam1 − log r`, increasing in `lam1` and decreasing in `r`, lies between `log lo1 − log hir` and
`log hi1 − log lor`. Positivity of `lam1` and of `r` follows from the two hypotheses and the lower
brackets, so `hi1` and `hir` need no sign hypothesis of their own. The brackets are arguments: the
statement propagates them and produces none.

DERIVED: `0` appears twice, as the sign condition on the two lower brackets `lo1` and `lor`. -/
theorem attenuation_interval_bounds {lo1 hi1 lor hir lam1 r : ℝ}
    (hlo1 : 0 < lo1) (hlor : 0 < lor)
    (h1 : lo1 ≤ lam1) (h1' : lam1 ≤ hi1) (hr : lor ≤ r) (hr' : r ≤ hir) :
    Real.log lo1 - Real.log hir ≤ Real.log lam1 - Real.log r ∧
      Real.log lam1 - Real.log r ≤ Real.log hi1 - Real.log lor := by
  have hr0 : 0 < r := lt_of_lt_of_le hlor hr
  have hlam0 : 0 < lam1 := lt_of_lt_of_le hlo1 h1
  refine ⟨?_, ?_⟩
  · have ha : Real.log lo1 ≤ Real.log lam1 := Real.log_le_log hlo1 h1
    have hb : Real.log r ≤ Real.log hir := Real.log_le_log hr0 hr'
    linarith
  · have ha : Real.log lam1 ≤ Real.log hi1 := Real.log_le_log hlam0 h1'
    have hb : Real.log lor ≤ Real.log r := Real.log_le_log hlor hr
    linarith

#print axioms attenuation_interval_bounds

/-- Two suprema of pointwise-close families are close.
For `rhat r : ι → ℝ` over a nonempty index, both with bounded range, `|rhat i − r i| ≤ ε` at every
`i` gives `|(⨆ i, rhat i) − (⨆ i, r i)| ≤ ε`. This is the Weyl estimate for a top eigenvalue
presented in Courant–Fischer form as a supremum of Rayleigh quotients, but the statement is about
the two suprema only: `ι` is an arbitrary nonempty type, and no matrix, inner product or sphere
occurs in it. Both `BddAbove` hypotheses are used, one for each direction.

DERIVED: no numeral appears in the statement. -/
theorem weyl_top_of_rayleigh {ι : Type*} [Nonempty ι] (rhat r : ι → ℝ) (ε : ℝ)
    (hbr : BddAbove (Set.range r)) (hbrhat : BddAbove (Set.range rhat))
    (h : ∀ i, |rhat i - r i| ≤ ε) :
    |(⨆ i, rhat i) - (⨆ i, r i)| ≤ ε := by
  have hub : (⨆ i, rhat i) ≤ (⨆ i, r i) + ε :=
    ciSup_le fun i => by have := (abs_le.mp (h i)).2; have := le_ciSup hbr i; linarith
  have hlb : (⨆ i, r i) ≤ (⨆ i, rhat i) + ε :=
    ciSup_le fun i => by have := (abs_le.mp (h i)).1; have := le_ciSup hbrhat i; linarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

#print axioms weyl_top_of_rayleigh

/-- The certified attenuation interval, from read values and one error bar.
From `|lam1hat − lam1| ≤ ε`, `|rhat − r| ≤ ε` and positivity of `lam1hat − ε` and of `rhat − ε`, the
true `log lam1 − log r` lies between `log (lam1hat − ε) − log (rhat + ε)` and
`log (lam1hat + ε) − log (rhat − ε)`. A single `ε` serves both read values, and no hypothesis
constrains its size. `attenuation_interval_bounds` is the propagation step; the four brackets are
read off the two absolute-value hypotheses. Its upper half is the endpoint
`MassGap.confinement_of_certified` compares against.

DERIVED: `0` appears twice, as the sign condition on the two lower endpoints `lam1hat − ε` and
`rhat − ε`. -/
theorem attenuation_weyl_certified {lam1hat rhat lam1 r ε : ℝ}
    (hlo1 : 0 < lam1hat - ε) (hlor : 0 < rhat - ε)
    (h1 : |lam1hat - lam1| ≤ ε) (hr : |rhat - r| ≤ ε) :
    Real.log (lam1hat - ε) - Real.log (rhat + ε) ≤ Real.log lam1 - Real.log r ∧
      Real.log lam1 - Real.log r ≤ Real.log (lam1hat + ε) - Real.log (rhat - ε) := by
  rw [abs_le] at h1 hr
  exact attenuation_interval_bounds hlo1 hlor (by linarith [h1.2]) (by linarith [h1.1])
    (by linarith [hr.2]) (by linarith [hr.1])

#print axioms attenuation_weyl_certified

/-- The certified count above an edge.
On a finset `s` over which the read values satisfy `|lamhat k − lam k| ≤ ε`, the number of true
values strictly above `edge` is enclosed by the two read-side counts, with the edge shifted by `ε`
each way. Both `lam` and `lamhat` are arguments, so the statement bounds the cardinality of a
supplied family and constructs none. `ι` carries no `Fintype` or `DecidableEq` instance; the filters
are formed classically, and `edge` and `ε` are unconstrained reals.

DERIVED: no numeral appears in the statement. -/
theorem resolved_count_certified {ι : Type*} (s : Finset ι) (lam lamhat : ι → ℝ) (ε edge : ℝ)
    (hband : ∀ k ∈ s, |lamhat k - lam k| ≤ ε) :
    (s.filter (fun k => edge < lamhat k - ε)).card ≤ (s.filter (fun k => edge < lam k)).card ∧
      (s.filter (fun k => edge < lam k)).card ≤ (s.filter (fun k => edge < lamhat k + ε)).card := by
  classical
  refine ⟨Finset.card_le_card ?_, Finset.card_le_card ?_⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    obtain ⟨hks, hlt⟩ := hk
    have hb := abs_le.mp (hband k hks)
    exact ⟨hks, by linarith [hb.2]⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    obtain ⟨hks, hlt⟩ := hk
    have hb := abs_le.mp (hband k hks)
    exact ⟨hks, by linarith [hb.1]⟩

#print axioms resolved_count_certified

/-- Non-overlapping certified intervals order the two true means.
From `|Ec − mc| ≤ tc`, `|Ed − md| ≤ td` and the strict separation `mc + tc < md − td`, the conclusion
is `Ec < Ed`. The two-sided form of a comparison whose one-sided case puts a constant in place of the
second interval; `tc` and `td` are unconstrained, and the separation hypothesis carries all of the
content.

DERIVED: no numeral appears in the statement. -/
theorem separated_of_disjoint_intervals {Ec Ed mc tc md td : ℝ}
    (hEc : |Ec - mc| ≤ tc) (hEd : |Ed - md| ≤ td) (hgap : mc + tc < md - td) :
    Ec < Ed := by
  have hc := abs_le.mp hEc
  have hd := abs_le.mp hEd
  linarith [hc.2, hd.1]

#print axioms separated_of_disjoint_intervals

/-- The floor `sqrt (σ2 · (μ + q · ςJ))` is monotone in the quantile `q`.
For `0 ≤ σ2`, `0 ≤ ςJ` and `q₁ ≤ q₂`, `sqrt (σ2 * (μ + q₁ * ςJ)) ≤ sqrt (σ2 * (μ + q₂ * ςJ))`. The
shape is the Johnstone/Tracy–Widom noise floor, with `μ` the centring and `ςJ` the scale. No sign
hypothesis is placed on `μ`, so the inner arguments may be negative, where `Real.sqrt` is zero.

DERIVED: `0` appears twice, as the sign condition on `σ2` and on `ςJ`; the subscripts of `q₁` and
`q₂` are parts of names. -/
theorem noise_floor_monotone {σ2 μ ςJ q₁ q₂ : ℝ}
    (hσ : 0 ≤ σ2) (hς : 0 ≤ ςJ) (hq : q₁ ≤ q₂) :
    Real.sqrt (σ2 * (μ + q₁ * ςJ)) ≤ Real.sqrt (σ2 * (μ + q₂ * ςJ)) := by
  apply Real.sqrt_le_sqrt
  have hinner : q₁ * ςJ ≤ q₂ * ςJ := mul_le_mul_of_nonneg_right hq hς
  exact mul_le_mul_of_nonneg_left (by linarith) hσ

#print axioms noise_floor_monotone

/-- The count above a floor is antitone in the floor.
For `s : Fin n → ℝ` and `Φ₁ ≤ Φ₂`, the cardinality of `{k | Φ₂ < s k}` is at most that of
`{k | Φ₁ < s k}`, by inclusion of the two filters. `n` is arbitrary and `s` is unconstrained.

DERIVED: no numeral appears in the statement; the subscripts of `Φ₁` and `Φ₂` are parts of names. -/
theorem resolved_dim_antitone {n : ℕ} (s : Fin n → ℝ) {Φ₁ Φ₂ : ℝ} (h : Φ₁ ≤ Φ₂) :
    (Finset.univ.filter (fun k => Φ₂ < s k)).card
      ≤ (Finset.univ.filter (fun k => Φ₁ < s k)).card := by
  classical
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_le_of_lt h hk.2⟩

#print axioms resolved_dim_antitone

/-! ## 2. The entropy layer

Stated for an arbitrary probability vector on `Fin n`. `Moment.Read.p` is one, with `p_nonneg` and
`p_sum` proved, so §5 instantiates these at `n := N + 1`. -/

/-- A maximal weight's share of the total lies between `1/n` and `1`.
For nonnegative `w : Fin n → ℝ` with `0 < n`, an index `k` maximal in the sense `∀ i, w i ≤ w k`, and
a positive total, `1 / n ≤ w k / (∑ i, w i)` and `w k / (∑ i, w i) ≤ 1`. The lower bound uses
maximality through `∑ i, w i ≤ n * w k`; the upper bound uses only `w k ≤ ∑ i, w i`. Nothing orders
`w`, and `k` need not be unique.

DERIVED: `0` is the sign condition in `0 < n`, in `0 ≤ w i` and on the total; `1` is the numerator of
the lower endpoint `1 / n` and the upper endpoint itself. -/
theorem ratio_bounds {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (k : Fin n) (htop : ∀ i, w i ≤ w k)
    (hpos : 0 < ∑ i, w i) :
    1 / (n : ℝ) ≤ w k / (∑ i, w i) ∧ w k / (∑ i, w i) ≤ 1 := by
  have hconst : (∑ _i : Fin n, w k) = (n : ℝ) * w k := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum_le : (∑ i, w i) ≤ (n : ℝ) * w k :=
    calc (∑ i, w i) ≤ ∑ _i : Fin n, w k := Finset.sum_le_sum (fun i _ => htop i)
      _ = (n : ℝ) * w k := hconst
  have hk_le : w k ≤ ∑ i, w i := Finset.single_le_sum (fun i _ => hw i) (Finset.mem_univ k)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · have hden : 0 < (n : ℝ) * (∑ i, w i) := mul_pos hnpos hpos
    have hnum : 0 ≤ (n : ℝ) * w k - (∑ i, w i) := by linarith [hsum_le]
    have hid : w k / (∑ i, w i) - 1 / (n : ℝ)
        = ((n : ℝ) * w k - (∑ i, w i)) / ((n : ℝ) * (∑ i, w i)) := by
      field_simp
    have hdiff : 0 ≤ w k / (∑ i, w i) - 1 / (n : ℝ) := by
      rw [hid]; exact div_nonneg hnum (le_of_lt hden)
    linarith
  · rw [div_le_one hpos]
    exact hk_le

#print axioms ratio_bounds

/-- The Shannon entropy of a probability vector on `Fin n` lies between `0` and `log n`.
For `0 < n` and `q` nonnegative with `∑ i, q i = 1`, `0 ≤ ∑ i, Real.negMulLog (q i)` and that sum is
at most `Real.log n`. The lower bound is termwise from `Real.negMulLog_nonneg`, using `q i ≤ 1` read
off the normalisation; the upper bound is Jensen against the uniform weights `(n : ℝ)⁻¹`, through
`Real.concaveOn_negMulLog`. The logarithm is natural, as is the `negMulLog` in the entropy.

DERIVED: `0` is the sign condition in `0 < n`, in `0 ≤ q i` and at the left end of the conclusion;
`1` is the normalisation `∑ i, q i = 1`. -/
theorem entropy_nonneg_le_log {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    0 ≤ ∑ i, Real.negMulLog (q i) ∧ ∑ i, Real.negMulLog (q i) ≤ Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hqle : ∀ i, q i ≤ 1 := fun i =>
    hsum ▸ Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)
  refine ⟨Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (hq i) (hqle i), ?_⟩
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ (n : ℝ)⁻¹ :=
    fun _ _ => by positivity
  have hwsum : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ (ne_of_gt hn0)]
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)), q i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => hq i
  have hJ := Real.concaveOn_negMulLog.le_map_sum hw hwsum hmem
  simp only [smul_eq_mul] at hJ
  have hLHS : (∑ i, (n : ℝ)⁻¹ * Real.negMulLog (q i))
      = (n : ℝ)⁻¹ * ∑ i, Real.negMulLog (q i) := by rw [Finset.mul_sum]
  have hRHS : (∑ i, (n : ℝ)⁻¹ * q i) = (n : ℝ)⁻¹ := by rw [← Finset.mul_sum, hsum, mul_one]
  rw [hLHS, hRHS] at hJ
  have hval : Real.negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * Real.log n := by
    rw [show Real.negMulLog ((n : ℝ)⁻¹) = -(n : ℝ)⁻¹ * Real.log ((n : ℝ)⁻¹) from rfl,
      Real.log_inv]; ring
  rw [hval] at hJ
  exact le_of_mul_le_mul_left hJ (by positivity)

#print axioms entropy_nonneg_le_log

/-- The exponentiated entropy and the fill fraction.
Under the hypotheses of `entropy_nonneg_le_log`, with `H` the natural-log entropy of `q`, the four
conjuncts are `1 ≤ 2 ^ (H / Real.log 2)`, `2 ^ (H / Real.log 2) ≤ n`, `1 / n ≤ 2 ^ (H / Real.log 2) / n`
and `2 ^ (H / Real.log 2) / n ≤ 1`. Dividing by `Real.log 2` converts the natural-log entropy to
bits, and `Real.rpow` is the exponential. No constant enters from outside: both endpoints are `n` and
its reciprocal.

DERIVED: `0` is the sign condition in `0 < n` and in `0 ≤ q i`; `1` is the normalisation
`∑ i, q i = 1`, the lower endpoint of the exponential, the numerator of `1 / n` and the upper
endpoint of the fraction; `2` is the base of the exponential and the base of the logarithm it is
divided by. -/
theorem fill_fraction_entropy_bounds {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    1 ≤ (2 : ℝ) ^ ((∑ i, Real.negMulLog (q i)) / Real.log 2) ∧
    (2 : ℝ) ^ ((∑ i, Real.negMulLog (q i)) / Real.log 2) ≤ (n : ℝ) ∧
    1 / (n : ℝ) ≤ (2 : ℝ) ^ ((∑ i, Real.negMulLog (q i)) / Real.log 2) / (n : ℝ) ∧
    (2 : ℝ) ^ ((∑ i, Real.negMulLog (q i)) / Real.log 2) / (n : ℝ) ≤ 1 := by
  obtain ⟨hH0, hHlog⟩ := entropy_nonneg_le_log hn q hq hsum
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set H := ∑ i, Real.negMulLog (q i) with hHdef
  have hbridge : (2 : ℝ) ^ (H / Real.log 2) = Real.exp H := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  rw [hbridge]
  have h1 : (1 : ℝ) ≤ Real.exp H := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hH0
  have h2 : Real.exp H ≤ (n : ℝ) := by
    calc Real.exp H ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hHlog
      _ = (n : ℝ) := Real.exp_log hn0
  refine ⟨h1, h2, ?_, (div_le_one hn0).mpr h2⟩
  gcongr

#print axioms fill_fraction_entropy_bounds

/-- A function of the characteristic polynomial is a congruence invariant.
For square matrices over a commutative ring and an arbitrary `f : Polynomial R → α`, the single
hypothesis `Q * P = 1` gives `f ((P * C * Q).charpoly) = f (C.charpoly)`. `f` carries no continuity,
measurability or symmetry assumption, and the ring is arbitrary. `Matrix.charpoly_mul_comm` does the
work; the index type is finite with decidable equality.

DERIVED: `1` is the identity matrix of `Matrix n n R` in the hypothesis `Q * P = 1`. -/
theorem spectral_read_congruence {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] {α : Type*}
    (f : Polynomial R → α) (P C Q : Matrix n n R) (hQP : Q * P = 1) :
    f ((P * C * Q).charpoly) = f (C.charpoly) := by
  have hcong : (P * C * Q).charpoly = C.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  rw [hcong]

#print axioms spectral_read_congruence

/-- The same under a transpose congruence.
`Pᵀ * P = 1` gives `f ((P * C * Pᵀ).charpoly) = f (C.charpoly)`, immediately from
`spectral_read_congruence` at `Q := Pᵀ`. The entries lie in an arbitrary commutative ring rather than
in `ℝ`, the hypothesis is the single equation `Pᵀ * P = 1`, and no determinant condition is imposed.

DERIVED: `1` is the identity matrix in the hypothesis `Pᵀ * P = 1`. -/
theorem spectral_read_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] {α : Type*}
    (f : Polynomial R → α) (P C : Matrix n n R) (hP : Pᵀ * P = 1) :
    f ((P * C * Pᵀ).charpoly) = f (C.charpoly) :=
  spectral_read_congruence f P C Pᵀ hP

#print axioms spectral_read_orthogonal

/-! ## 3. The join: the tension as an attenuation

One identity between `Moment.Read.tension` and a difference of logarithms, and the certified interval
that follows from it. -/

/-- The cosine average is a ratio of `ρ`-sums:
`∑ d, R.p d * cos (R.θ d) = (∑ d, R.ρ d * cos (R.θ d)) / (∑ d, R.ρ d)`, since `Moment.Read.p` is `ρ`
divided by its own sum. Written as structure factors, `⟨cos θ⟩_p = S(2π/(N+1)) / S(0)`. Term-by-term
algebra of the division; no positivity hypothesis is taken.

DERIVED: no numeral appears in the statement. -/
theorem cosAvg_eq_ratio {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * Real.cos (R.θ d)
      = (∑ d, R.ρ d * Real.cos (R.θ d)) / (∑ d, R.ρ d) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  show R.ρ d / (∑ d', R.ρ d') * Real.cos (R.θ d) = _
  ring

#print axioms cosAvg_eq_ratio

/-- The tension as a difference of logarithms.
Under `0 < ∑ d, R.ρ d * cos (R.θ d)`,
`R.tension = log (∑ d, R.ρ d) − log (∑ d, R.ρ d * cos (R.θ d))` — in structure-factor notation,
`log S(0) − log S(2π/(N+1))`, the attenuation `attenuation_interval_bounds` propagates brackets
through at `λ₁ := S(0)` and `r := S(2π/(N+1))`. `cosAvg_eq_ratio` supplies the ratio and
`Real.log_div` splits it, taking the two nonzero arguments from the hypothesis and from `R.hpos`.
The hypothesis is load-bearing: `Real.log` is even, so without it the left side reads an absolute
value (`tension_eq_neg_log_abs`).

DERIVED: `0` is the sign condition on the cosine-weighted sum. -/
theorem tension_eq_log_sub {N : ℕ} (R : Moment.Read N)
    (hc : 0 < ∑ d, R.ρ d * Real.cos (R.θ d)) :
    R.tension = Real.log (∑ d, R.ρ d) - Real.log (∑ d, R.ρ d * Real.cos (R.θ d)) := by
  show - Real.log (∑ d, R.p d * Real.cos (R.θ d)) = _
  rw [cosAvg_eq_ratio, Real.log_div (ne_of_gt hc) (ne_of_gt R.hpos)]
  ring

#print axioms tension_eq_log_sub

/-- A positive lower endpoint forces the cosine-weighted sum positive.
From `0 < S1hat − ε` and `|S1hat − ∑ d, R.ρ d * cos (R.θ d)| ≤ ε`, the sum
`∑ d, R.ρ d * cos (R.θ d)` is positive. This is exactly the guard `tension_eq_log_sub` requires, so
the certified statements below supply it from their own hypotheses rather than assuming it.

DERIVED: `0` appears twice, as the sign condition on `S1hat − ε` and on the cosine-weighted sum. -/
theorem cosAvg_pos_of_certified {N : ℕ} (R : Moment.Read N) {S1hat ε : ℝ}
    (h1 : 0 < S1hat - ε)
    (hr1 : |S1hat - ∑ d, R.ρ d * Real.cos (R.θ d)| ≤ ε) :
    0 < ∑ d, R.ρ d * Real.cos (R.θ d) := by
  have hb := abs_le.mp hr1
  linarith [hb.2]

#print axioms cosAvg_pos_of_certified

/-- The certified interval on `Moment.Read.tension`.
Given read values `S0hat` for `∑ d, R.ρ d` and `S1hat` for `∑ d, R.ρ d * cos (R.θ d)`, each within
`ε`, and with both lower endpoints positive, `R.tension` lies between
`log (S0hat − ε) − log (S1hat + ε)` and `log (S0hat + ε) − log (S1hat − ε)`.
`tension_eq_log_sub` rewrites the tension, `cosAvg_pos_of_certified` discharges its guard, and
`attenuation_weyl_certified` supplies the two endpoints. One `ε` serves both reads, and no hypothesis
bounds it.

DERIVED: `0` appears twice, as the sign condition on `S0hat − ε` and on `S1hat − ε`. -/
theorem tension_certified_interval {N : ℕ} (R : Moment.Read N) {S0hat S1hat ε : ℝ}
    (h0 : 0 < S0hat - ε) (h1 : 0 < S1hat - ε)
    (hr0 : |S0hat - ∑ d, R.ρ d| ≤ ε)
    (hr1 : |S1hat - ∑ d, R.ρ d * Real.cos (R.θ d)| ≤ ε) :
    Real.log (S0hat - ε) - Real.log (S1hat + ε) ≤ R.tension ∧
      R.tension ≤ Real.log (S0hat + ε) - Real.log (S1hat - ε) := by
  rw [tension_eq_log_sub R (cosAvg_pos_of_certified R h1 hr1)]
  exact attenuation_weyl_certified h0 h1 hr0 hr1

#print axioms tension_certified_interval

/-- A certified upper endpoint below `κ₀YM` gives `R.tension < MassGap.κ₀YM`.
The right half of `tension_certified_interval` composed with `MassGap.confinement_of_certified`. The
strict comparison is made against the endpoint `log (S0hat + ε) − log (S1hat − ε)`, so the conclusion
costs the four read hypotheses plus that inequality; the left endpoint plays no part.

DERIVED: `0` appears twice, as the sign condition on `S0hat − ε` and on `S1hat − ε`. -/
theorem tension_lt_floor_of_certified {N : ℕ} (R : Moment.Read N) {S0hat S1hat ε : ℝ}
    (h0 : 0 < S0hat - ε) (h1 : 0 < S1hat - ε)
    (hr0 : |S0hat - ∑ d, R.ρ d| ≤ ε)
    (hr1 : |S1hat - ∑ d, R.ρ d * Real.cos (R.θ d)| ≤ ε)
    (hcert : Real.log (S0hat + ε) - Real.log (S1hat - ε) < MassGap.κ₀YM) :
    R.tension < MassGap.κ₀YM :=
  MassGap.confinement_of_certified (tension_certified_interval R h0 h1 hr0 hr1).2 hcert

#print axioms tension_lt_floor_of_certified

/-! ## 4. Landing the interval on `EvenAperture.μEven` -/

/-- The tension at one even aperture and one coupling, from a certified read.
`μEven a β` is `(readEven a β).tension` definitionally, so `tension_lt_floor_of_certified` applies
with the read taken at `readEven a β`. The aperture `a` and the coupling `β` are fixed throughout,
and the two read values are those of that aperture at that coupling.

DERIVED: `0` appears twice, as the sign condition on `S0hat − ε` and on `S1hat − ε`. -/
theorem μEven_lt_floor_of_certified (a : EvenAp) (β : ℝ) {S0hat S1hat ε : ℝ}
    (h0 : 0 < S0hat - ε) (h1 : 0 < S1hat - ε)
    (hr0 : |S0hat - ∑ d, (readEven a β).ρ d| ≤ ε)
    (hr1 : |S1hat - ∑ d, (readEven a β).ρ d * Real.cos ((readEven a β).θ d)| ≤ ε)
    (hcert : Real.log (S0hat + ε) - Real.log (S1hat - ε) < MassGap.κ₀YM) :
    μEven a β < MassGap.κ₀YM := by
  show (readEven a β).tension < MassGap.κ₀YM
  exact tension_lt_floor_of_certified _ h0 h1 hr0 hr1 hcert

#print axioms μEven_lt_floor_of_certified

/-- `∃ a : EvenAp, ∀ β : ℝ, μEven a β < MassGap.κ₀YM`, from a certified read at one aperture.
The inputs are one even aperture `a`, two read functions `S0hat S1hat : ℝ → ℝ` of the coupling, and a
single error bar `ε`, followed by five conditions each holding at every coupling: the two
positivities `0 < S0hat β − ε` and `0 < S1hat β − ε`, the two error bounds, and the certified upper
endpoint below `κ₀YM`. `μEven_lt_floor_of_certified` supplies each instance.

`ε` is bound outside the quantifier over couplings, so it is one bar for the whole half-line, and no
hypothesis constrains its size. The bound `a` in the conclusion shadows the argument `a`, which is
the witness supplied. `β` ranges over all of `ℝ`, so `h1` is a condition on the read at negative
couplings too.

DERIVED: `0` appears twice, as the sign condition on `S0hat β − ε` and on `S1hat β − ε`. -/
theorem confines_at_an_aperture_of_certified
    (a : EvenAp) (S0hat S1hat : ℝ → ℝ) (ε : ℝ)
    (h0 : ∀ β, 0 < S0hat β - ε) (h1 : ∀ β, 0 < S1hat β - ε)
    (hr0 : ∀ β, |S0hat β - ∑ d, (readEven a β).ρ d| ≤ ε)
    (hr1 : ∀ β, |S1hat β
        - ∑ d, (readEven a β).ρ d * Real.cos ((readEven a β).θ d)| ≤ ε)
    (hcert : ∀ β, Real.log (S0hat β + ε) - Real.log (S1hat β - ε) < MassGap.κ₀YM) :
    ∃ a : EvenAp, ∀ β : ℝ, μEven a β < MassGap.κ₀YM :=
  ⟨a, fun β => μEven_lt_floor_of_certified a β (h0 β) (h1 β) (hr0 β) (hr1 β) (hcert β)⟩

#print axioms confines_at_an_aperture_of_certified

/-! ## 5. The entropy of the read -/

/-- The entropy of `Moment.Read.p` lies between `0` and `log ((N : ℝ) + 1)`.
`entropy_nonneg_le_log` at `n := N + 1`, with `R.p_nonneg` and `R.p_sum` as its two hypotheses and
the cast `((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1` rewritten. `Moment.Read N` indexes its lags by
`Fin (N + 1)`, so the upper endpoint is the logarithm of the number of lags. No constant is supplied
from outside: both endpoints come from the index type.

DERIVED: `0` is the left endpoint; `1` is the offset in `(N : ℝ) + 1`, the cardinality of the index
`Fin (N + 1)`. -/
theorem read_entropy_bounds {N : ℕ} (R : Moment.Read N) :
    0 ≤ ∑ d, Real.negMulLog (R.p d) ∧
      ∑ d, Real.negMulLog (R.p d) ≤ Real.log ((N : ℝ) + 1) := by
  have h := entropy_nonneg_le_log (n := N + 1) (by omega) R.p
    (fun d => R.p_nonneg d) R.p_sum
  rw [show (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 by push_cast; ring] at h
  exact h

#print axioms read_entropy_bounds

/-- The fill fraction of `Moment.Read.p` lies between `1 / ((N : ℝ) + 1)` and `1`.
The third and fourth conjuncts of `fill_fraction_entropy_bounds` at `n := N + 1`. The quantity is
`2 ^ (H / Real.log 2) / ((N : ℝ) + 1)` with `H` the natural-log entropy of `R.p`. It is a statement
about how the read's weight is spread over its lags; `R.θ` does not occur in it, so it says nothing
about where that weight sits (`antipodeRead_entropy_eq_zero`).

DERIVED: `1` is the offset in `(N : ℝ) + 1`, the cardinality of `Fin (N + 1)`, the numerator of the
lower endpoint and the upper endpoint itself; `2` is the base of the exponential and the base of the
logarithm dividing the entropy. -/
theorem read_fill_fraction_bounds {N : ℕ} (R : Moment.Read N) :
    1 / ((N : ℝ) + 1)
        ≤ (2 : ℝ) ^ ((∑ d, Real.negMulLog (R.p d)) / Real.log 2) / ((N : ℝ) + 1) ∧
      (2 : ℝ) ^ ((∑ d, Real.negMulLog (R.p d)) / Real.log 2) / ((N : ℝ) + 1) ≤ 1 := by
  have h := fill_fraction_entropy_bounds (n := N + 1) (by omega) R.p
    (fun d => R.p_nonneg d) R.p_sum
  rw [show (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 by push_cast; ring] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

#print axioms read_fill_fraction_bounds

/-! ## 6. The tension reads an absolute value

`Real.log` is even, so `Moment.Read.tension` is `−log |⟨cos θ⟩_p|`. The statements below are
consequences of that, ending with `Substrate.antipodeRead` as a worked case. -/

/-- `R.tension = −log |∑ d, R.p d * cos (R.θ d)|`, by `Real.log_abs`. Unconditional: no sign
hypothesis is taken on the cosine average, and the equation holds for every `R : Moment.Read N`.

DERIVED: no numeral appears in the statement. -/
theorem tension_eq_neg_log_abs {N : ℕ} (R : Moment.Read N) :
    R.tension = - Real.log |∑ d, R.p d * Real.cos (R.θ d)| := by
  show - Real.log (∑ d, R.p d * Real.cos (R.θ d)) = _
  rw [Real.log_abs]

#print axioms tension_eq_neg_log_abs

/-- A read whose cosine average is below `−3 ^ (−1/4)` satisfies `R.tension < MassGap.κ₀YM`.
The hypothesis is one-sided and negative: `∑ d, R.p d * cos (R.θ d) < −(3 ^ (−1/4))`. Through
`tension_eq_neg_log_abs` the absolute value then exceeds `3 ^ (−1/4)`, and unfolding `MassGap.κ₀YM`
closes the comparison. `Moment.Read.tension_lt_floor_of_cosAvg` reaches the same conclusion from the
opposite-sign hypothesis `⟨cos θ⟩ > 3 ^ (−1/4)`, which this hypothesis excludes; the conclusion here
is about `tension` alone and says nothing about decay.

DERIVED: `3` is the base of the constant `3 ^ (−1/4)` the hypothesis negates, and `1` and `4` are the
numerator and denominator of its exponent `−1/4`. -/
theorem reads_confined_of_cosAvg_lt_neg {N : ℕ} (R : Moment.Read N)
    (h : ∑ d, R.p d * Real.cos (R.θ d) < -((3 : ℝ) ^ (-(1 : ℝ) / 4))) :
    R.tension < MassGap.κ₀YM := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hneg : ∑ d, R.p d * Real.cos (R.θ d) < 0 := by linarith
  have hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < |∑ d, R.p d * Real.cos (R.θ d)| := by
    rw [abs_of_neg hneg]; linarith
  have hlog := Real.log_lt_log ht hc
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hlog
  rw [tension_eq_neg_log_abs]
  simp only [MassGap.κ₀YM]
  linarith

#print axioms reads_confined_of_cosAvg_lt_neg

/-- `Substrate.antipodeRead k` has phase `π` at the lag `Substrate.antipode k`.
The read's phases are `θ d = 2π d / (N + 1)` at `N = 2 * k + 1`, and `Substrate.antipode k` is the
element of `Fin (2 * k + 1 + 1)` whose value is `k + 1`, half the period. The proof casts that value
and cancels.

DERIVED: no numeral appears in the statement; `k` is the only argument, and the period is fixed
inside `Substrate.antipodeRead`'s own definition. -/
theorem antipodeRead_theta_eq_pi (k : ℕ) :
    (MassGap.Substrate.antipodeRead k).θ (MassGap.Substrate.antipode k) = Real.pi := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hv : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) = k + 1 := rfl
  have hr : ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℝ) = (k : ℝ) + 1 := by
    show (((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℕ) : ℝ) = _
    rw [hv]; push_cast; ring
  show 2 * Real.pi * ((MassGap.Substrate.antipode k : Fin (2 * k + 1 + 1)) : ℝ)
      / (((2 * k + 1 : ℕ) : ℝ) + 1) = Real.pi
  rw [hr, show (((2 * k + 1 : ℕ) : ℝ) + 1) = 2 * ((k : ℝ) + 1) by push_cast; ring]
  field_simp

#print axioms antipodeRead_theta_eq_pi

/-- The cosine average of `Substrate.antipodeRead k` is `−1`.
`Substrate.antipodeRead_sum` makes `p` equal to `ρ`, which is the indicator of
`Substrate.antipode k`, so the sum collapses to a single term and
`antipodeRead_theta_eq_pi` evaluates the cosine there through `Real.cos_pi`.

DERIVED: `1` is the value of `cos π` taken with its sign, the right-hand side `−1`. -/
theorem antipodeRead_cosAvg_eq_neg_one (k : ℕ) :
    ∑ d, (MassGap.Substrate.antipodeRead k).p d
        * Real.cos ((MassGap.Substrate.antipodeRead k).θ d) = -1 := by
  classical
  have hsum := MassGap.Substrate.antipodeRead_sum k
  have hp : ∀ d, (MassGap.Substrate.antipodeRead k).p d
      = (MassGap.Substrate.antipodeRead k).ρ d := by
    intro d; simp [Moment.Read.p, hsum]
  have hterm : ∀ d : Fin (2 * k + 1 + 1),
      (MassGap.Substrate.antipodeRead k).p d
          * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)
        = if d = MassGap.Substrate.antipode k then
            Real.cos ((MassGap.Substrate.antipodeRead k).θ d) else 0 := by
    intro d
    rw [hp d]
    show (if d = MassGap.Substrate.antipode k then (1 : ℝ) else 0) * _ = _
    split <;> ring
  rw [Finset.sum_congr rfl (fun d _ => hterm d),
    Finset.sum_ite_eq' Finset.univ (MassGap.Substrate.antipode k)
      (fun d => Real.cos ((MassGap.Substrate.antipodeRead k).θ d))]
  simp only [Finset.mem_univ, if_true]
  rw [antipodeRead_theta_eq_pi k, Real.cos_pi]

#print axioms antipodeRead_cosAvg_eq_neg_one

/-- `(Substrate.antipodeRead k).tension < MassGap.κ₀YM`, for every `k`.
Its cosine average is `−1` (`antipodeRead_cosAvg_eq_neg_one`) and `Real.log` is even, so the tension
is `−log |−1| = 0`; `MassGap.κ₀YM_pos` closes it. The same read fails the hypothesis
`⟨cos θ⟩ > 3 ^ (−1/4)` of `Moment.Read.tension_lt_floor_of_cosAvg`, and is the read
`antipodeRead_moment_eq_quarter_sq` uses on the second-moment side, so the two criteria disagree on
it.

DERIVED: no numeral appears in the statement. -/
theorem antipodeRead_reads_confined (k : ℕ) :
    (MassGap.Substrate.antipodeRead k).tension < MassGap.κ₀YM := by
  have h0 : (MassGap.Substrate.antipodeRead k).tension = 0 := by
    show - Real.log (∑ d, (MassGap.Substrate.antipodeRead k).p d
      * Real.cos ((MassGap.Substrate.antipodeRead k).θ d)) = 0
    rw [antipodeRead_cosAvg_eq_neg_one k, ← Real.log_abs]
    simp
  rw [h0]
  exact MassGap.κ₀YM_pos

#print axioms antipodeRead_reads_confined

/-- The entropy of `Substrate.antipodeRead k` is `0`.
Its `p` takes only the values `0` and `1`, and `Real.negMulLog` vanishes at both, so every term of
the sum vanishes. Read against `read_fill_fraction_bounds`, this read sits at the lower endpoint
`1 / ((N : ℝ) + 1)` of the fill fraction, while `antipodeRead_reads_confined` puts its tension below
`κ₀YM`: the entropy records how the weight is spread over lags and the tension records where it
sits, so neither bounds the other.

DERIVED: `0` is the value of the entropy sum, the left endpoint of `read_entropy_bounds`. -/
theorem antipodeRead_entropy_eq_zero (k : ℕ) :
    ∑ d, Real.negMulLog ((MassGap.Substrate.antipodeRead k).p d) = 0 := by
  classical
  have hsum := MassGap.Substrate.antipodeRead_sum k
  have hp : ∀ d, (MassGap.Substrate.antipodeRead k).p d
      = (MassGap.Substrate.antipodeRead k).ρ d := by
    intro d; simp [Moment.Read.p, hsum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rw [hp d]
  show Real.negMulLog (if d = MassGap.Substrate.antipode k then (1 : ℝ) else 0) = 0
  split
  · simp [Real.negMulLog]
  · simp [Real.negMulLog]

#print axioms antipodeRead_entropy_eq_zero

/-! ## 7. Footprints -/

section Audit
#print axioms attenuation_interval_bounds
#print axioms weyl_top_of_rayleigh
#print axioms attenuation_weyl_certified
#print axioms resolved_count_certified
#print axioms separated_of_disjoint_intervals
#print axioms noise_floor_monotone
#print axioms resolved_dim_antitone
#print axioms ratio_bounds
#print axioms entropy_nonneg_le_log
#print axioms fill_fraction_entropy_bounds
#print axioms spectral_read_congruence
#print axioms spectral_read_orthogonal
#print axioms cosAvg_eq_ratio
#print axioms tension_eq_log_sub
#print axioms cosAvg_pos_of_certified
#print axioms tension_certified_interval
#print axioms tension_lt_floor_of_certified
#print axioms μEven_lt_floor_of_certified
#print axioms confines_at_an_aperture_of_certified
#print axioms read_entropy_bounds
#print axioms read_fill_fraction_bounds
#print axioms tension_eq_neg_log_abs
#print axioms reads_confined_of_cosAvg_lt_neg
#print axioms antipodeRead_theta_eq_pi
#print axioms antipodeRead_cosAvg_eq_neg_one
#print axioms antipodeRead_reads_confined
#print axioms antipodeRead_entropy_eq_zero
end Audit

end MassGap.ReadLayer
