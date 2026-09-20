import Mathlib
import MassGap.EvenAperture
import MassGap.Substrate

/-!
# MassGap.ReadLayer — the read layer's certified intervals, imported rather than cited

`Certify.lean`'s header cites three theorems by name — `attenuation_weyl_certified`,
`resolved_count_certified`, `separated_of_disjoint_intervals` — and says "those are read-layer facts,
so they live with the read layer". They live in a companion Lean development that this tree has never
imported, so the citation was prose. This file carries them across.

**THE PORT IS VERBATIM AND COSTS NOTHING.** Both developments pin `leanprover/lean4:v4.31.0` and
mathlib `v4.31.0` at the same revision, so no statement or proof needed adapting. No cross-project
dependency is introduced: the proofs are copied, not required.

## What the read layer supplies, and what it does not

It supplies **certified intervals**: given a read-side quantity and an error bar, it encloses the true
quantity. It supplies **no absolute mode bound**. Every spectral statement below is about a RATIO
(`log λ₁ − log r`) or a COUNT (`#{λ > edge}`) relative to a read. There is no theorem here — and none
in the development this ports from — of the form `‖eigenvalue‖ ≤ ρ < 1`.

That matters for `Aperture.lean`. `finite_flow_decays`, `gap_at_finite_F` and `gap_of_confinement`
take `∀ k ∈ s, ‖μ k‖ ≤ exp(−κ)` as a HYPOTHESIS, and nothing here discharges it. The dichotomy those
theorems name — a mode on the unit circle, or a strict margin — is not decided by this layer. What
this layer does decide is the OTHER open input, `μ < κ₀`, and it decides it as an interval.

## The join, and it is one identity

`Moment.Read.tension` is DEFINED as `−log ⟨cos θ⟩_p`. Since `p = ρ/Σρ`, that is

    tension = log (Σ ρ) − log (Σ ρ cos θ) = log S(0) − log S(2π/(N+1)),

which is exactly the shape `attenuation_interval_bounds` propagates a Weyl band through, with
`λ₁ := S(0)` and `r := S(2π/(N+1))`. The identity is asserted in `Moment.Read.tension`'s docstring
("`= log(S(0)/S(2π/N))`") and was not proved anywhere; `tension_eq_log_sub` proves it, and
`tension_certified_interval` is the composition. `confines_at_an_aperture_of_certified` lands the
result on `∃ a : EvenAp, ∀ β, μEven a β < κ₀YM` — which is `ApertureRoute.ConfinesAtAnAperture`
unfolded, the hypothesis the flagship actually consumes.

**WHAT THAT DOES AND DOES NOT ESTABLISH.** It converts a read of two structure-factor values, with an
error bar, into confinement. The error bar is supplied by the caller. Nothing here measures anything,
and nothing here proves the bar is small enough at any coupling. It replaces an opaque hypothesis
with a hypothesis about two numbers the read reports, which is a change in what has to be measured,
not a discharge.

## The sign is not read, and that is a defect in the definition

`Real.log` is even (`Real.log_abs`), so `tension` reads the MAGNITUDE of the cosine average. A read
that is maximally ANTI-correlated at the probed wavenumber therefore reports tension `0` — the most
confined value available. `reads_confined_of_cosAvg_lt_neg` proves that for any such read, and
`antipodeRead_reads_confined` proves it of `Substrate.antipodeRead`, the very read this tree exhibits
as the extremal obstruction to the second-moment route. That read satisfies `μ < κ₀`.

This is not a defect in the intended route: `Moment.Read.tension_lt_floor_of_cosAvg` requires
`⟨cos θ⟩ > 3^{−1/4}`, which excludes it. It IS a defect in `ConfinesAtAnAperture`, which is stated on
`μEven a β < κ₀YM` with no positivity guard, and is therefore satisfiable by a degenerate read.
`cosAvg_pos_of_certified` records that the certified route below never produces one, because its
`0 < Ŝ₁ − ε` hypothesis forces the cosine average positive.

## The entropy layer joins, and it does not bound the tension

`Moment.Read.p` is a probability vector with both field lemmas proved, so the entropy bound applies
verbatim: `0 ≤ H(p) ≤ log(N+1)`, and the fill fraction `φ = 2^H/(N+1) ∈ [1/(N+1), 1]`, derived from
the read's own distribution with no supplied constant. It bounds the aperture's fill and NOT the
tension: `antipodeRead` has entropy exactly `0`, the minimum, and cosine average `−1`. Entropy is
blind to WHERE the mass sits, and the tension is a statement about exactly that.

All theorems are machine-checked; `#print axioms` follows every declaration.
-/

namespace MassGap.ReadLayer

open scoped BigOperators Matrix
open MassGap.EvenAperture

/-! ## 1. The certified-interval layer

Ported verbatim. These are the three theorems `Certify.lean` cites, plus the two monotonicity
statements the noise floor and the resolved dimension rest on. -/

/-- **Weyl-certified attenuation, monotone-propagation step.**
Given eigenvalue bounds `λ₁ ∈ [lo1, hi1]`, `r ∈ [lor, hir]` (all positive), the attenuation
`log λ₁ − log r`, increasing in `λ₁` and decreasing in `r`, lies in
`[log lo1 − log hir, log hi1 − log lor]`. Weyl's inequality supplies the eigenvalue bounds; this
propagates them through the read. -/
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

/-- **The Weyl estimate for the top eigenvalue.**
The top of a supremum of Rayleigh quotients moves by at most the perturbation. In Courant–Fischer
form `λ₁ = ⨆ x, ⟪C x, x⟫` over the unit sphere; if `|⟪(Ĉ − C) x, x⟫| ≤ ε` at every test point (in
particular `ε = ‖Ĉ − C‖₂`), then `|λ̂₁ − λ₁| ≤ ε`. Proved at the level of the two suprema, over any
nonempty index of bounded Rayleigh values. -/
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

/-- **The certified attenuation interval, end-to-end.**
Composing the Weyl eigenvalue bound `|λ̂₁ − λ₁| ≤ ε`, `|r̂ − r| ≤ ε` with the monotone propagation
certifies the attenuation from the READ eigenvalues: the true `log λ₁ − log r` lies in
`[log(λ̂₁ − ε) − log(r̂ + ε), log(λ̂₁ + ε) − log(r̂ − ε)]`.

This is the theorem `Certify.lean` cites as `[E, Lem 6.2]` and is what
`Certify.confinement_of_certified` consumes as its `μ ≤ α_hi`. -/
theorem attenuation_weyl_certified {lam1hat rhat lam1 r ε : ℝ}
    (hlo1 : 0 < lam1hat - ε) (hlor : 0 < rhat - ε)
    (h1 : |lam1hat - lam1| ≤ ε) (hr : |rhat - r| ≤ ε) :
    Real.log (lam1hat - ε) - Real.log (rhat + ε) ≤ Real.log lam1 - Real.log r ∧
      Real.log lam1 - Real.log r ≤ Real.log (lam1hat + ε) - Real.log (rhat - ε) := by
  rw [abs_le] at h1 hr
  exact attenuation_interval_bounds hlo1 hlor (by linarith [h1.2]) (by linarith [h1.1])
    (by linarith [hr.2]) (by linarith [hr.1])

#print axioms attenuation_weyl_certified

/-- **The certified resolved count.**
The count analogue. Read eigenvalues `lamhat` differ from the true `lam` by at most `ε` (Weyl), and
the noise edge is a fixed function of the shape. Then the count of TRUE eigenvalues above the edge is
enclosed by the two read-side counts, `K_lo ≤ K_true ≤ K_hi`.

**IT COUNTS A SUPPLIED FAMILY.** Both `lam` and `lamhat` are arguments, so this bounds the
cardinality of a mode set only once such a set exists; it cannot be used to derive one. The family
itself is what `Complete.WilsonSpectral` provides, and at the Clay extent that is now proved —
`SlabQuadratic.wilsonSpectral (hβ : 0 ≤ β)` gives a `Spectral.PeriodicSpectralForm 4 (wilsonCorrAt 3 β)`,
whose `Idx`, `w` and `lam` are exactly such a family. What it does not give is a COUNT: the form's
index is whatever the construction supplies, and `SpectralFour` shows two modes always suffice at
this extent. -/
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

/-- **Certified separation.**
Two ensemble means lie in their certified intervals. If the intervals do not overlap, the true means
are ordered: the two populations are distinct. The two-sided form of
`Certify.confinement_of_certified`, which is its one-sided special case at a constant. -/
theorem separated_of_disjoint_intervals {Ec Ed mc tc md td : ℝ}
    (hEc : |Ec - mc| ≤ tc) (hEd : |Ed - md| ≤ td) (hgap : mc + tc < md - td) :
    Ec < Ed := by
  have hc := abs_le.mp hEc
  have hd := abs_le.mp hEd
  linarith [hc.2, hd.1]

#print axioms separated_of_disjoint_intervals

/-- **The noise floor rises with the significance quantile.**
The Johnstone/Tracy–Widom floor `Φ(q) = sqrt(σ²·(μ + q·ς_J))` is monotone in `q`: a stricter
false-alarm rate gives a higher floor. This is the floor `Certify.confinement_iff_contrast_lt_rpow`
divides by — its `contrast = λ₁/Φ` — so a stricter `q` lowers the contrast and makes the confinement
criterion easier, which is the direction a certificate must be read in. -/
theorem noise_floor_monotone {σ2 μ ςJ q₁ q₂ : ℝ}
    (hσ : 0 ≤ σ2) (hς : 0 ≤ ςJ) (hq : q₁ ≤ q₂) :
    Real.sqrt (σ2 * (μ + q₁ * ςJ)) ≤ Real.sqrt (σ2 * (μ + q₂ * ςJ)) := by
  apply Real.sqrt_le_sqrt
  have hinner : q₁ * ςJ ≤ q₂ * ςJ := mul_le_mul_of_nonneg_right hq hς
  exact mul_le_mul_of_nonneg_left (by linarith) hσ

#print axioms noise_floor_monotone

/-- **The resolved dimension is antitone in the floor.**
`K_signal = #{k : sₖ > Φ}` is nonincreasing in `Φ`, by monotonicity of the counting filter. -/
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

Also ported verbatim. These apply to `Moment.Read.p` directly, because it is a probability vector
with `p_nonneg` and `p_sum` already proved. -/

/-- **A dominating weight's share lies in `[1/n, 1]`.**
Taking `w` the singular-value power spectrum bounds the fill fraction; taking `w` the ordered
correlation spectrum bounds the Strehl ratio. -/
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

/-- **The entropy bound.**
For a probability vector `q` on `Fin n` (`n ≥ 1`) the natural-log Shannon entropy
`H q = ∑ negMulLog (q i)` obeys `0 ≤ H q ≤ log n`. The lower bound is termwise; the upper bound is
Gibbs/Jensen, concavity of `negMulLog` on `[0,∞)` against the uniform weights `1/n`. -/
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

/-- **The fill fraction, from the signal's own entropy.**
Exponentiating the entropy bound: with the bit-entropy `H₂ = H/log 2`, `2^{H₂} ∈ [1, n]` and the fill
fraction `φ = 2^{H₂}/n ∈ [1/n, 1]`. No constant is supplied — the resolution is read off the
distribution. -/
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

/-- **A spectral read is a congruence invariant.**
A read `f` depending only on the operator's characteristic polynomial is unchanged by conjugation by
an inverse pair. This is the spectral form of "entropy is coordinate-free" that `Apriori.lean`'s A2
discussion cites; A2 itself is proved in this tree without it. -/
theorem spectral_read_congruence {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] {α : Type*}
    (f : Polynomial R → α) (P C Q : Matrix n n R) (hQP : Q * P = 1) :
    f ((P * C * Q).charpoly) = f (C.charpoly) := by
  have hcong : (P * C * Q).charpoly = C.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  rw [hcong]

#print axioms spectral_read_congruence

/-- **And under an orthogonal congruence**, the action of a rotation: every spectral read is isotropic
under `O(n)` and its rotation subgroup, the hypercubic point group being the special case. -/
theorem spectral_read_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] {α : Type*}
    (f : Polynomial R → α) (P C : Matrix n n R) (hP : Pᵀ * P = 1) :
    f ((P * C * Pᵀ).charpoly) = f (C.charpoly) :=
  spectral_read_congruence f P C Pᵀ hP

#print axioms spectral_read_orthogonal

/-! ## 3. The join: the tension IS an attenuation

One identity, and the certified interval follows from it. -/

/-- **The cosine average is a ratio of structure factors.** `⟨cos θ⟩_p = S(2π/(N+1)) / S(0)`, because
`p` is `ρ` normalised. Pure algebra of the definition of `Moment.Read.p`. -/
theorem cosAvg_eq_ratio {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * Real.cos (R.θ d)
      = (∑ d, R.ρ d * Real.cos (R.θ d)) / (∑ d, R.ρ d) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  show R.ρ d / (∑ d', R.ρ d') * Real.cos (R.θ d) = _
  ring

#print axioms cosAvg_eq_ratio

/-- **THE TENSION IS AN ATTENUATION.** `μ = log S(0) − log S(2π/(N+1))`, the identity
`Moment.Read.tension`'s docstring asserts and nothing proved. With it, the tension is exactly the
quantity `attenuation_interval_bounds` propagates a Weyl band through, at `λ₁ := S(0)` and
`r := S(2π/(N+1))`.

The hypothesis `0 < Σ ρ cos θ` is the guard that makes the identity meaningful rather than merely
true: `Real.log` is even, so below it the left side reads a magnitude (see §5). -/
theorem tension_eq_log_sub {N : ℕ} (R : Moment.Read N)
    (hc : 0 < ∑ d, R.ρ d * Real.cos (R.θ d)) :
    R.tension = Real.log (∑ d, R.ρ d) - Real.log (∑ d, R.ρ d * Real.cos (R.θ d)) := by
  show - Real.log (∑ d, R.p d * Real.cos (R.θ d)) = _
  rw [cosAvg_eq_ratio, Real.log_div (ne_of_gt hc) (ne_of_gt R.hpos)]
  ring

#print axioms tension_eq_log_sub

/-- **The certified read never produces a degenerate one.** The hypothesis `0 < Ŝ₁ − ε` together with
the error bar forces the true `S(2π/(N+1))` positive, hence the cosine average positive. So the
vacuity of §5 cannot arise on this route. -/
theorem cosAvg_pos_of_certified {N : ℕ} (R : Moment.Read N) {S1hat ε : ℝ}
    (h1 : 0 < S1hat - ε)
    (hr1 : |S1hat - ∑ d, R.ρ d * Real.cos (R.θ d)| ≤ ε) :
    0 < ∑ d, R.ρ d * Real.cos (R.θ d) := by
  have hb := abs_le.mp hr1
  linarith [hb.2]

#print axioms cosAvg_pos_of_certified

/-- **THE CERTIFIED INTERVAL ON THE TENSION.** Given a read of the two structure factors with a Weyl
error bar `ε`, the true tension of the read is enclosed:

    log(Ŝ₀ − ε) − log(Ŝ₁ + ε)  ≤  μ  ≤  log(Ŝ₀ + ε) − log(Ŝ₁ − ε).

`attenuation_weyl_certified` composed with `tension_eq_log_sub`. This is what `Certify.lean`'s header
promised the read layer would supply, said about `Moment.Read.tension` rather than about an abstract
attenuation. -/
theorem tension_certified_interval {N : ℕ} (R : Moment.Read N) {S0hat S1hat ε : ℝ}
    (h0 : 0 < S0hat - ε) (h1 : 0 < S1hat - ε)
    (hr0 : |S0hat - ∑ d, R.ρ d| ≤ ε)
    (hr1 : |S1hat - ∑ d, R.ρ d * Real.cos (R.θ d)| ≤ ε) :
    Real.log (S0hat - ε) - Real.log (S1hat + ε) ≤ R.tension ∧
      R.tension ≤ Real.log (S0hat + ε) - Real.log (S1hat - ε) := by
  rw [tension_eq_log_sub R (cosAvg_pos_of_certified R h1 hr1)]
  exact attenuation_weyl_certified h0 h1 hr0 hr1

#print axioms tension_certified_interval

/-- **A certified upper endpoint below the floor gives confinement of the read.**
`Certify.confinement_of_certified` with the enclosure now proved rather than assumed. -/
theorem tension_lt_floor_of_certified {N : ℕ} (R : Moment.Read N) {S0hat S1hat ε : ℝ}
    (h0 : 0 < S0hat - ε) (h1 : 0 < S1hat - ε)
    (hr0 : |S0hat - ∑ d, R.ρ d| ≤ ε)
    (hr1 : |S1hat - ∑ d, R.ρ d * Real.cos (R.θ d)| ≤ ε)
    (hcert : Real.log (S0hat + ε) - Real.log (S1hat - ε) < MassGap.κ₀YM) :
    R.tension < MassGap.κ₀YM :=
  MassGap.confinement_of_certified (tension_certified_interval R h0 h1 hr0 hr1).2 hcert

#print axioms tension_lt_floor_of_certified

/-! ## 4. Landing it on the hypothesis the flagship consumes -/

/-- **The tension at an even aperture, from a certified read.** `μEven` is `(readEven a β).tension` by
definition, so the certified interval applies to it unchanged. -/
theorem μEven_lt_floor_of_certified (a : EvenAp) (β : ℝ) {S0hat S1hat ε : ℝ}
    (h0 : 0 < S0hat - ε) (h1 : 0 < S1hat - ε)
    (hr0 : |S0hat - ∑ d, (readEven a β).ρ d| ≤ ε)
    (hr1 : |S1hat - ∑ d, (readEven a β).ρ d * Real.cos ((readEven a β).θ d)| ≤ ε)
    (hcert : Real.log (S0hat + ε) - Real.log (S1hat - ε) < MassGap.κ₀YM) :
    μEven a β < MassGap.κ₀YM := by
  show (readEven a β).tension < MassGap.κ₀YM
  exact tension_lt_floor_of_certified _ h0 h1 hr0 hr1 hcert

#print axioms μEven_lt_floor_of_certified

/-- **CONFINEMENT AT ONE APERTURE, FROM A CERTIFIED READ.** The conclusion is
`ApertureRoute.ConfinesAtAnAperture` unfolded — the hypothesis
`ApertureRoute.flagship_of_confinement_at_an_aperture` consumes, and through it the whole flagship.

The inputs are: one even extent `a`; read-side structure factors `Ŝ₀ β`, `Ŝ₁ β` at every coupling;
one error bar `ε` valid at every coupling; and the certified endpoint below the floor at every
coupling.

**WHAT IS AND IS NOT DISCHARGED.** The opaque quantity `μEven a β` is replaced by two numbers the
read reports and an error bar on them. Nothing here establishes any of the four hypotheses, and in
particular nothing here bounds `ε`. The `∀ β` is unrestricted, so the `β → ∞` end that
`ApertureRoute`'s "WHERE THE DIFFICULTY MOVES TO" identifies is untouched: as the correlation
flattens, `Ŝ₁ β → 0` and `h1 : 0 < Ŝ₁ β − ε` fails. That is the same obstruction, now visible as a
positivity condition on a measured number rather than as a moment bound. -/
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

/-! ## 5. The entropy of the read, and what it does not bound -/

/-- **The read's own entropy bound.** `Moment.Read.p` is a probability vector, so `0 ≤ H(p) ≤ log(N+1)`
with no supplied constant: the aperture's resolution is read off the correlation's own distribution
over lags. -/
theorem read_entropy_bounds {N : ℕ} (R : Moment.Read N) :
    0 ≤ ∑ d, Real.negMulLog (R.p d) ∧
      ∑ d, Real.negMulLog (R.p d) ≤ Real.log ((N : ℝ) + 1) := by
  have h := entropy_nonneg_le_log (n := N + 1) (by omega) R.p
    (fun d => R.p_nonneg d) R.p_sum
  rw [show (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 by push_cast; ring] at h
  exact h

#print axioms read_entropy_bounds

/-- **The read's fill fraction.** `φ = 2^{H₂}/(N+1) ∈ [1/(N+1), 1]`, derived from the same entropy.
This is the finite aperture measured in the read's own coordinates — and it is a statement about the
aperture, not about the gap (see `antipodeRead_entropy_eq_zero`). -/
theorem read_fill_fraction_bounds {N : ℕ} (R : Moment.Read N) :
    1 / ((N : ℝ) + 1)
        ≤ (2 : ℝ) ^ ((∑ d, Real.negMulLog (R.p d)) / Real.log 2) / ((N : ℝ) + 1) ∧
      (2 : ℝ) ^ ((∑ d, Real.negMulLog (R.p d)) / Real.log 2) / ((N : ℝ) + 1) ≤ 1 := by
  have h := fill_fraction_entropy_bounds (n := N + 1) (by omega) R.p
    (fun d => R.p_nonneg d) R.p_sum
  rw [show (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 by push_cast; ring] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

#print axioms read_fill_fraction_bounds

/-! ## 6. NEGATIVE CONTROLS: the sign is not read

`Real.log` is even, so `Moment.Read.tension` reports the MAGNITUDE of the cosine average. Everything
below is a consequence of that one fact. -/

/-- **The tension reads a magnitude.** `μ = −log |⟨cos θ⟩_p|`, by `Real.log_abs`. -/
theorem tension_eq_neg_log_abs {N : ℕ} (R : Moment.Read N) :
    R.tension = - Real.log |∑ d, R.p d * Real.cos (R.θ d)| := by
  show - Real.log (∑ d, R.p d * Real.cos (R.θ d)) = _
  rw [Real.log_abs]

#print axioms tension_eq_neg_log_abs

/-- **A read anti-correlated at the probed wavenumber reads CONFINED.** If the cosine average is below
`−3^{−1/4}` — anti-correlated by more than the confinement threshold's own magnitude — then
`μ < κ₀YM`.

This is not a route to the gap; it is a defect in the criterion. `Moment.Read.tension_lt_floor_of_cosAvg`
guards against it by requiring `⟨cos θ⟩ > 3^{−1/4}`. `ApertureRoute.ConfinesAtAnAperture` does not,
so that hypothesis is satisfiable by a read with no decay at all. -/
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

/-- **The antipodal read's cosine average is exactly `−1`.** `Substrate.antipodeRead k` puts all its
weight at lag `k+1` of a period `2k+2`, where `θ = π`. -/
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

/-- The antipodal read's cosine average, computed. -/
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

/-- **THE EXTREMAL OBSTRUCTION IS A CONFINEMENT WITNESS.** `Substrate.antipodeRead` is the read this
tree exhibits to show the second-moment route's constant cannot be improved
(`antipodeRead_moment_eq_quarter_sq`) and that reflection positivity alone leaves the substrate moment
unbounded (`rp_alone_leaves_moment_unbounded`). Its tension is `−log|−1| = 0`, so it satisfies
`μ < κ₀YM`.

So the tension criterion and the moment criterion disagree on this read, and the disagreement is not
conservative: the read that maximally violates the sufficient condition passes the necessary one. -/
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

/-- **AND ITS ENTROPY IS THE MINIMUM.** The antipodal read is a point mass, so `H(p) = 0` — the fill
fraction is `1/(N+1)`, the smallest the aperture admits. Together with
`antipodeRead_reads_confined`: minimum entropy and "confined", and with
`antipodeRead_moment_eq_quarter_sq`: maximum second moment. Entropy is blind to WHERE the mass sits;
the tension is a statement about exactly that, so the entropy layer of §2 bounds the aperture's fill
and bounds the tension in neither direction. -/
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
