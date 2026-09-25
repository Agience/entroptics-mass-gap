import Mathlib
import MassGap.SpectralGap
import MassGap.WilsonReadGap
import MassGap.ContinuumE
import MassGap.ReadRoute

/-!
# MassGap.ReadReduce — the reads of the Wilson transfer operator from one box inequality per observable

`SpectralGap.ReadsClear a Ω k` asks that every read at aperture `2k + 1` of a vector orthogonal to
`Ω` have a positive cosine average and tension below `¼·log 3`. That is a strict inequality on a
ratio of two sums, so it does not pass to limits. This module strengthens it to a uniform margin
`γ > 3^{−1/4}` in a condition linear in the lag profile, carries that condition from the GNS
completion down to the local observables and from the infinite-volume state down to the
free-boundary boxes, and composes the steps.

## The chain

1. `marginSum k γ ρ = ∑_{d < 2k+2} (cos (readAngle k d) − γ)·ρ (circLag d)`, and
   `margin_nonneg_iff`: for a read `R`, `0 ≤ ∑_d (cos θ_d − γ)·ρ_d` exactly when the cosine average
   `∑_d p_d cos θ_d` is at least `γ`. `marginSum_eq_read` identifies the two sums when the read's
   correlation at lag `d` is the profile at `circLag d`, which is how `SpectralGap.ReadsClear` pairs a
   read with a vector.
2. `readsClear_of_readsClearWith` (W3): `ReadsClearWith a Ω k γ`, the linear inequality for every
   `v ⊥ Ω` with profile `c ↦ re ⟪v, aᶜ v⟫`, gives `ReadsClear a Ω k` whenever `3^{−1/4} < γ`.
   `readsClearWith_iff_cosAvg` states the linear inequality at the GNS transfer operator as a cosine
   average of `ContinuumE.transferRead` at least `γ`, vector by vector.
3. `readsClearWith_of_local` (W4): for any `TransferData D`, the inequality for the profile
   `c ↦ D.form x (Tᶜ x)` at every `x` with `D.form x D.vac = 0` gives `ReadsClearWith (opT D) Ω k γ`.
   With `vacSub Ω v = v − ⟪Ω, v⟫ Ω`, the map `v ↦ marginSum k γ (c ↦ re ⟪vacSub Ω v, opTᶜ (vacSub Ω v)⟫)`
   is continuous, so its nonnegative set is closed; at the class of a pair `z`, `vacSub Ω z` is the
   class of a pair `w` orthogonal to the vacuum, whose two components are then orthogonal to `D.vac`
   (`form_vac_eq_zero_of_orth`), and the real part of its profile is the sum of the two real profiles
   (`re_inner_opT_pow_coe`). Density of the pairs in the completion closes the step.
4. `localReads_of_boxReads` (W5): at the gauge-invariant Wilson data, the local inequality follows from
   `BoxReadsClearWith`: for each gauge-invariant half-space observable `x` and each `ε > 0`, along the
   free-boundary boxes `mixCube τ p n` the margin sum of the box's connected reflected-shifted profile
   `boxConn` is eventually at least `−ε`. Under `htend` that slack condition is exactly `0 ≤` the
   limit state's margin sum of the connected profile (`boxSlack_iff`); at
   `ν(θx) = D.form x D.vac = 0` the connected profile is `c ↦ D.form x (Tᶜ x)`
   (`GaugeInvariantAlgebra.gaugeInv_form_pow`). `boxReads_of_localReads` is the converse.
5. `wilson_readsClear_of_boxReads` composes 2–4, at any real `β`; `wilson_gap_of_boxReads` adds
   `WilsonReadGap.wilson_gap_of_reads`: the vacuum complement is contracted at a rate `ρ < 1` with
   `ρ^{k+1} = 12(1 − 3^{−1/4})/8`, at every `β ≥ 0`; `wilson_clay_gap_of_boxReads` adds
   `ReadRoute.wilson_gaugeInv_clay_gap_of_reads`, also at `β ≥ 0`: the spectrum in `{1} ∪ [0, ρ]`
   with top `1`.

## Scope

`BoxReadsClearWith` and the limit state `htend` are hypotheses of the chain; nothing here proves
`htend`, or `BoxReadsClearWith` at a positive coupling. At `β = 0`,
`boxReadsClearWith_at_zero_coupling` proves `BoxReadsClearWith` for every `γ ≤ 1`, and with the
limit state of `ClayCapstone.wilson_htend_at_zero_coupling` the hypotheses of
`wilson_clay_gap_of_boxReads` hold together there. `γ` is the caller's. `BoxReadsClearWith`
quantifies over every gauge-invariant half-space observable and every slack `ε > 0`, one eventual
inequality in finitely many free-boundary box expectations each; `boxReadsClearWith_of_eventually`
derives it from the same inequality without slack.

What the reduction keeps. W4 and W5 lose nothing: the class of `(x, 0)` gives the local inequality
back from `ReadsClearWith`, and at `x − ν(θx)·1` the form profile is the connected profile of `x`,
so under `htend` the local inequality gives `BoxReadsClearWith` back through `boxSlack_iff`
(`boxReads_of_localReads`). W3 is sufficient only: `ReadsClear` asks each vector for a cosine
average above `3^{−1/4}`, `ReadsClearWith` asks every vector for at least one `γ > 3^{−1/4}`. By
`ReadConverse.modeCosAvg_antitone` the least cosine average on the vacuum complement is
`modeCosAvg k` at the top of its spectrum, so at `β ≥ 0` some `γ > 3^{−1/4}` has
`BoxReadsClearWith` exactly when `opT` contracts the complement below the root `r*` of
`modeCosAvg k r = 3^{−1/4}` (argued, not proved): `r* = 0.1365, 0.2888, 0.9788` at
`k = 1, 3, 255` against the returned `ρ = 0.6002, 0.7747, 0.9960` (computed, not proved). The box
input is that gap stated through the boxes, not a weaker condition.
-/

namespace MassGap.ReadReduce

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.ClayCapstone MassGap.ReflectionHalfSpace

/-! ## 1. The margin sum, and the cosine average it encodes -/

section Margin

/-- The lag angle at aperture `2k + 1`: `2π·d / ((2k + 1) + 1)`. It is the angle `Moment.Read.θ`
assigns to lag `d` of a read on `Fin (2k + 1 + 1)` (`theta_eq_readAngle`).

DERIVED: the first `2` is the `2π` of a full turn; each `2 * k + 1` spells the aperture; each
remaining `1` is the `+ 1` giving the `2k + 2` lags, in the index type and in the angle's
denominator. -/
noncomputable def readAngle (k : ℕ) (d : Fin (2 * k + 1 + 1)) : ℝ :=
  2 * Real.pi * (d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1)

/-- A read at aperture `2k + 1` has angle `readAngle k d` at lag `d`; both sides unfold to the same
term.

DERIVED: `2` and `1` spell the aperture `2k + 1`; the last `1` is the `+ 1` of the lag arity. -/
theorem theta_eq_readAngle {k : ℕ} (R : Moment.Read (2 * k + 1)) (d : Fin (2 * k + 1 + 1)) :
    R.θ d = readAngle k d := rfl

#print axioms theta_eq_readAngle

/-- The margin sum of a lag profile `ρ : ℕ → ℝ` at aperture `2k + 1` and margin `γ`:
`∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · ρ (circLag d)`. It is linear in `ρ`.

DERIVED: `2` and `1` spell the aperture `2k + 1`; the last `1` is the `+ 1` of the lag arity. -/
noncomputable def marginSum (k : ℕ) (γ : ℝ) (ρ : ℕ → ℝ) : ℝ :=
  ∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ) * ρ (Moment.circLag d)

/-- Equal profiles have equal margin sums.

DERIVED: no numeral occurs. -/
theorem marginSum_congr (k : ℕ) (γ : ℝ) {f g : ℕ → ℝ} (h : ∀ c, f c = g c) :
    marginSum k γ f = marginSum k γ g :=
  congrArg (marginSum k γ) (funext h)

#print axioms marginSum_congr

/-- The margin sum of a sum of profiles is the sum of the margin sums.

DERIVED: no numeral occurs. -/
theorem marginSum_add (k : ℕ) (γ : ℝ) (f g : ℕ → ℝ) :
    marginSum k γ (fun c => f c + g c) = marginSum k γ f + marginSum k γ g := by
  show ∑ d : Fin (2 * k + 1 + 1),
        (Real.cos (readAngle k d) - γ) * (f (Moment.circLag d) + g (Moment.circLag d))
      = ∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ) * f (Moment.circLag d)
        + ∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ) * g (Moment.circLag d)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => by ring)

#print axioms marginSum_add

/-- If each lag of a family of profiles `f x` depends continuously on `x`, so does the margin sum.

DERIVED: no numeral occurs. -/
theorem continuous_marginSum {X : Type*} [TopologicalSpace X] (k : ℕ) (γ : ℝ)
    (f : X → ℕ → ℝ) (hf : ∀ c, Continuous fun x => f x c) :
    Continuous fun x => marginSum k γ (f x) := by
  show Continuous fun x => ∑ d : Fin (2 * k + 1 + 1),
    (Real.cos (readAngle k d) - γ) * f x (Moment.circLag d)
  exact continuous_finsetSum _ (fun d _ => continuous_const.mul (hf _))

#print axioms continuous_marginSum

/-- If each lag of a family of profiles `f i` converges along `l` to `g c`, the margin sums converge
to the margin sum of `g`.

DERIVED: no numeral occurs. -/
theorem tendsto_marginSum {ι : Type*} {l : Filter ι} (k : ℕ) (γ : ℝ)
    (f : ι → ℕ → ℝ) (g : ℕ → ℝ) (h : ∀ c, Filter.Tendsto (fun i => f i c) l (nhds (g c))) :
    Filter.Tendsto (fun i => marginSum k γ (f i)) l (nhds (marginSum k γ g)) := by
  show Filter.Tendsto
    (fun i => ∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ) * f i (Moment.circLag d)) l
    (nhds (∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ) * g (Moment.circLag d)))
  exact tendsto_finsetSum _ (fun d _ => (h _).const_mul _)

#print axioms tendsto_marginSum

/-- **The margin sum is the read's own linear form.** For a read `R` at aperture `2k + 1` whose
correlation at lag `d` is `ρ (circLag d)`, `marginSum k γ ρ = ∑_d (cos (R.θ d) − γ) · R.ρ d`.

DERIVED: `2` and `1` spell the aperture `2k + 1`. -/
theorem marginSum_eq_read {k : ℕ} (γ : ℝ) (R : Moment.Read (2 * k + 1)) (ρ : ℕ → ℝ)
    (hR : ∀ d, R.ρ d = ρ (Moment.circLag d)) :
    marginSum k γ ρ = ∑ d, (Real.cos (R.θ d) - γ) * R.ρ d := by
  show ∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ) * ρ (Moment.circLag d) = _
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [hR d, theta_eq_readAngle R d]

#print axioms marginSum_eq_read

/-- **The linear form is the cosine-average floor.** For a read `R` and any real `γ`:
`0 ≤ ∑_d (cos (R.θ d) − γ) · R.ρ d` exactly when `γ ≤ ∑_d R.p d · cos (R.θ d)`. The cosine average is
`(∑ ρ cos θ) / ∑ ρ` with `∑ ρ > 0` (`R.hpos`), so the two inequalities differ by that positive factor.

DERIVED: `0` is the sign of the linear form. -/
theorem margin_nonneg_iff {n : ℕ} (R : Moment.Read n) (γ : ℝ) :
    0 ≤ ∑ d, (Real.cos (R.θ d) - γ) * R.ρ d ↔ γ ≤ ∑ d, R.p d * Real.cos (R.θ d) := by
  have hS : 0 < ∑ d, R.ρ d := R.hpos
  have hexp : ∑ d, (Real.cos (R.θ d) - γ) * R.ρ d
      = (∑ d, R.ρ d * Real.cos (R.θ d)) - γ * ∑ d, R.ρ d := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  have hp : ∑ d, R.p d * Real.cos (R.θ d) = (∑ d, R.ρ d * Real.cos (R.θ d)) / ∑ d, R.ρ d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold Moment.Read.p
    ring
  rw [hexp, hp, le_div_iff₀ hS]
  constructor
  · intro h
    linarith
  · intro h
    linarith

#print axioms margin_nonneg_iff

end Margin

/-! ## 2. W3 — a margin above the floor clears the floor -/

section Engine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Every vector orthogonal to `Ω` reads at least `γ`, stated linearly.** For every `v` with
`⟪Ω, v⟫ = 0`: `0 ≤ marginSum k γ (c ↦ re ⟪v, aᶜ v⟫)`, that is
`0 ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · re ⟪v, a^{circLag d} v⟫`. At `v = 0` the sum is
`0`. Where the profile of `v` is the correlation of a read, `margin_nonneg_iff` makes the inequality
`γ ≤` that read's cosine average; `readsClearWith_iff_cosAvg` states this at the GNS transfer operator.

DERIVED: `0` is the orthogonality and the sign of the sum. -/
def ReadsClearWith (a : E →L[ℂ] E) (Ω : E) (k : ℕ) (γ : ℝ) : Prop :=
  ∀ v : E, inner ℂ Ω v = 0 →
    0 ≤ marginSum k γ (fun c => RCLike.re (inner ℂ v ((a ^ c) v)))

/-- **W3: a margin above the floor clears the floor.** For `3^{−1/4} < γ`, `ReadsClearWith a Ω k γ`
gives `SpectralGap.ReadsClear a Ω k`. A read `R` whose correlation is `v`'s profile has, by
`marginSum_eq_read` and `margin_nonneg_iff`, cosine average at least `γ > 3^{−1/4} > 0`; so the
average is positive and `Moment.Read.tension_lt_floor_of_cosAvg` puts the tension below `¼·log 3`.

DERIVED: `3`, `1` and `4` spell the floor `3^{−1/4} = e^{−κ₀YM}`, `κ₀YM = ¼·log 3`. -/
theorem readsClear_of_readsClearWith [CompleteSpace E] (a : E →L[ℂ] E) (Ω : E) (k : ℕ) {γ : ℝ}
    (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ) (h : ReadsClearWith a Ω k γ) :
    SpectralGap.ReadsClear a Ω k := by
  intro v hv R hR
  have hlin : 0 ≤ ∑ d, (Real.cos (R.θ d) - γ) * R.ρ d :=
    le_of_le_of_eq (h v hv)
      (marginSum_eq_read γ R (fun c => RCLike.re (inner ℂ v ((a ^ c) v))) hR)
  have hgt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) :=
    lt_of_lt_of_le hγ ((margin_nonneg_iff R γ).mp hlin)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  exact ⟨lt_trans h3 hgt, R.tension_lt_floor_of_cosAvg hgt⟩

#print axioms readsClear_of_readsClearWith

end Engine

/-! ## 3. Subtracting the vacuum component -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `v` with its `Ω`-component subtracted: `v − ⟪Ω, v⟫ Ω`. For `‖Ω‖ = 1` it is the orthogonal
projection onto the complement of `Ω` (`inner_vacSub`, `vacSub_of_orth`).

DERIVED: no numeral occurs. -/
noncomputable def vacSub (Ω v : E) : E := v - inner ℂ Ω v • Ω

/-- A vector already orthogonal to `Ω` is unchanged.

DERIVED: `0` is the orthogonality. -/
theorem vacSub_of_orth {Ω v : E} (h : inner ℂ Ω v = 0) : vacSub Ω v = v := by
  rw [vacSub, h, zero_smul, sub_zero]

#print axioms vacSub_of_orth

/-- For a unit `Ω`, `vacSub Ω v` is orthogonal to `Ω`: `⟪Ω, v⟫ − ⟪Ω, v⟫·‖Ω‖² = 0`.

DERIVED: `1` is the norm of `Ω`; `0` is the orthogonality concluded. -/
theorem inner_vacSub {Ω : E} (hΩ : ‖Ω‖ = 1) (v : E) : inner ℂ Ω (vacSub Ω v) = 0 := by
  rw [vacSub, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
  simp

#print axioms inner_vacSub

/-- `vacSub Ω` is continuous.

DERIVED: no numeral occurs. -/
theorem continuous_vacSub (Ω : E) : Continuous (vacSub Ω) := by
  show Continuous (fun v : E => v - inner ℂ Ω v • Ω)
  exact continuous_id.sub
    ((Continuous.inner (𝕜 := ℂ) continuous_const continuous_id).smul continuous_const)

#print axioms continuous_vacSub

end Projection

/-! ## 4. W4 — from the local observables to the whole vacuum complement -/

section Local

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The real component of the `j`-th iterate of the complexified translation is the `j`-th iterate of
`D.T` on the real component.

DERIVED: no numeral occurs; `.1` is the first product projection. -/
theorem cT_iterate_fst (D : TransferData A) (z : Pre D.toReflForm) (j : ℕ) :
    (((⇑(cT D))^[j] z : Pre D.toReflForm) : A × A).1 = (⇑D.T)^[j] (z : A × A).1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', cT_fst, ih]

#print axioms cT_iterate_fst

/-- The imaginary component of the `j`-th iterate of the complexified translation is the `j`-th
iterate of `D.T` on the imaginary component.

DERIVED: no numeral occurs; `.2` is the second product projection. -/
theorem cT_iterate_snd (D : TransferData A) (z : Pre D.toReflForm) (j : ℕ) :
    (((⇑(cT D))^[j] z : Pre D.toReflForm) : A × A).2 = (⇑D.T)^[j] (z : A × A).2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', cT_snd, ih]

#print axioms cT_iterate_snd

/-- `opTʲ` at the class of a pair is the class of the `j`-th iterate of `cT D` on the pair.

DERIVED: no numeral occurs. -/
theorem opT_pow_coe (D : TransferData A) (z : Pre D.toReflForm) (j : ℕ) :
    ((opT D) ^ j) (z : H D.toReflForm)
      = (((⇑(cT D))^[j] z : Pre D.toReflForm) : H D.toReflForm) := by
  rw [ContinuousLinearMap.coe_pow']
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, opT_coe, cTL_apply]

#print axioms opT_pow_coe

/-- **The profile of a pair is the sum of the two real profiles.** At the class of a pair `z`:
`re ⟪z, opTʲ z⟫ = D.form z.1 (Tʲ z.1) + D.form z.2 (Tʲ z.2)`, the real part of `cform` pairing like
component with like.

DERIVED: no numeral occurs; `.1` and `.2` are the product projections. -/
theorem re_inner_opT_pow_coe (D : TransferData A) (z : Pre D.toReflForm) (j : ℕ) :
    RCLike.re (inner ℂ (z : H D.toReflForm) (((opT D) ^ j) (z : H D.toReflForm)))
      = D.form (z : A × A).1 ((D.T ^ j) (z : A × A).1)
        + D.form (z : A × A).2 ((D.T ^ j) (z : A × A).2) := by
  rw [opT_pow_coe, MassGap.GNSHilbert.inner_coe, RCLike.re_to_complex, OSPositivity.cform_re,
    cT_iterate_fst, cT_iterate_snd, Module.End.pow_apply, Module.End.pow_apply]

#print axioms re_inner_opT_pow_coe

/-- **A pair orthogonal to the vacuum has both components orthogonal to `D.vac`.** If the class of
`w` is orthogonal to `Omega D.toReflForm D.vac`, then `D.form w.1 D.vac = 0` and
`D.form w.2 D.vac = 0`: the real and imaginary parts of `cform (vac, 0) w` are `D.form D.vac w.1` and
`D.form D.vac w.2`.

DERIVED: `0` is the orthogonality and the concluded values; `.1` and `.2` are the product
projections. -/
theorem form_vac_eq_zero_of_orth (D : TransferData A) (w : Pre D.toReflForm)
    (horth : inner ℂ (Omega D.toReflForm D.vac) (w : H D.toReflForm) = 0) :
    D.form (w : A × A).1 D.vac = 0 ∧ D.form (w : A × A).2 D.vac = 0 := by
  have hc : OSPositivity.cform D.toPreForm
      ((Pre.ofPair D.toReflForm D.vac (0 : A) : Pre D.toReflForm) : A × A) (w : A × A) = 0 :=
    (MassGap.GNSHilbert.inner_coe D.toReflForm (Pre.ofPair D.toReflForm D.vac (0 : A)) w).symm.trans
      horth
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  simp only [OSPositivity.cform_re, OSPositivity.cform_im, Pre.ofPair_fst, Pre.ofPair_snd,
    Complex.zero_re, Complex.zero_im, Transfer.PreForm.form_zero_left, add_zero, sub_zero]
    at hre him
  exact ⟨(D.form_symm (w : A × A).1 D.vac).trans hre, (D.form_symm (w : A × A).2 D.vac).trans him⟩

#print axioms form_vac_eq_zero_of_orth

/-- **Subtracting the vacuum component keeps a class a class.** For every pair `z` there is a pair `w`
whose class is `vacSub Ω z`, `Ω = Omega D.toReflForm D.vac`. The proof takes `w = z − ⟪ω, z⟫ ω` with
`ω = (D.vac, 0)`, whose class is `Ω`.

DERIVED: no numeral occurs in the statement; the `0` imaginary component of the vacuum is inside the
proof. -/
theorem exists_coe_eq_vacSub (D : TransferData A) (z : Pre D.toReflForm) :
    ∃ w : Pre D.toReflForm,
      vacSub (Omega D.toReflForm D.vac) (z : H D.toReflForm) = (w : H D.toReflForm) := by
  refine ⟨z - inner ℂ (Pre.ofPair D.toReflForm D.vac (0 : A)) z
      • Pre.ofPair D.toReflForm D.vac (0 : A), ?_⟩
  have h1 : inner ℂ (Omega D.toReflForm D.vac) (z : H D.toReflForm)
      = inner ℂ (Pre.ofPair D.toReflForm D.vac (0 : A)) z :=
    UniformSpace.Completion.inner_coe _ _
  rw [vacSub, h1, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul]
  rfl

#print axioms exists_coe_eq_vacSub

/-- **The local inequality at a pair orthogonal to the vacuum.** If every `x` with
`D.form x D.vac = 0` has `0 ≤ marginSum k γ (c ↦ D.form x (Tᶜ x))`, then so does the complex profile
`c ↦ re ⟪w, opTᶜ w⟫` of the class of any pair `w` orthogonal to the vacuum: it is the sum of the two
real profiles (`re_inner_opT_pow_coe`), each nonnegative under the margin sum by
`form_vac_eq_zero_of_orth`.

DERIVED: `0` is the orthogonality and the sign of the sums. -/
theorem margin_coe_nonneg (D : TransferData A) (k : ℕ) (γ : ℝ)
    (hloc : ∀ x : A, D.form x D.vac = 0 →
      0 ≤ marginSum k γ (fun c => D.form x ((D.T ^ c) x)))
    (w : Pre D.toReflForm)
    (horth : inner ℂ (Omega D.toReflForm D.vac) (w : H D.toReflForm) = 0) :
    0 ≤ marginSum k γ
      (fun c => RCLike.re (inner ℂ (w : H D.toReflForm) (((opT D) ^ c) (w : H D.toReflForm)))) := by
  obtain ⟨h1, h2⟩ := form_vac_eq_zero_of_orth D w horth
  exact le_of_le_of_eq (add_nonneg (hloc _ h1) (hloc _ h2))
    ((marginSum_add k γ _ _).symm.trans
      (marginSum_congr k γ (fun c => (re_inner_opT_pow_coe D w c).symm)))

#print axioms margin_coe_nonneg

/-- **W4: the margin read on the local observables gives it on the whole vacuum complement.** For
transfer data `D`: if every `x : A` with `D.form x D.vac = 0` has
`0 ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · D.form x (T^{circLag d} x)`, then
`ReadsClearWith (opT D) (Omega D.toReflForm D.vac) k γ`.

The map `v ↦ marginSum k γ (c ↦ re ⟪vacSub Ω v, opTᶜ (vacSub Ω v)⟫)` is continuous, so the set where it
is nonnegative is closed; at each class of a pair it is nonnegative (`exists_coe_eq_vacSub`,
`inner_vacSub`, `margin_coe_nonneg`); `UniformSpace.Completion.induction_on` carries that to every
`v`; and at `v ⊥ Ω`, `vacSub Ω v = v`.

DERIVED: `0` is the orthogonality and the sign of the sum. -/
theorem readsClearWith_of_local (D : TransferData A) (k : ℕ) (γ : ℝ)
    (hloc : ∀ x : A, D.form x D.vac = 0 →
      0 ≤ marginSum k γ (fun c => D.form x ((D.T ^ c) x))) :
    ReadsClearWith (opT D) (Omega D.toReflForm D.vac) k γ := by
  have hall : ∀ v : H D.toReflForm,
      0 ≤ marginSum k γ (fun c => RCLike.re (inner ℂ (vacSub (Omega D.toReflForm D.vac) v)
        (((opT D) ^ c) (vacSub (Omega D.toReflForm D.vac) v)))) := by
    intro v
    induction v using UniformSpace.Completion.induction_on with
    | hp =>
      refine isClosed_le continuous_const ?_
      exact continuous_marginSum k γ
        (fun u c => RCLike.re (inner ℂ (vacSub (Omega D.toReflForm D.vac) u)
          (((opT D) ^ c) (vacSub (Omega D.toReflForm D.vac) u))))
        (fun c => RCLike.continuous_re.comp
          (Continuous.inner (𝕜 := ℂ) (continuous_vacSub (Omega D.toReflForm D.vac))
            (((opT D) ^ c).continuous.comp (continuous_vacSub (Omega D.toReflForm D.vac)))))
    | ih z =>
      obtain ⟨w, hw⟩ := exists_coe_eq_vacSub D z
      have horth := inner_vacSub (norm_Omega_vac D) (z : H D.toReflForm)
      rw [hw] at horth
      rw [hw]
      exact margin_coe_nonneg D k γ hloc w horth
  intro v hv
  have h := hall v
  rwa [vacSub_of_orth hv] at h

#print axioms readsClearWith_of_local

/-- **The linear condition at the GNS transfer operator, vector by vector.** Under
`PositiveTransfer D`, `ReadsClearWith (opT D) Ω k γ` holds exactly when every nonzero `v` orthogonal
to `Ω` has `ContinuumE.transferRead D hP v hv k` — the read whose correlation at lag `d` is
`re ⟪v, opT^{circLag d} v⟫` — with cosine average at least `γ`. At `v = 0` the margin sum is `0`.

DERIVED: `0` is the zero vector and the orthogonality. -/
theorem readsClearWith_iff_cosAvg (D : TransferData A) (hP : PositiveTransfer D) (k : ℕ)
    (γ : ℝ) :
    ReadsClearWith (opT D) (Omega D.toReflForm D.vac) k γ ↔
      ∀ v : H D.toReflForm, ∀ hv : v ≠ 0, inner ℂ (Omega D.toReflForm D.vac) v = 0 →
        γ ≤ ∑ d, (ContinuumE.transferRead D hP v hv k).p d
          * Real.cos ((ContinuumE.transferRead D hP v hv k).θ d) := by
  constructor
  · intro h v hv hΩv
    refine (margin_nonneg_iff (ContinuumE.transferRead D hP v hv k) γ).mp ?_
    exact le_of_le_of_eq (h v hΩv)
      (marginSum_eq_read γ (ContinuumE.transferRead D hP v hv k)
        (fun c => RCLike.re (inner ℂ v (((opT D) ^ c) v))) (fun d => rfl))
  · intro h v hΩv
    rcases eq_or_ne v 0 with rfl | hv
    · have h0 : marginSum k γ
          (fun c => RCLike.re (inner ℂ (0 : H D.toReflForm) (((opT D) ^ c) 0))) = 0 := by
        show ∑ d : Fin (2 * k + 1 + 1), (Real.cos (readAngle k d) - γ)
            * RCLike.re (inner ℂ (0 : H D.toReflForm) (((opT D) ^ Moment.circLag d) 0)) = 0
        simp
      exact le_of_eq h0.symm
    · exact le_of_le_of_eq
        ((margin_nonneg_iff (ContinuumE.transferRead D hP v hv k) γ).mpr (h v hv hΩv))
        (marginSum_eq_read γ (ContinuumE.transferRead D hP v hv k)
          (fun c => RCLike.re (inner ℂ v (((opT D) ^ c) v))) (fun d => rfl)).symm

#print axioms readsClearWith_iff_cosAvg

/-- **At rate zero the margin sum is its lag-zero term.** Under `GapAt D 0` —
`D.form (T x) (T x) ≤ 0` at every `x` with `D.form x D.vac = 0` — every such `x` has
`0 ≤ marginSum k γ (c ↦ D.form x (Tᶜ x))` for every `γ ≤ 1`. `T x` is null (`GapAt D 0` and
`form_nonneg`), the null space is `T`-stable (`TransferData.T_mem_null`) and pairs to `0` with
everything (`ReflForm.form_eq_zero_of_mem_null`), so `D.form x (Tᶜ x) = 0` for `c ≥ 1`;
`circLag d = 0` only at `d = 0`, whose angle is `0`, so the sum is `(1 − γ)·D.form x x`.

DERIVED: `0` is the rate in `GapAt D 0`, the orthogonality and the sign of the sum; `1` is the upper
bound on `γ`, the cosine of the lag-zero angle. -/
theorem marginSum_nonneg_of_gapAt_zero (D : TransferData A) (k : ℕ) {γ : ℝ} (hγ : γ ≤ 1)
    (hg : MassGap.TransferGap.GapAt D 0) (x : A) (hx : D.form x D.vac = 0) :
    0 ≤ marginSum k γ (fun c => D.form x ((D.T ^ c) x)) := by
  have hTx : D.form (D.T x) (D.T x) = 0 := by
    have h1 := hg x hx
    have h2 := D.form_nonneg (D.T x)
    have h3 : (0 : ℝ) ^ 2 * D.form x x = 0 := by ring
    exact le_antisymm (by linarith) h2
  have hpow : ∀ j : ℕ, (D.T ^ j) (D.T x) ∈ D.toReflForm.nullSpace := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, Module.End.one_apply]
      exact D.toReflForm.mem_nullSpace.mpr hTx
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact MassGap.Transfer.TransferData.T_mem_null (D := D) ih
  have hzero : ∀ c : ℕ, 0 < c → D.form x ((D.T ^ c) x) = 0 := by
    intro c hc
    cases c with
    | zero => exact absurd hc (lt_irrefl 0)
    | succ j =>
      rw [pow_succ, Module.End.mul_apply]
      exact (D.form_symm x ((D.T ^ j) (D.T x))).trans
        (D.toReflForm.form_eq_zero_of_mem_null (hpow j) x)
  show 0 ≤ ∑ d : Fin (2 * k + 1 + 1),
    (Real.cos (readAngle k d) - γ) * D.form x ((D.T ^ Moment.circLag d) x)
  refine Finset.sum_nonneg (fun d _ => ?_)
  by_cases hd : Moment.circLag d = 0
  · have hd0 : (d : ℕ) = 0 := by
      have hlt := d.isLt
      unfold Moment.circLag at hd
      omega
    have hang : readAngle k d = 0 := by
      simp [readAngle, hd0]
    rw [hang, Real.cos_zero, hd, pow_zero, Module.End.one_apply]
    exact mul_nonneg (sub_nonneg.mpr hγ) (D.form_nonneg x)
  · exact le_of_eq (by rw [hzero _ (Nat.pos_of_ne_zero hd), mul_zero])

#print axioms marginSum_nonneg_of_gapAt_zero

end Local

/-! ## 5. W5 — the input in the finite boxes, and the composition -/

section Box

variable {N : ℕ}

/-- The connected reflected-shifted pairing of `x` at lag `c` in the free-boundary box
`mixCube τ p n` at coupling `β`: `μₙ(θx · Sᶜx) − μₙ(θx)·μₙ(Sᶜx)`, with `μₙ` the free-boundary Wilson
state on the box at the all-identity boundary configuration, θ = `ireflObs τ (2p)`, the reflection
`x_τ ↦ 2p − x_τ` whose mirror plane is `x_τ = p`, and `S` the unit shift along `τ`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`; `2` is the doubling
of the reflection plane `2 * p`, `ReflectionHalfSpace`'s convention; `1` is the all-identity boundary
configuration. -/
noncomputable def boxConn (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (n : ℕ)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (c : ℕ) : ℝ :=
  stateFree (φ := MassGap.WilsonAction.wilsonDensity) MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN) (MassGap.WilsonAction.wilsonDensity_le_two hN)
      β (mixCube τ p n) 1
      (MassGap.LatticeReflection.ireflObs τ (2 * p) x
        * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
    - stateFree (φ := MassGap.WilsonAction.wilsonDensity)
        MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN)
        β (mixCube τ p n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
      * stateFree (φ := MassGap.WilsonAction.wilsonDensity)
        MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN)
        β (mixCube τ p n) 1 ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)

/-- The box's connected pairing converges to the limit state's: each of its three box expectations
converges under `htend`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane; `1` is the all-identity boundary configuration. -/
theorem tendsto_boxConn (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (c : ℕ) :
    Filter.Tendsto (fun n => boxConn τ p hN β n x c) Filter.atTop
      (nhds (ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
        - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x))) :=
  (htend (MassGap.LatticeReflection.ireflObs τ (2 * p) x
      * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)).sub
    ((htend (MassGap.LatticeReflection.ireflObs τ (2 * p) x)).mul
      (htend ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)))

#print axioms tendsto_boxConn

/-- A convergent real sequence that is eventually at least `−ε` for every `ε > 0` has a nonnegative
limit.

DERIVED: `0` is the lower bound concluded and the sign of each slack `ε`. -/
theorem nonneg_of_slack {u : ℕ → ℝ} {L : ℝ} (hu : Filter.Tendsto u Filter.atTop (nhds L))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, -ε ≤ u n) : 0 ≤ L := by
  by_contra hneg
  have hL : L < 0 := not_le.mp hneg
  have hle : -(-L / 2) ≤ L := ge_of_tendsto hu (h (-L / 2) (by linarith))
  linarith

#print axioms nonneg_of_slack

/-- A real sequence converging to a nonnegative limit is eventually at least `−ε`, for every `ε > 0`.

DERIVED: `0` is the sign of the limit and of each slack `ε`. -/
theorem slack_of_nonneg {u : ℕ → ℝ} {L : ℝ} (hu : Filter.Tendsto u Filter.atTop (nhds L))
    (hL : 0 ≤ L) : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, -ε ≤ u n := by
  intro ε hε
  filter_upwards [hu.eventually (lt_mem_nhds (show L - ε < L by linarith))] with n hn
  linarith

#print axioms slack_of_nonneg

/-- **THE INPUT, as the tail of the box expectations.** At coupling `β`, aperture `2k + 1` and
margin `γ`: for every gauge-invariant half-space observable `x` and every slack `ε > 0`, for all
large `n`, `−ε ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · boxConn τ p hN β n x (circLag d)`
— a non-strict inequality, linear in the connected pairings of `x` at lags `0, …, k + 1` in the
free-boundary box `mixCube τ p n`.

The slack is what makes the condition a statement about the limit and nothing more: under `htend`,
for each `x` it holds exactly when the limit state's margin sum of the connected profile is
nonnegative (`boxSlack_iff`). A form asking `0 ≤` in every large box would also constrain the sign of
the approach, which the finite boxes do not control where the limit is `0` — for instance at an
observable whose class in the GNS space is zero, where the limit profile vanishes by Cauchy–Schwarz
for the reflection form. `boxReadsClearWith_of_eventually` derives this form from that one.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the sign of the slack. -/
def BoxReadsClearWith (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ) (γ : ℝ) : Prop :=
  ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, -ε ≤ marginSum k γ (boxConn τ p hN β n x)

/-- The box inequality without slack — `0 ≤` the box margin sum for all large `n`, at every
gauge-invariant half-space observable — gives `BoxReadsClearWith`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the sign of the sum. -/
theorem boxReadsClearWith_of_eventually (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ) (γ : ℝ)
    (h : ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ᶠ n in Filter.atTop, 0 ≤ marginSum k γ (boxConn τ p hN β n x)) :
    BoxReadsClearWith τ p hN β k γ := by
  intro x hx ε hε
  filter_upwards [h x hx] with n hn
  linarith

#print axioms boxReadsClearWith_of_eventually

/-- **The slack form is the limit statement, observable by observable.** Under `htend`, for any
continuous `x`: the box margin sums of `x` are eventually at least `−ε` for every `ε > 0` exactly when
`0 ≤ marginSum k γ (c ↦ ν(θx · Sᶜx) − ν(θx)·ν(Sᶜx))`, the margin sum of the limit state's connected
reflected-shifted profile. The box margin sums converge to it (`tendsto_boxConn`,
`tendsto_marginSum`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the sign of the slack and of
the limit; `2` is the doubling of the reflection plane; `1` is the all-identity boundary
configuration. -/
theorem boxSlack_iff (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ) (γ : ℝ) (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, -ε ≤ marginSum k γ (boxConn τ p hN β n x))
      ↔ 0 ≤ marginSum k γ (fun c =>
          ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
            - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
              * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)) := by
  have hlim := tendsto_marginSum k γ (fun n => boxConn τ p hN β n x) _
    (tendsto_boxConn τ p hN β ν htend x)
  exact ⟨nonneg_of_slack hlim, slack_of_nonneg hlim⟩

#print axioms boxSlack_iff

/-- The gauge-invariant Wilson form against the vacuum is the limit state's one-point function of the
reflected observable: `D.form x D.vac = ν(θx)`. The form is `ν(θx · y)` and the vacuum is the
constant `1`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane; `1` is the all-identity boundary configuration. -/
theorem wilson_form_vac (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)) :
    (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
        (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac
      = ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
          (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := by
  have h : (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
        (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac
      = ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
          (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := rfl
  rw [h, mul_one]

#print axioms wilson_form_vac

/-- The gauge-invariant Wilson form at a translate is the limit state's reflected-shifted pairing:
`D.form x (Tᶜ x) = ν(θx · Sᶜx)`. `GaugeInvariantAlgebra.gaugeInv_form_pow` at the three state facts
`wilsonGaugeInvMixCubeData` is built from.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane; `1` is the all-identity boundary configuration. -/
theorem wilson_form_pow (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (c : ℕ) :
    (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
        (((wilsonGaugeInvMixCubeData τ p hN β ν htend).T ^ c) x)
      = ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c]
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) :=
  MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))
    x c

#print axioms wilson_form_pow

/-- **W5: the box input gives the local condition at the limit state.** Under
`BoxReadsClearWith τ p hN β k γ`, every `x` in the gauge-invariant algebra with `D.form x D.vac = 0`
(`D = wilsonGaugeInvMixCubeData τ p hN β ν htend`) has
`0 ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · D.form x (T^{circLag d} x)`.

`boxSlack_iff` turns the slack inequality at `x` into `0 ≤` the margin sum of the limit profile
`c ↦ ν(θx · Sᶜx) − ν(θx)·ν(Sᶜx)`; `ν(θx) = D.form x D.vac = 0` (`wilson_form_vac`) and
`ν(θx · Sᶜx) = D.form x (Tᶜ x)` (`wilson_form_pow`) identify that profile with `c ↦ D.form x (Tᶜ x)`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the orthogonality and the
sign of the sum; `1` is the all-identity boundary configuration. -/
theorem localReads_of_boxReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ) (γ : ℝ) (hbox : BoxReadsClearWith τ p hN β k γ)
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (hx : (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
      (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac = 0) :
    0 ≤ marginSum k γ (fun c => (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
      (((wilsonGaugeInvMixCubeData τ p hN β ν htend).T ^ c) x)) := by
  have hθ : ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
      (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = 0 :=
    (wilson_form_vac τ p hN β ν htend x).symm.trans hx
  have hprof : ∀ c : ℕ,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c]
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
        - ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c]
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
      = (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
          (((wilsonGaugeInvMixCubeData τ p hN β ν htend).T ^ c) x) := by
    intro c
    rw [hθ, zero_mul, sub_zero, wilson_form_pow τ p hN β ν htend x c]
  have hlim := (boxSlack_iff τ p hN β ν htend k γ
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))).mp (hbox x.1 x.2)
  exact le_of_le_of_eq hlim (marginSum_congr k γ hprof)

#print axioms localReads_of_boxReads

/-- **The converse of W5: the local condition at the limit state gives the box input.** With
`D = wilsonGaugeInvMixCubeData τ p hN β ν htend`: if every `x` in the gauge-invariant algebra with
`D.form x D.vac = 0` has
`0 ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · D.form x (T^{circLag d} x)`, then
`BoxReadsClearWith τ p hN β k γ`.

For an observable `x` of the algebra, `y = x − ν(θx)·1` is in the algebra
(`GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg`), and `D.form y D.vac = ν(θy) = 0`
(`wilson_form_vac`), since `θ1 = 1` and `ν 1 = 1`. Its form profile `ν(θy · Sᶜy)`
(`wilson_form_pow`) is `ν(θx · Sᶜx) − ν(θx)·ν(Sᶜx)`, the connected profile of `x`, since `Sᶜ1 = 1`
(`GaugeInvariantAlgebra.iterate_shift_sub_smul_one`). So the hypothesis at `y` is `0 ≤` the limit
margin sum of the connected profile of `x`, which `boxSlack_iff` turns into the slack inequality.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the orthogonality and the
sign of the sum; `1` is the all-identity boundary configuration. -/
theorem boxReads_of_localReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ) (γ : ℝ)
    (hloc : ∀ x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p),
      (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
          (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac = 0 →
        0 ≤ marginSum k γ (fun c => (wilsonGaugeInvMixCubeData τ p hN β ν htend).form x
          (((wilsonGaugeInvMixCubeData τ p hN β ν htend).T ^ c) x))) :
    BoxReadsClearWith τ p hN β k γ := by
  intro x hx
  refine (boxSlack_iff τ p hN β ν htend k γ x).mpr ?_
  -- `ν` against a mean-subtracted product: `ν((f − ν f)(g − ν f)) = ν(f g) − ν f · ν g`
  have hν : ∀ f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν ((f - ν f • 1) * (g - ν f • 1)) = ν (f * g) - ν f * ν g := by
    intro f g
    have hexp : (f - ν f • 1) * (g - ν f • 1)
        = f * g - ν f • g - ν f • f
          + (ν f * ν f) • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
      ext U
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, ContinuousMap.add_apply, smul_eq_mul]
      ring
    rw [hexp]
    simp only [MassGap.DLRLimit.State.map_add, MassGap.DLRLimit.State.map_sub,
      MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one]
    ring
  have hθ1 : MassGap.LatticeReflection.ireflObs τ (2 * p)
      (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 := by
    ext U; rfl
  have hθy : MassGap.LatticeReflection.ireflObs τ (2 * p)
        (x - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
      = MassGap.LatticeReflection.ireflObs τ (2 * p) x
        - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
    rw [map_sub, map_smul, hθ1]
  have hy : x - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
        • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
    Submodule.sub_mem _ hx
      (Submodule.smul_mem _ _ (MassGap.GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg τ p))
  obtain ⟨y, hyv⟩ : ∃ y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p),
      (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        = x - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :=
    ⟨⟨_, hy⟩, rfl⟩
  have hvac : (wilsonGaugeInvMixCubeData τ p hN β ν htend).form y
      (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac = 0 := by
    rw [wilson_form_vac τ p hN β ν htend y, hyv, hθy, MassGap.DLRLimit.State.map_sub,
      MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one]
    ring
  have hprof : ∀ c : ℕ,
      (wilsonGaugeInvMixCubeData τ p hN β ν htend).form y
          (((wilsonGaugeInvMixCubeData τ p hN β ν htend).T ^ c) y)
        = ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
          - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
            * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x) := by
    intro c
    rw [wilson_form_pow τ p hN β ν htend y c, hyv, hθy,
      MassGap.GaugeInvariantAlgebra.iterate_shift_sub_smul_one τ c x
        (ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x))]
    exact hν _ _
  exact le_of_le_of_eq (hloc y hvac) (marginSum_congr k γ hprof)

#print axioms boxReads_of_localReads

/-- **The reads of the Wilson transfer operator from the box input.** At any real `β` with limit state
`ν` (the `atTop` limit of the free mixed-cube states), and a margin `γ > 3^{−1/4}`:
`BoxReadsClearWith τ p hN β k γ` gives `SpectralGap.ReadsClear` for the gauge-invariant GNS transfer
operator at aperture `2k + 1`. W5, then W4, then W3.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `1` is the all-identity
boundary configuration; `3`, `1` and `4` spell the floor `3^{−1/4}`. -/
theorem wilson_readsClear_of_boxReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ) {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (hbox : BoxReadsClearWith τ p hN β k γ) :
    SpectralGap.ReadsClear (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
        (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) k :=
  readsClear_of_readsClearWith (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
    (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
      (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) k hγ
    (readsClearWith_of_local (wilsonGaugeInvMixCubeData τ p hN β ν htend) k γ
      (localReads_of_boxReads τ p hN β ν htend k γ hbox))

#print axioms wilson_readsClear_of_boxReads

/-- **The Wilson transfer gap from the box input, at every `β ≥ 0`.** Under the limit state `htend`, a
margin `γ > 3^{−1/4}` and `BoxReadsClearWith τ p hN β k γ`, the vacuum complement of the
gauge-invariant GNS space is contracted: there is `ρ` with `0 ≤ ρ < 1`,
`ρ^{k+1} = 12(1 − 3^{−1/4})/8`, and `‖opTᵐ u‖ ≤ ρᵐ ‖u‖` for every `u` orthogonal to the vacuum and
every `m`. `WilsonReadGap.wilson_gap_of_reads` at `wilson_readsClear_of_boxReads`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `β` and of
`ρ`, and the orthogonality; `1` is the all-identity boundary configuration, the upper bound on `ρ` and
the `+ 1` of `k + 1`; `3`, `1` and `4` spell the floor `3^{−1/4}`; `12` and `8` complete the cap
`12(1 − 3^{−1/4})/8` of `SpectralRead.lam0_pow_lt_of_tension`. -/
theorem wilson_gap_of_boxReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ) {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (hbox : BoxReadsClearWith τ p hN β k γ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : H (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
        inner ℂ (Omega (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm
          (wilsonGaugeInvMixCubeData τ p hN β ν htend).vac) u = 0 →
        ∀ m : ℕ, ‖((opT (wilsonGaugeInvMixCubeData τ p hN β ν htend)) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  MassGap.WilsonReadGap.wilson_gap_of_reads τ p hN hβ ν htend k
    (wilson_readsClear_of_boxReads τ p hN β ν htend k hγ hbox)

#print axioms wilson_gap_of_boxReads

/-- **The Clay spectral statement from the box input, at every `β ≥ 0`.** Under the limit state
`htend`, a margin `γ > 3^{−1/4}` and `BoxReadsClearWith τ p hN β k γ`: there is `ρ` with `0 < ρ < 1`
and `ρ^{k+1} = 12(1 − 3^{−1/4})/8` such that the gauge-invariant GNS transfer operator is
self-adjoint, `0 < −log ρ`, its spectrum lies in `{1} ∪ [0, exp(−(−log ρ))]`, and `1` is its largest
element. `ReadRoute.wilson_gaugeInv_clay_gap_of_reads`, which takes `0 ≤ β`, at
`wilson_readsClear_of_boxReads`.

The statement does not assert a non-zero vacuum complement; at `2 ≤ N` that is
`PlaneVariance.exists_ne_zero_orth_vacuum`, and `ReadRoute.clayGapAt_of_reads` at
`wilson_readsClear_of_boxReads` gives both.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `β`, of `ρ`
and of the spectrum, and the sign of the gap; `1` is the all-identity boundary configuration, the
vacuum eigenvalue, the upper bound on `ρ` and the `+ 1` of `k + 1`; `3`, `1` and `4` spell the floor
`3^{−1/4}`; `12` and `8` complete the cap `12(1 − 3^{−1/4})/8`. -/
theorem wilson_clay_gap_of_boxReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (k : ℕ) {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (hbox : BoxReadsClearWith τ p hN β k γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))) 1 :=
  MassGap.ReadRoute.wilson_gaugeInv_clay_gap_of_reads τ p hN hβ ν htend k
    (wilson_readsClear_of_boxReads τ p hN β ν htend k hγ hbox)

#print axioms wilson_clay_gap_of_boxReads

/-- **The box input at zero coupling, for every `γ ≤ 1`.** At `β = 0`,
`ClayCapstone.wilson_htend_at_zero_coupling` gives a limit state `ν` of the free mixed-cube states;
`WilsonState.gapAt_zero_at_zero_coupling`, restricted to the invariant algebra by
`GaugeInvariantAlgebra.gapAt_gaugeInv_of_gapAt`, gives `GapAt D 0` at the gauge-invariant data `D`;
`marginSum_nonneg_of_gapAt_zero` gives the local inequality and `boxReads_of_localReads` the box
input.

With that state and any `γ` with `3^{−1/4} < γ ≤ 1`, the hypotheses of `wilson_clay_gap_of_boxReads`
hold together. That is at `β = 0` only, where this theorem makes such a `γ` available and the
transfer operator annihilates the vacuum complement; it says nothing about a gap at positive
coupling.

DERIVED: `4` is the spacetime dimension; `0` is the coupling and the excluded gauge rank in `hN`;
`1` is the upper bound on `γ`, the cosine of the lag-zero angle the margin sum reduces to. -/
theorem boxReadsClearWith_at_zero_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (k : ℕ) {γ : ℝ}
    (hγ : γ ≤ 1) : BoxReadsClearWith τ p hN 0 k γ := by
  obtain ⟨ν, hdlr, htend⟩ := wilson_htend_at_zero_coupling τ p hN
  have hgap : MassGap.TransferGap.GapAt (wilsonGaugeInvMixCubeData τ p hN 0 ν htend) 0 := by
    refine MassGap.GaugeInvariantAlgebra.gapAt_gaugeInv_of_gapAt τ p ν _ _ _ ?_
    exact MassGap.WilsonState.gapAt_zero_at_zero_coupling
      (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN)
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) hdlr τ p
      (wilson_reflInvariant_of_tendsto τ (2 * p) hN 0 ν Filter.atTop
        (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend))
      (wilson_reflPositive_even_of_tendsto τ p hN 0 1 ν Filter.atTop le_rfl
        (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend))
      (wilson_nu_T_of_tendsto τ p hN 0 ν Filter.atTop Filter.atTop
        (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend)
        (tendsto_symCube_odd_of_mixCube τ p hN 0 ν htend))
  exact boxReads_of_localReads τ p hN 0 ν htend k γ
    (fun x hx => marginSum_nonneg_of_gapAt_zero _ k hγ hgap x hx)

#print axioms boxReadsClearWith_at_zero_coupling

end Box

end MassGap.ReadReduce
