import Mathlib
import MassGap.ContinuumSchwinger

noncomputable section

/-!
# MassGap.ZoomForest — the same forest at every zoom

An observer at a fixed physical resolution `ℓ` and a fixed physical region `R` reads the
configuration through a measurable coarse-graining map `φ` into a fixed observer space. The
observer's law is the pushforward `μ.map φ`. The lattice spacing halves from step to step, so at
step `k` the observer map is `φ k` and the law is `(μ k).map (φ k)`; the observer space, the
resolution and the region stay the same. Two observers at two resolutions see two laws, each
correct for its aperture; the coarser one is the image of the finer one under a coarse-graining
`χ` of the observer space (`forestLimit_map_comp`).

## What Mathlib provides at the pin

* `InformationTheory.klDiv μ ν : ℝ≥0∞` (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`):
  `ENNReal.ofReal (∫ llr μ ν ∂μ + ν.real univ − μ.real univ)` when `μ ≪ ν` and `llr μ ν` is
  `μ`-integrable, `∞` otherwise (`klDiv_of_ac_of_integrable`, `klDiv_of_not_ac`,
  `klDiv_of_not_integrable`, `klDiv_ne_top_iff`, `klDiv_eq_zero_iff`, `toReal_klDiv_of_measure_eq`,
  `mul_log_le_klDiv`).
* `MeasureTheory.llr μ ν x = log (μ.rnDeriv ν x).toReal`, with `measurable_llr`.
* The chain rule (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`):
  `klDiv_compProd_eq_add : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` and
  `klDiv_compProd_left : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν`, for Markov kernels.
* Total variation exists for signed measures only (`SignedMeasure.totalVariation`, a measure).
  There is no total-variation distance between two measures, no Pinsker inequality, and no
  data-processing inequality for `Measure.map`.

Pinsker and data processing enter here as the named propositions `PinskerObs` and
`KLDataProcessing`, each a standard theorem. Total variation enters in its observable form
`ObsClose`: every measurable observable bounded by one has its two expectations within `ε`.

## The chain

* **Observable total variation** (`ObsClose`): reflexive, symmetric, triangle, contracted by every
  measurable map (`ObsClose.map`), scaled to observables bounded by `M`
  (`ObsClose.abs_integral_sub_le`), and bounding the setwise difference
  (`ObsClose.abs_real_sub_le`).
* **The same forest** (`ForestAt m ε`): the increments `ε k` between successive observer laws are
  summable. Then the laws are Cauchy in observable total variation (`ForestAt.obsClose_tail`,
  `ForestAt.cauchy`), and every bounded measurable observable has an expectation converging along
  `atTop` to `forestLimit m f`, with the rate `M · ∑' i, ε (n + i)` uniform over the observables
  bounded by `M` (`ForestAt.tendsto`). The limit is additive, positive and normalised
  (`ForestAt.forestLimit_add`, `ForestAt.forestLimit_nonneg`, `forestLimit_one`).
* **The observer's view** (`SameForestAt μ φ ε`, `SameForest μ φ`): `ForestAt` of the pushforwards.
  `SameForestAt.tendsto_coarse` reads it on the coarse observables `g ∘ φ k`.
  `SameForestAt.comp`: a coarser observer inherits the same forest with the same increments.
* **Entropy** (`SameForestKL μ φ`): the successive relative entropies are finite and their square
  roots are summable. Under `PinskerObs` this is `SameForestAt` with
  `ε k = √(2 · KL_k)` (`SameForestKL.sameForestAt`); under `KLDataProcessing` a coarser observer
  inherits it (`SameForestKL.comp`).

## Connection to `ContinuumSchwinger`

`tendsto_latSkR_of_sameForestAt`: if the step-`k` renormalised lattice Schwinger function of a
family is the expectation of one bounded measurable observer observable `g` under the step-`k`
view, `latSkR hN ρ k F = ∫ g (φ k x) ∂(μ k)`, then `SameForestAt μ φ ε` makes the lattice
functions converge along `atTop` to `contS hN ρ F`, with rate `M · ∑' i, ε (n + i)`. The value
`contS` picks along the ultrafilter is then the genuine limit, and `UniformBound` is not used.
The reading identity asks one bound `M` on `g` at every step. With
`μ k = DLRLimit.gibbsMeasure (stateK hN k)` it holds whenever `g ∘ φ k` is the continuous observable
`ρ.pref k F · ∏ᵢ smear aₖ (Oᵢ − cₖ Oᵢ) fᵢ` (`DLRLimit.integral_gibbsMeasure`) and that observable is
bounded by `M` at every `k`. The smeared fields are bounded uniformly in `k` at bounded
renormalisation data; with `Z` growing in the step the sup norm of the product grows with `Z`, and
no single bounded `g` reads it. One observer space serving a whole family is `β = (ι → ℝ)` with
`φ k U = (Zₖ · smear aₖ (Oᵢ − cₖ Oᵢ) fᵢ U)ᵢ`, the renormalised smeared fields themselves; then
`SameForest` is convergence in total variation of their joint law, and the bounded observables `g`
include every bounded function of the renormalised fields. The Schwinger functions are the moments
`g(y) = ∏ yᵢ`, unbounded on `ι → ℝ`; convergence in law together with uniform integrability of
`∏ᵢ yᵢ` under the step-`k` laws gives their convergence (Vitali). That step is not formalised here,
and the uniform integrability follows from `UniformBound` at the doubled family `F ⊕ F`, which
bounds `∫ (∏ᵢ yᵢ)²`: it is the input this route still needs at growing `Z`.

As an abstract statement the hypotheses of `tendsto_latSkR_of_sameForestAt` are satisfiable exactly
when `k ↦ latSkR hN ρ k F` has summable increments. `ObsClose.abs_integral_sub_le` bounds each
increment by `M · ε k`; conversely a sequence `s` with summable increments is bounded, and with
`M > sup |s|` it is read by the Bernoulli laws `P(1) = (s k + M) / (2M)`, `g(1) = M`, `g(0) = −M`,
at `ε k = |s (k + 1) − s k| / M`. The content of the theorem is in the choice of `μ` and `φ`: it
reaches the Schwinger functions when the physical observer (the Gibbs measures and the renormalised
fields) meets both hypotheses.

Total variation separates laws that concentrate at different scales. At bounded renormalisation
data a smeared field is a Riemann sum over about `a_k⁻⁴` cells, its law concentrates at a spread
shrinking with `a_k`, and two successive laws are expected to stay at total-variation distance of
order one (an estimate, not proved here). For that observer `SameForest` then fails, and so does
`WilsonZoomInput` under `PinskerObs`; the (degenerate) limit comes from `uniformBound_of_bounded`
instead.
`SameForest` is a statement about observer coordinates normalised so that their laws have a
non-degenerate limit, the renormalised fields with `Z` growing in the step, which is exactly where
`UniformBound` is open.

`SameForestAt.comp` reduces "the same forest at every observer scale" to a cofinal family of
fine observers: every coarser observer is the image of a finer one under a measurable `χ`, and
inherits the property with the same increments.

## Toward `WeakCouplingWindow.FixedWindowDecay`

`ForestAt.abs_conn_sub_le` and `ForestAt.abs_conn_le` state what the forest gives: for bounded
measurable observer observables `a`, `b` (`|a|, |b| ≤ M`), the step-`n` connected correlation
`∫ ab − ∫ a ∫ b` is within `3 M² ∑' i, ε (n + i)` of the limit's connected correlation. With `b`
the shift of `a` across a physical distance `t` inside the observer region, and decay of the limit
`|conn_lim(a, b)| ≤ D(t)`, the step-`n` connected correlation is at most
`D(t) + 3 M² ∑' i, ε (n + i)`.

`FixedWindowDecay τ p hN L` asks for one factor `q < 1`, uniform in the coupling, and at every
large coupling `β` a lag of physical length at most `L` with
`torusConn(x, m) ≤ q · torusConn(x, 0) + ε'` for every `ε' > 0`, eventually along
`periodicUltra hN β`, for every `x` in the gauge-invariant half-space algebra.
Three uniformities separate the forest bound from it.

1. **The observable class.** `x` ranges over every gauge-invariant half-space observable at the
   lattice spacing `aRun N β`, including single-plaquette observables. The forest at resolution
   `ℓ` controls functions of the `ℓ`-coarse field only; at fixed `ℓ` no lattice-scale observable
   is among them.
2. **Relative against additive.** At a fixed step the forest bound carries the additive remainder
   `3 M² · tail(n)`, where `M` is the sup-norm of the observable. `FixedWindowDecay` admits no
   remainder at fixed `β` (the slack `ε'` is arbitrary). Absorbing the remainder into
   `(q − q₀) · torusConn(x, 0)` needs `torusConn(x, 0) ≥ c · M²` with one `c > 0` across the
   class, a variance-to-sup-norm ratio bounded below, which the class does not have (indicators
   of rare events). The uniformity needed is a variance-relative increment: a bound
   `|E_{k+1} h − E_k h| ≤ δ_k · Var_k(h)^{1/2}` with `δ_k` summable, the form a `χ²`-divergence
   control gives by Cauchy–Schwarz, `|E_P h − E_Q h| ≤ χ²(P‖Q)^{1/2} Var_Q(h)^{1/2}`.
3. **The carriers.** `FixedWindowDecay` is stated for every large real `β` on the periodic tori
   along `periodicUltra`; the forest runs along the dyadic couplings
   `dyBeta (one_le_of_ne_zero hN) k` in the infinite-volume states `stateK hN k`.

## The open dynamical input

`WilsonZoomInput hN φ`: the Wilson measures at the dyadic couplings, represented as probability
measures, satisfy `ZoomGeometric` for the observer maps `φ`: each step-`(k+1)` observer law is
absolutely continuous with respect to the step-`k` law and their log-likelihood ratio is bounded
almost surely by `C θ^{2k}` with one `C ≥ 0` and one `θ < 1`. `klDiv_le_of_abs_llr_le` turns that
into `KL_k ≤ C θ^{2k}`, and `ZoomGeometric.sameForestKL` into `SameForestKL`.

Balaban's renormalisation-group bounds control the log-densities of block-spin effective measures
extensively: the effective action after `k` steps is a local polymer expansion with remainder
bounded by `E · |T|`, `|T|` the number of blocks, with `E` uniform in `k`. Through
`klDiv_le_of_abs_llr_le` an extensive bound gives `KL_k ≤ E · |T_R|` at the fixed region: finite
and uniform in `k`, and not summable. What `WilsonZoomInput` needs instead is a bound on the
*change* of the `ℓ`-scale marginal log-density on `R` between steps `k` and `k + 1`, of size
`C_R · θ^{2k}`: the corrections one more halving of the spacing leaves at the fixed observer
scale, after integrating down to `ℓ`, decay like a positive power of the spacing
(`θ = 2^{-γ}`, `a_k ∝ 2^{-k}`). It has to be local: `KLDataProcessing` bounds the marginal
relative entropy on `R` by the relative entropy of the full block-spin measures, which is extensive
in the volume, so the `R`-marginal bound has to come from the locality of the polymer expansion
(the influence of blocks outside a collar of `R` decaying), not from data processing.

## The zoom as a continuous path

Section 7 runs the zoom along a real parameter `t` (for the lattice, `t = log (a₀ / a)`) instead of
the dyadic steps.

* `abs_sub_le_of_hasDerivAt`: a real function whose derivative is dominated by a speed `v` moves at
  most the length `Λ s − Λ t` between `s ≤ t`, where `Λ' = −v` (with `Λ → 0`, `Λ t` is the
  remaining length `∫_t^∞ v`). No integral appears: `E + Λ` and `−E + Λ` are antitone.
* `SpeedBound P v`: every measurable observable bounded by one has an expectation differentiable in
  `t` with derivative of absolute value at most `v t`. `SpeedBound.obsClose`: then
  `ObsClose (P t) (P s) (Λ s − Λ t)`, the
  observer laws move at most the path length. `SpeedBound.comp`: a reparametrisation `b(t)`
  multiplies the speed by `|b'(t)|`.
* **Finite observer spaces** (`abs_sum_mul_le_sqrt_fisher`, `finitePath_abs_sub_le`): for a path of
  positive probability vectors `p t` with derivative `p' t`, every `|f| ≤ 1` has
  `|∑ f p'| ≤ √(∑ p'² / p)`, the square root of the Fisher information, by Cauchy–Schwarz; hence
  `|∑ f p t − ∑ f p s| ≤ Λ s − Λ t` for `Λ' = −√I`. Twice the total variation between two
  observer laws is at most the Fisher–Rao length of the path between them.
* `FiniteZoomLength P v` (a `SpeedBound` and a remaining length `Λ → 0`) gives the continuous
  same forest: every bounded observable converges along `atTop` (`FiniteZoomLength.tendsto`). The
  proof bounds the distance to the limit by `M · Λ t` with the remaining length of the hypothesis;
  the statement returns some `Λ → 0`, so as stated its content is the convergence.
* For a Gibbs family `dμ_b ∝ exp(−b S) dρ` the score is `∂_b log dμ_b = −(S − ⟨S⟩_b)`, and the
  observer's Fisher information is `observerFisher μ S φ b = Var_{μ_b}(E_{μ_b}[S | φ])`: the
  derivative of `∫ g ∘ φ dμ_b` is `−Cov(g ∘ φ, S) = −Cov(g ∘ φ, E[S | φ])`, bounded by
  `‖g‖_∞ · √(observerFisher)`. `GibbsObserverSpeed` states this (bounded `S`; a standard
  computation), and `finiteZoomLength_of_deafToUV` composes it with the zoom path `b(t)`:
  the Fisher–Rao speed per unit log-spacing is `√(Var(E[S | φ])) · |db/dt|`.
* **The open quantitative input** `DeafToUV μ S φ b b'`: that speed has an antiderivative `−Λ`
  with `Λ` tending to zero, so `∫^∞ √(Var_{μ_{b(t)}}(E[S | φ])) · |b'(t)| dt < ∞`: the coarse view
  becomes deaf to the fluctuations of the action as the spacing goes to zero.

Scope of the path statements. `DeafToUV` varies the measure at a fixed observer map. In lattice
units the observer map of a fixed physical resolution moves with the spacing (block size `ℓ / a`,
field normalisation `Z(a)`), so the full zoom composes the Fisher term with the drift of the
observer map; the drift moves the law in total variation only through the renormalised coordinates,
and the discrete `ForestAt` absorbs both parts into one relative entropy per step. On the Wilson
side the action `S` is the action of a finite box, the observer Fisher information is its limit as
the box grows (finite when the connected correlations between the observer's σ-algebra and the
action density are summable), and the family `b ↦ μ_b` is differentiable only on intervals of
couplings free of phase transitions: for `SU(N)` with `N ≥ 5` the Wilson action has a first-order
bulk transition at intermediate `β` (lattice Monte Carlo studies of the Wilson action, from the
early 1980s on). The Lean path statements run over all real `t`, and at bounded `S` (a finite box) the Gibbs
family is smooth on all of `ℝ`; for the infinite-volume family they apply to a coupling path whose
range avoids transitions. The zoom to `a → 0` uses the weak-coupling end.

## Scope

`WilsonZoomInput`, `GibbsObserverSpeed` and `DeafToUV` are stated and not proved. `PinskerObs` and
`KLDataProcessing` are stated here and proved in `MassGap.ChiForest` (`ChiForest.pinskerObs`,
`ChiForest.klDataProcessing`, from `MassGap.EntropyTools`). Everything else here is proved from Mathlib
and the tree.
-/

namespace MassGap.ZoomForest

open MeasureTheory Filter InformationTheory
open scoped Topology ENNReal

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-! ## 1. Observable total variation -/

section ObsClose

/-- **Two laws read alike by every bounded observable.** `ObsClose μ ν ε`: every measurable
`f : β → ℝ` with `|f| ≤ 1` has `|∫ f dμ − ∫ f dν| ≤ ε`. At probability measures the least such `ε`
is twice the total-variation distance `sup_s |μ s − ν s|` (the standard duality);
`ObsClose.abs_real_sub_le` is the direction used here.

DERIVED: `1` is the unit bound of the observable; `ObsClose.abs_integral_sub_le` carries any bound
`M`. -/
def ObsClose (μ ν : Measure β) (ε : ℝ) : Prop :=
  ∀ f : β → ℝ, Measurable f → (∀ y, |f y| ≤ 1) → |∫ y, f y ∂μ - ∫ y, f y ∂ν| ≤ ε

/-- The tolerance of `ObsClose` is nonnegative: the zero observable reads `0` on both sides.

DERIVED: `0` is the zero observable and the sign concluded; `1` the unit bound. -/
theorem ObsClose.nonneg {μ ν : Measure β} {ε : ℝ} (h : ObsClose μ ν ε) : 0 ≤ ε := by
  have h0 := h (fun _ => (0 : ℝ)) measurable_const (fun _ => by simp)
  simpa using h0

#print axioms ObsClose.nonneg

/-- A law is `ObsClose` to itself at tolerance `0`.

DERIVED: `0` is the tolerance. -/
theorem obsClose_refl (μ : Measure β) : ObsClose μ μ 0 := fun f _ _ => by simp

#print axioms obsClose_refl

/-- `ObsClose` is monotone in the tolerance.

DERIVED: no numeral. -/
theorem ObsClose.mono {μ ν : Measure β} {ε ε' : ℝ} (h : ObsClose μ ν ε) (hle : ε ≤ ε') :
    ObsClose μ ν ε' :=
  fun f hf hb => (h f hf hb).trans hle

#print axioms ObsClose.mono

/-- `ObsClose` is symmetric.

DERIVED: no numeral. -/
theorem ObsClose.symm {μ ν : Measure β} {ε : ℝ} (h : ObsClose μ ν ε) : ObsClose ν μ ε :=
  fun f hf hb => by
    rw [abs_sub_comm]
    exact h f hf hb

#print axioms ObsClose.symm

/-- **The triangle inequality** for `ObsClose`.

DERIVED: no numeral. -/
theorem ObsClose.trans {μ ν ρ : Measure β} {ε δ : ℝ} (h : ObsClose μ ν ε) (h' : ObsClose ν ρ δ) :
    ObsClose μ ρ (ε + δ) :=
  fun f hf hb =>
    (abs_sub_le (∫ y, f y ∂μ) (∫ y, f y ∂ν) (∫ y, f y ∂ρ)).trans
      (add_le_add (h f hf hb) (h' f hf hb))

#print axioms ObsClose.trans

/-- **Setwise closeness**: `ObsClose μ ν ε` gives `|μ s − ν s| ≤ ε` at every measurable `s`, from the
indicator of `s`.

DERIVED: `1` is the value of the indicator on `s` and its bound; `0` its value off `s`. -/
theorem ObsClose.abs_real_sub_le {μ ν : Measure β} {ε : ℝ} (h : ObsClose μ ν ε) {s : Set β}
    (hs : MeasurableSet s) : |μ.real s - ν.real s| ≤ ε := by
  have h1 := h (s.indicator 1) (measurable_one.indicator hs) (fun y => by
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy]
      simp)
  rwa [integral_indicator_one hs, integral_indicator_one hs] at h1

#print axioms ObsClose.abs_real_sub_le

/-- **Observables bounded by `M`**: `ObsClose μ ν ε` and `|f| ≤ M` give
`|∫ f dμ − ∫ f dν| ≤ M ε`, by reading `f / M`.

DERIVED: `0` is the sign of `M`; `1` the unit bound `f / M` meets. -/
theorem ObsClose.abs_integral_sub_le {μ ν : Measure β} {ε : ℝ} (h : ObsClose μ ν ε)
    {f : β → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 < M) (hfM : ∀ y, |f y| ≤ M) :
    |∫ y, f y ∂μ - ∫ y, f y ∂ν| ≤ M * ε := by
  have h1 : |∫ y, f y / M ∂μ - ∫ y, f y / M ∂ν| ≤ ε :=
    h (fun y => f y / M) (hf.div_const M) (fun y => by
      show |f y / M| ≤ 1
      rw [abs_div, abs_of_pos hM, div_le_one₀ hM]
      exact hfM y)
  rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hM, div_le_iff₀ hM] at h1
  rw [mul_comm]
  exact h1

#print axioms ObsClose.abs_integral_sub_le

/-- **Coarse-graining contracts.** `ObsClose μ ν ε` and a measurable `χ` give
`ObsClose (μ.map χ) (ν.map χ) ε`: an observable of the coarse view is the observable `f ∘ χ` of the
fine one.

DERIVED: no numeral. -/
theorem ObsClose.map {μ ν : Measure β} {ε : ℝ} (h : ObsClose μ ν ε) {χ : β → γ}
    (hχ : Measurable χ) : ObsClose (μ.map χ) (ν.map χ) ε := by
  intro f hf hb
  rw [integral_map hχ.aemeasurable hf.aestronglyMeasurable,
    integral_map hχ.aemeasurable hf.aestronglyMeasurable]
  exact h (fun x => f (χ x)) (hf.comp hχ) (fun x => hb (χ x))

#print axioms ObsClose.map

/-- A bounded observable of a probability law has expectation bounded by the same constant.

DERIVED: `1` is the total mass. -/
theorem abs_integral_le_of_prob {μ : Measure β} (hp : IsProbabilityMeasure μ) {f : β → ℝ}
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) : |∫ y, f y ∂μ| ≤ M := by
  haveI := hp
  have h0 : ‖∫ y, f y ∂μ‖ ≤ M * μ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hfM y))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h0

#print axioms abs_integral_le_of_prob

end ObsClose

/-! ## 2. The same forest: summable increments -/

section Forest

/-- **A real sequence with summable increments converges, at the tail rate.** `|s (k+1) − s k| ≤ d k`
with `d` summable gives a limit `L` along `atTop` and `|s n − L| ≤ ∑' i, d (n + i)`.

DERIVED: `1` is the step. -/
theorem exists_tendsto_of_abs_sub_le {s d : ℕ → ℝ} (hd : Summable d)
    (hs : ∀ k, |s (k + 1) - s k| ≤ d k) :
    ∃ L : ℝ, Tendsto s atTop (𝓝 L) ∧ ∀ n, |s n - L| ≤ ∑' i, d (n + i) := by
  have hdist : ∀ n, dist (s n) (s n.succ) ≤ d n := fun n => by
    rw [Real.dist_eq, abs_sub_comm]
    exact hs n
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hdist hd)
  refine ⟨L, hL, fun n => ?_⟩
  have h := dist_le_tsum_of_dist_le_of_tendsto d hdist hd hL n
  rwa [Real.dist_eq] at h

#print axioms exists_tendsto_of_abs_sub_le

/-- The tail sums `∑' i, ε (n + i)` tend to `0`.

DERIVED: `0` is the limit. -/
theorem tendsto_tail (ε : ℕ → ℝ) : Tendsto (fun n => ∑' i, ε (n + i)) atTop (𝓝 0) :=
  (tendsto_sum_nat_add ε).congr (fun n => tsum_congr (fun i => by rw [add_comm]))

#print axioms tendsto_tail

/-- **The same forest along a sequence of laws, with its increments.** `ForestAt m ε`: the
increments `ε k` are summable and successive laws are `ObsClose` at `ε k`.

DERIVED: `1` is the step. -/
structure ForestAt (m : ℕ → Measure β) (ε : ℕ → ℝ) : Prop where
  /-- The increments are summable. -/
  summable : Summable ε
  /-- Successive laws read alike up to the increment. -/
  step : ∀ k, ObsClose (m (k + 1)) (m k) (ε k)

/-- **Cauchy in observable total variation, finite form**: the law at `n + j` is `ObsClose` to the
law at `n` at the partial sum `∑_{i < j} ε (n + i)`.

DERIVED: `0` is the base of the induction; `1` the step. -/
theorem ForestAt.obsClose_add {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε) (n j : ℕ) :
    ObsClose (m (n + j)) (m n) (∑ i ∈ Finset.range j, ε (n + i)) := by
  induction j with
  | zero => simpa using obsClose_refl (m n)
  | succ j ih =>
    rw [Finset.sum_range_succ, add_comm (∑ i ∈ Finset.range j, ε (n + i)), ← add_assoc]
    exact (h.step (n + j)).trans ih

#print axioms ForestAt.obsClose_add

/-- **Cauchy in observable total variation, tail form**: for every `j`, the law at `n + j` is
`ObsClose` to the law at `n` at the tail `∑' i, ε (n + i)`, uniformly in `j`.

DERIVED: `0` is the sign of the increments. -/
theorem ForestAt.obsClose_tail {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε) (n j : ℕ) :
    ObsClose (m (n + j)) (m n) (∑' i, ε (n + i)) := by
  have hs : Summable (fun i => ε (n + i)) :=
    ((summable_nat_add_iff n).mpr h.summable).congr (fun i => by rw [add_comm])
  refine (h.obsClose_add n j).mono ?_
  exact hs.sum_le_tsum _ (fun i _ => (h.step (n + i)).nonneg)

#print axioms ForestAt.obsClose_tail

/-- **The laws are Cauchy in observable total variation.** For every `δ > 0` there is `N` with the
law at `n + j` `ObsClose` to the law at `n` at `δ`, for all `n ≥ N` and all `j`.

DERIVED: `0` is the sign of `δ`. -/
theorem ForestAt.cauchy {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε) {δ : ℝ}
    (hδ : 0 < δ) : ∃ N : ℕ, ∀ n, N ≤ n → ∀ j, ObsClose (m (n + j)) (m n) δ := by
  have hev : ∀ᶠ n in atTop, ∑' i, ε (n + i) < δ := (tendsto_order.1 (tendsto_tail ε)).2 δ hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, fun n hn j => (h.obsClose_tail n j).mono (hN n hn).le⟩

#print axioms ForestAt.cauchy

/-- **The forest limit of an observable**: `limUnder atTop` of its expectations. Under `ForestAt`
this is the limit along `atTop` of every bounded measurable observable (`ForestAt.tendsto`).

DERIVED: no numeral. -/
def forestLimit (m : ℕ → Measure β) (f : β → ℝ) : ℝ :=
  limUnder atTop (fun k => ∫ y, f y ∂(m k))

/-- **Every bounded observable converges, at the tail rate.** Under `ForestAt m ε`, a measurable
`f` with `|f| ≤ M` has `∫ f d(m k) → forestLimit m f` along `atTop`, and
`|∫ f d(m n) − forestLimit m f| ≤ M · ∑' i, ε (n + i)` at every `n`: one rate for every observable
bounded by `M`.

DERIVED: `0` is the sign of `M`. -/
theorem ForestAt.tendsto {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε) {f : β → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : 0 < M) (hfM : ∀ y, |f y| ≤ M) :
    Tendsto (fun k => ∫ y, f y ∂(m k)) atTop (𝓝 (forestLimit m f)) ∧
      ∀ n, |∫ y, f y ∂(m n) - forestLimit m f| ≤ M * ∑' i, ε (n + i) := by
  obtain ⟨L, hL, hrate⟩ := exists_tendsto_of_abs_sub_le (s := fun k => ∫ y, f y ∂(m k))
    (h.summable.mul_left M) (fun k => (h.step k).abs_integral_sub_le hf hM hfM)
  have hlim : forestLimit m f = L := hL.limUnder_eq
  refine ⟨by rw [hlim]; exact hL, fun n => ?_⟩
  rw [hlim, ← tsum_mul_left]
  exact hrate n

#print axioms ForestAt.tendsto

/-- **The forest limit is additive** on bounded measurable observables of probability laws.

DERIVED: `0` is the sign of the bounds. -/
theorem ForestAt.forestLimit_add {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {f g : β → ℝ} (hf : Measurable f)
    (hg : Measurable g) {Mf Mg : ℝ} (hMf : 0 < Mf) (hMg : 0 < Mg) (hfM : ∀ y, |f y| ≤ Mf)
    (hgM : ∀ y, |g y| ≤ Mg) :
    forestLimit m (fun y => f y + g y) = forestLimit m f + forestLimit m g := by
  have hfg := (h.tendsto (hf.add hg) (add_pos hMf hMg)
    (fun y => (abs_add_le (f y) (g y)).trans (add_le_add (hfM y) (hgM y)))).1
  have h1 := (h.tendsto hf hMf hfM).1
  have h2 := (h.tendsto hg hMg hgM).1
  have hfg' : Tendsto (fun k => ∫ y, f y ∂(m k) + ∫ y, g y ∂(m k)) atTop
      (𝓝 (forestLimit m (fun y => f y + g y))) :=
    hfg.congr (fun k => by
      haveI := hprob k
      exact integral_add
        (Integrable.of_bound hf.aestronglyMeasurable Mf
          (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact hfM y)))
        (Integrable.of_bound hg.aestronglyMeasurable Mg
          (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact hgM y))))
  exact tendsto_nhds_unique hfg' (h1.add h2)

#print axioms ForestAt.forestLimit_add

/-- **The forest limit is positive.**

DERIVED: `0` is the lower bound, hypothesised pointwise and concluded; and the sign of `M`. -/
theorem ForestAt.forestLimit_nonneg {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε)
    {f : β → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 < M) (hfM : ∀ y, |f y| ≤ M)
    (hf0 : ∀ y, 0 ≤ f y) : 0 ≤ forestLimit m f :=
  ge_of_tendsto' (h.tendsto hf hM hfM).1 (fun _ => integral_nonneg hf0)

#print axioms ForestAt.forestLimit_nonneg

/-- **The forest limit is normalised** at probability laws: the constant `1` has limit `1`.

DERIVED: `1` is the constant observable and the total mass. -/
theorem forestLimit_one (m : ℕ → Measure β) (hprob : ∀ k, IsProbabilityMeasure (m k)) :
    forestLimit m (fun _ => 1) = 1 := by
  have e : (fun k => ∫ _y, (1 : ℝ) ∂(m k)) = fun _ => (1 : ℝ) := by
    funext k
    haveI := hprob k
    rw [integral_const, probReal_univ, one_smul]
  show limUnder atTop (fun k => ∫ _y, (1 : ℝ) ∂(m k)) = 1
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

#print axioms forestLimit_one

end Forest

/-! ## 3. The observer's view -/

section View

/-- **The observer's law at step `k`**: the pushforward of the step-`k` measure by the step-`k`
observer map, into the fixed observer space `β`.

DERIVED: no numeral. -/
abbrev observerLaw (μ : ℕ → Measure α) (φ : ℕ → α → β) (k : ℕ) : Measure β := (μ k).map (φ k)

/-- **The same forest seen by one observer, with its increments**: `ForestAt` of the observer laws
`(μ k).map (φ k)`.

DERIVED: no numeral. -/
abbrev SameForestAt (μ : ℕ → Measure α) (φ : ℕ → α → β) (ε : ℕ → ℝ) : Prop :=
  ForestAt (fun k => (μ k).map (φ k)) ε

/-- **The same forest seen by one observer**: some summable increments exist.

DERIVED: no numeral. -/
def SameForest (μ : ℕ → Measure α) (φ : ℕ → α → β) : Prop :=
  ∃ ε : ℕ → ℝ, SameForestAt μ φ ε

/-- **The observer's coarse readings converge.** Under `SameForestAt μ φ ε` and measurable observer
maps, a measurable `g` on the observer space with `|g| ≤ M` has
`∫ g (φ k x) ∂(μ k) → forestLimit (observer laws) g` along `atTop`, at the rate
`M · ∑' i, ε (n + i)`.

DERIVED: `0` is the sign of `M`. -/
theorem SameForestAt.tendsto_coarse {μ : ℕ → Measure α} {φ : ℕ → α → β} {ε : ℕ → ℝ}
    (h : SameForestAt μ φ ε) (hφ : ∀ k, Measurable (φ k)) {g : β → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : 0 < M) (hgM : ∀ y, |g y| ≤ M) :
    Tendsto (fun k => ∫ x, g (φ k x) ∂(μ k)) atTop
        (𝓝 (forestLimit (fun k => (μ k).map (φ k)) g)) ∧
      ∀ n, |∫ x, g (φ n x) ∂(μ n) - forestLimit (fun k => (μ k).map (φ k)) g|
        ≤ M * ∑' i, ε (n + i) := by
  have he : ∀ k, ∫ y, g y ∂((μ k).map (φ k)) = ∫ x, g (φ k x) ∂(μ k) := fun k =>
    integral_map (hφ k).aemeasurable hg.aestronglyMeasurable
  obtain ⟨h1, h2⟩ := ForestAt.tendsto h hg hM hgM
  refine ⟨h1.congr he, fun n => ?_⟩
  rw [← he n]
  exact h2 n

#print axioms SameForestAt.tendsto_coarse

/-- **From the beach to the cliff.** At measurable observer maps, a coarser observer, reading the
observer space through a measurable `χ`, sees the same forest with the same increments.

DERIVED: no numeral. -/
theorem SameForestAt.comp {μ : ℕ → Measure α} {φ : ℕ → α → β} {ε : ℕ → ℝ}
    (h : SameForestAt μ φ ε) (hφ : ∀ k, Measurable (φ k)) {χ : β → γ} (hχ : Measurable χ) :
    SameForestAt μ (fun k => χ ∘ φ k) ε := by
  refine ⟨h.summable, fun k => ?_⟩
  have hk : ObsClose ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) (ε k) := h.step k
  show ObsClose ((μ (k + 1)).map (χ ∘ φ (k + 1))) ((μ k).map (χ ∘ φ k)) (ε k)
  rw [← Measure.map_map hχ (hφ (k + 1)), ← Measure.map_map hχ (hφ k)]
  exact hk.map hχ

#print axioms SameForestAt.comp

/-- **The cliff's view is the beach's view through `χ`.** The forest limit of the coarse observer at
`g` is the forest limit of the fine observer at `g ∘ χ`, term by term.

DERIVED: no numeral. -/
theorem forestLimit_map_comp (μ : ℕ → Measure α) (φ : ℕ → α → β) (hφ : ∀ k, Measurable (φ k))
    {χ : β → γ} (hχ : Measurable χ) {g : γ → ℝ} (hg : Measurable g) :
    forestLimit (fun k => (μ k).map (χ ∘ φ k)) g
      = forestLimit (fun k => (μ k).map (φ k)) (fun y => g (χ y)) := by
  have e : (fun k => ∫ z, g z ∂((μ k).map (χ ∘ φ k)))
      = fun k => ∫ y, g (χ y) ∂((μ k).map (φ k)) := by
    funext k
    rw [← Measure.map_map hχ (hφ k), integral_map hχ.aemeasurable hg.aestronglyMeasurable]
  show limUnder atTop (fun k => ∫ z, g z ∂((μ k).map (χ ∘ φ k)))
    = limUnder atTop (fun k => ∫ y, g (χ y) ∂((μ k).map (φ k)))
  rw [e]

#print axioms forestLimit_map_comp

end View

/-! ## 4. Relative entropy -/

section Entropy

/-- **Pinsker's inequality in observable form (proved as `ChiForest.pinskerObs`).** For probability measures `P`, `Q` with
`klDiv P Q` finite, `ObsClose P Q (√(2 · KL(P‖Q)))`: every measurable `|f| ≤ 1` has
`|∫ f dP − ∫ f dQ| ≤ √(2 KL)`, which is `2 · TV ≤ 2 √(KL/2)` (Pinsker 1964; Csiszár 1967;
Kemperman 1969), with `KL` in nats as `klDiv` defines it.

DERIVED: `2` is Pinsker's constant in the observable form: twice the total variation against
`√(KL/2)`. -/
def PinskerObs : Prop :=
  ∀ (δ : Type) [MeasurableSpace δ] (P Q : Measure δ), IsProbabilityMeasure P →
    IsProbabilityMeasure Q → klDiv P Q ≠ ∞ → ObsClose P Q (Real.sqrt (2 * (klDiv P Q).toReal))

/-- **The data-processing inequality for pushforwards (proved as `ChiForest.klDataProcessing`).** For probability measures `P`,
`Q` and a measurable `χ`, `klDiv (P.map χ) (Q.map χ) ≤ klDiv P Q`. Mathlib at
the pin has the chain rule (`klDiv_compProd_eq_add`) and invariance under a common kernel
(`klDiv_compProd_left`), and no statement for `Measure.map`.

DERIVED: no numeral. -/
def KLDataProcessing : Prop :=
  ∀ (δ η : Type) [MeasurableSpace δ] [MeasurableSpace η] (P Q : Measure δ) (χ : δ → η),
    IsProbabilityMeasure P → IsProbabilityMeasure Q → Measurable χ →
      klDiv (P.map χ) (Q.map χ) ≤ klDiv P Q

/-- **The same forest in entropy.** The relative entropy of the step-`(k+1)` observer law to the
step-`k` one is finite at every step, and its square roots are summable.

DERIVED: `1` is the step. -/
structure SameForestKL (μ : ℕ → Measure α) (φ : ℕ → α → β) : Prop where
  /-- Every successive relative entropy is finite. -/
  finite : ∀ k, klDiv ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) ≠ ∞
  /-- The square roots of the successive relative entropies are summable. -/
  summable :
    Summable (fun k => Real.sqrt ((klDiv ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k))).toReal))

/-- **Entropy gives the forest.** Under `PinskerObs`, `SameForestKL μ φ` at probability measures and
measurable observer maps gives `SameForestAt μ φ ε` with `ε k = √(2 · KL_k)`.

DERIVED: `2` is `PinskerObs`'s constant; `1` the step. -/
theorem SameForestKL.sameForestAt {μ : ℕ → Measure α} {φ : ℕ → α → β} (h : SameForestKL μ φ)
    (hP : PinskerObs) (hprob : ∀ k, IsProbabilityMeasure (μ k)) (hφ : ∀ k, Measurable (φ k)) :
    SameForestAt μ φ
      (fun k => Real.sqrt (2 * (klDiv ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k))).toReal)) := by
  refine ⟨?_, fun k => ?_⟩
  · exact (h.summable.mul_left (Real.sqrt 2)).congr
      (fun k => (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _).symm)
  · haveI := hprob (k + 1)
    haveI := hprob k
    have h1 : IsProbabilityMeasure ((μ (k + 1)).map (φ (k + 1))) :=
      Measure.isProbabilityMeasure_map (hφ (k + 1)).aemeasurable
    have h0 : IsProbabilityMeasure ((μ k).map (φ k)) :=
      Measure.isProbabilityMeasure_map (hφ k).aemeasurable
    exact hP β ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) h1 h0 (h.finite k)

#print axioms SameForestKL.sameForestAt

/-- **A coarser observer inherits the entropy forest.** Under `KLDataProcessing`, `SameForestKL μ φ`
gives `SameForestKL μ (χ ∘ φ ·)` for every measurable `χ`.

DERIVED: `1` is the step. -/
theorem SameForestKL.comp {μ : ℕ → Measure α} {φ : ℕ → α → β} (h : SameForestKL μ φ)
    (hD : KLDataProcessing) (hprob : ∀ k, IsProbabilityMeasure (μ k)) (hφ : ∀ k, Measurable (φ k))
    {χ : β → γ} (hχ : Measurable χ) : SameForestKL μ (fun k => χ ∘ φ k) := by
  have hle : ∀ k, klDiv ((μ (k + 1)).map (χ ∘ φ (k + 1))) ((μ k).map (χ ∘ φ k))
      ≤ klDiv ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) := by
    intro k
    haveI := hprob (k + 1)
    haveI := hprob k
    rw [← Measure.map_map hχ (hφ (k + 1)), ← Measure.map_map hχ (hφ k)]
    exact hD β γ ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) χ
      (Measure.isProbabilityMeasure_map (hφ (k + 1)).aemeasurable)
      (Measure.isProbabilityMeasure_map (hφ k).aemeasurable) hχ
  refine ⟨fun k => ne_top_of_le_ne_top (h.finite k) (hle k), ?_⟩
  exact Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _)
    (fun k => Real.sqrt_le_sqrt (ENNReal.toReal_mono (h.finite k) (hle k))) h.summable

#print axioms SameForestKL.comp

/-- **A bounded log-likelihood ratio bounds the relative entropy.** For probability measures
`P ≪ Q` with `|llr P Q| ≤ D` `P`-almost everywhere, `klDiv P Q ≤ ENNReal.ofReal D`: the ratio is
integrable, the
mass terms cancel, and the integral of `llr` is at most `D`.

DERIVED: `1` is the total mass of each measure, which cancels in the mass terms. -/
theorem klDiv_le_of_abs_llr_le {P Q : Measure γ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P ≪ Q) {D : ℝ} (hD : ∀ᵐ x ∂P, |llr P Q x| ≤ D) : klDiv P Q ≤ ENNReal.ofReal D := by
  have hint : Integrable (llr P Q) P :=
    Integrable.of_bound (measurable_llr P Q).aestronglyMeasurable D
      (hD.mono (fun x hx => by rw [Real.norm_eq_abs]; exact hx))
  rw [klDiv_of_ac_of_integrable hac hint]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ∫ x, llr P Q x ∂P ≤ ∫ _x, D ∂P :=
    integral_mono_ae hint (integrable_const D) (hD.mono (fun x hx => (le_abs_self _).trans hx))
  have hc : ∫ _x, D ∂P = D := by rw [integral_const, probReal_univ, one_smul]
  rw [probReal_univ, probReal_univ, add_sub_cancel_right]
  exact h1.trans_eq hc

#print axioms klDiv_le_of_abs_llr_le

/-- **Bounded log-ratios between successive views.** At every step the step-`(k+1)` observer law is
absolutely continuous with respect to the step-`k` one, and their log-likelihood ratio is bounded by
`D k` almost surely.

DERIVED: `1` is the step. -/
structure ZoomLogRatio (μ : ℕ → Measure α) (φ : ℕ → α → β) (D : ℕ → ℝ) : Prop where
  /-- The finer view is absolutely continuous with respect to the coarser one. -/
  ac : ∀ k, (μ (k + 1)).map (φ (k + 1)) ≪ (μ k).map (φ k)
  /-- The log-likelihood ratio is bounded by `D k` almost surely. -/
  bound : ∀ k, ∀ᵐ y ∂((μ (k + 1)).map (φ (k + 1))),
    |llr ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) y| ≤ D k

/-- **Bounded log-ratios with summable square roots give the entropy forest.**

DERIVED: `0` is the sign of the bounds. -/
theorem ZoomLogRatio.sameForestKL {μ : ℕ → Measure α} {φ : ℕ → α → β} {D : ℕ → ℝ}
    (h : ZoomLogRatio μ φ D) (hprob : ∀ k, IsProbabilityMeasure (μ k))
    (hφ : ∀ k, Measurable (φ k)) (hD0 : ∀ k, 0 ≤ D k)
    (hDs : Summable (fun k => Real.sqrt (D k))) : SameForestKL μ φ := by
  have hkl : ∀ k, klDiv ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k)) ≤ ENNReal.ofReal (D k) := by
    intro k
    haveI : IsProbabilityMeasure ((μ (k + 1)).map (φ (k + 1))) :=
      Measure.isProbabilityMeasure_map (hφ (k + 1)).aemeasurable
    haveI : IsProbabilityMeasure ((μ k).map (φ k)) :=
      Measure.isProbabilityMeasure_map (hφ k).aemeasurable
    exact klDiv_le_of_abs_llr_le (h.ac k) (h.bound k)
  refine ⟨fun k => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hkl k), ?_⟩
  exact Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _)
    (fun k => Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (hD0 k) (hkl k))) hDs

#print axioms ZoomLogRatio.sameForestKL

/-- **Geometric log-ratios between successive views.** There are `C ≥ 0` and `0 ≤ θ < 1` with the
log-likelihood ratio of successive observer laws bounded by `C θ^{2k}`.

DERIVED: `0` is the lower end of `C` and `θ`; `1` the upper end of `θ`; `2` the square that
Pinsker's square root removes. CHOSEN: the geometric form, `θ = 2^{-γ}` for corrections of order
`a_k^γ` at the halving spacings; any form with summable square roots serves
(`ZoomLogRatio.sameForestKL`). -/
def ZoomGeometric (μ : ℕ → Measure α) (φ : ℕ → α → β) : Prop :=
  ∃ C θ : ℝ, 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧ ZoomLogRatio μ φ (fun k => C * (θ ^ k) ^ 2)

/-- **Geometric log-ratios give the entropy forest**: `ZoomGeometric μ φ` at probability measures
and measurable observer maps gives `SameForestKL μ φ`. The proof bounds `√KL_k` by `√C θ^k`; the
statement carries no rate.

DERIVED: `2` is the square of `ZoomGeometric`. -/
theorem ZoomGeometric.sameForestKL {μ : ℕ → Measure α} {φ : ℕ → α → β} (h : ZoomGeometric μ φ)
    (hprob : ∀ k, IsProbabilityMeasure (μ k)) (hφ : ∀ k, Measurable (φ k)) :
    SameForestKL μ φ := by
  obtain ⟨C, θ, hC, hθ, hθ1, hz⟩ := h
  refine hz.sameForestKL hprob hφ (fun k => mul_nonneg hC (sq_nonneg _)) ?_
  exact ((summable_geometric_of_lt_one hθ hθ1).mul_left (Real.sqrt C)).congr (fun k => by
    show Real.sqrt C * θ ^ k = Real.sqrt (C * (θ ^ k) ^ 2)
    rw [Real.sqrt_mul hC, Real.sqrt_sq (pow_nonneg hθ k)])

#print axioms ZoomGeometric.sameForestKL

end Entropy

/-! ## 5. Connected correlations: what the forest gives at one observer scale -/

section Connected

/-- The algebra of the connected-correlation comparison: if `xab`, `xa`, `xb` are within
`M² T`, `M T`, `M T` of `lab`, `la`, `lb`, and `|xb|, |la| ≤ M`, the connected combinations are within
`3 M² T`.

DERIVED: `3` counts the three differences `xab − lab`, `(xa − la) xb`, `la (xb − lb)`; `0` is the
sign of `M` and `T`. -/
theorem abs_conn_sub_le_aux {xab xa xb lab la lb M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hab : |xab - lab| ≤ M * M * T) (ha : |xa - la| ≤ M * T) (hb : |xb - lb| ≤ M * T)
    (hxb : |xb| ≤ M) (hla : |la| ≤ M) :
    |(xab - xa * xb) - (lab - la * lb)| ≤ 3 * (M * M) * T := by
  have e : (xab - xa * xb) - (lab - la * lb)
      = (xab - lab) - ((xa - la) * xb + la * (xb - lb)) := by ring
  have hY : |(xa - la) * xb| ≤ M * T * M := by
    rw [abs_mul]
    exact mul_le_mul ha hxb (abs_nonneg _) (mul_nonneg hM hT)
  have hZ : |la * (xb - lb)| ≤ M * (M * T) := by
    rw [abs_mul]
    exact mul_le_mul hla hb (abs_nonneg _) hM
  rw [e, abs_le]
  constructor
  · linarith [neg_abs_le (xab - lab), le_abs_self ((xa - la) * xb), le_abs_self (la * (xb - lb))]
  · linarith [le_abs_self (xab - lab), neg_abs_le ((xa - la) * xb), neg_abs_le (la * (xb - lb))]

#print axioms abs_conn_sub_le_aux

/-- **The step-`n` connected correlation is within `3 M² · tail(n)` of the limit's.** Under
`ForestAt m ε` at probability laws, for measurable `a`, `b` with `|a|, |b| ≤ M`:
`|(∫ ab − ∫ a ∫ b)(m n) − (L(ab) − L(a) L(b))| ≤ 3 M² ∑' i, ε (n + i)`, `L = forestLimit m`.

DERIVED: `3` is `abs_conn_sub_le_aux`'s; `0` the sign of `M`. -/
theorem ForestAt.abs_conn_sub_le {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {a b : β → ℝ} (ha : Measurable a)
    (hb : Measurable b) {M : ℝ} (hM : 0 < M) (haM : ∀ y, |a y| ≤ M) (hbM : ∀ y, |b y| ≤ M)
    (n : ℕ) :
    |(∫ y, a y * b y ∂(m n) - (∫ y, a y ∂(m n)) * ∫ y, b y ∂(m n))
      - (forestLimit m (fun y => a y * b y) - forestLimit m a * forestLimit m b)|
      ≤ 3 * (M * M) * ∑' i, ε (n + i) := by
  have hT : 0 ≤ ∑' i, ε (n + i) := tsum_nonneg (fun i => (h.step (n + i)).nonneg)
  have habM : ∀ y, |a y * b y| ≤ M * M := fun y => by
    rw [abs_mul]
    exact mul_le_mul (haM y) (hbM y) (abs_nonneg _) hM.le
  obtain ⟨-, hrab⟩ := h.tendsto (ha.mul hb) (mul_pos hM hM) habM
  obtain ⟨hla, hra⟩ := h.tendsto ha hM haM
  obtain ⟨-, hrb⟩ := h.tendsto hb hM hbM
  have hLa : |forestLimit m a| ≤ M :=
    le_of_tendsto' hla.abs (fun k => abs_integral_le_of_prob (hprob k) haM)
  exact abs_conn_sub_le_aux hM.le hT (hrab n) (hra n) (hrb n)
    (abs_integral_le_of_prob (hprob n) hbM) hLa

#print axioms ForestAt.abs_conn_sub_le

/-- **Decay of the limit at one observer scale transfers to every step, up to the tail.** If the
limit's connected correlation of `a`, `b` is at most `D` in absolute value, the step-`n` one is at
most `D + 3 M² ∑' i, ε (n + i)`. The remainder is additive and does not scale with the variance of
`a`; `WeakCouplingWindow.FixedWindowDecay` needs a remainder relative to the lag-zero value (see the
module docstring).

DERIVED: `3` is `ForestAt.abs_conn_sub_le`'s; `0` the sign of `M`. -/
theorem ForestAt.abs_conn_le {m : ℕ → Measure β} {ε : ℕ → ℝ} (h : ForestAt m ε)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {a b : β → ℝ} (ha : Measurable a)
    (hb : Measurable b) {M : ℝ} (hM : 0 < M) (haM : ∀ y, |a y| ≤ M) (hbM : ∀ y, |b y| ≤ M)
    {D : ℝ} (hD : |forestLimit m (fun y => a y * b y) - forestLimit m a * forestLimit m b| ≤ D)
    (n : ℕ) :
    |∫ y, a y * b y ∂(m n) - (∫ y, a y ∂(m n)) * ∫ y, b y ∂(m n)|
      ≤ D + 3 * (M * M) * ∑' i, ε (n + i) := by
  have h1 := h.abs_conn_sub_le hprob ha hb hM haM hbM n
  have h2 := abs_add_le
    ((∫ y, a y * b y ∂(m n) - (∫ y, a y ∂(m n)) * ∫ y, b y ∂(m n))
      - (forestLimit m (fun y => a y * b y) - forestLimit m a * forestLimit m b))
    (forestLimit m (fun y => a y * b y) - forestLimit m a * forestLimit m b)
  rw [sub_add_cancel] at h2
  linarith

#print axioms ForestAt.abs_conn_le

end Connected

/-! ## 6. The tree: `ContinuumSchwinger` and the Wilson views -/

section Tree

open MassGap.ContinuumSchwinger

/-- **The continuum Schwinger function is the genuine limit of a family the observer reads.** If at
every step `latSkR hN ρ k F = ∫ g (φ k x) ∂(μ k)` for one measurable observer observable `g` with
`|g| ≤ M`, then `SameForestAt μ φ ε` makes `latSkR hN ρ k F → contS hN ρ F` along `atTop`, with
`|latSkR hN ρ n F − contS hN ρ F| ≤ M · ∑' i, ε (n + i)`. `UniformBound` is not used: the value
`contS` picks along `ultra` is the `atTop` limit.

Scope. `hread` asks one bound `M` on `g` at every step. With the Gibbs measures and the renormalised
smeared fields as observer it holds at bounded renormalisation data, where successive observer laws
are expected to stay at total-variation distance of order one; with `Z` growing the product
observable is unbounded in `k` and no bounded `g` reads it. Over an arbitrary observer the two
hypotheses are satisfiable exactly when `latSkR hN ρ k F` has summable increments (module
docstring), so the physics is in exhibiting the physical `μ`, `φ`, `g`.

DERIVED: `0` is the excluded colour count and the sign of `M`. -/
theorem tendsto_latSkR_of_sameForestAt {N : ℕ} (hN : N ≠ 0) (ρ : Renorm N) {ι : Type}
    [Fintype ι] (F : ι → SField N) {μ : ℕ → Measure α} {φ : ℕ → α → β} {ε : ℕ → ℝ}
    (h : SameForestAt μ φ ε) (hφ : ∀ k, Measurable (φ k)) {g : β → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : 0 < M) (hgM : ∀ y, |g y| ≤ M)
    (hread : ∀ k, latSkR hN ρ k F = ∫ x, g (φ k x) ∂(μ k)) :
    Tendsto (fun k => latSkR hN ρ k F) atTop (𝓝 (contS hN ρ F)) ∧
      ∀ n, |latSkR hN ρ n F - contS hN ρ F| ≤ M * ∑' i, ε (n + i) := by
  obtain ⟨h1, h2⟩ := h.tendsto_coarse hφ hg hM hgM
  have hs : (fun k => latSkR hN ρ k F) = fun k => ∫ x, g (φ k x) ∂(μ k) := funext hread
  have hc : contS hN ρ F = forestLimit (fun k => (μ k).map (φ k)) g := by
    haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
    show limUnder (ultra : Filter ℕ) (fun k => latSkR hN ρ k F) = _
    rw [hs]
    exact (h1.mono_left ultra_le).limUnder_eq
  refine ⟨?_, fun n => ?_⟩
  · rw [hc, hs]
    exact h1
  · rw [hc, hread n]
    exact h2 n

#print axioms tendsto_latSkR_of_sameForestAt

/-- **THE OPEN DYNAMICAL INPUT (stated).** For observer maps `φ k : Cfg N → β` at a fixed physical
resolution and region, the Wilson states `stateK hN k` at the dyadic couplings are represented by
probability measures `μ k` (`∫ f dμ_k = stateK hN k f` on continuous observables), and the
successive views satisfy `ZoomGeometric μ φ`: log-likelihood ratios bounded by `C θ^{2k}`.
`DLRLimit.gibbsMeasure (stateK hN k)` supplies a representing probability measure
(`DLRLimit.integral_gibbsMeasure`, `DLRLimit.instIsProbabilityMeasure`).

The content is in `φ`: at a constant `φ` every view is one Dirac law and `ZoomGeometric` holds with
`C = 0`. With `φ` the smeared fields at bounded renormalisation data the observer laws concentrate
and successive laws are expected to stay at total-variation distance of order one, so under
`PinskerObs` the input fails there; it is meant for renormalised coordinates whose laws have a
non-degenerate limit.

DERIVED: `0` is the excluded colour count. -/
def WilsonZoomInput {N : ℕ} (hN : N ≠ 0) (φ : ℕ → Cfg N → β) : Prop :=
  ∃ μ : ℕ → Measure (Cfg N), (∀ k, IsProbabilityMeasure (μ k)) ∧
    (∀ (k : ℕ) (f : C(Cfg N, ℝ)), ∫ x, f x ∂(μ k) = stateK hN k f) ∧ ZoomGeometric μ φ

/-- **The Wilson observer's coarse readings converge**, under `PinskerObs` and `WilsonZoomInput`: for
continuous observables `G k = g ∘ φ k` with `g` measurable and `|g| ≤ M`, the values
`stateK hN k (G k)` converge along `atTop`, at the rate `M · ∑' i, ε (n + i)` for summable `ε`. The
proof takes `ε k = √(2 · KL_k)`; the statement leaves `ε` existential and chosen after `g`, and any
convergent sequence admits such an `ε`, so as stated its content is the convergence.

DERIVED: `0` is the excluded colour count and the sign of `M`. -/
theorem wilson_coarse_tendsto (hP : PinskerObs) {N : ℕ} (hN : N ≠ 0) {φ : ℕ → Cfg N → β}
    (hφ : ∀ k, Measurable (φ k)) (hW : WilsonZoomInput hN φ) {g : β → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : 0 < M) (hgM : ∀ y, |g y| ≤ M) (G : ℕ → C(Cfg N, ℝ))
    (hG : ∀ k x, G k x = g (φ k x)) :
    ∃ ε : ℕ → ℝ, Summable ε ∧ ∃ L : ℝ, Tendsto (fun k => stateK hN k (G k)) atTop (𝓝 L) ∧
      ∀ n, |stateK hN n (G n) - L| ≤ M * ∑' i, ε (n + i) := by
  obtain ⟨μ, hprob, hrep, hz⟩ := hW
  have hsf := (hz.sameForestKL hprob hφ).sameForestAt hP hprob hφ
  obtain ⟨h1, h2⟩ := hsf.tendsto_coarse hφ hg hM hgM
  have he : ∀ k, ∫ x, g (φ k x) ∂(μ k) = stateK hN k (G k) := fun k => by
    rw [← hrep k (G k)]
    exact integral_congr_ae (ae_of_all _ (fun x => (hG k x).symm))
  refine ⟨_, hsf.summable, _, h1.congr he, fun n => ?_⟩
  rw [← he n]
  exact h2 n

#print axioms wilson_coarse_tendsto

end Tree

/-! ## 7. The zoom as a continuous path -/

section Path

/-- **A function whose derivative is dominated by a speed moves at most the length.** If `E` has
derivative `e t` with `|e t| ≤ v t` at every `t`, and `Λ` has derivative `−v t`, then
`|E t − E s| ≤ Λ s − Λ t` for `s ≤ t`: `E + Λ` and `−E + Λ` have nonpositive derivatives and are
antitone.

DERIVED: `0` is the sign of the derivatives of `E + Λ` and `−E + Λ`. -/
theorem abs_sub_le_of_hasDerivAt {E e v Λ : ℝ → ℝ} (hE : ∀ t, HasDerivAt E (e t) t)
    (hev : ∀ t, |e t| ≤ v t) (hΛ : ∀ t, HasDerivAt Λ (-v t) t) {s t : ℝ} (hst : s ≤ t) :
    |E t - E s| ≤ Λ s - Λ t := by
  have h1 : Antitone (E + Λ) :=
    antitone_of_hasDerivAt_nonpos (fun r => (hE r).add (hΛ r)) (fun r => by
      have := (abs_le.mp (hev r)).2
      show e r + -v r ≤ 0
      linarith)
  have h2 : Antitone (-E + Λ) :=
    antitone_of_hasDerivAt_nonpos (fun r => (hE r).neg.add (hΛ r)) (fun r => by
      have := (abs_le.mp (hev r)).1
      show -e r + -v r ≤ 0
      linarith)
  have a1 : E t + Λ t ≤ E s + Λ s := h1 hst
  have a2 : -E t + Λ t ≤ -E s + Λ s := h2 hst
  rw [abs_le]
  constructor <;> linarith

#print axioms abs_sub_le_of_hasDerivAt

/-- **A speed bound along a path of laws.** For every measurable observable bounded by one, the
expectation `t ↦ ∫ f d(P t)` has a derivative at every `t`, of absolute value at most `v t`.

DERIVED: `1` is the unit bound of the observable. -/
def SpeedBound (P : ℝ → Measure β) (v : ℝ → ℝ) : Prop :=
  ∀ f : β → ℝ, Measurable f → (∀ y, |f y| ≤ 1) → ∀ t : ℝ,
    ∃ e : ℝ, HasDerivAt (fun s => ∫ y, f y ∂(P s)) e t ∧ |e| ≤ v t

/-- **The laws move at most the path length.** Under `SpeedBound P v` and `Λ' = −v`, the laws at
`s ≤ t` are `ObsClose` at `Λ s − Λ t`.

DERIVED: no numeral. -/
theorem SpeedBound.obsClose {P : ℝ → Measure β} {v Λ : ℝ → ℝ} (h : SpeedBound P v)
    (hΛ : ∀ t, HasDerivAt Λ (-v t) t) {s t : ℝ} (hst : s ≤ t) :
    ObsClose (P t) (P s) (Λ s - Λ t) := by
  intro f hf hb
  choose e he hev using h f hf hb
  exact abs_sub_le_of_hasDerivAt he hev hΛ hst

#print axioms SpeedBound.obsClose

/-- **Reparametrising the path** by a differentiable `b` multiplies the speed by `|b'|`.

DERIVED: no numeral. -/
theorem SpeedBound.comp {P : ℝ → Measure β} {v : ℝ → ℝ} (h : SpeedBound P v) {b b' : ℝ → ℝ}
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    SpeedBound (fun t => P (b t)) (fun t => v (b t) * |b' t|) := by
  intro f hf hfb t
  obtain ⟨e, he, hev⟩ := h f hf hfb (b t)
  refine ⟨e * b' t, he.comp t (hb t), ?_⟩
  show |e * b' t| ≤ v (b t) * |b' t|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hev (abs_nonneg _)

#print axioms SpeedBound.comp

/-- **The Fisher bound on a finite observer space.** For a positive probability vector `p`, a
tangent `p'` and an observable `|f| ≤ 1`, `|∑ f p'| ≤ √(∑ p'² / p)`: Cauchy–Schwarz on
`(f √p) · (p' / √p)`, with `∑ f² p ≤ ∑ p = 1`.

DERIVED: `0` is the lower end of `p`; `1` the total mass and the bound of `f`; `2` the square of
Cauchy–Schwarz. -/
theorem abs_sum_mul_le_sqrt_fisher {Y : Type} [Fintype Y] (p p' f : Y → ℝ) (hp : ∀ y, 0 < p y)
    (hsum : ∑ y, p y = 1) (hf : ∀ y, |f y| ≤ 1) :
    |∑ y, f y * p' y| ≤ Real.sqrt (∑ y, p' y ^ 2 / p y) := by
  apply Real.abs_le_sqrt
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => f y * Real.sqrt (p y))
    (fun y => p' y / Real.sqrt (p y))
  have e1 : ∀ y, f y * Real.sqrt (p y) * (p' y / Real.sqrt (p y)) = f y * p' y := fun y => by
    have hs : Real.sqrt (p y) ≠ 0 := (Real.sqrt_pos.mpr (hp y)).ne'
    have hinv : Real.sqrt (p y) * (Real.sqrt (p y))⁻¹ = 1 := mul_inv_cancel₀ hs
    calc f y * Real.sqrt (p y) * (p' y / Real.sqrt (p y))
        = f y * p' y * (Real.sqrt (p y) * (Real.sqrt (p y))⁻¹) := by ring
      _ = f y * p' y := by rw [hinv, mul_one]
  have e2 : ∀ y, (f y * Real.sqrt (p y)) ^ 2 ≤ p y := fun y => by
    have hf2 : f y ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (hf y)
    rw [mul_pow, Real.sq_sqrt (hp y).le]
    calc f y ^ 2 * p y ≤ 1 * p y := mul_le_mul_of_nonneg_right hf2 (hp y).le
      _ = p y := one_mul _
  have e3 : ∀ y, (p' y / Real.sqrt (p y)) ^ 2 = p' y ^ 2 / p y := fun y => by
    rw [div_pow, Real.sq_sqrt (hp y).le]
  have hI : 0 ≤ ∑ y, p' y ^ 2 / p y :=
    Finset.sum_nonneg (fun y _ => div_nonneg (sq_nonneg _) (hp y).le)
  simp only [e1, e3] at hcs
  calc (∑ y, f y * p' y) ^ 2
      ≤ (∑ y, (f y * Real.sqrt (p y)) ^ 2) * ∑ y, p' y ^ 2 / p y := hcs
    _ ≤ (∑ y, p y) * ∑ y, p' y ^ 2 / p y :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun y _ => e2 y)) hI
    _ = ∑ y, p' y ^ 2 / p y := by rw [hsum, one_mul]

#print axioms abs_sum_mul_le_sqrt_fisher

/-- **The Fisher–Rao length bounds the distance on a finite observer space.** For a differentiable
path `t ↦ p t` of positive probability vectors on a finite `Y` with tangent `p' t`, and `Λ` with
`Λ' = −√I`, `I t = ∑ p'² / p` the Fisher information: every `|f| ≤ 1` has
`|∑ f p t − ∑ f p s| ≤ Λ s − Λ t` for `s ≤ t`.

DERIVED: `0` is the lower end of `p`; `1` the total mass and the bound of `f`; `2` the square in the
Fisher information. -/
theorem finitePath_abs_sub_le {Y : Type} [Fintype Y] (p p' : ℝ → Y → ℝ) (hp : ∀ t y, 0 < p t y)
    (hsum : ∀ t, ∑ y, p t y = 1) (hd : ∀ t y, HasDerivAt (fun s => p s y) (p' t y) t)
    {Λ : ℝ → ℝ} (hΛ : ∀ t, HasDerivAt Λ (-Real.sqrt (∑ y, p' t y ^ 2 / p t y)) t)
    (f : Y → ℝ) (hf : ∀ y, |f y| ≤ 1) {s t : ℝ} (hst : s ≤ t) :
    |∑ y, f y * p t y - ∑ y, f y * p s y| ≤ Λ s - Λ t :=
  abs_sub_le_of_hasDerivAt (E := fun r => ∑ y, f y * p r y) (e := fun r => ∑ y, f y * p' r y)
    (v := fun r => Real.sqrt (∑ y, p' r y ^ 2 / p r y))
    (fun r => HasDerivAt.fun_sum (fun y _ => (hd r y).const_mul (f y)))
    (fun r => abs_sum_mul_le_sqrt_fisher (p r) (p' r) f (hp r) (hsum r) hf) hΛ hst

#print axioms finitePath_abs_sub_le

/-- **A finite zoom length.** The path of laws has a speed bound `v`, and a remaining length `Λ`
(`Λ' = −v`, so `Λ t = ∫_t^∞ v`) tending to `0`.

DERIVED: `0` is the limit of the remaining length. -/
structure FiniteZoomLength (P : ℝ → Measure β) (v : ℝ → ℝ) : Prop where
  /-- The speed bound. -/
  speed : SpeedBound P v
  /-- A remaining length, with derivative `−v`, tending to `0`. -/
  length : ∃ Λ : ℝ → ℝ, (∀ t, HasDerivAt Λ (-v t) t) ∧ Tendsto Λ atTop (𝓝 0)

/-- **The continuous same forest.** Under `FiniteZoomLength P v`, every measurable `f` with
`|f| ≤ M` has `∫ f d(P t)` converging along `atTop` to some `L`, with
`|∫ f d(P t) − L| ≤ M · Λ t` for some `Λ` tending to `0`. The proof takes `Λ` the remaining length of
`h`; the statement returns `Λ` existentially, and `Λ t = |∫ f d(P t) − L| / M` always serves, so as
stated its content is the convergence.

DERIVED: `0` is the sign of `M` and the limit of `Λ`. -/
theorem FiniteZoomLength.tendsto {P : ℝ → Measure β} {v : ℝ → ℝ} (h : FiniteZoomLength P v)
    {f : β → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 < M) (hfM : ∀ y, |f y| ≤ M) :
    ∃ Λ : ℝ → ℝ, Tendsto Λ atTop (𝓝 0) ∧ ∃ L : ℝ,
      Tendsto (fun t => ∫ y, f y ∂(P t)) atTop (𝓝 L) ∧
      ∀ t, |∫ y, f y ∂(P t) - L| ≤ M * Λ t := by
  obtain ⟨hS, Λ, hΛ, hΛ0⟩ := h
  have hclose : ∀ s t, s ≤ t →
      |∫ y, f y ∂(P t) - ∫ y, f y ∂(P s)| ≤ M * (Λ s - Λ t) :=
    fun s t hst => (hS.obsClose hΛ hst).abs_integral_sub_le hf hM hfM
  have hnn : ∀ t, 0 ≤ Λ t := fun t =>
    le_of_tendsto hΛ0 (Filter.eventually_atTop.2 ⟨t, fun u hu => by
      have := (hS.obsClose hΛ hu).nonneg
      show Λ u ≤ Λ t
      linarith⟩)
  have hc : CauchySeq (fun t => ∫ y, f y ∂(P t)) := by
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.1 ((tendsto_order.1 hΛ0).2 (δ / M) (div_pos hδ hM))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hclose N n hn
    have h2 : Λ N * M < δ := (lt_div_iff₀ hM).1 (hN N le_rfl)
    have h3 := mul_nonneg hM.le (hnn n)
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨Λ, hΛ0, L, hL, fun t => ?_⟩
  have hlim : Tendsto (fun u => |∫ y, f y ∂(P u) - ∫ y, f y ∂(P t)|) atTop
      (𝓝 |L - ∫ y, f y ∂(P t)|) := (hL.sub_const _).abs
  have hle : |L - ∫ y, f y ∂(P t)| ≤ M * Λ t :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨t, fun u hu => by
      have h1 := hclose t u hu
      have h3 := mul_nonneg hM.le (hnn u)
      show |∫ y, f y ∂(P u) - ∫ y, f y ∂(P t)| ≤ M * Λ t
      linarith⟩)
  rw [abs_sub_comm]
  exact hle

#print axioms FiniteZoomLength.tendsto

/-- **The observer Fisher information** of a family `b ↦ μ b` whose score is `−(S − ⟨S⟩_b)`: the
variance under `μ b` of the conditional expectation of `S` given the observer's σ-algebra `σ(φ)`.

DERIVED: no numeral. -/
def observerFisher (μ : ℝ → Measure α) (S : α → ℝ) (φ : α → β) (b : ℝ) : ℝ :=
  ProbabilityTheory.variance (condExp (MeasurableSpace.comap φ inferInstance) (μ b) S) (μ b)

/-- **The Gibbs family** `dμ_b = exp(−b S) / Z(b) dρ`.

DERIVED: no numeral beyond the sign of the exponent, which makes `b` the inverse temperature. -/
def gibbsFamily (ρ : Measure α) (S : α → ℝ) (b : ℝ) : Measure α :=
  ρ.withDensity (fun x => ENNReal.ofReal (Real.exp (-(b * S x)) / ∫ z, Real.exp (-(b * S z)) ∂ρ))

/-- **The observer speed of a Gibbs family (stated).** For a probability measure `ρ`, a bounded
measurable action `S` and a measurable observer map `φ`, the observer laws `(gibbsFamily ρ S b).map φ`
satisfy `SpeedBound` with speed `√(observerFisher)`: the derivative in `b` of `∫ g ∘ φ dμ_b` is
`−Cov_{μ_b}(g ∘ φ, S) = −Cov_{μ_b}(g ∘ φ, E[S | φ])`, and Cauchy–Schwarz with
`Var(g ∘ φ) ≤ 1` bounds it by `√(Var(E[S | φ]))`. A standard computation (differentiation under the
integral at bounded `S`, the tower property, Cauchy–Schwarz); `abs_sum_mul_le_sqrt_fisher` is its
finite-space core.

DERIVED: no numeral. -/
def GibbsObserverSpeed : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (ρ : Measure X) (S : X → ℝ)
    (φ : X → Y), IsProbabilityMeasure ρ → Measurable S → (∃ C : ℝ, ∀ x, |S x| ≤ C) →
      Measurable φ →
        SpeedBound (fun b => (gibbsFamily ρ S b).map φ)
          (fun b => Real.sqrt (observerFisher (gibbsFamily ρ S) S φ b))

/-- **THE OPEN QUANTITATIVE INPUT of the continuous zoom (stated): the coarse view becomes deaf to
the ultraviolet.** Along a coupling path `b(t)` with derivative `b'(t)` (for the lattice,
`t = log (a₀ / a)` and `b = β(a)`), the Fisher–Rao speed per unit log-spacing
`√(Var_{μ_{b(t)}}(E[S | φ])) · |b'(t)|` has a remaining length `Λ` tending to `0`:
`∫^∞ √(Var(E[S | φ])) · |db/dt| dt < ∞`.

DERIVED: `0` is the limit of the remaining length. -/
def DeafToUV (μ : ℝ → Measure α) (S : α → ℝ) (φ : α → β) (b b' : ℝ → ℝ) : Prop :=
  ∃ Λ : ℝ → ℝ, (∀ t, HasDerivAt Λ (-(Real.sqrt (observerFisher μ S φ (b t)) * |b' t|)) t) ∧
    Tendsto Λ atTop (𝓝 0)

/-- **Deafness gives a finite zoom length**, under `GibbsObserverSpeed`: for a Gibbs family with
bounded measurable action, a measurable observer map and a differentiable coupling path,
`DeafToUV` makes the observer laws along the path a `FiniteZoomLength` path, so every bounded
observer observable converges along it (`FiniteZoomLength.tendsto`).

DERIVED: no numeral. -/
theorem finiteZoomLength_of_deafToUV (hG : GibbsObserverSpeed) (ρ : Measure α)
    [IsProbabilityMeasure ρ] (S : α → ℝ) (hS : Measurable S) (hSb : ∃ C : ℝ, ∀ x, |S x| ≤ C)
    (φ : α → β) (hφ : Measurable φ) {b b' : ℝ → ℝ} (hb : ∀ t, HasDerivAt b (b' t) t)
    (hD : DeafToUV (gibbsFamily ρ S) S φ b b') :
    FiniteZoomLength (fun t => (gibbsFamily ρ S (b t)).map φ)
      (fun t => Real.sqrt (observerFisher (gibbsFamily ρ S) S φ (b t)) * |b' t|) :=
  ⟨(hG α β ρ S φ inferInstance hS hSb hφ).comp hb, hD⟩

#print axioms finiteZoomLength_of_deafToUV

end Path

end MassGap.ZoomForest
