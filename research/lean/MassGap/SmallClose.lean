import Mathlib
import MassGap.CompKernel
import MassGap.FloorFold

/-!
# MassGap.SmallClose — uniqueness in Bernstein–Widder, and the floor at positive physical gaps

Two statements the docstrings of `BernsteinWidder`, `CompKernel` and `FloorFold` leave open. Declarations are in
the namespace `MassGap.SmallClose`.

## 1. Uniqueness of the Laplace measure (proved)

* `measure_eq_of_moments`: two finite measures on `ℝ`, carried by `[0, 1]`, with equal moments are equal (the
  Weierstrass theorem, then `ext_of_forall_integral_eq_of_IsFiniteMeasure`).
* `laplaceRep_unique`: two finite measures on `[0, ∞)` with one Laplace transform on `(0, ∞)` are equal. The
  push-forward by `e^{−E}` to `[0, 1]` has moments `∫ e^{−nE}`; the moment of order `0` is the total mass, the limit
  of the transform along `τ = 1/(n+1)`. `E = −log(e^{−E})` undoes the push-forward.
* `laplaceRep_existsUnique`, `bernsteinWidder_existsUnique`: the measure of a `LaplaceRep`, so of a function under the
  hypotheses of `bernsteinWidder`, and of the time kernel of a regular margin monomial through
  `CompKernel.timeKernel_laplaceRep`.
* `expKernel_measure_eq_dirac`: at the exponential test the measure is `δ_E`.
* `measure_eq_rateMeasure`: the measure of a vector correlator of a positive contraction is its `rateMeasure`.

## 2. The floor at positive gaps (proved)

`covRead Φ P k m` is the covariance `PhysFloor` reads at step `k` and gap `m`.

* `tendsto_covRead`: at a dyadic physical time `t = n a_j` the read at gap `n 2^{k−j}`, physical separation `2t`,
  converges along `ultra` to `timeKernel (2t) − S(P)²`, `S(P)` the one-point reading. The gap is exact, not rounded.
* `physFloor_near`: a non-zero connected reading at gap `0` gives a floor at one positive dyadic gap, by
  `CompKernel.continuous_timeKernel` at `t = 0`.
* `physFloor_of_regConnected`: for the observer's flow, `RegConnectedNonzero` gives one regular monomial `Q` such
  that every bound `L` on the physical gap has a `c > 0` with `PhysFloor` at every gap sequence with
  `2 gap_k a_k ≤ L` eventually along `ultra`. Antitonicity (`gP_antitone`) carries a floor down to smaller gaps,
  so sequences that are not dyadic are covered; the doubling `g(m)² ≤ g(2m) g(0)` (`periodic_far_ge`), with the
  ceiling `FloorFold.contact_ceiling`, carries it up to every `L`.
* `physFloor_floor_gap`: the integer gaps `⌊w/(2 a_k)⌋` of a fixed physical separation `w`.
* `contact_eq_separated`: the connected reading of a monomial of margin `d` at gap `0` is the connected reading of
  the same monomial moved back by `t`, at physical separation `2t`, for every `t` with `0 < d − t`, `r < d − t`. This
  is the statement `RegNontrivial` and `FloorFold` give informally: a contact read of a margin monomial is a separated
  read, up to separation `2 (d − max r 0)`.

## What does not follow, plainly

* `c` depends on `L`: the doubling gives `c_{i+1} = c_i²/C`, and nothing here bounds the decay of `c` in `L`. This
  is not `ReadPos.ReflFloorAt`, which reads the bare tensor reading along `atTop`; every clause of "What does not
  follow" in `FloorFold` stands, except that a floor at positive physical gap now follows from
  `RegConnectedNonzero`.
* The floor is on the state `stateK`, along `ultra`, for the flow `energy0 W D hD` with `hpos`, `hcube` and
  `PosPreserving 0 r` as inputs. They are not discharged here.
* The time kernel has one measure per monomial. It is not identified with `klSec ρ`. Its tie to the rate
  measure of `gvecT P` is `KernelRate.kernel_measure_eq`.

DERIVED (module-wide): `0` the contact gap, the plane, the time axis, the signs and the moment of order `0`; `1` the
unit interval, the unit step and the shift of a bound; `2` the two steps of one reflected gap, the doubling, the
halving of a limit and the square. No number enters a clause.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.SmallClose

open Real Filter Topology MeasureTheory Set
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow
  MassGap.ObserverOS MassGap.ObserverEnergyBox
  MassGap.ApertureThing
open MassGap.ShellMeasure (ReflPos LaplaceRep rateMeasure rateMeasure_Iio re_inner_powT_eq_laplace)
open MassGap.ShellTranslate
open MassGap.BernsteinWidder (expKernel expKernel_dirac bernsteinWidder)
open MassGap.CompKernel (tVec timeKernel continuous_timeKernel timeKernel_laplaceRep)
open MassGap.RegularDense (RegConnectedNonzero)
open MassGap.FocusZoom (stateCov)
open MassGap.FloorFold (macroX macroX_mem PhysFloor HS contact_ceiling regConnected_of_physFloor gP_nonneg
  gP_antitone)
open MassGap.StepPeriodic (gP connP gP_conn connP_mem periodic_far_ge)

/-! ## 1. Uniqueness of the Laplace measure -/

section Moments

/-- A continuous function is integrable against a finite measure carried by `[0, 1]`. DERIVED: `0`, `1` the ends of
the interval. -/
theorem integrable_of_carried {μ : Measure ℝ} [IsFiniteMeasure μ] (h : μ (Icc (0 : ℝ) 1)ᶜ = 0) {g : ℝ → ℝ}
    (hg : Continuous g) : Integrable g μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact h
  filter_upwards [hae] with x hx using hC x hx

/-- Equal moments give equal integrals of every polynomial. DERIVED: `0`, `1` the ends of the interval. -/
theorem integral_poly_eq {μ μ' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : μ (Icc (0 : ℝ) 1)ᶜ = 0) (h' : μ' (Icc (0 : ℝ) 1)ᶜ = 0)
    (hm : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂μ') (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂μ' := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add (integrable_of_carried h p.continuous) (integrable_of_carried h q.continuous),
      integral_add (integrable_of_carried h' p.continuous) (integrable_of_carried h' q.continuous), hp, hq]
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    rw [integral_const_mul, integral_const_mul, hm]

/-- **Two finite measures carried by `[0, 1]` with equal moments are equal.** The Weierstrass theorem reads every
bounded continuous function as a uniform limit of polynomials on `[0, 1]`. DERIVED: `0`, `1` the ends of the
interval; `1` the shift of the denominator. -/
theorem measure_eq_of_moments {μ μ' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : μ (Icc (0 : ℝ) 1)ᶜ = 0) (h' : μ' (Icc (0 : ℝ) 1)ᶜ = 0)
    (hm : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂μ') : μ = μ' := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  set T : ℝ := μ.real univ + μ'.real univ with hT
  have hT0 : 0 ≤ T := add_nonneg measureReal_nonneg measureReal_nonneg
  have hkey : ∀ ε > 0, |∫ x, f x ∂μ - ∫ x, f x ∂μ'| ≤ ε * T := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn ε hε
    have hb : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], ν (Icc (0 : ℝ) 1)ᶜ = 0 →
        |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| ≤ ε * ν.real univ := by
      intro ν _ hν
      rw [← integral_sub (integrable_of_carried hν f.continuous) (integrable_of_carried hν p.continuous)]
      have hae : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1 := by
        rw [ae_iff]
        exact hν
      have hn : ∀ᵐ x ∂ν, ‖f x - p.eval x‖ ≤ ε := by
        filter_upwards [hae] with x hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hp x hx).le
      exact norm_integral_le_of_norm_le_const hn
    have h1 := hb μ h
    have h2 := hb μ' h'
    have e := integral_poly_eq h h' hm p
    rw [abs_le] at h1 h2 ⊢
    rw [hT, mul_add]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h0 : |∫ x, f x ∂μ - ∫ x, f x ∂μ'| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := hkey (ε / (T + 1)) (by positivity)
    have h2 : ε / (T + 1) * T ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

/-- **The total mass is the limit of the transform at `τ = 1/(n+1)`.** DERIVED: `1` the shift away from `0`; `0` the
sign of the rates. -/
theorem tendsto_mass (σ : Measure ℝ) [IsFiniteMeasure σ] (h0 : σ (Iio 0) = 0) :
    Tendsto (fun n : ℕ => ∫ E, Real.exp (-((1 / ((n : ℝ) + 1)) * E)) ∂σ) atTop (𝓝 (σ.real univ)) := by
  have hae : ∀ᵐ E ∂σ, 0 ≤ E := by
    rw [ae_iff]
    have : {E : ℝ | ¬ 0 ≤ E} = Iio 0 := by ext E; simp [not_le]
    rw [this]; exact h0
  have h := tendsto_integral_of_dominated_convergence (μ := σ)
    (F := fun (n : ℕ) (E : ℝ) => Real.exp (-((1 / ((n : ℝ) + 1)) * E))) (f := fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (by fun_prop : Continuous fun E : ℝ => Real.exp (-((1 / ((n : ℝ) + 1)) * E))).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => by
      filter_upwards [hae] with E hE
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ 1 / ((n : ℝ) + 1) * E := by positivity
      linarith)
    (Eventually.of_forall fun E => by
      have h1 : Tendsto (fun n : ℕ => -((1 / ((n : ℝ) + 1)) * E)) atTop (𝓝 (-(0 * E))) :=
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const E).neg
      have h2 := (Real.continuous_exp.tendsto _).comp h1
      simpa [Function.comp_def] using h2)
  simpa using h

/-- **Uniqueness in Bernstein–Widder**: two finite measures on `[0, ∞)` with equal Laplace transforms on `(0, ∞)` are
equal. DERIVED: `0` the sign of `τ`, the bottom of the rates and the moment of order `0`; `1` the unit interval. -/
theorem laplaceRep_unique {σ σ' : Measure ℝ} [IsFiniteMeasure σ] [IsFiniteMeasure σ'] (h0 : σ (Iio 0) = 0)
    (h0' : σ' (Iio 0) = 0)
    (h : ∀ τ : ℝ, 0 < τ → ∫ E, Real.exp (-(τ * E)) ∂σ = ∫ E, Real.exp (-(τ * E)) ∂σ') : σ = σ' := by
  have hmass : σ.real univ = σ'.real univ :=
    tendsto_nhds_unique (tendsto_mass σ h0)
      ((tendsto_mass σ' h0').congr fun n => (h _ (by positivity)).symm)
  have hφ : Measurable fun x : ℝ => Real.exp (-x) := (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).measurable
  have hψ : Measurable fun x : ℝ => -Real.log x := Real.measurable_log.neg
  have hS : ∀ ν : Measure ℝ, ν (Iio 0) = 0 → (ν.map fun x : ℝ => Real.exp (-x)) (Icc (0 : ℝ) 1)ᶜ = 0 := by
    intro ν hν
    rw [Measure.map_apply hφ measurableSet_Icc.compl]
    refine measure_mono_null ?_ hν
    intro E hE
    by_contra hne
    have hE0 : 0 ≤ E := not_lt.mp hne
    exact hE ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have hm : ∀ n : ℕ, ∫ x, x ^ n ∂(σ.map fun x : ℝ => Real.exp (-x))
      = ∫ x, x ^ n ∂(σ'.map fun x : ℝ => Real.exp (-x)) := by
    intro n
    rw [integral_map hφ.aemeasurable (by fun_prop : Continuous fun x : ℝ => x ^ n).aestronglyMeasurable,
      integral_map hφ.aemeasurable (by fun_prop : Continuous fun x : ℝ => x ^ n).aestronglyMeasurable]
    cases n with
    | zero => simpa using hmass
    | succ n =>
      have e : ∀ E : ℝ, Real.exp (-E) ^ (n + 1) = Real.exp (-(((n + 1 : ℕ) : ℝ) * E)) := fun E => by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      simp_rw [e]
      exact h _ (by positivity)
  have hmap := measure_eq_of_moments (hS σ h0) (hS σ' h0') hm
  have key : ∀ ν : Measure ℝ, ((ν.map fun x : ℝ => Real.exp (-x)).map fun x : ℝ => -Real.log x) = ν := by
    intro ν
    rw [Measure.map_map hψ hφ]
    have e : ((fun x : ℝ => -Real.log x) ∘ fun x : ℝ => Real.exp (-x)) = id := by
      funext x
      simp
    rw [e, Measure.map_id]
  rw [← key σ, hmap, key]

/-- **The measure of a `LaplaceRep` is unique.** DERIVED: `0` the sign of `τ` and the bottom of the rates. -/
theorem laplaceRep_existsUnique {C : ℝ → ℝ} (h : LaplaceRep C) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ σ (Iio 0) = 0 ∧
      ∀ τ, 0 < τ → C τ = ∫ E, Real.exp (-(τ * E)) ∂σ := by
  obtain ⟨σ, hf, h0, hr⟩ := h
  refine ⟨σ, ⟨hf, h0, hr⟩, ?_⟩
  rintro σ' ⟨hf', h0', hr'⟩
  exact laplaceRep_unique h0' h0 fun τ hτ => (hr' τ hτ).symm.trans (hr τ hτ)

/-- **Bernstein–Widder with uniqueness.** DERIVED: `0` the sign of `τ` and the bottom of the rates. -/
theorem bernsteinWidder_existsUnique {C : ℝ → ℝ} (hC : ReflPos C) (hcont : ContinuousOn C (Ioi 0))
    (hbd : ∃ M, ∀ t, 0 < t → |C t| ≤ M) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ σ (Iio 0) = 0 ∧
      ∀ τ, 0 < τ → C τ = ∫ E, Real.exp (-(τ * E)) ∂σ :=
  laplaceRep_existsUnique (bernsteinWidder hC hcont hbd)

/-- **At the exponential test the measure is `δ_E`.** DERIVED: `0` the sign of `E`, of `τ` and the bottom of the
rates. -/
theorem expKernel_measure_eq_dirac {E : ℝ} (hE : 0 ≤ E) {σ : Measure ℝ} [IsFiniteMeasure σ] (h0 : σ (Iio 0) = 0)
    (hr : ∀ τ, 0 < τ → expKernel E τ = ∫ x, Real.exp (-(τ * x)) ∂σ) : σ = Measure.dirac E := by
  obtain ⟨hd0, hd⟩ := expKernel_dirac hE
  exact laplaceRep_unique h0 hd0 fun τ hτ => (hr τ hτ).symm.trans (hd τ hτ)

/-- **The measure of a vector correlator is its rate measure.** DERIVED: `0`, `1` the ends of the spectrum interval;
`0` the sign of `τ`. -/
theorem measure_eq_rateMeasure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (u : E) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (h0 : σ (Iio 0) = 0)
    (hr : ∀ τ, 0 < τ → (inner ℂ u (MassGap.ContinuumTimeGroup.powT a τ u)).re = ∫ x, Real.exp (-(τ * x)) ∂σ) :
    σ = rateMeasure a u :=
  laplaceRep_unique h0 (rateMeasure_Iio a u) fun τ hτ =>
    (hr τ hτ).symm.trans (re_inner_powT_eq_laplace hsp u hτ)

end Moments

/-! ## 2. The floor at positive gaps -/

section Floor

variable {N : ℕ} [NeZero N]

/-- **The covariance `PhysFloor` reads at step `k` and gap `m`.** DERIVED: `2` the two steps of one gap; `0` the
plane. -/
def covRead (Φ : Flow N) (P : Mono N) (k m : ℕ) : ℝ :=
  stateCov (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0 (macroX Φ P k))
    (transObs ((2 * m) • eT) (macroX Φ P k))

/-- `PhysFloor` in terms of `covRead`. DERIVED: no numeral. -/
theorem physFloor_iff (Φ : Flow N) (P : Mono N) (gap : ℕ → ℕ) (c : ℝ) (l : Filter ℕ) :
    PhysFloor Φ P gap c l ↔ ∀ᶠ k in l, c ≤ |covRead Φ P k (gap k)| := Iff.rfl

/-- The read is a centred reflected read. DERIVED: `1` the least colour count. -/
theorem covRead_eq_gP (Φ : Flow N) (P : Mono N) (k m : ℕ) :
    covRead Φ P k m = gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
      (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ P k)) m :=
  (gP_conn _ _ _).symm

/-- **The read as Schwinger functions at step `k`.** DERIVED: `0` the plane; `2` the square. -/
theorem covRead_eq_latSF (Φ : Flow N) (P : Mono N) (r : ℝ) (k m : ℕ) :
    covRead Φ P k m = latSF (NeZero.ne N) Φ k (pairFam 0 P (Mono.shift (site (dySpacing N k) ((2 * m) • eT)) P))
      - latSF (NeZero.ne N) Φ k (pairFam 0 (emptyMargin N 0 r).1 P) ^ 2 := by
  set hN := NeZero.ne N
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  set X := prodSmear (dySpacing N k) (Φ.mono k P) with hX
  set ν := stateK hN k with hν
  have h0 := RegNontrivial.latSF_conn hN Φ 0 r k P
  have hc := RegNontrivial.connAt_eq_cov ν ha 0
    (MassGap.PeriodicState.periodicState_reflInvariant hN _ 0 0) (Φ.mono k P)
  have hT : ν (transObs ((2 * m) • eT) X) = ν X :=
    state_transObs (fun τ => MassGap.PeriodicState.periodicState_shift hN _ τ) _ X
  have h1 : latSF hN Φ k (pairFam 0 P P) = ν (LatticeReflection.ireflObs 0 0 X * X) := by
    rw [latSF_pairFam]
    exact latS_pairFam ν ha 0 _ _
  have h2 : latSF hN Φ k (pairFam 0 P (Mono.shift (site (dySpacing N k) ((2 * m) • eT)) P))
      = ν (LatticeReflection.ireflObs 0 0 X * transObs ((2 * m) • eT) X) := by
    rw [latSF_pairFam, hX, MassGap.ContinuumCluster.transObs_prodSmear ha]
    exact latS_pairFam ν ha 0 _ (Mono.shift (site (dySpacing N k) ((2 * m) • eT)) (Φ.mono k P))
  have h3 : covRead Φ P k m = ν (LatticeReflection.ireflObs 0 0 X * transObs ((2 * m) • eT) X)
      - ν (LatticeReflection.ireflObs 0 0 X) * ν X := by
    show ν _ - ν _ * ν (transObs ((2 * m) • eT) X) = _
    rw [hT]
    rfl
  unfold stateCov at hc
  rw [h3, h2]
  linarith [h0.trans hc, h1]

/-- The lattice vector of a gap as a physical time. DERIVED: `0` the time axis; `2` the two steps of one gap. -/
theorem site_gap (a : ℝ) (m : ℕ) : site a ((2 * m) • eT) = tVec 0 (a * (2 * m)) := by
  funext i
  by_cases h : i = 0
  · subst h
    simp [site, eT, tVec]
  · simp [site, eT, tVec, h]

/-- The dyadic spacings. DERIVED: `2` the halving per step. -/
theorem dySpacing_scale {j k : ℕ} (h : j ≤ k) : dySpacing N k * 2 ^ (k - j) = dySpacing N j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold dySpacing
  rw [Nat.add_sub_cancel_left, show j + d + 1 = (j + 1) + d by ring, pow_add]
  field_simp

/-- **At a dyadic physical time the read converges to the connected kernel.** The gap `n 2^{k−j}` has physical
separation exactly `2 n a_j`, from step `j` on. DERIVED: `2` the two steps of one gap and the square; `0` the plane. -/
theorem tendsto_covRead {Φ : Flow N} (hB : UniformBoundF (NeZero.ne N) Φ) (P : Mono N) (r : ℝ) (j n : ℕ) :
    Tendsto (fun k => covRead Φ P k (n * 2 ^ (k - j))) (ultra : Filter ℕ)
      (𝓝 (kernF (NeZero.ne N) Φ 0 P (Mono.shift (tVec 0 (dySpacing N j * (2 * n))) P)
        - kernF (NeZero.ne N) Φ 0 (emptyMargin N 0 r).1 P ^ 2)) := by
  have h := (tendsto_contSF (NeZero.ne N) Φ hB
      (pairFam 0 P (Mono.shift (tVec 0 (dySpacing N j * (2 * n))) P))).sub
    ((tendsto_contSF (NeZero.ne N) Φ hB (pairFam 0 (emptyMargin N 0 r).1 P)).pow 2)
  refine h.congr' ?_
  filter_upwards [(eventually_ge_atTop j).filter_mono ultra_le] with k hk
  have e : dySpacing N k * (2 * ((n * 2 ^ (k - j) : ℕ) : ℝ)) = dySpacing N j * (2 * n) := by
    rw [← dySpacing_scale (N := N) hk]
    push_cast
    ring
  rw [covRead_eq_latSF Φ P r k, site_gap, e]

/-- The read is non-negative in the half-space algebra. DERIVED: `0` the sign. -/
theorem covRead_nonneg {Φ : Flow N} {P : Mono N} {k : ℕ} (hm : macroX Φ P k ∈ HS N) (m : ℕ) :
    0 ≤ covRead Φ P k m := by
  rw [covRead_eq_gP]
  exact gP_nonneg _ (connP_mem _ hm) _

/-- The read does not increase in the gap. DERIVED: no numeral. -/
theorem covRead_anti {Φ : Flow N} {P : Mono N} {k : ℕ} (hm : macroX Φ P k ∈ HS N) {a b : ℕ} (h : a ≤ b) :
    covRead Φ P k b ≤ covRead Φ P k a := by
  rw [covRead_eq_gP, covRead_eq_gP]
  exact gP_antitone _ (connP_mem _ hm) h

/-- **The doubling**: `g(m)² ≤ g(2m) g(0)`, log-convexity at three points. DERIVED: `2` the doubling and the square;
`0` the contact gap. -/
theorem covRead_double {Φ : Flow N} {P : Mono N} {k : ℕ} (hm : macroX Φ P k ∈ HS N) {m : ℕ} (h0 : 0 < m) :
    covRead Φ P k m ^ 2 ≤ covRead Φ P k (2 * m) * covRead Φ P k 0 := by
  have hc := connP_mem (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) hm
  have h := periodic_far_ge (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) hc (show m ≤ 2 * m by omega)
  rw [show 2 * m - m = m by omega, ← mul_pow] at h
  simp only [covRead_eq_gP]
  refine le_of_pow_le_pow_left₀ h0.ne' (mul_nonneg (gP_nonneg _ hc _) (gP_nonneg _ hc _)) ?_
  rw [← pow_mul]
  exact h

variable (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound (NeZero.ne N) W O)

/-- `t = 0` is the zero translation. DERIVED: `0` the time. -/
theorem tVec_zero (τ : Fin 4) : tVec τ (0 : ℝ) = 0 := by
  funext i
  by_cases h : i = τ <;> simp [tVec, h]

include hpos hcube

/-- **A non-zero connected reading at gap `0` gives a floor at one positive dyadic gap**, by continuity of the time
kernel at `t = 0`. DERIVED: `0` the contact gap; `2` the two steps of one gap and the half of the limit; `1` the
single multiple of the step. -/
theorem physFloor_near {r : ℝ} (Q : RMono N D 0 r)
    (hQ : kernF (NeZero.ne N) (energy0 W D hD) 0 Q.1.1 Q.1.1
      - kernF (NeZero.ne N) (energy0 W D hD) 0 (emptyMargin N 0 r).1 Q.1.1 ^ 2 ≠ 0) :
    ∃ j : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in (ultra : Filter ℕ), c ≤ |covRead (energy0 W D hD) Q.1.1 k (1 * 2 ^ (k - j))| := by
  set hN := NeZero.ne N
  set M := kernF hN (energy0 W D hD) 0 (emptyMargin N 0 r).1 Q.1.1 with hM
  set G : ℝ → ℝ := fun t => timeKernel hN W hD 0 Q.1.1 t - M ^ 2 with hG
  have hGc : Continuous G := (continuous_timeKernel hN W hD hpos hcube 0 Q.2).sub continuous_const
  have hG0 : G 0 ≠ 0 := by
    have e2 : timeKernel hN W hD 0 Q.1.1 0 = kernF hN (energy0 W D hD) 0 Q.1.1 Q.1.1 := by
      unfold timeKernel
      rw [tVec_zero, Mono.shift_zero]
    rw [hG]
    simp only
    rw [e2]
    exact hQ
  have hlim : Tendsto (fun j => G (dySpacing N j * (2 * ((1 : ℕ) : ℝ)))) atTop (𝓝 (G 0)) := by
    have h := (tendsto_dySpacing N).mul_const (2 * ((1 : ℕ) : ℝ))
    rw [zero_mul] at h
    exact (hGc.tendsto 0).comp h
  obtain ⟨j, hj⟩ := (hlim.eventually_ne hG0).exists
  refine ⟨j, _, half_pos (abs_pos.mpr hj), ?_⟩
  have tend : Tendsto (fun k => covRead (energy0 W D hD) Q.1.1 k (1 * 2 ^ (k - j))) (ultra : Filter ℕ)
      (𝓝 (G (dySpacing N j * (2 * ((1 : ℕ) : ℝ))))) :=
    tendsto_covRead (uniformBoundF_energy0 hN W D hD hpos hcube) Q.1.1 r j 1
  filter_upwards [tend.abs.eventually (lt_mem_nhds (half_lt_self (abs_pos.mpr hj)))] with k hk using hk.le

/-- **`RegConnectedNonzero ⇒ PhysFloor` at positive gaps.** A non-zero connected reading at gap `0` gives one regular
monomial `Q` with, for every bound `L` on the physical gap, a floor `c > 0` at every gap sequence of physical
separation `2 gap_k a_k ≤ L` eventually along `ultra`. DERIVED: `0` the contact gap and the signs; `2` the two steps
of one gap, the doubling and the square; `1` the base of the doubling. -/
theorem physFloor_of_regConnected {r : ℝ} (hpp : (energy0 W D hD).PosPreserving 0 r)
    (hR : RegConnectedNonzero (NeZero.ne N) (energy0 W D hD) D 0 r) :
    ∃ Q : RMono N D 0 r, ∀ L : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ gap : ℕ → ℕ,
      (∀ᶠ k in (ultra : Filter ℕ), 2 * (gap k : ℝ) * dySpacing N k ≤ L) →
        PhysFloor (energy0 W D hD) Q.1.1 gap c (ultra : Filter ℕ) := by
  obtain ⟨Q, hQ⟩ := hR
  refine ⟨Q, ?_⟩
  set hN := NeZero.ne N
  have hB := uniformBoundF_energy0 hN W D hD hpos hcube
  obtain ⟨j, c0, hc0, hfl⟩ := physFloor_near W hD hpos hcube Q hQ
  obtain ⟨C, hC, hceil⟩ := contact_ceiling hB Q.1.1
  have hmem := (macroX_mem hpp Q.1).filter_mono ultra_le
  have hfar : ∀ᶠ k in (ultra : Filter ℕ), j ≤ k := (eventually_ge_atTop j).filter_mono ultra_le
  have hz : ∀ k, covRead (energy0 W D hD) Q.1.1 k 0 = stateCov (stateK hN k)
      (LatticeReflection.ireflObs 0 0 (macroX (energy0 W D hD) Q.1.1 k)) (macroX (energy0 W D hD) Q.1.1 k) := by
    intro k
    unfold covRead
    simp only [mul_zero, zero_smul, transObs_zero]
  have hdbl : ∀ i : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in (ultra : Filter ℕ),
      c ≤ covRead (energy0 W D hD) Q.1.1 k (2 ^ i * 2 ^ (k - j)) := by
    intro i
    induction i with
    | zero =>
      refine ⟨c0, hc0, ?_⟩
      filter_upwards [hfl, hmem] with k hk hm
      rw [pow_zero]
      rwa [abs_of_nonneg (covRead_nonneg hm _)] at hk
    | succ i ih =>
      obtain ⟨c, hc, h⟩ := ih
      refine ⟨c ^ 2 / C, by positivity, ?_⟩
      filter_upwards [h, hmem, hceil] with k hk hm hce
      have hm0 : 0 < 2 ^ i * 2 ^ (k - j) := by positivity
      have d := covRead_double hm hm0
      rw [show 2 ^ (i + 1) * 2 ^ (k - j) = 2 * (2 ^ i * 2 ^ (k - j)) by ring]
      rw [div_le_iff₀ hC]
      have h1 : c ^ 2 ≤ covRead (energy0 W D hD) Q.1.1 k (2 ^ i * 2 ^ (k - j)) ^ 2 :=
        pow_le_pow_left₀ hc.le hk 2
      have h2 : covRead (energy0 W D hD) Q.1.1 k 0 ≤ C := by
        rw [hz]
        exact (le_abs_self _).trans hce
      have h3 := mul_le_mul_of_nonneg_left h2 (covRead_nonneg hm (2 * (2 ^ i * 2 ^ (k - j))))
      linarith
  intro L
  have haj := dySpacing_pos (one_le_of_ne_zero hN) j
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (L / (2 * dySpacing N j)) (one_lt_two (α := ℝ))
  obtain ⟨c, hc, hf⟩ := hdbl i
  refine ⟨c, hc, fun gap hgap => ?_⟩
  rw [physFloor_iff]
  filter_upwards [hf, hmem, hgap, hfar] with k hk hm hg hjk
  have hak := dySpacing_pos (one_le_of_ne_zero hN) k
  have hs := dySpacing_scale (N := N) hjk
  have h1 : L < 2 ^ i * (2 * dySpacing N j) := (div_lt_iff₀ (by positivity)).mp hi
  have h2 : (gap k : ℝ) < 2 ^ i * 2 ^ (k - j) := by
    refine lt_of_mul_lt_mul_left ?_ (mul_pos two_pos hak).le
    calc 2 * dySpacing N k * (gap k : ℝ) = 2 * (gap k : ℝ) * dySpacing N k := by ring
      _ ≤ L := hg
      _ < 2 ^ i * (2 * dySpacing N j) := h1
      _ = 2 * dySpacing N k * (2 ^ i * 2 ^ (k - j)) := by rw [← hs]; ring
  have h3 : gap k ≤ 2 ^ i * 2 ^ (k - j) := by exact_mod_cast h2.le
  exact (hk.trans (covRead_anti hm h3)).trans (le_abs_self _)

/-- **A fixed physical separation `w`**: the integer gaps `⌊w/(2 a_k)⌋`. DERIVED: `2` the two steps of one gap; `0`
the sign of `w`. -/
theorem physFloor_floor_gap {r : ℝ} (hpp : (energy0 W D hD).PosPreserving 0 r)
    (hR : RegConnectedNonzero (NeZero.ne N) (energy0 W D hD) D 0 r) :
    ∃ Q : RMono N D 0 r, ∀ w : ℝ, 0 < w → ∃ c : ℝ, 0 < c ∧
      PhysFloor (energy0 W D hD) Q.1.1 (fun k => ⌊w / (2 * dySpacing N k)⌋₊) c (ultra : Filter ℕ) := by
  obtain ⟨Q, hQ⟩ := physFloor_of_regConnected W hD hpos hcube hpp hR
  refine ⟨Q, fun w hw => ?_⟩
  obtain ⟨c, hc, h⟩ := hQ w
  refine ⟨c, hc, h _ (Eventually.of_forall fun k => ?_)⟩
  have ha := dySpacing_pos (one_le_of_ne_zero (NeZero.ne N)) k
  have h1 := Nat.floor_le (a := w / (2 * dySpacing N k)) (by positivity)
  calc 2 * (⌊w / (2 * dySpacing N k)⌋₊ : ℝ) * dySpacing N k
      = (⌊w / (2 * dySpacing N k)⌋₊ : ℝ) * (2 * dySpacing N k) := by ring
    _ ≤ w / (2 * dySpacing N k) * (2 * dySpacing N k) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = w := div_mul_cancel₀ _ (by positivity)

/-- **The contact read of a margin monomial is a separated read.** If `Q` has margin `d` and `0 < d − t` with
`r < d − t`, then `Q'`, the monomial `Q` moved back by `t`, is a margin monomial, and the connected reading of `Q` at
gap `0` is the connected reading of `Q'` at physical separation `2t`. DERIVED: `0` the contact gap and the time axis;
`2` the separation and the square. -/
theorem contact_eq_separated {r : ℝ} (Q : RMono N D 0 r) {d t : ℝ} (hd : posAt 0 d Q.1.1) (ht : 0 < d - t)
    (hrt : r < d - t) :
    ∃ Q' : RMono N D 0 r, Q'.1.1 = Mono.shift (tVec 0 (-t)) Q.1.1 ∧
      kernF (NeZero.ne N) (energy0 W D hD) 0 Q.1.1 Q.1.1
          - kernF (NeZero.ne N) (energy0 W D hD) 0 (emptyMargin N 0 r).1 Q.1.1 ^ 2
        = timeKernel (NeZero.ne N) W hD 0 Q'.1.1 (2 * t)
          - kernF (NeZero.ne N) (energy0 W D hD) 0 (emptyMargin N 0 r).1 Q'.1.1 ^ 2 := by
  set hN := NeZero.ne N
  have hp : posAt 0 (d - t) (Mono.shift (tVec 0 (-t)) Q.1.1) := by
    intro i y hy
    have h1 := hd i (y - tVec 0 (-t)) hy
    have h2 : (y - tVec 0 (-t)) 0 = y 0 + t := by simp [tVec]
    rw [h2] at h1
    linarith
  have hreg : Reg D (Mono.shift (tVec 0 (-t)) Q.1.1) := reg_shift Q.2 _
  refine ⟨⟨⟨_, d - t, ht, hrt, hp⟩, hreg⟩, rfl, ?_⟩
  set P := Mono.shift (tVec 0 (-t)) Q.1.1 with hP
  have hback : Mono.shift (tVec 0 t) P = Q.1.1 := by
    rw [hP, Mono.shift_shift, CompKernel.tVec_add, neg_add_cancel, tVec_zero, Mono.shift_zero]
  have hE : Reg D (emptyMargin N 0 r).1 := fun i => i.elim0
  have hEs : ∀ v, Mono.shift v (emptyMargin N 0 r).1 = (emptyMargin N 0 r).1 := fun v =>
    congrArg (Sigma.mk 0) (funext fun i => i.elim0)
  have h1 := CompKernel.kernF_tshift hN W hD hpos hcube 0 hreg hreg t t
  have h2 := CompKernel.kernF_tshift hN W hD hpos hcube 0 hE hreg (-t) t
  rw [hback] at h1 h2
  rw [hEs, neg_add_cancel, tVec_zero, Mono.shift_zero] at h2
  show _ = kernF hN (energy0 W D hD) 0 P (Mono.shift (tVec 0 (2 * t)) P) - _
  rw [h1, h2, two_mul]

end Floor

end MassGap.SmallClose

end

#print axioms MassGap.SmallClose.measure_eq_of_moments
#print axioms MassGap.SmallClose.tendsto_mass
#print axioms MassGap.SmallClose.laplaceRep_unique
#print axioms MassGap.SmallClose.laplaceRep_existsUnique
#print axioms MassGap.SmallClose.bernsteinWidder_existsUnique
#print axioms MassGap.SmallClose.expKernel_measure_eq_dirac
#print axioms MassGap.SmallClose.measure_eq_rateMeasure
#print axioms MassGap.SmallClose.tendsto_covRead
#print axioms MassGap.SmallClose.covRead_double
#print axioms MassGap.SmallClose.physFloor_near
#print axioms MassGap.SmallClose.physFloor_of_regConnected
#print axioms MassGap.SmallClose.physFloor_floor_gap
#print axioms MassGap.SmallClose.contact_eq_separated
