import MassGap.WilsonRead
import MassGap.Certify

/-!
# MassGap.WilsonAnalytic — finite-volume analyticity in β, and the covariance identity, PROVED

The first rung of the RG / no-bulk-transition route to the crossover interior.

## What was missing

`Interior.lean` reduces the interior to a β-derivative bound and states the underlying identity in
prose — "the finite-volume statistical-mechanics fact `|d⟨d²⟩/dβ| = |Cov_β(⟨d²⟩,S)|` … an established
fact" — but never proves it, and
`Interior.interior_confinement_of_analytic_grid` carries `hdiff : DifferentiableAt ℝ d2 x` as a
HYPOTHESIS. On a genuine Wilson measure both are theorems, and this file proves them.

## What is proved here

For the real SU(2) Wilson system `WilsonReal.sysReal` (8 links, 2 ordered-loop plaquettes, real Wilson
action, Haar) and any bounded measurable observable `O`:

* `corrNum_hasDerivAt` / `partition_hasDerivAt` — the unnormalised correlator and the partition
  function are differentiable in `β`, with the expected derivatives, by differentiation under the
  integral sign. The domination is uniform because `sysReal`'s action is bounded in `[0,4]`
  (`sysReal_action_nonneg`, `sysReal_action_le`), so on any unit ball of couplings the integrand's
  β-derivative is bounded by a CONSTANT — and a constant is integrable against a probability measure.
* `expect_hasDerivAt` — **the covariance identity**
  `d⟨O⟩_β/dβ = −(⟨O·S⟩_β − ⟨O⟩_β⟨S⟩_β) = −Cov_β(O, S)`,
  by the quotient rule on `⟨O⟩ = corrNum / Z` with `Z > 0` (`sysReal_partition_pos`).
* `expect_differentiable` — hence `β ↦ ⟨O⟩_β` is differentiable on all of `ℝ`, which is the
  `hdiff` that `Interior` assumes.
* `wilsonCorrReal_differentiable` — the same for this development's own genuine Wilson correlation.

## Scope — what this does and does not settle

It settles the FINITE-VOLUME half exactly: at any fixed lattice, `Z(β) > 0` and every Gibbs
expectation is differentiable in `β` with the covariance derivative, so there is no non-analyticity
anywhere on the real axis. That is the precise content of "no phase transition at finite volume", and
it is now a theorem rather than a citation.

It does NOT settle the interior. A bulk transition is a non-analyticity of the free-energy DENSITY in
the thermodynamic limit, which appears only if the Lee–Yang zeros pinch the real axis as `V → ∞`. The
covariance identity is the right object for that question — `Cov_β(O, S)` is what must be shown to
stay `O(ξ⁴)` rather than `O(V)` — but nothing here bounds it uniformly in volume, and the naive
bounds do not: Popoviciu gives `O(V)`, Cauchy–Schwarz `O(√V)`. Closing that is the open step.

No constant is introduced. The `4` below is `sysReal_action_le`, itself two plaquettes times the proved
`wilsonDensity_le_two`; the unit radius of the ball is a choice of neighbourhood, not a threshold, and
nothing downstream depends on its value.

Footprint: the three foundational axioms.
-/

namespace MassGap.WilsonAnalytic

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonReal MassGap.WilsonAction
open MassGap.CompactGauge MeasureTheory

/-- The Boltzmann weight is differentiable in the coupling, with derivative `−S·e^{−βS}`. -/
theorem boltz_hasDerivAt (β : ℝ) (U : sysReal.Config) :
    HasDerivAt (fun x : ℝ => sysReal.boltz x U)
      (-(sysReal.action U) * sysReal.boltz β U) β := by
  have h : HasDerivAt (fun x : ℝ => -x * sysReal.action U) (-1 * sysReal.action U) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const (sysReal.action U))
  have he := h.exp
  unfold System.boltz
  convert he using 1
  ring

/-- On the unit ball around `β` the weight is bounded by `e^{4(|β|+1)}` — the domination the
differentiation-under-the-integral lemma needs. `4` is `sysReal_action_le`, not a chosen constant. -/
theorem boltz_le_on_ball {β x : ℝ} (hx : x ∈ Metric.ball β 1) (U : sysReal.Config) :
    sysReal.boltz x U ≤ Real.exp (4 * (|β| + 1)) := by
  have hxb : |x - β| < 1 := by rwa [Metric.mem_ball, Real.dist_eq] at hx
  have hxle : |x| ≤ |β| + 1 := by
    have := abs_sub_abs_le_abs_sub x β
    linarith [hxb]
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : -x * sysReal.action U ≤ |x| * sysReal.action U := by
    have := mul_le_mul_of_nonneg_right (neg_le_abs x) (sysReal_action_nonneg U)
    linarith
  have h2 : |x| * sysReal.action U ≤ |x| * 4 :=
    mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg x)
  have h3 : |x| * 4 ≤ (|β| + 1) * 4 := by linarith
  linarith

/-- **The unnormalised correlator is differentiable in `β`**, with
`d/dβ ∫ O·e^{−βS} = ∫ O·(−S)·e^{−βS}` — differentiation under the integral, dominated by a constant
because the action is bounded. -/
theorem corrNum_hasDerivAt (β : ℝ) (O : sysReal.Config → ℝ) (hmeas : Measurable O)
    (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    HasDerivAt (fun x : ℝ => sysReal.corrNum (probHaar G2) x O)
      (∫ U, O U * (-(sysReal.action U) * sysReal.boltz β U) ∂(sysReal.vol (probHaar G2))) β := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound (fun _ => (1 : G2)))
  set K : ℝ := M * (4 * Real.exp (4 * (|β| + 1))) with hK
  have hmeasF : ∀ x : ℝ, Measurable (fun U => O U * sysReal.boltz x U) :=
    fun x => hmeas.mul (measurable_sysReal_boltz x)
  have hint : ∀ x : ℝ, Integrable (fun U => O U * sysReal.boltz x U)
      (sysReal.vol (probHaar G2)) := fun x =>
    sysReal_mul_boltz_integrable x O hmeas M hbound
  have hmeasF' : ∀ x : ℝ,
      Measurable (fun U => O U * (-(sysReal.action U) * sysReal.boltz x U)) := by
    intro x
    have ha : Measurable (fun U : sysReal.Config => -(sysReal.action U)) :=
      measurable_sysReal_action.neg
    exact hmeas.mul (ha.mul (measurable_sysReal_boltz x))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sysReal.vol (probHaar G2))
    (F := fun (x : ℝ) (U : sysReal.Config) => O U * sysReal.boltz x U)
    (F' := fun (x : ℝ) (U : sysReal.Config) => O U * (-(sysReal.action U) * sysReal.boltz x U))
    (x₀ := β) (bound := fun _ => K) (s := Metric.ball β 1)
    (Metric.ball_mem_nhds β one_pos)
    (Filter.Eventually.of_forall (fun x => (hmeasF x).aestronglyMeasurable))
    (hint β)
    (hmeasF' β).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun U x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
      have h1 : |O U| ≤ M := hbound U
      have h2 : |sysReal.action U| ≤ 4 := by
        rw [abs_of_nonneg (sysReal_action_nonneg U)]; exact sysReal_action_le U
      have h3 : |sysReal.boltz x U| ≤ Real.exp (4 * (|β| + 1)) := by
        rw [abs_of_nonneg (sysReal_boltz_pos x U).le]; exact boltz_le_on_ball hx U
      have hnn : (0 : ℝ) ≤ |sysReal.action U| * |sysReal.boltz x U| := by positivity
      calc |O U| * (|sysReal.action U| * |sysReal.boltz x U|)
          ≤ M * (|sysReal.action U| * |sysReal.boltz x U|) :=
            mul_le_mul_of_nonneg_right h1 hnn
        _ ≤ M * (4 * Real.exp (4 * (|β| + 1))) := by
            refine mul_le_mul_of_nonneg_left ?_ hM
            exact mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)))
    (integrable_const K)
    (Filter.Eventually.of_forall (fun U x _ => by
      have hb := boltz_hasDerivAt x U
      simpa using hb.const_mul (O U)))
  exact hderiv.2

/-- **The partition function is differentiable in `β`**, with `dZ/dβ = ∫ (−S)·e^{−βS}`. -/
theorem partition_hasDerivAt (β : ℝ) :
    HasDerivAt (fun x : ℝ => sysReal.partition (probHaar G2) x)
      (∫ U, (1 : ℝ) * (-(sysReal.action U) * sysReal.boltz β U)
        ∂(sysReal.vol (probHaar G2))) β := by
  have h := corrNum_hasDerivAt β (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
  have hc : (fun x : ℝ => sysReal.corrNum (probHaar G2) x (fun _ => (1 : ℝ)))
      = fun x : ℝ => sysReal.partition (probHaar G2) x := by
    funext x; unfold System.corrNum System.partition; simp
  rwa [hc] at h

/-- The action is a bounded measurable observable (`S ∈ [0,4]`), so it may itself be averaged. -/
theorem action_bound (U : sysReal.Config) : |sysReal.action U| ≤ 4 := by
  rw [abs_of_nonneg (sysReal_action_nonneg U)]; exact sysReal_action_le U

/-- Pulling the minus sign out of the differentiated integrand: `∫ O·(−S)·e^{−βS} = −∫ (O·S)·e^{−βS}`,
i.e. the derivative of the unnormalised correlator is minus the correlator of `O·S`. -/
theorem integral_deriv_eq_neg_corrNum (β : ℝ) (O : sysReal.Config → ℝ) :
    (∫ U, O U * (-(sysReal.action U) * sysReal.boltz β U) ∂(sysReal.vol (probHaar G2)))
      = -(sysReal.corrNum (probHaar G2) β (fun U => O U * sysReal.action U)) := by
  unfold System.corrNum
  rw [show (fun U => O U * (-(sysReal.action U) * sysReal.boltz β U))
        = (fun U => -((O U * sysReal.action U) * sysReal.boltz β U)) from
      funext (fun U => by ring), integral_neg]

/-- **THE COVARIANCE IDENTITY — `d⟨O⟩_β/dβ = −Cov_β(O, S)`.**

The finite-volume statistical-mechanics fact `Interior.lean` states in prose and never proves. Here it
is a theorem on the genuine SU(2) Wilson Gibbs measure: the quotient rule applied to
`⟨O⟩ = corrNum/Z`, with `Z > 0` (`sysReal_partition_pos`) and both numerator and denominator
differentiated under the integral sign (`corrNum_hasDerivAt`, `partition_hasDerivAt`).

This is the object the whole interior question turns on. The `∀β` bound the grid route needs is a
bound on `|Cov_β(O, S)|`, and the naive estimates are `O(V)` (Popoviciu) or `O(√V)`
(Cauchy–Schwarz); showing it is instead `O(ξ⁴)` is clustering, which is the open step. What is settled
here is that the derivative EXISTS and IS that covariance, at every real `β`, with no
non-analyticity anywhere on the real axis at finite volume. -/
theorem expect_hasDerivAt (β : ℝ) (O : sysReal.Config → ℝ) (hmeas : Measurable O)
    (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    HasDerivAt (fun x : ℝ => sysReal.expect (probHaar G2) x O)
      (-(sysReal.expect (probHaar G2) β (fun U => O U * sysReal.action U)
          - sysReal.expect (probHaar G2) β O
            * sysReal.expect (probHaar G2) β sysReal.action)) β := by
  have hZ := sysReal_partition_pos β
  have hc := corrNum_hasDerivAt β O hmeas M hbound
  have hd := partition_hasDerivAt β
  rw [integral_deriv_eq_neg_corrNum β O] at hc
  rw [integral_deriv_eq_neg_corrNum β (fun _ => (1 : ℝ))] at hd
  have hd' : HasDerivAt (fun x : ℝ => sysReal.partition (probHaar G2) x)
      (-(sysReal.corrNum (probHaar G2) β sysReal.action)) β := by
    have hfun : (fun U => (1 : ℝ) * sysReal.action U) = sysReal.action := funext (fun U => one_mul _)
    rwa [hfun] at hd
  have h := hc.div hd' hZ.ne'
  simp only [Pi.div_def] at h
  have hval : -(sysReal.expect (probHaar G2) β (fun U => O U * sysReal.action U)
        - sysReal.expect (probHaar G2) β O * sysReal.expect (probHaar G2) β sysReal.action)
      = ((-(sysReal.corrNum (probHaar G2) β (fun U => O U * sysReal.action U)))
            * sysReal.partition (probHaar G2) β
          - sysReal.corrNum (probHaar G2) β O
            * -(sysReal.corrNum (probHaar G2) β sysReal.action))
        / sysReal.partition (probHaar G2) β ^ 2 := by
    unfold System.expect
    field_simp
    ring
  rw [hval]
  exact h

/-- **Every bounded Gibbs expectation is differentiable in the coupling, everywhere on `ℝ`.** This is
the `hdiff` hypothesis of `Interior.interior_confinement_of_analytic_grid`, discharged for a genuine
Wilson measure. -/
theorem expect_differentiable (O : sysReal.Config → ℝ) (hmeas : Measurable O)
    (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Differentiable ℝ (fun x : ℝ => sysReal.expect (probHaar G2) x O) :=
  fun β => (expect_hasDerivAt β O hmeas M hbound).differentiableAt

/-- **This development's own genuine Wilson correlation is differentiable in `β` at every lag.** -/
theorem wilsonCorrReal_differentiable (d : Fin 2) :
    Differentiable ℝ (fun β : ℝ => MassGap.WilsonRead.wilsonCorrReal β d) :=
  expect_differentiable _ ((measurable_plaqObs 0).mul (measurable_plaqObs d)) 4
    (fun U => by
      rw [abs_of_nonneg (mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg d U))]
      calc plaqObs 0 U * plaqObs d U
          ≤ 2 * 2 := mul_le_mul (plaqObs_le_two 0 U) (plaqObs_le_two d U)
              (plaqObs_nonneg d U) (by norm_num)
        _ = 4 := by norm_num)

/-! ### The obstruction, as a theorem: the only rigorous derivative bound is EXTENSIVE

`expect_hasDerivAt` says the interior's β-derivative IS a covariance. The grid route
(`MassGap.le_of_lipschitz_grid`) needs that covariance bounded by a constant that does NOT grow with
the volume, because the `∀β` statement it feeds must survive `L → ∞`. What is rigorously available
does grow with the volume, and the theorem below is that fact rather than an estimate about it.

`|Cov_β(O, S)| ≤ 4·M·#Plaq` for a bounded observable, on ANY `SU(N)` Wilson system: the action is a
sum over plaquettes (`wilsonSystem_action_le : S ≤ 2·#Plaq`), so every bound that goes through the
action's range is proportional to the plaquette count — which IS the volume. Sharper estimates move
the exponent, not the conclusion: Cauchy–Schwarz gives `√(Var O · Var S) = O(√V)` because
`Var S = V·χ`, and a Cauchy estimate on the complex disc gives `O(V)` again because the elementary
zero-free radius of `Z(β) = ∫e^{−βS}` is `O(1/V)`.

Making the interior's `∀β` work therefore requires showing the connected sum `Σ_p Cov(O, φ_p)` is
`O(ξ⁴)` rather than `O(V)` — i.e. clustering, which is the thing being proved. This file does not
close that, and states the barrier in the form a later argument has to beat. -/

/-- **The covariance bound available at finite volume is proportional to the plaquette count.**
For any `SU(N)` Wilson system and any observable bounded by `M`,
`|⟨O·S⟩_β − ⟨O⟩_β⟨S⟩_β| ≤ 4·M·#Plaq`. The `#Plaq` is not slack in the proof — the action is a sum of
that many plaquette densities, each in `[0,2]` (`wilsonSystem_action_le`), so its range is `2·#Plaq`
and any bound through that range inherits the factor.

THIS IS WHY THE GRID ROUTE DOES NOT CLOSE. `MassGap.le_of_lipschitz_grid` absorbs `L·δ`, so it needs
an `L` independent of the volume; the rigorous `L` here is linear in it. At the read aperture
`L = 16` on a `16³×32` lattice, `#Plaq = 6·16³·32 ≈ 7.9×10⁵`, against the `L ≲ 18` a realistic `δ`
could absorb. -/
theorem cov_bound_extensive {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonSystem bd (wilsonDensity (N := N))).action|
      ≤ 4 * M * (Fintype.card Pq : ℝ) := by
  have hVnn : (0 : ℝ) ≤ (Fintype.card Pq : ℝ) := by positivity
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound (fun _ => (1 : MassGap.SUN.SU N)))
  have hS : ∀ U, |(wilsonSystem bd (wilsonDensity (N := N))).action U|
      ≤ 2 * (Fintype.card Pq : ℝ) := fun U => by
    rw [abs_of_nonneg (wilsonSystem_action_nonneg hN bd U)]
    exact wilsonSystem_action_le hN bd U
  have h1 : |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
      (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)|
      ≤ M * (2 * (Fintype.card Pq : ℝ)) :=
    wilsonSystem_expect_abs_le hN bd β _ (hmeas.mul (measurable_wilsonSystem_action bd))
      (M * (2 * (Fintype.card Pq : ℝ))) (fun U => by
        rw [abs_mul]; exact mul_le_mul (hbound U) (hS U) (abs_nonneg _) hM)
  have h2 : |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O|
      ≤ M := wilsonSystem_expect_abs_le hN bd β O hmeas M hbound
  have h3 : |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
      (wilsonSystem bd (wilsonDensity (N := N))).action| ≤ 2 * (Fintype.card Pq : ℝ) :=
    wilsonSystem_expect_abs_le hN bd β _ (measurable_wilsonSystem_action bd)
      (2 * (Fintype.card Pq : ℝ)) hS
  have hprod : |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
      * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (wilsonSystem bd (wilsonDensity (N := N))).action|
      ≤ M * (2 * (Fintype.card Pq : ℝ)) := by
    rw [abs_mul]; exact mul_le_mul h2 h3 (abs_nonneg _) hM
  have habs := abs_sub ((wilsonSystem bd (wilsonDensity (N := N))).expect
      (probHaar (MassGap.SUN.SU N)) β
      (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U))
    ((wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
      * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (wilsonSystem bd (wilsonDensity (N := N))).action)
  linarith [habs, h1, hprod]

/-- **The Gibbs expectation is Lipschitz in β, with the covariance bound as its constant.**
Mean-value on `expect_hasDerivAt` (the derivative is `−Cov`) with `cov_bound_extensive` (the
covariance is bounded by `4·M·#Plaq`). For `sysReal` the plaquette count is `2`, so the constant is
`8·M`; the general form and its volume factor are `cov_bound_extensive`.

This is the `hlip` that `MassGap.le_of_lipschitz_grid` consumes and that
`Interior.d2_lipschitz_of_deriv_bound` derives from an ASSUMED derivative bound. Here both inputs are
theorems, so on a genuine Wilson measure the grid certificate's only remaining hypothesis is
`hcover` — the finite grid of measured values. That is the state of the interior route: every
analytic step proved, the measurement still measured, and the constant still extensive. -/
theorem expect_lipschitz (O : sysReal.Config → ℝ) (hmeas : Measurable O)
    (M : ℝ) (hbound : ∀ U, |O U| ≤ M) (x y : ℝ) :
    |sysReal.expect (probHaar G2) x O - sysReal.expect (probHaar G2) y O|
      ≤ (4 * M * 2) * |x - y| := by
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun t : ℝ => sysReal.expect (probHaar G2) t O) z :=
    fun z _ => (expect_hasDerivAt z O hmeas M hbound).differentiableAt
  have hbnd : ∀ z ∈ (Set.univ : Set ℝ),
      ‖deriv (fun t : ℝ => sysReal.expect (probHaar G2) t O) z‖ ≤ 4 * M * 2 := by
    intro z _
    rw [(expect_hasDerivAt z O hmeas M hbound).deriv, Real.norm_eq_abs, abs_neg]
    have hcb := cov_bound_extensive (N := 2) (by norm_num) bd2 z O hmeas M hbound
    have hc : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
    rw [hc] at hcb
    exact hcb
  have h := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_deriv_le hdiff hbnd
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

#print axioms expect_lipschitz

/-! ### The way past the extensivity wall: the bound is by the SUPPORT, not the volume

`cov_bound_extensive` bounds `|Cov(O,S)|` by `4·M·#Plaq`, and that factor is what stops the grid
route: `MassGap.le_of_lipschitz_grid` needs a Lipschitz constant independent of the volume.

But `S = Σ_p φ_p`, so `Cov(O, S) = Σ_p Cov(O, φ_p)` — and that sum is extensive only if every
plaquette contributes. The lemma below is the step that makes the difference explicit: whatever the
index set, the total is bounded by the size of the set on which the summands are NONZERO. Nothing is
assumed about how the vanishing arises, and no constant is introduced — `C` is whatever bound the
caller already has on a single term, and `supp` is wherever the terms are nonzero.

This is the precise sense in which CLUSTERING closes the interior: if `Cov(O, φ_p)` vanishes for `p`
outside a neighbourhood of `O`'s support, the Lipschitz constant is `4·M·|supp|` — a number fixed by
the observable's reach, not by the lattice. The `O(V)` in `cov_bound_extensive` is then not a
property of the system but of having assumed nothing.

That the hypothesis is attainable is not hypothetical here: `WilsonReal.expect_plaqObs_factor` proves
`⟨φ₀φ₁⟩_β = ⟨φ₀⟩_β⟨φ₁⟩_β` EXACTLY, at every `β`, for the two plaquettes of `sysReal`, which share no
link. Their connected correlator is identically zero — clustering in its extreme form, with no decay
rate and no constant — and `InteractingTwoPoint` shows the companion system whose plaquettes DO share
a link has a nonzero one. So on this system the connected correlator is supported exactly on
overlapping plaquettes, which is the hypothesis below with `supp` the overlapping set.

What remains open, and it is the whole of it: on a real lattice the plaquettes are coupled through
shared links at every separation, and showing the connected correlator decays there is the clustering
theorem itself. This file does not prove that. It proves that clustering is SUFFICIENT, so the
interior's open input is now one named statement rather than an unexplained gap. -/

/-- **A sum of terms is bounded by its SUPPORT, not by its index set.** If every term is bounded by
`C` and the terms vanish off `supp`, then `|∑ p, cov p| ≤ C · |supp|`.

Trivial as algebra, and it is exactly the step the interior turns on: applied to
`Cov(O, S) = ∑_p Cov(O, φ_p)` it replaces the plaquette count of `cov_bound_extensive` by the number
of plaquettes whose connected correlator with `O` does not vanish. No constant is introduced: `C` is
the caller's own per-term bound and `supp` is read off where the terms are nonzero. -/
theorem cov_sum_bound_of_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : ι → ℝ) (supp : Finset ι) (C : ℝ)
    (hloc : ∀ p, p ∉ supp → cov p = 0) (hb : ∀ p, |cov p| ≤ C) :
    |∑ p, cov p| ≤ C * (supp.card : ℝ) := by
  have hrestrict : ∑ p, cov p = ∑ p ∈ supp, cov p := by
    refine (Finset.sum_subset (Finset.subset_univ supp) ?_).symm
    intro p _ hp
    exact hloc p hp
  rw [hrestrict]
  calc |∑ p ∈ supp, cov p|
      ≤ ∑ p ∈ supp, |cov p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ supp, C := Finset.sum_le_sum (fun p _ => hb p)
    _ = C * (supp.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Expectation commutes with a finite sum of bounded observables.** The linearity step that lets
the covariance be split over plaquettes; `wilsonSystem_expect_add` iterated, with the partial sums'
integrability carried by the bound `|∑_{p ∈ s} f p| ≤ |s| · M`. -/
theorem expect_finset_sum {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (f : Pq → (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : ∀ p, Measurable (f p)) (M : ℝ) (hb : ∀ p U, |f p U| ≤ M) (s : Finset Pq) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => ∑ p ∈ s, f p U)
      = ∑ p ∈ s, (wilsonSystem bd (wilsonDensity (N := N))).expect
          (probHaar (MassGap.SUN.SU N)) β (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold System.expect System.corrNum
      simp
  | @insert q t hq ih =>
      have hpart : ∀ (u : Finset Pq) (U : _), |∑ p ∈ u, f p U| ≤ (u.card : ℝ) * M := by
        intro u U
        calc |∑ p ∈ u, f p U| ≤ ∑ p ∈ u, |f p U| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _p ∈ u, M := Finset.sum_le_sum (fun p _ => hb p U)
          _ = (u.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
      have hmq : Measurable (fun U => ∑ p ∈ t, f p U) :=
        Finset.measurable_sum t (fun p _ => hmeas p)
      have i1 := wilsonSystem_mul_boltz_integrable hN bd β (f q) (hmeas q) M (fun U => hb q U)
      have i2 := wilsonSystem_mul_boltz_integrable hN bd β (fun U => ∑ p ∈ t, f p U) hmq
        ((t.card : ℝ) * M) (fun U => hpart t U)
      rw [Finset.sum_insert hq]
      have hfun : (fun U => ∑ p ∈ insert q t, f p U)
          = fun U => f q U + ∑ p ∈ t, f p U := by
        funext U; rw [Finset.sum_insert hq]
      rw [hfun, wilsonSystem_expect_add bd β _ _ i1 i2, ih]

/-- **The action IS the plaquette sum** — `S = ∑_p φ_W(hol_p)`, by definition of `System.action` and
`wilsonPlaqObs`. Recorded so the covariance split below reads as what it is. -/
theorem action_eq_sum_plaqObs {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).action U = ∑ p, wilsonPlaqObs bd p U := rfl

/-- **`Cov(O, S)` SPLITS over the plaquettes: `Cov(O,S) = ∑_p Cov(O, φ_p)`.**

This is the identity that makes `cov_sum_bound_of_local` applicable to the real object. The action is
a plaquette sum, expectation is linear over it (`expect_finset_sum`), and the product `O·S` splits the
same way. No bound and no constant enters — it is an equality. -/
theorem cov_eq_sum_over_plaquettes {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonSystem bd (wilsonDensity (N := N))).action
      = ∑ p, ((wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (fun U => O U * wilsonPlaqObs bd p U)
            - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
              * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
                  (wilsonPlaqObs bd p)) := by
  classical
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound (fun _ => (1 : MassGap.SUN.SU N)))
  -- <O.S> = sum_p <O.phi_p>
  have h1 : (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
      = ∑ p, (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * wilsonPlaqObs bd p U) := by
    have hfun : (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        = fun U => ∑ p, O U * wilsonPlaqObs bd p U := by
      funext U; rw [action_eq_sum_plaqObs, Finset.mul_sum]
    rw [hfun]
    exact expect_finset_sum hN bd β (fun p U => O U * wilsonPlaqObs bd p U)
      (fun p => hmeas.mul (measurable_wilsonPlaqObs bd p)) (M * 2)
      (fun p U => by
        rw [abs_mul]
        exact mul_le_mul (hbound U)
          (by rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd p U)]
              exact wilsonPlaqObs_le_two hN bd p U) (abs_nonneg _) hM)
      Finset.univ
  -- <S> = sum_p <phi_p>
  have h2 : (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (wilsonSystem bd (wilsonDensity (N := N))).action
      = ∑ p, (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (wilsonPlaqObs bd p) := by
    have hfun : ((wilsonSystem bd (wilsonDensity (N := N))).action)
        = fun U => ∑ p, wilsonPlaqObs bd p U := funext (action_eq_sum_plaqObs bd)
    rw [hfun]
    exact expect_finset_sum hN bd β (fun p U => wilsonPlaqObs bd p U)
      (fun p => measurable_wilsonPlaqObs bd p) 2
      (fun p U => by
        rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd p U)]
        exact wilsonPlaqObs_le_two hN bd p U) Finset.univ
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- **THE CAPSTONE: with clustering, the covariance bound is set by the OBSERVABLE'S REACH, not by
the volume.**

Given that the connected correlator `Cov(O, φ_p)` vanishes for every plaquette outside a finite set
`supp` — which is what clustering says — the total covariance obeys

    |Cov(O, S)| ≤ 4 · M · |supp|

with **no dependence on the plaquette count**. Compare `cov_bound_extensive`, which is the same bound
with `|supp|` replaced by `#Plaq` because nothing was assumed.

WHY THIS IS THE INTERIOR. `expect_hasDerivAt` proves `d⟨O⟩_β/dβ = −Cov(O,S)`, so this is a Lipschitz
constant for `β ↦ ⟨O⟩_β`, and `MassGap.le_of_lipschitz_grid` turns a Lipschitz constant plus a finite
grid of measured values into a `∀β` statement. The grid route was blocked because the only available
constant grew with the volume, and the `∀β` it must support has to survive `L → ∞`. Under clustering
it does not grow, and the route closes.

So the interior's open input is exactly one statement — that the connected plaquette correlator
vanishes (or decays summably) outside a bounded neighbourhood on a real lattice. Everything from
there to `μ < κ₀` on every compact interval is proved.

No constant is introduced: `4` is `2 + 2` from `wilsonPlaqObs_le_two`, `M` is the caller's own bound
on `O`, and `supp` is read off wherever the connected correlator fails to vanish. -/
theorem cov_bound_local {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M)
    (supp : Finset Pq)
    (hclust : ∀ p, p ∉ supp →
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * wilsonPlaqObs bd p U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonPlaqObs bd p) = 0) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonSystem bd (wilsonDensity (N := N))).action|
      ≤ 4 * M * (supp.card : ℝ) := by
  classical
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound (fun _ => (1 : MassGap.SUN.SU N)))
  rw [cov_eq_sum_over_plaquettes hN bd β O hmeas M hbound]
  have hterm : ∀ p, |(wilsonSystem bd (wilsonDensity (N := N))).expect
          (probHaar (MassGap.SUN.SU N)) β (fun U => O U * wilsonPlaqObs bd p U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonPlaqObs bd p)| ≤ 4 * M := by
    intro p
    have hphi : ∀ U, |wilsonPlaqObs bd p U| ≤ 2 := fun U => by
      rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd p U)]; exact wilsonPlaqObs_le_two hN bd p U
    have h1 : |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O U * wilsonPlaqObs bd p U)| ≤ M * 2 :=
      wilsonSystem_expect_abs_le hN bd β _ (hmeas.mul (measurable_wilsonPlaqObs bd p)) (M * 2)
        (fun U => by rw [abs_mul]; exact mul_le_mul (hbound U) (hphi U) (abs_nonneg _) hM)
    have h2 : |(wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β O| ≤ M :=
      wilsonSystem_expect_abs_le hN bd β O hmeas M hbound
    have h3 : |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (wilsonPlaqObs bd p)| ≤ 2 :=
      wilsonSystem_expect_abs_le hN bd β _ (measurable_wilsonPlaqObs bd p) 2 hphi
    have hprod : |(wilsonSystem bd (wilsonDensity (N := N))).expect
          (probHaar (MassGap.SUN.SU N)) β O
        * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
            (wilsonPlaqObs bd p)| ≤ M * 2 := by
      rw [abs_mul]; exact mul_le_mul h2 h3 (abs_nonneg _) hM
    have := abs_sub ((wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β (fun U => O U * wilsonPlaqObs bd p U))
      ((wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
        * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
            (wilsonPlaqObs bd p))
    linarith [this, h1, hprod]
  exact cov_sum_bound_of_local _ supp (4 * M) hclust hterm

#print axioms cov_bound_local

#print axioms expect_finset_sum
#print axioms cov_eq_sum_over_plaquettes

#print axioms cov_sum_bound_of_local

#print axioms cov_bound_extensive

#print axioms integral_deriv_eq_neg_corrNum
#print axioms expect_hasDerivAt
#print axioms expect_differentiable
#print axioms wilsonCorrReal_differentiable
#print axioms boltz_hasDerivAt
#print axioms corrNum_hasDerivAt
#print axioms partition_hasDerivAt


/-! ## The volume-general analytic chain

Everything above that differentiates is stated on `sysReal`, the two-plaquette instance. That is
enough to prove the covariance identity exists, but NOT enough to say anything about volume: a
Lipschitz constant for a fixed two-plaquette system carries no information about `L → ∞`.

The following redo the differentiation for an ARBITRARY `SU(N)` Wilson system — any link set, any
plaquette set, any boundary map — so that the plaquette count appears explicitly and can be watched.
The action bound is `wilsonSystem_action_le`, `2·#Plaq`; it is derived from `wilsonDensity_le_two`
per plaquette and is not a chosen constant. -/

/-- The Boltzmann weight of an arbitrary Wilson system is differentiable in `β`. -/
theorem wilsonSystem_boltz_hasDerivAt {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    HasDerivAt (fun x : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).boltz x U)
      (-((wilsonSystem bd (wilsonDensity (N := N))).action U)
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U) β := by
  have h : HasDerivAt (fun x : ℝ => -x * (wilsonSystem bd (wilsonDensity (N := N))).action U)
      (-1 * (wilsonSystem bd (wilsonDensity (N := N))).action U) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const
      ((wilsonSystem bd (wilsonDensity (N := N))).action U))
  have he := h.exp
  unfold System.boltz
  convert he using 1
  ring

/-- Domination on the unit ball: `e^{-xS} ≤ e^{(|β|+1)·2·#Plaq}` for `|x - β| < 1`. The radius `1`
is a choice of neighbourhood, not a threshold — nothing downstream depends on its value. -/
theorem wilsonSystem_boltz_le_on_ball {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) {β x : ℝ} (hx : x ∈ Metric.ball β 1)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).boltz x U
      ≤ Real.exp ((|β| + 1) * (2 * (Fintype.card Pq : ℝ))) := by
  have hxb : |x - β| < 1 := by rwa [Metric.mem_ball, Real.dist_eq] at hx
  have hxle : |x| ≤ |β| + 1 := by
    have := abs_sub_abs_le_abs_sub x β
    linarith
  refine le_trans (wilsonSystem_boltz_le hN bd x U) ?_
  rw [Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_right hxle (by positivity)

/-- **Differentiation under the integral at arbitrary volume.** -/
theorem wilsonSystem_corrNum_hasDerivAt {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk]
    [Fintype Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    HasDerivAt (fun x : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).corrNum
        (probHaar (MassGap.SUN.SU N)) x O)
      (∫ U, O U * (-((wilsonSystem bd (wilsonDensity (N := N))).action U)
          * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))) β := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound (fun _ => (1 : MassGap.SUN.SU N)))
  have hA : (0 : ℝ) ≤ 2 * (Fintype.card Pq : ℝ) := by positivity
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))
    (F := fun (x : ℝ) U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz x U)
    (F' := fun (x : ℝ) U => O U * (-((wilsonSystem bd (wilsonDensity (N := N))).action U)
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz x U))
    (x₀ := β)
    (bound := fun _ => M * ((2 * (Fintype.card Pq : ℝ))
      * Real.exp ((|β| + 1) * (2 * (Fintype.card Pq : ℝ)))))
    (s := Metric.ball β 1)
    (Metric.ball_mem_nhds β one_pos)
    (Filter.Eventually.of_forall (fun x =>
      ((hmeas.mul (measurable_wilsonSystem_boltz bd x)).aestronglyMeasurable)))
    (wilsonSystem_mul_boltz_integrable hN bd β O hmeas M hbound)
    ((hmeas.mul ((measurable_wilsonSystem_action bd).neg.mul
      (measurable_wilsonSystem_boltz bd β))).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U x hx => ?_))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun U x _ => by
      simpa using (wilsonSystem_boltz_hasDerivAt bd x U).const_mul (O U)))).2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
  have h2 : |(wilsonSystem bd (wilsonDensity (N := N))).action U| ≤ 2 * (Fintype.card Pq : ℝ) := by
    rw [abs_of_nonneg (wilsonSystem_action_nonneg hN bd U)]; exact wilsonSystem_action_le hN bd U
  have h3 : |(wilsonSystem bd (wilsonDensity (N := N))).boltz x U|
      ≤ Real.exp ((|β| + 1) * (2 * (Fintype.card Pq : ℝ))) := by
    rw [abs_of_nonneg (wilsonSystem_boltz_pos bd x U).le]
    exact wilsonSystem_boltz_le_on_ball hN bd hx U
  have hnn : (0 : ℝ) ≤ |(wilsonSystem bd (wilsonDensity (N := N))).action U|
      * |(wilsonSystem bd (wilsonDensity (N := N))).boltz x U| := by positivity
  calc |O U| * (|(wilsonSystem bd (wilsonDensity (N := N))).action U|
          * |(wilsonSystem bd (wilsonDensity (N := N))).boltz x U|)
      ≤ M * (|(wilsonSystem bd (wilsonDensity (N := N))).action U|
          * |(wilsonSystem bd (wilsonDensity (N := N))).boltz x U|) :=
        mul_le_mul_of_nonneg_right (hbound U) hnn
    _ ≤ M * ((2 * (Fintype.card Pq : ℝ))
          * Real.exp ((|β| + 1) * (2 * (Fintype.card Pq : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (abs_nonneg _) hA) hM

/-- Minus sign out of the differentiated integrand, at arbitrary volume. -/
theorem wilsonSystem_integral_deriv {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) :
    (∫ U, O U * (-((wilsonSystem bd (wilsonDensity (N := N))).action U)
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
      = -((wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)) := by
  unfold System.corrNum
  rw [show (fun U => O U * (-((wilsonSystem bd (wilsonDensity (N := N))).action U)
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U))
      = (fun U => -((O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)) from
    funext (fun U => by ring), integral_neg]

/-- **THE COVARIANCE IDENTITY AT ARBITRARY VOLUME: `d⟨O⟩_β/dβ = −Cov_β(O, S)`.**

The same quotient-rule argument as `expect_hasDerivAt`, but on any `SU(N)` Wilson system rather than
the two-plaquette instance — so the statement survives `L → ∞` in form, and the only thing that can
grow with the volume is the covariance itself. Which is exactly the question `cov_bound_local`
answers. -/
theorem wilsonSystem_expect_hasDerivAt {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk]
    [Fintype Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    HasDerivAt (fun x : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) x O)
      (-((wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
            (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
          - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
            * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
                (wilsonSystem bd (wilsonDensity (N := N))).action)) β := by
  have hZ := wilsonSystem_partition_pos hN bd β
  have hc := wilsonSystem_corrNum_hasDerivAt hN bd β O hmeas M hbound
  have hd := wilsonSystem_corrNum_hasDerivAt hN bd β (fun _ => (1 : ℝ)) measurable_const 1
    (fun _ => by norm_num)
  rw [wilsonSystem_integral_deriv bd β O] at hc
  rw [wilsonSystem_integral_deriv bd β (fun _ => (1 : ℝ))] at hd
  have hcz : (fun x : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).corrNum
        (probHaar (MassGap.SUN.SU N)) x (fun _ => (1 : ℝ)))
      = fun x : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) x := by
    funext x; unfold System.corrNum System.partition; simp
  have hfun : (fun U => (1 : ℝ) * (wilsonSystem bd (wilsonDensity (N := N))).action U)
      = (wilsonSystem bd (wilsonDensity (N := N))).action := funext (fun U => one_mul _)
  rw [hcz, hfun] at hd
  have h := hc.div hd hZ.ne'
  simp only [Pi.div_def] at h
  have hval : -((wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonSystem bd (wilsonDensity (N := N))).action)
      = ((-((wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
              (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)))
            * (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (MassGap.SUN.SU N)) β
          - (wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β O
            * -((wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
                (wilsonSystem bd (wilsonDensity (N := N))).action))
        / (wilsonSystem bd (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β ^ 2 := by
    unfold System.expect
    field_simp
    ring
  rw [hval]
  exact h

/-- **THE PAYOFF: a Lipschitz constant for `β ↦ ⟨O⟩_β` that does not grow with the volume.**

Assume the connected correlator `Cov_β(O, φ_p)` vanishes for plaquettes outside a finite set `supp`,
at every coupling. Then

    |⟨O⟩_x − ⟨O⟩_y| ≤ 4·M·|supp| · |x − y|

on ANY `SU(N)` Wilson system — any link set, any plaquette set, any lattice size. The constant is
fixed by the observable's reach and its own bound, and the plaquette count has dropped out entirely.

WHAT THIS CLOSES. `MassGap.le_of_lipschitz_grid` converts a Lipschitz constant plus a finite grid of
measured values into a `∀β` statement on an interval. That route was blocked because the only
available constant was `cov_bound_extensive`'s `4·M·#Plaq`, which diverges in the thermodynamic
limit — so the `∀β` it supports says nothing about `L → ∞`. Under clustering it does not diverge, and
the interior closes: no bulk transition in the interval, uniformly in volume.

WHAT REMAINS OPEN, PRECISELY. One statement, and only one: that `hclust` holds — the connected
plaquette correlator vanishes (or, in the quantitative version, decays summably) outside a bounded
neighbourhood of the observable's support, uniformly in `β` on the interval and in the volume. That
is the physics input. Everything from there to the interior is proved here.

It is not vacuous: `WilsonReal.expect_plaqObs_factor` proves the connected correlator is identically
zero at every `β` for the disjoint plaquettes of `sysReal`, so `hclust` holds outright there, and
`InteractingTwoPoint` exhibits a shared-link pair whose connected correlator is nonzero — the
hypothesis is exactly the statement that the second kind is confined to a bounded set.

No constant is introduced: `4` is `2 + 2` from `wilsonPlaqObs_le_two`, `M` is the caller's own bound
on `O`, `supp` is read off wherever the connected correlator fails to vanish. -/
theorem expect_lipschitz_local {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M)
    (supp : Finset Pq)
    (hclust : ∀ z : ℝ, ∀ p, p ∉ supp →
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
          (fun U => O U * wilsonPlaqObs bd p U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
              (wilsonPlaqObs bd p) = 0)
    (x y : ℝ) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) x O
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) y O|
      ≤ (4 * M * (supp.card : ℝ)) * |x - y| := by
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun t : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) t O) z :=
    fun z _ => (wilsonSystem_expect_hasDerivAt hN bd z O hmeas M hbound).differentiableAt
  have hbnd : ∀ z ∈ (Set.univ : Set ℝ),
      ‖deriv (fun t : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) t O) z‖ ≤ 4 * M * (supp.card : ℝ) := by
    intro z _
    rw [(wilsonSystem_expect_hasDerivAt hN bd z O hmeas M hbound).deriv, Real.norm_eq_abs, abs_neg]
    exact cov_bound_local hN bd z O hmeas M hbound supp (hclust z)
  have h := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_deriv_le hdiff hbnd
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

#print axioms wilsonSystem_corrNum_hasDerivAt
#print axioms wilsonSystem_expect_hasDerivAt
#print axioms expect_lipschitz_local


/-! ## The interior, on a genuine Wilson measure, uniformly in the volume

`Interior.interior_confinement_of_analytic_grid` closes the interior for the abstract read `d2`, taking
its Lipschitz constant as a hypothesis. The two theorems below do the same thing for an observable of a
REAL `SU(N)` Wilson Gibbs measure, and supply the Lipschitz constant rather than assuming it. -/

/-- **Interior confinement on a genuine Wilson measure, from clustering plus a finite grid.**

`⟨O⟩_β ≤ B` for every `β` in `[a,b]`, given only: the observable's own bound `M`, the clustering support
`supp`, and a `δ`-grid of measured values clearing `B − 4·M·|supp|·δ`. Compare
`Interior.interior_confinement_of_analytic_grid`, which assumes the Lipschitz constant; here it is
derived — `expect_lipschitz_local`, itself from the proved covariance identity. -/
theorem wilson_le_of_clustering_grid {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ U, |O U| ≤ M)
    (supp : Finset Pq)
    (hclust : ∀ z : ℝ, ∀ p, p ∉ supp →
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
          (fun U => O U * wilsonPlaqObs bd p U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
              (wilsonPlaqObs bd p) = 0)
    {a b B δ : ℝ}
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) γ O
        ≤ B - (4 * M * (supp.card : ℝ)) * δ) :
    ∀ β ∈ Set.Icc a b,
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O ≤ B := by
  refine MassGap.le_of_lipschitz_grid (by positivity) ?_ hcover
  intro x _ y _
  exact expect_lipschitz_local hN bd O hmeas M hbound supp hclust x y

/-- **THE UNIFORM-IN-VOLUME INTERIOR.**

A family of `SU(N)` Wilson systems indexed by volume — each with its own link set, plaquette set and
boundary map, so the lattice genuinely grows — together with

  * one bound `M` on the observable at every volume,
  * clustering at every volume, with supports of a common size bound `R`,
  * one `δ`-grid of measured values clearing `B − 4·M·R·δ` at every volume,

gives `⟨O⟩_β ≤ B` on `[a,b]` **at every volume, with the same constants**. The plaquette count does not
appear in the hypotheses or the conclusion.

This is the statement the crossover interior needs and the one `cov_bound_extensive` cannot supply: its
constant `4·M·#Plaq` diverges, so the `∀β` it yields degrades to vacuity as `L → ∞`. Here nothing
degrades. `R` is the reach of the observable's connected correlator, not a property of the lattice.

The three inputs are of different kinds and it is worth being exact about which is which. `M` is proved
per observable (`wilsonPlaqObs_le_two` and friends). The grid is measured — finitely many deterministic
reads, exactly as `Interior` intends. `R` — that clustering holds with a volume-independent reach — is
the physics input, and it is the only one. -/
theorem wilson_le_uniform_in_volume {N : ℕ} (hN : N ≠ 0)
    {Lk Pq : ℕ → Type} [∀ V, Fintype (Lk V)] [∀ V, Fintype (Pq V)] [∀ V, DecidableEq (Pq V)]
    (bd : ∀ V, Pq V → List (Lk V × Bool))
    (O : ∀ V, (wilsonSystem (bd V) (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : ∀ V, Measurable (O V)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ V U, |O V U| ≤ M)
    (supp : ∀ V, Finset (Pq V)) (R : ℝ) (hR : ∀ V, ((supp V).card : ℝ) ≤ R)
    (hclust : ∀ V, ∀ z : ℝ, ∀ p, p ∉ supp V →
      (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
          (fun U => O V U * wilsonPlaqObs (bd V) p U)
        - (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z (O V)
          * (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
              (wilsonPlaqObs (bd V) p) = 0)
    {a b B δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ V, ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧
      (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) γ (O V)
        ≤ B - (4 * M * R) * δ) :
    ∀ V, ∀ β ∈ Set.Icc a b,
      (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β (O V)
        ≤ B := by
  intro V
  have hRnn : (0 : ℝ) ≤ R := le_trans (Nat.cast_nonneg _) (hR V)
  refine MassGap.le_of_lipschitz_grid (L := 4 * M * R) (by positivity) ?_ (hcover V)
  intro x _ y _
  refine le_trans (expect_lipschitz_local hN (bd V) (O V) (hmeas V) M (hbound V) (supp V)
    (hclust V) x y) ?_
  have : 4 * M * ((supp V).card : ℝ) ≤ 4 * M * R :=
    mul_le_mul_of_nonneg_left (hR V) (by positivity)
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

#print axioms wilson_le_of_clustering_grid
#print axioms wilson_le_uniform_in_volume


/-! ## The summable form — what a measurement can actually support

`cov_bound_local` asks the connected correlator to VANISH outside a finite set. No measurement can
establish that: a correlator below its own uncertainty is not a correlator known to be zero. The
physically correct hypothesis, and the one a lattice read can support, is that the connected
correlator is DOMINATED by a summable profile whose total does not grow with the volume.

The theorems below are that version. They subsume the vanishing form (take the dominating profile to
be `4M` on `supp` and `0` off it, with total `4M·|supp|`), and they are what the empirical reach
measurement should be compared against. -/

/-- A finite sum is bounded by the total of any dominating profile. -/
theorem cov_sum_bound_of_summable {ι : Type*} [Fintype ι]
    (cov : ι → ℝ) (c : ι → ℝ) (K : ℝ)
    (hdom : ∀ p, |cov p| ≤ c p) (hsum : ∑ p, c p ≤ K) :
    |∑ p, cov p| ≤ K :=
  le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun p _ => hdom p))) hsum

/-- **`|Cov(O, S)| ≤ K` from a summable connected-correlator profile.**

`K` is whatever the profile totals. If the profile decays fast enough that its total is bounded
independently of the volume — which is what "the theory clusters" means quantitatively — then so is
this bound, and the plaquette count never enters. -/
theorem cov_bound_summable {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M)
    (c : Pq → ℝ) (K : ℝ)
    (hdom : ∀ p,
      |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * wilsonPlaqObs bd p U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonPlaqObs bd p)| ≤ c p)
    (hsum : ∑ p, c p ≤ K) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).action U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonSystem bd (wilsonDensity (N := N))).action| ≤ K := by
  rw [cov_eq_sum_over_plaquettes hN bd β O hmeas M hbound]
  exact cov_sum_bound_of_summable _ c K hdom hsum

/-- **The Lipschitz constant is the clustering total `K`.** -/
theorem expect_lipschitz_summable {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M)
    (c : ℝ → Pq → ℝ) (K : ℝ)
    (hdom : ∀ z : ℝ, ∀ p,
      |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
          (fun U => O U * wilsonPlaqObs bd p U)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z O
          * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
              (wilsonPlaqObs bd p)| ≤ c z p)
    (hsum : ∀ z : ℝ, ∑ p, c z p ≤ K) (x y : ℝ) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) x O
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) y O|
      ≤ K * |x - y| := by
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ),
      DifferentiableAt ℝ (fun t : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) t O) z :=
    fun z _ => (wilsonSystem_expect_hasDerivAt hN bd z O hmeas M hbound).differentiableAt
  have hbnd : ∀ z ∈ (Set.univ : Set ℝ),
      ‖deriv (fun t : ℝ => (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) t O) z‖ ≤ K := by
    intro z _
    rw [(wilsonSystem_expect_hasDerivAt hN bd z O hmeas M hbound).deriv, Real.norm_eq_abs, abs_neg]
    exact cov_bound_summable hN bd z O hmeas M hbound (c z) K (hdom z) (hsum z)
  have h := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_deriv_le hdiff hbnd
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- **THE UNIFORM-IN-VOLUME INTERIOR, IN THE FORM A LATTICE READ CAN SUPPORT.**

One clustering total `K` at every volume, one `δ`-grid of measured values clearing `B − K·δ`, and the
conclusion `⟨O⟩_β ≤ B` holds on `[a,b]` at every volume. The hypothesis is no longer that a correlator
is exactly zero somewhere — it is that the connected profile SUMS to something volume-independent.

That is a quantity a lattice measurement produces directly. For a single plaquette observable it has
a closed form: translation invariance gives `Cov(phi_0, S) = Var(S)/N_p = N_p·Var(phibar)`, which is
the **plaquette susceptibility**. So this hypothesis is exactly the statement that the susceptibility
is INTENSIVE — the textbook signature of no bulk transition, here turned into the interior.

-/
theorem wilson_le_uniform_of_clustering_total {N : ℕ} (hN : N ≠ 0)
    {Lk Pq : ℕ → Type} [∀ V, Fintype (Lk V)] [∀ V, Fintype (Pq V)] [∀ V, DecidableEq (Pq V)]
    (bd : ∀ V, Pq V → List (Lk V × Bool))
    (O : ∀ V, (wilsonSystem (bd V) (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : ∀ V, Measurable (O V)) (M : ℝ) (hbound : ∀ V U, |O V U| ≤ M)
    (c : ∀ V, ℝ → Pq V → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hdom : ∀ V, ∀ z : ℝ, ∀ p,
      |(wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
          (fun U => O V U * wilsonPlaqObs (bd V) p U)
        - (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z (O V)
          * (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) z
              (wilsonPlaqObs (bd V) p)| ≤ c V z p)
    (hsum : ∀ V, ∀ z : ℝ, ∑ p, c V z p ≤ K)
    {a b B δ : ℝ}
    (hcover : ∀ V, ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧
      (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) γ (O V)
        ≤ B - K * δ) :
    ∀ V, ∀ β ∈ Set.Icc a b,
      (wilsonSystem (bd V) (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β (O V)
        ≤ B := by
  intro V
  refine MassGap.le_of_lipschitz_grid (L := K) hK ?_ (hcover V)
  intro x _ y _
  exact expect_lipschitz_summable hN (bd V) (O V) (hmeas V) M (hbound V) (c V) K (hdom V)
    (hsum V) x y

#print axioms cov_bound_summable
#print axioms expect_lipschitz_summable
#print axioms wilson_le_uniform_of_clustering_total

end MassGap.WilsonAnalytic
