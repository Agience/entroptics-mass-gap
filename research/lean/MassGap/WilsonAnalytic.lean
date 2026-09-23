import MassGap.WilsonRead
import MassGap.Certify

/-!
# MassGap.WilsonAnalytic — differentiability in `β`, and the covariance identity

For Wilson systems built by `wilsonSystem` over `SU(N)` with Haar link measure, this file proves that
Gibbs expectations are differentiable in the coupling, identifies the derivative as a covariance, and
turns that into Lipschitz bounds and interval statements.

## The chain on `WilsonReal.sysReal`

`sysReal` is the real `SU(2)` system on `Fin 8` links with two ordered-loop plaquettes; its action
takes values in `[0, 4]` (`sysReal_action_nonneg`, `sysReal_action_le`).

* `boltz_hasDerivAt`, `boltz_le_on_ball` — the Boltzmann weight's `β`-derivative and its domination
  on a unit ball of couplings.
* `corrNum_hasDerivAt`, `partition_hasDerivAt` — differentiation under the integral sign. The
  dominating function is a constant, integrable because the link measure is a probability measure.
* `expect_hasDerivAt` — `d⟨O⟩_β/dβ = -(⟨O·S⟩_β - ⟨O⟩_β⟨S⟩_β)`, by the quotient rule on
  `⟨O⟩ = corrNum / partition`, with `partition > 0` from `sysReal_partition_pos`.
* `expect_differentiable`, `wilsonCorrReal_differentiable`, `expect_lipschitz`.

## The same chain at arbitrary volume

`wilsonSystem_boltz_hasDerivAt` through `wilsonSystem_expect_hasDerivAt` repeat the argument for an
arbitrary `SU(N)` Wilson system — any link type, any plaquette type, any boundary map — so the
plaquette count `Fintype.card Pq` appears explicitly in every bound. The action bound there is
`wilsonSystem_action_le`, namely `2 * Fintype.card Pq`.

## How the plaquette count enters the covariance, and how it leaves

* `cov_bound_extensive` bounds `|⟨O·S⟩_β - ⟨O⟩_β⟨S⟩_β|` by `4 * M * Fintype.card Pq`, with no
  hypothesis beyond `M` bounding `O`; the factor is the plaquette count because the action's range is
  `2 * Fintype.card Pq`.
* `cov_eq_sum_over_plaquettes` splits that covariance into `∑_p Cov(O, φ_p)`, as an equality.
* `cov_sum_bound_of_local` and `cov_bound_local` replace the plaquette count by `supp.card`, the size
  of a set off which the summands are assumed to vanish; `cov_sum_bound_of_summable` and
  `cov_bound_summable` replace it by the total `K` of an assumed dominating profile.
* `expect_lipschitz_local`, `expect_lipschitz_summable`, `wilson_le_of_clustering_grid`,
  `wilson_le_uniform_in_volume` and `wilson_le_uniform_of_clustering_total` carry those constants
  through the mean-value theorem and `MassGap.le_of_lipschitz_grid`.

The vanishing (`hclust`) or domination (`hdom`) of the connected plaquette correlator is a
hypothesis of every theorem in that last group, and is proved nowhere in this file. Every statement
here is at a fixed finite lattice; no thermodynamic limit is taken anywhere.

The `4` in the covariance bounds is `2 + 2` from `wilsonPlaqObs_le_two`, and the radius `1` in the
domination lemmas names the neighbourhood `hasDerivAt_integral_of_dominated_loc_of_deriv_le` works on.

Footprint: the three foundational axioms.
-/

namespace MassGap.WilsonAnalytic

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonReal MassGap.WilsonAction
open MassGap.CompactGauge MeasureTheory

/-- The Boltzmann weight of `sysReal` at a fixed configuration `U` has derivative `-S(U)·e^{-βS(U)}`
in the coupling, at every real `β`. The chain rule on `x ↦ exp (-x · S U)`.
DERIVED: no numeral. -/
theorem boltz_hasDerivAt (β : ℝ) (U : sysReal.Config) :
    HasDerivAt (fun x : ℝ => sysReal.boltz x U)
      (-(sysReal.action U) * sysReal.boltz β U) β := by
  have h : HasDerivAt (fun x : ℝ => -x * sysReal.action U) (-1 * sysReal.action U) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const (sysReal.action U))
  have he := h.exp
  unfold System.boltz
  convert he using 1
  ring

/-- For `x` in the ball of radius `1` around `β`, the Boltzmann weight of `sysReal` is at most
`exp (4 · (|β| + 1))`, uniformly in the configuration. This is the domination hypothesis of
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, and it is uniform in `U` because `sysReal`'s
action is bounded.
DERIVED: the `1` is the ball radius, so `|x| ≤ |β| + 1` by the triangle inequality; the `4` is `sysReal_action_le`, the action's upper bound. -/
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

/-- The unnormalised correlator of `sysReal` has derivative `∫ O·(-S)·e^{-βS}` in the coupling:
differentiation under the integral sign, at every real `β`.

`O` must be measurable and bounded — the hypotheses supply a real `M` with `|O U| ≤ M` for every
configuration. Together with `boltz_le_on_ball` and the action bound that makes the dominating
function a constant, which is integrable because `sysReal.vol (probHaar G2)` is a probability
measure on `Fin 8` links.
DERIVED: no numeral. -/
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

/-- The partition function of `sysReal` has derivative `∫ 1·(-S)·e^{-βS}` in the coupling, at every
real `β`. It is `corrNum_hasDerivAt` at the constant observable `1`, which is measurable and bounded
by `1`, after rewriting `corrNum ... (fun _ => 1)` as `partition`.
DERIVED: the `1` in the derivative is the constant observable that turns `corrNum` into `partition`. -/
theorem partition_hasDerivAt (β : ℝ) :
    HasDerivAt (fun x : ℝ => sysReal.partition (probHaar G2) x)
      (∫ U, (1 : ℝ) * (-(sysReal.action U) * sysReal.boltz β U)
        ∂(sysReal.vol (probHaar G2))) β := by
  have h := corrNum_hasDerivAt β (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
  have hc : (fun x : ℝ => sysReal.corrNum (probHaar G2) x (fun _ => (1 : ℝ)))
      = fun x : ℝ => sysReal.partition (probHaar G2) x := by
    funext x; unfold System.corrNum System.partition; simp
  rwa [hc] at h

/-- `sysReal`'s action is bounded in absolute value by `4` at every configuration. The proof drops
the absolute value using `sysReal_action_nonneg` and then applies `sysReal_action_le`. The statement
is the bound alone; measurability of the action is a separate fact
(`measurable_sysReal_action`), not part of this conclusion.
DERIVED: the `4` is `sysReal_action_le` — two plaquettes at `wilsonDensity_le_two` each. -/
theorem action_bound (U : sysReal.Config) : |sysReal.action U| ≤ 4 := by
  rw [abs_of_nonneg (sysReal_action_nonneg U)]; exact sysReal_action_le U

/-- Pulls the minus sign out of the differentiated integrand:
`∫ O·(-S)·e^{-βS} = -(corrNum β (O·S))`, so the derivative produced by `corrNum_hasDerivAt` is minus
the unnormalised correlator of `O·S`. Pure rewriting under `integral_neg`; `O` is arbitrary here,
with no measurability or boundedness assumed.
DERIVED: no numeral. -/
theorem integral_deriv_eq_neg_corrNum (β : ℝ) (O : sysReal.Config → ℝ) :
    (∫ U, O U * (-(sysReal.action U) * sysReal.boltz β U) ∂(sysReal.vol (probHaar G2)))
      = -(sysReal.corrNum (probHaar G2) β (fun U => O U * sysReal.action U)) := by
  unfold System.corrNum
  rw [show (fun U => O U * (-(sysReal.action U) * sysReal.boltz β U))
        = (fun U => -((O U * sysReal.action U) * sysReal.boltz β U)) from
      funext (fun U => by ring), integral_neg]

/-- The covariance identity on `sysReal`: the Gibbs expectation `β ↦ ⟨O⟩_β` has derivative
`-(⟨O·S⟩_β - ⟨O⟩_β·⟨S⟩_β)` at every real `β`, for every measurable `O` bounded by some `M`.

The proof is the quotient rule on `⟨O⟩ = corrNum / partition`, with both parts differentiated by
`corrNum_hasDerivAt` and `partition_hasDerivAt`, their derivatives rewritten by
`integral_deriv_eq_neg_corrNum`, and the denominator kept nonzero by `sysReal_partition_pos`.

The statement gives the derivative's existence and its value. It says nothing about how that
covariance behaves as the lattice grows — `sysReal` is a fixed two-plaquette system.
DERIVED: no numeral. -/
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

/-- For a measurable `O` bounded by `M`, the map `β ↦ ⟨O⟩_β` on `sysReal` is differentiable on all of
`ℝ`. It is `expect_hasDerivAt` at each point, forgetting the derivative's value.
DERIVED: no numeral. -/
theorem expect_differentiable (O : sysReal.Config → ℝ) (hmeas : Measurable O)
    (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Differentiable ℝ (fun x : ℝ => sysReal.expect (probHaar G2) x O) :=
  fun β => (expect_hasDerivAt β O hmeas M hbound).differentiableAt

/-- `MassGap.WilsonRead.wilsonCorrReal β d` is differentiable in `β` on all of `ℝ`. It is
`expect_differentiable` applied to the product `plaqObs 0 · plaqObs d`, which is measurable and
bounded by `4` since each factor lies in `[0, 2]`.

The lag `d` ranges over `Fin 2`, the two plaquettes of `sysReal` — not over arbitrary separations.
DERIVED: the `2` in `Fin 2` is `sysReal`'s plaquette count, and the bound `4` used in the proof is `2 · 2` from `plaqObs_le_two` on each factor. -/
theorem wilsonCorrReal_differentiable (d : Fin 2) :
    Differentiable ℝ (fun β : ℝ => MassGap.WilsonRead.wilsonCorrReal β d) :=
  expect_differentiable _ ((measurable_plaqObs 0).mul (measurable_plaqObs d)) 4
    (fun U => by
      rw [abs_of_nonneg (mul_nonneg (plaqObs_nonneg 0 U) (plaqObs_nonneg d U))]
      calc plaqObs 0 U * plaqObs d U
          ≤ 2 * 2 := mul_le_mul (plaqObs_le_two 0 U) (plaqObs_le_two d U)
              (plaqObs_nonneg d U) (by norm_num)
        _ = 4 := by norm_num)

/-! ### The covariance bound with no locality hypothesis

`expect_hasDerivAt` makes the `β`-derivative a covariance, so a Lipschitz constant for `β ↦ ⟨O⟩_β` is
a bound on `|Cov_β(O, S)|`. The next theorem gives one that assumes nothing beyond a bound on the
observable, and its constant is proportional to `Fintype.card Pq`: the action is a sum over
plaquettes (`wilsonSystem_action_le : S ≤ 2 · Fintype.card Pq`), so any bound routed through the
action's range carries that factor.

`MassGap.le_of_lipschitz_grid` consumes a Lipschitz constant, so a constant proportional to the
plaquette count yields an interval statement whose strength depends on the lattice size. The lemmas
after it replace that factor, under a hypothesis about where the connected correlator lives. -/

/-- For any `SU(N)` Wilson system with `N ≠ 0`, any coupling `β`, and any measurable observable
bounded by `M`, the covariance obeys `|⟨O·S⟩_β - ⟨O⟩_β·⟨S⟩_β| ≤ 4 · M · Fintype.card Pq`.

The bound goes through the action's range: `wilsonSystem_action_le` gives
`|S| ≤ 2 · Fintype.card Pq`, so each of the two terms is bounded by `M · 2 · Fintype.card Pq` and
their difference by twice that. `M` is not assumed nonnegative in the statement; nonnegativity is
recovered from `hbound` at the constant-`1` configuration. The plaquette count therefore appears in
the constant, because nothing restricts which plaquettes contribute.
DERIVED: the `0` is the `N ≠ 0` needed for `wilsonSystem_action_nonneg`; the `4` is `2 + 2`, the action's range `2 · Fintype.card Pq` entering once for `⟨O·S⟩` and once for `⟨O⟩·⟨S⟩`. -/
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

/-- `β ↦ ⟨O⟩_β` on `sysReal` is Lipschitz on all of `ℝ` with constant `4 · M · 2`, for every
measurable `O` bounded by `M`.

The mean value theorem on the convex set `Set.univ`, with the derivative supplied by
`expect_hasDerivAt` and bounded by `cov_bound_extensive` instantiated at `N = 2` and the boundary map
`bd2`, whose plaquette type is `Fin 2`.
DERIVED: the `4` is `cov_bound_extensive`'s, and the `2` is `Fintype.card (Fin 2)`, `sysReal`'s plaquette count — so the constant is `8 · M` and it is fixed by this one system's size. -/
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

/-! ### Bounding the covariance by a support instead of by the plaquette count

`S = ∑_p φ_p`, so `Cov(O, S) = ∑_p Cov(O, φ_p)` (`cov_eq_sum_over_plaquettes`). If the summands
vanish off a finite set `supp`, the sum is bounded by `supp.card` terms rather than by
`Fintype.card Pq`, and the Lipschitz constant becomes `4 · M · supp.card`.

The lemmas below take that vanishing as a hypothesis. Nothing is assumed about how it arises, and no
new constant appears: `C` is the caller's own per-term bound and `supp` is whatever set the caller
names.

The hypothesis is satisfiable: `WilsonReal.expect_plaqObs_factor` gives
`⟨φ₀φ₁⟩_β = ⟨φ₀⟩_β·⟨φ₁⟩_β` at every `β` for the two link-disjoint plaquettes of `sysReal`, so their
connected correlator is identically zero, while `InteractingTwoPoint` exhibits a shared-link pair
whose connected correlator is not. Whether the vanishing holds outside a bounded neighbourhood on a
larger lattice is not addressed here; it enters every theorem below as `hclust`. -/

/-- A finite sum of reals whose terms vanish off a `Finset supp` and are each bounded by `C` in
absolute value satisfies `|∑ p, cov p| ≤ C * supp.card`. The index type is an arbitrary `Fintype`,
and the bound refers to `supp.card`, not to `Fintype.card ι`.

`Finset.sum_subset` restricts the sum to `supp` using `hloc`, then the triangle inequality and
`hb` give the count. Applied to `cov_eq_sum_over_plaquettes`, this is what replaces the plaquette
count by the size of the set where the connected correlator is allowed to be nonzero.
DERIVED: the `0` is the value `hloc` requires off `supp`; `C` and `supp` are both supplied by the caller. -/
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

/-- Expectation commutes with a finite sum of observables: for a family `f` indexed by the plaquette
type, each member measurable and bounded by a common `M`, and any `Finset s`,
`⟨∑_{p ∈ s} f p⟩_β = ∑_{p ∈ s} ⟨f p⟩_β`.

Induction on `s` with `wilsonSystem_expect_add` at each step. The common bound `M` is what keeps the
partial sums integrable, via `|∑_{p ∈ u} f p U| ≤ u.card * M`; `hN : N ≠ 0` is needed by
`wilsonSystem_mul_boltz_integrable`. This is the linearity step behind
`cov_eq_sum_over_plaquettes`.
DERIVED: the `0` is the `N ≠ 0` that the integrability lemmas require; there is no other numeral in the statement. -/
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

/-- The action of a Wilson system is the sum of its plaquette observables:
`action U = ∑ p, wilsonPlaqObs bd p U`, definitionally, so the proof is `rfl`. It holds for every
`N`, with no `N ≠ 0` hypothesis, because it unfolds a definition rather than using any bound.
DERIVED: no numeral. -/
theorem action_eq_sum_plaqObs {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).action U = ∑ p, wilsonPlaqObs bd p U := rfl

/-- The covariance splits over the plaquettes, as an equality:
`⟨O·S⟩_β - ⟨O⟩_β·⟨S⟩_β = ∑ p, (⟨O·φ_p⟩_β - ⟨O⟩_β·⟨φ_p⟩_β)`.

`action_eq_sum_plaqObs` turns `S` into the plaquette sum, `expect_finset_sum` moves the expectation
inside both `⟨O·S⟩` and `⟨S⟩`, and `Finset.mul_sum` distributes the product term. The measurability
and boundedness hypotheses on `O` are what `expect_finset_sum` needs; no inequality is used and no
constant is introduced.
DERIVED: the `0` is the `N ≠ 0` required by the integrability lemmas underneath `expect_finset_sum`. -/
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

/-- The covariance bound with a locality hypothesis: if the connected correlator
`⟨O·φ_p⟩_β - ⟨O⟩_β·⟨φ_p⟩_β` is exactly `0` for every plaquette outside a `Finset supp`, then

    |⟨O·S⟩_β - ⟨O⟩_β·⟨S⟩_β| ≤ 4 * M * supp.card

with `Fintype.card Pq` absent from the conclusion. It is `cov_eq_sum_over_plaquettes` followed by
`cov_sum_bound_of_local`, with the per-term bound `4 * M` coming from `wilsonPlaqObs_le_two`.

`hclust` is a hypothesis at this one coupling `β`, and this file proves it for no lattice. The
statement is the implication only; compare `cov_bound_extensive`, which is the same bound with
`supp.card` replaced by the plaquette count and no hypothesis at all.
DERIVED: the `0`s are the `N ≠ 0` and the exact vanishing `hclust` asserts; the `4` is `2 + 2`, each `2` being `wilsonPlaqObs_le_two` entering once for `⟨O·φ_p⟩` and once for `⟨O⟩·⟨φ_p⟩`. -/
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


/-! ## The same differentiation at arbitrary volume

Everything above that differentiates is stated on `sysReal`, the two-plaquette instance, so its
constants are fixed by that one system.

The theorems below redo the same argument for an arbitrary `SU(N)` Wilson system — any link type, any
plaquette type, any boundary map — so that `Fintype.card Pq` appears explicitly in each bound. The
action bound used throughout is `wilsonSystem_action_le`, namely `2 * Fintype.card Pq`, which comes
from `wilsonDensity_le_two` per plaquette. -/

/-- The Boltzmann weight of an arbitrary `SU(N)` Wilson system at a fixed configuration has
derivative `-S(U)·e^{-βS(U)}` in the coupling, at every real `β`. The same chain rule as
`boltz_hasDerivAt`, and it needs no `N ≠ 0` hypothesis, since no bound on the action is used.
DERIVED: no numeral. -/
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

/-- For `x` in the ball of radius `1` around `β`, the Boltzmann weight of an arbitrary `SU(N)` Wilson
system is at most `exp ((|β| + 1) * (2 * Fintype.card Pq))`, uniformly in the configuration. The
volume-general form of `boltz_le_on_ball`, with the plaquette count in place of `sysReal`'s `4`. It
requires `N ≠ 0`, which `wilsonSystem_boltz_le` needs.
DERIVED: the `0` is the `N ≠ 0`; the `1` is the ball radius, giving `|x| ≤ |β| + 1`; the `2` is `wilsonDensity_le_two` per plaquette, so the action's range is `2 * Fintype.card Pq`. -/
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

/-- The unnormalised correlator of an arbitrary `SU(N)` Wilson system has derivative
`∫ O·(-S)·e^{-βS}` in the coupling, at every real `β`, for every measurable `O` bounded by some `M`.

Differentiation under the integral sign with `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on
the ball of radius `1`. Here the dominating constant is
`M * ((2 * Fintype.card Pq) * exp ((|β| + 1) * (2 * Fintype.card Pq)))`, which grows with the
plaquette count but is still a constant in `U`, hence integrable against the probability measure on
configurations. `N ≠ 0` is needed by the integrability and bound lemmas.
DERIVED: the `0` is the `N ≠ 0`; the statement carries no other numeral. -/
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

/-- The volume-general form of `integral_deriv_eq_neg_corrNum`: pulls the minus sign out of the
differentiated integrand, giving `∫ O·(-S)·e^{-βS} = -(corrNum β (O·S))`. Pure rewriting under
`integral_neg`, so `O` is arbitrary and `N ≠ 0` is not needed.
DERIVED: no numeral. -/
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

/-- The covariance identity on an arbitrary `SU(N)` Wilson system: `β ↦ ⟨O⟩_β` has derivative
`-(⟨O·S⟩_β - ⟨O⟩_β·⟨S⟩_β)` at every real `β`, for every measurable `O` bounded by some `M`.

The same quotient-rule argument as `expect_hasDerivAt`, using `wilsonSystem_corrNum_hasDerivAt` for
both numerator and denominator, `wilsonSystem_integral_deriv` to rewrite the derivatives, and
`wilsonSystem_partition_pos` to keep the denominator nonzero. No constant appears in the conclusion:
the plaquette count enters only when the covariance on the right is itself bounded.
DERIVED: the `0` is the `N ≠ 0` required downstream; the statement carries no other numeral. -/
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

/-- A Lipschitz bound whose constant is `supp.card` rather than the plaquette count: given that the
connected correlator vanishes off `supp` at *every* real coupling `z`,

    |⟨O⟩_x - ⟨O⟩_y| ≤ (4 * M * supp.card) * |x - y|

for all real `x`, `y`, on any `SU(N)` Wilson system with `N ≠ 0`. The mean value theorem on
`Set.univ`, with `wilsonSystem_expect_hasDerivAt` giving the derivative and `cov_bound_local` bounding
it at each point.

`hclust` is quantified over all `z : ℝ`, not over an interval, and it is assumed, not proved.
`Fintype.card Pq` does not appear in the conclusion, but it does not follow that `supp.card` is
independent of the lattice — that is part of what `hclust` is asked to supply.
DERIVED: the `0`s are the `N ≠ 0` and the exact vanishing `hclust` asserts; the `4` is `cov_bound_local`'s, itself `2 + 2` from `wilsonPlaqObs_le_two`. -/
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


/-! ## Interval statements from a Lipschitz constant and a grid

`MassGap.le_of_lipschitz_grid` turns a Lipschitz constant plus a `δ`-grid of values into a bound at
every point of an interval. The two theorems below feed it the constants derived above, for an
observable of an `SU(N)` Wilson Gibbs measure, so the Lipschitz hypothesis is discharged rather than
assumed — the clustering hypothesis `hclust` remains. -/

/-- `⟨O⟩_β ≤ B` for every `β` in `Set.Icc a b`, on an `SU(N)` Wilson system with `N ≠ 0`, given a
measurable `O` bounded by a nonnegative `M`, a clustering set `supp` with `hclust` at every real
coupling, and `hcover`: every `β` in the interval has a `γ` in it within `δ` whose expectation is at
most `B - (4 * M * supp.card) * δ`.

`expect_lipschitz_local` supplies the Lipschitz hypothesis of `MassGap.le_of_lipschitz_grid`;
`hcover` supplies the grid. `a`, `b`, `B` and `δ` are implicit and unconstrained apart from what
`hcover` asserts — in particular `δ` is not required to be nonnegative here, unlike in
`wilson_le_uniform_in_volume`.
DERIVED: the `0`s are the `N ≠ 0`, the `0 ≤ M`, and the exact vanishing `hclust` asserts; the `4` is `expect_lipschitz_local`'s. -/
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

/-- The same conclusion for a family of `SU(N)` Wilson systems indexed by a natural number `V`, each
with its own link type, plaquette type and boundary map. Given

  * one bound `M` on the observable at every index,
  * `hclust` at every index and every real coupling, with supports whose cards share the bound `R`,
  * one `δ`-grid clearing `B - (4 * M * R) * δ` at every index,

it concludes `⟨O V⟩_β ≤ B` on `Set.Icc a b`, for every `V`. `Fintype.card (Pq V)` appears in neither
the hypotheses nor the conclusion; the constant is `4 * M * R`, and `hR` is what keeps it fixed as
`V` varies.

The proof weakens `expect_lipschitz_local`'s `4 * M * (supp V).card` to `4 * M * R` using `hR V`, then
applies `MassGap.le_of_lipschitz_grid` at each `V`. The index `V` is a bare natural number: nothing in
the statement makes the lattices grow with it, and no limit is taken.

`hclust` and `hR` are hypotheses. Whether a real lattice family satisfies them is not addressed.
DERIVED: the `0`s are the `N ≠ 0`, the `0 ≤ M`, the `0 ≤ δ` and the exact vanishing `hclust` asserts; the `4` is `expect_lipschitz_local`'s, itself `2 + 2` from `wilsonPlaqObs_le_two`. -/
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


/-! ## The summable form of the locality hypothesis

`cov_bound_local` asks the connected correlator to be exactly `0` outside a finite set. The theorems
below weaken that to domination: the connected correlator at plaquette `p` is at most `c p`, and the
`c p` total at most `K`. The conclusion's constant is then `K`.

This subsumes the vanishing form — take `c` to be `4 * M` on `supp` and `0` off it, with total
`4 * M * supp.card`. As before, both the domination and the total are hypotheses. -/

/-- If `|cov p| ≤ c p` for every index and `∑ p, c p ≤ K`, then `|∑ p, cov p| ≤ K`. The triangle
inequality followed by `Finset.sum_le_sum` and `hsum`. The index type is an arbitrary `Fintype` and
`c` is not assumed nonnegative — that follows from `hdom`.
DERIVED: no numeral. -/
theorem cov_sum_bound_of_summable {ι : Type*} [Fintype ι]
    (cov : ι → ℝ) (c : ι → ℝ) (K : ℝ)
    (hdom : ∀ p, |cov p| ≤ c p) (hsum : ∑ p, c p ≤ K) :
    |∑ p, cov p| ≤ K :=
  le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun p _ => hdom p))) hsum

/-- `|⟨O·S⟩_β - ⟨O⟩_β·⟨S⟩_β| ≤ K` whenever the connected correlator at each plaquette is dominated by
`c p` and `∑ p, c p ≤ K`. It is `cov_eq_sum_over_plaquettes` followed by
`cov_sum_bound_of_summable`.

`K` is whatever the caller's profile totals; `M` appears only in the hypotheses that make the split
valid, not in the conclusion. Nothing here bounds `K` — that is `hsum`'s job.
DERIVED: the `0` is the `N ≠ 0` required by the split; the statement carries no other numeral. -/
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

/-- `|⟨O⟩_x - ⟨O⟩_y| ≤ K * |x - y|` for all real `x`, `y`, when the connected correlator is dominated
by a profile `c z` at every coupling `z` whose total is at most `K`. The mean value theorem on
`Set.univ`, with `wilsonSystem_expect_hasDerivAt` for the derivative and `cov_bound_summable` for the
bound at each point.

The profile is allowed to depend on the coupling; `K` is not. `M` is used only through the
measurability and boundedness needed by the split, and does not appear in the constant.
DERIVED: the `0` is the `N ≠ 0`; the statement carries no other numeral. -/
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

/-- The summable counterpart of `wilson_le_uniform_in_volume`. For a family of `SU(N)` Wilson systems
indexed by a natural number `V`, given one bound `M` on the observable at every index, a dominating
profile `c V z` at every index and coupling, one nonnegative total `K` bounding every
`∑ p, c V z p`, and one `δ`-grid clearing `B - K * δ` at every index, the conclusion is
`⟨O V⟩_β ≤ B` on `Set.Icc a b` for every `V`.

`expect_lipschitz_summable` supplies the Lipschitz constant `K` and `MassGap.le_of_lipschitz_grid`
does the rest. The hypothesis is domination rather than exact vanishing, so the correlator is never
required to be zero anywhere.

`hdom` and `hsum` are hypotheses, and `K`'s independence of `V` is asserted by `hsum`, not derived.
`Fintype.card (Pq V)` appears nowhere, and no limit in `V` is taken.
DERIVED: the `0`s are the `N ≠ 0` and the `0 ≤ K` that `le_of_lipschitz_grid` requires of its constant; the statement carries no other numeral. -/
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
