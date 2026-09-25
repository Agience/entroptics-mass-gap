import Mathlib
import MassGap.Moment
import MassGap.WilsonBridge
import MassGap.ReflectionPositivity

/-!
# MassGap.StrongCoupling — geometric clustering at small coupling

This file bounds the connected Wilson plaquette correlation on a finite lattice by a constant times
a geometric factor in the touch-distance between the two plaquettes, and carries that bound to the
weights of a `Moment.Read`. Both the constant and the rate are read off the plaquette-graph degree
`touchDeg bd` and the coupling `β`; the lattice extent appears in neither.

## The expansion

Write the Boltzmann weight as a product over plaquettes and expand each factor as
`1 + (e^{−βφ_p} − 1)`. `boltz_eq_subset_sum` makes that a finite sum over subsets of plaquettes,
an identity at every `β` with nothing to converge. Each activated plaquette pays a factor of at most
`e^{2|β|} − 1` (`boltz_factor_bound`), so a subset of size `n` weighs at most `(e^{2|β|} − 1)ⁿ`
(`subset_weight_bound`), and the touch-connected sets of size `n` containing a fixed plaquette
number at most `touchDeg bd ^ n` (`card_connSets_le`). Summing from size `k` upwards gives
`coreConst · coreRate ^ k` with `coreRate K β = K · (e^{2β} − 1)`.

## The two halves

* Analytic: `boltz_factor_bound` for the per-plaquette weight, `decay_of_tail_series` and the
  `assembly_arith` lemmas for the resummation, and `core_rate_lt_one_of_small` and
  `core_rate_lt_one_of_small_hypercubic` for the `β` below which the rate is under one.
* Combinatorial: `nonbridging_sum_eq_zero`, and `wilsonCorrConn_eq_bridging_sum` on the correlation
  itself, say a pair of activated subsets carrying no touching chain from `p₀` to `p_d` contributes
  exactly zero, at every coupling and every lattice size. `card_connSets_le`,
  `card_bridging_pairs_le`, `card_ge_of_bridging` and `coreSpan_card_ge_of_not_mem_ball` count the
  surviving pairs and make the separation force their size. `pairTerm_abs_le` bounds the per-pair
  factor and `hard_core_ratio_le` the `Z²` denominator on `0 ≤ β`.

The cancellation is an explicit involution on pairs of activated subsets, exchanging the halves that
lie beyond a separator. It uses no expansion in `β` and no bound on the lattice size.

## Inputs from elsewhere in the tree

* `MassGap.WilsonBridge` — `wilsonCorrConn`, the connected correlation this file bounds.
* `MassGap.ReflectionPositivity.hol_congr_on_support` — a holonomy reads only the links its own
  boundary word names; every restriction lemma here goes through it.
* `MassGap.WilsonReal.block_integral_factor` — product Haar factorises across disjoint link blocks;
  every splitting lemma here goes through it.
* `MassGap.Moment` — `Read`, `Read.p` and `circLag`, the weights the final bound lands on.

## Scope

`wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds the connected Wilson correlation by
`coreConst · coreRate ^ k` whenever `pd ∉ ball bd p₀ k`. `siteAtHyper_not_mem_ball` converts that
touch-ball index into the lag `Moment.Read` carries, at the circle distance the periodic torus
imposes rather than the raw lag, and `read_p_le_of_corrClay` carries the bound to the read's
weights. The constant and the rate both depend on `β`, and the rate is below one only for `β` near
`0`. Everything here is stated on a finite lattice at a fixed coupling; the hypercubic sections fix
the periodic torus `Site dim n`.
-/

namespace MassGap.StrongCoupling

open Filter

/-! ### The analytic half -/

/-- **The Boltzmann factor of one plaquette sits within `e^{2|β|} − 1` of one.** For a real `φ` with
`0 ≤ φ ≤ 2` and any real `β`, `|e^{−βφ} − 1| ≤ e^{2|β|} − 1`.

The statement is about an arbitrary real in that range. The two hypotheses are the range of the
Wilson plaquette density `φ_W(g) = 1 − ½ Re tr g` on `SU(N)`, discharged at the call sites in
`subset_weight_bound` by `wilsonDensity_nonneg` and `wilsonDensity_le_two`.

DERIVED: the `0` and the `2` bounding `φ` are that density's range; the `2` in the exponent is the
same one, entering through `|β * φ| ≤ 2 * |β|`. The two `1`s are `e^0`, the factor at zero coupling,
from which both sides measure the deviation. -/
theorem boltz_factor_bound {β φ : ℝ} (h0 : 0 ≤ φ) (h2 : φ ≤ 2) :
    |Real.exp (-(β * φ)) - 1| ≤ Real.exp (2 * |β|) - 1 := by
  have habs : |β * φ| ≤ 2 * |β| := by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg β]
  obtain ⟨hlo', hup'⟩ := abs_le.mp habs
  have hup : Real.exp (-(β * φ)) ≤ Real.exp (2 * |β|) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlo : Real.exp (-(2 * |β|)) ≤ Real.exp (-(β * φ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : Real.exp (2 * |β|) * Real.exp (-(2 * |β|)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (2 * |β|)
  have hposn := Real.exp_pos (-(2 * |β|))
  have hsum : 2 ≤ Real.exp (2 * |β|) + Real.exp (-(2 * |β|)) := by
    nlinarith [sq_nonneg (Real.exp (2 * |β|) - 1)]
  rw [abs_le]
  constructor <;> linarith

#print axioms boltz_factor_bound

/-! ### From the correlation to the read's weights -/

/-- **A geometric bound on the unnormalised weights is a geometric bound on the normalised ones.**
Given `0 < m`, `m ≤ ∑ d, R.ρ d`, `0 ≤ C`, `0 ≤ q` and `R.ρ d ≤ C * q ^ (d : ℕ)` at every lag, the
normalised weight obeys `R.p d ≤ (C / m) * q ^ (d : ℕ)` at every lag.

`Moment.Read.p` is `ρ` divided by the total mass, so the lower bound `m` on that mass is what turns
a bound on the numerator into one on the quotient. `m` is a hypothesis: it is bound outside the
quantifier over `d`, and nothing in this theorem produces one.

DERIVED: the three `0`s are the sign hypotheses on `m`, `C` and `q`; the `1` in `Fin (N + 1)` is
`Moment.Read N`'s index type, which carries the `N + 1` lags `0` through `N`. -/
theorem read_decay_of_correlation_decay {N : ℕ} (R : Moment.Read N) {C q m : ℝ}
    (hm : 0 < m) (hmass : m ≤ ∑ d, R.ρ d) (hC : 0 ≤ C) (hq0 : 0 ≤ q)
    (hdecay : ∀ d : Fin (N + 1), R.ρ d ≤ C * q ^ (d : ℕ)) :
    ∀ d : Fin (N + 1), R.p d ≤ (C / m) * q ^ (d : ℕ) := by
  intro d
  have hsum : 0 < ∑ d', R.ρ d' := lt_of_lt_of_le hm hmass
  have hpd : R.p d = R.ρ d / ∑ d', R.ρ d' := rfl
  rw [hpd, div_le_iff₀ hsum]
  have hqd : 0 ≤ q ^ (d : ℕ) := pow_nonneg hq0 _
  have hstep : R.ρ d ≤ C * q ^ (d : ℕ) := hdecay d
  have hmul : (C / m) * q ^ (d : ℕ) * m = C * q ^ (d : ℕ) := by field_simp
  calc R.ρ d ≤ C * q ^ (d : ℕ) := hstep
    _ = (C / m) * q ^ (d : ℕ) * m := hmul.symm
    _ ≤ (C / m) * q ^ (d : ℕ) * (∑ d', R.ρ d') := by
        refine mul_le_mul_of_nonneg_left hmass ?_
        exact mul_nonneg (div_nonneg hC hm.le) hqd

#print axioms read_decay_of_correlation_decay

/-! ### A tail series with Cauchy-bounded coefficients

`decay_of_tail_series` is a real-analysis fact stated for an arbitrary coefficient sequence, with no
lattice and no measure in it: a series whose terms all carry order at least `d`, with coefficients
obeying the Cauchy estimate `|a_k| ≤ M / R^k`, sums at `0 ≤ x < R` to at most
`M (x/R)^d / (1 − x/R)`. The order `d` becomes the exponent and the rate is `x / R`, the evaluation
point measured against the radius. -/

/-- **A series supported on orders `≥ d`, with Cauchy-bounded coefficients, decays geometrically.**
If `|a (d + n)| ≤ M / R ^ (d + n)` for every `n` — the Cauchy estimate for a function analytic and
bounded by `M` on a disc of radius `R` — and `0 ≤ M`, `0 < R`, `0 ≤ x < R`, then
`|∑' n, a (d + n) * x ^ (d + n)| ≤ M * (x / R) ^ d / (1 - x / R)`.

The coefficient hypothesis is imposed only at the indices `d + n`, so entries of `a` below order `d`
are unconstrained and do not enter the sum.

DERIVED: the `0`s are the sign hypotheses `0 ≤ M`, `0 < R` and `0 ≤ x`; the `1` is the value
`(1 - x / R)⁻¹` of the geometric series at ratio `x / R`. -/
theorem decay_of_tail_series {a : ℕ → ℝ} {M R x : ℝ} (d : ℕ)
    (hM : 0 ≤ M) (hR : 0 < R) (hx0 : 0 ≤ x) (hxR : x < R)
    (hcoef : ∀ n : ℕ, |a (d + n)| ≤ M / R ^ (d + n)) :
    |∑' n : ℕ, a (d + n) * x ^ (d + n)| ≤ M * (x / R) ^ d / (1 - x / R) := by
  have hq0 : 0 ≤ x / R := div_nonneg hx0 hR.le
  have hq1 : x / R < 1 := (div_lt_one hR).mpr hxR
  -- each term is under the geometric one
  have hterm : ∀ n : ℕ, ‖a (d + n) * x ^ (d + n)‖ ≤ M * (x / R) ^ (d + n) := by
    intro n
    have hRpow : (0 : ℝ) < R ^ (d + n) := pow_pos hR _
    have hxpow : (0 : ℝ) ≤ x ^ (d + n) := pow_nonneg hx0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxpow]
    calc |a (d + n)| * x ^ (d + n) ≤ M / R ^ (d + n) * x ^ (d + n) :=
          mul_le_mul_of_nonneg_right (hcoef n) hxpow
      _ = M * (x / R) ^ (d + n) := by rw [div_pow]; ring
  -- the dominating series sums, and to the claimed value
  have hgeom : HasSum (fun n : ℕ => M * (x / R) ^ (d + n))
      (M * (x / R) ^ d * (1 - x / R)⁻¹) := by
    have hbase := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * (x / R) ^ d)
    refine hbase.congr_fun ?_
    intro n; rw [pow_add]; ring
  refine le_trans (tsum_of_norm_bounded hgeom hterm) (le_of_eq ?_)
  field_simp

#print axioms decay_of_tail_series

/-! ### The estimate the expansion produces

The bound assembled in this file is `wilsonCorrConn_abs_le_coreConst_mul_rate_pow`: the connected
Wilson correlation is at most `coreConst · coreRate ^ k` whenever `pd ∉ ball bd p₀ k`, with
`coreConst` and `coreRate` functions of `touchDeg bd` and `β` alone. Three ingredients go into it:

* the cancellation — `nonbridging_sum_eq_zero`, and on the Wilson correlation itself
  `wilsonCorrConn_eq_bridging_sum`: a pair of activated subsets that carries no touching chain from
  `p₀` to `pd` contributes exactly zero, at every coupling and every lattice size;
* the count of the pairs that survive — `card_connSets_le` and `card_bridging_pairs_le`, neither
  mentioning the lattice extent, with `card_ge_of_bridging` and `coreSpan_card_ge_of_not_mem_ball`
  making the separation force the size;
* the weight — `pairTerm_abs_le` for the per-pair factor, with `hard_core_ratio_le` bounding the
  `Z²` denominator on `0 ≤ β`.

The index throughout is the touch-ball `ball bd p₀ k`, while a `Moment.Read` is indexed by a lag.
`siteAtHyper_not_mem_ball` converts between them on the periodic hypercubic lattice, at the circle
distance the torus imposes rather than the raw lag, and `read_p_le_of_corrClay` carries the result
to the read's weights. -/

/-! ### Zero coupling

At `β = 0` the Boltzmann weight is `1`, so the Gibbs state is product Haar and two plaquettes drawing
on disjoint link sets are independent. `wilsonCorrConn_at_zero_of_disjoint` below turns that into the
vanishing of the connected correlation, for an arbitrary plaquette geometry, with the disjointness
of the two link sets carried as an explicit hypothesis. -/

section ZeroCoupling

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

open scoped Classical in
/-- Extend a tuple on `S` to a full link configuration, taking the group identity outside `S`.

CHOSEN: the `1` is the group identity of `SU(Nc)`, filling the links outside `S`. It is not a
magnitude and nothing depends on it: every consumer carries a support hypothesis placing the links
it reads inside `S`, which is what `plaqOn_eq`, `prodOn_eq`, `actOn_eq` and `locOn_eq` use. -/
noncomputable def extendOn (S : Finset Lk) (v : S → MassGap.SUN.SU Nc) : Lk → MassGap.SUN.SU Nc :=
  fun i => if h : i ∈ S then v ⟨i, h⟩ else 1

/-- The Wilson plaquette observable of `p`, as a function of a tuple on `S` alone, via `extendOn`.

DERIVED: no numeral. -/
noncomputable def plaqOn (bd : Pq → List (Lk × Bool)) (p : Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  wilsonPlaqObs (N := Nc) bd p (extendOn (Lk := Lk) (Nc := Nc) S v)

/-- **Restricting a configuration to `S` does not change the plaquette observable**, provided every
link of `p`'s boundary word lies in `S`. Proved from
`MassGap.ReflectionPositivity.hol_congr_on_support`: a holonomy reads only the links its own word
names, and outside `S` the extension differs from `U`.

DERIVED: no numeral. -/
theorem plaqOn_eq (bd : Pq → List (Lk × Bool)) (p : Pq) (S : Finset Lk)
    (hsupp : ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    plaqOn (Nc := Nc) bd p S (fun i : S => U i.val) = wilsonPlaqObs (N := Nc) bd p U := by
  unfold plaqOn wilsonPlaqObs
  congr 1
  refine MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => ?_)
  have hmem : l ∈ S := hsupp l hl
  simp only [extendOn, dif_pos hmem]

/-- `plaqOn bd p S` is measurable. `extendOn` is coordinatewise a projection or a constant, so it is
measurable, and `measurable_wilsonPlaqObs` supplies the rest.

DERIVED: no numeral. -/
theorem measurable_plaqOn (bd : Pq → List (Lk × Bool)) (p : Pq) (S : Finset Lk) :
    Measurable (plaqOn (Nc := Nc) bd p S) := by
  refine (measurable_wilsonPlaqObs bd p).comp ?_
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i ∈ S
  · simp only [extendOn, dif_pos h]; exact measurable_pi_apply (⟨i, h⟩ : S)
  · simp only [extendOn, dif_neg h]; exact measurable_const

/-- **At zero coupling the connected correlation of two link-disjoint plaquettes vanishes**, at any
plaquette geometry. The hypotheses are two link sets `S`, `T` with `Disjoint S T`, `p₀`'s boundary
word inside `S` and `p`'s inside `T`; the conclusion is `wilsonCorrConn bd p₀ 0 p = 0`.

At zero coupling the Boltzmann weight is `1`, so the state is product Haar
(`wilsonSystem_expect_at_zero`) and observables reading disjoint blocks are independent
(`WilsonReal.block_integral_factor`). The unconnected correlation is then exactly the product of the
two marginals, which is what `wilsonCorrConn` subtracts.

DERIVED: the first `0` is the coupling the statement fixes — this is the `β = 0` case only, and
`wilsonCorrConn_eq_zero_of_split` is the corresponding statement at arbitrary `β`. The second `0` is
the value of the connected correlation. -/
theorem wilsonCorrConn_at_zero_of_disjoint (bd : Pq → List (Lk × Bool)) (p₀ p : Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    (h0 : ∀ l ∈ (bd p₀).map Prod.fst, l ∈ S)
    (h1 : ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ 0 p = 0 := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (plaqOn (Nc := Nc) bd p₀ S) (plaqOn (Nc := Nc) bd p T)
    (measurable_plaqOn bd p₀ S) (measurable_plaqOn bd p T)
  -- rewrite both sides of the factorisation into the full-configuration observables
  have hprod : ∀ U : Lk → MassGap.SUN.SU Nc,
      plaqOn (Nc := Nc) bd p₀ S (fun i : S => U i.val)
        * plaqOn (Nc := Nc) bd p T (fun i : T => U i.val)
      = wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U := by
    intro U; rw [plaqOn_eq bd p₀ S h0 U, plaqOn_eq bd p T h1 U]
  simp only [hprod] at hfac
  simp only [plaqOn_eq bd p₀ S h0, plaqOn_eq bd p T h1] at hfac
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  rw [wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero]
  show (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U
      ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
    - (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
      * (∫ U, wilsonPlaqObs (N := Nc) bd p U
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)))) = 0
  rw [show ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)))
      = Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) from rfl]
  -- the same equation, stated at the `Config` binder so `rw` matches it syntactically
  have hfac' : (∫ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
        wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
          wilsonPlaqObs (N := Nc) bd p₀ U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
          wilsonPlaqObs (N := Nc) bd p U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := hfac
  exact sub_eq_zero_of_eq hfac'

#print axioms wilsonCorrConn_at_zero_of_disjoint

/-! ### Factorisation across a link-disjoint split of two groups

`WilsonReal.block_integral_factor` is stated for two observables. `haar_prod_factor_of_split` below
is the same fact for two groups of plaquettes: `prodOn` bundles a group into a single observable of
its own links, and the two-block lemma then applies unchanged. It is the step `order_one_cancels`
and `wilsonCorrConn_eq_zero_of_split` both run on. -/

/-- A finite product of plaquette observables over `A`, as a function of a tuple on `S` alone.

DERIVED: no numeral. -/
noncomputable def prodOn (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  ∏ p ∈ A, plaqOn (Nc := Nc) bd p S v

/-- **Restricting to `S` does not change the bundled product**, given that every plaquette of `A`
draws its boundary word from `S`. A `Finset.prod_congr` over `plaqOn_eq`.

DERIVED: no numeral. -/
theorem prodOn_eq (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (hsupp : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    prodOn (Nc := Nc) bd A S (fun i : S => U i.val)
      = ∏ p ∈ A, wilsonPlaqObs (N := Nc) bd p U := by
  unfold prodOn
  exact Finset.prod_congr rfl (fun p hp => plaqOn_eq bd p S (hsupp p hp) U)

/-- `prodOn bd A S` is measurable, being a finite product of `measurable_plaqOn` factors.

DERIVED: no numeral. -/
theorem measurable_prodOn (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk) :
    Measurable (prodOn (Nc := Nc) bd A S) :=
  Finset.measurable_prod _ (fun p _ => measurable_plaqOn bd p S)

/-- **The product Haar integral factorises across a link-disjoint split of two plaquette groups.**
If every plaquette of `A` draws its boundary word from `S`, every plaquette of `B` from `T`, and `S`
and `T` are disjoint, then the Haar integral of the product over `A ∪ B` is the product of the two
group integrals.

This is `WilsonReal.block_integral_factor` with each group bundled by `prodOn`. The measure is
product Haar, not the Gibbs measure: no Boltzmann weight appears.

DERIVED: no numeral. -/
theorem haar_prod_factor_of_split (bd : Pq → List (Lk × Bool)) (A B : Finset Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hB : ∀ p ∈ B, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, (∏ p ∈ A, wilsonPlaqObs (N := Nc) bd p U) * (∏ p ∈ B, wilsonPlaqObs (N := Nc) bd p U)
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (∏ p ∈ A, wilsonPlaqObs (N := Nc) bd p U)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, (∏ p ∈ B, wilsonPlaqObs (N := Nc) bd p U)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (prodOn (Nc := Nc) bd A S) (prodOn (Nc := Nc) bd B T)
    (measurable_prodOn bd A S) (measurable_prodOn bd B T)
  simp only [prodOn_eq bd A S hA, prodOn_eq bd B T hB] at hfac
  exact hfac

#print axioms haar_prod_factor_of_split

/-! ### Order one

`wilsonCorrConn` is a ratio. Writing `N(O, β) = ∫ O e^{−βS}` and `Z(β) = ∫ e^{−βS}`,

    ρ_conn = [ N(φ₀φ_d)·Z − N(φ₀)·N(φ_d) ] / Z²,

so the connected correlation vanishes exactly where the numerator does, and the numerator is a
difference of products of integrals with no division in it. Its `βᵏ` coefficient is

    [βᵏ] = (−1)ᵏ ∑_{i+j=k} 1/(i!j!) [ ∫φ₀φ_d Sⁱ · ∫Sʲ − ∫φ₀Sⁱ · ∫φ_d Sʲ ],

a polynomial identity in product-Haar moments. `order_one_cancels` below is the `k = 1` combination:
four applications of `haar_prod_factor_of_split` and `ring`. -/

/-- **The order-one four-term combination cancels across a link-disjoint split.** For plaquettes
`p₀`, `pd`, `q` pairwise distinct, link sets `S` and `T` with `Disjoint S T`, `p₀`'s boundary word
inside `S` and `pd`'s inside `T`, and `q`'s word inside `S` or inside `T`,

    ∫φ₀φ_d·φ_q − (∫φ₀φ_q)·(∫φ_d) + (∫φ₀φ_d)·(∫φ_q) − (∫φ₀)·(∫φ_d φ_q) = 0

under product Haar.

The hypothesis on `q` is a disjunction: `q` lies wholly on one side of the split or wholly on the
other, and the statement says nothing about a `q` whose word meets both. With `q` on `p₀`'s side the
first two terms agree and the last two agree; with `q` on `pd`'s side the pairing is the mirror
image. Neither case uses anything about `q` beyond which side it lies on.

DERIVED: the `0` is the value of the four-term combination. -/
theorem order_one_cancels (bd : Pq → List (Lk × Bool)) (p₀ pd q : Pq)
    (hq0 : q ≠ p₀) (hqd : q ≠ pd) (h0d : p₀ ≠ pd)
    (S T : Finset Lk) (hST : Disjoint S T)
    (h0 : ∀ l ∈ (bd p₀).map Prod.fst, l ∈ S)
    (hd : ∀ l ∈ (bd pd).map Prod.fst, l ∈ T)
    (hq : (∀ l ∈ (bd q).map Prod.fst, l ∈ S) ∨ (∀ l ∈ (bd q).map Prod.fst, l ∈ T)) :
    (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
          * wilsonPlaqObs (N := Nc) bd q U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      - (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, wilsonPlaqObs (N := Nc) bd pd U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      + (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      - (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, wilsonPlaqObs (N := Nc) bd pd U * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) = 0 := by
  classical
  -- the split with `p₀` alone against `p_d` alone, used in both cases
  have hsplit0d := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {pd} S T hST
    (by simpa using h0) (by simpa using hd)
  simp only [Finset.prod_singleton] at hsplit0d
  rcases hq with hqS | hqT
  · -- `q` joins `p₀`'s side
    have hA := haar_prod_factor_of_split (Nc := Nc) bd {p₀, q} {pd} S T hST
      (by
        intro p hp l hl
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact h0 l hl
        · rw [Finset.mem_singleton] at hp'; subst hp'; exact hqS l hl)
      (by simpa using hd)
    have hB := haar_prod_factor_of_split (Nc := Nc) bd {q} {pd} S T hST
      (by simpa using hqS) (by simpa using hd)
    have hC := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {pd} S T hST
      (by simpa using h0) (by simpa using hd)
    simp only [Finset.prod_pair hq0.symm, Finset.prod_singleton] at hA
    simp only [Finset.prod_singleton] at hB hC
    -- the `p_d`-side integral of `φ_d · φ_q` factorises the other way
    have hD := haar_prod_factor_of_split (Nc := Nc) bd {q} {pd} S T hST
      (by simpa using hqS) (by simpa using hd)
    simp only [Finset.prod_singleton] at hD
    have hDcomm : (∫ U, wilsonPlaqObs (N := Nc) bd pd U * wilsonPlaqObs (N := Nc) bd q U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = (∫ U, wilsonPlaqObs (N := Nc) bd q U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          * (∫ U, wilsonPlaqObs (N := Nc) bd pd U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
      rw [← hD]; exact integral_congr_ae (Filter.Eventually.of_forall (fun U => by ring))
    have hAcomm : (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
          * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd q U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          * (∫ U, wilsonPlaqObs (N := Nc) bd pd U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
      rw [← hA]; exact integral_congr_ae (Filter.Eventually.of_forall (fun U => by ring))
    rw [hAcomm, hC, hDcomm]
    ring
  · -- `q` joins `p_d`'s side — the mirror image
    have hA := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {pd, q} S T hST
      (by simpa using h0)
      (by
        intro p hp l hl
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact hd l hl
        · rw [Finset.mem_singleton] at hp'; subst hp'; exact hqT l hl)
    have hB := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {q} S T hST
      (by simpa using h0) (by simpa using hqT)
    simp only [Finset.prod_singleton, Finset.prod_pair hqd.symm] at hA
    simp only [Finset.prod_singleton] at hB
    have hAcomm : (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
          * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          * (∫ U, wilsonPlaqObs (N := Nc) bd pd U * wilsonPlaqObs (N := Nc) bd q U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
      rw [← hA]; exact integral_congr_ae (Filter.Eventually.of_forall (fun U => by ring))
    rw [hAcomm, hB, hsplit0d]
    ring

#print axioms order_one_cancels

/-! ### Vanishing across a link-disjoint split, at every coupling

Suppose the plaquette type splits as `A ⊎ Aᶜ` with `A`'s links inside `S`, `Aᶜ`'s inside `T`, and
`S`, `T` disjoint, with `p₀ ∈ A` and `p_d ∈ Aᶜ`. Then the action splits as `S = S_A + S_{Aᶜ}`, each
half a function of its own links, so the Boltzmann weight factorises and every integral does:

    N(φ₀φ_d) = N_A(φ₀)·N_B(φ_d)     Z      = Z_A·Z_B
    N(φ₀)    = N_A(φ₀)·Z_B          N(φ_d) = Z_A·N_B(φ_d)

and therefore

    D = N(φ₀φ_d)·Z − N(φ₀)·N(φ_d) = N_A(φ₀)N_B(φ_d)Z_A Z_B − N_A(φ₀)Z_B Z_A N_B(φ_d) = 0

identically in `β`. The `β = 0` statement above is the special case in which the split is free.

The hypothesis is a split of the whole plaquette type, so the lemma does not apply to a lattice whose
plaquette graph is connected. It is applied below to the activated set of one term of the subset
expansion instead, in `pairTerm_add_exchange` and `nonbridging_sum_eq_zero`. -/

/-- The half of the Wilson action carried by the plaquettes of `A`, as a function of a tuple on `S`
alone, via `extendOn`.

DERIVED: no numeral. -/
noncomputable def actOn (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  ∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p (extendOn (Lk := Lk) (Nc := Nc) S v))

/-- **Restricting to `S` does not change the half-action**, given that every plaquette of `A` draws
its boundary word from `S`. A `Finset.sum_congr` over
`MassGap.ReflectionPositivity.hol_congr_on_support`.

DERIVED: no numeral. -/
theorem actOn_eq (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (hsupp : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    actOn (Nc := Nc) bd A S (fun i : S => U i.val)
      = ∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p U) := by
  unfold actOn
  exact Finset.sum_congr rfl (fun p hp => by
    rw [MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => by
      have hmem : l ∈ S := hsupp p hp l hl
      simp only [extendOn, dif_pos hmem])])

/-- The product of `E`'s plaquette observables times `exp (-β · actOn bd A S)`, the half Boltzmann
factor of `A`, all as a function of a tuple on `S` alone. This is what each of the four integrals in
`N(φ₀φ_d)·Z − N(φ₀)·N(φ_d)` restricts to on one side of a split. Note `E` and `A` are separate
arguments: the observables and the action half need not range over the same plaquettes.

DERIVED: no numeral. -/
noncomputable def wtOn (bd : Pq → List (Lk × Bool)) (E : Finset Pq) (A : Finset Pq)
    (S : Finset Lk) (β : ℝ) (v : S → MassGap.SUN.SU Nc) : ℝ :=
  prodOn (Nc := Nc) bd E S v * Real.exp (-β * actOn (Nc := Nc) bd A S v)

theorem wtOn_eq (bd : Pq → List (Lk × Bool)) (E A : Finset Pq) (S : Finset Lk) (β : ℝ)
    (hE : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    wtOn (Nc := Nc) bd E A S β (fun i : S => U i.val)
      = (∏ p ∈ E, wilsonPlaqObs (N := Nc) bd p U)
        * Real.exp (-β * ∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold wtOn
  rw [prodOn_eq bd E S hE U, actOn_eq bd A S hA U]

theorem measurable_wtOn (bd : Pq → List (Lk × Bool)) (E A : Finset Pq) (S : Finset Lk) (β : ℝ) :
    Measurable (wtOn (Nc := Nc) bd E A S β) := by
  refine (measurable_prodOn bd E S).mul ?_
  refine (Real.measurable_exp.comp ?_)
  refine (measurable_const.mul ?_)
  exact Finset.measurable_sum _ (fun p _ =>
    measurable_wilsonDensity.comp ((measurable_wilsonHol bd p).comp
      (by
        classical
        refine measurable_pi_lambda _ (fun i => ?_)
        by_cases h : i ∈ S
        · simp only [extendOn, dif_pos h]; exact measurable_pi_apply (⟨i, h⟩ : S)
        · simp only [extendOn, dif_neg h]; exact measurable_const)))

#print axioms actOn_eq
#print axioms wtOn_eq

/-- **The connected correlation vanishes across a link-disjoint split, at every coupling.** If the
plaquette type splits as `A ⊎ Aᶜ` with `A` drawing only on `S`, `Aᶜ` only on `T`, `S` and `T`
disjoint, and `p₀ ∈ A`, `pd ∈ Aᶜ`, then `wilsonCorrConn bd p₀ β pd = 0` for the given `β`, which is
universally quantified in the statement.

The action splits into two halves, each a function of its own links, so the Boltzmann weight
factorises and all four integrals do:

    N(φ₀φ_d) = a·b,  Z = c·e,  N(φ₀) = a·e,  N(φ_d) = c·b

whence `N(φ₀φ_d)·Z − N(φ₀)·N(φ_d) = abce − aecb = 0`. No coupling is assumed small and nothing is
expanded. The degenerate case `c * e = 0` is handled separately in the proof, since
`wilsonCorrConn` divides by `Z`.

The hypothesis is a split of the whole plaquette type, and `hA`/`hB` must hold for every plaquette
of `A` and of `Aᶜ`, not only for `p₀` and `pd`.

DERIVED: the `0` is the value of the connected correlation. -/
theorem wilsonCorrConn_eq_zero_of_split (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    (A : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hB : ∀ p ∈ Aᶜ, ∀ l ∈ (bd p).map Prod.fst, l ∈ T)
    (h0 : p₀ ∈ A) (hd : pd ∈ Aᶜ) (β : ℝ) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd = 0 := by
  classical
  set vol := Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) with hvol
  -- the action splits into the two halves, each a function of its own links
  have hact : ∀ U : Lk → MassGap.SUN.SU Nc,
      (wilsonSystem bd (wilsonDensity (N := Nc))).action U
        = (∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p U))
          + ∑ p ∈ Aᶜ, wilsonDensity (N := Nc) (wilsonHol bd p U) := by
    intro U
    show (∑ p, wilsonDensity (N := Nc) (wilsonHol bd p U)) = _
    rw [← Finset.sum_add_sum_compl A]
  -- the four factorisations, one per integral in the connected combination
  have hsplit : ∀ (E F : Finset Pq),
      (∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) →
      (∀ p ∈ F, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) →
      (∫ U, ((∏ p ∈ E, wilsonPlaqObs (N := Nc) bd p U)
              * (∏ p ∈ F, wilsonPlaqObs (N := Nc) bd p U))
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
        = (∫ U, wtOn (Nc := Nc) bd E A S β (fun i : S => U i.val) ∂vol)
          * (∫ U, wtOn (Nc := Nc) bd F Aᶜ T β (fun i : T => U i.val) ∂vol) := by
    intro E F hE hF
    have hfac := block_integral_factor (N := Nc) S T hST
      (wtOn (Nc := Nc) bd E A S β) (wtOn (Nc := Nc) bd F Aᶜ T β)
      (measurable_wtOn bd E A S β) (measurable_wtOn bd F Aᶜ T β)
    rw [← hfac]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    dsimp only
    rw [wtOn_eq bd E A S β hE hA U, wtOn_eq bd F Aᶜ T β hF hB U]
    unfold System.boltz
    rw [hact U, mul_add, neg_mul, neg_mul, Real.exp_add]
    ring
  -- name the four halves
  have hN2 := hsplit {p₀} {pd} (by simpa using hA p₀ h0) (by simpa using hB pd hd)
  have hZ := hsplit ∅ ∅ (by simp) (by simp)
  have hN0 := hsplit {p₀} ∅ (by simpa using hA p₀ h0) (by simp)
  have hNd := hsplit ∅ {pd} (by simp) (by simpa using hB pd hd)
  simp only [Finset.prod_singleton, Finset.prod_empty, one_mul, mul_one] at hN2 hZ hN0 hNd
  -- assemble
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  unfold System.expect System.corrNum System.partition
  show ((∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
      / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol))
    - ((∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
        / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol))
      * ((∫ U, wilsonPlaqObs (N := Nc) bd pd U
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
        / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)) = 0
  rw [hN2, hZ, hN0, hNd]
  set a := ∫ U, wtOn (Nc := Nc) bd {p₀} A S β (fun i : S => U i.val) ∂vol with ha
  set b := ∫ U, wtOn (Nc := Nc) bd {pd} Aᶜ T β (fun i : T => U i.val) ∂vol with hb
  set c := ∫ U, wtOn (Nc := Nc) bd (∅ : Finset Pq) A S β (fun i : S => U i.val) ∂vol with hc
  set e := ∫ U, wtOn (Nc := Nc) bd (∅ : Finset Pq) Aᶜ T β (fun i : T => U i.val) ∂vol with he
  rcases eq_or_ne (c * e) 0 with hz | hz
  · rw [hz]; simp
  · field_simp
    ring

#print axioms wilsonCorrConn_eq_zero_of_split

/-! ### The subset expansion

Writing `w_p = e^{−βφ_p} − 1`,

    e^{−βS} = ∏_p e^{−βφ_p} = ∏_p (1 + w_p) = ∑_{E ⊆ P} ∏_{p∈E} w_p

by `Finset.prod_add`: a finite sum over subsets of the plaquette type, holding at every `β`, with no
radius and no remainder. Each factor obeys `|w_p| ≤ e^{2|β|} − 1` (`boltz_factor_bound`), so a subset
of size `n` contributes at most `(e^{2|β|}−1)ⁿ` (`subset_weight_bound`).

The cancellation of the subsets that do not bridge `p₀` to `p_d` is not term by term. It is proved
below for pairs of subsets, under an explicit involution, in `pairTerm_add_pairFlip` and
`nonbridging_sum_eq_zero`. -/

/-- **The Boltzmann weight is a finite sum over subsets of plaquettes**, at any `β` and any
configuration: `boltz β U = ∑_{E ⊆ univ} ∏_{p ∈ E} (e^{−βφ_p(U)} − 1)`. The sum runs over
`(Finset.univ : Finset Pq).powerset`, so `Pq` being a `Fintype` is what makes it finite.

DERIVED: the `1` is the one split off each factor in `e^{−βφ_p} = (e^{−βφ_p} − 1) + 1`, which is
what `Finset.prod_add` then expands over subsets. -/
theorem boltz_eq_subset_sum (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) :
    (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
      = ∑ E ∈ (Finset.univ : Finset Pq).powerset,
          ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) := by
  classical
  have hexp : (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
      = ∏ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) := by
    unfold System.boltz
    show Real.exp (-β * ∑ p, wilsonDensity (N := Nc) (wilsonHol bd p U)) = _
    rw [Finset.mul_sum, ← Real.exp_sum]
    exact congrArg Real.exp (Finset.sum_congr rfl (fun p _ => by ring))
  rw [hexp]
  -- split each factor as `w_p + 1`, by congruence rather than rewriting (which would loop)
  have hone : ∏ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = ∏ p : Pq, ((Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) + 1) :=
    Finset.prod_congr rfl (fun p _ => by ring)
  rw [hone, Finset.prod_add]
  exact Finset.sum_congr rfl (fun E _ => by simp)

#print axioms boltz_eq_subset_sum

/-- **A subset's activated weight is at most the per-plaquette bound raised to its cardinality.**
`|∏_{p ∈ E} (e^{−βφ_p(U)} − 1)| ≤ (e^{2|β|} − 1) ^ E.card`, for any `β`, any configuration and any
`E`. Requires `Nc ≠ 0`, which is what `wilsonDensity_nonneg` and `wilsonDensity_le_two` need to put
the density in `[0, 2]`.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`, excluding the empty gauge group. The two `1`s and the
`2` are `boltz_factor_bound`'s, applied once per factor by `Finset.prod_le_prod`; the exponent is
`E.card`, not a chosen power. -/
theorem subset_weight_bound (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) (E : Finset Pq) :
    |∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1)|
      ≤ (Real.exp (2 * |β|) - 1) ^ E.card := by
  classical
  rw [Finset.abs_prod]
  calc ∏ p ∈ E, |Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1|
      ≤ ∏ _p ∈ E, (Real.exp (2 * |β|) - 1) := by
        refine Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => ?_)
        exact boltz_factor_bound (wilsonDensity_nonneg hN _) (wilsonDensity_le_two hN _)
    _ = (Real.exp (2 * |β|) - 1) ^ E.card := by rw [Finset.prod_const]

#print axioms subset_weight_bound

/-- **A Gibbs numerator is a finite sum of product-Haar integrals, one per subset of plaquettes.**
`∫ O · boltz β = ∑_{E ⊆ univ} ∫ O · ∏_{p ∈ E} (e^{−βφ_p} − 1)`, for an arbitrary observable `O`.

`boltz_eq_subset_sum` moved inside the integral. The sum being finite, linearity needs no convergence
condition, only integrability of each summand — carried here as the hypothesis `hint`, one condition
per subset.

DERIVED: the `1` is `boltz_eq_subset_sum`'s, split off each Boltzmann factor. -/
theorem corrNum_eq_subset_sum (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ)
    (hint : ∀ E ∈ (Finset.univ : Finset Pq).powerset,
      Integrable (fun U => O U * ∏ p ∈ E,
          (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
        (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) :
    (∫ U, O U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E ∈ (Finset.univ : Finset Pq).powerset,
          ∫ U, O U * (∏ p ∈ E,
              (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hfun : (fun U => O U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U)
      = fun U => ∑ E ∈ (Finset.univ : Finset Pq).powerset,
          O U * ∏ p ∈ E,
            (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) := by
    funext U
    rw [boltz_eq_subset_sum bd β U, Finset.mul_sum]
  rw [hfun]
  exact integral_finsetSum _ hint

#print axioms corrNum_eq_subset_sum

/-! ### Plaquette connectivity

Two plaquettes are coupled by the Haar measure only through a shared link, which is what
`haar_prod_factor_of_split` says. `Touch` names that relation, and `split_links_disjoint` turns a
plaquette set closed under it into the pair of disjoint link sets the analytic lemmas above consume.
`wilsonCorrConn_eq_zero_of_touch_closed` is then the vanishing statement with the link bookkeeping
discharged: its hypothesis mentions only the plaquette graph. -/

/-- The links a plaquette's boundary word names, as a `Finset`.

DERIVED: no numeral. -/
def linkSupp (bd : Pq → List (Lk × Bool)) (p : Pq) : Finset Lk :=
  ((bd p).map Prod.fst).toFinset

/-- Two plaquettes touch when some link lies in both their boundary supports. This is the relation
under which product Haar couples them; `haar_prod_factor_of_split` factorises whenever it fails.

DERIVED: no numeral. -/
def Touch (bd : Pq → List (Lk × Bool)) (p q : Pq) : Prop :=
  ∃ l ∈ linkSupp bd p, l ∈ linkSupp bd q

/-- Every link of a plaquette of `A` lies in `A.biUnion (linkSupp bd)`. This is the support
hypothesis the splitting lemmas take, discharged for the canonical link set of a plaquette group.

DERIVED: no numeral. -/
theorem supp_subset_biUnion (bd : Pq → List (Lk × Bool)) (A : Finset Pq) :
    ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ A.biUnion (linkSupp bd) := by
  intro p hp l hl
  exact Finset.mem_biUnion.mpr ⟨p, hp, by simpa [linkSupp] using hl⟩

/-- **A plaquette set closed under touching has links disjoint from its complement's.** If no
plaquette of `A` touches one outside `A`, then `A.biUnion (linkSupp bd)` and
`Aᶜ.biUnion (linkSupp bd)` are disjoint. A shared link would itself witness a touch.

This converts the combinatorial hypothesis into the pair of disjoint link sets that
`wilsonCorrConn_eq_zero_of_split` consumes.

DERIVED: no numeral. -/
theorem split_links_disjoint (bd : Pq → List (Lk × Bool)) (A : Finset Pq)
    (hclosed : ∀ p ∈ A, ∀ q, q ∉ A → ¬ Touch bd p q) :
    Disjoint (A.biUnion (linkSupp bd)) (Aᶜ.biUnion (linkSupp bd)) := by
  classical
  rw [Finset.disjoint_left]
  intro l hl hl'
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨q, hq, hlq⟩ := Finset.mem_biUnion.mp hl'
  exact hclosed p hp q (Finset.mem_compl.mp hq) ⟨l, hlp, hlq⟩

/-- **The connected correlation vanishes when a touch-closed set separates the two plaquettes.** If
`A` contains `p₀`, excludes `pd`, and no plaquette of `A` touches one outside `A`, then
`wilsonCorrConn bd p₀ β pd = 0` for the given `β`.

This is `wilsonCorrConn_eq_zero_of_split` through `split_links_disjoint` and `supp_subset_biUnion`:
the hypothesis is now about the plaquette graph alone and no link set appears in it.

DERIVED: the `0` is the value of the connected correlation. -/
theorem wilsonCorrConn_eq_zero_of_touch_closed (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    (A : Finset Pq) (hclosed : ∀ p ∈ A, ∀ q, q ∉ A → ¬ Touch bd p q)
    (h0 : p₀ ∈ A) (hd : pd ∉ A) (β : ℝ) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd = 0 := by
  classical
  exact wilsonCorrConn_eq_zero_of_split bd p₀ pd A
    (A.biUnion (linkSupp bd)) (Aᶜ.biUnion (linkSupp bd))
    (split_links_disjoint bd A hclosed)
    (supp_subset_biUnion bd A) (supp_subset_biUnion bd Aᶜ)
    h0 (Finset.mem_compl.mpr hd) β

#print axioms split_links_disjoint
#print axioms wilsonCorrConn_eq_zero_of_touch_closed

/-! ### Multiplicativity of the activated weight

The Boltzmann correction `w_p = e^{−βφ_p} − 1` reads only `p`'s own links, just as `φ_p` does, so
`haar_prod_factor_of_split` generalises from the plaquette observable to any per-plaquette function
`f`:

    ∫ ∏_{p ∈ E₁ ⊎ E₂} f(φ_p)  =  (∫ ∏_{E₁} f(φ_p)) · (∫ ∏_{E₂} f(φ_p))

whenever `E₁` and `E₂` are link-disjoint. Taking `f = id` recovers the plaquette observables; taking
`f x = e^{−βx} − 1` gives the activated-subset weights `ζ(E) = ∫ W_E` of the subset expansion. That
is `weight_mult_of_split`, and `zw_split` below is the version carrying an observable alongside. -/

/-- The product over `E` of a per-plaquette function `f` of the plaquette's own Wilson density, as a
function of a tuple on `S` alone, via `extendOn`.

DERIVED: no numeral. -/
noncomputable def locOn (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (E : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p (extendOn (Lk := Lk) (Nc := Nc) S v)))

theorem locOn_eq (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (E : Finset Pq) (S : Finset Lk)
    (hsupp : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    locOn (Nc := Nc) bd f E S (fun i : S => U i.val)
      = ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold locOn
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => by
    have hmem : l ∈ S := hsupp p hp l hl
    simp only [extendOn, dif_pos hmem])]

theorem measurable_locOn (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (E : Finset Pq) (S : Finset Lk) :
    Measurable (locOn (Nc := Nc) bd f E S) := by
  classical
  refine Finset.measurable_prod _ (fun p _ => hf.comp ?_)
  exact measurable_wilsonDensity.comp ((measurable_wilsonHol bd p).comp
    (by
      refine measurable_pi_lambda _ (fun i => ?_)
      by_cases h : i ∈ S
      · simp only [extendOn, dif_pos h]; exact measurable_pi_apply (⟨i, h⟩ : S)
      · simp only [extendOn, dif_neg h]; exact measurable_const))

/-- **The activated weight is multiplicative across a link-disjoint split.** For any measurable
per-plaquette function `f`, with `A`'s boundary words inside `S`, `B`'s inside `T` and `S`, `T`
disjoint, the product-Haar integral of `∏_A f(φ_p) · ∏_B f(φ_p)` is the product of the two integrals.

`haar_prod_factor_of_split` is the case `f = id`. Taking `f = wfun β` gives the activated-subset
weight of the expansion. `f` need only be measurable; no continuity or boundedness is assumed.

DERIVED: no numeral. -/
theorem weight_mult_of_split (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (A B : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hB : ∀ p ∈ B, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, (∏ p ∈ A, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          * (∏ p ∈ B, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (∏ p ∈ A, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, (∏ p ∈ B, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (locOn (Nc := Nc) bd f A S) (locOn (Nc := Nc) bd f B T)
    (measurable_locOn bd hf A S) (measurable_locOn bd hf B T)
  simp only [locOn_eq bd f A S hA, locOn_eq bd f B T hB] at hfac
  exact hfac

#print axioms weight_mult_of_split

/-! ### Non-bridging pairs cancel under an exchange

`boltz_eq_subset_sum` makes every Gibbs numerator a finite sum over activated subsets, so the
connected correlation's numerator

    D(β) = N(φ₀φ_d)·Z − N(φ₀)·N(φ_d)

is a finite double sum over pairs `(E, F)` of activated subsets, with summand

    T(E,F) = ζ_{p₀p_d}(E)·ζ_∅(F) − ζ_{p₀}(E)·ζ_{p_d}(F),   ζ_D(E) = ∫ (∏_{p∈D} φ_p)·∏_{p∈E} w_p,

`ζ_D(E)` being `zw` below and `T` being `pairTerm`.

Let `A` be touch-closed relative to `V = E ∪ F ∪ {p₀, p_d}` with `p₀ ∈ A` and `p_d ∉ A`, so that `A`
separates the two plaquettes inside the union of the two activated sets. Writing `X = E ∩ A`,
`Y = E \ A`, `X' = F ∩ A`, `Y' = F \ A`, all four integrals factorise across the split and

    T(E,F) = ζ₀(X)·ζ(X')·(ζ_d(Y)·ζ(Y') − ζ(Y)·ζ_d(Y')),

so the exchange `(E,F) ↦ (X ∪ Y', X' ∪ Y)` — swapping the far halves and keeping the near ones —
sends `T` to its negative. It preserves `E ∪ F`, hence `A`, hence the separating condition, and it is
an involution, so the non-bridging part of the double sum is zero. That is `pairTerm_add_pairFlip`
and `nonbridging_sum_eq_zero`. The cancellation is between pairs, not within one term, and it holds
at every `β` and every lattice size.

The pairs that survive are those in which `p₀` reaches `p_d` by a chain of touching plaquettes inside
`E ∪ F`. `card_bridging_pairs_le` counts them and `pairTerm_abs_le` bounds their weight. -/

/-- The activated weight of one plaquette, `wfun β x = e^{−βx} − 1`. A name for the function the
splitting lemmas below instantiate `f` with; `wfun_apply` is the `rfl` that unfolds it back to the
form `boltz_eq_subset_sum` produces.

DERIVED: the `1` is the one split off `e^{−βφ_p} = (e^{−βφ_p} − 1) + 1` in
`boltz_eq_subset_sum`. -/
noncomputable def wfun (β x : ℝ) : ℝ := Real.exp (-(β * x)) - 1

theorem wfun_apply (β x : ℝ) : wfun β x = Real.exp (-(β * x)) - 1 := rfl

theorem measurable_wfun (β : ℝ) : Measurable (wfun β) :=
  (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).sub measurable_const

/-- `prodOn bd D S` times `locOn bd f E S`: the plaquette observables of `D` together with the
activated weights of `E`, both read on a tuple on `S` alone. This is what one side of a link-disjoint
split of an expansion term restricts to. `D` and `E` are independent arguments.

DERIVED: no numeral. -/
noncomputable def mixOn (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (D E : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  prodOn (Nc := Nc) bd D S v * locOn (Nc := Nc) bd f E S v

theorem mixOn_eq (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (D E : Finset Pq) (S : Finset Lk)
    (hD : ∀ p ∈ D, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    mixOn (Nc := Nc) bd f D E S (fun i : S => U i.val)
      = (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold mixOn
  rw [prodOn_eq bd D S hD U, locOn_eq bd f E S hE U]

theorem measurable_mixOn (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (D E : Finset Pq) (S : Finset Lk) : Measurable (mixOn (Nc := Nc) bd f D E S) :=
  (measurable_prodOn bd D S).mul (measurable_locOn bd hf E S)

/-- An arbitrary function `O` of a tuple on `S`, times `locOn bd f E S`, the activated weights of
`E`. Where `mixOn` fixes the first factor to be a plaquette product, this leaves it free.
`mixObs_prodOn` records that `mixOn` is the plaquette instance.

DERIVED: no numeral. -/
noncomputable def mixObs (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (E : Finset Pq) (S : Finset Lk)
    (O : (S → MassGap.SUN.SU Nc) → ℝ) (v : S → MassGap.SUN.SU Nc) : ℝ :=
  O v * locOn (Nc := Nc) bd f E S v

/-- **`mixObs` at `O = prodOn bd D S` is `mixOn bd f D E S`**, by `rfl`. `D` appears only in the
observable slot, so the two bundles agree definitionally.

DERIVED: no numeral. -/
theorem mixObs_prodOn (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (D E : Finset Pq) (S : Finset Lk) :
    mixObs (Nc := Nc) bd f E S (prodOn (Nc := Nc) bd D S) = mixOn (Nc := Nc) bd f D E S := rfl

#print axioms mixObs_prodOn

/-- **What `mixObs` reads on a full configuration**: `O` at the restriction to `S`, times
`∏_{p ∈ E} f(φ_p U)`. Needs every plaquette of `E` to draw its boundary word from `S`; no hypothesis
is placed on `O`, which already takes a tuple on `S`.

DERIVED: no numeral. -/
theorem mixObs_eq (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (E : Finset Pq) (S : Finset Lk)
    (O : (S → MassGap.SUN.SU Nc) → ℝ)
    (hE : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    mixObs (Nc := Nc) bd f E S O (fun i : S => U i.val)
      = O (fun i : S => U i.val)
        * ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold mixObs
  rw [locOn_eq bd f E S hE U]

/-- `mixObs bd f E S O` is measurable when `f` and `O` are.

DERIVED: no numeral. -/
theorem measurable_mixObs (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (E : Finset Pq) (S : Finset Lk) {O : (S → MassGap.SUN.SU Nc) → ℝ} (hO : Measurable O) :
    Measurable (mixObs (Nc := Nc) bd f E S O) :=
  hO.mul (measurable_locOn bd hf E S)

#print axioms measurable_mixObs

/-- **Product Haar factorises across a link-disjoint split, with an arbitrary observable on each
side.** `O₁` is a measurable function of a tuple on `S`, `O₂` one of a tuple on `T`, `Disjoint S T`,
and `E₁`, `E₂` draw their boundary words from `S` and `T` respectively. Then the integral of
`(O₁ · ∏_{E₁} f(φ_p)) · (O₂ · ∏_{E₂} f(φ_p))` is the product of the two integrals.

`haar_mix_factor` is the case where each observable is a plaquette product. What the split asks of
an observable is measurability and locality on one link set; `WilsonReal.block_integral_factor`,
which supplies it, is already stated at that generality. `f` need only be measurable.

DERIVED: no numeral. -/
theorem haar_obs_mix_factor (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (E₁ E₂ : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    {O₁ : (S → MassGap.SUN.SU Nc) → ℝ} {O₂ : (T → MassGap.SUN.SU Nc) → ℝ}
    (hO₁ : Measurable O₁) (hO₂ : Measurable O₂)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, (O₁ (fun i : S => U i.val)
            * ∏ p ∈ E₁, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          * (O₂ (fun i : T => U i.val)
            * ∏ p ∈ E₂, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, O₁ (fun i : S => U i.val)
            * ∏ p ∈ E₁, f (wilsonDensity (N := Nc) (wilsonHol bd p U))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, O₂ (fun i : T => U i.val)
            * ∏ p ∈ E₂, f (wilsonDensity (N := Nc) (wilsonHol bd p U))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (mixObs (Nc := Nc) bd f E₁ S O₁) (mixObs (Nc := Nc) bd f E₂ T O₂)
    (measurable_mixObs bd hf E₁ S hO₁) (measurable_mixObs bd hf E₂ T hO₂)
  simp only [mixObs_eq bd f E₁ S O₁ hE₁, mixObs_eq bd f E₂ T O₂ hE₂] at hfac
  exact hfac

#print axioms haar_obs_mix_factor

/-- **Product Haar factorises across a link-disjoint split carrying observables and weights at
once.** Four plaquette groups: `D₁`, `E₁` drawing on `S` and `D₂`, `E₂` drawing on `T`, with
`Disjoint S T`. The integral of `(∏_{D₁} φ_p · ∏_{E₁} f(φ_p)) · (∏_{D₂} φ_p · ∏_{E₂} f(φ_p))` is the
product of the two side integrals.

The common generalisation of `haar_prod_factor_of_split` (observables only, `f` absent) and
`weight_mult_of_split` (weights only, `D₁ = D₂ = ∅`). A term of the subset expansion carries both,
so both must cross the split together. Nothing requires `D₁` and `E₁` to be related.

DERIVED: no numeral. -/
theorem haar_mix_factor (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (D₁ E₁ D₂ E₂ : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    (hD₁ : ∀ p ∈ D₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hD₂ : ∀ p ∈ D₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, ((∏ p ∈ D₁, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₁, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          * ((∏ p ∈ D₂, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₂, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (∏ p ∈ D₁, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₁, f (wilsonDensity (N := Nc) (wilsonHol bd p U))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, (∏ p ∈ D₂, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₂, f (wilsonDensity (N := Nc) (wilsonHol bd p U))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (mixOn (Nc := Nc) bd f D₁ E₁ S) (mixOn (Nc := Nc) bd f D₂ E₂ T)
    (measurable_mixOn bd hf D₁ E₁ S) (measurable_mixOn bd hf D₂ E₂ T)
  simp only [mixOn_eq bd f D₁ E₁ S hD₁ hE₁, mixOn_eq bd f D₂ E₂ T hD₂ hE₂] at hfac
  exact hfac

#print axioms haar_mix_factor

/-- A term of the subset expansion: `zw bd β D E = ∫ (∏_{p ∈ D} φ_p) · ∏_{p ∈ E} wfun β (φ_p)`
against product Haar, the plaquette observables of `D` read against the activated subset `E`. The
four integrals the connected numerator is built from are the choices
`D = {p₀, pd}`, `∅`, `{p₀}`, `{pd}`.

DERIVED: no numeral. -/
noncomputable def zw (bd : Pq → List (Lk × Bool)) (β : ℝ) (D E : Finset Pq) : ℝ :=
  ∫ U, (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
      * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
    ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))

/-- **A `zw` term is the product of its two half-terms when its plaquettes divide across a
link-disjoint split.** `D = D₁ ∪ D₂` and `E = E₁ ∪ E₂`, each union disjoint, with the `₁` groups
drawing on `S`, the `₂` groups on `T` and `Disjoint S T`. Then
`zw bd β D E = zw bd β D₁ E₁ * zw bd β D₂ E₂`.

`haar_mix_factor` with the two products rewritten by `Finset.prod_union`. It is the computational
step `pairTerm_add_exchange` uses, there applied eight times.

DERIVED: no numeral. -/
theorem zw_split (bd : Pq → List (Lk × Bool)) (β : ℝ) (D D₁ D₂ E E₁ E₂ : Finset Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    (hDu : D = D₁ ∪ D₂) (hEu : E = E₁ ∪ E₂)
    (hDd : Disjoint D₁ D₂) (hEd : Disjoint E₁ E₂)
    (hD₁ : ∀ p ∈ D₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hD₂ : ∀ p ∈ D₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    zw (Nc := Nc) bd β D E = zw (Nc := Nc) bd β D₁ E₁ * zw (Nc := Nc) bd β D₂ E₂ := by
  classical
  subst hDu; subst hEu
  unfold zw
  rw [← haar_mix_factor (Nc := Nc) bd (measurable_wfun β) D₁ E₁ D₂ E₂ S T hST hD₁ hE₁ hD₂ hE₂]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [Finset.prod_union hDd, Finset.prod_union hEd]
  ring

#print axioms zw_split

/-- A term of the subset expansion with the observable left free: `∫ O(U|_S) · ∏_{p ∈ E} wfun β (φ_p)`
against product Haar, where `O` is typed on a tuple on `S`. `zw` is the case where `O` is a plaquette
product (`zwObs_eq_zw`).

DERIVED: no numeral. -/
noncomputable def zwObs (bd : Pq → List (Lk × Bool)) (β : ℝ) {S : Finset Lk}
    (O : (S → MassGap.SUN.SU Nc) → ℝ) (E : Finset Pq) : ℝ :=
  ∫ U, O (fun i : S => U i.val)
      * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
    ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))

/-- **`zwObs` at `prodOn bd D S` is `zw bd β D E`**, given that every plaquette of `D` draws its
boundary word from `S`. The hypothesis is what `prodOn_eq` needs; without it the restricted product
is not the full one.

DERIVED: no numeral. -/
theorem zwObs_eq_zw (bd : Pq → List (Lk × Bool)) (β : ℝ) (D E : Finset Pq) (S : Finset Lk)
    (hD : ∀ p ∈ D, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) :
    zwObs (Nc := Nc) bd β (prodOn (Nc := Nc) bd D S) E = zw (Nc := Nc) bd β D E := by
  unfold zwObs zw
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  -- `simp only`, not `rw`: `integral_congr_ae` leaves both sides as beta-redexes.
  simp only [prodOn_eq bd D S hD U]

#print axioms zwObs_eq_zw

/-- **The split at arbitrary observables.** With `O₁` measurable on a tuple on `S`, `O₂` on one on
`T`, `Disjoint S T`, and `E = E₁ ∪ E₂` a disjoint union with `E₁` drawing on `S` and `E₂` on `T`, the
integral of `(O₁ · O₂) · ∏_{p ∈ E} wfun β (φ_p)` equals `zwObs bd β O₁ E₁ * zwObs bd β O₂ E₂`.

`zw_split` with the plaquette products replaced by two measurable observables, each reading one side
of the split. Proved from `haar_obs_mix_factor` and `Finset.prod_union`.

DERIVED: no numeral. -/
theorem zwObs_split (bd : Pq → List (Lk × Bool)) (β : ℝ) (E E₁ E₂ : Finset Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    {O₁ : (S → MassGap.SUN.SU Nc) → ℝ} {O₂ : (T → MassGap.SUN.SU Nc) → ℝ}
    (hO₁ : Measurable O₁) (hO₂ : Measurable O₂)
    (hEu : E = E₁ ∪ E₂) (hEd : Disjoint E₁ E₂)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, (O₁ (fun i : S => U i.val) * O₂ (fun i : T => U i.val))
        * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
      ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = zwObs (Nc := Nc) bd β O₁ E₁ * zwObs (Nc := Nc) bd β O₂ E₂ := by
  classical
  subst hEu
  -- unfold the two half-terms to integrals before matching the factorisation
  unfold zwObs
  rw [← haar_obs_mix_factor (Nc := Nc) bd (measurable_wfun β) E₁ E₂ S T hST hO₁ hO₂ hE₁ hE₂]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [Finset.prod_union hEd]
  ring

#print axioms zwObs_split

/-- An observable on full configurations reads only the links of `S`: there is a measurable `Ô` on
tuples over `S` with `O U = Ô (U|_S)` at every `U`. Locality as a predicate on an ordinary
observable, rather than as a restricted type.

`zwObs` types its observable on the restriction, which is what `block_integral_factor` consumes but
is awkward to compose: the product of a pair of such observables would live on `S ∪ T` and carry a
coercion at every step. With locality as a hypothesis, that product is an ordinary product.

DERIVED: no numeral. -/
def LocalOnLinks (S : Finset Lk) (O : (Lk → MassGap.SUN.SU Nc) → ℝ) : Prop :=
  ∃ Ô : (S → MassGap.SUN.SU Nc) → ℝ, Measurable Ô ∧
    ∀ U : Lk → MassGap.SUN.SU Nc, O U = Ô (fun i : S => U i.val)

/-- **A plaquette product is `LocalOnLinks S` whenever its plaquettes draw their boundary words from
`S`.** The witness is `prodOn bd D S`, measurable by `measurable_prodOn` and equal to the full
product by `prodOn_eq`.

DERIVED: no numeral. -/
theorem localOnLinks_prod (bd : Pq → List (Lk × Bool)) (D : Finset Pq) (S : Finset Lk)
    (hD : ∀ p ∈ D, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) :
    LocalOnLinks (Nc := Nc) S (fun U => ∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U) :=
  ⟨prodOn (Nc := Nc) bd D S, measurable_prodOn bd D S,
    fun U => (prodOn_eq bd D S hD U).symm⟩

#print axioms localOnLinks_prod

/-- A term of the subset expansion at an observable of full configurations:
`∫ O U · ∏_{p ∈ E} wfun β (φ_p)` against product Haar. Locality is absent from the type and enters as
a hypothesis in `zwFull_split`, the one place the split needs it.

DERIVED: no numeral. -/
noncomputable def zwFull (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ) (E : Finset Pq) : ℝ :=
  ∫ U, O U * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
    ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))

/-- **`zwFull` at `O` is `zwObs` at `Ô`**, given `O U = Ô (U|_S)` at every `U`. The hypothesis is
the equation part of `LocalOnLinks`; measurability of `Ô` is not needed here.

DERIVED: no numeral. -/
theorem zwFull_eq_zwObs (bd : Pq → List (Lk × Bool)) (β : ℝ) (E : Finset Pq) (S : Finset Lk)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} {Ô : (S → MassGap.SUN.SU Nc) → ℝ}
    (hO : ∀ U : Lk → MassGap.SUN.SU Nc, O U = Ô (fun i : S => U i.val)) :
    zwFull (Nc := Nc) bd β O E = zwObs (Nc := Nc) bd β Ô E := by
  unfold zwFull zwObs
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [hO U]

#print axioms zwFull_eq_zwObs

/-- **The split at ordinary observables.** With `LocalOnLinks S O₁`, `LocalOnLinks T O₂`,
`Disjoint S T`, and `E = E₁ ∪ E₂` a disjoint union whose halves draw on `S` and on `T`,
`zwFull bd β (O₁ · O₂) E = zwFull bd β O₁ E₁ * zwFull bd β O₂ E₂`.

`zwObs_split` with locality carried as a hypothesis rather than in the type, so that the two
observables multiply without a coercion. `pairTerm`'s four terms take this form: `(O₁·O₂, q.1)`,
`(1, q.2)`, `(O₁, q.1)` and `(O₂, q.2)` are four `zwFull`s.

DERIVED: no numeral. -/
theorem zwFull_split (bd : Pq → List (Lk × Bool)) (β : ℝ) (E E₁ E₂ : Finset Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ}
    (h₁ : LocalOnLinks (Nc := Nc) S O₁) (h₂ : LocalOnLinks (Nc := Nc) T O₂)
    (hEu : E = E₁ ∪ E₂) (hEd : Disjoint E₁ E₂)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    zwFull (Nc := Nc) bd β (fun U => O₁ U * O₂ U) E
      = zwFull (Nc := Nc) bd β O₁ E₁ * zwFull (Nc := Nc) bd β O₂ E₂ := by
  classical
  obtain ⟨Ô₁, hm₁, he₁⟩ := h₁
  obtain ⟨Ô₂, hm₂, he₂⟩ := h₂
  rw [zwFull_eq_zwObs bd β E₁ S he₁, zwFull_eq_zwObs bd β E₂ T he₂,
    ← zwObs_split (Nc := Nc) bd β E E₁ E₂ S T hST hm₁ hm₂ hEu hEd hE₁ hE₂]
  unfold zwFull
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [he₁ U, he₂ U]

#print axioms zwFull_split

/-- **`zwFull` at a plaquette product over `D` is `zw bd β D E`**, by `rfl`. No support hypothesis
is needed: the observable is already a function of the full configuration.

DERIVED: no numeral. -/
theorem zwFull_prod_eq_zw (bd : Pq → List (Lk × Bool)) (β : ℝ) (D E : Finset Pq) :
    zwFull (Nc := Nc) bd β (fun U => ∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U) E
      = zw (Nc := Nc) bd β D E := rfl

#print axioms zwFull_prod_eq_zw

/-- **`zwFull` at the constant observable is `zw bd β ∅ E`**, the empty plaquette product being `1`.

DERIVED: the `1` is the constant observable, and the `∅` is the plaquette set whose empty product it
equals. -/
theorem zwFull_one_eq_zw_empty (bd : Pq → List (Lk × Bool)) (β : ℝ) (E : Finset Pq) :
    zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) E = zw (Nc := Nc) bd β ∅ E := by
  unfold zwFull zw
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [Finset.prod_empty]

#print axioms zwFull_one_eq_zw_empty




/-- The summand of the connected numerator's double sum at the pair `q = (E, F)` of activated
subsets: `zw {p₀, pd} E · zw ∅ F − zw {p₀} E · zw {pd} F`. The first component of the pair always
carries the observables and the second never does.

DERIVED: no numeral. -/
noncomputable def pairTerm (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (q : Finset Pq × Finset Pq) : ℝ :=
  zw (Nc := Nc) bd β {p₀, pd} q.1 * zw (Nc := Nc) bd β ∅ q.2
    - zw (Nc := Nc) bd β {p₀} q.1 * zw (Nc := Nc) bd β {pd} q.2

/-- The exchange across a separator `A`: `(E, F) ↦ (E ∩ A ∪ F \ A, F ∩ A ∪ E \ A)`, swapping the two
halves outside `A` and keeping those inside. `pairFlip_union` records that it preserves the union of
the pair, and `pairFlip_pairFlip` that it is an involution.

DERIVED: no numeral. -/
def pairFlip (A : Finset Pq) (q : Finset Pq × Finset Pq) : Finset Pq × Finset Pq :=
  ((q.1 ∩ A) ∪ (q.2 \ A), (q.2 ∩ A) ∪ (q.1 \ A))

/-- **A pair's term and its exchange's term sum to zero across a separator.** If `A` contains `p₀`,
misses `pd`, and no plaquette of `(E ∪ F ∪ {p₀, pd}) ∩ A` touches one of `(E ∪ F ∪ {p₀, pd}) \ A`,
then

    pairTerm (E, F) + pairTerm (E ∩ A ∪ F \ A, F ∩ A ∪ E \ A) = 0,

written out in `zw`s. `hne : p₀ ≠ pd` is needed for `{p₀, pd}` to split as two singletons.

The eight factorisations are all `zw_split` across the same two link sets, built as the boundary
unions of `V ∩ A` and `V \ A`, and the algebra is `ac(be − gh) + ac(hg − eb) = 0`. The closure
hypothesis is relative to `E ∪ F ∪ {p₀, pd}` only, not to the whole plaquette type. It is an identity
in `β` at any lattice size.

DERIVED: the `0` is the value of the two terms summed. -/
theorem pairTerm_add_exchange (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r)
    (h0 : p₀ ∈ A) (hd : pd ∉ A) :
    (zw (Nc := Nc) bd β {p₀, pd} E * zw (Nc := Nc) bd β ∅ F
        - zw (Nc := Nc) bd β {p₀} E * zw (Nc := Nc) bd β {pd} F)
      + (zw (Nc := Nc) bd β {p₀, pd} ((E ∩ A) ∪ (F \ A))
            * zw (Nc := Nc) bd β ∅ ((F ∩ A) ∪ (E \ A))
          - zw (Nc := Nc) bd β {p₀} ((E ∩ A) ∪ (F \ A))
            * zw (Nc := Nc) bd β {pd} ((F ∩ A) ∪ (E \ A))) = 0 := by
  classical
  set V : Finset Pq := E ∪ F ∪ {p₀, pd} with hV
  set S : Finset Lk := (V ∩ A).biUnion (linkSupp bd) with hS
  set T : Finset Lk := (V \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    exact hclosed p hp r hr ⟨l, hlp, hlr⟩
  have hinS : ∀ W : Finset Pq, W ⊆ V ∩ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    rw [hS]; exact supp_subset_biUnion bd (V ∩ A) p (hW hp) l hl
  have hinT : ∀ W : Finset Pq, W ⊆ V \ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    rw [hT]; exact supp_subset_biUnion bd (V \ A) p (hW hp) l hl
  have hEV : E ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hFV : F ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hp0V : p₀ ∈ V := by rw [hV]; simp
  have hpdV : pd ∈ V := by rw [hV]; simp
  -- the six groups, each on its own side of the split
  have hsubIn : ∀ W : Finset Pq, W ⊆ V → (W ∩ A) ⊆ V ∩ A := by
    intro W hW x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have hsubOut : ∀ W : Finset Pq, W ⊆ V → (W \ A) ⊆ V \ A := by
    intro W hW x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have g0 : ({p₀} : Finset Pq) ⊆ V ∩ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_inter.mpr ⟨hp0V, h0⟩
  have gd : ({pd} : Finset Pq) ⊆ V \ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_sdiff.mpr ⟨hpdV, hd⟩
  have gEA := hsubIn E hEV
  have gFA := hsubIn F hFV
  have gEc := hsubOut E hEV
  have gFc := hsubOut F hFV
  have gEm : (∅ : Finset Pq) ⊆ V ∩ A := Finset.empty_subset _
  have gEn : (∅ : Finset Pq) ⊆ V \ A := Finset.empty_subset _
  -- the set identities the split needs
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hDu : ({p₀, pd} : Finset Pq) = {p₀} ∪ {pd} := by ext x; simp
  have hD0 : ({p₀} : Finset Pq) = {p₀} ∪ ∅ := (Finset.union_empty _).symm
  have hDd : ({pd} : Finset Pq) = ∅ ∪ {pd} := (Finset.empty_union _).symm
  have hDz : (∅ : Finset Pq) = ∅ ∪ ∅ := (Finset.union_empty _).symm
  have hd0d : Disjoint ({p₀} : Finset Pq) {pd} := by
    simp [hne]
  -- the eight factorisations
  have e1 := zw_split (Nc := Nc) bd β {p₀, pd} {p₀} {pd} E (E ∩ A) (E \ A) S T hST hDu hEu
    hd0d (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gd) (hinT _ gEc)
  have e2 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ F (F ∩ A) (F \ A) S T hST hDz hFu
    (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  have e3 := zw_split (Nc := Nc) bd β {p₀} {p₀} ∅ E (E ∩ A) (E \ A) S T hST hD0 hEu
    (by simp) (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e4 := zw_split (Nc := Nc) bd β {pd} ∅ {pd} F (F ∩ A) (F \ A) S T hST hDd hFu
    (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gd) (hinT _ gFc)
  have e5 := zw_split (Nc := Nc) bd β {p₀, pd} {p₀} {pd} ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A)
    S T hST hDu rfl hd0d (hIO E F) (hinS _ g0) (hinS _ gEA) (hinT _ gd) (hinT _ gFc)
  have e6 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A)
    S T hST hDz rfl (by simp) (hIO F E) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gEc)
  have e7 := zw_split (Nc := Nc) bd β {p₀} {p₀} ∅ ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A)
    S T hST hD0 rfl (by simp) (hIO E F) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gFc)
  have e8 := zw_split (Nc := Nc) bd β {pd} ∅ {pd} ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A)
    S T hST hDd rfl (by simp) (hIO F E) (hinS _ gEm) (hinS _ gFA) (hinT _ gd) (hinT _ gEc)
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  ring

#print axioms pairTerm_add_exchange

/-- **The exchange cancels for observables carried on two finsets of plaquettes.**
`pairTerm_add_exchange` with `{p₀, pd}` replaced by `Ao ∪ Bo`, `{p₀}` by `Ao` and `{pd}` by `Bo`.
`zw_split` is already general in the observable finsets, so the eight factorisations are unchanged;
what the singletons carried becomes `Ao ⊆ A`, `Disjoint Bo A` and `Disjoint Ao Bo`. The closure
hypothesis is relative to `E ∪ F ∪ (Ao ∪ Bo)`.

DERIVED: the `0` is the value of the pair's term and its exchange's term summed. -/
theorem zw_add_exchange_of_finsets (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq)
    (hod : Disjoint Ao Bo) (β : ℝ) (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A, ∀ r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A,
      ¬ Touch bd p r)
    (h0 : Ao ⊆ A) (hd : Disjoint Bo A) :
    (zw (Nc := Nc) bd β (Ao ∪ Bo) E * zw (Nc := Nc) bd β ∅ F
        - zw (Nc := Nc) bd β Ao E * zw (Nc := Nc) bd β Bo F)
      + (zw (Nc := Nc) bd β (Ao ∪ Bo) ((E ∩ A) ∪ (F \ A))
            * zw (Nc := Nc) bd β ∅ ((F ∩ A) ∪ (E \ A))
          - zw (Nc := Nc) bd β Ao ((E ∩ A) ∪ (F \ A))
            * zw (Nc := Nc) bd β Bo ((F ∩ A) ∪ (E \ A))) = 0 := by
  classical
  set V : Finset Pq := E ∪ F ∪ (Ao ∪ Bo) with hV
  set S : Finset Lk := (V ∩ A).biUnion (linkSupp bd) with hS
  set T : Finset Lk := (V \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    exact hclosed p hp r hr ⟨l, hlp, hlr⟩
  have hinS : ∀ W : Finset Pq, W ⊆ V ∩ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    rw [hS]; exact supp_subset_biUnion bd (V ∩ A) p (hW hp) l hl
  have hinT : ∀ W : Finset Pq, W ⊆ V \ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    rw [hT]; exact supp_subset_biUnion bd (V \ A) p (hW hp) l hl
  have hEV : E ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hFV : F ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hAoV : Ao ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hBoV : Bo ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hsubIn : ∀ W : Finset Pq, W ⊆ V → (W ∩ A) ⊆ V ∩ A := by
    intro W hW x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have hsubOut : ∀ W : Finset Pq, W ⊆ V → (W \ A) ⊆ V \ A := by
    intro W hW x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have g0 : Ao ⊆ V ∩ A := fun x hx => Finset.mem_inter.mpr ⟨hAoV hx, h0 hx⟩
  have gd : Bo ⊆ V \ A := fun x hx =>
    Finset.mem_sdiff.mpr ⟨hBoV hx, Finset.disjoint_left.mp hd hx⟩
  have gEA := hsubIn E hEV
  have gFA := hsubIn F hFV
  have gEc := hsubOut E hEV
  have gFc := hsubOut F hFV
  have gEm : (∅ : Finset Pq) ⊆ V ∩ A := Finset.empty_subset _
  have gEn : (∅ : Finset Pq) ⊆ V \ A := Finset.empty_subset _
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hDu : Ao ∪ Bo = Ao ∪ Bo := rfl
  have hD0 : Ao = Ao ∪ ∅ := (Finset.union_empty _).symm
  have hDd : Bo = ∅ ∪ Bo := (Finset.empty_union _).symm
  have hDz : (∅ : Finset Pq) = ∅ ∪ ∅ := (Finset.union_empty _).symm
  have e1 := zw_split (Nc := Nc) bd β (Ao ∪ Bo) Ao Bo E (E ∩ A) (E \ A) S T hST hDu hEu
    hod (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gd) (hinT _ gEc)
  have e2 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ F (F ∩ A) (F \ A) S T hST hDz hFu
    (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  have e3 := zw_split (Nc := Nc) bd β Ao Ao ∅ E (E ∩ A) (E \ A) S T hST hD0 hEu
    (by simp) (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e4 := zw_split (Nc := Nc) bd β Bo ∅ Bo F (F ∩ A) (F \ A) S T hST hDd hFu
    (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gd) (hinT _ gFc)
  have e5 := zw_split (Nc := Nc) bd β (Ao ∪ Bo) Ao Bo ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A)
    S T hST hDu rfl hod (hIO E F) (hinS _ g0) (hinS _ gEA) (hinT _ gd) (hinT _ gFc)
  have e6 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A)
    S T hST hDz rfl (by simp) (hIO F E) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gEc)
  have e7 := zw_split (Nc := Nc) bd β Ao Ao ∅ ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A)
    S T hST hD0 rfl (by simp) (hIO E F) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gFc)
  have e8 := zw_split (Nc := Nc) bd β Bo ∅ Bo ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A)
    S T hST hDd rfl (by simp) (hIO F E) (hinS _ gEm) (hinS _ gFA) (hinT _ gd) (hinT _ gEc)
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  ring

#print axioms zw_add_exchange_of_finsets

/-- The expansion's summand with the two observables carried on finsets of plaquettes: `pairTerm`
with `{p₀, pd}` replaced by `Ao ∪ Bo`, `{p₀}` by `Ao` and `{pd}` by `Bo`. Nothing here requires `Ao`
and `Bo` to be disjoint; the lemmas that need it take it as a hypothesis.

DERIVED: no numeral. -/
noncomputable def pairTermF (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq) (β : ℝ)
    (q : Finset Pq × Finset Pq) : ℝ :=
  zw (Nc := Nc) bd β (Ao ∪ Bo) q.1 * zw (Nc := Nc) bd β ∅ q.2
    - zw (Nc := Nc) bd β Ao q.1 * zw (Nc := Nc) bd β Bo q.2

/-- **`pairTermF (E, F) + pairTermF (pairFlip A (E, F)) = 0`**, under the same hypotheses as
`zw_add_exchange_of_finsets`: `Disjoint Ao Bo`, `Ao ⊆ A`, `Disjoint Bo A`, and no touch between
`(E ∪ F ∪ (Ao ∪ Bo)) ∩ A` and `(E ∪ F ∪ (Ao ∪ Bo)) \ A`. This is the shape the summation over an
involution consumes.

DERIVED: the `0` is the value of the two terms summed. -/
theorem pairTermF_add_pairFlip (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq)
    (hod : Disjoint Ao Bo) (β : ℝ) (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A, ∀ r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A,
      ¬ Touch bd p r)
    (h0 : Ao ⊆ A) (hd : Disjoint Bo A) :
    pairTermF (Nc := Nc) bd Ao Bo β (E, F)
      + pairTermF (Nc := Nc) bd Ao Bo β (pairFlip A (E, F)) = 0 := by
  simp only [pairTermF, pairFlip]
  exact zw_add_exchange_of_finsets bd Ao Bo hod β E F A hclosed h0 hd

#print axioms pairTermF_add_pairFlip

/-- **The summand is its restriction to `A` times the two outside weights.** With both observable
finsets inside `A` (`Ao ∪ Bo ⊆ A`) and no touch across `A` inside `E ∪ F ∪ (Ao ∪ Bo)`,

    pairTermF (E, F) = pairTermF (E ∩ A, F ∩ A) · (zw ∅ (E \ A) · zw ∅ (F \ A)).

The finset counterpart of `pairTerm_eq_core_mul_outside`, where `p₀ ∈ A` and `pd ∈ A` become the
single hypothesis `Ao ∪ Bo ⊆ A`. Note `hd : Disjoint Bo A` of the exchange lemma is replaced here by
`Bo ⊆ A`: this statement puts both observable groups on the same side.

DERIVED: no numeral. -/
theorem pairTermF_eq_core_mul_outside (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A, ∀ r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A,
      ¬ Touch bd p r)
    (hobs : Ao ∪ Bo ⊆ A) :
    pairTermF (Nc := Nc) bd Ao Bo β (E, F)
      = pairTermF (Nc := Nc) bd Ao Bo β (E ∩ A, F ∩ A)
        * (zw (Nc := Nc) bd β ∅ (E \ A) * zw (Nc := Nc) bd β ∅ (F \ A)) := by
  classical
  set V : Finset Pq := E ∪ F ∪ (Ao ∪ Bo) with hV
  set S : Finset Lk := (V ∩ A).biUnion (linkSupp bd) with hS
  set T : Finset Lk := (V \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    exact hclosed p hp r hr ⟨l, hlp, hlr⟩
  have hinS : ∀ W : Finset Pq, W ⊆ V ∩ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    rw [hS]; exact supp_subset_biUnion bd (V ∩ A) p (hW hp) l hl
  have hinT : ∀ W : Finset Pq, W ⊆ V \ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    rw [hT]; exact supp_subset_biUnion bd (V \ A) p (hW hp) l hl
  have hEV : E ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hFV : F ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hObsV : Ao ∪ Bo ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hsubIn : ∀ W : Finset Pq, W ⊆ V → (W ∩ A) ⊆ V ∩ A := by
    intro W hW x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have hsubOut : ∀ W : Finset Pq, W ⊆ V → (W \ A) ⊆ V \ A := by
    intro W hW x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have gcore : Ao ∪ Bo ⊆ V ∩ A := fun x hx => Finset.mem_inter.mpr ⟨hObsV hx, hobs hx⟩
  have g0 : Ao ⊆ V ∩ A := fun x hx => gcore (Finset.mem_union_left _ hx)
  have gd : Bo ⊆ V ∩ A := fun x hx => gcore (Finset.mem_union_right _ hx)
  have gEA := hsubIn E hEV
  have gFA := hsubIn F hFV
  have gEc := hsubOut E hEV
  have gFc := hsubOut F hFV
  have gEm : (∅ : Finset Pq) ⊆ V ∩ A := Finset.empty_subset _
  have gEn : (∅ : Finset Pq) ⊆ V \ A := Finset.empty_subset _
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hDr : ∀ W : Finset Pq, W = W ∪ ∅ := fun W => (Finset.union_empty W).symm
  have e1 := zw_split (Nc := Nc) bd β (Ao ∪ Bo) (Ao ∪ Bo) ∅ E (E ∩ A) (E \ A) S T hST
    (hDr _) hEu (by simp) (hIO E E) (hinS _ gcore) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e2 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ F (F ∩ A) (F \ A) S T hST
    (hDr _) hFu (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  have e3 := zw_split (Nc := Nc) bd β Ao Ao ∅ E (E ∩ A) (E \ A) S T hST
    (hDr _) hEu (by simp) (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e4 := zw_split (Nc := Nc) bd β Bo Bo ∅ F (F ∩ A) (F \ A) S T hST
    (hDr _) hFu (by simp) (hIO F F) (hinS _ gd) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  simp only [pairTermF]
  rw [e1, e2, e3, e4]
  ring

#print axioms pairTermF_eq_core_mul_outside

/-- The connected numerator's summand at two arbitrary observables of full configurations:
`zwFull (O₁·O₂) q.1 · zwFull 1 q.2 − zwFull O₁ q.1 · zwFull O₂ q.2`. `pairTermF`'s four terms with
the two plaquette products replaced by `O₁` and `O₂`; `pairTermObs_eq_pairTermF` records the
reduction. No measurability or locality is asked for here.

DERIVED: the `1` is the constant observable standing where `pairTermF` has `zw` at the empty
plaquette set, the two being equal by `zwFull_one_eq_zw_empty`. -/
noncomputable def pairTermObs (bd : Pq → List (Lk × Bool))
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (β : ℝ)
    (q : Finset Pq × Finset Pq) : ℝ :=
  zwFull (Nc := Nc) bd β (fun U => O₁ U * O₂ U) q.1 * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) q.2
    - zwFull (Nc := Nc) bd β O₁ q.1 * zwFull (Nc := Nc) bd β O₂ q.2

/-- **`pairTermObs` at the two plaquette products of `Ao` and `Bo` is `pairTermF bd Ao Bo β q`**,
given `Disjoint Ao Bo`.

The disjointness is what turns `∏ Ao · ∏ Bo` into `∏ (Ao ∪ Bo)` under `Finset.prod_union`; it is the
same hypothesis `pairTermF_add_pairFlip` carries. So the `…F` family is the plaquette case of the
observable one.

DERIVED: no numeral. -/
theorem pairTermObs_eq_pairTermF (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq)
    (hod : Disjoint Ao Bo) (β : ℝ) (q : Finset Pq × Finset Pq) :
    pairTermObs (Nc := Nc) bd
        (fun U => ∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
        (fun U => ∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U) β q
      = pairTermF (Nc := Nc) bd Ao Bo β q := by
  classical
  unfold pairTermObs pairTermF
  rw [zwFull_one_eq_zw_empty bd β q.2, zwFull_prod_eq_zw bd β Ao q.1,
    zwFull_prod_eq_zw bd β Bo q.2]
  congr 1
  congr 1
  unfold zwFull zw
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [Finset.prod_union hod]

#print axioms pairTermObs_eq_pairTermF

/-- **`zwFull` depends on its observable only through its values**: pointwise equality of `O` and
`O'` at every configuration gives equal terms. Pointwise, not almost everywhere.

DERIVED: no numeral. -/
theorem zwFull_congr (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O O' : (Lk → MassGap.SUN.SU Nc) → ℝ} (h : ∀ U, O U = O' U) (E : Finset Pq) :
    zwFull (Nc := Nc) bd β O E = zwFull (Nc := Nc) bd β O' E := by
  unfold zwFull
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  -- `simp only`, not `rw`: `integral_congr_ae` leaves both sides as beta-redexes.
  simp only [h U]

#print axioms zwFull_congr

/-- **The constant observable `fun _ => 1` is `LocalOnLinks S` for every `S`**, the witness being the
constant on the restriction. It reads no link, so every `S` serves.

DERIVED: the `1` is the constant observable's value. -/
theorem localOnLinks_one (S : Finset Lk) :
    LocalOnLinks (Nc := Nc) S (fun _ => (1 : ℝ)) :=
  ⟨fun _ => (1 : ℝ), measurable_const, fun _ => rfl⟩

#print axioms localOnLinks_one

/-- **A pair and its flip across `A` sum to zero, at two arbitrary observables.**
`pairTermObs bd O₁ O₂ β (E, F) + pairTermObs bd O₁ O₂ β (pairFlip A (E, F)) = 0`, given
`LocalOnLinks S O₁`, `LocalOnLinks T O₂`, `Disjoint S T`, and the two support conditions: the
plaquettes of `(E ∪ F) ∩ A` draw on `S` and those of `(E ∪ F) \ A` draw on `T`.

`zw_add_exchange_of_finsets` with the plaquette products replaced by two observables, each reading
one side of the split. The link blocks differ in how they arrive: there they are built inside the
proof as the boundary unions of `V ∩ A` and `V \ A`, with disjointness derived from the closure
hypothesis, which works because the observable is itself made of plaquettes of `V`. An arbitrary
observable's support need not lie in `V`, so here `S` and `T` are parameters and the caller supplies
`hST` along with the two locality facts.

The algebra is eight `zwFull_split`s and `a·c·(b·d − e·f) + a·c·(f·e − d·b) = 0`.

DERIVED: the `0` is the value of the pair's term and its flip's term summed. -/
theorem zwFull_add_exchange (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (E F A : Finset Pq) (S T : Finset Lk)
    (hST : Disjoint S T)
    (h₁ : LocalOnLinks (Nc := Nc) S O₁) (h₂ : LocalOnLinks (Nc := Nc) T O₂)
    (hinS : ∀ p ∈ (E ∪ F) ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hinT : ∀ p ∈ (E ∪ F) \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    pairTermObs (Nc := Nc) bd O₁ O₂ β (E, F)
      + pairTermObs (Nc := Nc) bd O₁ O₂ β (pairFlip A (E, F)) = 0 := by
  classical
  -- the four plaquette groups and where their links live
  have hEA : ∀ p ∈ E ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro p hp
    rw [Finset.mem_inter] at hp
    exact hinS p (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hp.1, hp.2⟩)
  have hFA : ∀ p ∈ F ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro p hp
    rw [Finset.mem_inter] at hp
    exact hinS p (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hp.1, hp.2⟩)
  have hEc : ∀ p ∈ E \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    exact hinT p (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hp.1, hp.2⟩)
  have hFc : ∀ p ∈ F \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    exact hinT p (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hp.1, hp.2⟩)
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by ext x; by_cases hx : x ∈ A <;> simp [hx]
  -- the eight splits, in the same order as the plaquette proof
  have e1 := zwFull_split (Nc := Nc) bd β E (E ∩ A) (E \ A) S T hST h₁ h₂ hEu (hIO E E) hEA hEc
  have e2' := zwFull_split (Nc := Nc) bd β F (F ∩ A) (F \ A) S T hST (localOnLinks_one (Nc := Nc) S) (localOnLinks_one (Nc := Nc) T) hFu
    (hIO F F) hFA hFc
  have e3' := zwFull_split (Nc := Nc) bd β E (E ∩ A) (E \ A) S T hST h₁ (localOnLinks_one (Nc := Nc) T) hEu
    (hIO E E) hEA hEc
  have e4' := zwFull_split (Nc := Nc) bd β F (F ∩ A) (F \ A) S T hST (localOnLinks_one (Nc := Nc) S) h₂ hFu
    (hIO F F) hFA hFc
  have e5 := zwFull_split (Nc := Nc) bd β ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A) S T hST h₁ h₂
    rfl (hIO E F) hEA hFc
  have e6' := zwFull_split (Nc := Nc) bd β ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A) S T hST
    (localOnLinks_one (Nc := Nc) S) (localOnLinks_one (Nc := Nc) T) rfl (hIO F E) hFA hEc
  have e7' := zwFull_split (Nc := Nc) bd β ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A) S T hST h₁
    (localOnLinks_one (Nc := Nc) T) rfl (hIO E F) hEA hFc
  have e8' := zwFull_split (Nc := Nc) bd β ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A) S T hST
    (localOnLinks_one (Nc := Nc) S) h₂ rfl (hIO F E) hFA hEc
  -- the constant-observable products collapse
  rw [zwFull_congr (Nc := Nc) bd β (fun U => one_mul (1 : ℝ)) F] at e2'
  rw [zwFull_congr (Nc := Nc) bd β (fun U => mul_one (O₁ U)) E] at e3'
  rw [zwFull_congr (Nc := Nc) bd β (fun U => one_mul (O₂ U)) F] at e4'
  rw [zwFull_congr (Nc := Nc) bd β (fun U => one_mul (1 : ℝ)) ((F ∩ A) ∪ (E \ A))] at e6'
  rw [zwFull_congr (Nc := Nc) bd β (fun U => mul_one (O₁ U)) ((E ∩ A) ∪ (F \ A))] at e7'
  rw [zwFull_congr (Nc := Nc) bd β (fun U => one_mul (O₂ U)) ((F ∩ A) ∪ (E \ A))] at e8'
  unfold pairTermObs pairFlip
  simp only
  rw [e1, e2', e3', e4', e5, e6', e7', e8']
  ring

#print axioms zwFull_add_exchange




/-- **`pairTerm (E, F) + pairTerm (pairFlip A (E, F)) = 0`**, under the same hypotheses as
`pairTerm_add_exchange`: `p₀ ≠ pd`, `p₀ ∈ A`, `pd ∉ A`, and no touch between
`(E ∪ F ∪ {p₀, pd}) ∩ A` and `(E ∪ F ∪ {p₀, pd}) \ A`. This is the shape the summation over an
involution consumes.

DERIVED: the `0` is the value of the two terms summed. -/
theorem pairTerm_add_pairFlip (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r)
    (h0 : p₀ ∈ A) (hd : pd ∉ A) :
    pairTerm (Nc := Nc) bd p₀ pd β (E, F)
      + pairTerm (Nc := Nc) bd p₀ pd β (pairFlip A (E, F)) = 0 := by
  simp only [pairTerm, pairFlip]
  exact pairTerm_add_exchange bd p₀ pd hne β E F A hclosed h0 hd

#print axioms pairTerm_add_pairFlip

/-! ### The separator a pair supplies by itself

`pairTerm_add_exchange` takes a separator `A`, and summing over an involution needs one chosen as a
function of the pair. `compOf` is that choice: `p₀`'s touch-reachable component inside the pair's own
union. It is touch-closed there by construction (`compOf_closed`), it contains `p₀`
(`self_mem_compOf`), and it misses `pd` exactly when `p₀` does not reach `pd` inside the union. -/

/-- Touch-reachability inside a plaquette set: the reflexive-transitive closure of touching, with
both endpoints of every step required to lie in `V`.

DERIVED: no numeral. -/
def Reach (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a b : Pq) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ V ∧ y ∈ V ∧ Touch bd x y) a b

open scoped Classical in
/-- `a`'s touch-reachable component inside `V`: the plaquettes of `V` that `Reach bd V a` holds of.
`a` itself belongs only when `a ∈ V`.

DERIVED: no numeral. -/
noncomputable def compOf (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) : Finset Pq :=
  V.filter (fun p => Reach bd V a p)

open scoped Classical in
theorem mem_compOf {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {a p : Pq} :
    p ∈ compOf bd V a ↔ p ∈ V ∧ Reach bd V a p := by
  unfold compOf; exact Finset.mem_filter

open scoped Classical in
theorem self_mem_compOf {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {a : Pq} (ha : a ∈ V) :
    a ∈ compOf bd V a :=
  mem_compOf.mpr ⟨ha, Relation.ReflTransGen.refl⟩

open scoped Classical in
/-- **A component is touch-closed inside its own set.** No plaquette of `V ∩ compOf bd V a` touches
one of `V \ compOf bd V a`: such a touch would extend the reach chain and put the far end back in the
component. This is the closure hypothesis `pairTerm_add_exchange` takes, here produced rather than
assumed. The closure is relative to `V`; a touch to a plaquette outside `V` is not excluded.

DERIVED: no numeral. -/
theorem compOf_closed (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) :
    ∀ p ∈ V ∩ compOf bd V a, ∀ r ∈ V \ compOf bd V a, ¬ Touch bd p r := by
  intro p hp r hr ht
  rw [Finset.mem_inter] at hp
  rw [Finset.mem_sdiff] at hr
  exact hr.2 (mem_compOf.mpr ⟨hr.1, (mem_compOf.mp hp.2).2.tail ⟨hp.1, hr.1, ht⟩⟩)

#print axioms compOf_closed

open scoped Classical in
/-- The plaquettes of `V` reachable inside `V` from some member of `A`: the union of the components
of `V` that meet `A`. `compsMeet_singleton` records that `compOf` is the case `A = {a}`.

`pairTermF_add_pairFlip` takes a touch-closed `S` with `Ao ⊆ S` and `Disjoint Bo S`. When `Ao` is a
single plaquette its own component serves; when `Ao` spans several components it does not, since it
holds one member of `Ao` and misses the rest. This set contains all of `A` that lies in `V`
(`subset_compsMeet`), is touch-closed in `V` (`compsMeet_closed`), sits inside every touch-closed
superset of `A ∩ V` (`compsMeet_minimal`), and misses `B` exactly when no component of `V` meets both
(`disjoint_compsMeet_iff`).

DERIVED: no numeral. -/
noncomputable def compsMeet (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (A : Finset Pq) :
    Finset Pq :=
  V.filter (fun p => ∃ a ∈ A, Reach bd V a p)

open scoped Classical in
/-- **`p ∈ compsMeet bd V A ↔ p ∈ V ∧ ∃ a ∈ A, Reach bd V a p`**, the defining filter unfolded.

DERIVED: no numeral. -/
theorem mem_compsMeet {bd : Pq → List (Lk × Bool)} {V A : Finset Pq} {p : Pq} :
    p ∈ compsMeet bd V A ↔ p ∈ V ∧ ∃ a ∈ A, Reach bd V a p := by
  unfold compsMeet; exact Finset.mem_filter

#print axioms mem_compsMeet

open scoped Classical in
/-- **`compsMeet bd V A ⊆ V`**, being a filter of `V`. Members of `A` outside `V` are not included.

DERIVED: no numeral. -/
theorem compsMeet_subset (bd : Pq → List (Lk × Bool)) (V A : Finset Pq) :
    compsMeet bd V A ⊆ V :=
  Finset.filter_subset _ _

#print axioms compsMeet_subset

open scoped Classical in
/-- **`A ∩ V ⊆ compsMeet bd V A`**: each member of `A` inside `V` reaches itself, by reflexivity of
`Reach`. The intersection with `V` is needed — the statement is not `A ⊆ compsMeet bd V A`.

DERIVED: no numeral. -/
theorem subset_compsMeet (bd : Pq → List (Lk × Bool)) (V A : Finset Pq) :
    A ∩ V ⊆ compsMeet bd V A := by
  intro a ha
  rw [Finset.mem_inter] at ha
  exact mem_compsMeet.mpr ⟨ha.2, a, ha.1, Relation.ReflTransGen.refl⟩

#print axioms subset_compsMeet

open scoped Classical in
/-- **`compsMeet bd V A` is touch-closed in `V`**: no plaquette of `V ∩ compsMeet bd V A` touches one
of `V \ compsMeet bd V A`. Same one-step argument as `compOf_closed` — a touch out of the set extends
the chain from whichever `a ∈ A` reached `p`, putting the far end back in. This is the closure
hypothesis `pairTermF_add_pairFlip` takes.

DERIVED: no numeral. -/
theorem compsMeet_closed (bd : Pq → List (Lk × Bool)) (V A : Finset Pq) :
    ∀ p ∈ V ∩ compsMeet bd V A, ∀ r ∈ V \ compsMeet bd V A, ¬ Touch bd p r := by
  intro p hp r hr ht
  rw [Finset.mem_inter] at hp
  rw [Finset.mem_sdiff] at hr
  obtain ⟨a, haA, hap⟩ := (mem_compsMeet.mp hp.2).2
  exact hr.2 (mem_compsMeet.mpr ⟨hr.1, a, haA, hap.tail ⟨hp.1, hr.1, ht⟩⟩)

#print axioms compsMeet_closed

open scoped Classical in
/-- **`compsMeet bd V A` is the smallest touch-closed set containing `A ∩ V`.** Any `S` that is
touch-closed in `V` and contains `A ∩ V` contains it. The induction runs along the reach chain: the
first vertex lies in `A ∩ V ⊆ S`, and a chain step leaving `S` would be a touch from `V ∩ S` to
`V \ S`, which the closure hypothesis forbids. `S` is not required to be a subset of `V`.

With this, a touch-closed `S ⊇ A ∩ V` missing `B` forces `compsMeet bd V A` to miss `B` as well, so
`disjoint_compsMeet_iff` characterises when any separator at all exists, not just this one.

DERIVED: no numeral. -/
theorem compsMeet_minimal (bd : Pq → List (Lk × Bool)) (V A S : Finset Pq)
    (hclosed : ∀ p ∈ V ∩ S, ∀ r ∈ V \ S, ¬ Touch bd p r)
    (hA : A ∩ V ⊆ S) :
    compsMeet bd V A ⊆ S := by
  intro x hx
  obtain ⟨hxV, a, haA, hreach⟩ := mem_compsMeet.mp hx
  have key : ∀ y, Relation.ReflTransGen
      (fun u v => u ∈ V ∧ v ∈ V ∧ Touch bd u v) a y → y ∈ V → y ∈ S := by
    intro y hy
    induction hy with
    | refl => intro haV; exact hA (Finset.mem_inter.mpr ⟨haA, haV⟩)
    | @tail b c _hab hstep ih =>
        intro _
        obtain ⟨hbV, hcV, ht⟩ := hstep
        by_contra hcS
        exact hclosed b (Finset.mem_inter.mpr ⟨hbV, ih hbV⟩) c
          (Finset.mem_sdiff.mpr ⟨hcV, hcS⟩) ht
  exact key x hreach hxV

#print axioms compsMeet_minimal

open scoped Classical in
/-- **`compsMeet bd V {a} = compOf bd V a`.** Every lemma about a single plaquette's component is
therefore the singleton instance of the corresponding `compsMeet` lemma. Note `a ∈ V` is not
assumed: both sides are empty when it fails.

DERIVED: no numeral. -/
theorem compsMeet_singleton (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) :
    compsMeet bd V {a} = compOf bd V a := by
  ext p
  rw [mem_compsMeet, mem_compOf]
  constructor
  · rintro ⟨hpV, a', ha', hr⟩
    rw [Finset.mem_singleton] at ha'
    subst ha'
    exact ⟨hpV, hr⟩
  · rintro ⟨hpV, hr⟩
    exact ⟨hpV, a, Finset.mem_singleton_self a, hr⟩

#print axioms compsMeet_singleton

open scoped Classical in
/-- **`compOf bd V a ⊆ compsMeet bd V A` whenever `a ∈ A`.** Replacing a single plaquette's component
by the union of the components meeting `A` only enlarges the separator.

DERIVED: no numeral. -/
theorem compOf_subset_compsMeet (bd : Pq → List (Lk × Bool)) (V A : Finset Pq) {a : Pq}
    (ha : a ∈ A) : compOf bd V a ⊆ compsMeet bd V A := by
  intro p hp
  obtain ⟨hpV, hreach⟩ := mem_compOf.mp hp
  exact mem_compsMeet.mpr ⟨hpV, a, ha, hreach⟩

#print axioms compOf_subset_compsMeet

open scoped Classical in
/-- **`Disjoint B (compsMeet bd V A) ↔ ∀ b ∈ B, ∀ a ∈ A, ¬ Reach bd V a b`**, given `B ⊆ V`. The
separator misses `B` exactly when no plaquette of `B` is touch-reachable inside `V` from any
plaquette of `A`, which is to say when no component of `V` meets both.

With `compsMeet_minimal`, this characterises when a touch-closed separator containing `A ∩ V` and
missing `B` exists at all: if any does, this one does.

The hypothesis `B ⊆ V` is used in the forward direction only.

DERIVED: no numeral. -/
theorem disjoint_compsMeet_iff (bd : Pq → List (Lk × Bool)) (V A B : Finset Pq)
    (hB : B ⊆ V) :
    Disjoint B (compsMeet bd V A) ↔ ∀ b ∈ B, ∀ a ∈ A, ¬ Reach bd V a b := by
  constructor
  · intro hd b hb a ha hr
    exact (Finset.disjoint_left.mp hd hb) (mem_compsMeet.mpr ⟨hB hb, a, ha, hr⟩)
  · intro h
    rw [Finset.disjoint_left]
    intro b hb hmem
    obtain ⟨a, ha, hr⟩ := (mem_compsMeet.mp hmem).2
    exact h b hb a ha hr

#print axioms disjoint_compsMeet_iff

open scoped Classical in
/-- **`compsMeet bd V A = compOf bd V a` when every plaquette of `A` is reachable from `a` inside
`V`.** Anything reached from some `a' ∈ A` is reached from `a` by composing the two chains, so the
union of the components meeting `A` is the single component containing `a`. Both `a ∈ A` and the
connectivity hypothesis are needed; `A ⊆ V` is not.

DERIVED: no numeral. -/
theorem compsMeet_eq_compOf_of_connected (bd : Pq → List (Lk × Bool)) (V A : Finset Pq) {a : Pq}
    (ha : a ∈ A) (hconn : ∀ p ∈ A, Reach bd V a p) :
    compsMeet bd V A = compOf bd V a := by
  refine Finset.Subset.antisymm ?_ (compOf_subset_compsMeet bd V A ha)
  intro x hx
  obtain ⟨hxV, a', ha', hr⟩ := mem_compsMeet.mp hx
  exact mem_compOf.mpr ⟨hxV, (hconn a' ha').trans hr⟩

#print axioms compsMeet_eq_compOf_of_connected

open scoped Classical in
/-- The plaquettes of `V` at least one of whose boundary links lies in `S`.

This is the seed from which a separator for an arbitrary observable is grown. `nonbridging_sum_eq_zeroF`
flips across the component of an anchor plaquette; an observable given only by a link support has no
anchor, and these are the plaquettes that meet the support instead.

DERIVED: no numeral. -/
noncomputable def plaqsMeetingLinks (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (S : Finset Lk) :
    Finset Pq :=
  V.filter (fun p => ∃ l ∈ linkSupp bd p, l ∈ S)

open scoped Classical in
/-- **`p ∈ plaqsMeetingLinks bd V S ↔ p ∈ V ∧ ∃ l ∈ linkSupp bd p, l ∈ S`**, the defining filter
unfolded.

DERIVED: no numeral. -/
theorem mem_plaqsMeetingLinks {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {S : Finset Lk}
    {p : Pq} :
    p ∈ plaqsMeetingLinks bd V S ↔ p ∈ V ∧ ∃ l ∈ linkSupp bd p, l ∈ S := by
  unfold plaqsMeetingLinks; exact Finset.mem_filter

#print axioms mem_plaqsMeetingLinks

open scoped Classical in
/-- The separator grown from a link support: `compsMeet bd V (plaqsMeetingLinks bd V S)`, the
plaquettes of `V` whose links meet `S`, closed under touching inside `V`.

It plays the part a single plaquette's component plays when the observable is a plaquette product.
At the link support of one plaquette's boundary the seed contains that plaquette, so the separator
contains its component.

DERIVED: no numeral. -/
noncomputable def sepOfLinks (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (S : Finset Lk) :
    Finset Pq :=
  compsMeet bd V (plaqsMeetingLinks bd V S)

open scoped Classical in
/-- **`sepOfLinks bd V S` is touch-closed in `V`**: `compsMeet_closed` at the seed
`plaqsMeetingLinks bd V S`.

DERIVED: no numeral. -/
theorem sepOfLinks_closed (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (S : Finset Lk) :
    ∀ p ∈ V ∩ sepOfLinks bd V S, ∀ r ∈ V \ sepOfLinks bd V S, ¬ Touch bd p r :=
  compsMeet_closed bd V (plaqsMeetingLinks bd V S)

#print axioms sepOfLinks_closed

open scoped Classical in
/-- **`sepOfLinks bd V S ⊆ V`**: `compsMeet_subset` at the seed.

DERIVED: no numeral. -/
theorem sepOfLinks_subset (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (S : Finset Lk) :
    sepOfLinks bd V S ⊆ V :=
  compsMeet_subset bd V (plaqsMeetingLinks bd V S)

#print axioms sepOfLinks_subset

open scoped Classical in
/-- **A plaquette of `V` outside `sepOfLinks bd V S` has no link in `S`.** The separator contains the
whole seed, which is every plaquette of `V` meeting `S`, so a plaquette left outside meets `S`
nowhere. This is what puts the observable's own support on one side of the link split.

DERIVED: no numeral. -/
theorem no_link_of_not_mem_sepOfLinks (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (S : Finset Lk)
    {p : Pq} (hp : p ∈ V) (hnot : p ∉ sepOfLinks bd V S) :
    ∀ l ∈ linkSupp bd p, l ∉ S := by
  intro l hl hlS
  refine hnot ?_
  refine subset_compsMeet bd V (plaqsMeetingLinks bd V S) ?_
  rw [Finset.mem_inter]
  exact ⟨mem_plaqsMeetingLinks.mpr ⟨hp, l, hl, hlS⟩, hp⟩

#print axioms no_link_of_not_mem_sepOfLinks

open scoped Classical in
/-- One side's link block: `S ∪ W.biUnion (linkSupp bd)`, an observable's own link support together
with the links of the plaquettes `W` on that side. This is what `zwFull_add_exchange` takes for its
two link sets, since both the observable and that side's activated plaquettes must read only it.

DERIVED: no numeral. -/
noncomputable def linkBlock (bd : Pq → List (Lk × Bool)) (W : Finset Pq) (S : Finset Lk) :
    Finset Lk :=
  S ∪ W.biUnion (linkSupp bd)

open scoped Classical in
/-- **`l ∈ linkBlock bd W S ↔ l ∈ S ∨ ∃ p ∈ W, l ∈ linkSupp bd p`**, the union unfolded.

DERIVED: no numeral. -/
theorem mem_linkBlock {bd : Pq → List (Lk × Bool)} {W : Finset Pq} {S : Finset Lk} {l : Lk} :
    l ∈ linkBlock bd W S ↔ l ∈ S ∨ ∃ p ∈ W, l ∈ linkSupp bd p := by
  unfold linkBlock
  rw [Finset.mem_union, Finset.mem_biUnion]

#print axioms mem_linkBlock

open scoped Classical in
/-- **The two link blocks either side of `sepOfLinks bd V Sa` are disjoint**, given that `Sa` and
`Sb` are disjoint and that no plaquette of `V ∩ sepOfLinks bd V Sa` carries a link of `Sb`.

A link in both blocks falls into four cases, three of which the construction already rules out:

* in both `Sa` and `Sb` — excluded by `hab`;
* in `Sa` and on a plaquette outside the separator — excluded by `no_link_of_not_mem_sepOfLinks`,
  since the separator contains every plaquette of `V` meeting `Sa`;
* on plaquettes on both sides — excluded by `sepOfLinks_closed`, two plaquettes sharing a link being
  a touch.

The fourth is `hbridge`, which is a hypothesis: no plaquette of the separator carries a link of
`Sb`. That is the non-bridging condition stated at the level of links.

DERIVED: no numeral. -/
theorem disjoint_linkBlocks (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (Sa Sb : Finset Lk)
    (hab : Disjoint Sa Sb)
    (hbridge : ∀ p ∈ V ∩ sepOfLinks bd V Sa, ∀ l ∈ linkSupp bd p, l ∉ Sb) :
    Disjoint (linkBlock bd (V ∩ sepOfLinks bd V Sa) Sa)
      (linkBlock bd (V \ sepOfLinks bd V Sa) Sb) := by
  classical
  rw [Finset.disjoint_left]
  intro l hl hl'
  rcases mem_linkBlock.mp hl with hA | ⟨p, hp, hlp⟩
  · rcases mem_linkBlock.mp hl' with hB | ⟨r, hr, hlr⟩
    · exact Finset.disjoint_left.mp hab hA hB
    · rw [Finset.mem_sdiff] at hr
      exact no_link_of_not_mem_sepOfLinks bd V Sa hr.1 hr.2 l hlr hA
  · rcases mem_linkBlock.mp hl' with hB | ⟨r, hr, hlr⟩
    · exact hbridge p hp l hlp hB
    · exact sepOfLinks_closed bd V Sa p hp r hr ⟨l, hlp, hlr⟩

#print axioms disjoint_linkBlocks

open scoped Classical in
/-- **`LocalOnLinks` is monotone in the link set**: `S ⊆ S'` and `LocalOnLinks S O` give
`LocalOnLinks S' O`. The witness is the old one composed with the inclusion of coordinates.

Used because each observable is local on its own support while `zwFull_add_exchange` needs it local
on the whole block, which also carries that side's plaquette links.

DERIVED: no numeral. -/
theorem localOnLinks_mono (bd : Pq → List (Lk × Bool)) {S S' : Finset Lk} (hSS : S ⊆ S')
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} (h : LocalOnLinks (Nc := Nc) S O) :
    LocalOnLinks (Nc := Nc) S' O := by
  obtain ⟨Ô, hm, he⟩ := h
  refine ⟨fun v => Ô (fun i : S => v ⟨i.val, hSS i.2⟩), ?_, fun U => ?_⟩
  · exact hm.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  · exact he U

#print axioms localOnLinks_mono

open scoped Classical in
/-- **A pair and its flip sum to zero, for two observables on disjoint link supports.** With
`Disjoint Sa Sb`, `LocalOnLinks Sa O₁`, `LocalOnLinks Sb O₂`, and no plaquette of
`(E ∪ F) ∩ sepOfLinks bd (E ∪ F) Sa` carrying a link of `Sb`,

    pairTermObs bd O₁ O₂ β (E, F) + pairTermObs bd O₁ O₂ β (pairFlip A (E, F)) = 0,

where `A = sepOfLinks bd (E ∪ F) Sa`.

The observable counterpart of `pairTermF_add_pairFlip`, with no anchor plaquette. The separator is
grown from `Sa` inside the pair's union, and the two link blocks are each observable's support
together with its side's plaquette links. `hbridge` is the only hypothesis that concerns the
activated plaquettes; `disjoint_linkBlocks` disposes of the other three ways the blocks could meet.

DERIVED: the `0` is the value of the pair's term and its flip's term summed, inherited from
`zwFull_add_exchange`. -/
theorem pairTermObs_add_flip_of_no_bridge (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (E F : Finset Pq) (Sa Sb : Finset Lk)
    (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    (hbridge : ∀ p ∈ (E ∪ F) ∩ sepOfLinks bd (E ∪ F) Sa, ∀ l ∈ linkSupp bd p, l ∉ Sb) :
    pairTermObs (Nc := Nc) bd O₁ O₂ β (E, F)
      + pairTermObs (Nc := Nc) bd O₁ O₂ β
          (pairFlip (sepOfLinks bd (E ∪ F) Sa) (E, F)) = 0 := by
  classical
  set V : Finset Pq := E ∪ F with hV
  set A : Finset Pq := sepOfLinks bd V Sa with hA
  refine zwFull_add_exchange (Nc := Nc) bd β O₁ O₂ E F A
    (linkBlock bd (V ∩ A) Sa) (linkBlock bd (V \ A) Sb)
    (disjoint_linkBlocks bd V Sa Sb hab hbridge)
    (localOnLinks_mono bd (fun l hl => mem_linkBlock.mpr (Or.inl hl)) h₁)
    (localOnLinks_mono bd (fun l hl => mem_linkBlock.mpr (Or.inl hl)) h₂)
    ?_ ?_
  · intro p hp l hl
    exact mem_linkBlock.mpr (Or.inr ⟨p, hp, List.mem_toFinset.mpr hl⟩)
  · intro p hp l hl
    exact mem_linkBlock.mpr (Or.inr ⟨p, hp, List.mem_toFinset.mpr hl⟩)

#print axioms pairTermObs_add_flip_of_no_bridge




open scoped Classical in
/-- **`Disjoint B (compOf bd V a) ↔ ∀ b ∈ B, ∀ a' ∈ A, ¬ Reach bd V a' b`**, when `a ∈ A`, `B ⊆ V`
and every plaquette of `A` is reachable from `a` inside `V`.

`disjoint_compsMeet_iff` composed with `compsMeet_eq_compOf_of_connected`. The right-hand side
quantifies over every `a' ∈ A`, so it is the multi-plaquette condition "no component of `V` meets
both", while the left-hand side mentions only the component of the single plaquette `a`. The
connectivity of `A` inside `V` is what makes the two agree; without it the equivalence is stated for
`compsMeet bd V A` instead.

DERIVED: no numeral. -/
theorem disjoint_compOf_iff_of_connected (bd : Pq → List (Lk × Bool)) (V A B : Finset Pq) {a : Pq}
    (ha : a ∈ A) (hB : B ⊆ V) (hconn : ∀ p ∈ A, Reach bd V a p) :
    Disjoint B (compOf bd V a) ↔ ∀ b ∈ B, ∀ a' ∈ A, ¬ Reach bd V a' b := by
  rw [← compsMeet_eq_compOf_of_connected bd V A ha hconn]
  exact disjoint_compsMeet_iff bd V A B hB

#print axioms disjoint_compOf_iff_of_connected

open scoped Classical in
/-- The exchange a pair supplies for itself: `pairFlip` across `p₀`'s touch component inside
`q.1 ∪ q.2 ∪ {p₀, pd}`. The separator is a function of the pair, which is what summing over an
involution requires.

DERIVED: no numeral. -/
noncomputable def exchange (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    (q : Finset Pq × Finset Pq) : Finset Pq × Finset Pq :=
  pairFlip (compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀) q

/-- **`pairFlip` preserves the union of the pair**: `(pairFlip A q).1 ∪ (pairFlip A q).2 = q.1 ∪ q.2`
for every `A`. A separator computed from that union is therefore unchanged by the flip.

DERIVED: no numeral. -/
theorem pairFlip_union (A : Finset Pq) (q : Finset Pq × Finset Pq) :
    (pairFlip A q).1 ∪ (pairFlip A q).2 = q.1 ∪ q.2 := by
  classical
  ext x
  by_cases hx : x ∈ A <;> simp [pairFlip, hx] <;> tauto

/-- **`pairFlip A` is an involution**: flipping twice across the same `A` returns the pair.

DERIVED: no numeral. -/
theorem pairFlip_pairFlip (A : Finset Pq) (q : Finset Pq × Finset Pq) :
    pairFlip A (pairFlip A q) = q := by
  classical
  obtain ⟨X, Y⟩ := q
  simp only [pairFlip, Prod.mk.injEq]
  constructor <;> · ext x; by_cases hx : x ∈ A <;> simp [hx]

theorem exchange_union (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (q : Finset Pq × Finset Pq) :
    (exchange bd p₀ pd q).1 ∪ (exchange bd p₀ pd q).2 = q.1 ∪ q.2 := by
  unfold exchange; exact pairFlip_union _ q

theorem exchange_exchange (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (q : Finset Pq × Finset Pq) :
    exchange bd p₀ pd (exchange bd p₀ pd q) = q := by
  have h : (exchange bd p₀ pd q).1 ∪ (exchange bd p₀ pd q).2 ∪ {p₀, pd}
      = q.1 ∪ q.2 ∪ {p₀, pd} := by rw [exchange_union]
  show pairFlip (compOf bd ((exchange bd p₀ pd q).1 ∪ (exchange bd p₀ pd q).2 ∪ {p₀, pd}) p₀)
      (exchange bd p₀ pd q) = q
  rw [h]
  exact pairFlip_pairFlip _ q

#print axioms exchange_exchange

open scoped Classical in
/-- The exchange for an observable given by a link support: `pairFlip` across
`sepOfLinks bd (q.1 ∪ q.2) Sa`. Where `exchange` flips across the component of an anchor plaquette,
this needs only a link set.

DERIVED: no numeral. -/
noncomputable def exchangeObs (bd : Pq → List (Lk × Bool)) (Sa : Finset Lk)
    (q : Finset Pq × Finset Pq) : Finset Pq × Finset Pq :=
  pairFlip (sepOfLinks bd (q.1 ∪ q.2) Sa) q

open scoped Classical in
/-- **`exchangeObs` preserves the union of the pair**, so the separator recomputed from that union
after the flip is the same set. `pairFlip_union` at `sepOfLinks bd (q.1 ∪ q.2) Sa`.

DERIVED: no numeral. -/
theorem exchangeObs_union (bd : Pq → List (Lk × Bool)) (Sa : Finset Lk)
    (q : Finset Pq × Finset Pq) :
    (exchangeObs bd Sa q).1 ∪ (exchangeObs bd Sa q).2 = q.1 ∪ q.2 := by
  unfold exchangeObs; exact pairFlip_union _ q

#print axioms exchangeObs_union

open scoped Classical in
/-- **`exchangeObs bd Sa` is an involution.** The separator is a function of the pair's union alone,
and `exchangeObs_union` says the union survives the flip, so the second flip is across the same set
and `pairFlip_pairFlip` applies.

DERIVED: no numeral. -/
theorem exchangeObs_exchangeObs (bd : Pq → List (Lk × Bool)) (Sa : Finset Lk)
    (q : Finset Pq × Finset Pq) :
    exchangeObs bd Sa (exchangeObs bd Sa q) = q := by
  have h : (exchangeObs bd Sa q).1 ∪ (exchangeObs bd Sa q).2 = q.1 ∪ q.2 :=
    exchangeObs_union bd Sa q
  show pairFlip (sepOfLinks bd ((exchangeObs bd Sa q).1 ∪ (exchangeObs bd Sa q).2) Sa)
      (exchangeObs bd Sa q) = q
  rw [h]
  exact pairFlip_pairFlip _ q

#print axioms exchangeObs_exchangeObs

open scoped Classical in
/-- **The non-bridging pairs cancel on every family fixed by the pair's union.** For any predicate `Q`
on plaquette sets, the pairs `q` with `Q (q.1 ∪ q.2)` in which no plaquette of the separator grown
from `Sa` carries a link of `Sb` sum to zero. The exchange `exchangeObs bd Sa` preserves `q.1 ∪ q.2`
(`exchangeObs_union`), so it maps the family to itself, and each pair cancels its image
(`pairTermObs_add_flip_of_no_bridge`). `nonbridging_sum_eq_zeroObs` is this at `Q` constantly true.

DERIVED: the `0` is the value of the cancelled sum. -/
theorem nonbridging_sum_eq_zeroObs_of (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (Sa Sb : Finset Lk)
    (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    (Q : Finset Pq → Prop) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => Q (q.1 ∪ q.2) ∧ ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
          ∀ l ∈ linkSupp bd p, l ∉ Sb),
      pairTermObs (Nc := Nc) bd O₁ O₂ β q = 0 := by
  classical
  set s : Finset (Finset Pq × Finset Pq) :=
    (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => Q (q.1 ∪ q.2) ∧ ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
        ∀ l ∈ linkSupp bd p, l ∉ Sb) with hs
  have hmem : ∀ q ∈ s, exchangeObs bd Sa q ∈ s := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [exchangeObs_union]
    exact hq.2
  have hcancel : ∀ q ∈ s, pairTermObs (Nc := Nc) bd O₁ O₂ β q
      + pairTermObs (Nc := Nc) bd O₁ O₂ β (exchangeObs bd Sa q) = 0 := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq
    have h := pairTermObs_add_flip_of_no_bridge (Nc := Nc) bd β O₁ O₂ q.1 q.2 Sa Sb hab h₁ h₂ hq.2.2
    simpa [exchangeObs] using h
  have hinj : ∀ x ∈ s, ∀ y ∈ s, exchangeObs bd Sa x = exchangeObs bd Sa y → x = y := by
    intro x _ y _ hxy
    rw [← exchangeObs_exchangeObs bd Sa x, ← exchangeObs_exchangeObs bd Sa y, hxy]
  have himg : s.image (exchangeObs bd Sa) = s := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      exact hmem r hr
    · intro q hq
      exact Finset.mem_image.mpr
        ⟨exchangeObs bd Sa q, hmem q hq, exchangeObs_exchangeObs bd Sa q⟩
  have key : ∑ q ∈ s, pairTermObs (Nc := Nc) bd O₁ O₂ β q
      = - ∑ q ∈ s, pairTermObs (Nc := Nc) bd O₁ O₂ β q := by
    calc ∑ q ∈ s, pairTermObs (Nc := Nc) bd O₁ O₂ β q
        = ∑ q ∈ s.image (exchangeObs bd Sa), pairTermObs (Nc := Nc) bd O₁ O₂ β q := by rw [himg]
      _ = ∑ q ∈ s, pairTermObs (Nc := Nc) bd O₁ O₂ β (exchangeObs bd Sa q) :=
          Finset.sum_image hinj
      _ = ∑ q ∈ s, (- pairTermObs (Nc := Nc) bd O₁ O₂ β q) :=
          Finset.sum_congr rfl (fun q hq => by have := hcancel q hq; linarith)
      _ = - ∑ q ∈ s, pairTermObs (Nc := Nc) bd O₁ O₂ β q := by simp
  linarith

#print axioms nonbridging_sum_eq_zeroObs_of

open scoped Classical in
/-- **The non-bridging sum vanishes, at two arbitrary observables.** For `O₁` local on `Sa`, `O₂`
local on `Sb` and `Disjoint Sa Sb`, the sum of `pairTermObs bd O₁ O₂ β q` over the pairs `q` in which
no plaquette of `(q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa` carries a link of `Sb` is zero, at every
`β`.

`nonbridging_sum_eq_zeroF` with the two plaquette finsets replaced by two observables. The filter is
at the level of links: where the plaquette version asks that no plaquette of `Ao` reach one of `Bo`,
this asks that no plaquette of the separator grown from `Sa` carry a link of `Sb`.
`exchangeObs_exchangeObs` makes the flip an involution on that filtered set and
`pairTermObs_add_flip_of_no_bridge` negates the summand, so the sum equals its own negation.

DERIVED: the `0` is the value of the filtered sum. -/
theorem nonbridging_sum_eq_zeroObs (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (Sa Sb : Finset Lk)
    (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
          ∀ l ∈ linkSupp bd p, l ∉ Sb),
      pairTermObs (Nc := Nc) bd O₁ O₂ β q = 0 := by
  have h := nonbridging_sum_eq_zeroObs_of (Nc := Nc) bd β O₁ O₂ Sa Sb hab h₁ h₂ (fun _ => True)
  simpa only [true_and] using h

#print axioms nonbridging_sum_eq_zeroObs

/-! #### Bounded local observables -/

/-- **A product of local observables is local on the union of their supports.** The witness
restricts to each support and multiplies.

DERIVED: no numeral. -/
theorem localOnLinks_mul {S T : Finset Lk} {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ}
    (h₁ : LocalOnLinks (Nc := Nc) S O₁) (h₂ : LocalOnLinks (Nc := Nc) T O₂) :
    LocalOnLinks (Nc := Nc) (S ∪ T) (fun U => O₁ U * O₂ U) := by
  obtain ⟨A, hA, eA⟩ := h₁
  obtain ⟨B, hB, eB⟩ := h₂
  refine ⟨fun V => A (fun i : S => V ⟨i.val, Finset.mem_union_left T i.property⟩)
      * B (fun i : T => V ⟨i.val, Finset.mem_union_right S i.property⟩), ?_, fun U => ?_⟩
  · have hA' : Measurable (fun V : (S ∪ T : Finset Lk) → MassGap.SUN.SU Nc =>
        A (fun i : S => V ⟨i.val, Finset.mem_union_left T i.property⟩)) :=
      hA.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    have hB' : Measurable (fun V : (S ∪ T : Finset Lk) → MassGap.SUN.SU Nc =>
        B (fun i : T => V ⟨i.val, Finset.mem_union_right S i.property⟩)) :=
      hB.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    exact hA'.mul hB'
  · simp only [eA U, eB U]

#print axioms localOnLinks_mul

/-- **A local observable is measurable**: it is its measurable witness composed with the restriction.

DERIVED: no numeral. -/
theorem measurable_of_localOnLinks {S : Finset Lk} {O : (Lk → MassGap.SUN.SU Nc) → ℝ}
    (h : LocalOnLinks (Nc := Nc) S O) : Measurable O := by
  obtain ⟨Ô, hÔ, hO⟩ := h
  have he : O = fun U => Ô (fun i : S => U i.val) := funext hO
  rw [he]
  exact hÔ.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))

#print axioms measurable_of_localOnLinks

/-- **A continuous observable that reads only the links of `S` is local on `S`.** The witness extends a
configuration on `S` by the identity off `S` and evaluates; it is continuous, hence measurable.

DERIVED: no numeral. -/
theorem localOnLinks_of_continuous {S : Finset Lk} {O : (Lk → MassGap.SUN.SU Nc) → ℝ}
    (hc : Continuous O)
    (hloc : ∀ U V : Lk → MassGap.SUN.SU Nc, (∀ i ∈ S, U i = V i) → O U = O V) :
    LocalOnLinks (Nc := Nc) S O := by
  classical
  refine ⟨fun w => O (fun i => if h : i ∈ S then w ⟨i, h⟩ else 1), ?_, fun U => ?_⟩
  · refine (hc.comp (continuous_pi (fun i => ?_))).measurable
    by_cases h : i ∈ S
    · have he : (fun w : S → MassGap.SUN.SU Nc => if h' : i ∈ S then w ⟨i, h'⟩ else 1)
          = fun w => w ⟨i, h⟩ := funext fun w => dif_pos h
      rw [he]; exact continuous_apply _
    · have he : (fun w : S → MassGap.SUN.SU Nc => if h' : i ∈ S then w ⟨i, h'⟩ else 1)
          = fun _ => 1 := funext fun w => dif_neg h
      rw [he]; exact continuous_const
  · exact hloc _ _ (fun i hi => by simp [hi])

#print axioms localOnLinks_of_continuous

open scoped Classical in
/-- **A pair term of two local observables is its restriction to `A` times the two outside
weights.** With `LocalOnLinks Sa O₁`, `LocalOnLinks Sb O₂`, no touch across `A` inside `E ∪ F`, and
no plaquette of `(E ∪ F) \ A` meeting `Sa ∪ Sb`,

    pairTermObs (E, F) = pairTermObs (E ∩ A, F ∩ A) · (zwFull 1 (E \ A) · zwFull 1 (F \ A)).

`pairTermF_eq_core_mul_outside` with the plaquette products replaced by observables: the inside link
block is the boundary union of `(E ∪ F) ∩ A` together with `Sa ∪ Sb`, the outside block the boundary
union of `(E ∪ F) \ A`, and each of the four terms splits by `zwFull_split` against the constant
observable on the outside block.

DERIVED: the `1` is the constant observable of `pairTermObs`. -/
theorem pairTermObs_eq_core_mul_outside (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk}
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F) ∩ A, ∀ r ∈ (E ∪ F) \ A, ¬ Touch bd p r)
    (hobs : ∀ r ∈ (E ∪ F) \ A, ∀ l ∈ linkSupp bd r, l ∉ Sa ∪ Sb) :
    pairTermObs (Nc := Nc) bd O₁ O₂ β (E, F)
      = pairTermObs (Nc := Nc) bd O₁ O₂ β (E ∩ A, F ∩ A)
        * (zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) (E \ A)
          * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) (F \ A)) := by
  classical
  set S : Finset Lk := ((E ∪ F) ∩ A).biUnion (linkSupp bd) ∪ (Sa ∪ Sb) with hS
  set T : Finset Lk := ((E ∪ F) \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
      exact hclosed p hp r hr ⟨l, hlp, hlr⟩
    · exact hobs r hr l hlr hl
  have hsp : ∀ X : (Lk → MassGap.SUN.SU Nc) → ℝ, LocalOnLinks (Nc := Nc) S X →
      ∀ W : Finset Pq, W ⊆ E ∪ F →
      zwFull (Nc := Nc) bd β X W
        = zwFull (Nc := Nc) bd β X (W ∩ A) * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) (W \ A) := by
    intro X hX W hW
    have hEu : W = (W ∩ A) ∪ (W \ A) := by
      ext x; by_cases hx : x ∈ A <;> simp [hx]
    have hEd : Disjoint (W ∩ A) (W \ A) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
    have hE₁ : ∀ p ∈ W ∩ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
      intro p hp l hl
      have hp' : p ∈ (E ∪ F) ∩ A :=
        Finset.mem_inter.mpr ⟨hW (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
      rw [hS]
      exact Finset.mem_union_left _ (supp_subset_biUnion bd _ p hp' l hl)
    have hE₂ : ∀ p ∈ W \ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
      intro p hp l hl
      have hp' : p ∈ (E ∪ F) \ A :=
        Finset.mem_sdiff.mpr ⟨hW (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩
      rw [hT]
      exact supp_subset_biUnion bd _ p hp' l hl
    rw [zwFull_congr (Nc := Nc) bd β
      (O' := fun U => X U * (fun _ : Lk → MassGap.SUN.SU Nc => (1 : ℝ)) U)
      (fun U => (mul_one (X U)).symm) W]
    exact zwFull_split (Nc := Nc) bd β W (W ∩ A) (W \ A) S T hST hX (localOnLinks_one T)
      hEu hEd hE₁ hE₂
  have hSab : Sa ∪ Sb ⊆ S := by rw [hS]; exact Finset.subset_union_right
  have l12 : LocalOnLinks (Nc := Nc) S (fun U => O₁ U * O₂ U) :=
    localOnLinks_mono bd hSab (localOnLinks_mul h₁ h₂)
  have l1 : LocalOnLinks (Nc := Nc) S O₁ :=
    localOnLinks_mono bd (Finset.subset_union_left.trans hSab) h₁
  have l2 : LocalOnLinks (Nc := Nc) S O₂ :=
    localOnLinks_mono bd (Finset.subset_union_right.trans hSab) h₂
  have hE : E ⊆ E ∪ F := Finset.subset_union_left
  have hF : F ⊆ E ∪ F := Finset.subset_union_right
  have e1 := hsp _ l12 E hE
  have e2 := hsp _ (localOnLinks_one S) F hF
  have e3 := hsp _ l1 E hE
  have e4 := hsp _ l2 F hF
  simp only [pairTermObs]
  rw [e1, e2, e3, e4]
  ring

#print axioms pairTermObs_eq_core_mul_outside

/-- **A bounded measurable observable times a product of activated weights is integrable** against
product Haar, at every `β` and every `E`, given `Nc ≠ 0`. The observable's bound `c` and
`subset_weight_bound` bound the integrand by a constant against a probability measure. This is the
integrability `corrNum_eq_subset_sum` consumes, for one observable.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `1` subtracted from the exponential is
`boltz_eq_subset_sum`'s activated weight. -/
theorem integrable_obsFull_mul_wprod (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} (hm : Measurable O) {c : ℝ} (hc : ∀ U, |O U| ≤ c)
    (E : Finset Pq) :
    Integrable (fun U => O U * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hmw : Measurable (fun U : Lk → MassGap.SUN.SU Nc =>
      ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))) :=
    Finset.measurable_prod _ (fun p _ => (measurable_wfun β).comp
      (measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p)))
  refine (integrable_const (c * (Real.exp (2 * |β|) - 1) ^ E.card)).mono'
    (hm.mul hmw).aestronglyMeasurable (Filter.Eventually.of_forall (fun U => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc U) (subset_weight_bound hN bd β U E) (abs_nonneg _)
    ((abs_nonneg _).trans (hc U))

#print axioms integrable_obsFull_mul_wprod

open scoped Classical in
/-- The connected correlator of two arbitrary observables:
`⟨O₁·O₂⟩_β − ⟨O₁⟩_β ⟨O₂⟩_β`, each expectation taken in the Gibbs state of `wilsonSystem`.
`WilsonBridge.wilsonCorrConnF` with the two plaquette finsets replaced by observables.

DERIVED: no numeral. -/
noncomputable def wilsonCorrConnObs (bd : Pq → List (Lk × Bool))
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (β : ℝ) : ℝ :=
  (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
      (fun U => O₁ U * O₂ U)
    - (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β O₁
      * (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β O₂

open scoped Classical in
/-- **The connected correlator of two observables on disjoint link supports is the bridging sum over
`Z²`.** With `Nc ≠ 0`, `Disjoint Sa Sb`, `LocalOnLinks Sa O₁`, `LocalOnLinks Sb O₂` and the bounds
`|O₁| ≤ c₁`, `|O₂| ≤ c₂`,

    wilsonCorrConnObs bd O₁ O₂ β = (∑ over bridging q, pairTermObs bd O₁ O₂ β q) / Z ^ 2,

the sum running over the pairs that fail the non-bridging filter — those in which some plaquette of
the separator grown from `Sa` carries a link of `Sb`.

The observable counterpart of `wilsonCorrConnF_eq_bridging_sumF`. `corrNum_eq_subset_sum` is already
general in the observable, so the subset expansion is reused with the four specialisations `O₁·O₂`,
`O₁`, `O₂` and the constant `1`, each integrable against every activated product by
`integrable_obsFull_mul_wprod` — locality gives measurability (`measurable_of_localOnLinks`) and the
bounds give the rest; `nonbridging_sum_eq_zeroObs` removes the complementary pairs.

DERIVED: the `2` in `Z ^ 2` is the number of independent subset sums, one per component of the pair
— `hprod` turns two sums over `Finset Pq` into one over `Finset Pq × Finset Pq`, so each of the two
Gibbs numerators carries its own partition function. The `0` is `hN : Nc ≠ 0`, which makes the
partition function positive so the division is meaningful. The `1` and `2` in
`q.1` and `q.2` are projections, not numerals. -/
theorem wilsonCorrConnObs_eq_bridging_sumObs (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ) (Sa Sb : Finset Lk)
    (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {c₁ c₂ : ℝ} (hc₁ : ∀ U, |O₁ U| ≤ c₁) (hc₂ : ∀ U, |O₂ U| ≤ c₂) (β : ℝ) :
    wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ β
      = (∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
            (fun q => ¬ ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
              ∀ l ∈ linkSupp bd p, l ∉ Sb),
          pairTermObs (Nc := Nc) bd O₁ O₂ β q)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β) ^ 2 := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  have hz : ∀ O : (Lk → MassGap.SUN.SU Nc) → ℝ, Measurable O → ∀ c : ℝ, (∀ U, |O U| ≤ c) →
      (∫ U, O U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = ∑ E : Finset Pq, zwFull (Nc := Nc) bd β O E := by
    intro O hm c hc
    have h := corrNum_eq_subset_sum (Nc := Nc) bd β O
      (fun E _ => integrable_obsFull_mul_wprod hN bd β hm hc E)
    rw [Finset.powerset_univ] at h
    exact h
  have hprod : ∀ f g : Finset Pq → ℝ,
      (∑ E : Finset Pq, f E) * (∑ F : Finset Pq, g F)
        = ∑ q : Finset Pq × Finset Pq, f q.1 * g q.2 := by
    intro f g
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hnum : (∑ E : Finset Pq, zwFull (Nc := Nc) bd β (fun U => O₁ U * O₂ U) E)
        * (∑ F : Finset Pq, zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) F)
      - (∑ E : Finset Pq, zwFull (Nc := Nc) bd β O₁ E)
        * (∑ F : Finset Pq, zwFull (Nc := Nc) bd β O₂ F)
      = ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
          (fun q => ¬ ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
            ∀ l ∈ linkSupp bd p, l ∉ Sb),
        pairTermObs (Nc := Nc) bd O₁ O₂ β q := by
    rw [hprod, hprod, ← Finset.sum_sub_distrib]
    have hpt : ∀ q : Finset Pq × Finset Pq,
        zwFull (Nc := Nc) bd β (fun U => O₁ U * O₂ U) q.1
            * zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) q.2
          - zwFull (Nc := Nc) bd β O₁ q.1 * zwFull (Nc := Nc) bd β O₂ q.2
        = pairTermObs (Nc := Nc) bd O₁ O₂ β q := fun q => rfl
    rw [Finset.sum_congr rfl (fun q _ => hpt q),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset Pq × Finset Pq))
        (fun q => ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
          ∀ l ∈ linkSupp bd p, l ∉ Sb)
        (pairTermObs (Nc := Nc) bd O₁ O₂ β),
      nonbridging_sum_eq_zeroObs (Nc := Nc) bd β O₁ O₂ Sa Sb hab h₁ h₂, zero_add]
  have hpart : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
        (probHaar (MassGap.SUN.SU Nc)) β
      = ∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := rfl
  have hZ : (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) E := by
    refine Eq.trans ?_ (hz (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by simp))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [one_mul]
  have hne0 : (∑ E : Finset Pq, zwFull (Nc := Nc) bd β (fun _ => (1 : ℝ)) E) ≠ 0 := by
    rw [← hZ, ← hpart]; exact hZpos.ne'
  -- `expect` is the ratio definitionally, exactly as in `wilsonCorrConnF_eq_bridging_sumF`
  have hconnEq : wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ β
      = (∫ U, (fun U => O₁ U * O₂ U) U
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        - ((∫ U, O₁ U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))))
          * ((∫ U, O₂ U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))) := rfl
  have hm₁ := measurable_of_localOnLinks h₁
  have hm₂ := measurable_of_localOnLinks h₂
  have h0₁ : 0 ≤ c₁ := (abs_nonneg _).trans (hc₁ (fun _ => 1))
  rw [hconnEq, hpart, hz (fun U => O₁ U * O₂ U) (hm₁.mul hm₂) (c₁ * c₂)
      (fun U => by rw [abs_mul]; exact mul_le_mul (hc₁ U) (hc₂ U) (abs_nonneg _) h0₁),
    hz O₁ hm₁ c₁ hc₁, hz O₂ hm₂ c₂ hc₂, hZ, ← hnum]
  field_simp

#print axioms wilsonCorrConnObs_eq_bridging_sumObs

open scoped Classical in
/-- **At zero coupling the connected correlator of two observables on disjoint link supports is
zero.** `wilsonCorrConnObs bd O₁ O₂ 0 = 0`, given `Disjoint Sa Sb`, `LocalOnLinks Sa O₁` and
`LocalOnLinks Sb O₂`.

At `β = 0` the Boltzmann weight is `1`, so the state is product Haar and `block_integral_factor`
factorises the joint expectation into the two marginals, which is what `wilsonCorrConnObs`
subtracts. No plaquette structure is used, and the measurability of the two witnesses is what
`block_integral_factor` needs.

This is the statement at `β = 0` alone. There the links are independent and the vanishing is by
factorisation, not by decay in any separation; nothing in it applies at `β > 0`, where the Boltzmann
weight couples the two blocks.

DERIVED: the first `0` is the coupling the statement fixes; the second is the value of the
correlator. -/
theorem wilsonCorrConnObs_at_zero (bd : Pq → List (Lk × Bool))
    {Sa Sb : Finset Lk} (hab : Disjoint Sa Sb)
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ}
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂) :
    wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ 0 = 0 := by
  classical
  obtain ⟨Ô₁, hm₁, he₁⟩ := h₁
  obtain ⟨Ô₂, hm₂, he₂⟩ := h₂
  -- stated against `vol` rather than `Measure.pi`: they are defeq, and `rw` needs the syntactic
  -- form the goal carries
  have hfac : (∫ U, Ô₁ (fun i : Sa => (U : Lk → MassGap.SUN.SU Nc) i.val)
          * Ô₂ (fun i : Sb => (U : Lk → MassGap.SUN.SU Nc) i.val)
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, Ô₁ (fun i : Sa => (U : Lk → MassGap.SUN.SU Nc) i.val)
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
        * ∫ U, Ô₂ (fun i : Sb => (U : Lk → MassGap.SUN.SU Nc) i.val)
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    block_integral_factor (N := Nc) Sa Sb hab Ô₁ Ô₂ hm₁ hm₂
  unfold wilsonCorrConnObs
  rw [wilsonSystem_expect_at_zero bd (fun U => O₁ U * O₂ U),
    wilsonSystem_expect_at_zero bd O₁, wilsonSystem_expect_at_zero bd O₂]
  simp only [he₁, he₂]
  rw [hfac]
  ring

#print axioms wilsonCorrConnObs_at_zero




open scoped Classical in
/-- **The non-bridging part of the connected numerator's double sum is zero.** Summing `pairTerm` over
the pairs `q` with `¬ Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd` gives `0`, for every `β` and at any
lattice size. `p₀ ≠ pd` is required.

The exchange is `pairFlip` across `p₀`'s own component inside the pair's union. It is an involution
(`exchange_exchange`), it preserves the union and hence the component (`exchange_union`), and it
negates the summand (`pairTerm_add_pairFlip`). A sum equal to its own negation is zero.

The complementary sum, over pairs whose union carries a touching chain from `p₀` to `pd`, is counted
by `card_bridging_pairs_le` and weighted by `subset_weight_bound`.

DERIVED: the `0` is the value of the filtered sum. -/
theorem nonbridging_sum_eq_zero (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ¬ Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
      pairTerm (Nc := Nc) bd p₀ pd β q = 0 := by
  classical
  set s : Finset (Finset Pq × Finset Pq) :=
    (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => ¬ Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd) with hs
  have hmem : ∀ q ∈ s, exchange bd p₀ pd q ∈ s := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [exchange_union]
    exact hq.2
  have hcancel : ∀ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q
      + pairTerm (Nc := Nc) bd p₀ pd β (exchange bd p₀ pd q) = 0 := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq
    have hpdV : pd ∈ q.1 ∪ q.2 ∪ {p₀, pd} := by simp
    have hp0V : p₀ ∈ q.1 ∪ q.2 ∪ {p₀, pd} := by simp
    have hnotin : pd ∉ compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ := by
      intro hc; exact hq.2 (mem_compOf.mp hc).2
    have := pairTerm_add_pairFlip (Nc := Nc) bd p₀ pd hne β q.1 q.2
      (compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)
      (compOf_closed bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)
      (self_mem_compOf hp0V) hnotin
    simpa [exchange] using this
  have hinj : ∀ x ∈ s, ∀ y ∈ s, exchange bd p₀ pd x = exchange bd p₀ pd y → x = y := by
    intro x _ y _ hxy
    rw [← exchange_exchange bd p₀ pd x, ← exchange_exchange bd p₀ pd y, hxy]
  have himg : s.image (exchange bd p₀ pd) = s := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      exact hmem r hr
    · intro q hq
      exact Finset.mem_image.mpr ⟨exchange bd p₀ pd q, hmem q hq, exchange_exchange bd p₀ pd q⟩
  have key : ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q
      = - ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q := by
    calc ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q
        = ∑ q ∈ s.image (exchange bd p₀ pd), pairTerm (Nc := Nc) bd p₀ pd β q := by rw [himg]
      _ = ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β (exchange bd p₀ pd q) :=
          Finset.sum_image hinj
      _ = ∑ q ∈ s, (- pairTerm (Nc := Nc) bd p₀ pd β q) :=
          Finset.sum_congr rfl (fun q hq => by have := hcancel q hq; linarith)
      _ = - ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q := by simp
  linarith

#print axioms nonbridging_sum_eq_zero

/-- **When `p₀` touches `pd`, no `A` satisfies the separator hypothesis.** For any `A` containing
`p₀` and missing `pd`, the closure condition of `pairTerm_add_exchange` is false: `p₀` lies in
`(E ∪ F ∪ {p₀, pd}) ∩ A`, `pd` in the complement, and they touch. So that lemma and
`pairTerm_eq_core_mul_outside` say nothing about a pair at touch-separation one.

DERIVED: no numeral. -/
theorem no_separator_of_touch (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F A : Finset Pq)
    (ht : Touch bd p₀ pd) (h0 : p₀ ∈ A) (hd : pd ∉ A) :
    ¬ (∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r) := by
  intro hclosed
  exact hclosed p₀ (Finset.mem_inter.mpr ⟨by simp, h0⟩) pd
    (Finset.mem_sdiff.mpr ⟨by simp, hd⟩) ht

#print axioms no_separator_of_touch

/-- **A pair's term is its restriction to `A` times the two outside weights.** For `A` containing
both `p₀` and `pd` and touch-closed inside `E ∪ F ∪ {p₀, pd}`,

    pairTerm (E, F) = pairTerm (E ∩ A, F ∩ A) · (zw ∅ (E \ A) · zw ∅ (F \ A)).

The outside factors carry no plaquette observable: both are `zw` at the empty observable set.

The companion of `pairTerm_add_exchange` on the other side of the split — there `pd ∉ A`, here
`pd ∈ A`. It is what turns the surviving sum into a sum over cores, each multiplied by a sum over
outside sets that do not touch the core; `hard_core_ratio_le` is what bounds the latter against `Z`.

DERIVED: no numeral. -/
theorem pairTerm_eq_core_mul_outside (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r)
    (h0 : p₀ ∈ A) (hd : pd ∈ A) :
    pairTerm (Nc := Nc) bd p₀ pd β (E, F)
      = pairTerm (Nc := Nc) bd p₀ pd β (E ∩ A, F ∩ A)
        * (zw (Nc := Nc) bd β ∅ (E \ A) * zw (Nc := Nc) bd β ∅ (F \ A)) := by
  classical
  set V : Finset Pq := E ∪ F ∪ {p₀, pd} with hV
  set S : Finset Lk := (V ∩ A).biUnion (linkSupp bd) with hS
  set T : Finset Lk := (V \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    exact hclosed p hp r hr ⟨l, hlp, hlr⟩
  have hinS : ∀ W : Finset Pq, W ⊆ V ∩ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    rw [hS]; exact supp_subset_biUnion bd (V ∩ A) p (hW hp) l hl
  have hinT : ∀ W : Finset Pq, W ⊆ V \ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    rw [hT]; exact supp_subset_biUnion bd (V \ A) p (hW hp) l hl
  have hEV : E ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hFV : F ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hp0V : p₀ ∈ V := by rw [hV]; simp
  have hpdV : pd ∈ V := by rw [hV]; simp
  have hsubIn : ∀ W : Finset Pq, W ⊆ V → (W ∩ A) ⊆ V ∩ A := by
    intro W hW x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have hsubOut : ∀ W : Finset Pq, W ⊆ V → (W \ A) ⊆ V \ A := by
    intro W hW x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have gcore : ({p₀, pd} : Finset Pq) ⊆ V ∩ A := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_inter.mpr ⟨hp0V, h0⟩
    · rw [Finset.mem_singleton] at hx'; subst hx'
      exact Finset.mem_inter.mpr ⟨hpdV, hd⟩
  have g0 : ({p₀} : Finset Pq) ⊆ V ∩ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_inter.mpr ⟨hp0V, h0⟩
  have gd : ({pd} : Finset Pq) ⊆ V ∩ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_inter.mpr ⟨hpdV, hd⟩
  have gEA := hsubIn E hEV
  have gFA := hsubIn F hFV
  have gEc := hsubOut E hEV
  have gFc := hsubOut F hFV
  have gEm : (∅ : Finset Pq) ⊆ V ∩ A := Finset.empty_subset _
  have gEn : (∅ : Finset Pq) ⊆ V \ A := Finset.empty_subset _
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hDr : ∀ W : Finset Pq, W = W ∪ ∅ := fun W => (Finset.union_empty W).symm
  have e1 := zw_split (Nc := Nc) bd β {p₀, pd} {p₀, pd} ∅ E (E ∩ A) (E \ A) S T hST
    (hDr _) hEu (by simp) (hIO E E) (hinS _ gcore) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e2 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ F (F ∩ A) (F \ A) S T hST
    (hDr _) hFu (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  have e3 := zw_split (Nc := Nc) bd β {p₀} {p₀} ∅ E (E ∩ A) (E \ A) S T hST
    (hDr _) hEu (by simp) (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e4 := zw_split (Nc := Nc) bd β {pd} {pd} ∅ F (F ∩ A) (F \ A) S T hST
    (hDr _) hFu (by simp) (hIO F F) (hinS _ gd) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  simp only [pairTerm]
  rw [e1, e2, e3, e4]
  ring

#print axioms pairTerm_eq_core_mul_outside

/-! ### The cancellation, applied to the Wilson connected correlation itself

`nonbridging_sum_eq_zero` is an identity about the double sum; `wilsonCorrConn_eq_bridging_sum` below
is the same identity about `MassGap.WilsonBridge.wilsonCorrConn`. The four Gibbs integrals expand
over activated subsets (`corrNum_eq_subset_sum`), their two products become one sum over pairs, and
the non-bridging pairs drop out, leaving a sum over pairs whose union carries a touching chain from
`p₀` to `p_d`, divided by `Z²`.

The integrability side condition is the one `corrNum_eq_subset_sum` carries, stated once for all the
observable/subset pairs the proof uses. -/

open scoped Classical in
/-- **The connected Wilson correlation is the sum over bridging pairs, divided by `Z²`.** With
`Nc ≠ 0`, `p₀ ≠ pd` and the integrability condition `hint`,

    wilsonCorrConn bd p₀ β pd = (∑ over q with Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd,
                                   pairTerm bd p₀ pd β q) / Z ^ 2.

The pairs that carry no touching chain from `p₀` to `pd` inside their own union contribute nothing,
by `nonbridging_sum_eq_zero`, at every coupling and any lattice size. This is an identity, not a
bound; the surviving sum is bounded further down by `wilsonCorrConn_abs_le_core_sum` and its
successors.

DERIVED: the `2` in `Z ^ 2` is the number of independent subset sums, one per component of the pair,
each Gibbs numerator carrying its own partition function. The `0` is `hN : Nc ≠ 0`, which makes `Z`
positive so the division is meaningful. The `1` in `hint`'s `Real.exp (-(β * φ_p)) - 1` is the
activated weight of `boltz_eq_subset_sum`; the `1` and `2` in `q.1` and `q.2` are projections. -/
theorem wilsonCorrConn_eq_bridging_sum (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd
      = (∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
            (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
          pairTerm (Nc := Nc) bd p₀ pd β q)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β) ^ 2 := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  -- every Gibbs numerator is a finite sum over activated subsets
  have hz : ∀ D : Finset Pq,
      (∫ U, (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = ∑ E : Finset Pq, zw (Nc := Nc) bd β D E := by
    intro D
    have h := corrNum_eq_subset_sum (Nc := Nc) bd β
      (fun U => ∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U) (fun E _ => hint D E)
    rw [Finset.powerset_univ] at h
    exact h
  have h2 : (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀, pd} E := by
    refine Eq.trans ?_ (hz {p₀, pd})
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_pair hne]
  have hA : (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀} E := by
    refine Eq.trans ?_ (hz {p₀})
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_singleton]
  have hB : (∫ U, wilsonPlaqObs (N := Nc) bd pd U
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β {pd} E := by
    refine Eq.trans ?_ (hz {pd})
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_singleton]
  have hZ : (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β ∅ E := by
    refine Eq.trans ?_ (hz ∅)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul]
  -- two sums over subsets become one sum over pairs
  have hprod : ∀ f g : Finset Pq → ℝ,
      (∑ E : Finset Pq, f E) * (∑ F : Finset Pq, g F)
        = ∑ q : Finset Pq × Finset Pq, f q.1 * g q.2 := by
    intro f g
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hnum : (∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀, pd} E)
        * (∑ F : Finset Pq, zw (Nc := Nc) bd β ∅ F)
      - (∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀} E)
        * (∑ F : Finset Pq, zw (Nc := Nc) bd β {pd} F)
      = ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
          (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
        pairTerm (Nc := Nc) bd p₀ pd β q := by
    rw [hprod, hprod, ← Finset.sum_sub_distrib]
    have hpt : ∀ q : Finset Pq × Finset Pq,
        zw (Nc := Nc) bd β {p₀, pd} q.1 * zw (Nc := Nc) bd β ∅ q.2
          - zw (Nc := Nc) bd β {p₀} q.1 * zw (Nc := Nc) bd β {pd} q.2
        = pairTerm (Nc := Nc) bd p₀ pd β q := fun q => rfl
    rw [Finset.sum_congr rfl (fun q _ => hpt q),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset Pq × Finset Pq))
        (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd)
        (pairTerm (Nc := Nc) bd p₀ pd β),
      nonbridging_sum_eq_zero bd p₀ pd hne β, add_zero]
  -- the connected correlation, written out over the same measure
  have hconn : MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd
      = (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        - ((∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
              * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))))
          * ((∫ U, wilsonPlaqObs (N := Nc) bd pd U
              * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))) := rfl
  have hpart : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
        (probHaar (MassGap.SUN.SU Nc)) β
      = ∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := rfl
  have hne0 : (∑ E : Finset Pq, zw (Nc := Nc) bd β ∅ E) ≠ 0 := by
    rw [← hZ, ← hpart]; exact hZpos.ne'
  rw [hconn, hpart, h2, hA, hB, hZ, ← hnum]
  field_simp

#print axioms wilsonCorrConn_eq_bridging_sum

/-! ### Separation forces size

`wilsonCorrConn_eq_bridging_sum` is an identity and carries no dependence on the separation by
itself. What puts the separation in the exponent is that a surviving pair must be large: its union
carries a chain of touching plaquettes from `p₀` to `p_d`, and if `p_d` is more than `k` touch-steps
from `p₀` then that chain needs `k` plaquettes strictly between them, all lying in `E ∪ F`. That is
`card_ge_of_bridging`.

The argument is a level function rather than a path. Let `lvl p` be `touchLvl bd p₀ p`, the
touch-distance from `p₀`. It is `0` at `p₀` (`touchLvl_self`), rises by at most one across a touch
(`touchLvl_lipschitz`), and exceeds `k` at `p_d` (`lt_touchLvl_of_not_mem_ball`). Along any reaching
chain the level starts at `0` and ends above `k` in steps of at most `+1`, so it takes every value
`1, …, k` somewhere on the chain (`exists_of_level_le`). Those `k` witnesses have distinct levels,
hence are distinct; none is `p₀`, of level `0`, or `p_d`, of level above `k`; and all lie in the
chain's ambient set.

`mem_ball_of_bridging` is the converse: a bridging pair always puts `p_d` within `|E| + |F| + 1`
steps, so the hypothesis `p_d ∉ ball p₀ k` of `card_ge_of_bridging` is false for every
`k ≥ |E| + |F| + 1`, and `k ≤ |E| + |F|` is the strongest conclusion the hypothesis admits. -/

/-- **`Touch` is symmetric**, sharing a link being a symmetric condition.

DERIVED: no numeral. -/
theorem touch_symm {bd : Pq → List (Lk × Bool)} {p q : Pq} (h : Touch bd p q) : Touch bd q p := by
  obtain ⟨l, hp, hq⟩ := h
  exact ⟨l, hq, hp⟩

open scoped Classical in
/-- The plaquettes within `n` touch-steps of `p₀`, by recursion on `n`. No ambient set restricts it,
unlike `Reach` and `compOf`: this is the geometry of `bd` alone.

DERIVED: the `0` and the `1` are the recursion's base and step. The ball of radius `0` is `{p₀}`,
zero steps reaching only the start, and radius `n + 1` adds exactly the touch-neighbours of radius
`n`, one step being one touch. -/
noncomputable def ball (bd : Pq → List (Lk × Bool)) (p₀ : Pq) : ℕ → Finset Pq
  | 0 => {p₀}
  | n + 1 => ball bd p₀ n ∪ Finset.univ.filter (fun q => ∃ p ∈ ball bd p₀ n, Touch bd p q)

theorem self_mem_ball (bd : Pq → List (Lk × Bool)) (p₀ : Pq) : ∀ n, p₀ ∈ ball bd p₀ n
  | 0 => Finset.mem_singleton_self p₀
  | n + 1 => Finset.mem_union_left _ (self_mem_ball bd p₀ n)

theorem ball_subset_succ (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (n : ℕ) :
    ball bd p₀ n ⊆ ball bd p₀ (n + 1) := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem ball_mono (bd : Pq → List (Lk × Bool)) (p₀ : Pq) {m n : ℕ} (h : m ≤ n) :
    ball bd p₀ m ⊆ ball bd p₀ n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (ball_subset_succ bd p₀ k)
      · rw [Nat.le_antisymm h hge]

theorem mem_ball_succ_of_touch (bd : Pq → List (Lk × Bool)) (p₀ : Pq) {p q : Pq} (n : ℕ)
    (hp : p ∈ ball bd p₀ n) (ht : Touch bd p q) : q ∈ ball bd p₀ (n + 1) := by
  classical
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hp, ht⟩⟩

/-- **A reach inside any `V` lands in some ball**: `Reach bd V a b` gives an `n` with
`b ∈ ball bd a n`. A chain confined to `V` is still a chain in the geometry of `bd`. The `n` is
existential — no bound on it is claimed here.

DERIVED: no numeral. -/
theorem exists_mem_ball_of_reach (bd : Pq → List (Lk × Bool)) {V : Finset Pq} {a b : Pq}
    (h : Reach bd V a b) : ∃ n, b ∈ ball bd a n := by
  induction h with
  | refl => exact ⟨0, self_mem_ball bd a 0⟩
  | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, mem_ball_succ_of_touch bd a n hn hbc.2.2⟩

open scoped Classical in
/-- The touch-distance from `p₀`: the least `n` with `p ∈ ball bd p₀ n` when one exists, and a
sentinel value otherwise.

DERIVED: `Fintype.card Pq + 1` is that sentinel, not a bound on any distance. Every reachable
plaquette lies in a ball of radius below `Fintype.card Pq`, so the sentinel is attained only off
`p₀`'s component; the `1` puts it past every attainable distance, which is what
`touchLvl_lipschitz` needs in its off-component case. -/
noncomputable def touchLvl (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) : ℕ :=
  if h : ∃ n, p ∈ ball bd p₀ n then Nat.find h else Fintype.card Pq + 1

theorem touchLvl_self (bd : Pq → List (Lk × Bool)) (p₀ : Pq) : touchLvl bd p₀ p₀ = 0 := by
  classical
  have hex : ∃ n, p₀ ∈ ball bd p₀ n := ⟨0, self_mem_ball bd p₀ 0⟩
  rw [touchLvl, dif_pos hex]
  exact Nat.le_zero.mp (Nat.find_le (self_mem_ball bd p₀ 0))

theorem mem_ball_touchLvl (bd : Pq → List (Lk × Bool)) (p₀ p : Pq)
    (hex : ∃ n, p ∈ ball bd p₀ n) : p ∈ ball bd p₀ (touchLvl bd p₀ p) := by
  classical
  rw [touchLvl, dif_pos hex]
  exact Nat.find_spec hex

/-- **`touchLvl` rises by at most one across a touch**: `Touch bd p q` gives
`touchLvl bd p₀ q ≤ touchLvl bd p₀ p + 1`. On `p₀`'s component this is the ball recursion; off it
both sides take the sentinel value, since by `touch_symm` a touch cannot cross from the component to
its outside.

DERIVED: the `1` is one touch-step, the increment of the ball recursion. -/
theorem touchLvl_lipschitz (bd : Pq → List (Lk × Bool)) (p₀ : Pq) :
    ∀ p q : Pq, Touch bd p q → touchLvl bd p₀ q ≤ touchLvl bd p₀ p + 1 := by
  classical
  intro p q ht
  by_cases hp : ∃ n, p ∈ ball bd p₀ n
  · have hstep : q ∈ ball bd p₀ (touchLvl bd p₀ p + 1) :=
      mem_ball_succ_of_touch bd p₀ _ (mem_ball_touchLvl bd p₀ p hp) ht
    have hq : ∃ n, q ∈ ball bd p₀ n := ⟨_, hstep⟩
    rw [touchLvl, dif_pos hq]
    exact Nat.find_le hstep
  · have hq : ¬ ∃ n, q ∈ ball bd p₀ n := by
      rintro ⟨n, hn⟩
      exact hp ⟨n + 1, mem_ball_succ_of_touch bd p₀ n hn (touch_symm ht)⟩
    simp only [touchLvl, dif_neg hp, dif_neg hq]
    omega

theorem lt_touchLvl_of_not_mem_ball (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) (k : ℕ)
    (hex : ∃ n, p ∈ ball bd p₀ n) (hk : p ∉ ball bd p₀ k) : k < touchLvl bd p₀ p := by
  classical
  rw [touchLvl, dif_pos hex]
  by_contra hcon
  exact hk (ball_mono bd p₀ (Nat.le_of_not_lt hcon) (Nat.find_spec hex))

/-- **A reaching chain realises every level up to its endpoint's.** For any `lvl` that is `0` at `a`
and rises by at most one across a touch, a `Reach bd V a b` gives, for each `j ≤ lvl b`, some `c`
with `lvl c = j` and `c = a` or `c ∈ V`. `lvl` is an arbitrary function here, not `touchLvl`.

DERIVED: the `0` is the hypothesis `lvl a = 0`; the `1` is the Lipschitz step
`lvl q ≤ lvl p + 1`. -/
theorem exists_of_level_le (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (lvl : Pq → ℕ) (a : Pq)
    (hlip : ∀ p q : Pq, Touch bd p q → lvl q ≤ lvl p + 1) (h0 : lvl a = 0) {b : Pq}
    (h : Reach bd V a b) : ∀ j ≤ lvl b, ∃ c, (c = a ∨ c ∈ V) ∧ lvl c = j := by
  induction h with
  | refl =>
      intro j hj
      rw [h0] at hj
      exact ⟨a, Or.inl rfl, by omega⟩
  | tail _ hbc ih =>
      rename_i b' c' _
      intro j hj
      obtain ⟨_, hcV, ht⟩ := hbc
      have hlc := hlip b' c' ht
      rcases Nat.lt_or_ge j (lvl b' + 1) with hjb | hjb
      · exact ih j (by omega)
      · exact ⟨c', Or.inr hcV, by omega⟩

/-- **Separation forces size, in the level form.** For `lvl` with `lvl a = 0` and the Lipschitz
property, `k < lvl b` and `Reach bd V a b` give `k ≤ ((V.erase a).erase b).card`: the chain forces
`k` distinct members of `V` other than `a` and `b`, one per level in `Finset.Icc 1 k`.

DERIVED: the `0` is `lvl a = 0`; the `1` is the Lipschitz step, and also the lower end of the
interval `Finset.Icc 1 k` of levels the witnesses realise. -/
theorem card_ge_of_reach_of_lvl (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (lvl : Pq → ℕ)
    (a b : Pq) (k : ℕ) (hlip : ∀ p q : Pq, Touch bd p q → lvl q ≤ lvl p + 1) (h0 : lvl a = 0)
    (hk : k < lvl b) (hreach : Reach bd V a b) :
    k ≤ ((V.erase a).erase b).card := by
  classical
  have hsub : Finset.Icc 1 k ⊆ ((V.erase a).erase b).image lvl := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨c, hc, hlv⟩ := exists_of_level_le bd V lvl a hlip h0 hreach j (by omega)
    have hca : c ≠ a := by
      rintro rfl; rw [h0] at hlv; omega
    have hcb : c ≠ b := by
      rintro rfl; omega
    have hcV : c ∈ V := by
      rcases hc with rfl | hcV
      · exact absurd rfl hca
      · exact hcV
    exact Finset.mem_image.mpr
      ⟨c, Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, hcV⟩⟩, hlv⟩
  calc k = (Finset.Icc 1 k).card := by rw [Nat.card_Icc]; omega
    _ ≤ (((V.erase a).erase b).image lvl).card := Finset.card_le_card hsub
    _ ≤ ((V.erase a).erase b).card := Finset.card_image_le

#print axioms card_ge_of_reach_of_lvl

/-- **A bridging pair at separation more than `k` has at least `k` activated plaquettes.** If
`pd ∉ ball bd p₀ k` and `Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd`, then `k ≤ E.card + F.card`.

`card_ge_of_reach_of_lvl` at `lvl = touchLvl bd p₀`, with the `k` witnesses placed inside `E ∪ F` by
erasing `p₀` and `pd` from the ambient set. Together with `wilsonCorrConn_eq_bridging_sum` this is
what puts the separation in the exponent: each of those plaquettes costs `e^{2|β|} − 1` by
`subset_weight_bound`. The count of bridging configurations is separate, in `card_connSets_le`.

DERIVED: no numeral. -/
theorem card_ge_of_bridging (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F : Finset Pq) (k : ℕ)
    (hk : pd ∉ ball bd p₀ k)
    (hreach : Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd) :
    k ≤ E.card + F.card := by
  classical
  have hex : ∃ n, pd ∈ ball bd p₀ n := exists_mem_ball_of_reach bd hreach
  have hlt : k < touchLvl bd p₀ pd := lt_touchLvl_of_not_mem_ball bd p₀ pd k hex hk
  have hcore := card_ge_of_reach_of_lvl bd (E ∪ F ∪ {p₀, pd}) (touchLvl bd p₀) p₀ pd k
    (touchLvl_lipschitz bd p₀) (touchLvl_self bd p₀) hlt hreach
  have hsub : (((E ∪ F ∪ {p₀, pd}).erase p₀).erase pd) ⊆ E ∪ F := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxd, hx0, hxV⟩ := hx
    rcases Finset.mem_union.mp hxV with hEF | hpair
    · exact hEF
    · rcases Finset.mem_insert.mp hpair with rfl | hx'
      · exact absurd rfl hx0
      · rw [Finset.mem_singleton] at hx'; exact absurd hx' hxd
  exact le_trans (le_trans hcore (Finset.card_le_card hsub)) (Finset.card_union_le E F)

#print axioms card_ge_of_bridging

/-- **A bridging pair puts `pd` within `E.card + F.card + 1` touch-steps of `p₀`.** The converse of
`card_ge_of_bridging`: its hypothesis `pd ∉ ball bd p₀ k` is false for every
`k ≥ E.card + F.card + 1`, so `k ≤ E.card + F.card` is the strongest conclusion that hypothesis
admits, and `k + 1 ≤ E.card + F.card` would be unsatisfiable rather than stronger.

DERIVED: the `1` is the last touch-step, the one from the chain's final intermediate plaquette to
`pd` itself, which lies outside `E ∪ F`. -/
theorem mem_ball_of_bridging (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F : Finset Pq)
    (hreach : Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd) :
    pd ∈ ball bd p₀ (E.card + F.card + 1) := by
  by_contra hcon
  have hbig := card_ge_of_bridging bd p₀ pd E F (E.card + F.card + 1) hcon hreach
  omega

#print axioms mem_ball_of_bridging

/-- **Touching plaquettes are one step apart**: `Touch bd p₀ pd` gives `pd ∈ ball bd p₀ 1`. So
`card_ge_of_bridging`'s hypothesis `pd ∉ ball bd p₀ k` fails there for every `k ≥ 1`, leaving only
`k = 0`.

DERIVED: the `1` is the ball radius one touch-step reaches, `mem_ball_succ_of_touch` at `n = 0`. -/
theorem mem_ball_one_of_touch (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (ht : Touch bd p₀ pd) :
    pd ∈ ball bd p₀ 1 :=
  mem_ball_succ_of_touch bd p₀ 0 (self_mem_ball bd p₀ 0) ht

#print axioms mem_ball_one_of_touch

/-! ### The connectivity constant, read off `bd`

The connectivity constant `K` of the expansion is read off the geometry: `linkMult` counts how many
plaquettes name a given link, `touchNbrs` is the set of plaquettes touching a given one, and
`touchDeg` is the largest such set's cardinality. No numeral appears in any of these definitions.

`ball_card_le` is the statement they are for: the number of plaquettes within `n` touch-steps is at
most `(touchDeg bd + 1) ^ n`, with the lattice extent in neither side. -/

open scoped Classical in
/-- How many plaquettes name the link `l` in their boundary word.

DERIVED: no numeral. -/
noncomputable def linkMult (bd : Pq → List (Lk × Bool)) (l : Lk) : ℕ :=
  (Finset.univ.filter (fun q : Pq => l ∈ linkSupp bd q)).card

open scoped Classical in
/-- The plaquettes touching `p`, `p` itself included when it touches itself.

DERIVED: no numeral. -/
noncomputable def touchNbrs (bd : Pq → List (Lk × Bool)) (p : Pq) : Finset Pq :=
  Finset.univ.filter (fun q => Touch bd p q)

open scoped Classical in
theorem mem_touchNbrs {bd : Pq → List (Lk × Bool)} {p q : Pq} :
    q ∈ touchNbrs bd p ↔ Touch bd p q := by
  unfold touchNbrs
  simp

open scoped Classical in
/-- **A plaquette's touch-neighbours number at most the total multiplicity of its own links**:
`(touchNbrs bd p).card ≤ ∑ l ∈ linkSupp bd p, linkMult bd l`. A touch goes through a link `p` names,
so `touchNbrs bd p` sits inside the union over those links of the plaquettes naming each. Both sides
are read off `bd`.

DERIVED: no numeral. -/
theorem touchNbrs_card_le (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (touchNbrs bd p).card ≤ ∑ l ∈ linkSupp bd p, linkMult bd l := by
  classical
  have hsub : touchNbrs bd p
      ⊆ (linkSupp bd p).biUnion (fun l => Finset.univ.filter (fun q : Pq => l ∈ linkSupp bd q)) := by
    intro q hq
    obtain ⟨l, hlp, hlq⟩ := mem_touchNbrs.mp hq
    exact Finset.mem_biUnion.mpr ⟨l, hlp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlq⟩⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)

#print axioms touchNbrs_card_le

open scoped Classical in
/-- The largest number of plaquettes any one plaquette touches: the supremum of `touchNbrs` cards
over all of `Pq`, and the connectivity constant `K` the rate is built from.

DERIVED: no numeral. -/
noncomputable def touchDeg (bd : Pq → List (Lk × Bool)) : ℕ :=
  Finset.univ.sup (fun p => (touchNbrs bd p).card)

open scoped Classical in
theorem touchNbrs_card_le_touchDeg (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (touchNbrs bd p).card ≤ touchDeg bd :=
  Finset.le_sup (f := fun p => (touchNbrs bd p).card) (Finset.mem_univ p)

open scoped Classical in
/-- **The `n`-step touch-ball has at most `(touchDeg bd + 1) ^ n` plaquettes**, at every `n`. The
lattice extent appears on neither side. Induction on `n`: the ball at `n + 1` sits inside the ball at
`n` together with its plaquettes' neighbourhoods, and each contributes at most `touchDeg bd`.

DERIVED: the `1` added to `touchDeg bd` is the plaquette itself, kept alongside its at most
`touchDeg bd` neighbours at each step. -/
theorem ball_card_le (bd : Pq → List (Lk × Bool)) (p₀ : Pq) :
    ∀ n : ℕ, (ball bd p₀ n).card ≤ (touchDeg bd + 1) ^ n := by
  classical
  intro n
  induction n with
  | zero => simp [ball]
  | succ m ih =>
      have hstep : ball bd p₀ (m + 1)
          ⊆ ball bd p₀ m ∪ (ball bd p₀ m).biUnion (touchNbrs bd) := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq' | hq'
        · exact Finset.mem_union_left _ hq'
        · obtain ⟨p, hp, ht⟩ := (Finset.mem_filter.mp hq').2
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨p, hp, mem_touchNbrs.mpr ht⟩)
      have hbi : ((ball bd p₀ m).biUnion (touchNbrs bd)).card
          ≤ (ball bd p₀ m).card * touchDeg bd := by
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ p ∈ ball bd p₀ m, (touchNbrs bd p).card
            ≤ ∑ _p ∈ ball bd p₀ m, touchDeg bd :=
              Finset.sum_le_sum (fun p _ => touchNbrs_card_le_touchDeg bd p)
          _ = (ball bd p₀ m).card * touchDeg bd := by rw [Finset.sum_const, smul_eq_mul]
      have hcard : (ball bd p₀ (m + 1)).card ≤ (ball bd p₀ m).card * (touchDeg bd + 1) := by
        refine le_trans (Finset.card_le_card hstep) ?_
        refine le_trans (Finset.card_union_le _ _) ?_
        calc (ball bd p₀ m).card + ((ball bd p₀ m).biUnion (touchNbrs bd)).card
            ≤ (ball bd p₀ m).card + (ball bd p₀ m).card * touchDeg bd := by omega
          _ = (ball bd p₀ m).card * (touchDeg bd + 1) := by ring
      calc (ball bd p₀ (m + 1)).card ≤ (ball bd p₀ m).card * (touchDeg bd + 1) := hcard
        _ ≤ (touchDeg bd + 1) ^ m * (touchDeg bd + 1) := by
            exact Nat.mul_le_mul_right _ ih
        _ = (touchDeg bd + 1) ^ (m + 1) := by ring

#print axioms ball_card_le

open scoped Classical in
/-- **At most `4 ^ S.card` pairs have union `S`.** Each component of such a pair is a subset of `S`,
so the pairs inject into `S.powerset ×ˢ S.powerset`. This is what turns a double sum over pairs into
a sum over their unions.

DERIVED: the `4` is `2 * 2`, one factor of `2 ^ S.card` per component of the pair, each ranging over
the subsets of `S`. -/
theorem card_pairs_with_union_le (S : Finset Pq) :
    ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S)).card
      ≤ 4 ^ S.card := by
  classical
  have hsub : ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S))
      ⊆ S.powerset ×ˢ S.powerset := by
    intro q hq
    have hu : q.1 ∪ q.2 = S := (Finset.mem_filter.mp hq).2
    refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_powerset.mpr ?_⟩
    · rw [← hu]; exact Finset.subset_union_left
    · rw [← hu]; exact Finset.subset_union_right
  calc ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S)).card
      ≤ (S.powerset ×ˢ S.powerset).card := Finset.card_le_card hsub
    _ = 2 ^ S.card * 2 ^ S.card := by rw [Finset.card_product, Finset.card_powerset]
    _ = 4 ^ S.card := by rw [← mul_pow]; norm_num

#print axioms card_pairs_with_union_le

end ZeroCoupling

/-! ### The constant on the periodic hypercubic lattice

`touchDeg` is read off `bd` at any geometry. This section bounds it for `WilsonHypercubic.bd`, the
periodic `dim`-dimensional lattice on `Site dim n`: a link is named by at most `4 * dim` plaquettes
(four boundary-word slots, each leaving only the plane's other direction free) and a plaquette names
at most four links, so `touchDeg (bd (d := dim) (n := n)) ≤ 16 * dim`. The extent `n` appears in
neither bound.

The `4` is the length of the plaquette boundary word and `dim` is the number of directions a plane's
second axis can take. The bound is not tight: brute force over `dim, n` in `2..4 × 3..5` gives
`touchDeg = 16 * dim − 14`, that is `18, 34, 50` at `dim = 2, 3, 4`, independent of `n`. -/

section Hypercubic

open MassGap.WilsonHypercubic

variable {dim n : ℕ} [NeZero n]

/-- One periodic step back along direction `μ`: `Function.update x μ (x μ - 1)`. `unshift_shift`
records that it is a left inverse of `WilsonHypercubic.shift`.

DERIVED: the `1` is the lattice step, the same one `shift` adds; this subtracts it. -/
def unshift (μ : Fin dim) (x : Site dim n) : Site dim n :=
  Function.update x μ (x μ - 1)

theorem unshift_shift (μ : Fin dim) (x : Site dim n) :
    unshift (n := n) μ (shift μ x) = x := by
  unfold unshift shift
  rw [Function.update_self, Function.update_idem]
  simp

open scoped Classical in
/-- **A link of the periodic hypercubic lattice is named by at most `4 * dim` plaquettes**:
`linkMult (bd (d := dim) (n := n)) l ≤ 4 * dim`. The plaquettes naming `l` inject into
`Fin 4 × Fin dim` — one slot of the boundary word, and the plane's other direction — with the site
determined by the slot. The extent `n` does not enter either side.

DERIVED: the `4` is the length of `bd`'s boundary word, four links per plaquette; `dim` is the number
of choices for the plane's second direction. -/
theorem linkMult_bd_le (l : Link dim n) :
    linkMult (bd (d := dim) (n := n)) l ≤ 4 * dim := by
  classical
  obtain ⟨δ, y⟩ := l
  set g : Fin 4 × Fin dim → Plaq dim n := fun z =>
    if z.1 = 0 then ((δ, z.2), y)
    else if z.1 = 1 then ((z.2, δ), unshift (n := n) z.2 y)
    else if z.1 = 2 then ((δ, z.2), unshift (n := n) z.2 y)
    else ((z.2, δ), y) with hg
  have hsub : (Finset.univ.filter
        (fun q : Plaq dim n => (δ, y) ∈ linkSupp (bd (d := dim) (n := n)) q))
      ⊆ Finset.image g Finset.univ := by
    intro q hq
    obtain ⟨⟨μ, ν⟩, x⟩ := q
    have hmem := (Finset.mem_filter.mp hq).2
    simp only [linkSupp, bd, List.map_cons, List.map_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
    refine Finset.mem_image.mpr ?_
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact ⟨(0, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · exact ⟨(1, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg, unshift_shift]⟩
    · exact ⟨(2, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg, unshift_shift]⟩
    · exact ⟨(3, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · simp at h
  unfold linkMult
  calc (Finset.univ.filter
        (fun q : Plaq dim n => (δ, y) ∈ linkSupp (bd (d := dim) (n := n)) q)).card
      ≤ (Finset.image g Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4 × Fin dim)).card := Finset.card_image_le
    _ = 4 * dim := by simp

#print axioms linkMult_bd_le

/-- **A hypercubic plaquette names at most four links**:
`(linkSupp (bd (d := dim) (n := n)) q).card ≤ 4`, since `linkSupp` is the `toFinset` of a four-entry
boundary word and duplicates can only shrink it.

DERIVED: the `4` is the length of `bd`'s boundary word. -/
theorem linkSupp_bd_card_le (q : Plaq dim n) :
    (linkSupp (bd (d := dim) (n := n)) q).card ≤ 4 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  simp [bd]

open scoped Classical in
/-- **`touchDeg (bd (d := dim) (n := n)) ≤ 16 * dim`**, with the extent `n` on neither side.
`touchNbrs_card_le` bounds the degree by the summed multiplicity of a plaquette's own links, then
`linkSupp_bd_card_le` and `linkMult_bd_le` bound the number of terms and each term. With
`ball_card_le` this gives at most `(16 * dim + 1) ^ n` plaquettes within `n` touch-steps.

DERIVED: the `16` is `4 * 4` — `linkSupp_bd_card_le`'s four links per plaquette times
`linkMult_bd_le`'s four boundary-word slots — and `dim` is that lemma's count of second
directions. -/
theorem touchDeg_bd_le : touchDeg (bd (d := dim) (n := n)) ≤ 16 * dim := by
  classical
  refine Finset.sup_le (fun p _ => ?_)
  refine le_trans (touchNbrs_card_le (bd (d := dim) (n := n)) p) ?_
  calc ∑ l ∈ linkSupp (bd (d := dim) (n := n)) p, linkMult (bd (d := dim) (n := n)) l
      ≤ ∑ _l ∈ linkSupp (bd (d := dim) (n := n)) p, 4 * dim :=
        Finset.sum_le_sum (fun l _ => linkMult_bd_le l)
    _ = (linkSupp (bd (d := dim) (n := n)) p).card * (4 * dim) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * (4 * dim) := Nat.mul_le_mul_right _ (linkSupp_bd_card_le p)
    _ = 16 * dim := by ring

#print axioms touchDeg_bd_le

end Hypercubic

end MassGap.StrongCoupling

/-! ### The constrained outside sum, measured against `Z²`

`pairTerm_eq_core_mul_outside` factorises a surviving pair into a core anchored on `p₀` and `p_d` and
an outside that carries no observable. Resumming the surviving double sum by its core turns
`wilsonCorrConn_eq_bridging_sum` into

    ρ_conn = ∑_{cores A}  (core term)  ·  ( ∑_{E' not touching A} ζ_∅(E') )² / Z²,

the two outside sets being independent and each constrained only by not touching `A`. The
unconstrained version of the inner sum is `Z`, so what this section bounds is the ratio

    R(A) = ( ∑_{E ⊆ Ω(A)} ζ_∅(E) ) / Z,      Ω(A) = { p : p touches nothing in A }.

`Z = ∫e^{−βS}` is exponentially small in the volume, so a bound on the numerator alone divided by
`Z²` would grow with the lattice.

The constrained sum is itself a partition function. Summing `ζ_∅` over the subsets of `W` reassembles
the product that was split:

    ∑_{E ⊆ W} ∫ ∏_{p∈E} w_p  =  ∫ ∏_{p∈W} (1 + w_p)  =  ∫ ∏_{p∈W} e^{−βφ_p}  =  Z_W,

the partition function of the sub-system carrying only `W`'s plaquettes (`subset_sum_eq_subPart`).
Both `Z_W` and `Z = Z_P` are integrals of strictly positive weights, so no absolute values are
needed. Writing `S_P = S_W + S_{P∖W}` and using `φ ∈ [0,2]`,

    e^{−2β·|P∖W|} ≤ Z_P / Z_W ≤ 1        (β ≥ 0),

so `1 ≤ Z_W/Z ≤ e^{2β·|P∖W|}`. With `W = Ω(A)` the excluded set `P∖Ω(A)` is the plaquettes touching
the core, of which there are at most `touchDeg bd · |A|` by `touchNbrs_card_le_touchDeg`, with the
lattice extent nowhere in the count. Hence

    1 ≤ R(A) ≤ exp(2β · touchDeg(bd) · |A|),

depending on the core size and the connectivity constant and not on the volume. That is
`hard_core_ratio_le` and `hard_core_outside_sq_div_partition_sq_le`.

Both inequalities require `0 ≤ β`. At `β < 0` each factor `e^{−βφ}` exceeds one, the sub-system's
partition function is smaller than the full one, so `R(A) ≤ 1` while `e^{2βK|A|} < 1`, and both
directions fail. Nothing beyond `0 ≤ β` is required: there is no threshold in this ratio, and it is
stated without one.

A threshold appears when the ratio is combined with the count. Each activated plaquette costs
`e^{2β} − 1` (`subset_weight_bound`), a connected core of `n` plaquettes anchored at `p₀` is one of
at most `(touchDeg + 1)ⁿ` (`ball_card_le`), and this section contributes `e^{4β·touchDeg}` per core
plaquette. The product

    q_eff(β) = (touchDeg + 1) · (e^{2β} − 1) · e^{4β·touchDeg}

is `hardCoreRate`, and `hard_core_rate_lt_one_of_small` gives a neighbourhood of `β = 0` on which it
is below one, from `q_eff(0) = 0` and continuity rather than from a numeral.

Measured on an exact-rational `Z₂` model, where the product uniform measure is product Haar and block
independence across link-disjoint sets holds unchanged: the constrained and unconstrained sums differ
(`Z_Ω/Z = 2.3703…` against `1`), the bound holds on every core of every geometry tried, and it fails
at `β < 0` and when the degree constant is replaced by one smaller than `touchDeg`. `R(A)` at a fixed
core over rings of 5 to 14 plaquettes moved from `2.36066` to `2.37037`. -/

namespace MassGap.StrongCoupling

section HardCore

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- The Boltzmann weight of the sub-system carrying only `W`'s plaquettes:
`∏_{p ∈ W} e^{−βφ_p(U)}`. The whole lattice's weight is the case `W = univ`
(`subPart_univ_eq_partition`).

DERIVED: no numeral. -/
noncomputable def subBoltz (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) : ℝ :=
  ∏ p ∈ W, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))

/-- **`subBoltz bd β W U = exp (-(β · S_W(U)))`**, the product of exponentials being the exponential
of the partial action `∑_{p ∈ W} φ_p(U)`. Every bound below reads this form rather than the product.

DERIVED: no numeral. -/
theorem subBoltz_eq_exp (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) :
    subBoltz (Nc := Nc) bd β W U
      = Real.exp (-(β * ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U))) := by
  unfold subBoltz
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  simp

theorem subBoltz_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) : 0 < subBoltz (Nc := Nc) bd β W U := by
  rw [subBoltz_eq_exp]; exact Real.exp_pos _

theorem measurable_subBoltz (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    Measurable (subBoltz (Nc := Nc) bd β W) := by
  refine Finset.measurable_prod _ (fun p _ => Real.measurable_exp.comp ?_)
  exact (measurable_const.mul
    (measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p))).neg

/-- **The partial action over `W` is nonnegative**, each plaquette density being so by
`wilsonDensity_nonneg`, which needs `Nc ≠ 0`.

DERIVED: the first `0` is the hypothesis `Nc ≠ 0`; the second is the lower bound on the sum. -/
theorem partial_action_nonneg (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) :
    0 ≤ ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U) :=
  Finset.sum_nonneg (fun _ _ => wilsonDensity_nonneg hN _)

/-- **The partial action over `W` is at most `2 * W.card`**, one plaquette at a time. Requires
`Nc ≠ 0`.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`; the `2` is the upper end of the Wilson density's range,
`WilsonAction.wilsonDensity_le_two`. -/
theorem partial_action_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) :
    ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U) ≤ 2 * (W.card : ℝ) := by
  calc ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U) ≤ ∑ _p ∈ W, (2 : ℝ) :=
        Finset.sum_le_sum (fun p _ => wilsonDensity_le_two hN _)
    _ = 2 * (W.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **A larger plaquette set has the smaller sub-weight**: `W ⊆ W'` gives
`subBoltz bd β W' U ≤ subBoltz bd β W U`, at every configuration. Adding plaquettes adds nonnegative
action, which at `0 ≤ β` lowers the exponential. This is the lower half of the ratio bound and it
fails at `β < 0`.

DERIVED: the first `0` is the hypothesis `Nc ≠ 0`; the second is the sign hypothesis `0 ≤ β`. -/
theorem subBoltz_le_of_subset (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') (U : Lk → MassGap.SUN.SU Nc) :
    subBoltz (Nc := Nc) bd β W' U ≤ subBoltz (Nc := Nc) bd β W U := by
  rw [subBoltz_eq_exp, subBoltz_eq_exp, Real.exp_le_exp]
  have hle : ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U)
      ≤ ∑ p ∈ W', wilsonDensity (N := Nc) (wilsonHol bd p U) :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun p _ _ => wilsonDensity_nonneg hN _)
  nlinarith

/-- **And the smaller set's weight exceeds the larger's by at most `e^{2β|W'\W|}`**: for `W ⊆ W'`,
`subBoltz bd β W U ≤ exp (2 * β * (W' \ W).card) * subBoltz bd β W' U`. The dropped plaquettes carry
at most `2` of action each (`partial_action_le`). Upper half of the ratio bound, requiring `0 ≤ β`.

DERIVED: the first `0` is `Nc ≠ 0`; the second is `0 ≤ β`; the `2` is the upper end of the Wilson
density's range, one factor per dropped plaquette. -/
theorem subBoltz_le_mul (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') (U : Lk → MassGap.SUN.SU Nc) :
    subBoltz (Nc := Nc) bd β W U
      ≤ Real.exp (2 * β * ((W' \ W).card : ℝ)) * subBoltz (Nc := Nc) bd β W' U := by
  rw [subBoltz_eq_exp, subBoltz_eq_exp, ← Real.exp_add, Real.exp_le_exp]
  have hsplit : ∑ p ∈ W' \ W, wilsonDensity (N := Nc) (wilsonHol bd p U)
      + ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U)
      = ∑ p ∈ W', wilsonDensity (N := Nc) (wilsonHol bd p U) := Finset.sum_sdiff h
  have hgap := partial_action_le hN bd (W' \ W) U
  nlinarith

/-- The sub-system's partition function, `Z_W = ∫ subBoltz bd β W` against product Haar. The full
partition function is the case `W = univ`, by `subPart_univ_eq_partition`.

DERIVED: no numeral. -/
noncomputable def subPart (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) : ℝ :=
  ∫ U, subBoltz (Nc := Nc) bd β W U ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))

theorem integrable_subBoltz (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    Integrable (subBoltz (Nc := Nc) bd β W)
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  refine (integrable_const (Real.exp (2 * |β| * (Fintype.card Pq : ℝ)))).mono'
    (measurable_subBoltz bd β W).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [Real.norm_of_nonneg (subBoltz_pos bd β W U).le, subBoltz_eq_exp, Real.exp_le_exp]
  have h0 := partial_action_nonneg hN bd W U
  have h2 := partial_action_le hN bd W U
  have hW : (W.card : ℝ) ≤ (Fintype.card Pq : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ W)
  have hb : -β ≤ |β| := neg_le_abs β
  have habs : (0 : ℝ) ≤ |β| := abs_nonneg β
  nlinarith

/-- **`0 < subPart bd β W`** at every `β` and every `W`. The integrand is everywhere positive
(`subBoltz_pos`) and integrable (`integrable_subBoltz`) against a probability measure, so its support
is the whole space. No sign condition on `β` is needed.

DERIVED: the first `0` is the hypothesis `Nc ≠ 0`; the second is the strict lower bound on the
integral. -/
theorem subPart_pos (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    0 < subPart (Nc := Nc) bd β W := by
  unfold subPart
  rw [integral_pos_iff_support_of_nonneg (fun U => (subBoltz_pos bd β W U).le)
      (integrable_subBoltz hN bd β W)]
  have hsupp : Function.support (subBoltz (Nc := Nc) bd β W) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (subBoltz_pos bd β W U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

theorem subPart_le_of_subset (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') :
    subPart (Nc := Nc) bd β W' ≤ subPart (Nc := Nc) bd β W :=
  integral_mono (integrable_subBoltz hN bd β W') (integrable_subBoltz hN bd β W)
    (fun U => subBoltz_le_of_subset hN bd hβ h U)

theorem subPart_le_mul (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') :
    subPart (Nc := Nc) bd β W
      ≤ Real.exp (2 * β * ((W' \ W).card : ℝ)) * subPart (Nc := Nc) bd β W' := by
  unfold subPart
  have hmono := integral_mono (integrable_subBoltz hN bd β W)
    ((integrable_subBoltz hN bd β W').const_mul (Real.exp (2 * β * ((W' \ W).card : ℝ))))
    (fun U => subBoltz_le_mul hN bd hβ h U)
  rwa [integral_const_mul] at hmono

/-- **A product of activated weights over `E` is integrable** against product Haar: it is measurable
and bounded, and the measure is a probability measure. Requires `Nc ≠ 0`, which is what puts the
Wilson density in `[0, 2]` and so bounds each factor. The dominating constant appears in the proof,
not the statement.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. -/
theorem integrable_wprod (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (E : Finset Pq) :
    Integrable (fun U => ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hmeas : Measurable (fun U : Lk → MassGap.SUN.SU Nc =>
      ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))) :=
    Finset.measurable_prod _ (fun p _ => (measurable_wfun β).comp
      (measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p)))
  refine (integrable_const (Real.exp (2 * |β|) ^ (Fintype.card Pq))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun U => ?_))
  rw [Real.norm_eq_abs, Finset.abs_prod]
  have hone : (1 : ℝ) ≤ Real.exp (2 * |β|) := Real.one_le_exp (by positivity)
  have hstep : ∀ p ∈ E, |wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))|
      ≤ Real.exp (2 * |β|) := by
    intro p _
    rw [wfun_apply]
    have := boltz_factor_bound (β := β) (wilsonDensity_nonneg hN (wilsonHol bd p U))
      (wilsonDensity_le_two hN (wilsonHol bd p U))
    linarith
  calc ∏ p ∈ E, |wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))|
      ≤ ∏ _p ∈ E, Real.exp (2 * |β|) := Finset.prod_le_prod (fun p _ => abs_nonneg _) hstep
    _ = Real.exp (2 * |β|) ^ E.card := by rw [Finset.prod_const]
    _ ≤ Real.exp (2 * |β|) ^ (Fintype.card Pq) :=
        pow_le_pow_right₀ hone (Finset.card_le_univ E)

/-- **The outside sum over the subsets of `W` is the sub-system's partition function**:
`∑_{E ⊆ W} zw bd β ∅ E = subPart bd β W`, at every `β`. Summing the activated weights over subsets
reassembles `∏_{p∈W}(1 + w_p) = ∏_{p∈W} e^{−βφ_p}` under `Finset.prod_add`. Requires `Nc ≠ 0`, for
`integrable_wprod`.

`subPart` is an integral of an everywhere-positive weight, so the ratio `Z_W/Z` compared below needs
no absolute values.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `1` split off each factor is the same one as in
`boltz_eq_subset_sum`; the `∅` is the empty observable set, this sum carrying no plaquette
observable. -/
theorem subset_sum_eq_subPart (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    ∑ E ∈ W.powerset, zw (Nc := Nc) bd β ∅ E = subPart (Nc := Nc) bd β W := by
  classical
  have hzw : ∀ E : Finset Pq, zw (Nc := Nc) bd β ∅ E
      = ∫ U, ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
    intro E
    unfold zw
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul]
  rw [Finset.sum_congr rfl (fun E _ => hzw E),
    ← integral_finsetSum _ (fun E _ => integrable_wprod hN bd β E)]
  unfold subPart
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  unfold subBoltz
  have hone : ∀ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)) + 1 := by
    intro p; rw [wfun_apply]; ring
  have hprod : (∏ p ∈ W, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))))
      = ∏ p ∈ W, (wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)) + 1) :=
    Finset.prod_congr rfl (fun p _ => hone p)
  rw [hprod, Finset.prod_add]
  exact Finset.sum_congr rfl (fun E _ => by simp)

#print axioms subset_sum_eq_subPart

/-- **`subPart bd β Finset.univ` is the Wilson partition function.** The unconstrained outside sum is
therefore `Z`, by `subset_sum_eq_subPart` at `W = univ`.

DERIVED: no numeral. -/
theorem subPart_univ_eq_partition (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    subPart (Nc := Nc) bd β Finset.univ
      = (wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β := by
  have hpart : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
        (probHaar (MassGap.SUN.SU Nc)) β
      = ∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := rfl
  rw [hpart]
  unfold subPart
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  rw [subBoltz_eq_exp]
  unfold System.boltz
  show Real.exp (-(β * ∑ p ∈ (Finset.univ : Finset Pq),
        wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = Real.exp (-β * ∑ p, wilsonDensity (N := Nc) (wilsonHol bd p U))
  congr 1
  ring

#print axioms subPart_univ_eq_partition

/-- **The constrained outside sum is at least `Z`**: for `0 ≤ β` and any `Ω`,
`1 ≤ (∑_{E ⊆ Ω} zw bd β ∅ E) / Z`. Restricting to `Ω` removes nonnegative action, which raises the
weight. It fails at `β < 0`.

DERIVED: the first `0` is `Nc ≠ 0`; the second is the sign hypothesis `0 ≤ β`; the `1` is the value
of the ratio at `Ω = univ`, where numerator and denominator coincide by
`subPart_univ_eq_partition`. -/
theorem one_le_outside_sum_div_partition (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ}
    (hβ : 0 ≤ β) (Ω : Finset Pq) :
    1 ≤ (∑ E ∈ Ω.powerset, zw (Nc := Nc) bd β ∅ E)
      / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β) := by
  have hpos : 0 < subPart (Nc := Nc) bd β Finset.univ := subPart_pos hN bd β _
  rw [subset_sum_eq_subPart hN bd β Ω, ← subPart_univ_eq_partition bd β, le_div_iff₀ hpos,
    one_mul]
  exact subPart_le_of_subset hN bd hβ (Finset.subset_univ Ω)

#print axioms one_le_outside_sum_div_partition

/-- **The constrained outside sum divided by `Z` is at most `exp (2βn)`**, where `n` bounds `Ωᶜ.card`,
the number of plaquettes the constraint removes. Requires `0 ≤ β` and `Nc ≠ 0`. Neither side mentions
the lattice size; `n` and `β` are all that enter.

`hard_core_ratio_le` is this with `n` instantiated at the core's touch-neighbourhood.

DERIVED: the first `0` is `Nc ≠ 0` and the second is the sign hypothesis `0 ≤ β`, which is required
and is not a smallness assumption. The `2` is the upper end of the Wilson density's range, so `2βn`
is the most action `n` excluded plaquettes can carry. -/
theorem outside_sum_div_partition_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ}
    (hβ : 0 ≤ β) (Ω : Finset Pq) (n : ℕ) (hn : Ωᶜ.card ≤ n) :
    (∑ E ∈ Ω.powerset, zw (Nc := Nc) bd β ∅ E)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β)
      ≤ Real.exp (2 * β * (n : ℝ)) := by
  classical
  have hpos : 0 < subPart (Nc := Nc) bd β Finset.univ := subPart_pos hN bd β _
  rw [subset_sum_eq_subPart hN bd β Ω, ← subPart_univ_eq_partition bd β, div_le_iff₀ hpos]
  have hcard : (((Finset.univ : Finset Pq) \ Ω).card : ℝ) ≤ (n : ℝ) := by
    have hEq : (Finset.univ : Finset Pq) \ Ω = Ωᶜ := (Finset.compl_eq_univ_sdiff Ω).symm
    rw [hEq]
    exact_mod_cast hn
  have hmono : Real.exp (2 * β * (((Finset.univ : Finset Pq) \ Ω).card : ℝ))
      ≤ Real.exp (2 * β * (n : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc subPart (Nc := Nc) bd β Ω
      ≤ Real.exp (2 * β * (((Finset.univ : Finset Pq) \ Ω).card : ℝ))
          * subPart (Nc := Nc) bd β Finset.univ :=
        subPart_le_mul hN bd hβ (Finset.subset_univ Ω)
    _ ≤ Real.exp (2 * β * (n : ℝ)) * subPart (Nc := Nc) bd β Finset.univ :=
        mul_le_mul_of_nonneg_right hmono hpos.le

#print axioms outside_sum_div_partition_le

open scoped Classical in
/-- The plaquettes touching nothing in `A`: the set an outside plaquette may be drawn from once the
core `A` is fixed. `compOf_closed` makes the core touch-closed in the pair's union, so the outside
half of a factorised pair lies here.

DERIVED: no numeral. -/
noncomputable def outsideOf (bd : Pq → List (Lk × Bool)) (A : Finset Pq) : Finset Pq :=
  Finset.univ.filter (fun p => ∀ a ∈ A, ¬ Touch bd p a)

open scoped Classical in
/-- **The constraint excludes at most `touchDeg bd * A.card` plaquettes**:
`(outsideOf bd A)ᶜ.card ≤ touchDeg bd * A.card`. Each excluded plaquette is a touch-neighbour of some
member of `A`, and `touchNbrs_card_le_touchDeg` bounds each member's neighbourhood. The lattice size
appears on neither side.

DERIVED: no numeral. -/
theorem card_compl_outsideOf_le (bd : Pq → List (Lk × Bool)) (A : Finset Pq) :
    (outsideOf bd A)ᶜ.card ≤ touchDeg bd * A.card := by
  classical
  have hsub : (outsideOf bd A)ᶜ ⊆ A.biUnion (touchNbrs bd) := by
    intro p hp
    obtain ⟨a, ha, ht⟩ : ∃ a ∈ A, Touch bd p a := by
      by_contra hcon
      exact (Finset.mem_compl.mp hp)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun a ha ht => hcon ⟨a, ha, ht⟩⟩)
    exact Finset.mem_biUnion.mpr ⟨a, ha, mem_touchNbrs.mpr (touch_symm ht)⟩
  calc (outsideOf bd A)ᶜ.card ≤ (A.biUnion (touchNbrs bd)).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, (touchNbrs bd a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, touchDeg bd :=
        Finset.sum_le_sum (fun a _ => touchNbrs_card_le_touchDeg bd a)
    _ = touchDeg bd * A.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

#print axioms card_compl_outsideOf_le

open scoped Classical in
/-- **The constrained outside sum divided by `Z` lies between `1` and `exp (2β · touchDeg bd ·
A.card)`**, for every core `A`, given `Nc ≠ 0` and `0 ≤ β`. A conjunction of
`one_le_outside_sum_div_partition` and `outside_sum_div_partition_le` at `Ω = outsideOf bd A`, with
`card_compl_outsideOf_le` supplying the exclusion count.

Both bounds are functions of the core size and the connectivity constant; `Fintype.card Pq` appears
in neither. The hypotheses are `0 ≤ β` and the Wilson density's range `[0, 2]`, and there is no
smallness assumption on `β`.

This bounds one factor of the core resummation. Summing over cores needs their count at each size,
which is `card_connSets_le`, and the per-plaquette weight, which is `subset_weight_bound`.

DERIVED: the first `0` is `Nc ≠ 0` and the second is `0 ≤ β`. The `1` is the value of the ratio when
the constraint is vacuous. The `2` is the upper end of the Wilson density's range, one factor per
excluded plaquette. -/
theorem hard_core_ratio_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    (A : Finset Pq) :
    1 ≤ (∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β)
    ∧ (∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β)
      ≤ Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) :=
  ⟨one_le_outside_sum_div_partition hN bd hβ (outsideOf bd A),
   outside_sum_div_partition_le hN bd hβ (outsideOf bd A) (touchDeg bd * A.card)
     (card_compl_outsideOf_le bd A)⟩

#print axioms hard_core_ratio_le

open scoped Classical in
/-- **The product of the two constrained outside sums, over `Z²`, is at most
`exp (4β · touchDeg bd · A.card)`.** `pairTerm_eq_core_mul_outside` leaves two outside sets, each
constrained by the same core, and `wilsonCorrConn_eq_bridging_sum` carries `Z ^ 2` in its
denominator, so what multiplies each core term is the square of `hard_core_ratio_le`'s ratio.
Requires `Nc ≠ 0` and `0 ≤ β`.

DERIVED: the `0`s are `Nc ≠ 0` and `0 ≤ β`. The `2` in `Z ^ 2` is the two outside sums, and the `4`
is `hard_core_ratio_le`'s `2` doubled by squaring that bound. -/
theorem hard_core_outside_sq_div_partition_sq_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ}
    (hβ : 0 ≤ β) (A : Finset Pq) :
    ((∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E)
        * ∑ F ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ F)
      / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition
          (probHaar (MassGap.SUN.SU Nc)) β) ^ 2
      ≤ Real.exp (4 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) := by
  classical
  obtain ⟨hlo, hup⟩ := hard_core_ratio_le hN bd hβ A
  set S := ∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E with hSdef
  set Z := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hsq : S * S / Z ^ 2 = S / Z * (S / Z) := by
    rw [div_mul_div_comm, pow_two]
  have hexp : Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ))
      * Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ))
      = Real.exp (4 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsq, ← hexp]
  have hrnn : (0 : ℝ) ≤ S / Z := le_trans zero_le_one hlo
  exact mul_le_mul hup hup hrnn (Real.exp_pos _).le

#print axioms hard_core_outside_sq_div_partition_sq_le

/-! ### The threshold the ratio creates when combined with the count

The ratio bound carries no smallness assumption. A threshold in `β` appears when it is multiplied by
the two other factors the core sum pays: the per-plaquette Boltzmann weight `e^{2β} − 1`
(`subset_weight_bound`) and the geometric branching `touchDeg + 1` (`ball_card_le`). That product is
`hardCoreRate`. It is `0` at `β = 0` and continuous, so `hard_core_rate_lt_one_of_small` places it
below one on a neighbourhood of zero without naming a numeral. -/

/-- The effective per-plaquette rate of the core sum:
`hardCoreRate K β = (K + 1) · (e^{2β} − 1) · e^{4βK}`, the branching factor times the activated
weight times the hard core's own factor. `K` is a parameter, instantiated at `touchDeg bd` by the
callers.

DERIVED: the `1` added to `K` is `stepSet`'s stay-put step, the same one in `ball_card_le`. The `1`
subtracted is `boltz_factor_bound`'s, the factor at zero coupling. The `2` in `e^{2β}` is the upper
end of `wilsonDensity`'s range; the `4` is that `2` doubled by the two outside sums of
`hard_core_outside_sq_div_partition_sq_le`. -/
noncomputable def hardCoreRate (K : ℕ) (β : ℝ) : ℝ :=
  ((K : ℝ) + 1) * (Real.exp (2 * β) - 1) * Real.exp (4 * β * (K : ℝ))

theorem hardCoreRate_at_zero (K : ℕ) : hardCoreRate K 0 = 0 := by
  unfold hardCoreRate; simp

theorem continuous_hardCoreRate (K : ℕ) : Continuous (hardCoreRate K) := by
  unfold hardCoreRate
  fun_prop

/-- **There is a `b > 0` with `hardCoreRate K β < 1` for every `β` in `[0, b)`.** The rate is `0` at
`β = 0` (`hardCoreRate_at_zero`) and continuous (`continuous_hardCoreRate`), so it is below one on a
neighbourhood. `b` is existential and depends on `K`; no value for it is named.

DERIVED: the `0`s are the coupling at which the rate vanishes, the lower end of the interval, and the
strict lower bound on `b`. The `1` is the threshold the rate is compared against, the value at which
a geometric series stops converging. -/
theorem hard_core_rate_lt_one_of_small (K : ℕ) :
    ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → hardCoreRate K β < 1 := by
  have hlt : hardCoreRate K 0 < 1 := by rw [hardCoreRate_at_zero]; norm_num
  have ht : Filter.Tendsto (hardCoreRate K) (nhds 0) (nhds (hardCoreRate K 0)) :=
    (continuous_hardCoreRate K).continuousAt
  have hev : ∀ᶠ x in nhds (0 : ℝ), hardCoreRate K x < 1 := ht.eventually_lt_const hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun β hβ0 hβ => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
  exact hβ

#print axioms hard_core_rate_lt_one_of_small

/-! ### The shape after the hard core is bounded

With the ratio bounded, the surviving sum reads

    ρ_conn = ∑_{cores (X,Y)} pairTerm(X,Y) · R(A)²,   1 ≤ R(A) ≤ e^{2β·touchDeg·|A|},

and `|pairTerm(X,Y)| ≤ 4·(e^{2|β|}−1)^{|X|+|Y|}` by `subset_weight_bound`, the two plaquette
observables being bounded by `2` each. The remaining factor is the number of cores at each size:
how many touch-connected sets containing `p₀` and `p_d` have `|X| + |Y| = n`. `ball_card_le` bounds
the `n`-step ball, which is a different count; `card_connSets_le` is the one this needs. -/

/-! ### Where the hard-core bound is consumed

`pairTerm_eq_core_mul_outside` factorises each surviving pair. `CoreResummation` is the statement
that the double sum over pairs regroups as a sum over cores times the constrained outside sums;
`coreResummation_holds` proves it at the canonical witnesses. Given it,
`wilsonCorrConn_abs_le_of_coreResummation` converts a bound on the cores alone into a bound on the
connected correlation, with `Z²` discharged by `hard_core_outside_sq_div_partition_sq_le`. -/

open scoped Classical in
/-- The proposition that the bridging sum regroups by core: for a finite family `cores` and an
assignment `core` naming each one's touch-closed set,

    ∑ over bridging q, pairTerm q = ∑ c ∈ cores, pairTerm c · (outside sum)²,

the outside sums being taken over the subsets of `outsideOf bd (core c)`.

The underlying map is `(E, F) ↦ ((E ∩ A, F ∩ A), (E \ A, F \ A))` between bridging pairs and cores
paired with outside pairs confined to `outsideOf A`. `pairTerm_eq_core_mul_outside` gives the summand
identity and `compOf_closed` the separator; the content is the reindexing of the sum.
`coreResummation_holds` proves it at `corePairs` and `coreSpan`. It stays a `def` because
`wilsonCorrConn_abs_le_of_coreResummation` takes the cores and the core map as parameters.

DERIVED: no numeral. -/
def CoreResummation (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (cores : Finset (Finset Pq × Finset Pq)) (core : Finset Pq × Finset Pq → Finset Pq) : Prop :=
  ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
    pairTerm (Nc := Nc) bd p₀ pd β q
  = ∑ c ∈ cores, pairTerm (Nc := Nc) bd p₀ pd β c
      * ((∑ E ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ E)
        * ∑ F ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ F)

open scoped Classical in
/-- **The resummation identity for a pair of plaquette FAMILIES.**

`CoreResummation` is the same statement for two single plaquettes: the reach-filtered sum of
`pairTerm` equals a sum over cores of `pairTerm` times the outside partition functions squared. This
replaces `pairTerm` by `pairTermF` and the two-point reach condition by the one
`bridging_sum_eq_core_sumF` proves the identity for: every plaquette of `Ao ∪ Bo` reachable from a
base point `a`, within the configuration together with `Ao ∪ Bo`.

That is not the condition `wilsonCorrConnF_eq_bridging_sumF` produces. That one filters on
`∃ b ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b` — SOME plaquette of `Bo` reachable
from SOME plaquette of `Ao`, not every plaquette reachable from one base point. The two coincide for
single plaquettes, where `Ao ∪ Bo` is two points, which is why `coreResummation_holds` composes
directly and this one does not. `reach_filter_iff_of_connected` supplies the join: the filters are
equal whenever each anchor family is internally touch-connected, which is the hypothesis
`wilsonCorrConnF_eq_bridging_sumF` already imposes on `Ao`, plus its mirror for `Bo`.

Why it is wanted. `wilsonCorrConn_abs_le_of_coreResummation` is generic in the core family — it takes
`cores` and `core` as arguments — but its conclusion is fixed to the single-plaquette
`wilsonCorrConn` and to `pairTerm`, so the family case cannot reuse it.
`coreResummationF_holds` proves this predicate in one line over `bridging_sum_eq_core_sumF`;
`wilsonCorrConnF_abs_le_of_coreResummationF` is the matching bound step; and
`wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` composes them with `corePairsF_sum_le`, so the
strong-coupling estimate reaches products of plaquette observables rather than single ones.

DERIVED: no numeral occurs. `a`, `Ao`, `Bo`, `β`, `cores` and `core` are the caller's. -/
def CoreResummationF (bd : Pq → List (Lk × Bool)) (a : Pq) (Ao Bo : Finset Pq) (β : ℝ)
    (cores : Finset (Finset Pq × Finset Pq)) (core : Finset Pq × Finset Pq → Finset Pq) : Prop :=
  ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => ∀ p ∈ Ao ∪ Bo, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p),
    pairTermF (Nc := Nc) bd Ao Bo β q
  = ∑ c ∈ cores, pairTermF (Nc := Nc) bd Ao Bo β c
      * ((∑ E ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ E)
        * ∑ F ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ F)

#print axioms CoreResummationF


open scoped Classical in
/-- **A bound on the cores alone bounds the connected correlation.** Given `Nc ≠ 0`, `p₀ ≠ pd`,
`0 ≤ β`, the integrability condition, a `CoreResummation` at `cores` and `core`, and

    ∑ c ∈ cores, |pairTerm bd p₀ pd β c| · exp (4β · touchDeg bd · (core c).card) ≤ M,

then `|wilsonCorrConn bd p₀ β pd| ≤ M`.

No partition function appears in the hypothesis: `hard_core_outside_sq_div_partition_sq_le` cancels
the `Z ^ 2` of `wilsonCorrConn_eq_bridging_sum` against the constrained outside sums, core by core.
Each summand of the hypothesis is bounded per core by `subset_weight_bound` and the core's own size,
so what the bound depends on is the number of cores at each size.

DERIVED: the first `0` is `Nc ≠ 0`, the second the sign hypothesis `0 ≤ β`. The `1` in `hint`'s
`Real.exp (-(β * φ_p)) - 1` is `boltz_eq_subset_sum`'s activated weight. The `4` is
`hard_core_outside_sq_div_partition_sq_le`'s, the Wilson density's `2` doubled by the two outside
sums. -/
theorem wilsonCorrConn_abs_le_of_coreResummation (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) (hne : p₀ ≠ pd) {β : ℝ} (hβ : 0 ≤ β)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
    (cores : Finset (Finset Pq × Finset Pq)) (core : Finset Pq × Finset Pq → Finset Pq)
    (hres : CoreResummation (Nc := Nc) bd p₀ pd β cores core) (M : ℝ)
    (hM : ∑ c ∈ cores, |pairTerm (Nc := Nc) bd p₀ pd β c|
            * Real.exp (4 * β * ((touchDeg bd * (core c).card : ℕ) : ℝ)) ≤ M) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd| ≤ M := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  rw [wilsonCorrConn_eq_bridging_sum hN bd p₀ pd hne β hint, hres, Finset.sum_div]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum ?_) hM)
  intro c _
  set S := ∑ E ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ E with hSdef
  set Z := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hsq := hard_core_outside_sq_div_partition_sq_le hN bd hβ (core c)
  have hone := one_le_outside_sum_div_partition hN bd hβ (outsideOf bd (core c))
  have hSpos : 0 < S := by
    have h1 : 1 * Z ≤ S := (le_div_iff₀ hZpos).mp hone
    rw [one_mul] at h1
    exact lt_of_lt_of_le hZpos h1
  have hrnn : 0 ≤ S * S / Z ^ 2 := div_nonneg (by positivity) (by positivity)
  calc |pairTerm (Nc := Nc) bd p₀ pd β c * (S * S) / Z ^ 2|
      = |pairTerm (Nc := Nc) bd p₀ pd β c| * (S * S / Z ^ 2) := by
        rw [mul_div_assoc, abs_mul, abs_of_nonneg hrnn]
    _ ≤ |pairTerm (Nc := Nc) bd p₀ pd β c|
          * Real.exp (4 * β * ((touchDeg bd * (core c).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

#print axioms wilsonCorrConn_abs_le_of_coreResummation

open scoped Classical in
/-- **A core plaquette with a nonempty link support is excluded from its own outside set**: `a ∈ A`
and `(linkSupp bd a).Nonempty` give `a ∉ outsideOf bd A`, since `a` touches itself through any of its
own links.

So `outsideOf bd A` is a proper subset whenever `A` is nonempty and its plaquettes have boundary
words, and the constrained sum of `hard_core_ratio_le` is not the unconstrained one. Measured in an
exact-rational `Z₂` model, the two sums differ by a factor `2.37` at `A.card = 1` on a ring, and that
factor converges rather than growing as the ring is enlarged.

DERIVED: no numeral. -/
theorem not_mem_outsideOf_self (bd : Pq → List (Lk × Bool)) (A : Finset Pq) {a : Pq} (ha : a ∈ A)
    (hne : (linkSupp bd a).Nonempty) : a ∉ outsideOf bd A := by
  classical
  intro hmem
  obtain ⟨l, hl⟩ := hne
  exact (Finset.mem_filter.mp hmem).2 a ha ⟨l, hl, hl⟩

#print axioms not_mem_outsideOf_self

end HardCore

end MassGap.StrongCoupling

-- ==== BEGIN connected-set count (lattice animal) ====

/-! ### Counting connected plaquette sets

`card_ge_of_bridging` says a surviving pair is large; the count of such pairs is separate, and it is
the last place `Fintype.card Pq` could enter. What `card_connSets_le` gives is

    #{ S : S touch-connected, p₀ ∈ S, |S| = m }  ≤  ((touchDeg bd + 1)^2)^m

with the lattice extent on neither side. Routing it through `ball_card_le` would not do: the ball has
at most `(touchDeg+1)^m` members and its subsets number `2^((touchDeg+1)^m)`. The argument is an
injection instead of a containment.

A touch-connected set of size `m` rooted at `p₀` is the entry set of a walk from `p₀` of length
`2m − 1`: start at `p₀`, and whenever a neighbour of the covered part is still uncovered, step into
it and step back — two steps per new plaquette, `m − 1` of them (`exists_walk_exact`). Distinct sets
have distinct entry sets, so the count is at most the number of such walks, and a walk is a sequence
of steps into `stepSet`, of size at most `touchDeg + 1` — the neighbours, plus staying put, which is
what lets every walk be padded to a common length (`isWalk_pad`). Hence
`K = (touchDeg bd + 1)^2`.

`walks` is built by `biUnion` over the step set rather than filtered out of `List Pq`, which is what
gives `walks_card_le` a cardinality to bound.

`card_rooted_pairs_ge` is the control on the connectedness hypothesis: the size-two sets containing
`p₀` number `Fintype.card Pq − 1` exactly, so without connectedness the count carries the whole
volume. `compOf_mem_connSets` is what supplies connectedness from a bridging pair. -/


namespace MassGap.StrongCoupling

section AnimalCount

variable {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- Where one step of a walk may land: `insert p (touchNbrs bd p)`, a touch-neighbour of `p` or `p`
itself. Staying put is what lets walks of different lengths be padded to a common length
(`isWalk_pad`), and it costs one in the branching factor.

DERIVED: no numeral. -/
noncomputable def stepSet (bd : Pq → List (Lk × Bool)) (p : Pq) : Finset Pq :=
  insert p (touchNbrs bd p)

theorem self_mem_stepSet (bd : Pq → List (Lk × Bool)) (p : Pq) : p ∈ stepSet bd p :=
  Finset.mem_insert_self _ _

theorem mem_stepSet_of_touch {bd : Pq → List (Lk × Bool)} {p q : Pq} (h : Touch bd p q) :
    q ∈ stepSet bd p :=
  Finset.mem_insert_of_mem (mem_touchNbrs.mpr h)

/-- **One step has at most `touchDeg bd + 1` destinations**:
`(stepSet bd p).card ≤ touchDeg bd + 1`, from `Finset.card_insert_le` and
`touchNbrs_card_le_touchDeg`.

DERIVED: the `1` is the stay-put destination `p` itself, inserted into `touchNbrs bd p`. -/
theorem stepSet_card_le (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (stepSet bd p).card ≤ touchDeg bd + 1 := by
  have h1 := Finset.card_insert_le p (touchNbrs bd p)
  have h2 := touchNbrs_card_le_touchDeg bd p
  unfold stepSet
  omega

/-- **`List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)`.** The two-element step of a
chain, stated here so that the proofs below do not carry a library spelling.

DERIVED: no numeral. -/
theorem ischain_cc {R : Pq → Pq → Prop} {a b : Pq} {l : List Pq} :
    List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l) := by
  simp

/-- **A one-element list is a chain**, for any relation `R`.

DERIVED: no numeral. -/
theorem ischain_one {R : Pq → Pq → Prop} (a : Pq) : List.IsChain R [a] := by
  simp

/-- A plaquette list whose head is `p₀` and whose consecutive entries are related by `stepSet`:
each moves to a touch-neighbour or stays put.

DERIVED: no numeral. -/
def IsWalk (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (w : List Pq) : Prop :=
  w.head? = some p₀ ∧ List.IsChain (fun x y => y ∈ stepSet bd x) w

theorem IsWalk.head_eq {bd : Pq → List (Lk × Bool)} {p₀ : Pq} {w : List Pq}
    (h : IsWalk bd p₀ w) : w.head? = some p₀ := h.1

theorem IsWalk.chain {bd : Pq → List (Lk × Bool)} {p₀ : Pq} {w : List Pq}
    (h : IsWalk bd p₀ w) : List.IsChain (fun x y => y ∈ stepSet bd x) w := h.2

theorem IsWalk.cons_eq {bd : Pq → List (Lk × Bool)} {p₀ : Pq} {w : List Pq}
    (h : IsWalk bd p₀ w) : ∃ t, w = p₀ :: t := by
  cases w with
  | nil => exact absurd h.head_eq (by simp)
  | cons u t =>
      refine ⟨t, ?_⟩
      have hu : u = p₀ := by simpa using h.head_eq
      rw [hu]

theorem IsWalk.mem_head {bd : Pq → List (Lk × Bool)} {p₀ : Pq} {w : List Pq}
    (h : IsWalk bd p₀ w) : p₀ ∈ w := by
  obtain ⟨t, hw⟩ := h.cons_eq
  rw [hw]
  simp

/-- The lists of `k + 1` plaquettes that start at `p` and step, as a `Finset`. Assembled by `biUnion`
over `stepSet` rather than filtered out of `List Pq`, which is what gives `walks_card_le` something
to bound. `mem_walks_of_isWalk` records that every `IsWalk` of that length belongs.

DERIVED: the `0` and the `1` are the recursion's base and step. A zero-step walk is the single list
`[p]`, and each further step prepends one plaquette drawn from `stepSet`. -/
noncomputable def walks (bd : Pq → List (Lk × Bool)) : ℕ → Pq → Finset (List Pq)
  | 0, p => {[p]}
  | (k + 1), p => (stepSet bd p).biUnion (fun q => (walks bd k q).image (fun l => p :: l))

theorem walks_zero (bd : Pq → List (Lk × Bool)) (p : Pq) : walks bd 0 p = {[p]} := rfl

theorem walks_succ (bd : Pq → List (Lk × Bool)) (k : ℕ) (p : Pq) :
    walks bd (k + 1) p
      = (stepSet bd p).biUnion (fun q => (walks bd k q).image (fun l => p :: l)) := rfl

/-- **`(walks bd k p).card ≤ (touchDeg bd + 1) ^ k`**, at every `k` and every start. Induction on
`k` through `stepSet_card_le`: each step multiplies the count by at most the branching factor. The
lattice extent appears on neither side.

DERIVED: the `1` added to `touchDeg bd` is `stepSet`'s stay-put destination; the exponent `k` is the
number of steps, one factor per step. -/
theorem walks_card_le (bd : Pq → List (Lk × Bool)) (k : ℕ) (p : Pq) :
    (walks bd k p).card ≤ (touchDeg bd + 1) ^ k := by
  induction k generalizing p with
  | zero => simp [walks_zero]
  | succ k ih =>
      rw [walks_succ]
      refine le_trans Finset.card_biUnion_le ?_
      calc ∑ q ∈ stepSet bd p, ((walks bd k q).image (fun l => p :: l)).card
          ≤ ∑ _q ∈ stepSet bd p, (touchDeg bd + 1) ^ k :=
            Finset.sum_le_sum (fun q _ => le_trans Finset.card_image_le (ih q))
        _ = (stepSet bd p).card * (touchDeg bd + 1) ^ k := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (touchDeg bd + 1) * (touchDeg bd + 1) ^ k :=
            Nat.mul_le_mul_right _ (stepSet_card_le bd p)
        _ = (touchDeg bd + 1) ^ (k + 1) := by ring

#print axioms walks_card_le

/-- **An `IsWalk bd p w` of length `k + 1` belongs to `walks bd k p`.** This is what lets
`walks_card_le` bound a set of walks described by the predicate rather than by the construction.

DERIVED: the `1` is the walk's own head: a `k`-step walk has `k + 1` entries. -/
theorem mem_walks_of_isWalk (bd : Pq → List (Lk × Bool)) :
    ∀ (k : ℕ) (p : Pq) (w : List Pq), IsWalk bd p w → w.length = k + 1 → w ∈ walks bd k p := by
  intro k
  induction k with
  | zero =>
      intro p w hw hlen
      obtain ⟨t, rfl⟩ := hw.cons_eq
      cases t with
      | nil => simp [walks_zero]
      | cons a b => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
      intro p w hw hlen
      obtain ⟨t, rfl⟩ := hw.cons_eq
      cases t with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons q t' =>
          have hchain := hw.chain
          rw [ischain_cc] at hchain
          have hq : IsWalk bd q (q :: t') := ⟨by simp, hchain.2⟩
          have hlen' : (q :: t').length = k + 1 := by
            simp only [List.length_cons] at hlen ⊢
            omega
          have hmem := ih q (q :: t') hq hlen'
          rw [walks_succ]
          exact Finset.mem_biUnion.mpr ⟨q, hchain.1, Finset.mem_image.mpr ⟨_, hmem, rfl⟩⟩

/-! #### Padding

`walks bd k p` fixes one length, while a covering walk may be shorter than `2m − 1`. Repeating the
start is a legal step, `stepSet` containing the plaquette itself, and it changes neither the head nor
the set of entries. `isWalk_pad` is the statement. -/

theorem isWalk_cons_self {bd : Pq → List (Lk × Bool)} {p₀ : Pq} {w : List Pq}
    (h : IsWalk bd p₀ w) : IsWalk bd p₀ (p₀ :: w) := by
  obtain ⟨t, hw⟩ := h.cons_eq
  refine ⟨by simp, ?_⟩
  rw [hw]
  refine ischain_cc.mpr ⟨self_mem_stepSet bd p₀, ?_⟩
  rw [← hw]
  exact h.chain

theorem toFinset_cons_self {p₀ : Pq} {w : List Pq} (h : p₀ ∈ w) :
    (p₀ :: w).toFinset = w.toFinset := by
  rw [List.toFinset_cons, Finset.insert_eq_self]
  exact List.mem_toFinset.mpr h

theorem isWalk_pad (bd : Pq → List (Lk × Bool)) (p₀ : Pq) :
    ∀ (i : ℕ) (w : List Pq), IsWalk bd p₀ w →
      ∃ w', IsWalk bd p₀ w' ∧ w'.toFinset = w.toFinset ∧ w'.length = w.length + i := by
  intro i
  induction i with
  | zero => intro w hw; exact ⟨w, hw, rfl, rfl⟩
  | succ i ih =>
      intro w hw
      obtain ⟨w', hw', hf, hl⟩ := ih w hw
      refine ⟨p₀ :: w', isWalk_cons_self hw', ?_, ?_⟩
      · rw [toFinset_cons_self hw'.mem_head, hf]
      · simp only [List.length_cons, hl]
        omega

/-! #### The detour

`isWalk_detour` adds one plaquette to a walk's entry set at a cost of exactly two in length. -/

theorem head?_append_congr {a b c : List Pq} (h : b.head? = c.head?) :
    (a ++ b).head? = (a ++ c).head? := by
  cases a with
  | nil => simpa using h
  | cons u a' => simp

/-- **Splicing `y, x, y` in for one occurrence of `y` keeps a chain a chain**, given `R y x` and
`R x y`. Proved by induction on the prefix, so only the two-element step `ischain_cc` is needed.
`R` is an arbitrary relation here, not `stepSet`.

DERIVED: no numeral. -/
theorem ischain_detour {R : Pq → Pq → Prop} {y x : Pq} (h1 : R y x) (h2 : R x y) :
    ∀ (a b : List Pq), List.IsChain R (a ++ y :: b) → List.IsChain R (a ++ y :: x :: y :: b) := by
  intro a
  induction a with
  | nil =>
      intro b h
      simp only [List.nil_append] at h ⊢
      exact ischain_cc.mpr ⟨h1, ischain_cc.mpr ⟨h2, h⟩⟩
  | cons u a' ih =>
      intro b h
      cases a' with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h ⊢
          obtain ⟨huy, hrest⟩ := ischain_cc.mp h
          exact ischain_cc.mpr ⟨huy, ischain_cc.mpr ⟨h1, ischain_cc.mpr ⟨h2, hrest⟩⟩⟩
      | cons v a'' =>
          simp only [List.cons_append] at h ⊢
          obtain ⟨huv, hrest⟩ := ischain_cc.mp h
          refine ischain_cc.mpr ⟨huv, ?_⟩
          have hstep := ih b (by simpa using hrest)
          simpa using hstep

/-- **One new plaquette costs two steps.** A walk `w` from `p₀` that visits `y`, with `Touch bd y x`,
extends to a walk `w'` with `w'.toFinset = insert x w.toFinset` and `w'.length = w.length + 2`. The
entry set gains `x` and nothing else. Both `Touch bd y x` and its symmetric form are used, by
`touch_symm`, since the detour steps out and back.

DERIVED: the `2` is the detour's length, one step out to `x` and one back to `y`. -/
theorem isWalk_detour (bd : Pq → List (Lk × Bool)) (p₀ : Pq) {w : List Pq}
    (hw : IsWalk bd p₀ w) {y x : Pq} (hy : y ∈ w) (ht : Touch bd y x) :
    ∃ w', IsWalk bd p₀ w' ∧ w'.toFinset = insert x w.toFinset ∧ w'.length = w.length + 2 := by
  classical
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hy
  refine ⟨a ++ y :: x :: y :: b, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [head?_append_congr (a := a) (b := y :: x :: y :: b) (c := y :: b) (by simp)]
    exact hw.head_eq
  · exact ischain_detour (mem_stepSet_of_touch ht) (mem_stepSet_of_touch (touch_symm ht))
      a b hw.chain
  · ext u
    simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    tauto
  · simp only [List.length_append, List.length_cons]
    omega

/-! #### Connectedness supplies the next plaquette

`exists_boundary_of_reach` turns a reach that leaves `W` into a touch across `W`'s boundary, which
`isWalk_detour` then consumes; `exists_walk_cover` iterates the two. -/

/-- **A reach out of `W` produces a boundary touch.** If `a ∈ W` and `Reach bd V a b`, then either
`b ∈ W` or there are `y ∈ W` and `x ∈ V \ W` with `Touch bd y x`.

DERIVED: no numeral. -/
theorem exists_boundary_of_reach (bd : Pq → List (Lk × Bool)) (V W : Finset Pq) (a : Pq)
    (ha : a ∈ W) {b : Pq} (h : Reach bd V a b) :
    b ∈ W ∨ ∃ y ∈ W, ∃ x ∈ V, x ∉ W ∧ Touch bd y x := by
  classical
  induction h with
  | refl => exact Or.inl ha
  | tail hab hbc ih =>
      obtain ⟨hbV, hcV, ht⟩ := hbc
      rcases ih with hb | hfound
      · exact (Classical.em _).imp id (fun hc => ⟨_, hb, _, hcV, hc, ht⟩)
      · exact Or.inr hfound

/-- **A walk inside a connected `S` extends to one covering `S`, at two steps per new plaquette.**
Given `S` touch-connected from `p₀`, a walk `w` with `w.toFinset ⊆ S` and
`S.card ≤ w.toFinset.card + j`, there is a `w'` with `w'.toFinset = S` and
`w'.length + 2 * w.toFinset.card ≤ w.length + 2 * S.card`. The induction runs on the fuel `j`, not
on `S`.

DERIVED: both `2`s are `isWalk_detour`'s detour length, one detour per plaquette added. -/
theorem exists_walk_cover (bd : Pq → List (Lk × Bool)) (S : Finset Pq) (p₀ : Pq)
    (hconn : ∀ q ∈ S, Reach bd S p₀ q) :
    ∀ (j : ℕ) (w : List Pq), IsWalk bd p₀ w → w.toFinset ⊆ S → S.card ≤ w.toFinset.card + j →
      ∃ w', IsWalk bd p₀ w' ∧ w'.toFinset = S ∧
        w'.length + 2 * w.toFinset.card ≤ w.length + 2 * S.card := by
  classical
  intro j
  induction j with
  | zero =>
      intro w hw hsub hcard
      have hEq : w.toFinset = S := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact ⟨w, hw, hEq, by rw [hEq]⟩
  | succ j ih =>
      intro w hw hsub hcard
      by_cases hfull : w.toFinset = S
      · exact ⟨w, hw, hfull, by rw [hfull]⟩
      · obtain ⟨z, hzS, hzW⟩ : ∃ z ∈ S, z ∉ w.toFinset := by
          by_contra hcon
          refine hfull (Finset.Subset.antisymm hsub (fun u hu => ?_))
          by_contra hu2
          exact hcon ⟨u, hu, hu2⟩
        have hp0 : p₀ ∈ w.toFinset := List.mem_toFinset.mpr hw.mem_head
        rcases exists_boundary_of_reach bd S w.toFinset p₀ hp0 (hconn z hzS) with
          hz | ⟨y, hyW, x, hxS, hxW, ht⟩
        · exact absurd hz hzW
        · obtain ⟨w₁, hw₁, hf₁, hl₁⟩ := isWalk_detour bd p₀ hw (List.mem_toFinset.mp hyW) ht
          have hcard₁ : w₁.toFinset.card = w.toFinset.card + 1 := by
            rw [hf₁, Finset.card_insert_of_notMem hxW]
          have hsub₁ : w₁.toFinset ⊆ S := by
            rw [hf₁]
            exact Finset.insert_subset_iff.mpr ⟨hxS, hsub⟩
          obtain ⟨w', hw', hfS, hlen⟩ := ih w₁ hw₁ hsub₁ (by omega)
          exact ⟨w', hw', hfS, by omega⟩

/-- **A set touch-connected from `p₀ ∈ S` is the entry set of a walk with
`w.length + 2 ≤ 1 + 2 * S.card`.** `exists_walk_cover` started from the one-element walk `[p₀]`.

DERIVED: the `2`s are `isWalk_detour`'s detour length; the `1`s are the single starting entry `p₀`,
which costs no step. -/
theorem exists_walk_of_connected (bd : Pq → List (Lk × Bool)) (S : Finset Pq) (p₀ : Pq)
    (h0 : p₀ ∈ S) (hconn : ∀ q ∈ S, Reach bd S p₀ q) :
    ∃ w, IsWalk bd p₀ w ∧ w.toFinset = S ∧ w.length + 2 ≤ 1 + 2 * S.card := by
  classical
  have hstart : IsWalk bd p₀ [p₀] := ⟨by simp, ischain_one _⟩
  have hone : ([p₀] : List Pq).toFinset = {p₀} := by simp
  have hsub : ([p₀] : List Pq).toFinset ⊆ S := by
    rw [hone]
    exact Finset.singleton_subset_iff.mpr h0
  have hcard1 : ([p₀] : List Pq).toFinset.card = 1 := by rw [hone]; simp
  obtain ⟨w, hw, hfS, hlen⟩ :=
    exists_walk_cover bd S p₀ hconn S.card [p₀] hstart hsub (by omega)
  refine ⟨w, hw, hfS, ?_⟩
  rw [hcard1] at hlen
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- **A set touch-connected from `p₀ ∈ S` is the entry set of a walk of exactly
`2 * S.card - 1` entries.** `exists_walk_of_connected` followed by `isWalk_pad`, which stretches a
shorter walk to the common length without changing its entry set. The subtraction is on `ℕ`.

DERIVED: the `2` is `isWalk_detour`'s detour length, two entries per plaquette; the `1` subtracted is
the start `p₀`, counted once rather than twice. -/
theorem exists_walk_exact (bd : Pq → List (Lk × Bool)) (S : Finset Pq) (p₀ : Pq)
    (h0 : p₀ ∈ S) (hconn : ∀ q ∈ S, Reach bd S p₀ q) :
    ∃ w, IsWalk bd p₀ w ∧ w.toFinset = S ∧ w.length = 2 * S.card - 1 := by
  obtain ⟨w, hw, hfS, hlen⟩ := exists_walk_of_connected bd S p₀ h0 hconn
  obtain ⟨w', hw', hf', hl'⟩ := isWalk_pad bd p₀ (2 * S.card - 1 - w.length) w hw
  exact ⟨w', hw', by rw [hf', hfS], by omega⟩

/-! #### The count -/

open scoped Classical in
/-- The plaquette sets of size `m` containing `p₀` in which every member is touch-reachable from `p₀`
inside the set itself. `compOf_mem_connSets` is what puts a bridging pair's component here.

DERIVED: no numeral. -/
noncomputable def connSets (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (m : ℕ) : Finset (Finset Pq) :=
  Finset.univ.filter (fun S => p₀ ∈ S ∧ (∀ q ∈ S, Reach bd S p₀ q) ∧ S.card = m)

open scoped Classical in
theorem mem_connSets {bd : Pq → List (Lk × Bool)} {p₀ : Pq} {m : ℕ} {S : Finset Pq} :
    S ∈ connSets bd p₀ m ↔ p₀ ∈ S ∧ (∀ q ∈ S, Reach bd S p₀ q) ∧ S.card = m := by
  rw [connSets, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ _)

open scoped Classical in
/-- **`(connSets bd p₀ m).card ≤ (touchDeg bd + 1) ^ (2 * m - 2)`.** The touch-connected sets of size
`m` containing `p₀` inject into `walks bd (2 * m - 2) p₀` by `exists_walk_exact` and
`mem_walks_of_isWalk`, and `walks_card_le` counts those. The `m = 0` case holds because `connSets`
is empty there, `p₀` belonging to no set of size zero.

The exponent is the number of steps: a walk covering `m` plaquettes takes `2(m − 1)` of them, and
each chooses among at most `touchDeg bd + 1` destinations. `Fintype.card Pq` appears neither in the
statement nor in the proof.

DERIVED: the `1` added to `touchDeg bd` is `stepSet`'s stay-put destination. The `2` multiplying `m`
is `isWalk_detour`'s two steps per plaquette, and the `2` subtracted removes the root's own, which
costs none. -/
theorem card_connSets_le_steps (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (m : ℕ) :
    (connSets bd p₀ m).card ≤ (touchDeg bd + 1) ^ (2 * m - 2) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hempty : connSets bd p₀ 0 = ∅ := by
      ext S
      constructor
      · intro hS
        obtain ⟨h0, -, hc⟩ := mem_connSets.mp hS
        rw [Finset.card_eq_zero] at hc
        subst hc
        exact absurd h0 (Finset.notMem_empty p₀)
      · intro hS
        exact absurd hS (Finset.notMem_empty S)
    rw [hempty]
    simp
  · have hsub : connSets bd p₀ m ⊆ (walks bd (2 * m - 2) p₀).image List.toFinset := by
      intro S hS
      obtain ⟨h0, hconn, hcard⟩ := mem_connSets.mp hS
      obtain ⟨w, hw, hfS, hlen⟩ := exists_walk_exact bd S p₀ h0 hconn
      refine Finset.mem_image.mpr ⟨w, ?_, hfS⟩
      refine mem_walks_of_isWalk bd (2 * m - 2) p₀ w hw ?_
      omega
    calc (connSets bd p₀ m).card
        ≤ ((walks bd (2 * m - 2) p₀).image List.toFinset).card := Finset.card_le_card hsub
      _ ≤ (walks bd (2 * m - 2) p₀).card := Finset.card_image_le
      _ ≤ (touchDeg bd + 1) ^ (2 * m - 2) := walks_card_le bd _ p₀

#print axioms card_connSets_le_steps

/-- **`(connSets bd p₀ m).card ≤ ((touchDeg bd + 1) ^ 2) ^ m`.** `card_connSets_le_steps` with the
exponent raised from `2m − 2` to `2m`, which weakens it by one factor of `(touchDeg bd + 1) ^ 2` and
puts it in the `K ^ m` shape the resummation sums.

DERIVED: the `1` is `stepSet`'s stay-put destination; the `2` is the two steps a detour costs, so
`K = (touchDeg bd + 1) ^ 2` is the per-plaquette branching. Both are read off `bd`. -/
theorem card_connSets_le (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (m : ℕ) :
    (connSets bd p₀ m).card ≤ ((touchDeg bd + 1) ^ 2) ^ m := by
  calc (connSets bd p₀ m).card
      ≤ (touchDeg bd + 1) ^ (2 * m - 2) := card_connSets_le_steps bd p₀ m
    _ ≤ (touchDeg bd + 1) ^ (2 * m) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ((touchDeg bd + 1) ^ 2) ^ m := pow_mul _ 2 m

#print axioms card_connSets_le

open scoped Classical in
/-- **The same bound with `pd ∈ S` demanded as well.** The extra membership only shrinks the filtered
set, so `card_connSets_le` applies unchanged. The connectedness required is reach from `p₀`, not from
`pd`.

DERIVED: the `1` is `stepSet`'s stay-put destination; the `2` is the two steps a detour costs, both
inherited from `card_connSets_le`. -/
theorem card_connSets_bridging_le (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (m : ℕ) :
    (Finset.univ.filter (fun S : Finset Pq =>
        p₀ ∈ S ∧ pd ∈ S ∧ (∀ q ∈ S, Reach bd S p₀ q) ∧ S.card = m)).card
      ≤ ((touchDeg bd + 1) ^ 2) ^ m := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_connSets_le bd p₀ m)
  intro S hS
  obtain ⟨h0, -, hconn, hcard⟩ := (Finset.mem_filter.mp hS).2
  exact mem_connSets.mpr ⟨h0, hconn, hcard⟩

#print axioms card_connSets_bridging_le

open scoped Classical in
/-- **The same bound with `pd ∈ S` demanded, at the `2 * m - 2` exponent.**
`card_connSets_le_steps` in place of `card_connSets_le`, for a caller that wants the factor of `K`
that `card_connSets_bridging_le` gives away.

DERIVED: the `1` is `stepSet`'s stay-put destination; the `2`s are the two steps per plaquette and
the root's exemption, both inherited from `card_connSets_le_steps`. -/
theorem card_connSets_bridging_le_steps (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (m : ℕ) :
    (Finset.univ.filter (fun S : Finset Pq =>
        p₀ ∈ S ∧ pd ∈ S ∧ (∀ q ∈ S, Reach bd S p₀ q) ∧ S.card = m)).card
      ≤ (touchDeg bd + 1) ^ (2 * m - 2) := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_connSets_le_steps bd p₀ m)
  intro S hS
  obtain ⟨h0, -, hconn, hcard⟩ := (Finset.mem_filter.mp hS).2
  exact mem_connSets.mpr ⟨h0, hconn, hcard⟩

#print axioms card_connSets_bridging_le_steps

open scoped Classical in
/-- **The pairs whose union is touch-connected through `p₀` and has size `m` number at most
`(4 * (touchDeg bd + 1) ^ 2) ^ m`.** The expansion sums over pairs, not over unions, so
`card_connSets_le` is paid once more against `card_pairs_with_union_le`, which carries a fixed union
of size `m` by at most `4 ^ m` pairs. Note the filter asks nothing about `pd`.

DERIVED: the `4` is `card_pairs_with_union_le`'s, two subsets of the union per component of the pair.
The `1` is `stepSet`'s stay-put destination and the `2` is the two steps a detour costs, both from
`card_connSets_le`. -/
theorem card_bridging_pairs_le (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (m : ℕ) :
    ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q =>
        p₀ ∈ q.1 ∪ q.2 ∧ (∀ r ∈ q.1 ∪ q.2, Reach bd (q.1 ∪ q.2) p₀ r)
          ∧ (q.1 ∪ q.2).card = m)).card
      ≤ (4 * (touchDeg bd + 1) ^ 2) ^ m := by
  classical
  have hsub : ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q =>
        p₀ ∈ q.1 ∪ q.2 ∧ (∀ r ∈ q.1 ∪ q.2, Reach bd (q.1 ∪ q.2) p₀ r)
          ∧ (q.1 ∪ q.2).card = m))
      ⊆ (connSets bd p₀ m).biUnion (fun S =>
          (Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S)) := by
    intro q hq
    obtain ⟨h0, hconn, hcard⟩ := (Finset.mem_filter.mp hq).2
    exact Finset.mem_biUnion.mpr ⟨q.1 ∪ q.2, mem_connSets.mpr ⟨h0, hconn, hcard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc ∑ S ∈ connSets bd p₀ m,
        ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S)).card
      ≤ ∑ _S ∈ connSets bd p₀ m, 4 ^ m := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hc := card_pairs_with_union_le S
        rw [(mem_connSets.mp hS).2.2] at hc
        exact hc
    _ = (connSets bd p₀ m).card * 4 ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ((touchDeg bd + 1) ^ 2) ^ m * 4 ^ m :=
        Nat.mul_le_mul_right _ (card_connSets_le bd p₀ m)
    _ = (4 * (touchDeg bd + 1) ^ 2) ^ m := by rw [mul_pow]; ring

#print axioms card_bridging_pairs_le

/-! #### What the expansion hands the count -/

/-- **A reach inside `V` to a point of `V` is a reach inside `compOf bd V a`.** The witnessing chain
never leaves the component, so the component is touch-connected as a set in its own right. That is
what `connSets` requires and what `compOf_closed` alone does not give.

DERIVED: no numeral. -/
theorem reach_compOf (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) {p : Pq}
    (h : Reach bd V a p) : p ∈ V → Reach bd (compOf bd V a) a p := by
  classical
  induction h with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      intro _
      obtain ⟨hbV, hcV, ht⟩ := hbc
      exact (ih hbV).tail
        ⟨mem_compOf.mpr ⟨hbV, hab⟩, mem_compOf.mpr ⟨hcV, hab.tail ⟨hbV, hcV, ht⟩⟩, ht⟩

#print axioms reach_compOf

open scoped Classical in
/-- **`compOf bd V p₀ ∈ connSets bd p₀ (compOf bd V p₀).card`**, given `p₀ ∈ V`. The component a
bridging pair supplies is one of the counted sets, so `card_connSets_le` applies to it. Its size is
whatever it is; no bound on it is claimed here.

DERIVED: no numeral. -/
theorem compOf_mem_connSets (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (p₀ : Pq) (h : p₀ ∈ V) :
    compOf bd V p₀ ∈ connSets bd p₀ (compOf bd V p₀).card := by
  classical
  refine mem_connSets.mpr ⟨self_mem_compOf h, ?_, rfl⟩
  intro q hq
  obtain ⟨hqV, hqR⟩ := mem_compOf.mp hq
  exact reach_compOf bd V p₀ hqR hqV

#print axioms compOf_mem_connSets

open scoped Classical in
/-- **The sets of size two containing `p₀` number at least `Fintype.card Pq - 1`.** One per other
plaquette, by the injection `x ↦ {p₀, x}` from `Finset.univ.erase p₀`. No constant read off `bd`
bounds this, so the connectedness hypothesis of `card_connSets_le` is what keeps the lattice size out
of that count.

DERIVED: the `2` is the size the filter demands; the `1` subtracted is `p₀` itself, excluded from the
injection's domain. -/
theorem card_rooted_pairs_ge (p₀ : Pq) :
    Fintype.card Pq - 1
      ≤ (Finset.univ.filter (fun S : Finset Pq => p₀ ∈ S ∧ S.card = 2)).card := by
  classical
  have hcard : (Finset.univ.erase p₀).card = Fintype.card Pq - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun x => insert p₀ {x}) ?_ ?_
  · intro x hx
    have hxp : x ≠ p₀ := (Finset.mem_erase.mp hx).1
    have h2 : (insert p₀ ({x} : Finset Pq)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hxp)]
      simp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self _ _, h2⟩
  · intro x hx y _ hxy
    have hxp : x ≠ p₀ := (Finset.mem_erase.mp (Finset.mem_coe.mp hx)).1
    have hxy' : (insert p₀ ({x} : Finset Pq)) = insert p₀ ({y} : Finset Pq) := hxy
    have hx' : x ∈ insert p₀ ({y} : Finset Pq) := by
      rw [← hxy']
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self x)
    rcases Finset.mem_insert.mp hx' with h | h
    · exact absurd h hxp
    · exact Finset.mem_singleton.mp h

#print axioms card_rooted_pairs_ge

end AnimalCount

section AnimalHypercubic

open MassGap.WilsonHypercubic

variable {dim n : ℕ} [NeZero n]

open scoped Classical in
/-- **`(connSets (bd (d := dim) (n := n)) p₀ m).card ≤ ((16 * dim + 1) ^ 2) ^ m`.**
`card_connSets_le` with `touchDeg_bd_le` substituted for the degree. The extent `n` appears on
neither side.

DERIVED: the `16 * dim` is `touchDeg_bd_le`'s bound on the degree; the `1` is `stepSet`'s stay-put
destination; the `2` is the two steps a detour costs. -/
theorem card_connSets_le_hypercubic (p₀ : Plaq dim n) (m : ℕ) :
    (connSets (bd (d := dim) (n := n)) p₀ m).card ≤ ((16 * dim + 1) ^ 2) ^ m := by
  classical
  refine le_trans (card_connSets_le _ p₀ m) ?_
  have hdeg : touchDeg (bd (d := dim) (n := n)) + 1 ≤ 16 * dim + 1 := by
    have := touchDeg_bd_le (dim := dim) (n := n)
    omega
  exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hdeg 2) m

#print axioms card_connSets_le_hypercubic

open scoped Classical in
/-- **`(connSets (bd (d := dim) (n := n)) p₀ m).card ≤ (16 * dim + 1) ^ (2 * m - 2)`.**
`card_connSets_le_steps` with `touchDeg_bd_le` substituted, keeping the step exponent.

DERIVED: the `16 * dim` is `touchDeg_bd_le`'s bound; the `1` is the stay-put destination; the `2`
multiplying `m` is the two steps per plaquette and the `2` subtracted is the root's exemption. -/
theorem card_connSets_le_steps_hypercubic (p₀ : Plaq dim n) (m : ℕ) :
    (connSets (bd (d := dim) (n := n)) p₀ m).card ≤ (16 * dim + 1) ^ (2 * m - 2) := by
  classical
  refine le_trans (card_connSets_le_steps _ p₀ m) ?_
  have hdeg : touchDeg (bd (d := dim) (n := n)) + 1 ≤ 16 * dim + 1 := by
    have := touchDeg_bd_le (dim := dim) (n := n)
    omega
  exact Nat.pow_le_pow_left hdeg _

#print axioms card_connSets_le_steps_hypercubic

end AnimalHypercubic

end MassGap.StrongCoupling
-- ==== END connected-set count (lattice animal) ====

-- ==== BEGIN core resummation ====

/-! ### The core resummation, and the per-pair magnitude bound

`CoreResummation` is a reindexing of the double sum: a bijection between bridging pairs and cores
paired with outside pairs. `bridging_sum_eq_core_sum` proves it at the canonical witnesses and
`coreResummation_holds` states the result in the form the consumer takes.

The map. For a bridging pair `(E, F)` put `A = compOf bd (E ∪ F ∪ {p₀, p_d}) p₀`, `p₀`'s
touch-component of the pair's own union. Then

    (E, F)  ↦  ( (E ∩ A, F ∩ A) , (E ∖ A, F ∖ A) ),   inverse  ((X,Y),(X',Y')) ↦ (X ∪ X', Y ∪ Y').

The core `A` depends on the pair, so this is a fibration rather than a product: the sum is regrouped
by `Finset.sum_fiberwise_of_maps_to` over the fibres of `(E, F) ↦ (E ∩ A, F ∩ A)`, and each fibre is
put in bijection with the square of `outsideOf A`'s powerset by `Finset.sum_nbij'`.

Three facts make the fibre exact, each proved below:

* `A` is recoverable from the core alone. `A ⊆ E ∪ F ∪ {p₀, p_d}` with `p₀, p_d ∈ A` gives
  `A = (E ∩ A) ∪ (F ∩ A) ∪ {p₀, p_d}`, the core's own span (`coreSpan`, `coreSpan_eq_of_mem_crs`).
  That is what lets `CoreResummation`'s `core` be a function of the core pair.
* The core is its own component: a reach chain inside `V` never leaves `p₀`'s component of `V`, so
  `compOf bd A p₀ = A`. That is `IsCorePair`, and it is the image of the forward map.
* A core and its outside are disjoint (`not_mem_coreSpan_of_mem_outsideOf_crs`). Every plaquette of a
  core touches another one — `p₀` because the core bridges to `p_d ≠ p₀`, every other because it is
  reached along a chain — so none survives `outsideOf`. Without it the outside data would not be
  recoverable from the union. It is the only place `p₀ ≠ p_d` is used.

The magnitude bound is `pairTerm_abs_le`: `|pairTerm (E, F)| ≤ 8 · q ^ (|E| + |F|)` with
`q = e^{2|β|} − 1`. `zw_abs_le` gives `|zw D E| ≤ 2^{|D|} · q^{|E|}`, each plaquette observable lying
in `[0, 2]` (`wilsonPlaqObs_le_two`) and each activated weight being bounded by `q`
(`subset_weight_bound`); the two products of the connected numerator contribute `2²·2⁰ = 4` and
`2¹·2¹ = 4`.

Measured on the exact-rational `Z₂` model (`code/certify/z2_polymer_hard_core.py`), on rings: a
plaquette chain is degenerate there, its holonomies independent and every connected correlator zero,
so a chain check would be vacuous. On rings of 5, 6 and 7 both directions of the bijection are exact,
the fibres partition the bridging pairs (912, 3312 and 12240 of them, against 912, 3312 and 11808
cores), and the two sums agree as rationals: `27/16384`, `81/262144`, `243/4194304`, none zero. -/

namespace MassGap.StrongCoupling

section CoreResum

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-! #### The geometry of a core -/

/-- **`Reach` is monotone in its ambient set**: `V ⊆ W` carries `Reach bd V a b` to `Reach bd W a b`.

DERIVED: no numeral. -/
theorem reach_mono_crs (bd : Pq → List (Lk × Bool)) {V W : Finset Pq} (hVW : V ⊆ W) {a b : Pq}
    (h : Reach bd V a b) : Reach bd W a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail ⟨hVW hstep.1, hVW hstep.2.1, hstep.2.2⟩

#print axioms reach_mono_crs

/-- **`Reach` is symmetric.** `Touch` is symmetric — `touch_symm`, two plaquettes sharing a link —
and the ambient membership conditions are symmetric in the two endpoints, so the step relation is
symmetric and its reflexive-transitive closure inherits that.

DERIVED: no numeral occurs. -/
theorem reach_symm {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {a b : Pq}
    (h : Reach bd V a b) : Reach bd V b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, touch_symm hstep.2.2⟩ ih

#print axioms reach_symm

/-- **The two reach filters agree when both anchor families are internally connected.**

This is the join the family case was missing. `wilsonCorrConnF_eq_bridging_sumF` expresses
`wilsonCorrConnF` as a sum filtered on *some* plaquette of `Bo` being reachable from *some*
plaquette of `Ao`; `bridging_sum_eq_core_sumF` resums the sum filtered on *every* plaquette of
`Ao ∪ Bo` being reachable from the single base point `a`. Those are different conditions, and
without this lemma the two do not compose.

They agree under the hypothesis `wilsonCorrConnF_eq_bridging_sumF` already imposes on `Ao` —
internal touch-connectedness — together with its mirror for `Bo`. Backwards is immediate: `a ∈ Ao`
and `b ∈ Bo` are the witnesses. Forwards is the chain `a → a' → b' → b → p`, whose middle link is
the existential's witness and whose last two links need `reach_symm`. A connected family is exactly
what a Wilson loop is, so this asks nothing the intended callers do not already satisfy.

It is invisible in the single-plaquette case: there `Ao ∪ Bo` is two points, both conditions read
`Reach bd V p₀ pd`, and `coreResummation_holds` composes without any of this.

DERIVED: no numeral occurs. `Ao`, `Bo`, `a`, `b` and `q` are the caller's. -/
theorem reach_filter_iff_of_connected (bd : Pq → List (Lk × Bool)) {Ao Bo : Finset Pq} {a b : Pq}
    (ha : a ∈ Ao) (hb : b ∈ Bo)
    (hconnA : ∀ p ∈ Ao, Reach bd Ao a p) (hconnB : ∀ p ∈ Bo, Reach bd Bo b p)
    (q : Finset Pq × Finset Pq) :
    (∃ b' ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b')
      ↔ ∀ p ∈ Ao ∪ Bo, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p := by
  have hAV : Ao ⊆ q.1 ∪ q.2 ∪ (Ao ∪ Bo) :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_union_left _ hx)
  have hBV : Bo ⊆ q.1 ∪ q.2 ∪ (Ao ∪ Bo) :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
  constructor
  · rintro ⟨b', hb', a', ha', hr⟩ p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact reach_mono_crs bd hAV (hconnA p h)
    · have h1 : Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a a' :=
        reach_mono_crs bd hAV (hconnA a' ha')
      have h2 : Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) b' b :=
        reach_symm (reach_mono_crs bd hBV (hconnB b' hb'))
      have h3 : Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) b p :=
        reach_mono_crs bd hBV (hconnB p h)
      exact ((h1.trans hr).trans h2).trans h3
  · intro h
    exact ⟨b, hb, a, ha, h b (Finset.mem_union_right _ hb)⟩

#print axioms reach_filter_iff_of_connected

open scoped Classical in
/-- **`compOf bd (compOf bd V a) a = compOf bd V a`.** A reach chain from `a` inside `V` never leaves
`a`'s component, so restricting the ambient set to that component loses nothing.

DERIVED: no numeral. -/
theorem compOf_idem_crs (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) :
    compOf bd (compOf bd V a) a = compOf bd V a := by
  apply Finset.Subset.antisymm
  · intro x hx
    exact (mem_compOf.mp hx).1
  · intro x hx
    refine mem_compOf.mpr ⟨hx, ?_⟩
    have hrx : Reach bd V a x := (mem_compOf.mp hx).2
    clear hx
    induction hrx with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact ih.tail ⟨mem_compOf.mpr ⟨hbc.1, hab⟩,
          mem_compOf.mpr ⟨hbc.2.1, hab.tail hbc⟩, hbc.2.2⟩

#print axioms compOf_idem_crs

/-- The span of a core pair: `c.1 ∪ c.2 ∪ {p₀, pd}`, its two halves together with the two anchors.
This is the `core` function `CoreResummation` takes — a set read off the core pair alone, with no
reference to the bridging pair it came from.

DERIVED: no numeral. -/
def coreSpan (p₀ pd : Pq) (c : Finset Pq × Finset Pq) : Finset Pq :=
  c.1 ∪ c.2 ∪ {p₀, pd}

theorem mem_coreSpan_left (p₀ pd : Pq) (c : Finset Pq × Finset Pq) : p₀ ∈ coreSpan p₀ pd c := by
  simp [coreSpan]

theorem mem_coreSpan_right (p₀ pd : Pq) (c : Finset Pq × Finset Pq) : pd ∈ coreSpan p₀ pd c := by
  simp [coreSpan]

theorem fst_subset_coreSpan (p₀ pd : Pq) (c : Finset Pq × Finset Pq) : c.1 ⊆ coreSpan p₀ pd c := by
  intro x hx; simp [coreSpan, hx]

theorem snd_subset_coreSpan (p₀ pd : Pq) (c : Finset Pq × Finset Pq) : c.2 ⊆ coreSpan p₀ pd c := by
  intro x hx; simp [coreSpan, hx]

/-- **`coreSpan p₀ pd (E ∩ A, F ∩ A) = A`**, given `A ⊆ E ∪ F ∪ {p₀, pd}`, `p₀ ∈ A` and `pd ∈ A`. A
set caught between the anchors and the pair's union is the span of the pair it cuts down to. A
`Finset` identity, with no reachability in it: this is what makes `core` a function of the core pair
rather than of the bridging pair.

DERIVED: no numeral. -/
theorem coreSpan_eq_of_mem_crs (A E F : Finset Pq) (p₀ pd : Pq)
    (hAV : A ⊆ E ∪ F ∪ {p₀, pd}) (h0 : p₀ ∈ A) (hd : pd ∈ A) :
    coreSpan p₀ pd (E ∩ A, F ∩ A) = A := by
  ext x
  simp only [coreSpan, Finset.mem_union, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ((⟨-, h⟩ | ⟨-, h⟩) | (rfl | rfl))
    · exact h
    · exact h
    · exact h0
    · exact hd
  · intro hx
    have hxV := hAV hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxV
    rcases hxV with (h | h) | (h | h)
    · exact Or.inl (Or.inl ⟨h, hx⟩)
    · exact Or.inl (Or.inr ⟨h, hx⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

#print axioms coreSpan_eq_of_mem_crs

open scoped Classical in
/-- **A bridging pair's component is the span of the core it cuts down to.**
`coreSpan_eq_of_mem_crs` at `A = compOf bd (E ∪ F ∪ {p₀, pd}) p₀`; the bridging hypothesis is what
puts `pd` in that component.

DERIVED: no numeral. -/
theorem coreSpan_core_eq_crs (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F : Finset Pq)
    (hbr : Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd) :
    coreSpan p₀ pd (E ∩ compOf bd (E ∪ F ∪ {p₀, pd}) p₀,
                    F ∩ compOf bd (E ∪ F ∪ {p₀, pd}) p₀)
      = compOf bd (E ∪ F ∪ {p₀, pd}) p₀ :=
  coreSpan_eq_of_mem_crs (compOf bd (E ∪ F ∪ {p₀, pd}) p₀) E F p₀ pd
    (fun _ hx => (mem_compOf.mp hx).1)
    (self_mem_compOf (by simp))
    (mem_compOf.mpr ⟨by simp, hbr⟩)

#print axioms coreSpan_core_eq_crs

open scoped Classical in
/-- A pair is a core when its span is exactly `p₀`'s touch-component of that span: nothing in it is
detached from `p₀`, and `pd` is reached because `pd` lies in the span.

DERIVED: no numeral. -/
def IsCorePair (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (c : Finset Pq × Finset Pq) : Prop :=
  compOf bd (coreSpan p₀ pd c) p₀ = coreSpan p₀ pd c

open scoped Classical in
/-- The pairs satisfying `IsCorePair`, as a `Finset`: the index set `coreResummation_holds` sums
over.

DERIVED: no numeral. -/
noncomputable def corePairs (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) :
    Finset (Finset Pq × Finset Pq) :=
  Finset.univ.filter (fun c => IsCorePair bd p₀ pd c)

open scoped Classical in
theorem mem_corePairs {bd : Pq → List (Lk × Bool)} {p₀ pd : Pq} {c : Finset Pq × Finset Pq} :
    c ∈ corePairs bd p₀ pd ↔ IsCorePair bd p₀ pd c := by
  rw [corePairs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- **A core pair's span is one of the counted connected sets**:
`coreSpan p₀ pd c ∈ connSets bd p₀ (coreSpan p₀ pd c).card` for every `IsCorePair`.
`compOf_mem_connSets` rewritten along the `IsCorePair` equation.

The reindexing lands on `p₀`'s component, not on a connected union, which is what lets it compose
with the count: a span is touch-connected as a set in its own right, so `card_connSets_le` applies
with no side condition. A bridging pair's union need not be connected as a whole.

One span carries more than one core pair — `c.1` and `c.2` are two subsets whose union with the
anchors is the span — so counting `corePairs` needs `card_corePairs_span_le` for the ordered splits
alongside `card_connSets_le` for the spans.

DERIVED: no numeral. -/
theorem coreSpan_mem_connSets (bd : Pq → List (Lk × Bool)) {p₀ pd : Pq}
    {c : Finset Pq × Finset Pq} (hc : IsCorePair bd p₀ pd c) :
    coreSpan p₀ pd c ∈ connSets bd p₀ (coreSpan p₀ pd c).card := by
  have h := compOf_mem_connSets bd (coreSpan p₀ pd c) p₀ (mem_coreSpan_left p₀ pd c)
  rwa [hc] at h

#print axioms coreSpan_mem_connSets

open scoped Classical in
/-- **Cutting a bridging pair down to `p₀`'s component produces a core pair.** The forward map of the
resummation lands in `corePairs`, by `coreSpan_core_eq_crs` and `compOf_idem_crs`.

DERIVED: no numeral. -/
theorem isCorePair_of_bridging (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F : Finset Pq)
    (hbr : Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd) :
    IsCorePair bd p₀ pd (E ∩ compOf bd (E ∪ F ∪ {p₀, pd}) p₀,
                         F ∩ compOf bd (E ∪ F ∪ {p₀, pd}) p₀) := by
  unfold IsCorePair
  rw [coreSpan_core_eq_crs bd p₀ pd E F hbr]
  exact compOf_idem_crs bd _ p₀

#print axioms isCorePair_of_bridging

open scoped Classical in
/-- **A member of a core's outside is not in the core's span.** For an `IsCorePair` with `p₀ ≠ pd`,
`z ∈ outsideOf bd (coreSpan p₀ pd c)` gives `z ∉ coreSpan p₀ pd c`. Every plaquette of the span
touches another one — reached along its own chain — so none survives the `outsideOf` filter. `p₀` is
the case needing `p₀ ≠ pd`: a core reaches `pd`, so `p₀`'s chain to it has a first step.

Without this the union `c.1 ∪ X` would not determine `(c.1, X)` and the reindexing in
`bridging_sum_eq_core_sum` would not be injective.

DERIVED: no numeral. -/
theorem not_mem_coreSpan_of_mem_outsideOf_crs (bd : Pq → List (Lk × Bool)) {p₀ pd : Pq}
    (hne : p₀ ≠ pd) {c : Finset Pq × Finset Pq} (hc : IsCorePair bd p₀ pd c) {z : Pq}
    (hz : z ∈ outsideOf bd (coreSpan p₀ pd c)) : z ∉ coreSpan p₀ pd c := by
  intro hzA
  have hout : ∀ b ∈ coreSpan p₀ pd c, ¬ Touch bd z b := (Finset.mem_filter.mp hz).2
  have hreach : Reach bd (coreSpan p₀ pd c) p₀ z := by
    have hzc : z ∈ compOf bd (coreSpan p₀ pd c) p₀ := by rw [hc]; exact hzA
    exact (mem_compOf.mp hzc).2
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨y, -, hstep⟩
  · rw [hEq] at hout
    have hpd : Reach bd (coreSpan p₀ pd c) p₀ pd := by
      have hm : pd ∈ compOf bd (coreSpan p₀ pd c) p₀ := by
        rw [hc]; exact mem_coreSpan_right p₀ pd c
      exact (mem_compOf.mp hm).2
    rcases Relation.ReflTransGen.cases_head hpd with hEq2 | ⟨y, hy, -⟩
    · exact hne hEq2
    · exact hout y hy.2.1 hy.2.2
  · exact hout y hstep.1 (touch_symm hstep.2.2)

#print axioms not_mem_coreSpan_of_mem_outsideOf_crs

open scoped Classical in
/-- **`W \ compOf bd V a ⊆ outsideOf bd (compOf bd V a)`**, for `W ⊆ V`. What falls outside the
component touches nothing inside it, by `compOf_closed`, so it is confined to the set the hard-core
bound is stated against.

DERIVED: no numeral. -/
theorem sdiff_compOf_subset_outsideOf_crs (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq)
    {W : Finset Pq} (hW : W ⊆ V) :
    W \ compOf bd V a ⊆ outsideOf bd (compOf bd V a) := by
  intro p hp
  rw [Finset.mem_sdiff] at hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, ?_⟩
  intro z hz ht
  exact compOf_closed bd V a z (Finset.mem_inter.mpr ⟨(mem_compOf.mp hz).1, hz⟩)
    p (Finset.mem_sdiff.mpr ⟨hW hp.1, hp.2⟩) (touch_symm ht)

#print axioms sdiff_compOf_subset_outsideOf_crs

open scoped Classical in
/-- **A core rebuilt with an untouching outside has the core's span as its component**:
`compOf bd ((c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ {p₀, pd}) p₀ = coreSpan p₀ pd c` when `X` and `Y` lie in
`outsideOf bd (coreSpan p₀ pd c)` and `c` is a core pair. Plaquettes touching nothing in the span
cannot extend `p₀`'s reach, so the rebuilt pair lands on the fibre it came from. This is the inverse
direction of the reindexing in `bridging_sum_eq_core_sum`.

DERIVED: no numeral. -/
theorem compOf_union_outside_crs (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    {c : Finset Pq × Finset Pq} (hc : IsCorePair bd p₀ pd c) {X Y : Finset Pq}
    (hX : X ⊆ outsideOf bd (coreSpan p₀ pd c)) (hY : Y ⊆ outsideOf bd (coreSpan p₀ pd c)) :
    compOf bd ((c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ {p₀, pd}) p₀ = coreSpan p₀ pd c := by
  have hAV : coreSpan p₀ pd c ⊆ (c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ {p₀, pd} := by
    intro x hx
    simp only [coreSpan, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have hout : ∀ z ∈ (c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ {p₀, pd}, z ∉ coreSpan p₀ pd c →
      z ∈ outsideOf bd (coreSpan p₀ pd c) := by
    intro z hz hzn
    by_cases h1 : z ∈ X
    · exact hX h1
    · by_cases h2 : z ∈ Y
      · exact hY h2
      · exfalso
        apply hzn
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [coreSpan, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
  apply Finset.Subset.antisymm
  · intro x hx
    have hrx : Reach bd ((c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ {p₀, pd}) p₀ x := (mem_compOf.mp hx).2
    clear hx
    induction hrx with
    | refl => exact mem_coreSpan_left p₀ pd c
    | tail _ hbc ih =>
        by_contra hcon
        exact (Finset.mem_filter.mp (hout _ hbc.2.1 hcon)).2 _ ih (touch_symm hbc.2.2)
  · intro x hx
    refine mem_compOf.mpr ⟨hAV hx, ?_⟩
    have hxc : x ∈ compOf bd (coreSpan p₀ pd c) p₀ := by rw [hc]; exact hx
    exact reach_mono_crs bd hAV (mem_compOf.mp hxc).2

#print axioms compOf_union_outside_crs

/-! #### The reindexing -/

/-- **`T * ((∑_P w) * (∑_P w)) = ∑_{P ×ˢ P} T * (w x.1 * w x.2)`.** A scalar times the square of a
finite sum, rewritten as a sum over the product of index pairs — the shape `Finset.sum_nbij'` needs
on the right-hand side in `bridging_sum_eq_core_sum`. The index type is arbitrary.

DERIVED: the `1` and `2` in `x.1` and `x.2` are projections, not numerals. -/
theorem mul_sq_sum_eq_sum_product_crs {ι : Type*} (T : ℝ) (P : Finset ι) (w : ι → ℝ) :
    T * ((∑ E ∈ P, w E) * ∑ F ∈ P, w F) = ∑ x ∈ P ×ˢ P, T * (w x.1 * w x.2) := by
  rw [Finset.sum_product]
  dsimp only
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]

#print axioms mul_sq_sum_eq_sum_product_crs

open scoped Classical in
/-- **The bridging sum equals the sum over core pairs of the core term times its two constrained
outside sums**, for `p₀ ≠ pd` and every `β`. `Finset.sum_fiberwise_of_maps_to` over the fibres of
`(E, F) ↦ (E ∩ A, F ∩ A)`, then `Finset.sum_nbij'` on each fibre against
`(outsideOf bd (coreSpan p₀ pd c)).powerset ×ˢ` itself, with `pairTerm_eq_core_mul_outside` as the
summand identity and `compOf_closed` as the separator. Nothing measure-theoretic enters.

DERIVED: the `∅`s are the empty observable set, the outside sums carrying no plaquette observable.
The `1` and `2` in `q.1`, `q.2`, `c.1`, `c.2` are projections, not numerals. -/
theorem bridging_sum_eq_core_sum (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd)
    (β : ℝ) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
      pairTerm (Nc := Nc) bd p₀ pd β q
    = ∑ c ∈ corePairs bd p₀ pd, pairTerm (Nc := Nc) bd p₀ pd β c
        * ((∑ E ∈ (outsideOf bd (coreSpan p₀ pd c)).powerset, zw (Nc := Nc) bd β ∅ E)
          * ∑ F ∈ (outsideOf bd (coreSpan p₀ pd c)).powerset, zw (Nc := Nc) bd β ∅ F) := by
  refine Eq.trans (Finset.sum_fiberwise_of_maps_to (t := corePairs bd p₀ pd)
      (g := fun q : Finset Pq × Finset Pq =>
        (q.1 ∩ compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀,
         q.2 ∩ compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)) ?_ _).symm ?_
  · intro q hq
    exact mem_corePairs.mpr
      (isCorePair_of_bridging bd p₀ pd q.1 q.2 (Finset.mem_filter.mp hq).2)
  · refine Finset.sum_congr rfl ?_
    intro c hc
    have hcore : IsCorePair bd p₀ pd c := mem_corePairs.mp hc
    rw [mul_sq_sum_eq_sum_product_crs]
    refine Finset.sum_nbij'
      (i := fun q : Finset Pq × Finset Pq =>
        (q.1 \ coreSpan p₀ pd c, q.2 \ coreSpan p₀ pd c))
      (j := fun x : Finset Pq × Finset Pq => (c.1 ∪ x.1, c.2 ∪ x.2)) ?_ ?_ ?_ ?_ ?_
    · -- the forward map lands in the outside pairs
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hspan : coreSpan p₀ pd c = compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ := by
        rw [← hq.2]; exact coreSpan_core_eq_crs bd p₀ pd q.1 q.2 hq.1
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset, hspan]
      exact ⟨sdiff_compOf_subset_outsideOf_crs bd _ p₀ (fun x hx => by simp [hx]),
             sdiff_compOf_subset_outsideOf_crs bd _ p₀ (fun x hx => by simp [hx])⟩
    · -- the inverse map lands in the fibre
      intro x hx
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
      have hcomp : compOf bd ((c.1 ∪ x.1) ∪ (c.2 ∪ x.2) ∪ {p₀, pd}) p₀ = coreSpan p₀ pd c :=
        compOf_union_outside_crs bd p₀ pd hcore hx.1 hx.2
      have hi1 : (c.1 ∪ x.1) ∩ coreSpan p₀ pd c = c.1 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact hz
          · exact absurd hzA (not_mem_coreSpan_of_mem_outsideOf_crs bd hne hcore (hx.1 hz))
        · intro hz
          exact ⟨Or.inl hz, fst_subset_coreSpan p₀ pd c hz⟩
      have hi2 : (c.2 ∪ x.2) ∩ coreSpan p₀ pd c = c.2 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact hz
          · exact absurd hzA (not_mem_coreSpan_of_mem_outsideOf_crs bd hne hcore (hx.2 hz))
        · intro hz
          exact ⟨Or.inl hz, snd_subset_coreSpan p₀ pd c hz⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · exact (mem_compOf.mp (by rw [hcomp]; exact mem_coreSpan_right p₀ pd c)).2
      · show ((c.1 ∪ x.1) ∩ compOf bd ((c.1 ∪ x.1) ∪ (c.2 ∪ x.2) ∪ {p₀, pd}) p₀,
              (c.2 ∪ x.2) ∩ compOf bd ((c.1 ∪ x.1) ∪ (c.2 ∪ x.2) ∪ {p₀, pd}) p₀) = c
        rw [hcomp, hi1, hi2]
    · -- rebuilding a bridging pair from its core and its outside returns it
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hspan : coreSpan p₀ pd c = compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ := by
        rw [← hq.2]; exact coreSpan_core_eq_crs bd p₀ pd q.1 q.2 hq.1
      have hc1 : c.1 = q.1 ∩ coreSpan p₀ pd c := by rw [hspan, ← hq.2]
      have hc2 : c.2 = q.2 ∩ coreSpan p₀ pd c := by rw [hspan, ← hq.2]
      have hrec : ∀ W : Finset Pq,
          (W ∩ coreSpan p₀ pd c) ∪ (W \ coreSpan p₀ pd c) = W := by
        intro W
        ext z
        by_cases hz : z ∈ coreSpan p₀ pd c <;> simp [hz]
      show (c.1 ∪ (q.1 \ coreSpan p₀ pd c), c.2 ∪ (q.2 \ coreSpan p₀ pd c)) = q
      rw [hc1, hc2, hrec, hrec]
    · -- and splitting a rebuilt pair returns the outside it was built from
      intro x hx
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
      have hrec1 : (c.1 ∪ x.1) \ coreSpan p₀ pd c = x.1 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact absurd (fst_subset_coreSpan p₀ pd c hz) hzA
          · exact hz
        · intro hz
          exact ⟨Or.inr hz,
            not_mem_coreSpan_of_mem_outsideOf_crs bd hne hcore (hx.1 hz)⟩
      have hrec2 : (c.2 ∪ x.2) \ coreSpan p₀ pd c = x.2 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact absurd (snd_subset_coreSpan p₀ pd c hz) hzA
          · exact hz
        · intro hz
          exact ⟨Or.inr hz,
            not_mem_coreSpan_of_mem_outsideOf_crs bd hne hcore (hx.2 hz)⟩
      show ((c.1 ∪ x.1) \ coreSpan p₀ pd c, (c.2 ∪ x.2) \ coreSpan p₀ pd c) = x
      rw [hrec1, hrec2]
    · -- the summand identity: this is `pairTerm_eq_core_mul_outside`
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hspan : coreSpan p₀ pd c = compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ := by
        rw [← hq.2]; exact coreSpan_core_eq_crs bd p₀ pd q.1 q.2 hq.1
      have hfac := pairTerm_eq_core_mul_outside (Nc := Nc) bd p₀ pd β q.1 q.2
        (compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)
        (compOf_closed bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)
        (self_mem_compOf (by simp))
        (mem_compOf.mpr ⟨by simp, hq.1⟩)
      rw [hq.2] at hfac
      show pairTerm (Nc := Nc) bd p₀ pd β q
        = pairTerm (Nc := Nc) bd p₀ pd β c
          * (zw (Nc := Nc) bd β ∅ (q.1 \ coreSpan p₀ pd c)
            * zw (Nc := Nc) bd β ∅ (q.2 \ coreSpan p₀ pd c))
      rw [hspan]
      exact hfac

#print axioms bridging_sum_eq_core_sum

open scoped Classical in
/-- **`CoreResummation` holds at `corePairs` with `coreSpan` as the core map**, given `p₀ ≠ pd`. This
is `bridging_sum_eq_core_sum` restated in the form `wilsonCorrConn_abs_le_of_coreResummation` takes.

DERIVED: no numeral. -/
theorem coreResummation_holds (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ) :
    CoreResummation (Nc := Nc) bd p₀ pd β (corePairs bd p₀ pd) (coreSpan p₀ pd) :=
  bridging_sum_eq_core_sum bd p₀ pd hne β

#print axioms coreResummation_holds

/-! #### The per-pair magnitude bound -/

/-- **`|zw bd β D E| ≤ 2 ^ D.card * (e^{2|β|} − 1) ^ E.card`**, at every `β` and every pair of
plaquette sets. Requires `Nc ≠ 0`. The integrand is bounded pointwise and the measure is a
probability measure, so no volume factor appears.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `2` in the base is the upper end of the Wilson
plaquette observable's range (`wilsonPlaqObs_le_two`), one factor per member of `D`. The `2` in the
exponent and the `1` come from `subset_weight_bound`, one factor per member of `E`. -/
theorem zw_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (D E : Finset Pq) :
    |zw (Nc := Nc) bd β D E| ≤ 2 ^ D.card * (Real.exp (2 * |β|) - 1) ^ E.card := by
  have hbound : ∀ U : Lk → MassGap.SUN.SU Nc,
      ‖(∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))‖
      ≤ 2 ^ D.card * (Real.exp (2 * |β|) - 1) ^ E.card := by
    intro U
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U| ≤ 2 ^ D.card := by
      rw [Finset.abs_prod]
      calc ∏ p ∈ D, |wilsonPlaqObs (N := Nc) bd p U|
          ≤ ∏ _p ∈ D, (2 : ℝ) := by
            refine Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => ?_)
            rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd p U)]
            exact wilsonPlaqObs_le_two hN bd p U
        _ = 2 ^ D.card := by rw [Finset.prod_const]
    have h2 : |∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))|
        ≤ (Real.exp (2 * |β|) - 1) ^ E.card := subset_weight_bound hN bd β U E
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hfin : ‖∫ U, (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
      ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))‖
      ≤ (2 ^ D.card * (Real.exp (2 * |β|) - 1) ^ E.card)
        * ((Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)
  rw [measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at hfin
  unfold zw
  exact hfin

#print axioms zw_abs_le

/-- **`|a*b − c*d| ≤ A*B + C*D`** when each of `a, b, c, d` is bounded in absolute value by the
corresponding capital and `0 ≤ A`, `0 ≤ C`. The triangle inequality for a difference of two products.
No sign condition is needed on `B` or `D`.

DERIVED: the `0`s are the sign hypotheses on `A` and `C`, which `mul_le_mul` needs. -/
theorem abs_sub_mul_le_crs {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (hA : 0 ≤ A) (hC : 0 ≤ C) : |a * b - c * d| ≤ A * B + C * D := by
  have h1 : |a * b| ≤ A * B := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hA
  have h2 : |c * d| ≤ C * D := by
    rw [abs_mul]; exact mul_le_mul hc hd (abs_nonneg _) hC
  have p1 := le_abs_self (a * b)
  have p2 := neg_abs_le (a * b)
  have p3 := le_abs_self (c * d)
  have p4 := neg_abs_le (c * d)
  rw [abs_le]
  constructor <;> linarith

/-- **`|zwFull bd β O E| ≤ c · (e^{2|β|} − 1)^|E|`** for an observable bounded by `c`, at every `β`.
`zw_abs_le` with the plaquette product's `2 ^ D.card` replaced by the observable's bound. The measure
is a probability measure, so no volume factor appears.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `2` in `2 * |β|` and the `1` subtracted from the
exponential are `subset_weight_bound`'s, one factor per member of `E`. -/
theorem zwFull_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O : (Lk → MassGap.SUN.SU Nc) → ℝ} {c : ℝ} (hc : ∀ U, |O U| ≤ c) (E : Finset Pq) :
    |zwFull (Nc := Nc) bd β O E| ≤ c * (Real.exp (2 * |β|) - 1) ^ E.card := by
  have hbound : ∀ U : Lk → MassGap.SUN.SU Nc,
      ‖O U * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))‖
      ≤ c * (Real.exp (2 * |β|) - 1) ^ E.card := by
    intro U
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hc U) (subset_weight_bound hN bd β U E) (abs_nonneg _)
      ((abs_nonneg _).trans (hc U))
  have hfin : ‖∫ U, O U * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
      ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))‖
      ≤ (c * (Real.exp (2 * |β|) - 1) ^ E.card)
        * ((Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)
  rw [measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at hfin
  unfold zwFull
  exact hfin

#print axioms zwFull_abs_le

/-- **`|pairTermObs bd O₁ O₂ β q| ≤ 2 · c₁ c₂ · (e^{2|β|} − 1)^(|q.1| + |q.2|)`** for observables
bounded by `c₁` and `c₂`. `pairTermF_abs_le` with the plaquette products' `2 ^ card` replaced by the
observables' bounds: `zwFull_abs_le` on each of the four terms and the triangle inequality
`abs_sub_mul_le_crs`.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The leading `2` counts the two products the triangle
inequality adds. The `2` in `2 * |β|` and the `1` subtracted from the exponential are
`subset_weight_bound`'s, through `zwFull_abs_le`. The `1` in `fun _ => 1` is the constant observable
of `pairTermObs`. The `1` and `2` in `q.1` and `q.2` are projections. -/
theorem pairTermObs_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {c₁ c₂ : ℝ}
    (hc₁ : ∀ U, |O₁ U| ≤ c₁) (hc₂ : ∀ U, |O₂ U| ≤ c₂) (β : ℝ)
    (q : Finset Pq × Finset Pq) :
    |pairTermObs (Nc := Nc) bd O₁ O₂ β q|
      ≤ 2 * (c₁ * c₂) * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by
  have h0₁ : 0 ≤ c₁ := (abs_nonneg _).trans (hc₁ (fun _ => 1))
  have h0₂ : 0 ≤ c₂ := (abs_nonneg _).trans (hc₂ (fun _ => 1))
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * |β|) - 1 := by
    have h := Real.one_le_exp (x := 2 * |β|) (by positivity)
    linarith
  have hp1 : (0 : ℝ) ≤ (Real.exp (2 * |β|) - 1) ^ q.1.card := pow_nonneg hq0 _
  have hp2 : (0 : ℝ) ≤ (Real.exp (2 * |β|) - 1) ^ q.2.card := pow_nonneg hq0 _
  have e1 := zwFull_abs_le hN bd β (O := fun U => O₁ U * O₂ U) (c := c₁ * c₂)
    (fun U => by
      rw [abs_mul]
      exact mul_le_mul (hc₁ U) (hc₂ U) (abs_nonneg _) h0₁) q.1
  have e2 := zwFull_abs_le hN bd β (O := fun _ => (1 : ℝ)) (c := 1) (fun U => by simp) q.2
  have e3 := zwFull_abs_le hN bd β hc₁ q.1
  have e4 := zwFull_abs_le hN bd β hc₂ q.2
  have key := abs_sub_mul_le_crs e1 e2 e3 e4 (mul_nonneg (mul_nonneg h0₁ h0₂) hp1)
    (mul_nonneg h0₁ hp1)
  unfold pairTermObs
  calc _ ≤ c₁ * c₂ * (Real.exp (2 * |β|) - 1) ^ q.1.card
          * (1 * (Real.exp (2 * |β|) - 1) ^ q.2.card)
        + c₁ * (Real.exp (2 * |β|) - 1) ^ q.1.card
          * (c₂ * (Real.exp (2 * |β|) - 1) ^ q.2.card) := key
    _ = 2 * (c₁ * c₂) * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by
        rw [pow_add]; ring

#print axioms pairTermObs_abs_le

/-- **`|pairTerm bd p₀ pd β q| ≤ 8 * (e^{2|β|} − 1) ^ (q.1.card + q.2.card)`**, at every coupling, on
any lattice, with no separation required between `p₀` and `pd`. Requires `Nc ≠ 0`.

`zw_abs_le` bounds each of the four terms, and `abs_sub_mul_le_crs` adds the two products. The bound
is not claimed attained: the largest ratio `|pairTerm|/(8·q^{|E|+|F|})` measured in the finite-group
control is `1/8`, on a geometry where `p₀` and `pd` share a boundary word, and `1/16` on rings.
`zw_abs_le` itself is attained, its ratio reaching `1` at `D = E = ∅`; dropping its observable factor
`2 ^ D.card` would make it false by a factor `2` at `D = {p₀, pd}` on that same geometry.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `2` and the `1` in `e^{2|β|} − 1` are
`subset_weight_bound`'s. The `8` is `4 + 4`: `zw_abs_le` gives `2 ^ D.card` per observable set, and
the two products of `pairTerm` carry `{p₀, pd}` against `∅`, so `2² · 2⁰ = 4`, and `{p₀}` against
`{pd}`, so `2¹ · 2¹ = 4`. The `1` and `2` in `q.1` and `q.2` are projections. -/
theorem pairTerm_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (q : Finset Pq × Finset Pq) :
    |pairTerm (Nc := Nc) bd p₀ pd β q|
      ≤ 8 * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * |β|) - 1 := by
    have h := Real.one_le_exp (x := 2 * |β|) (by positivity)
    linarith
  have hp1 : (0 : ℝ) ≤ (Real.exp (2 * |β|) - 1) ^ q.1.card := pow_nonneg hq0 _
  have hp2 : (0 : ℝ) ≤ (Real.exp (2 * |β|) - 1) ^ q.2.card := pow_nonneg hq0 _
  have hcard2 : ({p₀, pd} : Finset Pq).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  have e1 : |zw (Nc := Nc) bd β {p₀, pd} q.1| ≤ 4 * (Real.exp (2 * |β|) - 1) ^ q.1.card := by
    refine le_trans (zw_abs_le hN bd β _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ hp1
    calc (2 : ℝ) ^ ({p₀, pd} : Finset Pq).card ≤ (2 : ℝ) ^ 2 :=
          pow_le_pow_right₀ (by norm_num) hcard2
      _ = 4 := by norm_num
  have e2 : |zw (Nc := Nc) bd β ∅ q.2| ≤ 1 * (Real.exp (2 * |β|) - 1) ^ q.2.card := by
    refine le_trans (zw_abs_le hN bd β _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ hp2
    simp
  have e3 : |zw (Nc := Nc) bd β {p₀} q.1| ≤ 2 * (Real.exp (2 * |β|) - 1) ^ q.1.card := by
    refine le_trans (zw_abs_le hN bd β _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ hp1
    simp
  have e4 : |zw (Nc := Nc) bd β {pd} q.2| ≤ 2 * (Real.exp (2 * |β|) - 1) ^ q.2.card := by
    refine le_trans (zw_abs_le hN bd β _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ hp2
    simp
  have key := abs_sub_mul_le_crs e1 e2 e3 e4 (by linarith) (by linarith)
  calc |pairTerm (Nc := Nc) bd p₀ pd β q|
      ≤ 4 * (Real.exp (2 * |β|) - 1) ^ q.1.card * (1 * (Real.exp (2 * |β|) - 1) ^ q.2.card)
        + 2 * (Real.exp (2 * |β|) - 1) ^ q.1.card
          * (2 * (Real.exp (2 * |β|) - 1) ^ q.2.card) := key
    _ = 8 * ((Real.exp (2 * |β|) - 1) ^ q.1.card * (Real.exp (2 * |β|) - 1) ^ q.2.card) := by
        ring
    _ = 8 * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by rw [← pow_add]

#print axioms pairTerm_abs_le

/-- **`|pairTermF bd Ao Bo β q| ≤ 2 ^ (Ao.card + Bo.card + 1) * (e^{2|β|} − 1) ^ (q.1.card +
q.2.card)`**, requiring `Nc ≠ 0`.

`pairTerm_abs_le` with the constant `8` replaced by a power of the observable sizes: `zw_abs_le` pays
`2 ^ D.card` for the observable finset `D`, and `(Ao ∪ Bo).card ≤ Ao.card + Bo.card`. At
`Ao = {p₀}`, `Bo = {pd}` the constant is `2 ^ 3 = 8`, which is `pairTerm_abs_le`'s.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `2` in the base is `zw_abs_le`'s per-observable
factor; the `1` added to the cards is the second of the two products the triangle inequality adds.
The `2` in `2 * |β|` and the `1` subtracted from the exponential are `subset_weight_bound`'s, through
`zw_abs_le`. The `1` and `2` in `q.1` and `q.2` are projections. -/
theorem pairTermF_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq) (β : ℝ)
    (q : Finset Pq × Finset Pq) :
    |pairTermF (Nc := Nc) bd Ao Bo β q|
      ≤ 2 ^ (Ao.card + Bo.card + 1)
        * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * |β|) - 1 := by
    have h := Real.one_le_exp (x := 2 * |β|) (by positivity)
    linarith
  have hp1 : (0 : ℝ) ≤ (Real.exp (2 * |β|) - 1) ^ q.1.card := pow_nonneg hq0 _
  have hp2 : (0 : ℝ) ≤ (Real.exp (2 * |β|) - 1) ^ q.2.card := pow_nonneg hq0 _
  have hcardU : (Ao ∪ Bo).card ≤ Ao.card + Bo.card := Finset.card_union_le _ _
  have e1 : |zw (Nc := Nc) bd β (Ao ∪ Bo) q.1|
      ≤ (2 : ℝ) ^ (Ao.card + Bo.card) * (Real.exp (2 * |β|) - 1) ^ q.1.card := by
    refine le_trans (zw_abs_le hN bd β _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ hp1
    exact pow_le_pow_right₀ (by norm_num) hcardU
  have e2 : |zw (Nc := Nc) bd β ∅ q.2| ≤ 1 * (Real.exp (2 * |β|) - 1) ^ q.2.card := by
    refine le_trans (zw_abs_le hN bd β _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ hp2
    simp
  have e3 : |zw (Nc := Nc) bd β Ao q.1|
      ≤ (2 : ℝ) ^ Ao.card * (Real.exp (2 * |β|) - 1) ^ q.1.card := zw_abs_le hN bd β _ _
  have e4 : |zw (Nc := Nc) bd β Bo q.2|
      ≤ (2 : ℝ) ^ Bo.card * (Real.exp (2 * |β|) - 1) ^ q.2.card := zw_abs_le hN bd β _ _
  have key := abs_sub_mul_le_crs e1 e2 e3 e4 (by positivity) (by positivity)
  have hpow : (2 : ℝ) ^ (Ao.card + Bo.card + 1)
      = (2 : ℝ) ^ Ao.card * (2 : ℝ) ^ Bo.card * 2 := by
    rw [pow_succ, pow_add]
  have hr : (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card)
      = (Real.exp (2 * |β|) - 1) ^ q.1.card * (Real.exp (2 * |β|) - 1) ^ q.2.card :=
    pow_add _ _ _
  have h2 : (2 : ℝ) ^ (Ao.card + Bo.card) = (2 : ℝ) ^ Ao.card * (2 : ℝ) ^ Bo.card :=
    pow_add _ _ _
  calc |pairTermF (Nc := Nc) bd Ao Bo β q|
      ≤ (2 : ℝ) ^ (Ao.card + Bo.card) * (Real.exp (2 * |β|) - 1) ^ q.1.card
          * (1 * (Real.exp (2 * |β|) - 1) ^ q.2.card)
        + (2 : ℝ) ^ Ao.card * (Real.exp (2 * |β|) - 1) ^ q.1.card
          * ((2 : ℝ) ^ Bo.card * (Real.exp (2 * |β|) - 1) ^ q.2.card) := key
    _ = 2 ^ (Ao.card + Bo.card + 1)
          * (Real.exp (2 * |β|) - 1) ^ (q.1.card + q.2.card) := by
        rw [hpow, hr, h2]
        ring

#print axioms pairTermF_abs_le

/-! #### The bound with `Z²` discharged -/

open scoped Classical in
/-- **The connected correlation is bounded by a sum over `corePairs` alone.** With `Nc ≠ 0`,
`p₀ ≠ pd`, `0 ≤ β`, the integrability condition, and

    ∑ c ∈ corePairs bd p₀ pd, |pairTerm bd p₀ pd β c| ·
        exp (4β · touchDeg bd · (coreSpan p₀ pd c).card) ≤ M,

then `|wilsonCorrConn bd p₀ β pd| ≤ M`.

`wilsonCorrConn_abs_le_of_coreResummation` with `coreResummation_holds` supplying the resummation, so
the only side condition left is the integrability `corrNum_eq_subset_sum` carries. No partition
function appears. `pairTerm_abs_le` bounds each summand and `card_corePairs_span_le` counts them.

DERIVED: the first `0` is `Nc ≠ 0`, the second the sign hypothesis `0 ≤ β`. The `1` in `hint`'s
`Real.exp (-(β * φ_p)) - 1` is `boltz_eq_subset_sum`'s activated weight. The `4` is
`hard_core_outside_sq_div_partition_sq_le`'s, the Wilson density's `2` doubled by the two outside
sums. -/
theorem wilsonCorrConn_abs_le_core_sum (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) (hne : p₀ ≠ pd) {β : ℝ} (hβ : 0 ≤ β)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) (M : ℝ)
    (hM : ∑ c ∈ corePairs bd p₀ pd, |pairTerm (Nc := Nc) bd p₀ pd β c|
            * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ)) ≤ M) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd| ≤ M :=
  wilsonCorrConn_abs_le_of_coreResummation hN bd p₀ pd hne hβ hint
    (corePairs bd p₀ pd) (coreSpan p₀ pd) (coreResummation_holds bd p₀ pd hne β) M hM

#print axioms wilsonCorrConn_abs_le_core_sum

end CoreResum

end MassGap.StrongCoupling
-- ==== END core resummation ====

-- ==== BEGIN assembled core sum ====

/-! ### The assembly: the core sum resummed, and the separation put in the exponent

What is assembled:

    ∑_{cores} |pairTerm| · e^{4β·K·|span|}  ≤  8·L²·W² · rᵏ / (1 − r),
    L = 4(K+1)²,  W = e^{4βK},  q = e^{2β} − 1,  r = L·q·W,  K = touchDeg bd.

The cores are grouped by the size of their span. A core whose span has `m` plaquettes carries

* a weight at most `8·q^{|c₁|+|c₂|}` (`pairTerm_abs_le`), and `m ≤ |c₁| + |c₂| + 2` because the span
  is `c₁ ∪ c₂ ∪ {p₀,p_d}`, so the weight is at most `8·q^{m−2}`;
* a hard-core factor `e^{4βK·m} = W^m`, from `hard_core_outside_sq_div_partition_sq_le` through
  `wilsonCorrConn_abs_le_core_sum`;
* and there are at most `L^m` such cores: `((K+1)²)^m` spans (`card_connSets_le` through
  `coreSpan_mem_connSets`) times `4^m` ordered splits of a span into a pair of subsets
  (`card_pairs_with_union_le`).

The product is `8·L^m·q^{m−2}·W^m = 8·L²·W²·(LqW)^{m−2}` (`assembly_arith`), and summing the
geometric series in `m − 2` gives the bound. `r < 1` is what bounds the partial sums
(`geom_sum_le_inv_one_sub_asm`); `geom_sum_ge_of_one_le_asm` shows they grow at least linearly when
it fails.

`Fintype.card Pq` enters the proof only as the range of span sizes, making the geometric sum finite,
and leaves it again because `∑_{j<n} rʲ ≤ (1−r)⁻¹` holds at every `n`. `corePairs_sum_le`'s
`coreConst` and `coreRate` take `touchDeg bd` and `β` and nothing else.

`coreSpan_card_ge_of_not_mem_ball` is `card_ge_of_reach_of_lvl` applied to the span rather than to
the activated pair: a core's span is touch-connected and contains both anchors, so it realises every
intermediate touch-level, and `|span| ≥ k + 2` whenever `p_d ∉ ball p₀ k`. That empties every fibre
below `k`, so the geometric series starts there and the bound reads `C · rᵏ`.

`core_rate_lt_one_of_small` establishes a threshold in `β` by continuity at `β = 0`, as
`hard_core_rate_lt_one_of_small` does, and names no numeral. The prefactor `8·L²·W²` is at least
`128` (`le_corePrefactor`) and is not claimed sharp; `pairTerm_abs_le` records that its own `8` is
not attained. It sits in `coreConst` rather than in the rate.

The index `k` is a parameter of `wilsonCorrConn_abs_le_coreConst_mul_rate_pow`, whose hypothesis is
`pd ∉ ball bd p₀ k`. A family demanding such a plaquette at every `d : ℕ` cannot exist here:
`no_sep_family_of_reachable` rules it out once the plaquettes named are reachable from `p₀`, and
`wilsonCorrConn_eq_zero_of_no_ball` gives the correlation exactly zero where they are not.
`siteAtHyper_not_mem_ball` and `read_p_le_of_corrClay` carry the fixed-`k` form to a lag indexed by
`Fin (N + 1)`. -/

namespace MassGap.StrongCoupling

section CoreAssembly

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-! #### Arithmetic, proved here rather than named from the library

Each of these is a few lines and each would otherwise be a library spelling this file would have to
track. -/

/-- **`exp (x * n) = (exp x) ^ n`** for `n : ℕ`, by induction on `n`.

DERIVED: no numeral. -/
theorem exp_mul_nat_asm (x : ℝ) (n : ℕ) : Real.exp (x * (n : ℝ)) = Real.exp x ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hc, mul_add, Real.exp_add, ih, mul_one, pow_succ]

/-- **`1 ≤ a` gives `1 ≤ a ^ n`** at every `n : ℕ`.

DERIVED: both `1`s are the multiplicative unit, the threshold the hypothesis and the conclusion are
stated against. -/
theorem one_le_pow_asm {a : ℝ} (h : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ]; nlinarith

/-- **`0 ≤ a ≤ 1` gives `a ^ n ≤ 1`** at every `n : ℕ`.

DERIVED: the `0` and the two `1`s are the endpoints of the unit interval the hypothesis confines `a`
to, and the bound the conclusion states. -/
theorem pow_le_one_asm {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ]; nlinarith [pow_nonneg h0 m]

/-- **On `0 ≤ a ≤ 1` a bigger exponent is a smaller power**: `n ≤ m` gives `a ^ m ≤ a ^ n`.

DERIVED: the `0` and the `1` are the endpoints of the unit interval the hypothesis confines `a`
to. -/
theorem pow_le_pow_of_le_one_asm {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) {m n : ℕ} (h : n ≤ m) :
    a ^ m ≤ a ^ n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have ht := pow_le_one_asm h0 h1 t
  have hn := pow_nonneg h0 n
  nlinarith

/-- **`∑_{j < n} r ^ j ≤ (1 - r)⁻¹` for `0 ≤ r < 1`, at every `n`.** The bound does not depend on the
number of terms, which is how the lattice's size leaves the estimate.

DERIVED: the `0` is the sign hypothesis on `r`; the `1`s are the threshold `r < 1` and the numerator
of the geometric series' value. -/
theorem geom_sum_le_inv_one_sub_asm {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ j ≤ (1 - r)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have key : ∀ m : ℕ, (1 - r) * ∑ j ∈ Finset.range m, r ^ j = 1 - r ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ i ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  have hle : (1 - r) * ∑ j ∈ Finset.range n, r ^ j ≤ 1 := by
    rw [key n]
    have := pow_nonneg hr0 n
    linarith
  have hinv : (0 : ℝ) < (1 - r)⁻¹ := by positivity
  calc ∑ j ∈ Finset.range n, r ^ j
      = (1 - r)⁻¹ * ((1 - r) * ∑ j ∈ Finset.range n, r ^ j) := by
        field_simp
    _ ≤ (1 - r)⁻¹ * 1 := mul_le_mul_of_nonneg_left hle hinv.le
    _ = (1 - r)⁻¹ := by ring

/-- **`1 ≤ r` gives `n ≤ ∑_{j < n} r ^ j`.** At rate one or above the partial sums grow at least
linearly, so no constant independent of `n` bounds them and the hypothesis `r < 1` of
`geom_sum_le_inv_one_sub_asm` cannot be dropped.

DERIVED: the `1` is the threshold the hypothesis states, and the value of each term it bounds
below. -/
theorem geom_sum_ge_of_one_le_asm {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    (n : ℝ) ≤ ∑ j ∈ Finset.range n, r ^ j := by
  calc (n : ℝ) = ∑ _j ∈ Finset.range n, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ Finset.range n, r ^ j :=
        Finset.sum_le_sum (fun j _ => one_le_pow_asm hr j)

/-- **`A ^ (n+2) * (8 * q ^ n * W ^ (n+2)) = 8 * A ^ 2 * W ^ 2 * (A * q * W) ^ n`.** The regrouping
the core sum performs, as algebra over `ℝ` with no hypotheses: count times weight becomes prefactor
times rate to a power.

DERIVED: the `2`s added to `n` are `two_le_coreSpan_card`'s two anchors, which the count and the
hard-core factor pay for but the weight does not; they become the `A ^ 2` and `W ^ 2` of the
prefactor. The `8` is `pairTerm_abs_le`'s constant, carried through unchanged. -/
theorem assembly_arith (A q W : ℝ) (n : ℕ) :
    A ^ (n + 2) * (8 * q ^ n * W ^ (n + 2)) = 8 * A ^ 2 * W ^ 2 * (A * q * W) ^ n := by
  rw [pow_add, pow_add, mul_pow, mul_pow]
  ring

/-- **`exp (4β · (touchDeg bd * m)) = (exp (4β · touchDeg bd)) ^ m`.** The hard-core factor rewritten
as a power of a per-plaquette constant, by `exp_mul_nat_asm`.

DERIVED: both `4`s are `hard_core_outside_sq_div_partition_sq_le`'s, the Wilson density's `2` doubled
by the two outside sums. -/
theorem exp_touchDeg_pow (bd : Pq → List (Lk × Bool)) (β : ℝ) (m : ℕ) :
    Real.exp (4 * β * ((touchDeg bd * m : ℕ) : ℝ))
      = Real.exp (4 * β * (touchDeg bd : ℝ)) ^ m := by
  rw [← exp_mul_nat_asm]
  congr 1
  push_cast
  ring

/-! #### The size of a core's span -/

/-- **`2 ≤ (coreSpan p₀ pd c).card`** for `p₀ ≠ pd`. Both anchors lie in every span, so no span is
smaller than two, whatever the core pair.

DERIVED: the `2` is the two anchors `p₀` and `pd`, distinct by hypothesis. -/
theorem two_le_coreSpan_card (p₀ pd : Pq) (hne : p₀ ≠ pd) (c : Finset Pq × Finset Pq) :
    2 ≤ (coreSpan p₀ pd c).card := by
  classical
  have hsub : ({p₀, pd} : Finset Pq) ⊆ coreSpan p₀ pd c := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · rw [hx']
      exact mem_coreSpan_left p₀ pd c
    · rw [Finset.mem_singleton] at hx'
      rw [hx']
      exact mem_coreSpan_right p₀ pd c
  have hc2 : ({p₀, pd} : Finset Pq).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne)]
    simp
  rw [← hc2]
  exact Finset.card_le_card hsub

#print axioms two_le_coreSpan_card

open scoped Classical in
/-- **`pd ∉ ball bd p₀ k` forces `k + 2 ≤ (coreSpan p₀ pd c).card`** for every core pair `c`, given
`p₀ ≠ pd`.

`card_ge_of_bridging` bounds `E.card + F.card`, which is not what the core sum is indexed by; this
applies `card_ge_of_reach_of_lvl` to the span itself. A span is touch-connected and contains both
anchors, so it realises every intermediate touch-level. This is what empties the low fibres of the
core sum.

DERIVED: the `2` added to `k` is the two anchors, which the level argument erases before counting and
`two_le_coreSpan_card` then restores. -/
theorem coreSpan_card_ge_of_not_mem_ball (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd)
    (k : ℕ) (hk : pd ∉ ball bd p₀ k) {c : Finset Pq × Finset Pq}
    (hc : IsCorePair bd p₀ pd c) :
    k + 2 ≤ (coreSpan p₀ pd c).card := by
  classical
  have h0 : p₀ ∈ coreSpan p₀ pd c := mem_coreSpan_left p₀ pd c
  have hd : pd ∈ coreSpan p₀ pd c := mem_coreSpan_right p₀ pd c
  have hreach : Reach bd (coreSpan p₀ pd c) p₀ pd := by
    have hm : pd ∈ compOf bd (coreSpan p₀ pd c) p₀ := by rw [hc]; exact hd
    exact (mem_compOf.mp hm).2
  have hex : ∃ n, pd ∈ ball bd p₀ n := exists_mem_ball_of_reach bd hreach
  have hlt : k < touchLvl bd p₀ pd := lt_touchLvl_of_not_mem_ball bd p₀ pd k hex hk
  have hcore := card_ge_of_reach_of_lvl bd (coreSpan p₀ pd c) (touchLvl bd p₀) p₀ pd k
    (touchLvl_lipschitz bd p₀) (touchLvl_self bd p₀) hlt hreach
  have hd' : pd ∈ (coreSpan p₀ pd c).erase p₀ := Finset.mem_erase.mpr ⟨Ne.symm hne, hd⟩
  have hc1 : ((coreSpan p₀ pd c).erase p₀).card = (coreSpan p₀ pd c).card - 1 :=
    Finset.card_erase_of_mem h0
  have hc2 : (((coreSpan p₀ pd c).erase p₀).erase pd).card
      = ((coreSpan p₀ pd c).erase p₀).card - 1 := Finset.card_erase_of_mem hd'
  have h2 : 2 ≤ (coreSpan p₀ pd c).card := two_le_coreSpan_card p₀ pd hne c
  omega

#print axioms coreSpan_card_ge_of_not_mem_ball

/-! ### The same geometry for observables supported on finsets of plaquettes

The decay statements above are anchored at one plaquette on each side. This section carries the same
constructions with each anchor replaced by a finset of plaquettes: `coreSpanF` and `IsCorePairF` are
the analogues of `coreSpan` and `IsCorePair`, and the originals are the case `A = {p₀}`,
`B = {pd}`. -/

/-- The span of a core pair for two finset anchors: `c.1 ∪ c.2 ∪ (A ∪ B)`. `coreSpan` with
`{p₀, pd}` replaced by `A ∪ B`.

DERIVED: no numeral. -/
def coreSpanF (A B : Finset Pq) (c : Finset Pq × Finset Pq) : Finset Pq :=
  c.1 ∪ c.2 ∪ (A ∪ B)

/-- **`a ∈ A` gives `a ∈ coreSpanF A B c`**, at every core pair `c`.

DERIVED: no numeral. -/
theorem mem_coreSpanF_left {a : Pq} {A : Finset Pq} (ha : a ∈ A) (B : Finset Pq)
    (c : Finset Pq × Finset Pq) : a ∈ coreSpanF A B c := by
  simp [coreSpanF, ha]

#print axioms mem_coreSpanF_left

/-- **`b ∈ B` gives `b ∈ coreSpanF A B c`**, at every core pair `c`.

DERIVED: no numeral. -/
theorem mem_coreSpanF_right {b : Pq} (A : Finset Pq) {B : Finset Pq} (hb : b ∈ B)
    (c : Finset Pq × Finset Pq) : b ∈ coreSpanF A B c := by
  simp [coreSpanF, hb]

#print axioms mem_coreSpanF_right

/-- A pair is a core for the finset anchors when its span is exactly `a`'s touch-component of that
span. `a` is a parameter and is not required to lie in `A`.

DERIVED: no numeral. -/
def IsCorePairF (bd : Pq → List (Lk × Bool)) (a : Pq) (A B : Finset Pq)
    (c : Finset Pq × Finset Pq) : Prop :=
  compOf bd (coreSpanF A B c) a = coreSpanF A B c

/-- **`2 ≤ (coreSpanF A B c).card`** given `a ∈ A`, `b ∈ B` and `a ≠ b`. The distinctness is a
hypothesis: `A` and `B` may otherwise overlap.

DERIVED: the `2` is the two plaquettes `a` and `b` exhibited in the span. -/
theorem two_le_coreSpanF_card {a b : Pq} {A B : Finset Pq} (ha : a ∈ A) (hb : b ∈ B)
    (hne : a ≠ b) (c : Finset Pq × Finset Pq) : 2 ≤ (coreSpanF A B c).card := by
  classical
  have hsub : ({a, b} : Finset Pq) ⊆ coreSpanF A B c := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · rw [hx']
      exact mem_coreSpanF_left ha B c
    · rw [Finset.mem_singleton] at hx'
      rw [hx']
      exact mem_coreSpanF_right A hb c
  calc (2 : ℕ) = ({a, b} : Finset Pq).card := (Finset.card_pair hne).symm
    _ ≤ (coreSpanF A B c).card := Finset.card_le_card hsub

#print axioms two_le_coreSpanF_card

/-- **`b ∉ ball bd a k` forces `k + 2 ≤ (coreSpanF A B c).card`**, given `a ∈ A`, `b ∈ B`, `a ≠ b`
and `IsCorePairF bd a A B c`. `coreSpan_card_ge_of_not_mem_ball` with the two anchors replaced by
members of the two finsets; `card_ge_of_reach_of_lvl` does not mention them, so the proof is the
same with the memberships supplied rather than definitional.

This is a cardinality bound on the span. The rate's exponent is read off it in the singleton
chain, by `corePairs_sum_le` and `wilsonCorrConn_abs_le_coreConst_mul_rate_pow`.

DERIVED: the `2` added to `k` is `two_le_coreSpanF_card`'s two plaquettes, which the level argument
erases before counting; the two erasures each cost a `1` inside the proof. -/
theorem coreSpanF_card_ge_of_not_mem_ball (bd : Pq → List (Lk × Bool))
    {a b : Pq} {A B : Finset Pq} (ha : a ∈ A) (hb : b ∈ B) (hne : a ≠ b)
    (k : ℕ) (hk : b ∉ ball bd a k) {c : Finset Pq × Finset Pq}
    (hc : IsCorePairF bd a A B c) :
    k + 2 ≤ (coreSpanF A B c).card := by
  classical
  have h0 : a ∈ coreSpanF A B c := mem_coreSpanF_left ha B c
  have hd : b ∈ coreSpanF A B c := mem_coreSpanF_right A hb c
  have hreach : Reach bd (coreSpanF A B c) a b := by
    have hm : b ∈ compOf bd (coreSpanF A B c) a := by rw [hc]; exact hd
    exact (mem_compOf.mp hm).2
  have hex : ∃ n, b ∈ ball bd a n := exists_mem_ball_of_reach bd hreach
  have hlt : k < touchLvl bd a b := lt_touchLvl_of_not_mem_ball bd a b k hex hk
  have hcore := card_ge_of_reach_of_lvl bd (coreSpanF A B c) (touchLvl bd a) a b k
    (touchLvl_lipschitz bd a) (touchLvl_self bd a) hlt hreach
  have hd' : b ∈ (coreSpanF A B c).erase a := Finset.mem_erase.mpr ⟨Ne.symm hne, hd⟩
  have hc1 : ((coreSpanF A B c).erase a).card = (coreSpanF A B c).card - 1 :=
    Finset.card_erase_of_mem h0
  have hc2 : (((coreSpanF A B c).erase a).erase b).card
      = ((coreSpanF A B c).erase a).card - 1 := Finset.card_erase_of_mem hd'
  have h2 : 2 ≤ (coreSpanF A B c).card := two_le_coreSpanF_card ha hb hne c
  omega

#print axioms coreSpanF_card_ge_of_not_mem_ball

/-- **`c.1 ⊆ coreSpanF A B c`**, the span being a union that contains it.

DERIVED: no numeral. -/
theorem fst_subset_coreSpanF (A B : Finset Pq) (c : Finset Pq × Finset Pq) :
    c.1 ⊆ coreSpanF A B c := by
  intro x hx; simp [coreSpanF, hx]

#print axioms fst_subset_coreSpanF

/-- **`c.2 ⊆ coreSpanF A B c`**, likewise.

DERIVED: no numeral. -/
theorem snd_subset_coreSpanF (A B : Finset Pq) (c : Finset Pq × Finset Pq) :
    c.2 ⊆ coreSpanF A B c := by
  intro x hx; simp [coreSpanF, hx]

#print axioms snd_subset_coreSpanF

/-- **`coreSpanF Ao Bo (E ∩ A, F ∩ A) = A`**, given `A ⊆ E ∪ F ∪ (Ao ∪ Bo)` and `Ao ∪ Bo ⊆ A`.
`coreSpan_eq_of_mem_crs` with the two anchor memberships replaced by the single inclusion
`Ao ∪ Bo ⊆ A`. A `Finset` identity, with no reachability in it.

DERIVED: no numeral. -/
theorem coreSpanF_eq_of_mem (Ao Bo A E F : Finset Pq)
    (hAV : A ⊆ E ∪ F ∪ (Ao ∪ Bo)) (hobs : Ao ∪ Bo ⊆ A) :
    coreSpanF Ao Bo (E ∩ A, F ∩ A) = A := by
  ext x
  simp only [coreSpanF, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ((⟨-, h⟩ | ⟨-, h⟩) | h)
    · exact h
    · exact h
    · exact hobs (Finset.mem_union.mpr h)
  · intro hx
    have hxV := hAV hx
    simp only [Finset.mem_union] at hxV
    rcases hxV with (h | h) | h
    · exact Or.inl (Or.inl ⟨h, hx⟩)
    · exact Or.inl (Or.inr ⟨h, hx⟩)
    · exact Or.inr h

#print axioms coreSpanF_eq_of_mem

open scoped Classical in
/-- **A bridging pair's component is the span of the core it cuts down to**, for finset anchors. The
bridging hypothesis is that `a` reaches every plaquette of `Ao ∪ Bo` inside the pair's union, not
just one of them.

DERIVED: no numeral. -/
theorem coreSpanF_core_eq (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq) (a : Pq)
    (E F : Finset Pq)
    (hbr : ∀ p ∈ Ao ∪ Bo, Reach bd (E ∪ F ∪ (Ao ∪ Bo)) a p) :
    coreSpanF Ao Bo (E ∩ compOf bd (E ∪ F ∪ (Ao ∪ Bo)) a,
                     F ∩ compOf bd (E ∪ F ∪ (Ao ∪ Bo)) a)
      = compOf bd (E ∪ F ∪ (Ao ∪ Bo)) a :=
  coreSpanF_eq_of_mem Ao Bo (compOf bd (E ∪ F ∪ (Ao ∪ Bo)) a) E F
    (fun _ hx => (mem_compOf.mp hx).1)
    (fun p hp => mem_compOf.mpr ⟨Finset.mem_union_right _ hp, hbr p hp⟩)

#print axioms coreSpanF_core_eq

open scoped Classical in
/-- **Cutting a bridging pair down to `a`'s component produces an `IsCorePairF`**, by
`coreSpanF_core_eq` and `compOf_idem_crs`.

DERIVED: no numeral. -/
theorem isCorePairF_of_bridging (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq) (a : Pq)
    (E F : Finset Pq)
    (hbr : ∀ p ∈ Ao ∪ Bo, Reach bd (E ∪ F ∪ (Ao ∪ Bo)) a p) :
    IsCorePairF bd a Ao Bo (E ∩ compOf bd (E ∪ F ∪ (Ao ∪ Bo)) a,
                            F ∩ compOf bd (E ∪ F ∪ (Ao ∪ Bo)) a) := by
  unfold IsCorePairF
  rw [coreSpanF_core_eq bd Ao Bo a E F hbr]
  exact compOf_idem_crs bd _ a

#print axioms isCorePairF_of_bridging

open scoped Classical in
/-- The pairs satisfying `IsCorePairF bd a Ao Bo`, as a `Finset`. `corePairs` with the anchor `a`
an explicit argument rather than one of the two singletons.

DERIVED: no numeral. -/
noncomputable def corePairsF (bd : Pq → List (Lk × Bool)) (a : Pq) (Ao Bo : Finset Pq) :
    Finset (Finset Pq × Finset Pq) :=
  Finset.univ.filter (fun c => IsCorePairF bd a Ao Bo c)

open scoped Classical in
/-- **`c ∈ corePairsF bd a Ao Bo ↔ IsCorePairF bd a Ao Bo c`**, the defining filter unfolded.

DERIVED: no numeral. -/
theorem mem_corePairsF {bd : Pq → List (Lk × Bool)} {a : Pq} {Ao Bo : Finset Pq}
    {c : Finset Pq × Finset Pq} :
    c ∈ corePairsF bd a Ao Bo ↔ IsCorePairF bd a Ao Bo c := by
  unfold corePairsF
  simp

#print axioms mem_corePairsF

open scoped Classical in
/-- **A member of a core's outside is not in the core's span**, for finset anchors:
`z ∈ outsideOf bd (coreSpanF Ao Bo c)` gives `z ∉ coreSpanF Ao Bo c`.

The hypotheses `b ∈ Bo` and `a ≠ b` play the part `p₀ ≠ pd` plays in the singleton counterpart
`not_mem_coreSpan_of_mem_outsideOf_crs`: the reflexive branch needs a plaquette of `Bo` distinct from
the anchor, to give `a`'s chain a first step.

DERIVED: no numeral. -/
theorem not_mem_coreSpanF_of_mem_outsideOf (bd : Pq → List (Lk × Bool))
    {a b : Pq} {Ao Bo : Finset Pq} (hb : b ∈ Bo) (hne : a ≠ b)
    {c : Finset Pq × Finset Pq} (hc : IsCorePairF bd a Ao Bo c) {z : Pq}
    (hz : z ∈ outsideOf bd (coreSpanF Ao Bo c)) : z ∉ coreSpanF Ao Bo c := by
  intro hzA
  have hout : ∀ y ∈ coreSpanF Ao Bo c, ¬ Touch bd z y := (Finset.mem_filter.mp hz).2
  have hreach : Reach bd (coreSpanF Ao Bo c) a z := by
    have hzc : z ∈ compOf bd (coreSpanF Ao Bo c) a := by rw [hc]; exact hzA
    exact (mem_compOf.mp hzc).2
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨y, -, hstep⟩
  · rw [hEq] at hout
    have hpd : Reach bd (coreSpanF Ao Bo c) a b := by
      have hm : b ∈ compOf bd (coreSpanF Ao Bo c) a := by
        rw [hc]; exact mem_coreSpanF_right Ao hb c
      exact (mem_compOf.mp hm).2
    rcases Relation.ReflTransGen.cases_head hpd with hEq2 | ⟨y, hy, -⟩
    · exact hne hEq2
    · exact hout y hy.2.1 hy.2.2
  · exact hout y hstep.1 (touch_symm hstep.2.2)

#print axioms not_mem_coreSpanF_of_mem_outsideOf

open scoped Classical in
/-- **A core rebuilt with an untouching outside has the core's span as its component**, for finset
anchors: `compOf bd ((c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ (Ao ∪ Bo)) a = coreSpanF Ao Bo c` when `X` and `Y` lie
in `outsideOf bd (coreSpanF Ao Bo c)`. Requires `a ∈ Ao`, for the reflexive case.

DERIVED: no numeral. -/
theorem compOf_union_outsideF (bd : Pq → List (Lk × Bool))
    {a : Pq} {Ao Bo : Finset Pq} (ha : a ∈ Ao)
    {c : Finset Pq × Finset Pq} (hc : IsCorePairF bd a Ao Bo c) {X Y : Finset Pq}
    (hX : X ⊆ outsideOf bd (coreSpanF Ao Bo c)) (hY : Y ⊆ outsideOf bd (coreSpanF Ao Bo c)) :
    compOf bd ((c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ (Ao ∪ Bo)) a = coreSpanF Ao Bo c := by
  have hAV : coreSpanF Ao Bo c ⊆ (c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ (Ao ∪ Bo) := by
    intro x hx
    simp only [coreSpanF, Finset.mem_union] at hx ⊢
    tauto
  have hout : ∀ z ∈ (c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ (Ao ∪ Bo), z ∉ coreSpanF Ao Bo c →
      z ∈ outsideOf bd (coreSpanF Ao Bo c) := by
    intro z hz hzn
    by_cases h1 : z ∈ X
    · exact hX h1
    · by_cases h2 : z ∈ Y
      · exact hY h2
      · exfalso
        apply hzn
        simp only [Finset.mem_union] at hz
        simp only [coreSpanF, Finset.mem_union]
        tauto
  apply Finset.Subset.antisymm
  · intro x hx
    have hrx : Reach bd ((c.1 ∪ X) ∪ (c.2 ∪ Y) ∪ (Ao ∪ Bo)) a x := (mem_compOf.mp hx).2
    clear hx
    induction hrx with
    | refl => exact mem_coreSpanF_left ha Bo c
    | tail _ hbc ih =>
        by_contra hcon
        exact (Finset.mem_filter.mp (hout _ hbc.2.1 hcon)).2 _ ih (touch_symm hbc.2.2)
  · intro x hx
    refine mem_compOf.mpr ⟨hAV hx, ?_⟩
    have hxc : x ∈ compOf bd (coreSpanF Ao Bo c) a := by rw [hc]; exact hx
    exact reach_mono_crs bd hAV (mem_compOf.mp hxc).2

#print axioms compOf_union_outsideF

/-- **`Ao ∪ Bo ⊆ coreSpanF Ao Bo c`**, at every core pair `c`.

DERIVED: no numeral. -/
theorem obs_subset_coreSpanF (Ao Bo : Finset Pq) (c : Finset Pq × Finset Pq) :
    Ao ∪ Bo ⊆ coreSpanF Ao Bo c := fun _ hx => Finset.mem_union_right _ hx

#print axioms obs_subset_coreSpanF

open scoped Classical in
/-- The finset exchange: flip across the anchor's component inside the pair's union. Identical in
shape to `exchange`, with `{p₀, pd}` replaced by `Ao ∪ Bo`.

DERIVED: no numeral. -/
noncomputable def exchangeF (bd : Pq → List (Lk × Bool)) (a : Pq) (Ao Bo : Finset Pq)
    (q : Finset Pq × Finset Pq) : Finset Pq × Finset Pq :=
  pairFlip (compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a) q

open scoped Classical in
/-- **`exchangeF` preserves the union of the pair**, so the separator recomputed from that union
after the flip is the same set. `pairFlip_union` at the anchor's component.

DERIVED: no numeral. -/
theorem exchangeF_union (bd : Pq → List (Lk × Bool)) (a : Pq) (Ao Bo : Finset Pq)
    (q : Finset Pq × Finset Pq) :
    (exchangeF bd a Ao Bo q).1 ∪ (exchangeF bd a Ao Bo q).2 = q.1 ∪ q.2 := by
  unfold exchangeF; exact pairFlip_union _ q

#print axioms exchangeF_union

open scoped Classical in
/-- **`exchangeF bd a Ao Bo` is an involution.** The separator is a function of the pair's union,
which `exchangeF_union` says survives the flip, so `pairFlip_pairFlip` applies.

DERIVED: no numeral. -/
theorem exchangeF_exchangeF (bd : Pq → List (Lk × Bool)) (a : Pq) (Ao Bo : Finset Pq)
    (q : Finset Pq × Finset Pq) :
    exchangeF bd a Ao Bo (exchangeF bd a Ao Bo q) = q := by
  have h : (exchangeF bd a Ao Bo q).1 ∪ (exchangeF bd a Ao Bo q).2 ∪ (Ao ∪ Bo)
      = q.1 ∪ q.2 ∪ (Ao ∪ Bo) := by rw [exchangeF_union]
  show pairFlip (compOf bd ((exchangeF bd a Ao Bo q).1 ∪ (exchangeF bd a Ao Bo q).2 ∪ (Ao ∪ Bo)) a)
      (exchangeF bd a Ao Bo q) = q
  rw [h]
  exact pairFlip_pairFlip _ q

#print axioms exchangeF_exchangeF

open scoped Classical in
/-- **The non-bridging sum vanishes, for observables on two finsets of plaquettes.** With
`Disjoint Ao Bo`, `a ∈ Ao` and `Ao` touch-connected from `a` inside `Ao` itself, the sum of
`pairTermF bd Ao Bo β q` over the pairs in which no plaquette of `Ao` reaches one of `Bo` inside
`q.1 ∪ q.2 ∪ (Ao ∪ Bo)` is zero, at every `β`.

`nonbridging_sum_eq_zero` with the two anchors replaced by finsets. `exchangeF_exchangeF` makes the
flip an involution on the filtered set and `pairTermF_add_pairFlip` negates the summand, so the sum
equals its own negation.

`hconn` is stated on `Ao` alone, not on the pair's union. The separator
`compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a` moves with `q`, so a connectivity hypothesis at the union
would have to be re-supplied per term; inside `Ao` it is a property of the observable, checked once,
and `reach_mono_crs` carries it into every pair's union. So the statement covers observables whose
support is touch-connected. For a support spanning several components the separator would have to be
`compsMeet`.

DERIVED: the `0` is the value of the filtered sum. -/
theorem nonbridging_sum_eq_zeroF (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq)
    (hod : Disjoint Ao Bo) {a : Pq} (ha : a ∈ Ao)
    (hconn : ∀ p ∈ Ao, Reach bd Ao a p) (β : ℝ) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∀ b ∈ Bo, ∀ a' ∈ Ao, ¬ Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b),
      pairTermF (Nc := Nc) bd Ao Bo β q = 0 := by
  classical
  set s : Finset (Finset Pq × Finset Pq) :=
    (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => ∀ b ∈ Bo, ∀ a' ∈ Ao, ¬ Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b) with hs
  -- `Ao` and `Bo` sit inside every pair's union, and `Ao` is connected there by monotonicity.
  have hAoV : ∀ q : Finset Pq × Finset Pq, Ao ⊆ q.1 ∪ q.2 ∪ (Ao ∪ Bo) := by
    intro q x hx
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
  have hBoV : ∀ q : Finset Pq × Finset Pq, Bo ⊆ q.1 ∪ q.2 ∪ (Ao ∪ Bo) := by
    intro q x hx
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
  have hconnV : ∀ q : Finset Pq × Finset Pq, ∀ p ∈ Ao,
      Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p := by
    intro q p hp
    exact reach_mono_crs bd (hAoV q) (hconn p hp)
  have hmem : ∀ q ∈ s, exchangeF bd a Ao Bo q ∈ s := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [exchangeF_union]
    exact hq.2
  have hcancel : ∀ q ∈ s, pairTermF (Nc := Nc) bd Ao Bo β q
      + pairTermF (Nc := Nc) bd Ao Bo β (exchangeF bd a Ao Bo q) = 0 := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq
    -- `Ao` lands in the anchor's component: connected, and inside the union.
    have h0 : Ao ⊆ compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a := by
      intro p hp
      exact mem_compOf.mpr ⟨hAoV q hp, hconnV q p hp⟩
    -- and `Bo` misses it, which is exactly the filter.
    have hd : Disjoint Bo (compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a) :=
      (disjoint_compOf_iff_of_connected bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) Ao Bo ha (hBoV q)
        (hconnV q)).mpr hq.2
    have := pairTermF_add_pairFlip (Nc := Nc) bd Ao Bo hod β q.1 q.2
      (compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a)
      (compOf_closed bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a) h0 hd
    simpa [exchangeF] using this
  have hinj : ∀ x ∈ s, ∀ y ∈ s, exchangeF bd a Ao Bo x = exchangeF bd a Ao Bo y → x = y := by
    intro x _ y _ hxy
    rw [← exchangeF_exchangeF bd a Ao Bo x, ← exchangeF_exchangeF bd a Ao Bo y, hxy]
  have himg : s.image (exchangeF bd a Ao Bo) = s := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      exact hmem r hr
    · intro q hq
      exact Finset.mem_image.mpr ⟨exchangeF bd a Ao Bo q, hmem q hq, exchangeF_exchangeF bd a Ao Bo q⟩
  have key : ∑ q ∈ s, pairTermF (Nc := Nc) bd Ao Bo β q
      = - ∑ q ∈ s, pairTermF (Nc := Nc) bd Ao Bo β q := by
    calc ∑ q ∈ s, pairTermF (Nc := Nc) bd Ao Bo β q
        = ∑ q ∈ s.image (exchangeF bd a Ao Bo), pairTermF (Nc := Nc) bd Ao Bo β q := by rw [himg]
      _ = ∑ q ∈ s, pairTermF (Nc := Nc) bd Ao Bo β (exchangeF bd a Ao Bo q) :=
          Finset.sum_image hinj
      _ = ∑ q ∈ s, (- pairTermF (Nc := Nc) bd Ao Bo β q) :=
          Finset.sum_congr rfl (fun q hq => by have := hcancel q hq; linarith)
      _ = - ∑ q ∈ s, pairTermF (Nc := Nc) bd Ao Bo β q := by simp
  linarith

#print axioms nonbridging_sum_eq_zeroF

open scoped Classical in
/-- **`wilsonCorrConnF bd Ao β Bo` is the bridging sum over `Z²`.** The connected correlation of
`∏ Ao` against `∏ Bo` equals the sum of `pairTermF` over the pairs of activated subsets in which some
plaquette of `Ao` touch-reaches some plaquette of `Bo` inside `q.1 ∪ q.2 ∪ (Ao ∪ Bo)`, divided by
`Z ^ 2`. `wilsonCorrConn_eq_bridging_sum` with the two anchor plaquettes replaced by finsets;
`nonbridging_sum_eq_zeroF` removes the non-reaching pairs.

Scope: `hconn` asks `Ao` to be touch-connected inside itself, so the statement covers a connected
support. `hod` asks the two supports to be disjoint, which is what `Finset.prod_union` needs to read
`∏ Ao · ∏ Bo` as `∏ (Ao ∪ Bo)`. `hint` is the integrability side condition, required for every pair
of finsets. `hN` excludes the empty gauge group.

DERIVED: the `2` in `Z ^ 2` is the number of independent subset sums, one per component of the pair
— `hprod` turns two sums over `Finset Pq` into one over `Finset Pq × Finset Pq`, so each of the two
Gibbs numerators carries its own partition function. The `0` is `hN : Nc ≠ 0`, which makes the
partition function positive (`wilsonSystem_partition_pos`) so the division is meaningful. The `1` in
`hint`'s `Real.exp (-(β * φ_p)) - 1` is `boltz_eq_subset_sum`'s activated weight; the `1` and `2` in
`q.1` and `q.2` are projections. -/
theorem wilsonCorrConnF_eq_bridging_sumF (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (Ao Bo : Finset Pq) (hod : Disjoint Ao Bo) {a : Pq} (ha : a ∈ Ao)
    (hconn : ∀ p ∈ Ao, Reach bd Ao a p) (β : ℝ)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) :
    MassGap.WilsonBridge.wilsonCorrConnF (Nc := Nc) bd Ao β Bo
      = (∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
            (fun q => ∃ b ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b),
          pairTermF (Nc := Nc) bd Ao Bo β q)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β) ^ 2 := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  have hz : ∀ D : Finset Pq,
      (∫ U, (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = ∑ E : Finset Pq, zw (Nc := Nc) bd β D E := by
    intro D
    have h := corrNum_eq_subset_sum (Nc := Nc) bd β
      (fun U => ∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U) (fun E _ => hint D E)
    rw [Finset.powerset_univ] at h
    exact h
  have h2 : (∫ U, ((∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β (Ao ∪ Bo) E := by
    refine Eq.trans ?_ (hz (Ao ∪ Bo))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    -- `simp only`, not `rw`: the goal is a beta-redex on both sides, so `rw` cannot see the
    -- product it is meant to match.
    simp only [Finset.prod_union hod]
  have hA : (∫ U, (∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β Ao E := hz Ao
  have hB : (∫ U, (∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β Bo E := hz Bo
  have hZ : (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β ∅ E := by
    refine Eq.trans ?_ (hz ∅)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul]
  have hprod : ∀ f g : Finset Pq → ℝ,
      (∑ E : Finset Pq, f E) * (∑ F : Finset Pq, g F)
        = ∑ q : Finset Pq × Finset Pq, f q.1 * g q.2 := by
    intro f g
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  -- the non-bridging set, written as the negation the involution theorem is stated against
  have hfilset : (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ¬ ∀ b ∈ Bo, ∀ a' ∈ Ao, ¬ Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b)
      = (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∃ b ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not, exists_prop]
  have hnum : (∑ E : Finset Pq, zw (Nc := Nc) bd β (Ao ∪ Bo) E)
        * (∑ F : Finset Pq, zw (Nc := Nc) bd β ∅ F)
      - (∑ E : Finset Pq, zw (Nc := Nc) bd β Ao E)
        * (∑ F : Finset Pq, zw (Nc := Nc) bd β Bo F)
      = ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
          (fun q => ∃ b ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b),
        pairTermF (Nc := Nc) bd Ao Bo β q := by
    rw [hprod, hprod, ← Finset.sum_sub_distrib]
    have hpt : ∀ q : Finset Pq × Finset Pq,
        zw (Nc := Nc) bd β (Ao ∪ Bo) q.1 * zw (Nc := Nc) bd β ∅ q.2
          - zw (Nc := Nc) bd β Ao q.1 * zw (Nc := Nc) bd β Bo q.2
        = pairTermF (Nc := Nc) bd Ao Bo β q := fun q => rfl
    rw [Finset.sum_congr rfl (fun q _ => hpt q),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset Pq × Finset Pq))
        (fun q => ∀ b ∈ Bo, ∀ a' ∈ Ao, ¬ Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b)
        (pairTermF (Nc := Nc) bd Ao Bo β),
      nonbridging_sum_eq_zeroF bd Ao Bo hod ha hconn β, zero_add, hfilset]
  have hconnEq : MassGap.WilsonBridge.wilsonCorrConnF (Nc := Nc) bd Ao β Bo
      = (∫ U, ((∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U)
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        - ((∫ U, (∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
              * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))))
          * ((∫ U, (∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U)
              * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))) := rfl
  have hpart : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
        (probHaar (MassGap.SUN.SU Nc)) β
      = ∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := rfl
  have hne0 : (∑ E : Finset Pq, zw (Nc := Nc) bd β ∅ E) ≠ 0 := by
    rw [← hZ, ← hpart]; exact hZpos.ne'
  rw [hconnEq, hpart, h2, hA, hB, hZ, ← hnum]
  field_simp

#print axioms wilsonCorrConnF_eq_bridging_sumF

/-- **A product of two sums over one index set is the sum over the product set.**
`T · ((∑ w₁) · (∑ w₂)) = ∑ over P ×ˢ P of T · (w₁ x.1 · w₂ x.2)`. `mul_sq_sum_eq_sum_product_crs`
with the two factors allowed to differ.

DERIVED: no numeral. -/
theorem mul_sum_sum_eq_sum_product {ι : Type*} (T : ℝ) (P : Finset ι) (w₁ w₂ : ι → ℝ) :
    T * ((∑ E ∈ P, w₁ E) * ∑ F ∈ P, w₂ F) = ∑ x ∈ P ×ˢ P, T * (w₁ x.1 * w₂ x.2) := by
  rw [Finset.sum_product]
  dsimp only
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]

#print axioms mul_sum_sum_eq_sum_product

open scoped Classical in
/-- **The resummation identity for any summand that factors through its core.** For `g` on pairs of
plaquette sets satisfying the core/outside factorisation

    g (E, F) = g (E ∩ A, F ∩ A) · (w₁ (E \ A) · w₂ (F \ A))

whenever `A ⊇ Ao ∪ Bo` and nothing touches across `A` inside `E ∪ F ∪ (Ao ∪ Bo)`, the sum of `g`
over the pairs in which every plaquette of `Ao ∪ Bo` is reachable from `a` regroups by core:

    ∑ g q = ∑ c ∈ corePairsF bd a Ao Bo, g c · (∑ w₁ over the outside) · (∑ w₂ over the outside).

The reindexing `q ↦ ((q.1 ∩ A, q.2 ∩ A), (q.1 \ A, q.2 \ A))` with `A` the component of `a` is
the whole content; `g`, `w₁` and `w₂` enter only through the factorisation. The two outside weights
may differ: the plaquette-family and observable routes take `w₁ = w₂ = zw ∅`, and the box comparison
takes both restricted to plaquette subsets (`BoxCompare.meanR_sub_abs_le`). `bridging_sum_eq_core_sumF` is this at
`pairTermF` (`pairTermF_eq_core_mul_outside`); `wilsonCorrConnObs_abs_le_core_sum` uses it at
`pairTermObs` through `pairTermObs_fac_halo`.

DERIVED: no numeral. -/
theorem bridging_sum_eq_core_sum_of_fac (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq)
    {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo) (hne : a ≠ b)
    (w₁ w₂ : Finset Pq → ℝ) (g : Finset Pq × Finset Pq → ℝ)
    (hg : ∀ E F A : Finset Pq,
      (∀ p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A, ∀ r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A, ¬ Touch bd p r) →
      Ao ∪ Bo ⊆ A →
      g (E, F) = g (E ∩ A, F ∩ A) * (w₁ (E \ A) * w₂ (F \ A))) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∀ p ∈ Ao ∪ Bo, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p),
      g q
    = ∑ c ∈ corePairsF bd a Ao Bo, g c
        * ((∑ E ∈ (outsideOf bd (coreSpanF Ao Bo c)).powerset, w₁ E)
          * ∑ F ∈ (outsideOf bd (coreSpanF Ao Bo c)).powerset, w₂ F) := by
  refine Eq.trans (Finset.sum_fiberwise_of_maps_to (t := corePairsF bd a Ao Bo)
      (g := fun q : Finset Pq × Finset Pq =>
        (q.1 ∩ compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a,
         q.2 ∩ compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a)) ?_ _).symm ?_
  · intro q hq
    exact mem_corePairsF.mpr
      (isCorePairF_of_bridging bd Ao Bo a q.1 q.2 (Finset.mem_filter.mp hq).2)
  · refine Finset.sum_congr rfl ?_
    intro c hc
    have hcore : IsCorePairF bd a Ao Bo c := mem_corePairsF.mp hc
    rw [mul_sum_sum_eq_sum_product]
    refine Finset.sum_nbij'
      (i := fun q : Finset Pq × Finset Pq =>
        (q.1 \ coreSpanF Ao Bo c, q.2 \ coreSpanF Ao Bo c))
      (j := fun x : Finset Pq × Finset Pq => (c.1 ∪ x.1, c.2 ∪ x.2)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hspan : coreSpanF Ao Bo c = compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a := by
        rw [← hq.2]; exact coreSpanF_core_eq bd Ao Bo a q.1 q.2 hq.1
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset, hspan]
      exact ⟨sdiff_compOf_subset_outsideOf_crs bd _ a (fun x hx => by simp [hx]),
             sdiff_compOf_subset_outsideOf_crs bd _ a (fun x hx => by simp [hx])⟩
    · intro x hx
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
      have hcomp : compOf bd ((c.1 ∪ x.1) ∪ (c.2 ∪ x.2) ∪ (Ao ∪ Bo)) a = coreSpanF Ao Bo c :=
        compOf_union_outsideF bd ha hcore hx.1 hx.2
      have hi1 : (c.1 ∪ x.1) ∩ coreSpanF Ao Bo c = c.1 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact hz
          · exact absurd hzA
              (not_mem_coreSpanF_of_mem_outsideOf bd hb hne hcore (hx.1 hz))
        · intro hz
          exact ⟨Or.inl hz, fst_subset_coreSpanF Ao Bo c hz⟩
      have hi2 : (c.2 ∪ x.2) ∩ coreSpanF Ao Bo c = c.2 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact hz
          · exact absurd hzA
              (not_mem_coreSpanF_of_mem_outsideOf bd hb hne hcore (hx.2 hz))
        · intro hz
          exact ⟨Or.inl hz, snd_subset_coreSpanF Ao Bo c hz⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro p hp
        exact (mem_compOf.mp (by rw [hcomp]; exact obs_subset_coreSpanF Ao Bo c hp)).2
      · show ((c.1 ∪ x.1) ∩ compOf bd ((c.1 ∪ x.1) ∪ (c.2 ∪ x.2) ∪ (Ao ∪ Bo)) a,
              (c.2 ∪ x.2) ∩ compOf bd ((c.1 ∪ x.1) ∪ (c.2 ∪ x.2) ∪ (Ao ∪ Bo)) a) = c
        rw [hcomp, hi1, hi2]
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hspan : coreSpanF Ao Bo c = compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a := by
        rw [← hq.2]; exact coreSpanF_core_eq bd Ao Bo a q.1 q.2 hq.1
      have hc1 : c.1 = q.1 ∩ coreSpanF Ao Bo c := by rw [hspan, ← hq.2]
      have hc2 : c.2 = q.2 ∩ coreSpanF Ao Bo c := by rw [hspan, ← hq.2]
      have hrec : ∀ W : Finset Pq,
          (W ∩ coreSpanF Ao Bo c) ∪ (W \ coreSpanF Ao Bo c) = W := by
        intro W
        ext z
        by_cases hz : z ∈ coreSpanF Ao Bo c <;> simp [hz]
      show (c.1 ∪ (q.1 \ coreSpanF Ao Bo c), c.2 ∪ (q.2 \ coreSpanF Ao Bo c)) = q
      rw [hc1, hc2, hrec, hrec]
    · intro x hx
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
      have hrec1 : (c.1 ∪ x.1) \ coreSpanF Ao Bo c = x.1 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact absurd (fst_subset_coreSpanF Ao Bo c hz) hzA
          · exact hz
        · intro hz
          exact ⟨Or.inr hz,
            not_mem_coreSpanF_of_mem_outsideOf bd hb hne hcore (hx.1 hz)⟩
      have hrec2 : (c.2 ∪ x.2) \ coreSpanF Ao Bo c = x.2 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hz | hz, hzA⟩
          · exact absurd (snd_subset_coreSpanF Ao Bo c hz) hzA
          · exact hz
        · intro hz
          exact ⟨Or.inr hz,
            not_mem_coreSpanF_of_mem_outsideOf bd hb hne hcore (hx.2 hz)⟩
      show ((c.1 ∪ x.1) \ coreSpanF Ao Bo c, (c.2 ∪ x.2) \ coreSpanF Ao Bo c) = x
      rw [hrec1, hrec2]
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hspan : coreSpanF Ao Bo c = compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a := by
        rw [← hq.2]; exact coreSpanF_core_eq bd Ao Bo a q.1 q.2 hq.1
      have hfac := hg q.1 q.2
        (compOf bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a)
        (compOf_closed bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a)
        (fun p hp => mem_compOf.mpr ⟨Finset.mem_union_right _ hp, hq.1 p hp⟩)
      rw [hq.2] at hfac
      show g q
        = g c
          * (w₁ (q.1 \ coreSpanF Ao Bo c)
            * w₂ (q.2 \ coreSpanF Ao Bo c))
      rw [hspan]
      exact hfac

#print axioms bridging_sum_eq_core_sum_of_fac

open scoped Classical in
/-- **The bridging sum regroups by core, for finset anchors.** With `a ∈ Ao`, `b ∈ Bo` and `a ≠ b`,
the sum of `pairTermF` over the pairs in which `a` reaches every plaquette of `Ao ∪ Bo` inside
`q.1 ∪ q.2 ∪ (Ao ∪ Bo)` equals the sum over `corePairsF bd a Ao Bo` of the core term times its two
constrained outside sums. `bridging_sum_eq_core_sum_of_fac` at `pairTermF`, whose factorisation is
`pairTermF_eq_core_mul_outside`.

The filter here is not the complement of `nonbridging_sum_eq_zeroF`'s. This one asks one component
to contain all of `Ao ∪ Bo`; that one excludes only the pairs in which no component meets both `Ao`
and `Bo`, and the set between the two is non-empty — for instance `Ao = {x, y}`, `Bo = {z}` with
components `{x, z}` and `{y}`. So the two do not compose into a numerator identity as they stand.
For `Ao` and `Bo` each connected in the pair's union the two filters agree, since then a component
meeting both contains both.

`compsMeet` is the separator for the wider filter: touch-closed (`compsMeet_closed`), containing `Ao`
(`subset_compsMeet`), smallest such (`compsMeet_minimal`), and missing `Bo` exactly when no component
meets both (`disjoint_compsMeet_iff`), which is the shape `pairTermF_add_pairFlip`'s `hclosed` takes
at `V = coreSpanF Ao Bo (E, F)`. Under that wider filter `IsCorePairF` has no witnesses when the
support is split across components, since `coreSpanF Ao Bo c` then contains components `a` never
reaches, and `card_corePairsF_span_le` counts through `connSets`, whose members are touch-connected
sets rooted at one plaquette; `card_rooted_pairs_ge` is the control on that connectedness.
`coreSpanF_eq_of_mem`'s `hobs : Ao ∪ Bo ⊆ A` and the involution's `Disjoint Bo A` agree only at
`Bo = ∅`, and `coreSpanF` contains `Ao ∪ Bo` by definition.

DERIVED: the `∅`s are the empty observable set, the outside sums carrying no plaquette observable. -/
theorem bridging_sum_eq_core_sumF (bd : Pq → List (Lk × Bool)) (Ao Bo : Finset Pq)
    {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo) (hne : a ≠ b) (β : ℝ) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∀ p ∈ Ao ∪ Bo, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p),
      pairTermF (Nc := Nc) bd Ao Bo β q
    = ∑ c ∈ corePairsF bd a Ao Bo, pairTermF (Nc := Nc) bd Ao Bo β c
        * ((∑ E ∈ (outsideOf bd (coreSpanF Ao Bo c)).powerset, zw (Nc := Nc) bd β ∅ E)
          * ∑ F ∈ (outsideOf bd (coreSpanF Ao Bo c)).powerset, zw (Nc := Nc) bd β ∅ F) :=
  bridging_sum_eq_core_sum_of_fac bd Ao Bo ha hb hne (zw (Nc := Nc) bd β ∅) (zw (Nc := Nc) bd β ∅)
    (pairTermF (Nc := Nc) bd Ao Bo β)
    (fun E F A h1 h2 => pairTermF_eq_core_mul_outside (Nc := Nc) bd Ao Bo β E F A h1 h2)

#print axioms bridging_sum_eq_core_sumF

/-- **The resummation holds for a pair of plaquette families.** One line over
`bridging_sum_eq_core_sumF`, exactly as `coreResummation_holds` is over `bridging_sum_eq_core_sum`.

The cores are `corePairsF bd a Ao Bo` and the span `coreSpanF Ao Bo` — the same families
`corePairsF_sum_le` bounds, so those two meet.

DERIVED: no numeral occurs. -/
theorem coreResummationF_holds (bd : Pq → List (Lk × Bool)) {a b : Pq} {Ao Bo : Finset Pq}
    (ha : a ∈ Ao) (hb : b ∈ Bo) (hne : a ≠ b) (β : ℝ) :
    CoreResummationF (Nc := Nc) bd a Ao Bo β (corePairsF bd a Ao Bo) (coreSpanF Ao Bo) :=
  bridging_sum_eq_core_sumF bd Ao Bo ha hb hne β

#print axioms coreResummationF_holds

open scoped Classical in
/-- **A bound on the cores alone bounds the connected correlation of two plaquette FAMILIES.**

The family counterpart of `wilsonCorrConn_abs_le_of_coreResummation`, and the step that closes the
`Finset` route. Composing `wilsonCorrConnF_eq_bridging_sumF` with a `CoreResummationF` witness needed
the two reach filters to agree, which `reach_filter_iff_of_connected` now supplies from the internal
connectedness of `Ao` and `Bo`.

Everything after the rewrite is shared with the single-plaquette proof, because
`hard_core_outside_sq_div_partition_sq_le` and `one_le_outside_sum_div_partition` are generic in the
core set: each outside partition sum over the core's complement is at most
`exp (4 · β · touchDeg bd · |core|)` times the full one, so the squared ratio is absorbed termwise
and only `hM`'s core sum remains.

With `coreResummationF_holds` for `hres` and `corePairsF_sum_le` for `hM`, this yields the geometric
`Finset` bound: products of plaquette observables decay in the separation, not only single ones.

DERIVED: `0` is the coupling's lower end, where `hard_core_outside_sq_div_partition_sq_le` needs
`β` non-negative; `4` is the exponent's constant, transcribed from that lemma, where it is
`hard_core_ratio_le`'s `2` doubled by squaring the ratio; the `1` subtracted in `hint` is the
Mayer link `e^(-βS) - 1`, which vanishes at zero coupling and is what makes the expansion connected.
-/
theorem wilsonCorrConnF_abs_le_of_coreResummationF (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (Ao Bo : Finset Pq) (hod : Disjoint Ao Bo) {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo)
    (hconnA : ∀ p ∈ Ao, Reach bd Ao a p) (hconnB : ∀ p ∈ Bo, Reach bd Bo b p)
    {β : ℝ} (hβ : 0 ≤ β)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
    (cores : Finset (Finset Pq × Finset Pq)) (core : Finset Pq × Finset Pq → Finset Pq)
    (hres : CoreResummationF (Nc := Nc) bd a Ao Bo β cores core) (M : ℝ)
    (hM : ∑ c ∈ cores, |pairTermF (Nc := Nc) bd Ao Bo β c|
            * Real.exp (4 * β * ((touchDeg bd * (core c).card : ℕ) : ℝ)) ≤ M) :
    |MassGap.WilsonBridge.wilsonCorrConnF (Nc := Nc) bd Ao β Bo| ≤ M := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  have hfil : (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∃ b' ∈ Bo, ∃ a' ∈ Ao, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a' b')
      = (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∀ p ∈ Ao ∪ Bo, Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p) :=
    Finset.filter_congr fun q _ => reach_filter_iff_of_connected bd ha hb hconnA hconnB q
  rw [wilsonCorrConnF_eq_bridging_sumF hN bd Ao Bo hod ha hconnA β hint, hfil, hres,
    Finset.sum_div]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum ?_) hM)
  intro c _
  set S := ∑ E ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ E with hSdef
  set Z := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hsq := hard_core_outside_sq_div_partition_sq_le hN bd hβ (core c)
  have hone := one_le_outside_sum_div_partition hN bd hβ (outsideOf bd (core c))
  have hSpos : 0 < S := by
    have h1 : 1 * Z ≤ S := (le_div_iff₀ hZpos).mp hone
    rw [one_mul] at h1
    exact lt_of_lt_of_le hZpos h1
  have hrnn : 0 ≤ S * S / Z ^ 2 := div_nonneg (by positivity) (by positivity)
  calc |pairTermF (Nc := Nc) bd Ao Bo β c * (S * S) / Z ^ 2|
      = |pairTermF (Nc := Nc) bd Ao Bo β c| * (S * S / Z ^ 2) := by
        rw [mul_div_assoc, abs_mul, abs_of_nonneg hrnn]
    _ ≤ |pairTermF (Nc := Nc) bd Ao Bo β c|
          * Real.exp (4 * β * ((touchDeg bd * (core c).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

#print axioms wilsonCorrConnF_abs_le_of_coreResummationF

open scoped Classical in
/-- **`coreSpanF Ao Bo c ∈ connSets bd a (coreSpanF Ao Bo c).card`** for an `IsCorePairF` with
`a ∈ Ao`. The finset counterpart of `coreSpan_mem_connSets`.

DERIVED: no numeral. -/
theorem coreSpanF_mem_connSets (bd : Pq → List (Lk × Bool)) {a : Pq} {Ao Bo : Finset Pq}
    (ha : a ∈ Ao) {c : Finset Pq × Finset Pq} (hc : IsCorePairF bd a Ao Bo c) :
    coreSpanF Ao Bo c ∈ connSets bd a (coreSpanF Ao Bo c).card := by
  have h := compOf_mem_connSets bd (coreSpanF Ao Bo c) a (mem_coreSpanF_left ha Bo c)
  rwa [hc] at h

#print axioms coreSpanF_mem_connSets

open scoped Classical in
/-- **The core pairs whose span has size `m` number at most `(4 * (touchDeg bd + 1) ^ 2) ^ m`**, for
finset anchors with `a ∈ Ao`. The same bound as `card_corePairs_span_le`: the count runs over
connected sets of size `m` containing the anchor and over pairs of their subsets, and `Bo` never
enters it.

The generalisation is paid for in the weight, not the count: `pairTermF_abs_le` carries
`2 ^ (Ao.card + Bo.card + 1)` where `pairTerm_abs_le` carries `8`.

DERIVED: the `4` is `card_pairs_with_union_le`'s ordered split of a span into a pair of subsets; the
`1` is `stepSet`'s stay-put step; the `2` is the two steps a detour costs, both through
`card_connSets_le`. -/
theorem card_corePairsF_span_le (bd : Pq → List (Lk × Bool)) {a : Pq} {Ao Bo : Finset Pq}
    (ha : a ∈ Ao) (m : ℕ) :
    ((corePairsF bd a Ao Bo).filter (fun c => (coreSpanF Ao Bo c).card = m)).card
      ≤ (4 * (touchDeg bd + 1) ^ 2) ^ m := by
  classical
  have hsub : ((corePairsF bd a Ao Bo).filter (fun c => (coreSpanF Ao Bo c).card = m))
      ⊆ (connSets bd a m).biUnion (fun S => S.powerset ×ˢ S.powerset) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcp, hcard⟩ := hc
    have hcore : IsCorePairF bd a Ao Bo c := mem_corePairsF.mp hcp
    have hmem : coreSpanF Ao Bo c ∈ connSets bd a m := by
      have h := coreSpanF_mem_connSets bd ha hcore
      rwa [hcard] at h
    refine Finset.mem_biUnion.mpr ⟨coreSpanF Ao Bo c, hmem, ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (fst_subset_coreSpanF Ao Bo c),
       Finset.mem_powerset.mpr (snd_subset_coreSpanF Ao Bo c)⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc ∑ S ∈ connSets bd a m, (S.powerset ×ˢ S.powerset).card
      ≤ ∑ _S ∈ connSets bd a m, 4 ^ m := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hSm : S.card = m := (mem_connSets.mp hS).2.2
        have h : (S.powerset ×ˢ S.powerset).card = 4 ^ m := by
          rw [Finset.card_product, Finset.card_powerset, hSm, ← mul_pow]
          norm_num
        exact le_of_eq h
    _ = (connSets bd a m).card * 4 ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ((touchDeg bd + 1) ^ 2) ^ m * 4 ^ m :=
        Nat.mul_le_mul_right _ (card_connSets_le bd a m)
    _ = (4 * (touchDeg bd + 1) ^ 2) ^ m := by rw [mul_pow]; ring

#print axioms card_corePairsF_span_le

/-- **`A ^ (n+u) * (C * q ^ n * W ^ (n+u)) = C * A ^ u * W ^ u * (A * q * W) ^ n`**, as algebra over
`ℝ` with no hypotheses. `assembly_arith` with its constant and its offset made parameters: that
lemma's `8` is `C` here and its `+ 2` is `u`.

DERIVED: no numeral. -/
theorem assembly_arith_gen (A q W C : ℝ) (n u : ℕ) :
    A ^ (n + u) * (C * q ^ n * W ^ (n + u)) = C * A ^ u * W ^ u * (A * q * W) ^ n := by
  rw [pow_add, pow_add, mul_pow, mul_pow]
  ring

#print axioms assembly_arith_gen


/-! #### The count of cores, indexed by span size -/

open scoped Classical in
/-- **The core pairs whose span has size `m` number at most `(4 * (touchDeg bd + 1) ^ 2) ^ m`.**
`card_connSets_le` counts the spans through `coreSpan_mem_connSets`, and a span of `m` plaquettes is
split into an ordered pair of subsets in exactly `4 ^ m` ways. The lattice extent appears in neither
factor.

DERIVED: the `4` is the ordered split of a span into a pair of subsets, `2 ^ m` per component; the
`1` is `stepSet`'s stay-put step and the `2` the two steps a detour costs, both through
`card_connSets_le`. -/
theorem card_corePairs_span_le (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (m : ℕ) :
    ((corePairs bd p₀ pd).filter (fun c => (coreSpan p₀ pd c).card = m)).card
      ≤ (4 * (touchDeg bd + 1) ^ 2) ^ m := by
  classical
  have hsub : ((corePairs bd p₀ pd).filter (fun c => (coreSpan p₀ pd c).card = m))
      ⊆ (connSets bd p₀ m).biUnion (fun S => S.powerset ×ˢ S.powerset) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcp, hcard⟩ := hc
    have hcore : IsCorePair bd p₀ pd c := mem_corePairs.mp hcp
    have hmem : coreSpan p₀ pd c ∈ connSets bd p₀ m := by
      have h := coreSpan_mem_connSets bd hcore
      rwa [hcard] at h
    refine Finset.mem_biUnion.mpr ⟨coreSpan p₀ pd c, hmem, ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (fst_subset_coreSpan p₀ pd c),
       Finset.mem_powerset.mpr (snd_subset_coreSpan p₀ pd c)⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  calc ∑ S ∈ connSets bd p₀ m, (S.powerset ×ˢ S.powerset).card
      ≤ ∑ _S ∈ connSets bd p₀ m, 4 ^ m := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hSm : S.card = m := (mem_connSets.mp hS).2.2
        have h : (S.powerset ×ˢ S.powerset).card = 4 ^ m := by
          rw [Finset.card_product, Finset.card_powerset, hSm, ← mul_pow]
          norm_num
        exact le_of_eq h
    _ = (connSets bd p₀ m).card * 4 ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ((touchDeg bd + 1) ^ 2) ^ m * 4 ^ m :=
        Nat.mul_le_mul_right _ (card_connSets_le bd p₀ m)
    _ = (4 * (touchDeg bd + 1) ^ 2) ^ m := by rw [mul_pow]; ring

#print axioms card_corePairs_span_le

/-! #### The rate, the prefactor, and the threshold they create -/

/-- The assembled per-plaquette rate of the core sum:
`coreRate K β = (4 (K+1)²) · (e^{2β} − 1) · e^{4βK}`, count times weight times hard-core factor.
`hardCoreRate` is the same product with `K + 1` in place of the core count `4 (K+1)²`. `K` is a
parameter, instantiated at `touchDeg bd` by the callers.

DERIVED: the `4` in the count is `card_pairs_with_union_le`'s ordered split of a span into a pair of
subsets; the `1` added to `K` is `stepSet`'s stay-put step and the `2` in `(K+1)²` the two steps a
detour costs, both through `card_connSets_le`. The `2` in `e^{2β}` is the upper end of
`wilsonDensity`'s range and the `1` subtracted is `boltz_factor_bound`'s value at zero coupling. The
`4` in `e^{4βK}` is that same `2` doubled by the two outside sums of
`hard_core_outside_sq_div_partition_sq_le`. -/
noncomputable def coreRate (K : ℕ) (β : ℝ) : ℝ :=
  (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) * Real.exp (4 * β * (K : ℝ))

/-- The prefactor of the assembled bound:
`corePrefactor K β = 8 · (4 (K+1)²)² · (e^{4βK})²`. The two anchors lie in the span but not in the
activated pair, so a span of `m` plaquettes pays the count and the hard-core factor at `m` against a
weight at `m − 2`, leaving two factors of each that the geometric series in `m − 2` does not absorb.

DERIVED: the `8` is `pairTerm_abs_le`'s constant. The outer `2`s are the two anchors the span carries
beyond the activated pair, as in `assembly_arith`. The `4`, the `1` and the inner `2` of `4 (K+1)²`,
and the `4` of `e^{4βK}`, are `coreRate`'s own factors. -/
noncomputable def corePrefactor (K : ℕ) (β : ℝ) : ℝ :=
  8 * (4 * ((K : ℝ) + 1) ^ 2) ^ 2 * Real.exp (4 * β * (K : ℝ)) ^ 2

/-- The assembled constant: `corePrefactor K β / (1 - coreRate K β)`. Its only inputs are `K` and
`β`; no lattice size enters. It is negative when `1 < coreRate K β`, which
`coreConst_nonpos_of_one_le` records.

DERIVED: the `1` is the geometric series' own denominator in `∑ rᵐ = (1 − r)⁻¹`, not a cutoff. -/
noncomputable def coreConst (K : ℕ) (β : ℝ) : ℝ :=
  corePrefactor K β / (1 - coreRate K β)

theorem coreRate_at_zero (K : ℕ) : coreRate K 0 = 0 := by
  unfold coreRate; simp

theorem continuous_coreRate (K : ℕ) : Continuous (coreRate K) := by
  unfold coreRate; fun_prop

theorem coreRate_nonneg (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ coreRate K β := by
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith)
    linarith
  have hA : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by positivity
  have hW : (0 : ℝ) < Real.exp (4 * β * (K : ℝ)) := Real.exp_pos _
  unfold coreRate
  exact mul_nonneg (mul_nonneg hA hq0) hW.le

/-- **There is a `b > 0` with `coreRate K β < 1` for every `β` in `[0, b)`.** `coreRate_at_zero` and
`continuous_coreRate`, as in `hard_core_rate_lt_one_of_small`. `b` is existential and depends on `K`;
no value for it is named.

DERIVED: the `0`s are the coupling at which the rate vanishes, the lower end of the interval, and the
strict lower bound on `b`. The `1` is the threshold at which a geometric series stops
converging. -/
theorem core_rate_lt_one_of_small (K : ℕ) :
    ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → coreRate K β < 1 := by
  have hlt : coreRate K 0 < 1 := by rw [coreRate_at_zero]; norm_num
  have ht : Filter.Tendsto (coreRate K) (nhds 0) (nhds (coreRate K 0)) :=
    (continuous_coreRate K).continuousAt
  have hev : ∀ᶠ x in nhds (0 : ℝ), coreRate K x < 1 := ht.eventually_lt_const hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun β hβ0 hβ => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
  exact hβ

#print axioms core_rate_lt_one_of_small

/-- **`coreRate K β` is below any positive threshold at small enough coupling.**
`core_rate_lt_one_of_small` at threshold `1`; the proof is the same continuity argument, and the
only change is that `coreRate K 0 = 0` is below `c` by hypothesis rather than by `norm_num`.

Wanted because `sum_pow_touchLvl_le` needs `((touchDeg bd : ℝ) + 1) * ρ < 1`, which is strictly
stronger than the `coreRate K β < 1` every existing strong-coupling theorem carries: at threshold
`c = ((touchDeg bd : ℝ) + 1)⁻¹` this supplies it.

DERIVED: `0` is the coupling at which `coreRate` vanishes, and the lower end of the window. -/
theorem core_rate_lt_of_small (K : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → coreRate K β < c := by
  have hlt : coreRate K 0 < c := by rw [coreRate_at_zero]; exact hc
  have ht : Filter.Tendsto (coreRate K) (nhds 0) (nhds (coreRate K 0)) :=
    (continuous_coreRate K).continuousAt
  have hev : ∀ᶠ x in nhds (0 : ℝ), coreRate K x < c := ht.eventually_lt_const hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun β hβ0 hβ => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
  exact hβ

#print axioms core_rate_lt_of_small

open scoped Classical in
/-- **A geometric factor summed over a family, indexed by touch distance.**

The counting step the diagonal-dominance route needs. Bounding an off-diagonal entry gives a factor
geometric in the separation; to compare the SUM of those against a diagonal, the number of family
members at each separation has to be controlled, and that is what this does.

Fibre `S` over its touch distance to `p₀`. The fibre at distance `m` sits inside `ball bd p₀ m` by
`mem_ball_touchLvl`, so `ball_card_le` bounds its cardinality by `(touchDeg bd + 1) ^ m` and the
fibre contributes at most `((touchDeg bd + 1) * ρ) ^ m`. Summing over `m` is then geometric, via
`geom_sum_le_inv_one_sub_asm`.

`hS` asks every member to be reachable from `p₀`. It is needed and not cosmetic: `touchLvl` takes a
sentinel value off `p₀`'s component, `mem_ball_touchLvl` does not apply there, and the fibre at the
sentinel has no ball to inject into.

`m₀` is a uniform minimum separation, and the bound is geometric in it — so a family held away from
the base point contributes geometrically little, which is the shape the dominance test consumes.

DERIVED: `1` is the increment in `touchDeg bd + 1`, the branching count of the touch graph — a
plaquette's neighbours plus itself, which is what `ball_card_le` counts per step; `1` is also the
threshold the ratio must lie below for the geometric series to converge. `0` is the lower bound on
`ρ`, a modulus factor being non-negative. -/
theorem sum_pow_touchLvl_le (bd : Pq → List (Lk × Bool)) (p₀ : Pq)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hu1 : ((touchDeg bd : ℝ) + 1) * ρ < 1)
    (S : Finset Pq) (hS : ∀ q ∈ S, ∃ n, q ∈ ball bd p₀ n)
    (m₀ : ℕ) (hm₀ : ∀ q ∈ S, m₀ ≤ touchLvl bd p₀ q) :
    ∑ q ∈ S, ρ ^ (touchLvl bd p₀ q)
      ≤ (((touchDeg bd : ℝ) + 1) * ρ) ^ m₀ * (1 - ((touchDeg bd : ℝ) + 1) * ρ)⁻¹ := by
  classical
  have hu0 : (0 : ℝ) ≤ ((touchDeg bd : ℝ) + 1) * ρ := by positivity
  have hmaps : ∀ q ∈ S, touchLvl bd p₀ q ∈ S.image (touchLvl bd p₀) :=
    fun q hq => Finset.mem_image_of_mem _ hq
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun q => ρ ^ (touchLvl bd p₀ q))]
  have hfib : ∀ m ∈ S.image (touchLvl bd p₀),
      (∑ q ∈ S.filter (fun q => touchLvl bd p₀ q = m), ρ ^ (touchLvl bd p₀ q))
        ≤ (((touchDeg bd : ℝ) + 1) * ρ) ^ m := by
    intro m _
    have hconst : ∀ q ∈ S.filter (fun q => touchLvl bd p₀ q = m),
        ρ ^ (touchLvl bd p₀ q) = ρ ^ m := by
      intro q hq; rw [(Finset.mem_filter.mp hq).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hsub : S.filter (fun q => touchLvl bd p₀ q = m) ⊆ ball bd p₀ m := by
      intro q hq
      obtain ⟨hqS, hqm⟩ := Finset.mem_filter.mp hq
      have hmem := mem_ball_touchLvl bd p₀ q (hS q hqS)
      rwa [hqm] at hmem
    have hcard : ((S.filter (fun q => touchLvl bd p₀ q = m)).card : ℝ)
        ≤ ((touchDeg bd : ℝ) + 1) ^ m := by
      have hn : (S.filter (fun q => touchLvl bd p₀ q = m)).card ≤ (touchDeg bd + 1) ^ m :=
        Nat.le_trans (Finset.card_le_card hsub) (ball_card_le bd p₀ m)
      calc ((S.filter (fun q => touchLvl bd p₀ q = m)).card : ℝ)
          ≤ (((touchDeg bd + 1) ^ m : ℕ) : ℝ) := by exact_mod_cast hn
        _ = ((touchDeg bd : ℝ) + 1) ^ m := by push_cast; ring
    calc ((S.filter (fun q => touchLvl bd p₀ q = m)).card : ℝ) * ρ ^ m
        ≤ ((touchDeg bd : ℝ) + 1) ^ m * ρ ^ m :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (((touchDeg bd : ℝ) + 1) * ρ) ^ m := (mul_pow _ _ m).symm
  refine le_trans (Finset.sum_le_sum hfib) ?_
  have hsplit : ∀ m ∈ S.image (touchLvl bd p₀), (((touchDeg bd : ℝ) + 1) * ρ) ^ m
      = (((touchDeg bd : ℝ) + 1) * ρ) ^ m₀ * (((touchDeg bd : ℝ) + 1) * ρ) ^ (m - m₀) := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    have hge := hm₀ q hq
    rw [← pow_add]
    congr 1
    omega
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hinj : Set.InjOn (fun m => m - m₀) (S.image (touchLvl bd p₀) : Finset ℕ) := by
    intro x hx y hy hxy
    obtain ⟨qx, hqx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨qy, hqy, rfl⟩ := Finset.mem_image.mp hy
    have h1 := hm₀ qx hqx
    have h2 := hm₀ qy hqy
    simp only at hxy
    omega
  rw [← Finset.sum_image (g := fun m => m - m₀)
    (f := fun j => (((touchDeg bd : ℝ) + 1) * ρ) ^ j) hinj]
  have hsubr : (S.image (touchLvl bd p₀)).image (fun m => m - m₀)
      ⊆ Finset.range ((S.image (touchLvl bd p₀)).sup id + 1) := by
    intro j hj
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hj
    have hle : m ≤ (S.image (touchLvl bd p₀)).sup id := Finset.le_sup (f := id) hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (Nat.sub_le m m₀) hle))
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubr (fun _ _ _ => by positivity))
    (geom_sum_le_inv_one_sub_asm hu0 hu1 _)

#print axioms sum_pow_touchLvl_le

/-- **`128 ≤ corePrefactor K β` for `0 ≤ β`**, at every `K`.

DERIVED: the `0` is the sign hypothesis on `β`, which is what makes `e^{4βK} ≥ 1`. The `128` is
`8 * 16`: `8` from `pairTerm_abs_le` and `16 = 4 ^ 2` from the two anchor factors of `4 (K+1)²` at
`K = 0`, the hard-core factor contributing at least `1`. -/
theorem le_corePrefactor (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 128 ≤ corePrefactor K β := by
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hexp : (0 : ℝ) ≤ 4 * β * (K : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hβ) hKnn
  have hW : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp hexp
  have hA : (4 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by nlinarith
  have h1 : (16 : ℝ) ≤ (4 * ((K : ℝ) + 1) ^ 2) ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) ^ 2 := by nlinarith
  unfold corePrefactor
  nlinarith

theorem one_le_corePrefactor (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 1 ≤ corePrefactor K β := by
  have := le_corePrefactor K (β := β) hβ
  linarith

/-- **`coreRate K β < 1` and `0 ≤ β` give `e^{2β} − 1 ≤ 1`.** The count factor alone is at least `4`
and the hard-core factor at least `1`, so a rate below one forces the per-plaquette weight below
`1/4`. This is the hypothesis `pow_le_pow_of_le_one_asm` needs in the fibre bounds, where a larger
exponent is traded for a smaller one.

DERIVED: the `0` is the sign hypothesis on `β`. The `2` in `e^{2β}` is `wilsonDensity`'s range; the
`1` subtracted is `boltz_factor_bound`'s value at zero coupling; the `1`s bounding `coreRate` and the
conclusion are the geometric threshold and the bound the count's factor of `4` yields. -/
theorem exp_sub_one_le_one_of_coreRate (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate K β < 1) :
    Real.exp (2 * β) - 1 ≤ 1 := by
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith)
    linarith
  have hexp : (0 : ℝ) ≤ 4 * β * (K : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hβ) hKnn
  have hW : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp hexp
  have hA : (4 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by nlinarith
  have hAW : (4 : ℝ) ≤ (4 * ((K : ℝ) + 1) ^ 2) * Real.exp (4 * β * (K : ℝ)) := by nlinarith
  have hstep : (Real.exp (2 * β) - 1) * 4
      ≤ (Real.exp (2 * β) - 1) * ((4 * ((K : ℝ) + 1) ^ 2) * Real.exp (4 * β * (K : ℝ))) :=
    mul_le_mul_of_nonneg_left hAW hq0
  unfold coreRate at hr
  nlinarith

/-! #### The core sum, resummed -/

open scoped Classical in
/-- **One fibre of the core sum.** Given `Nc ≠ 0`, `0 ≤ β`, `e^{2β} − 1 ≤ 1`, and `hlow` placing
every core's span above `k + 2`, the cores whose span has exactly `k + j + 2` plaquettes contribute
at most `corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ (k + j)`.

`pairTerm_abs_le` and `exp_touchDeg_pow` bound each summand, `card_corePairs_span_le` counts them,
and `assembly_arith` regroups the product. The fibre is indexed by
`(coreSpan p₀ pd c).card - (k + 2) = j` in `ℕ`, so `hlow` is what makes that subtraction faithful.

DERIVED: the first `0` is `Nc ≠ 0`, the second the sign hypothesis `0 ≤ β`. The `2` in `e^{2β}` and
the `1`s are `exp_sub_one_le_one_of_coreRate`'s. The `4` in the hard-core exponent is
`hard_core_outside_sq_div_partition_sq_le`'s. The `2` added to `k` is `two_le_coreSpan_card`'s two
anchors. -/
theorem corePairs_fiber_sum_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    {β : ℝ} (hβ : 0 ≤ β) (hq1 : Real.exp (2 * β) - 1 ≤ 1) (k j : ℕ)
    (hlow : ∀ c ∈ corePairs bd p₀ pd, k + 2 ≤ (coreSpan p₀ pd c).card) :
    ∑ c ∈ (corePairs bd p₀ pd).filter
        (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
      |pairTerm (Nc := Nc) bd p₀ pd β c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ))
      ≤ corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ (k + j) := by
  classical
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith)
    linarith
  have hWpos : (0 : ℝ) < Real.exp (4 * β * (touchDeg bd : ℝ)) := Real.exp_pos _
  -- every core in the fibre has a span of exactly `k + j + 2` plaquettes
  have hcard : ∀ c ∈ (corePairs bd p₀ pd).filter
      (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
      (coreSpan p₀ pd c).card = k + j + 2 := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have h1 := hlow c hc.1
    have h2 := hc.2
    omega
  -- the per-core bound
  have hpt : ∀ c ∈ (corePairs bd p₀ pd).filter
      (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
      |pairTerm (Nc := Nc) bd p₀ pd β c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ))
      ≤ 8 * (Real.exp (2 * β) - 1) ^ (k + j)
          * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (k + j + 2) := by
    intro c hc
    have hm := hcard c hc
    have hspan : (coreSpan p₀ pd c).card ≤ c.1.card + c.2.card + 2 := by
      have h1 := Finset.card_union_le c.1 c.2
      have h2 : ({p₀, pd} : Finset Pq).card ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp
      have h3 : (coreSpan p₀ pd c).card ≤ (c.1 ∪ c.2).card + ({p₀, pd} : Finset Pq).card := by
        unfold coreSpan
        exact Finset.card_union_le _ _
      omega
    have hle : k + j ≤ c.1.card + c.2.card := by omega
    have hpair := pairTerm_abs_le (Nc := Nc) hN bd p₀ pd β c
    rw [abs_of_nonneg hβ] at hpair
    have hw : (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card)
        ≤ (Real.exp (2 * β) - 1) ^ (k + j) := pow_le_pow_of_le_one_asm hq0 hq1 hle
    have hpair' : |pairTerm (Nc := Nc) bd p₀ pd β c| ≤ 8 * (Real.exp (2 * β) - 1) ^ (k + j) := by
      refine le_trans hpair ?_
      exact mul_le_mul_of_nonneg_left hw (by norm_num)
    rw [exp_touchDeg_pow bd β ((coreSpan p₀ pd c).card), hm]
    exact mul_le_mul_of_nonneg_right hpair' (pow_nonneg hWpos.le _)
  -- the count
  have hcount : (((corePairs bd p₀ pd).filter
      (fun c => (coreSpan p₀ pd c).card - (k + 2) = j)).card : ℝ)
      ≤ ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) ^ (k + j + 2) := by
    have hsub : ((corePairs bd p₀ pd).filter
        (fun c => (coreSpan p₀ pd c).card - (k + 2) = j))
        ⊆ (corePairs bd p₀ pd).filter (fun c => (coreSpan p₀ pd c).card = k + j + 2) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, hcard c hc⟩
    have hnat := le_trans (Finset.card_le_card hsub)
      (card_corePairs_span_le bd p₀ pd (k + j + 2))
    calc (((corePairs bd p₀ pd).filter
          (fun c => (coreSpan p₀ pd c).card - (k + 2) = j)).card : ℝ)
        ≤ (((4 * (touchDeg bd + 1) ^ 2) ^ (k + j + 2) : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      _ = ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) ^ (k + j + 2) := by push_cast; ring
  have hnn : (0 : ℝ) ≤ 8 * (Real.exp (2 * β) - 1) ^ (k + j)
      * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (k + j + 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq0 _)) (pow_nonneg hWpos.le _)
  have hL : ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) = 4 * ((touchDeg bd : ℝ) + 1) ^ 2 := by
    push_cast; ring
  calc ∑ c ∈ (corePairs bd p₀ pd).filter
        (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
        |pairTerm (Nc := Nc) bd p₀ pd β c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ))
      ≤ ∑ _c ∈ (corePairs bd p₀ pd).filter
          (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
          (8 * (Real.exp (2 * β) - 1) ^ (k + j)
            * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (k + j + 2)) := Finset.sum_le_sum hpt
    _ = (((corePairs bd p₀ pd).filter
          (fun c => (coreSpan p₀ pd c).card - (k + 2) = j)).card : ℝ)
          * (8 * (Real.exp (2 * β) - 1) ^ (k + j)
            * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (k + j + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) ^ (k + j + 2)
          * (8 * (Real.exp (2 * β) - 1) ^ (k + j)
            * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (k + j + 2)) :=
        mul_le_mul_of_nonneg_right hcount hnn
    _ = corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ (k + j) := by
        rw [hL]
        unfold corePrefactor coreRate
        exact assembly_arith _ _ _ _

#print axioms corePairs_fiber_sum_le

/-- The prefactor of the core sum at a per-term constant `C`:
`corePrefactorG C K β u = C · (4 (K + 1)²)^u · e^{4βK u}`. `corePrefactorF` is this at
`C = 2 ^ (na + nb + 1)`, `pairTermF_abs_le`'s constant.

DERIVED: the `4 (K + 1)²` is `card_corePairsF_span_le`'s count per core plaquette; the `4` in
`e^{4βK}` is `hard_core_outside_sq_div_partition_sq_le`'s, the Wilson density's `2` doubled by the two
outside sums; the `1` is `stepSet`'s stay-put step. -/
noncomputable def corePrefactorG (C : ℝ) (K : ℕ) (β : ℝ) (u : ℕ) : ℝ :=
  C * (4 * ((K : ℝ) + 1) ^ 2) ^ u * Real.exp (4 * β * (K : ℝ)) ^ u

/-- The constant of the core sum at a per-term constant `C`: the prefactor over `1 − coreRate K β`,
the geometric sum over core sizes. `coreConstF` is this at `C = 2 ^ (na + nb + 1)`.

DERIVED: the `1` is the geometric series' leading term. -/
noncomputable def coreConstG (C : ℝ) (K : ℕ) (β : ℝ) (u : ℕ) : ℝ :=
  corePrefactorG C K β u / (1 - coreRate K β)

/-- The prefactor for finset anchors:
`corePrefactorF K β na nb u = 2^(na + nb + 1) · (4 (K+1)²)^u · (e^{4βK})^u`. `corePrefactor` with its
two fixed numbers made parameters: the per-pair constant becomes `pairTermF_abs_le`'s
`2^(na + nb + 1)`, and the two anchor factors become `u`, the size of `Ao ∪ Bo`, because a span of
`m` plaquettes pays the count at `m` against a weight at `m − u`.

At `u = 2`, `na = nb = 1` it is `8 · (4(K+1)²)² · (e^{4βK})²`, which is `corePrefactor`.

DERIVED: the `2` in the base is `pairTermF_abs_le`'s per-observable factor and the `1` added to the
cards is that lemma's second product. The `4`, the `1` added to `K` and the `2` in `4 (K+1)²`, and
the `4` in `e^{4βK}`, are `coreRate`'s. -/
noncomputable def corePrefactorF (K : ℕ) (β : ℝ) (na nb u : ℕ) : ℝ :=
  2 ^ (na + nb + 1) * (4 * ((K : ℝ) + 1) ^ 2) ^ u * Real.exp (4 * β * (K : ℝ)) ^ u

open scoped Classical in
/-- **The core sum at one core size, for any summand with a per-term bound.** Given `a ∈ Ao`,
`0 ≤ β`, `e^{2β} − 1 ≤ 1` and `0 ≤ C`, if `|g c| ≤ C · (e^{2β} − 1)^(|c.1| + |c.2|)` for every pair,
then the cores of span size `n + |Ao ∪ Bo|` contribute at most `corePrefactorG C (touchDeg bd) β |Ao ∪ Bo| · coreRate (touchDeg bd) β ^ n`.
`corePairsF_fiber_sum_le` is this at `pairTermF` and `C = 2 ^ (|Ao| + |Bo| + 1)`.

DERIVED: the `2` in `e^{2β}` and the `1` subtracted are `subset_weight_bound`'s; the `1` bounding
`e^{2β} − 1` is the geometric threshold; the `4` in `4β` is
`hard_core_outside_sq_div_partition_sq_le`'s; the `0` is the sign hypothesis on `β` and on `C`. -/
theorem corePairsF_fiber_sum_le_of_bound (bd : Pq → List (Lk × Bool))
    {a : Pq} {Ao Bo : Finset Pq} (ha : a ∈ Ao)
    {β : ℝ} (hβ : 0 ≤ β) (hq1 : Real.exp (2 * β) - 1 ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (g : Finset Pq × Finset Pq → ℝ)
    (hg : ∀ c, |g c| ≤ C * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card)) (n : ℕ) :
    ∑ c ∈ (corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      |g c| * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card * coreRate (touchDeg bd) β ^ n := by
  classical
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith)
    linarith
  have hWpos : (0 : ℝ) < Real.exp (4 * β * (touchDeg bd : ℝ)) := Real.exp_pos _
  have hcard : ∀ c ∈ (corePairsF bd a Ao Bo).filter
      (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card :=
    fun c hc => (Finset.mem_filter.mp hc).2
  have hpt : ∀ c ∈ (corePairsF bd a Ao Bo).filter
      (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      |g c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ C * (Real.exp (2 * β) - 1) ^ n
          * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (n + (Ao ∪ Bo).card) := by
    intro c hc
    have hm := hcard c hc
    have h3 : (coreSpanF Ao Bo c).card ≤ (c.1 ∪ c.2).card + (Ao ∪ Bo).card := by
      unfold coreSpanF
      exact Finset.card_union_le _ _
    have h1 := Finset.card_union_le c.1 c.2
    have hle : n ≤ c.1.card + c.2.card := by omega
    have hpair := hg c
    have hw : (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card)
        ≤ (Real.exp (2 * β) - 1) ^ n := pow_le_pow_of_le_one_asm hq0 hq1 hle
    have hpair' : |g c|
        ≤ C * (Real.exp (2 * β) - 1) ^ n := by
      refine le_trans hpair ?_
      exact mul_le_mul_of_nonneg_left hw hC
    rw [exp_touchDeg_pow bd β ((coreSpanF Ao Bo c).card), hm]
    exact mul_le_mul_of_nonneg_right hpair' (pow_nonneg hWpos.le _)
  have hcount : (((corePairsF bd a Ao Bo).filter
      (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card)).card : ℝ)
      ≤ ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) ^ (n + (Ao ∪ Bo).card) := by
    have hnat := card_corePairsF_span_le (Bo := Bo) bd ha (n + (Ao ∪ Bo).card)
    calc (((corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card)).card : ℝ)
        ≤ (((4 * (touchDeg bd + 1) ^ 2) ^ (n + (Ao ∪ Bo).card) : ℕ) : ℝ) :=
          Nat.cast_le.mpr hnat
      _ = ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) ^ (n + (Ao ∪ Bo).card) := by push_cast; ring
  have hnn : (0 : ℝ) ≤ C * (Real.exp (2 * β) - 1) ^ n
      * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (n + (Ao ∪ Bo).card) :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hq0 _)) (pow_nonneg hWpos.le _)
  have hL : ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) = 4 * ((touchDeg bd : ℝ) + 1) ^ 2 := by
    push_cast; ring
  calc ∑ c ∈ (corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
        |g c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ ∑ _c ∈ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
          (C * (Real.exp (2 * β) - 1) ^ n
            * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (n + (Ao ∪ Bo).card)) :=
        Finset.sum_le_sum hpt
    _ = (((corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card)).card : ℝ)
          * (C * (Real.exp (2 * β) - 1) ^ n
            * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (n + (Ao ∪ Bo).card)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((4 * (touchDeg bd + 1) ^ 2 : ℕ) : ℝ) ^ (n + (Ao ∪ Bo).card)
          * (C * (Real.exp (2 * β) - 1) ^ n
            * Real.exp (4 * β * (touchDeg bd : ℝ)) ^ (n + (Ao ∪ Bo).card)) :=
        mul_le_mul_of_nonneg_right hcount hnn
    _ = corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
          * coreRate (touchDeg bd) β ^ n := by
        rw [hL]
        unfold corePrefactorG coreRate
        exact assembly_arith_gen _ _ _ _ _ _

#print axioms corePairsF_fiber_sum_le_of_bound

open scoped Classical in
/-- **One fibre of the core sum, for finset anchors.** Given `Nc ≠ 0`, `a ∈ Ao`, `0 ≤ β` and
`e^{2β} − 1 ≤ 1`, the cores whose span has exactly `n + (Ao ∪ Bo).card` plaquettes contribute at most
`corePrefactorF (touchDeg bd) β Ao.card Bo.card (Ao ∪ Bo).card * coreRate (touchDeg bd) β ^ n`.

The same argument as `corePairs_fiber_sum_le`, with `(Ao ∪ Bo).card` in place of the two anchors and
`pairTermF_abs_le` and `card_corePairsF_span_le` in place of their singleton counterparts. The fibre
is indexed by an equation rather than a subtraction, so no lower bound on the span is needed.

DERIVED: the first `0` is `Nc ≠ 0`, the second the sign hypothesis `0 ≤ β`. The `2` in `e^{2β}` and
the `1`s in `hq1` are `subset_weight_bound`'s activated weight and its bound at the geometric
threshold, supplied by `exp_sub_one_le_one_of_coreRate` at the callers. The `4` in the hard-core
exponent is `hard_core_outside_sq_div_partition_sq_le`'s. -/
theorem corePairsF_fiber_sum_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {a : Pq} {Ao Bo : Finset Pq} (ha : a ∈ Ao)
    {β : ℝ} (hβ : 0 ≤ β) (hq1 : Real.exp (2 * β) - 1 ≤ 1) (n : ℕ) :
    ∑ c ∈ (corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card = n + (Ao ∪ Bo).card),
      |pairTermF (Nc := Nc) bd Ao Bo β c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ corePrefactorF (touchDeg bd) β Ao.card Bo.card (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ n :=
  corePairsF_fiber_sum_le_of_bound bd ha hβ hq1 (by positivity) (pairTermF (Nc := Nc) bd Ao Bo β)
    (fun c => by
      have h := pairTermF_abs_le (Nc := Nc) hN bd Ao Bo β c
      rwa [abs_of_nonneg hβ] at h) n

#print axioms corePairsF_fiber_sum_le

/-- **`1 ≤ corePrefactorF K β na nb u` for `0 ≤ β`**, at every `K, na, nb, u`. This is what the
nonnegativity step of `corePairsF_sum_le` reads off.

DERIVED: the `1` is the bound; the `0` is the sign hypothesis on `β`, needed because the hard-core
factor `e^{4βK}` is below one at negative `β`. -/
theorem one_le_corePrefactorF (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (na nb u : ℕ) :
    1 ≤ corePrefactorF K β na nb u := by
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hexp : (0 : ℝ) ≤ 4 * β * (K : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hβ) hKnn
  have hW : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp hexp
  have hA : (1 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by nlinarith
  have h1 : (1 : ℝ) ≤ (4 * ((K : ℝ) + 1) ^ 2) ^ u := one_le_pow₀ hA
  have h2 : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) ^ u := one_le_pow₀ hW
  have h3 : (1 : ℝ) ≤ 2 ^ (na + nb + 1) := one_le_pow₀ (by norm_num)
  unfold corePrefactorF
  have hinner : (1 : ℝ) * 1
      ≤ (4 * ((K : ℝ) + 1) ^ 2) ^ u * Real.exp (4 * β * (K : ℝ)) ^ u :=
    mul_le_mul h1 h2 (by norm_num) (by positivity)
  have houter : (1 : ℝ) * ((1 : ℝ) * 1)
      ≤ 2 ^ (na + nb + 1)
        * ((4 * ((K : ℝ) + 1) ^ 2) ^ u * Real.exp (4 * β * (K : ℝ)) ^ u) :=
    mul_le_mul h3 hinner (by norm_num) (by positivity)
  nlinarith [houter]

#print axioms one_le_corePrefactorF

/-- The assembled constant for finset anchors: `corePrefactorF K β na nb u / (1 - coreRate K β)`.
`coreConst` with the finset prefactor.

DERIVED: the `1` is the geometric series' own denominator in `∑ rᵐ = (1 − r)⁻¹`. -/
noncomputable def coreConstF (K : ℕ) (β : ℝ) (na nb u : ℕ) : ℝ :=
  corePrefactorF K β na nb u / (1 - coreRate K β)

open scoped Classical in
/-- **The core sum for any summand with a per-term bound.** Given `a ∈ Ao`, `0 ≤ β`, `0 ≤ C`,
`|g c| ≤ C · (e^{2β} − 1)^(|c.1| + |c.2|)` for every pair, `coreRate (touchDeg bd) β < 1`,
`|Ao ∪ Bo| ≤ k + 2`, and every core with `g c ≠ 0` spanning at least `k + 2` plaquettes,

    ∑ c ∈ corePairsF bd a Ao Bo, |g c| · e^{4β · touchDeg · |span c|}
      ≤ coreConstG C (touchDeg bd) β |Ao ∪ Bo| · coreRate (touchDeg bd) β ^ (k + 2 − |Ao ∪ Bo|).

`corePairsF_sum_le` is this at `pairTermF`; `wilsonCorrConnObs_abs_le_coreConstG_mul_rate_pow` uses it
at `pairTermObs` with `C = 2 c₁ c₂`.

DERIVED: the `2` in `k + 2` is the two anchors every core contains; the `2` in `e^{2β}` and the `1`
subtracted in `hg` are `subset_weight_bound`'s; the `4` in `4β` is
`hard_core_outside_sq_div_partition_sq_le`'s; the `0` is the sign hypothesis on `β` and on `C`; the
`1` in `< 1` is the geometric ratio's bound. -/
theorem corePairsF_sum_le_of_bound (bd : Pq → List (Lk × Bool))
    {a : Pq} {Ao Bo : Finset Pq} (ha : a ∈ Ao)
    {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate (touchDeg bd) β < 1) {C : ℝ} (hC : 0 ≤ C)
    (g : Finset Pq × Finset Pq → ℝ)
    (hg : ∀ c, |g c| ≤ C * (Real.exp (2 * β) - 1) ^ (c.1.card + c.2.card)) (k : ℕ)
    (hu : (Ao ∪ Bo).card ≤ k + 2)
    (hlow : ∀ c ∈ corePairsF bd a Ao Bo, g c ≠ 0 → k + 2 ≤ (coreSpanF Ao Bo c).card) :
    ∑ c ∈ corePairsF bd a Ao Bo, |g c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ coreConstG C (touchDeg bd) β (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card) := by
  classical
  have hq1 := exp_sub_one_le_one_of_coreRate (touchDeg bd) hβ hr
  have hr0 : 0 ≤ coreRate (touchDeg bd) β := coreRate_nonneg _ hβ
  have hmaps : ∀ c ∈ corePairsF bd a Ao Bo,
      (coreSpanF Ao Bo c).card - (k + 2) ∈ Finset.range (Fintype.card Pq + 1) := by
    intro c _
    rw [Finset.mem_range]
    have h : (coreSpanF Ao Bo c).card ≤ (Finset.univ : Finset Pq).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ] at h
    omega
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => |g c|
      * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)))).symm
  rw [hfib]
  have hstep : ∀ j ∈ Finset.range (Fintype.card Pq + 1),
      ∑ c ∈ (corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j),
        |g c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ (corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
          * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card))
          * coreRate (touchDeg bd) β ^ j := by
    intro j _
    have hsub : (((corePairsF bd a Ao Bo).filter
        (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j)).filter (fun c => g c ≠ 0))
        ⊆ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card
            = (k + 2 - (Ao ∪ Bo).card + j) + (Ao ∪ Bo).card) := by
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      refine ⟨hc.1.1, ?_⟩
      have h1 := hlow c hc.1.1 hc.2
      have h2 := hc.1.2
      -- `hu` is spent here: without `(Ao ∪ Bo).card ≤ k + 2` the truncated subtraction
      -- `k + 2 - (Ao ∪ Bo).card` collapses to `0` and this equation is false. `omega` reads it
      -- from the context, so no name appears.
      omega
    have hmono : ∑ c ∈ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j),
          |g c|
            * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ ∑ c ∈ (corePairsF bd a Ao Bo).filter
            (fun c => (coreSpanF Ao Bo c).card
              = (k + 2 - (Ao ∪ Bo).card + j) + (Ao ∪ Bo).card),
            |g c|
              * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)) := by
      rw [← Finset.sum_filter_of_ne (p := fun c => g c ≠ 0) (fun c _ hf hg0 => hf (by
        rw [hg0, abs_zero, zero_mul]))]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun c _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    have h := corePairsF_fiber_sum_le_of_bound (Bo := Bo) bd ha hβ hq1 hC g hg
      (k + 2 - (Ao ∪ Bo).card + j)
    rw [pow_add] at h
    calc ∑ c ∈ (corePairsF bd a Ao Bo).filter
          (fun c => (coreSpanF Ao Bo c).card - (k + 2) = j),
          |g c|
            * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
        ≤ ∑ c ∈ (corePairsF bd a Ao Bo).filter
            (fun c => (coreSpanF Ao Bo c).card
              = (k + 2 - (Ao ∪ Bo).card + j) + (Ao ∪ Bo).card),
            |g c|
              * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ)) := hmono
      _ ≤ corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
            * (coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card)
              * coreRate (touchDeg bd) β ^ j) := h
      _ = (corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
            * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card))
            * coreRate (touchDeg bd) β ^ j := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hpre : 0 ≤ corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
      * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card) :=
    mul_nonneg (by unfold corePrefactorG; exact mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
      (pow_nonneg hr0 _)
  have hgeom := geom_sum_le_inv_one_sub_asm hr0 hr (Fintype.card Pq + 1)
  calc (corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card))
        * ∑ j ∈ Finset.range (Fintype.card Pq + 1), coreRate (touchDeg bd) β ^ j
      ≤ (corePrefactorG C (touchDeg bd) β (Ao ∪ Bo).card
          * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card))
          * (1 - coreRate (touchDeg bd) β)⁻¹ := mul_le_mul_of_nonneg_left hgeom hpre
    _ = coreConstG C (touchDeg bd) β (Ao ∪ Bo).card
          * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card) := by
        unfold coreConstG
        rw [div_eq_mul_inv]
        ring

#print axioms corePairsF_sum_le_of_bound

open scoped Classical in
/-- **The core sum, resummed, for finset anchors.** Given `Nc ≠ 0`, `a ∈ Ao`, `0 ≤ β`,
`coreRate (touchDeg bd) β < 1`, `(Ao ∪ Bo).card ≤ k + 2`, and `hlow` placing every core's span above
`k + 2`,

    ∑ c ∈ corePairsF bd a Ao Bo, |pairTermF c| · e^{4β·touchDeg·|span c|}
      ≤ coreConstF (touchDeg bd) β Ao.card Bo.card (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card).

The exponent is `k + 2 - (Ao ∪ Bo).card`, not `k`. The span's guaranteed size is `k + 2`
(`coreSpanF_card_ge_of_not_mem_ball`) and the support occupies `(Ao ∪ Bo).card` of it, so the power
of the rate is reduced by the support's size. `hu` is what keeps that subtraction in `ℕ` faithful;
it holds when the supports are small relative to their separation. It cannot be dropped: a
connecting chain may run through the support, so `k + (Ao ∪ Bo).card ≤ (coreSpanF Ao Bo c).card` is
false in general. At `(Ao ∪ Bo).card = 2` the exponent is `corePairs_sum_le`'s `k`.

`Fintype.card Pq` enters only as the number of fibres and leaves again through
`geom_sum_le_inv_one_sub_asm`.

DERIVED: the `0`s are `Nc ≠ 0` and the sign hypothesis `0 ≤ β`. The `1` bounds `coreRate` at the
geometric threshold. The `2`s added to `k` are the span's two guaranteed plaquettes, from
`coreSpanF_card_ge_of_not_mem_ball`. The `4` is the hard-core exponent of
`hard_core_outside_sq_div_partition_sq_le`. -/
theorem corePairsF_sum_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {a : Pq} {Ao Bo : Finset Pq} (ha : a ∈ Ao)
    {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate (touchDeg bd) β < 1) (k : ℕ)
    (hu : (Ao ∪ Bo).card ≤ k + 2)
    (hlow : ∀ c ∈ corePairsF bd a Ao Bo, k + 2 ≤ (coreSpanF Ao Bo c).card) :
    ∑ c ∈ corePairsF bd a Ao Bo, |pairTermF (Nc := Nc) bd Ao Bo β c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpanF Ao Bo c).card : ℕ) : ℝ))
      ≤ coreConstF (touchDeg bd) β Ao.card Bo.card (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card) :=
  corePairsF_sum_le_of_bound bd ha hβ hr (by positivity) (pairTermF (Nc := Nc) bd Ao Bo β)
    (fun c => by
      have h := pairTermF_abs_le (Nc := Nc) hN bd Ao Bo β c
      rwa [abs_of_nonneg hβ] at h) k hu (fun c hc _ => hlow c hc)

#print axioms corePairsF_sum_le

/-! #### The cluster bound for bounded local observables

A local observable enters the family resummation through an anchor set `Ao` containing its halo,
the plaquettes whose boundary meets its link support. Every plaquette outside a core that contains
both anchor sets avoids both supports, so `pairTermObs` factors through that core exactly as
`pairTermF` does, and the family counting applies unchanged with the per-term constant `2 c₁ c₂`.
The anchors are free beyond containing the halos and being touch-connected; `BoxCube.cubePlaq` is the
choice in a `ℤ⁴` box. -/

open scoped Classical in
/-- The halo of a link set: the plaquettes whose boundary word uses one of its links.

DERIVED: no numeral. -/
noncomputable def linkHalo (bd : Pq → List (Lk × Bool)) (S : Finset Lk) : Finset Pq :=
  Finset.univ.filter (fun p => ∃ l ∈ linkSupp bd p, l ∈ S)

open scoped Classical in
/-- **`p ∈ linkHalo bd S ↔ ∃ l ∈ linkSupp bd p, l ∈ S`**, the defining filter unfolded.

DERIVED: no numeral. -/
theorem mem_linkHalo {bd : Pq → List (Lk × Bool)} {S : Finset Lk} {p : Pq} :
    p ∈ linkHalo bd S ↔ ∃ l ∈ linkSupp bd p, l ∈ S := by
  unfold linkHalo; simp

#print axioms mem_linkHalo

open scoped Classical in
/-- **A pair term of two local observables factors through any core containing both halos.** With
`linkHalo Sa ⊆ Ao`, `linkHalo Sb ⊆ Bo`, `A ⊇ Ao ∪ Bo` and no touch across `A` inside
`E ∪ F ∪ (Ao ∪ Bo)`,

    pairTermObs (E, F) = pairTermObs (E ∩ A, F ∩ A) · (zw ∅ (E \ A) · zw ∅ (F \ A)).

A plaquette outside `A` is outside both halos, so it uses no link of `Sa ∪ Sb`; that is the support
condition of `pairTermObs_eq_core_mul_outside`, and `zwFull_one_eq_zw_empty` rewrites the outside
weights. This is the factorisation `bridging_sum_eq_core_sum_of_fac` takes.

DERIVED: no numeral. -/
theorem pairTermObs_fac_halo (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk}
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao)
    (hBo : linkHalo bd Sb ⊆ Bo)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ (Ao ∪ Bo)) ∩ A,
      ∀ r ∈ (E ∪ F ∪ (Ao ∪ Bo)) \ A, ¬ Touch bd p r)
    (hA : Ao ∪ Bo ⊆ A) :
    pairTermObs (Nc := Nc) bd O₁ O₂ β (E, F)
      = pairTermObs (Nc := Nc) bd O₁ O₂ β (E ∩ A, F ∩ A)
        * (zw (Nc := Nc) bd β ∅ (E \ A) * zw (Nc := Nc) bd β ∅ (F \ A)) := by
  rw [← zwFull_one_eq_zw_empty, ← zwFull_one_eq_zw_empty]
  refine pairTermObs_eq_core_mul_outside (Nc := Nc) bd β h₁ h₂ E F A
    (fun p hp r hr => hclosed p ?_ r ?_) (fun r hr l hl hlS => ?_)
  · simp only [Finset.mem_inter, Finset.mem_union] at hp ⊢
    tauto
  · simp only [Finset.mem_sdiff, Finset.mem_union] at hr ⊢
    tauto
  · have hrA : r ∉ A := (Finset.mem_sdiff.mp hr).2
    apply hrA
    rcases Finset.mem_union.mp hlS with h | h
    · exact hA (Finset.mem_union_left _ (hAo (mem_linkHalo.mpr ⟨l, hl, h⟩)))
    · exact hA (Finset.mem_union_right _ (hBo (mem_linkHalo.mpr ⟨l, hl, h⟩)))

#print axioms pairTermObs_fac_halo

open scoped Classical in
/-- **A bridging configuration connects the two anchor sets.** Let `Ao ⊇ linkHalo Sa` and
`Bo ⊇ linkHalo Sb` be touch-connected from `a` and `b`. If some plaquette of the separator grown from
`Sa` in `V` carries a link of `Sb`, then every plaquette of `Ao ∪ Bo` is reachable from `a` inside
`V ∪ Ao ∪ Bo`: `a` reaches the separator's seed through `Ao`, the seed reaches the bridging
plaquette inside `V`, and that plaquette reaches every plaquette of `Bo` through `b`.

DERIVED: no numeral. -/
theorem reach_halos_of_bridging (bd : Pq → List (Lk × Bool)) {Sa Sb : Finset Lk}
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao)
    (hBo : linkHalo bd Sb ⊆ Bo) {a b : Pq}
    (hconnA : ∀ p ∈ Ao, Reach bd (Ao) a p)
    (hconnB : ∀ p ∈ Bo, Reach bd (Bo) b p) (V : Finset Pq)
    (hbr : ¬ ∀ p ∈ V ∩ sepOfLinks bd V Sa, ∀ l ∈ linkSupp bd p, l ∉ Sb) :
    ∀ p ∈ Ao ∪ Bo,
      Reach bd (V ∪ (Ao ∪ Bo)) a p := by
  classical
  push_neg at hbr
  obtain ⟨p, hp, l, hl, hlb⟩ := hbr
  have hpsep := (Finset.mem_inter.mp hp).2
  unfold sepOfLinks at hpsep
  obtain ⟨-, p', hp', hreach⟩ := mem_compsMeet.mp hpsep
  obtain ⟨-, l', hl', hl'a⟩ := mem_plaqsMeetingLinks.mp hp'
  have hW : ∀ X : Finset Pq, X ⊆ V → X ⊆ V ∪ (Ao ∪ Bo) :=
    fun X hX => hX.trans Finset.subset_union_left
  have hHa : Ao ⊆ V ∪ (Ao ∪ Bo) :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_union_left _ hx)
  have hHb : Bo ⊆ V ∪ (Ao ∪ Bo) :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
  have hp'H : p' ∈ Ao := hAo (mem_linkHalo.mpr ⟨l', hl', hl'a⟩)
  have hpH : p ∈ Bo := hBo (mem_linkHalo.mpr ⟨l, hl, hlb⟩)
  have r1 := reach_mono_crs bd hHa (hconnA p' hp'H)
  have r2 := reach_mono_crs bd (hW V (Finset.Subset.refl V)) hreach
  have r3 := reach_symm (reach_mono_crs bd hHb (hconnB p hpH))
  have hab : Reach bd (V ∪ (Ao ∪ Bo)) a b :=
    Relation.ReflTransGen.trans (Relation.ReflTransGen.trans r1 r2) r3
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact reach_mono_crs bd hHa (hconnA x hx)
  · exact Relation.ReflTransGen.trans hab (reach_mono_crs bd hHb (hconnB x hx))

#print axioms reach_halos_of_bridging

open scoped Classical in
/-- **The bridging sum is the sum over configurations connecting the anchors.** Given `Disjoint Sa Sb`,
`LocalOnLinks Sa O₁`, `LocalOnLinks Sb O₂`, and anchor sets `Ao ⊇ linkHalo Sa`, `Bo ⊇ linkHalo Sb`
touch-connected from `a` and `b`,
the sum of `pairTermObs` over the bridging pairs of `wilsonCorrConnObs_eq_bridging_sumObs` equals its
sum over the pairs in which every plaquette of `Ao ∪ Bo` is reachable from `a`, the filter
`bridging_sum_eq_core_sum_of_fac` resums. Every bridging pair lies in the second family
(`reach_halos_of_bridging`); the rest of the second family is non-bridging and fixed by the pair's
union, so it cancels (`nonbridging_sum_eq_zeroObs_of`).

DERIVED: no numeral. -/
theorem bridging_sumObs_eq_reach_sum (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk} (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao)
    (hBo : linkHalo bd Sb ⊆ Bo) {a b : Pq}
    (hconnA : ∀ p ∈ Ao, Reach bd (Ao) a p)
    (hconnB : ∀ p ∈ Bo, Reach bd (Bo) b p) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ¬ ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa,
          ∀ l ∈ linkSupp bd p, l ∉ Sb),
      pairTermObs (Nc := Nc) bd O₁ O₂ β q
    = ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ∀ p ∈ Ao ∪ Bo,
          Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p),
      pairTermObs (Nc := Nc) bd O₁ O₂ β q := by
  classical
  have hz := nonbridging_sum_eq_zeroObs_of (Nc := Nc) bd β O₁ O₂ Sa Sb hab h₁ h₂
    (fun V => ∀ p ∈ Ao ∪ Bo,
      Reach bd (V ∪ (Ao ∪ Bo)) a p)
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => ∀ p ∈ Ao ∪ Bo,
        Reach bd (q.1 ∪ q.2 ∪ (Ao ∪ Bo)) a p))
    (fun q => ∀ p ∈ (q.1 ∪ q.2) ∩ sepOfLinks bd (q.1 ∪ q.2) Sa, ∀ l ∈ linkSupp bd p, l ∉ Sb),
    Finset.filter_filter, Finset.filter_filter]
  have e : ∀ {X x y : ℝ}, x = 0 → X = y → X = x + y := fun hx hy => by rw [hx, hy, zero_add]
  -- `convert`: the two filters agree up to their `Decidable` instances
  refine e (by convert hz) ?_
  refine Finset.sum_congr (Finset.filter_congr (fun q _ => ?_)) (fun _ _ => rfl)
  exact ⟨fun h => ⟨reach_halos_of_bridging bd hAo hBo hconnA hconnB (q.1 ∪ q.2) h, h⟩, fun h => h.2⟩

#print axioms bridging_sumObs_eq_reach_sum

open scoped Classical in
/-- **The connected correlation of two bounded local observables is bounded by their core sum.**
With `Nc ≠ 0`, `0 ≤ β`, disjoint supports `Sa`, `Sb`, bounds `c₁`, `c₂`, and anchor sets
`Ao ⊇ linkHalo Sa`, `Bo ⊇ linkHalo Sb` touch-connected from distinct base points `a ∈ Ao`, `b ∈ Bo`,

    |wilsonCorrConnObs bd O₁ O₂ β|  ≤  ∑ c ∈ corePairsF bd a Ao Bo,
                                      |pairTermObs c| · e^{4β · touchDeg · |span c|}.

`wilsonCorrConnObs_eq_bridging_sumObs` expands, `bridging_sumObs_eq_reach_sum` changes the filter,
`bridging_sum_eq_core_sum_of_fac` regroups by core through `pairTermObs_fac_halo`, and
`hard_core_outside_sq_div_partition_sq_le` cancels `Z²` against each core's outside sums.

DERIVED: the `0`s are `Nc ≠ 0` and `0 ≤ β`. The `4` is
`hard_core_outside_sq_div_partition_sq_le`'s, the Wilson density's `2` doubled by the two outside
sums. -/
theorem wilsonCorrConnObs_abs_le_core_sum (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk} (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {c₁ c₂ : ℝ} (hc₁ : ∀ U, |O₁ U| ≤ c₁) (hc₂ : ∀ U, |O₂ U| ≤ c₂)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao)
    (hBo : linkHalo bd Sb ⊆ Bo)
    {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo) (hne : a ≠ b)
    (hconnA : ∀ p ∈ Ao, Reach bd (Ao) a p)
    (hconnB : ∀ p ∈ Bo, Reach bd (Bo) b p)
    {β : ℝ} (hβ : 0 ≤ β) :
    |wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ β|
      ≤ ∑ c ∈ corePairsF bd a (Ao) (Bo),
          |pairTermObs (Nc := Nc) bd O₁ O₂ β c|
            * Real.exp (4 * β * ((touchDeg bd
                * (coreSpanF (Ao) (Bo) c).card : ℕ) : ℝ)) := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  rw [wilsonCorrConnObs_eq_bridging_sumObs hN bd O₁ O₂ Sa Sb hab h₁ h₂ hc₁ hc₂ β,
    bridging_sumObs_eq_reach_sum bd β hab h₁ h₂ hAo hBo hconnA hconnB,
    bridging_sum_eq_core_sum_of_fac bd Ao Bo ha
      hb hne (zw (Nc := Nc) bd β ∅) (zw (Nc := Nc) bd β ∅) (pairTermObs (Nc := Nc) bd O₁ O₂ β)
      (fun E F A h1 h2 => pairTermObs_fac_halo bd β h₁ h₂ hAo hBo E F A h1 h2),
    Finset.sum_div]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro c _
  set S := ∑ E ∈ (outsideOf bd (coreSpanF (Ao) (Bo) c)).powerset,
    zw (Nc := Nc) bd β ∅ E with hSdef
  set Z := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hsq := hard_core_outside_sq_div_partition_sq_le hN bd hβ
    (coreSpanF (Ao) (Bo) c)
  have hone := one_le_outside_sum_div_partition hN bd hβ
    (outsideOf bd (coreSpanF (Ao) (Bo) c))
  have hSpos : 0 < S := by
    have h1 : 1 * Z ≤ S := (le_div_iff₀ hZpos).mp hone
    rw [one_mul] at h1
    exact lt_of_lt_of_le hZpos h1
  have hrnn : 0 ≤ S * S / Z ^ 2 := div_nonneg (by positivity) (by positivity)
  calc |pairTermObs (Nc := Nc) bd O₁ O₂ β c * (S * S) / Z ^ 2|
      = |pairTermObs (Nc := Nc) bd O₁ O₂ β c| * (S * S / Z ^ 2) := by
        rw [mul_div_assoc, abs_mul, abs_of_nonneg hrnn]
    _ ≤ |pairTermObs (Nc := Nc) bd O₁ O₂ β c|
          * Real.exp (4 * β * ((touchDeg bd
              * (coreSpanF (Ao) (Bo) c).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

#print axioms wilsonCorrConnObs_abs_le_core_sum

open scoped Classical in
/-- **L2: the cluster bound for two bounded local observables.** Under the hypotheses of
`wilsonCorrConnObs_abs_le_core_sum`, with `coreRate (touchDeg bd) β < 1`, anchors of total size
`|Ao ∪ Bo| ≤ k + 2`, and every core spanning at least `k + 2` plaquettes,

    |wilsonCorrConnObs bd O₁ O₂ β|
      ≤ coreConstG (2 c₁ c₂) (touchDeg bd) β |Ao ∪ Bo| · coreRate (touchDeg bd) β ^ (k + 2 − |Ao ∪ Bo|).

The rate is the plaquette-family rate; the observable enters through its sup-norm bound and the size
of its anchor, which is the per-vector constant the gap capstone takes. `pairTermObs_abs_le` supplies
the per-term bound and `corePairsF_sum_le_of_bound` the count.

DERIVED: the `2` in `2 c₁ c₂` is `pairTermObs_abs_le`'s two products; the `2` in `k + 2` is the two
anchors every core contains; the `0`s are `Nc ≠ 0` and `0 ≤ β`; the `1` is the geometric ratio's
bound. -/
theorem wilsonCorrConnObs_abs_le_coreConstG_mul_rate_pow (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk} (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {c₁ c₂ : ℝ} (hc₁ : ∀ U, |O₁ U| ≤ c₁) (hc₂ : ∀ U, |O₂ U| ≤ c₂)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao)
    (hBo : linkHalo bd Sb ⊆ Bo)
    {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo) (hne : a ≠ b)
    (hconnA : ∀ p ∈ Ao, Reach bd (Ao) a p)
    (hconnB : ∀ p ∈ Bo, Reach bd (Bo) b p)
    {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate (touchDeg bd) β < 1) (k : ℕ)
    (hu : (Ao ∪ Bo).card ≤ k + 2)
    (hlow : ∀ c ∈ corePairsF bd a (Ao) (Bo),
      k + 2 ≤ (coreSpanF (Ao) (Bo) c).card) :
    |wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ β|
      ≤ coreConstG (2 * (c₁ * c₂)) (touchDeg bd) β (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card) := by
  have h0₁ : 0 ≤ c₁ := (abs_nonneg _).trans (hc₁ (fun _ => 1))
  have h0₂ : 0 ≤ c₂ := (abs_nonneg _).trans (hc₂ (fun _ => 1))
  refine le_trans (wilsonCorrConnObs_abs_le_core_sum hN bd hab h₁ h₂ hc₁ hc₂ hAo hBo ha hb hne
    hconnA hconnB hβ) ?_
  exact corePairsF_sum_le_of_bound bd ha hβ hr (mul_nonneg zero_le_two (mul_nonneg h0₁ h0₂))
    (pairTermObs (Nc := Nc) bd O₁ O₂ β)
    (fun c => by
      have h := pairTermObs_abs_le hN bd hc₁ hc₂ β c
      rwa [abs_of_nonneg hβ] at h) k hu (fun c hc _ => hlow c hc)

#print axioms wilsonCorrConnObs_abs_le_coreConstG_mul_rate_pow

open scoped Classical in
/-- **The connected correlation of two plaquette FAMILIES decays geometrically.** The `Finset` route,
closed.

Three proved pieces meet here and nothing else is needed. `coreResummationF_holds` witnesses the
resummation at the cores `corePairsF bd a Ao Bo` with span `coreSpanF Ao Bo`;
`wilsonCorrConnF_abs_le_of_coreResummationF` turns any bound on that core sum into a bound on
`wilsonCorrConnF`; and `corePairsF_sum_le` is a bound on precisely that core sum. The only glue is
`a ≠ b`, which `hod` already gives.

`hconnA` and `hconnB` ask each anchor family to be internally touch-connected — what a Wilson loop
is — and `reach_filter_iff_of_connected` is where they are spent. `hu` and `hlow` are
`corePairsF_sum_le`'s geometry: the anchors fit inside the separation, and every core spans at least
it.

The single-plaquette counterpart is `wilsonCorrConn_abs_le_coreConst_mul_rate_pow`. The advance is
that `Ao` and `Bo` are now families, so the estimate reaches products of plaquette observables, which
is what a gauge-invariant observable of any extent is built from.

DERIVED: `2` is the two anchor plaquettes `a` and `b`, the smallest separation a core can span, so
the exponent counts spans beyond them; `0` is the coupling's lower end; `1` is `coreRate`'s
convergence threshold, below which the geometric series is summable. -/
theorem wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (Ao Bo : Finset Pq) (hod : Disjoint Ao Bo) {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo)
    (hconnA : ∀ p ∈ Ao, Reach bd Ao a p) (hconnB : ∀ p ∈ Bo, Reach bd Bo b p)
    {β : ℝ} (hβ : 0 ≤ β)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
    (hr : coreRate (touchDeg bd) β < 1) (k : ℕ)
    (hu : (Ao ∪ Bo).card ≤ k + 2)
    (hlow : ∀ c ∈ corePairsF bd a Ao Bo, k + 2 ≤ (coreSpanF Ao Bo c).card) :
    |MassGap.WilsonBridge.wilsonCorrConnF (Nc := Nc) bd Ao β Bo|
      ≤ coreConstF (touchDeg bd) β Ao.card Bo.card (Ao ∪ Bo).card
        * coreRate (touchDeg bd) β ^ (k + 2 - (Ao ∪ Bo).card) := by
  have hne : a ≠ b := by
    rintro rfl
    exact Finset.disjoint_left.mp hod ha hb
  exact wilsonCorrConnF_abs_le_of_coreResummationF hN bd Ao Bo hod ha hb hconnA hconnB hβ hint
    (corePairsF bd a Ao Bo) (coreSpanF Ao Bo) (coreResummationF_holds bd ha hb hne β) _
    (corePairsF_sum_le hN bd ha hβ hr k hu hlow)

#print axioms wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow

open scoped Classical in
/-- **The core sum, resummed.** Given `Nc ≠ 0`, `0 ≤ β`, `coreRate (touchDeg bd) β < 1` and `hlow`
placing every core's span above `k + 2`,

    ∑ c ∈ corePairs bd p₀ pd, |pairTerm c| · e^{4β·touchDeg·|span c|}
      ≤ coreConst (touchDeg bd) β * coreRate (touchDeg bd) β ^ k.

Grouped by span size, bounded fibre by fibre by `corePairs_fiber_sum_le`, and summed as a geometric
series. `Fintype.card Pq` enters the proof only as the number of fibres and leaves through
`geom_sum_le_inv_one_sub_asm`, whose bound holds at every length; the right-hand side reads
`touchDeg bd`, `β` and `k` alone.

DERIVED: the `0`s are `Nc ≠ 0` and the sign hypothesis `0 ≤ β`. The `1` bounds `coreRate` at the
geometric threshold. The `2` added to `k` is the span's two anchors, from `two_le_coreSpan_card` and
`coreSpan_card_ge_of_not_mem_ball`. The `4` is the hard-core exponent of
`hard_core_outside_sq_div_partition_sq_le`. -/
theorem corePairs_sum_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate (touchDeg bd) β < 1) (k : ℕ)
    (hlow : ∀ c ∈ corePairs bd p₀ pd, k + 2 ≤ (coreSpan p₀ pd c).card) :
    ∑ c ∈ corePairs bd p₀ pd, |pairTerm (Nc := Nc) bd p₀ pd β c|
        * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ))
      ≤ coreConst (touchDeg bd) β * coreRate (touchDeg bd) β ^ k := by
  classical
  have hq1 := exp_sub_one_le_one_of_coreRate (touchDeg bd) hβ hr
  have hr0 : 0 ≤ coreRate (touchDeg bd) β := coreRate_nonneg _ hβ
  have hmaps : ∀ c ∈ corePairs bd p₀ pd,
      (coreSpan p₀ pd c).card - (k + 2) ∈ Finset.range (Fintype.card Pq + 1) := by
    intro c _
    rw [Finset.mem_range]
    have h : (coreSpan p₀ pd c).card ≤ (Finset.univ : Finset Pq).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ] at h
    omega
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => |pairTerm (Nc := Nc) bd p₀ pd β c|
      * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ)))).symm
  rw [hfib]
  have hstep : ∀ j ∈ Finset.range (Fintype.card Pq + 1),
      ∑ c ∈ (corePairs bd p₀ pd).filter
        (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
        |pairTerm (Nc := Nc) bd p₀ pd β c|
          * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ))
      ≤ (corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ k)
          * coreRate (touchDeg bd) β ^ j := by
    intro j _
    have h := corePairs_fiber_sum_le (Nc := Nc) hN bd p₀ pd hβ hq1 k j hlow
    rw [pow_add] at h
    calc ∑ c ∈ (corePairs bd p₀ pd).filter
          (fun c => (coreSpan p₀ pd c).card - (k + 2) = j),
          |pairTerm (Nc := Nc) bd p₀ pd β c|
            * Real.exp (4 * β * ((touchDeg bd * (coreSpan p₀ pd c).card : ℕ) : ℝ))
        ≤ corePrefactor (touchDeg bd) β
            * (coreRate (touchDeg bd) β ^ k * coreRate (touchDeg bd) β ^ j) := h
      _ = (corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ k)
            * coreRate (touchDeg bd) β ^ j := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hpre : 0 ≤ corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ k :=
    mul_nonneg (le_trans zero_le_one (one_le_corePrefactor _ hβ)) (pow_nonneg hr0 k)
  have hgeom := geom_sum_le_inv_one_sub_asm hr0 hr (Fintype.card Pq + 1)
  calc (corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ k)
        * ∑ j ∈ Finset.range (Fintype.card Pq + 1), coreRate (touchDeg bd) β ^ j
      ≤ (corePrefactor (touchDeg bd) β * coreRate (touchDeg bd) β ^ k)
          * (1 - coreRate (touchDeg bd) β)⁻¹ := mul_le_mul_of_nonneg_left hgeom hpre
    _ = coreConst (touchDeg bd) β * coreRate (touchDeg bd) β ^ k := by
        unfold coreConst
        rw [div_eq_mul_inv]
        ring

#print axioms corePairs_sum_le

/-! #### The last side condition -/

open scoped Classical in
/-- **A plaquette product times a product of activated weights is integrable** against product Haar,
for any `β` and any `D`, `E`, given `Nc ≠ 0`. This is the `hint` hypothesis of
`wilsonCorrConn_abs_le_core_sum` and `wilsonCorrConn_eq_bridging_sum`, proved.

The observable lies in `[0, 2]` (`wilsonPlaqObs_le_two`) and the activated weight within `e^{2|β|}`
of one (`boltz_factor_bound`), so the integrand is bounded by a constant against a probability
measure. That constant carries `Fintype.card Pq`; it appears in the proof and not in the statement.

DERIVED: the `0` is the hypothesis `Nc ≠ 0`. The `1` subtracted from the exponential is
`boltz_eq_subset_sum`'s activated weight. -/
theorem integrable_obs_mul_wprod (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (D E : Finset Pq) :
    Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hmw : Measurable (fun U : Lk → MassGap.SUN.SU Nc =>
      ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))) :=
    Finset.measurable_prod _ (fun p _ => (measurable_wfun β).comp
      (measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p)))
  have hmeas : Measurable (fun U : Lk → MassGap.SUN.SU Nc =>
      (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1)) :=
    Measurable.mul (Finset.measurable_prod _
      (fun p _ => measurable_wilsonPlaqObs (N := Nc) bd p)) hmw
  refine (integrable_const ((2 : ℝ) ^ (Fintype.card Pq)
      * Real.exp (2 * |β|) ^ (Fintype.card Pq))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun U => ?_))
  have hone : (1 : ℝ) ≤ Real.exp (2 * |β|) := Real.one_le_exp (by positivity)
  have h1 : |∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U| ≤ (2 : ℝ) ^ (Fintype.card Pq) := by
    rw [Finset.abs_prod]
    calc ∏ p ∈ D, |wilsonPlaqObs (N := Nc) bd p U|
        ≤ ∏ _p ∈ D, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => ?_)
          rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd p U)]
          exact wilsonPlaqObs_le_two hN bd p U
      _ = (2 : ℝ) ^ D.card := by rw [Finset.prod_const]
      _ ≤ (2 : ℝ) ^ (Fintype.card Pq) :=
          pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ D)
  have h2 : |∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1)|
      ≤ Real.exp (2 * |β|) ^ (Fintype.card Pq) := by
    rw [Finset.abs_prod]
    have hstep : ∀ p ∈ E,
        |Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1|
          ≤ Real.exp (2 * |β|) := by
      intro p _
      have hb := boltz_factor_bound (β := β)
        (wilsonDensity_nonneg hN (wilsonHol bd p U))
        (wilsonDensity_le_two hN (wilsonHol bd p U))
      linarith
    calc ∏ p ∈ E, |Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1|
        ≤ ∏ _p ∈ E, Real.exp (2 * |β|) :=
          Finset.prod_le_prod (fun p _ => abs_nonneg _) hstep
      _ = Real.exp (2 * |β|) ^ E.card := by rw [Finset.prod_const]
      _ ≤ Real.exp (2 * |β|) ^ (Fintype.card Pq) :=
          pow_le_pow_right₀ hone (Finset.card_le_univ E)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

#print axioms integrable_obs_mul_wprod

/-! #### The assembled bounds -/

open scoped Classical in
/-- **`|wilsonCorrConn bd p₀ β pd| ≤ coreConst (touchDeg bd) β`**, given `Nc ≠ 0`, `p₀ ≠ pd`,
`0 ≤ β` and `coreRate (touchDeg bd) β < 1`. `corePairs_sum_le` at `k = 0`, where
`two_le_coreSpan_card` supplies `hlow`, fed to `wilsonCorrConn_abs_le_core_sum` with
`integrable_obs_mul_wprod` discharging the side condition. The right-hand side mentions only
`touchDeg bd` and `β`.

DERIVED: the `0`s are `Nc ≠ 0` and the sign hypothesis `0 ≤ β`. The `1` bounds `coreRate` at the
geometric threshold. -/
theorem wilsonCorrConn_abs_le_coreConst (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) (hne : p₀ ≠ pd) {β : ℝ} (hβ : 0 ≤ β)
    (hr : coreRate (touchDeg bd) β < 1) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd| ≤ coreConst (touchDeg bd) β := by
  classical
  have hlow : ∀ c ∈ corePairs bd p₀ pd, 0 + 2 ≤ (coreSpan p₀ pd c).card := by
    intro c _
    simpa using two_le_coreSpan_card p₀ pd hne c
  have h := corePairs_sum_le (Nc := Nc) hN bd p₀ pd hβ hr 0 hlow
  rw [pow_zero, mul_one] at h
  exact wilsonCorrConn_abs_le_core_sum hN bd p₀ pd hne hβ
    (integrable_obs_mul_wprod hN bd β) _ h

#print axioms wilsonCorrConn_abs_le_coreConst

open scoped Classical in
/-- **`|wilsonCorrConn bd p₀ β pd| ≤ coreConst (touchDeg bd) β * coreRate (touchDeg bd) β ^ k`**,
given `Nc ≠ 0`, `0 ≤ β`, `coreRate (touchDeg bd) β < 1` and `pd ∉ ball bd p₀ k`.

The separation empties every fibre of the core sum below `k`
(`coreSpan_card_ge_of_not_mem_ball`), so the geometric series starts there. `p₀ ≠ pd` is not a
hypothesis: it follows from `pd ∉ ball bd p₀ k` through `self_mem_ball`. Both the constant and the
rate read `touchDeg bd` and `β` alone; `k` is a parameter, not quantified inside.

DERIVED: the `0`s are `Nc ≠ 0` and the sign hypothesis `0 ≤ β`. The `1` bounds `coreRate` at the
geometric threshold. -/
theorem wilsonCorrConn_abs_le_coreConst_mul_rate_pow (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) {β : ℝ} (hβ : 0 ≤ β)
    (hr : coreRate (touchDeg bd) β < 1) (k : ℕ) (hk : pd ∉ ball bd p₀ k) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd|
      ≤ coreConst (touchDeg bd) β * coreRate (touchDeg bd) β ^ k := by
  classical
  have hne : p₀ ≠ pd := by
    rintro rfl
    exact hk (self_mem_ball bd p₀ k)
  have hlow : ∀ c ∈ corePairs bd p₀ pd, k + 2 ≤ (coreSpan p₀ pd c).card := by
    intro c hc
    exact coreSpan_card_ge_of_not_mem_ball bd p₀ pd hne k hk (mem_corePairs.mp hc)
  exact wilsonCorrConn_abs_le_core_sum hN bd p₀ pd hne hβ
    (integrable_obs_mul_wprod hN bd β) _
    (corePairs_sum_le (Nc := Nc) hN bd p₀ pd hβ hr k hlow)

#print axioms wilsonCorrConn_abs_le_coreConst_mul_rate_pow

/-! #### Controls on the hypotheses

Each of these exhibits a case in which the hypotheses above fail or the conclusion is vacuous. -/

open scoped Classical in
/-- **No family of plaquettes can lie outside `ball bd p₀ d` at every `d`, if each is reachable from
`p₀`.** On a finite `Pq` the touch-levels have a largest value `R`, so `ball bd p₀ R` already
contains every reachable plaquette and `pf R` has nowhere to be.

So a bound indexed by `∀ d : ℕ` is unsatisfiable here. `wilsonCorrConn_abs_le_coreConst_mul_rate_pow`
fixes `k` instead and asks only `pd ∉ ball bd p₀ k`.

DERIVED: no numeral. -/
theorem no_sep_family_of_reachable (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (pf : ℕ → Pq)
    (hreach : ∀ d : ℕ, ∃ m, pf d ∈ ball bd p₀ m) :
    ¬ (∀ d : ℕ, pf d ∉ ball bd p₀ d) := by
  classical
  intro hsep
  have hle : touchLvl bd p₀ (pf (Finset.univ.sup (fun q : Pq => touchLvl bd p₀ q)))
      ≤ Finset.univ.sup (fun q : Pq => touchLvl bd p₀ q) :=
    Finset.le_sup (f := fun q : Pq => touchLvl bd p₀ q) (Finset.mem_univ _)
  exact hsep _ (ball_mono bd p₀ hle
    (mem_ball_touchLvl bd p₀ _ (hreach (Finset.univ.sup (fun q : Pq => touchLvl bd p₀ q)))))

#print axioms no_sep_family_of_reachable

open scoped Classical in
/-- **A plaquette in no ball around `p₀` has connected correlation zero with it**, at every `β`. Such
a plaquette lies outside `compOf bd Finset.univ p₀`, which is touch-closed, so
`wilsonCorrConn_eq_zero_of_touch_closed` applies. No rate hypothesis and no expansion enter.

With `no_sep_family_of_reachable`, this covers the two cases of a separation family indexed by
`∀ d : ℕ`: either no such family exists, or it names a plaquette whose correlation with `p₀` is zero.

DERIVED: the `0` is the value of the connected correlation. -/
theorem wilsonCorrConn_eq_zero_of_no_ball (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (hd : ∀ m : ℕ, pd ∉ ball bd p₀ m) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd = 0 := by
  classical
  have hnot : pd ∉ compOf bd Finset.univ p₀ := by
    intro hmem
    obtain ⟨m, hm⟩ := exists_mem_ball_of_reach bd (mem_compOf.mp hmem).2
    exact hd m hm
  refine wilsonCorrConn_eq_zero_of_touch_closed bd p₀ pd (compOf bd Finset.univ p₀)
    ?_ (self_mem_compOf (Finset.mem_univ p₀)) hnot β
  intro p hp q hq
  exact compOf_closed bd Finset.univ p₀ p
    (Finset.mem_inter.mpr ⟨Finset.mem_univ p, hp⟩) q
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq⟩)

#print axioms wilsonCorrConn_eq_zero_of_no_ball

/-- **`1 ≤ coreRate K β` and `0 ≤ β` give `coreConst K β ≤ 0`.** `coreConst` is
`corePrefactor / (1 - coreRate)` with the prefactor at least `128` (`le_corePrefactor`), so at rate
one or above the quotient is non-positive and a bound `|ρ_conn| ≤ coreConst · rᵏ` would force the
correlation to vanish. The hypothesis `coreRate (touchDeg bd) β < 1` of
`wilsonCorrConn_abs_le_coreConst_mul_rate_pow` therefore carries weight.

DERIVED: the first `0` is the sign hypothesis on `β`; the `1` is the geometric threshold the rate is
assumed to reach; the second `0` is the upper bound on the constant. -/
theorem coreConst_nonpos_of_one_le (K : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hr : 1 ≤ coreRate K β) :
    coreConst K β ≤ 0 := by
  have hP := le_corePrefactor K (β := β) hβ
  have hden : 1 - coreRate K β ≤ 0 := by linarith
  unfold coreConst
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) hden

#print axioms coreConst_nonpos_of_one_le

/-! #### Monotonicity in the degree

`touchDeg bd` is exact; what a caller usually has is a bound on it, such as `touchDeg_bd_le`'s
`16 * dim`. Every factor of the estimate is monotone in the degree, so the bound may be substituted
throughout. `wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le` is the substituted statement. -/

theorem coreRate_mono {β : ℝ} (hβ : 0 ≤ β) {K K' : ℕ} (hK : K ≤ K') :
    coreRate K β ≤ coreRate K' β := by
  have hq0 : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (x := 2 * β) (by linarith)
    linarith
  have hc : (K : ℝ) ≤ (K' : ℝ) := Nat.cast_le.mpr hK
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : 4 * ((K : ℝ) + 1) ^ 2 ≤ 4 * ((K' : ℝ) + 1) ^ 2 := by nlinarith
  have hE : Real.exp (4 * β * (K : ℝ)) ≤ Real.exp (4 * β * (K' : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h1 : (4 * ((K : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1)
      ≤ (4 * ((K' : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) :=
    mul_le_mul_of_nonneg_right hA hq0
  have hb : (0 : ℝ) ≤ (4 * ((K' : ℝ) + 1) ^ 2) * (Real.exp (2 * β) - 1) :=
    mul_nonneg (by positivity) hq0
  unfold coreRate
  exact mul_le_mul h1 hE (Real.exp_pos _).le hb

theorem corePrefactor_mono {β : ℝ} (hβ : 0 ≤ β) {K K' : ℕ} (hK : K ≤ K') :
    corePrefactor K β ≤ corePrefactor K' β := by
  have hc : (K : ℝ) ≤ (K' : ℝ) := Nat.cast_le.mpr hK
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : 4 * ((K : ℝ) + 1) ^ 2 ≤ 4 * ((K' : ℝ) + 1) ^ 2 := by nlinarith
  have hA0 : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by positivity
  have hE : Real.exp (4 * β * (K : ℝ)) ≤ Real.exp (4 * β * (K' : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hE0 : (0 : ℝ) < Real.exp (4 * β * (K : ℝ)) := Real.exp_pos _
  have hsq1 : (4 * ((K : ℝ) + 1) ^ 2) ^ 2 ≤ (4 * ((K' : ℝ) + 1) ^ 2) ^ 2 := by nlinarith
  have hsq2 : Real.exp (4 * β * (K : ℝ)) ^ 2 ≤ Real.exp (4 * β * (K' : ℝ)) ^ 2 := by nlinarith
  unfold corePrefactor
  have hsq10 : (0 : ℝ) ≤ (4 * ((K : ℝ) + 1) ^ 2) ^ 2 := by positivity
  have hsq20 : (0 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) ^ 2 := by positivity
  nlinarith

/-- **`0 < y ≤ x` gives `x⁻¹ ≤ y⁻¹`.** A smaller positive denominator has the bigger reciprocal.
Proved here rather than named from the library, as with the other arithmetic in this section.

DERIVED: the `0` is the strict positivity of `y`, without which the reciprocals are not
ordered. -/
theorem inv_le_inv_asm {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) : x⁻¹ ≤ y⁻¹ := by
  have hx : (0 : ℝ) < x := lt_of_lt_of_le hy hxy
  have e1 : x⁻¹ * x = 1 := by field_simp
  have e2 : y⁻¹ * y = 1 := by field_simp
  nlinarith [inv_pos.mpr hx, inv_pos.mpr hy, mul_pos hx hy]

theorem coreConst_mono {β : ℝ} (hβ : 0 ≤ β) {K K' : ℕ} (hK : K ≤ K')
    (hr' : coreRate K' β < 1) : coreConst K β ≤ coreConst K' β := by
  have hrle := coreRate_mono hβ hK
  have h1 : (0 : ℝ) < 1 - coreRate K' β := by linarith
  have h2 : (0 : ℝ) < 1 - coreRate K β := by linarith
  have hple := corePrefactor_mono hβ hK
  have hP' : (1 : ℝ) ≤ corePrefactor K' β := one_le_corePrefactor K' hβ
  have hs : 1 - coreRate K' β ≤ 1 - coreRate K β := by linarith
  have hinv : (1 - coreRate K β)⁻¹ ≤ (1 - coreRate K' β)⁻¹ := inv_le_inv_asm h1 hs
  unfold coreConst
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hple hinv (inv_nonneg.mpr h2.le) (by linarith)

open scoped Classical in
/-- **`|wilsonCorrConn bd p₀ β pd| ≤ coreConst K β * coreRate K β ^ k`** for any `K` with
`touchDeg bd ≤ K`, given `Nc ≠ 0`, `0 ≤ β`, `coreRate K β < 1` and `pd ∉ ball bd p₀ k`.

`wilsonCorrConn_abs_le_coreConst_mul_rate_pow` with `coreRate_mono` and `coreConst_mono` carrying the
bound across. Note the rate hypothesis is at `K`, which is the stronger one. This is what takes the
estimate to a named geometry: `touchDeg_bd_le` supplies `K = 16 * dim` on the periodic hypercubic
lattice.

DERIVED: the `0`s are `Nc ≠ 0` and the sign hypothesis `0 ≤ β`. The `1` bounds `coreRate K β` at the
geometric threshold. -/
theorem wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le (hN : Nc ≠ 0)
    (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) {β : ℝ} (hβ : 0 ≤ β)
    (K : ℕ) (hK : touchDeg bd ≤ K) (hr : coreRate K β < 1)
    (k : ℕ) (hk : pd ∉ ball bd p₀ k) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd|
      ≤ coreConst K β * coreRate K β ^ k := by
  classical
  have hrle := coreRate_mono hβ hK
  have hrlt : coreRate (touchDeg bd) β < 1 := lt_of_le_of_lt hrle hr
  have hbase := wilsonCorrConn_abs_le_coreConst_mul_rate_pow (Nc := Nc) hN bd p₀ pd hβ hrlt k hk
  refine le_trans hbase ?_
  have hCC := coreConst_mono hβ hK hr
  have hpow : coreRate (touchDeg bd) β ^ k ≤ coreRate K β ^ k :=
    pow_le_pow_left₀ (coreRate_nonneg _ hβ) hrle k
  have hCK : (0 : ℝ) ≤ coreConst K β := by
    unfold coreConst
    have hP := le_corePrefactor K (β := β) hβ
    have : (0 : ℝ) < 1 - coreRate K β := by linarith
    positivity
  exact mul_le_mul hCC hpow (pow_nonneg (coreRate_nonneg _ hβ) k) hCK

#print axioms wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le

/-- **`corePrefactorG` is monotone in the touch degree**, at `0 ≤ C` and `0 ≤ β`: both the branching
factor `4 (K + 1)²` and the hard-core factor `e^{4βK}` grow with `K`.

DERIVED: the `4`, `1` and `2` are `corePrefactorG`'s; the `0`s are the sign hypotheses. -/
theorem corePrefactorG_mono {C : ℝ} (hC : 0 ≤ C) {β : ℝ} (hβ : 0 ≤ β) {K K' : ℕ}
    (hK : K ≤ K') (u : ℕ) : corePrefactorG C K β u ≤ corePrefactorG C K' β u := by
  have hc : (K : ℝ) ≤ (K' : ℝ) := Nat.cast_le.mpr hK
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : 4 * ((K : ℝ) + 1) ^ 2 ≤ 4 * ((K' : ℝ) + 1) ^ 2 := by nlinarith
  have hE : Real.exp (4 * β * (K : ℝ)) ≤ Real.exp (4 * β * (K' : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold corePrefactorG
  have h1 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2) hA u
  have h2 := pow_le_pow_left₀ (Real.exp_pos _).le hE u
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 (by positivity)
    (mul_nonneg hC (by positivity))

#print axioms corePrefactorG_mono

/-- **`coreConstG` is monotone in the touch degree** below the geometric threshold: the prefactor grows
(`corePrefactorG_mono`) and `1 − coreRate` shrinks (`coreRate_mono`).

DERIVED: the `0`s are the sign hypotheses; the `1` is the geometric threshold. -/
theorem coreConstG_mono {C : ℝ} (hC : 0 ≤ C) {β : ℝ} (hβ : 0 ≤ β) {K K' : ℕ} (hK : K ≤ K')
    (hr' : coreRate K' β < 1) (u : ℕ) : coreConstG C K β u ≤ coreConstG C K' β u := by
  have hrle := coreRate_mono hβ hK
  have h1 : (0 : ℝ) < 1 - coreRate K' β := by linarith
  have h2 : (0 : ℝ) < 1 - coreRate K β := by linarith
  have hple := corePrefactorG_mono hC hβ hK u
  have hP' : (0 : ℝ) ≤ corePrefactorG C K' β u := by
    unfold corePrefactorG; exact mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  have hinv : (1 - coreRate K β)⁻¹ ≤ (1 - coreRate K' β)⁻¹ := inv_le_inv_asm h1 (by linarith)
  unfold coreConstG
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hple hinv (inv_nonneg.mpr h2.le) hP'

#print axioms coreConstG_mono

open scoped Classical in
/-- **L2 at separation `k`, for any touch-degree bound `K`.** Two bounded local observables on
disjoint supports, with anchor sets `Ao ⊇ linkHalo Sa`, `Bo ⊇ linkHalo Sb` touch-connected from base
points `a`, `b`, `b` outside the `k`-ball of `a`, and anchors of total size `u ≤ k + 2`, satisfy

    |wilsonCorrConnObs bd O₁ O₂ β| ≤ coreConstG (2 c₁ c₂) K β u · coreRate K β ^ (k + 2 − u),

`u = |Ao ∪ Bo|`, for every `K ≥ touchDeg bd` with `coreRate K β < 1`. Every
core contains `a` and `b`, so it spans at least `k + 2` plaquettes
(`coreSpanF_card_ge_of_not_mem_ball`); `coreRate_mono` and `coreConstG_mono` carry the bound to `K`.

DERIVED: the `2` in `2 c₁ c₂` is `pairTermObs_abs_le`'s two products; the `2` in `k + 2` is the two
base points; the `0`s are `Nc ≠ 0` and `0 ≤ β`; the `1` is the geometric threshold. -/
theorem wilsonCorrConnObs_abs_le_of_not_mem_ball (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    {O₁ O₂ : (Lk → MassGap.SUN.SU Nc) → ℝ} {Sa Sb : Finset Lk} (hab : Disjoint Sa Sb)
    (h₁ : LocalOnLinks (Nc := Nc) Sa O₁) (h₂ : LocalOnLinks (Nc := Nc) Sb O₂)
    {c₁ c₂ : ℝ} (hc₁ : ∀ U, |O₁ U| ≤ c₁) (hc₂ : ∀ U, |O₂ U| ≤ c₂)
    {Ao Bo : Finset Pq} (hAo : linkHalo bd Sa ⊆ Ao)
    (hBo : linkHalo bd Sb ⊆ Bo)
    {a b : Pq} (ha : a ∈ Ao) (hb : b ∈ Bo)
    (hconnA : ∀ p ∈ Ao, Reach bd (Ao) a p)
    (hconnB : ∀ p ∈ Bo, Reach bd (Bo) b p)
    {β : ℝ} (hβ : 0 ≤ β) (K : ℕ) (hK : touchDeg bd ≤ K) (hr : coreRate K β < 1) (k : ℕ)
    (hk : b ∉ ball bd a k) (hu : (Ao ∪ Bo).card ≤ k + 2) :
    |wilsonCorrConnObs (Nc := Nc) bd O₁ O₂ β|
      ≤ coreConstG (2 * (c₁ * c₂)) K β (Ao ∪ Bo).card
        * coreRate K β ^ (k + 2 - (Ao ∪ Bo).card) := by
  classical
  have hne : a ≠ b := fun h => hk (h ▸ self_mem_ball bd a k)
  have h0₁ : 0 ≤ c₁ := (abs_nonneg _).trans (hc₁ (fun _ => 1))
  have h0₂ : 0 ≤ c₂ := (abs_nonneg _).trans (hc₂ (fun _ => 1))
  have hC : (0 : ℝ) ≤ 2 * (c₁ * c₂) := mul_nonneg zero_le_two (mul_nonneg h0₁ h0₂)
  have hrle := coreRate_mono hβ hK
  have hrlt : coreRate (touchDeg bd) β < 1 := lt_of_le_of_lt hrle hr
  have hbase := wilsonCorrConnObs_abs_le_coreConstG_mul_rate_pow hN bd hab h₁ h₂ hc₁ hc₂ hAo hBo ha hb hne
    hconnA hconnB hβ hrlt k hu
    (fun c hc => coreSpanF_card_ge_of_not_mem_ball bd ha hb hne k hk (mem_corePairsF.mp hc))
  refine le_trans hbase ?_
  have hCC := coreConstG_mono hC hβ hK hr (Ao ∪ Bo).card
  have hpow := pow_le_pow_left₀ (coreRate_nonneg _ hβ) hrle
    (k + 2 - (Ao ∪ Bo).card)
  have hCK : (0 : ℝ) ≤ coreConstG (2 * (c₁ * c₂)) K β (Ao ∪ Bo).card := by
    unfold coreConstG corePrefactorG
    have : (0 : ℝ) < 1 - coreRate K β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)) this.le
  exact mul_le_mul hCC hpow (pow_nonneg (coreRate_nonneg _ hβ) _) hCK

#print axioms wilsonCorrConnObs_abs_le_of_not_mem_ball

end CoreAssembly

section AssemblyHypercubic

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge
open MassGap.WilsonHypercubic

variable {Nc dim n : ℕ} [NeZero n]

open scoped Classical in
/-- **`|wilsonCorrConn bd p₀ β pd| ≤ coreConst (16 * dim) β * coreRate (16 * dim) β ^ k`** on the
periodic `dim`-dimensional lattice `Site dim n`, given `Nc ≠ 0`, `0 ≤ β`,
`coreRate (16 * dim) β < 1` and `pd ∉ ball bd p₀ k`.
`wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le` at `K = 16 * dim` through `touchDeg_bd_le`. The
extent `n` appears in neither the rate nor the constant. The index `k` is still a touch-ball radius;
`siteAtHyper_not_mem_ball` converts it to a lag.

DERIVED: the `0`s are `Nc ≠ 0` and the sign hypothesis `0 ≤ β`. The `1` bounds the rate at the
geometric threshold. The `16 * dim` is `touchDeg_bd_le`'s bound on the degree, four boundary links
times four word slots times the choices of second direction. -/
theorem wilsonCorrConn_abs_le_coreConst_mul_rate_pow_hypercubic (hN : Nc ≠ 0)
    (p₀ pd : Plaq dim n) {β : ℝ} (hβ : 0 ≤ β) (hr : coreRate (16 * dim) β < 1)
    (k : ℕ) (hk : pd ∉ ball (bd (d := dim) (n := n)) p₀ k) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) (bd (d := dim) (n := n)) p₀ β pd|
      ≤ coreConst (16 * dim) β * coreRate (16 * dim) β ^ k :=
  wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le (Nc := Nc) hN _ p₀ pd hβ (16 * dim)
    touchDeg_bd_le hr k hk

#print axioms wilsonCorrConn_abs_le_coreConst_mul_rate_pow_hypercubic

/-- **There is a `b > 0` with `coreRate (16 * dim) β < 1` for every `β` in `[0, b)`.**
`core_rate_lt_one_of_small` at `K = 16 * dim`, so the rate hypothesis of
`wilsonCorrConn_abs_le_coreConst_mul_rate_pow_hypercubic` is satisfiable. `b` is existential and
depends on `dim`; no value for it is named.

DERIVED: the `0`s are the lower end of the interval and the strict lower bound on `b`. The `1` is the
geometric threshold. The `16 * dim` is `touchDeg_bd_le`'s bound on the degree. -/
theorem core_rate_lt_one_of_small_hypercubic (dim : ℕ) :
    ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → coreRate (16 * dim) β < 1 :=
  core_rate_lt_one_of_small (16 * dim)

#print axioms core_rate_lt_one_of_small_hypercubic

end AssemblyHypercubic

end MassGap.StrongCoupling
-- ==== END assembled core sum ====

-- ==== BEGIN lag-to-ball bridge ====

namespace MassGap.StrongCoupling

/-! ## From a lag on the periodic lattice to a touch-ball radius

`wilsonCorrConn_abs_le_coreConst_mul_rate_pow` decays in `k` whenever `pd ∉ ball bd p₀ k`, a
touch-distance. A `Moment.Read` is indexed by a lag `d : Fin (N+1)`, carried to a plaquette by
`WilsonBridge.siteAtHyper`. This section relates the two indices.

The conversion factor is read off `bd`. Two plaquettes touch when they share a link, so the question
is how far one shared link moves a coordinate. Every link of the plaquette `((a,b), x)` sits at one
of the sites `x`, `x + â`, `x + b̂`, so along a fixed axis `τ` its site's `τ` coordinate is `x τ` or
`x τ + 1` and nothing else (`link_site_coord`, from `shift_coord`). A shared link therefore pins the
two plaquettes' `τ` coordinates to within one lattice step. The constant is `1`: one touch-step is at
most one lattice step along any axis, and `touch_advances_one` exhibits a touch that attains it.

The lattice is a torus, which caps the radius. The `τ` coordinate lives in `Fin n`, so the distance
to be crossed is the circle distance `circDist a = min a (n − a)` and not the raw lag. At `n = N + 1`
that is `Moment.circLag` definitionally (`circDist_eq_circLag`). `lag_last_mem_ball_two` shows the
cap is not a conservatism: the plaquette at raw lag `N` is two touch-steps from the origin, so a
bridge stated in the raw lag would be false, which `raw_lag_radius_refuted` records.
-/

section CircleDistance

/-- The number of lattice steps from the origin to `a` on the circle of `n` sites:
`min a (n - a)`, the distance the periodic lattice carries and the one `Moment.circLag` measures.

DERIVED: no numeral. The `min` is the two ways round the circle and `n - a` is the way that wraps,
both forced by the identification `a ∼ a + n` that `Fin n` carries. -/
def circDist {n : ℕ} (a : Fin n) : ℕ := min (a : ℕ) (n - (a : ℕ))

/-- **`circDist d = Moment.circLag d` on `Fin (N + 1)`**, by `rfl`: the two definitions agree, and
nothing is converted.

DERIVED: the `1` in `Fin (N + 1)` is `Moment.circLag`'s index type, whose extent is `N + 1`. -/
theorem circDist_eq_circLag {N : ℕ} (d : Fin (N + 1)) : circDist d = Moment.circLag d := rfl

theorem circDist_zero {n : ℕ} [NeZero n] : circDist (0 : Fin n) = 0 := by
  simp [circDist]

/-- **The value of `a + 1` in `Fin n` is either `a + 1` or `0` with `a + 1 = n`.** The two cases of
the wrap, needed because `circDist` is defined on the underlying natural number.

DERIVED: the `1`s are one lattice step, the increment being taken. The `0` is the wrapped value at
the top of `Fin n`. -/
theorem val_add_one_cases {n : ℕ} [NeZero n] (a : Fin n) :
    ((a + 1 : Fin n) : ℕ) = (a : ℕ) + 1 ∨
      (((a + 1 : Fin n) : ℕ) = 0 ∧ (a : ℕ) + 1 = n) := by
  have hlt : (a : ℕ) < n := a.isLt
  have h1 : ((1 : Fin n) : ℕ) = 1 % n := rfl
  have hval : ((a + 1 : Fin n) : ℕ) = ((a : ℕ) + 1) % n := by
    rw [Fin.val_add, h1, Nat.add_mod_mod]
  rcases Nat.lt_or_ge ((a : ℕ) + 1) n with hc | hc
  · exact Or.inl (by rw [hval, Nat.mod_eq_of_lt hc])
  · have he : (a : ℕ) + 1 = n := by omega
    exact Or.inr ⟨by rw [hval, he, Nat.mod_self], he⟩

/-- **`circDist (a + 1) ≤ circDist a + 1`**: one step forward costs at most one on the circle,
including across the wrap.

DERIVED: the `1`s are one lattice step, forward and in the bound. -/
theorem circDist_succ_le {n : ℕ} [NeZero n] (a : Fin n) :
    circDist (a + 1) ≤ circDist a + 1 := by
  have hlt : (a : ℕ) < n := a.isLt
  rcases val_add_one_cases a with h | ⟨h, hn⟩ <;> · unfold circDist; rw [h]; omega

/-- **`circDist a ≤ circDist (a + 1) + 1`**: one step back costs at most one on the circle. The
companion of `circDist_succ_le`, needed because a touch can move a coordinate either way.

DERIVED: the `1`s are one lattice step, forward and in the bound. -/
theorem circDist_le_succ {n : ℕ} [NeZero n] (a : Fin n) :
    circDist a ≤ circDist (a + 1) + 1 := by
  have hlt : (a : ℕ) < n := a.isLt
  rcases val_add_one_cases a with h | ⟨h, hn⟩ <;> · unfold circDist; rw [h]; omega

/-- **`a + 1 = b + 1` gives `a = b` in `Fin n`**: the successor is injective, and the wrap does not
merge two sites. `NeZero n` is required, `Fin 0` having no elements to speak of.

DERIVED: the `1`s are the lattice step added to each side. -/
theorem fin_add_one_inj {n : ℕ} [NeZero n] {a b : Fin n} (h : a + 1 = b + 1) : a = b := by
  have hva := val_add_one_cases a
  have hvb := val_add_one_cases b
  have hv : ((a + 1 : Fin n) : ℕ) = ((b + 1 : Fin n) : ℕ) := by rw [h]
  have hla : (a : ℕ) < n := a.isLt
  have hlb : (b : ℕ) < n := b.isLt
  refine Fin.val_injective ?_
  rcases hva with hA | ⟨hA, hAn⟩ <;> rcases hvb with hB | ⟨hB, hBn⟩ <;> omega

end CircleDistance

section BallLevel

variable {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- **A level function is at most `k` on the `k`-step ball.** Any `lvl : Pq → ℕ` with `lvl p₀ = 0`
that rises by at most one across a touch satisfies `lvl q ≤ k` for every `q ∈ ball bd p₀ k`. The
converse direction to `card_ge_of_reach_of_lvl`, and the form a radius argument takes; the induction
is on `ball`'s recursion.

DERIVED: the `0` is the hypothesis `lvl p₀ = 0`; the `1` is the Lipschitz step
`lvl q ≤ lvl p + 1`. -/
theorem lvl_le_of_mem_ball (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (lvl : Pq → ℕ)
    (h0 : lvl p₀ = 0) (hlip : ∀ p q : Pq, Touch bd p q → lvl q ≤ lvl p + 1) :
    ∀ (k : ℕ) (q : Pq), q ∈ ball bd p₀ k → lvl q ≤ k := by
  classical
  intro k
  induction k with
  | zero =>
      intro q hq
      have hq' : q ∈ ({p₀} : Finset Pq) := hq
      rw [Finset.mem_singleton.mp hq', h0]
  | succ m ih =>
      intro q hq
      rcases Finset.mem_union.mp hq with h | h
      · exact le_trans (ih q h) (Nat.le_succ m)
      · obtain ⟨p, hp, ht⟩ := (Finset.mem_filter.mp h).2
        exact le_trans (hlip p q ht) (Nat.add_le_add_right (ih p hp) 1)

#print axioms lvl_le_of_mem_ball

end BallLevel

section LagBallHypercubic

open MassGap.WilsonHypercubic

variable {dim n : ℕ} [NeZero n]

/-- **`shift μ x τ = x τ` or `x τ + 1`.** A shift moves one coordinate by one, so along any axis `τ`
the shifted site's `τ` coordinate is the original or its successor, according as `τ = μ`.

DERIVED: the `1` is the lattice step `shift` adds. -/
theorem shift_coord (τ μ : Fin dim) (x : Site dim n) :
    shift μ x τ = x τ ∨ shift μ x τ = x τ + 1 := by
  by_cases h : τ = μ
  · subst h; exact Or.inr (by simp [shift])
  · exact Or.inl (by simp [shift, h])

/-- **A link of the plaquette `((a, b), x)` sits at `x τ` or `x τ + 1` along every axis `τ`.** The
boundary word names the sites `x`, `shift a x` and `shift b x` and no others, so `shift_coord`
applies to each. This is the geometric input of the lag-to-ball bridge.

DERIVED: the `1` is `shift_coord`'s lattice step. -/
theorem link_site_coord (τ a b : Fin dim) (x : Site dim n) (ld : Fin dim) (ls : Site dim n)
    (hl : (ld, ls) ∈ linkSupp (bd (d := dim) (n := n)) ((a, b), x)) :
    ls τ = x τ ∨ ls τ = x τ + 1 := by
  have hsite : ls = x ∨ ls = shift a x ∨ ls = shift b x := by
    simp only [linkSupp, bd, List.map_cons, List.map_nil, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hl
    tauto
  rcases hsite with h | h | h
  · exact Or.inl (by rw [h])
  · rw [h]; exact shift_coord τ a x
  · rw [h]; exact shift_coord τ b x

/-- The level of a plaquette along an axis: `circDist` of its site's `τ` coordinate. The plane the
plaquette spans does not enter.

DERIVED: the `2` in `q.2` is a projection, not a numeral. -/
def axisLvl (τ : Fin dim) (q : Plaq dim n) : ℕ := circDist (q.2 τ)

/-- **`Touch bd p q` gives `axisLvl τ q ≤ axisLvl τ p + 1`.** The shared link sits within one step of
each plaquette's site (`link_site_coord`), so the two sites are within one step of each other on the
circle. Four cases, closed by `circDist_succ_le`, `circDist_le_succ` and `fin_add_one_inj`. This is
the Lipschitz hypothesis `lvl_le_of_mem_ball` takes.

DERIVED: the `1` is one lattice step, `link_site_coord`'s. -/
theorem axisLvl_lipschitz (τ : Fin dim) (p q : Plaq dim n)
    (h : Touch (bd (d := dim) (n := n)) p q) : axisLvl τ q ≤ axisLvl τ p + 1 := by
  obtain ⟨⟨a, b⟩, x⟩ := p
  obtain ⟨⟨c, e⟩, y⟩ := q
  obtain ⟨⟨ld, ls⟩, hp, hq⟩ := h
  have hP := link_site_coord τ a b x ld ls hp
  have hQ := link_site_coord τ c e y ld ls hq
  show circDist (y τ) ≤ circDist (x τ) + 1
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · rw [← hP, ← hQ]; omega
  · -- ls τ = x τ and ls τ = y τ + 1
    have : circDist (y τ) ≤ circDist (y τ + 1) + 1 := circDist_le_succ (y τ)
    rw [← hQ, hP] at this
    omega
  · -- ls τ = x τ + 1 and ls τ = y τ
    have : circDist (x τ + 1) ≤ circDist (x τ) + 1 := circDist_succ_le (x τ)
    rw [← hP, hQ] at this
    omega
  · -- ls τ = x τ + 1 and ls τ = y τ + 1
    have hxy : x τ = y τ := fin_add_one_inj (by rw [← hP, ← hQ])
    rw [hxy]; omega

/-- **The plaquette at lag `lag` lies outside `ball bd p₀ k` for every `k < circDist lag`.** With the
plane spanned by `(μ, ν)` and the lag running along `τ`, `((μ, ν), siteAtHyper τ lag)` is not in the
`k`-step touch-ball of `((μ, ν), fun _ => 0)`.

`axisLvl τ` is zero at the origin plaquette, equals `circDist lag` at the lag-`lag` plaquette, and
rises by at most one per touch (`axisLvl_lipschitz`), so `lvl_le_of_mem_ball` forbids a ball of
radius `k` from containing a plaquette of level above `k`.

The index is the circle distance, not the raw lag: `lag_last_mem_ball_two` and
`raw_lag_radius_refuted` exhibit a lag at which the raw index would make the statement false. The
step constant is attained (`touch_advances_one`). The radius is short by at most one, the level
argument permitting only `k < circDist lag` while both endpoint plaquettes span `(μ, ν)` and so name
links at a single `τ` coordinate; `lag_last_mem_ball_two` bounds that slack, the true touch-distance
there being `2` against a circle distance of `1`.

DERIVED: the `0` is the origin site, the base point the lag is measured from and the one at which
`axisLvl τ` vanishes. -/
theorem siteAtHyper_not_mem_ball (μ ν τ : Fin dim) (lag : Fin n) (k : ℕ)
    (hk : k < circDist lag) :
    (((μ, ν), MassGap.WilsonBridge.siteAtHyper τ lag) : Plaq dim n)
      ∉ ball (bd (d := dim) (n := n)) ((μ, ν), fun _ => 0) k := by
  intro hmem
  have hlvl := lvl_le_of_mem_ball (bd (d := dim) (n := n)) ((μ, ν), fun _ => 0)
    (axisLvl τ) (by simpa [axisLvl] using circDist_zero (n := n))
    (fun p q ht => axisLvl_lipschitz τ p q ht) k _ hmem
  have hval : axisLvl τ (((μ, ν), MassGap.WilsonBridge.siteAtHyper τ lag) : Plaq dim n)
      = circDist lag := by
    simp [axisLvl, MassGap.WilsonBridge.siteAtHyper]
  omega

#print axioms siteAtHyper_not_mem_ball

/-! ### Controls on the bridge -/

/-- **`Touch bd ((μ, τ), x) ((μ, ν), shift τ x)`**: a plaquette in a plane containing `τ` shares its
`μ`-link at `shift τ x` with the plaquette one lattice step along `τ`. So one touch moves one step
along the axis, and `axisLvl_lipschitz`'s constant is attained.

DERIVED: no numeral. -/
theorem touch_advances_one (μ ν τ : Fin dim) (x : Site dim n) :
    Touch (bd (d := dim) (n := n)) ((μ, τ), x) ((μ, ν), shift τ x) :=
  ⟨(μ, shift τ x), by simp [linkSupp, bd], by simp [linkSupp, bd]⟩

#print axioms touch_advances_one

/-- **At the origin, `touch_advances_one`'s touch raises `axisLvl τ` from `0` to `1`**, given
`2 ≤ n`. The level function is not constant along the chain the bound is about.

DERIVED: the `2` is the hypothesis `2 ≤ n`, without which `0 + 1` wraps back to `0` on `Fin n`. The
`0`s are the origin site and the level there; the `1` is the level after one step. -/
theorem axisLvl_origin_step (μ ν τ : Fin dim) (hn : 2 ≤ n) :
    axisLvl τ (((μ, τ), fun _ => 0) : Plaq dim n) = 0 ∧
      axisLvl τ (((μ, ν), shift τ (fun _ => 0)) : Plaq dim n) = 1 := by
  constructor
  · simpa [axisLvl] using circDist_zero (n := n)
  · have h0 : ((0 : Fin n) : ℕ) = 0 := by simp
    have hs : shift τ (fun _ => (0 : Fin n)) τ = (0 : Fin n) + 1 := by
      simp [shift]
    rcases val_add_one_cases (0 : Fin n) with h | ⟨_, hn'⟩
    · rw [h0] at h
      show circDist (shift τ (fun _ => (0 : Fin n)) τ) = 1
      rw [hs]
      unfold circDist
      omega
    · rw [h0] at hn'; omega

#print axioms axisLvl_origin_step

end LagBallHypercubic

section LagBallWrap

open MassGap.WilsonHypercubic

variable {dim N : ℕ}

/-- **The plaquette at raw lag `N` on `N + 1` sites is within two touch-steps of the origin**, at
every `N`. The intermediate plaquette `((μ, τ), y)`, with `y` the lag-`N` site, shares its `μ`-link
at the origin with the origin plaquette and its `μ`-link at `y` with the lag-`N` one.

So a bridge indexed by the raw lag would be false, which is why `siteAtHyper_not_mem_ball` is indexed
by `circDist`. `raw_lag_radius_refuted` states that refutation.

DERIVED: the `2` is the ball radius the two touches reach; the `1` in `N + 1` is the extent, one more
than the largest raw lag; the `0` is the origin site. -/
theorem lag_last_mem_ball_two (μ ν τ : Fin dim) :
    (((μ, ν), MassGap.WilsonBridge.siteAtHyper τ (Fin.last N)) : Plaq dim (N + 1))
      ∈ ball (bd (d := dim) (n := N + 1)) ((μ, ν), fun _ => 0) 2 := by
  classical
  set y : Site dim (N + 1) := MassGap.WilsonBridge.siteAtHyper τ (Fin.last N) with hy
  have hshift : shift τ y = (fun _ => 0 : Site dim (N + 1)) := by
    funext j
    by_cases h : j = τ
    · subst h
      simp [hy, shift, MassGap.WilsonBridge.siteAtHyper, Fin.last_add_one]
    · simp [hy, shift, MassGap.WilsonBridge.siteAtHyper, h]
  -- p₀ touches the transverse plaquette at `y`, through the link `(μ, origin)`
  have h1 : Touch (bd (d := dim) (n := N + 1)) ((μ, ν), fun _ => 0) ((μ, τ), y) := by
    refine ⟨(μ, fun _ => 0), by simp [linkSupp, bd], ?_⟩
    have : (μ, shift τ y) ∈ linkSupp (bd (d := dim) (n := N + 1)) ((μ, τ), y) := by
      simp [linkSupp, bd]
    rwa [hshift] at this
  -- and that plaquette touches the lag-`N` one, through the link `(μ, y)`
  have h2 : Touch (bd (d := dim) (n := N + 1)) ((μ, τ), y) ((μ, ν), y) :=
    ⟨(μ, y), by simp [linkSupp, bd], by simp [linkSupp, bd]⟩
  exact mem_ball_succ_of_touch _ _ 1
    (mem_ball_succ_of_touch _ _ 0 (self_mem_ball _ _ 0) h1) h2

#print axioms lag_last_mem_ball_two

/-- **`Moment.circLag (Fin.last (N + 1)) = 1`.** The circle distance at the largest raw lag is one,
whatever `N`, against a raw lag that grows without bound. This is the quantity
`siteAtHyper_not_mem_ball` is indexed by.

DERIVED: the `1` in `N + 1` makes `Fin.last` the top of `Fin (N + 2)`; the `1` on the right is the
circle distance `min (N + 1) ((N + 2) - (N + 1))`. -/
theorem circLag_last (N : ℕ) : Moment.circLag (Fin.last (N + 1)) = 1 := by
  unfold Moment.circLag
  simp [Fin.val_last]

#print axioms circLag_last

/-- **On `N + 4` sites the plaquette at raw lag `N + 3` lies inside the ball of radius `N + 2`.**
That is the radius a bridge indexed by the raw lag would have placed it outside of;
`lag_last_mem_ball_two` puts it two touch-steps from the origin and `ball_mono` widens to `N + 2`.

Its circle distance is `1` (`circLag_last`), so `siteAtHyper_not_mem_ball` claims only
`∉ ball p₀ 0` there, and the two statements agree.

DERIVED: the `3` and the `4` are the smallest extent at which the raw-lag radius `N + 2` exceeds the
touch-distance `2`; the `2` is that touch-distance, from `lag_last_mem_ball_two`; the `0` is the
origin site. -/
theorem raw_lag_radius_refuted (dim N : ℕ) (μ ν τ : Fin dim) :
    (((μ, ν), MassGap.WilsonBridge.siteAtHyper τ (Fin.last (N + 3))) : Plaq dim (N + 4))
      ∈ ball (bd (d := dim) (n := N + 4)) ((μ, ν), fun _ => 0) (N + 2) :=
  ball_mono _ _ (by omega) (lag_last_mem_ball_two (N := N + 3) μ ν τ)

#print axioms raw_lag_radius_refuted

end LagBallWrap

section LagDecay

open MassGap.WilsonHypercubic

/-- **`|corrClay (N + 1) β d| ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ k`** for every
`k < Moment.circLag d`, given `0 ≤ β` and `coreRate (16 * 4) β < 1`.

`WilsonBridge.corrClay` is the four-dimensional `SU(3)` connected plaquette correlation at lag `d`.
This is `wilsonCorrConn_abs_le_coreConst_mul_rate_pow_hypercubic` composed with
`siteAtHyper_not_mem_ball`, which converts the touch-ball index into the lag. The extent `N + 1`
appears in neither the constant nor the rate.

DERIVED: the `0` is the sign hypothesis on `β` and the `1` bounds the rate at the geometric
threshold. The `16 * 4` is `touchDeg_bd_le` at `dim = 4`, the dimension `corrClay` fixes. The `1`s
in `Fin (N + 1)` and `corrClay (N + 1)` are the lattice extent, one more than the largest lag. -/
theorem corrClay_abs_le_coreConst_mul_rate_pow (N : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (hr : coreRate (16 * 4) β < 1) (d : Fin (N + 1)) (k : ℕ) (hk : k < Moment.circLag d) :
    |MassGap.WilsonBridge.corrClay (N + 1) β d|
      ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ k := by
  have hball : (((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d) : Plaq 4 (N + 1))
      ∉ ball (bd (d := 4) (n := N + 1)) ((0, 1), fun _ => 0) k :=
    siteAtHyper_not_mem_ball 0 1 2 d k hk
  exact wilsonCorrConn_abs_le_coreConst_mul_rate_pow_hypercubic (Nc := 3) (dim := 4) (n := N + 1)
    (by norm_num) ((0, 1), fun _ => 0) ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d) hβ hr k hball

#print axioms corrClay_abs_le_coreConst_mul_rate_pow

/-- **A read whose `ρ` is `corrClay` has weights decaying in `Moment.circLag`.** For `R : Moment.Read
N` with `R.ρ d = corrClay (N + 1) β d` at every lag, `0 < m ≤ ∑ d', R.ρ d'`, `0 < β` and
`coreRate (16 * 4) β < 1`,

    R.p d ≤ (coreConst (16 * 4) β / (coreRate (16 * 4) β * m) + 1)
              * coreRate (16 * 4) β ^ Moment.circLag d.

`corrClay_abs_le_coreConst_mul_rate_pow` at exponent `circLag d - 1`, divided by the total mass. The
`circLag d = 0` case is separate: there the estimate says nothing and the read's own normalisation
`∑ p = 1` gives `R.p d ≤ 1`.

`read_decay_of_correlation_decay` above is the same normalisation step in the raw lag; the two are
not interchangeable, since at `r < 1` the smaller exponent is the weaker bound.

Scope, all of it visible in the statement:

* `m` is a hypothesis and is bound outside nothing — it may depend on `N`. `Moment.Read.p` is
  `ρ/∑ρ`, so the constant carries `1/m` for a lower bound `m ≤ ∑ρ`. A bound giving `0 < ∑ρ` at each
  `N` separately does not supply one `m` good for every `N`.
* `C` and `r` both depend on `β`. `coreRate (16 * 4) β < 1` holds only near `β = 0`
  (`core_rate_lt_one_of_small_hypercubic`) and the rate grows without bound as `β` does, so the
  statement is at a fixed `N` and a fixed small `β`.
* `hρ` is carried rather than discharged: the statement is about an arbitrary `Moment.Read N` whose
  `ρ` agrees with `corrClay`, and this file names no particular such read.

DERIVED: the `0`s are the strict positivity of `m` and of `β`; the `1` bounding `coreRate` is the
geometric threshold; the `1`s in `Fin (N + 1)` and `corrClay (N + 1)` are the lattice extent. The
`16 * 4` is `touchDeg_bd_le` at `dim = 4`. The `+ 1` in the constant covers the lag-zero term, where
the estimate is silent and `∑ p = 1` gives `p 0 ≤ 1` instead. The division by `coreRate` is the one
step of exponent the ball bound loses, being indexed by `circLag d - 1` with `r^{L−1} = r^L/r`; it is
why `0 < β` is needed, `coreRate` vanishing at `β = 0`. -/
theorem read_p_le_of_corrClay {N : ℕ} (R : Moment.Read N) {β m : ℝ}
    (hρ : ∀ d : Fin (N + 1), R.ρ d = MassGap.WilsonBridge.corrClay (N + 1) β d)
    (hm : 0 < m) (hmass : m ≤ ∑ d', R.ρ d')
    (hβ : 0 < β) (hr : coreRate (16 * 4) β < 1) (d : Fin (N + 1)) :
    R.p d ≤ (coreConst (16 * 4) β / (coreRate (16 * 4) β * m) + 1)
      * coreRate (16 * 4) β ^ (Moment.circLag d) := by
  have hq : (0 : ℝ) < Real.exp (2 * β) - 1 := by
    have h : Real.exp 0 < Real.exp (2 * β) := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at h; linarith
  have hrpos : (0 : ℝ) < coreRate (16 * 4) β := by
    unfold coreRate
    exact mul_pos (mul_pos (by positivity) hq) (Real.exp_pos _)
  have hP := le_corePrefactor (16 * 4) (β := β) hβ.le
  have hCpos : (0 : ℝ) < coreConst (16 * 4) β := by
    unfold coreConst
    exact div_pos (by linarith) (by linarith)
  have hpownn : (0 : ℝ) ≤ coreRate (16 * 4) β ^ (Moment.circLag d) := pow_nonneg hrpos.le _
  have hfrac : (0 : ℝ) ≤ coreConst (16 * 4) β / (coreRate (16 * 4) β * m) :=
    (div_pos hCpos (mul_pos hrpos hm)).le
  have hsum : (0 : ℝ) < ∑ d', R.ρ d' := lt_of_lt_of_le hm hmass
  rcases Nat.eq_zero_or_pos (Moment.circLag d) with h0 | hpos
  · rw [h0, pow_zero, mul_one]
    have h1 : R.p d ≤ 1 := by
      rw [← R.p_sum]
      exact Finset.single_le_sum (fun i _ => R.p_nonneg i) (Finset.mem_univ d)
    linarith
  · have hk : Moment.circLag d - 1 < Moment.circLag d := by omega
    have hbound := corrClay_abs_le_coreConst_mul_rate_pow N hβ.le hr d (Moment.circLag d - 1) hk
    have hrho : R.ρ d
        ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ (Moment.circLag d - 1) := by
      rw [hρ d]
      exact le_trans (le_abs_self _) hbound
    have hL : Moment.circLag d - 1 + 1 = Moment.circLag d := by omega
    have hsplit : coreRate (16 * 4) β ^ (Moment.circLag d - 1) * coreRate (16 * 4) β
        = coreRate (16 * 4) β ^ (Moment.circLag d) := by
      rw [← pow_succ, hL]
    have hrm : coreRate (16 * 4) β * m ≠ 0 := ne_of_gt (mul_pos hrpos hm)
    have hdiv : coreConst (16 * 4) β / (coreRate (16 * 4) β * m) * (coreRate (16 * 4) β * m)
        = coreConst (16 * 4) β := by field_simp
    have hA : coreConst (16 * 4) β / (coreRate (16 * 4) β * m)
          * coreRate (16 * 4) β ^ (Moment.circLag d) * m
        = coreConst (16 * 4) β * coreRate (16 * 4) β ^ (Moment.circLag d - 1) := by
      rw [← hsplit]
      calc coreConst (16 * 4) β / (coreRate (16 * 4) β * m)
            * (coreRate (16 * 4) β ^ (Moment.circLag d - 1) * coreRate (16 * 4) β) * m
          = coreConst (16 * 4) β / (coreRate (16 * 4) β * m) * (coreRate (16 * 4) β * m)
            * coreRate (16 * 4) β ^ (Moment.circLag d - 1) := by ring
        _ = coreConst (16 * 4) β * coreRate (16 * 4) β ^ (Moment.circLag d - 1) := by rw [hdiv]
    have hXnn : (0 : ℝ) ≤ coreConst (16 * 4) β / (coreRate (16 * 4) β * m) + 1 := by linarith
    have hprodnn : (0 : ℝ) ≤ (coreConst (16 * 4) β / (coreRate (16 * 4) β * m) + 1)
        * coreRate (16 * 4) β ^ (Moment.circLag d) := mul_nonneg hXnn hpownn
    have hpd : R.p d = R.ρ d / ∑ d', R.ρ d' := rfl
    rw [hpd, div_le_iff₀ hsum]
    calc R.ρ d
        ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ (Moment.circLag d - 1) := hrho
      _ = coreConst (16 * 4) β / (coreRate (16 * 4) β * m)
            * coreRate (16 * 4) β ^ (Moment.circLag d) * m := hA.symm
      _ ≤ (coreConst (16 * 4) β / (coreRate (16 * 4) β * m) + 1)
            * coreRate (16 * 4) β ^ (Moment.circLag d) * m := by
          have : (0 : ℝ) ≤ coreRate (16 * 4) β ^ (Moment.circLag d) * m := mul_nonneg hpownn hm.le
          nlinarith
      _ ≤ (coreConst (16 * 4) β / (coreRate (16 * 4) β * m) + 1)
            * coreRate (16 * 4) β ^ (Moment.circLag d) * (∑ d', R.ρ d') :=
          mul_le_mul_of_nonneg_left hmass hprodnn

#print axioms read_p_le_of_corrClay

/-- **`0 ≤ coreRate (16 * 4) β` for `0 ≤ β`.** `coreRate_nonneg` at `K = 16 * 4`. The companion
upper bound `coreRate (16 * 4) β < 1` is `core_rate_lt_one_of_small_hypercubic` at `dim = 4`, and
holds only near `β = 0`.

DERIVED: the `0`s are the sign hypothesis on `β` and the lower bound on the rate; the `16 * 4` is
`touchDeg_bd_le` at `dim = 4`. -/
theorem read_decay_rate_nonneg {β : ℝ} (hβ : 0 ≤ β) : (0 : ℝ) ≤ coreRate (16 * 4) β :=
  coreRate_nonneg _ hβ

#print axioms read_decay_rate_nonneg

end LagDecay

end MassGap.StrongCoupling

-- ==== END lag-to-ball bridge ====
