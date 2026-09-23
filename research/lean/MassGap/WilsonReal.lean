import MassGap.WilsonLattice
import MassGap.WilsonAction
import MassGap.SUN

/-!
# MassGap.WilsonReal — concrete `SU 2` Wilson systems and the general `SU N` Gibbs state

Three concrete systems and a body of general results about `WilsonLattice.wilsonSystem`.

## The concrete systems

* `sysReal` — two plaquettes over eight links, boundary words `U₀U₁U₂⁻¹U₃⁻¹` on links `0,1,2,3` and
  on `4,5,6,7`, with `wilsonDensity` as the action density. `σL2` relabels links by `i ↦ i + 4` and
  `σP2` swaps the two plaquettes; `hbd2` checks compatibility by `decide`, `symReal` bundles them,
  and `sysReal_invariant` is invariance of the Gibbs expectation under the swap.
* `sysRing` — three plaquettes over twelve links with the cyclic translation `σL3 : i ↦ i + 4`,
  `σP3 : p ↦ p + 1`; `hbd3` and `sysRing_invariant` are the corresponding statements.
* `sysInt` — two plaquettes over seven links sharing link `3`. `sysInt_partition_pos` and
  `sysInt_gauge_invariant` hold by the general lemmas; `sysInt_shares_link` and
  `blockInt_not_disjoint` record that its two link blocks overlap.

## The Gibbs state

For `sysReal` and then for an arbitrary `SU N` Wilson system on a finite lattice: the action is
nonnegative and bounded by `2 * Fintype.card Pq`, measurable, the Boltzmann weight is positive and
bounded by `exp (|β| * 2 * Fintype.card Pq)`, and the partition function is positive
(`wilsonSystem_partition_pos`). From that, `⟨1⟩ = 1`, `⟨O⟩ ≥ 0` for `O ≥ 0`, homogeneity,
additivity and monotonicity under integrability hypotheses, `|⟨O⟩| ≤ M` for `|O| ≤ M`, and
`⟨O⟩ = ∫ O dHaar` at `β = 0`. `wilsonSystem_mul_boltz_integrable` discharges the integrability
hypotheses for bounded measurable observables.

Gauge invariance: `wilsonAction_gauge_invariant` at one plaquette, then
`wilsonSystem_action_gauge`, `wilsonSystem_boltz_gauge` and `wilsonSystem_gauge_invariant` for the
expectation, the last through `confConjEquiv_measurePreserving`.

## Factorisation for `sysReal`

`coords_indep_SU` proves the coordinate tuples on two disjoint link blocks independent under the
product Haar measure, and `block_integral_factor` turns that into a factorising integral.
`plaqObs0_factor` and `plaqObs1_factor` show each plaquette observable reads only its own block, so
`plaqObs_indep` holds, and `expect_plaqObs_factor_at_zero` gives `⟨φ₀ φ₁⟩ = ⟨φ₀⟩⟨φ₁⟩` at `β = 0`.
`sysReal_boltz_factor` and `sysReal_partition_factor` extend the splitting to every coupling, and
`expect_plaqObs_factor` gives the same identity at every `β`.

## Scope

`sysReal` and `sysRing` have plaquettes with disjoint link sets, so their two-point function
factorises exactly at every coupling and carries no separation dependence. `sysInt`'s blocks
overlap, so the independence argument behind `plaqObs_indep` does not apply to it; nothing here
proves anything about correlations in `sysInt`.
-/

namespace MassGap.WilsonReal

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge MeasureTheory
  ProbabilityTheory

/-- `SU 2`, the two-by-two special unitary group, as the gauge group of the concrete systems below.

DERIVED: `2` is the matrix size. -/
abbrev G2 : Type := MassGap.SUN.SU 2

/-- Boundary words for two plaquettes over eight links: plaquette `0` traverses links `0, 1` forward
and `2, 3` backward, plaquette `1` the same pattern on `4, 5, 6, 7`. The two link sets are disjoint.

DERIVED: `2` is the plaquette count and `8` the link count, four per plaquette; `0` selects the first
plaquette, and `0, 1, 2, 3` and `4, 5, 6, 7` are the two blocks' link indices, listed in traversal
order. -/
def bd2 (p : Fin 2) : List (Fin 8 × Bool) :=
  if p = 0 then [(0, true), (1, true), (2, false), (3, false)]
  else [(4, true), (5, true), (6, false), (7, false)]

/-- The link relabelling `i ↦ i + 4` on `Fin 8`, which exchanges the two plaquettes' link blocks.

DERIVED: `8` is the link count and `4` the block size, so adding `4` modulo `8` swaps the two
blocks. -/
def σL2 : Equiv.Perm (Fin 8) := Equiv.addLeft (4 : Fin 8)

/-- The transposition of the two plaquettes, `Equiv.swap 0 1` on `Fin 2`.

DERIVED: `2` is the plaquette count; `0` and `1` are the two plaquettes being exchanged. -/
def σP2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- `bd2 (σP2 p) = (bd2 p).map (fun lo => (σL2 lo.1, lo.2))`: the boundary words transform
compatibly under the swap. By `decide` over the finitely many cases.

DERIVED: no numeral occurs in the statement; the indices are inside `bd2`, `σL2` and `σP2`. -/
theorem hbd2 : ∀ p, bd2 (σP2 p) = (bd2 p).map (fun lo => (σL2 lo.1, lo.2)) := by decide

/-- The two-plaquette `SU 2` Wilson system: `wilsonSystem bd2 wilsonDensity`, with the ordered-loop
holonomy and the real Wilson action density.

DERIVED: no numeral occurs. -/
noncomputable def sysReal : System G2 := wilsonSystem bd2 wilsonDensity

/-- The plaquette-swap symmetry of `sysReal`, assembled from `σL2`, `σP2` and `hbd2`.

DERIVED: no numeral occurs. -/
noncomputable def symReal : Symmetry sysReal := wilsonSymmetry bd2 wilsonDensity σL2 σP2 hbd2

/-- `sysReal.expect μ β (O ∘ Symmetry.reindex symReal.onLink) = sysReal.expect μ β O` at any
probability measure `μ` on the group, any coupling and any observable. `wilson_expect_invariant` at
`bd2`, `σL2`, `σP2` and `hbd2`.

DERIVED: no numeral occurs. -/
theorem sysReal_invariant (μ : Measure G2) [IsProbabilityMeasure μ] (β : ℝ)
    (O : sysReal.Config → ℝ) :
    sysReal.expect μ β (fun U => O (Symmetry.reindex symReal.onLink U)) = sysReal.expect μ β O :=
  wilson_expect_invariant bd2 wilsonDensity σL2 σP2 hbd2 μ β O

/-- `wilsonDensity (wilsonHol bd p (fun l => g * U l * g⁻¹)) = wilsonDensity (wilsonHol bd p U)` at
any `N`, boundary word and plaquette. `wilsonHol_conj` conjugates the holonomy and
`wilsonDensity_conj` is invariant under that.

DERIVED: no numeral occurs; `N` is the matrix size. -/
theorem wilsonAction_gauge_invariant {N : ℕ} {Lk Pq : Type}
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (p : Pq)
    (U : Lk → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol bd p (fun l => g * U l * g⁻¹))
      = wilsonDensity (wilsonHol bd p U) := by
  rw [wilsonHol_conj]
  exact wilsonDensity_conj g (wilsonHol bd p U)

/-- `sysReal.action (confConj G2 g U) = sysReal.action U`, by `Finset.sum_congr` over the plaquettes
from `wilsonAction_gauge_invariant`.

DERIVED: no numeral occurs. -/
theorem sysReal_action_gauge (g : G2) (U : sysReal.Config) :
    sysReal.action (confConj G2 g U) = sysReal.action U :=
  Finset.sum_congr rfl (fun p _ => wilsonAction_gauge_invariant bd2 g p U)

/-- `sysReal.boltz β (confConj G2 g U) = sysReal.boltz β U`, by rewriting with
`sysReal_action_gauge` inside the exponential.

DERIVED: no numeral occurs. -/
theorem sysReal_boltz_gauge (g : G2) (β : ℝ) (U : sysReal.Config) :
    sysReal.boltz β (confConj G2 g U) = sysReal.boltz β U := by
  unfold System.boltz; rw [sysReal_action_gauge]

/-- `sysReal.expect (probHaar G2) β (O ∘ confConj G2 g) = sysReal.expect (probHaar G2) β O`.
`System.expect_invariant_of_mp` with `confConjEquiv_measurePreserving` for the measure and
`sysReal_boltz_gauge` for the weight.

DERIVED: no numeral occurs. -/
theorem sysReal_gauge_invariant (g : G2) (β : ℝ) (O : sysReal.Config → ℝ) :
    sysReal.expect (probHaar G2) β (fun U => O (confConj G2 g U))
      = sysReal.expect (probHaar G2) β O :=
  System.expect_invariant_of_mp sysReal (probHaar G2) β O (confConjEquiv G2 g)
    (confConjEquiv_measurePreserving G2 g) (fun U => sysReal_boltz_gauge g β U)

/-! ### Gauge invariance for an arbitrary `SU N` Wilson system -/

/-- `(wilsonSystem bd wilsonDensity).action (confConj _ g U) = … action U` at any `N` and any finite
lattice, by `Finset.sum_congr` from `wilsonAction_gauge_invariant`.

DERIVED: no numeral occurs. -/
theorem wilsonSystem_action_gauge {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N)
    (U : (wilsonSystem bd wilsonDensity).Config) :
    (wilsonSystem bd wilsonDensity).action (confConj (MassGap.SUN.SU N) g U)
      = (wilsonSystem bd wilsonDensity).action U :=
  Finset.sum_congr rfl (fun p _ => wilsonAction_gauge_invariant bd g p U)

/-- The Boltzmann weight of any `SU N` Wilson system is unchanged by a global conjugation, by
rewriting with `wilsonSystem_action_gauge`.

DERIVED: no numeral occurs. -/
theorem wilsonSystem_boltz_gauge {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (β : ℝ)
    (U : (wilsonSystem bd wilsonDensity).Config) :
    (wilsonSystem bd wilsonDensity).boltz β (confConj (MassGap.SUN.SU N) g U)
      = (wilsonSystem bd wilsonDensity).boltz β U := by
  unfold System.boltz; rw [wilsonSystem_action_gauge]

/-- `⟨O ∘ (U ↦ g U g⁻¹)⟩ = ⟨O⟩` for any `SU N` Wilson system on a finite lattice, by
`System.expect_invariant_of_mp` as in `sysReal_gauge_invariant`, of which this is the general form.

DERIVED: no numeral occurs. -/
theorem wilsonSystem_gauge_invariant {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (β : ℝ)
    (O : (wilsonSystem bd wilsonDensity).Config → ℝ) :
    (wilsonSystem bd wilsonDensity).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O (confConj (MassGap.SUN.SU N) g U))
      = (wilsonSystem bd wilsonDensity).expect (probHaar (MassGap.SUN.SU N)) β O :=
  System.expect_invariant_of_mp (wilsonSystem bd wilsonDensity) (probHaar (MassGap.SUN.SU N)) β O
    (confConjEquiv (MassGap.SUN.SU N) g) (confConjEquiv_measurePreserving (MassGap.SUN.SU N) g)
    (fun U => wilsonSystem_boltz_gauge bd g β U)

/-! ### A three-plaquette ring, with a cyclic translation symmetry -/

/-- Boundary words for three plaquettes over twelve links, four per plaquette, on the blocks
`0, 1, 2, 3`, `4, 5, 6, 7` and `8, 9, 10, 11`. The three link sets are disjoint.

DERIVED: `3` is the plaquette count and `12` the link count, four per plaquette; `0` and `1` select
the first two plaquettes, and the index lists are the three blocks in traversal order. -/
def bd3 (p : Fin 3) : List (Fin 12 × Bool) :=
  if p = 0 then [(0, true), (1, true), (2, false), (3, false)]
  else if p = 1 then [(4, true), (5, true), (6, false), (7, false)]
  else [(8, true), (9, true), (10, false), (11, false)]

/-- The link translation `i ↦ i + 4` on `Fin 12`, carrying each plaquette's block to the next.

DERIVED: `12` is the link count and `4` the block size, so adding `4` modulo `12` advances one
plaquette. -/
def σL3 : Equiv.Perm (Fin 12) := Equiv.addLeft (4 : Fin 12)

/-- The cyclic translation `p ↦ p + 1` on `Fin 3`, the plaquette-index counterpart of `σL3`.

DERIVED: `3` is the plaquette count and `1` the step of the cycle. -/
def σP3 : Equiv.Perm (Fin 3) := Equiv.addLeft (1 : Fin 3)

/-- `bd3 (σP3 p) = (bd3 p).map (fun lo => (σL3 lo.1, lo.2))`, by `decide`.

DERIVED: no numeral occurs in the statement. -/
theorem hbd3 : ∀ p, bd3 (σP3 p) = (bd3 p).map (fun lo => (σL3 lo.1, lo.2)) := by decide

/-- The three-plaquette ring `SU 2` Wilson system, `wilsonSystem bd3 wilsonDensity`.

DERIVED: no numeral occurs. -/
noncomputable def sysRing : System G2 := wilsonSystem bd3 wilsonDensity

/-- The cyclic translation symmetry of `sysRing`, assembled from `σL3`, `σP3` and `hbd3`.

DERIVED: no numeral occurs. -/
noncomputable def symRing : Symmetry sysRing := wilsonSymmetry bd3 wilsonDensity σL3 σP3 hbd3

/-- `sysRing.expect μ β (O ∘ Symmetry.reindex symRing.onLink) = sysRing.expect μ β O` at any
probability measure on the group. `wilson_expect_invariant` at `bd3`, `σL3`, `σP3` and `hbd3`. The
symmetry is a cyclic translation of the three plaquettes rather than a transposition.

DERIVED: no numeral occurs. -/
theorem sysRing_invariant (μ : Measure G2) [IsProbabilityMeasure μ] (β : ℝ)
    (O : sysRing.Config → ℝ) :
    sysRing.expect μ β (fun U => O (Symmetry.reindex symRing.onLink U)) = sysRing.expect μ β O :=
  wilson_expect_invariant bd3 wilsonDensity σL3 σP3 hbd3 μ β O

/-- `Measurable (wilsonHol bd2 p)` at each plaquette, from `measurable_wilsonHol`, which uses the
`MeasurableMul₂` and `MeasurableInv` instances on `SU N`.

DERIVED: `2` is the plaquette count in `Fin 2`. -/
theorem measurable_bd2_hol (p : Fin 2) : Measurable (wilsonHol (G := G2) bd2 p) :=
  measurable_wilsonHol bd2 p

/-- `Measurable sysReal.action`, a finite sum of `wilsonDensity` composed with the holonomies.

DERIVED: no numeral occurs. -/
theorem measurable_sysReal_action : Measurable sysReal.action :=
  Finset.measurable_sum _ (fun p _ => measurable_wilsonDensity.comp (measurable_bd2_hol p))

/-- `Measurable (sysReal.boltz β)`, as `Real.exp` composed with a measurable function.

DERIVED: no numeral occurs. -/
theorem measurable_sysReal_boltz (β : ℝ) : Measurable (sysReal.boltz β) :=
  Real.measurable_exp.comp (measurable_const.mul measurable_sysReal_action)

/-- `0 ≤ sysReal.action U`, a finite sum of terms each nonnegative by `wilsonDensity_nonneg`.

DERIVED: `0` is the lower bound asserted. -/
theorem sysReal_action_nonneg (U : sysReal.Config) : 0 ≤ sysReal.action U :=
  Finset.sum_nonneg (fun p _ => wilsonDensity_nonneg (by norm_num) _)

/-- `sysReal.action U ≤ 4`, from `wilsonDensity_le_two` at each of the two plaquettes.

DERIVED: `4` is `2 * 2`, the plaquette count times `wilsonDensity`'s own upper bound. -/
theorem sysReal_action_le (U : sysReal.Config) : sysReal.action U ≤ 4 := by
  have h : sysReal.action U ≤ ∑ _p : Fin 2, (2 : ℝ) :=
    Finset.sum_le_sum (fun p _ => wilsonDensity_le_two (by norm_num) _)
  have he : (∑ _p : Fin 2, (2 : ℝ)) = 4 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  linarith

/-- `0 < sysReal.boltz β U`, since the weight is an exponential.

DERIVED: `0` is the strict lower bound asserted. -/
theorem sysReal_boltz_pos (β : ℝ) (U : sysReal.Config) : 0 < sysReal.boltz β U := by
  unfold System.boltz; exact Real.exp_pos _

/-- `0 < sysReal.partition (probHaar G2) β`. The weight is measurable, bounded by
`exp (4 * |β|)` because the action lies in `[0, 4]`, hence integrable against the probability Haar
measure, and strictly positive everywhere, so its integral is positive. This is what makes the Gibbs
quotient `(∫ O e^{-βS}) / Z` well defined.

DERIVED: `0` is the strict lower bound asserted; the `4` of the proof's bound is
`sysReal_action_le`'s. -/
theorem sysReal_partition_pos (β : ℝ) : 0 < sysReal.partition (probHaar G2) β := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  unfold System.partition
  have hbound : ∀ U, ‖sysReal.boltz β U‖ ≤ Real.exp (4 * |β|) := by
    intro U
    rw [Real.norm_of_nonneg (sysReal_boltz_pos β U).le]
    unfold System.boltz
    rw [Real.exp_le_exp]
    have h1 : -β * sysReal.action U ≤ |β| * sysReal.action U :=
      mul_le_mul_of_nonneg_right (neg_le_abs β) (sysReal_action_nonneg U)
    have h2 : |β| * sysReal.action U ≤ |β| * 4 :=
      mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg β)
    linarith
  have hint : Integrable (sysReal.boltz β) (sysReal.vol (probHaar G2)) :=
    (integrable_const (Real.exp (4 * |β|))).mono'
      (measurable_sysReal_boltz β).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [integral_pos_iff_support_of_nonneg (fun U => (sysReal_boltz_pos β U).le) hint]
  have hsupp : Function.support (sysReal.boltz β) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (sysReal_boltz_pos β U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

/-- `sysReal.expect (probHaar G2) β 1 = 1`: the numerator is the partition function, which
`sysReal_partition_pos` makes nonzero, so the quotient is one.

DERIVED: `1` is the constant observable and the value of its expectation. -/
theorem sysReal_expect_one (β : ℝ) : sysReal.expect (probHaar G2) β (fun _ => (1 : ℝ)) = 1 := by
  unfold System.expect System.corrNum
  simp only [one_mul]
  rw [show (∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2)))
      = sysReal.partition (probHaar G2) β from rfl]
  exact div_self (sysReal_partition_pos β).ne'

/-- `0 ≤ sysReal.expect (probHaar G2) β O` whenever `0 ≤ O U` everywhere: the integrand is a product
of nonnegative factors and the denominator is positive.

DERIVED: `0` is the lower bound on the observable and on the expectation. -/
theorem sysReal_expect_nonneg (β : ℝ) (O : sysReal.Config → ℝ) (hO : ∀ U, 0 ≤ O U) :
    0 ≤ sysReal.expect (probHaar G2) β O := by
  unfold System.expect
  refine div_nonneg ?_ (sysReal_partition_pos β).le
  unfold System.corrNum
  exact integral_nonneg (fun U => mul_nonneg (hO U) (sysReal_boltz_pos β U).le)

/-- `sysReal.expect (probHaar G2) β O ≤ sysReal.expect (probHaar G2) β O'` for `O ≤ O'`, given that
both weighted integrands are integrable. The denominator is positive and the weight is nonnegative.

Scope: the two integrability hypotheses are explicit. `sysReal_mul_boltz_integrable` discharges them
for bounded measurable observables.

DERIVED: no numeral occurs in the statement. -/
theorem sysReal_expect_mono (β : ℝ) (O O' : sysReal.Config → ℝ)
    (hint : Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)))
    (hint' : Integrable (fun U => O' U * sysReal.boltz β U) (sysReal.vol (probHaar G2)))
    (hO : ∀ U, O U ≤ O' U) :
    sysReal.expect (probHaar G2) β O ≤ sysReal.expect (probHaar G2) β O' := by
  unfold System.expect
  refine (div_le_div_iff_of_pos_right (sysReal_partition_pos β)).mpr ?_
  unfold System.corrNum
  exact integral_mono hint hint'
    (fun U => mul_le_mul_of_nonneg_right (hO U) (sysReal_boltz_pos β U).le)

/-- `sysReal.expect (probHaar G2) β (c * O) = c * sysReal.expect (probHaar G2) β O`, by
`integral_const_mul`, which needs no integrability hypothesis.

DERIVED: no numeral occurs. -/
theorem sysReal_expect_smul (β c : ℝ) (O : sysReal.Config → ℝ) :
    sysReal.expect (probHaar G2) β (fun U => c * O U)
      = c * sysReal.expect (probHaar G2) β O := by
  unfold System.expect System.corrNum
  have h : (fun U => (c * O U) * sysReal.boltz β U)
      = (fun U => c * (O U * sysReal.boltz β U)) := by funext U; ring
  rw [h, integral_const_mul, mul_div_assoc]

/-- `sysReal.expect (probHaar G2) β (O + O') = ⟨O⟩ + ⟨O'⟩`, given that both weighted integrands are
integrable. With `sysReal_expect_smul` this makes the expectation linear, and with
`sysReal_expect_one` and `sysReal_expect_nonneg` a positive normalised linear functional.

Scope: the two integrability hypotheses are explicit; `sysReal_mul_boltz_integrable` discharges them
for bounded measurable observables.

DERIVED: no numeral occurs in the statement. -/
theorem sysReal_expect_add (β : ℝ) (O O' : sysReal.Config → ℝ)
    (hint : Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)))
    (hint' : Integrable (fun U => O' U * sysReal.boltz β U) (sysReal.vol (probHaar G2))) :
    sysReal.expect (probHaar G2) β (fun U => O U + O' U)
      = sysReal.expect (probHaar G2) β O + sysReal.expect (probHaar G2) β O' := by
  unfold System.expect System.corrNum
  have h : (fun U => (O U + O' U) * sysReal.boltz β U)
      = (fun U => O U * sysReal.boltz β U + O' U * sysReal.boltz β U) := by funext U; ring
  rw [h, integral_add hint hint', add_div]

/-- `sysReal.boltz β U ≤ Real.exp (4 * |β|)`, from `sysReal_action_nonneg` and
`sysReal_action_le`. The reusable form of the bound used inside `sysReal_partition_pos`.

DERIVED: `4` is the action's upper bound from `sysReal_action_le`, which is the plaquette count times
`wilsonDensity`'s own bound. -/
theorem sysReal_boltz_le (β : ℝ) (U : sysReal.Config) :
    sysReal.boltz β U ≤ Real.exp (4 * |β|) := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : -β * sysReal.action U ≤ |β| * sysReal.action U :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) (sysReal_action_nonneg U)
  have h2 : |β| * sysReal.action U ≤ |β| * 4 :=
    mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg β)
  linarith

/-- `Integrable (fun U => O U * sysReal.boltz β U)` for measurable `O` with `|O U| ≤ M`: the
integrand is bounded by the constant `M * exp (4 * |β|)` and measurable, hence integrable against the
probability Haar measure. This discharges the integrability hypotheses of `sysReal_expect_add` and
`sysReal_expect_mono` for bounded measurable observables.

DERIVED: no numeral occurs in the statement; the `4` of the proof's bound is `sysReal_boltz_le`'s. -/
theorem sysReal_mul_boltz_integrable (β : ℝ) (O : sysReal.Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)) := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  refine (integrable_const (M * Real.exp (4 * |β|))).mono'
    ((hmeas.mul (measurable_sysReal_boltz β)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [norm_mul, Real.norm_of_nonneg (sysReal_boltz_pos β U).le]
  have hO : ‖O U‖ ≤ M := by rw [Real.norm_eq_abs]; exact hbound U
  exact mul_le_mul hO (sysReal_boltz_le β U) (sysReal_boltz_pos β U).le
    (le_trans (norm_nonneg _) hO)

/-- `|sysReal.expect (probHaar G2) β O| ≤ M` for measurable `O` with `|O U| ≤ M`:
`|∫ O e^{-βS}| ≤ ∫ |O| e^{-βS} ≤ M * Z`, divided by the positive `Z`.

DERIVED: no numeral occurs in the statement; `M` is the caller's bound. -/
theorem sysReal_expect_abs_le (β : ℝ) (O : sysReal.Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    |sysReal.expect (probHaar G2) β O| ≤ M := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  have hZ := sysReal_partition_pos β
  have hint := sysReal_mul_boltz_integrable β O hmeas M hbound
  have hb : Integrable (sysReal.boltz β) (sysReal.vol (probHaar G2)) := by
    have := sysReal_mul_boltz_integrable β (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
    simpa using this
  have hintM := hb.const_mul M
  unfold System.expect
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  unfold System.corrNum
  calc |∫ U, O U * sysReal.boltz β U ∂(sysReal.vol (probHaar G2))|
      ≤ ∫ U, |O U * sysReal.boltz β U| ∂(sysReal.vol (probHaar G2)) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ U, M * sysReal.boltz β U ∂(sysReal.vol (probHaar G2)) := by
        refine integral_mono hint.abs hintM (fun U => ?_)
        rw [abs_mul, abs_of_pos (sysReal_boltz_pos β U)]
        exact mul_le_mul_of_nonneg_right (hbound U) (sysReal_boltz_pos β U).le
    _ = M * ∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2)) := integral_const_mul M _
    _ = M * sysReal.partition (probHaar G2) β := rfl

/-- `sysReal.expect (probHaar G2) 0 O = ∫ U, O U`: at zero coupling the Boltzmann weight is the
constant one, so the partition function is one and the expectation is the bare product-Haar average.

DERIVED: `0` is the coupling at which the exponent vanishes and the weight becomes constant. -/
theorem sysReal_expect_at_zero (O : sysReal.Config → ℝ) :
    sysReal.expect (probHaar G2) 0 O = ∫ U, O U ∂(sysReal.vol (probHaar G2)) := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  have hb : ∀ U, sysReal.boltz 0 U = 1 := fun U => by unfold System.boltz; simp
  have hvol : (sysReal.vol (probHaar G2)).real Set.univ = 1 := by
    change ((sysReal.vol (probHaar G2)) Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  have hden : sysReal.partition (probHaar G2) 0 = 1 := by
    unfold System.partition
    simp only [hb, integral_const, smul_eq_mul, mul_one, hvol]
  unfold System.expect System.corrNum
  simp only [hb, mul_one]
  rw [hden, div_one]

/-! ### General `SU N` Wilson systems on a finite lattice

The `sysReal` results above, restated for an arbitrary `SU N` Wilson system on a finite lattice: the
same nonnegativity, uniform-bound, integrability and positivity chain, with `Fintype.card Pq` in
place of the concrete plaquette count. -/

/-- `0 ≤ (wilsonSystem bd wilsonDensity).action U` at any `N ≠ 0`, a finite sum of terms each
nonnegative by `wilsonDensity_nonneg`.

DERIVED: `0` is the value `N` must differ from, `wilsonDensity_nonneg`'s own hypothesis, and the
lower bound asserted. -/
theorem wilsonSystem_action_nonneg {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    0 ≤ (wilsonSystem bd (wilsonDensity (N := N))).action U :=
  Finset.sum_nonneg (fun p _ => wilsonDensity_nonneg hN _)

/-- `(wilsonSystem bd wilsonDensity).action U ≤ 2 * Fintype.card Pq` at any `N ≠ 0`, from
`wilsonDensity_le_two` at each plaquette.

DERIVED: `0` is the value `N` must differ from; `2` is `wilsonDensity`'s own upper bound, multiplied
by the plaquette count. -/
theorem wilsonSystem_action_le {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).action U ≤ 2 * (Fintype.card Pq : ℝ) := by
  have h : (wilsonSystem bd wilsonDensity).action U ≤ ∑ _p : Pq, (2 : ℝ) :=
    Finset.sum_le_sum (fun p _ => wilsonDensity_le_two hN _)
  have he : (∑ _p : Pq, (2 : ℝ)) = 2 * (Fintype.card Pq : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  linarith

/-- Measurability of the action of any `SU N` Wilson system, a finite sum of `wilsonDensity`
composed with `wilsonHol`.

DERIVED: no numeral occurs. -/
theorem measurable_wilsonSystem_action {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) :
    Measurable (wilsonSystem bd (wilsonDensity (N := N))).action :=
  Finset.measurable_sum _ (fun p _ =>
    measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU N) bd p))

/-- Measurability of the Boltzmann weight of any `SU N` Wilson system, as `Real.exp` composed with
the measurable action.

DERIVED: no numeral occurs. -/
theorem measurable_wilsonSystem_boltz {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    Measurable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) :=
  Real.measurable_exp.comp (measurable_const.mul (measurable_wilsonSystem_action bd))

/-- `0 < (wilsonSystem bd wilsonDensity).boltz β U`, since the weight is an exponential.

DERIVED: `0` is the strict lower bound asserted. -/
theorem wilsonSystem_boltz_pos {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).boltz β U := by
  unfold System.boltz; exact Real.exp_pos _

/-- `0 < (wilsonSystem bd wilsonDensity).partition (probHaar (SU N)) β` at any `N ≠ 0` and any
finite lattice. The shape of `sysReal_partition_pos`, with the uniform weight bound
`exp (|β| * 2 * Fintype.card Pq)` in place of the concrete one.

DERIVED: `0` is the value `N` must differ from and the strict lower bound asserted; the `2` of the
proof's weight bound is `wilsonSystem_action_le`'s. -/
theorem wilsonSystem_partition_pos {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) β := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  unfold System.partition
  set B : ℝ := |β| * (2 * (Fintype.card Pq : ℝ)) with hB
  have hbound : ∀ U : (wilsonSystem bd (wilsonDensity (N := N))).Config,
      ‖(wilsonSystem bd (wilsonDensity (N := N))).boltz β U‖ ≤ Real.exp B := by
    intro U
    rw [Real.norm_of_nonneg (wilsonSystem_boltz_pos bd β U).le]
    unfold System.boltz
    rw [Real.exp_le_exp]
    have h1 : -β * (wilsonSystem bd (wilsonDensity (N := N))).action U
        ≤ |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U :=
      mul_le_mul_of_nonneg_right (neg_le_abs β) (wilsonSystem_action_nonneg hN bd U)
    have h2 : |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U
        ≤ |β| * (2 * (Fintype.card Pq : ℝ)) :=
      mul_le_mul_of_nonneg_left (wilsonSystem_action_le hN bd U) (abs_nonneg β)
    rw [hB]; linarith
  have hint : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    (integrable_const (Real.exp B)).mono'
      (measurable_wilsonSystem_boltz bd β).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  rw [integral_pos_iff_support_of_nonneg
      (fun U => (wilsonSystem_boltz_pos bd β U).le) hint]
  have hsupp : Function.support ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (wilsonSystem_boltz_pos bd β U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

/-- `⟨1⟩ = 1` for any `SU N` Wilson system with `N ≠ 0`, the numerator being the partition function
and the denominator nonzero by `wilsonSystem_partition_pos`.

DERIVED: `0` is the value `N` must differ from; `1` is the constant observable and the value of its
expectation. -/
theorem wilsonSystem_expect_one {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
      (fun _ => (1 : ℝ)) = 1 := by
  unfold System.expect System.corrNum
  simp only [one_mul]
  rw [show (∫ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
      = (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (MassGap.SUN.SU N)) β from rfl]
  exact div_self (wilsonSystem_partition_pos hN bd β).ne'

/-- `0 ≤ ⟨O⟩` for `0 ≤ O` on any `SU N` Wilson system with `N ≠ 0`.

DERIVED: `0` is the value `N` must differ from, the lower bound on the observable, and the lower
bound on the expectation. -/
theorem wilsonSystem_expect_nonneg {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) (hO : ∀ U, 0 ≤ O U) :
    0 ≤ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O := by
  unfold System.expect
  refine div_nonneg ?_ (wilsonSystem_partition_pos hN bd β).le
  unfold System.corrNum
  exact integral_nonneg (fun U => mul_nonneg (hO U) (wilsonSystem_boltz_pos bd β U).le)

/-- `⟨c * O⟩ = c * ⟨O⟩` on any `SU N` Wilson system, by `integral_const_mul`, with no integrability
hypothesis and no condition on `N`.

DERIVED: no numeral occurs. -/
theorem wilsonSystem_expect_smul {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β c : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => c * O U)
      = c * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O := by
  unfold System.expect System.corrNum
  have h : (fun U => (c * O U) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      = (fun U => c * (O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)) := by
    funext U; ring
  rw [h, integral_const_mul, mul_div_assoc]

/-- `⟨O + O'⟩ = ⟨O⟩ + ⟨O'⟩` on any `SU N` Wilson system, given that both weighted integrands are
integrable; `wilsonSystem_mul_boltz_integrable` discharges that for bounded measurable observables.

DERIVED: no numeral occurs in the statement. -/
theorem wilsonSystem_expect_add {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O O' : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hint : Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
    (hint' : Integrable (fun U => O' U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O U + O' U)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
        + (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O' := by
  unfold System.expect System.corrNum
  have h : (fun U => (O U + O' U) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      = (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
          + O' U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U) := by funext U; ring
  rw [h, integral_add hint hint', add_div]

/-- `⟨O⟩ ≤ ⟨O'⟩` for `O ≤ O'` on any `SU N` Wilson system with `N ≠ 0`, given that both weighted
integrands are integrable. With the preceding four results the expectation is a positive, normalised,
linear, monotone functional at every `N ≠ 0` and every finite lattice.

DERIVED: `0` is the value `N` must differ from, which
`wilsonSystem_partition_pos` requires. -/
theorem wilsonSystem_expect_mono {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O O' : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hint : Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
    (hint' : Integrable (fun U => O' U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
    (hO : ∀ U, O U ≤ O' U) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
      ≤ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O' := by
  unfold System.expect
  refine (div_le_div_iff_of_pos_right (wilsonSystem_partition_pos hN bd β)).mpr ?_
  unfold System.corrNum
  exact integral_mono hint hint'
    (fun U => mul_le_mul_of_nonneg_right (hO U) (wilsonSystem_boltz_pos bd β U).le)

/-- `(wilsonSystem bd wilsonDensity).boltz β U ≤ Real.exp (|β| * (2 * Fintype.card Pq))` at any
`N ≠ 0`, from `wilsonSystem_action_nonneg` and `wilsonSystem_action_le`.

DERIVED: `0` is the value `N` must differ from; `2` is `wilsonDensity`'s own upper bound, multiplied
by the plaquette count. -/
theorem wilsonSystem_boltz_le {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
      ≤ Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))) := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : -β * (wilsonSystem bd (wilsonDensity (N := N))).action U
      ≤ |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) (wilsonSystem_action_nonneg hN bd U)
  have h2 : |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U
      ≤ |β| * (2 * (Fintype.card Pq : ℝ)) :=
    mul_le_mul_of_nonneg_left (wilsonSystem_action_le hN bd U) (abs_nonneg β)
  linarith

/-- `Integrable (fun U => O U * boltz β U)` for measurable `O` with `|O U| ≤ M`, on any `SU N`
Wilson system with `N ≠ 0`. Discharges the integrability hypotheses of `wilsonSystem_expect_add` and
`wilsonSystem_expect_mono` for bounded measurable observables.

DERIVED: `0` is the value `N` must differ from; `M` is the caller's bound. -/
theorem wilsonSystem_mul_boltz_integrable {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  refine (integrable_const (M * Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))))).mono'
    ((hmeas.mul (measurable_wilsonSystem_boltz bd β)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [norm_mul, Real.norm_of_nonneg (wilsonSystem_boltz_pos bd β U).le]
  have hO : ‖O U‖ ≤ M := by rw [Real.norm_eq_abs]; exact hbound U
  exact mul_le_mul hO (wilsonSystem_boltz_le hN bd β U) (wilsonSystem_boltz_pos bd β U).le
    (le_trans (norm_nonneg _) hO)

/-- `|⟨O⟩| ≤ M` for measurable `O` with `|O U| ≤ M`, on any `SU N` Wilson system with `N ≠ 0`. With
the preceding results the expectation is a bounded positive normalised linear functional at every
`N ≠ 0` and every finite lattice.

DERIVED: `0` is the value `N` must differ from; `M` is the caller's bound. -/
theorem wilsonSystem_expect_abs_le {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O| ≤ M := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hZ := wilsonSystem_partition_pos hN bd β
  have hint := wilsonSystem_mul_boltz_integrable hN bd β O hmeas M hbound
  have hb : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
    have := wilsonSystem_mul_boltz_integrable hN bd β (fun _ => (1 : ℝ)) measurable_const 1
      (fun _ => by norm_num)
    simpa using this
  have hintM := hb.const_mul M
  unfold System.expect
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  unfold System.corrNum
  calc |∫ U, O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))|
      ≤ ∫ U, |O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U|
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ U, M * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
        refine integral_mono hint.abs hintM (fun U => ?_)
        rw [abs_mul, abs_of_pos (wilsonSystem_boltz_pos bd β U)]
        exact mul_le_mul_of_nonneg_right (hbound U) (wilsonSystem_boltz_pos bd β U).le
    _ = M * ∫ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
        integral_const_mul M _
    _ = M * (wilsonSystem bd (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) β := rfl

/-- `⟨O⟩ = ∫ O dHaar` at `β = 0` on any `SU N` Wilson system: the weight is the constant one, so
the partition function is one and the expectation is the bare product-Haar average. No condition on
`N` is needed.

DERIVED: `0` is the coupling at which the exponent vanishes. -/
theorem wilsonSystem_expect_at_zero {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) 0 O
      = ∫ U, O U ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hb : ∀ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz 0 U = 1 :=
    fun U => by unfold System.boltz; simp
  have hvol : ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))).real Set.univ = 1 := by
    change (((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  have hden : (wilsonSystem bd (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) 0 = 1 := by
    unfold System.partition
    simp only [hb, integral_const, smul_eq_mul, mul_one, hvol]
  unfold System.expect System.corrNum
  simp only [hb, mul_one]
  rw [hden, div_one]

/-! ### The plaquette-energy observable at general `N` -/

/-- The plaquette-energy observable of an arbitrary `SU N` Wilson system:
`fun U => wilsonDensity (wilsonHol bd p U)`.

DERIVED: no numeral occurs. -/
noncomputable def wilsonPlaqObs {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ :=
  fun U => wilsonDensity (wilsonHol bd p U)

theorem wilsonPlaqObs_nonneg {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) : 0 ≤ wilsonPlaqObs bd p U :=
  wilsonDensity_nonneg hN _

theorem wilsonPlaqObs_le_two {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) : wilsonPlaqObs bd p U ≤ 2 :=
  wilsonDensity_le_two hN _

theorem measurable_wilsonPlaqObs {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq) : Measurable (wilsonPlaqObs (N := N) bd p) :=
  measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU N) bd p)

/-- `wilsonPlaqObs bd p (confConj _ g U) = wilsonPlaqObs bd p U`, which is
`wilsonAction_gauge_invariant` read at one plaquette.

DERIVED: no numeral occurs. -/
theorem wilsonPlaqObs_gauge_invariant {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    wilsonPlaqObs bd p (confConj (MassGap.SUN.SU N) g U) = wilsonPlaqObs bd p U :=
  wilsonAction_gauge_invariant bd g p U

/-- `0 ≤ ⟨wilsonPlaqObs bd p⟩ ≤ 2` on any `SU N` Wilson system with `N ≠ 0`, from
`wilsonSystem_expect_nonneg` and `wilsonSystem_expect_abs_le` at `M = 2`.

DERIVED: `0` is the value `N` must differ from and the lower bound asserted; `2` is
`wilsonDensity`'s own upper bound, which bounds the observable and hence its expectation. -/
theorem wilsonSystem_expect_plaqObs_mem {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) (p : Pq) :
    0 ≤ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (wilsonPlaqObs bd p)
      ∧ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (wilsonPlaqObs bd p) ≤ 2 := by
  refine ⟨wilsonSystem_expect_nonneg hN bd β (wilsonPlaqObs bd p)
    (fun U => wilsonPlaqObs_nonneg hN bd p U), ?_⟩
  have habs := wilsonSystem_expect_abs_le hN bd β (wilsonPlaqObs bd p)
    (measurable_wilsonPlaqObs bd p) 2
    (fun U => abs_le.mpr ⟨by linarith [wilsonPlaqObs_nonneg hN bd p U],
      wilsonPlaqObs_le_two hN bd p U⟩)
  exact (abs_le.mp habs).2

/-! ### The plaquette-energy observable of `sysReal` -/

/-- The plaquette-energy observable of `sysReal`: `fun U => wilsonDensity (wilsonHol bd2 p U)`, the
local Wilson action of plaquette `p`.

DERIVED: `2` is the plaquette count in `Fin 2`. -/
noncomputable def plaqObs (p : Fin 2) : sysReal.Config → ℝ :=
  fun U => wilsonDensity (wilsonHol bd2 p U)

/-- `0 ≤ plaqObs p U`, by `wilsonDensity_nonneg`.

DERIVED: `2` is the plaquette count in `Fin 2`; `0` is the lower bound asserted. -/
theorem plaqObs_nonneg (p : Fin 2) (U : sysReal.Config) : 0 ≤ plaqObs p U :=
  wilsonDensity_nonneg (by norm_num) _

/-- `plaqObs p U ≤ 2`, by `wilsonDensity_le_two`.

DERIVED: `2` is the plaquette count in `Fin 2` and, separately, `wilsonDensity`'s own upper
bound. -/
theorem plaqObs_le_two (p : Fin 2) (U : sysReal.Config) : plaqObs p U ≤ 2 :=
  wilsonDensity_le_two (by norm_num) _

/-- `Measurable (plaqObs p)`, as `wilsonDensity` composed with `measurable_bd2_hol`.

DERIVED: `2` is the plaquette count in `Fin 2`. -/
theorem measurable_plaqObs (p : Fin 2) : Measurable (plaqObs p) :=
  measurable_wilsonDensity.comp (measurable_bd2_hol p)

/-- `plaqObs p (confConj G2 g U) = plaqObs p U`, which is `wilsonAction_gauge_invariant` at `bd2`.

DERIVED: `2` is the plaquette count in `Fin 2`. -/
theorem plaqObs_gauge_invariant (g : G2) (p : Fin 2) (U : sysReal.Config) :
    plaqObs p (confConj G2 g U) = plaqObs p U :=
  wilsonAction_gauge_invariant bd2 g p U

/-- `0 ≤ ⟨plaqObs p⟩ ≤ 2` on `sysReal`, from `sysReal_expect_nonneg` and `sysReal_expect_abs_le` at
`M = 2`.

DERIVED: `2` is the plaquette count in `Fin 2` and, separately, `wilsonDensity`'s upper bound, which
bounds the observable and hence its expectation; `0` is the lower bound asserted. -/
theorem expect_plaqObs_mem (β : ℝ) (p : Fin 2) :
    0 ≤ sysReal.expect (probHaar G2) β (plaqObs p)
      ∧ sysReal.expect (probHaar G2) β (plaqObs p) ≤ 2 := by
  refine ⟨sysReal_expect_nonneg β (plaqObs p) (fun U => plaqObs_nonneg p U), ?_⟩
  have habs := sysReal_expect_abs_le β (plaqObs p) (measurable_plaqObs p) 2
    (fun U => abs_le.mpr ⟨by linarith [plaqObs_nonneg p U], plaqObs_le_two p U⟩)
  exact (abs_le.mp habs).2

/-! ### Independence of disjoint plaquette blocks

At `β = 0` the Wilson measure is the product Haar measure (`sysReal_expect_at_zero`), under which the
link coordinates of the two disjoint plaquettes are independent. -/

/-- The link block of plaquette `0`: `{0, 1, 2, 3} : Finset (Fin 8)`.

DERIVED: `8` is the link count; `0, 1, 2, 3` are the indices `bd2 0` traverses. -/
def blockA : Finset (Fin 8) := {0, 1, 2, 3}
/-- The link block of plaquette `1`: `{4, 5, 6, 7} : Finset (Fin 8)`, disjoint from `blockA`.

DERIVED: `8` is the link count; `4, 5, 6, 7` are the indices `bd2 1` traverses. -/
def blockB : Finset (Fin 8) := {4, 5, 6, 7}

theorem blockAB_disjoint : Disjoint blockA blockB := by decide

/-- For any finite index type and any two disjoint `Finset`s `S, T`, the coordinate tuples on `S`
and on `T` are independent under the product Haar measure on `SU N`-valued links. From
`iIndepFun_pi`, which makes the coordinates of a product measure mutually independent, grouped over
the two blocks by `iIndepFun.indepFun_finset`. `coords_indep` is the instance at `ι = Fin 8`,
`N = 2`.

DERIVED: no numeral occurs in the statement. -/
theorem coords_indep_SU {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun U (i : S) => (U : ι → MassGap.SUN.SU N) i.val)
      (fun U (i : T) => (U : ι → MassGap.SUN.SU N) i.val)
      (Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))) := by
  have hi : iIndepFun (fun (i : ι) (U : ι → MassGap.SUN.SU N) => U i)
      (Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  exact hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)

/-- The link coordinates on `blockA` and `blockB` are independent under `sysReal.vol (probHaar G2)`,
the instance of `coords_indep_SU` at those two disjoint blocks. At `β = 0` that measure is the Wilson
measure itself, by `sysReal_expect_at_zero`.

DERIVED: no numeral occurs in the statement. -/
theorem coords_indep :
    IndepFun (fun U (i : blockA) => (U : sysReal.Config) i.val)
      (fun U (i : blockB) => (U : sysReal.Config) i.val)
      (sysReal.vol (probHaar G2)) :=
  coords_indep_SU blockA blockB blockAB_disjoint

/-- For measurable `φ` and `ψ` reading only the disjoint blocks `S` and `T`,
`∫ φ(U|_S) * ψ(U|_T) = (∫ φ(U|_S)) * (∫ ψ(U|_T))` against the product Haar measure.
`coords_indep_SU` composed with `IndepFun.integral_fun_mul_eq_mul_integral`.

DERIVED: no numeral occurs in the statement. -/
theorem block_integral_factor {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (S T : Finset ι) (hST : Disjoint S T)
    (φ : (S → MassGap.SUN.SU N) → ℝ) (ψ : (T → MassGap.SUN.SU N) → ℝ)
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫ U, φ (fun i : S => (U : ι → MassGap.SUN.SU N) i.val)
        * ψ (fun i : T => (U : ι → MassGap.SUN.SU N) i.val)
        ∂(Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))))
      = (∫ U, φ (fun i : S => (U : ι → MassGap.SUN.SU N) i.val)
          ∂(Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))))
        * (∫ U, ψ (fun i : T => (U : ι → MassGap.SUN.SU N) i.val)
          ∂(Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N)))) := by
  have hrS : Measurable (fun U : ι → MassGap.SUN.SU N => fun i : S => U i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hrT : Measurable (fun U : ι → MassGap.SUN.SU N => fun i : T => U i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  exact ((coords_indep_SU S T hST).comp hφ hψ).integral_fun_mul_eq_mul_integral
    (hφ.comp hrS).aestronglyMeasurable (hψ.comp hrT).aestronglyMeasurable

/-- Extend a `blockA` tuple to a full configuration, placing the group identity on every link
outside the block. The value outside the block is arbitrary for the uses below, since `plaqObs 0`
does not read there.

DERIVED: `1` is the group identity used as the filler. -/
noncomputable def extendA (v : blockA → G2) : sysReal.Config :=
  fun j => if h : j ∈ blockA then v ⟨j, h⟩ else 1
/-- Extend a `blockB` tuple to a full configuration, placing the group identity on every link
outside the block.

DERIVED: `1` is the group identity used as the filler. -/
noncomputable def extendB (v : blockB → G2) : sysReal.Config :=
  fun j => if h : j ∈ blockB then v ⟨j, h⟩ else 1

theorem measurable_extendA : Measurable extendA := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j ∈ blockA
  · simp only [extendA, dif_pos h]; exact measurable_pi_apply (⟨j, h⟩ : ↥blockA)
  · simp only [extendA, dif_neg h]; exact measurable_const

theorem measurable_extendB : Measurable extendB := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j ∈ blockB
  · simp only [extendB, dif_pos h]; exact measurable_pi_apply (⟨j, h⟩ : ↥blockB)
  · simp only [extendB, dif_neg h]; exact measurable_const

/-- `plaqObs 0` equals a function of the `blockA` restriction alone, by `rfl`: the boundary word
`bd2 0` lists exactly the links `0, 1, 2, 3`, so extending the restriction with arbitrary values
elsewhere does not change the value.

DERIVED: `0` is the plaquette index whose block is `blockA`. -/
theorem plaqObs0_factor :
    plaqObs 0
      = (fun v => plaqObs 0 (extendA v)) ∘ (fun U (i : blockA) => (U : sysReal.Config) i.val) := by
  funext U
  show plaqObs 0 U = plaqObs 0 (extendA (fun i => U i.val))
  rfl

/-- `plaqObs 1` equals a function of the `blockB` restriction alone, by `rfl`, since `bd2 1` lists
exactly the links `4, 5, 6, 7`.

DERIVED: `1` is the plaquette index whose block is `blockB`. -/
theorem plaqObs1_factor :
    plaqObs 1
      = (fun v => plaqObs 1 (extendB v)) ∘ (fun U (i : blockB) => (U : sysReal.Config) i.val) := by
  funext U
  show plaqObs 1 U = plaqObs 1 (extendB (fun i => U i.val))
  rfl

/-- `IndepFun (plaqObs 0) (plaqObs 1)` under `sysReal.vol (probHaar G2)`. Each observable factors
through its own block (`plaqObs0_factor`, `plaqObs1_factor`), and those blocks are independent by
`coords_indep`.

DERIVED: `0` and `1` are the two plaquette indices. -/
theorem plaqObs_indep :
    IndepFun (plaqObs 0) (plaqObs 1) (sysReal.vol (probHaar G2)) := by
  rw [plaqObs0_factor, plaqObs1_factor]
  exact coords_indep.comp ((measurable_plaqObs 0).comp measurable_extendA)
    ((measurable_plaqObs 1).comp measurable_extendB)

/-- At `β = 0`, `⟨plaqObs 0 * plaqObs 1⟩ = ⟨plaqObs 0⟩ * ⟨plaqObs 1⟩`. `sysReal_expect_at_zero`
replaces each expectation by a product-Haar integral, and `plaqObs_indep` factorises the product
through `IndepFun.integral_fun_mul_eq_mul_integral`.

Scope: the two plaquettes of `sysReal` share no links, so this is an exact identity rather than a
bound, and it carries no dependence on a separation.

DERIVED: `0` is the coupling and the first plaquette index; `1` is the second plaquette index. -/
theorem expect_plaqObs_factor_at_zero :
    sysReal.expect (probHaar G2) 0 (fun U => plaqObs 0 U * plaqObs 1 U)
      = sysReal.expect (probHaar G2) 0 (plaqObs 0) * sysReal.expect (probHaar G2) 0 (plaqObs 1) := by
  rw [sysReal_expect_at_zero, sysReal_expect_at_zero, sysReal_expect_at_zero]
  exact plaqObs_indep.integral_fun_mul_eq_mul_integral
    (measurable_plaqObs 0).aestronglyMeasurable (measurable_plaqObs 1).aestronglyMeasurable

/-- `sysReal.boltz β U = exp (-β * plaqObs 0 U) * exp (-β * plaqObs 1 U)` at every coupling: the
action is the sum of the two plaquette energies, so the exponential splits.

DERIVED: `0` and `1` are the two plaquette indices. -/
theorem sysReal_boltz_factor (β : ℝ) (U : sysReal.Config) :
    sysReal.boltz β U = Real.exp (-β * plaqObs 0 U) * Real.exp (-β * plaqObs 1 U) := by
  unfold System.boltz
  rw [← Real.exp_add]
  congr 1
  have hact : sysReal.action U = plaqObs 0 U + plaqObs 1 U := by
    show (∑ p : Fin 2, wilsonDensity (wilsonHol bd2 p U))
        = wilsonDensity (wilsonHol bd2 0 U) + wilsonDensity (wilsonHol bd2 1 U)
    rw [Fin.sum_univ_two]
  rw [hact]; ring

/-- `sysReal.partition (probHaar G2) β = (∫ exp (-β * plaqObs 0)) * (∫ exp (-β * plaqObs 1))`, from
`sysReal_boltz_factor` and the independence of the two blocks.

DERIVED: `0` and `1` are the two plaquette indices. -/
theorem sysReal_partition_factor (β : ℝ) :
    sysReal.partition (probHaar G2) β
      = (∫ U, Real.exp (-β * plaqObs 0 U) ∂(sysReal.vol (probHaar G2)))
        * (∫ U, Real.exp (-β * plaqObs 1 U) ∂(sysReal.vol (probHaar G2))) := by
  have hg : Measurable (fun x : ℝ => Real.exp (-β * x)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hind : IndepFun (fun U => Real.exp (-β * plaqObs 0 U))
      (fun U => Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hg hg
  show (∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2))) = _
  simp_rw [sysReal_boltz_factor β]
  exact hind.integral_fun_mul_eq_mul_integral
    (hg.comp (measurable_plaqObs 0)).aestronglyMeasurable
    (hg.comp (measurable_plaqObs 1)).aestronglyMeasurable

/-- `⟨plaqObs 0 * plaqObs 1⟩ = ⟨plaqObs 0⟩ * ⟨plaqObs 1⟩` at every coupling. The plaquettes share no
links, so the weighted integrals split as `∫ φ₀ φ₁ e^{-βS} = A₀ A₁`, `∫ φ₀ e^{-βS} = A₀ Z₁` and
`∫ φ₁ e^{-βS} = Z₀ A₁`; with `Z = Z₀ Z₁ > 0` the two sides agree.

Scope: exact factorisation at every `β`, with no separation dependence. It is a statement about
`sysReal`, whose blocks are disjoint, and does not apply to `sysInt`.

DERIVED: `0` and `1` are the two plaquette indices. -/
theorem expect_plaqObs_factor (β : ℝ) :
    sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs 1 U)
      = sysReal.expect (probHaar G2) β (plaqObs 0) * sysReal.expect (probHaar G2) β (plaqObs 1) := by
  have hE : Measurable (fun x : ℝ => Real.exp (-β * x)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hG : Measurable (fun x : ℝ => x * Real.exp (-β * x)) :=
    measurable_id.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have iGG : IndepFun (fun U => plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
      (fun U => plaqObs 1 U * Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hG hG
  have iGE : IndepFun (fun U => plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
      (fun U => Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hG hE
  have iEG : IndepFun (fun U => Real.exp (-β * plaqObs 0 U))
      (fun U => plaqObs 1 U * Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hE hG
  set μ := sysReal.vol (probHaar G2) with hμ
  set A0 := ∫ U, plaqObs 0 U * Real.exp (-β * plaqObs 0 U) ∂μ with hA0
  set A1 := ∫ U, plaqObs 1 U * Real.exp (-β * plaqObs 1 U) ∂μ with hA1
  set Z0 := ∫ U, Real.exp (-β * plaqObs 0 U) ∂μ with hZ0
  set Z1 := ∫ U, Real.exp (-β * plaqObs 1 U) ∂μ with hZ1
  have gm0 := (hG.comp (measurable_plaqObs 0)).aestronglyMeasurable (μ := μ)
  have gm1 := (hG.comp (measurable_plaqObs 1)).aestronglyMeasurable (μ := μ)
  have em0 := (hE.comp (measurable_plaqObs 0)).aestronglyMeasurable (μ := μ)
  have em1 := (hE.comp (measurable_plaqObs 1)).aestronglyMeasurable (μ := μ)
  have hc01 : sysReal.corrNum (probHaar G2) β (fun U => plaqObs 0 U * plaqObs 1 U) = A0 * A1 := by
    show (∫ U, (plaqObs 0 U * plaqObs 1 U) * sysReal.boltz β U ∂μ) = A0 * A1
    have h : (fun U => (plaqObs 0 U * plaqObs 1 U) * sysReal.boltz β U)
        = (fun U => (plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
            * (plaqObs 1 U * Real.exp (-β * plaqObs 1 U))) := by
      funext U; rw [sysReal_boltz_factor]; ring
    rw [h]; exact iGG.integral_fun_mul_eq_mul_integral gm0 gm1
  have hc0 : sysReal.corrNum (probHaar G2) β (plaqObs 0) = A0 * Z1 := by
    show (∫ U, plaqObs 0 U * sysReal.boltz β U ∂μ) = A0 * Z1
    have h : (fun U => plaqObs 0 U * sysReal.boltz β U)
        = (fun U => (plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
            * Real.exp (-β * plaqObs 1 U)) := by
      funext U; rw [sysReal_boltz_factor]; ring
    rw [h]; exact iGE.integral_fun_mul_eq_mul_integral gm0 em1
  have hc1 : sysReal.corrNum (probHaar G2) β (plaqObs 1) = Z0 * A1 := by
    show (∫ U, plaqObs 1 U * sysReal.boltz β U ∂μ) = Z0 * A1
    have h : (fun U => plaqObs 1 U * sysReal.boltz β U)
        = (fun U => Real.exp (-β * plaqObs 0 U)
            * (plaqObs 1 U * Real.exp (-β * plaqObs 1 U))) := by
      funext U; rw [sysReal_boltz_factor]; ring
    rw [h]; exact iEG.integral_fun_mul_eq_mul_integral em0 gm1
  have hZeq : sysReal.partition (probHaar G2) β = Z0 * Z1 := sysReal_partition_factor β
  have hZne : sysReal.partition (probHaar G2) β ≠ 0 := (sysReal_partition_pos β).ne'
  unfold System.expect
  rw [hc01, hc0, hc1]
  rw [hZeq] at hZne ⊢
  field_simp

/-! ### Two plaquettes sharing a link

`sysReal` and `sysRing` have plaquettes with disjoint link sets, so their two-point function
factorises exactly at every coupling (`expect_plaqObs_factor`). `sysInt` below has two plaquettes
sharing link `3`. It is a well-defined gauge-invariant Wilson system by the general lemmas, but its
link blocks overlap, so the independence argument behind `plaqObs_indep` and
`expect_plaqObs_factor` has no instance there. -/

/-- Boundary words for two plaquettes over seven links sharing link `3`: plaquette `0` traverses
`0, 1` forward and `2, 3` backward, plaquette `1` traverses `3, 4` forward and `5, 6` backward.

DERIVED: `2` is the plaquette count and `7` the link count, which is one fewer than twice the block
size because link `3` is shared; `0` selects the first plaquette, and `0` through `6` are the link
indices in traversal order. -/
def bdInt (p : Fin 2) : List (Fin 7 × Bool) :=
  if p = 0 then [(0, true), (1, true), (2, false), (3, false)]
  else [(3, true), (4, true), (5, false), (6, false)]

/-- The two-plaquette `SU 2` Wilson system on `bdInt`, whose two plaquettes share link `3`.

DERIVED: no numeral occurs. -/
noncomputable def sysInt : System G2 := wilsonSystem bdInt wilsonDensity

/-- `0 < sysInt.partition (probHaar G2) β`, by `wilsonSystem_partition_pos` at `bdInt`.

DERIVED: `0` is the strict lower bound asserted. -/
theorem sysInt_partition_pos (β : ℝ) : 0 < sysInt.partition (probHaar G2) β :=
  wilsonSystem_partition_pos (by norm_num) bdInt β

/-- `sysInt.expect (probHaar G2) β (O ∘ confConj G2 g) = sysInt.expect (probHaar G2) β O`, by
`wilsonSystem_gauge_invariant` at `bdInt`.

DERIVED: no numeral occurs. -/
theorem sysInt_gauge_invariant (g : G2) (β : ℝ) (O : sysInt.Config → ℝ) :
    sysInt.expect (probHaar G2) β (fun U => O (confConj G2 g U))
      = sysInt.expect (probHaar G2) β O :=
  wilsonSystem_gauge_invariant bdInt g β O

/-- The link blocks of `sysInt`'s two plaquettes: `{0, 1, 2, 3}` and `{3, 4, 5, 6}` in `Finset (Fin 7)`.

DERIVED: `7` is the link count; the two index lists are the links `bdInt 0` and `bdInt 1` traverse,
which overlap at `3`. -/
def blockIntA : Finset (Fin 7) := {0, 1, 2, 3}
def blockIntB : Finset (Fin 7) := {3, 4, 5, 6}

/-- `(3 : Fin 7) ∈ blockIntA ∧ (3 : Fin 7) ∈ blockIntB`, by `decide`: link `3` belongs to both
blocks.

DERIVED: `7` is the link count and `3` the shared link's index. -/
theorem sysInt_shares_link : (3 : Fin 7) ∈ blockIntA ∧ (3 : Fin 7) ∈ blockIntB := by decide

/-- `¬ Disjoint blockIntA blockIntB`, by `decide`. So `coords_indep_SU`, whose hypothesis is
`Disjoint`, does not apply to `sysInt`'s two blocks, and the factorisation results proved for
`sysReal` have no instance there.

DERIVED: no numeral occurs in the statement; the shared index is inside the two blocks. -/
theorem blockInt_not_disjoint : ¬ Disjoint blockIntA blockIntB := by decide

#print axioms hbd2
#print axioms sysReal_invariant
#print axioms wilsonAction_gauge_invariant
#print axioms sysReal_gauge_invariant
#print axioms wilsonSystem_gauge_invariant
#print axioms hbd3
#print axioms sysRing_invariant
#print axioms measurable_bd2_hol
#print axioms sysReal_mul_boltz_integrable
#print axioms sysReal_expect_abs_le
#print axioms sysReal_expect_at_zero
#print axioms wilsonSystem_partition_pos
#print axioms wilsonSystem_expect_one
#print axioms wilsonSystem_expect_mono
#print axioms wilsonSystem_expect_abs_le
#print axioms wilsonSystem_expect_at_zero
#print axioms wilsonSystem_expect_plaqObs_mem
#print axioms coords_indep_SU
#print axioms block_integral_factor
#print axioms coords_indep
#print axioms plaqObs_indep
#print axioms expect_plaqObs_factor_at_zero
#print axioms sysReal_partition_factor
#print axioms expect_plaqObs_factor
#print axioms sysInt_partition_pos
#print axioms sysInt_gauge_invariant
#print axioms blockInt_not_disjoint
#print axioms plaqObs_gauge_invariant
#print axioms expect_plaqObs_mem

end MassGap.WilsonReal
