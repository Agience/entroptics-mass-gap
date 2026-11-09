import Mathlib
import MassGap.ObserverOSReconstructionS
import MassGap.ObserverRotationDense

noncomputable section

/-!
# MassGap.ObserverOSEuclidS — OS1, OS2 and SO(4) for the observer's Schwinger functions on decaying and Schwartz test functions

`ObserverOSSchwartz.schwSF` extends the energy density's Schwinger functions of one field to decaying
test functions. Here the extension is made for families of fields `Oᵢ` of the class `D`
(`schwSFM`), and the Euclidean axioms proved for compactly supported test functions are carried to it:
real translations (OS1), reflection positivity (OS2) and `SO(4)` from the `pyth` hypothesis.

## The cut-off

`chi R y = max 0 (min 1 (R + 1 − ‖y‖))`: continuous, `1` on the ball `‖y‖ ≤ R`, `0` beyond `R + 1`,
invariant under the axis reflections. `cut g R = chi R · g` is a test function, uniformly continuous
when `g` is continuous (compact support), and for `‖g‖₆ ≤ B`, `‖g − cut g R‖₅ ≤ B/(R + 1)`
(`decayBound_of_vanish`).

## Lipschitz estimate

`abs_contSF_sub_le_M`: under cube moments `CubeMomentsAt t C` for every field of the family,
two families of test functions with `‖fᵢ‖₅, ‖f'ᵢ‖₅ ≤ Bᵢ` and `‖f'ᵢ − fᵢ‖₅ ≤ δᵢ` have
`|S(f') − S(f)| ≤ (1 + n c) ∑ₐ 8192 δₐ ∏_{i ≠ a} 8192 Bᵢ`, `c = (2n)! t^{-2n} C`
(`ObserverOSSchwartz.abs_state_prod_sub_le` at each step, `moment_smear_decay_le` per factor).

## The extension and its approximations

`schwSFM O g = lim_R S(Oᵢ, cut gᵢ R)`; it exists (`tendsto_schwSFM`) and every sequence of test
functions converging to `g` in `‖·‖₅`, uniformly bounded, has Schwinger functions converging to it
(`tendsto_contSF_approx`). This is how each axiom passes to the limit: the axiom holds at each `R`
for an approximant of the transformed family, and the transformation moves the approximant by a
controlled amount in `‖·‖₅`.

* **OS1** (`schwSFM_translate`): `(1 + ‖y‖) ≤ (1 + ‖v‖)(1 + ‖y − v‖)`, so translation by `v` costs
  `(1 + ‖v‖)⁵` in `‖·‖₅`; `cut gᵢ R` is uniformly continuous, and
  `ObserverOS.contSF_energy0_translate_real` holds at each `R`.
* **SO(4)** (`schwSFM_rotate`): for `Aᵀ A = 1`, `‖y‖ ≤ 4 ‖A y‖`, so rotation costs `4⁵`; at each `R`
  `ObserverRotation.ObserverSO4` (from `pyth`, `ObserverRotationDense.observerSO4_energy0`) holds for
  the uniformly continuous `cut gᵢ R`.
* **OS2** (`schwSFM_gram_nonneg`): the cut-off keeps the positive-time support, so the cut monomials
  are margin monomials; `ContinuumFlow.contSF_gram_nonneg` at each `R`; the reflected cut-off is the
  cut-off of the reflected function (`chi` is reflection invariant); a limit of non-negative sums is
  non-negative.

`schwSF_eq_schwSFM` identifies the one-field extension of `ObserverOSSchwartz` (cube truncations)
with this one, and `schwCML_translate`, `schwCML_rotate` state OS1 and `SO(4)` for
`ObserverOSTempered.schwCML` on `𝓢(E4, ℝ)`.

The cube moments enter as one class-wide `t, C` (`ClassMoments`); per field they follow from
`UnitCubeExpBound` (`ObserverOSGrowth.cubeMoments_of_unitExp`) with constants depending on the field.
-/

namespace MassGap.ObserverOSEuclidS

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz
  MassGap.ObserverOSTempered MassGap.ObserverEnergyBox MassGap.ObserverRotation Filter
open scoped Topology Matrix

/-! ## 1. The continuous cut-off -/

section Cut

/-- **The cut-off** `max 0 (min 1 (R + 1 − ‖y‖))`.

DERIVED: `0`, `1` the values; `1` the width of the transition. -/
def chi (R : ℕ) (y : Fin 4 → ℝ) : ℝ := max 0 (min 1 ((R : ℝ) + 1 - ‖y‖))

/-- DERIVED: `0` the lower value. -/
theorem chi_nonneg (R : ℕ) (y : Fin 4 → ℝ) : 0 ≤ chi R y := le_max_left _ _

/-- DERIVED: `1` the upper value. -/
theorem chi_le_one (R : ℕ) (y : Fin 4 → ℝ) : chi R y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- DERIVED: `1` the value on the ball. -/
theorem chi_eq_one {R : ℕ} {y : Fin 4 → ℝ} (h : ‖y‖ ≤ R) : chi R y = 1 := by
  unfold chi
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

#print axioms chi_eq_one

/-- DERIVED: `0` the value beyond the ball; `1` the width. -/
theorem norm_lt_of_chi_ne {R : ℕ} {y : Fin 4 → ℝ} (h : chi R y ≠ 0) : ‖y‖ < R + 1 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold chi
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

#print axioms norm_lt_of_chi_ne

/-- DERIVED: no numeral. -/
theorem continuous_chi (R : ℕ) : Continuous (chi R) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

#print axioms continuous_chi

/-- DERIVED: `1` the upper value. -/
theorem abs_chi_mul_le (R : ℕ) (y : Fin 4 → ℝ) (v : ℝ) : |chi R y * v| ≤ |v| := by
  rw [abs_mul, abs_of_nonneg (chi_nonneg R y)]
  exact mul_le_of_le_one_left (abs_nonneg _) (chi_le_one R y)

#print axioms abs_chi_mul_le

/-- The axis reflections preserve the sup norm.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem norm_reflR (τ : Fin 4) (y : Fin 4 → ℝ) : ‖reflR τ y‖ = ‖y‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_))
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_))
  · rw [Real.norm_eq_abs, abs_reflR]
    have := norm_le_pi_norm y i
    rwa [Real.norm_eq_abs] at this
  · rw [Real.norm_eq_abs, ← abs_reflR τ y i]
    have := norm_le_pi_norm (reflR τ y) i
    rwa [Real.norm_eq_abs] at this

#print axioms norm_reflR

/-- DERIVED: no numeral. -/
theorem chi_reflR (R : ℕ) (τ : Fin 4) (y : Fin 4 → ℝ) : chi R (reflR τ y) = chi R y := by
  unfold chi; rw [norm_reflR]

#print axioms chi_reflR

/-- **A function vanishing on the ball of radius `R` and dominated by `g`** has
`‖h‖₅ ≤ ‖g‖₆ / (R + 1)`.

DERIVED: `5`, `6` the two orders; `1` the weight's unit term; `0` the sign. -/
theorem decayBound_of_vanish {h g : (Fin 4 → ℝ) → ℝ} {B : ℝ} (hg : DecayBound 6 g B) {R : ℝ}
    (hR : 0 ≤ R) (hvan : ∀ y, ‖y‖ ≤ R → h y = 0) (hle : ∀ y, |h y| ≤ |g y|) :
    DecayBound 5 h (B / (R + 1)) := by
  intro y
  have hy0 := norm_nonneg y
  have hR0 : (0 : ℝ) < R + 1 := by linarith
  by_cases hy : ‖y‖ ≤ R
  · rw [hvan y hy, abs_zero, mul_zero]
    exact div_nonneg hg.nonneg hR0.le
  · push_neg at hy
    have hp : 0 ≤ (1 + ‖y‖) ^ 5 := by positivity
    rw [le_div_iff₀ hR0]
    calc (1 + ‖y‖) ^ 5 * |h y| * (R + 1) ≤ (1 + ‖y‖) ^ 5 * |g y| * (1 + ‖y‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hle y) hp) (by linarith) hR0.le
            (mul_nonneg hp (abs_nonneg _))
      _ = (1 + ‖y‖) ^ 6 * |g y| := by ring
      _ ≤ B := hg y

#print axioms decayBound_of_vanish

/-- **The cut-off test function** `chi R · g`, supported in `[-(R + 1), R + 1]⁴`.

DERIVED: `1` the width of the cut-off; `0` the sign of the radius. -/
def cut (g : Decaying) (R : ℕ) : TestFn :=
  ⟨fun y => chi R y * g.1 y, by
    obtain ⟨B, hB⟩ := g.2
    refine ⟨R + 1, B, by positivity, fun y => (abs_chi_mul_le R y _).trans (hB.abs_le y),
      fun y hy i => ?_⟩
    have h1 : chi R y ≠ 0 := fun h => hy (by show chi R y * g.1 y = 0; rw [h, zero_mul])
    have h2 := norm_lt_of_chi_ne h1
    have h3 := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at h3
    linarith⟩

/-- The cut-off keeps every weighted bound.

DERIVED: `1` the weight's unit term. -/
theorem decayBound_cut {K : ℕ} {g : Decaying} {A : ℝ} (h : DecayBound K g.1 A) (R : ℕ) :
    DecayBound K (cut g R).1 A := fun y =>
  (mul_le_mul_of_nonneg_left (abs_chi_mul_le R y (g.1 y))
    (pow_nonneg (by linarith [norm_nonneg y]) _)).trans (h y)

#print axioms decayBound_cut

/-- **The cut-off is close to the function**: `‖cut g R − g‖₅ ≤ ‖g‖₆ / (R + 1)`, pointwise.

DERIVED: `5`, `6` the orders; `1` the value on the ball. -/
theorem cut_sub_le {g : Decaying} {B : ℝ} (hB : DecayBound 6 g.1 B) (R : ℕ) (y : Fin 4 → ℝ) :
    (1 + ‖y‖) ^ 5 * |chi R y * g.1 y - g.1 y| ≤ B / ((R : ℝ) + 1) := by
  refine decayBound_of_vanish (h := fun y => chi R y * g.1 y - g.1 y) hB (Nat.cast_nonneg R)
    (fun y hy => by show chi R y * g.1 y - g.1 y = 0; rw [chi_eq_one hy, one_mul, sub_self])
    (fun y => ?_) y
  show |chi R y * g.1 y - g.1 y| ≤ |g.1 y|
  rw [show chi R y * g.1 y - g.1 y = -((1 - chi R y) * g.1 y) by ring, abs_neg, abs_mul,
    abs_of_nonneg (by linarith [chi_le_one R y])]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [chi_nonneg R y])

#print axioms cut_sub_le

/-- **The cut-off of a continuous function is uniformly continuous** (continuous with compact
support).

DERIVED: `0` the centre of the ball; `1` its excess radius. -/
theorem uniformContinuous_cut {g : Decaying} (hg : Continuous g.1) (R : ℕ) :
    UniformContinuous (cut g R).1 := by
  refine HasCompactSupport.uniformContinuous_of_continuous ?_ ((continuous_chi R).mul hg)
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 4 → ℝ) ((R : ℝ) + 1)) ?_
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  show chi R y * g.1 y = 0
  have h : chi R y = 0 := by
    by_contra hc
    exact absurd (norm_lt_of_chi_ne hc) (not_lt.mpr hy.le)
  rw [h, zero_mul]

#print axioms uniformContinuous_cut

end Cut

/-! ## 2. The Lipschitz estimate for families of fields -/

section Lipschitz

variable {N : ℕ}

/-- The moment constant `(2n)! t^{-2n} C`.

DERIVED: `2` makes the power even. -/
def cN (t C : ℝ) (n : ℕ) : ℝ := ((2 * n).factorial : ℝ) / t ^ (2 * n) * C

/-- DERIVED: `0` the sign. -/
theorem cN_nonneg {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (n : ℕ) : 0 ≤ cN t C n :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0

#print axioms cN_nonneg

/-- **Cube moments uniform over the class**: one `t > 0`, `C ≥ 0` with `CubeMomentsAt` for every field
of `D`.

DERIVED: no numeral of its own. -/
def ClassMoments (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (t C : ℝ) :
    Prop :=
  ∀ O ∈ D, CubeMomentsAt hN W O t C

/-- **One step, a family of fields**: `|latSF| ≤ (1 + n c) ∏ᵢ 8192 (Aᵢ + ε)`.

DERIVED: `0` the excluded colour count and the signs; `8192` is `sum_shellWeight_le`'s; `1`, `2`
are `abs_state_prod_le`'s; `5 = 4 + 1` the decay order, the least integer above the dimension
(`ObserverOSSchwartz`). -/
theorem abs_latSF_le_M (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N))
    (hO : ∀ i, O i ∈ D) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) {k : ℕ}
    (hk : ∀ i, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (O i)).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C))
    (f : ι → TestFn) (A : ι → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) {ε : ℝ} (hε : 0 < ε) :
    |latSF hN (energy0 W D hD) k (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι)) * ∏ i, 8192 * (A i + ε) := by
  have hc0 := cN_nonneg ht hC0 (Fintype.card ι)
  have hb := abs_state_prod_le (stateK hN k)
    (fun i => smear (dySpacing N k) ((energy0 W D hD).map k (O i)).1 (f i))
    (fun i => 8192 * (A i + ε))
    (fun i => mul_pos (by norm_num) (by linarith [(hA i).nonneg]))
    (c := cN t C (Fintype.card ι))
    (fun i => (moment_smear_decay_le hN W hD hpos (hO i) k (f i) (hA i) hc0 _
        (Fintype.card_pos_iff.mpr ⟨i⟩).ne' (fun R hR => hk i R hR _)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (hA i).nonneg) (by linarith) _) hc0))
  show |latSk hN k (fun i => (energy0 W D hD).field k ((O i, f i) : SField N))| ≤ _
  rw [latSk_eq]
  exact hb

#print axioms abs_latSF_le_M

/-- **One step of the Lipschitz estimate, a family of fields.**

DERIVED: `0` the excluded colour count and the signs; `8192` is `sum_shellWeight_le`'s; `-1` the
coefficient of the subtracted test function; `1`, `2` are `abs_state_prod_le`'s; `5 = 4 + 1` the decay
order, as in `abs_latSF_le_M`. -/
theorem abs_latSF_sub_le_M (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, O i ∈ D) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    {k : ℕ}
    (hk : ∀ i, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (O i)).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C))
    (f f' : ι → TestFn) (B δ : ι → ℝ) (hB : ∀ i, DecayBound 5 (f i).1 (B i))
    (hB' : ∀ i, DecayBound 5 (f' i).1 (B i))
    (hδ : ∀ i y, (1 + ‖y‖) ^ 5 * |(f' i).1 y - (f i).1 y| ≤ δ i) {ε : ℝ} (hε : 0 < ε) :
    |latSF hN (energy0 W D hD) k (fun i => (O i, f' i))
        - latSF hN (energy0 W D hD) k (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
        * ∑ a, 8192 * (δ a + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε) := by
  have hc0 := cN_nonneg ht hC0 (Fintype.card ι)
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hmom : ∀ i (g : TestFn) (A : ℝ), DecayBound 5 g.1 A →
      stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k (O i)).1 g
        ^ (2 * Fintype.card ι)) ≤ cN t C (Fintype.card ι) * (8192 * (A + ε)) ^ (2 * Fintype.card ι) :=
    fun i g A hA' =>
      (moment_smear_decay_le hN W hD hpos (hO i) k g hA' hc0 _
        (Fintype.card_pos_iff.mpr ⟨i⟩).ne' (fun R hR => hk i R hR _)).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) hA'.nonneg) (by linarith) _) hc0)
  have hdec : ∀ i, DecayBound 5 (testAdd (f' i) (testSmul (-1) (f i))).1 (δ i) := fun i y => by
    show (1 + ‖y‖) ^ 5 * |(f' i).1 y + -1 * (f i).1 y| ≤ δ i
    rw [neg_one_mul, ← sub_eq_add_neg]
    exact hδ i y
  have hb := abs_state_prod_sub_le (stateK hN k)
    (fun i => smear (dySpacing N k) ((energy0 W D hD).map k (O i)).1 (f i))
    (fun i => smear (dySpacing N k) ((energy0 W D hD).map k (O i)).1 (f' i))
    (fun i => 8192 * (B i + ε)) (fun i => 8192 * (δ i + ε))
    (fun i => mul_pos (by norm_num) (by linarith [(hB i).nonneg]))
    (fun i => mul_pos (by norm_num) (by linarith [(hdec i).nonneg]))
    (c := cN t C (Fintype.card ι))
    (fun i => hmom i _ _ (hB i)) (fun i => hmom i _ _ (hB' i))
    (fun i => by
      show stateK hN k ((smear (dySpacing N k) ((energy0 W D hD).map k (O i)).1 (f' i)
          - smear (dySpacing N k) ((energy0 W D hD).map k (O i)).1 (f i))
            ^ (2 * Fintype.card ι)) ≤ _
      rw [← smear_tail ha]
      exact hmom i _ _ (hdec i))
  show |latSk hN k (fun i => (energy0 W D hD).field k ((O i, f' i) : SField N))
    - latSk hN k (fun i => (energy0 W D hD).field k ((O i, f i) : SField N))| ≤ _
  rw [latSk_eq, latSk_eq]
  exact hb

#print axioms abs_latSF_sub_le_M

/-- **A family of fields converges along the ultrafilter**, under the class moments.

DERIVED: `1` the choice `ε = 1`; `5 = 4 + 1` the decay order, as in `abs_latSF_le_M`. -/
theorem tendsto_latSF_M (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N))
    (hO : ∀ i, O i ∈ D) (f : ι → TestFn) (A : ι → ℝ) (hA : ∀ i, DecayBound 5 (f i).1 (A i)) :
    Tendsto (fun k => latSF hN (energy0 W D hD) k (fun i => (O i, f i))) (ultra : Filter ℕ)
      (𝓝 (contSF hN (energy0 W D hD) (fun i => (O i, f i)))) := by
  have hstep : ∀ᶠ k in atTop, |latSF hN (energy0 W D hD) k (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι)) * ∏ i, 8192 * (A i + 1) :=
    (Filter.eventually_all.mpr (fun i => hU (O i) (hO i))).mono
      (fun k hk => abs_latSF_le_M hN W hD hpos O hO ht hC0 hk f A hA one_pos)
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hstep
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_latSF_M

/-- **The Lipschitz estimate in `‖·‖₅` for a family of fields**:
`|S(f') − S(f)| ≤ (1 + n c) ∑ₐ 8192 δₐ ∏_{i ≠ a} 8192 Bᵢ`.

DERIVED: `0` the signs and the limit point; `8192`, `5` as in `abs_latSF_sub_le_M`; `1`, `2` are
`abs_state_prod_le`'s. -/
theorem abs_contSF_sub_le_M (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, O i ∈ D)
    (f f' : ι → TestFn) (B δ : ι → ℝ) (hB : ∀ i, DecayBound 5 (f i).1 (B i))
    (hB' : ∀ i, DecayBound 5 (f' i).1 (B i))
    (hδ : ∀ i y, (1 + ‖y‖) ^ 5 * |(f' i).1 y - (f i).1 y| ≤ δ i) :
    |contSF hN (energy0 W D hD) (fun i => (O i, f' i))
        - contSF hN (energy0 W D hD) (fun i => (O i, f i))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
        * ∑ a, 8192 * δ a * ∏ i ∈ Finset.univ \ {a}, 8192 * B i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hT' := tendsto_latSF_M hN W hD hpos ht hC0 hU O hO f' B hB'
  have hT := tendsto_latSF_M hN W hD hpos ht hC0 hU O hO f B hB
  have hcont : Continuous (fun ε : ℝ => (1 + Fintype.card ι * cN t C (Fintype.card ι))
      * ∑ a, 8192 * (δ a + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε)) :=
    continuous_const.mul (continuous_finsetSum _ (fun a _ =>
      (continuous_const.mul (continuous_const.add continuous_id)).mul
        (continuous_finsetProd _
          (fun i _ => continuous_const.mul (continuous_const.add continuous_id)))))
  have h := le_of_forall_pos_continuous hcont (fun ε hε => by
    have hstep : ∀ᶠ k in atTop,
        |latSF hN (energy0 W D hD) k (fun i => (O i, f' i))
          - latSF hN (energy0 W D hD) k (fun i => (O i, f i))|
        ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
          * ∑ a, 8192 * (δ a + ε) * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + ε) :=
      (Filter.eventually_all.mpr (fun i => hU (O i) (hO i))).mono
        (fun k hk => abs_latSF_sub_le_M hN W hD hpos O hO ht hC0 hk f f' B δ hB hB' hδ hε)
    exact le_of_tendsto (hT'.sub hT).abs (hstep.filter_mono ultra_le))
  simpa only [add_zero] using h

#print axioms abs_contSF_sub_le_M

end Lipschitz

/-! ## 3. The extension to families of fields -/

section Extension

variable {N : ℕ}

/-- **The Schwinger functions of a family of fields on decaying functions**: the limit of those of
the cut-offs.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def schwSFM (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {ι : Type}
    [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying) : ℝ :=
  limUnder atTop (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R)))

/-- The bound of the Lipschitz estimate tends to zero with `η` and `1/(R + 1)`.

DERIVED: `0` the limit; `1` the shift; `8192` the gauge. -/
theorem tendsto_lip_bound {ι : Type} [Fintype ι] (K : ℝ) (B P : ι → ℝ) {η : ℕ → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun R : ℕ => K * ∑ a, 8192 * (η R + B a / ((R : ℝ) + 1)) * P a) atTop (𝓝 0) := by
  have hinv : Tendsto (fun R : ℕ => 1 / ((R : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h : Tendsto (fun R : ℕ => K * ∑ a, 8192 * (η R + B a * (1 / ((R : ℝ) + 1))) * P a) atTop
      (𝓝 (K * ∑ a, 8192 * (0 + B a * 0) * P a)) :=
    tendsto_const_nhds.mul (tendsto_finsetSum _ (fun a _ =>
      ((tendsto_const_nhds.mul (hη.add (tendsto_const_nhds.mul hinv))).mul tendsto_const_nhds)))
  simp only [mul_zero, add_zero, zero_mul, Finset.sum_const_zero] at h
  refine h.congr (fun R => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [mul_one_div]

#print axioms tendsto_lip_bound

/-- **The cut-off Schwinger functions converge**: `S(Oᵢ, cut gᵢ R) → schwSFM O g`.

DERIVED: `0` the sign of `ε`; `6`, `5` the orders; `1` the shift. -/
theorem tendsto_schwSFM (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N))
    (hO : ∀ i, O i ∈ D) (g : ι → Decaying) :
    Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R))) atTop
      (𝓝 (schwSFM hN W D hD O g)) := by
  classical
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hB5 : ∀ (S : ℕ) i, DecayBound 5 (cut (g i) S).1 (B i) :=
    fun S i => decayBound_cut ((hB i).mono (by norm_num)) S
  set b : ℕ → ℝ := fun R => (1 + Fintype.card ι * cN t C (Fintype.card ι))
    * ∑ a, 8192 * (0 + B a / ((R : ℝ) + 1)) * ∏ i ∈ Finset.univ \ {a}, 8192 * B i with hbdef
  have hb : Tendsto b atTop (𝓝 0) := tendsto_lip_bound _ B _ tendsto_const_nhds
  have hdist : ∀ M m : ℕ, M ≤ m →
      dist (contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) m)))
        (contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) M))) ≤ b M := by
    intro M m hMm
    rw [Real.dist_eq]
    refine (abs_contSF_sub_le_M hN W hD hpos ht hC0 hU O hO (fun i => cut (g i) M)
      (fun i => cut (g i) m) B (fun i => B i / ((M : ℝ) + 1)) (fun i => hB5 M i)
      (fun i => hB5 m i) (fun i y => ?_)).trans (le_of_eq ?_)
    · refine decayBound_of_vanish (h := fun y => chi m y * (g i).1 y - chi M y * (g i).1 y)
        (hB i) (Nat.cast_nonneg M) (fun y hy => ?_) (fun y => ?_) y
      · have h1 := chi_eq_one hy
        have h2 : chi m y = 1 := chi_eq_one (hy.trans (by exact_mod_cast hMm))
        simp only [h1, h2, sub_self]
      · show |chi m y * (g i).1 y - chi M y * (g i).1 y| ≤ |(g i).1 y|
        rw [← sub_mul, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        rw [abs_le]
        constructor <;> linarith [chi_le_one m y, chi_nonneg m y, chi_le_one M y, chi_nonneg M y]
    · simp only [hbdef, zero_add]
  have hcs : CauchySeq
      (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R))) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨M, hM⟩ := (hb.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    exact ⟨M, fun m hm => (hdist M m hm).trans_lt (hM M le_rfl)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_schwSFM

/-- **Every approximation converges to the extension**: test functions `h R i`, uniformly bounded in
`‖·‖₅`, with `‖h R i − gᵢ‖₅ ≤ η R → 0`, have `S(Oᵢ, h R i) → schwSFM O g`.

DERIVED: `0` the limit; `5`, `6` the orders; `1` the shift; `8192` the gauge. -/
theorem tendsto_contSF_approx (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N))
    (hO : ∀ i, O i ∈ D) (g : ι → Decaying) (h : ℕ → ι → TestFn) (B' : ι → ℝ)
    (hhB : ∀ R i, DecayBound 5 (h R i).1 (B' i)) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hh : ∀ R i y, (1 + ‖y‖) ^ 5 * |(h R i).1 y - (g i).1 y| ≤ η R) :
    Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, h R i))) atTop
      (𝓝 (schwSFM hN W D hD O g)) := by
  classical
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hS := tendsto_schwSFM hN W hD hpos ht hC0 hU O hO g
  have hBB : ∀ R i, DecayBound 5 (cut (g i) R).1 (B i + B' i) := fun R i y =>
    ((decayBound_cut ((hB i).mono (by norm_num)) R) y).trans (by linarith [(hhB R i).nonneg])
  have hBB' : ∀ R i, DecayBound 5 (h R i).1 (B i + B' i) := fun R i y =>
    ((hhB R i) y).trans (by linarith [(hB i).nonneg])
  have hdiff : ∀ R : ℕ,
      |contSF hN (energy0 W D hD) (fun i => (O i, h R i))
        - contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R))|
      ≤ (1 + Fintype.card ι * cN t C (Fintype.card ι))
        * ∑ a, 8192 * (η R + B a / ((R : ℝ) + 1))
          * ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + B' i) := fun R =>
    abs_contSF_sub_le_M hN W hD hpos ht hC0 hU O hO (fun i => cut (g i) R) (fun i => h R i)
      (fun i => B i + B' i) (fun i => η R + B i / ((R : ℝ) + 1)) (hBB R) (hBB' R)
      (fun i y => by
        have h1 := hh R i y
        have h2 := cut_sub_le (hB i) R y
        have hp : 0 ≤ (1 + ‖y‖) ^ 5 := pow_nonneg (by linarith [norm_nonneg y]) 5
        show (1 + ‖y‖) ^ 5 * |(h R i).1 y - chi R y * (g i).1 y| ≤ _
        have h3 : |(h R i).1 y - chi R y * (g i).1 y|
            ≤ |(h R i).1 y - (g i).1 y| + |chi R y * (g i).1 y - (g i).1 y| := by
          have := abs_sub_le ((h R i).1 y) ((g i).1 y) (chi R y * (g i).1 y)
          rwa [abs_sub_comm ((g i).1 y)] at this
        calc (1 + ‖y‖) ^ 5 * |(h R i).1 y - chi R y * (g i).1 y|
            ≤ (1 + ‖y‖) ^ 5 * (|(h R i).1 y - (g i).1 y| + |chi R y * (g i).1 y - (g i).1 y|) :=
              mul_le_mul_of_nonneg_left h3 hp
          _ ≤ η R + B i / ((R : ℝ) + 1) := by rw [mul_add]; linarith)
  have hlim := tendsto_lip_bound (1 + Fintype.card ι * cN t C (Fintype.card ι)) B
    (fun a => ∏ i ∈ Finset.univ \ {a}, 8192 * (B i + B' i)) hη
  have hsub : Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, h R i))
      - contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun R => by rw [Real.norm_eq_abs]; exact hdiff R) hlim
  have := hsub.add hS
  simp only [sub_add_cancel, zero_add] at this
  exact this

#print axioms tendsto_contSF_approx

/-- **The one-field extension of `ObserverOSSchwartz` is this one**: `schwSF O g = schwSFM (O, …, O) g`
(cube truncations approximate in `‖·‖₅`).

DERIVED: `5`, `6` the orders; `1` the indicator on the cube; `0` the sign. -/
theorem schwSF_eq_schwSFM (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) {n : ℕ}
    (g : Fin n → Decaying) :
    schwSF hN W D hD O g = schwSFM hN W D hD (fun _ => O) g := by
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hB0 : ∀ i, 0 ≤ B i := fun i => (hB i).nonneg
  have hT := tendsto_contSF_approx hN W hD hpos ht hC0 hU (fun _ => O) (fun _ => hO) g
    (fun R i => trunc (g i) R) B (fun R i => decayBound_trunc ((hB i).mono (by norm_num)) R)
    (fun R => (∑ i, B i) / ((R : ℝ) + 1))
    (by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (∑ i, B i)
      rw [mul_zero] at h
      exact h.congr (fun R => by rw [mul_one_div]))
    (fun R i y => by
      have h1 := decayBound_of_vanish (h := fun y => cubeInd (R : ℝ) y * (g i).1 y - (g i).1 y)
        (hB i) (Nat.cast_nonneg R)
        (fun y hy => by
          have hin : ∀ j, |y j| ≤ (R : ℝ) := fun j => by
            have := norm_le_pi_norm y j
            rw [Real.norm_eq_abs] at this
            linarith
          show cubeInd (R : ℝ) y * (g i).1 y - (g i).1 y = 0
          unfold cubeInd
          rw [if_pos hin, one_mul, sub_self])
        (fun y => by
          show |cubeInd (R : ℝ) y * (g i).1 y - (g i).1 y| ≤ |(g i).1 y|
          unfold cubeInd
          split_ifs <;> simp) y
      refine h1.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      exact Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_univ i))
  exact hT.limUnder_eq

#print axioms schwSF_eq_schwSFM

end Extension

/-! ## 4. Translations, rotations and reflections of decaying functions -/

section Moves

/-- `1 + ‖y‖ ≤ (1 + ‖v‖)(1 + ‖y − v‖)`.

DERIVED: `1` the weight's unit term. -/
theorem one_add_norm_le_mul (y v : Fin 4 → ℝ) : 1 + ‖y‖ ≤ (1 + ‖v‖) * (1 + ‖y - v‖) := by
  have h : ‖y‖ ≤ ‖y - v‖ + ‖v‖ := by
    have := norm_add_le (y - v) v
    rwa [sub_add_cancel] at this
  nlinarith [norm_nonneg v, norm_nonneg (y - v)]

#print axioms one_add_norm_le_mul

/-- **Translation costs `(1 + ‖v‖)^K` in `‖·‖_K`.**

DERIVED: `1` the weight's unit term. -/
theorem decayBound_translate {K : ℕ} {g : (Fin 4 → ℝ) → ℝ} {A : ℝ} (h : DecayBound K g A)
    (v : Fin 4 → ℝ) : DecayBound K (fun y => g (y - v)) ((1 + ‖v‖) ^ K * A) := fun y => by
  have h1 := one_add_norm_le_mul y v
  have h0 : 0 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  calc (1 + ‖y‖) ^ K * |g (y - v)| ≤ ((1 + ‖v‖) * (1 + ‖y - v‖)) ^ K * |g (y - v)| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 K) (abs_nonneg _)
    _ = (1 + ‖v‖) ^ K * ((1 + ‖y - v‖) ^ K * |g (y - v)|) := by rw [mul_pow]; ring
    _ ≤ (1 + ‖v‖) ^ K * A :=
        mul_le_mul_of_nonneg_left (h (y - v)) (pow_nonneg (by linarith [norm_nonneg v]) K)

#print axioms decayBound_translate

/-- The translate of a decaying function.

DERIVED: `6` the order. -/
def decTr (g : Decaying) (v : Fin 4 → ℝ) : Decaying :=
  ⟨fun y => g.1 (y - v), by
    obtain ⟨B, hB⟩ := g.2
    exact ⟨_, decayBound_translate hB v⟩⟩

/-- **`‖y‖ ≤ 4 ‖A y‖` for `Aᵀ A = 1`**: `y = Aᵀ (A y)` and every entry of `A` is at most `1`
(`ObserverRotation.rotTest_support`, `ObserverRotationDense.abs_entry_le_one`).

DERIVED: `4` the number of coordinates; `1` the entry bound. -/
theorem norm_le_four_mul {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) (y : Fin 4 → ℝ) :
    ‖y‖ ≤ 4 * ‖A.mulVec y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  rw [Real.norm_eq_abs]
  have h1 := rotTest_support A hA y (R := ‖A.mulVec y‖)
    (fun j => by have := norm_le_pi_norm (A.mulVec y) j; rwa [Real.norm_eq_abs] at this) i
  have h2 : ∑ j, |A j i| ≤ 4 := by
    calc ∑ j, |A j i| ≤ ∑ _j : Fin 4, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => ObserverRotationDense.abs_entry_le_one hA j i)
      _ = 4 := by simp
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

#print axioms norm_le_four_mul

/-- **Rotation costs `4^K` in `‖·‖_K`.**

DERIVED: `4` from `norm_le_four_mul`; `1` the weight's unit term. -/
theorem decayBound_rotate {K : ℕ} {g : (Fin 4 → ℝ) → ℝ} {B : ℝ} (h : DecayBound K g B)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) :
    DecayBound K (fun y => g (A.mulVec y)) (4 ^ K * B) := fun y => by
  have h1 := norm_le_four_mul hA y
  have h0 : 0 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have h2 : 1 + ‖y‖ ≤ 4 * (1 + ‖A.mulVec y‖) := by linarith [norm_nonneg (A.mulVec y)]
  calc (1 + ‖y‖) ^ K * |g (A.mulVec y)| ≤ (4 * (1 + ‖A.mulVec y‖)) ^ K * |g (A.mulVec y)| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 K) (abs_nonneg _)
    _ = 4 ^ K * ((1 + ‖A.mulVec y‖) ^ K * |g (A.mulVec y)|) := by rw [mul_pow]; ring
    _ ≤ 4 ^ K * B := mul_le_mul_of_nonneg_left (h _) (by positivity)

#print axioms decayBound_rotate

/-- The rotation `g ∘ A` of a decaying function.

DERIVED: `6` the order. -/
def decRot (g : Decaying) {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) : Decaying :=
  ⟨fun y => g.1 (A.mulVec y), by
    obtain ⟨B, hB⟩ := g.2
    exact ⟨_, decayBound_rotate hB hA⟩⟩

/-- The axis reflection `g ∘ reflR τ` of a decaying function.

DERIVED: `6` the order. -/
def decRefl (τ : Fin 4) (g : Decaying) : Decaying :=
  ⟨fun y => g.1 (reflR τ y), by
    obtain ⟨B, hB⟩ := g.2
    exact ⟨B, fun y => by
      have := hB (reflR τ y)
      rwa [norm_reflR] at this⟩⟩

end Moves

/-! ## 5. OS1 and SO(4) on decaying functions -/

section Euclid

variable {N : ℕ}

/-- **OS1 for real translations on continuous decaying functions**: given (E) in cube form on `D`
and the class moments, `schwSFM O (g · − v) = schwSFM O g` for every `v ∈ ℝ⁴`. At each `R`,
`ObserverOS.contSF_energy0_translate_real` for the uniformly continuous `cut gᵢ R`; the translates of
the cut-offs approximate `gᵢ(· − v)` within `(1 + ‖v‖)⁵ ‖gᵢ‖₆/(R + 1)`.

DERIVED: `5` the order; `1` the shift; `0` the limit. -/
theorem schwSFM_translate (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) {ι : Type} [Fintype ι]
    (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, O i ∈ D) (g : ι → Decaying)
    (hg : ∀ i, Continuous (g i).1) (v : Fin 4 → ℝ) :
    schwSFM hN W D hD O (fun i => decTr (g i) v) = schwSFM hN W D hD O g := by
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hB0 : ∀ i, 0 ≤ B i := fun i => (hB i).nonneg
  have hv : 0 ≤ (1 + ‖v‖) ^ 5 := pow_nonneg (by linarith [norm_nonneg v]) 5
  have hT := tendsto_contSF_approx hN W hD hpos ht hC0 hU O hO (fun i => decTr (g i) v)
    (fun R i => (cut (g i) R).translate v) (fun i => (1 + ‖v‖) ^ 5 * B i)
    (fun R i => decayBound_translate (decayBound_cut ((hB i).mono (by norm_num)) R) v)
    (fun R => (1 + ‖v‖) ^ 5 * ((∑ i, B i) / ((R : ℝ) + 1)))
    (by
      have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (∑ i, B i)).const_mul
        ((1 + ‖v‖) ^ 5)
      rw [mul_zero, mul_zero] at h
      exact h.congr (fun R => by rw [mul_one_div]))
    (fun R i y => by
      have h1 := cut_sub_le (hB i) R (y - v)
      have h2 := one_add_norm_le_mul y v
      have h0 : 0 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      show (1 + ‖y‖) ^ 5 * |chi R (y - v) * (g i).1 (y - v) - (g i).1 (y - v)| ≤ _
      calc (1 + ‖y‖) ^ 5 * |chi R (y - v) * (g i).1 (y - v) - (g i).1 (y - v)|
          ≤ ((1 + ‖v‖) * (1 + ‖y - v‖)) ^ 5
              * |chi R (y - v) * (g i).1 (y - v) - (g i).1 (y - v)| :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 5) (abs_nonneg _)
        _ = (1 + ‖v‖) ^ 5 * ((1 + ‖y - v‖) ^ 5
              * |chi R (y - v) * (g i).1 (y - v) - (g i).1 (y - v)|) := by rw [mul_pow]; ring
        _ ≤ (1 + ‖v‖) ^ 5 * (B i / ((R : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1 hv
        _ ≤ (1 + ‖v‖) ^ 5 * ((∑ i, B i) / ((R : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
              (Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_univ i))
              (by positivity)) hv)
  have hS := tendsto_schwSFM hN W hD hpos ht hC0 hU O hO g
  have heq : ∀ R : ℕ, contSF hN (energy0 W D hD) (fun i => (O i, (cut (g i) R).translate v))
      = contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R)) := fun R =>
    contSF_energy0_translate_real hN W hD hpos hcube (fun i => (O i, cut (g i) R)) hO
      (fun i => uniformContinuous_cut (hg i) R) v
  exact tendsto_nhds_unique hT (hS.congr (fun R => (heq R).symm))

#print axioms schwSFM_translate

/-- **SO(4) on continuous decaying functions**: given `ObserverSO4` for the class `Φs` (from the
`pyth` hypothesis, `ObserverRotationDense.observerSO4_energy0`) and the class moments, for every
`A ∈ SO(4)` and fields in `D ∩ Φs`, `schwSFM O (g ∘ A) = schwSFM O g`. At each `R` the rotation
statement holds for the uniformly continuous `cut gᵢ R`; the rotated cut-offs approximate `gᵢ ∘ A`
within `4⁵ ‖gᵢ‖₆/(R + 1)`.

DERIVED: `4`, `5` from `decayBound_rotate`; `1` the shift; `0` the limit. -/
theorem schwSFM_rotate (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {Φs : Set (LField (MassGap.SUN.SU N))}
    (hSO4 : ObserverSO4 hN (energy0 W D hD) Φs) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ) {ι : Type} [Fintype ι]
    (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, O i ∈ D) (hOs : ∀ i, O i ∈ Φs)
    (g : ι → Decaying) (hg : ∀ i, Continuous (g i).1) :
    schwSFM hN W D hD O (fun i => decRot (g i) (transpose_mul_self_of_mem hA))
      = schwSFM hN W D hD O g := by
  have hAt := transpose_mul_self_of_mem hA
  have hex : ∀ i, ∃ B : ℝ, DecayBound 6 (g i).1 B := fun i => (g i).2
  choose B hB using hex
  have hB0 : ∀ i, 0 ≤ B i := fun i => (hB i).nonneg
  have h45 : (0 : ℝ) ≤ 4 ^ 5 := by norm_num
  have hT := tendsto_contSF_approx hN W hD hpos ht hC0 hU O hO
    (fun i => decRot (g i) hAt) (fun R i => rotTest A (cut (g i) R)) (fun i => 4 ^ 5 * B i)
    (fun R i y => by
      rw [rotTest_apply A hAt]
      exact decayBound_rotate (decayBound_cut ((hB i).mono (by norm_num)) R) hAt y)
    (fun R => 4 ^ 5 * ((∑ i, B i) / ((R : ℝ) + 1)))
    (by
      have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (∑ i, B i)).const_mul
        ((4 : ℝ) ^ 5)
      rw [mul_zero, mul_zero] at h
      exact h.congr (fun R => by rw [mul_one_div]))
    (fun R i y => by
      rw [rotTest_apply A hAt]
      have h1 := cut_sub_le (hB i) R (A.mulVec y)
      have h2 : 1 + ‖y‖ ≤ 4 * (1 + ‖A.mulVec y‖) := by
        linarith [norm_le_four_mul hAt y, norm_nonneg (A.mulVec y)]
      have h0 : 0 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      show (1 + ‖y‖) ^ 5 * |chi R (A.mulVec y) * (g i).1 (A.mulVec y) - (g i).1 (A.mulVec y)| ≤ _
      calc (1 + ‖y‖) ^ 5 * |chi R (A.mulVec y) * (g i).1 (A.mulVec y) - (g i).1 (A.mulVec y)|
          ≤ (4 * (1 + ‖A.mulVec y‖)) ^ 5
              * |chi R (A.mulVec y) * (g i).1 (A.mulVec y) - (g i).1 (A.mulVec y)| :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 5) (abs_nonneg _)
        _ = 4 ^ 5 * ((1 + ‖A.mulVec y‖) ^ 5
              * |chi R (A.mulVec y) * (g i).1 (A.mulVec y) - (g i).1 (A.mulVec y)|) := by
            rw [mul_pow]; ring
        _ ≤ 4 ^ 5 * (B i / ((R : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1 h45
        _ ≤ 4 ^ 5 * ((∑ i, B i) / ((R : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
              (Finset.single_le_sum (f := B) (fun i _ => hB0 i) (Finset.mem_univ i))
              (by positivity)) h45)
  have hS := tendsto_schwSFM hN W hD hpos ht hC0 hU O hO g
  have heq : ∀ R : ℕ, contSF hN (energy0 W D hD) (fun i => (O i, rotTest A (cut (g i) R)))
      = contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R)) := fun R =>
    hSO4 A hA ι (fun i => (O i, cut (g i) R)) hOs (fun i => uniformContinuous_cut (hg i) R)
  exact tendsto_nhds_unique hT (hS.congr (fun R => (heq R).symm))

#print axioms schwSFM_rotate

end Euclid

/-! ## 6. OS2 on decaying functions -/

section Positivity

variable {N : ℕ}

/-- **A monomial of decaying functions**: a finite family of fields with decaying test functions.

DERIVED: no numeral. -/
abbrev DMono (N : ℕ) : Type := Σ n : ℕ, (Fin n → LField (MassGap.SUN.SU N) × Decaying)

/-- Every decaying function of the monomial vanishes below the time `d`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def posAtD (τ : Fin 4) (d : ℝ) (P : DMono N) : Prop := ∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y τ

/-- **Margin monomials of decaying functions**: supported at times `≥ d` for some `d > max r 0`.

DERIVED: `0` the lower end of `d`. -/
abbrev DMarginMono (N : ℕ) (τ : Fin 4) (r : ℝ) : Type :=
  {P : DMono N // ∃ d : ℝ, 0 < d ∧ r < d ∧ posAtD τ d P}

/-- **The cut-off margin monomial**: the cut-off keeps the support.

DERIVED: `0` the vanishing value. -/
def cutM {τ : Fin 4} {r : ℝ} (R : ℕ) (P : DMarginMono N τ r) : MarginMono N τ r :=
  ⟨⟨P.1.1, fun i => ((P.1.2 i).1, cut (P.1.2 i).2 R)⟩, by
    obtain ⟨d, hd, hrd, hP⟩ := P.2
    exact ⟨d, hd, hrd, fun i y hy => hP i y (fun h0 => hy (by
      show chi R y * (P.1.2 i).2.1 y = 0
      rw [h0, mul_zero]))⟩⟩

/-- The fields of the reflected pair `θP ∪ Q`.

DERIVED: no numeral. -/
def pairFields (τ : Fin 4) (P Q : DMono N) : Fin P.1 ⊕ Fin Q.1 → LField (MassGap.SUN.SU N) :=
  Sum.elim (fun i => (P.2 i).1.refl τ) (fun j => (Q.2 j).1)

/-- The decaying functions of the reflected pair `θP ∪ Q`.

DERIVED: no numeral. -/
def pairFuns (τ : Fin 4) (P Q : DMono N) : Fin P.1 ⊕ Fin Q.1 → Decaying :=
  Sum.elim (fun i => decRefl τ (P.2 i).2) (fun j => (Q.2 j).2)

/-- **The reflected-pair kernel on decaying monomials**: `S(θP ∪ Q)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def kernS (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) (τ : Fin 4)
    (P Q : DMono N) : ℝ :=
  schwSFM hN W D hD (pairFields τ P Q) (pairFuns τ P Q)

/-- The reflected pair of cut-off monomials is the cut-off of the reflected pair (`chi` is reflection
invariant).

DERIVED: no numeral. -/
theorem pairFam_cutM {τ : Fin 4} {r : ℝ} (R : ℕ) (P Q : DMarginMono N τ r) :
    pairFam τ (cutM R P).1 (cutM R Q).1
      = fun x => (pairFields τ P.1 Q.1 x, cut (pairFuns τ P.1 Q.1 x) R) := by
  funext x
  cases x with
  | inl i =>
    refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
    show chi R (reflR τ y) * (P.1.2 i).2.1 (reflR τ y) = chi R y * (P.1.2 i).2.1 (reflR τ y)
    rw [chi_reflR]
  | inr j => rfl

#print axioms pairFam_cutM

/-- **Moving coefficients through a map of finite sets**: a Gram sum over `s` with the kernel read
through `φ` is the Gram sum over `φ(s)` with the fibre sums as coefficients.

DERIVED: no numeral. -/
theorem gram_image {α β : Type*} [DecidableEq β] (s : Finset α) (φ : α → β) (c : α → ℝ)
    (K : β → β → ℝ) :
    ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K (φ P) (φ Q)
      = ∑ M ∈ s.image φ, ∑ M' ∈ s.image φ,
          (∑ P ∈ s with φ P = M, c P) * (∑ Q ∈ s with φ Q = M', c Q) * K M M' := by
  have hmaps : ∀ P ∈ s, φ P ∈ s.image φ := fun P hP => Finset.mem_image_of_mem φ hP
  have key : ∀ M M', (∑ P ∈ s with φ P = M, c P) * (∑ Q ∈ s with φ Q = M', c Q) * K M M'
      = ∑ P ∈ s with φ P = M, ∑ Q ∈ s with φ Q = M', c P * c Q * K (φ P) (φ Q) := by
    intro M M'
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun P hP => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun Q hQ => ?_)
    rw [(Finset.mem_filter.mp hP).2, (Finset.mem_filter.mp hQ).2]
  symm
  calc ∑ M ∈ s.image φ, ∑ M' ∈ s.image φ,
        (∑ P ∈ s with φ P = M, c P) * (∑ Q ∈ s with φ Q = M', c Q) * K M M'
      = ∑ M ∈ s.image φ, ∑ M' ∈ s.image φ,
          ∑ P ∈ s with φ P = M, ∑ Q ∈ s with φ Q = M', c P * c Q * K (φ P) (φ Q) :=
        Finset.sum_congr rfl (fun M _ => Finset.sum_congr rfl (fun M' _ => key M M'))
    _ = ∑ M ∈ s.image φ, ∑ P ∈ s with φ P = M,
          ∑ M' ∈ s.image φ, ∑ Q ∈ s with φ Q = M', c P * c Q * K (φ P) (φ Q) :=
        Finset.sum_congr rfl (fun M _ => Finset.sum_comm)
    _ = ∑ M ∈ s.image φ, ∑ P ∈ s with φ P = M, ∑ Q ∈ s, c P * c Q * K (φ P) (φ Q) :=
        Finset.sum_congr rfl (fun M _ => Finset.sum_congr rfl (fun P _ =>
          Finset.sum_fiberwise_of_maps_to hmaps _))
    _ = ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K (φ P) (φ Q) :=
        Finset.sum_fiberwise_of_maps_to hmaps (fun P => ∑ Q ∈ s, c P * c Q * K (φ P) (φ Q))

#print axioms gram_image

/-- **OS2 on decaying functions**: given (E) in cube form on `D`, the class moments and a physical
range `r` for `energy0`, for every finite set of margin monomials of decaying functions and real
coefficients, `0 ≤ ∑_{P,Q} c_P c_Q S(θP ∪ Q)`. At each `R` the cut-off monomials are margin monomials
and `ContinuumFlow.contSF_gram_nonneg` applies (through `gram_image`); each kernel entry converges
(`tendsto_schwSFM`, `pairFam_cutM`); `[0, ∞)` is closed.

DERIVED: `0` the sign concluded and the excluded colour count; `4` in `Fin 4` is the spacetime
dimension. -/
theorem schwSFM_gram_nonneg (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0 W D hD).PhysRange r) (s : Finset (DMarginMono N τ r))
    (hs : ∀ P ∈ s, ∀ i, (P.1.2 i).1 ∈ D) (c : DMarginMono N τ r → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernS hN W D hD τ P.1 Q.1 := by
  classical
  have hB := uniformBoundF_energy0 hN W D hD hpos hcube
  have hpp := Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ
  have hfields : ∀ P ∈ s, ∀ Q ∈ s, ∀ x, pairFields τ P.1 Q.1 x ∈ D := by
    intro P hP Q hQ x
    cases x with
    | inl i => exact (hD τ _).mpr (hs P hP i)
    | inr j => exact hs Q hQ j
  have htend : Tendsto (fun R : ℕ => ∑ P ∈ s, ∑ Q ∈ s, c P * c Q
      * kernF hN (energy0 W D hD) τ (cutM R P).1 (cutM R Q).1) atTop
      (𝓝 (∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernS hN W D hD τ P.1 Q.1)) := by
    refine tendsto_finsetSum _ (fun P hP => tendsto_finsetSum _ (fun Q hQ => ?_))
    refine Tendsto.const_mul _ ?_
    have h := tendsto_schwSFM hN W hD hpos ht hC0 hU (pairFields τ P.1 Q.1)
      (hfields P hP Q hQ) (pairFuns τ P.1 Q.1)
    refine h.congr (fun R => ?_)
    show contSF hN (energy0 W D hD) (fun x => (pairFields τ P.1 Q.1 x, cut (pairFuns τ P.1 Q.1 x) R))
      = contSF hN (energy0 W D hD) (pairFam τ (cutM R P).1 (cutM R Q).1)
    rw [pairFam_cutM]
    rfl
  refine ge_of_tendsto' htend (fun R => ?_)
  rw [gram_image s (cutM R) c (fun M M' => kernF hN (energy0 W D hD) τ M.1 M'.1)]
  exact contSF_gram_nonneg hN (energy0 W D hD) hB τ hpp (s.image (cutM R))
    (fun M => ∑ P ∈ s with cutM R P = M, c P)

#print axioms schwSFM_gram_nonneg

end Positivity

/-! ## 7. OS1 and SO(4) for the Schwartz-class Schwinger functions -/

section Schwartz

variable {N : ℕ}

/-- DERIVED: `2` the Euclidean exponent. -/
theorem continuous_ofE4 (φ : MassGap.WightmanData.TestFn) : Continuous (ofE4 φ).1 :=
  φ.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ))

#print axioms continuous_ofE4

/-- The Euclidean translate is the coordinate translate.

DERIVED: `2` the Euclidean exponent. -/
theorem ofE4_translate (φ : MassGap.WightmanData.TestFn) (v : MassGap.WightmanData.E4) :
    ofE4 (SchwartzMap.compSubConstCLM ℝ v φ) = decTr (ofE4 φ) (WithLp.ofLp v) :=
  Subtype.ext (funext (fun y => by
    show φ (WithLp.toLp 2 y - v) = φ (WithLp.toLp 2 (y - WithLp.ofLp v))
    rw [WithLp.toLp_sub, WithLp.toLp_ofLp]))

#print axioms ofE4_translate

/-- **OS1 on `𝓢(E4, ℝ)`**: for one field `O ∈ D`, `S_n(φ₁(· − v), …, φₙ(· − v)) = S_n(φ)` for every
real `v ∈ E4` (`schwSFM_translate`, `schwSF_eq_schwSFM`).

DERIVED: `2` the Euclidean exponent; `4` in `Fin 4` the spacetime dimension. -/
theorem schwCML_translate (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) {O : LField (MassGap.SUN.SU N)}
    (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (n : ℕ)
    (φ : Fin n → MassGap.WightmanData.TestFn) (v : MassGap.WightmanData.E4) :
    schwCML hN W hD hpos hO h n (fun i => SchwartzMap.compSubConstCLM ℝ v (φ i))
      = schwCML hN W hD hpos hO h n φ := by
  rw [schwCML_apply, schwCML_apply, schwSF_eq_schwSFM hN W hD hpos ht hC0 hU hO,
    schwSF_eq_schwSFM hN W hD hpos ht hC0 hU hO]
  simp only [ofE4_translate]
  exact schwSFM_translate hN W hD hpos hcube ht hC0 hU (fun _ => O) (fun _ => hO)
    (fun i => ofE4 (φ i)) (fun i => continuous_ofE4 (φ i)) (WithLp.ofLp v)

#print axioms schwCML_translate

/-- **SO(4) on `𝓢(E4, ℝ)`, in coordinates**: for one field `O ∈ D ∩ Φs` with `ObserverSO4` on `Φs`,
the Schwinger functions of `φᵢ ∘ toLp ∘ A` equal those of `φᵢ ∘ toLp` for `A ∈ SO(4)`
(`schwSFM_rotate`, `schwSF_eq_schwSFM`).

DERIVED: `4` the dimension. -/
theorem schwCML_rotate (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {Φs : Set (LField (MassGap.SUN.SU N))}
    (hSO4 : ObserverSO4 hN (energy0 W D hD) Φs) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ) {O : LField (MassGap.SUN.SU N)}
    (hO : O ∈ D) (hOs : O ∈ Φs) (h : UnitCubeExpBound hN W O) (n : ℕ)
    (φ : Fin n → MassGap.WightmanData.TestFn) :
    schwSF hN W D hD O (fun i => decRot (ofE4 (φ i)) (transpose_mul_self_of_mem hA))
      = schwCML hN W hD hpos hO h n φ := by
  rw [schwCML_apply, schwSF_eq_schwSFM hN W hD hpos ht hC0 hU hO,
    schwSF_eq_schwSFM hN W hD hpos ht hC0 hU hO]
  exact schwSFM_rotate hN W hD hpos ht hC0 hU hSO4 hA (fun _ => O) (fun _ => hO) (fun _ => hOs)
    (fun i => ofE4 (φ i)) (fun i => continuous_ofE4 (φ i))

#print axioms schwCML_rotate

end Schwartz

end MassGap.ObserverOSEuclidS
