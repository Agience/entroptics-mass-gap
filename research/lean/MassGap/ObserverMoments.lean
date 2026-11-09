import Mathlib
import MassGap.ClayFull

/-!
# MassGap.ObserverMoments — the observer's moment inputs: what compactness gives, and what it does not

`ClayFull.clayFullAt_of_observer` takes three moment inputs for the observer's energy density:
`CubeMomentBound` on `PlaqClass N`, `ClassMoments t C` on `SymPlaqClass N`, and `UnitCubeExpBound`
for one field of the class. Each is a bound on the moments of the **cube energy**
`cubeSum a_k R (O ∘ V_k) = ∑_{a_k x ∈ [-R, R]⁴} O(V_k U ∘ T_x)`, eventually in the step `k`, with
one constant for all large `k`.

## Compactness

`SU(N)` is compact, so every local field is bounded by its sup norm, and so is its reading through
any configuration map. That bounds each term of the cube energy, and the number of terms is the
number of lattice sites in the physical cube, about `(2R/a_k)⁴`. `state_cubeSum_pow_le_norm` is the
whole of what compactness gives:

  `ν_k(E^{2p}) ≤ (‖O‖ (2R + 3)⁴ / a_k⁴)^{2p}`,

which grows like `a_k^{-8p}`. The cube energy is an unweighted site sum: the canonical factor `a⁻⁴`
of the scaled field and the cell volume `a⁴` of the smearing have cancelled
(`ObserverEnergyBox.smear_scaled_apply`), so no normalisation is left to absorb the count.

## The inputs are not compactness statements

`not_cubeMomentBound_of_mean_ge`: if the one-site mean `ν_k(O ∘ V_k)` of a non-negative field stays
above some `m > 0`, `CubeMomentBound` fails. The unit cube holds at least `1/a_k` sites, so its energy
has mean at least `m / a_k → ∞`. The same holds for `UnitCubeExpBound` and for `ClassMoments`
(`not_unitCubeExpBound_of_mean_ge`, `not_classMoments_of_mean_ge`). Each input therefore asserts
that the observer's smoothed reading vanishes in the continuum limit, at the rate of the cell volume
(the `a_k⁴` rate is the one `CubeMomentBound` gives).
For the plaquette of the flowed configuration that is the statement that the flowed energy density,
in lattice units, is `a⁴` times a finite physical density: the UV finiteness of the flow at a fixed
physical flow range, as a bound on moments under the Wilson states. A sup-norm bound does not reach
it, and neither does the flow kernel being an average: an average of plaquettes is at most `2` per
site, and the loss is the site count, not the size per site.

## The three inputs from one

`ClassUnitExp hN W D t C`: one exponential moment of the unit-cube energy, eventually in the step, with
one `t > 0`, `C` for every field of `D`. On a non-negative class it gives `ClassMoments hN W D t |C|`
(`classMoments_of_classUnitExp`), `CubeMomentBound` for every field (`cubeMomentBound_of_classUnitExp`)
and `UnitCubeExpBound` for every field (`unitCubeExpBound_of_classUnitExp`). On
`PlaqClass N ∪ SymPlaqClass N` it gives all three inputs of `clayFullAt_of_observer`
(`observer_moment_inputs_of_classUnitExp`), and `clayFullAt_of_classUnitExp` is that theorem with the
three replaced by it.

`DensityVolumeBound W D K`: eventually in the step, `|O ∘ V_k| ≤ K a_k⁴` pointwise for every field of
`D`. It gives `ClassUnitExp hN W D 1 (e^{625 K})` (`classUnitExp_of_density`): a sup bound at the scale
of the cell volume is the form of compactness that would suffice. Whether a given observer satisfies
it is a property of its configuration map, not of `SU(N)`.
-/

noncomputable section

namespace MassGap.ObserverMoments

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ContinuumHypercubic
  MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered
  MassGap.ObserverEnergyBox MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS
  MassGap.ObserverOSLinked MassGap.ObserverRotation MassGap.ObserverSymField
  MassGap.ContinuumTimeGroup MassGap.ClayFull Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Compactness -/

section Compact

/-- **Every observable is bounded by its sup norm**: `Cfg N` is compact.

DERIVED: no numeral. -/
theorem abs_apply_le_norm (F : C(Cfg N, ℝ)) (U : Cfg N) : |F U| ≤ ‖F‖ := by
  rw [← Real.norm_eq_abs]
  exact F.norm_coe_le_norm U

#print axioms abs_apply_le_norm

/-- **A pointwise bound is a bound on the state**: `G ≤ c` gives `ν(G) ≤ c`.

DERIVED: `1` the unit observable. -/
theorem state_le_of_le (ν : MassGap.DLRLimit.State (Cfg N)) (G : C(Cfg N, ℝ)) {c : ℝ}
    (h : ∀ U, G U ≤ c) : ν G ≤ c := by
  have hm : ν G ≤ ν (c • (1 : C(Cfg N, ℝ))) := ν.mono (fun U => by
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact h U)
  rw [ν.map_smul, ν.map_one] at hm
  simpa using hm

#print axioms state_le_of_le

/-- **The cube energy of a bounded reading is bounded by its site count**: for `|F| ≤ B`, `R ≥ 0`
and `0 < a ≤ 1`, `|cubeSum a R F| ≤ B (2R + 3)⁴ / a⁴` (`sum_cubeInd_le`).

DERIVED: `2`, `3`, `4` are `sum_cubeInd_le`'s; `1` the spacing bound; `0` the signs. -/
theorem abs_cubeSum_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (F : C(Cfg N, ℝ)) {B : ℝ} (hB : ∀ U, |F U| ≤ B) (U : Cfg N) :
    |cubeSum a R F U| ≤ B * ((2 * R + 3) ^ 4 / a ^ 4) := by
  rw [cubeSum_apply]
  have hI := sum_cubeInd_le ha ha1 hR
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB U)
  calc |∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)|
      ≤ ∑ x ∈ box ⌈R / a⌉₊, |cubeInd R (site a x) * F (transConf x U)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ box ⌈R / a⌉₊, B * cubeInd R (site a x) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (cubeInd_nonneg _ _), mul_comm B]
        exact mul_le_mul_of_nonneg_left (hB _) (cubeInd_nonneg _ _)
    _ = B * ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) := (Finset.mul_sum _ _ _).symm
    _ ≤ B * ((2 * R + 3) ^ 4 / a ^ 4) := mul_le_mul_of_nonneg_left hI hB0

#print axioms abs_cubeSum_le

/-- **What compactness gives the cube moments**: in every state,
`ν(cubeSum a R F ^ {2p}) ≤ (‖F‖ (2R + 3)⁴ / a⁴)^{2p}`, a bound that grows like `a^{-8p}`.

DERIVED: `2` makes the power even; `3`, `4` are `abs_cubeSum_le`'s; `1` the spacing bound. -/
theorem state_cubeSum_pow_le_norm (ν : MassGap.DLRLimit.State (Cfg N)) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) {R : ℝ} (hR : 0 ≤ R) (F : C(Cfg N, ℝ)) (p : ℕ) :
    ν (cubeSum a R F ^ (2 * p)) ≤ (‖F‖ * ((2 * R + 3) ^ 4 / a ^ 4)) ^ (2 * p) := by
  refine state_le_of_le ν _ (fun U => ?_)
  rw [ContinuousMap.pow_apply, ← (even_two_mul p).pow_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_cubeSum_le ha ha1 hR F (abs_apply_le_norm F) U) _

#print axioms state_cubeSum_pow_le_norm

/-- **The compactness bound for the observer**: at every step with `a_k ≤ 1`, the cube moments of
`O ∘ V_k` are at most `(‖O‖ (2R + 3)⁴ / a_k⁴)^{2p}`, whatever the configuration map.

DERIVED: `0` is the excluded colour count; `2`, `3`, `4`, `1` as in `abs_cubeSum_le`. -/
theorem observer_cubeMoment_le_norm (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N))
    (k : ℕ) (hk1 : dySpacing N k ≤ 1) {R : ℝ} (hR : 0 ≤ R) (p : ℕ) :
    stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))
      ≤ (‖O.1‖ * ((2 * R + 3) ^ 4 / dySpacing N k ^ 4)) ^ (2 * p) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  refine state_le_of_le _ _ (fun U => ?_)
  rw [ContinuousMap.pow_apply, ← (even_two_mul p).pow_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_cubeSum_le ha hk1 hR _ (fun V => abs_apply_le_norm O.1 (W.V k V)) U) _

#print axioms observer_cubeMoment_le_norm

end Compact

/-! ## 2. The inputs ask for a vanishing mean -/

section NoGo

/-- **The box energy's mean is the box's site count times one reading's mean** (translation
invariance, `ContinuumNontrivial.stateK_transObs`).

DERIVED: `2`, `1`, `4` are `card_box`'s count. -/
theorem state_boxSum (hN : N ≠ 0) (k K : ℕ) (F : C(Cfg N, ℝ)) :
    stateK hN k (boxSum K F) = ((2 * (K : ℝ) + 1) ^ 4) * stateK hN k F := by
  unfold boxSum
  rw [(stateK hN k).map_sum]
  simp only [MassGap.ContinuumNontrivial.stateK_transObs, Finset.sum_const, card_box,
    nsmul_eq_mul]
  push_cast
  ring

#print axioms state_boxSum

/-- **The unit cube's energy has mean at least `m / a`** when one reading has mean at least `m`:
the unit cube contains the box of side `2⌊1/a⌋ + 1 > 1/a` (`boxSum_le_cubeSum`).

DERIVED: `0` the signs; `1` the unit cube; `2`, `4` the box count. -/
theorem div_mul_le_state_cubeSum (hN : N ≠ 0) (k : ℕ) {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) {m : ℝ} (hm : 0 ≤ m) (hmF : m ≤ stateK hN k F) :
    1 / a * m ≤ stateK hN k (cubeSum a 1 F) := by
  have h2 : stateK hN k (boxSum ⌊1 / a⌋₊ F) ≤ stateK hN k (cubeSum a 1 F) :=
    (stateK hN k).mono (fun U => boxSum_le_cubeSum ha zero_le_one F hF U)
  rw [state_boxSum] at h2
  have hl : 1 / a < (⌊1 / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl0 : (0 : ℝ) ≤ (⌊1 / a⌋₊ : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ 2 * (⌊1 / a⌋₊ : ℝ) + 1 := by linarith
  have hp : 2 * (⌊1 / a⌋₊ : ℝ) + 1 ≤ (2 * (⌊1 / a⌋₊ : ℝ) + 1) ^ 4 := le_self_pow₀ h1 (by norm_num)
  have hcount : 1 / a ≤ (2 * (⌊1 / a⌋₊ : ℝ) + 1) ^ 4 := by linarith
  calc 1 / a * m ≤ (2 * (⌊1 / a⌋₊ : ℝ) + 1) ^ 4 * stateK hN k F :=
        mul_le_mul hcount hmF hm (by positivity)
    _ ≤ stateK hN k (cubeSum a 1 F) := h2

#print axioms div_mul_le_state_cubeSum

/-- **No bound on the unit cube's second moment once one reading's mean stays positive.** For a
non-negative field `O` with `ν_k(O ∘ V_k) ≥ m > 0` eventually, no `C` bounds
`ν_k(E_1²)` eventually, `E_1 = cubeSum a_k 1 (O ∘ V_k)`: `E ≤ (E² + 1)/2` and the mean of `E_1` is at
least `m / a_k → ∞`.

DERIVED: `0` the signs and the excluded colour count; `1` the unit cube and the unit observable; `2`
the square and the halving. -/
theorem not_unitSecondMoment_of_mean_ge (hN : N ≠ 0) (W : ConfFlow N)
    {O : LField (MassGap.SUN.SU N)} (hO : ∀ U, 0 ≤ O.1 U) {m : ℝ} (hm : 0 < m)
    (hmean : ∀ᶠ k in atTop, m ≤ stateK hN k (W.fieldMap k O).1) (C : ℝ) :
    ¬ ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) 1 (W.fieldMap k O).1 ^ (2 * 1)) ≤ C := by
  intro hC
  have hε : 0 < 2 * m / (|C| + 2) := by positivity
  have hsmall : ∀ᶠ k in atTop, dySpacing N k < 2 * m / (|C| + 2) :=
    (tendsto_dySpacing N).eventually (gt_mem_nhds hε)
  obtain ⟨k, hCk, hmk, hak⟩ := (hC.and (hmean.and hsmall)).exists
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hO (W.V k U)
  have h1 : stateK hN k (cubeSum (dySpacing N k) 1 (W.fieldMap k O).1) ≤ (C + 1) / 2 := by
    have hle : stateK hN k (cubeSum (dySpacing N k) 1 (W.fieldMap k O).1)
        ≤ stateK hN k ((1 / 2 : ℝ) • (cubeSum (dySpacing N k) 1 (W.fieldMap k O).1 ^ (2 * 1))
          + (1 / 2 : ℝ) • (1 : C(Cfg N, ℝ))) :=
      (stateK hN k).mono (fun U => by
        simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.pow_apply,
          ContinuousMap.one_apply, smul_eq_mul]
        nlinarith [sq_nonneg (cubeSum (dySpacing N k) 1 (W.fieldMap k O).1 U - 1)])
    rw [(stateK hN k).map_add, (stateK hN k).map_smul, (stateK hN k).map_smul,
      (stateK hN k).map_one] at hle
    linarith
  have h3 := div_mul_le_state_cubeSum hN k ha _ hF hm.le hmk
  have hC2 : 0 < |C| + 2 := by positivity
  have h4 : dySpacing N k * (|C| + 2) < 2 * m := (lt_div_iff₀ hC2).mp hak
  have h5 : (|C| + 2) / 2 < 1 / dySpacing N k * m := by
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ ha]
    linarith
  linarith [le_abs_self C]

#print axioms not_unitSecondMoment_of_mean_ge

/-- **`CubeMomentBound` fails once one reading's mean stays positive.**

DERIVED: `0` the signs and the lower end of `R`; `1` the unit cube and the moment. -/
theorem not_cubeMomentBound_of_mean_ge (hN : N ≠ 0) (W : ConfFlow N)
    {O : LField (MassGap.SUN.SU N)} (hO : ∀ U, 0 ≤ O.1 U) {m : ℝ} (hm : 0 < m)
    (hmean : ∀ᶠ k in atTop, m ≤ stateK hN k (W.fieldMap k O).1) : ¬ CubeMomentBound hN W O := by
  intro h
  obtain ⟨C, hC⟩ := h 1 zero_le_one 1
  exact not_unitSecondMoment_of_mean_ge hN W hO hm hmean C hC

#print axioms not_cubeMomentBound_of_mean_ge

/-- **`UnitCubeExpBound` fails once one reading's mean stays positive** (`cubeMomentBound_of_exp`'s
step `x² ≤ 2! t⁻² e^{tx}` at the unit cube).

DERIVED: `0` the signs; `1` the unit cube; `2` the moment. -/
theorem not_unitCubeExpBound_of_mean_ge (hN : N ≠ 0) (W : ConfFlow N)
    {O : LField (MassGap.SUN.SU N)} (hO : ∀ U, 0 ≤ O.1 U) {m : ℝ} (hm : 0 < m)
    (hmean : ∀ᶠ k in atTop, m ≤ stateK hN k (W.fieldMap k O).1) : ¬ UnitCubeExpBound hN W O := by
  rintro ⟨t, C, ht, hC⟩
  refine not_unitSecondMoment_of_mean_ge hN W hO hm hmean
    (((2 * 1).factorial : ℝ) / t ^ (2 * 1) * C) ?_
  filter_upwards [hC] with k hk
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hO (W.V k U)
  exact (state_pow_le_exp (stateK hN k) _ (cubeSum_nonneg _ _ hF) ht (2 * 1)).trans
    (mul_le_mul_of_nonneg_left hk (div_nonneg (by positivity) (pow_pos ht _).le))

#print axioms not_unitCubeExpBound_of_mean_ge

/-- **`CubeMomentsAt` gives `CubeMomentBound`**: fix the cube and the moment.

DERIVED: no numeral of its own. -/
theorem cubeMomentBound_of_cubeMomentsAt (hN : N ≠ 0) (W : ConfFlow N)
    {O : LField (MassGap.SUN.SU N)} {t C : ℝ} (h : CubeMomentsAt hN W O t C) :
    CubeMomentBound hN W O :=
  fun R hR p => ⟨_, h.mono fun _ hk => hk R hR p⟩

#print axioms cubeMomentBound_of_cubeMomentsAt

/-- **`ClassMoments` fails at a field of the class whose reading's mean stays positive.**

DERIVED: `0` the signs. -/
theorem not_classMoments_of_mean_ge (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} {O : LField (MassGap.SUN.SU N)} (hOD : O ∈ D)
    (hO : ∀ U, 0 ≤ O.1 U) {m : ℝ} (hm : 0 < m)
    (hmean : ∀ᶠ k in atTop, m ≤ stateK hN k (W.fieldMap k O).1) (t C : ℝ) :
    ¬ ClassMoments hN W D t C := fun h =>
  not_cubeMomentBound_of_mean_ge hN W hO hm hmean (cubeMomentBound_of_cubeMomentsAt hN W (h O hOD))

#print axioms not_classMoments_of_mean_ge

end NoGo

/-! ## 3. The three inputs from one exponential moment, uniform over the class -/

section OneInput

/-- **One exponential moment of the unit-cube energy, uniformly over a class**: one `t`, `C` with,
eventually in the step, `ν_k(e^{t E_1}) ≤ C` for every field of `D`, `E_1 = cubeSum a_k 1 (O ∘ V_k)`.

DERIVED: `1` the unit cube. -/
def ClassUnitExp (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (t C : ℝ) :
    Prop :=
  ∀ᶠ k in atTop, ∀ O ∈ D,
    stateK hN k (expC (t • cubeSum (dySpacing N k) 1 (W.fieldMap k O).1)) ≤ C

/-- `ClassUnitExp` passes to a subclass.

DERIVED: no numeral. -/
theorem classUnitExp_mono {hN : N ≠ 0} {W : ConfFlow N} {D D' : Set (LField (MassGap.SUN.SU N))}
    {t C : ℝ} (h : ClassUnitExp hN W D t C) (hDD : D' ⊆ D) : ClassUnitExp hN W D' t C :=
  Filter.Eventually.mono h fun _ hk O hO => hk O (hDD hO)

#print axioms classUnitExp_mono

/-- **`UnitCubeExpBound` at every field of the class.**

DERIVED: `0` the lower end of `t`. -/
theorem unitCubeExpBound_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} {t C : ℝ} (ht : 0 < t) (h : ClassUnitExp hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) : UnitCubeExpBound hN W O :=
  ⟨t, C, ht, Filter.Eventually.mono h fun _ hk => hk O hO⟩

#print axioms unitCubeExpBound_of_classUnitExp

/-- **`CubeMomentsAt t |C|` at every non-negative field of the class**: the cube of side `2R` by the
covering `state_cubeSum_pow_le`, the moment by `state_pow_le_exp`.

DERIVED: `0` the excluded colour count and the signs; `1`, `2`, `4` as in `state_cubeSum_pow_le`. -/
theorem cubeMomentsAt_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t)
    (h : ClassUnitExp hN W D t C) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) :
    CubeMomentsAt hN W O t |C| := by
  filter_upwards [h] with k hk
  intro R hR p
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  refine (state_cubeSum_pow_le hN k ha hR _ hF p).trans
    (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (pow_nonneg (by linarith) 4) _))
  exact (state_pow_le_exp (stateK hN k) _ (cubeSum_nonneg _ _ hF) ht (2 * p)).trans
    (mul_le_mul_of_nonneg_left ((hk O hO).trans (le_abs_self C))
      (div_nonneg (by positivity) (pow_pos ht _).le))

#print axioms cubeMomentsAt_of_classUnitExp

/-- **`ClassMoments t |C|` on a non-negative class.**

DERIVED: `0` the signs. -/
theorem classMoments_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t)
    (h : ClassUnitExp hN W D t C) : ClassMoments hN W D t |C| :=
  fun _ hO => cubeMomentsAt_of_classUnitExp hN W hpos ht h hO

#print axioms classMoments_of_classUnitExp

/-- **`CubeMomentBound` at every field of a non-negative class.**

DERIVED: `0` the signs. -/
theorem cubeMomentBound_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t)
    (h : ClassUnitExp hN W D t C) : ∀ O ∈ D, CubeMomentBound hN W O :=
  fun _ hO => cubeMomentBound_of_cubeMomentsAt hN W (cubeMomentsAt_of_classUnitExp hN W hpos ht h hO)

#print axioms cubeMomentBound_of_classUnitExp

/-- The plaquette class and the symmetrised class are non-negative.

DERIVED: `0` the sign. -/
theorem plaqSym_nonneg (hN : N ≠ 0) : ∀ O ∈ PlaqClass N ∪ SymPlaqClass N, ∀ U, 0 ≤ O.1 U := by
  rintro O (hO | hO)
  · exact plaqClass_nonneg hN O hO
  · exact symPlaq_nonneg hN O hO

/-- **`CubeMomentBound` on `PlaqClass N` from `ClassUnitExp` on the two classes.**

DERIVED: `0` the lower end of `t`. -/
theorem plaqCube_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (h : ClassUnitExp hN W (PlaqClass N ∪ SymPlaqClass N) t C) :
    ∀ O ∈ PlaqClass N, CubeMomentBound hN W O :=
  cubeMomentBound_of_classUnitExp hN W (fun O hO => plaqClass_nonneg hN O hO) ht
    (classUnitExp_mono h Set.subset_union_left)

#print axioms plaqCube_of_classUnitExp

/-- **`ClassMoments t |C|` on `SymPlaqClass N` from `ClassUnitExp` on the two classes.**

DERIVED: `0` the lower end of `t`. -/
theorem symMoments_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (h : ClassUnitExp hN W (PlaqClass N ∪ SymPlaqClass N) t C) :
    ClassMoments hN W (SymPlaqClass N) t |C| :=
  classMoments_of_classUnitExp hN W (symPlaq_nonneg hN) ht (classUnitExp_mono h Set.subset_union_right)

#print axioms symMoments_of_classUnitExp

/-- **The three moment inputs of `clayFullAt_of_observer` from one.** `ClassUnitExp` on
`PlaqClass N ∪ SymPlaqClass N` gives `CubeMomentBound` on `PlaqClass N`, `ClassMoments t |C|` on
`SymPlaqClass N`, and `UnitCubeExpBound` at every field of `SymPlaqClass N`.

DERIVED: `0` the lower end of `t`. -/
theorem observer_moment_inputs_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (ht : 0 < t) (h : ClassUnitExp hN W (PlaqClass N ∪ SymPlaqClass N) t C) :
    (∀ O ∈ PlaqClass N, CubeMomentBound hN W O) ∧ ClassMoments hN W (SymPlaqClass N) t |C|
      ∧ ∀ O ∈ SymPlaqClass N, UnitCubeExpBound hN W O :=
  ⟨plaqCube_of_classUnitExp hN W ht h, symMoments_of_classUnitExp hN W ht h,
    fun _ hO => unitCubeExpBound_of_classUnitExp hN W ht h (Set.mem_union_right _ hO)⟩

#print axioms observer_moment_inputs_of_classUnitExp

/-- **`clayFullAt_of_observer` with its three moment inputs replaced by `ClassUnitExp`** on
`PlaqClass N ∪ SymPlaqClass N`. The remaining inputs are those of `clayFullAt_of_observer`, stated at
the moment inputs that `ClassUnitExp` supplies.

DERIVED: `0` the signs and the excluded colour count; `1` the top of `ρ`; `4` in `Fin 4` the
dimension. -/
theorem clayFullAt_of_classUnitExp (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    {t C : ℝ} (ht : 0 < t) (hE : ClassUnitExp hN W (PlaqClass N ∪ SymPlaqClass N) t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ SymPlaqClass N)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW (plaqCube_of_classUnitExp hN W ht hE))) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) τ r)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F)
    (hNG : NonGaussian (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW (plaqCube_of_classUnitExp hN W ht hE)) ht (abs_nonneg C)
      (symMoments_of_classUnitExp hN W ht hE) hO
      (unitCubeExpBound_of_classUnitExp hN W ht hE (Set.mem_union_right _ hO))
      τ hphys m0 hL hρ0 hρ1 hg hNT))
    (hLL : LocalLink hN (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW (plaqCube_of_classUnitExp hN W ht hE)) ht (abs_nonneg C)
      (symMoments_of_classUnitExp hN W ht hE) hO
      (unitCubeExpBound_of_classUnitExp hN W ht hE (Set.mem_union_right _ hO))
      τ hphys m0 hL hρ0 hρ1 hg hNT))
    (hOS2Z : OS2Zero (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW (plaqCube_of_classUnitExp hN W ht hE)) ht (abs_nonneg C)
      (symMoments_of_classUnitExp hN W ht hE) hO
      (unitCubeExpBound_of_classUnitExp hN W ht hE (Set.mem_union_right _ hO))
      τ hphys m0 hL hρ0 hρ1 hg hNT))
    (hdense : Dense (Set.range (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW (plaqCube_of_classUnitExp hN W ht hE)) ht (abs_nonneg C)
      (symMoments_of_classUnitExp hN W ht hE) hO
      (unitCubeExpBound_of_classUnitExp hN W ht hE (Set.mem_union_right _ hO))
      τ hphys m0 hL hρ0 hρ1 hg hNT).cvec)) :
    ClayFullAt hN W (SymPlaqClass N) (symPlaq_refl N) :=
  clayFullAt_of_observer hN W hW (plaqCube_of_classUnitExp hN W ht hE) ht (abs_nonneg C)
    (symMoments_of_classUnitExp hN W ht hE) hO
    (unitCubeExpBound_of_classUnitExp hN W ht hE (Set.mem_union_right _ hO)) τ hphys m0 hL hρ0 hρ1
    hg hNT hpyth hNG hLL hOS2Z hdense

#print axioms clayFullAt_of_classUnitExp

end OneInput

/-! ## 4. A sup bound at the scale of the cell volume -/

section Density

/-- **The observer's reading is of the order of the cell volume, pointwise**: eventually in the step,
`|O ∘ V_k| ≤ K a_k⁴` everywhere, for every field of `D`.

DERIVED: `4` is the canonical dimension. -/
def DensityVolumeBound (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (K : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ O ∈ D, ∀ U, |(W.fieldMap k O).1 U| ≤ K * dySpacing N k ^ 4

/-- **`ClassUnitExp` from a sup bound at the scale of the cell volume**: the unit-cube energy is at
most `K a⁴ · 5⁴/a⁴ = 625 K` (`abs_cubeSum_le` at `R = 1`), so `ν_k(e^{E_1}) ≤ e^{625 K}`.

DERIVED: `0` the excluded colour count; `1` the unit cube, the spacing bound and `t`; `2`, `3`, `4`
are `abs_cubeSum_le`'s. -/
theorem classUnitExp_of_density (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} {K : ℝ} (h : DensityVolumeBound W D K) :
    ClassUnitExp hN W D 1 (Real.exp (K * (2 * 1 + 3) ^ 4)) := by
  filter_upwards [h, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1 O hO
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  refine state_le_of_le _ _ (fun U => ?_)
  rw [expC_apply, ContinuousMap.smul_apply, one_smul]
  refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
  have hb := abs_cubeSum_le ha hk1.le zero_le_one _ (hk O hO) U
  have e : K * dySpacing N k ^ 4 * ((2 * 1 + 3) ^ 4 / dySpacing N k ^ 4) = K * (2 * 1 + 3) ^ 4 := by
    field_simp
  linarith

#print axioms classUnitExp_of_density

end Density

end MassGap.ObserverMoments

end
