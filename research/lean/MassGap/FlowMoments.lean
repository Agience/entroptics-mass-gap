import Mathlib
import MassGap.FlowUV

/-!
# MassGap.FlowMoments — what `ClassMoments` asks of a flow, and where it fails

`ClaySUFinal.clayStatementAt_SU_final` takes `hU : ClassMoments hN W (SymPlaqClass N) t C`, and the
capstone of `ClayData` takes it together with `hreach : a_k · W.range k → 0`. This module proves the
rate that `hU` forces on the flowed plaquette mean, for every configuration flow, and the failure of
`hU` for the identity flow given a floor on the Wilson plaquette mean.

## The rate `hU` forces (proved, every flow)

`classMoments_mean_le`: for a non-negative field `O` of the class, `ClassMoments hN W D t C` gives,
eventually in the step,

  `ν_k(O ∘ V_k) ≤ ((3⁴)² · 2 C / t² + 1) / 2 · a_k⁴`.

The unit cube holds the box of side `2⌊1/a⌋ + 1 ≥ 1/a`, so `(1/a⁴) ν_k(O ∘ V_k)` is at most the
mean of the unit-cube energy `E_1` (`inv_pow_mul_le_state_cubeSum`), and the second moment of `E_1`
at `R = 1`, `p = 1` bounds that mean through `E ≤ (E² + 1)/2`. This sharpens
`ObserverMoments.not_classMoments_of_mean_ge` (a mean bounded below by a constant) to a mean bounded
below at any rate faster than `a_k⁴`: `not_classMoments_of_rate`.

So `hU` asserts that the flowed plaquette density, in physical units `a_k⁻⁴ ν_k(O ∘ V_k)`, has a
bounded mean. It is the same rate as `FlowUV.siteExp_mean_le`, now read off `ClassMoments` itself.

## The identity flow (proved, given a plaquette floor)

`not_classMoments_identity`: if the Wilson plaquette mean has a floor
`ν_k(1 − Re tr U_q / N) ≥ c e^{−λ β_k}` with `c > 0` and `λ < 96π² / (11 N²)`, then
`ClassMoments hN (ConfFlow.identity N) (SymPlaqClass N) t C` fails at every `t`, `C`. The exponent
`96π²/(11N²)` is the rate of `a⁴ = aRun N β⁴` (`tendsto_expFloor_div_aRun`): `aRun N β` is
`(48π²β/(11N²))^{51/121} e^{−24π²β/(11N²)}`. The identity flow has vanishing reach
(`identity_reach`), so it meets `hreach` and fails `hU`.

The floor is not proved in this module. The variance floor
`PeriodicContent.periodicState_var_iplaqObs_ge`, `e^{−128β}`, gives a mean floor
`e^{−128β} varReTr N / (2N²)` (the density lies in `[0, 2]`); `128` exceeds `96π²/(11N²)` (`21.5` at
`N = 2`) at every `N ≥ 2`, so it does not reach the rate. A polynomial floor meets the hypothesis at
every `λ > 0`: `PlaquetteFloor.stateK_plaq_ge` proves `ν_k(1 − Re tr U_q/N) ≥ c β_k^{−2}` for
`N ≥ 2`, and `PlaquetteFloor.not_classMoments_identity` is this theorem without the floor
hypothesis (through `ExistenceFlow.not_classMoments_identity_poly`).

## `hU` together with `hreach` (argued, not formalised)

`classMoments_mean_le` holds for every flow. For a smoothing flow of physical range `r_k = a_k ·
range_k`, the flowed plaquette density in physical units is the flowed energy density at flow time
`≈ r_k²`, and its mean grows like `g²(r_k)/r_k⁴` as `r_k → 0` (the leading small-flow-time behaviour
of the energy density, with the running coupling at scale `r_k`, which falls only logarithmically).
Under `hreach` that diverges, and `classMoments_mean_le` bounds it. The class is non-negative, so no
subtraction removes the identity-operator part `∝ r_k⁻⁴`; even with it removed, the integrated
energy density over the unit cube has variance `∫∫ ⟨T(x)T(y)⟩` with `⟨T T⟩ ∼ |x − y|⁻⁸`, which is not
integrable at coincident points. So for a translation-covariant smoothing flow in the Wilson theory
`hU` and `hreach` are not expected to hold together (argued, not a declaration). `ConfFlow` does not
require translation covariance, and a flow that flattens every plaquette inside a box of growing
lattice size meets both (sketched, not formalised); `cubeSum` then reads `O(V_k(T_x U))`, not the
flowed field at `x`. `ReachBlowup hN W D` names the property that encodes the covariant case (vanishing reach makes the
physical mean of some field of the class unbounded), and `not_classMoments_of_reachBlowup` is the
resulting incompatibility; `ReachBlowup` is not proved for any flow here.

At a fixed physical range `r > 0` (`range_k ≈ r/a_k`, `PhysRange r` but not `hreach`) the flowed
density is the energy density at fixed flow time, and `FlowUV.SiteExp` at some `s > 0` is its UV
finiteness in exponential form; `FlowUV` records the free-field threshold `s < 128π²τ²`. Its proof
for the Wilson measure is a weak-coupling small-field / large-field statement uniform in the zoom,
and none of the proved inputs reaches it: Haar moments are coupling-zero facts, the variance floors
are lower bounds, reflection positivity gives chessboard bounds on tori for one-cell observables
only, and Dobrushin uniqueness is a small-`β` statement while the zoom sends `β_k → ∞`.

## Contents

* `inv_pow_four_le`, `inv_pow_mul_le_state_cubeSum` — the site count `1/a⁴` of the unit cube.
* `classMoments_mean_le` — the `a_k⁴` rate forced by `ClassMoments`, any flow.
* `not_classMoments_of_rate` — a mean decaying slower than `a_k⁴` excludes `ClassMoments`.
* `tendsto_expFloor_div_aRun`, `rate_of_expFloor` — an exponential floor below `96π²/(11N²)` beats
  `a_k⁴`.
* `identity_fieldMap`, `identity_reach`, `plaq_le_sym`, `not_classMoments_identity` — the identity
  flow.
* `ReachBlowup`, `not_classMoments_of_reachBlowup` — the named property and its consequence.
-/

noncomputable section

namespace MassGap.FlowMoments

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ContinuumHypercubic
  MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered
  MassGap.ObserverEnergyBox MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS
  MassGap.ObserverOSLinked MassGap.ObserverRotation MassGap.ObserverSymField
  MassGap.ContinuumTimeGroup MassGap.ClayFull MassGap.ObserverMoments Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The site count of the unit cube -/

section Count

/-- **The box of side `2⌊1/a⌋ + 1` has at least `1/a⁴` sites**, `a > 0`.

DERIVED: `1` the unit cube; `2` the two sides; `4` the dimension. -/
theorem inv_pow_four_le {a : ℝ} (ha : 0 < a) :
    1 / a ^ 4 ≤ (2 * (⌊1 / a⌋₊ : ℝ) + 1) ^ 4 := by
  have hl : 1 / a < (⌊1 / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl0 : (0 : ℝ) ≤ (⌊1 / a⌋₊ : ℝ) := Nat.cast_nonneg _
  have h1 : 1 / a ≤ 2 * (⌊1 / a⌋₊ : ℝ) + 1 := by linarith
  have h0 : 0 ≤ 1 / a := (one_div_pos.mpr ha).le
  rw [← one_div_pow]
  exact pow_le_pow_left₀ h0 h1 4

#print axioms inv_pow_four_le

/-- **The unit cube's energy has mean at least `m / a⁴`** when one reading has mean at least `m ≥ 0`:
the unit cube contains the box of side `2⌊1/a⌋ + 1` (`boxSum_le_cubeSum`), whose mean is its site
count times one reading's (`ObserverMoments.state_boxSum`).

DERIVED: `0` the signs; `1` the unit cube; `4` the dimension. -/
theorem inv_pow_mul_le_state_cubeSum (hN : N ≠ 0) (k : ℕ) {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) {m : ℝ} (hm : 0 ≤ m) (hmF : m ≤ stateK hN k F) :
    1 / a ^ 4 * m ≤ stateK hN k (cubeSum a 1 F) := by
  have h2 : stateK hN k (boxSum ⌊1 / a⌋₊ F) ≤ stateK hN k (cubeSum a 1 F) :=
    (stateK hN k).mono (fun U => boxSum_le_cubeSum ha zero_le_one F hF U)
  rw [state_boxSum] at h2
  calc 1 / a ^ 4 * m ≤ (2 * (⌊1 / a⌋₊ : ℝ) + 1) ^ 4 * stateK hN k F :=
        mul_le_mul (inv_pow_four_le ha) hmF hm (by positivity)
    _ ≤ stateK hN k (cubeSum a 1 F) := h2

#print axioms inv_pow_mul_le_state_cubeSum

end Count

/-! ## 2. The rate `ClassMoments` forces -/

section Rate

/-- **`ClassMoments` forces the cell-volume rate of the mean**, for every configuration flow: for a
non-negative field `O` of the class, eventually in the step,
`ν_k(O ∘ V_k) ≤ (B + 1)/2 · a_k⁴`, `B = ((2·1 + 1)⁴)^{2·1} · (2·1)! / t^{2·1} · C` the second-moment
bound of `CubeMomentsAt` at `R = 1`, `p = 1`.

DERIVED: `1` the unit cube, the moment and the unit observable; `2` the square and the halving;
`4` the dimension; `0` the signs. -/
theorem classMoments_mean_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    {O : LField (MassGap.SUN.SU N)} (hOD : O ∈ D) (hO : ∀ U, 0 ≤ O.1 U) {t C : ℝ}
    (h : ClassMoments hN W D t C) :
    ∀ᶠ k in atTop, stateK hN k (W.fieldMap k O).1
      ≤ ((((2 * 1 + 1 : ℝ) ^ 4) ^ (2 * 1) * (((2 * 1).factorial : ℝ) / t ^ (2 * 1) * C) + 1) / 2)
        * dySpacing N k ^ 4 := by
  filter_upwards [h O hOD] with k hk
  set B : ℝ := ((2 * 1 + 1 : ℝ) ^ 4) ^ (2 * 1) * (((2 * 1).factorial : ℝ) / t ^ (2 * 1) * C)
    with hB
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos ha 4
  set F := (W.fieldMap k O).1 with hFdef
  have hF : ∀ U, 0 ≤ F U := fun U => hO (W.V k U)
  set E := cubeSum (dySpacing N k) 1 F with hE
  have hE2 : stateK hN k (E ^ (2 * 1)) ≤ B := by
    have := hk 1 zero_le_one 1
    rw [hB]
    exact this
  have h1 : stateK hN k E ≤ (B + 1) / 2 := by
    have hle : stateK hN k E
        ≤ stateK hN k ((1 / 2 : ℝ) • (E ^ (2 * 1)) + (1 / 2 : ℝ) • (1 : C(Cfg N, ℝ))) :=
      (stateK hN k).mono (fun U => by
        simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.pow_apply,
          ContinuousMap.one_apply, smul_eq_mul]
        nlinarith [sq_nonneg (E U - 1)])
    rw [(stateK hN k).map_add, (stateK hN k).map_smul, (stateK hN k).map_smul,
      (stateK hN k).map_one] at hle
    linarith
  have hm0 : 0 ≤ stateK hN k F := by
    have := (stateK hN k).mono (f := (0 : C(Cfg N, ℝ))) (g := F) (fun U => hF U)
    rwa [(stateK hN k).map_zero] at this
  have h3 := inv_pow_mul_le_state_cubeSum hN k ha F hF hm0 le_rfl
  have h4 : 1 / dySpacing N k ^ 4 * stateK hN k F ≤ (B + 1) / 2 := h3.trans h1
  rw [one_div, inv_mul_le_iff₀ ha4] at h4
  linarith [mul_comm (dySpacing N k ^ 4) ((B + 1) / 2)]

#print axioms classMoments_mean_le

/-- **A mean decaying slower than `a_k⁴` excludes `ClassMoments`**: if a non-negative field of the
class has `ν_k(O ∘ V_k) / a_k⁴ → ∞`, then `ClassMoments hN W D t C` fails at every `t`, `C`.

DERIVED: `4` the dimension. -/
theorem not_classMoments_of_rate (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} {O : LField (MassGap.SUN.SU N)} (hOD : O ∈ D)
    (hO : ∀ U, 0 ≤ O.1 U)
    (hrate : Tendsto (fun k => stateK hN k (W.fieldMap k O).1 / dySpacing N k ^ 4) atTop atTop)
    (t C : ℝ) : ¬ ClassMoments hN W D t C := by
  intro h
  set K : ℝ := (((2 * 1 + 1 : ℝ) ^ 4) ^ (2 * 1) * (((2 * 1).factorial : ℝ) / t ^ (2 * 1) * C) + 1) / 2
  obtain ⟨k, hk1, hk2⟩ := ((classMoments_mean_le hN W hOD hO h).and
    (hrate.eventually_gt_atTop K)).exists
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  have : stateK hN k (W.fieldMap k O).1 / dySpacing N k ^ 4 ≤ K := (div_le_iff₀ ha4).mpr hk1
  linarith

#print axioms not_classMoments_of_rate

end Rate

/-! ## 3. Exponential floors against the spacing -/

section Floor

/-- **An exponential floor below the rate of `a⁴` beats it**: for `c > 0` and
`λ < 96π² / (11 N²)`, `c e^{−λβ} / aRun N β⁴ → ∞` as `β → ∞`. `aRun N β⁴` is
`(48π²β/(11N²))^{4 · 51/121} e^{−96π²β/(11N²)}`, so the ratio is a positive constant times
`e^{(96π²/(11N²) − λ)β} / β^{4 · 51/121}`.

DERIVED: `96 = 4 · 24`, `48 = 24 · 2`, `11`, `51/121` are `aRun`'s (`aRun N β = aRunStd N (2β)`);
`4` the dimension; `0` the signs. -/
theorem tendsto_expFloor_div_aRun (hN : 1 ≤ N) {c lam : ℝ} (hc : 0 < c)
    (hlam : lam < 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2)) :
    Tendsto (fun β => c * Real.exp (-(lam * β)) / AsymptoticScaling.aRun N β ^ 4) atTop atTop := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hκ : 0 < 48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) := by positivity
  have hb : 0 < 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) - lam := sub_pos.mpr hlam
  set κ : ℝ := 48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) with hκdef
  set μ : ℝ := 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) with hμdef
  set s : ℝ := 51 / 121 * ((4 : ℕ) : ℝ) with hs
  have hmain := (tendsto_exp_mul_div_rpow_atTop s (μ - lam) hb).const_mul_atTop
    (div_pos hc (Real.rpow_pos_of_pos hκ s))
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hA : AsymptoticScaling.aRun N β ^ 4 = κ ^ s * β ^ s * Real.exp (-(μ * β)) := by
    unfold AsymptoticScaling.aRun AsymptoticScaling.aRunStd
    have e1 : 24 * Real.pi ^ 2 * (2 * β) / (11 * (N : ℝ) ^ 2) = κ * β := by
      rw [hκdef]; ring
    have e2 : ((4 : ℕ) : ℝ) * (-(12 * Real.pi ^ 2 * (2 * β)) / (11 * (N : ℝ) ^ 2)) = -(μ * β) := by
      rw [hμdef]; push_cast; ring
    rw [mul_pow, e1, ← Real.rpow_mul_natCast (mul_pos hκ hβ).le, ← Real.exp_nat_mul, e2,
      Real.mul_rpow hκ.le hβ.le]
  have hX : Real.exp ((μ - lam) * β) = Real.exp (-(lam * β)) * (Real.exp (-(μ * β)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hks : 0 < κ ^ s := Real.rpow_pos_of_pos hκ s
  have hbs : 0 < β ^ s := Real.rpow_pos_of_pos hβ s
  have hem : 0 < Real.exp (-(μ * β)) := Real.exp_pos _
  rw [hA, hX]
  field_simp

#print axioms tendsto_expFloor_div_aRun

/-- **An exponential floor on a mean beats `a_k⁴` along the zoom**: if eventually
`c e^{−λ β_k} ≤ m_k`, `c > 0`, `λ < 96π²/(11N²)`, then `m_k / a_k⁴ → ∞`
(`tendsto_expFloor_div_aRun` along `tendsto_dyBeta`, with `aRun N β_k = a_k`, `aRun_dyBeta`).

DERIVED: `96`, `11` are `aRun`'s; `4` the dimension; `0` the signs. -/
theorem rate_of_expFloor (hN : N ≠ 0) {m : ℕ → ℝ} {c lam : ℝ} (hc : 0 < c)
    (hlam : lam < 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2))
    (hm : ∀ᶠ k in atTop, c * Real.exp (-(lam * dyBeta (one_le_of_ne_zero hN) k)) ≤ m k) :
    Tendsto (fun k => m k / dySpacing N k ^ 4) atTop atTop := by
  have h := (tendsto_expFloor_div_aRun (one_le_of_ne_zero hN) hc hlam).comp
    (tendsto_dyBeta (one_le_of_ne_zero hN))
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [hm] with k hk
  simp only [Function.comp, aRun_dyBeta]
  exact div_le_div_of_nonneg_right hk (pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4).le

#print axioms rate_of_expFloor

end Floor

/-! ## 4. The identity flow -/

section Identity

/-- **The identity flow reads the field itself.**

DERIVED: no numeral. -/
theorem identity_fieldMap (k : ℕ) (O : LField (MassGap.SUN.SU N)) :
    ((ConfFlow.identity N).fieldMap k O).1 = O.1 :=
  ContinuousMap.ext fun _ => rfl

#print axioms identity_fieldMap

/-- **The identity flow has vanishing physical reach**: its range is `0`.

DERIVED: `0` the range and the limit. -/
theorem identity_reach :
    Tendsto (fun k => dySpacing N k * ((ConfFlow.identity N).range k : ℝ)) atTop (𝓝 0) := by
  have e : (fun k => dySpacing N k * ((ConfFlow.identity N).range k : ℝ)) = fun _ => 0 := by
    funext k
    show dySpacing N k * ((0 : ℕ) : ℝ) = 0
    simp
  rw [e]
  exact tendsto_const_nhds

#print axioms identity_reach

/-- **The symmetrised plaquette density dominates the plaquette density**: its sum over the
hypercubic images has non-negative terms and contains the plaquette itself (the identity
permutation, no reflection).

DERIVED: `0` the excluded colour count and the signs; `4` the dimension. -/
theorem plaq_le_sym (hN : N ≠ 0) (q : MassGap.GibbsSpec.IPlaq) (U : Cfg N) :
    (plaqField (N := N) q).1 U ≤ (sym (plaqField (N := N) q)).1 U := by
  rw [sym_apply]
  have h1 : reflAll (N := N) (fun _ => false) (iaxisConf 1 U) = U := rfl
  have hle := Finset.single_le_sum
    (f := fun g : Equiv.Perm (Fin 4) × (Fin 4 → Bool) =>
      (plaqField (N := N) q).1 (reflAll g.2 (iaxisConf g.1 U)))
    (fun g _ => plaqClass_nonneg hN _ ⟨q, [], rfl⟩ _)
    (Finset.mem_univ ((1 : Equiv.Perm (Fin 4)), (fun _ => false : Fin 4 → Bool)))
  simp only at hle
  rw [h1] at hle
  exact hle

#print axioms plaq_le_sym

/-- **The identity flow fails `ClassMoments` on the symmetrised plaquette class** under a floor on
the Wilson plaquette mean: if, at some plaquette `q`, eventually
`c e^{−λ β_k} ≤ ν_k(1 − Re tr U_q / N)` with `c > 0` and `λ < 96π²/(11N²)`, then
`ClassMoments hN (ConfFlow.identity N) (SymPlaqClass N) t C` fails at every `t`, `C`.

DERIVED: `96`, `11` are `aRun`'s; `4` the dimension; `0` the signs. -/
theorem not_classMoments_identity (hN : N ≠ 0) (q : MassGap.GibbsSpec.IPlaq) {c lam : ℝ}
    (hc : 0 < c) (hlam : lam < 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2))
    (hfloor : ∀ᶠ k in atTop,
      c * Real.exp (-(lam * dyBeta (one_le_of_ne_zero hN) k)) ≤ stateK hN k (plaqField (N := N) q).1)
    (t C : ℝ) : ¬ ClassMoments hN (ConfFlow.identity N) (SymPlaqClass N) t C := by
  have hOD : sym (plaqField (N := N) q) ∈ SymPlaqClass N := ⟨q, rfl⟩
  refine not_classMoments_of_rate hN (ConfFlow.identity N) hOD (symPlaq_nonneg hN _ hOD)
    (rate_of_expFloor hN hc hlam ?_) t C
  filter_upwards [hfloor] with k hk
  rw [identity_fieldMap]
  exact hk.trans ((stateK hN k).mono (fun U => plaq_le_sym hN q U))

#print axioms not_classMoments_identity

end Identity

/-! ## 5. Vanishing reach -/

section Reach

/-- **Vanishing reach makes the physical mean of a field of the class unbounded**: if
`a_k · W.range k → 0`, some non-negative field `O ∈ D` has `ν_k(O ∘ V_k) / a_k⁴ → ∞`.

DERIVED: `0` the limit and the sign; `4` the dimension. -/
def ReachBlowup (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) : Prop :=
  Tendsto (fun k => dySpacing N k * (W.range k : ℝ)) atTop (𝓝 0) →
    ∃ O ∈ D, (∀ U, 0 ≤ O.1 U) ∧
      Tendsto (fun k => stateK hN k (W.fieldMap k O).1 / dySpacing N k ^ 4) atTop atTop

/-- **`ReachBlowup` excludes `ClassMoments` under vanishing reach**: a flow with `ReachBlowup` and
`a_k · W.range k → 0` fails `ClassMoments hN W D t C` at every `t`, `C`
(`not_classMoments_of_rate`).

DERIVED: `0` the limit. -/
theorem not_classMoments_of_reachBlowup (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} (hB : ReachBlowup hN W D)
    (hreach : Tendsto (fun k => dySpacing N k * (W.range k : ℝ)) atTop (𝓝 0)) (t C : ℝ) :
    ¬ ClassMoments hN W D t C := by
  obtain ⟨O, hOD, hO, hrate⟩ := hB hreach
  exact not_classMoments_of_rate hN W hOD hO hrate t C

#print axioms not_classMoments_of_reachBlowup

end Reach

end MassGap.FlowMoments

end
