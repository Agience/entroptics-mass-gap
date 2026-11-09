import Mathlib
import MassGap.ObserverMoments

/-!
# MassGap.FlowUV — `ClassUnitExp` from one exponential moment at one site

`ObserverMoments.ClassUnitExp hN W D t C` bounds `ν_k(e^{t E_1})`, with
`E_1 = cubeSum a_k 1 (O ∘ V_k)` the unweighted sum of the flowed reading over the `≈ 2⁴/a_k⁴` lattice
sites of the unit cube. This module reduces it to one statement about **one site**:

  `SiteExp hN W D s C`: eventually in `k`, `ν_k(exp((s / a_k⁴) · O ∘ V_k)) ≤ C` for every `O ∈ D`.

`s / a_k⁴ · O ∘ V_k` is the flowed reading at the origin in physical units (the lattice reading of a
dimension-four density is `a⁴` times the physical one), so `SiteExp` is the exponential moment, at
strength `s`, of the flowed energy density at one point, uniformly in the spacing.

## The reduction

`exp_mul_wsum_le` is Jensen's inequality for `exp` at the normalised cube weights, pointwise in the
configuration: `e^{t Σ w_x f_x} ≤ Σ (w_x / M) e^{t M f_x}`, `M = Σ w_x`. The state is linear and
translation invariant (`ContinuumNontrivial.stateK_transObs`), so every translate on the right has
the same expectation, and the weights sum to `1` (`state_exp_cubeSum_le`):

  `ν(e^{t · cubeSum a R F}) ≤ ν(e^{t (2R + 3)⁴ / a⁴ · F})`   for `F ≥ 0`, `t ≥ 0`,

the site count `M ≤ (2R + 3)⁴ / a⁴` being `ObserverEnergyBox.sum_cubeInd_le` and `M ≥ 1` the origin
(`one_le_sum_cubeInd`). At `R = 1`: `classUnitExp_of_siteExp` gives
`ClassUnitExp hN W D t C` from `SiteExp hN W D (625 t) C` on a non-negative class.

The step costs only the value of `t`: `ClassUnitExp` asks for some `t > 0`, and `SiteExp` at any
`s > 0` supplies `t = s / 625`. It drops the cancellation between the translates (Jensen aligns
them); for a reading smoothed at a physical radius comparable to the cube that loss is a constant.

## Where `SiteExp` sits

* `siteExp_of_density`: the pointwise bound `DensityVolumeBound W D K` (`|O ∘ V_k| ≤ K a_k⁴`) gives
  `SiteExp hN W D s (e^{sK})` at every `s ≥ 0`; `classUnitExp_of_density'` recovers
  `ObserverMoments.classUnitExp_of_density` through it. `SiteExp` is strictly weaker: it is a tail
  bound, not a sup bound, so a configuration of large flowed density is allowed when it is rare. The
  abelian flux fixed points that make `DensityVolumeBound` unsatisfiable for a gradient flow are such
  configurations.
* `siteExp_mean_le`: `SiteExp` forces `ν_k(O ∘ V_k) ≤ (C − 1) a_k⁴ / s`, the cell-volume rate of
  `ObserverMoments.not_cubeMomentBound_of_mean_ge`; `one_le_of_siteExp`: `C ≥ 1` on a non-negative
  class.
* `siteExp_anti`: on a non-negative class `SiteExp` at `s` gives it at every `s' ≤ s`.

## Unit tests (numerics, `flowuv_tests.py` in the session scratchpad, under 10 s)

* Free field, 4D, exact. The flowed field strength at physical flow time `τ`, per colour component,
  is Gaussian with variance `σ²(a) = ½ [a⁻¹ e^{−x} I₀(x)]⁴`, `x = 4τ/a²`; the energy density is
  `½ Σ_{μ<ν} F²`, so `ν(e^{s E}) = (1 − s σ²)^{−3(N²−1)}`, finite exactly for `s < 1/σ²`. At `τ = 1`:
  `1/σ²(a) = 1223, 1253, 1261, 1263, 1263, 1263` at `a = 1/2, …, 1/64`, against the continuum
  `128π²τ² = 1263.3`: `SiteExp` holds at `s = 631` uniformly in `a ≤ 1/2` (at `SU(3)` the moment
is at most `3.8 · 10⁷`, falling to `2²⁴` in the continuum), so `ClassUnitExp` at `t ≈ 1`. With
  no flow (`τ = 0`), `1/σ² = 2a⁴`: the threshold closes and `SiteExp` fails at every `s > 0`.
* Compact `U(1)` in 2D, exact measure (independent von Mises plaquettes, `β = 1/(ga)²`), the flowed
  plaquette the average angle over a physical `r × r` block: `ν(exp(s a⁻⁴ (1 − cos θ̄)))` at
  `s = ½`, `r = g = 1` is `1.43, 1.42, 1.41, 1.42 (±0.01)` at `a = 1/4, …, 1/32`, against the
  Gaussian value `√2`, while the sup of `a⁻⁴ (1 − cos θ̄)` is `2a⁻⁴`. `SiteExp` holds in a compact
  model where `DensityVolumeBound` fails.

## The three angles (argued)

* **Change of variables along the gradient flow** (Jacobian). The flow is the gradient flow of the
  Wilson action, so `d/dτ log det DV_τ = −ΔS`. Each plaquette term is a character, `Δ Re tr U_P`
  proportional to `Re tr U_P`, so `|ΔS| ≈ β · #plaquettes`. On the region the unit-cube reading
  depends on, at physical flow time (`τ/a²` lattice steps), the Jacobian is `exp(O(β a⁻⁴ · a⁻²))`.
  Per site and per step it is a bounded relative factor, but the factors compose multiplicatively
  over `a⁻⁶` site-steps; no relative form survives. Monotonicity `S(V_τ U) ≤ S(U)` does not help
  either: the unflowed unit-cube action has mean `≈ g² a⁻⁴`. Not formalised.
* **Exact decimation.** `GapSideExactDecimation.effIter` is on the `SU(2)` torus with effective
  densities `DensE`, not on `stateK` over `ℤ⁴`; the observer of `ClassUnitExp` reads the fine lattice
  through `cubeSum`, an unweighted site sum. If `V_k` factored through a fixed-scale block map, the
  pushforward identity would make `E_1` a function of finitely many block variables, and the bound
  would be `DensityVolumeBound` again. The decimation route therefore returns the pointwise form,
  which is unsatisfiable for a flow; `SiteExp` is the expectation form of the same statement.
  `EffectiveDensityBound.UnitOsc` is the single-scale input on that route; it is not consumed here.
* **Chessboard.** On a reflection-positive torus, chessboard bounds `ν(e^{t E_1})` by
  `exp(|B| p(t))`, `p` the pressure shift per site of the perturbation `t · O ∘ V_k`. The `a⁴` scaling
  is then `p_k(t) = O(a_k⁴)`: a finite vacuum-energy shift per physical volume. That is a sharper
  statement than `SiteExp` (no alignment of the translates), but it needs the local function measurable
  for one chessboard cell, while `O ∘ V_k` has support of physical radius (range `≈ r/a_k` sites),
  and it holds on tori, not on `stateK`. Not formalised.

## The remaining input

`SiteExp hN W (PlaqClass N ∪ SymPlaqClass N) s C` for one `s > 0`: at fixed physical flow range, the
flowed plaquette energy density at one point, in physical units, has an exponential moment bounded
uniformly in the spacing. The free field satisfies it at every `s < 128π²τ²` and fails it with no
flow. For the interacting theory it is the UV finiteness of the flowed energy density at a point, in
exponential form.
-/

noncomputable section

namespace MassGap.FlowUV

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ContinuumHypercubic
  MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered
  MassGap.ObserverEnergyBox MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS
  MassGap.ObserverOSLinked MassGap.ObserverRotation MassGap.ObserverSymField
  MassGap.ContinuumTimeGroup MassGap.ClayFull MassGap.ObserverMoments Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Jensen at the cube weights -/

section Jensen

/-- **Jensen's inequality for `exp` at normalised weights**, pointwise:
`e^{t Σ w_i f_i} ≤ Σ (w_i / M) e^{t M f_i}` for `w ≥ 0`, `Σ w_i = M > 0`.

DERIVED: `0` the signs; `1` the total weight after normalising. -/
theorem exp_mul_wsum_le {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {M : ℝ} (hM : 0 < M) (hsum : ∑ i ∈ s, w i = M) (t : ℝ) :
    Real.exp (t * ∑ i ∈ s, w i * f i) ≤ ∑ i ∈ s, (w i / M) * Real.exp (t * M * f i) := by
  have h1 : ∑ i ∈ s, w i / M = 1 := by rw [← Finset.sum_div, hsum, div_self hM.ne']
  have hc := convexOn_exp.map_sum_le (t := s) (w := fun i => w i / M) (p := fun i => t * M * f i)
    (fun i hi => div_nonneg (hw i hi) hM.le) h1 (fun _ _ => Set.mem_univ _)
  have e : t * ∑ i ∈ s, w i * f i = ∑ i ∈ s, (w i / M) • (t * M * f i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hM.ne']
    ring
  rw [e]
  simpa only [smul_eq_mul] using hc

#print axioms exp_mul_wsum_le

/-- **The unit cube holds the origin**: `Σ_{x ∈ box ⌈R/a⌉} 1_{[-R,R]⁴}(a x) ≥ 1` for `R ≥ 0`.

DERIVED: `1` the indicator's value at the origin; `0` the origin and the sign of `R`. -/
theorem one_le_sum_cubeInd {a R : ℝ} (hR : 0 ≤ R) :
    1 ≤ ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) := by
  have h0 : (0 : ISite) ∈ box ⌈R / a⌉₊ := by
    rw [mem_box_iff]
    intro i
    simp
  have hc : cubeInd R (site a 0) = 1 := by
    unfold cubeInd site
    simp [hR]
  calc (1 : ℝ) = cubeInd R (site a 0) := hc.symm
    _ ≤ ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) :=
        Finset.single_le_sum (fun x _ => cubeInd_nonneg _ _) h0

#print axioms one_le_sum_cubeInd

/-- **The cube's exponential moment from one site's**, in a translation-invariant state: for `F ≥ 0`,
`t ≥ 0`, `0 < a ≤ 1`, `R ≥ 0`,
`ν(e^{t · cubeSum a R F}) ≤ ν(e^{t (2R + 3)⁴ / a⁴ · F})`.

DERIVED: `2`, `3`, `4` are `sum_cubeInd_le`'s; `0`, `1` the signs and the spacing bound. -/
theorem state_exp_cubeSum_le (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {R : ℝ} (hR : 0 ≤ R) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) {t : ℝ} (ht : 0 ≤ t) :
    ν (expC (t • cubeSum a R F)) ≤ ν (expC ((t * ((2 * R + 3) ^ 4 / a ^ 4)) • F)) := by
  set L : ℝ := (2 * R + 3) ^ 4 / a ^ 4 with hL
  set M : ℝ := ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) with hMdef
  have hM1 : 1 ≤ M := one_le_sum_cubeInd hR
  have hM : 0 < M := by linarith
  have hML : M ≤ L := sum_cubeInd_le ha ha1 hR
  set G : C(Cfg N, ℝ) := ∑ x ∈ box ⌈R / a⌉₊,
    (cubeInd R (site a x) / M) • transObs x (expC ((t * L) • F)) with hG
  have hpt : ∀ U, expC (t • cubeSum a R F) U ≤ G U := by
    intro U
    have hGU : G U = ∑ x ∈ box ⌈R / a⌉₊,
        (cubeInd R (site a x) / M) * Real.exp (t * L * F (transConf x U)) := by
      rw [hG]
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
        expC_apply, smul_eq_mul, mul_assoc]
    rw [hGU, expC_apply, ContinuousMap.smul_apply, smul_eq_mul, cubeSum_apply]
    refine (exp_mul_wsum_le _ (fun x => cubeInd R (site a x)) (fun x => F (transConf x U))
      (fun x _ => cubeInd_nonneg _ _) hM rfl t).trans ?_
    refine Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left ?_
      (div_nonneg (cubeInd_nonneg _ _) hM.le))
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hML ht) (hF _))
  have hνG : ν G = ν (expC ((t * L) • F)) := by
    rw [hG, ν.map_sum]
    simp only [ν.map_smul, htr]
    rw [← Finset.sum_mul, ← Finset.sum_div, ← hMdef, div_self hM.ne', one_mul]
  calc ν (expC (t • cubeSum a R F)) ≤ ν G := ν.mono hpt
    _ = ν (expC ((t * L) • F)) := hνG

#print axioms state_exp_cubeSum_le

/-- **`state_exp_cubeSum_le` in the Wilson states**: `stateK` is translation invariant
(`ContinuumNontrivial.stateK_transObs`).

DERIVED: `2`, `3`, `4` as in `state_exp_cubeSum_le`; `0`, `1` the signs and the spacing bound. -/
theorem stateK_exp_cubeSum_le (hN : N ≠ 0) (k : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {R : ℝ}
    (hR : 0 ≤ R) (F : C(Cfg N, ℝ)) (hF : ∀ U, 0 ≤ F U) {t : ℝ} (ht : 0 ≤ t) :
    stateK hN k (expC (t • cubeSum a R F))
      ≤ stateK hN k (expC ((t * ((2 * R + 3) ^ 4 / a ^ 4)) • F)) :=
  state_exp_cubeSum_le (stateK hN k) (MassGap.ContinuumNontrivial.stateK_transObs hN k) ha ha1 hR F
    hF ht

#print axioms stateK_exp_cubeSum_le

end Jensen

/-! ## 2. The single-site input -/

section Site

/-- **One exponential moment of the flowed reading at one site, in physical units**: one `s`, `C`
with, eventually in the step, `ν_k(exp((s / a_k⁴) · O ∘ V_k)) ≤ C` for every field of `D`.

DERIVED: `4` is the canonical dimension. -/
def SiteExp (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (s C : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ O ∈ D,
    stateK hN k (expC ((s / dySpacing N k ^ 4) • (W.fieldMap k O).1)) ≤ C

/-- **`ClassUnitExp` from `SiteExp`**: on a non-negative class, `SiteExp` at `(2·1 + 3)⁴ t = 625 t`
gives `ClassUnitExp` at `t`, with the same constant (`stateK_exp_cubeSum_le` at `R = 1`).

DERIVED: `1` the unit cube and the spacing bound; `2`, `3`, `4` the site count; `0` the signs. -/
theorem classUnitExp_of_siteExp (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 ≤ t)
    (h : SiteExp hN W D (t * (2 * 1 + 3) ^ 4) C) : ClassUnitExp hN W D t C := by
  filter_upwards [h, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1 O hO
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have e : t * ((2 * 1 + 3) ^ 4 / dySpacing N k ^ 4) = t * (2 * 1 + 3) ^ 4 / dySpacing N k ^ 4 :=
    (mul_div_assoc _ _ _).symm
  have hb := stateK_exp_cubeSum_le hN k ha hk1.le zero_le_one _ hF ht
  rw [e] at hb
  exact hb.trans (hk O hO)

#print axioms classUnitExp_of_siteExp

/-- **The pointwise density bound gives `SiteExp`**: `|O ∘ V_k| ≤ K a_k⁴` gives
`ν_k(exp((s / a_k⁴) O ∘ V_k)) ≤ e^{sK}` at every `s ≥ 0`.

DERIVED: `4` the canonical dimension; `0` the sign of `s` and the excluded colour count. -/
theorem siteExp_of_density (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    {K : ℝ} (h : DensityVolumeBound W D K) {s : ℝ} (hs : 0 ≤ s) :
    SiteExp hN W D s (Real.exp (s * K)) := by
  filter_upwards [h] with k hk O hO
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  refine state_le_of_le _ _ (fun U => ?_)
  rw [expC_apply, ContinuousMap.smul_apply, smul_eq_mul]
  refine Real.exp_le_exp.mpr ?_
  have hU := (le_abs_self _).trans (hk O hO U)
  have hsd : 0 ≤ s / dySpacing N k ^ 4 := div_nonneg hs ha4.le
  have hd : dySpacing N k ≠ 0 := (dySpacing_pos (one_le_of_ne_zero hN) k).ne'
  calc s / dySpacing N k ^ 4 * (W.fieldMap k O).1 U
      ≤ s / dySpacing N k ^ 4 * (K * dySpacing N k ^ 4) := mul_le_mul_of_nonneg_left hU hsd
    _ = s * K := by field_simp

#print axioms siteExp_of_density

/-- **`ObserverMoments.classUnitExp_of_density` through `SiteExp`**: the pointwise density bound at
`K`, on a non-negative class, gives `ClassUnitExp` at `t = 1` with constant `e^{625 K}`.

DERIVED: `1` the unit cube and `t`; `2`, `3`, `4` the site count; `0` the signs. -/
theorem classUnitExp_of_density' (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {K : ℝ}
    (h : DensityVolumeBound W D K) :
    ClassUnitExp hN W D 1 (Real.exp (1 * (2 * 1 + 3) ^ 4 * K)) :=
  classUnitExp_of_siteExp hN W hpos zero_le_one (siteExp_of_density hN W h (by norm_num))

#print axioms classUnitExp_of_density'

/-- **`SiteExp` forces the cell-volume rate of the mean**: on a non-negative class,
`ν_k(O ∘ V_k) ≤ (C − 1) a_k⁴ / s` eventually, from `1 + x ≤ eˣ`.

DERIVED: `1` the unit observable and `1 + x ≤ eˣ`; `4` the canonical dimension; `0` the signs. -/
theorem siteExp_mean_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    {s C : ℝ} (hs : 0 < s) (h : SiteExp hN W D s C) :
    ∀ᶠ k in atTop, ∀ O ∈ D,
      stateK hN k (W.fieldMap k O).1 ≤ (C - 1) * dySpacing N k ^ 4 / s := by
  filter_upwards [h] with k hk O hO
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  set F := (W.fieldMap k O).1
  set c := s / dySpacing N k ^ 4 with hc
  have hc0 : 0 < c := div_pos hs ha4
  have hm : stateK hN k (1 + c • F) ≤ stateK hN k (expC (c • F)) :=
    (stateK hN k).mono (fun U => by
      simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
        smul_eq_mul, expC_apply]
      linarith [Real.add_one_le_exp (c * F U)])
  rw [(stateK hN k).map_add, (stateK hN k).map_one, (stateK hN k).map_smul] at hm
  have h1 : c * stateK hN k F ≤ C - 1 := by linarith [hk O hO]
  rw [le_div_iff₀ hs]
  have hd : dySpacing N k ≠ 0 := (dySpacing_pos (one_le_of_ne_zero hN) k).ne'
  have e : c * stateK hN k F * dySpacing N k ^ 4 = stateK hN k F * s := by
    rw [hc]; field_simp
  nlinarith [mul_le_mul_of_nonneg_right h1 ha4.le]

#print axioms siteExp_mean_le

/-- **The constant of `SiteExp` is at least `1`** at a non-negative field of the class, `s ≥ 0`.

DERIVED: `1` the unit observable; `0` the signs. -/
theorem one_le_of_siteExp (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {s C : ℝ} (hs : 0 ≤ s) (h : SiteExp hN W D s C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) : 1 ≤ C := by
  obtain ⟨k, hk⟩ := h.exists
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  have hm : stateK hN k (1 : C(Cfg N, ℝ))
      ≤ stateK hN k (expC ((s / dySpacing N k ^ 4) • (W.fieldMap k O).1)) :=
    (stateK hN k).mono (fun U => by
      simp only [ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul, expC_apply]
      exact Real.one_le_exp (mul_nonneg (div_nonneg hs ha4.le) (hpos O hO (W.V k U))))
  rw [(stateK hN k).map_one] at hm
  exact hm.trans (hk O hO)

#print axioms one_le_of_siteExp

/-- **`SiteExp` passes to a smaller strength** on a non-negative class.

DERIVED: `4` the canonical dimension; `0` the signs. -/
theorem siteExp_anti (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {s s' C : ℝ} (hss : s' ≤ s)
    (h : SiteExp hN W D s C) : SiteExp hN W D s' C := by
  filter_upwards [h] with k hk O hO
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  refine le_trans ((stateK hN k).mono (fun U => ?_)) (hk O hO)
  simp only [ContinuousMap.smul_apply, smul_eq_mul, expC_apply]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hss ha4.le) (hpos O hO (W.V k U)))

#print axioms siteExp_anti

/-- **The three moment inputs of `clayFullAt_of_observer` from `SiteExp`** on
`PlaqClass N ∪ SymPlaqClass N` at strength `625 t`, `t > 0`
(`ObserverMoments.observer_moment_inputs_of_classUnitExp` after `classUnitExp_of_siteExp`).

DERIVED: `1` the unit cube; `2`, `3`, `4` the site count; `0` the lower end of `t`. -/
theorem observer_moment_inputs_of_siteExp (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (h : SiteExp hN W (PlaqClass N ∪ SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C) :
    (∀ O ∈ PlaqClass N, CubeMomentBound hN W O) ∧ ClassMoments hN W (SymPlaqClass N) t |C|
      ∧ ∀ O ∈ SymPlaqClass N, UnitCubeExpBound hN W O :=
  observer_moment_inputs_of_classUnitExp hN W ht
    (classUnitExp_of_siteExp hN W (plaqSym_nonneg hN) ht.le h)

#print axioms observer_moment_inputs_of_siteExp

end Site

end MassGap.FlowUV

end
