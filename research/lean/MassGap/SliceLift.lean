import Mathlib
import MassGap.ScaleControl
import MassGap.TorusRefPosPlane

/-!
# MassGap.SliceLift — slice functions read as periodic observables, and the block contraction on them

`ScaleControl.SliceControl` pairs slice vectors `v_kj` against periodic observables `X_kj` that are free, so at
`X = 0` its `bridge` field alone carries the bound. This module ties `X` to `v`.

## 1. The lift (proved)

* `readAt i t U`: the spatial links (directions `≠ i`) of the time-`t` slice (direction `i`) of a `ℤ⁴`
  configuration `U`, with transverse coordinates `y ∈ TT i T` placed at `y_j ∈ [0, T_j)`.
* `liftAt i q t = q ∘ readAt i t` and `lift i q = liftAt i q 0`, for `q` continuous on the slice of extents `T`.
  At `T = Tr n i` this is the lift of a function on `TensionFloor.Slice n i` to `C(IConf (SU 2), ℝ)`.
* `readAt_surjective`, `liftAt_injective`, **`lift_eq_zero_iff`**: `lift i q = 0 ↔ q = 0`. So the `X = 0`
  reading of `SliceControl` is available to `SliceControl'` only at `q = 0`.
* `shift_liftAt` (direction `0`): `S^d (liftAt 0 q t) = liftAt 0 q (t + d)`.

Argued, not a declaration: for `q = W_C` a Wilson loop on the slice torus that does not wrap, `lift i W_C` is the
`ℤ⁴` Wilson loop of `C` at time `0`; for a loop that wraps the slice torus it is the product along an open
`ℤ⁴` path (the wrap-around link `T_j − 1 → 0` is read as the `ℤ⁴` link `T_j − 1 → T_j`), not gauge invariant
in `ℤ⁴`. Centring is linear: `lift i (q − c) = lift i q − c` (precomposition).

## 2. The exact relation that exists: the cubic torus at step 0 (proved)

The tree relates the slice transfer to a periodic state on one geometry only: the cubic torus of side `M + 1`
sliced along direction `0` (`TorusChain`, `SliceRPStrict`, `TorusRefPosPlane`), state
`PeriodicState.torusState hN M β`. Its slice is `TensionFloor.Slice (M + 1) 0` (`Tr_zero`:
`Tr (M + 1) 0 = Tc M`).

* `torus_lift_pair_gen`: for `M = a + 1 + b`, `ν_M(θ X · S^{a+1} X) = (∫∫ q(x) q(y) P_a(x,y) P_b(y,x)) / Zc_M(1)`,
  `X = lift 0 q`, `θ = ireflObs 0 0`, `P_j = kT^{∗(j+1)}` the full (all flux sectors) slice transfer.
* **`torus_lift_pair`**: at side `n = 2(m + 1)`, `M = n − 1`, shift `s = n/2 = m + 1`:
  `ν_{n−1}(θ X · S^{n/2} X) = (∫∫ q(x) q(y) halfKN(x,y) halfKN(y,x)) / Zc_{n−1}(1)` with
  `halfKN = CentreSectorSeedN.halfKN 2 β n 0` (the transfer over half the time extent), the kernel whose
  centre average is `trivKN`.
* `inner_kernelCLM_self`: the slice side, `⟪T v, T v⟫ = ∫ (K q)²` for `v = q` a.e., any bounded kernel `K`.

**The slice pairing and the torus pairing are different numbers** (argued from the two formulas, not a
declaration). The slice pairing `∫ (trivKN q)²` is an `L²(Haar)` pairing over the full time extent `n`
(`T² = P₀ halfKN²`) in the zero-flux sector; the torus pairing is a trace `Tr(Q H Q H)/Tr(H²)`, `H = halfKN`, at
separation `n/2` closed by the remaining `n/2`, over all flux sectors. No cubic torus of the tree has the slice's
spatial extent `n` and a time extent `≥ 2n`; at `i ≠ 0` (anisotropic `Tr n i`, step direction `i`) the tree has
no periodic state whose slice is `Slice n i`. The infinite-volume `periodicState` is the limit of
`torusState (2j+1)` along `periodicUltra`, whose slices have side `2(j+1) → ∞`, not `n`.

* **`bridge_step0`**: at step `0`, `m ≥ 1`, `τ = 0`, `p = 0`, `s = n/2`, the diagonal bridge of
  `SliceControl'` holds with `Z = Zc_{n−1}(1)` and `η = sliceErr + Zc · (discErr + volErr)`, three explicit
  numbers:
  `sliceErr = |∫ (trivKN q)² − ∫∫ q q halfKN halfKN|` (slice vs finite torus, kernel integrals only);
  `discErr = |ν_{n−1}(θX) ν_{n−1}(S^{n/2} X)|` (the disconnected part on the torus);
  `volErr = |Cov_{ν_{n−1}} − Cov_{periodicState}|` (side `n` torus vs `ℤ⁴`). None is proved small.

**Scales.** `‖T v‖²` and both terms of `sliceErr` are kernel-scale integrals (`∫(trivKN q)²` is of order
`λ₀ⁿ ‖q‖²`); state values (`ν(θX · SX)`, the covariances, `discErr`, `volErr`) are normalised (`1` at `q = 1`).
`torus_lift_pair` says kernel integral `= Zc · ν_{n−1}(θX · S^{n/2} X)`, so `Zc` is the factor between the two
scales, and `bridge_step0` compares kernel scale with kernel scale throughout.

## 3. `SliceControl'` (proved: the gap from it)

`SliceControl'` is `SliceControl` with: continuous slice functions `q_kj` with `v_kj = q_kj` a.e.; the
periodic observables **fixed** to `X_kj := lift i q_kj` (no `X` field); `contract` and `bridge` **diagonal**
(one observable against its own reflected shift, the form of `torus_lift_pair`); `bridge` carries the
normalised periodic covariance times an explicit scale factor `Z ≥ 0`, and `rate` reads the contraction bound
times `Z`. Cauchy–Schwarz
(`abs_inner_le_of_norm_sq_le`) carries the diagonal bound to every pair.

* **`zeroFluxGap_of_sliceControl'`**: one record gives `ZeroFluxGap g₀ E (diagRate c c' σ δ (n a))`.

**What remains of `bridge`.** It does not disappear: it is the field `bridge` with `X = lift q` forced, and at
step `0` `bridge_step0` replaces it by the three explicit errors above; at `i ≠ 0` no finite periodic state of
the tree has the slice's geometry, so `bridge` stays a hypothesis on `periodicState` with free `η` and `Z`.
`contract` is now on the real lifted observables (`lift_eq_zero_iff`), but it still enters only through `rate`
(`δ_k = B αᵐ V D`) and is load-bearing only if `η_k` is small, which nothing in the tree proves: the record
asks `η_k ≥ max_j (sliceErr + Zc · (discErr + volErr))(q k j)` (`κ k` finite). `discErr` vanishes only when
`ν_{n−1}(lift 0 q) = 0` (argued, not a declaration: `ν_{n−1}` is reflection and shift invariant, so `discErr = ν_{n−1}(lift 0 q)²`).

DERIVED (module-wide): `0` is the time of the lifted slice, the step direction of `TorusChain`'s cubic torus
and the reflection plane `x₀ = 0`; `2` is `SU(2)`, the `L²` exponent and the factor in `n = 2(m+1)` (an even
side, so that `halfKN` covers exactly half of it); `1` is the constant insertion of `Zc` and the successor in
`M + 1`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SliceLift

open MeasureTheory Filter
open MassGap.RectWilson (SpT TT)
open MassGap.RectTransfer (hS kT)
open MassGap.KernelPower (iter)
open MassGap.CentreSectorSeedN (trivKN hSN halfKN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.SlabKernelOperator (kernelCLM kernelFun coeFn_kernelCLM)
open MassGap.PeriodicState (periodicState torusState)
open MassGap.LatticeReflection (ireflObs)
open MassGap.ReflectionShift (ishiftObsL)
open MassGap.FocusZoom (stateCov)
open MassGap.GibbsSpec (ILink IConf VConf splice)

variable {N : ℕ}

/-! ## 1. The lift -/

/-- The `ℤ⁴` site at time `t` (direction `i`) with transverse coordinates `y`. -/
def siteAt (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) (y : TT i T) : Fin 4 → ℤ :=
  fun j => if h : j = i then t else ((y ⟨j, h⟩ : ℕ) : ℤ)

/-- The spatial links of the time-`t` slice of a `ℤ⁴` configuration. -/
def readAt (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) (U : IConf (SUN.SU N)) :
    SpT i T → SUN.SU N :=
  fun p => U (p.1.1, siteAt i t p.2)

theorem continuous_readAt (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) :
    Continuous (readAt (N := N) i (T := T) t) :=
  continuous_pi fun _ => continuous_apply _

/-- **The lift at time `t`**: `q` read on the spatial links of the time-`t` slice. -/
def liftAt (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (q : C(SpT i T → SUN.SU N, ℝ)) (t : ℤ) :
    C(IConf (SUN.SU N), ℝ) :=
  ⟨fun U => q (readAt i t U), q.continuous.comp (continuous_readAt i t)⟩

/-- **The lift**: `q` read on the spatial links of the time-`0` slice. -/
def lift (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (q : C(SpT i T → SUN.SU N, ℝ)) :
    C(IConf (SUN.SU N), ℝ) :=
  liftAt i q 0

theorem siteAt_injective (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) :
    Function.Injective (siteAt i (T := T) t) := by
  intro a b h
  funext j
  apply Fin.ext
  have hj := congrFun h j.1
  simp only [siteAt, dif_neg j.2] at hj
  exact_mod_cast hj

/-- Every slice configuration is read off some `ℤ⁴` configuration. -/
theorem readAt_surjective (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) :
    Function.Surjective (readAt (N := N) i (T := T) t) := by
  intro V
  have hf : Function.Injective (fun p : SpT i T => ((p.1.1, siteAt i t p.2) : ILink)) := by
    intro a b h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (Subtype.ext h1) (siteAt_injective i t h2)
  exact ⟨Function.extend _ V (fun _ => 1), funext fun p => hf.extend_apply V _ p⟩

theorem liftAt_injective (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) :
    Function.Injective (fun q : C(SpT i T → SUN.SU N, ℝ) => liftAt i q t) := by
  intro q q' h
  ext V
  obtain ⟨U, rfl⟩ := readAt_surjective (N := N) i t V
  exact congrArg (fun F : C(IConf (SUN.SU N), ℝ) => F U) h

/-- **The lift vanishes only at `q = 0`.** -/
theorem lift_eq_zero_iff (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (q : C(SpT i T → SUN.SU N, ℝ)) :
    lift i q = 0 ↔ q = 0 := by
  constructor
  · intro h
    refine liftAt_injective (N := N) i 0 ?_
    show liftAt i q 0 = liftAt i 0 0
    rw [show liftAt i q 0 = lift i q from rfl, h]
    rfl
  · rintro rfl; rfl

/-- The unit shift along direction `0`, iterated, moves the lifted slice in time. -/
theorem shift_liftAt {T : {j : Fin 4 // j ≠ 0} → ℕ} (q : C(SpT 0 T → SUN.SU N, ℝ)) (t : ℤ) (d : ℕ) :
    (⇑(ishiftObsL (G := SUN.SU N) 0))^[d] (liftAt 0 q t) = liftAt 0 q (t + d) := by
  ext U
  rw [TorusChain.shiftObs_iter]
  show q (readAt 0 t _) = q (readAt 0 (t + d) U)
  congr 1
  funext p
  show U (p.1.1, Function.update (siteAt 0 t p.2) 0 (siteAt 0 t p.2 0 + d))
    = U (p.1.1, siteAt 0 (t + d) p.2)
  congr 2
  funext j
  by_cases hj : j = 0
  · subst hj; simp [siteAt]
  · simp [siteAt, hj]

/-! ## 2. The cubic torus at step 0 -/

/-- At step `0` the slice of side `M + 1` is the slice of `TorusChain`'s cubic torus of side `M + 1`. -/
theorem Tr_zero (M : ℕ) : CentreSectorSeed.Tr (M + 1) 0 = TorusChain.Tc M := by
  funext j
  have hp : CentreSectorSeed.pathV 0 j.1 = 0 := by
    have : CentreSectorSeed.pathV 0 = fun _ => 0 := by funext k; fin_cases k <;> rfl
    rw [this]
  show 2 ^ (CentreSectorSeed.pathV 0 j.1) * (M + 1) = M + 1
  rw [hp, pow_zero, one_mul]

/-- **The torus pairing of a lifted slice function** (cubic torus of side `M + 1`, `M = a + 1 + b`):
`ν_M(θ X · S^{a+1} X) = (∫∫ q(x) q(y) P_a(x,y) P_b(y,x)) / Zc_M(1)`, `X = lift 0 q`, `P_j = kT^{∗(j+1)}`. -/
theorem torus_lift_pair_gen (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ}
    {T : {j : Fin 4 // j ≠ 0} → ℕ} (hT : T = TorusChain.Tc M) (q : C(SpT 0 T → SUN.SU N, ℝ))
    (a b : ℕ) (hM : M = a + 1 + b) :
    torusState hN M β (ireflObs 0 0 (lift 0 q) * (⇑(ishiftObsL (G := SUN.SU N) 0))^[a + 1] (lift 0 q))
      = (∫ x, ∫ y, q x * q y * (iter (hS 0 T N) (kT 0 T N β) a x y
          * iter (hS 0 T N) (kT 0 T N β) b y x) ∂(hS 0 T N) ∂(hS 0 T N))
        / TorusChain.Zc M N β (fun _ _ => 1) := by
  subst hT
  rw [lift, shift_liftAt, zero_add]
  have h0 : liftAt 0 q 0 = SliceRPStrict.Qr q 0 := rfl
  have h1 : liftAt 0 q ((a + 1 : ℕ) : ℤ) = SliceRPStrict.Qr q (a + 1) := rfl
  rw [h0, h1, TorusRefPosPlane.torusState_refl_Qr_pair hN hβ (r := 0) (r' := a + 1) (by omega) q]
  congr 1
  exact SliceRPStrict.Zc_pair hN hβ q a b hM

/-- **The torus pairing at step 0 in the slice's own kernel.** At side `n = 2(m + 1)`, on the cubic torus of
side `n` (`torusState _ (2m + 1) β`), with `X = lift 0 q` and the shift `S^{n/2}`:
`ν(θ X · S^{n/2} X) = (∫∫ q(x) q(y) halfKN(x,y) halfKN(y,x)) / Zc(1)`, `halfKN = halfKN 2 β n 0`. -/
theorem torus_lift_pair {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) (q : C(Slice (2 * (m + 1)) 0, ℝ)) :
    torusState (two_ne_zero : (2 : ℕ) ≠ 0) (2 * m + 1) β
        (ireflObs 0 0 (lift 0 q) * (⇑(ishiftObsL (G := SUN.SU 2) 0))^[m + 1] (lift 0 q))
      = (∫ x, ∫ y, q x * q y * (halfKN 2 β (2 * (m + 1)) 0 x y * halfKN 2 β (2 * (m + 1)) 0 y x)
          ∂(hSN 2 (2 * (m + 1)) 0) ∂(hSN 2 (2 * (m + 1)) 0))
        / TorusChain.Zc (2 * m + 1) 2 β (fun _ _ => 1) := by
  have hT : CentreSectorSeed.Tr (2 * (m + 1)) 0 = TorusChain.Tc (2 * m + 1) := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring]; exact Tr_zero _
  rw [torus_lift_pair_gen two_ne_zero hβ hT q m m (by ring)]
  have hk : (2 * (m + 1)) / 2 - 1 = m := by omega
  simp only [halfKN, hk]

/-- **The slice pairing of a vector that is a function a.e.**: `⟪T v, T v⟫ = ∫ (K q)²` for `v = q` a.e. -/
theorem inner_kernelCLM_self {X : Type*} [MeasurableSpace X] (K : X → X → ℝ) (C : ℝ)
    (hK : Measurable (Function.uncurry K)) (hC0 : 0 ≤ C) (hKb : ∀ x y, |K x y| ≤ C) (μ : Measure X)
    [IsProbabilityMeasure μ] (v : Lp ℝ 2 μ) (q : X → ℝ) (hv : (v : X → ℝ) =ᵐ[μ] q) :
    inner ℝ (kernelCLM K C hK hC0 hKb μ μ v) (kernelCLM K C hK hC0 hKb μ μ v)
      = ∫ x, kernelFun K μ q x ^ 2 ∂μ := by
  have hfun : kernelFun K μ (v : X → ℝ) = kernelFun K μ q := funext fun x =>
    integral_congr_ae (hv.mono fun y hy => by simp only [hy])
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_kernelCLM K C hK hC0 hKb μ μ v] with x hx
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hfun, sq]

/-- The slice-vs-torus error at step 0: `|∫ (trivKN q)² − ∫∫ q q halfKN halfKN|`. Both terms are at kernel
scale (unnormalised kernel integrals over `hSN`); the torus normalisation `Zc` is not divided out here, it
multiplies the normalised torus quantities in `bridge_step0`. -/
def sliceErr (β : ℝ) (m : ℕ) (q : C(Slice (2 * (m + 1)) 0, ℝ)) : ℝ :=
  |∫ x, kernelFun (trivKN 2 β (2 * (m + 1)) 0) (hSN 2 (2 * (m + 1)) 0) q x ^ 2 ∂(hSN 2 (2 * (m + 1)) 0)
    - ∫ x, ∫ y, q x * q y * (halfKN 2 β (2 * (m + 1)) 0 x y * halfKN 2 β (2 * (m + 1)) 0 y x)
          ∂(hSN 2 (2 * (m + 1)) 0) ∂(hSN 2 (2 * (m + 1)) 0)|

/-- The disconnected part on the side-`n` torus: `|ν(θX) ν(S^{n/2} X)|`. -/
def discErr (β : ℝ) (m : ℕ) (q : C(Slice (2 * (m + 1)) 0, ℝ)) : ℝ :=
  |torusState (two_ne_zero : (2 : ℕ) ≠ 0) (2 * m + 1) β (ireflObs 0 0 (lift 0 q))
    * torusState (two_ne_zero : (2 : ℕ) ≠ 0) (2 * m + 1) β
        ((⇑(ishiftObsL (G := SUN.SU 2) 0))^[m + 1] (lift 0 q))|

/-- The volume error: the side-`n` torus covariance against the periodic state's. -/
def volErr (β : ℝ) (m : ℕ) (q : C(Slice (2 * (m + 1)) 0, ℝ)) : ℝ :=
  |stateCov (torusState (two_ne_zero : (2 : ℕ) ≠ 0) (2 * m + 1) β) (ireflObs 0 0 (lift 0 q))
      ((⇑(ishiftObsL (G := SUN.SU 2) 0))^[m + 1] (lift 0 q))
    - stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) (ireflObs 0 0 (lift 0 q))
      ((⇑(ishiftObsL (G := SUN.SU 2) 0))^[m + 1] (lift 0 q))|

/-- **The diagonal bridge at step 0 with explicit errors.** At side `n = 2(m + 1)`, `m ≥ 1`, `τ = 0`,
`p = 0`, `s = n/2`, for `v = q` a.e.:
`‖T v‖² ≤ Zc · (|Cov_ν(θ lift q, S^{n/2} lift q)| + discErr + volErr) + sliceErr`,
`ν = periodicState`, `T` the operator of `trivKN 2 β n 0`, `Zc = Zc_{n−1}(1)`.

Scales: `‖T v‖²` and both terms of `sliceErr` are kernel-scale integrals; the covariances, `discErr` and
`volErr` are normalised (state values, `= 1`-scale at `q = 1`). `Zc` carries the normalised side to kernel
scale (`torus_lift_pair`: kernel integral `= Zc · ν_{n−1}(θX · S^{n/2} X)`), so every comparison is between
like quantities. -/
theorem bridge_step0 {β : ℝ} (hβ : 0 < β) (m : ℕ) (hm : 1 ≤ m) {C : ℝ}
    (hkm : Measurable (Function.uncurry (trivKN 2 β (2 * (m + 1)) 0))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β (2 * (m + 1)) 0 x y| ≤ C) (v : Lp ℝ 2 (hSN 2 (2 * (m + 1)) 0))
    (q : C(Slice (2 * (m + 1)) 0, ℝ))
    (hv : (v : Slice (2 * (m + 1)) 0 → ℝ) =ᵐ[hSN 2 (2 * (m + 1)) 0] q) :
    ‖kernelCLM (trivKN 2 β (2 * (m + 1)) 0) C hkm hC0 hkb (hSN 2 (2 * (m + 1)) 0)
        (hSN 2 (2 * (m + 1)) 0) v‖ ^ 2
      ≤ TorusChain.Zc (2 * m + 1) 2 β (fun _ _ => 1)
          * (|stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) (ireflObs 0 (2 * 0) (lift 0 q))
              ((⇑(ishiftObsL (G := SUN.SU 2) 0))^[m + 1] (lift 0 q))|
            + discErr β m q + volErr β m q)
        + sliceErr β m q := by
  rw [← real_inner_self_eq_norm_sq, inner_kernelCLM_self _ _ _ _ _ _ v q hv,
    show (2 : ℤ) * 0 = 0 from rfl]
  set a := ∫ x, kernelFun (trivKN 2 β (2 * (m + 1)) 0) (hSN 2 (2 * (m + 1)) 0) q x ^ 2
    ∂(hSN 2 (2 * (m + 1)) 0) with ha
  set I := ∫ x, ∫ y, q x * q y * (halfKN 2 β (2 * (m + 1)) 0 x y * halfKN 2 β (2 * (m + 1)) 0 y x)
    ∂(hSN 2 (2 * (m + 1)) 0) ∂(hSN 2 (2 * (m + 1)) 0) with hI
  set Z := TorusChain.Zc (2 * m + 1) 2 β (fun _ _ => 1) with hZ
  set ν := torusState (two_ne_zero : (2 : ℕ) ≠ 0) (2 * m + 1) β with hν
  set θX := ireflObs 0 0 (lift 0 q) with hθX
  set SX := (⇑(ishiftObsL (G := SUN.SU 2) 0))^[m + 1] (lift 0 q) with hSX
  have hZpos : 0 < Z := TorusRefPosPlane.Zc_one_pos two_ne_zero hβ hm
  have hpair := torus_lift_pair hβ.le m q
  rw [← hν, ← hθX, ← hSX, ← hI, ← hZ] at hpair
  have hIZ : I = Z * ν (θX * SX) := by rw [hpair]; field_simp
  have hs : sliceErr β m q = |a - I| := rfl
  have hd : discErr β m q = |ν θX * ν SX| := rfl
  have hvol : volErr β m q
      = |stateCov ν θX SX - stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) θX SX| := rfl
  have hc : ν (θX * SX) = stateCov ν θX SX + ν θX * ν SX := by
    unfold stateCov; ring
  rw [hs, hd, hvol]
  have h1 : a ≤ |I| + |a - I| := by
    linarith [le_abs_self I, le_abs_self (a - I)]
  have h2 : |ν (θX * SX)| ≤ |stateCov ν θX SX| + |ν θX * ν SX| := by
    rw [hc]; exact abs_add_le _ _
  have h3 := abs_sub_abs_le_abs_sub (stateCov ν θX SX)
    (stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) θX SX)
  have h4 : |ν (θX * SX)| ≤ |stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) θX SX|
      + |ν θX * ν SX|
      + |stateCov ν θX SX - stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) θX SX| := by
    linarith
  have hIabs : |I| = Z * |ν (θX * SX)| := by rw [hIZ, abs_mul, abs_of_pos hZpos]
  have h5 := mul_le_mul_of_nonneg_left h4 hZpos.le
  linarith

/-! ## 3. `SliceControl'` -/

/-- Diagonal bounds give every pair: `‖x‖² ≤ e`, `‖y‖² ≤ e` give `|⟪x, y⟫| ≤ e`. -/
theorem abs_inner_le_of_norm_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {e : ℝ} (hx : ‖x‖ ^ 2 ≤ e) (hy : ‖y‖ ^ 2 ≤ e) : |inner ℝ x y| ≤ e := by
  have h := abs_real_inner_le_norm x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- **The control of one zero-flux slice with lifted observables.** As `ScaleControl.SliceControl`, with
continuous slice functions `q_kj` equal a.e. to the spanning vectors `v_kj`, the periodic observables fixed to
`lift i q_kj` (the spatial links at time `0` of a `ℤ⁴` configuration, direction `i`), and `contract`, `bridge`
diagonal. Fields `levels` … `gram`, `rate`, `count` are those of `SliceControl` (classification there). -/
structure SliceControl' (c c' σ δ α V D B t₀ Cc : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
  ι : Type
  g₀ : ι
  E : ι → ℝ
  φ : ι → Slice n i → ℝ
  μ : ι → ℝ
  levels : EigenLevels β n i g₀ E φ μ
  meas : ∀ j, Measurable (φ j)
  C : ℝ
  kmeas : Measurable (Function.uncurry (trivKN 2 β n i))
  C0 : 0 ≤ C
  kbd : ∀ x y, |trivKN 2 β n i x y| ≤ C
  R : ℕ → ℝ
  R_mono : Monotone R
  R_reach : ∀ N : ℕ, ∃ k, AsymptoticScaling.aRun 2 β * (N : ℝ) ≤ R k
  R_pos : ∀ k, 0 < R k
  R_step : ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k
  κ : ℕ → Type
  [κfin : ∀ k, Fintype (κ k)]
  v : ∀ k, κ k → Lp ℝ 2 (hSN 2 n i)
  span : ∀ k, ElectricLoops.shell (hSN 2 n i) (φ g₀) (AsymptoticScaling.aRun 2 β) R k
    ≤ Submodule.span ℝ (Set.range (v k))
  lam : ℕ → ℝ
  lam_pos : ∀ k, 0 < lam k
  gram : ∀ k (a : κ k → ℝ), lam k * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v k j‖ ^ 2
  /-- Bookkeeping: the spanning vectors are continuous slice functions (argued: eigenfunctions with
  `μ ≠ 0` are continuous, the kernel being continuous; not built). -/
  q : ∀ k, κ k → C(Slice n i, ℝ)
  hq : ∀ k j, (v k j : Slice n i → ℝ) =ᵐ[hSN 2 n i] q k j
  τ : Fin 4
  p : ℤ
  s : ℕ
  η : ℕ → ℝ
  M : ℕ → ℝ
  shells : ℕ → ℕ
  /-- Physics, open: the block contraction of the reflected lift at a box its shifted copy does not read. -/
  contract : ∀ k j, ∃ Δ : Finset ILink,
    ScaleControl.BlockContract β Δ (ireflObs τ (2 * p) (lift i (q k j))) α V D B (shells k) ∧
      (∀ (u : VConf (SUN.SU 2) Δ) (ω : IConf (SUN.SU 2)),
        (⇑(ishiftObsL τ))^[s] (lift i (q k j)) (splice Δ u ω) = (⇑(ishiftObsL τ))^[s] (lift i (q k j)) ω) ∧
      ∀ ω, |(⇑(ishiftObsL τ))^[s] (lift i (q k j)) ω| ≤ M k
  /-- The normalisation factor carrying the normalised periodic covariance to kernel scale (at step `0`,
  `bridge_step0`: `Z = Zc_{n−1}(1)`). -/
  Z : ℝ
  Z0 : 0 ≤ Z
  /-- Physics, open: the diagonal slice–periodic comparison of the lift, with error `η_k`. `‖T v‖²` is at
  kernel scale and the periodic covariance is normalised, so the covariance enters times `Z`
  (`bridge_step0` writes `η_k` at step `0` as `sliceErr + Zc · (discErr + volErr)`). -/
  bridge : ∀ k j,
    ‖kernelCLM (trivKN 2 β n i) C kmeas C0 kbd (hSN 2 n i) (hSN 2 n i) (v k j)‖ ^ 2
    ≤ Z * |stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) (ireflObs τ (2 * p) (lift i (q k j)))
        ((⇑(ishiftObsL τ))^[s] (lift i (q k j)))| + η k
  rate : ∀ k, (Fintype.card (κ k) : ℝ) * (Z * (2 * M k * (B * (α ^ shells k * V) * D)) + η k)
    ≤ lam k * (μ g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * AsymptoticScaling.aRun 2 β))))
  count : GlueballArea.ZeroFluxCount g₀ E t₀ Cc

/-- **One `SliceControl'` record gives the gap on that slice** at `diagRate c c' σ δ (n a)`. -/
theorem zeroFluxGap_of_sliceControl' {c c' σ δ α V D B t₀ Cc β : ℝ} {n : ℕ} {i : Fin 4}
    (hβ : 0 < β) (hn : 0 < n) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hδ : 0 < c * σ * δ)
    (hα : 0 ≤ α) (hV : 0 ≤ V) (hD : 0 ≤ D) (S : SliceControl' c c' σ δ α V D B t₀ Cc β n i) :
    GlueballArea.ZeroFluxGap S.g₀ S.E (LoopZoom.diagRate c c' σ δ ((n : ℝ) * AsymptoticScaling.aRun 2 β)) := by
  letI := S.κfin
  have hpos : ∀ j : {j : Fin 4 // j ≠ i}, 0 < CentreSectorSeed.Tr n i j := fun j => by
    simp only [CentreSectorSeed.Tr, RectWilson.tr, DoublingWilson.ext]
    positivity
  let y₀ : RectWilson.TT i (CentreSectorSeed.Tr n i) := fun j => ⟨0, hpos j⟩
  have hgen := MassGap.LoopsGenerate.excited_mem_closure_loops hβ S.levels S.meas y₀
  have hdiag : ∀ k j,
      ‖kernelCLM (trivKN 2 β n i) S.C S.kmeas S.C0 S.kbd (hSN 2 n i) (hSN 2 n i) (S.v k j)‖ ^ 2
        ≤ S.Z * (2 * S.M k * (B * (α ^ S.shells k * V) * D)) + S.η k := by
    intro k j
    obtain ⟨Δ, hK, hY, hYM⟩ := S.contract k j
    have hcov := MassGap.BoxFocusTest.cov_le_of_kernelNear (two_ne_zero : (2 : ℕ) ≠ 0) β Δ _ _ hY hYM
      (ScaleControl.kernelNear_of_blockContract hα hV hD hK)
    have hb := S.bridge k j
    have hZ := mul_le_mul_of_nonneg_left hcov S.Z0
    linarith
  refine MassGap.FocusFeed.zeroFluxGap_of_shellPairs hβ hn S.levels S.meas S.kmeas S.C0 S.kbd
    S.R_mono S.R_reach hgen hc hc' hσ hδ S.R_pos S.R_step S.κ S.v S.span S.lam S.lam_pos S.gram
    (fun k => S.Z * (2 * S.M k * (B * (α ^ S.shells k * V) * D)) + S.η k) ?_ S.rate
  intro k j l
  exact abs_inner_le_of_norm_sq_le (hdiag k j) (hdiag k l)

end MassGap.SliceLift

#print axioms MassGap.SliceLift.readAt_surjective
#print axioms MassGap.SliceLift.liftAt_injective
#print axioms MassGap.SliceLift.lift_eq_zero_iff
#print axioms MassGap.SliceLift.shift_liftAt
#print axioms MassGap.SliceLift.Tr_zero
#print axioms MassGap.SliceLift.torus_lift_pair_gen
#print axioms MassGap.SliceLift.torus_lift_pair
#print axioms MassGap.SliceLift.inner_kernelCLM_self
#print axioms MassGap.SliceLift.bridge_step0
#print axioms MassGap.SliceLift.abs_inner_le_of_norm_sq_le
#print axioms MassGap.SliceLift.zeroFluxGap_of_sliceControl'
