import Mathlib
import MassGap.TorusCapstone

noncomputable section

/-!
# MassGap.TorusPassageProof — what `TorusPassage` asks of the gap, and the part `hpos` needs

`TorusCapstone.TorusPassage hN M₀ Z 0 ε` compares, for every separated positive-time monomial `P`, the
infinite-volume reading `latSkR hN (Renorm.connected hN Z) k (θP ∪ P)` with the reading on the fixed physical
torus `stateT hN M₀ k`. This module reads its reference instance exactly and places the torus of `stateT`
against the tori on which the tree's gap is proved.

## The reference instance is a ratio

* `latSkRS_zCanS_ref`: in any state `σ`, at the canonical factor of any state `σ'` with
  `0 ≤ refReadingS σ'`, the reference reading is `refReadingS σ / refReadingS σ'`.
* `latSkR_zCanT_ref`: the capstone's reference reading at `zCanT` is `refReading k / refReadingS (stateT) k`.
* `refPassage_step_iff`: at a step with a positive torus reference reading, the `TorusPassage` inequality at the
  reference cube pair holds exactly when `|refReading k − refReadingS (stateT) k| ≤ ε · refReadingS (stateT) k`.
* `RefPassage hN M₀ O t ℓ ε`: that inequality eventually in `k`. `refPassage_of_torusPassage`: `TorusPassage`
  at `zCanT` gives it; `refPassage_iff`: under `TorusRefPos`, it is the reference instance of `TorusPassage`.

The passage is therefore a bound on the infinite-minus-torus difference relative to the torus reading itself,
at every step. A bound `C · e^{−m L}` with `C` uniform in `k` gives it only if the torus reading
`refReadingS (stateT) k` stays above `C e^{−m L}/ε` at every large `k`.

## `hpos` from the reference instance alone

* `hpos_of_refPassage`: `TorusRefPos` and `RefPassage` at `ε < 1` give the pinned
  `∀ᶠ k, 0 < refReading hN O t ℓ k`.
* `clay_canonical_refPassage`: `ExistenceReduce.clay_canonical` with `hpos` replaced by `TorusRefPos` and
  `RefPassage` at `ε < 1`; `hD` stays pinned at `zCan`, so no other monomial is compared.

## The torus of `stateT` is not one the tree's gap reads

* `stateT_extent_not_pow2`: at `M₀ ≥ 1`, `k ≥ 1` the extent `2(M₀ 2ᵏ + 1)` is not a power of two.
* `stateT_index_not_dyadic`: the index `M₀ 2ᵏ` lies in no seed set
  `{j | ∃ k', 2j + 2 = 2^{k'} 2^{a+1}}` of `PeriodicDyadic.periodicUltra_seed_mem`.
  `TorusDecay.dyadic_torus_decay` (the content of `DoublingClay2.DyadicTorusDecay`) is proved on exactly those
  tori, so it says nothing about `stateT hN M₀ k` at `k ≥ 1`.

## What the tree's gap provides (read from the proofs)

`DoublingClay2.DyadicTorusDecay hN` (proved, `dyadicTorusDecay`): at `β ≥ 0` and a power-of-two seed `n ≥ 2`
with `16 log ZR(n⁴) − log ZR((2n)⁴) ≤ 1/1000`, for every `x` in the gauge-invariant half-space algebra at
`(τ, p) = (0, 0)` and every `ε > 0`, eventually along `periodicUltra hN β`,
`torusConn 0 0 hN β j x n ≤ ½ · torusConn 0 0 hN β j x 0 + ε`. On the dyadic cubic torus of extent `2ᵏ n`
its proof has the transfer gap `‖Kⁿ f‖ ≤ ½ ‖K‖ⁿ ‖f‖` of the time-direction kernel of that torus's own spatial
slice, the excited weight `s ≤ (1/2)^{2^k}` (`DoublingSharp.excited_le_corner_sharp`), and the closing error `100 B² √(2s)` with `B` the sup norm of
`x`. `WeakCouplingWindow.FixedWindowDecay 0 0 hN (5ℓ₀)` (from `WDelta2`, `fixedWindowDecay_of_WDelta2`) is that
statement at the seed `nP N ℓ₀ β`, at every large `β`. Neither compares two tori: each bounds a connected
pairing inside one torus, with an additive error measured by the sup norm.

The obstruction (argued). Every torus in the tree is cubic, so going from one torus to a larger one changes
the spatial slice and with it the transfer kernel; the time-direction gap of one slice does not compare two
slices. A comparison through rectangular tori, one direction at a time, would need rectangular torus states and
their gaps, which the tree does not have. Granting such a comparison, its error is additive in the sup norm
`B ≍ 1` of the smeared field, while the reference reading is the connected reflected correlation of that field,
which is expected to vanish as `a_k → 0`; `RefPassage` at a fixed `M₀` needs the error below `ε` times that
reading at every large `k`.
-/

namespace MassGap.TorusPassageProof

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone Filter

variable {N : ℕ}

/-! ## 1. The reference instance of the passage is a ratio -/

section Ratio

/-- **The reference reading at another state's canonical factor.** In `σ`, at `zCanS σ'` with
`0 ≤ refReadingS σ'`: `refReadingS σ / refReadingS σ'`. -/
theorem latSkRS_zCanS_ref (σ σ' : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N))
    (t ℓ : ℝ) (k : ℕ) (h' : 0 ≤ refReadingS σ' O t ℓ k) :
    latSkRS σ (connectedS σ (zCanS σ' O t ℓ)) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
      = refReadingS σ O t ℓ k / refReadingS σ' O t ℓ k := by
  have hf : latS (σ k) (dySpacing N k) (fun i => (connectedS σ (zCanS σ' O t ℓ)).field k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ) i))
      = refReadingS σ O t ℓ k := by
    show _ = (∏ _i : Fin 1 ⊕ Fin 1, (1 : ℝ)) * _
    rw [Finset.prod_const_one, one_mul]
    rfl
  have hcan : latSkRS σ (connectedS σ (zCanS σ' O t ℓ)) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
      = (1 / Real.sqrt (refReadingS σ' O t ℓ k)) ^ 2 * refReadingS σ O t ℓ k := by
    show (∏ _i : Fin 1 ⊕ Fin 1, 1 / Real.sqrt (refReadingS σ' O t ℓ k)) * _ = _
    rw [hf, Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  rw [hcan, div_pow, one_pow, Real.sq_sqrt h']
  ring

/-- **The capstone's reference reading at the torus-canonical factor** is `refReading k / refReadingS (stateT) k`. -/
theorem latSkR_zCanT_ref (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ)
    (hT : 0 ≤ refReadingS (stateT hN M₀) O t ℓ k) :
    latSkR hN (Renorm.connected hN (zCanT hN M₀ O t ℓ)) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
      = ExistenceReduce.refReading hN O t ℓ k / refReadingS (stateT hN M₀) O t ℓ k :=
  latSkRS_zCanS_ref (stateK hN) (stateT hN M₀) O t ℓ k hT

/-- **The passage inequality at the reference cube pair, at one step**, is the relative bound
`|refReading − refReadingS (stateT)| ≤ ε · refReadingS (stateT)`, once the torus reading is positive. -/
theorem refPassage_step_iff (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ ε : ℝ) (k : ℕ)
    (hT : 0 < refReadingS (stateT hN M₀) O t ℓ k) :
    |latSkR hN (Renorm.connected hN (zCanT hN M₀ O t ℓ)) k
        (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
      - latSkRS (stateT hN M₀) (connectedS (stateT hN M₀) (zCanT hN M₀ O t ℓ)) k
        (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))| ≤ ε
    ↔ |ExistenceReduce.refReading hN O t ℓ k - refReadingS (stateT hN M₀) O t ℓ k|
        ≤ ε * refReadingS (stateT hN M₀) O t ℓ k := by
  have h1 : latSkRS (stateT hN M₀) (connectedS (stateT hN M₀) (zCanT hN M₀ O t ℓ)) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ)) = 1 :=
    latSkRS_zCanS (stateT hN M₀) O t ℓ k hT
  rw [latSkR_zCanT_ref hN M₀ O t ℓ k hT.le, h1]
  have hdiff : ExistenceReduce.refReading hN O t ℓ k / refReadingS (stateT hN M₀) O t ℓ k - 1
      = (ExistenceReduce.refReading hN O t ℓ k - refReadingS (stateT hN M₀) O t ℓ k)
        / refReadingS (stateT hN M₀) O t ℓ k := by
    field_simp
  rw [hdiff, abs_div, abs_of_pos hT, div_le_iff₀ hT]

/-- **The reference instance of the passage**, as a relative bound eventually in the step. -/
def RefPassage (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ ε : ℝ) : Prop :=
  ∀ᶠ k in atTop, |ExistenceReduce.refReading hN O t ℓ k - refReadingS (stateT hN M₀) O t ℓ k|
    ≤ ε * refReadingS (stateT hN M₀) O t ℓ k

/-- `TorusPassage` at the torus-canonical factor gives its reference instance. -/
theorem refPassage_of_torusPassage (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t)
    {M₀ : ℕ} (hposT : TorusRefPos hN M₀ O t ℓ) {ε : ℝ}
    (hpass : TorusPassage hN M₀ (zCanT hN M₀ O t ℓ) 0 ε) : RefPassage hN M₀ O t ℓ ε := by
  filter_upwards [hposT, hpass (ContinuumNontrivial.sepCube 0 O ht ℓ)] with k hk hp
  exact (refPassage_step_iff hN M₀ O t ℓ ε k hk).mp hp

/-- **Under `TorusRefPos`, `RefPassage` is the reference instance of `TorusPassage`.** -/
theorem refPassage_iff (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} {M₀ : ℕ}
    (hposT : TorusRefPos hN M₀ O t ℓ) (ε : ℝ) :
    RefPassage hN M₀ O t ℓ ε ↔ ∀ᶠ k in atTop,
      |latSkR hN (Renorm.connected hN (zCanT hN M₀ O t ℓ)) k
          (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
        - latSkRS (stateT hN M₀) (connectedS (stateT hN M₀) (zCanT hN M₀ O t ℓ)) k
          (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))| ≤ ε := by
  constructor
  · intro h
    filter_upwards [hposT, h] with k hk hp
    exact (refPassage_step_iff hN M₀ O t ℓ ε k hk).mpr hp
  · intro h
    filter_upwards [hposT, h] with k hk hp
    exact (refPassage_step_iff hN M₀ O t ℓ ε k hk).mp hp

end Ratio

/-! ## 2. `hpos` from the reference instance -/

section Hpos

/-- **The pinned `hpos` from the torus**: `TorusRefPos` and `RefPassage` at `ε < 1` give
`∀ᶠ k, 0 < refReading hN O t ℓ k`; the infinite-volume reading is at least `(1 − ε)` times the torus one. -/
theorem hpos_of_refPassage (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} {M₀ : ℕ}
    (hposT : TorusRefPos hN M₀ O t ℓ) {ε : ℝ} (hε : ε < 1) (h : RefPassage hN M₀ O t ℓ ε) :
    ∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k := by
  filter_upwards [hposT, h] with k hk hp
  have h2 := (abs_sub_le_iff.mp hp).2
  have h3 : 0 < (1 - ε) * refReadingS (stateT hN M₀) O t ℓ k := mul_pos (by linarith) hk
  nlinarith

/-- **The pinned path with `hpos` read on the torus through the reference instance only.** At `t > 0`,
`TorusRefPos`, `RefPassage` at some `ε < 1`, the pinned `hD` and `WDelta2`: the conclusion of
`ExistenceReduce.clay_canonical`. -/
theorem clay_canonical_refPassage (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) {M₀ : ℕ} (hposT : TorusRefPos hN M₀ O t ℓ) {ε : ℝ} (hε : ε < 1)
    (hR : RefPassage hN M₀ O t ℓ ε)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  ExistenceReduce.clay_canonical hN2 hN O ht (hpos_of_refPassage hN O hposT hε hR) hD hℓ hW

end Hpos

/-! ## 3. The torus of `stateT` is not a dyadic torus -/

section Dyadic

/-- **The extent of `stateT` is not a power of two** at `M₀ ≥ 1`, `k ≥ 1`: it is twice the odd number
`M₀ 2ᵏ + 1 ≥ 3`. -/
theorem stateT_extent_not_pow2 {M₀ k : ℕ} (hM : 1 ≤ M₀) (hk : 1 ≤ k) :
    ¬ PeriodicState.IsPow2 (2 * (M₀ * 2 ^ k) + 1 + 1) := by
  rintro ⟨b, hb⟩
  have hY : 0 < M₀ * 2 ^ k := Nat.mul_pos (by omega) (Nat.two_pow_pos k)
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  have hm : M₀ * 2 ^ (c + 1) = M₀ * 2 ^ c + M₀ * 2 ^ c := by rw [pow_succ]; ring
  generalize M₀ * 2 ^ c = m at hm
  generalize M₀ * 2 ^ (c + 1) = Y at hb hm hY
  rcases b with _ | _ | b
  · simp at hb
  · simp at hb; omega
  · rw [pow_succ, pow_succ] at hb
    generalize 2 ^ b = X at hb
    omega

/-- **The index of `stateT` lies in no dyadic seed set** of `PeriodicDyadic.periodicUltra_seed_mem`, the
sets on which `TorusDecay.dyadic_torus_decay` is proved. -/
theorem stateT_index_not_dyadic {M₀ k : ℕ} (hM : 1 ≤ M₀) (hk : 1 ≤ k) (a : ℕ) :
    M₀ * 2 ^ k ∉ {j : ℕ | ∃ k' : ℕ, 2 * j + 2 = 2 ^ k' * 2 ^ (a + 1)} := by
  rintro ⟨k', hk'⟩
  exact stateT_extent_not_pow2 hM hk ⟨k' + (a + 1), by rw [pow_add]; omega⟩

end Dyadic

end MassGap.TorusPassageProof

#print axioms MassGap.TorusPassageProof.latSkRS_zCanS_ref
#print axioms MassGap.TorusPassageProof.latSkR_zCanT_ref
#print axioms MassGap.TorusPassageProof.refPassage_step_iff
#print axioms MassGap.TorusPassageProof.refPassage_of_torusPassage
#print axioms MassGap.TorusPassageProof.refPassage_iff
#print axioms MassGap.TorusPassageProof.hpos_of_refPassage
#print axioms MassGap.TorusPassageProof.clay_canonical_refPassage
#print axioms MassGap.TorusPassageProof.stateT_extent_not_pow2
#print axioms MassGap.TorusPassageProof.stateT_index_not_dyadic
