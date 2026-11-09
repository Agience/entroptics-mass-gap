import Mathlib
import MassGap.SliceFormPlane
import MassGap.RelativeDecay

/-!
# MassGap.RefPassageLow — `hpos` needs only the lower side of the reference passage

`TorusPassageProof.RefPassage hN M₀ O t ℓ ε` is the two-sided relative bound
`|R_∞ k − R_T k| ≤ ε R_T k` eventually in `k`, with `R_∞ = ExistenceReduce.refReading hN O t ℓ`
(the reference reading in `stateK hN`) and `R_T = refReadingS (stateT hN M₀) O t ℓ` (the same
reading on the fixed physical torus). The positivity `hpos` reads only its lower side.

* `RefPassageLow hN M₀ O t ℓ c`: eventually in `k`, `c · R_T k ≤ R_∞ k`. The infinite-volume
  reference reading is at least the fraction `c` of the torus one; the comparison is relative to
  the torus reading, with no absolute scale.
* `refPassageLow_of_refPassage`: `RefPassage` at `ε` gives `RefPassageLow` at `c = 1 − ε`.
* `refPassageLow_mono`: under `TorusRefPos`, `RefPassageLow` at `c` gives it at every `c' ≤ c`.
* `refPassageLow_iff_excess`: at `c > 0`, `RefPassageLow` at `c` is `R_T k − R_∞ k ≤ (c⁻¹ − 1) R_∞ k`
  eventually: the excess of the torus reading over the infinite-volume one, measured against the
  infinite-volume reading, with no bound on the size of `c⁻¹ − 1`. It is the one-sided form of
  `RelativeDecay.refRel_of_relInf`, without that lemma's `δ < 1`.
* `hpos_of_refPassageLow`: `TorusRefPos` and `RefPassageLow` at some `c > 0` give the pinned
  `∀ᶠ k, 0 < refReading hN O t ℓ k`.
* `clay_canonical_planePlaq_low`: `ExistenceReduce.clay_canonical` at `O = planePlaq N`, for
  `2 ≤ N`, `0 < t`, `0 < ℓ`, `2(t + ℓ) < M₀ · aRun N 1`, with `hpos` replaced by
  `∃ c > 0, RefPassageLow hN M₀ (planePlaq N) t ℓ c`. `TorusRefPos` is supplied by
  `TorusRefPosPlane.torusRefPos_of_sliceForm` and `SliceFormPlane.sliceForm_planePlaq`.

`RefPassageLow` drops the upper side `R_∞ ≤ (1 + ε) R_T` and allows any positive fraction `c`.
At `ε < 1` the upper side caps `R_∞/R_T` below `2`; `RefPassageLow` has no cap.

## The lower side is not a consequence of a gap (proved, witness)

`wTorus_lower_fails`: on the two-level closed chain of `RelativeDecay` (kernel `diag(1, μ)`, gap
`1 − μ`, insertion `diag(0, 1)`), at every `0 < μ`, `n ≤ L` and `c > 0`, the vacuum reading is
strictly below `c` times the torus reading. The torus reading is the thermal floor `p − p²`,
`p = μᴸ/(1 + μᴸ)`, and the vacuum reading is `0`. So a gap and reflection positivity do not give the
lower side: it needs the vacuum-connected part of the insertion to carry a fixed fraction of the
torus reading, which an insertion orthogonal to the vacuum's excitations does not.

## What it asks (argued)

Under the ultrafilter `R_∞ k` is the limit over the tori `2j + 2` at the same `β_k` of their readings,
so `RefPassageLow` asks that eventually in `k` the torus of physical side `M₀ · aRun N 1 + 2a_k` does
not inflate the reading by more than `1/c` over the larger tori. A monotone decrease of the reading in
the extent would give the opposite side, `R_∞ ≤ R_T`. For free fields (computed, not proved) the ratio
`R_∞/R_T` at fixed physical side converges as `a → 0` to a positive constant of the continuum
geometry: massive, it is below `1` (every image term adds); massless with the zero mode removed it
can exceed `2`, where `RefPassage` fails at every `ε < 1` and `RefPassageLow` holds at `c = 1`.

Classification: weaker-implies. `hpos` at the plane plaquette reduces to `RefPassageLow` at some
`c > 0`, which `RefPassage` at `ε < 1` implies. This is a reduction, not a discharge.
-/

noncomputable section

namespace MassGap.PassageLow

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone Filter

variable {N : ℕ}

/-- **The lower side of the reference passage.** Eventually in `k`, the infinite-volume reference
reading is at least `c` times the reference reading on the fixed physical torus `stateT hN M₀ k`. -/
def RefPassageLow (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ c : ℝ) : Prop :=
  ∀ᶠ k in atTop, c * refReadingS (stateT hN M₀) O t ℓ k ≤ ExistenceReduce.refReading hN O t ℓ k

/-- **`RefPassage` at `ε` gives `RefPassageLow` at `1 − ε`.** -/
theorem refPassageLow_of_refPassage (hN : N ≠ 0) {M₀ : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ ε : ℝ} (h : TorusPassageProof.RefPassage hN M₀ O t ℓ ε) :
    RefPassageLow hN M₀ O t ℓ (1 - ε) := by
  filter_upwards [h] with k hp
  have h2 := (abs_sub_le_iff.mp hp).2
  linarith

/-- **`RefPassageLow` is monotone in the fraction** once the torus reading is positive. -/
theorem refPassageLow_mono (hN : N ≠ 0) {M₀ : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ c c' : ℝ}
    (hposT : TorusRefPos hN M₀ O t ℓ) (hcc : c' ≤ c) (h : RefPassageLow hN M₀ O t ℓ c) :
    RefPassageLow hN M₀ O t ℓ c' := by
  filter_upwards [hposT, h] with k hk hp
  exact le_trans (mul_le_mul_of_nonneg_right hcc hk.le) hp

/-- **The lower side as a bound on the torus excess**, measured against the infinite-volume reading. -/
theorem refPassageLow_iff_excess (hN : N ≠ 0) {M₀ : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ c : ℝ}
    (hc : 0 < c) :
    RefPassageLow hN M₀ O t ℓ c ↔ ∀ᶠ k in atTop,
      refReadingS (stateT hN M₀) O t ℓ k - ExistenceReduce.refReading hN O t ℓ k
        ≤ (c⁻¹ - 1) * ExistenceReduce.refReading hN O t ℓ k := by
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun k => ?_)
  set a := refReadingS (stateT hN M₀) O t ℓ k
  set b := ExistenceReduce.refReading hN O t ℓ k
  have h : (c⁻¹ - 1) * b = b / c - b := by ring
  rw [h, sub_le_sub_iff_right, le_div_iff₀ hc, mul_comm a c]

/-- **The lower side does not follow from a gap.** On the two-level closed chain, at every gap
`1 − μ` with `0 < μ`, every lag `n ≤ L` and every fraction `c > 0`, the vacuum reading is strictly
below `c` times the torus reading. -/
theorem wTorus_lower_fails {μ : ℝ} (hμ : 0 < μ) {L n : ℕ} (hn : n ≤ L) {c : ℝ} (hc : 0 < c) :
    RelativeDecay.wVacConn μ n < c * RelativeDecay.wTorusConn μ L n := by
  rw [RelativeDecay.wVacConn_eq]
  exact mul_pos hc (RelativeDecay.wTorusConn_pos hμ hn)

/-- **The pinned `hpos` from the lower side of the passage.** `TorusRefPos` and `RefPassageLow` at
some `c > 0` give `∀ᶠ k, 0 < refReading hN O t ℓ k`. -/
theorem hpos_of_refPassageLow (hN : N ≠ 0) {M₀ : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ c : ℝ}
    (hposT : TorusRefPos hN M₀ O t ℓ) (hc : 0 < c) (h : RefPassageLow hN M₀ O t ℓ c) :
    ∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k := by
  filter_upwards [hposT, h] with k hk hp
  exact lt_of_lt_of_le (mul_pos hc hk) hp

/-- **The pinned path at the plane plaquette with `hpos` reduced to the lower side of the passage.**
At `2 ≤ N`, `0 < t`, `0 < ℓ`, `2(t + ℓ) < M₀ · aRun N 1`: from `RefPassageLow` at some `c > 0`,
the pinned `hD` and `WDelta2`, the conclusion of `ExistenceReduce.clay_canonical`. -/
theorem clay_canonical_planePlaq_low (hN2 : 2 ≤ N) (hN : N ≠ 0) {t ℓ : ℝ} (ht : 0 < t)
    (hℓ : 0 < ℓ) {M₀ : ℕ} (hM : 2 * (t + ℓ) < M₀ * AsymptoticScaling.aRun N 1)
    (hL : ∃ c : ℝ, 0 < c ∧ RefPassageLow hN M₀ (ExistencePosNonnull.planePlaq N) t ℓ c)
    (hD : ContinuumSep.DiagBoundSep hN
      (Renorm.connected hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ) 0
      (ExistenceReduce.zCan_refl hN (ExistencePosNonnull.planePlaq N) t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ)) 0
        (Renorm.connected_reflCompat hN
          (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq N) t ℓ) 0
          (ExistenceReduce.zCan_refl hN (ExistencePosNonnull.planePlaq N) t ℓ)) hD) (5 * ℓ₀) := by
  obtain ⟨c, hc, hLc⟩ := hL
  exact ExistenceReduce.clay_canonical hN2 hN _ ht
    (hpos_of_refPassageLow hN
      (TorusRefPosPlane.torusRefPos_of_sliceForm hN
        (SliceFormPlane.sliceForm_planePlaq hN2 hN ht hℓ hM)) hc hLc) hD hℓ₀ hW

/-- **The plane-plaquette path from `RefPassage` factors through the lower side.** -/
theorem exists_refPassageLow_of_refPassage (hN : N ≠ 0) {M₀ : ℕ} {O : LField (MassGap.SUN.SU N)}
    {t ℓ ε : ℝ} (hε : ε < 1) (h : TorusPassageProof.RefPassage hN M₀ O t ℓ ε) :
    ∃ c : ℝ, 0 < c ∧ RefPassageLow hN M₀ O t ℓ c :=
  ⟨1 - ε, by linarith, refPassageLow_of_refPassage hN h⟩

end MassGap.PassageLow

#print axioms MassGap.PassageLow.refPassageLow_of_refPassage
#print axioms MassGap.PassageLow.refPassageLow_mono
#print axioms MassGap.PassageLow.refPassageLow_iff_excess
#print axioms MassGap.PassageLow.wTorus_lower_fails
#print axioms MassGap.PassageLow.hpos_of_refPassageLow
#print axioms MassGap.PassageLow.clay_canonical_planePlaq_low
#print axioms MassGap.PassageLow.exists_refPassageLow_of_refPassage
