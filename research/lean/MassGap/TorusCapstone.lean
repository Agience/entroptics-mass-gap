import Mathlib
import MassGap.ExistenceReduce

noncomputable section

/-!
# MassGap.TorusCapstone — the pinned path with the canonical normalisation read on a fixed physical torus

`ExistenceReduce.clay_canonical` reads every Schwinger function in `ContinuumSchwinger.stateK hN k =
PeriodicState.periodicState hN (dyBeta k)`, the infinite-volume periodic state (an ultralimit of the tori
`torusState hN (2j+1) (dyBeta k)` as `j → ∞` at fixed coupling). Its input `hpos` asks
`0 < refReading hN O t ℓ k` eventually: a strict inequality in an ultralimit, so a lower bound on the tori
uniform in the extent.

This module reads the normalisation and the inputs E (`hD`) and the reference positivity (`hpos`) on one
finite torus per step, of fixed physical side, and moves everything that is uniform in the volume into one
named comparison of the two states.

## State-generic readings

* `latSkRS σ ρ k F`: the renormalised Schwinger function of step `k` in an arbitrary per-step state `σ k`
  at spacing `dySpacing N k`; `connectedS σ Z` subtracts `σ k (O)`. At `σ = stateAlong hN βs` these are
  `latSkRAlong` and `Renorm.connectedAlong` (`latSkRAlong_eq_latSkRS`, `rfl`).
* `refReadingS`, `zCanS`, `latSkRS_zCanS`: the reflected reference cube-pair reading, the canonical factor
  `1/√(refReadingS)` and the reading `= 1` at that factor once the reading is positive, in any `σ`.
  `refReading_eq_refReadingS`: the pinned `refReading` is the instance `σ = stateK hN`.
* `DiagBoundSepS σ ρ τ`: E on the reflection diagonal, in `σ`.

## The fixed physical torus

`stateT hN M₀ k = torusState hN (2 · M₀ 2ᵏ + 1) (dyBeta k)`: the periodic Wilson state of extent
`2(M₀ 2ᵏ + 1)` at the step-`k` coupling. Its physical side is
`M₀ · aRun N 1 + 2 · dySpacing N k` (`stateT_physical_side`), fixed up to two lattice spacings.
It is shift and reflection invariant at every step (`stateT_shift`, `stateT_reflInvariant`).

## Inputs, each a typed Prop

* `TorusRefPos hN M₀ O t ℓ`: `0 < refReadingS (stateT hN M₀) O t ℓ k` eventually. At each `k` this is
  one strict inequality for one Wilson expectation on one finite torus; no constant is uniform in `k` or in
  the volume. Not proved here. Its finite-volume content is the strict positivity of the link-plane transfer
  kernel (Lüscher) on the reflected connected cube field (argued).
* `DiagBoundSepS (stateT hN M₀) (connectedS (stateT hN M₀) zCanT) 0`: E on the torus.
* `TorusPassage hN M₀ Z τ ε`: for every separated positive-time monomial `P`, eventually in `k`, the
  diagonal reflected reading of the capstone (infinite volume, `Renorm.connected hN Z`) is within `ε` of the
  same reading on the torus (`connectedS (stateT hN M₀) Z`). This is the infinite-volume passage. It is the
  one input uniform in `k`; the wrap-around terms it bounds are expected to be exponentially small in
  `M₀ · aRun N 1` times the physical gap (argued).
* `DoublingClay2.WDelta2 N ℓ₀`: (W_Δ) as pinned.

## The capstone

`clay_torus`: at `t > 0`, `TorusRefPos`, torus E, `TorusPassage` at some `ε < 1` and `WDelta2` give
`ClayRoutes.ClayContinuumPair` at the torus-canonical factor `zCanT hN M₀ O t ℓ`, window `5ℓ₀`.
`pairLowerBound_of_torus`: the reference reading is `1` on the torus, so at least `1 − ε` in infinite
volume. `diagBoundSep_of_torus`: the torus bound `C` gives `C + ε`.

## Scope

The conclusion is the pinned infinite-volume `ClayContinuumPair`. A conclusion read on the torus itself is
not available from the tree: `ContinuumCluster.DkAlong` (the transfer data behind `contDAlong` and
`TowerGapAt`) is `PeriodicState.periodicGaugeInvData`, reflection positivity on the whole gauge-invariant
half-space algebra, which a torus of fixed extent has only on observables of depth below its half-extent
(`PeriodicState.torusState_reflPositive_even_eventually`). `WDelta2` is a statement about the partition
functions of tori of fixed physical side, but its consequence `WeakCouplingWindow.FixedWindowDecay`, through
`DoublingClay2.DyadicTorusDecay`, is read along `PeriodicState.periodicUltra`, in infinite volume.
-/

namespace MassGap.TorusCapstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger Filter

variable {N : ℕ}

/-! ## 1. State-generic readings -/

section Generic

/-- The renormalised Schwinger function of step `k` in the per-step state `σ k`:
`∏ᵢ Z k Oᵢ · σ k (∏ᵢ smear aₖ (Oᵢ − c k Oᵢ) fᵢ)`, `aₖ = dySpacing N k`. -/
def latSkRS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (ρ : Renorm N) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SField N) : ℝ :=
  ρ.pref k F * latS (σ k) (dySpacing N k) (fun i => ρ.field k (F i))

/-- The connected composites `Z k O · (O − σ k (O))`. -/
def connectedS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) :
    Renorm N :=
  ⟨Z, fun k O => σ k O.1⟩

/-- At the periodic states along `βs` the generic reading is `latSkRAlong`. -/
theorem latSkRAlong_eq_latSkRS (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k F
      = latSkRS (stateAlong hN βs) (connectedS (stateAlong hN βs) Z) k F :=
  rfl

/-- The reflected reference cube-pair reading at unit field strength in `σ`. -/
def refReadingS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (k : ℕ) : ℝ :=
  latSkRS σ (connectedS σ (fun _ _ => 1)) k
    (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))

/-- The pinned reference reading is the instance `σ = stateK hN`. -/
theorem refReading_eq_refReadingS (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) :
    ExistenceReduce.refReading hN O t ℓ k = refReadingS (stateK hN) O t ℓ k :=
  rfl

/-- The canonical field-strength factor `1/√(refReadingS σ)`, the same for every field. -/
def zCanS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ℕ → LField (MassGap.SUN.SU N) → ℝ :=
  fun k _ => 1 / Real.sqrt (refReadingS σ O t ℓ k)

theorem zCanS_refl (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N))
    (t ℓ : ℝ) : ∀ k O', zCanS σ O t ℓ k (O'.refl 0) = zCanS σ O t ℓ k O' := fun _ _ => rfl

/-- **The reference reading is exactly `1` at the canonical factor**, in any per-step state. -/
theorem latSkRS_zCanS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (O : LField (MassGap.SUN.SU N))
    (t ℓ : ℝ) (k : ℕ) (hpos : 0 < refReadingS σ O t ℓ k) :
    latSkRS σ (connectedS σ (zCanS σ O t ℓ)) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ)) = 1 := by
  have hf : latS (σ k) (dySpacing N k) (fun i => (connectedS σ (zCanS σ O t ℓ)).field k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ) i))
      = refReadingS σ O t ℓ k := by
    show _ = (∏ _i : Fin 1 ⊕ Fin 1, (1 : ℝ)) * _
    rw [Finset.prod_const_one, one_mul]
    rfl
  have hcan : latSkRS σ (connectedS σ (zCanS σ O t ℓ)) k
      (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
      = (1 / Real.sqrt (refReadingS σ O t ℓ k)) ^ 2 * refReadingS σ O t ℓ k := by
    show (∏ _i : Fin 1 ⊕ Fin 1, 1 / Real.sqrt (refReadingS σ O t ℓ k)) * _ = _
    rw [hf, Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  rw [hcan, div_pow, one_pow, Real.sq_sqrt hpos.le, one_div, inv_mul_cancel₀ hpos.ne']

/-- **E on the reflection diagonal in `σ`**: each separated positive-time monomial `P` has one constant
bounding `latSkRS σ ρ k (θP ∪ P)` eventually in the step. -/
def DiagBoundSepS (σ : ℕ → MassGap.DLRLimit.State (Cfg N)) (ρ : Renorm N) (τ : Fin 4) : Prop :=
  ∀ P : ContinuumSep.SepMono N τ, ∃ C : ℝ, ∀ᶠ k in atTop, latSkRS σ ρ k (pairFam τ P.1 P.1) ≤ C

/-- At the periodic states along `dyBeta` the generic diagonal bound is the pinned `DiagBoundSep`. -/
theorem diagBoundSep_iff_S (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) τ
      ↔ DiagBoundSepS (stateK hN) (connectedS (stateK hN) Z) τ :=
  Iff.rfl

end Generic

/-! ## 2. The fixed physical torus -/

section Torus

/-- **The state of step `k` on the fixed physical torus**: the periodic Wilson state of extent
`2(M₀ 2ᵏ + 1)` at the coupling `dyBeta k`. -/
def stateT (hN : N ≠ 0) (M₀ : ℕ) (k : ℕ) : MassGap.DLRLimit.State (Cfg N) :=
  PeriodicState.torusState hN (2 * (M₀ * 2 ^ k) + 1) (dyBeta (one_le_of_ne_zero hN) k)

/-- **The physical side is fixed**: extent times spacing is `M₀ · aRun N 1 + 2 · dySpacing N k`. -/
theorem stateT_physical_side (M₀ k : ℕ) :
    ((2 * (M₀ * 2 ^ k) + 1 + 1 : ℕ) : ℝ) * dySpacing N k
      = M₀ * AsymptoticScaling.aRun N 1 + 2 * dySpacing N k := by
  unfold dySpacing
  push_cast
  have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
  rw [h2]
  field_simp
  ring

theorem stateT_shift (hN : N ≠ 0) (M₀ k : ℕ) (τ : Fin 4) (f : C(Cfg N, ℝ)) :
    stateT hN M₀ k (MassGap.ReflectionShift.ishiftObsL τ f) = stateT hN M₀ k f :=
  PeriodicState.torusState_shift hN _ _ τ f

theorem stateT_reflInvariant (hN : N ≠ 0) (M₀ k : ℕ) (τ : Fin 4) (c : ℤ) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c) (stateT hN M₀ k) :=
  PeriodicState.torusState_reflInvariant hN _ _ τ c

/-- The canonical factor read on the torus. -/
def zCanT (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ℕ → LField (MassGap.SUN.SU N) → ℝ :=
  zCanS (stateT hN M₀) O t ℓ

/-- **`hpos` on the torus.** Eventually in `k`, the reference reading on the torus of step `k` is
positive. One finite-volume strict inequality per step. -/
def TorusRefPos (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∀ᶠ k in atTop, 0 < refReadingS (stateT hN M₀) O t ℓ k

/-- **The infinite-volume passage on the reflection diagonal.** For every separated positive-time
monomial `P`, eventually in `k`, the capstone's reading `latSkR hN (Renorm.connected hN Z) k (θP ∪ P)`
is within `ε` of the torus reading `latSkRS (stateT hN M₀) (connectedS (stateT hN M₀) Z) k (θP ∪ P)`. -/
def TorusPassage (hN : N ≠ 0) (M₀ : ℕ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (ε : ℝ) : Prop :=
  ∀ P : ContinuumSep.SepMono N τ, ∀ᶠ k in atTop,
    |latSkR hN (Renorm.connected hN Z) k (pairFam τ P.1 P.1)
      - latSkRS (stateT hN M₀) (connectedS (stateT hN M₀) Z) k (pairFam τ P.1 P.1)| ≤ ε

end Torus

/-! ## 3. The capstone -/

section Capstone

/-- **E passes from the torus**: the torus bound `C` and the passage at `ε` give `C + ε`. -/
theorem diagBoundSep_of_torus (hN : N ≠ 0) (M₀ : ℕ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) {ε : ℝ} (hDT : DiagBoundSepS (stateT hN M₀) (connectedS (stateT hN M₀) Z) τ)
    (hpass : TorusPassage hN M₀ Z τ ε) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) τ := by
  show ∀ P : ContinuumSep.SepMono N τ, ∃ C : ℝ, ∀ᶠ k in atTop,
    latSkR hN (Renorm.connected hN Z) k (pairFam τ P.1 P.1) ≤ C
  intro P
  obtain ⟨C, hC⟩ := hDT P
  refine ⟨C + ε, ?_⟩
  filter_upwards [hC, hpass P] with k hk hp
  have h := (abs_sub_le_iff.mp hp).1
  linarith

/-- **The pair lower bound from the torus**: the torus reference reading is `1` at `zCanT`, so the
capstone's reading is at least `1 − ε`. -/
theorem pairLowerBound_of_torus (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t)
    {M₀ : ℕ} (hposT : TorusRefPos hN M₀ O t ℓ) {ε : ℝ} (hε : ε < 1)
    (hpass : TorusPassage hN M₀ (zCanT hN M₀ O t ℓ) 0 ε) :
    ClayReduce.PairLowerBound hN (zCanT hN M₀ O t ℓ) 0 := by
  refine ⟨O, t, ℓ, 1 - ε, ht, by linarith, ?_⟩
  filter_upwards [hposT, hpass (ContinuumNontrivial.sepCube 0 O ht ℓ)] with k hk hp
  have h1 : latSkRS (stateT hN M₀) (connectedS (stateT hN M₀) (zCanT hN M₀ O t ℓ)) k
      (pairFam 0 (ContinuumNontrivial.sepCube 0 O ht ℓ).1 (ContinuumNontrivial.sepCube 0 O ht ℓ).1)
      = 1 :=
    latSkRS_zCanS (stateT hN M₀) O t ℓ k hk
  have h2 := (abs_sub_le_iff.mp hp).2
  show 1 - ε ≤ latSkR hN (Renorm.connected hN (zCanT hN M₀ O t ℓ)) k
    (pairFam 0 (ContinuumNontrivial.sepCube 0 O ht ℓ).1 (ContinuumNontrivial.sepCube 0 O ht ℓ).1)
  linarith

/-- **The pinned path with the normalisation, `hpos` and E read on a fixed physical torus.** At `t > 0`,
torus `hpos`, torus E, the infinite-volume passage at some `ε < 1` and `WDelta2`:
`ClayRoutes.ClayContinuumPair` at the torus-canonical factor, window `5ℓ₀`. -/
theorem clay_torus (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) {M₀ : ℕ} (hposT : TorusRefPos hN M₀ O t ℓ)
    (hDT : DiagBoundSepS (stateT hN M₀) (connectedS (stateT hN M₀) (zCanT hN M₀ O t ℓ)) 0)
    {ε : ℝ} (hε : ε < 1) (hpass : TorusPassage hN M₀ (zCanT hN M₀ O t ℓ) 0 ε)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zCanT hN M₀ O t ℓ) 0 (zCanS_refl (stateT hN M₀) O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCanT hN M₀ O t ℓ)) 0
        (Renorm.connected_reflCompat hN (zCanT hN M₀ O t ℓ) 0 (zCanS_refl (stateT hN M₀) O t ℓ))
        (diagBoundSep_of_torus hN M₀ (zCanT hN M₀ O t ℓ) 0 hDT hpass)) (5 * ℓ₀) :=
  ExistenceReduce.clay_of_WDelta2_diag hN2 hN (zCanT hN M₀ O t ℓ) (zCanS_refl (stateT hN M₀) O t ℓ)
    (diagBoundSep_of_torus hN M₀ (zCanT hN M₀ O t ℓ) 0 hDT hpass) hℓ₀ hW
    (pairLowerBound_of_torus hN O ht hposT hε hpass)

end Capstone

end MassGap.TorusCapstone

#print axioms MassGap.TorusCapstone.latSkRAlong_eq_latSkRS
#print axioms MassGap.TorusCapstone.refReading_eq_refReadingS
#print axioms MassGap.TorusCapstone.latSkRS_zCanS
#print axioms MassGap.TorusCapstone.diagBoundSep_iff_S
#print axioms MassGap.TorusCapstone.stateT_physical_side
#print axioms MassGap.TorusCapstone.stateT_shift
#print axioms MassGap.TorusCapstone.stateT_reflInvariant
#print axioms MassGap.TorusCapstone.diagBoundSep_of_torus
#print axioms MassGap.TorusCapstone.pairLowerBound_of_torus
#print axioms MassGap.TorusCapstone.clay_torus
