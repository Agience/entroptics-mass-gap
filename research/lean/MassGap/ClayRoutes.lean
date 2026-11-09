import Mathlib
import MassGap.ContinuumClay

noncomputable section

/-!
# MassGap.ClayRoutes — the continuum Clay statement from each route to the uniform physical gap

`ContinuumClay.continuum_gap_nontrivial` concludes, at every dyadic step `m`, that the reconstructed
continuum transfer data `ContinuumClay.contD hN Z τ hZ hB m` is `ContinuumClay.GappedAt` a rate of
physical mass at least `c/L` and is `ContinuumClay.NontrivialVacuum`. `ClayContinuumPair hN Z τ hZ hB L`
names that conclusion at a witness `hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ`;
`ClayContinuum hN Z τ hZ hB L`, at `hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)`, is
`ClayContinuumPair` at the witness `ContinuumSep.pairBoundSep_of_uniformBoundSep`. The witness enters
only proof fields, so `ClayContinuum` and `ClayContinuumPair` at any witnesses are the same
proposition (`clayContinuum_iff_pair`). Its requirement M input is
`WeakCouplingWindow.FixedWindowDecay τ 0 hN L`; this module assembles it into `ClayContinuum`.

* `clay_continuum_pair_of_fixedWindowDecay`: the capstone with E as `PairBoundSep` and M as the single
  Prop `FixedWindowDecay`; `clay_continuum_of_fixedWindowDecay`, the same with E as `UniformBoundSep`.
* `stepConn` is the step-`n` connected pairing of two observables under a law `m n`, and
  `ChiCarrierBridge` is the carrier match between a class of observable pairs indexed by `S` with
  window pairs `(aw i, bw i)` and lag-zero pairs `(a0 i, b0 i)` along dyadic steps of
  infinite-volume observer laws, and the periodic tori along `PeriodicState.periodicUltra` at every
  large real `β` on `gaugeInvHalfSpaceAlg`, the carrier `FixedWindowDecay` reads.

## Open inputs of the Clay continuum statement, by requirement

Fixed data: a colour count `2 ≤ N`, a field-strength factor `Z` with its reflection invariance
`hZ`, a time direction `τ : Fin 4`, a window `0 < L`, a field `O` and a radial profile `G`.

* **E** — `ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)`: for every family and every
  `d > 0`, one constant bounding, eventually in the step, the renormalised lattice Schwinger function
  of every dyadic translate of the family whose supports are pairwise `d`-separated. The capstone reads
  it only as `ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ` (`ClayContinuumPair`): for each
  pair of separated positive-time monomials, one constant bounding the reflected pair at every common
  dyadic time shift. `ClayReduce.clay_continuum_of_diagBoundSep` takes it as
  `ContinuumSep.DiagBoundSep`, the bound on the unshifted reflection diagonal `θP ∪ P` alone.
* **N** — `ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
  (fun p q => G (ContinuumNontrivial.eDist p q))`: the renormalised lattice kernel of `O` converging
  to `G(|p − q|)` uniformly on every separated box `ContinuumNontrivial.sepBoxSet d R`, `d > 0`.
* **Y** — `ShortDistanceY.AFShortDistance G`: `r⁸ · G(r) · (log r)² → C` as `r → 0⁺`, some `C > 0`.
* **M** — `WeakCouplingWindow.FixedWindowDecay τ 0 hN L`, as one Prop; `ChiCarrierBridge τ 0 hN L m S
  aw bw a0 b0` matches the forest carrier to the periodic carrier it reads.

Outside the statement: rotation invariance off the hypercubic group,
`ContinuumHypercubic.RotationOpen`; and the choice of ultrafilter behind `ContinuumSchwinger.contS`.
-/

namespace MassGap.ClayRoutes

variable {N : ℕ}

/-! ## 1. The conclusion, named -/

section Capstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **The Clay continuum conclusion at window `L` along the coupling tower `βs`**, at a pair-bound
witness: some `c > 0` has, at every dyadic step `m`, the reconstructed transfer data
`ContinuumClay.contDAlong hN βs Z τ hZ hB m` `ContinuumClay.GappedAt` the rate
`e^{−(c/L)·dySpacing N m}` and `ContinuumClay.NontrivialVacuum`.

DERIVED: `0` is the excluded colour count and the lower end of `c`; `4` in `Fin 4` is the spacetime
dimension. -/
def ClayContinuumPairAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSepAlong hN βs (Renorm.connectedAlong hN βs Z) τ) (L : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
    ContinuumClay.GappedAt (ContinuumClay.contDAlong hN βs Z τ hZ hB m)
        (Real.exp (-(c / L) * dySpacing N m))
      ∧ ContinuumClay.NontrivialVacuum (ContinuumClay.contDAlong hN βs Z τ hZ hB m)

/-- **The Clay continuum conclusion at window `L`, at a pair-bound witness.** Some `c > 0` has, at
every dyadic step `m`, the reconstructed transfer data `ContinuumClay.contD hN Z τ hZ hB m`
`ContinuumClay.GappedAt` the rate `e^{−(c/L)·dySpacing N m}` and `ContinuumClay.NontrivialVacuum` — the
conclusion of `ContinuumClay.continuum_gap_nontrivial`: `ClayContinuumPairAlong` at the couplings
`dyBeta`. `hB` enters only proof fields of `contD`.

DERIVED: `0` is the excluded colour count and the lower end of `c`; `4` in `Fin 4` is the spacetime
dimension. -/
def ClayContinuumPair (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) (L : ℝ) : Prop :=
  ClayContinuumPairAlong hN (dyBeta (one_le_of_ne_zero hN)) Z τ hZ hB L

/-- `ClayContinuumPair` is `ClayContinuumPairAlong` at the couplings `dyBeta`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem clayContinuumPair_iff_along (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) (L : ℝ) :
    ClayContinuumPair hN Z τ hZ hB L
      ↔ ClayContinuumPairAlong hN (dyBeta (one_le_of_ne_zero hN)) Z τ hZ hB L :=
  Iff.rfl

/-- **The Clay continuum conclusion at window `L`.** `ClayContinuumPair` at the pair-bound witness
that `ContinuumSep.pairBoundSep_of_uniformBoundSep` gives from `hB` and the reflection compatibility
`Renorm.connected_reflCompat hN Z τ hZ`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def ClayContinuum (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) (L : ℝ) : Prop :=
  ClayContinuumPair hN Z τ hZ
    (ContinuumSep.pairBoundSep_of_uniformBoundSep hN (Renorm.connected hN Z) τ
      (Renorm.connected_reflCompat hN Z τ hZ) hB) L

/-- **The witness is immaterial**: `ClayContinuum` at any `UniformBoundSep` witness and
`ClayContinuumPair` at any `PairBoundSep` witness are the same proposition. Both witnesses are proofs,
and `contD` reads them only in proof fields, so the two sides are definitionally equal by proof
irrelevance.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem clayContinuum_iff_pair (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z))
    (hB' : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) (L : ℝ) :
    ClayContinuum hN Z τ hZ hB L ↔ ClayContinuumPair hN Z τ hZ hB' L :=
  Iff.rfl

#print axioms clayContinuum_iff_pair

/-- **The capstone with E as the pair bound and requirement M as one Prop.** At `2 ≤ N`, a
reflection-invariant `Z`, `ContinuumSep.PairBoundSep` at `Renorm.connected hN Z` (E), a window `L > 0`,
`WeakCouplingWindow.FixedWindowDecay τ 0 hN L` (M), `ContinuumNontrivial.KernelConvergesSep` towards a
radial `G` (N) and `ShortDistanceY.AFShortDistance G` (Y): `ClayContinuumPair hN Z τ hZ hB L`
(`ContinuumClay.continuum_gap_nontrivial`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
lower end of `L`, and the reflection plane offset `p = 0` that `continuum_gap_nontrivial` reads
`FixedWindowDecay` at; `4` in `Fin 4` is the spacetime dimension. -/
theorem clay_continuum_pair_of_fixedWindowDecay (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuumPair hN Z τ hZ hB L :=
  ContinuumClay.continuum_gap_nontrivial hN2 hN Z τ hZ hB hL hW O G hconv hY

#print axioms clay_continuum_pair_of_fixedWindowDecay

/-- **The capstone with requirement M as one Prop.** At `2 ≤ N`, a reflection-invariant `Z`, the
separated uniform bound `hB` (E), a window `L > 0`, `WeakCouplingWindow.FixedWindowDecay τ 0 hN L`
(M), `ContinuumNontrivial.KernelConvergesSep` towards a radial `G` (N) and
`ShortDistanceY.AFShortDistance G` (Y): `ClayContinuum hN Z τ hZ hB L`
(`clay_continuum_pair_of_fixedWindowDecay` at `ContinuumSep.pairBoundSep_of_uniformBoundSep`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
lower end of `L`, and the reflection plane offset `p = 0` that `continuum_gap_nontrivial` reads
`FixedWindowDecay` at; `4` in `Fin 4` is the spacetime dimension. -/
theorem clay_continuum_of_fixedWindowDecay (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_pair_of_fixedWindowDecay hN2 hN Z τ hZ
    (ContinuumSep.pairBoundSep_of_uniformBoundSep hN (Renorm.connected hN Z) τ
      (Renorm.connected_reflCompat hN Z τ hZ) hB) hL hW O G hconv hY

#print axioms clay_continuum_of_fixedWindowDecay

end Capstone

/-! ## 2. The finite-size route -/

section FiniteSize

open MassGap

end FiniteSize

section FiniteSizeCapstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

end FiniteSizeCapstone

/-! ## 3. The `χ²` route -/

section Chi

open MeasureTheory Filter
open scoped Topology

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type*}

/-- **The step-`n` connected pairing** of `a`, `b` under the law `m n`:
`E_n[a b] − E_n a · E_n b`.

DERIVED: no numeral. -/
def stepConn (m : ℕ → MeasureTheory.Measure Ω) (n : ℕ) (a b : Ω → ℝ) : ℝ :=
  ∫ x, a x * b x ∂(m n) - (∫ x, a x ∂(m n)) * ∫ x, b x ∂(m n)

/-- **The carrier bridge.** A step assignment `step : ℝ → ℕ` tending to `∞` with the coupling such
that, for all large `β`, some lag `lag ≠ 0` inside the window (`lag · aRun N β ≤ L`) has: every
`x ∈ gaugeInvHalfSpaceAlg τ p` is read by some `i ∈ S`, in the sense that for every `ε > 0`, along
`PeriodicState.periodicUltra hN β`, the torus pairing of `x` at `lag` is at most the forest's window
pairing at step `step β` plus `ε`, and the forest's lag-zero pairing at step `step β` is at most the
torus pairing of `x` at lag `0` plus `ε`.

It matches the two carriers: the forest's dyadic steps of infinite-volume observer laws and the
periodic tori along `periodicUltra` at every large real `β`; and the forest's class `S` of coarse
observables and the lattice class `gaugeInvHalfSpaceAlg`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the excluded lag, the sign of `ε`
and the lag-zero pairing. -/
def ChiCarrierBridge (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) (m : ℕ → MeasureTheory.Measure Ω)
    (S : Set ι) (aw bw a0 b0 : ι → Ω → ℝ) : Prop :=
  ∃ step : ℝ → ℕ, Tendsto step atTop atTop ∧ ∀ᶠ β in atTop, ∃ lag : ℕ, lag ≠ 0 ∧
    (lag : ℝ) * MassGap.AsymptoticScaling.aRun N β ≤ L ∧
    ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∃ i ∈ S, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in ((MassGap.PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x lag
              ≤ stepConn m (step β) (aw i) (bw i) + ε ∧
            stepConn m (step β) (a0 i) (b0 i)
              ≤ MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε

end Chi

section ChiCapstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

end ChiCapstone

end MassGap.ClayRoutes
