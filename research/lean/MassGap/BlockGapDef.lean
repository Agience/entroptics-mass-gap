import Mathlib
import MassGap.BlockDynamicStep
import MassGap.BoxGap

noncomputable section

/-!
# MassGap.BlockGapDef — the block-dynamics gap of the Wilson measure, defined

`BlockDynamicStep` takes the block gap `γ` as an arbitrary function. With `γ` constant, `BlockStep` holds at
`C = 0` and `ChebyshevConversion` is the uniform transfer gap itself (`chebyshevConversion_const_iff`), so its
capstone restates its conclusion. This module defines `γ` from the Wilson measure, so `BlockStep` and the base
`γ β₀ > 0` become statements about one dynamics, and states the conversion as the theorem it has to be.

## The definition

`WilsonBlockBath hN β n j`: on the periodic gauge-invariant observables at extent index `j`, with the torus
Wilson form `KnabeCriterion.torusForm hN β j`, one operator `condExp k` per site `k`, a form-self-adjoint
idempotent whose values read no link of the box `BoxGap.boxLinks n k` of side `n` at `k`, and which keeps
every observable reading none of them: the conditional expectation given every link outside the box, up to
form-null vectors (as `KnabeCriterion.WilsonHeatBath` for single links).
`blockH S = Σ_k (id − condExp k)`, the generator of the block heat bath that resamples one box from its
conditional law. `BlockGlobalGap S c`: `c ⟨Hx, x⟩ ≤ ⟨Hx, Hx⟩` at every `x` (the form of
`KnabeCriterion.PatchSystem.GlobalGap`).
`blockGap hN β n = sSup {c ≥ 0 | some family S j has BlockGlobalGap (S j) c at all large j}`: the gap of the
block dynamics uniform in the volume.
`blockSide s β = ⌈1 / s β⌉₊`, the box side in lattice units at physical side `ℓ` when `s = a/ℓ`, and
`gammaWilson hN s β = blockGap hN β (blockSide s β)`: the gap of the block dynamics at fixed physical block
size, a function of the Wilson measure and the scale alone.

## What it gives

1. `chebyshevConversion_const_iff`: for a constant `γ₀` the conversion is the uniform gap at the rate
   `c₀ √γ₀` (the restatement the arbitrary-`γ` form carried).
2. `WilsonBlockStep hN s βUV C := BlockStep (gammaWilson hN s) s βUV C`; `WilsonConversion τ hN s c₀ βUV`:
   the conversion for `gammaWilson`. `clay_continuum_of_wilsonBlockDynamics`: the capstone with `γ` the
   defined Wilson block gap.
3. `blockGap_nonneg`, `blockGap_le_of_bdd`: the defined gap is non-negative, and bounded by every `c` above
   the set.

## What is open, and why the capstone is not a restatement now

`WilsonBlockStep` and `0 < gammaWilson hN s β₀` are statements about the Wilson measure's block dynamics;
neither mentions the transfer. `WilsonConversion` still mentions the transfer: together with a lower bound on
`gammaWilson` it implies the uniform gap, and it is the theorem to prove (a Chebyshev filter of a gapped,
finite-depth symmetrised colour sweep of the block projections, with the locality of the box projections).
Until it is proved, `clay_continuum_of_wilsonBlockDynamics` is conditional on it; its other hypotheses are not
statements of the conclusion. The existence of a block conditional expectation with the four fields is not
constructed here; if no family exists, `blockGap` is `0` and the base hypothesis fails, so the capstone does
not hold vacuously.

DERIVED (module-wide): `4` the spacetime dimension; `2 * j + 1` the index of the even-extent family and
`+ 1` its successor; `0` the signs and the excluded rank; `1` the numerator of the box side.
-/

namespace MassGap.BlockGapDef

open MassGap MassGap.KnabeCriterion MassGap.PeriodicState Filter
open scoped Topology

/-! ## 1. The restatement in the arbitrary-`γ` form -/

section Restate

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **With a constant `γ` the conversion is the uniform gap.**

DERIVED: no numeral. -/
theorem chebyshevConversion_const_iff (D : ℝ → Transfer.TransferData A) (s : ℝ → ℝ)
    (c₀ βUV γ₀ : ℝ) :
    BlockDynamicStep.ChebyshevConversion D (fun _ => γ₀) s c₀ βUV ↔
      ∀ β, βUV ≤ β → TransferGap.GapAt (D β) (Real.exp (-(c₀ * Real.sqrt γ₀ * s β))) :=
  Iff.rfl

#print axioms chebyshevConversion_const_iff

/-- A constant `γ` satisfies `BlockStep` at `C = 0`.

DERIVED: `0` the loss. -/
theorem blockStep_const (s : ℝ → ℝ) (βUV γ₀ : ℝ) :
    BlockDynamicStep.BlockStep (fun _ => γ₀) s βUV 0 := by
  intro β β' _ _ _ _
  simp

#print axioms blockStep_const

end Restate

/-! ## 2. The block heat bath of the Wilson measure -/

section Wilson

variable {N : ℕ}

/-- **The block heat-bath system** at coupling `β`, box side `n`, extent index `j`. See the module
docstring.

DERIVED: `4` the spacetime dimension; `2 * j + 1` the index and `+ 1` its successor. -/
structure WilsonBlockBath (hN : N ≠ 0) (β : ℝ) (n j : ℕ) where
  condExp : WilsonHypercubic.Site 4 (2 * j + 1 + 1) →
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
  selfAdj : ∀ k x y, torusForm hN β j (condExp k x) y = torusForm hN β j x (condExp k y)
  idem : ∀ k x, condExp k (condExp k x) = condExp k x
  reads_not : ∀ k x, ∀ l ∈ BoxGap.boxLinks n k,
    ReadsNot j l ((condExp k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
      : C(GibbsSpec.IConf (SUN.SU N), ℝ))
  keeps : ∀ k (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))),
    (∀ l ∈ BoxGap.boxLinks n k, ReadsNot j l (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))) →
      torusObs (2 * j + 1) ((condExp k x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SUN.SU N), ℝ))
        = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))

/-- **The block heat-bath generator** `Σ_k (id − condExp k)`.

DERIVED: no numeral. -/
def blockH {hN : N ≠ 0} {β : ℝ} {n j : ℕ} (S : WilsonBlockBath hN β n j) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  ∑ k, (LinearMap.id - S.condExp k)

/-- **The gap of the block dynamics at one volume**: `c ⟨Hx, x⟩ ≤ ⟨Hx, Hx⟩` at every `x`.

DERIVED: no numeral. -/
def BlockGlobalGap {hN : N ≠ 0} {β : ℝ} {n j : ℕ} (S : WilsonBlockBath hN β n j) (c : ℝ) : Prop :=
  ∀ x, c * torusForm hN β j (blockH S x) x ≤ torusForm hN β j (blockH S x) (blockH S x)

/-- The gaps attained uniformly in the volume.

DERIVED: `0` the sign. -/
def blockGapSet (hN : N ≠ 0) (β : ℝ) (n : ℕ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∃ S : ∀ j : ℕ, WilsonBlockBath hN β n j, ∀ᶠ j in atTop, BlockGlobalGap (S j) c}

/-- **The block-dynamics gap of the Wilson measure** at coupling `β` and box side `n`.

DERIVED: no numeral. -/
def blockGap (hN : N ≠ 0) (β : ℝ) (n : ℕ) : ℝ := sSup (blockGapSet hN β n)

/-- DERIVED: `0` the sign. -/
theorem blockGap_nonneg (hN : N ≠ 0) (β : ℝ) (n : ℕ) : 0 ≤ blockGap hN β n :=
  Real.sSup_nonneg (fun _ hc => hc.1)

#print axioms blockGap_nonneg

/-- Every upper bound of the gaps bounds `blockGap`, when some gap is attained.

DERIVED: no numeral. -/
theorem blockGap_le_of_bdd (hN : N ≠ 0) (β : ℝ) (n : ℕ) {u : ℝ}
    (hne : (blockGapSet hN β n).Nonempty) (hu : ∀ c ∈ blockGapSet hN β n, c ≤ u) :
    blockGap hN β n ≤ u :=
  csSup_le hne hu

#print axioms blockGap_le_of_bdd

/-- **The box side at physical side `ℓ`** when `s = a/ℓ`: `⌈1/s β⌉₊`.

DERIVED: `1` the numerator. -/
def blockSide (s : ℝ → ℝ) (β : ℝ) : ℕ := ⌈1 / s β⌉₊

/-- **The block gap at fixed physical block size**, a function of the Wilson measure and the scale.

DERIVED: no numeral. -/
def gammaWilson (hN : N ≠ 0) (s : ℝ → ℝ) (β : ℝ) : ℝ := blockGap hN β (blockSide s β)

/-- **The block step for the Wilson block gap.**

DERIVED: no numeral. -/
def WilsonBlockStep (hN : N ≠ 0) (s : ℝ → ℝ) (βUV C : ℝ) : Prop :=
  BlockDynamicStep.BlockStep (gammaWilson hN s) s βUV C

/-- **The conversion for the Wilson block gap**, the theorem to prove: the periodic transfer has the gap
`e^{−c₀ √(gammaWilson β) s β}` from `βUV` on.

DERIVED: `4` the spacetime dimension; `0` the reflection plane. -/
def WilsonConversion (τ : Fin 4) (hN : N ≠ 0) (s : ℝ → ℝ) (c₀ βUV : ℝ) : Prop :=
  BlockDynamicStep.ChebyshevConversion (fun β => periodicGaugeInvData τ 0 hN β)
    (gammaWilson hN s) s c₀ βUV

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the Wilson block dynamics.** The defined block gap at one coupling,
its step along a scale function, the conversion for it, `ScaleDominatesRun`, and E, N, Y.

DERIVED: `2` the least rank; `0` the signs; `4` the spacetime dimension; `4/3` the budget. -/
theorem clay_continuum_of_wilsonBlockDynamics (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {s : ℝ → ℝ} {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < gammaWilson hN s β₀) (hC : 0 ≤ C)
    (hCs : ∀ β, βUV ≤ β → C * s β ^ 2 ≤ 1) (hb : 4 / 3 * C * s β₀ ^ 2 < 1) (hc₀ : 0 < c₀)
    (hstep : WilsonBlockStep hN s βUV C) (hconv : WilsonConversion τ hN s c₀ βUV)
    (hdomR : ScaleAlong.ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  BlockDynamicStep.clay_continuum_of_blockDynamics hN2 hN Z τ hZ hB hL hs hβ₀ hUVβ₀ hg₀ hC hCs hb hc₀
    hstep hconv hdomR O G hconvK hY

#print axioms clay_continuum_of_wilsonBlockDynamics

end Wilson

end MassGap.BlockGapDef
