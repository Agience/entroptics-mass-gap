import Mathlib
import MassGap.ZoomStep

/-!
# MassGap.BondMove — what a Migdal–Kadanoff sandwich gives the zoom step, and which half is missing

`ZoomStep.WilsonZoomStep N` asks for one map `φ` with `D(β, w + 1) ≤ D(φ β, w)`, where
`D(β, w) = 16 log Z_β(2^w) − log Z_β(2^{w+1})` is the window coupling (`CouplingTower.windowCoupling`,
`ZoomSelfScale.defectW`) and `Z_β(n)` the Wilson partition function `RectWilson.ZR` on the side-`n` 4-torus.
Migdal–Kadanoff bond moving followed by decimation compares the side-`2m` torus at `β` with a side-`m` torus at
an effective weight, up to a bulk factor `e^{m⁴ b}`. This module reads that comparison against the defect.
Declarations are in the namespace `MassGap.BondMove`.

## 1. The bulk factor cancels in the defect (proved, abstract)

For a log-partition family `L : ℝ → ℕ → ℝ` (coupling, side), `defectOf L β w = 16 L β (2^w) − L β (2 · 2^w)`.

* `UpperAt L φ bU β w`: `L β (2 · 2^w) ≤ (2^w)⁴ bU + L (φ β) (2^w)` (bond moving: Jensen / AM–GM, the
  direction `HolderBondMoving.zT_le_mkField` proves for the power half).
* `LowerAt L φ bL β w`: `(2^w)⁴ bL + L (φ β) (2^w) ≤ L β (2 · 2^w)` (the lower decimation).
* `defect_le_of_sandwich`: the upper bound at window `w` and the lower bound at window `w + 1`, with the same
  effective coupling `φ β`, give `defectOf L β (w + 1) ≤ defectOf L (φ β) w + 16 (2^w)⁴ (bU − bL)`.
  The bulk terms cancel because `(2^{w+1})⁴ = 16 (2^w)⁴`: the side-`2m` torus holds `16` copies of the
  side-`m` one, the same `16` that defines the defect. What survives is the gap between the two bulk
  factors, extensive in the window.
* `defect_le_of_matched`: with `bU = bL` the step holds exactly: `defectOf L β (w + 1) ≤ defectOf L (φ β) w`.

## 2. One side alone gives nothing (proved, abstract counterexamples)

In the defect the fine side `2^{w+1}` enters with `+16` and the side `2^{w+2}` with `−1`. An upper bound on
`L` controls only the first term, a lower bound only the second.

* `upperToy β n = −β n⁵` (CHOSEN) with `halfMap β = β / 2` (CHOSEN): `upperToy_upper` (the upper bound at
  every `β ≥ 0`, every window, bulk `0`), `halfMap_noFixedAbove`, and `upperToy_not_step` (the step fails at
  `β = 1`, `w = 1`: `16384 > 256`). So the bond-moving direction with an effective map that has no fixed point
  above `0` does not give `ZoomStepMap`.
* `lowerToy β n = β n³` (CHOSEN): `lowerToy_lower` and `lowerToy_not_step` (`512 > 32`). The lower bound alone
  does not give it either.

## 3. The Wilson form (proved from one named input)

* `logZ N β n = log ZR(n) `; `windowCoupling_eq_defectOf`: `windowCoupling N = defectOf (logZ N)` (by
  definition).
* `MatchedBlocking N φ`: `φ ≥ 0` on `β ≥ 0`, and some bulk `b` with `UpperAt` and `LowerAt` at every `β ≥ 0`
  and every window `w ≥ 1`, both at the same effective Wilson coupling `φ β` and the same bulk `b β`.
* `zoomStepMap_of_matchedBlocking`: `MatchedBlocking N φ → ZoomStepMap (windowCoupling N) φ`.
* `strongEnd_of_matchedBlocking`: with `NoFixedAbove φ`, `CouplingTower.StrongEnd N` (through
  `ZoomStep.strongEnd_of_wilsonZoomStep`).

## 4. The decimation half on one coefficient (proved; group-blind)

Decimation acts on a normalized character coefficient `ĉ = c_j/(d_j c_0)` of a plaquette weight by
`ĉ ↦ ĉ^{b²}` (`b² = 4`; exact by character orthogonality, cited, not built here). `decim_lt`: `0 < ĉ < 1`
gives `ĉ⁴ < ĉ`; `decim_tendsto`: the decimation orbit tends to `0`. Nothing in either statement names the
group: the contraction holds for `U(1)` as for `SU(N)`. The MK recursion with bond moving included flows to
`0` for `U(N)`, `U(1)` included, in `D ≤ 4` (Ito, Phys. Rev. Lett. 55 (1985) 558, as stated in Ito–Seiler
arXiv:0711.4930, Theorem 2.1; cited in `MKBound`, `OneWayCost`). So no `U(1)` fixed point of the MK flow at
`d = 4` exists to serve as a control: the MK flow does not separate the abelian from the non-abelian group.

## Strength

`MatchedBlocking N φ ∧ NoFixedAbove φ` implies `WilsonZoomStep N`. `MatchedBlocking` asks one effective Wilson
coupling and one bulk factor to bound `Z` from both sides at every window. Taken at one bulk `b β`, Upper and
Lower at the same window together say `logZ(2·2^w) = (2^w)⁴ b β + logZ(φβ, 2^w)` exactly, for every `w ≥ 1`.
It is the analogue for the defect of `MKBound.SandwichMatch`, at two sides (`2^{w+1}` above, `2^{w+2}` below)
instead of two boundary conditions. It is not proved here, and it may be unsatisfiable for the Wilson reading
beyond `β = 0`. Section 2 shows, for the chosen `halfMap`, that neither half alone gives the step.

## What does not follow

* `MatchedBlocking N φ` for any `φ`. Migdal–Kadanoff gives an upper bound by bond moving at the bulk
  `(∫ f^ζ)^{b²} ≥ 1` (`MKBound.mkUpperF0_ge_one`) with coefficients `c^U`, and a lower bound at bulk `1` with
  different coefficients `c^L`: the two bulks differ, so the surviving term `16 (2^w)⁴ (bU − bL)` is
  extensive. Interpolation (`MKBound.exists_interp`) matches each side with its own parameter, so `φ` would
  depend on the window; the input needs one `φ` at every window.
* The effective weight of bond moving is `N[(w^4)^{*4}]`, not a Wilson weight. Comparing it with the Wilson
  weight at some `φ β` needs monotonicity of `Z` in the weight (reflection positivity order, not built) and a
  Wilson weight below and above it at the same coupling; neither is here.
* The proved bond-moving bound in the tree (`HolderBondMoving.zT_le_mkField`) is the power half at the same
  side; the convolution half (integrating the interior links, side `2m` to side `m`) is not built in a rooted
  module. `GapSideExactDecimation` integrates exactly without moving, keeping the effective density non-local.
* A `U(1)` control: the MK flow contracts for `U(1)` too (Section 4), so any proof of `MatchedBlocking` must
  use a property the MK recursion does not see.

DERIVED (module-wide): `16 = 2⁴` the copies of the side-`m` torus in the side-`2m` one; `4` the dimension in
`(2^w)⁴`; `2` the doubling; `1` the least window index; `0` the signs and the limit; `4 = b²` the decimation
power at `b = 2`. CHOSEN (tests only): `upperToy` (`−β n⁵`), `lowerToy` (`β n³`), `halfMap` (`β/2`), and the
test point `β = 1`, `w = 1`. Inherited: none.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.BondMove

open Filter Topology
open MassGap.ZoomStep (ZoomStepMap NoFixedAbove WilsonZoomStep)

/-! ## 1. The bulk factor cancels in the defect -/

/-- **The doubling defect of a log-partition family** at window `w`. DERIVED: `16 = 2⁴`; `2` the doubling. -/
def defectOf (L : ℝ → ℕ → ℝ) (β : ℝ) (w : ℕ) : ℝ := 16 * L β (2 ^ w) - L β (2 * 2 ^ w)

/-- **Upper (bond-moving) bound at window `w`**: the side-`2·2^w` torus at `β` is at most the bulk
`(2^w)⁴ bU` plus the side-`2^w` torus at `φ β`. DERIVED: `4` the dimension; `2` the doubling. -/
def UpperAt (L : ℝ → ℕ → ℝ) (φ : ℝ → ℝ) (bU : ℝ) (β : ℝ) (w : ℕ) : Prop :=
  L β (2 * 2 ^ w) ≤ ((2 : ℝ) ^ w) ^ 4 * bU + L (φ β) (2 ^ w)

/-- **Lower (decimation) bound at window `w`.** DERIVED: `4` the dimension; `2` the doubling. -/
def LowerAt (L : ℝ → ℕ → ℝ) (φ : ℝ → ℝ) (bL : ℝ) (β : ℝ) (w : ℕ) : Prop :=
  ((2 : ℝ) ^ w) ^ 4 * bL + L (φ β) (2 ^ w) ≤ L β (2 * 2 ^ w)

/-- **The sandwich bounds the step up to the bulk gap.** DERIVED: `16 = 2⁴` (the bulk cancels through
`(2^{w+1})⁴ = 16 (2^w)⁴`); `1` the step. -/
theorem defect_le_of_sandwich {L : ℝ → ℕ → ℝ} {φ : ℝ → ℝ} {bU bL β : ℝ} {w : ℕ}
    (hU : UpperAt L φ bU β w) (hL : LowerAt L φ bL β (w + 1)) :
    defectOf L β (w + 1) ≤ defectOf L (φ β) w + 16 * ((2 : ℝ) ^ w) ^ 4 * (bU - bL) := by
  unfold UpperAt at hU
  unfold LowerAt at hL
  unfold defectOf
  have e1 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by ring
  have e2 : ((2 : ℝ) ^ (w + 1)) ^ 4 = 16 * ((2 : ℝ) ^ w) ^ 4 := by ring
  rw [e1] at hL ⊢
  rw [e2] at hL
  nlinarith

/-- **Matched bulk: the step holds exactly.** DERIVED: `1` the step. -/
theorem defect_le_of_matched {L : ℝ → ℕ → ℝ} {φ : ℝ → ℝ} {b β : ℝ} {w : ℕ}
    (hU : UpperAt L φ b β w) (hL : LowerAt L φ b β (w + 1)) :
    defectOf L β (w + 1) ≤ defectOf L (φ β) w := by
  have := defect_le_of_sandwich hU hL
  simpa using this

/-! ## 2. One side alone gives nothing -/

/-- CHOSEN: the halving map. -/
def halfMap (β : ℝ) : ℝ := β / 2

/-- DERIVED: `0` the trivial coupling. -/
theorem halfMap_noFixedAbove : NoFixedAbove halfMap :=
  ⟨by unfold halfMap; fun_prop, fun x hx => by unfold halfMap; linarith⟩

/-- CHOSEN: an upper-bound test reading `−β n⁵`. -/
def upperToy (β : ℝ) (n : ℕ) : ℝ := -(β * (n : ℝ) ^ 5)

/-- **The upper bound holds for the test reading**, bulk `0`, at every `β ≥ 0` and every window.
DERIVED: `0` the bulk and the sign. -/
theorem upperToy_upper {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) : UpperAt upperToy halfMap 0 β w := by
  unfold UpperAt upperToy halfMap
  push_cast
  have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ w) ^ 5 := by positivity
  nlinarith [mul_nonneg hβ hp]

/-- **The step fails for the test reading** at `β = 1`, `w = 1`: `16384 > 256`. -/
theorem upperToy_not_step : ¬ ZoomStepMap (fun β w => defectOf upperToy β w) halfMap := by
  rintro ⟨-, h⟩
  have := h 1 zero_le_one 1 le_rfl
  unfold defectOf upperToy halfMap at this
  norm_num at this

/-- CHOSEN: a lower-bound test reading `β n³`. -/
def lowerToy (β : ℝ) (n : ℕ) : ℝ := β * (n : ℝ) ^ 3

/-- **The lower bound holds for the test reading**, bulk `0`. DERIVED: `0` the bulk and the sign. -/
theorem lowerToy_lower {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) : LowerAt lowerToy halfMap 0 β w := by
  unfold LowerAt lowerToy halfMap
  push_cast
  have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ w) ^ 3 := by positivity
  nlinarith [mul_nonneg hβ hp]

/-- **The step fails for the lower test reading** at `β = 1`, `w = 1`: `512 > 32`. -/
theorem lowerToy_not_step : ¬ ZoomStepMap (fun β w => defectOf lowerToy β w) halfMap := by
  rintro ⟨-, h⟩
  have := h 1 zero_le_one 1 le_rfl
  unfold defectOf lowerToy halfMap at this
  norm_num at this

/-! ## 3. The Wilson form -/

/-- The log of the Wilson partition function on the side-`n` 4-torus. -/
def logZ (N : ℕ) (β : ℝ) (n : ℕ) : ℝ := Real.log (MassGap.RectWilson.ZR (fun _ => n) N β)

theorem windowCoupling_eq_defectOf (N : ℕ) :
    MassGap.CouplingTower.windowCoupling N = defectOf (logZ N) := rfl

/-- **Matched blocking**: one effective Wilson coupling `φ β ≥ 0` and one bulk `b β` bound the
side-`2·2^w` torus at `β` from above and from below by the side-`2^w` torus at `φ β`, at every window
`w ≥ 1`. DERIVED: `0` the signs; `1` the least window index. -/
def MatchedBlocking (N : ℕ) (φ : ℝ → ℝ) : Prop :=
  (∀ β : ℝ, 0 ≤ β → 0 ≤ φ β) ∧ ∃ b : ℝ → ℝ, ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w →
    UpperAt (logZ N) φ (b β) β w ∧ LowerAt (logZ N) φ (b β) β w

/-- **Matched blocking gives the zoom step map.** DERIVED: `1` the least window index and the step. -/
theorem zoomStepMap_of_matchedBlocking {N : ℕ} {φ : ℝ → ℝ} (h : MatchedBlocking N φ) :
    ZoomStepMap (MassGap.CouplingTower.windowCoupling N) φ := by
  obtain ⟨hφ, b, hb⟩ := h
  refine ⟨hφ, fun β hβ w hw => ?_⟩
  rw [windowCoupling_eq_defectOf]
  exact defect_le_of_matched (hb β hβ w hw).1 (hb β hβ (w + 1) (by omega)).2

theorem wilsonZoomStep_of_matchedBlocking {N : ℕ} {φ : ℝ → ℝ} (h : MatchedBlocking N φ)
    (hfix : NoFixedAbove φ) : WilsonZoomStep N :=
  ⟨φ, zoomStepMap_of_matchedBlocking h, hfix⟩

/-- **Matched blocking with no fixed point above `0` gives the strong end.** -/
theorem strongEnd_of_matchedBlocking {N : ℕ} (hN : N ≠ 0) {φ : ℝ → ℝ} (h : MatchedBlocking N φ)
    (hfix : NoFixedAbove φ) : MassGap.CouplingTower.StrongEnd N :=
  MassGap.ZoomStep.strongEnd_of_wilsonZoomStep hN (wilsonZoomStep_of_matchedBlocking h hfix)

/-! ## 4. The decimation half on one coefficient -/

/-- **Decimation contracts a normalized coefficient**: `0 < c < 1` gives `c⁴ < c`. DERIVED: `4 = b²` at
`b = 2`; `0`, `1` the trivial and the free coefficient. -/
theorem decim_lt {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : c ^ 4 < c :=
  pow_lt_self_of_lt_one₀ h0 h1 (by norm_num)

/-- **The decimation orbit tends to `0`**: `c^{4^k} → 0` for `0 ≤ c < 1`. DERIVED: `4 = b²`. -/
theorem decim_tendsto {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) :
    Tendsto (fun k : ℕ => c ^ (4 ^ k)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  exact hp.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 4))

end MassGap.BondMove

#print axioms MassGap.BondMove.defect_le_of_sandwich
#print axioms MassGap.BondMove.defect_le_of_matched
#print axioms MassGap.BondMove.halfMap_noFixedAbove
#print axioms MassGap.BondMove.upperToy_upper
#print axioms MassGap.BondMove.upperToy_not_step
#print axioms MassGap.BondMove.lowerToy_lower
#print axioms MassGap.BondMove.lowerToy_not_step
#print axioms MassGap.BondMove.windowCoupling_eq_defectOf
#print axioms MassGap.BondMove.zoomStepMap_of_matchedBlocking
#print axioms MassGap.BondMove.wilsonZoomStep_of_matchedBlocking
#print axioms MassGap.BondMove.strongEnd_of_matchedBlocking
#print axioms MassGap.BondMove.decim_lt
#print axioms MassGap.BondMove.decim_tendsto
