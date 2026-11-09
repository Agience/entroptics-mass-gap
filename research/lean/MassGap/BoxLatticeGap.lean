import Mathlib
import MassGap.BoxGapHS

noncomputable section

/-!
# MassGap.BoxLatticeGap — the lattice gaps that the side-15 box route proves at its couplings

The proofs of `BoxGapBE.clay_of_uvStep_su2`, `_su3` and `BoxGapHS.clay_of_uvStep_su2_hs`, `_su3_hs`
pass through three lattice statements at the box coupling `β` and the box gap `γ`. This module
states each of them on its own.

## The three gaps

1. Box-local (`BoxPatch.BoxLocalGap hN β 15 γ`, proved in `BoxGapBE`, `BoxGapHS`): on every periodic
   torus of extent `2(j + 1) ≥ 30`, at every corner `k`, the box operator
   `A_k = Σ_{l in the side-15 box at k} (1 − E_l)` has `γ ⟨A_k x, x⟩ ≤ ⟨A_k x, A_k x⟩`, where `E_l` is
   the heat-bath conditional expectation of link `l` (`RestoreShims.torusCondExp`), `⟨·,·⟩` is the
   torus Wilson `L²` form (`KnabeCriterion.torusForm`) and `x` ranges over the continuous periodic
   gauge-invariant observables. It is a gap of the heat-bath generator restricted to one box, in the
   full-torus measure.
2. Torus-wide (`torusGap_of_boxLocalGap` and its four instances): on the same tori, the full
   heat-bath generator `H = Σ_l (1 − E_l)` over every torus link has
   `c₀ ⟨H x, x⟩ ≤ ⟨H x, H x⟩` with `c₀ = boxConst γ > 0`, uniformly in `j ≥ 14`. This is the
   step `WeightedBox.globalGap_weighted` with the profile weights `WeightedProfile15.P15`.
3. Infinite volume (`transferGap_of_boxLocalGap` and its four instances): at the rate
   `r = e^{−min(c₀, 1)/508}` (`clusterRate_eq`), `0 < r < 1`,
   * `HeatBathGapDecay.TorusClusterAt τ p hN β r`: each gauge-invariant half-space observable has a
     constant `K` with the connected reflected pairing at lag `2n` at most `K r^{2n}` on every torus
     past a size that depends on `n`;
   * `TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β) r`: the one-step transfer
     operator in direction `τ` contracts by `r` on the vacuum's orthogonal complement, in the
     reflection-positivity form of the state `PeriodicState.periodicState hN β`, on the
     gauge-invariant half-space algebra.

At each coupling:

| group | `β` (Lean) | `γ` (box-local) | source of the box gap |
|---|---|---|---|
| `SU(2)` | `3/40` | `58/625` | `BoxGapBE.boxLocalGap15_su2` |
| `SU(2)` | every `β ∈ [0, 83/1000]` | `953/12500` | `BoxGapHS.boxLocalGap15_su2_hs` |
| `SU(3)` | `floorBeta 3 = 153/(88π²) ≈ 0.1762` | `367/2500` | `BoxGapBE.boxLocalGap15_su3` |
| `SU(3)` | every `β ∈ [0, 19/100]` | `41/500` | `BoxGapHS.boxLocalGap15_su3_hs` |

## The convention

`β` is the Lean coupling: the action sums `1 − Re tr U_p / N` over ordered plaquettes, each plane
twice, so the standard Wilson coupling is `β_W = 2β` (`BoxGapHS`, "The convention"). The couplings
above are `β_W = 3/20`, `83/500`, `≈ 0.3524`, `19/50`.

## What kind of gap

Item 3 is a gap of the full-lattice transfer operator, at one infinite-volume state. Item 2 is a
gap of the full finite-torus heat-bath generator (a dynamics, not the transfer matrix). Item 1 is
box-local. Items 1 and 2 are form-level gaps, `c B(Hx, x) ≤ B(Hx, Hx)` for all `x` (`KnabeEngine.GlobalGap`); read as a
spectral gap of `H` on the complement of its kernel they need `H` self-adjoint and positive in `torusForm`, which this module
does not state. The torus-wide constant is small: the profile threshold of `WeightedProfile15` is
`≈ 0.07589`, and `c₀ = (a₁²/(15⁴K))(γ − 0.07589)` (`WeightedBox.weightedConst`), so the lattice mass
`min(c₀, 1)/508` is at most `1/508` at every `γ`, and between about `1.3·10⁻⁹` (`SU(2)` on the range)
and `2.6·10⁻⁷` (`SU(3)` at `floorBeta 3`) at these four (COMPUTED with Python, not in Lean). The smallest margin is the `SU(2)` case at `953/12500`, where
`γ − 0.07589 ≈ 3.5·10⁻⁴`.

## What does not follow

* This is not the Clay statement: no continuum limit, no reconstruction, and the mass is a lattice rate.
* Uniqueness: `periodicState hN β` is one limit of torus states along an ultrafilter
  (`PeriodicState.periodicUltra`), shown to satisfy the DLR equations but not shown to be the only
  infinite-volume Gibbs state. `GapAt` is stated at that state and at no other.
* A transfer gap on a finite torus is not stated. `TorusClusterAt` bounds the torus pairings only past
  a size depending on the lag, with a constant depending on the observable; only the limit pairing is
  a statement about the transfer operator.
* Non-gauge-invariant observables are not covered: the observables are periodic gauge-invariant
  (items 1, 2) or in the gauge-invariant half-space algebra (item 3).
* Other groups: `N = 2`, `N = 3` only, through `HaarMomentsSU2`, `HaarMomentsSU3`.
* Weak coupling: the couplings stop at Lean `β = 83/1000` (`SU(2)`) and `19/100` (`SU(3)`), on the
  strong-coupling side of the crossover; the lowest octave of the dyadic tower is not reached
  (`BoxGapHS`, "What does not follow"). No continuum statement follows from this module alone; the UV
  step, E, N and Y stay hypotheses of the `clay_of_uvStep_*` theorems.
* The reduction of Bhattacharjee, Bhattacharya, Lockwood and Romanov (<https://github.com/creelie/4Y-M>,
  unrefereed; `OneCubeBridge`) is not used here: the chain is the pair route with Holley–Stroock on
  the fibre, the weighted Knabe bridge and the heat-bath clustering of `HeatBathGapDecay`. Their
  coupling ranges are quoted for comparison in `BoxGapHS`.

DERIVED (module-wide): `15` the box side of `WeightedProfile15`; `759/10000` its rounded threshold
`thr15`; `21` the neighbour bound of `HeatBathLocal.localityAt_holds`; `508 = 2 · 254`,
`254 = 2 · 127`, `127 = 6 · 21 + 1` the sweep of `clusterRate 21`, with `6` and `3` its sweep parameters; `2`, `3` the ranks; `4` the
spacetime dimension; `0` the lower ends and the excluded rank; `2 * j + 1` the index of the
even-extent family and `+ 1` its successor writing the extent. Inherited: `3/40`, `58/625`
(`BoxGapBE`, CHOSEN there), `floorBeta 3`, `367/2500` (`BoxGapBE`), `83/1000`, `953/12500`,
`19/100`, `41/500` (`BoxGapHS`).
-/

namespace MassGap.BoxLatticeGap

open MassGap MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathGapDecay MassGap.HeatBathLocal
open MassGap.WeightedProfile15 MassGap.WeightedBox
open MassGap.SUN (SU)
open Filter

variable {N : ℕ}

/-! ## 1. The generator, the constant and the rate -/

section Defs

/-- **The torus heat-bath generator** `H = Σ_l (1 − E_l)` over every link of the periodic torus of
extent `2(j + 1)`, on the periodic gauge-invariant observables, `E_l = torusCondExp β (2j + 1) l`.

DERIVED: `2 * j + 1` is the index of the even-extent family; `1` its successor writing the extent;
`4` the spacetime dimension. -/
def heatGen (β : ℝ) (j : ℕ) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  ∑ l : WilsonHypercubic.Link 4 (2 * j + 1 + 1),
    ((LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - torusCondExp β (2 * j + 1) l)

/-- **The torus-wide constant of the side-15 box at box gap `γ`**: `WeightedBox.weightedConst` at the
profile `P15`, `(γ a₁²/15⁴ − a₂ + K − e)/K`.

DERIVED: `15` the box side. -/
def boxConst (γ : ℝ) : ℝ := weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e γ

/-- `boxConst γ > 0` at `γ ≥ 759/10000` (`WeightedBox.weightedConst_pos`, `thr15`).

DERIVED: `15`, `759/10000` as in the module; `1` the least box side; `0` the sign. -/
theorem boxConst_pos {γ : ℝ} (hγ : 759 / 10000 ≤ γ) : 0 < boxConst γ :=
  weightedConst_pos (by norm_num) a15_ne K15_pos (lt_of_lt_of_le thr15 hγ)

#print axioms boxConst_pos

/-- **The clustering rate at neighbour bound `21` is `e^{−min(c, 1)/508}`** at every `c`: the branch
`e/3` of the maximum never wins, since `e/3 < 0.9061 < 1 − 1/254 ≤ e^{−min(c,1)/254}`
(`Real.exp_one_lt_d9`, `Real.add_one_le_exp`), and the square root halves the exponent.

DERIVED: `21` the neighbour bound; `127 = 6 · 21 + 1`; `254 = 2 · 127`; `508 = 2 · 254` from the square
root; `1` the clip of `min c 1`; `3` the sweep parameter of `clusterRate`. -/
theorem clusterRate_eq (c : ℝ) : clusterRate 21 c = Real.exp (-(min c 1 / 508)) := by
  unfold clusterRate
  have hm : min c 1 ≤ 1 := min_le_right c 1
  have hcast : (((6 * 21 + 1 : ℕ)) : ℝ) = 127 := by norm_num
  rw [hcast]
  have h1 : Real.exp 1 / 3 ≤ Real.exp (-(min c 1 / (2 * 127))) := by
    have he := Real.exp_one_lt_d9
    have hx := Real.add_one_le_exp (-(min c 1 / (2 * 127)))
    linarith
  rw [max_eq_right h1]
  have hsq : Real.exp (-(min c 1 / (2 * 127)))
      = Real.exp (-(min c 1 / 508)) * Real.exp (-(min c 1 / 508)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsq, Real.sqrt_mul_self (Real.exp_pos _).le]

#print axioms clusterRate_eq

end Defs

/-! ## 2. From the box-local gap to the torus and infinite-volume gaps -/

section General

/-- **The torus-wide heat-bath gap from the side-15 box gap.** At `BoxLocalGap hN β 15 γ`,
`γ ≥ 759/10000`: on every torus of extent `2(j + 1) ≥ 30`, every periodic gauge-invariant `x` has
`boxConst γ · ⟨H x, x⟩ ≤ ⟨H x, H x⟩` in the torus Wilson `L²` form, `H = heatGen β j`
(`WeightedBox.globalGap_weighted`, `WeightedProduct.ProfileData.toFamily`).

DERIVED: `15`, `759/10000` as in the module; `1` the least box side and the successor in `j + 1`;
`0` the sign of `γ` and the excluded rank. -/
theorem torusGap_of_boxLocalGap (hN : N ≠ 0) {β γ : ℝ} (hbox : BoxPatch.BoxLocalGap hN β 15 γ)
    (hγ : 759 / 10000 ≤ γ) (j : ℕ) (hj : 15 ≤ j + 1)
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    boxConst γ * torusForm hN β j (heatGen β j x) x
      ≤ torusForm hN β j (heatGen β j x) (heatGen β j x) :=
  globalGap_weighted hN (by norm_num) hj hbox (lt_of_lt_of_le (by norm_num) hγ) K15_pos
    (P15.toFamily hN β (by norm_num) j hj) x

#print axioms torusGap_of_boxLocalGap

/-- **The infinite-volume transfer gap from the side-15 box gap.** At `BoxLocalGap hN β 15 γ`,
`γ ≥ 759/10000`, with `r = e^{−min(boxConst γ, 1)/508}`: `0 < r < 1`, the torus clustering
`TorusClusterAt τ p hN β r`, and `TransferGap.GapAt (periodicGaugeInvData τ p hN β) r`
(`WeightedBox.globalGap_weighted`, `HeatBathLocal.localityAt_holds`,
`HeatBathGapDecay.torusClusterAt_of_localityAt`, `HeatBathGapDecay.gapAt_of_torusClusterAt`,
`clusterRate_eq`), at every direction `τ` and plane `p`.

DERIVED: `15`, `759/10000`, `21`, `508` as in the module; `1` the least box side, the clip and the
successor in `j + 1`; `0` the lower end of the rate and the excluded rank. -/
theorem transferGap_of_boxLocalGap (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β γ : ℝ}
    (hbox : BoxPatch.BoxLocalGap hN β 15 γ) (hγ : 759 / 10000 ≤ γ) :
    0 < Real.exp (-(min (boxConst γ) 1 / 508)) ∧ Real.exp (-(min (boxConst γ) 1 / 508)) < 1
      ∧ TorusClusterAt τ p hN β (Real.exp (-(min (boxConst γ) 1 / 508)))
      ∧ MassGap.TransferGap.GapAt (MassGap.PeriodicState.periodicGaugeInvData τ p hN β)
          (Real.exp (-(min (boxConst γ) 1 / 508))) := by
  let W : ∀ j, 15 ≤ j + 1 → WeightedFamilyAt hN β 15 j P15.a₁ P15.a₂ P15.K P15.e :=
    fun j hj => P15.toFamily hN β (by norm_num) j hj
  set S := weightedFamily hN β 15 W with hS
  have hG : ∀ᶠ j in atTop, (S j).toPatchSystem.GlobalGap (boxConst γ) := by
    refine eventually_atTop.mpr ⟨15, fun j hj => ?_⟩
    have hnj : 15 ≤ j + 1 := by omega
    have hSj : S j = (W j hnj).toHB := by
      rw [hS]; unfold weightedFamily; exact dif_pos hnj
    rw [hSj]
    exact globalGap_weighted hN (by norm_num) hnj hbox (lt_of_lt_of_le (by norm_num) hγ) K15_pos
      (W j hnj)
  obtain ⟨hr0, hr1, hcl⟩ :=
    torusClusterAt_of_localityAt τ p hN β (localityAt_holds τ p hN β S) (boxConst_pos hγ) hG
  rw [clusterRate_eq] at hr0 hr1 hcl
  exact ⟨hr0, hr1, hcl, gapAt_of_torusClusterAt τ p hN β hr0.le hcl⟩

#print axioms transferGap_of_boxLocalGap

end General

/-! ## 3. At the box couplings -/

section At

/-- **`SU(2)` at `β = 3/40`: the torus-wide heat-bath gap** `boxConst (58/625)`, on every torus of
extent `2(j + 1) ≥ 30` (`torusGap_of_boxLocalGap`, `BoxGapBE.boxLocalGap15_su2`).

DERIVED: `2` the rank; `15` the box side. Inherited: `3/40`, `58/625` from `BoxGapBE`. -/
theorem torusGap_su2_at (h2 : (2 : ℕ) ≠ 0) (j : ℕ) (hj : 15 ≤ j + 1)
    (x : ↥(periodicGaugeInvSubmodule (N := 2) (2 * j + 1))) :
    boxConst (58 / 625) * torusForm h2 (3 / 40) j (heatGen (3 / 40) j x) x
      ≤ torusForm h2 (3 / 40) j (heatGen (3 / 40) j x) (heatGen (3 / 40) j x) :=
  torusGap_of_boxLocalGap h2 (BoxGapBE.boxLocalGap15_su2 h2) (by norm_num) j hj x

#print axioms torusGap_su2_at

/-- **`SU(2)` on `[0, 83/1000]`: the torus-wide heat-bath gap** `boxConst (953/12500)`
(`torusGap_of_boxLocalGap`, `BoxGapHS.boxLocalGap15_su2_hs`).

DERIVED: `2` the rank; `15` the box side; `0` the lower end. Inherited: `83/1000`, `953/12500` from
`BoxGapHS`. -/
theorem torusGap_su2_le (h2 : (2 : ℕ) ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 83 / 1000) (j : ℕ)
    (hj : 15 ≤ j + 1) (x : ↥(periodicGaugeInvSubmodule (N := 2) (2 * j + 1))) :
    boxConst (953 / 12500) * torusForm h2 β j (heatGen β j x) x
      ≤ torusForm h2 β j (heatGen β j x) (heatGen β j x) :=
  torusGap_of_boxLocalGap h2 (BoxGapHS.boxLocalGap15_su2_hs h2 hβ0 hβ) (by norm_num) j hj x

#print axioms torusGap_su2_le

/-- **`SU(3)` at `β = floorBeta 3`: the torus-wide heat-bath gap** `boxConst (367/2500)`
(`torusGap_of_boxLocalGap`, `BoxGapBE.boxLocalGap15_su3`).

DERIVED: `3` the rank; `15` the box side. Inherited: `floorBeta 3`, `367/2500` from `BoxGapBE`. -/
theorem torusGap_su3_at (h3 : (3 : ℕ) ≠ 0) (j : ℕ) (hj : 15 ≤ j + 1)
    (x : ↥(periodicGaugeInvSubmodule (N := 3) (2 * j + 1))) :
    boxConst (367 / 2500) * torusForm h3 (PairCorrSharp.floorBeta 3) j
        (heatGen (PairCorrSharp.floorBeta 3) j x) x
      ≤ torusForm h3 (PairCorrSharp.floorBeta 3) j (heatGen (PairCorrSharp.floorBeta 3) j x)
          (heatGen (PairCorrSharp.floorBeta 3) j x) :=
  torusGap_of_boxLocalGap h3 (BoxGapBE.boxLocalGap15_su3 h3) (by norm_num) j hj x

#print axioms torusGap_su3_at

/-- **`SU(3)` on `[0, 19/100]`: the torus-wide heat-bath gap** `boxConst (41/500)`
(`torusGap_of_boxLocalGap`, `BoxGapHS.boxLocalGap15_su3_hs`).

DERIVED: `3` the rank; `15` the box side; `0` the lower end. Inherited: `19/100`, `41/500` from
`BoxGapHS`. -/
theorem torusGap_su3_le (h3 : (3 : ℕ) ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 19 / 100) (j : ℕ)
    (hj : 15 ≤ j + 1) (x : ↥(periodicGaugeInvSubmodule (N := 3) (2 * j + 1))) :
    boxConst (41 / 500) * torusForm h3 β j (heatGen β j x) x
      ≤ torusForm h3 β j (heatGen β j x) (heatGen β j x) :=
  torusGap_of_boxLocalGap h3 (BoxGapHS.boxLocalGap15_su3_hs h3 hβ0 hβ) (by norm_num) j hj x

#print axioms torusGap_su3_le

/-- **`SU(2)` at `β = 3/40`: the transfer gap at the periodic state**, rate
`e^{−min(boxConst (58/625), 1)/508} ∈ (0, 1)`, with the torus clustering at that rate
(`transferGap_of_boxLocalGap`, `BoxGapBE.boxLocalGap15_su2`).

DERIVED: `2` the rank; `15` the box side; `508` as in the module. Inherited: `3/40`, `58/625` from
`BoxGapBE`. -/
theorem transferGap_su2_at (τ : Fin 4) (p : ℤ) (h2 : (2 : ℕ) ≠ 0) :
    0 < Real.exp (-(min (boxConst (58 / 625)) 1 / 508))
      ∧ Real.exp (-(min (boxConst (58 / 625)) 1 / 508)) < 1
      ∧ TorusClusterAt τ p h2 (3 / 40) (Real.exp (-(min (boxConst (58 / 625)) 1 / 508)))
      ∧ MassGap.TransferGap.GapAt (MassGap.PeriodicState.periodicGaugeInvData τ p h2 (3 / 40))
          (Real.exp (-(min (boxConst (58 / 625)) 1 / 508))) :=
  transferGap_of_boxLocalGap τ p h2 (BoxGapBE.boxLocalGap15_su2 h2) (by norm_num)

#print axioms transferGap_su2_at

/-- **`SU(2)` on `[0, 83/1000]`: the transfer gap at the periodic state**, rate
`e^{−min(boxConst (953/12500), 1)/508} ∈ (0, 1)`, uniform in `β` on the range
(`transferGap_of_boxLocalGap`, `BoxGapHS.boxLocalGap15_su2_hs`).

DERIVED: `2` the rank; `15` the box side; `0` the lower end; `508` as in the module. Inherited:
`83/1000`, `953/12500` from `BoxGapHS`. -/
theorem transferGap_su2_le (τ : Fin 4) (p : ℤ) (h2 : (2 : ℕ) ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ 83 / 1000) :
    0 < Real.exp (-(min (boxConst (953 / 12500)) 1 / 508))
      ∧ Real.exp (-(min (boxConst (953 / 12500)) 1 / 508)) < 1
      ∧ TorusClusterAt τ p h2 β (Real.exp (-(min (boxConst (953 / 12500)) 1 / 508)))
      ∧ MassGap.TransferGap.GapAt (MassGap.PeriodicState.periodicGaugeInvData τ p h2 β)
          (Real.exp (-(min (boxConst (953 / 12500)) 1 / 508))) :=
  transferGap_of_boxLocalGap τ p h2 (BoxGapHS.boxLocalGap15_su2_hs h2 hβ0 hβ) (by norm_num)

#print axioms transferGap_su2_le

/-- **`SU(3)` at `β = floorBeta 3`: the transfer gap at the periodic state**, rate
`e^{−min(boxConst (367/2500), 1)/508} ∈ (0, 1)` (`transferGap_of_boxLocalGap`,
`BoxGapBE.boxLocalGap15_su3`).

DERIVED: `3` the rank; `15` the box side; `508` as in the module. Inherited: `floorBeta 3`, `367/2500`
from `BoxGapBE`. -/
theorem transferGap_su3_at (τ : Fin 4) (p : ℤ) (h3 : (3 : ℕ) ≠ 0) :
    0 < Real.exp (-(min (boxConst (367 / 2500)) 1 / 508))
      ∧ Real.exp (-(min (boxConst (367 / 2500)) 1 / 508)) < 1
      ∧ TorusClusterAt τ p h3 (PairCorrSharp.floorBeta 3)
          (Real.exp (-(min (boxConst (367 / 2500)) 1 / 508)))
      ∧ MassGap.TransferGap.GapAt
          (MassGap.PeriodicState.periodicGaugeInvData τ p h3 (PairCorrSharp.floorBeta 3))
          (Real.exp (-(min (boxConst (367 / 2500)) 1 / 508))) :=
  transferGap_of_boxLocalGap τ p h3 (BoxGapBE.boxLocalGap15_su3 h3) (by norm_num)

#print axioms transferGap_su3_at

/-- **`SU(3)` on `[0, 19/100]`: the transfer gap at the periodic state**, rate
`e^{−min(boxConst (41/500), 1)/508} ∈ (0, 1)`, uniform in `β` on the range
(`transferGap_of_boxLocalGap`, `BoxGapHS.boxLocalGap15_su3_hs`).

DERIVED: `3` the rank; `15` the box side; `0` the lower end; `508` as in the module. Inherited:
`19/100`, `41/500` from `BoxGapHS`. -/
theorem transferGap_su3_le (τ : Fin 4) (p : ℤ) (h3 : (3 : ℕ) ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ 19 / 100) :
    0 < Real.exp (-(min (boxConst (41 / 500)) 1 / 508))
      ∧ Real.exp (-(min (boxConst (41 / 500)) 1 / 508)) < 1
      ∧ TorusClusterAt τ p h3 β (Real.exp (-(min (boxConst (41 / 500)) 1 / 508)))
      ∧ MassGap.TransferGap.GapAt (MassGap.PeriodicState.periodicGaugeInvData τ p h3 β)
          (Real.exp (-(min (boxConst (41 / 500)) 1 / 508))) :=
  transferGap_of_boxLocalGap τ p h3 (BoxGapHS.boxLocalGap15_su3_hs h3 hβ0 hβ) (by norm_num)

#print axioms transferGap_su3_le

end At

end MassGap.BoxLatticeGap
