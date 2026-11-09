import Mathlib
import MassGap.FloorTension

/-!
# MassGap.VortexSheetFlux — flux confinement is the vanishing of the temporal vortex free energies

`FluxSplitCasimir.FluxConfinedAt N β`, the flux half of the bridge, reads the flux share of the
window `2^w` at the four corner steps. `CentreSectorSeedN.fluxShareN_eq_mean` writes that share as
`1 − N⁻³ Σ_g Z_g/Z` over the `N³` 't Hooft twists `g` of the transverse planes. This module turns the
flux half into a statement about the single twists, and for `SU(2)` about the vortex free energy
`GapSideVortexRect.vortexR = −log(Z_tw/Z)` of a centre sheet.

## What is proved

* `twistRatioN_le_one`: `Z_g/Z ≤ 1` at every twist (reflection positivity in sector form,
  `TwistDeficitUnionN.deficit_nonneg`).
* `one_sub_twistRatioN_le`: `1 − Z_g/Z ≤ N³ · fluxShareN`. The flux share bounds every twist deficit.
* **`fluxConfinedAt_iff_twists`**: for `β ≥ 0`, `FluxConfinedAt N β` iff at every step `i` and every
  transverse direction `ν` the single twist ratio `Z_{e_ν}/Z` of the window `2^w` tends to `1`.
  Forward by `one_sub_twistRatioN_le`; backward by the union bound
  `TwistDeficitUnionN.fluxShareN_le_of_single`.
* `twistRatio_two_eq_exp`: for `SU(2)` and `w ≥ 1`, `Z_{e_ν}/Z = exp(−vortexR)` on the corner torus
  `Lc (2^w) i`, the sheet in the plane `(i, ν)`.
* **`fluxConfinedAt_two_iff_vortexR`**: `FluxConfinedAt 2 β` iff every temporal sheet's vortex free
  energy `vortexR (Lc (2^w) i) i ν β` tends to `0` along the windows.
* **`strongEnd_two_iff_vortexR`**: `CouplingTower.StrongEnd 2` iff, frequently as `β → ∞`, every
  temporal vortex free energy tends to `0` along the windows and the zero-flux defect vanishes
  (`LineSeedsVanishing.ZeroFluxVanishing`).
* `vortexR_tendsto_of_tension`: a measured tension (`LineSeedsBasin.TensionBelow` with `A β > 0`)
  drives every temporal vortex free energy to `0`, through `FluxSplitCasimir.fluxConfinedAt_of_tension`.

## Direction

The flux half needs the twisted ratios to rise to `1`: the cost of inserting a centre sheet across
the whole temporal cross-section must vanish as the window grows. A per-unit-area cost `μ` of a
sheet bounds `vortexR` above by `μ` times an area that grows with the window, so it says nothing
about `vortexR → 0`. Entropy enters on the other side. `VortexEntropy.floorTerm_summable_iff` shows
the sum over closed sheets through a plaquette diverges at `μ ≤ ¼ ln 3`; the vortex free energy tends
to `0` only if the twisted and untwisted ensembles become indistinguishable, which is a statement
about the sheets that are present, not about the convergence of a sum.

DERIVED (module-wide): `1` the twist generator `e_ν` and the ratio's limit; `0` the limit of the free
energy and the lower end of the couplings; `2` the window base, the rank, and the least even side;
`3` the power `N³ = |Z_N³|` (`SliceCentreAction.card_cen`); `4` the steps; `9 ⌊N/2⌋²` is
`TwistDeficitUnionN.twistRatioN_ge_of_single`'s union constant.

## What does not follow

* No twisted ratio is bounded here at any `β > 0` beyond what the tree already gives
  (`StrongAnchor.strongAnchor` near `0`). The equivalences move the flux half onto the temporal
  vortex free energies; they do not prove that those tend to `0`.
* No theorem in the tree connects a per-area weight of closed sheets (`VortexEntropy`) to `vortexR`.
  The missing link is a representation of `Z_tw/Z` as the expectation of a sign over a gas of centre
  sheets linked with the twist, together with an estimate showing that gas fills the cross-section.
  The tree's sheet polymer representation (`VortexStrong.ZRp_eq_polymerZ`) is the convergent one, the
  regime of `StrongAnchor`.
* The zero-flux half (`ZeroFluxVanishing`) is untouched.
-/

noncomputable section

namespace MassGap.VortexSheetFlux

open Filter Topology
open MassGap.CentreSectorSeedN (fluxShareN twistRatioN fluxShareN_eq_mean hs_halfKN_pos bdd_halfKN)
open MassGap.FluxSplitCasimir (FluxConfinedAt)
open MassGap.SliceCentreAction (Cen centreAction card_cen)
open MassGap.GapSideVortexRect (vortexR zR Lc)

variable {N : ℕ} [NeZero N]

/-- **Every twisted ratio is at most `1`.** DERIVED: `1` the untwisted ratio. -/
theorem twistRatioN_le_one {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i N) :
    twistRatioN N β n i g ≤ 1 := by
  have h := TwistDeficitUnionN.one_sub_twistRatioN (N := N) hβ n i g
  have hA := hs_halfKN_pos (N := N) hβ n i
  have h0 : 0 ≤ 1 - twistRatioN N β n i g := by
    rw [h]
    exact div_nonneg (TwistDeficitUnionN.deficit_nonneg (bdd_halfKN hβ n i) centreAction g) hA.le
  linarith

/-- **The flux share bounds every twist deficit**: `1 − Z_g/Z ≤ N³ fluxShareN`. An alias of
`FluxCost.one_sub_twistRatioN_le_cube`. -/
alias one_sub_twistRatioN_le := MassGap.FluxCost.one_sub_twistRatioN_le_cube

/-- **Flux confinement is the single twist ratios rising to `1`.**
DERIVED: `1` the generator and the limit; `2` the window base; `9 ⌊N/2⌋²` the union constant. -/
theorem fluxConfinedAt_iff_twists {β : ℝ} (hβ : 0 ≤ β) :
    FluxConfinedAt N β ↔ ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
      Tendsto (fun w : ℕ => twistRatioN N β (2 ^ w) i (Pi.single ν 1)) atTop (𝓝 1) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  constructor
  · intro hF i ν
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => Eventually.of_forall fun w =>
      (twistRatioN_le_one hβ _ i _).trans_lt hb⟩
    have hε : 0 < (1 - a) / (2 * (N : ℝ) ^ 3) := div_pos (by linarith) (by positivity)
    filter_upwards [hF i _ hε] with w hw
    have h1 := one_sub_twistRatioN_le hβ (2 ^ w) i (Pi.single ν 1 : Cen i N)
    have h2 : (N : ℝ) ^ 3 * fluxShareN N β (2 ^ w) i ≤ (N : ℝ) ^ 3 * ((1 - a) / (2 * (N : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left hw hN3.le
    have h3 : (N : ℝ) ^ 3 * ((1 - a) / (2 * (N : ℝ) ^ 3)) = (1 - a) / 2 := by
      field_simp
    linarith
  · intro h i ε hε
    have hC : (0 : ℝ) ≤ 9 * ((N / 2 : ℕ) : ℝ) ^ 2 := by positivity
    have hδ : 0 < ε / (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1) := div_pos hε (by linarith)
    have hall : ∀ᶠ w in atTop, ∀ ν : {j : Fin 4 // j ≠ i},
        1 - ε / (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1) ≤ twistRatioN N β (2 ^ w) i (Pi.single ν 1) := by
      rw [Filter.eventually_all]
      intro ν
      exact ((h i ν).eventually (Ioi_mem_nhds (by linarith))).mono fun w hw => le_of_lt hw
    filter_upwards [hall] with w hw
    have hs := TwistDeficitUnionN.fluxShareN_le_of_single hβ (2 ^ w) i hδ.le hw
    have hm : 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * (ε / (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1))
        ≤ (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1) * (ε / (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have he : (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1) * (ε / (9 * ((N / 2 : ℕ) : ℝ) ^ 2 + 1)) = ε := by
      field_simp
    linarith

/-- **For `SU(2)` the single twist ratio is `exp(−vortexR)`** on the corner torus, `w ≥ 1`.
DERIVED: `2` the rank and the window base; `1` the least window with an even side `≥ 2`. -/
theorem twistRatio_two_eq_exp {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) :
    twistRatioN 2 β (2 ^ w) i (Pi.single ν 1) = Real.exp (-(vortexR (Lc (2 ^ w) i) i ν.1 β)) := by
  have hn : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have he : Even (2 ^ w) := (Nat.even_pow' (by omega)).mpr even_two
  rw [GapSideVortexRect.twistRatioN_eq_zR hβ hn he i ν, vortexR, neg_neg,
    Real.exp_log (GapSideVortexRect.zR_pos _ _ _ _)]

/-- **`SU(2)` flux confinement is the vanishing of every temporal vortex free energy.**
DERIVED: `2` the rank and the window base; `0` the limit; `1` the least window. -/
theorem fluxConfinedAt_two_iff_vortexR {β : ℝ} (hβ : 0 ≤ β) :
    FluxConfinedAt 2 β ↔ ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
      Tendsto (fun w : ℕ => vortexR (Lc (2 ^ w) i) i ν.1 β) atTop (𝓝 0) := by
  rw [fluxConfinedAt_iff_twists hβ]
  refine forall_congr' fun i => forall_congr' fun ν => ?_
  have he : (fun w : ℕ => twistRatioN 2 β (2 ^ w) i (Pi.single ν 1))
      =ᶠ[atTop] (fun w : ℕ => Real.exp (-(vortexR (Lc (2 ^ w) i) i ν.1 β))) := by
    filter_upwards [eventually_ge_atTop 1] with w hw
    exact twistRatio_two_eq_exp hβ hw i ν
  rw [tendsto_congr' he]
  constructor
  · intro h
    have hl := ((Real.continuousAt_log one_ne_zero).tendsto.comp h).neg
    rw [Real.log_one, neg_zero] at hl
    refine hl.congr fun w => ?_
    simp [Function.comp, Real.log_exp]
  · intro h
    have hn := h.neg
    rw [neg_zero] at hn
    have hc := (Real.continuous_exp.tendsto 0).comp hn
    rw [Real.exp_zero] at hc
    exact hc

/-- **The `SU(2)` bridge in vortex form**: `StrongEnd 2` iff, frequently as `β → ∞`, every temporal
vortex free energy tends to `0` along the windows and the zero-flux defect vanishes.
DERIVED: `2` the rank; `0` the limit and the lower end of the couplings. -/
theorem strongEnd_two_iff_vortexR :
    CouplingTower.StrongEnd 2 ↔ ∃ᶠ β in atTop,
      (∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
        Tendsto (fun w : ℕ => vortexR (Lc (2 ^ w) i) i ν.1 β) atTop (𝓝 0))
      ∧ LineSeedsVanishing.ZeroFluxVanishing 2 β := by
  rw [StrongAnchor.strongEnd_iff_frequently_vanishes]
  constructor
  · intro h
    refine (h.and_eventually (eventually_ge_atTop 0)).mono ?_
    rintro β ⟨hV, hβ⟩
    obtain ⟨hF, hZ⟩ := (FloorTension.vanishes_iff_flux_zeroFlux hβ).mp hV
    exact ⟨(fluxConfinedAt_two_iff_vortexR hβ).mp hF, hZ⟩
  · intro h
    refine (h.and_eventually (eventually_ge_atTop 0)).mono ?_
    rintro β ⟨⟨hF, hZ⟩, hβ⟩
    exact (FloorTension.vanishes_iff_flux_zeroFlux hβ).mpr
      ⟨(fluxConfinedAt_two_iff_vortexR hβ).mpr hF, hZ⟩

/-- **A measured tension drives every temporal vortex free energy to `0`.**
DERIVED: `2` the rank; `0` the signs and the limit. -/
theorem vortexR_tendsto_of_tension {A : ℝ → ℝ} (hT : LineSeedsBasin.TensionBelow 2 A) {β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 < A β) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) :
    Tendsto (fun w : ℕ => vortexR (Lc (2 ^ w) i) i ν.1 β) atTop (𝓝 0) :=
  (fluxConfinedAt_two_iff_vortexR hβ).mp (FluxSplitCasimir.fluxConfinedAt_of_tension hT hβ hA) i ν

#print axioms twistRatioN_le_one
#print axioms one_sub_twistRatioN_le
#print axioms fluxConfinedAt_iff_twists
#print axioms twistRatio_two_eq_exp
#print axioms fluxConfinedAt_two_iff_vortexR
#print axioms strongEnd_two_iff_vortexR
#print axioms vortexR_tendsto_of_tension

end MassGap.VortexSheetFlux

end
