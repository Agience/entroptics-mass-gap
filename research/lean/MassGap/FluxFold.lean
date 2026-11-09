import Mathlib
import MassGap.FlatCap
import MassGap.FiniteReadingFlux

/-!
# MassGap.FluxFold — the bridge of `FlatCap` folds into one contraction of the full doubling defect

`FlatCap` leaves the bridge as two clauses at every `β ≥ 0`: (i) contraction of `restW` (the zero-flux part of
the doubling defect `D = windowCoupling N β w`) by a fixed fraction at each doubling, and (ii)
`FluxSplitCasimir.FluxConfinedAt N β` (the mean twisted ratio tends to `1` along the windows). This module
proves that the two clauses fold into one clause on `D` itself, and that neither clause implies the other on
any reading the tree proves.

## 1. The single clause (proved)

`DefectContracts N β`: from some window `w₀ ≥ 1` on, `D(w + 1) ≤ η_w D(w)` with `0 ≤ η_w ≤ 1 − δ`, `δ > 0`.
It is a clause on the full doubling defect (zero-flux part plus the flat part carried by the flux mean,
`FlatCap.windowCoupling_split`), not a conjunction of (i) and (ii).

* `vanishes_of_defectContracts`: `DefectContracts ⇒ Vanishes` (`ZoomContract.tendsto_zero_of_contraction`).
* `defectContracts_of_vanishes`: `Vanishes ⇒ DefectContracts` with `η = 1/4`: once `D ≤ 1/1000` the
  quadratic recursion `D(w+1) ≤ 250 D(w)²` (`CouplingTower.basin_contracts`) divides `D` by `4` at every
  doubling. So any fixed contraction fraction is equivalent to the basin's `1/4`.
* `defectContracts_of_bridge`: (i) ∧ (ii) ⇒ `DefectContracts` (through `FlatCap.vanishes_of_rest_contraction`).
* `fluxConfined_of_defectContracts`, `zeroFluxVanishing_of_defectContracts`, `restW_tendsto_of_defectContracts`:
  `DefectContracts` gives (ii), the vanishing zero-flux defect and `restW → 0`.
* `defectContracts_iff_rest_flux`: `DefectContracts ↔ restW → 0 ∧ FluxConfinedAt`.

The bridge (i) ∧ (ii) implies `DefectContracts`, and `DefectContracts` is equivalent to `Vanishes`; nothing
open is reduced. `DefectContracts` implies (ii) and the limit form of (i). Plainly, `DefectContracts` does not give (i) in its contraction form: that would need a
lower bound of `restW` by `D`, and the tree has none (the flat part may be negative,
`FlatCap.flatStep_bounds`). The limit form `restW → 0` is what the vanishing read uses, and it suffices
(`defectContracts_iff_rest_flux`). Plainly also, `DefectContracts` is equivalent to the vanishing read itself
(`defectContracts_iff_vanishes`); the fold consolidates the bridge onto the full defect, it does not reduce
the open content.

## 2. Neither clause implies the other on a generic reading (proved, plainly)

* (i) does not give (ii): `z2_deconfined`. On `Bool` with the uniform measure, `Z₂` acting by the flip, the
  kernel `kB 1 = 1 + s(x) s(y)` is bounded, symmetric, invariant and idempotent (`kB 1 ∗ kB 1 = kB 1`), so it
  is its own transfer at every time extent. Its zero-flux kernel is the constant `1`, whose doubling defect is
  `0` (it contracts with any fraction), and its flux share is `1/2 = 1 − |Z₂|⁻¹` at every extent: the
  degenerate share of a deconfined centre (`FluxSplitCasimir.not_noCasimirAt_of_degenerate`).
* (ii) is independent of (i) given the Wilson share: `neutral_separates` (from `FiniteReadingFlux.wilson_neutral`). The Wilson slice
  tensored with a neutral two-state factor has every twisted ratio and the flux share of the Wilson slice, so
  (ii) holds for it exactly when it holds for Wilson, and its zero-flux defect is at least `log(25/17) > 0` at
  every window, so (i) fails for it.

Both readings are generic kernels with a centre action, not the Wilson torus. So no implication between (i) and
(ii) can come from the sector algebra alone (`zk_conv`, the sector split, the cap); it would have to use
the Wilson action. The proved Tomboulis–Yaffe and chessboard forms (`TomboulisYaffe.tyTwo_of_chessboard`,
`VortexTwo`) bound Wilson loops by the twisted ratio; they do not bound the zero-flux defect, and the zero-flux
defect does not enter them. Plainly, the tree proves no implication between (i) and (ii) on the Wilson torus.

## 3. Load tests (proved)

* `N = 1`: `fluxConfined_one` (no centre: share `≤ 0` at every `β ≥ 0`), and `defectContracts_one_iff`:
  `DefectContracts 1 β ↔ RestContracts 1 β`; at `N = 1` the bridge is (i) alone and the fold is exact.
* The anchor: `anchor_defectContracts`: on `[0, β₀)` the single clause holds (from
  `ZoomContract.anchor_by_contraction`, inherited).

DERIVED (module-wide): `1` the least window and the unit of the flip kernel; `0` signs and limits;
`1/4`, `3/4 = 1 − 1/4` the basin's contraction (`1/4 = 1/(250 · 1/1000)`, `CouplingTower.basin_contracts`);
`1/1000` the seed of `DoublingSharp` (inherited); `2 = |Z₂|`, `1/2 = 1 − |Z₂|⁻¹` the degenerate share;
`25/17` the neutral factor's defect (inherited, `FiniteReadingFlux.dd_kB_half`); `3` the exponent of `|Z_N³|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FluxFold

open Filter Topology MeasureTheory
open MassGap.KernelPower MassGap.SectorDefect MassGap.ZeroFluxSector
open MassGap.CouplingTower (windowCoupling windowCoupling_nonneg)
open MassGap.CentreSectorSeedN (hSN halfKN trivKN fluxShareN trivialDefectN)
open MassGap.LineSeedsVanishing (ZeroFluxVanishing)
open MassGap.FluxSplitCasimir (FluxConfinedAt)
open MassGap.FlatCap (restW flatW fluxW)

section Wilson

variable {N : ℕ} [NeZero N]

/-! ## 1. The single clause -/

variable (N) in
/-- **The full doubling defect contracts by a fixed fraction**, from a window `w₀ ≥ 1` on.
DERIVED: `1` the least window; `0` the signs. -/
def DefectContracts (β : ℝ) : Prop :=
  ∃ w₀ : ℕ, 1 ≤ w₀ ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℕ → ℝ, (∀ w, w₀ ≤ w → 0 ≤ η w) ∧
    (∀ w, w₀ ≤ w → η w ≤ 1 - δ) ∧ ∀ w, w₀ ≤ w → windowCoupling N β (w + 1) ≤ η w * windowCoupling N β w

variable (N) in
/-- **Clause (i) of `FlatCap`**: the zero-flux part `restW` contracts by a fixed fraction.
DERIVED: `0` the signs. -/
def RestContracts (β : ℝ) : Prop :=
  ∃ w₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℕ → ℝ, (∀ w, w₀ ≤ w → 0 ≤ η w) ∧
    (∀ w, w₀ ≤ w → η w ≤ 1 - δ) ∧ ∀ w, w₀ ≤ w → restW N β (w + 1) ≤ η w * restW N β w

/-- **The single clause gives the vanishing read.** DERIVED: `1` the least window. -/
theorem vanishes_of_defectContracts {β : ℝ} (hβ : 0 ≤ β) (h : DefectContracts N β) :
    StrongAnchor.Vanishes N β := by
  obtain ⟨w₀, hw₀, δ, hδ, η, hη, hgap, hstep⟩ := h
  exact ZoomContract.tendsto_zero_of_contraction w₀
    (fun w hw => windowCoupling_nonneg (NeZero.ne N) hβ (hw₀.trans hw)) hη hstep
    (ZoomContract.divergence_of_gap w₀ hδ hgap)

/-- **The vanishing read gives the single clause, with the basin's fraction `1/4`.**
DERIVED: `1/1000` the seed (inherited); `1/4` the basin contraction, `3/4 = 1 − 1/4`; `1` the least window. -/
theorem defectContracts_of_vanishes {β : ℝ} (hβ : 0 ≤ β) (h : StrongAnchor.Vanishes N β) :
    DefectContracts N β := by
  have hev : ∀ᶠ w in atTop, windowCoupling N β w ≤ 1 / 1000 ∧ 1 ≤ w :=
    (h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))).and (eventually_ge_atTop 1)
  obtain ⟨w₁, hw₁⟩ := eventually_atTop.mp hev
  refine ⟨w₁ + 1, by omega, 3 / 4, by norm_num, fun _ => 1 / 4, fun _ _ => by norm_num,
    fun _ _ => by norm_num, fun w hw => ?_⟩
  obtain ⟨hs, h1⟩ := hw₁ w (by omega)
  have := CouplingTower.basin_contracts (NeZero.ne N) hβ h1 hs
  show _ ≤ 1 / 4 * _
  linarith

/-- **The single clause is the vanishing read.** DERIVED: no numeral. -/
theorem defectContracts_iff_vanishes {β : ℝ} (hβ : 0 ≤ β) :
    DefectContracts N β ↔ StrongAnchor.Vanishes N β :=
  ⟨vanishes_of_defectContracts hβ, defectContracts_of_vanishes hβ⟩

/-- **The bridge gives the single clause.** DERIVED: no numeral. -/
theorem defectContracts_of_bridge {β : ℝ} (hβ : 0 ≤ β) (hR : RestContracts N β)
    (hF : FluxConfinedAt N β) : DefectContracts N β := by
  obtain ⟨w₀, δ, hδ, η, hη, hgap, hstep⟩ := hR
  exact defectContracts_of_vanishes hβ
    (FlatCap.vanishes_of_rest_contraction hβ w₀ hδ hη hgap hstep hF)

/-- **The single clause gives clause (ii).** DERIVED: no numeral. -/
theorem fluxConfined_of_defectContracts {β : ℝ} (hβ : 0 ≤ β) (h : DefectContracts N β) :
    FluxConfinedAt N β :=
  (FluxSplitCasimir.sectors_of_noCasimirAt hβ
    ((CasimirStep.vanishing_iff_noCasimirAt N β).mp (vanishes_of_defectContracts hβ h))).1

/-- **The single clause gives the vanishing zero-flux defect.** DERIVED: no numeral. -/
theorem zeroFluxVanishing_of_defectContracts {β : ℝ} (hβ : 0 ≤ β) (h : DefectContracts N β) :
    ZeroFluxVanishing N β :=
  (FluxSplitCasimir.sectors_of_noCasimirAt hβ
    ((CasimirStep.vanishing_iff_noCasimirAt N β).mp (vanishes_of_defectContracts hβ h))).2

/-- **The single clause gives the limit form of clause (i)**: `restW → 0`. DERIVED: `0` the limit. -/
theorem restW_tendsto_of_defectContracts {β : ℝ} (hβ : 0 ≤ β) (h : DefectContracts N β) :
    Tendsto (restW N β) atTop (𝓝 0) :=
  ((FlatCap.vanishes_iff_split hβ).mp (vanishes_of_defectContracts hβ h)).1

/-- **The single clause is the limit form of (i) with (ii).** DERIVED: `1` the least window; `2` the square
in `dd`; `0` signs and limits. -/
theorem defectContracts_iff_rest_flux {β : ℝ} (hβ : 0 ≤ β) :
    DefectContracts N β ↔ Tendsto (restW N β) atTop (𝓝 0) ∧ FluxConfinedAt N β := by
  refine ⟨fun h => ⟨restW_tendsto_of_defectContracts hβ h, fluxConfined_of_defectContracts hβ h⟩,
    fun ⟨hr, hF⟩ => defectContracts_of_vanishes hβ ?_⟩
  have hup := hr.add ((FlatCap.tendsto_fluxW hβ hF).const_mul 2)
  rw [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with w hw
    exact windowCoupling_nonneg (NeZero.ne N) hβ hw
  · filter_upwards [eventually_ge_atTop 1] with w hw
    rw [FlatCap.windowCoupling_split hβ hw]
    linarith [FlatCap.flatW_le_fluxW (N := N) hβ w]

/-! ## 2. (ii) does not give (i): the neutral factor -/

/-- **A reading with the Wilson flux and a zero-flux defect bounded away from `0`.** The Wilson slice tensored
with the neutral factor `kB ½` keeps the flux share of the Wilson slice and has zero-flux defect at least
`log(25/17)`. DERIVED: `25/17` and `1/2` inherited from `FiniteReadingFlux.wilson_neutral`. -/
theorem neutral_separates {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    FiniteReadingFlux.fluxShare ((hSN N n i).prod FiniteReadingFlux.νB)
        (FiniteReadingFlux.tensor (halfKN N β n i) (FiniteReadingFlux.kB (1 / 2)))
        (FiniteReadingFlux.prodAct (Z := Bool)
          (SliceCentreAction.act (μ := i) (T := CentreSectorSeed.Tr n i) (N := N)))
      = fluxShareN N β n i ∧
    Real.log (25 / 17) ≤ dd ((hSN N n i).prod FiniteReadingFlux.νB)
        (zk (FiniteReadingFlux.tensor (halfKN N β n i) (FiniteReadingFlux.kB (1 / 2)))
          (FiniteReadingFlux.prodAct (Z := Bool)
            (SliceCentreAction.act (μ := i) (T := CentreSectorSeed.Tr n i) (N := N)))) := by
  have h := FiniteReadingFlux.wilson_neutral (N := N) hβ n i
  dsimp only at h
  obtain ⟨-, -, -, -, -, -, -, hsh, hdd⟩ := h
  refine ⟨hsh, ?_⟩
  rw [hdd]
  linarith [FlatCap.trivialDefectN_nonneg (N := N) hβ n i]

/-! ## 3. Load tests -/

/-- **Load test, `N = 1`**: the flux is confined at every `β ≥ 0` (no centre). DERIVED: `1` the trivial
group; `3` the exponent of `|Z_N³|`. -/
theorem fluxConfined_one {β : ℝ} (hβ : 0 ≤ β) : FluxConfinedAt 1 β := by
  intro i ε hε
  refine Eventually.of_forall fun w => ?_
  have hA := CentreSectorSeedN.hs_halfKN_pos (N := 1) hβ (2 ^ w) i
  have hge := CentreSectorSeedN.hs_trivKN_ge (N := 1) hβ (2 ^ w) i
  simp only [Nat.cast_one, one_pow, div_one] at hge
  have : fluxShareN 1 β (2 ^ w) i ≤ 0 := by
    unfold fluxShareN
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  linarith

/-- **Load test, `N = 1`**: the single clause is clause (i). DERIVED: `1` the trivial group and the least
window. -/
theorem defectContracts_one_iff {β : ℝ} (hβ : 0 ≤ β) : DefectContracts 1 β ↔ RestContracts 1 β := by
  constructor
  · rintro ⟨w₀, hw₀, δ, hδ, η, hη, hgap, hstep⟩
    refine ⟨w₀, δ, hδ, η, hη, hgap, fun w hw => ?_⟩
    have h := hstep w hw
    rwa [FlatCap.windowCoupling_eq_rest_one hβ (hw₀.trans (hw.trans (Nat.le_succ w))),
      FlatCap.windowCoupling_eq_rest_one hβ (hw₀.trans hw)] at h
  · intro hR
    exact defectContracts_of_bridge hβ hR (fluxConfined_one hβ)

/-- **Load test, the anchor**: the single clause holds on `[0, β₀)`. Inherited from
`ZoomContract.anchor_by_contraction`. DERIVED: `0` the lower end. -/
theorem anchor_defectContracts :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → DefectContracts N β := by
  obtain ⟨β₀, hβ₀, h⟩ := ZoomContract.anchor_by_contraction (N := N) (NeZero.ne N)
  exact ⟨β₀, hβ₀, fun β h0 hlt => defectContracts_of_vanishes h0 (h β h0 hlt)⟩

end Wilson

/-! ## 2. (i) does not give (ii): the deconfined `Z₂` reading -/

section Z2

open MassGap.FiniteReadingFlux (νB sgn kB integral_νB)

/-- The `Z₂` flip on `Bool`. DERIVED: `0` the identity element. -/
def flipAct (g : ZMod 2) (x : Bool) : Bool := if g = 0 then x else !x

/-- The flip is a measure-preserving action of `Z₂`. -/
theorem flip_centreAction : FluxSectorFourier.CentreAction νB flipAct where
  meas _ := measurable_of_countable _
  zero x := by simp [flipAct]
  add g h x := by fin_cases g <;> fin_cases h <;> cases x <;> decide
  mp g := by
    refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun b => ?_⟩
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton b)]
    have e : flipAct g ⁻¹' {b} = {flipAct g b} := by
      ext x; fin_cases g <;> cases x <;> cases b <;> simp [flipAct]
    rw [e]
    simp [νB]

/-- `kB 1` is invariant under the flip. -/
theorem kB_one_inv (g : ZMod 2) (x y : Bool) : kB 1 (flipAct g x) (flipAct g y) = kB 1 x y := by
  have h2 : ∀ g : ZMod 2, g = 0 ∨ g = 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases h2 g with rfl | rfl <;> cases x <;> cases y <;> simp [flipAct, kB, sgn, h10]

/-- `kB 1` is idempotent: its own transfer at every time extent. DERIVED: `1` the unit. -/
theorem kB_one_idem : conv νB (kB 1) (kB 1) = kB 1 := by
  rw [FiniteReadingFlux.conv_kB, one_mul]

/-- The zero-flux kernel of `kB 1` is the constant `1`. DERIVED: `2 = |Z₂|`. -/
theorem zk_kB_one : zk (kB 1) flipAct = fun _ _ => 1 := by
  funext x y
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  unfold zk
  rw [hu, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), ZMod.card]
  cases x <;> cases y <;> norm_num [flipAct, kB, sgn]

/-- The constant kernel has doubling defect `0`. DERIVED: `1` the unit; `2` the square in `dd`. -/
theorem dd_const_one : dd νB (fun _ _ : Bool => (1 : ℝ)) = 0 := by
  have hc : conv νB (fun _ _ : Bool => (1 : ℝ)) (fun _ _ => 1) = fun _ _ => 1 := by
    funext x z; simp only [conv, integral_νB]; norm_num
  have hh : hs νB (fun _ _ : Bool => (1 : ℝ)) = 1 := by simp only [hs, integral_νB]; norm_num
  unfold dd
  rw [hc, hh, Real.log_one]
  ring

/-- **The deconfined `Z₂` reading**: a bounded, symmetric, flip-invariant, idempotent kernel whose zero-flux
defect is `0` and whose flux share is `1/2 = 1 − |Z₂|⁻¹` at every time extent. It is one kernel, not a window
sequence: its zero-flux defect is `0` (the analogue of (i)) and its flux share is the constant `1/2`, so it does
not tend to `0` (the analogue of (ii) fails). DERIVED: `1` the unit; `1/2 = 1 − 1/2` the degenerate share of `Z₂`. -/
theorem z2_deconfined :
    FluxSectorFourier.CentreAction νB flipAct ∧ Bdd (kB 1) ∧ (∀ x y, kB 1 x y = kB 1 y x) ∧
      (∀ g x y, kB 1 (flipAct g x) (flipAct g y) = kB 1 x y) ∧
      conv νB (kB 1) (kB 1) = kB 1 ∧
      dd νB (zk (kB 1) flipAct) = 0 ∧
      FiniteReadingFlux.fluxShare νB (kB 1) flipAct = 1 / 2 := by
  refine ⟨flip_centreAction, FiniteReadingFlux.bdd_kB 1, FiniteReadingFlux.kB_symm 1, kB_one_inv,
    kB_one_idem, by rw [zk_kB_one, dd_const_one], ?_⟩
  unfold FiniteReadingFlux.fluxShare
  rw [zk_kB_one, FiniteReadingFlux.hs_kB]
  have hh : hs νB (fun _ _ : Bool => (1 : ℝ)) = 1 := by simp only [hs, integral_νB]; norm_num
  rw [hh]
  norm_num

end Z2

end MassGap.FluxFold

end

#print axioms MassGap.FluxFold.vanishes_of_defectContracts
#print axioms MassGap.FluxFold.defectContracts_of_vanishes
#print axioms MassGap.FluxFold.defectContracts_iff_vanishes
#print axioms MassGap.FluxFold.defectContracts_of_bridge
#print axioms MassGap.FluxFold.fluxConfined_of_defectContracts
#print axioms MassGap.FluxFold.zeroFluxVanishing_of_defectContracts
#print axioms MassGap.FluxFold.restW_tendsto_of_defectContracts
#print axioms MassGap.FluxFold.defectContracts_iff_rest_flux
#print axioms MassGap.FluxFold.neutral_separates
#print axioms MassGap.FluxFold.fluxConfined_one
#print axioms MassGap.FluxFold.defectContracts_one_iff
#print axioms MassGap.FluxFold.anchor_defectContracts
#print axioms MassGap.FluxFold.flip_centreAction
#print axioms MassGap.FluxFold.kB_one_inv
#print axioms MassGap.FluxFold.kB_one_idem
#print axioms MassGap.FluxFold.zk_kB_one
#print axioms MassGap.FluxFold.dd_const_one
#print axioms MassGap.FluxFold.z2_deconfined
