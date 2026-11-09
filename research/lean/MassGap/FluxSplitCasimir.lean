import Mathlib
import MassGap.CasimirStep
import MassGap.LineSeedsVanishing

/-!
# MassGap.FluxSplitCasimir — the Casimir term splits into confinement and binding

`CasimirStep` proves that the window coupling vanishes at `β` iff `NoCasimirAt N β`: the finite-size free energy
of the periodic Wilson torus is `o(1/volume)`. `CentreSectorSeedN` splits each corner step of the window coupling
into the electric-flux sectors of the centre `Z_N³` ('t Hooft's twisted sectors of the slice): the flux share
`fluxShareN` (the trace carried by non-zero electric flux) and the zero-flux defect `trivialDefectN`. This module
proves that the Casimir term splits exactly along those sectors, gives each sector a quantitative lower bound on
the Casimir coefficient, and tests the constant-mode mechanism. Declarations are in the namespace
`MassGap.FluxSplitCasimir`.

## 1. Lower bounds on the real torus (proved)

* `windowCoupling_ge`: some `κ > 0` (depending on `N`) gives, at `β ≥ 0`, window `w ≥ 1`, step `i`,
  `min(κ s/N³, κ) ≤ g β w` with `s` the flux share, and `min(κ t, κ) ≤ g β w` with `t` the zero-flux defect
  (`CentreSectorSeedN.sectors_of_defectWN` read backwards; the explicit `κ` is proof-internal).
* `casimir_ge_of_flux`: some `κ > 0` makes a flux share at least `s` on infinitely many windows give every
  Casimir coefficient `c` (finite-size correction `c / volume`) the bound `min(κ s/N³, κ) ≤ 15 c`.
  `not_noCasimirAt_of_flux`: for `s > 0` there is no `NoCasimirAt`.
  `not_noCasimirAt_of_degenerate`: a flux share at least `1 − N⁻³` on infinitely many windows, at `N ≥ 2`,
  excludes `NoCasimirAt`. By `CentreSectorSeedN.fluxShareN_eq_mean` that is the share when every non-trivial
  twisted ratio is `0`, the exactly degenerate flux sectors of a deconfined centre (argued reading of the
  `Z₂`-at-weak-coupling phase); the theorem states that failure on the Wilson torus itself.
* `casimir_ge_of_zeroFlux`, `not_noCasimirAt_of_zeroFlux`: the same (bound `min(κ t, κ) ≤ 15 c`) from a
  zero-flux defect at least `t > 0` on infinitely many windows. This is the Coulomb failure: a neutral sector
  whose excited weight at the window's own time extent does not die.

## 2. The exact split (proved)

`FluxConfinedAt N β`: at every step the flux share of the window `2^w` is eventually below every positive value
(electric flux free energy unbounded along the windows: 't Hooft's confinement criterion, read on the windows).
`LineSeedsVanishing.ZeroFluxVanishing N β`: the same for the zero-flux defect.
`NeutralBindingAt N β`: at every step, for every `ε > 0` some `δ > 0` makes, eventually in `w`, a flux share
at most `δ` force a zero-flux defect at most `ε` (the neutral sector is held by the flux).

* `sectors_of_noCasimirAt`, `noCasimirAt_of_sectors`, `noCasimirAt_iff_sectors`: at `β ≥ 0`,
  `NoCasimirAt N β ↔ FluxConfinedAt N β ∧ ZeroFluxVanishing N β`.
* `zeroFluxVanishing_of_binding`, `binding_of_zeroFluxVanishing`: under `FluxConfinedAt N β`,
  `NeutralBindingAt N β ↔ ZeroFluxVanishing N β`; relative to confinement, binding is the zero-flux gap at the
  window.
* `noCasimirAt_iff_binding`: at `β ≥ 0`, `NoCasimirAt N β ↔ FluxConfinedAt N β ∧ NeutralBindingAt N β`.
* `fluxConfinedAt_of_tension`: `LineSeedsBasin.TensionBelow N A` with `0 < A β` gives `FluxConfinedAt N β`.
* `noCasimirAt_of_tension_binding`, `windowGap_of_tension_binding`, `strongEnd_of_tension_binding`: positive
  measured tension and `NeutralBindingAt` give `NoCasimirAt`, the periodic Clay gap at `β`, and (frequently in
  `β`) the strong end. `strongEnd_of_tension_binding` is `LineSeedsVanishing.strongEnd_of_tension_zeroFlux`
  restated through the binding equivalence (under `FluxConfinedAt`, `NeutralBindingAt` is exactly
  `ZeroFluxVanishing`), not a further reduction.

## 3. What each factor separates (argued readings; the theorems above are the proved part)

* The analogue of `FluxConfinedAt` fails for `Z₂` and for `U(1)` at weak coupling: in the deconfined `Z₂`
  phase the electric flux sectors are degenerate with the vacuum (share `→ 1 − 2⁻³`); in the Coulomb phase an
  electric flux line across a torus of side `L` costs energy `∝ e²/L`, so over time extent `L` its free energy
  stays bounded and the share stays positive. Section 1 turns either into a positive Casimir coefficient.
* The analogue of `NeutralBindingAt` holds for `Z₂` and `U(1)` at weak coupling, because there the flux share
  does not fall below a fixed positive value and the clause asks nothing (in `Z₂` the zero-flux sector is also
  gapped). It
  fails for a reading with a neutral sector decoupled from the flux: `FiniteReadingFlux.wilson_neutral` (proved)
  tensors the Wilson slice with a neutral factor; every twisted ratio and the flux share are unchanged and the
  zero-flux defect rises by `log(25/17)`. The physical case is `SU(N) × U(1)`: confined centre flux, massless
  photon. So no clause built from twisted ratios alone implies `NoCasimirAt`, and no clause on the zero-flux
  sector alone does either (the `Z₂` reading has a vanishing zero-flux defect and a Casimir term).

## 4. The constant-mode test (proved, abstract)

`logVolumeReading f a c w = 16^w f + a · log 16^w + c`: a bulk term, a term `a log(volume)` and a constant.
A compact flat direction of the action (a toron valley) adds `+ (1/2) log volume` per flat dimension relative to
its Gaussian count; a Gaussian constant mode adds `− (1/2) log volume`; a quartic constant mode adds
`− (1/4) log volume` (argued: `∫ e^{−V t²} dt ∝ V^{−1/2}`, `∫ e^{−V t⁴} dt ∝ V^{−1/4}`).

* `residue_logVolume`: the residue is `a w log 16 + c`.
* `defect_logVolume`: the dyadic defect is `15 a w log 16 − a log 16 + 15 c`.
* `not_vanishing_logVolume`: for `a ≠ 0` the defect does not vanish.

(argued) So a quartic instead of a quadratic constant-mode action (the non-abelian commutator term,
`ToronDecrement`) changes the coefficient `a`, not whether a finite-size term is present. That mechanism shapes
the crossover at `L ≪ ξ`; it cannot decide `NoCasimirAt` at fixed `β`, which is a statement about `L → ∞`, and
it does not separate `Z₂` (no constant modes, deconfined, Casimir `log 2³`).

DERIVED (module-wide): `16 = 2⁴` the copies and the volume ratio; `15 = 16 − 1`; `2` the doubling, the dyadic
side and the least rank; `N³ = |Z_N³|`; `1 − N⁻³` the share of `N³ − 1` degenerate flux sectors; `0` the limits
and signs; `1` the least window index and the step; `4` the corner steps. Proof-internal chosen constants (none
appears in a public statement): the linearization condition `(4 + N⁶) δ ≤ 2` of
`CentreSectorSeedN.sectors_of_defectWN` and the factors `1/2`, `2` of its bounds `N³ δ/2`, `2 δ`, which fix the
explicit `κ = 2/(4 + N⁶)`; the sector threshold `1/80000` and the seed `1/1000` (from `CentreSectorSeedN` and
`CouplingTower.tendsto_zero_of_seed`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FluxSplitCasimir

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd windowCoupling_nonneg)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)
open MassGap.LineSeedsBasin (TensionBelow)
open MassGap.LineSeedsVanishing (ZeroFluxVanishing)
open MassGap.CasimirStep (NoCasimirAt dyadicDefect residue logZ)

/-! ## 1. Lower bounds on the real torus -/

section Wilson

variable {N : ℕ} [NeZero N]

/-- DERIVED: `3` the power `|Z_N³| = N³`. -/
private theorem cube_pos : (0 : ℝ) < (N : ℝ) ^ 3 := by
  have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  positivity

/-- The explicit form of `windowCoupling_ge`. Proof-internal chosen constants: `4 + N⁶` and `2` the
linearization condition `(4 + N⁶) δ ≤ 2` of `sectors_of_defectWN`, `2` the factor of its bounds `N³ δ/2`, `2 δ`.
DERIVED: `0` the sign of `β`; `1` the least window index; `2` the dyadic side; `3` the power `|Z_N³| = N³`;
`4` the corner steps; `6` the power of `N` in the condition. -/
private theorem windowCoupling_ge_aux {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) :
    min (2 * fluxShareN N β (2 ^ w) i / (N : ℝ) ^ 3) (2 / (4 + (N : ℝ) ^ 6)) ≤ windowCoupling N β w ∧
      min (trivialDefectN N β (2 ^ w) i / 2) (2 / (4 + (N : ℝ) ^ 6)) ≤ windowCoupling N β w := by
  have hN := NeZero.ne N
  have hg0 : 0 ≤ windowCoupling N β w := windowCoupling_nonneg hN hβ hw
  have hM := cube_pos (N := N)
  have hP : (0 : ℝ) < 4 + (N : ℝ) ^ 6 := by positivity
  by_cases h : (4 + (N : ℝ) ^ 6) * windowCoupling N β w ≤ 2
  · obtain ⟨hf, ht⟩ := CentreSectorSeedN.sectors_of_defectWN hβ (DeltaLengthTower.two_le_two_pow hw)
      (DeltaLengthTower.even_two_pow hw) hg0 h le_rfl i
    refine ⟨(min_le_left _ _).trans ?_, (min_le_left _ _).trans (by linarith)⟩
    rw [div_le_iff₀ hM]
    linarith
  · push Not at h
    have h2 : 2 / (4 + (N : ℝ) ^ 6) ≤ windowCoupling N β w := by
      rw [div_le_iff₀ hP]; linarith
    exact ⟨(min_le_right _ _).trans h2, (min_le_right _ _).trans h2⟩

/-- **Each sector bounds the window coupling from below**: some `κ > 0` gives `min(κ s/N³, κ) ≤ g` for the flux
share `s` and `min(κ t, κ) ≤ g` for the zero-flux defect `t`. DERIVED: `0` the signs; `1` the least window
index; `2` the dyadic side; `3` the power `|Z_N³| = N³`; `4` the corner steps. Proof-internal: the explicit
`κ = 2/(4 + N⁶)` of `windowCoupling_ge_aux` (chosen). -/
theorem windowCoupling_ge : ∃ κ : ℝ, 0 < κ ∧ ∀ {β : ℝ}, 0 ≤ β → ∀ {w : ℕ}, 1 ≤ w → ∀ i : Fin 4,
    min (κ * fluxShareN N β (2 ^ w) i / (N : ℝ) ^ 3) κ ≤ windowCoupling N β w ∧
      min (κ * trivialDefectN N β (2 ^ w) i) κ ≤ windowCoupling N β w := by
  have hM := cube_pos (N := N)
  have hP : (0 : ℝ) < 4 + (N : ℝ) ^ 6 := by positivity
  have h6 : (0 : ℝ) ≤ (N : ℝ) ^ 6 := by positivity
  have hκ0 : (0 : ℝ) < 2 / (4 + (N : ℝ) ^ 6) := by positivity
  have hκ2 : 2 / (4 + (N : ℝ) ^ 6) ≤ 1 / 2 := by
    rw [div_le_iff₀ hP]
    linarith
  refine ⟨2 / (4 + (N : ℝ) ^ 6), hκ0, fun {β} hβ {w} hw i => ?_⟩
  obtain ⟨h1, h2⟩ := windowCoupling_ge_aux (N := N) hβ hw i
  have hg0 : 0 ≤ windowCoupling N β w := windowCoupling_nonneg (NeZero.ne N) hβ hw
  constructor
  · rcases le_total 0 (fluxShareN N β (2 ^ w) i) with hs | hs
    · refine le_trans (min_le_min ?_ le_rfl) h1
      exact div_le_div_of_nonneg_right (by nlinarith) hM.le
    · refine (min_le_left _ _).trans (le_trans ?_ hg0)
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hM.le
  · rcases le_total 0 (trivialDefectN N β (2 ^ w) i) with ht | ht
    · refine le_trans (min_le_min ?_ le_rfl) h2
      nlinarith
    · refine (min_le_left _ _).trans (le_trans ?_ hg0)
      nlinarith

/-- **A window coupling bounded below on infinitely many windows bounds the Casimir coefficient.**
DERIVED: `15 = 16 − 1`. -/
theorem casimir_ge_of_frequently {β m : ℝ} (hfreq : ∃ᶠ w in atTop, m ≤ windowCoupling N β w) {f c : ℝ}
    (h : Tendsto (residue (logZ N β) f) atTop (𝓝 c)) : m ≤ 15 * c := by
  have ht := CasimirStep.tendsto_defect_of_residue _ h
  have e : windowCoupling N β = dyadicDefect (logZ N β) := funext (CasimirStep.windowCoupling_eq N β)
  rw [← e] at ht
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw1, hw2⟩ := (hfreq.and_eventually (ht.eventually (gt_mem_nhds hlt))).exists
  linarith

/-- **Deconfined flux bounds the Casimir coefficient from below**: some `κ > 0` gives
`min(κ s/N³, κ) ≤ 15 c`. DERIVED: `0` the signs; `2` the dyadic side; `3` the power `|Z_N³| = N³`; `4` the
corner steps; `15 = 16 − 1`. Proof-internal: `κ` and `1` the least window index, as in `windowCoupling_ge`. -/
theorem casimir_ge_of_flux : ∃ κ : ℝ, 0 < κ ∧ ∀ {β : ℝ}, 0 ≤ β → ∀ {s : ℝ} (i : Fin 4),
    (∃ᶠ w in atTop, s ≤ fluxShareN N β (2 ^ w) i) → ∀ {f c : ℝ},
    Tendsto (residue (logZ N β) f) atTop (𝓝 c) → min (κ * s / (N : ℝ) ^ 3) κ ≤ 15 * c := by
  obtain ⟨κ, hκ, hg⟩ := windowCoupling_ge (N := N)
  refine ⟨κ, hκ, fun {β} hβ {s} i hfreq {f c} h => casimir_ge_of_frequently ?_ h⟩
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun w ⟨hs, hw⟩ => ?_
  refine le_trans (min_le_min ?_ le_rfl) (hg hβ hw i).1
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hκ.le) (cube_pos (N := N)).le

/-- **A neutral excess bounds the Casimir coefficient from below**: some `κ > 0` gives `min(κ t, κ) ≤ 15 c`.
DERIVED: `0` the signs; `2` the dyadic side; `4` the corner steps; `15 = 16 − 1`. Proof-internal: `κ` and `1`
the least window index, as in `windowCoupling_ge`. -/
theorem casimir_ge_of_zeroFlux : ∃ κ : ℝ, 0 < κ ∧ ∀ {β : ℝ}, 0 ≤ β → ∀ {t : ℝ} (i : Fin 4),
    (∃ᶠ w in atTop, t ≤ trivialDefectN N β (2 ^ w) i) → ∀ {f c : ℝ},
    Tendsto (residue (logZ N β) f) atTop (𝓝 c) → min (κ * t) κ ≤ 15 * c := by
  obtain ⟨κ, hκ, hg⟩ := windowCoupling_ge (N := N)
  refine ⟨κ, hκ, fun {β} hβ {t} i hfreq {f c} h => casimir_ge_of_frequently ?_ h⟩
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun w ⟨ht, hw⟩ => ?_
  exact le_trans (min_le_min (mul_le_mul_of_nonneg_left ht hκ.le) le_rfl) (hg hβ hw i).2

/-- **A positive flux share on infinitely many windows excludes `NoCasimirAt`.** DERIVED: `0` the signs; `2` the
dyadic side; `4` the corner steps. Proof-internal: `κ` as in `casimir_ge_of_flux`. -/
theorem not_noCasimirAt_of_flux {β : ℝ} (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (i : Fin 4)
    (hfreq : ∃ᶠ w in atTop, s ≤ fluxShareN N β (2 ^ w) i) : ¬ NoCasimirAt N β := by
  rintro ⟨f, hf⟩
  obtain ⟨κ, hκ, hc⟩ := casimir_ge_of_flux (N := N)
  have h := hc hβ i hfreq hf
  have hpos : 0 < min (κ * s / (N : ℝ) ^ 3) κ := lt_min (div_pos (mul_pos hκ hs) cube_pos) hκ
  linarith

/-- **A positive zero-flux defect on infinitely many windows excludes `NoCasimirAt`.** DERIVED: `0` the signs;
`2` the dyadic side; `4` the corner steps. Proof-internal: `κ` as in `casimir_ge_of_zeroFlux`. -/
theorem not_noCasimirAt_of_zeroFlux {β : ℝ} (hβ : 0 ≤ β) {t : ℝ} (ht : 0 < t) (i : Fin 4)
    (hfreq : ∃ᶠ w in atTop, t ≤ trivialDefectN N β (2 ^ w) i) : ¬ NoCasimirAt N β := by
  rintro ⟨f, hf⟩
  obtain ⟨κ, hκ, hc⟩ := casimir_ge_of_zeroFlux (N := N)
  have h := hc hβ i hfreq hf
  have hpos : 0 < min (κ * t) κ := lt_min (mul_pos hκ ht) hκ
  linarith

/-- **Degenerate flux sectors give a Casimir term**: at `N ≥ 2`, a flux share at least `1 − N⁻³` (the share of
`N³ − 1` flux sectors degenerate with the vacuum) on infinitely many windows excludes `NoCasimirAt`.
DERIVED: `2` the least rank and the dyadic side; `3` the power `|Z_N³| = N³`; `1 − N⁻³` the degenerate share;
`0` the sign of `β`; `4` the corner steps. -/
theorem not_noCasimirAt_of_degenerate (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4)
    (hfreq : ∃ᶠ w in atTop, 1 - ((N : ℝ) ^ 3)⁻¹ ≤ fluxShareN N β (2 ^ w) i) : ¬ NoCasimirAt N β := by
  have h8 : (8 : ℝ) ≤ (N : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have hs : 0 < 1 - ((N : ℝ) ^ 3)⁻¹ := by
    have : ((N : ℝ) ^ 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  exact not_noCasimirAt_of_flux hβ hs i hfreq

/-! ## 2. The exact split -/

variable (N) in
/-- **Confined flux at `β`**: at every step the flux share of the window `2^w` is eventually below every
positive value. DERIVED: `0` the sign of `ε`; `2` the dyadic side; `4` the steps. -/
def FluxConfinedAt (β : ℝ) : Prop :=
  ∀ i : Fin 4, ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, fluxShareN N β (2 ^ w) i ≤ ε

variable (N) in
/-- **The neutral sector is held by the flux at `β`**: at every step, for every `ε > 0` some `δ > 0` makes,
eventually in `w`, a flux share at most `δ` force a zero-flux defect at most `ε`. DERIVED: `0` the signs of `ε`,
`δ`; `2` the dyadic side; `4` the steps. -/
def NeutralBindingAt (β : ℝ) : Prop :=
  ∀ i : Fin 4, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ w in atTop, fluxShareN N β (2 ^ w) i ≤ δ → trivialDefectN N β (2 ^ w) i ≤ ε

/-- **No Casimir term forces both sectors to vanish.** DERIVED: `0` the sign of `β`. Proof-internal: `κ` as in
`windowCoupling_ge`; `1` the least window index; `2` the dyadic side; `3` the power of `N`; `4` the steps. -/
theorem sectors_of_noCasimirAt {β : ℝ} (hβ : 0 ≤ β) (h : NoCasimirAt N β) :
    FluxConfinedAt N β ∧ ZeroFluxVanishing N β := by
  have hv := (CasimirStep.vanishing_iff_noCasimirAt N β).mpr h
  have hM := cube_pos (N := N)
  obtain ⟨κ, hκ, hgκ⟩ := windowCoupling_ge (N := N)
  have key : ∀ (i : Fin 4) (ε : ℝ), 0 < ε → ∀ᶠ w in atTop,
      fluxShareN N β (2 ^ w) i ≤ ε ∧ trivialDefectN N β (2 ^ w) i ≤ ε := by
    intro i ε hε
    have hm : 0 < min (min (κ * ε / (N : ℝ) ^ 3) (κ * ε)) κ :=
      lt_min (lt_min (div_pos (mul_pos hκ hε) hM) (mul_pos hκ hε)) hκ
    filter_upwards [hv.eventually (gt_mem_nhds hm), eventually_ge_atTop 1] with w hg hw
    obtain ⟨h1, h2⟩ := hgκ hβ hw i
    constructor
    · by_contra hc
      push Not at hc
      have hle : min (min (κ * ε / (N : ℝ) ^ 3) (κ * ε)) κ
          ≤ min (κ * fluxShareN N β (2 ^ w) i / (N : ℝ) ^ 3) κ :=
        min_le_min ((min_le_left _ _).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc.le hκ.le) hM.le)) le_rfl
      linarith
    · by_contra hc
      push Not at hc
      have hle : min (min (κ * ε / (N : ℝ) ^ 3) (κ * ε)) κ
          ≤ min (κ * trivialDefectN N β (2 ^ w) i) κ :=
        min_le_min ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left hc.le hκ.le)) le_rfl
      linarith
  exact ⟨fun i ε hε => (key i ε hε).mono fun _ h => h.1,
    fun i ε hε => (key i ε hε).mono fun _ h => h.2⟩

/-- **Both sectors vanishing gives no Casimir term.** DERIVED: `0` the sign of `β`. Proof-internal: the sector
threshold `1/80000` and the seed `1/1000`; `2` the least window with a hop and the dyadic side; `4` the steps. -/
theorem noCasimirAt_of_sectors {β : ℝ} (hβ : 0 ≤ β) (hF : FluxConfinedAt N β)
    (hZ : ZeroFluxVanishing N β) : NoCasimirAt N β := by
  refine (CasimirStep.vanishing_iff_noCasimirAt N β).mp ?_
  have hε : (0 : ℝ) < 1 / 80000 := by norm_num
  have hall : ∀ᶠ w in atTop, 2 ≤ w ∧ ∀ i : Fin 4,
      fluxShareN N β (2 ^ w) i ≤ 1 / 80000 ∧ trivialDefectN N β (2 ^ w) i ≤ 1 / 80000 := by
    filter_upwards [eventually_ge_atTop 2, hF 0 _ hε, hF 1 _ hε, hF 2 _ hε, hF 3 _ hε,
      hZ 0 _ hε, hZ 1 _ hε, hZ 2 _ hε, hZ 3 _ hε] with w hw f0 f1 f2 f3 z0 z1 z2 z3
    refine ⟨hw, fun i => ?_⟩
    fin_cases i
    exacts [⟨f0, z0⟩, ⟨f1, z1⟩, ⟨f2, z2⟩, ⟨f3, z3⟩]
  obtain ⟨w, hw, hs⟩ := hall.exists
  have hn : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow (by omega : 1 ≤ w)
  have he : Even (2 ^ w) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hd : windowCoupling N β w ≤ 1 / 1000 := CentreSectorSeedN.defectW_le_of_sectorsN hβ hn he hs
  exact CouplingTower.tendsto_zero_of_seed (NeZero.ne N) hβ (by omega) hd

/-- **The Casimir term splits exactly into the flux sectors and the zero-flux sector.** DERIVED: `0` the sign of
`β`. -/
theorem noCasimirAt_iff_sectors {β : ℝ} (hβ : 0 ≤ β) :
    NoCasimirAt N β ↔ FluxConfinedAt N β ∧ ZeroFluxVanishing N β :=
  ⟨sectors_of_noCasimirAt hβ, fun h => noCasimirAt_of_sectors hβ h.1 h.2⟩

/-- **Confinement and binding give a vanishing zero-flux defect.** No numerals in the statement. -/
theorem zeroFluxVanishing_of_binding {β : ℝ} (hF : FluxConfinedAt N β) (hB : NeutralBindingAt N β) :
    ZeroFluxVanishing N β := by
  intro i ε hε
  obtain ⟨δ, hδ, hev⟩ := hB i ε hε
  filter_upwards [hev, hF i δ hδ] with w h1 h2
  exact h1 h2

/-- **A vanishing zero-flux defect is bound by the flux** (with `δ = 1`). No numerals in the statement.
Proof-internal: `1` the witness `δ`. -/
theorem binding_of_zeroFluxVanishing {β : ℝ} (hZ : ZeroFluxVanishing N β) : NeutralBindingAt N β :=
  fun i ε hε => ⟨1, one_pos, (hZ i ε hε).mono fun _ h _ => h⟩

/-- **No Casimir term is confinement plus binding.** DERIVED: `0` the sign of `β`. -/
theorem noCasimirAt_iff_binding {β : ℝ} (hβ : 0 ≤ β) :
    NoCasimirAt N β ↔ FluxConfinedAt N β ∧ NeutralBindingAt N β := by
  rw [noCasimirAt_iff_sectors hβ]
  exact ⟨fun h => ⟨h.1, binding_of_zeroFluxVanishing h.2⟩,
    fun h => ⟨h.1, zeroFluxVanishing_of_binding h.1 h.2⟩⟩

/-- **A positive measured tension confines the flux.** DERIVED: `0` the signs. -/
theorem fluxConfinedAt_of_tension {A : ℝ → ℝ} (hT : TensionBelow N A) {β : ℝ} (hβ : 0 ≤ β)
    (hA : 0 < A β) : FluxConfinedAt N β :=
  fun i _ hε => LineSeedsVanishing.fluxShare_eventually_le hT hβ hA i hε

/-- **Tension and binding give no Casimir term.** DERIVED: `0` the signs. -/
theorem noCasimirAt_of_tension_binding {A : ℝ → ℝ} (hT : TensionBelow N A) {β : ℝ} (hβ : 0 ≤ β)
    (hA : 0 < A β) (hB : NeutralBindingAt N β) : NoCasimirAt N β :=
  (noCasimirAt_iff_binding hβ).mpr ⟨fluxConfinedAt_of_tension hT hβ hA, hB⟩

/-- **Tension and binding give the periodic Clay gap at `β`.** DERIVED: `2` the least rank; `0` the plane, the
time axis and the signs; `1` the upper end of the rate interval. -/
theorem windowGap_of_tension_binding (hN2 : 2 ≤ N) {A : ℝ → ℝ} (hT : TensionBelow N A) {β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 < A β) (hB : NeutralBindingAt N β) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 (NeZero.ne N) β r :=
  CasimirStep.windowGap_of_noCasimirAt hN2 (NeZero.ne N) hβ (noCasimirAt_of_tension_binding hT hβ hA hB)

/-- **Tension and binding at arbitrarily large `β` give the strong end.** DERIVED: `0` the signs. -/
theorem strongEnd_of_tension_binding {A : ℝ → ℝ} (hT : TensionBelow N A)
    (h : ∃ᶠ β in atTop, 0 < A β ∧ NeutralBindingAt N β) : StrongEnd N := by
  refine (CasimirStep.strongEnd_iff_frequently_noCasimir (NeZero.ne N)).mpr ?_
  refine (h.and_eventually (eventually_ge_atTop 0)).mono ?_
  rintro β ⟨⟨hA, hB⟩, hβ⟩
  exact noCasimirAt_of_tension_binding hT hβ hA hB

end Wilson

/-! ## 4. The constant-mode test -/

/-- **A reading with a log-volume term**: bulk `16^w f`, `a log(16^w)`, constant `c`. DERIVED: `16 = 2⁴` the
volume ratio. -/
def logVolumeReading (f a c : ℝ) (w : ℕ) : ℝ := 16 ^ w * f + a * (w * Real.log 16) + c

/-- DERIVED: `16 = 2⁴`. -/
theorem residue_logVolume (f a c : ℝ) (w : ℕ) :
    residue (logVolumeReading f a c) f w = a * (w * Real.log 16) + c := by
  rw [CasimirStep.residue_eq]
  unfold logVolumeReading
  ring

/-- DERIVED: `16 = 2⁴`; `15 = 16 − 1`. -/
theorem defect_logVolume (f a c : ℝ) (w : ℕ) :
    dyadicDefect (logVolumeReading f a c) w = 15 * a * (w * Real.log 16) - a * Real.log 16 + 15 * c := by
  unfold dyadicDefect logVolumeReading
  push_cast
  ring

/-- **A log-volume term of either sign blocks the vanishing**: Gaussian, flat or quartic constant modes change
`a`, not the presence of a finite-size term. DERIVED: `0` the limit and the excluded coefficient.
Proof-internal: `15`, `16` as in `defect_logVolume`; `1` the step. -/
theorem not_vanishing_logVolume {f a c : ℝ} (ha : a ≠ 0) :
    ¬ Tendsto (dyadicDefect (logVolumeReading f a c)) atTop (𝓝 0) := by
  intro h
  have h1 := (h.comp (tendsto_add_atTop_nat 1)).sub h
  rw [sub_zero] at h1
  have hc : ∀ w : ℕ, (dyadicDefect (logVolumeReading f a c) ∘ fun n => n + 1) w
      - dyadicDefect (logVolumeReading f a c) w = 15 * a * Real.log 16 := by
    intro w
    simp only [Function.comp, defect_logVolume]
    push_cast
    ring
  have h2 : Tendsto (fun _ : ℕ => 15 * a * Real.log 16) atTop (𝓝 0) := h1.congr hc
  have h3 : 15 * a * Real.log 16 = 0 := tendsto_nhds_unique tendsto_const_nhds h2
  have hl : (15 : ℝ) * Real.log 16 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 16)
    positivity
  rw [show 15 * a * Real.log 16 = a * (15 * Real.log 16) by ring] at h3
  exact ha ((mul_eq_zero.mp h3).resolve_right hl)

end MassGap.FluxSplitCasimir

#print axioms MassGap.FluxSplitCasimir.windowCoupling_ge
#print axioms MassGap.FluxSplitCasimir.casimir_ge_of_frequently
#print axioms MassGap.FluxSplitCasimir.casimir_ge_of_flux
#print axioms MassGap.FluxSplitCasimir.casimir_ge_of_zeroFlux
#print axioms MassGap.FluxSplitCasimir.not_noCasimirAt_of_flux
#print axioms MassGap.FluxSplitCasimir.not_noCasimirAt_of_zeroFlux
#print axioms MassGap.FluxSplitCasimir.not_noCasimirAt_of_degenerate
#print axioms MassGap.FluxSplitCasimir.sectors_of_noCasimirAt
#print axioms MassGap.FluxSplitCasimir.noCasimirAt_of_sectors
#print axioms MassGap.FluxSplitCasimir.noCasimirAt_iff_sectors
#print axioms MassGap.FluxSplitCasimir.zeroFluxVanishing_of_binding
#print axioms MassGap.FluxSplitCasimir.binding_of_zeroFluxVanishing
#print axioms MassGap.FluxSplitCasimir.noCasimirAt_iff_binding
#print axioms MassGap.FluxSplitCasimir.fluxConfinedAt_of_tension
#print axioms MassGap.FluxSplitCasimir.noCasimirAt_of_tension_binding
#print axioms MassGap.FluxSplitCasimir.windowGap_of_tension_binding
#print axioms MassGap.FluxSplitCasimir.strongEnd_of_tension_binding
#print axioms MassGap.FluxSplitCasimir.residue_logVolume
#print axioms MassGap.FluxSplitCasimir.defect_logVolume
#print axioms MassGap.FluxSplitCasimir.not_vanishing_logVolume
