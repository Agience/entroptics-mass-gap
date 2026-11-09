import Mathlib
import MassGap.FluxSplitCasimir
import MassGap.ZoomContract

/-!
# MassGap.FlatCap — compactness caps the flat (twisted-sector) share of the doubling defect

The doubling defect `D(β, w) = windowCoupling N β w` is, along the corner path, `8p₀ + 4p₁ + 2p₂ + p₃`
(`CentreSectorSeedN.defectW_eqN`), each `pᵢ = dd(K)` the doubling defect `2 log hs(K) − log hs(K ∗ K)` of the
half-time transfer `K = halfKN` on the slice of step `i`. Every slice carries the centre action of `Z_N³`
(the electric-flux / twisted sectors of the slice), and `Kₜ = trivKN` is the zero-flux sector of `K`. This
module splits each step, and so `D`, exactly into the zero-flux part and the flat (flux) part, and caps the
flat part by the sector count.

## 1. The exact split (proved)

* `fluxLog = log hs(K) − log hs(Kₜ)` and `fluxLogDoubled = log hs(K ∗ K) − log hs(Kₜ ∗ Kₜ)`: the log inverse
  share of the zero-flux sector at time extents `n` and `2n`. `fluxLog_eq`: `fluxLog = −log(1 − fluxShareN)`;
  by `CentreSectorSeedN.fluxShareN_eq_mean` the share is one minus the mean twisted ratio `N⁻³ Σ_g Z_g/Z`.
* `flatStep = 2 fluxLog − fluxLogDoubled`, `dd_split`: `dd(K) = trivialDefectN + flatStep`, an identity.
* `windowCoupling_split`: for `w ≥ 1`, `D = restW + flatW`, with `restW = Σ cᵢ trivialDefectN` and
  `flatW = Σ cᵢ flatStep`, `(c₀, c₁, c₂, c₃) = (8, 4, 2, 1)`.

## 2. The compactness cap (proved)

The zero-flux sector carries at least `N⁻³ = 1/|Z_N³|` of the trace at both time extents
(`hs_trivKN_ge`, and `fluxLogDoubled_le` through `zk(K ∗ K) = Kₜ ∗ Kₜ`). So
`0 ≤ fluxLog, fluxLogDoubled ≤ log N³ = 3 log N` (`fluxLog_le`, `fluxLogDoubled_le`), and
`−3 log N ≤ flatStep ≤ 6 log N`, hence (`flat_cap`)

  `−45 log N ≤ flatW N β w ≤ 90 log N`   for every `β ≥ 0`, every `w`,

independent of `w` and `β`: compactness of SU(N) enters only through the finite centre `Z_N³` of the slice.
`restW_nonneg`: the zero-flux part is `≥ 0`. At `N = 1` (no centre, no twisted sector) `flatW = 0` exactly
and `D = restW` (`flatW_eq_zero_one`, `windowCoupling_eq_rest_one`).

## 3. The cap does not vanish by itself (proved, plainly)

* The cap does not remove the flat share: a capped flat share that does not tend to `0` keeps `D` away from
  `0`, and doubling multiplies a constant share by `15`. Two conditions remain, both open: (i) contraction of
  `restW`, and (ii) `FluxConfinedAt N β`, at every `β ≥ 0`. This module does not use `ToronDecrement`; that
  route is argued only there.

* `fifteen_constant`: a `w`-independent constant `c` in `log Z` enters `D = 16 x_w − x_{w+1}` with weight
  `16 − 1 = 15` (`CasimirStep.dyadicDefect` of `16^w f + c` is `15 c`). Doubling does not remove a constant
  flat share; it multiplies it by `15`. So a capped, non-vanishing flat share blocks `D → 0`, plainly; this is
  `FluxSplitCasimir.not_noCasimirAt_of_flux` on the torus itself.
* `vanishes_iff_split`: `Vanishes N β ↔ restW → 0 ∧ flatW → 0` at `β ≥ 0`. With
  `FluxSplitCasimir.noCasimirAt_iff_sectors`, `flatW → 0` is carried by `FluxConfinedAt N β` (every twisted
  ratio's mean `→ 1` along the windows), which is not proved at general `β` in the tree
  (`FluxSplitCasimir.fluxConfinedAt_of_tension` reduces it to a positive measured tension).
* `vanishes_of_rest_contraction`: if `restW` contracts by a fixed fraction `η ≤ 1 − δ` eventually and
  `FluxConfinedAt N β`, then `Vanishes N β` (the template `ZoomContract.tendsto_zero_of_contraction` for the
  rest; for the flat part, `0 ≤ D ≤ restW + 2 Σ cᵢ fluxLog` and `fluxLog ≤ 2 · share` at share `≤ 1/2`).
  Plainly, the contraction of `restW` with the cap alone gives only `D ≤ restW + 90 log N`, not `D → 0`.

## 4. Load tests (proved)

* `N = 1`: no flat sector; the split is `D = restW` and the contraction is the contraction of `D`.
* The anchor, which contains `β = 0` (all sectors equal in weight: Haar product measure):
  `anchor_split_vanishes`: on `[0, β₀)` both `restW → 0` and `flatW → 0`. Plainly, that the twisted ratios
  equal `1` exactly at `β = 0` is not proved here; only their limit along the windows is. The anchor conclusion is
  inherited from `ZoomContract.anchor_by_contraction`; it is not a flux-confinement proof.
* The free chain of `ZoomContract` §5 has no centre action: its contraction is the whole read
  (`ZoomContract.freeMassive_vanishes_by_contraction`); there is nothing to split.

DERIVED (module-wide): `8, 4, 2, 1` the corner-path weights of `DoublingRecursion.Δ`, summing to `15`;
`15 = 16 − 1` the copies minus the doubled torus; `3` the exponent of `|Z_N³| = N³` (`SliceCentreAction.card_cen`);
`2` the square in `dd` and in `hs`, and the dyadic side; `6 = 2 · 3`; `45 = 15 · 3`, `90 = 15 · 6`; `1/2` the
share at which `1 − s ≥ 1/2`, so `(A − B)/B ≤ 2 (A − B)/A`; `1` the least window; `0` signs and limits.
Proof-internal: `1/4` the share threshold `min(ε/4, 1/4)` (so `2 · share ≤ ε/2 < ε` and `share ≤ 1/2`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FlatCap

open Filter Topology MeasureTheory
open MassGap.KernelPower MassGap.SectorDefect MassGap.ZeroFluxSector
open MassGap.CouplingTower (windowCoupling windowCoupling_nonneg)
open MassGap.CentreSectorSeedN (hSN halfKN trivKN fluxShareN trivialDefectN)
open MassGap.LineSeedsVanishing (ZeroFluxVanishing)
open MassGap.FluxSplitCasimir (FluxConfinedAt)
open MassGap.SliceCentreAction (act centreAction card_cen)

variable {N : ℕ} [NeZero N]

/-! ## 1. The exact split -/

variable (N) in
/-- **The flux log** at time extent `n`: `log hs(K) − log hs(Kₜ)`. DERIVED: no numeral. -/
def fluxLog (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  Real.log (hs (hSN N n i) (halfKN N β n i)) - Real.log (hs (hSN N n i) (trivKN N β n i))

variable (N) in
/-- **The flux log at the doubled time extent**: `log hs(K ∗ K) − log hs(Kₜ ∗ Kₜ)`. DERIVED: no numeral. -/
def fluxLogDoubled (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  Real.log (hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i)))
    - Real.log (hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i)))

variable (N) in
/-- **The flat share of one step**: `2 fluxLog − fluxLogDoubled`. DERIVED: `2` the square in `dd`. -/
def flatStep (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ := 2 * fluxLog N β n i - fluxLogDoubled N β n i

/-- **One step splits exactly**: `dd(K) = trivialDefectN + flatStep`. DERIVED: no numeral. -/
theorem dd_split (β : ℝ) (n : ℕ) (i : Fin 4) :
    dd (hSN N n i) (halfKN N β n i) = trivialDefectN N β n i + flatStep N β n i := by
  unfold flatStep fluxLog fluxLogDoubled trivialDefectN dd
  ring

variable (N) in
/-- The zero-flux part of `D` at window `w`. DERIVED: `8, 4, 2, 1` the corner weights; `2` the side. -/
def restW (β : ℝ) (w : ℕ) : ℝ :=
  8 * trivialDefectN N β (2 ^ w) 0 + 4 * trivialDefectN N β (2 ^ w) 1
    + 2 * trivialDefectN N β (2 ^ w) 2 + trivialDefectN N β (2 ^ w) 3

variable (N) in
/-- The flat part of `D` at window `w`. DERIVED: `8, 4, 2, 1` the corner weights; `2` the side. -/
def flatW (β : ℝ) (w : ℕ) : ℝ :=
  8 * flatStep N β (2 ^ w) 0 + 4 * flatStep N β (2 ^ w) 1 + 2 * flatStep N β (2 ^ w) 2
    + flatStep N β (2 ^ w) 3

variable (N) in
/-- The flux-log part at window `w` (the upper envelope of the flat part). DERIVED: as `flatW`. -/
def fluxW (β : ℝ) (w : ℕ) : ℝ :=
  8 * fluxLog N β (2 ^ w) 0 + 4 * fluxLog N β (2 ^ w) 1 + 2 * fluxLog N β (2 ^ w) 2
    + fluxLog N β (2 ^ w) 3

/-- **`D = restW + flatW`** for `w ≥ 1`, `β ≥ 0`. DERIVED: `1` the least window. -/
theorem windowCoupling_split {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    windowCoupling N β w = restW N β w + flatW N β w := by
  unfold windowCoupling restW flatW
  rw [CentreSectorSeedN.defectW_eqN hβ (DeltaLengthTower.two_le_two_pow hw)
    (DeltaLengthTower.even_two_pow hw), dd_split, dd_split, dd_split, dd_split]
  ring

/-! ## 2. The compactness cap -/

private theorem Npos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))

/-- The log of `A / N³`. DERIVED: `3` the exponent of `|Z_N³|`. -/
private theorem log_div_cube {A : ℝ} (hA : 0 < A) :
    Real.log (A / (N : ℝ) ^ 3) = Real.log A - 3 * Real.log N := by
  rw [Real.log_div hA.ne' (pow_pos (Npos (N := N)) 3).ne', Real.log_pow]
  push_cast; ring

section Cap

variable {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
include hβ

/-- `fluxLog ≥ 0`. DERIVED: `0` the sign. -/
theorem fluxLog_nonneg : 0 ≤ fluxLog N β n i :=
  sub_nonneg.mpr (Real.log_le_log (CentreSectorSeedN.hs_trivKN_pos hβ n i)
    (CentreSectorSeedN.hs_trivKN_le hβ n i))

/-- **The cap at time extent `n`**: `fluxLog ≤ log N³`. DERIVED: `3` the exponent of `|Z_N³|`. -/
theorem fluxLog_le : fluxLog N β n i ≤ 3 * Real.log N := by
  have hA := CentreSectorSeedN.hs_halfKN_pos (N := N) hβ n i
  have h := Real.log_le_log (div_pos hA (pow_pos (Npos (N := N)) 3))
    (CentreSectorSeedN.hs_trivKN_ge (N := N) hβ n i)
  rw [log_div_cube hA] at h
  unfold fluxLog; linarith

/-- **The flux log is minus the log of the zero-flux share**: `fluxLog = −log(1 − fluxShareN)`.
DERIVED: `1` the total share. -/
theorem fluxLog_eq : fluxLog N β n i = -Real.log (1 - fluxShareN N β n i) := by
  have hA := CentreSectorSeedN.hs_halfKN_pos (N := N) hβ n i
  have hB := CentreSectorSeedN.hs_trivKN_pos (N := N) hβ n i
  have e : 1 - fluxShareN N β n i
      = hs (hSN N n i) (trivKN N β n i) / hs (hSN N n i) (halfKN N β n i) := by
    unfold fluxShareN; rw [sub_div, div_self hA.ne']; ring
  rw [e, Real.log_div hB.ne' hA.ne']
  unfold fluxLog; ring

/-- **A small flux share gives a small flux log**: share `≤ e ≤ 1/2` gives `fluxLog ≤ 2e`.
DERIVED: `1/2` the share at which `B ≥ A/2`; `2` its inverse. -/
theorem fluxLog_le_of_share {e : ℝ} (he : e ≤ 1 / 2) (hsh : fluxShareN N β n i ≤ e) :
    fluxLog N β n i ≤ 2 * e := by
  set A := hs (hSN N n i) (halfKN N β n i) with hAdef
  set B := hs (hSN N n i) (trivKN N β n i) with hBdef
  have hA : 0 < A := CentreSectorSeedN.hs_halfKN_pos hβ n i
  have hB : 0 < B := CentreSectorSeedN.hs_trivKN_pos hβ n i
  have h1 : A - B ≤ e * A := by
    have := (div_le_iff₀ hA).mp hsh
    linarith
  have h2 : Real.log A - Real.log B ≤ (A - B) / B := by
    rw [← Real.log_div hA.ne' hB.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hA hB)
    have e' : (A - B) / B = A / B - 1 := by rw [sub_div, div_self hB.ne']
    linarith
  have hAB : B ≤ A := CentreSectorSeedN.hs_trivKN_le hβ n i
  have h0 : 0 ≤ e := by nlinarith
  have hB2 : A ≤ 2 * B := by
    have := mul_le_mul_of_nonneg_right he hA.le
    linarith
  have h3 : (A - B) / B ≤ 2 * e := by
    rw [div_le_iff₀ hB]
    have := mul_le_mul_of_nonneg_left hB2 h0
    linarith
  show Real.log A - Real.log B ≤ 2 * e
  linarith

/-- `fluxLogDoubled ≥ 0`. DERIVED: `0` the sign. -/
theorem fluxLogDoubled_nonneg : 0 ≤ fluxLogDoubled N β n i :=
  sub_nonneg.mpr (Real.log_le_log (CentreSectorSeedN.hs_conv_trivKN_pos hβ n i)
    (CentreSectorSeedN.hs_conv_trivKN_le hβ n i))

/-- **The cap at the doubled time extent**: `fluxLogDoubled ≤ log N³`, through `zk(K ∗ K) = Kₜ ∗ Kₜ`.
DERIVED: `3` the exponent of `|Z_N³|`. -/
theorem fluxLogDoubled_le : fluxLogDoubled N β n i ≤ 3 * Real.log N := by
  have hK := CentreSectorSeedN.bdd_halfKN (N := N) hβ n i
  have hKK : Bdd (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i)) := hK.conv (μ := hSN N n i) hK
  have h0 : ∀ x y, 0 ≤ conv (hSN N n i) (halfKN N β n i) (halfKN N β n i) x y := fun x y =>
    integral_nonneg fun z => mul_nonneg (CentreSectorSeedN.nonneg_halfKN hβ n i _ _)
      (CentreSectorSeedN.nonneg_halfKN hβ n i _ _)
  have hge := hs_div_card_le_hs_zk hKK h0 (centreAction (μ := i) (T := CentreSectorSeed.Tr n i) (N := N))
  rw [card_cen, zk_conv hK centreAction (CentreSectorSeedN.inv_halfKN n i)] at hge
  have hC := CentreSectorSeedN.hs_conv_halfKN_pos (N := N) hβ n i
  have hge' : hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i)) / (N : ℝ) ^ 3
      ≤ hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i)) := by
    push_cast at hge; exact hge
  have h := Real.log_le_log (div_pos hC (pow_pos (Npos (N := N)) 3)) hge'
  rw [log_div_cube hC] at h
  unfold fluxLogDoubled
  linarith

/-- **The flat share of one step is capped**: `−3 log N ≤ flatStep ≤ 6 log N`.
DERIVED: `3` the exponent of `|Z_N³|`; `6 = 2 · 3`. -/
theorem flatStep_bounds : -(3 * Real.log N) ≤ flatStep N β n i ∧ flatStep N β n i ≤ 6 * Real.log N := by
  have a0 := fluxLog_nonneg (N := N) hβ n i
  have a1 := fluxLog_le (N := N) hβ n i
  have b0 := fluxLogDoubled_nonneg (N := N) hβ n i
  have b1 := fluxLogDoubled_le (N := N) hβ n i
  unfold flatStep
  constructor <;> linarith

/-- The flat share is at most twice the flux log. DERIVED: `2` the square in `dd`. -/
theorem flatStep_le_fluxLog : flatStep N β n i ≤ 2 * fluxLog N β n i := by
  have := fluxLogDoubled_nonneg (N := N) hβ n i
  unfold flatStep; linarith

/-- The zero-flux defect is `≥ 0`. DERIVED: `0` the sign. -/
theorem trivialDefectN_nonneg : 0 ≤ trivialDefectN N β n i := by
  have hadm : Adm ([] : List _) (CentreSectorSeed.floor β n i) (trivKN N β n i) :=
    ⟨CentreSectorSeedN.bdd_trivKN hβ n i,
      zk_symm centreAction (CentreSectorSeedN.symm_halfKN hβ n i) (CentreSectorSeedN.inv_halfKN n i),
      fun _ h => by simp at h, zk_low (CentreSectorSeedN.low_halfKN hβ n i)⟩
  exact CentreSectorSeed.dd_nonneg (CentreSectorSeed.floor_pos β n i) hadm

end Cap

/-- **The compactness cap**: `−45 log N ≤ flatW N β w ≤ 90 log N`, for every `β ≥ 0` and every `w`.
DERIVED: `45 = 15 · 3`, `90 = 15 · 6`, `15 = 8 + 4 + 2 + 1`. -/
theorem flat_cap {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) :
    -(45 * Real.log N) ≤ flatW N β w ∧ flatW N β w ≤ 90 * Real.log N := by
  have h0 := flatStep_bounds (N := N) hβ (2 ^ w) 0
  have h1 := flatStep_bounds (N := N) hβ (2 ^ w) 1
  have h2 := flatStep_bounds (N := N) hβ (2 ^ w) 2
  have h3 := flatStep_bounds (N := N) hβ (2 ^ w) 3
  unfold flatW
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `restW ≥ 0`. DERIVED: `0` the sign. -/
theorem restW_nonneg {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) : 0 ≤ restW N β w := by
  unfold restW
  linarith [trivialDefectN_nonneg (N := N) hβ (2 ^ w) 0, trivialDefectN_nonneg (N := N) hβ (2 ^ w) 1,
    trivialDefectN_nonneg (N := N) hβ (2 ^ w) 2, trivialDefectN_nonneg (N := N) hβ (2 ^ w) 3]

/-- `flatW ≤ 2 fluxW`. DERIVED: `2` the square in `dd`. -/
theorem flatW_le_fluxW {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) : flatW N β w ≤ 2 * fluxW N β w := by
  unfold flatW fluxW
  linarith [flatStep_le_fluxLog (N := N) hβ (2 ^ w) 0, flatStep_le_fluxLog (N := N) hβ (2 ^ w) 1,
    flatStep_le_fluxLog (N := N) hβ (2 ^ w) 2, flatStep_le_fluxLog (N := N) hβ (2 ^ w) 3]

/-- **Load test, `N = 1`**: no centre, no flat share. DERIVED: `1` the trivial group. -/
theorem flatW_eq_zero_one {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) : flatW 1 β w = 0 := by
  have h := flat_cap (N := 1) hβ w
  simp only [Nat.cast_one, Real.log_one, mul_zero, neg_zero] at h
  exact le_antisymm h.2 h.1

/-- **Load test, `N = 1`**: `D = restW`. DERIVED: `1` the trivial group and the least window. -/
theorem windowCoupling_eq_rest_one {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    windowCoupling 1 β w = restW 1 β w := by
  rw [windowCoupling_split hβ hw, flatW_eq_zero_one hβ w, add_zero]

/-! ## 3. The cap does not vanish by itself -/

/-- **A constant enters the defect fifteen-fold**: `16 x_w − x_{w+1} = 15 c` for `x_w = 16^w f + c`.
DERIVED: `16 = 2⁴` the copies; `15 = 16 − 1`. -/
theorem fifteen_constant (f c : ℝ) (w : ℕ) :
    CasimirStep.dyadicDefect (fun w => (16 : ℝ) ^ w * f + c) w = 15 * c := by
  show 16 * ((16 : ℝ) ^ w * f + c) - ((16 : ℝ) ^ (w + 1) * f + c) = 15 * c
  rw [pow_succ]; ring

/-- Each flux log tends to `0` under flux confinement. Proof-internal: the threshold `min(ε/4, 1/4)`. -/
theorem tendsto_fluxLog {β : ℝ} (hβ : 0 ≤ β) (hF : FluxConfinedAt N β) (i : Fin 4) :
    Tendsto (fun w => fluxLog N β (2 ^ w) i) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun w =>
    lt_of_lt_of_le ha (fluxLog_nonneg hβ _ i), fun a ha => ?_⟩
  have hm : 0 < min (a / 4) (1 / 4) := lt_min (by linarith) (by norm_num)
  filter_upwards [hF i _ hm] with w hw
  have := fluxLog_le_of_share hβ (2 ^ w) i ((min_le_right _ _).trans (by norm_num)) hw
  have := min_le_left (a / 4) (1 / 4)
  linarith

/-- `fluxW → 0` under flux confinement. DERIVED: the corner weights. -/
theorem tendsto_fluxW {β : ℝ} (hβ : 0 ≤ β) (hF : FluxConfinedAt N β) :
    Tendsto (fluxW N β) atTop (𝓝 0) := by
  have h := ((((tendsto_fluxLog hβ hF 0).const_mul 8).add ((tendsto_fluxLog hβ hF 1).const_mul 4)).add
    ((tendsto_fluxLog hβ hF 2).const_mul 2)).add (tendsto_fluxLog hβ hF 3)
  simp only [mul_zero, add_zero] at h
  exact h

/-- `restW → 0` when the zero-flux defect vanishes. DERIVED: the corner weights. -/
theorem tendsto_restW {β : ℝ} (hβ : 0 ≤ β) (hZ : ZeroFluxVanishing N β) :
    Tendsto (restW N β) atTop (𝓝 0) := by
  have hT : ∀ i : Fin 4, Tendsto (fun w => trivialDefectN N β (2 ^ w) i) atTop (𝓝 0) := fun i =>
    tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun w =>
      lt_of_lt_of_le ha (trivialDefectN_nonneg hβ _ i), fun a ha =>
        (hZ i (a / 2) (by linarith)).mono fun w hw => by linarith⟩
  have h := ((((hT 0).const_mul 8).add ((hT 1).const_mul 4)).add ((hT 2).const_mul 2)).add (hT 3)
  simp only [mul_zero, add_zero] at h
  exact h

/-- **The split reads the vanishing exactly**: `Vanishes N β ↔ restW → 0 ∧ flatW → 0`, at `β ≥ 0`.
DERIVED: `1` the least window; `0` the limits. -/
theorem vanishes_iff_split {β : ℝ} (hβ : 0 ≤ β) :
    StrongAnchor.Vanishes N β ↔
      Tendsto (restW N β) atTop (𝓝 0) ∧ Tendsto (flatW N β) atTop (𝓝 0) := by
  have heq : ∀ᶠ w in atTop, windowCoupling N β w = restW N β w + flatW N β w :=
    (eventually_ge_atTop 1).mono fun w hw => windowCoupling_split hβ hw
  constructor
  · intro h
    obtain ⟨_, hZ⟩ := FluxSplitCasimir.sectors_of_noCasimirAt hβ
      ((CasimirStep.vanishing_iff_noCasimirAt N β).mp h)
    have hr := tendsto_restW hβ hZ
    refine ⟨hr, ?_⟩
    have hsub := h.sub hr
    rw [sub_zero] at hsub
    refine hsub.congr' (heq.mono fun w hw => ?_)
    show windowCoupling N β w - restW N β w = flatW N β w
    rw [hw]; ring
  · rintro ⟨hr, hf⟩
    have hsum := hr.add hf
    rw [add_zero] at hsum
    exact hsum.congr' (heq.mono fun w hw => hw.symm)

/-- **Contraction of the zero-flux part, with flux confinement, gives the vanishing read.**
If `restW (w+1) ≤ η_w restW w` with `0 ≤ η_w ≤ 1 − δ`, `δ > 0`, from `w₀` on, and `FluxConfinedAt N β`, then
`Vanishes N β`. DERIVED: `1` the least window; `2` the square in `dd`; `0` signs and limits. -/
theorem vanishes_of_rest_contraction {β : ℝ} (hβ : 0 ≤ β) {η : ℕ → ℝ} (w₀ : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hη : ∀ w, w₀ ≤ w → 0 ≤ η w) (hgap : ∀ w, w₀ ≤ w → η w ≤ 1 - δ)
    (hstep : ∀ w, w₀ ≤ w → restW N β (w + 1) ≤ η w * restW N β w) (hF : FluxConfinedAt N β) :
    StrongAnchor.Vanishes N β := by
  have hr : Tendsto (restW N β) atTop (𝓝 0) :=
    ZoomContract.tendsto_zero_of_contraction w₀ (fun w _ => restW_nonneg hβ w) hη hstep
      (ZoomContract.divergence_of_gap w₀ hδ hgap)
  have hup := hr.add ((tendsto_fluxW hβ hF).const_mul 2)
  rw [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with w hw
    exact windowCoupling_nonneg (NeZero.ne N) hβ hw
  · filter_upwards [eventually_ge_atTop 1] with w hw
    rw [windowCoupling_split hβ hw]
    linarith [flatW_le_fluxW (N := N) hβ w]

/-- **Plainly, the cap alone bounds and does not vanish**: `D ≤ restW + 90 log N` for `w ≥ 1`.
DERIVED: `90 = 15 · 6`; `1` the least window. -/
theorem windowCoupling_le_rest_add_cap {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    windowCoupling N β w ≤ restW N β w + 90 * Real.log N := by
  rw [windowCoupling_split hβ hw]
  linarith [(flat_cap (N := N) hβ w).2]

/-! ## 4. Load test: the anchor (contains `β = 0`) -/

/-- **At the anchor both parts vanish**: some `β₀ > 0` has `restW → 0` and `flatW → 0` on `[0, β₀)`.
DERIVED: `0` the lower end. -/
theorem anchor_split_vanishes :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ →
      Tendsto (restW N β) atTop (𝓝 0) ∧ Tendsto (flatW N β) atTop (𝓝 0) := by
  obtain ⟨β₀, hβ₀, h⟩ := ZoomContract.anchor_by_contraction (N := N) (NeZero.ne N)
  exact ⟨β₀, hβ₀, fun β h0 hlt => (vanishes_iff_split h0).mp (h β h0 hlt)⟩

end MassGap.FlatCap

end

#print axioms MassGap.FlatCap.dd_split
#print axioms MassGap.FlatCap.windowCoupling_split
#print axioms MassGap.FlatCap.fluxLog_nonneg
#print axioms MassGap.FlatCap.fluxLog_le
#print axioms MassGap.FlatCap.fluxLog_eq
#print axioms MassGap.FlatCap.fluxLog_le_of_share
#print axioms MassGap.FlatCap.fluxLogDoubled_nonneg
#print axioms MassGap.FlatCap.fluxLogDoubled_le
#print axioms MassGap.FlatCap.flatStep_bounds
#print axioms MassGap.FlatCap.flatStep_le_fluxLog
#print axioms MassGap.FlatCap.trivialDefectN_nonneg
#print axioms MassGap.FlatCap.flat_cap
#print axioms MassGap.FlatCap.restW_nonneg
#print axioms MassGap.FlatCap.flatW_le_fluxW
#print axioms MassGap.FlatCap.flatW_eq_zero_one
#print axioms MassGap.FlatCap.windowCoupling_eq_rest_one
#print axioms MassGap.FlatCap.fifteen_constant
#print axioms MassGap.FlatCap.tendsto_fluxLog
#print axioms MassGap.FlatCap.tendsto_fluxW
#print axioms MassGap.FlatCap.tendsto_restW
#print axioms MassGap.FlatCap.vanishes_iff_split
#print axioms MassGap.FlatCap.vanishes_of_rest_contraction
#print axioms MassGap.FlatCap.windowCoupling_le_rest_add_cap
#print axioms MassGap.FlatCap.anchor_split_vanishes
