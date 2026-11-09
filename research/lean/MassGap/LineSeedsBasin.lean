import Mathlib
import MassGap.Telescope
import MassGap.WeakEndProved
import MassGap.ZeroFluxGap

/-!
# MassGap.LineSeedsBasin — the link split into a flux half (proved) and a zero-flux half (named)

`Telescope.LineSeedsBasin N A K` asks that a window holding tension area `A(β) (2^w)² ≥ K` be in the basin,
`CouplingTower.windowCoupling N β w = defectW N β (2^w) ≤ 1/1000`. By `CentreSectorSeedN.defectW_le_of_sectorsN`
the basin follows from two sector bounds at every step `i` of side `n = 2^w`: the flux share
`fluxShareN ≤ 1/80000` and the zero-flux defect `trivialDefectN ≤ 1/80000`. This module ties `A` to the measured
tension read, proves the flux half from it, names the zero-flux half, and chains both to the observer's gap.
Declarations are in the namespace `MassGap.LineSeedsBasin`.

## 1. The measured tension area (proved)

At side `n = 2^w` and step `i` the flux share is the relay share at aperture `Tr n i` and chain index `n/2 − 1`
(`RelayChain.fluxShareN_eq_relay`, `rfl`). The tension read on that same aperture and chain is
`Telescope.hopTension N i (Tr n i) β k = log o(k) − log o(k + 1)`, `o = RelayChain.relayOdds`. The chain has
`n/2` relays (indices `0` to `n/2 − 1`), so `n/2 − 1` hops; each hop adds two time steps, so the chain sweeps a
time extent `n − 2` from its one-hop anchor.

    tensionArea N β w i = Σ_{k < 2^w/2 − 1} hopTension N i (Tr (2^w) i) β k

* **`tensionArea_eq`**: `tensionArea = log o(0) − log o(2^w/2 − 1)`, exactly (the sum telescopes), whatever the
  zeros of `o`. `tensionArea_one`: at `w = 1` the chain has no hop and the area is `0`.
* **`relayOdds_le_of_logDrop`** (the log `0` convention handled): if `L ≤ log o(0) − log o(J)` then
  `o(J) ≤ N³ e^{−L}`. Case `o(J) = 0`: nothing to prove. Case `o(J) > 0`: `log o(0) ≤ log N³` in both sub-cases
  (`o(0) = 0` reads `log 0 = 0 ≤ log N³`; `o(0) > 0` uses `o(0) ≤ N³ − 1`, `RelayChain.relayOdds_le_card`).
* `fluxShareN_le_of_area`: `L ≤ tensionArea` gives `fluxShareN N β (2^w) i ≤ N³ e^{−L}`
  (`RelayChain.relayShare_le_odds`); `fluxShareN_le_of_area_ge`: `log(80000 N³) ≤ tensionArea` gives
  `fluxShareN ≤ 1/80000`.

**The line** (argued reading; `TensionBelow` is a named Prop). The flux sheet winding the aperture spans the time extent `n − 2` times a winding length; the
aperture's extents are at least `n` (`RelayChain.le_Tr`). `TensionBelow N A` says `A(β)` is a lower bound of the
measured tension per unit sheet area at every window `w ≥ 2` and step:

    A(β) · 2^w (2^w − 2) ≤ tensionArea N β w i.

At `w = 1` both sides are `0` and the clause carries nothing, so it is asked from `w = 2`, where the sheet bound
`2^w − 2 ≥ 2^w/2` used by (F) holds.

## 2. (F) the flux half (proved)

**`fluxHalf`**: with `TensionBelow N A` and `K ≥ K_F = 2 log(80000 N³)`, at every `β ≥ 0`, window `w ≥ 2` and
step `i`, `K ≤ A(β) (2^w)²` gives `fluxShareN N β (2^w) i ≤ 1/80000`. The factor `2` in `K_F` is the sheet's
`2^w − 2 ≥ 2^w/2` at `w ≥ 2`. At `N = 2`, `K_F = 2 log 640000 ≈ 26.7`.

## 3. (Z) the zero-flux half (named, assumed where used)

    def ZeroFluxAtWindow (A : ℝ → ℝ) (K : ℝ) : Prop :=
      ∀ β, 0 ≤ β → ∀ w, 2 ≤ w → K ≤ A β * ((2 : ℝ) ^ w) ^ 2 → ∀ i : Fin 4,
        2 * log Z₀(j) − log Z₀(2j + 1) ≤ 1/80000,     j = 2^w/2 − 1,  aperture Tr (2^w) i

`Z₀ = RelayChain.relayZ0` the zero-flux chain trace. On the windows where the tension area is at least `K`, the
zero-flux chain trace at the window's chain length is log-convex to within `1/80000`. It is stated in measured
traces; `trivialDefectN_eq_read` (from `RelayChain.relayDefect_eq`) identifies its left side with
`trivialDefectN N β (2^w) i`, and `zeroFluxAtWindow_iff` restates it as the zero-flux clause of
`defectW_le_of_sectorsN` on those windows.

**What it relates to** (proved, `ZeroFluxGap`). With an eigenpair `(λ, φ)` of the zero-flux one-hop kernel at the
window's aperture (`ZeroFluxGap.ZeroFluxGapAt`) and `x = ZeroFluxGap.excitedW` at index `j`:
* `trivialDefectN_le_excited`: `trivialDefectN ≤ 2 x` (from `defect_le_excess`, `log(1 + x) ≤ x`);
  `zeroFluxRead_of_excited`: `x ≤ 1/160000` gives the clause.
* `excited_of_zeroFluxRead`: at `ρ ≤ |λ|`, the clause gives `log(1 + x) ≤ 1/80000`.
So, wherever an eigenpair with `ρ ≤ |λ|` is given (`λ` is `c` in Lean), (Z) is within a factor `2` the statement that the excited zero-flux weight at the
window's chain length is below `≈ 1/80000`: the zero-flux sector has decorrelated over the window's own time
extent. That is the zero-flux (closed-loop) part of the gap, read at the window, with its anchor. It is not
implied by the tension read: the flux odds and the zero-flux defect are reads of different sectors, and
`ZeroFluxGap.no_defect_from_rate` (real-number lemma; spectral reading argued) shows that no rate and chain length
alone bound the defect.

**Is (Z) controlled by the blur `B` at focus?** No declaration ties them. In `Telescope` `B` is a free function;
its reading as `blurRead` of the closed-loop cost is argued, and no theorem relates a cost read on the zero-flux
side to `relayZ0`'s log-convexity. Argued: `B` is a localization coefficient (a cost at size `R`, `B/R`),
while the defect is an excited-weight count at a fixed chain length; a positive `B` constrains the lowest
closed-loop cost from one side, not the multiplicity of zero-flux states below it, which is what the anchor of
`ZeroFluxGap.trivialDefectN_le_gap` counts. At the focus window the lens fixes `A (2^w)² ∈ (B/4, B]`
(`Telescope.focus_line`), a statement about the line, so focus feeds (F) and leaves (Z) open.

## 4. The chain (proved)

* `LineSeedsBasinTwo N A K`: `Telescope.LineSeedsBasin` asked at windows `w ≥ 2`
  (`lineSeedsBasinTwo_of_lineSeedsBasin`: it is implied by `Telescope.LineSeedsBasin`). The `Telescope` form at `w = 1` is not
  reachable from the tension read: the side-`2` chain has no hop (`tensionArea_one`).
* **`lineSeedsBasinTwo_of_halves`**: `TensionBelow N A`, `K_F ≤ K` and `ZeroFluxAtWindow N A K` give
  `LineSeedsBasinTwo N A K` (`fluxHalf`, the zero-flux clause, `defectW_le_of_sectorsN`).
* `area_of_focus`, `strongEnd_of_focus_two`: `Telescope.strongEnd_of_focus` with windows `w + k ≥ 2`.
* `past_crossover`: in focus at `w`, the window `w + k`, `k ≥ 1`, lies past the crossover:
  `R* < 2^{w+k}` and the line dominates the blur there (`Telescope.blur_lt_line_iff`).
* **`observerGap_of_tension_zeroFlux`** (capstone): for `2 ≤ N`, `0 < u₀ ≤ 1/1000`, `TensionBelow N A`,
  `K_F ≤ K`, `ZeroFluxAtWindow N A K`, `k ≥ 1`, and frequently in `β` a window `w` in focus with `2 ≤ w + k` and
  `4K ≤ (2^k)² B(β)`: frequently in `β` the window `k` doublings past the focus is past the crossover and in the
  basin; a coupling tower at `u₀` exists (`WeakEndProved.strongEnd_iff_exists_couplingTower'`); and along it, for
  every flow `Φ` with `UniformBoundFG` and `PhysRange`, the observer's transfer has a gap at every step
  (`CouplingTower.observerGap_along`). `strongEnd_of_tension_zeroFlux` is the `StrongEnd` step alone.

## 5. Tests

* **`β = 0`** (proved). `tensionArea_zero_coupling`: the area is `0` (the odds vanish, `log 0 = 0`).
  `tensionBelow_zero_coupling`: `TensionBelow N A` forces `A(0) ≤ 0`, and `fluxHalf_hyp_zero_coupling`: at
  `K > 0` no window meets `K ≤ A(0) (2^w)²`, so (F) is not used at `β = 0`; the read `A(0) ≤ 0` is the
  free-field branch, so it does not tell `β = 0` from the massless case (`Telescope` section 6). `zeroFluxRead_zero_coupling`: the zero-flux defect at `β = 0` is `≤ 0` at
  every window (`ZeroFluxGap.zeroFluxGapAt_zero_coupling`, `excitedW_zero_coupling`), so the conclusion of (Z)
  holds there.
* **Strong coupling** (proved conclusions; tension argued). `halves_near_zero`: at every window `w ≥ 1` there is
  `β₀ > 0` with both sector bounds at `1/80000` on `[0, β₀]` (`SubstrateFluxRead.sectors_strong`). This is a
  witness for the conclusions of both halves, not for their hypothesis: the tree proves only upper bounds on the
  odds at strong coupling, and `tensionArea ≥ K` needs a lower bound on `o(0)` against `o(J)`. Argued, leading
  order: the odds are `≈ c · u^{2 T (j + 1)}` with `u ∝ β`, so `hopTension ≈ 2 T log(1/u)` and the measured line
  is `A ≈ (T/n) log(1/u) ≥ log(1/u) → ∞` as `β → 0⁺` (`T ≥ n` the winding extent), while at `β = 0` itself
  the read is `0` (`log 0 = 0`, `tensionBelow_zero_coupling`); `UniformRelayStrong.uniformRelayGap` gives the rate, uniform in `T`, not the
  line.
* **Vacuity and `log 0`** (proved). A single hop read can be positive for a trivial reason:
  `hop_read_from_zero` (real numbers): `0 < log 0 − log y` for `0 < y < 1`, a hop from odds `0` to odds `y`. The
  area telescopes exactly (`tensionArea_eq`); it can still read large from a zero anchor (`o(0) = 0` reads
  `log 0 = 0`), but the bound it feeds is sound at every zero: `relayOdds_le_of_logDrop` uses only
  `log o(0) ≤ log N³`, true in both cases. At the other end an exact zero `o(J) = 0` makes the area
  `log o(0)`, bounded, so `TensionBelow` can fail where the flux share is smallest.
  A per-hop minimum `τ` read gives `(2^w/2 − 1) τ ≤ tensionArea` (`area_ge_of_hop`) and inherits the same bound.
  The read cannot be large at `β = 0` (it is `0`) or at `w = 1` (it is `0`).
* **Measured scales only.** `tensionArea` is a difference of logs of trace ratios; `A (2^w)²` and `K_F` are
  dimensionless; the window is an index. No spacing enters.
* **Restatement against reduction.** (F) is a theorem with explicit `K_F`. Its content is thin and stated:
  `tensionArea` is `log o(0) − log o(J)` exactly, so (F) is the anchor bound `o(0) ≤ N³ − 1`, `share ≤ odds`
  and the sheet geometry `2^w − 2 ≥ 2^w/2`; what it does is tie the free `A` of `Telescope` to a measured read
  on the same aperture and chain as the flux share. `ZeroFluxAtWindow` is the zero-flux clause of the seed on the
  windows of large tension area (`zeroFluxAtWindow_iff`), stated in measured traces: it is that clause, not a
  reduction of it. It is a sector of the gap read at each window, asked at every window of tension area at least `K`; at a `β`
  with `A(β) > 0` that is every window from some size on.
* **Supercritical rule.** The capstone asks `k ≥ 1` and returns that the window used is past the crossover
  (`past_crossover`).

## Parameters

| symbol | meaning | status |
|---|---|---|
| `N` | gauge group `SU(N)` | shared; `2 ≤ N` in the capstone |
| `β` | coupling | swept; frequently in `β` in the capstone |
| `w` | window index, side `2^w` | swept, `w ≥ 2` (`w ≥ 1` in `halves_near_zero`) |
| `i` | corner-path step | every `i : Fin 4` |
| `Tr (2^w) i` | aperture of step `i` | fixed by the window (the flux share's own aperture) |
| `j = 2^w/2 − 1` | chain index of the window | fixed by the window; `j` hops from the anchor |
| `tensionArea` | `Σ hopTension` over the window's chain | measured |
| `A` | tension per unit sheet area | free; tied to the read by the assumed `TensionBelow` |
| `B` | blur coefficient | free, as in `Telescope` |
| `K_F` | `2 log(80000 N³)` | derived: (F)'s threshold |
| `K` | tension-area threshold | chosen, `K ≥ K_F`, shared with `ZeroFluxAtWindow` |
| `k` | doublings past the focus | chosen, `k ≥ 1`, fixed before `β` |
| `u₀` | tower constant | chosen, `0 < u₀ ≤ 1/1000` |
| `λ, φ, ρ` | zero-flux eigenpair and remainder norm (`c, φ, ρ` in Lean) | given: hypotheses (`ZeroFluxGapAt`) of the relations |
| `β₀` | strong-coupling range of `halves_near_zero` | derived from `strongBound (2^w)` |

## What is proved, argued, assumed

* Proved: every theorem below, with standard axioms only.
* Argued: the sheet reading of `tensionArea` and `A` (time extent `2^w − 2` by winding length); the
  leading-order strong-coupling line `A ≈ log(1/u)`; the absence of a link from `B` to the zero-flux defect.
* Assumed (named Props, used only where stated): `TensionBelow N A` (the tie of `A` to the read; with `A(β) > 0`,
  as focus requires, it is an area law of the flux odds with one constant uniform over every window `w ≥ 2` at that
  `β`, a confinement input asked at arbitrarily weak coupling) and `ZeroFluxAtWindow N A K` (the open zero-flux half), in `lineSeedsBasinTwo_of_halves`,
  `strongEnd_of_tension_zeroFlux` and `observerGap_of_tension_zeroFlux`; `LineSeedsBasinTwo` in
  `strongEnd_of_focus_two`.

DERIVED (module-wide): `80000`, `1/80000` the sector thresholds of `defectW_le_of_sectorsN`; `160000 = 2 · 80000`;
`1/1000` the seed; `3` in `N³ = |Z_N³|` and `N³ − 1` the anchor bound; `2` the doubling, the square, the
two-hop step and the half sheet `2^w − 2 ≥ 2^w/2`; `4 = 2²`; `8 = 2² (2² − 2)` the sheet at `w = 2`;
`65536 = 2^{16}` and `4 + N⁶` from `sectors_strong`; `0`, `1` the anchor index, the hop and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.LineSeedsBasin

open Filter Topology
open MassGap MassGap.ZoomSelfScale MassGap.MeasuredTower MassGap.MeasuredSpacing MassGap.ClayTreeG
  MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG MassGap.FlowClusterG
open MassGap.RelayChain (relayOdds relayZ0)
open MassGap.Telescope (hopTension InFocus focusLen)
open MassGap.CouplingTower (windowCoupling StrongEnd CouplingTower)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)

/-! ## 1. Real-number steps and the focus geometry -/

/-- **A single hop read can be positive from a zero**: a hop from odds `0` to odds `y ∈ (0, 1)` reads
`log 0 − log y > 0`. DERIVED: `0`, `1`. -/
theorem hop_read_from_zero {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < Real.log 0 - Real.log y := by
  rw [Real.log_zero]
  have := Real.log_neg hy0 hy1
  linarith

/-- **The window past the focus holds the area**: in focus at `w`, `4K ≤ (2^k)² B` gives
`K ≤ A (2^{w+k})²`. DERIVED: `4 = 2²`; `2` the doubling. -/
theorem area_of_focus {A B K : ℝ} {w k : ℕ} (hw : InFocus A B w) (hK : 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B) :
    K ≤ A * ((2 : ℝ) ^ (w + k)) ^ 2 := by
  have hl := (Telescope.focus_line hw).1
  have e : A * ((2 : ℝ) ^ (w + k)) ^ 2 = (A * ((2 : ℝ) ^ w) ^ 2) * ((2 : ℝ) ^ k) ^ 2 := by
    rw [pow_add]; ring
  rw [e]
  have h4 : 0 ≤ ((2 : ℝ) ^ k) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hl.le h4
  nlinarith

/-- **The window `k ≥ 1` doublings past the focus is past the crossover**: `R* < 2^{w+k}`, and there the line
dominates the blur. DERIVED: `1` the least doubling; `2` the doubling. -/
theorem past_crossover {A B : ℝ} {w k : ℕ} (h : InFocus A B w) (hk : 1 ≤ k) :
    focusLen A B < (2 : ℝ) ^ (w + k) ∧ B / (2 : ℝ) ^ (w + k) < A * (2 : ℝ) ^ (w + k) := by
  have h2k : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hp : (0 : ℝ) < 2 ^ w := by positivity
  have h2 : 2 * (2 : ℝ) ^ w ≤ 2 ^ (w + k) := by
    rw [pow_add]; nlinarith
  have hlt : focusLen A B < 2 ^ (w + k) := lt_of_lt_of_le h.2.2.2 h2
  exact ⟨hlt, (Telescope.blur_lt_line_iff h.1 h.2.1.le (by positivity)).2 hlt⟩

/-! ## 2. The basin from windows `w ≥ 2` -/

section Basin

variable {N : ℕ}

variable (N) in
/-- **`Telescope.LineSeedsBasin` from the window `w = 2` on** (assumed where used). DERIVED: `2` the least
window with a hop; `1/1000` the seed. -/
def LineSeedsBasinTwo (A : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 2 ≤ w → K ≤ A β * ((2 : ℝ) ^ w) ^ 2 → windowCoupling N β w ≤ 1 / 1000

/-- `Telescope.LineSeedsBasin` implies the link from `w = 2`. DERIVED: `1`, `2`. -/
theorem lineSeedsBasinTwo_of_lineSeedsBasin {A : ℝ → ℝ} {K : ℝ}
    (h : MassGap.Telescope.LineSeedsBasin N A K) : LineSeedsBasinTwo N A K :=
  fun β hβ w hw hA => h β hβ w (by omega) hA

/-- **(S) from focus and the link from `w = 2`**. DERIVED: `4 = 2²`; `2` the least window. -/
theorem strongEnd_of_focus_two (hN : N ≠ 0) {A B : ℝ → ℝ} {K : ℝ} (k : ℕ) (hL : LineSeedsBasinTwo N A K)
    (hF : ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ w : ℕ, 2 ≤ w + k ∧ 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B β ∧
      InFocus (A β) (B β) w) : StrongEnd N :=
  (CouplingTower.strongEnd_iff_seed hN).mpr
    (hF.mono fun β ⟨hβ, w, hwk, hK, hw⟩ => ⟨w + k, by omega, hL β hβ (w + k) hwk (area_of_focus hw hK)⟩)

end Basin

/-! ## 3. The tension area and the flux half -/

section Tension

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The measured tension area** at window `w`, step `i`: the hop tension summed over the window's chain, on the
flux share's own aperture `Tr (2^w) i`. DERIVED: `2` the side and the half; `1` the anchor offset. -/
def tensionArea (β : ℝ) (w : ℕ) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ w / 2 - 1), hopTension N i (CentreSectorSeed.Tr (2 ^ w) i) β k

/-- **The area telescopes**: `tensionArea = log o(0) − log o(2^w/2 − 1)`. DERIVED: `0` the anchor; `2`, `1`. -/
theorem tensionArea_eq (β : ℝ) (w : ℕ) (i : Fin 4) :
    tensionArea N β w i = Real.log (relayOdds N i (CentreSectorSeed.Tr (2 ^ w) i) β 0)
      - Real.log (relayOdds N i (CentreSectorSeed.Tr (2 ^ w) i) β (2 ^ w / 2 - 1)) := by
  unfold tensionArea hopTension
  exact Finset.sum_range_sub' (fun k => Real.log (relayOdds N i (CentreSectorSeed.Tr (2 ^ w) i) β k)) _

/-- **At `w = 1` the chain has no hop.** DERIVED: `1`, `0`. -/
theorem tensionArea_one (β : ℝ) (i : Fin 4) : tensionArea N β 1 i = 0 := by
  unfold tensionArea
  norm_num

/-- **At `β = 0` the area is `0`.** DERIVED: `0`. -/
theorem tensionArea_zero_coupling (w : ℕ) (i : Fin 4) : tensionArea N 0 w i = 0 := by
  unfold tensionArea
  exact Finset.sum_eq_zero fun k _ => Telescope.hopTension_zero_coupling _ _ k

/-- **A per-hop floor gives the area.** DERIVED: `2`, `1`. -/
theorem area_ge_of_hop {β : ℝ} {w : ℕ} {i : Fin 4} {τ : ℝ}
    (h : ∀ k, k < 2 ^ w / 2 - 1 → τ ≤ hopTension N i (CentreSectorSeed.Tr (2 ^ w) i) β k) :
    ((2 ^ w / 2 - 1 : ℕ) : ℝ) * τ ≤ tensionArea N β w i := by
  unfold tensionArea
  have := Finset.card_nsmul_le_sum (Finset.range (2 ^ w / 2 - 1))
    (fun k => hopTension N i (CentreSectorSeed.Tr (2 ^ w) i) β k) τ
    (fun k hk => h k (Finset.mem_range.1 hk))
  rw [Finset.card_range, nsmul_eq_mul] at this
  exact this

/-- **A log drop bounds the odds**, through every zero: `L ≤ log o(0) − log o(J)` gives `o(J) ≤ N³ e^{−L}`.
DERIVED: `3`, `1` the anchor bound `N³ − 1 ≤ N³`; `0` the anchor. -/
theorem relayOdds_le_of_logDrop {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ} (hβ : 0 ≤ β) (J : ℕ)
    {L : ℝ} (hL : L ≤ Real.log (relayOdds N i T β 0) - Real.log (relayOdds N i T β J)) :
    relayOdds N i T β J ≤ (N : ℝ) ^ 3 * Real.exp (-L) := by
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := TorusContraction.cube_pos (N := N)
  have h1N3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by linarith [TorusContraction.nsub_cube_nonneg (N := N)]
  rcases (RelayChain.relayOdds_nonneg (N := N) (i := i) (T := T) hβ J).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h0le : Real.log (relayOdds N i T β 0) ≤ Real.log ((N : ℝ) ^ 3) := by
      rcases (RelayChain.relayOdds_nonneg (N := N) (i := i) (T := T) hβ 0).eq_or_lt with h00 | h0pos
      · rw [← h00, Real.log_zero]; exact Real.log_nonneg h1N3
      · exact Real.log_le_log h0pos
          (by linarith [RelayChain.relayOdds_le_card (N := N) (i := i) (T := T) hβ 0])
    have hlog : Real.log (relayOdds N i T β J) ≤ Real.log ((N : ℝ) ^ 3) + -L := by linarith
    calc relayOdds N i T β J = Real.exp (Real.log (relayOdds N i T β J)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (Real.log ((N : ℝ) ^ 3) + -L) := Real.exp_le_exp.mpr hlog
      _ = (N : ℝ) ^ 3 * Real.exp (-L) := by rw [Real.exp_add, Real.exp_log hN3]

/-- **The flux share from the area**: `L ≤ tensionArea` gives `fluxShareN N β (2^w) i ≤ N³ e^{−L}`.
DERIVED: `3`; `2` the side. -/
theorem fluxShareN_le_of_area {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) {L : ℝ}
    (hL : L ≤ tensionArea N β w i) : fluxShareN N β (2 ^ w) i ≤ (N : ℝ) ^ 3 * Real.exp (-L) := by
  rw [RelayChain.fluxShareN_eq_relay]
  refine (RelayChain.relayShare_le_odds hβ _).trans ?_
  exact relayOdds_le_of_logDrop hβ _ (hL.trans (tensionArea_eq β w i).le)

/-- **The flux clause from the area**: `log(80000 N³) ≤ tensionArea` gives `fluxShareN ≤ 1/80000`.
DERIVED: `80000`, `1/80000` the threshold; `3`. -/
theorem fluxShareN_le_of_area_ge {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4)
    (hL : Real.log (80000 * (N : ℝ) ^ 3) ≤ tensionArea N β w i) :
    fluxShareN N β (2 ^ w) i ≤ 1 / 80000 := by
  have h := fluxShareN_le_of_area hβ w i hL
  have hN0 := TorusContraction.cube_pos (N := N)
  rw [Real.exp_neg, Real.exp_log (by positivity)] at h
  calc fluxShareN N β (2 ^ w) i ≤ (N : ℝ) ^ 3 * (80000 * (N : ℝ) ^ 3)⁻¹ := h
    _ = 1 / 80000 := by
        rw [mul_inv, ← mul_assoc, mul_comm ((N : ℝ) ^ 3), mul_assoc, mul_inv_cancel₀ hN0.ne', mul_one,
          one_div]

variable (N) in
/-- **`A` is a measured lower bound of the tension per unit sheet area** (the tie of the line to the read):
`A(β) · 2^w (2^w − 2) ≤ tensionArea N β w i` at every `β ≥ 0`, window `w ≥ 2` and step `i`.
DERIVED: `2` the least window with a hop, the side and the time extent `2^w − 2` swept from the anchor. -/
def TensionBelow (A : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 2 ≤ w → ∀ i : Fin 4,
    A β * ((2 : ℝ) ^ w * ((2 : ℝ) ^ w - 2)) ≤ tensionArea N β w i

/-- **(F) The flux half**: with `A` a measured lower bound of the tension and `K ≥ 2 log(80000 N³)`, a window
`w ≥ 2` with tension area `A(β) (2^w)² ≥ K` has flux share at most `1/80000` at every step.
DERIVED: `2` the half sheet `2^w − 2 ≥ 2^w/2` at `w ≥ 2`; `80000`, `1/80000` the threshold; `4 = 2²`;
`3` the directions transverse to `i`, `N³ = |Z_N³|` the centre sectors (`TorusContraction`). -/
theorem fluxHalf {A : ℝ → ℝ} (hT : TensionBelow N A) {K : ℝ}
    (hK : 2 * Real.log (80000 * (N : ℝ) ^ 3) ≤ K) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 2 ≤ w)
    (hA : K ≤ A β * ((2 : ℝ) ^ w) ^ 2) (i : Fin 4) : fluxShareN N β (2 ^ w) i ≤ 1 / 80000 := by
  refine fluxShareN_le_of_area_ge hβ w i ?_
  have hT' := hT β hβ w hw i
  have hN3 := TorusContraction.cube_pos (N := N)
  have h1N3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by linarith [TorusContraction.nsub_cube_nonneg (N := N)]
  have hlog : 0 < Real.log (80000 * (N : ℝ) ^ 3) := Real.log_pos (by linarith)
  have h4 : (4 : ℝ) ≤ 2 ^ w := by
    have : (2 : ℝ) ^ 2 ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hw
    norm_num at this
    linarith
  set R : ℝ := (2 : ℝ) ^ w with hR
  have hApos : 0 < A β := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [sq_nonneg R]
  have hsq : R ^ 2 / 2 ≤ R * (R - 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (by linarith : (0 : ℝ) ≤ R)]
  have hhalf := mul_le_mul_of_nonneg_left hsq hApos.le
  linarith

/-! ## 4. The zero-flux half -/

variable (N) in
/-- **(Z) The zero-flux half** (assumed where used): on every window `w ≥ 2` with tension area
`A(β) (2^w)² ≥ K`, at every step, the zero-flux chain trace at the window's chain index `j = 2^w/2 − 1` and
aperture `Tr (2^w) i` is log-convex to within `1/80000`: `2 log Z₀(j) − log Z₀(2j + 1) ≤ 1/80000`.
DERIVED: `2` the square in `hs`, the side and the doubled chain `2j + 1`; `1/80000` the sector threshold. -/
def ZeroFluxAtWindow (A : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 2 ≤ w → K ≤ A β * ((2 : ℝ) ^ w) ^ 2 → ∀ i : Fin 4,
    2 * Real.log (relayZ0 N i (CentreSectorSeed.Tr (2 ^ w) i) β (2 ^ w / 2 - 1))
      - Real.log (relayZ0 N i (CentreSectorSeed.Tr (2 ^ w) i) β (2 * (2 ^ w / 2 - 1) + 1)) ≤ 1 / 80000

/-- **The zero-flux read is the cubic zero-flux defect.** DERIVED: `2`, `1`. -/
theorem trivialDefectN_eq_read {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) :
    trivialDefectN N β (2 ^ w) i
      = 2 * Real.log (relayZ0 N i (CentreSectorSeed.Tr (2 ^ w) i) β (2 ^ w / 2 - 1))
        - Real.log (relayZ0 N i (CentreSectorSeed.Tr (2 ^ w) i) β (2 * (2 ^ w / 2 - 1) + 1)) := by
  rw [RelayChain.trivialDefectN_eq_relay, RelayChain.relayDefect_eq hβ]

/-- **(Z) is the zero-flux clause of the seed on the windows of large tension area.** DERIVED: `2`,
`1/80000`. -/
theorem zeroFluxAtWindow_iff {A : ℝ → ℝ} {K : ℝ} :
    ZeroFluxAtWindow N A K ↔ ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 2 ≤ w → K ≤ A β * ((2 : ℝ) ^ w) ^ 2 →
      ∀ i : Fin 4, trivialDefectN N β (2 ^ w) i ≤ 1 / 80000 := by
  constructor
  · intro h β hβ w hw hA i
    rw [trivialDefectN_eq_read hβ]
    exact h β hβ w hw hA i
  · intro h β hβ w hw hA i
    rw [← trivialDefectN_eq_read hβ]
    exact h β hβ w hw hA i

/-- **The zero-flux defect is at most twice the excited weight**, at the window's chain index, from an eigenpair
of the zero-flux one-hop kernel. DERIVED: `2`, `1`. -/
theorem trivialDefectN_le_excited {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) {c ρ : ℝ}
    {φ : MassGap.SliceCentreAction.Cfg i (CentreSectorSeed.Tr (2 ^ w) i) N → ℝ}
    (h : ZeroFluxGap.ZeroFluxGapAt N i (CentreSectorSeed.Tr (2 ^ w) i) β c φ ρ) :
    trivialDefectN N β (2 ^ w) i
      ≤ 2 * ZeroFluxGap.excitedW N i (CentreSectorSeed.Tr (2 ^ w) i) β c φ (2 ^ w / 2 - 1) := by
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hc, heig, -⟩ := h
  have hd := ZeroFluxGap.defect_le_excess (ZeroFluxGap.bdd_K0 (N := N) (i := i)
    (T := CentreSectorSeed.Tr (2 ^ w) i) hβ) (ZeroFluxGap.K0_symm β) hφm hφb hφ1 heig hc (2 ^ w / 2 - 1)
  have hx0 := ZeroFluxGap.excess_nonneg (μ := RectTransfer.hS i (CentreSectorSeed.Tr (2 ^ w) i) N)
    (k := ZeroFluxGap.K0 N i (CentreSectorSeed.Tr (2 ^ w) i) β) (φ := φ) hc (2 ^ w / 2 - 1)
  have hl := ZeroFluxGap.log_one_add_le hx0
  rw [RelayChain.trivialDefectN_eq_relay, ZeroFluxGap.relayDefect_eq_chain hβ]
  unfold ZeroFluxGap.excitedW
  linarith

/-- **An excited weight at most `1/160000` gives the zero-flux clause.** DERIVED: `160000 = 2 · 80000`. -/
theorem zeroFluxRead_of_excited {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) {c ρ : ℝ}
    {φ : MassGap.SliceCentreAction.Cfg i (CentreSectorSeed.Tr (2 ^ w) i) N → ℝ}
    (h : ZeroFluxGap.ZeroFluxGapAt N i (CentreSectorSeed.Tr (2 ^ w) i) β c φ ρ)
    (hx : ZeroFluxGap.excitedW N i (CentreSectorSeed.Tr (2 ^ w) i) β c φ (2 ^ w / 2 - 1) ≤ 1 / 160000) :
    trivialDefectN N β (2 ^ w) i ≤ 1 / 80000 := by
  have := trivialDefectN_le_excited hβ w i h
  linarith

/-- **The zero-flux clause bounds the excited weight**, when the remainder is at most the top:
`log(1 + x) ≤ 1/80000`. DERIVED: `1`, `1/80000`. -/
theorem excited_of_zeroFluxRead {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) {c ρ : ℝ}
    {φ : MassGap.SliceCentreAction.Cfg i (CentreSectorSeed.Tr (2 ^ w) i) N → ℝ}
    (h : ZeroFluxGap.ZeroFluxGapAt N i (CentreSectorSeed.Tr (2 ^ w) i) β c φ ρ) (hρ : ρ ≤ |c|)
    (hd : trivialDefectN N β (2 ^ w) i ≤ 1 / 80000) :
    Real.log (1 + ZeroFluxGap.excitedW N i (CentreSectorSeed.Tr (2 ^ w) i) β c φ (2 ^ w / 2 - 1))
      ≤ 1 / 80000 :=
  ((ZeroFluxGap.relayDefect_two_sided hβ h hρ _).1).trans hd

/-! ## 5. The chain -/

/-- **The two halves give the link from `w = 2`.** DERIVED: `1`, `2` the window; `1/80000`; `3` as in
`fluxHalf` (`N³ = |Z_N³|`). -/
theorem lineSeedsBasinTwo_of_halves {A : ℝ → ℝ} {K : ℝ} (hT : TensionBelow N A)
    (hK : 2 * Real.log (80000 * (N : ℝ) ^ 3) ≤ K) (hZ : ZeroFluxAtWindow N A K) :
    LineSeedsBasinTwo N A K := by
  intro β hβ w hw hA
  have hw1 : 1 ≤ w := by omega
  show ZoomSelfScale.defectW N β (2 ^ w) ≤ 1 / 1000
  refine CentreSectorSeedN.defectW_le_of_sectorsN hβ (DeltaLengthTower.two_le_two_pow hw1)
    (DeltaLengthTower.even_two_pow hw1) fun i => ⟨fluxHalf hT hK hβ hw hA i, ?_⟩
  rw [trivialDefectN_eq_read hβ]
  exact hZ β hβ w hw hA i

/-- **(S) from the tension read, the zero-flux half and focus.** DERIVED: `2`, `4`, `80000`; `3` as in
`fluxHalf` (`N³ = |Z_N³|`). -/
theorem strongEnd_of_tension_zeroFlux {A B : ℝ → ℝ} {K : ℝ} (hT : TensionBelow N A)
    (hK : 2 * Real.log (80000 * (N : ℝ) ^ 3) ≤ K) (hZ : ZeroFluxAtWindow N A K) (k : ℕ)
    (hF : ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ w : ℕ, 2 ≤ w + k ∧ 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B β ∧
      InFocus (A β) (B β) w) : StrongEnd N :=
  strongEnd_of_focus_two (NeZero.ne N) k (lineSeedsBasinTwo_of_halves hT hK hZ) hF

/-- **The capstone: the observer's gap from the tension read and the zero-flux half.** Frequently in `β` the
window `k ≥ 1` doublings past the focus is past the crossover and in the basin; a coupling tower at `u₀` exists;
and along it the observer's transfer has a gap at every step. DERIVED: `1/1000` the seed; `2`, `4`, `80000` as
above; `1` the least doubling; `0` the plane; `3` as in `fluxHalf` (`N³ = |Z_N³|`). -/
theorem observerGap_of_tension_zeroFlux [Fact (2 ≤ N)] {u₀ : ℝ} (hu0 : 0 < u₀) (hu : u₀ ≤ 1 / 1000)
    {A B : ℝ → ℝ} {K : ℝ} (hT : TensionBelow N A) (hK : 2 * Real.log (80000 * (N : ℝ) ^ 3) ≤ K)
    (hZ : ZeroFluxAtWindow N A K) (k : ℕ) (hk : 1 ≤ k)
    (hF : ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ w : ℕ, 2 ≤ w + k ∧ 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B β ∧
      InFocus (A β) (B β) w) :
    (∃ᶠ β in atTop, ∃ w : ℕ, InFocus (A β) (B β) w ∧ focusLen (A β) (B β) < (2 : ℝ) ^ (w + k) ∧
      windowCoupling N β (w + k) ≤ 1 / 1000) ∧
    ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧
      ∀ (Φ : GFlow (MassGap.SUN.SU N)) (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) (r : ℝ)
        (hphys : Φ.PhysRange (schedAlongG _ βs) r) (m0 : ℕ),
        ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
          TransferGap.GapAt (transferNG (schedAlongG _ βs) (schedOS_alongG _ βs) Φ hB 0 hphys m0) ρ := by
  have hL := lineSeedsBasinTwo_of_halves hT hK hZ
  refine ⟨hF.mono fun β ⟨hβ, w, hwk, hK4, hw⟩ =>
    ⟨w, hw, (past_crossover hw hk).1, hL β hβ (w + k) hwk (area_of_focus hw hK4)⟩, ?_⟩
  have hS := strongEnd_of_focus_two (NeZero.ne N) k hL hF
  obtain ⟨βs, hTw⟩ :=
    (WeakEndProved.strongEnd_iff_exists_couplingTower' (Fact.out : 2 ≤ N) hu0 hu).1 hS
  exact ⟨βs, hTw, fun Φ hB r hphys m0 => CouplingTower.observerGap_along hu hTw Φ hB hphys m0⟩

/-! ## 6. Tests -/

/-- **At `β = 0` the tie forces `A(0) ≤ 0`.** DERIVED: `8 = 2² (2² − 2)`; `2` the window. -/
theorem tensionBelow_zero_coupling {A : ℝ → ℝ} (hT : TensionBelow N A) : A 0 ≤ 0 := by
  have h := hT 0 le_rfl 2 le_rfl 0
  rw [tensionArea_zero_coupling] at h
  have e : ((2 : ℝ) ^ 2 * ((2 : ℝ) ^ 2 - 2)) = 8 := by norm_num
  rw [e] at h
  linarith

/-- **At `β = 0` and `K > 0` no window meets (F)'s hypothesis.** DERIVED: `0`, `2`. -/
theorem fluxHalf_hyp_zero_coupling {A : ℝ → ℝ} (hT : TensionBelow N A) {K : ℝ} (hK : 0 < K) (w : ℕ) :
    ¬ K ≤ A 0 * ((2 : ℝ) ^ w) ^ 2 := by
  intro h
  have h0 := tensionBelow_zero_coupling hT
  nlinarith [sq_nonneg ((2 : ℝ) ^ w)]

/-- **At `β = 0` the zero-flux defect is at most `0` at every window.** DERIVED: `0`, `1`. -/
theorem zeroFluxRead_zero_coupling (w : ℕ) (i : Fin 4) : trivialDefectN N 0 (2 ^ w) i ≤ 0 := by
  have h := trivialDefectN_le_excited (N := N) le_rfl w i ZeroFluxGap.zeroFluxGapAt_zero_coupling
  rw [ZeroFluxGap.excitedW_zero_coupling] at h
  linarith

/-- **Strong coupling: both sector bounds hold near `β = 0` at every window.** DERIVED: `65536 = 2^{16}`,
`4 + N⁶` from `sectors_strong`; `80000`, `160000 = 2 · 80000` the thresholds. -/
theorem halves_near_zero (w : ℕ) (hw : 1 ≤ w) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ i : Fin 4,
      fluxShareN N β (2 ^ w) i ≤ 1 / 80000 ∧ trivialDefectN N β (2 ^ w) i ≤ 1 / 80000 := by
  have hS0 : 0 ≤ MassGap.StrongFiniteSize.strongBound (2 ^ w) := SubstrateFluxRead.strongBound_nonneg _
  have hN3 := TorusContraction.cube_pos (N := N)
  have hN6 : 0 ≤ (N : ℝ) ^ 6 := by positivity
  have hM : 0 < 4 + (N : ℝ) ^ 6 + 80000 * (N : ℝ) ^ 3 + 160000 := by positivity
  have hD : 0 < 65536 + (4 + (N : ℝ) ^ 6 + 80000 * (N : ℝ) ^ 3 + 160000)
      * MassGap.StrongFiniteSize.strongBound (2 ^ w) := by positivity
  refine ⟨1 / (65536 + (4 + (N : ℝ) ^ 6 + 80000 * (N : ℝ) ^ 3 + 160000)
    * MassGap.StrongFiniteSize.strongBound (2 ^ w)), by positivity, fun β hβ0 hβ i => ?_⟩
  set S := MassGap.StrongFiniteSize.strongBound (2 ^ w) with hSdef
  have hb : β * (65536 + (4 + (N : ℝ) ^ 6 + 80000 * (N : ℝ) ^ 3 + 160000) * S) ≤ 1 := by
    rwa [le_div_iff₀ hD] at hβ
  have hbs0 : 0 ≤ β * S := mul_nonneg hβ0 hS0
  have hMbs : 0 ≤ (4 + (N : ℝ) ^ 6 + 80000 * (N : ℝ) ^ 3 + 160000) * (β * S) := mul_nonneg hM.le hbs0
  have hβ' : β ≤ 1 / 65536 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hbs : (4 + (N : ℝ) ^ 6 + 80000 * (N : ℝ) ^ 3 + 160000) * (β * S) ≤ 1 := by nlinarith
  have h6 := mul_nonneg hN6 hbs0
  have h3 := mul_nonneg hN3.le hbs0
  have hδ : (4 + (N : ℝ) ^ 6) * (β * S) ≤ 2 := by nlinarith
  obtain ⟨hf, ht⟩ := SubstrateFluxRead.sectors_strong hβ0 hβ' (DeltaLengthTower.two_le_two_pow hw)
    (DeltaLengthTower.even_two_pow hw) hδ i
  refine ⟨hf.trans ?_, ht.trans ?_⟩
  · nlinarith
  · nlinarith

end Tension

end MassGap.LineSeedsBasin

end

#print axioms MassGap.LineSeedsBasin.hop_read_from_zero
#print axioms MassGap.LineSeedsBasin.area_of_focus
#print axioms MassGap.LineSeedsBasin.past_crossover
#print axioms MassGap.LineSeedsBasin.lineSeedsBasinTwo_of_lineSeedsBasin
#print axioms MassGap.LineSeedsBasin.strongEnd_of_focus_two
#print axioms MassGap.LineSeedsBasin.tensionArea_eq
#print axioms MassGap.LineSeedsBasin.tensionArea_one
#print axioms MassGap.LineSeedsBasin.tensionArea_zero_coupling
#print axioms MassGap.LineSeedsBasin.area_ge_of_hop
#print axioms MassGap.LineSeedsBasin.relayOdds_le_of_logDrop
#print axioms MassGap.LineSeedsBasin.fluxShareN_le_of_area
#print axioms MassGap.LineSeedsBasin.fluxShareN_le_of_area_ge
#print axioms MassGap.LineSeedsBasin.fluxHalf
#print axioms MassGap.LineSeedsBasin.trivialDefectN_eq_read
#print axioms MassGap.LineSeedsBasin.zeroFluxAtWindow_iff
#print axioms MassGap.LineSeedsBasin.trivialDefectN_le_excited
#print axioms MassGap.LineSeedsBasin.zeroFluxRead_of_excited
#print axioms MassGap.LineSeedsBasin.excited_of_zeroFluxRead
#print axioms MassGap.LineSeedsBasin.lineSeedsBasinTwo_of_halves
#print axioms MassGap.LineSeedsBasin.strongEnd_of_tension_zeroFlux
#print axioms MassGap.LineSeedsBasin.observerGap_of_tension_zeroFlux
#print axioms MassGap.LineSeedsBasin.tensionBelow_zero_coupling
#print axioms MassGap.LineSeedsBasin.fluxHalf_hyp_zero_coupling
#print axioms MassGap.LineSeedsBasin.zeroFluxRead_zero_coupling
#print axioms MassGap.LineSeedsBasin.halves_near_zero
