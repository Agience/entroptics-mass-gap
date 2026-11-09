import Mathlib
import MassGap.CouplingTower
import MassGap.TorusContraction
import MassGap.FocusZoom
import MassGap.AttractCost

/-!
# MassGap.Telescope — the observer's four settings, the strict focus condition, and what focus reaches

The observer reads the substrate the way a telescope reads a scene. Four settings fix what is read:
**direction** (the slice axis `i` and the channel read: tensor, flux sector or zero-flux), **distance** (the
separation at which decorrelation is read; for the gap it goes to `∞`, the far field), **zoom** (the window,
block side `2^w`) and **focus** (the length matched to the subject). In `entroptics-rf` the same four are the
carrier, the offset, `L` and the read's cliff; there every one is measured and none is told. This module states the
four as reads, writes the strict focus condition as a Prop, and tests what it gives. Declarations are in the
namespace `MassGap.Telescope`.

## 1. The lens (proved, real arithmetic)

The shell cost of a closed flux configuration of size `R` is `shellCost A B R = A R + B / R`, with `A = c σ` the
line coefficient (tension times the loop's length per unit size) and `B = c'` the blur coefficient (the
localisation cost). Only `A` and `B` enter: `c` and `σ` are never read separately, and the floor and the focus
depend on the product `c σ` alone (`matches_focusZoom`). The focal length is `focusLen A B = √(B/A)` and the floor
is `floorCost A B = 2 √(A B)`.

* `floor_le_cost` (from `AttractCost.two_sqrt_le_cost`): `floorCost ≤ shellCost` at every `R > 0`.
* **`cost_sub_floor`**: `shellCost A B R − floorCost A B = A (R − R*)² / R`, `R* = focusLen A B`. The excess over
  the floor is exact and quadratic in the defocus.
* **`cost_eq_floor_iff`** (the strict focus condition, the lens equation): at `A > 0`, `B ≥ 0`, `R > 0`, the cost equals
  the floor exactly when `R = R*`. Equivalently (`line_eq_blur_iff`) the line term equals the blur term,
  `A R = B / R`. In focus means the tension (the line) and the blur balance.
* **`floor_lt_cost`**: off focus the cost is strictly above the floor.
  **`cost_at_scale`**: at `R = λ R*`, `shellCost = √(A B) (λ + 1/λ)`, so the cost relative to the floor is
  `(λ + 1/λ)/2`, the blur factor of a defocus by `λ`.
* `matches_focusZoom`: at `A = c σ`, `B = c'` these are `FocusZoom.focus_attains`'s `R* = √c'/√(cσ)` and floor
  `2 √(c c' σ)`.

## 2. The four settings as reads

**Direction** (proved: a carrier exists; argued: fixed by symmetry). `exists_carrier`: for any read
`r : Fin 4 → ℝ` of decay rates over the four axes, some axis has the least rate (the longest-range, strongest
signal); `carrier_of_symm`: if the read is the same on every axis, every axis is a carrier. The hypercubic symmetry
of the periodic state makes the axis reads equal (argued; `FluxHopGap` and `TransferGapMeasured` quantify over
every `i`), so `MeasureN`'s axis `0` is a carrier (argued; `MeasureN` takes it as chosen, by the same symmetry). The channel is fixed by what each read needs: the
line `A` is read on the flux sector, the blur `B` on the zero-flux (closed-loop) side, the gap on the tensor read.

**Zoom and focus** (proved: the reads are exact on the two-term shape). From a measured cost read `E` at two
windows `R` and `2R` (the zoom and one doubling):
`lineRead E R = (2 E(2R) − E(R)) / (3R)`, `blurRead E R = R (4 E(R) − 2 E(2R)) / 3`.
**`reads_exact`**: if `E(r) = A r + B / r` at `r = R, 2R`, the reads return `A` and `B`; `reads_shellCost`: on the
shell cost itself they return its two coefficients at every window. So `A` and `B` are measured, and
`R* = focusLen A B` and the focus window are functions of the capture (`u₀`: see `focusCoupling`). The tree's tension read is
`hopTension N i T β j = log o(j) − log o(j + 1)`, `o = RelayChain.relayOdds`, the per-hop decay of the flux
odds at aperture `T`. **`hopTension_ge`**: a `TorusContraction.HopClause` at factor `q > 0` gives,
at `β ≥ 0`, `−log q ≤ hopTension` at every index `k ≥ j₀` where the odds at `k + 1` are positive; **`hopTension_ge_rate`**: at the
factor `e^{−2 s m}` of `FluxHopGap` this is `2 s m ≤ hopTension`. Argued, not a declaration: the line coefficient
of the closed loop at side `R` is `hopTension / (2 T)` per lattice length, times the loop's length per unit size.

**Distance** (proved). `farField_rate`: a decorrelation `e^{−E t}` with any prefactor `e^{−P}` reads the rate
`(E t + P)/t → E` as `t → ∞`. In the far field the prefactor, the near-field part, drops out: one lens, focused at
infinity, and the near field allowed to blur.

## 3. The strict focus condition

```
def InFocus (A B : ℝ) (w : ℕ) : Prop :=
  0 < A ∧ 0 < B ∧ (2 : ℝ) ^ w ≤ focusLen A B ∧ focusLen A B < 2 * (2 : ℝ) ^ w
```

The window `2^w` lies at or below the focal length by less than one doubling. The factor `2` is the doubling of the
window, not a chosen tolerance: windows are dyadic, and once `R* ≥ 1` exactly one dyadic window brackets `R*`.

* `inFocus_unique`: at most one window is in focus. **`inFocus_iff_exists`**: some window is in focus iff
  `A > 0`, `B > 0` and `R* ≥ 1` (the focus is resolvable on the lattice). `focusWindow A B` names it.
* **`focus_line`** (the lens equation at the window): in focus, `B/4 < A (2^w)² ≤ B`. The dimensionless line at the
  focus window, tension times window squared, is pinned to the blur coefficient. This is the constraint focus
  imposes: it selects the window, it does not constrain the theory.
* **`inFocus_cost`**: in focus, `shellCost A B (2^w) ≤ (5/4) floorCost A B`.

## 4. The three questions

**(a) The floor at focus** (proved). `floor_pos_iff`: at `B > 0`, `A ≥ 0`, `floorCost A B > 0 ↔ A > 0`;
`inFocus_floor_pos`: in focus the floor is positive. The floor at focus is positive exactly when the line exists.
Circularity (argued): as arithmetic it is not circular, since `A` and `B` are read at two finite windows and the
floor is computed from them. As a gap statement it is the gap clause at `m = 2 √(A B)`: the floor bounds the cost of
the loop state of size `R*`, and a loop read gives an upper bound on the lowest excitation (a Rayleigh quotient
over centred states), not a lower bound. A lower bound needs every excited level to cost at least the shell cost at
its own size, which is `AttractCost.LevelsCost`, and with the size free that is the gap
(`AttractCost.levelsCost_iff_gap`); pinning the size to `R*` gives the same clause at the same `m`. What focus
adds is that `m` is a measured number, `2 √(A B)` from the two-window reads, where `AttractCost` and
`FocusZoom` take `c`, `c'` as told.

**(b) Off focus** (proved). `cost_sub_floor`, `floor_lt_cost`, `cost_at_scale`: the excess is `A (R − R*)²/R > 0`
at `R ≠ R*`, and at defocus `λ` the cost is the floor times `(λ + 1/λ)/2`.

**(c) Does focus reach the basin?** No, not alone. `LineSeedsBasin` is a sufficient link; it carries content only once `A` is tied to the measured tension read; `LineSeedsBasin.TensionBelow` does that,
and `LineSeedsBasin.lineSeedsBasinTwo_of_halves` proves the link from `w = 2` given that tie and the zero-flux half
`LineSeedsBasin.ZeroFluxAtWindow` (with `A`, `B` free, the link plus the
focus clause is interderivable with `StrongEnd` through `CouplingTower.windowCoupling_decay`: put `A = K/4^c`,
`B = K` at a seed window `c`; argued).
* `focus_without_link` (proved): on abstract readings, a lens in focus at every `β` (`A = B = 1`, window `0`) is
  compatible with a window reading that never enters the basin. The focus condition reads `A`, `B` and the window;
  it does not read the window coupling.
* **`LineSeedsBasin N A K`** (assumed, the missing link): at every `β ≥ 0` and window `w ≥ 1`, if the
  dimensionless line `A(β) (2^w)²` is at least `K`, the window coupling `CouplingTower.windowCoupling N β w` is at
  most `1/1000`. A window that holds at least `K` units of tension area is in the confined basin.
* **`strongEnd_of_focus`** (proved): with `LineSeedsBasin N A K`, if frequently in `β` a window `w` is in focus
  with `1 ≤ w + k` and `4 K ≤ (2^k)² B(β)`, then `CouplingTower.StrongEnd N`. The window used is `k` doublings past
  the focus, `k` fixed: far field. At `k = 0` it is the focus window itself, with `4K ≤ B`
  (`focusCoupling_le`).
* **`couplingTower_of_focus`** (proved): with `WeakEnd N u₀`, `0 < u₀`, a coupling tower exists, and with
  `u₀ ≤ 1/1000` `CouplingTower.observerGap_along` applies to it given its remaining hypotheses (`Φ`,
  `UniformBoundFG`, `PhysRange`).
* `focusCoupling N A B β = windowCoupling N β (focusWindow (A β) (B β))`: `u₀` read at the focus window.
  `focusCoupling_of_scales` (proved): if the window coupling is a function `φ` of the dimensionless line alone
  (`CouplingScales`, assumed), the focus coupling is `φ(x)` with `x ∈ (B/4, B]`. With `B` constant along `β`
  this pins `u₀` within `φ` of a fixed interval: the line of constant window coupling, read off the lens. Exact
  constancy of `u₀` is not reached: windows are dyadic, so `x` moves inside `(B/4, B]`.
So the named link is `LineSeedsBasin`, with `A` the measured line, together with the size of `B` against `K`: tension area on the
window must force the doubling reading into the basin. It is a strong-coupling statement at the window's own
scale, not the gap at infinity; whether it holds uniformly in `β` is open.

## 5. Where the focus sits against the crossover

`blur_lt_line_iff` (proved): at `R > 0`, `B / R < A R ↔ R* < R`. Below the focal length the blur term dominates
the cost (the ultraviolet side, supercritical); above it the line term dominates (the confined side). The focus
is the crossover of the cost between the two: confinement is the line, and the far field lies on one side of it.
So focus does not put the window past the crossover; it puts it at or within one doubling below the crossover, and every window `k ≥ 1`
doublings above it (`strongEnd_of_focus`) is past it in this read. `WindowRelay.PastPeak` reads the crossover on
a different quantity, the coarse plaquette susceptibility; no theorem connects its peak step to `log₂ R*`
(argued: both mark the passage from blur-dominated to line-dominated reads, so the peak step and `log₂ R*` should
differ by a bounded number of doublings; not proved, and no declaration here refers to `PastPeak`).

## 6. Tests

* **`β = 0`** (proved). `hopTension_zero_coupling`: the odds are `0` at every index, and with `log 0 = 0` the
  tension read is `0`. Physically the tension is infinite and `R* = 0`: the focus is at the lattice spacing and
  `InFocus` fails. In Lean it fails through the read `A = 0` (`not_inFocus_of_nonpos_line`), the same branch as
  the free field, so the read does not tell `β = 0` from the massless case; the physical `R* = 0 < 1` excludes
  focus by `inFocus_iff_exists` (argued). `basin_near_zero`: at every fixed window the window coupling is in the basin on a neighbourhood of
  `β = 0` (continuity and `windowCoupling_zero`), so `LineSeedsBasin` is consistent with strong coupling there.
  Strong coupling (argued): `UniformRelayStrong.uniformRelayGap` gives a uniform relay gap below `β₀`, which
  bounds the flux odds above by `e^{−2m(j+1)}` up to a constant; this is a rate uniform in `T`, not a line `A`
  uniform in `T`, so it does not by itself give `A (2^w)² ≥ K`; `PeriodicStrongCoupling`
  gives the transfer gap of the periodic state there. Not combined into a declaration here.
* **Free field** (proved). `focusLen_free`: `focusLen 0 B = 0` in Lean's convention; `focus_at_infinity`: as
  `A → 0⁺` the focal length tends to `∞` (at `B > 0`); `no_floor_free`: at `A = 0` the cost has no positive
  floor; `not_inFocus_of_nonpos_line`: no window is in focus. Massless: the focus is at infinity and there is no
  floor.
* **The open flux tube** (proved). `string_no_focus`: a flux tube energy `σ T − (π/12)/T` (Lüscher term,
  negative) read through the two windows gives `B = −π/12 < 0`, and no window is in focus. The lens is the contractible
  closed loop; that its blur coefficient is positive (localisation beating its Casimir term) is argued, not
  proved, and is the condition for focus to exist on the zero-flux side.
* **Vacuity** (proved). `bracket_of_neg`: at `A = B = −1` the bracket clause alone holds at `w = 0`, so the
  positivity clauses of `InFocus` are load-bearing; `not_inFocus_of_nonpos_line`, `not_inFocus_of_nonpos_blur`:
  `A ≤ 0` or `B ≤ 0` excludes focus. `inFocus_iff_exists`: once `A, B > 0` and `R* ≥ 1`, a focus window exists,
  and it is unique. So `InFocus` is a selection of the window, met by exactly one window whenever the line and
  the blur are positive; it is not a hypothesis about the theory beyond `A, B > 0`, `R* ≥ 1`.
* **Restatement against reduction** (argued, on the declarations above). "`σ > 0` measured at focus" is not the
  gap restated: `A > 0` is a two-window read and says the line exists at that scale. It gives the gap only through
  a lower bound of every level by the shell cost (part (a)), which is the gap clause at `m = 2 √(A B)`. The reduction
  focus achieves is on the constants: `m`, `R*` and the focus window are measured.
* **Only measured scales.** `A`, `B` and `R*` are in the units of the cost read `E` (lattice units if `E` is per
  lattice length); `A (2^w)²`, `R*/2^w` and `(λ + 1/λ)/2` are dimensionless; `focusWindow` is an index. No spacing
  `aRun` enters.

## Parameters

| setting / symbol | meaning | status |
|---|---|---|
| direction `i` | slice axis | measured (`exists_carrier`); all equal by symmetry (argued) |
| channel | flux sector for `A`, zero-flux for `B`, tensor for the gap | fixed by the read |
| distance `t` | separation of the decorrelation read | `t → ∞` (far field) |
| `E` | measured cost read at a window | measured |
| `A = c σ` | line coefficient, `lineRead E R` | measured (argued: `lineRead` of the loop cost read); a free function in `strongEnd_of_focus` |
| `B = c'` | blur coefficient, `blurRead E R` | measured (argued: `blurRead` of the loop cost read); a free function in `strongEnd_of_focus` |
| zoom `2^w` | the window | measured: the focus window `focusWindow A B` |
| focus `R*` | `√(B/A)` | measured |
| `k` | doublings past focus in `strongEnd_of_focus` | chosen, fixed before `β` |
| `K` | tension area threshold of `LineSeedsBasin` | shared with the assumed link |
| `u₀` | constant of `WeakEnd` in `couplingTower_of_focus`; `focusCoupling` is its β-dependent read at the focus window | shared with the assumed `WeakEnd`; pinned to `φ((B/4, B])` only under `CouplingScales` |
| `c`, `σ` separately | not read | not needed (only `c σ` enters) |

## What is proved, argued, assumed

* Proved: every declaration below, with standard axioms only.
* Argued: the axis symmetry; the identification of `A` with the closed loop's line coefficient from
  `hopTension`; the upper-bound reading of the loop cost in (a); the relation of `log₂ R*` to `PastPeak`; the
  strong-coupling test of `LineSeedsBasin`; the sign of the zero-flux blur `B`; the converse reading of
  `LineSeedsBasin` with `A`, `B` free.
* Assumed (named Props, used only where stated): `LineSeedsBasin` (in `strongEnd_of_focus`, `focusCoupling_le`,
  `couplingTower_of_focus`), `CouplingScales` (in `focusCoupling_of_scales`), and `WeakEnd` (in
  `couplingTower_of_focus`).

DERIVED (module-wide): `2` the doubling of the window and the square; `3 = 2² − 1` from solving the two windows;
`4 = 2²` the square of the doubling; `5/4 = (2 + 1/2)/2` the worst blur factor `(λ + 1/λ)/2` on `λ ∈ [1/2, 1]`;
`1/1000` the seed of `DoublingSharp`; `π/12` the Lüscher coefficient `π (d − 2)/24` at `d = 4`; `1` the least
window index and the unit of the vacuity example; `0` the free coupling and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.Telescope

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd WeakEnd CouplingTower continuous_windowCoupling
  windowCoupling_zero exists_couplingTower)
open MassGap.RelayChain (relayOdds relayZ0 relayZ0_pos relayOdds_zero_coupling)
open MassGap.TorusContraction (HopClause fluxTrace odds_step ratio_mono fluxTrace_nonneg relayZ0_lc)

/-! ## 1. The lens -/

/-- **The shell cost** of a closed flux configuration of size `R`: line `A R` plus blur `B / R`.
DERIVED: no numeral. -/
def shellCost (A B R : ℝ) : ℝ := A * R + B / R

/-- **The focal length** `R* = √(B/A)`. DERIVED: no numeral. -/
def focusLen (A B : ℝ) : ℝ := Real.sqrt (B / A)

/-- **The floor** `2 √(A B)`. DERIVED: `2` the two equal terms at focus. -/
def floorCost (A B : ℝ) : ℝ := 2 * Real.sqrt (A * B)

/-- DERIVED: `2` the square. -/
theorem exists_sq {A : ℝ} (hA : 0 ≤ A) : ∃ a : ℝ, 0 ≤ a ∧ A = a ^ 2 :=
  ⟨Real.sqrt A, Real.sqrt_nonneg A, (Real.sq_sqrt hA).symm⟩

/-- DERIVED: `2` the square. -/
theorem exists_sq_pos {A : ℝ} (hA : 0 < A) : ∃ a : ℝ, 0 < a ∧ A = a ^ 2 :=
  ⟨Real.sqrt A, Real.sqrt_pos.2 hA, (Real.sq_sqrt hA.le).symm⟩

/-- DERIVED: `2` the square. -/
theorem focusLen_sq {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : focusLen (a ^ 2) (b ^ 2) = b / a := by
  unfold focusLen
  rw [← div_pow, Real.sqrt_sq (div_nonneg hb ha.le)]

/-- DERIVED: `2` the square and the two terms. -/
theorem floorCost_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : floorCost (a ^ 2) (b ^ 2) = 2 * (a * b) := by
  unfold floorCost
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg ha hb)]

/-- **The floor is below the cost** at every size (`AttractCost.two_sqrt_le_cost` at `c = 1`).
DERIVED: `1` the unit factor. -/
theorem floor_le_cost {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 < R) :
    floorCost A B ≤ shellCost A B R := by
  have h := AttractCost.two_sqrt_le_cost (c := 1) (c' := B) (σ := A) zero_le_one hB hA hR
  unfold floorCost shellCost
  rw [show A * B = 1 * B * A by ring, show A * R = 1 * A * R by ring]
  exact h

/-- **The excess over the floor is exact**: `shellCost A B R − floorCost A B = A (R − R*)² / R`.
DERIVED: `2` the square. -/
theorem cost_sub_floor {A B R : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) :
    shellCost A B R - floorCost A B = A * (R - focusLen A B) ^ 2 / R := by
  obtain ⟨a, ha, rfl⟩ := exists_sq_pos hA
  obtain ⟨b, hb, rfl⟩ := exists_sq hB
  rw [focusLen_sq ha hb, floorCost_sq ha.le hb]
  unfold shellCost
  field_simp
  ring

/-- **The strict focus condition (the lens equation)**: the cost equals the floor exactly at `R = R*`.
DERIVED: `2` the square. -/
theorem cost_eq_floor_iff {A B R : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) :
    shellCost A B R = floorCost A B ↔ R = focusLen A B := by
  rw [← sub_eq_zero, cost_sub_floor hA hB hR]
  constructor
  · intro h
    have h1 := (div_eq_zero_iff.1 h).resolve_right hR.ne'
    have h2 := (mul_eq_zero.1 h1).resolve_left hA.ne'
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  · intro h
    rw [h, sub_self]
    simp

/-- **Off focus the cost is strictly above the floor.** DERIVED: `2` the square. -/
theorem floor_lt_cost {A B R : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) (hne : R ≠ focusLen A B) :
    floorCost A B < shellCost A B R := by
  have h := cost_sub_floor hA hB hR
  have hsq : 0 < (R - focusLen A B) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have hpos : 0 < A * (R - focusLen A B) ^ 2 / R := div_pos (mul_pos hA hsq) hR
  linarith

/-- **The blur factor of a defocus**: at `R = λ R*`, `shellCost = √(A B) (λ + 1/λ)`.
DERIVED: `1` the unit defocus. -/
theorem cost_at_scale {A B l : ℝ} (hA : 0 < A) (hB : 0 < B) (hl : 0 < l) :
    shellCost A B (l * focusLen A B) = Real.sqrt (A * B) * (l + 1 / l) := by
  obtain ⟨a, ha, rfl⟩ := exists_sq_pos hA
  obtain ⟨b, hb, rfl⟩ := exists_sq_pos hB
  rw [focusLen_sq ha hb.le, ← mul_pow, Real.sqrt_sq (mul_nonneg ha.le hb.le)]
  unfold shellCost
  field_simp

/-- **The line equals the blur exactly at focus.** DERIVED: no numeral. -/
theorem line_eq_blur_iff {A B R : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) :
    A * R = B / R ↔ R = focusLen A B := by
  obtain ⟨a, ha, rfl⟩ := exists_sq_pos hA
  obtain ⟨b, hb, rfl⟩ := exists_sq hB
  rw [focusLen_sq ha hb, eq_div_iff hR.ne', eq_div_iff ha.ne']
  have e : a ^ 2 * R * R = (R * a) ^ 2 := by ring
  rw [e, pow_left_inj₀ (by positivity) hb two_ne_zero]

/-- **Which term dominates**: at `R > 0`, the line dominates the blur exactly above the focal length.
DERIVED: no numeral. -/
theorem blur_lt_line_iff {A B R : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hR : 0 < R) :
    B / R < A * R ↔ focusLen A B < R := by
  obtain ⟨a, ha, rfl⟩ := exists_sq_pos hA
  obtain ⟨b, hb, rfl⟩ := exists_sq hB
  rw [focusLen_sq ha hb, div_lt_iff₀ hR, div_lt_iff₀ ha]
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have := mul_self_le_mul_self (by positivity : 0 ≤ R * a) hc
    nlinarith
  · intro h
    have := mul_self_lt_mul_self hb h
    nlinarith

/-- **The lens of `FocusZoom`**: at `A = c σ`, `B = c'` the focal length is `√c'/√(cσ)` and the floor is
`2 √(c c' σ)`, attained there (`FocusZoom.focus_attains`). DERIVED: `2` the two terms. -/
theorem matches_focusZoom {c c' σ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ) :
    focusLen (c * σ) c' = Real.sqrt c' / Real.sqrt (c * σ)
      ∧ floorCost (c * σ) c' = 2 * Real.sqrt (c * c' * σ)
      ∧ shellCost (c * σ) c' (focusLen (c * σ) c') = floorCost (c * σ) c' := by
  have h1 : focusLen (c * σ) c' = Real.sqrt c' / Real.sqrt (c * σ) := Real.sqrt_div hc'.le _
  have h2 : floorCost (c * σ) c' = 2 * Real.sqrt (c * c' * σ) := by
    unfold floorCost; rw [show c * σ * c' = c * c' * σ by ring]
  refine ⟨h1, h2, ?_⟩
  rw [h2, h1]
  exact (FocusZoom.focus_attains hc hc' hσ).2

/-! ## 2. The settings as reads -/

/-- **A carrier exists**: some axis has the least decay rate. DERIVED: `4` the axes. -/
theorem exists_carrier (r : Fin 4 → ℝ) : ∃ i : Fin 4, ∀ j : Fin 4, r i ≤ r j := by
  obtain ⟨i, -, hi⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- **Under symmetry every axis is a carrier.** DERIVED: `4` the axes. -/
theorem carrier_of_symm {r : Fin 4 → ℝ} (h : ∀ i j, r i = r j) (i : Fin 4) : ∀ j : Fin 4, r i ≤ r j :=
  fun j => (h i j).le

/-- **The line read** from a cost read at the windows `R` and `2R`. DERIVED: `2` the doubling; `3 = 2² − 1`. -/
def lineRead (E : ℝ → ℝ) (R : ℝ) : ℝ := (2 * E (2 * R) - E R) / (3 * R)

/-- **The blur read** from a cost read at the windows `R` and `2R`. DERIVED: `2` the doubling; `4 = 2²`;
`3 = 2² − 1`. -/
def blurRead (E : ℝ → ℝ) (R : ℝ) : ℝ := R * (4 * E R - 2 * E (2 * R)) / 3

/-- **The two-window reads are exact on the two-term shape.** DERIVED: `2`, `3`, `4` as in the reads. -/
theorem reads_exact {E : ℝ → ℝ} {A B R : ℝ} (hR : R ≠ 0) (h1 : E R = A * R + B / R)
    (h2 : E (2 * R) = A * (2 * R) + B / (2 * R)) : lineRead E R = A ∧ blurRead E R = B := by
  unfold lineRead blurRead
  rw [h1, h2]
  constructor
  · rw [div_eq_iff (mul_ne_zero three_ne_zero hR)]
    field_simp
    ring
  · field_simp
    ring

/-- **On the shell cost the reads return its coefficients**, at every window. DERIVED: `2` the doubling. -/
theorem reads_shellCost {A B R : ℝ} (hR : R ≠ 0) :
    lineRead (shellCost A B) R = A ∧ blurRead (shellCost A B) R = B :=
  reads_exact hR rfl rfl

section Tension

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The tension read**: the per-hop decay of the flux odds at aperture `T`, `log o(j) − log o(j + 1)`.
DERIVED: `1` the hop. -/
def hopTension (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  Real.log (relayOdds N i T β j) - Real.log (relayOdds N i T β (j + 1))

/-- **The hop clause bounds the tension read below**: past the anchor, wherever the odds are positive,
`−log q ≤ hopTension`. DERIVED: `1` the hop. -/
theorem hopTension_ge {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ} (hβ : 0 ≤ β) {j₀ k : ℕ}
    {q : ℝ} (hq : 0 < q) (hH : HopClause N i T β j₀ q) (hk : j₀ ≤ k)
    (hpos : 0 < relayOdds N i T β (k + 1)) : -Real.log q ≤ hopTension N i T β k := by
  have hs : relayOdds N i T β (k + 1) ≤ q * relayOdds N i T β k :=
    odds_step (F := fluxTrace N i T β) (Z := relayZ0 N i T β) (fun j => relayZ0_pos hβ j) hq.le
      (fluxTrace_nonneg hβ k) (hH k hk) (ratio_mono (fun j => relayZ0_pos hβ j) (relayZ0_lc hβ) j₀ k hk)
  have hok : 0 < relayOdds N i T β k := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hl := Real.log_le_log hpos hs
  rw [Real.log_mul hq.ne' hok.ne'] at hl
  unfold hopTension
  linarith

/-- **At the factor of `FluxHopGap`**: `2 s m ≤ hopTension`. DERIVED: `2` the two-hop time step. -/
theorem hopTension_ge_rate {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ} (hβ : 0 ≤ β) {j₀ k : ℕ}
    {s m : ℝ} (hH : HopClause N i T β j₀ (Real.exp (-(2 * s * m)))) (hk : j₀ ≤ k)
    (hpos : 0 < relayOdds N i T β (k + 1)) : 2 * s * m ≤ hopTension N i T β k := by
  have h := hopTension_ge hβ (Real.exp_pos _) hH hk hpos
  rwa [Real.log_exp, neg_neg] at h

/-- **At `β = 0` the tension read is `0`** (the odds vanish; `log 0 = 0`). DERIVED: `0` the coupling. -/
theorem hopTension_zero_coupling (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (j : ℕ) :
    hopTension N i T 0 j = 0 := by
  unfold hopTension
  rw [relayOdds_zero_coupling, relayOdds_zero_coupling]
  simp

end Tension

/-- **The far field reads the rate**: `(E t + P)/t → E` as `t → ∞`, whatever the prefactor `P`.
DERIVED: `0` the vanishing near-field share. -/
theorem farField_rate (E P : ℝ) : Tendsto (fun t : ℝ => (E * t + P) / t) atTop (𝓝 E) := by
  have h : Tendsto (fun t : ℝ => E + P / t) atTop (𝓝 (E + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [add_div, mul_div_assoc, div_self ht.ne', mul_one]

/-! ## 3. The strict focus condition -/

/-- **In focus**: the line and the blur are positive and the window `2^w` lies at or below the focal length by
less than one doubling. DERIVED: `2` the doubling of the window. -/
def InFocus (A B : ℝ) (w : ℕ) : Prop :=
  0 < A ∧ 0 < B ∧ (2 : ℝ) ^ w ≤ focusLen A B ∧ focusLen A B < 2 * (2 : ℝ) ^ w

/-- **At most one window is in focus.** DERIVED: `2` the doubling; `1` the step. -/
theorem inFocus_unique {A B : ℝ} {w w' : ℕ} (h : InFocus A B w) (h' : InFocus A B w') : w = w' := by
  have h1 : (2 : ℝ) ^ w < 2 ^ (w' + 1) := by rw [pow_succ]; linarith [h.2.2.1, h'.2.2.2]
  have h2 : (2 : ℝ) ^ w' < 2 ^ (w + 1) := by rw [pow_succ]; linarith [h'.2.2.1, h.2.2.2]
  rw [pow_lt_pow_iff_right₀ (by norm_num)] at h1 h2
  omega

/-- **Some window is in focus iff the line and the blur are positive and the focus is resolvable.**
DERIVED: `1` the lattice unit; `2` the doubling. -/
theorem inFocus_iff_exists {A B : ℝ} :
    (∃ w : ℕ, InFocus A B w) ↔ 0 < A ∧ 0 < B ∧ 1 ≤ focusLen A B := by
  constructor
  · rintro ⟨w, hA, hB, h1, -⟩
    exact ⟨hA, hB, (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans h1⟩
  · rintro ⟨hA, hB, h⟩
    obtain ⟨n, h1, h2⟩ := exists_nat_pow_near h (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, hA, hB, h1, ?_⟩
    rw [pow_succ] at h2
    linarith

open Classical in
/-- **The focus window**, when one exists; `0` otherwise. DERIVED: `0` the default. -/
def focusWindow (A B : ℝ) : ℕ := if h : ∃ w : ℕ, InFocus A B w then Classical.choose h else 0

open Classical in
/-- DERIVED: no numeral. -/
theorem focusWindow_spec {A B : ℝ} (h : ∃ w : ℕ, InFocus A B w) : InFocus A B (focusWindow A B) := by
  unfold focusWindow
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- DERIVED: no numeral. -/
theorem focusWindow_eq {A B : ℝ} {w : ℕ} (h : InFocus A B w) : focusWindow A B = w :=
  inFocus_unique (focusWindow_spec ⟨w, h⟩) h

/-- **The lens equation at the window**: in focus, `B/4 < A (2^w)² ≤ B`. DERIVED: `4 = 2²`, `2` the
doubling. -/
theorem focus_line {A B : ℝ} {w : ℕ} (h : InFocus A B w) :
    B / 4 < A * ((2 : ℝ) ^ w) ^ 2 ∧ A * ((2 : ℝ) ^ w) ^ 2 ≤ B := by
  obtain ⟨hA, hB, h1, h2⟩ := h
  obtain ⟨a, ha, rfl⟩ := exists_sq_pos hA
  obtain ⟨b, hb, rfl⟩ := exists_sq_pos hB
  rw [focusLen_sq ha hb.le] at h1 h2
  set R : ℝ := (2 : ℝ) ^ w with hRdef
  have hR : 0 < R := by positivity
  have e1 : a * R ≤ b := by rw [mul_comm]; exact (le_div_iff₀ ha).1 h1
  have e2 : b < 2 * (a * R) := by
    have := (div_lt_iff₀ ha).1 h2
    linarith
  have q1 := mul_self_le_mul_self (by positivity : 0 ≤ a * R) e1
  have q2 := mul_self_lt_mul_self hb.le e2
  constructor <;> nlinarith [q1, q2]

/-- **In focus the cost is within `5/4` of the floor.** DERIVED: `5/4 = (2 + 1/2)/2`. -/
theorem inFocus_cost {A B : ℝ} {w : ℕ} (h : InFocus A B w) :
    shellCost A B ((2 : ℝ) ^ w) ≤ 5 / 4 * floorCost A B := by
  obtain ⟨hA, hB, h1, h2⟩ := h
  obtain ⟨a, ha, rfl⟩ := exists_sq_pos hA
  obtain ⟨b, hb, rfl⟩ := exists_sq_pos hB
  rw [focusLen_sq ha hb.le] at h1 h2
  rw [floorCost_sq ha.le hb.le]
  set R : ℝ := (2 : ℝ) ^ w with hRdef
  have hR : 0 < R := by positivity
  have e1 : a * R ≤ b := by rw [mul_comm]; exact (le_div_iff₀ ha).1 h1
  have e2 : b < 2 * (a * R) := by
    have := (div_lt_iff₀ ha).1 h2
    linarith
  unfold shellCost
  rw [← sub_nonneg]
  have e : 5 / 4 * (2 * (a * b)) - (a ^ 2 * R + b ^ 2 / R) = (2 * b - a * R) * (a * R - b / 2) / R := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hR.le

/-! ## 4. (a) The floor at focus -/

/-- **The floor is positive iff the line exists** (at positive blur). DERIVED: `2` the two terms. -/
theorem floor_pos_iff {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) : 0 < floorCost A B ↔ 0 < A := by
  unfold floorCost
  constructor
  · intro h
    rcases hA.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul, Real.sqrt_zero, mul_zero] at h
      exact absurd h (lt_irrefl 0)
  · intro h
    have := Real.sqrt_pos.2 (mul_pos h hB)
    linarith

/-- **In focus the floor is positive.** DERIVED: no numeral. -/
theorem inFocus_floor_pos {A B : ℝ} {w : ℕ} (h : InFocus A B w) : 0 < floorCost A B :=
  (floor_pos_iff h.1.le h.2.1).2 h.1

/-! ## 5. (c) The basin -/

/-- **The missing link** (assumed where used): tension area at least `K` on a window forces the window coupling
into the basin. DERIVED: `1` the least window index; `1/1000` the seed; `2` the doubling. -/
def LineSeedsBasin (N : ℕ) (A : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → K ≤ A β * ((2 : ℝ) ^ w) ^ 2 → windowCoupling N β w ≤ 1 / 1000

/-- **(S) from focus and the link**: the window `k` doublings past the focus is in the basin, frequently in
`β`. DERIVED: `4 = 2²`; `2` the doubling. -/
theorem strongEnd_of_focus {N : ℕ} (hN : N ≠ 0) {A B : ℝ → ℝ} {K : ℝ} (k : ℕ) (hL : LineSeedsBasin N A K)
    (hF : ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ w : ℕ, 1 ≤ w + k ∧ 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B β ∧
      InFocus (A β) (B β) w) : StrongEnd N := by
  refine (CouplingTower.strongEnd_iff_seed hN).mpr
    (hF.mono fun β ⟨hβ, w, hwk, hK, hw⟩ => ⟨w + k, hwk, hL β hβ (w + k) hwk ?_⟩)
  have hl := (focus_line hw).1
  have e : A β * ((2 : ℝ) ^ (w + k)) ^ 2 = (A β * ((2 : ℝ) ^ w) ^ 2) * ((2 : ℝ) ^ k) ^ 2 := by
    rw [pow_add]; ring
  rw [e]
  have h4 : 0 ≤ ((2 : ℝ) ^ k) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hl.le h4
  nlinarith

/-- **A tower from focus**: with (W), focus and the link give a coupling tower. DERIVED: `4`, `2` as above. -/
theorem couplingTower_of_focus {N : ℕ} (hN : N ≠ 0) {u₀ : ℝ} (hu : 0 < u₀) (hW : WeakEnd N u₀)
    {A B : ℝ → ℝ} {K : ℝ} (k : ℕ) (hL : LineSeedsBasin N A K)
    (hF : ∃ᶠ β in atTop, 0 ≤ β ∧ ∃ w : ℕ, 1 ≤ w + k ∧ 4 * K ≤ ((2 : ℝ) ^ k) ^ 2 * B β ∧
      InFocus (A β) (B β) w) : ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
  exists_couplingTower hN hu (strongEnd_of_focus hN k hL hF) hW

/-- **`u₀` read at the focus window.** DERIVED: no numeral. -/
def focusCoupling (N : ℕ) (A B : ℝ → ℝ) (β : ℝ) : ℝ :=
  windowCoupling N β (focusWindow (A β) (B β))

/-- **The focus window is in the basin** under the link with `4 K ≤ B`. DERIVED: `4 = 2²`; `1/1000` the seed. -/
theorem focusCoupling_le {N : ℕ} {A B : ℝ → ℝ} {K : ℝ} (hL : LineSeedsBasin N A K) {β : ℝ} (hβ : 0 ≤ β)
    {w : ℕ} (hw : InFocus (A β) (B β) w) (hw1 : 1 ≤ w) (hK : 4 * K ≤ B β) :
    focusCoupling N A B β ≤ 1 / 1000 := by
  unfold focusCoupling
  rw [focusWindow_eq hw]
  refine hL β hβ w hw1 ?_
  have := (focus_line hw).1
  linarith

/-- **Scaling of the window coupling** (assumed where used): the window coupling depends on `β` and `w` only
through the dimensionless line `A(β) (2^w)²`. DERIVED: `1` the least window index; `2` the doubling. -/
def CouplingScales (N : ℕ) (A : ℝ → ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → windowCoupling N β w = φ (A β * ((2 : ℝ) ^ w) ^ 2)

/-- **Under scaling, `u₀` at focus is `φ` on `(B/4, B]`.** DERIVED: `4 = 2²`. -/
theorem focusCoupling_of_scales {N : ℕ} {A B : ℝ → ℝ} {φ : ℝ → ℝ} (hS : CouplingScales N A φ) {β : ℝ}
    (hβ : 0 ≤ β) {w : ℕ} (hw : InFocus (A β) (B β) w) (hw1 : 1 ≤ w) :
    ∃ x : ℝ, B β / 4 < x ∧ x ≤ B β ∧ focusCoupling N A B β = φ x := by
  refine ⟨A β * ((2 : ℝ) ^ w) ^ 2, (focus_line hw).1, (focus_line hw).2, ?_⟩
  unfold focusCoupling
  rw [focusWindow_eq hw]
  exact hS β hβ w hw1

/-- The basin (seed) form of `StrongEnd` on an arbitrary reading (`strongEnd_iff_of`). DERIVED: `1` the least
index; `1/1000` the sharp seed of `DoublingSharp`. -/
def StrongEndOf (g : ℝ → ℕ → ℝ) : Prop :=
  ∃ᶠ β in atTop, ∃ c : ℕ, 1 ≤ c ∧ g β c ≤ 1 / 1000

/-- `StrongEnd` in the seed form, for `N ≠ 0`. DERIVED: `0` the excluded rank. -/
theorem strongEnd_iff_of {N : ℕ} (hN : N ≠ 0) : StrongEnd N ↔ StrongEndOf (windowCoupling N) :=
  CouplingTower.strongEnd_iff_seed hN

/-- **Focus alone does not reach the basin**: a lens in focus at every `β` with a reading that never enters it.
DERIVED: `1` the unit lens and reading; `0` the window. -/
theorem focus_without_link :
    ∃ (g : ℝ → ℕ → ℝ) (A B : ℝ → ℝ), (∀ β, InFocus (A β) (B β) 0) ∧ ¬ StrongEndOf g := by
  refine ⟨fun _ _ => 1, fun _ => 1, fun _ => 1, fun _ => ?_, ?_⟩
  · refine ⟨one_pos, one_pos, ?_, ?_⟩ <;> norm_num [focusLen]
  · rw [StrongEndOf, Filter.not_frequently]
    exact Filter.Eventually.of_forall fun _ ⟨_, _, h⟩ => by norm_num at h

/-! ## 6. Tests -/

/-- **Strong coupling at a fixed window**: near `β = 0` the window coupling is in the basin.
DERIVED: `0` the coupling; `1/1000` the seed. -/
theorem basin_near_zero {N : ℕ} (hN : N ≠ 0) (w : ℕ) :
    ∀ᶠ β in 𝓝 (0 : ℝ), windowCoupling N β w ≤ 1 / 1000 := by
  have hc := (continuous_windowCoupling hN w).tendsto 0
  rw [windowCoupling_zero] at hc
  exact hc.eventually (eventually_le_nhds (by norm_num))

/-- **Free field**: the focal length at zero line is `0` (Lean's convention for `R* = ∞`). DERIVED: `0`. -/
theorem focusLen_free (B : ℝ) : focusLen 0 B = 0 := by
  simp [focusLen]

/-- **No line, no focus.** DERIVED: no numeral. -/
theorem not_inFocus_of_nonpos_line {A B : ℝ} {w : ℕ} (hA : A ≤ 0) : ¬ InFocus A B w :=
  fun h => absurd h.1 (not_lt.2 hA)

/-- **No blur, no focus.** DERIVED: no numeral. -/
theorem not_inFocus_of_nonpos_blur {A B : ℝ} {w : ℕ} (hB : B ≤ 0) : ¬ InFocus A B w :=
  fun h => absurd h.2.1 (not_lt.2 hB)

/-- **Focus at infinity**: as the line vanishes, the focal length diverges. DERIVED: `2` the square. -/
theorem focus_at_infinity {B : ℝ} (hB : 0 < B) : Tendsto (fun A => focusLen A B) (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro M
  have h := (Filter.Tendsto.const_mul_atTop hB (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))).eventually_ge_atTop
    (M ^ 2)
  filter_upwards [h] with A hA
  calc M ≤ |M| := le_abs_self M
    _ = Real.sqrt (M ^ 2) := (Real.sqrt_sq_eq_abs M).symm
    _ ≤ Real.sqrt (B / A) := Real.sqrt_le_sqrt (by rwa [div_eq_mul_inv])

/-- **Free field: no floor.** At zero line the cost goes below every `m > 0` (`AttractCost.no_floor_without_tension`).
DERIVED: `1` the unit factor; `0` the line. -/
theorem no_floor_free {B m : ℝ} (hB : 0 ≤ B) (hm : 0 < m) : ∃ R : ℝ, 0 < R ∧ shellCost 0 B R < m := by
  obtain ⟨R, hR, h⟩ := AttractCost.no_floor_without_tension (c := 1) hB hm
  exact ⟨R, hR, by simpa [shellCost] using h⟩

/-- **The open flux tube has no focus**: its Lüscher term gives a negative blur read. DERIVED: `12` from
`π (d − 2)/24` at `d = 4`. -/
theorem string_no_focus {σ T : ℝ} (hT : T ≠ 0) (w : ℕ) :
    ¬ InFocus (lineRead (shellCost σ (-(Real.pi / 12))) T) (blurRead (shellCost σ (-(Real.pi / 12))) T) w := by
  rw [(reads_shellCost hT).2]
  exact not_inFocus_of_nonpos_blur (by have := Real.pi_pos; linarith)

/-- **Vacuity**: the bracket alone is met by a negative pair, so the positivity clauses are load-bearing.
DERIVED: `1` the unit pair; `0` the window; `2` the doubling. -/
theorem bracket_of_neg :
    (2 : ℝ) ^ 0 ≤ focusLen (-1) (-1) ∧ focusLen (-1) (-1) < 2 * (2 : ℝ) ^ 0 := by
  constructor <;> norm_num [focusLen]

end MassGap.Telescope

end

#print axioms MassGap.Telescope.floor_le_cost
#print axioms MassGap.Telescope.cost_sub_floor
#print axioms MassGap.Telescope.cost_eq_floor_iff
#print axioms MassGap.Telescope.floor_lt_cost
#print axioms MassGap.Telescope.cost_at_scale
#print axioms MassGap.Telescope.line_eq_blur_iff
#print axioms MassGap.Telescope.blur_lt_line_iff
#print axioms MassGap.Telescope.matches_focusZoom
#print axioms MassGap.Telescope.exists_carrier
#print axioms MassGap.Telescope.carrier_of_symm
#print axioms MassGap.Telescope.reads_exact
#print axioms MassGap.Telescope.reads_shellCost
#print axioms MassGap.Telescope.hopTension_ge
#print axioms MassGap.Telescope.hopTension_ge_rate
#print axioms MassGap.Telescope.hopTension_zero_coupling
#print axioms MassGap.Telescope.farField_rate
#print axioms MassGap.Telescope.inFocus_unique
#print axioms MassGap.Telescope.inFocus_iff_exists
#print axioms MassGap.Telescope.focusWindow_spec
#print axioms MassGap.Telescope.focusWindow_eq
#print axioms MassGap.Telescope.focus_line
#print axioms MassGap.Telescope.inFocus_cost
#print axioms MassGap.Telescope.floor_pos_iff
#print axioms MassGap.Telescope.inFocus_floor_pos
#print axioms MassGap.Telescope.strongEnd_of_focus
#print axioms MassGap.Telescope.couplingTower_of_focus
#print axioms MassGap.Telescope.focusCoupling_le
#print axioms MassGap.Telescope.focusCoupling_of_scales
#print axioms MassGap.Telescope.strongEnd_iff_of
#print axioms MassGap.Telescope.focus_without_link
#print axioms MassGap.Telescope.basin_near_zero
#print axioms MassGap.Telescope.focusLen_free
#print axioms MassGap.Telescope.focus_at_infinity
#print axioms MassGap.Telescope.no_floor_free
#print axioms MassGap.Telescope.string_no_focus
#print axioms MassGap.Telescope.bracket_of_neg
