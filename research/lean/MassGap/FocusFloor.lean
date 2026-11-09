import Mathlib
import MassGap.Telescope
import MassGap.FloorTension
import MassGap.WindowFreq

/-!
# MassGap.FocusFloor — the inner edge of a contained pattern, read by sub-aperture spill, along the focus line

The open statement of the floor at every coupling, given flux confinement, is the zero-flux clause
`LineSeedsVanishing.ZeroFluxVanishing N β` at every `β ≥ 0` (`FloorTension.noStall_iff_flux_zeroFlux`). A pattern
contained in one window is not diffracted by the window's edge, so its floor needs an edge of its own. This module
formalises the sub-aperture reading of that edge: divide the window into sub-apertures; at fine enough subdivision a
contained pattern spills across sub-aperture edges; the spill read from neighbouring sub-apertures (parallax)
measures the pattern's size and its line term; the floor is read along the focus line (`Telescope.InFocus`), not
at a fixed window. Declarations are in the namespace `MassGap.FocusFloor`.

## 1. The spill (proved, real arithmetic)

A pattern occupying `(x, x + R]` on a line cut into sub-apertures of side `a` crosses
`spill a x R = ⌊(x + R)/a⌋ − ⌊x/a⌋` sub-aperture edges.

* `floor_le_spill`, `spill_le`: `⌊R/a⌋ ≤ spill a x R ≤ ⌊R/a⌋ + 1`. The count is the size in sub-aperture units,
  up to one edge.
* `spill_contained`: a pattern inside one sub-aperture (`0 ≤ x`, `x + R < a`) spills across no edge.
* `spill_pos`: once `0 < a ≤ R` it spills across at least one edge. Subdividing finer than the pattern always
  reaches the pattern.
* `spill_mul_bounds`, `spill_size_read`: `R − a < a · spill a x R ≤ R + a`, and `a · spill a x R → R` as
  `a → 0⁺`. The size of the pattern is read from the spill count at fine subdivision: the pattern's size `R`,
  recovered from the spill count (`R` is the pattern's extent, given to the count).

## 2. The parallax read on the free field (proved, closed form)

The free chain is the one-dimensional scalar field of mass `m`: a toy carrier, not the gauge theory. Its lattice
decay rate is `θ = WindowFreq.rate m` (`2 cosh θ − 2 = m²`, `WindowFreq.two_cosh_rate`).
`green θ r = e^{−θ r}/(2 sinh θ)` is the one-sided formula; it equals the propagator on the infinite chain for
`r ≥ 0`, and the propagator at `−r` is `green θ r`:

* `green_bulk`, `green_bulk_mass`: `(m² + 2) G(r) − G(r − 1) − G(r + 1) = 0` at every `r` (the lattice equation
  for the one-sided formula at every `r`; for the propagator it holds at `|r| ≥ 1`), and `green_source`: `2 cosh θ · G(0) − 2 G(1) = 1` (the source, with `G(−1) = G(1)`).
* `blockCov θ a n = Σ_{i,j < a} G(n a + j − i)`: the covariance of the sums over two sub-apertures of side `a`
  whose left ends are `n a` apart (`n ≥ 1` neighbours and beyond).
* `blockCov_eq`, `blockCov_succ`: `blockCov θ a n = e^{−θ n a} blockCov θ a 0` and
  `blockCov θ a (n + 1) = e^{−θ a} blockCov θ a n`, exact at every `n`.
* `parallaxRead θ a n = log(blockCov θ a n / blockCov θ a (n + 1))`, the read across neighbouring
  sub-apertures. `parallaxRead_eq`: it is `θ a` at every `n`; `parallax_per_length`: per unit length it is `θ`
  at every subdivision `a`. The massive read fixes a length, `1/θ`; `parallax_zoom`: doubling the sub-aperture
  doubles the read, so it is not scale invariant.
* Massless scaling template (not the `m → 0` limit of `green`, which has no limit on the chain): a homogeneous
  kernel `r^{−p}`. `pointRead G a n = log(G(n a)/G((n + 1) a))`; `pointRead_power`: the read is
  `p (log(n + 1) − log n)`, the point read is the same at every sub-aperture side `a`, so no length is fixed, and
  `pointRead_power_per_length`: per unit length it tends to `0` as `a → ∞`.

## 3. The zero-flux line term (the crux, proved on the free field, argued on the tree)

* `spillLine θ a x R = spill a x R · (θ a)`: each crossed edge costs one parallax read. `spillLine_bounds`:
  `θ (R − a) < spillLine ≤ θ (R + a)`; `spillLine_rate`: `spillLine / R → θ` as `R → ∞`, whatever `a`. The
  spill gives a line term in the size of the pattern, `A_zf R`, with `A_zf = θ`, independent of the subdivision.
* `free_reads_agree` (`m > 0`): the parallax line term per unit length and the rate of the free doubling defect
  (`WindowFreq.tendsto_rate_of_defect`, the free analogue of the zero-flux read) are the same number,
  `WindowFreq.rate m`.
* `free_line_iff_vanishing`: at the free field, `0 < rate m` (a positive zero-flux line term) holds exactly when
  the free window read vanishes (`WindowFreq.freeWindow_vanishes_iff`).
* `free_focus_iff`, `massless_no_focus`: with `A = rate m` the focus window exists iff `m > 0` and `R* ≥ 1`; at
  `m = 0` no window is in focus (`Telescope.not_inFocus_of_nonpos_line`).

Plainly, on the crux. The tree has one line read, `Telescope.hopTension` (with `LineSeedsBasin.TensionBelow`),
and it is read on the flux sector, from the relay odds. Telescope's `A = c σ` for a closed contractible loop is
tied to it by argument only. The zero-flux read `CentreSectorSeedN.trivialDefectN` carries no line read of its
own in the tree. The spill does produce one: `A_zf` is the per-length parallax rate, a read of the signal. But
`spillLine_rate` and `free_reads_agree` show what it is: the decorrelation rate of the zero-flux signal, the
zero-flux mass read itself. So a zero-flux line term exists as a read, and its positivity is the zero-flux gap,
not an input that yields it. At the free field the identification is a theorem; on the Wilson read it is argued
(the parallax read of `trivKN` across neighbouring blocks is the transfer decay of the zero-flux sector).

## 4. The inner-edge claim along the focus line, and the verdict (proved)

* `ReadFrom N β w₀`: at every step, the zero-flux defect at windows `2^{w₀ + k}` falls below every positive
  value as `k → ∞`. `FocusFloorRead N A B β := ReadFrom N β (focusWindow (A β) (B β))`: the read started at the
  focus window does not stall. `readFrom_iff`, `focusFloorRead_iff`: for every `w₀`, every measured `A`, `B`,
  this is exactly `ZeroFluxVanishing N β`: the same problem, restated from the focus window. Focus selects where
  the read starts; an eventual read does not see where it starts.
* `ZeroFluxLine N β`: a positive zero-flux line `A_zf` bounds the defect, `≤ C e^{−A_zf 2^w}` eventually.
  `zeroFluxVanishing_of_line`: it gives `ZeroFluxVanishing N β`. `line_strictly_stronger`: on abstract reads
  the converse fails (`1/(w + 1)` vanishes and admits no positive line); on `trivialDefectN` no separation is
  proved.
* Tests. `anchor_focusFloor`: at the strong-coupling anchor (`FloorTension.anchor_flux_zeroFlux`) the focus
  read holds on an interval `[0, β₀)`, `β₀ > 0`, for every `A`, `B`. Free field: §3.

Verdict, plainly. Along the focus line the inner-edge claim in read form (the zero-flux read past the focus
window does not stall) is (ii), equivalent to `ZeroFluxVanishing N β` at every `β` and for every focus read
`A`, `B`: the same problem in focus form. In line form (a positive zero-flux line term) it is (iii), at least as
strong as `ZeroFluxVanishing N β` at each `β`, strictly on abstract reads; for the free defect the corresponding
equivalence is `free_line_iff_vanishing` (`0 < rate m` iff the free window read vanishes). On `trivialDefectN` no
separation is proved. It is not (i) at any `β`: no reduction is available, so no capstone is built. The open count is unchanged: one
input, `ZeroFluxVanishing N β` at every `β ≥ 0` (with the confined flux, `FloorTension.noStall_iff_flux_zeroFlux`).
What the sub-aperture picture adds is the reading of the claim: the zero-flux floor is read as the statement that the
parallax read across neighbouring sub-apertures fixes a length (massive, §2) rather than being scale invariant
(massless, §2). At the free field this fixed length is `1/θ`; that it is the pattern's diffraction edge on the
Wilson read is the argued identification of §3.

DERIVED (module-wide): `0` the signs, the limits and the left end of the anchor interval; `1` one edge (the floor
error), the least spill, the step of the neighbour and the unit of the counterexample `1/(w + 1)`; `2` the
doubling of the window and of the sub-aperture, the `2` in `m² + 2` from the lattice Laplacian `2 − 2 cos`, `2 cosh`, `2 sinh` from the lattice Laplacian `2 − 2 cos` and the
source; `4` the four steps. Counterexample choice: the abstract read `1/(w + 1)` in `line_strictly_stronger`
(labelled there). Inherited tree constants: none beyond those inside the cited declarations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FocusFloor

open Filter Topology Finset
open MassGap.CentreSectorSeedN (trivialDefectN)
open MassGap.LineSeedsVanishing (ZeroFluxVanishing)
open MassGap.Telescope (InFocus focusLen focusWindow)
open MassGap.WindowFreq (rate)

/-! ## 1. The spill -/

/-- **The spill count**: the sub-aperture edges (multiples of `a`) in `(x, x + R]`. DERIVED: no numeral. -/
def spill (a x R : ℝ) : ℤ := ⌊(x + R) / a⌋ - ⌊x / a⌋

/-- The spill is at least the size in sub-aperture units. DERIVED: no numeral. -/
theorem floor_le_spill (a x R : ℝ) : ⌊R / a⌋ ≤ spill a x R := by
  unfold spill
  rw [add_div]
  have := Int.le_floor_add (x / a) (R / a)
  linarith

/-- The spill exceeds the size in sub-aperture units by at most one edge. DERIVED: `1` one edge. -/
theorem spill_le (a x R : ℝ) : spill a x R ≤ ⌊R / a⌋ + 1 := by
  unfold spill
  rw [add_div]
  have := Int.le_floor_add_floor (x / a) (R / a)
  linarith

/-- **A contained pattern does not spill.** DERIVED: `0` the left end; `1` the unit interval of the floor. -/
theorem spill_contained {a x R : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hR : 0 ≤ R) (hin : x + R < a) :
    spill a x R = 0 := by
  unfold spill
  have h1 : ⌊(x + R) / a⌋ = 0 := Int.floor_eq_zero_iff.mpr
    ⟨div_nonneg (by linarith) ha.le, (div_lt_one ha).mpr hin⟩
  have h2 : ⌊x / a⌋ = 0 := Int.floor_eq_zero_iff.mpr
    ⟨div_nonneg hx ha.le, (div_lt_one ha).mpr (by linarith)⟩
  rw [h1, h2, sub_zero]

/-- **Subdivided finer than the pattern, it spills.** DERIVED: `1` the least spill. -/
theorem spill_pos {a x R : ℝ} (ha : 0 < a) (haR : a ≤ R) : 1 ≤ spill a x R := by
  have h : (1 : ℤ) ≤ ⌊R / a⌋ := Int.le_floor.mpr (by
    push_cast
    rw [le_div_iff₀ ha]
    linarith)
  exact h.trans (floor_le_spill a x R)

/-- **The spill reads the size up to one sub-aperture.** DERIVED: `1` one edge. -/
theorem spill_mul_bounds {a x R : ℝ} (ha : 0 < a) :
    R - a < (spill a x R : ℝ) * a ∧ (spill a x R : ℝ) * a ≤ R + a := by
  have h1 : ((⌊R / a⌋ : ℤ) : ℝ) ≤ (spill a x R : ℝ) := by exact_mod_cast floor_le_spill a x R
  have h2 : (spill a x R : ℝ) ≤ ((⌊R / a⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast spill_le a x R
  have h3 : R / a - 1 < ((⌊R / a⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor (R / a)
  have h4 : ((⌊R / a⌋ : ℤ) : ℝ) ≤ R / a := Int.floor_le (R / a)
  have e : R / a * a = R := div_mul_cancel₀ R ha.ne'
  constructor
  · calc R - a = (R / a - 1) * a := by rw [sub_mul, e, one_mul]
      _ < (spill a x R : ℝ) * a := mul_lt_mul_of_pos_right (by linarith) ha
  · calc (spill a x R : ℝ) * a ≤ (R / a + 1) * a := mul_le_mul_of_nonneg_right (by linarith) ha.le
      _ = R + a := by rw [add_mul, e, one_mul]

/-- **The size read**: at fine subdivision the spill count times the sub-aperture is the size.
DERIVED: `0` the limit of the subdivision. -/
theorem spill_size_read (x R : ℝ) :
    Tendsto (fun a : ℝ => (spill a x R : ℝ) * a) (𝓝[>] 0) (𝓝 R) := by
  have hg : Tendsto (fun a : ℝ => R - a) (𝓝[>] 0) (𝓝 R) := by
    have h : Tendsto (fun a : ℝ => R - a) (𝓝 0) (𝓝 (R - 0)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun a : ℝ => R + a) (𝓝[>] 0) (𝓝 R) := by
    have h : Tendsto (fun a : ℝ => R + a) (𝓝 0) (𝓝 (R + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact (spill_mul_bounds (x := x) (R := R) ha).1.le
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact (spill_mul_bounds (x := x) (R := R) ha).2

/-! ## 2. The parallax read on the free field -/

/-- **The free chain propagator** at decay rate `θ`, for `r ≥ 0`. DERIVED: `2` from `2 sinh`. -/
def green (θ r : ℝ) : ℝ := Real.exp (-(θ * r)) / (2 * Real.sinh θ)

/-- **Off the source the propagator solves the lattice equation**: the lattice equation for the one-sided
formula at every `r`; for the propagator it holds at `|r| ≥ 1`. DERIVED: `2` from `2 cosh`; `1` the step of the
neighbour. -/
theorem green_bulk (θ r : ℝ) :
    2 * Real.cosh θ * green θ r - green θ (r - 1) - green θ (r + 1) = 0 := by
  unfold green
  have h1 : Real.exp (-(θ * (r - 1))) = Real.exp (-(θ * r)) * Real.exp θ := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(θ * (r + 1))) = Real.exp (-(θ * r)) * Real.exp (-θ) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2, Real.cosh_eq]
  ring

/-- **The lattice equation at mass `m`**: `(m² + 2) G(r) − G(r − 1) − G(r + 1) = 0` at `θ = rate m`.
DERIVED: `2` the lattice Laplacian `2 − 2 cos`. -/
theorem green_bulk_mass (m r : ℝ) :
    (m ^ 2 + 2) * green (rate m) r - green (rate m) (r - 1) - green (rate m) (r + 1) = 0 := by
  rw [show m ^ 2 + 2 = 2 * Real.cosh (rate m) by linarith [WindowFreq.two_cosh_rate m]]
  exact green_bulk _ r

/-- **The source**: with `G(−1) = G(1)`, `2 cosh θ · G(0) − 2 G(1) = 1`. DERIVED: `2` from `2 cosh`, the two
neighbours; `1` the unit source and the neighbour. -/
theorem green_source {θ : ℝ} (hθ : 0 < θ) : 2 * Real.cosh θ * green θ 0 - 2 * green θ 1 = 1 := by
  have hs : Real.sinh θ ≠ 0 := (Real.sinh_pos_iff.mpr hθ).ne'
  have h2s : 2 * Real.sinh θ ≠ 0 := mul_ne_zero two_ne_zero hs
  have key : 2 * Real.cosh θ - 2 * Real.exp (-θ) = 2 * Real.sinh θ := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  calc 2 * Real.cosh θ * green θ 0 - 2 * green θ 1
      = (2 * Real.cosh θ - 2 * Real.exp (-θ)) / (2 * Real.sinh θ) := by
        unfold green
        rw [mul_zero, neg_zero, Real.exp_zero, mul_one]
        ring
    _ = 1 := by rw [key, div_self h2s]

/-- The propagator is positive at positive rate. DERIVED: `0` the sign; `2` from `2 sinh`. -/
theorem green_pos {θ : ℝ} (hθ : 0 < θ) (r : ℝ) : 0 < green θ r :=
  div_pos (Real.exp_pos _) (mul_pos two_pos (Real.sinh_pos_iff.mpr hθ))

/-- **The block covariance**: sums over two sub-apertures of side `a`, left ends `n a` apart.
For neighbours `n ≥ 1` this is the covariance of the two block sums. At `n = 0` it is the formal one-sided sum,
used only as the normalizer in `blockCov_eq`.
DERIVED: no numeral. -/
def blockCov (θ : ℝ) (a n : ℕ) : ℝ :=
  ∑ i ∈ range a, ∑ j ∈ range a, green θ ((n : ℝ) * a + j - i)

/-- **The block covariance in closed form**: `e^{−θ n a}` times the self-block sum. DERIVED: `0` the self block. -/
theorem blockCov_eq (θ : ℝ) (a n : ℕ) :
    blockCov θ a n = Real.exp (-(θ * ((n : ℝ) * a))) * blockCov θ a 0 := by
  unfold blockCov
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold green
  have e : -(θ * ((n : ℝ) * a + j - i)) = -(θ * ((n : ℝ) * a)) + -(θ * (((0 : ℕ) : ℝ) * a + j - i)) := by
    push_cast; ring
  rw [e, Real.exp_add, mul_div_assoc]

/-- **One neighbour further, one factor `e^{−θ a}`.** DERIVED: `1` the step of the neighbour. -/
theorem blockCov_succ (θ : ℝ) (a n : ℕ) :
    blockCov θ a (n + 1) = Real.exp (-(θ * (a : ℝ))) * blockCov θ a n := by
  have e : -(θ * (((n + 1 : ℕ) : ℝ) * a)) = -(θ * (a : ℝ)) + -(θ * ((n : ℝ) * a)) := by
    push_cast; ring
  rw [blockCov_eq θ a (n + 1), blockCov_eq θ a n, e, Real.exp_add]
  ring

/-- The block covariance is positive. DERIVED: `0` the sign. -/
theorem blockCov_pos {θ : ℝ} (hθ : 0 < θ) {a : ℕ} (ha : 0 < a) (n : ℕ) : 0 < blockCov θ a n :=
  Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => green_pos hθ _)
    (Finset.nonempty_range_iff.mpr ha.ne')) (Finset.nonempty_range_iff.mpr ha.ne')

/-- **The parallax read** across neighbouring sub-apertures. DERIVED: `1` the step of the neighbour. -/
def parallaxRead (θ : ℝ) (a n : ℕ) : ℝ := Real.log (blockCov θ a n / blockCov θ a (n + 1))

/-- **The parallax read is `θ a`, exactly, at every separation** (physical for `n ≥ 1`). DERIVED: `1` the ratio. -/
theorem parallaxRead_eq {θ : ℝ} (hθ : 0 < θ) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    parallaxRead θ a n = θ * a := by
  have hc : blockCov θ a n ≠ 0 := (blockCov_pos hθ ha n).ne'
  unfold parallaxRead
  rw [blockCov_succ, mul_comm (Real.exp _) (blockCov θ a n), ← div_div, div_self hc, one_div,
    ← Real.exp_neg, Real.log_exp, neg_neg]

/-- **Per unit length the parallax read is `θ` at every subdivision**: the massive read fixes the length `1/θ`.
DERIVED: no numeral. -/
theorem parallax_per_length {θ : ℝ} (hθ : 0 < θ) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    parallaxRead θ a n / a = θ := by
  rw [parallaxRead_eq hθ ha n, mul_div_assoc, div_self (Nat.cast_pos.mpr ha).ne', mul_one]

/-- **The massive read is not scale invariant**: doubling the sub-aperture doubles the read.
DERIVED: `2` the doubling. -/
theorem parallax_zoom {θ : ℝ} (hθ : 0 < θ) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    parallaxRead θ (2 * a) n = 2 * parallaxRead θ a n := by
  rw [parallaxRead_eq hθ (by omega) n, parallaxRead_eq hθ ha n]
  push_cast; ring

/-- **The point read** at sub-aperture spacing `a`: one sample per sub-aperture. DERIVED: `1` the neighbour. -/
def pointRead (G : ℝ → ℝ) (a : ℝ) (n : ℕ) : ℝ := Real.log (G ((n : ℝ) * a) / G (((n : ℝ) + 1) * a))

/-- **Massless (power-law kernel): the read is the same at every sub-aperture side.** No length is fixed.
DERIVED: `0` the signs; `1` the neighbour. -/
theorem pointRead_power {p a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    pointRead (fun r => r ^ (-p)) a n = p * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : 0 < (n : ℝ) * a := mul_pos hn' ha
  have hy : 0 < ((n : ℝ) + 1) * a := mul_pos (by linarith) ha
  unfold pointRead
  rw [Real.log_div (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hy _).ne',
    Real.log_rpow hx, Real.log_rpow hy, Real.log_mul hn'.ne' ha.ne', Real.log_mul (by linarith) ha.ne']
  ring

/-- **Massless: per unit length the read tends to `0` at coarse subdivision.** DERIVED: `0` the limit. -/
theorem pointRead_power_per_length {p : ℝ} {n : ℕ} (hn : 0 < n) :
    Tendsto (fun a : ℝ => pointRead (fun r => r ^ (-p)) a n / a) atTop (𝓝 0) := by
  have h : Tendsto (fun a : ℝ => p * (Real.log ((n : ℝ) + 1) - Real.log n) / a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  rw [pointRead_power ha hn]

/-! ## 3. The zero-flux line term -/

/-- **The spill line**: each crossed edge costs one parallax read `θ a`. Here `θ` is supplied, not taken from
`parallaxRead`; `spillLine_rate` is then a computation. DERIVED: no numeral. -/
def spillLine (θ a x R : ℝ) : ℝ := (spill a x R : ℝ) * (θ * a)

/-- **The spill line is `θ R` up to one sub-aperture.** DERIVED: no numeral. -/
theorem spillLine_bounds {θ a x R : ℝ} (hθ : 0 < θ) (ha : 0 < a) :
    θ * (R - a) < spillLine θ a x R ∧ spillLine θ a x R ≤ θ * (R + a) := by
  obtain ⟨h1, h2⟩ := spill_mul_bounds (x := x) (R := R) ha
  unfold spillLine
  constructor
  · nlinarith
  · nlinarith

/-- **The zero-flux line term the spill gives is `θ`, whatever the subdivision.** DERIVED: `0` the limit. -/
theorem spillLine_rate {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R : ℝ => spillLine θ a x R / R) atTop (𝓝 θ) := by
  have hq : Tendsto (fun R : ℝ => θ * a / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hg : Tendsto (fun R : ℝ => θ - θ * a / R) atTop (𝓝 θ) := by
    simpa using (tendsto_const_nhds (x := θ)).sub hq
  have hh : Tendsto (fun R : ℝ => θ + θ * a / R) atTop (𝓝 θ) := by
    simpa using (tendsto_const_nhds (x := θ)).add hq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have h := (spillLine_bounds (x := x) (R := R) hθ ha).1
    have e : θ - θ * a / R = θ * (R - a) / R := by
      field_simp
    rw [e]
    exact (div_le_div_iff_of_pos_right hR).mpr h.le
  · filter_upwards [eventually_gt_atTop 0] with R hR
    have h := (spillLine_bounds (x := x) (R := R) hθ ha).2
    have e : θ + θ * a / R = θ * (R + a) / R := by
      field_simp
    rw [e]
    exact (div_le_div_iff_of_pos_right hR).mpr h

/-- **Two reads of the free zero-flux line agree**: the parallax line term per unit length and the rate of the
free doubling defect are both `rate m`. DERIVED: `0` the signs. -/
theorem free_reads_agree {m : ℝ} (hm : 0 < m) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    parallaxRead (rate m) a n / a = rate m ∧
      Tendsto (fun L : ℕ => -Real.log (WindowFreq.defect m L) / L) atTop (𝓝 (rate m)) :=
  ⟨parallax_per_length (WindowFreq.rate_pos_iff.mpr hm) ha n, WindowFreq.tendsto_rate_of_defect hm⟩

/-- **At the free field a positive zero-flux line is the vanishing read.** This is `rate_pos_iff` composed with the vanishing theorem: `m > 0` restated, not an
independent identification. DERIVED: `0` the signs and the limit. -/
theorem free_line_iff_vanishing {m : ℝ} (hm : 0 ≤ m) :
    0 < rate m ↔ Tendsto (WindowFreq.freeWindow m) atTop (𝓝 0) :=
  WindowFreq.rate_pos_iff.trans (WindowFreq.freeWindow_vanishes_iff hm).symm

/-- **Free field: focus on the zero-flux line exists iff the field is massive and `R* ≥ 1`.**
DERIVED: `0` the signs; `1` the lattice spacing. -/
theorem free_focus_iff {m B : ℝ} (hB : 0 < B) :
    (∃ w : ℕ, InFocus (rate m) B w) ↔ 0 < m ∧ 1 ≤ focusLen (rate m) B := by
  rw [Telescope.inFocus_iff_exists, WindowFreq.rate_pos_iff]
  exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hB, h3⟩⟩

/-- **Massless: no zero-flux line, no focus.** DERIVED: `0` the mass. -/
theorem massless_no_focus (B : ℝ) (w : ℕ) : ¬ InFocus (rate 0) B w :=
  Telescope.not_inFocus_of_nonpos_line (by simp [rate])

/-! ## 4. The inner-edge claim along the focus line -/

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The zero-flux read started at window `w₀`**: at every step the defect at `2^{w₀ + k}` falls below every
positive value as `k → ∞`. DERIVED: `0` the sign of `ε`; `2` the dyadic side; `4` the steps. -/
def ReadFrom (β : ℝ) (w₀ : ℕ) : Prop :=
  ∀ i : Fin 4, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, trivialDefectN N β (2 ^ (w₀ + k)) i ≤ ε

variable (N) in
/-- **The inner-edge claim in read form**: the zero-flux read past the focus window does not stall.
DERIVED: no numeral. -/
def FocusFloorRead (A B : ℝ → ℝ) (β : ℝ) : Prop := ReadFrom N β (focusWindow (A β) (B β))

/-- **An eventual read does not see where it starts.** DERIVED: no numeral. -/
theorem readFrom_iff {β : ℝ} (w₀ : ℕ) : ReadFrom N β w₀ ↔ ZeroFluxVanishing N β := by
  constructor
  · intro h i ε hε
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (h i ε hε)
    refine Filter.eventually_atTop.mpr ⟨w₀ + K, fun w hw => ?_⟩
    have := hK (w - w₀) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  · intro h i ε hε
    obtain ⟨W, hW⟩ := Filter.eventually_atTop.mp (h i ε hε)
    exact Filter.eventually_atTop.mpr ⟨W, fun k hk => hW _ (by omega)⟩

/-- **Verdict (ii): the focus read is `ZeroFluxVanishing`**, at every `β` and every measured `A`, `B`.
DERIVED: no numeral. -/
theorem focusFloorRead_iff (A B : ℝ → ℝ) {β : ℝ} : FocusFloorRead N A B β ↔ ZeroFluxVanishing N β :=
  readFrom_iff _

variable (N) in
/-- **The inner-edge claim in line form**: a positive zero-flux line `A_zf` bounds the defect.
DERIVED: `0` the sign; `2` the dyadic side; `4` the steps. -/
def ZeroFluxLine (β : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, ∀ i : Fin 4, ∀ᶠ w in atTop,
    trivialDefectN N β (2 ^ w) i ≤ C * Real.exp (-(A * (2 : ℝ) ^ w))

/-- **A positive zero-flux line gives the vanishing read.** DERIVED: `0` the limit; `1` and `2` the base of the
dyadic side. -/
theorem zeroFluxVanishing_of_line {β : ℝ} (h : ZeroFluxLine N β) : ZeroFluxVanishing N β := by
  obtain ⟨A, hA, C, hC⟩ := h
  have hu : Tendsto (fun w : ℕ => C * Real.exp (-(A * (2 : ℝ) ^ w))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop hA)
    simpa using he.const_mul C
  intro i ε hε
  filter_upwards [hC i, hu.eventually (gt_mem_nhds hε)] with w h1 h2
  linarith

/-- **On abstract reads the line form is strictly stronger.** Counterexample choice: the read `1/(w + 1)`
vanishes and admits no positive line `C e^{−A 2^w}`. DERIVED: `0` the limit; `1` the unit of the
counterexample; `2` the dyadic side. -/
theorem line_strictly_stronger :
    Tendsto (fun w : ℕ => 1 / ((w : ℝ) + 1)) atTop (𝓝 0) ∧
      ¬ ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, ∀ᶠ w : ℕ in atTop,
        1 / ((w : ℝ) + 1) ≤ C * Real.exp (-(A * (2 : ℝ) ^ w)) := by
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  rintro ⟨A, hA, C, h⟩
  have hx : Tendsto (fun w : ℕ => A * (2 : ℝ) ^ w) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop hA
  have hy : Tendsto (fun w : ℕ => (A * (2 : ℝ) ^ w) * Real.exp (-(A * (2 : ℝ) ^ w))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
    simpa [Function.comp_def] using this
  have hz : Tendsto (fun w : ℕ => |C| / A * ((A * (2 : ℝ) ^ w) * Real.exp (-(A * (2 : ℝ) ^ w))))
      atTop (𝓝 0) := by simpa using hy.const_mul (|C| / A)
  obtain ⟨w, hw1, hw2⟩ := (h.and (hz.eventually (gt_mem_nhds one_pos))).exists
  set e := Real.exp (-(A * (2 : ℝ) ^ w)) with he_def
  have he : 0 < e := Real.exp_pos _
  have hP : (w : ℝ) + 1 ≤ (2 : ℝ) ^ w := by
    have := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) w
    norm_num at this
    linarith
  have hw0 : (0 : ℝ) < (w : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hw0] at hw1
  have hrw : |C| / A * ((A * (2 : ℝ) ^ w) * e) = |C| * e * (2 : ℝ) ^ w := by
    field_simp
  rw [hrw] at hw2
  have hb : C * e * ((w : ℝ) + 1) ≤ |C| * e * (2 : ℝ) ^ w := by
    have h1 : C * e ≤ |C| * e := mul_le_mul_of_nonneg_right (le_abs_self C) he.le
    have h2 : 0 ≤ |C| * e := mul_nonneg (abs_nonneg C) he.le
    calc C * e * ((w : ℝ) + 1) ≤ |C| * e * ((w : ℝ) + 1) := mul_le_mul_of_nonneg_right h1 hw0.le
      _ ≤ |C| * e * (2 : ℝ) ^ w := mul_le_mul_of_nonneg_left hP h2
  linarith

/-- **Strong-coupling anchor**: on an interval `[0, β₀)`, `β₀ > 0`, the focus read holds for every `A`, `B`.
DERIVED: `0` the left end. -/
theorem anchor_focusFloor :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → ∀ A B : ℝ → ℝ, FocusFloorRead N A B β := by
  obtain ⟨β₀, hβ₀, h⟩ := FloorTension.anchor_flux_zeroFlux (N := N)
  exact ⟨β₀, hβ₀, fun β hβ hlt A B => (focusFloorRead_iff A B).mpr (h β hβ hlt).2⟩

end MassGap.FocusFloor

#print axioms MassGap.FocusFloor.floor_le_spill
#print axioms MassGap.FocusFloor.spill_le
#print axioms MassGap.FocusFloor.spill_contained
#print axioms MassGap.FocusFloor.spill_pos
#print axioms MassGap.FocusFloor.spill_mul_bounds
#print axioms MassGap.FocusFloor.spill_size_read
#print axioms MassGap.FocusFloor.green_bulk
#print axioms MassGap.FocusFloor.green_bulk_mass
#print axioms MassGap.FocusFloor.green_source
#print axioms MassGap.FocusFloor.green_pos
#print axioms MassGap.FocusFloor.blockCov_eq
#print axioms MassGap.FocusFloor.blockCov_succ
#print axioms MassGap.FocusFloor.blockCov_pos
#print axioms MassGap.FocusFloor.parallaxRead_eq
#print axioms MassGap.FocusFloor.parallax_per_length
#print axioms MassGap.FocusFloor.parallax_zoom
#print axioms MassGap.FocusFloor.pointRead_power
#print axioms MassGap.FocusFloor.pointRead_power_per_length
#print axioms MassGap.FocusFloor.spillLine_bounds
#print axioms MassGap.FocusFloor.spillLine_rate
#print axioms MassGap.FocusFloor.free_reads_agree
#print axioms MassGap.FocusFloor.free_line_iff_vanishing
#print axioms MassGap.FocusFloor.free_focus_iff
#print axioms MassGap.FocusFloor.massless_no_focus
#print axioms MassGap.FocusFloor.readFrom_iff
#print axioms MassGap.FocusFloor.focusFloorRead_iff
#print axioms MassGap.FocusFloor.zeroFluxVanishing_of_line
#print axioms MassGap.FocusFloor.line_strictly_stronger
#print axioms MassGap.FocusFloor.anchor_focusFloor
