import Mathlib
import MassGap.EffectiveCoupling
import MassGap.MeasuredSpacing

/-!
# MassGap.CouplingTower — the line of constant window coupling, and what is left of the gap after it

`β → ∞` is the critical point in lattice units. This module holds the theory at the observer's scale fixed
along the approach: at step `k` it takes the coupling `β_k` at which the window reading of the torus of side
`2^{w_k}` (the window, of fixed physical size) equals one value `u₀`. The theory read at the window is then the
same theory at every step (the step-scaling picture of a line of constant physics), and `β → ∞` only adds
structure below the window. What is left splits into one statement at the single window coupling `u₀` (the
infrared input) and one convergence statement along the tower (the ultraviolet input). Declarations are in the
namespace `MassGap.CouplingTower`.

## 1. The window coupling (defined; regularity proved)

`windowCoupling N β w = defectW N β (2^w) = 16 log ZR((2^w)⁴) − log ZR((2^{w+1})⁴)`: the doubling defect of the
periodic Wilson torus of side `2^w`, a finite-volume read at one coupling. It is the effective coupling of
`EffectiveCoupling` at side `2^w`, oriented as a stiffness: it is `0` at `β = 0` at every side
(`windowCoupling_zero`), and its basin `{g ≤ 1/1000}` is the basin of the trivial (ultralocal, confined) fixed
point.

* `continuous_windowCoupling`, `hasDerivAt_windowCoupling`: continuous in `β`, with derivative
  `⟨S⟩_{2^{w+1}} − 16 ⟨S⟩_{2^w}` (`EffectiveCoupling.hasDerivAt_defectW`).
* `windowCoupling_nonneg`: `0 ≤ g` at `β ≥ 0`, `w ≥ 1`.
* `windowCoupling_succ_le`, `basin_contracts`: in the basin one doubling squares the reading,
  `g(w+1) ≤ 250 g(w)² ≤ g(w)/4` (`DoublingSharp.rec_sharp`). `windowCoupling_decay`: `g(w+i) ≤ 4^{−i}/1000`.
  So past the basin's edge every further doubling contracts toward the trivial fixed point: this is where
  "past the crossover" sits in this read.

## 2. The coupling tower (defined; existence proved from two named ends)

`CouplingTower N u₀ βs ws`: `βs → ∞`, `ws → ∞`, and eventually `ws k ≥ 1`, `βs k ≥ 0`,
`windowCoupling N (βs k) (ws k) = u₀` exactly.

* (S) `StrongEnd N` (assumed): frequently in `β`, the window coupling vanishes along the windows,
  `g β w → 0` as `w → ∞`: the confined end at arbitrarily large `β`, with no threshold. `strongEnd_iff_seed`
  reads it in the basin form used inside proofs (some window in the basin of `DoublingSharp`). It follows from
  `DeltaLengthTower.SeedExistsPow` (A₂) (`strongEnd_of_seedExistsPow`). At `β = 0` it holds at every side
  (`windowCoupling_zero`); at large `β` it is open.
* (W) `WeakEnd N u₀` (assumed): on every fixed window `2^w`, frequently in `β`, `g > u₀`: on a fixed
  number of lattice sites the theory leaves the confined basin as `β → ∞` (asymptotic freedom on a small
  box). For `u₀ ≤ 1/1000` it follows from `DeltaLengthTower.DeltaLengthUnbounded` (B₂)
  (`weakEnd_of_deltaLengthUnbounded`). No module imported here proves (B₂); it is a named input.
* `exists_couplingTower` (proved): `0 < u₀`, (S) and (W) give a tower with `ws = id`. At step `b` the
  crossing starts from a seeded coupling `a ≥ J`, where the reading at `2^b` is below `u₀`
  (`eventually_le_of_seed`, from the decay), and ends at a coupling above `a` where (W) puts it above `u₀`;
  intermediate values give `g = u₀` exactly, at `β ≥ J`. `exists_tendsto_of_forall_eventually` picks `J → ∞`
  with `b` (`Nat.findGreatest`). No local boundedness in `β` and no seed on a whole ray is used.
* `strongEnd_iff_exists_couplingTower` (proved): for `0 < u₀ ≤ 1/1000` and (W), (S) holds exactly when a
  tower with `ws = id` exists. So the tower is (S) together with (W), and nothing else.

## 3. The two inputs

**(IR) `ConfinedAt N u₀ m`** (assumed): at every `β ≥ 0` and every window `w ≥ 1` with `g(β, w) = u₀`, the
measured tensor mass of the periodic state at `β` is at least `m` in window units:
`ofReal (m / 2^w) ≤ mU β`. One window coupling, no limit in `β`, no limit in the side, no spacing.
`mU β = measMassOf (periodicState β) tensorEnergy` is read in the infinite-volume periodic state at that one
`β` (a thermodynamic limit point at fixed coupling), not in any continuum limit.

**(UV) `UVConverges N βs ws μ`** (assumed): along the tower the window reading of the measured mass
converges: eventually `mU (βs k) ≠ ⊤`, and `2^{ws k} · m′(βs k) → μ ∈ ℝ`. This is the ratio window/`ξ` at
fixed window coupling, the step-scaling form of "the map from the lattice to the window converges": a Cauchy
sequence of window readings, so the lattice artifacts at the window go to `0`. It reads no `aRun` and no
coupling other than the tower's.

## 4. What they give (proved)

* `windowGap`: at `0 ≤ β`, `w ≥ 1`, `g(β, w) ≤ 1/1000` the periodic transfer has a gap at rate `r` with
  `−log r = log 2 / 2^w` exactly, and the periodic Clay gap holds (`DoublingClay2.dyadicTorusDecay` at side
  `2^w`), at `N ≥ 2`. This is (IR) in the transfer-gap form, proved for every `u₀ ≤ 1/1000`.
* `confinedAt_of_gapReadsTensor`: with the link `GapReadsTensor` (below) it is (IR) at `m = log 2`, for every
  `u₀ ≤ 1/1000`.
* `le_window_mass`, `le_of_confinedAt_uv`: along a tower, (IR) gives `m ≤ 2^{ws k} m′(βs k)` eventually, so
  (IR) and (UV) give `m ≤ μ`. A massless window (`μ = 0`) is incompatible with (IR) at `m > 0`.
* `measTowerG_of_confinedAt_uv`: a tower with `ws = id`, (IR) at `m > 0` and (UV) give
  `MeasuredTower.MeasTowerG (SU N) βs`, with unit `c = 4μ/(3 aRunG 1)` (`2^k m′ ∈ (2μ/3, 4μ/3)` eventually).
  The coupling tower is then a measured tower: the tower that `ClayStatementG.ClayStatementOf` selects its
  states by.
* `stepGap_of_seeds`, `stepGap_along`: wherever the window `2^k` is in the basin at `βs k`, the per-step gap
  along `schedAlongG (SU N) βs` holds with `−log r / a_k = 2 log 2 / aRunG 1` exactly. Along a tower at
  `u₀ ≤ 1/1000` this needs neither input.
* `flowClusterAbs_along`: `TimeGroupG.FlowClusterAbsG (schedAlongG (SU N) βs) Φ 0 r 1` along a tower at
  `u₀ ≤ 1/1000` (`MeasuredSpacing.flowClusterAbs_of_stepGap`). `observerGap_along`: the observer's
  transfer at every step `m₀` is gapped (`MeasuredSpacing.flowGapAt_of_stepGap`), the gap input `hg` of
  `ClayGFinal.observerOSDataSLinkedGN` at the tower's schedule, in time direction `τ = 0`.
* `measuredTower_of_ends`: (S), (W), `0 < u₀ ≤ 1/1000`, `GapReadsTensor` and (UV) along every tower give
  couplings that are at once a coupling tower and a measured tower, with the per-step gap along their
  schedule.

## 5. The missing links (named, not proved)

* `GapReadsTensor N` (assumed where used): a periodic Clay gap at rate `r` gives the tensor reading of the
  same periodic state decay at rate `−log r`. The Clay gap is a gap of the transfer in direction `0`; the
  measured mass reads `‖z‖∞` in all four directions, so the link needs the gap in every direction (lattice
  symmetry of the periodic state) and the passage from the transfer's spectrum to the correlation of the
  tensor reading. Argued true; not in the tree. It is the only step between the proved `windowGap` and (IR)
  at `u₀ ≤ 1/1000`.
* From the tower to every coupling. `WDeltaRun.RunSeed`, `SubstrateFluxRead.SectorSeedMeasured` and
  `SliceTransferGap.TransferGapMeasured` are `∀ᶠ β` statements. A tower gives the countable set `βs k`. The
  window reading at a fixed side is not known to be monotone in `β`, so nothing here interpolates between
  tower couplings. The root statement
  `ClayStatementOf` reads only a tower (`MeasTowerG`) and its schedule, so this link is not on its path;
  it is on the path of every capstone stated with `∀ᶠ β`.
* `TransferGapMeasured` asks spectral data of the slice transfer `kT` on every power-of-two side with
  `D ≤ n m′`, with an anchor; the periodic Clay gap is a statement about the infinite-volume transfer, and no
  theorem of the tree goes from it to eigen-data of `kT` on a finite slice.

## 6. Where `u₀` sits (the supercritical rule)

`0 < u₀ ≤ 1/1000`: inside the basin of the trivial fixed point of the doubling, where every further doubling
contracts the reading by at least `4` (`basin_contracts`). Seen from the ultraviolet the window is past the
crossover: the crossover is the passage of the reading from the weak-coupling values on small boxes (above
`1/1000`, by (W)) into the basin. `WindowRelay.PastPeak` (no rise of the coarse plaquette susceptibility of
`SU(2)` from step `k` on) is a different read of the same crossing; no theorem connects it to this basin, and
no statement here uses it; `Telescope.blur_lt_line_iff` places the
focal length `R*` at the crossover of the shell cost, and `Telescope.strongEnd_of_focus` gives (S) from focus and
`Telescope.LineSeedsBasin`.

## 7. Tests

* `β = 0`: `windowCoupling_zero`; `ne_zero_of_windowCoupling_eq`: a coupling with window reading `u₀ ≠ 0` is not
  `0`, so no tower step at `u₀ > 0` sits at the ultralocal point. (IR) itself holds at any `β` where
  `mU β = ⊤` (finite-range tensor correlations, as at `β = 0`); along a tower this case does not arise at a
  step. `stepGap_at_zero`, `flowClusterAbs_at_zero`:
  the per-step gap and `FlowClusterAbsG` hold along the schedule with every state at `β = 0`. The gap clause on
  a schedule alone is met by the ultralocal theory; along a tower it is the condition `g = u₀ > 0` with
  `βs → ∞` that excludes it, and in the measured read (UV) excludes it (at `β = 0` the window reading of the
  measured mass is not finite and convergent; argued, `m′(0)` is not computed here).
* Strong coupling: (IR) in the transfer-gap form is a theorem for every `u₀ ≤ 1/1000` (`windowGap`).
* Vacuity. (IR) holds at every `m ≤ 0`, since then `ofReal (m / 2^w) = 0`; every consumer here takes
  `m > 0`. `confinedAt_of_neg`: (IR) holds at every `u₀ < 0`, vacuously (`windowCoupling_nonneg`);
  `not_couplingTower_of_neg`: no tower exists there. For `u₀` above every value the reading takes, (IR) is
  again vacuous and (W) fails. So a vacuous (IR) is caught by existence. In the basin (IR) is not vacuous but
  is close to proved (`windowGap`, one link). Its content there moves into the tower's existence (S) and into
  (UV): (UV) with (IR) is what makes the window a bounded number of correlation lengths.
* Restatement against reduction. `strongEnd_iff_exists_couplingTower`: the tower is (S) and (W) restated, at
  `u₀ ≤ 1/1000`. Proved: on a tower, (UV) at `μ = 0` and (IR) at `m > 0` are incompatible
  (`le_of_confinedAt_uv`, `not_confinedAt_of_massless`). Argued, with no witness built: a massless window
  (`μ = 0`) satisfies (UV) and violates (IR), so (UV) does not contain (IR); a tower whose `2^k m′` diverges
  satisfies (IR) and violates (UV), so (IR) does not contain (UV). (UV) is ultraviolet in the step-scaling
  sense (fixed renormalized window coupling, lattice artifacts at the window); because the window is past the crossover,
  its proof needs control of the crossing at fixed physical size, which asymptotic freedom alone does not
  give.
* Free field. `exists_towerOf_const_iff`: for a reading that does not run (`g ≡ g₀` at every coupling and
  window, a scale-free fixed point, `EffectiveCoupling.meanAction_run`) a tower exists exactly at `u₀ = g₀`.
  At `g₀ = 0` (the free coupling in the usual orientation) no tower pins `u₀ > 0`. The theorem is about an
  abstract constant reading, not about `windowCoupling`; its reading for the gauge theory is argued: in this
  read's orientation the free value is a non-seed value (above `1/1000`, the regime of (W)), so it is outside
  `(0, 1/1000]`, and a tower at `u₀ = g₀` with a massless window (`μ = 0`) is ruled out for (IR) at `m > 0` by
  `not_confinedAt_of_massless`.
* Scales: the window coupling is a finite-torus read; (IR) and (UV) read the measured mass `m′` and the window
  index. `aRunG (SU N) 1` enters only through the dyadic spacing `dySpacingG`, as a unit of length.

## 8. Comparison with `BalabanUV.BalabanShape`

`BalabanShape lad steps μ β₀ nrm b₀ logL gmax` asks, on a ladder of block-spin systems, one-loop running of the
block couplings `gsq j ≤ gbar ≤ gmax` from the cutoff for `steps n` steps, with small-field effective actions
and large-field suppression at every step. It controls the scales between the cutoff and the scale where the
running coupling is still `≤ gbar`: the fine structure below the crossover. (UV) asks the convergence of the
window reading at a window past the crossover. Neither implies the other as stated: `BalabanShape` says nothing
at the window, and (UV) says nothing about block-spin effective actions. A proof of (UV) through `BalabanShape`
needs, in addition, the passage from `gbar` to the window coupling `u₀` at fixed physical size.

## Parameters

| symbol | meaning | where |
|---|---|---|
| `N` | rank of `SU(N)`, `N ≥ 2` where a gap is read | all |
| `β` | bare coupling (`β = N/g₀²` in the tree's normalization) | all |
| `w`, `ws k` | window index; the window is the torus of side `2^w` | §1–§3 |
| `u₀` | the fixed window coupling, `0 < u₀ ≤ 1/1000` in §4 | §2–§4 |
| `βs k` | the tower's couplings, `→ ∞` | §2–§4 |
| `m` | (IR) mass in window units | §3 |
| `μ` | (UV) limit of `2^{ws k} m′(βs k)` | §3 |
| `c = 4μ/(3 aRunG 1)` | unit of the measured band | §4 |
| `2 log 2 / aRunG 1` | per-step gap in units of `a_k` | §4 |

DERIVED (module-wide): `16 = 2⁴` and `2` the doubling; `1/1000` the sharp seed of `DoublingSharp`; `250` its
squaring constant; `4 = 1/(250 · 1/1000)` the contraction; `1/2` the decay ratio of `dyadicTorusDecay`, so
`log 2` the rate; `1` the least window index; `0` the plane, the time axis, the signs and the ultralocal
coupling; `2/3`, `4/3` the band around `μ`, with `4/3 = 2 · 2/3` the band's ratio.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.CouplingTower

open Filter Topology
open scoped ENNReal NNReal
open MassGap MassGap.ZoomSelfScale MassGap.MeasuredTower MassGap.MeasuredSpacing MassGap.ClayTreeG
  MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG MassGap.FlowClusterG

variable {N : ℕ}

/-! ## 1. The window coupling -/

/-- **The window coupling**: the doubling defect of the torus of side `2^w` at coupling `β`.
DERIVED: `2` the doubling. -/
def windowCoupling (N : ℕ) (β : ℝ) (w : ℕ) : ℝ := defectW N β (2 ^ w)

/-- DERIVED: `2` the doubling. -/
theorem continuous_windowCoupling (hN : N ≠ 0) (w : ℕ) : Continuous fun β => windowCoupling N β w :=
  DeltaLengthTower.continuous_defectW hN (2 ^ w)

/-- **The β-derivative of the window coupling** is the finite-size part of the mean action.
DERIVED: `16 = 2⁴`, `2` the doubling. -/
theorem hasDerivAt_windowCoupling (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    HasDerivAt (fun x => windowCoupling N x w)
      (EffectiveCoupling.meanAction N (fun _ => 2 * 2 ^ w) β
        - 16 * EffectiveCoupling.meanAction N (fun _ => 2 ^ w) β) β :=
  EffectiveCoupling.hasDerivAt_defectW hN (2 ^ w) β

/-- **The window coupling is `0` at `β = 0`**, at every window. DERIVED: `0` the ultralocal coupling. -/
theorem windowCoupling_zero (N w : ℕ) : windowCoupling N 0 w = 0 :=
  SeedZeroCoupling.defect_at_zero N (2 ^ w)

/-- DERIVED: `1` the least window index; `0` the sign. -/
theorem windowCoupling_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    0 ≤ windowCoupling N β w := by
  have hp := DoublingWilson.positive hN hβ (DeltaLengthTower.two_le_two_pow hw)
    (DeltaLengthTower.even_two_pow hw)
  have h := DoublingRecursion.Δ_nonneg hp (DoublingRecursion.corner 0)
  rw [DoublingWilson.Δ_corner0] at h
  exact h

/-- **One doubling squares the reading in the basin**: `g(w+1) ≤ 250 g(w)²`.
DERIVED: `1/1000`, `250` the sharp seed's; `1` the least index and the step. -/
theorem windowCoupling_succ_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (h : windowCoupling N β w ≤ 1 / 1000) :
    windowCoupling N β (w + 1) ≤ 250 * windowCoupling N β w ^ 2 := by
  have hn := DeltaLengthTower.two_le_two_pow hw
  have he := DeltaLengthTower.even_two_pow hw
  have hx := DoublingSharp.positiveS_of_facts (DoublingWilson.factRep hN hβ hn he)
  have e0 : DoublingRecursion.Δ (DoublingWilson.xW N (2 ^ w) β) (DoublingRecursion.corner 0)
      = windowCoupling N β w := DoublingWilson.Δ_corner0 _
  have h0 : DoublingRecursion.Δ (DoublingWilson.xW N (2 ^ w) β) (DoublingRecursion.corner 0)
      ≤ 1 / 1000 := by
    rw [e0]; exact h
  have hr := DoublingSharp.rec_sharp hx (DoublingRecursion.corner 0) h0
  have e1 : DoublingRecursion.Δ (DoublingWilson.xW N (2 ^ w) β)
      (DoublingRecursion.corner 0 + DoublingRecursion.one) = windowCoupling N β (w + 1) := by
    rw [← DoublingRecursion.corner_succ, WDeltaRun.Δ_corner]
    unfold windowCoupling
    congr 1
    ring
  rw [e1, e0] at hr
  exact hr

/-- **The basin contracts**: in the basin one doubling divides the reading by at least `4`.
DERIVED: `4 = 1/(250 · 1/1000)`; `1` the least index and the step. -/
theorem basin_contracts (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (h : windowCoupling N β w ≤ 1 / 1000) :
    windowCoupling N β (w + 1) ≤ windowCoupling N β w / 4 := by
  have hs := windowCoupling_succ_le hN hβ hw h
  have hnn := windowCoupling_nonneg hN hβ hw
  nlinarith [mul_le_mul_of_nonneg_left h hnn]

/-- **Decay in the basin**: `g(w+i) ≤ 4^{−i}/1000`. DERIVED: `1/1000` the seed; `1/4` the contraction. -/
theorem windowCoupling_decay (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (h : windowCoupling N β w ≤ 1 / 1000) (i : ℕ) :
    windowCoupling N β (w + i) ≤ (1 / 1000) * (1 / 4) ^ i := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have hp : (1 / 4 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hle : windowCoupling N β (w + i) ≤ 1 / 1000 := by nlinarith
    have hc := basin_contracts hN hβ (show 1 ≤ w + i by omega) hle
    rw [show w + (i + 1) = w + i + 1 by omega, pow_succ]
    linarith

/-- **A seed at one window puts every large window below any `u₀ > 0`**, at the same coupling.
DERIVED: `1/1000` the seed; `1/4` the contraction; `1000` its inverse. -/
theorem eventually_le_of_seed (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {c : ℕ} (hc : 1 ≤ c)
    (h : windowCoupling N β c ≤ 1 / 1000) {u₀ : ℝ} (hu : 0 < u₀) :
    ∀ᶠ b in atTop, windowCoupling N β b ≤ u₀ := by
  obtain ⟨i₀, hi₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1000 * u₀ by positivity)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (c + i₀)] with b hb
  have hd := windowCoupling_decay hN hβ hc h (b - c)
  rw [Nat.add_sub_of_le (by omega : c ≤ b)] at hd
  have hp : (1 / 4 : ℝ) ^ (b - c) ≤ (1 / 4) ^ i₀ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-! ## 2. The two ends and the tower -/

/-- **(S) The strong-coupling end**: frequently in `β`, the window coupling vanishes along the windows.
DERIVED: `0` the limit. -/
def StrongEnd (N : ℕ) : Prop :=
  ∃ᶠ β in atTop, Tendsto (windowCoupling N β) atTop (𝓝 0)

/-- **A window in the basin makes the window coupling vanish**: at `β ≥ 0`, one window `c ≥ 1` in the basin of
`DoublingSharp` sends the window coupling to `0` along the windows. A bridge for proofs. Proof-internal: `1/4` the
contraction. DERIVED: `0` the limit and the signs; `1` the least index; `1/1000` the seed of `DoublingSharp`. -/
theorem tendsto_zero_of_seed (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {c : ℕ} (hc : 1 ≤ c)
    (h : windowCoupling N β c ≤ 1 / 1000) : Tendsto (windowCoupling N β) atTop (𝓝 0) := by
  have hu : Tendsto (fun b : ℕ => (1 / 1000 : ℝ) * (1 / 4) ^ (b - c)) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).comp (tendsto_sub_atTop_nat c)
    simpa using hp.const_mul (1 / 1000 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_ge_atTop c] with b hb
    exact windowCoupling_nonneg hN hβ (hc.trans hb)
  · filter_upwards [eventually_ge_atTop c] with b hb
    have hd := windowCoupling_decay hN hβ hc h (b - c)
    rwa [Nat.add_sub_of_le hb] at hd

/-- **(S) in the basin form used inside proofs**: for `N ≠ 0`, the strong end holds exactly when, frequently in
`β`, some window `2^c`, `c ≥ 1`, is in the basin of `DoublingSharp`. A bridge for proofs; the statements of the
route use `StrongEnd`. Proof-internal: `1/1000` the seed of `DoublingSharp` and `1/4` its contraction.
DERIVED: `0` the limit and the signs; `1` the least index; `1/1000` the sharp seed of
`DoublingSharp`. -/
theorem strongEnd_iff_seed (hN : N ≠ 0) :
    StrongEnd N ↔ ∃ᶠ β in atTop, ∃ c : ℕ, 1 ≤ c ∧ windowCoupling N β c ≤ 1 / 1000 := by
  constructor
  · intro h
    refine h.mono fun β hβ => ?_
    obtain ⟨c, hlt, hc⟩ := ((hβ.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))).and
      (eventually_ge_atTop 1)).exists
    exact ⟨c, hc, hlt.le⟩
  · intro hS
    refine (hS.and_eventually (eventually_ge_atTop 0)).mono ?_
    rintro β ⟨⟨c, hc, h⟩, hβ⟩
    exact tendsto_zero_of_seed hN hβ hc h

/-- **(W) The weak-coupling end at `u₀`**: on every fixed window, frequently in `β`, the reading exceeds `u₀`.
DERIVED: `1` the least index. -/
def WeakEnd (N : ℕ) (u₀ : ℝ) : Prop :=
  ∀ w : ℕ, 1 ≤ w → ∃ᶠ β in atTop, u₀ < windowCoupling N β w

/-- (A₂) gives (S). DERIVED: `0` the excluded rank. -/
theorem strongEnd_of_seedExistsPow (hN : N ≠ 0) (h : DeltaLengthTower.SeedExistsPow N) : StrongEnd N :=
  (strongEnd_iff_seed hN).mpr h.frequently

/-- (B₂) gives (W) at every `u₀ ≤ 1/1000`. DERIVED: `1/1000` the seed. -/
theorem weakEnd_of_deltaLengthUnbounded {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000)
    (h : DeltaLengthTower.DeltaLengthUnbounded N) : WeakEnd N u₀ :=
  fun w hw => (h w hw).mono fun _ hβ => lt_of_le_of_lt hu hβ

/-- **A tower of values for a two-index reading `g`**: couplings and windows tending to infinity with
`g (βs k) (ws k) = u₀` eventually. DERIVED: `1` the least index; `0` the sign of the coupling. -/
def TowerOf (g : ℝ → ℕ → ℝ) (u₀ : ℝ) (βs : ℕ → ℝ) (ws : ℕ → ℕ) : Prop :=
  Tendsto βs atTop atTop ∧ Tendsto ws atTop atTop ∧
    ∀ᶠ k in atTop, 1 ≤ ws k ∧ 0 ≤ βs k ∧ g (βs k) (ws k) = u₀

set_option linter.dupNamespace false in
/-- **The coupling tower at window coupling `u₀`.** DERIVED: no numeral. -/
def CouplingTower (N : ℕ) (u₀ : ℝ) (βs : ℕ → ℝ) (ws : ℕ → ℕ) : Prop :=
  TowerOf (windowCoupling N) u₀ βs ws

/-- **Selecting a divergent sequence**: if for every `J` eventually in `b` some `β ≥ J` has `P b β`, one
choice `βs b` tends to infinity with `P b (βs b)` eventually. DERIVED: `0` the first bound. -/
theorem exists_tendsto_of_forall_eventually {P : ℕ → ℝ → Prop}
    (h : ∀ J : ℕ, ∀ᶠ b in atTop, ∃ β : ℝ, (J : ℝ) ≤ β ∧ P b β) :
    ∃ βs : ℕ → ℝ, Tendsto βs atTop atTop ∧ ∀ᶠ b in atTop, P b (βs b) := by
  classical
  let Q : ℕ → ℕ → Prop := fun b J => ∃ β : ℝ, (J : ℝ) ≤ β ∧ P b β
  let Jf : ℕ → ℕ := fun b => Nat.findGreatest (Q b) b
  have hspec : ∀ᶠ b in atTop, Q b (Jf b) := by
    filter_upwards [h 0] with b hb
    exact Nat.findGreatest_spec (P := Q b) (Nat.zero_le b) hb
  have hJ : ∀ M : ℕ, ∀ᶠ b in atTop, M ≤ Jf b := by
    intro M
    filter_upwards [h M, eventually_ge_atTop M] with b hb hbM
    exact Nat.le_findGreatest hbM hb
  let βs : ℕ → ℝ := fun b => if hb : Q b (Jf b) then hb.choose else 0
  refine ⟨βs, tendsto_atTop.mpr fun B => ?_, ?_⟩
  · obtain ⟨M, hM⟩ := exists_nat_ge B
    filter_upwards [hspec, hJ M] with b hb hbM
    have e : βs b = hb.choose := dif_pos hb
    have h1 := hb.choose_spec.1
    have h2 : (M : ℝ) ≤ (Jf b : ℝ) := by exact_mod_cast hbM
    rw [e]
    linarith
  · filter_upwards [hspec] with b hb
    have e : βs b = hb.choose := dif_pos hb
    rw [e]
    exact hb.choose_spec.2

/-- **The crossing at every large window, above any coupling `J`.** DERIVED: `1` the least index;
`0` the sign. -/
theorem eventually_crossing (hN : N ≠ 0) {u₀ : ℝ} (hu : 0 < u₀) (hS : StrongEnd N)
    (hW : WeakEnd N u₀) (J : ℕ) :
    ∀ᶠ b in atTop, ∃ β : ℝ, (J : ℝ) ≤ β ∧ (1 ≤ b ∧ 0 ≤ β ∧ windowCoupling N β b = u₀) := by
  obtain ⟨a, ha, c, hc, hseed⟩ := frequently_atTop.mp ((strongEnd_iff_seed hN).mp hS) (J : ℝ)
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg J) ha
  filter_upwards [eventually_le_of_seed hN ha0 hc hseed hu, eventually_ge_atTop 1] with b hb hb1
  obtain ⟨w, hw, hwd⟩ := frequently_atTop.mp (hW b hb1) a
  have hsub := intermediate_value_Icc hw (continuous_windowCoupling hN b).continuousOn
  obtain ⟨β, ⟨hβa, -⟩, hβ⟩ := hsub ⟨hb, hwd.le⟩
  exact ⟨β, ha.trans hβa, hb1, ha0.trans hβa, hβ⟩

/-- **Existence of the coupling tower** from (S) and (W), with window index `k` at step `k`.
DERIVED: `0` the sign of `u₀`. -/
theorem exists_couplingTower (hN : N ≠ 0) {u₀ : ℝ} (hu : 0 < u₀) (hS : StrongEnd N)
    (hW : WeakEnd N u₀) : ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id := by
  obtain ⟨βs, hT, hev⟩ := exists_tendsto_of_forall_eventually (eventually_crossing hN hu hS hW)
  exact ⟨βs, hT, tendsto_id, hev⟩

/-- **A tower in the basin is (S)**: its steps are seeds at couplings tending to infinity.
DERIVED: `1/1000` the seed; `0` the excluded rank. -/
theorem strongEnd_of_couplingTower (hN : N ≠ 0) {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} {ws : ℕ → ℕ}
    (hT : CouplingTower N u₀ βs ws) : StrongEnd N := by
  refine (strongEnd_iff_seed hN).mpr (frequently_atTop.mpr fun B => ?_)
  obtain ⟨k, hkB, hw, -, hg⟩ := ((hT.1.eventually (eventually_ge_atTop B)).and hT.2.2).exists
  exact ⟨βs k, hkB, ws k, hw, by rw [hg]; exact hu⟩

/-- **The tower is (S) with (W)**: for `0 < u₀ ≤ 1/1000` and (W), (S) holds exactly when a tower exists.
DERIVED: `1/1000` the seed; `0` the sign. -/
theorem strongEnd_iff_exists_couplingTower (hN : N ≠ 0) {u₀ : ℝ} (hu0 : 0 < u₀)
    (hu : u₀ ≤ 1 / 1000) (hW : WeakEnd N u₀) :
    StrongEnd N ↔ ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
  ⟨fun hS => exists_couplingTower hN hu0 hS hW, fun ⟨_, hT⟩ => strongEnd_of_couplingTower hN hu hT⟩

/-! ## 3. The two inputs -/

/-- **(IR) Confinement at the window coupling `u₀`**: wherever a window `2^w` reads `u₀`, the measured tensor
mass of the periodic state is at least `m` in window units. DERIVED: `2` the window's base; `1` the least
index; `0` the sign. -/
def ConfinedAt (N : ℕ) [NeZero N] (u₀ m : ℝ) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → windowCoupling N β w = u₀ →
    ENNReal.ofReal (m / 2 ^ w) ≤ mU (NeZero.ne N) β

/-- **(UV) The window reading converges along the tower**: the measured mass is eventually finite and
`2^{ws k} m′(βs k) → μ`. DERIVED: `2` the window's base. -/
def UVConverges (N : ℕ) [NeZero N] (βs : ℕ → ℝ) (ws : ℕ → ℕ) (μ : ℝ) : Prop :=
  (∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≠ ⊤) ∧
    Tendsto (fun k => (2 : ℝ) ^ ws k * measSpacing (NeZero.ne N) (βs k)) atTop (𝓝 μ)

/-- **The missing link between the Clay gap and the measured mass**: a periodic Clay gap at rate `r` makes the
tensor reading of the same state decay at rate `−log r`. DERIVED: `0` the plane, the time axis, the sign. -/
def GapReadsTensor (N : ℕ) [NeZero N] : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ r : ℝ, PeriodicContent.PeriodicClayGapAt 0 0 (NeZero.ne N) β r →
    ENNReal.ofReal (-Real.log r) ≤ mU (NeZero.ne N) β

/-! ## 4. What they give -/

/-- **The window gap**: a window in the basin gives the periodic transfer gap and the periodic Clay gap at
rate `r` with `−log r = log 2 / 2^w` exactly. DERIVED: `2` the least rank and the base; `0` the plane and the
time axis; `1/2` the ratio of `dyadicTorusDecay`; `1/1000` the seed. -/
theorem windowGap (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (hs : windowCoupling N β w ≤ 1 / 1000) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ TransferGap.GapAt (PeriodicState.periodicGaugeInvData 0 0 hN β) r ∧
      PeriodicContent.PeriodicClayGapAt 0 0 hN β r ∧ -Real.log r = Real.log 2 / 2 ^ w := by
  have hn : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have hm : 2 ^ w ≠ 0 := pow_ne_zero w (by norm_num)
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hq1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hdec := DoublingClay2.dyadicTorusDecay hN β hβ (2 ^ w) ⟨w, rfl⟩ hn hs
  have hlag := WeakCouplingWindow.torusLagClear_stepRate 0 0 hN β hq0.le hm hdec
  have hr0 := WeakCouplingWindow.stepRate_pos hq0 (2 ^ w)
  have hr1 := WeakCouplingWindow.stepRate_lt_one hq0.le hq1 hm
  have hg := (WeakCouplingWindow.torusLagClear_iff_gapAt 0 0 hN hβ hm hr0.le).mp hlag
  refine ⟨_, hr0, hr1, hg, GapStep.periodic_clayGapAt_of_gapAt 0 0 hN2 hN hβ hr0 hr1 hg, ?_⟩
  rw [WeakCouplingWindow.neg_log_stepRate hq0, one_div (2 : ℝ), Real.log_inv, neg_neg]
  push_cast
  rfl

/-- **(IR) in the basin, from the link**: `GapReadsTensor` gives `ConfinedAt N u₀ (log 2)` at every
`u₀ ≤ 1/1000`. DERIVED: `2` the least rank and `log 2` the rate; `1/1000` the seed. -/
theorem confinedAt_of_gapReadsTensor [NeZero N] (hN2 : 2 ≤ N) (hG : GapReadsTensor N) {u₀ : ℝ}
    (hu : u₀ ≤ 1 / 1000) : ConfinedAt N u₀ (Real.log 2) := by
  intro β hβ w hw hg
  obtain ⟨r, -, -, -, hcl, hlog⟩ := windowGap hN2 (NeZero.ne N) hβ hw (by rw [hg]; exact hu)
  have h := hG β hβ r hcl
  rwa [hlog] at h

/-- **(IR) is vacuous below `0`.** DERIVED: `0` the sign. -/
theorem confinedAt_of_neg [NeZero N] {u₀ : ℝ} (hu : u₀ < 0) (m : ℝ) : ConfinedAt N u₀ m := by
  intro β hβ w hw hg
  have := windowCoupling_nonneg (NeZero.ne N) hβ hw
  exfalso
  linarith

/-- **No tower below `0`.** DERIVED: `0` the sign. -/
theorem not_couplingTower_of_neg (hN : N ≠ 0) {u₀ : ℝ} (hu : u₀ < 0) (βs : ℕ → ℝ) (ws : ℕ → ℕ) :
    ¬ CouplingTower N u₀ βs ws := by
  rintro ⟨-, -, hev⟩
  obtain ⟨k, hw, hβ, hg⟩ := hev.exists
  have := windowCoupling_nonneg hN hβ hw
  linarith

/-- **(IR) along a tower**: eventually `m ≤ 2^{ws k} m′(βs k)`. DERIVED: `2` the base; `0` the sign. -/
theorem le_window_mass [NeZero N] {u₀ m : ℝ} {βs : ℕ → ℝ} {ws : ℕ → ℕ}
    (hT : CouplingTower N u₀ βs ws) (hIR : ConfinedAt N u₀ m) (hm : 0 ≤ m)
    (hfin : ∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≠ ⊤) :
    ∀ᶠ k in atTop, m ≤ (2 : ℝ) ^ ws k * measSpacing (NeZero.ne N) (βs k) := by
  filter_upwards [hT.2.2, hfin] with k ⟨hw, hβ, hg⟩ hne
  have h := hIR (βs k) hβ (ws k) hw hg
  have hp : (0 : ℝ) < 2 ^ ws k := by positivity
  have h2 := ENNReal.toReal_mono hne h
  rw [ENNReal.toReal_ofReal (div_nonneg hm hp.le), div_le_iff₀ hp] at h2
  unfold measSpacing
  rw [mul_comm]
  exact h2

/-- **(IR) and (UV) bound the limit below**: `m ≤ μ`. DERIVED: `0` the sign. -/
theorem le_of_confinedAt_uv [NeZero N] {u₀ m μ : ℝ} {βs : ℕ → ℝ} {ws : ℕ → ℕ}
    (hT : CouplingTower N u₀ βs ws) (hIR : ConfinedAt N u₀ m) (hm : 0 ≤ m)
    (hUV : UVConverges N βs ws μ) : m ≤ μ :=
  ge_of_tendsto hUV.2 (le_window_mass hT hIR hm hUV.1)

section SU

variable [NeZero N] [Fact (2 ≤ N)]

/-- **The coupling tower is a measured tower** under (IR) at `m > 0` and (UV). DERIVED: `2/3`, `4/3` the band
around `μ`; `3` their denominator; `0` the signs. -/
theorem measTowerG_of_confinedAt_uv {u₀ m μ : ℝ} {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (hm : 0 < m) (hIR : ConfinedAt N u₀ m) (hUV : UVConverges N βs id μ) :
    MeasTowerG (MassGap.SUN.SU N) βs := by
  have hμ : 0 < μ := lt_of_lt_of_le hm (le_of_confinedAt_uv hT hIR hm.le hUV)
  set A := GaugeRunning.aRunG (MassGap.SUN.SU N) 1 with hA
  have hA0 : 0 < A := aRunG_pos (MassGap.SUN.SU N) one_pos
  have hAne : A ≠ 0 := hA0.ne'
  refine ⟨hT.1, 4 * μ / (3 * A), by positivity, ?_⟩
  have hI : Set.Ioo (2 * μ / 3) (4 * μ / 3) ∈ 𝓝 μ := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hUV.2.eventually hI, hUV.1] with k ⟨hlo, hhi⟩ hne
  have e : mUG (MassGap.SUN.SU N) (βs k) = ENNReal.ofReal (measSpacing (NeZero.ne N) (βs k)) := by
    rw [mUG_SU]; exact (ENNReal.ofReal_toReal hne).symm
  have hd : dySpacingG (MassGap.SUN.SU N) k = A / 2 ^ (k + 1) := rfl
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  simp only [id_eq] at hlo hhi
  have e1 : 4 * μ / (3 * A) * (A / 2 ^ (k + 1)) = 2 * μ / 3 / 2 ^ k := by
    field_simp
    ring
  have e2 : 2 * (4 * μ / (3 * A)) * (A / 2 ^ (k + 1)) = 4 * μ / 3 / 2 ^ k := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [e, hd, e1]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hp]
    linarith
  · rw [e, hd, e2]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hp]
    linarith

/-- **The per-step gap from seeds at the step's window**: wherever `2^k` is in the basin at `βs k`, the
transfer along `schedAlongG (SU N) βs` has `−log r / a_k = 2 log 2 / aRunG 1`. DERIVED: `2` the base and the
first halving of `dySpacingG`; `1` the reference coupling and the least index; `0` the plane and the time
axis; `1/1000` the sharp seed of `DoublingSharp`. -/
theorem stepGap_of_seeds {βs : ℕ → ℝ}
    (h : ∀ᶠ k in atTop, 1 ≤ k ∧ 0 ≤ βs k ∧ windowCoupling N (βs k) k ≤ 1 / 1000) :
    ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
      2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
        ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k := by
  have hA0 : 0 < GaugeRunning.aRunG (MassGap.SUN.SU N) 1 := aRunG_pos (MassGap.SUN.SU N) one_pos
  have hAne := hA0.ne'
  filter_upwards [h] with k ⟨hw, hβ, hs⟩
  obtain ⟨r, hr0, hr1, hgap, -, hlog⟩ := windowGap (Fact.out : 2 ≤ N) (NeZero.ne N) hβ hw hs
  refine ⟨r, hr0, hr1, hgap, le_of_eq ?_⟩
  rw [hlog]
  show _ = Real.log 2 / 2 ^ k / (GaugeRunning.aRunG (MassGap.SUN.SU N) 1 / 2 ^ (k + 1))
  field_simp
  ring

/-- **The per-step gap along a tower in the basin.** DERIVED: `1/1000` the seed. -/
theorem stepGap_along {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
      2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
        ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k :=
  stepGap_of_seeds (hT.2.2.mono fun k ⟨hw, hβ, hg⟩ => ⟨hw, hβ, by
    show windowCoupling N (βs k) (id k) ≤ 1 / 1000
    rw [hg]; exact hu⟩)

/-- DERIVED: `2` the base; `1` the reference coupling; `0` the sign. -/
theorem cGap_pos : 0 < 2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1 :=
  div_pos (mul_pos two_pos (Real.log_pos one_lt_two)) (aRunG_pos (MassGap.SUN.SU N) one_pos)

/-- **`FlowClusterAbsG` from seeds at the step's window.** DERIVED: `1` the window; `0` the time axis;
`1/1000` the sharp seed of `DoublingSharp`. -/
theorem flowClusterAbs_of_seeds {βs : ℕ → ℝ}
    (h : ∀ᶠ k in atTop, 1 ≤ k ∧ 0 ≤ βs k ∧ windowCoupling N (βs k) k ≤ 1 / 1000)
    (Φ : GFlow (MassGap.SUN.SU N)) (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ}
    (hpos : Φ.PosPreserving (schedAlongG _ βs) 0 r) :
    FlowClusterAbsG (schedAlongG _ βs) Φ 0 r 1 := by
  refine flowClusterAbs_of_stepGap (schedAlongG _ βs) (schedOS_alongG _ βs).dyadic βs (fun _ => rfl) Φ hB 0
    hpos (cGap_pos (N := N)) ?_
  filter_upwards [stepGap_of_seeds h] with k ⟨r', hr0, _, hg, hrate⟩
  exact ⟨r', hr0, hg, hrate⟩

/-- **`FlowClusterAbsG` along a tower in the basin.** DERIVED: `1` the window; `0` the time axis;
`1/1000` the seed. -/
theorem flowClusterAbs_along {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ}
    (hT : CouplingTower N u₀ βs id) (Φ : GFlow (MassGap.SUN.SU N))
    (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ}
    (hpos : Φ.PosPreserving (schedAlongG _ βs) 0 r) :
    FlowClusterAbsG (schedAlongG _ βs) Φ 0 r 1 :=
  flowClusterAbs_of_seeds (hT.2.2.mono fun k ⟨hw, hβ, hg⟩ => ⟨hw, hβ, by
    show windowCoupling N (βs k) (id k) ≤ 1 / 1000
    rw [hg]; exact hu⟩) Φ hB hpos

/-- **The observer's gap along a tower in the basin**, at every step `m₀`. DERIVED: `0` the plane; `1` the
top of the rate; `1/1000` the seed. -/
theorem observerGap_along {u₀ : ℝ} (hu : u₀ ≤ 1 / 1000) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (Φ : GFlow (MassGap.SUN.SU N)) (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ}
    (hphys : Φ.PhysRange (schedAlongG _ βs) r) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (transferNG (schedAlongG _ βs) (schedOS_alongG _ βs) Φ hB 0 hphys m0) ρ := by
  refine flowGapAt_of_stepGap (schedAlongG _ βs) (schedOS_alongG _ βs) βs (fun _ => rfl) Φ hB hphys m0
    (cGap_pos (N := N)) ?_
  filter_upwards [stepGap_along hu hT] with k ⟨r', hr0, _, hg, hrate⟩
  exact ⟨r', hr0, hg, hrate⟩

/-- **The ends, the link and (UV) give a coupling tower that is a measured tower, with the per-step gap.**
DERIVED: `1/1000` the seed; `log 2` the window rate; `0` the signs. -/
theorem measuredTower_of_ends {u₀ : ℝ} (hu0 : 0 < u₀) (hu : u₀ ≤ 1 / 1000) (hS : StrongEnd N)
    (hW : WeakEnd N u₀) (hG : GapReadsTensor N)
    (hUV : ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ∃ μ : ℝ, UVConverges N βs id μ) :
    ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id ∧ MeasTowerG (MassGap.SUN.SU N) βs ∧
      ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 (βs k)) r ∧
        2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
          ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k := by
  obtain ⟨βs, hT⟩ := exists_couplingTower (NeZero.ne N) hu0 hS hW
  obtain ⟨μ, hμ⟩ := hUV βs hT
  exact ⟨βs, hT, measTowerG_of_confinedAt_uv hT (Real.log_pos one_lt_two)
    (confinedAt_of_gapReadsTensor (Fact.out : 2 ≤ N) hG hu) hμ, stepGap_along hu hT⟩

/-! ## 5. Tests -/

/-- **The ultralocal schedule meets the per-step gap**: every state at `β = 0`. DERIVED: `0` the ultralocal
coupling; `1` the least index. -/
theorem stepGap_at_zero :
    ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TransferGap.GapAt (periodicGaugeInvDataG (MassGap.SUN.SU N) 0 0 ((fun _ : ℕ => (0 : ℝ)) k)) r ∧
      2 * Real.log 2 / GaugeRunning.aRunG (MassGap.SUN.SU N) 1
        ≤ -Real.log r / dySpacingG (MassGap.SUN.SU N) k :=
  stepGap_of_seeds ((eventually_ge_atTop 1).mono fun k hk => ⟨hk, le_rfl, by
    show windowCoupling N 0 k ≤ 1 / 1000
    rw [windowCoupling_zero]; norm_num⟩)

/-- **The ultralocal schedule meets `FlowClusterAbsG`.** DERIVED: `0` the ultralocal coupling and the time
axis; `1` the window. -/
theorem flowClusterAbs_at_zero (Φ : GFlow (MassGap.SUN.SU N))
    (hB : UniformBoundFG (schedAlongG _ (fun _ => (0 : ℝ))) Φ.map) {r : ℝ}
    (hpos : Φ.PosPreserving (schedAlongG _ (fun _ => (0 : ℝ))) 0 r) :
    FlowClusterAbsG (schedAlongG _ (fun _ => (0 : ℝ))) Φ 0 r 1 :=
  flowClusterAbs_of_seeds ((eventually_ge_atTop 1).mono fun k hk => ⟨hk, le_rfl, by
    show windowCoupling N 0 k ≤ 1 / 1000
    rw [windowCoupling_zero]; norm_num⟩) Φ hB hpos

end SU

/-- **A window reading `u₀ ≠ 0` is not read at `β = 0`.** DERIVED: `0` the ultralocal coupling. -/
theorem ne_zero_of_windowCoupling_eq {u₀ β : ℝ} {w : ℕ} (hu : u₀ ≠ 0) (h : windowCoupling N β w = u₀) :
    β ≠ 0 := by
  rintro rfl
  rw [windowCoupling_zero] at h
  exact hu h.symm

/-- **A reading that does not run has a tower exactly at its own value.** DERIVED: `1` the least index and
the shift of the windows; `0` the sign. -/
theorem exists_towerOf_const_iff (g₀ u₀ : ℝ) :
    (∃ (βs : ℕ → ℝ) (ws : ℕ → ℕ), TowerOf (fun _ _ => g₀) u₀ βs ws) ↔ u₀ = g₀ := by
  constructor
  · rintro ⟨βs, ws, -, -, hev⟩
    obtain ⟨k, -, -, hk⟩ := hev.exists
    exact hk.symm
  · rintro rfl
    exact ⟨fun k => (k : ℝ), fun k => k + 1, tendsto_natCast_atTop_atTop, tendsto_add_atTop_nat 1,
      Eventually.of_forall fun k => ⟨Nat.le_add_left 1 k, Nat.cast_nonneg k, rfl⟩⟩

/-- **A massless window excludes (IR)**: along a tower, (UV) at `μ = 0` and (IR) at `m > 0` are
incompatible. DERIVED: `0` the massless limit and the sign. -/
theorem not_confinedAt_of_massless [NeZero N] {u₀ m : ℝ} {βs : ℕ → ℝ} {ws : ℕ → ℕ}
    (hT : CouplingTower N u₀ βs ws) (hm : 0 < m) (hUV : UVConverges N βs ws 0) :
    ¬ ConfinedAt N u₀ m := fun hIR => by
  have := le_of_confinedAt_uv hT hIR hm.le hUV
  linarith

end MassGap.CouplingTower

end

#print axioms MassGap.CouplingTower.continuous_windowCoupling
#print axioms MassGap.CouplingTower.hasDerivAt_windowCoupling
#print axioms MassGap.CouplingTower.windowCoupling_zero
#print axioms MassGap.CouplingTower.windowCoupling_nonneg
#print axioms MassGap.CouplingTower.windowCoupling_succ_le
#print axioms MassGap.CouplingTower.basin_contracts
#print axioms MassGap.CouplingTower.windowCoupling_decay
#print axioms MassGap.CouplingTower.eventually_le_of_seed
#print axioms MassGap.CouplingTower.strongEnd_of_seedExistsPow
#print axioms MassGap.CouplingTower.weakEnd_of_deltaLengthUnbounded
#print axioms MassGap.CouplingTower.exists_tendsto_of_forall_eventually
#print axioms MassGap.CouplingTower.eventually_crossing
#print axioms MassGap.CouplingTower.exists_couplingTower
#print axioms MassGap.CouplingTower.strongEnd_of_couplingTower
#print axioms MassGap.CouplingTower.strongEnd_iff_exists_couplingTower
#print axioms MassGap.CouplingTower.windowGap
#print axioms MassGap.CouplingTower.confinedAt_of_gapReadsTensor
#print axioms MassGap.CouplingTower.confinedAt_of_neg
#print axioms MassGap.CouplingTower.not_couplingTower_of_neg
#print axioms MassGap.CouplingTower.le_window_mass
#print axioms MassGap.CouplingTower.le_of_confinedAt_uv
#print axioms MassGap.CouplingTower.measTowerG_of_confinedAt_uv
#print axioms MassGap.CouplingTower.stepGap_of_seeds
#print axioms MassGap.CouplingTower.stepGap_along
#print axioms MassGap.CouplingTower.cGap_pos
#print axioms MassGap.CouplingTower.flowClusterAbs_of_seeds
#print axioms MassGap.CouplingTower.flowClusterAbs_along
#print axioms MassGap.CouplingTower.observerGap_along
#print axioms MassGap.CouplingTower.measuredTower_of_ends
#print axioms MassGap.CouplingTower.stepGap_at_zero
#print axioms MassGap.CouplingTower.flowClusterAbs_at_zero
#print axioms MassGap.CouplingTower.ne_zero_of_windowCoupling_eq
#print axioms MassGap.CouplingTower.exists_towerOf_const_iff
#print axioms MassGap.CouplingTower.not_confinedAt_of_massless
