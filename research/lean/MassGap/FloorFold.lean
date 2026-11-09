import Mathlib
import MassGap.RegNontrivial

/-!
# MassGap.FloorFold — the two open floors compared: amplitude, slope, and the one clause that folds them

`ReadPos.ReflFloorAt` (the upper half of the band) and `RegNontrivial.regConnected_iff_floor` (non-triviality)
are both floors on a reflected read `g(m) = ν(θX · T_{2m e₀} X)`, `X` in the half-space algebra. This module
computes what each one reads. Declarations are in the namespace `MassGap.FloorFold`.

## 1. A reflected read is antitone (proved)

A non-negative, log-convex, bounded sequence is antitone (`step_le_of_bounded`). Every reflected read of the
periodic state is such a sequence (`gP_nonneg`, `gP_logConvex`, `gP_le_norm`), so `gP_antitone`: the read at
gap `m` is at most the read at gap `0`. The covariance form is `cov_far_le_contact`.

## 2. The window floor reads a slope, not an amplitude (proved)

For a log-convex read `g` with `g(0) > 0`:

* `far_of_slope`: a chord of two reads continues beyond them;
* `window_of_slope`: a chord at rate `r < u` gives `g(0) e^{−2Mu} ≤ g(M)` at some `M`;
* `slope_of_window`: `g(0) e^{−2m₁u} ≤ g(m₁)` gives the chord at rate `u` beyond `m₁`.

So `∃ m₁, g(0) e^{−2m₁u} ≤ g(m₁)` is the bound `u` on the slope of `log g` at far gaps, up to the strictness of
`u`. The contact read and every overall factor of `g` leave the statement: they are absorbed by taking `M` large.

## 3. The normalisation, computed

With `a_k` the spacing, `2 m a_k` the physical gap, so `m ≈ 2^k` is a fixed physical gap. In the composites'
normalisation a read at fixed physical gap is taken to have size `s_k = a_k⁸` (two factors of `a_k⁴` per pair; not proved here, and `PhysBand` takes `s` as data).

* `contact_le_of_window`: if the window inequality holds at `m ≤ D 2^k` then `g(0) ≤ e^{2DU} g(m)`. A window
  floor at bounded physical gap is a ceiling on the contact read.
* `not_window_of_contact`: if `g_k(m_k) ≤ C s_k` at `m_k ≤ D 2^k` and `g_k(0)/s_k → ∞`, the window inequality fails
  at `m_k` eventually. So the bare tensor read, whose contact term is expected to be much larger than `a_k⁸` (no
  theorem here says so), does not meet the window inequality at any bounded physical gap.
* `window_of_ratio`: if `c s ≤ g(m)`, `g(0) ≤ C s`, `m ≥ w 2^k` and `log(C/c) ≤ 2wU`, the window inequality holds.
  For a read whose contact and far terms have one normalisation the floor passes, whatever `s` is.
* `amplitude_not_window`: `G_k(n) = e^{−2nk/2^k}`, log-convex, has `a⁸ ≤ G_k(2^k)` with `a = 2^{−k}` and fails the window
  inequality at every gap for every `U`, eventually. The rate is `k` in window units, the logarithmic loss
  `log(1/a⁸)/d` of a floor at one separation `d`. So one amplitude at one physical separation gives no window floor.
* `window_not_amplitude`: `H_k(n) = 2^{−9k} e^{−2n/2^k}` meets the window inequality at `U = 1` at every step and no
  floor `c a⁸`. So no window floor gives an amplitude.

These are sequence models; they rule out proofs that use only log-convexity. On the bare read the clause that gives
the window floor is two reads in one normalisation: `PhysBand` (a floor at one physical gap, a ceiling at a
smaller one) gives `SlopeAt` (`slope_of_physBand`), `s_k` cancels, and `SlopeAt` below `U` gives `WindowFloorAt` at
`U` (`windowFloorAt_of_slope`). The converse with the same `U` is `slope_of_windowFloorAt`.

## 4. The clause that folds (proved, at the macroscopic read)

`macroX Φ P k` is the flowed smeared monomial. At a macroscopic observable contact and far reads have one
normalisation, because its contact read is, by the geometry of the margin monomial, a separated read (`θX` and `X` stand `2(d − r)` apart); this is not proved here.

`PhysFloor Φ P gap c l`: `c ≤ |cov_k(θX_k, T_{2 gap_k} X_k)|` along `l`. With `gap_k ≥ w 2^k` it is a correlation floor
at a fixed physical separation, in the normalisation the composites use.

* `regConnected_of_physFloor`: `PhysFloor` along `ultra` at any gaps gives `RegConnectedNonzero`, through
  `cov_far_le_contact` and `regConnected_iff_floor`.
* `regConnected_iff_physFloor`: `RegConnectedNonzero` is `PhysFloor` at gap `0` of some regular monomial.
* `macro_window`: `PhysFloor` at `gap_k ≥ w 2^k` gives the window inequality of the same read, at a measured `U`.
  The ceiling is `contact_ceiling`, from `UniformBoundF`.
* `windowUpper_of_macroReads`: along a tower, a floor and a ceiling on a macroscopic read and its comparability
  with the diagonal tensor read give `WindowUpper` (`MacroReadsAt`). This is
  `BandClose.windowUpper_of_tensorReads` with an observable that depends on `k`.

## What does not follow, plainly

`PhysFloor` does not imply `ReadPos.ReflFloorAt`, and no capstone with fewer open clauses is built. The count of
`ReadPos.clayStatement_of_strongEnd_floor` stays three: `StrongEnd N`, `ReflFloorAt`, `ExistAlong`.

* Observable. `ReflFloorAt` reads the bare tensor reading `E`, because `measMassOfG` does; `regConnected_iff_floor`
  reads a flowed monomial. Comparability of the two is the hypothesis of `MacroReadsAt`; it takes the place of the
  defect bound, and nothing here proves it.
* The defect conjunct of `ReflFloorAt` (`DefectAt`) is independent of any floor: `reflFloorAt_iff` splits it off.
* Filter. `regConnected_iff_floor` is a statement along `ultra`, `WindowUpper` along `atTop`. A floor along `ultra`
  says nothing about the steps off one set of the ultrafilter. For the same reason `amplitude_of_conv` puts an
  amplitude inside `ExistAlong` (a non-zero separated `contTG` reading, as in `TwoPointKernelG`) and that amplitude
  stays along `ultra`, on the trace channel, not on `E`.
* State. `regConnected_iff_floor` reads `stateK`, the couplings `dyBeta`; `ReflFloorAt` reads every coupling tower. No
  theorem found identifies them, and `RegConnectedNonzero` is not a clause of `ExistAlong`: the capstone has no
  separate non-triviality input for a floor to absorb.
* Rate. `macro_window` gives a measured `U = |log(C/c)|/(2w)`. The band needs `U ≤ 2 log 2`; nothing relates them.
* Non-Gaussianity (`NonGaussianTG`, a three-point reading) does not follow from a two-point floor at all.
* Converse at positive gap. `RegConnectedNonzero` is `PhysFloor` at gap `0`. That it gives `PhysFloor` at physical
  gaps `w > 0` needs continuity of the limit read at gap `0`; with it, positivity at every gap is log-convexity.
  It is not proved here.
* `ProxyNondeg` is a floor of the same shape (`ProxyCov.proxRead_far`), uncentred and on combinations of flowed
  proxies at flow time `→ 0`. It is not tied to `PhysFloor` here.

DERIVED (module-wide): `0` the plane, the time axis, the contact gap and the signs; `1` the unit step, the least gap
and the shift of a bound away from `0`; `2` the two steps of one reflected gap, the window base and the square; `3`
in `3 * 3` a bound on `e` in the model; `8` and `9` in the sequence models only, the exponent of `a⁸` and one more. No
number of the models enters a clause: `PhysBand` takes its scale `s` as data.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FloorFold

open Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyMoments MassGap.ObserverSymField
  MassGap.ApertureThing
open MassGap.ShellTranslate
open MassGap.RegularDense (RegConnectedNonzero)
open MassGap.FocusZoom (stateCov)
open MassGap.StepPeriodic (gP connP gP_conn connP_mem gapRead_eq_P reflShiftP periodic_far_ge)
open MassGap.MeasuredTower (tensorEnergyG)
open MassGap.MeasuredSpacing (mUG_SU)
open MassGap.BandClose (gE)

/-! ## 1. Log-convex reads -/

section Seq

variable {g : ℕ → ℝ}

/-- **A ratio persists along a log-convex sequence.** DERIVED: `0` the sign; `1` the step. -/
theorem growth (hL : LogConvexSeq g) {n : ℕ} (hn : 0 < g n) {q : ℝ} (hq : 0 < q)
    (h : q * g n ≤ g (n + 1)) : ∀ j, 0 < g (n + j) ∧ q * g (n + j) ≤ g (n + j + 1) := by
  intro j
  induction j with
  | zero => exact ⟨hn, h⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp : 0 < g (n + j + 1) := lt_of_lt_of_le (mul_pos hq h1) h2
    refine ⟨hp, ?_⟩
    have hl := hL (n + j)
    have h3 := mul_le_mul_of_nonneg_left h2 hp.le
    have h4 : g (n + j) * (q * g (n + j + 1)) ≤ g (n + j) * g (n + j + 1 + 1) := by nlinarith
    exact le_of_mul_le_mul_left h4 h1

/-- **A non-negative, log-convex, bounded sequence does not increase.** An increase at one step would repeat
with at least the same ratio. DERIVED: `0` the sign; `1` the step. -/
theorem step_le_of_bounded (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {B : ℝ} (hB : ∀ n, g n ≤ B)
    (n : ℕ) : g (n + 1) ≤ g n := by
  by_contra hlt0
  have hlt := not_le.mp hlt0
  have hn : 0 < g n := by
    rcases (h0 n).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := null_propagates hL h.symm 1
      linarith
  have hq1 : 1 < g (n + 1) / g n := (one_lt_div hn).mpr hlt
  have hq : 0 < g (n + 1) / g n := by linarith
  have he : g (n + 1) / g n * g n = g (n + 1) := div_mul_cancel₀ _ hn.ne'
  have hgr := growth hL hn hq he.le
  have hpow : ∀ j : ℕ, (g (n + 1) / g n) ^ j * g n ≤ g (n + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := (hgr j).2
      calc (g (n + 1) / g n) ^ (j + 1) * g n
          = g (n + 1) / g n * ((g (n + 1) / g n) ^ j * g n) := by ring
        _ ≤ g (n + 1) / g n * g (n + j) := mul_le_mul_of_nonneg_left ih hq.le
        _ ≤ g (n + j + 1) := h1
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / g n) hq1
  rw [div_lt_iff₀ hn] at hj
  linarith [hpow j, hB (n + j)]

/-- **A chord continues**: `g(s) e^{−2wr} ≤ g(s+w)` gives `g(s) e^{−2jr} ≤ g(s+j)` for `j ≥ w`. DERIVED: `2` the
two steps of one gap; `1` the least chord. -/
theorem far_of_slope (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {s w j : ℕ} (hw : 1 ≤ w) (hj : w ≤ j)
    (hp : 0 < g s) {r : ℝ} (h : g s * Real.exp (-(2 * w * r)) ≤ g (s + w)) :
    g s * Real.exp (-(2 * j * r)) ≤ g (s + j) := by
  have hL' : LogConvexSeq (fun n => g (s + n)) := fun n => hL (s + n)
  have h0' : ∀ n, 0 ≤ g (s + n) := fun n => h0 _
  have hw1 : 0 < g (s + w) := lt_of_lt_of_le (mul_pos hp (Real.exp_pos _)) h
  have hf := far_ge_rpow_pos (g := fun n => g (s + n)) h0' hL' hw hj hw1
  simp only [add_zero] at hf
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw
  have hb : Real.exp (-(2 * w * r)) ≤ g (s + w) / g s := by
    rw [le_div_iff₀ hp]
    linarith
  have hexp : Real.exp (-(2 * j * r)) = Real.exp (-(2 * w * r)) ^ ((j : ℝ) / w) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [hexp]
  calc g s * Real.exp (-(2 * w * r)) ^ ((j : ℝ) / w)
      ≤ g s * (g (s + w) / g s) ^ ((j : ℝ) / w) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Real.exp_pos _).le hb (by positivity)) hp.le
    _ ≤ g (s + j) := hf

/-- **A chord below the rate gives the window inequality**: at a far enough gap the contact read and every
factor of `g` are absorbed by the strict difference of the rates. DERIVED: `2` the two steps of one gap; `1` the
least gap; `0` the contact gap. -/
theorem window_of_slope (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) (hg0 : 0 < g 0) {s w : ℕ}
    (hw : 1 ≤ w) (hp : 0 < g s) {r u : ℝ} (hru : r < u)
    (h : g s * Real.exp (-(2 * w * r)) ≤ g (s + w)) :
    ∃ M : ℕ, 1 ≤ M ∧ g 0 * Real.exp (-(2 * M * u)) ≤ g M := by
  have hd : 0 < 2 * (u - r) := by linarith
  obtain ⟨j0, hj0⟩ := exists_nat_ge ((Real.log (g 0 / g s) - 2 * s * u) / (2 * (u - r)))
  obtain ⟨j, hj, hjw⟩ : ∃ j : ℕ, j0 ≤ j ∧ w ≤ j := ⟨max j0 w, le_max_left _ _, le_max_right _ _⟩
  have hjr : (j0 : ℝ) ≤ j := by exact_mod_cast hj
  have hkey : Real.log (g 0 / g s) - 2 * s * u ≤ 2 * j * (u - r) := by
    have := (div_le_iff₀ hd).mp (hj0.trans hjr)
    linarith
  refine ⟨s + j, by omega, le_trans ?_ (far_of_slope h0 hL hw hjw hp h)⟩
  have hratio : 0 < g 0 / g s := div_pos hg0 hp
  have e : g 0 = g s * Real.exp (Real.log (g 0 / g s)) := by
    rw [Real.exp_log hratio]
    field_simp
  calc g 0 * Real.exp (-(2 * ((s + j : ℕ) : ℝ) * u))
      = g s * (Real.exp (Real.log (g 0 / g s)) * Real.exp (-(2 * ((s + j : ℕ) : ℝ) * u))) := by
        nth_rewrite 1 [e]
        ring
    _ = g s * Real.exp (Real.log (g 0 / g s) + -(2 * ((s + j : ℕ) : ℝ) * u)) := by
        rw [Real.exp_add]
    _ ≤ g s * Real.exp (-(2 * j * r)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hp.le
        push_cast
        linarith

/-- **The window inequality gives the chord at the same rate beyond its gap.** DERIVED: `2` the two steps of one
gap; `1` the least gap; `0` the contact gap. -/
theorem slope_of_window (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) (hg0 : 0 < g 0) {m₁ : ℕ}
    (hm : 1 ≤ m₁) {u : ℝ} (h : g 0 * Real.exp (-(2 * m₁ * u)) ≤ g m₁) {s : ℕ} (hs : m₁ ≤ s)
    (w : ℕ) : 0 < g s ∧ g s * Real.exp (-(2 * w * u)) ≤ g (s + w) := by
  have hg1 : 0 < g m₁ := lt_of_lt_of_le (mul_pos hg0 (Real.exp_pos _)) h
  have hp := pos_of_logConvex h0 hL hm hg1
  refine ⟨hp s, ?_⟩
  have hs1 : 1 ≤ s := hm.trans hs
  have hlm := Real.log_le_log (mul_pos hg0 (Real.exp_pos _)) h
  rw [Real.log_mul hg0.ne' (Real.exp_pos _).ne', Real.log_exp] at hlm
  have ha := far_log h0 hL hm hs hg1
  have hb := far_log h0 hL hs1 (Nat.le_add_right s w) (hp s)
  push_cast at hb
  have hm0 : (0 : ℝ) < m₁ := by exact_mod_cast hm
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  set L0 := Real.log (g 0)
  set Lm := Real.log (g m₁)
  set Ls := Real.log (g s)
  set Lw := Real.log (g (s + w))
  have hLs : L0 - 2 * s * u ≤ Ls := by
    have h1 := mul_le_mul_of_nonneg_left hlm hs0.le
    have h2 : (m₁ : ℝ) * (L0 - 2 * s * u) ≤ m₁ * Ls := by nlinarith
    exact le_of_mul_le_mul_left h2 hm0
  have hLw : Ls - 2 * w * u ≤ Lw := by
    have h1 := mul_le_mul_of_nonneg_left hLs hw0
    have h2 : (s : ℝ) * (Ls - 2 * w * u) ≤ s * Lw := by nlinarith
    exact le_of_mul_le_mul_left h2 hs0
  calc g s * Real.exp (-(2 * w * u)) = Real.exp (Ls - 2 * w * u) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (hp s)]
    _ ≤ Real.exp Lw := Real.exp_le_exp.mpr hLw
    _ = g (s + w) := Real.exp_log (hp _)

end Seq

/-! ## 2. The normalisation -/

section Scale

/-- **A far read and a contact read in one normalisation meet the window inequality.** `s` is the common scale; it
cancels. DERIVED: `2` the two steps of one gap and the window base; `0` the signs. -/
theorem window_of_ratio {g0 gm s c C w U : ℝ} {m k : ℕ} (hs : 0 < s) (hc : 0 < c) (hC : 0 < C)
    (hU0 : 0 ≤ U) (hfl : c * s ≤ gm) (hcl : g0 ≤ C * s) (hm : w * 2 ^ k ≤ m)
    (hU : Real.log (C / c) ≤ 2 * w * U) : g0 * Real.exp (-(2 * m * (U / 2 ^ k))) ≤ gm := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hx : 2 * w * U ≤ 2 * m * (U / 2 ^ k) := by
    have e : 2 * (m : ℝ) * (U / 2 ^ k) = 2 * (m / 2 ^ k) * U := by ring
    rw [e]
    have : w ≤ (m : ℝ) / 2 ^ k := (le_div_iff₀ h2k).mpr hm
    gcongr
  have hexp : Real.exp (-(2 * m * (U / 2 ^ k))) ≤ c / C := by
    have hq : 0 < c / C := div_pos hc hC
    rw [← Real.exp_log hq, Real.log_div hc.ne' hC.ne']
    refine Real.exp_le_exp.mpr ?_
    rw [Real.log_div hC.ne' hc.ne'] at hU
    linarith
  calc g0 * Real.exp (-(2 * m * (U / 2 ^ k))) ≤ C * s * Real.exp (-(2 * m * (U / 2 ^ k))) :=
        mul_le_mul_of_nonneg_right hcl (Real.exp_pos _).le
    _ ≤ C * s * (c / C) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = c * s := by field_simp
    _ ≤ gm := hfl

/-- **A window inequality at bounded physical gap is a ceiling on the contact read.** DERIVED: `2` the two steps of
one gap and the window base; `0` the signs. -/
theorem contact_le_of_window {g0 gm U D : ℝ} {m k : ℕ} (hU : 0 ≤ U) (hgm : 0 ≤ gm)
    (hm : (m : ℝ) ≤ D * 2 ^ k) (h : g0 * Real.exp (-(2 * m * (U / 2 ^ k))) ≤ gm) :
    g0 ≤ Real.exp (2 * D * U) * gm := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hx : 2 * m * (U / 2 ^ k) ≤ 2 * D * U := by
    have e : 2 * (m : ℝ) * (U / 2 ^ k) = 2 * (m / 2 ^ k) * U := by ring
    rw [e]
    have : (m : ℝ) / 2 ^ k ≤ D := (div_le_iff₀ h2k).mpr hm
    gcongr
  have e : g0 = g0 * Real.exp (-(2 * m * (U / 2 ^ k))) * Real.exp (2 * m * (U / 2 ^ k)) := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  calc g0 = g0 * Real.exp (-(2 * m * (U / 2 ^ k))) * Real.exp (2 * m * (U / 2 ^ k)) := e
    _ ≤ gm * Real.exp (2 * m * (U / 2 ^ k)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ gm * Real.exp (2 * D * U) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hgm
    _ = Real.exp (2 * D * U) * gm := mul_comm _ _

/-- **A contact read larger than the far normalisation excludes the window inequality at bounded physical gap.**
`s k` is the scale of the far read. DERIVED: `2` the two steps of one gap and the window base; `0` the signs and the
contact gap. -/
theorem not_window_of_contact {g : ℕ → ℕ → ℝ} {m₁ : ℕ → ℕ} {s : ℕ → ℝ} {U C D : ℝ} (hU : 0 ≤ U)
    (hs : ∀ k, 0 < s k) (hnn : ∀ k, 0 ≤ g k (m₁ k)) (hD : ∀ᶠ k in atTop, (m₁ k : ℝ) ≤ D * 2 ^ k)
    (hcl : ∀ᶠ k in atTop, g k (m₁ k) ≤ C * s k)
    (hdiv : Tendsto (fun k => g k 0 / s k) atTop atTop) :
    ∀ᶠ k in atTop, ¬ g k 0 * Real.exp (-(2 * m₁ k * (U / 2 ^ k))) ≤ g k (m₁ k) := by
  filter_upwards [hD, hcl, hdiv.eventually_gt_atTop (Real.exp (2 * D * U) * C)] with k h1 h2 h3 hw
  have hc := contact_le_of_window hU (hnn k) h1 hw
  rw [lt_div_iff₀ (hs k)] at h3
  have h4 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (2 * D * U)).le
  nlinarith

/-- **One amplitude at one physical separation gives no window floor.** `G_k(n) = e^{−2nk/2^k}` is log-convex and
non-negative, reads at least `a⁸`, `a = 2^{−k}`, at the fixed physical gap `2^k`, and for every `U` eventually fails
the window inequality at every gap. DERIVED: `2` the two steps of one gap and the window base; `3` a bound on `e`; `8`
the exponent of the model; `1` the least gap; `0` the contact gap. -/
theorem amplitude_not_window :
    ∃ G : ℕ → ℕ → ℝ, (∀ k n, 0 ≤ G k n) ∧ (∀ k, LogConvexSeq (G k)) ∧
      (∀ k, ((1 : ℝ) / 2 ^ k) ^ 8 ≤ G k (2 ^ k)) ∧
      ∀ U : ℝ, ∀ᶠ k in atTop, ∀ m : ℕ, 1 ≤ m →
        ¬ G k 0 * Real.exp (-(2 * m * (U / 2 ^ k))) ≤ G k m := by
  refine ⟨fun k n => Real.exp (-(2 * n * ((k : ℝ) / 2 ^ k))), fun _ _ => (Real.exp_pos _).le, ?_, ?_, ?_⟩
  · intro k n
    show Real.exp _ ^ 2 ≤ Real.exp _ * Real.exp _
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    push_cast
    ring
  · intro k
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have e : Real.exp (-(2 * ((2 ^ k : ℕ) : ℝ) * ((k : ℝ) / 2 ^ k))) = Real.exp (-2) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    show ((1 : ℝ) / 2 ^ k) ^ 8 ≤ Real.exp (-(2 * ((2 ^ k : ℕ) : ℝ) * ((k : ℝ) / 2 ^ k)))
    rw [e]
    have e2 : ((1 : ℝ) / 2 ^ k) ^ 8 = ((1 / 2) ^ 8) ^ k := by
      rw [one_div, ← inv_pow, ← pow_mul, ← pow_mul, one_div, mul_comm]
    rw [e2]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have h3 : Real.exp 2 ≤ 3 * 3 := by
      have h1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have e3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [e3]
      exact mul_le_mul h1 h1 (Real.exp_pos _).le (by norm_num)
    rw [Real.exp_neg, ← one_div]
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (Real.exp_pos _) (by linarith [show (9 : ℝ) ≤ 2 ^ 8 by norm_num])
  · intro U
    obtain ⟨k0, hk0⟩ := exists_nat_gt U
    filter_upwards [eventually_ge_atTop k0] with k hk m hm hw
    have hkr : U < k := lt_of_lt_of_le hk0 (by exact_mod_cast hk)
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul] at hw
    have h1 := Real.exp_le_exp.mp hw
    have h2 : 2 * (m : ℝ) * ((k : ℝ) / 2 ^ k) ≤ 2 * m * (U / 2 ^ k) := by linarith
    have h3 : (k : ℝ) / 2 ^ k ≤ U / 2 ^ k := le_of_mul_le_mul_left h2 (by positivity)
    have h4 := (div_le_div_iff_of_pos_right h2k).mp h3
    linarith

/-- **A window floor gives no amplitude.** `H_k(n) = 2^{−9k} e^{−2n/2^k}` meets the window inequality at `U = 1` at gap
`1`, at every step, and no floor `c a⁸`, `a = 2^{−k}`, at any gap. DERIVED: `2` the two steps of one gap and the window
base; `9`, `8` the exponents of the model; `1` the least gap; `0` the contact gap. -/
theorem window_not_amplitude :
    ∃ H : ℕ → ℕ → ℝ, (∀ k n, 0 ≤ H k n) ∧ (∀ k, LogConvexSeq (H k)) ∧
      (∀ k, H k 0 * Real.exp (-(2 * (1 : ℕ) * ((1 : ℝ) / 2 ^ k))) ≤ H k 1) ∧
      ∀ c : ℝ, 0 < c → ∀ᶠ k in atTop, ∀ m : ℕ, ¬ c * ((1 : ℝ) / 2 ^ k) ^ 8 ≤ H k m := by
  refine ⟨fun k n => ((1 : ℝ) / 2 ^ k) ^ 9 * Real.exp (-(2 * n * ((1 : ℝ) / 2 ^ k))),
    fun _ _ => by positivity, ?_, ?_, ?_⟩
  · intro k n
    show (_ * Real.exp _) ^ 2 ≤ (_ * Real.exp _) * (_ * Real.exp _)
    rw [mul_pow, ← Real.exp_nat_mul]
    have e : ∀ A B C : ℝ, A * Real.exp B * (A * Real.exp C) = A ^ 2 * Real.exp (B + C) := by
      intro A B C
      rw [Real.exp_add]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_of_eq ?_)) (by positivity)
    push_cast
    ring
  · intro k
    simp
  · intro c hc
    have ht : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    filter_upwards [ht.eventually (gt_mem_nhds hc)] with k hk m hfl
    have h2k : (0 : ℝ) < 1 / 2 ^ k := by positivity
    have h8 : (0 : ℝ) < (1 / 2 ^ k) ^ 8 := by positivity
    have hle : Real.exp (-(2 * m * ((1 : ℝ) / 2 ^ k))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ 2 * m * (1 / 2 ^ k) := by positivity
      linarith
    have h1 : c * ((1 : ℝ) / 2 ^ k) ^ 8 ≤ ((1 : ℝ) / 2 ^ k) ^ 9 := by
      refine hfl.trans ?_
      calc _ ≤ ((1 : ℝ) / 2 ^ k) ^ 9 * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = _ := mul_one _
    have e : ((1 : ℝ) / 2 ^ k) ^ 9 = (1 / 2) ^ k * ((1 : ℝ) / 2 ^ k) ^ 8 := by
      have e' : (1 : ℝ) / 2 ^ k = (1 / 2) ^ k := (one_div_pow 2 k).symm
      rw [e']
      ring
    rw [e] at h1
    exact absurd (le_of_mul_le_mul_right h1 h8) (not_le.mpr hk)

/-- **A non-zero limit is an amplitude along its filter.** DERIVED: `0` the excluded value; `2` the half of the
limit. -/
theorem amplitude_of_ne {u : ℕ → ℝ} {L : ℝ} {l : Filter ℕ} (hL : L ≠ 0) (h : Tendsto u l (𝓝 L)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in l, c ≤ |u k| :=
  ⟨|L| / 2, half_pos (abs_pos.mpr hL),
    (h.abs.eventually (lt_mem_nhds (half_lt_self (abs_pos.mpr hL)))).mono fun _ hk => hk.le⟩

end Scale

/-! ## 3. The reflected read of the periodic state -/

section Read

variable {N : ℕ} [NeZero N]

/-- The positive half-space algebra of the plane `x₀ = 0`. DERIVED: `0` the plane. -/
abbrev HS (N : ℕ) [NeZero N] : Submodule ℝ C(Cfg N, ℝ) :=
  HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0

/-- A reflected read is non-negative. DERIVED: `0` the sign. -/
theorem gP_nonneg (β : ℝ) {X : C(Cfg N, ℝ)} (hX : X ∈ HS N) (m : ℕ) : 0 ≤ gP β X m := by
  rw [← gapRead_eq_P]
  exact gapRead_nonneg (reflShiftP β) hX m

/-- A reflected read is log-convex. DERIVED: no numeral. -/
theorem gP_logConvex (β : ℝ) {X : C(Cfg N, ℝ)} (hX : X ∈ HS N) : LogConvexSeq (gP (N := N) β X) := by
  intro n
  have h := gapRead_logConvex (reflShiftP (N := N) β) hX n
  simpa only [gapRead_eq_P] using h

/-- A reflected read is at most `‖X‖²`. DERIVED: `2` the square. -/
theorem gP_le_norm (β : ℝ) (X : C(Cfg N, ℝ)) (m : ℕ) : gP β X m ≤ ‖X‖ ^ 2 := by
  have h := (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β).abs_le_norm
    (LatticeReflection.ireflObs 0 0 X * transObs ((2 * m) • eT) X)
  refine (le_abs_self _).trans (h.trans ?_)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro U
  rw [ContinuousMap.mul_apply, LatticeReflection.ireflObs_apply, transObs_apply, norm_mul, sq]
  exact mul_le_mul (X.norm_coe_le_norm _) (X.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

/-- **A reflected read is antitone in the gap.** DERIVED: no numeral. -/
theorem gP_antitone (β : ℝ) {X : C(Cfg N, ℝ)} (hX : X ∈ HS N) : Antitone (gP (N := N) β X) :=
  antitone_nat_of_succ_le (step_le_of_bounded (gP_nonneg β hX) (gP_logConvex β hX) (gP_le_norm β X))

/-- **The covariance at any reflected gap is at most the covariance at gap `0`.** DERIVED: `2` the two steps of one
gap; `0` the contact gap. -/
theorem cov_far_le_contact (β : ℝ) {X : C(Cfg N, ℝ)} (hX : X ∈ HS N) (m : ℕ) :
    |stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β) (LatticeReflection.ireflObs 0 0 X)
        (transObs ((2 * m) • eT) X)|
      ≤ |stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
          (LatticeReflection.ireflObs 0 0 X) X| := by
  have hc := connP_mem β hX
  have e0 := gP_conn (N := N) β X 0
  rw [mul_zero, zero_smul, transObs_zero] at e0
  rw [← gP_conn, ← e0, abs_of_nonneg (gP_nonneg β hc _), abs_of_nonneg (gP_nonneg β hc _)]
  exact gP_antitone β hc (Nat.zero_le m)

variable (N) in
/-- **The window floor conjunct of `ReadPos.ReflFloorAt`.** DERIVED: `2` the two steps of one gap and the window
base; `1` the least gap; `0` the contact gap. -/
def WindowFloorAt (βs : ℕ → ℝ) (U : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ m₁ : ℕ, 1 ≤ m₁ ∧
    gE (N := N) (βs k) 0 * Real.exp (-(2 * m₁ * (U / 2 ^ k))) ≤ gE (N := N) (βs k) m₁

variable (N) in
/-- **The defect conjunct of `ReadPos.ReflFloorAt`.** DERIVED: `2` the two steps of one gap; `1` the unit
fraction. -/
def DefectAt (βs : ℕ → ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ c : ℝ, c < 1 ∧ ∀ᶠ m in atTop,
    |stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k)) (BandClose.mirrorDefect (N := N))
      (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))| ≤ c * |gE (N := N) (βs k) m|

/-- **`ReflFloorAt` is the window floor and the defect bound.** DERIVED: no numeral. -/
theorem reflFloorAt_iff {βs : ℕ → ℝ} {U : ℝ} :
    ReadPos.ReflFloorAt N βs U ↔ WindowFloorAt N βs U ∧ DefectAt N βs := by
  unfold ReadPos.ReflFloorAt WindowFloorAt DefectAt
  rw [← eventually_and]

variable (N) in
/-- **The far slope of the tensor read at level `U`**: eventually, a positive read and a chord at rate `U/2^k`. It
does not name the contact read. DERIVED: `2` the two steps of one gap and the window base; `1` the least chord; `0` the
sign. -/
def SlopeAt (βs : ℕ → ℝ) (U : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ s w : ℕ, 1 ≤ w ∧ 0 < gE (N := N) (βs k) s ∧
    gE (N := N) (βs k) s * Real.exp (-(2 * w * (U / 2 ^ k))) ≤ gE (N := N) (βs k) (s + w)

variable (N) in
/-- **Two reads of the tensor read in one normalisation** `s`: a floor at `m₂`, a ceiling at `m₁`, the gaps `w 2^k`
apart. At `s k = a_k⁸` these are physical reads when `m₁`, `m₂` are of order `2^k`; the implication does not read
that order. DERIVED: `2` the window base. -/
def PhysBand (βs s : ℕ → ℝ) (m₁ m₂ : ℕ → ℕ) (c C w : ℝ) : Prop :=
  ∀ᶠ k in atTop, w * 2 ^ k + m₁ k ≤ m₂ k ∧ c * s k ≤ gE (N := N) (βs k) (m₂ k) ∧
    gE (N := N) (βs k) (m₁ k) ≤ C * s k

/-- The centred tensor reading is a half-space observable. DERIVED: no numeral. -/
theorem connE_mem (β : ℝ) :
    connP β (tensorEnergyG (MassGap.SUN.SU N) 0) ∈ HS N :=
  connP_mem β BandClose.tensorEnergyG_zero_mem

/-- **`PhysBand` gives the slope**: `s` cancels, and the positivity of the near read is `gP_antitone`. DERIVED: `2`
the two steps of one gap; `1` the least chord; `0` the signs. -/
theorem slope_of_physBand {βs s : ℕ → ℝ} {m₁ m₂ : ℕ → ℕ} {c C w U : ℝ} (hs : ∀ k, 0 < s k)
    (hc : 0 < c) (hC : 0 < C) (hw : 0 < w) (hU0 : 0 ≤ U) (hU : Real.log (C / c) ≤ 2 * w * U)
    (h : PhysBand N βs s m₁ m₂ c C w) : SlopeAt N βs U := by
  filter_upwards [h] with k ⟨hgap, hfl, hcl⟩
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hle : m₁ k ≤ m₂ k := by
    have h1 : (m₁ k : ℝ) ≤ m₂ k := by nlinarith [mul_pos hw h2k]
    exact_mod_cast h1
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hdr : w * 2 ^ k ≤ (d : ℝ) := by
    rw [hd] at hgap
    push_cast at hgap
    linarith
  have hd1 : 1 ≤ d := by
    have h1 : (0 : ℝ) < d := lt_of_lt_of_le (mul_pos hw h2k) hdr
    exact_mod_cast h1
  have hfar : 0 < gE (N := N) (βs k) (m₂ k) := lt_of_lt_of_le (mul_pos hc (hs k)) hfl
  have hnear : 0 < gE (N := N) (βs k) (m₁ k) :=
    lt_of_lt_of_le hfar (gP_antitone (βs k) (connE_mem (βs k)) hle)
  refine ⟨m₁ k, d, hd1, hnear, ?_⟩
  rw [← hd]
  exact window_of_ratio (hs k) hc hC hU0 hfl hcl hdr hU

/-- **The slope below `U` gives the window floor at `U`.** DERIVED: `0` the sign of the coupling and the contact
gap; `2` the window base. -/
theorem windowFloorAt_of_slope [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U' U : ℝ} (hβ : ∀ᶠ k in atTop, 0 ≤ βs k)
    (hlt : U' < U) (h : SlopeAt N βs U') : WindowFloorAt N βs U := by
  filter_upwards [hβ, h] with k hk ⟨s, w, hw, hp, hsl⟩
  have hc := connE_mem (N := N) (βs k)
  exact window_of_slope (gP_nonneg _ hc) (gP_logConvex _ hc) (ReadPos.gE_zero_pos hk) hw hp
    (div_lt_div_of_pos_right hlt (by positivity)) hsl

/-- **The window floor at `U` gives the slope at `U`.** DERIVED: `0` the sign of the coupling and the contact gap;
`1` the unit chord; `2` the window base. -/
theorem slope_of_windowFloorAt [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U : ℝ} (hβ : ∀ᶠ k in atTop, 0 ≤ βs k)
    (h : WindowFloorAt N βs U) : SlopeAt N βs U := by
  filter_upwards [hβ, h] with k hk ⟨m₁, hm, hw⟩
  have hc := connE_mem (N := N) (βs k)
  have hs := slope_of_window (gP_nonneg _ hc) (gP_logConvex _ hc) (ReadPos.gE_zero_pos hk) hm hw
    le_rfl 1
  exact ⟨m₁, 1, le_rfl, hs.1, hs.2⟩

end Read

/-! ## 4. The macroscopic read -/

section Macro

variable {N : ℕ} [NeZero N]

/-- **The macroscopic observable of step `k`**: the flowed smeared monomial. DERIVED: no numeral. -/
def macroX (Φ : Flow N) (P : Mono N) (k : ℕ) : C(Cfg N, ℝ) :=
  prodSmear (dySpacing N k) (Φ.mono k P)

/-- A margin monomial lies in the half-space algebra eventually. DERIVED: `0` the plane. -/
theorem macroX_mem {Φ : Flow N} {r : ℝ} (hpos : Φ.PosPreserving 0 r) (Q : MarginMono N 0 r) :
    ∀ᶠ k in atTop, macroX Φ Q.1 k ∈ HS N := by
  obtain ⟨d, hd, hrd, hP⟩ := Q.2
  have h : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1,
      smear (dySpacing N k) (Φ.map k (Q.1.2 i).1).1 (Q.1.2 i).2 ∈ HS N :=
    eventually_all.mpr fun i => hpos _ _ d hd hrd (hP i)
  filter_upwards [h] with k hk
  exact HalfSpaceAlgebra.halfSpaceAlg_prod_mem 0 0 Finset.univ _ fun i _ => hk i

/-- **`PhysFloor`: the floor on the macroscopic reflected read at the gaps `gap`, along `l`.** DERIVED: `2` the two
steps of one gap; `0` the plane. -/
def PhysFloor (Φ : Flow N) (P : Mono N) (gap : ℕ → ℕ) (c : ℝ) (l : Filter ℕ) : Prop :=
  ∀ᶠ k in l, c ≤ |stateCov (stateK (NeZero.ne N) k)
    (LatticeReflection.ireflObs 0 0 (macroX Φ P k)) (transObs ((2 * gap k) • eT) (macroX Φ P k))|

/-- **`PhysFloor ⇒ RegConnectedNonzero`**, at any gaps. DERIVED: `0` the plane and the sign of `c`. -/
theorem regConnected_of_physFloor {Φ : Flow N} (hB : UniformBoundF (NeZero.ne N) Φ)
    {A : Set (LField (MassGap.SUN.SU N))} {r : ℝ} (hpos : Φ.PosPreserving 0 r) (Q : RMono N A 0 r)
    {gap : ℕ → ℕ} {c : ℝ} (hc : 0 < c) (h : PhysFloor Φ Q.1.1 gap c (ultra : Filter ℕ)) :
    RegConnectedNonzero (NeZero.ne N) Φ A 0 r := by
  refine (RegNontrivial.regConnected_iff_floor (NeZero.ne N) Φ hB A 0 r).2 ⟨Q, c, hc, ?_⟩
  filter_upwards [h, (macroX_mem hpos Q.1).filter_mono ultra_le] with k hk hm
  exact hk.trans (cov_far_le_contact _ hm (gap k))

/-- **`RegConnectedNonzero` is `PhysFloor` at gap `0` of some regular monomial.** DERIVED: `0` the contact gap and
the sign of `c`. -/
theorem regConnected_iff_physFloor {Φ : Flow N} (hB : UniformBoundF (NeZero.ne N) Φ)
    {A : Set (LField (MassGap.SUN.SU N))} {r : ℝ} :
    RegConnectedNonzero (NeZero.ne N) Φ A 0 r ↔ ∃ Q : RMono N A 0 r, ∃ c : ℝ, 0 < c ∧
      PhysFloor Φ Q.1.1 (fun _ => 0) c (ultra : Filter ℕ) := by
  rw [RegNontrivial.regConnected_iff_floor (NeZero.ne N) Φ hB A 0 r]
  refine exists_congr fun Q => exists_congr fun c => and_congr_right fun _ => ?_
  unfold PhysFloor macroX
  simp only [mul_zero, zero_smul, transObs_zero]

/-- **The contact read of a monomial has a ceiling along `ultra`**, from `UniformBoundF`. DERIVED: `0` the plane;
`1` the shift of the bound; `2` the square. -/
theorem contact_ceiling {Φ : Flow N} (hB : UniformBoundF (NeZero.ne N) Φ) (P : Mono N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in (ultra : Filter ℕ), |stateCov (stateK (NeZero.ne N) k)
      (LatticeReflection.ireflObs 0 0 (macroX Φ P k)) (macroX Φ P k)| ≤ C := by
  have hN := NeZero.ne N
  have hcov : ∀ k, stateCov (stateK hN k) (LatticeReflection.ireflObs 0 0 (macroX Φ P k)) (macroX Φ P k)
      = latSF hN Φ k (pairFam 0 P P) - latSF hN Φ k (pairFam 0 (emptyMargin N 0 0).1 P) ^ 2 := by
    intro k
    rw [RegNontrivial.latSF_conn hN Φ 0 0 k P]
    exact (RegNontrivial.connAt_eq_cov _ (dySpacing_pos (one_le_of_ne_zero hN) k) 0
      (MassGap.PeriodicState.periodicState_reflInvariant hN _ 0 0) _).symm
  have hlim := ((tendsto_contSF hN Φ hB (pairFam 0 P P)).sub
    ((tendsto_contSF hN Φ hB (pairFam 0 (emptyMargin N 0 0).1 P)).pow 2)).abs
  obtain ⟨L, hL⟩ : ∃ L : ℝ, Tendsto (fun k => |stateCov (stateK hN k)
      (LatticeReflection.ireflObs 0 0 (macroX Φ P k)) (macroX Φ P k)|) (ultra : Filter ℕ) (𝓝 L) :=
    ⟨_, hlim.congr fun k => by rw [hcov]⟩
  refine ⟨|L| + 1, by positivity, ?_⟩
  filter_upwards [hL.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self L) (lt_add_one _)))] with k hk
  exact hk.le

/-- **`PhysFloor` at physical gaps gives the window inequality of the same macroscopic read**, at a measured `U`.
`g_k = gP (dyBeta k) (connP (dyBeta k) X_k)`. DERIVED: `2` the two steps of one gap and the window base; `0` the
contact gap and the signs; `1` the unit scale. -/
theorem macro_window {Φ : Flow N} (hB : UniformBoundF (NeZero.ne N) Φ) {r : ℝ}
    (hpos : Φ.PosPreserving 0 r) (Q : MarginMono N 0 r) {gap : ℕ → ℕ} {c w : ℝ} (hc : 0 < c)
    (hw : 0 < w) (hgap : ∀ᶠ k in (ultra : Filter ℕ), w * 2 ^ k ≤ gap k)
    (h : PhysFloor Φ Q.1 gap c (ultra : Filter ℕ)) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ᶠ k in (ultra : Filter ℕ),
      gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
          (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1 k)) 0
          * Real.exp (-(2 * gap k * (U / 2 ^ k)))
        ≤ gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
          (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1 k)) (gap k) := by
  obtain ⟨C, hC, hcl⟩ := contact_ceiling (Φ := Φ) hB Q.1
  have hU0 : 0 ≤ |Real.log (C / c)| / (2 * w) := by positivity
  refine ⟨_, hU0, ?_⟩
  filter_upwards [h, hcl, hgap, (macroX_mem hpos Q).filter_mono ultra_le] with k hk hu hgk hm
  have hcm := connP_mem (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) hm
  have e0 := gP_conn (N := N) (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1 k) 0
  rw [mul_zero, zero_smul, transObs_zero] at e0
  have efar := gP_conn (N := N) (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1 k) (gap k)
  have hfl : c * 1 ≤ gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
      (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1 k)) (gap k) := by
    rw [mul_one, ← abs_of_nonneg (gP_nonneg _ hcm (gap k)), efar]
    exact hk
  have hup : gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
      (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1 k)) 0 ≤ C * 1 := by
    rw [mul_one, ← abs_of_nonneg (gP_nonneg _ hcm 0), e0]
    exact hu
  refine window_of_ratio one_pos hc hC hU0 hfl hup hgk ?_
  rw [mul_div_cancel₀ _ (by positivity)]
  exact le_abs_self _

/-- **`PhysFloor` at physical gaps gives both reads**: non-triviality and the window inequality of the same read.
DERIVED: `0` the plane. -/
theorem physFloor_fold {Φ : Flow N} (hB : UniformBoundF (NeZero.ne N) Φ)
    {A : Set (LField (MassGap.SUN.SU N))} {r : ℝ} (hpos : Φ.PosPreserving 0 r) (Q : RMono N A 0 r)
    {gap : ℕ → ℕ} {c w : ℝ} (hc : 0 < c) (hw : 0 < w)
    (hgap : ∀ᶠ k in (ultra : Filter ℕ), w * 2 ^ k ≤ gap k)
    (h : PhysFloor Φ Q.1.1 gap c (ultra : Filter ℕ)) :
    RegConnectedNonzero (NeZero.ne N) Φ A 0 r ∧
      ∃ U : ℝ, 0 ≤ U ∧ ∀ᶠ k in (ultra : Filter ℕ),
        gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
            (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1.1 k)) 0
            * Real.exp (-(2 * gap k * (U / 2 ^ k)))
          ≤ gP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k)
            (connP (dyBeta (one_le_of_ne_zero (NeZero.ne N)) k) (macroX Φ Q.1.1 k)) (gap k) :=
  ⟨regConnected_of_physFloor hB hpos Q hc h, macro_window hB hpos Q.1 hc hw hgap h⟩

variable (N) in
/-- **Macroscopic reads along a tower at level `U`**: half-space observables `X k`, a floor `c` at gaps at least
`w 2^k`, a ceiling `C` at gap `0`, with `log(C/c) ≤ 2wU`, and comparability of the read with the diagonal tensor read at
each step. DERIVED: `2` the two steps of one gap and the window base; `0` the signs and the contact gap. -/
def MacroReadsAt (βs : ℕ → ℝ) (U : ℝ) : Prop :=
  ∃ (X : ℕ → C(Cfg N, ℝ)) (gap : ℕ → ℕ) (c C w : ℝ), 0 < c ∧ 0 < w ∧
    Real.log (C / c) ≤ 2 * w * U ∧ ∀ᶠ k in atTop, X k ∈ HS N ∧ w * 2 ^ k ≤ gap k ∧
      c ≤ gP (βs k) (connP (βs k) (X k)) (gap k) ∧ gP (βs k) (connP (βs k) (X k)) 0 ≤ C ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ m in atTop, a * |gP (βs k) (connP (βs k) (X k)) m| ≤
        |stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k))
          (tensorEnergyG (MassGap.SUN.SU N) 0)
          (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))|

/-- **The window upper bound from macroscopic reads.** `BandClose.windowUpper_of_tensorReads` with the observable
depending on the step; the contact positivity follows from the floor (`gP_antitone`). DERIVED: `2` the two steps of one
gap and the window base; `1` the least gap and the unit scale; `0` the contact gap and the signs. -/
theorem windowUpper_of_macroReads [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U : ℝ} (hU : 0 ≤ U)
    (h : MacroReadsAt N βs U) : BandUpper.WindowUpper N βs U := by
  obtain ⟨X, gap, c, C, w, hc, hw, hlog, hev⟩ := h
  filter_upwards [hev] with k ⟨hX, hgap, hfl, hcl, hcmp⟩
  have hXc := connP_mem (βs k) hX
  set g : ℕ → ℝ := gP (βs k) (connP (βs k) (X k)) with hg
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hgp : 0 < g (gap k) := lt_of_lt_of_le hc hfl
  have hm₁ : 1 ≤ gap k := by
    have h1 : (0 : ℝ) < gap k := lt_of_lt_of_le (mul_pos hw h2k) hgap
    exact_mod_cast h1
  have hg0 : 0 < g 0 := lt_of_lt_of_le hgp (gP_antitone (βs k) hXc (Nat.zero_le _))
  have hC : 0 < C := lt_of_lt_of_le hg0 hcl
  have hwin : g 0 * Real.exp (-(2 * gap k * (U / 2 ^ k))) ≤ g (gap k) :=
    window_of_ratio one_pos hc hC hU (by rwa [mul_one]) (by rwa [mul_one]) hgap hlog
  have hlc : ∀ m, gap k ≤ m → g (gap k) ^ m ≤ g m ^ gap k * g 0 ^ (m - gap k) := fun m hm =>
    periodic_far_ge (βs k) hXc hm
  have hM := BandClose.measMassOfG_le_of_logConvex_cmp (E := tensorEnergyG (MassGap.SUN.SU N))
    (0 : ISite) (z := fun m => (2 * m) • eT) BandClose.snormG_eT hm₁ hg0 hgp hlc hcmp
  rw [← mUG_SU]
  refine le_trans hM (ENNReal.ofReal_le_ofReal ?_)
  have hl := Real.log_le_log (mul_pos hg0 (Real.exp_pos _)) hwin
  rw [Real.log_mul hg0.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have hm1r : (0 : ℝ) < gap k := by exact_mod_cast hm₁
  rw [div_le_iff₀ (by positivity), Real.log_div hg0.ne' hgp.ne']
  linarith

end Macro

/-! ## 5. The amplitude inside the bundle -/

section Bundle

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

open MassGap.ClayTreeG MassGap.ClayStatement MassGap.ClayStatementG

/-- **A non-zero separated reading of the sector is an amplitude along `ultra`**, in the composites' normalisation.
At the two-point family of the trace, `TwoPointKernelG` reads such a limit as an integral of `Gk`. The floor is along
`ultra` only. DERIVED: `0` the excluded value. -/
theorem amplitude_of_conv (S : Sched G) (ρ : RenormMixG G) (hC : SepConvG S ρ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) (h : contTG S ρ F ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in (ultra : Filter ℕ), c ≤ |latTG S ρ k F| :=
  amplitude_of_ne h (hC ι F hF)

end Bundle

end MassGap.FloorFold

end

#print axioms MassGap.FloorFold.growth
#print axioms MassGap.FloorFold.step_le_of_bounded
#print axioms MassGap.FloorFold.far_of_slope
#print axioms MassGap.FloorFold.window_of_slope
#print axioms MassGap.FloorFold.slope_of_window
#print axioms MassGap.FloorFold.window_of_ratio
#print axioms MassGap.FloorFold.contact_le_of_window
#print axioms MassGap.FloorFold.not_window_of_contact
#print axioms MassGap.FloorFold.amplitude_not_window
#print axioms MassGap.FloorFold.window_not_amplitude
#print axioms MassGap.FloorFold.amplitude_of_ne
#print axioms MassGap.FloorFold.gP_nonneg
#print axioms MassGap.FloorFold.gP_logConvex
#print axioms MassGap.FloorFold.gP_le_norm
#print axioms MassGap.FloorFold.gP_antitone
#print axioms MassGap.FloorFold.cov_far_le_contact
#print axioms MassGap.FloorFold.reflFloorAt_iff
#print axioms MassGap.FloorFold.connE_mem
#print axioms MassGap.FloorFold.slope_of_physBand
#print axioms MassGap.FloorFold.windowFloorAt_of_slope
#print axioms MassGap.FloorFold.slope_of_windowFloorAt
#print axioms MassGap.FloorFold.macroX_mem
#print axioms MassGap.FloorFold.regConnected_of_physFloor
#print axioms MassGap.FloorFold.regConnected_iff_physFloor
#print axioms MassGap.FloorFold.contact_ceiling
#print axioms MassGap.FloorFold.macro_window
#print axioms MassGap.FloorFold.physFloor_fold
#print axioms MassGap.FloorFold.windowUpper_of_macroReads
#print axioms MassGap.FloorFold.amplitude_of_conv
