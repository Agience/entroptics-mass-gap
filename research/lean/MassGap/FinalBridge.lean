import Mathlib
import MassGap.WindowFreq
import MassGap.GapReadsTensorProved

/-!
# MassGap.FinalBridge — a bridge from the frequency read: the mass in aperture units does not stall

The candidate bridge `B`, read from `FreqRead`, `BandShell` and `WindowFreq`: the mass read in units of the
aperture does not stall. This module states `B`, proves what follows from it without a template, and records
that `B` replaces `StrongEnd N` only under a named template. It maps `B` input by input against the
inputs of the root `StrongAnchor.clayStatementOf_of_noStall` / `ProxBound.clayStatementOf_of_proxBound`.
Declarations are in the namespace `MassGap.FinalBridge`.

The second factor of the template, `MassGivesGap` (a positive tensor-channel decay rate gives the transfer gap), is not a standard theorem: the tensor rate bounds the transfer gap from above, so the implication needs the tensor channel to overlap the lowest state above the vacuum. It is a lattice working assumption and is not proved here.

## 1. The bridge `B` (stated)

`apertureRead N β w = 2^w · mU β`: the measured tensor mass of the periodic state at coupling `β`
(`MeasuredSpacing.mU`, the supremum of the decay rates of the tensor reading, in `[0, ∞]`), read in units of the
aperture `2^w`. This is the read `windowReading = 2^k m′(β_k)` of `ScaleLightCone` §3 at one fixed coupling,
and the read `A ω₀ = A m` of `FreqRead.full_rate` on the interacting state.

* `ReadOpens N β`: the read opens without bound as the aperture opens, `2^w mU β → ∞`. It does not stall.
* **`MassReadOpens N` (the bridge `B`)**: `ReadOpens N β` at every coupling `β ≥ 0`.

Nothing is chosen: the rate is the state's own (`measMassOf` is a supremum over the decay rates the reading
has), the aperture is the window `2^w`, and the statement carries no threshold. `readOpens_iff`: at one `β`,
`ReadOpens N β ↔ 0 < mU β`. `B` is, plainly, positivity of the lattice mass `mU β` (the supremum of the tensor
reading's decay rates) at every coupling `β ≥ 0`, written in aperture units: `2^w · mU β → ∞` exactly when
`0 < mU β` (`readOpens_iff`). It adds no content beyond that positivity; the aperture form is the same statement
as a growing read.

## 2. Load tests (proved)

* `freeRead_opens_iff`: at the free field, `2^w m → ∞` exactly when `m > 0` (`m ≥ 0`); `freeRead_massless_stalls`:
  the massless read stays at `0`. `cross_opens_iff`: the in-aperture read `FreqRead.cross m c (2^w)` opens
  exactly when `m ≠ 0`; at `m = 0` it is `|c|` at every aperture (`FreqRead.cross_massless`). So `B` fails at
  the massless free field and holds at the massive one, in both the rest-sector and the in-aperture form.
* `free_readOpens_iff_vanishing`: at the free one-dimensional chain, the read opens exactly when the doubling
  defect vanishes (`WindowFreq.freeWindow_vanishes_iff`). This is the free instance of the template of §3,
  proved in closed form.
* `readOpens_anchor`, `exists_pos_readOpens` (non-vacuity on the tree's objects): `B` holds at every coupling
  of an actual interval `[0, β₀)`, `β₀ > 0` (the strong anchor and the proved link `GapReadsTensor`).

## 3. The map against `StrongEnd` / `NoStall` (proved, and proved under a named template)

Proved, no template:

* `mU_pos_of_clayGap`, `mU_pos_of_gapAt`: a periodic Clay gap at `β` gives `0 < mU β`
  (`GapReadsTensorProved.gapReadsTensor`).
* `readOpens_of_vanishes`: the vanishing read at `β` gives `ReadOpens N β` (vanishing ⇒ gap ⇒ mass).
* **`massReadOpens_of_noStall`**: `NoStall N ⇒ B`. `B` is implied by the existing input.
* `frequently_readOpens_of_strongEnd`: `StrongEnd N ⇒` `ReadOpens` frequently at `∞`.

The template. `MassGivesVanishing N`: at every `β ≥ 0`, `0 < mU β` gives the vanishing read of the window
coupling. This is Lüscher's finite-volume statement (the finite-size part of the free energy of a massive theory
is `O(e^{−m L})`), proved by Borgs–Kotecký where a convergent cluster or contour expansion holds; it is not
proved for the Wilson torus at every `β`. Its free one-dimensional instance is proved
(`free_readOpens_iff_vanishing`). It factors exactly (`massGivesVanishing_iff`) into
`WindowFreq.GapGivesVanishing` (gap ⇒ vanishing, the same Lüscher template) and `MassGivesGap` (a positive
decay rate of the one tensor channel gives the transfer gap on the whole vacuum complement). The second factor
is not a standard theorem: by the spectral theorem for the reflection-positive transfer, the tensor channel's
rate is the bottom of its own spectral measure, which bounds the transfer gap from above, not below; it gives
the gap only if the tensor channel overlaps the lowest state above the vacuum. That overlap is the usual lattice
working assumption, not a proved fact.

* `gapGivesVanishing_of_massGivesVanishing`, `massGivesVanishing_of_gap`, **`massGivesVanishing_iff`**.
* **`noStall_of_massReadOpens`**: under the template, `B ⇒ NoStall N`; **`massReadOpens_iff_noStall`**: under
  the template, `B ↔ NoStall N`.
* `strongEnd_of_massReadOpens`; **`strongEnd_iff_frequently_readOpens`**: under the template, `StrongEnd N` is
  `ReadOpens` frequently at `∞`.

## 4. The map against `ZoomSettlesUV` (proved: the half `B` reads is already in the tree)

`ZoomSettlesUV N βs` asks the tower read `windowReading N βs k = 2^k m′(β_k)` to be eventually finite and to
settle with a rate. "Does not stall" along the tower is the lower half of that read. It is proved:

* **`windowReading_floor`**: along every coupling tower at every window coupling near `0⁺`, wherever the
  measured mass is eventually finite, `log 2 ≤ windowReading N βs k` eventually
  (`CouplingTower.le_window_mass` with the proved `GapReadsTensorProved.confinedAt`).
  `windowReading_floor_of_zoomSettlesUV`: under `ZoomSettlesUV` (its finiteness conjunct) the floor holds.
* `floor_not_settling` (load test): a read that is non-decreasing and bounded below by any level `b` need not
  converge (`q k = b + k`, a counterexample choice), so the floor, and the monotone form of `FreqRead` §5, do not
  give `ZoomSettlesUV`, which gives convergence (`ScaleLightCone.uvConverges_of_zoomSettlesUV`).

Plainly: `B` does not touch `ZoomSettlesUV`. The tower form of "no stall" is already proved in the basin; what
`ZoomSettlesUV` carries is the other half, no runaway (an upper bound) and settling with a rate. That is the
ultraviolet side (Bałaban's block-spin control, `ScaleLightCone` §1's Lieb–Robinson template), not read by `B`.

## 5. The map against the 9 conjuncts of `ProxBound.CoreInputsAlongWPB` (untouched, argued)

`B` is a statement about one function, `β ↦ mU β`, the decay rate of one reading of the infinite-volume
periodic state at fixed coupling. Every conjunct of the bundle reads the flows `Wf` and coefficients `cf` of the
flowed composites along `cpl βs` as the flow time `s → 0⁺`, or the bare states along the tower at coincident or
finitely separated points; none reads `mU`, and none is a decay-rate statement (argued from their definitions,
not checked by a Lean statement). Every 'Untouched' entry is an argument in prose; none is a Lean statement.
Conjunct by conjunct:

* `ApertureBridge`: moment bounds of the flowed channels, the plaquette normalisation `O(a_k⁴)` and the
  asymptotic-freedom form of the two-point kernel as `r → 0⁺`. Ultraviolet and normalisation. Untouched.
* `ExpandMatch`: the small-flow-time expansion matching `latC` with `msLat` (tail-read in the step,
  `ProxBound.tailRead_expandMatchOf`). Ultraviolet. Untouched.
* `ProxBound`: a supremum-norm bound on the flowed proxies at the first step of every separation. Normalisation.
  Untouched.
* `ZoomSettling`: settling of the relative connected read along the zoom at fixed separation, with no decay
  factor in the separation (`ScaleLightCone` §5). Ultraviolet; a mass enters nowhere. Untouched.
* `FlowCovLim`, `FlowWard`: under `ExpandMatch` these are `CovC` and `WardT` (`FlowSym.flowSym_iff_of_expandMatch`),
  symmetry of the continuum limit. Untouched.
* `ProxyNondeg`: a lower bound on a separated two-point read, presupposed by a band excess and strictly weaker
  than it (`NondegFold` §5); its obstruction is the relative sign of the electric channels
  (`NondegFold.mixed_zero_every_gap`), which a positive decay rate does not see. Untouched.
* `ProxyGenLimGerm`: an approximation (upper bound) of the proxies by the observer's span. Untouched.
* `ThreePointAtScale`: a lower bound `κ a_k¹²` on a bare three-point read, a non-Gaussianity statement; the
  massive free field meets `B` and has zero connected three-point reads (argued, as in `NondegFold` §4). Untouched.

## 6. The count, plainly

`B` with the template replaces `StrongEnd N` only through a template of the same strength as
`WindowFreq.GapGivesVanishing` plus the channel-overlap clause `MassGivesGap` (`massGivesVanishing_iff`); without
the template it replaces nothing. The second factor of the template, `MassGivesGap` (a positive tensor-channel decay rate gives the transfer gap), is not a standard theorem: the tensor rate bounds the transfer gap from above, so the implication needs the tensor channel to overlap the lowest state above the vacuum. It is a lattice working assumption and is not proved here. `clayStatementOf_of_readOpens` and `clayStatementOf_of_massReadOpens` are the root with `B`
(frequently at `∞`, or at every coupling) and `MassGivesVanishing` in place of `StrongEnd N`. They are not a reduction of the hypothesis list: `B` plus one named template stands where `StrongEnd N` stood. What remains besides `B` is the ultraviolet half of the tower read
(`ZoomSettlesUV`: no runaway and settling) and the nine flowed-composite clauses, which are ultraviolet,
normalisation, symmetry and non-triviality statements of the continuum limit; none of them is a mass statement.
The route at its sharpest is stated in PAPER §6.6 "The route at its sharpest".

The physics this records. The one read `2^k m′(β_k)` splits into two halves: "does not stall" (bounded below),
which is the infrared side and is proved along every tower in the basin; and "does not run away" (bounded above,
settling), which is the ultraviolet side and is the open content of `ZoomSettlesUV`. At a fixed coupling, `B` is
the infrared side alone, and under the finite-size template it is exactly `NoStall N`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower end of the couplings, the zero mass and the limit `0⁺`; `2` the
window base `2^w` and the least rank of `SU(N)`; `1` the base of `2^w > 1` and of `log 2 ≥ 0`; `log 2` the
window rate of `CouplingTower.windowGap` (inherited through `GapReadsTensorProved.confinedAt`); `∞` the limit of
an opening read. Inherited, not derived here: `1/1000` the seed of `DoublingSharp`, used only inside the proof
of `windowReading_floor` to exhibit the neighbourhood of `0⁺`. Counterexample choice: `q k = b + k` in
`floor_not_settling`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FinalBridge

open Filter Topology
open scoped ENNReal NNReal
open MassGap.CouplingTower (windowCoupling StrongEnd CouplingTower)
open MassGap.MeasuredSpacing (mU measSpacing)

/-! ## 1. The bridge -/

section Bridge

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The mass read in aperture units** at coupling `β` and aperture `2^w`: `2^w · mU β`.
DERIVED: `2` the window base. -/
def apertureRead (β : ℝ) (w : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ w * mU (NeZero.ne N) β

variable (N) in
/-- **The read opens**: it grows without bound with the aperture; it does not stall.
DERIVED: `∞` the limit of an opening read. -/
def ReadOpens (β : ℝ) : Prop := Tendsto (apertureRead N β) atTop (𝓝 ∞)

variable (N) in
/-- **The bridge `B`**: the mass read in aperture units opens at every coupling `β ≥ 0`.
DERIVED: `0` the lower end of the couplings. -/
def MassReadOpens : Prop := ∀ β : ℝ, 0 ≤ β → ReadOpens N β

/-- The aperture opens: `2^w → ∞` in `[0, ∞]`. DERIVED: `1`, `2` the window base above `1`. -/
theorem tendsto_two_pow_top : Tendsto (fun w : ℕ => (2 : ℝ≥0∞) ^ w) atTop (𝓝 ∞) := by
  have h := ENNReal.tendsto_nat_nhds_top.comp
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by norm_num))
  refine h.congr fun w => ?_
  simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]

/-- **The read opens exactly when the mass is positive.** DERIVED: `0` the zero mass. -/
theorem readOpens_iff (β : ℝ) : ReadOpens N β ↔ 0 < mU (NeZero.ne N) β := by
  constructor
  · intro h
    rw [pos_iff_ne_zero]
    intro h0
    have e : apertureRead N β = fun _ => 0 := funext fun w => by
      simp only [apertureRead, h0, mul_zero]
    have hc : Tendsto (apertureRead N β) atTop (𝓝 0) := by
      rw [e]
      exact tendsto_const_nhds
    exact ENNReal.top_ne_zero (tendsto_nhds_unique h hc)
  · intro h
    have h2 := ENNReal.Tendsto.mul_const (b := mU (NeZero.ne N) β) tendsto_two_pow_top
      (Or.inl ENNReal.top_ne_zero)
    rw [ENNReal.top_mul h.ne'] at h2
    exact h2

/-! ## 2. The map against `StrongEnd` / `NoStall` -/

/-- **A periodic Clay gap gives a positive mass** (`GapReadsTensorProved.gapReadsTensor`).
DERIVED: `0` the signs, the plane and the time axis; `1` the upper end of the rate. -/
theorem mU_pos_of_clayGap {β r : ℝ} (hβ : 0 ≤ β) (hr0 : 0 < r) (hr1 : r < 1)
    (h : PeriodicContent.PeriodicClayGapAt 0 0 (NeZero.ne N) β r) : 0 < mU (NeZero.ne N) β := by
  have hle := (GapReadsTensorProved.gapReadsTensor (N := N)) β hβ r h
  have hpos : 0 < ENNReal.ofReal (-Real.log r) :=
    ENNReal.ofReal_pos.mpr (neg_pos.mpr (Real.log_neg hr0 hr1))
  exact lt_of_lt_of_le hpos hle

/-- **The gap at `β` gives a positive mass.** DERIVED: `0` the lower end. -/
theorem mU_pos_of_gapAt {β : ℝ} (hβ : 0 ≤ β) (h : WindowFreq.GapAt N (NeZero.ne N) β) :
    0 < mU (NeZero.ne N) β := by
  obtain ⟨r, hr0, hr1, hg⟩ := h
  exact mU_pos_of_clayGap hβ hr0 hr1 hg

/-- **The vanishing read opens the mass read** (vanishing ⇒ gap ⇒ mass). DERIVED: `2` the least rank;
`0` the lower end. -/
theorem readOpens_of_vanishes (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) (h : StrongAnchor.Vanishes N β) :
    ReadOpens N β :=
  (readOpens_iff β).mpr (mU_pos_of_gapAt hβ (WindowFreq.gapAt_of_vanishes hN2 (NeZero.ne N) hβ h))

/-- **`NoStall N ⇒ B`** (no template). DERIVED: `2` the least rank; `0` the lower end. -/
theorem massReadOpens_of_noStall (hN2 : 2 ≤ N) (hR : StrongAnchor.NoStall N) : MassReadOpens N :=
  fun β hβ => readOpens_of_vanishes hN2 hβ (((StrongAnchor.noStall_iff (NeZero.ne N)).mp hR) β hβ)

/-- **`StrongEnd N` gives the read opening frequently at `∞`** (no template). DERIVED: `2` the least rank;
`0` the lower end. -/
theorem frequently_readOpens_of_strongEnd (hN2 : 2 ≤ N) (hS : StrongEnd N) :
    ∃ᶠ β in atTop, ReadOpens N β := by
  have hS' : ∃ᶠ β in atTop, StrongAnchor.Vanishes N β := hS
  exact (hS'.and_eventually (eventually_ge_atTop 0)).mono fun β hb => readOpens_of_vanishes hN2 hb.2 hb.1

variable (N) in
/-- **Template (Lüscher finite volume; Borgs–Kotecký where a convergent expansion holds)**, not proved: at every
`β ≥ 0` a positive measured mass gives the vanishing read of the window coupling. Free one-dimensional instance:
`free_readOpens_iff_vanishing`. DERIVED: `0` the lower end and the zero mass. -/
def MassGivesVanishing : Prop :=
  ∀ β : ℝ, 0 ≤ β → 0 < mU (NeZero.ne N) β → StrongAnchor.Vanishes N β

variable (N) in
/-- **Channel overlap (template, not a standard theorem)**: at every `β ≥ 0` a positive decay rate of the tensor
channel gives the periodic transfer gap. DERIVED: `0` the lower end and the zero mass. -/
def MassGivesGap : Prop :=
  ∀ β : ℝ, 0 ≤ β → 0 < mU (NeZero.ne N) β → WindowFreq.GapAt N (NeZero.ne N) β

/-- **The mass template contains the gap template.** DERIVED: no numeral. -/
theorem gapGivesVanishing_of_massGivesVanishing (hT : MassGivesVanishing N) :
    WindowFreq.GapGivesVanishing N (NeZero.ne N) :=
  fun β hβ hg => hT β hβ (mU_pos_of_gapAt hβ hg)

/-- **The gap template and channel overlap give the mass template.** DERIVED: no numeral. -/
theorem massGivesVanishing_of_gap (hG : WindowFreq.GapGivesVanishing N (NeZero.ne N))
    (hM : MassGivesGap N) : MassGivesVanishing N :=
  fun β hβ hm => hG β hβ (hM β hβ hm)

/-- **The mass template is exactly the gap template with channel overlap.** DERIVED: `2` the least rank. -/
theorem massGivesVanishing_iff (hN2 : 2 ≤ N) :
    MassGivesVanishing N ↔ WindowFreq.GapGivesVanishing N (NeZero.ne N) ∧ MassGivesGap N :=
  ⟨fun hT => ⟨gapGivesVanishing_of_massGivesVanishing hT,
      fun β hβ hm => WindowFreq.gapAt_of_vanishes hN2 (NeZero.ne N) hβ (hT β hβ hm)⟩,
    fun h => massGivesVanishing_of_gap h.1 h.2⟩

/-- **Under the template, `B ⇒ NoStall N`.** DERIVED: no numeral. -/
theorem noStall_of_massReadOpens (hT : MassGivesVanishing N) (hB : MassReadOpens N) :
    StrongAnchor.NoStall N :=
  (StrongAnchor.noStall_iff (NeZero.ne N)).mpr fun β hβ => hT β hβ ((readOpens_iff β).mp (hB β hβ))

/-- **Under the template, `B ↔ NoStall N`.** DERIVED: `2` the least rank. -/
theorem massReadOpens_iff_noStall (hN2 : 2 ≤ N) (hT : MassGivesVanishing N) :
    MassReadOpens N ↔ StrongAnchor.NoStall N :=
  ⟨noStall_of_massReadOpens hT, massReadOpens_of_noStall hN2⟩

/-- **Under the template, `B ⇒ StrongEnd N`.** DERIVED: no numeral. -/
theorem strongEnd_of_massReadOpens (hT : MassGivesVanishing N) (hB : MassReadOpens N) : StrongEnd N :=
  StrongAnchor.strongEnd_of_noStall (NeZero.ne N) (noStall_of_massReadOpens hT hB)

/-- **Under the template, the read opening frequently at `∞` gives `StrongEnd N`.** DERIVED: `0` the lower
end. -/
theorem strongEnd_of_frequently_readOpens (hT : MassGivesVanishing N)
    (h : ∃ᶠ β in atTop, ReadOpens N β) : StrongEnd N :=
  (h.and_eventually (eventually_ge_atTop 0)).mono fun β hb => hT β hb.2 ((readOpens_iff β).mp hb.1)

/-- **Under the template, `StrongEnd N` is the read opening frequently at `∞`.** DERIVED: `2` the least
rank. -/
theorem strongEnd_iff_frequently_readOpens (hN2 : 2 ≤ N) (hT : MassGivesVanishing N) :
    StrongEnd N ↔ ∃ᶠ β in atTop, ReadOpens N β :=
  ⟨frequently_readOpens_of_strongEnd hN2, strongEnd_of_frequently_readOpens hT⟩

/-- **`B` at every coupling gives it frequently at `∞`.** DERIVED: `0` the lower end. -/
theorem frequently_readOpens_of_massReadOpens (hB : MassReadOpens N) : ∃ᶠ β in atTop, ReadOpens N β :=
  ((eventually_ge_atTop (0 : ℝ)).mono fun β hβ => hB β hβ).frequently

/-! ### Non-vacuity on the tree's objects -/

/-- **`B` holds on an actual interval `[0, β₀)`** (the strong anchor and the proved link).
DERIVED: `2` the least rank; `0` the lower end. -/
theorem readOpens_anchor (hN2 : 2 ≤ N) : ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → ReadOpens N β := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongAnchor.strongAnchor (N := N) (NeZero.ne N)
  exact ⟨β₀, hβ₀, fun β h0 hlt => readOpens_of_vanishes hN2 h0 (h β h0 hlt)⟩

/-- **An actual coupling `β > 0` has the read opening.** DERIVED: `2` the least rank and the halving; `0` the
sign. -/
theorem exists_pos_readOpens (hN2 : 2 ≤ N) : ∃ β > 0, ReadOpens N β := by
  obtain ⟨β₀, hβ₀, h⟩ := readOpens_anchor (N := N) hN2
  exact ⟨β₀ / 2, half_pos hβ₀, h _ (half_pos hβ₀).le (half_lt_self hβ₀)⟩

end Bridge

/-! ## 3. Load tests at the free field -/

section Free

/-- **The free read opens exactly when the mass is positive**: `2^w m → ∞ ↔ m > 0` (`m ≥ 0`).
DERIVED: `0` the zero mass; `1`, `2` the window base above `1`. -/
theorem freeRead_opens_iff {m : ℝ} (hm : 0 ≤ m) :
    Tendsto (fun w : ℕ => (2 : ℝ) ^ w * m) atTop atTop ↔ 0 < m := by
  refine ⟨fun h => ?_, fun h =>
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).atTop_mul_const h⟩
  rcases hm.lt_or_eq with hm | hm
  · exact hm
  · subst hm
    simp only [mul_zero] at h
    exact absurd h (not_tendsto_const_atTop 0 atTop)

/-- **Load test (massless stalls)**: the massless free read does not open. DERIVED: `0` the zero mass. -/
theorem freeRead_massless_stalls : ¬ Tendsto (fun w : ℕ => (2 : ℝ) ^ w * 0) atTop atTop :=
  fun h => lt_irrefl (0 : ℝ) ((freeRead_opens_iff le_rfl).mp h)

/-- **The in-aperture read opens exactly when the mass is non-zero**: `FreqRead.cross m c (2^w) → ∞ ↔ m ≠ 0`.
At `m = 0` it is `|c|` at every aperture. DERIVED: `0` the zero mass; `1`, `2` the window base above `1`. -/
theorem cross_opens_iff (m c : ℝ) :
    Tendsto (fun w : ℕ => FreqRead.cross m c (2 ^ w)) atTop atTop ↔ m ≠ 0 := by
  constructor
  · intro h hm
    subst hm
    simp only [FreqRead.cross_massless] at h
    exact not_tendsto_const_atTop |c| atTop h
  · intro hm
    have hlow : ∀ w : ℕ, (2 : ℝ) ^ w * |m| ≤ FreqRead.cross m c (2 ^ w) := by
      intro w
      have h1 : Real.sqrt ((m * 2 ^ w) ^ 2) ≤ Real.sqrt ((m * 2 ^ w) ^ 2 + c ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg c))
      have e : FreqRead.cross m c (2 ^ w) = Real.sqrt ((m * 2 ^ w) ^ 2 + c ^ 2) := rfl
      rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ w)] at h1
      rw [e]
      linarith
    exact tendsto_atTop_mono hlow
      ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).atTop_mul_const (abs_pos.mpr hm))

/-- **The free template, proved**: at the free one-dimensional chain the mass read opens exactly when the
doubling defect vanishes along the windows (`WindowFreq.freeWindow_vanishes_iff`). DERIVED: `0` the zero mass and
the limit; `2` the window base. -/
theorem free_readOpens_iff_vanishing {m : ℝ} (hm : 0 ≤ m) :
    Tendsto (fun w : ℕ => (2 : ℝ) ^ w * m) atTop atTop ↔ Tendsto (WindowFreq.freeWindow m) atTop (𝓝 0) :=
  (freeRead_opens_iff hm).trans (WindowFreq.freeWindow_vanishes_iff hm).symm

end Free

/-! ## 4. The map against `ZoomSettlesUV` -/

section Tower

variable {N : ℕ} [NeZero N]

/-- **The tower form of "no stall" is proved**: along every coupling tower at every window coupling near `0⁺`,
where the measured mass is eventually finite, eventually `log 2 ≤ windowReading N βs k`.
DERIVED: `0` the limit `0⁺`; `2` the least rank; `log 2` the window rate (inherited through
`GapReadsTensorProved.confinedAt`); `1` the base of `log 2 ≥ 0`. Inherited: `1/1000` the seed of
`DoublingSharp`, used only to exhibit the neighbourhood. -/
theorem windowReading_floor (hN2 : 2 ≤ N) :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      (∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≠ ∞) →
        ∀ᶠ k in atTop, Real.log 2 ≤ ScaleLightCone.windowReading N βs k := by
  filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))] with u hu βs hT hfin
  exact CouplingTower.le_window_mass hT (GapReadsTensorProved.confinedAt hN2 hu)
    (Real.log_nonneg one_le_two) hfin

/-- **Under `ZoomSettlesUV` the floor holds** (its finiteness conjunct). DERIVED: `2` the least rank; `0` the
limit `0⁺`; `log 2` the window rate. -/
theorem windowReading_floor_of_zoomSettlesUV (hN2 : 2 ≤ N) :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ScaleLightCone.ZoomSettlesUV N βs →
      ∀ᶠ k in atTop, Real.log 2 ≤ ScaleLightCone.windowReading N βs k :=
  (windowReading_floor hN2).mono fun _ h βs hT hZ => h βs hT hZ.1

end Tower

/-- **Load test: a floor does not settle.** For every level `b`, a non-decreasing read bounded below by `b` need
not converge. Counterexample choice: `q k = b + k`. DERIVED: no other numeral. -/
theorem floor_not_settling (b : ℝ) :
    ∃ q : ℕ → ℝ, Monotone q ∧ (∀ k, b ≤ q k) ∧ ¬ ∃ L : ℝ, Tendsto q atTop (𝓝 L) := by
  refine ⟨fun k => b + k, fun i j hij => ?_, fun k => le_add_of_nonneg_right (Nat.cast_nonneg k), ?_⟩
  · have h : (i : ℝ) ≤ j := by exact_mod_cast hij
    show b + (i : ℝ) ≤ b + (j : ℝ)
    linarith
  · rintro ⟨L, hL⟩
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_atTop_add_const_left _ b tendsto_natCast_atTop_atTop) L hL

/-! ## 5. The root with `B` in place of `StrongEnd` (not a reduction) -/

section Capstone

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The root with `B` frequently at `∞` and the template in place of `StrongEnd N`**
(`ProxBound.clayStatementOf_of_proxBound`). Inputs: 11 and one template; not a reduction.
DERIVED: `0` the limit `0⁺`; `2` the least rank (`Fact (2 ≤ N)`). -/
theorem clayStatementOf_of_readOpens (hT : MassGivesVanishing N) (hB : ∃ᶠ β in atTop, ReadOpens N β)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ScaleLightCone.ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ProxBound.CoreInputsAlongWPB N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  ProxBound.clayStatementOf_of_proxBound (strongEnd_of_frequently_readOpens hT hB) hUV hF

/-- **The root with `B` at every coupling and the template** (`StrongAnchor.clayStatementOf_of_noStall`).
Inputs: 11 and one template; not a reduction. DERIVED: `0` the limit `0⁺`; `2` the least rank
(`Fact (2 ≤ N)`). -/
theorem clayStatementOf_of_massReadOpens (hT : MassGivesVanishing N) (hB : MassReadOpens N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ScaleLightCone.ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ProxBound.CoreInputsAlongWPB N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  StrongAnchor.clayStatementOf_of_noStall (noStall_of_massReadOpens hT hB) hUV hF

end Capstone

end MassGap.FinalBridge

end

#print axioms MassGap.FinalBridge.tendsto_two_pow_top
#print axioms MassGap.FinalBridge.readOpens_iff
#print axioms MassGap.FinalBridge.mU_pos_of_clayGap
#print axioms MassGap.FinalBridge.mU_pos_of_gapAt
#print axioms MassGap.FinalBridge.readOpens_of_vanishes
#print axioms MassGap.FinalBridge.massReadOpens_of_noStall
#print axioms MassGap.FinalBridge.frequently_readOpens_of_strongEnd
#print axioms MassGap.FinalBridge.gapGivesVanishing_of_massGivesVanishing
#print axioms MassGap.FinalBridge.massGivesVanishing_of_gap
#print axioms MassGap.FinalBridge.massGivesVanishing_iff
#print axioms MassGap.FinalBridge.noStall_of_massReadOpens
#print axioms MassGap.FinalBridge.massReadOpens_iff_noStall
#print axioms MassGap.FinalBridge.strongEnd_of_massReadOpens
#print axioms MassGap.FinalBridge.strongEnd_of_frequently_readOpens
#print axioms MassGap.FinalBridge.strongEnd_iff_frequently_readOpens
#print axioms MassGap.FinalBridge.frequently_readOpens_of_massReadOpens
#print axioms MassGap.FinalBridge.readOpens_anchor
#print axioms MassGap.FinalBridge.exists_pos_readOpens
#print axioms MassGap.FinalBridge.freeRead_opens_iff
#print axioms MassGap.FinalBridge.freeRead_massless_stalls
#print axioms MassGap.FinalBridge.cross_opens_iff
#print axioms MassGap.FinalBridge.free_readOpens_iff_vanishing
#print axioms MassGap.FinalBridge.windowReading_floor
#print axioms MassGap.FinalBridge.windowReading_floor_of_zoomSettlesUV
#print axioms MassGap.FinalBridge.floor_not_settling
#print axioms MassGap.FinalBridge.clayStatementOf_of_readOpens
#print axioms MassGap.FinalBridge.clayStatementOf_of_massReadOpens
