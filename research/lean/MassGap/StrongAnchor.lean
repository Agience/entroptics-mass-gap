import Mathlib
import MassGap.ProxBound
import MassGap.StrongEndVanishing

/-!
# MassGap.StrongAnchor — a proved anchor for the strong end, and the stronger no-stall hypothesis

`NoStall N` is stronger than `StrongEnd N`: it is equivalent to the vanishing read at every coupling `β ≥ 0`
(`noStall_iff`), where `StrongEnd N` asks it only frequently as `β → ∞`. `clayStatementOf_of_noStall` is therefore
a weaker theorem than `ProxBound.clayStatementOf_of_proxBound`. It does not reduce the strength of the input.
What this module proves is the anchor (the read holds on `[0, β₀)`), the openness of the read, and the location of
a first stall. Nothing here proves `StrongEnd N`.

`CouplingTower.StrongEnd N` asks: frequently as `β → ∞`, the window coupling `windowCoupling N β w` (the doubling
defect `16 log ZR(n⁴) − log ZR((2n)⁴)` of the periodic Wilson torus of side `n = 2^w`) tends to `0` as `w → ∞`.
Call that read `Vanishes N β`.

## 1. The abstract split (proved)

For a read `V : ℝ → Prop` on the couplings `β ≥ 0`:

* `OpenRead V`: wherever `V` holds, it holds on a neighbourhood (within `β ≥ 0`).
* `Anchor V`: `V` holds on some `[0, β₀)`, `β₀ > 0` existential.
* `NoStallOf V`: for every `b > 0`, if `V` holds on `[0, b)` it holds at `b` (no first stall).
* `all_of_anchor_noStall`: open, anchored and stall-free gives `V` at every `β ≥ 0` (real induction on the
  infimum of the failures).
* `anchor_open_not_frequently` (load test): open and anchored alone do not give `V` frequently at `∞`; the
  counterexample is `V β := β < 1` (counterexample choice: `1`, any positive cut). So the residual carries the
  whole passage to large `β`.

## 2. The window read (proved)

* `vanishes_iff_seed`: at `β ≥ 0`, `Vanishes N β` exactly when some window `c ≥ 1` reads strictly below the seed
  of `DoublingSharp`.
* `openRead_vanishes`: the read is open, by continuity of each window coupling in `β`.
* `strongAnchor`: `StrongAnchor N := Anchor (Vanishes N)` holds; `β₀` is existential, from continuity at
  `β = 0` where every window reads `0` (`windowCoupling_zero`). No cluster expansion; the only threshold is the inherited seed `1/1000` of `DoublingSharp`.
* `exists_pos_vanishes`, `anchor_windowGap` (non-vacuity): an actual coupling `β > 0` vanishes, and on all of
  `[0, β₀)` the periodic Clay gap holds at a rate in `(0, 1)` (`StrongEndVanishing.windowGap_of_vanishing`).

## 3. The residual and the capstone (proved)

* `NoStall N := NoStallOf (Vanishes N)`: the crossover — no coupling `b` is the first at which the window coupling
  stops vanishing.
* `noStall_iff`: `NoStall N ↔ ∀ β ≥ 0, Vanishes N β` (given the proved anchor).
* `exists_first_stall`: if the read fails anywhere, there is a first stall `b > 0` with the read on `[0, b)` and
  not at `b`.
* `vanishes_of_uniformBelow`: the read at `b` follows from uniform vanishing on `[0, b)`, so a stall at `b` is
  exactly a loss of uniformity: the window at which the read falls below any given level diverges as `β → b⁻`.
* `strongEnd_of_anchor_noStall`, `strongEnd_of_noStall`: anchor and residual give `StrongEnd N`.
* `clayStatementOf_of_noStall`: `ProxBound.clayStatementOf_of_proxBound` with the hypothesis `StrongEnd N`
  replaced by the stronger `NoStall N`.

Plainly: `NoStall N` is stronger than `StrongEnd N` (`noStall_iff`: it is the read at every `β ≥ 0`). The split
changes the shape of the input, not its strength. The residual is a closure statement at one coupling at a time
(the read on `[0, b)` reaches `b`), the anchor and the openness it needs are proved, and the first point where it
could fail is located (`exists_first_stall`, at `b ≥ β₀ > 0`). The cluster-expansion gap `PeriodicStrongCoupling.periodic_gapAt_strong_coupling`
(live in the tree) is a gap on a bounded coupling range; a bounded range contributes nothing to a statement that
is frequently at `∞`, and the tree has no lemma from a transfer gap to the vanishing of the window coupling (only
the converse, `windowGap_of_vanishing`). So it discharges no clause of `StrongEnd N`.

## 4. The residual in frequency terms (argued, not proved)

`windowCoupling N β w` is the read at aperture `2^w`: the free energy the doubled torus carries beyond sixteen
copies of the smaller one, a finite-size (Casimir) read of the spectrum at that aperture. `Vanishes N β` is the
read settling to `0` as the aperture opens. `vanishes_of_uniformBelow` says a stall at `b` is the settling
aperture diverging as `β → b⁻`. In the terms of `FreqRead`/`BandShell`, the free crossover
`cross m c A = √((mA)² + c²)` is strictly increasing in the aperture `A` (`cross_strictMonoOn`), and the
interacting statement "`windowReading` is non-decreasing in the aperture from the strong-coupling anchor" would
keep the settling aperture bounded on every bounded coupling range, hence give `NoStall N`. That implication is
argued only: `windowReading = 2^k m′(β_k)` is a mass read along a tower and the window coupling is a free-energy
read, and no Lean lemma ties the monotonicity of the first to the uniformity of the second.

DERIVED (module-wide): `0` the limit of the read, the lower end of the couplings and the signs; `1` the least
window index; `2` the least rank of `SU(N)` (the capstone's `Fact (2 ≤ N)`), the doubling `n = 2^w`, and the
halving `ε / 2`; `16 = 2⁴` the copies in the doubling defect and `4` the exponent of the torus volume `n⁴`.
Inherited, not derived here: `1/1000` the seed of `DoublingSharp`, which `tendsto_zero_of_seed` and
`windowGap_of_vanishing` fix; this module uses it only to pass between the vanishing read and a seed window.
Counterexample choice: `1` in `anchor_open_not_frequently` (and the `β₀ = 1` inside its proof).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.StrongAnchor

open Filter Topology
open MassGap.CouplingTower (windowCoupling StrongEnd CouplingTower continuous_windowCoupling
  windowCoupling_zero tendsto_zero_of_seed windowCoupling_nonneg)

/-! ## 1. The abstract split -/

section Abstract

/-- **An open read**: wherever `V` holds at `β ≥ 0`, it holds at every nearby `β' ≥ 0`.
DERIVED: `0` the lower end of the couplings. -/
def OpenRead (V : ℝ → Prop) : Prop :=
  ∀ β : ℝ, 0 ≤ β → V β → ∀ᶠ β' in 𝓝 β, 0 ≤ β' → V β'

/-- **An anchored read**: `V` holds on `[0, β₀)` for some `β₀ > 0`. DERIVED: `0` the lower end. -/
def Anchor (V : ℝ → Prop) : Prop :=
  ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → V β

/-- **No stall**: for every `b > 0`, if `V` holds on `[0, b)` it holds at `b`. DERIVED: `0` the lower end. -/
def NoStallOf (V : ℝ → Prop) : Prop :=
  ∀ b : ℝ, 0 < b → (∀ β : ℝ, 0 ≤ β → β < b → V β) → V b

/-- **Open, anchored and stall-free gives the read at every coupling** (real induction on the infimum of the
failures). DERIVED: `0` the lower end. -/
theorem all_of_anchor_noStall {V : ℝ → Prop} (hO : OpenRead V) (hA : Anchor V) (hR : NoStallOf V) :
    ∀ β : ℝ, 0 ≤ β → V β := by
  by_contra hne
  obtain ⟨β₁, hβ₁0, hβ₁⟩ : ∃ β : ℝ, 0 ≤ β ∧ ¬ V β := by
    by_contra h'
    exact hne fun β h0 => by_contra fun hv => h' ⟨β, h0, hv⟩
  obtain ⟨β₀, hβ₀, hA⟩ := hA
  let S : Set ℝ := {β | 0 ≤ β ∧ ¬ V β}
  have hSne : S.Nonempty := ⟨β₁, hβ₁0, hβ₁⟩
  have hSbdd : BddBelow S := ⟨0, fun β hβ => hβ.1⟩
  have hbelow : ∀ β : ℝ, 0 ≤ β → β < sInf S → V β := by
    intro β h0 hlt
    by_contra hv
    exact absurd (csInf_le hSbdd ⟨h0, hv⟩) (not_le.mpr hlt)
  have hb0 : β₀ ≤ sInf S := le_csInf hSne fun β hβ => by
    by_contra hlt
    exact hβ.2 (hA β hβ.1 (not_le.mp hlt))
  have hbpos : 0 < sInf S := lt_of_lt_of_le hβ₀ hb0
  have hVb : V (sInf S) := hR _ hbpos hbelow
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hO _ hbpos.le hVb)
  have hup : sInf S + ε ≤ sInf S := le_csInf hSne fun β hβ => by
    by_contra hlt
    have hlt' : β < sInf S + ε := not_le.mp hlt
    have hbβ : sInf S ≤ β := csInf_le hSbdd hβ
    refine hβ.2 (hball ?_ hβ.1)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  linarith

/-- **Load test: open and anchored alone do not reach `∞`.** The read `β < 1` is open and anchored, is not
stall-free, and does not hold frequently at `∞`. Counterexample choice: `1`, any positive cut. -/
theorem anchor_open_not_frequently :
    OpenRead (fun β : ℝ => β < 1) ∧ Anchor (fun β : ℝ => β < 1) ∧
      ¬ NoStallOf (fun β : ℝ => β < 1) ∧ ¬ ∃ᶠ β in atTop, (β : ℝ) < 1 := by
  refine ⟨?_, ⟨1, one_pos, fun β _ h => h⟩, ?_, ?_⟩
  · intro β _ h
    filter_upwards [eventually_lt_nhds h] with β' h' _
    exact h'
  · intro h
    exact lt_irrefl _ (h 1 one_pos fun β _ hβ => hβ)
  · rw [not_frequently]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β h
    exact not_lt.mpr h

end Abstract

/-! ## 2. The window read -/

variable {N : ℕ}

/-- **The vanishing read at `β`**: the window coupling tends to `0` along the windows.
DERIVED: `0` the limit. -/
def Vanishes (N : ℕ) (β : ℝ) : Prop :=
  Tendsto (windowCoupling N β) atTop (𝓝 0)

/-- `StrongEnd N` is the vanishing read frequently at `∞`. DERIVED: no numeral. -/
theorem strongEnd_iff_frequently_vanishes : StrongEnd N ↔ ∃ᶠ β in atTop, Vanishes N β :=
  Iff.rfl

/-- **The vanishing read is a seed window**: at `β ≥ 0`, it holds exactly when some window `c ≥ 1` reads
strictly below the seed of `DoublingSharp`. DERIVED: `0` the lower end; `1` the least window index.
Inherited: `1/1000` the seed of `DoublingSharp`. -/
theorem vanishes_iff_seed (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Vanishes N β ↔ ∃ c : ℕ, 1 ≤ c ∧ windowCoupling N β c < 1 / 1000 :=
  ⟨fun h => StrongEndVanishing.exists_window_lt_of_tendsto_zero h (by norm_num),
    fun ⟨_, hc, h⟩ => tendsto_zero_of_seed hN hβ hc h.le⟩

/-- **The read at `β = 0`**: every window reads `0`. DERIVED: `0` the ultralocal coupling. -/
theorem vanishes_zero : Vanishes N 0 := by
  have e : windowCoupling N 0 = fun _ => 0 := funext fun w => windowCoupling_zero N w
  unfold Vanishes
  rw [e]
  exact tendsto_const_nhds

/-- **The vanishing read is open in the coupling**: a seed window strictly below the seed stays below it nearby,
by continuity in `β`. Inherited: `1/1000` the seed of `DoublingSharp`. DERIVED: `0` the lower end. -/
theorem openRead_vanishes (hN : N ≠ 0) : OpenRead (Vanishes N) := by
  intro β hβ h
  obtain ⟨c, hc, hlt⟩ := (vanishes_iff_seed hN hβ).mp h
  have hev : ∀ᶠ x in 𝓝 β, windowCoupling N x c < 1 / 1000 :=
    ((continuous_windowCoupling hN c).tendsto β).eventually (eventually_lt_nhds hlt)
  filter_upwards [hev] with β' h' h0
  exact (vanishes_iff_seed hN h0).mpr ⟨c, hc, h'⟩

set_option linter.dupNamespace false in
/-- **The strong anchor**: the vanishing read holds on an interval `[0, β₀)`. DERIVED: `0` the lower end. -/
def StrongAnchor (N : ℕ) : Prop := Anchor (Vanishes N)

/-- **The strong anchor holds**, `β₀ > 0` existential (from continuity at `β = 0`).
DERIVED: `0` the lower end and the subtraction. -/
theorem strongAnchor (hN : N ≠ 0) : StrongAnchor N := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp (openRead_vanishes hN 0 le_rfl vanishes_zero)
  refine ⟨ε, hε, fun β h0 hlt => h ?_ h0⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact hlt

/-- **Non-vacuity**: an actual coupling `β > 0` has the vanishing read. DERIVED: `0` the sign. -/
theorem exists_pos_vanishes (hN : N ≠ 0) : ∃ β > 0, Vanishes N β := by
  obtain ⟨β₀, hβ₀, h⟩ := strongAnchor hN
  exact ⟨β₀ / 2, half_pos hβ₀, h _ (half_pos hβ₀).le (half_lt_self hβ₀)⟩

/-- **The anchor carries a gap**: on `[0, β₀)` the periodic Clay gap holds at a rate in `(0, 1)`.
DERIVED: `2` the least rank; `0` the plane, the time axis and the signs; `1` the upper end of the rate. -/
theorem anchor_windowGap (hN2 : 2 ≤ N) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r := by
  obtain ⟨β₀, hβ₀, h⟩ := strongAnchor hN
  exact ⟨β₀, hβ₀, fun β h0 hlt => StrongEndVanishing.windowGap_of_vanishing hN2 hN h0 (h β h0 hlt)⟩

/-! ## 3. The residual and the capstone -/

/-- **(S-residual) No stall**: stronger than `StrongEnd N`; equivalent to the read at every `β ≥ 0`
(`noStall_iff`). No coupling `b > 0` is the first at which the window coupling stops vanishing.
DERIVED: no numeral. -/
def NoStall (N : ℕ) : Prop := NoStallOf (Vanishes N)

/-- **The anchor and the residual give the read at every coupling.** DERIVED: `0` the lower end. -/
theorem vanishes_of_anchor_noStall (hN : N ≠ 0) (hA : StrongAnchor N) (hR : NoStall N) :
    ∀ β : ℝ, 0 ≤ β → Vanishes N β :=
  all_of_anchor_noStall (openRead_vanishes hN) hA hR

/-- **The residual is the read at every coupling.** DERIVED: `0` the lower end. -/
theorem noStall_iff (hN : N ≠ 0) : NoStall N ↔ ∀ β : ℝ, 0 ≤ β → Vanishes N β :=
  ⟨vanishes_of_anchor_noStall hN (strongAnchor hN), fun h b hb _ => h b hb.le⟩

/-- **The first stall**: if the read fails at some `β ≥ 0`, there is `b > 0` with the read on `[0, b)` and not
at `b`. DERIVED: `0` the lower end. -/
theorem exists_first_stall (hN : N ≠ 0) (h : ¬ ∀ β : ℝ, 0 ≤ β → Vanishes N β) :
    ∃ b > 0, (∀ β : ℝ, 0 ≤ β → β < b → Vanishes N β) ∧ ¬ Vanishes N b := by
  by_contra h'
  refine h ((noStall_iff hN).mp fun b hb hbelow => ?_)
  by_contra hv
  exact h' ⟨b, hb, hbelow, hv⟩

/-- **Uniform vanishing below `b` reaches `b`**: if for every level `ε > 0` one window index bounds every
coupling in `[0, b)` below `ε` from there on, the read holds at `b`. DERIVED: `0` the lower end and the limit;
`1` the least window index; `2` the halving of the tolerance. -/
theorem vanishes_of_uniformBelow (hN : N ≠ 0) {b : ℝ} (hb : 0 < b)
    (hU : ∀ ε > 0, ∃ W : ℕ, ∀ w ≥ W, ∀ β : ℝ, 0 ≤ β → β < b → windowCoupling N β w ≤ ε) :
    Vanishes N b := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨W, hW⟩ := hU (ε / 2) (half_pos hε)
  refine ⟨max W 1, fun w hw => ?_⟩
  have hw1 : 1 ≤ w := le_trans (le_max_right _ _) hw
  have hwW : W ≤ w := le_trans (le_max_left _ _) hw
  have ht : Tendsto (fun β => windowCoupling N β w) (𝓝[<] b) (𝓝 (windowCoupling N b w)) :=
    ((continuous_windowCoupling hN w).tendsto b).mono_left nhdsWithin_le_nhds
  have hle : windowCoupling N b w ≤ ε / 2 := by
    refine le_of_tendsto ht ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hb), self_mem_nhdsWithin] with β h0 hlt
    exact hW w hwW β h0.le hlt
  have hnn := windowCoupling_nonneg hN hb.le hw1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **The anchor and the residual give the strong end.** DERIVED: `0` the lower end. -/
theorem strongEnd_of_anchor_noStall (hN : N ≠ 0) (hA : StrongAnchor N) (hR : NoStall N) :
    StrongEnd N :=
  ((eventually_ge_atTop (0 : ℝ)).mono fun β h => vanishes_of_anchor_noStall hN hA hR β h).frequently

/-- **The residual alone gives the strong end** (the anchor is proved). DERIVED: no numeral. -/
theorem strongEnd_of_noStall (hN : N ≠ 0) (hR : NoStall N) : StrongEnd N :=
  strongEnd_of_anchor_noStall hN (strongAnchor hN) hR

section Capstone

variable [NeZero N] [Fact (2 ≤ N)]

/-- **The root at `SU(N)` from the no-stall residual**: `ProxBound.clayStatementOf_of_proxBound` with the strong
end replaced by `NoStall N`. DERIVED: `0` the lower end of the window coupling's range. -/
theorem clayStatementOf_of_noStall (hR : NoStall N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ScaleLightCone.ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ProxBound.CoreInputsAlongWPB N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  ProxBound.clayStatementOf_of_proxBound (strongEnd_of_noStall (NeZero.ne N) hR) hUV hF

end Capstone

end MassGap.StrongAnchor

end

#print axioms MassGap.StrongAnchor.all_of_anchor_noStall
#print axioms MassGap.StrongAnchor.anchor_open_not_frequently
#print axioms MassGap.StrongAnchor.openRead_vanishes
#print axioms MassGap.StrongAnchor.strongAnchor
#print axioms MassGap.StrongAnchor.exists_pos_vanishes
#print axioms MassGap.StrongAnchor.anchor_windowGap
#print axioms MassGap.StrongAnchor.noStall_iff
#print axioms MassGap.StrongAnchor.exists_first_stall
#print axioms MassGap.StrongAnchor.vanishes_of_uniformBelow
#print axioms MassGap.StrongAnchor.strongEnd_of_anchor_noStall
#print axioms MassGap.StrongAnchor.strongEnd_of_noStall
#print axioms MassGap.StrongAnchor.clayStatementOf_of_noStall
#print axioms MassGap.StrongAnchor.strongEnd_iff_frequently_vanishes
#print axioms MassGap.StrongAnchor.vanishes_iff_seed
#print axioms MassGap.StrongAnchor.vanishes_zero
#print axioms MassGap.StrongAnchor.vanishes_of_anchor_noStall
