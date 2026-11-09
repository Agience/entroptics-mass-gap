import Mathlib
import MassGap.FocusFloor

/-!
# MassGap.DisclosureFloor — the divided aperture discloses the diffraction; the mass is the total it carries

The author's picture: "The divided aperture forces the stretching of the signal to disclose its diffraction limits. Same
picture. Finer models. The mass is carried in the diffraction so we need to force it to be visible somehow."
This module formalises it. Divide a window into sub-apertures of side `a`. A pattern of extent `R` crosses
`spill a x R ≈ R/a` sub-aperture edges (`FocusFloor.spill`), and leaks across each one a per-edge read `μ` in
lattice units. The disclosure is the total, `spill · μ`. At the free field `μ = θ a` and the total is `θ R` at
every subdivision: refinement redistributes the mass over more edges and keeps the total. Interacting, keeping the
total under refinement is `ConstantPhysics`, which is argued to be the line of constant physics. The total can be
lost at a finite coupling only where the per-edge read reaches zero in lattice units: a divergence of the
disclosure length, a critical point in the usual sense (argued). Declarations are in the namespace
`MassGap.DisclosureFloor`.

## 0. What the tree had (map)

* `CouplingTower.continuous_windowCoupling` (from `DeltaLengthTower.continuous_defectW`): at a fixed window the
  read is continuous in `β`. This is the only continuity in `β` in the tree. There is no `continuous_mU`, no
  continuity of `measSpacing`, no continuity of `trivialDefectN` in `β`, and no semicontinuity of any decay rate.
* `StrongAnchor`: the abstract split `OpenRead`/`Anchor`/`NoStallOf` with `all_of_anchor_noStall` (real induction
  on the infimum of the failures); `openRead_vanishes` (the vanishing read is open in `β`, from the seed basin
  and continuity at a fixed window); `strongAnchor`; `noStall_iff` (`NoStall N` is the read at every `β ≥ 0`);
  `exists_first_stall`; `vanishes_of_uniformBelow`.
* `FloorTension.noStall_iff_flux_zeroFlux`: `NoStall N` is the confined flux and `ZeroFluxVanishing` at every
  `β ≥ 0`. `FloorTension.anchor_flux_zeroFlux`: both on `[0, β₀)`.
* `CouplingTower`, `ConstantPhysicsLine`: a coupling tower (`CouplingTower N u₀ βs id`, the window `2^k` reads `u₀`
  at `βs k`), its existence near `0⁺` iff `StrongEnd N`, and `LineOfConstantPhysics N` (tower, (UV) convergence of
  the window reading of the measured mass, `ExistAlong`). The line is stated as an input bundle; no theorem in the
  tree builds it or relates it to a continuity of the lattice mass in `β`.

So, of the reduction asked for, (a) the anchor and (b) in openness form are already proved for the vanishing read
(`StrongAnchor.strongAnchor`, `StrongAnchor.openRead_vanishes`), and (c) is `StrongAnchor.NoStall N`.

## 1. The disclosure read (proved)

* `disclosure μ a x R = spill a x R · μ`: per-edge read `μ` (lattice units) times the edges crossed.
* `disclosure_free`: at the free field (`μ = θ a`) it is `FocusFloor.spillLine θ a x R`; `disclosure_free_rate`:
  per unit extent it tends to `θ` at every subdivision.
* `spill_exact`, `disclosure_free_exact`: when the window `R` is divided into `n` equal sub-apertures the free
  disclosure is `θ R` exactly, at every `n ≥ 1`. `disclosure_lattice_exact`: on the free chain, `n` sub-apertures
  of `a` sites, each edge read by `FocusFloor.parallaxRead`, total `θ (n a)`, exactly.
* `disclosure_tendsto`: along a refinement `as k → 0⁺` with `μs k / as k → m` (`ConstantPhysics`), the disclosure
  tends to `R m` for every pattern. `constantPhysics_of_disclosure`: conversely, if the disclosure of one pattern of
  extent `R > 0` converges to `D`, then `μs k / as k → D / R`. Keeping the total under refinement is `ConstantPhysics`,
  the per-edge read over the spacing converging, exactly. That `ConstantPhysics` is the tree's
  `LineOfConstantPhysics` (its (UV) convergence of the window reading) is argued only; no theorem in the tree
  relates them.

## 2. The reduction (proved), and its two tests

* `pos_of_noCritical`: an abstract rate `r` continuous in `β` with `r 0 > 0` and no stall (`NoStallOf (0 < r ·)`)
  is positive at every `β ≥ 0`; `pos_iff_noCritical`: given continuity and the anchor this is an equivalence.
* Free field (`free_rate_continuous`, `free_critical`, `free_massless_disclosure`): the rate `WindowFreq.rate` is
  continuous in the mass, positive exactly for `m > 0`, zero at `m = 0`; at the massless point the disclosure is
  `0` at every subdivision. The massless point is the critical point.
* Counterexample (labelled): `kink β = max (1 − β) 0` is continuous and anchored, stalls at `β = 1`, and is zero
  there (`kink_counterexample`). an anchor and continuity without the no-stall condition give nothing.

## 3. On the tree: a failure at finite `β` is a divergence of the seed window (a critical point in the usual sense is argued only) (proved)

* `SeedWindowDiverges N b`: for every `K`, near `b` every window `1 ≤ c ≤ K` reads above the seed. The read's
  disclosure length (the least seed window) diverges at `b`.
* `vanishes_of_boundedSeed`: if near `b` some window `≤ K` frequently reads at or below the seed, the read holds
  at `b`. A finite jump with bounded seed window cannot remove the read.
* `not_vanishes_iff_diverges`: at `b ≥ 0`, the read fails exactly when the seed window diverges at `b`.
* `NoCriticalPoint N` and `noStall_iff_noCriticalPoint`: no stall is exactly no critical point.
* Capstone `zeroFlux_of_noCriticalPoint`: `NoCriticalPoint N` gives `ZeroFluxVanishing N β` (and the confined flux)
  at every `β ≥ 0`.

## Verdict, plainly

(b) Openness of the gapped set in `β` is provable from the tree, and is already proved for the vanishing read
(`openRead_vanishes`): continuity at a fixed window plus the seed basin. Continuity of an infinite-volume lattice
mass in `β` is not in the tree and is not needed. For the zero-flux read alone there is no seed basin in the tree,
so openness of `{β : ZeroFluxVanishing N β}` by itself is not proved; it is reached through the full read.
(c) is not a different problem. `noStall_iff_noCriticalPoint` and `StrongAnchor.noStall_iff` prove that "no
critical point at finite `β`" is equivalent to the read at every `β ≥ 0`, which is equivalent to the confined flux
and the zero-flux gap at every `β ≥ 0`. What §3 adds is the shape of any failure: it must be a divergence of the
seed window (the disclosure length in lattice units), not a finite jump. Reading that divergence as a critical
point is argued only. That a first-order bulk transition keeps
the seed window bounded is argued only. The absence of a finite-`β` critical point for the 4-D `SU(N)` Wilson
action is a physics expectation, unproved. The capstone has one input, `NoCriticalPoint N`, equivalent to
`StrongAnchor.NoStall N`: the open count is unchanged at one.

DERIVED (module-wide): `0` the signs, the limits, the left end and the ultralocal point; `1` the least window
index, the least subdivision and the unit of the counterexample. Counterexample choice: `kink` (its `1`, labelled
there). Inherited tree constants: `1/1000` the seed of `DoublingSharp` (via `CouplingTower.tendsto_zero_of_seed`
and `StrongAnchor.vanishes_iff_seed`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.DisclosureFloor

open Filter Topology
open MassGap.FocusFloor (spill spillLine spillLine_rate spill_size_read parallaxRead parallaxRead_eq)
open MassGap.WindowFreq (rate)
open MassGap.StrongAnchor (OpenRead Anchor NoStallOf Vanishes)
open MassGap.CouplingTower (windowCoupling continuous_windowCoupling tendsto_zero_of_seed)
open MassGap.LineSeedsVanishing (ZeroFluxVanishing)

/-! ## 1. The disclosure read -/

/-- **The disclosure**: the per-edge read `μ` (lattice units) times the sub-aperture edges the pattern crosses.
DERIVED: no numeral. -/
def disclosure (μ a x R : ℝ) : ℝ := (spill a x R : ℝ) * μ

/-- **At the free field the disclosure is the spill line.** DERIVED: no numeral. -/
theorem disclosure_free (θ a x R : ℝ) : disclosure (θ * a) a x R = spillLine θ a x R := rfl

/-- **Free field: per unit extent the disclosure is `θ`, at every subdivision.** DERIVED: `0` the sign. -/
theorem disclosure_free_rate {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R : ℝ => disclosure (θ * a) a x R / R) atTop (𝓝 θ) :=
  spillLine_rate hθ ha x

/-- **An exact division has `n` edges.** DERIVED: `0` the left end and the sign; `1` the least subdivision. -/
theorem spill_exact {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) : spill (R / n) 0 R = n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have e : (0 + R) / (R / n) = n := by rw [zero_add]; field_simp
  unfold spill
  rw [e, zero_div]
  simp

/-- **Free field: the total is the same at every refinement, exactly.** DERIVED: `0` the left end and the sign;
`1` the least subdivision. -/
theorem disclosure_free_exact (θ : ℝ) {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) :
    disclosure (θ * (R / n)) (R / n) 0 R = θ * R := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold disclosure
  rw [spill_exact hR hn]
  push_cast
  field_simp

/-- **Free chain: `n` sub-apertures of `a` sites, each edge read by parallax, total `θ (n a)`.**
DERIVED: `0` the signs. -/
theorem disclosure_lattice_exact {θ : ℝ} (hθ : 0 < θ) {a : ℕ} (ha : 0 < a) (n j : ℕ) :
    (n : ℝ) * parallaxRead θ a j = θ * ((n * a : ℕ) : ℝ) := by
  rw [parallaxRead_eq hθ ha j]
  push_cast
  ring

/-- **The constant physics line in mass form**: along the refinement, the per-edge read over the spacing tends to
the mass `m`. That this is the tree's `LineOfConstantPhysics` is argued only. DERIVED: no numeral. -/
def ConstantPhysics (μs as : ℕ → ℝ) (m : ℝ) : Prop :=
  Tendsto (fun k => μs k / as k) atTop (𝓝 m)

/-- **Constant physics keeps the total**: the disclosure tends to `R m` for every pattern.
DERIVED: `0` the limit of the spacing. -/
theorem disclosure_tendsto {μs as : ℕ → ℝ} {m : ℝ} (has : Tendsto as atTop (𝓝[>] 0))
    (h : ConstantPhysics μs as m) (x R : ℝ) :
    Tendsto (fun k => disclosure (μs k) (as k) x R) atTop (𝓝 (R * m)) := by
  have hpos : ∀ᶠ k in atTop, 0 < as k := has.eventually self_mem_nhdsWithin
  have hp := ((spill_size_read x R).comp has).mul h
  refine hp.congr' ?_
  filter_upwards [hpos] with k hk
  have hk' : as k ≠ 0 := hk.ne'
  simp only [Function.comp_apply, disclosure]
  field_simp

/-- **A kept total is constant physics**: if one pattern's disclosure converges to `D`, the per-edge read over
the spacing converges to `D / R`. DERIVED: `0` the limit of the spacing and the sign. -/
theorem constantPhysics_of_disclosure {μs as : ℕ → ℝ} (has : Tendsto as atTop (𝓝[>] 0)) {x R D : ℝ}
    (hR : 0 < R) (hD : Tendsto (fun k => disclosure (μs k) (as k) x R) atTop (𝓝 D)) :
    ConstantPhysics μs as (D / R) := by
  have hS := (spill_size_read x R).comp has
  have hSpos : ∀ᶠ k in atTop, 0 < (fun a : ℝ => (spill a x R : ℝ) * a) (as k) :=
    hS.eventually (eventually_gt_nhds hR)
  unfold ConstantPhysics
  refine (hD.div hS hR.ne').congr' ?_
  filter_upwards [hSpos] with k hk
  have hs : (spill (as k) x R : ℝ) ≠ 0 := left_ne_zero_of_mul hk.ne'
  have ha : as k ≠ 0 := right_ne_zero_of_mul hk.ne'
  simp only [Pi.div_apply, Function.comp_apply, disclosure]
  field_simp

/-! ## 2. The reduction and its tests -/

/-- **Continuous, anchored and without a stall gives a positive rate at every coupling.**
DERIVED: `0` the left end and the sign. -/
theorem pos_of_noCritical {r : ℝ → ℝ} (hc : Continuous r) (h0 : 0 < r 0)
    (hR : NoStallOf (fun β => 0 < r β)) : ∀ β : ℝ, 0 ≤ β → 0 < r β := by
  have hO : OpenRead (fun β => 0 < r β) := fun β _ hβ =>
    ((hc.tendsto β).eventually (eventually_gt_nhds hβ)).mono fun _ h _ => h
  have hA : Anchor (fun β => 0 < r β) := by
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp ((hc.tendsto 0).eventually (eventually_gt_nhds h0))
    refine ⟨ε, hε, fun β hβ hlt => h ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ]
    exact hlt
  exact StrongAnchor.all_of_anchor_noStall hO hA hR

/-- **Given continuity and the anchor, no stall is the conclusion.** DERIVED: `0` the left end and the sign. -/
theorem pos_iff_noCritical {r : ℝ → ℝ} (hc : Continuous r) (h0 : 0 < r 0) :
    (∀ β : ℝ, 0 ≤ β → 0 < r β) ↔ NoStallOf (fun β => 0 < r β) :=
  ⟨fun h b hb _ => h b hb.le, pos_of_noCritical hc h0⟩

/-- **Free field: the rate is continuous in the mass.** DERIVED: `2` from `WindowFreq.rate`. -/
theorem free_rate_continuous : Continuous rate := by
  unfold rate
  exact (Real.continuous_arsinh.comp (continuous_id.div_const 2)).const_mul 2

/-- **Free field: the massless point is the critical point**: the rate is positive exactly for `m > 0` and zero at
`m = 0`. DERIVED: `0` the mass. -/
theorem free_critical : (∀ m : ℝ, 0 < rate m ↔ 0 < m) ∧ rate 0 = 0 :=
  ⟨fun _ => WindowFreq.rate_pos_iff, by simp [rate]⟩

/-- **Free field: at the massless point nothing is disclosed, at any subdivision.** DERIVED: `0` the mass. -/
theorem free_massless_disclosure (a x R : ℝ) : disclosure (rate 0 * a) a x R = 0 := by
  simp [disclosure, rate]

/-- **Counterexample choice**: an abstract rate with a zero at the finite coupling `1` (its unit labelled here).
DERIVED: `0` the floor of the rate. -/
def kink (β : ℝ) : ℝ := max (1 - β) 0

/-- **An anchor and continuity without the no-stall condition give nothing**: `kink` is continuous and anchored, stalls at `1`, and is zero there.
DERIVED: `0` the left end and the sign; `1` the counterexample's zero. -/
theorem kink_counterexample :
    Continuous kink ∧ 0 < kink 0 ∧ ¬ NoStallOf (fun β => 0 < kink β) ∧ kink 1 = 0 := by
  have h1 : kink 1 = 0 := by simp [kink]
  refine ⟨(continuous_const.sub continuous_id).max continuous_const, by simp [kink], ?_, h1⟩
  intro h
  have : 0 < kink 1 := h 1 one_pos fun β _ hlt => lt_max_of_lt_left (by linarith)
  rw [h1] at this
  exact lt_irrefl _ this

/-! ## 3. On the tree: a failure is a divergence of the seed window -/

variable {N : ℕ}

variable (N) in
/-- **The seed window diverges at `b`**: for every `K`, near `b` every window `1 ≤ c ≤ K` reads above the seed.
Inherited: `1/1000` the seed of `DoublingSharp`. DERIVED: `1` the least window index. -/
def SeedWindowDiverges (b : ℝ) : Prop :=
  ∀ K : ℕ, ∀ᶠ β in 𝓝 b, ∀ c : ℕ, 1 ≤ c → c ≤ K → 1 / 1000 < windowCoupling N β c

/-- **A failure makes the seed window diverge.** Inherited: `1/1000` the seed. DERIVED: `0` the left end; `1` the
least window index. -/
theorem diverges_of_not_vanishes (hN : N ≠ 0) {b : ℝ} (hb : 0 ≤ b) (hv : ¬ Vanishes N b) :
    SeedWindowDiverges N b := by
  intro K
  have hc : ∀ c ∈ Finset.Icc 1 K, ∀ᶠ β in 𝓝 b, 1 / 1000 < windowCoupling N β c := by
    intro c hcK
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcK).1
    have hlt : 1 / 1000 < windowCoupling N b c :=
      lt_of_not_ge fun hle => hv (tendsto_zero_of_seed hN hb hc1 hle)
    exact ((continuous_windowCoupling hN c).tendsto b).eventually (eventually_gt_nhds hlt)
  filter_upwards [(Filter.eventually_all_finset _).mpr hc] with β hβ c h1 hK
  exact hβ c (Finset.mem_Icc.mpr ⟨h1, hK⟩)

/-- **A bounded seed window keeps the read**: if near `b` some window `≤ K` frequently reads at or below the seed,
the read holds at `b`. Inherited: `1/1000` the seed. DERIVED: `0` the left end; `1` the least window index;
`1/1000` the seed of `DoublingSharp` (`CouplingTower.tendsto_zero_of_seed`). -/
theorem vanishes_of_boundedSeed (hN : N ≠ 0) {b : ℝ} (hb : 0 ≤ b) (K : ℕ)
    (h : ∃ᶠ β in 𝓝 b, ∃ c : ℕ, 1 ≤ c ∧ c ≤ K ∧ windowCoupling N β c ≤ 1 / 1000) : Vanishes N b := by
  by_contra hv
  obtain ⟨β, ⟨c, h1, hK, hle⟩, hβ⟩ := (h.and_eventually (diverges_of_not_vanishes hN hb hv K)).exists
  exact absurd (hβ c h1 hK) (not_lt.mpr hle)

/-- **At `b ≥ 0` the read fails exactly when the seed window diverges.**
DERIVED: `0` the left end. -/
theorem not_vanishes_iff_diverges (hN : N ≠ 0) {b : ℝ} (hb : 0 ≤ b) :
    ¬ Vanishes N b ↔ SeedWindowDiverges N b := by
  refine ⟨diverges_of_not_vanishes hN hb, fun hD hv => ?_⟩
  obtain ⟨c, hc, hlt⟩ := (StrongAnchor.vanishes_iff_seed hN hb).mp hv
  exact absurd ((hD c).self_of_nhds c hc le_rfl) (not_lt.mpr hlt.le)

variable (N) in
/-- **No divergence of the seed window at the first failure**: wherever the read holds on `[0, b)`, the seed
window does not diverge at `b`. Calling such a divergence a critical point of the lattice theory is argued only.
DERIVED: `0` the left end. -/
def NoCriticalPoint : Prop :=
  ∀ b : ℝ, 0 < b → (∀ β : ℝ, 0 ≤ β → β < b → Vanishes N β) → ¬ SeedWindowDiverges N b

/-- **No stall is exactly no critical point.** DERIVED: `0` the left end. -/
theorem noStall_iff_noCriticalPoint (hN : N ≠ 0) : StrongAnchor.NoStall N ↔ NoCriticalPoint N := by
  constructor
  · intro h b hb hbelow hD
    exact (not_vanishes_iff_diverges hN hb.le).mpr hD (h b hb hbelow)
  · intro h b hb hbelow
    by_contra hv
    exact h b hb hbelow ((not_vanishes_iff_diverges hN hb.le).mp hv)

/-- **Capstone: no critical point gives the zero-flux gap (and the confined flux) at every coupling.** One input,
`NoCriticalPoint N`, equivalent to `StrongAnchor.NoStall N` (`noStall_iff_noCriticalPoint`). DERIVED: `0` the left
end. -/
theorem zeroFlux_of_noCriticalPoint [NeZero N] (h : NoCriticalPoint N) :
    (∀ β : ℝ, 0 ≤ β → FluxSplitCasimir.FluxConfinedAt N β) ∧ ∀ β : ℝ, 0 ≤ β → ZeroFluxVanishing N β :=
  FloorTension.noStall_iff_flux_zeroFlux.mp ((noStall_iff_noCriticalPoint (NeZero.ne N)).mpr h)

end MassGap.DisclosureFloor

#print axioms MassGap.DisclosureFloor.disclosure_free
#print axioms MassGap.DisclosureFloor.disclosure_free_rate
#print axioms MassGap.DisclosureFloor.spill_exact
#print axioms MassGap.DisclosureFloor.disclosure_free_exact
#print axioms MassGap.DisclosureFloor.disclosure_lattice_exact
#print axioms MassGap.DisclosureFloor.disclosure_tendsto
#print axioms MassGap.DisclosureFloor.constantPhysics_of_disclosure
#print axioms MassGap.DisclosureFloor.pos_of_noCritical
#print axioms MassGap.DisclosureFloor.pos_iff_noCritical
#print axioms MassGap.DisclosureFloor.free_rate_continuous
#print axioms MassGap.DisclosureFloor.free_critical
#print axioms MassGap.DisclosureFloor.free_massless_disclosure
#print axioms MassGap.DisclosureFloor.kink_counterexample
#print axioms MassGap.DisclosureFloor.diverges_of_not_vanishes
#print axioms MassGap.DisclosureFloor.vanishes_of_boundedSeed
#print axioms MassGap.DisclosureFloor.not_vanishes_iff_diverges
#print axioms MassGap.DisclosureFloor.noStall_iff_noCriticalPoint
#print axioms MassGap.DisclosureFloor.zeroFlux_of_noCriticalPoint
