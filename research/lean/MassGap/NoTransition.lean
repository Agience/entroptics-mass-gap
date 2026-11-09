import Mathlib
import MassGap.ApertureInvariance
import MassGap.EdgeCost
import MassGap.NonAbelianForget

/-!
# MassGap.NoTransition — the author's three reasons why the edge cost cannot fade between coarse and fine

The open bridge is `ApertureInvariance.RatioInvariant gLat rLat q C`: the gap in the observer's units
stays above a positive floor at every zoom, i.e. no phase transition along the line from the coarse
(strong-coupling) end to the fine (weak-coupling) end. Asked why the `SU(N)` edge cost cannot fade to
zero along that line when the `U(1)` one can, the author gave three reasons:

1. **Running is one-way**: the coupling only grows toward the coarse end (asymptotic freedom), so the
   edge cost only rises outward; there is nowhere for it to vanish.
2. **Edges cannot end**: the centre `Z_N` is finite, a flux edge cannot break into free pieces, and
   removing its cost would require breaking centre symmetry; the centre of `U(1)` is all of `U(1)`.
3. **One scale only**: pure Yang–Mills has one scale (the observer's); a transition needs a second
   scale; there is none.

This module states each link in terms of the existing objects, proves what each link implies, proves
the group facts, and tests each against the controls.

## 0. The line

`ratio gLat rLat k = gLat k / rLat k`, the gap in the observer's units at zoom `k` (`k` grows toward
the fine end). `Floor f`: a positive lower bound at every zoom. `ratioInvariant_iff_floor`:
`∃ q > 0, ∃ C, RatioInvariant gLat rLat q C` is exactly `Floor (ratio gLat rLat)`.
`floor_iff_pos_and_tail`: a floor is the same as positivity at every zoom plus a floor on a tail
`k ≥ K` (finitely many zooms below `K` have a positive minimum).

## 1. Running is one-way

Two forms.

* Running form. `oneLoop_coupling_strictMonoOn`: for `b₀ > 0` the one-loop coupling
  `g²(r) = 1/invCoup` strictly increases with physical distance on `(0, 1/Λ)`.
  `u1_not_oneWayRunning`: at `b₀ = 0` (`U(1)`) it is constant, so strict running fails on any two
  distances. This form is load-bearing against `U(1)`.
* Line form. `OneWay f := Antitone f`: the reading only rises toward the coarse end. It is an
  independent hypothesis, not derived from the running form: on the observer's line the coupling at
  the observer's distance is the same at every zoom (`coupling_at_observer_const`), so the running
  form says nothing about how a reading at that distance varies with the zoom.
  `floor_iff_limit_of_oneWay`: under `OneWay`, a floor is the same as a positive fine-end limit, and
  `floor_of_oneWay_tail`: a floor on a tail is a floor everywhere. So link 1 puts the minimum of the
  edge cost at the fine end (the continuum), which is where it has to be shown positive.
  `u1_oneWay_no_floor`: the `U(1)` profile (positive at the coarse end, zero from some zoom on) is
  antitone: `U(1)` satisfies the line form. `oneWay_not_sufficient`: an antitone, everywhere positive
  profile with no floor (`fade k = 1/(k+1)`). `oneWay_allows_jump`: a finite downward jump is
  antitone and keeps a floor; the line form does not forbid it. (That the `SU(N)` Wilson action at
  large `N` has a first-order bulk transition in the bare coupling — Creutz; Campostrini; Lucini–Teper
  — is cited, not proved here; the jump profile is the model of it.) `edgeRate_of_oneWay`: an antitone edge cost with fine-end limit `L > h` gives a uniform
  edge rate below one (`EdgeCost.uniform_edgeRate`).

The force `V'(r)` of the static potential is nonincreasing in `r` (concavity of the potential,
Bachas 1986, from reflection positivity; cited, not proved here), so "the edge cost rises outward" is read here as the
coupling, `g²(r)`, or as the reading along the zoom, never as the force.

Residual of link 1: the fine-end limit of the reading is positive. Under `OneWay` it is equivalent to
`RatioInvariant` (`floor_iff_limit_of_oneWay`), and monotone running beyond the Landau length is not
proved (only the one-loop form is).

## 2. Edges cannot end

* Group facts: `center_ZN_top` (`Z_N` is abelian: its centre is all of it), `noAbelianSector_ZN`
  (finite), `center_U1_top` (`U(1)`: centre all of it), `center_SU_ne_top` (`N ≥ 2`: the centre of
  `SU(N)` is proper; with `NonAbelianForget.center_SU_finite` it is finite and proper),
  `fundamental_edge_cannot_end` (from `EdgeCost.edge_can_end_iff`).
* `EdgesCannotEnd G σk := NoAbelianSector G → Floor σk`. `edgesCannotEnd_U1`: vacuous at `U(1)`
  (premise false), so `U(1)` is outside it. `zN_refutes_edgesCannotEnd`: the profile `σk` is free and
  tied to no group, so the Lean content is that a finite-centre premise (here `Z_N`'s, proved) forbids
  every profile with one zero. The physics enters as the hypothesis `hdec`: the deconfined phase of 4D
  `Z_N` (Creutz–Jacobs–Rebbi 1979; cited, not proved here) is a zoom of zero edge cost on a `Z_N` line.
  With that input, link 2 as stated wrongly forbids the `Z_N` transition.
* The named escape: `EdgesCannotEndNA G σk := NoAbelianSector G → center G ≠ ⊤ → Floor σk` (finite
  and proper centre). `zN_escapes`, `u1_escapes`: both abelian groups fall outside it.
  `edgesCannotEndNA_SU_iff`: at `SU(N)`, `N ≥ 2`, the link is exactly `Floor σk`: the premise is a
  group fact and the conclusion is the floor itself. `edgesCannotEndNA_SU_not_universal`: it cannot
  hold for every line over `SU(N)`, so its content is in the particular line (zero temperature,
  infinite volume), not in the group. `SU(N)` itself deconfines at finite temperature with the same
  finite centre (cited, not proved here): breaking a finite centre symmetry is allowed.

Residual of link 2: "the centre symmetry is unbroken at every zoom", i.e. `Floor σk` on the line.
Equal to the floor on the edge cost (a restatement once the group facts are proved), and it is a
floor on `σ`, not on the gap ratio; the passage from the edge cost to the gap is
`NonAbelianForget.ConfinedEdges`.

## 3. One scale only

* At finite coupling: `OneScale gLat rLat := ∀ k, 0 < gLat k ∧ 0 < rLat k` (the correlation length
  `1/gLat k` is finite at every zoom; a second scale at finite coupling is `ξ → ∞` there).
  `oneScale_segment`: a floor on every finite segment of zooms. `ratioInvariant_iff_tail_of_oneScale`:
  under `OneScale`, `RatioInvariant` is the floor on a tail. `u1_not_oneScale`: a zoom with zero gap
  breaks it; with the zero-gap zoom of 4D `U(1)` (the Coulomb-phase photon, Guth 1980,
  Fröhlich–Spencer 1982; cited, not proved here) as that input, `U(1)` fails it.
  `oneScale_not_sufficient`: `fade` satisfies it with no
  floor. `oneScale_allows_jump`: a finite jump keeps it and keeps `RatioInvariant` (that a
  first-order bulk transition has finite `ξ`, and so do the 4D `Z_2`, `Z_3`, `Z_4` transitions, is
  cited, not proved here).
* As a ratio: `OneScaleRatio ξ ℓ := ∃ D > 0, ∀ k, ξ k ≤ D ℓ k` (at every zoom, the correlation length
  within one factor of the observer's length). `oneScaleRatio_iff`: it is exactly
  `RatioInvariant (1/ξ) (1/ℓ)` with some `q > 0`. At the fine end both lengths diverge in lattice
  units (that is the continuum limit); "no second scale" there is the bridge itself.
* Running form (links 1 and 3 together). `invCoup_eq_of_rStar`: the one-loop coupling at distance `r`
  is `us − 2b₀ log(r / rStar)`. `coupling_at_observer_const`: on a line of fixed transmuted length
  `rStar = L` the coupling at the observer's distance is the same at every zoom. `af_line`: for
  `b₀ ≠ 0` such a line exists at every spacing. The `U(1)` contrast is `u1_not_oneWayRunning`: at
  `b₀ = 0` the coupling does not run. `ReadsOnlyCoupling R Φ`: the reading at zoom `k`
  is `Φ` of the coupling at the observer's distance (one scale, read exactly).
  `ratioInvariant_of_oneLoop_oneScale`: line plus exact reading plus a positive value at the first
  zoom give `RatioInvariant` with `q = ratio 0 > 0`, `C = 1`. `exact_reading_forbids_jump`: the exact
  form makes the reading constant, so it contradicts a bulk transition along the line;
  `ReadsCouplingWithin` (factor `C`) is the form compatible with it, and `readsCouplingWithin_iff`: on
  the line it is exactly `RatioInvariant` with `q = Φ(coupling at the observer)` (positivity of that
  `q` is not part of either side).

Residual of link 3: at finite coupling, nothing beyond pointwise positivity (weaker than
`RatioInvariant`; `oneScale_not_sufficient`); as a ratio, `OneScaleRatio` or
`ReadsCouplingWithin` with `q > 0`, each equal to `RatioInvariant`; read exactly, stronger than it and
false for lattice actions with a bulk transition.

## 4. The combination

`ratioInvariant_iff_links`: with link 3 at finite coupling, `RatioInvariant` is equivalent to
`NoFadeAtFineEnd` (a floor on a tail). `links_not_sufficient`: `fade` satisfies link 1 on the line and
link 3 at finite coupling, and fails `NoFadeAtFineEnd`. `all_links_not_sufficient`: the same `fade`
line together with the running form of link 1 (`b₀ > 0`) and the escaped link 2 at `SU(N)`, `N ≥ 2`
(on an edge-cost profile with a floor): all hold and `NoFadeAtFineEnd` fails. The edge cost `σk` and
the coupling are tied to `gLat`, `rLat` by no declaration, so the running form and link 2 constrain
other objects than the ratio. `physical_gap_of_links`: link 3 and `NoFadeAtFineEnd` on the observer's
line give a uniform positive physical gap (`ApertureInvariance.gap_of_ratioInvariant`). The three
links, in the forms stated here, move the open statement from every zoom to the fine end; none of
them, alone or combined, makes the fine end positive.

DERIVED (module-wide): `0` the sign of every floor and the first zoom; `1` the factor of the exact
form and of the step and fade profiles; `2` the high value of the step profile, `2b₀` the one-loop
normalisation of `EdgeCost.invCoup`; `0` and `1` the indices of the transposition in
`center_SU_ne_top`.
-/

noncomputable section

namespace MassGap.NoTransition

open Filter Topology
open MassGap.ApertureInvariance MassGap.EdgeCost MassGap.NonAbelianForget

variable {gLat rLat : ℕ → ℝ}

/-! ## 0. The line -/

/-- **A positive floor at every zoom.** -/
def Floor (f : ℕ → ℝ) : Prop := ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ f k

/-- The gap in the observer's units at zoom `k`. -/
def ratio (gLat rLat : ℕ → ℝ) (k : ℕ) : ℝ := gLat k / rLat k

/-- **`RatioInvariant` with `q > 0` is a floor on the ratio.** -/
theorem ratioInvariant_iff_floor (gLat rLat : ℕ → ℝ) :
    (∃ q C : ℝ, 0 < q ∧ RatioInvariant gLat rLat q C) ↔ Floor (ratio gLat rLat) := by
  constructor
  · rintro ⟨q, C, hq, hC, hk⟩
    exact ⟨q / C, div_pos hq hC, fun k => (div_le_iff₀' hC).2 (hk k)⟩
  · rintro ⟨c, hc, hk⟩
    exact ⟨c, 1, hc, one_pos, fun k => by rw [one_mul]; exact hk k⟩

/-- Finitely many positive readings have a positive minimum. -/
theorem floor_of_initial (f : ℕ → ℝ) (hpos : ∀ k, 0 < f k) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ k < K, c ≤ f k := by
  induction K with
  | zero => exact ⟨1, one_pos, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ K ih =>
    obtain ⟨c, hc, hk⟩ := ih
    refine ⟨min c (f K), lt_min hc (hpos K), fun k hkK => ?_⟩
    rcases (show k < K ∨ k = K by omega) with h | h
    · exact (min_le_left _ _).trans (hk k h)
    · rw [h]; exact min_le_right _ _

/-- **A floor is positivity at every zoom plus a floor on a tail.** -/
theorem floor_iff_pos_and_tail (f : ℕ → ℝ) :
    Floor f ↔ (∀ k, 0 < f k) ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, c ≤ f k := by
  constructor
  · rintro ⟨c, hc, hk⟩
    exact ⟨fun k => hc.trans_le (hk k), c, hc, Filter.Eventually.of_forall hk⟩
  · rintro ⟨hpos, c, hc, ht⟩
    obtain ⟨K, hK⟩ := eventually_atTop.mp ht
    obtain ⟨c', hc', hk'⟩ := floor_of_initial f hpos K
    refine ⟨min c c', lt_min hc hc', fun k => ?_⟩
    rcases lt_or_ge k K with h | h
    · exact (min_le_right _ _).trans (hk' k h)
    · exact (min_le_left _ _).trans (hK k h)

/-! ## Control profiles -/

/-- A two-valued profile: `hi` below zoom `k₁`, `lo` from `k₁` on. -/
def stepProfile (k₁ : ℕ) (hi lo : ℝ) (k : ℕ) : ℝ := if k < k₁ then hi else lo

theorem stepProfile_antitone {k₁ : ℕ} {hi lo : ℝ} (h : lo ≤ hi) :
    Antitone (stepProfile k₁ hi lo) := by
  intro a b hab
  unfold stepProfile
  by_cases hb : b < k₁
  · have ha : a < k₁ := lt_of_le_of_lt hab hb
    simp [ha, hb]
  · by_cases ha : a < k₁
    · simp [ha, hb, h]
    · simp [ha, hb]

/-- A profile positive at every zoom that tends to `0` at the fine end: `1/(k+1)`. -/
def fade (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem fade_pos (k : ℕ) : 0 < fade k := by unfold fade; positivity

theorem fade_antitone : Antitone fade := by
  intro a b hab
  unfold fade
  have h1 : ((a : ℝ) + 1) ≤ (b : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hab; linarith
  exact one_div_le_one_div_of_le (by positivity) h1

theorem fade_not_floor : ¬ Floor fade := by
  rintro ⟨c, hc, hk⟩
  obtain ⟨k, hk'⟩ :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)).exists
  have h := hk k
  unfold fade at h
  linarith

theorem ratio_fade_one : ratio fade (fun _ => 1) = fade := by
  funext k; simp [ratio]

/-! ## 1. Running is one-way -/

/-- **Link 1, running form.** For `b₀ > 0` the one-loop coupling `g²(r) = 1/invCoup` strictly
increases with physical distance on `(0, 1/Λ)`, `1/Λ = rStar b₀ r₀ u₀ 0`. -/
theorem oneLoop_coupling_strictMonoOn {b₀ r₀ u₀ : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) :
    StrictMonoOn (fun r => (invCoup b₀ r₀ u₀ r)⁻¹) (Set.Ioo 0 (rStar b₀ r₀ u₀ 0)) := by
  intro r hr r' hr' hlt
  have hpos : 0 < invCoup b₀ r₀ u₀ r := (invCoup_pos_iff hb hr₀ hr.1).2 hr.2
  have hpos' : 0 < invCoup b₀ r₀ u₀ r' := (invCoup_pos_iff hb hr₀ hr'.1).2 hr'.2
  have hanti := invCoup_strictAntiOn (u₀ := u₀) hb hr₀ (Set.mem_Ioi.2 hr.1) (Set.mem_Ioi.2 hr'.1) hlt
  exact (inv_lt_inv₀ hpos hpos').2 hanti

/-- **`U(1)` fails link 1, running form**: at `b₀ = 0` the coupling is the same at every distance, so
it is not strictly increasing on any set with two points. -/
theorem u1_not_oneWayRunning (r₀ u₀ : ℝ) {s : Set ℝ} {r r' : ℝ} (hr : r ∈ s) (hr' : r' ∈ s)
    (hlt : r < r') : ¬ StrictMonoOn (fun x => (invCoup 0 r₀ u₀ x)⁻¹) s := by
  intro h
  have := h hr hr' hlt
  simp only [invCoup_abelian] at this
  exact lt_irrefl _ this

/-- **Link 1, line form**: the reading only rises toward the coarse end (antitone in the zoom). An
independent hypothesis: it is not derived from the running form, since on the observer's line the
coupling at the observer's distance is the same at every zoom (`coupling_at_observer_const`). -/
def OneWay (f : ℕ → ℝ) : Prop := Antitone f

/-- **Under link 1 a floor is a positive fine-end limit.** -/
theorem floor_iff_limit_of_oneWay {f : ℕ → ℝ} (h : OneWay f) :
    Floor f ↔ ∃ L : ℝ, 0 < L ∧ Tendsto f atTop (𝓝 L) := by
  constructor
  · rintro ⟨c, hc, hk⟩
    have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hk k⟩
    exact ⟨⨅ k, f k, lt_of_lt_of_le hc (le_ciInf hk), tendsto_atTop_ciInf h hbdd⟩
  · rintro ⟨L, hL, ht⟩
    exact ⟨L, hL, fun k => h.le_of_tendsto ht k⟩

/-- **Under link 1 a floor on a tail is a floor at every zoom.** -/
theorem floor_of_oneWay_tail {f : ℕ → ℝ} (h : OneWay f) {c : ℝ} (hc : 0 < c)
    (ht : ∀ᶠ k in atTop, c ≤ f k) : Floor f := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp ht
  exact ⟨c, hc, fun k => (hK (max k K) (le_max_right _ _)).trans (h (le_max_left _ _))⟩

/-- **`U(1)` satisfies link 1, line form**: positive edge cost at the coarse end, zero from zoom `k₁`
on (the model of the 4D Coulomb phase; that phase is cited, not proved here) is antitone and has no
floor. -/
theorem u1_oneWay_no_floor (k₁ : ℕ) {hi : ℝ} (hhi : 0 ≤ hi) :
    OneWay (stepProfile k₁ hi 0) ∧ ¬ Floor (stepProfile k₁ hi 0) := by
  refine ⟨stepProfile_antitone hhi, ?_⟩
  rintro ⟨c, hc, hk⟩
  have := hk k₁
  simp [stepProfile] at this
  linarith

/-- **Link 1, line form, does not give a floor**: `fade` is antitone and positive at every zoom. -/
theorem oneWay_not_sufficient : OneWay fade ∧ (∀ k, 0 < fade k) ∧ ¬ Floor fade :=
  ⟨fade_antitone, fade_pos, fade_not_floor⟩

/-- **Link 1, line form, allows a finite jump** (the model of a bulk first-order transition; the
transition itself is cited, not proved here): antitone, with a floor. -/
theorem oneWay_allows_jump (k₁ : ℕ) : OneWay (stepProfile k₁ 2 1) ∧ Floor (stepProfile k₁ 2 1) := by
  refine ⟨stepProfile_antitone (by norm_num), 1, one_pos, fun k => ?_⟩
  unfold stepProfile; split_ifs <;> norm_num

/-- **An antitone edge cost with fine-end limit above the entropy gives a uniform edge rate.** -/
theorem edgeRate_of_oneWay {σk : ℕ → ℝ} (h : OneWay σk) {L hent slab : ℝ}
    (hL : Tendsto σk atTop (𝓝 L)) (hLh : hent < L) (hs : 0 < slab) :
    ∃ q : ℝ, q < 1 ∧ ∀ k, NonAbelianForget.edgeRate (σk k) hent slab ≤ q :=
  uniform_edgeRate (fun k => h.le_of_tendsto hL k) hLh hs

/-! ## 2. Edges cannot end -/

section Centre

open Matrix

/-- `Z_N` as a multiplicative group. -/
abbrev ZN (N : ℕ) : Type := Multiplicative (ZMod N)

/-- **The centre of `Z_N` is all of `Z_N`.** -/
theorem center_ZN_top (N : ℕ) : Subgroup.center (ZN N) = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun z => Subgroup.mem_center_iff.mpr fun g => mul_comm g z

/-- **`Z_N` has a finite centre.** -/
theorem noAbelianSector_ZN (N : ℕ) [NeZero N] : NoAbelianSector (ZN N) := Set.toFinite _

/-- **The centre of `U(1)` is all of `U(1)`.** -/
theorem center_U1_top : Subgroup.center U1 = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun z => Subgroup.mem_center_iff.mpr fun g => ?_
  apply Subtype.ext
  show (g : Matrix (Fin 1) (Fin 1) ℂ) * (z : Matrix (Fin 1) (Fin 1) ℂ)
    = (z : Matrix (Fin 1) (Fin 1) ℂ) * (g : Matrix (Fin 1) (Fin 1) ℂ)
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

/-- **The centre of `SU(N)`, `N ≥ 2`, is proper**: the signed transposition is not central. -/
theorem center_SU_ne_top {N : ℕ} (hN : 2 ≤ N) : Subgroup.center (MassGap.SUN.SU N) ≠ ⊤ := by
  intro htop
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  have hpq : (⟨0, h0⟩ : Fin N) ≠ ⟨1, h1⟩ := fun h => absurd (congrArg Fin.val h) (by norm_num)
  have hs : (⟨swapElt (𝕜 := ℂ) ⟨0, h0⟩ ⟨1, h1⟩, swapElt_mem hpq⟩ : MassGap.SUN.SU N)
      ∈ Subgroup.center (MassGap.SUN.SU N) := by
    rw [htop]; exact Subgroup.mem_top _
  have hcomm : Commutes (swapElt (𝕜 := ℂ) (⟨0, h0⟩ : Fin N) ⟨1, h1⟩) := by
    intro g hg
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hs) ⟨g, hg⟩)
  have hz := (commutant_SU hcomm).1 _ _ hpq
  rw [swapElt_apply hpq] at hz
  exact one_ne_zero hz

/-- **A single fundamental edge cannot end on gluons** (`N ≥ 2`): its centre phase is not `1`. -/
theorem fundamental_edge_cannot_end {N : ℕ} (hN : 2 ≤ N) {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    (m : ℕ) : ω ^ 1 * (ω * star ω) ^ m ≠ 1 := by
  intro h0
  have h := (edge_can_end_iff (by omega) hω 1 m).1 h0
  have := Nat.le_of_dvd one_pos h
  omega

/-- **Link 2 as stated**: a finite centre gives a floor on the edge cost along the line. -/
def EdgesCannotEnd (G : Type) [Group G] (σk : ℕ → ℝ) : Prop := NoAbelianSector G → Floor σk

/-- **At `U(1)` link 2 is vacuous** (infinite centre): `U(1)` is outside it. -/
theorem edgesCannotEnd_U1 (σk : ℕ → ℝ) : EdgesCannotEnd U1 σk :=
  fun h => absurd h not_noAbelianSector_U1

/-- **A finite-centre premise forbids every profile with one zero.** `σk` is free and tied to no group;
the premise used is `Z_N`'s finite centre (proved). The `Z_N` deconfined phase (Creutz–Jacobs–Rebbi;
cited, not proved here) enters only as the hypothesis `hdec`. -/
theorem zN_refutes_edgesCannotEnd (N : ℕ) [NeZero N] {σk : ℕ → ℝ} {k₀ : ℕ} (hdec : σk k₀ = 0) :
    ¬ EdgesCannotEnd (ZN N) σk := by
  intro h
  obtain ⟨c, hc, hk⟩ := h (noAbelianSector_ZN N)
  have := hk k₀
  rw [hdec] at this
  linarith

/-- **Link 2 with its escape named**: a finite and proper centre gives a floor on the edge cost. -/
def EdgesCannotEndNA (G : Type) [Group G] (σk : ℕ → ℝ) : Prop :=
  NoAbelianSector G → Subgroup.center G ≠ ⊤ → Floor σk

/-- **`Z_N` escapes**: its centre is all of it. -/
theorem zN_escapes (N : ℕ) (σk : ℕ → ℝ) : EdgesCannotEndNA (ZN N) σk :=
  fun _ h => absurd (center_ZN_top N) h

/-- **`U(1)` escapes**: its centre is all of it. -/
theorem u1_escapes (σk : ℕ → ℝ) : EdgesCannotEndNA U1 σk :=
  fun _ h => absurd center_U1_top h

/-- **At `SU(N)`, `N ≥ 2`, link 2 is the floor itself**: its premise is a proved group fact. -/
theorem edgesCannotEndNA_SU_iff {N : ℕ} (hN : 2 ≤ N) (σk : ℕ → ℝ) :
    EdgesCannotEndNA (MassGap.SUN.SU N) σk ↔ Floor σk := by
  haveI : NeZero N := ⟨by omega⟩
  exact ⟨fun h => h (noAbelianSector_SU N) (center_SU_ne_top hN), fun h _ _ => h⟩

/-- **Link 2 is not a property of the group**: it fails for some line over `SU(N)`. -/
theorem edgesCannotEndNA_SU_not_universal {N : ℕ} (hN : 2 ≤ N) :
    ¬ ∀ σk : ℕ → ℝ, EdgesCannotEndNA (MassGap.SUN.SU N) σk := fun h =>
  fade_not_floor ((edgesCannotEndNA_SU_iff hN fade).1 (h fade))

end Centre

/-! ## 3. One scale only -/

/-- **Link 3 at finite coupling**: gap and observer's reading positive in lattice units at every zoom
(the correlation length `1/gLat k` finite at every zoom of the line).
DERIVED: `0` the sign; `3` the index of this link among the module's three links. -/
def OneScale (gLat rLat : ℕ → ℝ) : Prop := ∀ k, 0 < gLat k ∧ 0 < rLat k

theorem oneScale_ratio_pos (h : OneScale gLat rLat) (k : ℕ) : 0 < ratio gLat rLat k :=
  div_pos (h k).1 (h k).2

/-- **Link 3 gives a floor on every finite segment of zooms.** -/
theorem oneScale_segment (h : OneScale gLat rLat) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ k < K, c ≤ ratio gLat rLat k :=
  floor_of_initial _ (oneScale_ratio_pos h) K

/-- **Under link 3, `RatioInvariant` is a floor on a tail.** -/
theorem ratioInvariant_iff_tail_of_oneScale (h : OneScale gLat rLat) :
    (∃ q C : ℝ, 0 < q ∧ RatioInvariant gLat rLat q C) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, c ≤ ratio gLat rLat k := by
  rw [ratioInvariant_iff_floor, floor_iff_pos_and_tail]
  exact ⟨fun h' => h'.2, fun h' => ⟨oneScale_ratio_pos h, h'⟩⟩

/-- **A zoom with zero gap breaks link 3.** The `U(1)` reading of the hypothesis (the Coulomb-phase
photon, `ξ = ∞` at finite coupling) is cited, not proved here. -/
theorem u1_not_oneScale {k₁ : ℕ} (hk₁ : gLat k₁ = 0) : ¬ OneScale gLat rLat :=
  fun h => (h k₁).1.ne' hk₁

/-- **Link 3 at finite coupling does not give `RatioInvariant`**: `fade` with a unit observer. -/
theorem oneScale_not_sufficient :
    OneScale fade (fun _ => 1) ∧ ∀ q C : ℝ, 0 < q → ¬ RatioInvariant fade (fun _ => 1) q C := by
  refine ⟨fun k => ⟨fade_pos k, one_pos⟩, fun q C hq hR => fade_not_floor ?_⟩
  have h := (ratioInvariant_iff_floor _ _).1 ⟨q, C, hq, hR⟩
  rwa [ratio_fade_one] at h

/-- **Link 3 allows a finite jump** (the model of a first-order transition with finite correlation
length; such transitions are cited, not proved here) and `RatioInvariant`
holds across it. -/
theorem oneScale_allows_jump (k₁ : ℕ) :
    OneScale (stepProfile k₁ 2 1) (fun _ => 1) ∧
      RatioInvariant (stepProfile k₁ 2 1) (fun _ => 1) 1 1 := by
  refine ⟨fun k => ⟨?_, one_pos⟩, one_pos, fun k => ?_⟩
  · unfold stepProfile; split_ifs <;> norm_num
  · simp only [div_one, one_mul]; unfold stepProfile; split_ifs <;> norm_num

/-- **Link 3 as a ratio**: at every zoom, the correlation length is within one factor `D` of the
observer's length. DERIVED: `0` the sign of `D`; `3` the index of this link among the module's three
links. -/
def OneScaleRatio (ξ ℓ : ℕ → ℝ) : Prop := ∃ D : ℝ, 0 < D ∧ ∀ k, ξ k ≤ D * ℓ k

/-- **Link 3 as a ratio is `RatioInvariant`** for the gap `1/ξ` and the observer's reading `1/ℓ`. -/
theorem oneScaleRatio_iff {ξ ℓ : ℕ → ℝ} (hξ : ∀ k, 0 < ξ k) (hℓ : ∀ k, 0 < ℓ k) :
    OneScaleRatio ξ ℓ ↔
      ∃ q C : ℝ, 0 < q ∧ RatioInvariant (fun k => 1 / ξ k) (fun k => 1 / ℓ k) q C := by
  have e : ∀ k, (1 / ξ k) / (1 / ℓ k) = ℓ k / ξ k := fun k => by
    have := (hξ k).ne'; have := (hℓ k).ne'; field_simp
  rw [ratioInvariant_iff_floor]
  constructor
  · rintro ⟨D, hD, hk⟩
    refine ⟨1 / D, by positivity, fun k => ?_⟩
    show 1 / D ≤ (1 / ξ k) / (1 / ℓ k)
    rw [e, le_div_iff₀ (hξ k), div_mul_eq_mul_div, one_mul, div_le_iff₀ hD, mul_comm]
    exact hk k
  · rintro ⟨c, hc, hk⟩
    refine ⟨1 / c, by positivity, fun k => ?_⟩
    have h1 : c ≤ (1 / ξ k) / (1 / ℓ k) := hk k
    rw [e, le_div_iff₀ (hξ k)] at h1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
    exact h1

/-! ### Links 1 and 3 through the running -/

/-- **The one-loop coupling at distance `r` is fixed by the transmuted length.**

DERIVED: `2b₀` the normalisation of `invCoup`. -/
theorem invCoup_eq_of_rStar {b₀ a u₀ us r : ℝ} (hb : b₀ ≠ 0) (ha : 0 < a) (hr : 0 < r) :
    invCoup b₀ a u₀ r = us - 2 * b₀ * Real.log (r / rStar b₀ a u₀ us) := by
  simp only [invCoup, rStar]
  rw [Real.log_div hr.ne' (mul_pos ha (Real.exp_pos _)).ne',
    Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hr.ne' ha.ne']
  have h2 : 2 * b₀ * ((u₀ - us) / (2 * b₀)) = u₀ - us := by field_simp
  linear_combination -h2

/-- **On a line of fixed transmuted length the coupling at the observer's distance is the same at
every zoom.** -/
theorem coupling_at_observer_const {b₀ us L r : ℝ} (hb : b₀ ≠ 0) (hr : 0 < r) {a u₀ : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (hline : ∀ k, rStar b₀ (a k) (u₀ k) us = L) (k : ℕ) :
    invCoup b₀ (a k) (u₀ k) r = us - 2 * b₀ * Real.log (r / L) := by
  rw [invCoup_eq_of_rStar (us := us) hb (ha k) hr, hline k]

/-- **The asymptotically free line exists at every spacing**: `u₀ = us + 2b₀ log(L/a)` gives
transmuted length `L`. -/
theorem af_line {b₀ us L a : ℝ} (hb : b₀ ≠ 0) (ha : 0 < a) (hL : 0 < L) :
    rStar b₀ a (us + 2 * b₀ * Real.log (L / a)) us = L := by
  simp only [rStar]
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hb),
    Real.exp_log (div_pos hL ha), mul_div_assoc']
  exact mul_div_cancel_left₀ L ha.ne'

/-- **One scale, read exactly through the running**: the reading at zoom `k` is `Φ` of the coupling
at the observer's distance `r`. -/
def ReadsOnlyCoupling (R : ℕ → ℝ) (Φ : ℝ → ℝ) (b₀ r : ℝ) (a u₀ : ℕ → ℝ) : Prop :=
  ∀ k, R k = Φ (invCoup b₀ (a k) (u₀ k) r)

/-- On the line the exact reading is the same at every zoom. -/
theorem reading_const_of_oneScale {R : ℕ → ℝ} {Φ : ℝ → ℝ} {b₀ us L r : ℝ} (hb : b₀ ≠ 0)
    (hr : 0 < r) {a u₀ : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hline : ∀ k, rStar b₀ (a k) (u₀ k) us = L)
    (hreads : ReadsOnlyCoupling R Φ b₀ r a u₀) (k : ℕ) : R k = R 0 := by
  rw [hreads k, hreads 0, coupling_at_observer_const hb hr ha hline k,
    coupling_at_observer_const hb hr ha hline 0]

/-- **Links 1 and 3, exact form, give `RatioInvariant` with factor `1`**: on a one-loop line, a
ratio that reads only the coupling at the observer's distance and is positive at the first zoom has
`RatioInvariant` with `q = ratio 0 > 0`. -/
theorem ratioInvariant_of_oneLoop_oneScale {Φ : ℝ → ℝ} {b₀ us L r : ℝ} (hb : b₀ ≠ 0) (hr : 0 < r)
    {a u₀ : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hline : ∀ k, rStar b₀ (a k) (u₀ k) us = L)
    (hreads : ReadsOnlyCoupling (ratio gLat rLat) Φ b₀ r a u₀) (h0 : 0 < ratio gLat rLat 0) :
    0 < ratio gLat rLat 0 ∧ RatioInvariant gLat rLat (ratio gLat rLat 0) 1 := by
  refine ⟨h0, one_pos, fun k => ?_⟩
  show ratio gLat rLat 0 ≤ 1 * ratio gLat rLat k
  rw [one_mul, reading_const_of_oneScale hb hr ha hline hreads k]

/-- **The exact form forbids a bulk transition**: on the line a reading that differs at two zooms is
not an exact function of the coupling at the observer's distance. -/
theorem exact_reading_forbids_jump {R : ℕ → ℝ} {Φ : ℝ → ℝ} {b₀ us L r : ℝ} (hb : b₀ ≠ 0)
    (hr : 0 < r) {a u₀ : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hline : ∀ k, rStar b₀ (a k) (u₀ k) us = L)
    {k₁ k₂ : ℕ} (hjump : R k₁ ≠ R k₂) : ¬ ReadsOnlyCoupling R Φ b₀ r a u₀ := fun hreads =>
  hjump (by rw [reading_const_of_oneScale hb hr ha hline hreads k₁,
    reading_const_of_oneScale hb hr ha hline hreads k₂])

/-- **One scale up to a factor**: `Φ` of the coupling at the observer's distance is within `C` of the
reading at every zoom. The value `Φ(…)` is not required to be positive; a floor needs it positive. -/
def ReadsCouplingWithin (R : ℕ → ℝ) (Φ : ℝ → ℝ) (C b₀ r : ℝ) (a u₀ : ℕ → ℝ) : Prop :=
  0 < C ∧ ∀ k, Φ (invCoup b₀ (a k) (u₀ k) r) ≤ C * R k

/-- **On the line, one scale up to a factor is `RatioInvariant`** with `q` the value of `Φ` at the
coupling at the observer's distance. Neither side requires `q > 0`. -/
theorem readsCouplingWithin_iff {Φ : ℝ → ℝ} {C b₀ us L r : ℝ} (hb : b₀ ≠ 0) (hr : 0 < r)
    {a u₀ : ℕ → ℝ} (ha : ∀ k, 0 < a k) (hline : ∀ k, rStar b₀ (a k) (u₀ k) us = L) :
    ReadsCouplingWithin (ratio gLat rLat) Φ C b₀ r a u₀ ↔
      RatioInvariant gLat rLat (Φ (us - 2 * b₀ * Real.log (r / L))) C := by
  unfold ReadsCouplingWithin RatioInvariant
  simp only [coupling_at_observer_const hb hr ha hline]
  exact Iff.rfl

/-- **The factor form allows a jump**: a step reading is within factor `1` of the constant `1` (here
`Φ ≡ 1 > 0`). -/
theorem within_allows_jump (k₁ : ℕ) (b₀ r : ℝ) (a u₀ : ℕ → ℝ) :
    ReadsCouplingWithin (stepProfile k₁ 2 1) (fun _ => 1) 1 b₀ r a u₀ := by
  refine ⟨one_pos, fun k => ?_⟩
  rw [one_mul]; unfold stepProfile; split_ifs <;> norm_num

/-! ## 4. The combination -/

/-- **The remaining statement, in the author's terms: the edge cost does not fade at the fine end.** A
positive floor on the ratio from some zoom on. -/
def NoFadeAtFineEnd (gLat rLat : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, c ≤ ratio gLat rLat k

/-- **With link 3, `RatioInvariant` is exactly `NoFadeAtFineEnd`.** -/
theorem ratioInvariant_iff_links (h3 : OneScale gLat rLat) :
    (∃ q C : ℝ, 0 < q ∧ RatioInvariant gLat rLat q C) ↔ NoFadeAtFineEnd gLat rLat :=
  ratioInvariant_iff_tail_of_oneScale h3

/-- **With link 1 on the ratio, `NoFadeAtFineEnd` is a positive fine-end limit.** -/
theorem noFade_iff_limit_of_oneWay (h1 : OneWay (ratio gLat rLat)) :
    NoFadeAtFineEnd gLat rLat ↔ ∃ L : ℝ, 0 < L ∧ Tendsto (ratio gLat rLat) atTop (𝓝 L) := by
  rw [← floor_iff_limit_of_oneWay h1]
  constructor
  · rintro ⟨c, hc, ht⟩; exact floor_of_oneWay_tail h1 hc ht
  · intro h; exact ((floor_iff_pos_and_tail _).1 h).2

/-- **Links 1 and 3 on the line, together, do not give `NoFadeAtFineEnd`.** -/
theorem links_not_sufficient :
    OneWay (ratio fade (fun _ => 1)) ∧ OneScale fade (fun _ => 1) ∧
      ¬ NoFadeAtFineEnd fade (fun _ => 1) := by
  refine ⟨by rw [ratio_fade_one]; exact fade_antitone, fun k => ⟨fade_pos k, one_pos⟩, ?_⟩
  intro h
  have hf := (ratioInvariant_iff_links (fun k => ⟨fade_pos k, one_pos⟩)).2 h
  obtain ⟨q, C, hq, hR⟩ := hf
  exact oneScale_not_sufficient.2 q C hq hR

/-- **All three links, in the forms stated here, do not give `NoFadeAtFineEnd`.** The `fade` line
satisfies link 1 (line form) and link 3; the one-loop running at `b₀ > 0` satisfies link 1 (running
form); the edge cost `≡ 1` satisfies the escaped link 2 at `SU(N)`, `N ≥ 2`. The edge cost and the
coupling are tied to the ratio by no declaration. -/
theorem all_links_not_sufficient {N : ℕ} (hN : 2 ≤ N) {b₀ r₀ u₀ : ℝ} (hb : 0 < b₀) (hr₀ : 0 < r₀) :
    OneWay (ratio fade (fun _ => 1)) ∧ OneScale fade (fun _ => 1) ∧
      StrictMonoOn (fun r => (invCoup b₀ r₀ u₀ r)⁻¹) (Set.Ioo 0 (rStar b₀ r₀ u₀ 0)) ∧
      EdgesCannotEndNA (MassGap.SUN.SU N) (fun _ => 1) ∧ ¬ NoFadeAtFineEnd fade (fun _ => 1) := by
  obtain ⟨h1, h3, hno⟩ := links_not_sufficient
  exact ⟨h1, h3, oneLoop_coupling_strictMonoOn hb hr₀,
    (edgesCannotEndNA_SU_iff hN _).2 ⟨1, one_pos, fun _ => le_rfl⟩, hno⟩

/-- **Link 3 and `NoFadeAtFineEnd` on the observer's line give a uniform positive physical gap.** -/
theorem physical_gap_of_links {a : ℕ → ℝ} {r₀ : ℝ} (hr0 : 0 < r₀) (h3 : OneScale gLat rLat)
    (hfine : NoFadeAtFineEnd gLat rLat) (ha : ∀ k, a k ≠ 0) (hline : ∀ k, rLat k / a k = r₀) :
    ∃ m : ℝ, 0 < m ∧ ∀ k, m ≤ gLat k / a k := by
  obtain ⟨q, C, hq, hR⟩ := (ratioInvariant_iff_links h3).2 hfine
  obtain ⟨hm, hk⟩ := gap_of_ratioInvariant hq hr0 hR ha (fun k => (h3 k).2.ne') hline
  exact ⟨_, hm, hk⟩

#print axioms ratioInvariant_iff_floor
#print axioms floor_iff_pos_and_tail
#print axioms fade_not_floor
#print axioms oneLoop_coupling_strictMonoOn
#print axioms u1_not_oneWayRunning
#print axioms floor_iff_limit_of_oneWay
#print axioms floor_of_oneWay_tail
#print axioms u1_oneWay_no_floor
#print axioms oneWay_not_sufficient
#print axioms oneWay_allows_jump
#print axioms edgeRate_of_oneWay
#print axioms center_ZN_top
#print axioms noAbelianSector_ZN
#print axioms center_U1_top
#print axioms center_SU_ne_top
#print axioms fundamental_edge_cannot_end
#print axioms edgesCannotEnd_U1
#print axioms zN_refutes_edgesCannotEnd
#print axioms zN_escapes
#print axioms u1_escapes
#print axioms edgesCannotEndNA_SU_iff
#print axioms edgesCannotEndNA_SU_not_universal
#print axioms oneScale_segment
#print axioms ratioInvariant_iff_tail_of_oneScale
#print axioms u1_not_oneScale
#print axioms oneScale_not_sufficient
#print axioms oneScale_allows_jump
#print axioms oneScaleRatio_iff
#print axioms invCoup_eq_of_rStar
#print axioms coupling_at_observer_const
#print axioms af_line
#print axioms ratioInvariant_of_oneLoop_oneScale
#print axioms exact_reading_forbids_jump
#print axioms readsCouplingWithin_iff
#print axioms within_allows_jump
#print axioms ratioInvariant_iff_links
#print axioms noFade_iff_limit_of_oneWay
#print axioms links_not_sufficient
#print axioms all_links_not_sufficient
#print axioms physical_gap_of_links

end MassGap.NoTransition
