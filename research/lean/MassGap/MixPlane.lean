import Mathlib
import MassGap.MixAnchor
import MassGap.StrongAnchor

/-!
# MassGap.MixPlane — the coupling plane `(β, β_⊥)` and where the strong end sits in it

The bridge is `CouplingTower.StrongEnd N`. This module places it in the closed quadrant of couplings
`(β, β_⊥)`, `β` on the in-plane plaquettes and `β_⊥` on the mixed ones (`AnisoTorus.DA`). Declarations are in
`MassGap.MixPlane`.

## The picture

* `continuous_DA₂`: at a fixed window, `(β, β_⊥) ↦ DA N β β_⊥ w` is continuous on `ℝ²`.
* `VanishSet N`: the points of the quadrant `Quad = [0, ∞)²` at which `DA N β β_⊥ · → 0` along the windows.
  `mem_vanishSet_iff_seed` / `mem_vanishSet_iff_seed_lt`: membership is a seed window `w ≥ 1` with
  `DA ≤ 1/1000` (or `< 1/1000`); the squaring `MixAnchor.DA_succ_le` reads `β, β_⊥ ≥ 0`, which is why the set
  lives in the quadrant. `vanishSet_eq`, `exists_open_vanishSet`: `VanishSet N = U ∩ Quad` with `U` open, the
  union over windows of the strict seed sets. `eventually_mem_vanishSet`: a point of the set has a quadrant
  neighbourhood in it.
* `StallSet N = Quad \ VanishSet N`. `isClosed_stallSet`: it is closed in `ℝ²` (so relatively closed in the
  quadrant).
* Anchors. `zero_mem_vanishSet`: the origin, with no input (`StrongAnchor.vanishes_zero` through `DA_iso`).
  `exists_ball_origin`: a quadrant ball around the origin lies in `VanishSet N`, with no input.
  `axis_mem_vanishSet`: `(β, 0)` under the cited `LayerSplit.TwoDCharacter N β`, through
  `DecoupledSplit.decoupled_vanishes_of_twoD`. `diag_anchor`: `(β, β)` for `β ∈ [0, b)`, from
  `StrongAnchor.strongAnchor` and `DA_iso`.
* The one statement. `diag_mem_iff`: `(β, β) ∈ VanishSet N ↔ 0 ≤ β ∧ StrongAnchor.Vanishes N β`.
  `strongEnd_iff_diag`: `StrongEnd N ↔ ∃ᶠ β in atTop, (β, β) ∈ VanishSet N`.
* The geometric remaining input. `NoStallOnSegment N β`: the vertical segment `{(β, t) | 0 ≤ t ≤ β}` misses
  `StallSet N`. `diag_mem_of_noStallOnSegment`: it gives `(β, β) ∈ VanishSet N` at `β ≥ 0` (the endpoint is on
  the segment; `TwoDCharacter` is not read). `strongEnd_of_noStallOnSegment`: frequently in `β` it gives the
  strong end.
* First stall. `first_stall_of_path`: along any continuous path in the quadrant that starts in `VanishSet N` and
  meets `StallSet N` on `[0, a]`, there is a least parameter `t* ∈ (0, a]` with the path in `StallSet N` at `t*`
  and in `VanishSet N` on `[0, t*)` (closedness of `StallSet N`; `t* > 0` because the start vanishes).
  `segment_first_stall`: on the vertical segment from the axis anchor `(β, 0)`, under `TwoDCharacter N β`.
  `diag_first_stall`: on the diagonal from the origin, with no input; its `t*` is at least the isotropic anchor
  length (`diag_first_stall_ge`).

DERIVED (module-wide): `0` the lower ends, the decoupled end and the limit; `1` the least window. Inherited:
`1/1000` the seed of `DoublingSharp` (through `MixAnchor.tendsto_DA_of_seed`).

## Two first stalls of one kind

`segment_first_stall` and `diag_first_stall` are the same statement: a stall boundary inside the quadrant, met
first at a positive parameter along a path that starts at a proved anchor. The axis start costs the cited 2D
character expansion; the diagonal start costs nothing. Either `t*` is where a proof of the strong end has to act:
at `(β, t*)` or `(t*, t*)` the window defect stays outside the basin at every window although it vanishes along
the windows at every earlier point of the path.

## U(1) (argued, not proved)

Nothing in this module reads the non-abelian structure of `SU(N)` beyond what `DA_succ_le` and the 2D anchor read.
For `U(1)` the 4D theory at large isotropic coupling is in its Coulomb phase (Guth 1980; Fröhlich–Spencer 1982),
where the window coupling is expected to stall; the axis is expected to vanish by the 2D picture. So for `U(1)` the
stall set is expected to be non-empty, with a first stall on the segment above each large `β`. This is argued, not
proved here. Nothing here excludes a non-empty stall set for `SU(N)`.

## What does not follow

`strongEnd_iff_diag` restates `StrongEnd N` in the plane; it discharges nothing. `NoStallOnSegment N β` is a
stronger sufficient condition for the same statement, frequently in `β` (`strongEnd_of_noStallOnSegment` is one
direction only), so it restates the one open statement and does not discharge it. No hypothesis of the bridge is
discharged by this module.

`NoStallOnSegment N β` is not proved at any `β > 0` beyond the anchors' neighbourhoods; neither is `(β, β) ∈
VanishSet N` frequently at `∞`, which is `StrongEnd N` itself (`strongEnd_iff_diag`). The neighbourhoods given by
openness have no quantified size. `LayerSplit.TwoDCharacter N β` stays a cited input. The first-stall statements
locate where an argument must act; they give no information on whether the stall set is empty.
-/

namespace MassGap.MixPlane

open Filter Topology Set MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson
open MassGap.CouplingTower (windowCoupling StrongEnd)

variable {N : ℕ}

/-! ## 1. Joint continuity -/

/-- `(β, β_⊥) ↦ ZC(cA β β_⊥)` is continuous on `ℝ²`, at every extent. No numeral. -/
theorem continuous_ZC_cA₂ (L : Fin 4 → ℕ) :
    Continuous fun p : ℝ × ℝ => MixAnchor.ZC N (MixAnchor.cA p.1 p.2) L := by
  have hcA : ∀ i j : Fin 4, Continuous fun q : (ℝ × ℝ) × (RLink L → SUN.SU N) =>
      MixAnchor.cA q.1.1 q.1.2 i j := by
    intro i j
    unfold MixAnchor.cA
    exact continuous_if_const _ (fun _ => continuous_fst.fst) (fun _ => continuous_fst.snd)
  have hf0 : Continuous fun q : (ℝ × ℝ) × (RLink L → SUN.SU N) =>
      Real.exp (-MixAnchor.actC (MixAnchor.cA q.1.1 q.1.2) L q.2) := by
    refine Real.continuous_exp.comp (Continuous.neg ?_)
    unfold MixAnchor.actC
    exact continuous_finsetSum _ fun r _ => (hcA r.1.1 r.1.2).mul
      (WilsonAction.continuous_wilsonDensity.comp ((MixAnchor.continuous_hol r).comp continuous_snd))
  have hf : Continuous (Function.uncurry fun (p : ℝ × ℝ) (U : RLink L → SUN.SU N) =>
      Real.exp (-MixAnchor.actC (MixAnchor.cA p.1 p.2) L U)) := hf0
  have h := continuous_parametric_integral_of_continuous
    (μ := Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

/-- **Joint continuity**: at a fixed window, `(β, β_⊥) ↦ DA N β β_⊥ w` is continuous on `ℝ²`.
DERIVED: `16 = 2⁴` the copies; `1` the next window. -/
theorem continuous_DA₂ (w : ℕ) : Continuous fun p : ℝ × ℝ => AnisoTorus.DA N p.1 p.2 w := by
  have e : (fun p : ℝ × ℝ => AnisoTorus.DA N p.1 p.2 w) = fun p =>
      16 * Real.log (MixAnchor.ZC N (MixAnchor.cA p.1 p.2) (fun _ => 2 ^ w))
        - Real.log (MixAnchor.ZC N (MixAnchor.cA p.1 p.2) (fun _ => 2 ^ (w + 1))) := by
    funext p; unfold AnisoTorus.DA AnisoTorus.logZA; rw [MixAnchor.ZA_eq, MixAnchor.ZA_eq]
  rw [e]
  exact (continuous_const.mul ((continuous_ZC_cA₂ _).log fun _ => (MixAnchor.ZC_pos N _ _).ne')).sub
    ((continuous_ZC_cA₂ _).log fun _ => (MixAnchor.ZC_pos N _ _).ne')

/-! ## 2. The vanishing set and the stall set -/

/-- **The closed quadrant** `[0, ∞)²`. DERIVED: `0` the lower ends. -/
def Quad : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

theorem isClosed_quad : IsClosed Quad :=
  (isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_const continuous_snd)

/-- **The vanishing set**: the quadrant points at which `DA N β β_⊥ · → 0` along the windows. DERIVED: `0` the
lower ends and the limit. -/
def VanishSet (N : ℕ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ Tendsto (fun w => AnisoTorus.DA N p.1 p.2 w) atTop (𝓝 0)}

/-- **The stall set**: the quadrant minus the vanishing set. No numeral. -/
def StallSet (N : ℕ) : Set (ℝ × ℝ) := Quad \ VanishSet N

/-- **The strict seed set**: some window `w ≥ 1` reads strictly below the seed. Inherited: `1/1000` the seed of
`DoublingSharp`. DERIVED: `1` the least window. -/
def SeedSet (N : ℕ) : Set (ℝ × ℝ) := {p | ∃ w : ℕ, 1 ≤ w ∧ AnisoTorus.DA N p.1 p.2 w < 1 / 1000}

theorem isOpen_seedSet : IsOpen (SeedSet N) := by
  have e : SeedSet N = ⋃ w : ℕ, ⋃ (_ : 1 ≤ w), {p : ℝ × ℝ | AnisoTorus.DA N p.1 p.2 w < 1 / 1000} := by
    ext p; simp [SeedSet]
  rw [e]
  exact isOpen_iUnion fun w => isOpen_iUnion fun _ => isOpen_lt (continuous_DA₂ w) continuous_const

/-- **Membership is a seed window**: in the quadrant, `p ∈ VanishSet N` iff some window `w ≥ 1` has
`DA ≤ 1/1000`. Inherited: `1/1000` the seed. DERIVED: `1` the least window; `0` the lower ends; `1/1000` the
basin of `MixAnchor.tendsto_DA_of_seed`. -/
theorem mem_vanishSet_iff_seed (hN : N ≠ 0) {p : ℝ × ℝ} :
    p ∈ VanishSet N ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ ∃ w : ℕ, 1 ≤ w ∧ AnisoTorus.DA N p.1 p.2 w ≤ 1 / 1000 := by
  constructor
  · rintro ⟨h1, h2, h⟩
    obtain ⟨w, hlt, hw⟩ := ((h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))).and
      (eventually_ge_atTop 1)).exists
    exact ⟨h1, h2, w, hw, hlt.le⟩
  · rintro ⟨h1, h2, w, hw, h⟩
    exact ⟨h1, h2, MixAnchor.tendsto_DA_of_seed hN h1 h2 hw h⟩

/-- **The strict seed form**: in the quadrant, `p ∈ VanishSet N` iff some window `w ≥ 1` has `DA < 1/1000`.
Inherited: `1/1000` the seed. DERIVED: `1` the least window; `0` the lower ends. -/
theorem mem_vanishSet_iff_seed_lt (hN : N ≠ 0) {p : ℝ × ℝ} :
    p ∈ VanishSet N ↔ p ∈ Quad ∧ p ∈ SeedSet N := by
  constructor
  · rintro ⟨h1, h2, h⟩
    obtain ⟨w, hlt, hw⟩ := ((h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 1000 by norm_num))).and
      (eventually_ge_atTop 1)).exists
    exact ⟨⟨h1, h2⟩, w, hw, hlt⟩
  · rintro ⟨⟨h1, h2⟩, w, hw, h⟩
    exact ⟨h1, h2, MixAnchor.tendsto_DA_of_seed hN h1 h2 hw h.le⟩

theorem vanishSet_eq (hN : N ≠ 0) : VanishSet N = SeedSet N ∩ Quad := by
  ext p
  rw [mem_vanishSet_iff_seed_lt hN, mem_inter_iff, and_comm]

/-- **The vanishing set is relatively open in the quadrant**: `VanishSet N = U ∩ Quad`, `U` open. No numeral. -/
theorem exists_open_vanishSet (hN : N ≠ 0) : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ VanishSet N = U ∩ Quad :=
  ⟨SeedSet N, isOpen_seedSet, vanishSet_eq hN⟩

/-- **A point of the vanishing set has a quadrant neighbourhood in it.** No numeral. -/
theorem eventually_mem_vanishSet (hN : N ≠ 0) {p : ℝ × ℝ} (hp : p ∈ VanishSet N) :
    ∀ᶠ q in 𝓝 p, q ∈ Quad → q ∈ VanishSet N := by
  rw [vanishSet_eq hN] at hp ⊢
  filter_upwards [isOpen_seedSet.mem_nhds hp.1] with q hq hQ
  exact ⟨hq, hQ⟩

theorem stallSet_eq (hN : N ≠ 0) : StallSet N = Quad ∩ (SeedSet N)ᶜ := by
  ext p
  simp only [StallSet, Set.mem_sdiff, mem_inter_iff, mem_compl_iff, vanishSet_eq hN]
  tauto

/-- **The stall set is closed** in `ℝ²`, so relatively closed in the quadrant. No numeral. -/
theorem isClosed_stallSet (hN : N ≠ 0) : IsClosed (StallSet N) := by
  rw [stallSet_eq hN]
  exact isClosed_quad.inter isOpen_seedSet.isClosed_compl

theorem mem_stallSet_iff {p : ℝ × ℝ} : p ∈ StallSet N ↔ p ∈ Quad ∧ p ∉ VanishSet N := Iff.rfl

/-! ## 3. The anchors -/

/-- **The diagonal is the window coupling**: `(β, β) ∈ VanishSet N ↔ 0 ≤ β ∧ Vanishes N β`, through `DA_iso`.
DERIVED: `0` the lower end. -/
theorem diag_mem_iff {β : ℝ} : (β, β) ∈ VanishSet N ↔ 0 ≤ β ∧ StrongAnchor.Vanishes N β := by
  have e : (fun w => AnisoTorus.DA N β β w) = windowCoupling N β := funext fun w => AnisoTorus.DA_iso N β w
  simp only [VanishSet, mem_setOf_eq, e, StrongAnchor.Vanishes]
  tauto

/-- **The origin vanishes**, with no input. DERIVED: `0` the ultralocal coupling. -/
theorem zero_mem_vanishSet : ((0 : ℝ), (0 : ℝ)) ∈ VanishSet N :=
  diag_mem_iff.mpr ⟨le_rfl, StrongAnchor.vanishes_zero⟩

/-- **A quadrant ball around the origin vanishes**, with no input; its radius is existential.
DERIVED: `0` the origin. -/
theorem exists_ball_origin (hN : N ≠ 0) :
    ∃ ε > 0, ∀ p ∈ Quad, dist p ((0 : ℝ), (0 : ℝ)) < ε → p ∈ VanishSet N := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp (eventually_mem_vanishSet hN zero_mem_vanishSet)
  exact ⟨ε, hε, fun p hQ hd => h hd hQ⟩

/-- **The axis anchor**: under the cited `TwoDCharacter N β`, `(β, 0) ∈ VanishSet N`, through
`DecoupledSplit`. DERIVED: `0` the decoupled end. -/
theorem axis_mem_vanishSet {β : ℝ} (hβ : 0 ≤ β) (hC : LayerSplit.TwoDCharacter N β) :
    (β, (0 : ℝ)) ∈ VanishSet N :=
  ⟨hβ, le_rfl, DecoupledSplit.decoupled_vanishes_of_twoD hC⟩

/-- **The axis lies in the vanishing set** when the cited 2D character expansion holds at every `β ≥ 0`.
DERIVED: `0` the decoupled end. -/
theorem axis_subset (hC : ∀ β : ℝ, 0 ≤ β → LayerSplit.TwoDCharacter N β) :
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = 0} ⊆ VanishSet N := by
  rintro ⟨β, t⟩ ⟨hβ, rfl⟩
  exact axis_mem_vanishSet hβ (hC β hβ)

/-- **A quadrant neighbourhood of the axis point**, under `TwoDCharacter N β`. DERIVED: `0` the decoupled end. -/
theorem axis_nhds (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (hC : LayerSplit.TwoDCharacter N β) :
    ∀ᶠ q in 𝓝 (β, (0 : ℝ)), q ∈ Quad → q ∈ VanishSet N :=
  eventually_mem_vanishSet hN (axis_mem_vanishSet hβ hC)

/-- **The isotropic anchor in the plane**: `(β, β) ∈ VanishSet N` on `[0, b)`, `b > 0` existential, from
`StrongAnchor.strongAnchor`. DERIVED: `0` the lower end. -/
theorem diag_anchor (hN : N ≠ 0) : ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → (β, β) ∈ VanishSet N := by
  obtain ⟨b, hb, h⟩ := StrongAnchor.strongAnchor hN
  exact ⟨b, hb, fun β h0 hlt => diag_mem_iff.mpr ⟨h0, h β h0 hlt⟩⟩

/-- **A quadrant neighbourhood of each isotropic anchor point.** DERIVED: `0` the lower end. -/
theorem diag_anchor_nhds (hN : N ≠ 0) : ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b →
    ∀ᶠ q in 𝓝 (β, β), q ∈ Quad → q ∈ VanishSet N := by
  obtain ⟨b, hb, h⟩ := diag_anchor hN
  exact ⟨b, hb, fun β h0 hlt => eventually_mem_vanishSet hN (h β h0 hlt)⟩

/-! ## 4. The one statement in the plane -/

/-- **The strong end is the diagonal**: `StrongEnd N ↔` frequently as `β → ∞`, `(β, β) ∈ VanishSet N`.
DERIVED: `0` the lower end. -/
theorem strongEnd_iff_diag : StrongEnd N ↔ ∃ᶠ β in atTop, (β, β) ∈ VanishSet N := by
  constructor
  · intro h
    refine (h.and_eventually (eventually_ge_atTop (0 : ℝ))).mono ?_
    rintro β ⟨hv, h0⟩
    exact diag_mem_iff.mpr ⟨h0, hv⟩
  · intro h
    exact h.mono fun β hβ => (diag_mem_iff.mp hβ).2

/-- **`NoStallOnSegment N β`, the geometric remaining input (not proved)**: the vertical segment
`{(β, t) | 0 ≤ t ≤ β}` from the axis to the diagonal misses the stall set. DERIVED: `0` the axis. -/
def NoStallOnSegment (N : ℕ) (β : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ β → (β, t) ∉ StallSet N

/-- **No stall on the segment reaches the diagonal** (the endpoint `t = β` is on the segment; `TwoDCharacter` is
not read). DERIVED: `0` the lower end. -/
theorem diag_mem_of_noStallOnSegment {β : ℝ} (hβ : 0 ≤ β) (h : NoStallOnSegment N β) :
    (β, β) ∈ VanishSet N := by
  by_contra hv
  exact h β hβ le_rfl ⟨⟨hβ, hβ⟩, hv⟩

/-- **Frequently no stall on the segment gives the strong end.** DERIVED: `0` the lower end. -/
theorem strongEnd_of_noStallOnSegment (h : ∃ᶠ β in atTop, NoStallOnSegment N β) : StrongEnd N := by
  refine strongEnd_iff_diag.mpr ((h.and_eventually (eventually_ge_atTop (0 : ℝ))).mono ?_)
  rintro β ⟨hs, h0⟩
  exact diag_mem_of_noStallOnSegment h0 hs

/-- **First stall along a path**: a continuous path in the quadrant on `[0, a]` that starts in the vanishing set
and meets the stall set has a least stall parameter `t* ∈ (0, a]`, with the path in the vanishing set on
`[0, t*)`. DERIVED: `0` the start. -/
theorem first_stall_of_path (hN : N ≠ 0) {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) {a : ℝ}
    (hQ : ∀ t : ℝ, 0 ≤ t → t ≤ a → γ t ∈ Quad) (h0 : γ 0 ∈ VanishSet N)
    (h : ∃ t : ℝ, 0 ≤ t ∧ t ≤ a ∧ γ t ∈ StallSet N) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ a ∧ γ ts ∈ StallSet N ∧ ∀ t : ℝ, 0 ≤ t → t < ts → γ t ∈ VanishSet N := by
  let S : Set ℝ := Icc 0 a ∩ γ ⁻¹' StallSet N
  have hSc : IsClosed S := isClosed_Icc.inter ((isClosed_stallSet hN).preimage hγ)
  obtain ⟨t₁, ht0, hta, hts⟩ := h
  have hSne : S.Nonempty := ⟨t₁, ⟨ht0, hta⟩, hts⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hpos : 0 < sInf S := by
    refine lt_of_le_of_ne hmem.1.1 fun he => ?_
    have hst : γ (sInf S) ∈ StallSet N := hmem.2
    rw [← he] at hst
    exact hst.2 h0
  refine ⟨sInf S, hpos, hmem.1.2, hmem.2, fun t htn hlt => ?_⟩
  by_contra hv
  have htS : t ∈ S := ⟨⟨htn, (hlt.trans_le hmem.1.2).le⟩, hQ t htn (hlt.trans_le hmem.1.2).le, hv⟩
  exact absurd (csInf_le hSbdd htS) (not_le.mpr hlt)

/-- **First stall on the segment**: under the cited `TwoDCharacter N β`, if the segment above `β` meets the stall
set, there is a least `t* ∈ (0, β]` with `(β, t*)` stalled and `(β, t)` vanishing for `t ∈ [0, t*)`.
DERIVED: `0` the axis. -/
theorem segment_first_stall (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (hC : LayerSplit.TwoDCharacter N β)
    (h : ¬ NoStallOnSegment N β) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ β ∧ (β, ts) ∈ StallSet N ∧
      ∀ t : ℝ, 0 ≤ t → t < ts → (β, t) ∈ VanishSet N := by
  have h' : ∃ t : ℝ, 0 ≤ t ∧ t ≤ β ∧ (β, t) ∈ StallSet N := by
    by_contra hn
    exact h fun t h0 h1 hs => hn ⟨t, h0, h1, hs⟩
  exact first_stall_of_path (γ := fun t => (β, t)) hN (continuous_const.prodMk continuous_id)
    (fun t ht _ => ⟨hβ, ht⟩) (axis_mem_vanishSet hβ hC) h'

/-- **First stall on the diagonal**, with no input: if `(β, β)` is stalled for some `β ≥ 0`, there is a least
`t* ∈ (0, β]` with `(t*, t*)` stalled and `(t, t)` vanishing for `t ∈ [0, t*)`. DERIVED: `0` the origin. -/
theorem diag_first_stall (hN : N ≠ 0) {β : ℝ} (hβ : (β, β) ∈ StallSet N) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ β ∧ (ts, ts) ∈ StallSet N ∧
      ∀ t : ℝ, 0 ≤ t → t < ts → (t, t) ∈ VanishSet N :=
  first_stall_of_path (γ := fun t => (t, t)) hN (continuous_id.prodMk continuous_id)
    (fun _ ht _ => ⟨ht, ht⟩) zero_mem_vanishSet ⟨β, hβ.1.1, le_rfl, hβ⟩

/-- **The diagonal first stall lies beyond the isotropic anchor**: any `b` with `(t, t) ∈ VanishSet N` on `[0, b)`
bounds a diagonal stall from below. DERIVED: `0` the origin. -/
theorem diag_first_stall_ge {b ts : ℝ} (hb : ∀ t : ℝ, 0 ≤ t → t < b → (t, t) ∈ VanishSet N)
    (hts : (ts, ts) ∈ StallSet N) : b ≤ ts := by
  by_contra hlt
  exact hts.2 (hb ts hts.1.1 (not_le.mp hlt))

/-- **The diagonal stall set is the failure of the window read**: for `β ≥ 0`, `(β, β) ∈ StallSet N ↔
¬ Vanishes N β`. DERIVED: `0` the lower end. -/
theorem diag_stall_iff {β : ℝ} (hβ : 0 ≤ β) : (β, β) ∈ StallSet N ↔ ¬ StrongAnchor.Vanishes N β := by
  rw [mem_stallSet_iff, diag_mem_iff]
  exact ⟨fun h hv => h.2 ⟨hβ, hv⟩, fun h => ⟨⟨hβ, hβ⟩, fun hv => h hv.2⟩⟩

end MassGap.MixPlane

#print axioms MassGap.MixPlane.continuous_ZC_cA₂
#print axioms MassGap.MixPlane.continuous_DA₂
#print axioms MassGap.MixPlane.isClosed_quad
#print axioms MassGap.MixPlane.isOpen_seedSet
#print axioms MassGap.MixPlane.mem_vanishSet_iff_seed
#print axioms MassGap.MixPlane.mem_vanishSet_iff_seed_lt
#print axioms MassGap.MixPlane.vanishSet_eq
#print axioms MassGap.MixPlane.exists_open_vanishSet
#print axioms MassGap.MixPlane.eventually_mem_vanishSet
#print axioms MassGap.MixPlane.stallSet_eq
#print axioms MassGap.MixPlane.isClosed_stallSet
#print axioms MassGap.MixPlane.mem_stallSet_iff
#print axioms MassGap.MixPlane.diag_mem_iff
#print axioms MassGap.MixPlane.zero_mem_vanishSet
#print axioms MassGap.MixPlane.exists_ball_origin
#print axioms MassGap.MixPlane.axis_mem_vanishSet
#print axioms MassGap.MixPlane.axis_subset
#print axioms MassGap.MixPlane.axis_nhds
#print axioms MassGap.MixPlane.diag_anchor
#print axioms MassGap.MixPlane.diag_anchor_nhds
#print axioms MassGap.MixPlane.strongEnd_iff_diag
#print axioms MassGap.MixPlane.diag_mem_of_noStallOnSegment
#print axioms MassGap.MixPlane.strongEnd_of_noStallOnSegment
#print axioms MassGap.MixPlane.first_stall_of_path
#print axioms MassGap.MixPlane.segment_first_stall
#print axioms MassGap.MixPlane.diag_first_stall
#print axioms MassGap.MixPlane.diag_first_stall_ge
#print axioms MassGap.MixPlane.diag_stall_iff
