import MassGap.Complete
import MassGap.ActionSplit
import MassGap.WilsonModel

/-!
# MassGap.EvenAperture — the model chain rebuilt on even apertures and clamped coupling

`Complete.readYMAt N β` is defined as `readA (wilsonCorrAt N β) (wilson_reflection_positive_at N β)`,
so it mentions the named axiom `Complete.wilson_reflection_positive_at`, and every object defined
from it — `μYMAt`, `d2At`, `ymModelAt`, `WilsonModel.fullModelOfSubstrate`,
`WilsonModel.existence_and_gap_of_substrate` — reports that axiom.
`Complete.wilson_reflection_positive_at_even` proves the same conjunction about the same
`wilsonCorrAt` whenever `N + 1 = 2 * m` with `2 ≤ m` and `0 ≤ β`, on the foundational axioms only.
This module rebuilds the chain on that theorem.

Contents:
* `EvenAp` — the subtype `{N // ∃ m, N + 1 = 2 * m ∧ 2 ≤ m}`. `mem_evenAp_iff` shows the condition
  is `4 ≤ N + 1 ∧ Even (N + 1)`.
* `frequently_even_extent_four`, `exists_even_extent_four_of_eventually`,
  `exists_evenAp_of_eventually` — that set is frequently true along `atTop`, so it meets any
  eventual set, which is what `Complete.confinement_of_bounded_substrate` produces.
  `not_eventually_even_extent_four` and `two_le_half_is_load_bearing` are the two negative controls:
  the condition is not eventually true, and parity alone does not give `2 ≤ m`.
* `readEven` — `readA (wilsonCorrAt a.1 (max β 0))` with the theorem as its certificate.
  `readA_congr`, `readEven_eq_readYMAt_max`, `readEven_eq_readYMAt` and `readEven_eq_at_zero` relate
  it to `readYMAt`.
* `d2Even`, `μEven`, `d2Even_eq`, `μEven_eq`, `μEven_eq_at_zero`, `substrate_even_of_substrate` —
  the second circle moment and the tension, rebuilt, and the restricted substrate bound derived from
  the original.
* `exists_confining_even_aperture`, `apertureEven`, `apertureEven_confines`, `ymModelEven`,
  `A2_even`, `fullModelEven`, `wilsonEven` — confinement at a chosen even aperture, and the model,
  full model and Wilson realisation built on it.
* `ym_mass_gap_of_substrate_even`, `existence_and_gap_of_substrate_even`,
  `mass_gap_rate_and_continuum_even` — the three conclusions at that aperture.
* `apFour`, `evenAp_nonempty`, `rp_at_extent_four`, `readEven_apFour_rho`,
  `ym_mass_gap_at_extent_four` — the explicit aperture `3`, whose extent `4` is the smallest the
  even-extent theorem reaches.

Scope.
* `Apriori.A1 μ κ₀` quantifies over all of `ℝ` and `LatticeYM.μ : ℝ → ℝ` is total, while
  `wilson_reflection_positive_at_even` requires `0 ≤ β`. `readEven a β` is therefore built at
  `max β 0`. At `0 ≤ β` it equals `readYMAt a.1 β` (`readEven_eq_readYMAt`); at `β ≤ 0` it equals
  `readEven a 0` (`readEven_eq_at_zero`), and `μEven_eq_at_zero` records the same for the tension.
  So at negative coupling the model states its `β = 0` content.
  `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` is an iff placing the boundary at `0`.
* The substrate hypothesis `∃ B, ∀ (a : EvenAp) β, d2Even a β ≤ B` is `d2Even_eq`'s restriction of
  `∃ B, ∀ N β, d2At N β ≤ B` to even extents at least four and clamped coupling.
  `substrate_even_of_substrate` derives the restricted form from the original; the converse is not
  proved here, and nothing in this module constrains `d2At` at an odd extent or a negative coupling.
* `readEven_eq_readYMAt`, `d2Even_eq`, `μEven_eq` and `substrate_even_of_substrate` mention the
  axiom-carrying objects and so report the named axiom; the other declarations do not.
-/

namespace MassGap.EvenAperture

open Filter
open scoped Matrix

/-! ## 1. The cofinal choice, at extent at least four

`ActionSplit.exists_even_extent_of_eventually` gives `Even (N + 1)`. `wilson_reflection_positive_at_even`
needs more: `N + 1 = 2 * m` with `2 ≤ m`, because at `m = 1` levels `1` and `m` coincide and the plane
assignment collides (`OddLagSplit.negctl_plane_assignment_collides_at_m_one`). The larger set is still
cofinal, so the strengthening costs nothing. -/

/-- The subtype of apertures `N` with `N + 1 = 2 * m` for some `m` with `2 ≤ m`: even extent, at
least four. These are the extents `Complete.wilson_reflection_positive_at_even` applies at.

DERIVED: `1` is the `+ 1` relating the aperture `N` to the extent `N + 1`; `2` appears twice, as the
factor making the extent even and as the lower bound on the half `m`. Both are read off
`wilson_reflection_positive_at_even`'s hypotheses; neither is chosen here. -/
abbrev EvenAp : Type := {N : ℕ // ∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m}

/-- `(∃ m, N + 1 = 2 * m ∧ 2 ≤ m) ↔ (4 ≤ N + 1 ∧ Even (N + 1))`: the two descriptions of `EvenAp`'s
membership condition agree. Both directions by `omega` after unpacking.

DERIVED: `1` is the `+ 1` from aperture to extent; `2` is the factor making the extent even and the
lower bound on the half; `4` is the resulting lower bound on the extent, which is `2 * 2`. -/
theorem mem_evenAp_iff (N : ℕ) :
    (∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m) ↔ (4 ≤ N + 1 ∧ Even (N + 1)) := by
  constructor
  · rintro ⟨m, hm, hm2⟩
    exact ⟨by omega, ⟨m, by omega⟩⟩
  · rintro ⟨h4, r, hr⟩
    exact ⟨r, by omega, by omega⟩

/-- `∃ᶠ N in atTop, ∃ m, N + 1 = 2 * m ∧ 2 ≤ m`: the even extents at least four occur arbitrarily
late. Given any `a`, the witness is `N = 2 * a + 3` with `m = a + 2`. The strengthening of
`ActionSplit.frequently_even_succ` by the bound `2 ≤ m`.

DERIVED: `1` is the `+ 1` from aperture to extent; the two `2`s are the even factor and the lower
bound on the half. The witnesses `2 * a + 3` and `a + 2` are in the proof. -/
theorem frequently_even_extent_four :
    ∃ᶠ N : ℕ in atTop, ∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m := by
  rw [Filter.frequently_atTop]
  intro a
  exact ⟨2 * a + 3, by omega, a + 2, by omega, by omega⟩

/-- From `∀ᶠ N in atTop, P N`, an `N` and `m` with `P N`, `N + 1 = 2 * m` and `2 ≤ m`: an eventual
set meets the frequently-true even-extent set. Via
`ActionSplit.exists_of_eventually_of_frequently` and `frequently_even_extent_four`. Generic in `P`.

DERIVED: `1` is the `+ 1` from aperture to extent; the two `2`s are the even factor and the lower
bound on the half. -/
theorem exists_even_extent_four_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ N in atTop, P N) : ∃ N m : ℕ, P N ∧ N + 1 = 2 * m ∧ 2 ≤ m := by
  obtain ⟨N, hPN, m, hm, hm2⟩ :=
    MassGap.ActionSplit.exists_of_eventually_of_frequently hP frequently_even_extent_four
  exact ⟨N, m, hPN, hm, hm2⟩

/-- The same conclusion bundled as `∃ a : EvenAp, P a.1`, which is the form the rest of this module
consumes.

DERIVED: no numeral occurs in the statement; the extent conditions are inside `EvenAp`. -/
theorem exists_evenAp_of_eventually {P : ℕ → Prop} (hP : ∀ᶠ N in atTop, P N) :
    ∃ a : EvenAp, P a.1 := by
  obtain ⟨N, hPN, hE⟩ :=
    MassGap.ActionSplit.exists_of_eventually_of_frequently hP frequently_even_extent_four
  exact ⟨⟨N, hE⟩, hPN⟩

/-- `¬ (∀ᶠ N in atTop, ∃ m, N + 1 = 2 * m ∧ 2 ≤ m)`: the condition is frequently true but not
eventually true, since `2 * a + 2` fails it beyond any `a`. So `Filter.Eventually.and` cannot
produce the conjunction of this with an eventual property, and the frequently-meets-eventually
argument of `exists_even_extent_four_of_eventually` is the one that applies.

DERIVED: `1` is the `+ 1` from aperture to extent; the two `2`s are the even factor and the lower
bound on the half. -/
theorem not_eventually_even_extent_four :
    ¬ (∀ᶠ N : ℕ in atTop, ∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m) := by
  rw [Filter.eventually_atTop]
  rintro ⟨a, ha⟩
  obtain ⟨m, hm, _⟩ := ha (2 * a + 2) (by omega)
  omega

/-- `Even (1 + 1) ∧ ¬ (∃ m, 1 + 1 = 2 * m ∧ 2 ≤ m)`: parity alone does not give `2 ≤ m`. At aperture
`1` the extent is `2`, which is even, but its half is `1`, below the bound.

DERIVED: `1` is the aperture at which the two conditions come apart, and the `+ 1` giving its
extent; `2` is that extent's even factor and the lower bound on the half that fails there. -/
theorem two_le_half_is_load_bearing :
    Even (1 + 1) ∧ ¬ (∃ m : ℕ, 1 + 1 = 2 * m ∧ 2 ≤ m) := by
  refine ⟨⟨1, rfl⟩, ?_⟩
  rintro ⟨m, hm, hm2⟩
  omega

/-! ## 2. The read, built from the PROVED reflection positivity

This is the single point of attack. `readEven` is `readYMAt` with the axiom replaced by the theorem;
everything below is the existing chain rebuilt on it. -/

/-- Reading-A of the Wilson correlation at an even aperture: `readA (wilsonCorrAt a.1 (max β 0))`,
with the positivity certificate supplied by the theorem
`Complete.wilson_reflection_positive_at_even` at `a.2.choose` rather than by the axiom
`Complete.wilson_reflection_positive_at`. The shape is `Complete.readYMAt`'s, and at `0 ≤ β` the two
are the same object (`readEven_eq_readYMAt`).

DERIVED: the `0` is the lower end of the physical coupling domain — the clamp `max β 0` is what makes
this a total function `ℝ → Moment.Read` so the `A1` field can be populated, and
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` is what puts the boundary there rather than
anywhere else. It sets no scale. -/
noncomputable def readEven (a : EvenAp) (β : ℝ) : Moment.Read a.1 :=
  MassGap.readA (MassGap.wilsonCorrAt a.1 (max β 0))
    (MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1 a.2.choose_spec.2
      (le_max_right β 0))

/-- `readA ρ h = readA ρ' h'` whenever `ρ = ρ'`: two reads built from the same correlation agree,
because the remaining fields are proofs. By `subst` and `rfl`. Used to compare `readEven` with
`readYMAt` without unfolding either certificate.

DERIVED: `1` is the `+ 1` in the index type `Fin (N + 1)`, the number of lags; `0` is the lower
bound in the nonnegativity clause and the strict lower bound on the total mass, both belonging to
`readA`'s certificate. -/
theorem readA_congr {N : ℕ} {ρ ρ' : Fin (N + 1) → ℝ}
    {h : (∀ d, 0 ≤ ρ d) ∧ 0 < ∑ d, ρ d} {h' : (∀ d, 0 ≤ ρ' d) ∧ 0 < ∑ d, ρ' d}
    (e : ρ = ρ') : MassGap.readA ρ h = MassGap.readA ρ' h' := by
  subst e; rfl

/-- `readEven a β = readYMAt a.1 (max β 0)`, by `readA_congr rfl`. A bridge lemma: it mentions
`readYMAt` and therefore reports the named axiom, which is why it is stated separately from the
chain.

DERIVED: the one numeral is `0`, the clamp point in `max β 0`. -/
theorem readEven_eq_readYMAt_max (a : EvenAp) (β : ℝ) :
    readEven a β = MassGap.readYMAt a.1 (max β 0) := readA_congr rfl

/-- `readEven a β = readYMAt a.1 β` whenever `0 ≤ β`: on the nonnegative coupling range the clamp is
inert, so the two reads are the same object and the same Wilson correlation.

DERIVED: the one numeral is `0`, the lower bound on `β` at which `max β 0` reduces to `β`. -/
theorem readEven_eq_readYMAt (a : EvenAp) {β : ℝ} (hβ : 0 ≤ β) :
    readEven a β = MassGap.readYMAt a.1 β :=
  readA_congr (by rw [max_eq_left hβ])

/-- `readEven a β = readEven a 0` whenever `β ≤ 0`: below zero the clamp collapses the read to the
one at zero coupling, so every statement the model makes at a negative `β` is its statement at
`β = 0`.

DERIVED: the one numeral is `0`, the clamp point, appearing as the upper bound on `β` and as the
coupling the read collapses to. -/
theorem readEven_eq_at_zero (a : EvenAp) {β : ℝ} (hβ : β ≤ 0) :
    readEven a β = readEven a 0 :=
  readA_congr (by rw [max_eq_right hβ, max_self])

/-! ## 3. The substrate moment and the tension, rebuilt -/

/-- The substrate's second moment about the CIRCLE distance at an even aperture — `Complete.d2At`
with `readEven` in place of `readYMAt`.

DERIVED: the exponent `2` is the definition of a SECOND moment and `Moment.circLag` is the separation
on the circle, both exactly as in `Complete.d2At`; nothing new is introduced. -/
noncomputable def d2Even (a : EvenAp) (β : ℝ) : ℝ :=
  ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2

/-- The centre-vortex tension at an even aperture — `Complete.μYMAt` with `readEven` in place of
`readYMAt`.

DERIVED: no numeral; `tension` is `-log ⟨cos θ⟩_p`, defined in `Moment`. -/
noncomputable def μEven (a : EvenAp) (β : ℝ) : ℝ := (readEven a β).tension

/-- `d2Even a β = d2At a.1 (max β 0)`, by rewriting with `readEven_eq_readYMAt_max`. A bridge
lemma; it mentions `d2At` and so reports the named axiom.

DERIVED: the one numeral is `0`, the clamp point in `max β 0`. -/
theorem d2Even_eq (a : EvenAp) (β : ℝ) : d2Even a β = MassGap.d2At a.1 (max β 0) := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [readEven_eq_readYMAt_max]
  rfl

/-- `μEven a β = μYMAt a.1 (max β 0)`, by rewriting with `readEven_eq_readYMAt_max`. A bridge
lemma; it mentions `μYMAt` and so reports the named axiom.

DERIVED: the one numeral is `0`, the clamp point in `max β 0`. -/
theorem μEven_eq (a : EvenAp) (β : ℝ) : μEven a β = MassGap.μYMAt a.1 (max β 0) := by
  show (readEven a β).tension = _
  rw [readEven_eq_readYMAt_max]
  rfl

/-- `μEven a β = μEven a 0` whenever `β ≤ 0`: `readEven_eq_at_zero` at the level of the tension.

DERIVED: the one numeral is `0`, the upper bound on `β` and the coupling the tension collapses
to. -/
theorem μEven_eq_at_zero (a : EvenAp) {β : ℝ} (hβ : β ≤ 0) : μEven a β = μEven a 0 := by
  show (readEven a β).tension = (readEven a 0).tension
  rw [readEven_eq_at_zero a hβ]

/-- From `∃ B, ∀ N β, d2At N β ≤ B`, the restricted bound `∃ B, ∀ (a : EvenAp) β, d2Even a β ≤ B`,
with the same `B`. Via `d2Even_eq`.

Scope: the implication runs one way. Nothing here derives the unrestricted bound from the restricted
one. This lemma mentions `d2At` and so reports the named axiom.

DERIVED: no numeral occurs in the statement. -/
theorem substrate_even_of_substrate (h : ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B) :
    ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun a β => ?_⟩
  rw [d2Even_eq]
  exact hB _ _

/-! ## 4. Confinement, and the aperture chosen from the cofinal set -/

/-- From `∃ B, ∀ (a : EvenAp) β, d2Even a β ≤ B`, an even aperture `a` with `μEven a β < κ₀YM` at
every `β`. `Moment.aperture_factor_tendsto_zero` makes the floor comparison eventually true along
`atTop`, `exists_evenAp_of_eventually` selects an even extent at least four inside that eventual
set, and `Moment.Read.tension_lt_floor_of_circ_moment` converts the moment bound into the tension
bound. The last lemma is generic in the read, so no named axiom enters.

DERIVED: no numeral occurs in the statement; `κ₀YM` is a named constant. The `2`, `1`, `3` and `4`
of the aperture factor and the floor appear in the proof. -/
theorem exists_confining_even_aperture
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    ∃ a : EvenAp, ∀ β : ℝ, μEven a β < MassGap.κ₀YM := by
  obtain ⟨B, hB⟩ := h
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  obtain ⟨a, ha⟩ := exists_evenAp_of_eventually hev
  exact ⟨a, fun β => (readEven a β).tension_lt_floor_of_circ_moment (hB a β) ha⟩

/-- An even aperture at which confinement holds, obtained from the substrate bound. No value is
named — as in `WilsonModel.apertureOf`, the threshold moves with the existentially supplied `B`.

DERIVED: no numeral; the aperture is `Classical.choose`n from the bound's own cofinal set. -/
noncomputable def apertureEven (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) : EvenAp :=
  (exists_confining_even_aperture h).choose

theorem apertureEven_confines (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    ∀ β : ℝ, μEven (apertureEven h) β < MassGap.κ₀YM :=
  (exists_confining_even_aperture h).choose_spec

/-! ## 5. The model, the full model, and the realisation -/

/-- The lattice Yang–Mills witness at an even aperture — `Complete.ymModelAt` with `μEven` in place
of `μYMAt`. Every other field is `ymModelAt`'s, verbatim.

DERIVED: as in `Complete.ymModelAt`, the `1` is the single mode's weight, forced by normalisation;
nothing else here carries a numeral. -/
noncomputable def ymModelEven (a : EvenAp) : MassGap.LatticeYM where
  Idx := Unit
  Dir := MassGap.DYM
  s := fun _ => (Finset.univ : Finset Unit)
  P := fun _ _ => 1
  m := fun β _ => ((Real.exp (-(MassGap.κ₀YM - μEven a β)) : ℝ) : ℂ)
  μ := μEven a
  R := fun d => MassGap.freadYM ((MassGap.Fym d)ᵀ * MassGap.Fym d).charpoly
  κ₀ := MassGap.κ₀YM
  κ := MassGap.κ₀YM
  hfloor := le_refl _
  hread := by
    intro β _ _
    have h : ‖((Real.exp (-(MassGap.κ₀YM - μEven a β)) : ℝ) : ℂ)‖
        = Real.exp (-(MassGap.κ₀YM - μEven a β)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq h

/-- `A2_YM (ymModelEven a)`: the directional read of `ymModelEven` takes the same value in every
direction. `Complete.ym_A2`'s argument replayed — `A2_continuum_of_congruence` against
`continuumRotationCongruence_of_gram`, with the two side goals discharged from `Otr_iso`.

Scope: `ym_A2` cannot be cited directly because its type mentions `ymModel`, hence `μYM`, hence the
named axiom, although its argument never reads the correlation. The `R` field of `ymModelEven` is
`ymModelAt`'s verbatim, so the same congruence applies.

DERIVED: no numeral occurs in the statement. -/
theorem A2_even (a : EvenAp) : MassGap.A2_YM (ymModelEven a) := by
  show MassGap.A2 (fun d => MassGap.freadYM ((MassGap.Fym d)ᵀ * MassGap.Fym d).charpoly)
  refine MassGap.A2_continuum_of_congruence MassGap.freadYM
    (fun d => (MassGap.Fym d)ᵀ * MassGap.Fym d)
    (MassGap.continuumRotationCongruence_of_gram MassGap.Fym
      (fun d d' => (MassGap.Otr d)ᵀ * MassGap.Otr d') ?_ ?_)
  · intro d d'
    exact MassGap.orthogonal_mul
      (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp (MassGap.Otr_iso d))
      (MassGap.Otr_iso d')
  · intro d d'
    show MassGap.Fbase * MassGap.Otr d'
        = MassGap.Fbase * MassGap.Otr d * ((MassGap.Otr d)ᵀ * MassGap.Otr d')
    rw [← Matrix.mul_assoc, Matrix.mul_assoc MassGap.Fbase (MassGap.Otr d) ((MassGap.Otr d)ᵀ),
      mul_eq_one_comm.mp (MassGap.Otr_iso d), Matrix.mul_one]

/-- A `FullModel` from the restricted substrate bound: `gap := ymModelEven (apertureEven h)`, the
two hypotheses from `apertureEven_confines` and `A2_even`, and the measure side
`WilsonModel.ymFamilyTension` unchanged. `WilsonModel.fullModelOfSubstrate` with the even aperture
in place of the arbitrary one.

DERIVED: no numeral; every constant belongs to the pieces assembled. -/
noncomputable def fullModelEven (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    MassGap.FullModel where
  gap := ymModelEven (apertureEven h)
  h1 := apertureEven_confines h
  h2 := A2_even (apertureEven h)
  measure := MassGap.WilsonModel.ymFamilyTension

/-- A `WilsonRealization` at an even aperture: `params := WilsonModel.paramsTension`,
`model := fullModelEven h`, and `hc` from `paramsTension_irCutoff`.

Scope: `paramsTension` is reused unchanged and reads its infrared cutoff off its own witness read.
That cutoff contains an extent — `kstar = 2π * cW` with `cW` carrying `rW ^ (kW + 1)` for a
`Classical.choose`n `kW` — but it is a bare `ℕ` on the measure side, fixed by that witness read and
unrelated to the `EvenAp` this module quantifies over.

DERIVED: no numeral occurs in the statement; the gauge group's degree and the cutoff's constants are
inside `paramsTension`. -/
noncomputable def wilsonEven (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelEven h
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

/-! ## 6. The flagship, with no named axiom on the gap side -/

/-- The three conclusions of `mass_gap_of_model` at `ymModelEven (apertureEven h)`, from the
restricted substrate bound: the mode expansion's norm tends to `0` at every coupling,
`μ β - κ < 0` at every coupling, and the directional read is direction-independent. The two
hypotheses are `apertureEven_confines` and `A2_even`.

DERIVED: the one numeral is `0`, the limit point in `nhds 0` and the strict upper bound in
`μ β - κ < 0`. -/
theorem ym_mass_gap_of_substrate_even
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    (∀ β, Tendsto (fun τ => ‖∑ k ∈ (ymModelEven (apertureEven h)).s β,
          (ymModelEven (apertureEven h)).P β k
            * ((ymModelEven (apertureEven h)).m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (ymModelEven (apertureEven h)).μ β - (ymModelEven (apertureEven h)).κ < 0) ∧
      (∀ d d', (ymModelEven (apertureEven h)).R d = (ymModelEven (apertureEven h)).R d') :=
  MassGap.mass_gap_of_model (ymModelEven (apertureEven h)) (apertureEven_confines h)
    (A2_even (apertureEven h))

/-- `existence_and_gap_of_wilson` at `wilsonEven h`: the three gap-side conclusions together with
the measure-side conclusion — a subsequence along which every `Q j` converges to a limit `q j`,
bounded by `⌈c⌉₊ * B`, nonnegative, and invariant under both group actions.
`WilsonModel.existence_and_gap_of_substrate` with the gap side rebuilt on the even-extent theorem.

Scope: the single hypothesis is `∃ B, ∀ (a : EvenAp) β, d2Even a β ≤ B`, which
`substrate_even_of_substrate` derives from the unrestricted substrate bound.

DERIVED: the one numeral is `0`, the limit point in `nhds 0`, the strict upper bound in
`μ β - κ < 0`, and the lower bound on each `q j`. -/
theorem existence_and_gap_of_substrate_even
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ (wilsonEven h).model.gap.s β,
          (wilsonEven h).model.gap.P β k
            * ((wilsonEven h).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, (wilsonEven h).model.gap.μ β - (wilsonEven h).model.gap.κ < 0) ∧
        (∀ d d', (wilsonEven h).model.gap.R d = (wilsonEven h).model.gap.R d')) ∧
      (∃ (q : (wilsonEven h).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (wilsonEven h).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(wilsonEven h).model.measure.c⌉₊ : ℝ)
                * (wilsonEven h).model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((wilsonEven h).model.measure.actE g j) = q j) ∧
        (∀ σ j, q ((wilsonEven h).model.measure.actP σ j) = q j)) :=
  MassGap.existence_and_gap_of_wilson (wilsonEven h)

/-- `mass_gap_rate_and_continuum` at `fullModelEven h` and a coupling `β`: strict positivity of
`κ₀ - μ β`, the geometric bound on the mode expansion at that coupling, and the measure-side
subsequence with its four properties.

DERIVED: the one numeral is `0`, the strict lower bound on `κ₀ - μ β`, the limit point in `nhds 0`,
and the lower bound on each `q j`. -/
theorem mass_gap_rate_and_continuum_even
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) (β : ℝ) :
    (0 < (fullModelEven h).gap.κ₀ - (fullModelEven h).gap.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ (fullModelEven h).gap.s β,
          (fullModelEven h).gap.P β k * ((fullModelEven h).gap.m β k) ^ τ‖
        ≤ (∑ k ∈ (fullModelEven h).gap.s β, ‖(fullModelEven h).gap.P β k‖)
            * Real.exp (-((fullModelEven h).gap.κ₀ - (fullModelEven h).gap.μ β)) ^ τ) ∧
      (∃ (q : (fullModelEven h).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (fullModelEven h).measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(fullModelEven h).measure.c⌉₊ : ℝ) * (fullModelEven h).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((fullModelEven h).measure.actE g j) = q j) ∧
        (∀ σ j, q ((fullModelEven h).measure.actP σ j) = q j)) :=
  MassGap.mass_gap_rate_and_continuum (fullModelEven h) β

/-! ## 7. NON-VACUITY — an explicit even aperture at extent four

A bound no extent satisfies would make everything above an empty quantification, and an aperture
chosen from a cofinal set names no value. Extent four is the smallest extent the proved reflection
positivity reaches, and the whole even chain is available there explicitly, in the style of
`OddLagSplit.corrClay_reflection_positive_at_extent_four`. -/

/-- The explicit aperture `3`, with half `2`, whose extent `3 + 1 = 4` is the smallest even extent
satisfying `2 ≤ m`.

DERIVED: `3` is the aperture whose extent `3 + 1` is the smallest even extent with `2 ≤ m`, and `2`
is that half. Both are read off `wilson_reflection_positive_at_even`'s bound, not chosen. -/
def apFour : EvenAp := ⟨3, 2, by norm_num, by norm_num⟩

/-- `Nonempty EvenAp`, witnessed by `apFour`: the quantifications over `EvenAp` above range over a
nonempty type.

DERIVED: no numeral occurs in the statement. -/
theorem evenAp_nonempty : Nonempty EvenAp := ⟨apFour⟩

/-- `(∀ d, 0 ≤ wilsonCorrAt 3 β d) ∧ 0 < ∑ d, wilsonCorrAt 3 β d` for every `0 ≤ β`:
`wilson_reflection_positive_at_even` instantiated at aperture `3` and half `2`. This is the body of
`Complete.wilson_reflection_positive_at` at one explicit aperture.

DERIVED: `3` is the aperture, whose extent `3 + 1 = 4` is the smallest the even-extent theorem
reaches; `0` is the lower bound on the coupling, on each correlation value, and the strict lower
bound on the total. -/
theorem rp_at_extent_four {β : ℝ} (hβ : 0 ≤ β) :
    (∀ d, 0 ≤ MassGap.wilsonCorrAt 3 β d) ∧ 0 < ∑ d, MassGap.wilsonCorrAt 3 β d :=
  MassGap.wilson_reflection_positive_at_even 3 2 (by norm_num) (by norm_num) hβ

/-- `(readEven apFour β).ρ = fun d => WilsonBridge.corrClay (3 + 1) (max β 0) d`, by `rfl`: at
aperture `3` the read's correlation is the constructed Wilson quantity at the clamped coupling, not
an abstract stand-in.

DERIVED: `3` is the aperture and `1` the `+ 1` giving its extent `4`, which is `corrClay`'s own
extent argument; `0` is the clamp point in `max β 0`. -/
theorem readEven_apFour_rho (β : ℝ) :
    (readEven apFour β).ρ = fun d => MassGap.WilsonBridge.corrClay (3 + 1) (max β 0) d := rfl

/-- The three conclusions of `mass_gap_of_model` at `ymModelEven apFour`, from the hypothesis
`hconf : ∀ β, μEven apFour β < κ₀YM` and `A2_even apFour`. The aperture is the named `apFour`, so
nothing here is chosen from an existential.

Scope: `hconf` is a hypothesis. Its threshold moves with the substrate bound `B`, and no value for
either is named in this module.

DERIVED: the one numeral is `0`, the limit point in `nhds 0` and the strict upper bound in
`μ β - κ < 0`. -/
theorem ym_mass_gap_at_extent_four (hconf : ∀ β, μEven apFour β < MassGap.κ₀YM) :
    (∀ β, Tendsto (fun τ => ‖∑ k ∈ (ymModelEven apFour).s β,
          (ymModelEven apFour).P β k * ((ymModelEven apFour).m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (ymModelEven apFour).μ β - (ymModelEven apFour).κ < 0) ∧
      (∀ d d', (ymModelEven apFour).R d = (ymModelEven apFour).R d') :=
  MassGap.mass_gap_of_model (ymModelEven apFour) hconf (A2_even apFour)

/-! ## 8. Footprints

The first block is the EXISTING chain, so the entry point of the axiom is visible rather than
asserted. The second is this module's. -/

section AuditExisting
#print axioms MassGap.wilsonCorrAt
#print axioms MassGap.wilson_reflection_positive_at_even
#print axioms MassGap.readYMAt
#print axioms MassGap.μYMAt
#print axioms MassGap.d2At
#print axioms MassGap.ymModelAt
#print axioms MassGap.ym_A2
#print axioms MassGap.confinement_of_bounded_substrate
#print axioms MassGap.ym_mass_gap_of_substrate
#print axioms MassGap.WilsonModel.apertureOf
#print axioms MassGap.WilsonModel.ymFamilyTension
#print axioms MassGap.WilsonModel.paramsTension
#print axioms MassGap.WilsonModel.fullModelOfSubstrate
#print axioms MassGap.WilsonModel.existence_and_gap_of_substrate
end AuditExisting

section AuditEven
#print axioms frequently_even_extent_four
#print axioms exists_even_extent_four_of_eventually
#print axioms not_eventually_even_extent_four
#print axioms mem_evenAp_iff
#print axioms two_le_half_is_load_bearing
#print axioms evenAp_nonempty
#print axioms readEven
#print axioms readEven_eq_at_zero
#print axioms d2Even
#print axioms μEven
#print axioms μEven_eq_at_zero
#print axioms exists_confining_even_aperture
#print axioms apertureEven
#print axioms ymModelEven
#print axioms A2_even
#print axioms fullModelEven
#print axioms wilsonEven
#print axioms ym_mass_gap_of_substrate_even
#print axioms existence_and_gap_of_substrate_even
#print axioms mass_gap_rate_and_continuum_even
#print axioms apFour
#print axioms rp_at_extent_four
#print axioms readEven_apFour_rho
#print axioms ym_mass_gap_at_extent_four
end AuditEven

section AuditBridges
-- These MENTION the axiom-carrying objects by design, so they report the axiom. They are the
-- comparison statements, not part of the axiom-free chain.
#print axioms readEven_eq_readYMAt
#print axioms d2Even_eq
#print axioms μEven_eq
#print axioms substrate_even_of_substrate
end AuditBridges

end MassGap.EvenAperture
