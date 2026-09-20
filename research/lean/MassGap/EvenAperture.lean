import MassGap.Complete
import MassGap.ActionSplit
import MassGap.WilsonModel

/-!
# MassGap.EvenAperture — the flagship with NO named axiom on the gap side

`Complete.wilson_reflection_positive_at` is the last named axiom the mass-gap chain carries. It is
not carried because reflection positivity is unproved: `Complete.wilson_reflection_positive_at_even`
PROVES the axiom's body — the same conjunction, of the same `wilsonCorrAt` — whenever the extent is
even and at least four and the coupling is nonnegative, with `#print axioms` reporting the
foundational three and nothing else. The axiom survives only because it is stated at EVERY aperture
and EVERY real coupling, and `Complete.readYMAt` is DEFINED from it:

    readYMAt N β := readA (wilsonCorrAt N β) (wilson_reflection_positive_at N β)

Every downstream object — `μYMAt`, `d2At`, `ymModelAt`, `WilsonModel.fullModelOfSubstrate`,
`WilsonModel.existence_and_gap_of_substrate` — mentions that definition, so all of them report the
axiom. There is exactly one place to attack, and it is that `def`.

## What this module does

The flagship does not need the read at every aperture. `Complete.confinement_of_bounded_substrate`
concludes `∀ᶠ N in atTop`, and `WilsonModel.apertureOf` picks a witness from that eventual set. An
eventual set is cofinal, and so is `{N | ∃ m, N + 1 = 2 * m ∧ 2 ≤ m}`, so the two meet: the aperture
may be taken with even extent at least four at no cost. `ActionSplit.exists_even_extent_of_eventually`
does this for parity alone; `exists_even_extent_four_of_eventually` below does it for the bound the
proved reflection positivity actually needs.

`readEven` is then the same read built from the PROVED reflection positivity, and everything above it
is rebuilt on that: `d2Even`, `μEven`, `ymModelEven`, `fullModelEven`, `wilsonEven`, and
`existence_and_gap_of_substrate_even`. None of them mentions the axiom.

## The coupling, stated rather than absorbed

`Apriori.A1 μ κ₀ := ∀ β, μ β < κ₀` quantifies over ALL of `ℝ`, and `LatticeYM.μ : ℝ → ℝ` is total, so
a read defined only at nonnegative coupling cannot populate the `A1` field. The proved reflection
positivity is available only at `0 ≤ β` — and that is not a gap in the argument but the sign of the
coupling: `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` proves the Wilson cross kernel is
positive-semidefinite EXACTLY when `0 ≤ β`.

So `readEven a β` is built at `max β 0`. On `0 ≤ β` it IS `readYMAt a.1 β` (`readEven_eq_readYMAt`);
below zero it is the `β = 0` read (`readEven_eq_at_zero`), and `μEven_eq_at_zero` says so in Lean.
**What the model claims at negative coupling is therefore the `β = 0` claim relabelled, and that is
the whole price of removing the axiom.** It is named here rather than hidden: the two lemmas that
locate the substitution are axiom-free and stated as theorems.

The hypothesis moves the same way. `existence_and_gap_of_substrate` asks `∃ B, ∀ N β, d2At N β ≤ B`;
this asks `∃ B, ∀ (a : EvenAp) β, d2Even a β ≤ B`, which by `d2Even_eq` is the original restricted to
even extents at least four and to nonnegative coupling. `substrate_even_of_substrate` proves the
restricted hypothesis follows from the original, so the axiom-free result is available everywhere the
axiom-carrying one is, and is STRICTLY WEAKER as a hypothesis — nothing in this tree derives the
original from it, because nothing here says anything about `d2At` at an odd extent or a negative
coupling.
-/

namespace MassGap.EvenAperture

open Filter
open scoped Matrix

/-! ## 1. The cofinal choice, at extent at least four

`ActionSplit.exists_even_extent_of_eventually` gives `Even (N + 1)`. `wilson_reflection_positive_at_even`
needs more: `N + 1 = 2 * m` with `2 ≤ m`, because at `m = 1` levels `1` and `m` coincide and the plane
assignment collides (`OddLagSplit.negctl_plane_assignment_collides_at_m_one`). The larger set is still
cofinal, so the strengthening costs nothing. -/

/-- The extents the PROVED reflection positivity is available at: even, and at least four.

DERIVED: `2 * m` is the even extent and `2 ≤ m` is `4 ≤ N + 1`, both read off
`Complete.wilson_reflection_positive_at_even`'s hypotheses. Neither is chosen here. -/
abbrev EvenAp : Type := {N : ℕ // ∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m}

/-- The membership condition is `{N | 4 ≤ N + 1 ∧ Even (N + 1)}`, written in the shape
`wilson_reflection_positive_at_even` consumes. Stated so the two descriptions are known to be the
same set rather than assumed to be. -/
theorem mem_evenAp_iff (N : ℕ) :
    (∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m) ↔ (4 ≤ N + 1 ∧ Even (N + 1)) := by
  constructor
  · rintro ⟨m, hm, hm2⟩
    exact ⟨by omega, ⟨m, by omega⟩⟩
  · rintro ⟨h4, r, hr⟩
    exact ⟨r, by omega, by omega⟩

/-- **The extents with `N + 1` even and at least four are cofinal.** The strengthening of
`ActionSplit.frequently_even_succ` that the proved reflection positivity needs. -/
theorem frequently_even_extent_four :
    ∃ᶠ N : ℕ in atTop, ∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m := by
  rw [Filter.frequently_atTop]
  intro a
  exact ⟨2 * a + 3, by omega, a + 2, by omega, by omega⟩

/-- **An aperture may be taken with even extent at least four, from any eventual set.** Generic in
`P`, as `ActionSplit.exists_even_extent_of_eventually` is. -/
theorem exists_even_extent_four_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ N in atTop, P N) : ∃ N m : ℕ, P N ∧ N + 1 = 2 * m ∧ 2 ≤ m := by
  obtain ⟨N, hPN, m, hm, hm2⟩ :=
    MassGap.ActionSplit.exists_of_eventually_of_frequently hP frequently_even_extent_four
  exact ⟨N, m, hPN, hm, hm2⟩

/-- The same in the bundled form the rest of this file consumes. -/
theorem exists_evenAp_of_eventually {P : ℕ → Prop} (hP : ∀ᶠ N in atTop, P N) :
    ∃ a : EvenAp, P a.1 := by
  obtain ⟨N, hPN, hE⟩ :=
    MassGap.ActionSplit.exists_of_eventually_of_frequently hP frequently_even_extent_four
  exact ⟨⟨N, hE⟩, hPN⟩

/-- **NEGATIVE CONTROL.** Like parity alone, the extent-four condition is only FREQUENTLY true, never
eventually — so `Filter.Eventually.and` cannot produce it and `and_frequently` is load-bearing here
for the same reason `ActionSplit.not_eventually_even_succ` gives for parity. -/
theorem not_eventually_even_extent_four :
    ¬ (∀ᶠ N : ℕ in atTop, ∃ m : ℕ, N + 1 = 2 * m ∧ 2 ≤ m) := by
  rw [Filter.eventually_atTop]
  rintro ⟨a, ha⟩
  obtain ⟨m, hm, _⟩ := ha (2 * a + 2) (by omega)
  omega

/-- **NEGATIVE CONTROL.** The strengthening is not cosmetic: parity alone does NOT give `2 ≤ m`. At
`N = 1` the extent `N + 1 = 2` is even and the half is `1`, which is exactly the case the plane
assignment collides at. So `ActionSplit.exists_even_extent_of_eventually` could not have been used
here as it stands. -/
theorem two_le_half_is_load_bearing :
    Even (1 + 1) ∧ ¬ (∃ m : ℕ, 1 + 1 = 2 * m ∧ 2 ≤ m) := by
  refine ⟨⟨1, rfl⟩, ?_⟩
  rintro ⟨m, hm, hm2⟩
  omega

/-! ## 2. The read, built from the PROVED reflection positivity

This is the single point of attack. `readEven` is `readYMAt` with the axiom replaced by the theorem;
everything below is the existing chain rebuilt on it. -/

/-- **Reading-A of the Wilson ensemble at an even aperture, with NO named axiom.**

Identical in shape to `Complete.readYMAt`, and identical in content at nonnegative coupling
(`readEven_eq_readYMAt`), but its positivity certificate is the THEOREM
`Complete.wilson_reflection_positive_at_even` rather than the axiom
`Complete.wilson_reflection_positive_at`. That is the whole difference, and it is what removes the
named axiom from every declaration below.

DERIVED: the `0` is the lower end of the physical coupling domain — the clamp `max β 0` is what makes
this a total function `ℝ → Moment.Read` so the `A1` field can be populated, and
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` is what puts the boundary there rather than
anywhere else. It sets no scale. -/
noncomputable def readEven (a : EvenAp) (β : ℝ) : Moment.Read a.1 :=
  MassGap.readA (MassGap.wilsonCorrAt a.1 (max β 0))
    (MassGap.wilson_reflection_positive_at_even a.1 a.2.choose a.2.choose_spec.1 a.2.choose_spec.2
      (le_max_right β 0))

/-- Two reads built by `readA` from the same correlation are the same read: the remaining fields are
proofs. Used to compare `readEven` with `readYMAt` without unfolding either certificate. -/
theorem readA_congr {N : ℕ} {ρ ρ' : Fin (N + 1) → ℝ}
    {h : (∀ d, 0 ≤ ρ d) ∧ 0 < ∑ d, ρ d} {h' : (∀ d, 0 ≤ ρ' d) ∧ 0 < ∑ d, ρ' d}
    (e : ρ = ρ') : MassGap.readA ρ h = MassGap.readA ρ' h' := by
  subst e; rfl

/-- **The read IS the axiom-carrying one, at the clamped coupling.** A bridge, so it mentions
`readYMAt` and therefore reports the axiom; that is the point of stating it separately. -/
theorem readEven_eq_readYMAt_max (a : EvenAp) (β : ℝ) :
    readEven a β = MassGap.readYMAt a.1 (max β 0) := readA_congr rfl

/-- **At nonnegative coupling the two reads are the SAME OBJECT.** Nothing is approximated and no
hypothesis is weakened on `0 ≤ β`; the axiom-free chain is about the same Wilson correlation. -/
theorem readEven_eq_readYMAt (a : EvenAp) {β : ℝ} (hβ : 0 ≤ β) :
    readEven a β = MassGap.readYMAt a.1 β :=
  readA_congr (by rw [max_eq_left hβ])

/-- **THE PRICE, NAMED.** At negative coupling `readEven` is the `β = 0` read. The model built below
therefore makes, at every `β < 0`, the claim it makes at `β = 0` — relabelled, not established. This
is axiom-free and is the exact statement of what the restriction costs. -/
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

/-- The moment is the axiom-carrying one at the clamped coupling. -/
theorem d2Even_eq (a : EvenAp) (β : ℝ) : d2Even a β = MassGap.d2At a.1 (max β 0) := by
  show ∑ d, (readEven a β).p d * (Moment.circLag d : ℝ) ^ 2 = _
  rw [readEven_eq_readYMAt_max]
  rfl

/-- The tension is the axiom-carrying one at the clamped coupling. -/
theorem μEven_eq (a : EvenAp) (β : ℝ) : μEven a β = MassGap.μYMAt a.1 (max β 0) := by
  show (readEven a β).tension = _
  rw [readEven_eq_readYMAt_max]
  rfl

/-- **THE PRICE, at the level of the tension.** Axiom-free. -/
theorem μEven_eq_at_zero (a : EvenAp) {β : ℝ} (hβ : β ≤ 0) : μEven a β = μEven a 0 := by
  show (readEven a β).tension = (readEven a 0).tension
  rw [readEven_eq_at_zero a hβ]

/-- **The restricted hypothesis follows from the original.** So every consequence of the axiom-free
chain is available wherever `existence_and_gap_of_substrate`'s hypothesis holds. This bridge mentions
`d2At` and so reports the axiom; the chain it feeds does not. -/
theorem substrate_even_of_substrate (h : ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B) :
    ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun a β => ?_⟩
  rw [d2Even_eq]
  exact hB _ _

/-! ## 4. Confinement, and the aperture chosen from the cofinal set -/

/-- **CONFINEMENT AT AN EVEN APERTURE, FROM ONE SUBSTRATE BOUND — no named axiom.**

The proof is `Complete.confinement_of_substrate_bound`'s, with the cofinal even choice inserted where
that one takes an arbitrary large `N`: the aperture factor tends to zero, so the floor comparison
holds eventually, and `frequently_even_extent_four` supplies an even extent at least four inside that
eventual set. `Moment.Read.tension_lt_floor_of_circ_moment` is generic in the read and carries no
axiom, so nothing here does. -/
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

/-- **A2 at an even aperture.** `Complete.ym_A2`'s proof, replayed. It cannot be cited directly:
`ym_A2 : A2_YM ymModel` has `ymModel` — hence `μYM`, hence the axiom — in its TYPE, so
`#print axioms ym_A2` reports the axiom although the argument never touches the read. The directional
field `R` of `ymModelEven` is `ymModelAt`'s verbatim, so the same Nyquist congruence discharges it. -/
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

/-- **A FULL MODEL FROM ONE OPEN HYPOTHESIS AND NO NAMED AXIOM.** `WilsonModel.fullModelOfSubstrate`
with the even aperture and the axiom-free read. The measure side is unchanged — it was already
foundational-only.

DERIVED: no numeral; every constant belongs to the pieces assembled. -/
noncomputable def fullModelEven (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    MassGap.FullModel where
  gap := ymModelEven (apertureEven h)
  h1 := apertureEven_confines h
  h2 := A2_even (apertureEven h)
  measure := MassGap.WilsonModel.ymFamilyTension

/-- **AN `SU(3)` WILSON REALISATION AT AN EVEN APERTURE.** `WilsonModel.paramsTension` is reused
unchanged: it reads its infrared cutoff off the witness read. That cutoff does contain an aperture --
`kstar = 2π·cW` and `cW` carries `rW ^ (kW + 1)` with `kW` a `Classical.choose`n extent
(`WilsonModel.lean:261`) -- but it is a bare `ℕ` on the MEASURE side, fixed by the witness read and
unrelated to the `EvenAp` this file quantifies over.

DERIVED: no numeral of this declaration's; `3` is `SU(3)`'s rank, carried from `paramsTension`. -/
noncomputable def wilsonEven (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    MassGap.WilsonRealization where
  params := MassGap.WilsonModel.paramsTension
  model := fullModelEven h
  hc := MassGap.WilsonModel.paramsTension_irCutoff.symm

/-! ## 6. The flagship, with no named axiom on the gap side -/

/-- **THE MASS GAP AT AN EVEN APERTURE, FROM THE SUBSTRATE BOUND — no named axiom.**
`Complete.ym_mass_gap_of_substrate`'s conclusion at the even aperture the bound supplies. -/
theorem ym_mass_gap_of_substrate_even
    (h : ∃ B : ℝ, ∀ (a : EvenAp) (β : ℝ), d2Even a β ≤ B) :
    (∀ β, Tendsto (fun τ => ‖∑ k ∈ (ymModelEven (apertureEven h)).s β,
          (ymModelEven (apertureEven h)).P β k
            * ((ymModelEven (apertureEven h)).m β k) ^ τ‖) atTop (nhds 0)) ∧
      (∀ β, (ymModelEven (apertureEven h)).μ β - (ymModelEven (apertureEven h)).κ < 0) ∧
      (∀ d d', (ymModelEven (apertureEven h)).R d = (ymModelEven (apertureEven h)).R d') :=
  MassGap.mass_gap_of_model (ymModelEven (apertureEven h)) (apertureEven_confines h)
    (A2_even (apertureEven h))

/-- **EXISTENCE AND THE GAP, FROM THE SUBSTRATE MOMENT BOUND, WITH NO NAMED AXIOM.**

`WilsonModel.existence_and_gap_of_substrate` with the gap side rebuilt on the PROVED reflection
positivity. The single open input is `∃ B, ∀ a β, d2Even a β ≤ B` — the original substrate bound
restricted to even extents at least four and nonnegative coupling, which
`substrate_even_of_substrate` derives from the original. -/
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

/-- **The gap WITH ITS RATE, and the continuum measure, with no named axiom.** -/
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

/-- The aperture whose extent is four.

DERIVED: `3` is the aperture whose extent `3 + 1` is the smallest even extent with `2 ≤ m`, and `2`
is that half. Both are read off `wilson_reflection_positive_at_even`'s bound, not chosen. -/
def apFour : EvenAp := ⟨3, 2, by norm_num, by norm_num⟩

/-- `EvenAp` is inhabited, so the substrate hypothesis is not a quantification over nothing. -/
theorem evenAp_nonempty : Nonempty EvenAp := ⟨apFour⟩

/-- **NON-VACUITY — the extent bound is met, at the smallest extent that meets it.** Reflection
positivity of the constructed Wilson correlation at aperture `3`, unconditionally at any nonnegative
coupling, with no named axiom. This is `Complete.wilson_reflection_positive_at`'s body at an explicit
aperture, proved. -/
theorem rp_at_extent_four {β : ℝ} (hβ : 0 ≤ β) :
    (∀ d, 0 ≤ MassGap.wilsonCorrAt 3 β d) ∧ 0 < ∑ d, MassGap.wilsonCorrAt 3 β d :=
  MassGap.wilson_reflection_positive_at_even 3 2 (by norm_num) (by norm_num) hβ

/-- **The read at extent four IS the constructed Wilson correlation**, by `rfl`: the four-dimensional
periodic `SU(3)` Gibbs expectation of `WilsonBridge.corrClay`, at the clamped coupling. So the
axiom-free object at this aperture is the physical one, not an abstract stand-in. -/
theorem readEven_apFour_rho (β : ℝ) :
    (readEven apFour β).ρ = fun d => MassGap.WilsonBridge.corrClay (3 + 1) (max β 0) d := rfl

/-- **THE AXIOM-FREE CHAIN FIRES AT AN EXPLICIT EVEN APERTURE.** Gap, non-triviality and `SO(4)` for
`ymModelEven apFour` — extent four — from confinement at that ONE aperture and nothing else. The
aperture is named, so nothing here is chosen from an existential; confinement stays a hypothesis
because its threshold moves with the substrate bound and no value for it is named anywhere. -/
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
