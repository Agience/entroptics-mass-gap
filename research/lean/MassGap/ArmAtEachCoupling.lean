import Mathlib
import MassGap.SubstrateArms
import MassGap.ApertureFamily

/-!
# MassGap.ArmAtEachCoupling — the contact-relative arm with its constant free per coupling

`NonnegArm.LawAbove b` asks for ONE constant `C` serving every coupling above the cut:

    ∃ C ≥ 0, ∀ N β d,  b < β → 1 ≤ circLag d →
      wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / circLag d ^ 4

The per-coupling aperture route needs less. `ApertureFamily.confinement_at_each_coupling_of_substrate`
fixes the coupling before choosing the extent, so the bound on the second moment may depend on the
coupling — and therefore so may `C`. `LawAboveAtCoupling β` is that arm at a single coupling,
uniform in the aperture alone.

The route from it is the tree's own: `ShareEnvelope.circ_moment_le_of_contact_relative` turns a
contact-relative quartic bound into a bound on the circular second moment, summing `k² / k⁴` over the
circle. That is where the exponent `4` is forced — `∑ k² · C / kˢ` converges exactly when `s > 3`.
-/

namespace MassGap.ArmAtEachCoupling

open Filter
open MassGap.EvenAperture

/-- **The contact-relative arm at one coupling**, uniform in the aperture.

`NonnegArm.LawAbove b` is this with one constant for every coupling past `b` at once;
`SubstrateArms.LawAboveAt N b` pins the aperture instead and leaves the coupling free. This pins the
coupling and leaves the aperture free, which is the direction
`ApertureFamily.confinement_at_each_coupling_of_substrate` consumes.

DERIVED: `0` is the lower bound on the constant; `1` is the lag guard, below which the contact value
itself sits; `4` is the quartic exponent, forced by the convergence of `∑ k² / kˢ` at `s > 3`. -/
def LawAboveAtCoupling (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (d : Fin (N + 1)), 1 ≤ MassGap.Moment.circLag d →
    MassGap.wilsonCorrAt N β d
      ≤ C * MassGap.wilsonCorrAt N β 0 / (MassGap.Moment.circLag d : ℝ) ^ 4

#print axioms LawAboveAtCoupling

/-- `NonnegArm.LawAbove b` gives the arm at every coupling past `b`, keeping the same constant.

DERIVED: no numeral appears in the statement; both sides carry their own inside their definitions. -/
theorem lawAboveAtCoupling_of_lawAbove {b β : ℝ} (h : MassGap.NonnegArm.LawAbove b) (hβ : b < β) :
    LawAboveAtCoupling β := by
  obtain ⟨C, hC, hbd⟩ := h
  exact ⟨C, hC, fun N d hd => hbd N β d hβ hd⟩

#print axioms lawAboveAtCoupling_of_lawAbove

/-- `NonnegArm.LawBelow b` gives the arm at every coupling in `[0, b]`, keeping the same constant.
`NonnegArm.lawBelow_holds` supplies that hypothesis, so the arm is proved on the whole of `[0, b]`.

DERIVED: `0` is the lower end of the coupling range. -/
theorem lawAboveAtCoupling_of_lawBelow {b β : ℝ} (h : MassGap.NonnegArm.LawBelow b)
    (h0 : 0 ≤ β) (hb : β ≤ b) : LawAboveAtCoupling β := by
  obtain ⟨C, hC, hbd⟩ := h
  exact ⟨C, hC, fun N d hd => hbd N β d h0 hb hd⟩

#print axioms lawAboveAtCoupling_of_lawBelow

/-- **The arm is proved on `[0, b]`**, for the cut `b` that `NonnegArm.lawBelow_holds` supplies.

`lawBelow_holds` is a theorem, not a hypothesis, so this is too: the contact-relative quartic bound
holds at every coupling from zero up to that cut, with foundational axioms only. Past the cut is what
remains.

DERIVED: `0` is the strict lower bound on the cut and the lower end of the coupling range. -/
theorem lawAboveAtCoupling_holds_below :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, 0 ≤ β → β ≤ b → LawAboveAtCoupling β := by
  obtain ⟨b, hb0, hb⟩ := MassGap.NonnegArm.lawBelow_holds
  exact ⟨b, hb0, fun β h0 hle => lawAboveAtCoupling_of_lawBelow hb h0 hle⟩

#print axioms lawAboveAtCoupling_holds_below

/-- **The second moment is bounded over the apertures, at a coupling where the arm holds.**

`ShareEnvelope.circ_moment_le_of_contact_relative` at `readEven a β`, whose profile is
`wilsonCorrAt a.1 (max β 0)` by definition. The bound is the envelope sum
`2 * ∑' k, k² * quarticWeight 1 C k`, which mentions no aperture — that is what makes it uniform in
the extent.

DERIVED: `2` is the exponent of the second moment and the two sides of the circle each lag is counted
on; `1` is the lag guard passed to the envelope; `0` is the clamp on the coupling. -/
theorem d2Even_bounded_of_arm {β : ℝ} (h : LawAboveAtCoupling (max β 0)) :
    ∃ B : ℝ, ∀ a : EvenAp, d2Even a β ≤ B := by
  obtain ⟨C, hC, hbd⟩ := h
  refine ⟨2 * ∑' k : ℕ, (k : ℝ) ^ 2 * MassGap.ShareEnvelope.quarticWeight 1 C k, fun a => ?_⟩
  show ∑ d, (readEven a β).p d * (MassGap.Moment.circLag d : ℝ) ^ 2 ≤ _
  refine MassGap.ShareEnvelope.circ_moment_le_of_contact_relative (readEven a β) 1 hC
    (fun d hd => ?_)
  exact hbd a.1 d hd

#print axioms d2Even_bounded_of_arm

/-- **`ConfinesAtEachCoupling` from the arm at each coupling.**

The chain: `d2Even_bounded_of_arm` gives the second-moment bound at the coupling, and
`ApertureFamily.confinement_at_each_coupling_of_substrate` turns that into the read above the entropy
floor at an extent chosen for that coupling.

What this asks for is a contact-relative quartic bound at each nonnegative coupling separately, with
the constant free to depend on it. `NonnegArm.lawBelow_holds` proves it on `[0, b]`; past `b` it is
what remains.

DERIVED: `0` is the lower end of the coupling range and the clamp inside `readEven`. -/
theorem confines_at_each_coupling_of_arm
    (h : ∀ β : ℝ, 0 ≤ β → LawAboveAtCoupling β) :
    MassGap.ApertureFamily.ConfinesAtEachCoupling :=
  MassGap.ApertureFamily.confinement_at_each_coupling_of_substrate
    (fun β => d2Even_bounded_of_arm (h (max β 0) (le_max_right β 0)))

#print axioms confines_at_each_coupling_of_arm

/-- **A geometric tail at one coupling gives the arm at that coupling.**

`SubstrateArms.lawAbove_of_geometric_tail` with the coupling fixed first, so the rate `r` may depend
on it — which is what a correlation length varying with the coupling means.
`StrongArm.exists_geom_quartic_bound` supplies an `S` with `(m+1)⁴ · rᵐ ≤ S` at every `m`, and the rest
is dividing by `L⁴`.

⚠ The contact value's nonnegativity comes from `PlaqVariance.corrClay_zero_pos`, not from
`readYMAt`. `readYMAt` is the one declaration in the tree that applies
`wilson_reflection_positive_at`, and routing through it would put that named axiom on everything
downstream. `SubstrateArms.lawAbove_of_geometric_tail`, the aperture-uniform twin of this theorem,
does take it from `readYMAt` and carries the axiom as a result.

DERIVED: `0` is the lower bound on the rate and on the contact value; `1` is the upper bound on the
rate, the lag guard, and the offset in the quartic envelope; `4` is the quartic exponent. -/
theorem lawAboveAtCoupling_of_geometric_tail {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (d : Fin (N + 1)), 1 ≤ MassGap.Moment.circLag d →
      MassGap.wilsonCorrAt N β d
        ≤ MassGap.wilsonCorrAt N β 0 * r ^ (MassGap.Moment.circLag d)) :
    LawAboveAtCoupling β := by
  obtain ⟨S, hS0, hS⟩ := MassGap.StrongArm.exists_geom_quartic_bound hr0 hr1
  refine ⟨S, hS0, fun N d hd => ?_⟩
  set L : ℕ := MassGap.Moment.circLag d with hLdef
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < (L : ℝ) ^ 4 := by positivity
  -- `readYMAt` would give this too, but it is the one declaration applying
  -- `wilson_reflection_positive_at`; `corrClay_zero_pos` proves the contact value positive outright.
  have hρ0 : 0 ≤ MassGap.wilsonCorrAt N β 0 := (MassGap.PlaqVariance.corrClay_zero_pos N β).le
  have hrL : (0 : ℝ) ≤ r ^ L := pow_nonneg hr0 L
  have hmono : ((L : ℝ)) ^ 4 * r ^ L ≤ (((L : ℝ)) + 1) ^ 4 * r ^ L := by
    have h0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hbase : ((L : ℝ)) ^ 4 ≤ (((L : ℝ)) + 1) ^ 4 := by gcongr <;> linarith
    exact mul_le_mul_of_nonneg_right hbase hrL
  have hquart : ((L : ℝ)) ^ 4 * r ^ L ≤ S := le_trans hmono (hS L)
  have hstep : MassGap.wilsonCorrAt N β d * ((L : ℝ)) ^ 4
      ≤ MassGap.wilsonCorrAt N β 0 * S := by
    have h1 := mul_le_mul_of_nonneg_right (hdecay N d hd) (le_of_lt hLpos)
    have h2 : MassGap.wilsonCorrAt N β 0 * r ^ L * ((L : ℝ)) ^ 4
        ≤ MassGap.wilsonCorrAt N β 0 * S := by
      have hmul := mul_le_mul_of_nonneg_left hquart hρ0
      calc MassGap.wilsonCorrAt N β 0 * r ^ L * ((L : ℝ)) ^ 4
          = MassGap.wilsonCorrAt N β 0 * (((L : ℝ)) ^ 4 * r ^ L) := by ring
        _ ≤ MassGap.wilsonCorrAt N β 0 * S := hmul
    exact le_trans h1 h2
  have hinv := mul_le_mul_of_nonneg_right hstep (le_of_lt (inv_pos.mpr hLpos))
  have hleft : MassGap.wilsonCorrAt N β d * ((L : ℝ)) ^ 4 * (((L : ℝ)) ^ 4)⁻¹
      = MassGap.wilsonCorrAt N β d := by
    field_simp
  rw [hleft] at hinv
  simpa only [div_eq_mul_inv, mul_comm] using hinv

#print axioms lawAboveAtCoupling_of_geometric_tail

/-- **Exponential clustering at each coupling gives the read at each coupling.**

The hypothesis is the textbook statement of a mass gap on the lattice: at each nonnegative coupling
the connected plaquette correlation falls geometrically in the circle distance, measured against its
own contact value, uniformly in the aperture. The rate is free to depend on the coupling.

Chained through `lawAboveAtCoupling_of_geometric_tail` and `confines_at_each_coupling_of_arm`, it
gives `ApertureFamily.ConfinesAtEachCoupling`, which
`ClayFromConfinement.clay_four_parts_at_each_coupling` turns into all four parts of the Clay
statement.

DERIVED: `0` is the lower end of the coupling range, the lower bound on the rate and the contact
lag; `1` is the strict upper bound on the rate and the lag guard. -/
theorem confines_at_each_coupling_of_clustering
    (h : ∀ β : ℝ, 0 ≤ β → ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ (N : ℕ) (d : Fin (N + 1)), 1 ≤ MassGap.Moment.circLag d →
        MassGap.wilsonCorrAt N β d
          ≤ MassGap.wilsonCorrAt N β 0 * r ^ (MassGap.Moment.circLag d)) :
    MassGap.ApertureFamily.ConfinesAtEachCoupling := by
  refine confines_at_each_coupling_of_arm (fun β hβ => ?_)
  obtain ⟨r, hr0, hr1, hdec⟩ := h β hβ
  exact lawAboveAtCoupling_of_geometric_tail hr0 hr1 hdec

#print axioms confines_at_each_coupling_of_clustering

/-- **One aperture per coupling is enough — no uniformity in the volume.**

`ApertureFamily.confinement_at_each_coupling_of_substrate` asks for a second-moment bound over EVERY
aperture at a coupling, then uses it at only one: the extent it picks once the window factor is small
enough. The lattice here is a four-dimensional torus with every side the aperture's extent, so
"every aperture" is "every volume", and that uniformity is the thermodynamic limit.

This asks only for the aperture actually used. At each coupling there should be ONE extent at which
the window-weighted circular second moment falls below the floor's slack:

    (2π / (a.1 + 1))² · d2Even a β / 2  <  1 − 3^(−1/4)

`Moment.Read.cos_avg_ge_circ` then clears the floor at that extent directly. The hypothesis is a
statement about one finite torus per coupling, with no limit in it.

It is implied by the second-moment bound over every aperture — that route supplies the extent through
`Moment.aperture_factor_tendsto_zero` — and it is the sharpest form of the quadratic cosine bound, the
one the read itself is closest to.

DERIVED: `2` is the `2π` of a full turn, the exponent of the square and the divisor of the quadratic
cosine bound; `1` is the `+ 1` giving the periodic extent and the leading term of that bound; `3` is
the base of the floor and `4` its exponent's denominator. -/
theorem confines_at_each_coupling_of_moment_at_some_aperture
    (h : ∀ β : ℝ, ∃ a : EvenAp,
      (2 * Real.pi / ((a.1 : ℝ) + 1)) ^ 2 * d2Even a β / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    MassGap.ApertureFamily.ConfinesAtEachCoupling := by
  intro β
  obtain ⟨a, ha⟩ := h β
  refine ⟨a, ?_⟩
  have hd2 : d2Even a β
      = ∑ d, (readEven a β).p d * (MassGap.Moment.circLag d : ℝ) ^ 2 := rfl
  rw [hd2] at ha
  have hge := (readEven a β).cos_avg_ge_circ
  show (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, (readEven a β).p d * Real.cos ((readEven a β).θ d)
  linarith

#print axioms confines_at_each_coupling_of_moment_at_some_aperture

end MassGap.ArmAtEachCoupling
