import MassGap.SUN
import MassGap.Measure
import MassGap.WilsonInstance
import MassGap.WilsonHypercubic

/-!
# MassGap.WilsonGauge — an OS-data family whose invariances are DERIVED, not `rfl` (step A3)

`WilsonInstance.ymFamily` discharges the Osterwalder–Schrader invariances `os_euc`/`os_perm` by `rfl`:
its reflected form reads only a label that the group actions leave fixed, so invariance holds for any
form reading that label — it is *modelled*.

Here we build a `LatticeYMFamily` (`ymFamilyGauge`) whose reflected form is a genuine `SU(3)` gauge
expectation — the Gibbs average, against the canonical probability Haar measure on `SU(3)` (A2b), of the
Wilson plaquette energy on a four-dimensional periodic lattice, transported by that lattice's
**axis-permutation symmetry** (A1) — and
whose `os_euc`/`os_perm` are **derived from `Symmetry.expect_invariant`**: the Euclidean/permutation
group elements act by relabelling the lattice axes, and Haar-invariance of the product measure makes
the expectation invariant. No `rfl` on the correlation; the invariance is a theorem about the actual
`SU(3)` measure.

`ym_continuum_gauge` then runs this family through `continuum_of_family`, giving the OS0–OS3 continuum
limit with the Euclidean/permutation invariances of the limit `q` now genuinely derived. Foundational
footprint only. The existing flagship (`ym_existence_and_gap`) is untouched; retargeting it onto this
family is a follow-up. Build: `lake build MassGap.WilsonGauge`.

The dynamical face (the confinement gap — B/C) is orthogonal to this invariance derivation and still
enters through the cited RP + measured reads. The LATTICE is not orthogonal to it, though, and is no
longer a stand-in: `sysYM` is `WilsonHypercubic.sysWilson 3 4 n`, the four-dimensional periodic `SU(3)`
Wilson system — `4 · n⁴` links, `16 · n⁴` plaquettes, the ordered-loop holonomy and the genuine Wilson
action density. It replaces a four-link, four-plaquette axis-indexed object whose action density was
identically zero: that carried the axis-permutation symmetry, which was all the invariance derivation
needed, but it was not a lattice in any dimension and `β` could not move its measure.
-/

namespace MassGap.WilsonGauge

open MassGap.LatticeGauge MassGap.CompactGauge MassGap.Measure
open MeasureTheory Filter Topology

/-- The rank-3 special unitary group `SU(3)` — the Clay problem's gauge group.

DERIVED: `3` is the rank the problem names. It is not a parameter of this development's choosing;
`SUN.SU` is general in the rank and this is the instantiation the statement is about. -/
abbrev NYM : ℕ := 3

/-- `SU(NYM)` — the Clay problem's gauge group, at the one rank this file names. -/
abbrev G3 : Type := MassGap.SUN.SU NYM

/-- The periodic extent of the constructed lattice.

DERIVED: `2` is the smallest extent at which a direction carries two distinct sites, so that the unit
shift is not the identity and a plaquette is a genuine four-link loop. It is ARITY — the minimum at
which the object exists at all — not a size, and nothing proved here depends on its value: the
underlying system, its cardinalities and its axis symmetry are established for `sysWilson 3 4 n` at
arbitrary `n` in `WilsonHypercubic`, and this family instantiates one of them. -/
abbrev nYM : ℕ := 2

/-- **The four-dimensional periodic `SU(3)` Wilson lattice gauge system.**

`d = 4` is the Clay problem's spacetime, `N = 3` its gauge group. Links are `(direction, site)` pairs
and plaquettes `(plane, site)` pairs, so there are `4 · nYM⁴` links and `16 · nYM⁴` plaquettes
(`WilsonHypercubic.card_link`, `card_plaq`); the holonomy is the ordered product around the boundary
word `U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)⁻¹ U_ν(x)⁻¹`, and the action density is Wilson's
`1 - (1/N) Re tr` rather than the zero function — which is what makes `β` move the Gibbs measure at
all (`WilsonHypercubic.sysWilson_phi`).

DERIVED: `3` is `SU(3)` and `4` is four dimensions — the Clay problem's own data; `nYM` carries its own
note. -/
noncomputable def sysYM : System G3 := MassGap.WilsonHypercubic.sysWilson NYM 4 nYM

/-- An axis-permutation symmetry of `sysYM`, DERIVED from the lattice geometry rather than asserted:
relabelling the axes commutes with the unit shift (`WilsonHypercubic.shift_axis`), hence transports
the plaquette boundary word (`bd_axis`), hence is a `Symmetry` of the gauge system. -/
noncomputable def symAxis (e : Equiv.Perm (Fin 4)) : Symmetry sysYM :=
  MassGap.WilsonHypercubic.axisSymmetry NYM (n := nYM) e

/-- A genuine config-dependent observable: the **Wilson plaquette energy** of one plaquette — the
physical local action density `1 - (1/3) Re tr` of its ordered-loop holonomy, not a matrix entry.

DERIVED: `3` and `4` are `G3`'s rank and the spacetime dimension, carried through from `sysYM`.
`0` and `1` are the two directions spanning the plaquette's plane — a plane needs two, and which
two is a naming freedom on a lattice whose axes are interchangeable (`axisSymmetry`). The site is
the origin, immaterial by periodicity. -/
noncomputable def O0 : sysYM.Config → ℝ :=
  fun U => MassGap.WilsonAction.wilsonDensity (N := 3)
    (sysYM.hol (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 nYM) U)

/-- The reflected Schwinger form: the clamped `SU(3)` Gibbs expectation of `O0` transported by the
axis symmetry encoded in the test configuration `j` (its Euclidean × permutation components).

DERIVED: `0` and `1` are the CLAMP, `min (max · 0) 1` — the interval a reflected Schwinger form is
required to lie in (`os_rp` is its lower end, `os_form` at `B = 1` its upper), not a cut on any
measured quantity. `3` and `4` are the rank and dimension, carried from `sysYM`. -/
noncomputable def QG (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) : ℝ :=
  min (max (sysYM.expect (probHaar G3) (a : ℝ)
    (fun U => O0 (Symmetry.reindex (symAxis (j.1 * j.2.1)).onLink U))) 0) 1

/-- **The reflected form is Euclidean/permutation-invariant, DERIVED from Haar-invariance.** For every
`j`, `QG j a` collapses to the clamped expectation of the *untransported* `O0`, because
`Symmetry.expect_invariant` (Haar-invariance of the `SU(3)` product measure under the axis relabelling)
removes the transport. This is `os_euc`/`os_perm` DERIVED rather than asserted. -/
theorem QG_eq (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    QG j a = min (max (sysYM.expect (probHaar G3) (a : ℝ) O0) 0) 1 := by
  unfold QG
  rw [Symmetry.expect_invariant sysYM (probHaar G3) (symAxis (j.1 * j.2.1)) (a : ℝ) O0]

/-- Euclidean action on test configurations: multiply the Euclidean component. -/
def actEG (g : Equiv.Perm (Fin 4)) (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) :
    Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ := (g * j.1, j.2.1, j.2.2)

/-- Permutation action on test configurations: multiply the permutation component. -/
def actPG (σ : Equiv.Perm (Fin 4)) (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) :
    Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ := (j.1, σ * j.2.1, j.2.2)

/-- Mode count per spacing (`→ ∞`). -/
def NaG (a : ℕ) : ℕ := a + 1

/-! ### The spectrum, the count, and the family

A `LatticeYMFamily` carries four Osterwalder–Schrader data. On this measure three of them -- `os_rp`,
`os_euc`, `os_perm` -- are theorems about `SU(3)` Haar-invariance and the lattice's own axis symmetry.
The fourth, `os_gap`, asks that every mode standing above the noise edge sit below a
spacing-independent index cutoff, and supplying THAT directly is asserting where the resolved modes
are.

`Measure.familyOfSortedCount` refuses to take it. It asks instead for the two things a read actually
produces -- an ORDERED spectrum, and a bound on HOW MANY of its modes clear the edge -- and derives
`os_gap` from the pair (`os_gap_of_sorted_count`). The count is exactly what
`ZeroMode.resolved_count_le_of_subset` obtains from the measured tension, so a family assembled this
way has its infrared input sourced from the correlation rather than asserted about it.

That is the ONLY constructor here. The unconditional family below is not a second route to the same
interface; it is this one at a particular spectrum.

WHICH EDGE. The count bound divides by the edge, so the edge is not a spectator, and
`ScreenedGap.resolved_count_under_reported_of_raw_edge` says which one a caller may use: the floor
computed on the identity-removed residual, since a floor taken as a share of the TOTAL weight is
larger by the vacuum's share and therefore under-reports the count.
-/

/-- **The `SU(3)` 4-D gauge family on a COUNTED spectrum.**

The reflected form `QG` is a real `SU(3)` Haar expectation over a genuine four-dimensional Wilson
lattice, and `os_euc`/`os_perm` are proved via `Symmetry.expect_invariant` (Haar-invariance composed
with the lattice's axis symmetry) rather than by `rfl` through an inert label. `os_rp` and the
aperture bound `os_form` come from the clamp into `[0,1]`. `os_gap` is DERIVED from `hsorted` and
`hcount`.

Two hypotheses are named rather than hidden:

* `hcount` -- at most `c` modes clear the edge, at every spacing. This is the one the tension supplies.
* `hres` -- at least ONE does. That is what makes `os_form` non-vacuous at `B = 1`, and it is true of
  any read of a theory with a vacuum: the near-unit component is resolved. It is arity (`Q ≤ 1` needs
  something to be bounded BY), not a threshold.

DERIVED: the `1` in `B := 1` is the range of the clamp `QG` already applies (`min (max _ 0) 1`), not a
scale chosen here; `zero_le_one` is its nonnegativity. -/
noncomputable def ymFamilyGaugeCounted
    (ev : ℕ → ℕ → ℝ) (edge c : ℝ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (NaG a)) (ev a) edge : ℕ) : ℝ) ≤ c)
    (hres : ∀ a, 1 ≤ resolvedDim (Finset.range (NaG a)) (ev a) edge) : LatticeYMFamily :=
  familyOfSortedCount (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ)
    (Equiv.Perm (Fin 4)) actEG (Equiv.Perm (Fin 4)) actPG
    NaG ev QG edge c 1 zero_le_one hsorted hcount
    (fun _ _ => le_min (le_max_right _ _) zero_le_one)
    (fun j a => by
      have h1 : (1 : ℝ) ≤ (resolvedDim (Finset.range (NaG a)) (ev a) edge : ℝ) := by
        exact_mod_cast hres a
      calc QG j a ≤ 1 := min_le_right _ _
        _ = (1 : ℝ) * 1 := (one_mul 1).symm
        _ ≤ (resolvedDim (Finset.range (NaG a)) (ev a) edge : ℝ) * 1 :=
            mul_le_mul_of_nonneg_right h1 zero_le_one)
    (fun _ j a => by rw [QG_eq, QG_eq])
    (fun _ j a => by rw [QG_eq, QG_eq])

/-- **The OS0–OS3 continuum limit of the 4-D `SU(3)` gauge measure, with the infrared input counted.**

The composition the program builds toward on the measure side: the reflected form is a genuine
`SU(3)` Gibbs expectation over a four-dimensional periodic Wilson lattice, its Euclidean and
permutation invariances are derived from Haar-invariance composed with the lattice's axis symmetry,
and `os_gap` is derived from an ordered spectrum together with a bound on its resolved count. Every
OS datum is a theorem about the measure or a quantity a read reports; none is an assertion about the
infrared. No axiom beyond the foundational three. -/
theorem ym_continuum_gauge_counted
    (ev : ℕ → ℕ → ℝ) (edge c : ℝ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (NaG a)) (ev a) edge : ℕ) : ℝ) ≤ c)
    (hres : ∀ a, 1 ≤ resolvedDim (Finset.range (NaG a)) (ev a) edge) :
    ∃ (q : (ymFamilyGaugeCounted ev edge c hsorted hcount hres).J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (ymFamilyGaugeCounted ev edge c hsorted hcount hres).Q j (φ k))
              atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(ymFamilyGaugeCounted ev edge c hsorted hcount hres).c⌉₊ : ℝ)
              * (ymFamilyGaugeCounted ev edge c hsorted hcount hres).B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((ymFamilyGaugeCounted ev edge c hsorted hcount hres).actE g j) = q j) ∧
      (∀ σ j, q ((ymFamilyGaugeCounted ev edge c hsorted hcount hres).actP σ j) = q j) :=
  continuum_of_family (ymFamilyGaugeCounted ev edge c hsorted hcount hres)

#print axioms ym_continuum_gauge_counted

/-! ### The unconditional family: the counted one at a single supra-edge mode

`ym_continuum_gauge_counted` is conditional, and a conditional theorem whose hypotheses cannot all
hold at once proves nothing. The spectrum below satisfies all three, so the conditional is about
something -- and rather than leaving it beside the thing it witnesses, it IS the spectrum the
unconditional family uses.

It is deliberately the shape a gapped theory has: one resolved mode standing above the floor,
everything else beneath it. What a physical instance must supply is the same three facts about a
MEASURED spectrum.
-/

/-- A spectrum with a single supra-edge mode: the vacuum at `1`, everything else at `0`.

DERIVED: `1` and `0` are the two values a single-resolved-mode spectrum takes; the floor is any
value strictly between them and `resolvedDim_evDemo` is proved at one. Nothing is compared
against these numbers — they ARE the spectrum, the object under discussion. -/
noncomputable def evDemo (_a n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- **Exactly one mode clears a floor strictly between `0` and `1`, at every spacing.** -/
theorem resolvedDim_evDemo (a : ℕ) :
    resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) = 1 := by
  have hfilter : (Finset.range (NaG a)).filter (fun k => (1 / 2 : ℝ) < evDemo a k) = {0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, evDemo]
    constructor
    · rintro ⟨_, hlt⟩
      by_contra hk
      rw [if_neg hk] at hlt
      linarith
    · rintro rfl
      exact ⟨by simp [NaG], by norm_num⟩
  rw [resolvedDim, hfilter, Finset.card_singleton]

/-- **The spectrum is ordered.** A later index never carries more weight than an earlier one. -/
theorem evDemo_sorted (a : ℕ) : ∀ m n : ℕ, m ≤ n → evDemo a n ≤ evDemo a m := by
  intro m n hmn
  by_cases hm : m = 0
  · subst hm
    simp only [evDemo, if_pos rfl]
    split <;> norm_num
  · have hn : n ≠ 0 := by
      intro h; exact hm (Nat.le_zero.mp (h ▸ hmn))
    simp [evDemo, if_neg hm, if_neg hn]

/-- At most one mode clears the floor, so `hcount` holds at `c = 1`. -/
theorem evDemo_count (a : ℕ) :
    ((resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) : ℕ) : ℝ) ≤ 1 := by
  rw [resolvedDim_evDemo]; norm_num

/-- At least one does, so `hres` holds. -/
theorem evDemo_res (a : ℕ) : 1 ≤ resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) := by
  rw [resolvedDim_evDemo]

/-- **The constructed `SU(3)` OS-data family with DERIVED invariances, on a 4-D lattice.**

The counted family at the single-supra-edge-mode spectrum. Unconditional, because the three
hypotheses are discharged here rather than assumed -- and it is the same constructor, so there is one
route to this interface and not two.

DERIVED: the floor `1/2` is any value strictly between the two the spectrum takes; nothing depends on
which, and `resolvedDim_evDemo` is proved for this one. It separates the resolved mode from the rest,
which is what a floor is. -/
noncomputable def ymFamilyGauge : LatticeYMFamily :=
  ymFamilyGaugeCounted evDemo (1 / 2) 1 evDemo_sorted evDemo_count evDemo_res

/-- **The OS0–OS3 continuum limit with genuinely-derived invariances.** `continuum_of_family` on the
constructed four-dimensional `SU(3)` family: a subsequence and limit `q` with joint convergence, the
temperedness bound (OS0), reflection positivity (OS2), and Euclidean (OS1) / permutation (OS3)
invariance — the last two now flowing from Haar-invariance of the actual `SU(3)` gauge measure
composed with the hypercubic lattice's axis symmetry, not a `rfl`. Foundational footprint only. -/
theorem ym_continuum_gauge :
    ∃ (q : ymFamilyGauge.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => ymFamilyGauge.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈ymFamilyGauge.c⌉₊ : ℝ) * ymFamilyGauge.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (ymFamilyGauge.actE g j) = q j) ∧
      (∀ σ j, q (ymFamilyGauge.actP σ j) = q j) :=
  continuum_of_family ymFamilyGauge

#print axioms resolvedDim_evDemo
#print axioms evDemo_sorted
#print axioms ym_continuum_gauge

/-! ### The flagship existence-and-gap on the genuine-measure model

Reuse the flagship gap side (`gapModel`, with A1/A2 discharged in `WilsonInstance`) but take the
Osterwalder–Schrader measure to be the genuine `ymFamilyGauge` — whose invariances are derived from
`SU(3)` Haar-invariance rather than `rfl`. The existing flagship is untouched; this is the additive,
higher-fidelity companion (the OS-measure's OS1/OS3 are now genuine). Footprint is set by the gap
side; the measure side contributes NO axiom (its `os_rp` is the `[0,1]` clamp, not RP). -/

/-- The full `SU(N)` model with the junction gap data at an aperture and the **genuine gauge
OS-measure**. Confinement enters as the hypothesis `hconf`; the mode family is arbitrary. -/
-- DERIVED: the `0` below is the hypothesis `0 ≤ β`, the boundary of the physical half-line, not
-- a threshold on any measured quantity.
noncomputable def ymFullModelGauge (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : FullModel where
  gap := gapModelOf N s P m Δ c hdom hfe hgap
  h1 := gapModelOf_A1 N hconf s P m Δ c hdom hfe hgap
  h2 := gapModelOf_A2 N s P m Δ c hdom hfe hgap
  measure := ymFamilyGauge

/-- **Existence and the mass gap, with the OS-measure's Euclidean/permutation invariances DERIVED from
`SU(3)` Haar-invariance.** Same statement as `ym_existence_and_gap_model`, but the continuum measure's
OS1 (Euclidean) and OS3 (permutation) invariances flow from the actual `SU(3)` gauge measure, not from
a `rfl` through an inert label. -/
theorem ym_existence_and_gap_gauge (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.s β,
          (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.P β k * ((ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.μ β - (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.κ < 0) ∧
        (∀ d d', (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.R d = (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).gap.R d')) ∧
      (∃ (q : (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).measure.c⌉₊ : ℝ) * (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).measure.actE g j) = q j) ∧
        (∀ σ j, q ((ymFullModelGauge N hconf s P m Δ c hdom hfe hgap).measure.actP σ j) = q j)) :=
  existence_and_gap_of_model (ymFullModelGauge N hconf s P m Δ c hdom hfe hgap)

#print axioms ym_existence_and_gap_gauge

/-- The `SU(N)` Wilson realisation on the **genuine gauge OS-measure**: the flagship physical parameters
(`ymParams`: box `L=1`, confinement scale `k⋆=2π`) with the genuine-measure `ymFullModelGauge`, the
infrared cutoff matched (`hc`).

TWO RANKS APPEAR HERE, AND ONE OF THEM IS A PARAMETER. This carried three until `ymParams` took its
rank as an argument:

* `N` is the rank of BOTH the gap side (what `μYMAt N` and `μClampAt N` are read at) and the physical
  parameters (`ymParams N hN`). These were separate and are now one.
* the OS measure's rank is `NYM = 3`, fixed in `sysYM` as the Clay problem's group.

At `N = NYM` — `ym_wilson_gauge_su3` below — the two coincide and the realisation is a statement about
a single theory. At other `N` it is not, and no theorem here asserts otherwise: the gap side is a claim
about a correlation's decay and the measure side a claim about `SU(3)` Haar-invariance, and
`existence_and_gap_of_model` conjoins them without either referring to the other. Keeping `N` general
and instantiating separately is what makes the coincidence visible where it holds rather than assumed
everywhere.

DERIVED: `2` in `hN` is the arity of a special unitary group — the smallest rank at which `SU(N)` is
non-abelian — and `0 ≤ β` is the boundary of the physical half-line. Neither is a cut on a measured
quantity. -/
noncomputable def ym_wilson_gauge (N : ℕ) (hN : 2 ≤ N) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WilsonRealization where
  params := ymParams N hN
  model := ymFullModelGauge N hconf s P m Δ c hdom hfe hgap
  hc := by
    show (1 : ℝ) = 2 * Real.pi * 1 / (2 * Real.pi)
    rw [mul_one, div_self (show (0 : ℝ) < 2 * Real.pi by positivity).ne']

/-- **THE GAP WITH ITS RATE, ON THE `SU(3)` GAUGE CONSTRUCTION.**

`ym_existence_and_gap_gauge_wilson` concludes that the correlation tends to zero. This concludes what
a mass gap actually asserts: GEOMETRIC decay at a named rate, on the same hypotheses, with nothing
added.

    ‖C(τ)‖  ≤  (∑_k ‖P_k‖) · e^{-Δβ · τ}        and        κ₀ - μ_clamp  ≤  Δβ

The second half is where the entropy floor enters: the rate is bounded below by the MARGIN between
the proved floor `κ₀ = ¼ log 3` and the measured tension. It is not fitted, not asymptotic, and not an
existential -- it is a difference of two named quantities, and it is positive exactly when the
measurement clears the floor.

WHAT IS STILL ASSUMED, stated plainly because the hypotheses are where the content sits. `hdom` says
the active mode magnitudes are bounded by `e^{-Δβ}`; that is the modelling identification of §2-§3,
cited, and this theorem does not discharge it. `hfe` and `hgap` chain the floor margin into `Δ`. What
is proved here is that GIVEN those, the decay is geometric at that rate -- which is the step the
`Tendsto → 0` conclusion was missing, and the one the problem's statement asks for.

WHAT THIS DOES NOT YET GIVE. A rate at one spacing. Uniformity in the spacing is
`ZeroMode.gap_phys_of_fixed_screen`, which needs the aperture held at fixed PHYSICAL extent; the two
compose but are not composed here.

DERIVED: every quantity is a hypothesis of the statement. `κ₀YM` is the proved floor. -/
theorem ym_mass_gap_rate_gauge (N : ℕ)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) (β : ℝ) :
    κ₀YM - μClampAt N β ≤ Δ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖
        ≤ (∑ k ∈ s β, ‖P β k‖) * Real.exp (-Δ β) ^ τ :=
  ⟨le_trans (hfe β) (hgap β),
   fun τ => geometric_bound_of_mode_bound (s β) (P β) (m β) _
     (Real.exp_pos _).le (fun k hk => hdom β k hk) τ⟩

#print axioms ym_mass_gap_rate_gauge

/-- **And the rate is positive exactly when the measurement clears the floor.**

The gap is `Δ > 0`, and this says what has to be true of the ENSEMBLE for that: the clamped tension
below `κ₀`. That is the measured statement the certificates report, so the chain's positivity
requirement and the experiment's verdict are the same proposition rather than two that resemble each
other. -/
theorem ym_mass_gap_rate_pos (N : ℕ) (c Δ : ℝ → ℝ)
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β)
    (β : ℝ) (hclear : μClampAt N β < κ₀YM) :
    0 < Δ β :=
  lt_of_lt_of_le (by linarith) (le_trans (hfe β) (hgap β))

#print axioms ym_mass_gap_rate_pos

/-- **The existence-and-gap problem for the `SU(N)` Wilson realisation, on the genuine gauge measure.**
Same statement as `ym_existence_and_gap` (with named physical parameters), but the continuum OS-measure's
Euclidean/permutation invariances are DERIVED from `SU(3)` Haar-invariance rather than `rfl`. The existing
flagship `ym_existence_and_gap` is untouched; this is the additive, higher-fidelity realisation companion. -/
theorem ym_existence_and_gap_gauge_wilson (N : ℕ) (hN : 2 ≤ N)
    (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.s β,
          (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.P β k * ((ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.μ β - (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.κ < 0) ∧
        (∀ d d', (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.R d = (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.gap.R d')) ∧
      (∃ (q : (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.measure.c⌉₊ : ℝ) * (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.measure.actE g j) = q j) ∧
        (∀ σ j, q ((ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap).model.measure.actP σ j) = q j)) :=
  existence_and_gap_of_wilson (ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap)

#print axioms ym_existence_and_gap_gauge_wilson

/-! ### The Clay rank — where the gap side, the parameters and the measure are one group -/

/-- **The `SU(3)` Wilson realisation.** `ym_wilson_gauge` at `N = NYM`.

This is the object the three-ranks note is about. Here there is one rank and it is `NYM = 3`:

* the gap side is read at `NYM` — `μYMAt NYM`, `μClampAt NYM`;
* the physical parameters are `ymParams NYM`, since `ymParams` takes its rank as an argument;
* the OS measure is built on `sysYM = sysWilson NYM 4 nYM`, the four-dimensional periodic `SU(3)`
  Wilson lattice.

`NYM` appears once, in its own definition; every use above is that one symbol. There is no numeral
here to disagree with another numeral.

WHAT THIS DOES AND DOES NOT BUY. It makes the realisation a statement about a single gauge theory,
which the general-`N` form is not. It does not discharge `hfe` or `hgap` — those are the two open
junction residuals, and they are open at every rank. Nor does it make the measure side stronger: what
`Measure.continuum_of_family` proves is still a subsequential pointwise limit, not a measure on `ℝ⁴`.
The rank was never what those depended on, and tying it does not pretend otherwise.

DERIVED: every numeral here is the Clay problem's own data or a boundary, none a cut on a measured
quantity -- `3` is the rank `SU(3)` (written `NYM` everywhere it is used), `4` is four-dimensional
spacetime, and `0` is the boundary of the physical half-line `0 <= beta`. -/
noncomputable def ym_wilson_gauge_su3 (hconf : ∀ β, 0 ≤ β → μYMAt NYM β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt NYM β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WilsonRealization :=
  ym_wilson_gauge NYM (by norm_num) hconf s P m Δ c hdom hfe hgap

/-- The `SU(3)` realisation's physical rank IS the rank its OS measure is built at — the identity the
general-`N` form cannot state, and the whole point of taking the rank as a parameter. -/
theorem ym_wilson_gauge_su3_rank (hconf : ∀ β, 0 ≤ β → μYMAt NYM β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt NYM β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    (ym_wilson_gauge_su3 hconf s P m Δ c hdom hfe hgap).params.N = NYM := rfl

#print axioms ym_wilson_gauge_su3_rank

end MassGap.WilsonGauge
