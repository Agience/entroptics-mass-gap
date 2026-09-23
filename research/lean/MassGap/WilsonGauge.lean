import MassGap.SUN
import MassGap.Measure
import MassGap.WilsonInstance
import MassGap.WilsonHypercubic

/-!
# MassGap.WilsonGauge — a `LatticeYMFamily` built on the four-dimensional `SU(3)` Wilson system

Assembles `Measure.LatticeYMFamily` data whose reflected Schwinger form is an actual Gibbs
expectation, and runs it through `Measure.continuum_of_family`.

`sysYM` is `WilsonHypercubic.sysWilson NYM 4 nYM` with `NYM = 3` and `nYM = 2`: the four-dimensional
periodic Wilson system over `SU 3`, with `4 * nYM ^ 4` links and `16 * nYM ^ 4` plaquettes
(`WilsonHypercubic.card_link`, `card_plaq`), ordered-loop holonomy, and `WilsonAction.wilsonDensity`
as action density (`WilsonHypercubic.sysWilson_phi`). `symAxis e` is its axis-permutation symmetry,
from `WilsonHypercubic.axisSymmetry`.

`O0` is the Wilson plaquette energy of one plaquette; `QG j a` is the Gibbs expectation of `O0`
transported by the axis symmetry `symAxis (j.1 * j.2.1)`, clamped into `[0, 1]`. `QG_eq` collapses
the transport by `Symmetry.expect_invariant`, which is how the `os_euc` and `os_perm` fields are
discharged: `actEG` and `actPG` multiply the two permutation components of the index, and `QG` does
not see them.

`ymFamilyGaugeCounted` builds the family through `Measure.familyOfSortedCount`, which derives
`os_gap` from an ordered spectrum (`hsorted`) plus a bound on how many modes clear the edge
(`hcount`), with `hres` supplying at least one so the `os_form` bound at `B = 1` is not vacuous.
`ym_continuum_gauge_counted` applies `continuum_of_family` to it.

`evDemo` is the spectrum `1` at index `0` and `0` elsewhere; `resolvedDim_evDemo`, `evDemo_sorted`,
`evDemo_count` and `evDemo_res` discharge the three hypotheses at edge `1 / 2`, giving the
hypothesis-free `ymFamilyGauge` and `ym_continuum_gauge`.

The remaining declarations pair that measure with the gap side: `ymFullModelGauge` is a
`Measure.FullModel` whose `measure` field is `ymFamilyGauge`, `ym_wilson_gauge` wraps it with
`ymParams N hN` as a `WilsonRealization`, and `ym_wilson_gauge_su3` fixes `N := NYM`, where
`ym_wilson_gauge_su3_rank` records `params.N = NYM` by `rfl`. `ym_existence_and_gap_gauge`,
`ym_existence_and_gap_gauge_wilson`, `ym_mass_gap_rate_gauge` and `ym_mass_gap_rate_pos` state the
conclusions those carry.

Scope: `os_rp` here is the lower end of the clamp `min (max _ 0) 1`, not reflection positivity of a
measure. `hdom`, `hfe`, `hgap` and `hconf` are hypotheses in every theorem that uses them, and no
declaration in this file discharges them. `Measure.continuum_of_family` produces a subsequential
pointwise limit of the forms, not a measure on `ℝ⁴`. The gap side's rank `N` and the OS measure's
rank `NYM` are independent parameters except in `ym_wilson_gauge_su3`, where `N := NYM`.
-/

namespace MassGap.WilsonGauge

open MassGap.LatticeGauge MassGap.CompactGauge MassGap.Measure
open MeasureTheory Filter Topology

/-- The natural number `3`, used as the rank of the gauge group throughout this file. `SUN.SU` is
general in the rank; this abbreviation fixes the one instantiation the file is about, so that every
use below reads the same symbol.

DERIVED: `3` is the rank of the gauge group the Clay problem names. -/
abbrev NYM : ℕ := 3

/-- `MassGap.SUN.SU NYM`, the special unitary group at the rank `NYM` fixed above. All measures and
configurations in this file are valued in it.

DERIVED: no numeral appears in the statement; the rank is written `NYM`. -/
abbrev G3 : Type := MassGap.SUN.SU NYM

/-- The natural number `2`, used as the periodic extent of the constructed lattice.

Scope: `WilsonHypercubic` establishes the system, its cardinalities and its axis symmetry at
arbitrary extent; this abbreviation picks one, and nothing below depends on which.

DERIVED: `2` is the smallest extent at which a direction carries two distinct sites, so that the
unit shift is not the identity. It is the arity at which the object exists, not a size. -/
abbrev nYM : ℕ := 2

/-- `WilsonHypercubic.sysWilson NYM 4 nYM`: the periodic Wilson lattice gauge system over `G3` in
four dimensions at extent `nYM`. Links are `(direction, site)` pairs and plaquettes `(plane, site)`
pairs, so there are `4 * nYM ^ 4` links and `16 * nYM ^ 4` plaquettes (`WilsonHypercubic.card_link`,
`card_plaq`). The holonomy is the ordered product around `U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)⁻¹ U_ν(x)⁻¹`, and
the action density is `WilsonAction.wilsonDensity` rather than the zero function
(`WilsonHypercubic.sysWilson_phi`), so the coupling carried by `System.expect` moves the Gibbs
weight.

DERIVED: `4` is the spacetime dimension the Clay problem names. The rank and the extent are written
`NYM` and `nYM` and carry their own notes. -/
noncomputable def sysYM : System G3 := MassGap.WilsonHypercubic.sysWilson NYM 4 nYM

/-- The `Symmetry sysYM` carried by an axis permutation `e : Equiv.Perm (Fin 4)`, as
`WilsonHypercubic.axisSymmetry NYM e`. It rests on `WilsonHypercubic.shift_axis` (relabelling
commutes with the unit shift) and `bd_axis` (so the plaquette boundary word transports).

Scope: axis permutations only — reflections, translations and continuous rotations are not
constructed.

DERIVED: `4` is the spacetime dimension, the size of the permuted axis set. -/
noncomputable def symAxis (e : Equiv.Perm (Fin 4)) : Symmetry sysYM :=
  MassGap.WilsonHypercubic.axisSymmetry NYM (n := nYM) e

/-- The Wilson plaquette energy of the plaquette spanning directions `(0, 1)` at the origin site:
`WilsonAction.wilsonDensity (N := 3)` applied to `sysYM.hol` of that plaquette. It depends on the
configuration, unlike a label-reading form.

Scope: one fixed plaquette. Which pair of directions is named is a labelling choice on a lattice
whose axes are interchangeable by `symAxis`, and the site is the origin, which periodicity makes
immaterial.

DERIVED: `3` is the gauge rank passed to `wilsonDensity`, matching `NYM`; `4` is the spacetime
dimension in the plaquette's type; `0` and `1` are the two directions spanning the plane — a plane
needs exactly two — and the second `0` is the origin site `fun _ => 0`. -/
noncomputable def O0 : sysYM.Config → ℝ :=
  fun U => MassGap.WilsonAction.wilsonDensity (N := 3)
    (sysYM.hol (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 nYM) U)

/-- The reflected Schwinger form of the family: the Gibbs expectation of `O0` reindexed by
`symAxis (j.1 * j.2.1)`, at coupling `(a : ℝ)`, clamped by `min (max _ 0) 1`. The test configuration
`j` carries a Euclidean permutation, a permutation component and a natural number; the spacing index
`a` doubles as the coupling.

Scope: the clamp is what makes `os_rp` and the `os_form` bound available; it is applied to the
expectation, not derived from it.

DERIVED: `4` occurs twice, as the size of the axis set in each permutation component of the index
type; `0` and `1` are the endpoints of the clamp — the interval a reflected form is required to lie
in, with `0` the lower end used by `os_rp` and `1` the value of `B` used by `os_form`. -/
noncomputable def QG (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) : ℝ :=
  min (max (sysYM.expect (probHaar G3) (a : ℝ)
    (fun U => O0 (Symmetry.reindex (symAxis (j.1 * j.2.1)).onLink U))) 0) 1

/-- `QG j a = min (max (sysYM.expect (probHaar G3) a O0) 0) 1` at every `j` and `a`: the transport by
`symAxis (j.1 * j.2.1)` drops out. The single rewrite is
`Symmetry.expect_invariant`, which holds because the product Haar measure is invariant under the
axis relabelling.

Since the right-hand side does not mention `j`, this is what discharges the `os_euc` and `os_perm`
fields of the family: both reduce to an equality between two copies of it.

DERIVED: `4` occurs twice, as the size of the axis set in each permutation component of the index
type; `0` and `1` are the endpoints of the clamp, carried from `QG`. -/
theorem QG_eq (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    QG j a = min (max (sysYM.expect (probHaar G3) (a : ℝ) O0) 0) 1 := by
  unfold QG
  rw [Symmetry.expect_invariant sysYM (probHaar G3) (symAxis (j.1 * j.2.1)) (a : ℝ) O0]

/-- The action of `g : Equiv.Perm (Fin 4)` on a test configuration, multiplying the first component
and leaving the other two: `actEG g j = (g * j.1, j.2.1, j.2.2)`. It is the `actE` field of the
family.

DERIVED: `4` occurs five times, as the size of the axis set — once in the type of `g`, and twice in
each of the argument and result types. The `.1` and `.2` are projection notation, not numerals. -/
def actEG (g : Equiv.Perm (Fin 4)) (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) :
    Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ := (g * j.1, j.2.1, j.2.2)

/-- The action of `σ : Equiv.Perm (Fin 4)` on a test configuration, multiplying the second component
and leaving the other two: `actPG σ j = (j.1, σ * j.2.1, j.2.2)`. It is the `actP` field of the
family.

DERIVED: `4` occurs five times, as the size of the axis set — once in the type of `σ`, and twice in
each of the argument and result types. The `.1` and `.2` are projection notation, not numerals. -/
def actPG (σ : Equiv.Perm (Fin 4)) (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) :
    Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ := (j.1, σ * j.2.1, j.2.2)

/-- The mode count at spacing index `a`, as `a + 1`. It is strictly positive at every `a`, which is
what lets `Finset.range (NaG a)` contain the index `0`, and it increases without bound.

DERIVED: `1` is the offset that keeps the count nonzero at `a = 0`. -/
def NaG (a : ℕ) : ℕ := a + 1

/-! ### The family, assembled through `Measure.familyOfSortedCount`

A `LatticeYMFamily` carries four Osterwalder–Schrader data. Here `os_rp` and the `os_form` bound come
from the clamp `QG` applies, and `os_euc` and `os_perm` from `QG_eq`. The fourth, `os_gap`, asks that
every mode standing above the noise edge sit below a spacing-independent index cutoff.

`Measure.familyOfSortedCount` derives `os_gap` (by `os_gap_of_sorted_count`) from two other inputs:
an ordered spectrum, and a bound on how many of its modes clear the edge.
`ZeroMode.resolved_count_le_of_subset` is one source of such a count.

The edge appears in the count bound's divisor.
`ScreenedGap.resolved_count_under_reported_of_raw_edge` compares two candidate edges: a floor taken
as a share of the total weight is larger than one taken on the identity-removed residual by the
vacuum's share, and therefore reports a smaller count.
-/

/-- A `Measure.LatticeYMFamily` on the index type
`Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ`, with reflected form `QG`, actions `actEG` and `actPG`,
mode count `NaG`, spectrum `ev`, edge `edge`, count bound `c` and `B := 1`.

It is `Measure.familyOfSortedCount` at those arguments. The `os_rp` and `os_form` fields come from
the clamp `QG` applies: `le_min (le_max_right _ _) zero_le_one` for the former, and for the latter
`QG j a ≤ 1 ≤ resolvedDim … * 1` using `hres`. The `os_euc` and `os_perm` fields are `QG_eq` on both
sides. The `os_gap` field is derived by `familyOfSortedCount` from `hsorted` and `hcount`.

Scope: `hcount` bounds how many modes clear the edge at each spacing; `hres` requires at least one,
which is what makes the `os_form` bound at `B = 1` usable. Both are hypotheses, as are `ev`, `edge`
and `c`; nothing here obtains them from a measurement.

DERIVED: `1` in the type is the lower bound on `resolvedDim` in `hres`, requiring at least one
resolved mode. In the body, `4` is the spacetime dimension in the index type, and `1` is the value of
`B`, the upper end of the clamp `QG` already applies. -/
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

/-- `Measure.continuum_of_family` applied to `ymFamilyGaugeCounted`. Under the same three hypotheses,
there are a limit `q` on the family's index type and a strictly monotone `φ : ℕ → ℕ` such that
`Q j (φ k) → q j` at every `j`, with `|q j| ≤ ⌈c⌉₊ * B`, `0 ≤ q j`, and `q` invariant under both the
Euclidean and the permutation actions.

Scope: the conclusion is a subsequential pointwise limit of the forms `Q j`, along one subsequence
common to all `j`. It is not a measure on `ℝ⁴`, and the invariances are equalities between values of
`q`.

DERIVED: `1` is the lower bound on `resolvedDim` in `hres`, inherited from `ymFamilyGaugeCounted`;
`0` is the lower bound on each limit value `q j`. -/
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

/-! ### A spectrum satisfying the three hypotheses, and the resulting hypothesis-free family

`evDemo` puts weight `1` at index `0` and `0` at every other index. `resolvedDim_evDemo`,
`evDemo_sorted`, `evDemo_count` and `evDemo_res` discharge `hsorted`, `hcount` at `c = 1` and `hres`
at edge `1 / 2`, so `ymFamilyGauge` and `ym_continuum_gauge` carry no hypotheses.

The shape is one resolved mode above the floor and the rest beneath it. A different instance supplies
the same three facts about a different spectrum; the constructor is the same.
-/

/-- The spectrum `fun _a n => if n = 0 then 1 else 0`: weight `1` at index `0`, weight `0` at every
other index, the same at every spacing. The first argument is ignored.

Scope: two-valued, so any edge strictly between `0` and `1` resolves exactly the index `0`;
`resolvedDim_evDemo` fixes `1 / 2`.

DERIVED: `0` occurs twice — the index at which the spectrum is nonzero, and the value taken
everywhere else; `1` is the value at that index. These are the spectrum itself, not comparisons
against it. -/
noncomputable def evDemo (_a n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- `resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) = 1` at every spacing `a`. The filter
`{k ∈ range (NaG a) | 1 / 2 < evDemo a k}` is shown to be `{0}`: the index `0` is in range because
`NaG a = a + 1` is positive and carries value `1`, and every other index carries `0`, which does not
exceed `1 / 2`.

DERIVED: `1` and `2` are the edge `1 / 2`, a value strictly between the spectrum's two values; the
final `1` is the resulting count, one resolved mode. -/
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

/-- `evDemo a n ≤ evDemo a m` whenever `m ≤ n`: a later index never carries more weight. The proof
splits on whether `m` is `0`; if it is, the left side is at most `1`, and if it is not, `m ≤ n`
forces `n` nonzero too and both sides are `0`. This is the `hsorted` hypothesis of
`ymFamilyGaugeCounted`.

DERIVED: no numeral appears in the statement. -/
theorem evDemo_sorted (a : ℕ) : ∀ m n : ℕ, m ≤ n → evDemo a n ≤ evDemo a m := by
  intro m n hmn
  by_cases hm : m = 0
  · subst hm
    simp only [evDemo, if_pos rfl]
    split <;> norm_num
  · have hn : n ≠ 0 := by
      intro h; exact hm (Nat.le_zero.mp (h ▸ hmn))
    simp [evDemo, if_neg hm, if_neg hn]

/-- `(resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) : ℝ) ≤ 1` at every spacing, immediate
from `resolvedDim_evDemo`. This is the `hcount` hypothesis of `ymFamilyGaugeCounted` at `c = 1`.

DERIVED: `1` and `2` are the edge `1 / 2`; the final `1` is the count bound `c`, the number of modes
the spectrum places above that edge. -/
theorem evDemo_count (a : ℕ) :
    ((resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) : ℕ) : ℝ) ≤ 1 := by
  rw [resolvedDim_evDemo]; norm_num

/-- `1 ≤ resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2)` at every spacing, immediate from
`resolvedDim_evDemo`. This is the `hres` hypothesis of `ymFamilyGaugeCounted`.

DERIVED: the leading `1` is the lower bound, at least one resolved mode; `1` and `2` are the edge
`1 / 2`. -/
theorem evDemo_res (a : ℕ) : 1 ≤ resolvedDim (Finset.range (NaG a)) (evDemo a) (1 / 2) := by
  rw [resolvedDim_evDemo]

/-- `ymFamilyGaugeCounted` at spectrum `evDemo`, edge `1 / 2` and count bound `1`, with the three
hypotheses supplied by `evDemo_sorted`, `evDemo_count` and `evDemo_res`. It takes no arguments.

DERIVED: no numeral appears in the type. In the body, `1` and `2` are the edge `1 / 2`, any value
strictly between the spectrum's two values, and the trailing `1` is the count bound `c`. -/
noncomputable def ymFamilyGauge : LatticeYMFamily :=
  ymFamilyGaugeCounted evDemo (1 / 2) 1 evDemo_sorted evDemo_count evDemo_res

/-- `Measure.continuum_of_family` at `ymFamilyGauge`, with no hypotheses: there exist a limit `q` on
the family's index type and a strictly monotone `φ : ℕ → ℕ` with `Q j (φ k) → q j` at every `j`,
`|q j| ≤ ⌈c⌉₊ * B`, `0 ≤ q j`, and `q` invariant under `actE` and `actP`.

Scope: a subsequential pointwise limit of the forms along one common subsequence. The `os_rp` datum
behind `0 ≤ q j` is the lower end of the clamp in `QG`.

DERIVED: `0` is the lower bound on each limit value `q j`. No other numeral appears in the
statement. -/
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

/-! ### Pairing the gap side with `ymFamilyGauge`

The gap side is `gapModelOf` with A1 and A2 discharged in `WilsonInstance`; the measure field is
`ymFamilyGauge`. The axiom footprint is set by the gap side — the measure side's `os_rp` is the
lower end of the `[0, 1]` clamp in `QG`, not reflection positivity of a measure. -/

/-- A `Measure.FullModel` whose `gap` field is `gapModelOf N s P m Δ c hdom hfe hgap`, whose `h1` and
`h2` are `gapModelOf_A1` and `gapModelOf_A2`, and whose `measure` field is `ymFamilyGauge`.

Scope: the rank `N` of the gap side is a parameter, independent of the measure's rank `NYM`;
`ym_wilson_gauge_su3` is where the two are identified. `hconf`, `hdom`, `hfe` and `hgap` are
hypotheses carried into the record, not discharged. The mode index type `Idx` is arbitrary.

DERIVED: `0` is the lower bound on `β` in `hconf`, the boundary of the half-line on which
confinement is required. No other numeral appears in the statement. -/
-- The `0` above is the hypothesis `0 ≤ β`, the boundary of the physical half-line, not
-- a threshold on any measured quantity.
noncomputable def ymFullModelGauge (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : FullModel where
  gap := gapModelOf N s P m Δ c hdom hfe hgap
  h1 := gapModelOf_A1 N hconf s P m Δ c hdom hfe hgap
  h2 := gapModelOf_A2 N s P m Δ c hdom hfe hgap
  measure := ymFamilyGauge

/-- `Measure.existence_and_gap_of_model` at `ymFullModelGauge`. The conclusion is a conjunction of two
groups: from the gap side, that the mode sum tends to `0` at every `β`, that `gap.μ β - gap.κ < 0`,
and that `gap.R` is constant; and from the measure side, the subsequential limit `q` with its
temperedness bound, nonnegativity and invariance under `actE` and `actP`.

Scope: the two groups are conjoined by `existence_and_gap_of_model` without either referring to the
other — the gap side is about a correlation's decay at rank `N`, the measure side about
`ymFamilyGauge` at rank `NYM`. `hconf`, `hdom`, `hfe` and `hgap` are hypotheses.

DERIVED: `0` occurs four times — the lower bound on `β` in `hconf`, the limit point of the mode sum,
the comparison point in `gap.μ β - gap.κ < 0`, and the lower bound on each `q j`. -/
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

/-- A `WilsonRealization` with `params := ymParams N hN` (box `L = 1`, confinement scale `k⋆ = 2π`)
and `model := ymFullModelGauge N hconf s P m Δ c hdom hfe hgap`. The `hc` field, matching the
infrared cutoff, is `1 = 2 * π * 1 / (2 * π)`, closed by `div_self`.

Scope: two ranks appear. `N` is the rank of the gap side (`μYMAt N`, `μClampAt N`) and of the
physical parameters `ymParams N hN`. The OS measure's rank is `NYM`, fixed inside `sysYM`. They
coincide only when `N` is instantiated at `NYM`, which `ym_wilson_gauge_su3` does; at other `N` the
two sides are about different ranks and no declaration here asserts otherwise.

DERIVED: `2` is the lower bound on `N` in `hN`, the smallest rank at which `SU(N)` is non-abelian;
`0` is the lower bound on `β` in `hconf`, the boundary of the half-line confinement is required on.
The `1` and `2 * π` of the `hc` field live in the body, from `ymParams`. -/
noncomputable def ym_wilson_gauge (N : ℕ) (hN : 2 ≤ N) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WilsonRealization where
  params := ymParams N hN
  model := ymFullModelGauge N hconf s P m Δ c hdom hfe hgap
  hc := by
    show (1 : ℝ) = 2 * Real.pi * 1 / (2 * Real.pi)
    rw [mul_one, div_self (show (0 : ℝ) < 2 * Real.pi by positivity).ne']

/-- Given `hdom` (every active mode magnitude at `β` is at most `Real.exp (-Δ β)`), `hfe`
(`κ₀YM - μClampAt N β ≤ c β`) and `hgap` (`c β ≤ Δ β`), the conclusion at each `β` is the conjunction

    κ₀YM - μClampAt N β ≤ Δ β    and    ∀ τ, ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖ ≤ (∑ k ∈ s β, ‖P β k‖) * Real.exp (-Δ β) ^ τ.

The first conjunct chains `hfe` with `hgap`; the second is `geometric_bound_of_mode_bound` at the
mode bound `Real.exp (-Δ β)`, whose nonnegativity is `Real.exp_pos`.

Scope: the bound is at a single spacing, with `Δ` an arbitrary function — it is not asserted
positive, so the second conjunct need not decay. `hdom` identifies the mode magnitudes and is a
hypothesis. The first conjunct bounds `Δ β` below by the difference of `κ₀YM` and `μClampAt N β`;
whether that difference is positive is the separate `ym_mass_gap_rate_pos`.

DERIVED: no numeral appears in the statement. `κ₀YM` and `μClampAt N` are named quantities defined
elsewhere, and `s`, `P`, `m`, `Δ`, `c` and `β` are the caller's. -/
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

/-- Given `hfe` (`κ₀YM - μClampAt N β ≤ c β`), `hgap` (`c β ≤ Δ β`) and `hclear`
(`μClampAt N β < κ₀YM`), the rate satisfies `0 < Δ β`. Chaining `hfe` and `hgap` bounds `Δ β` below
by `κ₀YM - μClampAt N β`, which `hclear` makes positive.

Scope: one direction only. `Δ` is an arbitrary function, so `0 < Δ β` can hold without `hclear`; the
converse is not stated.

DERIVED: `0` is the lower bound on `Δ β`. No other numeral appears in the statement. -/
theorem ym_mass_gap_rate_pos (N : ℕ) (c Δ : ℝ → ℝ)
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β)
    (β : ℝ) (hclear : μClampAt N β < κ₀YM) :
    0 < Δ β :=
  lt_of_lt_of_le (by linarith) (le_trans (hfe β) (hgap β))

#print axioms ym_mass_gap_rate_pos

/-- `Measure.existence_and_gap_of_wilson` at `ym_wilson_gauge N hN hconf s P m Δ c hdom hfe hgap`.
The conclusion is the same two-group conjunction as `ym_existence_and_gap_gauge`, read through the
realisation's `model` field: the gap side's decay to `0`, the strict inequality
`model.gap.μ β - model.gap.κ < 0` and constancy of `model.gap.R`; and the measure side's
subsequential limit `q` with its temperedness bound, nonnegativity and invariance under `actE` and
`actP`.

Scope: adds the named physical parameters `ymParams N hN` to `ym_existence_and_gap_gauge`; the
mathematical content of the two conclusions is the same. `hconf`, `hdom`, `hfe` and `hgap` remain
hypotheses.

DERIVED: `2` is the lower bound on `N` in `hN`, the smallest rank at which `SU(N)` is non-abelian;
`0` occurs four times — the lower bound on `β` in `hconf`, the limit point of the mode sum, the
comparison point in `model.gap.μ β - model.gap.κ < 0`, and the lower bound on each `q j`. -/
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

/-! ### The instantiation at `N := NYM`, where the gap side and the measure share a rank -/

/-- `ym_wilson_gauge` at `N := NYM`, with `hN : 2 ≤ NYM` discharged by `norm_num`. Here one rank
serves all three components: the gap side is read at `NYM` (`μYMAt NYM`, `μClampAt NYM`), the
physical parameters are `ymParams NYM`, and the OS measure is built on
`sysYM = sysWilson NYM 4 nYM`. Every occurrence is the symbol `NYM`, whose value is fixed in one
place.

Scope: `hfe` and `hgap` remain hypotheses, as at every rank, and the measure side still delivers a
subsequential pointwise limit rather than a measure on `ℝ⁴`. What the instantiation adds is that the
two sides are about the same rank.

DERIVED: `0` is the lower bound on `β` in `hconf`, the boundary of the half-line confinement is
required on. The rank is written `NYM` throughout, so no rank numeral appears in the statement; the
dimension `4` is inside `sysYM`. -/
noncomputable def ym_wilson_gauge_su3 (hconf : ∀ β, 0 ≤ β → μYMAt NYM β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt NYM β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WilsonRealization :=
  ym_wilson_gauge NYM (by norm_num) hconf s P m Δ c hdom hfe hgap

/-- `(ym_wilson_gauge_su3 hconf s P m Δ c hdom hfe hgap).params.N = NYM`, by `rfl`: the realisation's
physical rank is the same symbol the OS measure is built at. The general-`N` form cannot state this,
since there the two ranks are independent parameters.

DERIVED: `0` is the lower bound on `β` in `hconf`. The rank is written `NYM` on both sides, so no
rank numeral appears. -/
theorem ym_wilson_gauge_su3_rank (hconf : ∀ β, 0 ≤ β → μYMAt NYM β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt NYM β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    (ym_wilson_gauge_su3 hconf s P m Δ c hdom hfe hgap).params.N = NYM := rfl

#print axioms ym_wilson_gauge_su3_rank

end MassGap.WilsonGauge
