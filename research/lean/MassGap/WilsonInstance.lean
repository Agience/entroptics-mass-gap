import MassGap.FullModel
import MassGap.Complete

/-!
# MassGap.WilsonInstance — a constructed `SU(N)` `FullModel` and `WilsonRealization`

`existence_and_gap_of_model` is stated over abstract structure variables. This module constructs
values of `LatticeYMFamily`, `LatticeYM`, `FullModel`, `WilsonParams` and `WilsonRealization` at
rank `N`, so that `existence_and_gap_of_wilson` can be applied to a concrete object; that
application is `ym_existence_and_gap_of_junction`.

## The measure side

`ymFamily N hev` is a `LatticeYMFamily` on test configurations
`JYM = Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ`. Its reflected form `QYM N j a` is the Wilson
ensemble correlation `wilsonCorrAt N (a : ℝ)` at the lag `j.2.2 % (N + 1)`, truncated above by `1`.
The fields are discharged as follows:

* `os_rp` — nonnegativity, from `Complete.wilson_reflection_positive_at_even`. This is why the
  family carries `hev : ∃ k, N + 1 = 2 * k ∧ 2 ≤ k`: that theorem holds at even extent at least
  four. Its coupling hypothesis is met because `wilsonCorrAt` is read at the spacing `a : ℕ` cast to
  `ℝ`, which is nonnegative.
* `os_gap` — from `evYM`, which places every mode but `n = 0` below the edge.
* `os_form` — from `QYM ≤ 1` and `resolvedDim ≥ 1 = c`, a single hardwired supra-edge mode.
* `os_euc` and `os_perm` — by `rfl`. `actEYM` acts on `j.1` and `actPYM` on `j.2.1`, while `QYM`
  reads `j` only through `j.2.2`, so the invariances hold because the actions do not move the
  component the form reads. Any `Q` reading only that component would satisfy them.

The coupling slot of `wilsonCorrAt` is occupied here by the cast spacing `a`, whereas on the gap
side it is the coupling `β`.

## The gap side

`μClampAt N β` is `μYMAt N β` for `0 ≤ β` and `0` otherwise. `gapModelOf` is
`Capacity.modelOfJunction` at the floor `κ₀YM` and that tension, over a mode family `s`, `P`, `m`
and functions `Δ`, `c` that are all arguments, with `hread` derived from three hypotheses: `hdom`,
`‖m β k‖ ≤ exp (-Δ β)`; `hfe`, `κ₀YM - μClampAt N β ≤ c β`; and `hgap`, `c β ≤ Δ β`. `gapModelOf_A1`
and `gapModelOf_A2` discharge `A1_YM` and `A2_YM`, the first from `hconf` on `0 ≤ β` and `κ₀YM_pos`
on the clamped branch, the second as `ym_A2_at N`.

At `κ = κ₀` the three hypotheses recombine to `‖m β k‖ ≤ exp (-(κ₀YM - μClampAt N β))`, with `c`
cancelling, so taking the mode family as an argument makes the assumption appear in the statement
rather than in a definition.

## Scope

`hfe` and `hgap` are hypotheses of every gap-side declaration here. `hconf` is a hypothesis on the
half-line `0 ≤ β`. What `Measure.continuum_of_family` supplies on the measure side is a bounded,
nonnegative, invariance-preserving subsequential pointwise limit `q : JYM → ℝ` over a countable
index set, obtained by a diagonal Bolzano–Weierstrass argument: not a measure, not on `ℝ⁴`, and with
no Schwinger function, reflection positivity of the limit as a quadratic form, clustering or
regularity. The OS-to-Wightman reconstruction is not composed anywhere in this module, and no
declaration carries it: `QYM` is a value per test configuration, while
`WightmanData.os_reconstruction_wightman` consumes a continuous bilinear form on a normed test
space. `ymFamily` realises the `LatticeYMFamily` interface with one supra-edge mode and is tied to
the ensemble through `QYM` and `os_rp` alone; it does not match `ymModel`'s aperture. No new axiom
and no `sorry`.

Footprint of `ym_existence_and_gap_of_junction`: the three foundational axioms and the named cited
axiom `wilson_reflection_positive_at`, which reaches it through the gap side's `μYMAt` and
`ymModelAt`; `ymFamily` is foundational-only.

DERIVED: `4` is the spacetime dimension in `Equiv.Perm (Fin 4)`; `2` in `hev` is the even extent
divisor, `2 ≤ k` is `4 ≤ N + 1`, and `2 ≤ N` is the smallest rank at which `SU(N)` is non-abelian —
the first two read off `wilson_reflection_positive_at_even`'s hypotheses; `1` is the lag arity
offset in `N + 1`, the family's `c` and `B`, the unit box `L`, and the clamp's upper truncation; `0`
is the boundary of the physical half-line, the family's `edge`, the clamped tension, and the mode
index above the edge; `2 * Real.pi` is the confinement scale `k⋆`, fixed so that
`k⋆ * L / (2 * Real.pi) = 1` equals the family's `c`.
-/

namespace MassGap
open MassGap.Measure Filter

/-! ## The measure side: a constructed `LatticeYMFamily` -/

/-- The test-configuration type: a Euclidean element, a permutation, and a natural-number label,
`Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ`. `actEYM` acts on the first component, `actPYM` on the
second, and `QYM` reads the third.

DERIVED: `4` is the spacetime dimension the permutation groups act on. -/
abbrev JYM : Type := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ

/-- The reflected form: `min (wilsonCorrAt N (a : ℝ) ⟨j.2.2 % (N + 1), _⟩) 1`. It reads the Wilson
ensemble correlation at rank `N`, with the spacing `a` cast to `ℝ` in `wilsonCorrAt`'s coupling slot
and with lag `j.2.2 % (N + 1)`, and truncates the value above by `1`. Nonnegativity is supplied by
`Complete.wilson_reflection_positive_at_even` in `ymFamily`'s `os_rp` field.

`QYM` depends on the test configuration `j` only through its third component `j.2.2`; the first two
components do not appear.

DERIVED: `4` reaches the statement through `JYM`'s permutation groups; `2` appears as the product
projections in `j.2.2`; `1` in `N + 1` is the lag arity offset, `Fin (N + 1)` indexing lags `0 … N`,
and the trailing `1` is the upper truncation. -/
noncomputable def QYM (N : ℕ) (j : JYM) (a : ℕ) : ℝ :=
  min (wilsonCorrAt N (a : ℝ) ⟨j.2.2 % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩) 1

/-- The Euclidean action on test configurations: left multiplication by `g` on the first component,
leaving the other two fixed. It is a non-trivial group action of `Equiv.Perm (Fin 4)`, and it does
not move the component `QYM` reads.

DERIVED: `4` is the spacetime dimension the permutation group acts on; `1` and `2` are the product
projections `j.1`, `j.2.1` and `j.2.2`. -/
def actEYM (g : Equiv.Perm (Fin 4)) (j : JYM) : JYM := (g * j.1, j.2.1, j.2.2)

/-- The permutation action on test configurations: left multiplication by `σ` on the second
component, leaving the other two fixed. Like `actEYM`, it is non-trivial and does not move the
component `QYM` reads.

DERIVED: `4` is the spacetime dimension the permutation group acts on; `1` and `2` are the product
projections `j.1`, `j.2.1` and `j.2.2`. -/
def actPYM (σ : Equiv.Perm (Fin 4)) (j : JYM) : JYM := (j.1, σ * j.2.1, j.2.2)

/-- The family's eigenvalue field: `1` at mode `n = 0` and `-1` elsewhere, at every spacing. With
the family's `edge := 0`, exactly one mode lies above the edge, which is what makes the aperture a
single supra-edge mode and discharges `os_gap`.

DERIVED: `0` is the index of the one supra-edge mode and the value `n` is compared against; `1` and
`-1` are the two eigenvalues, placed on either side of the family's `edge := 0`. -/
def evYM (_a n : ℕ) : ℝ := if n = 0 then 1 else -1

/-- The mode count at spacing index `a`: `a + 1`, so the range `Finset.range (NaYM a)` is nonempty
at every `a` and grows with `a`.

DERIVED: `1` makes the mode count positive at `a = 0`, so mode `0` is always present. -/
def NaYM (a : ℕ) : ℕ := a + 1

/-- A `LatticeYMFamily` at rank `N`, with `J := JYM`, both group fields `Equiv.Perm (Fin 4)`,
`Q := QYM N`, `ev := evYM`, `Na := NaYM`, `edge := 0`, and `c = B = 1`.

The fields are discharged thus. `os_rp` is `Complete.wilson_reflection_positive_at_even` combined
with `zero_le_one` through `le_min`; it consumes `hev`, and its coupling hypothesis is met because
`wilsonCorrAt`'s coupling slot holds the cast spacing `(a : ℝ)`, which is nonnegative. `os_gap` is a
case split on `n = 0`, the only mode `evYM` puts above `edge := 0`. `os_form` uses `QYM ≤ 1` from
the truncation together with `1 ≤ resolvedDim`, mode `0` being in range at every spacing. `os_euc`
and `os_perm` are `rfl`, since `actEYM` and `actPYM` move `j.1` and `j.2.1` while `QYM` reads
`j.2.2`.

The family realises the interface with one supra-edge mode and is tied to the Wilson ensemble
through `QYM` and `os_rp` alone. No named axiom is used: `os_rp` is a theorem, at the price of the
extent hypothesis `hev`. The `SU(3)` instantiation runs at `N = NYM = 3`, whose extent is
`4 = 2 * 2`, so `hev` is met there.

DERIVED: `4` is the spacetime dimension in the group fields; in `hev`, `2 * k` is the even extent
and `2 ≤ k` is `4 ≤ N + 1`, both read off `wilson_reflection_positive_at_even`'s hypotheses and
carried as one existential, which is `EvenAperture.EvenAp`'s membership predicate; `1` in `N + 1` is
the lag arity offset, and `c := 1`, `B := 1` are the single supra-edge mode and the truncation
bound; `0` is the noise `edge`, set below the one supra-edge eigenvalue. -/
noncomputable def ymFamily (N : ℕ) (hev : ∃ k : ℕ, N + 1 = 2 * k ∧ 2 ≤ k) : LatticeYMFamily where
  J := JYM
  G := Equiv.Perm (Fin 4)
  actE := actEYM
  P := Equiv.Perm (Fin 4)
  actP := actPYM
  Na := NaYM
  ev := evYM
  Q := QYM N
  edge := 0
  c := 1
  B := 1
  hB := zero_le_one
  os_rp := fun _ a =>
    le_min ((wilson_reflection_positive_at_even N hev.choose hev.choose_spec.1 hev.choose_spec.2
      (show (0 : ℝ) ≤ (a : ℝ) by positivity)).1 _) zero_le_one
  os_gap := by
    intro a n _ h
    by_cases hn0 : n = 0
    · subst hn0; norm_num
    · exfalso; simp only [evYM, if_neg hn0] at h; linarith
  os_form := by
    intro j a
    have h1 : 1 ≤ resolvedDim (Finset.range (NaYM a)) (evYM a) 0 := by
      rw [resolvedDim, Finset.one_le_card]
      exact ⟨0, by simp [Finset.mem_filter, Finset.mem_range, NaYM, evYM]⟩
    have hc : (1 : ℝ) ≤ (resolvedDim (Finset.range (NaYM a)) (evYM a) 0 : ℝ) := by exact_mod_cast h1
    calc QYM N j a ≤ 1 := min_le_right _ _
      _ ≤ (resolvedDim (Finset.range (NaYM a)) (evYM a) 0 : ℝ) * 1 := by nlinarith
  os_euc := fun _ _ _ => rfl
  os_perm := fun _ _ _ => rfl

#print axioms ymFamily

/-! ## The gap side: `A1_YM` discharged on the physical half-line -/

/-- The tension at rank `N`, clamped on the unphysical branch: `μYMAt N β` when `0 ≤ β`, and `0`
otherwise. The clamp is what lets `A1_YM`, which quantifies over all real `β`, follow from a
confinement hypothesis stated only on the half-line.
-/
-- DERIVED: `0` is the boundary of the physical half-line in the branch condition, and the value the
-- unphysical branch takes. That branch needs only some value below the floor, and `κ₀YM_pos` is what
-- puts zero below it.
noncomputable def μClampAt (N : ℕ) (β : ℝ) : ℝ := if 0 ≤ β then μYMAt N β else 0

/-- A `LatticeYM` over an arbitrary mode family: `Capacity.modelOfJunction` at floor `κ₀YM`, both
`κ₀` and `κ` set to `κ₀YM`, tension `μClampAt N`, and the direction profile `(ymModelAt N).R`. The
index type `Idx`, the active sets `s`, the weights `P`, the modes `m` and the functions `Δ`, `c` are
all arguments, and the structure's `hread` field is derived from three hypotheses:

* `hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β)`,
* `hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β`,
* `hgap : ∀ β, c β ≤ Δ β`.

Taking the mode family as an argument puts the assumption in the signature rather than in a
definition. It is not a weaker assumption: at `κ = κ₀` the three recombine to
`‖m β k‖ ≤ Real.exp (-(κ₀YM - μClampAt N β))`, with `c` cancelling, as
`Capacity.hread_of_junction`'s own scope note records.

DERIVED: no numeral appears in the statement. -/
noncomputable def gapModelOf (N : ℕ) {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ)
    (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : LatticeYM :=
  Capacity.modelOfJunction s P m (ymModelAt N).R κ₀YM κ₀YM (μClampAt N) Δ c (le_refl _) hdom hfe hgap

/-- `A1_YM (gapModelOf N s P m Δ c hdom hfe hgap)` from `hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM`.
`A1_YM` reads only the `μ` and `κ₀` fields, which `gapModelOf` fixes to `μClampAt N` and `κ₀YM`
whatever the mode family, so the proof splits on `0 ≤ β`: `hconf` on the physical branch, `κ₀YM_pos`
on the clamped one. It does not use `m`, `Δ`, `c`, `hdom`, `hfe` or `hgap`.

DERIVED: `0` is the boundary of the physical half-line, both in `hconf` and in the case split. -/
theorem gapModelOf_A1 (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    A1_YM (gapModelOf N s P m Δ c hdom hfe hgap) := by
  show ∀ β, μClampAt N β < κ₀YM
  intro β
  by_cases h : 0 ≤ β
  · simp only [μClampAt, if_pos h]; exact hconf β h
  · simp only [μClampAt, if_neg h]; have := κ₀YM_pos; linarith

/-- `A2_YM (gapModelOf N s P m Δ c hdom hfe hgap)`, which is `ym_A2_at N` unchanged: `gapModelOf`
keeps `(ymModelAt N).R` as its direction profile, so the isotropy clause is the same statement.

DERIVED: no numeral appears in the statement. -/
theorem gapModelOf_A2 (N : ℕ) {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    A2_YM (gapModelOf N s P m Δ c hdom hfe hgap) := ym_A2_at N

/-! ### The collapsed instance

`gapModel` is `gapModelOf` at the one mode family for which `hfe` and `hgap` hold by `le_refl`: a
single mode defined to be `exp (-(κ₀YM - μClampAt N β))`. In that instance the two hypotheses carry
no content, which is what its own docstring records. -/

/-- A `FullModel` at rank `N`: the `gap` field is `gapModelOf` over the caller's mode family, `h1`
and `h2` are `gapModelOf_A1` and `gapModelOf_A2`, and the `measure` field is `ymFamily N hev`. The
mode family and the hypotheses `hdom`, `hfe`, `hgap`, `hconf`, `hev` are all arguments; the two
fields are independent, nothing in `FullModel` relating the gap datum to the measure family.
-/
-- DERIVED: `0` is the boundary of the physical half-line in `hconf`; in `hev`, `2 * k` is the even
-- extent and `2 ≤ k` is `4 ≤ N + 1`, both read off `wilson_reflection_positive_at_even`; the `1` in
-- `N + 1` is the lag arity offset.
noncomputable def ymFullModelOf (N : ℕ) (hev : ∃ k : ℕ, N + 1 = 2 * k ∧ 2 ≤ k)
    (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : FullModel where
  gap := gapModelOf N s P m Δ c hdom hfe hgap
  h1 := gapModelOf_A1 N hconf s P m Δ c hdom hfe hgap
  h2 := gapModelOf_A2 N s P m Δ c hdom hfe hgap
  measure := ymFamily N hev

/-! ## The existence-and-gap problem, for an SU(N) Wilson realisation with named physical parameters -/

/-- `WilsonParams` at rank `N`: box size `L := 1`, confinement scale `kstar := 2 * Real.pi`, so the
derived infrared cutoff `irCutoff = kstar * L / (2 * Real.pi)` is `1`, matching `ymFamily`'s `c`.
`ym_hc` states that match.

The rank is the argument `N`, with `hN : 2 ≤ N`, so a realisation built from this record is read at
one rank throughout.

DERIVED: `2` in `hN` is the smallest rank at which `SU(N)` is non-abelian; `1` is the unit box `L`;
`2 * Real.pi` is the confinement scale `k⋆`, fixed so that `k⋆ * L / (2 * Real.pi) = 1` equals the
family's infrared cutoff — an identity between two named quantities, not a magnitude. -/
noncomputable def ymParams (N : ℕ) (hN : 2 ≤ N) : WilsonParams where
  N := N
  hN := hN
  L := 1
  hL := one_pos
  kstar := 2 * Real.pi
  hk := by positivity

/-- `(ymFamily N hev).c = (ymParams N hN).irCutoff`: both sides are `1`, the right after
`2 * Real.pi * 1 / (2 * Real.pi)` is reduced by `div_self`. It is the `hc` field every
`WilsonRealization` below needs, and it involves neither the gap side nor any mode family.

DERIVED: `1` is the family's `c` and the box size `L`; `2 * Real.pi` is `k⋆` and the divisor in
`irCutoff`; in `hev`, `2 * k` is the even extent and `2 ≤ k` is `4 ≤ N + 1`; `2 ≤ N` is the smallest
non-abelian rank. -/
theorem ym_hc (N : ℕ) (hev : ∃ k : ℕ, N + 1 = 2 * k ∧ 2 ≤ k) (hN : 2 ≤ N) :
    ((ymFamily N hev).c) = (ymParams N hN).irCutoff := by
  show (1 : ℝ) = 2 * Real.pi * 1 / (2 * Real.pi)
  rw [mul_one, div_self (show (0 : ℝ) < 2 * Real.pi by positivity).ne']

/-- A `WilsonRealization` at rank `N`: `params := ymParams N hN`, `model := ymFullModelOf ...` over
the caller's mode family, and `hc := ym_hc N hev hN`, which matches the family's infrared cutoff to
`k⋆ * L / (2 * Real.pi)`.
-/
-- DERIVED: `0` is the physical half-line boundary in `hconf`; `2` in `hN` is the smallest rank at
-- which `SU(N)` is non-abelian, not a size; in `hev`, `2 * k` is the even extent and `2 ≤ k` is
-- `4 ≤ N + 1`; the `1` in `N + 1` is the lag arity offset.
noncomputable def ym_wilson_of (N : ℕ) (hev : ∃ k : ℕ, N + 1 = 2 * k ∧ 2 ≤ k) (hN : 2 ≤ N)
    (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WilsonRealization where
  params := ymParams N hN
  model := ymFullModelOf N hev hconf s P m Δ c hdom hfe hgap
  hc := ym_hc N hev hN

/-- `existence_and_gap_of_wilson` applied to `ym_wilson_of`, for any mode family satisfying `hdom`,
`hfe` and `hgap`. The conclusion is a conjunction of two independent parts.

The gap part: at every `β`, `‖∑ k ∈ s β, P β k * m β k ^ τ‖ → 0` as `τ → ∞`; non-triviality
`μClampAt N β - κ₀YM < 0`; and `(ymModelAt N).R d = (ymModelAt N).R d'` for all directions. It is
conditional on `hfe` and `hgap`, which are hypotheses supplied by the caller, and on `hconf`.

The measure part: a subsequence `φ` and a pointwise limit `q : JYM → ℝ` of the reflected forms, with
`|q j| ≤ ⌈c⌉₊ * B`, `0 ≤ q j`, and invariance under both actions. What
`Measure.continuum_of_family` supplies is that limit — obtained by a diagonal Bolzano–Weierstrass
argument over a countable index set — and not a measure, not one on `ℝ⁴`, and not OS0–OS4: there is
no Schwinger function, no reflection positivity of the limit as a quadratic form, no clustering and
no regularity. The invariance holds by `rfl`, since `QYM` reads only `j.2.2` and the
`Equiv.Perm (Fin 4)` actions move `j.1` and `j.2.1`.

`ymFamily` realises the `LatticeYMFamily` interface with one supra-edge mode and `QYM` truncated
above by `1`, tied to the Wilson ensemble through `QYM` and `os_rp` alone.

DERIVED: `4` is the spacetime dimension in the permutation groups; in `hev`, `2 * k` is the even
extent and `2 ≤ k` is `4 ≤ N + 1`, and `2 ≤ N` is the smallest non-abelian rank; `1` in `N + 1` is
the lag arity offset; `0` is the boundary of the physical half-line in `hconf`, the limit point of
the `Tendsto` clauses, the level non-triviality compares against, and the lower bound asserted on
`q`. -/
theorem ym_existence_and_gap_of_junction (N : ℕ) (hev : ∃ k : ℕ, N + 1 = 2 * k ∧ 2 ≤ k)
    (hN : 2 ≤ N) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, μClampAt N β - κ₀YM < 0) ∧ (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d')) ∧
      (∃ (q : JYM → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (ymFamily N hev).Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(ymFamily N hev).c⌉₊ : ℝ) * (ymFamily N hev).B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((ymFamily N hev).actE g j) = q j) ∧
        (∀ σ j, q ((ymFamily N hev).actP σ j) = q j)) :=
  existence_and_gap_of_wilson (ym_wilson_of N hev hN hconf s P m Δ c hdom hfe hgap)

#print axioms ym_existence_and_gap_of_junction

end MassGap
