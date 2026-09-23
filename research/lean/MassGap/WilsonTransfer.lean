import Mathlib
import MassGap.LogConvex

/-!
# MassGap.WilsonTransfer — the lattice time shift as an operator on Wilson observables

The time translation `Transfer.TransferData` asks for, built on the Wilson measure, together with
the two of its four fields that hold for it and the exact reason the other two cannot be stated on
the slab algebra.

## The shift, and the identity everything rests on

`shiftConf τ U l = U (shiftLink τ l)` is one lattice step along `τ`, pulled back to configurations.
The identity the rest of the file uses is

    shiftConf τ U = reflConf τ c (reflConf τ (c + 1) U)          (`shiftConf_eq_reflConf_comp`)

at every reflection constant `c`: a one-step translation is the composite of the two site reflections
whose constants differ by one. On an axis link each reflection inverts the gauge variable, so the two
inversions cancel and the composite is a bare relabelling. Two consequences follow with no measure
theory beyond `Reflect`'s: invariance of the Gibbs expectation under the shift
(`expect_shift_invariant`) is `Reflect.expect_reflect_invariant` applied twice, and

    shiftConf τ (reflConf τ c (shiftConf τ U)) = reflConf τ c U  (`shiftConf_reflConf_shiftConf`)

is involutivity of the two reflections.

## Relation to the fields of `Transfer.TransferData`

* `T` — `shiftObs τ` is an `ℝ`-linear endomorphism of the observables and an algebra map
  (`shiftObs_one`, `shiftObs_mul`). It is carried on the full observable space.
* `T_symm` — `reflForm_shiftObs_symm` gives `⟨T F, G⟩ = ⟨F, T G⟩` for the concrete Gibbs reflection
  form `Transfer.reflForm N τ c β`, at every real `β`, every reflection constant and every pair of
  observables, with no measurability, boundedness or positivity hypothesis.
* `T_vac` — `shiftObs_one`: the constant observable is fixed by the shift, by `rfl`.
* `T_contract` — no statement of it appears in this file. Contractivity would be a Cauchy–Schwarz
  argument on a positive semidefinite form, and the form
  `ReflectionStrong.wilsonGibbsReflForm` carries is positive semidefinite on
  `LogConvex.localObs (blkS τ a m) (blkR τ a m)`, which the theorems in Part 6 show is not stable
  under the shift.

## The slab is not stable under the shift

`shiftLink_axis_leaves_slab` exhibits an axis link at level `m − 1`, which `mem_blkS_union_blkR`
admits, whose image one step along `τ` is at level `m`, which it refuses.
`shift_not_stable_on_slab` states that existentially. `shiftObs_mem` says where a shifted observable
does live: an observable reading `S ∪ R` becomes an observable reading the image of `S ∪ R` under
`shiftLink`.

The region a site reflection cuts out on a periodic lattice is a slab of width `m`, bounded above by
the second mirror plane, rather than a half-line. The shift permutes the `n` levels cyclically, so
the only subsets of levels stable under it are the empty one and all of them, while `blkS ∪ blkR`
omits the axis levels from `m` to `n − 1`.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.WilsonTransfer`.
-/

namespace MassGap.WilsonTransfer

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.CompactGauge
open MassGap.ActionSplit MassGap.LogConvex

/-! ## Part 1 — the shift on sites and links -/

section Geometry

variable {d n : ℕ} [NeZero n]

/-- A link moved one lattice step along `τ`: the direction component is unchanged, the base site
moves by `WilsonHypercubic.shift`.

DERIVED: the statement carries no numeral. The single step lives inside `shift`, which is where a
neighbouring site is defined. -/
def shiftLink (τ : Fin d) (l : Link d n) : Link d n := (l.1, shift τ l.2)

@[simp] theorem shiftLink_fst (τ : Fin d) (l : Link d n) : (shiftLink τ l).1 = l.1 := rfl

@[simp] theorem shiftLink_snd (τ : Fin d) (l : Link d n) : (shiftLink τ l).2 = shift τ l.2 := rfl

/-- Two site reflections whose constants differ by one compose to one step:
`reflSite τ (c + 1) (reflSite τ c x) = shift τ x`.

The coordinate along `τ` goes `x ↦ c - x ↦ (c + 1) - (c - x) = x + 1`; the other coordinates are
untouched by both reflections. `c` is arbitrary in `Fin n` and does not survive into the conclusion.

DERIVED: `1` is the gap between the two reflection constants, and it is the same `1` as the lattice
step it produces. -/
theorem reflSite_comp_succ (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ (c + 1) (reflSite τ c x) = shift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

/-- The same composite with the lower constant written as a predecessor:
`reflSite τ c (reflSite τ (c - 1) x) = shift τ x`.

This is the form needed for axis links, which `reflLink` reflects about `c - 1` rather than `c`.
Arithmetic in `Fin n`, so the predecessor wraps at `0`.

DERIVED: `1` is the gap between the two reflection constants, and the lattice step it produces. -/
theorem reflSite_comp_pred (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c (reflSite τ (c - 1) x) = shift τ x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

@[simp] theorem reflLink_fst (τ : Fin d) (c : Fin n) (l : Link d n) :
    (reflLink τ c l).1 = l.1 := rfl

/-- Two link reflections whose constants differ by one compose to one step:
`reflLink τ (c + 1) (reflLink τ c l) = shiftLink τ l`, for every link `l`.

Axis links reflect about the predecessor constant on both applications and land where the transverse
ones do, so one statement covers the whole link set with no case hypothesis on `l.1`.

DERIVED: `1` is the gap between the two reflection constants, and the lattice step it produces. -/
theorem reflLink_comp_succ (τ : Fin d) (c : Fin n) (l : Link d n) :
    reflLink τ (c + 1) (reflLink τ c l) = shiftLink τ l := by
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · have hc : c + 1 - 1 = c := by abel
    simp [reflLink, shiftLink, h, hc, reflSite_comp_pred]
  · simp [reflLink, shiftLink, h, reflSite_comp_succ]

end Geometry

/-! ## Part 2 — the shift on configurations, as a composite of two reflections -/

section Configs

variable {d n : ℕ} [NeZero n] {G : Type}

/-- A configuration moved one lattice step along `τ`, by pullback along `shiftLink τ`.

A relabelling only: unlike `reflConf` it applies no inverse on the axis links, because a translation
does not reverse the traversal of a link. `G` carries no structure here beyond being a type.

DERIVED: the statement carries no numeral. -/
def shiftConf (τ : Fin d) (U : Link d n → G) : Link d n → G := fun l => U (shiftLink τ l)

@[simp] theorem shiftConf_apply (τ : Fin d) (U : Link d n → G) (l : Link d n) :
    shiftConf τ U l = U (shiftLink τ l) := rfl

theorem measurable_shiftConf [MeasurableSpace G] (τ : Fin d) :
    Measurable (shiftConf (d := d) (n := n) (G := G) τ) :=
  measurable_pi_lambda _ (fun l => measurable_pi_apply (shiftLink τ l))

variable [Group G]

theorem reflConf_apply_axis (τ : Fin d) (c : Fin n) (U : Link d n → G) {l : Link d n}
    (h : l.1 = τ) : reflConf τ c U l = (U (reflLink τ c l))⁻¹ := by
  simp [reflConf, h]

theorem reflConf_apply_transverse (τ : Fin d) (c : Fin n) (U : Link d n → G) {l : Link d n}
    (h : l.1 ≠ τ) : reflConf τ c U l = U (reflLink τ c l) := by
  simp [reflConf, h]

/-- One step along `τ` is the composite of two configuration reflections one apart:
`shiftConf τ U = reflConf τ c (reflConf τ (c + 1) U)`, for every `c : Fin n`.

On an axis link each reflection inverts the gauge variable and the two inversions cancel, leaving a
relabelling; off the axis there is no inversion to cancel. `reflLink_comp_succ` supplies the
geometry. The constant `c` is universally quantified and does not appear on the left, so the
composite is one map rather than a `c`-indexed family. `G` is required to be a `Group` for the
inversions.

DERIVED: `1` is the gap between the two reflection constants, the same `1` as the lattice step it
produces. -/
theorem shiftConf_eq_reflConf_comp (τ : Fin d) (c : Fin n) (U : Link d n → G) :
    shiftConf τ U = reflConf τ c (reflConf τ (c + 1) U) := by
  funext l
  have hfst : (reflLink τ c l).1 = l.1 := rfl
  by_cases h : l.1 = τ
  · rw [reflConf_apply_axis τ c _ h,
      reflConf_apply_axis τ (c + 1) U (hfst.trans h), inv_inv, reflLink_comp_succ]
    rfl
  · rw [reflConf_apply_transverse τ c _ h,
      reflConf_apply_transverse τ (c + 1) U (hfst.trans_ne h), reflLink_comp_succ]
    rfl

/-- Stepping, reflecting and stepping again is reflecting:
`shiftConf τ (reflConf τ c (shiftConf τ U)) = reflConf τ c U`.

This is `Θ ∘ S = S⁻¹ ∘ Θ` written without an inverse. The proof rewrites each shift by
`shiftConf_eq_reflConf_comp` at the same constant `c` and cancels with `reflConf_involutive` at `c`
and at `c + 1`. It holds at every `c` and every configuration, with no hypothesis beyond `G` being a
group.

DERIVED: the statement carries no numeral. -/
theorem shiftConf_reflConf_shiftConf (τ : Fin d) (c : Fin n) (U : Link d n → G) :
    shiftConf τ (reflConf τ c (shiftConf τ U)) = reflConf τ c U := by
  have hinv : ∀ V : Link d n → G, reflConf τ c (reflConf τ c V) = V :=
    reflConf_involutive τ c
  have hinv' : ∀ V : Link d n → G, reflConf τ (c + 1) (reflConf τ (c + 1) V) = V :=
    reflConf_involutive τ (c + 1)
  rw [shiftConf_eq_reflConf_comp τ c (reflConf τ c (shiftConf τ U)),
    shiftConf_eq_reflConf_comp τ c U, hinv, hinv']

end Configs

/-! ## Part 3 — the Gibbs expectation is invariant under the shift -/

section Invariance

variable {d n : ℕ} [NeZero n]

/-- The Wilson Gibbs expectation is unchanged when an observable is composed with one lattice step:
`expect (fun U => O (shiftConf τ U)) = expect O`.

Holds at every gauge order `N`, every direction `τ`, every real `β` and every real-valued observable
`O`, with no measurability or boundedness hypothesis. The proof rewrites the shift as two reflections
(`shiftConf_eq_reflConf_comp`) and applies `Reflect.expect_reflect_invariant` twice; the reflection
constant it picks is immaterial, since the composite identity holds at every constant.

DERIVED: the statement carries no numeral. The gauge order, direction, coupling and observable are
all parameters, and the reflection constants appear in the proof rather than in the type. -/
theorem expect_shift_invariant (N : ℕ) (τ : Fin d) (β : ℝ)
    (O : (Link d n → MassGap.SUN.SU N) → ℝ) :
    (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β (fun U => O (shiftConf τ U))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O := by
  have hstep : (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O (shiftConf τ U))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => (fun V => O (reflConf τ (0 : Fin n) V)) (reflConf τ ((0 : Fin n) + 1) U)) :=
    MassGap.Transfer.expect_congr N β
      (fun U => by rw [shiftConf_eq_reflConf_comp τ (0 : Fin n) U])
  have h2 := MassGap.Reflect.expect_reflect_invariant N τ ((0 : Fin n) + 1) β
    (fun V => O (reflConf τ (0 : Fin n) V))
  have h1 := MassGap.Reflect.expect_reflect_invariant N τ (0 : Fin n) β O
  exact hstep.trans (h2.trans h1)

end Invariance

/-! ## Part 4 — the shift as a linear operator on observables

`shiftObs` is the `T` of `Transfer.TransferData`: an `ℝ`-linear endomorphism of the observables,
and an algebra map. It is stated on the full observable space; Part 6 gives a witness showing it is
not an endomorphism of the slab algebra.
-/

section Operator

variable {d n N : ℕ} [NeZero n]

/-- The time translation as an `ℝ`-linear endomorphism of the real observables on
`Link d n → SU N`: `shiftObs τ F = F ∘ shiftConf τ`.

Additivity and scalar multiplication both hold by `rfl`, since the map is a precomposition. The
domain and codomain are the full function space, with no measurability or locality condition.

DERIVED: the statement carries no numeral. -/
def shiftObs (τ : Fin d) :
    ((Link d n → MassGap.SUN.SU N) → ℝ) →ₗ[ℝ] ((Link d n → MassGap.SUN.SU N) → ℝ) where
  toFun F := fun U => F (shiftConf τ U)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shiftObs_apply (τ : Fin d) (F : (Link d n → MassGap.SUN.SU N) → ℝ)
    (U : Link d n → MassGap.SUN.SU N) : shiftObs τ F U = F (shiftConf τ U) := rfl

/-- `shiftObs τ` fixes the constant observable `fun _ => 1`, by `rfl`. This is the `T_vac` field of
`Transfer.TransferData`.

DERIVED: `1` is the constant observable's value, and is the only numeral in the statement. -/
theorem shiftObs_one (τ : Fin d) :
    shiftObs (n := n) (N := N) τ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := rfl

/-- `shiftObs τ` is multiplicative: the shift of a pointwise product is the product of the shifts,
by `rfl`. With `shiftObs_one` and linearity this makes it an algebra map on the full observable
space.

DERIVED: the statement carries no numeral. -/
theorem shiftObs_mul (τ : Fin d) (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    shiftObs τ (fun U => F U * G U) = (fun U => shiftObs τ F U * shiftObs τ G U) := rfl

/-- An observable in `localObs S R` lands in `localObs E ∅` after one step, provided `E` contains
the image of both `S` and `R` under `shiftLink τ`.

Measurability composes with `measurable_shiftConf`, the bound `C` carries over unchanged, and
locality transports because the shifted configuration reads `E` exactly where the original read
`S ∪ R`. The second block of the conclusion is empty: the two blocks merge into `E`, so the output
is not split into a reflected and unreflected part.

DERIVED: the statement carries no numeral; `∅` is the empty `Finset`, not a numeral. -/
theorem shiftObs_mem (τ : Fin d) {S R E : Finset (Link d n)}
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ localObs S R)
    (hS : ∀ l ∈ S, shiftLink τ l ∈ E) (hR : ∀ l ∈ R, shiftLink τ l ∈ E) :
    shiftObs τ F ∈ localObs E (∅ : Finset (Link d n)) := by
  obtain ⟨hFm, ⟨C, hFb⟩, hFl⟩ := hF
  refine mem_localObs.mpr ⟨hFm.comp (measurable_shiftConf τ), ⟨C, fun U => hFb _⟩, ?_⟩
  intro U V hUE _
  exact hFl _ _ (fun i hi => hUE _ (hS i hi)) (fun i hi => hUE _ (hR i hi))

end Operator

/-! ## Part 5 — `T_symm`: the shift is self-adjoint for the Wilson reflection form -/

section Symm

variable {d n N : ℕ} [NeZero n]

/-- `shiftObs τ` is self-adjoint for the Wilson Gibbs reflection form:
`reflForm N τ c β (shiftObs τ F) G = reflForm N τ c β F (shiftObs τ G)`.

This is the `T_symm` field of `Transfer.TransferData`, on the concrete form
`Transfer.reflForm N τ c β` that `ReflectionStrong.wilsonGibbsReflForm` carries. The two ingredients
are `expect_shift_invariant` and `shiftConf_reflConf_shiftConf`.

Scope: no hypothesis is imposed — it holds at every real `β`, every reflection constant, and every
pair of real-valued observables, with no measurability, boundedness or positivity. In particular
nothing here asserts that the form is positive semidefinite on these arguments.

DERIVED: the statement carries no numeral. -/
theorem reflForm_shiftObs_symm (N : ℕ) (τ : Fin d) (c : Fin n) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    MassGap.Transfer.reflForm N τ c β (shiftObs τ F) G
      = MassGap.Transfer.reflForm N τ c β F (shiftObs τ G) := by
  have hcancel : ∀ U : Link d n → MassGap.SUN.SU N,
      F (shiftConf τ (reflConf τ c (shiftConf τ U))) * G (shiftConf τ U)
        = F (reflConf τ c U) * G (shiftConf τ U) := by
    intro U
    rw [shiftConf_reflConf_shiftConf τ c U]
  have h := expect_shift_invariant N τ β (fun U => F (shiftConf τ (reflConf τ c U)) * G U)
  exact h.symm.trans (MassGap.Transfer.expect_congr N β hcancel)

end Symm

/-! ## Part 6 — the slab is not stable under the shift

An explicit link of `blkS ∪ blkR` whose image under one step lies outside it, and the existential
form of that fact.
-/

section Blocker

variable {d n : ℕ} [NeZero n]

/-- An axis link at level `m - 1` lies in `blkS τ a m ∪ blkR τ a m` and its image under
`shiftLink τ` does not.

`mem_blkS_union_blkR` admits an axis link exactly when its level is strictly below `m`, and
`lv_shift_axis` sends level `m - 1` to level `m`. The hypotheses are that the extent is even,
`n = 2 * m`, that `m` is positive, that the link is an axis link (`hl1 : l.1 = τ`), and that its
level is `m - 1`.

Scope: stated for the periodic torus `Link d n` at even extent; it says nothing about transverse
links, whose membership condition is different.

DERIVED: `2` is the factor in the evenness hypothesis `n = 2 * m`, which is what makes the slab half
the extent. `0` is the strict lower bound in `hm0 : 0 < m`, required so that `m - 1` is a level below
`m`. `1` is the single lattice step, appearing as the offset in `m - 1`, the highest axis level the
slab admits. All three are read off `mem_blkS_union_blkR` and the step, not chosen. -/
theorem shiftLink_axis_leaves_slab (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m)
    {l : Link d n} (hl1 : l.1 = τ) (hlv : lv a (l.2 τ) = m - 1) :
    l ∈ blkS τ a m ∪ blkR τ a m ∧ shiftLink τ l ∉ blkS τ a m ∪ blkR τ a m := by
  have hmn : m < n := by omega
  constructor
  · rw [mem_blkS_union_blkR, if_pos hl1, hlv]
    omega
  · rw [mem_blkS_union_blkR, if_pos (show (shiftLink τ l).1 = τ from hl1), shiftLink_snd,
      lv_shift_axis, hlv]
    have hs : m - 1 + 1 = m := by omega
    rw [hs, Nat.mod_eq_of_lt hmn]
    omega

/-- Some link of `blkS τ a m ∪ blkR τ a m` has its image under `shiftLink τ` outside that set, at
even extent `n = 2 * m` with `m` positive.

The witness is the axis link at level `m - 1` supplied by `shiftLink_axis_leaves_slab`. Together with
`shiftObs_mem`, which says the shifted observable reads the image of the block, this is the statement
that the block is not stable under the shift, so `shiftObs τ` is not an endomorphism of
`LogConvex.localObs (blkS τ a m) (blkR τ a m)`.

Scope: an existential about the link set. It is not a statement about observables, and it does not
assert that no other region is stable.

DERIVED: `2` is the factor in the evenness hypothesis `n = 2 * m`, making the slab half the extent.
`0` is the strict lower bound in `hm0 : 0 < m`. Both come from `shiftLink_axis_leaves_slab`'s own
hypotheses. -/
theorem shift_not_stable_on_slab (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m) :
    ∃ l ∈ blkS τ a m ∪ blkR τ a m, shiftLink τ l ∉ blkS τ a m ∪ blkR τ a m := by
  have hlt : m - 1 < n := by omega
  refine ⟨(τ, fun _ => a + fcast n (m - 1)), ?_, ?_⟩
  · exact (shiftLink_axis_leaves_slab τ a m hm hm0 (l := (τ, fun _ => a + fcast n (m - 1)))
      rfl (lv_add_fcast a (m - 1) hlt)).1
  · exact (shiftLink_axis_leaves_slab τ a m hm hm0 (l := (τ, fun _ => a + fcast n (m - 1)))
      rfl (lv_add_fcast a (m - 1) hlt)).2

end Blocker

#print axioms shiftLink
#print axioms reflSite_comp_succ
#print axioms reflSite_comp_pred
#print axioms reflLink_comp_succ
#print axioms shiftConf
#print axioms measurable_shiftConf
#print axioms reflConf_apply_axis
#print axioms reflConf_apply_transverse
#print axioms shiftConf_eq_reflConf_comp
#print axioms shiftConf_reflConf_shiftConf
#print axioms expect_shift_invariant
#print axioms shiftObs
#print axioms shiftObs_one
#print axioms shiftObs_mul
#print axioms shiftObs_mem
#print axioms reflForm_shiftObs_symm
#print axioms shiftLink_axis_leaves_slab
#print axioms shift_not_stable_on_slab

end MassGap.WilsonTransfer
