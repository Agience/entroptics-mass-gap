import Mathlib
import MassGap.WilsonHypercubic
import MassGap.ReflectionPositivity

/-!
# MassGap.Reflect — the coordinate reflection `x_τ ↦ c − x_τ` of the periodic hypercubic lattice

`WilsonHypercubic` supplies the axis permutations of the hypercubic lattice. This file supplies the
reflection in one coordinate, on sites, links, plaquettes and configurations, and proves that the
Wilson action and the Gibbs expectation are invariant under it.

## How a reflection differs from an axis permutation

* **The base site of a `τ`-link moves by one step.** The link `U_τ(x)` spans `[x_τ, x_τ+1]`; its
  mirror spans `[c−x_τ−1, c−x_τ]`, based at `c−1−x_τ`. So `reflLink` acts on `τ`-links through the
  constant `c−1` and on every other link through `c`.
* **A `τ`-link is traversed backwards by the mirrored loop**, so `reflConf` inverts the gauge
  variable on those links. This is the `†` of the Osterwalder–Seiler time reflection, and it is why
  a reflection is not of the form `LatticeGauge.Symmetry`, whose `onLink` is a bare permutation.

The mirrored boundary word is therefore a cyclic rotation of the image plaquette's word rather than
that word itself (`bd_reflect_axis_fst` rotates by `3`, `bd_reflect_axis_snd` by `1`,
`bd_reflect_transverse` not at all), so the holonomies agree only up to conjugation
(`hol_reflConf`). `reflect_action_invariant` is proved from that conjugation together with
`WilsonAction.wilsonDensity_conj`, not from `WilsonLattice.wilsonSymmetry`.

## Contents

`reflSite`, `reflLink`, `reflPlaq`, `reflConf` with their involutivity; the four site identities the
geometry rests on; the boundary-word transformation in its three non-degenerate shapes; the holonomy
conjugation; invariance of the Wilson action; and, over a compact gauge group, invariance of the
Gibbs expectation (`expect_reflect_invariant`), routed through
`LatticeGauge.System.expect_invariant_of_mp`.

The character expansion is not here. `ReflectionPositivity.reflection_positive_of_expansion` consumes
a paired expansion of the cross term with nonnegative coefficients; no declaration below produces
one. What this file provides is the geometry such an expansion would be stated over.

`c` is a `Fin n`, and the subtraction is `Fin n`'s own modular one, so every statement is on the
periodic lattice.

Build: `python code/lean_build.py build MassGap.Reflect`.
-/

namespace MassGap.Reflect

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonHypercubic

variable {d n : ℕ}

/-! ### The reflection on sites -/

/-- Reflection of one coordinate: `x_τ ↦ c − x_τ`, every other coordinate fixed, by
`Function.update`.

`c` is the reflection constant, not a position: the fixed set of `x ↦ c − x` on `Fin n` is where
`2x = c`, so the plane sits at `c/2` and the family of reflections in direction `τ` is swept by `c`.
Carrying `c` rather than a plane makes the two hyperplanes of an even-extent lattice (`c` even and
`c` odd) the same construction at two values.

DERIVED: no numeral. `c` and `τ` are the caller's; the subtraction is `Fin n`'s own, which is
modular, so periodicity is inherited rather than imposed. -/
def reflSite [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) : Site d n :=
  Function.update x τ (c - x τ)

/-- The reflected site's `τ` coordinate is `c - x τ`, by `Function.update_self`.

DERIVED: no numeral. -/
@[simp] theorem reflSite_axis [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c x τ = c - x τ := by
  simp [reflSite]

/-- Every coordinate other than `τ` is fixed by the reflection, by `Function.update_of_ne`.

DERIVED: no numeral. -/
theorem reflSite_of_ne [NeZero n] {τ j : Fin d} (h : j ≠ τ) (c : Fin n) (x : Site d n) :
    reflSite τ c x j = x j := by
  simp [reflSite, Function.update_of_ne h]

/-- `reflSite τ c` is an involution on `Site d n`, from `c − (c − a) = a` in `Fin n` on the `τ`
coordinate and from the update being trivial on the others.

DERIVED: no numeral. -/
theorem reflSite_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflSite (d := d) (n := n) τ c) := by
  intro x
  funext j
  by_cases h : j = τ
  · subst h
    simp [reflSite, sub_sub_cancel]
  · simp [reflSite, Function.update_of_ne h]

/-- A step in a direction `ν ≠ τ` commutes with the reflection:
`reflSite τ c (shift ν x) = shift ν (reflSite τ c x)`. The two updates are at different coordinates.

DERIVED: no numeral. -/
theorem reflSite_shift_of_ne [NeZero n] {τ ν : Fin d} (h : ν ≠ τ) (c : Fin n) (x : Site d n) :
    reflSite τ c (shift ν x) = shift ν (reflSite τ c x) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    have h' : j ≠ ν := fun hc => h (hc ▸ rfl)
    simp [reflSite, shift, Function.update_of_ne (Ne.symm h)]
  · by_cases hν : j = ν
    · subst hν
      simp [reflSite, shift, Function.update_of_ne hj]
    · simp [reflSite, shift, Function.update_of_ne hj, Function.update_of_ne hν]

/-- A step along the reflection axis shifts the reflection constant by one:
`reflSite τ c (shift τ x) = reflSite τ (c − 1) x`. Reflecting the far end of a `τ`-link is
reflecting its near end about the neighbouring constant, and this is what makes `τ`-links
base-shifted in `reflLink`.

DERIVED: the `1` is one lattice step, the same `1` as in `WilsonHypercubic.shift`. -/
theorem reflSite_shift_axis [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c (shift τ x) = reflSite τ (c - 1) x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

/-- The converse rewriting: `shift τ (reflSite τ (c − 1) x) = reflSite τ c x`. The same identity as
`reflSite_shift_axis` with the shift on the other side, used to rewrite in the opposite direction.

DERIVED: the `1` is one lattice step, the same `1` as in `WilsonHypercubic.shift`. -/
theorem shift_reflSite_axis [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    shift τ (reflSite τ (c - 1) x) = reflSite τ c x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

/-! ### The reflection on links and plaquettes -/

/-- Reflection of a link, keeping its direction and reflecting its base site: through `c − 1` when
the direction is `τ`, through `c` otherwise. A `τ`-link spans `[x_τ, x_τ+1]`, so its mirror spans
`[c−1−x_τ, c−x_τ]`, based at `c−1−x_τ`. That base shift is the whole difference between a reflection
and an axis permutation on the link set.

DERIVED: the `1` is the length of a link in lattice steps, the offset between a link's two ends. The
`1` and `2` in `l.1` and `l.2` are the pair's projections, not numerals. -/
def reflLink [NeZero n] (τ : Fin d) (c : Fin n) (l : Link d n) : Link d n :=
  (l.1, if l.1 = τ then reflSite τ (c - 1) l.2 else reflSite τ c l.2)

/-- `reflLink τ c` is an involution on `Link d n`, by cases on whether the direction is `τ` and
`reflSite_involutive` at the matching constant.

DERIVED: no numeral. -/
theorem reflLink_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflLink (d := d) (n := n) τ c) := by
  intro l
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp [reflLink, h, reflSite_involutive τ (c - 1) x]
  · simp [reflLink, h, reflSite_involutive τ c x]

/-- `reflLink τ c` packaged as an `Equiv.Perm (Link d n)` via `Function.Involutive.toPerm`, so it
can be summed over with `Equiv.sum_comp`.

DERIVED: no numeral. -/
def reflLinkPerm [NeZero n] (τ : Fin d) (c : Fin n) : Equiv.Perm (Link d n) :=
  (reflLink_involutive (d := d) (n := n) τ c).toPerm _

/-- `reflLinkPerm τ c l = reflLink τ c l`, by `rfl`.

DERIVED: no numeral. -/
@[simp] theorem reflLinkPerm_apply [NeZero n] (τ : Fin d) (c : Fin n) (l : Link d n) :
    reflLinkPerm τ c l = reflLink τ c l := rfl

/-- Reflection of a plaquette. A plaquette whose plane misses the axis keeps its plane and moves its
corner through `c`; one whose plane contains the axis has its loop traversed the other way by the
mirror, and `WilsonHypercubic.bd` writes a reversed loop by swapping the two spanning directions, so
the image plane is the transposed pair based at the corner reflected through `c − 1`.

DERIVED: the `1` is the link-length offset of `reflLink`, for the same reason. The `1`s and `2`s in
`q.1.1`, `q.1.2` and `q.2` are projections of the nested pair, not numerals. -/
def reflPlaq [NeZero n] (τ : Fin d) (c : Fin n) (q : Plaq d n) : Plaq d n :=
  if q.1.1 = τ then ((q.1.2, τ), reflSite τ (c - 1) q.2)
  else if q.1.2 = τ then ((τ, q.1.1), reflSite τ (c - 1) q.2)
  else ((q.1.1, q.1.2), reflSite τ c q.2)

/-- `reflPlaq τ c` is an involution on `Plaq d n`. Four cases on which of the two spanning
directions is `τ`, including the degenerate one where both are; in each, `reflSite_involutive`
applies at the matching constant and the direction pair returns to its original order.

DERIVED: no numeral. -/
theorem reflPlaq_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflPlaq (d := d) (n := n) τ c) := by
  intro q
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  by_cases hμ : μ = τ
  · subst hμ
    by_cases hν : ν = μ
    · subst hν
      simp [reflPlaq, reflSite_involutive ν (c - 1) x]
    · simp [reflPlaq, hν, reflSite_involutive μ (c - 1) x]
  · by_cases hν : ν = τ
    · subst hν
      simp [reflPlaq, hμ, reflSite_involutive ν (c - 1) x]
    · simp [reflPlaq, hμ, hν, reflSite_involutive τ c x]

/-- `reflPlaq τ c` packaged as an `Equiv.Perm (Plaq d n)`. This is what lets
`reflect_action_invariant` reindex the sum over plaquettes with `Equiv.sum_comp`.

DERIVED: no numeral. -/
def reflPlaqPerm [NeZero n] (τ : Fin d) (c : Fin n) : Equiv.Perm (Plaq d n) :=
  (reflPlaq_involutive (d := d) (n := n) τ c).toPerm _

/-- `reflPlaqPerm τ c q = reflPlaq τ c q`, by `rfl`.

DERIVED: no numeral. -/
@[simp] theorem reflPlaqPerm_apply [NeZero n] (τ : Fin d) (c : Fin n) (q : Plaq d n) :
    reflPlaqPerm τ c q = reflPlaq τ c q := rfl

/-! ### The reflection on configurations, dagger included -/

variable {G : Type} [Group G]

/-- The reflection acting on a gauge-field configuration: off the axis a relabelling by `reflLink`,
on the axis a relabelling followed by inversion, because the mirror traverses a `τ`-link the other
way. The inversion is the `†` of the Osterwalder–Seiler time reflection, and is why a reflection is
not a `LatticeGauge.Symmetry`, whose `onLink` is a bare permutation of links.

`G` need only be a `Group`; no topology or measure is required for this definition.

DERIVED: no numeral. The `1` in `l.1` is the pair's first projection, not a numeral; the only data is
the caller's `τ` and `c`. -/
def reflConf [NeZero n] (τ : Fin d) (c : Fin n) (U : Link d n → G) : Link d n → G :=
  fun l => if l.1 = τ then (U (reflLink τ c l))⁻¹ else U (reflLink τ c l)

/-- `reflConf τ c` is an involution on configurations. The direction of a link is unchanged by
`reflLink`, so the same branch is taken twice; on the axis the two inversions cancel by `inv_inv`,
and off it `reflLink_involutive` closes it.

DERIVED: no numeral. -/
theorem reflConf_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflConf (d := d) (n := n) (G := G) τ c) := by
  intro U
  funext l
  have hfst : (reflLink τ c l).1 = l.1 := rfl
  by_cases h : l.1 = τ
  · simp only [reflConf, hfst, if_pos h, reflLink_involutive τ c l, inv_inv]
  · simp only [reflConf, hfst, if_neg h, reflLink_involutive τ c l]

/-! ### The boundary word under reflection -/

/-- The mirrored boundary word: each link is carried by `reflLink`, and the orientation bit of a
`τ`-link is flipped. The bit flip here and `reflConf`'s inversion are two readings of the same
reversal.

DERIVED: no numeral. The `1` and `2` in `lo.1`, `lo.1.1` and `lo.2` are projections, not numerals. -/
def reflWord [NeZero n] (τ : Fin d) (c : Fin n) (w : List (Link d n × Bool)) :
    List (Link d n × Bool) :=
  w.map (fun lo => (reflLink τ c lo.1, if lo.1.1 = τ then !lo.2 else lo.2))

/-- A plaquette whose two spanning directions both differ from `τ` keeps its boundary word:
`reflWord τ c (bd ((μ, ν), x)) = bd (reflPlaq τ c ((μ, ν), x))`, with no rotation. No link of its
boundary runs along the axis, so nothing is reversed and nothing is base-shifted.

DERIVED: no numeral. -/
theorem bd_reflect_transverse [NeZero n] (τ : Fin d) (c : Fin n) {μ ν : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (x : Site d n) :
    reflWord τ c (bd ((μ, ν), x)) = bd (reflPlaq τ c ((μ, ν), x)) := by
  simp only [reflWord, bd, reflPlaq, reflLink, reflSite_shift_of_ne hμ, reflSite_shift_of_ne hν,
    hμ, hν, if_false, List.map_cons, List.map_nil]

/-- A plaquette whose FIRST spanning direction is `τ`: the mirrored word is the image plaquette's
own word rotated by `3`, i.e. the last of the four letters brought to the front. So the two words
have the same letters in a rotated order, and the holonomies agree only up to conjugation.

DERIVED: `3` is the rotation, the index of the last letter of a four-letter plaquette word, which is
what brings it to the front. -/
theorem bd_reflect_axis_fst [NeZero n] (τ : Fin d) (c : Fin n) {ν : Fin d}
    (hν : ν ≠ τ) (x : Site d n) :
    reflWord τ c (bd ((τ, ν), x)) = (bd (reflPlaq τ c ((τ, ν), x))).rotate 3 := by
  simp only [reflWord, bd, reflPlaq, reflLink, hν, if_false, if_true,
    reflSite_shift_of_ne hν, reflSite_shift_axis, ← shift_reflSite_axis τ c x,
    List.map_cons, List.map_nil]
  rfl

/-- A plaquette whose SECOND spanning direction is `τ`: the mirrored word is the image plaquette's
word rotated by `1`, the other direction from `bd_reflect_axis_fst`.

DERIVED: `1` is the rotation, one place, which is the inverse of `bd_reflect_axis_fst`'s `3` on a
four-letter word. -/
theorem bd_reflect_axis_snd [NeZero n] (τ : Fin d) (c : Fin n) {μ : Fin d}
    (hμ : μ ≠ τ) (x : Site d n) :
    reflWord τ c (bd ((μ, τ), x)) = (bd (reflPlaq τ c ((μ, τ), x))).rotate 1 := by
  simp only [reflWord, bd, reflPlaq, reflLink, hμ, if_false, if_true,
    reflSite_shift_of_ne hμ, reflSite_shift_axis, ← shift_reflSite_axis τ c x,
    List.map_cons, List.map_nil]
  rfl

/-! ### The holonomy, and the action -/

/-- The plaquette holonomy of `WilsonHypercubic.bd` written out as the four-factor product
`V(μ,x) · V(ν, x+μ̂) · V(μ, x+ν̂)⁻¹ · V(ν,x)⁻¹`, by `simp [wilsonHol, bd]`.

DERIVED: no numeral. The `1`s and `2`s in `q.1.1`, `q.1.2` and `q.2` are projections of the nested
pair, not numerals. -/
theorem hol_bd [NeZero n] (q : Plaq d n) (V : Link d n → G) :
    wilsonHol (bd (d := d) (n := n)) q V
      = V (q.1.1, q.2) * (V (q.1.2, shift q.1.1 q.2)
          * ((V (q.1.1, shift q.1.2 q.2))⁻¹ * (V (q.1.2, q.2))⁻¹)) := by
  simp [wilsonHol, bd]

/-- The mirrored holonomy is conjugate to the image plaquette's holonomy: there is a `g` with
`wilsonHol bd q (reflConf τ c U) = g · wilsonHol bd (reflPlaq τ c q) U · g⁻¹`. Conjugate, not equal,
because the mirrored word is a cyclic rotation of the image word (`bd_reflect_axis_fst`,
`bd_reflect_axis_snd`) and a rotated ordered product is a conjugated one. The conjugator is exhibited
in each of the four cases: `1` where both directions miss the axis and where the plaquette is
degenerate, and an inverse link variable in the two axis cases.

This is the point at which a reflection stops being a `LatticeGauge.Symmetry`. It is enough for
`reflect_action_invariant`, because `WilsonAction.wilsonDensity` is a class function.

DERIVED: no numeral. -/
theorem hol_reflConf [NeZero n] (τ : Fin d) (c : Fin n) (q : Plaq d n) (U : Link d n → G) :
    ∃ g : G, wilsonHol (bd (d := d) (n := n)) q (reflConf τ c U)
      = g * wilsonHol (bd (d := d) (n := n)) (reflPlaq τ c q) U * g⁻¹ := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  by_cases hμ : μ = τ
  · subst hμ
    by_cases hν : ν = μ
    · -- both directions are the axis: a degenerate plaquette, holonomy `1` on either side
      subst hν
      refine ⟨1, ?_⟩
      rw [hol_bd, hol_bd]
      simp only [reflPlaq, reflConf, reflLink, if_true]
      group
    · refine ⟨(U (μ, reflSite μ (c - 1) x))⁻¹, ?_⟩
      rw [hol_bd, hol_bd]
      simp only [reflPlaq, reflConf, reflLink, hν, if_false, if_true,
        reflSite_shift_of_ne hν, reflSite_shift_axis, ← shift_reflSite_axis μ c x]
      group
  · by_cases hν : ν = τ
    · subst hν
      refine ⟨(U (ν, reflSite ν (c - 1) x))⁻¹, ?_⟩
      rw [hol_bd, hol_bd]
      simp only [reflPlaq, reflConf, reflLink, hμ, if_false, if_true,
        reflSite_shift_of_ne hμ, reflSite_shift_axis, ← shift_reflSite_axis ν c x]
      group
    · refine ⟨1, ?_⟩
      rw [hol_bd, hol_bd]
      simp only [reflPlaq, reflConf, reflLink, hμ, hν, if_false,
        reflSite_shift_of_ne hμ, reflSite_shift_of_ne hν]
      group

/-! ### The Wilson action is invariant under the reflection -/

open MassGap.WilsonAction in
/-- `(sysWilson N d n).action (reflConf τ c U) = (sysWilson N d n).action U`, for every `N`, every
reflection axis `τ` and constant `c`, and every configuration. Termwise, `hol_reflConf` replaces the
mirrored holonomy by a conjugate of the image plaquette's and `WilsonAction.wilsonDensity_conj`
discards the conjugator; `Equiv.sum_comp` at `reflPlaqPerm` then reindexes the sum over plaquettes.

It does not go through `WilsonLattice.wilsonSymmetry`, whose hypothesis asks for equality of boundary
words rather than conjugacy of holonomies.

DERIVED: no numeral. -/
theorem reflect_action_invariant (N : ℕ) [NeZero n] (τ : Fin d) (c : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action (reflConf τ c U) = (sysWilson N d n).action U := by
  have hact : ∀ V : Link d n → MassGap.SUN.SU N,
      (sysWilson N d n).action V
        = ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q V) := fun _ => rfl
  rw [hact, hact]
  calc ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ c U))
      = ∑ q : Plaq d n,
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) (reflPlaqPerm τ c q) U) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        obtain ⟨g, hg⟩ := hol_reflConf τ c q U
        simp only [reflPlaqPerm_apply]
        rw [hg, wilsonDensity_conj]
    _ = ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) :=
        Equiv.sum_comp (reflPlaqPerm τ c)
          (fun q => wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U))

/-! ### The reflection preserves the gauge measure, dagger and all -/

open MeasureTheory MassGap.CompactGauge MassGap.ReflectionPositivity

/-- The probability Haar measure of a compact group is invariant under inversion. Stated for any
compact, nonempty topological group with a Borel structure, so it covers the non-abelian `SU(N)`,
which `Measure.IsHaarMeasure.isInvInvariant_of_regular` does not.

The proof uses unimodularity: `μ.inv` is left-invariant because `μ` is right-invariant
(`CompactGauge.isMulRightInvariant_probHaar`), so by
`Measure.isMulInvariant_eq_smul_of_compactSpace` it is a Haar multiple of `μ`, and evaluating both at
`univ` forces the scalar factor to be one.

This is what `reflConf`'s inversion needs of the measure.

DERIVED: no numeral. The unit Haar scalar factor is a step of the proof, not part of the
statement. -/
instance isInvInvariant_probHaar (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] :
    (probHaar G).IsInvInvariant := by
  haveI hprob : IsProbabilityMeasure ((probHaar G).inv) :=
    ⟨by rw [Measure.inv_apply, Set.inv_univ, measure_univ]⟩
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ((probHaar G).inv) (probHaar G)
  have hc : Measure.haarScalarFactor ((probHaar G).inv) (probHaar G) = 1 := by
    have h1 := congrArg (fun m : Measure G => m Set.univ) h
    simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at h1
    exact_mod_cast h1.symm
  exact ⟨by rw [h, hc, one_smul]⟩

variable {N : ℕ}

/-- The inversion half of the reflection on its own: invert the gauge variable on every link running
along `τ`, leave the rest alone. Composed with `ReflectionPositivity.relabel (reflLinkPerm τ c)` it
is `reflConf`, which is what lets the measure argument be made coordinatewise.

DERIVED: no numeral. The `1` in `l.1` is the pair's first projection, not a numeral. -/
def daggerAxis [NeZero n] (τ : Fin d) (V : Link d n → MassGap.SUN.SU N) :
    Link d n → MassGap.SUN.SU N :=
  fun l => if l.1 = τ then (V l)⁻¹ else V l

/-- `daggerAxis τ` preserves the product Haar measure `vol (Link d n) N`. Coordinatewise: each
coordinate map is either the identity or inversion, measure-preserving by `MeasurePreserving.id` and
`Measure.measurePreserving_inv` (available through `isInvInvariant_probHaar`), and
`Measure.pi_map_pi` assembles them.

DERIVED: no numeral. -/
theorem daggerAxis_measurePreserving [NeZero n] (τ : Fin d) :
    MeasurePreserving (daggerAxis (d := d) (n := n) (N := N) τ)
      (vol (Link d n) N) (vol (Link d n) N) := by
  have hf : ∀ l : Link d n, MeasurePreserving
      (fun u : MassGap.SUN.SU N => if l.1 = τ then u⁻¹ else u)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
    intro l
    by_cases h : l.1 = τ
    · simpa [h] using Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
    · have hid : (fun u : MassGap.SUN.SU N => if l.1 = τ then u⁻¹ else u) = id := by
        funext u; simp [h]
      rw [hid]
      exact MeasurePreserving.id _
  refine ⟨measurable_pi_lambda _ (fun l => (hf l).measurable.comp (measurable_pi_apply l)), ?_⟩
  show Measure.map (fun (V : Link d n → MassGap.SUN.SU N) (l : Link d n) =>
      (fun u : MassGap.SUN.SU N => if l.1 = τ then u⁻¹ else u) (V l)) (vol (Link d n) N)
      = vol (Link d n) N
  rw [Measure.pi_map_pi (fun l => (hf l).aemeasurable)]
  exact congrArg Measure.pi (funext fun l => (hf l).map_eq)

/-- `reflConf τ c` preserves the product Haar measure over links. It factors by `rfl` as
`daggerAxis τ ∘ relabel (reflLinkPerm τ c)`; the relabelling is measure-preserving because the
factors are identical (`ReflectionPositivity.relabel_measurePreserving`) and the inversion by
`daggerAxis_measurePreserving`.

DERIVED: no numeral. -/
theorem reflConf_measurePreserving [NeZero n] (τ : Fin d) (c : Fin n) :
    MeasurePreserving (reflConf (G := MassGap.SUN.SU N) τ c)
      (vol (Link d n) N) (vol (Link d n) N) := by
  have hcomp : reflConf (G := MassGap.SUN.SU N) (d := d) (n := n) τ c
      = (daggerAxis (N := N) τ) ∘ (relabel (N := N) (reflLinkPerm τ c)) := by
    funext U l
    rfl
  rw [hcomp]
  exact (daggerAxis_measurePreserving τ).comp (relabel_measurePreserving (reflLinkPerm τ c))

/-- `reflConf τ c` as a measurable equivalence of configuration space, with itself as inverse on
both sides (`reflConf_involutive`) and measurability from `reflConf_measurePreserving`. This is the
shape `LatticeGauge.System.expect_invariant_of_mp` takes.

DERIVED: no numeral. -/
noncomputable def reflConfEquiv [NeZero n] (τ : Fin d) (c : Fin n) :
    (Link d n → MassGap.SUN.SU N) ≃ᵐ (Link d n → MassGap.SUN.SU N) where
  toFun := reflConf τ c
  invFun := reflConf τ c
  left_inv := reflConf_involutive τ c
  right_inv := reflConf_involutive τ c
  measurable_toFun := (reflConf_measurePreserving (N := N) τ c).measurable
  measurable_invFun := (reflConf_measurePreserving (N := N) τ c).measurable

/-- The Gibbs expectation of the `d`-dimensional `SU(N)` Wilson system is unchanged by precomposing
an observable with the reflection:
`expect … (fun U => O (reflConf τ c U)) = expect … O`, for every real `β` and every
`O : (Link d n → SU N) → ℝ`, with no integrability or measurability hypothesis on `O`.

It is `LatticeGauge.System.expect_invariant_of_mp` at `reflConfEquiv`, whose two hypotheses are the
halves proved above: the measure is preserved (`reflConf_measurePreserving`) and the Boltzmann weight
is unchanged (`reflect_action_invariant`). It does not go through `Symmetry`, which cannot carry the
inversion.

DERIVED: no numeral. -/
theorem expect_reflect_invariant (N : ℕ) [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (O : (Link d n → MassGap.SUN.SU N) → ℝ) :
    (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β (fun U => O (reflConf τ c U))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O :=
  System.expect_invariant_of_mp (sysWilson N d n) (probHaar (MassGap.SUN.SU N)) β O
    (reflConfEquiv τ c) (reflConf_measurePreserving τ c)
    (fun U => by
      show (sysWilson N d n).boltz β (reflConf τ c U) = (sysWilson N d n).boltz β U
      unfold System.boltz
      rw [reflect_action_invariant])

#print axioms reflSite_involutive
#print axioms reflLink_involutive
#print axioms reflPlaq_involutive
#print axioms reflConf_involutive
#print axioms bd_reflect_transverse
#print axioms bd_reflect_axis_fst
#print axioms bd_reflect_axis_snd
#print axioms hol_reflConf
#print axioms reflect_action_invariant
#print axioms isInvInvariant_probHaar
#print axioms daggerAxis_measurePreserving
#print axioms reflConf_measurePreserving
#print axioms expect_reflect_invariant

end MassGap.Reflect
