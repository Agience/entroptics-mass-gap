import Mathlib
import MassGap.WilsonHypercubic
import MassGap.ReflectionPositivity

/-!
# MassGap.Reflect — the coordinate REFLECTION of the periodic hypercubic lattice

`WilsonHypercubic` supplies the axis PERMUTATIONS of the hypercubic lattice: relabel direction `μ`
as `e μ`, carry the site coordinates with it, and `wilsonSymmetry` turns it into a `Symmetry` of the
gauge system. This file supplies the other half of the lattice's discrete Euclidean group — the
REFLECTION `x_τ ↦ c − x_τ` in one coordinate — because that is the map Osterwalder–Seiler reflection
positivity is stated about and the one thing the tree could not write down.

## Why a reflection is not an axis permutation, and what has to change

An axis permutation carries a link to a link and leaves the traversal direction alone, so
`wilsonSymmetry`'s hypothesis — the boundary word of the permuted plaquette is the relabelled
boundary word, ORDER AND ORIENTATION INTACT — is available. A reflection in direction `τ` is not
like that, in two ways, and both are forced:

* **The base site of a `τ`-link moves by one step.** The link `U_τ(x)` spans `[x_τ, x_τ+1]`; its
  mirror image spans `[c−x_τ−1, c−x_τ]`, whose base is `c−1−x_τ`. So the reflection acts on
  `τ`-links through the constant `c−1` and on every other link through `c` (`reflLink`).
* **A `τ`-link is traversed BACKWARDS by the mirrored loop**, so the reflection carries a DAGGER on
  those links: `U_τ(x) ↦ U_τ(c−1−x_τ)⁻¹` (`reflConf`). Without it the action is not invariant — the
  plaquette holonomy `A·B·C⁻¹·D⁻¹` would go to `A·B·C⁻¹·D⁻¹` with the wrong two letters inverted,
  which is not conjugate to any plaquette's holonomy. This is exactly the `†` that appears in the
  Osterwalder–Seiler time reflection, and it is why a reflection is NOT of the form
  `LatticeGauge.Symmetry` (whose `onLink` is a bare permutation of the links).

The consequence worth stating plainly: the mirrored boundary word is a CYCLIC ROTATION of the image
plaquette's own word, not that word itself, so the holonomies agree only up to CONJUGATION
(`hol_reflConf`). That is enough, because the Wilson density is a class function
(`WilsonAction.wilsonDensity_conj`), and it is the reason `reflect_action_invariant` is proved here
rather than obtained from `wilsonSymmetry`.

## What is here and what is not

`reflSite`/`reflLink`/`reflPlaq`/`reflConf` with their involutivity, the four site identities the
geometry rests on, the boundary-word transformation in each of its three non-degenerate shapes
(`bd_reflect_*`), the holonomy conjugation, the invariance of the Wilson action, and — over a compact
gauge group — the invariance of the Gibbs expectation (`expect_reflect_invariant`).

What is NOT here is the character expansion. `ReflectionPositivity.reflection_positive_of_expansion`
consumes a paired expansion of the cross term with nonnegative coefficients; producing it is the
cited half of Osterwalder–Seiler and nothing below attempts it. This file supplies the geometry that
expansion would be stated over, which is what the tree was missing.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.Reflect`.
-/

namespace MassGap.Reflect

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonHypercubic

variable {d n : ℕ}

/-! ### The reflection on sites -/

/-- **Reflection of one coordinate**: `x_τ ↦ c − x_τ`, every other coordinate fixed.

`c` is the reflection constant, not a position: the fixed set of `x ↦ c − x` on `Fin n` is where
`2x = c`, so the plane sits at `c/2` and the whole one-parameter family of reflections in direction
`τ` is swept by `c`. Carrying `c` rather than a plane is what makes the two hyperplanes of an
even-extent lattice (`c` even and `c` odd) the same construction at two values.

DERIVED: no literal appears. `c` and `τ` are the caller's; the subtraction is `Fin n`'s own, which is
modular, so periodicity is inherited rather than imposed. -/
def reflSite [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) : Site d n :=
  Function.update x τ (c - x τ)

@[simp] theorem reflSite_axis [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c x τ = c - x τ := by
  simp [reflSite]

theorem reflSite_of_ne [NeZero n] {τ j : Fin d} (h : j ≠ τ) (c : Fin n) (x : Site d n) :
    reflSite τ c x j = x j := by
  simp [reflSite, Function.update_of_ne h]

/-- **The reflection is an involution on sites** — `c − (c − a) = a`. -/
theorem reflSite_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflSite (d := d) (n := n) τ c) := by
  intro x
  funext j
  by_cases h : j = τ
  · subst h
    simp [reflSite, sub_sub_cancel]
  · simp [reflSite, Function.update_of_ne h]

/-- **A step in a direction the reflection does not touch commutes with it.** -/
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

/-- **A step ALONG the reflection axis shifts the reflection constant by one.** This is the identity
that makes `τ`-links base-shifted: reflecting the far end of a `τ`-link is reflecting its near end
about the neighbouring constant.

DERIVED: the `1` is one lattice step, the same `1` as in `WilsonHypercubic.shift`. -/
theorem reflSite_shift_axis [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c (shift τ x) = reflSite τ (c - 1) x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

/-- **And stepping back along the axis undoes it.**

DERIVED: the `1` is one lattice step. -/
theorem shift_reflSite_axis [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    shift τ (reflSite τ (c - 1) x) = reflSite τ c x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [reflSite, shift, Function.update_self]
    abel
  · simp [reflSite, shift, Function.update_of_ne hj]

/-! ### The reflection on links and plaquettes -/

/-- **Reflection of a link.** A link in direction `τ` spans `[x_τ, x_τ+1]`, so its mirror image spans
`[c−1−x_τ, c−x_τ]` and is based at `c−1−x_τ`; a link in any other direction is based at the mirror
of its own base. That base shift by one is the whole difference between a reflection and an axis
permutation on the link set, and it is not a choice.

DERIVED: the `1` is the length of a link in lattice steps — the offset between a link's two ends. -/
def reflLink [NeZero n] (τ : Fin d) (c : Fin n) (l : Link d n) : Link d n :=
  (l.1, if l.1 = τ then reflSite τ (c - 1) l.2 else reflSite τ c l.2)

theorem reflLink_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflLink (d := d) (n := n) τ c) := by
  intro l
  obtain ⟨μ, x⟩ := l
  by_cases h : μ = τ
  · simp [reflLink, h, reflSite_involutive τ (c - 1) x]
  · simp [reflLink, h, reflSite_involutive τ c x]

/-- The reflection of links as a permutation. -/
def reflLinkPerm [NeZero n] (τ : Fin d) (c : Fin n) : Equiv.Perm (Link d n) :=
  (reflLink_involutive (d := d) (n := n) τ c).toPerm _

@[simp] theorem reflLinkPerm_apply [NeZero n] (τ : Fin d) (c : Fin n) (l : Link d n) :
    reflLinkPerm τ c l = reflLink τ c l := rfl

/-- **Reflection of a plaquette.** A plaquette whose plane misses the reflection axis keeps its plane
and moves its corner; one whose plane CONTAINS the axis has its loop traversed the other way round by
the mirror, and the boundary word `WilsonHypercubic.bd` writes a reversed loop by swapping the two
spanning directions — so the image plane is the transposed pair, based at the shifted corner.

DERIVED: the `1` is the link-length offset of `reflLink`, for the same reason. -/
def reflPlaq [NeZero n] (τ : Fin d) (c : Fin n) (q : Plaq d n) : Plaq d n :=
  if q.1.1 = τ then ((q.1.2, τ), reflSite τ (c - 1) q.2)
  else if q.1.2 = τ then ((τ, q.1.1), reflSite τ (c - 1) q.2)
  else ((q.1.1, q.1.2), reflSite τ c q.2)

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

/-- The reflection of plaquettes as a permutation. -/
def reflPlaqPerm [NeZero n] (τ : Fin d) (c : Fin n) : Equiv.Perm (Plaq d n) :=
  (reflPlaq_involutive (d := d) (n := n) τ c).toPerm _

@[simp] theorem reflPlaqPerm_apply [NeZero n] (τ : Fin d) (c : Fin n) (q : Plaq d n) :
    reflPlaqPerm τ c q = reflPlaq τ c q := rfl

/-! ### The reflection on configurations, dagger included -/

variable {G : Type} [Group G]

/-- **The reflection acting on a gauge-field configuration.** Off the axis it is a relabelling; ON
the axis it is a relabelling followed by INVERSION, because the mirror traverses a `τ`-link the other
way. This is the `†` of the Osterwalder–Seiler time reflection, and the reason a reflection is not a
`LatticeGauge.Symmetry`: `Symmetry.onLink` is a bare permutation of links and cannot carry it.

DERIVED: nothing numeric; the only data is the caller's `τ` and `c`. -/
def reflConf [NeZero n] (τ : Fin d) (c : Fin n) (U : Link d n → G) : Link d n → G :=
  fun l => if l.1 = τ then (U (reflLink τ c l))⁻¹ else U (reflLink τ c l)

theorem reflConf_involutive [NeZero n] (τ : Fin d) (c : Fin n) :
    Function.Involutive (reflConf (d := d) (n := n) (G := G) τ c) := by
  intro U
  funext l
  have hfst : (reflLink τ c l).1 = l.1 := rfl
  by_cases h : l.1 = τ
  · simp only [reflConf, hfst, if_pos h, reflLink_involutive τ c l, inv_inv]
  · simp only [reflConf, hfst, if_neg h, reflLink_involutive τ c l]

/-! ### The boundary word under reflection -/

/-- **The mirrored boundary word.** Each link is carried by `reflLink`, and the traversal of a
`τ`-link is REVERSED — which is what `reflConf`'s dagger and this bit flip are two readings of. -/
def reflWord [NeZero n] (τ : Fin d) (c : Fin n) (w : List (Link d n × Bool)) :
    List (Link d n × Bool) :=
  w.map (fun lo => (reflLink τ c lo.1, if lo.1.1 = τ then !lo.2 else lo.2))

/-- **A plaquette transverse to the reflection keeps its word**, exactly as under an axis
permutation (`WilsonHypercubic.bd_axis`): no link of its boundary runs along the axis, so nothing is
reversed and nothing is base-shifted. -/
theorem bd_reflect_transverse [NeZero n] (τ : Fin d) (c : Fin n) {μ ν : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (x : Site d n) :
    reflWord τ c (bd ((μ, ν), x)) = bd (reflPlaq τ c ((μ, ν), x)) := by
  simp only [reflWord, bd, reflPlaq, reflLink, reflSite_shift_of_ne hμ, reflSite_shift_of_ne hν,
    hμ, hν, if_false, List.map_cons, List.map_nil]

/-- **A plaquette whose FIRST direction is the reflection axis.** The mirrored word is the image
plaquette's own word rotated by one — the last letter brought to the front — so the holonomies agree
only up to conjugation, which is all a class function needs.

DERIVED: `3` is the index of the last letter of a four-letter plaquette word; `1` is the link-length
offset carried by `reflLink`. -/
theorem bd_reflect_axis_fst [NeZero n] (τ : Fin d) (c : Fin n) {ν : Fin d}
    (hν : ν ≠ τ) (x : Site d n) :
    reflWord τ c (bd ((τ, ν), x)) = (bd (reflPlaq τ c ((τ, ν), x))).rotate 3 := by
  simp only [reflWord, bd, reflPlaq, reflLink, hν, if_false, if_true,
    reflSite_shift_of_ne hν, reflSite_shift_axis, ← shift_reflSite_axis τ c x,
    List.map_cons, List.map_nil]
  rfl

/-- **A plaquette whose SECOND direction is the reflection axis** — the mirror image of the previous
case, rotated the other way.

DERIVED: `1` is one place of rotation, and the link-length offset of `reflLink`. -/
theorem bd_reflect_axis_snd [NeZero n] (τ : Fin d) (c : Fin n) {μ : Fin d}
    (hμ : μ ≠ τ) (x : Site d n) :
    reflWord τ c (bd ((μ, τ), x)) = (bd (reflPlaq τ c ((μ, τ), x))).rotate 1 := by
  simp only [reflWord, bd, reflPlaq, reflLink, hμ, if_false, if_true,
    reflSite_shift_of_ne hμ, reflSite_shift_axis, ← shift_reflSite_axis τ c x,
    List.map_cons, List.map_nil]
  rfl

/-! ### The holonomy, and the action -/

/-- The plaquette holonomy of the hypercubic boundary word, written out. -/
theorem hol_bd [NeZero n] (q : Plaq d n) (V : Link d n → G) :
    wilsonHol (bd (d := d) (n := n)) q V
      = V (q.1.1, q.2) * (V (q.1.2, shift q.1.1 q.2)
          * ((V (q.1.1, shift q.1.2 q.2))⁻¹ * (V (q.1.2, q.2))⁻¹)) := by
  simp [wilsonHol, bd]

/-- **The mirrored holonomy is CONJUGATE to the image plaquette's holonomy.**

Not equal: the mirrored boundary word is a cyclic rotation of the image word (`bd_reflect_axis_fst`,
`bd_reflect_axis_snd`), and a rotated ordered product is a conjugated one. Equality holds only for
plaquettes transverse to the reflection, where the rotation is trivial.

This is the exact point at which a reflection stops being a `LatticeGauge.Symmetry`, and it costs
nothing downstream because the Wilson density is a class function. -/
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
/-- **The Wilson action is invariant under the reflection** — the analogue of
`WilsonHypercubic.axisSymmetry` for the other half of the lattice's Euclidean group, and the
property `CompactGauge.expect_invariant_haar` needs of a map before it can move it through the
Gibbs measure.

It does NOT go through `WilsonLattice.wilsonSymmetry`, and cannot: the mirrored holonomy is only
CONJUGATE to the image plaquette's (`hol_reflConf`), so what carries the sum is that `wilsonDensity`
is a class function (`wilsonDensity_conj`) together with `reflPlaqPerm` being a bijection of the
plaquettes. -/
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

/-- **The probability Haar measure of a compact group is invariant under INVERSION.**

Mathlib derives this from regularity only for an ABELIAN group
(`Measure.IsHaarMeasure.isInvInvariant_of_regular`), and `SU(N)` is not abelian. On a compact group
it follows instead from unimodularity: `μ.inv` is left-invariant because `μ` is right-invariant
(`CompactGauge.isMulRightInvariant_probHaar`), so by uniqueness of Haar measure on a compact group it
is a multiple of `μ`, and both are probability measures, so the multiple is one.

This is what the reflection's dagger needs: inverting the gauge variable on the axis links has to
leave the measure alone, or the reflected expectation is not the original one.

DERIVED: the `1` is the total mass of a probability measure, which is what forces the Haar scalar
factor between `μ.inv` and `μ` to be one. It is the conclusion, not an input. -/
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

/-- **The DAGGER half of the reflection**, on its own: invert the gauge variable on every link that
runs along the reflection axis, leave the rest alone. Composed with the relabelling
`ReflectionPositivity.relabel (reflLinkPerm τ c)` it is `reflConf`, and splitting it off this way is
what lets the measure argument be made one coordinate at a time.

DERIVED: nothing numeric. -/
def daggerAxis [NeZero n] (τ : Fin d) (V : Link d n → MassGap.SUN.SU N) :
    Link d n → MassGap.SUN.SU N :=
  fun l => if l.1 = τ then (V l)⁻¹ else V l

/-- **The dagger preserves the product Haar measure** — coordinatewise, since each coordinate map is
either the identity or inversion and Haar is invariant under both. -/
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

/-- **The reflection preserves the product Haar measure over links.** Relabelling is
measure-preserving because the factors are identical
(`ReflectionPositivity.relabel_measurePreserving`); the dagger is because Haar is
inversion-invariant. -/
theorem reflConf_measurePreserving [NeZero n] (τ : Fin d) (c : Fin n) :
    MeasurePreserving (reflConf (G := MassGap.SUN.SU N) τ c)
      (vol (Link d n) N) (vol (Link d n) N) := by
  have hcomp : reflConf (G := MassGap.SUN.SU N) (d := d) (n := n) τ c
      = (daggerAxis (N := N) τ) ∘ (relabel (N := N) (reflLinkPerm τ c)) := by
    funext U l
    rfl
  rw [hcomp]
  exact (daggerAxis_measurePreserving τ).comp (relabel_measurePreserving (reflLinkPerm τ c))

/-- The reflection of configurations as a measurable equivalence — its own inverse. -/
noncomputable def reflConfEquiv [NeZero n] (τ : Fin d) (c : Fin n) :
    (Link d n → MassGap.SUN.SU N) ≃ᵐ (Link d n → MassGap.SUN.SU N) where
  toFun := reflConf τ c
  invFun := reflConf τ c
  left_inv := reflConf_involutive τ c
  right_inv := reflConf_involutive τ c
  measurable_toFun := (reflConf_measurePreserving (N := N) τ c).measurable
  measurable_invFun := (reflConf_measurePreserving (N := N) τ c).measurable

/-- **The Gibbs expectation of the `d`-dimensional `SU(N)` Wilson system is invariant under the
reflection.**

The reflection analogue of `WilsonHypercubic.axisSymmetry`'s payoff
(`WilsonLattice.wilson_expect_invariant`), reached the only way it can be: not through `Symmetry`,
which cannot carry the dagger, but through `LatticeGauge.System.expect_invariant_of_mp`, whose two
hypotheses are exactly the two halves proved above — the measure is preserved
(`reflConf_measurePreserving`) and the Boltzmann weight is unchanged (`reflect_action_invariant`).

This is the invariance a reflection-positivity argument on this lattice consumes: it is what makes
the reflected copy of an observable integrate to the same number as the observable, which is the
`hmirror` step inside `ReflectionPositivity.pairing_with_reflection_nonneg`. -/
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
