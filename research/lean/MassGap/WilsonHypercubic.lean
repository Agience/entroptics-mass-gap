import MassGap.WilsonLattice
import MassGap.WilsonAction

/-!
# The Wilson lattice gauge system on a periodic `d`-dimensional hypercubic lattice

`WilsonLattice.wilsonSystem` builds a gauge system from a boundary word — the ordered list of links
a plaquette's loop traverses. It is agnostic about geometry: whatever boundary word it is handed is
the lattice it describes. This file supplies the boundary word of the periodic hypercubic lattice in
`d` dimensions, so that `d = 4` is a genuine four-dimensional Yang–Mills lattice rather than a label.

## What "four-dimensional" has to mean

A four-dimensional lattice is not a system with four links. It has one link per (site, direction) —
`d·n^d` of them — and one plaquette per (site, oriented plane), whose holonomy is the ORDERED PRODUCT
around the loop:

    U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹

and whose action is the Wilson density `1 − Re tr U_p / N`. Those three things — the link count, the
loop product, and the action — are what make the system a gauge theory rather than a collection of
independent group elements, and all three are supplied here.

## Dimension-general, so `d = 3` and `d = 4` are one construction

`WilsonBridge.bd3` indexes a plaquette by its NORMAL, which is available only in three dimensions
(where a plane is fixed by the axis orthogonal to it). That parameterisation does not extend. Here a
plaquette carries the pair of directions spanning its plane, which is the general description; `d = 3`
is then the same construction as `bd3` under the correspondence `normal k ↔ plane (k+1, k+2)`.
-/

namespace MassGap.WilsonHypercubic

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice

variable {d n : ℕ}

/-- Sites of a periodic `n^d` lattice: one coordinate per direction. -/
abbrev Site (d n : ℕ) : Type := Fin d → Fin n

/-- Links: a direction and a site. There are `d · n^d` of them, not `d`. -/
abbrev Link (d n : ℕ) : Type := Fin d × Site d n

/-- Plaquettes: an ORDERED PAIR of directions spanning the plane, and a site.

Carrying the pair rather than a normal is what makes this dimension-general: in `d` dimensions a
plane needs two directions, and only in `d = 3` does one suffice. Degenerate pairs `μ = ν` are
present in the type and contribute the identity holonomy (the loop retraces itself), so they cost
nothing and need no separate exclusion.

DERIVED: the `2` directions are what a plane has; in `d` dimensions a plaquette needs exactly two
and no fewer. Nothing here is chosen. -/
abbrev Plaq (d n : ℕ) : Type := (Fin d × Fin d) × Site d n

/-- Translate a site one step in direction `μ`, periodically.

DERIVED: `1` is one lattice step -- the definition of a neighbouring site, not a length. -/
def shift [NeZero n] (μ : Fin d) (x : Site d n) : Site d n :=
  Function.update x μ (x μ + 1)

/-- **The plaquette boundary word**: `U_μ(x) · U_ν(x+μ̂) · U_μ(x+ν̂)⁻¹ · U_ν(x)⁻¹`.

The `Bool` is the orientation — `true` traverses the link forwards, `false` inverts it — and
`WilsonLattice.wilsonHol` turns the word into the ordered product. This is the elementary Wilson
loop, and it is the only place the lattice geometry enters the construction. -/
def bd [NeZero n] (q : Plaq d n) : List (Link d n × Bool) :=
  let μ := q.1.1
  let ν := q.1.2
  let x := q.2
  [((μ, x), true), ((ν, shift μ x), true),
   ((μ, shift ν x), false), ((ν, x), false)]

/-- **The `d`-dimensional periodic `SU(N)` Wilson lattice gauge system.**

Ordered-loop holonomy on the hypercubic boundary word, Wilson plaquette action, product Haar over
links. With `d = 4` this is four-dimensional Yang–Mills on a periodic lattice; with `d = 3` it is the
three-dimensional one, the same construction at a different dimension rather than a separate object.

The coupling is not part of the system: `LatticeGauge.expect` carries `β`, and because `φ` here is
the genuine Wilson density rather than the zero function, `β` actually moves the Gibbs measure.

DERIVED: `d` and `n` are arguments, not literals -- the dimension and the extent are the caller's.
Yang-Mills as the Clay problem states it is `d = 4`, `N = 3`; both are instantiations of this, not
separate constructions. -/
noncomputable def sysWilson (N d n : ℕ) [NeZero n] : System (MassGap.SUN.SU N) :=
  wilsonSystem (G := MassGap.SUN.SU N) (bd (d := d) (n := n))
    (MassGap.WilsonAction.wilsonDensity (N := N))

/-- The links of the system really are `(direction, site)` pairs -- the link count is `d · n^d`. -/
theorem sysWilson_link (N d n : ℕ) [NeZero n] :
    (sysWilson N d n).Link = Link d n := rfl

/-- The plaquettes really are `(plane, site)` pairs. -/
theorem sysWilson_plaq (N d n : ℕ) [NeZero n] :
    (sysWilson N d n).Plaq = Plaq d n := rfl

/-- The holonomy really is the ordered loop product of the boundary word. -/
theorem sysWilson_hol (N d n : ℕ) [NeZero n] (q : Plaq d n) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).hol q U = wilsonHol (bd (d := d) (n := n)) q U := rfl

/-- The action density really is Wilson's, not the zero function -- which is what makes `β` matter. -/
theorem sysWilson_phi (N d n : ℕ) [NeZero n] :
    (sysWilson N d n).φ = MassGap.WilsonAction.wilsonDensity (N := N) := rfl

/-- **A degenerate plane contributes nothing.** With `μ = ν` the boundary word traverses the same two
links forwards and backwards, so the holonomy is the identity and the Wilson density vanishes. This
is why the plaquette type may carry all pairs without excluding the diagonal. -/
theorem bd_diag_hol_one [NeZero n] (μ : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU 2) :
    wilsonHol (bd (d := d) (n := n)) ((μ, μ), x) U = 1 := by
  simp [wilsonHol, bd]

/-- **The link count is `d · n^d`, which is what distinguishes a LATTICE from a label.**

A system with `Fin d` as its link type has `d` links and is not a lattice in any dimension. This one
has one link per (direction, site): at `d = 4, n = 8` that is `4 · 4096 = 16384` links, and it grows
with the volume as a four-dimensional gauge theory must. Stated as a cardinality because that is the
claim a reader should be able to check without reading the definitions. -/
theorem card_link (d n : ℕ) : Fintype.card (Link d n) = d * n ^ d := by
  simp [Link, Fintype.card_prod, Fintype.card_fin]

/-- And the plaquette count is `d² · n^d` -- one per ordered plane per site. -/
theorem card_plaq (d n : ℕ) : Fintype.card (Plaq d n) = d * d * n ^ d := by
  simp [Plaq, Fintype.card_prod, Fintype.card_fin]

/-! ### Axis permutations are a symmetry of the lattice

The hypercubic lattice's discrete Euclidean symmetry is the permutation of its axes. Relabelling
direction `μ` as `e μ` must carry the site coordinates with it -- a site's coordinate in direction
`e μ` is its old coordinate in direction `μ` -- and the whole content is that this commutes with the
unit shift. Given that, `WilsonLattice.wilsonSymmetry` turns it into a genuine `Symmetry` of the
gauge system, which is what an `os_euc` field needs.
-/

/-- Relabelling the axes of a site: the coordinate in direction `e μ` is the old one in `μ`. -/
def axisSite (e : Equiv.Perm (Fin d)) : Equiv.Perm (Site d n) :=
  Equiv.arrowCongr e (Equiv.refl (Fin n))

/-- Relabelling the axes of a link. -/
def axisLink (e : Equiv.Perm (Fin d)) : Equiv.Perm (Link d n) :=
  Equiv.prodCongr e (axisSite e)

/-- Relabelling the axes of a plaquette: both spanning directions move together. -/
def axisPlaq (e : Equiv.Perm (Fin d)) : Equiv.Perm (Plaq d n) :=
  Equiv.prodCongr (Equiv.prodCongr e e) (axisSite e)

/-- **The unit shift commutes with an axis relabelling.** The one geometric fact the symmetry needs:
stepping in direction `e μ` after relabelling is relabelling after stepping in direction `μ`. -/
theorem shift_axis [NeZero n] (e : Equiv.Perm (Fin d)) (μ : Fin d) (x : Site d n) :
    shift (e μ) (axisSite e x) = axisSite e (shift μ x) := by
  funext j
  simp only [shift, axisSite, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq]
  by_cases h : j = e μ
  · subst h
    simp [Function.update_self]
  · have h' : e.symm j ≠ μ := by
      intro hc
      exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h']

/-- **Axis relabelling maps boundary words compatibly** -- the hypothesis `wilsonSymmetry` consumes. -/
theorem bd_axis [NeZero n] (e : Equiv.Perm (Fin d)) (q : Plaq d n) :
    bd (axisPlaq e q) = (bd q).map (fun lo => (axisLink e lo.1, lo.2)) := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only [bd, axisPlaq, axisLink, Equiv.prodCongr_apply, Prod.map_apply,
    List.map_cons, List.map_nil]
  rw [shift_axis, shift_axis]

/-- **The axis symmetry of the `d`-dimensional Wilson system.**

The discrete Euclidean invariance of the hypercubic lattice, as a `Symmetry` of the gauge system --
so the Gibbs expectation is invariant under it by `WilsonLattice.wilson_expect_invariant`, and the
`os_euc`/`os_perm` fields of a `LatticeYMFamily` are DERIVED rather than asserted. -/
noncomputable def axisSymmetry (N : ℕ) [NeZero n] (e : Equiv.Perm (Fin d)) :
    Symmetry (sysWilson N d n) :=
  wilsonSymmetry (G := MassGap.SUN.SU N) (bd (d := d) (n := n))
    (MassGap.WilsonAction.wilsonDensity (N := N)) (axisLink e) (axisPlaq e) (bd_axis e)

#print axioms shift_axis
#print axioms bd_axis

/-! ### Why `d >= 3` is an interacting theory, in any dimension

`WilsonBridge.bd3_link_not_private` records the structural fact that makes a three-dimensional gauge
theory interacting: no plaquette owns a link that appears in no other plaquette. It matters because a
PRIVATE link can be integrated out first, and left-translation by it carries its plaquette's holonomy
through Haar -- so that plaquette becomes Haar-distributed and independent of everything else, the
connected correlation collapses to a contact term, and the aperture condition is satisfied trivially
by a free theory. That is the free-field non-vacuity the development elsewhere warns about.

Stated there for `d = 3` and a plaquette indexed by its NORMAL, which only exists in three dimensions.
Here it is the same fact in any `d >= 3`, on the plane-pair indexing, on the lattice the OS measure
actually uses -- so the gap side's reason and the measure side's object stop being two constructions.

WHERE THE `3` COMES FROM, and it is not a choice. The second plaquette must be NON-DEGENERATE: its
two directions must differ, or its boundary word retraces itself and its holonomy is the identity
(`bd_diag_hol_one`). So the witness direction has to avoid both `mu` and `nu`, and a set of two
directions has a complement exactly when there are more than two directions. `d <= 2` fails, which is
why two-dimensional lattice gauge theory is exactly solvable.
-/

/-- **No plaquette owns a private link, in any dimension `d >= 3`.**

The link `U_mu(x)` opens the boundary word of the plaquette spanning `(mu, nu)` at `x`; it also opens
the one spanning `(mu, rho)` at `x`, which is a different plaquette whenever `rho != nu` and a
non-degenerate one whenever `rho != mu`. Both are available exactly when `d >= 3`.

DERIVED: the `3` is where a two-element set of directions has a complement. Nothing is chosen. -/
theorem link_not_private [NeZero n] (hd : 3 ≤ d) (μ ν : Fin d) (x : Site d n) :
    ∃ ρ : Fin d, ρ ≠ μ ∧ ρ ≠ ν ∧
      ((μ, x) ∈ (bd ((μ, ν), x)).map Prod.fst) ∧
      ((μ, x) ∈ (bd ((μ, ρ), x)).map Prod.fst) ∧
      (((μ, ρ), x) : Plaq d n) ≠ ((μ, ν), x) := by
  -- a two-element set of directions does not exhaust `Fin d` when `d >= 3`
  have hcard : ({μ, ν} : Finset (Fin d)).card < Fintype.card (Fin d) := by
    have h2 : ({μ, ν} : Finset (Fin d)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have : Fintype.card (Fin d) = d := Fintype.card_fin d
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin d, ρ ∉ ({μ, ν} : Finset (Fin d)) := by
    by_contra hcon
    push Not at hcon
    have : Finset.univ ⊆ ({μ, ν} : Finset (Fin d)) := fun a _ => hcon a
    have := Finset.card_le_card this
    simp only [Finset.card_univ] at this
    omega
  rw [Finset.mem_insert, Finset.mem_singleton] at hρ
  push Not at hρ
  refine ⟨ρ, hρ.1, hρ.2, by simp [bd], by simp [bd], ?_⟩
  intro hcon
  exact hρ.2 (by simpa using congrArg (fun q => (q : Plaq d n).1.2) hcon)

#print axioms link_not_private

#print axioms card_link
#print axioms card_plaq
#print axioms sysWilson_link
#print axioms sysWilson_plaq
#print axioms sysWilson_hol
#print axioms sysWilson_phi
#print axioms bd_diag_hol_one

end MassGap.WilsonHypercubic
