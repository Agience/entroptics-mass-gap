import MassGap.WilsonLattice
import MassGap.WilsonAction

/-!
# The Wilson lattice gauge system on a periodic `d`-dimensional hypercubic lattice

Supplies the geometry that `WilsonLattice.wilsonSystem` is parameterised over. That constructor takes
a boundary word — the ordered list of `(link, orientation)` pairs a plaquette's loop traverses — and
is otherwise agnostic about the lattice; this file gives it the periodic hypercubic word in `d`
dimensions with extent `n`.

Types: `Site d n := Fin d → Fin n`, `Link d n := Fin d × Site d n`, and
`Plaq d n := (Fin d × Fin d) × Site d n`, a plaquette carrying the ordered pair of directions
spanning its plane rather than a normal, which is what makes the construction work at any `d`.
`card_link` and `card_plaq` compute the cardinalities as `d * n ^ d` and `d * d * n ^ d`.

`shift μ x` steps one site in direction `μ` with wrap-around, and `bd q` is the four-entry boundary
word `U_μ(x) · U_ν(x + μ̂) · U_μ(x + ν̂)⁻¹ · U_ν(x)⁻¹`. `sysWilson N d n` feeds `bd` and
`WilsonAction.wilsonDensity` to `wilsonSystem` over the group `MassGap.SUN.SU N`; the four `rfl`
theorems after it pin down that system's link type, plaquette type, holonomy and action density.

`axisSite`, `axisLink` and `axisPlaq` are the axis-relabelling permutations induced by
`e : Equiv.Perm (Fin d)`; `shift_axis` is the commutation fact they rest on, `bd_axis` the
boundary-word compatibility `wilsonSymmetry` consumes, and `axisSymmetry` the resulting
`Symmetry (sysWilson N d n)`.

`bd_diag_hol_one` evaluates the holonomy of a degenerate plane (`μ = ν`) to `1`, and
`link_not_private` exhibits, at `3 ≤ d`, a second plaquette through a given link.

Scope: `d` and `n` are arguments throughout — no statement fixes a dimension or an extent, and no
statement fixes `N` except `bd_diag_hol_one`, which is stated at `MassGap.SUN.SU 2` only. `[NeZero n]`
is required wherever `shift` appears. The coupling is not part of `sysWilson`;
`LatticeGauge.expect` carries `β`.
-/

namespace MassGap.WilsonHypercubic

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice

variable {d n : ℕ}

/-- Sites of a periodic `n ^ d` lattice, as `Fin d → Fin n`: one `Fin n` coordinate per direction.
Periodicity is the wrap-around of `Fin n` and is not imposed separately.

DERIVED: no numeral appears in the statement. -/
abbrev Site (d n : ℕ) : Type := Fin d → Fin n

/-- Links, as `Fin d × Site d n`: a direction together with the site the link leaves. The
cardinality is computed in `card_link`.

DERIVED: no numeral appears in the statement. -/
abbrev Link (d n : ℕ) : Type := Fin d × Site d n

/-- Plaquettes, as `(Fin d × Fin d) × Site d n`: an ordered pair of directions spanning the plane,
together with a site. Indexing by a pair rather than by a normal is what lets the same definition
serve every `d`; a normal determines a plane only at `d = 3`.

Scope: the diagonal `μ = ν` is inhabited and is not excluded by the type. Such a plaquette's
boundary word retraces itself, and `bd_diag_hol_one` evaluates its holonomy to `1` at
`MassGap.SUN.SU 2`.

DERIVED: no numeral appears in the statement. The plane is carried as a pair of `Fin d`, so the
"two directions" are the product structure, not a literal. -/
abbrev Plaq (d n : ℕ) : Type := (Fin d × Fin d) × Site d n

/-- Translate a site one step in direction `μ`: `Function.update x μ (x μ + 1)`. The successor is
taken in `Fin n`, so it wraps at the extent, which is what makes the lattice periodic. `[NeZero n]`
is required for that arithmetic.

DERIVED: `1` is the single step added to the `μ` coordinate — the definition of a neighbouring site,
not a physical length. -/
def shift [NeZero n] (μ : Fin d) (x : Site d n) : Site d n :=
  Function.update x μ (x μ + 1)

/-- The boundary word of the plaquette `q = ((μ, ν), x)`: the four-entry list
`[((μ, x), true), ((ν, shift μ x), true), ((μ, shift ν x), false), ((ν, x), false)]`, spelling out
`U_μ(x) · U_ν(x + μ̂) · U_μ(x + ν̂)⁻¹ · U_ν(x)⁻¹`.

The `Bool` is the orientation — `true` traverses the link forwards, `false` inverts it — and
`WilsonLattice.wilsonHol` turns the word into the ordered product. This definition is where the
lattice geometry enters; everything downstream reads `bd`.

DERIVED: no numeral appears in the statement; `true` and `false` are orientation flags, not
numerals, and the list has four entries because a plaquette loop has four sides. -/
def bd [NeZero n] (q : Plaq d n) : List (Link d n × Bool) :=
  let μ := q.1.1
  let ν := q.1.2
  let x := q.2
  [((μ, x), true), ((ν, shift μ x), true),
   ((μ, shift ν x), false), ((ν, x), false)]

/-- The periodic `d`-dimensional Wilson lattice gauge system over `MassGap.SUN.SU N` with extent
`n`: `wilsonSystem` applied to the hypercubic boundary word `bd` and the action density
`WilsonAction.wilsonDensity`.

Scope: `N`, `d` and `n` are all arguments, so this is one construction covering every gauge group,
dimension and extent. The coupling is not a field of the system — `LatticeGauge.expect` carries `β`
— and the measure over links is the one `expect` supplies, not one fixed here. Since `φ` is
`wilsonDensity` rather than the zero function, `β` does move the Gibbs weight.

DERIVED: no numeral appears in the statement; `N`, `d` and `n` are the caller's. -/
noncomputable def sysWilson (N d n : ℕ) [NeZero n] : System (MassGap.SUN.SU N) :=
  wilsonSystem (G := MassGap.SUN.SU N) (bd (d := d) (n := n))
    (MassGap.WilsonAction.wilsonDensity (N := N))

/-- `(sysWilson N d n).Link` is definitionally `Link d n`, that is `Fin d × Site d n`. Proved by
`rfl`.

DERIVED: no numeral appears in the statement. -/
theorem sysWilson_link (N d n : ℕ) [NeZero n] :
    (sysWilson N d n).Link = Link d n := rfl

/-- `(sysWilson N d n).Plaq` is definitionally `Plaq d n`, that is `(Fin d × Fin d) × Site d n`.
Proved by `rfl`.

DERIVED: no numeral appears in the statement. -/
theorem sysWilson_plaq (N d n : ℕ) [NeZero n] :
    (sysWilson N d n).Plaq = Plaq d n := rfl

/-- `(sysWilson N d n).hol q U` is definitionally `wilsonHol bd q U`, the ordered product along the
hypercubic boundary word. Proved by `rfl`, at every plaquette `q` and every link configuration `U`.

DERIVED: no numeral appears in the statement. -/
theorem sysWilson_hol (N d n : ℕ) [NeZero n] (q : Plaq d n) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).hol q U = wilsonHol (bd (d := d) (n := n)) q U := rfl

/-- `(sysWilson N d n).φ` is definitionally `WilsonAction.wilsonDensity (N := N)`, not the zero
function. Proved by `rfl`. This is what makes the coupling carried by `LatticeGauge.expect` move the
Gibbs weight.

DERIVED: no numeral appears in the statement. -/
theorem sysWilson_phi (N d n : ℕ) [NeZero n] :
    (sysWilson N d n).φ = MassGap.WilsonAction.wilsonDensity (N := N) := rfl

/-- For a degenerate plaquette `((μ, μ), x)`, the holonomy is the group identity:
`wilsonHol bd ((μ, μ), x) U = 1`. The boundary word traverses `(μ, x)` and `(μ, shift μ x)` once
forwards and once inverted, so the ordered product collapses; `simp [wilsonHol, bd]` closes it.

Scope, and it is narrower than the name suggests: the statement is fixed at the group
`MassGap.SUN.SU 2` — `U : Link d n → MassGap.SUN.SU 2` — so it does not cover general `N`. It states
the holonomy only; the value of `wilsonDensity` at that holonomy is not part of the conclusion.

DERIVED: `2` is the rank fixed in the type of `U`, `MassGap.SUN.SU 2`; `1` is the group identity the
holonomy is equated to. -/
theorem bd_diag_hol_one [NeZero n] (μ : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU 2) :
    wilsonHol (bd (d := d) (n := n)) ((μ, μ), x) U = 1 := by
  simp [wilsonHol, bd]

/-- `Fintype.card (Link d n) = d * n ^ d`: one link per (direction, site) pair. Immediate from
`Fintype.card_prod` and `Fintype.card_fin`. At `d = 4`, `n = 8` this is `4 * 4096 = 16384`.

Scope: `d` and `n` are arbitrary naturals, including `0`, where both sides are `0`.

DERIVED: no numeral appears in the statement; `d` and `n` are the caller's. -/
theorem card_link (d n : ℕ) : Fintype.card (Link d n) = d * n ^ d := by
  simp [Link, Fintype.card_prod, Fintype.card_fin]

/-- `Fintype.card (Plaq d n) = d * d * n ^ d`: one plaquette per (ordered direction pair, site).
Immediate from `Fintype.card_prod` and `Fintype.card_fin`.

Scope: the count is over ORDERED pairs and includes the `d` degenerate pairs `μ = ν`, so it is
`d * d` rather than `d * (d - 1) / 2`.

DERIVED: no numeral appears in the statement; the two factors of `d` are the two directions spanning
the plane. -/
theorem card_plaq (d n : ℕ) : Fintype.card (Plaq d n) = d * d * n ^ d := by
  simp [Plaq, Fintype.card_prod, Fintype.card_fin]

/-! ### Axis permutations as a `Symmetry` of the system

Relabelling direction `μ` as `e μ` carries the site coordinates with it: a site's coordinate in
direction `e μ` is its old coordinate in direction `μ`. `shift_axis` is the fact that this commutes
with the unit shift, `bd_axis` lifts it to boundary words, and `WilsonLattice.wilsonSymmetry` turns
that into a `Symmetry (sysWilson N d n)`.
-/

/-- The permutation of `Site d n` induced by an axis permutation `e : Equiv.Perm (Fin d)`, as
`Equiv.arrowCongr e (Equiv.refl (Fin n))`: the coordinate in direction `e μ` is the old coordinate
in direction `μ`. Coordinates within `Fin n` are untouched.

DERIVED: no numeral appears in the statement. -/
def axisSite (e : Equiv.Perm (Fin d)) : Equiv.Perm (Site d n) :=
  Equiv.arrowCongr e (Equiv.refl (Fin n))

/-- The permutation of `Link d n` induced by an axis permutation `e`, as `Equiv.prodCongr e
(axisSite e)`: the direction moves by `e` and the site by `axisSite e`.

DERIVED: no numeral appears in the statement. -/
def axisLink (e : Equiv.Perm (Fin d)) : Equiv.Perm (Link d n) :=
  Equiv.prodCongr e (axisSite e)

/-- The permutation of `Plaq d n` induced by an axis permutation `e`, as
`Equiv.prodCongr (Equiv.prodCongr e e) (axisSite e)`: both spanning directions move by `e`, and the
site by `axisSite e`.

DERIVED: no numeral appears in the statement. -/
def axisPlaq (e : Equiv.Perm (Fin d)) : Equiv.Perm (Plaq d n) :=
  Equiv.prodCongr (Equiv.prodCongr e e) (axisSite e)

/-- `shift (e μ) (axisSite e x) = axisSite e (shift μ x)`: stepping in direction `e μ` after
relabelling equals relabelling after stepping in direction `μ`. Proved coordinatewise, splitting on
whether the coordinate index is `e μ`.

Scope: `e` is an arbitrary `Equiv.Perm (Fin d)`; `[NeZero n]` is required for `shift`.

DERIVED: no numeral appears in the statement. -/
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

/-- `bd (axisPlaq e q) = (bd q).map (fun lo => (axisLink e lo.1, lo.2))`: relabelling the axes of a
plaquette relabels its boundary word entrywise, preserving the orientation flags and their order.
The proof destructures `q` and rewrites the two `shift` occurrences with `shift_axis`. This is the
hypothesis `WilsonLattice.wilsonSymmetry` consumes.

DERIVED: no numeral appears in the statement. -/
theorem bd_axis [NeZero n] (e : Equiv.Perm (Fin d)) (q : Plaq d n) :
    bd (axisPlaq e q) = (bd q).map (fun lo => (axisLink e lo.1, lo.2)) := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only [bd, axisPlaq, axisLink, Equiv.prodCongr_apply, Prod.map_apply,
    List.map_cons, List.map_nil]
  rw [shift_axis, shift_axis]

/-- The `Symmetry (sysWilson N d n)` carried by an axis permutation `e`, built by
`WilsonLattice.wilsonSymmetry` from `axisLink e`, `axisPlaq e` and the compatibility `bd_axis e`.

Because it is a `Symmetry`, `WilsonLattice.wilson_expect_invariant` applies to it, which is what an
`os_euc` or `os_perm` field of a `LatticeYMFamily` can be discharged from.

Scope: this covers axis permutations only — the discrete hypercubic group. Reflections, translations
and continuous rotations are not constructed here.

DERIVED: no numeral appears in the statement. -/
noncomputable def axisSymmetry (N : ℕ) [NeZero n] (e : Equiv.Perm (Fin d)) :
    Symmetry (sysWilson N d n) :=
  wilsonSymmetry (G := MassGap.SUN.SU N) (bd (d := d) (n := n))
    (MassGap.WilsonAction.wilsonDensity (N := N)) (axisLink e) (axisPlaq e) (bd_axis e)

#print axioms shift_axis
#print axioms bd_axis

/-! ### Every link lies on at least two plaquettes once `3 <= d`

`link_not_private` states this on the plane-pair indexing, at any `d >= 3`.
`WilsonBridge.bd3_link_not_private` is the corresponding statement at `d = 3` on the normal-indexed
parameterisation.

The bound `3 <= d` is where the statement's own requirements land: the second plaquette must be
non-degenerate, so its two directions must differ, so the witness direction must avoid both `mu` and
`nu`; a two-element subset of `Fin d` has a complement exactly when `d` exceeds two.
-/

/-- For `3 ≤ d`, any directions `μ`, `ν` and any site `x`, there exists a direction `ρ` with
`ρ ≠ μ`, `ρ ≠ ν`, such that the link `(μ, x)` occurs in the boundary word of `((μ, ν), x)` and in
that of `((μ, ρ), x)`, and those two plaquettes are distinct.

The proof bounds `({μ, ν} : Finset (Fin d)).card` by `2 < Fintype.card (Fin d)`, extracts `ρ` outside
that pair, and reads the two memberships off `bd` by `simp`. Distinctness of the plaquettes follows
from `ρ ≠ ν` by projecting the second direction.

Scope: the statement concerns the single link `(μ, x)` — the first entry of the boundary word — and
the two plaquettes sharing it; it is not a statement about every link of every plaquette, nor about
the measure or any correlation. `ρ ≠ μ` keeps the second plaquette off the degenerate diagonal.

DERIVED: `3` is the lower bound on `d`, the point at which a two-element subset of `Fin d` has a
nonempty complement. No other numeral appears in the statement. -/
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
