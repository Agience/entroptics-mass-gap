import MassGap.LatticeGauge

/-!
# MassGap.WilsonLattice — plaquette holonomy as an ordered loop product

`LatticeGauge.System` leaves the plaquette holonomy `hol` abstract. This module instantiates it as an
ordered product of link variables around a loop, presented combinatorially: a plaquette `p` carries a
**boundary word** `bd p : List (L × Bool)`, an ordered list of `(link, orientation)` pairs where
`true` means the link variable and `false` its inverse, and

    wilsonHol bd p U = ∏ over that list, in order.

The lattice is not coordinatised anywhere here. `L` and `P` are arbitrary types — the links and the
plaquettes — and `bd` is an arbitrary function; no incidence, dimension or extent condition relates
them, and nothing forces a boundary word to have length four or to close. A symmetry is likewise
combinatorial: a pair of permutations `σL`, `σP` satisfying the hypothesis `hbd`, that `bd (σP p)` is
the `σL`-relabelling of `bd p`. Under that hypothesis `compat` reduces to a `List.map`/`List.prod`
reindexing.

What the module supplies:

* `wilsonHol`, `wilsonSystem` — the holonomy and the `System G` built from it with a caller-supplied
  plaquette density `φ : G → ℝ`.
* `wilsonSymmetry`, `wilson_expect_invariant` — a `Symmetry` from `hbd`, and invariance of the Gibbs
  expectation under transporting the observable by it, inherited from `Symmetry.expect_invariant`.
* `list_prod_conj`, `wilsonHol_conj` — conjugating every link variable by a fixed `g` conjugates the
  holonomy. This is the global (constant) gauge transformation; no position-dependent gauge
  transformation is treated.
* `measurable_stepListProd`, `measurable_wilsonHol` — measurability of the holonomy in the
  configuration, given `MeasurableMul₂ G` and `MeasurableInv G`.

`G` is any group with a `MeasurableSpace`; compactness, connectedness and `SU(N)` play no part.
-/

namespace MassGap.WilsonLattice

open MassGap.LatticeGauge

variable {G : Type} [Group G] [MeasurableSpace G] {L P : Type}

/-- The holonomy of plaquette `p` in configuration `U`: map the boundary word `bd p` to group
elements, sending `(l, true)` to `U l` and `(l, false)` to `(U l)⁻¹`, then take the ordered
`List.prod`. Order matters, so this is the non-abelian loop product and not a sum of link variables.

`bd` is arbitrary. The definition does not require the word to be a closed loop, to have any
particular length, or to visit each link once.

DERIVED: no numeral. The `⁻¹` is the group inverse, notation rather than a literal exponent; `true`
and `false` are `Bool` constructors. -/
def wilsonHol (bd : P → List (L × Bool)) (p : P) (U : L → G) : G :=
  ((bd p).map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod

/-- The `LatticeGauge.System G` with link type `L`, plaquette type `P`, holonomy `wilsonHol bd`, and
plaquette density the caller-supplied `φ : G → ℝ`. `L` and `P` must be `Fintype`s; that finiteness is
the only constraint the system places on them.

`φ` is an arbitrary real function on `G`. Nothing here fixes it to a character, a trace or a real
part, so any property of the Wilson action proper has to come from the `φ` passed in.

DERIVED: no numeral. -/
def wilsonSystem [Fintype L] [Fintype P]
    (bd : P → List (L × Bool)) (φ : G → ℝ) : System G where
  Link := L
  Plaq := P
  hol := wilsonHol bd
  φ := φ

/-- A `Symmetry (wilsonSystem bd φ)` built from a permutation `σL` of links and a permutation `σP` of
plaquettes, given the hypothesis `hbd` that `bd (σP p)` is the pointwise `σL`-relabelling of `bd p`,
orientations unchanged. The `compat` field is then `List.map_map` followed by `rfl`.

`hbd` is the entire content: the pair of permutations is otherwise unconstrained, and no geometric
condition — rotation, translation, reflection — is imposed or available, because the lattice has no
coordinates in this module.

DERIVED: no numeral. -/
def wilsonSymmetry [Fintype L] [Fintype P]
    (bd : P → List (L × Bool)) (φ : G → ℝ)
    (σL : Equiv.Perm L) (σP : Equiv.Perm P)
    (hbd : ∀ p, bd (σP p) = (bd p).map (fun lo => (σL lo.1, lo.2))) :
    Symmetry (wilsonSystem bd φ) where
  onLink := σL
  onPlaq := σP
  compat := by
    intro p U
    show wilsonHol bd p (fun l => U (σL l)) = wilsonHol bd (σP p) U
    unfold wilsonHol
    rw [hbd p, List.map_map]
    rfl

/-- The Gibbs expectation of `wilsonSystem bd φ` at coupling `β` is unchanged when the observable `O`
is precomposed with the link relabelling of `wilsonSymmetry bd φ σL σP hbd`. Immediate from
`Symmetry.expect_invariant` applied to that symmetry.

`μ` is any probability measure on `G` with a `MeasurableSpace`; the statement carries an
`IsProbabilityMeasure` instance and nothing more, so `β`, `φ` and `O` are all arbitrary and the
result holds for each. The invariance is under the given pair of permutations only — it says nothing
about any permutation not satisfying `hbd`.

DERIVED: no numeral. -/
theorem wilson_expect_invariant [Fintype L] [Fintype P]
    (bd : P → List (L × Bool)) (φ : G → ℝ)
    (σL : Equiv.Perm L) (σP : Equiv.Perm P)
    (hbd : ∀ p, bd (σP p) = (bd p).map (fun lo => (σL lo.1, lo.2)))
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ] (β : ℝ)
    (O : (wilsonSystem bd φ).Config → ℝ) :
    (wilsonSystem bd φ).expect μ β
        (fun U => O (Symmetry.reindex (wilsonSymmetry bd φ σL σP hbd).onLink U))
      = (wilsonSystem bd φ).expect μ β O :=
  Symmetry.expect_invariant (wilsonSystem bd φ) μ (wilsonSymmetry bd φ σL σP hbd) β O

/-! ### Global gauge invariance of the holonomy -/

/-- For a group element `g` and a list `xs` of group elements, `∏ (g * xᵢ * g⁻¹) = g * (∏ xᵢ) * g⁻¹`.
List induction; the cons step is the telescoping `g⁻¹ * g` cancellation, closed by `group`.

DERIVED: no numeral. The `⁻¹` is the group inverse. -/
theorem list_prod_conj (g : G) (xs : List G) :
    (xs.map (fun x => g * x * g⁻¹)).prod = g * xs.prod * g⁻¹ := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.prod_cons, ih]; group

/-- Replacing every link variable `U l` by `g * U l * g⁻¹`, for one fixed `g`, conjugates the
holonomy: `wilsonHol bd p (g · U · g⁻¹) = g * wilsonHol bd p U * g⁻¹`. Proved from `list_prod_conj`,
with a case split on the orientation bit, since the inverse of a conjugate is the conjugate of the
inverse.

The transformation is global — a single `g` for all links — so this is not gauge invariance under a
position-dependent transformation, which would act on the two endpoints of each link separately. No
measure and no finiteness is used; `bd`, `p` and `U` are arbitrary.

DERIVED: no numeral. The `⁻¹` is the group inverse. -/
theorem wilsonHol_conj (bd : P → List (L × Bool)) (g : G) (p : P) (U : L → G) :
    wilsonHol bd p (fun l => g * U l * g⁻¹) = g * wilsonHol bd p U * g⁻¹ := by
  unfold wilsonHol
  rw [← list_prod_conj g, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro lo _
  simp only [Function.comp_apply]
  cases h : lo.2 <;> simp [mul_inv_rev, mul_assoc]

/-! ### Measurability of the holonomy -/

/-- For any list `l : List (L × Bool)`, the map sending a configuration `U : L → G` to the ordered
product of its step factors (`U lo.1` when the orientation bit is `true`, `(U lo.1)⁻¹` when it is
`false`) is measurable. List induction: the empty product is constant, and the cons step is
`Measurable.mul` of a coordinate projection, inverted or not, with the inductive hypothesis.

Requires `MeasurableMul₂ G` and `MeasurableInv G`; the product space `L → G` carries the pi
measurable structure.

DERIVED: no numeral. -/
theorem measurable_stepListProd [MeasurableMul₂ G] [MeasurableInv G] (l : List (L × Bool)) :
    Measurable (fun U : L → G => (l.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil]; exact measurable_const
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Measurable.mul ?_ ih
    by_cases ha : a.2 = true
    · have he : (fun U : L → G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => U a.1 :=
        funext fun U => if_pos ha
      rw [he]; exact measurable_pi_apply a.1
    · have he : (fun U : L → G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => (U a.1)⁻¹ :=
        funext fun U => if_neg ha
      rw [he]; exact (measurable_pi_apply a.1).inv

/-- `wilsonHol bd p : (L → G) → G` is measurable, for every boundary word assignment `bd` and every
plaquette `p`. It is `measurable_stepListProd` at the list `bd p`.

Measurability is in the configuration, for one fixed plaquette; joint measurability in `p` is not
stated and `P` carries no measurable structure here.

DERIVED: no numeral. -/
theorem measurable_wilsonHol [MeasurableMul₂ G] [MeasurableInv G]
    (bd : P → List (L × Bool)) (p : P) : Measurable (wilsonHol (G := G) bd p) :=
  measurable_stepListProd (G := G) (bd p)

#print axioms wilsonSymmetry
#print axioms wilson_expect_invariant
#print axioms wilsonHol_conj
#print axioms measurable_wilsonHol

end MassGap.WilsonLattice
