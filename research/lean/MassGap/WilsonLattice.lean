import MassGap.LatticeGauge

/-!
# MassGap.WilsonLattice — real plaquette holonomies with tractable symmetry (dynamical face, brick 2)

The `LatticeGauge.System` holonomy `hol` was abstract. Here we give it the genuine Wilson form — the
**ordered product of link variables around a plaquette loop** — while keeping the Euclidean/permutation
`compat` obligation tractable. The trick: present each plaquette by its **boundary word**, an ordered
list of `(link, orientation)` pairs (orientation `true` = the link, `false` = its inverse). Then

  `hol p U = ∏ over the boundary word of p`  (a real Wilson loop),

and a lattice symmetry that relabels links/plaquettes so that boundary words map compatibly makes
`compat` a one-line `List.map`/`List.prod` reindexing — no lattice-coordinate arithmetic. Lattice
rotations "permuting plaquettes with matching holonomy" is exactly the `hbd` hypothesis below.

Combined with `WilsonAction.wilsonDensity` as `φ`, `wilsonSystem` is a genuine Wilson gauge theory whose
Gibbs correlations are Euclidean/permutation-invariant by `wilson_expect_invariant` — the A1 payoff on a
real action. Foundational footprint only. Build: `lake build MassGap.WilsonLattice`.
-/

namespace MassGap.WilsonLattice

open MassGap.LatticeGauge

variable {G : Type} [Group G] [MeasurableSpace G] {L P : Type}

/-- The ordered plaquette holonomy from a boundary word: the product `∏ (Uₗ or Uₗ⁻¹)` along the loop,
in order (`true` = forward link, `false` = inverse). A genuine Wilson loop. -/
def wilsonHol (bd : P → List (L × Bool)) (p : P) (U : L → G) : G :=
  ((bd p).map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod

/-- A finite lattice gauge system whose holonomy is the ordered plaquette loop of a boundary word,
with plaquette action density `φ` (e.g. `WilsonAction.wilsonDensity`). -/
def wilsonSystem [Fintype L] [Fintype P]
    (bd : P → List (L × Bool)) (φ : G → ℝ) : System G where
  Link := L
  Plaq := P
  hol := wilsonHol bd
  φ := φ

/-- **A boundary-relabelling symmetry.** Link/plaquette permutations `σL, σP` that map boundary words
compatibly (`hbd`: the boundary of the permuted plaquette is the `σL`-relabelled boundary word) yield a
genuine `Symmetry` of the Wilson system. `compat` is a `List.map`/`prod` reindexing — the honest content
of "a lattice rotation permutes plaquettes with matching holonomy." -/
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

/-- **Euclidean/permutation invariance of the Wilson Gibbs correlation, on the real action.** For any
boundary-relabelling symmetry and any left-invariant probability measure `μ` on the gauge group, the
Gibbs expectation of an observable is invariant under transporting it by the symmetry — derived from
Haar-invariance (`Symmetry.expect_invariant`), now on a genuine ordered-loop Wilson holonomy. -/
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

/-- Product of conjugates is the conjugate of the product: `∏ (g xᵢ g⁻¹) = g (∏ xᵢ) g⁻¹`. -/
theorem list_prod_conj (g : G) (xs : List G) :
    (xs.map (fun x => g * x * g⁻¹)).prod = g * xs.prod * g⁻¹ := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.prod_cons, ih]; group

/-- **The Wilson holonomy conjugates under a global gauge transformation.** Conjugating every link
variable by a fixed `g` conjugates the plaquette holonomy: `hol p (g U g⁻¹) = g · hol p U · g⁻¹`
(conjugation distributes over the ordered loop product, orientations included). This is the algebraic
core of gauge invariance — the global/centre subgroup — needing no measure input. -/
theorem wilsonHol_conj (bd : P → List (L × Bool)) (g : G) (p : P) (U : L → G) :
    wilsonHol bd p (fun l => g * U l * g⁻¹) = g * wilsonHol bd p U * g⁻¹ := by
  unfold wilsonHol
  rw [← list_prod_conj g, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro lo _
  simp only [Function.comp_apply]
  cases h : lo.2 <;> simp [h, mul_inv_rev, mul_assoc]

/-! ### Measurability of the holonomy -/

/-- The ordered product of link-dependent step factors is measurable (list induction). -/
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

/-- **The Wilson plaquette holonomy is measurable** in the configuration — needed for the integrability
of the Gibbs weight and for a rigorous Wilson measure. -/
theorem measurable_wilsonHol [MeasurableMul₂ G] [MeasurableInv G]
    (bd : P → List (L × Bool)) (p : P) : Measurable (wilsonHol (G := G) bd p) :=
  measurable_stepListProd (G := G) (bd p)

#print axioms wilsonSymmetry
#print axioms wilson_expect_invariant
#print axioms wilsonHol_conj
#print axioms measurable_wilsonHol

end MassGap.WilsonLattice
