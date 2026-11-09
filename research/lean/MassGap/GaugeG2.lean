import Mathlib
import MassGap.GaugeInstances
import MassGap.ClayTreeG
import MassGap.ClayStatementG
import MassGap.ObserverLinkedG

/-!
# MassGap.GaugeG2 — compact `G₂` as a `GaugeGroup`

`G₂` is the stabiliser in `SO(7)` of the associative 3-form. The sign convention is Bryant's
(*Some remarks on G₂-structures*, 2005), with indices `1, …, 7` read as `Fin 7 = {0, …, 6}`:

  `φ = e¹²³ + e¹⁴⁵ + e¹⁶⁷ + e²⁴⁶ − e²⁵⁷ − e³⁴⁷ − e³⁵⁶`.

In complex coordinates `z₁ = x₂ + i x₃`, `z₂ = x₄ + i x₅`, `z₃ = x₆ + i x₇` this is
`e¹ ∧ ω + Re (dz₁ ∧ dz₂ ∧ dz₃)` with `ω = e²³ + e⁴⁵ + e⁶⁷`.

## Objects

* `e3 a b c x y z`: the elementary 3-form `eᵃᵇᶜ(x, y, z)`, the `3 × 3` determinant of the
  coordinates `a, b, c` of `x, y, z`, over any commutative ring.
* `phi3 x y z`: the 3-form `φ` above, over any commutative ring.
* `G2Sub`: the subgroup `{g ∈ SO(7) | ∀ x y z, φ(gx, gy, gz) = φ(x, y, z)}` of
  `GaugeInstances.SO 7`; `G2` is its carrier type.
* `isClosed_G2Sub`: `G2Sub` is closed in `SO(7)`, an intersection of zero sets of polynomials in
  the entries; `G2` is compact as a closed subset of the compact `SO(7)`.
* `g2Rep`: the representation `G₂ → U(7)`, `SO(7)`'s `soRep 7` restricted to `G2Sub`.

## Instances

* `instGaugeGroupG2`: compact, second-countable, Borel, with `g2Rep` faithful and continuous.
* `instGaugeSimpleG2`: `lieDim = 14`, `dualCoxeter = 4`, `dynkinIndex = 1`. These are the
  classification values, entered as constants like every other `GaugeSimple` instance; nothing here
  derives them from `G2Sub`.
* `instGaugeLieG2`: `lieGen X` is `X` Hermitian, `Xᵀ = −X` (the `SO(n)` predicate of
  `ClayTreeG.instGaugeLieSO`), and `X` a derivation of `φ`:
  `φ(Xx, y, z) + φ(x, Xy, z) + φ(x, y, Xz) = 0` for all complex `x, y, z`. A Hermitian
  antisymmetric `X` is `i B` with `B` real antisymmetric, and the derivation condition on `X` is the
  same condition on `B`, so `lieGen` cuts out `i 𝔤₂` inside `i 𝔰𝔬(7)`. That its real span has
  dimension `14` is not proved here. `lieGen_cartanM` exhibits one nonzero member, the Cartan
  generator `i (E₃₂ − E₂₃ − E₅₄ + E₄₅)` (1-based), which rotates `z₁` and `z₂` by opposite angles.

## The Dynkin index `T(7) = 1`

Normalisation of `GaugeSimple`: long roots of squared length two, in which `T(adj) = h^∨`, and at
`SO(n)`, `n ≥ 5`, `T(vector) = 1` (`GaugeInstances.instGaugeSimpleSO`). For `G₂`, `h^∨ = 4`. The
ratio `tr₇(X²) / tr_adj(X²)` is independent of the normalisation of the invariant form, and for
`G₂` equals `dim(7) C₂(7) / (dim(14) C₂(14)) = 7 · 2 / (14 · 4) = 1/4`, so
`T(7) = h^∨ / 4 = 1`. The same value follows from the embedding `G₂ ⊂ SO(7)`: the adjoint of
`SO(7)` restricts as `21 = 14 ⊕ 7`, so `T_{SO(7)}(21) = h^∨(SO(7)) = 5 = T(14) + T(7) = 4 + T(7)`;
the embedding index is `T_{G₂}(7) / T_{SO(7)}(7) = 1`, and the plaquette density of `G₂` is that
of `SO(7)` restricted (`wilsonDensityG_G2`). These are statements of the classification, recorded
for the constant `1`; the tree carries no Lie algebra from which to check them.

## The Clay statement at `G₂`

`ClayStatementG2 := ClayStatementOf G2`. Every theorem of the tree stated over a `G` with
`[GaugeGroup G] [GaugeSimple G] [GaugeLie G]` applies at `G2` through the three instances; in
particular `ObserverLinkedG.clayStatementAtG_of_observer (G := G2)` concludes
`ClayStatementAtG G2 W (SymPlaqClassG G2)` from its inputs, and `clayStatementG2_of_atG` with
`SymPlaqG.symPlaqG_refl G2` turns that into `ClayStatementOfDy G2`, the statement at the frozen tower;
`MeasuredSpacing.clayStatementMeasOf_of_of` lifts it to
`ClayStatementG2` under asymptotic scaling of the tensor mass.
-/

namespace MassGap.GaugeG2

open Matrix MeasureTheory MassGap.GaugeGroup MassGap.GaugeInstances

/-! ## The associative 3-form -/

section Form

variable {R : Type} [CommRing R]

/-- The elementary 3-form `eᵃᵇᶜ(x, y, z)`: the determinant of the `3 × 3` matrix of the coordinates
`a, b, c` of `x, y, z`, expanded along `x`.

DERIVED: `7` the dimension of the space the form lives on (the imaginary octonions, `G₂ ⊂ SO(7)`). -/
def e3 (a b c : Fin 7) (x y z : Fin 7 → R) : R :=
  x a * (y b * z c - y c * z b) - x b * (y a * z c - y c * z a) + x c * (y a * z b - y b * z a)

/-- The associative 3-form in Bryant's convention, indices shifted to `Fin 7`:
`φ = e¹²³ + e¹⁴⁵ + e¹⁶⁷ + e²⁴⁶ − e²⁵⁷ − e³⁴⁷ − e³⁵⁶`.

DERIVED: the index triples and signs are the convention stated in the module docstring; `7` the
dimension of the form. -/
def phi3 (x y z : Fin 7 → R) : R :=
  e3 0 1 2 x y z + e3 0 3 4 x y z + e3 0 5 6 x y z + e3 1 3 5 x y z
    - e3 1 4 6 x y z - e3 2 3 6 x y z - e3 2 4 5 x y z

/-- `φ` is jointly continuous in its three arguments, read along continuous maps.

DERIVED: `7` the dimension of the form. -/
theorem continuous_phi3 {X : Type} [TopologicalSpace X] {f g h : X → Fin 7 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t => phi3 (f t) (g t) (h t) := by
  have hf' : ∀ a, Continuous fun t => f t a := fun a => (continuous_apply a).comp hf
  have hg' : ∀ a, Continuous fun t => g t a := fun a => (continuous_apply a).comp hg
  have hh' : ∀ a, Continuous fun t => h t a := fun a => (continuous_apply a).comp hh
  unfold phi3 e3
  fun_prop

end Form

/-! ## `G₂ ⊆ SO(7)` -/

/-- **Compact `G₂`**: the elements of `SO(7)` preserving `φ`,
`φ(gx, gy, gz) = φ(x, y, z)` for all real `x, y, z`. Closure under inverse: `g⁻¹ = gᵀ = star g`
and `g g⁻¹ = 1`, so `φ(g⁻¹x, g⁻¹y, g⁻¹z) = φ(g g⁻¹x, g g⁻¹y, g g⁻¹z) = φ(x, y, z)`.

DERIVED: `7` the dimension of the form. -/
def G2Sub : Subgroup (SO 7) where
  carrier := {g | ∀ x y z : Fin 7 → ℝ,
    phi3 ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ x) ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ y)
      ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ z) = phi3 x y z}
  mul_mem' := by
    intro a b ha hb x y z
    show phi3 (((a : Matrix (Fin 7) (Fin 7) ℝ) * (b : Matrix (Fin 7) (Fin 7) ℝ)) *ᵥ x)
      (((a : Matrix (Fin 7) (Fin 7) ℝ) * (b : Matrix (Fin 7) (Fin 7) ℝ)) *ᵥ y)
      (((a : Matrix (Fin 7) (Fin 7) ℝ) * (b : Matrix (Fin 7) (Fin 7) ℝ)) *ᵥ z) = phi3 x y z
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro x y z
    show phi3 ((1 : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ x) ((1 : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ y)
      ((1 : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ z) = phi3 x y z
    rw [Matrix.one_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
  inv_mem' := by
    intro a ha x y z
    have hu : (a : Matrix (Fin 7) (Fin 7) ℝ) * star (a : Matrix (Fin 7) (Fin 7) ℝ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp a.2).1
    show phi3 (star (a : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ x)
      (star (a : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ y) (star (a : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ z)
      = phi3 x y z
    have h := ha (star (a : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ x)
      (star (a : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ y) (star (a : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact h.symm

/-- Compact `G₂` as a type. -/
abbrev G2 : Type := ↥G2Sub

/-- Membership in `G2Sub` is invariance of `φ`. DERIVED: `7` the dimension of the form. -/
theorem mem_G2Sub_iff (g : SO 7) :
    g ∈ G2Sub ↔ ∀ x y z : Fin 7 → ℝ,
      phi3 ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ x) ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ y)
        ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ z) = phi3 x y z :=
  Iff.rfl

/-- **`G2Sub` is closed in `SO(7)`**: the intersection over `x, y, z` of the zero sets of the
continuous maps `g ↦ φ(gx, gy, gz) − φ(x, y, z)`.

DERIVED: `7` the dimension of the form. -/
theorem isClosed_G2Sub : IsClosed (G2Sub : Set (SO 7)) := by
  have hset : (G2Sub : Set (SO 7)) = ⋂ x : Fin 7 → ℝ, ⋂ y : Fin 7 → ℝ, ⋂ z : Fin 7 → ℝ,
      {g : SO 7 | phi3 ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ x) ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ y)
        ((g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ z) = phi3 x y z} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_G2Sub_iff g
  rw [hset]
  have hv : ∀ v : Fin 7 → ℝ, Continuous fun g : SO 7 => (g : Matrix (Fin 7) (Fin 7) ℝ) *ᵥ v :=
    fun v => continuous_subtype_val.matrix_mulVec continuous_const
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
    isClosed_eq (continuous_phi3 (hv x) (hv y) (hv z)) continuous_const

instance : CompactSpace G2 := isCompact_iff_compactSpace.mp isClosed_G2Sub.isCompact

noncomputable instance : MeasurableSpace G2 := borel _
instance : BorelSpace G2 := ⟨rfl⟩

instance : SecondCountableTopology G2 :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

/-! ## The representation and the instances -/

/-- The 7-dimensional representation `G₂ → U(7)`: `soRep 7` restricted to `G2Sub`,
`g ↦ g.map ofReal`.

DERIVED: `7` the dimension. -/
noncomputable def g2Rep : G2 →* Matrix.unitaryGroup (Fin 7) ℂ :=
  (soRep 7).comp G2Sub.subtype

/-- **`G₂` as a `GaugeGroup`**: compact, second-countable, Borel, with the faithful continuous `g2Rep`.

DERIVED: `7` the dimension of the representation `g2Rep`. -/
noncomputable instance instGaugeGroupG2 : GaugeGroup G2 where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := 7
  repDim_pos := by norm_num
  rep := g2Rep
  continuous_rep := by
    have h : Continuous fun g : SO 7 =>
        ((soRep 7 g : Matrix.unitaryGroup (Fin 7) ℂ) : Matrix (Fin 7) (Fin 7) ℂ) :=
      continuous_subtype_val.matrix_map Complex.continuous_ofReal
    exact h.comp continuous_subtype_val
  rep_injective := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have := congrArg
      (fun U : Matrix.unitaryGroup (Fin 7) ℂ => (U : Matrix (Fin 7) (Fin 7) ℂ) i j) hgh
    exact Complex.ofReal_injective this

theorem dim_G2 : GaugeGroup.dim G2 = 7 := rfl

/-- The Wilson density of `G₂` is that of `SO(7)` at the same matrix: `1 − tr g / 7`.

DERIVED: no numeral beyond the density's own `1`; `7` the dimension of the representation. -/
theorem wilsonDensityG_G2 (g : G2) :
    wilsonDensityG G2 g = wilsonDensityG (SO 7) (g : SO 7) := rfl

/-- **`G₂`**: `dim 𝔤 = 14`, `h^∨ = 4`, `T(7) = 1`. Classification values in the normalisation of
`GaugeSimple`; the derivation of `T(7) = 1` from `h^∨ = 4` and the embedding `G₂ ⊂ SO(7)` is in the
module docstring. Nothing here derives them from `G2Sub`.

DERIVED: `14`, `4`, `1` are the classification values. -/
noncomputable instance instGaugeSimpleG2 : GaugeSimple G2 where
  lieDim := 14
  dualCoxeter := 4
  dynkinIndex := 1
  dualCoxeter_pos := by norm_num
  dynkinIndex_pos := one_pos

/-- **The Hermitian generators of `ρ(𝔤₂)`**: `X` Hermitian, `Xᵀ = −X`, and `X` a derivation of `φ`
over `ℂ`. `14 > 0`.

DERIVED: `0` the derivation condition; `14` the dimension. -/
instance instGaugeLieG2 : MassGap.ClayTreeG.GaugeLie G2 where
  lieGen M := M.IsHermitian ∧ M.transpose = -M ∧
    ∀ x y z : Fin 7 → ℂ, phi3 (M *ᵥ x) y z + phi3 x (M *ᵥ y) z + phi3 x y (M *ᵥ z) = 0
  lieDim_pos := by
    show 0 < 14
    norm_num

/-! ## One generator -/

/-- The real Cartan generator `E₃₂ − E₂₃ − E₅₄ + E₄₅` (1-based): it rotates the `(x₂, x₃)` plane by
`+1` and the `(x₄, x₅)` plane by `−1`, i.e. `z₁ ↦ e^{it} z₁`, `z₂ ↦ e^{−it} z₂`.

DERIVED: the entries `±1` are the two opposite unit angles; `7` the dimension. -/
def cartanB : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of ![![0, 0, 0, 0, 0, 0, 0],
              ![0, 0, -1, 0, 0, 0, 0],
              ![0, 1, 0, 0, 0, 0, 0],
              ![0, 0, 0, 0, 1, 0, 0],
              ![0, 0, 0, -1, 0, 0, 0],
              ![0, 0, 0, 0, 0, 0, 0],
              ![0, 0, 0, 0, 0, 0, 0]]

/-- The Hermitian generator `i · cartanB`. DERIVED: `7` the dimension. -/
noncomputable def cartanM : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.of fun i j => Complex.I * (cartanB i j : ℂ)

/-- **`cartanM` is a generator of `ρ(𝔤₂)`** in the sense of `instGaugeLieG2`, and it is nonzero:
`lieGen` is not the zero predicate.

DERIVED: the index `(2, 1)` is the entry `i`. -/
theorem lieGen_cartanM :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := G2) cartanM ∧ cartanM ≠ 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show cartanM.conjTranspose = cartanM
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cartanM, cartanB, Matrix.conjTranspose_apply]
  · show cartanM.transpose = -cartanM
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cartanM, cartanB]
  · have hM : ∀ v : Fin 7 → ℂ, (cartanM *ᵥ v) 0 = 0 ∧ (cartanM *ᵥ v) 1 = -(Complex.I * v 2)
        ∧ (cartanM *ᵥ v) 2 = Complex.I * v 1 ∧ (cartanM *ᵥ v) 3 = Complex.I * v 4
        ∧ (cartanM *ᵥ v) 4 = -(Complex.I * v 3) ∧ (cartanM *ᵥ v) 5 = 0
        ∧ (cartanM *ᵥ v) 6 = 0 := by
      intro v
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [cartanM, cartanB, Matrix.mulVec, dotProduct, Fin.sum_univ_seven]
    intro x y z
    obtain ⟨x0, x1, x2, x3, x4, x5, x6⟩ := hM x
    obtain ⟨y0, y1, y2, y3, y4, y5, y6⟩ := hM y
    obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := hM z
    simp only [phi3, e3, x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6,
      z0, z1, z2, z3, z4, z5, z6]
    ring
  · intro h
    have h21 := congrFun (congrFun h 2) 1
    simp [cartanM, cartanB] at h21

/-! ## The Clay statement at `G₂` -/

open MassGap.ClayTreeG MassGap.ClayStatementG MassGap.SymPlaqG

/-- **The Clay Yang–Mills statement for `G₂`**: `ClayStatementOf` at `G2`.

DERIVED: no numeral. -/
def ClayStatementG2 : Prop := ClayStatementOf G2

/-- **`ClayStatementOfDy G2`, the statement at the frozen tower, from
`ClayStatementAtG` on the symmetrised plaquette class**, which is
reflection closed (`symPlaqG_refl`). `ObserverLinkedG.clayStatementAtG_of_observer (G := G2)`
concludes the hypothesis from its inputs.

DERIVED: no numeral. -/
theorem clayStatementG2_of_atG (W : ConfFlowG G2)
    (h : ClayStatementAtG G2 W (SymPlaqClassG G2)) : ClayStatementOfDy G2 :=
  ⟨W, SymPlaqClassG G2, symPlaqG_refl G2, h⟩

-- The observer capstone elaborates at `G₂`: the six instance arguments resolve, and its conclusion
-- is `ClayStatementAtG G2 W (SymPlaqClassG G2)`, the hypothesis of `clayStatementG2_of_atG`.
example : True := by
  have _h := @MassGap.ObserverLinkedG.clayStatementAtG_of_observer G2 _ _ _ _ _ _
  trivial

end MassGap.GaugeG2

#print axioms MassGap.GaugeG2.continuous_phi3
#print axioms MassGap.GaugeG2.G2Sub
#print axioms MassGap.GaugeG2.isClosed_G2Sub
#print axioms MassGap.GaugeG2.g2Rep
#print axioms MassGap.GaugeG2.instGaugeGroupG2
#print axioms MassGap.GaugeG2.wilsonDensityG_G2
#print axioms MassGap.GaugeG2.instGaugeSimpleG2
#print axioms MassGap.GaugeG2.instGaugeLieG2
#print axioms MassGap.GaugeG2.lieGen_cartanM
#print axioms MassGap.GaugeG2.clayStatementG2_of_atG
