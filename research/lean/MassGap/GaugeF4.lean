import Mathlib
import MassGap.GaugeInstances
import MassGap.GaugeG2
import MassGap.ClayTreeG
import MassGap.ClayStatementG
import MassGap.ObserverLinkedG

/-!
# MassGap.GaugeF4 — compact `F₄` as a `GaugeGroup`

`F₄` is the automorphism group of the exceptional Jordan algebra `J = J₃(𝕆)` of `3 × 3` octonionic
Hermitian matrices. Here it is the stabiliser in `SO(26)` of the determinant restricted to the
traceless part `J₀`, written in orthonormal coordinates of the trace form.

## Conventions

*Octonions.* `𝕆 = ℝ ⊕ Im 𝕆 = ℝ⁸`, index `0` the real part and `1, …, 7` the imaginary part
(`im7 x i = x (i + 1)`). The cross product on `Im 𝕆 = ℝ⁷` is read off the 3-form `GaugeG2.phi3`
(Bryant's convention), `⟨x × y, z⟩ = φ(x, y, z)` (`dot7_cross`), and the product is

  `x y = (x₀ y₀ − ⟨x', y'⟩, x₀ y' + y₀ x' + x' × y')`  (`octMul`),

so that `Re((x y) z) = x₀y₀z₀ − z₀⟨x', y'⟩ − x₀⟨y', z'⟩ − y₀⟨x', z'⟩ − φ(x', y', z')`
(`octRe3_eq`, which is the definition of `octRe3` read through `octMul`).

*The Jordan algebra.* `X = [[a, z, ȳ], [z̄, b, x], [y, x̄, c]]` with `a, b, c ∈ ℝ`, `x, y, z ∈ 𝕆`,
and `det X = abc − a n(x) − b n(y) − c n(z) + 2 Re(x y z)`. The trace form
`tr(X²) = a² + b² + c² + 2(n(x) + n(y) + n(z))` is made Euclidean on `J₀` by the coordinates
`v : Fin 26 → ℝ`: `v 0 = u`, `v 1 = w` with `a = u/√2 + w/√6`, `b = −u/√2 + w/√6`, `c = −2w/√6`, and
`x = (v 2, …, v 9)/√2`, `y = (v 10, …, v 17)/√2`, `z = (v 18, …, v 25)/√2`. In these coordinates
`6√6 · det X` is

  `d(v) = 6u²w − 2w³ − 3(s u + w) n(x) + 3(s u − w) n(y) + 6 w n(z) + 6 s Re((x y) z)`,

`s = √3`, with `x, y, z` now the unscaled blocks of `v` (`f4Cubic`). The `√3` is the one irrational
the orthonormal traceless diagonal forces (its three weight directions sit at `120°`); it enters as
a parameter `s` so that the form is defined over any commutative ring and is evaluated at
`s = √3` in `ℝ` and at its image in `ℂ`.

## Objects

* `f4Tri s p q r`: a trilinear form with `f4Tri s v v v = f4Cubic s v`. It is not symmetric; only
  its diagonal and its derivative along a matrix enter below.
* `F4Sub`: `{g ∈ SO(26) | ∀ v, d(g v) = d(v)}`; `F4` is its carrier type.
* `isClosed_F4Sub`, compactness: as for `G₂`, an intersection of zero sets of polynomials in the
  entries, closed in the compact `SO(26)`.
* `f4Rep`: `soRep 26` restricted to `F4Sub`, `F₄ → U(26)`.

That `F4Sub` is the compact group `F₄` is the classification statement (an element of `O(J₀)`
fixing `d` extends by `1 ↦ 1` to an element of `O(J)` fixing `det`, since
`det(t·1 + X) = t³ − t tr(X²)/2 + det X` on `J₀`, hence to an automorphism of `J`); it is not
proved here. `research/code/f4_checks.py` checks numerically, in exactly these coordinates, that
the stabiliser algebra `{B ∈ 𝔰𝔬(26) | ∇d(v) · B v = 0}` has dimension `52` and is closed under the
bracket, and that `d = 6√6 det` with the coordinates orthonormal for `tr(X²)`.

## Instances

* `instGaugeGroupF4`: compact, second-countable, Borel, `f4Rep` faithful and continuous.
* `instGaugeSimpleF4`: `lieDim = 52`, `dualCoxeter = 9`, `dynkinIndex = 3`, the classification
  values entered as constants like every other `GaugeSimple` instance; nothing here derives them
  from `F4Sub`.
* `instGaugeLieF4`: `lieGen M` is `M` Hermitian, `Mᵀ = −M`, and `M` a derivation of the complexified
  cubic, `f4Tri(Mx, x, x) + f4Tri(x, Mx, x) + f4Tri(x, x, Mx) = 0` for all complex `x`, the
  derivative of `d` at `x` along `M x`. For `M = i B`, `B` real antisymmetric, this is the same
  condition on `B`, so `lieGen` cuts out `i 𝔣₄` inside `i 𝔰𝔬(26)`; that its real span has
  dimension `52` is the numerical check above, not a theorem here. `lieGen_cartanF4` exhibits one
  nonzero member: `GaugeG2.cartanM`'s generator acting on the imaginary parts of the three
  octonion blocks at once (a `G₂ ⊂ F₄` generator, acting by derivations of `𝕆`).

## The Dynkin index `T(26) = 3`

Normalisation of `GaugeSimple`: long roots of squared length two, `T(adj) = h^∨`, and
`T(vector) = 1` at `SO(n)`, `n ≥ 5`. For `F₄`, `h^∨ = 9`. The ratio `tr₂₆(X²) / tr_adj(X²)` does
not depend on the normalisation and equals `T(26)/T(52) = dim(26) C₂(26) / (dim(52) C₂(52))`; with
`C₂(adj) = 9`, `C₂(26) = 6` it is `26 · 6 / (52 · 9) = 1/3`, so `T(26) = 9/3 = 3`.
`f4_checks.py` computes the ratio on the stabiliser algebra of `d` and finds `1/3`. The embedding
`Spin(9) ⊂ F₄` gives the same value: `52 = 36 ⊕ 16` and `26 = 1 ⊕ 9 ⊕ 16`, with
`T_{SO(9)}(36) = h^∨(SO(9)) = 7`, `T_{SO(9)}(9) = 1`, `T_{SO(9)}(16) = 2`; so `7 + 2 = 9 = h^∨(F₄)`
(embedding index one) and `T(26) = 0 + 1 + 2 = 3`. These are statements of the classification and
of the numerics, recorded for the constant `3`; the tree carries no Lie algebra from which to
check them.

## The Clay statement at `F₄`

`ClayStatementF4 := ClayStatementOf F4`; `ObserverLinkedG.clayStatementAtG_of_observer (G := F4)`
elaborates, and `clayStatementF4_of_atG` with `SymPlaqG.symPlaqG_refl F4` turns its conclusion
into `ClayStatementOfDy F4`, the statement at the frozen tower;
`MeasuredSpacing.clayStatementMeasOf_of_of` lifts it to
`ClayStatementF4` under asymptotic scaling of the tensor mass.
-/

namespace MassGap.GaugeF4

open Matrix MeasureTheory MassGap.GaugeGroup MassGap.GaugeInstances MassGap.GaugeG2

/-! ## Octonions from the `G₂` 3-form -/

section Oct

variable {R : Type} [CommRing R]

/-- The Euclidean pairing on `ℝ⁷`. DERIVED: `7 = 8 − 1` the imaginary octonion directions. -/
def dot7 (x y : Fin 7 → R) : R := ∑ i, x i * y i

/-- The Euclidean pairing on `ℝ⁸`. DERIVED: `8` the real dimension of `𝕆`. -/
def dot8 (x y : Fin 8 → R) : R := ∑ i, x i * y i

/-- The imaginary part of an octonion, coordinates `1, …, 7`. DERIVED: `8` the real dimension of `𝕆`;
`7 = 8 − 1` its imaginary directions. -/
def im7 (x : Fin 8 → R) : Fin 7 → R := fun i => x i.succ

/-- The cross product on `ℝ⁷` with `⟨x × y, z⟩ = φ(x, y, z)` (`dot7_cross`), `φ = GaugeG2.phi3`.

DERIVED: the coefficients are those of `φ`, checked by `dot7_cross`. -/
def cross (x y : Fin 7 → R) : Fin 7 → R :=
  ![x 1 * y 2 - x 2 * y 1 + x 3 * y 4 - x 4 * y 3 + x 5 * y 6 - x 6 * y 5,
    x 2 * y 0 - x 0 * y 2 + x 3 * y 5 - x 5 * y 3 - x 4 * y 6 + x 6 * y 4,
    x 0 * y 1 - x 1 * y 0 - x 3 * y 6 + x 6 * y 3 - x 4 * y 5 + x 5 * y 4,
    x 4 * y 0 - x 0 * y 4 + x 5 * y 1 - x 1 * y 5 - x 6 * y 2 + x 2 * y 6,
    x 0 * y 3 - x 3 * y 0 - x 6 * y 1 + x 1 * y 6 - x 5 * y 2 + x 2 * y 5,
    x 6 * y 0 - x 0 * y 6 + x 1 * y 3 - x 3 * y 1 - x 2 * y 4 + x 4 * y 2,
    x 0 * y 5 - x 5 * y 0 - x 1 * y 4 + x 4 * y 1 - x 2 * y 3 + x 3 * y 2]

/-- **The cross product is the one of `φ`**: `⟨x × y, z⟩ = φ(x, y, z)`.

DERIVED: `7 = 8 − 1` the imaginary octonion directions. -/
theorem dot7_cross (x y z : Fin 7 → R) : dot7 (cross x y) z = phi3 x y z := by
  simp only [dot7, cross, phi3, e3, Fin.sum_univ_seven, Matrix.cons_val]
  ring

/-- **The octonion product** `x y = (x₀ y₀ − ⟨x', y'⟩, x₀ y' + y₀ x' + x' × y')`.

DERIVED: `8` the real dimension of `𝕆`. -/
def octMul (x y : Fin 8 → R) : Fin 8 → R :=
  Fin.cons (x 0 * y 0 - dot7 (im7 x) (im7 y))
    (fun k => x 0 * im7 y k + y 0 * im7 x k + cross (im7 x) (im7 y) k)

/-- `Re((x y) z)` in terms of `φ`:
`x₀y₀z₀ − z₀⟨x', y'⟩ − x₀⟨y', z'⟩ − y₀⟨x', z'⟩ − φ(x', y', z')`.

DERIVED: `8` the real dimension of `𝕆`. -/
def octRe3 (x y z : Fin 8 → R) : R :=
  x 0 * y 0 * z 0 - z 0 * dot7 (im7 x) (im7 y) - x 0 * dot7 (im7 y) (im7 z)
    - y 0 * dot7 (im7 x) (im7 z) - phi3 (im7 x) (im7 y) (im7 z)

/-- **`octRe3` is the real part of `(x y) z`** for the product `octMul`.

DERIVED: `8` the real dimension of `𝕆`. -/
theorem octRe3_eq (x y z : Fin 8 → R) : octRe3 x y z = octMul (octMul x y) z 0 := by
  rw [octRe3, ← dot7_cross]
  simp only [octMul, Fin.cons_zero, im7, Fin.cons_succ, dot7, Fin.sum_univ_seven]
  ring

end Oct

/-! ## The cubic form on the traceless exceptional Jordan algebra -/

section Cubic

variable {R : Type} [CommRing R]

/-- The octonion `x`, coordinates `2, …, 9`. DERIVED: the block offset; `8` the real dimension of `𝕆`;
`26 = 27 − 1 = (3 + 3 · 8) − 1` the dimension of the traceless part of `J₃(𝕆)`. -/
def xo (v : Fin 26 → R) : Fin 8 → R := ![v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9]

/-- The octonion `y`, coordinates `10, …, 17`. DERIVED: the block offset; `8` the real dimension of `𝕆`;
`26 = 27 − 1 = (3 + 3 · 8) − 1` the dimension of the traceless part of `J₃(𝕆)`. -/
def yo (v : Fin 26 → R) : Fin 8 → R := ![v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17]

/-- The octonion `z`, coordinates `18, …, 25`. DERIVED: the block offset; `8` the real dimension of `𝕆`;
`26 = 27 − 1 = (3 + 3 · 8) − 1` the dimension of the traceless part of `J₃(𝕆)`. -/
def zo (v : Fin 26 → R) : Fin 8 → R := ![v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25]

/-- A trilinear form whose diagonal is the cubic `f4Cubic`; `s` stands for `√3`.

DERIVED: `6, 2, 3, 6, 6` are `6√6 det` in the orthonormal coordinates of the module docstring;
`26` the dimension of the traceless part of `J₃(𝕆)`. -/
def f4Tri (s : R) (p q r : Fin 26 → R) : R :=
  6 * p 0 * q 0 * r 1 - 2 * p 1 * q 1 * r 1
    - 3 * (s * p 0 + p 1) * dot8 (xo q) (xo r) + 3 * (s * p 0 - p 1) * dot8 (yo q) (yo r)
    + 6 * p 1 * dot8 (zo q) (zo r) + 6 * s * octRe3 (xo p) (yo q) (zo r)

/-- **The cubic form** `d(v) = 6√6 det X` on the traceless part of `J₃(𝕆)`, with `s = √3`:
`6u²w − 2w³ − 3(su + w) n(x) + 3(su − w) n(y) + 6w n(z) + 6s Re((xy)z)`.

DERIVED: no numeral beyond those of `f4Tri`; `26` the dimension of the traceless part of `J₃(𝕆)`. -/
def f4Cubic (s : R) (v : Fin 26 → R) : R := f4Tri s v v v

end Cubic

/-- `d` is continuous along continuous maps into `ℝ²⁶`.

DERIVED: `26` the dimension of the traceless part of `J₃(𝕆)`. -/
theorem continuous_f4Cubic {X : Type} [TopologicalSpace X] (s : ℝ) {f : X → Fin 26 → ℝ}
    (hf : Continuous f) : Continuous fun t => f4Cubic s (f t) := by
  have hf' : ∀ a, Continuous fun t => f t a := fun a => (continuous_apply a).comp hf
  simp only [f4Cubic, f4Tri, octRe3, dot7, dot8, im7, xo, yo, zo, phi3, e3, Fin.sum_univ_seven,
    Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val]
  fun_prop

/-! ## `F₄ ⊆ SO(26)` -/

/-- `√3` in `ℝ`, the parameter of the cubic. DERIVED: `3` from the orthonormal traceless diagonal
(three weight directions at `120°`; module docstring). -/
noncomputable abbrev s3 : ℝ := Real.sqrt 3

/-- **Compact `F₄`**: the elements of `SO(26)` preserving the cubic form `d`,
`d(g v) = d(v)` for all real `v`. Closure under inverse: `g⁻¹ = gᵀ = star g` with `g g⁻¹ = 1`.

DERIVED: `26` the dimension of the traceless part. -/
noncomputable def F4Sub : Subgroup (SO 26) where
  carrier := {g | ∀ v : Fin 26 → ℝ,
    f4Cubic s3 ((g : Matrix (Fin 26) (Fin 26) ℝ) *ᵥ v) = f4Cubic s3 v}
  mul_mem' := by
    intro a b ha hb v
    show f4Cubic s3 (((a : Matrix (Fin 26) (Fin 26) ℝ) * (b : Matrix (Fin 26) (Fin 26) ℝ)) *ᵥ v)
      = f4Cubic s3 v
    rw [← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v
    show f4Cubic s3 ((1 : Matrix (Fin 26) (Fin 26) ℝ) *ᵥ v) = f4Cubic s3 v
    rw [Matrix.one_mulVec]
  inv_mem' := by
    intro a ha v
    have hu : (a : Matrix (Fin 26) (Fin 26) ℝ) * star (a : Matrix (Fin 26) (Fin 26) ℝ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp a.2).1
    show f4Cubic s3 (star (a : Matrix (Fin 26) (Fin 26) ℝ) *ᵥ v) = f4Cubic s3 v
    have h := ha (star (a : Matrix (Fin 26) (Fin 26) ℝ) *ᵥ v)
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] at h
    exact h.symm

/-- Compact `F₄` as a type. -/
abbrev F4 : Type := ↥F4Sub

/-- Membership in `F4Sub` is invariance of `d`. DERIVED: `26` the dimension of the traceless part. -/
theorem mem_F4Sub_iff (g : SO 26) :
    g ∈ F4Sub ↔ ∀ v : Fin 26 → ℝ,
      f4Cubic s3 ((g : Matrix (Fin 26) (Fin 26) ℝ) *ᵥ v) = f4Cubic s3 v :=
  Iff.rfl

/-- **`F4Sub` is closed in `SO(26)`**: the intersection over `v` of the zero sets of the continuous
maps `g ↦ d(g v) − d(v)`.

DERIVED: `26` the dimension of the traceless part. -/
theorem isClosed_F4Sub : IsClosed (F4Sub : Set (SO 26)) := by
  have hset : (F4Sub : Set (SO 26)) = ⋂ v : Fin 26 → ℝ,
      {g : SO 26 | f4Cubic s3 ((g : Matrix (Fin 26) (Fin 26) ℝ) *ᵥ v) = f4Cubic s3 v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_F4Sub_iff g
  rw [hset]
  exact isClosed_iInter fun v => isClosed_eq
    (continuous_f4Cubic s3 (continuous_subtype_val.matrix_mulVec continuous_const))
    continuous_const

instance : CompactSpace F4 := isCompact_iff_compactSpace.mp isClosed_F4Sub.isCompact

noncomputable instance : MeasurableSpace F4 := borel _
instance : BorelSpace F4 := ⟨rfl⟩

instance : SecondCountableTopology F4 :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

/-! ## The representation and the instances -/

/-- The 26-dimensional representation `F₄ → U(26)`: `soRep 26` restricted to `F4Sub`.

DERIVED: `26` the dimension. -/
noncomputable def f4Rep : F4 →* Matrix.unitaryGroup (Fin 26) ℂ :=
  (soRep 26).comp F4Sub.subtype

/-- **`F₄` is a `GaugeGroup`** through `f4Rep`. DERIVED: `26` the dimension of the representation. -/
noncomputable instance instGaugeGroupF4 : GaugeGroup F4 where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := 26
  repDim_pos := by norm_num
  rep := f4Rep
  continuous_rep := by
    have h : Continuous fun g : SO 26 =>
        ((soRep 26 g : Matrix.unitaryGroup (Fin 26) ℂ) : Matrix (Fin 26) (Fin 26) ℂ) :=
      continuous_subtype_val.matrix_map Complex.continuous_ofReal
    exact h.comp continuous_subtype_val
  rep_injective := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have := congrArg
      (fun U : Matrix.unitaryGroup (Fin 26) ℂ => (U : Matrix (Fin 26) (Fin 26) ℂ) i j) hgh
    exact Complex.ofReal_injective this

theorem dim_F4 : GaugeGroup.dim F4 = 26 := rfl

/-- The Wilson density of `F₄` is that of `SO(26)` at the same matrix: `1 − tr g / 26`.

DERIVED: no numeral beyond the density's own `1`; `26` the dimension of the representation. -/
theorem wilsonDensityG_F4 (g : F4) :
    wilsonDensityG F4 g = wilsonDensityG (SO 26) (g : SO 26) := rfl

/-- **`F₄`**: `dim 𝔤 = 52`, `h^∨ = 9`, `T(26) = 3`. Classification values in the normalisation of
`GaugeSimple`; the derivation of `T(26) = 3` (trace ratio `1/3`, and `Spin(9) ⊂ F₄`) is in the
module docstring. Nothing here derives them from `F4Sub`.

DERIVED: `52`, `9`, `3` are the classification values. -/
noncomputable instance instGaugeSimpleF4 : GaugeSimple F4 where
  lieDim := 52
  dualCoxeter := 9
  dynkinIndex := 3
  dualCoxeter_pos := by norm_num
  dynkinIndex_pos := by norm_num

/-- `√3` in `ℂ`, the parameter of the complexified cubic. DERIVED: `3` as in `s3`. -/
noncomputable abbrev s3C : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

/-- **The Hermitian generators of `ρ(𝔣₄)`**: `M` Hermitian, `Mᵀ = −M`, and `M` a derivation of the
complexified cubic: `f4Tri(Mx, x, x) + f4Tri(x, Mx, x) + f4Tri(x, x, Mx) = 0` for all complex `x`.
`52 > 0`.

DERIVED: `0` the derivation condition; `52` the dimension. -/
noncomputable instance instGaugeLieF4 : MassGap.ClayTreeG.GaugeLie F4 where
  lieGen M := M.IsHermitian ∧ M.transpose = -M ∧
    ∀ x : Fin 26 → ℂ,
      f4Tri s3C (M *ᵥ x) x x + f4Tri s3C x (M *ᵥ x) x + f4Tri s3C x x (M *ᵥ x) = 0
  lieDim_pos := by
    show 0 < 52
    norm_num

/-! ## One generator -/

/-- The generator `GaugeG2.cartanM` on the imaginary parts of the three octonion blocks:
`i (E₅₄ − E₄₅ + E₆₇ − E₇₆)` (0-based) and its translates by `8` and `16`.

DERIVED: the entries `±i` are those of `GaugeG2.cartanM` at the block offsets `3, 11, 19`; `26` the
dimension of the representation. -/
noncomputable def cartanF4 : Matrix (Fin 26) (Fin 26) ℂ :=
  Matrix.single 4 5 (-Complex.I) + Matrix.single 5 4 Complex.I
    + Matrix.single 6 7 Complex.I + Matrix.single 7 6 (-Complex.I)
    + Matrix.single 12 13 (-Complex.I) + Matrix.single 13 12 Complex.I
    + Matrix.single 14 15 Complex.I + Matrix.single 15 14 (-Complex.I)
    + Matrix.single 20 21 (-Complex.I) + Matrix.single 21 20 Complex.I
    + Matrix.single 22 23 Complex.I + Matrix.single 23 22 (-Complex.I)

/-- `cartanF4` on a vector. DERIVED: `26` the dimension of the representation. -/
noncomputable def cartanF4Vec (x : Fin 26 → ℂ) : Fin 26 → ℂ :=
  ![0, 0, 0, 0, -Complex.I * x 5, Complex.I * x 4, Complex.I * x 7, -Complex.I * x 6,
    0, 0, 0, 0, -Complex.I * x 13, Complex.I * x 12, Complex.I * x 15, -Complex.I * x 14,
    0, 0, 0, 0, -Complex.I * x 21, Complex.I * x 20, Complex.I * x 23, -Complex.I * x 22,
    0, 0]

theorem cartanF4_mulVec (x : Fin 26 → ℂ) : cartanF4 *ᵥ x = cartanF4Vec x := by
  simp only [cartanF4, Matrix.add_mulVec, Matrix.single_mulVec]
  ext k
  fin_cases k <;> simp [cartanF4Vec]

/-- **`cartanF4` is a generator of `ρ(𝔣₄)`** in the sense of `instGaugeLieF4`, and it is nonzero:
`lieGen` is not the zero predicate.

DERIVED: the index `(5, 4)` is the entry `i`. -/
theorem lieGen_cartanF4 :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := F4) cartanF4 ∧ cartanF4 ≠ 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show cartanF4.conjTranspose = cartanF4
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    simp only [cartanF4, Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_neg, hI,
      neg_neg]
    abel
  · show cartanF4.transpose = -cartanF4
    simp only [cartanF4, Matrix.transpose_add, Matrix.transpose_single, neg_add, Matrix.single_neg,
      neg_neg]
    abel
  · intro x
    show f4Tri s3C (cartanF4 *ᵥ x) x x + f4Tri s3C x (cartanF4 *ᵥ x) x
      + f4Tri s3C x x (cartanF4 *ᵥ x) = 0
    rw [cartanF4_mulVec]
    simp only [f4Tri, octRe3, dot7, dot8, im7, xo, yo, zo, phi3, e3, cartanF4Vec,
      Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val]
    ring
  · intro h
    have h54 := congrFun (congrFun h 5) 4
    simp [cartanF4] at h54

/-! ## The Clay statement at `F₄` -/

open MassGap.ClayTreeG MassGap.ClayStatementG MassGap.SymPlaqG

/-- **The Clay Yang–Mills statement for `F₄`**: `ClayStatementOf` at `F4`.

DERIVED: no numeral. -/
def ClayStatementF4 : Prop := ClayStatementOf F4

/-- **`ClayStatementOfDy F4`, the statement at the frozen tower, from
`ClayStatementAtG` on the symmetrised plaquette class**, which is
reflection closed (`symPlaqG_refl`). `ObserverLinkedG.clayStatementAtG_of_observer (G := F4)`
concludes the hypothesis from its inputs.

DERIVED: no numeral. -/
theorem clayStatementF4_of_atG (W : ConfFlowG F4)
    (h : ClayStatementAtG F4 W (SymPlaqClassG F4)) : ClayStatementOfDy F4 :=
  ⟨W, SymPlaqClassG F4, symPlaqG_refl F4, h⟩

-- The observer capstone elaborates at `F₄`: the six instance arguments resolve, and its conclusion
-- is `ClayStatementAtG F4 W (SymPlaqClassG F4)`, the hypothesis of `clayStatementF4_of_atG`.
example : True := by
  have _h := @MassGap.ObserverLinkedG.clayStatementAtG_of_observer F4 _ _ _ _ _ _
  trivial

end MassGap.GaugeF4

#print axioms MassGap.GaugeF4.dot7_cross
#print axioms MassGap.GaugeF4.octRe3_eq
#print axioms MassGap.GaugeF4.continuous_f4Cubic
#print axioms MassGap.GaugeF4.F4Sub
#print axioms MassGap.GaugeF4.isClosed_F4Sub
#print axioms MassGap.GaugeF4.f4Rep
#print axioms MassGap.GaugeF4.instGaugeGroupF4
#print axioms MassGap.GaugeF4.wilsonDensityG_F4
#print axioms MassGap.GaugeF4.instGaugeSimpleF4
#print axioms MassGap.GaugeF4.instGaugeLieF4
#print axioms MassGap.GaugeF4.cartanF4_mulVec
#print axioms MassGap.GaugeF4.lieGen_cartanF4
#print axioms MassGap.GaugeF4.clayStatementF4_of_atG
