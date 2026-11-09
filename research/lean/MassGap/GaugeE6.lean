import Mathlib
import MassGap.GaugeF4

/-!
# MassGap.GaugeE6 — compact `E₆` as a `GaugeGroup`

Compact `E₆` is the group of unitary transformations of the complexified exceptional Jordan algebra
`J_ℂ = J₃(𝕆) ⊗ ℂ ≅ ℂ²⁷` preserving the cubic norm `N` (the determinant of `J`, extended
complex-polynomially to all `27` coordinates, not restricted to the traceless part). Here it is the
stabiliser of `N` in `SU(27)`, written in coordinates orthonormal for the trace form of `J`.

## Conventions

*Octonions* are those of `GaugeF4`: `octMul`, `dot8`, `octRe3 x y z = Re((x y) z)` (`octRe3_eq`),
over any commutative ring, so over `ℂ` they are the complex-bilinear and trilinear extensions, with
no conjugation.

*Coordinates.* `X = [[a, z, ȳ], [z̄, b, x], [y, x̄, c]]`, `N(X) = abc − a n(x) − b n(y) − c n(z)
+ 2 Re(x y z)`, `tr(X²) = a² + b² + c² + 2(n(x) + n(y) + n(z))`. The coordinates `v : Fin 27 → ℂ`
are `v 0 = a`, `v 1 = b`, `v 2 = c`, and the blocks `v 3 … v 10`, `v 11 … v 18`, `v 19 … v 26` are
`√2 x`, `√2 y`, `√2 z` (`xE`, `yE`, `zE`), so that `tr(X²)` is the Euclidean form of `v`. In these
coordinates `2 N` is

  `e6Cubic s v = 2abc − a n(xE) − b n(yE) − c n(zE) + s Re((xE yE) zE)`,   `s = √2`.

The scaling is not cosmetic: the compact real form is the stabiliser in the unitary group of a
Hermitian form invariant under `F₄`, which is the trace form. In `J`'s raw coordinates (off-diagonal
octonions unscaled) the standard Hermitian form of `ℂ²⁷` is not the trace form, and the stabiliser
of `N` in that `U(27)` has dimension `30`, not `78` (`research/code/e6_checks.py`). As in
`GaugeF4`, the irrational enters as a parameter `s`, evaluated at `√2` in `ℂ`.

## The ambient group: `SU(27)`

The stabiliser of `N` in `U(27)` lies in `SU(27)`: it is the compact form of the connected group
`E₆(ℂ)`, whose Lie algebra is semisimple, so `det` restricted to it is a character of a connected
group with perfect Lie algebra, hence trivial; its centre `ℤ₃` acts by cube roots of unity, of
determinant `ω²⁷ = 1`. That is the classification statement and is not proved here; the numerical
counterpart (every element of the `78`-dimensional stabiliser algebra in `𝔲(27)` is traceless) is
in `e6_checks.py`. The subgroup is therefore defined inside `SU(27)` (`MassGap.SUN.SU 27`), which
gives the representation as the inclusion `suRep 27` and the `SU` convention for `lieGen`. What is
proved here about the centre: `ω · 1 ∈ E6Sub` for `ω³ = 1` (`centreE6_mem`), from the homogeneity
`N(c v) = c³ N(v)` (`e6Cubic_smul`).

## Objects

* `e6Tri s p q r`: a trilinear form with `e6Tri s v v v = e6Cubic s v`, not symmetric.
* `E6Sub`: `{g ∈ SU(27) | ∀ v : ℂ²⁷, N(g v) = N(v)}`; `E6` its carrier type.
* `isClosed_E6Sub`: an intersection of zero sets of polynomials in the entries, closed in the
  compact `SU(27)`; hence compact.
* `e6Rep`: `suRep 27` restricted to `E6Sub`, `E₆ → U(27)`, `repDim = 27`.

That `E6Sub` is the compact group `E₆` is the classification statement; it is not proved here.
`e6_checks.py` checks numerically, in exactly these coordinates, that the stabiliser algebra
`{A ∈ 𝔲(27) | ∇N(v) · A v = 0 ∀ v ∈ ℂ²⁷}` has dimension `78`, is closed under the bracket and
consists of traceless matrices, and that `GaugeF4.f4Cubic = 3√6 e6Cubic = 6√6 N` on the traceless
part (so `F₄ ⊂ E₆` as the stabiliser of the identity `a = b = c = 1`).

## Instances

* `instGaugeGroupE6`: compact, second-countable, Borel, `e6Rep` faithful and continuous.
* `instGaugeSimpleE6`: `lieDim = 78`, `dualCoxeter = 12`, `dynkinIndex = 3`, the classification
  values entered as constants like every other `GaugeSimple` instance; nothing here derives them
  from `E6Sub`.
* `instGaugeLieE6`: `lieGen M` is `M` Hermitian, `tr M = 0`, and `M` a derivation of the complexified
  cubic, `e6Tri(Mx, x, x) + e6Tri(x, Mx, x) + e6Tri(x, x, Mx) = 0` for all complex `x` (the
  derivative of `N` at `x` along `M x`). The derivation condition is `ℂ`-linear in `M`, so for
  Hermitian `M` it says `i M` lies in the stabiliser algebra of `N` in `𝔲(27)`; then `exp(i t M)`
  is unitary and preserves `N`, the `SU` convention `exp(i a g M) ∈ ρ(G)`. The trace condition is
  that of `SU(N)`'s `lieGen`; on the stabiliser algebra it is implied (numerically: every generator
  is traceless), and it is stated so that `lieGen` sits inside `SU(27)`'s. That the real span has
  dimension `78` is the numerical check above, not a theorem here. Two nonzero members are proved:
  `lieGen_cartanE6`, `GaugeF4.cartanF4`'s pattern (`GaugeG2.cartanM` on the imaginary parts of the
  three octonion blocks, a `G₂ ⊂ F₄ ⊂ E₆` generator, killing the identity of `J`); and
  `lieGen_diagE6`, the diagonal `diag(2, −2, 0; −1⁸, 1⁸, 0⁸)`, which does not kill the identity
  and so lies outside the `F₄` part.

## The Dynkin index `T(27) = 3`

Normalisation of `GaugeSimple`: long roots of squared length two, `T(adj) = h^∨`, and at `SU(N)`
`T(fund) = 1/2`, `h^∨ = N`. For `E₆`, `h^∨ = 12`. The ratio `tr₂₇(X²) / tr_adj(X²)` does not depend
on the normalisation and equals `T(27)/T(78) = dim(27) C₂(27) / (dim(78) C₂(78))`; with
`C₂(adj) = 12`, `C₂(27) = 26/3` it is `27 · 26/3 / (78 · 12) = 1/4`, so `T(27) = 12/4 = 3`.
`e6_checks.py` computes the ratio on the stabiliser algebra of `N` and finds `1/4`. The embedding
`F₄ ⊂ E₆` gives the same value: `27 = 26 ⊕ 1` and `78 = 52 ⊕ 26`, with `T_{F₄}(52) = 9`,
`T_{F₄}(26) = 3` (`GaugeF4.instGaugeSimpleF4`); so `T_{F₄}(78) = 9 + 3 = 12 = h^∨(E₆)` (embedding
index one) and `T_{E₆}(27) = T_{F₄}(26) + T_{F₄}(1) = 3 + 0 = 3`. These are statements of the
classification and of the numerics, recorded for the constant `3`; the tree carries no Lie algebra
from which to check them.

## The Clay statement at `E₆`

`ClayStatementE6 := ClayStatementOf E6`; `ObserverLinkedG.clayStatementAtG_of_observer (G := E6)`
elaborates, and `clayStatementE6_of_atG` with `SymPlaqG.symPlaqG_refl E6` turns its conclusion
into `ClayStatementOfDy E6`, the statement at the frozen tower;
`MeasuredSpacing.clayStatementMeasOf_of_of` lifts it to
`ClayStatementE6` under asymptotic scaling of the tensor mass.
-/

namespace MassGap.GaugeE6

open Matrix MeasureTheory MassGap.GaugeGroup MassGap.GaugeInstances
open MassGap.GaugeG2 (phi3 e3)
open MassGap.GaugeF4 (dot7 dot8 im7 octRe3)

/-! ## The cubic norm on the complexified exceptional Jordan algebra -/

section Cubic

variable {R : Type} [CommRing R]

/-- The octonion block `√2 x`, coordinates `3, …, 10`. DERIVED: the block offset `3`, after the three
diagonal coordinates; `8` the octonion dimension; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def xE (v : Fin 27 → R) : Fin 8 → R := ![v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10]

/-- The octonion block `√2 y`, coordinates `11, …, 18`. DERIVED: the block offset `11 = 3 + 8`; `8` the
octonion dimension; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def yE (v : Fin 27 → R) : Fin 8 → R := ![v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18]

/-- The octonion block `√2 z`, coordinates `19, …, 26`. DERIVED: the block offset `19 = 3 + 2 · 8`; `8` the
octonion dimension; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def zE (v : Fin 27 → R) : Fin 8 → R := ![v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26]

/-- A trilinear form whose diagonal is the cubic `e6Cubic`; `s` stands for `√2`.

DERIVED: `2` is `2 N` in the orthonormal coordinates of the module docstring
(`2 · abc`, and `2 · 2 Re(xyz) = s Re((√2x)(√2y)(√2z))` at `s = √2`); `27 = 3 + 3 · 8` the dimension
of `J₃(𝕆)`. -/
def e6Tri (s : R) (p q r : Fin 27 → R) : R :=
  2 * p 0 * q 1 * r 2 - p 0 * dot8 (xE q) (xE r) - p 1 * dot8 (yE q) (yE r)
    - p 2 * dot8 (zE q) (zE r) + s * octRe3 (xE p) (yE q) (zE r)

/-- **The cubic norm** `2 N(X)` of `J₃(𝕆) ⊗ ℂ` in orthonormal coordinates, with `s = √2`:
`2abc − a n(x) − b n(y) − c n(z) + s Re((x y) z)`, on all `27` coordinates.

DERIVED: no numeral beyond those of `e6Tri`; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def e6Cubic (s : R) (v : Fin 27 → R) : R := e6Tri s v v v

/-- **`N` is homogeneous of degree three**: `N(c v) = c³ N(v)`.

DERIVED: `3` the degree; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
theorem e6Cubic_smul (s c : R) (v : Fin 27 → R) :
    e6Cubic s (fun i => c * v i) = c ^ 3 * e6Cubic s v := by
  simp only [e6Cubic, e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, Fin.sum_univ_seven,
    Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val]
  ring

end Cubic

/-- `N` is continuous along continuous maps into `ℂ²⁷`.

DERIVED: `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
theorem continuous_e6Cubic {X : Type} [TopologicalSpace X] (s : ℂ) {f : X → Fin 27 → ℂ}
    (hf : Continuous f) : Continuous fun t => e6Cubic s (f t) := by
  have hf' : ∀ a, Continuous fun t => f t a := fun a => (continuous_apply a).comp hf
  simp only [e6Cubic, e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, Fin.sum_univ_seven,
    Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val]
  fun_prop

/-! ## `E₆ ⊆ SU(27)` -/

/-- `√2` in `ℂ`, the parameter of the cubic. -/
noncomputable abbrev s2C : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

/-- **Compact `E₆`**: the elements of `SU(27)` preserving the cubic norm, `N(g v) = N(v)` for all
complex `v`. Closure under inverse: `g⁻¹ = star g` with `g g⁻¹ = 1`.

DERIVED: `27` the dimension of `J₃(𝕆)`. -/
noncomputable def E6Sub : Subgroup (MassGap.SUN.SU 27) where
  carrier := {g | ∀ v : Fin 27 → ℂ,
    e6Cubic s2C ((g : Matrix (Fin 27) (Fin 27) ℂ) *ᵥ v) = e6Cubic s2C v}
  mul_mem' := by
    intro a b ha hb v
    show e6Cubic s2C (((a : Matrix (Fin 27) (Fin 27) ℂ) * (b : Matrix (Fin 27) (Fin 27) ℂ)) *ᵥ v)
      = e6Cubic s2C v
    rw [← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v
    show e6Cubic s2C ((1 : Matrix (Fin 27) (Fin 27) ℂ) *ᵥ v) = e6Cubic s2C v
    rw [Matrix.one_mulVec]
  inv_mem' := by
    intro a ha v
    have hu : (a : Matrix (Fin 27) (Fin 27) ℂ) * star (a : Matrix (Fin 27) (Fin 27) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp a.2).1
    show e6Cubic s2C (star (a : Matrix (Fin 27) (Fin 27) ℂ) *ᵥ v) = e6Cubic s2C v
    have h := ha (star (a : Matrix (Fin 27) (Fin 27) ℂ) *ᵥ v)
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] at h
    exact h.symm

/-- Compact `E₆` as a type. -/
abbrev E6 : Type := ↥E6Sub

/-- Membership in `E6Sub` is invariance of `N`. DERIVED: `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
theorem mem_E6Sub_iff (g : MassGap.SUN.SU 27) :
    g ∈ E6Sub ↔ ∀ v : Fin 27 → ℂ,
      e6Cubic s2C ((g : Matrix (Fin 27) (Fin 27) ℂ) *ᵥ v) = e6Cubic s2C v :=
  Iff.rfl

/-- **`E6Sub` is closed in `SU(27)`**: the intersection over `v` of the zero sets of the continuous
maps `g ↦ N(g v) − N(v)`.

DERIVED: `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
theorem isClosed_E6Sub : IsClosed (E6Sub : Set (MassGap.SUN.SU 27)) := by
  have hset : (E6Sub : Set (MassGap.SUN.SU 27)) = ⋂ v : Fin 27 → ℂ,
      {g : MassGap.SUN.SU 27 |
        e6Cubic s2C ((g : Matrix (Fin 27) (Fin 27) ℂ) *ᵥ v) = e6Cubic s2C v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_E6Sub_iff g
  rw [hset]
  exact isClosed_iInter fun v => isClosed_eq
    (continuous_e6Cubic s2C (continuous_subtype_val.matrix_mulVec continuous_const))
    continuous_const

instance : CompactSpace E6 := isCompact_iff_compactSpace.mp isClosed_E6Sub.isCompact

noncomputable instance : MeasurableSpace E6 := borel _
instance : BorelSpace E6 := ⟨rfl⟩

instance : SecondCountableTopology E6 :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

/-! ## The centre -/

/-- `ω³ = 1` gives `ω²⁷ = 1`, the determinant of `ω · 1` on `ℂ²⁷`. DERIVED: `27 = 3 · 9`. -/
theorem pow27_of_pow3 {ω : ℂ} (hω : ω ^ 3 = 1) : ω ^ 27 = 1 := by
  rw [show (27 : ℕ) = 3 * 9 by norm_num, pow_mul, hω, one_pow]

/-- **The cube roots of unity lie in `E₆`**: `ω · 1 ∈ SU(27)` (`GaugeInstances.centreElt`, as
`ω²⁷ = 1`) preserves `N`, since `N(ω v) = ω³ N(v)`.

DERIVED: `3` the degree of `N`; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
theorem centreE6_mem {ω : ℂ} (hω : ω ^ 3 = 1) :
    centreElt (N := 27) (by norm_num) (pow27_of_pow3 hω) ∈ E6Sub := by
  intro v
  have hv : (Matrix.diagonal (fun _ : Fin 27 => ω)) *ᵥ v = fun i => ω * v i := by
    funext i
    rw [Matrix.mulVec_diagonal]
  show e6Cubic s2C ((Matrix.diagonal (fun _ : Fin 27 => ω)) *ᵥ v) = e6Cubic s2C v
  rw [hv, e6Cubic_smul, hω, one_mul]

/-! ## The representation and the instances -/

/-- The 27-dimensional representation `E₆ → U(27)`: the inclusion `suRep 27` restricted to
`E6Sub`.

DERIVED: `27` the dimension. -/
noncomputable def e6Rep : E6 →* Matrix.unitaryGroup (Fin 27) ℂ :=
  (suRep 27).comp E6Sub.subtype

/-- Compact `E₆` as a `GaugeGroup` through `e6Rep`. DERIVED: `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`,
the representation dimension. -/
noncomputable instance instGaugeGroupE6 : GaugeGroup E6 where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := 27
  repDim_pos := by norm_num
  rep := e6Rep
  continuous_rep := by
    have h : Continuous fun g : MassGap.SUN.SU 27 =>
        ((suRep 27 g : Matrix.unitaryGroup (Fin 27) ℂ) : Matrix (Fin 27) (Fin 27) ℂ) :=
      continuous_subtype_val
    exact h.comp continuous_subtype_val
  rep_injective := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun U : Matrix.unitaryGroup (Fin 27) ℂ => (U : Matrix (Fin 27) (Fin 27) ℂ)) hgh

theorem dim_E6 : GaugeGroup.dim E6 = 27 := rfl

/-- The Wilson density of `E₆` is that of `SU(27)` at the same matrix: `1 − Re tr g / 27`.

DERIVED: no numeral beyond the density's own `1`; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
theorem wilsonDensityG_E6 (g : E6) :
    wilsonDensityG E6 g = wilsonDensityG (MassGap.SUN.SU 27) (g : MassGap.SUN.SU 27) := rfl

/-- **`E₆`**: `dim 𝔤 = 78`, `h^∨ = 12`, `T(27) = 3`. Classification values in the normalisation of
`GaugeSimple`; the derivation of `T(27) = 3` (trace ratio `1/4`, and `F₄ ⊂ E₆`) is in the module
docstring. Nothing here derives them from `E6Sub`.

DERIVED: `78`, `12`, `3` are the classification values. -/
noncomputable instance instGaugeSimpleE6 : GaugeSimple E6 where
  lieDim := 78
  dualCoxeter := 12
  dynkinIndex := 3
  dualCoxeter_pos := by norm_num
  dynkinIndex_pos := by norm_num

/-- **The Hermitian generators of `ρ(𝔢₆)`**: `M` Hermitian, traceless, and a derivation of the
complexified cubic norm: `e6Tri(Mx, x, x) + e6Tri(x, Mx, x) + e6Tri(x, x, Mx) = 0` for all complex
`x`. `78 > 0`.

DERIVED: `0` the trace and the derivation condition; `78` the dimension. -/
noncomputable instance instGaugeLieE6 : MassGap.ClayTreeG.GaugeLie E6 where
  lieGen M := M.IsHermitian ∧ M.trace = 0 ∧
    ∀ x : Fin 27 → ℂ,
      e6Tri s2C (M *ᵥ x) x x + e6Tri s2C x (M *ᵥ x) x + e6Tri s2C x x (M *ᵥ x) = 0
  lieDim_pos := by
    show 0 < 78
    norm_num

/-! ## Two generators -/

/-- The generator `GaugeG2.cartanM` on the imaginary parts of the three octonion blocks of `ℂ²⁷`:
`i (E₆₅ − E₅₆ + E₇₈ − E₈₇)` (0-based) and its translates by `8` and `16`; the pattern of
`GaugeF4.cartanF4` at the block offsets of `xE`, `yE`, `zE`.

DERIVED: the entries `±i` are those of `GaugeG2.cartanM` at the block offsets `4, 12, 20`;
`27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
noncomputable def cartanE6 : Matrix (Fin 27) (Fin 27) ℂ :=
  Matrix.single 5 6 (-Complex.I) + Matrix.single 6 5 Complex.I
    + Matrix.single 7 8 Complex.I + Matrix.single 8 7 (-Complex.I)
    + Matrix.single 13 14 (-Complex.I) + Matrix.single 14 13 Complex.I
    + Matrix.single 15 16 Complex.I + Matrix.single 16 15 (-Complex.I)
    + Matrix.single 21 22 (-Complex.I) + Matrix.single 22 21 Complex.I
    + Matrix.single 23 24 Complex.I + Matrix.single 24 23 (-Complex.I)

/-- `cartanE6` on a vector. DERIVED: `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
noncomputable def cartanE6Vec (x : Fin 27 → ℂ) : Fin 27 → ℂ :=
  ![0, 0, 0, 0, 0, -Complex.I * x 6, Complex.I * x 5, Complex.I * x 8, -Complex.I * x 7,
    0, 0, 0, 0, -Complex.I * x 14, Complex.I * x 13, Complex.I * x 16, -Complex.I * x 15,
    0, 0, 0, 0, -Complex.I * x 22, Complex.I * x 21, Complex.I * x 24, -Complex.I * x 23,
    0, 0]

theorem cartanE6_mulVec (x : Fin 27 → ℂ) : cartanE6 *ᵥ x = cartanE6Vec x := by
  simp only [cartanE6, Matrix.add_mulVec, Matrix.single_mulVec]
  ext k
  fin_cases k <;> simp [cartanE6Vec]

/-- **`cartanE6` is a generator of `ρ(𝔢₆)`** in the sense of `instGaugeLieE6`, and it is nonzero.
Its trace vanishes because `cartanE6ᵀ = −cartanE6`.

DERIVED: the index `(6, 5)` is the entry `i`; `2` the halving of `tr = −tr`. -/
theorem lieGen_cartanE6 :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := E6) cartanE6 ∧ cartanE6 ≠ 0 := by
  have hT : cartanE6.transpose = -cartanE6 := by
    simp only [cartanE6, Matrix.transpose_add, Matrix.transpose_single, neg_add, Matrix.single_neg,
      neg_neg]
    abel
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show cartanE6.conjTranspose = cartanE6
    have hI : star Complex.I = -Complex.I := Complex.conj_I
    simp only [cartanE6, Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_neg, hI,
      neg_neg]
    abel
  · show cartanE6.trace = 0
    have h := Matrix.trace_transpose cartanE6
    rw [hT, Matrix.trace_neg] at h
    linear_combination (-1 / 2 : ℂ) * h
  · intro x
    show e6Tri s2C (cartanE6 *ᵥ x) x x + e6Tri s2C x (cartanE6 *ᵥ x) x
      + e6Tri s2C x x (cartanE6 *ᵥ x) = 0
    rw [cartanE6_mulVec]
    simp only [e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, cartanE6Vec,
      Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val]
    ring
  · intro h
    have h65 := congrFun (congrFun h 6) 5
    simp [cartanE6] at h65

/-- The diagonal weights `(2, −2, 0; −1⁸, 1⁸, 0⁸)`: `a ↦ 2a`, `b ↦ −2b`, `c ↦ 0`, `x ↦ −x`,
`y ↦ y`, `z ↦ 0`. Each monomial of `N` has weight `0`: `2 − 2 + 0`, `2 − 2`, `−2 + 2`, `0 + 0`,
`−1 + 1 + 0`.

DERIVED: the weights solve the five linear conditions; `2` clears the halves; `27 = 3 + 3 · 8` the
dimension of `J₃(𝕆)`. -/
def diagWeight : Fin 27 → ℂ :=
  ![2, -2, 0, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The diagonal Cartan generator `diag(diagWeight)`. DERIVED: `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def diagE6 : Matrix (Fin 27) (Fin 27) ℂ := Matrix.diagonal diagWeight

/-- **`diagE6` is a generator of `ρ(𝔢₆)`** in the sense of `instGaugeLieE6`, and it is nonzero. It
does not annihilate the identity `a = b = c = 1` of `J` (its `(0, 0)` entry is `2`), so it is not in
the `F₄` part.

DERIVED: the index `(0, 0)` is the entry `2`. -/
theorem lieGen_diagE6 :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := E6) diagE6 ∧ diagE6 ≠ 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show diagE6.conjTranspose = diagE6
    rw [diagE6, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> simp [diagWeight]
  · show diagE6.trace = 0
    simp [diagE6, Matrix.trace, Fin.sum_univ_succ, diagWeight]
  · intro x
    show e6Tri s2C (diagE6 *ᵥ x) x x + e6Tri s2C x (diagE6 *ᵥ x) x
      + e6Tri s2C x x (diagE6 *ᵥ x) = 0
    simp only [diagE6, e6Tri, octRe3, dot7, dot8, im7, xE, yE, zE, phi3, e3, Matrix.mulVec_diagonal,
      Fin.sum_univ_seven, Fin.sum_univ_eight, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val, diagWeight]
    ring
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [diagE6, diagWeight] at h00

/-! ## The Clay statement at `E₆` -/

open MassGap.ClayTreeG MassGap.ClayStatementG MassGap.SymPlaqG

/-- **The Clay Yang–Mills statement for `E₆`**: `ClayStatementOf` at `E6`.

DERIVED: no numeral. -/
def ClayStatementE6 : Prop := ClayStatementOf E6

/-- **`ClayStatementOfDy E6`, the statement at the frozen tower, from
`ClayStatementAtG` on the symmetrised plaquette class**, which is
reflection closed (`symPlaqG_refl`). `ObserverLinkedG.clayStatementAtG_of_observer (G := E6)`
concludes the hypothesis from its inputs.

DERIVED: no numeral. -/
theorem clayStatementE6_of_atG (W : ConfFlowG E6)
    (h : ClayStatementAtG E6 W (SymPlaqClassG E6)) : ClayStatementOfDy E6 :=
  ⟨W, SymPlaqClassG E6, symPlaqG_refl E6, h⟩

-- The observer capstone elaborates at `E₆`: the six instance arguments resolve, and its conclusion
-- is `ClayStatementAtG E6 W (SymPlaqClassG E6)`, the hypothesis of `clayStatementE6_of_atG`.
example : True := by
  have _h := @MassGap.ObserverLinkedG.clayStatementAtG_of_observer E6 _ _ _ _ _ _
  trivial

end MassGap.GaugeE6

#print axioms MassGap.GaugeE6.e6Cubic_smul
#print axioms MassGap.GaugeE6.continuous_e6Cubic
#print axioms MassGap.GaugeE6.E6Sub
#print axioms MassGap.GaugeE6.isClosed_E6Sub
#print axioms MassGap.GaugeE6.centreE6_mem
#print axioms MassGap.GaugeE6.e6Rep
#print axioms MassGap.GaugeE6.instGaugeGroupE6
#print axioms MassGap.GaugeE6.wilsonDensityG_E6
#print axioms MassGap.GaugeE6.instGaugeSimpleE6
#print axioms MassGap.GaugeE6.instGaugeLieE6
#print axioms MassGap.GaugeE6.cartanE6_mulVec
#print axioms MassGap.GaugeE6.lieGen_cartanE6
#print axioms MassGap.GaugeE6.lieGen_diagE6
#print axioms MassGap.GaugeE6.clayStatementE6_of_atG
