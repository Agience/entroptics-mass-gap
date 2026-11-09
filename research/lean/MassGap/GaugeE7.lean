import Mathlib
import MassGap.GaugeInstances
import MassGap.GaugeF4
import MassGap.ClayTreeG
import MassGap.ClayStatementG
import MassGap.ObserverLinkedG

/-!
# MassGap.GaugeE7 — compact `E₇` as a `GaugeGroup`

`E₇` is the automorphism group of Freudenthal's quartic form `q` on the 56-dimensional
Freudenthal triple system `𝔐 = ℂ ⊕ J_ℂ ⊕ ℂ ⊕ J_ℂ`, `J_ℂ = J₃(𝕆) ⊗ ℂ`. Here it is the stabiliser of
`q` in compact `USp(28) = GaugeInstances.USp 28 ⊆ U(56)`.

## Conventions

*The Jordan algebra.* Octonions, `octMul`, `octRe3`, `dot8` are those of `GaugeF4`. An element of
`J_ℂ` is `A : Fin 27 → ℂ`: `A 0 = a`, `A 1 = b`, `A 2 = c` the diagonal, `A 3, …, A 10 = p`,
`A 11, …, A 18 = q`, `A 19, …, A 26 = s` the off-diagonal octonions (`jp`, `jq`, `js`), with
`p = √2 x`, `q = √2 y`, `s = √2 z` for the `x, y, z` of `GaugeF4`'s determinant
`abc − a n(x) − b n(y) − c n(z) + 2 Re((x y) z)`. In these coordinates the trace form
`T(A, B) = tr(A ∘ B)` is the plain sum `∑ₖ A k · B k` (`dot27`), so the standard Hermitian form on
`ℂ²⁷` is `T(Ā, B)`. With `r = √2`:

  `4N(A) = 4abc − 2a n(p) − 2b n(q) − 2c n(s) + 2r Re((p q) s)`  (`N4tri r A A A`),
  `2A^# = (2bc − n(p), 2ca − n(q), 2ab − n(s), r conj(q s) − 2a p, r conj(s p) − 2b q,`
  `        r conj(p q) − 2c s)`  (`sharp2 r A A`),

`A^#` the Jordan adjoint, `T(A^#, B) = d/dt N(A + tB)|₀`. As in `GaugeF4`, the irrational `√2`
enters as a parameter `r` so the forms are defined over any commutative ring.

*The triple system.* `v : Fin (28 + 28) → ℂ`: `v (castAdd 28 0) = α`, `v (castAdd 28 (k+1)) = A k`,
`v (natAdd 28 0) = β`, `v (natAdd 28 (k+1)) = B k` (`ftsAlpha`, `ftsA`, `ftsBeta`, `ftsB`). The
quartic is

  `q(v) = (αβ − T(A, B))² − 4α N(A) − 4β N(B) − 4 T(A^#, B^#)`  (`e7Quartic`).

Up to the sign convention `A, B ↦ −A, −B` (which flips the `N` terms) this is `−1` times
Freudenthal's quartic in the normalisation `4 [T(A^#, B^#) − α N(A) − β N(B)] − (αβ − T(A, B))²`.
The sign of the `T(A^#, B^#)` term relative to the square is not a convention: with `+4T(A^#, B^#)`
the stabiliser in `𝔰𝔭(56)` has dimension `79 = dim(E₆ × U(1))` (`e7_checks.py --variants`).

*The symplectic form.* `USp 28` preserves `Jsp 28`, Mathlib's `Matrix.J = fromBlocks 0 (−1) 1 0`
reindexed by `finSumFinEquiv`. In the coordinates above
(`jsp_form`): `vᵀ (Jsp 28) w = β α' − α β' + T(B, A') − T(A, B')`. This is the triple-system form
`αβ' − βα' + T(A, B') − T(B, A')` with the labels `(α, A)` and `(β, B)` exchanged, and `q` is
invariant under that exchange.

## Objects

* `e7Q4 r v₁ v₂ v₃ v₄`: a 4-linear form with `e7Q4 r v v v v = e7Quartic r v`, not symmetric; only
  its diagonal and its derivative along a matrix enter.
* `E7Sub`: `{g ∈ USp(28) | ∀ v : ℂ⁵⁶, q(g v) = q(v)}`; `E7` is its carrier type.
* `isClosed_E7Sub`: an intersection of zero sets of polynomials in the entries, so `E7` is
  compact as a closed subset of the compact `USp 28`.
* `e7Rep`: the inclusion `E₇ ⊆ USp(28) ⊆ U(56)`.

That `E7Sub` is the compact group `E₇` is the classification statement; it is not proved here.
`research/code/e7_checks.py` checks numerically, in exactly these coordinates, that the stabiliser
algebra `{X ∈ 𝔰𝔭(56) | ∇q(v) · X v = 0}` has dimension `133` and is closed under the bracket, that
its intersection with `𝔲(56)` (the Lie algebra of `E7Sub`) has real dimension `133`, that
`4N = 4 det` and `T(A^#, B) = D_B N(A)`, and that `q` is invariant under the exchange of blocks.

## Instances

* `instGaugeGroupE7`: compact, second-countable, Borel, `e7Rep` faithful and continuous,
  `repDim = 28 + 28 = 56`.
* `instGaugeSimpleE7`: `lieDim = 133`, `dualCoxeter = 18`, `dynkinIndex = 6`, the classification
  values entered as constants like every other `GaugeSimple` instance; nothing here derives them
  from `E7Sub`.
* `instGaugeLieE7`: `lieGen M` is the `USp` predicate of `ClayTreeG.instGaugeLieUSp` (`M` Hermitian,
  `M J + J Mᵀ = 0`) and `M` a derivation of the complex quartic's polarisation:
  `e7Q4(Mv, v, v, v) + e7Q4(v, Mv, v, v) + e7Q4(v, v, Mv, v) + e7Q4(v, v, v, Mv) = 0` for all complex
  `v`, the derivative of `q` at `v` along `M v`. For `M = i X`, `X ∈ 𝔲(56)`, this cuts out
  `i Lie(E7Sub)`; that its real span has dimension `133` is the numerical check above, not a
  theorem here. `lieGen_e7Weight` exhibits one nonzero member: the diagonal `e7Weight` acting by
  `−3` on `α`, `1` on `A`, `3` on `β`, `−1` on `B`, the generator of the `U(1)` in
  `E₆ × U(1) ⊂ E₇`.

## The Dynkin index `T(56) = 6`

Normalisation of `GaugeSimple`: long roots of squared length two, `T(adj) = h^∨`, `T(fund) = 1/2` at
`USp`. For `E₇`, `h^∨ = 18`. The ratio `tr₅₆(X²) / tr_adj(X²)` does not depend on the normalisation
and equals `T(56)/h^∨ = dim(56) C₂(56) / (dim(133) C₂(133))`; with `C₂(56) = 57/4` (in the units
where `C₂(adj) = 18`) it is `56 · 57/4 / (133 · 18) = 1/3`, so `T(56) = 18/3 = 6`. `e7_checks.py`
computes the ratio on the stabiliser algebra of `q` and finds `1/3`. The embedding `E₆ × U(1) ⊂ E₇`
gives the same value: the centraliser of `e7Weight` in the stabiliser algebra has dimension `79`,
its derived algebra dimension `78`, and under it `56 = 1 ⊕ 27 ⊕ 1 ⊕ 27̄` (the blocks `α, A, β, B`);
the numerics find `T_{E₆}(27) = 3` (`h^∨(E₆) = 12`) and embedding index one, so
`T(56) = 3 + 3 = 6`. These are statements of the classification and of the numerics, recorded for
the constant `6`; the tree carries no Lie algebra from which to check them.

## The Clay statement at `E₇`

`ClayStatementE7 := ClayStatementOf E7`; `ObserverLinkedG.clayStatementAtG_of_observer (G := E7)`
elaborates, and `clayStatementE7_of_atG` with `SymPlaqG.symPlaqG_refl E7` turns its conclusion
into `ClayStatementOfDy E7`, the statement at the frozen tower;
`MeasuredSpacing.clayStatementMeasOf_of_of` lifts it to
`ClayStatementE7` under asymptotic scaling of the tensor mass.
-/

namespace MassGap.GaugeE7

open Matrix MeasureTheory MassGap.GaugeGroup MassGap.GaugeInstances MassGap.GaugeG2
  MassGap.GaugeF4

/-! ## The exceptional Jordan algebra over a commutative ring -/

section Jordan

variable {R : Type} [CommRing R]

/-- The octonion `p`, coordinates `3, …, 10`. DERIVED: the block offset; `27 = 3 + 3 · 8` the dimension of
`J₃(𝕆)`; `8` the octonion dimension. -/
def jp (A : Fin 27 → R) : Fin 8 → R := ![A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10]

/-- The octonion `q`, coordinates `11, …, 18`. DERIVED: the block offset; `27 = 3 + 3 · 8` the dimension of
`J₃(𝕆)`; `8` the octonion dimension. -/
def jq (A : Fin 27 → R) : Fin 8 → R := ![A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18]

/-- The octonion `s`, coordinates `19, …, 26`. DERIVED: the block offset; `27 = 3 + 3 · 8` the dimension of
`J₃(𝕆)`; `8` the octonion dimension. -/
def js (A : Fin 27 → R) : Fin 8 → R := ![A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26]

/-- The trace form `T(A, B) = tr(A ∘ B)` in the orthonormal coordinates. DERIVED: `27 = 3 + 3 · 8` the dimension of
`J₃(𝕆)`. -/
def dot27 (A B : Fin 27 → R) : R := ∑ k, A k * B k

/-- Octonion conjugation `(w₀, w') ↦ (w₀, −w')`. DERIVED: `8` the octonion dimension. -/
def octConj (w : Fin 8 → R) : Fin 8 → R := Fin.cons (w 0) (fun k => -w k.succ)

/-- A trilinear form whose diagonal is `4N`, `N` the cubic norm; `r` stands for `√2`:
`4abc − 2a n(p) − 2b n(q) − 2c n(s) + 2r Re((p q) s)`.

DERIVED: `4, 2, 2, 2, 2` are `4 det` in the coordinates `p = √2 x`, `q = √2 y`, `s = √2 z`;
`27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def N4tri (r : R) (P Q S : Fin 27 → R) : R :=
  4 * P 0 * Q 1 * S 2 - 2 * P 0 * dot8 (jp Q) (jp S) - 2 * P 1 * dot8 (jq Q) (jq S)
    - 2 * P 2 * dot8 (js Q) (js S) + 2 * r * octRe3 (jp P) (jq Q) (js S)

/-- An off-diagonal block of `2A^#`: `r conj(u v) − 2 t w`. DERIVED: `2` the doubling of `A^#`; `8` the octonion
dimension. -/
def shOff (r t : R) (u v w : Fin 8 → R) : Fin 8 → R :=
  fun i => r * octConj (octMul u v) i - 2 * t * w i

/-- A bilinear map whose diagonal is `2A^#`, `A^#` the Jordan adjoint:
`(2bc − n(p), 2ca − n(q), 2ab − n(s), r conj(q s) − 2a p, r conj(s p) − 2b q, r conj(p q) − 2c s)`.

DERIVED: `2` the doubling of `A^#`; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def sharp2 (r : R) (P Q : Fin 27 → R) : Fin 27 → R :=
  ![2 * P 1 * Q 2 - dot8 (jp P) (jp Q), 2 * P 2 * Q 0 - dot8 (jq P) (jq Q),
    2 * P 0 * Q 1 - dot8 (js P) (js Q),
    shOff r (P 0) (jq P) (js Q) (jp Q) 0, shOff r (P 0) (jq P) (js Q) (jp Q) 1,
    shOff r (P 0) (jq P) (js Q) (jp Q) 2, shOff r (P 0) (jq P) (js Q) (jp Q) 3,
    shOff r (P 0) (jq P) (js Q) (jp Q) 4, shOff r (P 0) (jq P) (js Q) (jp Q) 5,
    shOff r (P 0) (jq P) (js Q) (jp Q) 6, shOff r (P 0) (jq P) (js Q) (jp Q) 7,
    shOff r (P 1) (js P) (jp Q) (jq Q) 0, shOff r (P 1) (js P) (jp Q) (jq Q) 1,
    shOff r (P 1) (js P) (jp Q) (jq Q) 2, shOff r (P 1) (js P) (jp Q) (jq Q) 3,
    shOff r (P 1) (js P) (jp Q) (jq Q) 4, shOff r (P 1) (js P) (jp Q) (jq Q) 5,
    shOff r (P 1) (js P) (jp Q) (jq Q) 6, shOff r (P 1) (js P) (jp Q) (jq Q) 7,
    shOff r (P 2) (jp P) (jq Q) (js Q) 0, shOff r (P 2) (jp P) (jq Q) (js Q) 1,
    shOff r (P 2) (jp P) (jq Q) (js Q) 2, shOff r (P 2) (jp P) (jq Q) (js Q) 3,
    shOff r (P 2) (jp P) (jq Q) (js Q) 4, shOff r (P 2) (jp P) (jq Q) (js Q) 5,
    shOff r (P 2) (jp P) (jq Q) (js Q) 6, shOff r (P 2) (jp P) (jq Q) (js Q) 7]

end Jordan

/-! ## The Freudenthal triple system and its quartic -/

section Triple

variable {R : Type} [CommRing R]

/-- `α`, the coordinate `castAdd 28 0`. DERIVED: the block layout; `28 = 1 + 27` the block `(α, A)`, half the
dimension `56` of the triple system. -/
def ftsAlpha (v : Fin (28 + 28) → R) : R := v (Fin.castAdd 28 0)

/-- `A`, the coordinates `castAdd 28 (k + 1)`. DERIVED: the block layout; `28 = 1 + 27` the block `(α, A)`,
half the dimension `56` of the triple system; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def ftsA (v : Fin (28 + 28) → R) : Fin 27 → R := fun k => v (Fin.castAdd 28 k.succ)

/-- `β`, the coordinate `natAdd 28 0`. DERIVED: the block layout; `28 = 1 + 27` the block `(β, B)`, half the
dimension `56` of the triple system. -/
def ftsBeta (v : Fin (28 + 28) → R) : R := v (Fin.natAdd 28 0)

/-- `B`, the coordinates `natAdd 28 (k + 1)`. DERIVED: the block layout; `28 = 1 + 27` the block `(β, B)`,
half the dimension `56` of the triple system; `27 = 3 + 3 · 8` the dimension of `J₃(𝕆)`. -/
def ftsB (v : Fin (28 + 28) → R) : Fin 27 → R := fun k => v (Fin.natAdd 28 k.succ)

/-- A 4-linear form whose diagonal is Freudenthal's quartic `e7Quartic`:
`(α₁β₂ − T(A₁, B₂))(α₃β₄ − T(A₃, B₄)) − α₁ 4N(A₂, A₃, A₄) − β₁ 4N(B₂, B₃, B₄)
 − T(2A^#(A₁, A₂), 2B^#(B₃, B₄))`.

DERIVED: no numeral beyond those of `N4tri` and `sharp2`; `28 = 1 + 27` the block size, half the
dimension `56` of the triple system. -/
def e7Q4 (r : R) (v₁ v₂ v₃ v₄ : Fin (28 + 28) → R) : R :=
  (ftsAlpha v₁ * ftsBeta v₂ - dot27 (ftsA v₁) (ftsB v₂))
      * (ftsAlpha v₃ * ftsBeta v₄ - dot27 (ftsA v₃) (ftsB v₄))
    - ftsAlpha v₁ * N4tri r (ftsA v₂) (ftsA v₃) (ftsA v₄)
    - ftsBeta v₁ * N4tri r (ftsB v₂) (ftsB v₃) (ftsB v₄)
    - dot27 (sharp2 r (ftsA v₁) (ftsA v₂)) (sharp2 r (ftsB v₃) (ftsB v₄))

/-- **Freudenthal's quartic** `q(v) = (αβ − T(A, B))² − 4αN(A) − 4βN(B) − 4T(A^#, B^#)`, with
`r = √2`.

DERIVED: no numeral beyond those of `e7Q4`; `28 = 1 + 27` the block size, half the dimension `56`. -/
def e7Quartic (r : R) (v : Fin (28 + 28) → R) : R := e7Q4 r v v v v

end Triple

/-! ## The symplectic form of `USp 28` in these coordinates -/

/-- `Jsp 28` on the first block: `(J w)(castAdd 28 a) = −w(natAdd 28 a)`. DERIVED: `28` the block size of
`USp(28) ⊆ U(56)`. -/
theorem jsp_mulVec_castAdd (w : Fin (28 + 28) → ℂ) (a : Fin 28) :
    (Jsp 28 *ᵥ w) (Fin.castAdd 28 a) = -w (Fin.natAdd 28 a) := by
  rw [Jsp, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
    finSumFinEquiv_symm_apply_castAdd, Equiv.symm_symm, Matrix.J, Matrix.fromBlocks_mulVec,
    Sum.elim_inl]
  simp only [Pi.add_apply, Matrix.zero_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
    Pi.neg_apply, Function.comp_apply, finSumFinEquiv_apply_right, Pi.zero_apply, zero_add]

/-- `Jsp 28` on the second block: `(J w)(natAdd 28 a) = w(castAdd 28 a)`. DERIVED: `28` the block size of
`USp(28) ⊆ U(56)`. -/
theorem jsp_mulVec_natAdd (w : Fin (28 + 28) → ℂ) (a : Fin 28) :
    (Jsp 28 *ᵥ w) (Fin.natAdd 28 a) = w (Fin.castAdd 28 a) := by
  rw [Jsp, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.symm_symm, Matrix.J, Matrix.fromBlocks_mulVec,
    Sum.elim_inr]
  simp only [Pi.add_apply, Matrix.zero_mulVec, Matrix.one_mulVec, Function.comp_apply,
    finSumFinEquiv_apply_left, Pi.zero_apply, add_zero]

/-- **The form of `USp 28` is the triple-system form**:
`vᵀ (Jsp 28) w = β α' − α β' + T(B, A') − T(A, B')`.

DERIVED: `28` the block size of `USp(28) ⊆ U(56)`. -/
theorem jsp_form (v w : Fin (28 + 28) → ℂ) :
    v ⬝ᵥ (Jsp 28 *ᵥ w) = ftsBeta v * ftsAlpha w - ftsAlpha v * ftsBeta w
      + dot27 (ftsB v) (ftsA w) - dot27 (ftsA v) (ftsB w) := by
  rw [dotProduct, Fin.sum_univ_add]
  simp only [jsp_mulVec_castAdd, jsp_mulVec_natAdd, Fin.sum_univ_succ (n := 27), ftsAlpha,
    ftsBeta, ftsA, ftsB, dot27, mul_neg, Finset.sum_neg_distrib]
  ring

/-! ## Continuity of the quartic -/

section Continuity

variable {X : Type} [TopologicalSpace X]

@[fun_prop]
theorem continuous_dot7' {f g : X → Fin 7 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => dot7 (f t) (g t) := by
  simp only [dot7]
  fun_prop

@[fun_prop]
theorem continuous_dot8' {f g : X → Fin 8 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => dot8 (f t) (g t) := by
  simp only [dot8]
  fun_prop

@[fun_prop]
theorem continuous_dot27 {f g : X → Fin 27 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => dot27 (f t) (g t) := by
  simp only [dot27]
  fun_prop

@[fun_prop]
theorem continuous_im7' {f : X → Fin 8 → ℂ} (hf : Continuous f) :
    Continuous fun t => im7 (f t) :=
  continuous_pi fun i => (continuous_apply i.succ).comp hf

@[fun_prop]
theorem continuous_cross' {f g : X → Fin 7 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => cross (f t) (g t) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [cross] <;> fun_prop

@[fun_prop]
theorem continuous_octMul' {f g : X → Fin 8 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => octMul (f t) (g t) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun _ => ?_) i
  · simp only [octMul, Fin.cons_zero]
    fun_prop
  · simp only [octMul, Fin.cons_succ]
    fun_prop

@[fun_prop]
theorem continuous_octConj {f : X → Fin 8 → ℂ} (hf : Continuous f) :
    Continuous fun t => octConj (f t) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun _ => ?_) i
  · simp only [octConj, Fin.cons_zero]
    fun_prop
  · simp only [octConj, Fin.cons_succ]
    fun_prop

@[fun_prop]
theorem continuous_octRe3' {f g h : X → Fin 8 → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) : Continuous fun t => octRe3 (f t) (g t) (h t) := by
  simp only [octRe3, phi3, e3]
  fun_prop

@[fun_prop]
theorem continuous_jp {f : X → Fin 27 → ℂ} (hf : Continuous f) :
    Continuous fun t => jp (f t) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [jp] <;> fun_prop

@[fun_prop]
theorem continuous_jq {f : X → Fin 27 → ℂ} (hf : Continuous f) :
    Continuous fun t => jq (f t) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [jq] <;> fun_prop

@[fun_prop]
theorem continuous_js {f : X → Fin 27 → ℂ} (hf : Continuous f) :
    Continuous fun t => js (f t) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [js] <;> fun_prop

@[fun_prop]
theorem continuous_shOff (r : ℂ) {t : X → ℂ} {u v w : X → Fin 8 → ℂ} (ht : Continuous t)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => shOff r (t x) (u x) (v x) (w x) := by
  refine continuous_pi fun i => ?_
  simp only [shOff]
  fun_prop

@[fun_prop]
theorem continuous_sharp2 (r : ℂ) {f g : X → Fin 27 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => sharp2 r (f t) (g t) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [sharp2] <;> fun_prop

@[fun_prop]
theorem continuous_N4tri (r : ℂ) {f g h : X → Fin 27 → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t => N4tri r (f t) (g t) (h t) := by
  simp only [N4tri]
  fun_prop

@[fun_prop]
theorem continuous_ftsA {f : X → Fin (28 + 28) → ℂ} (hf : Continuous f) :
    Continuous fun t => ftsA (f t) :=
  continuous_pi fun _ => (continuous_apply _).comp hf

@[fun_prop]
theorem continuous_ftsB {f : X → Fin (28 + 28) → ℂ} (hf : Continuous f) :
    Continuous fun t => ftsB (f t) :=
  continuous_pi fun _ => (continuous_apply _).comp hf

@[fun_prop]
theorem continuous_ftsAlpha {f : X → Fin (28 + 28) → ℂ} (hf : Continuous f) :
    Continuous fun t => ftsAlpha (f t) :=
  (continuous_apply _).comp hf

@[fun_prop]
theorem continuous_ftsBeta {f : X → Fin (28 + 28) → ℂ} (hf : Continuous f) :
    Continuous fun t => ftsBeta (f t) :=
  (continuous_apply _).comp hf

/-- `q` is continuous along continuous maps into `ℂ⁵⁶`.

DERIVED: `28` the block size, `56 = 28 + 28`. -/
theorem continuous_e7Quartic (r : ℂ) {f : X → Fin (28 + 28) → ℂ} (hf : Continuous f) :
    Continuous fun t => e7Quartic r (f t) := by
  simp only [e7Quartic, e7Q4]
  fun_prop

end Continuity

/-! ## `E₇ ⊆ USp(28)` -/

/-- `√2` in `ℂ`, the parameter of the quartic. -/
noncomputable abbrev s2C : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

/-- **Compact `E₇`**: the elements of `USp(28) ⊆ U(56)` preserving Freudenthal's quartic,
`q(g v) = q(v)` for all complex `v`. Closure under inverse: `g⁻¹ = star g` with `g g⁻¹ = 1`.

DERIVED: `28` half the dimension `56` of the triple system. -/
noncomputable def E7Sub : Subgroup (USp 28) where
  carrier := {g | ∀ v : Fin (28 + 28) → ℂ, e7Quartic s2C (g.1.1 *ᵥ v) = e7Quartic s2C v}
  mul_mem' := by
    intro a b ha hb v
    show e7Quartic s2C ((a.1.1 * b.1.1) *ᵥ v) = e7Quartic s2C v
    rw [← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v
    show e7Quartic s2C ((1 : Matrix (Fin (28 + 28)) (Fin (28 + 28)) ℂ) *ᵥ v) = e7Quartic s2C v
    rw [Matrix.one_mulVec]
  inv_mem' := by
    intro a ha v
    have hu : a.1.1 * star a.1.1 = 1 := Matrix.mem_unitaryGroup_iff.mp a.1.2
    show e7Quartic s2C (star a.1.1 *ᵥ v) = e7Quartic s2C v
    have h := ha (star a.1.1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] at h
    exact h.symm

/-- Compact `E₇` as a type. -/
abbrev E7 : Type := ↥E7Sub

/-- Membership in `E7Sub` is invariance of `q`. DERIVED: `28` the block size of `USp(28) ⊆ U(56)`. -/
theorem mem_E7Sub_iff (g : USp 28) :
    g ∈ E7Sub ↔ ∀ v : Fin (28 + 28) → ℂ, e7Quartic s2C (g.1.1 *ᵥ v) = e7Quartic s2C v :=
  Iff.rfl

/-- **`E7Sub` is closed in `USp(28)`**: the intersection over `v` of the zero sets of the
continuous maps `g ↦ q(g v) − q(v)`.

DERIVED: `28` the block size of `USp(28) ⊆ U(56)`. -/
theorem isClosed_E7Sub : IsClosed (E7Sub : Set (USp 28)) := by
  have hset : (E7Sub : Set (USp 28)) = ⋂ v : Fin (28 + 28) → ℂ,
      {g : USp 28 | e7Quartic s2C (g.1.1 *ᵥ v) = e7Quartic s2C v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_E7Sub_iff g
  rw [hset]
  have hm : Continuous fun g : USp 28 => g.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  exact isClosed_iInter fun v => isClosed_eq
    (continuous_e7Quartic s2C (hm.matrix_mulVec continuous_const)) continuous_const

instance : CompactSpace E7 := isCompact_iff_compactSpace.mp isClosed_E7Sub.isCompact

noncomputable instance : MeasurableSpace E7 := borel _
instance : BorelSpace E7 := ⟨rfl⟩

instance : SecondCountableTopology E7 :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

/-! ## The representation and the instances -/

/-- The 56-dimensional representation `E₇ → U(56)`: the inclusion through `USp(28)`.

DERIVED: `28` the block size, `56 = 28 + 28`. -/
noncomputable def e7Rep : E7 →* Matrix.unitaryGroup (Fin (28 + 28)) ℂ :=
  (USpSub 28).subtype.comp E7Sub.subtype

/-- `E₇` as a `GaugeGroup` through `e7Rep`. DERIVED: `repDim = 28 + 28 = 56`, the dimension of the triple
system, `28` the block size of `USp(28)`. -/
noncomputable instance instGaugeGroupE7 : GaugeGroup E7 where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := 28 + 28
  repDim_pos := by norm_num
  rep := e7Rep
  continuous_rep :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  rep_injective := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)

theorem dim_E7 : GaugeGroup.dim E7 = 56 := rfl

/-- The Wilson density of `E₇` is that of `USp(28)` at the same matrix: `1 − Re tr g / 56`.

DERIVED: no numeral beyond the density's own `1`; `28` the block size of `USp(28)`, `56 = 28 + 28`. -/
theorem wilsonDensityG_E7 (g : E7) :
    wilsonDensityG E7 g = wilsonDensityG (USp 28) (g : USp 28) := rfl

/-- **`E₇`**: `dim 𝔤 = 133`, `h^∨ = 18`, `T(56) = 6`. Classification values in the normalisation of
`GaugeSimple`; the derivation of `T(56) = 6` (trace ratio `1/3`, and `E₆ × U(1) ⊂ E₇`) is in the
module docstring. Nothing here derives them from `E7Sub`.

DERIVED: `133`, `18`, `6` are the classification values. -/
noncomputable instance instGaugeSimpleE7 : GaugeSimple E7 where
  lieDim := 133
  dualCoxeter := 18
  dynkinIndex := 6
  dualCoxeter_pos := by norm_num
  dynkinIndex_pos := by norm_num

/-- **The Hermitian generators of `ρ(𝔢₇)`**: the `USp` predicate (`M` Hermitian,
`M J + J Mᵀ = 0`, `J = Jsp 28`) and `M` a derivation of the complex quartic:
`e7Q4(Mv, v, v, v) + e7Q4(v, Mv, v, v) + e7Q4(v, v, Mv, v) + e7Q4(v, v, v, Mv) = 0` for all complex
`v`. `133 > 0`.

DERIVED: `0` the defining relations; `133` the dimension. -/
noncomputable instance instGaugeLieE7 : MassGap.ClayTreeG.GaugeLie E7 where
  lieGen M := M.IsHermitian ∧ M * Jsp 28 + Jsp 28 * M.transpose = 0 ∧
    ∀ v : Fin (28 + 28) → ℂ,
      e7Q4 s2C (M *ᵥ v) v v v + e7Q4 s2C v (M *ᵥ v) v v + e7Q4 s2C v v (M *ᵥ v) v
        + e7Q4 s2C v v v (M *ᵥ v) = 0
  lieDim_pos := by
    show 0 < 133
    norm_num

/-! ## Linearity under negation, slot by slot -/

section Neg

variable {R : Type} [CommRing R]

theorem jp_neg (P : Fin 27 → R) : jp (-P) = -jp P := by
  funext i; fin_cases i <;> simp [jp]

theorem jq_neg (P : Fin 27 → R) : jq (-P) = -jq P := by
  funext i; fin_cases i <;> simp [jq]

theorem js_neg (P : Fin 27 → R) : js (-P) = -js P := by
  funext i; fin_cases i <;> simp [js]

theorem im7_neg (x : Fin 8 → R) : im7 (-x) = -im7 x := rfl

theorem dot7_neg_left (x y : Fin 7 → R) : dot7 (-x) y = -dot7 x y := by
  simp [dot7, Finset.sum_neg_distrib]

theorem dot7_neg_right (x y : Fin 7 → R) : dot7 x (-y) = -dot7 x y := by
  simp [dot7, Finset.sum_neg_distrib]

theorem dot8_neg_left (x y : Fin 8 → R) : dot8 (-x) y = -dot8 x y := by
  simp [dot8, Finset.sum_neg_distrib]

theorem dot8_neg_right (x y : Fin 8 → R) : dot8 x (-y) = -dot8 x y := by
  simp [dot8, Finset.sum_neg_distrib]

theorem dot27_neg_right (A B : Fin 27 → R) : dot27 A (-B) = -dot27 A B := by
  simp [dot27, Finset.sum_neg_distrib]

theorem cross_neg_left (x y : Fin 7 → R) : cross (-x) y = -cross x y := by
  funext k; fin_cases k <;> simp [cross] <;> ring

theorem cross_neg_right (x y : Fin 7 → R) : cross x (-y) = -cross x y := by
  funext k; fin_cases k <;> simp [cross] <;> ring

theorem octMul_neg_left (x y : Fin 8 → R) : octMul (-x) y = -octMul x y := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [octMul, Fin.cons_zero, im7_neg, dot7_neg_left, Pi.neg_apply]
    ring
  · simp only [octMul, Fin.cons_succ, im7_neg, cross_neg_left, Pi.neg_apply]
    ring

theorem octMul_neg_right (x y : Fin 8 → R) : octMul x (-y) = -octMul x y := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [octMul, Fin.cons_zero, im7_neg, dot7_neg_right, Pi.neg_apply]
    ring
  · simp only [octMul, Fin.cons_succ, im7_neg, cross_neg_right, Pi.neg_apply]
    ring

theorem octConj_neg (w : Fin 8 → R) : octConj (-w) = -octConj w := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [octConj, Fin.cons_zero, Pi.neg_apply]
  · simp only [octConj, Fin.cons_succ, Pi.neg_apply]

theorem octRe3_neg_1 (x y z : Fin 8 → R) : octRe3 (-x) y z = -octRe3 x y z := by
  simp only [octRe3, dot7, im7, phi3, e3, Pi.neg_apply, Fin.sum_univ_seven]
  ring

theorem octRe3_neg_2 (x y z : Fin 8 → R) : octRe3 x (-y) z = -octRe3 x y z := by
  simp only [octRe3, dot7, im7, phi3, e3, Pi.neg_apply, Fin.sum_univ_seven]
  ring

theorem octRe3_neg_3 (x y z : Fin 8 → R) : octRe3 x y (-z) = -octRe3 x y z := by
  simp only [octRe3, dot7, im7, phi3, e3, Pi.neg_apply, Fin.sum_univ_seven]
  ring

theorem N4tri_neg_1 (r : R) (P Q S : Fin 27 → R) : N4tri r (-P) Q S = -N4tri r P Q S := by
  simp only [N4tri, Pi.neg_apply, jp_neg, octRe3_neg_1]
  ring

theorem N4tri_neg_2 (r : R) (P Q S : Fin 27 → R) : N4tri r P (-Q) S = -N4tri r P Q S := by
  simp only [N4tri, Pi.neg_apply, jp_neg, jq_neg, js_neg, dot8_neg_left, octRe3_neg_2]
  ring

theorem N4tri_neg_3 (r : R) (P Q S : Fin 27 → R) : N4tri r P Q (-S) = -N4tri r P Q S := by
  simp only [N4tri, Pi.neg_apply, jp_neg, jq_neg, js_neg, dot8_neg_right, octRe3_neg_3]
  ring

theorem shOff_neg_tu (r t : R) (u v w : Fin 8 → R) :
    shOff r (-t) (-u) v w = -shOff r t u v w := by
  funext i
  simp only [shOff, octMul_neg_left, octConj_neg, Pi.neg_apply]
  ring

theorem shOff_neg_vw (r t : R) (u v w : Fin 8 → R) :
    shOff r t u (-v) (-w) = -shOff r t u v w := by
  funext i
  simp only [shOff, octMul_neg_right, octConj_neg, Pi.neg_apply]
  ring

theorem sharp2_neg_left (r : R) (P Q : Fin 27 → R) : sharp2 r (-P) Q = -sharp2 r P Q := by
  funext k
  fin_cases k <;> simp [sharp2, jp_neg, jq_neg, js_neg, dot8_neg_left, shOff_neg_tu] <;> ring

theorem sharp2_neg_right (r : R) (P Q : Fin 27 → R) : sharp2 r P (-Q) = -sharp2 r P Q := by
  funext k
  fin_cases k <;> simp [sharp2, jp_neg, jq_neg, js_neg, dot8_neg_right, shOff_neg_vw] <;> ring

end Neg

/-! ## One generator: the `U(1)` of `E₆ × U(1) ⊂ E₇` -/

/-- The weights on one block: `−3` on `α` (index `0`), `1` on `A`. DERIVED: the weights `−3, 1`
make `α N(A)` and `T(A, B)` invariant against `3, −1` on the other block; `28 = 1 + 27` the block
`(α, A)`. -/
noncomputable def e7U (a : Fin 28) : ℝ := if a = 0 then -3 else 1

/-- The diagonal of `e7Weight`: `e7U` on the first block, `−e7U` on the second. DERIVED: `28` the block size,
`56 = 28 + 28`. -/
noncomputable def e7WeightVec (i : Fin (28 + 28)) : ℂ :=
  ((Sum.elim e7U (fun a => -e7U a) (finSumFinEquiv.symm i) : ℝ) : ℂ)

/-- **The witness**: `diag(−3 on α, 1 on A, 3 on β, −1 on B)`. DERIVED: no numeral beyond `e7U`; `28`
the block size, `56 = 28 + 28`. -/
noncomputable def e7Weight : Matrix (Fin (28 + 28)) (Fin (28 + 28)) ℂ :=
  Matrix.diagonal e7WeightVec

theorem e7WeightVec_castAdd (a : Fin 28) : e7WeightVec (Fin.castAdd 28 a) = (e7U a : ℂ) := by
  simp only [e7WeightVec, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]

theorem e7WeightVec_natAdd (a : Fin 28) : e7WeightVec (Fin.natAdd 28 a) = -(e7U a : ℂ) := by
  simp only [e7WeightVec, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Complex.ofReal_neg]

theorem ftsAlpha_e7Weight (v : Fin (28 + 28) → ℂ) :
    ftsAlpha (e7Weight *ᵥ v) = -3 * ftsAlpha v := by
  simp only [ftsAlpha, e7Weight, Matrix.mulVec_diagonal, e7WeightVec_castAdd]
  simp [e7U]

theorem ftsBeta_e7Weight (v : Fin (28 + 28) → ℂ) :
    ftsBeta (e7Weight *ᵥ v) = 3 * ftsBeta v := by
  simp only [ftsBeta, e7Weight, Matrix.mulVec_diagonal, e7WeightVec_natAdd]
  simp [e7U]

theorem ftsA_e7Weight (v : Fin (28 + 28) → ℂ) : ftsA (e7Weight *ᵥ v) = ftsA v := by
  funext k
  simp only [ftsA, e7Weight, Matrix.mulVec_diagonal, e7WeightVec_castAdd]
  simp [e7U]

theorem ftsB_e7Weight (v : Fin (28 + 28) → ℂ) : ftsB (e7Weight *ᵥ v) = -ftsB v := by
  funext k
  simp only [ftsB, e7Weight, Matrix.mulVec_diagonal, e7WeightVec_natAdd, Pi.neg_apply]
  simp [e7U]

/-- The weights of the first block in `ℂ`. DERIVED: `28 = 1 + 27` the block `(α, A)`. -/
noncomputable def e7Uc (a : Fin 28) : ℂ := (e7U a : ℂ)

/-- `e7Weight` is `fromBlocks (diag u) 0 0 (diag (−u))` reindexed by `finSumFinEquiv`.

DERIVED: no numeral. -/
theorem e7Weight_eq_fromBlocks :
    e7Weight = (Matrix.fromBlocks (Matrix.diagonal e7Uc) 0 0
      (Matrix.diagonal (-e7Uc))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
  unfold e7Weight
  congr 1
  funext i
  simp only [e7WeightVec, Function.comp_apply]
  generalize finSumFinEquiv.symm i = s
  cases s <;> simp [e7Uc]

/-- **`e7Weight` is in `𝔰𝔭(56)`**: `W J + J Wᵀ = 0`, the weights of `i` and `28 + i` being
opposite.

DERIVED: `28` the block size of `USp(28)`. -/
theorem e7Weight_sp : e7Weight * Jsp 28 + Jsp 28 * e7Weight.transpose = 0 := by
  have hJ : Jsp 28 = (Matrix.J (Fin 28) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    simp [Jsp, Matrix.reindex_apply]
  rw [e7Weight_eq_fromBlocks, hJ, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  have hin : Matrix.fromBlocks (Matrix.diagonal e7Uc) 0 0 (Matrix.diagonal (-e7Uc))
        * Matrix.J (Fin 28) ℂ
      + Matrix.J (Fin 28) ℂ
        * (Matrix.fromBlocks (Matrix.diagonal e7Uc) 0 0 (Matrix.diagonal (-e7Uc))).transpose
      = 0 := by
    simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add, Matrix.diagonal_transpose, Matrix.transpose_zero]
    rw [← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.diagonal_neg]
  ext i j
  have h := congrFun (congrFun hin (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [Matrix.add_apply] using h

/-- **`e7Weight` is a generator of `ρ(𝔢₇)`** in the sense of `instGaugeLieE7`, and it is nonzero:
`lieGen` is not the zero predicate.

DERIVED: the index `castAdd 28 0` is the entry `−3`. -/
theorem lieGen_e7Weight :
    MassGap.ClayTreeG.GaugeLie.lieGen (G := E7) e7Weight ∧ e7Weight ≠ 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show e7Weight.conjTranspose = e7Weight
    unfold e7Weight
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [e7WeightVec]
  · exact e7Weight_sp
  · intro v
    show e7Q4 s2C (e7Weight *ᵥ v) v v v + e7Q4 s2C v (e7Weight *ᵥ v) v v
      + e7Q4 s2C v v (e7Weight *ᵥ v) v + e7Q4 s2C v v v (e7Weight *ᵥ v) = 0
    simp only [e7Q4, ftsAlpha_e7Weight, ftsBeta_e7Weight, ftsA_e7Weight, ftsB_e7Weight,
      dot27_neg_right, N4tri_neg_1, N4tri_neg_2, N4tri_neg_3, sharp2_neg_left, sharp2_neg_right]
    ring
  · intro h
    have h00 := congrFun (congrFun h (Fin.castAdd 28 0)) (Fin.castAdd 28 0)
    simp only [e7Weight, Matrix.diagonal_apply_eq, e7WeightVec_castAdd, Matrix.zero_apply] at h00
    simp [e7U] at h00

/-! ## The Clay statement at `E₇` -/

open MassGap.ClayTreeG MassGap.ClayStatementG MassGap.SymPlaqG

/-- **The Clay Yang–Mills statement for `E₇`**: `ClayStatementOf` at `E7`.

DERIVED: no numeral. -/
def ClayStatementE7 : Prop := ClayStatementOf E7

/-- **`ClayStatementOfDy E7`, the statement at the frozen tower, from
`ClayStatementAtG` on the symmetrised plaquette class**, which is
reflection closed (`symPlaqG_refl`). `ObserverLinkedG.clayStatementAtG_of_observer (G := E7)`
concludes the hypothesis from its inputs.

DERIVED: no numeral. -/
theorem clayStatementE7_of_atG (W : ConfFlowG E7)
    (h : ClayStatementAtG E7 W (SymPlaqClassG E7)) : ClayStatementOfDy E7 :=
  ⟨W, SymPlaqClassG E7, symPlaqG_refl E7, h⟩

-- The observer capstone elaborates at `E₇`: the six instance arguments resolve, and its conclusion
-- is `ClayStatementAtG E7 W (SymPlaqClassG E7)`, the hypothesis of `clayStatementE7_of_atG`.
example : True := by
  have _h := @MassGap.ObserverLinkedG.clayStatementAtG_of_observer E7 _ _ _ _ _ _
  trivial

end MassGap.GaugeE7

#print axioms MassGap.GaugeE7.jsp_mulVec_castAdd
#print axioms MassGap.GaugeE7.jsp_mulVec_natAdd
#print axioms MassGap.GaugeE7.jsp_form
#print axioms MassGap.GaugeE7.continuous_e7Quartic
#print axioms MassGap.GaugeE7.E7Sub
#print axioms MassGap.GaugeE7.isClosed_E7Sub
#print axioms MassGap.GaugeE7.e7Rep
#print axioms MassGap.GaugeE7.instGaugeGroupE7
#print axioms MassGap.GaugeE7.dim_E7
#print axioms MassGap.GaugeE7.wilsonDensityG_E7
#print axioms MassGap.GaugeE7.instGaugeSimpleE7
#print axioms MassGap.GaugeE7.instGaugeLieE7
#print axioms MassGap.GaugeE7.sharp2_neg_left
#print axioms MassGap.GaugeE7.sharp2_neg_right
#print axioms MassGap.GaugeE7.e7Weight_sp
#print axioms MassGap.GaugeE7.lieGen_e7Weight
#print axioms MassGap.GaugeE7.clayStatementE7_of_atG
