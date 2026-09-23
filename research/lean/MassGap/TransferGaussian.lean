import Mathlib
import MassGap.SliceTransferSelfAdjoint

/-!
# MassGap.TransferGaussian — the slice transfer kernel as a Gaussian, its positivity, and
injectivity of `transferCLM`

`SliceTransferSelfAdjoint.transferCLM` is a bounded self-adjoint operator on `L²` of a slice. This
module proves its kernel positive definite and the operator injective.

## Sections 1-3: the kernel in Gaussian form

`SliceTransfer.transferKernel b s V W = exp (-s V / 2) * exp (b * sliceForm V W) * exp (-s W / 2)`,
with `sliceForm V W = ∑ l, Re trace (V l * (W l)ᴴ)`. `CharacterExpansion.hsRe_eq_sum` presents each
`Re trace (A Bᴴ)` as the Euclidean inner product of the two matrices' `2 * N ^ 2` real coordinates.
On `SU N` every configuration has the same norm — `hsRe V V = Re trace 1 = N`
(`hsRe_self_of_su`) — so polarisation turns the inner product into a distance
(`sliceForm_eq_gaussian`):

    sliceForm V W = Fintype.card ι * N - sqDist V W / 2

and therefore (`transferKernel_gaussian`)

    transferKernel b s V W
      = exp (b * Fintype.card ι * N) * (exp (-s V / 2) * exp (-(b / 2) * sqDist V W) * exp (-s W / 2)).

`transferKernel_gaussian_factors` states the same as `c * (f V * G V W * f W)` with `0 < c` and
`0 < f`.

Scope: `-(b / 2) ≤ 0` is what makes the middle factor a decaying Gaussian. At `b < 0` the identity
still holds and the factor is `exp ((|b| / 2) * sqDist V W)`.

## Section 4: positive definiteness

`CharacterExpansion.wilson_kernel_nonneg` proves `exp (β * hsRe A B)` positive semidefinite for
`β ≥ 0` at one link, by expanding the exponential and writing each order as a sum of squares. Its
proof uses only that `hsRe A B = ∑ p, coord p A * coord p B` is a Gram form over a finite index, so
`gram_pow`, `gram_quadform_pow_eq_sum_sq` and `gram_exp_kernel_nonneg` restate it for an arbitrary
coordinate family. `sliceForm_eq_gram` writes the slice form as a Gram form over `ι × Coord N`, so
`sliceWeight_nonneg` and `transferKernel_posDef` follow at the slice, with no Schur product theorem.

`0 ≤ b` cannot be dropped: `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` computes the form
on two `SU 3` elements and it is nonnegative exactly when `β ≥ 0`.

## Sections 5-6: strict positive definiteness on finite families

`coords_separate` shows the coordinates separate slice configurations.
`MonomialsSeparateFinitely` states that a linear functional killing every monomial in the
coordinates kills every weight, and `transferKernel_strictly_posDef` reduces strict positive
definiteness to it. `monomials_separate_of_separating` proves that statement for any separating
coordinate family, by peeling one affine factor per configuration rather than expanding a Lagrange
product — `monomial_hyp_stable` is the stability of the hypothesis under that peeling, which rests
on `gmono_cons`. `monomialsSeparateFinitely_holds` instantiates it, and
`transferKernel_strictly_posDef'` is the unconditional form.
`monomialsSeparateFinitely_at_one` and `monomialsSeparateFinitely_at_two` are the first two cases.

Scope: this is strict positive definiteness of the kernel — every Gram matrix it forms on distinct
configurations is nonsingular — not yet `ker T = 0` on `L²`.

## Sections 7-8: density

`continuous_sliceCoord` makes each coordinate continuous, `coordAlgebra` is the subalgebra they
generate, `coordAlgebra_separatesPoints` is `coords_separate` bundled, and `coordAlgebra_dense` is
Stone–Weierstrass on the compact Hausdorff configuration space
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`, present at this pin;
`ContinuousMap.polynomialFunctions_closure_eq_top` is not, so the route goes through the general
subalgebra version). `coordAlgebra_dense_in_L2` carries that to `L²` through
`ContinuousMap.toLp_denseRange` and continuity of `ContinuousMap.toLp`.

## Sections 9-15: the integral expansion

`inner_transferCLM_eq_double_integral` writes `⟪T z, z⟫` as a double integral against the kernel.
`integral_integral_mul_self` turns a separable double integral into a square,
`sliceForm_pow_separates` and `abs_sliceForm_pow_le` supply the separation and the domination, and
`integral_exp_mul_eq_tsum` moves the exponential series through an integral for any bounded exponent
against an integrable function. Section 12 assembles the order-`k` double integral as
`∑ α, (gramCoeff μ φ f α) ^ 2` (`integral_integral_gram_pow`), section 13 sums the orders
(`integral_integral_exp_gram_eq_tsum`), and section 14 gives nonnegativity
(`integral_integral_exp_gram_nonneg`) and the vanishing case
(`gramCoeff_eq_zero_of_quadform_eq_zero`), the latter needing `summable_gram_orders` because `∑'` of
a non-summable family is `0` by convention. Section 15 instantiates all of it at the slice:
`abs_sliceCoord_le_one`, `sliceCoeff`, `slice_quadform_eq_tsum`, `slice_gramCoeff_eq_zero`.

The integrals here are iterated and never reordered, so no Fubini enters; `integral_const_mul` does
that work. The domination constant used at the slice is `Fintype.card ι * 2 * N ^ 2` from
`|coord| ≤ 1`, cruder than the `Fintype.card ι * N` of
`SliceTransferSelfAdjoint.abs_sliceForm_le` by a factor `2 * N`; only convergence is used and both
converge.

## Sections 16-18: `ker T = 0`

`sliceMonoCM_mul` makes a product of monomials a monomial, so their span is a subalgebra
(`monoSpan`) containing `coordAlgebra` (`coordAlgebra_le_monoSpan`).
`integral_mul_eq_zero_of_mem_span` and `integral_mul_eq_zero_of_mem_coordAlgebra` extend a vanishing
coefficient from monomials to the algebra, and `lp_eq_zero_of_sliceCoeff_eq_zero` and
`ae_eq_zero_of_sliceCoeff_eq_zero` conclude from density. `weighted` absorbs the kernel's diagonal
factors, `kernelFun_mul_eq_weighted` moves them onto `z`, `memLp_weighted` keeps the result in `L²`,
and `transferCLM_eq_zero` and `transferCLM_injective` are the conclusions, at every `b > 0`.

## Scope

* Injectivity is not `0 ∉ spectrum T`. On an infinite-dimensional space an injective operator whose
  inverse is unbounded has `0` in its spectrum, and `Reconstruction.hamiltonian`, which is
  `cfc (fun x => -Real.log x) T`, needs `-Real.log` continuous on the spectrum.
  `Reconstruction.reconstruct_qm_core` takes `1 ∈ spectrum T` and
  `spectrum T ⊆ {1} ∪ [ε, exp (-Δ)]` with `0 < ε` and returns the operator-theoretic conclusions on
  foundational axioms; that spectral hypothesis comes from decay through
  `MomentSupport.le_of_positive_weight_decay`.
* A carrier for this operator on `GNSHilbert.ymH` is not constructed here.
* `transferKernel_posDef` is positive definiteness of the kernel in the sense positivity of an
  integral operator means. Carrying Mathlib's Gaussian positive-definiteness across instead is not
  done here; Mathlib does not state it in this form.
* A positive-definite kernel stays positive-definite on any subset, the defining inequality being
  over finitely supported weights, so restricting from `(ℝ ^ (2 * N ^ 2)) ^ ι` to `(SU N) ^ ι` costs
  nothing.
-/

namespace MassGap.TransferGaussian

open MassGap MassGap.CharacterExpansion MassGap.SliceTransfer

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Every `SU(N)` matrix has the same Hilbert–Schmidt norm -/

/-- `hsRe V V = N` for `V : SU N`, since `V * Vᴴ = 1` and the identity matrix traces to the
dimension. Every configuration therefore has the same Hilbert–Schmidt norm, which is what lets
polarisation turn the cross form into a distance.

DERIVED: no numeral occurs in the statement; the value is the matrix size `N`, which is what the identity matrix traces to. -/
theorem hsRe_self_of_su (V : MassGap.SUN.SU N) :
    hsRe ((V : Matrix (Fin N) (Fin N) ℂ)) ((V : Matrix (Fin N) (Fin N) ℂ)) = (N : ℝ) := by
  have hu0 := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp V.2).1
  have hu : (V : Matrix (Fin N) (Fin N) ℂ)
      * Matrix.conjTranspose (V : Matrix (Fin N) (Fin N) ℂ) = 1 := hu0
  simp [hsRe, hu, Matrix.trace_one]

#print axioms hsRe_self_of_su

/-- The aggregate over the slice's links.

DERIVED: no numeral occurs; the value is the link count times the matrix size. -/
theorem sum_hsRe_self (V : ι → MassGap.SUN.SU N) :
    (∑ l : ι, hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((V l : Matrix (Fin N) (Fin N) ℂ)))
      = (Fintype.card ι : ℝ) * (N : ℝ) := by
  rw [Finset.sum_congr rfl (fun l _ => hsRe_self_of_su (V l))]
  simp [Finset.card_univ]

#print axioms sum_hsRe_self

/-- The cross form on the diagonal: `|ι|·N`, at every configuration.

DERIVED: no numeral occurs; the value is the link count times the matrix size. -/
theorem sliceForm_self (V : ι → MassGap.SUN.SU N) :
    sliceForm V V = (Fintype.card ι : ℝ) * (N : ℝ) :=
  sum_hsRe_self V

#print axioms sliceForm_self

/-! ## 2. The squared distance and the polarisation identity -/

/-- **The squared Euclidean distance between two slice configurations**, in the real coordinates
`CharacterExpansion.coord` supplies — `2N²` of them per link, `|ι|` links.

DERIVED: the `2` is the square, not a chosen exponent. -/
noncomputable def sqDist (V W : ι → MassGap.SUN.SU N) : ℝ :=
  ∑ l : ι, ∑ p : Coord N,
    (coord p ((V l : Matrix (Fin N) (Fin N) ℂ)) - coord p ((W l : Matrix (Fin N) (Fin N) ℂ))) ^ 2

#print axioms sqDist

/-- Polarisation, one link at a time.

DERIVED: `2` is the exponent of the squared difference and the cross-term coefficient a square of a difference produces. -/
theorem sq_dist_link (A B : Matrix (Fin N) (Fin N) ℂ) :
    (∑ p : Coord N, (coord p A - coord p B) ^ 2)
      = hsRe A A - 2 * hsRe A B + hsRe B B := by
  rw [hsRe_eq_sum, hsRe_eq_sum, hsRe_eq_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ => by ring)

#print axioms sq_dist_link

/-- `sliceForm V W = Fintype.card ι * N - sqDist V W / 2`. Polarisation link by link
(`sq_dist_link`), with `sum_hsRe_self` supplying both diagonal terms.

Scope: the reduction to a distance uses that all `SU N` configurations have the same norm; on a
group where they did not, the cross form would remain an inner product and not become a distance.

DERIVED: `2` is the halving in `sqDist V W / 2`, which is the `2` of the polarisation identity. -/
theorem sliceForm_eq_gaussian (V W : ι → MassGap.SUN.SU N) :
    sliceForm V W = (Fintype.card ι : ℝ) * (N : ℝ) - sqDist V W / 2 := by
  have hsum : sqDist V W
      = (∑ l : ι, hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((V l : Matrix (Fin N) (Fin N) ℂ)))
        - 2 * sliceForm V W
        + (∑ l : ι, hsRe ((W l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))) := by
    rw [sqDist, sliceForm, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => sq_dist_link _ _)
  rw [sum_hsRe_self V, sum_hsRe_self W] at hsum
  linarith

#print axioms sliceForm_eq_gaussian

/-! ## 3. The kernel, in Gaussian form -/

/-- The slice transfer kernel written as a Gaussian:

    transferKernel b s V W
      = exp (b * (Fintype.card ι * N)) * (exp (-s V / 2) * exp (-(b / 2) * sqDist V W) * exp (-s W / 2)).

`sliceForm_eq_gaussian` substituted into the definition and the exponents split.

Scope: only the middle factor depends on both arguments. The leading constant is a positive scalar
and the outer factors are a diagonal conjugation, neither of which changes the sign of a quadratic
form.

DERIVED: `2` appears as the even split of the intra-slice action between the two ends,
`-(s V) / 2` and `-(s W) / 2`, and as the halving `-(b / 2)` the polarisation identity produces. -/
theorem transferKernel_gaussian (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) :
    transferKernel b s V W
      = Real.exp (b * ((Fintype.card ι : ℝ) * (N : ℝ)))
        * (Real.exp (-(s V) / 2) * Real.exp (-(b / 2) * sqDist V W) * Real.exp (-(s W) / 2)) := by
  rw [transferKernel, sliceForm_eq_gaussian V W]
  rw [show b * ((Fintype.card ι : ℝ) * (N : ℝ) - sqDist V W / 2)
      = b * ((Fintype.card ι : ℝ) * (N : ℝ)) + -(b / 2) * sqDist V W by ring]
  rw [Real.exp_add]
  ring

#print axioms transferKernel_gaussian

/-- The same in the shape `c * (f V * exp (-(b / 2) * sqDist V W) * f W)` with `0 < c` and
`0 < f X` at every `X`: the two arguments meet only in the Gaussian factor.

DERIVED: `0` is the strict lower bound on the scalar `c` and on the diagonal factor `f`; `2` is the
even split of the intra-slice action and the halving from polarisation, as in
`transferKernel_gaussian`. -/
theorem transferKernel_gaussian_factors (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) :
    ∃ c : ℝ, 0 < c ∧ ∃ f : (ι → MassGap.SUN.SU N) → ℝ, (∀ X, 0 < f X) ∧
      transferKernel b s V W = c * (f V * Real.exp (-(b / 2) * sqDist V W) * f W) :=
  ⟨Real.exp (b * ((Fintype.card ι : ℝ) * (N : ℝ))), Real.exp_pos _,
   fun X => Real.exp (-(s X) / 2), fun X => Real.exp_pos _,
   transferKernel_gaussian b s V W⟩

#print axioms transferKernel_gaussian_factors

/-! ## 4. The kernel is positive definite

`CharacterExpansion.wilson_kernel_nonneg` proves `exp (β * hsRe A B)` positive semidefinite for
`β ≥ 0` at one link, by expanding the exponential and writing each order as an explicit sum of
squares (`quadform_pow_eq_sum_sq`). The slice form is a sum over links, so the slice weight is a
product of those kernels, and a product of positive kernels would need the Schur product theorem,
which this tree does not carry.

It is not needed. The proof of `wilson_kernel_nonneg` uses nothing about matrices, only that
`hsRe A B = ∑ p, coord p A * coord p B` is a Gram form over a finite index. The slice form is a Gram
form as well, over `ι × Coord N` in place of `Coord N`, so the same argument applies at the slice.
The three lemmas below are that argument stated for an arbitrary Gram form, with the single-link
case as an instance.
-/

/-- A degree-`k` monomial of a Gram form's coordinate functions. The analogue of
`CharacterExpansion.mono`, for an arbitrary coordinate family.

DERIVED: no numeral occurs; `k` is the monomial's degree. -/
noncomputable def gmono {P X : Type*} (φ : P → X → ℝ) {k : ℕ} (α : Fin k → P) (x : X) : ℝ :=
  ∏ t, φ (α t) x

#print axioms gmono

/-- `(∑ p, φ p x * φ p y) ^ k = ∑ α : Fin k → P, gmono φ α x * gmono φ α y`:
a power of a Gram form is a finite sum of terms each separating `x` from `y`, with the same function
on both sides. `CharacterExpansion.hsRe_pow` with the coordinate family abstracted, via
`Fintype.sum_pow`.

DERIVED: no numeral occurs in the statement. Multiplying out the power of a sum gives every paired
product with coefficient one, which is why no coefficient appears. -/
theorem gram_pow {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ) (k : ℕ) (x y : X) :
    (∑ p, φ p x * φ p y) ^ k = ∑ α : Fin k → P, gmono φ α x * gmono φ α y := by
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  unfold gmono
  rw [← Finset.prod_mul_distrib]

#print axioms gram_pow

/-- `∑ α, (∑ i, z i * gmono φ α (A i)) ^ 2 = ∑ i, ∑ j, z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k`:
the order-`k` quadratic form of a Gram form is a sum of squares.
`CharacterExpansion.quadform_pow_eq_sum_sq` with the coordinate family abstracted.

DERIVED: `2` is the square on the left-hand side, which is what pairing a term with itself produces. -/
theorem gram_quadform_pow_eq_sum_sq {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ)
    (k m : ℕ) (A : Fin m → X) (z : Fin m → ℝ) :
    (∑ α : Fin k → P, (∑ i, z i * gmono φ α (A i)) ^ 2)
      = ∑ i, ∑ j, z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k := by
  have hR : ∀ α : Fin k → P, (∑ i, z i * gmono φ α (A i)) ^ 2
      = ∑ i, ∑ j, (z i * gmono φ α (A i)) * (z j * gmono φ α (A j)) := by
    intro α
    rw [sq, Finset.sum_mul_sum]
  calc (∑ α : Fin k → P, (∑ i, z i * gmono φ α (A i)) ^ 2)
      = ∑ α : Fin k → P, ∑ i, ∑ j, (z i * gmono φ α (A i)) * (z j * gmono φ α (A j)) :=
        Finset.sum_congr rfl (fun α _ => hR α)
    _ = ∑ i, ∑ j, ∑ α : Fin k → P, (z i * gmono φ α (A i)) * (z j * gmono φ α (A j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [gram_pow φ k (A i) (A j), Finset.mul_sum]
        exact Finset.sum_congr rfl (fun α _ => by ring)

#print axioms gram_quadform_pow_eq_sum_sq

/-- `0 ≤ ∑ i, ∑ j, z i * z j * exp (β * ∑ p, φ p (A i) * φ p (A j))` for `0 ≤ β`:
the exponential of any Gram form is a positive semidefinite kernel.
`CharacterExpansion.wilson_kernel_nonneg` with the coordinate family abstracted. Each order is
`β ^ k / k !` times `gram_quadform_pow_eq_sum_sq`'s sum of squares, and the series converges to the
weight.

Scope: `0 ≤ β` cannot be dropped —
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` computes the form on two `SU 3` elements and
it is nonnegative exactly when `β ≥ 0`.

DERIVED: the one numeral is `0`, the lower bound on `β` and the lower bound asserted, which is the
content of positive semidefiniteness. -/
theorem gram_exp_kernel_nonneg {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ)
    {β : ℝ} (hβ : 0 ≤ β) {m : ℕ} (A : Fin m → X) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * Real.exp (β * ∑ p, φ p (A i) * φ p (A j)) := by
  have hterm : ∀ i j, HasSum
      (fun k : ℕ => MassGap.CharacterExpansion.wilsonCoef β k
        * (z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
      (z i * z j * Real.exp (β * ∑ p, φ p (A i) * φ p (A j))) := by
    intro i j
    have heq : (fun k : ℕ => MassGap.CharacterExpansion.wilsonCoef β k
          * (z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
        = fun k : ℕ => (z i * z j)
          * ((β * ∑ p, φ p (A i) * φ p (A j)) ^ k / (Nat.factorial k : ℝ)) := by
      funext k
      rw [MassGap.CharacterExpansion.wilsonCoef, mul_pow]
      ring
    rw [heq]
    exact (MassGap.CharacterExpansion.hasSum_exp_div
      (β * ∑ p, φ p (A i) * φ p (A j))).mul_left (z i * z j)
  have hsum : HasSum
      (fun k : ℕ => ∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef β k
        * (z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
      (∑ i, ∑ j, z i * z j * Real.exp (β * ∑ p, φ p (A i) * φ p (A j))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hterm i j))
  have hnn : ∀ k : ℕ, 0 ≤ ∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef β k
      * (z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k) := by
    intro k
    have h1 : (∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef β k
          * (z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
        = MassGap.CharacterExpansion.wilsonCoef β k
          * ∑ i, ∑ j, z i * z j * (∑ p, φ p (A i) * φ p (A j)) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    rw [h1, ← gram_quadform_pow_eq_sum_sq φ k m A z]
    exact mul_nonneg (MassGap.CharacterExpansion.wilsonCoef_nonneg hβ k)
      (Finset.sum_nonneg (fun α _ => sq_nonneg _))
  rw [← hsum.tsum_eq]
  exact tsum_nonneg hnn

#print axioms gram_exp_kernel_nonneg

/-! ### The slice form is a Gram form, so the slice weight is positive -/

/-- The slice form written as a single Gram form over `ι × Coord N`. This is the one step that
carries `CharacterExpansion`'s single-link machinery to the whole slice, and it is bookkeeping:
`hsRe_eq_sum` on each link, then `Fintype.sum_prod_type` to merge the two indices.

DERIVED: no numeral occurs in the statement; the index type `ι × Coord N` is what merges the per-link and per-coordinate sums. -/
theorem sliceForm_eq_gram (V W : ι → MassGap.SUN.SU N) :
    sliceForm V W
      = ∑ q : ι × Coord N,
          coord q.2 ((V q.1 : Matrix (Fin N) (Fin N) ℂ))
            * coord q.2 ((W q.1 : Matrix (Fin N) (Fin N) ℂ)) := by
  rw [Fintype.sum_prod_type, sliceForm]
  exact Finset.sum_congr rfl (fun l _ => hsRe_eq_sum _ _)

#print axioms sliceForm_eq_gram

/-- `0 ≤ ∑ i, ∑ j, z i * z j * exp (b * sliceForm (V i) (V j))` for `0 ≤ b`:
`gram_exp_kernel_nonneg` at `P := ι × Coord N`, through `sliceForm_eq_gram`. The slice form is
itself a Gram form, so no Schur product theorem is needed to pass from one link to the slice.

DERIVED: `0` is the lower bound on the coupling and the lower bound asserted on the form. -/
theorem sliceWeight_nonneg {b : ℝ} (hb : 0 ≤ b) {m : ℕ}
    (V : Fin m → (ι → MassGap.SUN.SU N)) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * Real.exp (b * sliceForm (V i) (V j)) := by
  have h := gram_exp_kernel_nonneg
    (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
      coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) hb V z
  simpa only [← sliceForm_eq_gram] using h

#print axioms sliceWeight_nonneg

/-- `0 ≤ ∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j)` for `0 ≤ b`. The diagonal factors
`exp (-s (V i) / 2)` are absorbed into the weights, which is all a diagonal conjugation does to a
quadratic form, and `sliceWeight_nonneg` finishes.

DERIVED: `0` is the lower bound on `b`, inherited from `sliceWeight_nonneg`, and the lower bound
asserted on the form. The even split of the intra-slice action lives in `transferKernel` and is
absorbed into the weights in the proof. -/
theorem transferKernel_posDef {b : ℝ} (hb : 0 ≤ b) (s : (ι → MassGap.SUN.SU N) → ℝ) {m : ℕ}
    (V : Fin m → (ι → MassGap.SUN.SU N)) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j) := by
  have hrw : (∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j))
      = ∑ i, ∑ j, (fun t => z t * Real.exp (-(s (V t)) / 2)) i
          * (fun t => z t * Real.exp (-(s (V t)) / 2)) j
          * Real.exp (b * sliceForm (V i) (V j)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [transferKernel]
    ring
  rw [hrw]
  exact sliceWeight_nonneg hb V _

#print axioms transferKernel_posDef

/-! ## 5. Separation, and strict positivity on finite families

Strict positivity of the quadratic form is what the expansion gives a criterion for. Writing
`w i = z i * exp (-s (V i) / 2)`, the form is

    ∑ k, (b ^ k / k !) * ∑ α, (∑ i, w i * gmono φ α (V i)) ^ 2

so at `0 < b` it vanishes exactly when every coefficient `∑ i, w i * gmono φ α (V i)` does, that is,
when the functional `q ↦ ∑ i, w i * q (V i)` kills every monomial in the coordinates.

`coords_separate` supplies the geometric input: two distinct slice configurations differ at some
link, hence in some matrix entry, hence in that entry's real or imaginary part. That is also the
input Stone–Weierstrass consumes in section 7.

`MonomialsSeparateFinitely` names the step from that to `w = 0`, and
`transferKernel_strictly_posDef` proves strict positivity from it. Section 6 discharges it.
-/

/-- Two distinct slice configurations differ at some coordinate: they differ at some link, hence in
some matrix entry, hence in that entry's real or imaginary part, which is one of the `coord`
functions the Gram form is built from.

DERIVED: no numeral occurs in the statement. -/
theorem coords_separate {V W : ι → MassGap.SUN.SU N} (h : V ≠ W) :
    ∃ q : ι × Coord N,
      coord q.2 ((V q.1 : Matrix (Fin N) (Fin N) ℂ))
        ≠ coord q.2 ((W q.1 : Matrix (Fin N) (Fin N) ℂ)) := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp h
  have hm : (V l : Matrix (Fin N) (Fin N) ℂ) ≠ (W l : Matrix (Fin N) (Fin N) ℂ) := by
    intro hc
    exact hl (Subtype.ext hc)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  rcases Classical.em (((V l : Matrix (Fin N) (Fin N) ℂ) i j).re
      = ((W l : Matrix (Fin N) (Fin N) ℂ) i j).re) with hre | hre
  · refine ⟨(l, (i, j, false)), ?_⟩
    simp only [coord]
    intro hc
    exact hj (Complex.ext hre hc)
  · exact ⟨(l, (i, j, true)), hre⟩

#print axioms coords_separate

/-- The proposition: for an injective family of configurations `V` and weights `w`, if
`∑ i, w i * gmono φ α (V i) = 0` at every monomial `α`, then every `w i` is `0`. A `Prop`;
`monomialsSeparateFinitely_holds` proves it below, and `transferKernel_strictly_posDef` consumes it.

DERIVED: the one numeral is `0`, the value of every monomial coefficient in the hypothesis and of
every weight in the conclusion. -/
def MonomialsSeparateFinitely (ι : Type) [Fintype ι] (N : ℕ) : Prop :=
  ∀ {m : ℕ} (V : Fin m → (ι → MassGap.SUN.SU N)) (w : Fin m → ℝ),
    Function.Injective V →
    (∀ (k : ℕ) (α : Fin k → ι × Coord N),
      ∑ i, w i * gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
        coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α (V i) = 0) →
    ∀ i, w i = 0

#print axioms MonomialsSeparateFinitely

/-- The one-configuration case, directly: the degree-zero monomial is the empty product, so the
hypothesis at `k = 0` reads `w 0 = 0`.

DERIVED: `1` is the number of configurations, `Fin 1`; `0` is the value of every monomial coefficient in the hypothesis and of every weight in the conclusion. -/
theorem monomialsSeparateFinitely_at_one
    (V : Fin 1 → (ι → MassGap.SUN.SU N)) (w : Fin 1 → ℝ)
    (hmono : ∀ (k : ℕ) (α : Fin k → ι × Coord N),
      ∑ i, w i * gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
        coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α (V i) = 0) :
    ∀ i, w i = 0 := by
  intro i
  have h := hmono 0 (fun t => t.elim0)
  simpa [gmono, Fin.sum_univ_one, Fin.eq_zero i] using h

#print axioms monomialsSeparateFinitely_at_one

/-- From a vanishing quadratic form at `0 < b`, every paired coefficient vanishes: each order
contributes `b ^ k / k !` times a sum of squares, all nonnegative, so a total of zero forces every
order, every square in it, and hence every `∑ i, w i * gmono φ α (A i)` to zero.

DERIVED: `0` is the strict lower bound on `b`, the value of the vanishing quadratic form, and the value of each extracted coefficient. -/
theorem gram_exp_kernel_eq_zero_coeffs {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ)
    {b : ℝ} (hb : 0 < b) {m : ℕ} (A : Fin m → X) (w : Fin m → ℝ)
    (hzero : (∑ i, ∑ j, w i * w j * Real.exp (b * ∑ p, φ p (A i) * φ p (A j))) = 0) :
    ∀ (k : ℕ) (α : Fin k → P), ∑ i, w i * gmono φ α (A i) = 0 := by
  have hb0 : (0 : ℝ) ≤ b := le_of_lt hb
  -- the series, exactly as in `gram_exp_kernel_nonneg`
  have hterm : ∀ i j, HasSum
      (fun k : ℕ => MassGap.CharacterExpansion.wilsonCoef b k
        * (w i * w j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
      (w i * w j * Real.exp (b * ∑ p, φ p (A i) * φ p (A j))) := by
    intro i j
    have heq : (fun k : ℕ => MassGap.CharacterExpansion.wilsonCoef b k
          * (w i * w j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
        = fun k : ℕ => (w i * w j)
          * ((b * ∑ p, φ p (A i) * φ p (A j)) ^ k / (Nat.factorial k : ℝ)) := by
      funext k
      rw [MassGap.CharacterExpansion.wilsonCoef, mul_pow]
      ring
    rw [heq]
    exact (MassGap.CharacterExpansion.hasSum_exp_div
      (b * ∑ p, φ p (A i) * φ p (A j))).mul_left (w i * w j)
  have hsum : HasSum
      (fun k : ℕ => ∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef b k
        * (w i * w j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
      (∑ i, ∑ j, w i * w j * Real.exp (b * ∑ p, φ p (A i) * φ p (A j))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hterm i j))
  -- each order rewrites to a coefficient times a sum of squares
  have hrw : ∀ k : ℕ, (∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef b k
        * (w i * w j * (∑ p, φ p (A i) * φ p (A j)) ^ k))
      = MassGap.CharacterExpansion.wilsonCoef b k
        * ∑ α : Fin k → P, (∑ i, w i * gmono φ α (A i)) ^ 2 := by
    intro k
    rw [gram_quadform_pow_eq_sum_sq φ k m A w, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
  have hnn : ∀ k : ℕ, 0 ≤ ∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef b k
      * (w i * w j * (∑ p, φ p (A i) * φ p (A j)) ^ k) := by
    intro k
    rw [hrw k]
    exact mul_nonneg (MassGap.CharacterExpansion.wilsonCoef_nonneg hb0 k)
      (Finset.sum_nonneg (fun α _ => sq_nonneg _))
  -- a convergent series of nonnegatives summing to zero has every term zero
  intro k α
  have hle := le_hasSum hsum k (fun j _ => hnn j)
  rw [hzero] at hle
  have hk0 : (∑ i, ∑ j, MassGap.CharacterExpansion.wilsonCoef b k
      * (w i * w j * (∑ p, φ p (A i) * φ p (A j)) ^ k)) = 0 := le_antisymm hle (hnn k)
  rw [hrw k] at hk0
  have hcpos : 0 < MassGap.CharacterExpansion.wilsonCoef b k := by
    rw [MassGap.CharacterExpansion.wilsonCoef]
    exact div_pos (pow_pos hb k) (by positivity)
  have hsq : (∑ α : Fin k → P, (∑ i, w i * gmono φ α (A i)) ^ 2) = 0 := by
    rcases mul_eq_zero.mp hk0 with h | h
    · exact absurd h (ne_of_gt hcpos)
    · exact h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => sq_nonneg _)).mp hsq α
    (Finset.mem_univ α)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

#print axioms gram_exp_kernel_eq_zero_coeffs

/-- Given `MonomialsSeparateFinitely ι N`, `0 < b`, an injective family of configurations and a
vanishing quadratic form, every weight is zero. The diagonal factors are absorbed into the weights
and `gram_exp_kernel_eq_zero_coeffs` extracts the coefficients, which the hypothesis then kills.
With `transferKernel_posDef` this is strict positive definiteness on finite families.

DERIVED: `0` is the strict lower bound on `b`, the value of the vanishing quadratic form, and the value of each weight concluded. -/
theorem transferKernel_strictly_posDef (hsep : MonomialsSeparateFinitely ι N)
    {b : ℝ} (hb : 0 < b) (s : (ι → MassGap.SUN.SU N) → ℝ) {m : ℕ}
    (V : Fin m → (ι → MassGap.SUN.SU N)) (hV : Function.Injective V) (z : Fin m → ℝ)
    (hzero : (∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j)) = 0) :
    ∀ i, z i = 0 := by
  set w : Fin m → ℝ := fun t => z t * Real.exp (-(s (V t)) / 2) with hw
  have hrw : (∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j))
      = ∑ i, ∑ j, w i * w j * Real.exp (b * sliceForm (V i) (V j)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [transferKernel, hw]
    ring
  rw [hrw] at hzero
  have hgram : (∑ i, ∑ j, w i * w j
      * Real.exp (b * ∑ q : ι × Coord N,
          coord q.2 ((V i q.1 : Matrix (Fin N) (Fin N) ℂ))
            * coord q.2 ((V j q.1 : Matrix (Fin N) (Fin N) ℂ)))) = 0 := by
    simpa only [← sliceForm_eq_gram] using hzero
  have hcoeff := gram_exp_kernel_eq_zero_coeffs
    (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
      coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) hb V w hgram
  have hwzero := hsep V w hV hcoeff
  intro i
  have h := hwzero i
  rw [hw] at h
  have hexp : Real.exp (-(s (V i)) / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  simpa [hexp] using h

#print axioms transferKernel_strictly_posDef

/-- The two-configuration case. `coords_separate` gives one coordinate `q` telling the two apart;
the degree-zero monomial gives `w 0 + w 1 = 0`, the degree-one monomial at `q` gives
`w 0 * φ q (V 0) + w 1 * φ q (V 1) = 0`, and substituting the first into the second leaves
`w 0 * (φ q (V 0) - φ q (V 1)) = 0` with a nonzero difference.

DERIVED: `2` is the number of configurations, `Fin 2`; `0` is the value of every monomial
coefficient in the hypothesis and of every weight in the conclusion. The degrees `0` and `1` the
proof uses are the empty monomial and a single coordinate. -/
theorem monomialsSeparateFinitely_at_two
    (V : Fin 2 → (ι → MassGap.SUN.SU N)) (hV : Function.Injective V) (w : Fin 2 → ℝ)
    (hmono : ∀ (k : ℕ) (α : Fin k → ι × Coord N),
      ∑ i, w i * gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
        coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α (V i) = 0) :
    ∀ i, w i = 0 := by
  have hne : V 0 ≠ V 1 := by
    intro h
    exact absurd (hV h) (by decide)
  obtain ⟨q, hq⟩ := coords_separate hne
  have h0 := hmono 0 (fun t => t.elim0)
  have h1 := hmono 1 (fun _ => q)
  simp only [gmono, Fin.sum_univ_two, Finset.univ_eq_empty, Finset.prod_empty,
    Fin.prod_univ_one, mul_one] at h0 h1
  have hw0 : w 0 = 0 := by
    have hsub : w 0 * (coord q.2 ((V 0 q.1 : Matrix (Fin N) (Fin N) ℂ))
        - coord q.2 ((V 1 q.1 : Matrix (Fin N) (Fin N) ℂ))) = 0 := by
      have hw1 : w 1 = -w 0 := by linarith
      rw [hw1] at h1
      linarith [h1]
    rcases mul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hq
  have hw1 : w 1 = 0 := by linarith [h0, hw0]
  intro i
  fin_cases i
  · exact hw0
  · exact hw1

#print axioms monomialsSeparateFinitely_at_two

/-! ## 6. The separation theorem

A Lagrange polynomial expanded into monomials would need the multinomial expansion and an
enumeration of subsets. Instead, the hypothesis — that the functional `q ↦ ∑ i, w i * q (V i)` kills
every monomial — is stable under replacing the weights `w i` by `w i * (φ q (V i) - c)` at any
coordinate `q` and constant `c`, because `φ q * gmono α` is the monomial at `Fin.cons q α` and the
rest is linearity (`monomial_hyp_stable`).

So the affine factors are applied one at a time to the weights rather than multiplied out. After one
factor for each configuration other than `j`, each vanishing at its own configuration, only the
`j`-th weight survives and the degree-zero monomial reads it off.
-/

/-- Prepending an index to a monomial multiplies it by that coordinate.

DERIVED: no numeral occurs in the statement. -/
theorem gmono_cons {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ) {k : ℕ} (q : P)
    (α : Fin k → P) (x : X) :
    gmono φ (Fin.cons q α) x = φ q x * gmono φ α x := by
  simp [gmono, Fin.prod_univ_succ]

#print axioms gmono_cons

/-- If the functional with weights `w` kills every monomial, so does the functional with weights
`w i * (φ q (V i) - c)`, at any coordinate `q` and constant `c`. The proof splits each term using
`gmono_cons`, which makes `φ q * gmono α` the monomial at `Fin.cons q α`, and uses linearity for the
rest.

DERIVED: `0` is the value the functional takes on every monomial, in both hypothesis and conclusion. -/
theorem monomial_hyp_stable {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ) {m : ℕ}
    (V : Fin m → X) (w : Fin m → ℝ) (q : P) (c : ℝ)
    (h : ∀ (k : ℕ) (α : Fin k → P), ∑ i, w i * gmono φ α (V i) = 0) :
    ∀ (k : ℕ) (α : Fin k → P),
      ∑ i, (w i * (φ q (V i) - c)) * gmono φ α (V i) = 0 := by
  intro k α
  have hsplit : ∀ i, (w i * (φ q (V i) - c)) * gmono φ α (V i)
      = w i * gmono φ (Fin.cons q α) (V i) - c * (w i * gmono φ α (V i)) := by
    intro i
    rw [gmono_cons]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    h (k + 1) (Fin.cons q α), h k α]
  ring

#print axioms monomial_hyp_stable

/-- For any coordinate family separating the configurations, a functional killing every monomial
kills every weight. The proof peels one affine factor per configuration other than `j` — each
vanishing at its own configuration and, by separation, not at `V j` — using `monomial_hyp_stable`
each time; after all of them only the `j`-th weight survives, and the degree-zero monomial reads it
off.

Scope: no multinomial expansion or enumeration of subsets is used; the factors are applied to the
weights one at a time.

DERIVED: the one numeral is `0`, the value of every monomial coefficient in the hypothesis and of
every weight in the conclusion. -/
theorem monomials_separate_of_separating {P : Type*} [Fintype P] {X : Type*} (φ : P → X → ℝ)
    {m : ℕ} (V : Fin m → X) (w : Fin m → ℝ)
    (hsep : ∀ i j : Fin m, i ≠ j → ∃ q, φ q (V i) ≠ φ q (V j))
    (h : ∀ (k : ℕ) (α : Fin k → P), ∑ i, w i * gmono φ α (V i) = 0) :
    ∀ j, w j = 0 := by
  intro j
  -- if `j` is the only configuration, degree zero settles it outright
  by_cases hone : ∀ a : Fin m, a = j
  · have hz := h 0 (fun t => t.elim0)
    have hgm : ∀ x : X, gmono φ (fun t : Fin 0 => t.elim0) x = 1 := fun x => by simp [gmono]
    simp only [hgm, mul_one] at hz
    have hs : ∑ i, w i = w j :=
      Finset.sum_eq_single j (fun i _ hij => absurd (hone i) hij)
        (fun hc => absurd (Finset.mem_univ j) hc)
    rw [hs] at hz
    exact hz
  push_neg at hone
  obtain ⟨a0, ha0⟩ := hone
  haveI : Nonempty P := ⟨(hsep a0 j ha0).choose⟩
  -- a separating coordinate for each other configuration, against `V j`
  have hchoice : ∀ a : Fin m, ∃ q : P, a ≠ j → φ q (V a) ≠ φ q (V j) := by
    intro a
    by_cases ha : a = j
    · exact ⟨Classical.arbitrary P, fun hc => absurd ha hc⟩
    · obtain ⟨q, hq⟩ := hsep a j ha
      exact ⟨q, fun _ => hq⟩
  choose qq hqq using hchoice
  -- peeling any set of factors preserves the hypothesis
  have key : ∀ S : Finset (Fin m), ∀ (k : ℕ) (α : Fin k → P),
      ∑ i, (w i * ∏ a ∈ S, (φ (qq a) (V i) - φ (qq a) (V a))) * gmono φ α (V i) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using h
    | insert a S ha ih =>
        intro k α
        have hstep := monomial_hyp_stable φ V
          (fun i => w i * ∏ b ∈ S, (φ (qq b) (V i) - φ (qq b) (V b)))
          (qq a) (φ (qq a) (V a)) ih k α
        refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) hstep
        rw [Finset.prod_insert ha]
        ring
  -- with every other configuration killed, degree zero reads off `w j`
  have hzero := key (Finset.univ.erase j) 0 (fun t => t.elim0)
  have hgm : ∀ x : X, gmono φ (fun t : Fin 0 => t.elim0) x = 1 := by
    intro x; simp [gmono]
  simp only [hgm, mul_one] at hzero
  have hsingle : ∑ i, w i * ∏ a ∈ Finset.univ.erase j, (φ (qq a) (V i) - φ (qq a) (V a))
      = w j * ∏ a ∈ Finset.univ.erase j, (φ (qq a) (V j) - φ (qq a) (V a)) := by
    refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun hc => absurd (Finset.mem_univ j) hc)
    have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    have : ∏ a ∈ Finset.univ.erase j, (φ (qq a) (V i) - φ (qq a) (V a)) = 0 :=
      Finset.prod_eq_zero hmem (by ring)
    rw [this, mul_zero]
  rw [hsingle] at hzero
  have hprod : (∏ a ∈ Finset.univ.erase j, (φ (qq a) (V j) - φ (qq a) (V a))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a hmem => ?_)
    have hne : a ≠ j := (Finset.mem_erase.mp hmem).1
    have := hqq a hne
    exact fun hc => this (by linarith [sub_eq_zero.mp hc])
  rcases mul_eq_zero.mp hzero with hw | hp
  · exact hw
  · exact absurd hp hprod

#print axioms monomials_separate_of_separating

/-- `MonomialsSeparateFinitely ι N`, by `monomials_separate_of_separating` with `coords_separate`
as the separation input; injectivity of `V` turns index distinctness into configuration
distinctness.

DERIVED: no numeral occurs in the statement; the vanishing conditions live inside `MonomialsSeparateFinitely`. -/
theorem monomialsSeparateFinitely_holds : MonomialsSeparateFinitely ι N := by
  intro m V w hV hmono
  refine monomials_separate_of_separating _ V w (fun i j hij => ?_) hmono
  have hne : V i ≠ V j := fun hc => hij (hV hc)
  obtain ⟨q, hq⟩ := coords_separate hne
  exact ⟨q, hq⟩

#print axioms monomialsSeparateFinitely_holds

/-- `transferKernel_strictly_posDef` with its hypothesis discharged by
`monomialsSeparateFinitely_holds`: at distinct configurations and `0 < b`, a vanishing quadratic
form forces every weight to zero.

Scope: this is strict positive definiteness of the kernel on finite families — every Gram matrix it
forms on distinct configurations is nonsingular. It is a statement about sums over `Fin m`, with no
integral in it. `ker T = 0` for the operator on `L²` needs in addition the density of sections 7-8
and the integral expansion of sections 9-15; `transferCLM_injective` is where the three meet.

DERIVED: `0` is the strict lower bound on `b`, the value of the vanishing quadratic form, and the value of each weight concluded. -/
theorem transferKernel_strictly_posDef' {b : ℝ} (hb : 0 < b)
    (s : (ι → MassGap.SUN.SU N) → ℝ) {m : ℕ}
    (V : Fin m → (ι → MassGap.SUN.SU N)) (hV : Function.Injective V) (z : Fin m → ℝ)
    (hzero : (∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j)) = 0) :
    ∀ i, z i = 0 :=
  transferKernel_strictly_posDef monomialsSeparateFinitely_holds hb s V hV z hzero

#print axioms transferKernel_strictly_posDef'

/-! ## 7. The coordinate subalgebra is dense in `C(X, ℝ)`

Lifting strict positive definiteness of the kernel to `ker T = 0` for the operator needs the
coordinate functions to generate a dense subalgebra of the continuous functions. This section is the
first step.

`SUN`'s `CompactSpace` and `IsTopologicalGroup` instances, both anonymous, make `SU N` compact
Hausdorff, and `ι → SU N` is then compact Hausdorff as a product.
`OddLagSplit.continuous_su_entry` makes each matrix entry continuous and `coord` is a real or
imaginary part of one. `coords_separate` is the separating-points input, and
`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints` is Stone–Weierstrass,
present at this Mathlib pin.
-/

/-- Each coordinate function is continuous on the configuration space: evaluation at a link, then a
matrix entry, then a real or imaginary part.

DERIVED: no numeral occurs in the statement. -/
theorem continuous_sliceCoord (q : ι × Coord N) :
    Continuous (fun U : ι → MassGap.SUN.SU N =>
      coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) := by
  have hentry : Continuous (fun U : ι → MassGap.SUN.SU N =>
      ((U q.1 : Matrix (Fin N) (Fin N) ℂ)) q.2.1 q.2.2.1) :=
    (MassGap.OddLagSplit.continuous_su_entry q.2.1 q.2.2.1).comp (continuous_apply q.1)
  by_cases hb : q.2.2.2 = true
  · have hshape : (fun U : ι → MassGap.SUN.SU N =>
        coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ)))
        = fun U : ι → MassGap.SUN.SU N =>
          (((U q.1 : Matrix (Fin N) (Fin N) ℂ)) q.2.1 q.2.2.1).re := by
      funext U; simp [coord, hb]
    rw [hshape]
    exact Complex.continuous_re.comp hentry
  · simp only [Bool.not_eq_true] at hb
    have hshape : (fun U : ι → MassGap.SUN.SU N =>
        coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ)))
        = fun U : ι → MassGap.SUN.SU N =>
          (((U q.1 : Matrix (Fin N) (Fin N) ℂ)) q.2.1 q.2.2.1).im := by
      funext U; simp [coord, hb]
    rw [hshape]
    exact Complex.continuous_im.comp hentry

#print axioms continuous_sliceCoord

/-- A coordinate function as a bundled continuous map.

DERIVED: no numeral occurs. -/
noncomputable def sliceCoordCM (q : ι × Coord N) :
    C(ι → MassGap.SUN.SU N, ℝ) :=
  ⟨fun U => coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ)), continuous_sliceCoord q⟩

#print axioms sliceCoordCM

/-- **THE COORDINATE SUBALGEBRA** of `C(X, ℝ)` — everything the coordinates generate. Its elements
are exactly the polynomial combinations of the `coord` functions, which is the span of the monomials
`gmono` ranges over.

DERIVED: no numeral occurs. -/
noncomputable def coordAlgebra (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Subalgebra ℝ C(ι → MassGap.SUN.SU N, ℝ) :=
  Algebra.adjoin ℝ (Set.range (sliceCoordCM (ι := ι) (N := N)))

#print axioms coordAlgebra

/-- **IT SEPARATES POINTS**, which is `coords_separate` bundled.

DERIVED: no numeral occurs in the statement. -/
theorem coordAlgebra_separatesPoints :
    (coordAlgebra ι N).SeparatesPoints := by
  intro x y hxy
  obtain ⟨q, hq⟩ := coords_separate (V := x) (W := y) hxy
  refine ⟨sliceCoordCM q, ?_, ?_⟩
  · exact ⟨sliceCoordCM q, Algebra.subset_adjoin ⟨q, rfl⟩, rfl⟩
  · simpa [sliceCoordCM] using hq

#print axioms coordAlgebra_separatesPoints

/-- **AND THEREFORE IT IS DENSE**: its topological closure is everything.

Stone–Weierstrass on a compact Hausdorff space, with `coordAlgebra_separatesPoints` as the input.
This is the first half of the density step `ker T = 0` needs; the second is
`MeasureTheory.Lp.boundedContinuousFunction_dense`, carrying it from `C(X, ℝ)` to `L²`.

DERIVED: no numeral occurs in the statement. -/
theorem coordAlgebra_dense :
    (coordAlgebra ι N).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    coordAlgebra_separatesPoints

#print axioms coordAlgebra_dense

/-! ## 8. …and dense in `L²`

`coordAlgebra_dense` is sup-norm density in `C(X, ℝ)`. Carrying it to `L²` uses
`ContinuousMap.toLp_denseRange`, which makes the continuous functions dense in `Lᵖ`, and continuity
of `ContinuousMap.toLp`, which is a continuous linear map. Both are present at this Mathlib pin with
every instance resolving for `sliceHaar`. A continuous map sends a dense set to one whose closure
contains the whole range, and that range is already dense.
-/

/-- The image of the coordinate subalgebra under `ContinuousMap.toLp` is dense in `L²`.
`coordAlgebra_dense` gives sup-norm density in `C(X, ℝ)`, and continuity of `ContinuousMap.toLp`
together with `ContinuousMap.toLp_denseRange` carries it across.

This is one of the three ingredients `transferCLM_injective` combines: strict positive definiteness
on finite families (`transferKernel_strictly_posDef'`, section 6), this density, and the integral
expansion `slice_gramCoeff_eq_zero` (section 15), which is what connects a vanishing quadratic form
to vanishing monomial integrals. The integrals in that expansion are iterated and never reordered,
so `integral_const_mul` suffices and no Fubini enters; what it does use is the series interchange of
section 11.

DERIVED: the one numeral is `2`, the exponent of the `Lᵖ` space, which is the one an inner product lives on. -/
theorem coordAlgebra_dense_in_L2 :
    Dense ((ContinuousMap.toLp (E := ℝ) 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) ℝ) ''
      (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ))) := by
  set T := (ContinuousMap.toLp (E := ℝ) 2
    (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) ℝ) with hT
  have hcont : Continuous T := T.continuous
  have hSdense : closure (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ)) = Set.univ := by
    have h := coordAlgebra_dense (ι := ι) (N := N)
    rw [← Subalgebra.topologicalClosure_coe, h]
    simp
  have hrange : Set.range T
      ⊆ closure (T '' (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ))) := by
    rintro y ⟨x, rfl⟩
    have hx : x ∈ closure (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ)) := by
      rw [hSdense]; trivial
    exact image_closure_subset_closure_image hcont ⟨x, hx, rfl⟩
  have hTdense : DenseRange T := ContinuousMap.toLp_denseRange (𝕜 := ℝ) (E := ℝ) (p := 2)
    (μ := MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) (by norm_num)
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  calc (Set.univ : Set _) = closure (Set.range T) := hTdense.closure_range.symm
    _ ⊆ closure (closure (T '' (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ)))) :=
        closure_mono hrange
    _ = closure (T '' (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ))) := closure_closure

#print axioms coordAlgebra_dense_in_L2

/-! ## 9. The quadratic form as a double integral

The integral analogue of `gram_exp_kernel_eq_zero_coeffs` has two steps: write `⟪T z, z⟫` as a
double integral against the kernel, then expand the exponential inside it. This section is the
first, through `SlabKernelOperator`'s API: `L2.inner_def` turns the inner product into an integral
and `coeFn_kernelCLM` identifies the operator's value with `kernelFun` almost everywhere.

The domination the second step needs is `|sliceForm V W| ≤ Fintype.card ι * N`, since each link
contributes `|Re trace (V l * (W l)ᴴ)| ≤ N`, so the order-`k` terms are bounded by
`(b * Fintype.card ι * N) ^ k / k !` times an integrable function.
-/

/-- **THE QUADRATIC FORM IS THE DOUBLE INTEGRAL AGAINST THE KERNEL.**

`⟪T z, z⟫ = ∫ V (∫ W, K(V,W)·z(W)) · z(V)`, which is what the expansion has to be performed inside.
No analysis here — `L2.inner_def` and `coeFn_kernelCLM`, and an `integral_congr_ae` to move between
the operator's value and the kernel action.

DERIVED: the one numeral is `2`, the `Lᵖ` exponent the operator acts on. -/
theorem inner_transferCLM_eq_double_integral (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ) (Cs : ℝ)
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs)
    (z : MeasureTheory.Lp ℝ 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) :
    (inner ℝ (MassGap.SliceTransferSelfAdjoint.transferCLM b s Cs hs hsb z) z : ℝ)
      = ∫ V, (MassGap.SlabKernelOperator.kernelFun
            (MassGap.SliceTransfer.transferKernel b s)
            (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) (z : _ → ℝ) V)
          * (z : _ → ℝ) V ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) := by
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MassGap.SlabKernelOperator.coeFn_kernelCLM
    (MassGap.SliceTransfer.transferKernel b s)
    (MassGap.SliceTransferSelfAdjoint.transferCap ι N b Cs)
    (MassGap.SliceTransferSelfAdjoint.measurable_transferKernel_uncurry b s hs)
    (le_of_lt (MassGap.SliceTransferSelfAdjoint.transferCap_pos b Cs))
    (MassGap.SliceTransferSelfAdjoint.abs_transferKernel_le b s Cs hsb)
    (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)
    (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) z] with V hV
  -- `transferCLM` IS `kernelCLM` by definition, so the hypothesis retypes by defeq; `rw` alone
  -- cannot see that, being syntactic.
  have hV' : ((MassGap.SliceTransferSelfAdjoint.transferCLM b s Cs hs hsb z :
        MeasureTheory.Lp ℝ 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) : _ → ℝ) V
      = MassGap.SlabKernelOperator.kernelFun (MassGap.SliceTransfer.transferKernel b s)
          (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) (z : _ → ℝ) V := hV
  rw [RCLike.inner_apply, hV']
  simp [mul_comm]

#print axioms inner_transferCLM_eq_double_integral

/-! ## 10. A separable double integral is a square

`gram_pow` writes the order-`k` part of the kernel as `∑_α gmono α V · gmono α W` — a sum of terms
each SEPARATING the two variables. Under the double integral a separated term factors, and because
the two factors are the same function it factors into a SQUARE. That is where the sum of squares in
the finite argument comes from, and it is what makes the integral version give nonnegative orders
too.

No Fubini is needed for this: the integral is ITERATED, and the inner one has `F V` as a constant.
Fubini would be needed to exchange the ORDER of integration, which nothing here does.

`abs_sliceForm_le` — already in `SliceTransferSelfAdjoint` — is the sharp form of the domination the
series interchange needs: `|sliceForm V W| ≤ |ι|·N`, so the order-`k` terms are bounded by
`(b|ι|N)^k/k!`, summing to `e^{b|ι|N}`. §11 performs that interchange; it runs on the cruder
coordinate bound `|coord| ≤ 1` instead, because only convergence is used and both converge.
-/

/-- **A SEPARABLE DOUBLE INTEGRAL OF A FUNCTION WITH ITSELF IS A SQUARE.**

`∫∫ F(V)·F(W) = (∫F)²`, by pulling `F V` out of the inner integral and the resulting constant out of
the outer one. Unconditional: where `F` is not integrable both sides are zero, which is the Bochner
convention and is why no integrability hypothesis appears.

DERIVED: the one numeral is the exponent `2`, which is what pairing `F` with itself produces. -/
theorem integral_integral_mul_self {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (F : X → ℝ) :
    (∫ V, (∫ W, F V * F W ∂μ) ∂μ) = (∫ V, F V ∂μ) ^ 2 := by
  have hinner : ∀ V, (∫ W, F V * F W ∂μ) = F V * ∫ W, F W ∂μ :=
    fun V => MeasureTheory.integral_const_mul _ _
  simp only [hinner]
  rw [MeasureTheory.integral_mul_const]
  ring

#print axioms integral_integral_mul_self

/-- **AND THE ORDER-`k` PART OF THE KERNEL SEPARATES INTO SUCH TERMS.**

`gram_pow` at the slice: the `k`-th power of the cross form is `∑_α gmono α V · gmono α W`, so the
order-`k` contribution to the quadratic form is `∑_α (∫ gmono α · f · z)²` once
`integral_integral_mul_self` is applied termwise. Stated on the integrand so the shape is explicit
before any integral is taken.

DERIVED: no numeral occurs in the statement; `k` is the order. -/
theorem sliceForm_pow_separates (k : ℕ) (V W : ι → MassGap.SUN.SU N) :
    (sliceForm V W) ^ k
      = ∑ α : Fin k → ι × Coord N,
          gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
            coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α V
          * gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
            coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α W := by
  rw [sliceForm_eq_gram V W]
  exact gram_pow (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
    coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) k V W

#print axioms sliceForm_pow_separates

/-- **THE DOMINATION FOR THE SERIES INTERCHANGE, in the form it will be used.**

`|sliceForm V W|^k ≤ (|ι|·N)^k`, so the order-`k` term of `e^{b·sliceForm}` is bounded by
`(b|ι|N)^k/k!` uniformly in both arguments — a summable bound independent of the configurations,
which is what dominated convergence needs. `SliceTransferSelfAdjoint.abs_sliceForm_le` is the input.

DERIVED: no numeral occurs in the statement; the bound is the link count times the matrix size, raised to the order `k`. -/
theorem abs_sliceForm_pow_le (k : ℕ) (V W : ι → MassGap.SUN.SU N) :
    |sliceForm V W| ^ k ≤ ((Fintype.card ι : ℝ) * (N : ℝ)) ^ k :=
  pow_le_pow_left₀ (abs_nonneg _)
    (MassGap.SliceTransferSelfAdjoint.abs_sliceForm_le V W) k

#print axioms abs_sliceForm_pow_le

/-! ## 11. The series interchange

`MeasureTheory.integral_tsum_of_summable_integral_norm` is Mathlib's statement that a series may be
moved out of a Bochner integral when the integrals of the NORMS are summable. That is the one
hypothesis to discharge, and the domination of §10 discharges it: the order-`k` term is
`(G^k/k!)·f` with `|G| ≤ M`, so its norm integral is at most `(M^k/k!)·‖f‖₁`, and
`Real.summable_pow_div_factorial` sums that to `e^M·‖f‖₁`.

**Nothing about the kernel enters here.** The statement is about ANY bounded exponent against ANY
integrable function, and it is deliberately stated that way because the expansion has to be performed
TWICE — once inside the inner integral over `W` at each fixed `V`, and once in the outer integral
over `V`. One lemma serves both.

The exponential series itself is not re-proved: `CharacterExpansion.hasSum_exp_div` already has it,
and it is the same series the strong-coupling expansion runs on.
-/

/-- **THE EXPONENTIAL SERIES PASSES THROUGH AN INTEGRAL when the exponent is bounded.**

`∫ e^G·f = ∑ₖ ∫ (G^k/k!)·f`, for `|G| ≤ M` and `f` integrable. No finiteness is asked of the measure
and no boundedness of `f`: the bound on the exponent alone carries the domination, because it makes
the order-`k` coefficient a CONSTANT multiple of `f`.

**No sign is asked of `M`.** One might expect `0 ≤ M`, and at a nonempty space `|G x| ≤ M` gives it —
but the proof never uses it: `pow_le_pow_left₀` wants `0 ≤ |G x|`, which is free, and
`Real.summable_pow_div_factorial` holds at every real. The hypothesis would have been decoration.

DERIVED: no numeral of this tree's — `M` is the caller's bound and `k !` the series' own. -/
theorem integral_exp_mul_eq_tsum {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {G : X → ℝ} {M : ℝ}
    (hGm : MeasureTheory.AEStronglyMeasurable G μ) (hGM : ∀ x, |G x| ≤ M)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) :
    (∫ x, Real.exp (G x) * f x ∂μ)
      = ∑' k : ℕ, ∫ x, (G x) ^ k / (Nat.factorial k : ℝ) * f x ∂μ := by
  have hfac : ∀ k : ℕ, (0 : ℝ) < (Nat.factorial k : ℝ) := by
    intro k
    exact_mod_cast Nat.factorial_pos k
  -- the order-`k` coefficient is bounded UNIFORMLY in `x`, which is the whole of the domination
  have hpow : ∀ k : ℕ, ∀ x, ‖(G x) ^ k / (Nat.factorial k : ℝ)‖
      ≤ M ^ k / (Nat.factorial k : ℝ) := by
    intro k x
    have h1 : |G x| ^ k ≤ M ^ k := pow_le_pow_left₀ (abs_nonneg _) (hGM x) k
    have hfabs : |(Nat.factorial k : ℝ)| = (Nat.factorial k : ℝ) :=
      abs_of_nonneg (hfac k).le
    rw [Real.norm_eq_abs, abs_div, abs_pow, hfabs, div_le_div_iff₀ (hfac k) (hfac k)]
    exact mul_le_mul_of_nonneg_right h1 (hfac k).le
  have hFm : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun x => (G x) ^ k / (Nat.factorial k : ℝ)) μ := by
    intro k
    have hcont : Continuous (fun t : ℝ => t ^ k / (Nat.factorial k : ℝ)) :=
      (continuous_pow k).div_const _
    exact hcont.comp_aestronglyMeasurable hGm
  have hFint : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => (G x) ^ k / (Nat.factorial k : ℝ) * f x) μ :=
    fun k => hf.bdd_mul (hFm k) (Filter.Eventually.of_forall (hpow k))
  have hnormint : ∀ k : ℕ,
      (∫ x, ‖(G x) ^ k / (Nat.factorial k : ℝ) * f x‖ ∂μ)
        ≤ M ^ k / (Nat.factorial k : ℝ) * ∫ x, ‖f x‖ ∂μ := by
    intro k
    have hle : ∀ x, ‖(G x) ^ k / (Nat.factorial k : ℝ) * f x‖
        ≤ M ^ k / (Nat.factorial k : ℝ) * ‖f x‖ := by
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hpow k x) (norm_nonneg _)
    calc (∫ x, ‖(G x) ^ k / (Nat.factorial k : ℝ) * f x‖ ∂μ)
        ≤ ∫ x, M ^ k / (Nat.factorial k : ℝ) * ‖f x‖ ∂μ :=
          MeasureTheory.integral_mono (hFint k).norm (hf.norm.const_mul _) hle
      _ = M ^ k / (Nat.factorial k : ℝ) * ∫ x, ‖f x‖ ∂μ :=
          MeasureTheory.integral_const_mul _ _
  have hsum : Summable fun k : ℕ =>
      ∫ x, ‖(G x) ^ k / (Nat.factorial k : ℝ) * f x‖ ∂μ :=
    Summable.of_nonneg_of_le
      (fun _ => MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)) hnormint
      ((Real.summable_pow_div_factorial M).mul_right _)
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsum]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show Real.exp (G x) * f x = ∑' k : ℕ, (G x) ^ k / (Nat.factorial k : ℝ) * f x
  rw [tsum_mul_right, (MassGap.CharacterExpansion.hasSum_exp_div (G x)).tsum_eq]

#print axioms integral_exp_mul_eq_tsum

/-! ## 12. The integral Gram expansion

§10 separated the order-`k` kernel and §11 moved the series out of an integral. This section puts
them together at finite order, and the result is the INTEGRAL analogue of
`gram_quadform_pow_eq_sum_sq`:

    ∫∫ (∑ₚ φₚ(V)·φₚ(W))^k · f(W) · f(V)  =  ∑_α (∫ gmono φ α · f)²

a sum of SQUARES, hence nonnegative, and with no positivity hypothesis anywhere. The finite argument
summed over a finite configuration set; this one integrates against a measure, and what replaces
`Finset.sum_comm` is `integral_finsetSum` — the sum over `α` is FINITE, so no second interchange is
needed at this order.

**Why the COORDINATES are asked to be bounded rather than the Gram form.** One hypothesis does both
jobs: `|φ| ≤ B` gives `|gmono φ α| ≤ B^k`, which is what makes each coefficient's integral converge,
AND `|∑ₚ φₚ(V)φₚ(W)| ≤ |P|·B²`, which is the domination §11 consumes. Assuming the Gram bound
instead would give the second and not the first.

Everything is stated for an arbitrary coordinate family, as `gram_pow` and `gram_exp_kernel_nonneg`
already are. The slice is one instance of it.
-/

/-- **A MONOMIAL IS BOUNDED BY `B^k`** when every coordinate is bounded by `B`.

DERIVED: the exponent is the monomial's own degree; no numeral is chosen here. -/
theorem abs_gmono_le {P X : Type*} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) {k : ℕ} (α : Fin k → P) (x : X) :
    |gmono φ α x| ≤ B ^ k := by
  unfold gmono
  rw [Finset.abs_prod]
  calc (∏ t, |φ (α t) x|) ≤ ∏ _t : Fin k, B :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => hφ _ _)
    _ = B ^ k := by simp

#print axioms abs_gmono_le

/-- **AND THE GRAM FORM ITSELF BY `|P|·B²`** — the domination `integral_exp_mul_eq_tsum` consumes.

`0 ≤ B` is not assumed: it is available inside the sum, where a `p` is in hand and `hφ p x` supplies
it. Outside the sum there need be no `p` at all, and then both sides are `0`.

DERIVED: `2` is the exponent on the coordinate bound `B`, since each term of the Gram form is a product of two coordinates; `Fintype.card P` is the number of terms. -/
theorem abs_gram_le {P : Type*} [Fintype P] {X : Type*} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (x y : X) :
    |∑ p, φ p x * φ p y| ≤ (Fintype.card P : ℝ) * B ^ 2 := by
  have h1 : ∀ p : P, |φ p x * φ p y| ≤ B ^ 2 := by
    intro p
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hφ p x)
    rw [abs_mul, sq]
    exact mul_le_mul (hφ p x) (hφ p y) (abs_nonneg _) hB
  calc |∑ p, φ p x * φ p y| ≤ ∑ p, |φ p x * φ p y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : P, B ^ 2 := Finset.sum_le_sum (fun p _ => h1 p)
    _ = (Fintype.card P : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

#print axioms abs_gram_le

/-- A monomial is measurable as soon as the coordinates are.

DERIVED: no numeral occurs in the statement. -/
theorem aestronglyMeasurable_gmono {P X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ}
    (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ) {k : ℕ} (α : Fin k → P) :
    MeasureTheory.AEStronglyMeasurable (gmono φ α) μ := by
  unfold gmono
  exact Finset.aestronglyMeasurable_fun_prod _ (fun _ _ => hφm _)

#print axioms aestronglyMeasurable_gmono

/-- **THE COEFFICIENT THE EXPANSION PRODUCES**, one per monomial: `∫ gmono φ α · f`.

This is the object the whole injectivity argument turns on. `⟪T z, z⟫` will be a nonnegative
combination of its SQUARES, so the form vanishing forces every one of these to vanish — and a
function orthogonal to every monomial is orthogonal to their closed span.

DERIVED: no numeral occurs. -/
noncomputable def gramCoeff {P X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (φ : P → X → ℝ) (f : X → ℝ) {k : ℕ} (α : Fin k → P) : ℝ :=
  ∫ x, gmono φ α x * f x ∂μ

#print axioms gramCoeff

/-- and it is a genuine number: a bounded measurable factor against an integrable one.

DERIVED: no numeral occurs in the statement. -/
theorem integrable_gmono_mul {P X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) {k : ℕ} (α : Fin k → P) :
    MeasureTheory.Integrable (fun x => gmono φ α x * f x) μ :=
  hf.bdd_mul (aestronglyMeasurable_gmono hφm α)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_gmono_le hφ α x))

#print axioms integrable_gmono_mul

/-- **THE INNER INTEGRAL AT ORDER `k` IS A FINITE COMBINATION OF THE COEFFICIENTS.**

`∫ (∑ₚ φₚ(V)φₚ(W))^k f(W) dW = ∑_α gmono φ α V · c_α`. The point is that the dependence on `V` is
now through the monomials alone — finitely many CONTINUOUS functions — so the outer integral needs no
parametric-integral measurability. That is what makes the second expansion cheap.

DERIVED: no numeral occurs in the statement; `k` is the order. -/
theorem integral_gram_pow_mul_eq_sum {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) (k : ℕ) (V : X) :
    (∫ W, (∑ p, φ p V * φ p W) ^ k * f W ∂μ)
      = ∑ α : Fin k → P, gmono φ α V * gramCoeff μ φ f α := by
  unfold gramCoeff
  have hexp : ∀ W, (∑ p, φ p V * φ p W) ^ k * f W
      = ∑ α : Fin k → P, gmono φ α V * (gmono φ α W * f W) := by
    intro W
    rw [gram_pow φ k V W, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [hexp]
  rw [MeasureTheory.integral_finsetSum _
    (fun α _ => (integrable_gmono_mul hφ hφm hf α).const_mul _)]
  exact Finset.sum_congr rfl (fun _ _ => MeasureTheory.integral_const_mul _ _)

#print axioms integral_gram_pow_mul_eq_sum

/-- **AND THE ORDER-`k` DOUBLE INTEGRAL IS A SUM OF SQUARES.**

The integral analogue of `gram_quadform_pow_eq_sum_sq`, and the reason every order of the expansion
is nonnegative. No hypothesis on the sign of anything: squares are squares.

DERIVED: the one numeral is the exponent `2`, which is what `integral_integral_mul_self` produces from a separable term. -/
theorem integral_integral_gram_pow {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) (k : ℕ) :
    (∫ V, (∫ W, (∑ p, φ p V * φ p W) ^ k * f W ∂μ) * f V ∂μ)
      = ∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2 := by
  have h1 : ∀ V, (∫ W, (∑ p, φ p V * φ p W) ^ k * f W ∂μ) * f V
      = ∑ α : Fin k → P, gramCoeff μ φ f α * (gmono φ α V * f V) := by
    intro V
    rw [integral_gram_pow_mul_eq_sum hφ hφm hf k V, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [h1]
  rw [MeasureTheory.integral_finsetSum _
    (fun α _ => (integrable_gmono_mul hφ hφm hf α).const_mul _)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  unfold gramCoeff
  rw [MeasureTheory.integral_const_mul, sq]

#print axioms integral_integral_gram_pow

/-! ## 13. The expansion, in full

Putting §11 and §12 together:

    ∫∫ e^{b·⟨φ(V),φ(W)⟩} f(W) f(V)  =  ∑ₖ (bᵏ/k!) · ∑_α (∫ gmono φ α · f)²

which is `gram_exp_kernel_nonneg` with the finite configuration sum replaced by an integral. The two
expansions are NOT symmetrical in effort. The inner one is §11 applied at each fixed `V`. The outer
one cannot be, because the outer integrand is not an exponential of `V` — so it goes through
`integral_tsum_of_summable_integral_norm` directly, and what makes that cheap is §12's observation
that the inner integral depends on `V` only through finitely many monomials.

**What it buys.** Every order is a sum of squares and every coefficient `bᵏ/k!` is positive for
`b > 0`, so the form is nonnegative, and it VANISHES only if every coefficient `∫ gmono φ α · f`
does. That is the integral statement `gram_exp_kernel_eq_zero_coeffs` was the finite version of, and
it is the third of the three things `ker T = 0` needs.
-/

/-- One row of the Gram form, as a function of the second argument.

DERIVED: no numeral occurs in the statement. -/
theorem aestronglyMeasurable_gramRow {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ}
    (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ) (V : X) :
    MeasureTheory.AEStronglyMeasurable (fun W => ∑ p, φ p V * φ p W) μ :=
  Finset.aestronglyMeasurable_fun_sum _ (fun p _ => (hφm p).const_mul _)

#print axioms aestronglyMeasurable_gramRow

/-- **THE INNER INTEGRAL AT ORDER `k`**, named so the outer expansion has something to talk about.

DERIVED: no numeral occurs. -/
noncomputable def gramInner {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (φ : P → X → ℝ) (f : X → ℝ) (k : ℕ) (V : X) : ℝ :=
  ∫ W, (∑ p, φ p V * φ p W) ^ k * f W ∂μ

#print axioms gramInner

/-- It is bounded UNIFORMLY in `V`, by `(|P|B²)^k · ‖f‖₁` — the domination the outer expansion needs.

Note where this differs from §11's: there the bound was on the integrand, here on an integral, and it
is the `L¹` norm of `f` rather than `f` itself that appears. That is why no boundedness of `f` is
ever required.

DERIVED: the one numeral is the exponent `2` on the coordinate bound `B`, inherited from `abs_gram_le`; the order `k` and the link-coordinate count are the caller's. -/
theorem abs_gramInner_le {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) (k : ℕ) (V : X) :
    |gramInner μ φ f k V|
      ≤ ((Fintype.card P : ℝ) * B ^ 2) ^ k * ∫ x, ‖f x‖ ∂μ := by
  have hle : ∀ W, ‖(∑ p, φ p V * φ p W) ^ k * f W‖
      ≤ ((Fintype.card P : ℝ) * B ^ 2) ^ k * ‖f W‖ := by
    intro W
    rw [norm_mul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (abs_gram_le hφ V W) k) (norm_nonneg _)
  have hpowm : MeasureTheory.AEStronglyMeasurable
      (fun W => (∑ p, φ p V * φ p W) ^ k) μ :=
    (aestronglyMeasurable_gramRow hφm V).pow k
  have hint : MeasureTheory.Integrable
      (fun W => (∑ p, φ p V * φ p W) ^ k * f W) μ :=
    hf.bdd_mul hpowm (Filter.Eventually.of_forall (fun W => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_gram_le hφ V W) k))
  unfold gramInner
  calc |∫ W, (∑ p, φ p V * φ p W) ^ k * f W ∂μ|
      ≤ ∫ W, ‖(∑ p, φ p V * φ p W) ^ k * f W‖ ∂μ := by
        rw [← Real.norm_eq_abs]
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ W, ((Fintype.card P : ℝ) * B ^ 2) ^ k * ‖f W‖ ∂μ :=
        MeasureTheory.integral_mono hint.norm (hf.norm.const_mul _) hle
    _ = ((Fintype.card P : ℝ) * B ^ 2) ^ k * ∫ x, ‖f x‖ ∂μ :=
        MeasureTheory.integral_const_mul _ _

#print axioms abs_gramInner_le

/-- and it is measurable in `V`, because §12 wrote it as a FINITE sum of monomials.

DERIVED: no numeral occurs in the statement. -/
theorem aestronglyMeasurable_gramInner {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) (k : ℕ) :
    MeasureTheory.AEStronglyMeasurable (gramInner μ φ f k) μ := by
  have hrep : gramInner μ φ f k
      = fun V => ∑ α : Fin k → P, gmono φ α V * gramCoeff μ φ f α := by
    funext V
    exact integral_gram_pow_mul_eq_sum hφ hφm hf k V
  rw [hrep]
  exact Finset.aestronglyMeasurable_fun_sum _
    (fun α _ => (aestronglyMeasurable_gmono hφm α).mul_const _)

#print axioms aestronglyMeasurable_gramInner

/-- **THE EXPONENTIAL GRAM QUADRATIC FORM, EXPANDED.**

`∫∫ e^{b⟨φ(V),φ(W)⟩} f(W) f(V) = ∑ₖ (bᵏ/k!) ∑_α (∫ gmono φ α · f)²`. The integral analogue of
`gram_exp_kernel_nonneg`, and strictly more than it: this is an EQUALITY, so it gives the vanishing
case as well as the sign.

DERIVED: no numeral. `b` is the caller's coupling, `k !` the exponential series' own, and the `2` is
a square. -/
theorem integral_integral_exp_gram_eq_tsum {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) (b : ℝ) :
    (∫ V, (∫ W, Real.exp (b * ∑ p, φ p V * φ p W) * f W ∂μ) * f V ∂μ)
      = ∑' k : ℕ, b ^ k / (Nat.factorial k : ℝ)
          * ∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2 := by
  have hfac : ∀ k : ℕ, (0 : ℝ) < (Nat.factorial k : ℝ) := by
    intro k
    exact_mod_cast Nat.factorial_pos k
  set M : ℝ := (Fintype.card P : ℝ) * B ^ 2 with hM
  set L : ℝ := ∫ x, ‖f x‖ ∂μ with hL
  have hL0 : 0 ≤ L := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  -- the coefficient's absolute value, once
  have habs : ∀ k : ℕ, |b ^ k / (Nat.factorial k : ℝ)| = |b| ^ k / (Nat.factorial k : ℝ) := by
    intro k
    rw [abs_div, abs_pow, abs_of_nonneg (hfac k).le]
  -- STEP 1 — the inner expansion, at each fixed `V`
  have hinner : ∀ V, (∫ W, Real.exp (b * ∑ p, φ p V * φ p W) * f W ∂μ)
      = ∑' k : ℕ, b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V := by
    intro V
    have hGm : MeasureTheory.AEStronglyMeasurable
        (fun W => b * ∑ p, φ p V * φ p W) μ :=
      (aestronglyMeasurable_gramRow hφm V).const_mul b
    have hGM : ∀ W, |b * ∑ p, φ p V * φ p W| ≤ |b| * M := by
      intro W
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_gram_le hφ V W) (abs_nonneg b)
    rw [integral_exp_mul_eq_tsum hGm hGM hf]
    refine tsum_congr (fun k => ?_)
    unfold gramInner
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
    show (b * ∑ p, φ p V * φ p W) ^ k / (Nat.factorial k : ℝ) * f W
        = b ^ k / (Nat.factorial k : ℝ) * ((∑ p, φ p V * φ p W) ^ k * f W)
    rw [mul_pow]
    ring
  -- STEP 2 — the outer expansion, which is NOT an exponential and so goes through Mathlib directly
  have hbd : ∀ (k : ℕ) (V : X),
      ‖b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V‖
        ≤ |b| ^ k / (Nat.factorial k : ℝ) * (M ^ k * L) := by
    intro k V
    rw [Real.norm_eq_abs, abs_mul, habs k]
    refine mul_le_mul_of_nonneg_left (abs_gramInner_le hφ hφm hf k V) ?_
    positivity
  have hFint : ∀ k : ℕ, MeasureTheory.Integrable
      (fun V => b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V) μ :=
    fun k => hf.bdd_mul ((aestronglyMeasurable_gramInner hφ hφm hf k).const_mul _)
      (Filter.Eventually.of_forall (hbd k))
  have hnormint : ∀ k : ℕ,
      (∫ V, ‖b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V‖ ∂μ)
        ≤ (|b| * M) ^ k / (Nat.factorial k : ℝ) * (L * L) := by
    intro k
    have hle : ∀ V, ‖b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V‖
        ≤ (|b| * M) ^ k / (Nat.factorial k : ℝ) * L * ‖f V‖ := by
      intro V
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := hbd k V
      calc ‖b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V‖
          ≤ |b| ^ k / (Nat.factorial k : ℝ) * (M ^ k * L) := this
        _ = (|b| * M) ^ k / (Nat.factorial k : ℝ) * L := by
            rw [mul_pow]
            field_simp
            ring
    calc (∫ V, ‖b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V‖ ∂μ)
        ≤ ∫ V, (|b| * M) ^ k / (Nat.factorial k : ℝ) * L * ‖f V‖ ∂μ :=
          MeasureTheory.integral_mono (hFint k).norm (hf.norm.const_mul _) hle
      _ = (|b| * M) ^ k / (Nat.factorial k : ℝ) * L * L :=
          MeasureTheory.integral_const_mul _ _
      _ = (|b| * M) ^ k / (Nat.factorial k : ℝ) * (L * L) := by ring
  have hsum : Summable fun k : ℕ =>
      ∫ V, ‖b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V‖ ∂μ :=
    Summable.of_nonneg_of_le
      (fun _ => MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)) hnormint
      ((Real.summable_pow_div_factorial (|b| * M)).mul_right _)
  -- STEP 3 — assemble
  have hstep : (∫ V, (∫ W, Real.exp (b * ∑ p, φ p V * φ p W) * f W ∂μ) * f V ∂μ)
      = ∫ V, ∑' k : ℕ, b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun V => ?_))
    show (∫ W, Real.exp (b * ∑ p, φ p V * φ p W) * f W ∂μ) * f V
        = ∑' k : ℕ, b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V
    rw [hinner V, tsum_mul_right]
  rw [hstep, ← MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsum]
  refine tsum_congr (fun k => ?_)
  have hshape : (fun V => b ^ k / (Nat.factorial k : ℝ) * gramInner μ φ f k V * f V)
      = fun V => b ^ k / (Nat.factorial k : ℝ) * (gramInner μ φ f k V * f V) := by
    funext V
    ring
  rw [hshape, MeasureTheory.integral_const_mul]
  unfold gramInner
  rw [integral_integral_gram_pow hφ hφm hf k]

#print axioms integral_integral_exp_gram_eq_tsum

/-! ## 14. Nonnegativity, and the vanishing case

The expansion is an equality, so it gives both halves at once. Nonnegativity is immediate — every
order is a sum of squares with a positive coefficient. The vanishing case needs one more thing,
SUMMABILITY, because `∑'` of a non-summable family is `0` by convention and a `0` that means
"undefined" forces nothing. So the orders are bounded first: order `k` is at most `(bM)^k/k!·‖f‖₁²`,
which sums.

With that, `Summable.le_tsum` puts each order below the total, the total is `0` and each order is
nonnegative, so every order is `0` — and an order is a positive multiple of a sum of SQUARES.

This is `gram_exp_kernel_eq_zero_coeffs` for an integral rather than a finite configuration set, and
it is the last of the three things `ker T = 0` needs.
-/

/-- **THE ORDERS ARE BOUNDED**, which is what makes the series summable rather than merely formal.

DERIVED: `2` is the square on each coefficient and the exponent on the coordinate bound `B` inherited from `abs_gram_le`. -/
theorem sum_sq_gramCoeff_le {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) (k : ℕ) :
    (∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2)
      ≤ ((Fintype.card P : ℝ) * B ^ 2) ^ k * ((∫ x, ‖f x‖ ∂μ) * ∫ x, ‖f x‖ ∂μ) := by
  have hL0 : (0 : ℝ) ≤ ∫ x, ‖f x‖ ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have hint : MeasureTheory.Integrable (fun V => gramInner μ φ f k V * f V) μ :=
    hf.bdd_mul (aestronglyMeasurable_gramInner hφ hφm hf k)
      (Filter.Eventually.of_forall (fun V => by
        rw [Real.norm_eq_abs]
        exact abs_gramInner_le hφ hφm hf k V))
  have hle : ∀ V, ‖gramInner μ φ f k V * f V‖
      ≤ ((Fintype.card P : ℝ) * B ^ 2) ^ k * (∫ x, ‖f x‖ ∂μ) * ‖f V‖ := by
    intro V
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_gramInner_le hφ hφm hf k V) (norm_nonneg _)
  have hrw : (∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2)
      = ∫ V, gramInner μ φ f k V * f V ∂μ :=
    (integral_integral_gram_pow hφ hφm hf k).symm
  rw [hrw]
  calc (∫ V, gramInner μ φ f k V * f V ∂μ)
      ≤ |∫ V, gramInner μ φ f k V * f V ∂μ| := le_abs_self _
    _ ≤ ∫ V, ‖gramInner μ φ f k V * f V‖ ∂μ := by
        rw [← Real.norm_eq_abs]
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ V, ((Fintype.card P : ℝ) * B ^ 2) ^ k * (∫ x, ‖f x‖ ∂μ) * ‖f V‖ ∂μ :=
        MeasureTheory.integral_mono hint.norm (hf.norm.const_mul _) hle
    _ = ((Fintype.card P : ℝ) * B ^ 2) ^ k * (∫ x, ‖f x‖ ∂μ) * ∫ x, ‖f x‖ ∂μ :=
        MeasureTheory.integral_const_mul _ _
    _ = ((Fintype.card P : ℝ) * B ^ 2) ^ k * ((∫ x, ‖f x‖ ∂μ) * ∫ x, ‖f x‖ ∂μ) := by ring

#print axioms sum_sq_gramCoeff_le

/-- **SO THE SERIES CONVERGES.** Without this the vanishing case proves nothing: `∑'` of a
non-summable family is `0` by convention, and that `0` would carry no information.

DERIVED: `0` is the lower bound on `b`, which is what makes the orders nonnegative; `2` is the square on each coefficient. -/
theorem summable_gram_orders {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) {b : ℝ} (hb : 0 ≤ b) :
    Summable fun k : ℕ => b ^ k / (Nat.factorial k : ℝ)
      * ∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2 := by
  have hfac : ∀ k : ℕ, (0 : ℝ) < (Nat.factorial k : ℝ) := by
    intro k
    exact_mod_cast Nat.factorial_pos k
  set M : ℝ := (Fintype.card P : ℝ) * B ^ 2 with hM
  set L : ℝ := ∫ x, ‖f x‖ ∂μ with hL
  have hL0 : (0 : ℝ) ≤ L := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((Real.summable_pow_div_factorial (b * M)).mul_right (L * L))
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · have hbound := sum_sq_gramCoeff_le hφ hφm hf (B := B) k
    have hcoef : (0 : ℝ) ≤ b ^ k / (Nat.factorial k : ℝ) := by positivity
    calc b ^ k / (Nat.factorial k : ℝ) * ∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2
        ≤ b ^ k / (Nat.factorial k : ℝ) * (M ^ k * (L * L)) :=
          mul_le_mul_of_nonneg_left hbound hcoef
      _ = (b * M) ^ k / (Nat.factorial k : ℝ) * (L * L) := by
          rw [mul_pow]
          field_simp
          ring

#print axioms summable_gram_orders

/-- **THE FORM IS NONNEGATIVE** — the integral `gram_exp_kernel_nonneg`, now a corollary rather than
an argument of its own.

DERIVED: `0` is the lower bound on `b` and the lower bound asserted on the form. -/
theorem integral_integral_exp_gram_nonneg {P : Type*} [Fintype P] {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ ∫ V, (∫ W, Real.exp (b * ∑ p, φ p V * φ p W) * f W ∂μ) * f V ∂μ := by
  rw [integral_integral_exp_gram_eq_tsum hφ hφm hf b]
  refine tsum_nonneg (fun k => ?_)
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

#print axioms integral_integral_exp_gram_nonneg

/-- **AND IT VANISHES ONLY IF EVERY COEFFICIENT DOES.**

`⟪T f, f⟫ = 0 → ∫ gmono φ α · f = 0` at every monomial. The strict positivity of `b` is what makes
every order carry weight; at `b = 0` the kernel is the constant `1` and only the order-zero
coefficient is seen, which is exactly `gram_exp_kernel_eq_zero_coeffs`' own hypothesis.

DERIVED: `0` is the strict lower bound on `b`, the value of the vanishing quadratic form, and the value of the coefficient concluded. -/
theorem gramCoeff_eq_zero_of_quadform_eq_zero {P : Type*} [Fintype P] {X : Type*}
    [MeasurableSpace X] {μ : MeasureTheory.Measure X} {φ : P → X → ℝ} {B : ℝ}
    (hφ : ∀ p x, |φ p x| ≤ B) (hφm : ∀ p, MeasureTheory.AEStronglyMeasurable (φ p) μ)
    {f : X → ℝ} (hf : MeasureTheory.Integrable f μ) {b : ℝ} (hb : 0 < b)
    (h0 : (∫ V, (∫ W, Real.exp (b * ∑ p, φ p V * φ p W) * f W ∂μ) * f V ∂μ) = 0)
    {k : ℕ} (α : Fin k → P) :
    gramCoeff μ φ f α = 0 := by
  rw [integral_integral_exp_gram_eq_tsum hφ hφm hf b] at h0
  have hnn : ∀ j : ℕ, 0 ≤ b ^ j / (Nat.factorial j : ℝ)
      * ∑ α : Fin j → P, (gramCoeff μ φ f α) ^ 2 := by
    intro j
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hle := (summable_gram_orders hφ hφm hf hb.le).le_tsum k (fun j _ => hnn j)
  rw [h0] at hle
  have hterm : b ^ k / (Nat.factorial k : ℝ)
      * ∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2 = 0 := le_antisymm hle (hnn k)
  have hpos : (0 : ℝ) < b ^ k / (Nat.factorial k : ℝ) := by positivity
  have hs : ∑ α : Fin k → P, (gramCoeff μ φ f α) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ => sq_nonneg (gramCoeff μ φ f α))).mp hs α (Finset.mem_univ α)
  exact sq_eq_zero_iff.mp hzero

#print axioms gramCoeff_eq_zero_of_quadform_eq_zero

/-! ## 15. At the slice

The general theorem asks for two things of the coordinate family: a uniform bound and measurability.
The slice supplies both outright — `|coord| ≤ 1` because an `SU(N)` entry has modulus at most one,
and continuity from §7 — so `B = 1` and the domination constant is `|ι × Coord N| = |ι|·2N²`.

That constant is CRUDER than the `|ι|·N` of `abs_sliceForm_le`, by a factor `2N`. It costs nothing:
the series converges either way, and only convergence is used. The sharper bound stays in §10 as the
statement of what the form actually satisfies.
-/

/-- **EVERY SLICE COORDINATE IS BOUNDED BY ONE.** An `SU(N)` matrix is unitary, so each entry has
modulus at most one, so each real or imaginary part does.

DERIVED: `1` is the unitary entry bound (`SUN.unitary_entry_norm_le_one`), not a chosen cut. -/
theorem abs_sliceCoord_le_one (q : ι × Coord N) (U : ι → MassGap.SUN.SU N) :
    |coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))| ≤ 1 := by
  refine MassGap.OddLagSplit.abs_coord_le_one_of_entries (fun i j => ?_) q.2
  exact MassGap.SUN.unitary_entry_norm_le_one N
    (Matrix.mem_specialUnitaryGroup_iff.mp (U q.1).2).1 i j

#print axioms abs_sliceCoord_le_one

/-- **THE COEFFICIENT AT THE SLICE**, named so the statements below do not carry the lambda.

`sliceCoeff f α = ∫ gmono α · f` over the slice's Haar measure: the integral of `f` against one
monomial in the link coordinates.

DERIVED: no numeral occurs. -/
noncomputable def sliceCoeff (f : (ι → MassGap.SUN.SU N) → ℝ) {k : ℕ}
    (α : Fin k → ι × Coord N) : ℝ :=
  gramCoeff (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)
    (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
      coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) f α

#print axioms sliceCoeff

/-- **THE SLICE QUADRATIC FORM, EXPANDED.** `§13` at `P := ι × Coord N`, with `sliceForm_eq_gram`
turning the slice form into the Gram form the general theorem is stated over.

DERIVED: the one numeral is the square `2` on each coefficient; `k !` is the exponential series' own denominator and `b` the caller's coupling. -/
theorem slice_quadform_eq_tsum {b : ℝ} {f : (ι → MassGap.SUN.SU N) → ℝ}
    (hf : MeasureTheory.Integrable f (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) :
    (∫ V, (∫ W, Real.exp (b * sliceForm V W) * f W
          ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) * f V
        ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
      = ∑' k : ℕ, b ^ k / (Nat.factorial k : ℝ)
          * ∑ α : Fin k → ι × Coord N, (sliceCoeff f α) ^ 2 := by
  simp only [sliceForm_eq_gram]
  exact integral_integral_exp_gram_eq_tsum (B := 1)
    (fun q U => abs_sliceCoord_le_one q U)
    (fun q => (continuous_sliceCoord q).aestronglyMeasurable) hf b

#print axioms slice_quadform_eq_tsum

/-- **AND IT VANISHES ONLY IF EVERY MONOMIAL COEFFICIENT DOES.**

This is the integral `gram_exp_kernel_eq_zero_coeffs`, at the slice. Everything the rest of the
injectivity argument needs from the kernel is in this one line: a function whose quadratic form
against the slice weight vanishes is orthogonal to every monomial in the link coordinates.

DERIVED: `0` is the strict lower bound on `b`, the value of the vanishing quadratic form, and the value of the coefficient concluded. -/
theorem slice_gramCoeff_eq_zero {b : ℝ} (hb : 0 < b) {f : (ι → MassGap.SUN.SU N) → ℝ}
    (hf : MeasureTheory.Integrable f (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
    (h0 : (∫ V, (∫ W, Real.exp (b * sliceForm V W) * f W
          ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) * f V
        ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) = 0)
    {k : ℕ} (α : Fin k → ι × Coord N) :
    sliceCoeff f α = 0 := by
  simp only [sliceForm_eq_gram] at h0
  exact gramCoeff_eq_zero_of_quadform_eq_zero (B := 1)
    (fun q U => abs_sliceCoord_le_one q U)
    (fun q => (continuous_sliceCoord q).aestronglyMeasurable) hf hb h0 α

#print axioms slice_gramCoeff_eq_zero

/-! ## 16. The monomials span the coordinate algebra

§15 gives a coefficient at every MONOMIAL. §8 gives density of the ALGEBRA. They are about different
sets, and this section is the bridge: the algebra is exactly the linear span of the monomials.

The direction that needs an argument is `coordAlgebra ≤ span (monomials)`, and the way to get it is
to show the span is itself a SUBALGEBRA — then `Algebra.adjoin_le` applies, because the generators
are the degree-one monomials. Being a subalgebra needs two things of the span: it contains `1`, which
is the degree-ZERO monomial (the empty product), and it is closed under multiplication, which holds
because a product of monomials is a monomial. `Fin.prod_univ_add` with `Fin.append` is that fact.

The reverse inclusion is true and not needed: what the argument uses is that every element of the
algebra is a finite linear combination of monomials, never that every such combination is in the
algebra.
-/

/-- A monomial in the link coordinates, as a bundled continuous map.

DERIVED: no numeral occurs. -/
noncomputable def sliceMonoCM {k : ℕ} (α : Fin k → ι × Coord N) :
    C(ι → MassGap.SUN.SU N, ℝ) :=
  ∏ t, sliceCoordCM (α t)

#print axioms sliceMonoCM

/-- and its value is the `gmono` the expansion produces — the two descriptions agree pointwise.

DERIVED: no numeral occurs in the statement. -/
theorem sliceMonoCM_apply {k : ℕ} (α : Fin k → ι × Coord N) (U : ι → MassGap.SUN.SU N) :
    sliceMonoCM α U
      = gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
          coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α U := by
  unfold sliceMonoCM gmono
  rw [ContinuousMap.prod_apply]
  rfl

#print axioms sliceMonoCM_apply

/-- **A PRODUCT OF MONOMIALS IS A MONOMIAL** — concatenate the two index families.

This is the whole reason the span is an algebra, and `Fin.append` is the concatenation.

DERIVED: no numeral occurs in the statement; `Fin.append` concatenates the two index families. -/
theorem sliceMonoCM_mul {k m : ℕ} (α : Fin k → ι × Coord N) (β : Fin m → ι × Coord N) :
    sliceMonoCM α * sliceMonoCM β = sliceMonoCM (Fin.append α β) := by
  unfold sliceMonoCM
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_left])
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_right])

#print axioms sliceMonoCM_mul

/-- The set of all monomials, at every degree.

DERIVED: no numeral occurs. -/
def monoSet (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Set C(ι → MassGap.SUN.SU N, ℝ) :=
  {g | ∃ (k : ℕ) (α : Fin k → ι × Coord N), g = sliceMonoCM α}

#print axioms monoSet

/-- `1` is the degree-ZERO monomial: the empty product.

DERIVED: the one numeral is `1`, the unit of the algebra, which is the empty product of coordinates. -/
theorem one_mem_monoSet : (1 : C(ι → MassGap.SUN.SU N, ℝ)) ∈ monoSet ι N :=
  ⟨0, Fin.elim0, by simp [sliceMonoCM]⟩

#print axioms one_mem_monoSet

/-- **THE SPAN OF THE MONOMIALS IS CLOSED UNDER MULTIPLICATION.**

`Submodule.mul_mem_mul` puts the product in the submodule product, `Submodule.span_mul_span`
identifies that with the span of the setwise product, and `sliceMonoCM_mul` says the setwise product
lands back in the monomials.

DERIVED: no numeral occurs in the statement. -/
theorem mul_mem_span_monoSet {x y : C(ι → MassGap.SUN.SU N, ℝ)}
    (hx : x ∈ Submodule.span ℝ (monoSet ι N)) (hy : y ∈ Submodule.span ℝ (monoSet ι N)) :
    x * y ∈ Submodule.span ℝ (monoSet ι N) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro z hz
  rw [Set.mem_mul] at hz
  obtain ⟨a, ⟨ka, αa, rfl⟩, b, ⟨kb, αb, rfl⟩, rfl⟩ := hz
  exact Submodule.subset_span ⟨ka + kb, Fin.append αa αb, sliceMonoCM_mul αa αb⟩

#print axioms mul_mem_span_monoSet

/-- so it is a subalgebra.

DERIVED: no numeral occurs. -/
noncomputable def monoSpan (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    Subalgebra ℝ C(ι → MassGap.SUN.SU N, ℝ) :=
  (Submodule.span ℝ (monoSet ι N)).toSubalgebra
    (Submodule.subset_span one_mem_monoSet)
    (fun _ _ hx hy => mul_mem_span_monoSet hx hy)

#print axioms monoSpan

/-- **AND IT CONTAINS THE COORDINATE ALGEBRA.** `Algebra.adjoin_le`, with the generators as the
degree-ONE monomials.

DERIVED: no numeral occurs in the statement; the generators are the degree-one monomials. -/
theorem coordAlgebra_le_monoSpan : coordAlgebra ι N ≤ monoSpan ι N := by
  refine Algebra.adjoin_le ?_
  rintro g ⟨q, rfl⟩
  exact Submodule.subset_span ⟨1, fun _ => q, by simp [sliceMonoCM]⟩

#print axioms coordAlgebra_le_monoSpan

/-! ## 17. Orthogonal to every monomial means zero

The last step, and it is the JOIN rather than a new estimate. §15 gives a vanishing coefficient at
every monomial; §16 says the monomials span the algebra; §8 says the algebra is dense in `L²`. Put
together: the functional `h ↦ ⟪F, h⟫` vanishes on a dense set and is continuous, so it vanishes
everywhere — in particular at `F` itself, and `⟪F, F⟫ = 0` is `F = 0`.

Nothing here is specific to the transfer kernel. What IS specific is the hypothesis, and §15 is what
supplies it from a vanishing quadratic form.
-/

/-- A continuous function times an integrable one is integrable: the space is compact, so `‖g U‖` is
bounded by the sup norm `‖g‖` and `Integrable.bdd_mul` applies.

DERIVED: no numeral occurs in the statement. -/
theorem integrable_continuousMap_mul (g : C(ι → MassGap.SUN.SU N, ℝ))
    {f : (ι → MassGap.SUN.SU N) → ℝ}
    (hf : MeasureTheory.Integrable f (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) :
    MeasureTheory.Integrable (fun U => g U * f U)
      (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) :=
  hf.bdd_mul g.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun U => g.norm_coe_le_norm U))

#print axioms integrable_continuousMap_mul

/-- **A FUNCTION ORTHOGONAL TO EVERY MONOMIAL IS ORTHOGONAL TO THEIR SPAN.**

`Submodule.span_induction`: the base case is a monomial, where the integral IS `sliceCoeff`, and the
two closure cases are linearity of the integral. Integrability is available at every step because
every element of the span is a continuous function on a compact space.

DERIVED: `0` is the value of every monomial coefficient in the hypothesis and of the integral in the conclusion. -/
theorem integral_mul_eq_zero_of_mem_span {f : (ι → MassGap.SUN.SU N) → ℝ}
    (hf : MeasureTheory.Integrable f (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
    (hzero : ∀ (k : ℕ) (α : Fin k → ι × Coord N), sliceCoeff f α = 0)
    {g : C(ι → MassGap.SUN.SU N, ℝ)} (hg : g ∈ Submodule.span ℝ (monoSet ι N)) :
    (∫ U, g U * f U ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) = 0 := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, α, rfl⟩ := hx
      have heq : (∫ U, sliceMonoCM α U * f U
          ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) = sliceCoeff f α := by
        unfold sliceCoeff gramCoeff
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
        show sliceMonoCM α U * f U
            = gmono (fun q : ι × Coord N => fun U : ι → MassGap.SUN.SU N =>
                coord q.2 ((U q.1 : Matrix (Fin N) (Fin N) ℂ))) α U * f U
        rw [sliceMonoCM_apply]
      rw [heq, hzero k α]
  | zero => simp
  | add x y hx hy ihx ihy =>
      have hshape : ∀ U, (x + y) U * f U = x U * f U + y U * f U := by
        intro U
        rw [ContinuousMap.add_apply]
        ring
      simp only [hshape]
      rw [MeasureTheory.integral_add (integrable_continuousMap_mul x hf)
        (integrable_continuousMap_mul y hf), ihx, ihy, add_zero]
  | smul c x hx ih =>
      have hshape : ∀ U, (c • x) U * f U = c * (x U * f U) := by
        intro U
        rw [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      simp only [hshape]
      rw [MeasureTheory.integral_const_mul, ih, mul_zero]

#print axioms integral_mul_eq_zero_of_mem_span

/-- and therefore to every element of the coordinate algebra, by §16.

DERIVED: `0` is the value of every monomial coefficient in the hypothesis and of the integral in the conclusion. -/
theorem integral_mul_eq_zero_of_mem_coordAlgebra {f : (ι → MassGap.SUN.SU N) → ℝ}
    (hf : MeasureTheory.Integrable f (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
    (hzero : ∀ (k : ℕ) (α : Fin k → ι × Coord N), sliceCoeff f α = 0)
    {g : C(ι → MassGap.SUN.SU N, ℝ)} (hg : g ∈ coordAlgebra ι N) :
    (∫ U, g U * f U ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) = 0 :=
  integral_mul_eq_zero_of_mem_span hf hzero (coordAlgebra_le_monoSpan hg)

#print axioms integral_mul_eq_zero_of_mem_coordAlgebra

/-- **AND THEN IT IS ZERO IN `L²`.**

The functional `h ↦ ⟪F, h⟫` is continuous and vanishes on the image of the coordinate algebra, which
`coordAlgebra_dense_in_L2` says is dense. A continuous function agreeing with `0` on a dense set
agrees with it everywhere, so it vanishes at `F`, and `⟪F, F⟫ = 0` is `F = 0`.

DERIVED: `2` is the `Lᵖ` exponent; `0` is the value of every coefficient in the hypothesis and of the element in the conclusion. -/
theorem lp_eq_zero_of_sliceCoeff_eq_zero
    (F : MeasureTheory.Lp ℝ 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
    (hzero : ∀ (k : ℕ) (α : Fin k → ι × Coord N), sliceCoeff (F : _ → ℝ) α = 0) :
    F = 0 := by
  have hF1 : MeasureTheory.Integrable (F : _ → ℝ)
      (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) :=
    (MeasureTheory.Lp.memLp F).integrable (by norm_num)
  have hvanish : ∀ g : C(ι → MassGap.SUN.SU N, ℝ), g ∈ coordAlgebra ι N →
      (inner ℝ F (ContinuousMap.toLp (E := ℝ) 2
        (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) ℝ g) : ℝ) = 0 := by
    intro g hg
    rw [MeasureTheory.L2.inner_def]
    have hae : (∫ U, (inner ℝ ((F : _ → ℝ) U)
          ((ContinuousMap.toLp (E := ℝ) 2
            (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) ℝ g : _ → ℝ) U) : ℝ)
        ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
        = ∫ U, g U * (F : _ → ℝ) U ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (E := ℝ) (p := 2)
        (μ := MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) g] with U hU
      rw [RCLike.inner_apply, hU]
      simp [mul_comm]
    rw [hae]
    exact integral_mul_eq_zero_of_mem_coordAlgebra hF1 hzero hg
  have hclosed : IsClosed {h : MeasureTheory.Lp ℝ 2
      (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) | (inner ℝ F h : ℝ) = 0} :=
    isClosed_eq (innerSL ℝ F).continuous continuous_const
  have hsub : (ContinuousMap.toLp (E := ℝ) 2
        (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) ℝ)
      '' (coordAlgebra ι N : Set C(ι → MassGap.SUN.SU N, ℝ))
      ⊆ {h : MeasureTheory.Lp ℝ 2
        (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) | (inner ℝ F h : ℝ) = 0} := by
    rintro h ⟨g, hg, rfl⟩
    exact hvanish g hg
  have huniv : (Set.univ : Set (MeasureTheory.Lp ℝ 2
      (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)))
      ⊆ {h | (inner ℝ F h : ℝ) = 0} := by
    rw [← (coordAlgebra_dense_in_L2 (ι := ι) (N := N)).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  exact inner_self_eq_zero.mp (huniv (Set.mem_univ F))

#print axioms lp_eq_zero_of_sliceCoeff_eq_zero

/-- The same, for a raw function rather than an `Lp` element — which is the form §18 needs, because
the function the expansion runs on is `e^{-s/2}·z` and that is not an `Lp` element on the nose.

DERIVED: `2` is the `Lᵖ` exponent; `0` is the value of every coefficient in the hypothesis and the function the conclusion equates to almost everywhere. -/
theorem ae_eq_zero_of_sliceCoeff_eq_zero {f : (ι → MassGap.SUN.SU N) → ℝ}
    (hf2 : MeasureTheory.MemLp f 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
    (hzero : ∀ (k : ℕ) (α : Fin k → ι × Coord N), sliceCoeff f α = 0) :
    f =ᵐ[MassGap.SliceTransferSelfAdjoint.sliceHaar ι N] 0 := by
  have hco : ∀ (k : ℕ) (α : Fin k → ι × Coord N),
      sliceCoeff ((hf2.toLp f : _) : _ → ℝ) α = 0 := by
    intro k α
    have heq : sliceCoeff ((hf2.toLp f : _) : _ → ℝ) α = sliceCoeff f α := by
      unfold sliceCoeff gramCoeff
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp] with U hU
      show _ * ((hf2.toLp f : _) : _ → ℝ) U = _ * f U
      rw [hU]
    rw [heq, hzero k α]
  have hLp := lp_eq_zero_of_sliceCoeff_eq_zero (hf2.toLp f) hco
  have h1 : ((hf2.toLp f : _) : _ → ℝ)
      =ᵐ[MassGap.SliceTransferSelfAdjoint.sliceHaar ι N] 0 := by
    rw [hLp]
    exact MeasureTheory.Lp.coeFn_zero ℝ 2 _
  exact hf2.coeFn_toLp.symm.trans h1

#print axioms ae_eq_zero_of_sliceCoeff_eq_zero

/-! ## 18. `ker T = 0`

Everything above is about the Gaussian factor `e^{b·sliceForm}` alone. The transfer kernel carries
two more, `e^{-s(V)/2}` and `e^{-s(W)/2}`, and they are exactly what turns the quadratic form of `T`
against `z` into the quadratic form of the Gaussian factor against the WEIGHTED function
`e^{-s/2}·z`. Those factors are positive, so weighting loses nothing: the weighted function vanishes
exactly where `z` does.

That is the whole of this section. `T z = 0` gives `⟪T z, z⟫ = 0`; §9 makes that a double integral;
the two diagonal factors move onto `z`; §15 kills every coefficient; §17 kills the weighted function;
positivity of `e^{-s/2}` kills `z`.

**`transferCLM` is therefore injective, and the second of C1's three obstacles is closed.**

⚠ **What that does NOT give is `-log T`.** `ClayAssembly`'s note on `TransferMovesSomething` states
the distinction and it holds here: the logarithm needs `0 ∉ spectrum T`, which on an
infinite-dimensional space is STRICTLY stronger than `ker T = 0`. An injective operator whose inverse
is unbounded has `0` in its spectrum.

**But `-log T` is NOT an unbuilt thing in this tree.** `Reconstruction.hamiltonian` IS
`cfc (fun x => -Real.log x) T`, and `Reconstruction.reconstruct_qm_core` proves — foundational axioms
only — that from `1 ∈ spectrum T` and `spectrum T ⊆ {1} ∪ [ε, e^{−Δ}]` with `0 < ε` it is
self-adjoint, nonnegative, has its vacuum at `0` and satisfies `spectrum H ⊆ {0} ∪ [Δ, ∞)`. The
spectral hypothesis is supplied by DECAY, through `MomentSupport.le_of_positive_weight_decay`.

So `0 ∉ spectrum T` is a HYPOTHESIS OF AN EXISTING THEOREM rather than a further construction, and
what remains for C1 is the CARRIER: a `T` on `ymH` satisfying it.
-/

/-- The function the expansion actually runs on: `z` with the kernel's diagonal factor absorbed.

DERIVED: the `2` is `SliceTransfer.transferKernel`'s own — the intra-slice action is split EVENLY
between the two ends of the kernel, which is what makes it symmetric. It is carried here unchanged,
not chosen. -/
noncomputable def weighted (s z : (ι → MassGap.SUN.SU N) → ℝ)
    (V : ι → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-(s V) / 2) * z V

#print axioms weighted

/-- **THE DIAGONAL FACTORS MOVE ONTO `z`.** Pointwise in `V`, and it is `integral_const_mul` twice:
`e^{-s(V)/2}` is constant in `W` so it leaves the inner integral, and `e^{-s(W)/2}` pairs with `z W`
inside it.

DERIVED: no numeral occurs in the statement; the halving of the intra-slice action lives in `weighted` and in `transferKernel`. -/
theorem kernelFun_mul_eq_weighted (b : ℝ) (s z : (ι → MassGap.SUN.SU N) → ℝ)
    (V : ι → MassGap.SUN.SU N) :
    MassGap.SlabKernelOperator.kernelFun (transferKernel b s)
        (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) z V * z V
      = (∫ W, Real.exp (b * sliceForm V W) * weighted s z W
          ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) * weighted s z V := by
  have hin : (∫ W, transferKernel b s V W * z W
        ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
      = Real.exp (-(s V) / 2) * ∫ W, Real.exp (b * sliceForm V W) * weighted s z W
          ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
    show transferKernel b s V W * z W
        = Real.exp (-(s V) / 2) * (Real.exp (b * sliceForm V W) * weighted s z W)
    unfold transferKernel weighted
    ring
  show (∫ W, transferKernel b s V W * z W
      ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) * z V = _
  rw [hin]
  unfold weighted
  ring

#print axioms kernelFun_mul_eq_weighted

/-- **THE WEIGHTED FUNCTION IS STILL IN `L²`** — the weight is bounded by `e^{Cs/2}`.

DERIVED: the one numeral is `2`, the `Lᵖ` exponent carried from `Z` to the weighted function. -/
theorem memLp_weighted {s : (ι → MassGap.SUN.SU N) → ℝ} {Cs : ℝ} (hs : Continuous s)
    (hsb : ∀ V, |s V| ≤ Cs)
    (Z : MeasureTheory.Lp ℝ 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) :
    MeasureTheory.MemLp (weighted s (Z : _ → ℝ)) 2
      (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) := by
  refine ((MeasureTheory.Lp.memLp Z).const_mul (Real.exp (Cs / 2))).of_le ?_ ?_
  · exact ((Real.continuous_exp.comp (by fun_prop : Continuous
      fun V => -(s V) / 2)).aestronglyMeasurable).mul (MeasureTheory.Lp.aestronglyMeasurable Z)
  · refine Filter.Eventually.of_forall (fun V => ?_)
    have hle : Real.exp (-(s V) / 2) ≤ Real.exp (Cs / 2) := by
      refine Real.exp_le_exp.mpr ?_
      have := (abs_le.mp (hsb V)).1
      linarith
    unfold weighted
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

#print axioms memLp_weighted

/-- **`ker T = 0`: THE SLICE TRANSFER OPERATOR IS INJECTIVE, at every `b > 0`.**

The second of the three things standing between `transferCLM` and C1's Hamiltonian. Positivity was
§4; this is injectivity; the carrier on `ymH` is what is left.

DERIVED: `0 < b` is the sign positivity needs and `NegControl.su3_kernel_nonneg_iff` shows cannot be
dropped; the `2`s are the `L²` exponent and the even split of the intra-slice action. -/
theorem transferCLM_eq_zero {b : ℝ} (hb : 0 < b) {s : (ι → MassGap.SUN.SU N) → ℝ} {Cs : ℝ}
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs)
    (Z : MeasureTheory.Lp ℝ 2 (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
    (h : MassGap.SliceTransferSelfAdjoint.transferCLM b s Cs hs hsb Z = 0) :
    Z = 0 := by
  have hf2 := memLp_weighted hs hsb Z
  have hfint : MeasureTheory.Integrable (weighted s (Z : _ → ℝ))
      (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) := hf2.integrable (by norm_num)
  have h0 : (inner ℝ (MassGap.SliceTransferSelfAdjoint.transferCLM b s Cs hs hsb Z) Z : ℝ) = 0 := by
    rw [h]
    simp
  rw [inner_transferCLM_eq_double_integral] at h0
  have hform : (∫ V, MassGap.SlabKernelOperator.kernelFun (transferKernel b s)
        (MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) (Z : _ → ℝ) V * (Z : _ → ℝ) V
        ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N))
      = ∫ V, (∫ W, Real.exp (b * sliceForm V W) * weighted s (Z : _ → ℝ) W
            ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N)) * weighted s (Z : _ → ℝ) V
          ∂(MassGap.SliceTransferSelfAdjoint.sliceHaar ι N) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun V => kernelFun_mul_eq_weighted b s (Z : _ → ℝ) V))
  rw [hform] at h0
  have hcoef : ∀ (k : ℕ) (α : Fin k → ι × Coord N),
      sliceCoeff (weighted s (Z : _ → ℝ)) α = 0 :=
    fun k α => slice_gramCoeff_eq_zero hb hfint h0 α
  have hae := ae_eq_zero_of_sliceCoeff_eq_zero hf2 hcoef
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae] with V hV
  have hw : Real.exp (-(s V) / 2) * (Z : _ → ℝ) V = 0 := hV
  rcases mul_eq_zero.mp hw with h1 | h1
  · exact absurd h1 (Real.exp_pos _).ne'
  · exact h1

#print axioms transferCLM_eq_zero

/-- **and therefore injective**, since it is linear.

DERIVED: `0` is the strict lower bound on `b`; `2` is the `Lᵖ` exponent the operator acts on. -/
theorem transferCLM_injective {b : ℝ} (hb : 0 < b) {s : (ι → MassGap.SUN.SU N) → ℝ} {Cs : ℝ}
    (hs : Continuous s) (hsb : ∀ V, |s V| ≤ Cs) :
    Function.Injective (MassGap.SliceTransferSelfAdjoint.transferCLM b s Cs hs hsb) := by
  intro x y hxy
  have h : MassGap.SliceTransferSelfAdjoint.transferCLM b s Cs hs hsb (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have := transferCLM_eq_zero hb hs hsb (x - y) h
  exact sub_eq_zero.mp this

#print axioms transferCLM_injective

end MassGap.TransferGaussian
