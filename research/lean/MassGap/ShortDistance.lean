import Mathlib
import MassGap.ApproxFromExpand

/-!
# MassGap.ShortDistance — the short-distance clause, its tree values, and what it gives

The `SU(2)` target has four composite inputs that are not size statements: `CompNondeg`, `ObsLower` (equivalent to `NonGaussianT` given `CompOS`,
`InputsTriage.nonGaussianT_rhoD_iff_lower`), `CovC` and `WardT`. This module tests one clause
`ShortDist`: as the separation `t → 0`, every renormalised reading of `n ≤ 3` insertions equals its
leading perturbative value, the tree (Gaussian) value times the running-coupling factor, up to
relative error `→ 0`. The clause is a limit with explicit tree values; it asks no value at any fixed
separation, so it restates none of the four inputs.

## 1. Relative asymptotics (proved, abstract)

`RelTo R T`: `|R t − T t| ≤ ε |T t|` eventually as `t → 0⁺`, for every `ε > 0`.

* `eventually_ne_zero_of_relTo`, `exists_ne_zero_of_relTo`: if the tree value `T` is eventually
  non-zero, so is the reading `R`, and some `t > 0` has `R t ≠ 0`. This is the form in which a
  short-distance clause gives a non-vanishing input.
* `relTo_sub`: two readings with the same tree value differ by `o(|T|)`. An identity of the tree
  values (covariance, Ward identity) passes to the readings only in this asymptotic form.
* `relTo_not_exact`: two readings with the same tree value that differ at every `t > 0`. So an exact
  identity at a fixed separation, the form of `CovC` and `WardT`, is not a consequence of relative
  asymptotics, whatever the tree values satisfy.

## 2. The Gaussian tensor algebra (proved)

On `ℝ⁴ ⊗ ℝ⁴` (`Fin 4 × Fin 4`): `swapM` the exchange of the factors, `projA = 1 − swapM`,
`pT A = (A ⊗ A) · projA`. For `u ≠ 0`, `reflM u = 1 − 2 u uᵀ/(u·u)`.

* `pT_mul_pT`: `pT A · pT B = 2 · pT (A B)`.
* `trace_pT`: `tr pT M = (tr M)² − tr (M M)`.
* `tree2_eq`, `tree3_eq`: `tr (pT A pT B) = 2((tr AB)² − tr(AB AB))`,
  `tr (pT A pT B pT C) = 4((tr M)² − tr(M M))`, `M = ABC`.
* `det_one_add_add_det_one_sub`: for every `4 × 4` matrix,
  `det(1 + X) + det(1 − X) = 2 + (tr X)² − tr(X X) + 2 det X`.
* `trace_sq_eq_of_orth`: for `M` orthogonal with `det M = −1`, `(tr M)² = tr(M M)`
  (`det(1 ± M) = 0` from `M Mᵀ = 1` and the even dimension).
* `refl_orth`, `det_refl`: `reflM u` is orthogonal with determinant `−1` when `u ≠ 0`.
* `tree2_refl_self`: `tr (pT (reflM u) pT (reflM u)) = 24`.
* `tree3_refl_zero`: `tr (pT (reflM u) pT (reflM v) pT (reflM w)) = 0` for all non-zero `u, v, w`.

## 3. The tree values of the trace (definitions; their derivation is ARGUED)

ARGUED (the Gaussian measure on gauge potentials and the Wick contraction are not formalised):
in the free theory, Feynman gauge, `⟨A^a_μ(x) A^b_ν(0)⟩ = δ^{ab} δ_{μν}/(4π² x²)` gives
`⟨F^a_{μν}(x) F^b_{ρσ}(0)⟩ = δ^{ab} (I_{μρ} I_{νσ} − I_{μσ} I_{νρ})/(π² x⁴)`, `I = reflM x`, which is
`pT (reflM x)` as a matrix on index pairs. The trace channel `trC` has classical lead
`g² Σ_{μ,ν} F^aF^a` (`ScalarTie`: 24 plaquettes × 16 × N/(8a⁴)), tree value `48(N² − 1)/π⁴` at unit
separation, matching `afConst`. Its connected Gaussian `n`-point function is `2^{n−1}(n − 1)!` times
the cyclic contraction, which gives `treeTwoTr` and `treeThreeTr`:

* `treeTwoTr N g x y = 2g⁴(N² − 1)/π⁴ · tr(pT I pT I)/|x − y|⁸ = 48 g⁴ (N² − 1)/(π⁴ |x − y|⁸)`;
* `treeThreeTr N g x y z = 8g⁶(N² − 1)/π⁶ · tr(pT I₁ pT I₂ pT I₃)/(|x − y|⁴ |y − z|⁴ |z − x|⁴)`.

Proved about these expressions: `treeTwoTr_unit` (`= 48(N² − 1)/π⁴` at unit separation, `g = 1`),
`treeTwoTr_pos`, and `treeThreeTr_eq_zero`: **the tree three-point value of the trace vanishes at every
configuration of distinct points.** (ARGUED, the physics: the product of three reflections is an
orientation-reversing orthogonal map, whose action on 2-forms exchanges self-dual and anti-self-dual
parts and so has trace `0`; equivalently, free Maxwell theory is self-dual and `F² ↦ −F²`.)

## 4. The clause on the trace sector (definitions) and what it gives (proved)

`ThreePointKernel hN ρ G3`: `cum3T` is `∫∫∫ f g h G3` on separated continuous triples.
`ShortDist2 N G`: `r⁸ G(r) (log r)² → treeTwoTr(unit)/(4 b₀²)` (`ḡ⁴ (log r)² → 1/(4b₀²)`).
`ShortDist3 N G3`: `t¹² G3(t x, t y, t z) |log t|³ → treeThreeTr(x, y, z)/(8 b₀³)` at distinct
`x, y, z` (`ḡ⁶ |log t|³ → 1/(8b₀³)`). `ShortDistTr hN ρ`: kernels `G`, `G3` of the trace sector with
both.

* `eventually_pos_of_shortDist2`: under `ShortDist2`, `G > 0` near `0` (`2 ≤ N`).
* `shortDist2_const`: the limit of `ShortDist2` is `afConst N`. With `ScalarTie`'s normalisation
  `ShortDist2` is `AFCoefficient` (`shortDist2_const`); the target's `ScalarTie` and `afConst` agree.
* `shortDist3_zero`: the zero kernel satisfies `ShortDist3`. `not_nonGaussianT_of_zero_kernel`: a zero
  three-point kernel excludes `NonGaussianT`. `shortDist3_no_lower`: so `ShortDist3` with the tree
  value does not give `NonGaussianT`, hence not `ObsLower`.

## 5. Against the four inputs

1. `CompNondeg`. Proved (`compNondeg_of_shortDistC`) from two clauses on a value function
   `T : (C.Ix →₀ ℝ) → ℝ → ℝ`: `ShortDistC` (for every combination `c`, the reading `readC` at
   continuous test functions separated by `t` is `RelTo` `T c`) and `TreeNondeg` (where the
   top-dimension classical part of `c` is non-zero on shell, `T c` is non-zero near `0`). `TreeNondeg`
   speaks of `T` only. ARGUED, not formalised: `T` is the Gaussian (tree) value of the classical leads
   with the running-coupling factor; with `T` left free `ShortDistC` holds with `T := readC`, so the
   content of the pair lies in `T` being fixed by the free theory. On the trace channel `T` is
   `treeTwoTr` (§3), positive by `treeTwoTr_pos`; for general combinations the tree values need the
   Wick contraction of arbitrary `CMono`s, not built. ARGUED: when the free part of the top classical
   term vanishes (commutator combinations, `[D_μ, D_ν] = i g [F_μν, ·]`) the leading value sits at the
   next power of `g`, so `T` must be taken at the first non-vanishing order of each combination.
2. `ObsLower` / `NonGaussianT`. Not from `ShortDist`: the tree three-point value of the trace is
   identically `0` (`treeThreeTr_eq_zero`), so `ShortDist3` is satisfied by a zero kernel
   (`shortDist3_no_lower`). This is why `NonGaussianT` witnesses interaction: the Gaussian theory has
   no connected three-point function of the trace. ARGUED: the first non-zero order is `ḡ⁸`, from the
   cubic and quartic vertices, a loop computation not in the tree; a clause stating its coefficient
   (and that it is non-zero) would give `NonGaussianT` by §1.
3. `CovC`. Given `ConvC` (derived in the capstone), `CovC` is the identity
   `contC(i, f ∘ R) = Σ rep · contC(σ, f)` on every admissible family. The tree values are `O(4)`
   covariant (ARGUED; `pT` transforms by `R ⊗ R`). With `ShortDist`, `relTo_sub` gives the identity
   up to `o(|tree|)` as the separation `→ 0`; `relTo_not_exact` shows that no fixed separation
   follows. CovC at finite separation needs its own clause (rotation restoration at every scale).
4. `WardT`. Likewise: the tree values satisfy the classical (free) Ward identity with `κ = 0`
   (ARGUED); `ShortDist` gives it up to `o(|tree|)` at short distance, not the exact identity with a
   fixed `κ` at fixed `d` (`relTo_not_exact`).

## 6. What the clause gives

`compNondeg_of_shortDistC` gives `CompNondeg` from `ShortDistC` and `TreeNondeg`. The count of inputs does
not fall (one is traded for two). With `T` a free parameter the
pair is satisfied by `T := readC` exactly when the readings are eventually non-zero, so it is a
restatement of `CompNondeg`, not a reduction. It becomes a reduction once `T` is fixed to the tree
value of the classical leads, which is ARGUED and not built (§5.1).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and the factor of the triple product; `2` the projector
factor, the Wick factor over the four orderings of the index pairs and the squares; `48 = 2 · 24`
the tree value at unit separation; `0` the plane, the limit point and the
vanishing tree value; `1` the unit vector, the unit coupling and the identity; `8`, `12` the
scaling dimensions `2 · 4`, `3 · 4`; `3` the power of the log at `n = 3`; `6` the power of `π` and of
`g` at `n = 3`; `24` the value `2 (4² − 4)`; `1/2` the tolerance of `eventually_ne_zero_of_relTo`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ShortDistance

open Filter MeasureTheory
open scoped Topology Kronecker Matrix
open MassGap MassGap.ContinuumField MassGap.ClayStatement

/-! ## 1. Relative asymptotics -/

/-- **Relative asymptotics at `0⁺`**: `|R t − T t| ≤ ε |T t|` eventually, for every `ε > 0`.
DERIVED: `0` the limit point. -/
def RelTo (R T : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), |R t - T t| ≤ ε * |T t|

/-- **A non-zero tree value gives a non-zero reading** near `0`. DERIVED: `1/2` the tolerance. -/
theorem eventually_ne_zero_of_relTo {R T : ℝ → ℝ} (h : RelTo R T)
    (hT : ∀ᶠ t in 𝓝[>] (0 : ℝ), T t ≠ 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), R t ≠ 0 := by
  filter_upwards [h (1 / 2) (by norm_num), hT] with t h1 h2 hR
  rw [hR, zero_sub, abs_neg] at h1
  have : 0 < |T t| := abs_pos.mpr h2
  linarith

/-- **Some separation with a non-zero reading.** DERIVED: `0` the limit point. -/
theorem exists_ne_zero_of_relTo {R T : ℝ → ℝ} (h : RelTo R T)
    (hT : ∀ᶠ t in 𝓝[>] (0 : ℝ), T t ≠ 0) : ∃ t : ℝ, 0 < t ∧ R t ≠ 0 := by
  obtain ⟨t, h1, h2⟩ :=
    ((eventually_ne_zero_of_relTo h hT).and (eventually_mem_nhdsWithin (a := (0 : ℝ))
      (s := Set.Ioi 0))).exists
  exact ⟨t, h2, h1⟩

/-- **Two readings with one tree value agree to `o(|T|)`.** DERIVED: `2` the halving. -/
theorem relTo_sub {R₁ R₂ T : ℝ → ℝ} (h₁ : RelTo R₁ T) (h₂ : RelTo R₂ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), |R₁ t - R₂ t| ≤ ε * |T t| := by
  intro ε hε
  filter_upwards [h₁ (ε / 2) (by positivity), h₂ (ε / 2) (by positivity)] with t a b
  have := abs_sub_le (R₁ t) (T t) (R₂ t)
  rw [abs_sub_comm (T t)] at this
  linarith

/-- **Relative asymptotics fixes no value at a positive separation**: two readings with the same
tree value that differ at every `t > 0`. DERIVED: `1` the tree value and the shift. -/
theorem relTo_not_exact :
    ∃ R₁ R₂ T : ℝ → ℝ, RelTo R₁ T ∧ RelTo R₂ T ∧ ∀ t : ℝ, 0 < t → R₁ t ≠ R₂ t := by
  refine ⟨fun t => 1 + t, fun _ => 1, fun _ => 1, ?_, ?_, fun t ht h => ?_⟩
  · intro ε hε
    have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε :=
      (gt_mem_nhds hε).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlt, eventually_mem_nhdsWithin] with t h1 h2
    have h2' : (0 : ℝ) < t := h2
    show |1 + t - 1| ≤ ε * |(1 : ℝ)|
    rw [abs_one, mul_one, add_sub_cancel_left, abs_of_pos h2']
    exact h1.le
  · intro ε hε
    exact Filter.Eventually.of_forall fun t => by simp [hε.le]
  · have h' : 1 + t = 1 := h
    linarith

/-! ## 2. The Gaussian tensor algebra -/

/-- **The exchange of the two tensor factors** of `ℝ⁴ ⊗ ℝ⁴`. DERIVED: `4` the dimension; `1`, `0`
the entries. -/
def swapM : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℝ :=
  Matrix.of fun p q => if p = q.swap then 1 else 0

/-- DERIVED: `4` the dimension. -/
theorem mul_swapM_apply (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℝ) (p q : Fin 4 × Fin 4) :
    (X * swapM) p q = X p q.swap := by
  simp [Matrix.mul_apply, swapM]

/-- DERIVED: `4` the dimension. -/
theorem swapM_mul_apply (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℝ) (p q : Fin 4 × Fin 4) :
    (swapM * X) p q = X p.swap q := by
  have e : ∀ r : Fin 4 × Fin 4, (p = r.swap) ↔ (r = p.swap) := fun r =>
    ⟨fun h => by rw [h, Prod.swap_swap], fun h => by rw [h, Prod.swap_swap]⟩
  simp only [Matrix.mul_apply, swapM, Matrix.of_apply, e, ite_mul, one_mul, zero_mul]
  simp

/-- **`A ⊗ A` commutes with the exchange.** DERIVED: `4` the dimension. -/
theorem kron_swapM_comm (A : Matrix (Fin 4) (Fin 4) ℝ) : (A ⊗ₖ A) * swapM = swapM * (A ⊗ₖ A) := by
  ext p q
  rw [mul_swapM_apply, swapM_mul_apply]
  simp only [Matrix.kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap]
  ring

/-- **The exchange is an involution.** DERIVED: `4` the dimension. -/
theorem swapM_mul_self : swapM * swapM = 1 := by
  ext p q
  rw [swapM_mul_apply]
  by_cases hpq : p = q
  · simp [swapM, Matrix.one_apply, hpq]
  · simp [swapM, hpq, Prod.swap_injective.eq_iff]

/-- **Twice the antisymmetriser**, `1 − swap`. DERIVED: `1` the identity; `4` the dimension. -/
def projA : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℝ := 1 - swapM

/-- `(1 − swap)² = 2 (1 − swap)`. DERIVED: `2` the factor. -/
theorem projA_mul_self : projA * projA = (2 : ℝ) • projA := by
  unfold projA
  simp only [sub_mul, mul_sub, one_mul, mul_one, swapM_mul_self]
  rw [two_smul]
  abel

/-- DERIVED: `4` the dimension. -/
theorem kron_projA_comm (A : Matrix (Fin 4) (Fin 4) ℝ) : (A ⊗ₖ A) * projA = projA * (A ⊗ₖ A) := by
  unfold projA
  rw [mul_sub, sub_mul, mul_one, one_mul, kron_swapM_comm]

/-- **The propagator tensor** `(A ⊗ A)(1 − swap)`, entries `A_{μρ} A_{νσ} − A_{μσ} A_{νρ}`.
DERIVED: `4` the dimension. -/
def pT (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℝ :=
  (A ⊗ₖ A) * projA

/-- **The product of two propagator tensors**: `pT A · pT B = 2 · pT (A B)`. DERIVED: `2` the
factor of `projA_mul_self`. -/
theorem pT_mul_pT (A B : Matrix (Fin 4) (Fin 4) ℝ) : pT A * pT B = (2 : ℝ) • pT (A * B) := by
  unfold pT
  calc (A ⊗ₖ A) * projA * ((B ⊗ₖ B) * projA)
      = (A ⊗ₖ A) * ((projA * (B ⊗ₖ B)) * projA) := by simp only [Matrix.mul_assoc]
    _ = (A ⊗ₖ A) * (((B ⊗ₖ B) * projA) * projA) := by rw [kron_projA_comm]
    _ = ((A ⊗ₖ A) * (B ⊗ₖ B)) * (projA * projA) := by simp only [Matrix.mul_assoc]
    _ = (2 : ℝ) • (((A * B) ⊗ₖ (A * B)) * projA) := by
        rw [projA_mul_self, Matrix.mul_smul, ← Matrix.mul_kronecker_mul]

/-- **The trace of a propagator tensor**: `(tr M)² − tr(M M)`. DERIVED: `2` the square. -/
theorem trace_pT (M : Matrix (Fin 4) (Fin 4) ℝ) : (pT M).trace = M.trace ^ 2 - (M * M).trace := by
  unfold pT projA
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_kronecker]
  congr 1
  · ring
  · simp only [Matrix.trace, Matrix.diag_apply, mul_swapM_apply]
    simp only [Fintype.sum_prod_type, Prod.swap_prod_mk, Matrix.kroneckerMap_apply, Matrix.mul_apply]

/-- **The two-point contraction** `tr(pT A pT B)`. DERIVED: `4` the dimension. -/
def tree2 (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := (pT A * pT B).trace

/-- **The three-point contraction** `tr(pT A pT B pT C)`. DERIVED: `4` the dimension. -/
def tree3 (A B C : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := (pT A * pT B * pT C).trace

/-- DERIVED: `2` the factor of `pT_mul_pT` and the square. -/
theorem tree2_eq (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    tree2 A B = 2 * ((A * B).trace ^ 2 - (A * B * (A * B)).trace) := by
  unfold tree2
  rw [pT_mul_pT, Matrix.trace_smul, trace_pT, smul_eq_mul]

/-- DERIVED: `4 = 2 · 2` the factors of `pT_mul_pT`; `2` the square. -/
theorem tree3_eq (A B C : Matrix (Fin 4) (Fin 4) ℝ) :
    tree3 A B C = 4 * ((A * B * C).trace ^ 2 - (A * B * C * (A * B * C)).trace) := by
  unfold tree3
  rw [pT_mul_pT, Matrix.smul_mul, pT_mul_pT, smul_smul, Matrix.trace_smul, trace_pT, smul_eq_mul]
  norm_num

set_option maxHeartbeats 4000000 in
/-- **`det(1 + X) + det(1 − X) = 2 + (tr X)² − tr(X X) + 2 det X`** for every `4 × 4` matrix: the
even coefficients of `det(1 + tX)` at `t = ±1`. DERIVED: `2` the even part; `4` the dimension. -/
theorem det4_identity (a b c d e f g h i j k l m n o p : ℝ) :
    Matrix.det !![1 + a, b, c, d; e, 1 + f, g, h; i, j, 1 + k, l; m, n, o, 1 + p]
      + Matrix.det !![1 - a, -b, -c, -d; -e, 1 - f, -g, -h; -i, -j, 1 - k, -l; -m, -n, -o, 1 - p]
      = 2 + (a + f + k + p) ^ 2
        - (a * a + b * e + c * i + d * m + e * b + f * f + g * j + h * n
          + i * c + j * g + k * k + l * o + m * d + n * h + o * l + p * p)
        + 2 * Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, p] := by
  simp only [Matrix.det_succ_row_zero (n := 3), Fin.sum_univ_four, Matrix.det_fin_three]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  ring

/-- **The identity on a `4 × 4` matrix.** DERIVED: `2` the even part; `4` the dimension. -/
theorem det_one_add_add_det_one_sub (X : Matrix (Fin 4) (Fin 4) ℝ) :
    (1 + X).det + (1 - X).det = 2 + X.trace ^ 2 - (X * X).trace + 2 * X.det := by
  have h1 : 1 + X = !![1 + X 0 0, X 0 1, X 0 2, X 0 3; X 1 0, 1 + X 1 1, X 1 2, X 1 3;
      X 2 0, X 2 1, 1 + X 2 2, X 2 3; X 3 0, X 3 1, X 3 2, 1 + X 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h2 : 1 - X = !![1 - X 0 0, -X 0 1, -X 0 2, -X 0 3; -X 1 0, 1 - X 1 1, -X 1 2, -X 1 3;
      -X 2 0, -X 2 1, 1 - X 2 2, -X 2 3; -X 3 0, -X 3 1, -X 3 2, 1 - X 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h3 : X = !![X 0 0, X 0 1, X 0 2, X 0 3; X 1 0, X 1 1, X 1 2, X 1 3;
      X 2 0, X 2 1, X 2 2, X 2 3; X 3 0, X 3 1, X 3 2, X 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have ht : X.trace = X 0 0 + X 1 1 + X 2 2 + X 3 3 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four]
  have ht2 : (X * X).trace = X 0 0 * X 0 0 + X 0 1 * X 1 0 + X 0 2 * X 2 0 + X 0 3 * X 3 0
      + X 1 0 * X 0 1 + X 1 1 * X 1 1 + X 1 2 * X 2 1 + X 1 3 * X 3 1
      + X 2 0 * X 0 2 + X 2 1 * X 1 2 + X 2 2 * X 2 2 + X 2 3 * X 3 2
      + X 3 0 * X 0 3 + X 3 1 * X 1 3 + X 3 2 * X 2 3 + X 3 3 * X 3 3 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_four]
    ring
  rw [ht, ht2, h1, h2, det4_identity, ← h3]

/-- **`det(1 + M) = 0`** for `M` orthogonal with `det M = −1`. DERIVED: `1` the identity. -/
theorem det_one_add_eq_zero (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * M = 1) (hd : M.det = -1) :
    (1 + M).det = 0 := by
  have hMM : M * Mᵀ = 1 := mul_eq_one_comm.mp hM
  have e : 1 + M = M * (1 + M)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_one, hMM, add_comm]
  have h := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_transpose, hd] at h
  linarith

/-- **`det(1 − M) = 0`** for `M` orthogonal with `det M = −1` in even dimension. DERIVED: `1` the
identity; `4` the dimension. -/
theorem det_one_sub_eq_zero (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * M = 1) (hd : M.det = -1) :
    (1 - M).det = 0 := by
  have hMM : M * Mᵀ = 1 := mul_eq_one_comm.mp hM
  have e : 1 - M = -(M * (1 - M)ᵀ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, hMM, neg_sub]
  have h := congrArg Matrix.det e
  rw [Matrix.det_neg, Matrix.det_mul, Matrix.det_transpose, hd, Fintype.card_fin] at h
  norm_num at h
  linarith

/-- **`(tr M)² = tr(M M)`** for `M` orthogonal with `det M = −1`: the second elementary symmetric
function of the eigenvalues vanishes. DERIVED: `2` the square. -/
theorem trace_sq_eq_of_orth (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * M = 1) (hd : M.det = -1) :
    M.trace ^ 2 = (M * M).trace := by
  have h := det_one_add_add_det_one_sub M
  rw [det_one_add_eq_zero M hM hd, det_one_sub_eq_zero M hM hd, hd] at h
  linarith

/-- **The reflection** `1 − 2 u uᵀ/(u·u)` in the hyperplane orthogonal to `u`. DERIVED: `2` the
reflection factor; `4` the dimension. -/
def reflM (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  1 - (2 / (u ⬝ᵥ u)) • Matrix.vecMulVec u u

/-- DERIVED: no numeral. -/
theorem refl_transpose (u : Fin 4 → ℝ) : (reflM u)ᵀ = reflM u := by
  unfold reflM
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

/-- DERIVED: `2` the reflection factor; `0` the excluded vector. -/
theorem refl_mul_self (u : Fin 4 → ℝ) (hu : u ⬝ᵥ u ≠ 0) : reflM u * reflM u = 1 := by
  unfold reflM
  set c : ℝ := 2 / (u ⬝ᵥ u) with hc
  set P := Matrix.vecMulVec u u with hP
  have hPP : P * P = (u ⬝ᵥ u) • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h2 : c * (u ⬝ᵥ u) = 2 := by rw [hc]; exact div_mul_cancel₀ 2 hu
  have hcc : c * c * (u ⬝ᵥ u) = 2 * c := by
    calc c * c * (u ⬝ᵥ u) = c * (c * (u ⬝ᵥ u)) := by ring
      _ = 2 * c := by rw [h2]; ring
  calc (1 - c • P) * (1 - c • P) = 1 - (2 * c) • P + (c * c) • (P * P) := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [two_mul, add_smul]
        abel
    _ = 1 := by rw [hPP, smul_smul, hcc, sub_add_cancel]

/-- **The reflection is orthogonal.** DERIVED: `0` the excluded vector. -/
theorem refl_orth (u : Fin 4 → ℝ) (hu : u ⬝ᵥ u ≠ 0) : (reflM u)ᵀ * reflM u = 1 := by
  rw [refl_transpose, refl_mul_self u hu]

/-- **The reflection has determinant `−1`** (the matrix determinant lemma). DERIVED: `2` the
reflection factor; `1` the sign. -/
theorem det_refl (u : Fin 4 → ℝ) (hu : u ⬝ᵥ u ≠ 0) : (reflM u).det = -1 := by
  have e : reflM u = 1 + Matrix.replicateCol Unit (-(2 / (u ⬝ᵥ u)) • u)
      * Matrix.replicateRow Unit u := by
    rw [← Matrix.vecMulVec_eq Unit]
    unfold reflM
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul, neg_mul,
    div_mul_cancel₀ (2 : ℝ) hu]
  norm_num

/-- DERIVED: no numeral. -/
theorem orth_mul {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A * B)ᵀ * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, Matrix.one_mul, hB]

/-- **The two-point contraction at one reflection is `24`**. DERIVED: `24 = 2 (4² − 4)`. -/
theorem tree2_refl_self (u : Fin 4 → ℝ) (hu : u ⬝ᵥ u ≠ 0) : tree2 (reflM u) (reflM u) = 24 := by
  rw [tree2_eq, refl_mul_self u hu, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- **The three-point contraction of three reflections vanishes.** The product is orthogonal with
determinant `−1`, so `(tr M)² = tr(M M)` (`trace_sq_eq_of_orth`). DERIVED: `0` the value. -/
theorem tree3_refl_zero (u v w : Fin 4 → ℝ) (hu : u ⬝ᵥ u ≠ 0) (hv : v ⬝ᵥ v ≠ 0)
    (hw : w ⬝ᵥ w ≠ 0) : tree3 (reflM u) (reflM v) (reflM w) = 0 := by
  have hM : (reflM u * reflM v * reflM w)ᵀ * (reflM u * reflM v * reflM w) = 1 :=
    orth_mul (orth_mul (refl_orth u hu) (refl_orth v hv)) (refl_orth w hw)
  have hd : (reflM u * reflM v * reflM w).det = -1 := by
    rw [Matrix.det_mul, Matrix.det_mul, det_refl u hu, det_refl v hv, det_refl w hw]
    norm_num
  rw [tree3_eq, trace_sq_eq_of_orth _ hM hd, sub_self, mul_zero]

/-! ## 3. The tree values of the trace -/

/-- A separation vector of distinct points has non-zero square length. DERIVED: `0` the excluded
value. -/
theorem dot_sub_ne_zero {x y : Fin 4 → ℝ} (h : x ≠ y) : (x - y) ⬝ᵥ (x - y) ≠ 0 := fun h0 =>
  h (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0))

/-- **The tree two-point value of the trace**: `2g⁴(N² − 1)/π⁴ · tr(pT I pT I)/|x − y|⁸`,
`I = reflM (x − y)`, with `trC`'s classical lead `g² F^aF^a` (`ScalarTie`). Its derivation as the
Gaussian value is ARGUED (module docstring, §3). DERIVED: `4` the power of `g` and of `π` and of
`|x − y|²`; `2` the Wick factor over the four orderings of the index pairs; `1` the subtraction in
`N² − 1`. -/
def treeTwoTr (N : ℕ) (g : ℝ) (x y : Fin 4 → ℝ) : ℝ :=
  2 * g ^ 4 * ((N : ℝ) ^ 2 - 1) / Real.pi ^ 4 * tree2 (reflM (x - y)) (reflM (x - y))
    / ((x - y) ⬝ᵥ (x - y)) ^ 4

/-- **The tree three-point value of the trace**:
`8g⁶(N² − 1)/π⁶ · tr(pT I₁ pT I₂ pT I₃)/(|x − y|⁴ |y − z|⁴ |z − x|⁴)`, with `trC`'s classical lead
`g² F^aF^a` (`ScalarTie`). Its derivation as the Gaussian value is ARGUED (module docstring, §3).
DERIVED: `6` the power of `g` and of `π`; `8 = 2² · 2!` the cyclic Wick factor at `n = 3`; `2` the
power of each square length; `1` the subtraction in `N² − 1`. -/
def treeThreeTr (N : ℕ) (g : ℝ) (x y z : Fin 4 → ℝ) : ℝ :=
  8 * g ^ 6 * ((N : ℝ) ^ 2 - 1) / Real.pi ^ 6
    * tree3 (reflM (x - y)) (reflM (y - z)) (reflM (z - x))
    / (((x - y) ⬝ᵥ (x - y)) ^ 2 * ((y - z) ⬝ᵥ (y - z)) ^ 2 * ((z - x) ⬝ᵥ (z - x)) ^ 2)

/-- **The tree three-point value of the trace vanishes** at every configuration of distinct points.
DERIVED: `0` the value. -/
theorem treeThreeTr_eq_zero (N : ℕ) (g : ℝ) {x y z : Fin 4 → ℝ} (hxy : x ≠ y) (hyz : y ≠ z)
    (hzx : z ≠ x) : treeThreeTr N g x y z = 0 := by
  unfold treeThreeTr
  rw [tree3_refl_zero _ _ _ (dot_sub_ne_zero hxy) (dot_sub_ne_zero hyz) (dot_sub_ne_zero hzx)]
  simp

/-- The unit vector of the first direction. DERIVED: `0` the direction; `1` the length. -/
def unitVec : Fin 4 → ℝ := Pi.single 0 1

/-- DERIVED: `1` the length. -/
theorem unitVec_dot : unitVec ⬝ᵥ unitVec = 1 := by
  simp [unitVec, dotProduct, Fin.sum_univ_four]

/-- **The tree two-point value at unit separation and unit coupling**: `48(N² − 1)/π⁴`.
DERIVED: `48 = 2 · 24`; `4` the power of `π`. -/
theorem treeTwoTr_unit (N : ℕ) : treeTwoTr N 1 unitVec 0 = 48 * ((N : ℝ) ^ 2 - 1) / Real.pi ^ 4 := by
  unfold treeTwoTr
  rw [sub_zero, tree2_refl_self unitVec (by rw [unitVec_dot]; exact one_ne_zero), unitVec_dot]
  ring

/-- **The tree two-point value is positive** at distinct points, `g ≠ 0`, `2 ≤ N`.
DERIVED: `2` the least colour count; `0` the sign. -/
theorem treeTwoTr_pos {N : ℕ} (hN2 : 2 ≤ N) {g : ℝ} (hg : g ≠ 0) {x y : Fin 4 → ℝ} (hxy : x ≠ y) :
    0 < treeTwoTr N g x y := by
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hn : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by nlinarith
  have hd0 : 0 ≤ (x - y) ⬝ᵥ (x - y) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hd : 0 < (x - y) ⬝ᵥ (x - y) := lt_of_le_of_ne hd0 (dot_sub_ne_zero hxy).symm
  unfold treeTwoTr
  rw [tree2_refl_self _ (dot_sub_ne_zero hxy)]
  have hg4 : 0 < 2 * g ^ 4 := by positivity
  exact div_pos (mul_pos (div_pos (mul_pos hg4 hn) (by positivity)) (by norm_num)) (pow_pos hd 4)

/-! ## 4. The clause on the trace sector -/

section Clause

variable {N : ℕ}

/-- **The three-point kernel of the trace**: on separated continuous triples,
`cum3T f g h = ∫∫∫ f(x) g(y) h(z) G3(x, y, z)`. DERIVED: `0` the sign of the separation. -/
def ThreePointKernel (hN : N ≠ 0) (ρ : RenormMix N)
    (G3 : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ f g h : TestFn, Continuous f.1 → Continuous g.1 → Continuous h.1 →
    (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g ∧ ContinuumSep.sepBy d f h
        ∧ ContinuumSep.sepBy d g h) →
      cum3T hN ρ f g h = ∫ x, ∫ y, ∫ z, f.1 x * g.1 y * h.1 z * G3 x y z

/-- **The short-distance clause at `n = 2`**: `r⁸ G(r) (log r)² → treeTwoTr(unit)/(4 b₀²)`, the tree
value times the limit of `ḡ⁴ (log r)²`. DERIVED: `8 = 2 · 4` the scaling dimension; `2` the power of
the log; `4 b₀²` the running-coupling limit; `0` the limit point; `1` the unit coupling. -/
def ShortDist2 (N : ℕ) (G : ℝ → ℝ) : Prop :=
  Tendsto (fun r => r ^ 8 * G r * Real.log r ^ 2) (𝓝[>] (0 : ℝ))
    (𝓝 (treeTwoTr N 1 unitVec 0 / (4 * b0 N ^ 2)))

/-- **The short-distance clause at `n = 3`**: at distinct `x, y, z`,
`t¹² G3(t x, t y, t z) |log t|³ → treeThreeTr(x, y, z)/(8 b₀³)`, the tree value times the limit of
`ḡ⁶ |log t|³`. DERIVED: `12 = 3 · 4` the scaling dimension; `3` the power of the log; `8 b₀³` the
running-coupling limit; `0` the limit point; `1` the unit coupling. -/
def ShortDist3 (N : ℕ) (G3 : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ x y z : Fin 4 → ℝ, x ≠ y → y ≠ z → z ≠ x →
    Tendsto (fun t : ℝ => t ^ 12 * G3 (t • x) (t • y) (t • z) * |Real.log t| ^ 3) (𝓝[>] (0 : ℝ))
      (𝓝 (treeThreeTr N 1 x y z / (8 * b0 N ^ 3)))

/-- **The short-distance clause of the trace sector**: a two-point kernel and a three-point kernel
with `ShortDist2` and `ShortDist3`. DERIVED: no numeral. -/
def ShortDistTr (hN : N ≠ 0) (ρ : RenormMix N) : Prop :=
  ∃ (G : ℝ → ℝ) (G3 : (Fin 4 → ℝ) → (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ),
    TwoPointKernel hN ρ G ∧ ThreePointKernel hN ρ G3 ∧ ShortDist2 N G ∧ ShortDist3 N G3

/-- **The limit of `ShortDist2` is `afConst N`**: `ShortDist2` is `AFCoefficient`. DERIVED: `4` the
running-coupling limit `4 b₀²`. -/
theorem shortDist2_const (N : ℕ) :
    treeTwoTr N 1 unitVec 0 / (4 * b0 N ^ 2) = afConst N := by
  rw [treeTwoTr_unit]
  unfold afConst
  ring

/-- **Under `ShortDist2` the kernel is positive near `0`.** DERIVED: `2` the least colour count;
`0` the sign. -/
theorem eventually_pos_of_shortDist2 (hN2 : 2 ≤ N) {G : ℝ → ℝ} (h : ShortDist2 N G) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < G r := by
  have hL : 0 < treeTwoTr N 1 unitVec 0 / (4 * b0 N ^ 2) := by
    rw [shortDist2_const]
    exact afConst_pos hN2
  filter_upwards [h.eventually (lt_mem_nhds hL)] with r h1
  by_contra hG
  rw [not_lt] at hG
  have hp : 0 ≤ r ^ 8 * Real.log r ^ 2 := by positivity
  have e : r ^ 8 * G r * Real.log r ^ 2 = G r * (r ^ 8 * Real.log r ^ 2) := by ring
  rw [e] at h1
  linarith [mul_nonneg (neg_nonneg.mpr hG) hp]

/-- **The zero kernel satisfies `ShortDist3`**, because the tree value vanishes. DERIVED: `0` the
kernel. -/
theorem shortDist3_zero (N : ℕ) : ShortDist3 N (fun _ _ _ => 0) := by
  intro x y z hxy hyz hzx
  rw [treeThreeTr_eq_zero N 1 hxy hyz hzx, zero_div]
  simp only [mul_zero, zero_mul]
  exact tendsto_const_nhds

/-- **A zero three-point kernel excludes `NonGaussianT`.** DERIVED: `0` the kernel. -/
theorem not_nonGaussianT_of_zero_kernel (hN : N ≠ 0) (ρ : RenormMix N)
    (hK : ThreePointKernel hN ρ (fun _ _ _ => 0)) : ¬ NonGaussianT hN ρ := by
  rintro ⟨f, g, h, hf, hg, hh, hsep, hne⟩
  apply hne
  rw [hK f g h hf hg hh hsep]
  simp

/-- **`ShortDist3` gives no lower bound**: the zero kernel satisfies it, and on every sector with zero
three-point kernel `NonGaussianT` fails. So `ShortDist3` with the tree value does not give
`NonGaussianT`. DERIVED: `0` the kernel. -/
theorem shortDist3_no_lower (N : ℕ) :
    ShortDist3 N (fun _ _ _ => 0)
      ∧ ∀ (hN : N ≠ 0) (ρ : RenormMix N), ThreePointKernel hN ρ (fun _ _ _ => 0) →
          ¬ NonGaussianT hN ρ :=
  ⟨shortDist3_zero N, fun hN ρ hK => not_nonGaussianT_of_zero_kernel hN ρ hK⟩

end Clause

/-! ## 5. The clause on every composite combination, and `CompNondeg` -/

section Comp

variable {N : ℕ} (hN : N ≠ 0) (C : Composites N)

/-- **The two-point reading of a combination** `∑ cᵢ Φᵢ` at `(f, h)`: the quantity `CompNondeg` asks
to be non-zero. DERIVED: `2` the order. -/
def readC (c : C.Ix →₀ ℝ) (f h : TestFn) : ℝ :=
  ∑ i ∈ c.support, ∑ j ∈ c.support,
    c i * c j * contC hN C (![(i, f), (j, h)] : Fin 2 → CDatum C)

/-- **The short-distance clause on composites at `n = 2`**: for every combination `c` there are
continuous test functions `f t`, `h t` separated by `t` whose reading is `RelTo` the value `T c t`.
`T` is the leading perturbative value (tree value times running-coupling factor); its identification
with the Gaussian Wick contraction of the classical leads `C.cl` is ARGUED, not formalised. With `T`
left free the clause is satisfied by `T c t := readC …` itself, so its content lies in `T` being fixed
by the free theory. DERIVED: `0` the limit point and the sign of the separation. -/
def ShortDistC (T : (C.Ix →₀ ℝ) → ℝ → ℝ) : Prop :=
  ∀ c : C.Ix →₀ ℝ, ∃ f h : ℝ → TestFn,
    (∀ t : ℝ, 0 < t → Continuous (f t).1 ∧ Continuous (h t).1 ∧ ContinuumSep.sepBy t (f t) (h t))
    ∧ RelTo (fun t => readC hN C c (f t) (h t)) (T c)

/-- **Tree non-degeneracy**: whenever the top-dimension classical part of `c` is non-zero on some
on-shell potential (the premise of `CompNondeg`), the leading value `T c` is non-zero near `0`. A
statement about `T` only, not about the interacting readings. DERIVED: `0` the limit point and the
excluded value. -/
def TreeNondeg (T : (C.Ix →₀ ℝ) → ℝ → ℝ) : Prop :=
  ∀ c : C.Ix →₀ ℝ,
    (∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim (C.cl i) = c.support.sup (fun j => cdim (C.cl j))),
          c i * g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0) →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), T c t ≠ 0

/-- **`CompNondeg` from the short-distance clause and tree non-degeneracy.** DERIVED: no numeral. -/
theorem compNondeg_of_shortDistC {T : (C.Ix →₀ ℝ) → ℝ → ℝ} (hS : ShortDistC hN C T)
    (hT : TreeNondeg C T) : CompNondeg hN C := by
  intro c hc
  obtain ⟨f, h, hfh, hR⟩ := hS c
  obtain ⟨t, ht, hne⟩ := exists_ne_zero_of_relTo hR (hT c hc)
  obtain ⟨h1, h2, h3⟩ := hfh t ht
  exact ⟨f t, h t, h1, h2, ⟨t, ht, h3⟩, hne⟩

end Comp

end MassGap.ShortDistance

end

#print axioms MassGap.ShortDistance.eventually_ne_zero_of_relTo
#print axioms MassGap.ShortDistance.exists_ne_zero_of_relTo
#print axioms MassGap.ShortDistance.relTo_sub
#print axioms MassGap.ShortDistance.relTo_not_exact
#print axioms MassGap.ShortDistance.pT_mul_pT
#print axioms MassGap.ShortDistance.trace_pT
#print axioms MassGap.ShortDistance.tree2_eq
#print axioms MassGap.ShortDistance.tree3_eq
#print axioms MassGap.ShortDistance.det4_identity
#print axioms MassGap.ShortDistance.det_one_add_add_det_one_sub
#print axioms MassGap.ShortDistance.trace_sq_eq_of_orth
#print axioms MassGap.ShortDistance.refl_orth
#print axioms MassGap.ShortDistance.det_refl
#print axioms MassGap.ShortDistance.tree2_refl_self
#print axioms MassGap.ShortDistance.tree3_refl_zero
#print axioms MassGap.ShortDistance.treeThreeTr_eq_zero
#print axioms MassGap.ShortDistance.treeTwoTr_unit
#print axioms MassGap.ShortDistance.treeTwoTr_pos
#print axioms MassGap.ShortDistance.shortDist2_const
#print axioms MassGap.ShortDistance.eventually_pos_of_shortDist2
#print axioms MassGap.ShortDistance.shortDist3_zero
#print axioms MassGap.ShortDistance.not_nonGaussianT_of_zero_kernel
#print axioms MassGap.ShortDistance.shortDist3_no_lower
#print axioms MassGap.ShortDistance.compNondeg_of_shortDistC
