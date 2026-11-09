import Mathlib
import MassGap.LoopZoom
import MassGap.BoxFocusTest
import MassGap.PeriodicReduce

/-!
# MassGap.FocusFeed — from loop-pair covariance bounds to the diagonal shell bound of `LoopZoom`

`FocusZoom` (section "How the remainder would feed `LoopZoom.zeroFluxGap_of_electricDiag`") names two
gaps between the covariance bounds of the periodic Wilson state (`BoxFocusTest.cov_le_of_kernelNear`,
`FocusZoom.cov_le_of_focus`) and the diagonal shell bound on the slice operator `T = kernelCLM` of
`trivKN 2 β n i` that `LoopZoom.zeroFluxGap_of_electricDiag` asks: (a) the bridge from the periodic
state's connected pairings to the slice's shell elements; (b) the uniformity over a shell. This module
proves every link that holds on the declarations and states the one that does not as a hypothesis.

## 1. The two connected pairings (proved, each on its own objects)

* **Slice** (`loopPair_centred`, real objects, `0 ≤ β`): for loops `C, C'` and every `m`, with
  `Ω = φ_{g₀}`, `u_C = W_C Ω`, `ψ_C` the loop state,
  `⟪T^m ψ_C, ψ_C'⟫ = ⟪T^m u_C, u_C'⟫ − μ_{g₀}^m ⟨W_C⟩ ⟨W_C'⟩`. The abstract form is
  `inner_pow_centred` (any symmetric `T` with `T Ω = μ Ω`, `‖Ω‖ = 1`). The diagonal shell bound reads
  the pairing `⟪T x, T y⟫ = ⟪T² x, y⟫` (`inner_T_T`), i.e. `m = 2`, the transfer time `t = n a` of
  `μ_j² = e^{−E_j t}` (`TensionFloor.EigenLevels.energy`).
* **Periodic** (`periodic_connPair`): on `D = PeriodicState.periodicGaugeInvData τ p hN β` and
  `ν = periodicState hN β`, for `x, y` in the gauge-invariant half-space algebra and every `c`,
  `D.form x (Tᶜ y) − D.form x D.vac · D.form D.vac (Tᶜ y) = Cov_ν(θx, Sᶜy)`
  (`periodic_form_pair` is the polarised `PeriodicReduce.periodic_form_pow`). With
  `BoxFocusTest.KernelNear Δ (θx) δ`, `Sᶜy` not reading `Δ` and `|Sᶜy| ≤ M`, this connected pairing is
  at most `2 M δ` (`periodic_connPair_le_of_kernelNear`).

**The bridge between them is not a declaration, and is not an identity** (argued). The slice is the
`SU(2)` spatial torus of extents `Tr n i` with the zero-flux transfer over half the time extent and the
finite-volume ground state `φ_{g₀}`; `ν` is the infinite-volume `SU(N)` limit along
`periodicUltra hN β` of tori of extent `2(j+1)` in all four directions. At `N = 2` the two pairings
are the same correlator in two volumes (finite spatial torus with the zero-flux projection, against
ℤ⁴), so any relation carries a finite-volume error. It enters below as the named hypothesis `hbridge`
with error `η_k`.

## 2. From pair bounds to a block bound (proved, any real inner product space)

* **`norm_sq_T_sum_le`** (Schur on a family): for a finite family `v_j`, pair bounds
  `|⟪T v_j, T v_l⟫| ≤ ε_jl` with row and column sums at most `D ≥ 0`, and a Gram lower bound
  `λ Σ a_j² ≤ ‖Σ a_j v_j‖²` (`λ > 0`): `‖T(Σ a_j v_j)‖² ≤ (D/λ) ‖Σ a_j v_j‖²`.
* **`norm_sq_le_on_span`**: with one bound `ε` for all pairs, every `x ∈ span(v)` has
  `‖T x‖² ≤ (d ε / λ) ‖x‖²`, `d = #κ` the number of spanning vectors. **This is how the finite dimension
  enters**: through `d` and the least Gram eigenvalue `λ` of the chosen spanning family. A Gram lower
  bound `λ > 0` holds only for a linearly independent family; argued, not a declaration: loop states are
  linearly dependent (Mandelstam, `ElectricLoops.Loop.wl_mul`), so the family is a basis of the shell
  chosen among its spanning vectors.
* **`inf_orth_eq_span`, `shell_succ_eq_span`**: `B ⊓ Aᗮ` is spanned by the images of `B`'s generators
  under `1 − P_A`. So shell `k + 1` is spanned by the **projected** loop states
  `(1 − P_{H_{R_k}}) ψ_C`, `a · len C ≤ R_{k+1}` (shell `0` is spanned by the loop states themselves).
  The pairings a shell's block bound reads are those of projected loop states: each is (argued) a combination,
  with coefficients from the inverse Gram matrix of `H_{R_k}`, of loop–loop pairings including loops of
  every smaller size.

**Uniformity** (argued): `d_k` is at least the dimension of shell `k`, which counts the independent
projected loop states of perimeter in `(R_{k−1}, R_k]`, including all their spatial translates on the
torus of side `~ L/a`; `λ_k` is a Gram eigenvalue that nothing in the tree bounds below. So the bound is
not uniform: it asks each pair bound `ε_k ≤ λ_k μ² e^{−(c σ R_k + c'/R_k) t} / d_k`, with `d_k` growing
with the volume at fixed `R_k`. This is the quantitative form of the clustering `LoopZoom.block_rayleigh`
found circular: the per-pair bound must beat the number of pairs.

## 3. The composed theorems (proved, conditional on the named inputs)

* **`zeroFluxGap_of_shellPairs`**: the hypotheses of `LoopZoom.zeroFluxGap_of_electricDiag` except its
  diagonal clause, plus for each shell `k` a finite family `v_k` whose span contains the shell, a Gram
  bound `λ_k > 0`, a uniform pair bound `|⟪T v_kj, T v_kl⟫| ≤ e_k`, and
  `d_k e_k ≤ λ_k μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}`: then `ZeroFluxGap g₀ E (diagRate c c' σ δ t)`.
* **`zeroFluxGap_of_kernelNear_bridge`**: the same, with `e_k = 2 M_k δ_k + η_k` produced by
  `KernelNear` at the focal boxes: for periodic observables `X_kj` (on `IConf (SU 2)`), a reflection
  `θ = ireflObs τ (2p)` and a shift `S^s`, if for every pair `KernelNear Δ (θ X_kj) δ_k` holds at some box
  `Δ` that `S^s X_kl` does not read, `|S^s X_kl| ≤ M_k`, and the **bridge**
  `|⟪T v_kj, T v_kl⟫| ≤ |Cov_ν(θ X_kj, S^s X_kl)| + η_k` (`ν = periodicState` at `SU(2)`, coupling `β`),
  then the gap holds once `d_k (2 M_k δ_k + η_k) ≤ λ_k μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}`.

## What remains (named)

1. `hbridge`: the slice pairing of the shell's basis vectors against the periodic covariance of chosen
   observables, with error `η_k`. Not in the tree; not an identity (§1). `X`, `τ`, `p`, `s` are unconstrained:
   at `X = 0`, `hnear` holds with `δ_k = M_k = 0` and `hbridge` is the pair bound `he` with `e_k = η_k`, so the
   bridge theorem is as strong as `zeroFluxGap_of_shellPairs`; the `KernelNear` part is load-bearing only when
   `X_kj` is the periodic counterpart of `v_kj` with `η_k` small (argued, not a declaration).
2. `hnear`: `KernelNear` at the focal box for every reflected basis observable, at `δ_k` with
   `d_k (2 M_k δ_k + η_k) / λ_k` below the shell rate (`BoxFocusTest`, item 5: open uniformly in `β`).
3. The Gram bound `λ_k` of the chosen basis, and its size against `d_k` (§2, not uniform).

## What is proved

* §1 (abstract): `mul_app`, `pow_vac`, `pow_symm`, `inner_T_T`, `inner_pow_centred`, `norm_sq_T_sum_le`,
  `norm_sq_le_on_span`, `inf_orth_eq_span`.
* §2 (loop shells): `shell_zero_eq`, `shell_succ_eq_span`.
* §3 (slice): `loopVec`, `loopPair_centred`.
* §4 (periodic state): `coe_T_pow`, `periodic_form_pair`, `periodic_form_vac_left`, `periodic_connPair`,
  `periodic_connPair_le_of_kernelNear`.
* §5 (composed): `zeroFluxGap_of_shellPairs`, `zeroFluxGap_of_kernelNear_bridge`.

DERIVED (module-wide): `2` is the `L²` exponent, the square in `‖·‖²`, the power `T²` in `inner_T_T`, `N = 2`
of the slice, the doubling `2p` of the reflection plane, and the two-sided spread `2 M δ` of
`BoxFocusTest.cov_le_of_near_const`; `1/2` is `|a b| ≤ (a² + b²)/2`; `1` is the unit norm of `Ω`
and the constant observable.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FocusFeed

open MeasureTheory Filter
open MassGap.ElectricLoops

/-! ## 1. Abstract: centred powers, Schur on a family, shells spanned by projections -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Composition of operators, applied. -/
theorem mul_app (A B : E →L[ℝ] E) (z : E) : (A * B) z = A (B z) := rfl

/-- `T Ω = μ Ω` gives `T^m Ω = μ^m Ω`. -/
theorem pow_vac {T : E →L[ℝ] E} {Ω : E} {μ : ℝ} (hΩ : T Ω = μ • Ω) (m : ℕ) :
    (T ^ m) Ω = μ ^ m • Ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_app, hΩ, map_smul, ih, smul_smul, pow_succ, mul_comm]

/-- A symmetric `T` has symmetric powers. -/
theorem pow_symm {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) (m : ℕ) :
    ∀ x y, inner ℝ ((T ^ m) x) y = inner ℝ x ((T ^ m) y) := by
  induction m with
  | zero => intro x y; simp
  | succ m ih =>
    intro x y
    calc inner ℝ ((T ^ (m + 1)) x) y = inner ℝ (T ((T ^ m) x)) y := by rw [pow_succ', mul_app]
      _ = inner ℝ ((T ^ m) x) (T y) := hT _ _
      _ = inner ℝ x ((T ^ m) (T y)) := ih _ _
      _ = inner ℝ x ((T ^ (m + 1)) y) := by rw [pow_succ, mul_app]

/-- `⟪T x, T y⟫ = ⟪T² x, y⟫` for symmetric `T`. -/
theorem inner_T_T {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y)) (x y : E) :
    inner ℝ (T x) (T y) = inner ℝ ((T ^ 2) x) y := by
  rw [pow_two, mul_app, hT (T x) y]

/-- **The centred pairing at power `m` is the raw one minus the disconnected part**: for symmetric `T`
with `T Ω = μ Ω`, `‖Ω‖ = 1`,
`⟪T^m (u − ⟪Ω,u⟫Ω), u' − ⟪Ω,u'⟫Ω⟫ = ⟪T^m u, u'⟫ − μ^m ⟪Ω,u⟫ ⟪Ω,u'⟫`. -/
theorem inner_pow_centred {T : E →L[ℝ] E} (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    {Ω : E} {μ : ℝ} (hΩ : T Ω = μ • Ω) (h1 : ‖Ω‖ = 1) (m : ℕ) (u u' : E) :
    inner ℝ ((T ^ m) (u - inner ℝ Ω u • Ω)) (u' - inner ℝ Ω u' • Ω)
      = inner ℝ ((T ^ m) u) u' - μ ^ m * inner ℝ Ω u * inner ℝ Ω u' := by
  have hTu : inner ℝ ((T ^ m) u) Ω = μ ^ m * inner ℝ Ω u := by
    rw [pow_symm hT, pow_vac hΩ, real_inner_smul_right, real_inner_comm]
  have hΩΩ : inner ℝ Ω Ω = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h1]; norm_num
  rw [map_sub, map_smul, pow_vac hΩ, smul_smul, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, hTu,
    hΩΩ]
  ring

/-- **Schur on a family.** Pair bounds `|⟪T v_j, T v_l⟫| ≤ ε_jl` with row and column sums at most
`D ≥ 0`, and a Gram lower bound `λ Σ a_j² ≤ ‖Σ a_j v_j‖²` with `λ > 0`, give
`‖T(Σ a_j v_j)‖² ≤ (D/λ) ‖Σ a_j v_j‖²`. -/
theorem norm_sq_T_sum_le {κ : Type*} [Fintype κ] (T : E →L[ℝ] E) (v : κ → E) (ε : κ → κ → ℝ)
    (hε : ∀ j l, |inner ℝ (T (v j)) (T (v l))| ≤ ε j l) {D lam : ℝ} (hD : 0 ≤ D)
    (hrow : ∀ j, ∑ l, ε j l ≤ D) (hcol : ∀ l, ∑ j, ε j l ≤ D) (hlam : 0 < lam)
    (hgram : ∀ a : κ → ℝ, lam * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v j‖ ^ 2) (a : κ → ℝ) :
    ‖T (∑ j, a j • v j)‖ ^ 2 ≤ D / lam * ‖∑ j, a j • v j‖ ^ 2 := by
  have e : ‖T (∑ j, a j • v j)‖ ^ 2 = ∑ j, ∑ l, a j * a l * inner ℝ (T (v j)) (T (v l)) := by
    rw [← real_inner_self_eq_norm_sq, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hterm : ∀ j l, a j * a l * inner ℝ (T (v j)) (T (v l))
      ≤ 1 / 2 * (a j ^ 2 * ε j l) + 1 / 2 * (a l ^ 2 * ε j l) := by
    intro j l
    have h1 := hε j l
    have h0 : 0 ≤ ε j l := (abs_nonneg _).trans h1
    have h2 : a j * a l * inner ℝ (T (v j)) (T (v l)) ≤ |a j * a l| * ε j l := by
      calc a j * a l * inner ℝ (T (v j)) (T (v l))
          ≤ |a j * a l * inner ℝ (T (v j)) (T (v l))| := le_abs_self _
        _ = |a j * a l| * |inner ℝ (T (v j)) (T (v l))| := abs_mul _ _
        _ ≤ |a j * a l| * ε j l := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h3 : |a j * a l| ≤ 1 / 2 * a j ^ 2 + 1 / 2 * a l ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|a j| - |a l|), sq_abs (a j), sq_abs (a l)]
    nlinarith [mul_le_mul_of_nonneg_right h3 h0]
  have hA : ∑ j, ∑ l, a j ^ 2 * ε j l ≤ D * ∑ j, a j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.mul_sum, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg _)
  have hB : ∑ j, ∑ l, a l ^ 2 * ε j l ≤ D * ∑ j, a j ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.mul_sum, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hcol l) (sq_nonneg _)
  have hsum : ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v j‖ ^ 2 / lam := by
    rw [le_div_iff₀ hlam, mul_comm]; exact hgram a
  rw [e]
  calc ∑ j, ∑ l, a j * a l * inner ℝ (T (v j)) (T (v l))
      ≤ ∑ j, ∑ l, (1 / 2 * (a j ^ 2 * ε j l) + 1 / 2 * (a l ^ 2 * ε j l)) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
    _ = 1 / 2 * ∑ j, ∑ l, a j ^ 2 * ε j l + 1 / 2 * ∑ j, ∑ l, a l ^ 2 * ε j l := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 1 / 2 * (D * ∑ j, a j ^ 2) + 1 / 2 * (D * ∑ j, a j ^ 2) := by linarith
    _ = D * ∑ j, a j ^ 2 := by ring
    _ ≤ D * (‖∑ j, a j • v j‖ ^ 2 / lam) := mul_le_mul_of_nonneg_left hsum hD
    _ = D / lam * ‖∑ j, a j • v j‖ ^ 2 := by ring

/-- **The block bound on the span of a family, from one pair bound.** `|⟪T v_j, T v_l⟫| ≤ ε` for all
pairs and a Gram lower bound `λ > 0` give `‖T x‖² ≤ (d ε / λ) ‖x‖²` on `span(v)`, `d = #κ`. -/
theorem norm_sq_le_on_span {κ : Type*} [Fintype κ] (T : E →L[ℝ] E) (v : κ → E) {ε lam : ℝ}
    (hε : ∀ j l, |inner ℝ (T (v j)) (T (v l))| ≤ ε) (hlam : 0 < lam)
    (hgram : ∀ a : κ → ℝ, lam * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v j‖ ^ 2) :
    ∀ x ∈ Submodule.span ℝ (Set.range v),
      ‖T x‖ ^ 2 ≤ (Fintype.card κ : ℝ) * ε / lam * ‖x‖ ^ 2 := by
  intro x hx
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  have hD : 0 ≤ (Fintype.card κ : ℝ) * ε := by
    rcases isEmpty_or_nonempty κ with h | h
    · simp [Fintype.card_eq_zero]
    · obtain ⟨j⟩ := h
      exact mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans (hε j j))
  have hs : ∀ j : κ, ∑ _l : κ, ε = (Fintype.card κ : ℝ) * ε := fun _ => by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact norm_sq_T_sum_le T v (fun _ _ => ε) hε hD (fun j => (hs j).le) (fun l => (hs l).le) hlam
    hgram a

/-- **`B ⊓ Aᗮ` is spanned by the projected generators of `B`**: for `A ≤ B = span S` with an orthogonal
projection on `A`, `B ⊓ Aᗮ = span {x − P_A x : x ∈ S}`. -/
theorem inf_orth_eq_span {A B : Submodule ℝ E} [A.HasOrthogonalProjection] (hAB : A ≤ B) {S : Set E}
    (hB : B = Submodule.span ℝ S) :
    B ⊓ Aᗮ = Submodule.span ℝ ((fun x => x - A.starProjection x) '' S) := by
  set Q : E →ₗ[ℝ] E := LinearMap.id - (A.starProjection : E →ₗ[ℝ] E) with hQ
  have hQx : ∀ x, Q x = x - A.starProjection x := fun x => rfl
  have himg : (fun x => x - A.starProjection x) = ⇑Q := funext fun x => (hQx x).symm
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨hyB, hyA⟩ := Submodule.mem_inf.1 hy
    have hy0 : A.starProjection y = 0 := (Submodule.starProjection_apply_eq_zero_iff (K := A)).2 hyA
    rw [himg, Submodule.span_image, ← hB]
    refine ⟨y, hyB, ?_⟩
    rw [hQx, hy0, sub_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxB : x ∈ B := hB ▸ Submodule.subset_span hx
    exact Submodule.mem_inf.2 ⟨B.sub_mem hxB (hAB (A.starProjection_apply_mem x)),
      Submodule.sub_starProjection_mem_orthogonal (K := A) x⟩

end Abstract

/-! ## 2. The loop shells are spanned by projected loop states -/

section Shells

open MassGap.RectWilson (SpT TT)

variable {i : Fin 4} {T : Dir i → ℕ} {μ : Measure (SpT i T → SUN.SU 2)}

/-- Shell `0` is the span of the loop states of size at most `R₀`. -/
theorem shell_zero_eq (Ω : (SpT i T → SUN.SU 2) → ℝ) (a : ℝ) (R : ℕ → ℝ) :
    shell μ Ω a R 0 = Submodule.span ℝ (loopSet μ Ω a (R 0)) := rfl

/-- **Shell `k + 1` is spanned by the projected loop states** `(1 − P_{H_{R_k}}) ψ_C`,
`a · len C ≤ R_{k+1}`. -/
theorem shell_succ_eq_span (Ω : (SpT i T → SUN.SU 2) → ℝ) (a : ℝ) {R : ℕ → ℝ} (hR : Monotone R)
    (k : ℕ) [(H μ Ω a (R k)).HasOrthogonalProjection] :
    shell μ Ω a R (k + 1) = Submodule.span ℝ
      ((fun x => x - (H μ Ω a (R k)).starProjection x) '' loopSet μ Ω a (R (k + 1))) := by
  show H μ Ω a (R (k + 1)) ⊓ (H μ Ω a (R k))ᗮ = _
  exact inf_orth_eq_span (H_mono Ω a (hR (Nat.le_succ k))) rfl

end Shells

/-! ## 3. The connected loop pairing on the slice -/

section Slice

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.CentreSectorSeed (Tr)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.SlabKernelOperator (kernelCLM)

/-- The `L²` vector `u = W_C φ_{g₀}`, its vacuum component `⟨W_C⟩`, and its centring the loop state. -/
theorem loopVec {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (Cl : Loop i (Tr n i)) :
    ∃ u : Lp ℝ 2 (hSN 2 n i),
      (u : Slice n i → ℝ) =ᵐ[hSN 2 n i] (fun V => Cl.wl V * φ g₀ V) ∧
      inner ℝ (vecOf (hm g₀) (hL.norm g₀)) u = vev (hSN 2 n i) (φ g₀) Cl ∧
      ((u - inner ℝ (vecOf (hm g₀) (hL.norm g₀)) u • vecOf (hm g₀) (hL.norm g₀) :
          Lp ℝ 2 (hSN 2 n i)) : Slice n i → ℝ)
        =ᵐ[hSN 2 n i] loopState (hSN 2 n i) (φ g₀) Cl := by
  have hφ := memLp_of_norm (hm g₀) (hL.norm g₀)
  have hu : MemLp (fun V => Cl.wl V * φ g₀ V) 2 (hSN 2 n i) :=
    hφ.of_le_mul (c := 2) ((continuous_wl Cl).measurable.mul (hm g₀)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun V => by
        rw [norm_mul, Real.norm_eq_abs (Cl.wl V)]
        exact mul_le_mul_of_nonneg_right (abs_wl_le Cl V) (norm_nonneg _))
  set Ω : Lp ℝ 2 (hSN 2 n i) := vecOf (hm g₀) (hL.norm g₀) with hΩdef
  set u : Lp ℝ 2 (hSN 2 n i) := hu.toLp _ with hudef
  have hv : inner ℝ Ω u = vev (hSN 2 n i) (φ g₀) Cl := by
    rw [L2.inner_def]
    unfold vev
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp, hu.coeFn_toLp] with x hx hx'
    rw [hΩdef, vecOf, hx, hudef, hx']
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  refine ⟨u, hu.coeFn_toLp, hv, ?_⟩
  filter_upwards [Lp.coeFn_sub u (inner ℝ Ω u • Ω), Lp.coeFn_smul (inner ℝ Ω u) Ω,
    hu.coeFn_toLp, hφ.coeFn_toLp] with x h1x h2x h3x h4x
  rw [h1x, Pi.sub_apply, h2x, Pi.smul_apply, smul_eq_mul, hv, hudef, h3x, hΩdef, vecOf, h4x]
  unfold loopState
  ring

/-- **The connected loop–loop pairing on the slice.** With `Ω = φ_{g₀}` and `T` the operator of
`trivKN 2 β n i` (`0 ≤ β`): for loops `C, C'` and every `m` there are `L²` vectors `u = W_C Ω`,
`u' = W_C' Ω`, `ψ = ψ_C`, `ψ' = ψ_C'` with
`⟪T^m ψ, ψ'⟫ = ⟪T^m u, u'⟫ − μ_{g₀}^m ⟨W_C⟩ ⟨W_C'⟩`. -/
theorem loopPair_centred {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C) (Cl Cl' : Loop i (Tr n i)) (m : ℕ) :
    ∃ u u' ψ ψ' : Lp ℝ 2 (hSN 2 n i),
      (u : Slice n i → ℝ) =ᵐ[hSN 2 n i] (fun V => Cl.wl V * φ g₀ V) ∧
      (u' : Slice n i → ℝ) =ᵐ[hSN 2 n i] (fun V => Cl'.wl V * φ g₀ V) ∧
      (ψ : Slice n i → ℝ) =ᵐ[hSN 2 n i] loopState (hSN 2 n i) (φ g₀) Cl ∧
      (ψ' : Slice n i → ℝ) =ᵐ[hSN 2 n i] loopState (hSN 2 n i) (φ g₀) Cl' ∧
      inner ℝ ((kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) ^ m) ψ) ψ'
        = inner ℝ ((kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) ^ m) u) u'
          - μv g₀ ^ m * vev (hSN 2 n i) (φ g₀) Cl * vev (hSN 2 n i) (φ g₀) Cl' := by
  obtain ⟨u, hu1, hv, hψ⟩ := loopVec hL hm Cl
  obtain ⟨u', hu1', hv', hψ'⟩ := loopVec hL hm Cl'
  set Ω : Lp ℝ 2 (hSN 2 n i) := vecOf (hm g₀) (hL.norm g₀) with hΩdef
  set T := kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) with hTdef
  have hsa : IsSelfAdjoint T :=
    SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i)
      (FiniteReadingFlux.symm_trivKN hβ n i)
  have hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y) := fun x y =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa x y
  have hΩ : T Ω = μv g₀ • Ω := trivKN_vecOf hL hm hkm hC0 hkb g₀
  have h1 : ‖Ω‖ = 1 := norm_vecOf (hm g₀) (hL.norm g₀)
  refine ⟨u, u', _, _, hu1, hu1', hψ, hψ', ?_⟩
  rw [inner_pow_centred hT hΩ h1 m u u', hv, hv']

end Slice

/-! ## 4. The connected transfer pairing of the periodic state -/

section Periodic

open MassGap.PeriodicState (periodicState periodicGaugeInvData periodicState_reflInvariant
  periodicState_shift)
open MassGap.LatticeReflection (ireflObs)
open MassGap.ReflectionShift (ishiftObsL)
open MassGap.FocusZoom (stateCov)

variable {N : ℕ}

/-- The transfer of the periodic data, iterated, is the iterated lattice shift on representatives. -/
theorem coe_T_pow (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)) (c : ℕ) :
    ((((periodicGaugeInvData τ p hN β).T ^ c) y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p)) : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      = (⇑(ishiftObsL τ))^[c] (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
  rw [Module.End.pow_apply]
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/-- **The periodic transfer form, polarised**: `D.form x (Tᶜ y) = ν(θx · Sᶜy)`. -/
theorem periodic_form_pair (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (c : ℕ) :
    (periodicGaugeInvData τ p hN β).form x (((periodicGaugeInvData τ p hN β).T ^ c) y)
      = periodicState hN β (ireflObs τ (2 * p) (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (⇑(ishiftObsL τ))^[c] (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := by
  rw [← coe_T_pow τ p hN β y c]
  rfl

/-- The vacuum against any element is the state's one-point function: `D.form D.vac z = ν(z)`. -/
theorem periodic_form_vac_left (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (z : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)) :
    (periodicGaugeInvData τ p hN β).form (periodicGaugeInvData τ p hN β).vac z
      = periodicState hN β (z : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
  show periodicState hN β (ireflObs τ (2 * p) (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      * (z : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = _
  rw [show ireflObs τ (2 * p) (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 from rfl,
    one_mul]

/-- **The connected transfer pairing of the periodic state is its covariance**:
`D.form x (Tᶜ y) − D.form x D.vac · D.form D.vac (Tᶜ y) = Cov_ν(θx, Sᶜy)`. -/
theorem periodic_connPair (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (c : ℕ) :
    (periodicGaugeInvData τ p hN β).form x (((periodicGaugeInvData τ p hN β).T ^ c) y)
        - (periodicGaugeInvData τ p hN β).form x (periodicGaugeInvData τ p hN β).vac
          * (periodicGaugeInvData τ p hN β).form (periodicGaugeInvData τ p hN β).vac
              (((periodicGaugeInvData τ p hN β).T ^ c) y)
      = stateCov (periodicState hN β)
          (ireflObs τ (2 * p) (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          ((⇑(ishiftObsL τ))^[c] (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := by
  rw [periodic_form_pair, MassGap.PeriodicReduce.periodic_form_vac, periodic_form_vac_left,
    coe_T_pow]
  rfl

/-- **`KernelNear` bounds the connected periodic transfer pairing**: with `KernelNear Δ (θx) δ`,
`Sᶜy` not reading `Δ` and `|Sᶜy| ≤ M`, the connected pairing is at most `2 M δ`. -/
theorem periodic_connPair_le_of_kernelNear (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (c : ℕ) (Δ : Finset MassGap.GibbsSpec.ILink) {δ M : ℝ}
    (hY : ∀ (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Δ)
      (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      (⇑(ishiftObsL τ))^[c] (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          (MassGap.GibbsSpec.splice Δ u ω)
        = (⇑(ishiftObsL τ))^[c] (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) ω)
    (hYM : ∀ ω, |(⇑(ishiftObsL τ))^[c] (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) ω|
      ≤ M)
    (hK : MassGap.BoxFocusTest.KernelNear hN β Δ
      (ireflObs τ (2 * p) (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) δ) :
    |(periodicGaugeInvData τ p hN β).form x (((periodicGaugeInvData τ p hN β).T ^ c) y)
        - (periodicGaugeInvData τ p hN β).form x (periodicGaugeInvData τ p hN β).vac
          * (periodicGaugeInvData τ p hN β).form (periodicGaugeInvData τ p hN β).vac
              (((periodicGaugeInvData τ p hN β).T ^ c) y)| ≤ 2 * M * δ := by
  rw [periodic_connPair]
  exact MassGap.BoxFocusTest.cov_le_of_kernelNear hN β Δ _ _ hY hYM hK

end Periodic

/-! ## 5. The composed theorems -/

section Compose

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.GlueballArea (ZeroFluxGap)
open MassGap.SlabKernelOperator (kernelCLM)
open MassGap.LoopZoom (diagRate zeroFluxGap_of_electricDiag)
open MassGap.PeriodicState (periodicState)
open MassGap.LatticeReflection (ireflObs)
open MassGap.ReflectionShift (ishiftObsL)
open MassGap.FocusZoom (stateCov)

/-- **The gap from uniform pair bounds on a basis of each shell.** The hypotheses of
`LoopZoom.zeroFluxGap_of_electricDiag` except its diagonal clause; for each shell `k` a finite family
`v_k` whose span contains the shell, a Gram bound `λ_k > 0`, a pair bound
`|⟪T v_kj, T v_kl⟫| ≤ e_k`, and `d_k e_k ≤ λ_k μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}` (`d_k = #κ_k`).
Then `ZeroFluxGap g₀ E (diagRate c c' σ δ t)`, `t = n · aRun 2 β`. -/
theorem zeroFluxGap_of_shellPairs {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (hgen : ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))))
    {c c' σ δ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hδ : 0 < c * σ * δ)
    (hR0 : ∀ k, 0 < R k) (hRδ : ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k)
    (κ : ℕ → Type*) [∀ k, Fintype (κ k)] (v : ∀ k, κ k → Lp ℝ 2 (hSN 2 n i))
    (hspan : ∀ k, shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k ≤ Submodule.span ℝ (Set.range (v k)))
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k)
    (hgram : ∀ k (a : κ k → ℝ), lam k * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v k j‖ ^ 2)
    (e : ℕ → ℝ)
    (he : ∀ k j l, |inner ℝ (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) (v k j))
      (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) (v k l))| ≤ e k)
    (hrate : ∀ k, (Fintype.card (κ k) : ℝ) * e k
      ≤ lam k * (μv g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))))) :
    ZeroFluxGap g₀ E (diagRate c c' σ δ ((n : ℝ) * aRun 2 β)) := by
  refine zeroFluxGap_of_electricDiag hβ hn hL hm hkm hC0 hkb hR hreach hgen hc hc' hσ hδ hR0 hRδ ?_
  intro k x hx
  have h := norm_sq_le_on_span _ (v k) (he k) (hlam k) (hgram k) x (hspan k hx)
  have hq : (Fintype.card (κ k) : ℝ) * e k / lam k
      ≤ μv g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))) := by
    rw [div_le_iff₀ (hlam k), mul_comm _ (lam k)]
    exact hrate k
  exact h.trans (mul_le_mul_of_nonneg_right hq (sq_nonneg _))

/-- **`KernelNear` at the focal boxes and the slice–periodic bridge give the gap.** As
`zeroFluxGap_of_shellPairs`, with the pair bound produced as follows. For periodic `SU(2)` observables
`X_kj`, the reflection `θ = ireflObs τ (2p)` and the shift `S^s`: for every pair, `KernelNear Δ (θ X_kj)
δ_k` at some box `Δ` that `S^s X_kl` does not read, `|S^s X_kl| ≤ M_k`; and the bridge
`|⟪T v_kj, T v_kl⟫| ≤ |Cov_ν(θ X_kj, S^s X_kl)| + η_k`, `ν = periodicState` at coupling `β`. Then the gap
holds once `d_k (2 M_k δ_k + η_k) ≤ λ_k μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}`. The bridge is a hypothesis:
no declaration relates the slice to the periodic state (module docstring, §1). `X`, `τ`, `p`, `s` are
unconstrained: at `X = 0`, `hnear` holds with `δ_k = M_k = 0` and `hbridge` is the pair bound `he` with
`e_k = η_k`, so this theorem is as strong as `zeroFluxGap_of_shellPairs`; the `KernelNear` part is
load-bearing only when `X_kj` is the periodic counterpart of `v_kj` with `η_k` small (argued). -/
theorem zeroFluxGap_of_kernelNear_bridge {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (hgen : ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))))
    {c c' σ δ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hδ : 0 < c * σ * δ)
    (hR0 : ∀ k, 0 < R k) (hRδ : ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k)
    (κ : ℕ → Type*) [∀ k, Fintype (κ k)] (v : ∀ k, κ k → Lp ℝ 2 (hSN 2 n i))
    (hspan : ∀ k, shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k ≤ Submodule.span ℝ (Set.range (v k)))
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k)
    (hgram : ∀ k (a : κ k → ℝ), lam k * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v k j‖ ^ 2)
    (X : ∀ k, κ k → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU 2), ℝ)) (τ : Fin 4) (p : ℤ) (s : ℕ)
    (η Mk δk : ℕ → ℝ)
    (hbridge : ∀ k j l,
      |inner ℝ (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) (v k j))
        (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) (v k l))|
      ≤ |stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) (ireflObs τ (2 * p) (X k j))
          ((⇑(ishiftObsL τ))^[s] (X k l))| + η k)
    (hnear : ∀ k j l, ∃ Δ : Finset MassGap.GibbsSpec.ILink,
      MassGap.BoxFocusTest.KernelNear (two_ne_zero : (2 : ℕ) ≠ 0) β Δ (ireflObs τ (2 * p) (X k j))
          (δk k) ∧
        (∀ (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU 2) Δ)
          (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 2)),
          (⇑(ishiftObsL τ))^[s] (X k l) (MassGap.GibbsSpec.splice Δ u ω)
            = (⇑(ishiftObsL τ))^[s] (X k l) ω) ∧
        ∀ ω, |(⇑(ishiftObsL τ))^[s] (X k l) ω| ≤ Mk k)
    (hrate : ∀ k, (Fintype.card (κ k) : ℝ) * (2 * Mk k * δk k + η k)
      ≤ lam k * (μv g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))))) :
    ZeroFluxGap g₀ E (diagRate c c' σ δ ((n : ℝ) * aRun 2 β)) := by
  refine zeroFluxGap_of_shellPairs hβ hn hL hm hkm hC0 hkb hR hreach hgen hc hc' hσ hδ hR0 hRδ κ v
    hspan lam hlam hgram (fun k => 2 * Mk k * δk k + η k) ?_ hrate
  intro k j l
  obtain ⟨Δ, hK, hY, hYM⟩ := hnear k j l
  have hcov := MassGap.BoxFocusTest.cov_le_of_kernelNear (two_ne_zero : (2 : ℕ) ≠ 0) β Δ _ _ hY hYM hK
  exact (hbridge k j l).trans (by linarith)

end Compose

#print axioms pow_vac
#print axioms inner_pow_centred
#print axioms norm_sq_T_sum_le
#print axioms norm_sq_le_on_span
#print axioms inf_orth_eq_span
#print axioms shell_succ_eq_span
#print axioms loopPair_centred
#print axioms periodic_form_pair
#print axioms periodic_connPair
#print axioms periodic_connPair_le_of_kernelNear
#print axioms zeroFluxGap_of_shellPairs
#print axioms zeroFluxGap_of_kernelNear_bridge

end MassGap.FocusFeed
