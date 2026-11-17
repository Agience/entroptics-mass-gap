import MassGap.PurityWeyl
import MassGap.PuritySpectralTrace
import MassGap.PurityCharacter

/-!
# MassGap.PurityTemporalOperator — the operator steps of Proposition C.1, on finite-dimensional spaces

The operator steps in the proof of Proposition C.1 (temporal spectrum comparison) of
D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and S. Singha Roy,
*Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft, 15 November 2026,
<https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`), on a
finite-dimensional inner product space. `C ≥ 0` is the convolution operator, `P` an orthogonal
projection commuting with `C` (the gauge projection `Π`), `B = C P`, `D` symmetric with
`‖D y‖² ≤ c ‖y‖²` (`c = e^{max V_s}`), and `K = D B D`.

* `pow_succ_mul`, `trace_pow_mul_comm`: `(X Y)^{T+1} = X (Y X)^T Y` and `Tr (X Y)^T = Tr (Y X)^T`,
  the trace form of the equality of the nonzero spectra of `A A*` and `A* A`.
* `sqrtOp`, `sqrtOp_apply_eigenvectorBasis`, `sqrtOp_isSymmetric`, `sqrtOp_mul_self`: for `B ≥ 0`,
  `S x = Σ_i √λ_i ⟪e_i, x⟫ e_i` is symmetric with `S S = B`; `exists_sqrt`.
* `inner_mul_proj`, `isPositive_mul_proj`, `form_proj_le`: `⟪C P x, x⟫ = ⟪C P x, P x⟫`, so
  `B = C P ≥ 0` and `B ≤ C` as forms.
* `re_trace_pow_le`: `0 ≤ X ≤ Y` as forms gives `re Tr X^T ≤ re Tr Y^T` (min–max, through
  `PurityWeyl.eigenvalues_le_add`).
* `re_trace_conj_pow_le`: `re Tr K^T ≤ c^T re Tr C^T`, through `Tr K^T = Tr (S D² S)^T` with
  `S S = B` and `S D² S ≤ c B ≤ c C` as forms.
* `temporal_trace_ratio_le`: for `A, J > 0` and `l ≥ A/J`,
  `re Tr (K/l)^T ≤ (c J)^T re Tr (C/A)^T`; with `l = λ₀(K)`, `A = a₀^M`, `J = J_s` this is (C.1)
  with right side `Tr (C/A)^T`.
* `temporal_trace_tensor`: when `C` has an orthonormal eigenbasis indexed by labels `f : Fin M → ι`
  with eigenvalues `∏_l a(f l)`, `re Tr (K/l)^T ≤ (c J)^T (Σ_{i∈ι} (a_i/a₀)^T)^M` for
  `l ≥ a₀^M/J`; with `ι` indexing a basis of one link factor (each representation `ρ` listed
  `d_ρ²` times) the right side is `(c J)^T (Σ_ρ d_ρ² (a_ρ/a₀)^T)^M`. Proved through `PuritySpectralTrace.re_trace_pow_eq_of_basis` and `PurityCharacter.tensor_sum`.
* `rayleigh_top`: for `A, J > 0`, `u ≠ 0` with `P u = u`, `C u = A u` and `w` with `D w = u`,
  `‖w‖² ≤ J ‖u‖²`, the largest eigenvalue satisfies `λ₀(K) ≥ A/J` (the test vector `D⁻¹1` of
  the paper).
* `temporal_trace_ratio_top`: under the hypotheses of both, `re Tr (K/λ₀)^T ≤ (c J)^T re Tr (C/A)^T`
  with `λ₀` the largest eigenvalue of `K`.
* `eigenvalues_conj_le`, `eigenvalues_temporal_le`: the sorted eigenvalues satisfy
  `λ_j(D B D) ≤ c μ_j(B)` for `B ≥ 0`, and `λ_j(K) ≤ c λ_j(C)` for `c ≥ 0` (through
  `PurityWeyl.exists_ne_zero_inter_map` and `PurityWeyl.eigenvalues_le_add`).
-/

namespace MassGap.PurityTemporalOperator

open LinearMap RCLike Module
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `(X Y)^{T+1} = X (Y X)^T Y`. -/
theorem pow_succ_mul (X Y : E →ₗ[𝕜] E) (T : ℕ) :
    (X * Y) ^ (T + 1) = X * (Y * X) ^ T * Y := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]

variable [FiniteDimensional 𝕜 E]

/-- `Tr (X Y)^T = Tr (Y X)^T`. -/
theorem trace_pow_mul_comm (X Y : E →ₗ[𝕜] E) (T : ℕ) :
    trace 𝕜 E ((X * Y) ^ T) = trace 𝕜 E ((Y * X) ^ T) := by
  cases T with
  | zero => simp
  | succ T =>
    rw [pow_succ_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← pow_succ']

/-- The square root of a positive `B`: `S x = Σ_i √λ_i ⟪e_i, x⟫ e_i`. -/
noncomputable def sqrtOp {B : E →ₗ[𝕜] E} (hB : B.IsPositive) : E →ₗ[𝕜] E where
  toFun x := ∑ i, ((√(hB.isSymmetric.eigenvalues rfl i) : ℝ) : 𝕜) •
    (⟪hB.isSymmetric.eigenvectorBasis rfl i, x⟫_𝕜 • hB.isSymmetric.eigenvectorBasis rfl i)
  map_add' x y := by
    simp only [inner_add_right, add_smul, smul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

/-- `S e_j = √λ_j e_j`. -/
theorem sqrtOp_apply_eigenvectorBasis {B : E →ₗ[𝕜] E} (hB : B.IsPositive)
    (j : Fin (finrank 𝕜 E)) :
    sqrtOp hB (hB.isSymmetric.eigenvectorBasis rfl j) =
      ((√(hB.isSymmetric.eigenvalues rfl j) : ℝ) : 𝕜) • hB.isSymmetric.eigenvectorBasis rfl j := by
  simp only [sqrtOp, LinearMap.coe_mk, AddHom.coe_mk, OrthonormalBasis.inner_eq_ite, ite_smul,
    one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `S` is symmetric. -/
theorem sqrtOp_isSymmetric {B : E →ₗ[𝕜] E} (hB : B.IsPositive) : (sqrtOp hB).IsSymmetric := by
  intro x y
  simp only [sqrtOp, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_conj_symm x (hB.isSymmetric.eigenvectorBasis rfl i)]
  ring

/-- `S S = B`. -/
theorem sqrtOp_mul_self {B : E →ₗ[𝕜] E} (hB : B.IsPositive) : sqrtOp hB * sqrtOp hB = B := by
  refine (hB.isSymmetric.eigenvectorBasis rfl).toBasis.ext fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, Module.End.mul_apply, sqrtOp_apply_eigenvectorBasis, map_smul,
    sqrtOp_apply_eigenvectorBasis, smul_smul, hB.isSymmetric.apply_eigenvectorBasis, ← ofReal_mul,
    Real.mul_self_sqrt (hB.nonneg_eigenvalues rfl j)]

/-- A positive `B` has a symmetric square root. -/
theorem exists_sqrt {B : E →ₗ[𝕜] E} (hB : B.IsPositive) :
    ∃ S : E →ₗ[𝕜] E, S.IsSymmetric ∧ S * S = B :=
  ⟨sqrtOp hB, sqrtOp_isSymmetric hB, sqrtOp_mul_self hB⟩

omit [FiniteDimensional 𝕜 E] in
/-- For `P` a projection commuting with `C`: `⟪C P x, x⟫ = ⟪C P x, P x⟫`. -/
theorem inner_mul_proj {C P : E →ₗ[𝕜] E} (hP : P.IsSymmetric) (hPP : P * P = P)
    (hCP : C * P = P * C) (x : E) : ⟪(C * P) x, x⟫_𝕜 = ⟪C (P x), P x⟫_𝕜 := by
  have hPz : P (x - P x) = 0 := by
    rw [map_sub, ← Module.End.mul_apply, hPP, sub_self]
  have hcomm : C (P x) = P (C x) := by
    rw [← Module.End.mul_apply, hCP, Module.End.mul_apply]
  have h1 : ⟪C (P x), x - P x⟫_𝕜 = 0 := by
    rw [hcomm, hP, hPz, inner_zero_right]
  rw [Module.End.mul_apply, ← add_zero ⟪C (P x), P x⟫_𝕜, ← h1, ← inner_add_right, add_sub_cancel]

omit [FiniteDimensional 𝕜 E] in
/-- `B = C P ≥ 0`. -/
theorem isPositive_mul_proj {C P : E →ₗ[𝕜] E} (hC : C.IsPositive) (hP : P.IsSymmetric)
    (hPP : P * P = P) (hCP : C * P = P * C) : (C * P).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have hcomm : C (P y) = P (C y) := by
      rw [← Module.End.mul_apply, hCP, Module.End.mul_apply]
    rw [Module.End.mul_apply, Module.End.mul_apply, hC.isSymmetric, hP, hcomm]
  · rw [inner_mul_proj hP hPP hCP]
    exact hC.2 (P x)

omit [FiniteDimensional 𝕜 E] in
/-- `B = C P ≤ C` as forms. -/
theorem form_proj_le {C P : E →ₗ[𝕜] E} (hC : C.IsPositive) (hP : P.IsSymmetric)
    (hPP : P * P = P) (hCP : C * P = P * C) (x : E) :
    re ⟪(C * P) x, x⟫_𝕜 ≤ re ⟪C x, x⟫_𝕜 := by
  have hPz : P (x - P x) = 0 := by
    rw [map_sub, ← Module.End.mul_apply, hPP, sub_self]
  have hcomm : C (P (x - P x)) = P (C (x - P x)) := by
    rw [← Module.End.mul_apply, hCP, Module.End.mul_apply]
  have h2 : ⟪C (x - P x), P x⟫_𝕜 = 0 := by
    rw [← hP, ← hcomm, hPz, map_zero, inner_zero_left]
  have hz : ⟪C (x - P x), x⟫_𝕜 = ⟪C (x - P x), x - P x⟫_𝕜 := by
    rw [← zero_add ⟪C (x - P x), x - P x⟫_𝕜, ← h2, ← inner_add_right, add_sub_cancel]
  have e1 : ⟪C x, x⟫_𝕜 = ⟪(C * P) x, x⟫_𝕜 + ⟪C (x - P x), x - P x⟫_𝕜 := by
    rw [← hz, Module.End.mul_apply, ← inner_add_left, ← map_add, add_sub_cancel]
  rw [e1, map_add]
  linarith [hC.2 (x - P x)]

/-- Min–max: `0 ≤ X ≤ Y` as forms gives `Tr X^T ≤ Tr Y^T`. -/
theorem re_trace_pow_le {X Y : E →ₗ[𝕜] E} (hX : X.IsPositive) (hY : Y.IsSymmetric)
    (h : ∀ x, re ⟪X x, x⟫_𝕜 ≤ re ⟪Y x, x⟫_𝕜) (T : ℕ) :
    re (trace 𝕜 E (X ^ T)) ≤ re (trace 𝕜 E (Y ^ T)) := by
  rw [PuritySpectralTrace.re_trace_pow_eq rfl hX.isSymmetric,
    PuritySpectralTrace.re_trace_pow_eq rfl hY]
  refine Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (hX.nonneg_eigenvalues rfl j) ?_ T
  have hj := PurityWeyl.eigenvalues_le_add rfl hX.isSymmetric hY (ε := 0)
    (fun x => by rw [zero_mul, add_zero]; exact h x) j
  rwa [add_zero] at hj

/-- `re Tr K^T ≤ c^T re Tr C^T` for `K = D (C P) D`. -/
theorem re_trace_conj_pow_le {C P D : E →ₗ[𝕜] E} (hC : C.IsPositive) (hP : P.IsSymmetric)
    (hPP : P * P = P) (hCP : C * P = P * C) (hD : D.IsSymmetric) {c : ℝ} (hc : 0 ≤ c)
    (hDc : ∀ y, ‖D y‖ ^ 2 ≤ c * ‖y‖ ^ 2) (T : ℕ) :
    re (trace 𝕜 E ((D * (C * P) * D) ^ T)) ≤ c ^ T * re (trace 𝕜 E (C ^ T)) := by
  have hB := isPositive_mul_proj hC hP hPP hCP
  obtain ⟨S, hS, hSS⟩ := exists_sqrt hB
  have h1 : D * (C * P) * D = D * S * (S * D) := by
    rw [← hSS]
    simp only [mul_assoc]
  have h2 : S * D * (D * S) = S * (D * D) * S := by
    simp only [mul_assoc]
  rw [h1, trace_pow_mul_comm, h2]
  have hform : ∀ x, re ⟪(S * (D * D) * S) x, x⟫_𝕜 = ‖D (S x)‖ ^ 2 := fun x => by
    simp only [Module.End.mul_apply]
    rw [hS, hD, inner_self_eq_norm_sq]
  have hBform : ∀ x, re ⟪(C * P) x, x⟫_𝕜 = ‖S x‖ ^ 2 := fun x => by
    rw [← hSS, Module.End.mul_apply, hS, inner_self_eq_norm_sq]
  have hX : (S * (D * D) * S).IsPositive := by
    refine ⟨fun x y => ?_, fun x => (hform x).symm ▸ sq_nonneg _⟩
    simp only [Module.End.mul_apply]
    rw [hS, hD, hD, hS]
  have hY : ((c : 𝕜) • (C * P)).IsSymmetric := fun x y => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      conj_ofReal, hB.isSymmetric]
  have hXY : ∀ x, re ⟪(S * (D * D) * S) x, x⟫_𝕜 ≤ re ⟪((c : 𝕜) • (C * P)) x, x⟫_𝕜 := fun x => by
    rw [LinearMap.smul_apply, inner_smul_left, conj_ofReal, re_ofReal_mul, hform, hBform]
    exact hDc (S x)
  calc re (trace 𝕜 E ((S * (D * D) * S) ^ T))
      ≤ re (trace 𝕜 E (((c : 𝕜) • (C * P)) ^ T)) := re_trace_pow_le hX hY hXY T
    _ = c ^ T * re (trace 𝕜 E ((C * P) ^ T)) := PuritySpectralTrace.re_trace_smul_pow _ _ _
    _ ≤ c ^ T * re (trace 𝕜 E (C ^ T)) :=
      mul_le_mul_of_nonneg_left
        (re_trace_pow_le hB hC.isSymmetric (form_proj_le hC hP hPP hCP) T) (pow_nonneg hc T)

/-- The operator form of (C.1): for `A, J > 0` and `l ≥ A/J`,
`Tr (K/l)^T ≤ (c J)^T Tr (C/A)^T`. -/
theorem temporal_trace_ratio_le {C P D : E →ₗ[𝕜] E} (hC : C.IsPositive) (hP : P.IsSymmetric)
    (hPP : P * P = P) (hCP : C * P = P * C) (hD : D.IsSymmetric) {c : ℝ} (hc : 0 ≤ c)
    (hDc : ∀ y, ‖D y‖ ^ 2 ≤ c * ‖y‖ ^ 2) {A J l : ℝ} (hA : 0 < A) (hJ : 0 < J)
    (hl : A / J ≤ l) (T : ℕ) :
    re (trace 𝕜 E ((((l⁻¹ : ℝ) : 𝕜) • (D * (C * P) * D)) ^ T)) ≤
      (c * J) ^ T * re (trace 𝕜 E ((((A⁻¹ : ℝ) : 𝕜) • C) ^ T)) := by
  rw [PuritySpectralTrace.re_trace_smul_pow, PuritySpectralTrace.re_trace_smul_pow]
  have hK := re_trace_conj_pow_le hC hP hPP hCP hD hc hDc T
  have hCnn : 0 ≤ re (trace 𝕜 E (C ^ T)) := by
    rw [PuritySpectralTrace.re_trace_pow_eq rfl hC.isSymmetric]
    exact Finset.sum_nonneg fun i _ => pow_nonneg (hC.nonneg_eigenvalues rfl i) T
  have hAJ : 0 < A / J := div_pos hA hJ
  have hl0 : 0 < l := hAJ.trans_le hl
  have hinv : l⁻¹ ≤ J / A := by
    have := inv_anti₀ hAJ hl
    rwa [inv_div] at this
  calc l⁻¹ ^ T * re (trace 𝕜 E ((D * (C * P) * D) ^ T))
      ≤ l⁻¹ ^ T * (c ^ T * re (trace 𝕜 E (C ^ T))) :=
        mul_le_mul_of_nonneg_left hK (pow_nonneg (inv_nonneg.2 hl0.le) T)
    _ ≤ (J / A) ^ T * (c ^ T * re (trace 𝕜 E (C ^ T))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.2 hl0.le) hinv T)
          (mul_nonneg (pow_nonneg hc T) hCnn)
    _ = (c * J) ^ T * (A⁻¹ ^ T * re (trace 𝕜 E (C ^ T))) := by
        rw [div_eq_mul_inv, mul_pow, mul_pow]
        ring

/-- The Rayleigh bound of Proposition C.1: for symmetric `D`, symmetric `K = D (C P) D`,
`A, J > 0`, `u ≠ 0` with `P u = u`, `C u = A u` and `w` with `D w = u`, `‖w‖² ≤ J ‖u‖²`, the
largest eigenvalue of `K` is at least `A/J`. -/
theorem rayleigh_top {n : ℕ} (hn : Module.finrank 𝕜 E = n) (h0 : 0 < n)
    {C P D : E →ₗ[𝕜] E} (hD : D.IsSymmetric) (hK : (D * (C * P) * D).IsSymmetric)
    {A J : ℝ} (hA : 0 < A) (hJ : 0 < J) {u w : E} (hu : u ≠ 0) (hPu : P u = u)
    (hCu : C u = (A : 𝕜) • u) (hw : D w = u) (hwJ : ‖w‖ ^ 2 ≤ J * ‖u‖ ^ 2) :
    A / J ≤ hK.eigenvalues hn ⟨0, h0⟩ := by
  set l := hK.eigenvalues hn ⟨0, h0⟩
  have hform : re ⟪(D * (C * P) * D) w, w⟫_𝕜 = A * ‖u‖ ^ 2 := by
    simp only [Module.End.mul_apply]
    rw [hD, hw, hPu, hCu, inner_smul_left, conj_ofReal, re_ofReal_mul, inner_self_eq_norm_sq]
  have htop := PurityWeyl.le_tail hn hK ⟨0, h0⟩ (x := w) fun i hi => absurd hi (Nat.not_lt_zero _)
  rw [hform] at htop
  have hu2 : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.2 hu) 2
  have hl : 0 ≤ l := by
    by_contra h
    replace h := lt_of_not_ge h
    have : l * ‖w‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
    linarith [mul_pos hA hu2]
  rw [div_le_iff₀ hJ]
  have := htop.trans (mul_le_mul_of_nonneg_left hwJ hl)
  nlinarith

/-- (C.1) in finite dimension at `l = λ₀(K)`: under the hypotheses of `temporal_trace_ratio_le`
and `rayleigh_top`, `re Tr (K/λ₀)^T ≤ (c J)^T re Tr (C/A)^T`. -/
theorem temporal_trace_ratio_top {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (h0 : 0 < n) {C P D : E →ₗ[𝕜] E} (hC : C.IsPositive) (hP : P.IsSymmetric) (hPP : P * P = P)
    (hCP : C * P = P * C) (hD : D.IsSymmetric) (hK : (D * (C * P) * D).IsSymmetric) {c : ℝ}
    (hc : 0 ≤ c) (hDc : ∀ y, ‖D y‖ ^ 2 ≤ c * ‖y‖ ^ 2) {A J : ℝ} (hA : 0 < A) (hJ : 0 < J)
    {u w : E} (hu : u ≠ 0) (hPu : P u = u) (hCu : C u = (A : 𝕜) • u) (hw : D w = u)
    (hwJ : ‖w‖ ^ 2 ≤ J * ‖u‖ ^ 2) (T : ℕ) :
    re (trace 𝕜 E (((((hK.eigenvalues hn ⟨0, h0⟩)⁻¹ : ℝ) : 𝕜) • (D * (C * P) * D)) ^ T)) ≤
      (c * J) ^ T * re (trace 𝕜 E ((((A⁻¹ : ℝ) : 𝕜) • C) ^ T)) :=
  temporal_trace_ratio_le hC hP hPP hCP hD hc hDc hA hJ
    (rayleigh_top hn h0 hD hK hA hJ hu hPu hCu hw hwJ) T

/-- The eigenvalue-wise bound: for `B ≥ 0`, symmetric `D` with `‖D y‖² ≤ c ‖y‖²` and symmetric
`K = D B D`, the sorted eigenvalues satisfy `λ_j(K) ≤ c μ_j(B)`. -/
theorem eigenvalues_conj_le {n : ℕ} (hn : Module.finrank 𝕜 E = n) {B D : E →ₗ[𝕜] E}
    (hB : B.IsPositive) (hD : D.IsSymmetric) (hK : (D * B * D).IsSymmetric) {c : ℝ}
    (hDc : ∀ y, ‖D y‖ ^ 2 ≤ c * ‖y‖ ^ 2) (j : Fin n) :
    hK.eigenvalues hn j ≤ c * hB.isSymmetric.eigenvalues hn j := by
  obtain ⟨x, hx0, h1, h2⟩ := PurityWeyl.exists_ne_zero_inter_map (hK.eigenvectorBasis hn)
    (hB.isSymmetric.eigenvectorBasis hn) D j
  have hform : re ⟪(D * B * D) x, x⟫_𝕜 = re ⟪B (D x), D x⟫_𝕜 := by
    simp only [Module.End.mul_apply]
    rw [hD]
  have hμ := hB.nonneg_eigenvalues hn j
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx0) 2
  have hhead := PurityWeyl.head_le hn hK j h1
  have htail := PurityWeyl.le_tail hn hB.isSymmetric j h2
  have hle : hK.eigenvalues hn j * ‖x‖ ^ 2 ≤ (c * hB.isSymmetric.eigenvalues hn j) * ‖x‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (hDc x) hμ]
  exact le_of_mul_le_mul_right hle hpos

/-- The eigenvalue-wise form of the comparison in Proposition C.1: for `C ≥ 0`, an orthogonal
projection `P` with `C P = P C`, symmetric `D` with `‖D y‖² ≤ c ‖y‖²`, `c ≥ 0`, and symmetric
`K = D (C P) D`, `λ_j(K) ≤ c λ_j(C)`. -/
theorem eigenvalues_temporal_le {n : ℕ} (hn : Module.finrank 𝕜 E = n) {C P D : E →ₗ[𝕜] E}
    (hC : C.IsPositive) (hP : P.IsSymmetric) (hPP : P * P = P) (hCP : C * P = P * C)
    (hD : D.IsSymmetric) (hK : (D * (C * P) * D).IsSymmetric) {c : ℝ} (hc : 0 ≤ c)
    (hDc : ∀ y, ‖D y‖ ^ 2 ≤ c * ‖y‖ ^ 2) (j : Fin n) :
    hK.eigenvalues hn j ≤ c * hC.isSymmetric.eigenvalues hn j := by
  have hB := isPositive_mul_proj hC hP hPP hCP
  have hBC := PurityWeyl.eigenvalues_le_add hn hB.isSymmetric hC.isSymmetric (ε := 0)
    (fun x => by simpa using form_proj_le hC hP hPP hCP x) j
  exact (eigenvalues_conj_le hn hB hD hK hDc j).trans
    (mul_le_mul_of_nonneg_left (by simpa using hBC) hc)

/-- (C.1) with the character sum on the right: if `C ≥ 0` has an orthonormal eigenbasis `b`
indexed by labels `f : Fin M → ι` with `C b_f = (∏_l a(f l)) b_f`, then for `a₀, J > 0` and
`l ≥ a₀^M/J`, `re Tr (K/l)^T ≤ (c J)^T (Σ_{i∈ι} (a_i/a₀)^T)^M`. With `ι` indexing a basis of one
link factor (each representation `ρ` listed `d_ρ²` times) this is
`(c J)^T (Σ_ρ d_ρ² (a_ρ/a₀)^T)^M`. -/
theorem temporal_trace_tensor {ι : Type*} [Fintype ι] {M : ℕ}
    (b : OrthonormalBasis (Fin M → ι) 𝕜 E) (a : ι → ℝ) {C P D : E →ₗ[𝕜] E} (hC : C.IsPositive)
    (hb : ∀ f, C (b f) = ((∏ l, a (f l) : ℝ) : 𝕜) • b f) (hP : P.IsSymmetric) (hPP : P * P = P)
    (hCP : C * P = P * C) (hD : D.IsSymmetric) {c : ℝ} (hc : 0 ≤ c)
    (hDc : ∀ y, ‖D y‖ ^ 2 ≤ c * ‖y‖ ^ 2) {a0 J l : ℝ} (ha0 : 0 < a0) (hJ : 0 < J)
    (hl : a0 ^ M / J ≤ l) (T : ℕ) :
    re (trace 𝕜 E ((((l⁻¹ : ℝ) : 𝕜) • (D * (C * P) * D)) ^ T)) ≤
      (c * J) ^ T * (∑ ρ, (a ρ / a0) ^ T) ^ M := by
  refine (temporal_trace_ratio_le hC hP hPP hCP hD hc hDc (pow_pos ha0 M) hJ hl T).trans_eq ?_
  rw [PuritySpectralTrace.re_trace_smul_pow, PuritySpectralTrace.re_trace_pow_eq_of_basis b hb,
    ← PurityCharacter.tensor_sum Finset.univ a a0 M T, Fintype.piFinset_univ, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [div_eq_mul_inv, mul_pow, mul_comm]

end MassGap.PurityTemporalOperator

#print axioms MassGap.PurityTemporalOperator.pow_succ_mul
#print axioms MassGap.PurityTemporalOperator.trace_pow_mul_comm
#print axioms MassGap.PurityTemporalOperator.sqrtOp_apply_eigenvectorBasis
#print axioms MassGap.PurityTemporalOperator.sqrtOp_isSymmetric
#print axioms MassGap.PurityTemporalOperator.sqrtOp_mul_self
#print axioms MassGap.PurityTemporalOperator.exists_sqrt
#print axioms MassGap.PurityTemporalOperator.inner_mul_proj
#print axioms MassGap.PurityTemporalOperator.isPositive_mul_proj
#print axioms MassGap.PurityTemporalOperator.form_proj_le
#print axioms MassGap.PurityTemporalOperator.re_trace_pow_le
#print axioms MassGap.PurityTemporalOperator.re_trace_conj_pow_le
#print axioms MassGap.PurityTemporalOperator.temporal_trace_ratio_le
#print axioms MassGap.PurityTemporalOperator.rayleigh_top
#print axioms MassGap.PurityTemporalOperator.temporal_trace_ratio_top
#print axioms MassGap.PurityTemporalOperator.temporal_trace_tensor
#print axioms MassGap.PurityTemporalOperator.eigenvalues_conj_le
#print axioms MassGap.PurityTemporalOperator.eigenvalues_temporal_le
