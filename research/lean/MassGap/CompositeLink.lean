import Mathlib
import MassGap.NonGaussLink

/-!
# MassGap.CompositeLink — the composites in the observer's space, from kernels

`NonGaussLink.clayStatementAt_SU_ng` takes a family `wC` of vectors of the pre-observer's space
`preH` (the flowed reconstruction `FlowH` of `energy0 W (SymPlaqClass N)`), `hLC : LinkCPre …` (Gram
matrix `kernC`, dyadic shift, vacuum) and `hX` (convergence of the sector's mixed reading `mixLatT`,
and `⟪wOfC eI wC P, preCvec Q⟫ = mixT`). This module replaces those three inputs by statements about
limit kernels only (`clayStatementAt_SU_link`), and proves the joint positivity among them necessary
(`jointRPK_of_vectors`).

## 1. Vectors from two kernels and a cross kernel (any complex inner product space)

Data: a family `v : M → H` with real Gram matrix `G`, a kernel `Kc : I → I → ℝ` and a cross kernel
`X : I → M → ℝ`. `jointQ P P' t c` is the value at `e_P + t e_{P'} − ∑ c_Q v_Q` of the form with those
blocks; `JointRP` is its non-negativity; `dist2 P c = jointQ P P 0 c`; `Approx` asks
`inf_c dist2 P c = 0`.

* `pairing_sq_le`: `JointRP` gives `X(P,c)² ≤ Kc(P,P) ‖∑ c_Q v_Q‖²` (the mixed Cauchy–Schwarz bound).
* `exists_link`: in a complete space, `JointRP ∧ Approx` give `w : I → H` with
  `⟪w P, v Q⟫ = X(P,Q)` and `⟪w P, w P'⟫ = Kc(P,P')` (`w P` the limit of approximants: they are
  Cauchy by the parallelogram bound `norm_sub_sq_le`).
* `jointRP_of_link`, `dist2_eq`, `approx_iff`: conversely, for any such `w`, `JointRP` holds,
  `dist2 P c = ‖w P − ∑ c_Q v_Q‖²`, and `Approx` holds iff every `w P` lies in the closure of the real
  combinations of `v`.
* `eq_of_inner_eq`: a vector is determined by its pairings with a family whose span is dense.

## 2. Kernel form

`JointRPK`, `ApproxK`: `JointRP`, `Approx` with `‖∑ c_Q v_Q‖²` written as `gForm G c c`
(`norm_yL_sq`, `jointRP_iff_K`, `approx_iff_K`).

## 3. The composites' mixed reading

* `mixLatC`, `mixKC`: the composites of `P` reflected, the observer's fields of `Q` flowed, read in
  `stateK hN k`; `mixKC P Q = sgnC P · lim_ultra mixLatC`.
* `mixLatT_eq_sum`, `prod_reflC`, `tendsto_mixLatT`: at every step the sector's mixed reading is the
  combination `∑_α ∏ᵢ cᵢ(αᵢ) sgnC(P_α) mixLatC(P_α, Q)` (no hypothesis beyond the two clauses of
  `TIn`); if the composites' readings at the components converge, `mixLatT → ∑_α ∏ᵢ cᵢ(αᵢ) mixKC(P_α, Q)`.
* `mixKC_shift`: `mixKC(T_m P, Q) = mixKC(P, T_m Q)` (lattice translation invariance of the periodic
  state, from step `m` on). `mixKC_empty`: `mixKC(∅, Q) = kernF(∅, Q)`.
* `adm_pairC`: `ΘP ∪ Q` of composites is admissible, so `CompOS` gives the convergence clause of
  `LinkCPre`.
* `mixConv_of_bounded`: an eventual bound on a mixed reading gives its convergence along `ultra`.
* `tendsto_abs_z_atTop`: `z_c(k) a_k⁴ → 2` forces `|z_c(k)| → ∞`.

## 4. The capstone

* `linkCPre_of_kernels`: from `CompOS`, `MixConv` (convergence of the composites' mixed readings at
  every composite monomial and every margin monomial), `JointRPK` and `ApproxK` for the blocks `kernC`, `mixK`, `gramF`, a family
  `wC` in `preH` with `LinkCPre` and both conjuncts of `hX`. The shift and the vacuum clauses are
  proved, by `eq_of_inner_eq` with the density of the span of `gvecT` (`obsGen_flow`),
  `mixKC_shift`, `mixKC_empty` and the self-adjointness of `timeT`.
* `clayStatementAt_SU_link`: `clayStatementAt_SU_ng` with `wC`, `hLC`, `hX` replaced by `hJ`, `hA`,
  `hMC`.
* `jointRPK_of_vectors`: `JointRPK` holds for every family `wC` of `preH` with cross pairings `mixK`
  and Gram matrix `kernC`; it is necessary.

## What is not proved here

* `MixConv` is not a consequence of the uniform bounds: the composites' coefficients carry
  `z_c(k)`, which diverges (`tendsto_abs_z_atTop`), while the bare readings are bounded uniformly in
  `k`. ARGUED: an eventual bound (hence `MixConv`, `mixConv_of_bounded`) would follow from the lattice
  Cauchy–Schwarz inequality `mixLatC(P,Q)² ≤ latC(ΘP ∪ P) · latSF(ΘQ ∪ Q)` of the reflection-positive
  periodic state, which needs the reflected composite `cField` with reflected test function to be
  `±` the lattice reflection of the composite (a reflection covariance of the bare fields not stated
  in the tree), together with the convergence of `latC(ΘP ∪ P)` (`CompOS`, `adm_pairC`) and the flowed
  uniform bound.
* `JointRPK`: ARGUED to follow, by the same reflection covariance, from `stateK_rp` applied to
  `sA_P + tA_{P'} − ∑ c_Q B_Q` at each step and the convergence of all three blocks.
* `ApproxK` carries the content: each composite's continuum vector is a limit of the observer's
  flowed vectors in the joint form. By `approx_iff` it is equivalent, for vectors with the cross
  pairings and the Gram matrix, to membership in the closure of the real span of `gvecT`. ARGUED:
  in `preH` that closure is the whole real part of the space (the span of `gvecT` is dense,
  `obsGen_flow`, and its Gram matrix is real), so for vectors of `preH` with real cross pairings
  `ApproxK` is automatic; `ApproxK` is thus exactly the statement that the composites have vectors in
  the observer's space at all.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the signs and the empty length; `1` the unit step and the unit
coefficient; `2` the cross-term factor, the square and the limit of the channel factors; `4` the
dimension.
-/

noncomputable section

namespace MassGap.CompositeLink

open Filter
open scoped Topology

/-! ## 1. Vectors from two kernels and a cross kernel -/

section Generic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {M I : Type}

/-- **The real combination** `∑_Q c_Q v_Q` of a family of vectors. DERIVED: no numeral. -/
def yL (v : M → H) (c : M →₀ ℝ) : H := c.sum fun Q a => (a : ℂ) • v Q

/-- **The real pairing** `∑_Q c_Q g(Q)`. DERIVED: no numeral. -/
def xL (g : M → ℝ) (c : M →₀ ℝ) : ℝ := c.sum fun Q a => a * g Q

/-- DERIVED: no numeral. -/
theorem yL_add (v : M → H) (c d : M →₀ ℝ) : yL v (c + d) = yL v c + yL v d := by
  unfold yL
  exact Finsupp.sum_add_index' (fun Q => by simp)
    (fun Q a b => by rw [Complex.ofReal_add, add_smul])

/-- DERIVED: no numeral. -/
theorem yL_smul (v : M → H) (t : ℝ) (c : M →₀ ℝ) : yL v (t • c) = (t : ℂ) • yL v c := by
  unfold yL
  rw [Finsupp.sum_smul_index' (fun Q => by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun Q _ => ?_
  rw [smul_eq_mul, Complex.ofReal_mul, mul_smul]

/-- DERIVED: no numeral. -/
theorem yL_single (v : M → H) (Q : M) (a : ℝ) : yL v (Finsupp.single Q a) = (a : ℂ) • v Q := by
  unfold yL
  exact Finsupp.sum_single_index (by simp)

/-- DERIVED: no numeral. -/
theorem xL_add (g : M → ℝ) (c d : M →₀ ℝ) : xL g (c + d) = xL g c + xL g d := by
  unfold xL
  exact Finsupp.sum_add_index' (fun Q => by simp) (fun Q a b => add_mul a b (g Q))

/-- DERIVED: no numeral. -/
theorem xL_smul (g : M → ℝ) (t : ℝ) (c : M →₀ ℝ) : xL g (t • c) = t * xL g c := by
  unfold xL
  rw [Finsupp.sum_smul_index' (fun Q => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun Q _ => ?_
  rw [smul_eq_mul, mul_assoc]

/-- DERIVED: no numeral. -/
theorem xL_single (g : M → ℝ) (Q : M) (a : ℝ) : xL g (Finsupp.single Q a) = a * g Q := by
  unfold xL
  exact Finsupp.sum_single_index (by simp)

/-- `⟪∑ c_Q v_Q, w⟫ = ∑ c_Q g(Q)` when every `⟪v_Q, w⟫ = g(Q)` is real. DERIVED: no numeral. -/
theorem inner_yL_left (v : M → H) (c : M →₀ ℝ) (w : H) (g : M → ℝ)
    (hg : ∀ Q, inner ℂ (v Q) w = (g Q : ℂ)) : inner ℂ (yL v c) w = (xL g c : ℂ) := by
  unfold yL xL Finsupp.sum
  rw [sum_inner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [inner_smul_left, Complex.conj_ofReal, hg, Complex.ofReal_mul]

/-- `⟪w, ∑ c_Q v_Q⟫ = ∑ c_Q g(Q)` when every `⟪w, v_Q⟫ = g(Q)` is real. DERIVED: no numeral. -/
theorem inner_yL_right (v : M → H) (c : M →₀ ℝ) (w : H) (g : M → ℝ)
    (hg : ∀ Q, inner ℂ w (v Q) = (g Q : ℂ)) : inner ℂ w (yL v c) = (xL g c : ℂ) := by
  unfold yL xL Finsupp.sum
  rw [inner_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [inner_smul_right, hg, Complex.ofReal_mul]

/-- **The discriminant bound**: `C + 2tB + t²A ≥ 0` for all real `t` gives `B² ≤ AC`.

DERIVED: `2`, `4` the coefficients of the discriminant. -/
theorem sq_le_of_quad {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ C + 2 * t * B + t ^ 2 * A) :
    B ^ 2 ≤ A * C := by
  have hd := discrim_le_zero (a := A) (b := 2 * B) (c := C) fun x => by
    have e : A * (x * x) + 2 * B * x + C = C + 2 * x * B + x ^ 2 * A := by ring
    rw [e]
    exact h x
  unfold discrim at hd
  have e2 : (2 * B) ^ 2 = 4 * B ^ 2 := by ring
  linarith

/-- `Bₙ² ≤ A dₙ` with `dₙ → 0` gives `Bₙ → 0`. DERIVED: `0` the limit; `2` the square. -/
theorem tendsto_zero_of_sq_le {B d : ℕ → ℝ} {A : ℝ} (h : ∀ n, B n ^ 2 ≤ A * d n)
    (hd : Tendsto d atTop (𝓝 0)) : Tendsto B atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => A * d n) atTop (𝓝 0) := by simpa using hd.const_mul A
  have h2 : Tendsto (fun n => Real.sqrt (A * d n)) atTop (𝓝 0) := by
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h3
    exact h3
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt (h n)) h2

/-- **The joint reflection form at two composites**: the value at `e_P + t e_{P'} − ∑ c_Q v_Q` of the
form with blocks `Kc` (composites), `X` (composite × observer) and the Gram matrix of `v`:
`Kc(P,P) + 2t Kc(P,P') + t² Kc(P',P') − 2 X(P,c) − 2t X(P',c) + ‖∑ c_Q v_Q‖²`.

DERIVED: `2` the cross-term factor and the square. -/
def jointQ (Kc : I → I → ℝ) (X : I → M → ℝ) (v : M → H) (P P' : I) (t : ℝ) (c : M →₀ ℝ) : ℝ :=
  Kc P P + 2 * t * Kc P P' + t ^ 2 * Kc P' P' - 2 * xL (X P) c - 2 * t * xL (X P') c
    + ‖yL v c‖ ^ 2

/-- **Joint reflection positivity**: `jointQ ≥ 0` at all composites `P, P'`, all real `t` and all
finite real combinations `c` of the observer's vectors. DERIVED: `0` the sign. -/
def JointRP (Kc : I → I → ℝ) (X : I → M → ℝ) (v : M → H) : Prop :=
  ∀ (P P' : I) (t : ℝ) (c : M →₀ ℝ), 0 ≤ jointQ Kc X v P P' t c

/-- **The joint distance** `Kc(P,P) − 2 X(P,c) + ‖∑ c_Q v_Q‖²` of the composite `P` from the
combination `c` (`jointQ` at `P' = P`, `t = 0`). DERIVED: `2` the cross-term factor and the square. -/
def dist2 (Kc : I → I → ℝ) (X : I → M → ℝ) (v : M → H) (P : I) (c : M →₀ ℝ) : ℝ :=
  Kc P P - 2 * xL (X P) c + ‖yL v c‖ ^ 2

/-- **Approximability**: every composite is at joint distance at most `ε` from some finite real
combination of the observer's vectors, for every `ε > 0`. DERIVED: `0` the sign of `ε`. -/
def Approx (Kc : I → I → ℝ) (X : I → M → ℝ) (v : M → H) : Prop :=
  ∀ (P : I) (ε : ℝ), 0 < ε → ∃ c : M →₀ ℝ, dist2 Kc X v P c ≤ ε

variable {Kc : I → I → ℝ} {X : I → M → ℝ} {v : M → H}

/-- DERIVED: `0` the value of `t`. -/
theorem jointQ_zero (P : I) (c : M →₀ ℝ) : jointQ Kc X v P P 0 c = dist2 Kc X v P c := by
  unfold jointQ dist2
  ring

/-- DERIVED: `0` the sign. -/
theorem dist2_nonneg (hJ : JointRP Kc X v) (P : I) (c : M →₀ ℝ) : 0 ≤ dist2 Kc X v P c := by
  rw [← jointQ_zero]
  exact hJ P P 0 c

/-- **The mixed Cauchy–Schwarz bound** `X(P,c)² ≤ Kc(P,P) ‖∑ c_Q v_Q‖²`, from `JointRP`. This is the
boundedness of `c ↦ X(P,c)` in the observer's Gram norm, which makes the Riesz vector of `P` exist
in the closed span of `v`.

DERIVED: `0` the excluded scale; `2` the square. -/
theorem pairing_sq_le (hJ : JointRP Kc X v) (P : I) (c : M →₀ ℝ) :
    xL (X P) c ^ 2 ≤ Kc P P * ‖yL v c‖ ^ 2 := by
  have h := sq_le_of_quad (A := Kc P P) (B := - xL (X P) c) (C := ‖yL v c‖ ^ 2) fun t => by
    have h0 := hJ P P 0 (t⁻¹ • c)
    rcases eq_or_ne t 0 with rfl | ht
    · nlinarith [sq_nonneg ‖yL v c‖]
    · unfold jointQ at h0
      rw [xL_smul, yL_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at h0
      have ht2 : 0 < t ^ 2 := by positivity
      have hts : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
      have key : ‖yL v c‖ ^ 2 + 2 * t * -xL (X P) c + t ^ 2 * Kc P P
          = t ^ 2 * (Kc P P + 2 * 0 * Kc P P + 0 ^ 2 * Kc P P - 2 * (t⁻¹ * xL (X P) c)
            - 2 * 0 * (t⁻¹ * xL (X P) c) + t⁻¹ ^ 2 * ‖yL v c‖ ^ 2) := by
        linear_combination (2 * t * xL (X P) c - ‖yL v c‖ ^ 2 * (1 + t * t⁻¹)) * hts
      rw [key]
      exact mul_nonneg ht2.le h0
  simpa [neg_sq] using h

/-- **The parallelogram bound**: `‖yL c − yL d‖² ≤ 2 (dist2 P c + dist2 P d)`, from `JointRP` at the
midpoint. DERIVED: `1/2` the midpoint; `1/4` its square; `2` the parallelogram constant. -/
theorem norm_sub_sq_le (hJ : JointRP Kc X v) (P : I) (c d : M →₀ ℝ) :
    ‖yL v c - yL v d‖ ^ 2 ≤ 2 * (dist2 Kc X v P c + dist2 Kc X v P d) := by
  have hm := dist2_nonneg hJ P ((1 / 2 : ℝ) • (c + d))
  have hy : yL v ((1 / 2 : ℝ) • (c + d)) = ((1 / 2 : ℝ) : ℂ) • (yL v c + yL v d) := by
    rw [yL_smul, yL_add]
  have hx : xL (X P) ((1 / 2 : ℝ) • (c + d)) = 1 / 2 * (xL (X P) c + xL (X P) d) := by
    rw [xL_smul, xL_add]
  have hn : ‖((1 / 2 : ℝ) : ℂ) • (yL v c + yL v d)‖ ^ 2 = 1 / 4 * ‖yL v c + yL v d‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow]
    norm_num
  have hp := parallelogram_law_with_norm ℂ (yL v c) (yL v d)
  unfold dist2 at hm ⊢
  rw [hy, hx, hn] at hm
  linarith

/-- Approximants with `dist2 → 0`. DERIVED: `1` the shift in `1/(n+1)`; `0` the limit. -/
theorem exists_seq (hJ : JointRP Kc X v) (hA : Approx Kc X v) (P : I) :
    ∃ c : ℕ → (M →₀ ℝ), Tendsto (fun n => dist2 Kc X v P (c n)) atTop (𝓝 0) := by
  choose c hc using fun n : ℕ => hA P (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  exact ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => dist2_nonneg hJ P (c n)) hc⟩

/-- The approximants' vectors are Cauchy. DERIVED: `2`, `4` from `norm_sub_sq_le`. -/
theorem cauchySeq_yL (hJ : JointRP Kc X v) (P : I) (c : ℕ → (M →₀ ℝ))
    (hc : Tendsto (fun n => dist2 Kc X v P (c n)) atTop (𝓝 0)) :
    CauchySeq (fun n => yL v (c n)) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hε2 : (0 : ℝ) < ε ^ 2 / 4 := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hc.eventually (gt_mem_nhds hε2))
  refine ⟨K, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have h1 := norm_sub_sq_le hJ P (c n) (c K)
  have h2 := hK n hn
  have h3 := hK K le_rfl
  have h4 : ‖yL v (c n) - yL v (c K)‖ ^ 2 < ε ^ 2 := by linarith
  nlinarith [norm_nonneg (yL v (c n) - yL v (c K))]

/-- **The limit pairs with the observer by `X`**: `⟪w, v_Q⟫ = X(P,Q)`, from `JointRP` at `c + t δ_Q`
and the real Gram matrix `G` of `v`. DERIVED: `1` the unit coefficient of `δ_Q`; `2` the square. -/
theorem pairing_of_seq (hJ : JointRP Kc X v) (G : M → M → ℝ)
    (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ)) (P : I) (c : ℕ → (M →₀ ℝ))
    (hc : Tendsto (fun n => dist2 Kc X v P (c n)) atTop (𝓝 0)) (w : H)
    (hw : Tendsto (fun n => yL v (c n)) atTop (𝓝 w)) (Q : M) :
    inner ℂ w (v Q) = (X P Q : ℂ) := by
  have hy : ∀ n, inner ℂ (yL v (c n)) (v Q) = (xL (fun Q' => G Q' Q) (c n) : ℂ) :=
    fun n => inner_yL_left v (c n) (v Q) (fun Q' => G Q' Q) (fun Q' => hG Q' Q)
  have hvv : ‖v Q‖ ^ 2 = G Q Q := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hG, RCLike.re_to_complex, Complex.ofReal_re]
  have hq : ∀ n, (xL (fun Q' => G Q' Q) (c n) - X P Q) ^ 2 ≤ G Q Q * dist2 Kc X v P (c n) := by
    intro n
    refine sq_le_of_quad fun t => ?_
    have h0 := dist2_nonneg hJ P (c n + t • Finsupp.single Q 1)
    unfold dist2 at h0 ⊢
    rw [xL_add, xL_smul, xL_single, yL_add, yL_smul, yL_single, Complex.ofReal_one, one_smul,
      norm_add_sq (𝕜 := ℂ), inner_smul_right, hy, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, hvv] at h0
    have hre : RCLike.re ((t : ℂ) * (xL (fun Q' => G Q' Q) (c n) : ℂ))
        = t * xL (fun Q' => G Q' Q) (c n) := by
      rw [RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre] at h0
    nlinarith [h0]
  have hB := tendsto_zero_of_sq_le hq hc
  have hx : Tendsto (fun n => xL (fun Q' => G Q' Q) (c n)) atTop (𝓝 (X P Q)) := by
    have := hB.add_const (X P Q)
    simpa using this
  have h1 : Tendsto (fun n => inner ℂ (yL v (c n)) (v Q)) atTop (𝓝 (X P Q : ℂ)) := by
    simp only [hy]
    exact (Complex.continuous_ofReal.tendsto _).comp hx
  exact tendsto_nhds_unique (hw.inner tendsto_const_nhds) h1

/-- **The limits have Gram matrix `Kc`**: `⟪w_P, w_{P'}⟫ = Kc(P,P')`, from `JointRP` at two composites.

DERIVED: no numeral. -/
theorem gram_of_seq (hJ : JointRP Kc X v) (P P' : I) (c : ℕ → (M →₀ ℝ))
    (hc : Tendsto (fun n => dist2 Kc X v P (c n)) atTop (𝓝 0)) (w w' : H)
    (hw : Tendsto (fun n => yL v (c n)) atTop (𝓝 w))
    (hw' : ∀ Q, inner ℂ w' (v Q) = (X P' Q : ℂ)) :
    inner ℂ w w' = (Kc P P' : ℂ) := by
  have hy : ∀ n, inner ℂ (yL v (c n)) w' = (xL (X P') (c n) : ℂ) := fun n =>
    inner_yL_left v (c n) w' (X P') fun Q => by
      rw [← inner_conj_symm, hw' Q, Complex.conj_ofReal]
  have hq : ∀ n, (Kc P P' - xL (X P') (c n)) ^ 2 ≤ Kc P' P' * dist2 Kc X v P (c n) := by
    intro n
    refine sq_le_of_quad fun t => ?_
    have h0 := hJ P P' t (c n)
    unfold jointQ at h0
    unfold dist2
    nlinarith [h0]
  have hB := tendsto_zero_of_sq_le hq hc
  have hx : Tendsto (fun n => xL (X P') (c n)) atTop (𝓝 (Kc P P')) := by
    have := (hB.neg).add_const (Kc P P')
    simpa using this
  have h1 : Tendsto (fun n => inner ℂ (yL v (c n)) w') atTop (𝓝 (Kc P P' : ℂ)) := by
    simp only [hy]
    exact (Complex.continuous_ofReal.tendsto _).comp hx
  exact tendsto_nhds_unique (hw.inner tendsto_const_nhds) h1

/-- **Vectors from two kernels and a cross kernel.** In a complete space, with `v` of real Gram matrix
`G`, `JointRP` and `Approx` give vectors `w P` with `⟪w P, v Q⟫ = X(P,Q)` and `⟪w P, w P'⟫ = Kc(P,P')`;
`w P` is the limit of approximants of `Approx`.

DERIVED: no numeral. -/
theorem exists_link [CompleteSpace H] (G : M → M → ℝ)
    (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ)) (hJ : JointRP Kc X v)
    (hA : Approx Kc X v) :
    ∃ w : I → H, (∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ))
      ∧ ∀ P P', inner ℂ (w P) (w P') = (Kc P P' : ℂ) := by
  choose c hc using exists_seq hJ hA
  choose w hw using fun P => cauchySeq_tendsto_of_complete (cauchySeq_yL hJ P (c P) (hc P))
  have hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ) :=
    fun P Q => pairing_of_seq hJ G hG P (c P) (hc P) (w P) (hw P) Q
  exact ⟨w, hX, fun P P' => gram_of_seq hJ P P' (c P) (hc P) (w P) (w P') (hw P) (hX P')⟩

/-- **The joint form is a squared norm** when vectors `w` with cross pairings `X` and Gram matrix
`Kc` exist: `jointQ P P' t c = ‖w P + t w P' − ∑ c_Q v_Q‖²`. DERIVED: `2` the square. -/
theorem jointQ_eq (w : I → H) (hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ))
    (hK : ∀ P P', inner ℂ (w P) (w P') = (Kc P P' : ℂ)) (P P' : I) (t : ℝ) (c : M →₀ ℝ) :
    jointQ Kc X v P P' t c = ‖w P + (t : ℂ) • w P' - yL v c‖ ^ 2 := by
  have hn : ∀ P, ‖w P‖ ^ 2 = Kc P P := fun P => by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hK, RCLike.re_to_complex, Complex.ofReal_re]
  have h1 : RCLike.re (inner ℂ (w P) ((t : ℂ) • w P')) = t * Kc P P' := by
    rw [RCLike.re_to_complex, inner_smul_right, hK, Complex.re_ofReal_mul, Complex.ofReal_re]
  have h2 : RCLike.re (inner ℂ (w P + (t : ℂ) • w P') (yL v c))
      = xL (X P) c + t * xL (X P') c := by
    rw [RCLike.re_to_complex, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      inner_yL_right v c (w P) (X P) (hX P), inner_yL_right v c (w P') (X P') (hX P'),
      Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), h1, h2,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hn, hn]
  unfold jointQ
  ring

/-- **`JointRP` is necessary** for vectors with cross pairings `X` and Gram matrix `Kc`.
DERIVED: no numeral. -/
theorem jointRP_of_link (w : I → H) (hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ))
    (hK : ∀ P P', inner ℂ (w P) (w P') = (Kc P P' : ℂ)) : JointRP Kc X v :=
  fun P P' t c => by
    rw [jointQ_eq w hX hK]
    positivity

/-- `dist2 P c = ‖w P − ∑ c_Q v_Q‖²`. DERIVED: `2` the square. -/
theorem dist2_eq (w : I → H) (hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ))
    (hK : ∀ P P', inner ℂ (w P) (w P') = (Kc P P' : ℂ)) (P : I) (c : M →₀ ℝ) :
    dist2 Kc X v P c = ‖w P - yL v c‖ ^ 2 := by
  rw [← jointQ_zero, jointQ_eq w hX hK]
  simp

/-- **`Approx` is membership in the closure of the real span**: for vectors with cross pairings `X`
and Gram matrix `Kc`, `Approx` holds iff every `w P` lies in the closure of the set of real
combinations of `v`. DERIVED: `2` the square; `1` the cap on the radius. -/
theorem approx_iff (w : I → H) (hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ))
    (hK : ∀ P P', inner ℂ (w P) (w P') = (Kc P P' : ℂ)) :
    Approx Kc X v ↔ ∀ P, w P ∈ closure (Set.range (yL v)) := by
  constructor
  · intro hA P
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨c, hc⟩ := hA P (ε ^ 2 / 2) (by positivity)
    rw [dist2_eq w hX hK] at hc
    refine ⟨yL v c, ⟨c, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have h4 : ‖w P - yL v c‖ ^ 2 < ε ^ 2 := by nlinarith
    nlinarith [norm_nonneg (w P - yL v c)]
  · intro h P ε hε
    have hδ : 0 < min ε 1 := lt_min hε one_pos
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := Metric.mem_closure_iff.mp (h P) (min ε 1) hδ
    refine ⟨c, ?_⟩
    rw [dist2_eq w hX hK]
    rw [dist_eq_norm] at hc
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    have h2 : min ε 1 ≤ 1 := min_le_right _ _
    nlinarith [norm_nonneg (w P - yL v c)]

/-- **A vector is determined by its pairings with a family of dense span.** DERIVED: `0` the
vanishing pairing. -/
theorem eq_of_inner_eq (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) {x y : H}
    (h : ∀ Q, inner ℂ x (v Q) = inner ℂ y (v Q)) : x = y := by
  set f : H →L[ℂ] ℂ := innerSL ℂ (x - y) with hf
  have hsub : Submodule.span ℂ (Set.range v) ≤ f.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨Q, rfl⟩
    show v Q ∈ f.ker
    rw [LinearMap.mem_ker]
    show f (v Q) = 0
    rw [hf, innerSL_apply_apply, inner_sub_left, h Q, sub_self]
  have hcl := Submodule.topologicalClosure_minimal _ hsub f.isClosed_ker
  rw [hd] at hcl
  have hxy : x - y ∈ f.ker := hcl Submodule.mem_top
  rw [LinearMap.mem_ker] at hxy
  have hxy' : f (x - y) = 0 := hxy
  rw [hf, innerSL_apply_apply, inner_self_eq_zero, sub_eq_zero] at hxy'
  exact hxy'

end Generic

/-! ## 2. The kernel form of the joint positivity -/

section KernelForm

open MassGap.ContinuumFlow

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {M I : Type}

/-- **The joint reflection form at two composites, from kernels**: `jointQ` with `‖∑ c_Q v_Q‖²`
replaced by `gForm G c c = ∑_{Q,Q'} c_Q c_{Q'} G(Q, Q')`.

DERIVED: `2` the cross-term factor and the square. -/
def JointRPK (Kc : I → I → ℝ) (X : I → M → ℝ) (G : M → M → ℝ) : Prop :=
  ∀ (P P' : I) (t : ℝ) (c : M →₀ ℝ),
    0 ≤ Kc P P + 2 * t * Kc P P' + t ^ 2 * Kc P' P' - 2 * xL (X P) c - 2 * t * xL (X P') c
      + gForm G c c

/-- **Approximability from kernels**: `dist2` with `‖∑ c_Q v_Q‖²` replaced by `gForm G c c`.

DERIVED: `2` the cross-term factor; `0` the sign of `ε`. -/
def ApproxK (Kc : I → I → ℝ) (X : I → M → ℝ) (G : M → M → ℝ) : Prop :=
  ∀ (P : I) (ε : ℝ), 0 < ε → ∃ c : M →₀ ℝ, Kc P P - 2 * xL (X P) c + gForm G c c ≤ ε

/-- **`‖∑ c_Q v_Q‖² = gForm G c c`** when the Gram matrix of `v` is the real kernel `G`.

DERIVED: `2` the square. -/
theorem norm_yL_sq {v : M → H} (G : M → M → ℝ)
    (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ)) (c : M →₀ ℝ) :
    ‖yL v c‖ ^ 2 = gForm G c c := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_yL_left v c (yL v c) (fun Q => xL (G Q) c)
      (fun Q => inner_yL_right v c (v Q) (G Q) (fun Q' => hG Q Q')),
    RCLike.re_to_complex, Complex.ofReal_re]
  unfold xL gForm
  refine Finsupp.sum_congr fun Q _ => ?_
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun Q' _ => by ring

variable {Kc : I → I → ℝ} {X : I → M → ℝ} {v : M → H}

/-- `JointRPK` is `JointRP` when the Gram matrix of `v` is `G`. DERIVED: no numeral. -/
theorem jointRP_iff_K (G : M → M → ℝ) (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ)) :
    JointRP Kc X v ↔ JointRPK Kc X G := by
  unfold JointRP JointRPK jointQ
  simp only [norm_yL_sq G hG, iff_self]

/-- `ApproxK` is `Approx` when the Gram matrix of `v` is `G`. DERIVED: no numeral. -/
theorem approx_iff_K (G : M → M → ℝ) (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ)) :
    Approx Kc X v ↔ ApproxK Kc X G := by
  unfold Approx ApproxK dist2
  simp only [norm_yL_sq G hG, iff_self]

end KernelForm

/-! ## 3. The composites' mixed reading -/

section Mixed

variable {N : ℕ}

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumReconstruction MassGap.ObserverSymField
  MassGap.ClayStatement MassGap.ClayWiring

/-- **The mixed lattice reading of the composites** at step `k`: the composites of `P` reflected
(test functions reflected, connected renormalised fields `cField` unchanged), the fields of `Q`
flowed by `Φ`, read in `stateK hN k`.

DERIVED: no numeral. -/
def mixLatC (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (k : ℕ) (P : TMonoG C.Ix)
    (Q : Mono N) : ℝ :=
  latSk hN k (Sum.elim (fun i => cField hN C k ((P.2 i).1, (P.2 i).2.reflect τ))
    (fun j => Φ.field k (Q.2 j)))

/-- **The mixed kernel of the composites** `sgn(P) · lim_ultra mixLatC(P, Q)`.

DERIVED: no numeral. -/
def mixKC (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (P : TSepG C.Ix τ)
    (Q : Mono N) : ℝ :=
  sgnC C τ P.1 * limUnder (ultra : Filter ℕ) (fun k => mixLatC hN C Φ τ k P.1 Q)

/-- DERIVED: no numeral. -/
theorem cField_snd (hN : N ≠ 0) (C : Composites N) (k : ℕ) (p : CDatum C) :
    (cField hN C k p).2 = p.2 := rfl

/-- DERIVED: no numeral. -/
theorem locField_snd (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) (b : ρ.B) (f : TestFn) :
    (locField hN ρ k b f).2 = f := rfl

/-- **A reading with composites and other fields expands over the basis** of the composites'
fields: if `ren k (x i) = ∑_b M k (α i) b · op b`, the reading of `(x i, f i)ᵢ ∪ G` is
`∑_b ∏ᵢ M k (α i) (b i) · ν_k(∏ᵢ smear(op bᵢ − ν_k(op bᵢ)) fᵢ · ∏ⱼ smear Gⱼ)`.

DERIVED: no numeral. -/
theorem latSk_elim_expand (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (k : ℕ)
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] (x : ι → C.Ix) (α : ι → Idx4)
    (hren : ∀ i, (C.ren k (x i)).1 = ∑ b, ρ.M k (α i) b • (ρ.op b).1) (f : ι → TestFn)
    (G : κ → SField N) :
    latSk hN k (Sum.elim (fun i => cField hN C k (x i, f i)) G)
      = ∑ b : ι → ρ.B, (∏ i, ρ.M k (α i) (b i))
          * latSk hN k (Sum.elim (fun i => locField hN ρ k (b i) (f i)) G) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have h1 : ∀ i, smear (dySpacing N k) (cField hN C k (x i, f i)).1.1 (f i)
      = ∑ b, ρ.M k (α i) b • smear (dySpacing N k) (locField hN ρ k b (f i)).1.1 (f i) :=
    fun i => by
      rw [LinkReduce.cField_field hN ρ C k (x i) (α i) (hren i), LinkReduce.smear_sum ha]
  simp only [latSk, latS, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, cField_snd,
    locField_snd]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Fintype.prod_sum, Finset.sum_mul,
    MassGap.DLRLimit.State.map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_smul, smul_mul_assoc, MassGap.DLRLimit.State.map_smul]

/-- **The sector's mixed reading as a combination of the composites' mixed readings**, from the
second clause of `TIn` at step `k`:
`mixLatT P Q = ∑_α ∏ᵢ (reflC cᵢ)(αᵢ) · mixLatC((e αᵢ, fᵢ)ᵢ, Q)`.

DERIVED: no numeral. -/
theorem mixLatT_eq_sum (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (Φ : Flow N) (τ : Fin 4) (k : ℕ)
    (hren : ∀ α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (P : TMono) (Q : Mono N) :
    mixLatT hN ρ Φ τ k P Q
      = ∑ α : Fin P.1 → Idx4, (∏ i, reflC τ (P.2 i).1 (α i))
          * mixLatC hN C Φ τ k ⟨P.1, fun i => (e (α i), (P.2 i).2)⟩ Q := by
  have h2 : ∀ α : Fin P.1 → Idx4, mixLatC hN C Φ τ k ⟨P.1, fun i => (e (α i), (P.2 i).2)⟩ Q
      = ∑ b : Fin P.1 → ρ.B, (∏ i, ρ.M k (α i) (b i))
          * latSk hN k (Sum.elim (fun i => locField hN ρ k (b i) ((P.2 i).2.reflect τ))
              (fun j => Φ.field k (Q.2 j))) :=
    fun α => latSk_elim_expand hN ρ C k (fun i => e (α i)) α (fun i => hren (α i))
      (fun i => (P.2 i).2.reflect τ) (fun j => Φ.field k (Q.2 j))
  unfold mixLatT
  simp only [h2, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin P.1 → Idx4)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h3 : (∏ i, mixC ρ k (reflC τ (P.2 i).1) (b i))
      = ∑ α : Fin P.1 → Idx4, ∏ i, (reflC τ (P.2 i).1 (α i) * ρ.M k (α i) (b i)) :=
    Fintype.prod_sum (fun i α' => reflC τ (P.2 i).1 α' * ρ.M k α' (b i))
  rw [h3, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- **The reflection signs**: `∏ᵢ (reflC cᵢ)(αᵢ) = sgnC(P_α) · ∏ᵢ cᵢ(αᵢ)`, from the first clause of
`TIn`.

DERIVED: `0`, `1`, `2`, `3` the four slots of a rank-four component `Idx4`. -/
theorem prod_reflC (C : Composites N) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)]) (τ : Fin 4)
    (P : TSep τ) (α : Fin P.1.1 → Idx4) :
    ∏ i, reflC τ (P.1.2 i).1 (α i)
      = sgnC C τ (LinkReduce.monoAt e P α).1 * LinkReduce.coefAt P α := by
  have hS : sgnC C τ (LinkReduce.monoAt e P α).1 = ∏ i, (-1 : ℝ) ^ ctau τ (C.cl (e (α i))) := rfl
  rw [hS, LinkReduce.coefAt, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [he1 (α i), LinkReduce.ctau_tensor τ (α i)]
  rfl

/-- **The sector's mixed reading converges to the combination of the composites' mixed kernels**
`∑_α ∏ᵢ cᵢ(αᵢ) · mixKC(P_α, Q)`, from the first two clauses of `TIn` and the convergence of the
composites' mixed readings at the components `P_α`.

DERIVED: `0`, `1`, `2`, `3` the four slots of a rank-four component `Idx4`. -/
theorem tendsto_mixLatT (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (Φ : Flow N) (τ : Fin 4)
    (P : TSep τ) (Q : Mono N)
    (hMC : ∀ α : Fin P.1.1 → Idx4, ∃ x, Tendsto
      (fun k => mixLatC hN C Φ τ k (LinkReduce.monoAt e P α).1 Q) (ultra : Filter ℕ) (𝓝 x)) :
    Tendsto (fun k => mixLatT hN ρ Φ τ k P.1 Q) (ultra : Filter ℕ)
      (𝓝 (∑ α : Fin P.1.1 → Idx4,
        LinkReduce.coefAt P α * mixKC hN C Φ τ (LinkReduce.monoAt e P α) Q)) := by
  have hk : (fun k => mixLatT hN ρ Φ τ k P.1 Q)
      = fun k => ∑ α : Fin P.1.1 → Idx4,
          (sgnC C τ (LinkReduce.monoAt e P α).1 * LinkReduce.coefAt P α)
            * mixLatC hN C Φ τ k (LinkReduce.monoAt e P α).1 Q := funext fun k => by
    rw [mixLatT_eq_sum hN ρ C e Φ τ k (hren k)]
    exact Finset.sum_congr rfl fun α _ => by rw [prod_reflC C e he1 τ P α]; rfl
  have hlim : (∑ α : Fin P.1.1 → Idx4,
        LinkReduce.coefAt P α * mixKC hN C Φ τ (LinkReduce.monoAt e P α) Q)
      = ∑ α : Fin P.1.1 → Idx4,
          (sgnC C τ (LinkReduce.monoAt e P α).1 * LinkReduce.coefAt P α)
            * limUnder (ultra : Filter ℕ)
                (fun k => mixLatC hN C Φ τ k (LinkReduce.monoAt e P α).1 Q) :=
    Finset.sum_congr rfl fun α _ => by unfold mixKC; ring
  rw [hk, hlim]
  exact tendsto_finsetSum _ fun α _ => (tendsto_nhds_limUnder (hMC α)).const_mul _

/-- **The dyadic step is symmetric for the mixed reading** from step `m` on:
`mixLatC(T_m P, Q) = mixLatC(P, T_m Q)`, by the lattice translation invariance of `stateK hN k`
(`latS_translate`, `PeriodicState.periodicState_shift`).

DERIVED: `1` the unit step; `-1` its reflection. -/
theorem mixLatC_shift (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) {m k : ℕ}
    (hk : m ≤ k) (P : TSepG C.Ix τ) (Q : Mono N) :
    mixLatC hN C Φ τ k (shiftT hN τ m P).1 Q
      = mixLatC hN C Φ τ k P.1 (Mono.shift (timeVec N m τ 1) Q) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hT := latS_translate (stateK hN k) (fun τ' => PeriodicState.periodicState_shift hN _ τ') ha
    (Sum.elim (fun i => cField hN C k ((P.1.2 i).1, (P.1.2 i).2.reflect τ))
      (fun j => Φ.field k ((Q.2 j).1, (Q.2 j).2.translate (timeVec N m τ 1))))
    (scaleSite (2 ^ (k - m)) (axisVec τ (-1)))
  rw [← site_dySpacing N hk] at hT
  unfold mixLatC
  rw [latSk_eq, latSk_eq]
  refine Eq.trans ?_ hT
  refine congrArg (latS (stateK hN k) (dySpacing N k)) (funext fun s => ?_)
  rcases s with i | j
  · refine Prod.ext rfl ?_
    show ((P.1.2 i).2.translate (timeVec N m τ 1)).reflect τ
      = ((P.1.2 i).2.reflect τ).translate (timeVec N m τ (-1))
    rw [TestFn.reflect_translate, reflR_timeVec]
  · refine Prod.ext rfl ?_
    show (Q.2 j).2 = ((Q.2 j).2.translate (timeVec N m τ 1)).translate (timeVec N m τ (-1))
    rw [TestFn.translate_translate, timeVec_add, add_neg_cancel, timeVec_zero,
      TestFn.translate_zero]

/-- **The dyadic step is symmetric for the mixed kernel**:
`mixKC(T_m P, Q) = mixKC(P, T_m Q)`.

DERIVED: `1` the unit step. -/
theorem mixKC_shift (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (m : ℕ)
    (P : TSepG C.Ix τ) (Q : Mono N) :
    mixKC hN C Φ τ (shiftT hN τ m P) Q = mixKC hN C Φ τ P (Mono.shift (timeVec N m τ 1) Q) := by
  unfold mixKC
  have hs : sgnC C τ (shiftT hN τ m P).1 = sgnC C τ P.1 := rfl
  rw [hs]
  congr 1
  exact limUnder_congr_ultra ((eventually_ge_atTop m).mono fun k hk => mixLatC_shift hN C Φ τ hk P Q)

/-- **The empty composite monomial reads the flowed kernel**:
`mixKC(∅, Q) = kernF(∅, Q)`.

DERIVED: `0` the empty length. -/
theorem mixKC_empty (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (r : ℝ)
    (Q : Mono N) :
    mixKC hN C Φ τ (emptyG C.Ix τ) Q = kernF hN Φ τ (emptyMargin N τ r).1 Q := by
  have hs : sgnC C τ (emptyG C.Ix τ).1 = 1 := Fin.prod_univ_zero _
  unfold mixKC kernF contSF
  rw [hs, one_mul]
  congr 1
  funext k
  unfold mixLatC latSF
  refine congrArg (latSk hN k) (funext fun s => ?_)
  rcases s with i | j
  · exact i.elim0
  · rfl

/-- **`ΘP ∪ Q` of composites is admissible.** The proof of `ClayWiring.adm_pairT`.

DERIVED: `4` the dimension. -/
theorem adm_pairC (C : Composites N) {τ : Fin 4} (P Q : TSepG C.Ix τ) :
    Adm (pairC C τ P.1 Q.1) := by
  obtain ⟨hcP, dP, hdP, hP⟩ := P.2
  obtain ⟨hcQ, dQ, hdQ, hQ⟩ := Q.2
  let O0 : LField (MassGap.SUN.SU 2) :=
    sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)
  let P' : Mono 2 := ⟨P.1.1, fun i => (O0, (P.1.2 i).2)⟩
  let Q' : Mono 2 := ⟨Q.1.1, fun i => (O0, (Q.1.2 i).2)⟩
  obtain ⟨d, hd, hs⟩ := ContinuumSep.famSep_pairFam_exists (τ := τ) (P := P') (Q := Q')
    ⟨dP, hdP, hP⟩ ⟨dQ, hdQ, hQ⟩
  have hr : Continuous (reflR τ) := continuous_id.update τ (continuous_apply τ).neg
  refine ⟨fun i => ?_, d, hd, fun i j hij => ?_⟩
  · rcases i with a | a
    · exact (hcP a).comp hr
    · exact hcQ a
  · have h := hs i j hij
    rcases i with a | a <;> rcases j with b | b <;> exact h

/-- **The composites' mixed readings are bounded, hence convergent along `ultra`**: an eventual
bound at each pair gives the existence of the limit (`exists_tendsto_ultra`).

DERIVED: no numeral. -/
theorem mixConv_of_bounded (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4)
    (P : TSepG C.Ix τ) (Q : Mono N)
    (hb : ∃ B : ℝ, ∀ᶠ k in atTop, |mixLatC hN C Φ τ k P.1 Q| ≤ B) :
    ∃ x, Tendsto (fun k => mixLatC hN C Φ τ k P.1 Q) (ultra : Filter ℕ) (𝓝 x) := by
  obtain ⟨B, hB⟩ := hb
  exact exists_tendsto_ultra _ B hB

/-- **The channel factors diverge**: `z_c(k) a_k⁴ → 2` forces `|z_c(k)| → ∞`. The mixing
coefficients `mixC (rhoD f z) k` of a composite carry the scalar and pseudoscalar factors, which
`hzS`, `hzP` make diverge, while the bare readings
are bounded uniformly in `k` (`ContinuumSchwinger.abs_latS_translate_le`); this is why the uniform
bounds do not bound `mixLatT`.

DERIVED: `4` the dimension; `2` the limit; `1` a level below it. -/
theorem tendsto_abs_z_atTop (hN : N ≠ 0) (z : ℕ → ℝ)
    (hz : Tendsto (fun k => z k * dySpacing N k ^ 4) atTop (𝓝 2)) :
    Tendsto (fun k => |z k|) atTop atTop := by
  have hpos : ∀ k, 0 < dySpacing N k ^ 4 := fun k => pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  have h0 : Tendsto (fun k => dySpacing N k ^ 4) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using (tendsto_dySpacing N).pow 4,
      Eventually.of_forall hpos⟩
  have hinv : Tendsto (fun k => (dySpacing N k ^ 4)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp h0
  refine tendsto_atTop_mono' atTop ?_ hinv
  filter_upwards [hz.eventually (le_mem_nhds (by norm_num : (1 : ℝ) < 2))] with k hk
  have hi : 0 < (dySpacing N k ^ 4)⁻¹ := inv_pos.mpr (hpos k)
  have e : (z k * dySpacing N k ^ 4) * (dySpacing N k ^ 4)⁻¹ = z k :=
    mul_inv_cancel_right₀ (hpos k).ne' (z k)
  calc (dySpacing N k ^ 4)⁻¹ = 1 * (dySpacing N k ^ 4)⁻¹ := (one_mul _).symm
    _ ≤ (z k * dySpacing N k ^ 4) * (dySpacing N k ^ 4)⁻¹ := mul_le_mul_of_nonneg_right hk hi.le
    _ = z k := e
    _ ≤ |z k| := le_abs_self _

end Mixed

/-! ## 4. The composites in the observer's space -/

section PreLink

variable {N : ℕ}

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.ClayWiring MassGap.ExistenceReduce MassGap.NonTrivialCanonical
open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData

/-- The composites of the SU capstone. DERIVED: no numeral. -/
abbrev Cb (N : ℕ) (z : Chan → ℕ → ℝ) : Composites N := build (rhoD (fT N) z) (bareD (fT N) (bT N))

/-- The observer's flow, `energy0` of the symmetrised plaquette class. DERIVED: no numeral. -/
abbrev Φ0 (W : ConfFlow N) : Flow N := energy0 W (SymPlaqClass N) (symPlaq_refl N)

/-- The observer's vectors `gvecT` of all margin monomials, in the pre-observer's space.
DERIVED: `0` the plane. -/
abbrev vO (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) : MarginMono N 0 r → preH (ne_zero_of_two_le hN2) W hU hphys :=
  gvecT (ne_zero_of_two_le hN2) (Φ0 W) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0)

/-- The composites' mixed kernel against the observer's margin monomials. DERIVED: `0` the plane. -/
abbrev mixK (hN2 : 2 ≤ N) (W : ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ)
    (P : TSepG (Cb N z).Ix 0) (Q : MarginMono N 0 r) : ℝ :=
  mixKC (ne_zero_of_two_le hN2) (Cb N z) (Φ0 W) 0 P Q.1

/-- The observer's flowed kernel on margin monomials. DERIVED: `0` the plane. -/
abbrev gramF (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) (Q Q' : MarginMono N 0 r) : ℝ :=
  kernF (ne_zero_of_two_le hN2) (Φ0 W) 0 Q.1 Q'.1

/-- **The convergence of the composites' mixed readings**: at every composite monomial `P` and
every margin monomial `Q`, the mixed reading of `P` against `Q` converges along `ultra`, so every
value of `mixK` that `JointRPK` and `ApproxK` read is a genuine limit. DERIVED: `0` the plane. -/
def MixConv (hN2 : 2 ≤ N) (W : ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ (P : TSepG (Cb N z).Ix 0) (Q : MarginMono N 0 r),
    ∃ x, Tendsto (fun k => mixLatC (ne_zero_of_two_le hN2) (Cb N z) (Φ0 W) 0 k P.1 Q.1)
      (ultra : Filter ℕ) (𝓝 x)

/-- **The composites in the pre-observer's space.** From the convergence of the composites' mixed
readings `hMC`, the joint reflection positivity `hJ` of the composites' kernel `kernC`, their mixed
kernel `mixK` and the observer's kernel `gramF`, approximability `hA` in that joint form, and
`CompOS` (for the convergence of the composites' Gram readings): vectors `wC` in `preH` with
`LinkCPre` and the two conjuncts of the cross reading `hX` of `NonGaussLink.clayStatementAt_SU_ng`.

`wC` is `exists_link` at `v = gvecT`; the shift and the vacuum follow from the density of the span
of `gvecT` (`obsGen_flow`) with `mixKC_shift`, `mixKC_empty` and the self-adjointness of `timeT`;
the cross reading is `tendsto_mixLatT` at `e = eI`.

DERIVED: `0` the plane. -/
theorem linkCPre_of_kernels (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (z : Chan → ℕ → ℝ)
    (hCO : CompOS (ne_zero_of_two_le hN2) (Cb N z))
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hMC : MixConv hN2 W z r) :
    ∃ wC : TSepG (Cb N z).Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys,
      LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
        (preTime (ne_zero_of_two_le hN2) W hU hphys) (Cb N z) wC
      ∧ ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
        Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) z) (Φ0 W) 0 k P.1 Q.1.1)
            (ultra : Filter ℕ) (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z) (Φ0 W) 0 P.1 Q.1.1))
          ∧ inner ℂ (LinkReduce.wOfC eI wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
            = (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z) (Φ0 W) 0 P.1 Q.1.1 : ℂ) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨hG1, hG2, hG3⟩ := obsGen_flow (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0)
  have hG : ∀ Q Q' : MarginMono N 0 r, inner ℂ (vO hN2 W hU hphys Q) (vO hN2 W hU hphys Q')
      = (gramF hN2 W r Q Q' : ℂ) := hG1
  have hG2' : ∀ (m : ℕ) (Q : MarginMono N 0 r),
      vO hN2 W hU hphys (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q)
        = preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m) (vO hN2 W hU hphys Q) :=
    fun m Q => hG2 m Q _ rfl
  obtain ⟨w, hwX, hwK⟩ := exists_link (gramF hN2 W r) hG ((jointRP_iff_K _ hG).mpr hJ)
    ((approx_iff_K _ hG).mpr hA)
  refine ⟨w, ⟨fun P Q => ⟨hCO.1 _ _ (adm_pairC (Cb N z) P Q), hwK P Q⟩, fun m P => ?_, ?_⟩,
    fun P Q => ?_⟩
  · refine eq_of_inner_eq hG3 fun Q => ?_
    calc inner ℂ (w (shiftT (ne_zero_of_two_le hN2) 0 m P)) (vO hN2 W hU hphys Q)
        = (mixK hN2 W z r P (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q) : ℂ) := by
          rw [hwX]
          exact congrArg Complex.ofReal (mixKC_shift _ _ _ 0 m P Q.1)
      _ = inner ℂ (w P) (vO hN2 W hU hphys (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q)) :=
          (hwX _ _).symm
      _ = inner ℂ (w P) (preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m)
            (vO hN2 W hU hphys Q)) := by
          rw [hG2' m Q]
      _ = inner ℂ (preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m) (w P))
            (vO hN2 W hU hphys Q) :=
          ((isSelfAdjoint_powT (a := stepT (ne_zero_of_two_le hN2) (Φ0 W)
            (preB (ne_zero_of_two_le hN2) W hU) 0
            (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0) 0)
            (dySpacing N m / dySpacing N 0)).isSymmetric (w P) (vO hN2 W hU hphys Q)).symm
  · have hvac : preVac (ne_zero_of_two_le hN2) W hU hphys = vO hN2 W hU hphys (emptyMargin N 0 r) :=
      rfl
    refine eq_of_inner_eq hG3 fun Q => ?_
    rw [hvac, hG, hwX]
    exact congrArg Complex.ofReal (mixKC_empty _ _ _ 0 r Q.1)
  · have hT := tendsto_mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) z) (Cb N z) eI
      (build_he1 _ _) (fun k α => build_he2 _ _ k α) (Φ0 W) 0 P Q.1.1
      (fun α => hMC (LinkReduce.monoAt eI P α) Q.1)
    have hmix : mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z) (Φ0 W) 0 P.1 Q.1.1
        = ∑ α : Fin P.1.1 → Idx4, LinkReduce.coefAt P α
            * mixKC (ne_zero_of_two_le hN2) (Cb N z) (Φ0 W) 0 (LinkReduce.monoAt eI P α) Q.1.1 :=
      hT.limUnder_eq
    refine ⟨by rw [hmix]; exact hT, ?_⟩
    rw [hmix]
    unfold LinkReduce.wOfC
    rw [sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul]
    exact congrArg (fun x => ((LinkReduce.coefAt P α : ℝ) : ℂ) * x) (hwX _ Q.1)

/-- **`NonGaussLink.clayStatementAt_SU_ng` with `wC`, `hLC`, `hX` replaced by kernel statements**:
the convergence of the composites' mixed readings `hMC` at every composite monomial and every
margin monomial, the joint reflection positivity `hJ` and
the approximability `hA` (`linkCPre_of_kernels`). The other inputs are those of
`clayStatementAt_SU_ng`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_link (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hMC : MixConv hN2 W z r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  obtain ⟨wC, hLC, hX⟩ := linkCPre_of_kernels hN2 W hU hphys z hCO hJ hA hMC
  exact NonGaussLink.clayStatementAt_SU_ng hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF hObs
    hWard hCO wC hLC hX

/-- **The joint reflection positivity is necessary**: if vectors `wC` of the pre-observer's space
pair with the observer's vectors `gvecT` by `mixK` and have Gram matrix `kernC`, then `JointRPK`
holds (`jointRP_of_link`). DERIVED: `0` the plane. -/
theorem jointRPK_of_vectors (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (z : Chan → ℕ → ℝ)
    (wC : TSepG (Cb N z).Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (hX : ∀ P Q, inner ℂ (wC P) (vO hN2 W hU hphys Q) = (mixK hN2 W z r P Q : ℂ))
    (hK : ∀ P P', inner ℂ (wC P) (wC P') = (kernC (ne_zero_of_two_le hN2) (Cb N z) 0 P P' : ℂ)) :
    JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r) := by
  obtain ⟨hG1, -, -⟩ := obsGen_flow (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0)
  exact (jointRP_iff_K (v := vO hN2 W hU hphys) _ hG1).mp (jointRP_of_link wC hX hK)

end PreLink

end MassGap.CompositeLink

end

#print axioms MassGap.CompositeLink.yL_add
#print axioms MassGap.CompositeLink.inner_yL_left
#print axioms MassGap.CompositeLink.sq_le_of_quad
#print axioms MassGap.CompositeLink.pairing_sq_le
#print axioms MassGap.CompositeLink.norm_sub_sq_le
#print axioms MassGap.CompositeLink.cauchySeq_yL
#print axioms MassGap.CompositeLink.pairing_of_seq
#print axioms MassGap.CompositeLink.gram_of_seq
#print axioms MassGap.CompositeLink.exists_link
#print axioms MassGap.CompositeLink.jointQ_eq
#print axioms MassGap.CompositeLink.jointRP_of_link
#print axioms MassGap.CompositeLink.dist2_eq
#print axioms MassGap.CompositeLink.approx_iff
#print axioms MassGap.CompositeLink.eq_of_inner_eq
#print axioms MassGap.CompositeLink.norm_yL_sq
#print axioms MassGap.CompositeLink.jointRP_iff_K
#print axioms MassGap.CompositeLink.approx_iff_K
#print axioms MassGap.CompositeLink.latSk_elim_expand
#print axioms MassGap.CompositeLink.mixLatT_eq_sum
#print axioms MassGap.CompositeLink.prod_reflC
#print axioms MassGap.CompositeLink.tendsto_mixLatT
#print axioms MassGap.CompositeLink.mixLatC_shift
#print axioms MassGap.CompositeLink.mixKC_shift
#print axioms MassGap.CompositeLink.mixKC_empty
#print axioms MassGap.CompositeLink.adm_pairC
#print axioms MassGap.CompositeLink.mixConv_of_bounded
#print axioms MassGap.CompositeLink.tendsto_abs_z_atTop
#print axioms MassGap.CompositeLink.linkCPre_of_kernels
#print axioms MassGap.CompositeLink.clayStatementAt_SU_link
#print axioms MassGap.CompositeLink.jointRPK_of_vectors
