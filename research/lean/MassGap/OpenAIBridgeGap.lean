import Mathlib
import MassGap.ApertureThing
import MassGap.ClassHamiltonian

/-!
# MassGap.OpenAIBridgeGap — exponential clustering in Euclidean time gives the gap of the reconstruction

The Osterwalder–Schrader step of §4.8: a reconstructed theory whose connected Euclidean two-point
readings cluster at rate `m` in time has a Hamiltonian with gap at least `m` above the vacuum. It is
stated here on an abstract complex inner product space, with hypotheses shaped like the
reconstruction of the OpenAI submission `yang-mills-group/OpenAI-YM-20261028` (Lean 4.32, not
importable at Lean 4.31): a complex Hilbert space (`PublicTheory.lean:79`, `HilbertSpace`), a unit
vacuum (`PublicTheory.lean:128`, `normalizedVacuum`), and a dense domain of states built from the
vacuum (`PublicTheory.lean:106`, `FieldSystem.domain`; `PublicTheory.lean:126`, W1). Their
`Reconstructed` (`ChallengeSpec.lean:117`) is the Wightman side and names no Euclidean time
semigroup; the semigroup `S t = e^{−tH}`, its self-adjointness and the Euclidean readings
`⟪v, S t w⟫` are the Osterwalder–Schrader data from which the Wightman theory is reconstructed, and
are taken here as hypotheses.

## 1. Discrete time

`T` is a self-adjoint operator (no positivity and no norm bound is used), `Ω` a unit vector with
`T Ω = Ω`, and `D` a set of vectors whose complex span is dense. The connected reading at lag `k` is
`conn T Ω k v w = ⟪v, Tᵏ w⟫ − ⟪v, Ω⟫ ⟪Ω, w⟫`.

* `norm_pow_logConvex`: `k ↦ ‖Tᵏ u‖` is log-convex,
  `‖T^{k+1} u‖² = ⟪Tᵏ u, T^{k+2} u⟫ ≤ ‖Tᵏ u‖ ‖T^{k+2} u‖`, so `ApertureThing.far_ge_pow` gives
  `‖T u‖^{k+1} ≤ ‖T^{k+1} u‖ ‖u‖ᵏ`.
* `norm_apply_le_of_pow_decay`: one vector with `‖Tᵏ u‖ ≤ C e^{−m k}` at every `k` has
  `‖T u‖ ≤ e^{−m} ‖u‖`. Otherwise `q = ‖T u‖ e^m / ‖u‖ > 1` and `q^{k+1} ‖u‖ ≤ C` for every `k`.
* `conn_span`: a bound `‖conn T Ω k v w‖ ≤ C e^{−m k}` for `v, w ∈ D` passes to the span of `D` in
  both slots (the reading is sesquilinear).
* `gap_of_cluster`: hence `‖T u‖ ≤ e^{−m} ‖u‖` for every `u ⊥ Ω`. For `u` in the span, the
  vacuum-complement part `u' = u − ⟪Ω, u⟫ Ω` has `‖Tᵏ u'‖² = conn T Ω (2k) u u` (`T` fixes `Ω`, so `Ω`
  drops from both slots); the set where the bound holds for the complement part is closed and
  contains the dense span.
* `gap_of_cluster_pow`: `‖Tᵏ u‖ ≤ e^{−m k} ‖u‖` on the vacuum complement, which `T` preserves.

## 2. Continuous time

`gap_of_cluster_time`: a family `S : ℝ → E →L[ℂ] E` with `S 0 = 1`, `S (s + t) = S s * S t` and
`S t` self-adjoint fixing `Ω` for `s, t ≥ 0`, clustering on `D` as `C(v, w) e^{−m t}` at every
`t ≥ 0`, has `‖S t u‖ ≤ e^{−m t} ‖u‖` for every `t ≥ 0` and `u ⊥ Ω`. At each `t > 0` this is
`gap_of_cluster` for `T = S t` at rate `m t`, since `(S t)ᵏ = S (k t)`; no continuity in `t` and no
monotonicity is used.

`hamiltonian_gap_of_cluster`: for `m ≥ 0` the generator `H = ClassHamiltonian.generator S`
(the limit of `t⁻¹ (u − S t u)` as `t → 0⁺`) has `m ‖u‖² ≤ re ⟪u, H u⟫` on the vacuum complement of
its domain (`ClassHamiltonian.generator_gap`), the form statement of `spec H ∩ (0, m) = ∅`, and for
`m > 0` its kernel is the vacuum line (`ClassHamiltonian.generator_ker`).

## Scope

What is proved is the abstract step. Not proved here: that their reconstruction carries such a
semigroup with these properties, that their dense domain (or the Euclidean field vectors) is the set
`D`, or that their connected Euclidean readings are the ones bounded in §4.8. Those are the
identification of this module's objects with theirs.
-/

namespace MassGap.OpenAIBridgeGap

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. Discrete time -/

/-- The connected reading at lag `k`: `⟪v, Tᵏ w⟫ − ⟪v, Ω⟫ ⟪Ω, w⟫`. For the transfer operator of a
reconstruction and its vacuum, this is the connected Euclidean two-point reading of the states `v`,
`w` at time separation `k`.

DERIVED: no numeral appears in the definition. -/
noncomputable def conn (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (v w : E) : ℂ :=
  inner ℂ v ((T ^ k) w) - inner ℂ v Ω * inner ℂ Ω w

/-- The norms of the iterates of a self-adjoint operator on one vector are log-convex:
`‖T^{k+1} u‖² ≤ ‖Tᵏ u‖ ‖T^{k+2} u‖`, from `‖T^{k+1} u‖² = ⟪Tᵏ u, T^{k+2} u⟫` (move one `T` across)
and Cauchy–Schwarz. In the form `ApertureThing.LogConvexSeq` reads.

DERIVED: `1` and `2` in the statement of `ApertureThing.LogConvexSeq` are the lag steps; `2` the
square. -/
theorem norm_pow_logConvex {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) (u : E) :
    ApertureThing.LogConvexSeq (fun k => ‖(T ^ k) u‖) := by
  intro k
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have h1 : (T ^ (k + 1)) u = T ((T ^ k) u) := by
    rw [pow_succ', ContinuousLinearMap.mul_apply]
  have h2 : (T ^ (k + 1 + 1)) u = T ((T ^ (k + 1)) u) := by
    rw [pow_succ' T (k + 1), ContinuousLinearMap.mul_apply]
  have hsym : inner ℂ (T ((T ^ k) u)) ((T ^ (k + 1)) u)
      = inner ℂ ((T ^ k) u) (T ((T ^ (k + 1)) u)) := by
    have := hs ((T ^ k) u) ((T ^ (k + 1)) u)
    simpa only [ContinuousLinearMap.coe_coe] using this
  show ‖(T ^ (k + 1)) u‖ ^ 2 ≤ ‖(T ^ k) u‖ * ‖(T ^ (k + 1 + 1)) u‖
  calc ‖(T ^ (k + 1)) u‖ ^ 2
      = RCLike.re (inner ℂ ((T ^ (k + 1)) u) ((T ^ (k + 1)) u)) :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = RCLike.re (inner ℂ ((T ^ k) u) ((T ^ (k + 1 + 1)) u)) := by
        rw [h2, ← hsym, ← h1]
    _ ≤ ‖(T ^ k) u‖ * ‖(T ^ (k + 1 + 1)) u‖ := re_inner_le_norm (𝕜 := ℂ) _ _

/-- **One vector decaying exponentially under the iterates of a self-adjoint operator is contracted
at the same rate in one step**: `‖Tᵏ u‖ ≤ C e^{−m k}` for every `k` gives `‖T u‖ ≤ e^{−m} ‖u‖`.
By log-convexity (`norm_pow_logConvex`, `ApertureThing.far_ge_pow`) `‖T u‖^{k+1} ≤ ‖T^{k+1} u‖ ‖u‖ᵏ`;
if `q = ‖T u‖ e^m / ‖u‖ > 1` this gives `q^{k+1} ‖u‖ ≤ C` for every `k`, which fails for large `k`.

DERIVED: `0` and `1` are the lag origin and the one step of the conclusion; the rate `m` and the
constant `C` are the hypothesis's. -/
theorem norm_apply_le_of_pow_decay {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {u : E} {m C : ℝ}
    (hdec : ∀ k : ℕ, ‖(T ^ k) u‖ ≤ C * Real.exp (-(m * k))) :
    ‖T u‖ ≤ Real.exp (-m) * ‖u‖ := by
  set g : ℕ → ℝ := fun k => ‖(T ^ k) u‖ with hg
  have hL := norm_pow_logConvex hT u
  have h0 : ∀ k, 0 ≤ g k := fun k => norm_nonneg _
  have hg0 : g 0 = ‖u‖ := by simp [hg]
  have hg1 : g 1 = ‖T u‖ := by simp [hg]
  rcases (norm_nonneg u).lt_or_eq with hu | hu
  · by_contra hcon
    push Not at hcon
    set b := ‖u‖
    set a := ‖T u‖ * Real.exp m
    have hem : 0 < Real.exp m := Real.exp_pos m
    have hab : b < a := by
      have h := mul_lt_mul_of_pos_right hcon hem
      rw [mul_comm (Real.exp (-m)) b, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        mul_one] at h
      exact h
    have hq : 1 < a / b := (one_lt_div hu).mpr hab
    have key : ∀ k : ℕ, (a / b) ^ (k + 1) * b ≤ C := by
      intro k
      have hfar := ApertureThing.far_ge_pow h0 hL (m₁ := 1) (m := k + 1) (by omega)
      rw [pow_one, Nat.add_sub_cancel, hg0, hg1] at hfar
      have hd := hdec (k + 1)
      have hbk : 0 < b ^ k := pow_pos hu k
      have hexp : Real.exp m ^ (k + 1) * Real.exp (-(m * ((k + 1 : ℕ) : ℝ))) = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        convert Real.exp_zero using 2
        push_cast
        ring
      have hA : a ^ (k + 1) ≤ C * b ^ k := by
        calc a ^ (k + 1) = ‖T u‖ ^ (k + 1) * Real.exp m ^ (k + 1) := by rw [mul_pow]
          _ ≤ (g (k + 1) * b ^ k) * Real.exp m ^ (k + 1) :=
              mul_le_mul_of_nonneg_right hfar (pow_nonneg hem.le _)
          _ ≤ (C * Real.exp (-(m * ((k + 1 : ℕ) : ℝ))) * b ^ k) * Real.exp m ^ (k + 1) := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hem.le _)
              exact mul_le_mul_of_nonneg_right hd hbk.le
          _ = C * b ^ k * (Real.exp m ^ (k + 1) * Real.exp (-(m * ((k + 1 : ℕ) : ℝ)))) := by ring
          _ = C * b ^ k := by rw [hexp, mul_one]
      have hb0 : b ≠ 0 := hu.ne'
      have he : (a / b) ^ (k + 1) * b = a ^ (k + 1) / b ^ k := by
        rw [div_pow, pow_succ b k]
        field_simp
      rw [he, div_le_iff₀ hbk]
      exact hA
    have hlim : Tendsto (fun k : ℕ => (a / b) ^ (k + 1) * b) atTop atTop :=
      ((tendsto_pow_atTop_atTop_of_one_lt hq).comp (tendsto_add_atTop_nat 1)).atTop_mul_const hu
    obtain ⟨k, hk⟩ := (hlim.eventually_gt_atTop C).exists
    exact absurd (key k) (not_le.mpr hk)
  · have hu0 : u = 0 := norm_eq_zero.mp hu.symm
    rw [hu0]
    simp

omit [CompleteSpace E] in
/-- The connected reading is additive in its first slot.

DERIVED: no numeral appears in the statement. -/
theorem conn_add_left (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (v v' w : E) :
    conn T Ω k (v + v') w = conn T Ω k v w + conn T Ω k v' w := by
  simp only [conn, inner_add_left]
  ring

omit [CompleteSpace E] in
/-- The connected reading is conjugate-linear in its first slot.

DERIVED: no numeral appears in the statement. -/
theorem conn_smul_left (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (c : ℂ) (v w : E) :
    conn T Ω k (c • v) w = (starRingEnd ℂ) c * conn T Ω k v w := by
  simp only [conn, inner_smul_left]
  ring

omit [CompleteSpace E] in
/-- The connected reading is additive in its second slot.

DERIVED: no numeral appears in the statement. -/
theorem conn_add_right (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (v w w' : E) :
    conn T Ω k v (w + w') = conn T Ω k v w + conn T Ω k v w' := by
  simp only [conn, map_add, inner_add_right]
  ring

omit [CompleteSpace E] in
/-- The connected reading is linear in its second slot.

DERIVED: no numeral appears in the statement. -/
theorem conn_smul_right (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (c : ℂ) (v w : E) :
    conn T Ω k v (c • w) = c * conn T Ω k v w := by
  simp only [conn, map_smul, inner_smul_right]
  ring

omit [CompleteSpace E] in
/-- The connected reading vanishes at the zero vector in the first slot.

DERIVED: `0` is the zero vector and the zero reading. -/
theorem conn_zero_left (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (w : E) : conn T Ω k 0 w = 0 := by
  simp [conn]

omit [CompleteSpace E] in
/-- The connected reading vanishes at the zero vector in the second slot.

DERIVED: `0` is the zero vector and the zero reading. -/
theorem conn_zero_right (T : E →L[ℂ] E) (Ω : E) (k : ℕ) (v : E) : conn T Ω k v 0 = 0 := by
  simp [conn]

/-- Exponential clustering of the pair `(v, w)` at rate `m`: some `C` bounds the connected reading by
`C e^{−m k}` at every lag `k`.

DERIVED: no numeral appears in the definition. -/
def Clusters (T : E →L[ℂ] E) (Ω : E) (m : ℝ) (v w : E) : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, ‖conn T Ω k v w‖ ≤ C * Real.exp (-(m * k))

/-- Clustering in the first slot is closed under sums, scalar multiples and contains `0`, so it holds
on the span of any set on which it holds, for a fixed second vector.

DERIVED: `0` is the zero vector and the zero constant. -/
theorem clusters_span_left {T : E →L[ℂ] E} {Ω : E} {m : ℝ} {D : Set E} {w : E}
    (h : ∀ v ∈ D, Clusters T Ω m v w) {v : E} (hv : v ∈ Submodule.span ℂ D) :
    Clusters T Ω m v w := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun k => by rw [conn_zero_left, norm_zero, zero_mul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨C₁, h₁⟩ := hx
    obtain ⟨C₂, h₂⟩ := hy
    refine ⟨C₁ + C₂, fun k => ?_⟩
    rw [conn_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ k) (h₂ k))
  | smul c x _ hx =>
    obtain ⟨C, hC⟩ := hx
    refine ⟨‖c‖ * C, fun k => ?_⟩
    rw [conn_smul_left, norm_mul, Complex.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg c)

/-- Clustering in the second slot holds on the span of any set on which it holds, for a fixed first
vector.

DERIVED: `0` is the zero vector and the zero constant. -/
theorem clusters_span_right {T : E →L[ℂ] E} {Ω : E} {m : ℝ} {D : Set E} {v : E}
    (h : ∀ w ∈ D, Clusters T Ω m v w) {w : E} (hw : w ∈ Submodule.span ℂ D) :
    Clusters T Ω m v w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun k => by rw [conn_zero_right, norm_zero, zero_mul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨C₁, h₁⟩ := hx
    obtain ⟨C₂, h₂⟩ := hy
    refine ⟨C₁ + C₂, fun k => ?_⟩
    rw [conn_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ k) (h₂ k))
  | smul c x _ hx =>
    obtain ⟨C, hC⟩ := hx
    refine ⟨‖c‖ * C, fun k => ?_⟩
    rw [conn_smul_right, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg c)

/-- **Clustering on a set passes to its span in both slots**: if every pair of `D` clusters at rate
`m`, so does every pair of `span D`.

DERIVED: no numeral appears in the statement. -/
theorem conn_span {T : E →L[ℂ] E} {Ω : E} {m : ℝ} {D : Set E}
    (h : ∀ v ∈ D, ∀ w ∈ D, Clusters T Ω m v w) {v w : E} (hv : v ∈ Submodule.span ℂ D)
    (hw : w ∈ Submodule.span ℂ D) : Clusters T Ω m v w :=
  clusters_span_right (fun w' hw' => clusters_span_left (fun v' hv' => h v' hv' w' hw') hv) hw

/-- The vacuum drops from the connected reading, in either slot: with `T` self-adjoint, `T Ω = Ω` and
`‖Ω‖ = 1`, `conn T Ω k Ω w = 0` and `conn T Ω k v Ω = 0`.

DERIVED: `1` is the unit norm of the vacuum; `0` the vanishing reading. -/
theorem conn_vac {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {Ω : E} (hΩn : ‖Ω‖ = 1) (hΩ : T Ω = Ω)
    (k : ℕ) (v w : E) : conn T Ω k Ω w = 0 ∧ conn T Ω k v Ω = 0 := by
  have hpow : (T ^ k) Ω = Ω := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hΩ]
  have hΩΩ : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hΩn]
    norm_num
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hT.pow k)
  have hsw : inner ℂ Ω ((T ^ k) w) = inner ℂ Ω w := by
    have := hs Ω w
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hpow]
  refine ⟨?_, ?_⟩
  · simp only [conn, hsw, hΩΩ, one_mul, sub_self]
  · simp only [conn, hpow, hΩΩ, mul_one, sub_self]

/-- The vacuum-complement part `u − ⟪Ω, u⟫ Ω` of a vector has the same connected readings on the
diagonal as the vector, and on it the reading at lag `2k` is `‖Tᵏ (u − ⟪Ω, u⟫ Ω)‖²`.

DERIVED: `2` in `2 * k` is the two half-lags `k` of the square `‖Tᵏ ·‖²`; `2` the square. -/
theorem norm_pow_compl_sq {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : T Ω = Ω) (u : E) (k : ℕ) :
    ‖(T ^ k) (u - inner ℂ Ω u • Ω)‖ ^ 2 = RCLike.re (conn T Ω (2 * k) u u) := by
  obtain ⟨u', hu'⟩ : ∃ u', u' = u - inner ℂ Ω u • Ω := ⟨_, rfl⟩
  rw [← hu']
  have hΩΩ : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hΩn]
    norm_num
  have horth : inner ℂ Ω u' = 0 := by
    rw [hu', inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
  have horth' : inner ℂ u' Ω = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  have hvL : ∀ w, conn T Ω (2 * k) Ω w = 0 := fun w => (conn_vac hT hΩn hΩ (2 * k) 0 w).1
  have hvR : ∀ v, conn T Ω (2 * k) v Ω = 0 := fun v => (conn_vac hT hΩn hΩ (2 * k) v 0).2
  have hsame : conn T Ω (2 * k) u' u' = conn T Ω (2 * k) u u := by
    rw [hu', sub_eq_add_neg, ← neg_smul]
    simp only [conn_add_left, conn_add_right, conn_smul_left, conn_smul_right, hvL, hvR, mul_zero,
      add_zero]
  have hdiag : conn T Ω (2 * k) u' u' = inner ℂ u' ((T ^ (2 * k)) u') := by
    simp only [conn, horth', zero_mul, sub_zero]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hT.pow k)
  have hsq : inner ℂ u' ((T ^ (2 * k)) u') = inner ℂ ((T ^ k) u') ((T ^ k) u') := by
    have := hs u' ((T ^ k) u')
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, two_mul, pow_add, ContinuousLinearMap.mul_apply]
  rw [← hsame, hdiag, hsq]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) _

/-- **Exponential clustering in discrete Euclidean time gives the gap on the vacuum complement.** Let
`T` be self-adjoint, `Ω` a unit vector with `T Ω = Ω`, and `D` a set whose span is dense. If every
pair `v, w ∈ D` has `|⟪v, Tᵏ w⟫ − ⟪v, Ω⟫ ⟪Ω, w⟫| ≤ C(v, w) e^{−m k}` at every lag `k`, then
`‖T u‖ ≤ e^{−m} ‖u‖` for every `u ⊥ Ω`.

For `u` in the span the complement part `u'` has `‖Tᵏ u'‖² = re conn T Ω (2k) u u ≤ C e^{−2mk}`
(`norm_pow_compl_sq`, `conn_span`), so `‖Tᵏ u'‖ ≤ √C e^{−mk}` and `norm_apply_le_of_pow_decay`
applies; the bound for the complement part is a closed condition and the span is dense.

DERIVED: `0` is the vanishing vacuum pairing; `1` the unit norm of the vacuum; `2` in the proof is
the square and the doubled lag. -/
theorem gap_of_cluster {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : T Ω = Ω) {D : Set E} (hD : Dense (Submodule.span ℂ D : Set E)) {m : ℝ}
    (hcl : ∀ v ∈ D, ∀ w ∈ D, ∃ C : ℝ, ∀ k : ℕ,
      ‖inner ℂ v ((T ^ k) w) - inner ℂ v Ω * inner ℂ Ω w‖ ≤ C * Real.exp (-(m * k)))
    (u : E) (hu : inner ℂ Ω u = 0) : ‖T u‖ ≤ Real.exp (-m) * ‖u‖ := by
  -- the bound for the vacuum-complement part, on the span
  have hspan : ∀ x ∈ (Submodule.span ℂ D : Set E),
      ‖T (x - inner ℂ Ω x • Ω)‖ ≤ Real.exp (-m) * ‖x - inner ℂ Ω x • Ω‖ := by
    intro x hx
    obtain ⟨C, hC⟩ := conn_span (T := T) (Ω := Ω) (m := m) hcl hx hx
    refine norm_apply_le_of_pow_decay hT (C := Real.sqrt C) (fun k => ?_)
    have h2 := norm_pow_compl_sq hT hΩn hΩ x k
    have hre : RCLike.re (conn T Ω (2 * k) x x) ≤ C * Real.exp (-(m * k)) ^ 2 := by
      refine (RCLike.re_le_norm _).trans ((hC (2 * k)).trans (le_of_eq ?_))
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [← h2] at hre
    have hsq := Real.sqrt_le_sqrt hre
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul' _ (sq_nonneg _),
      Real.sqrt_sq (Real.exp_pos _).le] at hsq
    exact hsq
  -- the condition is closed
  have hcont : Continuous fun x : E => x - inner ℂ Ω x • Ω :=
    continuous_id.sub ((continuous_const.inner continuous_id).smul continuous_const)
  have hclosed : IsClosed {x : E | ‖T (x - inner ℂ Ω x • Ω)‖
      ≤ Real.exp (-m) * ‖x - inner ℂ Ω x • Ω‖} :=
    isClosed_le (continuous_norm.comp (T.continuous.comp hcont))
      (continuous_const.mul (continuous_norm.comp hcont))
  have hall : (Set.univ : Set E) ⊆ {x : E | ‖T (x - inner ℂ Ω x • Ω)‖
      ≤ Real.exp (-m) * ‖x - inner ℂ Ω x • Ω‖} := by
    rw [← hD.closure_eq]
    exact closure_minimal hspan hclosed
  have h := hall (Set.mem_univ u)
  simp only [Set.mem_setOf_eq, hu, zero_smul, sub_zero] at h
  exact h

/-- **The gap at every lag**: under the hypotheses of `gap_of_cluster`, `‖Tᵏ u‖ ≤ e^{−m k} ‖u‖` for
every `u ⊥ Ω` and every `k`. `T` preserves the vacuum complement (`⟪Ω, T u⟫ = ⟪T Ω, u⟫`).

DERIVED: `0` is the vanishing vacuum pairing and the lag origin; `1` the unit norm of the vacuum and
the lag step. -/
theorem gap_of_cluster_pow {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : T Ω = Ω) {D : Set E} (hD : Dense (Submodule.span ℂ D : Set E)) {m : ℝ}
    (hcl : ∀ v ∈ D, ∀ w ∈ D, ∃ C : ℝ, ∀ k : ℕ,
      ‖inner ℂ v ((T ^ k) w) - inner ℂ v Ω * inner ℂ Ω w‖ ≤ C * Real.exp (-(m * k)))
    (u : E) (hu : inner ℂ Ω u = 0) (k : ℕ) :
    ‖(T ^ k) u‖ ≤ Real.exp (-(m * k)) * ‖u‖ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hpres : ∀ x : E, inner ℂ Ω x = 0 → inner ℂ Ω (T x) = 0 := by
    intro x hx
    have := hs Ω x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hΩ, hx]
  induction k with
  | zero => simp
  | succ k ih =>
    have horth : inner ℂ Ω ((T ^ k) u) = 0 := by
      clear ih
      induction k with
      | zero => simpa using hu
      | succ j hj => rw [pow_succ', ContinuousLinearMap.mul_apply]; exact hpres _ hj
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    calc ‖T ((T ^ k) u)‖ ≤ Real.exp (-m) * ‖(T ^ k) u‖ := gap_of_cluster hT hΩn hΩ hD hcl _ horth
      _ ≤ Real.exp (-m) * (Real.exp (-(m * k)) * ‖u‖) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (-(m * ((k + 1 : ℕ) : ℝ))) * ‖u‖ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring

/-! ## 2. Continuous time -/

omit [CompleteSpace E] in
/-- The integer powers of one step of a semigroup are its values at the integer multiples of the
step: `(S t)ᵏ = S (k t)`, from `S 0 = 1` and `S (s + t) = S s * S t` at `s, t ≥ 0`.

DERIVED: `0` is the time origin; `1` the identity and the lag step. -/
theorem semigroup_pow {S : ℝ → E →L[ℂ] E} (h0 : S 0 = 1)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    S t ^ k = S (k * t) := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [pow_succ', ih, ← hadd t (k * t) ht (mul_nonneg (Nat.cast_nonneg k) ht)]
    congr 1
    push_cast
    ring

/-- **Exponential clustering in continuous Euclidean time gives the gap on the vacuum complement.**
Let `S : ℝ → E →L[ℂ] E` be a semigroup on `t ≥ 0` (`S 0 = 1`, `S (s + t) = S s * S t`) of self-adjoint
operators fixing the unit vacuum `Ω`, and `D` a set with dense span. If every pair `v, w ∈ D` has
`|⟪v, S t w⟫ − ⟪v, Ω⟫ ⟪Ω, w⟫| ≤ C(v, w) e^{−m t}` at every `t ≥ 0`, then `‖S t u‖ ≤ e^{−m t} ‖u‖` for
every `t ≥ 0` and `u ⊥ Ω`. At `t > 0` it is `gap_of_cluster` for `S t` at rate `m t`, read at the
times `k t` (`semigroup_pow`).

The hypotheses are the Osterwalder–Schrader data of a reconstruction: in the OpenAI submission the
Hilbert space is `PublicTheory.lean:79`, the unit vacuum `PublicTheory.lean:128`, the dense domain
`PublicTheory.lean:106` with W1 at `PublicTheory.lean:126`; their `Reconstructed`
(`ChallengeSpec.lean:117`) does not name the Euclidean semigroup `S`.

DERIVED: `0` is the time origin and the vanishing vacuum pairing; `1` the identity at time `0` and
the unit norm of the vacuum. -/
theorem gap_of_cluster_time {S : ℝ → E →L[ℂ] E} (h0 : S 0 = 1)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hsa : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (S t)) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : ∀ t : ℝ, 0 ≤ t → S t Ω = Ω) {D : Set E} (hD : Dense (Submodule.span ℂ D : Set E))
    {m : ℝ} (hcl : ∀ v ∈ D, ∀ w ∈ D, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖inner ℂ v (S t w) - inner ℂ v Ω * inner ℂ Ω w‖ ≤ C * Real.exp (-(m * t)))
    {t : ℝ} (ht : 0 ≤ t) (u : E) (hu : inner ℂ Ω u = 0) :
    ‖S t u‖ ≤ Real.exp (-(m * t)) * ‖u‖ := by
  refine gap_of_cluster (hsa t ht) hΩn (hΩ t ht) hD (m := m * t) (fun v hv w hw => ?_) u hu
  obtain ⟨C, hC⟩ := hcl v hv w hw
  refine ⟨C, fun k => ?_⟩
  rw [semigroup_pow h0 hadd ht k]
  have h := hC (k * t) (mul_nonneg (Nat.cast_nonneg k) ht)
  rw [show m * (k * t) = m * t * k by ring] at h
  exact h

/-- **The reconstructed Hamiltonian has gap at least `m`**: under the hypotheses of
`gap_of_cluster_time` with `m ≥ 0`, the generator `H = ClassHamiltonian.generator S` (the limit of
`t⁻¹ (u − S t u)` as `t → 0⁺`) satisfies `m ‖u‖² ≤ re ⟪u, H u⟫` for every `u` in its domain with
`u ⊥ Ω` (`ClassHamiltonian.generator_gap`). This is the form statement of `spec H ∩ (0, m) = ∅` on
the vacuum complement.

DERIVED: `0` is the time origin, the sign of the rate and the vanishing vacuum pairing; `1` the
identity and the unit norm of the vacuum; `2` the square of the norm. -/
theorem hamiltonian_gap_of_cluster {S : ℝ → E →L[ℂ] E} (h0 : S 0 = 1)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hsa : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (S t)) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : ∀ t : ℝ, 0 ≤ t → S t Ω = Ω) {D : Set E} (hD : Dense (Submodule.span ℂ D : Set E))
    {m : ℝ} (hm : 0 ≤ m) (hcl : ∀ v ∈ D, ∀ w ∈ D, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖inner ℂ v (S t w) - inner ℂ v Ω * inner ℂ Ω w‖ ≤ C * Real.exp (-(m * t)))
    (u : (ClassHamiltonian.generator S).domain) (hu : inner ℂ Ω (u : E) = 0) :
    m * ‖(u : E)‖ ^ 2 ≤ (inner ℂ (u : E) (ClassHamiltonian.generator S u)).re :=
  ClassHamiltonian.generator_gap S hm
    (fun _ ht w hw => gap_of_cluster_time h0 hadd hsa hΩn hΩ hD hcl ht.le w hw) u hu

/-- **The vacuum is the only ground state of the reconstructed Hamiltonian**: under the hypotheses of
`gap_of_cluster_time` with `m > 0`, a vector of the domain with `H u = 0` is a multiple of `Ω`
(`ClassHamiltonian.generator_ker` at the gap of `hamiltonian_gap_of_cluster`).

DERIVED: `0` is the time origin, the sign of the rate, the vanishing vacuum pairing and the zero
vector; `1` the identity and the unit norm of the vacuum. -/
theorem hamiltonian_ker_of_cluster {S : ℝ → E →L[ℂ] E} (h0 : S 0 = 1)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hsa : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (S t)) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : ∀ t : ℝ, 0 ≤ t → S t Ω = Ω) {D : Set E} (hD : Dense (Submodule.span ℂ D : Set E))
    {m : ℝ} (hm : 0 < m) (hcl : ∀ v ∈ D, ∀ w ∈ D, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖inner ℂ v (S t w) - inner ℂ v Ω * inner ℂ Ω w‖ ≤ C * Real.exp (-(m * t)))
    (u : (ClassHamiltonian.generator S).domain) (hHu : ClassHamiltonian.generator S u = 0) :
    ∃ c : ℂ, (u : E) = c • Ω :=
  ClassHamiltonian.generator_ker S hm hΩn (fun t ht => hΩ t ht.le)
    (fun w hw => hamiltonian_gap_of_cluster h0 hadd hsa hΩn hΩ hD hm.le hcl w hw) u hHu

end MassGap.OpenAIBridgeGap

#print axioms MassGap.OpenAIBridgeGap.norm_pow_logConvex
#print axioms MassGap.OpenAIBridgeGap.norm_apply_le_of_pow_decay
#print axioms MassGap.OpenAIBridgeGap.conn_add_left
#print axioms MassGap.OpenAIBridgeGap.conn_smul_left
#print axioms MassGap.OpenAIBridgeGap.conn_add_right
#print axioms MassGap.OpenAIBridgeGap.conn_smul_right
#print axioms MassGap.OpenAIBridgeGap.conn_zero_left
#print axioms MassGap.OpenAIBridgeGap.conn_zero_right
#print axioms MassGap.OpenAIBridgeGap.clusters_span_left
#print axioms MassGap.OpenAIBridgeGap.clusters_span_right
#print axioms MassGap.OpenAIBridgeGap.conn_span
#print axioms MassGap.OpenAIBridgeGap.conn_vac
#print axioms MassGap.OpenAIBridgeGap.norm_pow_compl_sq
#print axioms MassGap.OpenAIBridgeGap.gap_of_cluster
#print axioms MassGap.OpenAIBridgeGap.gap_of_cluster_pow
#print axioms MassGap.OpenAIBridgeGap.semigroup_pow
#print axioms MassGap.OpenAIBridgeGap.gap_of_cluster_time
#print axioms MassGap.OpenAIBridgeGap.hamiltonian_gap_of_cluster
#print axioms MassGap.OpenAIBridgeGap.hamiltonian_ker_of_cluster
