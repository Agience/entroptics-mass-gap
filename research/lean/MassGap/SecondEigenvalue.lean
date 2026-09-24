import Mathlib
import MassGap.VolumeRate
import MassGap.SpectralBound

/-!
# MassGap.SecondEigenvalue — an operator bound on an invariant subspace from a Rayleigh bound

## §1 The generic lemma

For `T : E →ₗ[ℝ] E` symmetric on a real inner product space and `V : Submodule ℝ E`:

* `inner_map_quad` — the expansion
  `⟪T (t • u + v), t • u + v⟫ = ⟪T u, u⟫ t² + 2 ⟪T u, v⟫ t + ⟪T v, v⟫`, with symmetry used once to
  merge the two cross terms.
* `inner_map_cauchy_schwarz` — `⟪T u, v⟫ ² ≤ ⟪T u, u⟫ ⟪T v, v⟫` for `u, v ∈ V`, from the
  discriminant of that quadratic, assuming the form is nonnegative on `V` only.
* `norm_le_of_rayleigh_le` — if `V` is `T`-invariant and `0 ≤ ⟪T y, y⟫ ≤ Λ ‖y‖²` on `V`, then
  `‖T y‖ ≤ Λ ‖y‖` on `V`. The proof is one Cauchy–Schwarz with the Rayleigh bound read at `y` and at
  `T y`; invariance is what puts `T y` back in `V`.
* `rayleighSet`, `lambdaTwo` — the Rayleigh quotients at the nonzero vectors of `V`, and their
  supremum. `lambdaTwo_nonneg`, `rayleigh_le_of_lambdaTwo_le`, `lambdaTwo_le_of_rayleigh_le` and
  `norm_le_lambdaTwo_mul` relate the two directions and give the operator bound at the supremum.

The section uses no compactness, completeness, finite dimension, eigenvalue ordering or spectral
theorem. `lambdaTwo` is a definition, not an assertion that the supremum is attained; the theorems
that use it carry `BddAbove (rayleighSet T V)` or `(rayleighSet T V).Nonempty`, since `sSup` is a
junk value otherwise.

The discriminant step repeats what `Reconstruction.gns_cauchy_schwarz` and
`Transfer.ReflForm.cauchy_schwarz` do, with the same `discrim_le_zero` proof. It is separate because
both of those require the form to be nonnegative on the whole module, while `B (u, v) = ⟪T u, v⟫` is
assumed nonnegative on `V` alone.

## §2 At a `Transfer.TransferData`

`vacPerp D` is `{y | ⟪Ω, y⟫ = 0}` as a submodule, equal to `(Submodule.span ℝ {Ω})ᗮ`
(`vacPerp_eq_orthogonal`) but spelled so that `mem_vacPerp` is `Iff.rfl`. `vacPerp_invariant` is
`VolumeRate.inner_vac_Tq` in submodule form. `norm_Tq_le_of_rayleigh` produces `‖Tq y‖ ≤ Λ ‖y‖` on
the complement, which is the hypothesis `VolumeRate.rp_sub_geometric`, `VolumeRate.rp_gap_of_one_cut`
and `HalfLineTransfer` take; `Tq_pow_norm_le_of_rayleigh` and `tendsto_zero_of_rayleigh` are those
two consumers with it supplied.

## §3 Lag two

`inner_Tq_two_eq` is `⟪x, Tq² x⟫ = ‖Tq x‖²`, from symmetry alone; `inner_Tq_two_le_of_rayleigh`
bounds it by `Λ² ‖x‖²`. `lag_two_ratio_of_vacuum_rayleigh` and `spectralAt_of_vacuum_rayleigh` carry
that to `wilsonCorrAt 3 β 2 ≤ Λ² wilsonCorrAt 3 β 0` and to `SpectralBound.SpectralAt β Λ`.

## Scope

* The Rayleigh bound `Λ` is a hypothesis throughout. No declaration here produces one.
* `hpos`, nonnegativity of `⟪Tq y, y⟫` on the complement, is a hypothesis of every theorem that uses
  it and is not a field of `TransferData`. `T_contract` bounds the magnitude of the form, not its
  sign.
* §3's `h0 : wilsonCorrAt 3 β 0 = ‖x‖²` and `h2 : wilsonCorrAt 3 β 2 = ⟪x, Tq² x⟫` are equations
  between real numbers, supplied by the caller. Nothing in them ties `D` to the Wilson measure, and
  together with `hx` they assert that the whole contact value is carried by a vacuum-orthogonal
  vector.
* `SpectralBound.LagSpectralBound` requires one `Λ` below `SpectralBound.lambdaThreshold` at every
  `β ≥ 0`; a single coupling is not enough for it.
* `SpectralBound.spectralAt_iff` shows `SpectralAt β Λ` is the lag-two ratio statement, with no
  operator in it. The identification of that statement with an operator's subdominant bound is `h0`
  and `h2`, not a theorem.

Foundational footprint only (`#print axioms` throughout).
Build: `python code/lean_build.py build MassGap.SecondEigenvalue`.
-/

namespace MassGap.SecondEigenvalue

open MassGap MassGap.Transfer

/-! ## §1 The Rayleigh quotient on an invariant subspace, over any real inner product space

Nothing in this section mentions a lattice, a measure or a gauge group. `T` is any symmetric linear
map on a real inner product space and `V` is any submodule it preserves. -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `T` symmetric, `⟪T (t • u + v), t • u + v⟫ = ⟪T u, u⟫ * (t * t) + (2 * ⟪T u, v⟫) * t + ⟪T v, v⟫`
at every pair `u`, `v` and every real `t`. The map is expanded by linearity and the inner product by
bilinearity; symmetry is used once, to identify `⟪T v, u⟫` with `⟪T u, v⟫`.

Scope: without symmetry the middle coefficient would be `⟪T u, v⟫ + ⟪T v, u⟫`, and the discriminant
argument in `inner_map_cauchy_schwarz` would read a different number.

DERIVED: `2` is the coefficient of the linear term, the number of cross terms a symmetric form
produces. -/
theorem inner_map_quad (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (u v : E) (t : ℝ) :
    (inner ℝ (T (t • u + v)) (t • u + v) : ℝ)
      = (inner ℝ (T u) u : ℝ) * (t * t)
        + (2 * (inner ℝ (T u) v : ℝ)) * t + (inner ℝ (T v) v : ℝ) := by
  have hsymm : (inner ℝ (T v) u : ℝ) = (inner ℝ (T u) v : ℝ) := by
    rw [hT v u]
    exact (real_inner_comm v (T u)).symm
  have hmap : T (t • u + v) = t • T u + T v := by
    rw [map_add, map_smul]
  rw [hmap]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [hsymm]
  ring

#print axioms inner_map_quad

/-- For `T` symmetric and `V` a submodule on which `0 ≤ ⟪T y, y⟫`, every pair `u, v ∈ V` satisfies
`⟪T u, v⟫ ^ 2 ≤ ⟪T u, u⟫ * ⟪T v, v⟫`. The quadratic `t ↦ ⟪T (t • u + v), t • u + v⟫` is nonnegative
because `t • u + v` lies in `V`, so `discrim_le_zero` applies to the expansion `inner_map_quad`.

Scope: nonnegativity is required on `V` only, so `T` may be indefinite elsewhere.
`Transfer.ReflForm.cauchy_schwarz` and `Reconstruction.gns_cauchy_schwarz` are the same argument, but
both require the form to be nonnegative on the whole module, so neither is reused here.

DERIVED: `0` is the lower bound in the nonnegativity hypothesis; the exponent `2` is the square on
the left, the degree of the quadratic the discriminant is taken of. The `4` of `b ^ 2 - 4 * a * c`
lives inside `discrim`, not in this statement. -/
theorem inner_map_cauchy_schwarz (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (V : Submodule ℝ E)
    (hpos : ∀ y ∈ V, (0 : ℝ) ≤ (inner ℝ (T y) y : ℝ))
    {u v : E} (hu : u ∈ V) (hv : v ∈ V) :
    (inner ℝ (T u) v : ℝ) ^ 2 ≤ (inner ℝ (T u) u : ℝ) * (inner ℝ (T v) v : ℝ) := by
  have hq : ∀ t : ℝ, (0 : ℝ) ≤ (inner ℝ (T u) u : ℝ) * (t * t)
      + (2 * (inner ℝ (T u) v : ℝ)) * t + (inner ℝ (T v) v : ℝ) := by
    intro t
    rw [← inner_map_quad T hT u v t]
    exact hpos _ (V.add_mem (V.smul_mem t hu) hv)
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  nlinarith [hd]

#print axioms inner_map_cauchy_schwarz

/-- For `T` symmetric, `V` a `T`-invariant submodule on which `0 ≤ ⟪T y, y⟫ ≤ Λ * ‖y‖ ^ 2` with
`0 ≤ Λ`, every `y ∈ V` satisfies `‖T y‖ ≤ Λ * ‖y‖`.

The argument applies `inner_map_cauchy_schwarz` at the pair `y`, `T y` and reads the Rayleigh bound
at both:

    ‖T y‖ ^ 4 = ⟪T y, T y⟫ ^ 2 ≤ ⟪T y, y⟫ * ⟪T (T y), T y⟫ ≤ (Λ * ‖y‖ ^ 2) * (Λ * ‖T y‖ ^ 2).

Invariance is what puts `T y` back in `V`, licensing the second factor's bound; nonnegativity is
what makes the form semidefinite, licensing Cauchy–Schwarz.

Scope: `E` is any real inner product space and `T` any symmetric linear map — no compactness,
completeness, finite dimension, eigenvalue ordering or spectral theorem is used. `T.IsSymmetric` is
Mathlib's global condition `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`, although the proof invokes it only at pairs
from `V`. `hΛ : 0 ≤ Λ` follows from `hpos` and `hle` at any nonzero `y ∈ V`; it is taken as a
hypothesis so that `y = 0` needs no separate case.

DERIVED: `0` occurs twice, as the lower bound of the form on `V` and as the lower bound on `Λ`; the
exponent `2` is the degree of the quadratic form in the Rayleigh bound. -/
theorem norm_le_of_rayleigh_le (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (V : Submodule ℝ E)
    (hinv : ∀ y ∈ V, T y ∈ V)
    (hpos : ∀ y ∈ V, (0 : ℝ) ≤ (inner ℝ (T y) y : ℝ))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hle : ∀ y ∈ V, (inner ℝ (T y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {y : E} (hy : y ∈ V) : ‖T y‖ ≤ Λ * ‖y‖ := by
  have hTy : T y ∈ V := hinv y hy
  have hcs := inner_map_cauchy_schwarz T hT V hpos hy hTy
  have e1 : (inner ℝ (T y) (T y) : ℝ) = ‖T y‖ * ‖T y‖ := real_inner_self_eq_norm_mul_norm (T y)
  have e2 := hle y hy
  have e3 := hle (T y) hTy
  have e3' := hpos (T y) hTy
  have hb : (0 : ℝ) ≤ Λ * ‖y‖ ^ 2 := mul_nonneg hΛ (sq_nonneg _)
  have H : (‖T y‖ * ‖T y‖) ^ 2 ≤ (Λ * ‖y‖ ^ 2) * (Λ * ‖T y‖ ^ 2) := by
    rw [← e1]
    exact le_trans hcs (mul_le_mul e2 e3 e3' hb)
  rcases eq_or_lt_of_le (norm_nonneg (T y)) with hz | hlt
  · rw [← hz]
    exact mul_nonneg hΛ (norm_nonneg y)
  · have hy2 : (0 : ℝ) < ‖T y‖ ^ 2 := by positivity
    have hsq : ‖T y‖ ^ 2 ≤ (Λ * ‖y‖) ^ 2 := by nlinarith [H, hy2]
    nlinarith [hsq, hlt, mul_nonneg hΛ (norm_nonneg y)]

#print axioms norm_le_of_rayleigh_le

/-- **An operator norm bound gives a Rayleigh bound**, the converse of `norm_le_of_rayleigh_le`.

Ordinary Cauchy–Schwarz: `⟪T y, y⟫ ≤ ‖T y‖ · ‖y‖ ≤ Λ ‖y‖ ^ 2`. Note what is NOT needed — no
symmetry, no invariance of `V`, no non-negativity of the form. Together with
`norm_le_of_rayleigh_le` this makes the two bounds interchangeable on a submodule where those
hypotheses do hold, so an estimate may be produced in whichever of the two shapes is convenient.

DERIVED: the exponent `2` is the degree of the norm in a Rayleigh quotient. -/
theorem rayleigh_le_of_norm_le (T : E →ₗ[ℝ] E) (V : Submodule ℝ E) {Λ : ℝ}
    (hnorm : ∀ y ∈ V, ‖T y‖ ≤ Λ * ‖y‖) {y : E} (hy : y ∈ V) :
    (inner ℝ (T y) y : ℝ) ≤ Λ * ‖y‖ ^ 2 := by
  calc (inner ℝ (T y) y : ℝ) ≤ ‖T y‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ (Λ * ‖y‖) * ‖y‖ := mul_le_mul_of_nonneg_right (hnorm y hy) (norm_nonneg _)
    _ = Λ * ‖y‖ ^ 2 := by ring

#print axioms rayleigh_le_of_norm_le

/-- **`‖T y‖` is log-convex along the orbit**: `‖T y‖ ^ 2 ≤ ‖y‖ · ‖T (T y)‖`, for `T` symmetric.

`⟪T y, T y⟫ = ⟪y, T (T y)⟫` by symmetry, and Cauchy–Schwarz bounds the right side by
`‖y‖ · ‖T (T y)‖`.

This is the step that lets a MANY-step estimate control a ONE-step one. Iterating it gives
`‖T y‖ ≤ ‖T ^ (2 ^ k) y‖ ^ (1 / 2 ^ k) · ‖y‖ ^ (1 - 1 / 2 ^ k)`, so a decay bound at large
separation — which is the shape strong coupling produces, geometric in the separation — bounds the
single-step Rayleigh quotient, and `lambdaTwo_le_of_norm_le` turns that into the gap. No absolute
lower bound on the form appears anywhere in that chain, which is the point: the obligation is
relative.

The iteration itself is not written here; this is its inductive step.

DERIVED: the exponent `2` is the square of the norm, the degree at which Cauchy–Schwarz is applied.
-/
theorem norm_map_sq_le (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (y : E) :
    ‖T y‖ ^ 2 ≤ ‖y‖ * ‖T (T y)‖ := by
  have h1 : ‖T y‖ ^ 2 = (inner ℝ y (T (T y)) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    exact hT y (T y)
  rw [h1]
  exact real_inner_le_norm _ _

#print axioms norm_map_sq_le

/-- **The squaring inequality at an arbitrary power**: `‖T ^ m y‖ ^ 2 ≤ ‖y‖ · ‖T ^ (2 * m) y‖`.

`norm_map_sq_le` is the case `m = 1`, and the general case is that same lemma applied to `T ^ m`,
which `LinearMap.IsSymmetric.pow` makes symmetric. Composing the operator with itself is `pow_add`,
and application of a product of endomorphisms is definitional.

DERIVED: the exponent `2` is the square of the norm, and the factor `2` in `2 * m` is the same
doubling — the lemma compares a power with its double. -/
theorem norm_pow_sq_le (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (m : ℕ) (y : E) :
    ‖(T ^ m) y‖ ^ 2 ≤ ‖y‖ * ‖(T ^ (2 * m)) y‖ := by
  have h := norm_map_sq_le (T ^ m) (hT.pow m) y
  have he : (T ^ m) ((T ^ m) y) = (T ^ (2 * m)) y := by
    rw [two_mul, pow_add]; rfl
  rwa [he] at h

#print axioms norm_pow_sq_le

/-- **A `2 ^ k`-step bound controls the one-step norm**:
`‖T y‖ ^ (2 ^ k) ≤ ‖y‖ ^ (2 ^ k - 1) · ‖T ^ (2 ^ k) y‖`.

The dyadic iteration of `norm_pow_sq_le`, by induction on `k`: squaring the inductive hypothesis and
applying the squaring inequality at `m = 2 ^ k` advances the exponent from `2 ^ k` to `2 ^ (k + 1)`.

**This is the step that lets strong coupling reach the gap without a lower bound.** Suppose the
`2 ^ k`-step norm decays, `‖T ^ n y‖ ≤ C ρ ^ n ‖y‖` — the shape a geometric correlation estimate
gives, since `n` is the separation. Then `‖T y‖ ^ (2 ^ k) ≤ C ρ ^ (2 ^ k) ‖y‖ ^ (2 ^ k)`, so
`‖T y‖ ≤ C ^ (1 / 2 ^ k) ρ ‖y‖`, and letting `k` grow drives the constant to one. `lambdaTwo` is
then below `ρ` by `lambdaTwo_le_of_norm_le`, and `ClayCapstone.clay_gap_of_lambdaTwo` closes.

Everything in that chain is an upper bound. No absolute lower bound on the form appears, which is
what distinguishes this route from the Gram and diagonal-dominance one — there the positive diagonal
is a requirement of the reduction, not of the obligation, and it is where the reflected-pairing
no-go applies.

The limit `k → ∞` is not taken here; this is the inequality it would be taken in.

DERIVED: `2` is the dyadic base — each step doubles the number of applications of `T`, because the
inductive step is a squaring; `1` is the single application of `T` on the left, which is the quantity
being bounded, and the unit subtracted from the exponent of `‖y‖` to account for it. -/
theorem norm_map_pow_le (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (y : E) (k : ℕ) :
    ‖T y‖ ^ (2 ^ k) ≤ ‖y‖ ^ (2 ^ k - 1) * ‖(T ^ (2 ^ k)) y‖ := by
  induction k with
  | zero => simp
  | succ j ih =>
      have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
      have hstep := norm_pow_sq_le T hT (2 ^ j) y
      have hdouble : 2 * 2 ^ j = 2 ^ (j + 1) := by omega
      rw [hdouble] at hstep
      calc ‖T y‖ ^ (2 ^ (j + 1)) = (‖T y‖ ^ (2 ^ j)) ^ 2 := by
            rw [← pow_mul]; congr 1
        _ ≤ (‖y‖ ^ (2 ^ j - 1) * ‖(T ^ (2 ^ j)) y‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) ih 2
        _ = ‖y‖ ^ ((2 ^ j - 1) * 2) * ‖(T ^ (2 ^ j)) y‖ ^ 2 := by
            rw [mul_pow, ← pow_mul]
        _ ≤ ‖y‖ ^ ((2 ^ j - 1) * 2) * (‖y‖ * ‖(T ^ (2 ^ (j + 1))) y‖) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = ‖y‖ ^ ((2 ^ j - 1) * 2 + 1) * ‖(T ^ (2 ^ (j + 1))) y‖ := by
            rw [pow_succ]; ring
        _ = ‖y‖ ^ (2 ^ (j + 1) - 1) * ‖(T ^ (2 ^ (j + 1))) y‖ := by
            congr 2
            omega

#print axioms norm_map_pow_le

/-- **A fixed constant cannot hold a geometric comparison open.** If `a ^ (2 ^ k) ≤ C · b ^ (2 ^ k)`
for every `k`, with `C` not depending on `k`, then `a ≤ b`.

This is the step that washes the constant out. Taking `2 ^ k`-th roots would give
`a ≤ C ^ (1 / 2 ^ k) · b`, and the root of a fixed constant tends to one — but the statement needs
no roots and no limit: if `b < a` then `b / a < 1`, and `exists_pow_lt_of_lt_one` produces a power
below `1 / C` directly, contradicting the hypothesis at that power. Archimedean descent, not
topology.

DERIVED: `2` is the dyadic base the hypothesis is indexed along, matching `norm_map_pow_le`'s; `1`
is the multiplicative unit the contradiction is drawn against; `0` is the lower bound on `a` and `b`
and the strict lower bound on `C`. -/
theorem le_of_pow_two_pow_le {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 < C)
    (h : ∀ k : ℕ, a ^ (2 ^ k) ≤ C * b ^ (2 ^ k)) : a ≤ b := by
  by_contra hcon
  push_neg at hcon
  have ha0 : 0 < a := lt_of_le_of_lt hb hcon
  set r : ℝ := b / a with hr
  have hr0 : 0 ≤ r := div_nonneg hb ha0.le
  have hr1 : r < 1 := (div_lt_one ha0).mpr hcon
  have hba : r * a = b := by rw [hr]; field_simp
  have hkey : ∀ k : ℕ, 1 ≤ C * r ^ (2 ^ k) := by
    intro k
    have hak : (0 : ℝ) < a ^ (2 ^ k) := pow_pos ha0 _
    have hb' : b ^ (2 ^ k) = r ^ (2 ^ k) * a ^ (2 ^ k) := by rw [← mul_pow, hba]
    have hh := h k
    rw [hb'] at hh
    refine le_of_mul_le_mul_right ?_ hak
    calc 1 * a ^ (2 ^ k) = a ^ (2 ^ k) := one_mul _
      _ ≤ C * (r ^ (2 ^ k) * a ^ (2 ^ k)) := hh
      _ = C * r ^ (2 ^ k) * a ^ (2 ^ k) := by ring
  have hk2 : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have hm : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
        have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
        omega
  have hbound : ∀ n : ℕ, 1 ≤ C * r ^ n := by
    intro n
    refine le_trans (hkey n) ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr0 hr1.le (hk2 n)) hC.le
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / C) hr1
  have hlt : C * r ^ n < 1 := by
    have hmul := mul_lt_mul_of_pos_left hn hC
    rwa [mul_one_div, div_self hC.ne'] at hmul
  linarith [hbound n]

#print axioms le_of_pow_two_pow_le

/-- **One factor of the rate moves an exponent.** `K · r ^ j = (K / r) · r ^ (j + 1)`.

Stated at `j` and `j + 1` rather than at `m - 1` and `m`, so that no natural subtraction appears and
the caller does the index arithmetic where the positivity is known.

DERIVED: `1` is the single factor of `r` moved across; `0` is the value `r` is required to differ
from, since the conversion divides by it. -/
theorem mul_pow_pred_eq (K r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    K * r ^ j = K / r * r ^ (j + 1) := by
  rw [pow_succ]
  field_simp

#print axioms mul_pow_pred_eq

/-- **A bound at the odd exponent, recast at the even one.**

The strong-coupling estimates bound a quantity by `K · r ^ k` for every `k` below the translation, so
at translation `2 * n` the exponent `2 * n - 1` is available. The gap obligation asks for a bound by
`r ^ (2 * n)`. One factor of the rate converts between them, at the cost of `K / r` in the constant;
`hK` is where the caller pays it.

The `n = 0` case is separate because `2 * n - 1` underflows there, so it is supplied by `h0`, a bound
at the contact value — which is what the obligation compares against anyway.

DERIVED: `0` is the index where the shifted exponent is unavailable and the lower bound on `r`; `1`
is the single factor of `r` moved across; `2` is the doubling relating the translation to the
exponent. -/
theorem le_mul_pow_of_shifted {K B r C : ℝ} (hr : r ≠ 0) (hr0 : 0 ≤ r)
    (hB : B ≤ C) (hK : K / r ≤ C) (P : ℕ → ℝ) (h0 : |P 0| ≤ B)
    (hpos : ∀ j : ℕ, |P (j + 1)| ≤ K * r ^ (2 * (j + 1) - 1)) :
    ∀ n : ℕ, |P n| ≤ C * r ^ (2 * n) := by
  intro n
  cases n with
  | zero => simpa using le_trans h0 hB
  | succ j =>
      have hj : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      have hj2 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      have hstep := hpos j
      rw [hj] at hstep
      rw [hj2]
      calc |P (j + 1)| ≤ K * r ^ (2 * j + 1) := hstep
        _ = K / r * r ^ (2 * j + 1 + 1) := mul_pow_pred_eq K r hr (2 * j + 1)
        _ ≤ C * r ^ (2 * j + 1 + 1) :=
            mul_le_mul_of_nonneg_right hK (by positivity)

#print axioms le_mul_pow_of_shifted

/-- **The same bound, in the obligation's squared shape.**

`ClayCapstone.clay_gap_of_two_point_decay` asks for a bound by `(C · ρ ^ n) ^ 2`. Taking `ρ` to be
the rate itself, that is `C ^ 2 · ρ ^ (2 * n)`, so the leading constant is the square root of the one
`le_mul_pow_of_shifted` produces.

DERIVED: `0` is the lower bound on the constant, needed for the square root to square back, the
value `r` differs from, and the index at which the shifted exponent is unavailable; `1` is the single
factor of `r` moved across and the offset placing that index outside the shifted range; `2` is the
obligation's own exponent, matching the form's quadratic degree. -/
theorem le_sq_mul_pow_of_shifted {K B r C : ℝ} (hr : r ≠ 0) (hr0 : 0 ≤ r) (hC : 0 ≤ C)
    (hB : B ≤ C) (hK : K / r ≤ C) (P : ℕ → ℝ) (h0 : |P 0| ≤ B)
    (hpos : ∀ j : ℕ, |P (j + 1)| ≤ K * r ^ (2 * (j + 1) - 1)) :
    ∀ n : ℕ, |P n| ≤ (Real.sqrt C * r ^ n) ^ 2 := by
  intro n
  have hcomm : (2 : ℕ) * n = n * 2 := Nat.mul_comm 2 n
  calc |P n| ≤ C * r ^ (2 * n) :=
        le_mul_pow_of_shifted hr hr0 hB hK P h0 hpos n
    _ = (Real.sqrt C * r ^ n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC, ← pow_mul, hcomm]

#print axioms le_sq_mul_pow_of_shifted

/-- **Geometric decay of the iterates bounds the operator in one step.** If
`‖T ^ n y‖ ≤ C · ρ ^ n · ‖y‖` at every `n`, then `‖T y‖ ≤ ρ · ‖y‖`.

`norm_map_pow_le` turns the `2 ^ k`-step bound into `‖T y‖ ^ (2 ^ k) ≤ C · (ρ ‖y‖) ^ (2 ^ k)`, and
`le_of_pow_two_pow_le` washes out `C`.

**This closes the relative route's chain, up to the estimate itself.** A geometric decay bound on the
iterates — which is what a correlation estimate at growing separation supplies, and it is an UPPER
bound throughout — now gives `lambdaTwo … ≤ ρ` through `lambdaTwo_le_of_norm_le`, and
`ClayCapstone.clay_gap_of_lambdaTwo` turns `ρ < 1` into the Clay spectral statement. At no point is a
lower bound on the form required.

What is not supplied here is `hdec`. The strong-coupling estimates in `StrongCoupling` bound
connected correlators at separation, not `‖T ^ n y‖` in the GNS space, and no declaration relates
the two.

DERIVED: `0` is the strict lower bound on `C` and the lower bound on `ρ`; `2` is the dyadic base
inherited from `norm_map_pow_le`; `1` is the single application of `T` being bounded, and the unit
subtracted in that lemma's exponent. -/
theorem norm_le_of_iterate_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {C ρ : ℝ}
    (hC : 0 < C) (hρ : 0 ≤ ρ) {y : E}
    (hdec : ∀ n : ℕ, ‖(T ^ n) y‖ ≤ C * ρ ^ n * ‖y‖) :
    ‖T y‖ ≤ ρ * ‖y‖ := by
  refine le_of_pow_two_pow_le (norm_nonneg _) (by positivity) hC (fun k => ?_)
  refine le_trans (norm_map_pow_le T hT y k) ?_
  have hone : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  calc ‖y‖ ^ (2 ^ k - 1) * ‖(T ^ (2 ^ k)) y‖
      ≤ ‖y‖ ^ (2 ^ k - 1) * (C * ρ ^ (2 ^ k) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hdec (2 ^ k)) (by positivity)
    _ = C * (ρ ^ (2 ^ k) * (‖y‖ ^ (2 ^ k - 1) * ‖y‖)) := by ring
    _ = C * (ρ ^ (2 ^ k) * ‖y‖ ^ (2 ^ k)) := by
        congr 2
        rw [← pow_succ]
        congr 1
        omega
    _ = C * (ρ * ‖y‖) ^ (2 ^ k) := by rw [mul_pow]

#print axioms norm_le_of_iterate_bound

/-- **An absolute bound on a submodule forces the operator to vanish there.**

If `‖T y‖ ≤ C` for every `y` in a submodule `V`, with `C` not scaled by `‖y‖`, then `T` is zero on
`V`. A submodule is closed under scaling, so the bound applies to every dilate of every vector at
once, and a nonzero value could be scaled past `C`.

**Why this is worth stating.** Every hypothesis on the route to the Clay spectral conclusion is a
RATIO — `norm_le_of_iterate_bound` asks `‖(T ^ n) y‖ ≤ C * ρ ^ n * ‖y‖`,
`ClayCapstone.clay_gap_of_form_decay` asks `form ((T ^ n) x) ((T ^ n) x) ≤ (C * ρ ^ n) ^ 2 * form x x`,
and `TransferGap.GapAt` is relative by definition. It would be natural to hope the factor of `‖y‖`
could be dropped, since the strong-coupling arm produces bounds with no such factor. This says it
cannot: the absolute form is not a weaker decay hypothesis but a vacuous one.

The collapse is for ONE constant serving the whole submodule. With the constant allowed per vector,
an absolute bound at a fixed `y ≠ 0` is the ratio form at `C = K / ‖y‖`, and
`norm_le_of_absolute_iterate_bound` records that: per-vector absolute decay gives the rate.

DERIVED: `0` is the value `T` takes on `V` and the strict lower bound the proof puts on `‖T y‖`;
`1` is the amount by which the scaled vector is pushed past `C`. -/
theorem eq_zero_of_norm_le_const {V : Submodule ℝ E} {T : E →ₗ[ℝ] E} {C : ℝ}
    (h : ∀ y ∈ V, ‖T y‖ ≤ C) {y : E} (hy : y ∈ V) : T y = 0 := by
  by_contra hne
  have hpos : 0 < ‖T y‖ := norm_pos_iff.mpr hne
  have hne0 : ‖T y‖ ≠ 0 := ne_of_gt hpos
  have hq : (0 : ℝ) < (C + 1) / ‖T y‖ := by
    have hC : 0 < C := lt_of_lt_of_le hpos (h y hy)
    positivity
  have hmul : (C + 1) / ‖T y‖ * ‖T y‖ = C + 1 := by field_simp
  have ht := h (((C + 1) / ‖T y‖) • y) (V.smul_mem _ hy)
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hq, hmul] at ht
  linarith

#print axioms eq_zero_of_norm_le_const

/-- **An absolute iterate bound on a submodule is vacuous**, at every power.

`eq_zero_of_norm_le_const` at `T ^ n`. This is `norm_le_of_iterate_bound`'s hypothesis with the
factor of `‖y‖` removed, and removing it collapses the operator to zero on `V` rather than giving a
rate — so the contraction that `lambdaTwo_le_of_iterate_bound` extracts from the ratio form has no
counterpart here.

Read together with `HalfLineTransfer.no_rate_of_shift_transfer`, which shows a contraction rate on the
vacuum complement at finite periodic extent forces that complement to be zero: both are collapses,
and both say the content of a decay hypothesis lives entirely in what it is measured AGAINST.

DERIVED: `0` is the value each iterate takes on `V`. -/
theorem eq_zero_of_iterate_norm_le {V : Submodule ℝ E} {T : E →ₗ[ℝ] E} {C ρ : ℝ}
    (hdec : ∀ y ∈ V, ∀ n : ℕ, ‖(T ^ n) y‖ ≤ C * ρ ^ n) {y : E} (hy : y ∈ V) (n : ℕ) :
    (T ^ n) y = 0 :=
  eq_zero_of_norm_le_const (C := C * ρ ^ n) (fun z hz => hdec z hz n) hy

#print axioms eq_zero_of_iterate_norm_le

/-- **Absolute decay of the iterates at one vector bounds `T` at that vector.**

`‖Tⁿ y‖ ≤ K · ρⁿ` with no factor of `‖y‖` is `norm_le_of_iterate_bound`'s hypothesis at
`C = K / ‖y‖`: the constant is chosen after the vector, so it absorbs the vector's own norm. At
`n = 0` the bound reads `‖y‖ ≤ K`, which makes that constant positive whenever `y ≠ 0`.

This is what lets an absolute cluster estimate — the form a strong-coupling expansion produces — feed
the spectral bound directly, one vector at a time, with no lower bound on any pairing.

DERIVED: `0` is the lower bound on `ρ` and the exponent at which the bound reads `‖y‖ ≤ K`. -/
theorem norm_le_of_absolute_iterate_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {K ρ : ℝ}
    (hρ : 0 ≤ ρ) {y : E} (hdec : ∀ n : ℕ, ‖(T ^ n) y‖ ≤ K * ρ ^ n) :
    ‖T y‖ ≤ ρ * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hK : ‖y‖ ≤ K := by simpa using hdec 0
  have hKpos : 0 < K := lt_of_lt_of_le hy0 hK
  refine norm_le_of_iterate_bound T hT (C := K / ‖y‖) (div_pos hKpos hy0) hρ (fun n => ?_)
  calc ‖(T ^ n) y‖ ≤ K * ρ ^ n := hdec n
    _ = K / ‖y‖ * ρ ^ n * ‖y‖ := by field_simp

#print axioms norm_le_of_absolute_iterate_bound

/-- The set `{r | ∃ y ∈ V, y ≠ 0 ∧ r = ⟪T y, y⟫ / ‖y‖ ^ 2}`: the Rayleigh quotients of `T` at the
nonzero vectors of `V`. It may be empty (when `V` is the zero submodule) and may be unbounded above;
both are handled by hypotheses on the theorems that use `lambdaTwo`.

DERIVED: `0` is the vector excluded from the index set, at which the quotient is undefined; the
exponent `2` is the degree of the norm in a Rayleigh quotient. -/
def rayleighSet (T : E →ₗ[ℝ] E) (V : Submodule ℝ E) : Set ℝ :=
  {r | ∃ y ∈ V, y ≠ 0 ∧ r = (inner ℝ (T y) y : ℝ) / ‖y‖ ^ 2}

#print axioms rayleighSet

/-- `sSup (rayleighSet T V)`: the supremum of the Rayleigh quotient over the nonzero vectors of `V`.
With `V` the vacuum complement and `T` a transfer operator this is the subdominant eigenvalue read
variationally.

Scope: the definition involves no enumeration or ordering of a spectrum, no compactness and no
finite dimension, and it does not assert the supremum is attained. When `rayleighSet T V` is empty
or unbounded above, `sSup` returns Lean's junk value, which is why
`lambdaTwo_le_of_rayleigh_le` carries `Nonempty` and the others carry `BddAbove`.

DERIVED: no numeral appears in the statement. -/
noncomputable def lambdaTwo (T : E →ₗ[ℝ] E) (V : Submodule ℝ E) : ℝ := sSup (rayleighSet T V)

#print axioms lambdaTwo

/-- If `rayleighSet T V` is nonempty and `⟪T y, y⟫ ≤ Λ * ‖y‖ ^ 2` on `V`, then `lambdaTwo T V ≤ Λ`.
By `csSup_le`, each element of the set is a quotient at some nonzero `y ∈ V`, and dividing the
hypothesis by the positive `‖y‖ ^ 2` bounds it by `Λ`.

Scope: nonemptiness is required because `sSup ∅` is `0` by convention, which would make the
conclusion a statement about a junk value at negative `Λ`.

DERIVED: the exponent `2` is the degree of the norm in the Rayleigh bound. No other numeral appears
in the statement. -/
theorem lambdaTwo_le_of_rayleigh_le (T : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hne : (rayleighSet T V).Nonempty) {Λ : ℝ}
    (hle : ∀ y ∈ V, (inner ℝ (T y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    lambdaTwo T V ≤ Λ := by
  refine csSup_le hne ?_
  rintro r ⟨y, hyV, hy0, rfl⟩
  have hn : (0 : ℝ) < ‖y‖ ^ 2 := by
    have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
    positivity
  rw [div_le_iff₀ hn]
  linarith [hle y hyV]

#print axioms lambdaTwo_le_of_rayleigh_le

/-- **A contraction's Rayleigh set is bounded above, by one.**

Cauchy–Schwarz gives `⟪T y, y⟫ ≤ ‖T y‖ · ‖y‖`, and a norm-contraction bounds that by `‖y‖ ^ 2`, so
every quotient is at most one.

This matters because `BddAbove (rayleighSet …)` is carried as a hypothesis by
`lambdaTwo_le_of_rayleigh_le`'s consumers and by `ClayCapstone.clay_gap_of_lambdaTwo`. For a transfer
operator it is not an assumption: `Transfer.TransferData`'s `T_contract` field already makes the
operator a contraction, so the hypothesis is discharged rather than assumed.

DERIVED: `1` is the bound, which is the contraction constant — the operator does not expand, so no
quotient exceeds it; `2` is the degree of the norm in a Rayleigh quotient; `0` is the vector excluded
from the index set. -/
theorem bddAbove_rayleighSet_of_norm_le (T : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hnorm : ∀ y : E, ‖T y‖ ≤ ‖y‖) : BddAbove (rayleighSet T V) := by
  refine ⟨1, ?_⟩
  rintro r ⟨y, _, hy0, rfl⟩
  have hy : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  have hn : (0 : ℝ) < ‖y‖ ^ 2 := by positivity
  rw [div_le_one hn]
  calc (inner ℝ (T y) y : ℝ) ≤ ‖T y‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right (hnorm y) (norm_nonneg _)
    _ = ‖y‖ ^ 2 := by ring

#print axioms bddAbove_rayleighSet_of_norm_le

/-- **The Rayleigh set is nonempty as soon as `V` holds a nonzero vector.**

The other side condition `lambdaTwo_le_of_rayleigh_le` carries. It is a statement about `V` alone,
not about the operator, and it fails only for `V = ⊥`.

DERIVED: `0` is the vector `V` must contain something other than. -/
theorem rayleighSet_nonempty (T : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    {y : E} (hyV : y ∈ V) (hy0 : y ≠ 0) : (rayleighSet T V).Nonempty :=
  ⟨(inner ℝ (T y) y : ℝ) / ‖y‖ ^ 2, y, hyV, hy0, rfl⟩

#print axioms rayleighSet_nonempty

/-- **An operator norm bound bounds `lambdaTwo`.** `rayleigh_le_of_norm_le` then
`lambdaTwo_le_of_rayleigh_le`.

This is the form in which the relative route would consume a strong-coupling estimate:
`ClayCapstone.clay_gap_of_lambdaTwo` takes exactly a `lambdaTwo … ≤ Λ` with `Λ < 1`, and this
supplies it from a bound on how far the transfer operator contracts, with no absolute lower bound on
the form anywhere.

DERIVED: no numeral occurs; `Λ` and `V` are the caller's. -/
theorem lambdaTwo_le_of_norm_le (T : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hne : (rayleighSet T V).Nonempty) {Λ : ℝ}
    (hnorm : ∀ y ∈ V, ‖T y‖ ≤ Λ * ‖y‖) :
    lambdaTwo T V ≤ Λ :=
  lambdaTwo_le_of_rayleigh_le T V hne (fun y hy => rayleigh_le_of_norm_le T V hnorm hy)

#print axioms lambdaTwo_le_of_norm_le

/-- **Per-vector absolute decay bounds `lambdaTwo`.** Each `y ∈ V` may carry its own constant.

`norm_le_of_absolute_iterate_bound` at each vector, then `lambdaTwo_le_of_norm_le`.

DERIVED: `0` is the lower bound on `ρ`. -/
theorem lambdaTwo_le_of_absolute_iterate_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (V : Submodule ℝ E) (hne : (rayleighSet T V).Nonempty) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdec : ∀ y ∈ V, ∃ K : ℝ, ∀ n : ℕ, ‖(T ^ n) y‖ ≤ K * ρ ^ n) :
    lambdaTwo T V ≤ ρ :=
  lambdaTwo_le_of_norm_le T V hne (fun y hy => by
    obtain ⟨K, hK⟩ := hdec y hy
    exact norm_le_of_absolute_iterate_bound T hT hρ hK)

#print axioms lambdaTwo_le_of_absolute_iterate_bound

/-- **The vectors whose iterates decay geometrically at rate `ρ` form a submodule.**

`‖Tⁿ (y + z)‖ ≤ ‖Tⁿ y‖ + ‖Tⁿ z‖` adds the constants, and `‖Tⁿ (c • y)‖ = |c| · ‖Tⁿ y‖` scales one. So decay
proved on a spanning set holds on its span: a cluster estimate on a generating family of observables
covers every finite combination of them.

DERIVED: `0` is the zero vector's constant. -/
def decaySubmodule (T : E →ₗ[ℝ] E) (ρ : ℝ) : Submodule ℝ E where
  carrier := {y | ∃ K : ℝ, ∀ n : ℕ, ‖(T ^ n) y‖ ≤ K * ρ ^ n}
  add_mem' := by
    rintro y z ⟨Ky, hy⟩ ⟨Kz, hz⟩
    refine ⟨Ky + Kz, fun n => ?_⟩
    rw [map_add]
    calc ‖(T ^ n) y + (T ^ n) z‖ ≤ ‖(T ^ n) y‖ + ‖(T ^ n) z‖ := norm_add_le _ _
      _ ≤ Ky * ρ ^ n + Kz * ρ ^ n := add_le_add (hy n) (hz n)
      _ = (Ky + Kz) * ρ ^ n := by ring
  zero_mem' := ⟨0, fun n => by simp⟩
  smul_mem' := by
    rintro c y ⟨K, hy⟩
    refine ⟨|c| * K, fun n => ?_⟩
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc |c| * ‖(T ^ n) y‖ ≤ |c| * (K * ρ ^ n) := mul_le_mul_of_nonneg_left (hy n) (abs_nonneg c)
      _ = |c| * K * ρ ^ n := by ring

#print axioms decaySubmodule

/-- **Decay on a spanning set bounds `lambdaTwo`.** If `V` lies in the span of `S` and every element
of `S` decays at rate `ρ`, then `lambdaTwo T V ≤ ρ`: `Submodule.span_le` puts the span inside
`decaySubmodule`, and `lambdaTwo_le_of_absolute_iterate_bound` finishes.

DERIVED: `0` is the lower bound on `ρ`. -/
theorem lambdaTwo_le_of_span_decay (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (V : Submodule ℝ E)
    (hne : (rayleighSet T V).Nonempty) {ρ : ℝ} (hρ : 0 ≤ ρ) (S : Set E)
    (hV : V ≤ Submodule.span ℝ S)
    (hS : ∀ s ∈ S, ∃ K : ℝ, ∀ n : ℕ, ‖(T ^ n) s‖ ≤ K * ρ ^ n) :
    lambdaTwo T V ≤ ρ := by
  have hspan : Submodule.span ℝ S ≤ decaySubmodule T ρ := Submodule.span_le.mpr hS
  exact lambdaTwo_le_of_absolute_iterate_bound T hT V hne hρ (fun y hy => hspan (hV hy))

#print axioms lambdaTwo_le_of_span_decay

/-- **Geometric decay of the iterates, uniform over `V`, bounds `lambdaTwo`.**

`norm_le_of_iterate_bound` at each `y ∈ V`, then `lambdaTwo_le_of_norm_le`.

This is the interface `ClayCapstone.clay_gap_of_lambdaTwo` consumes: with `ρ < 1` it yields the Clay
spectral statement. The whole chain from here to the gap is built and axiom-clean, and every step in
it is an UPPER bound — no lower bound on the reflection form appears anywhere, which is what
separates this route from the Gram and diagonal-dominance one.

The remaining obligation is `hdec` itself: geometric decay of `‖T ^ n y‖` in the GNS space. The
strong-coupling estimates bound connected correlators at growing separation, which is the same
physical statement, but no declaration relates the two objects.

DERIVED: `0` is the strict lower bound on `C` and the lower bound on `ρ`; the numerals in the proof
are `norm_le_of_iterate_bound`'s. -/
theorem lambdaTwo_le_of_iterate_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (V : Submodule ℝ E)
    (hne : (rayleighSet T V).Nonempty) {C ρ : ℝ} (hC : 0 < C) (hρ : 0 ≤ ρ)
    (hdec : ∀ y ∈ V, ∀ n : ℕ, ‖(T ^ n) y‖ ≤ C * ρ ^ n * ‖y‖) :
    lambdaTwo T V ≤ ρ :=
  lambdaTwo_le_of_norm_le T V hne
    (fun y hy => norm_le_of_iterate_bound T hT hC hρ (hdec y hy))

#print axioms lambdaTwo_le_of_iterate_bound

/-- If `rayleighSet T V` is bounded above, then `⟪T y, y⟫ ≤ lambdaTwo T V * ‖y‖ ^ 2` at every
`y ∈ V`. At `y = 0` both sides vanish; otherwise the quotient at `y` belongs to the set, `le_csSup`
bounds it by the supremum, and multiplying through by the positive `‖y‖ ^ 2` gives the statement.

Scope: `BddAbove` is what makes `sSup` an upper bound rather than a junk value.

DERIVED: the exponent `2` is the degree of the norm in the Rayleigh bound. No other numeral appears
in the statement. -/
theorem rayleigh_le_of_lambdaTwo_le (T : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hbdd : BddAbove (rayleighSet T V)) {y : E} (hy : y ∈ V) :
    (inner ℝ (T y) y : ℝ) ≤ lambdaTwo T V * ‖y‖ ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hn : (0 : ℝ) < ‖y‖ ^ 2 := by
      have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
      positivity
    have hmem : (inner ℝ (T y) y : ℝ) / ‖y‖ ^ 2 ∈ rayleighSet T V := ⟨y, hy, hy0, rfl⟩
    have hle : (inner ℝ (T y) y : ℝ) / ‖y‖ ^ 2 ≤ lambdaTwo T V := le_csSup hbdd hmem
    rw [div_le_iff₀ hn] at hle
    exact hle

#print axioms rayleigh_le_of_lambdaTwo_le

/-- **Two forms close at every vector have close subdominant suprema.**
If `|⟪T₁ y, y⟫ - ⟪T₂ y, y⟫| ≤ d‖y‖²` on `V`, then `|lambdaTwo T₁ V - lambdaTwo T₂ V| ≤ d`.

This is how a bound on a subdominant eigenvalue becomes reachable: the eigenvalue is a SUPREMUM,
which is hard to bound directly and easy to bound pointwise. `csSup_le` on one side, `le_csSup` on
the other, and the pointwise hypothesis between them. Nothing here is about transfer operators — it
is a statement about two suprema of quotients over one index set.

⛔ BOTH OPERATORS ACT ON THE SAME SPACE, and that is a real limit on where this applies. A family of
`TransferData` indexed by a coupling has a GNS space that varies with the coupling, so the Rayleigh
suprema at two couplings are suprema over different types and this lemma does not compare them. See
`ClayCapstone.clay_gap_on_interval`, whose `hlip` is exactly that comparison.

Nonemptiness is stated as `∃ y ∈ V, y ≠ 0` rather than on either `rayleighSet`, because one witness
serves both: the two sets share `V`, and the quotient is defined at every nonzero vector of it. Both
`BddAbove`s are load-bearing — `sSup` of a set unbounded above is a junk value on that side.

DERIVED: the exponent `2` is the degree of the norm in a Rayleigh quotient; `0` is the vector
excluded from the index set, where the quotient is undefined. -/
theorem lambdaTwo_dist_le (T₁ T₂ : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hne : ∃ y ∈ V, y ≠ 0)
    (hb₁ : BddAbove (rayleighSet T₁ V)) (hb₂ : BddAbove (rayleighSet T₂ V))
    {d : ℝ} (hd : ∀ y ∈ V, y ≠ 0 →
      |(inner ℝ (T₁ y) y : ℝ) - (inner ℝ (T₂ y) y : ℝ)| ≤ d * ‖y‖ ^ 2) :
    |lambdaTwo T₁ V - lambdaTwo T₂ V| ≤ d := by
  obtain ⟨w, hwV, hw0⟩ := hne
  have hstep : ∀ S₁ S₂ : E →ₗ[ℝ] E, BddAbove (rayleighSet S₂ V) →
      (∀ y ∈ V, y ≠ 0 → (inner ℝ (S₁ y) y : ℝ) - (inner ℝ (S₂ y) y : ℝ) ≤ d * ‖y‖ ^ 2) →
      lambdaTwo S₁ V ≤ lambdaTwo S₂ V + d := by
    intro S₁ S₂ hb hle
    refine csSup_le ⟨_, w, hwV, hw0, rfl⟩ ?_
    rintro r ⟨y, hyV, hy0, rfl⟩
    have hn : (0 : ℝ) < ‖y‖ ^ 2 := by
      have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
      positivity
    have h₂ : (inner ℝ (S₂ y) y : ℝ) / ‖y‖ ^ 2 ≤ lambdaTwo S₂ V :=
      le_csSup hb ⟨y, hyV, hy0, rfl⟩
    rw [div_le_iff₀ hn] at h₂
    rw [div_le_iff₀ hn]
    have hy := hle y hyV hy0
    nlinarith [h₂, hy, hn]
  have h₁₂ := hstep T₁ T₂ hb₂ (fun y hy hy0 => (abs_le.mp (hd y hy hy0)).2)
  have h₂₁ := hstep T₂ T₁ hb₁ (fun y hy hy0 => by
    have := (abs_le.mp (hd y hy hy0)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms lambdaTwo_dist_le

/-- If the form is nonnegative on `V`, `rayleighSet T V` is bounded above, and `V` contains some
nonzero `y₀`, then `0 ≤ lambdaTwo T V`. The quotient at `y₀` is nonnegative and lies below the
supremum.

The nonzero witness is what makes the set nonempty; without it `sSup ∅` would be the junk value.
This is the sign `norm_le_lambdaTwo_mul` needs in order to apply `norm_le_of_rayleigh_le`.

DERIVED: `0` occurs three times — the lower bound of the form on `V`, the value `y₀` is assumed to
differ from, and the lower bound concluded for `lambdaTwo T V`. -/
theorem lambdaTwo_nonneg (T : E →ₗ[ℝ] E) (V : Submodule ℝ E)
    (hbdd : BddAbove (rayleighSet T V))
    (hpos : ∀ y ∈ V, (0 : ℝ) ≤ (inner ℝ (T y) y : ℝ))
    {y₀ : E} (hy₀ : y₀ ∈ V) (hy₀0 : y₀ ≠ 0) : 0 ≤ lambdaTwo T V := by
  have hmem : (inner ℝ (T y₀) y₀ : ℝ) / ‖y₀‖ ^ 2 ∈ rayleighSet T V := ⟨y₀, hy₀, hy₀0, rfl⟩
  have hle : (inner ℝ (T y₀) y₀ : ℝ) / ‖y₀‖ ^ 2 ≤ lambdaTwo T V := le_csSup hbdd hmem
  have h0 : (0 : ℝ) ≤ (inner ℝ (T y₀) y₀ : ℝ) / ‖y₀‖ ^ 2 :=
    div_nonneg (hpos y₀ hy₀) (sq_nonneg _)
  linarith

#print axioms lambdaTwo_nonneg

/-- `‖T y‖ ≤ lambdaTwo T V * ‖y‖` at every `y ∈ V`, for `T` symmetric, `V` invariant and carrying a
nonnegative form, `rayleighSet T V` bounded above, and some nonzero `y₀ ∈ V`. It is
`norm_le_of_rayleigh_le` with `Λ := lambdaTwo T V`, whose nonnegativity is `lambdaTwo_nonneg` and
whose Rayleigh bound is `rayleigh_le_of_lambdaTwo_le`.

Scope: no step requires the supremum to be attained, and no compactness or spectral theorem is used.

DERIVED: `0` occurs twice, as the lower bound of the form on `V` and as the value `y₀` is assumed to
differ from. No other numeral appears in the statement. -/
theorem norm_le_lambdaTwo_mul (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (V : Submodule ℝ E)
    (hinv : ∀ y ∈ V, T y ∈ V)
    (hpos : ∀ y ∈ V, (0 : ℝ) ≤ (inner ℝ (T y) y : ℝ))
    (hbdd : BddAbove (rayleighSet T V))
    {y₀ : E} (hy₀ : y₀ ∈ V) (hy₀0 : y₀ ≠ 0)
    {y : E} (hy : y ∈ V) : ‖T y‖ ≤ lambdaTwo T V * ‖y‖ :=
  norm_le_of_rayleigh_le T hT V hinv hpos
    (lambdaTwo_nonneg T V hbdd hpos hy₀ hy₀0)
    (fun _ hz => rayleigh_le_of_lambdaTwo_le T V hbdd hz) hy

#print axioms norm_le_lambdaTwo_mul

end Generic

/-! ## §2 §1 applied to `Transfer.TransferData`'s operator on the vacuum complement

`Transfer.TransferData` carries `Tq_isSymmetric` and `Tq_vacGNS`: the operator is symmetric for the
reflection form and fixes the vacuum. Those two facts make the vacuum complement invariant
(`VolumeRate.inner_vac_Tq`), which is the hypothesis §1's lemma needs. -/

section Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The submodule `{y | ⟪D.vacGNS, y⟫ = 0}` of `GNS D.toReflForm`, with the three closure fields
proved from additivity and homogeneity of the inner product in its right argument. Membership is the
equation `⟪Ω, y⟫ = 0` definitionally (`mem_vacPerp` is `Iff.rfl`), which is the form
`VolumeRate.rp_sub_geometric` and `HalfLineTransfer` state their hypotheses in.

`vacPerp_eq_orthogonal` identifies it with `(Submodule.span ℝ {D.vacGNS})ᗮ`, so this is a spelling
rather than a second notion.

DERIVED: `0` in the carrier is orthogonality to the vacuum. -/
def vacPerp (D : TransferData A) : Submodule ℝ (GNS D.toReflForm) where
  carrier := {y | (inner ℝ D.vacGNS y : ℝ) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [inner_add_right, ha, hb]
    ring
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [real_inner_smul_right, ha]
    ring

#print axioms vacPerp

/-- `y ∈ vacPerp D ↔ ⟪D.vacGNS, y⟫ = 0`, by `Iff.rfl`. Marked `@[simp]`, so consumers stating their
hypotheses as the equation need no rewriting step.

DERIVED: `0` is orthogonality to the vacuum, the same `0` as in `vacPerp`'s carrier. -/
@[simp] theorem mem_vacPerp (D : TransferData A) {y : GNS D.toReflForm} :
    y ∈ vacPerp D ↔ (inner ℝ D.vacGNS y : ℝ) = 0 := Iff.rfl

#print axioms mem_vacPerp

/-- `vacPerp D = (Submodule.span ℝ {D.vacGNS})ᗮ`, by extensionality through `mem_vacPerp` and
`Submodule.mem_orthogonal_singleton_iff_inner_right`. So `vacPerp` is a spelling of Mathlib's
orthogonal complement of the vacuum line rather than a second notion; it is written out so that
`mem_vacPerp` is `Iff.rfl`, which the orthogonal-complement form is not.

DERIVED: no numeral appears in the statement. -/
theorem vacPerp_eq_orthogonal (D : TransferData A) :
    vacPerp D = (Submodule.span ℝ {D.vacGNS})ᗮ :=
  Submodule.ext fun _ =>
    (mem_vacPerp D).trans Submodule.mem_orthogonal_singleton_iff_inner_right.symm

#print axioms vacPerp_eq_orthogonal

/-- `∀ y ∈ vacPerp D, D.Tq y ∈ vacPerp D`: the vacuum complement is invariant under the transfer
operator, in submodule form. It is `VolumeRate.inner_vac_Tq`, which moves `Tq` across the inner
product by `Tq_isSymmetric` and uses `Tq_vacGNS` to return to the hypothesis.

This is the `hinv` hypothesis of `norm_le_of_rayleigh_le`.

DERIVED: no numeral appears in the statement. -/
theorem vacPerp_invariant (D : TransferData A) :
    ∀ y ∈ vacPerp D, D.Tq y ∈ vacPerp D :=
  fun _ hy => MassGap.VolumeRate.inner_vac_Tq D hy

#print axioms vacPerp_invariant

/-- From `0 ≤ Λ`, nonnegativity of `⟪Tq y, y⟫` on the vacuum complement (`hpos`), and the Rayleigh
bound `⟪Tq y, y⟫ ≤ Λ * ‖y‖ ^ 2` there (`hray`), every vacuum-orthogonal `y` satisfies
`‖D.Tq y‖ ≤ Λ * ‖y‖`. It is `norm_le_of_rayleigh_le` at `T := D.Tq`, `V := vacPerp D`, with symmetry
from `TransferData.Tq_isSymmetric` and invariance from `vacPerp_invariant`.

This is the hypothesis `VolumeRate.rp_sub_geometric`, `VolumeRate.rp_gap_of_one_cut` and
`HalfLineTransfer` take.

Scope: `hpos` is a separate hypothesis, not a consequence of `TransferData.T_contract`, which bounds
the magnitude of the form and not its sign. It is not a field of `TransferData`.

DERIVED: `0` occurs five times — the lower bound on `Λ`, the orthogonality condition in `hpos`, the
lower bound of the form in `hpos`, the orthogonality condition in `hray`, and the orthogonality of
`y`. The exponent `2` is the degree of the norm in the Rayleigh bound. -/
theorem norm_Tq_le_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {y : GNS D.toReflForm} (hy : (inner ℝ D.vacGNS y : ℝ) = 0) :
    ‖D.Tq y‖ ≤ Λ * ‖y‖ :=
  norm_le_of_rayleigh_le D.Tq (TransferData.Tq_isSymmetric D) (vacPerp D)
    (vacPerp_invariant D) (fun z hz => hpos z hz) hΛ (fun z hz => hray z hz) hy

#print axioms norm_Tq_le_of_rayleigh

/-- `‖(D.Tq ^ n) x‖ ≤ Λ ^ n * ‖x‖` at every `n`, for vacuum-orthogonal `x`, from `0 ≤ Λ` and the same
nonnegativity and Rayleigh hypotheses as `norm_Tq_le_of_rayleigh`. It is `VolumeRate.norm_Tq_pow_le`
with its per-step hypothesis supplied by that theorem.

DERIVED: `0` occurs five times — the lower bound on `Λ`, the orthogonality condition in `hpos`, the
lower bound of the form in `hpos`, the orthogonality condition in `hray`, and the orthogonality of
`x`. The exponent `2` is the degree of the norm in the Rayleigh bound. -/
theorem Tq_pow_norm_le_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {x : GNS D.toReflForm} (hx : (inner ℝ D.vacGNS x : ℝ) = 0) (n : ℕ) :
    ‖(D.Tq ^ n) x‖ ≤ Λ ^ n * ‖x‖ :=
  MassGap.VolumeRate.norm_Tq_pow_le D hΛ
    (fun _ hz => norm_Tq_le_of_rayleigh D hΛ hpos hray hz) hx n

#print axioms Tq_pow_norm_le_of_rayleigh

/-- With `0 ≤ Λ < 1` and the same nonnegativity and Rayleigh hypotheses,
`Tendsto (fun n => ‖(D.Tq ^ n) x‖) atTop (nhds 0)` for vacuum-orthogonal `x`. It is
`VolumeRate.rp_gap_of_one_cut` with its per-step hypothesis supplied by `norm_Tq_le_of_rayleigh`.

Scope: `n` counts applications of `Tq`, not a volume.

DERIVED: `0` occurs six times — the lower bound on `Λ`, the orthogonality condition in `hpos`, the
lower bound of the form in `hpos`, the orthogonality condition in `hray`, the orthogonality of `x`,
and the limit point `nhds 0`. `1` is the upper bound on `Λ`, the value the vacuum's own Rayleigh
quotient takes and which the powers must sit below to vanish. The exponent `2` is the degree of the
norm in the Rayleigh bound. -/
theorem tendsto_zero_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {x : GNS D.toReflForm} (hx : (inner ℝ D.vacGNS x : ℝ) = 0) :
    Filter.Tendsto (fun n => ‖(D.Tq ^ n) x‖) Filter.atTop (nhds 0) :=
  MassGap.VolumeRate.rp_gap_of_one_cut D hΛ hΛ1
    (fun _ hz => norm_Tq_le_of_rayleigh D hΛ hpos hray hz) hx

#print axioms tendsto_zero_of_rayleigh

/-! ## §3 Lag two, and the shape `SpectralBound` consumes

At lag two symmetry turns `⟪x, Tq ^ 2 x⟫` into `‖Tq x‖ ^ 2` exactly, so the bound is the operator
bound squared and no second Cauchy–Schwarz on the correlator is needed. -/

/-- `⟪x, (D.Tq ^ 2) x⟫ = ‖D.Tq x‖ * ‖D.Tq x‖` at every `x`. Expanding `Tq ^ 2` and moving one `Tq`
across by `TransferData.Tq_isSymmetric` leaves `⟪Tq x, Tq x⟫`, which
`real_inner_self_eq_norm_mul_norm` evaluates.

Scope: no hypothesis beyond the structure's own symmetry; `x` need not be vacuum-orthogonal.

DERIVED: `2` is the power of `Tq`, the lag index, and it is the same `2` that makes the right side a
square. -/
theorem inner_Tq_two_eq (D : TransferData A) (x : GNS D.toReflForm) :
    (inner ℝ x ((D.Tq ^ 2) x) : ℝ) = ‖D.Tq x‖ * ‖D.Tq x‖ := by
  have h2 : (D.Tq ^ 2) x = D.Tq (D.Tq x) := by
    rw [pow_two]
    rfl
  rw [h2, real_inner_comm, TransferData.Tq_isSymmetric D (D.Tq x) x,
    real_inner_self_eq_norm_mul_norm]

#print axioms inner_Tq_two_eq

/-- For vacuum-orthogonal `x` and the same hypotheses as `norm_Tq_le_of_rayleigh`,
`⟪x, (D.Tq ^ 2) x⟫ ≤ Λ ^ 2 * ‖x‖ ^ 2`. `inner_Tq_two_eq` rewrites the left side as `‖D.Tq x‖ ^ 2`
and `norm_Tq_le_of_rayleigh` bounds `‖D.Tq x‖` by `Λ * ‖x‖`.

DERIVED: `0` occurs five times — the lower bound on `Λ`, the orthogonality condition in `hpos`, the
lower bound of the form in `hpos`, the orthogonality condition in `hray`, and the orthogonality of
`x`. `2` occurs four times — the exponent in the Rayleigh bound, the power of `Tq` (the lag index),
and the two squares in the conclusion, both forced by that lag. -/
theorem inner_Tq_two_le_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {x : GNS D.toReflForm} (hx : (inner ℝ D.vacGNS x : ℝ) = 0) :
    (inner ℝ x ((D.Tq ^ 2) x) : ℝ) ≤ Λ ^ 2 * ‖x‖ ^ 2 := by
  have hstep : ‖D.Tq x‖ ≤ Λ * ‖x‖ := norm_Tq_le_of_rayleigh D hΛ hpos hray hx
  have hnn : (0 : ℝ) ≤ ‖D.Tq x‖ := norm_nonneg _
  rw [inner_Tq_two_eq]
  nlinarith [hstep, hnn, mul_nonneg hΛ (norm_nonneg x)]

#print axioms inner_Tq_two_le_of_rayleigh

/-- `MassGap.wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * MassGap.wilsonCorrAt 3 β 0`, from the Rayleigh hypotheses
together with two identifications supplied by the caller:

* `h0 : wilsonCorrAt 3 β 0 = ‖x‖ ^ 2` — the contact value is the trial vector's squared norm;
* `h2 : wilsonCorrAt 3 β 2 = ⟪x, (D.Tq ^ 2) x⟫` — the lag-two value is its two-step two-point
  function.

The proof rewrites by both and applies `inner_Tq_two_le_of_rayleigh`.

Scope: `h0` and `h2` are equations between real numbers and are hypotheses; nothing in them relates
`D` to the Wilson measure, so a `D` chosen to match the numbers satisfies them. Together with
`hx : ⟪Ω, x⟫ = 0`, `h0` asserts that the whole contact value is carried by a vacuum-orthogonal
vector. The conclusion is the shape `LagTwoBound.confines_of_lag_two_ratio` consumes, at `K = Λ ^ 2`;
that consumer requires one `Λ` serving every `β ≥ 0`.

DERIVED: `3` occurs four times, as the aperture argument of each `wilsonCorrAt` — once in `h0`, once
in `h2`, and twice in the conclusion. `0` occurs seven times — the lower bound on `Λ`, the
orthogonality condition in `hpos`, the lower bound of the form in `hpos`, the orthogonality condition
in `hray`, the orthogonality of `x`, and the contact lag index in `h0` and in the conclusion. `2`
occurs six times — the exponent in the Rayleigh bound, the exponent in `h0`, the lag index and the
power of `Tq` in `h2`, and the lag index and the exponent on `Λ` in the conclusion; every one of them
is the second lag or the square that lag forces. -/
theorem lag_two_ratio_of_vacuum_rayleigh {β : ℝ} (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {x : GNS D.toReflForm} (hx : (inner ℝ D.vacGNS x : ℝ) = 0)
    (h0 : MassGap.wilsonCorrAt 3 β 0 = ‖x‖ ^ 2)
    (h2 : MassGap.wilsonCorrAt 3 β 2 = (inner ℝ x ((D.Tq ^ 2) x) : ℝ)) :
    MassGap.wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * MassGap.wilsonCorrAt 3 β 0 := by
  rw [h0, h2]
  exact inner_Tq_two_le_of_rayleigh D hΛ hpos hray hx

#print axioms lag_two_ratio_of_vacuum_rayleigh

/-- `MassGap.SpectralBound.SpectralAt β Λ`, from the same hypotheses as
`lag_two_ratio_of_vacuum_rayleigh`. `SpectralBound.spectralAt_iff` unfolds that proposition to
`0 ≤ Λ ∧ wilsonCorrAt 3 β 2 ≤ Λ ^ 2 * wilsonCorrAt 3 β 0`, whose two halves are `hΛ` and the previous
theorem.

Scope: this is one coupling. `SpectralBound.confines_of_subdominant_bound` consumes
`SpectralBound.LagSpectralBound Λ`, which requires a single `Λ` serving every `β ≥ 0`, together with
a strict comparison `Λ < SpectralBound.lambdaThreshold`. That threshold is the closed form
`(1 - 3 ^ (-1/4)) / (1 + 3 ^ (-1/4))`, whose square is `LagTwoBound.lagTwoThreshold` by
`SpectralBound.lambdaThreshold_sq`; `SpectralBound.lambdaThreshold_lt` and `lambdaThreshold_gt`
bracket it strictly between `0.136469` and `0.13647`, and
`SpectralBound.confines_of_subdominant_le` takes the lower bracket.

DERIVED: `3` occurs twice, as the aperture argument of `wilsonCorrAt` in `h0` and in `h2`. `0`
occurs six times — the lower bound on `Λ`, the orthogonality condition in `hpos`, the lower bound of
the form in `hpos`, the orthogonality condition in `hray`, the orthogonality of `x`, and the contact
lag index in `h0`. `2` occurs four times — the exponent in the Rayleigh bound, the exponent in `h0`,
and the lag index and power of `Tq` in `h2`. -/
theorem spectralAt_of_vacuum_rayleigh {β : ℝ} (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {x : GNS D.toReflForm} (hx : (inner ℝ D.vacGNS x : ℝ) = 0)
    (h0 : MassGap.wilsonCorrAt 3 β 0 = ‖x‖ ^ 2)
    (h2 : MassGap.wilsonCorrAt 3 β 2 = (inner ℝ x ((D.Tq ^ 2) x) : ℝ)) :
    MassGap.SpectralBound.SpectralAt β Λ := by
  rw [MassGap.SpectralBound.spectralAt_iff]
  exact ⟨hΛ, lag_two_ratio_of_vacuum_rayleigh D hΛ hpos hray hx h0 h2⟩

#print axioms spectralAt_of_vacuum_rayleigh

end Transfer

end MassGap.SecondEigenvalue
