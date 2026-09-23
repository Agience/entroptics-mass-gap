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
a STRICT comparison `Λ < SpectralBound.lambdaThreshold`. That threshold is the closed form
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
