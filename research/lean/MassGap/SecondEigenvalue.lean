import Mathlib
import MassGap.VolumeRate
import MassGap.SpectralBound

/-!
# MassGap.SecondEigenvalue — an upper bound on the subdominant eigenvalue, with no spectral theorem

## What this file is for

`VolumeRate.rp_sub_geometric`, `VolumeRate.rp_gap_of_one_cut` and `HalfLineTransfer` all take one
input and none of them produces it:

    hρ :  ∀ y ⊥ Ω,  ‖T y‖ ≤ Λ ‖y‖.

`SpectralBound.confines_of_subdominant_bound` closes Clay row B5 from an input written in the same
letter — `Λ` below `lambdaThreshold` at every nonnegative coupling — but IT IS NOT THE SAME INPUT.
`SpectralBound.LagSpectralBound` unfolds through `SpectralAt` (`SpectralBound.lean:288`) into a
statement about `wilsonCorrAt 3 β 0` and `wilsonCorrAt 3 β 2` and nothing else; `SpectralBound`'s own
docstring says so — "no operator, no completeness, no identification of `Z` with a trace". Equating
the two IS the unproved step, and it appears below as the named hypotheses `h0` and `h2`, never as
prose.

The obstruction to producing `hρ` was believed to be that Mathlib v4.31.0 has no
apparatus for a second eigenvalue. THAT READING IS WRONG IN BOTH DIRECTIONS, and both halves were
checked by grep against the pinned checkout on the build host (rev
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, "chore: bump toolchain to v4.31.0", 2026-06-15), not
recalled:

* **Eigenvalue ordering EXISTS.** `LinearMap.IsSymmetric.eigenvalues`
  (`Mathlib/Analysis/InnerProductSpace/Spectrum.lean:279`) is DEFINED sorted in decreasing order —
  `unsortedEigenvalues ∘ Tuple.sort ∘ Fin.revPerm` — and `eigenvalues_antitone` (same file, line 312)
  proves it. `Matrix.IsHermitian.eigenvalues₀_antitone` (`Mathlib/Analysis/Matrix/Spectrum.lean:61`)
  is the matrix corollary, and that file contains no TODO at all. So `λ₂` is nameable as
  `hT.eigenvalues hn 1` — BUT ONLY IN FINITE DIMENSION: every one of those declarations carries
  `hn : Module.finrank 𝕜 E = n`. `Transfer`'s spectral section already uses them, behind
  `[FiniteDimensional ℝ (GNS ...)]`, and `SliceTrace` records why that hypothesis is not available
  for Yang–Mills: a slab configuration is a point of a compact group of positive dimension, so the
  operator acts on `L²` of a continuum.
* **The compact self-adjoint spectral theorem EXISTS too**, in eigenspace-completeness form:
  `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` (Spectrum.lean:443) and
  `finite_dimensional_eigenspace` (Spectrum.lean:463), both under `IsCompactOperator`. The file's
  TODO (line 59) is "Spectral theory for bounded self-adjoint operators" — the NON-compact case.
  `Rayleigh.lean`'s TODO (line 31) is a different one again: an eigenvector AT the `iSup` for a
  compact operator on a complete space.

So the long route to `λ₂` is available in finite dimension and unavailable here, for a reason that
bumping Mathlib would not change. This file takes the short route instead.

## The finding, stated loudly: NONE OF THAT APPARATUS IS NEEDED

An UPPER bound on the subdominant eigenvalue is a bound on the Rayleigh quotient over the orthogonal
complement of the top eigenvector, and that is a definition rather than a theorem. What has to be
proved is only the step from the quotient to the operator norm, and for a SELF-ADJOINT map that step
is one application of Cauchy–Schwarz to the semidefinite form `B(u,v) = ⟪T u, v⟫`, followed by the
Rayleigh hypothesis at TWO vectors — at `y`, and at `T y`, which is where invariance earns its place:

    ‖T y‖⁴ = B(y, T y)² ≤ B(y, y) · B(T y, T y) ≤ (Λ‖y‖²)(Λ‖T y‖²).

`norm_le_of_rayleigh_le` is that argument. It needs no compactness, no completeness, no finite
dimension, no eigenvalue ordering, no min-max principle, no Hilbert–Schmidt or trace class, no
Perron–Frobenius and no spectral theorem. Three of its four hypotheses are statements about the
subspace `V` alone — `V` is `T`-invariant, the form is nonnegative on `V`, the form is bounded by `Λ`
on `V`. The fourth, `T.IsSymmetric`, is Mathlib's and is GLOBAL: `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫` over all
of `E`. The proof invokes it only at pairs drawn from `V`, so the hypothesis is stronger than the
proof needs; it is taken in Mathlib's form because that is the form every caller already has
(`Transfer.TransferData.Tq_isSymmetric`).

WHAT IS GENUINELY ABSENT FROM MATHLIB AT THE PIN, also by grep over the whole checkout, is the rest
of the list — and none of it turns out to be needed. Zero mathematical hits for Cheeger or
conductance; for Hilbert–Schmidt, Schatten or trace class (the only hits are Lean's own
`registerTraceClass` in tactic files); for Perron–Frobenius; for a spectral gap of any kind; for
Doeblin; and for a Poincaré or log-Sobolev inequality (the `Poincare` files are the conjecture and a
curve integral). There is no Birkhoff CONTRACTION and no Hilbert projective metric: the three
`Birkhoff` locations are `Dynamics/BirkhoffSum` (ergodic sums), `Analysis/Convex/Birkhoff.lean`
(Birkhoff–von Neumann) and `Order/Birkhoff.lean` (lattice representation). There is no
Courant–Fischer: the four `MinMax` files are lattice `min`/`max`, and `Mathlib/Topology/Sion.lean` is
Sion's minimax for a quasiconvex–quasiconcave function, which says nothing about eigenvalues. The one
near-miss is `ProbabilityTheory.Kernel.IsReversible`
(`Mathlib/Probability/Kernel/Invariance.lean:60`) with `IsReversible.invariant` — reversibility of a
Markov kernel is defined, and nothing spectral is attached to it.

WHAT THIS DOES AND DOES NOT CHANGE. It removes the Mathlib obstruction from the OPERATOR route —
`VolumeRate` and `HalfLineTransfer`'s `hρ` is now derivable from a Rayleigh bound. It changes nothing
about the path from `SpectralAt` to `ConfinesAtAnAperture`, which never had one:
`SpectralBound.spectralAt_iff` already proves, unconditionally and with no operator anywhere, that at
extent four the subdominant-eigenvalue statement and the lag-two ratio statement are the SAME
statement. What is still missing is the bridge between the two routes, and it is not a Mathlib
absence — see the last section.

## What is proved

**§1, generic.** For `T : E →ₗ[ℝ] E` symmetric on a real inner product space and `V : Submodule ℝ E`:

* `inner_map_quad` — the quadratic expansion `⟪T(t•u+v), t•u+v⟫ = ⟪Tu,u⟫t² + 2⟪Tu,v⟫t + ⟪Tv,v⟫`.
  Symmetry enters exactly once, to merge the two cross terms.
* `inner_map_cauchy_schwarz` — `⟪Tu,v⟫² ≤ ⟪Tu,u⟫⟪Tv,v⟫` for `u, v ∈ V`, from the discriminant.
* `norm_le_of_rayleigh_le` — **the lemma.** The Rayleigh bound on `V` gives the operator bound on `V`.
* `rayleighSet`, `lambdaTwo` — the variational characterisation as a DEFINITION: `lambdaTwo T V` is
  the supremum of `⟪Ty,y⟫/‖y‖²` over nonzero `y ∈ V`. With `V = Ωᗮ` this is `λ₂`, named without any
  enumeration or ordering of a spectrum, and without `T` being compact or even bounded.
* `lambdaTwo_nonneg`, `rayleigh_le_of_lambdaTwo_le`, `lambdaTwo_le_of_rayleigh_le`,
  `norm_le_lambdaTwo_mul` — the two directions of the characterisation, and the operator bound at the
  supremum itself. THESE THREE ARE WHERE THE SUPREMUM HAS TO BE REAL: each carries
  `BddAbove (rayleighSet T V)`, and `lambdaTwo_le_of_rayleigh_le` carries `Nonempty` instead. So the
  definition is free of boundedness and every USE of it is not.

The discriminant step reproves what `Reconstruction.gns_cauchy_schwarz` and
`Transfer.ReflForm.cauchy_schwarz` already do, twice over, with the same `discrim_le_zero` + `nlinarith`
proof. It is separate here for one reason: both of those need the form nonnegative on the WHOLE
module, and the form `B(u,v) = ⟪T u, v⟫` is nonnegative only on the vacuum complement — positivity in
the vacuum direction is a different statement. Reusing `gns_cauchy_schwarz` would mean carrying `↥V`
as the module and building `B : ↥V →ₗ[ℝ] ↥V →ₗ[ℝ] ℝ`; that is a real alternative and it is not taken
here.

**§2, the transfer operator.** `vacPerp` is the vacuum complement as a submodule — it IS Mathlib's
`(Submodule.span ℝ {Ω})ᗮ` (`vacPerp_eq_orthogonal`), constructed rather than abbreviated only so that
membership is the equation `⟪Ω, y⟫ = 0` by `Iff.rfl`, which is the form every consumer in the tree
states it in. `vacPerp_invariant` is `VolumeRate.inner_vac_Tq` in submodule form;
`norm_Tq_le_of_rayleigh` produces the hypothesis `hρ` that `VolumeRate.rp_sub_geometric`,
`VolumeRate.rp_gap_of_one_cut` and `HalfLineTransfer` consume. `Tq_pow_norm_le_of_rayleigh` and
`tendsto_zero_of_rayleigh` are those consumers with `hρ` discharged.

**§3, to B5.** `inner_Tq_two_le_of_rayleigh` is the lag-two two-point bound `⟪x, T²x⟫ ≤ Λ²‖x‖²`. It
still runs through §1's Cauchy–Schwarz, via `norm_Tq_le_of_rayleigh`; what lag two avoids is a SECOND
Cauchy–Schwarz on the correlator, because self-adjointness turns `⟪x, T²x⟫` into `‖Tx‖²` exactly.
`lag_two_ratio_of_vacuum_rayleigh` and `spectralAt_of_vacuum_rayleigh` carry it into
`SpectralBound.SpectralAt`, hence into `SpectralBound.confines_of_subdominant_bound`.

## What is ASSUMED, and it is not one thing

* **`0 ≤ ⟪T y, y⟫` on the complement.** `Transfer`'s header says why this is a second application of
  reflection positivity — about a half-integer time plane — and not a consequence of contractivity: a
  negative transfer eigenvalue is what an oscillating correlator looks like, and `T_contract` bounds
  `|λ|`, not `λ`. It is a named hypothesis of every theorem here that uses it, never a field.
* **The Rayleigh bound itself.** This file converts it; it does not prove it. Producing `Λ` is the
  open work.
* **That the contact value lies entirely in the vacuum complement.** §3 pairs `hx : ⟪Ω, x⟫ = 0` with
  `h0 : ρ(0) = ‖x‖²`, and together those say the whole of `ρ(0)` is carried by a vacuum-orthogonal
  vector — i.e. that `wilsonCorrAt` is already vacuum-subtracted. That is a physical claim about the
  correlator, it is not proved anywhere in the tree, and it is separate from the Rayleigh bound.

## What stands between this and B5, named exactly

1. **There is no `TransferData` over the Wilson measure, and the reason is NOT reflection
   positivity.** `Complete.wilson_reflection_positive_at` is an axiom, but
   `Complete.wilson_reflection_positive_at_even` PROVES its body at even extent `N + 1 = 2m`,
   `2 ≤ m`, `0 ≤ β` — and §3 lives at `N = 3`, so `N + 1 = 4 = 2·2`, exactly that domain.
   `ConfinesZero` already calls it there. The blocker is the one `Spectral2` names:
   `Transfer.TransferData` needs a time-translation ENDOMORPHISM of the observable module, and
   `Transfer`'s spectral section needs a finite-dimensional GNS space, and neither exists in the
   tree. §1 removes the finite-dimensionality requirement; the endomorphism it does not.
2. **`SliceTrace`'s `K_t` is not `SliceTransfer.transferKernel`.** `SliceTrace.partition_eq_cycleIntegral`
   gives `Z` as a cyclic integral of `K_t`, but `K_t` reads the axis links of its own slab (removing
   them is a change of variables in temporal gauge, a hypothesis in `SliceTransfer` and discharged
   nowhere), carries the whole intra-slice weight rather than the symmetric `e^{−s/2}` split, and
   carries a constant plus an ordered-`Plaq` sum that counts each plane twice
   (`PlaqCount.boltz_eq_std`). So `transferKernel_symm` and `transferKernel_psd` are NOT transported
   to `K_t`; only `slabKernel_pos` is. Symmetry is what `LinearMap.IsSymmetric` needs, so §1 does not
   apply to `K_t` as it stands.
3. **Nothing proves `K_t` couples its two arguments.** Strict positivity and the regrouping bijection
   do not rule out a kernel constant in its second argument, and a kernel constant in its second
   argument has `Λ = 0` for a trivial and useless reason. `SliceTransfer.exists_nondeg_interPlaq` is
   where a non-degeneracy control would start; there is none.
4. **The arcs are not composed.** `SliceTrace.cycle_kernel_prod_split` exhibits the cut and no more;
   turning an arc into an operator power needs one Fubini per intermediate variable.
5. **`h0` and `h2` are satisfiable by objects with no relation to Yang–Mills, so they carry no
   physics on their own.** They assert that two REAL NUMBERS agree; nothing in them ties `D` to the
   Wilson measure. `Spectral2` makes the same observation about `WilsonSpectral` and calls it the
   free point. What stops `spectralAt_of_vacuum_rayleigh` being useless is not the hypotheses' shape
   but the quantifier a caller must eventually meet: `LagSpectralBound` needs ONE `Λ` below
   `lambdaThreshold` at EVERY `β ≥ 0`, and the smallest `Λ` any construction can report is
   `√(ρ(2)/ρ(0))` itself.
6. **`Λ` is still not produced.** `SpectralBound.expansion_domain_bounded` proves the cluster
   expansion's own rate exceeds one past a cut, and `SpectralBound.doeblin_exceeds_lambdaThreshold`
   puts the Doeblin floor above `lambdaThreshold` at every coupling. This file supplies the
   conversion from a Rayleigh bound; it does not produce one.

Foundational footprint only (`#print axioms` throughout).
Build: `python code/lean_build.py build MassGap.SecondEigenvalue`.
-/

namespace MassGap.SecondEigenvalue

open MassGap MassGap.Transfer

/-! ## §1 The variational route, on any real inner product space

Nothing in this section knows about a lattice, a measure, or a gauge group. `T` is any symmetric
linear map and `V` is any submodule it preserves. -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The quadratic expansion.** `⟪T(t•u+v), t•u+v⟫ = ⟪Tu,u⟫·t² + 2⟪Tu,v⟫·t + ⟪Tv,v⟫`.

Symmetry of `T` is used exactly once, to identify the two cross terms `⟪Tu,v⟫` and `⟪Tv,u⟫`. Without
it the middle coefficient is `⟪Tu,v⟫ + ⟪Tv,u⟫` and the discriminant argument below reads a different
number.

DERIVED: the `2` is the number of cross terms a symmetric form produces. Nothing is chosen. -/
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

/-- **Cauchy–Schwarz for the form `B(u,v) = ⟪T u, v⟫`, on a subspace where it is nonnegative.**

The hypothesis is nonnegativity on `V` only, so `T` may be indefinite off `V` — which is the point:
the vacuum direction is where the transfer operator's positivity is a different statement.

Proved the elementary way, as `Transfer.ReflForm.cauchy_schwarz` and `Reconstruction.gns_cauchy_schwarz`
both are: the quadratic `t ↦ B(t•u+v, t•u+v)` is nonnegative because `t•u+v` lies in `V`, so its
discriminant is not positive. Neither of those two is reused here because both require the form
nonnegative on the whole module; see the module docstring for what reuse would cost.

DERIVED: the exponent `2` is the degree of that quadratic and the `4` inside `discrim` is the `4` of
`b² − 4ac`. Neither is chosen. -/
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

/-- **THE LEMMA: A RAYLEIGH BOUND ON AN INVARIANT SUBSPACE IS AN OPERATOR BOUND ON IT.**

If `V` is `T`-invariant and `0 ≤ ⟪T y, y⟫ ≤ Λ‖y‖²` for every `y ∈ V`, then `‖T y‖ ≤ Λ‖y‖` on `V`.

This is the whole of the spectral apparatus B5 needs, and it is ONE Cauchy–Schwarz with the Rayleigh
hypothesis read at two vectors:

    ‖T y‖⁴ = ⟪T y, T y⟫² = B(y, T y)² ≤ B(y,y)·B(T y, T y) ≤ (Λ‖y‖²)(Λ‖T y‖²).

Invariance is what puts `T y` back in `V`, which is what licenses the second factor's bound; without
it the argument does not start. Nonnegativity is what makes `B` a semidefinite form, which is what
licenses Cauchy–Schwarz at all.

NO COMPACTNESS, NO COMPLETENESS, NO SPECTRAL THEOREM, NO EIGENVALUE ORDERING. `E` is any real inner
product space and `T` any symmetric linear map on it. In particular the conclusion holds where
`Analysis/InnerProductSpace/Spectrum.lean`'s compact spectral theorem — a TODO at the pin — would not
even apply.

`hΛ : 0 ≤ Λ` is convenience rather than content: at any nonzero `y ∈ V` it already follows from
`hpos` and `hle`. It is taken as a hypothesis so the `y = 0` case needs no separate argument.

DERIVED: the exponent `2` in `‖y‖^2` is the degree of a quadratic form; `0` is a sign. Nothing here
is a magnitude and nothing is chosen. -/
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

/-- The Rayleigh quotients of `T` at the nonzero vectors of `V`, as a set of reals.

DERIVED: the `2` is the degree of the norm in a Rayleigh quotient; `0` is the excluded vector, at
which the quotient is not defined. Neither is a magnitude. -/
def rayleighSet (T : E →ₗ[ℝ] E) (V : Submodule ℝ E) : Set ℝ :=
  {r | ∃ y ∈ V, y ≠ 0 ∧ r = (inner ℝ (T y) y : ℝ) / ‖y‖ ^ 2}

#print axioms rayleighSet

/-- **`λ₂`, NAMED.** The supremum of the Rayleigh quotient over the nonzero vectors of `V`. With
`V = Ωᗮ` and `T` the transfer operator this IS the subdominant eigenvalue, and it is written down
here as a DEFINITION — no enumeration of a spectrum, no ordering of eigenvalues, no compactness, no
`Matrix.IsHermitian.eigenvalues` and so no dependence on the ordering TODOs at the pin.

What the definition does not do is assert that the supremum is ATTAINED, which is what would need a
spectral theorem. Every theorem below uses it only as an upper bound, where attainment is irrelevant.

DERIVED: nothing numeric. -/
noncomputable def lambdaTwo (T : E →ₗ[ℝ] E) (V : Submodule ℝ E) : ℝ := sSup (rayleighSet T V)

#print axioms lambdaTwo

/-- **The variational characterisation, upward.** A Rayleigh bound on `V` bounds the supremum. The
nonemptiness hypothesis is not cosmetic: `sSup ∅ = 0` in `ℝ` by convention, so without it the
statement would be about a junk value rather than about `T`.

DERIVED: the `2` is the degree of the norm in the quotient; `0` is the excluded vector. -/
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

/-- **The variational characterisation, downward.** The supremum bounds the Rayleigh quotient, hence
the form. `BddAbove` is what makes `sSup` an upper bound rather than a junk value.

The zero vector is handled separately and trivially: both sides are `0` there.

DERIVED: the `2` is the degree of the norm in the quotient; `0` is the vector split off. -/
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

/-- **`λ₂ ≥ 0` when the form is nonnegative on `V`.** The sign, not a magnitude — it is what lets
`norm_le_lambdaTwo_mul` apply `norm_le_of_rayleigh_le`.

DERIVED: `0` is that sign; the `2` is the degree of the norm in the quotient. -/
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

/-- **THE OPERATOR BOUND AT THE SUPREMUM ITSELF.** `‖T y‖ ≤ λ₂ ‖y‖` on `V`.

This is the statement the spectral theorem is usually invoked for, and it is here without one: the
two directions of the variational characterisation compose with `norm_le_of_rayleigh_le`, and no step
needs the supremum to be attained.

DERIVED: nothing numeric beyond the `0` sign carried by `lambdaTwo_nonneg`. -/
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

/-! ## §2 The transfer operator on the vacuum complement

`Transfer.TransferData` carries the Osterwalder–Seiler data. `Tq` is self-adjoint
(`Transfer.TransferData.Tq_isSymmetric`, which is reflection positivity's payload) and fixes the
vacuum (`Tq_vacGNS`), and those two facts alone make the vacuum complement invariant. -/

section Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The vacuum complement `Ωᗮ`, as a submodule.** Membership is the equation
`⟪Ω, y⟫ = 0` definitionally, which is the form every consumer in the tree states it in
(`VolumeRate.rp_sub_geometric`, `HalfLineTransfer`).

DERIVED: the `0` is orthogonality. -/
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

/-- Membership in `vacPerp` is orthogonality to the vacuum, definitionally.

DERIVED: the `0` is orthogonality, the same `0` as in `vacPerp`'s carrier. -/
@[simp] theorem mem_vacPerp (D : TransferData A) {y : GNS D.toReflForm} :
    y ∈ vacPerp D ↔ (inner ℝ D.vacGNS y : ℝ) = 0 := Iff.rfl

#print axioms mem_vacPerp

/-- **`vacPerp` IS Mathlib's orthogonal complement of the vacuum line**, so the construction above is
a spelling and not a second definition. It is spelled out rather than abbreviated because
`mem_vacPerp` is then `Iff.rfl`, and `⟪Ω, y⟫ = 0` is the form `VolumeRate.rp_sub_geometric` and
`HalfLineTransfer` state their hypotheses in; `Submodule.mem_orthogonal_singleton_iff_inner_right`
is a lemma rather than a definitional unfolding.

DERIVED: nothing numeric. -/
theorem vacPerp_eq_orthogonal (D : TransferData A) :
    vacPerp D = (Submodule.span ℝ {D.vacGNS})ᗮ :=
  Submodule.ext fun _ =>
    (mem_vacPerp D).trans Submodule.mem_orthogonal_singleton_iff_inner_right.symm

#print axioms vacPerp_eq_orthogonal

/-- **The vacuum complement is transfer-invariant**, in submodule form. This is
`VolumeRate.inner_vac_Tq`, which is `⟨Ω, Tx⟩ = ⟨TΩ, x⟩ = ⟨Ω, x⟩ = 0` — self-adjointness and the
vacuum eigenvector, so the step is reflection positivity's. -/
theorem vacPerp_invariant (D : TransferData A) :
    ∀ y ∈ vacPerp D, D.Tq y ∈ vacPerp D :=
  fun _ hy => MassGap.VolumeRate.inner_vac_Tq D hy

#print axioms vacPerp_invariant

/-- **THE HYPOTHESIS `hρ`, DISCHARGED FROM A RAYLEIGH BOUND.**

`VolumeRate.rp_sub_geometric`, `VolumeRate.rp_gap_of_one_cut` and `HalfLineTransfer` all take
`‖T y‖ ≤ Λ‖y‖` on the vacuum complement as an assumption. This produces it from a bound on the
Rayleigh quotient there, via `norm_le_of_rayleigh_le`.

`hpos` IS A SEPARATE ASSUMPTION AND NOT A CONSEQUENCE OF CONTRACTIVITY. `TransferData.T_contract`
bounds `|λ|`; it says nothing about the sign of `λ`, and a negative transfer eigenvalue is what an
oscillating correlator looks like. `Transfer`'s header records this: positivity of the transfer
operator is reflection positivity about a HALF-INTEGER time plane, a second application of the
physics. It appears here as a hypothesis and nowhere as a field.

DERIVED: the `2` is the degree of the norm in a Rayleigh quotient; the `0`s are a sign and an
orthogonality. -/
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

/-- **The geometric law, with its hypothesis gone.** `‖Tⁿx‖ ≤ Λⁿ‖x‖` on the vacuum complement,
from a Rayleigh bound alone. This is `VolumeRate.norm_Tq_pow_le` — equivalently
`VolumeRate.rp_sub_geometric` — with `hρ` supplied by `norm_Tq_le_of_rayleigh`.

DERIVED: the `2` is the Rayleigh quotient's norm degree; the `0`s are a sign and an orthogonality. -/
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

/-- **One cut controls every separation, from a Rayleigh bound.** A Rayleigh bound strictly below one
on the vacuum complement sends `‖Tⁿx‖ → 0`. `VolumeRate.rp_gap_of_one_cut` with its hypothesis
discharged.

DERIVED: the `1` is the vacuum eigenvalue, which is what a subdominant bound must sit below; the `2`
is the Rayleigh quotient's norm degree; the `0`s are a sign and an orthogonality. -/
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

/-! ## §3 The lag-two two-point function, and B5

At lag two the argument is shorter than at a general lag, and it is worth saying why: self-adjointness
turns `⟪x, T²x⟫` into `‖Tx‖²` exactly, so the bound is the operator bound squared and no
Cauchy–Schwarz on the correlator is needed. -/

/-- **`⟪x, T²x⟫ = ‖Tx‖²`.** Self-adjointness, with nothing else in it. Stated separately because it
is the step that makes lag two cheaper than an odd lag.

DERIVED: the `2` is the lag index, and it is the same `2` as the square. -/
theorem inner_Tq_two_eq (D : TransferData A) (x : GNS D.toReflForm) :
    (inner ℝ x ((D.Tq ^ 2) x) : ℝ) = ‖D.Tq x‖ * ‖D.Tq x‖ := by
  have h2 : (D.Tq ^ 2) x = D.Tq (D.Tq x) := by
    rw [pow_two]
    rfl
  rw [h2, real_inner_comm, TransferData.Tq_isSymmetric D (D.Tq x) x,
    real_inner_self_eq_norm_mul_norm]

#print axioms inner_Tq_two_eq

/-- **THE LAG-TWO BOUND: `⟪x, T²x⟫ ≤ Λ²‖x‖²` on the vacuum complement.**

`inner_Tq_two_eq` makes it `‖Tx‖²`, and `norm_Tq_le_of_rayleigh` bounds `‖Tx‖` by `Λ‖x‖`.

DERIVED: the `2`s are the lag index and the square it forces; the `0`s are a sign and an
orthogonality. Nothing is a magnitude. -/
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

/-- **THE B5 RATIO, FROM A RAYLEIGH BOUND.** `ρ(2) ≤ Λ²·ρ(0)` at extent four, given two numeric
identifications:

* `h0 : ρ(0) = ‖x‖²` — the contact value is the trial vector's squared norm;
* `h2 : ρ(2) = ⟪x, T²x⟫` — the lag-two value is its two-step two-point function.

BOTH ARE HYPOTHESES AND NEITHER IS PROVED ANYWHERE IN THIS TREE. They are what `Z = Tr(Tⁿ)` would
supply, and `SliceTrace` records exactly why it does not yet: its `K_t` is not
`SliceTransfer.transferKernel`, it is not known to be symmetric, and it is not known to couple its two
arguments. Carrying them as named hypotheses is the point — it puts the missing step in the
statement rather than in the prose.

AND THEY ASSERT LESS THAN THEY LOOK LIKE. Each says two REAL NUMBERS agree; nothing in either ties
`D` to the Wilson measure, so a `D` built to hit the numbers satisfies them while carrying no physics
— `Spectral2` calls the same phenomenon the free point. What keeps the chain from being empty is the
quantifier downstream: `SpectralBound.LagSpectralBound` needs a SINGLE `Λ` below `lambdaThreshold` at
EVERY `β ≥ 0`, and the smallest `Λ` any such construction can report is `√(ρ(2)/ρ(0))` itself. Note
also that `hx` and `h0` together assert the whole contact value is vacuum-orthogonal.

This is the exact shape `LagTwoBound.confines_of_lag_two_ratio` consumes, at `K = Λ²`.

DERIVED: `0` and `2` are the two lag indices `ConfinesZero.confines_extent_four_of_lag_two_small`
reads; the `2` in `Λ²` is that same lag; `3` is the extent-four index `N + 1 = 4`, the smallest even
extent `EvenAp` admits. -/
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

/-- **THE SAME, IN `SpectralBound`'s VARIABLE.** `SpectralAt β Λ` is by `SpectralBound.spectralAt_iff`
exactly `0 ≤ Λ ∧ ρ(2) ≤ Λ²ρ(0)`, so the Rayleigh bound lands directly in the `Prop` that
`SpectralBound.confines_of_subdominant_bound` consumes.

To reach `ApertureRoute.ConfinesAtAnAperture` a caller supplies this at every `β ≥ 0` — that is
`SpectralBound.LagSpectralBound Λ` — together with `Λ < SpectralBound.lambdaThreshold`. The
comparison there is STRICT and the threshold is the closed form
`(1 − 3^{−1/4})/(1 + 3^{−1/4})`, whose square is `LagTwoBound.lagTwoThreshold` definitionally
(`SpectralBound.lambdaThreshold_sq`); `SpectralBound.lambdaThreshold_lt` puts it strictly below
`0.13647`, so `0.13647` is NOT an admissible value of `Λ`, while `0.136469` is
(`SpectralBound.lambdaThreshold_gt`) and is what `SpectralBound.confines_of_subdominant_le` takes.
Rounding `0.1364697…` up to `0.13647` and comparing non-strictly is the unsafe direction, and it is
wrong. No numeral is introduced here.

DERIVED: `0` and `2` are the two lag indices; the `2` in `Λ²` is that lag; `3` is the extent-four
index `N + 1 = 4`. -/
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
