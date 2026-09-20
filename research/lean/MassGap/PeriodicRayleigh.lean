import Mathlib
import MassGap.SecondEigenvalue
import MassGap.OSPositivity
import MassGap.HalfLineTransfer

/-!
# MassGap.PeriodicRayleigh — the periodic decay bound without finite dimension, and what finite
dimension was actually holding up

## The question this file answers

`Transfer`'s Parts 5 and 6 live under `[FiniteDimensional ℝ (Transfer.GNS D.toReflForm)]`. That
hypothesis is not one a Mathlib bump would supply. `SliceTrace`'s "Why an iterated integral and not
`LinearMap.trace`" gives the reason: a slab configuration is a point of `SlabIdx τ t → SU N`, a
compact group of POSITIVE DIMENSION for `N ≥ 2`, so the operator acts on `L²` of a continuum. READ
THAT AS PROSE, NOT AS A THEOREM — nothing in this tree formalises the dimension of `SU N` or the
infinite-dimensionality of any GNS space, and no declaration here depends on it. What follows is the
same either way: it says the finite-dimensional route should not be relied on, not that it has been
refuted in Lean.

`SecondEigenvalue.norm_le_of_rayleigh_le` takes a Rayleigh bound on an invariant subspace to an
operator-norm bound on it with one Cauchy–Schwarz and no compactness, completeness, finite dimension,
eigenvalue ordering or spectral theorem. The question is whether that removes the finite-dimension
requirement from `Transfer`'s Part 6. The answer has two halves and they differ.

## THE OBJECT CANNOT BE BUILT THAT WAY; THE BOUND CAN

`Spectral.PeriodicSpectralForm`'s `hrep` field is an EQUALITY —
`ρ d = ∑ k, w k * (lam k ^ d + lam k ^ (n − d))` — over a `Fintype` index. Producing one means
producing an exact finite spectral decomposition of the correlator, which is what
`Transfer.inner_pow_expand` uses the eigenvector basis for. `norm_le_of_rayleigh_le` yields an
INEQUALITY and can yield nothing else, so it does not and cannot supply `hrep`.
`Transfer.periodicSpectralForm_of_transfer` keeps its `[FiniteDimensional]` hypothesis, and this file
does not remove it.

But `periodicSpectralForm_of_transfer`'s only consumer inside `Transfer` is
`periodic_decay_of_transfer`, whose CONCLUSION is an inequality:

    periodicCorr D v per d ≤ 2 * (∑ i, ⟪eᵢ, v⟫²) * r ^ d      (Transfer.lean:761)

and `Transfer.sum_weights` proves `∑ i, ⟪eᵢ, v⟫² = ‖v‖ * ‖v‖` — under `[FiniteDimensional]`, so the
two right-hand sides are the same number only inside the hypothesis set being escaped. What survives
outside it is the SHAPE: the spectral form is an intermediate object whose only trace in the
conclusion is Parseval's `‖v‖²`. `periodic_decay_of_rayleigh` below proves that bound, with
`‖v‖ * ‖v‖` written directly, from a Rayleigh bound on the vacuum complement — no finite dimension,
no eigenbasis, no `hrep`.

THE TWO ARE INCOMPARABLE AS STATEMENTS, and the difference is the one `Transfer`'s own header insists
on. `periodic_decay_of_transfer` holds at EVERY `v` but assumes the bound at every eigenvalue, which
`Transfer.one_le_of_eigenvalues_le` shows forces `r ≥ 1` — so at any `r` worth having its hypothesis
is false. `periodic_decay_of_rayleigh` assumes the bound only on the vacuum complement and in
exchange requires `v` to lie there. That is the connected correlator, vacuum subtracted, which is the
only place a bound below one can live.

The route is not the spectral one shortened. It is Cauchy–Schwarz on the correlator:
`⟪v, Tᵏv⟫ ≤ ‖v‖·‖Tᵏv‖ ≤ Λᵏ‖v‖²`, with the second step
`SecondEigenvalue.Tq_pow_norm_le_of_rayleigh`. The half-period condition `2d ≤ per` enters exactly
where it does in `Spectral.periodic_decay_le` — it is what makes the far term of the periodic shape no
larger than the near one — and here it needs `Λ ≤ 1`, which `Transfer.norm_TqL_le_one` gives for any
transfer operator but which is taken as a hypothesis so the lemma stays about any `Λ`.

## What each `FiniteDimensional` in `Transfer` is FOR, and whether it survives

`FiniteDimensional` occurs in CODE only in `Transfer.lean`, at lines 553 and 631 (two `variable`
blocks) and line 692 (an `omit`); elsewhere in the tree — including below — it appears only in prose.
That is the token, not the property: `CellSpectrum` and `CellCouple` are finite-dimensional by
construction (`Fin N → ℝ`, `Matrix (Fin N) (Fin N) ℝ`) and use `Module.finrank` throughout, and
completeness enters the tree through `CStarAlgebra` in `RefinementLaw`, `Reconstruction`,
`MassFinite` and `GappedTheory`. None of those is on the transfer-operator route and none of them is
what follows.

TEN declarations sit in the two blocks and EIGHT carry the instance. The two that do not are named at
the end of the list, and they are the reason a count read off the block boundaries is wrong.

* `Tq_pow_eigenvectorBasis`, `abs_eigenvalue_le_one`, `eigenvalue_nonneg` — to NAME an eigenvalue and
  an eigenvector at all. `LinearMap.IsSymmetric.eigenvectorBasis` and `.eigenvalues` both carry
  `hn : Module.finrank 𝕜 E = n` at the pin. Not replaceable: the Rayleigh route never names an
  eigenvalue, it names `SecondEigenvalue.lambdaTwo`, a supremum.
* `inner_pow_expand`, `sum_weights` — for the EXACT expansion, through the orthonormal basis's
  `sum_inner_mul_inner`. Not replaceable by an inequality.
* `periodicSpectralForm_of_transfer` — `Idx := Fin m`, `w`, `lam` and `hrep`, all four from the
  eigenbasis. NOT REPLACEABLE, for `hrep`.
* `periodic_decay_of_transfer` — only to reach the above. ITS BOUND IS REACHABLE WITHOUT IT:
  `periodic_decay_of_rayleigh` proves the same inequality with no finite dimension. It is not a drop-in
  replacement — it asks `v` to be vacuum-orthogonal and `Λ ≤ 1`, which the original does not — and
  the comparison is set out above.
* `one_le_of_eigenvalues_le` — it reads the vacuum's own weight out of `inner_pow_expand` and
  `sum_weights`. REPLACEABLE, and more cheaply than the original: `one_le_of_rayleigh_le` below is
  the Rayleigh hypothesis evaluated at `Ω`, where `⟪TΩ, Ω⟫ = ⟪Ω, Ω⟫ = 1` and `‖Ω‖ = 1`.

The two that do NOT carry it, and the reason the count is eight rather than ten:

* `periodicCorr` (line 649) — it rebinds `D` in its own binder list, so the block's instance, whose
  type mentions the block's `D`, is not included. A reader checking this should elaborate
  `@Transfer.TransferData.periodicCorr` and read the binders, not count declarations between the
  block boundaries. That it carries nothing is what lets everything below be stated about the tree's
  own `periodicCorr` rather than a copy of it.
* `periodicCorr_vac` (line 700) — `omit`s it explicitly at line 692.

So the verdict is: finite dimension is needed for the spectral OBJECT and for anything that names an
individual eigenvalue, and is needed for nothing else in Part 6. Both theorems that state a BOUND are
reachable without it.

## What this does NOT do

It produces no `Λ`. `SecondEigenvalue`'s list of six obstructions to B5 stands unchanged; this file
touches only the finite-dimensionality entry of it, which is the one that entry says `§1 removes`.

It also does not make the shift-built transfer operator gapped. `HalfLineTransfer.shiftObs_pow_period`
gives `(shiftObs τ)^n = id` on a lattice periodic in `τ`, and
`HalfLineTransfer.no_rate_of_shift_transfer` turns that into: no `Λ < 1` is available on the vacuum
complement for ANY `TransferData` whose `T` is the lattice shift, on any module. That obstruction is
independent of finite dimension and is untouched here.

## §2, on the two premises of `OSPositivity.wilsonSlabTransfer`

`OSPositivity.wilsonSlabTransfer` already assembles a full `Transfer.TransferData` on the slab algebra
from exactly two premises, with the foundational axioms only. §2 says what each of them is.

`slabShiftContractive_iff_two_step` rewrites the second, `SlabShiftContractive`, into the two-step
correlator inequality `⟨F, T²F⟩ ≤ ⟨F, F⟩` — one application of
`WilsonTransfer.reflForm_shiftObs_symm`. It is worth naming because that is the shape B5 reads:
`SpectralBound.SpectralAt` is `ρ(2) ≤ Λ²ρ(0)`, and contractivity is the same inequality at `Λ = 1`.

`const_of_slabShiftStable` says what the first, `SlabShiftStable`, costs: at `2 ≤ m` it forces every
observable of the slab algebra to be constant, by `HalfLineTransfer.const_of_shift_stable` applied at
`M := localObs`, which is a submodule. So the `TransferData` that premise unlocks is a transfer
operator on constants with `T = id`. The assembly theorem is unaffected; what changes is how the
premise should be read.

Foundational footprint only (`#print axioms` throughout).
Build: `python research/code/lean_build.py build MassGap.PeriodicRayleigh`.
-/

namespace MassGap.PeriodicRayleigh

open MassGap MassGap.Transfer MassGap.SecondEigenvalue

/-! ## §1 The half-line correlator, bounded by a Rayleigh bound

Nothing in this section knows about a lattice. `D` is any `Transfer.TransferData` and the bound is on
the vacuum complement, stated in the `⟪Ω, y⟫ = 0` form every consumer in the tree uses.
-/

section Generic

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **THE HALF-LINE CORRELATOR DECAYS GEOMETRICALLY, FROM A RAYLEIGH BOUND.**
`⟪v, Tᵏ v⟫ ≤ Λᵏ ‖v‖²` on the vacuum complement.

Cauchy–Schwarz on the inner product — `real_inner_le_norm`, which is Mathlib's and holds on any real
inner product space — composed with `SecondEigenvalue.Tq_pow_norm_le_of_rayleigh`. Neither step knows
the dimension of `GNS D.toReflForm`, and neither names an eigenvalue.

This is the exact statement `Transfer.inner_pow_expand` proves as an EQUALITY in finite dimension. The
equality is strictly stronger and is not reachable this way; the inequality is all `periodic_decay_le`
ever uses.

DERIVED: the `2` is the degree of the norm in a Rayleigh quotient; the `0`s are a sign and an
orthogonality. Nothing is a magnitude. -/
theorem inner_pow_le_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    {v : GNS D.toReflForm} (hv : (inner ℝ D.vacGNS v : ℝ) = 0) (k : ℕ) :
    (inner ℝ v ((D.Tq ^ k) v) : ℝ) ≤ Λ ^ k * (‖v‖ * ‖v‖) := by
  have hcs : (inner ℝ v ((D.Tq ^ k) v) : ℝ) ≤ ‖v‖ * ‖(D.Tq ^ k) v‖ := real_inner_le_norm _ _
  have hgeo : ‖(D.Tq ^ k) v‖ ≤ Λ ^ k * ‖v‖ :=
    Tq_pow_norm_le_of_rayleigh D hΛ hpos hray hv k
  have hstep : ‖v‖ * ‖(D.Tq ^ k) v‖ ≤ ‖v‖ * (Λ ^ k * ‖v‖) :=
    mul_le_mul_of_nonneg_left hgeo (norm_nonneg v)
  calc (inner ℝ v ((D.Tq ^ k) v) : ℝ)
      ≤ ‖v‖ * ‖(D.Tq ^ k) v‖ := hcs
    _ ≤ ‖v‖ * (Λ ^ k * ‖v‖) := hstep
    _ = Λ ^ k * (‖v‖ * ‖v‖) := by ring

#print axioms inner_pow_le_of_rayleigh

/-- **THE PERIODIC CORRELATOR, TERM BY TERM.** `Transfer.periodicCorr` is the sum of the two ways
round the circle, so a bound on each is a bound on it.

`periodicCorr` itself carries no `FiniteDimensional` instance — it is `⟪v, T^d v⟫ + ⟪v, T^{per−d} v⟫`
and names no eigenvalue — so this is a statement about the tree's own definition and not about a copy
of it.

DERIVED: the `2` is the Rayleigh quotient's norm degree; the `0`s are a sign and an orthogonality.
The two summands are the two arcs of the circle, which is `periodicCorr`'s own shape. -/
theorem periodicCorr_le_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    (per : ℕ) {v : GNS D.toReflForm} (hv : (inner ℝ D.vacGNS v : ℝ) = 0) (d : Fin per) :
    TransferData.periodicCorr D v per d
      ≤ Λ ^ (d : ℕ) * (‖v‖ * ‖v‖) + Λ ^ (per - (d : ℕ)) * (‖v‖ * ‖v‖) := by
  have hnear := inner_pow_le_of_rayleigh D hΛ hpos hray hv (d : ℕ)
  have hfar := inner_pow_le_of_rayleigh D hΛ hpos hray hv (per - (d : ℕ))
  rw [TransferData.periodicCorr]
  linarith

#print axioms periodicCorr_le_of_rayleigh

/-- **`Transfer.periodic_decay_of_transfer`'S CONCLUSION, WITH NO FINITE DIMENSION.**

    periodicCorr D v per d ≤ 2 * (‖v‖ * ‖v‖) * Λ ^ d      for  2d ≤ per.

Compare `Transfer.periodic_decay_of_transfer`, whose bound is `2 * (∑ i, ⟪eᵢ, v⟫²) * r ^ d` — and
`Transfer.sum_weights` proves that sum IS `‖v‖ * ‖v‖`. So this is the same bound with the eigenbasis
removed from the statement as well as from the proof.

The hypotheses are not the same ones weakened. `periodic_decay_of_transfer` takes GLOBAL positivity
`∀ x : A, 0 ≤ D.form x (D.T x)` and a bound at every eigenvalue, and holds at every `v`; this takes
positivity and the bound on the vacuum complement only, and requires `v` to lie there. Neither
implies the other. What makes this the useful direction is
`Transfer.one_le_of_eigenvalues_le` — equivalently `one_le_of_rayleigh_le` below — which says a
hypothesis read over everything forces the bound to be at least one.

What replaces the spectral decomposition is `inner_pow_le_of_rayleigh` at the two lags, and what
replaces `hgap : ∀ i, eigenvalues i ≤ r` is the Rayleigh bound `hray`. What replaces nothing is the
half-period condition: `2d ≤ per` gives `d ≤ per − d`, and with `Λ ≤ 1` that makes the far arc's
factor no larger than the near arc's. Past half the period the bound is false for the same reason it
is false in `Spectral.periodic_decay_le` — a torus correlator turns back up.

`hΛ1 : Λ ≤ 1` costs nothing that is wanted. `Transfer.Tq_norm_le` gives `‖T y‖ ≤ ‖y‖` for every
`TransferData`, so `Λ = 1` is always a valid Rayleigh bound and a `Λ` above one is slack against the
free one; the hypothesis excludes only bounds already weaker than that. It is carried rather than
derived so the lemma states what its proof uses.

DERIVED: the `2` in `2 * (‖v‖ * ‖v‖)` is the two arcs of the periodic shape, the same `2` as in
`Spectral.periodic_decay_le`; the `2` in `2 * d ≤ per` is the halving of the period; the `2` in
`‖y‖ ^ 2` is the Rayleigh quotient's norm degree; the `1` in `Λ ≤ 1` is the vacuum eigenvalue, which
is the total mass of a probability measure; the `0`s are a sign and an orthogonality. No numeral here
is a threshold and none is chosen. -/
theorem periodic_decay_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hΛ1 : Λ ≤ 1)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2)
    (per : ℕ) {v : GNS D.toReflForm} (hv : (inner ℝ D.vacGNS v : ℝ) = 0)
    (d : Fin per) (hhalf : 2 * (d : ℕ) ≤ per) :
    TransferData.periodicCorr D v per d ≤ 2 * (‖v‖ * ‖v‖) * Λ ^ (d : ℕ) := by
  have hle : (d : ℕ) ≤ per - (d : ℕ) := by omega
  have hfar : Λ ^ (per - (d : ℕ)) ≤ Λ ^ (d : ℕ) := pow_le_pow_of_le_one hΛ hΛ1 hle
  have hnn : (0 : ℝ) ≤ ‖v‖ * ‖v‖ := mul_nonneg (norm_nonneg v) (norm_nonneg v)
  have hsplit := periodicCorr_le_of_rayleigh D hΛ hpos hray per hv d
  nlinarith [hsplit, hfar, hnn]

#print axioms periodic_decay_of_rayleigh

/-- **THE VACUUM OBSTRUCTION, WITH NO FINITE DIMENSION.** A Rayleigh bound `Λ` holding at EVERY
vector — not only on the vacuum complement — forces `1 ≤ Λ`.

`Transfer.one_le_of_eigenvalues_le` is the same statement about the eigenvalue family, and needs the
eigenbasis, `inner_pow_expand` and `sum_weights` to reach it. Read as a Rayleigh bound it is the
hypothesis evaluated at one vector: `T Ω = Ω` (`Transfer.Tq_vacGNS`) and `‖Ω‖ = 1`
(`Transfer.norm_vacGNS`) make `⟪T Ω, Ω⟫ = 1` and `Λ * ‖Ω‖² = Λ`.

What it says is `SecondEigenvalue`'s reason for working on `vacPerp` at all, and `Transfer`'s reason
for saying `hdecay` is false over the full spectrum: a bound below one can only ever be about the
vacuum complement.

DERIVED: the `1`s are the vacuum eigenvalue and the vacuum's norm, both the total mass of a
probability measure; the `2` is the Rayleigh quotient's norm degree. -/
theorem one_le_of_rayleigh_le (D : TransferData A) {Λ : ℝ}
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) : 1 ≤ Λ := by
  have h := hray D.vacGNS
  rw [TransferData.Tq_vacGNS D, real_inner_self_eq_norm_mul_norm,
    TransferData.norm_vacGNS D] at h
  simpa using h

#print axioms one_le_of_rayleigh_le

end Generic

/-! ## §2 The two-step reading of the remaining slab premise

`OSPositivity.wilsonSlabTransfer` builds a full `Transfer.TransferData` on the slab algebra from
`SlabShiftStable` and `SlabShiftContractive`. This section says what the second one is.
-/

section Slab

open MassGap.WilsonHypercubic MassGap.WilsonTransfer MassGap.OSPositivity
open MassGap.LogConvex MassGap.ActionSplit

variable {d n N : ℕ} [NeZero n]

/-- **CONTRACTIVITY IS A TWO-STEP CORRELATOR STATEMENT.** `⟨T F, T F⟩ = ⟨F, T²F⟩` for the Wilson
reflection form.

One application of `WilsonTransfer.reflForm_shiftObs_symm` with `G := shiftObs τ F`, and it holds with
no hypothesis — every real `β`, every reflection constant, every observable, no measurability,
boundedness or positivity.

DERIVED: no numeral. The "two steps" are two applications of one shift, not a chosen lag. -/
theorem reflForm_shiftObs_self (N : ℕ) (τ : Fin d) (c : Fin n) (β : ℝ)
    (F : (Link d n → MassGap.SUN.SU N) → ℝ) :
    MassGap.Transfer.reflForm N τ c β (shiftObs τ F) (shiftObs τ F)
      = MassGap.Transfer.reflForm N τ c β F (shiftObs τ (shiftObs τ F)) :=
  reflForm_shiftObs_symm N τ c β F (shiftObs τ F)

#print axioms reflForm_shiftObs_self

/-- **`OSPositivity.SlabShiftContractive` IS `⟨F, T²F⟩ ≤ ⟨F, F⟩` ON THE SLAB ALGEBRA.**

The premise as written compares the form at the SHIFTED observable with the form at the observable;
this says it is the two-step correlator against the contact value. The shape matters because it is
B5's: `SpectralBound.SpectralAt β Λ` is `ρ(2) ≤ Λ² ρ(0)`
(`SpectralBound.spectralAt_iff`), and contractivity is that inequality at `Λ = 1`. So the premise
`OSPositivity.wilsonSlabTransfer` still carries is the lag-two bound with no gap in it — the weakest
member of the family B5 needs a strict member of.

A SHAPE MATCH IS NOT AN IDENTIFICATION. `SpectralBound`'s `ρ` is `MassGap.wilsonCorrAt`, and that it
equals the transfer two-point function is exactly `SecondEigenvalue.lag_two_ratio_of_vacuum_rayleigh`'s
hypotheses `h0` and `h2`, which are unproved there and unproved here. Nothing below connects the two
sides; it rewrites one of them.

This changes nothing about whether the premise holds. `HalfLineTransfer.no_rate_of_shift_transfer`
says that even granted it, no `Λ < 1` follows for a shift-built `T` on a lattice periodic in `τ`.

DERIVED: no numeral of its own. -/
theorem slabShiftContractive_iff_two_step (N : ℕ) (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ) :
    SlabShiftContractive N τ a m β ↔
      ∀ F ∈ localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m),
        MassGap.Transfer.reflForm N τ (a + a) β F (shiftObs τ (shiftObs τ F))
          ≤ MassGap.Transfer.reflForm N τ (a + a) β F F := by
  constructor
  · intro h F hF
    have hs := h F hF
    rwa [reflForm_shiftObs_self N τ (a + a) β F] at hs
  · intro h F hF
    have hs := h F hF
    rwa [← reflForm_shiftObs_self N τ (a + a) β F] at hs

#print axioms slabShiftContractive_iff_two_step

/-- **AND THE FIRST PREMISE COLLAPSES THE OBJECT IT IS FOR.** At `n = 2m` with `2 ≤ m`,
`OSPositivity.SlabShiftStable` implies every observable of the slab algebra is CONSTANT.

`HalfLineTransfer.const_of_shift_stable` says this for every submodule `M` of the slab algebra that
the shift preserves. `LogConvex.localObs` IS such a submodule, and `SlabShiftStable` is exactly that
preservation hypothesis at `M := localObs`, so the theorem applies to the whole algebra with
`hMsub := id`. `HalfLineTransfer.shiftObs_eq_self_of_shift_stable` then makes `T` the identity there.

WHAT THIS DOES TO `OSPositivity.wilsonSlabTransfer`. It still builds a complete
`Transfer.TransferData` from two premises and no other unproved input — that is unchanged and it is
a theorem. What it says is that reading the first premise as merely open understates it: granted, the
`TransferData` it produces is a transfer operator on constants, with `T = id`, every eigenvalue one
and no vacuum complement. `OSPositivity`'s own header says the premise is named rather than offered;
this is the same point as a consequence rather than as a remark.

DERIVED: `2` in `n = 2 * m` is the two mirror planes of an even extent and `2 ≤ m` is
`HalfLineTransfer.blkR_shift_stable_of_extent_two`'s sharp boundary, not a choice. -/
theorem const_of_slabShiftStable (N : ℕ) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm2 : 2 ≤ m) (h : SlabShiftStable N τ a m)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF : F ∈ localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))
    (U V : Link d n → MassGap.SUN.SU N) : F U = F V :=
  MassGap.HalfLineTransfer.const_of_shift_stable τ a m hm hm2 (fun _ hG => hG) h hF U V

#print axioms const_of_slabShiftStable

end Slab

end MassGap.PeriodicRayleigh
