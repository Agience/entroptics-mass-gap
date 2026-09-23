import Mathlib
import MassGap.SecondEigenvalue
import MassGap.OSPositivity
import MassGap.HalfLineTransfer

/-!
# MassGap.PeriodicRayleigh — periodic decay from a Rayleigh bound, and two readings of the slab
premises

## §1 — the periodic correlator bounded from a Rayleigh estimate

Four statements about an arbitrary `Transfer.TransferData D` over a real inner product space, with no
finite-dimensionality instance and no eigenvalue named anywhere.

* `inner_pow_le_of_rayleigh` — `⟪v, Tᵏ v⟫ ≤ Λᵏ (‖v‖ * ‖v‖)` for `v` orthogonal to the vacuum class.
  Cauchy–Schwarz (`real_inner_le_norm`) composed with
  `SecondEigenvalue.Tq_pow_norm_le_of_rayleigh`.
* `periodicCorr_le_of_rayleigh` — the same bound applied to each of the two arcs that
  `Transfer.periodicCorr` sums.
* `periodic_decay_of_rayleigh` — `periodicCorr D v per d ≤ 2 * (‖v‖ * ‖v‖) * Λ ^ d`, for
  `2 * d ≤ per` and `Λ ≤ 1`.
* `one_le_of_rayleigh_le` — a Rayleigh bound `Λ` holding at every vector, rather than only on the
  vacuum complement, forces `1 ≤ Λ`. The vacuum class is the witness: `Transfer.Tq_vacGNS` and
  `Transfer.norm_vacGNS` give `⟪T Ω, Ω⟫ = 1` and `‖Ω‖ = 1`.

Relation to `Transfer`'s Part 6. `Transfer.periodic_decay_of_transfer` concludes
`periodicCorr D v per d ≤ 2 * (∑ i, ⟪eᵢ, v⟫²) * r ^ d` under `[FiniteDimensional]`, and
`Transfer.sum_weights` identifies that sum with `‖v‖ * ‖v‖` under the same instance.
`periodic_decay_of_rayleigh` states the bound with `‖v‖ * ‖v‖` written directly.

The two are not comparable as statements. `periodic_decay_of_transfer` holds at every `v` and assumes
a bound at every eigenvalue; `periodic_decay_of_rayleigh` assumes the bound only on the vacuum
complement and requires `v` to lie there. Neither hypothesis implies the other.
`Transfer.one_le_of_eigenvalues_le`, and `one_le_of_rayleigh_le` here, say what a bound read over
everything costs.

`Spectral.PeriodicSpectralForm`'s `hrep` field is an equality over a `Fintype` index, so nothing in
this file supplies it, and `Transfer.periodicSpectralForm_of_transfer` keeps its
`[FiniteDimensional]` hypothesis.

Scope of §1. `Λ` is a parameter throughout; no declaration here produces a value for it, and the
hypotheses `hpos` and `hray` are inputs. `hΛ1 : Λ ≤ 1` is carried rather than derived, so the
statement names what its proof uses; `Transfer.Tq_norm_le` makes `Λ = 1` always admissible. The
half-period condition `2 * d ≤ per` is what makes the far arc's factor no larger than the near arc's,
as in `Spectral.periodic_decay_le`.

## §2 — two readings of the premises of `OSPositivity.wilsonSlabTransfer`

That theorem builds a `Transfer.TransferData` on the slab algebra from `SlabShiftStable` and
`SlabShiftContractive`.

`reflForm_shiftObs_self` and `slabShiftContractive_iff_two_step` rewrite the second premise as the
two-step correlator inequality `⟨F, T² F⟩ ≤ ⟨F, F⟩` on the slab algebra, by one application of
`WilsonTransfer.reflForm_shiftObs_symm`. That is the shape `SpectralBound.SpectralAt` takes —
`ρ(2) ≤ Λ² ρ(0)` by `SpectralBound.spectralAt_iff` — at `Λ = 1`. The shapes agree; identifying
`SpectralBound`'s `ρ` with the transfer two-point function is
`SecondEigenvalue.lag_two_ratio_of_vacuum_rayleigh`'s hypotheses `h0` and `h2`, which are not
supplied there or here.

`const_of_slabShiftStable` reads the first premise: at `n = 2 * m` with `2 ≤ m`, `SlabShiftStable`
makes every observable of the slab algebra constant, by `HalfLineTransfer.const_of_shift_stable`
applied at the submodule `LogConvex.localObs`. `OSPositivity.wilsonSlabTransfer` is unaffected as a
theorem; the consequence is that the `TransferData` that premise yields has `T = id`, by
`HalfLineTransfer.shiftObs_eq_self_of_shift_stable`.

Foundational footprint only (`#print axioms` throughout).
Build: `python research/code/lean_build.py build MassGap.PeriodicRayleigh`.
-/

namespace MassGap.PeriodicRayleigh

open MassGap MassGap.Transfer MassGap.SecondEigenvalue

/-! ## §1 The half-line correlator, bounded by a Rayleigh estimate

Nothing in this section mentions a lattice. `D` is any `Transfer.TransferData` over a real module,
and the Rayleigh bound is stated on the vacuum complement in the `⟪Ω, y⟫ = 0` form the rest of the
tree uses.
-/

section Generic

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- `⟪v, (D.Tq ^ k) v⟫ ≤ Λ ^ k * (‖v‖ * ‖v‖)` at every `k : ℕ`, for `v` orthogonal to the vacuum
class, given `0 ≤ Λ` and the positivity and Rayleigh hypotheses on the vacuum complement.

Cauchy–Schwarz (`real_inner_le_norm`, which holds on any real inner product space) composed with
`SecondEigenvalue.Tq_pow_norm_le_of_rayleigh`.

Scope: an inequality. `Transfer.inner_pow_expand` states the corresponding equality, but only under
`[FiniteDimensional]` and through an eigenvector basis; no finite-dimensionality instance and no
eigenvalue appear here. `Λ` is a parameter and `hpos`, `hray` are inputs.

DERIVED: `0` is the lower bound in `hΛ : 0 ≤ Λ`, the value of the two orthogonality conditions, and
the lower bound in `hpos`. `2` is the exponent in `‖y‖ ^ 2` of the Rayleigh quotient. -/
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

/-- `periodicCorr D v per d ≤ Λ ^ d * (‖v‖ * ‖v‖) + Λ ^ (per - d) * (‖v‖ * ‖v‖)`, for `v` orthogonal
to the vacuum class.

`Transfer.periodicCorr` is `⟪v, T^d v⟫ + ⟪v, T^(per-d) v⟫`, so this is `inner_pow_le_of_rayleigh` at
the two lags added together. The subtraction `per - d` is in `ℕ`.

Scope: `periodicCorr` itself carries no `FiniteDimensional` instance, so this is stated about that
definition rather than a copy of it. No relation between `d` and `per` is assumed beyond `d : Fin per`.

DERIVED: `0` is the lower bound in `hΛ : 0 ≤ Λ`, the value of the orthogonality conditions, and the
lower bound in `hpos`. `2` is the exponent in `‖y‖ ^ 2` of the Rayleigh quotient. -/
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

/-- `periodicCorr D v per d ≤ 2 * (‖v‖ * ‖v‖) * Λ ^ d`, for `v` orthogonal to the vacuum class,
`0 ≤ Λ ≤ 1`, and `d` at most half the period.

`periodicCorr_le_of_rayleigh` splits the correlator into its two arcs; `2 * d ≤ per` gives
`d ≤ per - d`, and `Λ ≤ 1` then makes the far arc's factor no larger than the near arc's.

Scope. The half-period condition is required: past half the period a torus correlator turns back up,
which is why `Spectral.periodic_decay_le` carries the same condition. `hΛ1 : Λ ≤ 1` is a hypothesis
rather than a consequence, so the statement names what its proof uses; `Transfer.Tq_norm_le` makes
`Λ = 1` admissible for every `TransferData`, so the hypothesis excludes only bounds already weaker
than that. `hpos` and `hray` are on the vacuum complement only, and `v` must lie there.
`Transfer.periodic_decay_of_transfer` instead assumes a bound at every eigenvalue and holds at every
`v`; neither statement implies the other.

DERIVED: `2` is the number of arcs in `Transfer.periodicCorr`, appearing as the factor in
`2 * (‖v‖ * ‖v‖)`; it is also the halving in `2 * d ≤ per` and the exponent in `‖y‖ ^ 2` of the
Rayleigh quotient. `1` is the upper bound in `hΛ1 : Λ ≤ 1`, the value a transfer operator's own norm
bound always permits. `0` is the lower bound in `hΛ`, the value of the orthogonality conditions, and
the lower bound in `hpos`. None is a threshold. -/
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

/-- A Rayleigh bound `⟪D.Tq y, y⟫ ≤ Λ * ‖y‖ ^ 2` holding at every `y`, with no orthogonality
restriction, forces `1 ≤ Λ`.

The hypothesis evaluated at the vacuum class: `Transfer.Tq_vacGNS` gives `T Ω = Ω` and
`Transfer.norm_vacGNS` gives `‖Ω‖ = 1`, so the left side is `1` and the right side is `Λ`.

Scope: the hypothesis is quantified over all of `GNS D.toReflForm`. Restricting it to the vacuum
complement, as every other statement in this section does, removes the witness and the conclusion.
`Transfer.one_le_of_eigenvalues_le` is the corresponding statement about an eigenvalue family and
needs a finite-dimensionality instance; this one does not.

DERIVED: `1` is the value of `⟪T Ω, Ω⟫` and of `‖Ω‖`, and so the lower bound concluded. `2` is the
exponent in `‖y‖ ^ 2` of the Rayleigh quotient. -/
theorem one_le_of_rayleigh_le (D : TransferData A) {Λ : ℝ}
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) : 1 ≤ Λ := by
  have h := hray D.vacGNS
  rw [TransferData.Tq_vacGNS D, real_inner_self_eq_norm_mul_norm,
    TransferData.norm_vacGNS D] at h
  simpa using h

#print axioms one_le_of_rayleigh_le

end Generic

/-! ## §2 Readings of the two slab premises

`OSPositivity.wilsonSlabTransfer` builds a `Transfer.TransferData` on the slab algebra from
`SlabShiftStable` and `SlabShiftContractive`. This section restates each of them.
-/

section Slab

open MassGap.WilsonHypercubic MassGap.WilsonTransfer MassGap.OSPositivity
open MassGap.LogConvex MassGap.ActionSplit

variable {d n N : ℕ} [NeZero n]

/-- `reflForm N τ c β (shiftObs τ F) (shiftObs τ F) = reflForm N τ c β F (shiftObs τ (shiftObs τ F))`.

One application of `WilsonTransfer.reflForm_shiftObs_symm` with the second argument taken to be
`shiftObs τ F`.

Scope: the statement's only hypothesis is the section instance `[NeZero n]`, which makes the extent
nonzero. It holds at every real `β`, every reflection constant and every observable, with no
measurability, boundedness or positivity.

DERIVED: the statement carries no numeral. The two shifts are two applications of one map, written
out rather than indexed. -/
theorem reflForm_shiftObs_self (N : ℕ) (τ : Fin d) (c : Fin n) (β : ℝ)
    (F : (Link d n → MassGap.SUN.SU N) → ℝ) :
    MassGap.Transfer.reflForm N τ c β (shiftObs τ F) (shiftObs τ F)
      = MassGap.Transfer.reflForm N τ c β F (shiftObs τ (shiftObs τ F)) :=
  reflForm_shiftObs_symm N τ c β F (shiftObs τ F)

#print axioms reflForm_shiftObs_self

/-- `OSPositivity.SlabShiftContractive N τ a m β` holds exactly when
`reflForm N τ (a + a) β F (shiftObs τ (shiftObs τ F)) ≤ reflForm N τ (a + a) β F F` for every `F` in
the slab algebra.

The premise as written compares the form at the shifted observable with the form at the observable;
`reflForm_shiftObs_self` moves both shifts to one side, giving the two-step correlator against the
contact value.

Scope. This is a rewriting of one statement, not a link to another. `SpectralBound.SpectralAt β Λ` is
`ρ(2) ≤ Λ² ρ(0)` by `SpectralBound.spectralAt_iff`, and the shape here is that inequality at `Λ = 1`;
but `SpectralBound`'s `ρ` is `wilsonCorrAt`, and identifying it with the transfer two-point function
is what `SecondEigenvalue.lag_two_ratio_of_vacuum_rayleigh` takes as its hypotheses `h0` and `h2`.
Neither side of this equivalence is asserted to hold.

DERIVED: the statement carries no numeral. -/
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

/-- At `n = 2 * m` with `2 ≤ m`, `OSPositivity.SlabShiftStable N τ a m` makes every observable of the
slab algebra constant: `F U = F V` for all configurations `U`, `V`.

`HalfLineTransfer.const_of_shift_stable` states this for every shift-stable submodule of the slab
algebra. `LogConvex.localObs` is such a submodule and `SlabShiftStable` is exactly the preservation
hypothesis at it, so the containment argument is `fun _ hG => hG`. Combined with
`HalfLineTransfer.shiftObs_eq_self_of_shift_stable`, the shift acts as the identity there.

Scope. The extent must be even and `m` at least `2`; `HalfLineTransfer.blkR_shift_stable_of_extent_two`
marks where that boundary is sharp. This is a consequence of the premise, not an assertion that the
premise holds, and it leaves `OSPositivity.wilsonSlabTransfer` unchanged as a theorem.

DERIVED: `2` is the factor in `n = 2 * m`, the two mirror planes of an even extent, and the lower
bound in `hm2 : 2 ≤ m`, which is where `HalfLineTransfer.const_of_shift_stable` becomes available. -/
theorem const_of_slabShiftStable (N : ℕ) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm2 : 2 ≤ m) (h : SlabShiftStable N τ a m)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF : F ∈ localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))
    (U V : Link d n → MassGap.SUN.SU N) : F U = F V :=
  MassGap.HalfLineTransfer.const_of_shift_stable τ a m hm hm2 (fun _ hG => hG) h hF U V

#print axioms const_of_slabShiftStable

end Slab

end MassGap.PeriodicRayleigh
