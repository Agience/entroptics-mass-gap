import Mathlib
import MassGap.SchwarzIteration
import MassGap.OSPositivity
import MassGap.HalfLineTransfer

/-!
# MassGap.SlabContractive — contractivity of a finite-order symmetric map

`OSPositivity.wilsonSlabTransfer` takes two premises about the slab shift: `SlabShiftStable`, that
the shift maps the local slab algebra into itself, and `SlabShiftContractive`, that it does not
increase the reflection form. This module derives the second from the first.

## The general statement

`SchwarzIteration.contract_of_bounded_orbit` gives contractivity for a map symmetric with respect to
a positive semidefinite form, provided the orbit quantities `P.form (T^[k] x) (T^[k] x)` are
uniformly bounded in `k`. `iterate_eq_mod_of_period` shows that a map of finite order `n` has
`T^[k] x = T^[k % n] x`, so the orbit takes at most `n` values and the supremum over `Finset.range n`
is a bound. `contract_of_periodic` combines the two.

That lemma is stated for an arbitrary real module `A`, an arbitrary `ReflForm A` and an arbitrary map
`T`. It assumes only symmetry for the form and `T^[n] = id` with `0 < n`. No positivity of `T`, no
topology, no compactness and no spectral theory enters, and no gauge theory appears in its statement.

## At the Wilson slab

`shiftSlab_iterate_period` shows the slab shift has order dividing the temporal extent `n`, by
transporting `HalfLineTransfer.shiftObs_pow_period` through the subtype.
`slabShiftContractive_of_stable` then applies `contract_of_periodic` with the form
`ReflectionStrong.wilsonGibbsReflForm` and the symmetry `WilsonTransfer.reflForm_shiftObs_symm`,
producing `SlabShiftContractive` from `SlabShiftStable`.
`wilsonSlabTransferOfStable` is `wilsonSlabTransfer` with that argument filled in, so it constructs a
`TransferData` from `SlabShiftStable` alone.

Scope: the slab results require an even extent, `n = 2 * m` with `0 < m`, and `N ≠ 0`, and they are
stated on the periodic torus `Link d n` that `Fin n` indexes. Finite order is what supplies the
orbit bound, so the argument applies to the periodic lattice and not to an infinite time axis.
-/

namespace MassGap.SlabContractive

open MassGap.Transfer MassGap.SchwarzIteration
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ActionSplit
open MassGap.LogConvex MassGap.ReflectionStrong

/-! ## 1. A periodic symmetric map is a contraction, in general -/

section General

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A map `T : A → A` of finite order `n` has `T^[k] x = T^[k % n] x` for every `k`. Proved by
writing `k = n * (k / n) + k % n` and iterating the periodicity hypothesis `n * (k / n)` times.

Consequence: the orbit `{T^[k] x : k : ℕ}` is contained in the finite set of iterates below `n`. The
hypothesis `0 < n` is what makes `k % n` meaningful as a representative.

DERIVED: `0` is the strict lower bound on the period `n` in `hn`; it is the only numeral. `n` is the
caller's period and `k` the caller's index. -/
theorem iterate_eq_mod_of_period {T : A → A} {n : ℕ} (hn : 0 < n)
    (hper : ∀ y, T^[n] y = y) (k : ℕ) (x : A) : T^[k] x = T^[k % n] x := by
  have hmul : ∀ (q : ℕ) (y : A), T^[n * q] y = y := by
    intro q
    induction q with
    | zero => intro y; simp
    | succ j ih =>
        intro y
        rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]
  conv_lhs => rw [← Nat.div_add_mod k n]
  rw [Function.iterate_add_apply, hmul]

#print axioms iterate_eq_mod_of_period

/-- For a `ReflForm A` and a map `T : A → A` symmetric for it (`P.form (T y) z = P.form y (T z)`)
with `T^[n] = id` for some `n > 0`, every `x` satisfies `P.form (T x) (T x) ≤ P.form x x`.

The bound `contract_of_bounded_orbit` needs is `(Finset.range n).sup'` of the orbit quantities,
which is a genuine element of the orbit by `iterate_eq_mod_of_period`.

`A` is any real module, `P` any `ReflForm A`, `T` any map: no linearity of `T`, no topology, no
compactness and no operator positivity is assumed, and nothing about a lattice or a gauge group
appears. Finite order is essential — it is the sole source of the orbit bound.

DERIVED: `0` is the strict lower bound on the period `n` in `hn`; it is the only numeral. `n` is the
caller's period. -/
theorem contract_of_periodic (P : ReflForm A) (T : A → A)
    (hsym : ∀ y z, P.form (T y) z = P.form y (T z))
    {n : ℕ} (hn : 0 < n) (hper : ∀ y, T^[n] y = y) (x : A) :
    P.form (T x) (T x) ≤ P.form x x := by
  classical
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.mpr hn⟩
  refine contract_of_bounded_orbit P T hsym x
    ((Finset.range n).sup' hne (fun j => P.form (T^[j] x) (T^[j] x))) (fun k => ?_)
  rw [iterate_eq_mod_of_period hn hper k x]
  exact Finset.le_sup' (fun j => P.form (T^[j] x) (T^[j] x))
    (Finset.mem_range.mpr (Nat.mod_lt _ hn))

#print axioms contract_of_periodic

end General

/-! ## 2. At the Wilson slab -/

section Slab

variable {d n N : ℕ} [NeZero n]

/-- The `n`-th iterate of `OSPositivity.shiftSlab τ a m hstab` is the identity on the local slab
algebra `localObs (blkS τ a m) (blkR τ a m)`, where `n` is the temporal extent carried by `Fin n`.

The proof descends to the underlying observable: iterating `shiftSlab` is `Subtype.ext`-equal to
iterating `WilsonTransfer.shiftObs τ`, that iterate is the monoid power, and
`HalfLineTransfer.shiftObs_pow_period` closes it. So the order divides `n`; the statement does not
claim `n` is least.

Requires `N ≠ 0` and `[NeZero n]`. The period is the extent of the periodic direction, so this is a
torus statement.

DERIVED: `0` is the value `N` is required to differ from in `hN`; it is the only numeral. `n` is the
extent, fixed by the section variable, and `d`, `τ`, `a`, `m` are the caller's. -/
theorem shiftSlab_iterate_period (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hstab : MassGap.OSPositivity.SlabShiftStable N τ a m)
    (F : ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))) :
    (⇑(MassGap.OSPositivity.shiftSlab τ a m hstab))^[n] F = F := by
  have hpow : ∀ (k : ℕ) (G : ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))),
      ((⇑(MassGap.OSPositivity.shiftSlab τ a m hstab))^[k] G : _).1
        = (⇑(MassGap.WilsonTransfer.shiftObs (n := n) (N := N) τ))^[k] G.1 := by
    intro k
    induction k with
    | zero => intro G; simp
    | succ j ih =>
        intro G
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
        rfl
  apply Subtype.ext
  rw [hpow]
  have hper : ∀ (k : ℕ) (H : (Link d n → MassGap.SUN.SU N) → ℝ),
      (⇑(MassGap.WilsonTransfer.shiftObs (n := n) (N := N) τ))^[k] H
        = ((MassGap.WilsonTransfer.shiftObs (n := n) (N := N) τ) ^ k) H := by
    intro k
    induction k with
    | zero => intro H; simp
    | succ j ih =>
        intro H
        rw [Function.iterate_succ_apply, ih, pow_succ]
        rfl
  rw [hper, MassGap.HalfLineTransfer.shiftObs_pow_period]

#print axioms shiftSlab_iterate_period

/-- `OSPositivity.SlabShiftContractive N τ a m β` holds whenever `OSPositivity.SlabShiftStable N τ a m`
does, at `N ≠ 0`, even extent `n = 2 * m` with `0 < m`, and any real coupling `β`.

The proof is `contract_of_periodic` at the form `ReflectionStrong.wilsonGibbsReflForm hN τ a m hm hm0 β`
and the map `shiftSlab τ a m hstab`. Its symmetry hypothesis is discharged by
`WilsonTransfer.reflForm_shiftObs_symm` at reflection constant `a + a`, whose only hypothesis is the
`NeZero n` instance it shares with this statement; its periodicity hypothesis is
`shiftSlab_iterate_period`, and `0 < n` comes from that same instance.

`β` is unconstrained: the conclusion holds at every real coupling, strong or weak.

DERIVED: `0` is the value `N` is required to differ from in `hN` and the strict lower bound on `m` in
`hm0`. `2` is the factor in `hm : n = 2 * m`, the evenness of the extent, which is what allows the
reflection plane and the half-extent `m` to be named. -/
theorem slabShiftContractive_of_stable (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    (hstab : MassGap.OSPositivity.SlabShiftStable N τ a m) :
    MassGap.OSPositivity.SlabShiftContractive N τ a m β := by
  intro F hF
  have hn : 0 < n := NeZero.pos n
  exact contract_of_periodic
    (MassGap.ReflectionStrong.wilsonGibbsReflForm hN τ a m hm hm0 β)
    (⇑(MassGap.OSPositivity.shiftSlab τ a m hstab))
    (fun G H => MassGap.WilsonTransfer.reflForm_shiftObs_symm N τ (a + a) β G.1 H.1)
    hn (shiftSlab_iterate_period hN τ a m hstab) ⟨F, hF⟩

#print axioms slabShiftContractive_of_stable

/-- The `Transfer.TransferData` on the local slab algebra built by
`OSPositivity.wilsonSlabTransfer`, with its contractivity argument supplied by
`slabShiftContractive_of_stable`. The remaining inputs are `N ≠ 0`, the even extent `n = 2 * m` with
`0 < m`, the coupling `β`, and `SlabShiftStable N τ a m`.

Definitionally the same `TransferData` as `wilsonSlabTransfer` at those arguments; the only change is
which of its premises the caller must provide.

DERIVED: `0` is the value `N` is required to differ from in `hN` and the strict lower bound on `m` in
`hm0`. `2` is the factor in `hm : n = 2 * m`. All three are the binders'
(`slabShiftContractive_of_stable` and `wilsonSlabTransfer` share them); the body introduces none. -/
noncomputable def wilsonSlabTransferOfStable (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    (hstab : MassGap.OSPositivity.SlabShiftStable N τ a m) :
    MassGap.Transfer.TransferData
      ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m)) :=
  MassGap.OSPositivity.wilsonSlabTransfer hN τ a m hm hm0 β hstab
    (slabShiftContractive_of_stable hN τ a m hm hm0 β hstab)

#print axioms wilsonSlabTransferOfStable

end Slab

end MassGap.SlabContractive
