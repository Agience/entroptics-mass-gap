import Mathlib
import MassGap.SchwarzIteration
import MassGap.OSPositivity
import MassGap.HalfLineTransfer

/-!
# MassGap.SlabContractive — `SlabShiftContractive` is not an independent premise

## What this closes

`OSPositivity.wilsonSlabTransfer` produces a `Transfer.TransferData` on the Wilson slab algebra from
**two** named premises and nothing else: `SlabShiftStable` (the shift is an endomorphism) and
`SlabShiftContractive` (it does not expand the reflection form). Its own docstring says *"the distance
from what is proved to a transfer operator is exactly `SlabShiftStable` and `SlabShiftContractive`."*

**It is one premise.** `SlabShiftContractive` follows from `SlabShiftStable` alone.

## Why — a periodic symmetric map cannot expand a positive form

`SchwarzIteration.contract_of_bounded_orbit` derives `T_contract` from `T_symm` plus a uniform bound
on the orbit `⟨Tⁿx, Tⁿx⟩`. On the torus the orbit is **finite**: `HalfLineTransfer.shiftObs_pow_period`
gives `shiftObs τ ^ n = id`, so the orbit visits at most `n` points and the maximum over
`Finset.range n` bounds it. `contract_of_periodic` packages that, and it is general — nothing about
Yang–Mills enters, only that the map is symmetric for the form and has finite order.

The symmetry it needs is already unconditional: `WilsonTransfer.reflForm_shiftObs_symm` holds at every
real coupling and every reflection constant, with no hypothesis, and is what `wilsonSlabTransfer`
already uses for its own `T_symm` field.

## ⚠ And this makes the slab route WORSE, not better

The premise that survives is `SlabShiftStable`, and the tree proves it is fatal:
`HalfLineTransfer.shiftObs_eq_self_of_shift_stable` says a shift-stable submodule of the slab algebra
is acted on by the shift as the IDENTITY at `2 ≤ m`, and `GNSHilbert.shiftSlab_eq_id` is that
statement for this carrier. So `wilsonSlabTransfer`'s operator is `1` whenever its premises hold.

**Removing a premise from a construction whose surviving premise forces triviality is a sharpening of
a no-go, not progress toward a gap.** What it establishes is that contractivity was never the
obstruction: the whole content of the slab route is the stability premise, and that premise is the one
`TransferGap.finite_order_fails_gap` and `shiftObs_eq_self_of_shift_stable` between them close.
-/

namespace MassGap.SlabContractive

open MassGap.Transfer MassGap.SchwarzIteration
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ActionSplit
open MassGap.LogConvex MassGap.ReflectionStrong

/-! ## 1. A periodic symmetric map is a contraction, in general -/

section General

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **AN ORBIT THAT REPEATS IS AN ORBIT THAT IS BOUNDED.** With `T^[n] = id` the iterate at `k` is the
iterate at `k % n`, so the orbit visits at most `n` points.

DERIVED: no numeral. `n` is the caller's period. -/
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

/-- **⭐ A PERIODIC SYMMETRIC MAP CANNOT EXPAND A POSITIVE SEMIDEFINITE FORM.**

`SchwarzIteration.contract_of_bounded_orbit` needs symmetry and a bounded orbit. Finite order supplies
the bound for free: the orbit takes at most `n` values, and the maximum over `Finset.range n` is one
of them.

**No positivity of the operator, no compactness, no spectral theory** — only that the form is positive
semidefinite and the map is symmetric for it and repeats.

DERIVED: no numeral. `n` is the caller's period. -/
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

/-! ## 2. ⭐ At the Wilson slab -/

section Slab

variable {d n N : ℕ} [NeZero n]

/-- The slab shift has the torus's period, on the subtype.

DERIVED: no numeral. `n` is the lattice extent, `shiftObs_pow_period`'s own. -/
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

/-- **⭐ `SlabShiftContractive` FOLLOWS FROM `SlabShiftStable`.**

So `OSPositivity.wilsonSlabTransfer` carries ONE premise, not two, and `SchwarzIteration`'s headline
— that `T_contract` is derived rather than assumed — is cashed at the one site in the tree where a
`T_contract` was a live hypothesis.

**⚠ This does not help the gap.** `GNSHilbert.shiftSlab_eq_id` proves the surviving premise makes the
shift the IDENTITY at `2 ≤ m`, so the operator it buys is `1`. What is established is that
contractivity was never the obstruction.

DERIVED: no numeral. `n` is the extent and the shift's period. -/
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

/-- **AND THE TRANSFER DATA FROM ONE PREMISE.** `wilsonSlabTransfer` with its second premise
discharged.

DERIVED: no numeral. -/
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
