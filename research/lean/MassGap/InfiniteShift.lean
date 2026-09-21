import Mathlib
import MassGap.InfiniteLattice

/-!
# MassGap.InfiniteShift — a time translation that is neither the identity nor of finite order

## The obstruction this answers

`Transfer.TransferData` asks for `T : A →ₗ[ℝ] A` — an ENDOMORPHISM of the observable algebra. The
Wilson time shift is not one on any finite carrier the tree has, and the tree proves this twice, by
two unrelated arguments:

| carrier | closed by | why |
|---|---|---|
| the fixed-block slab algebra | `HalfLineTransfer.shiftObs_eq_self_of_shift_stable` | asking the shift to land back inside ONE FIXED BLOCK forces it to be the identity |
| any algebra on the torus `Link d n` | `TransferGap.finite_order_fails_gap` | `shiftObs_pow_period` gives `shiftObs^[n] = id`, and a finite-order operator cannot carry a gap |

**Read the first no-go's hypothesis and it says what to build.** `const_of_shift_stable` requires

    hMsub : ∀ F ∈ M, F ∈ localObs (blkS τ a m) (blkR τ a m)

— every element determined by ONE FIXED finite block. The proof needs exactly that: `detBy_orbitCore`
intersects the shifted copies of *the same* block and `orbitCore_eq_empty` empties the intersection.
**A directed union of local algebras satisfies no such hypothesis**, because an observable in it is
determined by *some* finite set and the shift carries that set to another finite set. The support is
allowed to MOVE rather than required to STAY. The no-go does not reach the union — not because the
union evades it, but because its hypothesis is false of the union.

`InfiniteLattice.quasiLocalAlg` is that directed union, already built, and `ISite = Fin 4 → ℤ` makes
it infinite in every direction. **This file shows the shift acts on it, and acts non-trivially.**

## What is proved

* `ishiftObs_mem_quasiLocalAlg` — the shift is an endomorphism of the quasi-local algebra. Its
  support moves from `S` to `S.image (ishiftLink μ)`, which is what the slab could not do.
* `ishiftObs_ne_id_of_separating` — it is **not the identity**, so the first no-go's conclusion fails
  here, as its hypothesis predicted.
* `ishiftObs_infinite_order` — no positive power of it is the identity, so
  `TransferGap.finite_order_fails_gap` does not apply either. This is where `ℤ` is doing the work:
  `ishift` adds one to a coordinate, and `k` steps add `k`, which is never zero for `k > 0`.

**So this is the first carrier in the tree on which the time translation is a non-trivial
endomorphism of infinite order** — the two properties every finite carrier was proved to lack.

## ⚠ What is NOT proved, and it is the larger half

**No reflection form, no positivity, no `TransferData`.** A `TransferData` on this algebra needs a
Gibbs reflection form on `IConf` with `form_nonneg`, `T_symm` and `T_contract`, and those need the
infinite-volume state (`DLRLimit`) together with reflection positivity transported to it. None of
that is here. What is closed is the *structural* obstruction that made the finite carriers worthless;
what remains is the analysis.

**This file therefore proves a necessary condition, not a sufficient one.** A carrier on which the
shift is trivial is certainly useless; that this one is non-trivial does not by itself make it
useful, and nothing here should be read as saying the transfer operator has been built.
-/

namespace MassGap.InfiniteShift

open MassGap.InfiniteLattice

section Shift

variable {G : Type} [TopologicalSpace G]

/-! ## 1. The shift, on links, configurations and observables -/

/-- **TRANSLATE A LINK** one step in direction `μ`: same direction, base site moved.

DERIVED: no numeral of its own — the step is `InfiniteLattice.ishift`'s. -/
def ishiftLink (μ : Fin 4) (l : ILink) : ILink := (l.1, ishift μ l.2)

/-- **TRANSLATE A CONFIGURATION** by pulling back along the link shift.

DERIVED: `4` is the spacetime dimension, the same constant `InfiniteLattice.ISite` and `ILink` are
built on. It is the direction index's range, not a size. -/
def ishiftConf (μ : Fin 4) (U : IConf G) : IConf G := fun l => U (ishiftLink μ l)

/-- **TRANSLATE AN OBSERVABLE** by precomposition — this is the map that must be an endomorphism.

DERIVED: `4` is the spacetime dimension again, as in `ishiftConf`. -/
def ishiftObs (μ : Fin 4) (F : IConf G → ℝ) : IConf G → ℝ := fun U => F (ishiftConf μ U)

/-! ## 2. The shift moves every site, and keeps moving -/

/-- **`k` STEPS ADD `k` TO THE COORDINATE.** This is the whole of why the infinite lattice differs
from the torus: on `Fin n` the coordinate wraps, on `ℤ` it does not.

DERIVED: no numeral. The `1` inside `ishift` is one lattice step. -/
theorem ishift_iterate (μ : Fin 4) (k : ℕ) (x : ISite) :
    ((ishift μ)^[k] x) μ = x μ + k := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ishift, Function.update_self, ih]
      push_cast
      ring

#print axioms MassGap.InfiniteShift.ishift_iterate

/-- **SO NO POSITIVE NUMBER OF STEPS RETURNS A SITE.** The torus statement
`HalfLineTransfer.shift_iterate_period` has no counterpart here, and that is the point.

DERIVED: the `0` is the excluded step count; nothing is chosen. -/
theorem ishift_iterate_ne (μ : Fin 4) {k : ℕ} (hk : 0 < k) (x : ISite) :
    (ishift μ)^[k] x ≠ x := by
  intro h
  have hcoord : ((ishift μ)^[k] x) μ = x μ := congrFun h μ
  rw [ishift_iterate] at hcoord
  omega

#print axioms MassGap.InfiniteShift.ishift_iterate_ne

/-- The link shift inherits it. -/
theorem ishiftLink_iterate_ne (μ : Fin 4) {k : ℕ} (hk : 0 < k) (l : ILink) :
    (ishiftLink μ)^[k] l ≠ l := by
  have hfst : ∀ j : ℕ, ((ishiftLink μ)^[j] l) = (l.1, (ishift μ)^[j] l.2) := by
    intro j
    induction j with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, ishiftLink, Function.iterate_succ_apply']
  intro h
  rw [hfst k] at h
  exact ishift_iterate_ne μ hk l.2 (congrArg Prod.snd h)

#print axioms MassGap.InfiniteShift.ishiftLink_iterate_ne

/-! ## 3. Iterating the shift on configurations and observables -/

omit [TopologicalSpace G] in
theorem ishiftConf_iterate (μ : Fin 4) (k : ℕ) (U : IConf G) :
    (ishiftConf μ)^[k] U = fun l => U ((ishiftLink μ)^[k] l) := by
  induction k with
  | zero => simp
  | succ j ih =>
      funext l
      rw [Function.iterate_succ_apply']
      show ((ishiftConf μ)^[j] U) (ishiftLink μ l) = _
      rw [ih]
      show U ((ishiftLink μ)^[j] (ishiftLink μ l)) = _
      rw [Function.iterate_succ_apply]

omit [TopologicalSpace G] in
theorem ishiftObs_iterate (μ : Fin 4) (k : ℕ) (F : IConf G → ℝ) :
    (ishiftObs μ)^[k] F = fun U => F ((ishiftConf μ)^[k] U) := by
  induction k with
  | zero => simp
  | succ j ih =>
      funext U
      rw [Function.iterate_succ_apply']
      show ((ishiftObs μ)^[j] F) (ishiftConf μ U) = _
      rw [ih]
      show F ((ishiftConf μ)^[j] (ishiftConf μ U)) = _
      rw [Function.iterate_succ_apply]

/-! ## 4. It is an endomorphism of the quasi-local algebra -/

/-- The shift on configurations is continuous: each output coordinate IS an input coordinate. -/
theorem continuous_ishiftConf (μ : Fin 4) :
    Continuous (ishiftConf (G := G) μ) :=
  continuous_pi fun l => continuous_apply (ishiftLink μ l)

#print axioms MassGap.InfiniteShift.continuous_ishiftConf

omit [TopologicalSpace G] in
/-- **LOCALITY MOVES WITH THE SUPPORT.** An observable local on `S` becomes local on the image of `S`
under the link shift. **This is exactly what a fixed-block algebra cannot do**, and it is the whole
difference between this carrier and the slab.

DERIVED: no numeral. -/
theorem isLocalOn_ishiftObs (μ : Fin 4) {S : Finset ILink} {F : IConf G → ℝ}
    (hF : IsLocalOn S F) :
    IsLocalOn (S.image (ishiftLink μ)) (ishiftObs μ F) := by
  classical
  intro U V h
  refine hF _ _ (fun l hl => ?_)
  exact h (ishiftLink μ l) (Finset.mem_image_of_mem _ hl)

#print axioms MassGap.InfiniteShift.isLocalOn_ishiftObs

/-- **⭐ THE SHIFT IS AN ENDOMORPHISM OF THE QUASI-LOCAL ALGEBRA.**

The support is not required to stay inside one block; it is required only to stay FINITE, and the
shift of a finite set is finite. That is the hypothesis `HalfLineTransfer.const_of_shift_stable`
needs and does not get here.

DERIVED: no numeral. -/
theorem ishiftObs_mem_quasiLocalAlg (μ : Fin 4) {F : IConf G → ℝ}
    (hF : F ∈ quasiLocalAlg (G := G)) :
    ishiftObs μ F ∈ quasiLocalAlg (G := G) := by
  classical
  obtain ⟨hFc, S, hFl⟩ := hF
  exact ⟨hFc.comp (continuous_ishiftConf μ), S.image (ishiftLink μ), isLocalOn_ishiftObs μ hFl⟩

#print axioms MassGap.InfiniteShift.ishiftObs_mem_quasiLocalAlg

/-! ## 5. And it is non-trivial, at every power -/

/-- The witness observable: read one link through a real-valued function.

DERIVED: no numeral. -/
def linkObs (l : ILink) (f : G → ℝ) : IConf G → ℝ := fun U => f (U l)

theorem linkObs_mem_quasiLocalAlg {l : ILink} {f : G → ℝ} (hf : Continuous f) :
    linkObs (G := G) l f ∈ quasiLocalAlg (G := G) := by
  classical
  refine ⟨hf.comp (continuous_coord l), {l}, fun U V h => ?_⟩
  show f (U l) = f (V l)
  rw [h l (Finset.mem_singleton_self l)]

#print axioms MassGap.InfiniteShift.linkObs_mem_quasiLocalAlg

omit [TopologicalSpace G] in
/-- **⛔ NO POSITIVE POWER OF THE SHIFT IS THE IDENTITY.** Both no-gos fail here at once: `k = 1`
gives that the shift is not the identity, and general `k` gives that it has no finite order, so
`TransferGap.finite_order_fails_gap` has no `p` to be applied at.

The separation hypothesis is what makes the statement about the shift rather than about a constant
observable: a group on which every continuous function is constant would make every operator the
identity, and that is a fact about the group, not about the translation.

DERIVED: the `0` is the excluded step count. `g₀`, `g₁` and `f` are the caller's separating data. -/
theorem ishiftObs_infinite_order (μ : Fin 4) {k : ℕ} (hk : 0 < k) (l : ILink)
    {f : G → ℝ} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) :
    (ishiftObs (G := G) μ)^[k] (linkObs l f) ≠ linkObs l f := by
  classical
  intro h
  have hmoved : (ishiftLink μ)^[k] l ≠ l := ishiftLink_iterate_ne μ hk l
  have hval := congrFun h (fun j : ILink => if j = l then g₁ else g₀)
  rw [ishiftObs_iterate] at hval
  simp only [linkObs, ishiftConf_iterate, if_neg hmoved] at hval
  exact hf hval

#print axioms MassGap.InfiniteShift.ishiftObs_infinite_order

/-- **AND IN PARTICULAR IT IS NOT THE IDENTITY** — the direct contradiction of
`HalfLineTransfer.shiftObs_eq_self_of_shift_stable`'s conclusion, on a carrier its hypothesis does
not cover.

DERIVED: the `1` is one shift step, `ishiftObs_infinite_order` at `k = 1`. -/
theorem ishiftObs_ne_id_of_separating (μ : Fin 4) (l : ILink)
    {f : G → ℝ} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) :
    ishiftObs (G := G) μ (linkObs l f) ≠ linkObs l f := by
  have h := ishiftObs_infinite_order μ Nat.one_pos l hf
  rwa [Function.iterate_one] at h

#print axioms MassGap.InfiniteShift.ishiftObs_ne_id_of_separating

end Shift

end MassGap.InfiniteShift
