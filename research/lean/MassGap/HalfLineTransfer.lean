import Mathlib
import MassGap.WilsonTransfer
import MassGap.VolumeRate

/-!
# MassGap.HalfLineTransfer — why a shift-built transfer operator on a periodic lattice carries no gap

`WilsonTransfer` proved three of the five fields of `Transfer.TransferData` on the genuine Wilson
measure and exhibited ONE link whose image under the lattice shift leaves the slab
(`shift_not_stable_on_slab`). That witness leaves two questions open, and this file answers both.

## 1. The shift has order `n`, so no module can carry a gap

`shiftObs_pow_period`: `(shiftObs τ)^n = id` on EVERY observable of the periodic lattice, because
`n` steps along `τ` is the identity on sites. There is no hypothesis on the module, the coupling or
the reflection.

`no_rate_below_one_of_finite_order` turns that into a statement about the object B5 wants. A
`Transfer.TransferData` whose `T` has finite order `p` admits NO per-step contraction factor
`ρ₁ < 1` on the vacuum complement: `VolumeRate.norm_Tq_pow_le` gives `‖T^p x‖ ≤ ρ₁^p‖x‖` while
`T^p = id` gives `‖T^p x‖ = ‖x‖`, so `x = 0`. `no_rate_of_shift_transfer` is the same statement for
any `TransferData` on a submodule of Wilson observables whose `T` is the one-step shift.

**So the spectral route to `ρ(2) ≤ K·ρ(0)` cannot be run with the lattice shift as `T` on a lattice
periodic in `τ`, at any extent, on any module, however the module is chosen.** The eigenvalues of
such a `T` are real (self-adjointness) and satisfy `λ^n = 1`, hence `λ = ±1`;
`VolumeRate.rp_sub_geometric` then delivers `ρ₁ = 1` and nothing else. This is a stronger obstruction
than the failure of shift-stability, and it is independent of it.

## 2. Shift-stability, for ALL submodules rather than for support sets

`const_of_shift_stable`: at `n = 2m` with `2 ≤ m`, EVERY submodule of the slab algebra
`LogConvex.localObs (blkS τ a m) (blkR τ a m)` that is stable under `shiftObs τ` consists of CONSTANT
observables, and `shiftObs_eq_self_of_shift_stable` says the shift acts on it as the identity.

The argument is not about support sets. An observable has a smallest set of links it is determined
by, because determination is closed under intersection (`detBy_inter`, proved by splicing two
configurations along the set). Stability pushes that set through every power of the shift
(`detBy_iterate`), and the links whose whole `τ`-orbit stays inside the slab are none
(`orbitCore_eq_empty`): an axis link admitted below level `m` meets level `m`, and a transverse link
admitted up to level `m` meets level `n − 1 = 2m − 1 > m`. So the smallest determining set is empty
and the observable is constant.

`2 ≤ m` is sharp, not an artefact. At `n = 2` the transverse level set `{0, m} = {0, 1}` is already
the whole cycle, so `blkR τ a 1` — all transverse links — IS shift-stable inside the slab
(`blkR_shift_stable_of_extent_two`). That extent carries no lag `2` at all (`Fin 2` has no such
index) and the shift there still has order two, so part 1 applies to it unchanged. Extent four, the
extent `Complete.wilsonCorrAt 3` is defined at, has `m = 2` and is covered by the theorem.

## What this says about the route

Both obstructions point the same way and neither can be worked around inside this lattice: what a
transfer operator needs is a `τ`-direction with infinitely many levels, so that the shift is not of
finite order and a half-line of levels exists to be stable. Nothing in this development carries an
infinite-volume Gibbs measure — `InfiniteVolume` takes subsequential limits of finite-volume NUMBERS,
not of measures — so that is the cost, and it is a new measure-theoretic foundation rather than a
change of block.

Everything below is stated at an arbitrary reflection constant, arbitrary `β` and arbitrary module,
so nothing here has to be restated when the geometry changes; what changes is that
`shiftObs_pow_period` stops being true, which is the point.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.HalfLineTransfer`.
-/

namespace MassGap.HalfLineTransfer

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.CompactGauge
open MassGap.ActionSplit MassGap.LogConvex MassGap.WilsonTransfer
open MassGap.Transfer

/-! ## Part 1 — the lattice shift has order `n` -/

section Order

/-- **Every level is reachable**: from level `j` some number of steps below the extent lands on
level `t`. The orbit of the shift meets every level, which is what Part 4 reads off it.

DERIVED: no numeral; `j` and `t` are levels of the caller's lattice. -/
theorem exists_step_to_level {n : ℕ} (hn : 0 < n) (j t : ℕ) (hj : j < n) (ht : t < n) :
    ∃ k < n, (j + k) % n = t := by
  refine ⟨(n + t - j) % n, Nat.mod_lt _ hn, ?_⟩
  have h1 : (j + (n + t - j) % n) % n = (j + (n + t - j)) % n := Nat.add_mod_mod _ _ _
  have h2 : j + (n + t - j) = n + t := by omega
  rw [h1, h2, Nat.add_mod_left, Nat.mod_eq_of_lt ht]

variable {d n : ℕ} [NeZero n]

/-- **`k` steps along `τ` add `k` to the `τ`-coordinate.** The site shift only ever touches one
coordinate, so its iterate is a single `Function.update`.

DERIVED: the `1` inside `shift` is one lattice step; `k` is the caller's. -/
theorem shift_iterate (τ : Fin d) (k : ℕ) (x : Site d n) :
    (shift τ)^[k] x = Function.update x τ (x τ + fcast n k) := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply, fcast_zero, add_zero, Function.update_eq_self]
  | succ k ih =>
      rw [Function.iterate_succ_apply' (shift τ), ih]
      show Function.update (Function.update x τ (x τ + fcast n k)) τ
          (Function.update x τ (x τ + fcast n k) τ + 1)
        = Function.update x τ (x τ + fcast n (k + 1))
      rw [Function.update_self, Function.update_idem]
      congr 1
      rw [add_assoc]
      congr 1
      rw [← fcast_one (n := n), fcast_add]

/-- **`n` steps along `τ` is the identity on sites.** The `τ`-coordinate returns to itself because
`fcast n n = 0`; that is the whole content of periodicity in `τ`. -/
theorem shift_iterate_period (τ : Fin d) (x : Site d n) : (shift τ)^[n] x = x := by
  rw [shift_iterate, fcast_self, add_zero, Function.update_eq_self]

/-- Iterating the shift on links moves the base site and leaves the direction alone. -/
theorem shiftLink_iterate (τ : Fin d) (k : ℕ) (l : Link d n) :
    (shiftLink τ)^[k] l = (l.1, (shift τ)^[k] l.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply' (shiftLink τ), ih,
        Function.iterate_succ_apply' (shift τ)]
      rfl

/-- The direction of an iterated shift is untouched. -/
theorem shiftLink_iterate_fst (τ : Fin d) (k : ℕ) (l : Link d n) :
    ((shiftLink τ)^[k] l).1 = l.1 := by
  rw [shiftLink_iterate]

/-- **The link shift has order `n`.** -/
theorem shiftLink_iterate_period (τ : Fin d) (l : Link d n) : (shiftLink τ)^[n] l = l := by
  rw [shiftLink_iterate, shift_iterate_period]

/-- **The level after `k` steps is `(level + k) mod n`.** The one arithmetic fact the orbit argument
needs, and the reason the orbit of any link visits every level.

DERIVED: no numeral of its own; `lv_add_fcast` and `fcast_mod` carry the modular arithmetic. -/
theorem lv_shift_iterate (τ : Fin d) (a : Fin n) (k : ℕ) (x : Site d n) :
    lv a (((shift τ)^[k] x) τ) = (lv a (x τ) + k) % n := by
  have h1 : ((shift τ)^[k] x) τ = x τ + fcast n k := by
    rw [shift_iterate]
    exact Function.update_self _ _ _
  have h2 : x τ + fcast n k = a + fcast n ((lv a (x τ) + k) % n) := by
    rw [fcast_mod, ← fcast_add, ← add_assoc, ← eq_add_lv]
  rw [h1, h2, lv_add_fcast a _ (Nat.mod_lt _ (NeZero.pos n))]

/-- The level of an iterated link shift. -/
theorem lv_shiftLink_iterate (τ : Fin d) (a : Fin n) (k : ℕ) (l : Link d n) :
    lv a (((shiftLink τ)^[k] l).2 τ) = (lv a (l.2 τ) + k) % n := by
  rw [shiftLink_iterate]
  exact lv_shift_iterate τ a k l.2

/-- **`n` steps along `τ` is the identity on configurations.** -/
theorem shiftConf_iterate {G : Type} (τ : Fin d) (k : ℕ) :
    ∀ U : Link d n → G, (shiftConf τ)^[k] U = fun l => U ((shiftLink τ)^[k] l) := by
  induction k with
  | zero => intro U; rfl
  | succ k ih =>
      intro U
      funext l
      rw [Function.iterate_succ_apply, ih]
      show (shiftConf τ U) ((shiftLink τ)^[k] l) = U ((shiftLink τ)^[k + 1] l)
      rw [shiftConf_apply, ← Function.iterate_succ_apply' (shiftLink τ)]

/-- **The configuration shift has order `n`.** -/
theorem shiftConf_period {G : Type} (τ : Fin d) (U : Link d n → G) :
    (shiftConf τ)^[n] U = U := by
  rw [shiftConf_iterate]
  funext l
  rw [shiftLink_iterate_period]

variable {N : ℕ}

/-- A power of the shift operator, read on configurations. -/
theorem shiftObs_pow_apply (τ : Fin d) (k : ℕ)
    (F : (Link d n → MassGap.SUN.SU N) → ℝ) :
    ((shiftObs (n := n) (N := N) τ) ^ k) F = fun U => F ((shiftConf τ)^[k] U) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hstep : ((shiftObs (d := d) (n := n) (N := N) τ) ^ (k + 1)) F
          = shiftObs τ (((shiftObs τ) ^ k) F) := by
        rw [pow_succ']; rfl
      rw [hstep, ih]
      funext U
      show F ((shiftConf τ)^[k] (shiftConf τ U)) = F ((shiftConf τ)^[k + 1] U)
      rw [Function.iterate_succ_apply]

/-- **THE SHIFT OPERATOR HAS ORDER `n` ON EVERY OBSERVABLE.**

No hypothesis: not on the module, not on the coupling, not on the reflection. It is periodicity of
the lattice in `τ` and nothing else, and it is what makes a shift-built transfer operator gapless.

DERIVED: `n` is the extent — the caller's lattice, not a choice made here. -/
theorem shiftObs_pow_period (τ : Fin d) (F : (Link d n → MassGap.SUN.SU N) → ℝ) :
    ((shiftObs (n := n) (N := N) τ) ^ n) F = F := by
  rw [shiftObs_pow_apply]
  funext U
  rw [shiftConf_period]

end Order

/-! ## Part 2 — a transfer operator of finite order has no contraction rate below one -/

section FiniteOrder

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A power of the transfer operator, read on a representative. -/
theorem Tq_pow_mk (D : TransferData A) (k : ℕ) (x : A) :
    ((TransferData.Tq D) ^ k) (GNS.mk D.toReflForm x)
      = GNS.mk D.toReflForm ((D.T ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : ((TransferData.Tq D) ^ (k + 1)) (GNS.mk D.toReflForm x)
          = TransferData.Tq D (((TransferData.Tq D) ^ k) (GNS.mk D.toReflForm x)) := by
        rw [pow_succ']; rfl
      have h2 : (D.T ^ (k + 1)) x = D.T ((D.T ^ k) x) := by
        rw [pow_succ']; rfl
      rw [h1, ih, h2, TransferData.Tq_mk]

/-- **A TRANSFER OPERATOR OF FINITE ORDER ADMITS NO RATE BELOW ONE.**

If `T^p = id` for some `p > 0`, then a per-step contraction `‖T y‖ ≤ ρ₁‖y‖` on the vacuum complement
with `ρ₁ < 1` forces that complement to be zero. `VolumeRate.norm_Tq_pow_le` iterates the per-step
bound to `‖T^p x‖ ≤ ρ₁^p‖x‖`; finite order says the left side is `‖x‖`.

This is the whole obstruction to the spectral route on a periodic lattice, in the abstract. It uses
`T_symm` (through `norm_Tq_pow_le`) and nothing else about the form.

DERIVED: the `1` is the vacuum's own eigenvalue, carried through `ρ₁ < 1`; `p` is the caller's
order. -/
theorem no_rate_below_one_of_finite_order (D : TransferData A) {p : ℕ} (hp : 0 < p)
    (hper : ∀ x : A, (D.T ^ p) x = x)
    {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁) (hρ1 : ρ₁ < 1)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖TransferData.Tq D y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) : x = 0 := by
  obtain ⟨y, rfl⟩ := GNS.exists_mk x
  have hfix : ((TransferData.Tq D) ^ p) (GNS.mk D.toReflForm y) = GNS.mk D.toReflForm y := by
    rw [Tq_pow_mk, hper]
  have hgeo := MassGap.VolumeRate.norm_Tq_pow_le D hρ0 hρ hx p
  rw [hfix] at hgeo
  have hlt : ρ₁ ^ p < 1 := pow_lt_one₀ hρ0 hρ1 (by omega)
  have hnn : (0 : ℝ) ≤ ‖GNS.mk D.toReflForm y‖ := norm_nonneg _
  have hzero : ‖GNS.mk D.toReflForm y‖ = 0 := by nlinarith
  exact norm_eq_zero.mp hzero

end FiniteOrder

/-! ## Part 3 — the same, for the concrete lattice shift -/

section ShiftTransfer

variable {d n N : ℕ} [NeZero n]

/-- A power of a transfer operator that acts as the shift on representatives. -/
theorem T_pow_coe_of_shift
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (D : TransferData ↥M) (τ : Fin d)
    (hT : ∀ F : ↥M, ((D.T F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ)
      = shiftObs τ ((F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ))
    (k : ℕ) (F : ↥M) :
    (((D.T ^ k) F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ)
      = ((shiftObs τ) ^ k) ((F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : (D.T ^ (k + 1)) F = D.T ((D.T ^ k) F) := by rw [pow_succ']; rfl
      have h2 : ((shiftObs (d := d) (n := n) (N := N) τ) ^ (k + 1))
            ((F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ)
          = shiftObs τ (((shiftObs τ) ^ k) ((F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ)) := by
        rw [pow_succ']; rfl
      rw [h1, hT, ih, h2]

/-- **NO TRANSFER OPERATOR BUILT FROM THE LATTICE SHIFT HAS A GAP, ON ANY MODULE.**

Take any submodule `M` of the Wilson observables, any `Transfer.TransferData` on it whose `T` is the
one-step shift, and any per-step contraction factor `ρ₁ < 1` on the vacuum complement: the vacuum
complement is zero. `shiftObs_pow_period` supplies the order, `no_rate_below_one_of_finite_order`
does the rest.

The module is arbitrary. So this is not the failure of shift-stability on one block — it says that
even if a shift-stable positive module were found, `VolumeRate.rp_sub_geometric` applied to it would
deliver `ρ₁ = 1` and the lag-two bound `ρ(2) ≤ K·ρ(0)` with `K < 1` would not follow.

DERIVED: `n` is the extent; the `1` is the vacuum eigenvalue. -/
theorem no_rate_of_shift_transfer
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (D : TransferData ↥M) (τ : Fin d)
    (hT : ∀ F : ↥M, ((D.T F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ)
      = shiftObs τ ((F : ↥M) : (Link d n → MassGap.SUN.SU N) → ℝ))
    {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁) (hρ1 : ρ₁ < 1)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖TransferData.Tq D y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) : x = 0 := by
  refine no_rate_below_one_of_finite_order D (NeZero.pos n) ?_ hρ0 hρ1 hρ hx
  intro F
  refine Subtype.ext ?_
  rw [T_pow_coe_of_shift D τ hT n F, shiftObs_pow_period]

end ShiftTransfer

/-! ## Part 4 — determination sets, and the shift-stable submodules of the slab algebra -/

section Determination

variable {ι : Type} {Ω : Type}

/-- **`F` is determined by the links in `E`** — the locality clause of `LogConvex.localObs`, with the
two blocks merged and the measurability and boundedness clauses dropped, because the argument below
uses only this one. -/
def DetBy (E : Set ι) (F : (ι → Ω) → ℝ) : Prop :=
  ∀ U V : ι → Ω, (∀ i ∈ E, U i = V i) → F U = F V

/-- **DETERMINATION IS CLOSED UNDER INTERSECTION** — the fact that makes "the smallest set an
observable is determined by" exist, and the only non-formal step in Part 4.

Given `U` and `V` agreeing on `E₁ ∩ E₂`, splice them: `W` follows `U` on `E₁` and `V` off it. Then
`W` agrees with `U` on `E₁`, and with `V` on `E₂` — on `E₂ \ E₁` because it IS `V` there, and on
`E₂ ∩ E₁` because `U` and `V` agree there. So `F U = F W = F V`. -/
theorem detBy_inter {E₁ E₂ : Set ι} {F : (ι → Ω) → ℝ}
    (h1 : DetBy E₁ F) (h2 : DetBy E₂ F) : DetBy (E₁ ∩ E₂) F := by
  classical
  intro U V hUV
  have hUW : F U = F (fun i => if i ∈ E₁ then U i else V i) :=
    h1 U _ (fun i hi => by simp only [if_pos hi])
  have hWV : F (fun i => if i ∈ E₁ then U i else V i) = F V := by
    refine h2 _ V (fun i hi => ?_)
    by_cases h : i ∈ E₁
    · simp only [if_pos h]
      exact hUV i ⟨h, hi⟩
    · simp only [if_neg h]
  exact hUW.trans hWV

/-- An observable determined by nothing is constant. -/
theorem const_of_detBy_empty {F : (ι → Ω) → ℝ} (h : DetBy (∅ : Set ι) F) (U V : ι → Ω) :
    F U = F V :=
  h U V (fun i hi => absurd hi (by simp))

variable [MeasurableSpace Ω]

/-- Membership in the local module gives determination by the union of the two blocks. -/
theorem detBy_of_mem_localObs [DecidableEq ι] {S R : Finset ι} {F : (ι → Ω) → ℝ}
    (hF : F ∈ localObs S R) : DetBy (↑(S ∪ R) : Set ι) F := by
  intro U V hUV
  refine hF.2.2 U V (fun i hi => hUV i ?_) (fun i hi => hUV i ?_)
  · exact Finset.mem_coe.mpr (Finset.mem_union_left _ hi)
  · exact Finset.mem_coe.mpr (Finset.mem_union_right _ hi)

end Determination

section Stable

variable {d n N : ℕ} [NeZero n]

/-- **THE SHIFTED OBSERVABLE'S DETERMINATION SET, PULLED BACK.** If one step of the shift is
determined by `E`, the observable itself is determined by the preimage of `E`.

The inverse of the shift is not introduced: `n − 1` further steps invert it
(`shiftConf_period`), so the configuration `U` is exhibited as a shift of one built from `U`
itself. -/
theorem detBy_of_detBy_shiftObs (τ : Fin d) {E : Set (Link d n)}
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (h : DetBy E (shiftObs τ F)) :
    DetBy ((shiftLink τ) ⁻¹' E) F := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  intro U V hUV
  have hper : ∀ l : Link d (p + 1), (shiftLink τ)^[p] (shiftLink τ l) = l := fun l =>
    (Function.iterate_succ_apply (shiftLink τ) p l).symm.trans (shiftLink_iterate_period τ l)
  have hper' : ∀ l : Link d (p + 1), shiftLink τ ((shiftLink τ)^[p] l) = l := fun l =>
    (Function.iterate_succ_apply' (shiftLink τ) p l).symm.trans (shiftLink_iterate_period τ l)
  have hback : ∀ W : Link d (p + 1) → MassGap.SUN.SU N,
      shiftConf τ (fun l => W ((shiftLink τ)^[p] l)) = W := by
    intro W
    funext l
    show W ((shiftLink τ)^[p] (shiftLink τ l)) = W l
    rw [hper]
  have hFU : F U = shiftObs τ F (fun l => U ((shiftLink τ)^[p] l)) := by
    rw [shiftObs_apply, hback]
  have hFV : F V = shiftObs τ F (fun l => V ((shiftLink τ)^[p] l)) := by
    rw [shiftObs_apply, hback]
  rw [hFU, hFV]
  refine h _ _ (fun l hl => ?_)
  refine hUV ((shiftLink τ)^[p] l) ?_
  show shiftLink τ ((shiftLink τ)^[p] l) ∈ E
  rw [hper']
  exact hl

/-- **The links whose first `k` shifts all stay inside `X`.** The candidate determination set after
`k` uses of stability. -/
def orbitCore (τ : Fin d) (X : Set (Link d n)) (k : ℕ) : Set (Link d n) :=
  {l | ∀ j < k, (shiftLink τ)^[j] l ∈ X}

theorem orbitCore_succ (τ : Fin d) (X : Set (Link d n)) (k : ℕ) :
    orbitCore τ X (k + 1) = orbitCore τ X k ∩ ((shiftLink τ)^[k] ⁻¹' X) := by
  ext l
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact h1 j h
    · subst h; exact h2

variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- Stability pushes membership through every power of the shift. -/
theorem detBy_iterate
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (hMsub : ∀ F ∈ M, F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hMstab : ∀ F ∈ M, shiftObs τ F ∈ M) (k : ℕ) :
    ∀ F ∈ M, DetBy ((shiftLink τ)^[k] ⁻¹' (↑(blkS τ a m ∪ blkR τ a m) : Set (Link d n))) F := by
  induction k with
  | zero =>
      intro F hF
      have h := detBy_of_mem_localObs (hMsub F hF)
      intro U V hUV
      exact h U V (fun i hi => hUV i hi)
  | succ k ih =>
      intro F hF
      have h1 := ih (shiftObs τ F) (hMstab F hF)
      have h2 := detBy_of_detBy_shiftObs τ h1
      intro U V hUV
      refine h2 U V (fun l hl => hUV l ?_)
      show (shiftLink τ)^[k + 1] l ∈ (↑(blkS τ a m ∪ blkR τ a m) : Set (Link d n))
      rw [Function.iterate_succ_apply]
      exact hl

/-- The determination set after `k` uses of stability is the `k`-fold orbit core. -/
theorem detBy_orbitCore
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (hMsub : ∀ F ∈ M, F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hMstab : ∀ F ∈ M, shiftObs τ F ∈ M) (k : ℕ) :
    ∀ F ∈ M, DetBy (orbitCore τ (↑(blkS τ a m ∪ blkR τ a m) : Set (Link d n)) k) F := by
  induction k with
  | zero =>
      intro F hF U V hUV
      have hall : ∀ l : Link d n,
          l ∈ orbitCore τ (↑(blkS τ a m ∪ blkR τ a m) : Set (Link d n)) 0 := by
        intro l j hj
        exact absurd hj (Nat.not_lt_zero j)
      have : U = V := funext (fun l => hUV l (hall l))
      rw [this]
  | succ k ih =>
      intro F hF
      rw [orbitCore_succ]
      exact detBy_inter (ih F hF) (detBy_iterate τ a m hMsub hMstab k F hF)

/-- **No link keeps its whole `τ`-orbit inside the slab**, once the extent is at least four.

An axis link is admitted only strictly below level `m`, and its orbit visits level `m`; a transverse
link is admitted only up to level `m`, and its orbit visits level `m + 1`, which is below the extent
exactly because `2 ≤ m`. Both targets are read off `mem_blkS_union_blkR`.

DERIVED: `m` and `m + 1` are the first levels the union refuses for the two kinds of link; neither is
chosen. -/
theorem orbitCore_eq_empty (hm : n = 2 * m) (hm2 : 2 ≤ m) :
    orbitCore τ (↑(blkS τ a m ∪ blkR τ a m) : Set (Link d n)) n = (∅ : Set (Link d n)) := by
  have hn : 0 < n := NeZero.pos n
  ext l
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hl
  have hj : lv a (l.2 τ) < n := lv_lt a _
  by_cases hax : l.1 = τ
  · obtain ⟨k, hk, hkk⟩ :=
      exists_step_to_level hn (lv a (l.2 τ)) m hj (by omega)
    have hmem := hl k hk
    rw [Finset.mem_coe, mem_blkS_union_blkR, shiftLink_iterate_fst, if_pos hax,
      lv_shiftLink_iterate, hkk] at hmem
    omega
  · obtain ⟨k, hk, hkk⟩ :=
      exists_step_to_level hn (lv a (l.2 τ)) (m + 1) hj (by omega)
    have hmem := hl k hk
    rw [Finset.mem_coe, mem_blkS_union_blkR, shiftLink_iterate_fst, if_neg hax,
      lv_shiftLink_iterate, hkk] at hmem
    omega

/-- **EVERY SHIFT-STABLE SUBMODULE OF THE SLAB ALGEBRA IS CONSTANTS**, at extent four and above.

Not "every submodule cut out by a support set" — every submodule. An observable in such a module is
determined by the orbit core at every depth (`detBy_orbitCore`), the core at depth `n` is empty
(`orbitCore_eq_empty`), and determination by nothing is constancy.

`2 ≤ m` is where the statement lives: `blkR_shift_stable_of_extent_two` shows it fails at `n = 2`. -/
theorem const_of_shift_stable (hm : n = 2 * m) (hm2 : 2 ≤ m)
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (hMsub : ∀ F ∈ M, F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hMstab : ∀ F ∈ M, shiftObs τ F ∈ M)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ M)
    (U V : Link d n → MassGap.SUN.SU N) : F U = F V := by
  have h := detBy_orbitCore τ a m hMsub hMstab n F hF
  rw [orbitCore_eq_empty τ a m hm hm2] at h
  exact const_of_detBy_empty h U V

/-- **SO THE SHIFT ACTS ON SUCH A MODULE AS THE IDENTITY.** `T = id` has every eigenvalue one; there
is no vacuum complement to contract and no lag-two ratio below one to extract. -/
theorem shiftObs_eq_self_of_shift_stable (hm : n = 2 * m) (hm2 : 2 ≤ m)
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (hMsub : ∀ F ∈ M, F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hMstab : ∀ F ∈ M, shiftObs τ F ∈ M)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ M) :
    shiftObs τ F = F := by
  funext U
  rw [shiftObs_apply]
  exact const_of_shift_stable τ a m hm hm2 hMsub hMstab hF _ U

end Stable

/-! ## Part 5 — `2 ≤ m` is sharp -/

section Sharp

variable {d n : ℕ} [NeZero n]

/-- **AT EXTENT TWO THE TRANSVERSE LINKS ARE SHIFT-STABLE AND INSIDE THE SLAB.**

`blkR τ a 1` is every transverse link, because at `n = 2` the two admitted levels `0` and `m = 1` are
the whole cycle. So `const_of_shift_stable`'s hypothesis `2 ≤ m` is not slack.

That extent settles nothing about the mass gap. `Fin 2` carries no lag `2`, so `ρ(2)` is not even an
index there, and `shiftObs_pow_period` still says the shift squares to the identity, so Part 3
applies to it unchanged.

DERIVED: `1` is `m` at extent two and `2` is that extent; both are forced by `n = 2 * m`. -/
theorem blkR_shift_stable_of_extent_two (hn2 : n = 2) (τ : Fin d) (a : Fin n)
    {l : Link d n} (hl : l ∈ blkR τ a 1) : shiftLink τ l ∈ blkR τ a 1 := by
  obtain ⟨hne, hor⟩ := (mem_blkR τ a 1 l).mp hl
  refine (mem_blkR τ a 1 (shiftLink τ l)).mpr ⟨hne, ?_⟩
  have h := lv_shift_axis τ a l.2
  rw [shiftLink_snd, h]
  subst hn2
  omega

/-- The transverse links are inside the slab at every extent — level `0` and level `m` are `blkR`'s
own. -/
theorem blkR_subset_slab (τ : Fin d) (a : Fin n) (m : ℕ) :
    blkR τ a m ⊆ blkS τ a m ∪ blkR τ a m := Finset.subset_union_right

end Sharp

#print axioms shift_iterate
#print axioms shift_iterate_period
#print axioms exists_step_to_level
#print axioms shiftLink_iterate
#print axioms shiftLink_iterate_fst
#print axioms shiftLink_iterate_period
#print axioms lv_shift_iterate
#print axioms lv_shiftLink_iterate
#print axioms shiftConf_iterate
#print axioms shiftConf_period
#print axioms shiftObs_pow_apply
#print axioms shiftObs_pow_period
#print axioms Tq_pow_mk
#print axioms no_rate_below_one_of_finite_order
#print axioms T_pow_coe_of_shift
#print axioms no_rate_of_shift_transfer
#print axioms DetBy
#print axioms detBy_inter
#print axioms const_of_detBy_empty
#print axioms detBy_of_mem_localObs
#print axioms detBy_of_detBy_shiftObs
#print axioms orbitCore
#print axioms orbitCore_succ
#print axioms detBy_iterate
#print axioms detBy_orbitCore
#print axioms orbitCore_eq_empty
#print axioms const_of_shift_stable
#print axioms shiftObs_eq_self_of_shift_stable
#print axioms blkR_shift_stable_of_extent_two
#print axioms blkR_subset_slab

end MassGap.HalfLineTransfer
