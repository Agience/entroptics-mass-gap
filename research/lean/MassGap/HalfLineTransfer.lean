import Mathlib
import MassGap.WilsonTransfer
import MassGap.VolumeRate

/-!
# MassGap.HalfLineTransfer — the lattice shift as a transfer operator on a periodic lattice

`Transfer.TransferData` carries six own fields beyond `ReflForm` — `T`, `vac`, `T_symm`,
`T_contract`, `T_vac` and `vac_norm`. On the Wilson measure `WilsonTransfer` supplies ingredients for
three of them: `shiftObs` as `T`, `reflForm_shiftObs_symm` as `T_symm`, and `shiftObs_one` with
`expect_shift_invariant` toward `T_vac`. It assembles no `TransferData`, and
`shift_not_stable_on_slab` exhibits one link whose image under the lattice shift leaves the slab.
This file proves two further statements about that shift.

## 1. `n` steps of the shift is the identity

`shiftObs_pow_period`: `(shiftObs τ)^n F = F` for every observable `F` of the lattice of extent `n`,
because `n` steps along `τ` is the identity on sites. There is no hypothesis on the module, the
coupling or the reflection.

`no_rate_below_one_of_finite_order` takes a `Transfer.TransferData` whose `T` satisfies `T^p = id` for
some `p > 0` and a per-step contraction factor `ρ₁ < 1` on the vacuum complement, and concludes that
the complement is zero: `VolumeRate.norm_Tq_pow_le` gives `‖T^p x‖ ≤ ρ₁^p‖x‖` while `T^p = id` gives
`‖T^p x‖ = ‖x‖`. `no_rate_of_shift_transfer` is the same statement for any `TransferData` on a
submodule of Wilson observables whose `T` is the one-step shift, at any extent and on any module.

## 2. Shift-stable submodules of the slab algebra

`const_of_shift_stable`: at even extent `n = 2m` with `2 ≤ m`, every submodule of the slab algebra
`LogConvex.localObs (blkS τ a m) (blkR τ a m)` that is stable under `shiftObs τ` consists of constant
observables, and `shiftObs_eq_self_of_shift_stable` says the shift acts on such a module as the
identity.

The argument quantifies over submodules, not over support sets. Determination by a set of links is
closed under intersection (`detBy_inter`, proved by splicing two configurations along the set).
Stability pushes a determination set through every power of the shift (`detBy_iterate`), and no link
keeps its whole `τ`-orbit inside the slab (`orbitCore_eq_empty`): an axis link is admitted only below
level `m` and its orbit meets level `m`, and a transverse link is admitted only up to level `m` and
its orbit meets level `m + 1`, which lies below the extent because `2 ≤ m`. Determination by the empty
set is constancy.

`2 ≤ m` is not slack. At `n = 2` the admitted transverse levels `{0, m} = {0, 1}` are the whole cycle,
so `blkR τ a 1`, every transverse link, is shift-stable inside the slab
(`blkR_shift_stable_of_extent_two`). `Fin 2` carries no lag `2`, and `shiftObs_pow_period` still
applies at that extent. Extent four has `m = 2` and is covered by `const_of_shift_stable`.

Scope. Every statement is at an arbitrary reflection constant, arbitrary `β` and arbitrary module, on
a lattice periodic in `τ` of extent `n`. Nothing here is stated for an infinite `τ`-direction, and
nothing in this development carries an infinite-volume Gibbs measure: `InfiniteVolume` takes
subsequential limits of finite-volume numbers, not of measures.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.HalfLineTransfer`.
-/

namespace MassGap.HalfLineTransfer

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.CompactGauge
open MassGap.ActionSplit MassGap.LogConvex MassGap.WilsonTransfer
open MassGap.Transfer

/-! ## Part 1 — `n` steps of the lattice shift is the identity -/

section Order

/-- From any level `j` below the extent, some step count `k < n` satisfies `(j + k) % n = t` for any
target level `t` below the extent. The witness is `(n + t - j) % n`. Part 4 uses it to send an orbit
to a chosen level.

DERIVED: the `0` is the positivity of the extent, without which the modulus is not defined; `j` and
`t` are levels of the caller's lattice. -/
theorem exists_step_to_level {n : ℕ} (hn : 0 < n) (j t : ℕ) (hj : j < n) (ht : t < n) :
    ∃ k < n, (j + k) % n = t := by
  refine ⟨(n + t - j) % n, Nat.mod_lt _ hn, ?_⟩
  have h1 : (j + (n + t - j) % n) % n = (j + (n + t - j)) % n := Nat.add_mod_mod _ _ _
  have h2 : j + (n + t - j) = n + t := by omega
  rw [h1, h2, Nat.add_mod_left, Nat.mod_eq_of_lt ht]

variable {d n : ℕ} [NeZero n]

/-- `k` steps of the site shift along `τ` add `fcast n k` to the `τ`-coordinate and leave the others
alone: the iterate is a single `Function.update`. Proved by induction on `k`.

DERIVED: no numeral. -/
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

/-- `n` steps of the site shift along `τ` is the identity. The `τ`-coordinate returns to itself
because `fcast n n = 0`. The statement is that `n` steps act trivially; it does not say `n` is the
least such count.

DERIVED: no numeral. -/
theorem shift_iterate_period (τ : Fin d) (x : Site d n) : (shift τ)^[n] x = x := by
  rw [shift_iterate, fcast_self, add_zero, Function.update_eq_self]

/-- Iterating the link shift moves the base site by the iterated site shift and leaves the direction
alone. Induction on `k`.

DERIVED: no numeral; the `.1` and `.2` are the projections of a link onto its direction and its base
site, not magnitudes. -/
theorem shiftLink_iterate (τ : Fin d) (k : ℕ) (l : Link d n) :
    (shiftLink τ)^[k] l = (l.1, (shift τ)^[k] l.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply' (shiftLink τ), ih,
        Function.iterate_succ_apply' (shift τ)]
      rfl

/-- The direction component of an iterated link shift is the original direction, read off
`shiftLink_iterate`.

DERIVED: no numeral; the `.1` is the projection of a link onto its direction. -/
theorem shiftLink_iterate_fst (τ : Fin d) (k : ℕ) (l : Link d n) :
    ((shiftLink τ)^[k] l).1 = l.1 := by
  rw [shiftLink_iterate]

/-- `n` steps of the link shift is the identity on links, from `shiftLink_iterate` and
`shift_iterate_period`. It does not say `n` is the least such count.

DERIVED: no numeral. -/
theorem shiftLink_iterate_period (τ : Fin d) (l : Link d n) : (shiftLink τ)^[n] l = l := by
  rw [shiftLink_iterate, shift_iterate_period]

/-- The level of a site after `k` steps of the shift is `(level + k) % n`, measured from the base point
`a`. This is the arithmetic the orbit argument of Part 4 runs on; `lv_add_fcast` and `fcast_mod` carry
the modular arithmetic.

DERIVED: no numeral. -/
theorem lv_shift_iterate (τ : Fin d) (a : Fin n) (k : ℕ) (x : Site d n) :
    lv a (((shift τ)^[k] x) τ) = (lv a (x τ) + k) % n := by
  have h1 : ((shift τ)^[k] x) τ = x τ + fcast n k := by
    rw [shift_iterate]
    exact Function.update_self _ _ _
  have h2 : x τ + fcast n k = a + fcast n ((lv a (x τ) + k) % n) := by
    rw [fcast_mod, ← fcast_add, ← add_assoc, ← eq_add_lv]
  rw [h1, h2, lv_add_fcast a _ (Nat.mod_lt _ (NeZero.pos n))]

/-- The level of an iterated link shift's base site is `(level + k) % n`: `lv_shift_iterate` applied
through `shiftLink_iterate`.

DERIVED: no numeral; the `.2` is the projection of a link onto its base site. -/
theorem lv_shiftLink_iterate (τ : Fin d) (a : Fin n) (k : ℕ) (l : Link d n) :
    lv a (((shiftLink τ)^[k] l).2 τ) = (lv a (l.2 τ) + k) % n := by
  rw [shiftLink_iterate]
  exact lv_shift_iterate τ a k l.2

/-- `k` steps of the configuration shift precompose the configuration with `k` steps of the link
shift. Induction on `k`; the period statement is the separate `shiftConf_period`.

DERIVED: no numeral. -/
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

/-- `n` steps of the configuration shift is the identity, for a configuration valued in any type `G`.
It composes `shiftConf_iterate` with `shiftLink_iterate_period`, and does not say `n` is the least
such count.

DERIVED: no numeral. -/
theorem shiftConf_period {G : Type} (τ : Fin d) (U : Link d n → G) :
    (shiftConf τ)^[n] U = U := by
  rw [shiftConf_iterate]
  funext l
  rw [shiftLink_iterate_period]

variable {N : ℕ}

/-- The `k`-th power of the shift operator on observables acts by precomposing with `k` steps of the
configuration shift. Induction on `k`.

DERIVED: no numeral. -/
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

/-- The `n`-th power of the shift operator is the identity on every observable of a lattice of extent
`n`, where `n` is the extent the observable's configuration type is indexed by. There is no hypothesis
on the module, the coupling or the reflection: it follows from `shiftObs_pow_apply` and
`shiftConf_period`. It does not say `n` is the least power that acts trivially.

DERIVED: no numeral. -/
theorem shiftObs_pow_period (τ : Fin d) (F : (Link d n → MassGap.SUN.SU N) → ℝ) :
    ((shiftObs (n := n) (N := N) τ) ^ n) F = F := by
  rw [shiftObs_pow_apply]
  funext U
  rw [shiftConf_period]

end Order

/-! ## Part 2 — a transfer operator of finite order has no contraction rate below one -/

section FiniteOrder

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The `k`-th power of `TransferData.Tq` on a GNS class is the class of the `k`-th power of `T` on a
representative. Induction on `k`, from `TransferData.Tq_mk`.

DERIVED: no numeral. -/
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

/-- For a `TransferData` whose `T` satisfies `T^p = id` at some `p > 0`, a per-step contraction
`‖Tq y‖ ≤ ρ₁‖y‖` on the vacuum complement with `0 ≤ ρ₁ < 1` forces every vector of that complement to
be zero. `VolumeRate.norm_Tq_pow_le` iterates the per-step bound to `‖Tq^p x‖ ≤ ρ₁^p‖x‖`, and
`Tq_pow_mk` with `hper` makes the left-hand side `‖x‖`.

The module `A` is an arbitrary real vector space. The proof uses `T_symm` through `norm_Tq_pow_le` and
nothing else about the form.

DERIVED: the `0` in `0 < p` is what makes `ρ₁^p` strictly below one; the `0` in `0 ≤ ρ₁` is the sign of
a norm ratio; the `1` in `ρ₁ < 1` is the vacuum's own eigenvalue, the value a contraction must beat;
the `0`s in `inner ℝ D.vacGNS y = 0` and `x = 0` are the orthogonality to the vacuum and the
conclusion. -/
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

/-- If `D.T` acts as `shiftObs τ` on representatives, then `D.T ^ k` acts as `(shiftObs τ) ^ k` on
them. Induction on `k`, carrying the coercion out of the submodule at each step.

DERIVED: no numeral. -/
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

/-- For any submodule `M` of the Wilson observables at extent `n`, any `TransferData` on `M` whose `T`
acts as the one-step shift on representatives, and any per-step contraction factor `ρ₁ < 1` on the
vacuum complement, that complement is zero. `shiftObs_pow_period` supplies `T^n = id` through
`T_pow_coe_of_shift`, and `no_rate_below_one_of_finite_order` does the rest.

`M` is arbitrary, so the statement is not about shift-stability on one block; it holds at every extent
`n` with `NeZero n`.

DERIVED: the `0` in `0 ≤ ρ₁` is the sign of a norm ratio; the `1` in `ρ₁ < 1` is the vacuum's own
eigenvalue; the `0`s in `inner ℝ D.vacGNS y = 0` and `x = 0` are the orthogonality to the vacuum and
the conclusion. -/
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

/-- `F` is determined by the links in `E`: any two configurations agreeing on `E` give `F` the same
value. It is the locality clause of `LogConvex.localObs` with the two blocks merged and the
measurability and boundedness clauses dropped, which is all Part 4 uses.

DERIVED: no numeral. -/
def DetBy (E : Set ι) (F : (ι → Ω) → ℝ) : Prop :=
  ∀ U V : ι → Ω, (∀ i ∈ E, U i = V i) → F U = F V

/-- Determination is closed under intersection: if `F` is determined by `E₁` and by `E₂`, it is
determined by `E₁ ∩ E₂`.

Given `U` and `V` agreeing on `E₁ ∩ E₂`, splice them: `W` follows `U` on `E₁` and `V` off it. Then `W`
agrees with `U` on `E₁`, and with `V` on `E₂` — on `E₂ \ E₁` because it is `V` there, and on `E₂ ∩ E₁`
because `U` and `V` agree there. So `F U = F W = F V`.

DERIVED: no numeral. -/
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

/-- An observable determined by the empty set takes the same value on any two configurations: the
agreement hypothesis of `DetBy` is vacuous there.

DERIVED: no numeral. -/
theorem const_of_detBy_empty {F : (ι → Ω) → ℝ} (h : DetBy (∅ : Set ι) F) (U V : ι → Ω) :
    F U = F V :=
  h U V (fun i hi => absurd hi (by simp))

variable [MeasurableSpace Ω]

/-- An observable in `localObs S R` is determined by the union of the two blocks. It reads the locality
clause of `localObs` and weakens the two agreement hypotheses to one over `S ∪ R`.

DERIVED: no numeral. -/
theorem detBy_of_mem_localObs [DecidableEq ι] {S R : Finset ι} {F : (ι → Ω) → ℝ}
    (hF : F ∈ localObs S R) : DetBy (↑(S ∪ R) : Set ι) F := by
  intro U V hUV
  refine hF.2.2 U V (fun i hi => hUV i ?_) (fun i hi => hUV i ?_)
  · exact Finset.mem_coe.mpr (Finset.mem_union_left _ hi)
  · exact Finset.mem_coe.mpr (Finset.mem_union_right _ hi)

end Determination

section Stable

variable {d n N : ℕ} [NeZero n]

/-- If `shiftObs τ F` is determined by `E`, then `F` is determined by `shiftLink τ ⁻¹' E`.

No inverse shift is introduced: `n − 1` further steps invert one step (`shiftLink_iterate_period`), so
each configuration is exhibited as a shift of one built from it.

DERIVED: no numeral. -/
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

/-- The set of links whose first `k` shifts all stay inside `X`: `{l | ∀ j < k, (shiftLink τ)^[j] l ∈ X}`.
It is the candidate determination set after `k` uses of stability.

DERIVED: no numeral. -/
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

/-- For a submodule `M` inside the slab algebra and stable under `shiftObs τ`, every `F ∈ M` is
determined by the `k`-step preimage of the slab's link set, at every `k`. Induction on `k`, pushing
`F` through `hMstab` and pulling the determination set back with `detBy_of_detBy_shiftObs`.

DERIVED: no numeral. -/
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

/-- For the same `M`, every `F ∈ M` is determined by the `k`-fold orbit core of the slab's link set, at
every `k`. Induction on `k`: `orbitCore_succ` splits the core as an intersection and `detBy_inter`
combines the two determination statements.

DERIVED: no numeral. -/
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

/-- At even extent `n = 2m` with `2 ≤ m`, the `n`-fold orbit core of the slab's link set is empty: no
link keeps its whole `τ`-orbit inside the slab.

An axis link is admitted only strictly below level `m`, and `exists_step_to_level` sends its orbit to
level `m`; a transverse link is admitted only up to level `m`, and its orbit is sent to level `m + 1`,
which is below the extent because `2 ≤ m`. Both targets are read off `mem_blkS_union_blkR`.

DERIVED: the `2` in `n = 2 * m` makes the extent twice the slab width, and the `2` in `2 ≤ m` is what
puts level `m + 1` below the extent — the two levels the union refuses for the two kinds of link are
`m` and `m + 1`, neither chosen. -/
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

/-- At even extent `n = 2m` with `2 ≤ m`, every `F` in a submodule of the slab algebra that is stable
under `shiftObs τ` is constant: it takes the same value on any two configurations.

The quantification is over submodules, not over submodules cut out by a support set. An observable in
such a module is determined by the orbit core at every depth (`detBy_orbitCore`), the core at depth
`n` is empty (`orbitCore_eq_empty`), and determination by the empty set is constancy.

The hypothesis `2 ≤ m` is not slack: `blkR_shift_stable_of_extent_two` exhibits a shift-stable module
inside the slab at `n = 2`.

DERIVED: the `2` in `n = 2 * m` makes the extent twice the slab width, and the `2` in `2 ≤ m` is what
`orbitCore_eq_empty` needs; together they put the extent at four or more. -/
theorem const_of_shift_stable (hm : n = 2 * m) (hm2 : 2 ≤ m)
    {M : Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ)}
    (hMsub : ∀ F ∈ M, F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hMstab : ∀ F ∈ M, shiftObs τ F ∈ M)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ M)
    (U V : Link d n → MassGap.SUN.SU N) : F U = F V := by
  have h := detBy_orbitCore τ a m hMsub hMstab n F hF
  rw [orbitCore_eq_empty τ a m hm hm2] at h
  exact const_of_detBy_empty h U V

/-- Under the same hypotheses, the shift fixes every element of such a module: `shiftObs τ F = F`. It
is `const_of_shift_stable` read at the shifted and unshifted configuration.

DERIVED: the `2`s are `const_of_shift_stable`'s, the extent being twice the slab width and the slab
width being at least two. -/
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

/-- At extent two, `blkR τ a 1` is stable under the link shift. `blkR τ a 1` is every transverse link
there, because the two admitted levels `0` and `m = 1` are the whole cycle, so the shift cannot leave
it. This is why `const_of_shift_stable` asks for `2 ≤ m`.

Scope. The statement is about one block at one extent. `Fin 2` carries no lag `2`, and
`shiftObs_pow_period` applies at this extent as at any other.

DERIVED: the `2` is the extent fixed by `hn2`, and the `1` is `m` at that extent, forced by
`n = 2 * m`. -/
theorem blkR_shift_stable_of_extent_two (hn2 : n = 2) (τ : Fin d) (a : Fin n)
    {l : Link d n} (hl : l ∈ blkR τ a 1) : shiftLink τ l ∈ blkR τ a 1 := by
  obtain ⟨hne, hor⟩ := (mem_blkR τ a 1 l).mp hl
  refine (mem_blkR τ a 1 (shiftLink τ l)).mpr ⟨hne, ?_⟩
  have h := lv_shift_axis τ a l.2
  rw [shiftLink_snd, h]
  subst hn2
  omega

/-- `blkR τ a m` is contained in `blkS τ a m ∪ blkR τ a m`, at every extent and every `m`. It is
`Finset.subset_union_right` and depends on nothing about the blocks.

DERIVED: no numeral. -/
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
