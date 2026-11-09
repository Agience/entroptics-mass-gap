import Mathlib
import MassGap.LocalApe
import MassGap.ReflApe
import MassGap.ContinuumFlow

/-!
# MassGap.ObserverFlow — the localised APE smearing as a `ContinuumFlow.ConfFlow`

The observer at a fixed physical resolution, made formal: at step `k`, `n k` APE steps (`0 ≤ c < 1/6`)
run inside the box of half-width `R k` around each output link, the outside held fixed. The box is
measured on link midpoints (`mid`), so the time reflection maps boxes onto boxes exactly
(`mem_mbox_refl`), and the flow commutes with it (`obsFlow_refl`). It is continuous, gauge covariant
and of range `R k + 3` (`obsFlow_local`), so it is a `ContinuumFlow.ConfFlow` (`obsConfFlow`).
-/

namespace MassGap.ObserverFlow

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.BlockSU2 MassGap.BlockLattice
  MassGap.ApeLattice MassGap.LocalApe MassGap.ReflApe MassGap.LatticeReflection
  MassGap.GaugeInvariantAlgebra

/-- The midpoint of a link in doubled coordinates: `2x + μ̂`.

DERIVED: `2` doubles the coordinates so the midpoint is integral; `1` is the half-step along the link. -/
def mid (l : ILink) : ISite := fun i => 2 * l.2 i + (if l.1 = i then 1 else 0)

/-- The time reflection negates the `τ`-coordinate of a midpoint and fixes the others.

DERIVED: `0` the reflection constant; `2`, `1` as in `mid`. -/
theorem mid_refl (τ : Fin 4) (l : ILink) (i : Fin 4) :
    mid (ireflLink τ 0 l) i = if i = τ then -mid l i else mid l i := by
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = τ <;> by_cases hi : i = τ
  · subst hμ; subst hi; simp [mid, ireflLink, ireflSite] <;> ring
  · subst hμ; simp [mid, ireflLink, ireflSite, hi, Ne.symm hi]
  · subst hi; simp [mid, ireflLink, ireflSite, hμ] <;> ring
  · simp [mid, ireflLink, ireflSite, hμ, hi]

#print axioms mid_refl

/-- **The midpoint box** of half-width `R` around a link.

DERIVED: `2` converts the half-width to doubled coordinates. -/
def mbox (l0 : ILink) (R : ℕ) : Set ILink :=
  {l | ∀ i, mid l0 i - 2 * R ≤ mid l i ∧ mid l i ≤ mid l0 i + 2 * R}

/-- **The reflection maps midpoint boxes onto midpoint boxes.**

DERIVED: `0` the reflection constant. -/
theorem mem_mbox_refl (τ : Fin 4) (l0 l : ILink) (R : ℕ) :
    ireflLink τ 0 l ∈ mbox l0 R ↔ l ∈ mbox (ireflLink τ 0 l0) R := by
  simp only [mbox, Set.mem_setOf_eq, mid_refl]
  constructor <;> intro h i <;> have hh := h i <;> by_cases hi : i = τ <;>
    simp only [hi, if_true, if_false] at hh ⊢ <;> constructor <;> omega

#print axioms mem_mbox_refl

/-- **The localised step commutes with the reflection**, the box reflected with it.

DERIVED: `0` the reflection constant; `1/6` the dominance bound. -/
theorem apeOn_refl {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (τ : Fin 4) (S : Set ILink) (U : IConf G2) :
    apeOn c hc0 hc S (ireflConf τ 0 U)
      = ireflConf τ 0 (apeOn c hc0 hc {l | ireflLink τ 0 l ∈ S} U) := by
  classical
  funext l
  have key := congrFun (apeConf_refl hc0 hc τ U) l
  have hinv := ireflLink_involutive τ 0 l
  simp only [apeOn, ireflConf, Set.mem_setOf_eq, hinv] at key ⊢
  split_ifs <;> simp_all

#print axioms apeOn_refl

/-- Iterates of the localised step commute with the reflection.

DERIVED: `0` is the base of the induction and the reflection constant; `1/6` the dominance bound. -/
theorem apeOnIter_refl {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (τ : Fin 4) (S : Set ILink) (n : ℕ)
    (U : IConf G2) :
    (apeOn c hc0 hc S)^[n] (ireflConf τ 0 U)
      = ireflConf τ 0 ((apeOn c hc0 hc {l | ireflLink τ 0 l ∈ S})^[n] U) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, apeOn_refl, ih]

#print axioms apeOnIter_refl

/-- **The observer flow**: `n` APE steps inside the midpoint box of half-width `R` around each output
link.

DERIVED: `1/6` the dominance bound. -/
noncomputable def obsFlow (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (U : IConf G2) :
    IConf G2 :=
  fun l => (apeOn c hc0 hc (mbox l R))^[n] U l

/-- **The observer flow commutes with the time reflection.**

DERIVED: `0` the reflection constant; `1/6` the dominance bound. -/
theorem obsFlow_refl {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (τ : Fin 4) (U : IConf G2) :
    obsFlow c hc0 hc n R (ireflConf τ 0 U) = ireflConf τ 0 (obsFlow c hc0 hc n R U) := by
  funext l
  have hset : {l' | ireflLink τ 0 l' ∈ mbox l R} = mbox (ireflLink τ 0 l) R := by
    ext l'; exact mem_mbox_refl τ l l' R
  show (apeOn c hc0 hc (mbox l R))^[n] (ireflConf τ 0 U) l = ireflConf τ 0 (obsFlow c hc0 hc n R U) l
  rw [apeOnIter_refl, hset]
  simp only [ireflConf, obsFlow, ireflLink_fst]

#print axioms obsFlow_refl

/-- **The observer flow is gauge covariant.**

DERIVED: `1/6` the dominance bound. -/
theorem obsFlow_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (g : ISite → G2)
    (U : IConf G2) :
    obsFlow c hc0 hc n R (igaugeTransform g U) = igaugeTransform g (obsFlow c hc0 hc n R U) := by
  funext l
  simp only [obsFlow]
  rw [apeOnIter_gauge]
  rfl

#print axioms obsFlow_gauge

/-- **The observer flow is continuous.**

DERIVED: `1/6` the dominance bound. -/
theorem continuous_obsFlow {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) :
    Continuous (obsFlow c hc0 hc n R) :=
  continuous_pi (fun l => (continuous_apply l).comp ((continuous_apeOn hc0 hc _).iterate n))

#print axioms continuous_obsFlow

/-- The midpoint box of half-width `R` and every link near it lie in the box of half-width `R + 2`.

DERIVED: `2` is the widening (one site is two doubled units, plus the half-step). -/
theorem mbox_near (l0 : ILink) (R : ℕ) :
    ∀ l ∈ mbox l0 R, ∀ ν y, Near y l.2 → (ν, y) ∈ mbox l0 (R + 2) := by
  intro l hl ν y hy i
  have h1 := hl i
  have h2 := hy i
  simp only [mid] at h1 ⊢
  push_cast
  split_ifs at h1 ⊢ <;> constructor <;> omega

#print axioms mbox_near

/-- **The observer flow reads only the box of half-width `R + 2`**, whatever the number of steps.

DERIVED: `2` is the widening; `1/6` the dominance bound. -/
theorem obsFlow_local {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (l : ILink)
    {U U' : IConf G2} (h : ∀ l' ∈ mbox l (R + 2), U l' = U' l') :
    obsFlow c hc0 hc n R U l = obsFlow c hc0 hc n R U' l := by
  have hl : l ∈ mbox l (R + 2) := fun i => by constructor <;> omega
  exact apeOnIter_agree hc0 hc (mbox_near l R) n h l hl

#print axioms obsFlow_local

/-- The links whose base lies within `r` of `x` in every coordinate, as a finite set.

DERIVED: no numeral; `r` is the caller's radius. -/
noncomputable def baseBox (x : ISite) (r : ℕ) : Finset ILink :=
  Finset.univ ×ˢ Fintype.piFinset (fun i => Finset.Icc (x i - r) (x i + r))

/-- DERIVED: no numeral. -/
theorem mem_baseBox (x : ISite) (r : ℕ) (l : ILink) :
    l ∈ baseBox x r ↔ ∀ i, x i - r ≤ l.2 i ∧ l.2 i ≤ x i + r := by
  simp [baseBox, Fintype.mem_piFinset]

#print axioms mem_baseBox

/-- The midpoint box of half-width `R + 2` lies in the base box of radius `R + 3`.

DERIVED: `2`, `3` as in `mbox_near` and the half-step. -/
theorem mbox_sub_baseBox (l : ILink) (R : ℕ) {l' : ILink} (h : l' ∈ mbox l (R + 2)) :
    l' ∈ baseBox l.2 (R + 3) := by
  rw [mem_baseBox]
  intro i
  have h1 := h i
  simp only [mid] at h1
  push_cast at h1 ⊢
  split_ifs at h1 <;> constructor <;> omega

#print axioms mbox_sub_baseBox

/-- **The observer as a configuration flow**: at step `k`, `n k` APE steps inside midpoint boxes of
half-width `R k`; range `R k + 3`.

DERIVED: `2` is the rank; `3` the range beyond the box; `1/6` the dominance bound. -/
noncomputable def obsConfFlow (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ) :
    MassGap.ContinuumFlow.ConfFlow 2 where
  V k := obsFlow c hc0 hc (n k) (R k)
  continuous_V k := continuous_obsFlow hc0 hc (n k) (R k)
  gauge k g U := obsFlow_gauge hc0 hc (n k) (R k) g U
  refl k τ U := obsFlow_refl hc0 hc (n k) (R k) τ U
  range k := R k + 3
  local_V k l := ⟨baseBox l.2 (R k + 3), fun l' hl' i => by
      rw [mem_baseBox] at hl'
      have := hl' i
      rw [abs_le]
      push_cast at this ⊢
      constructor <;> omega,
    fun U U' h => obsFlow_local hc0 hc (n k) (R k) l
      (fun l' hl' => h l' (mbox_sub_baseBox l (R k) hl'))⟩

end MassGap.ObserverFlow
