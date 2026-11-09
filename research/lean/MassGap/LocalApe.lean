import Mathlib
import MassGap.ApeLattice

/-!
# MassGap.LocalApe — APE smearing run inside a box, the outside held fixed

The localised smearing flow: each output link is the result of `n` APE steps run only on the links of a
box around it, every other link frozen. Its range is then the box enlarged by one site, whatever `n`: the
flow has a fixed physical range when the box has a fixed physical size, as `ContinuumFlow.ConfFlow`
needs.

* `apeOn S`: one APE step on the links of `S`, the identity elsewhere. Gauge covariant
  (`apeOn_gauge`), continuous (`continuous_apeOn`).
* `apeOn_agree`: two configurations agreeing on `S` and every link within one site of `S` still agree
  there after one step; `apeOnIter_agree`: after any number.
-/

namespace MassGap.LocalApe

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.BlockSU2 MassGap.BlockLattice
  MassGap.ApeLattice MassGap.GaugeInvariantAlgebra

/-- **One APE step on the links of `S`**, the identity elsewhere.

DERIVED: `1/6` the dominance bound. -/
noncomputable def apeOn (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (S : Set ILink) (U : IConf G2) :
    IConf G2 := by
  classical
  exact fun l => if l ∈ S then apeConf c hc0 hc U l else U l

/-- **The localised step is gauge covariant.**

DERIVED: `1/6` the dominance bound. -/
theorem apeOn_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (S : Set ILink) (g : ISite → G2)
    (U : IConf G2) :
    apeOn c hc0 hc S (igaugeTransform g U) = igaugeTransform g (apeOn c hc0 hc S U) := by
  classical
  funext l
  have key := congrFun (apeConf_gauge hc0 hc g U) l
  simp only [apeOn, igaugeTransform] at key ⊢
  split_ifs with h
  · exact key
  · rfl

#print axioms apeOn_gauge

/-- Iterates of the localised step stay gauge covariant.

DERIVED: `0` is the base of the induction; `1/6` the dominance bound. -/
theorem apeOnIter_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (S : Set ILink) (n : ℕ)
    (g : ISite → G2) (U : IConf G2) :
    (apeOn c hc0 hc S)^[n] (igaugeTransform g U) = igaugeTransform g ((apeOn c hc0 hc S)^[n] U) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, apeOn_gauge, ih]

#print axioms apeOnIter_gauge

/-- **The localised step is continuous.**

DERIVED: `1/6` the dominance bound. -/
theorem continuous_apeOn {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (S : Set ILink) :
    Continuous (apeOn c hc0 hc S) := by
  classical
  refine continuous_pi (fun l => ?_)
  simp only [apeOn]
  split_ifs with h
  · exact (continuous_apply l).comp (continuous_apeConf hc0 hc)
  · exact continuous_apply l

#print axioms continuous_apeOn

/-- The links an APE step at `(μ, x)` reads: base sites within one step of `x` in every coordinate.

DERIVED: `1` is one lattice step. -/
def Near (x y : ISite) : Prop := ∀ i, y i - 1 ≤ x i ∧ x i ≤ y i + 1

/-- The sites the step reads are near.

DERIVED: `1` is one lattice step. -/
theorem near_self (x : ISite) : Near x x := fun i => ⟨by omega, by omega⟩

/-- DERIVED: `1` is one lattice step. -/
theorem near_ishift (μ : Fin 4) (x : ISite) : Near (ishift μ x) x := by
  intro i
  by_cases h : i = μ
  · subst h; simp [ishift] <;> omega
  · simp [ishift, Function.update_of_ne h]

/-- DERIVED: `1` is one lattice step. -/
theorem near_iback (ν : Fin 4) (x : ISite) : Near (iback ν x) x := by
  intro i
  by_cases h : i = ν
  · subst h; simp [iback] <;> omega
  · simp [iback, Function.update_of_ne h]

/-- DERIVED: `1` is one lattice step. -/
theorem near_ishift_ishift {μ ν : Fin 4} (hμν : μ ≠ ν) (x : ISite) :
    Near (ishift μ (ishift ν x)) x := by
  intro i
  by_cases h1 : i = μ <;> by_cases h2 : i = ν
  · exact absurd (h1.symm.trans h2) hμν
  · subst h1; simp [ishift, Function.update_of_ne h2] <;> omega
  · subst h2; simp [ishift, Function.update_of_ne h1] <;> omega
  · simp [ishift, Function.update_of_ne h1, Function.update_of_ne h2]

/-- DERIVED: `1` is one lattice step. -/
theorem near_ishift_iback {μ ν : Fin 4} (hμν : μ ≠ ν) (x : ISite) :
    Near (ishift μ (iback ν x)) x := by
  intro i
  by_cases h1 : i = μ <;> by_cases h2 : i = ν
  · exact absurd (h1.symm.trans h2) hμν
  · subst h1; simp [ishift, iback, Function.update_of_ne h2] <;> omega
  · subst h2; simp [ishift, iback, Function.update_of_ne h1] <;> omega
  · simp [ishift, iback, Function.update_of_ne h1, Function.update_of_ne h2]

/-- A transverse direction differs from the link's.

DERIVED: `3` transverse directions. -/
theorem other_ne (μ : Fin 4) (j : Fin 3) : μ ≠ other μ j := (Fin.succAbove_ne μ j).symm

/-- **The APE step at a link reads only near links**: configurations agreeing on every link based at
a site near `x` give the same output at `(μ, x)`.

DERIVED: `0` names the upper side; `1/6` the dominance bound. -/
theorem apeConf_local {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (μ : Fin 4) (x : ISite)
    {U U' : IConf G2} (h : ∀ ν y, Near y x → U (ν, y) = U' (ν, y)) :
    apeConf c hc0 hc U (μ, x) = apeConf c hc0 hc U' (μ, x) := by
  have hS : ∀ p : Fin 3 × Fin 2, apeStaple U μ x p = apeStaple U' μ x p := by
    intro p
    have hne := other_ne μ p.1
    unfold apeStaple
    split_ifs
    · rw [h _ _ (near_self x), h _ _ (near_ishift _ x), h _ _ (near_ishift _ x)]
    · rw [h _ _ (near_iback _ x), h _ _ (near_iback _ x), h _ _ (near_ishift_iback hne x)]
  simp only [apeConf]
  rw [h _ _ (near_self x)]
  congr 1
  funext i
  exact hS _

#print axioms apeConf_local

/-- **Agreement is preserved by the localised step** on any set `A` that contains `S` and every link
near a link of `S`: inside `S` the step reads only near links (`apeConf_local`), outside it is the
identity.

DERIVED: `1/6` the dominance bound. -/
theorem apeOn_agree {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) {S A : Set ILink}
    (hSA : ∀ l ∈ S, ∀ ν y, Near y l.2 → (ν, y) ∈ A) {U U' : IConf G2}
    (h : ∀ l ∈ A, U l = U' l) : ∀ l ∈ A, apeOn c hc0 hc S U l = apeOn c hc0 hc S U' l := by
  classical
  intro l hl
  simp only [apeOn]
  split_ifs with hS
  · obtain ⟨μ, x⟩ := l
    exact apeConf_local hc0 hc μ x (fun ν y hy => h _ (hSA _ hS ν y hy))
  · exact h l hl

#print axioms apeOn_agree

/-- Agreement is preserved by any number of localised steps.

DERIVED: `0` is the base of the induction; `1/6` the dominance bound. -/
theorem apeOnIter_agree {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) {S A : Set ILink}
    (hSA : ∀ l ∈ S, ∀ ν y, Near y l.2 → (ν, y) ∈ A) (n : ℕ) {U U' : IConf G2}
    (h : ∀ l ∈ A, U l = U' l) :
    ∀ l ∈ A, (apeOn c hc0 hc S)^[n] U l = (apeOn c hc0 hc S)^[n] U' l := by
  induction n generalizing U U' with
  | zero => exact h
  | succ n ih =>
    intro l hl
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (apeOn_agree hc0 hc hSA h) l hl

#print axioms apeOnIter_agree

/-- The links whose base lies within `R` of `x` in every coordinate.

DERIVED: no numeral; `R` is the caller's radius. -/
def box (x : ISite) (R : ℕ) : Set ILink := {l | ∀ i, x i - R ≤ l.2 i ∧ l.2 i ≤ x i + R}

/-- The box of radius `R` and every link near it lie in the box of radius `R + 1`.

DERIVED: `1` is one lattice step. -/
theorem box_near (x : ISite) (R : ℕ) :
    ∀ l ∈ box x R, ∀ ν y, Near y l.2 → (ν, y) ∈ box x (R + 1) := by
  intro l hl ν y hy i
  have h1 := hl i
  have h2 := hy i
  push_cast
  constructor <;> omega

#print axioms box_near

/-- **The localised smearing flow**: `n` APE steps run inside the box of radius `R` around the output
link's base, the outside held fixed.

DERIVED: `1/6` the dominance bound. -/
noncomputable def locApe (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (U : IConf G2) :
    IConf G2 :=
  fun l => (apeOn c hc0 hc (box l.2 R))^[n] U l

/-- **The localised flow is gauge covariant.**

DERIVED: `1/6` the dominance bound. -/
theorem locApe_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (g : ISite → G2)
    (U : IConf G2) :
    locApe c hc0 hc n R (igaugeTransform g U) = igaugeTransform g (locApe c hc0 hc n R U) := by
  funext l
  simp only [locApe]
  rw [apeOnIter_gauge]
  rfl

#print axioms locApe_gauge

/-- **The localised flow is continuous.**

DERIVED: `1/6` the dominance bound. -/
theorem continuous_locApe {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) :
    Continuous (locApe c hc0 hc n R) :=
  continuous_pi (fun l => (continuous_apply l).comp ((continuous_apeOn hc0 hc _).iterate n))

#print axioms continuous_locApe

/-- **The localised flow has range `R + 1`, whatever `n`**: configurations agreeing on the links based
within `R + 1` of the output link's base give the same output.

DERIVED: `1` is one lattice step; `1/6` the dominance bound. -/
theorem locApe_local {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ) (l : ILink)
    {U U' : IConf G2} (h : ∀ l' ∈ box l.2 (R + 1), U l' = U' l') :
    locApe c hc0 hc n R U l = locApe c hc0 hc n R U' l := by
  have hl : l ∈ box l.2 (R + 1) := fun i => by push_cast; constructor <;> omega
  exact apeOnIter_agree hc0 hc (box_near l.2 R) n h l hl

#print axioms locApe_local

end MassGap.LocalApe
