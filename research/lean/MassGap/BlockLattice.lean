import Mathlib
import MassGap.BlockSU2
import MassGap.GaugeInvariantAlgebra

/-!
# MassGap.BlockLattice — the averaged block step of an `SU(2)` configuration on `ℤ⁴`

The coarse lattice is the even sublattice, relabelled as `ℤ⁴` by `two x = 2x`. The coarse link `(μ, x)`
is `BlockSU2.blockLink` of the doubled fine link `U_μ(2x) U_μ(2x + μ̂)` and the six staples beside it,
three transverse directions `ν` (`Fin.succAbove μ`) on two sides:

    up   : U_ν(y) U_μ(y + ν̂) U_μ(y + ν̂ + μ̂) U_ν(y + 2μ̂)⁻¹,
    down : U_ν(y − ν̂)⁻¹ U_μ(y − ν̂) U_μ(y − ν̂ + μ̂) U_ν(y + 2μ̂ − ν̂),     y = 2x.

* `blockConf c hc0 hc : IConf (SU 2) → IConf (SU 2)`, for `0 ≤ c < 1/6`.
* `blockConf_gauge`: `blockConf (g · U) = (g ∘ two) · blockConf U` — a fine gauge transformation acts on
  the blocked configuration as the coarse one it restricts to.
* `continuous_blockConf`: continuous in the product topology.
-/

namespace MassGap.BlockLattice

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.BlockSU2 MassGap.GaugeInvariantAlgebra

/-- `SU(2)`.

DERIVED: `2` is the rank. -/
abbrev G2 : Type := MassGap.SUN.SU 2

/-- The fine site of a coarse site: `2x`.

DERIVED: `2` is the block factor. -/
def two (x : ISite) : ISite := fun i => 2 * x i

/-- One step back in direction `ν`.

DERIVED: `1` is one lattice step. -/
def iback (ν : Fin 4) (x : ISite) : ISite := Function.update x ν (x ν - 1)

/-- The `j`-th direction transverse to `μ`.

DERIVED: `3` transverse directions in four dimensions. -/
def other (μ : Fin 4) (j : Fin 3) : Fin 4 := Fin.succAbove μ j

/-- A forward step undoes a backward one.

DERIVED: `1` is one lattice step. -/
theorem ishift_iback (ν : Fin 4) (x : ISite) : ishift ν (iback ν x) = x := by
  funext i
  by_cases h : i = ν
  · subst h; simp [ishift, iback]
  · simp [ishift, iback, Function.update_of_ne h]

#print axioms ishift_iback

/-- The coarse shift is two fine shifts: `2(x + μ̂) = 2x + 2μ̂`.

DERIVED: `2` is the block factor. -/
theorem two_ishift (μ : Fin 4) (x : ISite) : two (ishift μ x) = ishift μ (ishift μ (two x)) := by
  funext i
  by_cases h : i = μ
  · subst h; simp [two, ishift]; ring
  · simp [two, ishift, Function.update_of_ne h]

#print axioms two_ishift

/-- Shifts and back-shifts in different directions commute.

DERIVED: `1` is one lattice step. -/
theorem ishift_iback_comm (μ ν : Fin 4) (x : ISite) :
    ishift μ (iback ν x) = iback ν (ishift μ x) := by
  funext i
  by_cases hν : i = ν <;> by_cases hμ : i = μ
  · subst hν; subst hμ; simp [ishift, iback]
  · subst hν; simp [ishift, iback, Function.update_of_ne hμ]
  · subst hμ; simp [ishift, iback, Function.update_of_ne hν]
  · simp [ishift, iback, Function.update_of_ne hν, Function.update_of_ne hμ]

#print axioms ishift_iback_comm

/-- **The doubled fine link** `U_μ(2x) U_μ(2x + μ̂)`.

DERIVED: no numeral. -/
def dbl (U : IConf G2) (μ : Fin 4) (x : ISite) : G2 := U (μ, two x) * U (μ, ishift μ (two x))

/-- **A staple** beside the doubled link: transverse direction `other μ p.1`, side `p.2` (`0` up, `1`
down).

DERIVED: `0` names the upper side; `3` the transverse directions of `other` in four dimensions. -/
def staple (U : IConf G2) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) : G2 :=
  if p.2 = 0 then
    U (other μ p.1, two x) * U (μ, ishift (other μ p.1) (two x))
      * U (μ, ishift μ (ishift (other μ p.1) (two x)))
      * (U (other μ p.1, ishift μ (ishift μ (two x))))⁻¹
  else
    (U (other μ p.1, iback (other μ p.1) (two x)))⁻¹ * U (μ, iback (other μ p.1) (two x))
      * U (μ, ishift μ (iback (other μ p.1) (two x)))
      * U (other μ p.1, ishift μ (ishift μ (iback (other μ p.1) (two x))))

/-- **The blocked configuration**: every coarse link is the normalised block link of its doubled fine
link and its six staples.

DERIVED: `6 = 3 · 2` staples (`finProdFinEquiv`); `1/6` the dominance bound. -/
noncomputable def blockConf (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (U : IConf G2) : IConf G2 :=
  fun l => blockLink c hc0 hc (dbl U l.1 l.2) (fun i => staple U l.1 l.2 (finProdFinEquiv.symm i))

/-- The doubled link of a gauge-transformed configuration.

DERIVED: no numeral. -/
theorem dbl_gauge (g : ISite → G2) (U : IConf G2) (μ : Fin 4) (x : ISite) :
    dbl (igaugeTransform g U) μ x
      = g (two x) * dbl U μ x * (g (ishift μ (ishift μ (two x))))⁻¹ := by
  simp only [dbl, igaugeTransform]
  group

#print axioms dbl_gauge

/-- A staple of a gauge-transformed configuration.

DERIVED: `0` names the upper side; `3` the transverse directions of `other` in four dimensions. -/
theorem staple_gauge (g : ISite → G2) (U : IConf G2) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    staple (igaugeTransform g U) μ x p
      = g (two x) * staple U μ x p * (g (ishift μ (ishift μ (two x))))⁻¹ := by
  have hup : ishift μ (ishift μ (ishift (other μ p.1) (two x)))
      = ishift (other μ p.1) (ishift μ (ishift μ (two x))) := by
    rw [ishift_comm μ (other μ p.1), ishift_comm μ (other μ p.1)]
  have hdn : ishift (other μ p.1) (iback (other μ p.1) (two x)) = two x := ishift_iback _ _
  have hdn2 : ishift (other μ p.1) (ishift μ (ishift μ (iback (other μ p.1) (two x))))
      = ishift μ (ishift μ (two x)) := by
    rw [ishift_comm (other μ p.1) μ, ishift_comm (other μ p.1) μ, hdn]
  unfold staple
  split_ifs with h
  · simp only [igaugeTransform]
    rw [hup]
    group
  · simp only [igaugeTransform]
    rw [hdn, hdn2]
    group

#print axioms staple_gauge

/-- **The block step is gauge covariant**: a fine gauge transformation `g` acts on the blocked
configuration as the coarse gauge transformation `g ∘ two` it restricts to.

DERIVED: `1/6` the dominance bound. -/
theorem blockConf_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (g : ISite → G2) (U : IConf G2) :
    blockConf c hc0 hc (igaugeTransform g U)
      = igaugeTransform (fun x => g (two x)) (blockConf c hc0 hc U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  simp only [blockConf, igaugeTransform]
  rw [two_ishift]
  have hS : (fun i => staple (igaugeTransform g U) μ x (finProdFinEquiv.symm i))
      = fun i => g (two x) * staple U μ x (finProdFinEquiv.symm i)
          * (g (ishift μ (ishift μ (two x))))⁻¹ :=
    funext (fun i => staple_gauge g U μ x _)
  rw [hS, dbl_gauge]
  exact blockLink_gauge hc0 hc _ _ _ _

#print axioms blockConf_gauge

/-- A staple is continuous in the configuration.

DERIVED: `0` names the upper side; `3` the transverse directions of `other` in four dimensions. -/
theorem continuous_staple (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    Continuous (fun U : IConf G2 => staple U μ x p) := by
  by_cases h : p.2 = 0
  · simp only [staple, h, if_true]
    fun_prop
  · simp only [staple, h, if_false]
    fun_prop

#print axioms continuous_staple

/-- The doubled link is continuous in the configuration.

DERIVED: no numeral. -/
theorem continuous_dbl (μ : Fin 4) (x : ISite) : Continuous (fun U : IConf G2 => dbl U μ x) := by
  unfold dbl
  fun_prop

#print axioms continuous_dbl

/-- **The block step is continuous** in the product topology.

DERIVED: `1/6` the dominance bound. -/
theorem continuous_blockConf {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) :
    Continuous (blockConf c hc0 hc) := by
  unfold blockConf
  refine continuous_pi (fun l => ?_)
  have hs : Continuous (fun U : IConf G2 => fun i : Fin 6 => staple U l.1 l.2 (finProdFinEquiv.symm i)) :=
    continuous_pi (fun i => continuous_staple l.1 l.2 _)
  have h := (continuous_blockLink hc0 hc).comp ((continuous_dbl l.1 l.2).prodMk hs)
  exact h

#print axioms continuous_blockConf

end MassGap.BlockLattice
