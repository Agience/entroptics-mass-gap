import Mathlib
import MassGap.BlockLattice

/-!
# MassGap.ApeLattice — one APE smearing step of an `SU(2)` configuration on `ℤ⁴`, same lattice

The continuum-compatible observer is a same-lattice smearing of fixed physical radius (a block lattice
samples the field at points; a smearing defines it everywhere). One step replaces each link by
`BlockSU2.blockLink` of the link itself and its six staples:

    up   : U_ν(x) U_μ(x + ν̂) U_ν(x + μ̂)⁻¹,
    down : U_ν(x − ν̂)⁻¹ U_μ(x − ν̂) U_ν(x − ν̂ + μ̂).

For `0 ≤ c < 1/6` the step is continuous (`continuous_apeConf`) and gauge covariant under the ordinary
gauge action (`apeConf_gauge`): it is a configuration map of the kind `ContinuumFlow.ConfFlow` asks for,
the building block of the localised smearing flow.
-/

namespace MassGap.ApeLattice

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.BlockSU2 MassGap.BlockLattice
  MassGap.GaugeInvariantAlgebra

/-- **A same-lattice staple** beside the link `(μ, x)`: transverse direction `other μ p.1`, side `p.2`.

DERIVED: `0` names the upper side; `3 = 4 − 1` the directions transverse to `μ` (`other μ`). -/
def apeStaple (U : IConf G2) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) : G2 :=
  if p.2 = 0 then
    U (other μ p.1, x) * U (μ, ishift (other μ p.1) x) * (U (other μ p.1, ishift μ x))⁻¹
  else
    (U (other μ p.1, iback (other μ p.1) x))⁻¹ * U (μ, iback (other μ p.1) x)
      * U (other μ p.1, ishift μ (iback (other μ p.1) x))

/-- **One APE step**: every link replaced by the normalised sum of itself and `c` times its staples.

DERIVED: `6 = 3 · 2` staples; `1/6` the dominance bound. -/
noncomputable def apeConf (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (U : IConf G2) : IConf G2 :=
  fun l => blockLink c hc0 hc (U l) (fun i => apeStaple U l.1 l.2 (finProdFinEquiv.symm i))

/-- A same-lattice staple of a gauge-transformed configuration.

DERIVED: `0` names the upper side; `3 = 4 − 1` the directions transverse to `μ` (`other μ`). -/
theorem apeStaple_gauge (g : ISite → G2) (U : IConf G2) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    apeStaple (igaugeTransform g U) μ x p = g x * apeStaple U μ x p * (g (ishift μ x))⁻¹ := by
  have hup : ishift μ (ishift (other μ p.1) x) = ishift (other μ p.1) (ishift μ x) :=
    ishift_comm μ (other μ p.1) x
  have hdn : ishift (other μ p.1) (iback (other μ p.1) x) = x := ishift_iback _ _
  have hdn2 : ishift (other μ p.1) (ishift μ (iback (other μ p.1) x)) = ishift μ x := by
    rw [ishift_comm (other μ p.1) μ, hdn]
  unfold apeStaple
  split_ifs with h
  · simp only [igaugeTransform]
    rw [hup]
    group
  · simp only [igaugeTransform]
    rw [hdn, hdn2]
    group

#print axioms apeStaple_gauge

/-- **The APE step is gauge covariant** under the ordinary gauge action.

DERIVED: `1/6` the dominance bound. -/
theorem apeConf_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (g : ISite → G2) (U : IConf G2) :
    apeConf c hc0 hc (igaugeTransform g U) = igaugeTransform g (apeConf c hc0 hc U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  simp only [apeConf]
  have hS : (fun i => apeStaple (igaugeTransform g U) μ x (finProdFinEquiv.symm i))
      = fun i => g x * apeStaple U μ x (finProdFinEquiv.symm i) * (g (ishift μ x))⁻¹ :=
    funext (fun i => apeStaple_gauge g U μ x _)
  rw [hS]
  show blockLink c hc0 hc (g x * U (μ, x) * (g (ishift μ x))⁻¹) _ = _
  rw [blockLink_gauge hc0 hc]
  rfl

#print axioms apeConf_gauge

/-- A same-lattice staple is continuous in the configuration.

DERIVED: `0` names the upper side; `3 = 4 − 1` the directions transverse to `μ` (`other μ`). -/
theorem continuous_apeStaple (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    Continuous (fun U : IConf G2 => apeStaple U μ x p) := by
  by_cases h : p.2 = 0
  · simp only [apeStaple, h, if_true]
    fun_prop
  · simp only [apeStaple, h, if_false]
    fun_prop

#print axioms continuous_apeStaple

/-- **The APE step is continuous** in the product topology.

DERIVED: `1/6` the dominance bound. -/
theorem continuous_apeConf {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) :
    Continuous (apeConf c hc0 hc) := by
  unfold apeConf
  refine continuous_pi (fun l => ?_)
  have hs : Continuous (fun U : IConf G2 => fun i : Fin 6 => apeStaple U l.1 l.2 (finProdFinEquiv.symm i)) :=
    continuous_pi (fun i => continuous_apeStaple l.1 l.2 _)
  have h := (continuous_blockLink hc0 hc).comp ((continuous_apply l).prodMk hs)
  exact h

#print axioms continuous_apeConf

/-- **Iterated APE steps** stay gauge covariant.

DERIVED: `0` is the base of the induction; `1/6` the dominance bound. -/
theorem apeIter_gauge {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n : ℕ) (g : ISite → G2) (U : IConf G2) :
    (apeConf c hc0 hc)^[n] (igaugeTransform g U) = igaugeTransform g ((apeConf c hc0 hc)^[n] U) := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, apeConf_gauge, ih]

#print axioms apeIter_gauge

/-- **Iterated APE steps** stay continuous.

DERIVED: `1/6` the dominance bound. -/
theorem continuous_apeIter {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n : ℕ) :
    Continuous ((apeConf c hc0 hc)^[n]) :=
  (continuous_apeConf hc0 hc).iterate n

#print axioms continuous_apeIter

end MassGap.ApeLattice
