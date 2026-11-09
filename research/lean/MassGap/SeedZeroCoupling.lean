import Mathlib
import MassGap.RectWilson

/-!
# MassGap.SeedZeroCoupling — the doubling seed holds at zero coupling

`DoublingClay2.WDelta2` is the seed `16 log ZR(n⁴) − log ZR((2n)⁴) ≤ 1/1000` read eventually in `β` at
the power-of-two side `nP N ℓ₀ β`. Every consequence the tree draws from it runs through
`DoublingClay2.DyadicTorusDecay`, which takes the seed at one coupling `β ≥ 0` and one side `n`.

`ZR_at_zero`: at `β = 0` the Boltzmann weight is `1` and the link measure is a probability, so
`ZR L N 0 = 1` on every rectangular torus. `seed_at_zero` and `defect_at_zero`: the seed holds at
`β = 0` on every side, with defect exactly `0`. There the links are independent Haar variables and the
connected function of two plaquettes at nonzero lag vanishes.

So a statement of the form "the seed at `(β, n)` gives `P(β)`" also gives `P(0)`. A lower bound on a
separated connected function of order two, three or four is false at `β = 0`, so no such statement
draws one from the seed. Non-triviality (item 4) needs an input that is not a per-coupling consequence
of the seed: the coupling's tie to the scale (`aRun` inside `nP`, requirement Y), or a lower bound on a
separated cumulant.

DERIVED: `0` the coupling; `1` the weight `exp 0` and the total mass of the probability measure; `16`,
`2` and `1/1000` are the seed's.
-/

namespace MassGap.SeedZeroCoupling

open MeasureTheory MassGap MassGap.LatticeGauge MassGap.CompactGauge

/-- **The rectangular partition function is `1` at zero coupling.**

DERIVED: `0` the coupling; `1` the weight and the total mass. -/
theorem ZR_at_zero (L : Fin 4 → ℕ) (N : ℕ) : RectWilson.ZR L N 0 = 1 := by
  haveI : IsProbabilityMeasure ((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ => probHaar (SUN.SU N))))
  have hb : ∀ U, (RectWilson.sysR L N).boltz 0 U = 1 := fun U => by unfold System.boltz; simp
  have hvol : ((RectWilson.sysR L N).vol (probHaar (SUN.SU N))).real Set.univ = 1 := by
    change (((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  unfold RectWilson.ZR System.partition
  simp only [hb, integral_const, smul_eq_mul, mul_one, hvol]

#print axioms ZR_at_zero

/-- **The doubling defect is `0` at zero coupling**, on every side `n`.

DERIVED: `16 = 2⁴` and `2` are the seed's. -/
theorem defect_at_zero (N n : ℕ) :
    16 * Real.log (RectWilson.ZR (fun _ => n) N 0) - Real.log (RectWilson.ZR (fun _ => 2 * n) N 0)
      = 0 := by
  rw [ZR_at_zero, ZR_at_zero, Real.log_one]
  ring

#print axioms defect_at_zero

/-- **The seed holds at zero coupling**, on every side `n`.

DERIVED: `16`, `2` and `1/1000` are the seed's. -/
theorem seed_at_zero (N n : ℕ) :
    16 * Real.log (RectWilson.ZR (fun _ => n) N 0) - Real.log (RectWilson.ZR (fun _ => 2 * n) N 0)
      ≤ 1 / 1000 := by
  rw [defect_at_zero]
  norm_num

#print axioms seed_at_zero

end MassGap.SeedZeroCoupling
