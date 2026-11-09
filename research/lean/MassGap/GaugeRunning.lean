import Mathlib
import MassGap.GaugeInstances
import MassGap.AsymptoticScaling

/-!
# MassGap.GaugeRunning — the two-loop running spacing over a `GaugeGroup`

The pure Yang–Mills beta function `μ dg/dμ = −b₀ g³ − b₁ g⁵` has, for a simple `𝔤` normalised so
that long roots have squared length two,

  `b₀ = 11 C₂(adj) / (3 · 16π²) = 11 h^∨ / (48π²)`,  `b₁ = 34 C₂(adj)² / (3 · (16π²)²)`.

The Wilson action `β Σ_planes (1 − Re tr ρ(U)/d)`, each plane counted once, has naive continuum
limit `(β g² T(ρ) / (4d)) ∫ Σ_{μν} (F^a_{μν})²`, so `g² = d / (T(ρ) β)` (at `SU(N)`, fundamental:
`g² = 2N/β`). The two-loop spacing in units of `Λ` is `(b₀g²)^{−b₁/(2b₀²)} exp(−1/(2b₀g²))`.

`aRunStdG G β` is that expression with the constants of `GaugeSimple G`. Two facts:

* `exponent_eq`: `b₁/(2b₀²) = 51/121` at every simple `G`, since both coefficients are carried by
  `h^∨` alone; only the argument `48π² T β / (11 h^∨ d)` depends on the group
  (`aRunStdG_eq`).
* `aRunStdG_SU`: at `SU(N)`, `N ≥ 2`, `aRunStdG = AsymptoticScaling.aRunStd N`, and
  `aRunG_SU`: the Lean-coupling form `aRunG G β = aRunStdG G (2β)` is `AsymptoticScaling.aRun N`.

So every `SU(N)` statement that reads the spacing through `aRunStd N`/`aRun N` reads, at a general
`G`, the same function of the rescaled coupling `β · (2 T(ρ) N² / (h^∨ d))`.
-/

namespace MassGap.GaugeRunning

open MassGap.GaugeGroup Real

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- `h^∨ = C₂(adj)` as a real. -/
noncomputable abbrev hG : ℝ := (GaugeSimple.dualCoxeter (G := G) : ℝ)

/-- `T(ρ)`, the Dynkin index of the plaquette representation. -/
noncomputable abbrev TG : ℝ := GaugeSimple.dynkinIndex (G := G)

/-- `d`, the dimension of the plaquette representation, as a real. -/
noncomputable abbrev dG : ℝ := (GaugeGroup.dim G : ℝ)

/-- One-loop coefficient. DERIVED: `11/3` is the gluon loop, `16π²` the loop measure. -/
noncomputable def b0G : ℝ := 11 * hG G / (48 * π ^ 2)

/-- Two-loop coefficient. DERIVED: `34/3` is the two-loop gluon coefficient. -/
noncomputable def b1G : ℝ := 34 * hG G ^ 2 / (3 * (16 * π ^ 2) ^ 2)

/-- The bare coupling of the Wilson action at standard coupling `β`, `g² = d / (T(ρ) β)`.

DERIVED: from `1 − Re tr ρ(e^{iX})/d = T(ρ)|X|²/(2d) + O(X⁴)`. -/
noncomputable def gSqG (β : ℝ) : ℝ := dG G / (TG G * β)

/-- The two-loop running spacing at standard coupling `β`, `Λ = 1`.

DERIVED: the `1` and `2` are those of `(b₀g²)^{−b₁/(2b₀²)} exp(−1/(2b₀g²))`. -/
noncomputable def aRunStdG (β : ℝ) : ℝ :=
  ((b0G G * gSqG G β)⁻¹) ^ (b1G G / (2 * b0G G ^ 2)) * Real.exp (-(1 / (2 * (b0G G * gSqG G β))))

/-- The spacing at the Lean coupling (each plane counted twice), `aRunStdG G (2β)`.

DERIVED: `2` is the number of orderings of a plane. -/
noncomputable def aRunG (β : ℝ) : ℝ := aRunStdG G (2 * β)

variable {G}

theorem hG_pos : 0 < hG G := Nat.cast_pos.mpr GaugeSimple.dualCoxeter_pos

theorem TG_pos : 0 < TG G := GaugeSimple.dynkinIndex_pos

omit [GaugeSimple G] in
theorem dG_pos : 0 < dG G := Nat.cast_pos.mpr GaugeGroup.dim_pos

theorem b0G_pos : 0 < b0G G := by unfold b0G; have := hG_pos (G := G); positivity

/-- The two-loop exponent is group-independent.

DERIVED: `51/121 = 34 · 48² / (3 · 256 · 2 · 121)`. -/
theorem exponent_eq : b1G G / (2 * b0G G ^ 2) = 51 / 121 := by
  have hh := (hG_pos (G := G)).ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  unfold b1G b0G
  first | (field_simp; done) | (field_simp; ring)

/-- `(b₀ g²)⁻¹ = 48π² T β / (11 h^∨ d)`, at every `β` (both sides vanish at `β = 0`).

DERIVED: the numerals are `b0G`'s: `11` the gluon loop of `11/3`, `48 = 3 · 16` from `11/3` over the
loop measure `16π²`. -/
theorem inv_b0_gSq (β : ℝ) :
    (b0G G * gSqG G β)⁻¹ = 48 * π ^ 2 * TG G * β / (11 * hG G * dG G) := by
  have hh := (hG_pos (G := G)).ne'
  have hT := (TG_pos (G := G)).ne'
  have hd := (dG_pos (G := G)).ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  unfold b0G gSqG
  rcases eq_or_ne β 0 with rfl | hβ
  · simp
  · field_simp

/-- The closed form of `aRunStdG`.

DERIVED: `24 = 48/2` from the `2` of `1/(2b₀g²)`; `48`, `11` as in `inv_b0_gSq`; `51/121` the
two-loop exponent of `exponent_eq`. -/
theorem aRunStdG_eq (β : ℝ) :
    aRunStdG G β = (48 * π ^ 2 * TG G * β / (11 * hG G * dG G)) ^ (51 / 121 : ℝ)
      * Real.exp (-(24 * π ^ 2 * TG G * β / (11 * hG G * dG G))) := by
  unfold aRunStdG
  rw [exponent_eq, inv_b0_gSq, one_div, mul_inv, inv_b0_gSq]
  congr 2
  ring

variable (N : ℕ) [NeZero N] [Fact (2 ≤ N)]

/-- At `SU(N)`, `N ≥ 2`, the generic spacing is `AsymptoticScaling.aRunStd N`.

DERIVED: `T = 1/2`, `h^∨ = d = N` turn `48π² T β/(11 h^∨ d)` into `24π²β/(11N²)`. -/
theorem aRunStdG_SU (β : ℝ) :
    aRunStdG (MassGap.SUN.SU N) β = MassGap.AsymptoticScaling.aRunStd N β := by
  rw [aRunStdG_eq]
  show (48 * π ^ 2 * (1 / 2 : ℝ) * β / (11 * (N : ℝ) * (N : ℝ))) ^ (51 / 121 : ℝ)
      * Real.exp (-(24 * π ^ 2 * (1 / 2 : ℝ) * β / (11 * (N : ℝ) * (N : ℝ)))) = _
  unfold MassGap.AsymptoticScaling.aRunStd
  have h1 : 48 * π ^ 2 * (1 / 2 : ℝ) * β / (11 * (N : ℝ) * (N : ℝ))
      = (24 * π ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by ring
  have h2 : -(24 * π ^ 2 * (1 / 2 : ℝ) * β / (11 * (N : ℝ) * (N : ℝ)))
      = -(12 * π ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by ring
  rw [h1, h2]

theorem aRunG_SU (β : ℝ) :
    aRunG (MassGap.SUN.SU N) β = MassGap.AsymptoticScaling.aRun N β := by
  unfold aRunG MassGap.AsymptoticScaling.aRun
  exact aRunStdG_SU N (2 * β)

theorem b0G_SU : b0G (MassGap.SUN.SU N) = 11 * (N : ℝ) / (48 * π ^ 2) := rfl

theorem gSqG_SU (β : ℝ) : gSqG (MassGap.SUN.SU N) β = (N : ℝ) / ((1 / 2) * β) := rfl

#print axioms exponent_eq
#print axioms aRunStdG_eq
#print axioms aRunStdG_SU
#print axioms aRunG_SU

end MassGap.GaugeRunning
