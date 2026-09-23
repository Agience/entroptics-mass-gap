import MassGap.SUN

/-!
# MassGap.WilsonAction — the Wilson plaquette density on `SU(N)`

The Wilson action density of a plaquette holonomy `g ∈ SU(N)` in the fundamental representation,
`φ_W(g) = 1 - (1/N) · Re tr g ∈ ℝ`. `SU N` is `MassGap.SUN.SU N`, a submonoid of
`Matrix (Fin N) (Fin N) ℂ`; `N` is a `variable`, so every declaration here is stated for arbitrary
colour count.

The file proves five facts about it:

* `wilsonDensity_one` — `φ_W(1) = 0`, requiring `N ≠ 0`;
* `wilsonDensity_conj` — `φ_W(h g h⁻¹) = φ_W(g)`, from trace cyclicity, with no hypothesis on `N`;
* `wilsonDensity_nonneg` and `wilsonDensity_le_two` — the range `φ_W ∈ [0, 2]`, both requiring `N ≠ 0`
  and both routed through `abs_re_trace_le : |Re tr g| ≤ N`;
* `continuous_wilsonDensity` and `measurable_wilsonDensity` — regularity, with no hypothesis on `N`.

Nothing here refers to a lattice, a plaquette map or a measure: `wilsonDensity` is a function of a
single group element. Whether it is admissible as some system's action field is settled at the call
site, not by any declaration in this file.

Build: `lake build MassGap.WilsonAction`.
-/

namespace MassGap.WilsonAction

open Matrix

variable {N : ℕ}

/-- The Wilson action density of `g ∈ SU(N)`: `1 - (1/N) · Re tr g`, a real number. `N` is
unconstrained, so at `N = 0` the cast makes `1 / (N : ℝ) = 0` and the density is constantly `1`; the
lemmas giving it the range `[0, 2]` and the value `0` at the identity all carry `N ≠ 0`.

DERIVED: the leading `1` is the density's normalisation, fixed by `Re tr 1 = N` so that the identity
holonomy costs nothing; the `1` in `1 / N` is that same normalisation divided over the `N` colours. -/
noncomputable def wilsonDensity (g : MassGap.SUN.SU N) : ℝ :=
  1 - (1 / (N : ℝ)) * (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re

/-- `wilsonDensity (1 : SU N) = 0` when `N ≠ 0`. From `Matrix.trace_one` and `Fintype.card_fin`,
`Re tr 1 = N`; `inv_mul_cancel₀` then needs the cast `(N : ℝ)` nonzero, which is what `hN` supplies.
The hypothesis cannot be dropped: at `N = 0` the density is `1`.

DERIVED: the `0` in `hN` is the excluded colour count; `1` is the group identity, the argument being
measured; the `0` on the right is its density, forced by `Re tr 1 = N`. -/
theorem wilsonDensity_one (hN : N ≠ 0) : wilsonDensity (1 : MassGap.SUN.SU N) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold wilsonDensity
  rw [Submonoid.coe_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, one_div,
    inv_mul_cancel₀ hN', sub_self]

/-- `wilsonDensity (h * g * h⁻¹) = wilsonDensity g` for all `h g : SU N`. By `Matrix.trace_mul_comm`
and the fact that the `SU(N)` inverse coerces to the matrix inverse, so `tr (h g h⁻¹) = tr (h⁻¹ h g)
= tr g`. Stated for every `N`, including `N = 0`: only the trace moves, so no nonvanishing hypothesis
is needed.

DERIVED: no numeral. -/
theorem wilsonDensity_conj (h g : MassGap.SUN.SU N) :
    wilsonDensity (h * g * h⁻¹) = wilsonDensity g := by
  have hinv : ((h⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      * ((h : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    exact Submonoid.coe_one _
  have hcoe3 : ((h * g * h⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (h : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ)
        * ((h⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
  have key : Matrix.trace ((h * g * h⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.trace ((g : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hcoe3, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  unfold wilsonDensity
  rw [key]

/-- `|Re tr g| ≤ (N : ℝ)` for `g : SU N`. Each diagonal entry satisfies `|Re z| ≤ ‖z‖ ≤ 1` — the
first by `Complex.abs_re_le_norm`, the second by `MassGap.SUN.unitary_entry_norm_le_one` applied to
the unitarity extracted from `Matrix.mem_specialUnitaryGroup_iff` — and the trace is the sum of `N`
of them. The bound is `N` itself, so it degenerates correctly at `N = 0`.

DERIVED: no numeral. The `N` on the right is the index type's cardinality, via `Fintype.card_fin`. -/
theorem abs_re_trace_le {N : ℕ} (g : MassGap.SUN.SU N) :
    |(Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re| ≤ (N : ℝ) := by
  have hu : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have hentry : ∀ i, |((g : Matrix (Fin N) (Fin N) ℂ) i i).re| ≤ 1 := fun i =>
    le_trans (Complex.abs_re_le_norm _) (MassGap.SUN.unitary_entry_norm_le_one N hu i i)
  have htr : (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re
      = ∑ i, ((g : Matrix (Fin N) (Fin N) ℂ) i i).re := by
    rw [show Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)
        = ∑ i, (g : Matrix (Fin N) (Fin N) ℂ) i i from rfl, Complex.re_sum]
  rw [htr]
  calc |∑ i, ((g : Matrix (Fin N) (Fin N) ℂ) i i).re|
      ≤ ∑ i, |((g : Matrix (Fin N) (Fin N) ℂ) i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hentry i)
    _ = (N : ℝ) := by simp

/-- `0 ≤ wilsonDensity g` when `N ≠ 0`. The upper half of `abs_re_trace_le` gives `Re tr g ≤ N`, and
`div_le_one` needs `(N : ℝ) > 0`, which `hN` supplies.

DERIVED: the `0` in `hN` is the excluded colour count; the `0` on the left is the density's value at
the identity (`wilsonDensity_one`), which `Re tr g ≤ N` shows to be its minimum. -/
theorem wilsonDensity_nonneg {N : ℕ} (hN : N ≠ 0) (g : MassGap.SUN.SU N) :
    0 ≤ wilsonDensity g := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hle : (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re ≤ N := (abs_le.mp (abs_re_trace_le g)).2
  unfold wilsonDensity
  rw [sub_nonneg, div_mul_eq_mul_div, one_mul, div_le_one hNpos]
  exact hle

/-- `wilsonDensity g ≤ 2` when `N ≠ 0`. The lower half of `abs_re_trace_le` gives `-N ≤ Re tr g`,
hence `(1/N) · Re tr g ≥ -1` and `φ_W ≤ 1 - (-1) = 2`. With `wilsonDensity_nonneg` this pins the
range to `[0, 2]`.

DERIVED: the `0` in `hN` is the excluded colour count; `2` is `1 - (-1)`, the density's normalisation
`1` plus the largest value `-(1/N) · Re tr g` can take, attained when `Re tr g = -N`. -/
theorem wilsonDensity_le_two {N : ℕ} (hN : N ≠ 0) (g : MassGap.SUN.SU N) :
    wilsonDensity g ≤ 2 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hge : -(N : ℝ) ≤ (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re :=
    (abs_le.mp (abs_re_trace_le g)).1
  have hbd : -1 ≤ (1 / (N : ℝ)) * (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hNpos, neg_one_mul]
    exact hge
  unfold wilsonDensity
  linarith [hbd]

/-- `wilsonDensity : SU N → ℝ` is continuous, for every `N`. The subtype inclusion, `Matrix.trace`
and `Complex.re` are each continuous and the surrounding arithmetic is by constants.

DERIVED: no numeral. -/
theorem continuous_wilsonDensity {N : ℕ} : Continuous (wilsonDensity : MassGap.SUN.SU N → ℝ) := by
  unfold wilsonDensity
  refine continuous_const.sub (continuous_const.mul ?_)
  exact Complex.continuous_re.comp continuous_subtype_val.matrix_trace

/-- `wilsonDensity : SU N → ℝ` is measurable, for every `N`, as the measurability of
`continuous_wilsonDensity`.

DERIVED: no numeral. -/
theorem measurable_wilsonDensity {N : ℕ} : Measurable (wilsonDensity : MassGap.SUN.SU N → ℝ) :=
  continuous_wilsonDensity.measurable

#print axioms wilsonDensity_one
#print axioms wilsonDensity_conj
#print axioms wilsonDensity_nonneg
#print axioms wilsonDensity_le_two
#print axioms measurable_wilsonDensity

end MassGap.WilsonAction
