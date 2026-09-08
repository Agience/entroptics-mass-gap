import MassGap.SUN

/-!
# MassGap.WilsonAction — the genuine Wilson action density on `SU(N)` (dynamical face, brick 1)

The A1–A3 modules give the *measure* face of the fidelity lift: a genuine `SU(N)` Haar measure whose
Osterwalder–Schrader invariances are derived, at the cost of a trivial action (`φ ≡ 0`). The *dynamical*
face — the confinement content that feeds the mass gap (residuals B/C) — needs the real **Wilson action
density** on a plaquette holonomy `g ∈ SU(N)`:
$$ \varphi_W(g) \;=\; 1 - \tfrac1N \operatorname{Re}\operatorname{tr} g \;\in\; \mathbb{R}. $$

This file defines it and proves the two properties any Wilson action rests on:

* `wilsonDensity_one` — the identity holonomy (no flux) has zero action;
* `wilsonDensity_conj` — **conjugation invariance** `φ_W(h g h⁻¹) = φ_W(g)` (trace cyclicity): the seed of
  gauge invariance, since a lattice gauge transformation conjugates each plaquette holonomy.

It is a valid `LatticeGauge.System.φ`, so a `System` built with a real plaquette holonomy and this `φ` is a
genuine Wilson gauge theory. The remaining dynamical-face work (a hypercubic plaquette holonomy with
axis-permutation `compat`, and the centre-vortex count-injection `vortexTerm μ n ≤ Z n`) builds on this.

Foundational footprint only. Build: `lake build MassGap.WilsonAction`.
-/

namespace MassGap.WilsonAction

open Matrix

variable {N : ℕ}

/-- The **Wilson action density** of a holonomy `g ∈ SU(N)`: `1 − (1/N)·Re tr g`. The plaquette energy in
the fundamental representation; zero at the identity, positive off it. -/
noncomputable def wilsonDensity (g : MassGap.SUN.SU N) : ℝ :=
  1 - (1 / (N : ℝ)) * (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re

/-- The identity holonomy (no flux) has zero Wilson action: `tr 1 = N`, so `1 − (1/N)·N = 0`. -/
theorem wilsonDensity_one (hN : N ≠ 0) : wilsonDensity (1 : MassGap.SUN.SU N) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold wilsonDensity
  rw [Submonoid.coe_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, one_div,
    inv_mul_cancel₀ hN', sub_self]

/-- **Conjugation invariance** `φ_W(h g h⁻¹) = φ_W(g)` — the gauge-invariance seed. From trace cyclicity:
`tr(h g h⁻¹) = tr(h⁻¹ h g) = tr g`, using that `h⁻¹` is the matrix inverse of `h` in `SU(N)`. -/
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

/-- `|Re tr U| ≤ N` for `U ∈ SU(N)`: each diagonal entry has `|Re| ≤ ‖·‖ ≤ 1` (unitarity). -/
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

/-- **The Wilson action density is nonnegative** (`Re tr U ≤ N`). -/
theorem wilsonDensity_nonneg {N : ℕ} (hN : N ≠ 0) (g : MassGap.SUN.SU N) :
    0 ≤ wilsonDensity g := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hle : (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re ≤ N := (abs_le.mp (abs_re_trace_le g)).2
  unfold wilsonDensity
  rw [sub_nonneg, div_mul_eq_mul_div, one_mul, div_le_one hNpos]
  exact hle

/-- **The Wilson action density is at most 2** (`-N ≤ Re tr U`). So `φ_W ∈ [0, 2]`. -/
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

/-- The Wilson action density is continuous (trace and real part are continuous). -/
theorem continuous_wilsonDensity {N : ℕ} : Continuous (wilsonDensity : MassGap.SUN.SU N → ℝ) := by
  unfold wilsonDensity
  refine continuous_const.sub (continuous_const.mul ?_)
  exact Complex.continuous_re.comp continuous_subtype_val.matrix_trace

/-- The Wilson action density is measurable. -/
theorem measurable_wilsonDensity {N : ℕ} : Measurable (wilsonDensity : MassGap.SUN.SU N → ℝ) :=
  continuous_wilsonDensity.measurable

#print axioms wilsonDensity_one
#print axioms wilsonDensity_conj
#print axioms wilsonDensity_nonneg
#print axioms wilsonDensity_le_two
#print axioms measurable_wilsonDensity

end MassGap.WilsonAction
